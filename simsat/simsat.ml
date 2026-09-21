open Ark

module Ctx = ArkAst.Ctx
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx [("model", "true");
                                    ("unsat_core", "true")]

let validate = ref false

let file_contents filename =
  let chan = open_in filename in
  let len = in_channel_length chan in
  let buf = Bytes.create len in
  really_input chan buf 0 len;
  close_in chan;
  Bytes.to_string buf

let load_smtlib2 filename = smt_ctx#load_smtlib2 (file_contents filename)

(* Like smt_ctx#load_smtlib2, except that symbols are interned by name in the
   ark context rather than in a table private to the call.  Several strings
   can therefore be parsed into formulas that share variables, which is what
   sequence interpolation needs. *)
let parse_smtlib2_shared str =
  let z3 = smt_ctx#z3 in
  let ast = Z3.SMT.parse_smtlib2_string z3 str [] [] [] [] in
  let sym_of_decl decl =
    let name = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
    let typ = ArkZ3.typ_of_sort (Z3.FuncDecl.get_range decl) in
    if Syntax.is_registered_name ctx name then
      Syntax.get_named_symbol ctx name
    else begin
      Syntax.register_named_symbol ctx name typ;
      Syntax.get_named_symbol ctx name
    end
  in
  match Syntax.Expr.refine ctx (ArkZ3.of_z3 ctx sym_of_decl ast) with
  | `Formula phi -> phi
  | `Term _ -> invalid_arg "parse_smtlib2_shared: expected a formula"

(* Sequence interpolation.

   The input file holds the elements of the sequence separated by a line
   containing only [seq_separator].  The text preceding the first separator is
   a preamble (declarations) that is prepended to every element, so each
   element is parsed as a self-contained SMT-LIB2 script.

   On success the output is

     (unsat (interpolant <formula>) ... (interpolant <formula>))

   and on failure either (sat) -- the conjunction of the sequence is
   satisfiable, so no interpolant exists -- or (unknown). *)
let seq_separator = ";;;SEQ;;;"

(* Which interpolant MathSAT should hand back, when several would do.

   An interpolant is only pinned down between the two sides of the split, and
   the algorithm chosen decides where in that range it lands: McMillan's gives
   the strongest, the inverse gives the weakest.  Strength is not always what
   a caller wants -- a procedure that covers one annotation with another is
   looking for the most general statement that still rules the failure out --
   so it is left to the caller to say. *)
let interpolation_mode = ref None

(* Sequence interpolation, through MathSAT.

   ArkZ3.interpolate_seq goes through Z3's interpolating prover, which in the
   version this repository builds against cannot handle every proof the solver
   hands it: a game whose transition relation is a disjunction of conjunctions
   -- one case per observation, say -- makes it fail with "Unsupported proof
   rule: (rewrite (= (and p q) (not (or (not p) (not q)))))", and reshaping
   the input to avoid that rewrite runs into a malformed term inside the
   prover instead.  MathSAT is already a dependency, and its interpolation for
   linear arithmetic is dependable, so the sequence goes there: one
   interpolation group per element, and the interpolant for the first j + 1
   groups separates the first j + 1 elements from the rest.  Z3 is kept as a
   fallback for sequences MathSAT cannot decide.

   Interpolants come back as SMT-LIB2 text rather than through
   ArkMathsat.of_msat, which crashes on them. *)
let interpolate_seq seq =
  match seq with
  | [] | [_] -> invalid_arg "interpolate_seq: need at least two formulas"
  | _ ->
    let config = Mathsat.msat_create_config () in
    Mathsat.msat_set_option config "interpolation" "true";
    begin match !interpolation_mode with
      | None -> ()
      | Some mode ->
        let mode = string_of_int mode in
        Mathsat.msat_set_option config "dpll.interpolation_mode" mode;
        Mathsat.msat_set_option config "theory.la.interpolation_mode" mode
    end;
    let msat = Mathsat.msat_create_env config in
    let msat_type =
      let msat_bool = Mathsat.msat_get_bool_type msat in
      let msat_int = Mathsat.msat_get_integer_type msat in
      let msat_rational = Mathsat.msat_get_rational_type msat in
      let rec go = function
        | `TyInt -> msat_int
        | `TyReal -> msat_rational
        | `TyBool -> msat_bool
        | `TyFun (args, ret) ->
          Mathsat.msat_get_function_type msat
            (List.map go (args :> Syntax.typ list))
            (go (ret :> Syntax.typ))
      in
      go
    in
    (* MathSAT declarations carry the ark symbol's name, which is also how
       parse_smtlib2_shared interns symbols, so an interpolant printed by
       MathSAT parses back onto the same ark symbols. *)
    let decl_of_sym =
      Memo.memo (fun sym ->
          Mathsat.msat_declare_function msat
            (Syntax.show_symbol ctx sym)
            (msat_type (Syntax.typ_symbol ctx sym)))
    in
    let of_formula = ArkMathsat.msat_of_formula ctx msat decl_of_sym in
    let groups =
      List.map (fun phi ->
          let group = Mathsat.msat_create_itp_group msat in
          Mathsat.msat_set_itp_group msat group;
          Mathsat.msat_assert_formula msat (of_formula phi);
          group)
        seq
    in
    begin match Mathsat.msat_solve msat with
      | Mathsat.Sat -> `Sat
      | Mathsat.Unknown ->
        begin match smt_ctx#interpolate_seq seq with
          | `Unsat interpolants -> `Unsat interpolants
          | `Sat _ -> `Sat
          | `Unknown -> `Unknown
        end
      | Mathsat.Unsat ->
        let prefix = ref [] in
        let interpolants =
          (* One interpolant per split point: all but the last element. *)
          BatList.take (List.length groups - 1) groups
          |> List.map (fun group ->
              prefix := group :: !prefix;
              Mathsat.msat_get_interpolant msat !prefix
              |> Mathsat.msat_to_smtlib2 msat
              |> parse_smtlib2_shared)
        in
        `Unsat interpolants
    end

let interpolate filename =
  let chunks = BatString.split_on_string ~by:seq_separator (file_contents filename) in
  match chunks with
  | [] | [_] ->
    failwith ("interpolate: " ^ filename ^ " contains no `" ^ seq_separator ^ "' separator")
  | preamble::elements ->
    let seq =
      List.map (fun element -> parse_smtlib2_shared (preamble ^ "\n" ^ element)) elements
    in
    begin match interpolate_seq seq with
      | `Unsat interpolants ->
        Format.printf "(unsat";
        List.iter (fun interpolant ->
            Format.printf "@\n  (interpolant %a)" (SmtlibOut.pp_formula ctx) interpolant)
          interpolants;
        Format.printf ")@\n"
      | `Sat -> Format.printf "(sat)@\n"
      | `Unknown -> Format.printf "(unknown)@\n"
    end

(* Strategy synthesis with machine-readable output.

   Same computation as -synth on an .smt2 file, but the winning strategy is
   printed as an s-expression over SMT-LIB2 formulas instead of being
   pretty-printed for a human reader.  The quantifier prefix is printed
   alongside it: the strategy tree has one level per move of the winning
   player, and the prefix says which variable each level decides. *)
let strategy filename =
  let phi =
    parse_smtlib2_shared (file_contents filename)
    |> Syntax.eliminate_ite ctx
  in
  let (qf_pre, matrix) = Quantifier.normalize ctx phi in
  let pp_prefix formatter =
    List.iter (fun (quantifier, sym) ->
        Format.fprintf formatter "@\n  (%s %s %a)"
          (match quantifier with `Exists -> "exists" | `Forall -> "forall")
          (SmtlibOut.symbol_name ctx sym)
          SmtlibOut.pp_typ (match Syntax.typ_symbol ctx sym with
              | `TyFun (_, _) -> invalid_arg "strategy: function-typed quantifier"
              | (`TyInt | `TyReal | `TyBool) as typ -> typ))
      qf_pre
  in
  let rec pp_strategy formatter (Quantifier.Strategy cases) =
    Format.fprintf formatter "(strategy";
    List.iter (fun (guard, move, sub_strategy) ->
        Format.fprintf formatter "@\n(case %a %a %a)"
          (SmtlibOut.pp_formula ctx) guard
          (SmtlibOut.pp ctx) move
          pp_strategy sub_strategy)
      cases;
    Format.fprintf formatter ")"
  in
  let print_strategy winner strategy =
    Format.printf "(%s@\n (prefix%t)@\n %a)@\n"
      winner
      pp_prefix
      pp_strategy strategy
  in
  match Quantifier.winning_strategy ctx qf_pre matrix with
  | `Sat strategy -> print_strategy "sat" strategy
  | `Unsat strategy -> print_strategy "unsat" strategy
  | `Unknown -> Format.printf "(unknown)@\n"

let load_reachability_game filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try ArkParse.game ArkLex.game_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let synthesize_strategy filename =
  if Filename.check_suffix filename "rg" then
    let module M = Syntax.Symbol.Map in
    let (vars, primed_vars, start, safe, reach) =
      load_reachability_game filename
    in
    let map =
      List.fold_left2
        (fun map x x' ->
           M.add x (Ctx.mk_const x')
             (M.add x' (Ctx.mk_const x) map))
        M.empty
        vars
        primed_vars
    in
    let reach =
      Syntax.substitute_const ctx (fun x -> M.find x map) reach
    in
    begin
      match Game.solve ctx (vars, primed_vars) ~start ~safe ~reach with
      | None ->
        Format.printf "Reachability player wins.@\n"
      | Some strategy ->
        Format.printf "Winning strategy:@\n%a@\n" Game.GameTree.pp strategy;
        Format.printf "Safety player wins.@\n";
        if !validate then begin
          Format.printf "Validating strategy... ";
          if Game.GameTree.well_labeled strategy then
            Format.printf "ok.@\n"
          else
            Format.printf "error!@\n"
        end
    end
  else if Filename.check_suffix filename "smt2" then
    let phi =
      load_smtlib2 filename
      |> Syntax.eliminate_ite ctx
    in
    let (qf_pre, matrix) = Quantifier.normalize ctx phi in
    begin
      match Quantifier.winning_strategy ctx qf_pre matrix with
      | `Sat strategy ->
        Format.printf "Sat player wins:@\n%a@\n"
          (Quantifier.pp_strategy ctx) strategy;
        if !validate then begin
          Format.printf "Validating strategy... ";
          match Quantifier.check_strategy ctx qf_pre phi strategy with
          | `Valid -> Format.printf "ok.@\n"
          | `Invalid -> Format.printf "error!@\n"
          | `Unknown -> Format.printf "inconclusive.@\n"
        end

      | `Unsat strategy ->
        Format.printf "Unsat player wins:@\n%a@\n"
          (Quantifier.pp_strategy ctx) strategy

      | `Unknown ->
        Format.printf "Could not find winning strategy!"
    end
  else Log.fatalf "Unrecognized file extension for %s" filename

let print_result = function
  | `Sat -> Log.logf ~level:`always "sat"
  | `Unsat -> Log.logf ~level:`always "unsat"
  | `Unknown -> Log.logf ~level:`always "unknown"

let sat filename =
  let phi = load_smtlib2 filename in
  print_result (Quantifier.simsat_forward ctx phi)

let spec_list = [
  ("-sat", Arg.String sat, " Test satisfiability");
  ("-synth", Arg.String synthesize_strategy, " Synthesizing a winning strategy");
  ("-validate", Arg.Set validate, " Validate winning strategy");

  ("-strategy", Arg.String strategy,
   " Synthesize a winning strategy for a satisfiability game, printing it as \
    an s-expression over SMT-LIB2 formulas");
  ("-interpolation-mode",
   Arg.Int (fun mode -> interpolation_mode := Some mode),
   " Which interpolant to prefer when several would do: 0 strongest \
     (McMillan), 1 symmetric, 2 weakest (inverse McMillan)");
  ("-interpolate", Arg.String interpolate,
   " Compute a sequence interpolant for a `;;;SEQ;;;'-separated sequence of \
    SMT-LIB2 formulas");

  ("-verbosity",
   Arg.String (fun v -> Log.verbosity_level := (Log.level_of_string v)),
   " Set verbosity level (higher = more verbose; defaults to 0)");

  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v `info),
   " Raise verbosity for a particular module");

  ("-verbose-list",
   Arg.Unit (fun () ->
       print_endline "Available modules for setting verbosity:";
       Hashtbl.iter (fun k _ ->
           print_endline (" - " ^ k);
         ) Log.loggers;
       exit 0;
     ),
   " List modules which can be used with -verbose")
]

let usage_msg = "SimSat: strategy improvement for logical games\nUsage: simsat [OPTIONS] -sat file.smt2\n       simsat -synth [OPTIONS] file.[rg|smt2]"
let anon_fun s = failwith ("Unknown option: " ^ s)
let () =
  if Array.length Sys.argv == 1 then
    print_endline usage_msg
  else
    Arg.parse (Arg.align spec_list) anon_fun usage_msg

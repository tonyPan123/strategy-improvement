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

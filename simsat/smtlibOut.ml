(* SMT-LIB2 output for ark expressions.

   ark's own pretty-printer (Syntax.Expr.pp) is meant for humans; this one
   emits s-expressions that an SMT-LIB2 parser can read back, so that results
   computed here (interpolants, strategies) can be consumed by another tool. *)

open Ark
open Syntax

(* A name for a symbol that is unique within the ark context and legal as an
   SMT-LIB2 simple symbol.  Symbols that were registered by name (i.e. those
   that came from an input file) keep that name; symbols invented by ark --
   the bound variables introduced by Quantifier.normalize, say -- are
   disambiguated with their id, since several of them may share a name. *)
let symbol_name ctx sym =
  match Syntax.symbol_name ctx sym with
  | Some name -> name
  | None ->
    Printf.sprintf "%s!%d"
      (Syntax.show_symbol ctx sym)
      (Syntax.int_of_symbol sym)

let pp_typ formatter = function
  | `TyInt -> Format.pp_print_string formatter "Int"
  | `TyReal -> Format.pp_print_string formatter "Real"
  | `TyBool -> Format.pp_print_string formatter "Bool"

let pp_zz formatter zz =
  if ZZ.lt zz ZZ.zero then
    Format.fprintf formatter "(- %s)" (ZZ.show (ZZ.negate zz))
  else
    Format.pp_print_string formatter (ZZ.show zz)

let pp_qq formatter qq =
  let num = QQ.numerator qq in
  let den = QQ.denominator qq in
  if ZZ.equal den ZZ.one then pp_zz formatter num
  else Format.fprintf formatter "(/ %a %s)" pp_zz num (ZZ.show den)

(* Print an expression.  [env] maps de Bruijn indices to the names given to
   them by the enclosing quantifiers. *)
let rec pp_expr ctx env formatter (expr : ('a, typ_fo) expr) =
  let open Format in
  let pp_list op args =
    match args with
    | [] -> invalid_arg "pp_expr: empty application"
    | [x] -> pp_expr ctx env formatter x
    | _ ->
      fprintf formatter "(%s" op;
      List.iter (fun x -> fprintf formatter " %a" (pp_expr ctx env) x) args;
      fprintf formatter ")"
  in
  match Syntax.destruct ctx expr with
  | `Real qq -> pp_qq formatter qq
  | `App (sym, []) -> pp_print_string formatter (symbol_name ctx sym)
  | `App (sym, args) ->
    fprintf formatter "(%s" (symbol_name ctx sym);
    List.iter (fun x -> fprintf formatter " %a" (pp_expr ctx env) x) args;
    fprintf formatter ")"
  | `Var (v, _) ->
    (try pp_print_string formatter (Env.find env v)
     with Not_found -> invalid_arg "pp_expr: unbound variable")
  | `Add args -> pp_list "+" (List.map (fun t -> (t :> ('a, typ_fo) expr)) args)
  | `Mul args -> pp_list "*" (List.map (fun t -> (t :> ('a, typ_fo) expr)) args)
  | `Binop (`Div, s, t) ->
    fprintf formatter "(/ %a %a)"
      (pp_expr ctx env) (s :> ('a, typ_fo) expr)
      (pp_expr ctx env) (t :> ('a, typ_fo) expr)
  | `Binop (`Mod, s, t) ->
    fprintf formatter "(mod %a %a)"
      (pp_expr ctx env) (s :> ('a, typ_fo) expr)
      (pp_expr ctx env) (t :> ('a, typ_fo) expr)
  | `Unop (`Floor, t) ->
    fprintf formatter "(to_int %a)" (pp_expr ctx env) (t :> ('a, typ_fo) expr)
  | `Unop (`Neg, t) ->
    fprintf formatter "(- %a)" (pp_expr ctx env) (t :> ('a, typ_fo) expr)
  | `Ite (cond, s, t) ->
    fprintf formatter "(ite %a %a %a)"
      (pp_expr ctx env) (cond :> ('a, typ_fo) expr)
      (pp_expr ctx env) s
      (pp_expr ctx env) t
  | `Tru -> pp_print_string formatter "true"
  | `Fls -> pp_print_string formatter "false"
  | `And [] -> pp_print_string formatter "true"
  | `Or [] -> pp_print_string formatter "false"
  | `And args -> pp_list "and" (List.map (fun t -> (t :> ('a, typ_fo) expr)) args)
  | `Or args -> pp_list "or" (List.map (fun t -> (t :> ('a, typ_fo) expr)) args)
  | `Not phi ->
    fprintf formatter "(not %a)" (pp_expr ctx env) (phi :> ('a, typ_fo) expr)
  | `Quantify (qt, name, typ, body) ->
    (* Give the bound variable a name that cannot collide with an enclosing
       one, since SMT-LIB2 scoping is by name rather than by index. *)
    let name = Printf.sprintf "%s!b%d" name (BatEnum.count (Env.enum env)) in
    let quantifier = match qt with
      | `Exists -> "exists"
      | `Forall -> "forall"
    in
    fprintf formatter "(%s ((%s %a)) %a)"
      quantifier
      name
      pp_typ typ
      (pp_expr ctx (Env.push name env)) (body :> ('a, typ_fo) expr)
  | `Atom (op, s, t) ->
    let op = match op with
      | `Eq -> "="
      | `Leq -> "<="
      | `Lt -> "<"
    in
    fprintf formatter "(%s %a %a)"
      op
      (pp_expr ctx env) (s :> ('a, typ_fo) expr)
      (pp_expr ctx env) (t :> ('a, typ_fo) expr)
  | `Proposition (`Var v) ->
    (try pp_print_string formatter (Env.find env v)
     with Not_found -> invalid_arg "pp_expr: unbound propositional variable")
  | `Proposition (`App (sym, [])) ->
    pp_print_string formatter (symbol_name ctx sym)
  | `Proposition (`App (_, _::_)) ->
    (* An applied predicate symbol.  These do not arise in the linear
       arithmetic games this printer is used for, and the type ark gives to
       the arguments of `Proposition does not permit printing them. *)
    invalid_arg "pp_expr: applied predicate symbol"

let pp (ctx : 'a context) formatter (expr : ('a, typ_fo) expr) =
  pp_expr ctx Env.empty formatter expr

let pp_formula (ctx : 'a context) formatter (phi : 'a formula) =
  pp_expr ctx Env.empty formatter (phi :> ('a, typ_fo) expr)

let show ctx expr = ArkUtil.mk_show (fun formatter -> pp ctx formatter) expr

(* Declarations for every symbol that occurs in [exprs], so that the consumer
   can parse the printed expressions without knowing the input file. *)
let pp_declarations ctx formatter exprs =
  let symbols =
    List.fold_left
      (fun set expr -> Symbol.Set.union set (Syntax.symbols expr))
      Symbol.Set.empty
      exprs
  in
  Symbol.Set.iter (fun sym ->
      match typ_symbol ctx sym with
      | `TyFun (_, _) -> ()
      | (`TyInt | `TyReal | `TyBool) as typ ->
        Format.fprintf formatter "(declare-fun %s () %a)@\n"
          (symbol_name ctx sym)
          pp_typ typ)
    symbols

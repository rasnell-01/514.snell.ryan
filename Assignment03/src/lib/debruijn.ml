(* debruijn.ml

   Analysis question 10 asks how the named AST could be translated to de
   Bruijn indices instead.  It is an essay question, but the answer is
   short enough to write down and check, so this module does both: it
   translates, and it evaluates the translated form with a positional
   environment.

   A variable becomes the number of binders between its use and the
   binder that bound it, and the binder keeps no name at all:

     fun x -> fun y -> x + y    becomes    fun. fun. (#1 + #0)

   Two consequences are worth seeing in the tests.  Alpha-equivalent
   programs translate to *identical* terms, so comparing them is
   ordinary structural equality rather than the renaming procedure from
   Assignment 2.  And shadowing needs no special handling, because an
   inner binder simply occupies index 0.

   Nothing else in the project depends on this module. *)

open Ast

type dexpr =
  | DInt of int
  | DBool of bool
  | DVar of int (* 0 is the innermost enclosing binder *)
  | DNeg of dexpr
  | DBinop of binop * dexpr * dexpr
  | DIf of dexpr * dexpr * dexpr
  | DLet of dexpr * dexpr (* the body sits under one more binder *)
  | DLetRec of dexpr * dexpr (* the function, then the body *)
  | DFun of dexpr (* the parameter name is gone *)
  | DApp of dexpr * dexpr

exception Unbound of string

(* The context is the list of names currently in scope, innermost
   first, so a name's index is just its position in that list. *)
let index_of name context =
  let rec walk i = function
    | [] -> raise (Unbound name)
    | name' :: rest -> if String.equal name name' then i else walk (i + 1) rest
  in
  walk 0 context

let rec translate context expr =
  match expr with
  | Int n -> DInt n
  | Bool b -> DBool b
  | Var name -> DVar (index_of name context)
  | Neg operand -> DNeg (translate context operand)
  | Binop (op, lhs, rhs) -> DBinop (op, translate context lhs, translate context rhs)
  | If (c, t, e) -> DIf (translate context c, translate context t, translate context e)
  | Let (name, bound, body) ->
    (* The bound expression is *not* under the new binder; the body is. *)
    DLet (translate context bound, translate (name :: context) body)
  | LetRec (name, Fun (parameter, body), rest) ->
    (* Inside the function, index 0 is the parameter and index 1 is the
       function's own name; in the rest of the program the name is
       index 0. *)
    DLetRec
      ( translate (parameter :: name :: context) body,
        translate (name :: context) rest )
  | LetRec (name, _, _) -> raise (Unbound ("let rec " ^ name ^ " must bind a function"))
  | Fun (parameter, body) -> DFun (translate (parameter :: context) body)
  | App (fn, arg) -> DApp (translate context fn, translate context arg)

let of_expr expr = translate [] expr

let rec string_of_dexpr = function
  | DInt n -> string_of_int n
  | DBool b -> string_of_bool b
  | DVar i -> "#" ^ string_of_int i
  | DNeg e -> "-" ^ string_of_dexpr e
  | DBinop (op, lhs, rhs) ->
    "(" ^ string_of_dexpr lhs ^ " " ^ symbol_of_binop op ^ " " ^ string_of_dexpr rhs ^ ")"
  | DIf (c, t, e) ->
    "if " ^ string_of_dexpr c ^ " then " ^ string_of_dexpr t ^ " else "
    ^ string_of_dexpr e
  | DLet (bound, body) -> "let. " ^ string_of_dexpr bound ^ " in " ^ string_of_dexpr body
  | DLetRec (fn, body) ->
    "let rec. " ^ string_of_dexpr fn ^ " in " ^ string_of_dexpr body
  | DFun body -> "fun. " ^ string_of_dexpr body
  | DApp (fn, arg) -> "(" ^ string_of_dexpr fn ^ " " ^ string_of_dexpr arg ^ ")"

(* ------------------------------------------------------------------ *)
(* Evaluation.  The environment is now a plain list used positionally:
   [extend] is a cons and [lookup] is [List.nth].  There are no strings
   left to compare in the inner loop, which is the practical reason a
   compiler does this. *)

type dvalue =
  | DVInt of int
  | DVBool of bool
  | DVClosure of dexpr * dvalue list
  | DVRecClosure of dexpr * dvalue list

exception Type_error of string

let string_of_dvalue = function
  | DVInt n -> string_of_int n
  | DVBool b -> string_of_bool b
  | DVClosure _ | DVRecClosure _ -> "<closure>"

(* Deliberately a mirror of [Eval.arithmetic] over the other value
   type, so that the two evaluators can be run against each other on
   the same programs; the tests do exactly that. *)
let arithmetic op lhs rhs =
  match (op, lhs, rhs) with
  | Add, DVInt a, DVInt b -> DVInt (a + b)
  | Sub, DVInt a, DVInt b -> DVInt (a - b)
  | Mul, DVInt a, DVInt b -> DVInt (a * b)
  | Div, DVInt _, DVInt 0 -> raise (Type_error "division by zero")
  | Div, DVInt a, DVInt b -> DVInt (a / b)
  | Lt, DVInt a, DVInt b -> DVBool (a < b)
  | Le, DVInt a, DVInt b -> DVBool (a <= b)
  | Gt, DVInt a, DVInt b -> DVBool (a > b)
  | Ge, DVInt a, DVInt b -> DVBool (a >= b)
  | Eq, DVInt a, DVInt b -> DVBool (a = b)
  | Eq, DVBool a, DVBool b -> DVBool (a = b)
  | Ne, DVInt a, DVInt b -> DVBool (a <> b)
  | Ne, DVBool a, DVBool b -> DVBool (a <> b)
  | _ -> raise (Type_error ("operator " ^ symbol_of_binop op ^ " applied to the wrong types"))

let rec eval env expr =
  match expr with
  | DInt n -> DVInt n
  | DBool b -> DVBool b
  | DVar i -> List.nth env i
  | DNeg operand -> (
    match eval env operand with
    | DVInt n -> DVInt (-n)
    | _ -> raise (Type_error "unary - expects an integer"))
  | DBinop (And, lhs, rhs) -> (
    match eval env lhs with
    | DVBool false -> DVBool false
    | DVBool true -> eval env rhs
    | _ -> raise (Type_error "&& expects a boolean"))
  | DBinop (Or, lhs, rhs) -> (
    match eval env lhs with
    | DVBool true -> DVBool true
    | DVBool false -> eval env rhs
    | _ -> raise (Type_error "|| expects a boolean"))
  | DBinop (op, lhs, rhs) ->
    let left = eval env lhs in
    let right = eval env rhs in
    arithmetic op left right
  | DIf (c, t, e) -> (
    match eval env c with
    | DVBool true -> eval env t
    | DVBool false -> eval env e
    | _ -> raise (Type_error "the condition of if expects a boolean"))
  | DLet (bound, body) -> eval (eval env bound :: env) body
  | DLetRec (fn, rest) -> eval (DVRecClosure (fn, env) :: env) rest
  | DFun body -> DVClosure (body, env)
  | DApp (fn_expr, arg_expr) -> (
    let fn_value = eval env fn_expr in
    let arg_value = eval env arg_expr in
    match fn_value with
    (* Same rule as the named evaluator: extend the closure's own
       environment, not the caller's. *)
    | DVClosure (body, closure_env) -> eval (arg_value :: closure_env) body
    | DVRecClosure (body, closure_env) ->
      (* Index 0 is the parameter, index 1 is the function itself. *)
      eval (arg_value :: fn_value :: closure_env) body
    | _ -> raise (Type_error "attempt to call a non-function"))

let run source = eval [] (of_expr (Parser.parse source))

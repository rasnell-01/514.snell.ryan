(* ast.ml

   The abstract syntax tree produced by the parser.

   Starting from the lecture's expression AST (integers, variables,
   arithmetic, let, if), Question 3 adds [Fun] and [App], and
   Question 2 adds [Neg] for unary minus, the comparison and logical
   operators, and [LetRec]. *)

type binop =
  (* arithmetic *)
  | Add
  | Sub
  | Mul
  | Div
  (* comparison -- Question 2 *)
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne
  (* logical -- Question 2 *)
  | And
  | Or

type expr =
  | Int of int
  | Bool of bool
  | Var of string
  | Neg of expr (* unary ::= "-" unary *)
  | Binop of binop * expr * expr
  | If of expr * expr * expr
  | Let of string * expr * expr
  | LetRec of string * expr * expr (* letrec ::= "let" "rec" ... *)
  | Fun of string * expr (* one parameter; see the note below *)
  | App of expr * expr (* one argument *)

(* A multi-parameter function such as [fun x y -> x + y] is not a
   separate kind of node.  The parser curries it into
   [Fun ("x", Fun ("y", ...))], and the corresponding application
   [f 2 3] into [App (App (f, 2), 3)].  Keeping exactly one parameter
   per [Fun] means the evaluator has exactly one rule for abstraction
   and one for application, no matter how many arguments the source
   text mentions. *)

(* ------------------------------------------------------------------ *)
(* Printing an expression as its AST, in the notation the assignment
   uses: [fun x -> x] prints as [Fun ("x", Var "x")].  Useful in the
   unit tests and in the demo, where the parse tree is the thing under
   discussion. *)

let name_of_binop = function
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Div -> "Div"
  | Lt -> "Lt"
  | Le -> "Le"
  | Gt -> "Gt"
  | Ge -> "Ge"
  | Eq -> "Eq"
  | Ne -> "Ne"
  | And -> "And"
  | Or -> "Or"

let rec string_of_expr expr =
  match expr with
  | Int n -> if n < 0 then Printf.sprintf "Int (%d)" n else Printf.sprintf "Int %d" n
  | Bool b -> Printf.sprintf "Bool %b" b
  | Var name -> Printf.sprintf "Var %S" name
  | Neg e -> Printf.sprintf "Neg (%s)" (string_of_expr e)
  | Binop (op, lhs, rhs) ->
    Printf.sprintf "Binop (%s, %s, %s)" (name_of_binop op) (string_of_expr lhs)
      (string_of_expr rhs)
  | If (c, t, e) ->
    Printf.sprintf "If (%s, %s, %s)" (string_of_expr c) (string_of_expr t)
      (string_of_expr e)
  | Let (name, bound, body) ->
    Printf.sprintf "Let (%S, %s, %s)" name (string_of_expr bound) (string_of_expr body)
  | LetRec (name, bound, body) ->
    Printf.sprintf "LetRec (%S, %s, %s)" name (string_of_expr bound)
      (string_of_expr body)
  | Fun (parameter, body) ->
    Printf.sprintf "Fun (%S, %s)" parameter (string_of_expr body)
  | App (fn, arg) ->
    Printf.sprintf "App (%s, %s)" (string_of_expr fn) (string_of_expr arg)

(* ------------------------------------------------------------------ *)
(* Printing an expression back as source text.  The trace output reads
   much better this way than it does in AST notation, so parentheses
   are inserted only where the precedence of the enclosing operator
   would otherwise change the meaning. *)

let symbol_of_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Eq -> "="
  | Ne -> "<>"
  | And -> "&&"
  | Or -> "||"

(* Precedence levels, loosest to tightest, matching the grammar in
   parser.ml: 0 let/if/fun, 1 logical, 2 comparison, 3 additive,
   4 multiplicative, 5 unary, 6 application, 7 atom. *)
let level_of_binop = function
  | And | Or -> 1
  | Lt | Le | Gt | Ge | Eq | Ne -> 2
  | Add | Sub -> 3
  | Mul | Div -> 4

let parenthesize needed text = if needed then "(" ^ text ^ ")" else text

let rec print_at level expr =
  match expr with
  | Int n -> if n < 0 then "(" ^ string_of_int n ^ ")" else string_of_int n
  | Bool b -> string_of_bool b
  | Var name -> name
  | Neg e -> parenthesize (level > 5) ("-" ^ print_at 5 e)
  | Binop (op, lhs, rhs) ->
    let here = level_of_binop op in
    (* The right operand is printed one level tighter, which is what
       makes the left associativity of [a - b - c] visible. *)
    parenthesize (level > here)
      (print_at here lhs ^ " " ^ symbol_of_binop op ^ " " ^ print_at (here + 1) rhs)
  | App (fn, arg) -> parenthesize (level > 6) (print_at 6 fn ^ " " ^ print_at 7 arg)
  | Fun (parameter, body) ->
    parenthesize (level > 0) ("fun " ^ parameter ^ " -> " ^ print_at 0 body)
  | If (c, t, e) ->
    parenthesize (level > 0)
      ("if " ^ print_at 0 c ^ " then " ^ print_at 0 t ^ " else " ^ print_at 0 e)
  | Let (name, bound, body) ->
    parenthesize (level > 0)
      ("let " ^ name ^ " = " ^ print_at 0 bound ^ " in " ^ print_at 0 body)
  | LetRec (name, bound, body) ->
    parenthesize (level > 0)
      ("let rec " ^ name ^ " = " ^ print_at 0 bound ^ " in " ^ print_at 0 body)

let to_source expr = print_at 0 expr

(* A one-line form for tracing, so that a large [let] body does not
   push the interesting part of the trace off the screen. *)
let to_source_short ?(width = 46) expr =
  let text = to_source expr in
  let text =
    String.map (function '\n' | '\t' -> ' ' | c -> c) text
  in
  if String.length text <= width then text else String.sub text 0 width ^ " ..."

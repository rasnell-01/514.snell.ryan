(* Syntax of the Simply Typed Lambda Calculus with Booleans (Part 1). *)

type ty =
  | TyBool
  | TyArrow of ty * ty

type term =
  | Var of string
  | Abs of string * ty * term
  | App of term * term
  | True
  | False
  | If of term * term * term

(* Types are compared structurally: two types are equal exactly when they
   have the same shape. *)
let equal_ty (a : ty) (b : ty) : bool = a = b

(* Arrow is right-associative, so only an arrow on the LEFT of an arrow
   needs parentheses: (Bool -> Bool) -> Bool -> Bool. *)
let rec string_of_ty = function
  | TyBool -> "Bool"
  | TyArrow (a, b) ->
    let left =
      match a with
      | TyArrow _ -> "(" ^ string_of_ty a ^ ")"
      | TyBool -> string_of_ty a
    in
    left ^ " -> " ^ string_of_ty b

let paren s = "(" ^ s ^ ")"

(* Terms print in the same notation used in the assignment text. *)
let rec string_of_term = function
  | Var x -> x
  | True -> "true"
  | False -> "false"
  | Abs (x, ty, body) ->
    "lambda " ^ x ^ ":" ^ string_of_ty ty ^ "." ^ string_of_term body
  | App (f, a) -> string_of_fun f ^ " " ^ string_of_arg a
  | If (c, t, e) ->
    "if " ^ string_of_term c ^ " then " ^ string_of_term t ^ " else "
    ^ string_of_term e

(* Function position of an application: abstractions and conditionals
   extend as far right as possible, so they need parentheses. *)
and string_of_fun = function
  | (Abs _ | If _) as t -> paren (string_of_term t)
  | t -> string_of_term t

(* Argument position: anything that is not an atom needs parentheses. *)
and string_of_arg = function
  | (Var _ | True | False) as t -> string_of_term t
  | t -> paren (string_of_term t)

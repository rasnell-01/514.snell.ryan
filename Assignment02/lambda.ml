(* Assignment 02 - Untyped Lambda Calculus
   AST definition + small functions over lambda terms. *)

type term =
  | Var of string
  | Abs of string * term
  | App of term * term

(* ----------------------------------------------------------------- *)
(* Question 7 - Translate  lambda x.(x y)  into the OCaml AST above.  *)
(* ----------------------------------------------------------------- *)
let q7_example : term =
  Abs ("x", App (Var "x", Var "y"))

(* ----------------------------------------------------------------- *)
(* Question 8 - Translate  lambda x.lambda y.x  into the OCaml AST.   *)
(* ----------------------------------------------------------------- *)
let q8_example : term =
  Abs ("x", Abs ("y", Var "x"))

(* ----------------------------------------------------------------- *)
(* Question 15A - Count every Var / Abs / App node as one node.      *)
(* ----------------------------------------------------------------- *)
let rec size (t : term) : int =
  match t with
  | Var _ -> 1
  | Abs (_, body) -> 1 + size body
  | App (t1, t2) -> 1 + size t1 + size t2

(* ----------------------------------------------------------------- *)
(* Question 15B - Only abstractions count as values.                 *)
(* ----------------------------------------------------------------- *)
let is_value (t : term) : bool =
  match t with
  | Abs (_, _) -> true
  | _ -> false

(* ----------------------------------------------------------------- *)
(* Pretty-printer, used only by bin/main.ml to display terms.        *)
(* ----------------------------------------------------------------- *)
let rec to_string (t : term) : string =
  match t with
  | Var x -> x
  | Abs (x, body) -> Printf.sprintf "\\%s.%s" x (to_string body)
  | App (t1, t2) ->
    Printf.sprintf "(%s %s)" (to_string t1) (to_string t2)

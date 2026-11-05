(* Abstract syntax for the simply typed lambda calculus with Booleans,
   natural numbers, Top, records, subtyping, ascription, and let.

   Assignment09 change: a lambda parameter annotation is now optional.
   [Abs (x, Some t, body)] is "lambda x:T. body" and
   [Abs (x, None, body)] is "lambda x. body". The type grammar is unchanged:
   every annotation the programmer writes is a complete type, so no
   inference-variable constructor is needed. *)

type ty =
  | TyBool
  | TyNat
  | TyTop
  | TyArrow of ty * ty
  | TyRecord of (string * ty) list

type term =
  | Var of string
  | True
  | False
  | Zero
  | Succ of term
  | Pred of term
  | IsZero of term
  | If of term * term * term
  | Abs of string * ty option * term
  | App of term * term
  | Record of (string * term) list
  | Proj of term * string
  | Ascribe of term * ty
  | Let of string * term * term

(* Returns the first label that occurs twice, if any. Shared by the parser
   and the type checker so duplicate labels are rejected however an AST is
   built. *)
let find_duplicate (labels : string list) : string option =
  let rec go seen = function
    | [] -> None
    | l :: rest -> if List.mem l seen then Some l else go (l :: seen) rest
  in
  go [] labels

(* A numeric literal n is shorthand for n applications of succ to 0. *)
let rec nat_literal n = if n <= 0 then Zero else Succ (nat_literal (n - 1))

(* ---- Printing types ------------------------------------------------- *)

(* Arrows associate to the right, so only an arrow on the left of another
   arrow needs parentheses. *)
let rec string_of_ty = function
  | TyBool -> "Bool"
  | TyNat -> "Nat"
  | TyTop -> "Top"
  | TyArrow (a, b) -> string_of_ty_atom a ^ " -> " ^ string_of_ty b
  | TyRecord fields ->
    "{"
    ^ String.concat ", "
        (List.map (fun (l, t) -> l ^ ":" ^ string_of_ty t) fields)
    ^ "}"

and string_of_ty_atom t =
  match t with
  | TyArrow _ -> "(" ^ string_of_ty t ^ ")"
  | _ -> string_of_ty t

(* ---- Printing terms ------------------------------------------------- *)

(* Precedence levels, loosest first, matching the parser:
     term     lambda, let, if (their bodies extend as far right as possible)
     ascr     app {as Type}
     app      application and succ/pred/iszero
     postfix  projection t.l
     atom     variables, constants, records, parenthesized terms
   The output always parses back to the same AST. *)
let rec string_of_term t =
  match t with
  | Abs (x, None, body) -> "lambda " ^ x ^ ". " ^ string_of_term body
  | Abs (x, Some ty, body) ->
    "lambda " ^ x ^ ":" ^ string_of_ty_atom ty ^ ". " ^ string_of_term body
  | Let (x, e1, e2) ->
    "let " ^ x ^ " = " ^ string_of_term e1 ^ " in " ^ string_of_term e2
  | If (c, a, b) ->
    "if " ^ string_of_term c ^ " then " ^ string_of_term a ^ " else "
    ^ string_of_term b
  | _ -> ascr t

and ascr t =
  match t with
  | Ascribe (e, ty) -> ascr e ^ " as " ^ string_of_ty_atom ty
  | _ -> app t

and app t =
  match t with
  | App (f, a) -> app f ^ " " ^ postfix a
  | Succ e -> "succ " ^ postfix e
  | Pred e -> "pred " ^ postfix e
  | IsZero e -> "iszero " ^ postfix e
  | _ -> postfix t

and postfix t =
  match t with
  | Proj (e, l) -> postfix e ^ "." ^ l
  | _ -> atom t

and atom t =
  match t with
  | Var x -> x
  | True -> "true"
  | False -> "false"
  | Zero -> "0"
  | Record fields ->
    "{"
    ^ String.concat ", "
        (List.map (fun (l, e) -> l ^ "=" ^ string_of_term e) fields)
    ^ "}"
  | _ -> "(" ^ string_of_term t ^ ")"

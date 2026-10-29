(* The type checker (Part 4): static semantics.

   [typeof] decides the judgment  Gamma |- t : T  by recursion on t.
   Every case is labeled with the typing rule it implements. *)

open Syntax
open Context

type type_error =
  | UnboundVariable of string
  | ExpectedFunction of ty
  | ArgumentMismatch of { expected : ty; actual : ty }
  | ExpectedBool of ty
  | BranchMismatch of { then_ty : ty; else_ty : ty }

let string_of_type_error = function
  | UnboundVariable x -> Printf.sprintf "unbound variable '%s'" x
  | ExpectedFunction t ->
    Printf.sprintf
      "expected a function type in function position, but found %s"
      (string_of_ty t)
  | ArgumentMismatch { expected; actual } ->
    Printf.sprintf "argument type mismatch: function expects %s but got %s"
      (string_of_ty expected) (string_of_ty actual)
  | ExpectedBool t ->
    Printf.sprintf "condition of 'if' must have type Bool, but found %s"
      (string_of_ty t)
  | BranchMismatch { then_ty; else_ty } ->
    Printf.sprintf
      "branches of 'if' must have the same type, but 'then' has %s and \
       'else' has %s"
      (string_of_ty then_ty) (string_of_ty else_ty)

let ( let* ) = Result.bind

let rec typeof (ctx : context) (t : term) : (ty, type_error) result =
  match t with
  (* T-True:   Gamma |- true : Bool *)
  | True -> Ok TyBool
  (* T-False:  Gamma |- false : Bool *)
  | False -> Ok TyBool
  (* T-Var:    x : T in Gamma   ==>   Gamma |- x : T *)
  | Var x -> (
    match lookup x ctx with
    | Some ty -> Ok ty
    | None -> Error (UnboundVariable x))
  (* T-Abs:    Gamma, x:T1 |- t2 : T2   ==>   Gamma |- lambda x:T1. t2 : T1 -> T2 *)
  | Abs (x, t1, body) ->
    let* t2 = typeof (extend x t1 ctx) body in
    Ok (TyArrow (t1, t2))
  (* T-App:    Gamma |- t1 : T1 -> T2    Gamma |- t2 : T1
               ==>   Gamma |- t1 t2 : T2 *)
  | App (f, a) -> (
    let* tf = typeof ctx f in
    match tf with
    | TyArrow (t1, t2) ->
      let* ta = typeof ctx a in
      if equal_ty t1 ta then Ok t2
      else Error (ArgumentMismatch { expected = t1; actual = ta })
    | other -> Error (ExpectedFunction other))
  (* T-If:     Gamma |- t1 : Bool    Gamma |- t2 : T    Gamma |- t3 : T
               ==>   Gamma |- if t1 then t2 else t3 : T *)
  | If (c, t2, t3) ->
    let* tc = typeof ctx c in
    if not (equal_ty tc TyBool) then Error (ExpectedBool tc)
    else
      let* then_ty = typeof ctx t2 in
      let* else_ty = typeof ctx t3 in
      if equal_ty then_ty else_ty then Ok then_ty
      else Error (BranchMismatch { then_ty; else_ty })

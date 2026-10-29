(* Evaluator (Part 7): dynamic semantics.

   This module does not use the type checker and the type checker does not
   use it. A term can be evaluated without being typed, and typed without
   being evaluated; the two operations meet only in the demo and tests.

   The evaluator is call-by-value, small-step, and uses capture-avoiding
   substitution. Type annotations on lambdas are carried along but play no
   role in evaluation. *)

open Syntax
module S = Set.Make (String)

let rec free_vars = function
  | Var x -> S.singleton x
  | True | False -> S.empty
  | Abs (x, _, body) -> S.remove x (free_vars body)
  | App (a, b) -> S.union (free_vars a) (free_vars b)
  | If (a, b, c) -> S.union (free_vars a) (S.union (free_vars b) (free_vars c))

let rec fresh x avoid = if S.mem x avoid then fresh (x ^ "'") avoid else x

(* [subst x s t] = t[x := s], renaming a binder when it would capture. *)
let rec subst x s t =
  match t with
  | Var y -> if y = x then s else t
  | True | False -> t
  | App (a, b) -> App (subst x s a, subst x s b)
  | If (a, b, c) -> If (subst x s a, subst x s b, subst x s c)
  | Abs (y, ty, body) ->
    if y = x then t
    else if S.mem y (free_vars s) then
      let avoid = S.add x (S.union (free_vars s) (free_vars body)) in
      let y' = fresh y avoid in
      Abs (y', ty, subst x s (subst y (Var y') body))
    else Abs (y, ty, subst x s body)

let is_value = function Abs _ | True | False -> true | _ -> false

(* One step of call-by-value evaluation, or None if the term is a value or
   is stuck (stuck terms are exactly the ones the type checker rejects). *)
let rec step (t : term) : term option =
  match t with
  | App (Abs (x, _, body), v) when is_value v -> Some (subst x v body)
  | App (f, a) when is_value f -> (
    match step a with Some a' -> Some (App (f, a')) | None -> None)
  | App (f, a) -> (
    match step f with Some f' -> Some (App (f', a)) | None -> None)
  | If (True, t2, _) -> Some t2
  | If (False, _, t3) -> Some t3
  | If (c, t2, t3) -> (
    match step c with Some c' -> Some (If (c', t2, t3)) | None -> None)
  | Var _ | Abs _ | True | False -> None

(* Ill-typed terms such as (lambda x:Bool. x x) can loop forever, so the
   evaluator gives up after a fixed number of steps. Well-typed terms
   always reach a value long before this. *)
let max_steps = 10_000

let eval (t : term) : term =
  let rec go n t =
    if n >= max_steps then t
    else match step t with Some t' -> go (n + 1) t' | None -> t
  in
  go 0 t

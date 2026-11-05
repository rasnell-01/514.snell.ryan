(* Call-by-value evaluator with closures and lexical scope.

   Parameter annotations have no runtime role: annotated and unannotated
   lambdas build the same closure. Ascriptions evaluate their operand
   unchanged. Record fields are evaluated left to right, and a record keeps
   every field at run time even when its static type exposes fewer. *)

open Syntax

type value =
  | VBool of bool
  | VNat of int
  | VClosure of string * term * env
  | VRecord of (string * value) list

and env = (string * value) list

exception Runtime_error of string

(* Counts top-level evaluations, so tests can confirm that a program with a
   static error is never run. *)
let evaluations = ref 0

let stuck what = raise (Runtime_error ("evaluation is stuck: " ^ what))

let rec eval_in (env : env) (t : term) : value =
  match t with
  | Var x -> (
    match List.assoc_opt x env with Some v -> v | None -> stuck ("unbound " ^ x))
  | True -> VBool true
  | False -> VBool false
  | Zero -> VNat 0
  | Succ t1 -> (
    match eval_in env t1 with VNat n -> VNat (n + 1) | _ -> stuck "succ of a non-number")
  | Pred t1 -> (
    match eval_in env t1 with
    | VNat n -> VNat (max 0 (n - 1))
    | _ -> stuck "pred of a non-number")
  | IsZero t1 -> (
    match eval_in env t1 with
    | VNat n -> VBool (n = 0)
    | _ -> stuck "iszero of a non-number")
  | If (c, a, b) -> (
    match eval_in env c with
    | VBool true -> eval_in env a
    | VBool false -> eval_in env b
    | _ -> stuck "if on a non-Boolean")
  | Abs (x, _, body) -> VClosure (x, body, env)
  | App (f, a) -> (
    let vf = eval_in env f in
    let va = eval_in env a in
    match vf with
    | VClosure (x, body, cenv) -> eval_in ((x, va) :: cenv) body
    | _ -> stuck "application of a non-function")
  | Record fields ->
    (* Explicit left-to-right order; List.map's order is unspecified. *)
    let rec go acc = function
      | [] -> VRecord (List.rev acc)
      | (l, ti) :: rest ->
        let v = eval_in env ti in
        go ((l, v) :: acc) rest
    in
    go [] fields
  | Proj (t1, l) -> (
    match eval_in env t1 with
    | VRecord fs -> (
      match List.assoc_opt l fs with Some v -> v | None -> stuck ("no field " ^ l))
    | _ -> stuck "projection from a non-record")
  | Ascribe (t1, _) -> eval_in env t1
  | Let (x, e1, e2) ->
    let v = eval_in env e1 in
    eval_in ((x, v) :: env) e2

let eval (t : term) : value =
  incr evaluations;
  eval_in [] t

let rec string_of_value = function
  | VBool b -> string_of_bool b
  | VNat n -> string_of_int n
  | VClosure (x, body, _) -> "<closure lambda " ^ x ^ ". " ^ string_of_term body ^ ">"
  | VRecord fields ->
    "{"
    ^ String.concat ", "
        (List.map (fun (l, v) -> l ^ "=" ^ string_of_value v) fields)
    ^ "}"

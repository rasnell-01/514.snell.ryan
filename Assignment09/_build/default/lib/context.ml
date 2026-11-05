(* Typing contexts: newest binding first, so lookup finds the innermost
   binder and shadowing falls out of List.assoc_opt. *)

open Syntax

type context = (string * ty) list

let empty : context = []

let extend (x : string) (t : ty) (ctx : context) : context = (x, t) :: ctx

let lookup (x : string) (ctx : context) : ty option = List.assoc_opt x ctx

(* Prints only the visible bindings, oldest first: "x:Nat, y:Bool". *)
let to_string (ctx : context) : string =
  let rec visible seen = function
    | [] -> []
    | (x, t) :: rest ->
      if List.mem x seen then visible seen rest
      else (x, t) :: visible (x :: seen) rest
  in
  visible [] ctx |> List.rev
  |> List.map (fun (x, t) -> x ^ ":" ^ string_of_ty t)
  |> String.concat ", "

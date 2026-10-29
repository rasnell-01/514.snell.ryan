(* Typing contexts (Part 2).

   A context Gamma is an association list from names to types. The MOST
   RECENT binding is at the front of the list, and [lookup] returns the
   first match, so an inner binding shadows an outer one with the same name.
   This is exactly lexical scoping. *)

open Syntax

type context = (string * ty) list

let empty_context : context = []

(* Gamma, x : T *)
let extend (x : string) (t : ty) (ctx : context) : context = (x, t) :: ctx

(* x : T in Gamma  (nearest binding wins) *)
let lookup (x : string) (ctx : context) : ty option = List.assoc_opt x ctx

(* Printed outermost-first, the way a context is written on paper:
   f:Bool -> Bool, x:Bool *)
let string_of_context (ctx : context) : string =
  ctx
  |> List.rev
  |> List.map (fun (x, t) -> x ^ ":" ^ string_of_ty t)
  |> String.concat ", "

(* env.ml

   The representation is a plain association list, with the most
   recently added binding at the head.  That makes [extend] O(1) and
   [lookup] O(n), and it makes shadowing fall out for free: a new
   binding is consed onto the front, so [lookup] finds it before it
   ever reaches the old one.

   Because the list is never mutated, an old environment stays valid
   after an [extend].  Sharing the tail means the copy costs one cons
   cell, not a full copy of the list. *)

type 'a t = (string * 'a) list

let empty = []

let extend name value env = (name, value) :: env

let rec lookup name env =
  match env with
  | [] -> None
  | (name', value) :: rest ->
    if String.equal name name' then Some value else lookup name rest

let is_bound name env =
  match lookup name env with Some _ -> true | None -> false

let of_list pairs =
  List.fold_left (fun env (name, value) -> extend name value env) empty pairs

let bindings env =
  (* Walk from the innermost binding outward, dropping any name that
     has already been seen: that name is shadowed and cannot be
     reached through [lookup]. *)
  let rec walk seen acc = function
    | [] -> List.rev acc
    | (name, value) :: rest ->
      if List.mem name seen then walk seen acc rest
      else walk (name :: seen) ((name, value) :: acc) rest
  in
  walk [] [] env

let to_string string_of_value env =
  let one (name, value) = name ^ " = " ^ string_of_value value in
  "[" ^ String.concat "; " (List.map one (bindings env)) ^ "]"

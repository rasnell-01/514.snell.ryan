(* The subtype relation from Assignment08, unchanged.

     S <: Top                                         (S-Top)
     Bool <: Bool,  Nat <: Nat                        (S-Refl on base types)
     T1 <: S1 and S2 <: T2  ==>  S1->S2 <: T1->T2     (S-Arrow)
     every label l:T of the expected record occurs
     in the actual record at some S with S <: T       (S-Rcd: width,
                                                       depth, permutation)

   The checker in Assignment09 calls [subtype actual expected] in exactly one
   direction: the synthesized type on the left, the expectation on the right. *)

open Syntax

let rec subtype (s : ty) (t : ty) : bool =
  match s, t with
  | _, TyTop -> true
  | TyBool, TyBool | TyNat, TyNat -> true
  | TyArrow (s1, s2), TyArrow (t1, t2) -> subtype t1 s1 && subtype s2 t2
  | TyRecord sf, TyRecord tf ->
    List.for_all
      (fun (l, tl) ->
        match List.assoc_opt l sf with
        | Some sl -> subtype sl tl
        | None -> false)
      tf
  | _ -> false

(* Mutual subtyping: used by the synthesis rule for conditionals. *)
let equiv s t = subtype s t && subtype t s

(* A one-line reason why [subtype s t] fails, for diagnostics. *)
let rec explain (s : ty) (t : ty) : string =
  let str = string_of_ty in
  match s, t with
  | TyArrow (s1, s2), TyArrow (t1, t2) ->
    if not (subtype t1 s1) then
      Printf.sprintf
        "function domains are contravariant, so %s <: %s is required (%s)"
        (str t1) (str s1) (explain t1 s1)
    else
      Printf.sprintf
        "function results are covariant, so %s <: %s is required (%s)"
        (str s2) (str t2) (explain s2 t2)
  | TyRecord sf, TyRecord tf -> (
    let bad =
      List.find_opt
        (fun (l, tl) ->
          match List.assoc_opt l sf with
          | Some sl -> not (subtype sl tl)
          | None -> true)
        tf
    in
    match bad with
    | Some (l, tl) -> (
      match List.assoc_opt l sf with
      | None -> Printf.sprintf "%s has no field %s" (str s) l
      | Some sl ->
        Printf.sprintf "field %s: %s <: %s fails (%s)" l (str sl) (str tl)
          (explain sl tl))
    | None -> Printf.sprintf "%s is not a subtype of %s" (str s) (str t))
  | _ -> Printf.sprintf "%s is not a subtype of %s" (str s) (str t)

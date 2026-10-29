(* Typing derivations (Part 6).

   [Typecheck.typeof] only answers "is there a derivation, and what is the
   conclusion's type?". [derive] builds the derivation (the proof tree)
   itself. There is one constructor per typing rule, using the design
   suggested in the assignment. Each node stores the context of its
   conclusion and the type of its conclusion; the term of the conclusion is
   recovered from the node (see [term_of]). *)

open Syntax
open Context
open Typecheck

type derivation =
  | DTrue of context
  | DFalse of context
  | DVar of context * string * ty
  | DAbs of context * string * ty * derivation * ty
  | DApp of context * derivation * derivation * ty
  | DIf of context * derivation * derivation * derivation * ty

(* ---- Reading a derivation back --------------------------------------- *)

let context_of = function
  | DTrue c | DFalse c -> c
  | DVar (c, _, _) -> c
  | DAbs (c, _, _, _, _) -> c
  | DApp (c, _, _, _) -> c
  | DIf (c, _, _, _, _) -> c

let type_of = function
  | DTrue _ | DFalse _ -> TyBool
  | DVar (_, _, t) -> t
  | DAbs (_, _, _, _, t) -> t
  | DApp (_, _, _, t) -> t
  | DIf (_, _, _, _, t) -> t

(* The term in the conclusion of a node is rebuilt from the node and its
   premises: the premises' conclusions are exactly the subterms. *)
let rec term_of = function
  | DTrue _ -> True
  | DFalse _ -> False
  | DVar (_, x, _) -> Var x
  | DAbs (_, x, t1, d, _) -> Abs (x, t1, term_of d)
  | DApp (_, d1, d2, _) -> App (term_of d1, term_of d2)
  | DIf (_, d1, d2, d3, _) -> If (term_of d1, term_of d2, term_of d3)

let rule_name = function
  | DTrue _ -> "T-True"
  | DFalse _ -> "T-False"
  | DVar _ -> "T-Var"
  | DAbs _ -> "T-Abs"
  | DApp _ -> "T-App"
  | DIf _ -> "T-If"

let premises = function
  | DTrue _ | DFalse _ | DVar _ -> []
  | DAbs (_, _, _, d, _) -> [ d ]
  | DApp (_, d1, d2, _) -> [ d1; d2 ]
  | DIf (_, d1, d2, d3, _) -> [ d1; d2; d3 ]

(* ---- Building derivations -------------------------------------------- *)

(* Same case analysis, in the same order, as [Typecheck.typeof]; the only
   difference is that each case also returns the proof node for its rule. *)
let rec derive (ctx : context) (t : term) :
    (ty * derivation, type_error) result =
  match t with
  (* T-True *)
  | True -> Ok (TyBool, DTrue ctx)
  (* T-False *)
  | False -> Ok (TyBool, DFalse ctx)
  (* T-Var *)
  | Var x -> (
    match lookup x ctx with
    | Some ty -> Ok (ty, DVar (ctx, x, ty))
    | None -> Error (UnboundVariable x))
  (* T-Abs *)
  | Abs (x, t1, body) ->
    let* t2, d = derive (extend x t1 ctx) body in
    let ty = TyArrow (t1, t2) in
    Ok (ty, DAbs (ctx, x, t1, d, ty))
  (* T-App *)
  | App (f, a) -> (
    let* tf, df = derive ctx f in
    match tf with
    | TyArrow (t1, t2) ->
      let* ta, da = derive ctx a in
      if equal_ty t1 ta then Ok (t2, DApp (ctx, df, da, t2))
      else Error (ArgumentMismatch { expected = t1; actual = ta })
    | other -> Error (ExpectedFunction other))
  (* T-If *)
  | If (c, t2, t3) ->
    let* tc, dc = derive ctx c in
    if not (equal_ty tc TyBool) then Error (ExpectedBool tc)
    else
      let* then_ty, d2 = derive ctx t2 in
      let* else_ty, d3 = derive ctx t3 in
      if equal_ty then_ty else_ty then
        Ok (then_ty, DIf (ctx, dc, d2, d3, then_ty))
      else Error (BranchMismatch { then_ty; else_ty })

(* ---- Pretty-printing ------------------------------------------------- *)

(* The judgment at the root of a node, e.g. "x:Bool |- x : Bool". An empty
   context prints as just "|- ...". *)
let string_of_judgment (ctx : context) (t : term) (ty : ty) : string =
  let c = string_of_context ctx in
  (if c = "" then "" else c ^ " ")
  ^ "|- " ^ string_of_term t ^ " : " ^ string_of_ty ty

let judgment_of d = string_of_judgment (context_of d) (term_of d) (type_of d)

let pad_right s w = s ^ String.make (max 0 (w - String.length s)) ' '

let center s w =
  let total = max 0 (w - String.length s) in
  let left = total / 2 in
  String.make left ' ' ^ s ^ String.make (total - left) ' '

let rtrim s =
  let n = ref (String.length s) in
  while !n > 0 && s.[!n - 1] = ' ' do
    decr n
  done;
  String.sub s 0 !n

(* Render a node as a block of equal-width lines: premises side by side on
   top, a bar labeled with the rule name, and the conclusion underneath. *)
let rec render (d : derivation) : string list * int =
  let concl = judgment_of d in
  let blocks = List.map render (premises d) in
  let height =
    List.fold_left (fun m (ls, _) -> max m (List.length ls)) 0 blocks
  in
  (* Bottom-align premise blocks so their conclusions sit on one row. *)
  let aligned =
    List.map
      (fun (ls, w) ->
        List.init (height - List.length ls) (fun _ -> String.make w ' ') @ ls)
      blocks
  in
  let gap = "    " in
  let prem_width =
    match blocks with
    | [] -> 0
    | _ ->
      List.fold_left (fun s (_, w) -> s + w) 0 blocks
      + (String.length gap * (List.length blocks - 1))
  in
  let prem_lines =
    List.init height (fun i ->
        String.concat gap (List.map (fun b -> List.nth b i) aligned))
  in
  let bar_width = max prem_width (String.length concl) in
  let label = " " ^ rule_name d in
  let total = bar_width + String.length label in
  let lines =
    List.map (fun l -> pad_right (center l bar_width) total) prem_lines
    @ [ String.make bar_width '-' ^ label; pad_right (center concl bar_width) total ]
  in
  (lines, total)

let string_of_derivation (d : derivation) : string =
  let lines, _ = render d in
  lines |> List.map rtrim |> String.concat "\n"

(* ---- Reporting failed derivations ------------------------------------ *)

let rule_of_term = function
  | True -> "T-True"
  | False -> "T-False"
  | Var _ -> "T-Var"
  | Abs _ -> "T-Abs"
  | App _ -> "T-App"
  | If _ -> "T-If"

(* The innermost, leftmost subterm where typing gets stuck, together with
   the context it was being checked in. Subterms are tried first, so the
   report points at the real cause rather than at the enclosing term. *)
let rec first_failure (ctx : context) (t : term) :
    (context * term * type_error) option =
  let ( <|> ) a b = match a with Some _ -> a | None -> b () in
  let in_subterms =
    match t with
    | True | False | Var _ -> None
    | Abs (x, ty, body) -> first_failure (extend x ty ctx) body
    | App (f, a) ->
      first_failure ctx f <|> fun () -> first_failure ctx a
    | If (c, t2, t3) ->
      first_failure ctx c
      <|> fun () ->
      first_failure ctx t2 <|> fun () -> first_failure ctx t3
  in
  in_subterms
  <|> fun () ->
  match typeof ctx t with
  | Ok _ -> None
  | Error e -> Some (ctx, t, e)

let explain_failure (ctx : context) (t : term) : string =
  match first_failure ctx t with
  | None -> "no type error found"
  | Some (c, sub, e) ->
    let ctx_text = if c = [] then "(empty)" else string_of_context c in
    String.concat "\n"
      [ "Type error: no derivation exists for the judgment";
        "  " ^ (if string_of_context ctx = "" then "" else string_of_context ctx ^ " ")
        ^ "|- " ^ string_of_term t ^ " : ?";
        "Rule " ^ rule_of_term sub ^ " cannot be applied to the subterm";
        "  " ^ string_of_term sub;
        "in context: " ^ ctx_text;
        "Reason: " ^ string_of_type_error e ]

(* Success: the proof tree. Failure: where and why the proof gets stuck. *)
let report (ctx : context) (t : term) : string =
  match derive ctx t with
  | Ok (_, d) -> string_of_derivation d
  | Error _ -> explain_failure ctx t

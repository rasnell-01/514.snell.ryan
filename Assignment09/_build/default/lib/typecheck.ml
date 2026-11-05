(* Bidirectional type checking with subtyping.

   Two mutually recursive judgments:

     synth   G |- e => T     compute a type from e and the context G
     check   G |- e <= T     confirm that e has the expected type T, using T
                             to supply omitted lambda annotations

   Checking returns no type: the answer is yes or no. When no specialized
   checking rule applies, checking falls back to subsumption:

     G |- e => S    S <: T
     ---------------------  (C-Sub)
          G |- e <= T

   Every rule below is labeled with the name it prints under --trace-types. *)

open Syntax

let ( let* ) = Result.bind

(* ---- Where in the program an error happened ------------------------- *)

type frame =
  | Ascription_operand of ty
  | Lambda_body of string
  | App_function
  | App_argument
  | Required_field of string
  | Extra_field of string
  | Record_field of string
  | If_condition
  | Then_branch
  | Else_branch
  | Let_binding of string
  | Let_body of string
  | Operand of string
  | Projection_receiver of string

let string_of_frame = function
  | Ascription_operand ty -> "ascription to " ^ string_of_ty ty
  | Lambda_body x -> "lambda " ^ x ^ " body"
  | App_function -> "function of application"
  | App_argument -> "argument of application"
  | Required_field l -> "field " ^ l
  | Extra_field l -> "extra field " ^ l ^ " (not in the expected interface)"
  | Record_field l -> "field " ^ l
  | If_condition -> "if condition"
  | Then_branch -> "then branch"
  | Else_branch -> "else branch"
  | Let_binding x -> "let binding of " ^ x
  | Let_body x -> "body of let " ^ x
  | Operand op -> "operand of " ^ op
  | Projection_receiver l -> "receiver of ." ^ l

(* ---- Errors ---------------------------------------------------------- *)

(* Not enough static information: a more powerful system might accept the
   program, but this algorithm refuses to guess. *)
type missing_info =
  | Unannotated_lambda of { param : string; lam : term }
      (* "lambda x. e" reached synthesis, which has no expected type *)
  | No_function_domain of { param : string; lam : term }
      (* "lambda x. e" checked against Top, which names no domain *)

(* The information is present and it contradicts itself. *)
type incompatibility =
  | Not_subtype of { actual : ty; expected : ty }
  | Expected_function of ty
  | Expected_record of ty
  | No_such_field of { label : string; record : ty }
  | Missing_required_field of { label : string; field_ty : ty; interface : ty }
  | Incompatible_annotation of {
      param : string;
      written : ty;
      expected_domain : ty;
    }
  | Lambda_against_non_function of { param : string; expected : ty }
  | Branch_mismatch of { then_ty : ty; else_ty : ty }

type error_kind =
  | Insufficient_information of missing_info
  | Incompatible_types of incompatibility
  | Unbound_variable of string
  | Duplicate_label of string

(* [path] runs from the outermost frame to the innermost one. *)
type type_error = { kind : error_kind; path : frame list }

let is_missing_info e =
  match e.kind with Insufficient_information _ -> true | _ -> false

let is_incompatible e =
  match e.kind with Incompatible_types _ -> true | _ -> false

let category e =
  match e.kind with
  | Insufficient_information _ -> "insufficient type information"
  | Incompatible_types _ -> "incompatible types"
  | Unbound_variable _ -> "unbound variable"
  | Duplicate_label _ -> "malformed record"

(* Extra explanation for an unannotated lambda, based on the construct
   that sent it to synthesis instead of checking. *)
let why_no_expectation path =
  match List.rev path with
  | App_function :: _ ->
    Some
      "an application synthesizes its function first; the argument is \
       checked afterwards and is never used to infer the function's \
       parameter type"
  | Let_binding x :: _ ->
    Some
      (Printf.sprintf
         "a let binding is synthesized with no expected type; later uses of %s \
          do not flow back into its binding"
         x)
  | Extra_field l :: _ ->
    Some
      (Printf.sprintf
         "field %s is not part of the expected record type, so it is \
          synthesized with no expectation"
         l)
  | Record_field _ :: _ ->
    Some
      "a record with no expected record type synthesizes every field"
  | (Then_branch | Else_branch) :: _ ->
    Some
      "a conditional with no expected type synthesizes both branches"
  | _ -> None

let repair_for param =
  Printf.sprintf
    "annotate parameter %s (lambda %s:T. ...), or ascribe the lambda to a \
     function type ((lambda %s. ...) as (T -> U))"
    param param param

let string_of_error (e : type_error) : string =
  let str = string_of_ty in
  let where =
    match e.path with
    | [] -> "top level"
    | frames -> String.concat " > " (List.map string_of_frame frames)
  in
  let body =
    match e.kind with
    | Insufficient_information (Unannotated_lambda { param; lam }) ->
      [
        Printf.sprintf
          "cannot synthesize a type for %s: parameter %s has no annotation \
           and no expected function type is available"
          (string_of_term lam) param;
      ]
      @ (match why_no_expectation e.path with
        | Some n -> [ "note: " ^ n ]
        | None -> [])
      @ [ "repair: " ^ repair_for param ]
    | Insufficient_information (No_function_domain { param; lam }) ->
      [
        Printf.sprintf
          "cannot check %s against Top: Top supplies no function domain, so \
           the type of parameter %s is unknown"
          (string_of_term lam) param;
        "repair: " ^ repair_for param;
      ]
    | Incompatible_types (Not_subtype { actual; expected }) ->
      [
        Printf.sprintf "expected type %s, but found %s" (str expected)
          (str actual);
        "actual:   " ^ str actual;
        "expected: " ^ str expected;
        "why: " ^ Subtype.explain actual expected;
      ]
    | Incompatible_types (Expected_function ty) ->
      [ "this expression is applied, but its type " ^ str ty
        ^ " is not a function type" ]
    | Incompatible_types (Expected_record ty) ->
      [ "this expression is projected, but its type " ^ str ty
        ^ " is not a record type" ]
    | Incompatible_types (No_such_field { label; record }) ->
      [ Printf.sprintf "type %s has no field %s" (str record) label ]
    | Incompatible_types (Missing_required_field { label; field_ty; interface })
      ->
      [
        Printf.sprintf
          "the record has no field %s, which the expected type %s requires \
           (at type %s)"
          label (str interface) (str field_ty);
      ]
    | Incompatible_types
        (Incompatible_annotation { param; written; expected_domain }) ->
      [
        Printf.sprintf
          "parameter %s is annotated %s, but the expected function type \
           supplies arguments of type %s"
          param (str written) (str expected_domain);
        Printf.sprintf
          "checking an annotated lambda requires expected domain <: written \
           domain, and %s <: %s fails"
          (str expected_domain) (str written);
      ]
    | Incompatible_types (Lambda_against_non_function { param; expected }) ->
      [
        Printf.sprintf
          "lambda %s. ... is checked against %s, but a lambda needs an \
           expected function type"
          param (str expected);
      ]
    | Incompatible_types (Branch_mismatch { then_ty; else_ty }) ->
      [
        Printf.sprintf
          "the branches synthesize %s and %s, which are not mutual subtypes"
          (str then_ty) (str else_ty);
        "repair: ascribe the conditional to a common type, e.g. (if ... ) as T";
      ]
    | Unbound_variable x -> [ "variable " ^ x ^ " is not bound here" ]
    | Duplicate_label l -> [ "label " ^ l ^ " appears more than once" ]
  in
  String.concat "\n"
    (("Type error (" ^ category e ^ ")") :: ("  at: " ^ where)
    :: List.map (fun s -> "  " ^ s) body)

(* ---- Tracing ---------------------------------------------------------- *)

type tracer = { on : bool; mutable lines : string list; mutable depth : int }

let silent () = { on = false; lines = []; depth = 0 }

let emit tr s =
  if tr.on then
    tr.lines <-
      (String.concat "" (List.init tr.depth (fun _ -> "| ")) ^ s) :: tr.lines

let judgment ctx t =
  let c = Context.to_string ctx in
  (if c = "" then "|- " else c ^ " |- ") ^ string_of_term t

let synth_rule = function
  | Var _ -> "T-Var"
  | True -> "T-True"
  | False -> "T-False"
  | Zero -> "T-Zero"
  | Succ _ -> "T-Succ"
  | Pred _ -> "T-Pred"
  | IsZero _ -> "T-IsZero"
  | Abs (_, Some _, _) -> "T-Abs"
  | Abs (_, None, _) -> "T-Abs: parameter has no annotation"
  | App _ -> "T-App"
  | Record _ -> "T-Rcd"
  | Proj _ -> "T-Proj"
  | Ascribe _ -> "T-Ascribe"
  | Let _ -> "T-Let"
  | If _ -> "T-If"

let check_rule t expected =
  match t, expected with
  | Abs (_, None, _), TyArrow _ -> "C-Abs"
  | Abs (_, None, _), _ -> "C-Abs: expected type is not a function type"
  | Abs (_, Some _, _), TyArrow _ -> "C-AbsAnn"
  | Record _, TyRecord _ -> "C-Rcd"
  | If _, _ -> "C-If"
  | Let _, _ -> "C-Let"
  | _ -> "C-Sub"

(* ---- Helpers ---------------------------------------------------------- *)

let fail path kind = Error { kind; path = List.rev path }

let missing path m = fail path (Insufficient_information m)

let incompatible path i = fail path (Incompatible_types i)

(* Types written by the programmer must not repeat a label at any depth. *)
let rec well_formed path (t : ty) : (unit, type_error) result =
  match t with
  | TyBool | TyNat | TyTop -> Ok ()
  | TyArrow (a, b) ->
    let* () = well_formed path a in
    well_formed path b
  | TyRecord fields -> (
    match find_duplicate (List.map fst fields) with
    | Some l -> fail path (Duplicate_label l)
    | None ->
      List.fold_left
        (fun acc (_, ft) ->
          let* () = acc in
          well_formed path ft)
        (Ok ()) fields)

let distinct_fields path fields =
  match find_duplicate (List.map fst fields) with
  | Some l -> fail path (Duplicate_label l)
  | None -> Ok ()

(* ---- The two judgments ------------------------------------------------ *)

(* [path] is built innermost-first while descending and reversed when an
   error is created. *)
let rec synth_t tr path ctx (t : term) : (ty, type_error) result =
  let rule = synth_rule t in
  if tr.on then emit tr (Printf.sprintf "synth %s   [%s]" (judgment ctx t) rule);
  tr.depth <- tr.depth + 1;
  let result = synth_rules tr path ctx t in
  (match result with
  | Ok ty -> emit tr (Printf.sprintf "=> %s   [%s]" (string_of_ty ty) rule)
  | Error _ -> emit tr "failed");
  tr.depth <- tr.depth - 1;
  result

and synth_rules tr path ctx t =
  match t with
  (* T-Var *)
  | Var x -> (
    match Context.lookup x ctx with
    | Some ty -> Ok ty
    | None -> fail path (Unbound_variable x))
  (* T-True, T-False, T-Zero *)
  | True | False -> Ok TyBool
  | Zero -> Ok TyNat
  (* T-Succ, T-Pred, T-IsZero: the operand is checked against Nat *)
  | Succ t1 ->
    let* () = check_t tr (Operand "succ" :: path) ctx t1 TyNat in
    Ok TyNat
  | Pred t1 ->
    let* () = check_t tr (Operand "pred" :: path) ctx t1 TyNat in
    Ok TyNat
  | IsZero t1 ->
    let* () = check_t tr (Operand "iszero" :: path) ctx t1 TyNat in
    Ok TyBool
  (* T-Abs: G, x:S |- e => T  gives  G |- lambda x:S. e => S -> T *)
  | Abs (x, Some s, body) ->
    let* () = well_formed path s in
    let* t2 = synth_t tr (Lambda_body x :: path) (Context.extend x s ctx) body in
    Ok (TyArrow (s, t2))
  (* No synthesis rule for an unannotated lambda. *)
  | Abs (x, None, _) -> missing path (Unannotated_lambda { param = x; lam = t })
  (* T-App: synthesize the function, then CHECK the argument against the
     domain. Checking (not synthesize-then-subtype) is what lets an
     unannotated lambda appear as an argument. *)
  | App (f, a) -> (
    let* tf = synth_t tr (App_function :: path) ctx f in
    match tf with
    | TyArrow (dom, cod) ->
      let* () = check_t tr (App_argument :: path) ctx a dom in
      Ok cod
    | other -> incompatible path (Expected_function other))
  (* T-Rcd: synthesize every field, left to right *)
  | Record fields ->
    let* () = distinct_fields path fields in
    let rec go acc = function
      | [] -> Ok (TyRecord (List.rev acc))
      | (l, ti) :: rest ->
        let* ty = synth_t tr (Record_field l :: path) ctx ti in
        go ((l, ty) :: acc) rest
    in
    go [] fields
  (* T-Proj *)
  | Proj (t1, l) -> (
    let* ty = synth_t tr (Projection_receiver l :: path) ctx t1 in
    match ty with
    | TyRecord fs -> (
      match List.assoc_opt l fs with
      | Some tl -> Ok tl
      | None -> incompatible path (No_such_field { label = l; record = ty }))
    | other -> incompatible path (Expected_record other))
  (* T-Ascribe: G |- e <= T  gives  G |- e as T => T *)
  | Ascribe (t1, ty) ->
    let* () = well_formed path ty in
    let* () = check_t tr (Ascription_operand ty :: path) ctx t1 ty in
    Ok ty
  (* T-Let: the binding is synthesized and bound at that one type
     (monomorphic: no generalization, no instantiation at lookup). *)
  | Let (x, e1, e2) ->
    let* t1 = synth_t tr (Let_binding x :: path) ctx e1 in
    synth_t tr (Let_body x :: path) (Context.extend x t1 ctx) e2
  (* T-If: without an expected type, the branches must be mutual subtypes
     (the Assignment08 policy). *)
  | If (c, a, b) ->
    let* () = check_t tr (If_condition :: path) ctx c TyBool in
    let* ta = synth_t tr (Then_branch :: path) ctx a in
    let* tb = synth_t tr (Else_branch :: path) ctx b in
    let ok = Subtype.equiv ta tb in
    emit tr
      (Printf.sprintf "branches %s and %s mutual subtypes: %s" (string_of_ty ta)
         (string_of_ty tb) (if ok then "yes" else "no"));
    if ok then Ok ta
    else incompatible path (Branch_mismatch { then_ty = ta; else_ty = tb })

and check_t tr path ctx (t : term) (expected : ty) : (unit, type_error) result =
  let rule = check_rule t expected in
  if tr.on then
    emit tr
      (Printf.sprintf "check %s <= %s   [%s]" (judgment ctx t)
         (string_of_ty expected) rule);
  tr.depth <- tr.depth + 1;
  let result = check_rules tr path ctx t expected in
  (match result with
  | Ok () -> emit tr (Printf.sprintf "ok   [%s]" rule)
  | Error _ -> emit tr "failed");
  tr.depth <- tr.depth - 1;
  result

and check_rules tr path ctx t expected =
  match t, expected with
  (* C-Abs: G, x:A |- e <= B  gives  G |- lambda x. e <= A -> B *)
  | Abs (x, None, body), TyArrow (a, b) ->
    emit tr
      (Printf.sprintf "parameter %s has no annotation: take %s:%s from the \
                       expected domain"
         x x (string_of_ty a));
    check_t tr (Lambda_body x :: path) (Context.extend x a ctx) body b
  (* Top names no domain: insufficient information, not a mismatch. *)
  | Abs (x, None, _), TyTop ->
    missing path (No_function_domain { param = x; lam = t })
  (* A lambda can never have a base or record type. *)
  | Abs (x, None, _), _ ->
    incompatible path (Lambda_against_non_function { param = x; expected })
  (* C-AbsAnn: A <: S and G, x:S |- e <= B  give  G |- lambda x:S. e <= A -> B.
     The body is checked under the WRITTEN type S, never under A. *)
  | Abs (x, Some s, body), TyArrow (a, b) ->
    let* () = well_formed path s in
    let ok = Subtype.subtype a s in
    emit tr
      (Printf.sprintf "expected domain %s <: written domain %s: %s"
         (string_of_ty a) (string_of_ty s) (if ok then "holds" else "fails"));
    if not ok then
      incompatible path
        (Incompatible_annotation { param = x; written = s; expected_domain = a })
    else begin
      emit tr (Printf.sprintf "keep the written annotation %s:%s" x (string_of_ty s));
      check_t tr (Lambda_body x :: path) (Context.extend x s ctx) body b
    end
  (* C-Rcd: every expected label must be present and checked against its
     expected type; every extra field is still synthesized. *)
  | Record fields, TyRecord required -> (
    let* () = distinct_fields path fields in
    match List.find_opt (fun (l, _) -> not (List.mem_assoc l fields)) required with
    | Some (l, lt) ->
      incompatible path
        (Missing_required_field { label = l; field_ty = lt; interface = expected })
    | None ->
      let rec go = function
        | [] -> Ok ()
        | (l, ti) :: rest ->
          let* () =
            match List.assoc_opt l required with
            | Some lt -> check_t tr (Required_field l :: path) ctx ti lt
            | None ->
              let* _ = synth_t tr (Extra_field l :: path) ctx ti in
              Ok ()
          in
          go rest
      in
      go fields)
  (* C-If: the expectation flows into both branches; no join is needed. *)
  | If (c, a, b), _ ->
    let* () = check_t tr (If_condition :: path) ctx c TyBool in
    let* () = check_t tr (Then_branch :: path) ctx a expected in
    check_t tr (Else_branch :: path) ctx b expected
  (* C-Let: synthesize the binding; the expectation flows into the body
     only, never backward into the binding. *)
  | Let (x, e1, e2), _ ->
    let* t1 = synth_t tr (Let_binding x :: path) ctx e1 in
    check_t tr (Let_body x :: path) (Context.extend x t1 ctx) e2 expected
  (* C-Sub: synthesize, then require actual <: expected (never reversed). *)
  | _ ->
    let* actual = synth_t tr path ctx t in
    let ok = Subtype.subtype actual expected in
    emit tr
      (Printf.sprintf "%s <: %s: %s" (string_of_ty actual)
         (string_of_ty expected) (if ok then "holds" else "fails"));
    if ok then Ok () else incompatible path (Not_subtype { actual; expected })

(* ---- Public interface ------------------------------------------------- *)

let synth (ctx : Context.context) (t : term) : (ty, type_error) result =
  synth_t (silent ()) [] ctx t

let check (ctx : Context.context) (t : term) (expected : ty) :
    (unit, type_error) result =
  check_t (silent ()) [] ctx t expected

(* Compatibility wrapper kept from earlier assignments. *)
let typeof (ctx : Context.context) (t : term) : (ty, type_error) result =
  synth ctx t

let synth_traced ctx t =
  let tr = { on = true; lines = []; depth = 0 } in
  let r = synth_t tr [] ctx t in
  (r, List.rev tr.lines)

let check_traced ctx t expected =
  let tr = { on = true; lines = []; depth = 0 } in
  let r = check_t tr [] ctx t expected in
  (r, List.rev tr.lines)

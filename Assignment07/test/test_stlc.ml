(* Automated tests (Part 8). Run with: dune runtest
   Any failed check makes the program exit with status 1. *)

open Stlc
open Syntax
open Context
open Typecheck
open Derivation

let failures = ref 0

let check name ok =
  if ok then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let b = TyBool
let arrow x y = TyArrow (x, y)
let typeof0 = typeof empty_context

let id_bool = Abs ("x", b, Var "x")
let id_bool_y = Abs ("y", b, Var "y")
let apply_f = Abs ("f", arrow b b, Abs ("x", b, App (Var "f", Var "x")))

(* ---- Typing context --------------------------------------------------- *)

let () =
  check "context: empty has no bindings" (lookup "x" empty_context = None);
  check "context: extend then lookup"
    (lookup "x" (extend "x" b empty_context) = Some b);
  check "context: lookup of other name fails"
    (lookup "y" (extend "x" b empty_context) = None);
  let shadowed = extend "x" b (extend "x" (arrow b b) empty_context) in
  check "context: inner binding shadows outer" (lookup "x" shadowed = Some b)

(* ---- Required examples (Part 5 / Part 8) ------------------------------ *)

let () =
  check "T-Abs/T-Var: Boolean identity has type Bool -> Bool"
    (typeof0 id_bool = Ok (arrow b b));
  check "T-App: identity applied to true has type Bool"
    (typeof0 (App (id_bool, True)) = Ok b);
  check "higher-order: (Bool -> Bool) -> Bool -> Bool"
    (typeof0 apply_f = Ok (arrow (arrow b b) (arrow b b)));
  check "T-True and T-False" (typeof0 True = Ok b && typeof0 False = Ok b);
  check "T-If: accepts matching branches"
    (typeof0 (If (True, False, True)) = Ok b);
  check "T-If: accepts matching function-typed branches"
    (typeof0 (If (True, id_bool, id_bool_y)) = Ok (arrow b b))

let () =
  check "error: unbound variable"
    (typeof0 (Var "z") = Error (UnboundVariable "z"));
  check "error: applying a Boolean as a function"
    (typeof0 (App (True, False)) = Error (ExpectedFunction b));
  check "error: argument type mismatch"
    (typeof0 (App (id_bool, id_bool_y))
     = Error (ArgumentMismatch { expected = b; actual = arrow b b }));
  check "error: branch type mismatch"
    (typeof0 (If (True, True, id_bool))
     = Error (BranchMismatch { then_ty = b; else_ty = arrow b b }));
  check "error: non-Boolean condition"
    (typeof0 (If (id_bool, True, False)) = Error (ExpectedBool (arrow b b)));
  check "error: unbound variable inside an abstraction body"
    (typeof0 (Abs ("x", b, Var "y")) = Error (UnboundVariable "y"));
  check "error: variable is not in scope outside its binder"
    (typeof0 (App (id_bool, Var "x")) = Error (UnboundVariable "x"))

(* ---- Lexical shadowing in the checker -------------------------------- *)

let () =
  (* lambda x:Bool->Bool. lambda x:Bool. x  -- the body's x is the inner Bool *)
  let inner = Abs ("x", arrow b b, Abs ("x", b, Var "x")) in
  check "shadowing: inner x : Bool wins over outer x : Bool -> Bool"
    (typeof0 inner = Ok (arrow (arrow b b) (arrow b b)));
  (* lambda x:Bool. lambda x:Bool->Bool. x  -- body is a function, not Bool *)
  let inner2 = Abs ("x", b, Abs ("x", arrow b b, Var "x")) in
  check "shadowing: result type follows the innermost binding"
    (typeof0 inner2 = Ok (arrow b (arrow (arrow b b) (arrow b b))));
  (* The outer x must NOT be used once shadowed: applying it would be fine
     for Bool -> Bool but the inner x : Bool is not a function. *)
  let bad = Abs ("x", arrow b b, Abs ("x", b, App (Var "x", True))) in
  check "shadowing: shadowed outer binding is not visible"
    (typeof0 bad = Error (ExpectedFunction b))

(* ---- Derivations ------------------------------------------------------ *)

let contains s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  go 0

let () =
  let t = App (id_bool, True) in
  (match derive empty_context t with
   | Ok (ty, d) ->
     check "derive: type is Bool" (ty = b);
     check "derive: root rule is T-App" (rule_name d = "T-App");
     check "derive: conclusion term is the input term" (term_of d = t);
     check "derive: premises are T-Abs and T-True"
       (List.map rule_name (premises d) = [ "T-Abs"; "T-True" ]);
     (match premises d with
      | [ abs; _ ] ->
        check "derive: T-Abs premise has T-Var premise"
          (List.map rule_name (premises abs) = [ "T-Var" ]);
        check "derive: T-Var premise is under x:Bool"
          (match premises abs with
           | [ v ] -> context_of v = [ ("x", b) ]
           | _ -> false)
      | _ -> check "derive: two premises" false);
     let s = string_of_derivation d in
     check "print: contains x:Bool |- x : Bool" (contains s "x:Bool |- x : Bool");
     check "print: contains abstraction conclusion"
       (contains s "|- lambda x:Bool.x : Bool -> Bool");
     check "print: contains true conclusion" (contains s "|- true : Bool");
     check "print: contains application conclusion"
       (contains s "|- (lambda x:Bool.x) true : Bool");
     List.iter
       (fun r -> check ("print: mentions " ^ r) (contains s r))
       [ "T-Var"; "T-Abs"; "T-True"; "T-App" ]
   | Error _ -> check "derive: succeeds on (lambda x:Bool. x) true" false);
  (* T-If and T-False nodes *)
  (match derive empty_context (If (True, False, True)) with
   | Ok (_, d) ->
     check "derive: T-If root with three premises"
       (rule_name d = "T-If"
        && List.map rule_name (premises d) = [ "T-True"; "T-False"; "T-True" ])
   | Error _ -> check "derive: succeeds on a conditional" false)

let () =
  (* derive and typeof must agree on every term, successes and failures. *)
  let terms =
    [ id_bool; App (id_bool, True); apply_f; App (True, False);
      App (id_bool, id_bool_y); If (True, True, id_bool);
      If (id_bool, True, False); Var "z"; Abs ("x", b, Var "y");
      App (True, Var "y"); If (Var "q", True, False);
      Abs ("x", arrow b b, Abs ("x", b, Var "x")) ]
  in
  check "derive agrees with typeof on every example"
    (List.for_all
       (fun t ->
         match (typeof0 t, derive empty_context t) with
         | Ok a, Ok (b', _) -> a = b'
         | Error e1, Error e2 -> e1 = e2
         | _ -> false)
       terms);
  (* The type in every derivation's root agrees with its own conclusion. *)
  check "derive: root type matches returned type"
    (List.for_all
       (fun t ->
         match derive empty_context t with
         | Ok (ty, d) -> type_of d = ty
         | Error _ -> true)
       terms)

(* ---- Failed derivations ----------------------------------------------- *)

let () =
  let r = report empty_context (App (True, False)) in
  check "failure report: names the rule T-App" (contains r "T-App");
  check "failure report: shows the stuck subterm" (contains r "true false");
  check "failure report: explains the reason"
    (contains r "expected a function type");
  let r2 = report empty_context (App (id_bool, id_bool_y)) in
  check "failure report: argument mismatch mentions both types"
    (contains r2 "expects Bool" && contains r2 "Bool -> Bool");
  (* The report points at the innermost failing subterm, not the whole term. *)
  let nested = Abs ("u", b, If (Var "u", True, id_bool)) in
  let r3 = report empty_context nested in
  check "failure report: points at the innermost failing subterm"
    (contains r3 "Rule T-If cannot be applied"
     && contains r3 "if u then true else lambda x:Bool.x"
     && contains r3 "u:Bool");
  check "failure report: branch mismatch reason"
    (contains r3 "branches of 'if' must have the same type");
  check "failure report: unbound variable"
    (contains (report empty_context (Var "z")) "unbound variable 'z'")

(* ---- Evaluator and the static/dynamic split --------------------------- *)

let () =
  check "eval: identity applied to true is true"
    (Eval.eval (App (id_bool, True)) = True);
  let not_fn = Abs ("b", b, If (Var "b", False, True)) in
  check "eval: not true = false" (Eval.eval (App (not_fn, True)) = False);
  check "eval: higher-order application"
    (Eval.eval (App (App (apply_f, not_fn), False)) = True);
  check "eval: a lambda is already a value" (Eval.eval id_bool = id_bool);
  (* Capture-avoiding substitution: substituting y for z under a binder
     named y must rename the binder. *)
  let t = App (Abs ("z", b, Abs ("y", b, Var "z")), True) in
  check "eval: substitution under a binder"
    (Eval.eval t = Abs ("y", b, True));
  (* (lambda y:Bool. x)[x := y] must rename the binder, giving
     lambda y':Bool. y, not lambda y:Bool. y. *)
  check "eval: subst renames a binder that would capture"
    (Eval.subst "x" (Var "y") (Abs ("y", b, Var "x"))
     = Abs ("y'", b, Var "y"));
  (* Typing and evaluation are separate: an ill-typed term is stuck. *)
  check "eval: ill-typed term gets stuck (no type check involved)"
    (Eval.eval (App (True, False)) = App (True, False));
  check "static vs dynamic: well-typed term reaches a value of the same type"
    (let t = App (App (apply_f, not_fn), True) in
     typeof0 t = Ok b && (Eval.eval t = True || Eval.eval t = False))

(* ---- Printing --------------------------------------------------------- *)

let () =
  check "string_of_ty: left arrow is parenthesized"
    (string_of_ty (arrow (arrow b b) (arrow b b)) = "(Bool -> Bool) -> Bool -> Bool");
  check "string_of_term: application of abstraction"
    (string_of_term (App (id_bool, True)) = "(lambda x:Bool.x) true");
  check "string_of_type_error: unbound variable"
    (string_of_type_error (UnboundVariable "q") = "unbound variable 'q'")

let () =
  if !failures > 0 then begin
    Printf.printf "\n%d test(s) failed\n" !failures;
    exit 1
  end
  else print_endline "\nall tests passed"

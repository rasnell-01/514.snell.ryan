(* Test suite for Assignment09. Run with: dune runtest *)

open Stlc
open Syntax

let passed = ref 0
let failed = ref 0

let check name cond =
  if cond then incr passed
  else begin
    incr failed;
    Printf.printf "FAIL: %s\n" name
  end

let section title = Printf.printf "-- %s\n" title

let contains s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  go 0

let parse = Parser.parse_program
let ty = Parser.parse_type
let synth_src s = Typecheck.synth Context.empty (parse s)
let check_src s t = Typecheck.check Context.empty (parse s) (ty t)

let synth_is name src expected =
  match synth_src src with
  | Ok t -> check name (Subtype.equiv t (ty expected) && string_of_ty t = string_of_ty (ty expected))
  | Error e ->
    check name false;
    print_endline (Typecheck.string_of_error e)

let check_ok name src t =
  match check_src src t with
  | Ok () -> check name true
  | Error e ->
    check name false;
    print_endline (Typecheck.string_of_error e)

let error_of = function Ok _ -> None | Error e -> Some e

let is_missing r = match error_of r with Some e -> Typecheck.is_missing_info e | None -> false

let is_incompatible r =
  match error_of r with Some e -> Typecheck.is_incompatible e | None -> false

let parse_fails src =
  match parse src with
  | _ -> false
  | exception (Parser.Parse_error _ | Lexer.Lex_error _) -> true

let parse_error_mentions src word =
  match parse src with
  | _ -> false
  | exception Parser.Parse_error m -> contains m word
  | exception Lexer.Lex_error _ -> false

let example dir name = Filename.concat (Filename.concat "../examples" dir) name

let run_file path = fst (Driver.run (Driver.read_file path))

let expect_success name path ty_str value_str =
  match run_file path with
  | Driver.Success { ty = t; value; _ } ->
    check (name ^ ": type") (string_of_ty t = ty_str);
    check (name ^ ": value") (Eval.string_of_value value = value_str)
  | Driver.Static_error (_, e) ->
    check (name ^ ": typechecks") false;
    print_endline (Typecheck.string_of_error e)
  | Driver.Syntax_error m ->
    check (name ^ ": parses") false;
    print_endline m
  | Driver.Runtime_failure (_, _, m) ->
    check (name ^ ": runs") false;
    print_endline m

(* Checks the error category and a phrase that must appear in the message. *)
let expect_rejection name path ~missing ~mentions =
  let before = !Eval.evaluations in
  match run_file path with
  | Driver.Static_error (_, e) ->
    check (name ^ ": category")
      (if missing then Typecheck.is_missing_info e else Typecheck.is_incompatible e);
    let msg = Typecheck.string_of_error e in
    List.iter
      (fun phrase ->
        check (Printf.sprintf "%s: message mentions %S" name phrase) (contains msg phrase))
      mentions;
    check (name ^ ": not evaluated") (!Eval.evaluations = before)
  | _ -> check (name ^ ": rejected") false

(* --------------------------------------------------------------------- *)

let () =
  section "Parser and AST";
  check "annotated lambda" (parse "lambda x:Nat. succ x" = Abs ("x", Some TyNat, Succ (Var "x")));
  check "unannotated lambda" (parse "lambda x. succ x" = Abs ("x", None, Succ (Var "x")));
  check "arrow annotation without parens"
    (parse "lambda f:Nat -> Nat. f 0" = Abs ("f", Some (TyArrow (TyNat, TyNat)), App (Var "f", Zero)));
  check "arrow annotation with parens"
    (parse "lambda f:(Nat -> Nat). f 0" = parse "lambda f:Nat -> Nat. f 0");
  check "arrow types are right associative"
    (ty "Nat -> Bool -> Nat" = TyArrow (TyNat, TyArrow (TyBool, TyNat)));
  check "application is left associative"
    (parse "f x y" = App (App (Var "f", Var "x"), Var "y"));
  check "lambda body extends right"
    (parse "lambda x. f x" = Abs ("x", None, App (Var "f", Var "x")));
  check "parenthesized ascription"
    (parse "((lambda x. succ x) as (Nat -> Nat)) 0"
    = App (Ascribe (Abs ("x", None, Succ (Var "x")), TyArrow (TyNat, TyNat)), Zero));
  check "top-level ascription" (parse "(lambda x. x) as Top" = Ascribe (Abs ("x", None, Var "x"), TyTop));
  check "projection binds tighter than application"
    (parse "f r.a" = App (Var "f", Proj (Var "r", "a")));
  check "numeric literal" (parse "2" = Succ (Succ Zero));
  check "empty record and empty record type" (parse "{} as {}" = Ascribe (Record [], TyRecord []));
  check "comments are skipped" (parse "(* note (* nested *) *) true" = True);
  check "duplicate label in record expression" (parse_error_mentions "{a=0, a=true}" "duplicate label 'a'");
  check "duplicate label in nested record expression" (parse_fails "{a={b=0, b=0}}");
  check "duplicate label in record type annotation"
    (parse_error_mentions "lambda r:{a:Nat, a:Bool}. r" "duplicate label 'a'");
  check "duplicate label in nested type annotation"
    (parse_fails "({x={y=0}} as {x:{y:Nat, y:Nat}})");
  check "duplicate label nested in an arrow type"
    (parse_fails "lambda f:(Nat -> {a:Nat, b:Bool, a:Nat}). f");
  check "missing dot after parameter is an error" (parse_fails "lambda x x");
  check "trailing garbage is an error" (parse_fails "0 )");
  let roundtrip src =
    let t = parse src in
    check ("printer round trip: " ^ src) (parse (string_of_term t) = t)
  in
  List.iter roundtrip
    [
      "((lambda x. succ x) as (Nat -> Nat)) 0";
      "lambda x:Nat. succ x";
      "lambda f:(Nat -> Nat). f 0";
      "let apply = lambda f:(Nat -> Nat). f 0 in apply (lambda n. succ n)";
      "((if true then {id=0, active=true} else {id=succ 0, score=0}) as {id:Nat}).id";
      "{run=lambda n. succ n, active=true} as {run:Nat -> Nat}";
      "(f (succ x)) (iszero (pred y))";
      "(lambda x. x) as Top as Top";
      "lambda x. x as Nat";
    ];
  check "printer shows omitted annotation"
    (string_of_term (Abs ("x", None, Var "x")) = "lambda x. x");
  check "printer shows explicit annotation"
    (string_of_term (Abs ("x", Some (TyArrow (TyNat, TyNat)), Var "x")) = "lambda x:(Nat -> Nat). x");

  (* ------------------------------------------------------------------ *)
  section "Subtyping (unchanged from Assignment08)";
  let sub a b = Subtype.subtype (ty a) (ty b) in
  check "reflexive base" (sub "Nat" "Nat");
  check "Nat is not Bool" (not (sub "Nat" "Bool"));
  check "anything <: Top" (sub "{a:Nat} -> Bool" "Top");
  check "Top is not <: Nat" (not (sub "Top" "Nat"));
  check "width" (sub "{a:Nat, b:Bool}" "{a:Nat}");
  check "width is one-directional" (not (sub "{a:Nat}" "{a:Nat, b:Bool}"));
  check "depth" (sub "{p:{x:Nat, y:Bool}}" "{p:{x:Nat}}");
  check "permutation" (sub "{a:Nat, b:Bool}" "{b:Bool, a:Nat}");
  check "record <: empty record" (sub "{a:Nat}" "{}");
  check "arrow: contravariant domain" (sub "{a:Nat} -> Nat" "{a:Nat, b:Bool} -> Nat");
  check "arrow: domain is not covariant" (not (sub "{a:Nat, b:Bool} -> Nat" "{a:Nat} -> Nat"));
  check "arrow: covariant result" (sub "Nat -> {a:Nat, b:Bool}" "Nat -> {a:Nat}");
  check "arrow: result is not contravariant" (not (sub "Nat -> {a:Nat}" "Nat -> {a:Nat, b:Bool}"));

  (* ------------------------------------------------------------------ *)
  section "Synthesis on small ASTs";
  let ctx = Context.extend "n" TyNat Context.empty in
  check "var" (Typecheck.synth ctx (Var "n") = Ok TyNat);
  check "unbound var"
    (match Typecheck.synth Context.empty (Var "q") with
    | Error { kind = Typecheck.Unbound_variable "q"; _ } -> true
    | _ -> false);
  check "true" (Typecheck.synth Context.empty True = Ok TyBool);
  check "zero" (Typecheck.synth Context.empty Zero = Ok TyNat);
  check "iszero" (Typecheck.synth ctx (IsZero (Var "n")) = Ok TyBool);
  check "succ of Bool is incompatible" (is_incompatible (Typecheck.synth Context.empty (Succ True)));
  check "annotated lambda synthesizes arrow"
    (Typecheck.synth Context.empty (Abs ("x", Some TyNat, Succ (Var "x"))) = Ok (TyArrow (TyNat, TyNat)));
  check "unannotated lambda: missing info"
    (is_missing (Typecheck.synth Context.empty (Abs ("x", None, Var "x"))));
  check "application of annotated lambda"
    (Typecheck.synth Context.empty (App (Abs ("x", Some TyNat, Succ (Var "x")), Zero)) = Ok TyNat);
  check "application of non-function"
    (match Typecheck.synth Context.empty (App (Zero, Zero)) with
    | Error { kind = Typecheck.Incompatible_types (Typecheck.Expected_function TyNat); _ } -> true
    | _ -> false);
  check "record synthesizes all fields"
    (Typecheck.synth Context.empty (Record [ ("a", Zero); ("b", True) ])
    = Ok (TyRecord [ ("a", TyNat); ("b", TyBool) ]));
  check "projection" (Typecheck.synth Context.empty (Proj (Record [ ("a", Zero) ], "a")) = Ok TyNat);
  check "projection of missing field is incompatible"
    (is_incompatible (Typecheck.synth Context.empty (Proj (Record [ ("a", Zero) ], "b"))));
  check "ascription synthesizes the annotation"
    (Typecheck.synth Context.empty (Ascribe (Zero, TyTop)) = Ok TyTop);
  check "let synthesizes body under binding"
    (Typecheck.synth Context.empty (Let ("y", Zero, IsZero (Var "y"))) = Ok TyBool);
  check "if: mutual subtypes accepted (permuted records)"
    (Typecheck.synth Context.empty
       (If (True, Record [ ("a", Zero); ("b", True) ], Record [ ("b", False); ("a", Zero) ]))
    = Ok (TyRecord [ ("a", TyNat); ("b", TyBool) ]));
  check "if: synthesis rejects if true then 0 else false"
    (is_incompatible (Typecheck.synth Context.empty (If (True, Zero, False))));
  check "duplicate label in hand-built record AST"
    (match Typecheck.synth Context.empty (Record [ ("a", Zero); ("a", True) ]) with
    | Error { kind = Typecheck.Duplicate_label "a"; _ } -> true
    | _ -> false);
  check "duplicate label in hand-built type annotation"
    (match
       Typecheck.synth Context.empty (Ascribe (Record [], TyRecord [ ("a", TyNat); ("a", TyNat) ]))
     with
    | Error { kind = Typecheck.Duplicate_label "a"; _ } -> true
    | _ -> false);
  check "typeof is synth" (Typecheck.typeof Context.empty Zero = Ok TyNat);

  (* ------------------------------------------------------------------ *)
  section "Checking on small ASTs";
  let nn = TyArrow (TyNat, TyNat) in
  check "C-Abs: unannotated lambda against Nat -> Nat"
    (Typecheck.check Context.empty (Abs ("x", None, Succ (Var "x"))) nn = Ok ());
  check "C-Abs: nested"
    (Typecheck.check Context.empty
       (Abs ("x", None, Abs ("y", None, Var "x")))
       (TyArrow (TyNat, TyArrow (TyBool, TyNat)))
    = Ok ());
  check "C-Abs: body mismatch is incompatible"
    (is_incompatible
       (Typecheck.check Context.empty (Abs ("x", None, Succ (Var "x"))) (TyArrow (TyBool, TyNat))));
  check "C-Abs: against Top is missing info"
    (is_missing (Typecheck.check Context.empty (Abs ("x", None, Var "x")) TyTop));
  check "C-Abs: against Nat is incompatible"
    (is_incompatible (Typecheck.check Context.empty (Abs ("x", None, Var "x")) TyNat));
  check "C-AbsAnn: exact domain"
    (Typecheck.check Context.empty (Abs ("x", Some TyNat, Var "x")) nn = Ok ());
  check "C-AbsAnn: wider written domain is allowed"
    (Typecheck.check Context.empty
       (Abs ("p", Some (TyRecord [ ("id", TyNat) ]), Proj (Var "p", "id")))
       (TyArrow (TyRecord [ ("id", TyNat); ("active", TyBool) ], TyNat))
    = Ok ());
  check "C-AbsAnn: narrower written domain is rejected"
    (match
       Typecheck.check Context.empty
         (Abs ("p", Some (TyRecord [ ("id", TyNat); ("active", TyBool) ]), Proj (Var "p", "id")))
         (TyArrow (TyRecord [ ("id", TyNat) ], TyNat))
     with
    | Error { kind = Typecheck.Incompatible_types (Typecheck.Incompatible_annotation _); _ } -> true
    | _ -> false);
  check "C-AbsAnn: body checked under the written type, not the expected domain"
    (* Expected domain {id, active} would allow p.active, but the written
       annotation {id} hides it, so this must fail. *)
    (is_incompatible
       (Typecheck.check Context.empty
          (Abs ("p", Some (TyRecord [ ("id", TyNat) ]), Proj (Var "p", "active")))
          (TyArrow (TyRecord [ ("id", TyNat); ("active", TyBool) ], TyBool))));
  check "annotated lambda against Top succeeds via subsumption"
    (Typecheck.check Context.empty (Abs ("x", Some TyNat, Var "x")) TyTop = Ok ());
  check "C-Sub: Nat <: Top" (Typecheck.check Context.empty Zero TyTop = Ok ());
  check "C-Sub: Bool not <: Nat" (is_incompatible (Typecheck.check Context.empty True TyNat));
  check "C-If: different branch types against Top"
    (Typecheck.check Context.empty (If (True, Zero, False)) TyTop = Ok ());
  check "C-If: unannotated lambdas in both branches"
    (Typecheck.check Context.empty
       (If (True, Abs ("n", None, Succ (Var "n")), Abs ("n", None, Var "n")))
       nn
    = Ok ());
  check "C-If: condition still checked against Bool"
    (is_incompatible (Typecheck.check Context.empty (If (Zero, Zero, Zero)) TyNat));
  check "C-Let: expectation flows into the body"
    (Typecheck.check Context.empty (Let ("one", Succ Zero, Abs ("z", None, Var "one"))) (TyArrow (TyBool, TyNat))
    = Ok ());
  check "C-Let: expectation does not flow into the binding"
    (is_missing
       (Typecheck.check Context.empty (Let ("f", Abs ("x", None, Var "x"), Var "f")) nn));
  check "C-Rcd: required field gets its expectation"
    (Typecheck.check Context.empty
       (Record [ ("run", Abs ("n", None, Succ (Var "n"))) ])
       (TyRecord [ ("run", nn) ])
    = Ok ());
  check "C-Rcd: variable holding a record uses subsumption"
    (Typecheck.check
       (Context.extend "r" (TyRecord [ ("a", TyNat); ("b", TyBool) ]) Context.empty)
       (Var "r") (TyRecord [ ("a", TyNat) ])
    = Ok ());

  (* ------------------------------------------------------------------ *)
  section "Required successful programs";
  expect_success "A" (example "" "contextual_lambda.stlc") "Nat" "1";
  expect_success "B" (example "" "b_parameter_expectation.stlc") "Nat" "1";
  expect_success "C" (example "" "c_nested.stlc") "Nat" "1";
  expect_success "D" (example "" "d_record_width.stlc") "Nat" "1";
  expect_success "E" (example "" "e_conditional_branches.stlc") "Nat" "1";
  expect_success "F" (example "" "f_common_interface.stlc") "Nat" "0";
  expect_success "G" (example "" "g_let_body.stlc") "Nat" "1";
  expect_success "H" (example "" "h_variance.stlc") "Nat" "0";
  check "the earlier annotated syntax still works"
    (match fst (Driver.run "(lambda x:Nat. succ x) 0") with
    | Driver.Success { ty = TyNat; value = Eval.VNat 1; _ } -> true
    | _ -> false);

  (* ------------------------------------------------------------------ *)
  section "Required rejections";
  let r = example "reject" in
  expect_rejection "r01 lambda x. x" (r "r01_bare_lambda.stlc") ~missing:true
    ~mentions:[ "annotate parameter x"; "ascribe the lambda to a function type" ];
  expect_rejection "r02 applied lambda" (r "r02_applied_lambda.stlc") ~missing:true
    ~mentions:[ "function of application"; "never used to infer" ];
  expect_rejection "r03 let id" (r "r03_let_identity.stlc") ~missing:true
    ~mentions:[ "let binding of id" ];
  expect_rejection "r04 as Top" (r "r04_top_no_domain.stlc") ~missing:true
    ~mentions:[ "Top supplies no function domain" ];
  expect_rejection "r05 extra field" (r "r05_extra_field_lambda.stlc") ~missing:true
    ~mentions:[ "extra field run" ];
  expect_rejection "r06 succ on Bool" (r "r06_succ_on_bool.stlc") ~missing:false
    ~mentions:[ "actual:   Bool"; "expected: Nat"; "lambda x body > operand of succ" ];
  expect_rejection "r07 annotation conflict" (r "r07_annotation_conflict.stlc") ~missing:false
    ~mentions:[ "annotated Nat"; "Bool <: Nat fails" ];
  expect_rejection "r08 missing active" (r "r08_missing_interface_field.stlc") ~missing:false
    ~mentions:[ "no field active" ];
  expect_rejection "r09 monomorphic let" (r "r09_monomorphic_let.stlc") ~missing:false
    ~mentions:[ "field b"; "actual:   Bool" ];
  expect_rejection "r10 dead branch" (r "r10_dead_branch.stlc") ~missing:false
    ~mentions:[ "else branch > lambda n body" ];

  (* ------------------------------------------------------------------ *)
  section "Records, interfaces, and diagnostics";
  synth_is "Student record synthesizes its full type"
    "{name=7, year=succ 0, enrolled=true}" "{name:Nat, year:Nat, enrolled:Bool}";
  check_ok "Student record literal checked against Person"
    "{name=7, year=succ 0, enrolled=true}" "{name:Nat}";
  check "Student variable checked against Person (subsumption)"
    (Typecheck.check
       (Context.extend "student"
          (TyRecord [ ("name", TyNat); ("year", TyNat); ("enrolled", TyBool) ])
          Context.empty)
       (Var "student") (TyRecord [ ("name", TyNat) ])
    = Ok ());
  expect_success "Student passed where a Person is expected"
    (example "extra" "student_person.stlc") "Nat" "7";
  check "missing required record field"
    (match check_src "{year=0}" "{name:Nat}" with
    | Error { kind = Typecheck.Incompatible_types (Typecheck.Missing_required_field { label = "name"; _ }); _ } ->
      true
    | _ -> false);
  check "incompatible field type, with structural path"
    (match check_src "{name=true}" "{name:Nat}" with
    | Error e ->
      Typecheck.is_incompatible e && contains (Typecheck.string_of_error e) "at: field name"
    | Ok () -> false);
  check_ok "field permutation against expected record" "{b=true, a=0}" "{a:Nat, b:Bool}";
  check_ok "depth through a record check" "{p={x=0, y=true}}" "{p:{x:Nat}}";
  check_ok "well-typed extra annotated method checked against {}"
    "{run=lambda x:Nat. succ x}" "{}";
  check "extra unannotated method against {} needs an annotation"
    (is_missing (check_src "{run=lambda x. x}" "{}"));
  check "extra field must be well typed even though hidden"
    (is_incompatible (check_src "{id=0, bad=succ true}" "{id:Nat}"));
  expect_success "runtime record keeps hidden field"
    (example "extra" "service_runtime_record.stlc") "{run:Nat -> Nat}"
    "{run=<closure lambda n. succ n>, active=true}";
  expect_success "if checked against Top" (example "extra" "if_checked_against_top.stlc") "Top" "0";
  expect_rejection "if synthesized without expectation"
    (example "extra" "if_synthesized_mismatch.stlc") ~missing:false
    ~mentions:[ "not mutual subtypes" ];

  (* ------------------------------------------------------------------ *)
  section "Scope and closures after contextual checking";
  expect_success "shadowing and closure capture" (example "extra" "shadowing_closure.stlc") "Nat" "1";
  synth_is "inner unannotated binder shadows outer Bool"
    "let x = true in ((lambda x. succ x) as (Nat -> Nat)) 0" "Nat";
  synth_is "outer binding visible again after the lambda"
    "let x = true in let f = ((lambda x. succ x) as (Nat -> Nat)) in if x then f 0 else 0" "Nat";
  check "closure captures its defining environment"
    (match
       fst
         (Driver.run
            "let y = succ 0 in let f = ((lambda x. y) as (Bool -> Nat)) in let y = 0 in f true")
     with
    | Driver.Success { value = Eval.VNat 1; _ } -> true
    | _ -> false);

  (* ------------------------------------------------------------------ *)
  section "Assignment08 annotated examples";
  let a8 = example "assignment08" in
  expect_success "a8 width" (a8 "a8_width.stlc") "Nat" "0";
  expect_success "a8 depth" (a8 "a8_depth.stlc") "Nat" "1";
  expect_success "a8 permutation" (a8 "a8_permutation.stlc") "Bool" "true";
  expect_success "a8 arrow variance" (a8 "a8_arrow_variance.stlc") "Top" "0";
  expect_success "a8 top" (a8 "a8_top.stlc") "Bool" "true";
  expect_success "a8 if mutual" (a8 "a8_if_mutual.stlc") "{a:Nat, b:Bool}" "{a=0, b=true}";
  expect_success "a8 let" (a8 "a8_let.stlc") "Bool" "false";
  expect_success "a8 ascription" (a8 "a8_ascription.stlc") "Nat" "0";

  (* ------------------------------------------------------------------ *)
  section "No evaluation after a static error";
  let before = !Eval.evaluations in
  (match fst (Driver.run "(lambda x. succ x) 0") with
  | Driver.Static_error _ -> check "static error reported" true
  | _ -> check "static error reported" false);
  (match fst (Driver.run "if true then 0 else false") with
  | Driver.Static_error _ -> check "dead-branch program not run" true
  | _ -> check "dead-branch program not run" false);
  check "evaluator never called" (!Eval.evaluations = before);
  (match fst (Driver.run "0") with
  | Driver.Success _ -> check "evaluator called after success" (!Eval.evaluations = before + 1)
  | _ -> check "evaluator called after success" false);

  (* ------------------------------------------------------------------ *)
  section "Type trace for program A";
  let _, lines = Driver.run ~trace:true (Driver.read_file (example "" "contextual_lambda.stlc")) in
  let trace = String.concat "\n" lines in
  let has s = check ("trace shows: " ^ s) (contains trace s) in
  has "check |- lambda x. succ x <= Nat -> Nat   [C-Abs]";
  has "take x:Nat from the expected domain";
  has "check x:Nat |- succ x <= Nat";
  has "=> Nat -> Nat   [T-Ascribe]";
  has "check |- 0 <= Nat";
  has "=> Nat   [T-App]";
  check "trace is empty when not requested" (snd (Driver.run "0") = []);
  let _, lines = Typecheck.check_traced Context.empty (parse "lambda x:Nat. x") (ty "Nat -> Nat") in
  check "annotated trace shows domain comparison"
    (contains (String.concat "\n" lines) "expected domain Nat <: written domain Nat: holds");

  Printf.printf "\n%d checks passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1

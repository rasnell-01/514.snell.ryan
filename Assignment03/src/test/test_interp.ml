(* test_interp.ml -- unit tests for Questions 2 and 3. *)

open OUnit2
open Interp
open Ast

(* --- helpers ------------------------------------------------------ *)

let parses source expected =
  assert_equal ~printer:Ast.string_of_expr ~msg:source expected (Parser.parse source)

let evaluates source expected =
  assert_equal ~printer:Eval.string_of_value ~msg:source expected (Eval.run source)

let int_is source n = evaluates source (Eval.VInt n)
let bool_is source b = evaluates source (Eval.VBool b)

let runtime_error message source =
  assert_raises ~msg:source (Eval.Runtime_error message) (fun () -> Eval.run source)

let parse_error source =
  assert_raises ~msg:source
    (Parser.Parse_error "comparison operators do not chain; parenthesize the operand you meant")
    (fun () -> Parser.parse source)

(* --- the lexer ---------------------------------------------------- *)

let lexer_tests =
  [
    ( "two-character operators are one token" >:: fun _ ->
      assert_equal
        [ Lexer.TInt 1; Lexer.TLe; Lexer.TInt 2; Lexer.TEOF ]
        (Lexer.tokenize "1 <= 2") );
    ( "an identifier may begin with a keyword" >:: fun _ ->
      int_is "let letters = 1 in letters + 1" 2;
      int_is "let inner = 2 in inner * 3" 6 );
    ( "whitespace is irrelevant" >:: fun _ ->
      int_is "let\n  x\t=\n1 in x" 1 );
    ( "a stray & is reported" >:: fun _ ->
      assert_raises
        (Lexer.Lex_error "found '&'; the logical operator is '&&'")
        (fun () -> Lexer.tokenize "1 & 2") );
  ]

(* --- Question 3: the shape of the tree ---------------------------- *)

let function_parsing_tests =
  [
    ( "fun x -> x" >:: fun _ -> parses "fun x -> x" (Fun ("x", Var "x")) );
    ( "fun x y -> x + y curries" >:: fun _ ->
      parses "fun x y -> x + y"
        (Fun ("x", Fun ("y", Binop (Add, Var "x", Var "y")))) );
    ( "backslash notation is the same tree" >:: fun _ ->
      parses "\\x. x" (Fun ("x", Var "x"));
      parses "\\x y. x + y" (Parser.parse "fun x y -> x + y") );
    ( "f x y is left associative" >:: fun _ ->
      parses "f x y" (App (App (Var "f", Var "x"), Var "y")) );
    ( "application binds tighter than +" >:: fun _ ->
      parses "f x + 1" (Binop (Add, App (Var "f", Var "x"), Int 1)) );
    ( "parentheses group an argument" >:: fun _ ->
      parses "f (g x)" (App (Var "f", App (Var "g", Var "x"))) );
    ( "let with parameters is sugar for a fun" >:: fun _ ->
      parses "let f x = x in f"
        (Let ("f", Fun ("x", Var "x"), Var "f")) );
    ( "a function needs a parameter" >:: fun _ ->
      assert_raises (Parser.Parse_error "a function needs at least one parameter")
        (fun () -> Parser.parse "fun -> 1") );
  ]

(* --- Question 2: the new productions ------------------------------ *)

let precedence_tests =
  [
    ( "multiplication binds tighter than addition" >:: fun _ ->
      parses "1 + 2 * 3" (Binop (Add, Int 1, Binop (Mul, Int 2, Int 3))) );
    ( "subtraction is left associative" >:: fun _ ->
      parses "1 - 2 - 3" (Binop (Sub, Binop (Sub, Int 1, Int 2), Int 3)) );
    ( "unary minus binds tighter than multiplication" >:: fun _ ->
      parses "-x * y" (Binop (Mul, Neg (Var "x"), Var "y")) );
    ( "unary minus binds looser than application" >:: fun _ ->
      parses "-f x" (Neg (App (Var "f", Var "x"))) );
    ( "unary minus nests" >:: fun _ -> parses "- - 3" (Neg (Neg (Int 3))) );
    ( "binary minus followed by unary minus" >:: fun _ ->
      parses "3 - -4" (Binop (Sub, Int 3, Neg (Int 4))) );
    ( "comparison is looser than arithmetic" >:: fun _ ->
      parses "1 + 1 < 3" (Binop (Lt, Binop (Add, Int 1, Int 1), Int 3)) );
    ( "logical is looser than comparison" >:: fun _ ->
      parses "1 < 2 && 3 < 4"
        (Binop (And, Binop (Lt, Int 1, Int 2), Binop (Lt, Int 3, Int 4))) );
    ( "&& and || share a level and associate left" >:: fun _ ->
      parses "a && b || c"
        (Binop (Or, Binop (And, Var "a", Var "b"), Var "c")) );
    ( "comparisons do not chain" >:: fun _ -> parse_error "1 < 2 < 3" );
  ]

let unary_tests =
  [
    ("negative literal" >:: fun _ -> int_is "-5" (-5));
    ("negation of a sum" >:: fun _ -> int_is "-(2 + 3)" (-5));
    ("double negation" >:: fun _ -> int_is "- - 7" 7);
    ("subtracting a negative" >:: fun _ -> int_is "3 - -4" 7);
    ( "negation of a call" >:: fun _ ->
      int_is "let f = fun x -> x - 10 in -f 3" 7 );
    ("negation in a product" >:: fun _ -> int_is "let x = 3 in -x * 2" (-6));
    ( "negation is only for integers" >:: fun _ ->
      runtime_error "unary - expects an integer but got true" "-true" );
  ]

let comparison_tests =
  [
    ("less than" >:: fun _ -> bool_is "1 < 2" true);
    ("less than, false" >:: fun _ -> bool_is "2 < 1" false);
    ("less or equal" >:: fun _ -> bool_is "2 <= 2" true);
    ("greater than" >:: fun _ -> bool_is "3 > 4" false);
    ("greater or equal" >:: fun _ -> bool_is "3 >= 3" true);
    ("equality on integers" >:: fun _ -> bool_is "1 + 1 = 2" true);
    ("inequality on integers" >:: fun _ -> bool_is "1 <> 2" true);
    ("equality on booleans" >:: fun _ -> bool_is "(1 < 2) = true" true);
    ( "comparing a function is a runtime error" >:: fun _ ->
      runtime_error "operator < cannot be applied to <closure> and 1"
        "(fun x -> x) < 1" );
  ]

let logical_tests =
  [
    ("conjunction" >:: fun _ -> bool_is "1 < 2 && 2 < 3" true);
    ("conjunction, false" >:: fun _ -> bool_is "1 < 2 && 3 < 2" false);
    ("disjunction" >:: fun _ -> bool_is "false || 2 > 1" true);
    ("left associative chain" >:: fun _ -> bool_is "true && false || true" true);
    (* Short circuiting is observable: the right operand of a false
       conjunction would divide by zero if it were evaluated. *)
    ( "&& does not evaluate its right operand when it can tell" >:: fun _ ->
      bool_is "1 > 2 && 1 / 0 = 0" false );
    ( "|| does not evaluate its right operand when it can tell" >:: fun _ ->
      bool_is "1 < 2 || 1 / 0 = 0" true );
    ( "the operands must be booleans" >:: fun _ ->
      runtime_error "&& expects a boolean but got 1" "1 && true" );
  ]

let letrec_tests =
  [
    ( "factorial" >:: fun _ ->
      int_is
        "let rec fact = fun n -> if n <= 1 then 1 else n * fact (n - 1) in fact 5"
        120 );
    ( "factorial, using the parameter shorthand" >:: fun _ ->
      int_is "let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 10"
        3628800 );
    ( "fibonacci calls itself twice" >:: fun _ ->
      int_is
        "let rec fib n = if n < 2 then n else fib (n - 1) + fib (n - 2) in fib 10"
        55 );
    ( "a recursive function of two parameters" >:: fun _ ->
      int_is
        "let rec sum_to = fun acc n -> if n = 0 then acc else sum_to (acc + n) (n - 1) \
         in sum_to 0 100"
        5050 );
    ( "a recursive function may be passed to another function" >:: fun _ ->
      int_is
        "let rec double n = if n = 0 then 0 else 2 + double (n - 1) in \
         let apply = fun f x -> f x in apply double 4"
        8 );
    ( "recursion needs a function on the right" >:: fun _ ->
      runtime_error "the right-hand side of let rec x must be a function"
        "let rec x = 1 in x" );
    ( "a plain let is not recursive" >:: fun _ ->
      runtime_error "unbound variable: f"
        "let f = fun n -> if n <= 0 then 0 else f (n - 1) in f 3" );
  ]

(* --- Question 3: closures and lexical scope ----------------------- *)

let closure_tests =
  [
    ("the identity function" >:: fun _ -> int_is "(fun x -> x) 5" 5);
    ("identity again" >:: fun _ -> int_is "(fun x -> x) 42" 42);
    ("the body may use the parameter" >:: fun _ -> int_is "(fun x -> x + 1) 41" 42);
    ("arithmetic in the body" >:: fun _ -> int_is "(fun x -> x * x) 9" 81);
    ( "a curried function" >:: fun _ ->
      int_is "let add = fun x y -> x + y in add 2 3" 5 );
    ( "partial application produces a closure" >:: fun _ ->
      int_is "let add = fun x y -> x + y in let add2 = add 2 in add2 40" 42 );
    (* The test that tells lexical scope from dynamic scope.  With
       dynamic scope this is 105. *)
    ( "the defining environment wins over the calling one" >:: fun _ ->
      int_is
        "let x = 10 in let f = fun y -> x + y in let x = 100 in f 5" 15 );
    ( "a parameter shadows an outer binding" >:: fun _ ->
      int_is "let x = 1 in let f = fun x -> x * 2 in f 21" 42 );
    ( "an argument is evaluated before the call" >:: fun _ ->
      int_is "(fun x -> x + x) (3 * 4)" 24 );
    ( "a closure survives the scope that made it" >:: fun _ ->
      int_is "let make = fun n -> fun k -> n + k in let add5 = make 5 in add5 37" 42 );
  ]

let higher_order_tests =
  [
    ( "twice" >:: fun _ ->
      int_is "let twice = fun f x -> f (f x) in twice (fun x -> x * 2) 3" 12 );
    ( "apply_twice" >:: fun _ ->
      int_is "let apply_twice = fun f x -> f (f x) in apply_twice (fun x -> x + 1) 10"
        12 );
    ( "a function returned from a function" >:: fun _ ->
      int_is "let compose = fun f g x -> f (g x) in compose (fun x -> x + 1) (fun x -> x * 2) 20"
        41 );
    ( "a closure captured inside another closure" >:: fun _ ->
      int_is
        "let adder = fun n -> fun k -> n + k in \
         let apply = fun f x -> f x in apply (adder 30) 12"
        42 );
    ( "church-style self application" >:: fun _ ->
      int_is "(fun f -> f (f 1)) (fun x -> x * 10)" 100 );
  ]

let error_tests =
  [
    ( "an unbound variable is reported by name" >:: fun _ ->
      runtime_error "unbound variable: x" "x" );
    ( "calling an integer is an error" >:: fun _ ->
      runtime_error "attempt to call a non-function: 3" "3 4" );
    ( "calling a boolean is an error" >:: fun _ ->
      runtime_error "attempt to call a non-function: true" "true 1" );
    ("division by zero" >:: fun _ -> runtime_error "division by zero" "1 / 0");
    ( "adding a boolean to an integer" >:: fun _ ->
      runtime_error "operator + cannot be applied to 1 and true" "1 + true" );
    ( "the condition of an if must be a boolean" >:: fun _ ->
      runtime_error "the condition of if expects a boolean but got 1" "if 1 then 2 else 3" );
    ( "leftover input is reported" >:: fun _ ->
      assert_raises (Parser.Parse_error "unexpected ) after the end of the expression")
        (fun () -> Parser.parse "1 + 1)") );
  ]

(* --- predefined bindings ------------------------------------------ *)

let prelude_tests =
  [
    ("a predefined function is in scope" >:: fun _ -> int_is "abs (0 - 7)" 7);
    ("a predefined function of two arguments" >:: fun _ -> int_is "max 3 4" 4);
    ("another one" >:: fun _ -> int_is "min 3 4" 3);
    ( "a program may shadow a predefined name" >:: fun _ ->
      int_is "let max = 7 in max" 7 );
    ( "predefined functions are first class" >:: fun _ ->
      int_is "let apply = fun f x -> f x in apply succ 41" 42 );
    ( "evaluation can start from the empty environment instead" >:: fun _ ->
      assert_raises (Eval.Runtime_error "unbound variable: abs") (fun () ->
          Eval.run ~env:Env.empty "abs 1") );
  ]

(* --- printing ------------------------------------------------------ *)

let printing_tests =
  [
    ( "a closure does not print its environment" >:: fun _ ->
      assert_equal ~printer:(fun s -> s) "<closure>"
        (Eval.string_of_value (Eval.run "fun x -> x")) );
    ( "a recursive closure prints its name" >:: fun _ ->
      assert_equal ~printer:(fun s -> s) "<closure f>"
        (Eval.string_of_value (Eval.run "let rec f n = f n in f")) );
    ( "source printing round-trips through the parser" >:: fun _ ->
      List.iter
        (fun source ->
          let once = Parser.parse source in
          let twice = Parser.parse (Ast.to_source once) in
          assert_equal ~printer:Ast.string_of_expr ~msg:source once twice)
        [
          "1 + 2 * 3";
          "1 - 2 - 3";
          "-x * y";
          "-f x";
          "f x y";
          "f (g x)";
          "fun x y -> x + y";
          "let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 5";
          "a && b || c";
          "1 + 1 < 3";
        ] );
  ]

(* --- de Bruijn translation (analysis question 10) ------------------ *)

let translates source expected =
  assert_equal ~printer:(fun s -> s) ~msg:source expected
    (Debruijn.string_of_dexpr (Debruijn.of_expr (Parser.parse source)))

let debruijn_tests =
  [
    ( "a parameter becomes index 0" >:: fun _ ->
      translates "fun x -> x" "fun. #0" );
    ( "an outer parameter becomes index 1" >:: fun _ ->
      translates "fun x -> fun y -> x + y" "fun. fun. (#1 + #0)" );
    ( "an inner binder shadows by occupying index 0" >:: fun _ ->
      translates "fun x -> fun x -> x" "fun. fun. #0" );
    ( "let binds the body but not the bound expression" >:: fun _ ->
      translates "let x = 1 in x + x" "let. 1 in (#0 + #0)" );
    ( "alpha-equivalent programs become identical terms" >:: fun _ ->
      let one = Debruijn.of_expr (Parser.parse "fun x -> fun y -> x + y") in
      let other = Debruijn.of_expr (Parser.parse "fun a -> fun b -> a + b") in
      assert_bool "the two translations should be equal" (one = other) );
    ( "a free variable has no index" >:: fun _ ->
      assert_raises (Debruijn.Unbound "z") (fun () ->
          Debruijn.of_expr (Parser.parse "fun x -> z")) );
    (* Running both evaluators over the same programs is the real test
       that the translation preserves meaning. *)
    ( "the two evaluators agree" >:: fun _ ->
      List.iter
        (fun (source, expected) ->
          assert_equal ~printer:string_of_int ~msg:source expected
            (match Debruijn.run source with
            | Debruijn.DVInt n -> n
            | other -> assert_failure ("expected an integer, got " ^ Debruijn.string_of_dvalue other));
          assert_equal ~printer:Eval.string_of_value ~msg:source (Eval.VInt expected)
            (Eval.run source))
        [
          ("(fun x -> x) 42", 42);
          ("(fun x -> x * x) 9", 81);
          ("let add = fun x y -> x + y in add 2 3", 5);
          ("let x = 10 in let f = fun y -> x + y in let x = 100 in f 5", 15);
          ("let twice = fun f x -> f (f x) in twice (fun x -> x * 2) 3", 12);
          ("let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 6", 720);
          ("let rec fib n = if n < 2 then n else fib (n - 1) + fib (n - 2) in fib 12", 144);
          ("let x = 3 in -x * 2", -6);
        ] );
  ]

let suite =
  "Interpreter"
  >::: [
         "lexer" >::: lexer_tests;
         "functions (Q3)" >::: function_parsing_tests;
         "precedence (Q2)" >::: precedence_tests;
         "unary minus (Q2)" >::: unary_tests;
         "comparison (Q2)" >::: comparison_tests;
         "logical (Q2)" >::: logical_tests;
         "let rec (Q2)" >::: letrec_tests;
         "closures (Q3)" >::: closure_tests;
         "higher order (Q3)" >::: higher_order_tests;
         "errors" >::: error_tests;
         "prelude" >::: prelude_tests;
         "printing" >::: printing_tests;
         "de Bruijn" >::: debruijn_tests;
       ]

let () = run_test_tt_main suite

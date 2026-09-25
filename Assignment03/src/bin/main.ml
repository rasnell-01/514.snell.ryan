(* main.ml -- a demonstration runner for Assignment 3.

     dune exec bin/main.exe              the whole walkthrough
     dune exec bin/main.exe -- --trace   the walkthrough, plus a traced run
     dune exec bin/main.exe -- -e "1+1"  evaluate one expression
     dune exec bin/main.exe -- --repl    read expressions from stdin
*)

open Interp

let rule title =
  print_newline ();
  print_endline (String.make 68 '=');
  print_endline title;
  print_endline (String.make 68 '=')

let section title =
  print_newline ();
  print_endline (title ^ ":");
  print_endline (String.make (String.length title + 1) '-')

(* Evaluate one program and report it, catching the three ways it can
   fail so that the error cases in the assignment can be demonstrated
   alongside the successful ones. *)
let describe ?(show_ast = true) source =
  Printf.printf "  %s\n" source;
  (try
     let expression = Parser.parse source in
     if show_ast then Printf.printf "    ast   %s\n" (Ast.string_of_expr expression);
     Printf.printf "    value %s\n" (Eval.string_of_value (Eval.eval_expr_in expression))
   with
  | Lexer.Lex_error message -> Printf.printf "    error lexical: %s\n" message
  | Parser.Parse_error message -> Printf.printf "    error syntax: %s\n" message
  | Eval.Runtime_error message -> Printf.printf "    error runtime: %s\n" message);
  print_newline ()

let show_value source = describe ~show_ast:false source

(* ------------------------------------------------------------------ *)

let question1 () =
  rule "Question 1 -- environments";
  let show label env = Printf.printf "  %-26s %s\n" label (Env.to_string string_of_int env) in
  let show_lookup name env =
    Printf.printf "  %-26s %s\n"
      (Printf.sprintf "lookup %S" name)
      (match Env.lookup name env with Some n -> "Some " ^ string_of_int n | None -> "None")
  in
  section "Building x -> 10, y -> 20, z -> 30";
  let env = Env.empty |> Env.extend "x" 10 |> Env.extend "y" 20 |> Env.extend "z" 30 in
  show "the environment" env;
  show_lookup "x" env;
  show_lookup "y" env;
  show_lookup "w" env;
  Printf.printf "  %-26s %b\n" "is_bound \"z\"" (Env.is_bound "z" env);
  Printf.printf "  %-26s %b\n" "is_bound \"w\"" (Env.is_bound "w" env);

  section "Extending never modifies";
  let shadowed = Env.extend "x" 99 env in
  show "after extend x -> 99" shadowed;
  show "the original" env;
  show_lookup "x" shadowed;
  show_lookup "x" env;

  section "Predefined bindings, the way a runtime supplies cin and cout";
  Printf.printf "  %-26s %s\n" "the starting environment"
    (Env.to_string Eval.string_of_value Eval.prelude);
  show_value "max 3 4";
  show_value "let max = 7 in max"

let question2 () =
  rule "Question 2 -- unary, comparison, logical, and let rec";
  section "unary ::= \"-\" unary | application";
  describe "-5";
  describe "3 - -4";
  describe "let x = 3 in -x * 2";
  describe "let f = fun n -> n - 10 in -f 3";

  section "comparison ::= additive (\"<\" | \"<=\" | \">\" | \">=\") additive";
  describe "1 + 1 < 3";
  describe "2 >= 3";
  describe "1 < 2 < 3";

  section "logical ::= comparison { (\"&&\" | \"||\") comparison }";
  describe "1 < 2 && 2 < 3";
  describe "true && false || true";
  show_value "1 > 2 && 1 / 0 = 0";

  section "letrec ::= \"let\" \"rec\" IDENT \"=\" expr \"in\" expr";
  show_value "let rec fact = fun n -> if n <= 1 then 1 else n * fact (n - 1) in fact 10";
  show_value "let rec fib n = if n < 2 then n else fib (n - 1) + fib (n - 2) in fib 20";
  show_value "let rec x = 1 in x"

let question3 () =
  rule "Question 3 -- functions, application, and closures";
  section "Abstraction and application parse into curried trees";
  describe ~show_ast:true "fun x -> x";
  describe "fun x y -> x + y";
  describe "\\x. x + 1";
  Printf.printf "  f x y\n    ast   %s\n\n" (Ast.string_of_expr (Parser.parse "f x y"));

  section "The tests from the assignment";
  show_value "(fun x -> x) 5";
  show_value "(fun x -> x + 1) 41";
  show_value "(fun x -> x * x) 9";
  show_value "let add = fun x y -> x + y in add 2 3";
  show_value "let twice = fun f x -> f (f x) in twice (fun x -> x * 2) 3";
  show_value "let apply_twice = fun f x -> f (f x) in apply_twice (fun x -> x + 1) 10";

  section "Lexical scope -- 15 here, 105 under dynamic scope";
  show_value "let x = 10 in let f = fun y -> x + y in let x = 100 in f 5";

  section "Failures";
  show_value "x";
  show_value "3 4";

  section "A closure prints as a closure, not as its environment";
  show_value "let x = 10 in fun y -> x + y"

let debruijn () =
  rule "Beyond the questions -- de Bruijn indices (analysis question 10)";
  section "Names disappear; a variable counts binders outward";
  List.iter
    (fun source ->
      Printf.printf "  %-26s  %s\n" source
        (Debruijn.string_of_dexpr (Debruijn.of_expr (Parser.parse source))))
    [
      "fun x -> x";
      "fun x -> fun y -> x + y";
      "fun a -> fun b -> a + b";
      "fun x -> fun x -> x";
      "let x = 1 in x + x";
    ];
  print_newline ();
  print_endline
    "  The second and third are alpha-equivalent, and they translate to the";
  print_endline "  same term, so comparing them is ordinary structural equality.";

  section "Both evaluators agree";
  let source = "let x = 10 in let f = fun y -> x + y in let x = 100 in f 5" in
  Printf.printf "  %s\n" source;
  Printf.printf "    named     %s\n" (Eval.string_of_value (Eval.run source));
  Printf.printf "    de Bruijn %s\n" (Debruijn.string_of_dvalue (Debruijn.run source))

let traced () =
  rule "A traced run of the lexical scope program";
  let source = "let x = 10 in let f = fun y -> x + y in let x = 100 in f 5" in
  Printf.printf "  %s\n\n" source;
  Eval.trace := true;
  let result = Eval.run source in
  Eval.trace := false;
  Printf.printf "\n  result: %s\n" (Eval.string_of_value result)

let repl () =
  print_endline "Expressions, one per line. Ctrl-D to quit.";
  let rec loop () =
    print_string "> ";
    match read_line () with
    | exception End_of_file -> print_newline ()
    | "" -> loop ()
    | line ->
      show_value line;
      loop ()
  in
  loop ()

let () =
  match Array.to_list Sys.argv with
  | _ :: "--repl" :: _ -> repl ()
  | _ :: "-e" :: source :: _ -> show_value source
  | _ :: "--trace" :: _ ->
    question1 ();
    question2 ();
    question3 ();
    debruijn ();
    traced ()
  | _ ->
    question1 ();
    question2 ();
    question3 ();
    debruijn ();
    traced ()

(* expr_parser.ml
   Question 4: Extending our Expression Evaluator

   Implements a lexer + recursive-descent parser + evaluator for the
   grammar built up across Questions 2 and 3:

       Expr   -> Expr + Term
               | Expr - Term
               | Term

       Term   -> Term * Unary
               | Term / Unary
               | Unary

       Unary  -> + Unary
               | - Unary
               | Factor

       Factor -> ( Expr )
               | number

   The lecture-note starter only handled numbers and '+'. This file
   adds '-', '*', '/', parenthesization, and unary +/-, following the
   same left-recursion-as-a-loop technique (each left-recursive rule
   like "Expr -> Expr + Term | Term" is implemented as: parse one
   Term, then keep folding in more "+ Term"/"- Term" as long as we
   see one -- this is the standard way to turn left recursion into
   an iterative loop for a hand-written recursive-descent parser).
*)

(* ------------------------------------------------------------- *)
(* Tokens *)

type token =
  | NUM of int
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | LPAREN
  | RPAREN
  | EOF

let string_of_token = function
  | NUM n -> Printf.sprintf "NUM %d" n
  | PLUS -> "PLUS"
  | MINUS -> "MINUS"
  | TIMES -> "TIMES"
  | DIV -> "DIV"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | EOF -> "EOF"

(* ------------------------------------------------------------- *)
(* Lexer: turns a string into a token list.
   (A hand-written character scanner, in the spirit of the lecture
   code, rather than a generated ocamllex lexer -- kept dependency
   free so this file can be built with a single `ocamlc`.) *)

let tokenize (s : string) : token list =
  let n = String.length s in
  let rec go i =
    if i >= n then [ EOF ]
    else
      match s.[i] with
      | ' ' | '\t' | '\n' | '\r' -> go (i + 1)
      | '+' -> PLUS :: go (i + 1)
      | '-' -> MINUS :: go (i + 1)
      | '*' -> TIMES :: go (i + 1)
      | '/' -> DIV :: go (i + 1)
      | '(' -> LPAREN :: go (i + 1)
      | ')' -> RPAREN :: go (i + 1)
      | '0' .. '9' ->
        let j = ref i in
        while !j < n && s.[!j] >= '0' && s.[!j] <= '9' do
          incr j
        done;
        let num = int_of_string (String.sub s i (!j - i)) in
        NUM num :: go !j
      | c -> failwith (Printf.sprintf "Unexpected character %c at position %d" c i)
  in
  go 0

(* ------------------------------------------------------------- *)
(* AST.
   Unary +/- and binary +/-/*// all get their own constructors so
   that the parse tree structure (and hence evaluation) exactly
   mirrors the grammar in the write-up. *)

type expr =
  | Num of int
  | UPlus of expr
  | UMinus of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr

let rec string_of_expr = function
  | Num n -> string_of_int n
  | UPlus e -> Printf.sprintf "(+%s)" (string_of_expr e)
  | UMinus e -> Printf.sprintf "(-%s)" (string_of_expr e)
  | Add (a, b) -> Printf.sprintf "(%s + %s)" (string_of_expr a) (string_of_expr b)
  | Sub (a, b) -> Printf.sprintf "(%s - %s)" (string_of_expr a) (string_of_expr b)
  | Mul (a, b) -> Printf.sprintf "(%s * %s)" (string_of_expr a) (string_of_expr b)
  | Div (a, b) -> Printf.sprintf "(%s / %s)" (string_of_expr a) (string_of_expr b)

(* ------------------------------------------------------------- *)
(* Recursive-descent parser.

   Each grammar nonterminal becomes one function. Left recursion
   (Expr -> Expr + Term | ...) becomes: parse the first Term, then
   loop, consuming as many "+ Term" / "- Term" as are available and
   folding them onto an accumulator -- this naturally produces a
   left-associative tree, matching "Left recursion enforces
   left-associativity" from the write-up. *)

let parse (tokens : token list) : expr =
  let toks = ref tokens in

  let peek () = match !toks with t :: _ -> t | [] -> EOF in
  let advance () = match !toks with _ :: rest -> toks := rest | [] -> () in

  (* Factor -> ( Expr ) | number *)
  let rec parse_factor () : expr =
    match peek () with
    | NUM n -> advance (); Num n
    | LPAREN ->
      advance ();
      let e = parse_expr () in
      (match peek () with
       | RPAREN -> advance (); e
       | t -> failwith (Printf.sprintf "Expected ')' but found %s" (string_of_token t)))
    | t -> failwith (Printf.sprintf "Expected number or '(' but found %s" (string_of_token t))

  (* Unary -> + Unary | - Unary | Factor
     Right-recursive (as unary operators should be), so "--3" and
     "-+3" both parse by peeling off one sign at a time. *)
  and parse_unary () : expr =
    match peek () with
    | PLUS -> advance (); UPlus (parse_unary ())
    | MINUS -> advance (); UMinus (parse_unary ())
    | _ -> parse_factor ()

  (* Term -> Term * Unary | Term / Unary | Unary *)
  and parse_term () : expr =
    let lhs = ref (parse_unary ()) in
    let continue_ = ref true in
    while !continue_ do
      match peek () with
      | TIMES -> advance (); lhs := Mul (!lhs, parse_unary ())
      | DIV -> advance (); lhs := Div (!lhs, parse_unary ())
      | _ -> continue_ := false
    done;
    !lhs

  (* Expr -> Expr + Term | Expr - Term | Term *)
  and parse_expr () : expr =
    let lhs = ref (parse_term ()) in
    let continue_ = ref true in
    while !continue_ do
      match peek () with
      | PLUS -> advance (); lhs := Add (!lhs, parse_term ())
      | MINUS -> advance (); lhs := Sub (!lhs, parse_term ())
      | _ -> continue_ := false
    done;
    !lhs
  in

  let result = parse_expr () in
  (match peek () with
   | EOF -> result
   | t -> failwith (Printf.sprintf "Unexpected trailing token %s" (string_of_token t)))

(* ------------------------------------------------------------- *)
(* Evaluator *)

let rec eval (e : expr) : int =
  match e with
  | Num n -> n
  | UPlus e -> eval e
  | UMinus e -> - (eval e)
  | Add (a, b) -> eval a + eval b
  | Sub (a, b) -> eval a - eval b
  | Mul (a, b) -> eval a * eval b
  | Div (a, b) -> eval a / eval b

let run (s : string) : int * expr =
  let e = parse (tokenize s) in
  (eval e, e)

(* ------------------------------------------------------------- *)
(* Test driver: includes the three parse-tree expressions from
   Question 2 and the unary-operator expression from Question 3, so
   the evaluator's output can be checked against the hand-drawn
   trees in docs/answers.md. *)

let () =
  let tests = [
    "(3+(2*6)/2)";     (* Question 2, expr 1 -> 3 + 12/2   = 9 *)
    "4*(3+2)*4";       (* Question 2, expr 2 -> 4*5*4      = 80 *)
    "42*1+3*(80+90)";  (* Question 2, expr 3 -> 42 + 3*170 = 552 *)
    "(3+-3)*4";        (* Question 3 unary example         = 0 *)
    "-2*-3";           (* two unary minuses *)
    "-(2+3)";          (* unary minus applied to a parenthesized expr *)
    "+5 - -5";         (* unary plus and unary minus together *)
  ] in
  List.iter (fun s ->
    let (v, e) = run s in
    Printf.printf "%-20s parses as %-45s = %d\n" s (string_of_expr e) v)
    tests

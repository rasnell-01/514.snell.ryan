(* parser.ml

   A recursive-descent parser.  Each nonterminal in the grammar is one
   function, and a function for a tighter-binding nonterminal is
   called by the function for the looser one, which is what encodes
   precedence.

     expr           ::= let | letrec | if | fun | logical
     let            ::= "let" IDENT { IDENT } "=" expr "in" expr
     letrec         ::= "let" "rec" IDENT { IDENT } "=" expr "in" expr
     if             ::= "if" expr "then" expr "else" expr
     fun            ::= ("fun" | backslash) IDENT { IDENT } ("->" | ".") expr

     logical        ::= comparison { ("&&" | "||") comparison }
     comparison     ::= additive [ ("<" | "<=" | ">" | ">=" | "=" | "<>") additive ]
     additive       ::= multiplicative { ("+" | "-") multiplicative }
     multiplicative ::= unary { ("*" | "/") unary }
     unary          ::= "-" unary | application
     application    ::= atom { atom }
     atom           ::= INT | "true" | "false" | IDENT | "(" expr ")"

   The four productions Question 2 asks for are [unary], [comparison],
   [logical] and [letrec].  [application] is Question 3.  Three small
   decisions are worth flagging, and they are argued for in the docs:

   - [comparison] is written with an *optional* operator rather than a
     required one, so that a bare [additive] is still a comparison.
     Only one operator is allowed, so [a < b < c] is a syntax error
     rather than something that quietly compares a boolean.

   - [&&] and [||] share one precedence level, as the assignment's
     production has them, and so associate to the left.

   - [let f x = e] is sugar for [let f = fun x -> e].  The desugaring
     happens here, so the AST and the evaluator never see it. *)

open Ast
open Lexer

exception Parse_error of string

type state = {
  tokens : token array;
  mutable position : int;
}

let make_state tokens = { tokens = Array.of_list tokens; position = 0 }
let peek st = st.tokens.(st.position)
let advance st = st.position <- st.position + 1

let expect st expected =
  if peek st = expected then advance st
  else
    raise
      (Parse_error
         (Printf.sprintf "expected %s but found %s" (string_of_token expected)
            (string_of_token (peek st))))

let parse_ident st =
  match peek st with
  | TIdent name ->
    advance st;
    name
  | other ->
    raise
      (Parse_error
         (Printf.sprintf "expected an identifier but found %s" (string_of_token other)))

(* Zero or more identifiers, used for the parameter lists of [fun] and
   for the [let f x y = ...] shorthand. *)
let rec parse_idents st =
  match peek st with
  | TIdent name ->
    advance st;
    name :: parse_idents st
  | _ -> []

(* [fun x y -> body] becomes [Fun ("x", Fun ("y", body))].  Folding
   from the right is what makes the outermost parameter the first one. *)
let curry parameters body =
  List.fold_right (fun parameter body -> Fun (parameter, body)) parameters body

let is_comparison = function
  | TLt | TLe | TGt | TGe | TEq | TNe -> true
  | _ -> false

(* An atom is the only thing that can start an argument, so this is the
   test that tells [parse_application] when to stop consuming. *)
let begins_atom = function
  | TInt _ | TIdent _ | TTrue | TFalse | TLParen -> true
  | _ -> false

let rec parse_expr st =
  match peek st with
  | TLet -> parse_let st
  | TIf -> parse_if st
  | TFun | TBackslash -> parse_fun st
  | _ -> parse_logical st

and parse_let st =
  expect st TLet;
  let recursive = peek st = TRec in
  if recursive then advance st;
  let name = parse_ident st in
  let parameters = parse_idents st in
  expect st TEq;
  let bound = curry parameters (parse_expr st) in
  expect st TIn;
  let body = parse_expr st in
  if recursive then LetRec (name, bound, body) else Let (name, bound, body)

and parse_if st =
  expect st TIf;
  let condition = parse_expr st in
  expect st TThen;
  let consequent = parse_expr st in
  expect st TElse;
  let alternative = parse_expr st in
  If (condition, consequent, alternative)

and parse_fun st =
  (* [fun x y -> e] and the lambda-calculus spelling [\x y. e] parse
     into exactly the same tree. *)
  (match peek st with
  | TFun | TBackslash -> advance st
  | other ->
    raise
      (Parse_error
         (Printf.sprintf "expected fun but found %s" (string_of_token other))));
  let parameters = parse_idents st in
  if parameters = [] then
    raise (Parse_error "a function needs at least one parameter");
  (match peek st with
  | TArrow | TDot -> advance st
  | other ->
    raise
      (Parse_error
         (Printf.sprintf "expected -> after the parameters but found %s"
            (string_of_token other))));
  let body = parse_expr st in
  curry parameters body

and parse_logical st =
  let rec loop lhs =
    match peek st with
    | TAnd ->
      advance st;
      loop (Binop (And, lhs, parse_comparison st))
    | TOr ->
      advance st;
      loop (Binop (Or, lhs, parse_comparison st))
    | _ -> lhs
  in
  loop (parse_comparison st)

and parse_comparison st =
  let lhs = parse_additive st in
  if not (is_comparison (peek st)) then lhs
  else begin
    let op =
      match peek st with
      | TLt -> Lt
      | TLe -> Le
      | TGt -> Gt
      | TGe -> Ge
      | TEq -> Eq
      | TNe -> Ne
      | _ -> raise (Parse_error "expected a comparison operator")
    in
    advance st;
    let rhs = parse_additive st in
    if is_comparison (peek st) then
      raise
        (Parse_error
           "comparison operators do not chain; parenthesize the operand you meant")
    else Binop (op, lhs, rhs)
  end

and parse_additive st =
  let rec loop lhs =
    match peek st with
    | TPlus ->
      advance st;
      loop (Binop (Add, lhs, parse_multiplicative st))
    | TMinus ->
      advance st;
      loop (Binop (Sub, lhs, parse_multiplicative st))
    | _ -> lhs
  in
  loop (parse_multiplicative st)

and parse_multiplicative st =
  let rec loop lhs =
    match peek st with
    | TStar ->
      advance st;
      loop (Binop (Mul, lhs, parse_unary st))
    | TSlash ->
      advance st;
      loop (Binop (Div, lhs, parse_unary st))
    | _ -> lhs
  in
  loop (parse_unary st)

(* unary ::= "-" unary | application

   Written as ordinary right recursion, because the production is
   right recursive: [- - x] is [Neg (Neg (Var "x"))].  Sitting between
   multiplicative and application means [-f x] negates the *result* of
   the call, and [-x * y] multiplies the negated [x]. *)
and parse_unary st =
  match peek st with
  | TMinus ->
    advance st;
    Neg (parse_unary st)
  | _ -> parse_application st

(* application ::= atom { atom }

   The loop is what makes application left associative: each argument
   is folded into the function position of the next call, so [f x y] is
   [App (App (f, x), y)]. *)
and parse_application st =
  let rec loop lhs =
    if begins_atom (peek st) then loop (App (lhs, parse_atom st)) else lhs
  in
  loop (parse_atom st)

and parse_atom st =
  match peek st with
  | TInt n ->
    advance st;
    Int n
  | TTrue ->
    advance st;
    Bool true
  | TFalse ->
    advance st;
    Bool false
  | TIdent name ->
    advance st;
    Var name
  | TLParen ->
    advance st;
    let inner = parse_expr st in
    expect st TRParen;
    inner
  | other ->
    raise
      (Parse_error
         (Printf.sprintf "expected an expression but found %s" (string_of_token other)))

(* Parse a whole program, and insist that every token was consumed --
   otherwise [1 2 3 )] would quietly parse as [1 2 3]. *)
let parse source =
  let st = make_state (tokenize source) in
  let expression = parse_expr st in
  match peek st with
  | TEOF -> expression
  | other ->
    raise
      (Parse_error
         (Printf.sprintf "unexpected %s after the end of the expression"
            (string_of_token other)))

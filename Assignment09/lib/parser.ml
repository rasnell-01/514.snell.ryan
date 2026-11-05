(* Recursive-descent parser.

   term    ::= lambda x [: Type] . term
             | let x = term in term
             | if term then term else term
             | ascr
   ascr    ::= app {as Type}
   app     ::= head {postfix}
   head    ::= succ postfix | pred postfix | iszero postfix | postfix
   postfix ::= atom {. label}
   atom    ::= x | true | false | n | ( term ) | { [l = term {, l = term}] }

   Type    ::= TyAtom [-> Type]                      (right associative)
   TyAtom  ::= Bool | Nat | Top | ( Type ) | { [l : Type {, l : Type}] }

   Lambda, let, and if bodies extend as far right as possible, so
   "lambda x. x as T" ascribes the body. Write "(lambda x. x) as T" to
   ascribe the lambda itself. Duplicate labels are rejected in record
   expressions and in record types at any nesting depth. *)

open Syntax
open Lexer

exception Parse_error of string

type state = { toks : (token * pos) array; mutable i : int }

let peek st = fst st.toks.(st.i)

let advance st = if st.i < Array.length st.toks - 1 then st.i <- st.i + 1

let fail st msg =
  let tok, p = st.toks.(st.i) in
  raise
    (Parse_error
       (Printf.sprintf "line %d, column %d: %s (found %s)" p.line p.col msg
          (describe tok)))

let expect st tok what = if peek st = tok then advance st else fail st ("expected " ^ what)

let ident st what =
  match peek st with
  | IDENT x -> advance st; x
  | _ -> fail st ("expected " ^ what)

(* Parses "item {, item}" up to the closing brace, rejecting repeated
   labels. The opening brace has already been consumed. *)
let braced_fields st kind (item : state -> string * 'a) : (string * 'a) list =
  if peek st = RBRACE then (advance st; [])
  else begin
    let rec loop acc =
      let start = st.i in
      let ((l, _) as field) = item st in
      if List.mem_assoc l acc then begin
        st.i <- start;
        fail st (Printf.sprintf "duplicate label '%s' in %s" l kind)
      end;
      let acc = field :: acc in
      match peek st with
      | COMMA -> advance st; loop acc
      | RBRACE -> advance st; List.rev acc
      | _ -> fail st "expected ',' or '}'"
    in
    loop []
  end

let rec parse_ty st =
  let a = parse_ty_atom st in
  if peek st = ARROW then (advance st; TyArrow (a, parse_ty st)) else a

and parse_ty_atom st =
  match peek st with
  | TBOOL -> advance st; TyBool
  | TNAT -> advance st; TyNat
  | TTOP -> advance st; TyTop
  | LPAREN ->
    advance st;
    let t = parse_ty st in
    expect st RPAREN "')'";
    t
  | LBRACE ->
    advance st;
    TyRecord
      (braced_fields st "record type" (fun st ->
           let l = ident st "a field label" in
           expect st COLON "':'";
           (l, parse_ty st)))
  | _ -> fail st "expected a type"

let starts_postfix = function
  | IDENT _ | TRUE | FALSE | NUM _ | LPAREN | LBRACE -> true
  | _ -> false

let rec parse_term st =
  match peek st with
  | LAMBDA ->
    advance st;
    let x = ident st "a parameter name" in
    let ann = if peek st = COLON then (advance st; Some (parse_ty st)) else None in
    expect st DOT "'.' after the lambda parameter";
    Abs (x, ann, parse_term st)
  | LET ->
    advance st;
    let x = ident st "a variable name" in
    expect st EQ "'='";
    let e1 = parse_term st in
    expect st IN "'in'";
    Let (x, e1, parse_term st)
  | IF ->
    advance st;
    let c = parse_term st in
    expect st THEN "'then'";
    let a = parse_term st in
    expect st ELSE "'else'";
    If (c, a, parse_term st)
  | _ -> parse_ascr st

and parse_ascr st =
  let e = ref (parse_app st) in
  while peek st = AS do
    advance st;
    e := Ascribe (!e, parse_ty st)
  done;
  !e

and parse_app st =
  let head =
    match peek st with
    | SUCC -> advance st; Succ (parse_postfix st)
    | PRED -> advance st; Pred (parse_postfix st)
    | ISZERO -> advance st; IsZero (parse_postfix st)
    | _ -> parse_postfix st
  in
  let e = ref head in
  while starts_postfix (peek st) do
    e := App (!e, parse_postfix st)
  done;
  !e

and parse_postfix st =
  let e = ref (parse_atom st) in
  while peek st = DOT do
    advance st;
    e := Proj (!e, ident st "a field label after '.'")
  done;
  !e

and parse_atom st =
  match peek st with
  | IDENT x -> advance st; Var x
  | TRUE -> advance st; True
  | FALSE -> advance st; False
  | NUM n -> advance st; nat_literal n
  | LPAREN ->
    advance st;
    let t = parse_term st in
    expect st RPAREN "')'";
    t
  | LBRACE ->
    advance st;
    Record
      (braced_fields st "record expression" (fun st ->
           let l = ident st "a field label" in
           expect st EQ "'='";
           (l, parse_term st)))
  | _ -> fail st "expected an expression"

let parse_program (src : string) : term =
  let st = { toks = Array.of_list (tokenize src); i = 0 } in
  let t = parse_term st in
  if peek st <> EOF then fail st "unexpected input after the expression";
  t

let parse_type (src : string) : ty =
  let st = { toks = Array.of_list (tokenize src); i = 0 } in
  let t = parse_ty st in
  if peek st <> EOF then fail st "unexpected input after the type";
  t

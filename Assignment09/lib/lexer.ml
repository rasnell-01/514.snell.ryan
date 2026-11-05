(* Hand-written scanner. Comments are written (* like this *) and nest. *)

type token =
  | LAMBDA
  | LET
  | IN
  | IF
  | THEN
  | ELSE
  | TRUE
  | FALSE
  | SUCC
  | PRED
  | ISZERO
  | AS
  | TBOOL
  | TNAT
  | TTOP
  | IDENT of string
  | NUM of int
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | COLON
  | DOT
  | COMMA
  | EQ
  | ARROW
  | EOF

type pos = { line : int; col : int }

exception Lex_error of string

let describe = function
  | LAMBDA -> "'lambda'"
  | LET -> "'let'"
  | IN -> "'in'"
  | IF -> "'if'"
  | THEN -> "'then'"
  | ELSE -> "'else'"
  | TRUE -> "'true'"
  | FALSE -> "'false'"
  | SUCC -> "'succ'"
  | PRED -> "'pred'"
  | ISZERO -> "'iszero'"
  | AS -> "'as'"
  | TBOOL -> "'Bool'"
  | TNAT -> "'Nat'"
  | TTOP -> "'Top'"
  | IDENT x -> "identifier '" ^ x ^ "'"
  | NUM n -> "number " ^ string_of_int n
  | LPAREN -> "'('"
  | RPAREN -> "')'"
  | LBRACE -> "'{'"
  | RBRACE -> "'}'"
  | COLON -> "':'"
  | DOT -> "'.'"
  | COMMA -> "','"
  | EQ -> "'='"
  | ARROW -> "'->'"
  | EOF -> "end of input"

let keyword = function
  | "lambda" -> Some LAMBDA
  | "let" -> Some LET
  | "in" -> Some IN
  | "if" -> Some IF
  | "then" -> Some THEN
  | "else" -> Some ELSE
  | "true" -> Some TRUE
  | "false" -> Some FALSE
  | "succ" -> Some SUCC
  | "pred" -> Some PRED
  | "iszero" -> Some ISZERO
  | "as" -> Some AS
  | "Bool" -> Some TBOOL
  | "Nat" -> Some TNAT
  | "Top" -> Some TTOP
  | _ -> None

let is_ident_char c =
  match c with
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let tokenize (s : string) : (token * pos) list =
  let n = String.length s in
  let toks = ref [] in
  let line = ref 1 in
  let bol = ref 0 in
  let pos_at i = { line = !line; col = i - !bol + 1 } in
  let push tok i = toks := (tok, pos_at i) :: !toks in
  let error i msg =
    let p = pos_at i in
    raise (Lex_error (Printf.sprintf "line %d, column %d: %s" p.line p.col msg))
  in
  let rec skip_comment start i depth =
    if i >= n then error start "unterminated comment"
    else if s.[i] = '\n' then begin
      incr line;
      bol := i + 1;
      skip_comment start (i + 1) depth
    end
    else if s.[i] = '*' && i + 1 < n && s.[i + 1] = ')' then
      if depth = 1 then i + 2 else skip_comment start (i + 2) (depth - 1)
    else if s.[i] = '(' && i + 1 < n && s.[i + 1] = '*' then
      skip_comment start (i + 2) (depth + 1)
    else skip_comment start (i + 1) depth
  in
  let rec go i =
    if i >= n then push EOF i
    else
      match s.[i] with
      | '\n' ->
        incr line;
        bol := i + 1;
        go (i + 1)
      | ' ' | '\t' | '\r' -> go (i + 1)
      | '(' when i + 1 < n && s.[i + 1] = '*' -> go (skip_comment i (i + 2) 1)
      | '(' -> push LPAREN i; go (i + 1)
      | ')' -> push RPAREN i; go (i + 1)
      | '{' -> push LBRACE i; go (i + 1)
      | '}' -> push RBRACE i; go (i + 1)
      | ':' -> push COLON i; go (i + 1)
      | '.' -> push DOT i; go (i + 1)
      | ',' -> push COMMA i; go (i + 1)
      | '=' -> push EQ i; go (i + 1)
      | '-' when i + 1 < n && s.[i + 1] = '>' -> push ARROW i; go (i + 2)
      | '0' .. '9' ->
        let j = ref i in
        while !j < n && s.[!j] >= '0' && s.[!j] <= '9' do
          incr j
        done;
        push (NUM (int_of_string (String.sub s i (!j - i)))) i;
        go !j
      | 'a' .. 'z' | 'A' .. 'Z' | '_' ->
        let j = ref i in
        while !j < n && is_ident_char s.[!j] do
          incr j
        done;
        let word = String.sub s i (!j - i) in
        push (match keyword word with Some k -> k | None -> IDENT word) i;
        go !j
      | c -> error i (Printf.sprintf "unexpected character '%c'" c)
  in
  go 0;
  List.rev !toks

(* lexer.ml

   A hand-written scanner, in the same style as the lecture's, extended
   with the tokens the new productions need:

     Question 2   <  <=  >  >=  =  <>  &&  ||   and the keyword "rec"
     Question 3   fun  ->  \  .

   Supporting both [fun x -> e] and [\x. e] costs four tokens and gives
   us lambda-calculus notation for free. *)

type token =
  (* literals and names *)
  | TInt of int
  | TIdent of string
  | TTrue
  | TFalse
  (* keywords *)
  | TFun
  | TLet
  | TRec
  | TIn
  | TIf
  | TThen
  | TElse
  (* function syntax *)
  | TArrow (* -> *)
  | TBackslash (* \  *)
  | TDot (* .  *)
  (* arithmetic *)
  | TPlus
  | TMinus
  | TStar
  | TSlash
  (* comparison *)
  | TLt
  | TLe
  | TGt
  | TGe
  | TEq
  | TNe
  (* logical *)
  | TAnd (* && *)
  | TOr (* || *)
  (* grouping and end of input *)
  | TLParen
  | TRParen
  | TEOF

exception Lex_error of string

let string_of_token = function
  | TInt n -> string_of_int n
  | TIdent name -> name
  | TTrue -> "true"
  | TFalse -> "false"
  | TFun -> "fun"
  | TLet -> "let"
  | TRec -> "rec"
  | TIn -> "in"
  | TIf -> "if"
  | TThen -> "then"
  | TElse -> "else"
  | TArrow -> "->"
  | TBackslash -> "\\"
  | TDot -> "."
  | TPlus -> "+"
  | TMinus -> "-"
  | TStar -> "*"
  | TSlash -> "/"
  | TLt -> "<"
  | TLe -> "<="
  | TGt -> ">"
  | TGe -> ">="
  | TEq -> "="
  | TNe -> "<>"
  | TAnd -> "&&"
  | TOr -> "||"
  | TLParen -> "("
  | TRParen -> ")"
  | TEOF -> "end of input"

let is_digit c = c >= '0' && c <= '9'
let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_ident_char c = is_letter c || is_digit c || c = '\''
let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* Keywords are scanned as identifiers first and then looked up here,
   so that [letter] and [increment] are not mistaken for [let] and
   [in] followed by something else. *)
let keyword = function
  | "fun" -> Some TFun
  | "let" -> Some TLet
  | "rec" -> Some TRec
  | "in" -> Some TIn
  | "if" -> Some TIf
  | "then" -> Some TThen
  | "else" -> Some TElse
  | "true" -> Some TTrue
  | "false" -> Some TFalse
  | _ -> None

let tokenize source =
  let length = String.length source in
  (* [span] returns the end index of the longest run of characters
     starting at [start] that satisfy [ok]. *)
  let span ok start =
    let stop = ref start in
    while !stop < length && ok source.[!stop] do
      incr stop
    done;
    !stop
  in
  let rec scan position acc =
    if position >= length then List.rev (TEOF :: acc)
    else
      let c = source.[position] in
      if is_space c then scan (position + 1) acc
      else if is_digit c then begin
        let stop = span is_digit position in
        let text = String.sub source position (stop - position) in
        scan stop (TInt (int_of_string text) :: acc)
      end
      else if is_letter c then begin
        let stop = span is_ident_char position in
        let text = String.sub source position (stop - position) in
        let token = match keyword text with Some k -> k | None -> TIdent text in
        scan stop (token :: acc)
      end
      else begin
        (* Two-character operators must be tried before one-character
           ones, or [<=] would scan as [<] followed by [=]. *)
        let pair = if position + 1 < length then String.sub source position 2 else "" in
        match pair with
        | "->" -> scan (position + 2) (TArrow :: acc)
        | "<=" -> scan (position + 2) (TLe :: acc)
        | ">=" -> scan (position + 2) (TGe :: acc)
        | "<>" -> scan (position + 2) (TNe :: acc)
        | "&&" -> scan (position + 2) (TAnd :: acc)
        | "||" -> scan (position + 2) (TOr :: acc)
        | _ ->
          let single =
            match c with
            | '+' -> TPlus
            | '-' -> TMinus
            | '*' -> TStar
            | '/' -> TSlash
            | '<' -> TLt
            | '>' -> TGt
            | '=' -> TEq
            | '(' -> TLParen
            | ')' -> TRParen
            | '\\' -> TBackslash
            | '.' -> TDot
            | '&' -> raise (Lex_error "found '&'; the logical operator is '&&'")
            | '|' -> raise (Lex_error "found '|'; the logical operator is '||'")
            | other -> raise (Lex_error (Printf.sprintf "unexpected character %C" other))
          in
          scan (position + 1) (single :: acc)
      end
  in
  scan 0 []

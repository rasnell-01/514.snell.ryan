(* identifiers.mll
   Question 2, part 1: C++ identifiers.

   A C++ identifier is a letter or underscore, followed by zero or
   more letters, digits, or underscores:

       [a-zA-Z_][a-zA-Z0-9_]*
*)

{
  type result = Ident of string | Junk of string
}

let letter = ['a'-'z' 'A'-'Z']
let digit  = ['0'-'9']
let ident  = (letter | '_') (letter | digit | '_')*

rule token = parse
  | ident as id   { Some (Ident id) }
  | eof           { None }
  | _+ as junk    { Some (Junk junk) }

{
let classify (s : string) : string =
  let lexbuf = Lexing.from_string s in
  match token lexbuf with
  | Some (Ident id) when String.length id = String.length s ->
    Printf.sprintf "%-12s -> VALID identifier" id
  | Some (Ident id) ->
    Printf.sprintf "%-12s -> starts like an identifier (%s) but has trailing junk -> INVALID" s id
  | Some (Junk _) | None ->
    Printf.sprintf "%-12s -> INVALID identifier" s

let () =
  let tests = [
    "foo";            (* plain lowercase identifier *)
    "_bar123";        (* leading underscore, trailing digits *)
    "My_Class2";      (* mixed case, underscore, digit *)
    "3illegal";       (* starts with a digit: not valid *)
    "has space";      (* contains a space: not valid *)
    "__init__";       (* dunder-style identifier *)
  ] in
  List.iter (fun s -> print_endline (classify s)) tests
}

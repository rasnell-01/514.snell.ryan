(* floats.mll
   Question 2, part 3: floating point numbers that may optionally
   include a leading sign and a decimal point.

       [+-]? digit+ ('.' digit+)?

   i.e. an optional sign, one or more digits, and an optional
   '.' followed by one or more digits.
*)

let digit = ['0'-'9']
let sign  = ['+' '-']
let float_lit = sign? digit+ ('.' digit+)?

rule token = parse
  | float_lit as f { Some f }
  | eof             { None }
  | _+              { None }

{
let is_valid (s : string) : bool =
  let lexbuf = Lexing.from_string s in
  match token lexbuf with
  | Some f -> f = s
  | None -> false

let () =
  let tests = [
    "42";        (* plain unsigned integer *)
    "+42";       (* explicit positive sign, no decimal *)
    "-3.14";     (* negative, with decimal point *)
    "3.14159";   (* unsigned with decimal point *)
    "-.5";       (* no leading digit before '.': rejected by this grammar *)
    "1.";        (* trailing '.' with no digits after: rejected *)
    "1.2.3";     (* two decimal points: rejected *)
  ] in
  List.iter (fun s ->
    Printf.printf "%-10s -> %s\n" s (if is_valid s then "VALID" else "INVALID"))
    tests
}

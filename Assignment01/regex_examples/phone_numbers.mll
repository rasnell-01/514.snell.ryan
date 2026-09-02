(* phone_numbers.mll
   Question 2, part 2: U.S. phone numbers.

   Two accepted shapes:
       (XXX) XXX-XXXX
       XXX-XXX-XXXX

   ocamllex does not support the {n} counted-repetition syntax, so a
   run of exactly three or four digits is spelled out digit by digit.

       digit digit digit                       -- exactly 3 digits
       digit digit digit digit                 -- exactly 4 digits

       '(' ddd ')' ' ' ddd '-' dddd             (XXX) XXX-XXXX
     | ddd '-' ddd '-' dddd                     XXX-XXX-XXXX
*)

let digit = ['0'-'9']
let d3    = digit digit digit
let d4    = digit digit digit digit

let phone =
    ('(' d3 ')' ' ' d3 '-' d4)
  | (d3 '-' d3 '-' d4)

rule token = parse
  | phone as p { Some p }
  | eof        { None }
  | _+ as junk { ignore junk; None }

{
let is_valid (s : string) : bool =
  let lexbuf = Lexing.from_string s in
  match token lexbuf with
  | Some p -> p = s && String.length p = String.length s
  | None -> false

let () =
  let tests = [
    "(256) 555-0134";  (* parenthesized area code form *)
    "256-555-0134";    (* dashed form *)
    "256.555.0134";    (* wrong separators *)
    "(256)555-0134";   (* missing required space after ) *)
    "25-555-01345";    (* wrong digit groupings *)
  ] in
  List.iter (fun s ->
    Printf.printf "%-16s -> %s\n" s (if is_valid s then "VALID" else "INVALID"))
    tests
}

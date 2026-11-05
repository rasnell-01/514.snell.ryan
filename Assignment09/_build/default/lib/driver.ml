(* Parse, synthesize at the root, and evaluate only if synthesis succeeds. *)

open Syntax

type outcome =
  | Syntax_error of string
  | Static_error of term * Typecheck.type_error
  | Success of { program : term; ty : ty; value : Eval.value }
  | Runtime_failure of term * ty * string

let run ?(trace = false) (source : string) : outcome * string list =
  match Parser.parse_program source with
  | exception (Lexer.Lex_error msg | Parser.Parse_error msg) -> (Syntax_error msg, [])
  | program -> (
    let result, lines =
      if trace then Typecheck.synth_traced Context.empty program
      else (Typecheck.synth Context.empty program, [])
    in
    match result with
    | Error e -> (Static_error (program, e), lines)
    | Ok ty -> (
      match Eval.eval program with
      | value -> (Success { program; ty; value }, lines)
      | exception Eval.Runtime_error msg -> (Runtime_failure (program, ty, msg), lines)))

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

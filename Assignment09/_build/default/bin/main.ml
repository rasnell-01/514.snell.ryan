(* Command-line driver.

     dune exec ./bin/main.exe -- [--trace-types] [--ast] FILE
     dune exec ./bin/main.exe -- [--trace-types] -e 'EXPR'

   Exit status: 0 success, 1 type error, 2 syntax error, 3 runtime error. *)

open Stlc

let () =
  let trace = ref false in
  let show_ast = ref false in
  let expr = ref None in
  let file = ref None in
  let usage = "usage: main.exe [--trace-types] [--ast] (FILE | -e EXPR)" in
  Arg.parse
    [
      ("--trace-types", Arg.Set trace, " Print the direction of every typing call");
      ("--ast", Arg.Set show_ast, " Print the parsed program before typing it");
      ("-e", Arg.String (fun s -> expr := Some s), "EXPR Run EXPR instead of a file");
    ]
    (fun f -> file := Some f)
    usage;
  let source =
    match !expr, !file with
    | Some e, _ -> e
    | None, Some f -> Driver.read_file f
    | None, None -> In_channel.input_all stdin
  in
  let outcome, trace_lines = Driver.run ~trace:!trace source in
  let print_program p =
    if !show_ast then print_endline ("program: " ^ Syntax.string_of_term p)
  in
  let print_trace () =
    if !trace then begin
      print_endline "--- type trace ---";
      List.iter print_endline trace_lines;
      print_endline "--- end trace ---"
    end
  in
  match outcome with
  | Driver.Syntax_error msg ->
    prerr_endline ("Syntax error: " ^ msg);
    exit 2
  | Driver.Static_error (p, e) ->
    print_program p;
    print_trace ();
    print_endline (Typecheck.string_of_error e);
    print_endline "evaluation skipped: the program did not typecheck";
    exit 1
  | Driver.Success { program; ty; value } ->
    print_program program;
    print_trace ();
    print_endline ("type:  " ^ Syntax.string_of_ty ty);
    print_endline ("value: " ^ Eval.string_of_value value)
  | Driver.Runtime_failure (p, ty, msg) ->
    print_program p;
    print_trace ();
    print_endline ("type:  " ^ Syntax.string_of_ty ty);
    prerr_endline ("Runtime error: " ^ msg);
    exit 3

(* Demo: every example shows its static result (the type) and its dynamic
   result (the evaluated value), then a few proof trees and failure reports. *)

open Stlc
open Syntax
open Context
open Typecheck
open Derivation

let b = TyBool
let arrow a c = TyArrow (a, c)

let id_bool = Abs ("x", b, Var "x")
let id_bool_y = Abs ("y", b, Var "y")
let not_fn = Abs ("b", b, If (Var "b", False, True))
let apply_f = Abs ("f", arrow b b, Abs ("x", b, App (Var "f", Var "x")))

let well_typed =
  [ ("Boolean identity", id_bool);
    ("identity applied to true", App (id_bool, True));
    ("higher-order function", apply_f);
    ("higher-order function, fully applied", App (App (apply_f, not_fn), True));
    ("conditional", If (App (not_fn, True), id_bool, id_bool_y));
    ("shadowing: inner x wins",
     Abs ("x", arrow b b, Abs ("x", b, Var "x"))) ]

let ill_typed =
  [ ("applying a Boolean as a function", App (True, False));
    ("argument type mismatch", App (id_bool, id_bool_y));
    ("branch type mismatch", If (True, True, id_bool));
    ("non-Boolean condition", If (id_bool, True, False));
    ("unbound variable", App (id_bool, Var "z")) ]

let show_typed (name, t) =
  Printf.printf "%s\n" name;
  Printf.printf "  term  : %s\n" (string_of_term t);
  (match typeof empty_context t with
   | Ok ty ->
     Printf.printf "  type  : %s\n" (string_of_ty ty);
     Printf.printf "  value : %s\n" (string_of_term (Eval.eval t))
   | Error e ->
     Printf.printf "  type  : REJECTED (%s)\n" (string_of_type_error e);
     Printf.printf "  value : not evaluated\n");
  print_newline ()

let section title =
  Printf.printf "==== %s ====\n\n" title

let () =
  section "Well-typed terms: type (static) and value (dynamic)";
  List.iter show_typed well_typed;

  section "Ill-typed terms: rejected before evaluation";
  List.iter show_typed ill_typed;

  section "Why the type checker matters: evaluation alone gets stuck";
  let stuck = Eval.eval (App (True, False)) in
  Printf.printf "  eval (%s) = %s   (no rule applies)\n\n"
    (string_of_term (App (True, False)))
    (string_of_term stuck);

  section "Typing derivation: (lambda x:Bool. x) true";
  print_endline (report empty_context (App (id_bool, True)));
  print_newline ();

  section "Typing derivation: higher-order function";
  print_endline (report empty_context apply_f);
  print_newline ();

  section "Typing derivation: conditional with a free variable in Gamma";
  let ctx = extend "p" b empty_context in
  print_endline (report ctx (If (Var "p", False, True)));
  print_newline ();

  section "Failed derivations";
  List.iter
    (fun (name, t) ->
      Printf.printf "%s\n%s\n\n" name (report empty_context t))
    ill_typed

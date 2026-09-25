(* test_env.ml -- unit tests for Question 1.

   Run with [dune test], or [dune exec test/test_env.exe -- -runner
   sequential] to see each case listed. *)

open OUnit2
open Interp

let show_int_option = function None -> "None" | Some n -> "Some " ^ string_of_int n
let show_string_option = function None -> "None" | Some s -> "Some " ^ s
let show_bool = string_of_bool

(* The sample environment from the assignment:  x -> 10, y -> 20, z -> 30 *)
let sample =
  Env.empty |> Env.extend "x" 10 |> Env.extend "y" 20 |> Env.extend "z" 30

let lookup_tests =
  [
    ( "empty has nothing in it" >:: fun _ ->
      assert_equal ~printer:show_int_option None (Env.lookup "x" Env.empty) );
    ( "a binding can be looked up" >:: fun _ ->
      assert_equal ~printer:show_int_option (Some 10) (Env.lookup "x" sample) );
    ( "every binding can be looked up" >:: fun _ ->
      assert_equal ~printer:show_int_option (Some 10) (Env.lookup "x" sample);
      assert_equal ~printer:show_int_option (Some 20) (Env.lookup "y" sample);
      assert_equal ~printer:show_int_option (Some 30) (Env.lookup "z" sample) );
    ( "an unbound name gives None" >:: fun _ ->
      assert_equal ~printer:show_int_option None (Env.lookup "w" sample) );
    ( "lookup is case sensitive" >:: fun _ ->
      assert_equal ~printer:show_int_option None (Env.lookup "X" sample) );
    ( "the empty name is just another name" >:: fun _ ->
      let env = Env.extend "" 1 Env.empty in
      assert_equal ~printer:show_int_option (Some 1) (Env.lookup "" env) );
  ]

let is_bound_tests =
  [
    ( "nothing is bound in empty" >:: fun _ ->
      assert_equal ~printer:show_bool false (Env.is_bound "x" Env.empty) );
    ( "is_bound is true for a binding that exists" >:: fun _ ->
      assert_equal ~printer:show_bool true (Env.is_bound "y" sample) );
    ( "is_bound is false for one that does not" >:: fun _ ->
      assert_equal ~printer:show_bool false (Env.is_bound "w" sample) );
    ( "is_bound agrees with lookup" >:: fun _ ->
      List.iter
        (fun name ->
          let expected = Env.lookup name sample <> None in
          assert_equal ~printer:show_bool ~msg:name expected (Env.is_bound name sample))
        [ "x"; "y"; "z"; "w"; "X"; "" ] );
  ]

(* The requirement that an environment is a value, not a mutable
   structure, is the one worth testing hardest: closures depend on an
   environment they captured earlier staying exactly as it was. *)
let persistence_tests =
  [
    ( "extend leaves the original environment alone" >:: fun _ ->
      let outer = Env.extend "x" 1 Env.empty in
      let inner = Env.extend "y" 2 outer in
      assert_equal ~printer:show_int_option (Some 2) (Env.lookup "y" inner);
      assert_equal ~printer:show_int_option None (Env.lookup "y" outer) );
    ( "a shadowing extend does not disturb the older environment" >:: fun _ ->
      let outer = Env.extend "x" 1 Env.empty in
      let inner = Env.extend "x" 2 outer in
      assert_equal ~printer:show_int_option (Some 2) (Env.lookup "x" inner);
      assert_equal ~printer:show_int_option (Some 1) (Env.lookup "x" outer) );
    ( "two extensions of one environment are independent" >:: fun _ ->
      let base = Env.extend "x" 0 Env.empty in
      let left = Env.extend "x" 1 base in
      let right = Env.extend "x" 2 base in
      assert_equal ~printer:show_int_option (Some 1) (Env.lookup "x" left);
      assert_equal ~printer:show_int_option (Some 2) (Env.lookup "x" right);
      assert_equal ~printer:show_int_option (Some 0) (Env.lookup "x" base) );
  ]

let shadowing_tests =
  [
    ( "the most recent binding wins" >:: fun _ ->
      let env = sample |> Env.extend "x" 99 in
      assert_equal ~printer:show_int_option (Some 99) (Env.lookup "x" env) );
    ( "shadowing three deep" >:: fun _ ->
      let env =
        Env.empty |> Env.extend "n" 1 |> Env.extend "n" 2 |> Env.extend "n" 3
      in
      assert_equal ~printer:show_int_option (Some 3) (Env.lookup "n" env) );
    ( "shadowing one name leaves the others visible" >:: fun _ ->
      let env = Env.extend "y" 99 sample in
      assert_equal ~printer:show_int_option (Some 99) (Env.lookup "y" env);
      assert_equal ~printer:show_int_option (Some 10) (Env.lookup "x" env);
      assert_equal ~printer:show_int_option (Some 30) (Env.lookup "z" env) );
  ]

(* The type is ['a t], so the same three operations have to work for
   whatever the interpreter decides a value is. *)
let polymorphism_tests =
  [
    ( "an environment of strings" >:: fun _ ->
      let env = Env.empty |> Env.extend "greeting" "hello" in
      assert_equal ~printer:show_string_option (Some "hello")
        (Env.lookup "greeting" env) );
    ( "an environment of functions" >:: fun _ ->
      let env = Env.empty |> Env.extend "double" (fun n -> n * 2) in
      match Env.lookup "double" env with
      | Some f -> assert_equal ~printer:string_of_int 14 (f 7)
      | None -> assert_failure "double should be bound" );
    ( "an environment of environments" >:: fun _ ->
      let env = Env.empty |> Env.extend "inner" sample in
      match Env.lookup "inner" env with
      | Some captured ->
        assert_equal ~printer:show_int_option (Some 20) (Env.lookup "y" captured)
      | None -> assert_failure "inner should be bound" );
  ]

let convenience_tests =
  [
    ( "of_list binds every pair" >:: fun _ ->
      let env = Env.of_list [ ("x", 10); ("y", 20); ("z", 30) ] in
      assert_equal ~printer:show_int_option (Some 10) (Env.lookup "x" env);
      assert_equal ~printer:show_int_option (Some 30) (Env.lookup "z" env) );
    ( "of_list lets the rightmost pair win" >:: fun _ ->
      let env = Env.of_list [ ("x", 1); ("x", 2) ] in
      assert_equal ~printer:show_int_option (Some 2) (Env.lookup "x" env) );
    ( "bindings lists the visible bindings innermost first" >:: fun _ ->
      let names = List.map fst (Env.bindings sample) in
      assert_equal ~printer:(String.concat ", ") [ "z"; "y"; "x" ] names );
    ( "bindings leaves out what is shadowed" >:: fun _ ->
      let env = Env.extend "x" 99 sample in
      assert_equal ~printer:string_of_int 3 (List.length (Env.bindings env));
      assert_equal ~printer:show_int_option (Some 99) (List.assoc_opt "x" (Env.bindings env)) );
    ( "to_string renders the visible bindings" >:: fun _ ->
      assert_equal ~printer:(fun s -> s) "[z = 30; y = 20; x = 10]"
        (Env.to_string string_of_int sample) );
    ( "to_string of the empty environment" >:: fun _ ->
      assert_equal ~printer:(fun s -> s) "[]" (Env.to_string string_of_int Env.empty) );
  ]

let suite =
  "Env"
  >::: [
         "lookup" >::: lookup_tests;
         "is_bound" >::: is_bound_tests;
         "persistence" >::: persistence_tests;
         "shadowing" >::: shadowing_tests;
         "polymorphism" >::: polymorphism_tests;
         "convenience" >::: convenience_tests;
       ]

let () = run_test_tt_main suite

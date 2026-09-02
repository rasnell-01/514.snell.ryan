open Lambda

let print_size label t =
  Printf.printf "size (%s) = %d\n" label (size t)

let print_is_value label t =
  Printf.printf "is_value (%s) = %b\n" label (is_value t)

let () =
  Printf.printf "Q7: %s\n" (to_string q7_example);
  Printf.printf "Q8: %s\n" (to_string q8_example);
  print_newline ();

  (* size (Abs ("x", Var "x")) should return 2 *)
  print_size "\\x.x" (Abs ("x", Var "x"));
  print_size "Q7 example" q7_example;
  print_size "Q8 example" q8_example;
  print_newline ();

  (* is_value (Abs ("x", Var "x")) should return true *)
  print_is_value "\\x.x" (Abs ("x", Var "x"));
  (* is_value (Var "x") should return false *)
  print_is_value "x" (Var "x");
  print_is_value "(x y)" (App (Var "x", Var "y"))

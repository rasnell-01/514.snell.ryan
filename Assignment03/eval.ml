(* eval.ml

   An environment-and-closure interpreter.  Nothing here substitutes
   into an expression: a function evaluates to a closure that carries
   the environment it was defined in, and applying the closure
   evaluates the body in *that* environment extended with the
   parameter.  That single choice is what gives us lexical scope, and
   it is also why we never have to rename a bound variable to avoid
   capture. *)

open Ast

(* A runtime value is not an expression.  [Fun ("x", body)] is a piece
   of source text; the value it denotes also has to remember where it
   came from, which is the third field of [VClosure].

   The environment is [Env.t] from Question 1 rather than a bare
   association list, so the interpreter can only reach it through
   [empty], [extend] and [lookup]. *)
type value =
  | VInt of int
  | VBool of bool
  | VClosure of string * expr * env
  (* A recursive closure additionally knows the name it was bound to,
     so that applying it can put itself back into scope.  See the
     discussion of [let rec] in the docs folder. *)
  | VRecClosure of string * string * expr * env
  (* A function supplied by the runtime rather than written in the
     source language; this is how the predefined bindings work. *)
  | VBuiltin of string * (value -> value)

and env = value Env.t

exception Runtime_error of string

(* A closure must not print its captured environment: that environment
   may contain the closure itself, and even when it does not, the
   output is enormous. *)
let string_of_value = function
  | VInt n -> string_of_int n
  | VBool b -> string_of_bool b
  | VClosure _ -> "<closure>"
  | VRecClosure (name, _, _, _) -> "<closure " ^ name ^ ">"
  | VBuiltin (name, _) -> "<builtin " ^ name ^ ">"

let type_error context expected actual =
  raise
    (Runtime_error
       (Printf.sprintf "%s expects %s but got %s" context expected
          (string_of_value actual)))

(* ------------------------------------------------------------------ *)
(* Tracing.  Environments are invisible in the source text, so the
   cheapest way to see what the interpreter is doing is to print them. *)

let trace = ref false
let depth = ref 0

let say line =
  if !trace then print_string (String.make (2 * !depth) ' ' ^ line ^ "\n")

(* The predefined bindings are in every environment and never change,
   so printing them on every line would bury the bindings the trace is
   actually about. *)
let show_env env =
  let interesting (_, value) =
    match value with VBuiltin _ -> false | _ -> true
  in
  let one (name, value) = name ^ " = " ^ string_of_value value in
  "[" ^ String.concat "; " (List.map one (List.filter interesting (Env.bindings env))) ^ "]"

(* ------------------------------------------------------------------ *)

let arithmetic op lhs rhs =
  match (op, lhs, rhs) with
  | Add, VInt a, VInt b -> VInt (a + b)
  | Sub, VInt a, VInt b -> VInt (a - b)
  | Mul, VInt a, VInt b -> VInt (a * b)
  | Div, VInt _, VInt 0 -> raise (Runtime_error "division by zero")
  | Div, VInt a, VInt b -> VInt (a / b)
  | Lt, VInt a, VInt b -> VBool (a < b)
  | Le, VInt a, VInt b -> VBool (a <= b)
  | Gt, VInt a, VInt b -> VBool (a > b)
  | Ge, VInt a, VInt b -> VBool (a >= b)
  | Eq, VInt a, VInt b -> VBool (a = b)
  | Eq, VBool a, VBool b -> VBool (a = b)
  | Ne, VInt a, VInt b -> VBool (a <> b)
  | Ne, VBool a, VBool b -> VBool (a <> b)
  | (And | Or), _, _ ->
    (* Unreachable: [eval] handles these itself so that they can short
       circuit.  Raising rather than asserting keeps the failure
       reportable if a future change routes them here. *)
    raise (Runtime_error "&& and || are evaluated by eval, not by arithmetic")
  | _ ->
    raise
      (Runtime_error
         (Printf.sprintf "operator %s cannot be applied to %s and %s"
            (symbol_of_binop op) (string_of_value lhs) (string_of_value rhs)))

let rec eval env expr =
  if not !trace then eval_expr env expr
  else begin
    say ("eval: " ^ Ast.to_source_short expr);
    say ("env : " ^ show_env env);
    incr depth;
    let result = eval_expr env expr in
    decr depth;
    say ("value: " ^ string_of_value result);
    result
  end

and eval_expr env expr =
  match expr with
  | Int n -> VInt n
  | Bool b -> VBool b
  | Var name -> (
    match Env.lookup name env with
    | Some value -> value
    | None -> raise (Runtime_error ("unbound variable: " ^ name)))
  | Neg operand -> (
    match eval env operand with
    | VInt n -> VInt (-n)
    | other -> type_error "unary -" "an integer" other)
  (* [&&] and [||] short circuit, so they cannot go through the
     generic path, which evaluates both operands first. *)
  | Binop (And, lhs, rhs) -> (
    match eval env lhs with
    | VBool false -> VBool false
    | VBool true -> (
      match eval env rhs with
      | VBool b -> VBool b
      | other -> type_error "&&" "a boolean" other)
    | other -> type_error "&&" "a boolean" other)
  | Binop (Or, lhs, rhs) -> (
    match eval env lhs with
    | VBool true -> VBool true
    | VBool false -> (
      match eval env rhs with
      | VBool b -> VBool b
      | other -> type_error "||" "a boolean" other)
    | other -> type_error "||" "a boolean" other)
  (* The two [let]s are deliberate.  Writing
     [arithmetic op (eval env lhs) (eval env rhs)] would leave the
     order of evaluation up to OCaml, which evaluates arguments right
     to left; the interpreted language should decide that for itself,
     and left to right is what the trace and the error messages assume. *)
  | Binop (op, lhs, rhs) ->
    let left = eval env lhs in
    let right = eval env rhs in
    arithmetic op left right
  | If (condition, consequent, alternative) -> (
    match eval env condition with
    | VBool true -> eval env consequent
    | VBool false -> eval env alternative
    | other -> type_error "the condition of if" "a boolean" other)
  | Let (name, bound, body) ->
    let value = eval env bound in
    eval (Env.extend name value env) body
  (* [let rec f = fun x -> ...] builds a closure that knows its own
     name.  Only a function may be bound recursively: [let rec x = x + 1]
     has nothing to delay the reference to [x]. *)
  | LetRec (name, Fun (parameter, body), rest) ->
    let closure = VRecClosure (name, parameter, body, env) in
    eval (Env.extend name closure env) rest
  | LetRec (name, _, _) ->
    raise
      (Runtime_error
         ("the right-hand side of let rec " ^ name ^ " must be a function"))
  (* The body is not evaluated, no variable is replaced, and the
     defining environment is kept. *)
  | Fun (parameter, body) ->
    let closure = VClosure (parameter, body, env) in
    if !trace then begin
      say "created closure:";
      say ("  parameter = " ^ parameter);
      say ("  captured  = " ^ show_env env)
    end;
    closure
  | App (fn_expr, arg_expr) -> (
    let fn_value = eval env fn_expr in
    let arg_value = eval env arg_expr in
    match fn_value with
    | VClosure (parameter, body, closure_env) ->
      (* [closure_env], not [env]: the body must see the bindings that
         were in scope where the function was written, not the ones in
         scope where it happens to be called. *)
      let body_env = Env.extend parameter arg_value closure_env in
      if !trace then begin
        say "apply closure:";
        say ("  argument = " ^ string_of_value arg_value);
        say ("  body env = " ^ show_env body_env)
      end;
      eval body_env body
    | VRecClosure (name, parameter, body, closure_env) ->
      (* Same rule, plus the function's own name, so the body can call
         itself.  The binding is added at application time, which is
         what keeps the value from having to contain itself. *)
      let body_env =
        closure_env
        |> Env.extend name fn_value
        |> Env.extend parameter arg_value
      in
      if !trace then begin
        say ("apply closure " ^ name ^ ":");
        say ("  argument = " ^ string_of_value arg_value);
        say ("  body env = " ^ show_env body_env)
      end;
      eval body_env body
    | VBuiltin (_, fn) -> fn arg_value
    | other ->
      raise
        (Runtime_error
           ("attempt to call a non-function: " ^ string_of_value other)))

(* ------------------------------------------------------------------ *)
(* Predefined bindings.

   A C++ program can name [cin] and [cout] without declaring them
   because the runtime has already put them in the outermost scope.
   The same trick works here: evaluation starts in [prelude] rather
   than in [Env.empty].  Since [extend] shadows, a program that binds
   its own [max] simply hides this one. *)

let expect_int name value =
  match value with
  | VInt n -> n
  | other -> type_error name "an integer" other

let builtin1 name fn = VBuiltin (name, fun a -> fn (expect_int name a))

let builtin2 name fn =
  VBuiltin (name, fun a -> VBuiltin (name, fun b ->
    fn (expect_int name a) (expect_int name b)))

let prelude : env =
  Env.of_list
    [
      ("abs", builtin1 "abs" (fun n -> VInt (abs n)));
      ("succ", builtin1 "succ" (fun n -> VInt (n + 1)));
      ("pred", builtin1 "pred" (fun n -> VInt (n - 1)));
      ("max", builtin2 "max" (fun a b -> VInt (if a > b then a else b)));
      ("min", builtin2 "min" (fun a b -> VInt (if a < b then a else b)));
    ]

(* ------------------------------------------------------------------ *)
(* Front door: text in, value out. *)

let eval_expr_in ?(env = prelude) expr =
  depth := 0;
  eval env expr

let run ?(env = prelude) source = eval_expr_in ~env (Parser.parse source)

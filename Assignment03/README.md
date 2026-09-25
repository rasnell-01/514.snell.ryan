# Assignment 3

An environment module, a recursive-descent parser for an extended
expression grammar, and a closure-based interpreter for it. The three
questions share one implementation: the environment from Question 1 is
what the interpreter runs on, and the productions from Question 2 live
in the same parser as the function syntax from Question 3.

## Where each question is answered

| Question | Implementation | Tests |
| --- | --- | --- |
| 1, the environment type | `src/lib/env.mli`, `src/lib/env.ml` | `src/test/test_env.ml` |
| 2, unary / comparison / logical / let rec | `src/lib/lexer.ml`, `src/lib/parser.ml` | `src/test/test_interp.ml` |
| 3, functions, application, closures | `src/lib/ast.ml`, `src/lib/eval.ml` | `src/test/test_interp.ml` |
| 3, analysis question 10 | `src/lib/debruijn.ml` | `src/test/test_interp.ml` |

The written answers, including the two thought questions from Question
1 and the ten analysis questions from Question 3, are in
`docs/analysis.md` and `docs/analysis.pdf`.

## Building and running

From the `src` directory:

```
dune build                 compile everything
dune test                  run both OUnit2 suites (115 cases)
dune exec bin/main.exe     print the walkthrough, ending in a traced run
```

The runner takes a couple of flags:

```
dune exec bin/main.exe -- -e "let add = fun x y -> x + y in add 2 3"
dune exec bin/main.exe -- --repl
```

Tracing can also be switched on from anywhere by setting
`Eval.trace := true`, which prints each expression, the environment it
is evaluated in, every closure as it is created, and the environment
each closure body runs in.

## The language

```
let rec fact n = if n <= 1 then 1 else n * fact (n - 1) in fact 10
let twice = fun f x -> f (f x) in twice (fun x -> x * 2) 3
\x. x + 1
```

Integers and booleans; `+ - * /` with unary minus; `< <= > >= = <>`;
`&&` and `||`, both short-circuiting; `if ... then ... else ...`;
`let`, `let rec`, and one-argument functions written either as
`fun x -> e` or as `\x. e`, with multiple parameters curried
automatically. `abs`, `succ`, `pred`, `max` and `min` are predefined
and can be shadowed.

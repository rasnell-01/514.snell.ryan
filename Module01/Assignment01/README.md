# Assignment01

Written responses: `docs/answers.md` (parse trees, grammar, and explanations).

## Building and running

**Question 1 — rose trees**
```
cd rose_tree
ocamlc rose.ml -o rose
./rose
```

**Question 2 — regex / ocamllex examples**
```
cd regex_examples
ocamllex identifiers.mll   && ocamlc identifiers.ml -o identifiers   && ./identifiers
ocamllex phone_numbers.mll && ocamlc phone_numbers.ml -o phone_numbers && ./phone_numbers
ocamllex floats.mll        && ocamlc floats.ml -o floats            && ./floats
ocamllex palindromes.mll   && ocamlc palindromes.ml -o palindromes  && ./palindromes
```

**Question 4 — extended expression evaluator**
```
cd parser
ocamlc expr_parser.ml -o expr_parser
./expr_parser
```

All of the above were built and test-run with OCaml 4.14.1 while
preparing this assignment; every sample input/output shown in
`docs/answers.md` is real output from these programs, not
hand-typed.

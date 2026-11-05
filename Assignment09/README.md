# Assignment09: Bidirectional Typing with Subtyping

This project extends the Assignment08 interpreter (Booleans, natural numbers, Top, records, structural subtyping, ascription, and let) with bidirectional type checking. A lambda parameter annotation can now be omitted when the surrounding context supplies an expected function type.

## Build and run

```
dune build
dune runtest
dune exec ./bin/main.exe -- examples/contextual_lambda.stlc
dune exec ./bin/main.exe -- --trace-types examples/contextual_lambda.stlc
dune exec ./bin/main.exe -- -e '((lambda x. succ x) as (Nat -> Nat)) 0'
```

Driver options:

| Option | Effect |
|---|---|
| `--trace-types` | Print every synthesis and checking call before the result |
| `--ast` | Print the parsed program (normalized) before typing |
| `-e EXPR` | Run `EXPR` instead of reading a file |

With no file and no `-e`, the program is read from standard input. The driver prints `type:` and `value:` on success. Exit status: 0 success, 1 type error, 2 syntax error, 3 runtime error. A program is evaluated only after top-level synthesis succeeds.

## Project layout

```
Assignment09/
  dune-project
  bin/main.ml          command-line driver
  lib/syntax.ml        types, terms (Abs of string * ty option * term), printers
  lib/lexer.ml         scanner
  lib/parser.ml        recursive-descent parser
  lib/context.ml       typing contexts
  lib/subtype.ml       subtype relation from Assignment08 (unchanged)
  lib/typecheck.ml     synth / check, error classification, trace
  lib/eval.ml          call-by-value closure evaluator
  lib/driver.ml        parse -> synthesize -> evaluate
  test/test_main.ml    188 checks
  examples/            programs A-H (one file each)
  examples/reject/     the ten required rejection programs
  examples/assignment08/  annotated programs from the subtyping assignment
  examples/extra/      Student/Person, shadowing, runtime record, if-vs-Top
  DESIGN.md            written analysis
```

## Supported syntax

```
term    ::= lambda x : Type . term        annotated lambda
          | lambda x . term               unannotated lambda (new)
          | let x = term in term
          | if term then term else term
          | term as Type                  ascription
          | term term                     application (left associative)
          | succ t | pred t | iszero t
          | t . l                         projection
          | { l = term, ... }             record ({} is the empty record)
          | x | true | false | 0 | 1 | 2 ...   (n means n succs applied to 0)
          | ( term )

Type    ::= Bool | Nat | Top | Type -> Type | { l : Type, ... } | ( Type )
```

Precedence, loosest to tightest: lambda/let/if bodies (extend as far right as possible), `as`, application and `succ`/`pred`/`iszero`, projection, atoms. Arrows associate to the right. So `lambda x. x as T` ascribes the body. Write `(lambda x. x) as T` to ascribe the lambda. Comments are written `(* ... *)` and can nest.

Duplicate labels are rejected in record expressions and in record types at any depth, both by the parser and by the type checker (for hand-built ASTs). The type grammar is unchanged: every written annotation is a complete type, and there are no inference variables.

## Typing rules

`synth` (G |- e => T) computes a type. `check` (G |- e <= T) answers yes or no against an expected type.

| Rule | Behavior |
|---|---|
| T-Var, T-True, T-False, T-Zero | As before |
| T-Succ, T-Pred, T-IsZero | Check the operand against Nat |
| T-Abs | Annotated lambda only: bind `x:S`, synthesize the body, return `S -> T` |
| (none) | An unannotated lambda cannot be synthesized: insufficient information |
| T-App | Synthesize the function, require an arrow, **check** the argument against its domain |
| T-Rcd, T-Proj | Synthesize fields / receiver |
| T-Ascribe | Check the operand against the annotation, synthesize the annotation |
| T-Let | Synthesize the binding (one monomorphic type), synthesize the body |
| T-If | Check the condition against Bool, synthesize both branches, require mutual subtyping |
| C-Abs | `lambda x. e` against `A -> B`: bind `x:A`, check `e` against `B` |
| C-AbsAnn | `lambda x:S. e` against `A -> B`: require `A <: S`, bind `x:S` (the written type), check `e` against `B` |
| C-Rcd | Record against record type: every expected label present and checked, every extra field synthesized |
| C-If | Check the condition against Bool, check both branches against the expectation |
| C-Let | Synthesize the binding, check the body against the expectation |
| C-Sub | Everything else: synthesize `S`, require `S <: T` |

An unannotated lambda checked against Top is reported as insufficient information (Top names no domain). Checked against Bool, Nat, or a record type, it is reported as incompatible (a lambda can never have that type).

### Conditionals: synthesis vs. checking

Without an expected type, the Assignment08 policy applies: the branches must be mutual subtypes, so `if true then 0 else false` is rejected. With an expected type, each branch is checked separately, so `(if true then 0 else false) as Top` is accepted with type Top (see `examples/extra/if_checked_against_top.stlc`).

## Required limitations

This is contextual inference, not Hindley-Milner. There is no unification, no polymorphic let, no row inference, and no subtype-constraint solver. In particular:

- An unannotated lambda needs an expected function type: from an ascription, a function's parameter type, an expected record field, or an expected type flowing through `if` or `let`.
- An application never uses its argument to infer the function's parameter type.
- A let binding is synthesized, so `let id = lambda x. x in ...` is rejected. Let bindings are monomorphic.
- Top supplies no domain, so `(lambda x. x) as Top` is rejected.
- A missing parameter type is never filled in with Top, and runtime values are never used to guess static types.

## Error messages

Errors are classified as **insufficient type information** or **incompatible types** (plus unbound variables and duplicate labels). Every error shows a structural path from the root. Missing-information errors suggest a repair. Mismatch errors show the actual and expected types and why the subtype check failed.

```
Type error (insufficient type information)
  at: ascription to {} > extra field run (not in the expected interface)
  cannot synthesize a type for lambda x. x: parameter x has no annotation and no expected function type is available
  note: field run is not part of the expected record type, so it is synthesized with no expectation
  repair: annotate parameter x (lambda x:T. ...), or ascribe the lambda to a function type ((lambda x. ...) as (T -> U))

Type error (incompatible types)
  at: ascription to Bool -> Nat > lambda x body > operand of succ
  expected type Nat, but found Bool
  actual:   Bool
  expected: Nat
  why: Bool is not a subtype of Nat
```

## Type-trace format

`--trace-types` prints one line when each typing call starts and one when it returns. Nesting depth is shown with `| `.

```
synth CTX |- TERM   [RULE]          a synthesis call
check CTX |- TERM <= TYPE   [RULE]  a checking call
=> TYPE   [RULE]                    synthesis result
ok   [RULE]                         checking succeeded
failed                              the call reported an error
S <: T: holds | fails               a subsumption test
```

Lines without a leading verb are notes explaining a rule's decision (for example, where an omitted parameter type came from). Program A:

```
synth |- ((lambda x. succ x) as (Nat -> Nat)) 0   [T-App]
| synth |- (lambda x. succ x) as (Nat -> Nat)   [T-Ascribe]
| | check |- lambda x. succ x <= Nat -> Nat   [C-Abs]
| | | parameter x has no annotation: take x:Nat from the expected domain
| | | check x:Nat |- succ x <= Nat   [C-Sub]
| | | | synth x:Nat |- succ x   [T-Succ]
| | | | | check x:Nat |- x <= Nat   [C-Sub]
| | | | | | synth x:Nat |- x   [T-Var]
| | | | | | | => Nat   [T-Var]
| | | | | | Nat <: Nat: holds
| | | | | | ok   [C-Sub]
| | | | | => Nat   [T-Succ]
| | | | Nat <: Nat: holds
| | | | ok   [C-Sub]
| | | ok   [C-Abs]
| | => Nat -> Nat   [T-Ascribe]
| check |- 0 <= Nat   [C-Sub]
| | synth |- 0   [T-Zero]
| | | => Nat   [T-Zero]
| | Nat <: Nat: holds
| | ok   [C-Sub]
| => Nat   [T-App]
```

## Evaluation

Evaluation is call-by-value with closures and lexical scope. Annotated and unannotated lambdas build the same closure, ascriptions evaluate their operand unchanged, and record fields are evaluated left to right. A record keeps all its fields at run time even when its static type hides some (`examples/extra/service_runtime_record.stlc` prints `{run=<closure ...>, active=true}` at type `{run:Nat -> Nat}`). Natural numbers print in decimal.

## Tests

`dune runtest` runs 188 checks covering: the parser and printer (including round trips and duplicate labels), the unchanged subtype relation, synthesis and checking on hand-built ASTs, programs A-H (type and value), the ten required rejections (category, message, and no evaluation), Student/Person interfaces, missing and mistyped record fields, extra fields, shadowing and closure capture, the Assignment08 examples, and the program A trace.

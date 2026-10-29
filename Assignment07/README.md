# Assignment 07: Simply Typed Lambda Calculus with Derivations

An STLC type checker with Booleans, a derivation builder and printer, and a
separate evaluator, in OCaml.

## Build, test, run

```
dune build
dune runtest
dune exec ./bin/main.exe
```

`dune runtest` runs `test/test_stlc.ml` (plain OCaml, no extra libraries) and
fails with a nonzero exit status if any check fails. The full demo output is
saved in `example_output.txt`.

## Layout

```
lib/syntax.ml      ty, term, string_of_ty, string_of_term        (Part 1)
lib/context.ml     context, empty_context, extend, lookup         (Part 2)
lib/typecheck.ml   type_error, typeof, string_of_type_error       (Parts 3, 4)
lib/derivation.ml  derivation, derive, string_of_derivation       (Part 6)
lib/eval.ml        substitution, step, eval                       (Part 7)
bin/main.ml        demo: type and value side by side
test/test_stlc.ml  automated tests                                (Part 8)
```

## Where each typing rule lives

`typeof` (and `derive`, which has the same case structure) has exactly one
match case per rule. Each case is labeled with a comment naming its rule.

| Rule | Implemented in | What the code does |
|------|----------------|--------------------|
| T-True, T-False | `typeof`, `derive`: the `True` and `False` cases | return `TyBool`; `derive` builds `DTrue` / `DFalse` |
| T-Var | the `Var x` case | `lookup x ctx`; `None` becomes `UnboundVariable x` |
| T-Abs | the `Abs (x, t1, body)` case | check `body` in `extend x t1 ctx`, return `TyArrow (t1, t2)` |
| T-App | the `App (f, a)` case | check `f`, require `TyArrow (t1, t2)` (else `ExpectedFunction`), check `a` has type `t1` (else `ArgumentMismatch`), return `t2` |
| T-If | the `If (c, t2, t3)` case | require `c : Bool` (else `ExpectedBool`), require both branches to have the same type (else `BranchMismatch`) |

The premises of a rule are the recursive calls in its case, and the
conclusion is the value the case returns.

## Derivation design

`derivation` uses the constructors suggested in the assignment (`DTrue`,
`DFalse`, `DVar`, `DAbs`, `DApp`, `DIf`). Each node stores the context and
the type of its conclusion. The term of the conclusion is not stored; it is
rebuilt from the node and its premises by `term_of`, because the premises'
conclusions are exactly the subterms.

`string_of_derivation` prints a proof tree with premises side by side above a
bar labeled with the rule name, and the conclusion below the bar. For
`(lambda x:Bool. x) true`:

```
    ------------------ T-Var
    x:Bool |- x : Bool
--------------------------------- T-Abs    -------------- T-True
|- lambda x:Bool.x : Bool -> Bool          |- true : Bool
---------------------------------------------------------------- T-App
                |- (lambda x:Bool.x) true : Bool
```

When no derivation exists, `Derivation.report` says which rule is stuck, on
which subterm, in which context, and why. It points at the innermost failing
subterm rather than the whole term:

```
Type error: no derivation exists for the judgment
  |- true false : ?
Rule T-App cannot be applied to the subterm
  true false
in context: (empty)
Reason: expected a function type in function position, but found Bool
```

## Static versus dynamic

`Typecheck.typeof` and `Eval.eval` do not call each other. `main.ml` shows
both results for each example, and `eval (true false)` shows that evaluation
alone just gets stuck on a term the checker rejects.

`eval.ml` is a call-by-value, small-step evaluator with capture-avoiding
substitution. Type annotations on lambdas are carried along and ignored.
Evaluation stops after 10,000 steps so that ill-typed terms that loop cannot
hang the program.

## Tests

`test/test_stlc.ml` covers: Boolean identity; its application; the
higher-order function; an unbound variable; a Boolean applied as a function;
argument-type mismatch; branch-type mismatch; a non-Boolean condition;
lexical shadowing (in both the context and the checker); successful
derivation construction (rule at each node, contexts, printed output);
`derive` agreeing with `typeof` on every example; useful failure reports;
and the evaluator, including capture-avoiding substitution.

## Written answers

**1. What is the difference between a typing judgment and a typing
derivation?**
A judgment, such as `Γ ⊢ t : T`, is a claim that term `t` has type `T` under
context `Γ`. A derivation is a tree of rule applications that proves the
claim, with the judgment as its root and axioms such as T-True or T-Var at
the leaves. `typeof` answers the judgment; `derive` produces the tree.

**2. Why is a typing context necessary?**
A variable's type is not determined by the variable itself. It comes from the
binder that introduced it, which can be far from the use. T-Var needs the
context to find that type, and T-Abs needs it to check the body, which
mentions the parameter. Without a context, `x` inside `lambda x:Bool. x`
could not be typed.

**3. Why must both branches of `if` have the same type?**
The type of the whole expression must be one type `T`, and the checker does
not know which branch will run. If the branches had different types, the type
of the `if` would depend on the runtime value of the condition, and a
surrounding term such as `(if c then true else lambda x:Bool. x) true` could
not be given a type that is correct for both outcomes.

**4. Why must T-App require an arrow type in function position?**
The arrow type tells the checker what argument type to demand and what result
type to produce. If `t1` is not an arrow type, it cannot evaluate to a
function, so the application has no evaluation rule and would get stuck.
`true false` is an example: `eval` cannot reduce it.

**5. How does a typing context differ from the runtime environment used by a
closure-based evaluator?**
Both map names to something and both handle shadowing by taking the nearest
binding. The context maps names to types and exists before the program runs;
it is extended once per binder while walking the syntax and no argument value
is involved. A runtime environment maps names to values, is captured inside
closures when a lambda is evaluated, and depends on the actual arguments of
each call. The checker looks at a lambda body once, while the evaluator
enters it on every call.

**6. Why does the recursive structure of a type checker resemble a proof
tree?**
The rules are syntax-directed: each form of term has exactly one rule. So
each recursive call on a subterm is one premise, and the value a case returns
is its conclusion. The tree of recursive calls therefore has the same shape
as the derivation, and `derive` records that tree instead of discarding it.

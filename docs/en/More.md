# More: extending a typed language coherently {#more}

## Motivation {#motivation}

Adding a syntax constructor is only the beginning of extending a language.
Its typing rule, binder structure, value status, evaluation order, substitution
behavior, and progress case must agree. A product constructor without a rule
for evaluating its second component, for example, can leave a closed
well-typed program stuck.

This chapter extends the intrinsically typed calculus with primitive numbers
and multiplication, `let`, products, sums, unit, the empty type, and lists.
The upstream executable core focuses on primitives, let, and products; its
explanatory sections and exercises introduce the remaining constructs. Here
all of them receive renaming, substitution, call-by-value reduction, and
closed-progress implementations in one language.

## Model {#model}

### Introduction, elimination, and binding {#constructs}

`NatT` is the unary object-language natural type with zero, successor, and
case. `PrimT` is a separate primitive-number type whose literal stores a host
`Nat`; `Times` computes multiplication directly. Keeping the two distinct
makes the difference between an inductive encoding and a primitive operation
visible.

{{include:src/PLFA/Part2/More.idr#syntax}}

Read the additional constructors in introduction/elimination pairs:

| Type or construct | Introductions | Eliminations | Additional binders |
| --- | --- | --- | --- |
| Functions | `MLam` | `MApp` | one in the lambda body |
| `let` | bound expression plus body | substitution when the expression is a value | one in its body |
| Products | `Pair` | `Fst`, `Snd`, `Split` | two in the `Split` body |
| Sums | `InL`, `InR` | `SumCase` | one in each branch |
| Unit | `Unit` | `UnitCase` | none |
| Empty | none | `Absurd` | none |
| Lists | `Nil`, `Cons` | `ListCase` | head and tail in the cons branch |

A sum injection determines its chosen component, but its other component type
comes from the intrinsic expected type. Both `SumCase` branches return the
same result type. A list has one element type, and its tail has that same list
type. `Absurd` can have any result type when its argument has type `EmptyT`; it
does not require a value proof. Execution first evaluates that argument. There
is no rule for eliminating an empty-type value, because no such value exists.

### One binder, two binders {#substitution}

All constructors participate in structural operations. The interesting new
cases are `Split` and the cons branch of `ListCase`: their maps are extended
twice. Ordinary pair components do not bind anything.

{{include:src/PLFA/Part2/More.idr#structural}}

The context order is exact. Splitting a pair of types a and b gives the body
context b :: a :: Γ: zero selects the second component, one selects the first.
For a list cons branch the order is ListT a :: a :: Γ: zero selects the tail,
one the head. `double first second` implements this convention explicitly;
`inst2` performs both replacements simultaneously.

This is not an unexplained composition of two single substitutions. Removing
one binder changes all remaining indices, and a replacement may itself be an
open term. A simultaneous map states the intended meaning of every variable
before traversal, with weakening handled uniformly under any further binder.
The checked exercises below distinguish the two positions.

### Values and evaluation order {#dynamics}

Lambdas, unary numerals, primitive literals, and unit are values. Pairs,
injections, and cons cells are values only when their contained terms are
values. Lists therefore evaluate their heads and tails; they are not lazy
streams. There is no value constructor at `EmptyT`.

{{include:src/PLFA/Part2/More.idr#dynamics}}

Every binary strict constructor evaluates left to right. A projection waits
for **both** fields of its pair to be values, even if it will discard one.
`SumCase` first evaluates its scrutinee, including the selected injection's
payload, then substitutes into only the selected branch. `ListCase` first
obtains a fully evaluated list value and then replaces head and tail in its
cons branch. Branch bodies themselves are not evaluated before selection.

Projection and pair-pattern matching express the same choice of fields in
different forms. A first projection can be expressed by `Split` with a body
selecting index one; a second projection selects index zero. Conversely,
one can save the pair in a let binding and obtain its fields by projections.
Saving it first retains the intended single evaluation of the scrutinee. These
are explanatory translations here; a general equivalence theorem between both
product formulations is not claimed. The checked `swapPair` and `splitOrder`
examples exercise the two-binder formulation directly.

`Let` evaluates its binding once before substitution. Its body is not reduced
while the bound expression is still running. In the next chapter we prove
that replacing let by an application of a lambda respects these precise
rules.

## Worked examples {#examples}

`cube` first computes the square of its argument in a let binding. In the
body, the square is at index zero and the original argument at index one.
For input two, the checked trace performs four steps: beta application,
primitive multiplication inside the let, let substitution, and final
primitive multiplication. The result is literal eight.

{{include:src/PLFA/Part2/More.idr#examples}}

`swapPair` uses the two-binder eliminator to reverse a pair. `lengthList` is a
recursive function from lists to unary naturals. Its cons branch sees tail,
head, original list, and recursive function, in that order. It ignores the
head and calls the recursive function on the tail; the zero branch returns
zero and the cons branch adds one.

The primitive and unary result readers deliberately have different types.
These computations check both cube and the length of a two-element list.

{{include:src/PLFA/Part2/More.idr#computations}}

## Theorems for the extended language {#theorems}

### Closed progress {#progress}

`progress` handles every constructor. Its small helpers express the relevant
canonical forms: a primitive value must be a literal, a product value a pair,
a sum value a tagged value, and a list value either nil or a cons of values.
For `Absurd`, a progressing argument supplies a contextual step, while a
value argument is ruled out by `emptyValue`.

{{include:src/PLFA/Part2/More.idr#progress}}

All steps preserve the indexed type and context by construction; constructing
`SplitBeta` and `ListCons` relies on the typed `inst2` implementation.
Closedness is still essential to progress, because an open variable is neither
a value nor a redex in these rules.

### Values cannot step {#normality}

`valueNormal` covers the extended value grammar. In a pair or cons cell, a
contextual step would require one of the already-valued components to step;
recurse on that component's value proof. Injection and successor cases have
the same shape. Literals, unit, nil, and lambdas have no applicable rules.

{{include:src/PLFA/Part2/More.idr#value-normal}}

An empty type has no **values**, but general recursion permits closed terms at
that type. The following term unfolds to itself. This does not contradict
`emptyValue`: it never becomes a value. Confusing “no value” with “no term”
would incorrectly turn a programming language with general recursion into a
normalizing logic.

{{include:src/PLFA/Part2/More.idr#empty-loop}}

### Evidence-producing evaluation {#evaluation}

The fuelled evaluator uses progress to construct a trace. `Returned` includes
its value proof, while `OutOfFuel` makes no termination claim. Its fuel recursion
is total even when the represented program, such as `emptyLoop`, runs forever.

{{include:src/PLFA/Part2/More.idr#evaluation}}

## Pitfalls {#pitfalls}

- Primitive multiplication consumes `PrimT`, not unary `NatT`. These are two
  different object-language types.
- A pair containing an unevaluated expression is not a value. Projection
  therefore cannot silently skip evaluation of the discarded field.
- `Split` and a list cons branch each bind two variables, in a stated order.
  Their maps must be extended twice.
- A sum case evaluates only the chosen branch, but the payload must first be
  a value. This is call by value, not a name-based substitution rule.
- `EmptyT` has no values. General recursion prevents the stronger conclusion
  that it has no closed terms.
- Adding a constructor to `Term` without extending all structural and
  operational functions leaves an incomplete language definition; totality
  checking helps expose the missing cases.

## Exercises and checked solutions {#exercises}

1. **Product binder order.** Split the pair of literals three and five and
   multiply its first component by its second. Show the exact substituted
   target before the multiplication step.
2. **Sum selection.** Analyze a left injection of seven, double its payload,
   and give a constant right branch. Prove the selected one-step target.
3. **List binders.** Analyze a singleton list containing nine and return its
   head. Explain why the branch uses the older of its two variables.

{{include:src/PLFA/Part2/More.idr#solutions}}

The proofs `splitOrder`, `sumChoice`, and `listHead` instantiate general
reduction constructors with concrete value evidence. They check the binder
conventions against observable targets, rather than merely checking that the
terms can be written.

## References and adaptation {#references}

Based on [PLFA, More](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/More.lagda.md)
by Philip Wadler, Wen Kokke, and Jeremy G. Siek, frozen at
`1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The formal language includes the upstream core and the narrative's sum, unit,
empty, and list constructs. `inst2` explicitly implements simultaneous
substitution; we do not claim a general equation equating it with every
possible sequential-substitution formulation. The functions, progress proof,
value-normality proof, evaluation traces, and exercises are checked with
Idris2 0.8.0.

# Compositional: meaning from the meanings of parts {#compositional}

## Motivation {#motivation}

Suppose we replace one expression by another with the same denotation. Can the
surrounding program detect the change? A useful denotational semantics should
answer no: the meaning of a compound expression should depend only on the
meanings of its immediate parts. This property is called compositionality.

It is not enough to point at the lambda and application rules in
[Denotational](Denotational.html#judgment). A proof about a lambda can end with
`DJoin` or `DSub`, rather than `DLam`. A proof about an application can also
end with `DBot`. We must account for all those derivations before we can safely
reason from the outer syntax alone.

This chapter proves equations for variables, lambda abstractions, and
applications. It then uses those equations to prove congruence, replacement
inside arbitrary scope-correct one-hole contexts, and equivalence with a
structurally recursive presentation of the semantics.

## Model {#model}

We retain `Tm n`, finite information values, the full `Info` preorder, and the
inductive judgment `Denote g m v` from the preceding chapter. In particular,
no evaluator, step bound, or finite list of tested terms enters the definition.
`DenEq d e` is pointwise equivalence of predicates for **all** environments and
values; `SemEq m k` applies that equivalence to the meanings of terms.

There are two semantic operators to construct. `FunDen` takes the meaning of
a body with one additional variable and produces the meaning of a function.
`AppDen` takes the meanings of a function and an argument and produces the
meaning of their application. Neither operator examines source syntax.

### The lambda equation {#lambda-equation}

`FunDen d g v` follows the shape of the observation `v`:

- At `Bottom`, the proposition is the unit type: no information is required.
- At `Arrow a b`, the proposition is `d (extendEnv g a) b`: the body must
  provide `b` when the parameter supplies `a`.
- At `Join a b`, both component propositions must hold.

To handle a final `DSub`, we prove `funDown`: if an observation belongs to
`FunDen (meaning body)` then every smaller observation belongs too. This is
induction on the **information-order derivation**, not on the term.
In the arrow case, `upEnv` increases the body's parameter information and
`DSub` decreases its output information. In the distribution case, the two
body derivations combine with `DJoin`. The transitivity case applies the
induction hypotheses in reverse order, first to the larger bound.

The forward equation, `lambdaForward`, now follows by induction on a
denotation derivation. The reverse equation, `lambdaBackward`, follows by
recursion on the observed value. Together they establish `lamEquation`.
Specializing the forward equation to an arrow gives `lambdaInversion`, even
when the original derivation finishes with joins or subsumption.

{{include:src/PLFA/Part3/Compositional.idr#lambda-equation}}

### The application and variable equations {#application-equation}

An application has observation `w` if either `w` is below `Bottom`, or there
exists some finite input `a` such that the function has observation `Arrow a w`
and the argument has observation `a`. This is the definition of `AppDen`.

The bottom alternative cannot be dropped. Every application, including a
diverging one, has observation `Bottom`; we have not established that its
function part supplies an arrow. The existential input is also essential:
different uses of the same expression can require different finite observations.

`applicationInversion` is the forward direction. Its difficult case is
`DJoin p q`. The two induction hypotheses each return a bottom alternative or
an actual function row, giving four cases:

| First observation | Second observation | Construction for their join |
| --- | --- | --- |
| Below bottom | Below bottom | Combine the order proofs with `IJoinL`. |
| Below bottom | Function row | Keep that input and add the empty output information using `IFun`. |
| Function row | Below bottom | Symmetric to the preceding case. |
| Function row | Function row | Join both input demands and both function observations; use `mixedDist`. |

The final case explains why arrow distribution belongs to the model. Without
it, a join of two function rows does not immediately give a single row whose
output is the joined result. In the `DSub` case, an actual row keeps its input
while its output is lowered by `IFun`.

`applicationBackward` handles the bottom alternative with `DSub DBot`, and
the other alternative with `DApp`. For variables, `varInv` handles all possible
last rules and proves that an observation is below the environment's assignment.
These constructions give `appEquation` and `varEquation` in both directions.

{{include:src/PLFA/Part3/Compositional.idr#application-equation}}

## Worked examples {#examples}

Consider two derivations of the same application. One uses input observation
`a` and returns `b`; the other uses input `c` and returns `d`. The argument
therefore has observation `Join a c`. The function has observation
`Join (Arrow a b) (Arrow c d)`. `mixedDist` lowers that function observation
to `Arrow (Join a c) (Join b d)`, so one `DApp` can produce the combined
result. This construction is uniform in all four values and does not select
a bounded set of tables.

For a lambda example, suppose its observed row was obtained by first deriving
`Arrow a' b'`, then proving `Info (Arrow a b) (Arrow a' b')`. The order demands
`Info a' a` and `Info b b'`. To recover the body's observation at input `a`,
increase the old input information from `a'` to `a`, then discard output
information from `b'` to `b`. This is precisely the arrow case of `funDown`.

For an example of replacement under binding, let `l` and `r` be terms in scope
`S n`, and suppose `SemEq l r`. The context λ. ([hole] 0) turns them into
`Lam (App l (Var FZ))` and `Lam (App r (Var FZ))`. The hole may refer to the
newly bound variable, so equality only in an empty environment would not be
enough. Pointwise equality in every environment gives exactly what we need.
Exercise 2 supplies the checked proof of this example.

## Theorems and proof ideas {#theorems}

### Semantic equality is a congruence {#congruence}

`funMap` transports evidence through `FunDen`, recursively on the observation.
It needs just the forward implication between its input denotations. Applying
it once in each direction proves `funCong`.

`appMap` transports evidence through `AppDen`. It leaves the bottom alternative
alone. For an actual row, it keeps the same existential input and transports
the function evidence and argument evidence separately. Two uses give
`appDenCong`.

The term-level congruence theorems then follow by composing equivalences:
use the syntax equation, transport through the corresponding semantic operator,
and use the other syntax equation backwards. Thus `lamCong` has no hidden
assumption about lambda inversion, and `appCong` covers both operands.

{{include:src/PLFA/Part3/Compositional.idr#congruence}}

### One-hole contexts {#contexts}

`Ctx m n` describes a term with one hole: the hole accepts a term in scope
`m`, and filling it yields a term in scope `n`. `Hole` leaves a term alone.
`CLam` puts a binder around the context, reducing the resulting outer scope
by one. `CAppLeft` and `CAppRight` place the hole in either operand of an
application, keeping the other operand as an ordinary term.

The hole's scope is part of the type. In a context that binds a variable
occurring in the hole, that variable is already counted in `m`; it is not
silently invented or renamed by `plug`. A closed term can be explicitly
weakened when it is to be viewed in a larger hole scope. This is the scoped
context convention used by the theorem, not a claim about unscoped textual
search-and-replace.

`plug` recurses on the context. `compositionality` follows the very same
recursion: use `lamCong` for a binder; use `appCong` and reflexivity for the
unchanged operand of an application. Its exact statement quantifies over
all `m`, `n`, `l`, `r`, and `c : Ctx m n`. It is not restricted to closed
terms, empty contexts, or a list of example contexts.

{{include:src/PLFA/Part3/Compositional.idr#contexts}}

When `n` is zero, the context closes the inserted terms. The later
[ContextualEquivalence](ContextualEquivalence.html#theorems) chapter combines
this theorem with soundness and adequacy to show that denotationally equal
terms have the same termination observation in each such closing context.
Compositionality itself asserts equality of denotations, not yet the
operational observation theorem.

### A structurally recursive presentation {#structural}

The three semantic equations suggest the function `structural`: variables use
the information preorder, lambdas use `FunDen`, and applications use `AppDen`.
`structuralCorrect` proves pointwise equivalence with the inductive relation,
by induction on the term and the operator congruence theorems.

This function returns a **predicate**, not a yes/no answer deciding the
predicate. In the application case that predicate still contains an existential
quantifier over arbitrary finite information values. A total function from
syntax to predicates does not decide termination, and total checking of proof
transformers does not imply that every untyped program terminates.

{{include:src/PLFA/Part3/Compositional.idr#structural}}

## Common pitfalls {#pitfalls}

- Matching only `DLam` or `DApp` omits bottom, join, and subsumption derivations.
- A join of application results may require a join of argument demands.
  One guessed input is not sufficient for every observation.
- `FunDen` is defined for arbitrary predicates, but `funDown` uses the specific
  closure properties of `meaning body`. It does not claim that every predicate
  is downward closed.
- Congruence under a binder requires equality in every relevant environment.
- `structural` computes a proposition describing meaning; it is not a total
  evaluator for the untyped lambda calculus.
- This chapter does not prove the converse of contextual equivalence, nor
  does it identify syntactically distinct terms by propositional equality.

## Exercises and checked solutions {#exercises}

### Exercise 1: combine outputs {#exercise-1}

Suppose the same term has observations `Arrow a b` and `Arrow a c`. Derive
observation `Arrow a (Join b c)` for it. Explain why simply using `DJoin`
does not yet reach the requested observation.

**Checked solution:** `joinFunctionOutputs` first constructs
`Join (Arrow a b) (Arrow a c)` with `DJoin`, then uses `DSub` and `IDist`.
The information-order rule points from the requested single row to the
available joined rows, which is exactly the orientation needed by `DSub`.

### Exercise 2: replace beneath a binder {#exercise-2}

From `SemEq l r`, where both terms have scope `S n`, prove semantic equality
of λ. (l 0) and λ. (r 0). Build the context explicitly, and explain why the
hole's input scope differs from the final term's scope.

**Checked solution:** `replaceUnderBinder` uses
`CLam (CAppLeft Hole (Var FZ))`. The hole and the inner application have scope
`S n`; `CLam` binds index zero and produces scope `n`. The entire equality
follows from `compositionality`. `identityContextExample` additionally checks
the definitional behavior of a simple closed application context; it is an
example of plugging, not a substitute for the general theorem.

{{include:src/PLFA/Part3/Compositional.idr#exercises}}

## References and adaptation notes {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
[PLFA, Compositional](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part3/Compositional.lagda.md),
frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0.
This independent Idris2 adaptation retains the semantic operators, both
directions of their equations, binder-sensitive contexts, and the relational
versus structural equivalence theorem. `CLam` is stated with a general hole
index; the resulting scope is still checked by its argument type.

The proof uses explicit functions composing pointwise equivalences in place
of the upstream custom equational-reasoning syntax. All displayed code is
included from the module checked by Idris2 0.8.0 under `%default total`.
The two additional exercises provide checked applications of distribution
and replacement under a binder.

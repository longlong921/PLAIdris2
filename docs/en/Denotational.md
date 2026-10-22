# Denotational: finite information about untyped functions {#denotational}

## Motivation {#motivation}

A reduction sequence explains how a program runs. A denotation instead describes
what information the program supplies. The two views should agree, but they need
not use the same objects. We shall describe an untyped function by finite pieces
of its input/output table.

Why finite pieces? A complete table can have infinitely many rows. Even the
identity function accepts every possible argument. A finite observation needs
only finitely many rows, so we represent each observation by an inductive value
and represent the whole function by the collection of its observations.

Self application introduces a second problem: an exact table for a function
cannot literally contain itself as an input. We therefore allow an input to
supply **at least** the information demanded by a row. A row may mention a
smaller description of the function that owns it. This is how finite trees can
describe the behavior of an untyped language containing self application.

This chapter uses the complete scoped syntax from [Untyped](Untyped.html#model).
There is no bound on program size, reduction length, or the depth of a semantic
value. The proofs do not run a finite evaluator. They manipulate finite proofs
that a particular observation is justified.

## Model {#model}

### Information values and their order {#information}

`Value` has three constructors. `Bottom` contains no information. `Arrow a b`
describes a function that can produce observation `b` when its argument supplies
observation `a`. `Join a b` combines both observations. A value is a finite tree;
it is not a runtime closure and it does not carry a lambda body.

Write `Info a b` as “a contains no more information than b”, or a ⊑ b. Its first
five constructors express bottom, the least-upper-bound behavior of join, and
transitivity. Reflexivity is proved recursively over values, rather than added
as another rule.

The direction of `IFun` deserves attention. To show
`Info (Arrow a b) (Arrow a' b')`, we need `Info a' a` and `Info b b'`.
A function that accepts **less** input information and supplies **more** output
information is more informative. Inputs are contravariant; outputs are
covariant. This concerns descriptions of behavior, not the order of evaluation.

`IDist` says that two rows with the same input can jointly supply the join of
their outputs. The derived `mixedDist` first joins possibly different input
requirements, then combines the outputs. This rule will be essential in the
application equation in [Compositional](Compositional.html#application-equation).

{{include:src/PLFA/Part3/Denotational.idr#information}}

For example, `joinCommute` derives `Info (Join a b) (Join b a)`: select `a` from
the right branch of the target, select `b` from its left branch, then combine
the two derivations with `IJoinL`. Neither this fact nor the reverse direction
asserts that the two syntax trees are propositionally equal. The information
relation is a preorder, and multiple trees can represent equivalent information.

### Environments {#environments}

An environment `Env n` maps the `n` available variables, represented by `Fin n`,
to finite information values. Extending an environment assigns the new value
to `FZ` and retains the old assignment at `FS x`. The newest variable is thus
at index zero, exactly as in substitution.

`EnvLE g d` compares environments pointwise: every variable receives at least
as much information in `d` as in `g`. `joinEnv` also works pointwise. Its two
projection lemmas let us combine independently obtained information about free
variables.

The equation `envEta g x` recovers an environment from its head and tail **at
each index**. We deliberately state the equation pointwise. No assumption of
function extensionality is needed anywhere in these chapters.

{{include:src/PLFA/Part3/Denotational.idr#environments}}

### The denotation judgment {#judgment}

`Denote g m v` means that `v` is a justified finite observation of term `m` in
environment `g`. Read its rules as a small proof language:

1. `DVar` retrieves the observation assigned to a variable.
2. `DLam` constructs one table row. To observe `Arrow a b`, give the parameter
   information `a` and establish observation `b` of the body.
3. `DApp` selects a row from the function and supplies the row's input from the
   argument.
4. `DBot` observes nothing, and is valid for every term.
5. `DJoin` combines two observations of the same term.
6. `DSub` forgets some information according to `Info`.

`DApp` asks for an exact shared intermediate value, but this does not force an
exact table lookup. `applyLarger` uses `DSub` to discard excess information in
the argument first.

{{include:src/PLFA/Part3/Denotational.idr#judgment}}

The presence of `DBot` is especially important for call by name. A function may
ignore an argument that diverges. Such an argument still supplies `Bottom`, so
it can meet an unused parameter's requirement. A derivation of `Bottom` does
not certify either termination or divergence.

### Equality of denotations {#equality}

A `Denotation n` is a relation from environments and observations to types of
evidence. `meaning` just puts the term argument first. `DenEq d e` gives, for
every environment and every value, a function in each direction between the
two evidence types. `SemEq m k` is this equality applied to two terms.

This equality compares the sets of valid observations, not derivation trees.
The proofs `denEqRefl`, `denEqSym`, and `denEqTrans` establish an equivalence
relation. They are pointwise constructions and do not equate functions by an
extensionality axiom.

{{include:src/PLFA/Part3/Denotational.idr#equality}}

## Worked examples {#examples}

The identity function has observation `Arrow a a` for every finite `a`.
Inside the lambda, `DVar` supplies precisely the parameter's information;
`DLam` turns that derivation into a row. `identityTable` joins two such rows.
`identitySelf` then uses one identity observation as the input to another.

For Δ = λx. x x, supply `Join (Arrow a b) a`. The first occurrence of `x`
selects `Arrow a b`, the second selects `a`, and application produces `b`.
The two occurrences share an environment but use different parts of its
information. This is a concrete solution to the self-application difficulty.

The term Ω = Δ Δ also has a finite derivation of `Bottom`. `omegaBottom`
shows the actual table matching: one occurrence of Δ supplies a row whose
input is `Join (Arrow Bottom Bottom) Bottom`; the other supplies precisely
that join. The simpler proof `DBot` would suffice too. Neither proof alone
says that Ω has no more informative observations.

Finally, Church two requires two rows, `Arrow a b` and `Arrow b c`, from its
function parameter. The first application moves from `a` to `b`; the second
moves from `b` to `c`. Notice that the values need not be numerals.

{{include:src/PLFA/Part3/Denotational.idr#examples}}

## Theorems and proof ideas {#theorems}

### More information preserves observations {#monotonicity}

`envMono` proves that `Denote g m v` and `EnvLE g d` imply `Denote d m v`.
The variable case starts from `DVar` in the new environment and forgets excess
information with `DSub`. The lambda case extends both environments by the
same input value. The remaining cases rebuild the original proof constructors.
`upEnv` specializes this theorem to increasing only the newest assignment.

The more general `renamePres` also changes variable indices. Its premise says
that `g x` is below `d (rho x)` for every old variable. The lambda case uses
`liftRen rho`, fixing the freshly bound variable and shifting all older ones.
This is a semantic renaming theorem for arbitrary terms and arbitrary finite
observations.

{{include:src/PLFA/Part3/Denotational.idr#renaming}}

### Extracting function rows {#membership}

Suppose an arrow lies below a complicated join. It is unsafe to assume that
one row in that join already provides the whole output: `IDist` can combine
several rows. We must extract a **collection** of rows.

`Member` records a leaf in a value's join tree; `Included` maps each such
membership proof to a membership proof in another tree. Here `Bottom` counts
as a leaf, even though its information content is empty. `AllFuns` says every
leaf is an arrow and consequently ensures that there is at least one arrow.
These representational facts make the inversion proof precise.

`joinDomain` joins the inputs of all rows; `joinCodomain` joins the outputs.
`memberInfo` and `includedInfo` show that literal membership and inclusion imply
information ordering. The converse is false: variance and distribution can
establish ordering without literal membership.

{{include:src/PLFA/Part3/Denotational.idr#membership}}

### Function inversion {#factorization}

`Factor whole selected a b` packages **proved evidence** that `selected`
contains only function rows, is included in `whole`, demands at most `a`, and
jointly supplies at least `b`. Its fields are the conclusion constructed by
the proof below, not assumptions supplied to bypass that proof.

`subInv` proves a strengthened statement: if `Info u v` and `Arrow a b` occurs
in `u`, then some collection of rows in `v` factors the arrow. The strengthening
is necessary for the transitivity case. First extract rows in the intermediate
value. Then `factorAcross` recursively replaces each extracted row by rows
from the final value. `mergeFactors` joins the resulting collections; transitivity
composes the domain and codomain bounds. In the `IDist` case, both rows are
selected. Their joined domain is below their repeated input by idempotence.

The corollary `arrowInversion` has the exact scope
`Info (Arrow a b) (Arrow c d)` implies both `Info c a` and `Info b d`.
It holds for **every derivation** of the order, including derivations that pass
through joins and use transitivity. It is not just a pattern match on `IFun`.
`arrowNotBottom` likewise shows that even `Arrow Bottom Bottom` is strictly
more informative than `Bottom`.

{{include:src/PLFA/Part3/Denotational.idr#factorization}}

## Common pitfalls {#pitfalls}

- `Bottom` is absence of information, not a special runtime result. Every term
  has that observation, including terminating lambda abstractions.
- A lambda has finite observations of arbitrarily large size. Its denotation
  is not restricted to a single finite table selected in advance.
- Arrow inputs are contravariant. Reversing that premise changes the model.
- `Join` describes combined information, not nondeterministic execution.
- Syntactic equality of `Value` trees is stronger than equivalence under `Info`.
- Semantic equality alone is not yet an operational theorem. [Soundness](Soundness.html#theorems),
  [Adequacy](Adequacy.html#theorems), and [ContextualEquivalence](ContextualEquivalence.html#theorems)
  establish the connection to reduction and observable termination.

## Exercises and checked solutions {#exercises}

### Exercise 1: join laws {#exercise-1}

Derive `Info (Join a b) (Join b a)` and `Info (Join a a) a` for arbitrary
values. Use the order constructors, without comparing or simplifying trees.

**Checked solution:** `joinCommute` selects the opposite target branch in each
premise of `IJoinL`; `joinIdempotent` combines two reflexivity proofs. Both
definitions are included in [Information values](#information). Applying
`joinCommute` again gives the reverse ordering, not a proof that the trees are
equal.

### Exercise 2: Church addition {#exercise-2}

Give a non-bottom observation of λm. λn. λf. λx. m f (n f x). Assume the
first numeral, when supplied observation `f`, maps `b` to `c`, and the second
maps `a` to `b`. Determine the resulting row for their sum.

**Checked solution:** `churchPlusMeaning` describes the sum as mapping the same
`f` from `a` to `c`. Four `DLam` constructors bind the parameters; the inner
derivation supplies `f` to both numerals, applies the second to `x`, and passes
its observation to the first. This is a general path-composition property,
not a computation of a single numeral.

{{include:src/PLFA/Part3/Denotational.idr#addition}}

### Exercise 3: arbitrary Church numerals as paths {#exercise-3}

For a path of `k` edges, store its `k + 1` vertices in reverse order in a
vector. Build the join of its edges, then prove that Church `k` maps the
path's starting vertex to its ending vertex. Include the zero-edge case.

**Checked solution:** `pathTable` constructs the edges and `pathStart` selects
the vector's last vertex. `iterateMeaning` is induction on the path length.
For zero edges, the body is a variable. For another edge, select the new row
and apply it to the induction hypothesis. `pathEnvGrow` and `envMono` allow
the old proof to use the enlarged table. Two lambda introductions finish
`churchMeaning`, for every natural `k` and every vector of `k + 1` values.

{{include:src/PLFA/Part3/Denotational.idr#church-paths}}

## References and adaptation notes {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
[PLFA, Denotational](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part3/Denotational.lagda.md),
frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0.
This is an independent Idris2 adaptation. The model is PLFA's finite-information
filter model; “table” is an explanatory reading of its values, not a replacement
by an executable finite map.

Scopes use `Nat` and `Fin`; environment equations are pointwise. Membership and
“all rows are functions” are inductive evidence types instead of the upstream
function-valued predicates. Their role and the factorization theorem are
preserved. Both upstream exercises, addition and general Church paths, have
checked reference solutions here. All included definitions are checked in
Idris2 0.8.0 with `%default total`; no axiom or unchecked cast is used.

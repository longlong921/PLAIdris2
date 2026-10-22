# DeBruijn: making ill-typed terms unrepresentable {#debruijn}

## Motivation {#motivation}

In [Properties](Properties.html), a raw program and its typing derivation were
separate objects. Preservation had to rebuild the derivation after every step.
We can instead make the context and type indices of the program datatype.
Application then accepts only a function and an argument with matching types;
a reduction's source and target must have the same indexed type.

This is an **intrinsically typed** representation. It does not turn every
semantic theorem into reflexivity. Substitution must still traverse every
binder correctly, progress must still find the next step, and an evaluator
must still account for divergence. What changes is where type preservation is
checked: it becomes part of constructing the syntax operations and reduction
rules themselves.

The earlier chapters already introduced de Bruijn positions. Here those
positions gain type evidence. We keep the same types, context vectors,
call-by-value order, natural-number cases, and general recursion, so that the
two representations can be compared directly.

## Model {#model}

### Typed references and typed terms {#intrinsic}

`Ref gamma a` is a reference to a variable of type `a` in `gamma`. Its
constructor `At i` has type `Ref gamma (index i gamma)`: the type is determined
by the context at the chosen position. `vz` selects the newest variable, and
`vs` weakens an existing reference beneath a new binder. These are derived
functions over `Fin`, rather than a second independently numbered datatype.

`Term gamma a` contains only terms with the indicated context and type. Read
`App` from its premises: a term of type `Arr a b`, followed by a term of type
`a`, yields a term of type `b`. There is no way to supply `Zero` in the function
position because `TNat` cannot unify with an arrow.

{{include:src/PLFA/Part2/DeBruijn.idr#intrinsic}}

The `0` annotations on the datatype indices are Idris multiplicities: context
and type information is available to the checker but need not be retained at
runtime. The reference position and term constructors remain computational
data. Erasure does not authorize returning a result with the wrong index.

This representation also makes a distinction easy to overlook: two typings
of the external identity correspond to two differently indexed intrinsic
terms. We are not proving that the unannotated raw identity has one unique
type.

### Renaming as a typed map {#renaming}

A `TRen gamma delta` works at every variable type. It cannot change a variable
of type `a` into one of type `b`. `extendRen` fixes the new reference and
weakens the images of older ones. `renameTerm` then acts structurally on every
term constructor.

{{include:src/PLFA/Part2/DeBruijn.idr#renaming}}

For a lambda, both contexts acquire the same argument type. The natural case
branch acquires `TNat`; a fixpoint body acquires its result type. Renaming can
weaken, permute, or identify variables when the type-indexed map permits it;
it is not limited to incrementing all numeric positions.

### Substitution beneath binders {#substitution}

A `TSub gamma delta` maps each variable to a term of exactly its type.
`extendSub` sends the new reference to itself and weakens every older
replacement. Its use of `renameTerm vs` is the crucial capture-avoidance step.

{{include:src/PLFA/Part2/DeBruijn.idr#substitution}}

The signature of `substTerm` is already the general typed substitution
statement: an arbitrary type-respecting map between contexts transforms a
term while retaining its result type. The implementation supplies all its
cases. `instantiateTerm` is its one-variable specialization and is used by
both beta reduction and fixpoint unfolding. No value restriction belongs in
this structural operation.

## Worked examples {#examples}

The recursive addition program has the same binder layout as its raw
counterpart. In its successor branch, `vs (vs (vs vz))` selects the recursive
function. Multiplication reuses addition. `churchTwo` has the polymorphic
family of simple types `(a → a) → a → a`; this is an Idris family of typed
terms, not an extra polymorphic type constructor in the object language.

{{include:src/PLFA/Part2/DeBruijn.idr#examples}}

A useful way to read `multiplication` is from the inside outward. The recursive
call consumes the predecessor and the unchanged second argument. Addition
combines that result with the second argument. The case branches therefore
both return `TNat`, the two lambdas build a curried function, and `Fix` ties
the recursive reference to that same function type.

## What the indices prove, and what we still prove {#theorems}

### Progress and reduction {#dynamics}

`Step` relates terms with the same context and type. Each beta rule can be
constructed because `instantiateTerm` has the appropriate type-preserving
signature. This is intrinsic preservation for every context; it is not an
additional external typing theorem with a missing proof.

Closed progress is still a recursive proof. Values at arrow type can only be
lambdas, and values at natural type are zero or successors. The helpers inspect
these canonical shapes. An empty context excludes references, but an open
well-typed variable would have neither a value rule nor a reduction rule, so
the closedness hypothesis cannot be removed.

{{include:src/PLFA/Part2/DeBruijn.idr#dynamics}}

`Run` packages the actual endpoint, a finite reduction trace, and either a
value certificate or an exhaustion marker. `run` consumes fuel and uses
`progress` at each inspection. It does not call an unchecked general recursive
host evaluator. As before, zero fuel gives exhaustion even if the initial
program is a value.

### Relating external and intrinsic representations {#correspondence}

`elaborate` turns an existing external derivation into an intrinsic term. The
variable case wraps its position with `indexRef`; other cases replace each
typing constructor with the corresponding term constructor. This function is
not type inference: its caller must already possess the derivation.

{{include:src/PLFA/Part2/DeBruijn.idr#correspondence}}

In the opposite direction, `forget` removes the intrinsic type indices and
keeps the raw syntax. The theorem `forgetElaborate` says that elaborating any
typing derivation and then forgetting yields precisely the original raw term.
The proof recurses over the derivation, rewriting each immediate subterm by
its induction hypothesis. It does not merely compare two handpicked examples.

{{include:src/PLFA/Part2/DeBruijn.idr#erasure}}

[Inference](Inference.html#soundness) will supply these external derivations
algorithmically and reuse this correspondence to produce executable intrinsic
terms.

### Checked computations {#computations}

`naturalValue` reads the number represented by a natural-value proof.
`runNatural` uses it only when execution returns `Returned`; exhaustion remains
`Nothing`. The reference calculations check `2 + 2` and `3 × 2` by reducing
the programs and their proof-producing evaluator.

{{include:src/PLFA/Part2/DeBruijn.idr#computations}}

## Pitfalls {#pitfalls}

- Intrinsic typing rules out type errors, not infinite execution. The
  fixpoint that returns its own variable is still representable at every type.
- An index counts outward from the current binder. Entering a lambda changes
  the positions of all previously available variables.
- `substTerm` must extend its map at every binder, including the successor
  branch and fixpoint body. Handling only lambdas is insufficient.
- `elaborate` consumes a proof. It does not decide whether an arbitrary raw
  term has a type.
- The round-trip theorem concerns raw syntax after erasure. We have not
  identified arbitrary typing derivation objects or assumed function
  extensionality for maps.

## Exercises and checked solutions {#exercises}

1. **Capture avoidance.** In a context containing an outer natural variable,
   replace the parameter of the body λy. parameter by that outer variable.
   Show that the result is λy. outer, not λy. y.
2. **An indexed beta step.** Show that typed identity applied to two takes
   exactly the expected one step.
3. **Values are normal.** Prove, for any context and any type, that an
   intrinsic value has no outgoing `Step`.

{{include:src/PLFA/Part2/DeBruijn.idr#solutions}}

The solutions are `captureAvoidance`, `identityStep`, and `valueNormal`.
The first equality is discharged by computation of `extendSub` and weakening;
it is a concrete regression example. The third is the general theorem: a
successor can step only if its predecessor steps, contradicting the recursive
value proof. Lambdas and zero have no reduction rules at all.

## References and adaptation {#references}

Independent adaptation of [PLFA, DeBruijn](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/DeBruijn.lagda.md)
by Philip Wadler, Wen Kokke, and Jeremy G. Siek, frozen at
`1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Contexts are `Vect` values and references use `Fin` plus type lookup. This
choice preserves the intrinsic scope while allowing a structural bridge from
the earlier external judgements. Renaming, substitution, closed progress,
recursion, call-by-value steps, and fuelled evaluation are implemented for the
whole chapter language. Every included definition is checked with Idris2 0.8.0.

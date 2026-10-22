# Equality: computing, replacing, and reasoning {#equality}

## Motivation {#motivation}

The previous chapters used equality to connect intermediate results. Now we explain the evidence itself. Equality is not a Boolean test on two values. A term of type `x = y` is evidence that can transport any property of `x` to the corresponding property of `y`. This is what permits a theorem about one expression to be used when the goal mentions another.

## The model {#model}

Idris's propositional equality has a reflexive constructor, `Refl`. Its endpoints must coincide after definitional computation. Pattern matching on such evidence makes the two endpoints coincide in the branch. We use the built-in equality so that Idris's `rewrite` mechanism and ordinary equality notation work directly; we do not define a competing equality datatype.

{{include:src/PLFA/Part1/Equality.idr#equality}}

`eqSym` reverses equality, and `eqTrans` composes it. Matching `Refl` explains why both are possible: once the endpoints coincide, the required result is immediate. `eqCong` applies the same function to equal arguments; `eqCong2` handles two arguments. `applicationCong` goes in a different direction: an equality of functions gives equality at each argument. This direction needs no function extensionality.

`transport p eq px` is substitution in a type family. Its inputs are a family `p : a -> Type`, an equality `x = y`, and evidence of `p x`; its output has type `p y`. The family is a function returning a type, not an ordinary predicate returning `Bool`.

## Worked proof: moving parity {#examples}

Suppose we already know that `add m n` is even, and want evenness of `add n m`. The arithmetic theorem `addComm m n` is exactly the equality needed by `transport Even`. `evenComm` therefore does not rebuild the parity derivation manually; it changes the index of existing evidence.

{{include:src/PLFA/Part1/Equality.idr#reasoning}}

The second version, `evenCommRewrite`, uses `rewrite`. To fill a goal at `add n m` with evidence indexed by `add m n`, the proof rewrites the *goal* backwards. That explains the `sym`: the term being supplied already has the old index. This is a useful way to diagnose a rewrite whose orientation seems surprising.

`calculation` presents commutativity with a successor as a chain. First move the successor outside the second argument; then use congruence of the successor on the smaller commutativity theorem; finally close at the resulting expression. `step` records the starting expression and joins two equality proofs, while `finish` closes a chain by reflexivity. `leChain` demonstrates that the same transitivity pattern works for order evidence, even though inequalities cannot generally be reversed.

## Leibniz equality {#theorems}

{{include:src/PLFA/Part1/Equality.idr#leibniz}}

Leibniz's formulation says that `x` and `y` are equal when every property of `x` can be transferred to `y`. `Leibniz a x y` quantifies over all families `p : a -> Type` expressible using the implemented `Type`. Reflexivity leaves the evidence unchanged; transitivity passes it through both transformations.

Ordinary equality implies Leibniz equality by pattern matching. Conversely, choose the particular property “equal to `x`.” We have this property at `x` by `Refl`; applying the proposed Leibniz equality gives it at `y`, which is exactly `x = y`. Symmetry follows by converting to ordinary equality, reversing it, and converting back. These conversions apply to arbitrary types and values, not only naturals.

This chapter uses `Type` as implemented by Idris2 0.8.0. Its [versioned FAQ](https://github.com/idris-lang/Idris2/blob/v0.8.0/docs/source/faq/faq.rst) describes the implementation as `Type : Type`, so we cannot claim the protection of a sound predicative universe hierarchy. The source does not reproduce Agda's universe levels or its universe-polymorphic equality API. The equality and Leibniz arguments above are explicit proof programs checked within this host limitation; compiler acceptance is not a consistency proof. See [Trust](Trust.md#theorems) for the exact boundary.

## Common mistakes {#pitfalls}

Definitional equality is the checker's computation; propositional equality is a type whose inhabitants supply evidence. They interact, but they are not interchangeable. Congruence cannot turn pointwise equality into equality of functions: that converse is extensionality and has not been assumed. A rewrite can change a type index without changing the underlying logical evidence. When it fails, inspect the direction and the exact family being transported, rather than adding unrelated arithmetic lemmas.

## Exercises and checked solutions {#exercises}

1. **E.1 — Equality infrastructure.** Derive symmetry, transitivity, and congruence by matching equality evidence. References: `eqSym`, `eqTrans`, `eqCong`, `eqCong2`.
2. **E.2 — Reasoning chains.** Reconstruct `calculation` with explicit intermediate endpoints. Then explain why `leChain` cannot provide an inequality analogue of `sym`. References: `calculation`, `leChain`.
3. **E.3 — Transport.** Prove the parity commutation theorem once with substitution and once with rewriting. References: `evenComm`, `evenCommRewrite`.
4. **E.4 — Leibniz.** Prove both conversions and symmetry. References: `equalityToLeibniz`, `leibnizToEquality`, `leibnizSym`. The crucial choice is the family used in the converse.

All reference solutions are checked source inclusions. No general equality decision procedure is assumed; [Decidable](Decidable.md#decisions) will construct one for naturals.

## References and adaptation {#references}

Adapted from [PLFA Equality](https://plfa.github.io/Equality/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Idris's equality and ordinary named chain combinators replace Agda's explicit equality module and mixfix reasoning syntax. Agda's universe hierarchy is not reproduced by this host; see [Trust](Trust.md#theorems). The equality and Leibniz proof directions are retained as checked programs within that stated boundary.

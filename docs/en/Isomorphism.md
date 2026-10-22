# Isomorphism: when representations carry the same information {#isomorphism}

## Motivation {#motivation}

Two types may organize the same information differently. A conversion in each direction is not enough to establish this: the conversions might throw information away. An isomorphism includes evidence that both round trips return the original input. An embedding requires just one round trip, making it appropriate when one representation permits extra values.

## Functions and pointwise equality {#model}

{{include:src/PLFA/Part1/Isomorphism.idr#maps}}

A lambda introduces a function by naming its input. Composition applies the inner function first, then the outer function. `Pointwise f g` says that the outputs agree for every input. The two versions of addition demonstrate why this is useful: one recurses on the left argument, the other on the right. `sameApplications` proves their answers agree by induction and the successor lemma, although they have different defining computations.

**Scope of equality.** The upstream chapter assumes function extensionality to turn agreement at all inputs into a propositional equality of functions. This adaptation assumes no such axiom. `sameApplications` is an equality for every `m` and `n`; it is not a proof that the function values themselves are propositionally equal. Later chapters retain pointwise inverse laws explicitly wherever that distinction matters.

## An isomorphism record {#theorems}

{{include:src/PLFA/Part1/Isomorphism.idr#isomorphism}}

`Iso a b` contains `forward`, `backward`, and two laws. For any `x : a`, `backward (forward x) = x`; for any `y : b`, `forward (backward y) = y`. These laws themselves are already pointwise statements. No equality between whole functions is required to define an isomorphism of ordinary data types.

Identity conversions give reflexivity. Swapping the maps and their laws gives symmetry. For transitivity, compose both forward maps, compose the backward maps in reverse order, then cancel the inner round trip followed by the outer round trip. In the left-inverse proof, `cong i.backward` lifts the second isomorphism's cancellation through the first backward map. The resulting expression is exactly the first isomorphism's left-inverse law. The right-inverse proof mirrors this argument.

## Embeddings and a worked example {#examples}

{{include:src/PLFA/Part1/Isomorphism.idr#embedding}}

An `Embedding a b` contains an injection-like map `embed`, a recovery map `project`, and `retract`. The recovery law implies that `embed` cannot identify distinct source values: applying `project` to an equality of their images recovers equality of the sources. It places no requirement on extra target values.

`binaryEmbedding` embeds every natural in raw binary strings. `fromTo` proves that decoding the chosen encoding returns the natural. There is no second law for all strings because leading-zero variants would violate it. This is exactly the difference between an embedding and an isomorphism in a concrete program.

Embeddings compose in the same way as isomorphisms. `isoToEmbedding` simply forgets the second law. In `embeddingAntisym`, two opposed embeddings yield an isomorphism only with compatibility evidence: each map must agree pointwise with the other's recovery map. The theorem is **not** a claim that any two unrelated embeddings automatically supply these particular inverse functions.

`Iff a b` is weaker still: it contains implications in both directions, with no inverse laws. It expresses logical equivalence. Reflexivity, symmetry, and transitivity compose those implications, but do not establish that individual evidence objects are recovered unchanged.

## Common mistakes {#pitfalls}

Types having the same number of visible constructors does not prove isomorphism: constructors may contain different data. Two functions with opposite types need not be inverses. Two implications prove `Iff`, not automatically `Iso`. Conversely, the definition of `Iso` does not require an external extensionality axiom; only particular proofs involving function-valued endpoints may need it. Inspect the exact equality demanded by a round-trip law.

## Exercises and checked solutions {#exercises}

1. **S.1 — Composition.** Prove reflexivity, symmetry, and transitivity for isomorphism. References: `isoRefl`, `isoSym`, `isoTrans`. Trace the two cancellations in the composite left inverse.
2. **S.2 — Forgetting evidence.** Convert an isomorphism to an embedding and compose embeddings. References: `isoToEmbedding`, `embedTrans`.
3. **S.3 — Compatible embeddings.** Construct an isomorphism from opposed embeddings with the stated compatibility assumptions. Reference: `embeddingAntisym`; identify where each assumption is used.
4. **S.4 — Binary.** Construct the natural-to-binary embedding and explain why it is not the raw-string isomorphism. Reference: `binaryEmbedding`, together with `notRawRoundTrip` from Induction.
5. **S.5 — Logical equivalence.** Implement the equivalence operations that require no round-trip proofs. References: `Iff`, `iffRefl`, `iffSym`, `iffTrans`.

## References and adaptation {#references}

Adapted from [PLFA Isomorphism](https://plfa.github.io/Isomorphism/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Named records replace mixfix record names. Function extensionality and the upstream whole-function equality example are deliberately not postulated; the checked result is `sameApplications`. Map compatibility in the embedding theorem is stated pointwise.

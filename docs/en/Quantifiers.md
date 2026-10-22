# Quantifiers: functions over families and packages with witnesses {#quantifiers}

## Motivation {#motivation}

“Every natural has a binary representation” asks for a representation-producing function. “Some natural has this property” asks for a particular number together with evidence of that property. Dependent functions and dependent pairs express those requirements directly, keeping the witness connected to the evidence that mentions it.

## Universals {#model}

{{include:src/PLFA/Part1/Quantifiers.idr#universals}}

A family `p : a -> Type` assigns a proposition to each `x : a`. A universal proof has type `(x : a) -> p x`: the result type can change with the argument. `forallElim` simply applies it at the selected value.

`forallProduct` separates a function returning paired evidence into two dependent functions and recombines them. The recombination recovers each result by `pairEta`. This is an `Iff` with a pointwise inverse theorem, not equality between arbitrary dependent functions. `sumForall` goes from a single global choice of universal branch to a pointwise choice. The converse is not justified: the branch that works may vary with the input.

`Tri` has three values. A universal over it corresponds to three pieces of evidence, whose types are `p Aa`, `p Bb`, and `p Cc`. `triTabulate` selects the correct entry by matching the index; `triRound` proves that tabulating the values of a function recovers its answer at each input. For a finite family, universal quantification therefore behaves like a product.

## Existentials and elimination {#examples}

{{include:src/PLFA/Part1/Quantifiers.idr#existentials}}

A dependent pair `(x ** px)` inhabits `(x : a ** p x)`. The first component is a witness and the second has the witness-dependent type. An ordinary pair has a fixed second-component type; a dependent pair does not. `existsElim` opens the package and passes both components to a consumer whose final result does not depend on the hidden witness.

`existsCurry` converts between a function that takes a witness then its evidence and a function that takes the packaged pair. Its recovery is checked inputwise by `existsCurryRound`. Existential quantification distributes over a sum: the package contains a branch tag, so move that tag outside while preserving the same witness. Both round trips are proved in `existsSum`, a true `Iso` on data. The finite `existsTri` is similarly an `Iso` between one dependent package and the sum of its three possible evidence types.

`existsProduct` extracts two existential packages from a single shared witness. Its converse would need to identify possibly different witnesses, and is not supplied. For example, over `Bool`, “is True” and “is False” each have a witness, but no value witnesses both. Existential quantifiers cannot in general be distributed across conjunction as an isomorphism.

## Arithmetic witnesses {#theorems}

{{include:src/PLFA/Part1/Quantifiers.idr#parity-witnesses}}

An even number comes with a half: `evenWitness` produces `k` and an equality `mul k 2 = n`. An odd number produces `k` and `S (mul k 2) = n`. The functions recurse mutually on parity evidence. When an odd predecessor supplies a half, its even successor uses the successor of that half. When an even predecessor supplies a half, its odd successor uses the same half.

Conversely, `evenDouble` constructs evenness of twice any natural. `witnessEven` transports that evidence along the equality in the package. `witnessOdd` adds the odd constructor before transporting. The left-multiplication variants prove both directions for `2 * k`, using commutativity and the equation moving a final one to the front.

`leExists` characterizes `m ≤ n` by a nonnegative difference: there is a `k` with `k + m = n`. In the zero-left case of `leWitness`, choose `n` as the difference. In the successor case, keep the recursively found difference and move a successor through addition. The reverse direction uses the bound `m ≤ m + k`, commutes the sum, and transports it to `n`. All witnesses are actually produced, rather than being recorded as unexplained existence assertions.

## Negated quantifiers {#negated-quantifiers}

{{include:src/PLFA/Part1/Quantifiers.idr#negated-quantifiers}}

To refute an existential, refute its evidence for every proposed witness. `notExists` proves both implications. To refute a universal, one counterexample is enough: `existsNot` extracts its witness and contradicts the universal's answer there. The converse direction, extracting a counterexample merely from refutation of a universal, is not claimed constructively. The upstream extensional isomorphism for the first law is represented here as `Iff` without equality between whole refutation functions.

## The canonical binary isomorphism {#canonical-isomorphism}

{{include:src/PLFA/Part1/Quantifiers.idr#canonical-isomorphism}}

`CanonicalBin` pairs a raw bit string with proof that it is canonical. A natural maps to its encoding and `canonicalTo` evidence. Decoding forgets the proof and interprets the string. The natural-side inverse is `fromTo`.

The other inverse must recover the **whole dependent pair**. `canonicalRoundTrip` gives equality of the bit strings; it does not by itself compare the proof components. `canonicalPairEqual` first uses that equality to align their types, then applies `canonicalUnique`. This completes `canonicalIso : Iso Nat CanonicalBin`. The restriction is exact: it removes leading-zero aliases without changing the natural-number domain.

## Common mistakes {#pitfalls}

An existential proof includes a witness, not just evidence that a search might succeed. Two existentials can choose different witnesses. Equality of first projections is not in general equality of dependent pairs; here the specific predicate's proof uniqueness supplies the missing step. A universal dependent function may change result type with its input, so treating its results as a homogeneous list loses information.

## Exercises and checked solutions {#exercises}

1. **Q.1 — Universals.** Distribute a universal over a product and tabulate the three-element domain. References: `forallProduct`, `forallProductRound`, `forallTri`, `triRound`.
2. **Q.2 — Existentials.** Prove distribution over a sum and the three-element existential isomorphism. References: `existsSum`, `existsTri`. Explain why `existsProduct` gives only one direction.
3. **Q.3 — Parity witnesses.** Produce and consume the even/odd multiplication witnesses in both orientations. References: `evenWitness`, `oddWitness`, `witnessEven`, `witnessOdd`, `evenWitnessLeft`, `oddWitnessLeft`, `witnessEvenLeft`, `witnessOddLeft`.
4. **Q.4 — Differences.** Prove the difference characterization of order. Reference: `leExists`, using `leWitness` and `witnessLE`.
5. **Q.5 — Negation.** Relate a refuted existential to universal refutations, and use a counterexample to refute a universal. References: `notExists`, `existsNot`.
6. **Q.6 — Binary isomorphism.** Finish equality of the dependent canonical packages, then construct both inverse laws. References: `canonicalPairEqual`, `canonicalIso`.

## References and adaptation {#references}

Adapted from [PLFA Quantifiers](https://plfa.github.io/Quantifiers/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Idris dependent pairs replace Agda sigma notation. Data isomorphisms, arithmetic witnesses, and the complete canonical binary isomorphism are checked. Correspondences requiring whole-function extensionality are explicitly stated as logical equivalences and pointwise laws.

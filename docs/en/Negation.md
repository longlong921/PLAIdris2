# Negation: refutations and the boundary of classical reasoning {#negation}

## Motivation {#motivation}

To refute a proposition, show that any proposed evidence would lead to an impossibility. This is useful both in mathematics and in programs: a failed decision procedure should explain why a successful witness cannot exist. Constructive negation records that explanation as a function to the empty type.

## The model {#model}

{{include:src/PLFA/Part1/Negation.idr#constructive}}

`Refutes a` abbreviates `a -> Void`. We use this name because Idris already uses `Neg` for numeric negation. `notElim` combines a refutation and a witness, obtains `Void`, then eliminates it. Double-negation introduction is constructive: given `x : a`, any refutation of `a` can be contradicted by applying it to `x`.

Triple-negation elimination is constructive too. Given a refutation of double negation and a proposed `x : a`, first use `x` to build double-negation evidence, then feed that evidence to the original refutation. Contraposition precomposes a refutation with a function: if `f : a -> b` and `b` is impossible, then any `a` would produce an impossible `b`.

## Worked refutations {#examples}

`oneNotTwo` and `zeroNotSucc` inspect hypothetical equality evidence. The only equality constructor would identify incompatible natural constructors, so Idris accepts the marked `impossible` case. This is checked constructor exclusion, not a missing implementation or an exception.

`notSum` converts a refutation of a sum into one refutation for each branch, and combines branch refutations by case analysis. For example, a hypothetical `Left x` is rejected by the first component. The record is an `Iff`; its pointwise recovery follows from the fact that any input sum would itself contradict the refutation.

`negationsPointwise` says two refutations agree at every possible input, because such an input yields `Void`. It does not establish a propositional equality between the whole functions. The upstream “assimilation” theorem uses extensionality for that stronger conclusion; this adaptation does not assume it.

## Exclusive trichotomy {#strict-order}

{{include:src/PLFA/Part1/Negation.idr#strict-order}}

The Relations chapter produced a less-than, equality, or greater-than witness. `ExclusiveTri` additionally refutes the other two possibilities. If `m < n` and `m = n`, substitute to obtain `m < m`, contradicting irreflexivity. If `m < n` and `n < m`, transitivity with a non-strict bound again produces `m < m`. Thus `exclusiveTrichotomy` supplies exactly one consistent ordering case for every pair of naturals.

## Constructive and classical principles {#theorems}

Excluded middle claims that every proposition comes with either a witness or a refutation. Constructively, that would be a decision procedure for every type, which we have not supplied. However, its double negation is provable. If `reject` refutes both alternatives, then `x` would make `reject (Left x)` absurd; this defines a refutation of the left proposition. Passing that refutation to `reject` as a right alternative completes the contradiction. This is `excludedMiddleIrrefutable`, not excluded middle itself.

{{include:src/PLFA/Part1/Negation.idr#classical}}

The five named types describe excluded middle, double-negation elimination, Peirce's law, implication as a disjunction, and the classical De Morgan principle. Every theorem in this region takes a principle as an explicit input and constructs another. None supplies an unconditional inhabitant of any of those principle types.

Excluded middle implies double-negation elimination by inspecting the decision: return the witness, or contradict the refutation. Conversely, double-negation elimination applied to the irrefutability theorem gives excluded middle. Excluded middle also yields Peirce, implication-as-disjunction, and De Morgan by cases. Each has a route back: Peirce gives double-negation elimination; implication-as-disjunction applied to identity gives either a refutation or a witness; De Morgan is instantiated at `a` and its negation. Routing through excluded middle therefore shows all five imply one another without asserting that any has been proved outright.

## Stable propositions {#stability}

{{include:src/PLFA/Part1/Negation.idr#stability}}

`Stable a` means double negation can be eliminated for this particular `a`. Negations are stable by triple-negation elimination. If two propositions are stable, their conjunction is stable: derive a double negation of each component from the double negation of the pair, apply the corresponding stability function, then construct the pair. A local stability theorem is weaker than a uniform classical principle for every type.

## Common mistakes {#pitfalls}

Not having found a witness is not a refutation. A refutation must consume *any* proposed witness. Double-negation introduction does not authorize its converse. “Excluded middle is irrefutable” is not “excluded middle has been proved.” Finally, a theorem taking a classical principle as an argument is conditional even if its body compiles without further obligations.

## Exercises and checked solutions {#exercises}

1. **G.1 — Negation.** Derive contraposition and eliminate triple negation. References: `contraposition`, `tripleNegElim`.
2. **G.2 — Exclusive order.** Prove that strict order rules out equality and reverse strict order, then strengthen trichotomy. References: `ltNotEqual`, `ltAsymmetric`, `exclusiveTrichotomy`.
3. **G.3 — De Morgan for sums.** Construct both implications between a refuted sum and a pair of refutations. Reference: `notSum`.
4. **G.4 — Classical equivalence.** Connect the five principles through excluded middle. References: `emToDne`, `dneToEm`, `emToPeirce`, `peirceToEm`, `emToImplication`, `implicationToEm`, `emToDeMorgan`, `deMorganToEm`.
5. **G.5 — Stability.** Prove stability of negations and closure under products. References: `negationStable`, `productStable`.

## References and adaptation {#references}

Adapted from [PLFA Negation](https://plfa.github.io/Negation/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. The classical principles remain explicit assumptions of implication theorems. Equality of arbitrary negation functions and the corresponding extensional isomorphism are replaced by logical equivalence and pointwise equality, with no extensionality axiom.

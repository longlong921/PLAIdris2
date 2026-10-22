# Lists: structural proofs for higher-order programs {#lists}

## Motivation {#motivation}

Natural-number induction follows a chain of successors. List induction follows a chain of elements ending in the empty list. The same method proves useful program properties: concatenation laws, reverse correctness, map and fold fusion, and algorithms that return evidence about every selected element. The elements may have any type; the structure of the list drives these proofs.

## Lists, append, and length {#model}

Idris's `List a` has the empty constructor `[]` and the nonempty constructor `x :: xs`. The type parameter says what kind of elements the list contains; it does not fix its length. The bracket notation `[0, 1, 2]` abbreviates three cons constructors followed by the empty list.

{{include:src/PLFA/Part1/Lists.idr#append}}

`append` recurses over its first list and shares the second as its final suffix. Consequently, an empty first list is a left identity by computation. The right identity needs induction. Associativity follows by stripping the first list's head, applying the smaller theorem, and restoring the head with congruence. `sizeAppend` follows the same recursion, replacing each cons by a successor and append by natural addition.

## Reverse and an accumulator invariant {#examples}

{{include:src/PLFA/Part1/Lists.idr#reverse}}

The direct reverse recursively reverses the tail, then appends the head as a singleton. `reverseAppend` says reversing a concatenation reverses the order of its parts. Its successor case uses append associativity after the induction hypothesis. `reverseInvolutive` uses that distribution theorem: the reverse of the reversed tail followed by a singleton becomes the original head followed by the original tail.

Repeatedly appending at the end traverses growing prefixes, giving quadratic traversal work. `shunt` instead moves each head onto an accumulator. The informal cost is linear because each source element is processed once; no machine-cost theorem is claimed here.

The key correctness statement is stronger than the final result: for **every** accumulator `ys`, `shunt xs ys = append (reverseList xs) ys`. In the recursive step the accumulator changes to `x :: ys`, so a theorem fixed to the empty accumulator would be too weak. `shuntCorrect` quantifies over the accumulator; `reversesAgree` then specializes it to empty and uses the append right identity.

## Map, fold, and trees {#theorems}

{{include:src/PLFA/Part1/Lists.idr#map-fold}}

`mapList` changes each element while preserving list structure. `mapCompose` combines two traversals pointwise; `mapAppend` distributes mapping over concatenation. A right fold replaces the empty-list constructor by a base value and cons by a supplied combining function. The result type may differ from the element type. `sumList` and `productList` are instances with zero and one as their respective empty results.

`foldAppend` exposes exactly what happens at the boundary between two lists: folding the concatenation is folding the first list with the folded second list as the new base. This law needs no associativity assumption. `foldCons` reconstructs a list using its own constructors, and `mapAsFold` expresses mapping with a cons-building algebra.

{{include:src/PLFA/Part1/Lists.idr#trees}}

`Tree a b` distinguishes leaf payloads from internal-node labels. `mapTree` transforms both; `foldTree` consumes each constructor with its own operation. `mapTreeAsFold` proves the map implementation is a particular fold by induction over both subtrees. This is structural recursion over branching data, not an assumption that all trees have one fixed shape.

## Monoids and folding direction {#monoids}

{{include:src/PLFA/Part1/Lists.idr#monoids}}

`MonoidLaw` packages associativity and two identity laws for an operation and unit. Addition with zero, multiplication with one, and append with the empty list supply concrete records using the earlier proofs. A record of laws does not prove itself: each field is filled by a checked function.

`foldMonoid` moves a final base value outside a fold; `foldMonoidAppend` then turns concatenation into the monoid operation. The accumulator invariant `foldLeftInvariant` relates a left fold starting at any accumulator to a right fold. Associativity moves parentheses without reordering elements; commutativity is **not** required. Specializing the accumulator to the unit proves `foldDirectionsAgree`.

`downFrom n` lists `n - 1` down to zero. `sumDownFromTimes` proves the exact division-free arithmetic-series formula: its sum multiplied by two is `n * (n ∸ 1)`. The helper `sumDownFrom` states the doubled sum as addition. The step groups the two new leading terms with `doubleAdd`, applies the smaller sum theorem, and uses multiplication commutativity. Zero and one are handled explicitly, so truncation at zero introduces no hidden positivity assumption.

## Evidence about list elements {#predicates}

{{include:src/PLFA/Part1/Lists.idr#predicates}}

`All p xs` contains one `p` proof per element. `Any p xs` selects a position: `Here` proves the head satisfies `p`, while `There` shifts a tail witness one position right. Membership specializes `Any` to equality with a selected value.

The list `[0, 1, 0, 2]` contains zero at two positions. `firstZero` and `secondZero` deliberately use different evidence constructors. Membership is proof-relevant: a value can occur more than once, so its membership evidence need not be unique. `threeAbsent` checks every possible position and eliminates impossible equalities.

## Quantified list laws {#quantified-laws}

{{include:src/PLFA/Part1/Lists.idr#quantified-laws}}

Evidence that every element of an append satisfies `p` can be split into evidence for each part. `allAppendFrom` recombines it. `allAppendIso` proves both round trips on the actual evidence trees; no general proof-irrelevance or function-extensionality assumption is used. The recursive split theorem records an equality for its intermediate pair so its inverse proof follows the chosen components precisely.

For `Any`, a position in the concatenation lies in one part or the other, producing `anyAppendIff`. Refuting every possible `Any` witness is equivalent to having a refutation at each position, as `notAnyIff` shows. This latter statement is an `Iff`, not the upstream extensional `Iso` involving functions.

`allForall` relates `All` to a function that returns `p x` whenever supplied with membership evidence for `x`. `allForallLeft` proves recovery of the evidence tree; `allForallPointwise` proves recovery at each value and membership proof. The function-valued endpoint is treated pointwise, without extensionality. `anyExistsIso` is a full data isomorphism between `Any` and an actual element, its membership evidence, and its predicate evidence; `anyExists` retains the simpler two-map interface. These conversions preserve the relationship to the list; an existential witness without membership would not suffice.

## Deciding predicates and certified partition {#decidable-split}

{{include:src/PLFA/Part1/Lists.idr#decidable-split}}

If the element predicate has a decision procedure, `decAll` checks every element until a refutation is found, while `decAny` searches for one witness. The empty-list outcomes differ: `All` succeeds vacuously, but `Any` has no constructor. The negative results are functions that inspect any proposed evidence and contradict the failing component.

`Merge xs ys zs` records an interleaving: each element of `zs` comes from the head of one output list, preserving order within each. `split` returns two lists, a merge proof back to the original, proofs that all elements on the first list satisfy the predicate, and proofs that all on the second refute it. A positive decision prepends to the first list and uses `MergeLeft`; a negative decision prepends to the second and uses `MergeRight`. Thus the result accounts for the entire input, including duplicates, rather than merely proving something about a possibly incomplete filtered list.

## Common mistakes {#pitfalls}

A proof about an accumulator often needs a stronger invariant than the final desired result. Folding left and right need not agree for an arbitrary operation; the monoid hypotheses matter. `All` is not “the list is nonempty,” and `Any` is not “all elements satisfy the predicate.” Duplicate membership witnesses must not be silently identified. Finally, testing a filter on several inputs is weaker than returning the complete merge and predicate evidence produced by `split`.

## Exercises and checked solutions {#exercises}

1. **L.1 — Append.** Prove associativity, the right identity, and the length law. References: `appendAssoc`, `appendRightNil`, `sizeAppend`.
2. **L.2 — Reverse.** Prove reverse distributes over append and is involutive. References: `reverseAppend`, `reverseInvolutive`.
3. **L.3 — Faster reverse.** State the accumulator invariant before proving the optimized reverse correct. References: `shuntCorrect`, `reversesAgree`.
4. **L.4 — Map.** Prove map composition and distribution over append. References: `mapCompose`, `mapAppend`.
5. **L.5 — Folds and trees.** Define product, prove the append fold law and map-as-fold laws for both lists and trees. References: `productList`, `foldAppend`, `foldCons`, `mapAsFold`, `mapTree`, `foldTree`, `mapTreeAsFold`.
6. **L.6 — Arithmetic series.** Prove the doubled-sum formula for every natural, including zero. Reference: `sumDownFromTimes` with helpers `doubleAdd`, `sumDownFrom`.
7. **L.7 — Monoids.** Show fold distributes over append and both folding directions agree under the exact monoid laws. References: `foldMonoidAppend`, `foldLeftInvariant`, `foldDirectionsAgree`.
8. **L.8 — Quantified laws.** Split and recombine `All`, locate an `Any` witness in an append, and distribute its negation. References: `allAppendIso`, `anyAppendIff`, `notAnyIff`.
9. **L.9 — Membership.** Convert `All` into universal membership-indexed evidence and `Any` into an existential package. References: `allForall`, `allForallLeft`, `allForallPointwise`, `anyExistsIso`.
10. **L.10 — Certified algorithms.** Decide `All` and `Any`, then partition a list with a full reconstruction proof. References: `decAll`, `decAny`, `split`, `mergeExample`.

## References and adaptation {#references}

Adapted from [PLFA Lists](https://plfa.github.io/Lists/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. The generic list/tree laws, monoid hypotheses, arithmetic-series theorem, quantified evidence, and full certified split are retained. The negated-`Any` correspondence is checked as `Iff`, and the `All`/universal correspondence has evidence-tree and pointwise inverse laws; their function-valued extensional `Iso` upgrades are not assumed. All displayed Idris is included directly from the compiled module.

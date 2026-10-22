# Connectives: propositions as structured evidence {#connectives}

## Motivation {#motivation}

To prove “A and B,” provide evidence of both. To prove “A or B,” choose a side and provide its evidence. To prove “A implies B,” give a procedure that turns any evidence of A into evidence of B. This computational reading explains why logical connectives correspond to familiar types: pairs, tagged alternatives, and functions.

## Products and truth {#model}

{{include:src/PLFA/Part1/Connectives.idr#products}}

A pair `(x, y)` proves a conjunction; `fst` and `snd` eliminate it by selecting the needed evidence. `pairEta` says that decomposing and rebuilding a pair recovers it. The two projections reveal enough information to reconstruct the original value. `productComm` swaps the components, and `productAssoc` changes the nesting. Both are actual `Iso` records with both inverse laws.

The unit type `()` has a single constructor, also written `()`, and represents truth. Pairing evidence with unit adds no information, as `unitLeft` and `unitRight` show. `iffProduct` identifies the record of two implications with a pair of functions; its inverse laws hold by inspecting the record and pair, without comparing arbitrary function bodies.

## Sums and falsehood {#examples}

{{include:src/PLFA/Part1/Connectives.idr#sums}}

`Either a b` has a tag: `Left x` or `Right y`. The tag matters even when the payload types happen to coincide. `sumCase` consumes a sum by supplying one handler per alternative. `sumEta` rebuilds the chosen alternative. `sumUnique` says that any function out of a sum agrees, at each input, with the case analysis determined by its behavior on the two constructors.

A sum of a two-element type and a three-element type has five alternatives; their product has six pairs. These counts illustrate the names “sum” and “product.” They are finite examples of the type structure, not the proofs of the generic isomorphisms. `sumComm` and `sumAssoc` prove the generic laws by constructor analysis.

The empty type `Void` has no constructors and represents falsehood. `explode` eliminates impossible evidence into any requested type. No constructor supplies such an input; using this eliminator requires actual contradictory evidence. The host foundation boundary is explained in [Trust](Trust.md#theorems). `emptyLeft` and `emptyRight` establish that adding an impossible alternative contributes no inhabitants.

## Implication as a function {#theorems}

{{include:src/PLFA/Part1/Connectives.idr#functions}}

Applying a function eliminates an implication. If A has two values and B has three, a total function from A to B can independently choose one of three results at each input, giving nine possible tables. This motivates the exponential interpretation of function spaces.

Currying changes a function of a pair into a function with two successive inputs. `curryPair` and `uncurryPair` implement the conversions. `curryRound` proves recovery at each pair of inputs; `uncurryRound` proves recovery for each pair value. `functionSum` says that a function consuming a sum corresponds logically to a pair of branch handlers. Its nontrivial inverse is the case-analysis uniqueness theorem. `functionProduct` separates a pair-valued result into two functions, and `functionProductRound` recovers each result using pair eta.

**Exact scope:** these three function-space correspondences are `Iff` values with pointwise recovery theorems, not `Iso` records whose endpoints include arbitrary functions. The remaining recovery directions compute at each input by the definitions. The upstream upgrades to whole-function equality using extensionality; this book does not assume that upgrade.

## Distribution and information loss {#distribution}

{{include:src/PLFA/Part1/Connectives.idr#distribution}}

To distribute `(Either a b, c)`, inspect the tag and keep the accompanying `c` in the selected branch. Factoring reverses the construction, so `productSum` is a genuine isomorphism.

The other pattern, `Either (a, b) c` into `(Either a c, Either b c)`, has a checked embedding. A left pair becomes two left alternatives; a right value is copied to both right alternatives. The target also permits mixed tags and two different right payloads, so the given projection need not recover every target value. `sumProduct` asserts only the justified left inverse.

`weakDistribution` discards the accompanying `c` when the left alternative is selected. `disjunctToConjunct` transforms a disjunction of two conjunctions into a conjunction of disjunctions. Its general converse fails: instantiate A and D as unit, B and C as empty. The target pair has `(Left (), Right ())`, while either source alternative requires impossible evidence. `noGeneralConverse` checks that counterexample as a refutation of any proposed converse function at those types.

## Common mistakes {#pitfalls}

A disjunction requires knowing which branch holds; a pair cannot be used as an untagged “or.” Explosion does not manufacture a contradiction—it requires one. An embedding must not be described as an isomorphism merely because both map directions are implemented. When endpoint values are functions, pointwise recovery and propositional equality of those values must remain distinct.

## Exercises and checked solutions {#exercises}

1. **C.1 — Products.** Prove commutativity, associativity, and the truth identity laws. References: `productComm`, `productAssoc`, `unitLeft`, `unitRight`.
2. **C.2 — Sums.** Prove commutativity, associativity, and the falsehood identity laws. References: `sumComm`, `sumAssoc`, `emptyLeft`, `emptyRight`.
3. **C.3 — Functions.** Implement currying and show both inputwise round trips. References: `currying`, `curryRound`, `uncurryRound`.
4. **C.4 — Distribution.** Give the full product-over-sum isomorphism and the weak distribution function. References: `productSum`, `weakDistribution`; identify the data discarded by the latter.
5. **C.5 — A failed converse.** Implement the implication from disjuncts of conjuncts and refute its unrestricted converse. References: `disjunctToConjunct`, `noGeneralConverse`.

## References and adaptation {#references}

Adapted from [PLFA Connectives](https://plfa.github.io/Connectives/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Standard Idris pair, unit, sum, and empty types provide the connectives. Function-space isomorphisms are presented with their checked logical equivalences and pointwise laws, explicitly avoiding the upstream extensionality assumption.

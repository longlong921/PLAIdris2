# Decidable: computing answers with evidence {#decidable}

## Motivation {#motivation}

A Boolean comparison is convenient to execute, but its result alone does not explain the relation it computed. An inductive relation provides evidence, but does not by itself supply an algorithm that finds evidence or rules it out. A decision procedure joins the two: it terminates with either a witness or a function refuting every proposed witness.

## Booleans and evidence {#model}

{{include:src/PLFA/Part1/Decidable.idr#boolean-evidence}}

`Truth True` is unit and `Truth False` is empty. Thus `Truth` interprets a Boolean as a proposition that holds exactly in the true case. `truthEquality` connects this interpretation to equality with `True`, while `equalityTruth` goes back. This is an explicit bridge between computation and propositions.

`leBool` follows the same recursion as the order relation. `boolToLE` proves soundness: if the comparison computes true, there is order evidence. `leToBool` proves completeness: order evidence forces the comparison to compute true. In the successor case both reduce to the predecessor problem. Neither direction silently assumes that arbitrary Booleans are correct comparisons; they relate this particular algorithm to this particular relation.

## Decision procedures {#decisions}

{{include:src/PLFA/Part1/Decidable.idr#decisions}}

Idris's `Dec a` has `Yes` carrying an `a`, and `No` carrying `a -> Void`. `decLE` returns `Yes LZ` for zero. A positive number at most zero is impossible, so that branch returns a checked refutation. With two successors, it recursively decides the predecessors; success wraps the evidence with `LS`, and failure refutes any hypothetical `LS` evidence by stripping it and applying the recursive refutation.

`decLT` uses the shifted non-strict relation. `decNatEq` compares constructors, recurses on two successors, and uses `succInjective` to turn a hypothetical successor equality into the predecessor equality that has been refuted. These are decisions for concrete inductive propositions, not unrestricted excluded middle.

`decBool` forgets the evidence. `toWitness` recovers evidence when that forgotten result is true, and `fromWitness` proves that a valid witness forces a supplied decision to be positive. `reflectedLE` proves the erased `decLE` answer agrees with `leBool` on every pair. Its `with` split records an equality for the recursive decision so the proof can relate the inspected branch to the original expression.

## Worked computation {#examples}

`decisionExamples` checks that two is at most four, four is not at most two, and three equals itself. Follow the negative comparison: stripping two pairs of successors leaves the impossible judgment that two is at most zero. The returned `No` is a composed refutation of any attempted evidence for the original comparison; it is not an error string or an absent result.

## Combining decisions {#theorems}

{{include:src/PLFA/Part1/Decidable.idr#connectives}}

A conjunction is decidable when both components are. Two witnesses produce a pair; one refuted component rejects any pair by projection. A disjunction succeeds as soon as either witness is available; only two refutations justify rejecting the sum. Negation exchanges a negative witness with a refutation of positive evidence.

For implication, a refuted premise makes the function possible by explosion. If both propositions have witnesses, a constant function suffices. A witnessed premise and refuted conclusion refute any proposed function by applying it. `decIff` decides both implication directions and packages them in `Iff`.

The erasure theorems prove agreement with Boolean conjunction, disjunction, negation, implication, and biconditional truth tables. They compare only the Boolean answers, not the different possible proof objects stored in `Yes` or refutation functions stored in `No`. The algorithms therefore carry evidence while retaining familiar executable behavior.

## Proof by reflection {#reflection}

{{include:src/PLFA/Part1/Decidable.idr#reflection}}

`minus m n` requires evidence of `n ≤ m`. Its impossible branch shows that the precondition rules out underflow. `safeMinus` replaces that explicit derivation with an automatically supplied proof that the decision's Boolean result is true. The checked decision constructs the needed order evidence through `toWitness`.

For the concrete expression `safeMinus 5 3`, normalization computes the decision to true, leaving the unit proof for implicit search. `safeMinusExample` checks the result is two. At inputs where the precondition computes false, the required implicit type becomes `Void`; ordinary proof search cannot invent an inhabitant. With variables, the caller may need to supply evidence because the decision cannot yet compute. Reflection is not an oracle: it relies on a proved decision procedure and type-level evaluation.

`FalseDecision` gives the corresponding negative interpretation. `fromFalse` extracts a refutation from a negative decision, and `toFalse` proves that an existing refutation forces that decision's negative Boolean result.

## Deciding canonical binary syntax {#binary-decisions}

{{include:src/PLFA/Part1/Decidable.idr#binary-decisions}}

`decOne` inspects the finite bit-string structure. A single leading one succeeds; appending a digit requires the prefix's leading-one evidence; empty and leading-zero-only forms fail. `decCanonical` separately accepts the single zero and otherwise requires positive canonical evidence. `positiveDecision` shares the proof-producing part where the zero constructor is excluded by the input shape.

The examples distinguish zero, a noncanonical extra zero, and two. This decision checks representation syntax, not whether the string denotes a natural: every raw binary string already has a natural interpretation.

## Common mistakes {#pitfalls}

`No` must contain a refutation, not a guess or a timeout. Erasing a decision loses useful evidence, so keep `Dec` when later code requires a witness. A Boolean equality is not automatically an order derivation; use the proved bridge. Reflection may discharge concrete preconditions while leaving symbolic ones unresolved, and that is expected rather than a failure of the theorem.

## Exercises and checked solutions {#exercises}

1. **D.1 — Order and equality.** Implement strict-order and natural-equality decisions with negative evidence. References: `decLT`, `decNatEq`.
2. **D.2 — Reflection bridge.** Convert Boolean truth to order evidence and back; show that the two comparisons agree after erasure. References: `boolToLE`, `leToBool`, `reflectedLE`.
3. **D.3 — Logical decisions.** Decide conjunction, disjunction, negation, implication, and equivalence. References: `decAnd`, `decOr`, `decNot`, `decImplies`, `decIff`.
4. **D.4 — Erasure.** Prove the five Boolean truth-table correspondences. References: `andErasure`, `orErasure`, `notErasure`, `impliesErasure`, `iffErasure`.
5. **D.5 — Safe subtraction.** Use a reflected precondition and check five minus three. References: `safeMinus`, `safeMinusExample`; derive the negative counterpart with `fromFalse`, `toFalse`.
6. **D.6 — Binary syntax.** Decide the leading-one and canonical predicates, preserving evidence in both outcomes. References: `decOne`, `decCanonical`, `canonicalDecisionExamples`.

## References and adaptation {#references}

Adapted from [PLFA Decidable](https://plfa.github.io/Decidable/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Idris's `Dec` and implicit argument search replace Agda's decision datatype and instance-argument notation. The evidence/computation correspondence, connective erasure laws, reflection example, and binary-predicate decisions are checked for their full stated domains.

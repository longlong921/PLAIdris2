# Relations: evidence indexed by values {#relations}

## Motivation {#motivation}

A Boolean comparison can tell us that two is at most four. A relation can additionally explain *why*, by returning a finite derivation. Such evidence can be inspected, transformed, and passed to another theorem. This is the first sustained example of an indexed datatype: its indices record which judgment a constructor proves.

## The model {#model}

`LE m n` means that `m` is at most `n`. `LZ` proves zero is at most any natural. `LS` turns evidence for `m ≤ n` into evidence for `S m ≤ S n`. A derivation's type rules out impossible shapes. For example, evidence for two at most four must begin with two `LS` constructors, whereas no constructor can prove a successor at most zero.

{{include:src/PLFA/Part1/Relations.idr#order}}

`lePred` is inversion: from an indexed conclusion with successors on both sides, recover its premise. `leZero` says that being at most zero forces equality with zero. Braces mark implicit arguments; some are explicitly available because a proof-producing function must inspect them. Idris's erased parameters cannot be used for runtime computation merely because their names appear in a type.

## Reading an order proof {#examples}

`twoLEfour` is `LS (LS LZ)`. Its innermost rule proves zero at most two; the first successor produces one at most three; the second produces two at most four. To prove transitivity, inspect both derivations. If the first starts with `LZ`, the result is immediately `LZ`. If it starts with `LS`, the shared middle index forces the second derivation to start with `LS` too. Strip both, recurse, and restore one successor.

Antisymmetry follows the same pattern, ending in equality. Totality is different: for every pair of naturals it produces either `LE m n` or `LE n m`. It does not say these alternatives are exclusive; equal values satisfy both. `Trichotomy` separates strict order from equality. Strict order is defined here as `LT m n = LE (S m) n`, so its conversion to the successor formulation is definitional rather than a separate pair of constructors.

## Order and parity theorems {#theorems}

The order region proves reflexivity, transitivity, antisymmetry, totality, addition and multiplication monotonicity, strict transitivity, strict addition monotonicity, and irreflexivity. `addMono` permits both arguments to increase. `ltAddMono` proves that increasing both strictly also increases the sum strictly. `leStep` and `ltToLe` connect strict and non-strict bounds. These statements quantify over arbitrary naturals and derivations.

{{include:src/PLFA/Part1/Relations.idr#parity}}

Parity is defined mutually. Zero is even. A successor of an odd number is even; a successor of an even number is odd. `fourEven` alternates the constructors until reaching zero. The proofs that even plus even is even and odd plus even is odd also recurse mutually: removing the outer constructor changes which parity theorem is needed. The other pair proves even plus odd is odd and odd plus odd is even. Mutual recursion terminates because each call consumes part of the first evidence tree.

## Canonical binary strings {#canonical}

{{include:src/PLFA/Part1/Relations.idr#canonical}}

`One b` says that the first digit is one. It starts with exactly `B1 Empty` and permits either digit to be appended. `Canonical b` allows either such a positive string or the single zero. Leading zeroes have no constructor in this predicate. The datatype of bit strings remains unrestricted; the predicate identifies the valid representatives within it.

Increment preserves `One` for positive strings and preserves `Canonical` for all canonical strings. Therefore every result of `toBin` is canonical. `onePositive` proves a positive string has value at least one. This premise matters: doubling zero and appending zero to the chosen representation of zero produce different strings.

`toDoublePositive` proves the needed doubling law for positive naturals. `oneRoundTrip` uses it to move conversion through an appended digit; its induction hypothesis handles the prefix. `canonicalRoundTrip` adds the zero case and establishes the exact missing premise from [Induction](Induction.md#binary-laws). Finally, `oneUnique` and `canonicalUnique` show that each valid string has only one proof of its corresponding predicate. Later, that fact will allow equality of dependent pairs, not just equality of their bit strings.

## Common mistakes {#pitfalls}

A total *order* compares every pair; a total *function* terminates and covers every possible input. These are different meanings of “total.” Antisymmetry is not symmetry: two inequalities together force equality. Inverting a derivation is justified by its indices, not by wishful pattern matching. Canonicality is not the proposition “this string has a value”: every raw string has a value, including strings with leading zeroes.

## Exercises and checked solutions {#exercises}

1. **R.1 — Order structure.** Prove transitivity and antisymmetry, accounting for the impossible cases. References: `leTrans`, `leAntisym`.
2. **R.2 — Monotonicity.** Derive addition and multiplication monotonicity. References: `addMono`, `mulMono`. Explain where addition is needed in the multiplication proof.
3. **R.3 — Strict order.** Prove transitivity, irreflexivity, and strict addition monotonicity. References: `ltTrans`, `ltIrreflexive`, `ltAddMono`.
4. **R.4 — Odd plus odd.** Complete the mutually recursive parity proofs. References: `evenPlusOdd`, `oddPlusOdd`.
5. **R.5 — Binary predicates.** Define leading-one and canonical evidence, prove preservation by increment, and prove the canonical round trip. References: `One`, `Canonical`, `canonicalInc`, `canonicalTo`, `canonicalRoundTrip`.
6. **R.6 — Unique evidence.** Prove that two canonicality proofs for the same bit string are equal. References: `oneUnique`, `canonicalUnique`.

## References and adaptation {#references}

Adapted from [PLFA Relations](https://plfa.github.io/Relations/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; fixed upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. `LT` is represented by a shifted `LE`, retaining the same strict natural ordering. Mutually inductive parity and the full leading-zero-sensitive binary predicates are retained.

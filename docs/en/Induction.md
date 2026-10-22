# Induction: recursive programs that prove laws {#induction}

## Motivation {#motivation}

A calculation settles one input. Associativity says something about every triple of naturals. No finite list of numerical tests covers that claim. Induction works because every natural is either zero or a successor: establish the zero case, then construct the successor case from evidence for its predecessor. The resulting proof is a recursive function whose output type states the desired equality.

## The model {#model}

We retain the operations from [Naturals](Naturals.md#model). A theorem such as `addAssoc` takes arbitrary `m`, `n`, and `p`, and returns evidence for `(m + n) + p = m + (n + p)`, expressed with `add`. Parentheses matter: this is associativity, whereas exchanging two arguments is commutativity, and zero being neutral is an identity law. A property is a proposition to prove, not permission to rearrange terms without evidence.

{{include:src/PLFA/Part1/Induction.idr#addition}}

## A proof, step by step {#examples}

In `addAssoc Z n p`, both sides compute to `add n p`, so `Refl` finishes. For `S m`, both sides expose an outer `S`. The remaining equation is exactly `addAssoc m n p`. `cong S` lifts that equality through the common constructor. The recursive call is on the smaller `m`, making this both a valid induction and a total program.

Commutativity is harder because addition recurses on its first argument. In the zero case, the right side is `add n Z`, so we first need `addZeroRight`. In the successor case, `addSuccRight` moves a successor out of the *second* argument. The proof connects `S (add m n)` to `S (add n m)` using the induction hypothesis, then connects that to `add n (S m)` using the successor lemma backwards. `trans` joins the equalities and `sym` reverses the second one.

You can unroll this recursion for zero, one, or two, obtaining separate finite proofs. The recursive definition covers every finite natural without requiring infinitely many handwritten cases. When working interactively, inspect the goal after matching a constructor; then ask which computation exposes the smaller goal. The reference files contain completed proofs, not saved holes.

## Algebraic theorems {#theorems}

{{include:src/PLFA/Part1/Induction.idr#multiplication}}

`mulDistrib` proves `(m + n) * p = m * p + n * p`. Its successor case uses the induction hypothesis and addition associativity to regroup the extra copy of `p`. Multiplication associativity then follows by expanding one recursive multiplication, distributing, and applying its own smaller induction hypothesis. `mulSuccRight` plays the same supporting role for multiplication commutativity that `addSuccRight` played for addition.

{{include:src/PLFA/Part1/Induction.idr#powers-monus}}

The three exponent laws express addition of exponents, multiplication of exponents, and exponentiation of a product. Each uses previously proved multiplication laws; none treats arithmetic normalization as a black box. `powerProduct` uses `mulSwap` to exchange the middle factors before regrouping. `monusAdd` states that subtracting `n` and then `p` is the same as subtracting their sum, even when subtraction truncates at zero. Its zero case is why `zeroMonus` is useful.

## Binary laws and normalization {#binary-laws}

{{include:src/PLFA/Part1/Induction.idr#binary-laws}}

`fromInc` proceeds by the final binary digit. The carry case needs `doubleSucc`: doubling a successor adds two. `fromTo` then follows by induction on the natural, using `fromInc` at each step. There is no restriction on the natural or the input bit string in these two laws.

The reverse claim for arbitrary raw bit strings is false: converting `Empty` through its numerical value yields the single zero. `notRawRoundTrip` is a checked refutation of that particular equality. Nevertheless, normalization preserves numerical value and is idempotent. Applying it twice has no additional effect because `fromTo` removes the intervening natural-to-binary-to-natural conversion. Later we strengthen the reverse law with a canonicality premise.

## Common mistakes {#pitfalls}

Do not try `Refl` for equations that require induction. Do not assume the induction hypothesis at the original input: only a structurally smaller recursive call is justified. Rewriting has a direction, and the desired direction often requires `sym`. Proving commutativity before its supporting successor lemma creates an apparent dead end; choosing lemmas is part of the proof, not a workaround.

## Exercises and checked solutions {#exercises}

1. **I.1 — Rearrangement.** Exchange the first two summands without changing the third, then regroup four summands. References: `addSwap`, `addRearrange`.
2. **I.2 — Distributivity.** Prove both multiplication distribution laws. References: `mulDistrib`, `mulDistribRight`; identify which uses commutativity.
3. **I.3 — Multiplication.** Prove associativity and commutativity for arbitrary naturals. References: `mulAssoc`, `mulComm`, supported by `mulSuccRight`.
4. **I.4 — Monus.** Prove zero minus any natural is zero, and sequential subtraction equals subtraction of a sum. References: `zeroMonus`, `monusAdd`.
5. **I.5 — Powers.** Prove the three exponent laws and identify every multiplication lemma used. References: `powerAdd`, `powerMul`, `powerProduct`.
6. **I.6 — Binary laws.** Determine which of the two round trips holds without restrictions; prove increment correctness and normalization idempotence. References: `fromInc`, `fromTo`, `notRawRoundTrip`, `normalizeIdempotent`.

Each named solution is present in the included source and checked under `%default total`. These are universally quantified statements, not tests over a bounded range.

## References and adaptation {#references}

Adapted from [PLFA Induction](https://plfa.github.io/Induction/), CC BY 4.0, Philip Wadler, Wen Kokke, Jeremy G. Siek; fixed upstream `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Named Idris operations replace Agda mixfix operators. Both explicit equality composition and `rewrite` appear in the checked implementation. The mathematical arithmetic and binary laws retain their unrestricted domains.

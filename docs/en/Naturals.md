# Naturals: numbers from constructors {#naturals}

## Motivation {#motivation}

A proof assistant does not have to take arithmetic on trust. We can describe how a natural number is built, define arithmetic by following that construction, and ask the type checker to verify the resulting calculations. This chapter starts with that small foundation. Later chapters turn the same method into proofs about every number, and eventually every program.

Our natural numbers are Idris's `Nat`, whose constructors are `Z` and `S`. `Z` means zero; `S n` means the successor of `n`. Thus two is `S (S Z)`. These are finite constructor trees: repeatedly taking the predecessor eventually reaches `Z`. There is no negative constructor, no largest constructor tree, and no extra constructor for infinity. A finite definition therefore describes an unbounded collection of values.

## The model {#model}

The type `Nat -> Nat -> Nat` describes a curried function: it takes one natural and returns a function taking another. Function application associates leftward, so `add m n` means `(add m) n`. We give operations distinct names to make their defining equations visible; these are not calls to an arithmetic solver.

{{include:src/PLFA/Part1/Naturals.idr#arithmetic}}

Addition recurses on its **first** input. Zero contributes nothing. A successor contributes one `S` and leaves a smaller addition. Multiplication similarly adds one copy of the second input at each successor of the first. Exponentiation recurses on its exponent; its zero case is one, including when the base is zero. This is the usual algebraic convention for natural exponentiation.

Subtraction here is *monus*: it stops at zero. Removing zero leaves the first input unchanged; removing a successor from zero stays zero; removing successors from both inputs cancels one from each. Each recursive call consumes constructors, which is why these definitions satisfy `%default total`.

## Worked calculations {#examples}

To compute `add 2 3`, first expose two as a successor. The result becomes `S (add 1 3)`, then `S (S (add 0 3))`, then `S (S 3)`, which is five. `mul 2 3` becomes `add 3 (mul 1 3)`, and then two copies of three. `monus 3 5` cancels three pairs of successors before reaching the zero case with two subtractions still requested.

{{include:src/PLFA/Part1/Naturals.idr#examples}}

The type before each example is a proposition. `Refl` is evidence that its two sides are equal after the definitions compute. The explicit seven shows how numerals abbreviate constructors. These examples check the definitions' behavior; checking several inputs is not yet a proof of a law for all inputs.

## Binary representation {#binary}

Unary constructors make induction simple, but representing a large value takes many successors. A binary digit doubles the number represented by the prefix, and a one digit then adds one. `B0 b` appends a zero to the bit string `b`; the outer constructor is the rightmost, least significant digit. For example, eleven is `B1 (B1 (B0 (B1 Empty)))`: read the constructors from the inside outward to obtain 1011.

{{include:src/PLFA/Part1/Naturals.idr#binary}}

Incrementing a trailing zero changes it to one. Incrementing a trailing one changes it to zero and propagates the carry into the prefix. At the empty prefix the carry creates a one. Conversion `toBin` starts with the single zero and repeatedly increments; `fromBin` interprets each digit using doubling. `binaryExamples`, `binaryValues`, and `carryExample` check zero through four and the carry from eleven to twelve.

`Empty`, `B0 Empty`, and `B0 (B0 Empty)` all have value zero. The raw datatype intentionally permits leading zeroes. `normalize` chooses the representation produced by conversion through `Nat`. This conversion is a simple specification, not a claim of efficient large-number arithmetic: repeated increment still follows the unary input.

## What has been established {#theorems}

All displayed examples are closed equalities checked by computation. The next chapter proves that increment increases the interpreted value by one, and that converting a natural to binary and back is always the identity. The opposite round trip needs a restriction on representations, which [Relations](Relations.md#canonical) will supply. Keeping those two claims separate prevents an invalid theorem from looking plausible merely because a few test values passed.

## Common mistakes {#pitfalls}

`Refl` does not invoke commutativity. `add 0 n` computes to `n`, but `add n 0` is stuck when `n` is unknown because addition inspects its first argument. Monus is not integer subtraction: `monus 3 5` is zero, not minus two. Binary nesting runs opposite to the visual order of printed bits. Finally, distinguish the empty string from the chosen representation of zero even though they have the same numerical value.

## Exercises and checked solutions {#exercises}

1. **N.1 — Constructors.** Write seven without a numeric literal. Check the reference `seven` in the examples region.
2. **N.2 — Reduction.** Calculate three plus four and three times four, writing every use of a defining equation. The checked endpoints are `addExample` and `mulExample`.
3. **N.3 — Exponents.** Define exponentiation by recursion on the exponent and check three to the fourth power. References: `power`, `powerExample`. Explain why the zero-exponent result is one.
4. **N.4 — Truncated subtraction.** Compute three minus five and five minus three. Reference: `monusExample`; the two answers expose the truncation rule.
5. **N.5 — Carry and conversion.** Implement increment and both conversions, then check the five smallest values and eleven's successor. References: `inc`, `toBin`, `fromBin`, `binaryExamples`, `binaryValues`, `carryExample`.

The solution definitions above are included from the compiled source. Try each exercise before inspecting its named solution. Change a claimed numerical result locally and recheck: the wrong equality must be rejected.

## References and adaptation {#references}

Adapted from [PLFA Naturals](https://plfa.github.io/Naturals/) by Philip Wadler, Wen Kokke, and Jeremy G. Siek, CC BY 4.0; upstream freeze `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`. Idris supplies the inductive `Nat` and numeric notation; the arithmetic and binary algorithms are defined here. Agda-specific pragmas and editor keystrokes are replaced by Idris's totality and checking workflow. This is an independent adaptation.

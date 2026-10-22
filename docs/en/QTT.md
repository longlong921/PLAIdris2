# QTT · Which information survives execution?

## Motivation {#motivation}

A vector's type records its length. Must every compiled vector also carry an extra natural number? A proof can use an index to describe a value without requiring the index itself at run time. Idris2 makes this distinction explicit through quantities. It also offers a way to require a resource to be consumed once.

These are host-language features. They affect how we implement and check the book, but they do not silently turn the simply typed object language of Part 2 into a linear language.

## Erased, linear and unrestricted parameters {#model}

An argument annotated `0` cannot be read as run-time data. An argument annotated `1` must be used once in the relevant linear computation. An ordinary explicit argument has unrestricted use. Automatically introduced implicit parameters are normally erased; if a program needs the index at run time, we must make that need explicit. See the [official multiplicity reference](https://github.com/idris-lang/Idris2/blob/v0.8.0/docs/source/tutorial/multiplicities.rst).

{{include:src/PLFA/Extensions/QTT.idr#erasure}}

`storedLength` receives an unrestricted implicit `n`; it can return that argument immediately. The vector itself need not be traversed. `countSpine` receives an erased `n`; it returns a number by traversing the *vector*, whose constructors remain available. Its patterns refine the erased index along with the observed vector shape. They do not perform a run-time inspection of the erased number alone.

That last distinction explains a common error. If the implementation were only “return `n`” while `n` had quantity zero, it would try to recover data that is not present. The separate `ErasedRuntime` negative test asks the compiler to reject precisely that mistake.

## A resource passed once {#examples}

{{include:src/PLFA/Extensions/QTT.idr#linear}}

`linearIdentity` consumes its input once by returning it. `LinearPair` stores two linear fields. To swap such a pair, pattern matching consumes the outer pair and passes each field once to the new constructor. `mapOnce` consumes its function by applying it once, and consumes its argument in that application.

Read these signatures as resource protocols, not as timing promises. “Once” does not mean one processor instruction, nor does it imply that all functions are linear. For a concrete example, `swapOnce (PairOnce 4 9)` produces `PairOnce 9 4`; it neither invents nor duplicates an input field.

## Correctness is a separate question {#theorems}

`countCorrect` proves that traversing a vector recovers the length appearing in its type. In the empty case both are zero. In the cons case the induction hypothesis concerns the tail, and `cong S` turns equality of tail lengths into equality of successor lengths. The proof makes an arithmetic correctness claim. Quantities alone would not have proved that claim.

The theorem is allowed to mention erased indices because they are available to type checking. The executable algorithm still obtains its result from the vector spine. This is a useful pattern throughout the book: type-level information can constrain code even when the runtime representation omits that information.

## Common pitfalls {#pitfalls}

* Implicit and erased are related defaults, not synonyms. An explicit `{n : Nat}` can make an implicit index available at run time; `(0 n : Nat)` is explicit but erased.
* A proof needed to guide runtime branching may itself need a nonzero quantity. Do not indiscriminately mark every evidence argument `0`.
* Linearity of a field is interpreted relative to how its enclosing value is consumed. An unrestricted argument is not made linear merely because its constructor has a linear field.
* A linearity error does not justify duplicating a value through an unsafe cast. Redesign the interface or supply a resource that really permits duplication.

## Exercises and reference solutions {#exercises}

1. Explain why the length of `[4, 5, 6]` is available even when the length argument is erased, then give the equality proof. Reference: `countThree`.
2. Prove that swapping twice returns the original linear-pair value. Explain why the theorem's parameter is unrestricted although `swapOnce` accepts a linear input. Reference: `swapOnceTwice`.

{{include:src/PLFA/Extensions/QTT.idr#exercises}}

The first proof reduces `countSpine` over the three cons constructors. In the second proof, the theorem describes an equality of values; after exposing the pair, both sides compute to the same constructor application. This specification does not promise a resource-consuming theorem interface. The runtime function `swapOnce` has the resource-sensitive interface.

## Further reading {#references}

The [Idris2 0.8.0 documentation source](https://github.com/idris-lang/Idris2/tree/v0.8.0/docs/source) fixes the version of the host-language explanation. [Trust](Trust.md) separates accepted quantity/type/totality checks from the mathematical properties proved about our object languages.

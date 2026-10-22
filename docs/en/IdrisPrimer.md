# Idris2 Primer · Reading the notation

This extension is a companion to the original chapter sequence. It introduces the pieces of Idris2 notation used throughout the book; it does not replace [Naturals](Naturals.md) or [Equality](Equality.md).

## Motivation {#motivation}

A theorem prover can feel mysterious if you read its syntax as a collection of magic commands. In this book a proof is an ordinary definition with a precise result type. Constructors introduce evidence, pattern matching analyses evidence, and recursive calls provide induction hypotheses. Learning to identify those three operations makes most of the notation readable.

We will start with familiar functions, then change what their result types say. You need only lists, pairs, and the idea of recursion.

## Definitions and their types {#model}

{{include:src/PLFA/Extensions/IdrisPrimer.idr#definitions}}

`twice : Nat -> Nat` is a type declaration. The following two equations cover the two ways to build a natural number: `Z` and `S k`. In the successor branch the recursive input is `k`, a smaller piece of `S k`. Idris checks that the cases cover the inputs and that recursion decreases. `%default total`, at the top of the source file, makes this requirement apply to every definition unless explicitly changed; our reference source does not weaken it.

`Vect n a` is a list of elements of type `a` whose length is recorded in the type as `n`. The type of `mapVector` says that mapping preserves that index. It does not say that mapping preserves the values: `f` can change every element. In the empty case the length is zero; in the cons case the result has the same successor length as the input.

The names `n`, `a` and `b` in this signature are implicit parameters. A call usually infers them from the arguments. Curly braces make such a parameter explicit when inference needs help. Parentheses around an argument instead make it a normal explicit argument. `public export` makes a definition and its implementation available to importing modules; a proof may need to reduce that implementation while checking equality.

## Read a small example {#examples}

To evaluate `twice 3`, remember that `3` abbreviates `S (S (S Z))`. Each step peels off one `S` from the input and adds two to the output. After three recursive calls, the base case contributes `Z`, leaving six successors. This is computation by the defining equations, not a numerical oracle.

For `mapVector (\x => x) [2, 5]`, the lambda expression `\x => x` is the identity function. Pattern matching reveals the first element, preserves it, and recurses over the one-element tail. The resulting vector is `[2, 5]`. The proof below makes this observation work for *every* vector, including vectors whose length and elements are not known yet.

## Propositions as result types {#theorems}

{{include:src/PLFA/Extensions/IdrisPrimer.idr#proofs}}

The result of `twiceThree` is an equality type. `Refl` works because both sides compute to the same expression. Compare `mapIdentity`: an unknown vector cannot be reduced by inspecting its name, so we split into constructors. The empty case computes directly. In the cons case the recursive proof identifies the two tails; `cong (x ::)` lifts that equality through the operation of attaching the same head.

`swapTwice` needs no induction because a pair has one constructor and no recursive tail. After exposing its two fields, both swaps compute. A proof's shape follows the data it analyses; not every theorem about a data type needs a recursive proof.

These theorems return pointwise equalities for their explicitly quantified inputs. We have not postulated that any two functions giving equal answers are themselves equal as Idris values. That distinction becomes useful in [Isomorphism](Isomorphism.md).

## Common pitfalls {#pitfalls}

* A type signature is a goal, not a proof. The implementation must inhabit it.
* A lowercase name appearing only in a signature may be implicitly bound. When referring to a particular definition in a type, qualification such as `Module.name` can prevent an unintended new parameter.
* `Refl` does not prove arbitrary equations by algebra. It uses definitional computation. A symbolic right-identity law often needs induction even when the corresponding left-identity law computes immediately.
* `impossible` is for a constructor pattern the type checker can rule out. It is not a way to dismiss an awkward case. The negative suite checks that false claims do not silently pass.

## Exercises and reference solutions {#exercises}

1. Prove that mapping `g` and then `f` over a vector agrees with one traversal using their composition. State the theorem for arbitrary element types and arbitrary vector length. Identify the constructor through which you lift the induction hypothesis. Reference: `mapCompose`.
2. Prove that doubling a successor gives two successors of the doubled predecessor. Does this require induction? Explain why it differs from a theorem about an argument that the function does not inspect. Reference: `twiceSuccessor`.

{{include:src/PLFA/Extensions/IdrisPrimer.idr#exercises}}

For exercise 1, the shared head is `f (g x)`, while the tail equality comes from the recursive call. For exercise 2, the left side unfolds by a defining equation for any `n`, so the proof is `Refl` without inspecting `n`.

## Further reading {#references}

The [Idris2 tutorial](https://idris2.readthedocs.io/en/latest/tutorial/index.html) documents the host language. This book uses version 0.8.0; follow the locked toolchain when reproducing examples. Continue with [QTT](QTT.md) when an implicit argument is available in a type but unavailable at run time.

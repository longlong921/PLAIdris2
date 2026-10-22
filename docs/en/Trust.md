# Trust · The object language and the host

## Motivation {#motivation}

“This proof passed Idris” is useful information, but it is incomplete. Which proposition was checked? Which definitions give that proposition its meaning? Which implementation did the checking? A careful account keeps three layers separate: the object language described by our data, the mathematical metatheory stated about that data, and the Idris compiler that checks the implementation.

We use a deliberately tiny machine to separate these layers before returning to the full lambda calculus. This extension's machine supplements the main development; it does not replace any theorem about lambda terms.

## A language that can keep running {#model}

{{include:src/PLFA/Extensions/Trust.idr#machine}}

`Halt` has no transition. `Spin` has a transition back to itself. A `Trace n before after` records exactly `n` steps. Its constructors describe *finite evidence*. For every natural `fuel`, `spinFor fuel` constructs a trace of that many steps from `Spin` back to `Spin`.

The definition `spinFor` is total because its host recursion decreases on `fuel`. The described machine does not terminate: whatever finite number of steps we inspect, another `Again` step is available. There is no contradiction between these statements. One concerns constructing a bounded description; the other concerns executing the described system without a bound.

## Fuel is a budget, not a proof of divergence {#examples}

{{include:src/PLFA/Extensions/Trust.idr#observations}}

`runFor 4 Spin` consumes four units and returns `OutOfFuel`. `runFor 0 Halt` returns `Finished`, because the machine is already done. For this particular machine we can prove `spinExhausts` for *every* fuel value. By contrast, a single timeout for an arbitrary lambda term does not establish divergence: a larger budget might reach a result.

In [Untyped](Untyped.md), `Ω` is a concrete lambda term with a self-step. [BigStep](BigStep.md) separately proves that it has no finite call-by-name evaluation derivation. That proof, not an arbitrary timeout, establishes the relevant absence of convergence. [Confluence](Confluence.md) concerns joining finite full-beta paths and is compatible with this example.

## What the checks establish {#theorems}

The source proof `spinExhausts` is structural induction on the budget. `haltFinishes` follows directly from the defining equation. Neither theorem says that our proof checker is correct. The trust chain for this book includes elaboration, type conversion, coverage and termination checking, imported libraries, and the compiler implementation. Running compiled examples additionally depends on code generation and the chosen runtime.

Idris2 0.8.0's own [versioned FAQ](https://github.com/idris-lang/Idris2/blob/v0.8.0/docs/source/faq/faq.rst) describes its universe implementation as `Type : Type`. Consequently, acceptance by this compiler is not the same assurance as a formalisation in a sound predicative universe hierarchy. Avoiding explicit escape hatches and requiring totality does not repair that global foundational limitation. We make no claim to prove consistency of the host, and we do not exploit the universe limitation to manufacture proofs.

The development instead offers inspectable constructive proof programs in a disciplined fragment, checked by an exact compiler version. A reader can examine the definitions and the structural arguments independently. An upstream theorem is not automatically transferred merely by reusing its name; the translated proposition and implementation must be reviewed.

The automated suite checks for unfinished holes and prohibited trust escapes, compiles all reference modules, executes examples, and demands rejection of deliberately invalid proofs. It also verifies chapter structure, included source hashes and local links. These tests catch concrete classes of mistakes. They are not a proof of the test runner's completeness or of the compiler's metatheory.

## Common pitfalls {#pitfalls}

* Progress and preservation establish a form of safety. With general recursion they do not establish termination.
* A big-step relation describes successful finite evaluations. Merely failing to build a derivation is not a divergence proof; a refutation must rule out every possible finite derivation.
* Confluence does not mean one-step determinism, and neither property by itself promises normalization.
* A well-typed host representation does not make a wrongly stated object-language rule mathematically appropriate. Definitions must be reviewed along with their theorems.
* A rejected proof only provides useful negative-test evidence when it fails for the intended reason, not because the compiler executable or an import is missing.

## Exercises and reference solutions {#exercises}

1. Prove that `Halt` has no outgoing step. Which constructor would a hypothetical transition have to use, and why does its source index make that impossible? Reference: `noHaltStep`.
2. Prove that every finite trace beginning at `Spin` also ends at `Spin`. Explain why this result does not require running an infinite computation. Reference: `traceStaysSpin`.

{{include:src/PLFA/Extensions/Trust.idr#exercises}}

For exercise 1, `Again` always starts at `Spin`, so it cannot match the given source index `Halt`. For exercise 2, recurse on the finite trace: `Stop` preserves its endpoint, and `Next Again` leaves a smaller trace beginning at `Spin`.

## Further reading {#references}

Consult the [Idris2 FAQ](https://idris2.readthedocs.io/en/latest/faq/faq.html) for implementation limitations, and [PLFA](https://plfa.github.io/) for the original Agda development. The repository's `evidence/` directory records what was actually run for this edition; [Getting Started](GettingStarted.md) gives the commands for testing your own checkout.

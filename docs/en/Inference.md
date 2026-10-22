# Inference: a bidirectional checker with evidence {#inference}

## Motivation {#motivation}

A typing relation describes valid derivations, but it does not automatically
give an algorithm for finding one. For an unannotated lambda, the checker
cannot read the argument type from the syntax. For an application, however,
knowing the function's type tells us both what argument type to require and
what result type to return.

Bidirectional typing turns this asymmetry into two cooperating tasks:
**synthesize** a type from an expression, or **check** an expression against a
given type. We implement both as total decision procedures. Success returns a
real derivation. Failure returns a function showing that any proposed
derivation would be contradictory. The result is more informative than a
Boolean or `Maybe Ty`.

The algorithm accepts scoped syntax with `Fin` variables and a matching
context vector. It is not a text parser or a named-variable resolver. An
unbound name is excluded before this interface, because there is no out-of-
range `Fin` value. Type errors within well-scoped input remain possible and
are genuinely decided here.

## Model {#model}

### Two modes and two switches {#syntax}

The syntax is mutually defined. `SynthTerm` contains variables, applications,
and annotations. `CheckTerm` contains lambda, zero, successor, natural case,
fixpoint, and an embedding of a synthesizing term.

{{include:src/PLFA/Part2/Inference.idr#syntax}}

| Form | Mode | Information flow |
| --- | --- | --- |
| Variable | synthesize | read the type from the context |
| Application | synthesize | infer the function; check the argument at its domain |
| Annotated term | synthesize | check at the annotation, then return that type |
| Lambda | check | split the expected arrow into domain and codomain |
| Zero, successor | check | require `TNat` |
| Case | check | infer a natural scrutinee; check both branches at the expected result |
| Fixpoint | check | give the recursive variable the expected result type |
| Embedded synthesizing term | check | synthesize, then compare with the expected type |

`Annotate` switches from checking syntax to synthesizing syntax. `Embed`
switches back. A lambda needs no annotation when it is already being checked
against an arrow. A top-level lambda that must synthesize can be given one
annotation around the whole term.

### The judgements {#judgements}

`Synth gamma t a` and `Check gamma t a` are separate evidence types matching
these modes. In `ChEmbed`, the synthesized type is connected to the expected
type by an explicit equality proof. The application rule has no arbitrary
search over argument types: its function premise already supplies the domain.

{{include:src/PLFA/Part2/Inference.idr#judgements}}

The domain parameter of `SyApp` and synthesized type parameter of `ChEmbed`
are retained as computational implicit arguments. This matters for Idris:
in a failure proof we may need to reconstruct an existential package containing
that type. The context and syntax indices themselves remain erased. Retaining
this evidence is an implementation choice, not an extra typing premise.

## Worked examples {#examples}

`identityTwo` annotates the identity function with ℕ → ℕ and applies it to two.
The annotation tells the lambda to check its body at `TNat`; its variable
synthesizes `TNat`, and `Embed` verifies the equality. The argument two checks
structurally without needing another annotation.

{{include:src/PLFA/Part2/Inference.idr#examples}}

For recursive addition, the single outer annotation supplies ℕ → ℕ → ℕ.
`CFix` puts that type in the context, the two lambdas each receive a domain,
and the case checks both branches at the expected natural result. Inside the
successor branch the context order is predecessor, second argument, first
argument, recursive function. Thus the earlier arithmetic program can be
reconstructed with mode switches but without annotating every variable or
subexpression.

`plusAccepted` checks that synthesizing the application to two and two returns
success. The hand-written `identityTwoDerivation` is a separate readable
example of the judgement; the general algorithm does not depend on that
particular proof.

## Correctness of the algorithm {#theorems}

### Type equality and synthesis uniqueness {#uniqueness}

`typeEqual` decides equality of simple types recursively. Different outer
constructors are contradictory. For arrows, compare domains and codomains;
if either differs, any equality of the full arrows would yield an impossible
equality of that component.

`synthUnique` says that two synthesis derivations for the **same scoped term
in the same context** return equal types. The application case applies the
induction hypothesis to the functions and extracts equality of codomains.
Annotations fix the result type directly. This does not assert unique typing
for the erased raw language: identity can check at many arrow types.

{{include:src/PLFA/Part2/Inference.idr#equality}}

### Decisions with genuine failure evidence {#decision}

`synthesize` returns `Dec (a : Ty ** Synth gamma t a)`. `check` returns
`Dec (Check gamma t a)`. The functions recurse mutually on subexpressions,
including the bodies of binders with their extended contexts.

{{include:src/PLFA/Part2/Inference.idr#decision}}

The application's failure branches explain why uniqueness matters:

1. If function synthesis fails, any successful application derivation would
   contain a function derivation, contradicting that failure.
2. If the function synthesizes `TNat`, a successful application would give it
   an arrow type. `synthUnique` and `natNotArrow` rule that out.
3. If the function synthesizes an arrow but the argument fails to check,
   another proposed application derivation might mention a differently named
   domain. Uniqueness proves the domains equal; `convertCheck` transports its
   argument derivation to the rejected type, yielding the contradiction.

The embedding case uses the same pattern: a rejected equality cannot be
escaped by choosing some other synthesis derivation, because synthesis is
unique. These are proofs of failure, not unexplained `Nothing` branches.

### Soundness, elaboration, and erasure {#soundness}

The mutual erasure functions remove annotations and mode switches, leaving
the raw syntax of [Lambda](Lambda.html). `synthSound` and `checkSound`
transform every bidirectional derivation into an external `HasType`
derivation for that erased term. Constructor cases rebuild the corresponding
typing rule; the embedding equality is eliminated by matching `Refl`.

{{include:src/PLFA/Part2/Inference.idr#soundness}}

`elaborateSynth` and `elaborateCheck` then use the general correspondence from
[DeBruijn](DeBruijn.html#correspondence) to produce intrinsic terms.
`synthErasure` and `checkErasure` prove that forgetting those terms gives the
same raw syntax as direct annotation erasure. Thus the successful checker
provides an executable typed program with a checked connection to the input.

### What completeness means here {#completeness}

A `No` result already refutes every derivation of the queried judgement.
`synthesizeComplete` and `checkComplete` make the consequence explicit:
whenever a synthesis or checking derivation exists, the corresponding
procedure's success indicator is `True`. The impossible failure case is
eliminated by applying its refutation to the supplied derivation.

{{include:src/PLFA/Part2/Inference.idr#completeness}}

Completeness is relative to **these bidirectional judgements and these
annotations**. It is not the claim that every annotation on an otherwise
typable raw program will be accepted. In particular, annotating zero with an
arrow type must fail, even though the erased zero has type `TNat`. Exercise
three checks both facts.

### From input to a computed result {#execution}

`inferredTerm` runs synthesis on the addition example and retains a natural-
typed intrinsic result. `inferredTermCorrect` identifies it with the earlier
intrinsic addition program. `inferredComputed` transports that equality
through the fuelled evaluator and checks the resulting `Just 4`.

{{include:src/PLFA/Part2/Inference.idr#execution}}

The two-stage proof makes the connection between compilation and execution
visible. It uses the already-proved soundness and intrinsic evaluator; it does
not introduce a second unverified interpreter for the annotated syntax.

## Pitfalls {#pitfalls}

- Checking and synthesis are different interfaces. An unannotated lambda is
  checking syntax, not a synthesis case that the implementation forgot.
- A successful check returns a derivation, and a failed check must refute one.
  Returning a bare Boolean would lose both guarantees.
- Synthesis uniqueness is for the bidirectional term, including annotations.
  It is not a principal-type theorem for unannotated raw terms.
- Scoped variables remove name-resolution errors from the input datatype;
  they do not remove type errors such as applying zero.
- Type equality compares syntax of simple types. No subtyping or implicit
  coercion is part of this language.
- Successful typing does not imply terminating evaluation: `CFix` retains
  general recursion, just as in the previous chapters.

## Exercises and checked solutions {#exercises}

1. **Checking identity.** For any type `a` and any context, derive that the
   checking identity has type a → a. Explain why this does not violate
   synthesis uniqueness.
2. **Reject every result type.** Prove that zero annotated as natural and
   applied to zero cannot synthesize any type. Also check the algorithm's
   failure indicator.
3. **Annotations matter.** Annotate zero with an arrow. Check that synthesis
   rejects it while its erased raw term still has natural type. State the
   completeness claim that survives this example.

{{include:src/PLFA/Part2/Inference.idr#solutions}}

The solutions are `identityAt`; `badApplicationImpossible` and `badRejected`;
and `annotationRejected` with `erasureStillTyped`. The last pair is a useful
boundary test: a sound checker must respect an annotation rather than silently
replace it with a convenient type.

## References and adaptation {#references}

Based on [PLFA, Inference](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/Inference.lagda.md)
by Philip Wadler, Wen Kokke, and Jeremy G. Siek, at frozen commit
`1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The upstream synthesis/inheritance distinction is retained; the checking
function is named `check`. Named lookup is replaced by `Fin` and context-vector
lookup, with scope checking outside this interface. Both decisions, their
negative proofs, uniqueness, judgement-relative completeness, external
soundness, intrinsic elaboration, and erasure consistency are implemented and
checked with Idris2 0.8.0. Product and other extended-language inference rules
are not claimed here.

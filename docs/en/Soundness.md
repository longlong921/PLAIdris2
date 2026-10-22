# Soundness {#soundness}

## Motivation {#motivation}

Evaluation changes a program's syntax. Soundness says that it preserves the program's mathematical meaning. For the untyped lambda calculus, the precise claim is stronger than “both programs return the same answer”: every finite piece of information about either program is also information about the other, in every environment.

There are two directions. **Preservation** transports information from a redex to its reduct. **Reflection**, also called subject expansion, transports it back. A proof of only preservation would allow reduction to create new information. We need both directions before we may replace one expression by the other inside arbitrary programs.

The terms here are the full untyped terms from Untyped. A step may contract a beta redex, reduce either side of an application, or reduce inside an abstraction. No normalization hypothesis, evaluation strategy, or typing derivation appears in the theorem.

## Model {#model}

A term `Tm n` has `n` available de Bruijn variables. An environment `Env n` supplies each variable with a finite information value. Values are `Bottom`, `Arrow a b`, and `Join a b`. `Denote gamma term v` is evidence that `v` approximates `term` in `gamma`. It is a relation with finite proof trees, not a function that executes every lambda term.

`SemEq left right` is pointwise equivalence of those judgments: for each environment and value, there is a function transporting evidence in each direction. This avoids any assumption of function extensionality. The information order and the semantic rules, including arrow contravariance and distribution over joins, are those of Denotational.

Substitution replaces variables by terms. To preserve meaning, those replacement terms must supply the information assigned by the original environment. `SubDenote delta sigma gamma` states exactly this variable by variable. Under a lambda, the new variable keeps its assigned information, while old replacement terms are shifted past the binder.

{{include:src/PLFA/Part3/Soundness.idr#substitution-preservation}}

The induction in `substPres` follows the semantic derivation. The variable case uses the supplied variable evidence; application, join, and subsumption rebuild the same semantic rule. Abstraction extends both environments and the substitution. `substitution` is the single-variable instance needed for beta reduction.

## Worked examples {#examples}

Consider `(lambda x. x) A`. Its finite interpretation comes from a function approximation `Arrow a b` for the identity and information `a` about `A`. Lambda inversion gives the body judgment under the environment extended by `a`; substitution then gives the same result information `b` for `A`.

Now consider `(lambda x. lambda y. y) Omega`. Its beta reduct is the identity even though `Omega = (lambda x. x x) (lambda x. x x)` does not converge. Reflecting information about the identity requires no information about the unused argument: `Bottom` suffices. This is why reflection must allow a bottom environment.

For `(lambda x. x x) A`, the same argument occurs twice. A finite proof may use `Arrow a b` at the function occurrence and `a` at the argument occurrence. Reflection records their combined demand `Join (Arrow a b) a`. It does not require the two occurrences to start with identical approximations.

The final example reduces under a binder: `lambda z. ((lambda x. x) z)` reduces to `lambda z. z`. `underLambdaMeaning` certifies equality for this full beta step, even though weak call-by-name evaluation would stop immediately at the outer lambda.

## Theorems and proof structure {#theorems}

### Preservation {#preservation}

The beta case uses lambda inversion followed by the substitution theorem. The congruence cases recurse into the subderivation corresponding to the reduced subterm. Bottom, join, and subsumption remain valid after any step.

{{include:src/PLFA/Part3/Soundness.idr#preservation}}

### Recovering a finite demand {#finite-demand}

Reflection has to reconstruct information about an argument that has disappeared through substitution. We first undo renaming. A variable derivation may have ended with joins or subsumption, so its inversion lemma yields an information inequality, rather than merely inspecting the final constructor.

{{include:src/PLFA/Part3/Soundness.idr#renaming-reflection}}

`substReflect` takes a finite derivation for a substituted term and produces an environment `gamma` together with two proofs: the original term has the desired information in `gamma`, and every substituted variable supplies the information `gamma` requests.

For a variable, `oneEnv` records the requested value at that variable and bottom elsewhere. For an application or a join, the two recursive calls may request different environments. Taking their pointwise join supplies both demands; environment monotonicity transports the two derivations into that common environment. For a lambda, the recovered demand on the fresh variable is below the lambda's input information. We may therefore increase it to that input and remove the binder from the remaining environment. Environment equality is used only pointwise.

{{include:src/PLFA/Part3/Soundness.idr#finite-demand}}

The single-substitution corollary extracts one finite value `a` such that the argument denotes `a` and the original body denotes the result under an environment extended by `a`. This existential value is the missing ingredient for rebuilding the original beta redex.

### Reflection and equality {#reflection}

`reflectBeta` combines the recovered argument and body derivations with the lambda and application rules. `reflect` then handles reduction inside any syntactic constructor, including under a lambda.

{{include:src/PLFA/Part3/Soundness.idr#reflection}}

`stepSoundness` pairs preservation and reflection. `soundness` composes those pairs along a finite reduction sequence. Its endpoint is an arbitrary term; the familiar statement for a sequence ending at a lambda is a special case.

{{include:src/PLFA/Part3/Soundness.idr#soundness}}

## Pitfalls {#pitfalls}

- Subject expansion is a property of this finite-information interpretation. It is generally false for ordinary simple typing: an ignored argument can be untypable even when the reduct is typable.
- `Bottom` carries no termination evidence. It is available for every term, including a looping term.
- A finite semantic derivation may request a finite join of many argument observations. Choosing only one occurrence's demand loses information and breaks reflection.
- Soundness does not say every reduction terminates, nor that every two denotationally equal terms have a common normal form.

## Exercises and checked solutions {#exercises}

1. **S1 — Beta replacement.** State semantic equality for an arbitrary open body and argument, without assuming termination of either. Identify where the reverse direction obtains a shared argument approximation. Reference solution: `betaMeaning`; its use of `stepSoundness` includes the finite-demand construction above.
2. **S2 — An unused argument.** Prove that applying `lambda x. lambda y. y` to any argument has the meaning of the identity. Explain why the proof still applies to `Omega`. Reference solution: `ignoredArgumentMeaning`.
3. **S3 — Reduction under a binder.** Prove that `lambda z. ((lambda x. x) z)` has the meaning of `lambda z. z`. Explain why this is a full beta reduction theorem rather than a weak evaluation rule. Reference solution: `underLambdaMeaning`.

{{include:src/PLFA/Part3/Soundness.idr#exercises}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA: Soundness](https://plfa.github.io/Soundness/), frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. This independent Idris2 adaptation replaces Agda contexts with intrinsically scoped `Fin` indices and performs environment comparison pointwise. The name `soundness` covers arbitrary endpoints by iterating upstream's general `reduce-equal` theorem; upstream uses the name `soundness` for its lambda-endpoint special case. All displayed code is included from the checked source; the review record documents the exact compiler check.

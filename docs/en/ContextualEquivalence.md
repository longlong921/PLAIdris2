# Contextual equivalence {#contextual-equivalence}

## Motivation {#motivation}

A compiler optimization replaces part of a larger program. Knowing that two expressions happen to converge when run alone is insufficient: the surrounding program may apply them to arguments, put them under binders, or use them as arguments to another function. A valid replacement must preserve the observation in every permitted surrounding program.

Contextual equivalence expresses this requirement directly. It quantifies over all closing contexts and asks whether each resulting closed program converges. That definition is demanding to prove from scratch. The purpose of the preceding semantic development is to provide a compositional route: prove equality of meanings for the two expressions, then obtain contextual equivalence for free.

## Model {#model}

A `Ctx n 0` is a single-hole syntactic context that accepts a term with `n` variables and produces a closed term. Its constructors are the hole, a lambda around a context, an application with the context on the left, and an application with the context on the right. Plugging is scope-correct by construction. Closing binders may bind variables of the inserted open term; the indices specify exactly which ones.

`ContextuallyEquivalent left right` gives two evidence transformations for **each** closing context: convergence after plugging the left implies convergence after plugging the right, and conversely. It does not decide convergence or divergence. If one side cannot converge, the appropriate implication also rules out convergence of the other.

The module also defines `Terminates`, existence of a full beta reduction to a lambda, and `BetaContextuallyEquivalent`, the corresponding contextual observation. Adequacy proved that these two observations coincide for closed terms. Keeping both definitions visible makes the difference between a reduction relation and a particular evaluation strategy explicit.

{{include:src/PLFA/Part3/ContextualEquivalence.idr#observations}}

## Worked examples {#examples}

For every open body and argument, `(lambda x. body) arg` may be replaced by its capture-avoiding beta reduct. The proof is not restricted to evaluating at the top level: `betaReplacement` quantifies over all closing contexts, including contexts that put the expression under a lambda or in an argument position.

`openBetaReplacement` specializes this to the open expression `(lambda x. x) #0` and the variable `#0`. The context `closingBinder` binds that variable, producing the closed programs `lambda z. ((lambda x. x) z)` and `lambda z. z`. Contextual equivalence covers this deliberate binding; it is not an accidental capture in a faulty substitution function.

An ignored argument gives a useful optimization example. `(lambda x. lambda y. y) A` can be replaced by the identity in every context, even when `A` diverges. Soundness accounts for the missing argument through bottom information. The theorem is about the pure call-by-name language defined here; it does not authorize discarding effects in an unrelated language.

The last example shows why specifying the observation matters. The eta expansion `lambda x. Omega x` is a lambda and therefore converges immediately. `Omega` does not converge. The empty context alone distinguishes them. A general eta rule would therefore be unsound for this weak-head observation.

{{include:src/PLFA/Part3/ContextualEquivalence.idr#examples}}

## Theorems and proof structure {#theorems}

Take a semantic equality of open expressions `left` and `right`, and fix any closing context. Compositionality lifts the equality to the two plugged closed programs. If the first converges, it has information `Arrow Bottom Bottom` by soundness and the evaluation-to-reduction theorem. The lifted semantic equality transfers that arrow information to the second. Adequacy then supplies its call-by-name convergence witness.

That is `denotEqualConverges`. It uses the evidence transformation `equalPreservesConvergence` from Adequacy; that helper contains exactly the soundness-and-adequacy argument just described. Reversing the semantic equality proves the converse implication. `contextualEquivalence` packages both directions for the arbitrary context.

{{include:src/PLFA/Part3/ContextualEquivalence.idr#replacement}}

For the full beta formulation, `denotEqualTerminates` first converts an existing lambda-reaching reduction into call-by-name convergence. After transferring convergence through the context's semantic equality, it converts the new evaluation witness back into a beta sequence. `betaContextualEquivalence` again pairs this map with its symmetric version. No reduction strategy is assumed in the input sequence.

The dependence between the results is worth spelling out. Compositionality handles the surrounding syntax; soundness turns an existing operational success into finite semantic information; adequacy turns that information into operational success for the replacement. Omitting adequacy would leave the final step unjustified. Omitting reflection from soundness would lose the backward transport from the observed result to the original program.

## Pitfalls {#pitfalls}

- Equality of top-level convergence alone is too weak. Two lambdas both converge immediately, but a context can apply them and distinguish their behavior.
- The quantified contexts close the program. The theorem covers open expressions through those contexts, without pretending that a free variable is a closed executable program.
- The observation is existence of a lambda result, not the same printed lambda body or the same number of reduction steps.
- The theorem proves semantic equality implies contextual equivalence. It does not prove the converse, often called a full abstraction property.
- Beta replacement is justified. Unrestricted eta replacement is not: `etaNotContextual` supplies a checked counterexample for this precise observation.

## Exercises and checked solutions {#exercises}

1. **C1 — Replace beneath a lambda.** Prove contextual equivalence of `lambda z. ((lambda x. x) z)` and `lambda z. z`, including their use inside any further closing context. Reference solution: `underBinderReplacement`. Generalize the argument to any finite full beta reduction using `reduceReplacement`.
2. **C2 — Compose optimizations.** If `left` is contextually equivalent to `middle`, and `middle` to `right`, prove contextual equivalence of `left` and `right`. Compose evidence separately in the two directions at each context. Reference solution: `contextualTransitive`; `contextualReflexive` and `contextualSymmetric` complete the equivalence-relation laws.
3. **C3 — Reject unrestricted eta.** Use the hole context to show that `Omega` and `lambda x. Omega x` are not contextually equivalent. An alleged equivalence would transport convergence of the latter back to `Omega`, contradicting `omegaNoEval`. Reference solution: `etaNotContextual`.

{{include:src/PLFA/Part3/ContextualEquivalence.idr#exercises}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA: ContextualEquivalence](https://plfa.github.io/ContextualEquivalence/), frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. Upstream states contextual equivalence using full beta reachability of a lambda. This adaptation proves that statement as `betaContextualEquivalence` and additionally exposes the equivalent substitution-based weak call-by-name formulation as `contextualEquivalence`. Both quantify over arbitrary well-scoped closing contexts. The eta counterexample and the explicit equivalence-relation exercises are additions; no converse from contextual equivalence to semantic equality is claimed.

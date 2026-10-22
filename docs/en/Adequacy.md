# Adequacy {#adequacy}

## Motivation {#motivation}

Soundness says that reduction preserves meaning. Adequacy connects meaning back to an observable computation: a closed term with finite function information actually converges to a lambda by weak call-by-name evaluation. This is not a theorem that every lambda term terminates. It is a theorem whose semantic premise supplies exactly the evidence needed for convergence.

We observe reaching an outer lambda. We do not evaluate its body before reporting success. Thus `lambda x. Omega` converges in this sense although its body diverges. On the other hand, `Omega` itself has no such result. This observation is the one used in ContextualEquivalence.

## Model {#model}

`Converges term` packages a body and a finite `Eval term (Lam body)` derivation. `Eval` is the substitution-based weak call-by-name relation from BigStep: a lambda evaluates to itself; an application first evaluates its function, then evaluates the body with the original, unevaluated argument substituted. The term is closed, so the final body has one bound variable available and no free variables.

`HasFunction term` packages an arrow approximation `Arrow a b` together with its semantic derivation in the empty environment. The input and output approximations are arbitrary finite values. In particular `Arrow Bottom Bottom` is already enough: it records that the term is a function without demanding any behavior from its body.

{{include:src/PLFA/Part3/Adequacy.idr#observation}}

Neither predicate is a decision procedure. A member is finite evidence. Their equivalence lets us transform such evidence in either direction, but does not decide which predicate holds for an arbitrary term.

## Worked examples {#examples}

The identity has information `Arrow Bottom Bottom`: under a lambda we may use the bottom rule for the body. `functionConverges` turns this semantic evidence into an actual evaluation derivation. The same argument proves convergence of `lambda x. Omega`, because weak evaluation does not enter that body.

Consider `(lambda x. lambda y. y) A`. The inner lambda supplies `Arrow Bottom Bottom`; the outer lambda supplies `Arrow Bottom (Arrow Bottom Bottom)`; the argument supplies `Bottom`. The application rule therefore yields function information for the entire application. `constantIgnoresArgument` proves convergence for **every** closed argument, including `Omega`.

Every term has information `Bottom`, including `Omega`. Consequently bottom alone must not imply convergence. `bottomIsNotEnough` constructs the bottom judgment, while `omegaHasNoFunction` proves that any hypothetical arrow judgment for `Omega` leads to a contradiction. It uses BigStep's `omegaNoEval`: any evaluation of this self-reproducing application would contain a strictly smaller evaluation of itself. The proof eliminates finite evaluation derivations; it does not run an infinite evaluator.

## Theorems and proof structure {#theorems}

### A relation that remembers function behavior {#logical-relation}

Proving only “an arrow implies some lambda result” gives too weak an induction hypothesis for application. After obtaining the function's lambda body, we must know that applying it to an appropriate argument realizes the expected output information. `Realizes` records both facts.

- `Realizes Bottom term` imposes no requirement.
- Realizing a join means realizing both components for the same term.
- Realizing an arrow means the term evaluates to a particular lambda, and its body, when applied to any term realizing the input, realizes the output.

The definition recurses on finite information values, even though the terms being related may diverge. It is a type-valued function, so the function argument in the arrow clause is justified by structural recursion on the smaller input value; we do not add a negatively recursive datatype.

{{include:src/PLFA/Part3/Adequacy.idr#logical-relation}}

`realizesExpansion` changes the term whose evaluation we follow while keeping the resulting lambda and its behavior. In the application case, it prefixes an evaluation of the function to an evaluation of the substituted body.

`realizesDown` proves compatibility with **all** information-order rules. For arrows, the input is contravariant: stronger input evidence is weakened before invoking the available function behavior; the output evidence is then weakened to the requested output. The distribution rule is the subtle case. Two approximations of one function may initially carry two lambda witnesses. Evaluation determinism proves those lambdas equal, so their output evidence can be paired for each argument. No equality of arbitrary functions, or function extensionality axiom, is used.

### The fundamental lemma {#fundamental}

Open terms are needed inside the proof even though the final observation concerns closed programs. A substitution `sigma` sends each free variable to a closed term. `RealizesEnv gamma sigma` states, pointwise, that the replacement term realizes the information assigned by `gamma`.

The fundamental lemma says: if `term` denotes `value` in `gamma`, and `sigma` realizes `gamma`, then the closed term `subst sigma term` realizes `value`. Its proof follows the finite semantic derivation.

The variable case uses the corresponding environment evidence. For a lambda, the witness is the lambda with the substitution lifted under its binder. The argument-behavior proof extends `sigma` with an arbitrary realizing argument and applies induction to the body; `betaSubst` identifies this extended substitution with beta substitution into that lambda. For an application, induction gives the function witness and the argument relation. Apply the function behavior, then prefix the function evaluation using `realizesExpansion`. Join forms a pair, bottom is immediate, and subsumption uses `realizesDown`.

{{include:src/PLFA/Part3/Adequacy.idr#fundamental}}

For a closed term, the empty environment has no variables to check. Substituting the identity map changes nothing, by the checked substitution identity theorem. This gives `closedFundamental`.

### Observable adequacy and strategy completeness {#observable-adequacy}

`functionConverges` simply extracts the evaluation witness from the arrow clause of the logical relation. To obtain the familiar equality-based adequacy statement, observe that every lambda has information `Arrow Bottom Bottom`. A semantic equality transfers that information to the term, and `functionConverges` yields a lambda result. The result body need not be the body occurring in the equality hypothesis.

Conversely, a successful `Eval` derivation yields a full beta reduction sequence. Soundness transports `Arrow Bottom Bottom` back from the resulting lambda to the original term. `observableAdequacy` packages the two directions: a closed term has some finite arrow approximation **if and only if** it weakly converges.

{{include:src/PLFA/Part3/Adequacy.idr#adequacy}}

The same results establish `cbnBetaEquivalent`: existence of a full beta reduction to some lambda is equivalent to weak call-by-name convergence to some lambda. One direction is the already proved evaluation-to-reduction map. For the other, full beta soundness gives semantic equality with the lambda endpoint, and adequacy produces a call-by-name evaluation. This is an existence-of-observation theorem. It does not say every beta strategy terminates, and does not identify the exact final bodies of two different strategies.

### Recovering the closure formulation {#closure-adequacy}

The original PLFA theorem returns a lambda closure, which retains a function body together with the environment of its free variables. The substitution-based logical relation above gives a shorter central proof, but we also connect it to that original operational representation.

`ClosureConverges` packages an actual `ClosEval` derivation from the closed input with an empty closure environment, together with `ClosureValue` evidence that the result closure contains a lambda. `convergenceToClosure` uses the proved `closedEvalToClos` bridge from ClosureCorrespondence. That bridge reconstructs the closure evaluation and proves its reified result equal to the substitution evaluator's result. The reverse map uses the previously proved `closToEval` and the explicit lambda shape.

{{include:src/PLFA/Part3/Adequacy.idr#closure-adequacy}}

`closureAdequacy` therefore restores the closure-valued equality-to-convergence theorem, and `closureBetaEquivalent` restores the two-way correspondence between arbitrary full beta reachability of a lambda and closure call-by-name convergence. `closureObservableAdequacy` also identifies closure convergence with existence of a finite arrow observation. The inverse evaluator bridge internally measures an already supplied finite evaluation derivation. It does not impose a fixed fuel limit on the theorem or assume that all terms evaluate.

## Pitfalls {#pitfalls}

- `Bottom` and `Arrow Bottom Bottom` differ. The latter requires an outer lambda result; the former says nothing about convergence.
- Convergence is weak-head convergence, not a fully beta-normal body. This distinction matters for `lambda x. Omega`.
- The theorem assumes closed programs. An open variable can carry function information from its semantic environment without being executable as a closed program. The fundamental lemma handles open terms only with the required realizing substitution.
- `SemEq term (Lam body)` is a sufficient premise. Having some arrow approximation alone does not imply equality with that particular lambda; it only guarantees some observable lambda result.
- Totality of these proof transformations does not assert totality of the object language, nor consistency of every feature of Idris2. The proof is checked relative to the book's stated compiler and logical trust boundary.

## Exercises and checked solutions {#exercises}

1. **A1 — Ignoring divergence.** Derive `Arrow Bottom Bottom` for `(lambda x. lambda y. y) A` for arbitrary closed `A`, then obtain a convergence witness. Do not evaluate `A`. Reference solution: `constantIgnoresArgument`.
2. **A2 — Transfer an observation.** Given semantic equality of two closed terms and convergence of the first, prove convergence of the second. Use an arrow observation rather than claiming equality of their returned syntax. Reference solution: `equalPreservesConvergence`.
3. **A3 — The bottom boundary.** Construct a bottom denotation for `Omega`, then prove that it has no arrow denotation. Explain why the two results are consistent. Reference solutions: `bottomIsNotEnough` and `omegaHasNoFunction`.

{{include:src/PLFA/Part3/Adequacy.idr#exercises}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA: Adequacy](https://plfa.github.io/Adequacy/), frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. Upstream relates finite values to closures using separate value and expression relations. This adaptation relates values directly to closed substituted terms; an arrow includes its lambda evaluation witness. The finite-information order and the closed call-by-name observation remain unchanged in scope.

The main logical relation produces `Eval` evidence. The proved `closToEval` and `evalToClos` bridges connect that evaluator to the actual closure semantics in both directions, with equal reified results. The final `closureAdequacy` and `closureBetaEquivalent` corollaries retain the upstream closure observation, including evidence that the result is a lambda closure. All these statements concern arbitrary untyped closed programs and finite successful derivations, without a fixed evaluation budget.

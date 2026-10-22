# Weak call-by-name evaluation {#big-step}

## Motivation {#motivation}

Full β reduction describes every permitted contraction. An implementation also needs an order in which to perform them and a criterion for stopping. **Weak call-by-name** first evaluates the function of an application, passes the argument without evaluating it, and stops as soon as it reaches a lambda. It never reduces inside the body of a returned lambda.

A big-step relation records a whole successful evaluation at once. Its finite proof explains why an input reaches a value; absence of such a proof is not itself a usable algorithm for detecting divergence. We define both substitution-based evaluation and the closure-and-environment presentation used by upstream PLFA, then prove their correspondence.

## Model {#model}

`Eval term value` has two rules. `EvalLam` returns a lambda unchanged. `EvalApp` first evaluates the function to `Lam body`, substitutes the **unevaluated** argument into that body, and evaluates the resulting term. There is no premise evaluating the argument independently.

The relation is defined for arbitrary scopes, but a successful result is always a lambda. `evalValue` proves that statement by following the second premise of each application derivation until it reaches `EvalLam`. `evalDeterministic` proves that two successful evaluations of the same input have the same result. In the application case, the function results must agree before the body derivations can be compared.

{{include:src/PLFA/Part2/BigStep.idr#evaluation}}

## Examples {#examples}

Let Ω be `(λx. x x) (λx. x x)`. The term `(λx. λy. y) Ω` evaluates to the identity function: after the outer β contraction, the argument has disappeared. `ignoreOmegaTerminates` checks this derivation. An eager policy that first demanded a value for Ω would not finish this example.

The upstream example `(λx. λy. x) Ω` also terminates under weak call-by-name, but its result is different: `λy. Ω`. The body still contains a loop. Our `lazyCaptureTerminates` checks the substitution presentation, and `closureLazyCapture` checks the corresponding closure result. The closure stores Ω in an environment; it does not execute Ω merely because the surrounding lambda is returned.

Ω itself has no `Eval` derivation. `omegaNoEval` proves this by inspecting a proposed derivation. Its function must evaluate by `EvalLam`, and its body premise would then be a strictly smaller derivation of the same alleged evaluation of Ω. Recursing on that finite proof rules out every case. The recursion decreases the **proof**, even though the object-language term repeats.

## Theorems {#theorems}

### The matching small-step strategy {#weak-small-step}

`HeadStep` has exactly two rules: contract an application whose function is a lambda, or take a step in the function position. There is no argument rule and no under-lambda rule. `HeadSteps` records finite paths of this strategy.

`lambdaDoesNotStep` rules out a step from a lambda. It supplies the impossible overlap cases of `headDeterministic`. When both derivations step in the function position, the proof recursively compares those function steps. Every head step is nevertheless a valid full β step, as `headIsBeta` shows; `headsAreBetas` lifts the inclusion to finite paths.

{{include:src/PLFA/Part2/BigStep.idr#weak-small-step}}

### Big steps and weak small steps correspond {#correspondence}

`evalToHeadSteps` turns a big-step derivation into a head-step path. An application first follows the function path in function position, then performs one outer β step, then follows the body path. `evalToSteps` consequently gives a path in the full β relation too.

For the reverse direction, `headExpand` says that if one head step leads to a successfully evaluating term, the original term also evaluates to that value. Induction on a head-step path ending at a lambda then gives `headStepsToEval`. Thus `Eval term (Lam body)` and `HeadSteps term (Lam body)` are equivalent for every scope.

For **closed inputs**, a further theorem says that an *arbitrary full β path* to some lambda implies weak call-by-name evaluation to some, possibly different, lambda. That existence result is proved later in [Adequacy](Adequacy.md), using denotational semantics. It neither preserves the exact returned body nor extends the preceding equivalence to all open terms merely by forgetting which strategy performed the steps.

{{include:src/PLFA/Part2/BigStep.idr#correspondence}}

### Closures retain the argument's environment {#closures}

A closure `Close term env` stores a term together with the closures assigned to its free slots. Environments are finite indexed lists. `Extend` places a closure in the newest slot; `lookupEnv` interprets a `Fin` index. The mutually defined data structures contain finite trees of saved terms and environments.

`ClosEval` directly implements weak call-by-name. Its variable rule evaluates the closure found by lookup. Its lambda rule returns the current term and environment. Its application rule evaluates the function to a lambda closure with saved environment `delta`, then evaluates that lambda's body in `delta` extended by `Close arg env`.

There are two environments in that last sentence for a reason: the function body uses the environment saved with the function, while the argument uses the environment at its call site. Neither may be silently replaced by the other. The argument closure is stored without evaluation. `closDeterministic` proves uniqueness of the resulting closure.

`reify` recursively replaces all saved free slots by their reified closures, producing a closed term. `reifyBeta` proves that extending an environment corresponds to one capture-avoiding substitution; it relies on `betaSubst`. Induction on closure evaluation then yields `closToEval`. Composing with the earlier path theorem gives `closToSteps`, and `closedClosToLambda` states the upstream forward result: evaluating a closed program by closures produces a full β path to a lambda.

{{include:src/PLFA/Part2/BigStep.idr#closures}}

### The correspondence also goes back to closures {#closure-equivalence}

The inverse theorem is generalized to **any** closure, not only an empty initial environment. `evalToClos input` takes a derivation that `reify input` evaluates to a closed value. It constructs a result closure, a `ClosEval input result` derivation, and an equality saying that reifying the result yields exactly that value. `closedEvalToClos` specializes this theorem to closed input terms.

The proof needs two decreasing measures. When an application evaluates, its function and body derivations are smaller, but the body closure can contain a larger newly extended environment. When a variable is looked up, evaluation need not become smaller, but the saved closure lies deeper in a finite environment tree. A single recursion on syntax would not justify both moves.

`BoundedEval` annotates an already-existing derivation with an upper bound on its height. `weakenBound` enlarges a bound, and `evalBound` constructs a suitable bound for **every** finite `Eval` derivation. Thus no fixed budget is assumed in the final correspondence theorem. This is an induction device, not a fuel-limited replacement for the operational relation.

{{include:src/PLFA/Part2/ClosureBounds.idr#bounded-evaluation}}

{{include:src/PLFA/Part2/ClosureBounds.idr#finite-derivation-bound}}

`closValue` exposes the lambda shape of every successful closure result. `boundedToClos` and `boundedEnvToClos` then recurse mutually: application decreases the height bound, while variable lookup descends through the closure/environment structure with the same bound. In the application case, equality of the reified function result identifies its lambda body, and `reifyBeta` transports the second premise into the extended closure environment.

{{include:src/PLFA/Part2/ClosureCorrespondence.idr#closure-values}}

{{include:src/PLFA/Part2/ClosureCorrespondence.idr#inverse}}

## A total executable evaluator {#fuel}

`headView` inspects a term and either identifies a lambda, identifies an open neutral head, or supplies one `HeadStep`. Here a neutral head may have arbitrary arguments: weak evaluation will not inspect them. This `Neutral` differs from the `FullNeutral` predicate in [Untyped](Untyped.md#normalization), whose arguments must themselves be normal.

`run fuel term` repeats those inspections. `Returned` carries a path to a lambda; `Blocked` carries a path to an open neutral term; `OutOfFuel` carries a path to the current residual term. All three results therefore preserve an explicit account of the reductions performed. A successful result can be converted to `Eval` using `headStepsToEval`.

At zero fuel the evaluator immediately returns `OutOfFuel`, even for a lambda. A final value inspection consumes a budget unit, so one β step followed by recognizing a lambda needs two units. Increasing the budget allows longer searches, but an exhausted run does not prove divergence. The separate theorem `omegaNoEval`, rather than the finite test `fuelOmega`, establishes Ω's nonconvergence.

{{include:src/PLFA/Part2/BigStep.idr#fuel}}

## Pitfalls {#pitfalls}

- **Weak values are not necessarily full normal forms.** `λy. Ω` is a value of this strategy despite its reducible body.
- **Call-by-name does not mean call-by-need.** These rules do not memoize an evaluated argument; repeated variable uses may repeat its evaluation.
- **Closure arguments retain their call-site environment.** Using the function's environment for them would change the meaning of free variables.
- **Determinism permits divergence.** It proves uniqueness when two successful derivations exist, not that a derivation always exists.
- **A height bound on a supplied proof is not a termination oracle.** `evalBound` cannot manufacture an `Eval` derivation for an arbitrary program.

## Exercises and checked solutions {#exercises}

1. **BigStep-1 — Ignore a looping argument.** Construct evaluations of `(λx. λy. y) Ω` and `(λx. λy. x) Ω`, and explain why their returned lambdas differ. Solutions: `ignoreOmegaTerminates` and `lazyCaptureTerminates`.
2. **BigStep-2 — Keep the saved argument.** Construct the closure derivation for the second expression in Exercise 1. Identify which environment stores Ω and why no variable lookup happens before the result is returned. The checked solution is `closureLazyCapture`.
3. **BigStep-3 — Prove a negative result.** Refute any alleged evaluation of Ω by induction on its finite derivation, not by running a bounded test. The checked solution is `omegaNoEval`. Contrast it with the three executable checks `fuelIdentity`, `fuelOmega`, and `fuelNeutral`.

{{include:src/PLFA/Part2/BigStep.idr#examples}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA, “BigStep”](https://plfa.github.io/BigStep/), source `src/plfa/part2/BigStep.lagda.md`, frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. Closure evaluation, determinism, and reification to full β reduction are preserved. Environments use indexed lists instead of finite-domain functions. The substitution presentation, matching weak-step equivalence, proof-carrying fuel evaluator, and general reverse closure correspondence make the representation choices explicit. [Adequacy](Adequacy.md) uses that bridge to state its convergence results in both presentations; no implication from all β paths to the exact same weak value is asserted here.

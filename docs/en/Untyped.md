# Untyped lambda calculus {#untyped}

## Motivation {#motivation}

The simply typed lambda calculus rejects a function that applies its argument to itself. Removing that restriction gives a small language capable of describing nonterminating computations. We still want precise binding rules, meaningful execution traces, and theorems about different ways of reducing a program. None of those requires every program to terminate.

This chapter defines **full β reduction**. Any application of a lambda may contract, including one inside a lambda body or inside an argument. There is deliberately no prescribed evaluation order. [BigStep](BigStep.md) later selects weak call-by-name as an execution strategy; [Confluence](Confluence.md) proves that the broader reduction relation has consistent answers when answers exist.

Our Idris programs and proofs use total definitions. The language they describe remains untyped and may diverge. Keeping the host language and object language separate is essential to reading this development.

## Model {#model}

### Scope is different from a type {#scope}

`Tm n` is a lambda term with `n` available variable slots. The index counts variables in scope; it does not describe the kind of value a term computes. `Tm 0` contains closed terms, including both the identity function and the looping term Ω.

Variables use de Bruijn indices. `FZ` selects the nearest binder or newest surrounding slot. `FS i` skips one slot. Entering a lambda adds one slot, so the argument of `Lam` has type `Tm (S n)`. Application puts no typing restriction on either subterm: both have the same scope `n`.

| Named expression | Representation | What the index means |
|---|---|---|
| `λx. x` | `Lam (Var FZ)` | Select the binder just entered. |
| `λx. λy. x` | `Lam (Lam (Var (FS FZ)))` | Skip `y`, then select `x`. |
| `λx. x x` | `Lam (App (Var FZ) (Var FZ))` | Both occurrences select `x`. |

Changing a bound variable's spelling does not change this representation. There is therefore no separate choice of fresh *names* during substitution. There is still a binding problem to solve: moving a free variable below a binder must adjust its index.

### Renaming and substitution {#substitution}

A renaming maps each old variable to a new variable. A simultaneous substitution maps each old variable to a new term. The shape of both operations follows the syntax. Their lambda cases are the important ones.

`liftRen rho` fixes the new `FZ` slot and applies `rho` to older slots. `liftSub sigma` also fixes the bound variable. For an older variable, it first obtains the replacement term `sigma i`, then weakens that whole term with `rename FS`. Weakening keeps the replacement's free variables outside the newly crossed binder. Omitting it would silently capture variables.

`single arg` is the substitution used at a β redex: replace slot zero by `arg` and decrement every older slot. `beta body arg` applies this map throughout the body, extending it correctly whenever another lambda is crossed.

{{include:src/PLFA/Part2/Untyped.idr#syntax}}

For example, `(λx. λy. x) z` must become `λy. z`, with `z` still free. In a one-slot surrounding scope, its result is `Lam (Var (FS FZ))`. `Lam (Var FZ)` would instead be the identity function, and would be the wrong answer. The checked `captureAvoidance` equation below distinguishes those cases.

## Examples {#examples}

Let `I` stand for `λx. x`. The application `I a` contracts directly to `a`. The same contraction may happen under a binder: `λz. I z` reduces to `λz. z`. These are different reduction rules: the first uses `Beta`, and the second puts `Beta` inside `UnderLam`.

Now let `D = λx. x x`, and define Ω as `D D`. Substituting `D` for the two occurrences of `x` produces `D D` again. `omegaLoops` is a proof of this single β step back to the identical term. Repeating it gives a reduction sequence of any requested finite length. A self-loop alone would not rule out other terminating paths in an arbitrary nondeterministic system. For this particular Ω, [BigStep](BigStep.md#examples) separately proves that no weak call-by-name big-step derivation exists.

Reduction order can change the number of steps. For `(λx. x x) (I a)`, reducing the inner `I a` first avoids duplicating that redex. Reducing the outer redex first leaves two copies to contract. [Confluence](Confluence.md#examples) checks both paths and explains what they have in common.

### Numbers and recursion as terms {#encodings}

A Church numeral accepts a function `s` and a starting value `z`, then applies `s` the indicated number of times. Thus Church two is `λs. λz. s (s z)`. `churchAdd` composes the iterations supplied by two such numerals. After two outer β contractions, two-plus-two is already a lambda, but further reductions *under* its two binders are needed to expose Church four. This is an example that weak evaluation alone does not finish.

A Scott numeral instead performs one case analysis. Scott zero selects the zero branch; Scott successor passes its predecessor to the successor branch. `scottCase` supplies these two branches, wrapping the successor branch in a lambda because it has one additional variable in scope. `scottSucc` is an encoded application, so `scott 4` itself still contains reducible syntax.

`fixpoint` encodes recursion through self-application. Its argument is a body with a slot for its own recursive function. `scottAdd` examines its first argument: zero returns the second argument; successor returns the successor of a recursive call on the predecessor. `scottMultiply` similarly adds the second argument to the recursive product. These are ordinary finite lambda terms. The host functions constructing them terminate; running an arbitrary encoded recursion need not.

{{include:src/PLFA/Part2/Untyped.idr#encodings}}

## Theorems and reduction evidence {#theorems}

`Step source target` records one allowed contraction. Besides `Beta`, there are separate rules for the function position, argument position, and lambda body. In particular, `AppRight` has no premise saying that the function is already a value. `UnderLam` has no premise saying that execution has entered that function. Those absences are intentional: this is full reduction.

`Steps source target` records zero or more steps. `Done` is the empty path; it does not assert that its term is normal. `More` records an intermediate term and one additional step. A finite derivation certifies exactly the path it contains.

The four path lemmas construct longer evidence. `stepsTrans` concatenates paths. `stepsLam`, `stepsLeft`, and `stepsRight` lift every step of a path into one fixed syntactic context. Their proofs recurse on the path, not on an evaluator and not on a claim that reduction must finish.

{{include:src/PLFA/Part2/Untyped.idr#reduction}}

The scope index guarantees that renaming and substitution cannot produce a dangling variable. Stronger algebraic facts, including identity, composition, and substitution commuting with β contraction, are proved in [Substitution](Substitution.md). Confluence relies on those actual laws rather than treating substitution as informal text replacement.

### Full normal forms, progress, and fuel {#normalization}

For full reduction, a neutral term is a variable followed by zero or more **normal arguments**. A full normal form is either neutral or a lambda with a normal body. The mutually defined `FullNeutral` and `FullNormal` record exactly this structure. Requiring the arguments and lambda bodies to be normal is what distinguishes them from weak head forms.

`progress` works for every scope, including open terms. It either constructs a β step or returns a full-normal-form certificate. At an application of a lambda it immediately contracts the outer redex. Otherwise it searches the function first, then the argument; inside a lambda it searches the body. This is the leftmost-outermost, or normal-order, choice of next step. The theorem is a one-step alternative, not a claim that repeated choices finish.

`fullNormalNoStep` proves that a certified full normal form has no `Step` successor. `noStepIsNormal` proves the converse by running `progress`: its step case would contradict the supplied assumption. Open variables therefore count as finished normal forms, rather than as errors.

`normalize fuel term` repeats the selected step with a finite budget. Every result carries its complete `Steps` trace. `Exhausted` additionally proves that the trace length equals the supplied fuel. `Normalized` proves that its trace is strictly shorter than the fuel and that its endpoint is a full normal form. One budget unit is reserved for the final inspection: zero fuel reports exhaustion even when the initial term is already normal. Exhaustion reports incomplete work, not a divergence proof.

{{include:src/PLFA/Part2/Untyped.idr#normalization}}

For `λz. I z`, the full normalizer takes the internal step and returns `λz. z`. The weak evaluator in [BigStep](BigStep.md#fuel) immediately returns the original lambda. Both results satisfy their own specification. This development proves the normalizer's certificates and fuel accounting; it does not use a proof of the separate standardisation theorem that normal order finds every existing full normal form.

## Pitfalls {#pitfalls}

- **Well scoped does not mean well typed.** The term `selfApply` is deliberately accepted, and `omega` is closed.
- **An available step is not an evaluation policy.** `Step` permits several redex choices. A deterministic policy is a separate relation.
- **A lambda need not be a full normal form.** Its body may contain a redex. Weak call-by-name nevertheless treats every lambda as a value.
- **A finite trace is not a termination theorem.** The empty trace exists even for Ω. A fuel evaluator stopping after a fixed budget likewise says nothing by itself about divergence.
- **Indices do not make capture disappear automatically.** Correct lifting of substitutions is what prevents capture.

## Exercises and checked solutions {#exercises}

1. **Untyped-1 — Preserve a free variable.** Compute `(λx. λy. x) z` in a one-slot surrounding scope. Explain why the result's variable has index one below the remaining lambda. Check your equation against `captureAvoidance`.
2. **Untyped-2 — Reduce below a binder.** Construct evidence that `λz. I z` reduces to `λz. z`. Identify the outer rule and the inner rule separately. The solution is `underBinder`; a weak head-step rule could not construct it.
3. **Untyped-3 — Inspect self-application.** Expand one β contraction of Ω and show that it returns to Ω. The solution `omegaLoops` is a finite proof of a loop edge, not a recursive evaluator.
4. **Untyped-4 — Normalize arithmetic.** Check that Church two-plus-two returns Church four, and that Scott two-plus-two and two-times-two normalize to the same term as Scott four. Also check successful completion, not just equality of two residual terms. Solutions: `churchTwoPlusTwo`, `churchTwoPlusTwoFinishes`, `scottTwoPlusTwo`, `scottTwoTimesTwo`, and `scottArithmeticFinishes`. Explain why the Scott comparison uses normalized endpoints.

The following source also defines the named example terms and proves the general identity contraction `identityBeta`.

{{include:src/PLFA/Part2/Untyped.idr#examples}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA, “Untyped”](https://plfa.github.io/Untyped/), source `src/plfa/part2/Untyped.lagda.md`, frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. This independent Idris2 adaptation uses `Nat`/`Fin` scopes in place of a context containing repetitions of one dummy type. It preserves unrestricted syntax, full β reduction, open-term progress, certified full normalization with fuel, and Church/Scott/fixpoint examples. The distinct weak evaluator is in [BigStep](BigStep.md#fuel). As in the upstream chapter, the general normal-order standardisation fact is explained but not formalized here.

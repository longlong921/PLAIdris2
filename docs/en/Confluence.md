# Confluence of full beta reduction {#confluence}

## Motivation {#motivation}

Full β reduction lets us choose a redex anywhere in a term. If two choices lead to different intermediate terms, can their computations be reconciled? **Confluence** answers yes: whenever one source reduces in finitely many steps to `left` and to `right`, there is a common term `meet` reachable from both.

This is a statement about the unrestricted relation in [Untyped](Untyped.md#theorems), including reduction beneath lambdas and in both sides of an application. It is not obtained by choosing one deterministic strategy. It also says nothing about whether either path eventually reaches a normal form. Ω remains an allowed source.

## Model {#model}

A one-step relation has the diamond property if any two of its outgoing steps can each be followed by one step to a shared target. Ordinary β reduction does **not** have this property. Duplicating an argument can duplicate unfinished work.

We introduce an auxiliary relation `Par source target` for parallel reduction. `PVar` leaves a variable alone. `PLam` reduces a body in parallel. `PApp` reduces both subterms in parallel. `PBeta` reduces a lambda's body and its argument in parallel and then substitutes their results. `PApp` remains available even when the function is a lambda, so a parallel round may leave a particular outer redex uncontracted.

Every term reduces to itself in parallel, by `parRefl`. This is proved structurally; it is not an extra general reflexivity constructor. `Pars` is the finite reflexive-transitive closure of `Par`.

{{include:src/PLFA/Part2/Confluence.idr#parallel}}

## Examples {#examples}

Write `R = (λx. x) a`. From `(λx. x x) R`, one ordinary step can produce either `(λx. x x) a` or `R R`. The first branch reaches `a a` in one more step. The second needs two ordinary contractions, one in each copy of `R`. Thus the common endpoint exists, but the proposed ordinary **one-step** diamond fails.

In parallel reduction, `R R` reaches `a a` in one round using `PApp` with a contraction on each side. The duplication that caused trouble for an ordinary step now fits the auxiliary relation. `duplicateOuterFirst` and `duplicateInnerFirst` below check the original finite β paths; `duplicateJoin` checks the parallel duplication step for an arbitrary parallel argument reduction.

## Theorems {#theorems}

### Substitution preserves parallel reduction {#substitution}

The heart of the proof is `parSubst`: if the two substitutions are pointwise related by parallel reduction and the two input terms are parallel related, the substituted results are parallel related too. A weaker statement about replacing just one variable is insufficient for an induction beneath lambdas.

We first prove `parRename`. Its β case uses `renameBeta` from [Substitution](Substitution.md#substitution-laws). Renaming preservation then lifts a pointwise substitution relation beneath a binder. Finally, the β case of `parSubst` uses `substBeta`. These are precisely the two places where capture-avoiding substitution must be connected to reduction, not merely defined.

`parBeta` specializes the general lemma to one argument: parallel-related bodies and parallel-related arguments have parallel-related β results.

{{include:src/PLFA/Part2/Confluence.idr#preservation}}

### Complete development gives a triangle {#triangle}

`develop source` recursively contracts every redex visible in the original source. It does not promise a normal form, nor does it immediately contract every new redex created by those contractions. For example, reducing the function of an application can expose a lambda that was not originally in function position.

The triangle theorem `parTriangle` says that every parallel reduct of `source` can reduce in parallel again to `develop source`. The subtle case is a `PApp` round whose original function was a lambda: the first round deliberately retained the outer redex; the next round uses `PBeta` to catch up. If the first round already used `PBeta`, `parBeta` joins the two substituted components.

Two triangles with the same source have the same complete development at their base. Pairing them proves `parDiamond`, with an explicit shared target and an explicit proof from each branch.

{{include:src/PLFA/Part2/Confluence.idr#triangle}}

### Parallel and ordinary paths have the same reachability {#correspondence}

`stepPar` turns one ordinary step into a parallel round, leaving untouched subterms reflexively related. Conversely, `parSteps` serializes a parallel round into finitely many ordinary steps. In its β case it first reduces the body under the lambda, then the argument, and finally performs the outer contraction.

Lifting these conversions along paths gives `stepsPars` and `parsSteps`. The equivalence is between **finite reachability relations**. It is not an assertion that one ordinary step equals one parallel round, or that they have equal costs.

{{include:src/PLFA/Part2/Confluence.idr#correspondence}}

### Confluence and Church–Rosser {#church-rosser}

`strip` propagates a single parallel step across an entire parallel path by repeatedly completing diamonds. `parsConfluent` then repeats this construction along the other path. Converting the result back to ordinary steps yields `confluence` for arbitrary well-scoped terms and arbitrary finite β paths.

Church–Rosser is often stated with **convertibility** instead of two forward paths. `Convertible left right` records a finite chain whose edges may point forward or backward. `churchRosser` proves that such a chain has a common forward reduct. A backward edge is handled by a use of confluence; forward edges can be prepended directly.

Finally, `Normal term` means that no β step leaves `term`. `normalPath` shows that a path out of a normal form can only have length zero. Hence `normalUnique` proves that two normal forms reachable from the same source are equal. The structural `FullNormal` certificates from [Untyped](Untyped.md#normalization) supply this no-step property through `fullNormalNoStep`.

{{include:src/PLFA/Part2/Confluence.idr#confluence}}

## Pitfalls {#pitfalls}

- **Confluence is not termination.** The theorem accepts two finite paths; it never claims that all paths finish.
- **Unique normal forms need not exist.** `normalUnique` has two explicit reduction hypotheses and two normality hypotheses.
- **A complete development is not full normalization.** It handles the redex structure of one source in one recursively defined round.
- **Ordinary β reduction is not diamond.** Parallel reduction is introduced specifically to solve that difficulty.
- **Determinism of weak evaluation is a different theorem.** Restricting to one strategy would not establish the full β claim proved here.

## Exercises and checked solutions {#exercises}

1. **Confluence-1 — Join duplicated work.** Given `Par arg result`, construct `Par (App arg arg) (App result result)`. Explain why the two copies may be reduced in the same parallel round. The checked solution is `duplicateJoin`.
2. **Confluence-2 — Compare ordinary paths.** Construct both paths from `(λx. x x) ((λx. x) a)` to `a a`, choosing the outer redex first in one path and the inner redex first in the other. Solutions: `duplicateOuterFirst` and `duplicateInnerFirst`. Count three and two ordinary steps respectively.
3. **Confluence-3 — Identity in parallel.** Show that applying the identity function to any argument parallel reduces to that argument, without evaluating it. The checked solution is `identityParallel`.

{{include:src/PLFA/Part2/Confluence.idr#exercises}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA, “Confluence”](https://plfa.github.io/Confluence/), source `src/plfa/part2/Confluence.lagda.md`, frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. This adaptation preserves the parallel-reduction, complete-development, and strip proof for full untyped β reduction. It additionally spells out finite zigzag convertibility and uniqueness of reachable normal forms. No function extensionality, normalization assumption, or deterministic-strategy replacement is used.

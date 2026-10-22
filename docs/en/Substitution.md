# Substitution laws {#substitution}

## Motivation {#motivation}

Writing a capture-avoiding substitution function is only the first step. To reason about lambda calculus, we must know how two substitutions compose, how substitution interacts with renaming, and what happens when a substituted lambda is applied. [Confluence](Confluence.md) needs these laws to reduce a body and its argument simultaneously. [BigStep](BigStep.md) needs them to connect environments of closures with terms obtained by substitution.

This appendix proves the laws for all well-scoped untyped terms, including open terms. There is no typing, normalization, or evaluation hypothesis. The important assumptions are the scopes of the maps: every old slot must have an image in the specified new scope.

## Model {#model}

Recall that a renaming has type `Fin m -> Fin n`, while a substitution has type `Fin m -> Tm n`. Under a lambda, `liftRen` and `liftSub` reserve the new slot for the bound variable. In particular, `liftSub sigma (FS i)` weakens `sigma i` before putting it beneath the binder. The definitions themselves are in [Untyped](Untyped.md#substitution).

We compare maps **pointwise**: for every variable `i`, their images are equal. We never need an equality between the functions themselves. The lemmas `renameExt` and `substExt` transport pointwise equality to equality of the resulting terms. Their lambda cases lift the pointwise hypothesis; their application cases use the two induction hypotheses.

{{include:src/PLFA/Appendix/Substitution.idr#extensionality}}

This choice matters in intensional type theory. Pointwise equality is the evidence available in these proofs. Replacing it with equality of entire functions would introduce a separate function-extensionality principle that the development does not assume.

## Examples {#examples}

Suppose the surrounding slots are `x` and `y`. First rename `x` to `y`, then substitute a term `N` for `y`. The result should be the same as directly mapping `x` to `N`. `substRename` makes that observation precise for an arbitrary term and arbitrary maps.

The key cancellation example crosses one extra binder. `rename FS term` shifts every free slot of `term` away from the new zero slot. Substituting any `arg` into that unused zero slot should return `term`. This is `cancelShift`; the argument may itself contain free variables or diverging syntax. It is never evaluated by the proof.

For a concrete binding example, `(λx. λy. x) z` becomes `λy. z`. The `z` inserted beneath the inner binder is weakened, so its index becomes one. The numerical indices change, but the variable's binding does not. The checked example is `captureAvoidance` in [Untyped](Untyped.md#exercises).

## Theorems {#theorems}

### Renamings compose {#renaming-laws}

`renameId` says that using the identity map leaves a term unchanged. `renameComp rho tau term` says that renaming first with `tau` and then with `rho` equals renaming once with their pointwise composite. The order of the arguments matters: the first map in the theorem is the **outer**, later operation.

The variable case computes directly. In the lambda case the recursive call uses two lifted maps. `liftRenComposition` checks that lifting the composite agrees, variable by variable, with composing the lifts: the newly bound variable is fixed on both sides, and an older variable is shifted after applying both maps.

{{include:src/PLFA/Appendix/Substitution.idr#renaming}}

### Renaming and substitution interact {#mixed-laws}

There are two distinct mixed laws. `substRename sigma rho term` first renames the input slots and then substitutes their images. `renameSubst rho sigma term` first substitutes replacement terms and then renames the free variables of those replacements. Their right-hand sides are different maps, so the two laws should not be conflated.

The difficult-looking part of `renameSubst` is the old-variable case under a lambda. One side first weakens a replacement and then applies a lifted renaming; the other first renames that replacement and then weakens it. Two uses of `renameComp` identify those expressions. There is no new binding principle hidden in this step.

{{include:src/PLFA/Appendix/Substitution.idr#mixed-laws}}

### Substitutions compose {#substitution-laws}

`substId` uses the substitution mapping each variable to itself. `substComp sigma tau term` states the main composition law: substitute with `tau`, then with `sigma`, or substitute once with the map sending `i` to `subst sigma (tau i)`.

The proof follows the term structure. Its lambda case needs `liftSubComposition`. For an old variable, the lifted inner substitution has introduced a weakening. `substRename` moves the outer substitution past that weakening, and `renameSubst` moves it back on the other side. This is why the mixed laws were proved first.

`cancelShift` follows from `substRename` and `substId`. It then provides the old-variable case in the β interaction laws:

- `renameBeta` commutes renaming with one simultaneous body-and-argument contraction.
- `substBeta` commutes an arbitrary simultaneous substitution with that contraction.
- `betaSubst` substitutes an environment into a lambda body and then supplies an argument. Its result equals substituting once with `cons arg sigma`, the map that sends the newest slot to the argument and every older slot through `sigma`.

These statements concern syntactic equality of resulting terms. They do not assert that evaluating an argument terminates. In particular, `betaSubst` accepts a replacement for every old slot and a new argument in the **target** scope. It is the version used to extend a reified closure environment.

{{include:src/PLFA/Appendix/Substitution.idr#substitution-laws}}

## Pitfalls {#pitfalls}

- **Map composition is ordered.** In `substComp sigma tau term`, `tau` acts first. Swapping the maps generally changes both the types and the result.
- **Lifting is not ordinary map extension.** Older substitution images must be weakened; fixing only `FZ` is insufficient.
- **A binder can be unused even when the body has other free variables.** `cancelShift` is valid for arbitrary open terms, not just closed constants.
- **β substitution does not evaluate the argument.** These are syntax transformations, so Ω is a permitted argument.
- **Pointwise congruence is not function extensionality.** We prove equality after applying maps to a term, without postulating equality of the maps themselves.

## Exercises and checked solutions {#exercises}

1. **Substitution-1 — View renaming as substitution.** Prove that renaming with `rho` equals substituting each variable by `Var (rho i)`. Use `substId` on the renamed term, then `substRename`. The checked solution is `renamingAsSubstitution`.
2. **Substitution-2 — Remove an unused binder.** For arbitrary `arg` and `term` in the same scope, prove `beta (rename FS term) arg = term`. Explain why no assumption about the free variables of `arg`, or its termination, is needed. The checked solution is `unusedBinder`, obtained from `cancelShift`.

{{include:src/PLFA/Appendix/Substitution.idr#exercises}}

## References and adaptation {#references}

Adapted from Philip Wadler, Wen Kokke, and Jeremy G. Siek, [PLFA, “Substitution”](https://plfa.github.io/Substitution/), source `src/plfa/part2/Substitution.lagda.md`, frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under CC BY 4.0. This book places the chapter in the appendix and the module in `PLFA.Appendix.Substitution`. The Idris2 presentation uses `Fin`-indexed untyped scopes and pointwise map laws, avoiding a function-extensionality axiom. The exported identity, composition, weakening-cancellation, and β interaction results are general over all maps and all well-scoped terms.

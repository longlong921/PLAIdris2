# Bisimulation: proving a translation respects execution {#bisimulation}

## Motivation {#motivation}

A compiler can change a program's syntax without changing how it behaves.
Consider translating “let x = arg in body” into “(λx. body) arg”. Under our
weak call-by-value rules, both evaluate `arg` first and then substitute its
value into `body`. That informal explanation leaves a crucial question: if
`body` or `arg` contains more lets, does the translation still agree after
substitution?

We answer with a relation between source and target terms, prove it survives
renaming and substitution, and then match every reduction step in both
directions. Here the match is **one step for one step**, a stronger result
than the more general notion of simulation that permits several target steps.

Like the upstream chapter, we focus on the variable/lambda/application/let
fragment of [More](More.html). The ambient datatype has other constructs,
but the relation below has no cases for them. Thus the theorem is about all
terms in this precise fragment, not all possible `More` terms.

## Model {#model}

### A compilation relation {#relation}

`Related s t` means that `t` is the let-free translation of `s`. Both terms
have the same context and type. Variables stay variables, lambdas translate
their bodies, applications translate both parts, and a let becomes an
application whose function is a freshly formed lambda.

{{include:src/PLFA/Part2/Bisimulation.idr#relation}}

`RLet` is the only shape-changing rule. Its body relation lives under the same
additional bound-variable type on both sides. Therefore it cannot accidentally
translate a reference to the let-bound variable into a reference to some
outer variable.

`Fragment s` records that `s` contains only the four relevant constructors.
It is a structural domain for the executable `compile` function, not an
assumption that compilation is correct. `compile` recursively returns an
actual target together with a freshly constructed `Related` certificate.
`relatedFunctional` proves that any two related targets of the same source
are equal. Its lambda, application, and let cases use the corresponding
induction hypotheses.

## Worked example {#examples}

The source “let id = (λx. x) in id” translates to
“(λid. id) (λx. x)”. The source takes `LetBeta`; the target takes `Beta`.
Both arrive at identity, but their initial syntax trees differ. This small
example is a real instance of the translation, not identity simulation in
disguise.

{{include:src/PLFA/Part2/Bisimulation.idr#examples}}

For a binding that itself reduces, the source takes `LetStep`. The translated
function is already a lambda value, so the matching target rule is `AppR`,
not `AppL`. This choice is why the proof depends on the evaluation strategy.
If target reduction were allowed inside lambda bodies, additional target
steps would require a different argument.

## The simulation proofs {#theorems}

### Compatibility with values, renaming, and substitution {#compatibility}

Values in the related fragment can only be lambdas. `valueForward` and
`valueBackward` transport that fact in both directions. A translated let is
an application, so it is not itself a value even when its binding is one.

Renaming commutes with the relation structurally. Under a lambda or let body,
`renameRelated` extends the renaming map. This result is then used in the
old-variable case of `extendRelated`, where replacement terms must be
weakened under a new binder.

{{include:src/PLFA/Part2/Bisimulation.idr#compatibility}}

`substRelated` takes **two** substitution maps: one for the source and one for
the target. The hypothesis relates their images at every variable. It then
relates substitution into any related pair of terms. At a variable, use the
hypothesis; at a binder, extend it; at an application, recurse into both parts.
At a let, the target remains a lambda application with the corresponding
extended substitution in its body.

`instRelated` specializes this theorem to replacing one variable. Its premises
are relations between the two bodies and between the two arguments. It
produces a relation between the substituted results. This is the bridge needed
for beta rules; equating the original bodies would be a much stronger and
usually false requirement.

### Forward simulation {#forward}

The forward claim fills in the bottom and right sides of this square:

| | Before | After |
| --- | --- | --- |
| Source | s | u, with `Step s u` |
| Target | t, with `Related s t` | some v, with `Step t v` and `Related u v` |

`ForwardLeg` packages exactly those two missing pieces. Its constructor does
not assume the theorem: the implementation of `forward` must produce the
related result and the actual target reduction for every source rule.

{{include:src/PLFA/Part2/Bisimulation.idr#forward}}

Application context steps use the induction hypothesis, then rebuild `AppL`
or `AppR`; the latter also transports the function's value proof. A beta step
uses `instRelated` and the translated argument's value proof. A let context
step becomes `AppR VLam`, and a let beta step becomes an ordinary beta step.
There are no reduction cases for variables or lambda values.

### Reverse simulation {#backward}

Forward simulation alone does not rule out extra target behavior. `backward`
starts with a target step and produces a matching source step with related
results. At a translated let, a target `AppL` step is impossible: its function
is a lambda. A target `AppR` step corresponds to `LetStep`; target beta
corresponds to `LetBeta`.

{{include:src/PLFA/Part2/Bisimulation.idr#backward}}

The relation need not be symmetric as a relation on syntax: a let is related
to its expansion, and the grammar does not add the converse pair. What makes
it a bisimulation is that **steps can be matched from either side** of every
related pair. This is distinct from proving `Related t s` whenever
`Related s t`.

### Finite executions and the compilation graph {#traces}

`forwardMany` and `backwardMany` iterate the respective one-step proofs over
finite traces. An empty trace keeps the initial relation; a nonempty trace
matches its first step and recurses on its tail. Each matching step remains
present in the returned trace. No normalization or bound on trace length is
assumed.

{{include:src/PLFA/Part2/Bisimulation.idr#traces}}

Finally, `compiledMatches` identifies the target returned by `compile` with
any target certified by `Related`. It unpacks the compiler's certificate and
uses `relatedFunctional`. Together with `relatedFragment` below, this makes
precise why the relation describes the graph of this compiler on its domain.

{{include:src/PLFA/Part2/Bisimulation.idr#graph}}

## Pitfalls {#pitfalls}

- A relation describing a translation is not automatically a simulation.
  The step-matching functions are the separate proof obligations.
- A source let step maps to an application step. Requiring the same
  constructor name on both sides would miss the actual argument.
- Substitution compatibility needs related replacements, not identical
  substitution maps. The target replacements may already have lets expanded.
- Bisimulation concerns matching behavior in both directions; it does not
  require the compilation relation itself to be symmetric.
- The relation's grammar determines theorem scope. Literals, fixpoints,
  products, sums, and lists in `More` are not silently covered by this proof.
- Matching finite reductions is not, by itself, a contextual-equivalence
  theorem for every feature of the surrounding language.

## Exercises and checked solutions {#exercises}

1. **Compile a nested let.** Supply a `Fragment` certificate for a let whose
   body contains another let, then obtain a target and relation certificate.
2. **Use the reverse simulation.** Transport the beta step of the compiled
   identity example back to the source let step.
3. **Recover the domain.** Prove that any `Related s t` certificate yields a
   `Fragment s` certificate. Explain why this does not require inspecting an
   arbitrary `More` term.

{{include:src/PLFA/Part2/Bisimulation.idr#solutions}}

The solutions are `nestedCompilation`, `reverseExample`, and
`relatedFragment`. The first uses the compiler rather than hand-assuming its
result. The third recurses over the translation certificate, whose
constructors contain precisely the evidence required for the source fragment.

## References and adaptation {#references}

Independent adaptation of [PLFA, Bisimulation](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/Bisimulation.lagda.md)
by Philip Wadler, Wen Kokke, and Jeremy G. Siek, at frozen commit
`1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The upstream lambda/let fragment and forward simulation are retained. The
reverse simulation, suggested there as an exercise, is fully implemented,
as are both finite-trace directions and an executable certified translation.
The product-encoding exercise is not claimed as a proved general equivalence.
All included definitions and solutions are checked with Idris2 0.8.0.

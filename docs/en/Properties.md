# Properties: progress and preservation {#properties}

## Motivation {#motivation}

A type derivation describes a program before execution. Why should it tell us
anything about the program after execution? A beta step discards an application
and inserts an argument into a body, possibly many times and underneath other
binders. The connection is a substitution theorem, not an informal appeal to
what types are supposed to mean.

We prove two independent claims for the language from [Lambda](Lambda.html):
**preservation**, for any context, says one step retains the type;
**progress**, for the empty context, says the program is already a value or can
step. Their combination excludes stuck final states along every finite
execution of a closed well-typed program. General recursion remains present,
so this statement is deliberately different from termination.

## Model {#model}

The inputs are the external judgement `HasType gamma t a`, the call-by-value
relation `Step t u`, its finite closure `Steps`, and the value predicate from
the previous chapter. `Raw n` enforces scope only. In particular, preservation
is a statement about an independently defined reduction relation on raw terms;
it is not obtained merely by indexing that relation with a type.

The context vector lists newest variables first. A map between scopes is
usable for typing only if it respects the types stored at those positions.
This is the extra hypothesis missing from an arbitrary raw renaming or
substitution.

### The structural lemmas {#structural}

`renameTyping` assumes that variable `i` and its image `rho i` have equal
lookup types. It then transports **any** typing derivation through renaming.
Under a binder, zero is unchanged and older variables use the original
hypothesis. That is precisely `liftRenType`.

`substTyping` strengthens the map from variables to terms. Its hypothesis gives
a typing derivation for **every** replacement, at the replaced variable's
type. Under a binder, the new variable maps to itself, while every old
replacement is weakened using the already-proved renaming theorem.

{{include:src/PLFA/Part2/Properties.idr#structural}}

Notice the dependency order: renaming first, then lifted substitution, then
substitution itself. Using substitution to justify its own weakening case
would be circular. Both recursive proofs follow the original typing
derivation, including lambda, case, and fixpoint bodies.

`instantiateTyping` specializes simultaneous substitution to one variable.
Its premises are Γ,a ⊢ body : b and Γ ⊢ arg : a; its conclusion is
Γ ⊢ body[arg] : b. The argument need not be closed or a value. This stronger
statement is useful twice: beta reduction supplies a value, whereas fixpoint
unfolding supplies the recursive term itself.

## Worked examples {#examples}

Consider identity applied to a natural number. Inverting `TApp` and `TLam`
reveals a derivation of the body under one natural-number assumption, plus a
derivation of the argument at that same type. `instantiateTyping` combines
them into a derivation of the result. No equality between arbitrary programs
is assumed.

For a successor case, the branch context contains a natural-number predecessor.
The rule `CaseSucc` removes that binder, and the typing derivation of the
predecessor supplies exactly the replacement needed by `instantiateTyping`.
For `Unfold`, the replacement typing is the original `TFix` derivation itself;
the proof does not recursively evaluate the program.

A useful counterexample goes in the other direction. A case on zero ignores
its successor branch, even if that branch contains zero applied to zero. The
source is untypable, yet its one-step target is the well-typed zero. Thus
**subject expansion**, the converse of preservation, fails.

{{include:src/PLFA/Part2/Properties.idr#expansion}}

## The main theorems {#theorems}

### Preservation {#preservation}

`preservation` consumes a typing derivation and a reduction derivation and
returns the new typing derivation. Contextual steps recurse into the reduced
subterm and rebuild the surrounding typing rule. The beta, successor-case,
and fixpoint rules invoke the substitution result. `preservationMany` iterates
this argument over any finite trace.

{{include:src/PLFA/Part2/Properties.idr#preservation}}

Its context is arbitrary. Open well-typed programs also retain their types
when they take a step. Closedness is needed by progress, not by preservation.

### Progress and safety {#progress}

`Progress t` is constructive: either it holds a value derivation or it holds
an actual next term and a step derivation. `progress` takes the raw program
explicitly so that its computational result can contain that next program.
The typing derivation alone has erased term indices.

In an application, recursively inspect the function. If it steps, use `AppL`.
If it is a value, its arrow type forces it to be a lambda. Now inspect the
argument: it either steps by `AppR` or is ready for `Beta`. The helpers
`appProgress` and `caseProgress` express these canonical-form arguments.
There is no closed-variable case because `Fin 0` is empty.

{{include:src/PLFA/Part2/Properties.idr#progress}}

`valueNormal` proves that a value cannot step. `Normal t` says there is no step
to any target. The converse requires typing: `normalTypedIsValue` uses
progress to eliminate the hypothetical step. Finally, `safety` transports
typing along a supplied finite execution and proves that a normal endpoint is
a value. It neither promises an endpoint nor claims to decide divergence.

### Determinism {#determinism}

`deterministic` states that two steps from the same raw term have equal targets,
including on ill-typed or open terms. When the two derivations use the same
context rule, use induction. When one wants to evaluate a term that the other
requires to be a value, `valueNormal` gives a contradiction. The left-to-right
value premises are essential here.

{{include:src/PLFA/Part2/Properties.idr#determinism}}

## A total evaluator for a possibly diverging language {#evaluator}

A total host implementation cannot simply unfold arbitrary object-language
recursion until it ends. `evaluate` instead consumes fuel. At zero fuel it
returns the current program, the empty trace, and `OutOfFuel`. With fuel left,
it uses progress; after a step it uses preservation before recurring.

{{include:src/PLFA/Part2/Properties.idr#evaluator}}

Every result contains a genuine `Steps` derivation. `ReachedValue` also contains
a value proof. Exhaustion is inconclusive: even an initial value is reported
as exhausted if the supplied fuel is zero. Fuel measures this evaluator's
available inspections, not a theorem about the source program's running time.

### Checked computations {#computations}

`evaluateNatural` uses preservation along the returned trace before reading a
natural value. The tests compute addition and multiplication rather than
asserting arbitrary equalities about them. Both `Just` results have completed
value certificates; `Nothing` only reports exhaustion.

{{include:src/PLFA/Part2/Properties.idr#computations}}

## Pitfalls {#pitfalls}

- A preservation proof may use open substitution even though the evaluator
  accepts only closed programs. Weakening a lemma's scope too early makes the
  binder cases harder.
- Normal means unable to step, not necessarily a value. Zero applied to zero
  is normal and stuck.
- The object-language fixpoint has no totality promise. `%default total`
  checks the proof functions and fuelled evaluator, not every represented
  program.
- Preservation is one-way. The ignored ill-typed branch in `expansionSource`
  is a concrete reason its converse fails.
- Determinism chooses at most one next term; it says nothing about whether
  infinitely many such steps may occur.

## Exercises and checked solutions {#exercises}

1. **Typed divergence.** Give a term of any requested type that reduces to
   itself. Identify the typing and reduction rules used.
2. **Transport a derivation.** Starting with the typing of nested identity
   application, derive the type of its final numeral using the entire trace.
3. **A stuck raw term.** Prove zero applied to zero is normal but is not a
   value. Explain exactly which hypothesis prevents this example from
   contradicting progress.

{{include:src/PLFA/Part2/Properties.idr#solutions}}

The first solution is `loopType` with `loopStep`: the recursive body is its
own variable. The second is `nestedIdentityType`, which uses
`preservationMany`. The third consists of `stuckNormal` and `stuckNotValue`;
its missing ingredient is a typing derivation. The additional checked
`loopExhausts` computation above does not prove divergence by itself; the
self-step explains why this evaluator keeps consuming fuel.

## References and adaptation {#references}

Based on [PLFA, Properties](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/Properties.lagda.md)
by Philip Wadler, Wen Kokke, and Jeremy G. Siek, at frozen commit
`1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`,
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
General typed simultaneous substitution replaces named-variable drop/swap
bookkeeping. Preservation, closed progress, value normality, determinism,
safety along finite executions, and fuelled evaluation retain their substantive
scope. No theorem here asserts normalization. All included definitions and
reference solutions are checked by Idris2 0.8.0.

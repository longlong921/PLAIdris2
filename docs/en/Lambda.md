# Lambda: programs, binding, and reduction {#lambda}

## Motivation {#motivation}

A programming language definition separates three questions: what counts as a
program, what one execution step does, and which programs have a particular
type. Keeping these questions separate lets us state a useful theorem later:
execution cannot turn a well-typed program into an ill-typed one. If typing were
just a comment attached to an evaluator, there would be no independent claim to
prove.

Our language has functions, natural numbers, case analysis, and a general
recursion operator. It can express addition, multiplication, and nonterminating
programs. Evaluation is **weak, left-to-right call by value**: evaluate the
function, then its argument, then substitute the argument into the body. Do not
reduce inside a lambda merely because its body contains a redex.

PLFA introduces named variables here and replaces them with de Bruijn indices
later. This adaptation uses scoped indices immediately, while keeping typing
external. The distinction in [DeBruijn](DeBruijn.html#model) will be between a
raw term plus a separate typing derivation and a term whose type is part of its
representation. This change removes name-comparison bookkeeping; it does not
remove ill-typed programs or the need to prove preservation.

## Model {#model}

### Types, scopes, and binders {#binding}

`Ty` contains `TNat` and `Arr a b`. Arrows associate conceptually to the right:
a curried addition function has type ℕ → (ℕ → ℕ). A `Context n` is a vector of
`n` types, with the most recently bound variable at its head.

A `Raw n` may mention the `n` variables in its scope. `RVar` takes a `Fin n`, so
an out-of-scope index cannot be constructed. `FZ` means the nearest binder;
`FS FZ` means the next one out. For instance, λx. λy. x uses index one in its
body, whereas λx. λy. y uses index zero. Renaming the displayed letters has no
effect on either tree.

{{include:src/PLFA/Part2/Typed.idr#types}}

Binding is local to a constructor's indicated child:

| Constructor | Children with one additional variable | Meaning of that variable |
| --- | --- | --- |
| `RLam` | body | function argument |
| `RCase` | successor branch only | predecessor of the scrutinized number |
| `RFix` | body | the recursive program itself |

The zero branch of `RCase` has no new variable. In the successor branch, the
bound variable denotes the predecessor, **not** the entire successor. `RFix`
binds the whole recursive term, which need not be a value or a function.

### Substitution without capture {#substitution}

A renaming maps variables to variables. A simultaneous substitution maps
variables to terms. Both operations traverse every constructor, but must extend
their map when entering a binder.

{{include:src/PLFA/Part2/Typed.idr#maps}}

`liftRen` fixes the new index zero and shifts renamed old indices. `liftSub`
also fixes the new variable; an old replacement term is weakened by `rename FS`
before being moved under the binder. That shift prevents a free variable of
the replacement from becoming bound accidentally.

For example, substitute the outer variable `FZ` for the parameter in a body
λy. parameter. Inside λy, the parameter originally has index one. Its
replacement must also have index one after substitution: λy. outer. Returning
index zero would instead produce λy. y, a different program. We will check this
calculation explicitly in [DeBruijn](DeBruijn.html#exercises).

`single` replaces zero by the supplied argument and removes one binder from
all older variables. `instantiate body arg` is the resulting one-variable
substitution. It is defined for open as well as closed terms, and for arbitrary
arguments; the evaluation rules impose the separate value restriction where
needed.

### Typing is evidence {#typing}

`HasType gamma t a` is a derivation that raw term `t` has type `a` in `gamma`.
`TApp` requires the function's domain and the argument's type to agree.
`TCase` requires a natural-number scrutinee and branches with the same result
type. `TFix` checks its body under an additional assumption of its own result
type.

{{include:src/PLFA/Part2/Typed.idr#typing}}

A scope guarantees only that variable lookup makes sense. The closed raw term
zero applied to zero is still expressible, but has no typing derivation. A
closed lambda can have several external typings: the identity works at ℕ → ℕ
and also at (ℕ → ℕ) → (ℕ → ℕ). We have not implemented inference here.

### Small-step execution {#reduction}

Values are lambdas and numerals. In particular, `RSucc t` is a value only when
`t` is a value. `Step t u` records one reduction; `Steps t u` records finitely
many, including zero.

{{include:src/PLFA/Part2/Lambda.idr#dynamics}}

`AppL` evaluates the function. `AppR` starts the argument only after the
function is a value. `Beta` substitutes only a value. `CaseStep` evaluates the
scrutinee, then `CaseZero` selects the zero branch or `CaseSucc` substitutes the
predecessor. `Unfold` substitutes the fixpoint for its own bound variable and
has no value premise. Requiring a value there would prevent recursion from
unfolding at all.

## Worked examples {#examples}

`identityTwo` is a single beta step. In `plus`, the successor branch's context
is, from nearest to farthest: predecessor, second argument, first argument,
recursive function. The occurrence with three `FS` constructors therefore
selects the recursive function, and the occurrence with one selects the second
argument. Following this small context table is more reliable than counting
parentheses.

{{include:src/PLFA/Part2/Lambda.idr#examples}}

The accompanying typing derivations follow the same tree as the programs,
replacing each syntax constructor with a typing rule. This is a useful first
proof exercise: every recursive call in addition must consume two naturals,
and the successor branch must return a natural.

`churchTwo` represents two as repeated function application: given `s` and `z`,
it computes s (s z). Its type `(a → a) → a → a` differs from the built-in
natural type. An encoding is a program; it does not add a new constructor to
the language.

Multiplication recurses on its first argument and adds the second argument to
the recursive result. Its predecessor branch has the same four-variable
layout as addition.

{{include:src/PLFA/Part2/Lambda.idr#multiplication}}

For `(λx. x) ((λy. y) 2)`, the first step uses `AppR`, producing `(λx. x) 2`;
the second uses `Beta`, producing `2`. The checked `nestedIdentity` trace below
records exactly that order. Recursive arithmetic runs are checked in
[Properties](Properties.html#computations).

## What is established here? {#theorems}

`appendSteps` proves that two finite reduction traces can be composed.
`applicationSteps` lifts a trace through the function position of application;
it needs no argument-value premise because the function position evaluates
first. The example derivations establish the types of identity, addition,
multiplication, Church two, and the constant function.

These results do not yet prove that every well-typed closed program is a value
or can take a step, or that a step preserves typing. Those are separate general theorems in
[Properties](Properties.html#theorems). Nor does the definition of `Steps`
claim that every program has a finite trace ending in a value.

## Pitfalls {#pitfalls}

- `Raw 0` means closed, not well typed. Scope and type correctness are different
  invariants.
- A lambda is a value even if its body would diverge when called. These rules
  do not perform full beta reduction under binders.
- The `S` in a context size is a host natural-number constructor; `RSucc` is an
  object-language term constructor. Confusing the two mixes implementation and
  language.
- Substitute through a binder with `liftSub`, not the original map. Even a
  type-correct-looking example can otherwise capture a variable.
- A proof written `Refl` below proves a concrete definitional equality only.
  General semantic claims require their own arguments.

## Exercises and checked solutions {#exercises}

1. **Evaluation order.** Give the complete trace for identity applied to an
   identity application on two. Which rule justifies the first step?
2. **Outer variables.** Encode λx. λy. x and derive its type a → b → a. Explain
   why the variable has index one rather than zero.
3. **Scope versus type.** Prove that zero applied to zero has no typing
   derivation, even though the term is closed.

{{include:src/PLFA/Part2/Lambda.idr#solutions}}

Solutions are `nestedIdentity`, `constantType`, and
`zeroApplicationUntypable`. In the third solution, any proposed derivation
would have to contain a derivation giving zero an arrow type. The constructor
`TZero` can only produce `TNat`, so that case is impossible.

## References and adaptation {#references}

Adapted independently from Philip Wadler, Wen Kokke, and Jeremy G. Siek,
[PLFA, Lambda](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/Lambda.lagda.md),
frozen at commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Names are replaced early by scoped indices; named shadowing and name comparison
are explained through positions rather than implemented as string operations.
The language, weak call-by-value rules, external typing discipline, and general
recursion are retained. The checked Idris2 0.8.0 sources are linked by every
inclusion above; this is not an official PLFA edition.

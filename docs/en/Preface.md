# Preface

Imagine a tiny programming language with functions and natural numbers. An evaluator can run an expression. A type checker can reject some expressions. Neither fact alone tells us whether evaluation respects typing. To connect them, we need precise definitions and a proof. That is the central habit this book teaches.

## What you will learn {#learning}

Part 1 builds the language of proofs: data, induction, relations, equality, logical connectives, quantifiers and decisions. Part 2 uses those tools to define programming languages and reason about execution. Part 3 asks a different question: can we give a term a mathematical meaning that does not enumerate its execution steps? The final bridge relates those meanings to what a surrounding program can observe.

The chapters follow the exact order of the frozen [PLFA table of contents](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/data/tableOfContents.yml). There are three preliminary chapters, ten logical-foundations chapters, nine operational-semantics chapters, five denotational-semantics chapters, the substitution appendix, and two closing chapters. Idris2 syntax, quantitative types and trust are collected in a separate extension section. You can consult them when needed without changing the main reading sequence.

## How to read a checked proof {#reading}

Read a theorem's type before its implementation. Separate inputs that are ordinary data from inputs that are evidence. Then ask which input becomes smaller in a recursive call. For example, a proof about every natural number may recurse on the number; a proof about every reduction may recurse on a derivation of that reduction. These are different inductions.

Try the worked example by hand before running it. When a proof is short, resist the temptation to skip its explanation: a one-line constructor can encode several choices made by the type checker. When a proof is long, use the named intermediate lemmas as landmarks. You can inspect the complete source through the link above each included block.

Each technical chapter supplies exercises and reference solutions. Attempt the exercises before reading their solution symbols. There are no unfinished exercise holes in the reference build. Negative tests are kept separately because their job is to fail: a proof checker should reject an invalid proof as reliably as it accepts a valid one.

## Two languages, one development {#languages}

English and Chinese chapters share the same definitions, theorem hypotheses, exercise numbering, source inclusions and section identifiers. The language button goes to the corresponding chapter and carries the current fragment. A translated heading may sound different; the mathematical claim must not change.

The explanation is written for a reader comfortable with functions, recursion and elementary algebra. Prior Agda knowledge is unnecessary. Some Part 3 proofs are demanding. Their difficulty comes from higher-order computation, substitution and finite information—not from requiring you to memorise terse syntax. Pause at a lemma, work its smallest case, and return to the theorem that needs it.

## What “checked” means here {#checked}

Our reference definitions and proofs are checked by pinned Idris2 0.8.0 under a totality requirement. This is evidence relative to the host compiler and its implementation of dependent types; it is not a proof that Idris2 itself is a consistent foundational logic. In particular its universe implementation uses `Type : Type`. The [Trust extension](Trust.md) explains the boundary and the checks we actually perform.

The object language is distinct from its host. Untyped lambda terms can diverge. A total function that examines a finite derivation, or runs for a bounded amount of fuel, does not make all object-language programs terminate. Likewise, confluence says that two finite reduction paths can be joined; it does not promise a normal form for every term.

## Attribution and adaptation {#attribution}

This independent work adapts the organisation and mathematical development of *Programming Language Foundations in Agda* by **Philip Wadler, Wen Kokke and Jeremy G. Siek**, under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). It is not an official edition and does not imply their endorsement.

The upstream snapshot is commit `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb` on `dev`, dated 3 September 2026 and retrieved 22 October 2026. The upstream release label remains `v22.08`; the exact commit, not that label, identifies our baseline. We rewrote the exposition, implemented the material in Idris2, added paired Chinese and English text, and documented representation choices. Chapter review records state departures explicitly. The adaptation is also licensed CC BY 4.0.

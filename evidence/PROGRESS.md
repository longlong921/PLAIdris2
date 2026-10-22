# Progress — 2026-10-22

## Preserved work and environment

- Target cloned at /workspace/PLAIdris2; remote still empty main at recovery check.
- ctp-hs remained unchanged and clean during read-only inspections.
- PLFA frozen at 1c39b1e82caa4283274e64ba58c3bc3c9ab781eb, CC BY 4.0; exact ordered mapping and license preserved.
- Nix portable initially failed inside the outer sandbox; approved local bwrap execution resolved it. All package state is inside this repository's ignored .cache.
- Idris2 0.8.0, Python 3.13.15, Node 24.21.0 and Markdown 3.10.2 confirmed. Browser QA shell is pinned by the same flake lock.
- Astra max chapter agents were interrupted by an account/tool-review usage limit. Existing files were preserved. The user's resume instruction restored work without model substitution.

## Implementation and review milestones

- All Part1, Part2, Part3, appendix and extension modules passed their owner checks and the final whole-book checks.
- Genuine full-beta confluence, finite-information denotational semantics, compositionality, soundness, adequacy and contextual equivalence implemented and individually checked.
- Independent audit caught missing full-beta normalization and the inverse closure correspondence; both were added and checked, with closure versions of adequacy.
- All 25 core chapter pairs were independently read against the source and reviewed scope. All 10 recorded findings were resolved, including the Equality chapter's incorrect universe description; both languages now explicitly state the pinned host's Type : Type limitation.
- The final executable suite passed 34 scenarios, including typed recursion, inference-to-intrinsic evaluation, bidirectional rejection, CBN Omega/unused argument, full Church/Scott normalization and QTT examples.
- Negative test runner setup errors (source root and import search root) were diagnosed and fixed. The final suite rejected all ten deliberately invalid files for the intended reasons.
- The static site has 69 pages from 33 paired chapters. The whole-book check verified 4,151 local links/assets, fragments, language navigation and actual rendered source blocks.
- Pinned Chromium verified all 33 chapter language round trips and mobile menu, search, fragments and layout. All 36 external reference URLs returned HTTP 200.

## Local acceptance checkpoint before publication

- The complete command passed at 2026-10-22T19:20:14 UTC. All 32 reference source hashes and logs are archived under evidence/acceptance.
- The documented per-chapter command was exercised with Adequacy and passed.
- A fresh nix flake check passed on x86_64-linux (37-second build phase); nix build then reused the same checked derivation and produced the static site.
- Final logs, input hashes, source-extraction manifest and desktop/mobile screenshots were preserved. See ACCEPTANCE.md for commands, results and untested platforms.
- The remote remained empty at the prepublication read. The next gate is committing/pushing main, verifying the exact remote SHA and its GitHub Actions run. This is a historical local checkpoint; remote publication results are recorded separately.

No deployment or Pages setting changes are part of delivery. ctp-hs remained clean.

## Publication checkpoint

- Source commit 506b8e77140c9773f05b1dcd138025a815458f3e was pushed to main. A fresh remote read returned exactly the same SHA.
- Its push-triggered workflow 39840132740 and job 120038662836 completed successfully; the full Nix build took 44 seconds in CI. Actual source, link and runtime check output is archived in acceptance/first-remote-build.log.
- The successful run reported an obsolete checkout Node runtime and a moving ubuntu-latest label. The follow-up pins checkout v7.0.1 by commit and the runner to ubuntu-24.04, and records the actual publication evidence. Book source, manuscripts and tests are unchanged.
- The follow-up's exact remote SHA and complete CI result are recorded by its own GitHub Actions run and checked before final handoff. The first successful run is retained as historical evidence, not substituted for that later result.

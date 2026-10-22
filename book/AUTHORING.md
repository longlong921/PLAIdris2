# Editorial and implementation contract

All work is confined to `/workspace/PLAIdris2`. The reference checkout
`/workspace/PLFA-upstream` is read-only. Do not touch ctp-hs or other projects.

The upstream freeze is commit 1c39b1e82caa4283274e64ba58c3bc3c9ab781eb
(PLFA dev, 2026-09-03), retrieved 2026-10-22. Its CC BY 4.0 license is
copied verbatim to LICENSE. Authors: Philip Wadler, Wen Kokke, Jeremy G. Siek.
This is an independent adaptation, not an official PLFA edition.

## Delivery contract

- Modules live under src/PLFA/Part1, Part2, Part3, Appendix or Extensions.
  Every reference module uses `%default total`. No holes, postulates, unsafe
  casts, `believe_me`, `assert_total`, or unproved theorem fields in place of proofs.
- Idris2 0.8.0 from the pinned Nix flake. Check with `idris2 --source-dir src
  --check src/PLFA/...idr`; shared output in build, no per-chapter copies.
- Body files: docs/en/CHAPTER.md and docs/zh/CHAPTER.md. Same semantic chapter
  ID, definitions, hypotheses, theorem scope, exercise numbers, stable anchors.
- Use explicit Markdown heading IDs: `## Motivation {#motivation}`, then
  `model`, `examples`, `theorems`, `pitfalls`, `exercises`, `references`.
  Chinese headings use the same IDs. More headings are welcome with matched IDs.
- Source inclusion syntax on a line by itself:
  `{{include:src/PLFA/Part1/Naturals.idr}}` or
  `{{include:src/PLFA/Part1/Naturals.idr#region-name}}`.
  Regions use `-- region region-name` / `-- endregion region-name` lines.
  All displayed Idris code must come from source inclusions, never copied fences.
- Explain motivation, definitions, worked reductions/proofs, core theorems and
  proof ideas, pitfalls, 2+ meaningful numbered exercises, checked reference
  solutions. Avoid generic boilerplate. Text must be self-contained for learners.
- Preserve real PLFA theorem scope. In particular full untyped beta reduction,
  confluence, weak call-by-name big-step semantics, finite-information
  denotational semantics, compositionality, soundness, adequacy and contextual
  equivalence must not be replaced with trivial finite/typed/refl toy versions.
- Record exact deviations and remaining proof work in evidence; never describe
  an unchecked or unfinished result as checked. Compilation is not itself a
  proof of the host compiler's soundness.
- Each chapter owner writes book/review-CHAPTER.json with `chapter`, `sources`
  (paths), `core_claims` (names and exact scope), `exercises` (id and solution
  symbol), `upstream` (path), `deviations` and `checked` fields. The primary
  editor independently verifies claims and updates the final acceptance record.

## Shared untyped interface

The Untyped owner and Part 3 owners must agree the syntax/substitution and
operational interface immediately, before dependent proofs are written.
Prefer intrinsically scoped de Bruijn terms and pointwise equality of maps;
do not assume function extensionality. Keep semantic choices explicit.

## Work plan and acceptance gates

1. Freeze upstream commit, license and exact ordered mapping (before chapters).
2. Pin Nix tools and make the compiler runnable. Freeze shared term interfaces.
3. Implement and explain every mapped chapter in matching English and Chinese.
4. Independently review theorem hypotheses, proof scope, exercises and translation.
5. Run source audit, mapping/parity checks, all module compilation, executable
   examples, wrong-proof rejection tests, static build, local links, language
   switch including fragment preservation. Retain logs and actual outcomes.
6. Commit and push main only if remote is still empty. If it acquires work,
   preserve it and use a branch plus draft PR. Verify remote SHA and CI.

No deployment or GitHub Pages setting changes are part of this task.

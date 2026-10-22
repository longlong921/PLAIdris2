# Acknowledgements

The intellectual structure of this book comes from *Programming Language Foundations in Agda* by **Philip Wadler, Wen Kokke and Jeremy G. Siek**. Their decision to expose definitions and proofs as executable material makes this adaptation possible. The [upstream contributors](https://github.com/plfa/plfa.github.io/graphs/contributors) have improved that work over many years.

## What has been adapted {#adaptation}

We retain PLFA's chapter order and core mathematical progression. The host language is Idris2, the explanation is newly written in English and Chinese, and representation choices are made explicit where Idris2 calls for different engineering. The frozen upstream commit and per-chapter file hashes are recorded in `book/upstream.json` and `book/chapters.json`. The upstream license is preserved verbatim in `LICENSE`.

This is an independent adaptation under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/). It is not endorsed by or maintained on behalf of the PLFA authors. Please preserve attribution and identify your own changes when adapting this work further.

## Tools and review {#tools}

The implementation uses the work of Edwin Brady and the Idris community, the Nix community's reproducible toolchain, Python-Markdown for the reading site, and Node for compiled examples and interaction tests. System fonts keep the site self-contained; we do not redistribute a proprietary font.

This edition was prepared with Astra max agents at the user's request, with chapter ownership and a separate scope review. Generated material is treated as a proposal until it survives compiler checks and editorial review. Neither the model name nor the amount of text is evidence that a mathematical claim is correct. The source and validation records are the inspectable deliverables.

Corrections are welcome through [the repository](https://github.com/longlong921/PLAIdris2). A useful report names the chapter and language, states the claim in question, and gives a small counterexample or failing check where possible.

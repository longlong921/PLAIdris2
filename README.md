# Programming Language Foundations in Idris2

**[中文入门](docs/zh/GettingStarted.md) · [English getting started](docs/en/GettingStarted.md)**

**[中文前言](docs/zh/Preface.md) · [English preface](docs/en/Preface.md)**

沿着 PLFA 的原章节顺序，用 Idris2 学习逻辑、类型系统、操作语义和指称语义。中英文章节一一对应，静态阅读站可以切换到同一章、同一节。Idris2 语法、QTT 与可信边界独立放在扩展区。

An independent bilingual adaptation of PLFA, with source-linked explanations and Idris2 proofs. The reading site preserves the chapter and section when switching languages. The original table of contents stays intact; Idris2-specific extensions are separate.

## 阅读与检查 · Read and check

先安装 [Nix](https://nix.dev/install-nix)，启用 `nix-command`、`flakes`。Install Nix with those features enabled, then run from this checkout:

```sh
# 完整检查 / Full check
nix develop --command python3 tools/check.py

# 按章检查 / One chapter and its imports
nix develop --command python3 tools/check.py --chapter Naturals

# 构建阅读站 / Build the reading site
nix develop --command python3 tools/build.py

# 本地预览 / Serve locally
nix develop --command python3 -m http.server 8000 --bind 127.0.0.1 --directory dist
```

打开 [中文阅读入口](http://127.0.0.1:8000/zh/index.html) 或 [English reading entry](http://127.0.0.1:8000/en/index.html)，先保持预览命令运行。源码 Markdown 内的引用指令会在构建时展开；阅读完整代码块请使用生成的站点。

Keep the preview command running, then open either entry above. Source Markdown contains code-inclusion directives; the built site expands them directly from the checked `.idr` files. No public deployment or GitHub Pages configuration is required.

`nix build` produces the checked site in `result/`; `nix flake check --print-build-logs` runs the same immutable check derivation. Linux users can also run the real-browser suite after building:

```sh
nix develop .#browser --command python3 tools/browser_test.py
```

工具链由 `flake.nix` 与 `flake.lock` 锁定：Idris2 **0.8.0**、Python/Markdown、Node，以及可选浏览器测试环境。所有命令复用一个 `build/`，不按章节复制环境。实际验收平台与结果见 [evidence/ACCEPTANCE.md](evidence/ACCEPTANCE.md)；一次新检查的详细日志写入 `build/checks/`。

The flake pins Idris2 **0.8.0** and the build tools. Compiler acceptance, executable tests, deliberate proof rejection, source extraction, links and language behavior are checked separately. [Acceptance evidence](evidence/ACCEPTANCE.md) records actual results and limitations; new run logs go to `build/checks/`.

## 原目录 · Original order

| 部分 / Part | 章节 / Chapters |
| --- | --- |
| Front matter | Dedication → Preface → Getting Started |
| Part 1 | Naturals → Induction → Relations → Equality → Isomorphism → Connectives → Negation → Quantifiers → Decidable → Lists |
| Part 2 | Lambda → Properties → DeBruijn → More → Bisimulation → Inference → Untyped → Confluence → BigStep |
| Part 3 | Denotational → Compositional → Soundness → Adequacy → ContextualEquivalence |
| Appendix | Substitution |
| Back matter | Acknowledgements → Fonts |
| Separate extensions | Idris2 Primer → QTT → Trust |

冻结记录与逐章映射：[upstream.json](book/upstream.json)、[chapters.json](book/chapters.json)。实质定理范围与独立审查：[scope baseline](book/scope-baseline.json)、[scope audit](evidence/scope-audit.md)。参考源码位于 `src/PLFA/`；刻意不通过的例子独立放在 `tests/negative/`，不混入参考实现。

## 数学与宿主边界 · Mathematical and host boundaries

参考源码要求总性，不含未解决的洞或证明逃逸。对象语言仍可发散：无类型项 `Ω` 的不收敛有单独证明，燃料耗尽本身不等于发散。完整 β 正规化、弱按名求值与闭包求值各自定义并通过定理连接。

Total host definitions do not assert that every object-language program terminates. The book distinguishes full beta reduction, weak call-by-name evaluation and closure evaluation. Its proofs are relative to the pinned Idris2 implementation; Idris2 0.8.0 uses `Type : Type`, so this is not a claim of foundational consistency of the host. See [Trust / 可信边界](docs/en/Trust.md) and [中文版](docs/zh/Trust.md).

## 署名与许可 · Attribution and license

本书依据 **Philip Wadler、Wen Kokke、Jeremy G. Siek** 所著 [*Programming Language Foundations in Agda*](https://plfa.github.io/) 改编，采用 [CC BY 4.0](LICENSE)。上游固定为提交 [`1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`](https://github.com/plfa/plfa.github.io/tree/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb)，取得日期 2026-10-22。

This is an independent adaptation, not an official edition or an endorsement by the PLFA authors. Changes include newly written English/Chinese exposition, Idris2 implementations, explicit representation and trust-boundary explanations, and a new static site. Attribution, the full upstream license and the adaptation's CC BY 4.0 license are preserved. See [NOTICE](NOTICE).

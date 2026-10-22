# 验收记录 · Acceptance record

本记录对应 2026-10-22 的实际执行，平台为 **x86_64-linux**。全量本地检查、隔离 Nix 构建和浏览器检查均通过；没有未完成的核心证明。章节篇数只用于核对目录，数学范围依据逐章命题、源码和独立审校判断。

This records actual runs on **x86_64-linux**, dated 2026-10-22. The complete local suite, isolated Nix build and browser checks passed. No core proof obligation remains open. Chapter counts establish coverage of the table of contents; theorem scope is assessed from the actual propositions, implementations and independent review.

## 结果 · Results

| 检查 / Check | 实际结果 / Actual result | 证据 / Evidence |
| --- | --- | --- |
| Upstream freeze and license | All 30 frozen source hashes match; upstream CC BY 4.0 license retained verbatim | [Upstream verification](upstream-verification.json), [mapping](../book/chapters.json), [NOTICE](../NOTICE) |
| Original order and extensions | Exact original 30-entry order; 3 Idris2 extensions remain separate | [Full summary](acceptance/checks/summary.json), [chapter map](../book/chapters.json) |
| Mathematical scope and translation | All 25 core technical chapters reviewed in both languages; ten recorded findings resolved | [Scope audit](scope-audit.md), [baseline](../book/scope-baseline.json), `book/review-*.json` |
| Idris reference implementation | All 32 modules checked with Idris2 0.8.0; total defaults; no unresolved holes or audited proof escapes | [Compiler](acceptance/checks/compiler.log), [module list and hashes](acceptance/checks/summary.json), individual module logs in the same directory |
| Executable examples | 34 scenarios passed using the Node backend | [Build](acceptance/checks/runtime-build.log), [runtime output](acceptance/checks/runtime.log), [runner](../src/Main.idr) |
| Deliberately invalid proofs | All 10 rejected with the expected type, quantity, coverage or termination diagnostic | [Cases](../tests/negative/cases.json), [negative logs](acceptance/checks/) |
| Per-chapter interface | `--chapter Adequacy` passed with its imported dependencies | [Per-chapter summary](acceptance/checks-adequacy/summary.json) |
| Static site and local links | 69 HTML pages; 4,151 local links/assets checked, including fragments and paired navigation | [Full summary](acceptance/checks/summary.json) |
| Displayed code | Rendered source blocks, extracted region hashes and downloadable sources match the actual reference source | [Snippet manifest](acceptance/snippets.json), [checker](../tools/check.py) |
| Language-switch behavior | Node tests exercised the actual hash-change handler and all paired chapter targets | [Behavior log](acceptance/checks/site-behavior.log) |
| Real browser | Chromium 154.0.8037.97: all 33 chapter pairs switched EN → ZH → EN; section fragments, mobile menu/search/layout passed; no JavaScript errors | [Browser report](acceptance/browser/summary.json), screenshots below |
| External references | 36 distinct public HTTP(S) URLs returned HTTP 200, following redirects | [URL results](acceptance/external-links.json) |
| Isolated Nix validation | `nix flake check` exited 0 after a fresh build; `nix build` exited 0 and reused that checked derivation | [Nix result](acceptance/nix-result.json), [check log](acceptance/nix-check.log), [build log](acceptance/nix-build.log) |

运行示例覆盖算术与二进制、列表、外在与内在类型的递归求值、扩展语言构造、带失败证据的类型判定、类型推导到求值的完整路径、弱按名求值、完整 β 归约下的 Church/Scott 算术，以及 QTT 和宿主总性边界。源码中以 `Refl` 等表达的封闭计算例子也随模块编译接受计算检查。34 个运行场景不是对任意输入定理的替代。

Runtime scenarios cover arithmetic and binary representations, lists, extrinsic/intrinsic typed recursion, extended constructs, positive and negative type inference, the inference-to-evaluation pipeline, weak call-by-name, full-beta Church/Scott arithmetic, QTT and the host/object boundary. Closed equality examples are additionally checked by computation during module checking. The 34 scenarios do not replace the universally quantified proofs.

核心结果包括保持与进展、类型化替换、真正的双向模拟、完整 β 合流、闭包与替换式求值双向对应、有限信息指称语义的组合性与健全性、闭项充分性，以及语义相等蕴含上下文等价。具体前提和表示调整均见逐章记录；没有用定长燃料测试替代这些命题。

Core results include preservation/progress, typed substitution, genuine bidirectional simulation, full-beta confluence, both closure/substitution evaluation correspondences, compositionality and soundness of finite-information denotations, closed-term adequacy, and semantic equality implying contextual equivalence. Exact hypotheses and representation choices are recorded chapter by chapter; bounded tests do not stand in for these results.

## 复现 · Reproduce

Run from the repository root with Nix's `nix-command` and `flakes` features enabled:

```sh
nix develop --command python3 tools/check.py
nix develop --command python3 tools/check.py --chapter Adequacy
nix flake check --print-build-logs
nix build

# Local reading site / 本地阅读站
nix develop --command python3 tools/build.py
nix develop --command python3 -m http.server 8000 --bind 127.0.0.1 --directory dist
```

Open `http://127.0.0.1:8000/`. Stop the preview with Ctrl-C. The browser and external-reference checks are separate from the offline Nix derivation:

```sh
nix develop .#browser --command python3 tools/browser_test.py
nix develop --command python3 tools/external_links.py
```

`flake.lock` fixes nixpkgs at `7c8764b7c7b09b34f632464276218ef9090eaa11`. Observed tools: Idris2 0.8.0, Python 3.13.15, Markdown 3.10.2 and Node 24.21.0. The cloud environment used an isolated Nix-portable/bwrap wrapper; that wrapper is an environment convenience and is not needed on a normal Nix installation. The portable store and all compiler/build caches are excluded from Git.

The [input snapshot](acceptance/input-snapshot.json) records release input hashes, excluding evidence files to avoid self-reference. The single-chapter run predates the final runtime-runner addition; its Adequacy source is unchanged. The full-suite snapshot is authoritative for the final reference source. Logs record checks actually performed, not promised future checks. GitHub's [Actions history](https://github.com/longlong921/PLAIdris2/actions/workflows/check.yml) records the exact remote commit and result of each push-triggered Nix check.

## 范围与限制 · Scope and limits

- 本次未运行 / **Not run:** aarch64-linux, x86_64-darwin and aarch64-darwin builds; Firefox/WebKit; Idris backends other than Node for the executable suite. Declaring flake outputs for a platform is not evidence of testing it.
- 外链检查验证 URL 可达性，不验证外部页面锚点或其全部内容。External checks establish URL reachability, not the correctness of external fragment identifiers or source content. Local chapter fragments were checked.
- 证明依赖固定的 Idris2 实现及其可信边界，包括 `Type : Type`。Compiler acceptance does not establish the host's foundational consistency or compiler correctness. See [Trust](../docs/en/Trust.md) / [可信边界](../docs/zh/Trust.md).
- 无类型对象语言允许发散。燃料耗尽不是发散证明；Ω 的不收敛有独立推导。The total host functions do not imply termination of all lambda terms. Full-beta reduction, weak evaluation and closure evaluation are distinguished and connected by theorems.
- 未假设函数外延性；相关结论明确使用逐点逆律或逻辑等价。Function extensionality is not postulated. The scope records distinguish these adaptations from intensional function equality. Normal-order standardisation remains an explanatory upstream fact rather than an additional formal theorem; no full-abstraction converse or general product-encoding simulation is claimed.
- 未公开部署、未更改 Pages 设置。No public deployment or GitHub Pages setting change was performed. The separately supplied `ctp-hs` checkout remained clean and untouched.

此前的工具运行限制、负测试导入路径错误，以及审校发现的缺口均已解决；见 [阶段记录](PROGRESS.md) 和 [审校记录](scope-audit.md)。There is no outstanding local validation failure. The prior runtime setup, test-runner import configuration and review findings were corrected before the successful final gates.

## 阅读截图 · Reading screenshots

[中文桌面章节 / Chinese desktop chapter](acceptance/browser/desktop.png) · [英文目录 / English contents](acceptance/browser/contents.png) · [手机阅读 / Mobile reading](acceptance/browser/mobile.png)

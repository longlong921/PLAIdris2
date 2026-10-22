# Acknowledgements · 致谢

本书的思想结构来自 **Philip Wadler、Wen Kokke 与 Jeremy G. Siek** 所著 *Programming Language Foundations in Agda*。他们将定义与证明公开为可执行材料，使本改编成为可能。[上游贡献者](https://github.com/plfa/plfa.github.io/graphs/contributors)多年来不断完善了这项工作。

## 改编了哪些内容 {#adaptation}

我们保留 PLFA 的章节顺序与核心数学递进，改用 Idris2 作为宿主语言，重新撰写中英文讲解，并在 Idris2 需要不同工程处理时明确说明表示选择。`book/upstream.json` 与 `book/chapters.json` 记录冻结的上游提交及逐章文件哈希，`LICENSE` 完整保留上游许可证。

本书是遵循 [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/) 的独立改编，不代表 PLFA 作者维护，也不暗示得到其认可。进一步改编时，请保留署名并说明你所作的修改。

## 工具与审查 {#tools}

实现依赖 Edwin Brady 与 Idris 社区的工作、Nix 社区提供的可复现工具链、用于阅读站的 Python-Markdown，以及用于运行例子和交互测试的 Node。站点使用系统字体，保持自包含，不分发专有字体。

按照用户要求，本版使用 Astra max 智能体分章编写，并安排独立范围审查。生成内容在通过编译检查和编辑审阅之前，均视为待验证的候选。模型名称和文本数量都不能证明数学命题正确；可供检查的交付物是源码与验证记录。

欢迎通过[仓库](https://github.com/longlong921/PLAIdris2)提出更正。有效的问题报告应注明章节、语言和存疑命题，并尽可能附上小反例或失败的检查。

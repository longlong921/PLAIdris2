# 上下文等价 {#contextual-equivalence}

## 动机 {#motivation}

编译器优化会替换大程序中的一个部分。只知道两个表达式单独运行时都会收敛，还不够：外围程序可能把它们应用到参数、放在绑定者之下，或者把它们当作另一个函数的参数。有效替换必须在每个允许的外围程序中保持观察结果。

上下文等价直接表达这一要求。它量化所有能够闭合程序的上下文，并比较最终闭程序是否收敛。从定义直接证明这个性质很费力。前面建立语义理论的目的，就是提供一个可组合的方法：先证明两个表达式含义相等，再由定理得到上下文等价。

## 模型 {#model}

`Ctx n 0` 是一个单孔语法上下文：它接收具有 `n` 个可用变量的项，产生闭项。构造子包括孔、在上下文外加 lambda、把上下文放在应用左侧，以及把上下文放在应用右侧。填孔操作从构造上就保证作用域正确。闭合程序的绑定者可以绑定被填入开放项的变量；索引明确规定哪些变量被绑定。

`ContextuallyEquivalent left right` 对**每个**闭合上下文提供两个证据转换：填入左项后收敛，推出填入右项后收敛；反方向也成立。它不判定收敛或发散。如果一方不可能收敛，适当方向的蕴含也会排除另一方的收敛。

模块还定义 `Terminates`，即存在到达 lambda 的完整 beta 归约，以及采用这种观察的 `BetaContextuallyEquivalent`。充分性已经证明，对于闭项，这两种观察一致。把两个定义都列出来，有助于区分归约关系与具体求值策略。

{{include:src/PLFA/Part3/ContextualEquivalence.idr#observations}}

## 具体例子 {#examples}

对于每个开放函数体和参数，`(lambda x. body) arg` 都可以替换为避免捕获的 beta 归约结果。证明不局限于顶层求值：`betaReplacement` 量化所有闭合上下文，包括把表达式放到 lambda 之下或参数位置的上下文。

`openBetaReplacement` 把这个结论用于开放表达式 `(lambda x. x) #0` 与变量 `#0`。上下文 `closingBinder` 绑定这个变量，产生闭程序 `lambda z. ((lambda x. x) z)` 和 `lambda z. z`。上下文等价允许这种有意的绑定；它不是错误替换函数造成的意外捕获。

被忽略参数给出一个实用的优化例子。`(lambda x. lambda y. y) A` 在任意上下文中都可以换成恒等函数，即使 `A` 发散也成立。健全性通过底信息处理消失的参数。这个定理针对本书定义的纯按名语言，并不授权我们在无关语言中删除副作用。

最后一个例子说明，为何必须指定观察是什么。η 展开 `lambda x. Omega x` 是 lambda，因此立即收敛。`Omega` 本身不收敛。仅用空上下文就能区分二者。因此，一般的 η 规则对于本章弱头观察并不健全。

{{include:src/PLFA/Part3/ContextualEquivalence.idr#examples}}

## 定理与证明结构 {#theorems}

设开放表达式 `left` 与 `right` 语义相等，任取一个闭合上下文。组合性把相等关系提升为两个填孔后闭程序的语义相等。如果第一个收敛，健全性与求值到归约定理说明，它具有信息 `Arrow Bottom Bottom`。提升后的语义相等把这个箭头信息传给第二个程序。充分性于是提供第二个程序的按名收敛见证。

这就是 `denotEqualConverges`。它使用 Adequacy 中的证据转换 `equalPreservesConvergence`；该辅助函数包含的正是上面的健全性与充分性论证。把语义相等反向使用，就证明另一方向。`contextualEquivalence` 为任意上下文打包这两个方向。

{{include:src/PLFA/Part3/ContextualEquivalence.idr#replacement}}

对于完整 beta 表述，`denotEqualTerminates` 先把已有的、到达 lambda 的归约转换为按名收敛；经过上下文的语义相等传递收敛后，再把新的求值见证转回 beta 序列。`betaContextualEquivalence` 同样把这个转换与对称版本配成一对。输入归约序列不需要遵循某个固定策略。

各结果之间的依赖值得说清楚。组合性处理外围语法；健全性把已有的操作语义成功转成有限语义信息；充分性再把这些信息转成替换后程序的操作语义成功。省去充分性，最后一步就没有依据。省去健全性中的反映方向，则无法从观察到的结果把信息传回原程序。

## 易错点 {#pitfalls}

- 只有顶层收敛性相同还不够。两个 lambda 都能立即收敛，但上下文可以应用它们，区分它们的行为。
- 被量化的上下文必须闭合程序。定理通过这些上下文覆盖开放表达式，没有把自由变量假装成闭合可执行程序。
- 观察是存在 lambda 结果，不要求打印出来的函数体相同，也不要求归约步数相同。
- 定理证明语义相等推出上下文等价。它没有证明反方向；后一性质通常属于完全抽象性问题。
- Beta 替换有依据，不受限制的 η 替换则没有：`etaNotContextual` 为这里的确切观察给出经检查的反例。

## 习题与已检查解答 {#exercises}

1. **C1 — 在 lambda 之下替换。** 证明 `lambda z. ((lambda x. x) z)` 与 `lambda z. z` 上下文等价，包括把它们放入任意更外层闭合上下文的情形。参考解答：`underBinderReplacement`。用 `reduceReplacement` 把论证推广到任意有限完整 beta 归约。
2. **C2 — 复合优化。** 如果 `left` 与 `middle` 上下文等价，`middle` 与 `right` 上下文等价，证明 `left` 与 `right` 上下文等价。在每个上下文中分别复合两个方向的证据。参考解答：`contextualTransitive`；`contextualReflexive` 与 `contextualSymmetric` 补齐等价关系的其他性质。
3. **C3 — 排除无条件 η。** 使用孔上下文证明 `Omega` 与 `lambda x. Omega x` 不上下文等价。假想的等价关系会把后者的收敛传回 `Omega`，与 `omegaNoEval` 矛盾。参考解答：`etaNotContextual`。

{{include:src/PLFA/Part3/ContextualEquivalence.idr#exercises}}

## 参考与改编说明 {#references}

改编自 Philip Wadler、Wen Kokke 和 Jeremy G. Siek 的 [PLFA：ContextualEquivalence](https://plfa.github.io/ContextualEquivalence/)，冻结提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用 CC BY 4.0 许可。上游以完整 beta 归约到 lambda 的可达性定义上下文等价。本版以 `betaContextualEquivalence` 证明这一表述，并以 `contextualEquivalence` 额外展示等价的、基于替换的弱按名表述。二者都量化任意作用域正确的闭合上下文。η 反例与显式的等价关系习题是本版补充；本章没有声称上下文等价反过来推出语义相等。

# 充分性 {#adequacy}

## 动机 {#motivation}

健全性说明归约保持含义。充分性则从含义回到可观察的计算：一个具有有限函数信息的闭项，确实会通过弱按名求值收敛到 lambda。这不是“每个 lambda 项都终止”的定理；它的语义前提恰好提供了收敛所需的证据。

我们的观察是到达一个外层 lambda，报告成功前不进入函数体。因此，虽然 `lambda x. Omega` 的函数体发散，这个项在本章意义下仍然收敛。另一方面，`Omega` 自身没有这样的结果。ContextualEquivalence 一章采用的正是这种观察。

## 模型 {#model}

`Converges term` 打包一个函数体和一份有限的 `Eval term (Lam body)` 推导。`Eval` 来自 BigStep，是基于替换的弱按名求值关系：lambda 求值为自身；应用先求值函数，再把原始的、尚未求值的参数代入函数体并求值。项是闭合的，所以最终函数体可以使用一个绑定变量，没有自由变量。

`HasFunction term` 打包箭头近似 `Arrow a b` 及其在空环境中的语义推导。输入和输出近似可以是任意有限值。特别地，`Arrow Bottom Bottom` 已经足够：它记录该项是一个函数，但不要求函数体提供任何行为信息。

{{include:src/PLFA/Part3/Adequacy.idr#observation}}

这两个谓词都不是判定程序。它们的成员是有限证据。二者等价意味着可以双向转换这些证据，并不意味着能判定任意项是否满足它们。

## 具体例子 {#examples}

恒等函数具有信息 `Arrow Bottom Bottom`：进入 lambda 后，对函数体使用底规则即可。`functionConverges` 把这份语义证据转为实际求值推导。同样的论证也证明 `lambda x. Omega` 收敛，因为弱求值不会进入它的函数体。

考虑 `(lambda x. lambda y. y) A`。内层 lambda 提供 `Arrow Bottom Bottom`；外层 lambda 提供 `Arrow Bottom (Arrow Bottom Bottom)`；参数提供 `Bottom`。应用规则于是给出整个应用的函数信息。`constantIgnoresArgument` 证明它对**每个**闭参数都收敛，包括 `Omega`。

所有项都具有信息 `Bottom`，`Omega` 也不例外。因此，仅凭底不能推出收敛。`bottomIsNotEnough` 构造底判断；`omegaHasNoFunction` 则证明，任何假想的 `Omega` 箭头判断都会导致矛盾。它使用 BigStep 的 `omegaNoEval`：这个自我重现的应用若有求值推导，其中就会包含一份严格更小的自身求值推导。证明排除的是有限推导，并没有运行无限求值器。

## 定理与证明结构 {#theorems}

### 记录函数行为的关系 {#logical-relation}

如果只证明“箭头信息推出某个 lambda 结果”，应用分支的归纳假设就太弱。得到函数的 lambda 体之后，我们还必须知道：把它应用于适当参数，会实现期望的输出信息。`Realizes` 同时记录这两件事。

- `Realizes Bottom term` 不提出任何要求。
- 实现一个并，表示同一个项同时实现两个分量。
- 实现一个箭头，表示该项求值到某个确定的 lambda，而且把任何实现输入信息的项代入其函数体后，都能实现输出信息。

定义递归处理有限信息值，所关联的项却可以发散。它是一个返回类型的函数，因此箭头分支中的函数参数依靠较小输入信息值上的结构递归来定义；我们没有引入负递归的数据类型。

{{include:src/PLFA/Part3/Adequacy.idr#logical-relation}}

`realizesExpansion` 改变被观察求值的项，同时保留结果 lambda 及其行为。在应用分支，它把函数的求值过程接在替换后函数体的求值过程前面。

`realizesDown` 证明该关系兼容**全部**信息序规则。箭头输入是逆变的：先把较强的输入证据减弱，才能调用已有的函数行为；再把输出证据减弱到目标输出。分配规则最微妙。同一函数的两种近似起初可能携带两个 lambda 见证。求值确定性证明这两个 lambda 相等，因此对每个参数，都可以把两份输出证据配成一对。这里没有使用任意函数的相等性，也没有假设函数外延性。

### 基本引理 {#fundamental}

虽然最终观察针对闭程序，证明内部仍需要开放项。替换 `sigma` 把每个自由变量映射到闭项。`RealizesEnv gamma sigma` 逐点要求：每个替换项都实现 `gamma` 为相应变量指定的信息。

基本引理断言：如果 `term` 在 `gamma` 中表示 `value`，且 `sigma` 实现 `gamma`，那么闭项 `subst sigma term` 实现 `value`。证明沿有限语义推导归纳。

变量分支使用对应的环境证据。lambda 分支的见证，是把替换提升到绑定者之下所得到的 lambda。要证明参数行为，就给 `sigma` 加入任意一个实现输入信息的参数，再对函数体应用归纳假设；`betaSubst` 证明这个扩展替换与向该 lambda 作 beta 替换相同。应用分支通过归纳得到函数见证和参数关系，先调用函数行为，再用 `realizesExpansion` 接上函数求值。并分支构造一对证据，底分支直接成立，下闭分支使用 `realizesDown`。

{{include:src/PLFA/Part3/Adequacy.idr#fundamental}}

对于闭项，空环境没有变量需要检查。经检查的替换恒等定理说明，应用恒等替换不会改变项。因此得到 `closedFundamental`。

### 可观察充分性与策略完备性 {#observable-adequacy}

`functionConverges` 直接从逻辑关系的箭头分支提取求值见证。要得到常见的、以语义相等为前提的充分性表述，只需注意每个 lambda 都有信息 `Arrow Bottom Bottom`。语义相等把这份信息传给目标项，`functionConverges` 就给出一个 lambda 结果。结果函数体不必与相等前提中出现的函数体相同。

反过来，成功的 `Eval` 推导会给出完整 beta 归约序列。健全性把 `Arrow Bottom Bottom` 从结果 lambda 传回原项。`observableAdequacy` 打包这两个方向：闭项具有某个有限箭头近似，**当且仅当**它弱收敛。

{{include:src/PLFA/Part3/Adequacy.idr#adequacy}}

同一组结论还证明 `cbnBetaEquivalent`：存在一条到达某个 lambda 的完整 beta 归约，当且仅当弱按名求值能够收敛到某个 lambda。一个方向来自已有的求值到归约转换；另一个方向先用完整 beta 健全性，得到与终点 lambda 的语义相等，再用充分性产生按名求值。这是“存在可观察结果”的定理。它不表示每一种 beta 策略都会终止，也不把不同策略的最终函数体认定为相同语法。

### 恢复闭包形式 {#closure-adequacy}

PLFA 原定理返回一个 lambda 闭包，其中保留函数体及其自由变量的环境。上面基于替换的逻辑关系让中心证明更简洁，但我们也把它连接回原来的操作语义表示。

`ClosureConverges` 打包一份从闭输入和空闭包环境出发的实际 `ClosEval` 推导，以及证明结果闭包包含 lambda 的 `ClosureValue` 证据。`convergenceToClosure` 使用 ClosureCorrespondence 中已证的 `closedEvalToClos` 桥接定理。该桥重建闭包求值，并证明其结果经重新表示后，与替换式求值器的结果相等。反向转换使用已有的 `closToEval` 和显式的 lambda 形状。

{{include:src/PLFA/Part3/Adequacy.idr#closure-adequacy}}

因此，`closureAdequacy` 恢复了以闭包为结果的“语义相等推出收敛”定理；`closureBetaEquivalent` 恢复了任意完整 beta 归约到 lambda 与闭包按名收敛之间的双向对应。`closureObservableAdequacy` 也把闭包收敛与存在有限箭头观察联系起来。求值器反向桥在内部度量的是一份已经给出的有限求值推导，并没有给定理加上固定燃料上限，也没有假定所有项都能求值成功。

## 易错点 {#pitfalls}

- `Bottom` 与 `Arrow Bottom Bottom` 不同。后者要求存在外层 lambda 结果；前者完全不保证收敛。
- 收敛指弱头收敛，不要求函数体达到完整 beta 规范形。`lambda x. Omega` 正好体现这种差别。
- 定理要求闭程序。开放变量可以从语义环境获得函数信息，却不能直接作为闭程序运行。基本引理只有在提供实现环境的替换后，才处理开放项。
- `SemEq term (Lam body)` 是充分前提。仅有某个箭头近似，并不意味着与这个指定的 lambda 相等，只保证存在某个可观察 lambda 结果。
- 这些证明转换的总性，不表示对象语言的总性，也不表示 Idris2 每项特性的一致性。证明检查相对于本书明确说明的编译器与逻辑可信边界成立。

## 习题与已检查解答 {#exercises}

1. **A1 — 忽略发散。** 对任意闭项 `A`，推导 `(lambda x. lambda y. y) A` 的信息 `Arrow Bottom Bottom`，再得到收敛见证。不要求值 `A`。参考解答：`constantIgnoresArgument`。
2. **A2 — 传递观察。** 已知两个闭项语义相等，且第一个收敛，证明第二个也收敛。使用箭头观察，不要声称两个结果的语法相等。参考解答：`equalPreservesConvergence`。
3. **A3 — 底的边界。** 构造 `Omega` 的底解释，再证明它没有箭头解释。解释这两个结论为何不矛盾。参考解答：`bottomIsNotEnough` 和 `omegaHasNoFunction`。

{{include:src/PLFA/Part3/Adequacy.idr#exercises}}

## 参考与改编说明 {#references}

改编自 Philip Wadler、Wen Kokke 和 Jeremy G. Siek 的 [PLFA：Adequacy](https://plfa.github.io/Adequacy/)，冻结提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用 CC BY 4.0 许可。上游通过相互配合的值关系和表达式关系，把有限值关联到闭包。本版直接把值关联到经替换的闭项；箭头关系包含 lambda 求值见证。有限信息序以及闭项按名求值观察的范围保持不变。

中心逻辑关系产生 `Eval` 证据。已证的 `closToEval` 与 `evalToClos` 桥接定理，把这一求值器与真实闭包语义双向连接起来，并保证重新表示后的结果相等。最后的 `closureAdequacy` 与 `closureBetaEquivalent` 推论保留了上游的闭包观察，包括结果为 lambda 闭包的证据。所有这些陈述都针对任意无类型闭程序和有限成功推导，不附加固定求值预算。

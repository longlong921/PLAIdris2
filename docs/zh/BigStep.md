# 弱按名调用求值 {#big-step}

## 动机 {#motivation}

完整 β 归约描述所有允许的收缩。实现程序时，还需要决定执行顺序及停止条件。**弱按名调用**先求值应用的函数，传递尚未求值的参数，并在得到 λ 时立即停止。它不会进入返回的 λ 函数体继续归约。

大步关系一次记录整个成功求值过程。一个有限证明解释输入为什么能到达值；没有找到这种证明，本身并不构成判断发散的算法。我们同时定义基于替换的求值，以及上游 PLFA 使用的闭包与环境表述，再证明二者的对应。

## 模型 {#model}

`Eval term value` 只有两条规则。`EvalLam` 原样返回 λ；`EvalApp` 先把函数求值到 `Lam body`，将**未经求值**的参数替换进函数体，再求值所得项。规则中没有单独求值参数的前提。

该关系对任意作用域定义，但成功的结果必然是 λ。`evalValue` 沿每个应用推导的第二个前提向下，直到遇到 `EvalLam`，由此证明这一点。`evalDeterministic` 证明同一输入的两次成功求值具有相同结果。在应用分支中，必须先确认函数结果相同，才能比较函数体的推导。

{{include:src/PLFA/Part2/BigStep.idr#evaluation}}

## 例子 {#examples}

令 Ω 为 `(λx. x x) (λx. x x)`。项 `(λx. λy. y) Ω` 会求值得到恒等函数：外层 β 收缩后，参数已经消失。`ignoreOmegaTerminates` 检查这一推导。如果某种急切策略先要求 Ω 得到一个值，这个例子就不会结束。

上游例子 `(λx. λy. x) Ω` 在弱按名调用下也会终止，但结果不同，是 `λy. Ω`；函数体里仍然包含循环。`lazyCaptureTerminates` 检查替换表述，`closureLazyCapture` 检查相应的闭包结果。闭包把 Ω 存入环境，并不会仅仅因为外面的 λ 被返回，就开始执行 Ω。

Ω 本身没有 `Eval` 推导。`omegaNoEval` 通过检查一个假设存在的推导来证明这一点：函数只能通过 `EvalLam` 求值，而函数体前提将是对同一个 Ω 的、严格更小的求值推导。对这个有限证明递归便能排除所有情况。即使对象语言中的项原样重复，递归仍然减小了**证明**。

## 定理 {#theorems}

### 对应的小步策略 {#weak-small-step}

`HeadStep` 恰好有两条规则：收缩以 λ 为函数的应用，或者在函数位置走一步。它没有参数规则，也没有进入 λ 的规则。`HeadSteps` 记录该策略的有限路径。

`lambdaDoesNotStep` 排除从 λ 出发的一步，为 `headDeterministic` 提供不可能的重叠情况。如果两个推导都在函数位置走一步，就递归比较函数的这两步。每个头部步骤仍然是合法的完整 β 步，`headIsBeta` 证明这一点；`headsAreBetas` 将这种包含关系提升到有限路径。

{{include:src/PLFA/Part2/BigStep.idr#weak-small-step}}

### 大步与弱小步对应 {#correspondence}

`evalToHeadSteps` 把大步推导转换成头部归约路径。应用先在函数位置执行函数的路径，再做一次外层 β 收缩，最后执行函数体的路径。因此 `evalToSteps` 也能给出完整 β 关系中的路径。

反方向使用 `headExpand`：如果一个头部步骤通向能够成功求值的项，那么原项也能求值得到同一值。随后对终点为 λ 的头部路径归纳，得到 `headStepsToEval`。因此，对任意作用域，`Eval term (Lam body)` 与 `HeadSteps term (Lam body)` 等价。

对**闭输入项**，还有一个更进一步的定理：若存在到达某个 λ 的*任意完整 β 路径*，则弱按名调用能求值到某个 λ，但这个 λ 可能不同。后面的 [Adequacy](Adequacy.md) 会使用指称语义证明这一存在性结论。它不保持完全相同的结果函数体，也不能仅仅忘掉步骤采用的策略，就把前面的等价扩展成适用于所有开放项的完整 β 命题。

{{include:src/PLFA/Part2/BigStep.idr#correspondence}}

### 闭包保留参数自己的环境 {#closures}

闭包 `Close term env` 保存一个项，以及分配给其自由槽位的闭包。环境是有限的索引列表。`Extend` 把一个闭包放入最新槽位，`lookupEnv` 解释一个 `Fin` 索引。相互定义的数据结构构成保存项及环境的有限树。

`ClosEval` 直接实现弱按名调用。变量规则求值查找到的闭包；λ 规则返回当前项及环境；应用规则先把函数求值到一个保存着环境 `delta` 的 λ 闭包，再在 `delta` 的基础上加入 `Close arg env`，并用这个扩展环境求值函数体。

上一句中出现两个环境是有原因的：函数体使用随函数保存的环境，参数则使用调用位置的环境。二者不能暗中互换。参数闭包未经求值就被存入。`closDeterministic` 证明结果闭包的唯一性。

`reify` 递归地把所有保存的自由槽位替换为相应闭包还原出的项，得到一个闭项。`reifyBeta` 证明环境扩展对应一次避免捕获的替换，依赖的是 `betaSubst`。随后对闭包求值归纳得到 `closToEval`；再与前面的路径定理复合，就有 `closToSteps`。`closedClosToLambda` 表述上游的正向结果：闭程序通过闭包求值成功时，存在到达某个 λ 的完整 β 路径。

{{include:src/PLFA/Part2/BigStep.idr#closures}}

### 也能从替换求值返回闭包 {#closure-equivalence}

逆向定理推广到**任意**闭包，而非只处理初始空环境。`evalToClos input` 接受 `reify input` 能求值到某个闭值的推导，构造结果闭包、`ClosEval input result` 推导，以及“还原结果恰好等于该值”的等式。`closedEvalToClos` 将这个定理专门化到闭输入项。

证明需要两种下降度量。求值应用时，函数和函数体的推导会变小，但函数体闭包可能带有更大的新扩展环境；查找变量时，求值推导未必变小，但保存的闭包位于有限环境树更深的位置。只对语法做一次递归，不能同时解释这两种变化。

`BoundedEval` 为一个已经存在的推导标注高度上界。`weakenBound` 增大上界，`evalBound` 则为**每个**有限的 `Eval` 推导构造合适上界。因此最终的对应定理不假设固定预算。这只是归纳工具，并不是用带燃料限制的关系来替代操作语义。

{{include:src/PLFA/Part2/ClosureBounds.idr#bounded-evaluation}}

{{include:src/PLFA/Part2/ClosureBounds.idr#finite-derivation-bound}}

`closValue` 显露每个成功闭包结果的 λ 形状。随后 `boundedToClos` 与 `boundedEnvToClos` 相互递归：应用减小高度上界；变量查找保持上界不变，但沿闭包及环境结构向下。在应用分支中，函数还原结果的相等确定其 λ 函数体，再由 `reifyBeta` 把第二个前提转换到扩展后的闭包环境中。

{{include:src/PLFA/Part2/ClosureCorrespondence.idr#closure-values}}

{{include:src/PLFA/Part2/ClosureCorrespondence.idr#inverse}}

## 全定义的可执行求值器 {#fuel}

`headView` 检查一个项：要么识别出 λ，要么识别出开放的中性头部，要么给出一个 `HeadStep`。这里的中性头部可以带任意参数，因为弱求值不会检查这些参数。这个 `Neutral` 不同于 [Untyped](Untyped.md#normalization) 的 `FullNeutral`，后者要求参数自身也正规。

`run fuel term` 重复执行上述检查。`Returned` 携带到达 λ 的路径；`Blocked` 携带到达开放中性项的路径；`OutOfFuel` 携带到当前残余项的路径。因此，三种结果都明确记录已经执行的归约。成功结果可通过 `headStepsToEval` 转换为 `Eval`。

零燃料时，求值器立即返回 `OutOfFuel`，即使输入已经是 λ。最后检查一个值也消耗一个预算单位，因此一次 β 步之后再识别 λ，需要两个单位。增加预算可以搜索更长的过程，但某次运行耗尽不能证明发散。证明 Ω 不收敛的是独立定理 `omegaNoEval`，不是有限测试 `fuelOmega`。

{{include:src/PLFA/Part2/BigStep.idr#fuel}}

## 常见误区 {#pitfalls}

- **弱值不一定是完整正规形。** 即使函数体可以继续归约，`λy. Ω` 仍是该策略中的值。
- **按名调用不等于按需调用。** 这些规则不缓存已经求值的参数，重复使用变量可能重复求值。
- **参数闭包保留调用位置的环境。** 若误用函数的环境，会改变自由变量的含义。
- **确定性允许发散。** 它证明两个成功推导的结果唯一，不保证成功推导一定存在。
- **给定证明的高度上界不是终止判定器。** `evalBound` 不能凭空为任意程序制造 `Eval` 推导。

## 习题与已检查解答 {#exercises}

1. **BigStep-1 — 忽略循环参数。** 分别构造 `(λx. λy. y) Ω` 和 `(λx. λy. x) Ω` 的求值，解释为什么返回的 λ 不同。解答为 `ignoreOmegaTerminates` 与 `lazyCaptureTerminates`。
2. **BigStep-2 — 保存参数。** 为习题 1 的第二个表达式构造闭包推导，指出哪个环境保存 Ω，以及为什么返回结果前没有发生变量查找。已检查解答是 `closureLazyCapture`。
3. **BigStep-3 — 证明否定结论。** 对有限推导进行归纳，反驳任意声称 Ω 可以求值的证据，而不是运行一个有界测试。已检查解答是 `omegaNoEval`；将它与三个可执行检查 `fuelIdentity`、`fuelOmega`、`fuelNeutral` 对比。

{{include:src/PLFA/Part2/BigStep.idr#examples}}

## 参考与改编说明 {#references}

改编自 Philip Wadler、Wen Kokke 和 Jeremy G. Siek 的 [PLFA〈BigStep〉](https://plfa.github.io/BigStep/)，对应源码 `src/plfa/part2/BigStep.lagda.md`，冻结提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用 CC BY 4.0 许可。本改编保留闭包求值、确定性，以及还原到完整 β 归约的证明；环境用索引列表取代有限定义域上的函数。新增替换表述、相应弱小步的等价、携带证明的燃料求值器，以及一般的逆向闭包对应，使不同表示之间的选择明确可见。[Adequacy](Adequacy.md) 使用该对应在两种表述中陈述收敛结果；本章不声称任意 β 路径都会得到与弱求值完全相同的语法值。

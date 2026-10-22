# 完整 β 归约的合流性 {#confluence}

## 动机 {#motivation}

完整 β 归约允许在项的任何位置选择红式。如果两种选择得到不同的中间项，后续计算还能会合吗？**合流性**给出肯定回答：只要同一个起点分别经过有限步归约得到 `left` 与 `right`，就存在一个两边都能到达的共同项 `meet`。

这一命题讨论的是 [Untyped](Untyped.md#theorems) 中不受策略限制的关系，包括 λ 内部以及应用两侧的归约。它不是通过选定一个确定性策略获得的，也不保证任何一条路径最终到达正规形。Ω 仍然可以作为起点。

## 模型 {#model}

如果一个单步关系的任意两条出边，都能各接一步到达同一个目标，就称它具有菱形性质。普通 β 归约**不**具有这一性质：复制参数可能同时复制尚未完成的工作。

为此，引入辅助的平行归约关系 `Par source target`。`PVar` 保持变量不动；`PLam` 平行归约函数体；`PApp` 同时平行归约两个子项；`PBeta` 先平行归约 λ 的函数体与参数，再对所得结果进行替换。即使函数本来就是 λ，仍可以选择 `PApp`，因此一轮平行归约可以暂时不收缩某个外层红式。

`parRefl` 证明每个项都能平行归约到自身。它由结构递归证明，不是额外加入的通用自反构造器。`Pars` 是 `Par` 的有限自反传递闭包。

{{include:src/PLFA/Part2/Confluence.idr#parallel}}

## 例子 {#examples}

记 `R = (λx. x) a`。从 `(λx. x x) R` 出发，一次普通归约既可以得到 `(λx. x x) a`，也可以得到 `R R`。第一条分支再走一步就到 `a a`；第二条分支却需要两次普通收缩，分别处理两个 `R`。所以共同终点确实存在，但普通**单步**菱形不成立。

在平行归约中，`R R` 可以用一轮 `PApp` 到达 `a a`，两侧各放入一个收缩。原先让普通单步陷入困难的复制工作，现在符合辅助关系的定义。下文的 `duplicateOuterFirst` 与 `duplicateInnerFirst` 检查原来的有限 β 路径；`duplicateJoin` 则对任意平行参数归约检查复制后的平行步骤。

## 定理 {#theorems}

### 替换保持平行归约 {#substitution}

证明的核心是 `parSubst`：如果两个替换逐点满足平行归约关系，而且两个输入项也平行相关，那么替换后的结果仍平行相关。只讨论单个变量的替换太弱，无法直接对 λ 内部进行归纳。

先证明 `parRename`，其中 β 分支使用 [Substitution](Substitution.md#substitution-laws) 的 `renameBeta`。重命名的保持性随后让逐点替换关系可以提升到绑定者下面。最后，`parSubst` 的 β 分支使用 `substBeta`。正是在这两个地方，需要真正连接避免捕获的替换与归约，而不只是定义替换。

`parBeta` 将一般引理专门化到单个参数：平行相关的函数体与平行相关的参数，经过 β 替换后仍平行相关。

{{include:src/PLFA/Part2/Confluence.idr#preservation}}

### 完全展开给出三角形 {#triangle}

`develop source` 递归地收缩原始起点中已经可见的红式。它不保证得到正规形，也不立即收缩本轮收缩新产生的所有红式。例如，归约应用的函数部分，可能显露出原先不在函数位置上的 λ。

三角形定理 `parTriangle` 表示：从 `source` 得到的任意平行归约结果，都能再平行归约到 `develop source`。细致的一种情况是：原来的函数为 λ，但第一轮使用 `PApp`，有意保留了外层红式；下一轮便用 `PBeta` 追上完全展开。如果第一轮已经使用 `PBeta`，则用 `parBeta` 连接替换中的两个组成部分。

具有同一起点的两个三角形，其底部都是同一个完全展开。将二者配对，就得到 `parDiamond`：共同目标以及两条分支到该目标的证据都被显式构造出来。

{{include:src/PLFA/Part2/Confluence.idr#triangle}}

### 平行路径与普通路径具有相同的可达性 {#correspondence}

`stepPar` 把一次普通归约变成一轮平行归约，未触及的子项使用自反证据。反过来，`parSteps` 将一轮平行归约串行化为有限个普通步骤。在 β 分支，它先在 λ 下面归约函数体，再归约参数，最后执行外层收缩。

沿路径提升这两个转换，便得到 `stepsPars` 与 `parsSteps`。这里等价的是**有限可达关系**，并非声称一个普通步骤等于一轮平行归约，也不声称二者的计算成本相同。

{{include:src/PLFA/Part2/Confluence.idr#correspondence}}

### 合流与 Church–Rosser {#church-rosser}

`strip` 反复补全菱形，将一个平行单步沿整条平行路径传播。`parsConfluent` 再沿另一条路径重复该构造。最后将结果转换回普通归约，就得到适用于任意作用域正确项及任意有限 β 路径的 `confluence`。

Church–Rosser 常用**可转换性**而不是两条正向路径表述。`Convertible left right` 记录有限的一串边，每条边可以正向或反向。`churchRosser` 证明这样的链也有共同的正向归约结果。反向边通过合流性处理，正向边则直接接到路径前面。

最后，`Normal term` 表示没有任何 β 步能离开 `term`。`normalPath` 表明从正规形出发的路径只能是零步，因此 `normalUnique` 证明：从同一起点到达的两个正规形必然相等。[Untyped](Untyped.md#normalization) 的结构化 `FullNormal` 证书通过 `fullNormalNoStep` 提供这里所需的不可再走一步性质。

{{include:src/PLFA/Part2/Confluence.idr#confluence}}

## 常见误区 {#pitfalls}

- **合流不等于终止。** 定理接受两条有限路径，从不声称所有路径都会结束。
- **正规形至多唯一，不一定存在。** `normalUnique` 明确要求两条归约证据与两个正规性假设。
- **完全展开不等于完整规范化。** 它只按某一个起点的红式结构完成一轮递归定义的展开。
- **普通 β 归约不具有菱形性质。** 引入平行归约正是为了处理这一困难。
- **弱求值的确定性是另一个定理。** 把关系限制为单一策略，无法证明这里的完整 β 结论。

## 习题与已检查解答 {#exercises}

1. **Confluence-1 — 会合复制后的工作。** 给定 `Par arg result`，构造 `Par (App arg arg) (App result result)`。解释为什么两个副本可以在同一轮中归约。已检查解答是 `duplicateJoin`。
2. **Confluence-2 — 比较普通路径。** 从 `(λx. x x) ((λx. x) a)` 到 `a a` 构造两条路径，一条先选外层红式，另一条先选内层红式。解答是 `duplicateOuterFirst` 与 `duplicateInnerFirst`，普通步骤数分别为三和二。
3. **Confluence-3 — 平行归约恒等应用。** 证明恒等函数应用到任意参数后，能平行归约为该参数，且无需求值参数。已检查解答是 `identityParallel`。

{{include:src/PLFA/Part2/Confluence.idr#exercises}}

## 参考与改编说明 {#references}

改编自 Philip Wadler、Wen Kokke 和 Jeremy G. Siek 的 [PLFA〈Confluence〉](https://plfa.github.io/Confluence/)，对应源码 `src/plfa/part2/Confluence.lagda.md`，冻结提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用 CC BY 4.0 许可。本改编保留完整无类型 β 归约的平行归约、完全展开与条带证明，并额外明确给出有限双向链的可转换性，以及可达正规形的唯一性。证明不使用函数外延性、正规化假设，也没有改用确定性策略来替代原命题。

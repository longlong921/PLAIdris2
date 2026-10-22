# 替换法则 {#substitution}

## 动机 {#motivation}

写出避免捕获的替换函数只是第一步。要推理 λ 演算，还必须知道两次替换如何复合、替换怎样与重命名相互作用，以及替换后的 λ 被应用时会发生什么。[Confluence](Confluence.md) 需要这些法则，才能同时归约函数体和参数；[BigStep](BigStep.md) 则需要它们连接闭包环境与通过替换得到的项。

本附录为所有作用域正确的无类型项证明这些法则，包括开放项。定理不要求类型推导、正规化或求值前提。关键假设是映射的作用域：每个旧槽位必须在指定的新作用域中有一个像。

## 模型 {#model}

回顾：重命名的类型是 `Fin m -> Fin n`，替换的类型是 `Fin m -> Tm n`。在 λ 下面，`liftRen` 与 `liftSub` 为绑定变量保留新的槽位。特别地，`liftSub sigma (FS i)` 会先弱化 `sigma i`，再将其放到绑定者下面。定义本身见 [Untyped](Untyped.md#substitution)。

我们按**逐点相等**来比较映射：对每个变量 `i`，两个映射的像都相等。不需要证明函数本身相等。`renameExt` 和 `substExt` 将这种逐点相等传递到结果项的相等。λ 分支提升逐点假设；应用分支则使用两个归纳假设。

{{include:src/PLFA/Appendix/Substitution.idr#extensionality}}

这一选择在内涵类型论中很重要。逐点相等正是这些证明中已有的证据。如果将它替换为整个函数相等，就会额外引入本开发没有假设的函数外延性原则。

## 例子 {#examples}

假设外围有 `x`、`y` 两个槽位。先把 `x` 重命名成 `y`，再用项 `N` 替换 `y`，结果应当与直接将 `x` 映射到 `N` 相同。`substRename` 为任意项与任意映射精确表述了这一观察。

关键的消去例子会跨过一个额外绑定者。`rename FS term` 把 `term` 的所有自由槽位都移开新引入的零号槽位。此时用任意 `arg` 替换这个未使用的零号槽位，应当返回原来的 `term`。这就是 `cancelShift`。参数自身可以含自由变量，也可以包含会发散的语法；证明从不求值这个参数。

具体的绑定例子是 `(λx. λy. x) z` 变成 `λy. z`。插入内层绑定者下面的 `z` 被弱化，所以索引变为一。数字索引发生了变化，但变量的绑定没有变化。已检查的例子是 [Untyped](Untyped.md#exercises) 中的 `captureAvoidance`。

## 定理 {#theorems}

### 重命名的复合 {#renaming-laws}

`renameId` 表示使用恒等映射不会改变项。`renameComp rho tau term` 表示先用 `tau` 重命名，再用 `rho` 重命名，等于直接使用它们的逐点复合。参数顺序很重要：定理中第一个映射是**外层、后执行**的操作。

变量分支直接计算即可。λ 分支的递归调用使用两个提升后的映射。`liftRenComposition` 逐变量检查“提升复合”与“复合提升”相同：新绑定变量在两边都保持不动；旧变量则在应用两个映射之后再移位。

{{include:src/PLFA/Appendix/Substitution.idr#renaming}}

### 重命名与替换的相互作用 {#mixed-laws}

混合法则有两条，含义不同。`substRename sigma rho term` 先重命名输入槽位，再替换它们的像；`renameSubst rho sigma term` 先插入替换项，再重命名这些替换项的自由变量。它们右边的映射不同，因此不能混为一谈。

`renameSubst` 中看起来较难的是 λ 下面的旧变量分支。一边先弱化替换项，再应用提升后的重命名；另一边先重命名替换项，再弱化它。应用两次 `renameComp` 就能连接这两个表达式，这一步没有暗中加入新的绑定原则。

{{include:src/PLFA/Appendix/Substitution.idr#mixed-laws}}

### 替换的复合 {#substitution-laws}

`substId` 使用“把每个变量映射到自身”的替换。`substComp sigma tau term` 是主要的复合律：先用 `tau` 替换，再用 `sigma` 替换，等于一次使用把 `i` 映射到 `subst sigma (tau i)` 的替换。

证明沿项的结构进行。λ 分支需要 `liftSubComposition`。对旧变量，提升后的内层替换引入了一次弱化；`substRename` 让外层替换跨过这个弱化，`renameSubst` 再把另一边整理成所需形式。这正是先证明混合法则的原因。

`cancelShift` 由 `substRename` 与 `substId` 得到。它随后提供以下 β 相互作用法则中的旧变量分支：

- `renameBeta` 说明重命名与一次同时作用于函数体和参数的收缩可交换。
- `substBeta` 说明任意同时替换与该收缩可交换。
- `betaSubst` 先把环境替换到 λ 函数体中，再提供参数；结果等于直接用 `cons arg sigma` 替换一次。这个映射把最新槽位送到参数，其余槽位交给 `sigma`。

这些命题讨论结果项的语法相等，不声称参数求值会终止。特别地，`betaSubst` 接受旧槽位的替换，以及一个位于**目标**作用域中的新参数。将闭包环境还原为语法再扩展时，使用的正是这个版本。

{{include:src/PLFA/Appendix/Substitution.idr#substitution-laws}}

## 常见误区 {#pitfalls}

- **映射复合有先后顺序。** 在 `substComp sigma tau term` 中，先作用的是 `tau`。交换二者一般同时改变类型和结果。
- **提升不等于普通的映射扩展。** 旧变量的替换项必须弱化，只固定 `FZ` 还不够。
- **未使用某个绑定者，不代表函数体没有其他自由变量。** `cancelShift` 对任意开放项成立，不只适用于闭常量。
- **β 替换不会求值参数。** 这些都是语法变换，因此 Ω 也是合法参数。
- **逐点同余不等于函数外延性。** 我们证明的是将映射应用到项之后的结果相等，并未公理化映射本身的相等。

## 习题与已检查解答 {#exercises}

1. **Substitution-1 — 把重命名看作替换。** 证明使用 `rho` 重命名，等于将每个变量替换成 `Var (rho i)`。先对重命名后的项应用 `substId`，再用 `substRename`。已检查解答是 `renamingAsSubstitution`。
2. **Substitution-2 — 消去未使用的绑定者。** 对相同作用域中的任意 `arg` 与 `term`，证明 `beta (rename FS term) arg = term`。解释为什么不需要限制 `arg` 的自由变量或终止性。已检查解答 `unusedBinder` 直接来自 `cancelShift`。

{{include:src/PLFA/Appendix/Substitution.idr#exercises}}

## 参考与改编说明 {#references}

改编自 Philip Wadler、Wen Kokke 和 Jeremy G. Siek 的 [PLFA〈Substitution〉](https://plfa.github.io/Substitution/)，对应源码 `src/plfa/part2/Substitution.lagda.md`，冻结提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用 CC BY 4.0 许可。本书将该章放在附录，模块名为 `PLFA.Appendix.Substitution`。Idris2 表述使用 `Fin` 索引的无类型作用域及逐点映射法则，不假设函数外延性公理。导出的恒等律、复合律、弱化消去律和 β 相互作用结果，都对任意映射与任意作用域正确的项成立。

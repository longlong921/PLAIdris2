# 健全性 {#soundness}

## 动机 {#motivation}

求值会改变程序的语法。健全性断言：程序的数学含义不会因此改变。对于无类型 lambda 演算，这比“两段程序返回相同答案”更强：在任意环境中，关于任意一方的每一份有限信息，也都是关于另一方的信息。

这里有两个方向。**保持性**把信息从红式传到归约结果。**反映性**也叫主项扩张，把信息从结果传回红式。只证明保持性，仍允许归约凭空产生新信息。只有两个方向都成立，才为后续在任意程序中替换表达式奠定基础。

本章使用 Untyped 的完整无类型项。一步归约可以收缩 beta 红式，也可以归约应用的任意一侧，或进入抽象内部。定理没有要求规范化、特定求值策略或类型推导。

## 模型 {#model}

`Tm n` 表示可以使用 `n` 个 de Bruijn 变量的项。环境 `Env n` 为每个变量提供一个有限信息值。信息值包括 `Bottom`、`Arrow a b` 和 `Join a b`。`Denote gamma term v` 是证据，表明 `v` 近似描述了环境 `gamma` 中的 `term`。它是由有限证明树构成的关系，不是能够执行所有 lambda 项的求值函数。

`SemEq left right` 表示这些判断的逐点等价：对于每个环境和信息值，都存在两个方向的证据转换函数。我们因此不需要假设函数外延性。信息序和语义规则与 Denotational 一章相同，包括箭头输入的逆变以及箭头对并的分配规则。

替换把变量换成项。为了保持含义，替换项必须提供原环境赋予相应变量的信息。`SubDenote delta sigma gamma` 逐个变量表达了这一条件。进入 lambda 后，新变量保留其信息，原有的替换项则向后移动一层以越过绑定者。

{{include:src/PLFA/Part3/Soundness.idr#substitution-preservation}}

`substPres` 对语义推导归纳。变量分支使用已有的变量证据；应用、并和下闭分支重建原有语义规则。抽象分支同时扩展两个环境和替换。`substitution` 是 beta 归约所需的单变量特例。

## 具体例子 {#examples}

先看 `(lambda x. x) A`。它的一份有限解释来自恒等函数的近似 `Arrow a b`，以及参数 `A` 的信息 `a`。对 lambda 的解释作反演，可得到在加入 `a` 的环境中的函数体判断；再用替换定理，就得到 `A` 的同一份结果信息 `b`。

再看 `(lambda x. lambda y. y) Omega`。虽然 `Omega = (lambda x. x x) (lambda x. x x)` 不收敛，整个项的 beta 归约结果却是恒等函数。要从恒等函数的信息反推原项，根本不需要被忽略参数的信息：`Bottom` 足够。这正是反映性证明需要底环境的原因。

对于 `(lambda x. x x) A`，同一个参数出现两次。有限推导可能在函数位置使用 `Arrow a b`，在参数位置使用 `a`。反映性会记录它们合起来的需求 `Join (Arrow a b) a`，不要求两个位置起初就采用相同近似。

最后一个例子在绑定者内部归约：`lambda z. ((lambda x. x) z)` 归约为 `lambda z. z`。`underLambdaMeaning` 证明这一步完整 beta 归约保持语义；弱按名求值则会在外层 lambda 处立即停止。

## 定理与证明结构 {#theorems}

### 保持性 {#preservation}

beta 分支先对 lambda 作反演，再使用替换定理。合同分支递归处理被归约子项对应的子推导。无论采用哪一步归约，底、并和下闭规则仍然成立。

{{include:src/PLFA/Part3/Soundness.idr#preservation}}

### 恢复有限需求 {#finite-demand}

反映性需要恢复替换时消失的参数信息。我们先逆向处理重命名。变量的语义推导最后可能使用了并或下闭规则，因此不能只查看最后一个构造子；变量反演引理给出的是信息不等式。

{{include:src/PLFA/Part3/Soundness.idr#renaming-reflection}}

`substReflect` 接收替换后项的一棵有限推导，返回环境 `gamma` 和两份证明：原项在 `gamma` 中具有目标信息；每个替换项都能提供 `gamma` 为相应变量要求的信息。

变量分支中，`oneEnv` 只在该变量处记录所需信息，其余位置取底。应用分支和并分支的两个递归调用可能要求不同环境。取逐点并就能同时满足两种需求，再用环境单调性把两份推导移到这个共同环境中。lambda 分支中，新变量所需的信息低于 lambda 的输入信息，因此可以把它增大到该输入，然后从剩余环境移除这一绑定者。环境之间的比较始终是逐点进行的。

{{include:src/PLFA/Part3/Soundness.idr#finite-demand}}

单变量替换推论提取一个有限值 `a`：参数具有信息 `a`，原函数体在加入 `a` 的环境中具有结果信息。这个存在量化的值，正是重建原 beta 红式所缺少的部分。

### 反映性与相等 {#reflection}

`reflectBeta` 用 lambda 规则和应用规则，把恢复出的参数推导与函数体推导组合起来。`reflect` 随后处理任意语法构造内部的归约，包括 lambda 内部归约。

{{include:src/PLFA/Part3/Soundness.idr#reflection}}

`stepSoundness` 把保持性和反映性配成一对。`soundness` 沿有限归约序列复合这些证据转换。它的终点可以是任意项；常见的“归约到 lambda”表述只是一个特例。

{{include:src/PLFA/Part3/Soundness.idr#soundness}}

## 易错点 {#pitfalls}

- 主项扩张是这个有限信息解释的性质。普通简单类型系统通常不具有这一性质：即使归约结果可以赋型，被忽略的参数也可能无法赋型。
- `Bottom` 不提供任何终止证据。每个项都有它，包括循环项。
- 一棵有限语义推导可能需要参数的多种观察的有限并。只选某一次出现所需的信息，会丢失需求并使反映性证明失败。
- 健全性不表示每个归约过程都会终止，也不表示语义相等的两个项一定有共同的规范形。

## 习题与已检查解答 {#exercises}

1. **S1 — Beta 替换。** 对任意开放函数体和参数写出语义相等定理，不假定任意一方终止。指出反向证明从哪里取得共享的参数近似。参考解答：`betaMeaning`；它调用的 `stepSoundness` 包含前面的有限需求构造。
2. **S2 — 未使用的参数。** 证明把 `lambda x. lambda y. y` 应用于任意参数，都具有恒等函数的含义。解释为何参数取 `Omega` 时仍然成立。参考解答：`ignoredArgumentMeaning`。
3. **S3 — 绑定者内部的归约。** 证明 `lambda z. ((lambda x. x) z)` 与 `lambda z. z` 含义相同。解释为何这是完整 beta 归约的性质，而不是弱求值规则。参考解答：`underLambdaMeaning`。

{{include:src/PLFA/Part3/Soundness.idr#exercises}}

## 参考与改编说明 {#references}

改编自 Philip Wadler、Wen Kokke 和 Jeremy G. Siek 的 [PLFA：Soundness](https://plfa.github.io/Soundness/)，冻结提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用 CC BY 4.0 许可。本独立 Idris2 改编用内在限定作用域的 `Fin` 索引代替 Agda 上下文，并逐点比较环境。本版名为 `soundness` 的定理通过迭代上游的一般定理 `reduce-equal`，覆盖任意终点；上游把 `soundness` 这个名称用于终点为 lambda 的特例。所有展示代码都直接包含自经检查的源码；审查记录记载了实际编译检查。

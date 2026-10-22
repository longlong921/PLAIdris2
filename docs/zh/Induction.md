# Induction：用递归程序证明定律 {#induction}

## 为什么需要归纳 {#motivation}

一次计算只能确定一个输入。结合律却涉及每一组三个自然数，任何有限的数值测试表都不能覆盖这个命题。归纳利用自然数的构造：先证明零的情形，再根据前驱的证据构造后继的证据。得到的证明是一个递归函数，输出类型陈述了要证明的等式。

## 定义模型 {#model}

我们继续使用 [Naturals](Naturals.md#model) 中的运算。`addAssoc` 接收任意 `m`、`n`、`p`，返回 `(m + n) + p = m + (n + p)` 的证据，源码用 `add` 表达。括号很重要：这是结合律；交换两个参数是交换律；零不改变结果是单位元律。每个性质都是需要证明的命题，而不是允许无依据地改写表达式的规则。

{{include:src/PLFA/Part1/Induction.idr#addition}}

## 一步一步理解证明 {#examples}

在 `addAssoc Z n p` 中，两边都计算为 `add n p`，因此 `Refl` 足够。在 `S m` 情形，两边都会露出最外层的 `S`，剩下的等式恰好是 `addAssoc m n p`。`cong S` 把这个等式提升到共同的构造子之下。递归调用使用更小的 `m`，所以这既是合法的归纳，也是全定义程序。

交换律更难，因为加法对第一个参数递归。零情形的右边是 `add n Z`，因此先需要 `addZeroRight`。后继情形中，`addSuccRight` 把**第二个**参数的后继移到外面。证明先用归纳假设连接 `S (add m n)` 与 `S (add n m)`，再反向使用后继引理，连接到 `add n (S m)`。`trans` 串起等式，`sym` 反转第二步的方向。

可以分别把递归展开到零、一、二，得到各自的有限证明。递归定义却覆盖了每个有限自然数，无需手写无限多个分支。交互式证明时，先查看匹配构造子后的目标，再思考哪一步计算能显露更小的目标。参考文件保存完整证明，不保留待填的洞。

## 代数定理 {#theorems}

{{include:src/PLFA/Part1/Induction.idr#multiplication}}

`mulDistrib` 证明 `(m + n) * p = m * p + n * p`。后继情形使用归纳假设和加法结合律，重新组合额外的一份 `p`。乘法结合律随后通过展开一次递归乘法、分配、应用自己的归纳假设得到。`mulSuccRight` 对乘法交换律的作用，与 `addSuccRight` 对加法交换律的作用相同。

{{include:src/PLFA/Part1/Induction.idr#powers-monus}}

三个乘方定律分别说明指数相加、指数相乘以及乘积的乘方。它们都使用已经证明的乘法定律，不把算术规范化当作黑盒。`powerProduct` 用 `mulSwap` 交换中间的因子，再重新结合。`monusAdd` 表示：先减 `n` 再减 `p`，等于减去二者之和，即使减法会在零处截断也成立。它的零情形说明了 `zeroMonus` 为什么有用。

## 二进制定律与规范化 {#binary-laws}

{{include:src/PLFA/Part1/Induction.idr#binary-laws}}

`fromInc` 按最后一位分类。进位情形需要 `doubleSucc`：后继的两倍比原数的两倍多二。随后对自然数归纳，每一步使用 `fromInc`，就得到 `fromTo`。这两个定律不限制自然数，也不限制输入位串。

反方向的往返对任意原始位串并不成立：`Empty` 先解释为自然数再转回，会得到单独的一位零。`notRawRoundTrip` 是对这个特定等式的已检查反证。不过，规范化保持数值，并且具有幂等性：做两次不会比做一次产生更多变化，因为 `fromTo` 消去了中间一次自然数到二进制再回自然数的转换。后面会加入规范性前提，得到更强的反向定律。

## 容易混淆的地方 {#pitfalls}

需要归纳的等式不能只靠 `Refl`。不能在原输入上假设归纳结论，只能合法调用结构更小的递归情形。改写有方向，所需方向常常需要 `sym`。在证明交换律前没有准备好后继引理，容易陷入死路；选择引理本身就是证明的一部分。

## 习题与已检查解答 {#exercises}

1. **I.1 — 重排。** 交换前两个加数而保持第三个，再重新组合四个加数。参考 `addSwap`、`addRearrange`。
2. **I.2 — 分配律。** 证明乘法的两个分配律。参考 `mulDistrib`、`mulDistribRight`，指出哪一个使用了交换律。
3. **I.3 — 乘法。** 对任意自然数证明结合律和交换律。参考 `mulAssoc`、`mulComm`，辅助引理为 `mulSuccRight`。
4. **I.4 — 截断减法。** 证明零减任意自然数仍为零，以及连续两次减法等于减去和。参考 `zeroMonus`、`monusAdd`。
5. **I.5 — 乘方。** 证明三个乘方定律，并指出各步使用的乘法引理。参考 `powerAdd`、`powerMul`、`powerProduct`。
6. **I.6 — 二进制定律。** 判断哪个往返方向无需限制，证明加一正确性和规范化幂等性。参考 `fromInc`、`fromTo`、`notRawRoundTrip`、`normalizeIdempotent`。

所有具名解答都包含在源码中，并在 `%default total` 下接受检查。它们是全称量化的命题，不是有限范围的测试。

## 参考与改编说明 {#references}

改编自 [PLFA Induction](https://plfa.github.io/Induction/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。Idris 具名运算替代 Agda 的混合缀运算符。已检查实现同时展示显式等式组合和 `rewrite`。算术及二进制定律的论域没有缩小。

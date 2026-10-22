# Equality：计算、替换与等式推理 {#equality}

## 为什么学习相等 {#motivation}

前几章用等式连接中间结果，现在说明这种证据本身。相等不是比较两个值的布尔测试。类型 `x = y` 的值是一份证据，能够把 `x` 的任意性质转移为 `y` 的相应性质。因此，当目标中出现另一种表达式时，我们仍能使用关于原表达式的定理。

## 定义模型 {#model}

Idris 的命题相等有一个自反构造子 `Refl`，两端经过定义计算后必须一致。对这种证据做模式匹配，会使分支中的两个端点一致。我们采用内置相等，使 `rewrite` 机制和常见等号记法能够直接使用，不再另外定义一套相等类型。

{{include:src/PLFA/Part1/Equality.idr#equality}}

`eqSym` 反转等式，`eqTrans` 组合等式。匹配 `Refl` 解释了为什么可以这样做：端点重合后，结论立即成立。`eqCong` 对相等参数应用同一个函数；`eqCong2` 处理两个参数。`applicationCong` 则说明函数相等会导致每个输入上的结果相等。这个方向不需要函数外延性。

`transport p eq px` 是类型族中的替换。输入为类型族 `p : a -> Type`、等式 `x = y` 和 `p x` 的证据，输出的类型为 `p y`。这里的类型族返回类型，不是返回 `Bool` 的普通判断函数。

## 实例：转移奇偶证据 {#examples}

假设已有 `add m n` 为偶数的证据，要证明 `add n m` 为偶数。算术定理 `addComm m n` 正是 `transport Even` 所需的等式。因此 `evenComm` 不必手工重建奇偶推导，只需改变已有证据的索引。

{{include:src/PLFA/Part1/Equality.idr#reasoning}}

第二个版本 `evenCommRewrite` 使用 `rewrite`。为了用索引为 `add m n` 的证据填充 `add n m` 上的目标，证明反向改写**目标**。这解释了 `sym`：准备提供的证明已经有旧索引。改写方向看起来奇怪时，这种理解方式很有帮助。

`calculation` 把带后继的交换律写成等式链。先把第二个参数的后继移到外层，再把较小的交换律通过后继函数提升，最后在得到的表达式处结束。`step` 记录起点并组合两份等式证明，`finish` 用自反性结束。`leChain` 说明同样的传递性结构也适用于顺序证据，不过不等式通常不能反向使用。

## 莱布尼茨相等 {#theorems}

{{include:src/PLFA/Part1/Equality.idr#leibniz}}

莱布尼茨的表述是：如果 `x` 的每个性质都能转移给 `y`，则二者相等。`Leibniz a x y` 量化了通过实际实现的 `Type` 可表达的所有类型族 `p : a -> Type`。自反性保持证据不变；传递性依次通过两次转换传递证据。

普通相等通过模式匹配即可推出莱布尼茨相等。反过来，选择特定性质“与 `x` 相等”。由 `Refl` 可知这个性质在 `x` 处成立；应用给定的莱布尼茨相等，就得到它在 `y` 处成立，恰好是 `x = y`。对称性可以先转换成普通相等，反转，再转换回来。这些转换适用于任意类型和值，不限于自然数。

本章使用 Idris2 0.8.0 实际实现的 `Type`。它的[版本化 FAQ](https://github.com/idris-lang/Idris2/blob/v0.8.0/docs/source/faq/faq.rst)将该实现描述为 `Type : Type`，因此不能声称它提供可靠直谓宇宙层级的保障。源码没有复刻 Agda 的宇宙层级及宇宙多态相等接口。上述相等和莱布尼茨论证是显式证明程序，在这个宿主限制下接受检查；编译通过不等于一致性证明。准确边界见 [Trust](Trust.md#theorems)。

## 容易混淆的地方 {#pitfalls}

定义相等是检查器执行的计算；命题相等是承载证明的类型。二者相互配合，却不能混为一谈。合同性不能把逐点相等变成函数相等；反方向需要外延性，而这里没有假设它。改写可以改变类型索引，而不改变底层逻辑证据。改写失败时，应检查方向和被转移的准确类型族，而不是加入无关的算术引理。

## 习题与已检查解答 {#exercises}

1. **E.1 — 相等基础。** 通过匹配相等证据推导对称、传递和合同性。参考 `eqSym`、`eqTrans`、`eqCong`、`eqCong2`。
2. **E.2 — 推理链。** 写明各个中间端点，重建 `calculation`。再说明为何 `leChain` 不能提供不等式版本的 `sym`。参考 `calculation`、`leChain`。
3. **E.3 — 转移。** 分别使用替换和改写证明偶数交换定理。参考 `evenComm`、`evenCommRewrite`。
4. **E.4 — 莱布尼茨。** 证明两个转换和对称性。参考 `equalityToLeibniz`、`leibnizToEquality`、`leibnizSym`。关键是反方向中类型族的选择。

所有参考解答都来自已检查源码。这里没有假设通用的相等判定程序；[Decidable](Decidable.md#decisions) 将为自然数构造一个。

## 参考与改编说明 {#references}

改编自 [PLFA Equality](https://plfa.github.io/Equality/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。Idris 的相等和普通具名推理链组合子，替代 Agda 的显式相等模块及混合缀推理语法。这个宿主没有复刻 Agda 的宇宙层级，见 [Trust](Trust.md#theorems)。相等及莱布尼茨相等的证明方向作为已检查程序保留在所述边界内。

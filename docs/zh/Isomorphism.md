# Isomorphism：不同表示何时包含相同信息 {#isomorphism}

## 为什么研究同构 {#motivation}

两个类型可能以不同方式组织同样的信息。但仅有双向转换还不够：转换可能丢失信息。同构还包含证据，保证两个方向的往返都返回原输入。嵌入只要求其中一个方向的往返，因此适合某个表示允许额外值的情形。

## 函数与逐点相等 {#model}

{{include:src/PLFA/Part1/Isomorphism.idr#maps}}

lambda 通过命名输入来引入函数。函数组合先应用内层函数，再应用外层函数。`Pointwise f g` 表示每个输入上的输出都相等。两种加法说明了它的用途：一种对左参数递归，另一种对右参数递归。虽然定义计算不同，`sameApplications` 通过归纳和后继引理，证明结果一致。

**相等的范围。** 上游章节假设函数外延性，把所有输入上的一致提升为函数本身的命题相等。本改编没有假设这个公理。`sameApplications` 为每个 `m` 和 `n` 给出等式，但不是两个函数值本身命题相等的证明。后面涉及这个区别时，会明确保留逐点逆律。

## 同构记录 {#theorems}

{{include:src/PLFA/Part1/Isomorphism.idr#isomorphism}}

`Iso a b` 包含 `forward`、`backward` 及两条定律。对任意 `x : a`，`backward (forward x) = x`；对任意 `y : b`，`forward (backward y) = y`。这两条定律本来就是逐点陈述。定义普通数据类型之间的同构，不需要两个完整函数相等。

恒等转换给出自反性。交换映射及对应定律给出对称性。证明传递性时，组合两个正向映射，反序组合反向映射，然后先消去内层往返，再消去外层往返。左逆证明中，`cong i.backward` 把第二个同构的消去提升到第一个反向映射之下。剩下的表达式正是第一个同构的左逆定律。右逆证明与之对应。

## 嵌入与具体例子 {#examples}

{{include:src/PLFA/Part1/Isomorphism.idr#embedding}}

`Embedding a b` 包含嵌入映射 `embed`、恢复映射 `project` 以及恢复定律 `retract`。这个定律意味着 `embed` 不会把不同源值混成同一个值：对像的相等应用 `project`，就能恢复源值相等。但它不要求目标中的额外值满足什么。

`binaryEmbedding` 把每个自然数嵌入原始二进制位串。`fromTo` 保证解码选定的编码后得到原自然数。这里没有对所有位串成立的第二条定律，因为前导零变体会违反它。这个具体程序准确展示了嵌入与同构的区别。

嵌入和同构以相同方式组合。`isoToEmbedding` 直接忘掉第二条定律。在 `embeddingAntisym` 中，两个相反方向的嵌入只有加上相容性证据，才能用给定映射构成同构：每个映射必须与另一个嵌入的恢复映射逐点一致。定理**没有**宣称两个任意、不相关的嵌入都会自动使这些特定函数互为逆。

`Iff a b` 更弱：它只包含双向蕴涵，没有逆律，表示逻辑等价。自反、对称和传递操作组合这些蕴涵，但不保证恢复每个证据对象本身。

## 容易混淆的地方 {#pitfalls}

两个类型可见的构造子数目相同，并不能证明同构，因为构造子还可能携带不同数据。类型方向相反的两个函数不一定互逆。双向蕴涵证明的是 `Iff`，不会自动得到 `Iso`。另一方面，`Iso` 的定义本身不要求外部外延性公理；只有某些端点为函数的具体逆律证明可能需要它。应检查往返定律究竟要求哪一种相等。

## 习题与已检查解答 {#exercises}

1. **S.1 — 组合。** 证明同构的自反、对称和传递性。参考 `isoRefl`、`isoSym`、`isoTrans`；追踪组合左逆中的两次消去。
2. **S.2 — 忘掉证据。** 把同构转为嵌入，并组合嵌入。参考 `isoToEmbedding`、`embedTrans`。
3. **S.3 — 相容嵌入。** 在给出的相容性假设下，把相反方向的嵌入构造成同构。参考 `embeddingAntisym`，指出每个假设的用途。
4. **S.4 — 二进制。** 构造自然数到二进制的嵌入，并解释为什么它不是原始位串上的同构。参考 `binaryEmbedding` 和 Induction 中的 `notRawRoundTrip`。
5. **S.5 — 逻辑等价。** 实现无需往返证明的等价操作。参考 `Iff`、`iffRefl`、`iffSym`、`iffTrans`。

## 参考与改编说明 {#references}

改编自 [PLFA Isomorphism](https://plfa.github.io/Isomorphism/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。具名记录替代混合缀记录名。这里有意不公理化函数外延性或上游的完整函数相等示例；实际检查的结果是 `sameApplications`。嵌入定理的映射相容性采用逐点陈述。

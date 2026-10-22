# Lists：高阶程序的结构化证明 {#lists}

## 为什么学习列表 {#motivation}

自然数归纳沿着后继链前进，列表归纳沿着以空列表结束的元素链前进。同一种方法能够证明实用程序的性质：连接定律、反转正确性、映射与折叠的融合，以及返回所选每个元素之证据的算法。元素可以来自任意类型；驱动证明的是列表结构。

## 列表、连接与长度 {#model}

Idris 的 `List a` 有空构造子 `[]` 和非空构造子 `x :: xs`。类型参数规定元素种类，不固定列表长度。方括号 `[0, 1, 2]` 简写三个 cons 构造子后接空列表。

{{include:src/PLFA/Part1/Lists.idr#append}}

`append` 对第一个列表递归，把第二个列表直接用作最后的后缀。因此，第一个列表为空时，左单位元律由计算成立；右单位元律需要归纳。证明结合律时，去掉第一个列表的头，应用较小的定理，再用合同性恢复头。`sizeAppend` 沿着相同递归结构，把每个 cons 换成后继，把连接换成自然数加法。

## 反转与累积参数不变量 {#examples}

{{include:src/PLFA/Part1/Lists.idr#reverse}}

直接反转先递归反转尾部，再把头作为单元素列表连接到末尾。`reverseAppend` 表示反转连接会颠倒两部分的顺序；后继情形在归纳假设后使用连接结合律。`reverseInvolutive` 使用这个分配定理：反转“已反转的尾部接单元素列表”，会恢复原来的头，再接原来的尾部。

反复在末尾连接，需要遍历越来越长的前缀，遍历工作量为二次增长。`shunt` 则把每个头移动到累积参数前面。每个源元素只处理一次，因此其非形式化成本分析为线性；这里没有宣称证明机器成本定理。

正确性关键比最终结果更强：对**每个**累积参数 `ys`，都有 `shunt xs ys = append (reverseList xs) ys`。递归步骤把累积参数改为 `x :: ys`，因此固定为空的定理太弱。`shuntCorrect` 量化任意累积参数，`reversesAgree` 再把它特化为空，并使用连接右单位元律。

## 映射、折叠与树 {#theorems}

{{include:src/PLFA/Part1/Lists.idr#map-fold}}

`mapList` 改变每个元素，但保留列表结构。`mapCompose` 逐点合并两次遍历，`mapAppend` 将映射分配到连接。右折叠把空列表构造子替换为初值，把 cons 替换为给定组合函数；结果类型可以不同于元素类型。`sumList` 与 `productList` 分别以零和一作为空列表结果。

`foldAppend` 准确说明两个列表边界处的行为：折叠连接，等于以第二个列表的折叠结果为新初值，折叠第一个列表。这个定律不需要结合律假设。`foldCons` 用列表自己的构造子重建列表，`mapAsFold` 用构造 cons 的代数表达映射。

{{include:src/PLFA/Part1/Lists.idr#trees}}

`Tree a b` 区分叶子的载荷和内部节点的标签。`mapTree` 转换二者，`foldTree` 为每种构造子提供对应操作。`mapTreeAsFold` 对两个子树归纳，证明映射是一种特定折叠。这是分支数据上的结构递归，并没有假设所有树具有某一种固定形状。

## 幺半群与折叠方向 {#monoids}

{{include:src/PLFA/Part1/Lists.idr#monoids}}

`MonoidLaw` 为一个运算和单位元包装结合律及两个单位元律。加法与零、乘法与一、连接与空列表，都用先前证明填入具体记录。装有定律的记录不会自己变成证明：每个字段都由已检查函数填充。

`foldMonoid` 把最后的初值移到折叠外面，`foldMonoidAppend` 再把连接变为幺半群运算。累积不变量 `foldLeftInvariant` 把从任意累积值开始的左折叠与右折叠联系起来。结合律只移动括号，不改变元素顺序，因此**不需要**交换律。把累积值特化为单位元，就得到 `foldDirectionsAgree`。

`downFrom n` 列出从 `n - 1` 到零的数。`sumDownFromTimes` 证明准确且不含除法的等差数列公式：总和乘二等于 `n * (n ∸ 1)`。辅助定理 `sumDownFrom` 用加法表达双倍总和。归纳步骤用 `doubleAdd` 整理新增的两个首项，应用较小的求和定理，再使用乘法交换律。零和一都显式处理，因此零处截断没有带来隐藏的正数前提。

## 关于列表元素的证据 {#predicates}

{{include:src/PLFA/Part1/Lists.idr#predicates}}

`All p xs` 为每个元素保存一份 `p` 的证明。`Any p xs` 选择一个位置：`Here` 证明头满足 `p`，`There` 将尾部见证右移一位。成员关系把 `Any` 的谓词特化为与某个值相等。

列表 `[0, 1, 0, 2]` 在两个位置包含零。`firstZero` 与 `secondZero` 有意使用不同的证据构造子。成员关系具有证明相关性：值可能出现多次，因此成员证据不一定唯一。`threeAbsent` 检查每个可能位置，并消去不可能的相等。

## 列表量化定律 {#quantified-laws}

{{include:src/PLFA/Part1/Lists.idr#quantified-laws}}

若连接后的每个元素都满足 `p`，可以把证据分成两部分；`allAppendFrom` 将它们重新组合。`allAppendIso` 对实际证据树证明双向往返，没有使用一般的证明无关性或函数外延性。递归拆分定理记录中间对的等式，使逆向证明准确对应所选分量。

对于 `Any`，连接中的某个位置属于其中一部分，得到 `anyAppendIff`。反驳所有可能的 `Any` 见证，等价于在每个位置持有反证，正如 `notAnyIff` 所示。后一命题是 `Iff`，不是上游涉及函数的外延 `Iso`。

`allForall` 把 `All` 联系到一个函数：只要收到 `x` 的成员证据，就返回 `p x`。`allForallLeft` 证明证据树恢复，`allForallPointwise` 在每个值及其成员证据上证明恢复。函数端点按逐点方式处理，不使用外延性。`anyExistsIso` 是 `Any` 与“实际元素、成员证据、谓词证据”之间的完整数据同构；`anyExists` 保留较简单的双映射接口。这些转换保留了与列表的联系；没有成员证据的存在见证并不够。

## 判定谓词与有证据的划分 {#decidable-split}

{{include:src/PLFA/Part1/Lists.idr#decidable-split}}

若元素谓词有判定程序，`decAll` 逐个检查直到发现反证，`decAny` 则寻找一个见证。空列表的结果不同：`All` 真空成立，`Any` 却没有构造子。否定结果都是函数，会检查任何候选证据，并反驳失败的分量。

`Merge xs ys zs` 记录交织关系：`zs` 的每个元素来自某个输出列表的头，保持各输出内部顺序。`split` 返回两个列表、把它们合并回原输入的证明、第一列表所有元素满足谓词的证明，以及第二列表所有元素反驳谓词的证明。肯定判定把元素放到第一列表前面并用 `MergeLeft`；否定判定放到第二列表前面并用 `MergeRight`。因此，结果完整说明整个输入的去向，包括重复元素，而不只是证明某个可能遗漏元素的过滤列表具有性质。

## 容易混淆的地方 {#pitfalls}

累积参数的证明常常需要比最终目标更强的不变量。任意运算的左右折叠不一定相等，幺半群假设不可省略。`All` 不是“列表非空”，`Any` 也不是“所有元素满足谓词”。不能暗中把不同位置的重复成员证据视为相同。最后，在几个输入上测试过滤函数，弱于 `split` 返回的完整合并证据和谓词证据。

## 习题与已检查解答 {#exercises}

1. **L.1 — 连接。** 证明结合律、右单位元律和长度定律。参考 `appendAssoc`、`appendRightNil`、`sizeAppend`。
2. **L.2 — 反转。** 证明反转对连接分配，并证明反转两次恢复原列表。参考 `reverseAppend`、`reverseInvolutive`。
3. **L.3 — 更快反转。** 先陈述累积参数不变量，再证明优化后的反转正确。参考 `shuntCorrect`、`reversesAgree`。
4. **L.4 — 映射。** 证明映射组合及对连接的分配。参考 `mapCompose`、`mapAppend`。
5. **L.5 — 折叠与树。** 定义连乘，证明连接折叠律，以及列表和树上的映射即折叠定律。参考 `productList`、`foldAppend`、`foldCons`、`mapAsFold`、`mapTree`、`foldTree`、`mapTreeAsFold`。
6. **L.6 — 等差求和。** 对所有自然数，包括零，证明双倍和公式。参考 `sumDownFromTimes` 及辅助定理 `doubleAdd`、`sumDownFrom`。
7. **L.7 — 幺半群。** 在准确的幺半群假设下，证明折叠对连接分配，以及两种折叠方向一致。参考 `foldMonoidAppend`、`foldLeftInvariant`、`foldDirectionsAgree`。
8. **L.8 — 量化定律。** 拆分并重组 `All`，定位连接中的 `Any` 见证，并分配其否定。参考 `allAppendIso`、`anyAppendIff`、`notAnyIff`。
9. **L.9 — 成员关系。** 将 `All` 转换为以成员证据索引的全称证明，将 `Any` 转换为存在包。参考 `allForall`、`allForallLeft`、`allForallPointwise`、`anyExistsIso`。
10. **L.10 — 认证算法。** 判定 `All` 与 `Any`，再带完整重建证明划分列表。参考 `decAll`、`decAny`、`split`、`mergeExample`。

## 参考与改编说明 {#references}

改编自 [PLFA Lists](https://plfa.github.io/Lists/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。通用列表和树定律、幺半群前提、等差数列定理、量化证据及完整认证划分全部保留。否定 `Any` 的对应以 `Iff` 检查，`All` 与全称的对应具有证据树逆律和逐点逆律；不假设它们在函数值上的外延 `Iso` 提升。所有展示的 Idris 都直接包含自已编译模块。

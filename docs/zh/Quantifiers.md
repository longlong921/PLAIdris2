# Quantifiers：类型族上的函数与带见证的包 {#quantifiers}

## 为什么需要量词 {#motivation}

“每个自然数都有二进制表示”要求一个产生表示的函数。“存在某个自然数满足性质”要求一个具体的数，以及该性质的证据。依赖函数和依赖对直接表达这些要求，并始终把见证与涉及它的证据联系在一起。

## 全称量词 {#model}

{{include:src/PLFA/Part1/Quantifiers.idr#universals}}

类型族 `p : a -> Type` 给每个 `x : a` 指定一个命题。全称证明的类型为 `(x : a) -> p x`：结果类型可以随参数变化。`forallElim` 只需把它应用于选定值。

`forallProduct` 把返回成对证据的函数拆成两个依赖函数，再组合回来。组合后的每个结果通过 `pairEta` 恢复。这是带逐点逆定理的 `Iff`，不是任意依赖函数之间的相等。`sumForall` 从全局统一选择的全称分支，得到每个输入上的选择。反方向没有根据，因为有效的分支可能随输入而变。

`Tri` 有三个值。其上的全称命题对应三份证据，类型分别为 `p Aa`、`p Bb`、`p Cc`。`triTabulate` 通过匹配索引选出正确项；`triRound` 证明把函数的三个结果制成表后，会在每个输入上恢复原答案。因此，有限类型族上的全称量化表现为积。

## 存在量词及消去 {#examples}

{{include:src/PLFA/Part1/Quantifiers.idr#existentials}}

依赖对 `(x ** px)` 的类型是 `(x : a ** p x)`。第一分量是见证，第二分量的类型依赖这个见证。普通对的第二分量类型固定，依赖对则不然。`existsElim` 打开包，把两个分量交给一个消费者，消费者最终的结果类型不依赖隐藏的见证。

`existsCurry` 在“先接收见证，再接收证据”的函数与“接收整个包”的函数之间转换，`existsCurryRound` 逐输入检查恢复。存在量化对和分配：包中含有分支标签，所以只需将标签移到外面，同时保持同一个见证。`existsSum` 证明双向往返，是数据上的真正 `Iso`。有限的 `existsTri` 同样是依赖包与三种可能证据类型之和之间的 `Iso`。

`existsProduct` 从一个共享见证中提取两个存在包。反方向必须把可能不同的见证统一起来，因此没有提供。例如，在 `Bool` 上，“是 True”和“是 False”分别都有见证，但没有一个值同时满足两者。所以存在量词一般不能作为同构分配到合取之上。

## 算术见证 {#theorems}

{{include:src/PLFA/Part1/Quantifiers.idr#parity-witnesses}}

偶数可以给出它的一半：`evenWitness` 产生 `k` 及等式 `mul k 2 = n`。奇数产生 `k` 及 `S (mul k 2) = n`。两个函数对奇偶证据互相递归。若奇数前驱给出一半，其偶数后继使用这个一半的后继；若偶数前驱给出一半，其奇数后继使用同一个一半。

反过来，`evenDouble` 构造任意自然数两倍的偶数证据。`witnessEven` 沿包中的等式转移该证据。`witnessOdd` 先加入奇数构造子，再转移。左乘版本利用交换律及将末尾的一移到前面的等式，证明 `2 * k` 形式的两个方向。

`leExists` 用非负差刻画 `m ≤ n`：存在 `k` 使 `k + m = n`。`leWitness` 的左端为零时，选择 `n` 作为差；后继情形保持递归找到的差，并把后继移过加法。反方向使用界 `m ≤ m + k`，交换加数，再转移到 `n`。所有见证都由程序实际产生，而不是作为没有解释的存在性断言记录下来。

## 否定量词 {#negated-quantifiers}

{{include:src/PLFA/Part1/Quantifiers.idr#negated-quantifiers}}

要反驳存在命题，就需要对每个候选见证反驳相应证据。`notExists` 证明两个蕴涵方向。要反驳全称命题，一个反例就足够：`existsNot` 取出见证，在该点反驳全称函数的答案。这里没有构造性地宣称反方向，即仅由全称命题的反证就提取反例。上游第一条定律的外延同构在这里表示为 `Iff`，不比较整个反证函数的相等。

## 规范二进制同构 {#canonical-isomorphism}

{{include:src/PLFA/Part1/Quantifiers.idr#canonical-isomorphism}}

`CanonicalBin` 把原始位串与其规范性证明配对。自然数映射到它的编码及 `canonicalTo` 证据；解码时忘掉证明，解释位串。自然数一侧的逆律为 `fromTo`。

另一条逆律必须恢复**整个依赖对**。`canonicalRoundTrip` 给出位串相等，但它本身没有比较证明分量。`canonicalPairEqual` 先利用这个等式对齐类型，再应用 `canonicalUnique`。这样就完成了 `canonicalIso : Iso Nat CanonicalBin`。限制恰好排除前导零造成的多个表示，没有改变自然数的论域。

## 容易混淆的地方 {#pitfalls}

存在证明包括一个见证，不只是“搜索可能成功”的说明。两个存在命题可能选择不同见证。第一投影相等通常不保证依赖对相等；这里是特定谓词的证明唯一性补上了缺失步骤。全称依赖函数的结果类型可能随输入变化，把这些结果当成同质列表会丢失信息。

## 习题与已检查解答 {#exercises}

1. **Q.1 — 全称。** 将全称量词分配到积，并为三元素论域制表。参考 `forallProduct`、`forallProductRound`、`forallTri`、`triRound`。
2. **Q.2 — 存在。** 证明对和的分配及三元素存在同构。参考 `existsSum`、`existsTri`，并解释为何 `existsProduct` 只有一个方向。
3. **Q.3 — 奇偶见证。** 对乘法的两种方向，产生并使用奇偶见证。参考 `evenWitness`、`oddWitness`、`witnessEven`、`witnessOdd`、`evenWitnessLeft`、`oddWitnessLeft`、`witnessEvenLeft`、`witnessOddLeft`。
4. **Q.4 — 差。** 证明序关系的差值刻画。参考 `leExists`，其中使用 `leWitness` 与 `witnessLE`。
5. **Q.5 — 否定。** 联系“存在命题的反证”与“对每个见证的反证（∀x.¬P x）”，并利用反例反驳全称命题。参考 `notExists`、`existsNot`。
6. **Q.6 — 二进制同构。** 完成依赖规范包的相等，再构造双向逆律。参考 `canonicalPairEqual`、`canonicalIso`。

## 参考与改编说明 {#references}

改编自 [PLFA Quantifiers](https://plfa.github.io/Quantifiers/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。Idris 依赖对替代 Agda 的 sigma 记法。数据同构、算术见证和完整规范二进制同构均接受检查。需要完整函数外延性的对应，明确陈述为逻辑等价与逐点定律。

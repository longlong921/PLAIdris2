# Decidable：计算答案，同时携带证据 {#decidable}

## 为什么需要可判定性 {#motivation}

布尔比较便于执行，但结果本身没有解释所计算的关系。归纳关系提供证据，却没有自动提供寻找证据或排除证据的算法。判定程序把两者结合：它终止时返回见证，或者返回一个能反驳每个候选见证的函数。

## 布尔值与证据 {#model}

{{include:src/PLFA/Part1/Decidable.idr#boolean-evidence}}

`Truth True` 是单位类型，`Truth False` 是空类型。因此 `Truth` 将布尔值解释为恰好在真时成立的命题。`truthEquality` 把这种解释联系到与 `True` 相等，`equalityTruth` 给出反方向。这明确建立了计算与命题之间的桥梁。

`leBool` 按顺序关系的结构递归。`boolToLE` 证明可靠性：若比较为真，就存在顺序证据。`leToBool` 证明完备性：顺序证据会迫使比较为真。后继情形都归约为前驱问题。两个方向都没有暗中假设任意布尔值是正确比较；它们关联的是这个特定算法和这个特定关系。

## 判定程序 {#decisions}

{{include:src/PLFA/Part1/Decidable.idr#decisions}}

Idris 的 `Dec a` 有携带 `a` 的 `Yes`，以及携带 `a -> Void` 的 `No`。`decLE` 对零返回 `Yes LZ`。正数不大于零是不可能的，所以该分支返回已检查的反证。两边都是后继时，递归判定前驱；成功就用 `LS` 包装证据，失败则剥去任何假设证据的 `LS`，再交给递归得到的反证。

`decLT` 使用移位后的非严格关系。`decNatEq` 比较构造子，对两个后继递归；遇到假设的后继相等时，用 `succInjective` 提取已经被反驳的前驱相等。这些是具体归纳命题的判定，不是无限制的排中律。

`decBool` 忘掉证据。当遗忘后的结果为真时，`toWitness` 恢复证据；`fromWitness` 证明有效见证会迫使给定判定为肯定。`reflectedLE` 证明对任意两个数，擦除 `decLE` 得到的答案都与 `leBool` 一致。它的 `with` 分类记录递归判定的等式，以便把检查的分支与原表达式联系起来。

## 具体计算 {#examples}

`decisionExamples` 检查二不大于四、四不小于等于二，以及三等于自身。跟踪否定比较：剥去两对后继后，剩下不可能的“二不大于零”。返回的 `No` 是一个组合反证，能反驳任何声称证明原比较的证据，而不是错误字符串或缺失的结果。

## 组合判定 {#theorems}

{{include:src/PLFA/Part1/Decidable.idr#connectives}}

两个分量都可判定时，合取也可判定。两份见证产生一个对；任何一个被反驳的分量，都可通过投影反驳整个对。析取只要任一见证可得就成功；只有两份反证才能拒绝和。否定在已有反证与对正面证据的反驳之间转换。

对于蕴涵，被反驳的前提允许通过爆炸律构造函数。两边都有见证时，常值函数足够。若前提有见证、结论有反证，则应用任何候选函数都会导致矛盾。`decIff` 判定两个蕴涵方向，再包装成 `Iff`。

擦除定理证明这些算法与布尔合取、析取、否定、蕴涵及双条件真值表一致。它们只比较布尔答案，不比较 `Yes` 中可能不同的证明对象，也不比较 `No` 中的反证函数。因此，算法既携带证据，又保持熟悉的可执行行为。

## 通过反射证明 {#reflection}

{{include:src/PLFA/Part1/Decidable.idr#reflection}}

`minus m n` 要求 `n ≤ m` 的证据。它的不可能分支说明前置条件排除了下溢。`safeMinus` 把显式推导换成自动提供的证明：判定的布尔结果为真。已经检查的判定通过 `toWitness` 构造所需顺序证据。

对于具体表达式 `safeMinus 5 3`，规范化把判定算成真，隐式搜索只需填入单位证明。`safeMinusExample` 检查结果为二。如果输入使前置条件为假，要求的隐式类型就成为 `Void`，普通证明搜索不能凭空构造居民。参数为变量时，判定可能无法继续计算，调用者便可能需要提供证据。反射不是预言机，它依赖已证明的判定程序和类型层的求值。

`FalseDecision` 给出对应的否定解释。`fromFalse` 从否定判定提取反证；`toFalse` 证明已有反证会迫使该判定的布尔结果为否定。

## 判定规范二进制语法 {#binary-decisions}

{{include:src/PLFA/Part1/Decidable.idr#binary-decisions}}

`decOne` 检查有限位串结构。单独的首位一成功；追加数字需要前缀已有首位为一的证据；空串及只有前导零的形式失败。`decCanonical` 单独接受一位零，其余情形要求正数规范证据。`positiveDecision` 在输入形状已经排除零构造子的地方，共享产生证明的逻辑。

例子区分零、不规范的额外零以及二。这个判定检查表示语法，不是检查位串是否表示自然数；每个原始二进制位串本来就有自然数解释。

## 容易混淆的地方 {#pitfalls}

`No` 必须包含反证，不能放猜测或超时。擦除判定会丢失有用证据，后续需要见证时应保留 `Dec`。布尔相等不会自动变成顺序推导，需要使用已经证明的桥梁。反射能消去具体前置条件，却可能保留符号化条件；这是预期行为，不是定理失效。

## 习题与已检查解答 {#exercises}

1. **D.1 — 顺序与相等。** 实现带反证的严格顺序及自然数相等判定。参考 `decLT`、`decNatEq`。
2. **D.2 — 反射桥梁。** 在布尔真与顺序证据间转换，并证明两种比较擦除后相同。参考 `boolToLE`、`leToBool`、`reflectedLE`。
3. **D.3 — 逻辑判定。** 判定合取、析取、否定、蕴涵和等价。参考 `decAnd`、`decOr`、`decNot`、`decImplies`、`decIff`。
4. **D.4 — 擦除。** 证明五个布尔真值表对应。参考 `andErasure`、`orErasure`、`notErasure`、`impliesErasure`、`iffErasure`。
5. **D.5 — 安全减法。** 使用反射的前置条件，检查五减三。参考 `safeMinus`、`safeMinusExample`；再通过 `fromFalse`、`toFalse` 推导否定版本。
6. **D.6 — 二进制语法。** 判定首位为一和规范谓词，并在两种结果中保留证据。参考 `decOne`、`decCanonical`、`canonicalDecisionExamples`。

## 参考与改编说明 {#references}

改编自 [PLFA Decidable](https://plfa.github.io/Decidable/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。Idris 的 `Dec` 与隐式参数搜索替代 Agda 的判定数据类型和实例参数记法。证据与计算的对应、联结词擦除律、反射实例和二进制谓词判定，都在完整的所述论域上接受检查。

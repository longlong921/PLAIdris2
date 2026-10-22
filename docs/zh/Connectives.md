# Connectives：把命题理解为有结构的证据 {#connectives}

## 为什么这样理解逻辑 {#motivation}

证明“A 且 B”，需要同时给出两份证据。证明“A 或 B”，需要选择一边并给出证据。证明“A 蕴涵 B”，需要给出一个过程，把任意 A 的证据转换为 B 的证据。这种计算式理解解释了逻辑联结词为何对应熟悉的类型：对、带标签的选择以及函数。

## 积与真 {#model}

{{include:src/PLFA/Part1/Connectives.idr#products}}

对 `(x, y)` 证明合取；`fst` 与 `snd` 通过选择所需证据消去合取。`pairEta` 说明拆开再重建一个对会得到原值，两个投影提供了重建所需的全部信息。`productComm` 交换分量，`productAssoc` 改变嵌套方式。二者都是真正包含双向逆律的 `Iso` 记录。

单位类型 `()` 只有一个同样写成 `()` 的构造子，表示真。与单位值配对不增加信息，`unitLeft` 和 `unitRight` 证明这一点。`iffProduct` 把双向蕴涵记录与函数对联系起来；检查记录和对即可得到逆律，无需比较任意函数体。

## 和与假 {#examples}

{{include:src/PLFA/Part1/Connectives.idr#sums}}

`Either a b` 带有标签：`Left x` 或 `Right y`。即使载荷类型恰好相同，标签仍然有意义。`sumCase` 为每种选择提供一个处理函数，以此消去和。`sumEta` 重建被选中的分支。`sumUnique` 说明：任意从和出发的函数，在每个输入上都等于由它在两个构造子上的行为所确定的分类讨论。

有两个值的类型与有三个值的类型，其和有五种选择，其积有六个对。这解释了“和”与“积”的名称。计数是类型结构的有限示例，不是一般同构的证明。`sumComm` 和 `sumAssoc` 通过构造子分析证明一般定律。

空类型 `Void` 没有构造子，表示假。`explode` 把不可能的证据消去为任何所需类型。没有构造子提供这样的输入；使用这个消去函数需要实际的矛盾证据。宿主基础的边界见 [Trust](Trust.md#theorems)。`emptyLeft` 与 `emptyRight` 证明：添加一个不可能的选择，不增加任何类型居民。

## 蕴涵就是函数 {#theorems}

{{include:src/PLFA/Part1/Connectives.idr#functions}}

应用函数就是消去蕴涵。若 A 有两个值、B 有三个值，从 A 到 B 的全函数可以在每个输入上独立选择三个结果之一，因此共有九张可能的函数表。这说明函数空间为什么对应指数。

柯里化把接收一个对的函数改为依次接收两个输入。`curryPair` 与 `uncurryPair` 实现转换。`curryRound` 对每两个输入证明恢复，`uncurryRound` 对每个对值证明恢复。`functionSum` 表示接收和的函数与一对分支处理函数逻辑等价；其中非平凡的逆方向来自分类讨论唯一性。`functionProduct` 将返回对的函数拆成两个函数，`functionProductRound` 用对的 eta 性质恢复每个结果。

**准确范围：** 这三个函数空间对应是带逐点恢复定理的 `Iff`，不是端点包含任意函数的 `Iso` 记录。其余恢复方向在每个输入上按定义计算成立。上游用外延性提升为完整函数相等，本书没有假设这种提升。

## 分配与信息丢失 {#distribution}

{{include:src/PLFA/Part1/Connectives.idr#distribution}}

分配 `(Either a b, c)` 时，先检查标签，再把随附的 `c` 放入选中的分支。反向提取可以恢复原值，因此 `productSum` 是真正的同构。

另一个模式从 `Either (a, b) c` 到 `(Either a c, Either b c)`，得到的是已检查的嵌入。左边的对变成两个左分支，右边的值复制到两个右分支。但目标还允许混合标签，以及两个不同的右侧载荷，所以给出的投影不一定恢复每个目标值。`sumProduct` 只陈述已经证明的左逆。

`weakDistribution` 在选择左分支时丢掉随附的 `c`。`disjunctToConjunct` 把两个合取的析取转成两个析取的合取。一般逆命题不成立：令 A、D 为单位类型，B、C 为空类型，则目标对存在 `(Left (), Right ())`，而源的任一分支都需要不可能的证据。`noGeneralConverse` 把这个反例检查为对这些类型上任何逆向函数的反证。

## 容易混淆的地方 {#pitfalls}

析取必须知道哪一边成立；不能把一个对当作没有标签的“或”。爆炸律不会凭空制造矛盾，它要求输入矛盾。仅仅实现双向映射，不能把嵌入称为同构。当端点值是函数时，必须继续区分逐点恢复与这些函数值的命题相等。

## 习题与已检查解答 {#exercises}

1. **C.1 — 积。** 证明交换、结合及真作为单位元的定律。参考 `productComm`、`productAssoc`、`unitLeft`、`unitRight`。
2. **C.2 — 和。** 证明交换、结合及假作为单位元的定律。参考 `sumComm`、`sumAssoc`、`emptyLeft`、`emptyRight`。
3. **C.3 — 函数。** 实现柯里化，并证明两个逐输入往返。参考 `currying`、`curryRound`、`uncurryRound`。
4. **C.4 — 分配。** 给出积对和的完整分配同构，以及弱分配函数。参考 `productSum`、`weakDistribution`，指出后者丢弃的数据。
5. **C.5 — 失败的逆命题。** 实现从合取的析取出发的蕴涵，并反证其不受限制的逆命题。参考 `disjunctToConjunct`、`noGeneralConverse`。

## 参考与改编说明 {#references}

改编自 [PLFA Connectives](https://plfa.github.io/Connectives/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。使用 Idris 标准的对、单位、和及空类型表示联结词。函数空间同构改为展示已检查的逻辑等价与逐点定律，明确不采用上游的外延性假设。

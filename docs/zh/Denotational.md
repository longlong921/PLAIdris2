# Denotational：无类型函数的有限信息语义 {#denotational}

## 动机 {#motivation}

归约序列解释程序怎样运行；指称语义则描述程序能够提供哪些信息。这两种
观点应当相符，但不必使用相同的对象。本章用输入、输出表的有限片段来描述
无类型函数。

为什么只取有限片段？完整的函数表可能有无穷多行；恒等函数就能接受所有
可能的参数。一次有限观察只需有限多行，因此可以用归纳定义的值表示每个
观察，再用全部观察的集合表示整个函数。

自应用又带来一个困难：函数的精确表不能在输入中原样包含自身。因此，我们
允许实际参数提供的信息**多于或等于**某一行所要求的信息。表中只需出现
该函数自身的较小描述。这样，有限树就能描述包含自应用的无类型语言。

本章使用 [Untyped](Untyped.html#model) 中完整的带作用域语法。程序大小、
归约步数、语义值的深度均没有固定上限。证明不运行一个有步数限制的求值器，
而是操作“某个观察确实成立”的有限推导。

## 模型 {#model}

### 信息值与信息序 {#information}

`Value` 有三个构造子。`Bottom` 不提供信息；`Arrow a b` 表示函数在参数提供
观察 `a` 时能够产生观察 `b`；`Join a b` 同时包含两份观察。每个值都是有限树，
它不是运行时闭包，也不保存 lambda 的函数体。

把 `Info a b` 读作“a 的信息不多于 b”，也写作 a ⊑ b。前五种规则分别表示
底元素、并的最小上界性质和传递性。自反性通过对值递归来证明，没有另加
一条规则。

`IFun` 的方向尤其需要留意。要得到
`Info (Arrow a b) (Arrow a' b')`，需要 `Info a' a` 和 `Info b b'`。
如果一个函数要求的输入信息**更少**，而提供的输出信息**更多**，那么它的
描述就更有信息。输入是逆变的，输出是协变的。这讨论的是行为描述之间的
关系，与求值先后次序无关。

`IDist` 表示：输入相同的两行，可以共同提供两份输出的并。派生引理
`mixedDist` 先合并两个可能不同的输入要求，再合并输出。它是下一章
[应用组合方程](Compositional.html#application-equation) 的关键。

{{include:src/PLFA/Part3/Denotational.idr#information}}

例如，`joinCommute` 证明 `Info (Join a b) (Join b a)`：从目标的右支选出
`a`，从左支选出 `b`，再用 `IJoinL` 合并两份证据。这一结论及其反向都不
断言两个语法树具有命题相等性。信息序是预序，不同的树可以表达等价信息。

### 环境 {#environments}

`Env n` 把 `n` 个可用变量，即 `Fin n` 的元素，映到有限信息值。扩展环境时，
新值放在 `FZ`，旧变量 `x` 的赋值保存在 `FS x`。最新引入的变量位于零号位置，
与替换的约定一致。

`EnvLE g d` 逐点比较环境：对每个变量，`d` 提供的信息都不少于 `g`。
`joinEnv` 也逐点计算并；两个投影引理允许我们合并分别取得的自由变量信息。

`envEta g x` 在**每个索引处**证明：取出环境的头和尾，再接回去，结果相同。
我们有意使用逐点等式。这里及后续章节都不需要假设函数外延性。

{{include:src/PLFA/Part3/Denotational.idr#environments}}

### 指称判断 {#judgment}

`Denote g m v` 表示：在环境 `g` 中，`v` 是项 `m` 的一个有根据的有限观察。
可以把这些规则看成一门小型证明语言：

1. `DVar` 取出环境赋给变量的信息。
2. `DLam` 构造一行函数表。为了观察 `Arrow a b`，把参数赋为 `a`，再证明
   函数体具有观察 `b`。
3. `DApp` 从函数中选择一行，并由实参提供这一行要求的输入。
4. `DBot` 什么也不观察，因而适用于任意项。
5. `DJoin` 合并同一项的两个观察。
6. `DSub` 按 `Info` 丢弃一部分信息。

`DApp` 的中间值必须一致，但这不意味着查表只能精确匹配。`applyLarger`
先用 `DSub` 丢弃实参多余的信息，就可以应用这一行。

{{include:src/PLFA/Part3/Denotational.idr#judgment}}

`DBot` 对按名求值特别重要。函数可能忽略一个发散的参数；这个参数仍然能
提供 `Bottom`，满足一个未被使用的形参的要求。得到 `Bottom` 的推导本身
既不证明终止，也不证明发散。

### 指称相等 {#equality}

`Denotation n` 是从环境、观察到证据类型的关系。`meaning` 只是把项参数放在
最前面。`DenEq d e` 要求：对每个环境和每个值，两边的证据类型之间都有
一个正向函数和一个反向函数。`SemEq m k` 把这一定义用于两个项。

这种相等比较的是有效观察的集合，不是推导树。`denEqRefl`、`denEqSym`、
`denEqTrans` 证明它构成等价关系。这些都是逐点构造，没有通过外延性公理
直接把两个函数等同起来。

{{include:src/PLFA/Part3/Denotational.idr#equality}}

## 推导示例 {#examples}

对任意有限值 `a`，恒等函数都具有观察 `Arrow a a`。在 lambda 内部，`DVar`
恰好提供参数的信息；`DLam` 把这一推导变为一行函数表。`identityTable`
把两行合并起来，`identitySelf` 则把恒等函数的一个观察用作另一个观察的输入。

对于 Δ = λx. x x，向参数提供 `Join (Arrow a b) a`。第一个 `x` 选择
`Arrow a b`，第二个选择 `a`，应用得到 `b`。两个出现位置共享同一个环境，
却使用其中不同的信息。这就具体解决了自应用带来的困难。

Ω = Δ Δ 也有一个观察为 `Bottom` 的有限推导。`omegaBottom` 展示实际的
查表匹配：第一个 Δ 提供一行，其输入为 `Join (Arrow Bottom Bottom) Bottom`；
第二个 Δ 恰好提供这个并。也可以直接用更短的证明 `DBot`。这两个证明都不能
单独排除 Ω 还有其他更丰富的观察。

最后，Church 二向函数参数要求两行：`Arrow a b` 和 `Arrow b c`。第一次
应用从 `a` 到 `b`，第二次从 `b` 到 `c`。这些值并不需要是自然数。

{{include:src/PLFA/Part3/Denotational.idr#examples}}

## 定理与证明思路 {#theorems}

### 更多信息保持原有观察 {#monotonicity}

`envMono` 证明：若有 `Denote g m v` 和 `EnvLE g d`，则有 `Denote d m v`。
变量分支先在新环境中使用 `DVar`，再用 `DSub` 丢弃额外信息。lambda 分支
给两个环境扩展同一个输入值。其余分支直接重建原来的证明构造子。
`upEnv` 是只增加最新变量信息的特例。

更一般的 `renamePres` 还允许改变变量索引。它的前提要求：对每个旧变量，
`g x` 的信息不多于 `d (rho x)`。lambda 分支使用 `liftRen rho`，固定新绑定
的变量，并把旧变量向后移动。这个语义重命名定理适用于任意项和任意有限观察。

{{include:src/PLFA/Part3/Denotational.idr#renaming}}

### 提取函数表中的行 {#membership}

假设一个箭头位于复杂的并之下，不能直接断定其中某一行就提供了全部输出：
`IDist` 可能把多行结合起来。因此，我们必须提取**一组**行。

`Member` 记录并树中的一个叶子；`Included` 把一棵树中的每份成员证据映到
另一棵树中的成员证据。在这里，`Bottom` 虽然没有信息，却仍算一个表示层面的
叶子。`AllFuns` 表示所有叶子都是箭头，因此至少存在一个箭头。这些约定使
反演定理能够精确陈述。

`joinDomain` 合并各行的输入，`joinCodomain` 合并各行的输出。
`memberInfo` 和 `includedInfo` 证明字面上的成员关系和包含关系蕴含信息序。
反过来并不成立：逆变、协变和分配规则都能建立没有字面成员关系的信息序。

{{include:src/PLFA/Part3/Denotational.idr#membership}}

### 函数反演 {#factorization}

`Factor whole selected a b` 打包的是已经**证明出来的证据**：`selected`
只包含函数行，被 `whole` 包含，其输入要求至多为 `a`，输出合起来至少包含
`b`。这些字段是下面证明构造的结论，不是绕过证明而预先假定的定理。

`subInv` 证明一个加强的命题：若 `Info u v`，且 `Arrow a b` 是 `u` 中的一行，
那么 `v` 中存在一组行，可以分解出这个箭头的信息。加强命题是为了处理传递性。
先从中间值提取一组行，再由 `factorAcross` 递归地用最终值中的行替换它们。
`mergeFactors` 合并所得集合，传递性把定义域和陪域的界接起来。
对于 `IDist`，两行都需要选中；它们的重复输入之并，根据幂等性不大于原输入。

推论 `arrowInversion` 的准确范围是：
`Info (Arrow a b) (Arrow c d)` 蕴含 `Info c a` 和 `Info b d`。
它对信息序的**所有推导**都成立，包括经过中间并、使用传递性的推导，
而不是只对 `IFun` 构造子做一次匹配。`arrowNotBottom` 进一步证明：即使是
`Arrow Bottom Bottom`，信息也严格多于 `Bottom`。

{{include:src/PLFA/Part3/Denotational.idr#factorization}}

## 常见误区 {#pitfalls}

- `Bottom` 表示没有信息，不是某个特殊运行结果。包括能终止的 lambda 在内，
  每个项都有这个观察。
- lambda 可以有任意大的有限观察。它的指称不是预先选定的一张有限表。
- 箭头输入是逆变的；把前提方向写反会改变整个模型。
- `Join` 表示信息合并，不表示程序的非确定执行。
- `Value` 树的语法相等强于 `Info` 意义下的等价。
- 语义相等还不是操作行为定理。[Soundness](Soundness.html#theorems)、
  [Adequacy](Adequacy.html#theorems) 和 [ContextualEquivalence](ContextualEquivalence.html#theorems)
  将证明它与归约及可观察终止行为的联系。

## 习题与已检查解答 {#exercises}

### 习题 1：并的定律 {#exercise-1}

对任意值，证明 `Info (Join a b) (Join b a)` 和 `Info (Join a a) a`。
只使用信息序构造子，不比较或化简语法树。

**已检查解答：**`joinCommute` 在 `IJoinL` 的两项前提中分别选择目标的另一支；
`joinIdempotent` 合并两份自反性证据。这两个定义已包含在
[信息值](#information) 一节中。再用一次 `joinCommute` 得到反向信息序，
并不能由此得到两棵树的命题相等。

### 习题 2：Church 加法 {#exercise-2}

给出 λm. λn. λf. λx. m f (n f x) 的非底观察。假设第一个数接受观察 `f`
后将 `b` 映到 `c`，第二个接受 `f` 后将 `a` 映到 `b`。它们的和应具有哪一行？

**已检查解答：**`churchPlusMeaning` 描述和在相同的 `f` 下，把 `a` 映到 `c`。
四个 `DLam` 绑定参数；内部推导把 `f` 提供给两个数，先将第二个数用于 `x`，
再把所得观察交给第一个数。这证明了一般的路径复合性质，而不只是算出某个
固定的自然数。

{{include:src/PLFA/Part3/Denotational.idr#addition}}

### 习题 3：任意 Church 数表示路径 {#exercise-3}

一条有 `k` 条边的路径，其 `k + 1` 个顶点按逆序存入向量。构造各条边的并，
再证明 Church `k` 把起点映到终点。必须包括零条边的情况。

**已检查解答：**`pathTable` 构造各条边，`pathStart` 选择向量最后的顶点。
`iterateMeaning` 对路径长度归纳。零条边时，函数体只是变量；增加一条边时，
选择新的一行，再把归纳假设提供的观察作为输入。`pathEnvGrow` 和 `envMono`
使原来的证明可以在扩大后的表中继续使用。最后两次 lambda 引入得到
`churchMeaning`，适用于所有自然数 `k` 以及所有长度为 `k + 1` 的值向量。

{{include:src/PLFA/Part3/Denotational.idr#church-paths}}

## 参考与改编说明 {#references}

本章改编自 Philip Wadler、Wen Kokke、Jeremy G. Siek 的
[PLFA, Denotational](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part3/Denotational.lagda.md)，
冻结版本为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，遵循 CC BY 4.0。
这是独立的 Idris2 改编。模型仍是 PLFA 的有限信息滤子模型；“表”是对值的
直观解释，没有把它换成一个可执行的有限映射模型。

作用域改用 `Nat` 与 `Fin`，环境等式采用逐点形式。成员关系及“所有行都是函数”
改用归纳证据类型，替代上游的函数型谓词；它们的作用和分解定理都得到保留。
上游的加法和一般 Church 路径两道习题，在这里都有已检查参考解答。
所有包含的定义均在 Idris2 0.8.0 的 `%default total` 下通过检查，没有使用
公理或未经验证的类型转换。

# Compositional：由部分的意义构成整体的意义 {#compositional}

## 动机 {#motivation}

如果把一个表达式换成指称相同的另一个表达式，外层程序能观察到变化吗？
有用的指称语义应当回答“不能”：复合表达式的意义，只依赖其直接子表达式
的意义。这一性质称为组合性。

仅仅指出 [Denotational](Denotational.html#judgment) 中有 lambda 和应用规则
还不够。关于 lambda 的推导最后一步可能是 `DJoin` 或 `DSub`，而不是 `DLam`；
关于应用的推导也可能以 `DBot` 结束。要根据外层语法推理，必须先处理所有
这些推导形式。

本章分别证明变量、lambda 抽象和应用的语义方程，再由方程得到同余性、
任意作用域正确的单孔上下文中的替换性质，以及与按语法结构递归定义的
语义之间的等价。

## 模型 {#model}

沿用前章的 `Tm n`、有限信息值、完整的信息预序 `Info`，以及归纳判断
`Denote g m v`。定义中不加入求值器、步数界限或有限的测试项列表。
`DenEq d e` 是对**所有**环境和所有值逐点成立的谓词等价；`SemEq m k`
把这一等价用于两个项的指称。

需要构造两个语义算子。`FunDen` 接受多一个变量的函数体的指称，产生函数
的指称；`AppDen` 接受函数和实参的指称，产生它们应用后的指称。
这两个算子都不检查源程序语法。

### lambda 方程 {#lambda-equation}

`FunDen d g v` 按观察值 `v` 的结构定义：

- 对于 `Bottom`，命题是单元类型：不要求任何信息。
- 对于 `Arrow a b`，命题是 `d (extendEnv g a) b`：当参数提供 `a` 时，
  函数体必须提供 `b`。
- 对于 `Join a b`，两个分量命题都必须成立。

为了处理最后一步为 `DSub` 的情况，先证明 `funDown`：如果一个观察属于
`FunDen (meaning body)`，那么所有更小的观察也属于它。这里归纳的对象是
**信息序推导**，而不是项。在箭头分支，`upEnv` 增加函数体参数的信息，
`DSub` 则减少输出信息。在分配分支，用 `DJoin` 合并两个函数体推导。
传递性分支反向应用两个归纳假设，先从较大的界开始。

正向方程 `lambdaForward` 随后通过对指称推导归纳得到；反向方程
`lambdaBackward` 通过对观察值递归得到。两者合起来就是 `lamEquation`。
把正向方程特化到箭头值，便得到 `lambdaInversion`；即使原推导最后使用
并或信息削弱，这个反演结论仍然成立。

{{include:src/PLFA/Part3/Compositional.idr#lambda-equation}}

### 应用与变量方程 {#application-equation}

应用具有观察 `w`，当且仅当以下两种情况之一成立：`w` 不多于 `Bottom`；
或者存在某个有限输入 `a`，使函数具有观察 `Arrow a w`，实参具有观察 `a`。
这就是 `AppDen` 的定义。

不能去掉底信息分支。所有应用，包括发散的应用，都有 `Bottom` 观察；此时
我们尚未证明其函数部分能够提供箭头。输入的存在量化同样不可省略：同一
表达式的不同使用方式，可能需要不同的有限观察。

`applicationInversion` 证明正向。困难的情况是 `DJoin p q`。两个归纳假设
各自返回底信息分支或实际函数行，因此共有四种组合：

| 第一个观察 | 第二个观察 | 对它们的并所做的构造 |
| --- | --- | --- |
| 不多于底 | 不多于底 | 用 `IJoinL` 合并两个信息序证明。 |
| 不多于底 | 函数行 | 保留该输入，用 `IFun` 加入没有额外内容的输出信息。 |
| 函数行 | 不多于底 | 与上一种情况对称。 |
| 函数行 | 函数行 | 合并两个输入要求和两个函数观察，再用 `mixedDist`。 |

最后一种情况解释了模型为何需要箭头分配规则。若没有它，两行函数表的并
并不能立即变成输出为结果之并的单独一行。在 `DSub` 分支，实际函数行保留
原来的输入，只用 `IFun` 减少输出信息。

`applicationBackward` 用 `DSub DBot` 处理底信息分支，用 `DApp` 处理另一支。
对于变量，`varInv` 检查所有可能的末尾规则，证明观察值不多于环境中该变量
的赋值。这些构造给出了双向的 `appEquation` 和 `varEquation`。

{{include:src/PLFA/Part3/Compositional.idr#application-equation}}

## 推导示例 {#examples}

考虑同一个应用的两个推导：一个使用输入观察 `a`，得到 `b`；另一个使用
输入 `c`，得到 `d`。于是实参具有观察 `Join a c`，函数具有观察
`Join (Arrow a b) (Arrow c d)`。`mixedDist` 把函数观察削弱为
`Arrow (Join a c) (Join b d)`，这样一次 `DApp` 就能得到合并后的结果。
这个构造对四个任意值都适用，没有预先选定一个有界的表集合。

再看 lambda 的例子：先推导出 `Arrow a' b'`，再用
`Info (Arrow a b) (Arrow a' b')` 得到目标行。信息序要求 `Info a' a`
和 `Info b b'`。要恢复输入为 `a` 时的函数体观察，就先把旧输入的信息从
`a'` 增加到 `a`，再把输出从 `b'` 减少到 `b`。这恰好就是 `funDown` 的箭头分支。

对于绑定之下的替换，设 `l`、`r` 都处于作用域 `S n`，并且 `SemEq l r`。
上下文 λ. ([孔] 0) 把它们分别变成 `Lam (App l (Var FZ))` 和
`Lam (App r (Var FZ))`。孔中的项可能引用新绑定的变量，因此只在空环境中
成立的相等并不足够。对每个环境都成立的逐点相等恰好满足需要。
习题 2 给出了这个例子的已检查证明。

## 定理与证明思路 {#theorems}

### 语义相等是同余关系 {#congruence}

`funMap` 按观察值递归，把证据通过 `FunDen` 搬运。它只需要输入指称之间的
正向蕴含；正反各用一次，就得到 `funCong`。

`appMap` 把证据通过 `AppDen` 搬运。底信息分支保持不动；实际函数行分支保留
相同的存在见证输入，分别搬运函数证据和实参证据。正反各用一次，得到
`appDenCong`。

项层面的同余定理由等价的复合得到：先应用语法对应的语义方程，再经过
语义算子搬运，最后反向使用另一个语义方程。因此，`lamCong` 没有暗中
假设 lambda 反演，`appCong` 也同时涵盖了应用的两个位置。

{{include:src/PLFA/Part3/Compositional.idr#congruence}}

### 单孔上下文 {#contexts}

`Ctx m n` 描述一个只有一个孔的项：孔接受作用域为 `m` 的项，填入后得到
作用域为 `n` 的项。`Hole` 不增加外层结构；`CLam` 在上下文外增加绑定，
使最终外部作用域减少一；`CAppLeft`、`CAppRight` 把孔放在应用的任意一侧，
另一侧仍是普通项。

孔的作用域是类型的一部分。如果上下文绑定了孔中项引用的某个变量，这个
变量已经计入 `m`；`plug` 不会暗中创造或重命名它。若要把一个闭项视作处于
更大孔作用域中的项，可以显式使用弱化。这是定理采用的带作用域上下文约定，
并不是没有作用域检查的文本查找替换。

`plug` 对上下文递归；`compositionality` 沿同样的结构证明：遇到绑定，使用
`lamCong`；遇到应用，使用 `appCong`，并对未改变的一侧使用自反性。
准确的定理对所有 `m`、`n`、`l`、`r` 以及 `c : Ctx m n` 都成立，并不局限于
闭项、空上下文或有限的例子列表。

{{include:src/PLFA/Part3/Compositional.idr#contexts}}

当 `n` 为零时，上下文把填入的项封闭起来。后续
[ContextualEquivalence](ContextualEquivalence.html#theorems) 会结合本定理、
可靠性和充分性，证明指称相等的项在每个这样的闭合上下文中具有相同的
终止观察。组合性本身断言的是指称相等，还不是操作行为的观察定理。

### 按结构递归的语义表示 {#structural}

三个语义方程自然给出函数 `structural`：变量使用信息预序，lambda 使用
`FunDen`，应用使用 `AppDen`。`structuralCorrect` 对项归纳，并借助算子
同余定理，证明这一表示与归纳关系逐点等价。

这个函数返回的是**谓词**，不是判定谓词真假的是非答案。应用分支所返回的
谓词仍包含对任意有限信息值的存在量化。因此，从语法到谓词的全函数不等于
终止性判定器；证明变换器通过全性检查，也不意味着所有无类型程序都终止。

{{include:src/PLFA/Part3/Compositional.idr#structural}}

## 常见误区 {#pitfalls}

- 只匹配 `DLam` 或 `DApp`，会遗漏底信息、并和信息削弱的推导。
- 应用结果的并可能要求实参需求的并。猜定一个输入，不能覆盖所有观察。
- `FunDen` 可以接受任意谓词，但 `funDown` 使用了 `meaning body` 特有的
  封闭性质；它没有断言任意谓词都向下封闭。
- 绑定之下的同余性要求在所有相关环境中成立的相等。
- `structural` 计算的是描述意义的命题，并不是无类型 lambda 演算的全求值器。
- 本章没有证明上下文等价的逆命题，也没有把不同语法项变成命题相等。

## 习题与已检查解答 {#exercises}

### 习题 1：合并输出 {#exercise-1}

假设同一个项具有观察 `Arrow a b` 和 `Arrow a c`。推导它具有观察
`Arrow a (Join b c)`，并说明为什么只用 `DJoin` 还没有得到目标。

**已检查解答：**`joinFunctionOutputs` 先用 `DJoin` 构造
`Join (Arrow a b) (Arrow a c)`，再用 `DSub` 和 `IDist`。
信息序规则从目标的单行指向现有的两行之并，这正是 `DSub` 所要求的方向。

### 习题 2：在绑定之下替换 {#exercise-2}

由 `SemEq l r`，其中两项的作用域均为 `S n`，证明 λ. (l 0) 与 λ. (r 0)
的语义相等。显式构造上下文，并解释孔的输入作用域为什么不同于最终项的
作用域。

**已检查解答：**`replaceUnderBinder` 使用
`CLam (CAppLeft Hole (Var FZ))`。孔和内层应用的作用域为 `S n`；
`CLam` 绑定零号索引，得到作用域 `n`。整个相等由 `compositionality` 给出。
`identityContextExample` 另行检查一个简单闭应用上下文的定义行为；它只是
填孔操作的例子，不能代替一般定理。

{{include:src/PLFA/Part3/Compositional.idr#exercises}}

## 参考与改编说明 {#references}

本章改编自 Philip Wadler、Wen Kokke、Jeremy G. Siek 的
[PLFA, Compositional](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part3/Compositional.lagda.md)，
冻结版本为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，遵循 CC BY 4.0。
这一独立的 Idris2 改编保留了语义算子、双向方程、考虑绑定的上下文，以及
关系表示和结构递归表示之间的等价定理。`CLam` 使用一般的孔索引表述，
其参数类型仍然检查最终项的作用域。

证明使用显式函数复合逐点等价，替代上游定制的等式推理语法。所有展示的
代码都来自在 Idris2 0.8.0 中以 `%default total` 检查的模块。新增的两道习题
分别给出了分配规则和绑定之下替换的已检查应用。

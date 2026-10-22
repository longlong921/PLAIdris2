# DeBruijn：让类型错误的项无法表示 {#debruijn}

## 动机 {#motivation}

在 [Properties](Properties.html) 中，原始程序和类型推导是两个对象；
保持定理必须在每步执行后重建推导。另一种办法是把上下文和类型直接作为程序数据类型的索引。
这样，应用构造器只能接收类型匹配的函数与实参，归约起点和终点也必须具有同一个类型索引。

这就是**内在类型化**表示。它并不让所有语义定理都变成自反性：替换仍要正确遍历每个绑定者，
进展仍要找到下一步，求值器仍要处理可能的发散。
改变的是类型保持的检查位置：它成为构造语法操作与归约规则时必须满足的条件。

前面已经介绍 de Bruijn 位置，本章为这些位置加入类型证据。
我们保持相同的类型、上下文向量、按值次序、自然数分支和一般递归，
从而可以直接比较两种表示。

## 模型 {#model}

### 带类型的引用与项 {#intrinsic}

`Ref gamma a` 表示上下文 `gamma` 中一个类型为 `a` 的变量引用。
构造器 `At i` 的类型是 `Ref gamma (index i gamma)`：变量类型由上下文中的位置决定。
`vz` 选择最近变量，`vs` 把已有引用弱化到新绑定者下面。
它们是基于 `Fin` 的派生函数，没有再独立建立另一套编号。

`Term gamma a` 只包含具有指定上下文和类型的项。
从前提阅读 `App`：一个类型为 `Arr a b` 的项和一个类型为 `a` 的项，构成类型为 `b` 的项。
无法把 `Zero` 放在函数位置，因为 `TNat` 不能与函数类型统一。

{{include:src/PLFA/Part2/DeBruijn.idr#intrinsic}}

数据类型索引上的 `0` 是 Idris 的多重性标注：上下文和类型可供检查器使用，却不必保留到运行时。
变量位置和项构造器仍是计算数据。擦除并不允许函数返回索引不符的结果。

这种表示也揭示一个容易忽略的区别：外在恒等函数的两种类型推导，对应两个具有不同类型索引的内在项。
我们没有证明无注释原始恒等函数具有唯一类型。

### 重命名是带类型的映射 {#renaming}

`TRen gamma delta` 必须对所有变量类型成立，不能把类型为 `a` 的变量变成类型为 `b` 的变量。
`extendRen` 保留新引用，对旧引用的像进行弱化；`renameTerm` 随后结构递归地处理每个项构造器。

{{include:src/PLFA/Part2/DeBruijn.idr#renaming}}

进入 λ 时，两侧上下文增加相同的实参类型；进入自然数后继分支时增加 `TNat`；
进入不动点体时增加结果类型。只要带类型映射允许，重命名可以进行弱化、置换或把多个变量映到同一位置，
并不只限于给所有数字索引加一。

### 绑定者下面的替换 {#substitution}

`TSub gamma delta` 将每个变量映到一个具有完全相同类型的项。
`extendSub` 把新引用替换为自身，对所有旧替换项进行弱化。
其中 `renameTerm vs` 是避免捕获的关键步骤。

{{include:src/PLFA/Part2/DeBruijn.idr#substitution}}

`substTerm` 的签名已经表达一般带类型替换命题：任意尊重类型的上下文映射都能变换项，同时保留结果类型。
函数实现给出了该命题的所有构造器分支。
`instantiateTerm` 是单变量特例，同时用于 β 归约和不动点展开；结构替换本身不应要求实参是值。

## 例子 {#examples}

递归加法具有与原始版本相同的绑定布局。后继分支中的 `vs (vs (vs vz))` 选择递归函数。
乘法复用加法。`churchTwo` 具有 `(a → a) → a → a` 这一族简单类型；
这里是 Idris 中以类型为参数的一族项，并没有向对象语言加入多态类型构造器。

{{include:src/PLFA/Part2/DeBruijn.idr#examples}}

可以从内向外阅读 `multiplication`：递归调用接收前驱与不变的第二实参；
加法把其结果与第二实参加起来。于是两个分支都返回 `TNat`，
两个 λ 构成柯里化函数，`Fix` 再把递归引用连接到相同函数类型上。

## 索引已经保证什么，还要证明什么？ {#theorems}

### 进展与归约 {#dynamics}

`Step` 连接具有相同上下文和类型的项。每条 β 规则能够构造，
是因为 `instantiateTerm` 已有正确的类型保持签名。
这是对任意上下文成立的内在保持保证，并不是另写了一个外在定理却省略了证明。

闭项进展仍需要递归证明。函数类型的值只能是 λ，自然数类型的值只能是零或后继。
辅助函数检查这些规范形式。空上下文排除变量引用；开放的良类型变量既不是值，也没有归约规则，
因此不能删去闭合性前提。

{{include:src/PLFA/Part2/DeBruijn.idr#dynamics}}

`Run` 包装实际终点、有限归约序列，以及值证据或燃料耗尽标记。
`run` 消耗燃料，每次检查都使用 `progress`，并没有调用未经检查的一般递归宿主求值器。
同前一章一样，零燃料即使遇到初始值，也会返回耗尽。

### 外在与内在表示的对应 {#correspondence}

`elaborate` 将已有外在类型推导变成内在项。
变量分支用 `indexRef` 包装位置，其他分支把类型构造器换成相应项构造器。
这个函数不是类型推导算法：调用者必须已经持有推导。

{{include:src/PLFA/Part2/DeBruijn.idr#correspondence}}

反方向的 `forget` 去掉内在类型索引，保留原始语法。
`forgetElaborate` 表示：任意类型推导经过内在化，再忘记类型索引，恰好得到原始项。
证明沿推导递归，用归纳假设改写每个直接子项，不只是比较两个挑选出来的例子。

{{include:src/PLFA/Part2/DeBruijn.idr#erasure}}

[Inference](Inference.html#soundness) 将通过算法提供这些外在推导，
并复用这个对应关系，产生可以执行的内在项。

### 已检查的计算 {#computations}

`naturalValue` 从自然数值证据中读出所表示的数。
`runNatural` 只有在执行返回 `Returned` 时才调用它；耗尽仍是 `Nothing`。
参考计算通过实际归约程序和携带证据的求值器，检查 `2 + 2` 与 `3 × 2`。

{{include:src/PLFA/Part2/DeBruijn.idr#computations}}

## 常见误区 {#pitfalls}

- 内在类型化排除类型错误，不排除无限执行。直接返回递归变量的不动点仍可在任意类型表示。
- 索引从当前绑定者向外计数。进入 λ 会改变所有旧变量的位置。
- `substTerm` 必须在每个绑定位置扩展映射，包括后继分支与不动点体，不能只处理 λ。
- `elaborate` 消费证明，并不判定任意原始项是否具有类型。
- 往返定理讨论的是擦除后的原始语法；我们没有把任意类型推导对象视为相等，也没有假设映射的函数外延性。

## 习题与已检查解答 {#exercises}

1. **避免捕获。** 上下文含一个外层自然数变量。在 λy. parameter 中将 parameter 替换成该外层变量，
   证明结果是 λy. outer，而不是 λy. y。
2. **带索引的 β 步骤。** 证明类型化恒等函数应用于二，能进行预期的一步归约。
3. **值是正规形。** 对任意上下文和类型，证明内在值没有任何向外的 `Step`。

{{include:src/PLFA/Part2/DeBruijn.idr#solutions}}

对应解答是 `captureAvoidance`、`identityStep` 和 `valueNormal`。
第一题通过计算 `extendSub` 和弱化来完成，是具体的回归检查。
第三题是一般定理：后继要执行一步，必须由前驱执行一步，这与递归值证据矛盾。
λ 和零则根本没有对应归约规则。

## 参考资料与改编说明 {#references}

独立改编自 Philip Wadler、Wen Kokke 与 Jeremy G. Siek 的
[PLFA，DeBruijn](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/DeBruijn.lagda.md)，
固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) 许可。
上下文采用 `Vect`，引用采用 `Fin` 加类型查找，在保留内在类型化范围的同时，
允许从前面外在判断结构递归地构造对应项。
重命名、替换、闭项进展、递归、按值归约和带燃料求值覆盖本章全部语言。
所有包含的定义均通过 Idris2 0.8.0 检查。

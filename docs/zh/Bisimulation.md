# Bisimulation：证明翻译尊重执行 {#bisimulation}

## 动机 {#motivation}

编译器可以改变语法而不改变行为。考虑把“let x = arg in body”翻译为“(λx. body) arg”。
在我们的弱按值规则下，两边都先求 `arg`，再把其值代入 `body`。
但这种直观解释留下一个关键问题：如果 `body` 或 `arg` 内还有 let，替换之后翻译仍然一致吗？

我们用源项与目标项之间的关系回答：先证明关系在重命名和替换下保持，再从两个方向匹配每次归约。
这里是**一步对应一步**，比允许多个目标步骤匹配一个源步骤的一般模拟概念更强。

同上游一样，本章只研究 [More](More.html) 的变量、λ、应用、let 片段。
外围数据类型还含有其他构造，但下面的关系没有对应分支。
因此定理覆盖这个精确片段中的全部项，而不是所有可能的 `More` 项。

## 模型 {#model}

### 编译关系 {#relation}

`Related s t` 表示 `t` 是 `s` 消除 let 后的翻译，两项具有相同上下文和类型。
变量保持为变量，λ 翻译其主体，应用翻译两侧，let 则变成一个新构造的 λ 应用于绑定表达式。

{{include:src/PLFA/Part2/Bisimulation.idr#relation}}

`RLet` 是唯一改变外部形状的规则。其主体关系在两侧同样增加一个绑定变量类型，
所以不会意外地把对 let 变量的引用翻译成对某个外层变量的引用。

`Fragment s` 记录 `s` 只含这四种构造。它是可执行 `compile` 的结构化定义域，
不是对编译正确性的假设。`compile` 递归返回实际目标，并逐层构造 `Related` 证书。
`relatedFunctional` 证明同一源项的任意两个相关目标相等，λ、应用与 let 分支分别使用归纳假设。

## 例子 {#examples}

源项“let id = (λx. x) in id”翻译成“(λid. id) (λx. x)”。
源项执行 `LetBeta`，目标项执行 `Beta`，两者都得到恒等函数，但初始语法树不同。
这是实际改变语法的翻译实例，并不是换一个名字的恒等模拟。

{{include:src/PLFA/Part2/Bisimulation.idr#examples}}

如果绑定表达式本身还要执行，源项使用 `LetStep`。
翻译后的函数已经是 λ 值，因此目标必须使用 `AppR`，而不是 `AppL`。
这也解释证明为何依赖求值策略：如果目标允许在 λ 体内部归约，就会出现需要另外处理的目标步骤。

## 模拟证明 {#theorems}

### 与值、重命名和替换相容 {#compatibility}

本片段的值只能是 λ，`valueForward` 和 `valueBackward` 从两个方向搬运这个事实。
翻译后的 let 是应用，所以即使其绑定表达式已经是值，它本身也不是值。

重命名与关系按结构相容。进入 λ 或 let 体时，`renameRelated` 扩展映射。
随后，`extendRelated` 的旧变量分支使用这个结论，把替换项弱化到新绑定者下面。

{{include:src/PLFA/Part2/Bisimulation.idr#compatibility}}

`substRelated` 接收**两个**替换映射，分别作用于源项和目标项；
前提要求它们对每个变量的像都相关，结论则是对任意相关项替换后仍相关。
变量分支使用前提，绑定分支扩展前提，应用分支递归处理两侧。
let 分支的目标仍是 λ 应用，其主体使用相应的扩展替换。

`instRelated` 将这个定理特化为替换一个变量。
前提是两个主体相关、两个实参相关，结论是替换结果相关。
这就是 β 规则所需的桥梁；要求原主体彼此相等会过强，而且通常不成立。

### 正向模拟 {#forward}

正向命题补齐下列方形的下边和右边：

| | 执行前 | 执行后 |
| --- | --- | --- |
| 源项 | s | u，具有 `Step s u` |
| 目标项 | t，具有 `Related s t` | 某个 v，具有 `Step t v` 和 `Related u v` |

`ForwardLeg` 正好包装两个缺失部分。它的构造器不假设定理已经成立：
`forward` 的实现必须对每条源规则实际构造结果关系和目标归约。

{{include:src/PLFA/Part2/Bisimulation.idr#forward}}

应用上下文步骤使用归纳假设，再重建 `AppL` 或 `AppR`；后者还需搬运函数的值证明。
β 步骤使用 `instRelated` 和翻译后实参的值证明。
let 上下文步骤变成 `AppR VLam`，let 的 β 步骤变成普通 β 步骤。
变量和 λ 值则没有归约分支。

### 反向模拟 {#backward}

只有正向模拟还不能排除目标的额外行为。`backward` 从目标步骤出发，产生匹配的源步骤，
并证明结果仍相关。在翻译后的 let 上，目标不可能走 `AppL`，因为其函数是 λ。
目标 `AppR` 对应源 `LetStep`，目标 β 对应源 `LetBeta`。

{{include:src/PLFA/Part2/Bisimulation.idr#backward}}

这个语法关系本身不必对称：let 与其展开相关，但关系语法没有加入反过来的那一对。
称它为双模拟，是因为在每一对相关项之间，**任意一侧的步骤都能由另一侧匹配**。
这不同于由 `Related s t` 推出 `Related t s`。

### 有限执行与编译器的图像 {#traces}

`forwardMany` 和 `backwardMany` 沿有限轨迹迭代对应的单步证明。
空轨迹保留初始关系；非空轨迹先匹配第一步，再对尾部递归。
每个匹配步骤都保留在返回轨迹中，不假设正规化，也不限制轨迹长度。

{{include:src/PLFA/Part2/Bisimulation.idr#traces}}

最后，`compiledMatches` 证明 `compile` 返回的目标与任何由 `Related` 认证的目标相等。
它打开编译器产生的证书并使用 `relatedFunctional`。
结合下方的 `relatedFragment`，这精确说明关系为何描述该编译器在其定义域上的图像。

{{include:src/PLFA/Part2/Bisimulation.idr#graph}}

## 常见误区 {#pitfalls}

- 描述翻译的关系不会自动成为模拟关系；逐步匹配函数是另外的证明义务。
- 源 let 步骤对应应用步骤，若要求两侧使用相同名字的构造器，就错过了真正的论证。
- 替换相容要求替换项相关，而不是要求两个替换映射相同；目标替换项可能已经展开其中的 let。
- 双模拟要求两个方向匹配行为，并不要求编译关系本身对称。
- 定理范围由关系语法决定；本证明没有悄悄涵盖 `More` 中的字面量、不动点、积、和与列表。
- 有限归约的匹配本身不是对外围语言所有特性成立的上下文等价定理。

## 习题与已检查解答 {#exercises}

1. **编译嵌套 let。** 为主体含另一个 let 的程序提供 `Fragment` 证书，再取得目标与关系证书。
2. **使用反向模拟。** 把已编译恒等示例的 β 步骤搬回源 let 步骤。
3. **恢复定义域。** 证明任意 `Related s t` 证书都产生 `Fragment s` 证书，并说明为什么不必检查任意 `More` 项。

{{include:src/PLFA/Part2/Bisimulation.idr#solutions}}

对应解答为 `nestedCompilation`、`reverseExample` 和 `relatedFragment`。
第一题调用编译器，而不是手工假定其结果。
第三题沿翻译证书递归；它的构造器恰好包含源片段所需的全部证据。

## 参考资料与改编说明 {#references}

独立改编自 Philip Wadler、Wen Kokke 与 Jeremy G. Siek 的
[PLFA，Bisimulation](https://github.com/plfa/plfa.github.io/blob/1c39b1e82caa4283274e64ba58c3bc3c9ab781eb/src/plfa/part2/Bisimulation.lagda.md)，
固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`，采用
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) 许可。
保留上游的 λ/let 片段与正向模拟，完整实现上游作为习题提出的反向模拟，
并补充两个方向的有限轨迹和可执行认证翻译。
没有把积编码习题描述成已经证明的一般等价定理。
所有包含的定义和解答均通过 Idris2 0.8.0 检查。

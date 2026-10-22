# Negation：反证与经典推理的边界 {#negation}

## 为什么需要否定 {#motivation}

反驳一个命题，就是说明任何声称证明它的证据都会导致不可能。这对数学和程序都有用：失败的判定程序应当解释，为什么成功的见证不可能存在。构造性否定把这种解释记录成一个通向空类型的函数。

## 定义模型 {#model}

{{include:src/PLFA/Part1/Negation.idr#constructive}}

`Refutes a` 简写 `a -> Void`。使用这个名字，是因为 Idris 已经把 `Neg` 用于数值取负。`notElim` 把反证与见证结合，得到 `Void`，再消去它。双重否定引入是构造性的：给定 `x : a`，任意 `a` 的反证应用到 `x`，都会产生矛盾。

三重否定消去同样是构造性的。给定双重否定的反证以及候选 `x : a`，先用 `x` 构造双重否定证据，再交给原来的反证。逆否通过预先组合函数实现：若有 `f : a -> b` 且 `b` 不可能，则任意 `a` 都会产生不可能的 `b`。

## 具体反证 {#examples}

`oneNotTwo` 与 `zeroNotSucc` 检查假设的相等证据。唯一的相等构造子会迫使不相容的自然数构造子相同，所以 Idris 接受标记为 `impossible` 的情形。这是经过检查的构造子排除，不是未完成的实现，也不是异常。

`notSum` 把和的反证拆成两个分支各自的反证，并通过分类讨论把它们合起来。例如，假设得到 `Left x`，就使用第一份反证。这个记录是 `Iff`；其逐点恢复来自这样一个事实：任何输入的和本身都会与反证冲突。

`negationsPointwise` 说明两个反证在每个可能输入上相等，因为这样的输入会产生 `Void`。它并没有证明两个完整函数命题相等。上游的“assimilation”定理用外延性得到更强结论，本改编不作这个假设。

## 互斥三歧性 {#strict-order}

{{include:src/PLFA/Part1/Negation.idr#strict-order}}

Relations 章给出了小于、相等或大于的证据。`ExclusiveTri` 还会反驳另外两种可能。如果 `m < n` 且 `m = n`，替换后得到 `m < m`，与非自反性矛盾。如果 `m < n` 且 `n < m`，把传递性与非严格界结合，也会得到 `m < m`。因此 `exclusiveTrichotomy` 为任意两个自然数提供恰好一个相容的顺序情形。

## 构造性与经典原则 {#theorems}

排中律声称每个命题都带有见证或反证。构造性地理解，这需要为每个类型提供判定程序，而我们没有给出这样的程序。但它的双重否定可以证明。如果 `reject` 反驳两个选择，那么任意 `x` 都会使 `reject (Left x)` 产生矛盾；这就定义了左命题的反证。把它作为右分支交给 `reject`，矛盾完成。这是 `excludedMiddleIrrefutable`，不是排中律本身。

{{include:src/PLFA/Part1/Negation.idr#classical}}

五个具名类型分别描述排中律、双重否定消去、皮尔士律、用析取表示蕴涵以及经典德摩根原则。这个区域的每条定理都显式接收一个原则，再构造另一个。这里没有无条件提供任何一个原则类型的居民。

排中律通过检查选择推出双重否定消去：有见证就返回，有反证就推出矛盾。反过来，将双重否定消去应用于不可反驳性定理，就得到排中律。排中律也能通过分类讨论推出皮尔士律、蕴涵析取式和德摩根原则。它们各自都有返回路线：皮尔士律推出双重否定消去；将蕴涵析取式用于恒等函数，得到反证或见证；德摩根原则则在 `a` 与它的否定上实例化。因此，通过排中律可以连接五者，证明它们互相蕴涵，却没有声称已经直接证明其中任何一个。

## 稳定命题 {#stability}

{{include:src/PLFA/Part1/Negation.idr#stability}}

`Stable a` 表示对于这个特定的 `a`，可以消去双重否定。否定由三重否定消去而稳定。如果两个命题都稳定，它们的合取也稳定：从对的双重否定分别推出每个分量的双重否定，应用对应的稳定性函数，再构造对。局部的稳定性定理弱于对所有类型统一成立的经典原则。

## 容易混淆的地方 {#pitfalls}

没有找到见证，不等于给出反证。反证必须处理**任意**候选见证。双重否定引入不能授权使用反方向。“排中律不可反驳”不是“排中律已经证明”。最后，即使函数体无需其他义务就能编译，接收经典原则作为参数的定理仍然是条件性定理。

## 习题与已检查解答 {#exercises}

1. **G.1 — 否定。** 推导逆否并消去三重否定。参考 `contraposition`、`tripleNegElim`。
2. **G.2 — 互斥顺序。** 证明严格顺序排除相等及反向严格顺序，再加强三歧性。参考 `ltNotEqual`、`ltAsymmetric`、`exclusiveTrichotomy`。
3. **G.3 — 和的德摩根律。** 构造“和的反证”与“一对反证”之间的双向蕴涵。参考 `notSum`。
4. **G.4 — 经典等价。** 通过排中律连接五个原则。参考 `emToDne`、`dneToEm`、`emToPeirce`、`peirceToEm`、`emToImplication`、`implicationToEm`、`emToDeMorgan`、`deMorganToEm`。
5. **G.5 — 稳定性。** 证明否定稳定，并证明稳定性对积封闭。参考 `negationStable`、`productStable`。

## 参考与改编说明 {#references}

改编自 [PLFA Negation](https://plfa.github.io/Negation/)，CC BY 4.0，作者 Philip Wadler、Wen Kokke、Jeremy G. Siek；上游固定提交为 `1c39b1e82caa4283274e64ba58c3bc3c9ab781eb`。经典原则始终是蕴涵定理的显式假设。任意否定函数的相等，以及相应的外延同构，改用逻辑等价和逐点相等，不加入外延性公理。

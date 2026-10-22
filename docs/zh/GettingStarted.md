# Getting Started · 开始使用

阅读站只需要浏览器。要复现检查或动手编写代码，请使用仓库的 Nix 环境。`flake.lock` 固定软件包集合，`flake.nix` 从中选择 Idris2、带 Markdown 的 Python、Node 和 Make。

## 准备工作目录 {#setup}

按 [Nix 官方安装指南](https://nix.dev/install-nix)安装，并在需要时启用 `nix-command` 与 `flakes` 实验特性。flake 提供 Linux、macOS 的 x86-64 与 AArch64 输出。交付时记录的全量验收在 x86-64 Linux 上执行；提供其他平台输出不等于已经逐一验证。Windows 用户可以使用 WSL2 等 Linux 环境。

```sh
git clone https://github.com/longlong921/PLAIdris2.git
cd PLAIdris2
nix develop
idris2 --version
```

预期编译器版本是 `0.8.0`。首次运行可能下载依赖，之后会重复使用。不要为了使教程例子通过而随意更新锁文件，那会改变要复现的环境；先在记录的工具链下诊断错误。

## 一条命令完成全量检查 {#check}

在仓库目录运行下列命令，检查原章节顺序、双语节与源码引用、参考源码约束、Idris 模块、可执行例子、预期失败、站点构建、本地链接和语言切换行为：

```sh
nix develop --command python3 tools/check.py
```

失败时会返回非零退出码。详细输出与机器可读摘要写入 `build/checks/`。交付时的历史证据保存在 `evidence/`；那些文件记录某次运行，而新执行的命令检查你当前的源码。双语语义一致性还需要编辑审查：节标识相同不能证明两个句子意思相同。

只检查一章及它引用的源码模块，可以运行：

```sh
nix develop --command python3 tools/check.py --chapter Naturals
```

使用准确的章节 ID，例如 `DeBruijn`、`BigStep` 或 `ContextualEquivalence`。Idris 会检查导入的依赖。按章检查不能代替全站和运行例子套件。若要隔离、不可变的构建，可执行 `nix build`；只有全量检查成功后，`result/` 才会包含站点。`nix flake check` 为当前系统运行同一构建。

## 本地阅读 {#preview}

```sh
nix develop --command python3 tools/build.py
nix develop --command python3 -m http.server 8000 --bind 127.0.0.1 --directory dist
```

打开 `http://127.0.0.1:8000/`，选择中文或英文。语言按钮保留章节与锚点。链接采用相对路径，因此输出也可以放在仓库名称这样的子路径下。按 Ctrl-C 停止预览。构建或预览不会部署站点，也不会更改 GitHub Pages 设置。

## 第一次修改 {#edit}

打开 `src/PLFA/Part1/Naturals.idr` 及对应的两份 Markdown。正文通过引用指令插入源码区域；生成的代码块就是源码的一个视图。修改源码定义，运行按章检查，再重建站点。不要手动修改 `dist/`。

交互使用时，先进入 `nix develop`，再运行 `idris2 --source-dir src src/PLFA/Part1/Naturals.idr`。`:t name` 查询类型，`:r` 重载，`:q` 退出。习题尝试可以写在自己的草稿文件里。含有未完成洞的实验文件应放在 `src/` 之外，因为 `src/` 表示完整参考实现。

## 出错时如何处理 {#troubleshooting}

找不到导入模块，通常是没有在仓库根目录运行，或遗漏 `--source-dir src`。名字不可访问可能与擦除参数有关，改注解前先查阅 [QTT](QTT.md)。总性失败要求你展示递归参数变小或覆盖完整分支的理由，不是插入信任逃逸的理由。只有编译器给出预期种类的错误，拒绝错误证明才算负向测试成功。

本工程共享一个 `build/` 目录，另用一个小目录存放被拒绝的例子，不会为每章复制整套编译环境。检查中断后重新运行即可；不要把尚未写完的日志当作通过证据。

# Getting Started

The reading site needs only a browser. To reproduce the checks or work through the code, use the repository's Nix environment. `flake.lock` fixes the package collection; `flake.nix` selects Idris2, Python with Markdown, Node and Make from it.

## Prepare the checkout {#setup}

Install Nix using the [official installation guide](https://nix.dev/install-nix), then enable the `nix-command` and `flakes` experimental features if your installation requires it. The supported flake outputs cover Linux and macOS on x86-64 and AArch64. The recorded full acceptance run is on x86-64 Linux; the existence of other outputs is not a claim that they were all tested. On Windows use a Linux environment such as WSL2.

```sh
git clone https://github.com/longlong921/PLAIdris2.git
cd PLAIdris2
nix develop
idris2 --version
```

The expected compiler version is `0.8.0`. The first invocation may fetch packages; subsequent checks reuse them. Do not update the lock file just to make a tutorial example pass: that changes the environment being reproduced. Diagnose an error against the recorded toolchain first.

## One complete check {#check}

From the checkout, this single command checks the ordered chapter mapping, paired sections and source inclusions, reference-source policy, Idris modules, executable examples, expected failures, site build, local links and language-switch behavior:

```sh
nix develop --command python3 tools/check.py
```

It exits nonzero on failure. Detailed output and a machine-readable summary are written to `build/checks/`. Historical delivery evidence lives in `evidence/`; those files record a particular run, while a new check tests your current tree. Bilingual semantic agreement also needs editorial review: comparing section IDs cannot prove that two sentences mean the same thing.

To check one chapter and the source modules it includes:

```sh
nix develop --command python3 tools/check.py --chapter Naturals
```

Use the exact chapter ID, for example `DeBruijn`, `BigStep` or `ContextualEquivalence`. Imported dependencies are checked by Idris. A chapter check does not replace the whole-site and executable suite. For an isolated immutable build, run `nix build`; the resulting `result/` contains the site only after the full checks succeed. `nix flake check` runs the same derivation for the current system.

## Read locally {#preview}

```sh
nix develop --command python3 tools/build.py
nix develop --command python3 -m http.server 8000 --bind 127.0.0.1 --directory dist
```

Open `http://127.0.0.1:8000/`, then choose English or Chinese. The language button preserves the chapter and fragment. Links are relative, so the output also works under a repository subpath. Stop the preview with Ctrl-C. Building or serving does not deploy anything or change GitHub Pages settings.

## Your first edit {#edit}

Open `src/PLFA/Part1/Naturals.idr` and its paired Markdown chapters. Text includes source regions using an include directive; the generated code block is a view of the source. Edit the source definition, run the chapter check, then rebuild the site. Do not edit `dist/` by hand.

For interactive work, enter `nix develop`, then load the source with `idris2 --source-dir src src/PLFA/Part1/Naturals.idr`. `:t name` asks for a type, `:r` reloads, and `:q` exits. Write exercises in your own scratch file. An experimental file containing holes should remain outside `src/`, whose contents are the complete reference implementation.

## When something fails {#troubleshooting}

A missing import usually means the command was run outside the checkout or without `--source-dir src`. An inaccessible name may be an erased parameter; consult [QTT](QTT.md) before changing annotations. A totality failure asks you to make the recursive decrease or case coverage visible; it is not a reason to insert a trust escape. A rejected false proof is a successful negative test only when the compiler reports the expected kind of error.

The project uses one shared `build/` directory, with a small separate directory for rejected examples. It does not create a fresh copy of the entire compiler environment for every chapter. If a check is interrupted, rerun it; do not interpret a partially written log as a pass.

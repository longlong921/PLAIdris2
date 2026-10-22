#!/usr/bin/env python3
"""Build the book from paired Markdown and the checked Idris sources.

No network access or frontend build system is needed. Includes are expanded
from the source tree, never from a hand-maintained copy of a code fragment.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import shutil

import markdown

ROOT = Path(__file__).resolve().parents[1]
INCLUDE = re.compile(r"^\{\{include:([^}\s]+)\}\}\s*$", re.MULTILINE)
GROUPS = {
    "front": ("Front matter", "前言部分"),
    "part1": ("Part 1 · Logical Foundations", "第 1 部分 · 逻辑基础"),
    "part2": ("Part 2 · Programming Language Foundations", "第 2 部分 · 程序语言基础"),
    "part3": ("Part 3 · Denotational Semantics", "第 3 部分 · 指称语义"),
    "appendix": ("Appendix", "附录"),
    "back": ("Back matter", "后记部分"),
    "extensions": ("Idris2 extensions · separate reading", "Idris2 扩展 · 独立阅读区"),
}


def chapters():
    return json.loads((ROOT / "book/chapters.json").read_text())


def extensions():
    return json.loads((ROOT / "book/extensions.json").read_text())


def read_include(spec: str):
    file, _, region = spec.partition("#")
    path = (ROOT / file).resolve()
    if not path.is_relative_to(ROOT / "src") or path.suffix != ".idr":
        raise ValueError(f"Include must name an Idris reference source: {spec}")
    lines = path.read_text().splitlines()
    start, end = 0, len(lines)
    if region:
        starts = [i for i, line in enumerate(lines) if line.strip() == f"-- region {region}"]
        ends = [i for i, line in enumerate(lines) if line.strip() == f"-- endregion {region}"]
        if len(starts) != 1 or len(ends) != 1 or starts[0] >= ends[0]:
            raise ValueError(f"Missing, duplicated or reversed region: {spec}")
        start, end = starts[0] + 1, ends[0]
    code = "\n".join(line for line in lines[start:end]
                     if not re.match(r"\s*-- (?:end)?region ", line)) + "\n"
    return code, {"spec": spec, "source": file, "start_line": start + 1,
                  "end_line": end, "sha256": hashlib.sha256(code.encode()).hexdigest()}


def expand_includes(text: str, lang: str):
    snippets = []

    def include(match):
        spec = match.group(1)
        code, record = read_include(spec)
        snippets.append(record)
        label = "Source" if lang == "en" else "源码"
        caption = (f'<div class="code-caption"><a href="../source/{record["source"]}">'
                   f'{label} · {html.escape(spec)}</a>'
                   f'<span>L{record["start_line"]}–{record["end_line"]}</span></div>')
        return ("\n" + caption + '\n<pre class="source"><code class="language-idris">'
                + html.escape(code) + "</code></pre>\n")

    return INCLUDE.sub(include, text), snippets


def title(row, lang):
    text = (ROOT / row[lang]).read_text()
    match = re.search(r"^# (.+)", text, re.MULTILINE)
    if not match:
        raise ValueError(f"Missing chapter title: {row[lang]}")
    return re.sub(r"\s*\{#[^}]+\}", "", match.group(1)).strip()


def toc(rows, lang, current=None):
    sections = []
    for group, names in GROUPS.items():
        entries = [r for r in rows if r["group"] == group]
        if not entries:
            continue
        items = []
        for row in entries:
            state = ' aria-current="page"' if row["id"] == current else ""
            items.append(f'<li data-chapter="{row["id"]}"><a href="{row["id"]}.html"{state}>'
                         f'{html.escape(title(row, lang))}</a></li>')
        sections.append(f'<section class="nav-group"><h2>{names[lang == "zh"]}</h2>'
                        f'<ol>{"".join(items)}</ol></section>')
    return "\n".join(sections)


def document(lang, page_id, page_title, body, navigation, local_toc="", prev_next=""):
    other = "zh" if lang == "en" else "en"
    labels = {
        "en": ("Skip to content", "Contents", "On this page", "中文", "Filter chapters", "Search chapters",
               "An independent Idris2 adaptation of PLFA. Text and code: CC BY 4.0.",
               "Philip Wadler, Wen Kokke and Jeremy G. Siek · upstream authors"),
        "zh": ("跳到正文", "全书目录", "本章目录", "English", "筛选章节", "搜索章节",
               "独立的 PLFA Idris2 改编版。正文与代码采用 CC BY 4.0。",
               "Philip Wadler、Wen Kokke、Jeremy G. Siek · 上游作者"),
    }[lang]
    return f'''<!doctype html>
<html lang="{'zh-Hans' if lang == 'zh' else 'en'}">
<head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="description" content="Programming Language Foundations in Idris2 — a bilingual, source-linked textbook">
<title>{html.escape(page_title)} · PLF Idris2</title>
<link rel="stylesheet" href="../assets/book.css">
<link rel="alternate" hreflang="{other}" href="../{other}/{page_id}.html">
<script src="../assets/book.js" defer></script></head>
<body data-chapter="{page_id}">
<a class="skip" href="#main">{labels[0]}</a>
<header class="topbar"><a class="brand" href="index.html"><span class="brand-symbol">λ</span> PLF <b>Idris2</b></a>
<span class="book-tag">Programming Language Foundations</span>
<a id="language-switch" href="../{other}/{page_id}.html" lang="{other}" hreflang="{other}">{labels[3]} <span aria-hidden="true">⇄</span></a></header>
<div class="layout"><aside class="sidebar"><button id="nav-toggle" aria-expanded="false" aria-controls="chapter-nav">{labels[1]} <span aria-hidden="true">☰</span></button>
<nav id="chapter-nav" aria-label="{labels[1]}"><a class="contents-home" href="index.html">{labels[1]}</a>
<label class="sr-only" for="chapter-search">{labels[5]}</label><input type="search" id="chapter-search" placeholder="{labels[4]}" autocomplete="off">
{navigation}</nav></aside>
<main id="main" tabindex="-1"><article>{body}</article>{prev_next}
<footer><p>{labels[6]} <a href="../LICENSE">CC BY 4.0</a> · <a href="../NOTICE">{'Adaptation notice' if lang == 'en' else '改编说明'}</a></p><p>{labels[7]} · <a href="https://plfa.github.io/">PLFA</a> · <a href="https://github.com/longlong921/PLAIdris2">GitHub</a></p></footer></main>
<aside class="page-toc"><h2>{labels[2]}</h2>{local_toc}<a class="to-top" href="#main">↑ {'Top' if lang == 'en' else '回到顶部'}</a></aside></div>
</body></html>'''


def build(out: Path | None = None):
    out = out or ROOT / "dist"
    out.mkdir(parents=True, exist_ok=True)
    rows, extra = chapters(), extensions()
    all_rows = rows + extra
    snippets = {}
    for lang in ("en", "zh"):
        (out / lang).mkdir(exist_ok=True)
        for row in all_rows:
            path = ROOT / row[lang]
            source = path.read_text()
            expanded, records = expand_includes(source, lang)
            md = markdown.Markdown(extensions=["extra", "toc", "sane_lists"],
                                   extension_configs={"toc": {"toc_depth": "2-3"}})
            body = md.convert(expanded)
            # H1 is an identical fragment in both languages; subsection IDs are
            # explicit in the Markdown and checked for semantic correspondence.
            body = re.sub(r"<h1(?: [^>]*)?>", '<h1 id="chapter-title">', body, count=1)
            body = re.sub(r'href="([^"#?:]+)\.md(#[^"]*)?"',
                          lambda m: f'href="{m[1]}.html{m[2] or ""}"', body)
            chain = extra if row in extra else rows
            position = chain.index(row)
            links = []
            if position:
                prev = chain[position - 1]
                links.append(f'<a rel="prev" href="{prev["id"]}.html">← {html.escape(title(prev, lang))}</a>')
            if position + 1 < len(chain):
                nxt = chain[position + 1]
                links.append(f'<a rel="next" href="{nxt["id"]}.html">{html.escape(title(nxt, lang))} →</a>')
            pn = '<nav class="chapter-pager" aria-label="Chapters">' + "".join(links) + "</nav>"
            result = document(lang, row["id"], title(row, lang), body,
                              toc(all_rows, lang, row["id"]), md.toc, pn)
            (out / lang / f'{row["id"]}.html').write_text(result)
            snippets[f'{lang}/{row["id"]}'] = records
        intro = {
            "en": ('A small step.<br>A precise reason.', 'Programming Language Foundations in Idris2',
                   'Learn to state what a program means, explain why a proof works, and ask the compiler to check the details. Follow the original PLFA chapter order, with English and Chinese side by side.',
                   'Start reading', 'Idris2 extensions are collected separately below the original table of contents.'),
            "zh": ('每一小步，<br>都有理由。', 'Idris2 程序语言基础',
                   '把“程序是什么意思”写成定义，把“为什么成立”写成证明，再让编译器检查细节。沿着 PLFA 的原章节顺序阅读，随时切换到同章英文。',
                   '开始阅读', 'Idris2 专属扩展独立列于原目录之后。'),
        }[lang]
        body = (f'<div class="hero"><p class="eyebrow">PLFA → IDRIS2 · EN / 中文</p><h1>{intro[0]}</h1>'
                f'<p class="hero-subtitle">{intro[1]}</p><p>{intro[2]}</p>'
                f'<a class="start" href="Dedication.html">{intro[3]} →</a></div>'
                f'<h2 id="contents">{"Contents" if lang == "en" else "全书目录"}</h2>'
                f'<p>{intro[4]}</p><div class="full-toc">{toc(all_rows, lang)}</div>')
        (out / lang / "index.html").write_text(document(lang, "index", intro[1], body, toc(all_rows, lang)))
    shutil.copytree(ROOT / "site", out / "assets", dirs_exist_ok=True)
    shutil.copytree(ROOT / "src", out / "source/src", dirs_exist_ok=True)
    shutil.copy(ROOT / "LICENSE", out / "LICENSE")
    shutil.copy(ROOT / "NOTICE", out / "NOTICE")
    (out / "snippets.json").write_text(json.dumps(snippets, ensure_ascii=False, indent=2) + "\n")
    (out / "index.html").write_text('''<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>PLF Idris2 · English / 中文</title>
<link rel="stylesheet" href="assets/book.css"></head><body class="language-home"><main>
<span class="brand-symbol">λ</span><h1>Programming Language<br>Foundations in Idris2</h1>
<p>Precise programs. Understandable proofs.<br>清晰的程序，可理解的证明。</p>
<p class="language-choices"><a href="en/index.html" lang="en">Read in English →</a>
<a href="zh/index.html" lang="zh-Hans">阅读中文版 →</a></p>
<p class="muted">An independent adaptation of PLFA · 独立改编版 · CC BY 4.0</p></main></body></html>''')
    print(f"Built {2 * (len(all_rows) + 1) + 1} HTML pages from {len(all_rows)} paired chapters in {out}")
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    build(parser.parse_args().out)

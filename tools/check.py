#!/usr/bin/env python3
"""One command for mapping, bilingual structure, Idris, runtime and site checks."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from html import unescape
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

from build import ROOT, INCLUDE, build, chapters, extensions, read_include

EXPECTED = {
    "front": "Dedication Preface GettingStarted".split(),
    "part1": "Naturals Induction Relations Equality Isomorphism Connectives Negation Quantifiers Decidable Lists".split(),
    "part2": "Lambda Properties DeBruijn More Bisimulation Inference Untyped Confluence BigStep".split(),
    "part3": "Denotational Compositional Soundness Adequacy ContextualEquivalence".split(),
    "appendix": ["Substitution"],
    "back": ["Acknowledgements", "Fonts"],
}
CORE = {"motivation", "model", "examples", "theorems", "pitfalls", "exercises", "references"}
ESCAPES = re.compile(r"\b(?:believe_me|assert_total|assert_smaller|idris_crash|prim__crash|unsafePerformIO|partial|covering|postulate)\b|\?[A-Za-z_]|%(?:unsafe|extern|foreign|builtin)\b")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def mapping():
    rows = chapters()
    require([(r["group"], r["id"]) for r in rows] ==
            [(g, ch) for g, names in EXPECTED.items() for ch in names],
            "The original PLFA order or membership changed")
    frozen_paths = re.findall(r"^  - include: (.+)$", (ROOT / "book/upstream-toc.yml").read_text(), re.M)
    require(frozen_paths == [r["upstream_path"] for r in rows], "Mapping disagrees with frozen upstream TOC")
    frozen = json.loads((ROOT / "book/upstream.json").read_text())
    require(re.fullmatch(r"[0-9a-f]{40}", frozen["commit"]), "Upstream commit is not frozen")
    require(all(re.fullmatch(r"[0-9a-f]{64}", r["upstream_sha256"]) for r in rows), "Missing upstream source hashes")
    require(set(r["id"] for r in rows).isdisjoint(r["id"] for r in extensions()), "Extensions overlap original chapters")
    print("PASS exact 30-entry upstream mapping; extensions remain separate")


def content(rows):
    included = set()
    for row in rows:
        texts = [(ROOT / row[lang]).read_text() for lang in ("en", "zh")]
        anchors = [re.findall(r"\{#([\w-]+)\}", text) for text in texts]
        require(anchors[0] == anchors[1], f'{row["id"]}: bilingual section IDs differ')
        require(len(anchors[0]) == len(set(anchors[0])), f'{row["id"]}: duplicate section ID')
        if row["group"] not in ("front", "back"):
            require(CORE <= set(anchors[0]), f'{row["id"]}: missing pedagogical sections {CORE - set(anchors[0])}')
        specs = [INCLUDE.findall(t) for t in texts]
        require(specs[0] == specs[1], f'{row["id"]}: translations include different reference definitions')
        for lang, text in zip(("en", "zh"), texts):
            require(not re.search(r"^```(?:idris|idr|idris2)\b", text, re.M),
                    f'{row["id"]}/{lang}: copyable Idris code must be included from checked sources')
            require(not re.search(r"\b(?:TODO|TBD|FIXME)\b|待补充|尚待撰写", text), f'{row["id"]}/{lang}: placeholder text')
        for spec in specs[0]:
            _, record = read_include(spec)
            included.add(record["source"])
        if row["group"] not in ("front", "back"):
            require(specs[0], f'{row["id"]}: no reference implementation included')
            review_path = ROOT / f'book/review-{row["id"]}.json'
            review = json.loads(review_path.read_text())
            require(review["chapter"] == row["id"], f"Wrong chapter in {review_path}")
            require(review.get("core_claims") and len(review.get("exercises", [])) >= 2,
                    f'{row["id"]}: missing theorem/exercise review metadata')
            for source in review["sources"]:
                require((ROOT / source).is_file(), f"Missing review source: {source}")
    print(f"PASS paired sections and source inclusions for {len(rows)} chapters")
    return included


def audit_sources(paths):
    for path in paths:
        source = path.read_text()
        # This deliberately errs on the strict side. Examples discussing unsafe
        # features belong in prose, never in the reference build.
        code = re.sub(r"\{-.*?-\}", "", source, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        require("%default total" in code, f"Missing total default: {path.relative_to(ROOT)}")
        found = ESCAPES.search(code)
        require(not found, f"Forbidden proof escape or hole in {path.relative_to(ROOT)}: {found[0] if found else ''}")
    print(f"PASS no proof holes or escape hatches in {len(paths)} reference modules")


def run(command, log, expect_failure=False, pattern=None, env=None):
    print("RUN " + " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, timeout=600, env=env)
    log.write_text("$ " + " ".join(command) + "\n" + result.stdout + f"\nexit_code={result.returncode}\n")
    if expect_failure:
        require(result.returncode != 0, f"Invalid proof unexpectedly accepted: {command[-1]}")
        require(pattern and re.search(pattern, result.stdout, re.I),
                f"Negative test failed for the wrong reason: {log}; output:\n{result.stdout}")
    else:
        require(result.returncode == 0 and not re.search(r"^Error:", result.stdout, re.M),
                f"Command failed; see {log}\n{result.stdout[-6000:]}")
    return result.stdout


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.assets, self.headings = [], [], [], []
        self.language, self.switch, self.active = None, None, []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "id" in a:
            self.ids.append(a["id"])
        if tag == "html":
            self.language = a.get("lang")
        if tag in ("h2", "h3") and "id" in a:
            self.headings.append(a["id"])
        if tag in ("a", "link") and "href" in a:
            self.links.append(a["href"])
        if "src" in a:
            self.assets.append(a["src"])
        if a.get("id") == "language-switch":
            self.switch = a.get("href")
        if a.get("aria-current") == "page":
            self.active.append(a.get("href"))


def site_check(out):
    pages = {p.resolve(): Page(p.read_text()) for p in out.rglob("*.html")}
    count = 0
    for path, page in pages.items():
        duplicates = [key for key, n in Counter(page.ids).items() if n > 1]
        require(not duplicates, f"Duplicate HTML IDs in {path}: {duplicates}")
        for link in page.links + page.assets:
            parts = urlsplit(link)
            if parts.scheme or parts.netloc:
                continue
            target = (path.parent / unquote(parts.path)).resolve() if parts.path else path
            require(target.is_relative_to(out.resolve()), f"Link escapes build: {path}: {link}")
            if target.is_dir():
                target /= "index.html"
            require(target.exists(), f"Broken local link: {path.relative_to(out)} -> {link}")
            if parts.fragment and target in pages:
                require(unquote(parts.fragment) in pages[target].ids,
                        f"Broken fragment: {path.relative_to(out)} -> {link}")
            count += 1
        if page.switch:
            target = (path.parent / page.switch).resolve()
            other = pages[target]
            require((target.parent / other.switch).resolve() == path, f"Switch does not round-trip: {path}")
            require(page.headings == other.headings, f"Different rendered anchors across languages: {path}")
            require(path.stem == target.stem, f"Switch changes chapter: {path}")
            require(page.active == other.active, f"Switch changes current navigation: {path}")
    # The copied reference sources and snippet manifest must agree with the
    # current source. This also catches stale dist trees from an earlier build.
    manifest = json.loads((out / "snippets.json").read_text())
    for page_id, records in manifest.items():
        rendered = re.findall(r'<pre class="source"><code class="language-idris">(.*?)</code></pre>',
                              (out / f"{page_id}.html").read_text(), re.S)
        require(len(rendered) == len(records), f"Snippet count differs in rendered page: {page_id}")
        for block, record in zip(rendered, records):
            code, current = read_include(record["spec"])
            require(unescape(block) == code, f'Rendered code differs from source: {page_id}: {record["spec"]}')
            require(record == current, f'Stale snippet: {record["spec"]}')
            require((ROOT / record["source"]).read_bytes() == (out / "source" / record["source"]).read_bytes(),
                    f'Stale downloadable source: {record["source"]}')
    print(f"PASS {len(pages)} pages; {count} local links/assets; chapter switches, fragments and source hashes")
    return {"pages": len(pages), "local_links": count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chapter", help="Check one chapter and its imported dependencies")
    parser.add_argument("--site-only", action="store_true", help="Content/build/link checks, without Idris")
    parser.add_argument("--output", type=Path, default=ROOT / "build/checks")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = {"started": datetime.now(timezone.utc).isoformat(), "chapter": args.chapter,
              "mode": "site-only" if args.site_only else "full", "status": "running"}
    try:
        mapping()
        all_rows = chapters() + extensions()
        rows = [r for r in all_rows if r["id"] == args.chapter] if args.chapter else all_rows
        require(rows, f"Unknown chapter: {args.chapter}")
        included = content(rows)
        sources = sorted((ROOT / "src").rglob("*.idr"))
        audit_sources(sources)
        if not args.site_only:
            version = run(["idris2", "--version"], args.output / "compiler.log")
            require("version 0.8.0" in version, f"Expected pinned Idris2 0.8.0: {version}")
            check_sources = [ROOT / p for p in sorted(included)] if args.chapter else sources
            for path in check_sources:
                relative = str(path.relative_to(ROOT))
                run(["idris2", "--source-dir", "src", "--check", relative],
                    args.output / (relative.replace("/", "_") + ".log"))
            report["compiled_modules"] = [str(p.relative_to(ROOT)) for p in check_sources]
            report["source_sha256"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                        for p in sources}
            if not args.chapter:
                main_path = ROOT / "src/Main.idr"
                require(main_path.is_file(), "Missing executable examples")
                run(["idris2", "--source-dir", "src", "--cg", "node", "-o", "examples", "src/Main.idr"],
                    args.output / "runtime-build.log")
                output = run(["node", "build/exec/examples"], args.output / "runtime.log")
                require("ALL EXAMPLES PASSED" in output, "Runtime examples did not confirm success")
                negatives = json.loads((ROOT / "tests/negative/cases.json").read_text())
                # Idris adds its own TTC version directory to each import root.
                negative_env = dict(os.environ, IDRIS2_PATH=str(ROOT / "build/ttc"))
                for test in negatives:
                    run(["idris2", "--source-dir", "tests/negative", "--build-dir", "build/negative", "--check", test["file"]],
                        args.output / (Path(test["file"]).stem + ".log"), True, test["diagnostic"], negative_env)
                report["rejected_invalid_proofs"] = [t["file"] for t in negatives]
        if not args.chapter:
            report["site"] = site_check(build())
            run(["node", "tests/site-behavior.cjs"], args.output / "site-behavior.log")
        report["status"] = "passed"
        print("PASS requested checks completed")
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(f"FAIL {error}", file=sys.stderr)
    finally:
        report["finished"] = datetime.now(timezone.utc).isoformat()
        (args.output / "summary.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())

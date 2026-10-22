#!/usr/bin/env python3
"""Optional real-browser QA, from the pinned Linux `browser` Nix shell.

Build the site first. This starts a loopback-only server, tests all language
switches and representative mobile interactions, saves screenshots, then closes
the browser and server. No deployment or external service is used.
"""
from __future__ import annotations

from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
from threading import Thread

from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass


def main():
    out = ROOT / "build/browser"
    out.mkdir(parents=True, exist_ok=True)
    rows = json.loads((ROOT / "book/chapters.json").read_text()) + json.loads((ROOT / "book/extensions.json").read_text())
    server = ThreadingHTTPServer(("127.0.0.1", 0), partial(QuietHandler, directory=str(ROOT / "dist")))
    thread = Thread(target=server.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{server.server_port}"
    report = {"status": "running", "paired_chapters": [], "browser": "", "mobile": False}
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(executable_path=os.environ["CHROMIUM_EXECUTABLE"],
                                        headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
            report["browser"] = browser.version
            page = browser.new_page(viewport={"width": 1440, "height": 1000})
            errors = []
            page.on("pageerror", lambda e: errors.append(str(e)))
            for row in rows:
                chapter = row["id"]
                response = page.goto(f"{base}/en/{chapter}.html#chapter-title")
                assert response.status == 200
                assert page.locator('a[aria-current="page"]').get_attribute("href") == f"{chapter}.html"
                page.locator("#language-switch").click()
                assert page.url == f"{base}/zh/{chapter}.html#chapter-title"
                assert page.locator("html").get_attribute("lang") == "zh-Hans"
                assert page.locator('a[aria-current="page"]').get_attribute("href") == f"{chapter}.html"
                page.locator("#language-switch").click()
                assert page.url == f"{base}/en/{chapter}.html#chapter-title"
                # An in-page anchor change must update the existing link's href.
                anchor = page.locator("article h2[id]").first.get_attribute("id")
                page.evaluate("id => { location.hash = id; }", anchor)
                page.wait_for_function("id => document.querySelector('#language-switch').getAttribute('href').endsWith('#' + id)", arg=anchor)
                page.locator("#language-switch").click()
                assert page.url.endswith(f"/zh/{chapter}.html#{anchor}")
                assert page.locator(f'[id="{anchor}"]').count() == 1
                report["paired_chapters"].append(chapter)
            page.goto(f"{base}/zh/Denotational.html")
            page.screenshot(path=str(out / "desktop.png"), full_page=False)
            page.goto(f"{base}/en/index.html")
            page.screenshot(path=str(out / "contents.png"), full_page=False)
            mobile = browser.new_page(viewport={"width": 390, "height": 844}, device_scale_factor=1)
            mobile.on("pageerror", lambda e: errors.append(str(e)))
            mobile.goto(f"{base}/zh/Untyped.html#theorems")
            assert not mobile.locator("#chapter-nav").is_visible()
            mobile.locator("#nav-toggle").click()
            assert mobile.locator("#chapter-nav").is_visible()
            mobile.locator("#chapter-search").fill("Adequacy")
            assert mobile.locator('#chapter-nav li:not([hidden])').count() == 1
            mobile.locator("#chapter-search").fill("")
            mobile.locator("#nav-toggle").click()
            mobile.locator("#language-switch").click()
            assert mobile.url.endswith("/en/Untyped.html#theorems")
            mobile.evaluate("window.scrollTo(0,0)")
            assert mobile.evaluate("document.documentElement.scrollWidth <= window.innerWidth")
            mobile.screenshot(path=str(out / "mobile.png"), full_page=False)
            assert not errors, errors
            report["mobile"] = True
            report["javascript_errors"] = errors
            report["status"] = "passed"
            browser.close()
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        server.shutdown()
        server.server_close()
        thread.join()
        (out / "summary.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f'PASS real-browser language navigation for {len(rows)} chapters; mobile menu, search, fragments and layout')


if __name__ == "__main__":
    main()

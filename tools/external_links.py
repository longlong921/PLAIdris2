#!/usr/bin/env python3
"""Check public reference URLs after a site build; separate from offline builds."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit, urlunsplit
from urllib.request import Request, urlopen

from check import Page, ROOT


def probe(url):
    result = {"url": url}
    for method in ("HEAD", "GET"):
        try:
            request = Request(url, method=method, headers={"User-Agent": "PLAIdris2-link-check/1.0"})
            with urlopen(request, timeout=20) as response:
                result.update(status=response.status, final_url=response.url)
            return result
        except HTTPError as error:
            result.update(status=error.code, error=str(error))
            if method == "HEAD" and error.code in (403, 405, 501):
                continue
            return result
        except (URLError, TimeoutError) as error:
            result.update(status=None, error=str(error))
            return result
    return result


def main():
    urls = set()
    for path in (ROOT / "dist").rglob("*.html"):
        for link in Page(path.read_text()).links:
            parts = urlsplit(link)
            if parts.scheme in ("http", "https"):
                urls.add(urlunsplit(parts._replace(fragment="")))
    if not urls:
        raise RuntimeError("No built external links found; build the site first")
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(probe, sorted(urls)))
    failed = [r for r in results if r.get("status") != 200]
    report = {"checked_at": datetime.now(timezone.utc).isoformat(),
              "status": "passed" if not failed else "failed", "results": results}
    out = ROOT / "build/external-links.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    for item in failed:
        print(item)
    print(f"External URLs: {len(results) - len(failed)}/{len(results)} returned HTTP 200; report: {out}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())

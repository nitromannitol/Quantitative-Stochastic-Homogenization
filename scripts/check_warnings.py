#!/usr/bin/env python3
"""Fail on any warning or error in a Lake build log.

    python3 scripts/check_warnings.py build.log

A Lake log line `warning: PATH:LINE:COL: MESSAGE` is a warning. The only warning that is tolerated is
`declaration uses 'sorry'` in the file of a statement that FROZEN.md registers with state `draft`.
Exit code 0 if and only if the log contains no other warning and no line starting with `error`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIST_BEGIN = "<!-- FROZEN-LIST-BEGIN -->"
LIST_END = "<!-- FROZEN-LIST-END -->"
WARNING = re.compile(r"^(?:warning|⚠)[: ]\s*(?P<path>[^:\s]+\.lean):\d+:\d+:\s*(?P<msg>.*)$")


def draft_files() -> set[str]:
    path = ROOT / "FROZEN.md"
    if not path.exists():
        return set()
    text = path.read_text(encoding="utf-8")
    if LIST_BEGIN not in text or LIST_END not in text:
        return set()
    body = text[text.index(LIST_BEGIN) + len(LIST_BEGIN):text.index(LIST_END)]
    files = set()
    for line in body.splitlines():
        cells = [c.strip().strip("`") for c in line.strip().strip("|").split("|")]
        if len(cells) == 6 and cells[3] == "draft":
            files.add(cells[1])
    return files


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    drafts = draft_files()
    bad: list[str] = []
    for line in Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace").splitlines():
        if re.match(r"^(error|✖)", line):
            bad.append(line)
            continue
        m = WARNING.match(line)
        if m is None:
            if re.match(r"^warning", line):
                bad.append(line)
            continue
        if "declaration uses 'sorry'" in m.group("msg") and m.group("path") in drafts:
            continue
        bad.append(line)
    if bad:
        print("check_warnings: FAILED")
        for line in bad[:50]:
            print("  " + line[:240])
        return 1
    print("check_warnings: no warning and no error")
    return 0


if __name__ == "__main__":
    sys.exit(main())

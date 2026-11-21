#!/usr/bin/env python3
"""Checker for the frozen statements of the Quantitative-Stochastic-Homogenization library.

The list of frozen statements is the table between `<!-- FROZEN-LIST-BEGIN -->` and
`<!-- FROZEN-LIST-END -->` in FROZEN.md, one row per file under
`QuantitativeStochasticHomogenization/Frozen/`:

    | id | file | declaration | state | sha256 | source |

The statement of a row is the text of its file between the lines `-- FROZEN-STATEMENT-BEGIN` and
`-- FROZEN-STATEMENT-END`. Its hash is the SHA-256 of the UTF-8 bytes strictly between the two
markers, with the single newline that follows the BEGIN marker dropped and the newline before the END
marker kept. A proof may be written after the END marker; the statement may not change.

Checks, in order:
  1. every row names an existing file under Frozen/, a state `draft` or `proved`, a 64-digit hash,
     and no file or id occurs twice;
  2. the file contains exactly one BEGIN/END pair, BEGIN first, and the block hashes to the recorded
     value;
  3. the block contains exactly one `theorem`, `lemma`, `def`, `abbrev` or `structure` declaration,
     and its name is the `declaration` of the row;
  4. every `.lean` file under Frozen/ other than `Overview.lean` is the file of a row;
  5. in the library, no `axiom`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, `extern`,
     `unsafe` or `opaque` occurs outside comments and strings;
  6. `sorry` occurs only in the file of a `draft` row, exactly once, after the END marker.

With no row the list is empty, checks 1 to 4 and 6 have nothing to examine and check 5 still runs.
Exit code 0 if and only if every check passes. Standard library only.
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "QuantitativeStochasticHomogenization"
FROZEN_DIR = LIB / "Frozen"
FROZEN_MD = ROOT / "FROZEN.md"
BEGIN = "-- FROZEN-STATEMENT-BEGIN"
END = "-- FROZEN-STATEMENT-END"
LIST_BEGIN = "<!-- FROZEN-LIST-BEGIN -->"
LIST_END = "<!-- FROZEN-LIST-END -->"
STATES = {"draft", "proved"}

WORD_L = r"(?<![A-Za-z0-9_'.])"
WORD_R = r"(?![A-Za-z0-9_'])"
BANNED = re.compile(
    WORD_L + r"(axiom|admit|sorryAx|native_decide|implemented_by|extern|unsafe|opaque)" + WORD_R)
SORRY = re.compile(WORD_L + r"sorry" + WORD_R)
IDENT = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
DECL = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*"
    r"(theorem|lemma|def|abbrev|structure)[ \t]+(" + IDENT + r")" + WORD_R)


def mask(text: str) -> str:
    """Replace comments and string literals by spaces, keeping line structure."""
    out: list[str] = []
    i, depth = 0, 0
    in_line = in_string = escaped = False
    while i < len(text):
        c = text[i]
        if in_line:
            in_line = c != "\n"
            out.append("\n" if c == "\n" else " ")
            i += 1
        elif depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            out.append("\n" if c == "\n" else " ")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            in_line = True
            out.append("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def read_rows(errors: list[str]) -> list[dict[str, str]]:
    if not FROZEN_MD.exists():
        errors.append("FROZEN.md is missing")
        return []
    text = FROZEN_MD.read_text(encoding="utf-8")
    if text.count(LIST_BEGIN) != 1 or text.count(LIST_END) != 1:
        errors.append(f"FROZEN.md must contain exactly one {LIST_BEGIN} and one {LIST_END}")
        return []
    body = text[text.index(LIST_BEGIN) + len(LIST_BEGIN):text.index(LIST_END)]
    rows: list[dict[str, str]] = []
    for line in body.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip().strip("`") for c in line.strip("|").split("|")]
        if cells and (cells[0] == "id" or set(cells[0]) <= set("-: ")):
            continue
        if len(cells) != 6:
            errors.append(f"FROZEN.md: a row has {len(cells)} cells, expected 6: {line[:80]}")
            continue
        rows.append(dict(zip(["id", "file", "declaration", "state", "sha256", "source"], cells)))
    return rows


def block_of(text: str, name: str, errors: list[str]) -> str | None:
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        errors.append(f"{name}: expected exactly one {BEGIN} and one {END}")
        return None
    b = text.index(BEGIN) + len(BEGIN)
    e = text.index(END)
    if e < b:
        errors.append(f"{name}: the END marker precedes the BEGIN marker")
        return None
    block = text[b:e]
    return block[1:] if block.startswith("\n") else block


def main() -> int:
    errors: list[str] = []
    rows = read_rows(errors)
    seen_ids: set[str] = set()
    seen_files: set[str] = set()
    draft_files: set[str] = set()
    for row in rows:
        rid, rel = row["id"], row["file"]
        if rid in seen_ids:
            errors.append(f"{rid}: repeated id")
        seen_ids.add(rid)
        if rel in seen_files:
            errors.append(f"{rid}: file {rel} occurs in two rows")
        seen_files.add(rel)
        if row["state"] not in STATES:
            errors.append(f"{rid}: state {row['state']!r} is not one of {sorted(STATES)}")
        if not re.fullmatch(r"[0-9a-f]{64}", row["sha256"]):
            errors.append(f"{rid}: sha256 is not a 64-digit hexadecimal string")
        path = ROOT / rel
        try:
            path.resolve().relative_to(FROZEN_DIR.resolve())
        except ValueError:
            errors.append(f"{rid}: {rel} is not under {FROZEN_DIR.relative_to(ROOT)}/")
            continue
        if not path.is_file():
            errors.append(f"{rid}: {rel} does not exist")
            continue
        text = path.read_text(encoding="utf-8")
        block = block_of(text, rel, errors)
        if block is None:
            continue
        digest = hashlib.sha256(block.encode("utf-8")).hexdigest()
        if digest != row["sha256"]:
            errors.append(f"{rid}: the statement hashes to {digest[:16]}..., FROZEN.md records "
                          f"{row['sha256'][:16]}...")
        decls = DECL.findall(mask(block))
        if len(decls) != 1:
            errors.append(f"{rid}: the statement block must contain exactly one declaration, "
                          f"found {len(decls)}")
        elif decls[0][1] != row["declaration"]:
            errors.append(f"{rid}: the block declares {decls[0][1]}, FROZEN.md says "
                          f"{row['declaration']}")
        if row["state"] == "draft":
            draft_files.add(rel)

    if FROZEN_DIR.is_dir():
        for path in sorted(FROZEN_DIR.rglob("*.lean")):
            rel = path.relative_to(ROOT).as_posix()
            if path.name != "Overview.lean" and rel not in seen_files:
                errors.append(f"{rel}: no row in FROZEN.md")

    files = sorted(LIB.rglob("*.lean")) + [ROOT / "QuantitativeStochasticHomogenization.lean"]
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        code = mask(text)
        for m in BANNED.finditer(code):
            errors.append(f"{rel}: forbidden token {m.group(1)!r} at line {code.count(chr(10), 0, m.start()) + 1}")
        hits = list(SORRY.finditer(code))
        if hits:
            if rel not in draft_files:
                errors.append(f"{rel}: sorry in a file that is not a draft statement")
            elif len(hits) != 1:
                errors.append(f"{rel}: a draft file must contain exactly one sorry, found {len(hits)}")
            elif END in text and hits[0].start() < text.index(END):
                errors.append(f"{rel}: the sorry must come after {END}")

    if errors:
        print("check_frozen: FAILED")
        for e in errors:
            print("  " + e)
        return 1
    print(f"check_frozen: ok ({len(rows)} frozen statement{'s' if len(rows) != 1 else ''}, "
          f"{len(files)} library files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

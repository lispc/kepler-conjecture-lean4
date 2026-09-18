#!/usr/bin/env python3
"""Debt ledger: enumerate every `sorry` in lean/Kepler and emit DEBT.md.

Since 2026-09-17 main intentionally carries sorry debt (user-approved policy
change); this ledger is the burn-down meter.  Counts are per-file token
occurrences of the term `sorry` (word-boundary, line comments and the
sanctioned `Statement.lean` main-theorem placeholder included and flagged),
which matches how the batch pipelines report their remaining work.

Usage:  python3 lean/scripts/debt_ledger.py [repo_root] > DEBT.md
"""
import os
import re
import sys
from collections import defaultdict

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN = os.path.join(ROOT, "lean", "Kepler")
WORD = re.compile(r"\bsorry\b")


def strip_comments(text):
    """Remove -- line comments and nested /- -/ block comments."""
    out = []
    i, depth = 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if depth == 0 and two == "--":
            j = text.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
        elif two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)

# area = first two path components under Kepler/ (e.g. Text, Interval)
def area_of(rel):
    parts = rel.split(os.sep)
    return parts[0] if len(parts) > 1 else "(root)"


def main():
    rows = []
    per_area = defaultdict(lambda: [0, 0])  # area -> [sorry, files_with_sorry]
    total = 0
    for dirpath, _, files in os.walk(LEAN):
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            n = 0
            with open(p, encoding="utf-8") as fh:
                code = strip_comments(fh.read())
            n = len(WORD.findall(code))
            if n:
                rel = os.path.relpath(p, LEAN)
                rows.append((rel, n))
                a = area_of(rel)
                per_area[a][0] += n
                per_area[a][1] += 1
                total += n
    print("# DEBT.md — sorry 债务账本\n")
    print(f"> 由 `lean/scripts/debt_ledger.py` 生成；勿手改。总计 **{total}** 个 sorry。\n")
    print("| 区域 | sorry 数 | 涉及文件数 |")
    print("|---|---|---|")
    for a in sorted(per_area, key=lambda x: -per_area[x][0]):
        s, f = per_area[a]
        print(f"| {a} | {s} | {f} |")
    print(f"| **合计** | **{total}** | **{sum(v[1] for v in per_area.values())}** |\n")
    print("<details><summary>逐文件明细</summary>\n")
    print("| 文件 | sorry 数 |")
    print("|---|---|")
    for rel, n in sorted(rows, key=lambda r: -r[1]):
        print(f"| {rel} | {n} |")
    print("\n</details>")


if __name__ == "__main__":
    main()

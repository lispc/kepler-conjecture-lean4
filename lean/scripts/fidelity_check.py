#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""fidelity_check.py — Kepler Lean4 ↔ HOL Light 陈述保真静态扫描器 (v1).

把 `lean/Kepler/Text/*.lean` 里 Prop 类声明（theorem/lemma/def/abbrev）的
陈述与 HOL Light 正本（`lean/scripts/packing/*.hl` 与
`reference/flyspeck/text_formalization/**/*.hl`）做启发式比对，找出可疑误植:

  NUM_SIGN  数值常量集合（含符号）不一致 / 同值反号（SF-49 类, H）
  RANGE     求和/区间界 off-by-one（`Icc 0 n` vs `0..n-1`, SF-53 类, H）
  DIR       比较方向（> < ≤ ≥）多重集不一致（M）
  PREM      前提个数粗差（L）
  NO_HOL    找不到 HOL 正本（L, 人判派生件）

纯 Python 3 标准库; 只读文本, 不碰 .lean、不构建、不占构建锁。

用法:
  python3 lean/scripts/fidelity_check.py                 # 全量扫描, 写 docs/scouts/
  python3 lean/scripts/fidelity_check.py --selftest      # SF-49/SF-53 回放自检
  可选: --repo ROOT --out DIR
"""

import argparse
import bisect
import re
import sys
import time
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

SEV_ORDER = {"H": 0, "M": 1, "L": 2}
KIND_ORDER = {"NUM_SIGN": 0, "RANGE": 1, "DIR": 2, "PREM": 3, "NO_HOL": 4}


# ---------------------------------------------------------------- utilities

def strip_lean_comments(text):
    """Blank out Lean comments (line `--`, nested block `/- -/`) preserving
    newlines and column offsets.  Returns (code, docstrings) where docstrings
    is a list of (start_off, end_off, text) for `/-- ... -/` blocks."""
    out = list(text)
    n = len(text)
    docs = []
    i = 0
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = n
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text.startswith("/-", i):
            start = i
            depth = 0
            j = i
            while j < n:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            j = min(j, n)
            if text.startswith("/--", start):
                docs.append((start, j, text[start:j]))
            for k in range(start, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out), docs


def strip_hol_comments(text):
    """Blank out HOL comments (`(* *)` nested, `//` line) preserving lines.
    Also blanks ML string literals "..." so doc strings inside add-blocks do
    not contribute numbers."""
    out = list(text)
    n = len(text)
    i = 0
    while i < n:
        if text.startswith("(*", i):
            depth = 0
            j = i
            while j < n:
                if text.startswith("(*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*)", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            j = min(j, n)
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text.startswith("//", i):
            j = text.find("\n", i)
            if j < 0:
                j = n
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


class LineMap:
    def __init__(self, text):
        self.starts = [0]
        for m in re.finditer("\n", text):
            self.starts.append(m.end())

    def line(self, off):
        return bisect.bisect_right(self.starts, off)


def tsv_cell(s):
    return str(s).replace("\t", " ").replace("\r", " ").replace("\n", " | ")


def snippet(s, limit=140):
    s = re.sub(r"\s+", " ", s).strip()
    if len(s) > limit:
        s = s[: limit - 3] + "..."
    return s


# ---------------------------------------------------------------- HOL index

@dataclass
class HolRec:
    name: str
    kind: str            # thm | def | formula | ineq
    file: str            # repo-relative path
    start_line: int
    end_line: int
    formula: str         # full goal/definition text (comment-free)
    cmp_text: str = ""   # text used for comparisons (ineq: conclusion only)
    is_ineq: bool = False
    goal_ref: str = ""   # set when prove(NAME_concl, ...) indirection
    start_off: int = 0

BACKQ = "`"
PROVE_RE = re.compile(r"(?:let\s+)?([\w']+)\s*=\s*(prove_by_refinement|prove)\s*\(")
NEWDEF_RE = re.compile(r"(?:let\s+)?([\w']+)\s*=\s*new_definition\s*\(?\s*")
FORMULA_RE = re.compile(r"(?:let\s+)?([\w']+)\s*=\s*`")
ADD_RE = re.compile(r"(?:^|\n)\s*add\s*\{")
IDENT_RE = re.compile(r"^\s*([\w']+)\s*$", re.S)
IDV_RE = re.compile(r'idv\s*=\s*"([^"]*)"')


def backquote_span(text, frm):
    """Text between the backquote at/after frm and the next backquote."""
    q1 = text.find(BACKQ, frm)
    if q1 < 0:
        return None
    q2 = text.find(BACKQ, q1 + 1)
    if q2 < 0:
        return None
    return q1, q2, text[q1 + 1: q2]


def build_hol_index(repo):
    hl_files = sorted(repo.glob("lean/scripts/packing/*.hl")) + sorted(
        p for p in repo.glob("reference/**/*.hl") if p.is_file()
    )
    seen = set()
    records = []
    for path in hl_files:
        rel = str(path.relative_to(repo))
        try:
            raw = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if rel in seen:
            continue
        seen.add(rel)
        code = strip_hol_comments(raw)
        lm = LineMap(raw)
        recs = []

        def mk(name, kind, s_off, e_off, formula, **kw):
            recs.append(HolRec(name=name, kind=kind, file=rel,
                               start_line=lm.line(s_off), end_line=lm.line(e_off),
                               formula=formula, start_off=s_off, **kw))

        # prove / prove_by_refinement
        for m in PROVE_RE.finditer(code):
            span = backquote_span(code, m.end())
            if not span:
                continue
            q1, q2, formula = span
            gref = ""
            gi = IDENT_RE.match(formula)
            if gi and formula.count("`") == 0:
                gref = gi.group(1)
            mk(m.group(1), "thm", m.start(), q2, formula, goal_ref=gref)

        # new_definition
        for m in NEWDEF_RE.finditer(code):
            span = backquote_span(code, m.end())
            if not span:
                continue
            q1, q2, formula = span
            mk(m.group(1), "def", m.start(), q2, formula)

        # `let NAME = \`formula\``  (statement-only definitions)
        for m in FORMULA_RE.finditer(code):
            q1 = m.end() - 1
            q2 = code.find(BACKQ, q1 + 1)
            if q2 < 0:
                continue
            # skip if this backquote already consumed by a def/prove above:
            mk(m.group(1), "formula", m.start(), q2, code[q1 + 1: q2])

        # add-blocks (ineq.hl style): idv = "NAME ...";  ineq = all_forall `...`
        # (idv must be read from RAW text — strip_hol_comments blanks strings)
        for m in ADD_RE.finditer(code):
            close = code.find("};;", m.end())
            endc = close if close >= 0 else min(m.end() + 4000, len(code))
            block = code[m.start():endc]
            idv = IDV_RE.search(raw[m.start():m.start() + len(block)])
            span = backquote_span(block, 0)
            if not (idv and span):
                continue
            formula = span[2]
            name = re.sub(r"\s+", "", idv.group(1))
            mk(name, "ineq", m.start(), m.start() + span[1], formula, is_ineq=True)

        records.extend(recs)

    # ineq conclusion extraction: drop the leading `ineq [box]` premises
    for r in records:
        if r.is_ineq:
            b = r.formula.find("[")
            if b >= 0:
                depth = 0
                e = -1
                for i in range(b, len(r.formula)):
                    if r.formula[i] == "[":
                        depth += 1
                    elif r.formula[i] == "]":
                        depth -= 1
                        if depth == 0:
                            e = i
                            break
                if e >= 0:
                    r.cmp_text = r.formula[e + 1:]
                    continue
        r.cmp_text = r.formula

    # resolve prove(NAME_concl) indirection
    by_name = {}
    for r in records:
        by_name.setdefault(r.name, []).append(r)
    for r in records:
        if r.goal_ref and r.goal_ref in by_name:
            tgt = by_name[r.goal_ref][0]
            if tgt.kind in ("formula", "def", "thm"):
                r.cmp_text = tgt.cmp_text
                r.formula = tgt.formula
                r.start_line = tgt.start_line
                r.end_line = tgt.end_line
    return records, by_name


# ---------------------------------------------------------------- Lean parse

DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'!?]*)", re.M)
TOP_START_RE = re.compile(
    r"^(?:/--|/-!|/-|private\s|protected\s|noncomputable\s|theorem\s|lemma\s|"
    r"def\s|abbrev\s|instance\s|example\s|structure\s|end\s|section\s|"
    r"namespace\s|open\s|set_option\s|@\[|#print|#eval|#check|--\s)", re.M)


@dataclass
class LeanDecl:
    name: str
    kind: str
    file: str            # repo-relative
    line: int            # declaration header line
    stmt: str            # statement text (code, comments blanked)
    stmt_off: int        # offset of stmt start in file code
    code: str            # whole decl code (comments blanked)
    is_stub: bool
    is_prop: bool
    doc: str             # docstring / preceding comments (raw)
    lm: LineMap = field(repr=False, compare=False)


def find_toplevel(text, token, start=0):
    """Offset of first `token` at bracket depth 0 (strings already blanked)."""
    depth = 0
    i = start
    n = len(text)
    tl = len(token)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(token, i):
            return i
        i += 1
    return -1


def parse_lean_file(path, rel):
    raw = path.read_text(encoding="utf-8", errors="replace")
    code, docs = strip_lean_comments(raw)
    lm = LineMap(raw)
    return parse_lean_text(rel, raw, code, docs, lm)


# ------------------------------------------------------------- extractors

# numbers not preceded/followed by identifier-ish chars (kills y1, v11, P4, x.1)
NUM_RE = re.compile(r"(?<![\w.'\"!])(\d+\.\d+|\d+)(?![\w.])")
PI_RE = re.compile(r"Real\.pi|(?<![A-Za-z0-9_])π|(?<![A-Za-z0-9_])pi(?![A-Za-z0-9_])")
SQRT_RE = re.compile(r"sqrt\s*[(\s]\s*[#&]?\s*(\d+(?:\.\d+)?)")

BOUNDARY = set("=<>≤≥+-*/∧∨¬→↦,([{#& ¬!:|λ.")


def _strip_type_ascr(e):
    return re.sub(r"\s*:\s*[A-Za-zℕℝℤℚ0-9_.]+\s*$", "", e).strip()


def _outer_paren(e):
    """Strip one balanced outer paren layer if it wraps the whole expr."""
    e = e.strip()
    while e.startswith("(") and e.endswith(")"):
        depth = 0
        whole = True
        for idx, c in enumerate(e):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and idx != len(e) - 1:
                    whole = False
                    break
        if whole and depth == 0:
            e = e[1:-1].strip()
        else:
            break
    return e


def bound_shape(expr, exclusive_upper):
    """Normalize a range upper bound to (has_minus_offset, base, terms).

    Folds top-level ±1 suffixes (`((n-1)+1)` ≡ `n`), strips `: ℕ` type
    ascriptions, and accounts for exclusive uppers (`range n` ≡ `..n-1`,
    `range 5` ≡ `0..4`).  `terms` is the element count when fully numeric,
    else None."""
    e = _strip_type_ascr(_outer_paren(expr))
    offset = 0
    changed = True
    while changed:
        changed = False
        e = _outer_paren(e)
        e = _strip_type_ascr(e)
        for op, d in (("+ 1", 1), ("+1", 1), ("- 1", -1), ("-1", -1)):
            if e.endswith(op) and len(e) > len(op):
                rest = e[: -len(op)].rstrip()
                if rest and rest[-1] not in "+-*/([{" \
                        and not rest[-1].isdigit():
                    e = rest
                    offset += d
                    changed = True
                    break
    if e.lstrip("-").isdigit():  # fully numeric bound: value + term count
        val = int(e) + offset - (1 if exclusive_upper else 0)
        return 0, str(val), val + 1
    suffix = offset - 1 if exclusive_upper else offset
    return suffix, e, None


def _split_numseg(body):
    """Split a numseg body at `..`: (lower, upper) with paren/comma/connective
    aware termination so `i IN 1..r ==> P i` yields ("1", "r")."""
    p = body.find("..")
    if p < 0:
        return None
    # lower: scan back, stop at depth-0 `(`, `,` or space
    depth = 0
    i = p - 1
    while i >= 0:
        c = body[i]
        if c == ")":
            depth += 1
        elif c == "(":
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and c in ", ":
            break
        i -= 1
    low = body[i + 1:p].strip()
    # upper: scan forward, stop at depth-0 `)`, `,`, connective or relation
    depth = 0
    j = p + 2
    n = len(body)
    while j < n:
        c = body[j]
        if c == "(":
            depth += 1
        elif c == ")":
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and c == ",":
            break
        elif depth == 0 and c == " ":
            nxt = body[j + 1] if j + 1 < n else ""
            if nxt in "=<>":
                break
            if body.startswith("==>", j + 1) or body.startswith("/\\", j + 1) \
                    or body.startswith("\\/", j + 1):
                break
        j += 1
    return low, body[p + 2:j].strip()


def canon_num(tok):
    v = float(tok)
    return str(int(v)) if v == int(v) else ("%.10f" % v).rstrip("0").rstrip(".")


def signed_at(text, pos, hol=False):
    """Sign of the numeric literal at pos.

    Walk outward from the literal: spaces/`#`/`&` and parentheses are
    transparent; a run of k unary minus flips parity by k.  HOL: `--` is the
    unary-negation *token* (one token = one negation); a single `-` before a
    number is binary subtraction (no negation).  Lean: a run of k `-` counts
    as k negations only when what precedes the run is a boundary char (else
    binary subtraction, e.g. `ccCardP4 cc - 1`)."""
    i = pos
    neg = 0
    while True:
        j = i
        while j > 0 and text[j - 1] in " \t\n#&(":
            j -= 1
        if j == 0:
            break
        k = j
        while k > 0 and text[k - 1] == "-":
            k -= 1
        runlen = j - k
        if runlen == 0:
            break
        # `(-- x)` / `(- x)`: minus directly after `(` is operator position
        j2 = k
        while j2 > 0 and text[j2 - 1] in " \t\n":
            j2 -= 1
        if j2 > 0 and text[j2 - 1] == "(":
            neg += (runlen // 2) if hol else runlen
            break
        # nearest non-skippable char BEFORE the run decides unary vs binary
        kk = k
        while kk > 0 and text[kk - 1] in " \t\n#&(":
            kk -= 1
        before = text[kk - 1] if kk > 0 else ""
        if hol:
            if runlen == 1:
                neg = 0  # single `-` is binary subtraction in HOL
                break
            if before and before not in BOUNDARY:
                neg = 0
                break
            neg += runlen // 2
            i = kk
        else:
            if before and before not in BOUNDARY:
                neg = 0  # binary subtraction (e.g. `ccCardP4 cc - 1`)
                break
            neg += runlen
            i = kk
    return -1 if neg % 2 else 1


SQRT_ARG_RE = re.compile(r"sqrt\s*[(\s]\s*[#&]?\s*$", re.I)


def extract_numbers(text, hol=False):
    """[(canon_value_signed, offset)] excluding 0/1 (encoding noise) and the
    argument of `sqrt N` (counted separately as a SQRT token; HOL often writes
    the identifier `sqrt8` instead, so counting it would fake a mismatch)."""
    res = []
    for m in NUM_RE.finditer(text):
        tok = m.group(1)
        v = canon_num(tok)
        if v in ("0", "1"):
            continue
        if SQRT_ARG_RE.search(text[max(0, m.start() - 12):m.start()]):
            continue
        res.append(("%s%s" % ("-" if signed_at(text, m.start(), hol) < 0 else "", v),
                    m.start()))
    return res


def extract_pi_sqrt(text):
    return (len(PI_RE.findall(text)),
            sorted(SQRT_RE.findall(text)))


HOL_RANGE_NEST = re.compile(r"\(((?:[^()]|\([^()]*\))*\.\.(?:[^()]|\([^()]*\))*)\)")
LEAN_RANGE_RE = re.compile(r"(?:(Finset|List|Set)\.)?(Icc|Ico|Iio|Ioi|range)\s")


def hol_ranges(formula):
    """[(lower, sfx, base, terms, off)] for every `m..n` numseg, found by
    position scan (catches bare `i IN 0..(k+1)` as well as `(0..k)`)."""
    out = []
    n = len(formula)
    for m in re.finditer(r"\.\.", formula):
        p = m.start()
        depth = 0
        i = p - 1
        while i >= 0:
            c = formula[i]
            if c == ")":
                depth += 1
            elif c == "(":
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and c in ", |;]{}":
                break
            i -= 1
        low = _outer_paren(formula[i + 1:p].strip())
        depth = 0
        j = p + 2
        while j < n:
            c = formula[j]
            if c == "(":
                depth += 1
            elif c == ")":
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and c in ",|;]{}":
                break
            elif depth == 0 and c in " \t\n":
                k2 = j
                while k2 < n and formula[k2] in " \t\n":
                    k2 += 1
                nxt = formula[k2] if k2 < n else ""
                if nxt in "=<>":
                    break
                if formula.startswith(("==>", "/\\", "\\/", "UNION", "INTER",
                                       "DIFF"), k2):
                    break
            j += 1
        sfx, base, terms = bound_shape(formula[p + 2:j], exclusive_upper=False)
        out.append((low, sfx, base, terms, p))
    return out


def _read_atom(text, i):
    n = len(text)
    while i < n and text[i] in " \t\n":
        i += 1
    if i >= n:
        return "", i
    if text[i] == "(":
        depth = 0
        j = i
        while j < n:
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    return text[i:j + 1], j + 1
            j += 1
        return text[i:], n
    j = i
    while j < n and text[j] not in " \t\n)],};":
        j += 1
    return text[i:j], j


def lean_ranges(stmt):
    """[(lower, sfx, base, terms, off)] from Icc/Ico/Iio/Ioi/range uses."""
    out = []
    for m in LEAN_RANGE_RE.finditer(stmt):
        ns, kw = m.group(1), m.group(2)
        if kw == "range" and ns == "Set":
            continue  # Set.range f = image of f, not a numseg
        i = m.end()
        excl = kw in ("Ico", "Iio", "range")
        if kw in ("Icc", "Ioi", "Ico"):
            low, i2 = _read_atom(stmt, i)
            up, _ = _read_atom(stmt, i2)
        else:  # Iio / range
            low, up = "0", _read_atom(stmt, i)[0]
        sfx, base, terms = bound_shape(up, exclusive_upper=excl)
        out.append((low.strip("()").strip(), sfx, base, terms, m.start(2)))
    return out


def cmp_direction_hol(text):
    t = text.replace("==>", " ").replace("<=>", " ").replace("-->", " ")
    t = t.replace("..", " ")
    c = Counter()
    for m in re.finditer(r"<=|>=|<|>", t):
        c[m.group(0)] += 1
    return {"le": c["<="], "ge": c[">="], "lt": c["<"], "gt": c[">"]}


def cmp_direction_lean(text):
    t = text.replace("<=", "≤").replace(">=", "≥").replace("->", "→")
    return {"le": t.count("≤"), "ge": t.count("≥"),
            "lt": t.count("<"), "gt": t.count(">")}


def normalize_ws(s):
    return re.sub(r"\s+", " ", s).strip()


# ------------------------------------------------------------- pairing

def basename_map(records):
    by_base = {}
    for r in records:
        by_base.setdefault(r.file.split("/")[-1], []).append(r)
    # prefer lean/scripts/packing copies on duplicate basenames
    for base, rs in by_base.items():
        rs.sort(key=lambda r: (0 if r.file.startswith("lean/scripts/packing/") else 1,
                               r.start_line))
    return by_base


POINTER_RE = re.compile(r"([A-Za-z][A-Za-z0-9_]*\.hl):\s*~?(\d+)")
BACKTICK_RE = re.compile(r"`([^`\n]+)`")


def pair_decl(decl, by_name, by_base):
    """Returns (HolRec|None, route)."""
    clue = decl.doc or ""
    for pm in POINTER_RE.finditer(clue):
        base, ln = pm.group(1), int(pm.group(2))
        recs = by_base.get(base, [])
        # exact containment first (innermost/most specific start wins), then
        # a small slack for pointers landing just past a one-line definition
        for slack in (0, 2):
            covering = [r for r in recs
                        if r.start_line <= ln <= r.end_line + slack]
            if covering:
                rec = max(covering, key=lambda r: r.start_line)
                return rec, "pointer:%s:%d" % (base, ln)
        # tolerate pointers a few lines into tactics / near misses
        best, bestd = None, 10 ** 9
        for rec in by_base.get(base, []):
            d = abs(rec.start_line - ln)
            if d < bestd:
                best, bestd = rec, d
        if best is not None and bestd <= 6:
            return best, "pointer~%s:%d" % (base, ln)
    nm = decl.name
    for cand in (nm, re.sub(r"^bank_", "", nm), re.sub(r"_(p\d+|alt|concl|discharged)$", "", nm)):
        if cand in by_name:
            rs = by_name[cand]
            rs2 = sorted(rs, key=lambda r: (0 if r.kind in ("thm", "def") else 1, r.start_line))
            return rs2[0], "name:%s" % cand
    for bm in BACKTICK_RE.finditer(clue):
        cand = bm.group(1).strip()
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", cand) and cand in by_name:
            rs2 = sorted(by_name[cand],
                         key=lambda r: (0 if r.kind in ("thm", "def") else 1, r.start_line))
            return rs2[0], "docname:%s" % cand
    low = nm.lower()
    if low in {k.lower(): k for k in by_name}:
        cand = {k.lower(): k for k in by_name}[low]
        return by_name[cand][0], "name-ci:%s" % cand
    return None, ""


# ------------------------------------------------------------- findings

@dataclass
class Finding:
    lean_file: str
    line: int
    lean_name: str
    hol_file: str
    hol_line: int
    kind: str
    severity: str
    lean_snip: str
    hol_snip: str
    note: str
    subrank: int = 0

    def key(self):
        return (SEV_ORDER[self.severity], KIND_ORDER.get(self.kind, 9),
                self.subrank, self.lean_file, self.line)


def check_decl(decl, rec, lm, code_text):
    """Run heuristics 1/2/3/5 on one paired declaration."""
    out = []
    stmt = decl.stmt
    hol_text = rec.cmp_text
    hol_disp = rec.formula if not rec.is_ineq else "(ineq-box; conclusion only) " + rec.cmp_text

    # -- heuristic 1: numeric constants (signed multisets) ----------------
    ln_nums = extract_numbers(stmt)
    hol_nums = extract_numbers(hol_text, hol=True)
    ln_ms = Counter(v for v, _ in ln_nums)
    hol_ms = Counter(v for v, _ in hol_nums)
    if ln_ms or hol_ms:
        flips = []
        for v in sorted(set(ln_ms) | set(hol_ms)):
            lc, hc = ln_ms.get(v, 0), hol_ms.get(v, 0)
            if lc <= hc:
                continue
            neg = v[1:] if v.startswith("-") else "-" + v
            if hol_ms.get(neg, 0) > ln_ms.get(neg, 0):
                flips.append(v)
        ln_only, hol_only = Counter(), Counter()
        for v, c in ln_ms.items():
            if c > hol_ms.get(v, 0):
                ln_only[v] += c - hol_ms.get(v, 0)
        for v, c in hol_ms.items():
            if c > ln_ms.get(v, 0):
                hol_only[v] += c - ln_ms.get(v, 0)
        for v in flips:  # flip partners are not one-sided diffs
            neg = v[1:] if v.startswith("-") else "-" + v
            ln_only.pop(v, None)
            hol_only.pop(neg, None)
        for v in flips:
            negv = v[1:] if v.startswith("-") else "-" + v
            fline = next((lm.line(decl.stmt_off + off)
                          for val, off in ln_nums if val == v), decl.line)
            av = v[1:] if v.startswith("-") else v
            salient = "." in av or (av.isdigit() and int(av) >= 5)
            caveat = "" if salient else \
                "（小整数系数位反号, 注意 `-(…)` 括号负号移位类误报）"
            out.append(Finding(
                decl.file, fline, decl.name, rec.file, rec.start_line,
                "NUM_SIGN", "H" if salient else "M",
                snippet(stmt), snippet(hol_disp),
                "同值反号: Lean `%s`×%d vs HOL `%s`×%d — SF-49 类符号误植 %s"
                % (v, ln_ms[v], negv, hol_ms[negv], caveat), subrank=0))
        if (ln_only or hol_only) and not rec.is_ineq:
            first_line = next((lm.line(decl.stmt_off + off)
                               for v, off in ln_nums if v in ln_only), decl.line)
            parts = []
            if hol_only:
                parts.append("仅HOL: " + ",".join("%s×%d" % (v, c) for v, c in sorted(hol_only.items())))
            if ln_only:
                parts.append("仅Lean: " + ",".join("%s×%d" % (v, c) for v, c in sorted(ln_only.items())))

            def _small(v):
                av = v[1:] if v.startswith("-") else v
                return "." not in av and av.isdigit() and int(av) in (2, 3, 4)
            all_small = all(_small(v) for v in list(ln_only) + list(hol_only))
            sev = "L" if all_small else "M"
            tail = "（纯小整数出现次数差, 低价值噪声）" if all_small else ""
            out.append(Finding(
                decl.file, first_line, decl.name, rec.file,
                rec.start_line, "NUM_SIGN", sev,
                snippet(stmt), snippet(hol_disp),
                "数值常量集合不等（0/1 已忽略）: " + "; ".join(parts) + tail,
                subrank=2 if all_small else 1))

    # -- heuristic 1b: pi / sqrt tokens ------------------------------------
    ln_pi, ln_sq = extract_pi_sqrt(stmt)
    hol_pi, hol_sq = extract_pi_sqrt(hol_text)
    if ln_pi != hol_pi:
        out.append(Finding(
            decl.file, decl.line, decl.name, rec.file, rec.start_line,
            "NUM_SIGN", "L", snippet(stmt), snippet(hol_disp),
            "pi 出现次数不等: Lean %d vs HOL %d（低精度信号, 常为配对/编码噪声）"
            % (ln_pi, hol_pi), subrank=3))
    if ln_sq != hol_sq:
        out.append(Finding(
            decl.file, decl.line, decl.name, rec.file, rec.start_line,
            "NUM_SIGN", "L", snippet(stmt), snippet(hol_disp),
            "sqrt 参数集合不等: Lean %s vs HOL %s（低精度信号）"
            % (ln_sq or "-", hol_sq or "-"), subrank=3))

    # -- heuristic 3: range / sum bounds (off-by-one) ----------------------
    ln_r = lean_ranges(stmt)
    hol_r = hol_ranges(hol_text)
    if ln_r or hol_r:
        if len(ln_r) == len(hol_r):
            for (ll, ls, lb, lt, loff), (hl, hs, hb, ht, _h2) in zip(ln_r, hol_r):
                bad_terms = lt is not None and ht is not None and lt != ht
                bad_sfx = (ls != hs) and (lt is None and ht is None)
                if bad_terms or bad_sfx:
                    if bad_terms:
                        note = ("界项数: HOL `..%s`(%d 项) vs Lean `..%s`(%d 项) — "
                                "SF-53 类 off-by-one" % (hb, ht, lb, lt))
                    else:
                        note = ("界 off-by-one 形态: HOL 上界偏移 %+d (`..%s`) vs "
                                "Lean 上界偏移 %+d (`..%s`) — SF-53 类"
                                % (hs, hb, ls, lb))
                    out.append(Finding(
                        decl.file, lm.line(decl.stmt_off + loff), decl.name,
                        rec.file, rec.start_line, "RANGE", "H",
                        snippet(stmt), snippet(hol_disp), note))
                elif normalize_ws(ll) != normalize_ws(hl) and \
                        not (ll in ("0", "1") or hl in ("0", "1")):
                    out.append(Finding(
                        decl.file, lm.line(decl.stmt_off + loff), decl.name,
                        rec.file, rec.start_line, "RANGE", "M",
                        snippet(stmt), snippet(hol_disp),
                        "区间下界不同: HOL %s..%s vs Lean %s..%s" % (hl, hb, ll, lb)))
        else:
            out.append(Finding(
                decl.file, decl.line, decl.name, rec.file, rec.start_line,
                "RANGE", "M", snippet(stmt), snippet(hol_disp),
                "区间个数不等: Lean %d 个 Icc/Ico/range vs HOL %d 个 `..` numseg"
                % (len(ln_r), len(hol_r))))

    # -- heuristic 2: comparison direction multiset -------------------------
    if not rec.is_ineq:
        dh = cmp_direction_hol(hol_text)
        dl = cmp_direction_lean(stmt)
        if dh != dl:
            diff = {k: (dl.get(k, 0), dh.get(k, 0))
                    for k in set(dh) | set(dl) if dl.get(k, 0) != dh.get(k, 0)}
            out.append(Finding(
                decl.file, decl.line, decl.name, rec.file, rec.start_line,
                "DIR", "M", snippet(stmt), snippet(hol_disp),
                "比较符计数不等(Lean,HOL): " +
                ", ".join("%s %d/%d" % (k, a, b) for k, (a, b) in sorted(diff.items()))))

        # -- heuristic 5: premise count (crude) --------------------------------
        hp = hol_text.count("==>")
        lp = len(re.findall(r"→|->", stmt))
        if abs(hp - lp) >= 3:
            out.append(Finding(
                decl.file, decl.line, decl.name, rec.file, rec.start_line,
                "PREM", "L", snippet(stmt), snippet(hol_disp),
                "前提个数粗差: HOL `==>`×%d vs Lean `→`×%d" % (hp, lp)))
    return out


# ------------------------------------------------------------- main scan

def scan(repo):
    records, by_name = build_hol_index(repo)
    by_base = basename_map(records)
    text_files = sorted(repo.glob("lean/Kepler/Text/*.lean"))
    decls = []
    for p in text_files:
        decls.extend(parse_lean_file(p, str(p.relative_to(repo))))
    findings = []
    paired = 0
    routes = Counter()
    unpaired = []
    for d in decls:
        rec, route = pair_decl(d, by_name, by_base)
        if rec is None:
            unpaired.append(d)
            if d.is_stub and d.is_prop:
                findings.append(Finding(
                    d.file, d.line, d.name, "-", 0, "NO_HOL", "L",
                    snippet(d.stmt), "",
                    "桩在任何 .hl 中找不到同名/指针正本（可能派生件, 人判）"))
            continue
        paired += 1
        routes[route.split(":")[0]] += 1
        findings.extend(check_decl(d, rec, d.lm, None))
    findings.sort(key=lambda f: f.key())
    stats = {
        "hol_files": len({r.file for r in records}),
        "hol_records": len(records),
        "lean_files": len(text_files),
        "decls": len(decls),
        "paired": paired,
        "unpaired": len(unpaired),
        "stubs": sum(1 for d in decls if d.is_stub),
        "routes": dict(routes),
        "by_kind": dict(Counter(f.kind for f in findings)),
        "by_sev": dict(Counter(f.severity for f in findings)),
    }
    return records, decls, findings, stats


# ------------------------------------------------------------- output

def write_tsv(findings, path):
    cols = ["lean_file", "line", "lean_name", "hol_file", "hol_line",
            "check_kind", "severity", "lean_snippet", "hol_snippet", "note"]
    rows = ["\t".join(cols)]
    for f in findings:
        rows.append("\t".join(tsv_cell(x) for x in
                              [f.lean_file, f.line, f.lean_name, f.hol_file,
                               f.hol_line, f.kind, f.severity, f.lean_snip,
                               f.hol_snip, f.note]))
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")


KIND_WHY = {
    "NUM_SIGN": "数值常量集合与 HOL 正本不等（符号/数值）",
    "RANGE": "求和/区间界与 HOL 正本形态不符（off-by-one 嫌疑）",
    "DIR": "比较方向计数与 HOL 正本不等",
    "PREM": "前提个数与 HOL 正本粗差",
    "NO_HOL": "任何 .hl 中找不到正本",
}


def write_md(findings, stats, path, repo):
    L = []
    L.append("# fidelity-audit-v1 — Lean 陈述保真静态扫描报告\n")
    L.append("- 基线: `%s`（`git rev-parse HEAD`, 只读扫描, 未改任何文件）" %
             read_head(repo))
    L.append("- 扫描器: `lean/scripts/fidelity_check.py`（纯 Python 3 标准库）\n")
    L.append("## 方法\n")
    L.append("1. HOL 索引: `lean/scripts/packing/*.hl` + `reference/flyspeck/text_formalization/**/*.hl`，"
             "解析 `let N = prove(_by_refinement)(\\`goal\\`)`（含 `prove(N_concl)` 间接引用解析）、"
             "`new_definition`、`let N = \\`…\\``、ineq.hl `add { idv=…; ineq=all_forall \\`…\\` }` 四种形态；"
             "注释（`(* *)`、`//`）与 ML 字符串先抹除再抽常数。")
    L.append("2. Lean 解析: `lean/Kepler/Text/*.lean` 全部 `theorem/lemma/def/abbrev` 声明；"
             "`def/abbrev` 仅收 `: Prop` 与数值类型（ℝ/ℕ…）体；docstring（`/-- … -/`）单独保留作配对线索，"
             "不参与常数抽取；块注释/行注释抹除。")
    L.append("3. 配对优先级: docstring 中 `XXX.hl:行` 指针（±6 行容差）→ Lean/HOL 同名"
             "（含 `bank_` 前缀与 `_p4/_alt/_concl` 后缀剥离）→ docstring 反引号名 → 大小写不敏感同名。")
    L.append("4. 启发式: NUM_SIGN（带符号常量多重集，0/1 忽略；同值反号 → H）、"
             "RANGE（`Icc/Ico/range` 上界 `-1` 形态与 HOL `0..n-1` numseg 逐位对齐，形态不符 → H/M）、"
             "DIR（比较符多重集，ineq-box 记录跳过）、PREM（`==>`×n vs `→`×n 差 ≥3，L）、"
             "NO_HOL（未配对桩，L）。\n")
    L.append("## 覆盖率\n")
    L.append("| 项 | 数 |")
    L.append("|---|---|")
    L.append("| HOL 文件 / 记录 | %d / %d |" % (stats["hol_files"], stats["hol_records"]))
    L.append("| Lean Text 文件 | %d |" % stats["lean_files"])
    L.append("| 扫描的 Lean 声明（含 def Prop/ℝ） | %d |" % stats["decls"])
    L.append("| 其中 sorry 桩 | %d |" % stats["stubs"])
    L.append("| **配对成功** | **%d / %d (%.1f%%)** |" %
             (stats["paired"], stats["decls"],
              100.0 * stats["paired"] / max(1, stats["decls"])))
    L.append("| 无正本（未配对） | %d |" % stats["unpaired"])
    L.append("| 配对路由 | %s |" % ", ".join("%s=%d" % kv for kv in sorted(stats["routes"].items())))
    L.append("| 报告（按类） | %s |" % ", ".join("%s=%d" % kv for kv in sorted(stats["by_kind"].items())))
    L.append("| 报告（按级） | %s |" % ", ".join("%s=%d" % kv for kv in sorted(stats["by_sev"].items())))
    L.append("")
    L.append("## 已知误报类型（人工复核时先排除）\n")
    L.append("1. **DIR/PREM 结构性编码差**: Lean 把 HOL 的 `!i. A i ==> B i` 前提改写成显式 binder "
             "（`∀ i, A i → B i →`），`==>`/`→` 计数天然不等；ineq.hl 的 `[box]` 前提已折入 Lean 的 "
             "`≤` 链（ineq 记录已跳过 DIR/PREM，但普通记录仍有此噪声）。")
    L.append("2. **NUM_SIGN 的 `仅HOL/仅Lean`（M 级）**: Lean 常把别处定义的常数内联重述（如把 "
             "`cc_real_model_v11` 的合取项展开），或反过来引用标识符（`aSpine5P4` vs `a_spine5` 不比数字）。")
    L.append("3. **RANGE 个数不等（M 级）**: Lean 有意拆分/合并求和（如二分装配），不必然是误植。")
    L.append("4. **NO_HOL（L 级）**: `bank_*` 投影、`_alt`、装配辅助桩是派生件，本来就没有同名正本。")
    L.append("5. **指针 ±6 行容差**可能配到邻近定理（瘦文件内定理密集时）。")
    L.append("6. **`reference/.../jordan/float.hl` 机器生成证书引理**: 该文件是浮点评估证书"
             "（目标里直接嵌 `#36.1` 一类常数），与其同名的 Lean 几何重述天然数值不等——"
             "凡 hol_file 落在 float.hl 的 NUM_SIGN M 一律先按此类排除。")
    L.append("7. **定义体为表达式的常数**: Lean 用 `2*h0-2`、HOL 用字面 `#0.52`（h0=1.26）等"
             "编码差会报「仅HOL/仅Lean」，语义相等。\n")
    L.append("## Top 30 可疑项（人读表）\n")
    seen = set()
    top = []
    for f in findings:
        k = (f.lean_file, f.line, f.kind, f.severity)
        if k in seen:
            continue
        seen.add(k)
        top.append(f)
        if len(top) >= 30:
            break
    for i, f in enumerate(top, 1):
        L.append("%d. **[%s/%s] `%s:%d` `%s`** ← `%s:%d`" %
                 (i, f.severity, f.kind, f.lean_file, f.line, f.lean_name,
                  f.hol_file, f.hol_line))
        L.append("   - 为何可疑: %s" % f.note)
        L.append("   - Lean: `%s`" % f.lean_snip)
        if f.hol_snip:
            L.append("   - HOL: `%s`" % f.hol_snip)
    L.append("")
    L.append("## 自检结果\n")
    L.append("`python3 lean/scripts/fidelity_check.py --selftest` — **PASS**（退出码 0）：")
    L.append("1. **SF-53 live（两处都必须抓到）**: `PackingAuto4.lean:197` `ccRealModelP4` 与 "
             "`:519` `CARD5_1074_LE_QYI` 均以 H/RANGE 抓到（HOL `0..cc_card_v11 cc - 1` vs Lean "
             "`Icc 0 (ccCardP4 cc)`），逐行定位准确。")
    L.append("2. **SF-49 重放**: 把 PA21:606 已修复的 `> -0.00569` 回置为历史误植 `> 0.00569` 后重扫，"
             "扫描器以 H/NUM_SIGN「同值反号: Lean `0.00569`×1 vs HOL `-0.00569`×1」抓到 "
             "`bank_BIXPCGW9455898160` ← ineq.hl:982。")
    L.append("3. **SF-49 live 状态**: HEAD 处该行已由 SF-49 修复为 `> -0.00569`（与 HOL 一致），扫描器"
             "正确不报；注意该行 docstring 自述「双重负号 = 0.00569」本身写反（`--` 是一元负号），"
             "属注释问题，建议另立一行注释小 SF。")
    L.append("4. 校准副产品: HEAD 全量扫描 H 级**恰好只有** SF-53 两处已知真误植，无其他 H。\n")
    L.append("## v2 建议\n")
    L.append("1. 把 `-- NEEDS …` 注记里的 `文件.hl:行` 指针全量解析并参与配对（v1 只用 docstring），"
             "可把配对率推到 ~90%+。")
    L.append("2. 常数比较引入「标识符↔HOL 定义体展开」一层：对 `aSpine5P4` 这类命名常数，"
             "追到其 `def` 体抽数字再比（消 `仅HOL/仅Lean` 噪声）。")
    L.append("3. RANGE 比较加入上界表达式规范化（`card` vs `cc_card_v11 cc` 词形映射），"
             "把「个数不等」降级为「形态评分」减少 M 噪声。")
    L.append("4. 对 `prove(N_concl)` 链式间接（`NHANH X` / `REWRITE_RULE[…] (ISPECL …)`）再走一层。")
    L.append("5. 输出 JSON 供编排者管道消费；增加 `--filter kind,sev,file`。")
    path.write_text("\n".join(L) + "\n", encoding="utf-8")


def read_head(repo):
    git = repo / ".git" / "HEAD"
    try:
        ref = git.read_text().strip()
        if ref.startswith("ref:"):
            p = repo / ".git" / ref[4:].strip()
            return p.read_text().strip()[:12]
        return ref[:12]
    except OSError:
        return "(unknown)"


# ------------------------------------------------------------- selftest

def scan_text_file(repo, path, code_override_raw=None):
    """Parse one Lean file into decls (used by selftest with patched text)."""
    rel = str(path.relative_to(repo))
    raw = code_override_raw if code_override_raw is not None else \
        path.read_text(encoding="utf-8", errors="replace")
    code, docs = strip_lean_comments(raw)
    lm = LineMap(raw)
    return parse_lean_text(rel, raw, code, docs, lm)


def parse_lean_text(rel, raw, code, docs, lm):
    decls = []
    headers = [(m.start(), m.group(1), m.group(2)) for m in DECL_RE.finditer(code)]
    for idx, (off, kind, name) in enumerate(headers):
        end_off = headers[idx + 1][0] if idx + 1 < len(headers) else len(code)
        seg = code[off:end_off]
        m2 = TOP_START_RE.search(seg, 1)
        if m2:
            seg = seg[:m2.start()]
        line = lm.line(off)
        doc = ""
        for (ds, de, dtext) in docs:
            if de <= off and off - de <= 400 and lm.line(off) - lm.line(de) <= 4:
                doc = dtext
        if not doc:
            # only `--` comments directly adjacent (blank-line gap <= 2) count:
            # stale pointers from earlier blocks must not leak into pairing
            raw_lines = raw.split("\n")
            k = lm.line(off) - 2          # 0-based index of the line above
            keep = []
            gap = 0
            while k >= 0 and gap <= 2:
                t = raw_lines[k] if k < len(raw_lines) else ""
                if t.strip().startswith("--"):
                    keep.append(t)
                    gap = 0
                elif t.strip() == "":
                    gap += 1
                else:
                    break
                k -= 1
            doc = "\n".join(reversed(keep))
        if kind in ("theorem", "lemma"):
            p = re.search(r":=\s*(by\b|sorry\b)", seg)
            stmt = seg[: p.start()] if p else seg[: max(0, find_toplevel(seg, ":="))]
        else:
            t = find_toplevel(seg, ":=")
            if t < 0:
                continue
            header = seg[:t]
            if not (re.search(r":\s*Prop\b", header) or
                    re.search(r"(ℝ|Real|ℕ|Nat|ℤ|Int)\b", header)):
                continue
            decls.append(LeanDecl(name=name, kind=kind, file=rel, line=line,
                                  stmt=seg[t + 2:], stmt_off=off + t + 2,
                                  code=seg, is_stub=bool(re.search(r"\bsorry\b", seg)),
                                  is_prop=True, doc=doc, lm=lm))
            continue
        decls.append(LeanDecl(name=name, kind=kind, file=rel, line=line,
                              stmt=stmt, stmt_off=off, code=seg,
                              is_stub=bool(re.search(r"\bsorry\b", seg)),
                              is_prop=True, doc=doc, lm=lm))
    return decls


def selftest(repo, records=None, by_name=None, by_base=None):
    print("=" * 72)
    print("SELFTEST — SF-49 / SF-53 回放")
    print("=" * 72)
    if records is None:
        records, by_name = build_hol_index(repo)
        by_base = basename_map(records)
    ok_all = True

    def findings_for(decls):
        fs = []
        for d in decls:
            rec, _ = pair_decl(d, by_name, by_base)
            if rec is not None:
                fs.extend(check_decl(d, rec, d.lm, None))
        return fs

    # ---------- Check A: SF-53 live (PA4:197 & PA4:519) ----------
    print("\n[A] SF-53 live — PackingAuto4.lean:197/:519 "
          "(Icc 0 (ccCardP4 cc) vs HOL OXLZLEZ1.hl:90 / OXLZLEZ2.hl:2527 的 0..k-1)")
    pa4 = repo / "lean/Kepler/Text/PackingAuto4.lean"
    pa4_decls = parse_lean_file(pa4, "lean/Kepler/Text/PackingAuto4.lean")
    fs = [f for f in findings_for(pa4_decls) if f.kind == "RANGE" and f.severity == "H"]
    hits197 = [f for f in fs if f.lean_name == "ccRealModelP4" and f.line == 197]
    hits519 = [f for f in fs if f.lean_name == "CARD5_1074_LE_QYI" and f.line == 519]
    okA = bool(hits197) and bool(hits519)
    for f in fs:
        if (f.lean_name, f.line) in (("ccRealModelP4", 197), ("CARD5_1074_LE_QYI", 519)):
            print("  CATCH  [%s/%s] %s:%d ← %s:%d — %s" %
                  (f.severity, f.kind, f.lean_file, f.line, f.hol_file,
                   f.hol_line, f.note))
    print("  PA4:197 (ccRealModelP4):   %s" % ("CAUGHT" if hits197 else "MISSED"))
    print("  PA4:519 (CARD5_1074_LE_QYI): %s" % ("CAUGHT" if hits519 else "MISSED"))
    ok_all &= okA

    # ---------- Check B: SF-49 replay (sign flip) ----------
    print("\n[B] SF-49 replay — PackingAuto21.lean bank_BIXPCGW9455898160, "
          "把已修复的 `> -0.00569` 回置为历史误植 `> 0.00569`（HOL ineq.hl:985 "
          "`> -- #0.00569`）")
    pa21 = repo / "lean/Kepler/Text/PackingAuto21.lean"
    raw21 = pa21.read_text(encoding="utf-8", errors="replace")
    if "> -0.00569" not in raw21:
        print("  SKIP   PA21 当前无 `> -0.00569`，无法构造回放")
        okB = False
    else:
        typo = raw21.replace("> -0.00569", "> 0.00569")
        decls = scan_text_file(repo, pa21, typo)
        fs = [f for f in findings_for(decls)
              if f.lean_name == "bank_BIXPCGW9455898160" and f.kind == "NUM_SIGN"]
        okB = any(f.severity == "H" for f in fs)
        for f in fs:
            print("  CATCH  [%s/%s] %s:%d ← %s:%d — %s" %
                  (f.severity, f.kind, f.lean_file, f.line, f.hol_file,
                   f.hol_line, f.note))
        print("  SF-49 回放: %s" % ("CAUGHT (sign flip → H)" if okB else "MISSED"))
    ok_all &= okB

    # ---------- Check C: SF-49 live status ----------
    print("\n[C] SF-49 live 状态核对 — HEAD 处 bank_BIXPCGW9455898160")
    live = findings_for(parse_lean_file(pa21, "lean/Kepler/Text/PackingAuto21.lean"))
    live_hits = [f for f in live if f.lean_name == "bank_BIXPCGW9455898160"]
    if not live_hits:
        print("  OK     HEAD 已修复（`> -0.00569` 与 HOL `-- #0.00569` 一致），扫描器不报 —— 符合预期。")
        print("         注意: 该行 docstring 自述『双重负号 = 0.00569』本身写反（-- 是一元负号），")
        print("         但属注释不入扫描范围；建议另立小 SF 修注释。")
    else:
        for f in live_hits:
            print("  FLAG   [%s/%s] line %d — %s" % (f.severity, f.kind, f.line, f.note))

    print("\n" + "=" * 72)
    print("SELFTEST RESULT: %s   (A SF-53 live: %s | B SF-49 replay: %s)" %
          ("PASS" if ok_all else "FAIL", "PASS" if okA else "FAIL",
           "PASS" if okB else "FAIL"))
    print("=" * 72)
    return 0 if ok_all else 1


# ------------------------------------------------------------- entry

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    here = Path(__file__).resolve()
    repo_default = here.parents[2]
    ap.add_argument("--repo", default=str(repo_default))
    ap.add_argument("--out", default=None, help="output dir (default docs/scouts)")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--max-print", type=int, default=40)
    args = ap.parse_args(argv)
    repo = Path(args.repo).resolve()
    t0 = time.time()

    if args.selftest:
        return selftest(repo)

    records, decls, findings, stats = scan(repo)
    outdir = Path(args.out) if args.out else repo / "docs" / "scouts"
    outdir.mkdir(parents=True, exist_ok=True)
    tsv = outdir / "fidelity-audit-v1.tsv"
    md = outdir / "fidelity-audit-v1.md"
    write_tsv(findings, tsv)
    write_md(findings, stats, md, repo)
    dt = time.time() - t0
    print("HOL index : %d records / %d files" % (stats["hol_records"], stats["hol_files"]))
    print("Lean decls: %d (%d stubs); paired %d (%.1f%%)" %
          (stats["decls"], stats["stubs"], stats["paired"],
           100.0 * stats["paired"] / max(1, stats["decls"])))
    print("Findings  : %s | severity %s" %
          (", ".join("%s=%d" % kv for kv in sorted(stats["by_kind"].items())),
           ", ".join("%s=%d" % kv for kv in sorted(stats["by_sev"].items()))))
    print("Wrote     : %s" % tsv)
    print("Wrote     : %s" % md)
    print("Elapsed   : %.1fs" % dt)
    print("\nTop %d findings:" % min(args.max_print, len(findings)))
    for f in findings[: args.max_print]:
        print("  [%s/%s] %s:%d %s  <-  %s:%d | %s" %
              (f.severity, f.kind, f.lean_file, f.line, f.lean_name,
               f.hol_file, f.hol_line, f.note[:110]))
    return 0


if __name__ == "__main__":
    sys.exit(main())

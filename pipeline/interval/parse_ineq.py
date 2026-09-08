#!/usr/bin/env python3
"""Extract nonlinear-inequality records from Flyspeck HOL Light sources.

Scans (char-level, comment/string/backtick aware) the OCaml record literals
  { idv= "..."; ineq = ...; doc= "..."; tags=[...]; }
in the given .hl files and emits JSON records with bounds, raw HOL body,
tags, and eps.

Stdlib only.  Usage:  python3 pipeline/interval/parse_ineq.py
"""

import json
import os
import re
import sys
import bisect

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))

FILES = [
    "reference/flyspeck/text_formalization/nonlinear/ineq.hl",
    "reference/flyspeck/text_formalization/nonlinear/merge_ineq.hl",
]
OUT_PATH = os.path.join(HERE, "out", "ineqs.json")

FIELD_RE = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*=")
TAG_RE = re.compile(r"(?:\[\s*|;\s*|@\s*|\bthen\s+)([A-Z][A-Za-z0-9_']*)")
EPS_RE = re.compile(r"\bEps\s+([0-9][0-9A-Za-z_.+-]*)")


# ---------------------------------------------------------------- stripping
def strip_comments(text):
    """Blank out OCaml comments (* ... *) (nested-aware, string-aware).

    Comment characters are replaced by spaces (newlines kept) so that all
    offsets and line numbers of the original file are preserved.
    """
    out = list(text)
    n = len(text)
    i = 0
    in_str = False
    while i < n:
        c = text[i]
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "(" and i + 1 < n and text[i + 1] == "*":
            depth = 1
            out[i] = " "
            out[i + 1] = " "
            i += 2
            while i < n and depth > 0:
                c = text[i]
                if c == '"' and i + 1 < n:
                    # string literal inside a comment: skip it wholesale
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
                    continue
                if c == "(" and i + 1 < n and text[i + 1] == "*":
                    depth += 1
                    out[i] = " "
                    out[i + 1] = " "
                    i += 2
                    continue
                if c == "*" and i + 1 < n and text[i + 1] == ")":
                    depth -= 1
                    out[i] = " "
                    out[i + 1] = " "
                    i += 2
                    continue
                if c != "\n":
                    out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def build_mask(text):
    """Classify every char: 0 = code, 1 = inside "string", 2 = inside `quote`."""
    n = len(text)
    mask = bytearray(n)
    state = 0
    i = 0
    while i < n:
        if state == 0:
            c = text[i]
            if c == '"':
                mask[i] = 1
                state = 1
                i += 1
            elif c == "`":
                mask[i] = 2
                state = 2
                i += 1
            else:
                i += 1
        elif state == 1:
            c = text[i]
            mask[i] = 1
            if c == "\\" and i + 1 < n:
                mask[i + 1] = 1
                i += 2
            elif c == '"':
                state = 0
                i += 1
            else:
                i += 1
        else:  # state == 2, backtick quotation
            c = text[i]
            mask[i] = 2
            if c == "`":
                state = 0
            i += 1
    return mask


# ----------------------------------------------------------------- scanning
def find_matching_brace(text, mask, start):
    """start points at '{' in code context; return index of matching '}'."""
    depth = 0
    n = len(text)
    j = start
    while j < n:
        if mask[j] == 0:
            c = text[j]
            if c == "{":
                depth += 1
                j += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    return j
                j += 1
            else:
                j += 1
        else:
            m = mask[j]
            while j < n and mask[j] == m:
                j += 1
    return -1


def split_top_level(text, mask, lo, hi, sep):
    """Split text[lo:hi] at sep chars that sit in code context at bracket
    depth 0 (strings/backticks are opaque via the mask; (), [], {} tracked)."""
    parts = []
    start = lo
    depth = 0
    j = lo
    while j < hi:
        if mask[j] == 0:
            c = text[j]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == sep and depth == 0:
                parts.append((start, j))
                start = j + 1
            j += 1
        else:
            m = mask[j]
            while j < hi and mask[j] == m:
                j += 1
    parts.append((start, hi))
    return parts


def find_matching(text, lo, hi, open_c, close_c):
    """Char-level (no strings inside HOL quotations) matching for [ or ( ."""
    depth = 0
    j = lo
    while j < hi:
        c = text[j]
        if c == open_c:
            depth += 1
        elif c == close_c:
            depth -= 1
            if depth == 0:
                return j
        j += 1
    return -1


def strip_outer_parens(text, mask, a, b):
    """Repeatedly remove balanced outer parentheses from slice [a,b)."""
    for _ in range(10):
        while a < b and text[a].isspace():
            a += 1
        while b > a and text[b - 1].isspace():
            b -= 1
        if a >= b or text[a] != "(" or text[b - 1] != ")":
            break
        depth = 0
        j = a
        ok = False
        while j < b:
            if mask[j] == 0:
                c = text[j]
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                    if depth == 0:
                        ok = j == b - 1
                        break
                j += 1
            else:
                m = mask[j]
                while j < b and mask[j] == m:
                    j += 1
        if not ok:
            break
        a += 1
        b -= 1
    return a, b


def skip_ws(text, a, b):
    while a < b and text[a].isspace():
        a += 1
    return a


def normalize_ws(s):
    return " ".join(s.split())


def decode_ocaml_string(raw):
    """raw includes the surrounding double quotes."""
    body = raw[1:-1]
    out = []
    i = 0
    n = len(body)
    simple = {"n": "\n", "t": "\t", "r": "\r", "b": "\b", '"': '"',
              "\\": "\\", "'": "'", " ": " "}
    while i < n:
        c = body[i]
        if c != "\\":
            out.append(c)
            i += 1
            continue
        i += 1
        if i >= n:
            break
        d = body[i]
        if d in simple:
            out.append(simple[d])
            i += 1
        elif d == "x" and i + 2 < n:
            out.append(chr(int(body[i + 1:i + 3], 16)))
            i += 3
        elif d.isdigit():
            j = i
            while j < n and j < i + 3 and body[j].isdigit():
                j += 1
            out.append(chr(int(body[i:j])))
            i = j
        elif d == "\n":
            # line continuation: skip leading whitespace on next line
            i += 1
            while i < n and body[i] in " \t":
                i += 1
        else:
            out.append(d)
            i += 1
    return "".join(out)


# ------------------------------------------------------------ record fields
def parse_tags_value(text, mask, a, b):
    raw = normalize_ws(text[a:b])
    names = [m.group(1) for m in TAG_RE.finditer(text, a, b)]
    eps = None
    m = EPS_RE.search(text, a, b)
    if m:
        try:
            eps = float(m.group(1).rstrip("."))
        except ValueError:
            eps = None
    return names, eps, raw


def parse_bounds_region(text, lo, hi, notes):
    """Parse '(lo,var,hi); ...' triples from inside the bounds [ ... ]."""
    bounds = []
    # local paren/bracket-aware split on ';'
    parts = []
    start = lo
    depth = 0
    j = lo
    while j < hi:
        c = text[j]
        if c in "([{" :
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ";" and depth == 0:
            parts.append((start, j))
            start = j + 1
        j += 1
    parts.append((start, hi))
    for (a, b) in parts:
        a = skip_ws(text, a, b)
        while b > a and text[b - 1].isspace():
            b -= 1
        if a >= b:
            continue
        if text[a] != "(" or text[b - 1] != ")":
            notes.append("bounds item is not a triple: %r"
                         % normalize_ws(text[a:b]))
            bounds.append({"raw": normalize_ws(text[a:b])})
            continue
        # split at top-level commas
        trip = []
        s = a + 1
        depth = 0
        for k in range(a + 1, b - 1):
            c = text[k]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == "," and depth == 0:
                trip.append((s, k))
                s = k + 1
        trip.append((s, b - 1))
        if len(trip) == 3:
            toks = [normalize_ws(text[u:v]) for (u, v) in trip]
            bounds.append({"lo": toks[0], "var": toks[1], "hi": toks[2]})
        else:
            notes.append("bounds item has %d fields: %r"
                         % (len(trip), normalize_ws(text[a:b])))
            bounds.append({"raw": normalize_ws(text[a:b])})
    return bounds


def parse_ineq_value(text, mask, va, vb):
    """Returns dict with keys: standard(bool), bounds, body_raw, ineq_raw."""
    res = {"kind": "raw", "bounds": [], "body_raw": None, "ineq_raw": None}
    notes = []
    a, b = strip_outer_parens(text, mask, va, vb)
    for _ in range(4):
        a = skip_ws(text, a, b)
        m = re.match(r"(?:[A-Za-z_][A-Za-z0-9_']*\.)?all_forall\b", text[a:b])
        if m and mask[a] == 0:
            a += m.end()
            a, b = strip_outer_parens(text, mask, a, b)
        else:
            break
    a = skip_ws(text, a, b)
    if a < b and text[a] == "`" and mask[a] == 2:
        # backtick quotation: the whole quote is one contiguous mask-2 run
        # (opening backtick ... closing backtick)
        j = a
        while j < vb and mask[j] == 2:
            j += 1
        if j - 1 >= a and text[j - 1] != "`":
            res["ineq_raw"] = normalize_ws(text[va:vb])
            return res
        content_a, content_b = a + 1, j - 1
        m = re.compile(r"\s*(?:\\[^.]*\.|![^.=]*\.)?\s*ineq\b").match(
            text, content_a, content_b)
        if not m:
            res["ineq_raw"] = normalize_ws(text[va:vb])
            return res
        p = m.end()
        p = skip_ws(text, p, content_b)
        if p < content_b and text[p] == "[":
            q = find_matching(text, p, content_b, "[", "]")
            if q != -1:
                res["bounds"] = parse_bounds_region(text, p + 1, q, notes)
                res["kind"] = "bounds"
                res["body_raw"] = normalize_ws(text[q + 1:content_b])
            else:
                res["ineq_raw"] = normalize_ws(text[va:vb])
        else:
            # quotation without a bounds list (functional ineq form)
            res["kind"] = "quote_nobounds"
            res["bounds"] = []
            res["body_raw"] = normalize_ws(text[content_a:content_b])
            notes.append("ineq quotation without bounds list")
        if notes:
            res["notes"] = notes
        return res
    # not a backtick quotation: function application / identifier reference
    res["ineq_raw"] = normalize_ws(text[va:vb])
    return res


# -------------------------------------------------------------- main parser
def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def find_let_binding(text, semis, pos):
    """Name bound by the first `let` of the phrase (since the last ';;')."""
    k = bisect.bisect_left(semis, pos) - 1
    lo = semis[k] + 2 if k >= 0 else 0
    m = re.search(r"\blet\s+([A-Za-z_][A-Za-z0-9_']*)", text[lo:pos])
    return m.group(1) if m else None


def parse_file(relpath):
    path = os.path.join(ROOT, relpath)
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        raw = f.read()
    text = strip_comments(raw)
    mask = build_mask(text)
    n = len(text)

    semis = [i for i in range(n - 1)
             if mask[i] == 0 and mask[i + 1] == 0
             and text[i] == ";" and text[i + 1] == ";"]

    records = []
    leftover = []
    candidates = 0
    i = 0
    while i < n:
        if mask[i] == 0 and text[i] == "{":
            j = find_matching_brace(text, mask, i)
            if j != -1:
                chunks = split_top_level(text, mask, i + 1, j, ";")
                fields = []
                is_record = False
                for (ca, cb) in chunks:
                    m = FIELD_RE.match(text, ca, cb)
                    if m and m.group(1) == "idv":
                        is_record = True
                    fields.append((m.group(1) if m else None, ca, cb,
                                   m.end() if m else ca))
                if is_record:
                    candidates += 1
                    start_line = line_of(text, i)
                    try:
                        rec = {"idv": None, "idv_expr": None,
                               "source_file": relpath,
                               "let_binding": find_let_binding(text, semis, i),
                               "line": start_line,
                               "bounds": [], "body_raw": None,
                               "tags": [], "eps": None,
                               "parse_note": None}
                        notes = []
                        for (name, ca, cb, va) in fields:
                            if name == "idv":
                                a = skip_ws(text, va, cb)
                                if a < cb and text[a] == '"':
                                    k = a + 1
                                    while k < cb:
                                        if text[k] == "\\":
                                            k += 2
                                        elif text[k] == '"':
                                            break
                                        else:
                                            k += 1
                                    rec["idv"] = decode_ocaml_string(
                                        text[a:k + 1])
                                else:
                                    rec["idv_expr"] = normalize_ws(
                                        text[va:cb])
                                    notes.append(
                                        "idv field is an expression, "
                                        "not a string literal")
                            elif name == "ineq":
                                sub = parse_ineq_value(text, mask, va, cb)
                                rec["bounds"] = sub["bounds"]
                                rec["body_raw"] = sub["body_raw"]
                                if sub["kind"] == "raw":
                                    rec["ineq_raw"] = sub["ineq_raw"]
                                    notes.append(
                                        "ineq field is not a literal "
                                        "`ineq [...]' quotation: "
                                        + (sub["ineq_raw"] or ""))
                                if "notes" in sub:
                                    notes.extend(sub["notes"])
                            elif name == "tags":
                                names, eps, traw = parse_tags_value(
                                    text, mask, va, cb)
                                rec["tags"] = names
                                rec["eps"] = eps
                        if notes:
                            rec["parse_note"] = "; ".join(notes)
                        records.append(rec)
                    except Exception as exc:  # noqa: BLE001
                        leftover.append((start_line, repr(exc)))
                    i = j + 1
                    continue
            i += 1
        else:
            i += 1

    # cross-check numbers straight off the raw bytes (as grep would see)
    xcheck = {
        "grep_task_pattern": len(re.findall(r'idv= *"', raw)),
        "grep_lenient": len(re.findall(r'idv *= *"', raw)),
        "grep_lenient_no_comments":
            len(re.findall(r'idv *= *"', text)),
        "record_literals_found": candidates,
        "records_parsed": len(records),
        "leftover_unparsed": leftover,
        "records_with_string_idv":
            sum(1 for r in records if r["idv"] is not None),
    }
    return records, xcheck


def main():
    all_records = []
    per_file = {}
    for rel in FILES:
        recs, xc = parse_file(rel)
        all_records.extend(recs)
        per_file[rel] = xc

    out = {"records": all_records,
           "per_file_counts": {rel: xc["records_parsed"]
                               for rel, xc in per_file.items()}}
    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    with open(OUT_PATH, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)

    print("=== parse_ineq summary ===")
    print("total records: %d" % len(all_records))
    for rel, xc in per_file.items():
        print("file %s" % rel)
        print("  parsed records:            %d" % xc["records_parsed"])
        print("  record literals found:     %d" % xc["record_literals_found"])
        print("  grep 'idv= *\"' (task):     %d" % xc["grep_task_pattern"])
        print("  grep 'idv *= *\"' (lenient):%d" % xc["grep_lenient"])
        print("  lenient grep (comments stripped): %d"
              % xc["grep_lenient_no_comments"])
        print("  records with string idv:   %d" % xc["records_with_string_idv"])
        print("  leftover unparsed:         %d" % len(xc["leftover_unparsed"]))
        for (ln, err) in xc["leftover_unparsed"]:
            print("    leftover at line %d: %s" % (ln, err))
    noted = [r for r in all_records if r.get("parse_note")]
    print("records with parse_note (non-standard fields): %d" % len(noted))
    for r in noted:
        print("  - %s (line %d): %s" % (r["idv"] or r["idv_expr"],
                                        r["line"], r["parse_note"]))
    print("wrote %s" % OUT_PATH)
    leftover_total = sum(len(xc["leftover_unparsed"])
                         for xc in per_file.values())
    if leftover_total != 0:
        print("FAIL: leftover unparsed record literals: %d" % leftover_total)
        return 1
    for rel, xc in per_file.items():
        if xc["records_parsed"] != xc["record_literals_found"]:
            print("FAIL: candidate/parse mismatch for %s" % rel)
            return 1
        if xc["records_with_string_idv"] != xc["grep_lenient_no_comments"]:
            print("WARN: string-idv count != lenient grep for %s (%d vs %d)"
                  % (rel, xc["records_with_string_idv"],
                     xc["grep_lenient_no_comments"]))
    print("OK: all record literals parsed, zero leftover")
    return 0


if __name__ == "__main__":
    sys.exit(main())

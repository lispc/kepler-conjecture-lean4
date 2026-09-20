#!/usr/bin/env python3
"""Generate the six ID lists for the Assembly spine's nonlinearInequalities
interface (P6-E interface-side deliverable).

Reconstructs HOL Light's runtime registry `!Ineq.ineqs` from the Flyspeck
sources and applies, per component, the exact filter rules that build the six
conjuncts of `the_nonlinear_inequalities` (the_main_statement.hl:55-59):

  component                     HOL construction (registry-order filter unless noted)
  ---------------------------   ------------------------------------------------------
  pack_nonlinear_non_ox3q1h     merge_ineq.hl:98-116  Flypaper ∩ {UKBRPFE,BIEFJHU,
                                OXLZLEZ,TSKAJXY} ≠ ∅  ∧  ¬("OXLZLEZ 6346351218" prefix)
  ox3q1h                        merge_ineq.hl:78-92  ids "OXLZLEZ 6346351218 {i} {n}",
                                n ∈ 0..numcases-1 (record count of ineqdata3q1h.hl),
                                i ∈ 0..4, n-major order (definition order, NOT
                                registry order)
  main_nonlinear_terminal_v11   terminal.hl:24-44  tag Main_estimate
  lp_ineqs                      the_main_statement.hl:29-45  (tag Lp | Tablelp |
                                Lp_aux _  ∨  idv = "6170936724")  ∧
                                idv ∉ Tame_lemmas.deprecated_quads
                                (tame_lemmas-compiled.hl:6-13)
  pack_ineq_def_a               YSSKQOY.hl:24-28  Flypaper ∩ {UKBRPFE,WAZLDCD,BIEFJHU}
                                ≠ ∅
  kcblrqc_ineq_def              tame_lemmas-compiled.hl:34-46  (Flypaper ∩ {KCBLRQC}
                                ≠ ∅  ∨  idv ∈ extra_ids)  ∧  idv ∉ deprecated_quads

Registry composition (audit trail):
  * Only `nonlinear/ineq.hl` and `nonlinear/main_estimate_ineq.hl` ever call
    `Ineq.add` (optimize.hl:35 binds `add` but never calls it; prep.hl uses its
    own `Prep.prep_ineqs`, prep.hl:14-16).  Load order in
    build/build.hl:86-87 is ineq.hl BEFORE main_estimate_ineq.hl.
  * `Ineq.add` PREPENDS (ineq.hl:39-42), so the in-memory registry order is
    the reverse of the textual add order, main_estimate records first.
  * Literal records are added by `add { ... }` / `add{ ... }`; `skip { ... }`
    blocks and the commented-out `(* add *)` block (ineq.hl:2620) are NOT in
    the registry.  Programmatic additions (OCaml loops / function
    applications) are expanded mechanically below with source references:
      ineq.hl:495-499   make_F4 loop        16 ids  "ZTGIJCF4 i3 i4 i5 i6 1821661595"
      ineq.hl:845-862   add_QITNPEA1 loop    6 ids  "QITNPEA1 i3 i4 9063653052 A"
      ineq.hl:1563-1577 mk_3q1h_all        230 ids  "OXLZLEZ 6346351218 case r"
      ineq.hl:3334-3339 mk_iqd               6 ids  "181212899 d"
      ineq.hl:3461-3543 iqd                 17 ids  (parsed from source lines)
      ineq.hl:3590-3698 named records        6 ids  i4750199435 ... i2390583444
      main_estimate_ineq.hl:957-963 make_hex_ear loop  35 ids  "7550003505 i j k"
  * Cross-check: the literal-record parse of ineq.hl is validated against
    pipeline/interval/out/ineqs.json (g4e pipeline; 181 records / 177 unique
    ids) — same file, independent parser.

Usage:
  python3 lean/scripts/gen_idlists.py \
      --flyspeck reference/flyspeck/text_formalization \
      --ineqs-json <g4e>/pipeline/interval/out/ineqs.json \
      --out lean/Kepler/Assembly/IdLists.lean

Stdlib only.
"""

import argparse
import json
import os
import re
import sys

# ---------------------------------------------------------------------------
# char-level scanning utilities (comment/string/backtick aware, offsets kept)


def strip_comments(text):
    """Blank nested OCaml comments (* ... *), string-aware; keep offsets."""
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
            out[i] = out[i + 1] = " "
            i += 2
            while i < n and depth > 0:
                c = text[i]
                if c == '"':
                    # string literal inside a comment: skip wholesale
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
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if c == "*" and i + 1 < n and text[i + 1] == ")":
                    depth -= 1
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if out[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def make_mask(text):
    """mask[i] is True when text[i] is inside a string or backtick term."""
    mask = [False] * len(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    break
                j += 1
            for k in range(i, min(j + 1, n)):
                mask[k] = True
            i = j + 1
            continue
        if c == "`":
            j = i + 1
            while j < n and text[j] != "`":
                j += 1
            for k in range(i, min(j + 1, n)):
                mask[k] = True
            i = j + 1
            continue
        i += 1
    return mask


KEYWORD_RE = re.compile(r"\b(add|skip)\b\s*\{|\blet\s+(i[0-9]\w*)\s*=\s*\{")


def iter_block_sites(stripped, mask):
    """Yield (pos_of_open_brace, kind, name) for each record-literal site.

    kind: "add" | "skip" | "let" (name = bound identifier for kind "let").
    Occurrences inside strings/backtick terms are ignored via `mask`.
    """
    for m in KEYWORD_RE.finditer(stripped):
        if mask[m.start()]:
            continue
        brace = stripped.index("{", m.start())
        if m.group(1) is not None:
            yield brace, m.group(1), None
        else:
            yield brace, "let", m.group(2)


def block_extent(stripped, mask, brace):
    """Return end offset (one past the matching '}') of the block at `brace`."""
    depth = 0
    i = brace
    n = len(stripped)
    while i < n:
        if mask[i]:
            i += 1
            continue
        c = stripped[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced brace at %d" % brace)


IDV_RE = re.compile(r'\bidv\s*=\s*"((?:[^"\\]|\\.)*)"')
TAGS_RE = re.compile(r"\btags\s*=")
FLYPAPER_RE = re.compile(r"Flypaper\s*\[([^\]]*)\]")
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
CONSTR_RE = re.compile(r"\b([A-Z][A-Za-z0-9_']*)")
FIELD_RE = re.compile(r"\b(idv|ineq|doc)\s*=")


def parse_block(text):
    """Extract (idv, tag_names, flypaper_args) from a record-literal block.

    Returns idv=None (and empty tags/flypaper) when the idv is not a string
    literal — those are programmatic generator definitions (make_F4 /
    add_QITNPEA1 / mk_3q1h / mk_iqd / iqd) whose tags contain OCaml
    conditionals; they are expanded mechanically elsewhere.
    """
    m = IDV_RE.search(text)
    if not m:
        return None, [], []
    idv = m.group(1).replace('\\"', '"')
    tm = TAGS_RE.search(text)
    if not tm:
        raise ValueError("record block without tags: %r" % (text[:80],))
    # tags value: up to the next record field or end of block
    rest = text[tm.end():]
    fm = FIELD_RE.search(rest)
    value = rest[: fm.start()] if fm else rest
    if "if " in value or "then" in value:
        raise ValueError("conditional tags in literal block: %r" % value[:120])
    flypaper = []
    for g in FLYPAPER_RE.finditer(value):
        flypaper.extend(STRING_RE.findall(g.group(1)))
    flypaper = [s.strip('"') for s in flypaper]
    # keep the constructor name, drop only the argument list (ineqs.json's
    # flattened tags keep "Flypaper" as a name — cross-check needs parity)
    scrubbed = FLYPAPER_RE.sub(" Flypaper ", value)
    scrubbed = STRING_RE.sub(" ", scrubbed)
    names = CONSTR_RE.findall(scrubbed)
    return idv, names, flypaper


# ---------------------------------------------------------------------------
# registry reconstruction


def parse_literal_records(path):
    """Parse one .hl file -> list of events in textual order.

    Each event: dict(pos, kind, idv, tags, flypaper, name, line).
    kind: "add" (in registry), "skip"/"let"/"orphan" (not added here).
    Generator definitions (idv=None) are returned with kind "gendef".
    """
    raw = open(path, encoding="utf-8").read()
    stripped = strip_comments(raw)
    mask = make_mask(stripped)
    events = []
    covered = []
    for brace, kind, name in iter_block_sites(stripped, mask):
        end = block_extent(stripped, mask, brace)
        covered.append((brace, end))
        block = stripped[brace:end]
        idv, tags, flypaper = parse_block(block)
        line = raw.count("\n", 0, brace) + 1
        if idv is None:
            kind = "gendef"
        events.append(dict(pos=brace, kind=kind, idv=idv, tags=tags,
                           flypaper=flypaper, name=name, line=line,
                           src=os.path.basename(path)))
    # orphan literals (e.g. the commented-out `(* add *) {` block at
    # ineq.hl:2620 leaves a bare `{...}` after comment stripping)
    for m in re.finditer(r"\{", stripped):
        if mask[m.start()]:
            continue
        if any(a <= m.start() < b for a, b in covered):
            continue
        # cheap sanity: an orphan record literal has idv and tags fields
        end = block_extent(stripped, mask, m.start())
        block = stripped[m.start():end]
        if IDV_RE.search(block) and TAGS_RE.search(block):
            idv, tags, flypaper = parse_block(block)
            line = raw.count("\n", 0, m.start()) + 1
            events.append(dict(pos=m.start(), kind="orphan", idv=idv,
                               tags=tags, flypaper=flypaper, name=None,
                               line=line, src=os.path.basename(path)))
    events.sort(key=lambda e: e["pos"])
    return events, stripped, mask


def find_pos(stripped, pattern, count=1):
    """Position of a regex match in the stripped source (for add ordering)."""
    ms = list(re.finditer(pattern, stripped))
    if len(ms) != count:
        raise ValueError("pattern %r found %d times, expected %d"
                         % (pattern, len(ms), count))
    return [m.start() for m in ms]


def ineq_hl_programmatic(stripped, num_3q1h):
    """Programmatic additions of ineq.hl, as (pos, [records]) pairs."""
    out = []
    # ineq.hl:488-499 — make_F4 loop: for i3,i4,i5,i6 in 0..1
    recs = []
    for i3 in (0, 1):
        for i4 in (0, 1):
            for i5 in (0, 1):
                for i6 in (0, 1):
                    tags = (["Tex"] if (i3, i4, i5, i6) == (0, 0, 0, 0) else []) + \
                        ["Marchal", "Cfsqp", "Xconvert", "Penalty", "Branching",
                         "Split"]
                    recs.append(dict(
                        idv="ZTGIJCF4 %d %d %d %d 1821661595" % (i3, i4, i5, i6),
                        tags=tags, flypaper=["OXLZLEZ"],
                        gen="ineq.hl:495-499 make_F4 loop"))
    out.append((find_pos(stripped, r"add\(make_F4")[0], recs))
    # ineq.hl:845-862 — add_QITNPEA1 loop: for i3 in 1..2, for i4 in 0..2
    recs = []
    for i3 in (1, 2):
        for i4 in (0, 1, 2):
            tags = (["Tex"] if i3 + i4 == 1 else []) + \
                ["Marchal", "Cfsqp", "Xconvert", "Penalty", "Branching", "Split"]
            recs.append(dict(
                idv="QITNPEA1 %d %d 9063653052 A" % (i3, i4),
                tags=tags, flypaper=["OXLZLEZ"],
                gen="ineq.hl:859-862 add_QITNPEA1 loop"))
    out.append((find_pos(stripped, r"add_QITNPEA1 i3 i4\s+done done")[0], recs))
    # ineq.hl:1563-1577 — mk_3q1h_all: flatten(map mk_3q1hc (0--num-1)),
    # mk_3q1hc r = map (fun c -> mk_3q1h c r) (0--4);  idv = case then r
    recs = []
    for r in range(num_3q1h):
        for case in range(5):
            tags = (["Tex"] if (case, r) == (0, 0) else []) + \
                ["Marchal", "Clusterlp", "Branching"] + \
                (["Xconvert"] if case > 0 else [])
            recs.append(dict(
                idv="OXLZLEZ 6346351218 %d %d" % (case, r),
                tags=tags, flypaper=["OXLZLEZ"],
                gen="ineq.hl:1563-1577 mk_3q1h_all"))
    out.append((find_pos(stripped, r"map add mk_3q1h_all")[0], recs))
    # ineq.hl:3334-3339 — six mk_iqd adds, ids "181212899 d", d = 0..5
    poss = find_pos(stripped, r"add \(mk_iqd", count=6)
    for d, pos in enumerate(poss):
        tags = ["Cfsqp", "Xconvert", "Lp"] + (["Derived"] if d > 0 else ["Tex"])
        out.append((pos, [dict(idv="181212899 %d" % d, tags=tags, flypaper=[],
                               gen="ineq.hl:3334-3339 mk_iqd")]))
    # ineq.hl:3461-3543 — seventeen iqd adds, parsed mechanically
    recs = []
    iqd_re = re.compile(r'add\s*\(\s*iqd\s+"([^"]+)"\s+"[^"]+"\s+(true|false)')
    for m in iqd_re.finditer(stripped):
        sym = m.group(2) == "true"
        tags = ["Cfsqp", "Xconvert", "Lp"] + (["Lpsymmetry"] if sym else [])
        recs.append((m.start(), dict(idv=m.group(1), tags=tags, flypaper=[],
                                     gen="ineq.hl:3461-3543 iqd")))
    if len(recs) != 17:
        raise ValueError("expected 17 iqd adds, found %d" % len(recs))
    out.extend((pos, [r]) for pos, r in recs)
    return out


def main_estimate_programmatic(stripped):
    """Programmatic additions of main_estimate_ineq.hl (hex_ear loop)."""
    # main_estimate_ineq.hl:957-963 — for i1=0..4, i2=i1..4, i3=i2..4
    recs = []
    for i1 in range(5):
        for i2 in range(i1, 5):
            for i3 in range(i2, 5):
                recs.append(dict(
                    idv="7550003505 %d %d %d" % (i1, i2, i3),
                    tags=["Main_estimate", "Cfsqp", "Xconvert", "Penalty"],
                    flypaper=["LIAULBV"],
                    gen="main_estimate_ineq.hl:957-963 make_hex_ear loop"))
    return [(find_pos(stripped, r"add \(make_hex_ear i1 i2 i3\)")[0], recs)]


def build_registry(ineq_path, me_path, num_3q1h):
    """Reconstruct `!Ineq.ineqs` in in-memory (prepend) order."""
    ineq_events, ineq_stripped, _ = parse_literal_records(ineq_path)
    me_events, me_stripped, _ = parse_literal_records(me_path)

    def assemble(events, programmatic):
        adds = [(e["pos"], [e]) for e in events if e["kind"] == "add"]
        named = {e["name"]: e for e in events
                 if e["kind"] == "let" and e["idv"] is not None}
        return adds, named, programmatic

    adds_i, named_i, prog_i = assemble(ineq_events,
                                       ineq_hl_programmatic(ineq_stripped,
                                                            num_3q1h))
    adds_m, named_m, prog_m = assemble(me_events,
                                       main_estimate_programmatic(me_stripped))
    if named_m:
        raise ValueError("unexpected named records in main_estimate_ineq.hl")

    # named adds: `add i4750199435;;` etc. at their own positions
    for m in re.finditer(r"\badd\s+(i[0-9]\w*)\s*;;", ineq_stripped):
        name = m.group(1)
        if name not in named_i:
            raise ValueError("named add without definition: %s" % name)
        adds_i.append((m.start(), [named_i[name]]))

    def textual_order(adds, prog):
        seq = sorted(adds + prog, key=lambda p: p[0])
        out = []
        for _, recs in seq:
            out.extend(recs)
        return out

    ineq_order = textual_order(adds_i, prog_i)       # textual add order
    me_order = textual_order(adds_m, prog_m)
    # Ineq.add prepends; main_estimate_ineq.hl loads after ineq.hl
    # (build/build.hl:86-87), so its records sit at the head of the registry.
    registry = list(reversed(me_order)) + list(reversed(ineq_order))
    return registry, ineq_events, me_events


# ---------------------------------------------------------------------------
# six component rules (HOL sources quoted per rule)

OX_PREFIX = "OXLZLEZ 6346351218"


def parse_string_list(path, decl_re):
    """Parse an OCaml string-list declaration, e.g. deprecated_quads."""
    text = strip_comments(open(path, encoding="utf-8").read())
    m = re.search(decl_re, text, re.S)
    if not m:
        raise ValueError("declaration not found in %s: %s" % (path, decl_re))
    return [s.strip('"') for s in STRING_RE.findall(m.group(1))]


def component_lists(registry, tame_lemmas_path, num_3q1h):
    deprecated = parse_string_list(
        tame_lemmas_path, r"let deprecated_quads = \[(.*?)\]")
    quad_idv = parse_string_list(
        tame_lemmas_path, r"let quad_idv = \[(.*?)\]")
    extra_ids = parse_string_list(
        tame_lemmas_path, r"let extra_ids = \[(.*?)\] @ quad_idv")
    extra_ids = extra_ids + quad_idv
    if len(deprecated) != 6 or len(quad_idv) != 17 or len(extra_ids) != 20:
        raise ValueError("tame_lemmas parse off: %d/%d/%d"
                         % (len(deprecated), len(quad_idv), len(extra_ids)))

    def flypaper_hit(rec, names):
        return not set(rec["flypaper"]).isdisjoint(names)

    lists = {}
    # merge_ineq.hl:98-116
    lists["pack_nonlinear_non_ox3q1h"] = [
        r["idv"] for r in registry
        if flypaper_hit(r, {"UKBRPFE", "BIEFJHU", "OXLZLEZ", "TSKAJXY"})
        and not r["idv"].startswith(OX_PREFIX)]
    # merge_ineq.hl:78-92 — definition order (n-major, i-minor), NOT registry
    lists["ox3q1h"] = ["%s %d %d" % (OX_PREFIX, i, n)
                       for n in range(num_3q1h) for i in range(5)]
    # terminal.hl:24-44
    lists["main_nonlinear_terminal_v11"] = [
        r["idv"] for r in registry if "Main_estimate" in r["tags"]]
    # the_main_statement.hl:29-45
    lists["lp_ineqs"] = [
        r["idv"] for r in registry
        if r["idv"] not in deprecated
        and (not {"Lp", "Tablelp", "Lp_aux"}.isdisjoint(r["tags"])
             or r["idv"] == "6170936724")]
    # YSSKQOY.hl:24-28
    lists["pack_ineq_def_a"] = [
        r["idv"] for r in registry
        if flypaper_hit(r, {"UKBRPFE", "WAZLDCD", "BIEFJHU"})]
    # tame_lemmas-compiled.hl:34-46
    lists["kcblrqc_ineq_def"] = [
        r["idv"] for r in registry
        if r["idv"] not in deprecated
        and ("KCBLRQC" in r["flypaper"] or r["idv"] in extra_ids)]
    return lists, deprecated, extra_ids


# ---------------------------------------------------------------------------
# validation


def cross_check_json(registry, ineq_events, json_path):
    """Validate the ineq.hl literal parse against the g4e pipeline JSON."""
    data = json.load(open(json_path, encoding="utf-8"))
    recs = [r for r in data["records"]
            if r["source_file"].endswith("nonlinear/ineq.hl")]
    json_ids = [r["idv"] for r in recs if r["idv"] is not None]
    mine = [e for e in ineq_events if e["idv"] is not None]
    mine_ids = [e["idv"] for e in mine]
    report = []
    if set(json_ids) != set(mine_ids):
        only_json = sorted(set(json_ids) - set(mine_ids))
        only_mine = sorted(set(mine_ids) - set(json_ids))
        raise ValueError("ineq.hl literal-id mismatch vs ineqs.json: "
                         "only_json=%s only_mine=%s" % (only_json, only_mine))
    report.append("ineq.hl literal ids = ineqs.json ids "
                  "(%d unique, incl. skip/let/orphan blocks)"
                  % len(set(json_ids)))
    # flattened tag-name comparison
    by_id = {}
    for e in mine:
        by_id.setdefault(e["idv"], set(e["tags"]))
    bad = []
    for r in recs:
        if r["idv"] is None:
            continue
        jt = set(r["tags"])
        mt = by_id.get(r["idv"], set())
        if jt != mt:
            bad.append((r["idv"], sorted(jt - mt), sorted(mt - jt)))
    if bad:
        raise ValueError("tag-name mismatch vs ineqs.json: %s" % bad[:5])
    report.append("tag names match ineqs.json for all %d shared ids"
                  % len(set(json_ids)))
    # every JSON id that is added must be in the registry
    reg_ids = {r["idv"] for r in registry}
    skipped = [e["idv"] for e in ineq_events
               if e["kind"] in ("skip", "orphan", "gendef")]
    missing = [i for i in set(json_ids)
               if i not in reg_ids and i not in skipped]
    if missing:
        raise ValueError("registry missing non-skipped ids: %s" % missing)
    report.append("all non-skip/orphan ineqs.json ids are in the registry")
    return report


def validate(registry, lists, num_3q1h, mk_all_path, deprecated):
    report = []
    reg_ids = [r["idv"] for r in registry]
    dup = sorted({i for i in reg_ids if reg_ids.count(i) > 1})
    report.append("registry size %d (ineq.hl + main_estimate_ineq.hl); "
                  "duplicate idvs: %s" % (len(reg_ids), dup or "none"))
    # terminal.hl's hd(getexact t) re-resolution is the identity iff unique
    main = lists["main_nonlinear_terminal_v11"]
    if len(set(main)) != len(main):
        raise ValueError("main_nonlinear_terminal_v11 has duplicate ids")
    ox = lists["ox3q1h"]
    if len(ox) != 5 * num_3q1h:
        raise ValueError("ox3q1h count off")
    if not set(ox).issubset(set(reg_ids)):
        raise ValueError("ox3q1h ids missing from registry")
    if set(ox) & set(lists["pack_nonlinear_non_ox3q1h"]):
        raise ValueError("ox3q1h prefix exclusion broken")
    if "6170936724" not in lists["lp_ineqs"]:
        raise ValueError("6170936724 special case missing from lp_ineqs")
    report.append("ox3q1h = 5 x %d = %d ids, all present in registry, "
                  "disjoint from pack_nonlinear_non_ox3q1h"
                  % (num_3q1h, len(ox)))
    report.append('"6170936724" present in lp_ineqs via the ineq_ids '
                  "special case (its tags carry no Lp/Tablelp/Lp_aux)")
    # deprecated_quads exclusion must be non-vacuous: the deprecated ids
    # that would otherwise enter lp_ineqs / kcblrqc_ineq_def
    dep_lp = [r["idv"] for r in registry
              if r["idv"] in deprecated
              and not {"Lp", "Tablelp", "Lp_aux"}.isdisjoint(r["tags"])]
    if any(d in lists["lp_ineqs"] for d in deprecated):
        raise ValueError("deprecated id leaked into lp_ineqs")
    if any(d in lists["kcblrqc_ineq_def"] for d in deprecated):
        raise ValueError("deprecated id leaked into kcblrqc_ineq_def")
    report.append("deprecated_quads exclusion is non-vacuous: %d deprecated "
                  "ids carry Lp/Tablelp tags and are excluded from lp_ineqs: "
                  "%s" % (len(dep_lp), dep_lp))
    # external anchor: mk_all_ineq.hl:119-125 hardcodes kcblrqc_ineq_s
    # (the 28 ids the nonlinear_imp_the_nonlinear_inequalities proof uses)
    hardcoded = parse_string_list(mk_all_path, r"let kcblrqc_ineq_s =\s*\[(.*?)\]")
    filt = set(lists["kcblrqc_ineq_def"])
    if set(hardcoded) != filt:
        raise ValueError(
            "kcblrqc filter result != mk_all_ineq.hl hardcoded kcblrqc_ineq_s: "
            "only_filter=%s only_hardcoded=%s"
            % (sorted(filt - set(hardcoded)), sorted(set(hardcoded) - filt)))
    report.append("kcblrqc_ineq_def filter result = mk_all_ineq.hl:119-125 "
                  "hardcoded kcblrqc_ineq_s (%d ids, set equality)"
                  % len(hardcoded))
    return report


def count_3q1h_records(path):
    """`List.length Ineqdata3q1h.records` = |raw_nonlindatah| (line 542)."""
    text = strip_comments(open(path, encoding="utf-8").read())
    m = re.search(r"let raw_nonlindatah = \[(.*?)\]\s*;;", text, re.S)
    if not m:
        raise ValueError("raw_nonlindatah not found")
    heads = re.findall(r"\[\s*\[\s*`#[\d.]+`\s*\]", m.group(1))
    return len(heads)


# ---------------------------------------------------------------------------
# Lean emission

HEADER = """/-
  Kepler/Assembly/IdLists — `nonlinearInequalities` 接口六 ID 清单数据
  （P6-E 接口侧收尾件，{date}）。

  **本文件由 `lean/scripts/gen_idlists.py` 生成，请勿手改。**
  数据源与规则版本见脚本 docstring；再生成命令：

    python3 lean/scripts/gen_idlists.py \\
        --flyspeck reference/flyspeck/text_formalization \\
        --ineqs-json <g4e>/pipeline/interval/out/ineqs.json \\
        --out lean/Kepler/Assembly/IdLists.lean

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  `the_nonlinear_inequalities`（the_main_statement.hl:55-59）的六分量，
  每分量 = 生成式合取的 ID 清单（Assembly.lean:146-161 §2a 的已批准折算：
  ID 清单（数据）+ `AllCertified` 量化命题）。

  清单口径（HOL 构造规则逐条翻译，折算登记 docs/statement-fidelity.md 附录）：
{rules_doc}
  顺序说明：除 ox3q1h 外五清单按 HOL 注册表内存序（`Ineq.add` 前插，
  ineq.hl:39-42；载入序 build/build.hl:86-87）——与 HOL `filter (!Ineq.ineqs)`
  的合取顺序逐项对应；ox3q1h 按其定义 `ox3q1h_term()` 的 n 主序
  （merge_ineq.hl:89-91）。顺序无语义影响（合取/全称量化对排列封闭），
  保留它只为逐项对照可审计。
-/

namespace Kepler.Assembly

"""

RULES_DOC = """  - `packNonlinearNonOx3q1hIds`：merge_ineq.hl:98-116，
    Flypaper ∩ {{UKBRPFE,BIEFJHU,OXLZLEZ,TSKAJXY}} ≠ ∅ 且 idv 不带
    "OXLZLEZ 6346351218" 前缀（{c_pack} 条）；
  - `ox3q1hIds`：merge_ineq.hl:78-92，ineqdata3q1h.hl 的 {n3q1h} 条 record
    × 5 支 = {c_ox} 条（"OXLZLEZ 6346351218 i n"，i ∈ 0..4，n ∈ 0..{n3q1h_max}）；
  - `mainNonlinearTerminalV11Ids`：terminal.hl:24-44，Main_estimate 标签
    （{c_main} 条；含 main_estimate_ineq.hl:957-963 hex_ear 循环 35 条）；
  - `lpIneqsIds`：the_main_statement.hl:29-45，Lp/Tablelp/Lp_aux 标签或
    idv = "6170936724"，剔除 Tame_lemmas.deprecated_quads 6 条（{c_lp} 条）；
  - `packIneqDefAIds`：YSSKQOY.hl:24-28，Flypaper ∩ {{UKBRPFE,WAZLDCD,BIEFJHU}}
    ≠ ∅（{c_pa} 条）；
  - `kcblrqcIneqDefIds`：tame_lemmas-compiled.hl:34-46，Flypaper ∩ {{KCBLRQC}}
    ≠ ∅ 或 idv ∈ extra_ids（3 + quad_idv 17），剔除 deprecated_quads（{c_kc} 条）。
"""

DEF_DOC = {
    "pack_nonlinear_non_ox3q1h":
        "HOL `pack_nonlinear_non_ox3q1h`（merge_ineq.hl:118-134）分量清单。",
    "ox3q1h":
        "HOL `ox3q1h`（merge_ineq.hl:90-92）分量清单（定义序，n 主 i 次）。",
    "main_nonlinear_terminal_v11":
        "HOL `main_nonlinear_terminal_v11`（terminal.hl:37）分量清单。",
    "lp_ineqs":
        "HOL `lp_ineqs`（the_main_statement.hl:29-45）分量清单。",
    "pack_ineq_def_a":
        "HOL `pack_ineq_def_a`（YSSKQOY.hl:30-31）分量清单。",
    "kcblrqc_ineq_def":
        "HOL `kcblrqc_ineq_def`（tame_lemmas-compiled.hl:45-46）分量清单。",
}

LEAN_NAME = {
    "pack_nonlinear_non_ox3q1h": "packNonlinearNonOx3q1hIds",
    "ox3q1h": "ox3q1hIds",
    "main_nonlinear_terminal_v11": "mainNonlinearTerminalV11Ids",
    "lp_ineqs": "lpIneqsIds",
    "pack_ineq_def_a": "packIneqDefAIds",
    "kcblrqc_ineq_def": "kcblrqcIneqDefIds",
}

ASSEMBLY_PLACEHOLDER = {
    "pack_nonlinear_non_ox3q1h": "idsPackNonlinearNonOx3q1h",
    "ox3q1h": "idsOx3q1h",
    "main_nonlinear_terminal_v11": "idsMainNonlinearTerminalV11",
    "lp_ineqs": "idsLpIneqs",
    "pack_ineq_def_a": "idsPackIneqDefA",
    "kcblrqc_ineq_def": "idsKcblrqcIneqDef",
}

ORDER = ["pack_nonlinear_non_ox3q1h", "ox3q1h", "main_nonlinear_terminal_v11",
         "lp_ineqs", "pack_ineq_def_a", "kcblrqc_ineq_def"]


def mem_proof(list_name, ids, target):
    """Positional List.Mem proof script (kernel-friendly; no string reduction)."""
    if target not in ids:
        raise ValueError(target)
    return ("by\n  unfold %s\n  "
            "repeat (first | exact List.Mem.head _ | apply List.Mem.tail)"
            % list_name)


def emit_lean(lists, num_3q1h, date):
    rules = RULES_DOC.format(
        c_pack=len(lists["pack_nonlinear_non_ox3q1h"]),
        n3q1h=num_3q1h, n3q1h_max=num_3q1h - 1,
        c_ox=len(lists["ox3q1h"]),
        c_main=len(lists["main_nonlinear_terminal_v11"]),
        c_lp=len(lists["lp_ineqs"]),
        c_pa=len(lists["pack_ineq_def_a"]),
        c_kc=len(lists["kcblrqc_ineq_def"]))
    out = [HEADER.format(date=date, rules_doc=rules)]
    for key in ORDER:
        name = LEAN_NAME[key]
        ids = lists[key]
        out.append("/-- %s 对应 Assembly.lean 占位 `%s`（:%d）。 -/\n"
                   % (DEF_DOC[key], ASSEMBLY_PLACEHOLDER[key],
                      dict(zip(ORDER, [171, 173, 175, 177, 179, 181]))[key]))
        out.append("def %s : List String :=\n  [" % name)
        out.append(",\n  ".join('"%s"' % i for i in ids))
        out.append("]\n\n")
        out.append("-- 生成期条数钉死（内核 `rfl` 可判）。\n")
        out.append("set_option maxRecDepth 2048 in\n")
        out.append("theorem %s_length : %s.length = %d := rfl\n\n"
                   % (name, name, len(ids)))
    names = [LEAN_NAME[k] for k in ORDER]
    nails = (mem_proof("lpIneqsIds", lists["lp_ineqs"], "6170936724"),
             mem_proof("ox3q1hIds", lists["ox3q1h"],
                       "OXLZLEZ 6346351218 0 0"),
             mem_proof("kcblrqcIneqDefIds", lists["kcblrqc_ineq_def"],
                       "JNTEFVP 1"))
    out.append("""/-! ## 接线示范（P6-E 接口侧；**不改 Assembly.lean 本体**）

`TheNonlinearInequalities`（Assembly.lean:190-193）填入六清单后的展开形态。
按 IneqPilot.lean 先例，本数据文件不 import `Kepler.Assembly`
（避免为纯数据拉起整条装配链构建）；下面两个定义是 Assembly.lean:165-168
`CertifiedIneqHolds` / `AllCertified` 的逐字镜像，仅用于展示展开形态。
接线时（G4 粘合量产）把六个清单常量代入 Assembly.lean:171-183 的对应
PLACEHOLDER 字段，并将 `CertifiedIneqHolds` 填实为按 id 查表展开
（量产样板 = IneqPilot.lean `certifiedIneqHolds_pilot`）。 -/

/-- Assembly.lean:165 占位语义的本地镜像（填实后按 id 查表展开为字面量化
不等式命题，由 G4 内核证书闭合）。 -/
def CertifiedIneqHoldsMirror (_id : String) : Prop := True

/-- Assembly.lean:168 注册表量化的本地镜像。 -/
def AllCertifiedMirror (ids : List String) : Prop :=
  ∀ id ∈ ids, CertifiedIneqHoldsMirror id

/-- **填入后展开形态**：`TheNonlinearInequalities` = 六分量 `AllCertified` 合取
（Assembly.lean:190-193；`LpIneqs` = 第四分量，Assembly.lean:186）。 -/
def TheNonlinearInequalitiesFilled : Prop :=
  AllCertifiedMirror %s ∧ AllCertifiedMirror %s ∧
    AllCertifiedMirror %s ∧ AllCertifiedMirror %s ∧
    AllCertifiedMirror %s ∧ AllCertifiedMirror %s

/-- 清单上的量化逐点展开（注册表量化的定义等价值）。 -/
example : AllCertifiedMirror lpIneqsIds ↔
    ∀ id ∈ lpIneqsIds, CertifiedIneqHoldsMirror id := Iff.rfl

/-- 占位语义下填入形态可闭合（`True` 占位逐点平凡）；`CertifiedIneqHolds`
填实后此定理由 G4 证书逐条替换。 -/
theorem theNonlinearInequalitiesFilled_placeholder :
    TheNonlinearInequalitiesFilled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro _ _ <;> exact True.intro

/-- **清单 = 查表定义域** 不变量（IneqPilot.lean:72-76 警告的 else-True 静默
退化防线）：查表定义域 = 六清单并集；`CertifiedIneqHolds` 填实时其查表分支
必须覆盖此定义域的每个键（分量间有重叠——lp_ineqs 与 main/kcblrqc 共享若干
id——查表按键覆盖即可，重复键无语义影响；无 import 的纯数据文件不提供
`List.eraseDup`，去重留给接线方）。 -/
def certLookupDomain : List String :=
  %s ++ %s ++ %s ++ %s ++ %s ++ %s

-- 生成期特例钉子（位置式成员证明，内核可判、零新增公理——String 的 BEq
-- 内核归约不走 `decide`，故成员证明按位置构造）：`"6170936724"` 特例进
-- lp_ineqs；ox3q1h 首支 / kcblrqc 末支在列。
-- 负向钉子（deprecated_quads 六条不进 lp_ineqs / kcblrqc_ineq_def、ox3q1h
-- 230 条与 pack_nonlinear_non_ox3q1h 的前缀不交性）由生成期 assert 钉死
-- （gen_idlists.py `validate`），不写成 Lean example。
example : "6170936724" ∈ lpIneqsIds := %s
example : "OXLZLEZ 6346351218 0 0" ∈ ox3q1hIds := %s
example : "JNTEFVP 1" ∈ kcblrqcIneqDefIds := %s

end Kepler.Assembly
""" % tuple(names + names + list(nails)))
    return "".join(out)


# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--flyspeck", default="reference/flyspeck/text_formalization")
    ap.add_argument("--ineqs-json",
                    default="/home/scroll/repos/kepler-g4e/pipeline/interval/"
                            "out/ineqs.json")
    ap.add_argument("--out", default="lean/Kepler/Assembly/IdLists.lean")
    args = ap.parse_args()

    import datetime
    import os
    fs = args.flyspeck
    ineq_path = os.path.join(fs, "nonlinear/ineq.hl")
    me_path = os.path.join(fs, "nonlinear/main_estimate_ineq.hl")
    d3q1h_path = os.path.join(fs, "nonlinear/ineqdata3q1h.hl")
    tame_path = os.path.join(fs, "tame/ssreflect/tame_lemmas-compiled.hl")
    mk_all_path = os.path.join(fs, "nonlinear/mk_all_ineq.hl")

    num_3q1h = count_3q1h_records(d3q1h_path)
    print("ineqdata3q1h.hl raw_nonlindatah records: %d" % num_3q1h)

    registry, ineq_events, _ = build_registry(ineq_path, me_path, num_3q1h)
    lists, deprecated, extra_ids = component_lists(registry, tame_path,
                                                   num_3q1h)

    print("== generation-time validation ==")
    for line in cross_check_json(registry, ineq_events, args.ineqs_json):
        print("  [json]", line)
    for line in validate(registry, lists, num_3q1h, mk_all_path, deprecated):
        print("  [rule]", line)
    print("  deprecated_quads (%d): %s" % (len(deprecated), deprecated))

    print("== component counts ==")
    total = 0
    for key in ORDER:
        n = len(lists[key])
        total += n
        print("  %-28s %4d" % (key, n))
    print("  %-28s %4d" % ("TOTAL (with cross-component overlap)", total))
    union = set().union(*(set(lists[k]) for k in ORDER))
    print("  %-28s %4d" % ("union (deduped)", len(union)))

    # HOL-side count comments where they exist:
    # merge_ineq.hl:22-24 states "5*46 inequalities ... conjunction of these
    # 230 inequalities" for ox3q1h — align with that.
    assert len(lists["ox3q1h"]) == 230, \
        "ox3q1h != 230 contradicts merge_ineq.hl:22-24"
    print("  [HOL] ox3q1h = 230 aligns with merge_ineq.hl:22-24 comment "
          "(5*46); other components have no HOL count comments — measured "
          "values recorded above.")

    # spot-check material: first/last/median of each list with source line
    print("== spot-check samples (id <- source) ==")
    by_id = {}
    for r in registry:
        by_id.setdefault(r["idv"], r)
    for key in ORDER:
        ids = lists[key]
        for probe in (ids[0], ids[len(ids) // 2], ids[-1]):
            src = by_id.get(probe)
            where = ("%s:%s" % (src["src"], src["line"])) \
                if src and "line" in src \
                else (src["gen"] if src else "<generated>")
            print("  %-28s %-30s <- %s" % (key, probe, where))

    out = emit_lean(lists, num_3q1h, datetime.date.today().isoformat())
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(out)
    print("wrote %s (%d bytes)" % (args.out, len(out)))


if __name__ == "__main__":
    sys.exit(main())

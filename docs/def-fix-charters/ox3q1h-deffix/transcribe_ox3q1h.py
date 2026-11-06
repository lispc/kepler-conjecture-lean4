#!/usr/bin/env python3
"""Mechanical transcriber: HOL `ox3q1h` (ineqdata3q1h.hl) -> Lean `ox3q1hP25`.

Source of truth (read-only):
  reference/flyspeck/text_formalization/nonlinear/ineqdata3q1h.hl
    :265-541  `raw_nonlindatah`  (46 records x 11 fields)
    :131-263  `mk_irecord` / `mkpath` / `template` / `templateB` / `mk_ineq`
  reference/flyspeck/text_formalization/nonlinear/merge_ineq.hl
    :22-30    "the 5*46 inequalities ... merged into ox3q1h_merge (13 vars)"
    :78-92    `ox`/`ox_conj`/`ox3q1h_term` construction (record-major, case-minor)
  reference/flyspeck/text_formalization/nonlinear/ineq.hl
    :1563-1578 `add3q1h` registration (idv = "OXLZLEZ 6346351218 <case> <rec>")

Outputs (all under --out):
  PackingAuto25.mod.lean : full modified file (docstring + explicit def body)
  manifest.json          : per-item canonical tuple + sha256 + exact Lean line
  table.md               : 230-row correspondence table
  canonical_items.txt    : one canonical tuple per line (recomputable hashes)
  checks.log             : structural / prep-dump cross-check log
  charter_fence.txt      : exact -*-/+ lines of the file diff (for charter 2.1)

No hand-written inequality.  Every one of the 230 is produced by the code
below from the HL literal; the script asserts the HL shape before emitting.

Usage:
  python3 -I transcribe_ox3q1h.py --repo /path/to/repo --out /path/to/out
"""
import argparse
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

# --------------------------------------------------------------------------
# 1. Parse `raw_nonlindatah`
# --------------------------------------------------------------------------

TERM_RE = re.compile(r"`([^`]*)`")


def extract_raw_blob(text: str) -> str:
    i = text.index("let raw_nonlindatah =")
    j = text.index(";;", i)
    blob = text[i:j]
    # sanity: after the opening bracket, every non-space char must be part of
    # a backtick term, a bracket, or a semicolon.
    k = blob.index("[")
    residue = blob[k:]
    residue = TERM_RE.sub("", residue)
    residue = re.sub(r"[\[\];]", "", residue)
    if residue.strip():
        raise SystemExit(f"unparsed residue in raw_nonlindatah: {residue[:80]!r}")
    return blob


def tokenize(blob: str):
    toks = []
    pos = 0
    pat = re.compile(r"`([^`]*)`|(\[|\])|(;)")
    for m in pat.finditer(blob):
        if m.start(0) < pos:
            continue
        pos = m.end(0)
        if m.group(1) is not None:
            toks.append(("T", m.group(1).strip()))
        elif m.group(2):
            toks.append((m.group(2), m.group(2)))
        else:
            toks.append((";", ";"))
    return toks


def parse_nested(toks, k):
    assert toks[k][0] == "[", toks[k]
    k += 1
    out = []
    while toks[k][0] != "]":
        if toks[k][0] == "[":
            v, k = parse_nested(toks, k)
            out.append(v)
        elif toks[k][0] == ";":
            k += 1
        else:
            out.append(toks[k][1])
            k += 1
    return out, k + 1


def parse_term(s: str) -> str:
    s = s.strip()
    neg = False
    if s.startswith("--"):
        neg = True
        s = s[2:].strip()
    if s.startswith("#"):
        s = s[1:]
    if not re.fullmatch(r"\d+(?:\.\d+)?", s):
        raise SystemExit(f"bad HL decimal term: {s!r}")
    return ("-" + s) if neg else s


def parse_intterm(s: str) -> int:
    v = parse_term(s)
    f = Fraction(v)
    if f.denominator != 1:
        raise SystemExit(f"expected integer HL term, got {s!r}")
    return int(f)


def parse_records(repo: Path):
    src = repo / "reference/flyspeck/text_formalization/nonlinear/ineqdata3q1h.hl"
    text = src.read_text()
    blob = extract_raw_blob(text)
    toks = tokenize(blob)
    k = next(n for n, t in enumerate(toks) if t[0] == "[")
    raw, _ = parse_nested(toks, k)
    if len(raw) != 46:
        raise SystemExit(f"expected 46 records, got {len(raw)}")
    recs = []
    for n, r in enumerate(raw):
        if len(r) != 11:
            raise SystemExit(f"record {n}: expected 11 fields, got {len(r)}")
        case = parse_intterm(r[0][0])
        if case not in (1, 2, 3, 4):
            raise SystemExit(f"record {n}: bad caseno {case}")
        lin = [parse_term(x) for x in r[1]]
        if len(lin) != 14:
            raise SystemExit(f"record {n}: lindata len {len(lin)} != 14")
        branches = []
        for b in r[2:7]:
            vals = [parse_intterm(x) for x in b]
            if any(v not in (0, 1) for v in vals):
                raise SystemExit(f"record {n}: branch bit not 0/1: {vals}")
            branches.append(vals)
        nums = []
        for d in r[7:]:
            vals = [parse_term(x) for x in d]
            if len(vals) != 7:
                raise SystemExit(f"record {n}: numerical len {len(vals)} != 7")
            nums.append(vals)
        # mk_irecord: (eps,(a,b1,c1,d1),(a,b2,c2,d2),(a,b3,c3,d3),(a,b4,c4,d4))
        eps, a = lin[0], lin[1]
        coefs = [(lin[2 + 3 * i], lin[3 + 3 * i], lin[4 + 3 * i]) for i in range(4)]
        recs.append(dict(rec=n, case=case, eps=eps, a=a, coefs=coefs,
                         branches=branches, numerics=nums))
    return recs


# --------------------------------------------------------------------------
# 2. Symbolic endpoints: linear forms c + c0*h0 + cp*hplus + cm*hminus
# --------------------------------------------------------------------------

def L(const=0, h0=0, hp=0, hm=0):
    return (Fraction(const), Fraction(h0), Fraction(hp), Fraction(hm))


def ladd(x, y):
    return tuple(a + b for a, b in zip(x, y))


def lsub(x, y):
    return tuple(a - b for a, b in zip(x, y))


def lscale(x, k):
    return tuple(a * Fraction(k) for a in x)


def lmid(x, y):
    return lscale(ladd(x, y), Fraction(1, 2))


H0 = L(h0=2)
HPLUS = L(hp=2)
HMINUS = L(hm=2)
TWO = L(2)


Y1DOM = {1: (H0, HPLUS), 2: (H0, HPLUS), 3: (HMINUS, H0), 4: (HMINUS, H0)}
Y4DOM = {1: (HMINUS, H0), 2: (H0, HPLUS), 3: (HMINUS, H0), 4: (H0, HPLUS)}


def path_apply(interval, bits):
    lo, hi = interval
    for bit in bits:
        mid = lmid(lo, hi)
        if bit == 0:
            hi = mid
        else:
            lo = mid
    return lo, hi


def frac_str(f: Fraction) -> str:
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def render_lin(e) -> str:
    const, c0, cp, cm = e
    terms = []
    for coeff, sym in ((c0, "h0"), (cp, "hplus"), (cm, "hminus")):
        if coeff != 0:
            terms.append((coeff, sym))
    if const != 0 or not terms:
        terms.append((const, None))
    out = ""
    for i, (coeff, sym) in enumerate(terms):
        neg = coeff < 0
        a = abs(coeff)
        if sym is None:
            core = str(a.numerator) if a.denominator == 1 else f"{a.numerator} / {a.denominator}"
        elif a == 1:
            core = sym
        elif a.denominator == 1:
            core = f"{a.numerator} * {sym}"
        else:
            core = f"{a.numerator} * {sym} / {a.denominator}"
        if i == 0:
            out += ("-" if neg else "") + core
        else:
            out += (" - " if neg else " + ") + core
    return out


# --------------------------------------------------------------------------
# 3. Build the 230 canonical items
# --------------------------------------------------------------------------

def lit(s: str) -> str:
    """Lean literal, parenthesised when negative."""
    return f"({s})" if s.startswith("-") else s


def build_items(recs):
    items = []
    for r in recs:
        n = r["rec"]
        # ---- case 0: templateB (constant compatibility) ----
        y1lo, y1hi = path_apply(Y1DOM[r["case"]], r["branches"][0])
        a = r["a"]
        b = [r["coefs"][i][0] for i in range(4)]
        c = [r["coefs"][i][1] for i in range(4)]
        d = [r["coefs"][i][2] for i in range(4)]
        body0 = (
            f"2 * Real.pi * {lit(a)}"
            f" + ({' + '.join(lit(x) for x in b)}) * y1"
            f" + 2 * ({lit(c[0])} + {lit(c[1])}) * y12"
            f" + 2 * ({lit(c[1])} + {lit(c[2])}) * y23"
            f" + 2 * ({lit(c[2])} + {lit(c[3])}) * y34"
            f" + 2 * ({lit(c[3])} + {lit(c[0])}) * y41"
            f" + ({' + '.join(lit(x) for x in d)}) < 0"
        )
        box0 = [(y1lo, "y1", y1hi), (TWO, "y12", HMINUS),
                (TWO, "y23", HMINUS), (TWO, "y34", HMINUS),
                (TWO, "y41", HMINUS)]
        items.append(dict(rec=n, case=0, kind="templateB", vars=[v for _, v, _ in box0],
                          box=box0, a=a, b=b, c=c, d=d, w=1, m=0, body=body0))

        # ---- cases 1..4: template ----
        for case in (1, 2, 3, 4):
            y1lo, y1hi = path_apply(Y1DOM[r["case"]], r["branches"][0])
            if case == 1:
                y4base = Y4DOM[r["case"]]
            else:
                y4base = (TWO, HMINUS)
            y4lo, y4hi = path_apply(y4base, r["branches"][case])
            box = [(y1lo, "y1", y1hi), (TWO, "y2", HMINUS),
                   (TWO, "y3", HMINUS), (y4lo, "y4", y4hi),
                   (TWO, "y5", HMINUS), (TWO, "y6", HMINUS)]
            a = r["a"]
            bb, cc, dd = r["coefs"][case - 1]
            w = 2 if case == 1 else 1
            m = w - 1
            if case == 1:
                prefix = ("gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2"
                          " + (bump (y1 / 2) - bump (y4 / 2))")
            else:
                # HOL: / &1 + &0 * beta_bump_force_y ; arithmetic-normalised
                prefix = "gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun"
            body = (
                f"{prefix}"
                f" + {lit(a)} * dihY y1 y2 y3 y4 y5 y6"
                f" + {lit(bb)} * y1"
                f" + {lit(cc)} * (y2 + y3 + y5 + y6)"
                f" + {lit(dd)} > 0"
            )
            items.append(dict(rec=n, case=case, kind="template", vars=[v for _, v, _ in box],
                              box=box, a=a, b=[bb], c=[cc], d=[dd], w=w, m=m, body=body))
    if len(items) != 230:
        raise SystemExit(f"expected 230 items, got {len(items)}")
    return items


def render_item(it) -> str:
    vars_ = " ".join(it["vars"])
    hyps = []
    for lo, var, hi in it["box"]:
        hyps.append(f"({render_lin(lo)}) ≤ {var}")
        hyps.append(f"{var} ≤ ({render_lin(hi)})")
    return "  (∀ " + vars_ + " : ℝ, " + " → ".join(hyps) + " → " + it["body"] + ")"


def norm_lit(s: str) -> str:
    """Exact rational canonical form of a decimal literal."""
    return frac_str(Fraction(s))


def canonical(it) -> str:
    box = ";".join(
        f"{v}:{','.join(frac_str(x) for x in lo)}>{','.join(frac_str(x) for x in hi)}"
        for lo, v, hi in it["box"])
    if it["kind"] == "templateB":
        body = ("templateB|a=%s|b=%s|c=%s|d=%s"
                % (norm_lit(it["a"]), ",".join(norm_lit(x) for x in it["b"]),
                   ",".join(norm_lit(x) for x in it["c"]), ",".join(norm_lit(x) for x in it["d"])))
    else:
        body = ("template|a=%s|b=%s|c=%s|d=%s|w=%d|m=%d"
                % (norm_lit(it["a"]), norm_lit(it["b"][0]), norm_lit(it["c"][0]),
                   norm_lit(it["d"][0]), it["w"], it["m"]))
    return f"case={it['case']}|rec={it['rec']}|vars={','.join(it['vars'])}|box={box}|body={body}"


def sha256(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------
# 4. Independent prep.hl x-space dump cross-check (boxes + coefficients)
# --------------------------------------------------------------------------

class ExprParser:
    """Exact rational evaluator for prep bound expressions.

    Grammar: e := t (('+'|'-') t)* ; t := f (('*'|'/') f)* ;
             f := ['-'] (num | 'hminus' | '(' e ')')
    num is `&2`, `#2.0`, `2.01`, `2`.
    """

    TOK = re.compile(r"\s*(&|#)?(\d+(?:\.\d+)?|hminus|[()+\-*/])")

    def __init__(self, s, env):
        self.toks = []
        pos = 0
        while pos < len(s):
            m = self.TOK.match(s, pos)
            if not m:
                if s[pos:].strip() == "":
                    break
                raise ValueError(f"bad prep expr char at {pos}: {s[pos:pos+20]!r}")
            pos = m.end()
            pre, tok = m.group(1), m.group(2)
            if pre in ("&", "#"):
                pre = ""
            if tok == "hminus":
                self.toks.append(("num", env["hminus"]))
            elif re.fullmatch(r"\d+(?:\.\d+)?", tok):
                if "." in tok:
                    a, b = tok.split(".")
                    val = Fraction(int(a + b), 10 ** len(b))
                else:
                    val = Fraction(int(tok))
                self.toks.append(("num", val))
            else:
                self.toks.append((tok, tok))
        self.i = 0
        self.env = env
        self.v = self.parse_e()

    def peek(self):
        return self.toks[self.i][0] if self.i < len(self.toks) else None

    def eat(self, kind):
        if self.peek() != kind:
            raise ValueError(f"expected {kind}, got {self.peek()}")
        self.i += 1

    def parse_e(self):
        v = self.parse_t()
        while self.peek() in ("+", "-"):
            op = self.peek()
            self.i += 1
            w = self.parse_t()
            v = v + w if op == "+" else v - w
        return v

    def parse_t(self):
        v = self.parse_f()
        while self.peek() in ("*", "/"):
            op = self.peek()
            self.i += 1
            w = self.parse_f()
            v = v * w if op == "*" else v / w
        return v

    def parse_f(self):
        neg = False
        if self.peek() == "-":
            neg = True
            self.i += 1
        if self.peek() == "num":
            v = self.toks[self.i][1]
            self.i += 1
        elif self.peek() == "(":
            self.i += 1
            v = self.parse_e()
            self.eat(")")
        else:
            raise ValueError(f"bad factor at {self.i}: {self.toks[self.i:]}")
        return -v if neg else v


def eval_prep(s, env):
    p = ExprParser(s, env)
    if p.i != len(p.toks):
        raise ValueError(f"trailing tokens in {s!r}")
    return p.v


def eval_lin(e, env):
    return e[0] + e[1] * env["h0"] + e[2] * env["hplus"] + e[3] * env["hminus"]


def prep_crosscheck(items, repo: Path, log):
    dump = repo / "pipeline/interval/out/ineqs_prep.json"
    if not dump.exists():
        log("PREP-DUMP: missing, skipped")
        return False
    data = json.loads(dump.read_text())
    ox = [r for r in data["records"] if "6346351218" in (r.get("idv") or "")]
    if len(ox) != 230:
        log(f"PREP-DUMP: expected 230 records, got {len(ox)}")
        return False
    by_id = {}
    for r in ox:
        m = re.search(r"6346351218 (\d+) (\d+)", r["idv"])
        by_id[(int(m.group(1)), int(m.group(2)))] = r
    envs = [
        {"h0": Fraction(126, 100), "hplus": Fraction(13254, 10000), "hminus": Fraction(120, 100)},
        {"h0": Fraction(126, 100), "hplus": Fraction(13254, 10000), "hminus": Fraction(125, 100)},
        {"h0": Fraction(126, 100), "hplus": Fraction(13254, 10000), "hminus": Fraction(130, 100)},
    ]
    box_bad = []
    coef_bad = []
    for it in items:
        r = by_id.get((it["case"], it["rec"]))
        if r is None:
            box_bad.append((it["rec"], it["case"], "missing prep record"))
            continue
        bounds = r["bounds"]
        # case 0 prep uses x1..x5 as the y variables directly, x6 fixed 1;
        # cases 1..4 prep uses x_i = y_i^2.
        if it["case"] == 0:
            if len(it["box"]) != 5 or len(bounds) != 6:
                box_bad.append((it["rec"], 0, "unexpected bound counts"))
                continue
            pairs = [(it["box"][i], bounds[i]) for i in range(5)]
            def ours(lo, hi, env):
                return eval_lin(lo, env), eval_lin(hi, env)
        else:
            if len(it["box"]) != 6 or len(bounds) != 6:
                box_bad.append((it["rec"], it["case"], "unexpected bound counts"))
                continue
            pairs = [(it["box"][i], bounds[i]) for i in range(6)]
            def ours(lo, hi, env):
                a, b = eval_lin(lo, env), eval_lin(hi, env)
                return a * a, b * b
        for pos, ((lo, var, hi), bnd) in enumerate(pairs):
            if bnd["var"] != ("x%d" % (pos + 1)):
                box_bad.append((it["rec"], it["case"], f"var order {bnd['var']}"))
                break
            for env in envs:
                olo, ohi = ours(lo, hi, env)
                plo, phi = eval_prep(bnd["lo"], env), eval_prep(bnd["hi"], env)
                if (olo, ohi) != (plo, phi):
                    box_bad.append((it["rec"], it["case"],
                                    f"{var}: ours ({olo},{ohi}) prep ({plo},{phi})"))
                    break
            else:
                continue
            break
        # coefficient literal presence (sign orientation: prep negates >0 cases)
        body = r["body_raw"] or ""
        occ = []
        for m in re.finditer(r"#(\d+(?:\.\d+)?)", body):
            pre = body[max(0, m.start() - 8):m.start()]
            neg = bool(re.search(r"--\s*\(?\s*$", pre))
            occ.append((m.group(1), neg))
        if it["kind"] == "templateB":
            coefs = [it["a"]] + it["b"] + it["c"] + it["d"]
            flip = False
        else:
            coefs = [it["a"], it["b"][0], it["c"][0], it["d"][0]]
            flip = True
        for co in coefs:
            if co in ("0", "0.0", "-0", "-0.0"):
                continue
            neg = co.startswith("-")
            want = (co.lstrip("-"), (not neg) if flip else neg)
            if want not in occ:
                coef_bad.append((it["rec"], it["case"], co, want))
    log(f"PREP-DUMP: boxes {'OK' if not box_bad else 'FAIL'} ({len(box_bad)} bad)")
    for x in box_bad[:10]:
        log(f"  BOX-BAD {x}")
    log(f"PREP-DUMP: coefficients {'OK' if not coef_bad else 'FAIL'} ({len(coef_bad)} bad)")
    for x in coef_bad[:10]:
        log(f"  COEF-BAD {x}")
    return not box_bad and not coef_bad


# --------------------------------------------------------------------------
# 5. Emit the modified Lean file
# --------------------------------------------------------------------------

OLD_DOC_TAIL = "ported elsewhere.  NEEDS: exact Oxl_def.hl body. -/"
NEW_DOC_TAIL = (
    "ported elsewhere.  DEF-FIX 2026-11-06: body replaced by the explicit\n"
    "conjunction of the 230 `mk_ineq` terms generated from\n"
    "`ineqdata3q1h.hl:265-541` (46 records × 5 branches) via `merge_ineq.hl:78-92`;\n"
    "charter `docs/def-fix-charters/ox3q1h-deffix/`. -/"
)
OLD_HDR_LINE = "      `n = 4` conjunct; PackagingAuto3 has it only inline),"
NEW_HDR_LINE = (
    "      `n = 4` conjunct; PackagingAuto3 has it only inline; DEF-FIX\n"
    "      2026-11-06 made the body explicit — see `ox3q1hP25` below),"
)
OLD_DEF = "def ox3q1hP25 : Prop := sorry"


def emit_file(src_text, items):
    if src_text.count(OLD_DOC_TAIL) != 1:
        raise SystemExit("docstring tail not found exactly once")
    if src_text.count(OLD_HDR_LINE) != 1:
        raise SystemExit("header note line not found exactly once")
    if src_text.count(OLD_DEF) != 1:
        raise SystemExit("def line not found exactly once")
    lines = ["def ox3q1hP25 : Prop :="]
    for idx, it in enumerate(items):
        line = render_item(it)
        if idx != len(items) - 1:
            line += " ∧"
        lines.append(line)
    new_def = "\n".join(lines)
    out = src_text.replace(OLD_DOC_TAIL, NEW_DOC_TAIL)
    out = out.replace(OLD_HDR_LINE, NEW_HDR_LINE)
    out = out.replace(OLD_DEF, new_def)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)

    log_lines = []
    def log(s):
        print(s)
        log_lines.append(s)

    recs = parse_records(repo)
    log(f"HL: raw_nonlindatah records = {len(recs)}")
    log(f"HL: lindata lens = {sorted(set(1 + 1 + len([x for c in r['coefs'] for x in c]) for r in recs))}")
    log(f"HL: cases = {sorted(set(r['case'] for r in recs))}")
    log(f"HL: branch lists: {[len(b) for r in recs for b in r['branches']]}")

    items = build_items(recs)
    log(f"ITEMS: total = {len(items)} (records {len(recs)} x 5)")
    assert all(it["case"] == 0 or it["w"] in (1, 2) for it in items)

    src = repo / "lean/Kepler/Text/PackingAuto25.lean"
    src_text = src.read_text()
    mod_text = emit_file(src_text, items)
    (out / "PackingAuto25.mod.lean").write_text(mod_text)

    manifest = []
    canon_lines = []
    for idx, it in enumerate(items):
        c = canonical(it)
        h = sha256(c)
        canon_lines.append(f"{idx}\t{it['case']}\t{it['rec']}\t{h}\t{c}")
        manifest.append(dict(
            idx=idx, record=it["rec"], case=it["case"],
            hol_id=f"OXLZLEZ 6346351218 {it['case']} {it['rec']}",
            vars=it["vars"],
            box=[dict(var=v, lo=[frac_str(x) for x in lo], hi=[frac_str(x) for x in hi])
                 for lo, v, hi in it["box"]],
            kind=it["kind"],
            a=it["a"], b=it["b"], c=it["c"], d=it["d"], w=it["w"], m=it["m"],
            body=it["body"], lean=render_item(it), sha256=h,
        ))
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")
    (out / "canonical_items.txt").write_text("\n".join(canon_lines) + "\n")

    # 230-row table
    rows = ["| # | HOL id | box (y-space) | body sha256 (first 16) |",
            "|---|--------|----------------|--------------------------|"]
    for m in manifest:
        box = ", ".join(f"{b['var']}∈[{render_lin(tuple(Fraction(x) for x in b['lo']))},"
                        f"{render_lin(tuple(Fraction(x) for x in b['hi']))}]" for b in m["box"])
        rows.append(f"| {m['idx']} | `{m['hol_id']}` | {box} | `{m['sha256'][:16]}` |")
    (out / "table.md").write_text("\n".join(rows) + "\n")

    ok = prep_crosscheck(items, repo, log)
    (out / "checks.log").write_text("\n".join(log_lines) + "\n")
    if not ok:
        raise SystemExit("prep cross-check failed")
    log("DONE")


if __name__ == "__main__":
    main()

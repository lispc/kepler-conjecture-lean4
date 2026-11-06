#!/usr/bin/env python3
"""Independent verifier for the generated `ox3q1hP25` body.

Reads the *Lean text* (not the generator's objects), parses every conjunct,
recomputes the canonical tuple + sha256, and compares it with
manifest.json (which in turn was cross-checked against the prep.hl x-space
dump by transcribe_ox3q1h.py).

Usage:
  python3 -I verify_ox3q1h.py --lean out/PackingAuto25.mod.lean \
      --manifest out/manifest.json
"""
import argparse
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

FRAC_RE = re.compile(r"-?\d+(?:\.\d+)?")


def frac(s):
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        return frac(s[1:-1])
    if "/" in s:
        a, b = s.split("/")
        return frac(a) / frac(b)
    return Fraction(s)


class LinParser:
    """Parse the endpoint grammar emitted by the generator:
    e := t (('+'|'-') t)* ; t := f (('*'|'/') f)* ;
    f := ['-'] (num | 'h0' | 'hplus' | 'hminus' | '(' e ')')
    """
    TOK = re.compile(r"\s*(\d+(?:\.\d+)?|h0|hplus|hminus|[()+\-*/])")

    def __init__(self, s):
        self.toks = []
        pos = 0
        while pos < len(s):
            m = self.TOK.match(s, pos)
            if not m:
                if s[pos:].strip() == "":
                    break
                raise ValueError(f"bad endpoint char at {pos}: {s[pos:pos+30]!r}")
            pos = m.end()
            tok = m.group(1)
            if re.fullmatch(r"\d+(?:\.\d+)?", tok):
                if "." in tok:
                    a, b = tok.split(".")
                    self.toks.append(("num", Fraction(int(a + b), 10 ** len(b))))
                else:
                    self.toks.append(("num", Fraction(int(tok))))
            else:
                self.toks.append((tok, tok))
        self.i = 0
        self.v = self.parse_e()
        if self.i != len(self.toks):
            raise ValueError(f"trailing tokens in {s!r}")

    def peek(self):
        return self.toks[self.i][0] if self.i < len(self.toks) else None

    def eat(self, k):
        if self.peek() != k:
            raise ValueError(f"expected {k}, got {self.peek()}")
        self.i += 1

    def parse_e(self):
        v = self.parse_t()
        while self.peek() in ("+", "-"):
            op = self.peek(); self.i += 1
            w = self.parse_t()
            v = v + w if op == "+" else v - w
        return v

    def parse_t(self):
        v = self.parse_f()
        while self.peek() in ("*", "/"):
            op = self.peek(); self.i += 1
            w = self.parse_f()
            v = v * w if op == "*" else v / w
        return v

    def parse_f(self):
        neg = False
        if self.peek() == "-":
            neg = True; self.i += 1
        if self.peek() == "num":
            v = self.toks[self.i][1]; self.i += 1
        elif self.peek() == "(":
            self.i += 1
            v = self.parse_e(); self.eat(")")
        elif self.peek() in ("h0", "hplus", "hminus"):
            v = self.peek(); self.i += 1
        else:
            raise ValueError(f"bad factor at {self.i}: {self.toks[self.i:]}")
        # symbol becomes a 4-tuple at parse_e level; handle via wrapper below
        if isinstance(v, str):
            v = SYM0[v]
        return -v if neg else v


# Lin vectors: (const, h0, hplus, hminus)
SYM0 = {"h0": (Fraction(0), Fraction(1), Fraction(0), Fraction(0)),
        "hplus": (Fraction(0), Fraction(0), Fraction(1), Fraction(0)),
        "hminus": (Fraction(0), Fraction(0), Fraction(0), Fraction(1))}


def lin_fix(v):
    if isinstance(v, str):
        return SYM0[v]
    if isinstance(v, Fraction):
        return (v, Fraction(0), Fraction(0), Fraction(0))
    return v


# wrap the parser's arithmetic to keep vectors
def _vectorize(cls):
    def parse_e(self):
        v = lin_fix(self.parse_t())
        while self.peek() in ("+", "-"):
            op = self.peek(); self.i += 1
            w = lin_fix(self.parse_t())
            v = tuple(a + b for a, b in zip(v, w)) if op == "+" else tuple(a - b for a, b in zip(v, w))
        return v

    def parse_t(self):
        v = lin_fix(self.parse_f())
        while self.peek() in ("*", "/"):
            op = self.peek(); self.i += 1
            w = lin_fix(self.parse_f())
            if op == "*":
                # only scalar * vector is used
                if all(x == 0 for x in w[1:]):
                    v = tuple(a * w[0] for a in v)
                elif all(x == 0 for x in v[1:]):
                    v = tuple(a * v[0] for a in w)
                else:
                    raise ValueError("vector*vector unsupported")
            else:
                if all(x == 0 for x in w[1:]):
                    v = tuple(a / w[0] for a in v)
                else:
                    raise ValueError("vector/vector unsupported")
        return v

    def parse_f(self):
        neg = False
        if self.peek() == "-":
            neg = True; self.i += 1
        if self.peek() == "num":
            v = self.toks[self.i][1]; self.i += 1
        elif self.peek() in ("h0", "hplus", "hminus"):
            v = SYM0[self.peek()]; self.i += 1
        elif self.peek() == "(":
            self.i += 1
            v = self.parse_e(); self.eat(")")
        else:
            raise ValueError(f"bad factor at {self.i}: {self.toks[self.i:]}")
        v = lin_fix(v)
        return tuple(-a for a in v) if neg else v

    cls.parse_e, cls.parse_t, cls.parse_f = parse_e, parse_t, parse_f
    return cls


LinParser = _vectorize(LinParser)


def lif(s):
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        return s[1:-1]
    return s


def parse_lit(s):
    s = s.strip()
    neg = False
    while s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    if s.startswith("-"):
        neg = True; s = s[1:].strip()
    f = frac(s)
    return -f if neg else f


def lit_str(f):
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def canonical(it):
    def fs(x):
        return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
    box = ";".join(f"{v}:{','.join(fs(x) for x in lo)}>{','.join(fs(x) for x in hi)}"
                   for lo, v, hi in it["box"])
    if it["kind"] == "templateB":
        body = "templateB|a=%s|b=%s|c=%s|d=%s" % (it["a"], ",".join(it["b"]), ",".join(it["c"]), ",".join(it["d"]))
    else:
        body = "template|a=%s|b=%s|c=%s|d=%s|w=%d|m=%d" % (it["a"], it["b"][0], it["c"][0], it["d"][0], it["w"], it["m"])
    return f"case={it['case']}|rec={it['rec']}|vars={','.join(it['vars'])}|box={box}|body={body}"


def parse_line(line):
    s = line.strip()
    if s.endswith(" ∧"):
        s = s[:-2]
    if not (s.startswith("(∀ ") and s.endswith(")")):
        raise ValueError(f"not a conjunct line: {s[:80]!r}")
    s = s[1:-1]
    head, rest = s.split(" : ℝ, ", 1)
    assert head.startswith("∀ ")
    vars_ = head[2:].split()
    parts = rest.split(" → ")
    body = parts[-1]
    hyps = parts[:-1]
    if len(hyps) != 2 * len(vars_):
        raise ValueError(f"hyp count {len(hyps)} != 2*{len(vars_)}")
    box = []
    for k, v in enumerate(vars_):
        h1, h2 = hyps[2 * k].strip(), hyps[2 * k + 1].strip()
        m1 = re.fullmatch(r"(.+?) ≤ " + re.escape(v), h1)
        m2 = re.fullmatch(re.escape(v) + r" ≤ (.+)", h2)
        if not m1 or not m2:
            raise ValueError(f"bad hyp pair: {h1!r} / {h2!r}")
        lo = tuple(LinParser(m1.group(1)).v)
        hi = tuple(LinParser(m2.group(1)).v)
        box.append((lo, v, hi))
    if "2 * Real.pi" in body:
        kind = "templateB"
        # 2 * Real.pi * A + (B) * y1 + 2 * (C0 + C1) * y12 ... + (D) < 0
        m = re.fullmatch(
            r"2 \* Real\.pi \* (.+?) \+ \((.+?)\) \* y1 "
            r"\+ 2 \* \((.+?)\) \* y12 \+ 2 \* \((.+?)\) \* y23 "
            r"\+ 2 \* \((.+?)\) \* y34 \+ 2 \* \((.+?)\) \* y41 "
            r"\+ \((.+?)\) < 0", body)
        if not m:
            raise ValueError(f"templateB body parse failed: {body[:200]!r}")
        a = parse_lit(m.group(1))
        # split a parenthesised sum of literals at top level
        def split_sum(x):
            out, depth, cur = [], 0, ""
            for ch in x:
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                if ch == "+" and depth == 0:
                    out.append(cur); cur = ""
                else:
                    cur += ch
            out.append(cur)
            return [parse_lit(y) for y in out]
        b = split_sum(m.group(2))
        pairs = [split_sum(m.group(i)) for i in (3, 4, 5, 6)]
        c = [pairs[0][0], pairs[0][1], pairs[1][1], pairs[2][1]]
        # c0 from pair12, c1 from pair12; c2 from pair23; c3 from pair34
        c = [pairs[0][0], pairs[0][1], pairs[1][1], pairs[2][1]]
        d = split_sum(m.group(7))
        it = dict(case=None, rec=None, vars=vars_, box=box, kind=kind,
                  a=lit_str(a), b=[lit_str(x) for x in b], c=[lit_str(x) for x in c],
                  d=[lit_str(x) for x in d], w=1, m=0)
        return it
    else:
        # gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun [/ 2] [+ (bump...)] + A * dihY ... + B * y1 + C * (...) + D > 0
        m = re.fullmatch(
            r"gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun( / 2)?( \+ \(bump \(y1 / 2\) - bump \(y4 / 2\)\))?"
            r" \+ (.+?) \* dihY y1 y2 y3 y4 y5 y6 \+ (.+?) \* y1 "
            r"\+ (.+?) \* \(y2 \+ y3 \+ y5 \+ y6\) \+ (.+?) > 0", body)
        if not m:
            raise ValueError(f"template body parse failed: {body[:200]!r}")
        w = 2 if m.group(1) else 1
        mval = 1 if m.group(2) else 0
        it = dict(case=None, rec=None, vars=vars_, box=box, kind="template",
                  a=lit_str(parse_lit(m.group(3))), b=[lit_str(parse_lit(m.group(4)))],
                  c=[lit_str(parse_lit(m.group(5)))], d=[lit_str(parse_lit(m.group(6)))],
                  w=w, m=mval)
        return it


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True)
    ap.add_argument("--manifest", required=True)
    args = ap.parse_args()
    lines = Path(args.lean).read_text().splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith("def ox3q1hP25 : Prop :="))
    body = []
    k = i + 1
    while k < len(lines):
        l = lines[k]
        if l.startswith("  (∀ "):
            body.append(l); k += 1
        else:
            break
    man = json.loads(Path(args.manifest).read_text())
    print(f"VERIFY: conjunct lines = {len(body)}")
    assert len(body) == 230 == len(man)
    bad = []
    for idx, (line, m) in enumerate(zip(body, man)):
        try:
            it = parse_line(line)
        except Exception as e:
            bad.append((idx, f"parse: {e}")); continue
        it["case"] = m["case"]; it["rec"] = m["record"]
        c = canonical(it)
        h = hashlib.sha256(c.encode()).hexdigest()
        if h != m["sha256"]:
            bad.append((idx, f"hash {h[:12]} != {m['sha256'][:12]}"))
            continue
        # exact semantic fields
        if (it["vars"] != m["vars"] or it["kind"] != m["kind"] or
                Fraction(it["a"]) != Fraction(m["a"]) or
                [Fraction(x) for x in it["b"]] != [Fraction(x) for x in m["b"]] or
                [Fraction(x) for x in it["c"]] != [Fraction(x) for x in m["c"]] or
                [Fraction(x) for x in it["d"]] != [Fraction(x) for x in m["d"]] or
                it["w"] != m["w"] or it["m"] != m["m"]):
            bad.append((idx, "semantic field mismatch"))
            continue
        # box compare
        for (lo, v, hi), bm in zip(it["box"], m["box"]):
            if v != bm["var"]:
                bad.append((idx, f"var {v} != {bm['var']}")); break
            if [str(x.numerator) + ("/" + str(x.denominator) if x.denominator != 1 else "") for x in lo] != bm["lo"] or \
               [str(x.numerator) + ("/" + str(x.denominator) if x.denominator != 1 else "") for x in hi] != bm["hi"]:
                bad.append((idx, f"box mismatch {v}")); break
        else:
            continue
    print(f"VERIFY: matched = {230 - len(bad)} / 230")
    for b in bad[:20]:
        print("  BAD", b)
    if bad:
        sys.exit(1)
    print("VERIFY: 230/230 conjuncts match manifest (sha256 re-derived from Lean text)")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Phase 4: parse Flyspeck HOL-Light real-arithmetic `body_raw` terms into ASTs.

Reads  pipeline/interval/out/ineqs.json  (produced by parse_ineq.py) and
writes pipeline/interval/out/ineqs_ast.json.  Each record gains "body_ast"
(and "domain_raw" when a leading `ineq (dom) (...)` wrapper was present).

Term grammar (precedence climbing, loosest -> tightest):
    ==>   right      <=>  right
    \/    right      /\   right
    = < > <= >=     non-chain
    + -   left       * /  left
    pow   right
    application  f a b   (tightest after prefix)
    prefix --  (real negation, tightest),  prefix ~  (bool negation)

Atoms:  &n (integer-as-real, e.g. &2),  #d.ddd (decimal, kept verbatim),
bare numerals (rare, e.g. tame_table_d 2 1), identifiers
(y1..y9 / x1..x6 -> "var", other bare identifiers -> "const").

Extras found in the data and handled:
    !x1 ... xn. body       universal quantifier -> {"forall": ...}
    let v = e in body      HOL let-binding      -> {"let": ...}
    // ...                 source annotations (// Tan[Pi-2.089]^2) and
                           commented-out disjuncts; stripped heuristically
                           before parsing (see strip_slash_comments).
A leading `ineq (dom) body` wrapper (optionally under a quantifier) is
peeled off: dom is kept as raw text in "domain_raw".

Validation (all must pass, exit 0):
  * every non-null body_raw parses; failures print idv + token context
  * token round-trip: re-serialized AST (parens recorded during parsing)
    must equal the parsed token list exactly
  * applied function symbols and constants are tabulated with counts.

Stdlib only.  Usage:  python3 pipeline/interval/parse_body.py
"""

import json
import os
import re
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
IN_PATH = os.path.join(HERE, "out", "ineqs.json")
OUT_PATH = os.path.join(HERE, "out", "ineqs_ast.json")

# ------------------------------------------------------------------ lexing
TOKEN_RE = re.compile(
    r"&[0-9]+"                              # &n   integer-as-real
    r"|#[0-9]+(?:\.[0-9]+)?"                # #d(.d+)?  decimal literal
    r"|[0-9]+\.[0-9]+"                      # bare decimal (only in // annots)
    r"|[0-9]+"                              # bare integer
    r"|[A-Za-z_][A-Za-z0-9_']*"
    r"|==>|<=>|<=|>=|<|>|=|\+|\*"
    r"|\\/|/\\|//|/|--|-|~|\(|\)|\.|\[|\]|\^"
)

PREC = {  # infix op -> (precedence, associativity: l/r/n)
    "==>": (1, "r"), "<=>": (2, "r"),
    "\\/": (3, "r"), "/\\": (4, "r"),
    "=": (5, "n"), "<": (5, "n"), ">": (5, "n"),
    "<=": (5, "n"), ">=": (5, "n"),
    "+": (6, "l"), "-": (6, "l"),
    "*": (7, "l"), "/": (7, "l"),
    "pow": (9, "r"),
}
UNARY_MIN = 8                    # prefix -- / ~ operand includes pow
RESERVED = {"let", "in", "then", "else"}
ANNOT_TOKENS = {"Tan", "Pi", "[", "]", "^"}      # only inside // regions
ANNOT_DROP = ANNOT_TOKENS | {"-", "+"}
NUM_RE = re.compile(r"^(?:&|#)?[0-9]")
VAR_RE = re.compile(r"^[xy][0-9]+$")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
QUANT_RE = re.compile(
    r"^\s*!\s*((?:[A-Za-z_][A-Za-z0-9_']*\s+)*[A-Za-z_][A-Za-z0-9_']*)"
    r"\s*\.\s*(.*)$", re.S)
INEQ_RE = re.compile(r"^\s*ineq\s*\(")


class ParseError(Exception):
    pass


def tokenize(text, where):
    toks, i, n = [], 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        m = TOKEN_RE.match(text, i)
        if not m:
            raise ParseError("%s: cannot tokenize at ...%s"
                             % (where, text[max(0, i - 30):i + 20]))
        toks.append(m.group(0))
        i = m.end()
    return toks


# ------------------------------------------------- // annotation stripping
def next_slash_or_end(toks, i):
    j = i + 1
    while j < len(toks) and toks[j] != "\\/":
        j += 1
    return j


def slash_comment_candidates(toks, i):
    """Candidate token lists with the `//` region at index i removed.

    Two flavours occur in the data:
    * annotation between `(` and real content:  `// Tan[Pi-2.089]^2`
      (region up to the next `\/` contains [ ] ^ Tan Pi); drop only the
      annotation tokens.
    * commented-out disjunct / clause:  `A \/ // B \/ C`  ->  `A \/ C`.
    Cutting is verified by re-parsing the whole body, so a region that is
    neither of the above (mid-group comment) is recovered by trying every
    possible cut point, shortest surviving tail first.
    """
    j = next_slash_or_end(toks, i)
    n = len(toks)
    if any(t in ANNOT_TOKENS for t in toks[i + 1:j]):
        k = i + 1
        while k < n and (toks[k] in ANNOT_DROP or NUM_RE.match(toks[k])):
            k += 1
        return [toks[:i] + toks[k:]]
    cands = []
    if j < n:
        cands.append(toks[:i] + toks[j + 1:])    # drop region + its `\/`
        cands.append(toks[:i] + toks[j:])        # drop region only
    else:
        cands.append(toks[:i] + toks[j:])        # no `\/`: drop to end
    for k in range(i + 1, n):                    # mid-group comment
        cands.append(toks[:i] + toks[k:])
    return cands


def strip_slash_comments(toks, where):
    """Remove every `//` region; each cut is verified by re-parsing."""
    for idx, t in enumerate(toks):
        if t == "//":
            break
    else:
        return toks, 0
    for cand in slash_comment_candidates(toks, idx):
        try:
            out, ncomm = strip_slash_comments(cand, where)
            parse_tokens(drop_dangling_disj(list(out)), where)
            return out, ncomm + 1
        except (ParseError, RecursionError):
            continue
    raise ParseError("%s: cannot recover // comment region near %r"
                     % (where, " ".join(toks[idx:idx + 8])))


def drop_dangling_disj(toks):
    """Tidy leftovers of comment stripping: `\/ \/', `\/` at either end."""
    changed = True
    while changed:
        changed = False
        while toks and toks[-1] == "\\/":
            toks = toks[:-1]
            changed = True
        if toks and toks[0] == "\\/":
            toks = toks[1:]
            changed = True
        for k in range(len(toks) - 1):
            if toks[k] == "\\/" and toks[k + 1] in ("\\/", ")"):
                del toks[k]
                changed = True
                break
    return toks


# ------------------------------------------------------------------ parser
def parse_tokens(toks, where):
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def advance():
        t = toks[pos[0]]
        pos[0] += 1
        return t

    def err(msg):
        lo = max(0, pos[0] - 5)
        hi = min(len(toks), pos[0] + 5)
        near = " ".join(toks[lo:pos[0]]) + " >>> " + " ".join(toks[pos[0]:hi])
        raise ParseError("%s: %s | near: %s" % (where, msg, near))

    def expect(t):
        if peek() != t:
            err("expected %r, got %r" % (t, peek()))
        return advance()

    def can_start_atom(t):
        if t is None or t == "(":
            return t is not None
        if NUM_RE.match(t):
            return True
        return IDENT_RE.match(t) is not None and t not in RESERVED \
            and t not in PREC

    def parse_expr(min_prec):
        lhs = parse_unary()
        while True:
            t = peek()
            info = PREC.get(t)
            if info is None:
                break
            prec, assoc = info
            if prec < min_prec:
                break
            advance()
            if assoc == "l":
                rhs = parse_expr(prec + 1)
            elif assoc == "r":
                rhs = parse_expr(prec)
            else:  # non-chain comparison
                rhs = parse_expr(prec + 1)
                nt = peek()
                if PREC.get(nt, (0,))[0] == prec:
                    err("chained comparison %r after %r" % (nt, t))
            lhs = {"op": t, "args": [lhs, rhs]}
        return lhs

    def parse_unary():
        t = peek()
        if t == "~":
            advance()
            return {"not": parse_expr(UNARY_MIN)}
        if t == "--":
            advance()
            return {"neg": parse_expr(UNARY_MIN)}
        return parse_app()

    def parse_app():
        node = parse_primary()
        while can_start_atom(peek()):
            arg = parse_primary()
            if "app" in node and isinstance(node["app"], str):
                node = {"app": node["app"], "args": node["args"] + [arg]}
            elif "var" in node or "const" in node:
                node = {"app": node.get("var") or node.get("const"),
                        "args": [arg]}
            else:
                err("cannot apply non-symbol term")
        return node

    def parse_primary():
        t = peek()
        if t is None:
            err("unexpected end of input")
        if t == "(":
            advance()
            inner = parse_expr(1)
            expect(")")
            return {"paren": inner}          # kept for exact round-trip
        if t.startswith("&") and re.match(r"^&[0-9]+$", t):
            advance()
            return {"num": t[1:]}
        if t.startswith("#"):
            advance()
            return {"dec": t[1:]}
        if re.match(r"^[0-9]+$", t):
            advance()
            return {"bnum": t}
        if re.match(r"^[0-9]+\.[0-9]+$", t):
            advance()
            return {"dec": t}
        if t == "let":
            return parse_let()
        if IDENT_RE.match(t):
            advance()
            if t in RESERVED:
                err("unexpected reserved word %r" % t)
            kind = "var" if VAR_RE.match(t) else "const"
            return {kind: t}
        err("unexpected token %r" % t)

    def parse_let():
        advance()                            # `let`
        v = peek()
        if not IDENT_RE.match(v or ""):
            err("expected bound variable name, got %r" % v)
        advance()
        expect("=")
        val = parse_expr(1)
        expect("in")
        body = parse_expr(1)
        return {"let": {"var": v, "val": val, "body": body}}

    def at_top():
        t = peek()
        if t == "let":
            return parse_let()
        return parse_expr(1)

    ast = at_top()
    if peek() is not None:
        err("trailing tokens after end of term")
    return ast


# ---------------------------------------------------------- de Paren / ser
def strip_parens(node):
    if isinstance(node, dict):
        if "paren" in node:
            return strip_parens(node["paren"])
        return {k: strip_parens(v) for k, v in node.items()}
    if isinstance(node, list):
        return [strip_parens(x) for x in node]
    return node


def serialize(node):
    """Exact token-list round-trip (paren nodes preserved)."""
    if "num" in node:
        return ["&" + node["num"]]
    if "bnum" in node:
        return [node["bnum"]]
    if "dec" in node:
        return ["#" + node["dec"]]
    if "var" in node or "const" in node:
        return [node.get("var") or node.get("const")]
    if "neg" in node:
        return ["--"] + serialize(node["neg"])
    if "not" in node:
        return ["~"] + serialize(node["not"])
    if "paren" in node:
        return ["("] + serialize(node["paren"]) + [")"]
    if "app" in node:
        out = [node["app"]]
        for a in node["args"]:
            out += serialize(a)
        return out
    if "op" in node:
        return serialize(node["args"][0]) + [node["op"]] + \
            serialize(node["args"][1])
    if "forall" in node:
        f = node["forall"]
        return ["!"] + list(f["vars"]) + ["."] + serialize(f["body"])
    if "let" in node:
        l = node["let"]
        return ["let", l["var"], "="] + serialize(l["val"]) + \
            ["in"] + serialize(l["body"])
    raise ParseError("cannot serialize node %r" % (node,))


# ------------------------------------------------------------ ineq wrapper
def split_ineq_wrapper(text, where):
    """Peel a leading `ineq (dom) body` -> (dom_raw, body_raw) or None."""
    m = INEQ_RE.match(text)
    if not m:
        return None
    i = m.end() - 1                       # index of the opening '('
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return text[m.end():j].strip(), text[j + 1:].strip()
    raise ParseError("%s: unbalanced parens in ineq-domain wrapper" % where)


# -------------------------------------------------------------- term walks
def walk_syms(node, apps, consts):
    if isinstance(node, dict):
        if "app" in node:
            apps[node["app"]] += 1
            for a in node["args"]:
                walk_syms(a, apps, consts)
            return
        if "const" in node:
            consts[node["const"]] += 1
            return
        if "op" in node:
            for a in node["args"]:
                walk_syms(a, apps, consts)
            return
        if "forall" in node:
            walk_syms(node["forall"]["body"], apps, consts)
            return
        if "let" in node:
            l = node["let"]
            walk_syms(l["val"], apps, consts)
            walk_syms(l["body"], apps, consts)
            return
        for k in ("neg", "not", "paren"):
            if k in node:
                walk_syms(node[k], apps, consts)
                return


def parse_body_raw(raw, where):
    """-> (out_ast, domain_raw_or_None, n_slash_comments)"""
    quant = None
    text = raw
    m = QUANT_RE.match(text)
    if m:
        quant = m.group(1).split()
        text = m.group(2)
    domain = None
    w = split_ineq_wrapper(text, where)
    if w:
        domain, text = w
    toks = tokenize(text, where)
    toks, ncomm = strip_slash_comments(toks, where)
    toks = drop_dangling_disj(toks)
    ast = parse_tokens(toks, where)
    if quant:
        ast = {"forall": {"vars": quant, "body": ast}}
    # exact round-trip check
    expect = (["!"] + quant + ["."] if quant else []) + toks
    got = serialize(ast)
    if got != expect:
        k = next((i for i, (a, b) in enumerate(zip(expect, got))
                  if a != b), min(len(expect), len(got)))
        ctx_e = " ".join(expect[max(0, k - 5):k + 5])
        ctx_g = " ".join(got[max(0, k - 5):k + 5])
        raise ParseError("%s: round-trip mismatch at token %d: "
                         "input ~ %r vs reserialized ~ %r"
                         % (where, k, ctx_e, ctx_g))
    return strip_parens(ast), domain, ncomm


# -------------------------------------------------------------------- main
def main():
    with open(IN_PATH) as f:
        data = json.load(f)
    recs = data["records"]

    out_recs = []
    ok = nulled = nwrap = nquant = nlet = ncomm = 0
    failures, mismatches = [], []
    apps, consts = Counter(), Counter()

    for rec in recs:
        o = dict(rec)
        raw = rec.get("body_raw")
        rid = rec.get("idv") or rec.get("idv_expr") or "<idv?>"
        if not isinstance(raw, str):
            nulled += 1
            out_recs.append(o)
            continue
        try:
            ast, domain, nc = parse_body_raw(raw, rid)
        except (ParseError, RecursionError) as e:
            failures.append((rid, str(e)))
            out_recs.append(o)
            continue
        o["body_ast"] = ast
        if domain is not None:
            o["domain_raw"] = domain
            nwrap += 1
        if "forall" in ast:
            nquant += 1
        if "let" in ast:
            nlet += 1
        ncomm += nc
        walk_syms(ast, apps, consts)
        ok += 1
        out_recs.append(o)

    out = {k: v for k, v in data.items() if k != "records"}
    out["records"] = out_recs
    with open(OUT_PATH, "w") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)

    print("== parse_body.py summary ==")
    print("records total:            %d" % len(recs))
    print("  parsed OK:              %d" % ok)
    print("  null body_raw (skip):   %d" % nulled)
    print("  parse failures:         %d" % len(failures))
    print("ineq-wrapped (domain_raw):%d" % nwrap)
    print("quantified (!vars.):      %d" % nquant)
    print("let-bindings:             %d" % nlet)
    print("// comment regions:       %d" % ncomm)
    for rid, msg in failures:
        print("FAIL %s: %s" % (rid, msg))

    print("applied function symbols: %d distinct, %d uses"
          % (len(apps), sum(apps.values())))
    for name, c in apps.most_common(40):
        print("  app   %-34s %d" % (name, c))
    print("constants:                %d distinct, %d uses"
          % (len(consts), sum(consts.values())))
    for name, c in sorted(consts.items()):
        print("  const %-34s %d" % (name, c))

    if failures or len(out_recs) - nulled != ok:
        print("VALIDATION FAILED")
        return 1
    print("VALIDATION OK (%d parsed, 0 round-trip mismatches)" % ok)
    return 0


if __name__ == "__main__":
    sys.exit(main())

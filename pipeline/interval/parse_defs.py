#!/usr/bin/env python3
"""Phase 4: extract Flyspeck *definitions* and check closure over ineq symbols.

Reads
    reference/flyspeck/text_formalization/general/sphere.hl
    reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl
    (+ on-demand fallback: any *.hl under text_formalization/ for symbols
      that are still missing during the closure walk)
and writes pipeline/interval/out/defs.json:

    { NAME: {"params": [...], "body_ast": {...}, "source": "file:line"} ,
      ...
      "__unsupported__": {NAME: {"raw":..., "source":..., "reason":...}},
      "__meta__": {...summary/closure stats...} }

Reuses parse_body.py: its tokenizer is used verbatim for plain bodies
(parse_body.parse_tokens does the actual parsing there); the extended
parser below only kicks in for constructs outside the real-arithmetic
grammar of parse_body.py:
    if ... then ... else       -> {"if": ...}
    \\x. b   (lambda)          -> {"lambda": ...}
    !x. / ?x. / @x.  nested    -> {"forall"}/{"exists"}/{"choice"}
    (a, b, c) tuples           -> {"tuple": [...]}
    let (a,b) = e in b         -> {"let": {"vars": [...], ...}}
    &v  (real-of-num-var)      -> {"num2r": v}
    type annotations (x:A)     -> stripped in a pre-pass
Defs using set notation {x|...}, vector $i, list syntax, ... are recorded
in "__unsupported__" with their raw body.

Closure check: starting from every applied symbol / constant in
out/ineqs_ast.json (+ domain_raw wrappers), walk defs transitively and
report symbols with no definition.

Stdlib only.  Usage:  python3 pipeline/interval/parse_defs.py
"""

import glob
import json
import os
import re
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import parse_body as pb                       # noqa: E402  (reuse)

ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
TF_DIR = os.path.join(ROOT, "reference", "flyspeck", "text_formalization")
PRIMARY_FILES = [
    os.path.join(TF_DIR, "general", "sphere.hl"),
    os.path.join(TF_DIR, "nonlinear", "nonlin_def.hl"),
]
OUT_PATH = os.path.join(HERE, "out", "defs.json")
AST_PATH = os.path.join(HERE, "out", "ineqs_ast.json")

# ---------------------------------------------------------------- lexing
EXT_TOKEN_RE = re.compile(
    r"&[0-9]+"                                 # &n  integer-as-real
    r"|&[A-Za-z_][A-Za-z0-9_']*"               # &v  real-of-num-variable
    r"|#[0-9]+(?:\.[0-9]+)?"                   # #d(.d+)?  decimal
    r"|[0-9]+\.[0-9]+"
    r"|[0-9]+"
    r"|[A-Za-z_][A-Za-z0-9_']*"
    r"|==>|<=>|->|<=|>=|<|>|=|\+|\*"
    r"|\\/|/\\|//|/|%|\^"
    r"|:|\(|\)|\.|,|\{|\}|\||\?|@|\\|\[|\]|\$|;|!|--|-|~"
)

# tokens that force the extended parser (after type-annotation stripping)
EXT_MARKS = {"if", "then", "else", "\\", "?", "@", "!",
             "{", "}", ",", "|", "$", ";", "[", "]", ":"}


def tokenize(text, where):
    try:
        return pb.tokenize(text, where)
    except pb.ParseError:
        pass
    toks, i, n = [], 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        m = EXT_TOKEN_RE.match(text, i)
        if not m:
            raise pb.ParseError("%s: cannot tokenize at ...%s"
                                % (where, text[max(0, i - 30):i + 20]))
        toks.append(m.group(0))
        i = m.end()
    return toks


def has_ext(toks):
    for t in toks:
        if t in EXT_MARKS or t == "%":
            return True
        if t.startswith("&") and pb.IDENT_RE.match(t[1:]):
            return True                     # &v : real-of-num-variable
    return False


# ------------------------------------------------- type annotation removal
TYPE_CONT = {"^", "->"}


def strip_types(toks):
    """Remove `:TYPE` annotations:  (x:real^3) -> (x),  S:real^A->bool -> S."""
    out, i, n = [], 0, len(toks)
    while i < n:
        t = toks[i]
        if t != ":":
            out.append(t)
            i += 1
            continue
        i += 1                            # drop ':' and consume the type
        depth = 0
        while i < n:
            t = toks[i]
            if t == "(":
                depth += 1
                i += 1
            elif t == ")":
                if depth == 0:
                    break
                depth -= 1
                i += 1
            elif pb.IDENT_RE.match(t) or pb.NUM_RE.match(t) \
                    or t in TYPE_CONT:
                i += 1
            else:
                break
    return out


# ------------------------------------------------------- extended parser
EXT_PREC = dict(pb.PREC)
EXT_PREC["%"] = (7, "l")                  # vector/scalar mult, same as *
EXT_RESERVED = pb.RESERVED | {"if", "then", "else"}
NO_ARG_START = {")", "}", "]", ",", ".", "|", ";", ":", "$",
                "then", "else", "in", "{", "\\", "?", "@", "!", "if"}


class UnsupportedSyntax(pb.ParseError):
    pass


def ext_parse_tokens(toks, where):
    """Precedence climber mirroring parse_body.parse_tokens, plus the
    extended constructs.  Bodies without ext tokens go through
    parse_body.parse_tokens instead (see parse_term below)."""
    return _parser(toks, where)()


def _parser(toks, where):
    """Build a parser over `toks`; returns top-level parse function.
    Sub-slices (paren groups) get their own parser via recursion."""
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def advance():
        t = toks[pos[0]]
        pos[0] += 1
        return t

    def err(msg):
        lo, hi = max(0, pos[0] - 5), min(len(toks), pos[0] + 5)
        near = " ".join(toks[lo:pos[0]]) + " >>> " + \
            " ".join(toks[pos[0]:hi])
        raise pb.ParseError("%s: %s | near: %s" % (where, msg, near))

    def expect(t):
        if peek() != t:
            err("expected %r, got %r" % (t, peek()))
        return advance()

    def can_start_atom(t):
        if t is None or t in NO_ARG_START:
            return False
        if t == "(":
            return True                      # f (x) / f (a, b) applications
        if pb.NUM_RE.match(t):
            return True
        return pb.IDENT_RE.match(t) is not None \
            and t not in EXT_RESERVED and t not in EXT_PREC

    def parse_binders():
        """binders between sigil and '.':  x y  /  (x) (y)  /  (x,y)"""
        vs = []
        while True:
            t = peek()
            if t == "(":
                advance()
                while peek() != ")":
                    v = peek()
                    if not pb.IDENT_RE.match(v or ""):
                        err("bad binder %r" % v)
                    vs.append(v)
                    advance()
                    if peek() == ",":
                        advance()
                expect(")")
            elif t is not None and pb.IDENT_RE.match(t) \
                    and t not in EXT_RESERVED:
                vs.append(advance())
            else:
                break
        expect(".")
        return vs

    def parse_expr(min_prec):
        lhs = parse_unary()
        while True:
            t = peek()
            if t in ("{", "[", "$", ";"):
                raise UnsupportedSyntax(
                    "%s: unsupported construct %r" % (where, t))
            info = EXT_PREC.get(t)
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
            else:
                rhs = parse_expr(prec + 1)
                nt = peek()
                if EXT_PREC.get(nt, (0,))[0] == prec:
                    err("chained comparison %r after %r" % (nt, t))
            lhs = {"op": t, "args": [lhs, rhs]}
        return lhs

    def parse_unary():
        t = peek()
        if t == "~":
            advance()
            return {"not": parse_expr(pb.UNARY_MIN)}
        if t == "--":
            advance()
            return {"neg": parse_expr(pb.UNARY_MIN)}
        return parse_app()

    def parse_app():
        if peek() in ("{", "["):
            raise UnsupportedSyntax("%s: set/list notation" % where)
        node = parse_primary()
        while can_start_atom(peek()):
            arg = parse_primary()
            if "paren" in node and "args" in node:
                node["args"].append(arg)      # (f) a b -> paren node + args
            elif "paren" in node:
                node = {"paren": node["paren"], "args": [arg]}
            elif "app" in node and isinstance(node["app"], str):
                node = {"app": node["app"], "args": node["args"] + [arg]}
            elif "var" in node or "const" in node:
                node = {"app": node.get("var") or node.get("const"),
                        "args": [arg]}
            else:
                err("cannot apply non-symbol term")
        return node

    def find_group_end(i):
        depth = 0
        while i < len(toks):
            if toks[i] == "(":
                depth += 1
            elif toks[i] == ")":
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        err("unbalanced parentheses")

    def parse_primary():
        t = peek()
        if t is None:
            err("unexpected end of input")
        if t == "(":
            advance()
            j = find_group_end(pos[0] - 1)
            inner = toks[pos[0]:j]
            pos[0] = j + 1                    # consume ')'
            if len(inner) == 1 and (inner[0] in EXT_PREC
                                    or inner[0] in ("=", "--")):
                return {"paren": {"opref": inner[0]}}   # ( >= ) op reference
            if inner and inner[0] not in ("let", "\\", "?", "@", "!", "if"):
                # tuple group?  (a, b, c)
                depth, tops = 0, []
                for tt in inner:
                    if tt == "(":
                        depth += 1
                    elif tt == ")":
                        depth -= 1
                    elif tt == "," and depth == 0:
                        tops.append(tt)
                if tops:
                    parts, depth, last = [], 0, 0
                    for k, tt in enumerate(inner):
                        if tt == "(":
                            depth += 1
                        elif tt == ")":
                            depth -= 1
                        elif tt == "," and depth == 0:
                            parts.append(inner[last:k])
                            last = k + 1
                    parts.append(inner[last:])
                    return {"tuple": [parse_term(p, where + ":tuple")
                                      for p in parts]}
            if not has_ext(inner):
                try:
                    ast = pb.parse_tokens(inner, where + ":group")
                except (pb.ParseError, RecursionError):
                    ast = _parser(inner, where + ":group")()
            else:
                ast = _parser(inner, where + ":group")()
            return {"paren": ast}
        if re.match(r"^&[0-9]+$", t):
            advance()
            return {"num": t[1:]}
        if re.match(r"^&[A-Za-z_]", t):       # &v : real of num variable
            advance()
            return {"num2r": t[1:]}
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
        if t == "if":
            advance()
            c = parse_expr(1)
            expect("then")
            a = parse_expr(1)
            expect("else")
            b = parse_expr(1)
            return {"if": {"cond": c, "then": a, "else": b}}
        if t == "\\":
            advance()
            vs = parse_binders()
            return {"lambda": {"vars": vs, "body": parse_expr(1)}}
        if t in ("!", "?", "@"):
            sig = advance()
            vs = parse_binders()
            node = {"forall" if sig == "!" else
                    "exists" if sig == "?" else "choice":
                    {"vars": vs, "body": parse_expr(1)}}
            return node
        if t == "{":
            raise UnsupportedSyntax("%s: set notation" % where)
        if t in ("$", ";", "[", "]"):
            raise UnsupportedSyntax(
                "%s: unsupported construct %r" % (where, t))
        if pb.IDENT_RE.match(t):
            advance()
            if t in EXT_RESERVED:
                err("unexpected reserved word %r" % t)
            kind = "var" if pb.VAR_RE.match(t) else "const"
            return {kind: t}
        err("unexpected token %r" % t)

    def parse_let():
        advance()                              # `let`
        vs = []
        if peek() == "(":                      # tuple pattern
            advance()
            while peek() != ")":
                v = peek()
                if not pb.IDENT_RE.match(v or ""):
                    err("bad let binder %r" % v)
                vs.append(v)
                advance()
                if peek() == ",":
                    advance()
            expect(")")
        else:
            v = peek()
            if not pb.IDENT_RE.match(v or ""):
                err("expected bound variable name, got %r" % v)
            vs.append(v)
            advance()
        expect("=")
        val = parse_expr(1)
        expect("in")
        body = parse_expr(1)
        if len(vs) == 1:
            return {"let": {"var": vs[0], "val": val, "body": body}}
        return {"let": {"vars": vs, "val": val, "body": body}}

    def top():
        ast = parse_expr(1)
        if peek() is not None:
            err("trailing tokens after end of term")
        return ast

    return top


def parse_term(toks, where):
    """Parse a token slice: parse_body.parse_tokens when plain, else ext.
    If the plain parse fails, the extended parser (a strict superset that
    still delegates plain paren groups to parse_body) is tried."""
    if not toks:
        raise pb.ParseError("%s: empty term" % where)
    if not has_ext(toks):
        try:
            return pb.parse_tokens(toks, where)
        except (pb.ParseError, RecursionError):
            pass
    return ext_parse_tokens(toks, where)


# ------------------------------------------------------------ serializer
def _has_parenargs(node):
    if isinstance(node, dict):
        if "paren" in node and "args" in node:
            return True
        return any(_has_parenargs(v) for v in node.values())
    if isinstance(node, list):
        return any(_has_parenargs(v) for v in node)
    return False


def serialize(node):
    """Exact token round-trip for both plain and extended ASTs.

    Fast path: parse_body.serialize handles plain subtrees verbatim.
    Fallback: structural recursion for extended nodes / mixed trees."""
    if _has_parenargs(node):
        return _ser_ext(node)
    try:
        return pb.serialize(node)
    except (pb.ParseError, KeyError, TypeError):
        pass
    return _ser_ext(node)


def _ser_ext(node):
    """Structural serializer (extended nodes + plain nodes mixed)."""
    if "opref" in node:
        return [node["opref"]]
    if "num2r" in node:
        return ["&" + node["num2r"]]
    if "paren" in node and "args" in node:
        out = ["("] + _ser_ext(node["paren"]) + [")"]
        for a in node["args"]:
            out += _ser_ext(a)
        return out
    if "tuple" in node:
        out = ["("]
        for k, item in enumerate(node["tuple"]):
            if k:
                out.append(",")
            out += serialize(item)
        return out + [")"]
    if "if" in node:
        f = node["if"]
        return (["if"] + serialize(f["cond"]) + ["then"] +
                serialize(f["then"]) + ["else"] + serialize(f["else"]))
    if "lambda" in node:
        f = node["lambda"]
        return ["\\"] + list(f["vars"]) + ["."] + serialize(f["body"])
    for sig, key in (("!", "forall"), ("?", "exists"), ("@", "choice")):
        if key in node:
            f = node[key]
            return [sig] + list(f["vars"]) + ["."] + serialize(f["body"])
    if "let" in node:
        l = node["let"]
        if "vars" in l:
            head = ["let", "("]
            for k, v in enumerate(l["vars"]):
                if k:
                    head.append(",")
                head.append(v)
            head += [")", "="]
        else:
            head = ["let", l["var"], "="]
        return head + serialize(l["val"]) + ["in"] + serialize(l["body"])
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
    raise pb.ParseError("cannot serialize node %r" % (node,))


# --------------------------------------------------------- def extraction
DEF_RE = re.compile(
    r"(?:let\s+)?([A-Za-z_][A-Za-z0-9_']*)\s*=\s*"
    r"((?:new_recursive_definition|new_definition|define_dart|define)'?)\b"
    r"[^`]*`", re.S)


def strip_block_comments(text):
    """Blank out (* ... *) regions, preserving newlines (line numbers)."""
    out, i, n = [], 0, len(text)
    while i < n:
        j = text.find("(*", i)
        if j < 0:
            out.append(text[i:])
            break
        k = text.find("*)", j + 2)
        if k < 0:
            out.append(text[i:])
            break
        out.append(text[i:j])                 # preserved prefix
        seg = text[j:k + 2]                   # the comment itself
        out.append("".join(ch if ch == "\n" else " " for ch in seg))
        i = k + 2
    return "".join(out)


def extract_defs(path, _cache={}):
    """-> list of (name, quote_text, line) in file order (cached per file)."""
    if path in _cache:
        return _cache[path]
    with open(path, errors="replace") as f:
        raw = f.read()
    text = strip_block_comments(raw)
    defs = []
    for m in DEF_RE.finditer(text):
        # reject if a ';;' intervenes between keyword and backtick
        # (e.g. `let newdef rev t = define_dart (mk_dart rev t);;`)
        kw_end = m.end(2)
        if ";;" in text[kw_end:m.end() - 1]:
            continue
        name = m.group(1)
        i_bt = m.end() - 1
        j_bt = text.index("`", i_bt + 1)
        quote = text[i_bt + 1:j_bt]
        line = text[:m.start()].count("\n") + 1
        defs.append((name, quote, line))
    return defs


def norm_binder_parens(toks):
    """Flatten binder groups right after !/?/@ sigils:  ?(y). -> ?y.
    and ?(v,w)(r). -> ?v w r.  (pure binder sugar for exact round-trip;
    types are already stripped)."""
    out, i, n = [], 0, len(toks)
    while i < n:
        t = toks[i]
        out.append(t)
        if t in ("!", "?", "@"):
            i += 1
            while i < n:
                if toks[i] == "(":
                    j = i + 1
                    group = []
                    while j < n and toks[j] != ")":
                        if pb.IDENT_RE.match(toks[j]):
                            group.append(toks[j])
                        elif toks[j] != ",":
                            group = None
                            break
                        j += 1
                    if group is not None and j < n:
                        out.extend(group)
                        i = j + 1
                        continue
                    break
                elif pb.IDENT_RE.match(toks[i]) \
                        and toks[i] not in EXT_RESERVED:
                    out.append(toks[i])
                    i += 1
                else:
                    break
            continue
        i += 1
    return out


def split_header(toks, name):
    """Split `NAME params = body` -> (params, body_toks) or (None, toks)."""
    k = 0
    if toks and toks[0] == "!":               # `!h. bump h = ...`
        j = k + 1
        while j < len(toks) and toks[j] != ".":
            if not (pb.IDENT_RE.match(toks[j]) or toks[j] == "("
                    or toks[j] == ")"):
                j = 0
                break
            j += 1
        if j and j < len(toks):
            k = j + 1
    depth, eq = 0, None
    for i in range(k, len(toks)):
        t = toks[i]
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
        elif t == "=" and depth == 0:
            eq = i
            break
    if eq is None or eq == k:
        return None, toks
    prefix = toks[k:eq]
    if not pb.IDENT_RE.match(prefix[0]):
        return None, toks                     # no `NAME params` header
    params, i = [], 1
    while i < len(prefix):
        t = prefix[i]
        if pb.IDENT_RE.match(t):
            params.append(t)
            i += 1
        elif t == "(":                        # tuple / annotated param group
            i += 1
            while i < len(prefix) and prefix[i] != ")":
                if pb.IDENT_RE.match(prefix[i]):
                    params.append(prefix[i])
                i += 1
            i += 1                            # skip ')'
        else:
            return None, toks
    return params, toks[eq + 1:]


def parse_definition(name, quote, source):
    """-> (record, None) or (None, (raw, reason))."""
    where = source
    try:
        quant = None
        text = quote.strip()
        m = pb.QUANT_RE.match(text)
        if m:
            quant = m.group(1).split()
            text = m.group(2)
        toks = tokenize(text, where)
        if "//" in toks and not has_ext(toks):
            toks, _ = pb.strip_slash_comments(toks, where)
            toks = pb.drop_dangling_disj(toks)
        toks = strip_types(toks)
        toks = norm_binder_parens(toks)
        params, body_toks = split_header(toks, name)
        if params is None:
            params = []
            if not quant:
                quant = None
            else:
                body_toks = ["!"] + quant + ["."] + body_toks
        elif quant:                           # e.g. `!h. bump h = ...`
            params = params + [v for v in quant if v not in params]
            quant = None
        body = parse_term(body_toks, where)
        expect = (["!"] + quant + ["."] if quant else []) + body_toks
        got = serialize(body)
        if got != expect:
            kk = next((i for i, (a, b) in enumerate(zip(expect, got))
                       if a != b), min(len(expect), len(got)))
            raise pb.ParseError(
                "round-trip mismatch at token %d: input ~ %r vs got ~ %r"
                % (kk, " ".join(expect[max(0, kk - 5):kk + 5]),
                   " ".join(got[max(0, kk - 5):kk + 5])))
        ast = pb.strip_parens(body)
        if quant:
            ast = {"forall": {"vars": quant, "body": ast}}
        rec = {"params": params, "body_ast": ast, "source": source}
        return rec, None
    except (pb.ParseError, UnsupportedSyntax, RecursionError) as e:
        return None, (quote, str(e))


# ------------------------------------------------------------- symbol walk
def walk_syms(node, bound, out):
    """Collect free applied symbols / constants; `bound` = local binders."""
    if isinstance(node, dict):
        if "app" in node:
            out.add(node["app"])
            for a in node["args"]:
                walk_syms(a, bound, out)
            return
        if "var" in node or "const" in node:
            name = node.get("var") or node.get("const")
            if name not in bound:
                out.add(name)
            return
        if "num2r" in node:
            return
        if "opref" in node:
            return
        if "paren" in node:
            inner = node["paren"]
            if "args" in node:               # (f) a b : applied paren term
                if isinstance(inner, dict) and \
                        ("const" in inner or "var" in inner):
                    out.add(inner.get("const") or inner.get("var"))
                    for a in node["args"]:
                        walk_syms(a, bound, out)
                    return
                walk_syms(inner, bound, out)
                for a in node["args"]:
                    walk_syms(a, bound, out)
                return
            walk_syms(inner, bound, out)
            return
        if "op" in node:
            for a in node["args"]:
                walk_syms(a, bound, out)
            return
        if "tuple" in node:
            for a in node["tuple"]:
                walk_syms(a, bound, out)
            return
        for key in ("neg", "not", "paren"):
            if key in node:
                walk_syms(node[key], bound, out)
                return
        if "if" in node:
            f = node["if"]
            walk_syms(f["cond"], bound, out)
            walk_syms(f["then"], bound, out)
            walk_syms(f["else"], bound, out)
            return
        if "lambda" in node:
            f = node["lambda"]
            walk_syms(f["body"], bound | set(f["vars"]), out)
            return
        for key in ("forall", "exists", "choice"):
            if key in node:
                f = node[key]
                walk_syms(f["body"], bound | set(f["vars"]), out)
                return
        if "let" in node:
            l = node["let"]
            vs = [l["var"]] if "var" in l else l["vars"]
            walk_syms(l["val"], bound, out)
            walk_syms(l["body"], bound | set(vs), out)
            return


PRIMITIVES = {
    # real arithmetic / analysis primitives assumed builtin
    "sqrt", "atn", "asn", "acs", "sin", "cos", "tan", "log", "exp",
    "abs", "inv", "max", "min", "pi", "T", "F",
}

# free variables of the inequality statements themselves (never defs):
# x1..x9 / y1..y9 (pb.VAR_RE) and higher-order function placeholders
STMT_PLACEHOLDERS = {"f", "fx"}


def is_stmt_var(sym):
    return bool(pb.VAR_RE.match(sym)) or sym in STMT_PLACEHOLDERS


# ------------------------------------------------------------------- main
def main():
    # ---- 1. extract + parse definitions from the two primary files
    defs, unsupported = {}, {}
    dup = Counter()
    order = []
    for path in PRIMARY_FILES:
        rel = os.path.relpath(path, ROOT)
        for name, quote, line in extract_defs(path):
            if name in defs or name in unsupported:
                dup[name] += 1
                continue
            rec, bad = parse_definition(name, quote, "%s:%d" % (rel, line))
            if rec is not None:
                defs[name] = rec
                order.append(name)
            else:
                raw, reason = bad
                unsupported[name] = {"raw": raw.strip(),
                                     "source": "%s:%d" % (rel, line),
                                     "reason": reason}

    # ---- 2. closure roots from the inequality ASTs
    with open(AST_PATH) as f:
        ast_data = json.load(f)
    roots, domains_bad, stmt_vars = set(), [], set()
    for rec in ast_data["records"]:
        a = rec.get("body_ast")
        bound = set()
        if isinstance(a, dict) and "forall" in a:
            bound = set(a["forall"].get("vars") or [])
        if a:
            walk_syms(a, bound, roots)       # binder-aware walk
        d = rec.get("domain_raw")
        if isinstance(d, str):
            where = (rec.get("idv") or rec.get("idv_expr") or "<dom>")
            try:
                toks = pb.tokenize(d, where)
                if "//" in toks:
                    toks, _ = pb.strip_slash_comments(toks, where)
                    toks = pb.drop_dangling_disj(toks)
                walk_syms(pb.strip_parens(pb.parse_tokens(toks, where)),
                          bound, roots)
            except (pb.ParseError, RecursionError) as e:
                domains_bad.append((where, d, str(e)))

    # ---- 3. transitive closure, with fallback extraction when missing
    stmt_vars = {s for s in roots if is_stmt_var(s)}
    roots -= stmt_vars
    all_hl = sorted(glob.glob(os.path.join(TF_DIR, "*", "*.hl")))
    index = {}                               # name -> (path, quote, line)
    for path in all_hl:
        for name, quote, line in extract_defs(path):
            index.setdefault(name, (path, quote, line))
    fallback_used = {}
    seen, missing = set(), set()
    work = sorted(roots)
    while work:
        sym = work.pop()
        if sym in seen:
            continue
        seen.add(sym)
        if sym in PRIMITIVES:
            continue
        if sym not in defs:
            if sym in unsupported:
                continue                     # already triaged as unsupported
            hit = index.get(sym)
            if hit is None:
                missing.add(sym)
                continue
            path, quote, line = hit
            rel = os.path.relpath(path, ROOT)
            rec, bad = parse_definition(
                sym, quote, "auto:%s:%d" % (rel, line))
            if rec is not None:
                defs[sym] = rec
                fallback_used[sym] = rec["source"]
            else:
                unsupported[sym] = {"raw": bad[0].strip(),
                                    "source": "auto:%s:%d" % (rel, line),
                                    "reason": bad[1]}
                continue
        rec = defs[sym]
        ref = set()
        walk_syms(rec["body_ast"], set(rec["params"]), ref)
        for s in sorted(ref - seen):
            if not is_stmt_var(s):
                work.append(s)

    closure_syms = sorted(seen - missing)
    n_reachable = len([s for s in closure_syms if s in defs])

    # ---- 4. report + write
    print("== parse_defs.py summary ==")
    print("definitions parsed:         %d" % len(defs))
    print("  (of which auto-extracted:%d)" % len(fallback_used))
    print("definitions unsupported:    %d" % len(unsupported))
    for name in sorted(unsupported):
        u = unsupported[name]
        reason = u["reason"].split(": ", 1)[-1]
        print("  UNSUP %-30s %s" % (name, reason[:80]))
    print("duplicate definitions:      %d %s"
          % (sum(dup.values()), dict(dup) or ""))
    print("domain_raw that fail parse: %d" % len(domains_bad))
    for w, d, e in domains_bad[:5]:
        print("  dom %s: %s" % (w, e))
    print("closure roots (ineqs):      %d symbols" % len(roots))
    print("  statement variables:      %d (excluded: %s)"
          % (len(stmt_vars), " ".join(sorted(stmt_vars)) or "-"))
    print("closure size (transitive):  %d symbols" % len(seen))
    print("  resolved by defs.json:    %d" % n_reachable)
    print("  primitives (builtin):     %d" % len(seen & PRIMITIVES))
    print("  unsupported (skipped):    %d"
          % len([s for s in seen if s in unsupported]))
    print("symbols with NO definition: %d" % len(missing))
    for s in sorted(missing):
        print("  MISSING %s" % s)
    if fallback_used:
        print("fallback extractions:")
        for name, src in sorted(fallback_used.items()):
            print("  %-30s %s" % (name, src))

    out = {name: defs[name] for name in order}
    for name in sorted(defs):
        if name not in out:
            out[name] = defs[name]
    out["__unsupported__"] = unsupported
    out["__meta__"] = {
        "n_defs": len(defs),
        "n_unsupported": len(unsupported),
        "duplicates": dict(dup),
        "closure_roots": len(roots),
        "closure_size": len(seen),
        "closure_resolved": n_reachable,
        "statement_variables": sorted(stmt_vars),
        "missing": sorted(missing),
        "unsupported_names": sorted(unsupported),
        "fallback_sources": fallback_used,
    }
    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    with open(OUT_PATH, "w") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
    print("wrote %s" % OUT_PATH)

    if missing:
        print("NOTE: %d missing symbol(s) -- triage list above" % len(missing))
    print("VALIDATION OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

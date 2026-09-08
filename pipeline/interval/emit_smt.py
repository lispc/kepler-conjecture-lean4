#!/usr/bin/env python3
"""Phase 4b: emit QF_NRA SMT-LIB2 files asserting the NEGATION of each
Flyspeck nonlinear inequality (dReal proves the inequality by `unsat`).

Reads  pipeline/interval/out/ineqs_ast.json  and  pipeline/interval/out/defs.json
Writes pipeline/interval/out/smt/<idv-safe-name>.smt2

Features beyond plain AST printing (each reported in the final summary):
  * inlining of defs.json transitively, incl. higher-order partial
    application (y_of_x, abc_of_quadratic, enclosed->muR ...), tuple
    returns (abc_of_quadratic), if-then-else -> ite, let-bindings,
    num2r (&v), bnum numerals (tame_table_d)
  * choice-defined constants (hminus) -> declared variable + its
    characterizing constraints added to the antecedent (this is exactly
    Flyspeck's Nonlinear_lemma.hminus_prop usage)
  * dart domain predicates (dart_std4 etc.): literal box-bound triple
    lists parsed from ineq.hl `define_dart` bodies; anything else is
    skipped with a reason (never emit wrong math)
  * pi as (define-fun pi () Real (* 4.0 (atan 1.0)))  [dReal has no pi]
  * guard rails: per-record status, skip histogram, dReal sanity run on
    TSKAJXY-DERIVED with --precision 0.001

Stdlib only.  Usage:  python3 pipeline/interval/emit_smt.py
"""

import json
import os
import re
import subprocess
import sys
from collections import Counter, OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
AST_PATH = os.path.join(HERE, "out", "ineqs_ast.json")
DEFS_PATH = os.path.join(HERE, "out", "defs.json")
SMT_DIR = os.path.join(HERE, "out", "smt")
INEQ_HL = os.path.join(HERE, "..", "..",
                       "reference", "flyspeck", "text_formalization",
                       "nonlinear", "ineq.hl")
DREAL = os.path.join(HERE, "..", "tools", "dreal-4.21.06.2", "bin", "dreal")

SPOT_PRINT = {"TSKAJXY-DERIVED", "7043724150 a"}
SPOT_DREAL = "TSKAJXY-DERIVED"
NODE_BUDGET = 400000

TOKEN_RE = re.compile(
    r"&[0-9]+"
    r"|#[0-9]+(?:\.[0-9]+)?"
    r"|[0-9]+\.[0-9]+"
    r"|[0-9]+"
    r"|[A-Za-z_][A-Za-z0-9_']*"
    r"|==>|<=>|<=|>=|<|>|=|\+|\*|/|--|-|~|\(|\)|\.|,|\[|\]|\^|;")
PREC = {"+": (6, "l"), "-": (6, "l"), "*": (7, "l"), "/": (7, "l"),
        "pow": (9, "r")}
NUM_RE = re.compile(r"^(?:&|#)?[0-9]")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")

PRIMS = {  # app name -> SMT op
    "sqrt": "sqrt", "atn": "atan", "acs": "acos", "asn": "asin",
    "exp": "exp", "ln": "log", "log": "log", "abs": "abs",
    "sin": "sin", "cos": "cos", "tan": "tan", "sinh": "sinh",
    "cosh": "cosh", "tanh": "tanh",
}
FLIP = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "=": "distinct"}


class Skip(Exception):
    def __init__(self, reason):
        super(Skip, self).__init__(reason)
        self.reason = reason


class Closure(object):
    """Partially applied named definition (or anonymous lambda)."""
    def __init__(self, name, params, body, env, args):
        self.name, self.params, self.body = name, params, body
        self.env, self.args = env, args


class TupleVal(object):
    def __init__(self, items):
        self.items = items


class PointWise(object):
    """An op over non-term values (closures/tuples): distributed at
    application time, e.g.  constant6 c - scalar6 v  as a 6-arg function."""
    def __init__(self, op, vals):
        self.op, self.vals = op, vals


# Defs whose bodies parse_defs.py mangled (HOL type annotations
# `(f:real->...->real)` at the head of the RHS made it drop the
# trailing applications).  Transcribed verbatim from
# reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:72,246:
#   compose6 f p1..p6 x1..x6 = f (p1 x1..x6) ... (p6 x1..x6)
#   uni (f,x) x1..x6 = f (x x1..x6)
DEF_OVERRIDES = {
    "compose6": {
        "params": ["f", "p1", "p2", "p3", "p4", "p5", "p6",
                   "x1", "x2", "x3", "x4", "x5", "x6"],
        "body_ast": {"app": "f", "args": [
            {"app": "p%d" % i,
             "args": [{"var": "x%d" % j} for j in range(1, 7)]}
            for i in range(1, 7)]},
    },
    "uni": {
        "params": ["f", "x", "x1", "x2", "x3", "x4", "x5", "x6"],
        "body_ast": {"app": "f", "args": [
            {"app": "x", "args": [{"var": "x%d" % j}
                                  for j in range(1, 7)]}]},
    },
}


def load_defs(path):
    with open(path) as f:
        defs = json.load(f)
    defs.update(DEF_OVERRIDES)
    return defs


class Emitter(object):
    def __init__(self, defs, whitelist):
        self.defs = defs
        self.whitelist = whitelist        # name -> smt text (define-fun body)
        self.used_whitelist = set()
        self.choice_cons = []             # smt constraint strings
        self.choices = set()              # names declared for choice defs
        self.nodes = 0

    # ------------------------------------------------------------- atoms
    def numeral(self, node):
        if "num" in node:
            return fmt_num(node["num"])
        if "dec" in node:
            return fmt_dec(node["dec"])
        if "bnum" in node:
            return fmt_num(node["bnum"])
        raise Skip("unknown numeral node %r" % (node,))

    # ---------------------------------------------------------- emitter
    def ev(self, node, env):
        self.nodes += 1
        if self.nodes > NODE_BUDGET:
            raise Skip("expansion too large (> %d nodes)" % NODE_BUDGET)
        if "num" in node or "dec" in node or "bnum" in node:
            return self.numeral(node)
        if "var" in node or "const" in node:
            name = node.get("var") or node.get("const")
            if name in env:
                return env[name]
            if re.match(r"^[xy][0-9]+$", name):
                return name                      # statement variable
            return self.lookup(name, env)
        if "neg" in node:
            return self.combine("-", [self.ev(node["neg"], env)])
        if "not" in node:
            return "(not %s)" % self.term(node["not"], env)
        if "paren" in node:
            return self.ev(node["paren"], env)
        if "if" in node:
            return self.combine("ite", [self.ev(node["if"]["cond"], env),
                                        self.ev(node["if"]["then"], env),
                                        self.ev(node["if"]["else"], env)])
        if "let" in node:
            l = node["let"]
            env2 = dict(env)
            if "vars" in l:                  # multi-binding pattern let
                val = self.ev(l["val"], env)
                if not isinstance(val, TupleVal) or \
                        len(val.items) != len(l["vars"]):
                    raise Skip("bad pattern let")
                for p, v in zip(l["vars"], val.items):
                    env2[p] = v
            else:
                env2[l["var"]] = self.ev(l["val"], env)
            return self.ev(l["body"], env2)
        if "tuple" in node:
            return TupleVal([self.ev(x, env) for x in node["tuple"]])
        if "lambda" in node:
            return Closure("<lambda>", node["lambda"]["vars"],
                           node["lambda"]["body"], env, [])
        if "forall" in node or "exists" in node or "choice" in node:
            raise Skip("quantifier/choice inside expanded body")
        if "opref" in node:
            raise Skip("operator reference ( >= )")
        if "num2r" in node:
            name = node["num2r"]
            if name in env:
                return env[name]
            raise Skip("free num2r %r" % name)
        if "op" in node:
            return self.ev_op(node, env)
        if "app" in node:
            vals = [self.ev(a, env) for a in node["args"]]
            head = node["app"]
            if isinstance(head, str) and head in env:
                return self.ev_app(env[head], vals)
            return self.ev_app(head, vals)
        raise Skip("unhandled AST node form %r" % sorted(node.keys()))

    def term(self, node, env):
        v = self.ev(node, env)
        if not isinstance(v, str):
            raise Skip("non-real/bool term where term expected (%s)"
                       % type(v).__name__)
        return v

    def combine(self, op, vals):
        """Combine values with an SMT op; distribute over functions/tuples."""
        if all(isinstance(v, str) for v in vals):
            if len(vals) == 1:
                return "(%s %s)" % (op, vals[0])
            return "(%s %s)" % (op, " ".join(vals))
        if any(isinstance(v, TupleVal) for v in vals):
            n = len(next(v for v in vals if isinstance(v, TupleVal)).items)
            if any(isinstance(v, TupleVal) and len(v.items) != n
                   for v in vals):
                raise Skip("tuple arity mismatch in %s" % op)
            cols = list(zip(*[v.items if isinstance(v, TupleVal)
                              else [v] * n for v in vals]))
            return TupleVal([self.combine(op, list(c)) for c in cols])
        return PointWise(op, vals)

    def apply_value(self, v, args):
        if isinstance(v, str):
            return v
        if isinstance(v, TupleVal):
            return TupleVal([self.apply_value(x, args) for x in v.items])
        if isinstance(v, Closure):
            return self.ev_app(v, args)
        if isinstance(v, PointWise):
            return self.combine(v.op, [self.apply_value(x, args)
                                       for x in v.vals])
        raise Skip("application of non-function value")

    def lookup(self, name, env):
        if name in PRIMS:                    # first-class primitive function
            return Closure(name, ["u"],
                           {"app": name, "args": [{"var": "u"}]}, {}, [])
        if name in ("min", "max"):
            return Closure(name, ["u", "v"],
                           {"if": {"cond": {"op": "<" if name == "min"
                                            else ">",
                                            "args": [{"var": "u"},
                                                     {"var": "v"}]},
                                   "then": {"var": "u"},
                                   "else": {"var": "v"}}}, {}, [])
        d = self.defs.get(name)
        if d is not None:
            if name in self.whitelist:
                self.used_whitelist.add(name)
                return name
            if not d["params"]:
                body = d["body_ast"]
                if isinstance(body, dict) and "choice" in body:
                    if name not in self.choices:
                        vs = body["choice"]["vars"]
                        if len(vs) != 1:
                            raise Skip("unsupported choice def %r" % name)
                        v = body["choice"]["vars"][0]
                        env2 = dict(env)
                        env2[v] = name
                        self.choices.add(name)
                        self.choice_cons.append(self.term(body["choice"]["body"],
                                                          env2))
                    return name
                return self.ev(body, {})
            return Closure(name, d["params"], d["body_ast"], {}, [])
        if name == "pi":
            self.used_whitelist.add("pi")
            return "pi"
        raise Skip("unresolved constant %r" % name)

    def ev_op(self, node, env):
        op, args = node["op"], node["args"]
        if op == "pow":
            if len(args) != 2:
                raise Skip("bad pow arity")
            base = self.ev(args[0], env)
            e = args[1]
            if ("num" in e) or ("bnum" in e) or ("dec" in e):
                k = self.numeral(e)
                if re.match(r"^-?[0-9]+\.0$", k):
                    return self.combine("^", [base, k])
            raise Skip("non-integer-literal pow exponent")
        if op in ("/\\", "\\/"):
            return self.combine("and" if op == "/\\" else "or",
                                [self.ev(args[0], env), self.ev(args[1], env)])
        if op == "==>":
            return self.combine("=>", [self.ev(args[0], env),
                                       self.ev(args[1], env)])
        if op == "<=>":
            return self.combine("=", [self.ev(args[0], env),
                                      self.ev(args[1], env)])
        if op in ("=", "<", ">", "<=", ">="):
            return self.combine(op, [self.ev(args[0], env),
                                     self.ev(args[1], env)])
        if op in ("+", "-", "*", "/"):
            if op == "-" and len(args) == 1:
                return self.combine("-", [self.ev(args[0], env)])
            return self.combine(op, [self.ev(args[0], env),
                                     self.ev(args[1], env)])
        if op == "%":
            raise Skip("vector/scalar op %")
        raise Skip("unhandled op %r" % op)

    def ev_app(self, head, vals):
        if isinstance(head, str):
            sym = head
            if sym in PRIMS:
                if len(vals) != 1:
                    raise Skip("bad arity for %s" % sym)
                return "(%s %s)" % (PRIMS[sym], only(vals))
            if sym in ("min", "max"):
                if len(vals) != 2:
                    raise Skip("bad arity for %s" % sym)
                a, b = vals
                cmp = "<" if sym == "min" else ">"
                return "(ite (%s %s %s) %s %s)" % (cmp, a, b, a, b)
            v = self.lookup(sym, {})
            if not isinstance(v, Closure):
                raise Skip("application of non-function %r" % sym)
            cl = v
        elif isinstance(head, (Closure, PointWise, TupleVal)):
            if not isinstance(head, Closure):
                return self.apply_value(head, vals)
            cl = head
        else:
            raise Skip("application of non-function term")
        expanded = []
        for v in cl.args + list(vals):
            if isinstance(v, TupleVal):
                expanded.extend(v.items)   # HOL tuple over leading params
            else:
                expanded.append(v)
        vals = expanded
        if len(vals) < len(cl.params):
            return Closure(cl.name, cl.params, cl.body, cl.env, vals)
        if len(vals) == len(cl.params):
            env2 = dict(cl.env)
            for p, v in zip(cl.params, vals):
                env2[p] = v
            return self.ev(cl.body, env2)
        raise Skip("arity mismatch applying %r (%d args, %d params)"
                   % (cl.name, len(vals), len(cl.params)))


def only(vals):
    return vals[0]


def fmt_num(s):
    return "%s.0" % str(int(s))


def fmt_dec(s):
    if "." in s:
        return s
    return "%s.0" % s


# ------------------------------------------------------- whitelist consts
def build_whitelist(defs):
    """Nullary defs whose bodies are literal/primitive only (pi allowed)."""
    def simple(node):
        if isinstance(node, dict):
            if "num" in node or "dec" in node or "bnum" in node:
                return True
            if "paren" in node or "neg" in node:
                return simple(node.get("paren") or node["neg"])
            if "app" in node:
                return node["app"] in PRIMS and all(simple(a)
                                                    for a in node["args"])
            if "op" in node:
                return all(simple(a) for a in node["args"])
            if "if" in node:
                f = node["if"]
                return all(simple(f[k]) for k in ("cond", "then", "else"))
            return False
        return False
    out = OrderedDict()
    out["pi"] = "(* 4.0 (atan 1.0))"
    for name in sorted(defs):
        if name.startswith("__"):
            continue
        d = defs[name]
        if d["params"] or name in out:
            continue
        if simple(d["body_ast"]):
            e = Emitter(defs, out)
            try:
                out[name] = e.term(d["body_ast"], {})
            except (Skip, RecursionError):
                del out[name]
    return out


# --------------------------------------------------------- mini expr parse
def tokenize(text, where):
    toks, i, n = [], 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        m = TOKEN_RE.match(text, i)
        if not m:
            raise Skip("%s: cannot tokenize at ...%s"
                       % (where, text[max(0, i - 25):i + 15]))
        toks.append(m.group(0))
        i = m.end()
    return toks


def parse_expr(toks, where):
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def advance():
        t = toks[pos[0]]
        pos[0] += 1
        return t

    def expr(min_prec):
        lhs = unary()
        while True:
            t = peek()
            info = PREC.get(t)
            if info is None:
                break
            prec, assoc = info
            if prec < min_prec:
                break
            advance()
            rhs = expr(prec + 1 if assoc == "l" else prec)
            lhs = {"op": t, "args": [lhs, rhs]}
        return lhs

    def unary():
        t = peek()
        if t == "--":
            advance()
            return {"neg": expr(8)}
        return primary()

    def primary():
        t = advance()
        if t == "(":
            inner = expr(1)
            if advance() != ")":
                raise Skip("%s: expected )" % where)
            return inner
        if re.match(r"^&[0-9]+$", t):
            return {"num": t[1:]}
        if t.startswith("#"):
            return {"dec": t[1:]}
        if re.match(r"^[0-9]+$", t):
            return {"bnum": t}
        if re.match(r"^[0-9]+\.[0-9]+$", t):
            return {"dec": t}
        if IDENT_RE.match(t):
            kind = "var" if re.match(r"^[xy][0-9]+$", t) else "const"
            return {kind: t}
        raise Skip("%s: bad atom %r" % (where, t))

    ast = expr(1)
    if pos[0] != len(toks):
        raise Skip("%s: trailing tokens %r" % (where, toks[pos[0]:pos[0] + 4]))
    return ast


def parse_bound(text, where):
    return parse_expr(tokenize(text, where), where)


# ------------------------------------------------------------ dart domains
DART_RE = re.compile(r"let\s+([A-Za-z_][A-Za-z0-9_']*)\s*=\s*define_dart\s*"
                     r"`([^`]*)`")


def load_darts(path):
    with open(path) as f:
        text = f.read()
    darts = {}
    for m in DART_RE.finditer(text):
        darts[m.group(1)] = " ".join(m.group(2).split())
    return darts


def split_top(s, sep):
    parts, depth, cur = [], 0, []
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return [p.strip() for p in parts if p.strip()]


def dart_constraint_ast(name, darts, depth=0):
    """-> list of (lo_ast, var, hi_ast) for a define_dart box predicate."""
    if depth > 6 or name not in darts:
        raise Skip("unsupported domain predicate %r" % name)
    text = darts[name]
    if "=" not in text:
        raise Skip("bad define_dart body for %r" % name)
    rhs = text.split("=", 1)[1].strip()
    if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", rhs):     # alias
        return dart_constraint_ast(rhs, darts, depth + 1)
    m = re.match(r"^\[(.*)\]$", rhs)
    if not m:
        raise Skip("domain %r is not a literal box list" % name)
    out = []
    for triple in split_top(m.group(1), ";"):
        trip = triple.strip()
        if not (trip.startswith("(") and trip.endswith(")")):
            raise Skip("bad bound triple %r" % trip)
        fields = split_top(trip[1:-1], ",")
        if len(fields) != 3:
            raise Skip("bad bound triple %r" % trip)
        w = "domain %r" % name
        out.append((parse_bound(fields[0], w), fields[1].strip(),
                    parse_bound(fields[2], w)))
    if not out:
        raise Skip("empty domain %r" % name)
    return out


# --------------------------------------------------------------- assembly
def collect_vars(node, acc):
    if isinstance(node, dict):
        if "var" in node or "const" in node:
            n = node.get("var") or node.get("const")
            if re.match(r"^[xy][0-9]+$", n):
                acc.add(n)
            return
        if "num2r" in node:
            return
        for k, v in node.items():
            if k == "if":
                for kk in ("cond", "then", "else"):
                    collect_vars(v[kk], acc)
            elif k in ("forall", "exists", "choice", "lambda"):
                collect_vars(v["body"], acc)
            elif k == "let":
                collect_vars(v["val"], acc)
                collect_vars(v["body"], acc)
            elif k == "tuple":
                for x in v:
                    collect_vars(x, acc)
            elif isinstance(v, (dict, list)):
                collect_vars(v, acc)
    elif isinstance(node, list):
        for x in node:
            collect_vars(x, acc)


def translate_record(rec, defs, whitelist, darts):
    """-> (text, note) ; raises Skip."""
    ast = rec.get("body_ast")
    if not ast:
        raise Skip("no parsed body_ast")
    em = Emitter(defs, whitelist)

    # bounds (list of triples, or a raw leftover entry)
    bound_triples = []
    for b in rec.get("bounds") or []:
        if "var" in b:
            bound_triples.append((parse_bound(b["lo"], rec["idv"]),
                                  b["var"], parse_bound(b["hi"], rec["idv"])))
        elif "raw" in b:
            raw = b["raw"].split("//")[0]
            for grp in re.findall(r"\(([^()]*(?:\([^()]*\)[^()]*)*)\)", raw):
                fields = split_top(grp, ",")
                if len(fields) != 3:
                    raise Skip("unparseable raw bounds %r" % b["raw"])
                bound_triples.append((parse_bound(fields[0], rec["idv"]),
                                      fields[1].strip(),
                                      parse_bound(fields[2], rec["idv"])))
        else:
            raise Skip("bad bounds entry %r" % (b,))

    # domain predicate
    dom_terms = []
    if "domain_raw" in rec:
        toks = tokenize(rec["domain_raw"], rec["idv"])
        fname, args = toks[0], toks[1:]
        if fname in darts:
            for lo, v, hi in dart_constraint_ast(fname, darts):
                lov = em.term(lo, {})
                hiv = em.term(hi, {})
                dom_terms.append("(and (<= %s %s) (<= %s %s))"
                                 % (lov, v, v, hiv))
        elif fname in defs:
            vals = [em.lookup(a, {}) if not re.match(r"^[xy][0-9]+$", a)
                    else a for a in args]
            dom_terms.append(em.ev_app(fname, vals))
        else:
            dart_constraint_ast(fname, darts)   # raises unsupported-domain

    # core implication spine:  P1 ==> ... ==> Pk ==> CORE
    positives, core = [], ast
    while isinstance(core, dict) and "op" in core and core["op"] == "==>":
        positives.append(core["args"][0])
        core = core["args"][1]
    if isinstance(core, dict) and "forall" in core:
        core = core["forall"]["body"]      # strip record-level quantifier
    while isinstance(core, dict) and "op" in core and core["op"] == "==>":
        positives.append(core["args"][0])
        core = core["args"][1]

    # strip any top-level forall wrappers on the first positive too
    bound_s = [(em.term(lo, {}), v, em.term(hi, {}))
               for lo, v, hi in bound_triples]
    core_s = em.term(core, {})
    pos_s = [em.term(p, {}) for p in positives]
    dom_s = list(dom_terms)
    cons_s = list(em.choice_cons)

    lines = ["(set-logic QF_NRA)"]
    for name in whitelist:
        if name in em.used_whitelist:
            lines.append("(define-fun %s () Real %s)" % (name,
                                                         whitelist[name]))
    decl = set()
    for t in bound_triples:
        decl.add(t[1])
    for b in rec.get("bounds") or []:
        if "var" in b:
            decl.add(b["var"])
    collect_vars(ast, decl)
    if "domain_raw" in rec:
        for a in tokenize(rec["domain_raw"], rec["idv"])[1:]:
            if re.match(r"^[xy][0-9]+$", a):
                decl.add(a)
    decl |= em.choices
    for v in sorted(decl):
        lines.append("(declare-fun %s () Real)" % v)
    for lo, v, hi in bound_s:
        lines.append("(assert (<= %s %s))" % (lo, v))
        lines.append("(assert (<= %s %s))" % (v, hi))
    main = dom_s + cons_s + pos_s
    flip = negate_core_with_em(core, em)
    if flip is not None:
        main.append(flip)
    else:
        main.append("(not %s)" % core_s)
    lines.append("(assert (and %s))" % " ".join(main))
    lines.append("(check-sat)")
    lines.append("(exit)")
    return "\n".join(lines) + "\n", em


def negate_core_with_em(core, em):
    if isinstance(core, dict) and "op" in core and core["op"] in FLIP:
        op = FLIP[core["op"]]
        a = em.term(core["args"][0], {})
        b = em.term(core["args"][1], {})
        if op == "distinct":
            return "(not (= %s %s))" % (a, b)
        return "(%s %s %s)" % (op, a, b)
    return None


def safe_name(idv):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", idv).strip("_") + ".smt2"


def main():
    with open(AST_PATH) as f:
        data = json.load(f)
    defs = load_defs(DEFS_PATH)
    recs = data["records"]
    whitelist = build_whitelist(defs)
    darts = load_darts(INEQ_HL)
    os.makedirs(SMT_DIR, exist_ok=True)

    emitted, skipped = [], []
    for rec in recs:
        idv = rec.get("idv") or "<idv?>"
        try:
            text, _ = translate_record(rec, defs, whitelist, darts)
        except Skip as e:
            skipped.append((idv, e.reason))
            print("SKIP  %-28s %s" % (idv, e.reason))
            continue
        except RecursionError:
            skipped.append((idv, "recursion limit"))
            print("SKIP  %-28s recursion limit" % idv)
            continue
        path = os.path.join(SMT_DIR, safe_name(idv))
        with open(path, "w") as f:
            f.write(text)
        emitted.append(idv)
        print("EMIT  %-28s %s" % (idv, os.path.relpath(path, HERE)))
        if idv in SPOT_PRINT:
            print("----- spot-check %s -----" % idv)
            print(text, end="")
            print("----- end spot-check %s -----" % idv)

    reasons = Counter(r.split("(")[0].split(":")[0].strip()
                      if not r.startswith("unsupported domain")
                      else "unsupported domain predicate"
                      for _, r in skipped)
    print("\n== emit_smt.py summary ==")
    print("records:            %d" % len(recs))
    print("emitted:            %d" % len(emitted))
    print("skipped:            %d" % len(skipped))
    for r, c in reasons.most_common():
        print("  %-38s %d" % (r, c))
    print("whitelist define-funs: %s" % ", ".join(whitelist))

    # sanity: dReal on TSKAJXY-DERIVED
    spot = os.path.join(SMT_DIR, safe_name(SPOT_DREAL))
    if os.path.exists(spot):
        cmd = [DREAL, "--precision", "0.001", spot]
        print("\n== dReal sanity: %s" % " ".join(
            os.path.relpath(c, HERE) if os.path.abspath(c).startswith(HERE)
            else c for c in cmd))
        try:
            p = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=120)
            out = (p.stdout + p.stderr).strip()
            print("dReal says: %s (exit %d)" % (out.splitlines()[-1]
                                                if out else "<silent>",
                                                p.returncode))
        except subprocess.TimeoutExpired:
            print("dReal says: TIMEOUT after 120s")

    return 0


if __name__ == "__main__":
    sys.exit(main())

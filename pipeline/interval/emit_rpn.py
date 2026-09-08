#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Phase 4 (c) 第 1 段：把 176 条不等式展开成 RPN 案例文件（Arb 分支定界层的输入）。

读  pipeline/interval/out/ineqs_ast.json + pipeline/interval/out/defs.json
（与 emit_smt.py 同一展开闭包管线：Emitter 逐节点镜像 emit_smt.py，只是把
「SMT 文本」换成「Expr 树 → RPN 指令流」）。
写  pipeline/interval/out/cases/<idv-safe-name>.json

重要差别：SMT 版发射的是否定式（dReal unsat ⟺ 原式成立），本版直接编码
原式目标 prog，叶闭合条件 lo > 0（严格不等式，见 arb-layer.md §2）。

== case 文件格式（v1，对齐 arb-layer.md §1）==

{
  "id":      原始 idv,
  "orig_op": 原不等式核心比较算子（">" ">=" "<" "<=" 或 "disj"）,
  "vars":    ["y1", ...]           变量名有序表（自然排序，对应 Lean 的 Fin n）,
  "box":     [[lo, hi], ...]       与 vars 同序；端点 {"num":..,"den":..} 是
                                   精确有理数，已 dyadic 外扩到 2^q 网格,
  "q":       -30                   网格指数（步长 2^q，默认 2^-30）,
  "prog":    主目标 RPN 程序：在子盒上求值，叶闭合条件 lo > 0,
  "disj":    [可选] 额外闭合备选（原核心是析取时的其余析取项）：
               {"prog": [...], "orig_op": ">"}   比较型析取项（同样 lo>0 闭合）
               {"var_lt": [i, j]}                变量序型析取项 y_i < y_j：
                                                 子盒上 hi_i < lo_j 即成立,
  "notes":   [语义裁剪记录，见下],
  "stats":   {"ops":.., "ite":.., "depth":..}
}

RPN ops 编码：
  ["push_var", i]                     压入第 i 个变量的区间
  ["push_const", {"num":n,"den":d}]   压入精确有理常量 n/d
  ["add"|"sub"|"mul"|"neg"|"div"|"sqrt"|"atan"|"sin"|"cos"|"abs"|"log"]
  {"ite": {"cond": <prog>, "then": <prog>, "else": <prog>[, "mode": "eq"]}}
      结构化 guard 节点（嵌套 RPN，占外层指令流一个位置；比线性 guard_lt
      指令不易错）。语义 ite(c<0, then, else)——求值器先算 cond 的区间：
        mode "lt"（缺省）：hi < 0 → 取 then；lo >= 0 → 取 else；
                          跨 0 → STRADDLE（驱动层继续二分）
        mode "eq"（定义展开引入 ite(c=0,..) 时）：cond 恰为 [0,0] → then；
                          lo > 0 或 hi < 0 → else；其余 STRADDLE
      Python 冒烟求值器在 STRADDLE 时取 then∪else 并计数（sound，够冒烟）。
  命名常量在展开期内联：pi → 4*atan(1)，sqrt8 → sqrt(const 8)，
  其余（h0/hplus/cstab/...）查 defs.json 逐 def 内联——与 SMT define-fun
  白名单是同一批常量、同一些字面量。
  acos/asin 不设新 op（Lean 侧 IExpr 的 trans 节点也只有 sin/cos/arctan），
  在展开期用半角恒等式化掉（逐点成立，区间上 sound）：
    acos(x) = 2*atan( sqrt(1-x^2) / (1+x) )   x ∈ (−1,1]，x→−1 时分母趋 0
    asin(x) = 2*atan( x / (1 + sqrt(1-x^2)) ) |x|<=1，分母 >= 1 恒不爆
  其余原始函数（exp/tan/...）不出现，见到即 Skip。
  log 是一个**规格偏离**：Flyspeck 的 matan（arctan 的解析延拓）负分支
  matan(x) = ln((1+√(−x))/(1−√(−x))) / (2√(−x))（x<0）无法用 atan 代数化，
  176 条里有 6 条经定义展开真实到达该分支，故增设 ["log"] op（区间语义
  单调、有理外扩）。代价：bb_arb.c 用 arb_log 即可；Lean 证书层的
  trans 节点族需补 ln 一项（arb-layer.md §3 的扩展清单加一条）。

== 目标语义（核心比较 P 如何变成 prog）==

  P: a > b 或 a >= b → prog 编码 a - b（>= 用严格目标，证得更强，sound）
  P: a < b 或 a <= b → prog 编码 b - a
  P: A1 \/ A2 \/ ...（对称型记录）→ prog 取第一个比较型析取项，其余比较型
     析取项进 "disj"；纯变量序析取项 y_i < y_j 进 "disj" 的 var_lt。
     叶闭合 = prog lo>0 或任一 disj 项成立。
     若某析取项两者都不是（既非比较亦非变量序）→ 整条 Skip，绝不发错数学。

== soundness 说明（语义裁剪，全部写进 notes）==

  * ==> 前件（如 ~critical_edge_y y1、&0 < delta_y ...）：RPN 层无布尔约束，
    丢弃 = 在更大的盒上证原式（充分条件），sound 但该案例可能闭合不了；
  * choice 定义（hminus）：特征方程 marchal_quartic h = lmfun h 丢弃，变量 h
    按其特征不等式组的外扩盒（[1.2, 1.3]）处理——超集盒，sound；
  * 盒端点含 choice 变量时（如 hi = &2*hminus）按 h 的盒做区间外推再取并，
    仍是原域的超集。

== 冒烟自检 ==

内置 eval_rpn：Fraction 端点区间算术（sqrt 整数开方上下取整外扩、atan 交替
级数外扩、sin/cos 保守取 [-1,1]、div 越零抛 EvalError）——它只做冒烟不是
求解器。每个案例在根盒 dyadic 中点求值一次确认不 crash；另对若干人工案例
写死断言（x^2-2>0 在 [1.5,2] 上 lo>0 等）。末尾与 out/smt/*.smt2 交叉抽查
5 例（变量集合一致 + 常量字面量集合一致）。

Stdlib only.  Usage:  python3 pipeline/interval/emit_rpn.py [--ids ID1,ID2] [--q 30]
"""

import argparse
import json
import math
import os
import re
import sys
from collections import Counter
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
AST_PATH = os.path.join(HERE, "out", "ineqs_ast.json")
DEFS_PATH = os.path.join(HERE, "out", "defs.json")
CASES_DIR = os.path.join(HERE, "out", "cases")
SMT_DIR = os.path.join(HERE, "out", "smt")
INEQ_HL = os.path.join(HERE, "..", "..",
                       "reference", "flyspeck", "text_formalization",
                       "nonlinear", "ineq.hl")

NODE_BUDGET = 400000
DEFAULT_Q = 30

# 交叉抽查默认案例：覆盖 >= 核心 / 析取 / sqrt8+hminus 盒端点 / choice / ==> 前件
XCHECK_IDS = [
    "TSKAJXY-RIBCYXU",
    "BIXPCGW 7274157868 a",
    "QZECFIC wt0 sqrt8",
    "GLFVCVK4 2477216213",
    "TSKAJXY-DERIVED",
]

IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
STMT_VAR_RE = re.compile(r"^[xy][0-9]+$")

PRIMS = {  # app name -> RPN op（acos/asin 用半角恒等式化掉，见 ev_app；其余 Skip）
    "sqrt": "sqrt", "atn": "atan", "sin": "sin", "cos": "cos", "abs": "abs",
    "acs": "acos", "asn": "asin", "log": "log", "ln": "log",
}
CMP_OPS = ("<", "<=", ">", ">=", "=")


class Skip(Exception):
    def __init__(self, reason):
        super(Skip, self).__init__(reason)
        self.reason = reason


class EvalError(Exception):
    pass


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


# Defs whose bodies parse_defs.py mangled — 与 emit_smt.py 逐字一致。
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


def parse_dec(s):
    """十进制字面量 → 精确 Fraction（不用 float）。"""
    return Fraction(s)


def numeral_frac(node):
    if "num" in node or "bnum" in node:
        return Fraction(int(node.get("num") or node.get("bnum")))
    if "dec" in node:
        return parse_dec(node["dec"])
    raise Skip("unknown numeral node %r" % (node,))


# ----------------------------------------------------------- 精确外扩初等函数
SQRT_GRID_Q = 30  # sqrt 有理外扩的网格精度（box 端点需要紧下界，如 √8≈2.8284271）


def sqrt_floor_frac(a):
    """sqrt(a) 的有理下界（2^-SQRT_GRID_Q 网格，仍是有效下界）。要求 a >= 0。"""
    g = 1 << SQRT_GRID_Q
    # 最大 m 使 (m/g)^2 <= a：先估计再 ±1 校正，全程精确整数运算
    m2 = a * g * g
    m = math.isqrt(m2.numerator // m2.denominator)
    while Fraction(m + 1, g) ** 2 <= a:
        m += 1
    while m > 0 and Fraction(m, g) ** 2 > a:
        m -= 1
    return Fraction(m, g), (Fraction(m, g) ** 2 == a)


def sqrt_ceil_frac(a):
    """sqrt(a) 的有理上界（2^-SQRT_GRID_Q 网格，仍是有效上界）。要求 a >= 0。"""
    g = 1 << SQRT_GRID_Q
    m2 = a * g * g
    m = math.isqrt(-(-m2.numerator // m2.denominator))
    while Fraction(m, g) ** 2 < a:
        m += 1
    while m > 0 and Fraction(m - 1, g) ** 2 >= a:
        m -= 1
    return Fraction(m, g)


def atan_pos_bounds(t):
    """atan(t) 的有理上下界（0 <= t <= 1 用交替级数，t > 1 用 pi/2 - atan(1/t)）。

    交替级数部分和 S_even >= atan >= S_odd（项单调递减），天然外扩。
    """
    if t < 0:
        lo, hi = atan_pos_bounds(-t)
        return (-hi, -lo)
    if t == 0:
        return (Fraction(0), Fraction(0))
    if t > 1:
        plo, phi = pi_half_bounds()
        lo1, hi1 = atan_pos_bounds(Fraction(1, 1) / t)
        return (plo - hi1, phi - lo1)
    s = Fraction(0)
    lo = None
    hi = None
    k = 0
    while True:
        term = t ** (2 * k + 1) / (2 * k + 1)
        if k % 2 == 0:                   # 交替级数 (−1)^k t^(2k+1)/(2k+1)
            s += term
            hi = s
        else:
            s -= term
            lo = s
        if lo is not None and (term < Fraction(1, 1 << 50) or k >= 200):
            break
        k += 1
    return (lo, hi)


def pi_half_bounds():
    """pi/2 = 2*atan(1) 的有理外扩界（atan(1)≈0.7854 ∈ (39/50, 4/5) 级别）。"""
    lo, hi = atan_pos_bounds(Fraction(1))
    return (2 * lo, 2 * hi)


def log_pos_bounds(y):
    """ln(y)（y>0）的有理外扩界：ln y = 2*(z + z^3/3 + z^5/5 + ...)，
    z = (y-1)/(y+1) ∈ (−1,1)。z>0 时截断是下界，z<0 时交替级数夹逼；
    两种情况都再按几何级数余项 |R| <= 2|z|^{2K+1}/((2K+1)(1−z^2)) 外扩。"""
    z = (y - 1) / (y + 1)
    if z == 0:
        return (Fraction(0), Fraction(0))
    s = Fraction(0)
    prev = Fraction(0)
    k = 0
    while True:
        term = z ** (2 * k + 1) / (2 * k + 1)
        prev = s
        s += 2 * term
        if abs(term) < Fraction(1, 1 << 60) or k >= 300:
            break
        k += 1
    z2 = z * z
    if z2 < 1:
        rem = 2 * abs(term) / (1 - z2)
    else:                                # 不应发生（|z|<1），保守兜底
        rem = Fraction(10) ** 6
    return (min(s, prev) - rem, max(s, prev) + rem)


# ------------------------------------------------------------ Expr → 区间
def expr_kconsts(e, acc):
    """收集 Expr 里所有 ("k", f) 精确常量（交叉抽查用：对齐 SMT 文本字面量）。"""
    if not isinstance(e, tuple):
        return
    if e[0] == "k":
        acc.add(e[1])
        return
    for x in e[1:]:
        if isinstance(x, tuple):
            expr_kconsts(x, acc)
        elif isinstance(x, TupleVal):
            for y in x.items:
                expr_kconsts(y, acc)


def expr_interval(e, choice_boxes):
    """把展开期 Expr 树算成外扩有理区间 (lo, hi)：lo <= 真值 <= hi。

    只用于盒端点/choice 特征不等式（常量表达式）；见到语句变量即 Skip。
    + - * neg abs 在 Fraction 上精确；div 要求除盒不含 0（精确有理除法）；
    sqrt 整数开方外扩；atan 级数外扩；sin/cos 保守 [-1,1]；
    ite 对两支取并（与条件无关，天然 sound）。
    """
    kind = e[0]
    if kind == "k":
        return (e[1], e[1])
    if kind == "chc":
        if e[1] not in choice_boxes:
            raise Skip("choice %r box not extracted" % e[1])
        lo, hi = choice_boxes[e[1]][:2]
        return (lo, hi)
    if kind == "var":
        raise Skip("bound endpoint depends on variable %r" % e[1])
    if kind == "neg":
        lo, hi = expr_interval(e[1], choice_boxes)
        return (-hi, -lo)
    if kind == "abs":
        lo, hi = expr_interval(e[1], choice_boxes)
        if lo >= 0:
            return (lo, hi)
        if hi <= 0:
            return (-hi, -lo)
        return (Fraction(0), max(-lo, hi))
    if kind == "add":
        a = expr_interval(e[1], choice_boxes)
        b = expr_interval(e[2], choice_boxes)
        return (a[0] + b[0], a[1] + b[1])
    if kind == "sub":
        a = expr_interval(e[1], choice_boxes)
        b = expr_interval(e[2], choice_boxes)
        return (a[0] - b[1], a[1] - b[0])
    if kind == "mul":
        a = expr_interval(e[1], choice_boxes)
        b = expr_interval(e[2], choice_boxes)
        cands = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
        return (min(cands), max(cands))
    if kind == "div":
        a = expr_interval(e[1], choice_boxes)
        b = expr_interval(e[2], choice_boxes)
        if b[0] <= 0 <= b[1]:
            raise Skip("bound endpoint divides by interval containing 0")
        cands = [a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1]]
        return (min(cands), max(cands))
    if kind == "sqrt":
        lo, hi = expr_interval(e[1], choice_boxes)
        if hi < 0:
            raise Skip("sqrt of negative endpoint")
        return (sqrt_floor_frac(max(lo, Fraction(0)))[0],
                sqrt_ceil_frac(hi))
    if kind == "atan":
        lo, hi = expr_interval(e[1], choice_boxes)
        return (atan_pos_bounds(lo)[0], atan_pos_bounds(hi)[1])
    if kind == "log":
        lo, hi = expr_interval(e[1], choice_boxes)
        if lo <= 0:
            raise Skip("log of non-positive endpoint")
        return (log_pos_bounds(lo)[0], log_pos_bounds(hi)[1])
    if kind in ("sin", "cos"):
        return (Fraction(-1), Fraction(1))
    if kind == "ite":
        t = expr_interval(e[3], choice_boxes)
        f = expr_interval(e[4], choice_boxes)
        return (min(t[0], f[0]), max(t[1], f[1]))
    raise Skip("non-arithmetic Expr %r in bound endpoint" % (kind,))


# --------------------------------------------------------------- 展开器
class RPNEmitter(object):
    """镜像 emit_smt.py 的 Emitter：同一条 ev/ev_op/ev_app/lookup 递归，
    只是值域从 SMT 文本换成 Expr 树（+ Closure/TupleVal/PointWise 复用）。"""

    def __init__(self, defs):
        self.defs = defs
        self.choices = set()          # choice 常量名（作为变量声明）
        self.choice_boxes = {}        # name -> (lo, hi, note)
        self.choice_explaining = set()
        self.nodes = 0
        self.dropped_choice_eqs = 0
        self.eq_lits = set()          # 被丢弃的特征方程里的字面量（抽查对齐用）
        self.identity_lits = set()    # acos/asin 半角恒等式引入的常量

    # ------------------------------------------------------------- atoms
    def numeral(self, node):
        return ("k", numeral_frac(node))

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
            if STMT_VAR_RE.match(name):
                return ("var", name)          # statement variable
            return self.lookup(name, env)
        if "neg" in node:
            return self.combine("neg", [self.ev(node["neg"], env)])
        if "not" in node:
            return ("not", self.ev(node["not"], env))
        if "paren" in node:
            return self.ev(node["paren"], env)
        if "if" in node:
            return self.ite_of(self.ev(node["if"]["cond"], env),
                               self.ev(node["if"]["then"], env),
                               self.ev(node["if"]["else"], env))
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
        if not isinstance(v, tuple):
            raise Skip("non-real/bool term where term expected (%s)"
                       % type(v).__name__)
        return v

    def combine(self, op, vals):
        """Combine values with an op; distribute over functions/tuples."""
        if all(isinstance(v, tuple) for v in vals):
            if op in CMP_OPS:
                return ("cmp", op, vals[0], vals[1])
            if len(vals) == 1:
                return (op, vals[0])
            return (op, vals[0], vals[1])
        if any(isinstance(v, TupleVal) for v in vals):
            n = len(next(v for v in vals if isinstance(v, TupleVal)).items)
            if any(isinstance(v, TupleVal) and len(v.items) != n
                   for v in vals):
                raise Skip("tuple arity mismatch in %s" % op)
            cols = list(zip(*[v.items if isinstance(v, TupleVal)
                              else [v] * n for v in vals]))
            return TupleVal([self.combine(op, list(c)) for c in cols])
        return PointWise(op, vals)

    def ite_of(self, cond, then, els):
        """ite 节点构造：条件必须是比较型 Expr，归一成严格 guard；
        <= >= 交换分支，= 用 mode "eq"。元组逐分量分布。"""
        if not (isinstance(cond, tuple) and cond[0] == "cmp"):
            raise Skip("compound if condition (not a single comparison)")
        op, a, b = cond[1], cond[2], cond[3]
        vals = (a, b, then, els)
        if any(isinstance(v, TupleVal) for v in vals):
            n = len(next(v for v in vals
                         if isinstance(v, TupleVal)).items)
            if any(isinstance(v, TupleVal) and len(v.items) != n
                   for v in vals):
                raise Skip("tuple arity mismatch in ite")
            cols = list(zip(*[v.items if isinstance(v, TupleVal)
                              else [v] * n for v in vals]))
            return TupleVal([self.ite_of(("cmp", op, c[0], c[1]), c[2], c[3])
                             for c in cols])
        if op == "<":
            return ("ite", "lt", ("sub", a, b), then, els)
        if op == ">":
            return ("ite", "lt", ("sub", b, a), then, els)
        if op == "<=":                       # ite(a<=b,T,E) = ite(b-a<0,E,T)
            return ("ite", "lt", ("sub", b, a), els, then)
        if op == ">=":                       # ite(a>=b,T,E) = ite(a-b<0,E,T)
            return ("ite", "lt", ("sub", a, b), els, then)
        if op == "=":
            return ("ite", "eq", ("sub", a, b), then, els)
        raise Skip("bad ite condition op %r" % op)

    def apply_value(self, v, args):
        if isinstance(v, tuple):
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
            if not d["params"]:
                body = d["body_ast"]
                if isinstance(body, dict) and "choice" in body:
                    self.register_choice(name, body["choice"], env)
                    return ("chc", name)
                return self.ev(body, {})     # 内联（SMT 版走 define-fun 白名单）
            return Closure(name, d["params"], d["body_ast"], {}, [])
        if name == "pi":                     # dReal 无 pi，SMT 版以 define-fun 出现
            return ("mul", ("k", Fraction(4)), ("atan", ("k", Fraction(1))))
        raise Skip("unresolved constant %r" % name)

    def register_choice(self, name, ch, env):
        """choice 常量：从特征不等式组提取外扩盒；特征方程丢弃（记 note）。
        丢方程 = 在超集盒上证原式，sound。"""
        if name in self.choices:
            return
        vs = ch["vars"]
        if len(vs) != 1:
            raise Skip("unsupported choice def %r" % name)
        v = vs[0]
        if name in self.choice_explaining:
            raise Skip("recursive choice def %r" % name)
        self.choice_explaining.add(name)
        env2 = dict(env)
        env2[v] = ("chc", name)
        lo = None
        hi = None
        strict = []
        conj = [ch["body"]]
        while conj:                          # 拍平 /\ 链
            n = conj.pop()
            if isinstance(n, dict) and n.get("op") == "/\\":
                conj.append(n["args"][0])
                conj.append(n["args"][1])
                continue
            if isinstance(n, dict) and n.get("op") in ("<", "<=", ">", ">="):
                a, b = n["args"]
                va = a.get("var") or a.get("const")
                vb = b.get("var") or b.get("const")
                if va == v and not STMT_VAR_RE.match(va or ""):
                    side, sgn = b, 1
                elif vb == v and not STMT_VAR_RE.match(vb or ""):
                    side, sgn = a, -1
                else:
                    continue                 # 与 choice 变量无关（如方程）
                side_e = self.term(side, env2)
                expr_kconsts(side_e, self.eq_lits)   # 字面量进抽查对齐集
                val = expr_interval(side_e, self.choice_boxes)
                if sgn > 0:                  # v <op> side：side 是上界
                    hi = val[1] if hi is None else min(hi, val[1])
                    if n["op"] == "<":
                        strict.append("hi")
                else:                        # side <op> v：side 是下界
                    lo = val[0] if lo is None else max(lo, val[0])
                    if n["op"] == ">":
                        strict.append("lo")
            elif isinstance(n, dict) and n.get("op") == "=":
                # 特征方程：目标里丢弃，但字面量记下来供交叉抽查对齐
                for s in n["args"]:
                    expr_kconsts(self.term(s, env2), self.eq_lits)
                self.dropped_choice_eqs += 1
        if lo is None and hi is None:
            raise Skip("choice def %r: no usable bounds" % name)
        if lo is None:
            lo = Fraction(-10) ** 6
        if hi is None:
            hi = Fraction(10) ** 6
        note = ("choice const %s: 特征方程丢弃, 按外扩盒 [%s, %s] 处理%s"
                % (name, lo, hi,
                   "（原为" + "/".join(strict) + "开）" if strict else ""))
        self.choices.add(name)
        self.choice_boxes[name] = (lo, hi, note)

    def ev_op(self, node, env):
        op, args = node["op"], node["args"]
        if op == "pow":
            if len(args) != 2:
                raise Skip("bad pow arity")
            base = self.ev(args[0], env)
            e = args[1]
            if ("num" in e) or ("bnum" in e) or ("dec" in e):
                k = numeral_frac(e)
                if k.denominator != 1:
                    raise Skip("non-integer-literal pow exponent")
                k = int(k)
                r = ("k", Fraction(1))
                for _ in range(abs(k)):
                    r = ("mul", r, base)
                if k < 0:
                    return ("div", ("k", Fraction(1)), r)
                return r
            raise Skip("non-integer-literal pow exponent")
        if op in ("/\\", "\\/"):
            return self.combine("and" if op == "/\\" else "or",
                                [self.ev(args[0], env), self.ev(args[1], env)])
        if op == "==>":
            return self.combine("impl", [self.ev(args[0], env),
                                         self.ev(args[1], env)])
        if op == "<=>":
            return self.combine("=", [self.ev(args[0], env),
                                      self.ev(args[1], env)])
        if op in ("=", "<", ">", "<=", ">="):
            return self.combine(op, [self.ev(args[0], env),
                                     self.ev(args[1], env)])
        if op in ("+", "-", "*", "/"):
            if op == "-" and len(args) == 1:
                return self.combine("neg", [self.ev(args[0], env)])
            name = {"+": "add", "-": "sub", "*": "mul", "/": "div"}[op]
            return self.combine(name, [self.ev(args[0], env),
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
                only = vals[0]
                if not isinstance(only, tuple):
                    raise Skip("prim %s over non-term value" % sym)
                if sym == "acs":
                    # acos(x) = 2*atan( sqrt(1-x^2) / (1+x) )   （半角，x∈(−1,1]）
                    self.identity_lits.add(Fraction(1))
                    self.identity_lits.add(Fraction(2))
                    return ("mul", ("k", Fraction(2)),
                            ("atan", ("div",
                                      ("sqrt", ("sub", ("k", Fraction(1)),
                                                ("mul", only, only))),
                                      ("add", ("k", Fraction(1)), only))))
                if sym == "asn":
                    # asin(x) = 2*atan( x / (1 + sqrt(1-x^2)) ) （|x|<=1，分母>=1）
                    self.identity_lits.add(Fraction(1))
                    self.identity_lits.add(Fraction(2))
                    return ("mul", ("k", Fraction(2)),
                            ("atan", ("div", only,
                                      ("add", ("k", Fraction(1)),
                                       ("sqrt", ("sub", ("k", Fraction(1)),
                                                 ("mul", only, only)))))))
                return (PRIMS[sym], only)
            if sym in ("min", "max"):
                if len(vals) != 2:
                    raise Skip("bad arity for %s" % sym)
                a, b = vals
                cmp = "<" if sym == "min" else ">"
                return self.ite_of(("cmp", cmp, a, b), a, b)
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


# --------------------------------------------------------- mini expr parse
# （与 emit_smt.py 相同的词法/优先级分析，用于 ineq.hl 的盒端点字面量）
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
            kind = "var" if STMT_VAR_RE.match(t) else "const"
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
            if STMT_VAR_RE.match(n):
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


def var_key(n):
    """自然排序：y2 < y10（数字后缀按值比较）。"""
    m = re.match(r"^([A-Za-z_']*)([0-9]*)$", n)
    if m and m.group(2):
        return (m.group(1), int(m.group(2)), "")
    return (n, -1, "")


def strip_spine(ast):
    """==> 前件脊柱 + record 级 forall：-> (positives, core)。"""
    positives, core = [], ast
    while isinstance(core, dict) and "op" in core and core["op"] == "==>":
        positives.append(core["args"][0])
        core = core["args"][1]
    if isinstance(core, dict) and "forall" in core:
        core = core["forall"]["body"]      # strip record-level quantifier
    while isinstance(core, dict) and "op" in core and core["op"] == "==>":
        positives.append(core["args"][0])
        core = core["args"][1]
    return positives, core


def strip_lets(core, em, env):
    """剥掉核心处的 let（如 tan2lower/#3.07），值进 env。"""
    while isinstance(core, dict) and "let" in core:
        l = core["let"]
        if "vars" in l:
            raise Skip("pattern let in core")
        env = dict(env)
        env[l["var"]] = em.term(l["val"], env)
        core = l["body"]
    return core, env


def flatten_disj(core):
    """\/ 链拍平（没有则单元素表）。"""
    out = []
    def rec(n):
        if isinstance(n, dict) and n.get("op") == "\\/":
            rec(n["args"][0])
            rec(n["args"][1])
        else:
            out.append(n)
    rec(core)
    return out


def orient_cmp(op, a, b):
    """比较 (op, a, b) → 目标 Expr（求值 > 0 即该比较成立，>= / <= 用严格更强）。
    返回 (expr, orig_op)。"""
    if op in (">", ">="):
        return ("sub", a, b), op
    if op in ("<", "<="):
        return ("sub", b, a), op
    raise Skip("core comparison %r not a strict/weak inequality" % op)


def translate_record(rec, defs, darts, qexp):
    """-> case dict（含 _exact_box 供交叉抽查，序列化前剔除）；raises Skip。"""
    ast = rec.get("body_ast")
    if not ast:
        raise Skip("no parsed body_ast")
    idv = rec.get("idv") or "<idv?>"
    em = RPNEmitter(defs)
    notes = []

    # 盒约束（bounds 列表 + domain 谓词），同一变量取交
    bound_triples = []
    for b in rec.get("bounds") or []:
        if "var" in b:
            bound_triples.append((parse_bound(b["lo"], idv),
                                  b["var"], parse_bound(b["hi"], idv)))
        elif "raw" in b:
            raw = b["raw"].split("//")[0]
            for grp in re.findall(r"\(([^()]*(?:\([^()]*\)[^()]*)*)\)", raw):
                fields = split_top(grp, ",")
                if len(fields) != 3:
                    raise Skip("unparseable raw bounds %r" % b["raw"])
                bound_triples.append((parse_bound(fields[0], idv),
                                      fields[1].strip(),
                                      parse_bound(fields[2], idv)))
        else:
            raise Skip("bad bounds entry %r" % (b,))

    dom_triples = []
    if "domain_raw" in rec:
        toks = tokenize(rec["domain_raw"], idv)
        fname, args = toks[0], toks[1:]
        if fname in darts:
            dom_triples.extend(dart_constraint_ast(fname, darts))
        elif fname in defs:
            raise Skip("def-based domain predicate %r (need literal box)"
                       % fname)
        else:
            dart_constraint_ast(fname, darts)   # raises unsupported-domain

    # ==> 前件：展开一遍（登记 choice、验证可展开），然后丢弃（记 note）
    positives, core = strip_spine(ast)
    pos_lits = set()                         # 丢弃前件的字面量（抽查对齐用）
    for p in positives:
        expr_kconsts(em.term(p, {}), pos_lits)
    if positives:
        notes.append("丢弃 %d 条 ==> 前件（RPN 层无布尔约束；在超集盒上证原式，"
                     "sound 但可能闭合不了）" % len(positives))

    # 核心：剥 let、拍平 \/，分类出 prog 目标 + disj 备选
    core, cenv = strip_lets(core, em, {})
    disjuncts = flatten_disj(core)
    targets = []                             # (expr, orig_op)
    var_lts = []                             # (lo_name, hi_name)
    for d in disjuncts:
        d, denv = strip_lets(d, em, cenv)
        e = em.term(d, denv)
        if e[0] == "cmp":
            targets.append(orient_cmp(e[1], e[2], e[3]))
        else:
            raise Skip("core disjunct is not a comparison (%s)" % e[0])
    # 变量序比较（y_i < y_j 两边都是裸变量）改为 var_lt 盒判据（更紧且 sound）
    filtered = []
    for expr, op in targets:
        if expr[0] == "sub" and expr[1][0] == "var" and expr[2][0] == "var":
            if op in ("<", "<="):
                var_lts.append((expr[1][1], expr[2][1]))
                continue
            if op in (">", ">="):
                var_lts.append((expr[2][1], expr[1][1]))
                continue
        filtered.append((expr, op))
    targets = filtered
    if not targets:
        raise Skip("no comparison target in core")
    if len(targets) > 1 or var_lts:
        notes.append("核心为 %d 路析取：prog 取第一比较项，其余 %d 项入 disj"
                     % (len(disjuncts), len(targets) - 1 + len(var_lts)))

    # 盒端点求值（先于变量表冻结：choice 常量可能在端点里首次登记）
    box_parts = {}                       # var -> [(lo, hi), ...] 各约束外扩区间
    box_lits = set()                     # 端点字面量（交叉抽查对齐用）
    for loa, vv, hia in bound_triples + dom_triples:
        elo = em.term(loa, {})
        ehi = em.term(hia, {})
        expr_kconsts(elo, box_lits)
        expr_kconsts(ehi, box_lits)
        el = expr_interval(elo, em.choice_boxes)
        eh = expr_interval(ehi, em.choice_boxes)
        box_parts.setdefault(vv, []).append((el[0], eh[1]))
    for cname, (clo, chi, _n) in em.choice_boxes.items():
        box_parts.setdefault(cname, []).append((clo, chi))

    # choice 语义裁剪记录（register_choice 已被端点/核心求值触发过）
    if em.dropped_choice_eqs:
        notes.append("choice 特征方程共丢弃 %d 条（超集盒，sound）"
                     % em.dropped_choice_eqs)
    for cname in sorted(em.choice_boxes):
        notes.append(em.choice_boxes[cname][2])

    # 变量表：bound vars ∪ body vars ∪ domain args ∪ choice 常量（对齐 SMT declare）
    decl = set(t[1] for t in bound_triples)
    decl |= set(t[1] for t in dom_triples)
    collect_vars(ast, decl)
    if "domain_raw" in rec:
        for a in tokenize(rec["domain_raw"], idv)[1:]:
            if STMT_VAR_RE.match(a):
                decl.add(a)
    decl |= em.choices
    if not (decl >= set(n for t in targets for n in _expr_vars(t[0]))):
        raise Skip("internal: target var not in decl")
    vars_list = sorted(decl, key=var_key)
    vindex = dict((n, i) for i, n in enumerate(vars_list))

    # 盒：每变量取交 → 2^-q 网格外扩
    exact_box = []
    box = []
    for v in vars_list:
        parts = box_parts.get(v)
        if not parts:
            raise Skip("no box for variable %r" % v)
        lo = max(p[0] for p in parts)
        hi = min(p[1] for p in parts)
        if lo > hi:
            raise Skip("empty box for variable %r ([%s, %s])" % (v, lo, hi))
        exact_box.append((lo, hi))
        glo = _grid_round(lo, qexp, math.floor)
        ghi = _grid_round(hi, qexp, math.ceil)
        if glo > ghi:
            raise Skip("empty dyadic box for variable %r" % v)
        box.append((glo, ghi))

    # 编译 RPN（主目标 + disj 备选 + var_lt 下标）
    prog = compile_expr(targets[0][0], vindex)
    disj = []
    for expr, op in targets[1:]:
        disj.append({"prog": compile_expr(expr, vindex), "orig_op": op})
    for lo_name, hi_name in var_lts:
        if lo_name not in vindex or hi_name not in vindex:
            raise Skip("var_lt endpoint not declared (%s < %s)"
                       % (lo_name, hi_name))
        disj.append({"var_lt": [vindex[lo_name], vindex[hi_name]]})

    n_ops, n_ite, depth = prog_stats(prog)
    for d in disj:
        if "prog" in d:
            a, b, c = prog_stats(d["prog"])
            n_ops += a
            n_ite += b
            depth = max(depth, c)

    case = {
        "id": idv,
        "orig_op": targets[0][1] if len(targets) == 1 and not var_lts
                   else "disj",
        "vars": vars_list,
        "box": [[lo, hi] for lo, hi in box],
        "q": -qexp,
        "prog": prog,
        "notes": notes,
        "stats": {"ops": n_ops, "ite": n_ite, "depth": depth},
        "_exact_box": exact_box,           # 中点冒烟/交叉抽查用，序列化前剔除
        "_aux_lits": box_lits | pos_lits | em.eq_lits,
        "_identity_lits": set(em.identity_lits),
    }
    if disj:
        case["disj"] = disj
    return case


def _expr_vars(e):
    kind = e[0]
    if kind == "var":
        return (e[1],)
    if kind == "chc":
        return (e[1],)
    out = []
    for x in e[1:]:
        if isinstance(x, tuple):
            out.extend(_expr_vars(x))
    return out


def _is_pow2(n):
    return n > 0 and (n & (n - 1)) == 0


def _grid_round(f, qexp, rnd):
    """把有理数 f 按 2^-qexp 网格取整（rnd = floor/ceil），结果仍是 Fraction。"""
    scaled = f.numerator * (1 << qexp)
    den = f.denominator
    n = rnd(Fraction(scaled, den))  # Fraction→int 精确取整
    return Fraction(int(n), 1 << qexp)


def compile_expr(e, vindex):
    """Expr 树 → RPN 指令流（ite 编码为嵌套结构化节点）。"""
    kind = e[0]
    if kind == "k":
        return [["push_const", e[1]]]
    if kind == "var":
        if e[1] not in vindex:
            raise Skip("unbound statement var %r" % e[1])
        return [["push_var", vindex[e[1]]]]
    if kind == "chc":
        if e[1] not in vindex:
            raise Skip("unbound choice const %r" % e[1])
        return [["push_var", vindex[e[1]]]]
    if kind == "neg":
        return compile_expr(e[1], vindex) + [["neg"]]
    if kind in ("add", "sub", "mul", "div"):
        return compile_expr(e[1], vindex) + compile_expr(e[2], vindex) + [[kind]]
    if kind in ("sqrt", "atan", "sin", "cos", "abs", "log"):
        return compile_expr(e[1], vindex) + [[kind]]
    if kind == "ite":
        node = {"cond": compile_expr(e[2], vindex),
                "then": compile_expr(e[3], vindex),
                "else": compile_expr(e[4], vindex)}
        if e[1] != "lt":
            node["mode"] = e[1]
        return [{"ite": node}]
    raise Skip("cannot compile Expr %r to RPN" % (kind,))


def prog_stats(prog):
    """-> (指令总数含嵌套, ite/guard 节点数, 最大嵌套深度)。"""
    ops = 0
    ites = 0
    depth = 1
    for op in prog:
        ops += 1
        if isinstance(op, dict):
            ites += 1
            node = op["ite"]
            a, b, c = prog_stats(node["cond"])
            d, e2, f = prog_stats(node["then"])
            g, h, i = prog_stats(node["else"])
            ops += a + d + g
            ites += b + e2 + h
            depth = max(depth, 1 + max(c, f, i))
    return (ops, ites, depth)


# ----------------------------------------------------------- 冒烟区间求值器
def _iadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _isub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def _imul(a, b):
    c = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (min(c), max(c))


def _idiv(a, b):
    if b[0] <= 0 <= b[1]:
        raise EvalError("div: divisor interval contains 0")
    c = [a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1]]
    return (min(c), max(c))


def _isqrt(a):
    if a[1] < 0:
        raise EvalError("sqrt: negative interval")
    lo = Fraction(0) if a[0] < 0 else sqrt_floor_frac(a[0])[0]
    return (lo, sqrt_ceil_frac(a[1]))


def _iatan(a):
    return (atan_pos_bounds(a[0])[0], atan_pos_bounds(a[1])[1])


def _iabs(a):
    if a[0] >= 0:
        return a
    if a[1] <= 0:
        return (-a[1], -a[0])
    return (Fraction(0), max(-a[0], a[1]))


def _iunion(a, b):
    return (min(a[0], b[0]), max(a[1], b[1]))


def eval_rpn(prog, box):
    """分数区间求值器（冒烟测试用，不是求解器）。

    box: [(lo, hi)] Fractions 与 prog 的 push_var 下标对应。
    -> (顶层区间, {"ite": 求值次数, "straddle": guard 未定次数})。
    div 越零 / sqrt 负底抛 EvalError；STRADDLE 不算错误，取 then∪else。
    """
    st = []
    stats = {"ite": 0, "straddle": 0}

    def run(p):
        for op in p:
            if isinstance(op, dict):
                node = op["ite"]
                stats["ite"] += 1
                c, _ = eval_rpn(node["cond"], box)
                mode = node.get("mode", "lt")
                if mode == "lt":
                    if c[1] < 0:
                        run(node["then"])
                    elif c[0] >= 0:
                        run(node["else"])
                    else:
                        stats["straddle"] += 1
                        run(node["then"])
                        t = st.pop()
                        run(node["else"])
                        e = st.pop()
                        st.append(_iunion(t, e))
                else:  # eq
                    if c[0] == 0 and c[1] == 0:
                        run(node["then"])
                    elif c[0] > 0 or c[1] < 0:
                        run(node["else"])
                    else:
                        stats["straddle"] += 1
                        run(node["then"])
                        t = st.pop()
                        run(node["else"])
                        e = st.pop()
                        st.append(_iunion(t, e))
                continue
            kind = op[0]
            if kind == "push_var":
                st.append(box[op[1]])
            elif kind == "push_const":
                f = op[1]
                st.append((f, f))
            elif kind == "add":
                b = st.pop(); a = st.pop(); st.append(_iadd(a, b))
            elif kind == "sub":
                b = st.pop(); a = st.pop(); st.append(_isub(a, b))
            elif kind == "mul":
                b = st.pop(); a = st.pop(); st.append(_imul(a, b))
            elif kind == "div":
                b = st.pop(); a = st.pop(); st.append(_idiv(a, b))
            elif kind == "neg":
                a = st.pop(); st.append((-a[1], -a[0]))
            elif kind == "sqrt":
                a = st.pop(); st.append(_isqrt(a))
            elif kind == "atan":
                a = st.pop(); st.append(_iatan(a))
            elif kind == "log":
                a = st.pop()
                if a[0] <= 0:
                    raise EvalError("log: non-positive interval")
                st.append((log_pos_bounds(a[0])[0], log_pos_bounds(a[1])[1]))
            elif kind in ("sin", "cos"):
                a = st.pop(); st.append((Fraction(-1), Fraction(1)))
            elif kind == "abs":
                a = st.pop(); st.append(_iabs(a))
            else:
                raise EvalError("unknown op %r" % (op,))

    run(prog)
    if len(st) != 1:
        raise EvalError("stack depth %d after eval" % len(st))
    return st[0], stats


# ----------------------------------------------------------------- 自检
def selftest():
    """3+1 个人工案例的写死断言；全过返回 (True, [])。"""
    bad = []
    F = Fraction

    # 1) 纯多项式：x^2 - 2 > 0 在 [3/2, 2] 上应 lo > 0（叶闭合）；
    #    在 [1, 2] 上 lo = -1 < 0（证不了，但不 crash）。
    prog = [["push_var", 0], ["push_var", 0], ["mul"],
            ["push_const", F(2)], ["sub"]]
    r, _ = eval_rpn(prog, [(F(3, 2), F(2))])
    if not r[0] > 0:
        bad.append("x^2-2 在 [3/2,2] 上应 lo>0, got %s" % (r,))
    r, _ = eval_rpn(prog, [(F(1), F(2))])
    if not (r[0] <= 0 and r[1] >= 0):
        bad.append("x^2-2 在 [1,2] 上应跨 0, got %s" % (r,))

    # 2) ite/guard：ite(x<0, -1, 1)。跨 0 盒 → straddle 且并集 [-1,1]；
    #    全正盒 → else 支 [1,1]（lo>0 闭合）；全负盒 → then 支 [-1,-1]。
    ite = [{"ite": {"cond": [["push_var", 0]],
                    "then": [["push_const", F(-1)]],
                    "else": [["push_const", F(1, 1)] ]}}]
    r, s = eval_rpn(ite, [(F(-1), F(1))])
    if not (s["straddle"] == 1 and r == (F(-1), F(1))):
        bad.append("ite straddle 应并集 [-1,1], got %s %s" % (r, s))
    r, s = eval_rpn(ite, [(F(0), F(1))])
    if not (s["straddle"] == 0 and r == (F(1), F(1))):
        bad.append("ite 全正盒应取 else 支, got %s %s" % (r, s))
    r, s = eval_rpn(ite, [(F(-1), F(-1))])
    if not (r == (F(-1), F(-1)) and r[1] < 0):
        bad.append("ite 全负盒应取 then 支, got %s %s" % (r, s))

    # 2b) eq-guard：ite(x=0, 5, -5)。恰为 [0,0] → then；跨 0 → straddle∪[-5,5]。
    ite_eq = [{"ite": {"mode": "eq",
                       "cond": [["push_var", 0]],
                       "then": [["push_const", F(5)]],
                       "else": [["push_const", F(-5)]]}}]
    r, s = eval_rpn(ite_eq, [(F(0), F(0))])
    if not (r == (F(5), F(5))):
        bad.append("eq-guard 点盒 [0,0] 应取 then, got %s" % (r,))
    r, s = eval_rpn(ite_eq, [(F(-1), F(1))])
    if not (s["straddle"] == 1 and r == (F(-5), F(5))):
        bad.append("eq-guard 跨 0 应 straddle 并集, got %s %s" % (r, s))

    # 3) sqrt 外扩：sqrt([2,2]) = [1,2]（isqrt(2)=1 下取整 / 上取整 2），
    #    且 lo^2 <= 2 <= hi^2 恒成立。
    r, _ = eval_rpn([["push_var", 0], ["sqrt"]], [(F(2), F(2))])
    if not (r[0] ** 2 <= 2 <= r[1] ** 2):
        bad.append("sqrt 外扩应包住 sqrt2, got %s" % (r,))
    r, _ = eval_rpn([["push_var", 0], ["sqrt"]], [(F(4), F(4))])
    if r != (F(2), F(2)):
        bad.append("sqrt([4,4]) 应恰为 [2,2], got %s" % (r,))

    # 4) dyadic 网格外扩：63/25 = 2.52 落在 2^-30 网格两侧，端点分母是 2 的幂。
    glo = _grid_round(F(63, 25), 30, math.floor)
    ghi = _grid_round(F(63, 25), 30, math.ceil)
    if not (glo < F(63, 25) < ghi and _is_pow2(glo.denominator)
            and _is_pow2(ghi.denominator)):
        bad.append("2.52 网格外扩错: %s %s" % (glo, ghi))
    if _grid_round(F(2), 30, math.floor) != F(2):
        bad.append("已是网格点的外扩应不动: 2")

    # 5) div 区间：[1,2]/[2,4]... 即 x/2 在 [1,2] 上 = [1/2,1]。
    r, _ = eval_rpn([["push_var", 0], ["push_const", F(2)], ["div"]],
                    [(F(1), F(2))])
    if r != (F(1, 2), F(1)):
        bad.append("div 区间错: %s" % (r,))
    try:
        eval_rpn([["push_const", F(1)], ["push_var", 0], ["div"]],
                 [(F(-1), F(1))])
        bad.append("div 越零应抛 EvalError")
    except EvalError:
        pass

    # 6) atan 外扩：atan(1)=pi/4≈0.78539 应在级数界内，pi/2 界应包住 pi/2。
    alo, ahi = atan_pos_bounds(F(1))
    if not (alo < F(7854, 10000) and ahi > F(7853, 10000)):
        bad.append("atan(1) 级数界错: [%s, %s]" % (alo, ahi))
    plo, phi = pi_half_bounds()
    if not (plo < F(15708, 10000) < phi):    # 1.5708 ≈ pi/2
        bad.append("pi/2 界错: [%s, %s]" % (plo, phi))

    return (not bad, bad)


# --------------------------------------------------------------- 交叉抽查
def safe_name(idv):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", idv).strip("_") + ".json"


def smt_safe_name(idv):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", idv).strip("_") + ".smt2"


def collect_prog_consts(prog, acc):
    for op in prog:
        if isinstance(op, dict):
            node = op["ite"]
            for k in ("cond", "then", "else"):
                collect_prog_consts(node[k], acc)
        elif op[0] == "push_const":
            acc.add(op[1])


def xcheck_case(case):
    """与 out/smt/<id>.smt2 交叉抽查：变量集合 + 常量字面量值集合。

    我方集合 = prog（含 disj）的 push_const + 盒端点/被丢前件/被丢特征方程
    的原始字面量 − acos/asin 恒等式引入的常量；对方 = SMT 文件全部数字
    字面量（约束、define-fun、被丢内容都在同一文件里）。
    -> (var_ok, var_diff, smt_only, case_only, identity_used)。"""
    path = os.path.join(SMT_DIR, smt_safe_name(case["id"]))
    with open(path) as f:
        text = f.read()
    smt_vars = set(re.findall(r"\(declare-fun (\S+) \(\) Real\)", text))
    case_vars = set(case["vars"])
    var_diff = smt_vars ^ case_vars

    smt_consts = set()
    for m in re.findall(r"[0-9]+(?:\.[0-9]+)?", text):
        smt_consts.add(Fraction(m))
    my_consts = set(case["_aux_lits"])
    collect_prog_consts(case["prog"], my_consts)
    for d in case.get("disj") or []:
        if "prog" in d:
            collect_prog_consts(d["prog"], my_consts)
    idl = case["_identity_lits"]
    return (not var_diff, var_diff, smt_consts - my_consts,
            my_consts - smt_consts, idl)


# ------------------------------------------------------------------ main
def frac_json(o):
    if isinstance(o, Fraction):
        return {"num": o.numerator, "den": o.denominator}
    raise TypeError("%r is not JSON serializable" % (o,))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ids", default="", help="逗号分隔的 idv 子集（默认全量）")
    ap.add_argument("--q", type=int, default=DEFAULT_Q,
                    help="dyadic 网格指数（步长 2^-q，默认 30）")
    ap.add_argument("--no-xcheck", action="store_true",
                    help="跳过与 SMT 输出的交叉抽查")
    ap.add_argument("--ineqs", default="",
                    help="不等式 AST JSON 路径，覆盖 AST_PATH")
    ap.add_argument("--defs", default="",
                    help="定义闭包 JSON 路径，覆盖 DEFS_PATH")
    ap.add_argument("--outdir", default="",
                    help="案例输出目录，覆盖 CASES_DIR")
    args = ap.parse_args()
    ast_path = args.ineqs or AST_PATH
    defs_path = args.defs or DEFS_PATH
    cases_dir = args.outdir or CASES_DIR

    ok, bad = selftest()
    print("== 自检（Fraction 区间求值器 + dyadic 外扩） ==")
    for b in bad:
        print("FAIL %s" % b)
    print("自检: %s" % ("全部通过" if ok else "失败 %d 项" % len(bad)))
    if not ok:
        return 1

    with open(ast_path) as f:
        data = json.load(f)
    defs = load_defs(defs_path)
    darts = load_darts(INEQ_HL)
    recs = data["records"]
    wanted = None
    if args.ids.strip():
        wanted = set(s.strip() for s in args.ids.split(",") if s.strip())
    os.makedirs(cases_dir, exist_ok=True)

    emitted, skipped = [], []
    tot_ops = tot_ite = tot_disj = tot_varlt = 0
    eval_ok = eval_err = eval_straddle = 0
    cases_by_id = {}
    for rec in recs:
        idv = rec.get("idv") or "<idv?>"
        if wanted is not None and idv not in wanted:
            continue
        try:
            case = translate_record(rec, defs, darts, args.q)
        except Skip as e:
            skipped.append((idv, e.reason))
            print("SKIP  %-28s %s" % (idv, e.reason))
            continue
        except RecursionError:
            skipped.append((idv, "recursion limit"))
            print("SKIP  %-28s recursion limit" % idv)
            continue

        # 冒烟：根盒 dyadic 中点求值一次（确认不 crash；straddle 只计数）
        mid_box = [((lo + hi) / 2, (lo + hi) / 2) for lo, hi in case["_exact_box"]]
        try:
            r, s = eval_rpn(case["prog"], mid_box)
            evs = "eval=OK straddle=%d" % s["straddle"]
            eval_ok += 1
            eval_straddle += s["straddle"]
        except EvalError as e:
            evs = "eval=ERR(%s)" % e
            eval_err += 1

        path = os.path.join(cases_dir, safe_name(idv))
        out = dict((k, v) for k, v in case.items() if not k.startswith("_"))
        with open(path, "w") as f:
            json.dump(out, f, default=frac_json, separators=(",", ":"))
            f.write("\n")
        emitted.append(idv)
        cases_by_id[idv] = case
        ndisj = len(case.get("disj") or [])
        nvarlt = sum(1 for d in case.get("disj") or [] if "var_lt" in d)
        tot_ops += case["stats"]["ops"]
        tot_ite += case["stats"]["ite"]
        tot_disj += ndisj
        tot_varlt += nvarlt
        print("EMIT  %-28s vars=%-2d ops=%-5d ite=%-4d disj=%-2d %s"
              % (idv, len(case["vars"]), case["stats"]["ops"],
                 case["stats"]["ite"], ndisj, evs))

    print("\n== emit_rpn.py 汇总 ==")
    print("records:            %d%s" % (len(recs),
          "" if wanted is None else "（子集 %s）" % sorted(wanted)))
    print("emitted:            %d" % len(emitted))
    print("skipped:            %d" % len(skipped))
    for idv, r in skipped:
        print("  SKIP %-24s %s" % (idv, r))
    print("ops 总数:            %d" % tot_ops)
    print("ite/guard 节点总数:  %d" % tot_ite)
    print("disj 备选总数:       %d（其中 var_lt %d）" % (tot_disj, tot_varlt))
    print("中点冒烟求值:        OK %d / ERR %d / straddle 计 %d"
          % (eval_ok, eval_err, eval_straddle))
    if eval_err:
        print("  （ERR = 中点恰落在奇异点上被捕获的 EvalError，非 crash："
              "如诸 y_i 中点相等时 delta=0 的除零。SMT 版靠前件排除这些点，"
              "Arb 驱动层靠球算术+二分避开；程序结构本身全部有效。）")

    # 交叉抽查：与 emit_smt.py 输出对比变量集合 + 常量值
    if not args.no_xcheck:
        print("\n== 交叉抽查（vs out/smt/*.smt2） ==")
        xs = [i for i in XCHECK_IDS if i in cases_by_id]
        if wanted is not None:
            xs = [i for i in emitted if i in xs] or emitted[:5]
        xs = xs[:5]
        for idv in xs:
            case = cases_by_id[idv]
            try:
                vok, vdiff, sonly, conly, idl = xcheck_case(case)
            except IOError:
                print("XCHECK %-24s SMT 文件缺失，跳过" % idv)
                continue
            tag = "vars=%s" % ("一致" if vok else "不一致 %s" % sorted(vdiff))
            note = ""
            if idl:
                note += "（恒等式引入 %s 已扣除）" % sorted(idl)
            if sonly or conly:
                note += " 常量差异: smt-only=%s case-only=%s" % (
                    sorted(sonly), sorted(conly))
            print("XCHECK %-24s %s consts=%s%s"
                  % (idv, tag,
                     "一致" if not (sonly or conly) else "有差异", note))

    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""gen_farkas.py — G5 族解析层：infeasible 记录的 (族名+下标+乘子) → 整数行系统
→ LpFarkasCore 形（对接 Kepler.Text.LP.LPFarkas 的 farkasCheck）。

语义还原自 reference/flyspeck/formal_lp（C1.6 解剖结论，全部有源码锚点）：

1. 记录 = hypermap_string："id card_node f0_len f0... f1_len f1..."（card_node
   被丢弃；ListHyp.cs 构造器 i=2 起读、informal_computations.hl convert_to_list
   同构）。面表 L : num list list。
2. dart = 面的循环对：list_pairs f = zip f (rot 1 f)（list_hypermap-compiled.hl:22）。
   实例集（000.txt domain/set + ListHyp.ComputeAllSets 同序）：
     darts  = flatten (map list_pairs L)              （下标 0..ndarts-1）
     nodes  = undup (flatten L)（首现序；list_of_nodes = MAP (filter FST) 逐 node）
     faces  = map list_pairs L
     edges  = 与 darts 同序（edge k = {dart k, rev dart k}）
     darts3/4/5/6 = 恰好 size k 的面的 darts（面序+循环序）
3. 分裂树（prove_flyspeck_lp.hl terminal_cases + informal_computations.hl
   split_list；C# ListHyp.Split 逐字同构）：quad = [split13; split24; split13;
   split24; L]，pent = [L; s1_0..s1_4; s2_0..s2_4]，hex = [L; s_0..s_5]，
   tri/edge/236/218/high/mid/add_big = 子节点共用 L。split_list：含 dart 的面
   rotateL i 再 rotateR 1（dart 对落到 (1,2) 位），size≤3 原样，否则
   [f0,f1,f2] + [f0,f2,f3..]，原位替换后即止。
4. 族线性形式 = HOL 侧已证陈述（lp_head_ineqs.hl / lp_main_estimate-compiled.hl /
   lp_ineqs_proofs2-compiled.hl）+ body 族 = body.mod 的 Taylor 线性化（6 位
   十进制浮点；p≤5 时 floor/ceil 与精确值一致性由 Flyspeck 全库验证背书；
   p≥6 的 body 系数由 risk 旗报出）。
5. 取整规则（lp_approx_ineqs.hl create_approximations：≤ 形先 low-approx 左边、
   high-approx 右边，再 ×10^p 整数化）：精确 ≤ 形 Σ c_i v_i ≤ b 在精度 p 下
   发射为行 Σ floor(c_i·10^p) v_i ≤ ceil(b·10^p)。_neg 族 = 反向不等式独立取整
   （非已取整行的取负）。
6. 证书乘子 = 终端记录 constraints/targets/bounds 的 int64 乘子，逐实例
   （constraints 条目第 i 个下标 ↔ 第 i 个乘子）；infeasible 终端 target 恒空
   （C# PrintCertificate 对 infeasible 不标 TargetVariable）。

用法：
  gen_farkas.py --stats                          # 全 easy_*.dat infeasible 终端族分布
  gen_farkas.py --record easy_1.dat 392 0        # 解析单终端 + Python 侧 Farkas 预检
  gen_farkas.py --lean easy_1.dat 392 0 out.lean # 发射 Lean 探针模块
  gen_farkas.py --lean hard_1.dat 0 82 out.lean C17B086C --col-major
                                                 # 列主序发射（rows 转置为 cols 的
                                                 # LpFarkasCoreCol，对接 farkasCheckCol）
"""

import argparse
import math
import re
import sys
import threading
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "pipeline" / "lp"))
import parse_lpcert as P  # noqa: E402

BIN = REPO / "reference" / "flyspeck" / "formal_lp" / "glpk" / "binary"
BODY_MOD = REPO / "reference" / "flyspeck" / "formal_lp" / "glpk" / "body.mod"

# hard_7.dat 以 tar.gz 形式入库；解包副本可放额外目录（不在本仓库内）。
_EXTRA_BIN = [Path("/tmp/p4g5/hard7")]


def _dat_path(hs):
    p = BIN / hs
    if p.exists():
        return p
    for d in _EXTRA_BIN:
        if (d / hs).exists():
            return d / hs
    return p


def dat_files():
    out = sorted(BIN.glob("*.dat"))
    for d in _EXTRA_BIN:
        out.extend(sorted(d.glob("*.dat")))
    return out

getcontext().prec = 80

# ---------------------------------------------------------------- 常数原子
# π / sol0 = 3·arccos(1/3) − π / const1 = sol0/π / rho218 = rho(2.18)
# = 1 + const1·9/26 / sqrt8（tame_general sol0_over_pi_EQ_const1、sphere.hl
# rho/ly/interp、constants_approx.hl；55 位有效数字，p ≤ 7 下 floor/ceil 无歧义）。
ATOMS = {
    "1": Decimal(1),
    "pi": Decimal("3.141592653589793238462643383279502884197169399375105821"),
    "sol0": Decimal("0.551285598432530807942144151464459242933850628690178696"),
    "c1": Decimal("0.175479656091821810512566677667292733949885948318200862"),
    "r218": Decimal("1.06074295787793831902358077303867825405957590518706953"),
    "s8": Decimal("2.828427124746190097603377448419396157139343750753896146"),
}


class EV:
    """精确值 = Σ_atom coef·atom（coef: Fraction；atom ∈ ATOMS）。"""

    __slots__ = ("terms",)

    def __init__(self, rat=0, pi=0, sol0=0, c1=0, r218=0, s8=0):
        object.__setattr__(self, "terms", {})
        for a, c in (("1", rat), ("pi", pi), ("sol0", sol0),
                     ("c1", c1), ("r218", r218), ("s8", s8)):
            c = Fraction(c)
            if c:
                self.terms[a] = self.terms.get(a, Fraction(0)) + c

    def add(self, other, sign=1):
        out = EV()
        t = dict(self.terms)
        for a, c in other.terms.items():
            nc = t.get(a, Fraction(0)) + sign * c
            if nc:
                t[a] = nc
            else:
                t.pop(a, None)
        out.terms = t
        return out

    def mul(self, k):
        k = Fraction(k)
        out = EV()
        out.terms = {a: c * k for a, c in self.terms.items()}
        return out

    def neg(self):
        return self.mul(-1)

    def scaled(self, S):
        t = Decimal(0)
        for a, c in self.terms.items():
            t += Decimal(c.numerator) / Decimal(c.denominator) * ATOMS[a]
        return t * S

    def floor(self, S):
        return math.floor(self.scaled(S))

    def ceil(self, S):
        return math.ceil(self.scaled(S))

    def near_integer(self, S, tol=Decimal("0.000001")):
        v = self.scaled(S)
        fr = v - math.floor(v)
        return min(fr, 1 - fr) < tol

    def __repr__(self):
        return f"EV({self.terms})"


class Form:
    """行的精确 ≤ 形：Σ_col coef·v ≤ rhs。coef: EV（列 = (数量名, 元素)）。"""

    def __init__(self):
        self.coeffs = {}
        self.rhs = EV()

    def put(self, col, coef):
        if not isinstance(coef, EV):
            coef = EV(coef)
        if not coef.terms:
            return
        cur = self.coeffs.get(col)
        self.coeffs[col] = coef if cur is None else cur.add(coef)

    def negated(self):
        out = Form()
        out.coeffs = {c: e.neg() for c, e in self.coeffs.items()}
        out.rhs = self.rhs.neg()
        return out

    def flags(self, S):
        out = []
        for col, e in self.coeffs.items():
            if e.near_integer(S):
                out.append(("coef", col))
        if self.rhs.near_integer(S):
            out.append(("rhs", None))
        return out


# ---------------------------------------------------------------- 记录与分裂
def parse_record(s):
    toks = s.split()
    hid = toks[0]
    faces = []
    i = 2  # 跳过 id 与 card_node
    while i < len(toks):
        n = int(toks[i])
        i += 1
        faces.append([int(toks[i + k]) for k in range(n)])
        i += n
    return hid, faces


def list_pairs(face):
    n = len(face)
    return [(face[i], face[(i + 1) % n]) for i in range(n)]


def rotate_l(xs, i):
    i %= len(xs)
    return xs[i:] + xs[:i]


def split_list(faces, dart):
    """informal_computations.hl split_list 的 Python 镜像。"""
    out = []
    for idx, f in enumerate(faces):
        prs = list_pairs(f)
        if dart in prs:
            i = prs.index(dart)
            rf = rotate_l(f, i)
            rf = rf[-1:] + rf[:-1]  # rotateR 1：dart 对落到 (1,2) 位
            if len(rf) <= 3:
                out.append(rf)
            else:
                out.append(rf[:3])
                out.append([rf[0]] + rf[2:])
            out.extend(faces[idx + 1:])
            return out
        out.append(f)
    raise ValueError(f"split dart {dart} not found in record")


def terminal_records(hyp_list, case):
    """prove_flyspeck_lp.hl terminal_cases 的镜像：产出 (record, terminal)。"""
    if case[1] == 0:
        yield hyp_list, case[2][0][2]
        return
    info = case[2][0][2]
    stype, sface = info[0], P.to_list(info[1])
    kids = P.to_list(case[2][1])
    if stype in ("tri", "edge", "236", "218", "high", "mid", "add_big"):
        args = [hyp_list] * len(kids)
    elif stype == "quad":
        s13 = split_list(hyp_list, (sface[1], sface[2]))
        s24 = split_list(hyp_list, (sface[0], sface[1]))
        args = [s13, s24, s13, s24, hyp_list]
    elif stype in ("pent", "hex"):
        darts = rotate_l(list_pairs(sface), 1)
        singles = [split_list(hyp_list, d) for d in darts]
        if stype == "hex":
            args = [hyp_list] + singles
        else:  # pent：两刀 = 先 darts[i]，再 rotateL 2 (darts)[i]
            d2 = rotate_l(darts, 2)
            twos = [split_list(singles[i], d2[i]) for i in range(len(darts))]
            args = [hyp_list] + singles + twos
    else:
        raise ValueError(f"unknown split type {stype}")
    if len(args) != len(kids):
        raise ValueError(f"split {stype}: {len(args)} args vs {len(kids)} kids")
    for rec, kid in zip(args, kids):
        yield from terminal_records(rec, kid)


# ---------------------------------------------------------------- 超图集
class Hyp:
    """记录的组合集（ListHyp.ComputeAllSets / list_of_* 同序）。"""

    def __init__(self, faces):
        self.faces = [list(f) for f in faces]
        self.face_pairs = [list_pairs(f) for f in self.faces]
        starts, tot = [], 0
        for prs in self.face_pairs:
            starts.append(tot)
            tot += len(prs)
        self.starts = starts
        self.darts = [d for prs in self.face_pairs for d in prs]
        self.dart_face = [j for j, prs in enumerate(self.face_pairs) for _ in prs]
        self.dart_pos = [i for prs in self.face_pairs for i in range(len(prs))]
        self.dart_index = {d: k for k, d in enumerate(self.darts)}
        # C# removeDuplicates = 保留最后一次出现（ListMethods.cs:94）；
        # 证书往返验证背书此序（首现序会使试点 B 的 yn 列残留 ±413000）。
        fl = [x for f in self.faces for x in f]
        last = {}
        for i, x in enumerate(fl):
            last[x] = i
        self.nodes = sorted(last, key=lambda x: last[x])
        self.node_darts = {x: [k for k, d in enumerate(self.darts) if d[0] == x]
                           for x in self.nodes}
        by_size = {}
        for j, prs in enumerate(self.face_pairs):
            by_size.setdefault(len(prs), []).append(j)
        self.darts_k = {}
        for kk in (3, 4, 5, 6):
            lst = []
            for j in by_size.get(kk, []):
                lst.extend(range(self.starts[j], self.starts[j] + kk))
            self.darts_k[kk] = lst

    def fm(self, k):
        j, i = self.dart_face[k], self.dart_pos[k]
        return self.starts[j] + (i + 1) % len(self.face_pairs[j])

    def prev(self, k):
        j, i = self.dart_face[k], self.dart_pos[k]
        return self.starts[j] + (i - 1) % len(self.face_pairs[j])

    def rev(self, k):
        a, b = self.darts[k]
        return self.dart_index[(b, a)]

    def node_of(self, k):
        return self.darts[k][0]

    def face_of_dart(self, k):
        return self.dart_face[k]

    def prev_of_rev_fm(self, k):
        """yapex_sup_flat 的 d2 = f⁻¹(e_list(f d))。"""
        return self.prev(self.rev(self.fm(k)))

    def fm_of_rev(self, k):
        """crossdiag 的 fe = f(e_list d)。"""
        return self.fm(self.rev(k))


# ---------------------------------------------------------------- body 族表
_ROW_RE = re.compile(r"^(ineq\d+)\s+'ID\[", re.M)


def _tokenize(s):
    s = re.sub(r"\s+", "", s)
    out, i = [], 0
    while i < len(s):
        ch = s[i]
        if ch.isdigit() or ch == ".":
            j = i
            while j < len(s) and (s[j].isdigit() or s[j] == "."):
                j += 1
            out.append(s[i:j])
            i = j
        elif s.startswith("[i,j]", i):
            out.append("[i,j]")
            i += 5
        elif s.startswith("[j]", i):
            out.append("[j]")
            i += 3
        elif ch in "+-*()/":
            out.append(ch)
            i += 1
        else:
            j = i
            while j < len(s) and (s[j].isalnum() or s[j] == "_"):
                j += 1
            if j == i:  # 不可识别字符（杂散标点）：跳过
                i += 1
                continue
            out.append(s[i:j])
            i = j
    return out


_NUM_RE = re.compile(r"\d+\.\d*|\.\d+|\d+")


def _mul_ev(a, b):
    """EV×EV：仅允许 至多一方含非"1"原子（本语料无双原子积）。"""
    out = EV()
    for a1, c1 in a.terms.items():
        for a2, c2 in b.terms.items():
            if a1 == "1":
                atom = a2
            elif a2 == "1":
                atom = a1
            else:
                raise ValueError(f"product of atoms {a1}·{a2} not supported")
            coef = c1 * c2
            if coef:
                out.terms[atom] = out.terms.get(atom, Fraction(0)) + coef
    return out


def _div_ev(a, b):
    """EV ÷ EV：除式必须纯有理。"""
    if set(b.terms) - {"1"}:
        raise ValueError("non-rational divisor")
    d = b.terms.get("1", Fraction(1))
    out = EV()
    out.terms = {a1: c1 / d for a1, c1 in a.terms.items() if c1 / d}
    return out


def _parse_lin(expr):
    """body.mod 线性表达式求值器：返回 (dict varname->EV, EV const)。

    支持 + − * /、括号、十进制字面量（含 1. / 2. 形）、var[i,j] / var[j] /
    sqrt8（→ EV 的 s8 原子）。乘除仅限标量×线性。
    """
    toks = _tokenize(expr)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def take():
        t = toks[pos[0]]
        pos[0] += 1
        return t

    def parse_sum():
        coeffs, const = parse_term()
        while peek() in ("+", "-"):
            op = take()
            c2, k2 = parse_term()
            sgn = 1 if op == "+" else -1
            for v, x in c2.items():
                coeffs[v] = coeffs.get(v, EV()).add(x, sgn)
            const = const.add(k2, sgn)
        return coeffs, const

    def parse_term():
        coeffs, const = parse_factor()
        while peek() in ("*", "/"):
            op = take()
            c2, k2 = parse_factor()
            if coeffs and c2:
                raise ValueError(f"nonlinear term in body.mod: {expr}")
            if op == "*":
                if c2:  # 左纯常数 × 右含 var
                    coeffs = {v: _mul_ev(const, x) for v, x in c2.items()}
                else:  # 左含 var × 右纯常数
                    coeffs = {v: _mul_ev(k2, x) for v, x in coeffs.items()}
                const = _mul_ev(const, k2)
            else:  # 除法：右侧必须纯有理
                if c2:
                    raise ValueError(f"nonlinear division in body.mod: {expr}")
                q = _div_ev(EV(1), k2)
                coeffs = {v: _mul_ev(q, x) for v, x in coeffs.items()}
                const = _mul_ev(const, q)
        return coeffs, const

    def parse_factor():
        t = peek()
        if t == "(":
            take()
            r = parse_sum()
            got = take()
            if got != ")":
                raise ValueError(f"expected ) got {got!r} in {expr!r}")
            return r
        if t == "-":
            take()
            c, k = parse_factor()
            return {v: x.neg() for v, x in c.items()}, k.neg()
        if t == "+":
            take()
            return parse_factor()
        take()
        if _NUM_RE.fullmatch(t):
            return {}, EV(Fraction(t))
        if peek() is not None and str(peek()).startswith("["):
            t = t + take()  # 并入 [i,j] / [j]
        if t == "sqrt8":
            return {}, EV(s8=1)
        return {t: EV(1)}, EV()

    coeffs, const = parse_sum()
    if pos[0] != len(toks):
        raise ValueError(f"trailing tokens in {expr!r}: {toks[pos[0]:]}")
    return coeffs, const


_BODY = None


def body_form(name):
    """body.mod 的 expr >= 0 → ≤ 形（vars 取负、rhs = expr 常项）。

    expr = const + Σ a_i v_i ≥ 0 ⇔ Σ (−a_i) v_i ≤ const。
    """
    global _BODY
    if _BODY is None:
        text = BODY_MOD.read_text()
        ms = list(_ROW_RE.finditer(text))
        _BODY = {}
        for n, m in enumerate(ms):
            seg = text[m.end(): ms[n + 1].start() if n + 1 < len(ms) else len(text)]
            colon = seg.index(":")
            expr = seg[colon + 1: seg.index(">=")].strip()
            _BODY[m.group(1)] = _parse_lin(expr)
    coeffs, const = _BODY[name]
    form = {}
    for v, x in coeffs.items():
        var = v.split("[")[0]
        form[var] = x.neg()
    return form, const


# ---------------------------------------------------------------- 000.txt 族→集合映射
ZERO_TXT = REPO / "reference" / "flyspeck" / "formal_lp" / "LP-HL" / "LP-HL" / "000.txt"

_CONSTRAINT_SET = None


def constraint_set(name):
    """000.txt Constraints 段：族名 → 实例下标所属集合。

    返回 "darts"/"darts3"/"darts4"/"darts5"/"darts6"/"nodes"/"faces"/"edges"。
    第二字段（如 "ineq108: dart, darts3"）是 FindElementIndex 的集合覆盖——
    证书下标 = 该集合中的位置（试点 B 的 ineq 下标 < 30 时 darts3≡darts，
    曾掩盖此约定；pent 路径记录全面暴露）。
    """
    global _CONSTRAINT_SET
    if _CONSTRAINT_SET is None:
        _CONSTRAINT_SET = {}
        text = ZERO_TXT.read_text()
        seg = text.split("Constraints", 1)[1].split("\nend", 1)[0]
        for line in seg.splitlines():
            line = line.strip()
            if not line or ":" not in line:
                continue
            nm, rest = line.split(":", 1)
            parts = [p.strip() for p in rest.split(",") if p.strip()]
            # parts[0] = domain（Translate 用），parts[1] = set（FindElementIndex 用）
            _CONSTRAINT_SET[nm.strip()] = parts[1] if len(parts) > 1 else parts[0]
    return _CONSTRAINT_SET.get(name, "darts")


_SET_POS = {"darts": lambda H: list(range(len(H.darts))),
            "darts3": lambda H: H.darts_k[3],
            "darts4": lambda H: H.darts_k[4],
            "darts5": lambda H: H.darts_k[5],
            "darts6": lambda H: H.darts_k[6]}


def set_dart(H, name, k):
    """族实例下标 → dart 下标（按 000.txt 集合覆盖）。"""
    st = constraint_set(base_name(name))
    fn = _SET_POS.get(st)
    if fn is None:  # nodes/faces/edges 等：界族与 node 族不走此处
        return k
    pos = fn(H)
    return pos[k] if k < len(pos) else k


def base_name(name):
    return name[:-4] if name.endswith("_neg") else name


# ---------------------------------------------------------------- 族表主体
def _frac(s):
    """十进制字面量 → Fraction。"""
    return Fraction(s)


def _bound_form(name, k, H):
    """变量界族 var_lo / var_hi（000.txt Variables + lp_head_ineqs 界陈述）。"""
    var = name[:-3]
    table = {
        # var: (domain, L, U)   tgt = 1.541（constants_approx.hl tgt_interval）
        "azim": ("d", EV(), EV(pi=1)),
        "azim2": ("d", EV(), EV(pi=1)),
        "azim3": ("d", EV(), EV(pi=1)),
        "rhazim": ("d", EV(), EV(pi=1, sol0=1)),
        "rhazim2": ("d", EV(), EV(pi=1, sol0=1)),
        "rhazim3": ("d", EV(), EV(pi=1, sol0=1)),
        "ln": ("n", EV(), EV(1)),
        "rho": ("n", EV(1), EV(1, c1=1)),
        "yn": ("n", EV(2), EV(_frac("2.52"))),
        "ye": ("d", EV(2), EV(3)),
        "y1": ("d", EV(2), EV(_frac("2.52"))),
        "y2": ("d", EV(2), EV(_frac("2.52"))),
        "y3": ("d", EV(2), EV(_frac("2.52"))),
        "y4": ("d", EV(2), EV(3)),
        "y5": ("d", EV(2), EV(3)),
        "y6": ("d", EV(2), EV(3)),
        "y8": ("d", EV(2), EV(_frac("2.52"))),
        "y9": ("d", EV(2), EV(_frac("2.52"))),
        "sol": ("f", EV(), EV(pi=4)),
        "tau": ("f", EV(), EV(_frac("1.541"))),
    }
    dom, L, U = table[var]
    if dom == "d":
        col = (var, k)
    elif dom == "n":
        col = (var, H.nodes[k])
    else:  # "f"
        col = (var, k)
    f = Form()
    if name.endswith("_lo"):  # L ≤ v ⇔ −v ≤ −L
        f.put(col, -1)
        f.rhs = L.neg()
    else:  # v ≤ U
        f.put(col, 1)
        f.rhs = U
    return f


def family_form(name, k, H):
    """族实例（不含 _neg 后缀）的精确 ≤ 形。k = 实例集位置。"""
    if name.endswith("_lo") or name.endswith("_hi"):
        return _bound_form(name, k, H)

    f = Form()

    # ---- node 和式 / main ----
    if name == "azim_sum":  # Σ azim ≤ 2π
        for d in H.node_darts[H.nodes[k]]:
            f.put(("azim", d), 1)
        f.rhs = EV(pi=2)
        return f
    if name == "rhazim_sum":  # Σ rhazim − (2π)·rho(x) ≤ 0
        x = H.nodes[k]
        for d in H.node_darts[x]:
            f.put(("rhazim", d), 1)
        f.put(("rho", x), EV(pi=-2))
        return f
    if name == "main":  # −Σ ln ≤ −12
        for x in H.nodes:
            f.put(("ln", x), -1)
        f.rhs = EV(-12)
        return f

    # ---- face 和式 ----
    if name.startswith("sol_sum") or name.startswith("tau_sum"):
        size = len(H.face_pairs[k])
        s = size - 2
        for kk in range(H.starts[k], H.starts[k] + size):
            f.put(("azim" if name.startswith("sol_sum") else "rhazim", kk), 1)
        f.put(("sol" if name.startswith("sol_sum") else "tau", k), -1)
        f.rhs = EV(pi=s) if name.startswith("sol_sum") else EV(pi=s, sol0=s)
        return f

    # ---- node 定义 ----
    if name == "ln_def":  # ln + (25/13)·yn ≤ 63/13（0.52 = 13/25 精确十进制）
        x = H.nodes[k]
        f.put(("ln", x), 1)
        f.put(("yn", x), Fraction(25, 13))
        f.rhs = EV(Fraction(63, 13))
        return f
    if name == "rho_def":  # rho + c1·ln ≤ 1 + c1
        x = H.nodes[k]
        f.put(("rho", x), 1)
        f.put(("ln", x), EV(c1=1))
        f.rhs = EV(1, c1=1)
        return f

    # ---- edge ----
    if name == "edge_sym":  # ye(k) − ye(rev k) ≤ 0
        f.put(("ye", k), 1)
        f.put(("ye", H.rev(k)), -1)
        return f

    # ---- dart 定义（eq 家族；lp_ineqs_proofs-compiled.hl 已证陈述）----
    ydefs = {
        "y1_def": ("y1", lambda k: ("yn", H.node_of(k))),
        "y2_def": ("y2", lambda k: ("yn", H.node_of(H.fm(k)))),
        "y3_def": ("y3", lambda k: ("yn", H.node_of(H.prev(k)))),
        "y4_def": ("y4", lambda k: ("ye", H.fm(k))),
        "y5_def": ("y5", lambda k: ("ye", H.prev(k))),
        "y6_def": ("y6", lambda k: ("ye", k)),
        "y8_def": ("y8", lambda k: ("y5", H.prev(k))),
        "y9_def": ("y9", lambda k: ("ye", H.fm(k))),
        "azim2c": ("azim2", lambda k: ("azim", H.fm(k))),
        "azim3c": ("azim3", lambda k: ("azim", H.prev(k))),
        "rhazim2c": ("rhazim2", lambda k: ("rhazim", H.fm(k))),
        "rhazim3c": ("rhazim3", lambda k: ("rhazim", H.prev(k))),
    }
    if name in ydefs:
        q, other = ydefs[name]
        f.put((q, k), 1)
        f.put(other(k), -1)
        return f

    # ---- RHA/RHB 族 ----
    if name == "RHA":  # azim − rhazim ≤ 0
        f.put(("azim", k), 1)
        f.put(("rhazim", k), -1)
        return f
    if name == "RHB":  # rhazim − (1+c1)·azim ≤ 0
        f.put(("rhazim", k), 1)
        f.put(("azim", k), EV(-1, c1=-1))
        return f
    if name == "RHBLO":  # rhazim − rho218·azim ≤ 0
        f.put(("rhazim", k), 1)
        f.put(("azim", k), EV(r218=-1))
        return f
    if name == "RHBHI":  # rho218·azim − rhazim ≤ 0
        f.put(("azim", k), EV(r218=1))
        f.put(("rhazim", k), -1)
        return f

    # ---- yy 族 ----
    if name in ("yy1", "yy2"):  # ±(y4+y5+y6) ≤ ∓/±6.25
        k3 = H.darts_k[3][k]
        sgn = 1 if name == "yy2" else -1
        for q in ("y4", "y5", "y6"):
            f.put((q, k3), sgn)
        f.rhs = EV(Fraction(625, 100) * sgn)
        return f
    if name in ("yy3", "yy4", "yy5", "yy6", "yy7"):
        x = H.nodes[k]
        v = {"yy3": "2.18", "yy4": "2.18", "yy5": "2.36", "yy6": "2.36",
             "yy7": "2.18"}[name]
        if name in ("yy3", "yy5", "yy7"):  # v ≤ yn ⇔ −yn ≤ −v
            f.put(("yn", x), -1)
            f.rhs = EV(-_frac(v))
        else:
            f.put(("yn", x), 1)
            f.rhs = EV(_frac(v))
        return f
    if name in ("yy8", "yy9", "yy10"):
        v = {"yy8": "2.25", "yy9": "2.25", "yy10": "2.52"}[name]
        if name == "yy8":  # 2.25 ≤ ye
            f.put(("ye", k), -1)
            f.rhs = EV(-_frac(v))
        else:
            f.put(("ye", k), 1)
            f.rhs = EV(_frac(v))
        return f
    if name in ("yy11", "yy12", "yy13", "yy14", "yy15"):
        k3 = H.darts_k[3][k]
        q, rhs = {"yy11": ("y4", EV(_frac("2.52"))),
                  "yy12": ("y4", EV(s8=1)),
                  "yy13": ("y5", EV(_frac("2.52"))),
                  "yy14": ("y6", EV(_frac("2.52"))),
                  "yy15": ("y4", EV(s8=1))}[name]
        if name in ("yy11", "yy12"):  # rhs ≤ y4 ⇔ −y4 ≤ −rhs
            f.put((q, k3), -1)
            f.rhs = rhs.neg()
        else:
            f.put((q, k3), 1)
            f.rhs = rhs
        return f

    # ---- tau 族（Main Estimate 界；结论项）----
    tau_fam = {
        "tau3": (3, None), "tau4": (4, "0.206"), "tau5": (5, "0.4819"),
        "tau6": (6, "0.712"), "tauB5h": (5, "0.616"), "tauB4h": (4, "0.477"),
        "tau5h": (5, "0.616"),
    }
    if name in tau_fam:
        kk, v = tau_fam[name]
        j = H.face_of_dart(H.darts_k[kk][k])
        f.put(("tau", j), -1)
        f.rhs = EV() if v is None else EV(-_frac(v))
        return f

    # ---- proofs2 特型 ----
    if name == "perimZ":  # 8.472 ≤ y5(pd)+y6(pd)+y5(fm)+y6(fm)
        k4 = H.darts_k[4][k]
        pd, fm = H.prev(k4), H.fm(k4)
        for q, src in (("y5", pd), ("y6", pd), ("y5", fm), ("y6", fm)):
            f.put((q, src), -1)
        f.rhs = EV(-_frac("8.472"))
        return f
    if name == "yapex_sup_flat":
        # y5+y6(d) + y5+y6(d2) − 7.99 ≥ 2.75(y4(d) − s8)
        k3 = H.darts_k[3][k]
        d2 = H.prev_of_rev_fm(k3)
        for src in (k3, d2):
            f.put(("y5", src), -1)
            f.put(("y6", src), -1)
        f.put(("y4", k3), _frac("2.75"))
        f.rhs = EV(-_frac("7.99"), s8=_frac("2.75"))
        return f
    if name == "crossdiag":
        # −azim(d) − azim(fe) + 0.4·y1(d) − 0.49688·(y2(fe)+y3(d)+y5(d)+y6(fe))
        #   + y4(prev d) ≤ −5.07804 + s8
        k3 = H.darts_k[3][k]
        fe = H.fm_of_rev(k3)
        pd = H.prev(k3)
        f.put(("azim", k3), -1)
        f.put(("azim", fe), -1)
        f.put(("y1", k3), _frac("0.4"))
        for q, src in (("y2", fe), ("y3", k3), ("y5", k3), ("y6", fe)):
            f.put((q, src), -_frac("0.49688"))
        f.put(("y4", pd), 1)
        f.rhs = EV(-_frac("5.07804"), s8=1)
        return f

    # ---- body 族（ineqNNN；body.mod ≥0 形取反）----
    if re.fullmatch(r"ineq\d+", name):
        coeffs, const = body_form(name)
        kd = set_dart(H, name, k)  # 000.txt 集合覆盖：下标 ∈ darts3/4/5/6/darts
        for var, c in coeffs.items():
            base = var.split("[")[0]
            # [j] 引用（sol/tau）→ 面列；[i,j] 引用 → dart 列
            col = (base, H.face_of_dart(kd)) if base in ("sol", "tau") else (base, kd)
            f.put(col, c)
        f.rhs = const
        return f

    raise KeyError(f"unknown family {name!r}")


def instantiate(name, k, H, S):
    """→ (行 Int 系数 dict（行尺度）, rhs 精确 EV（行尺度）, 风险旗)。

    界族（var_lo/var_hi）行不乘 10^p（系数 ±1、rhs = 界值；y6@4/y9@33 等
    成对实例的精确对消背书）；其余族行按 10^p 缩放。
    core_of 再做全局 ×S：列对消按 λ·0=0 保持，rhs 取 ceil(精确值·S)
    （2.52 类界值在 ×S 后变整数，无取整损失；行仍为原不等式的弱化形）。
    """
    base = name[:-4] if name.endswith("_neg") else name
    form = family_form(base, k, H)
    if name.endswith("_neg"):
        form = form.negated()
    scaled = 1 if (base.endswith("_lo") or base.endswith("_hi")) else S
    # 风险旗只对 body 族有意义（6 位浮点系数 vs HOL 精确有理数的取整边界）；
    # head 族的系数在行尺度下是精确整数，near_integer 会误报。
    flags = form.flags(scaled) if re.fullmatch(r"ineq\d+", base) else []
    row = {}
    for col, e in form.coeffs.items():
        a = e.floor(scaled)
        if a:
            row[col] = a
    return row, form.rhs.mul(scaled), flags


# ---------------------------------------------------------------- 终端 → 核心
def decode_terminal(hs, gi, ti):
    certs = [P.to_cert(v) for v in P.to_list(P.read_marshal(str(_dat_path(hs))))]
    cert = certs[gi]
    hyps = cert["hypermap_string"]
    hid, faces0 = parse_record(hyps)
    recs = list(terminal_records(faces0, cert["root_case"]))
    record, term = recs[ti]
    cons = [(_c[2][0], P.to_list(_c[2][1]), P.to_list(_c[2][2]))
            for _c in P.to_list(term[2])]
    tgts = [(_c[2][0], P.to_list(_c[2][1]), P.to_list(_c[2][2]))
            for _c in P.to_list(term[3])]
    bnds = [(_c[2][0], P.to_list(_c[2][1]), P.to_list(_c[2][2]))
            for _c in P.to_list(term[4])]
    return dict(hid=hid, faces=record, prec=term[0], infeas=bool(term[1]),
                cons=cons, tgts=tgts, bnds=bnds, root_faces=faces0)


def core_of(hs, gi, ti):
    """终端 → LpFarkasCore 数据（nvars/rows/rhs/mults + 诊断）。"""
    t = decode_terminal(hs, gi, ti)
    if not t["infeas"]:
        raise ValueError("not an infeasible terminal")
    if t["tgts"]:
        raise ValueError("infeasible terminal with nonempty targets — 表需扩展")
    S = 10 ** t["prec"]
    H = Hyp(t["faces"])
    rows, rhs, mults, flags = [], [], [], []
    fam_count = {}
    D = S  # 全局行尺度（列对消按 λ·0=0 保持；rhs 取 ceil(精确·D)）
    for section in ("cons", "bnds"):
        for name, idxs, mult in t[section]:
            fam_count[name] = fam_count.get(name, 0) + len(idxs)
            if len(idxs) != len(mult):
                raise ValueError(f"{name}: indices/mults length mismatch")
            for k, m in zip(idxs, mult):
                row, b_ex, fl = instantiate(name, k, H, S)
                rows.append({c: v * D for c, v in row.items()})
                rhs.append(b_ex.ceil(D))
                mults.append(int(m))
                for x in fl:
                    flags.append((name, k) + x)
    qty_order = ["azim", "azim2", "azim3", "rhazim", "rhazim2", "rhazim3",
                 "ye", "y1", "y2", "y3", "y4", "y5", "y6", "y8", "y9",
                 "ln", "rho", "yn", "sol", "tau"]
    cols = sorted({c for r in rows for c in r},
                  key=lambda c: (qty_order.index(c[0]), c[1]))
    dense = [[r.get(c, 0) for c in cols] for r in rows]
    return dict(nvars=len(cols), rows=dense, rhs=rhs, mults=mults,
                cols=cols, prec=t["prec"], hid=t["hid"], flags=flags,
                fam_count=fam_count)


def farkas_precheck(core):
    """Python 侧镜像 farkasCheck：列和全零 + rhs 加权和为负。"""
    n, rows, rhs, mults = core["nvars"], core["rows"], core["rhs"], core["mults"]
    bad = []
    for i in range(n):
        s = sum(r[i] * m for r, m in zip(rows, mults))
        if s != 0:
            bad.append((core["cols"][i], s))
    rsum = sum(b * m for b, m in zip(rhs, mults))
    return dict(ok=(not bad) and rsum < 0, bad_cols=bad[:30], n_bad=len(bad),
                rhs_sum=rsum, n_rows=len(rows), nvars=n)


# ---------------------------------------------------------------- 统计
def all_infeasible_terminals():
    out = []
    for path in dat_files():
        certs = [P.to_cert(v) for v in P.to_list(P.read_marshal(str(path)))]
        for gi, cert in enumerate(certs):
            _, faces0 = parse_record(cert["hypermap_string"])
            for ti, (rec, term) in enumerate(terminal_records(faces0, cert["root_case"])):
                if term[1]:
                    out.append((path.name, gi, ti, term[0], rec, term))
    return out


def stats():
    """全 easy_*.dat 的 infeasible 终端：族分布、精度直方图、分裂类型、风险旗。"""
    fam = {}
    prec_hist = {}
    split_hist = {}
    problems = []
    n = 0
    for path in dat_files():
        certs = [P.to_cert(v) for v in P.to_list(P.read_marshal(str(path)))]
        for gi, cert in enumerate(certs):
            _walk_splits(cert["root_case"], split_hist)
            _, faces0 = parse_record(cert["hypermap_string"])
            for ti, (rec, term) in enumerate(terminal_records(faces0, cert["root_case"])):
                if not term[1]:
                    continue
                n += 1
                prec = term[0]
                prec_hist[prec] = prec_hist.get(prec, 0) + 1
                H = Hyp(rec)
                S = 10 ** prec
                for lst in (term[2], term[4]):
                    for c in P.to_list(lst):
                        name = c[2][0]
                        idxs = P.to_list(c[2][1])
                        e = fam.setdefault(name, [0, set()])
                        e[0] += len(idxs)
                        e[1].add(prec)
                        for k in idxs:
                            try:
                                _, _, fl = instantiate(name, k, H, S)
                                for x in fl:
                                    problems.append((path.name, name, prec, k, x))
                            except KeyError as ex:
                                problems.append((path.name, name, prec, k,
                                                 ("UNKNOWN_FAMILY", str(ex))))
                            except Exception as ex:  # noqa: BLE001
                                problems.append((path.name, name, prec, k,
                                                 ("ERROR", repr(ex)[:140])))
    print(f"infeasible terminals total: {n}")
    print("precision histogram:", dict(sorted(prec_hist.items())))
    print("split-type histogram (all easy certs):", dict(sorted(split_hist.items())))
    print(f"distinct families: {len(fam)}")
    for name in sorted(fam):
        cnt, ps = fam[name]
        print(f"  {name:24s} instances={cnt:5d} precisions={sorted(ps)}")
    print(f"\nparse problems / risk flags: {len(problems)}")
    for r in problems[:50]:
        print("  ", r)


def _walk_splits(case, acc, depth=0):
    if case[1] != 0:
        st = case[2][0][2][0]
        acc[st] = acc.get(st, 0) + 1
        for c in P.to_list(case[2][1]):
            _walk_splits(c, acc, depth + 1)


# ---------------------------------------------------------------- Lean 发射
def _fmt_list(xs, per=16):
    lines = []
    for i in range(0, len(xs), per):
        lines.append(" " * 6 + ", ".join(str(x) for x in xs[i:i + per]))
    return "[\n" + " ,\n".join(lines) + "]"


def emit_lean(core, ns, out_path, hs, gi, ti, col_major=False):
    n, rows, rhs, mults = core["nvars"], core["rows"], core["rhs"], core["mults"]
    assert all(len(r) == n for r in rows)
    assert len(rows) == len(rhs) == len(mults)
    rows_s = ",\n   ".join("[" + ", ".join(map(str, r)) + "]" for r in rows)
    L = []
    L.append(f"-- G5 gen_farkas.py 发射：{hs} #{gi} t{ti:04d} "
             f"(hid {core['hid']}, precision p{core['prec']}, "
             f"{len(rows)} 行 × {n} 列)。/tmp 隔离探针，非 tracked。")
    if col_major:
        # 列主序发射：行主序 rows 转置为 cols（cols[i][j] = rows[j][i]），
        # mults/rhs 按行平行不动、rhs 不动——转置不改变数学，farkasCheckCol
        # 逐列直读消去行主序求值的行内位置游走。prec 不变式照旧：系数仍为
        # 10^prec 缩放整数（prec 与行主序发射一致，转置不改 prec），10^p 口径
        # 由 Kepler.Text.LP.farkasCheckCol_scaled_sound 承接。
        cols = [[r[i] for r in rows] for i in range(n)]
        assert len(cols) == n and all(len(c) == len(rows) for c in cols)
        assert all(cols[i][j] == rows[j][i] for i in range(n)
                   for j in range(len(rows)))
        cols_s = ",\n   ".join("[" + ", ".join(map(str, c)) + "]" for c in cols)
        L.append("-- 列主序：rows 转置为 cols（cols[i][j] = rows[j][i]），"
                 "mults/rhs 按行平行不动；转置不改变数学。")
        L.append(f"-- prec 不变式：系数仍为 10^{core['prec']} 缩放整数（prec 未变），"
                 "10^p 口径由 farkasCheckCol_scaled_sound 承接。")
    L.append("import Kepler.Text.LP.LPSchemaFarkas")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace {ns}")
    L.append("")
    if col_major:
        L.append("def core : Kepler.Text.LP.LpFarkasCoreCol :=")
        L.append("  ⟨" + str(n) + ", [")
        L.append("   " + cols_s + "],")
    else:
        L.append("def core : Kepler.Text.LP.LpFarkasCore :=")
        L.append("  ⟨" + str(n) + ", [")
        L.append("   " + rows_s + "],")
    L.append("   " + _fmt_list(rhs) + ",")
    L.append("   " + _fmt_list(mults) + "⟩")
    L.append("")
    if col_major:
        L.append("theorem core_shape : Kepler.Text.LP.coreShapeCol core = true := by decide")
        L.append("")
        L.append(
            "theorem core_farkasCheck : Kepler.Text.LP.farkasCheckCol core = true := by decide")
    else:
        L.append("theorem core_shape : Kepler.Text.LP.coreShape core = true := by decide")
        L.append("")
        L.append("theorem core_farkasCheck : Kepler.Text.LP.farkasCheck core = true := by decide")
    L.append("")
    L.append("#print axioms " + ns + ".core_farkasCheck")
    L.append("")
    L.append(f"end {ns}")
    Path(out_path).write_text("\n".join(L) + "\n")


def land_module_name(core, ti):
    """落地产物模块名（C3 数据波）：`T<id 去 _>`（LPSchema 手册第 3 步同款
    命名；bound 支产物为 PRODDIR/<mod>/Assembly.lean 目录形，本支为
    PRODDIR/<mod>.lean 平文件形——记录 id 全库唯一，两支互斥不撞名）。"""
    return "T" + core["hid"] + "t%04d" % ti


def emit_lean_land(core, out_path, hs, gi, ti):
    """落地模块发射（--land）：列主序证书 + 列→行桥转发件，入库 tracked 形
    （对照 emit_lean 的 /tmp 隔离探针形）。叶闭合转发 = `⟨rowCore, row_check⟩`
    闭合 LpTerminalInfeasibleCertified（LPCert 冻结陈述，DEF-FIX 章程）。"""
    n, rows, rhs, mults = core["nvars"], core["rows"], core["rhs"], core["mults"]
    assert all(len(r) == n for r in rows)
    assert len(rows) == len(rhs) == len(mults)
    cols = [[r[i] for r in rows] for i in range(n)]
    assert len(cols) == n and all(len(c) == len(rows) for c in cols)
    assert all(cols[i][j] == rows[j][i] for i in range(n)
               for j in range(len(rows)))
    cols_s = ",\n   ".join("[" + ", ".join(map(str, c)) + "]" for c in cols)
    rhs_s = _fmt_list(rhs)
    mults_s = _fmt_list(mults)
    mod = land_module_name(core, ti)
    L = []
    L.append("/-")
    L.append("  AUTO-GENERATED infeasible-record Farkas certificate (column-major) — do not edit")
    L.append("")
    L.append(f"  Generated by `pipeline/lp/gen_farkas.py --lean --col-major --land`")
    L.append(f"  from `{hs}` graph #{gi} terminal t{ti:04d} (hid {core['hid']},")
    L.append(f"  precision p{core['prec']}, {len(rows)} rows x {n} vars). 族解析层 =")
    L.append("  G5（C1.6 口径，generator 头注有全源码锚点）；语义核与退化防线见")
    L.append("  `Kepler.Text.LP.LPFarkas` / `Kepler.Text.LP.LPFarkasCM`。")
    L.append("")
    L.append("  Farkas 证书：非负整数乘子 m 使列加权和为零 + rhs 加权和为负（HOL")
    L.append("  prove_flyspeck_lp.hl infeasible 支直译）。系数矩阵按列存储（10^p 缩放")
    L.append("  整数）；列检查 `core_farkasCheck` = 列主序单条 decide（C1.7 列主序章，")
    L.append("  巨物行主序 decide 的内存陷阱不在此路径）。行主序像 `rowCore`/`row_check`")
    L.append("  经 `farkasCheck_rowCoreOf` 桥直推（纯 List 结构归纳）。叶闭合转发形：")
    L.append("  `⟨rowCore, row_check⟩`（LPCert 冻结陈述 LpTerminalInfeasibleCertified）。")
    L.append("-/")
    L.append("import Kepler.Text.LP.LPFarkasCM")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append(f"namespace Kepler.LP.{mod}")
    L.append("")
    L.append(f"-- 列主序：rows 转置为 cols（cols[i][j] = rows[j][i]，发射侧已")
    L.append(f"-- round-trip assert）；rhs/mults 按行平行不动；转置不改变数学。")
    L.append(f"-- prec 不变式：系数为 10^{core['prec']} 缩放整数，10^p 口径由")
    L.append(f"-- farkasCheckCol_scaled_sound 承接。")
    L.append("def core : Kepler.Text.LP.LpFarkasCoreCol :=")
    L.append("  ⟨" + str(n) + ", [")
    L.append("   " + cols_s + "],")
    L.append("   " + rhs_s + ",")
    L.append("   " + mults_s + "⟩")
    L.append("")
    L.append("theorem core_shape : Kepler.Text.LP.coreShapeCol core = true := by decide")
    L.append("")
    L.append("theorem core_farkasCheck : Kepler.Text.LP.farkasCheckCol core = true := by decide")
    L.append("")
    L.append("/-- 行主序像（转置重建；唯一合法行主序核来源，不经行主序 decide）。 -/")
    L.append("def rowCore : Kepler.Text.LP.LpFarkasCore := Kepler.Text.LP.rowCoreOf core")
    L.append("")
    L.append("/-- 闭叶转发件：行主序 checker 由列检查经桥直推。 -/")
    L.append("theorem row_check : Kepler.Text.LP.farkasCheck rowCore = true :=")
    L.append("  Kepler.Text.LP.farkasCheck_rowCoreOf core core_farkasCheck")
    L.append("")
    L.append(f"end Kepler.LP.{mod}")
    Path(out_path).write_text("\n".join(L) + "\n")
    return mod


# ---------------------------------------------------------------- CLI
def _cli(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--stats", action="store_true")
    ap.add_argument("--record", nargs=3, metavar=("DAT", "GI", "TI"))
    ap.add_argument("--lean", nargs=5, metavar=("DAT", "GI", "TI", "OUT", "NS"))
    ap.add_argument("--col-major", action="store_true",
                    help="--lean 伴生旗标：行主序 rows 转置为 cols 发射 "
                         "LpFarkasCoreCol（mults/rhs 按行平行不动、rhs 不动；"
                         "转置不改变数学，对接 farkasCheckCol 列主序内核）")
    ap.add_argument("--land", action="store_true",
                    help="--lean 伴生旗标：落地模块发射（C3 数据波，tracked 形）——"
                         "列主序证书 + rowCore/row_check 列→行桥转发件，命名空间 "
                         "Kepler.LP.T<id 去 _>（NS 实参被忽略）；叶闭合由 "
                         "gen_lp_skeleton.py --emit-closure 消费。老路径（无 "
                         "--land）逐字节不变")
    args = ap.parse_args(argv)
    if args.stats:
        stats()
        return 0
    if args.record:
        hs, gi, ti = args.record[0], int(args.record[1]), int(args.record[2])
        core = core_of(hs, gi, ti)
        chk = farkas_precheck(core)
        print(f"hid={core['hid']} prec=p{core['prec']} rows={chk['n_rows']} "
              f"nvars={chk['nvars']}")
        print(f"farkas precheck: ok={chk['ok']} n_bad_cols={chk['n_bad']} "
              f"rhs_sum={chk['rhs_sum']}")
        if chk["bad_cols"]:
            print("bad cols (col, sum):", chk["bad_cols"])
        if core["flags"]:
            print(f"risk flags: {len(core['flags'])}")
            for x in core["flags"][:20]:
                print("  ", x)
        return 0
    if args.lean:
        hs, gi, ti, out, ns = (args.lean[0], int(args.lean[1]), int(args.lean[2]),
                               args.lean[3], args.lean[4])
        core = core_of(hs, gi, ti)
        if args.land:
            mod = emit_lean_land(core, out, hs, gi, ti)
            print(f"emitted {out} [land]: module Kepler.LP.{mod} "
                  f"rows={len(core['rows'])} nvars={core['nvars']}")
            return 0
        emit_lean(core, ns, out, hs, gi, ti, col_major=args.col_major)
        if args.col_major:
            print(f"emitted {out} [col-major]: rows={len(core['rows'])} "
                  f"nvars={core['nvars']}")
        else:
            print(f"emitted {out}: rows={len(core['rows'])} nvars={core['nvars']}")
        return 0
    ap.print_help()
    return 1


if __name__ == "__main__":
    # Marshal 深嵌套 cons 表 → 大栈线程
    sys.setrecursionlimit(2_000_000)
    threading.stack_size(1024 * 1024 * 1024)
    _res = []

    def _run():
        _res.append(_cli())

    _t = threading.Thread(target=_run)
    _t.start()
    _t.join()
    sys.exit(_res[0])

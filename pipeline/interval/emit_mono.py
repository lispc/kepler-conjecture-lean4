#!/usr/bin/env python3
"""549 M2: DerivSafeOn 证书发射器 —— mono 折叠叶的完整语义正性端到端.

对应 `lean/Kepler/Interval/Cases/C549Mono.lean` 的 `DerivSafeOnM`（模式索引安全
谓词）+ `safe*` discharge 引理。本工具在 emit_diff.py（face/der 两叶）之上追加：

  cert 叶: 对原表达式中 DerivSafeOn 路径上的每个节点发射符号定号证书
           ite  (then 模式) → guardNeg: checkPosTMHull (.neg guard) box ps
           ite  (else 模式) → guardNN:  checkPosTMHull guard box ps（>0 ⇒ ≥0）
           sqrt           → basePos:  checkPosTMHull base box ps
           div (非常数分母) → den ≠ 0，按 pos/neg/abs 形择优
           div (常数分母)   → 内联 safeConstNe（无 TM 叶）
           trans lnK       → base ≠ 0，按 pos/neg/abs 形择优
  DSafe 项: 逐节点拼装嵌套 `DerivSafeOnM` 证明项（模式单调：一旦 else 支，
            全程 else 支；abs 出现在值路径 → 拒发并报错）
  Sem 定理: 面叶 + 导数叶 + DSafe ⇒ `0 < e.evalReal ρ`（checkPosFace*_sound）

stage-A 收割走单驱动批量探针（每 (子表达式, 盒, 形) 一探针、一次编译）。

子命令:
  census <case.json> [--j=K]
      打印 then/else 模式下 DerivSafeOn 路径节点普查与所需证书叶清单。
  pilot2 <case.json> <leanfile> [--j=2] [--k=3] [--gran=-80] [--rung=128]
      [--rung-out=-80] [--out=<out.lean>] [--dir=lo] [--mode=then]
      端到端试点：前 k 个 PASS 单叶 × (面叶 + 导数叶 + 证书叶 + DSafe + Sem)。

  ---- facePos 全量评估（本工位；tight 证书直读，shard 化出题）----

  boxes <case.json> <cert.json> [--j=2] [--k=220] [--stride=0] [--skip=0]
        [--want-else=8] [--extra-cap=6000] [--out=<census.jsonl>]
        [--rung=128] [--rung-out=-80]
      资格普查（Python 侧精确有理区间算术，零近似）：逐叶判定 guard 定号
      （then 路径全 NEG / else 路径全 NN），输出 census jsonl（盒 dyadic
      字面量 + 逐 guard 定号 + 模式）。guard 形 |P|−√S 用平方比较精确判定。
      want-else>0 时在主样本后继续扫描补足 else 合格叶（extra-cap 封顶）。
  probe <case.json> <census.jsonl> --stage=der|cert|full|face
        [--der=<der.jsonl>] [--from=A] [--to=B] [--gran=-80] [--rung=128]
        [--rung-out=-80] [--out=<verdict.jsonl>] [--tag=S]
      stage-A 批量探针（单驱动多探针，逐探针毫秒计时）：
        der   逐叶 ±∂ⱼf（模式镜像表达式）两方向；
        cert  逐叶逐证书逐形（pos/neg/abs 择优）；
        full  逐叶原盒全叶（基线口径 + 原路 PASS 率）；
        face  逐叶面盒（方向取自 der 判定；需 --der）。
  emit <case.json> <census.jsonl> --der=<der.jsonl> --face=<face.jsonl>
       --cert=<cert.jsonl> [--full=<full.jsonl>] [--out-dir=<dir>]
       [--shard=20] [--name=Shard] [--baseline] [--native-ctl] [--ladder]
      合格叶全链 shard 出题（≤shard 叶/模块）：面叶+导数叶+证书叶+DSafe+Sem。
      --baseline：同批叶原盒全叶 decide 基线模块（需 --full）。
      --native-ctl：同内容的 native_decide 实验对照模块（不进主结论）。
      --ladder：单叶三层阶梯模块（CERT→+DER→+FOLD），decide 口径耗时分解。

用法：在 pipeline/interval/ 下 `python3 emit_mono.py ...`；
stage-A 运行在 lean/ 包根下 `lake env lean --run`。
"""
import json
import os
import re
import subprocess
import sys
from fractions import Fraction

from emit_lean import RPN, die, hull_expr
from emit_diff import (bal, dtext as dtext_then, face_box_lit, parse_leaf_defs,
                       parse_sexpr, params_lit)


# `derivIExprM` 的 Python 镜像（else 支）；dtext_then 已镜像 then 支。
def dtextM(node, src, j, mode):
    if mode == "then":
        return dtext_then(node, src, j)
    op = node.op
    k = node.kids
    if op == ".ite":
        return dtextM(k[2], src, j, mode)
    if op in (".neg", ".abs"):
        return dtextM(k[0], src, j, mode) if op == ".neg" else "(.const ⟨0, 0⟩)"
    if op == ".const":
        return "(.const ⟨0, 0⟩)"
    if op == ".var":
        return "(.const ⟨1, 0⟩)" if int(k[0]) == j else "(.const ⟨0, 0⟩)"
    if op == ".add":
        return f"(.add {dtextM(k[0], src, j, mode)} {dtextM(k[1], src, j, mode)})"
    if op == ".sub":
        return f"(.sub {dtextM(k[0], src, j, mode)} {dtextM(k[1], src, j, mode)})"
    if op == ".mul":
        return (f"(.add (.mul {dtextM(k[0], src, j, mode)} {k[1].text(src)}) "
                f"(.mul {k[0].text(src)} {dtextM(k[1], src, j, mode)}))")
    if op == ".div":
        out = k[2]
        return (f"(.div (.sub (.mul {dtextM(k[0], src, j, mode)} {k[1].text(src)}) "
                f"(.mul {k[0].text(src)} {dtextM(k[1], src, j, mode)})) "
                f"(.mul {k[1].text(src)} {k[1].text(src)}) {out})")
    if op == ".sqrt":
        a = k[0].text(src)
        return (f"(.div {dtextM(k[0], src, j, mode)} "
                f"(.add (.sqrt {a} {k[1]} {k[2]}) (.sqrt {a} {k[1]} {k[2]})) 0)")
    if op == ".trans":
        kind = k[0]
        a = k[1].text(src)
        N, out = k[2], k[3]
        da = dtextM(k[1], src, j, mode)
        if kind == ".sinK":
            return f"(.mul (.trans .cosK {a} {N} {out}) {da})"
        if kind == ".cosK":
            return f"(.neg (.mul (.trans .sinK {a} {N} {out}) {da}))"
        if kind == ".arctanK":
            return f"(.div {da} (.add (.const ⟨1, 0⟩) (.mul {a} {a})) 0)"
        if kind == ".lnK":
            return f"(.div {da} {a} 0)"
        die(f"bad kind {kind}")
    die(f"bad op {op}")


def node_counts(text):
    return (text.count("(.sqrt "), text.count("(.div "), text.count("(.trans "))


def const_dyad(kd):
    """const 节点的 dyadic 字面量文本（tokenizer 把 `⟨m, e⟩` 劈成两 token）。"""
    return " ".join(kd)


def walk_dsafe_path(node, src, mode, certs):
    """DerivSafeOn 路径普查/证书收集（模式单调：ite 只走选中支）。

    certs: list of dict(kind=, sub=, forms=[...])；dedup by (kind, sub)。
    form: (label, text, pointwise_target_tag)；div/ln 的 ≠0 目标按
    pos/neg/abs 形择优（stage-A PASS 为准）。
    """
    op = node.op
    kd = node.kids

    def add(kind, sub, forms):
        for c in certs:
            if c["kind"] == kind and c["sub"] == sub:
                for f in forms:
                    if f[0] not in [g[0] for g in c["forms"]]:
                        c["forms"].append(f)
                return
        certs.append(dict(kind=kind, sub=sub, forms=forms))

    if op == ".const" or op == ".var":
        return
    if op == ".abs":
        die("abs node on DerivSafeOn path: no DerivSafeOnM constructor "
            "(abs 不可导；仅 guard 内 abs 可经 TM 叶消化)")
    if op == ".neg":
        walk_dsafe_path(kd[0], src, mode, certs)
    elif op in (".add", ".sub", ".mul"):
        walk_dsafe_path(kd[0], src, mode, certs)
        walk_dsafe_path(kd[1], src, mode, certs)
    elif op == ".div":
        den = kd[1]
        if den.op == ".const":
            mm = re.match(r"⟨(-?\d+), (-?\d+)⟩", const_dyad(den.kids))
            if not mm or int(mm.group(1)) == 0:
                die(f"const denominator with zero mantissa: {const_dyad(den.kids)}")
        else:
            t = den.text(src)
            add("divNe", t, [("pos", t), ("neg", f"(.neg {t})"),
                             ("abs", f"(.abs {t})")])
        walk_dsafe_path(kd[0], src, mode, certs)
        walk_dsafe_path(kd[1], src, mode, certs)
    elif op == ".sqrt":
        t = kd[0].text(src)
        add("sqrtPos", t, [("pos", t)])
        walk_dsafe_path(kd[0], src, mode, certs)
    elif op == ".trans":
        kind = kd[0]
        if kind == ".lnK":
            t = kd[1].text(src)
            add("lnNe", t, [("pos", t), ("neg", f"(.neg {t})"),
                            ("abs", f"(.abs {t})")])
        walk_dsafe_path(kd[1], src, mode, certs)
    elif op == ".ite":
        guard = kd[0].text(src)
        if mode == "then":
            add("iteNeg", guard, [("neg", f"(.neg {guard})")])
            walk_dsafe_path(kd[1], src, mode, certs)
        else:
            add("iteNN", guard, [("pos", guard)])
            walk_dsafe_path(kd[2], src, mode, certs)
    else:
        die(f"bad op {op}")


def dsafe_term(node, src, mode, cert_names):
    """逐节点拼装嵌套 DerivSafeOnM 证明项（构造子的表达式索引全部可由
    expected type 统一；const/var 显式场由树 token 提供）。

    cert_names: (kind, sub) → pointwise 前提定理名（div/ln 常数分母为 None，
    内联 safeConstNe）。
    """
    op = node.op
    kd = node.kids
    if op == ".const":
        return f"(DerivSafeOnM.const {const_dyad(kd)})"
    if op == ".var":
        return f"(DerivSafeOnM.var {kd[0]})"
    if op == ".neg":
        return f"(DerivSafeOnM.neg {dsafe_term(kd[0], src, mode, cert_names)})"
    if op == ".abs":
        die("abs on DerivSafeOn path")
    if op == ".add":
        return (f"(DerivSafeOnM.add {dsafe_term(kd[0], src, mode, cert_names)} "
                f"{dsafe_term(kd[1], src, mode, cert_names)})")
    if op == ".sub":
        return (f"(DerivSafeOnM.sub {dsafe_term(kd[0], src, mode, cert_names)} "
                f"{dsafe_term(kd[1], src, mode, cert_names)})")
    if op == ".mul":
        return (f"(DerivSafeOnM.mul {dsafe_term(kd[0], src, mode, cert_names)} "
                f"{dsafe_term(kd[1], src, mode, cert_names)})")
    if op == ".div":
        den = kd[1]
        if den.op == ".const":
            mm = re.match(r"⟨(-?\d+), (-?\d+)⟩", const_dyad(den.kids))
            m, e = int(mm.group(1)), int(mm.group(2))
            hz = f"(fun ρ _ => safeConstNe {m} {e} (by norm_num) ρ)"
        else:
            hz = cert_names[("divNe", den.text(src))]
        return (f"(DerivSafeOnM.div {dsafe_term(kd[0], src, mode, cert_names)} "
                f"{dsafe_term(den, src, mode, cert_names)} {hz})")
    if op == ".sqrt":
        return (f"(DerivSafeOnM.sqrt {dsafe_term(kd[0], src, mode, cert_names)} "
                f"{cert_names[('sqrtPos', kd[0].text(src))]})")
    if op == ".trans":
        kind = kd[0][1:]
        if kind == "lnK":
            return (f"(DerivSafeOnM.transLn "
                    f"{dsafe_term(kd[1], src, mode, cert_names)} "
                    f"{cert_names[('lnNe', kd[1].text(src))]})")
        hk = {"sinK": "(Or.inl rfl)", "cosK": "(Or.inr (Or.inl rfl))",
              "arctanK": "(Or.inr (Or.inr rfl))"}[kind]
        return (f"(DerivSafeOnM.trans {dsafe_term(kd[1], src, mode, cert_names)} {hk})")
    if op == ".ite":
        if mode == "then":
            return (f"(DerivSafeOnM.iteNeg "
                    f"{dsafe_term(kd[1], src, mode, cert_names)} "
                    f"{cert_names[('iteNeg', kd[0].text(src))]})")
        return (f"(DerivSafeOnM.iteNN "
                f"{dsafe_term(kd[2], src, mode, cert_names)} "
                f"{cert_names[('iteNN', kd[0].text(src))]})")
    die(f"bad op {op}")


STAGEA2_TMPL = """/-  emit_mono.py batched stage-A probe driver (scratch). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Kepler.Interval

namespace Probe{mod}

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

instance : Inhabited (IExpr {n}) := ⟨.const ⟨0, 0⟩⟩

def Exprs : Array (IExpr {n}) := #[
    {exprs}
]

def Ps (nsqrt ndiv ntrans : ℕ) : TMParams :=
  ⟨List.replicate nsqrt ⟨0, 0, 0, ({gran}), ({gran})⟩,
   List.replicate ndiv ⟨({gran}), ({gran}), ({gran})⟩,
   List.replicate ntrans ⟨({gran}), ({gran})⟩⟩

/-- probes: (exprIdx, box, nsqrt, ndiv, ntrans) -/
def Probes : Array (ℕ × (Fin {n} → DInterval) × ℕ × ℕ × ℕ) := #[
    {probes}
]

end Probe{mod}

open Probe{mod} in
def main : List String → IO UInt32 := fun _ => do
  IO.println "RUNG mono2"
  for i in [0:Probes.size] do
    let (ei, bx, ns, ni, nt) := Probes[i]!
    match tmHullLeafProbe Exprs[ei]! bx (Ps ns ni nt) with
    | some (p, m, e, l) =>
        let v : String := if p then "PASS" else "NEG"
        let trip := String.intercalate " " (l.map fun t => s!"{{t.1}} {{t.2.1}} {{t.2.2}}")
        IO.println s!"{{i}} {{v}} {{m}} {{e}} {{trip}}"
    | none => IO.println s!"{{i}} FAIL"
  return 0
"""


def run_stagea2(mod, n, exprs, probes, gran, tmpdir="/tmp/opencode"):
    """批量 stage-A：单驱动多探针。probes: (expr_idx, box_text, ns, ni, nt)。

    返回 rows: list of (verdict, lo_m, lo_e, triples)（按 probe 序）。"""
    path = f"{tmpdir}/{mod}_stagea.lean"
    text = STAGEA2_TMPL.format(
        mod=mod, n=n,
        exprs=",\n    ".join(f"({e} : IExpr {n})" for e in exprs),
        gran=gran,
        probes=",\n    ".join(f"({ei}, ({bt} : Fin {n} → DInterval), {ns}, {ni}, {nt})"
                              for ei, bt, ns, ni, nt in probes))
    with open(path, "w") as f:
        f.write(text)
    lean_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean")
    proc = subprocess.run(["lake", "env", "lean", "--run", path], cwd=lean_root,
                          capture_output=True, text=True, timeout=7200)
    out = proc.stdout
    if "RUNG mono2" not in out:
        die(f"stage-A {mod} failed: {proc.stderr[-2000:]}")
    rows = []
    for ln in out.splitlines():
        tk = ln.split()
        if len(tk) >= 2 and tk[0].isdigit():
            if tk[1] == "FAIL":
                rows.append(("FAIL", 0, 0, []))
            else:
                trip = [int(x) for x in tk[4:]]
                rows.append((tk[1], int(tk[2]), int(tk[3]),
                             [tuple(trip[q:q + 3]) for q in range(0, len(trip), 3)]))
    if len(rows) != len(probes):
        die(f"stage-A rows {len(rows)} != probes {len(probes)}")
    return rows


# ===================== facePos 全量评估（本工位） =====================

# ---- guard 定号普查（Python 侧精确有理区间算术；零浮点零近似） ----

def parse_dyad_text(toktext):
    """const 节点文本 `⟨m, e⟩` → Fraction 值 m·2^e。"""
    mm = re.match(r"⟨(-?\d+), (-?\d+)⟩", toktext)
    if not mm:
        die(f"bad dyad text: {toktext!r}")
    return Fraction(int(mm.group(1))) * (Fraction(2) ** int(mm.group(2)))


def iv_eval(node, boxfr):
    """IExpr 子树在盒上的精确区间包围（Fraction 对；仅支持多项式算子 +
    abs——guard 路径上的 sqrt 由 guard_sign 的平方比较精确处理）。"""
    op = node.op
    kd = node.kids
    if op == ".const":
        v = parse_dyad_text(const_dyad(kd))
        return (v, v)
    if op == ".var":
        return boxfr[int(kd[0])]
    if op == ".neg":
        l, h = iv_eval(kd[0], boxfr)
        return (-h, -l)
    if op == ".abs":
        l, h = iv_eval(kd[0], boxfr)
        if l >= 0:
            return (l, h)
        if h <= 0:
            return (-h, -l)
        return (Fraction(0), max(-l, h))
    if op == ".add":
        a, b = iv_eval(kd[0], boxfr), iv_eval(kd[1], boxfr)
        return (a[0] + b[0], a[1] + b[1])
    if op == ".sub":
        a, b = iv_eval(kd[0], boxfr), iv_eval(kd[1], boxfr)
        return (a[0] - b[1], a[1] - b[0])
    if op == ".mul":
        a, b = iv_eval(kd[0], boxfr), iv_eval(kd[1], boxfr)
        cands = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
        return (min(cands), max(cands))
    die(f"iv_eval: unsupported op {op} on guard path")


def guard_sign(g, boxfr):
    """guard 子表达式在盒上的定号判定："NEG"（全 <0）/ "NN"（全 ≥0）/
    "STRADDLE" / "SQRTNEG"（√ 底全负——值语义未定义）。

    `|P| − √S` 形用平方比较精确判定（两侧均 ≥0 时 |P|<√S ⟺ P²<S）：
    NEG ⟺ sup(P²) < inf(S)；NN ⟺ inf(P²) ≥ sup(S)。其余形走精确区间。"""
    if g.op == ".sub" and g.kids[1].op == ".sqrt" and g.kids[0].op == ".abs":
        A = iv_eval(g.kids[0], boxfr)
        S = iv_eval(g.kids[1].kids[0], boxfr)
        if S[1] < 0:
            return "SQRTNEG"
        if S[0] < 0:
            return "STRADDLE"
        a, b = A
        a2lo = a * a if a >= 0 else (b * b if b <= 0 else Fraction(0))
        a2hi = max(a * a, b * b)
        if a2hi < S[0]:
            return "NEG"
        if a2lo >= S[1]:
            return "NN"
        return "STRADDLE"
    lo, hi = iv_eval(g, boxfr)
    if hi < 0:
        return "NEG"
    if lo >= 0:
        return "NN"
    return "STRADDLE"


def path_guards(node, mode, acc):
    """模式选定路径上遇到的全部 ite guard（DerivSafeOnM 路径镜像：
    ite 只进选中支，其余构造子遍历全部子树）。"""
    if node.op == ".ite":
        acc.append(node.kids[0])
        path_guards(node.kids[2] if mode == "else" else node.kids[1], mode, acc)
        return
    for kd in node.kids:
        if hasattr(kd, "op"):
            path_guards(kd, mode, acc)


def cert_list(tree, src, mode):
    certs = []
    walk_dsafe_path(tree, src, mode, certs)
    return certs


def cmd_boxes(case_path, cert_path, j, k, stride, skip, want_else, extra_cap,
              out_path, rung_n, rung_out):
    from emit_lean import box_frac, box_lit
    case = json.load(open(case_path))
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    tree = parse_sexpr(expr)
    cert = json.load(open(cert_path))
    leaves = cert["leaves"]
    total = len(leaves)
    if stride <= 0:
        stride = max(1, total // max(1, k))
    gt, ge = [], []
    path_guards(tree, "then", gt)
    path_guards(tree, "else", ge)
    print(f"census: total {total} leaves, stride {stride}, skip {skip}; "
          f"guards then-path={len(gt)} else-path={len(ge)}")

    # 模式一致性自检：else 路径的前缀 guard 集应含 then 路径 guard 集
    # （同根 ite）。不强制，仅打印。

    rows = []
    gstat = {"NEG": 0, "NN": 0, "STRADDLE": 0, "SQRTNEG": 0}
    mstat = {"then": 0, "else": 0, "none": 0}
    extra_scanned = 0

    def census_leaf(idx):
        nonlocal extra_scanned
        leaf = leaves[idx]
        # 精确有理盒（box_frac 的 (m,e) dyadic 对 → Fraction）
        boxfr = [(Fraction(c[0]["num"], c[0]["den"]),
                  Fraction(c[1]["num"], c[1]["den"])) for c in leaf["box"]]
        tg = [guard_sign(g, boxfr) for g in gt]
        eg = [guard_sign(g, boxfr) for g in ge]
        for s in tg + eg:
            gstat[s] += 1
        then_ok = all(s == "NEG" for s in tg)
        else_ok = all(s == "NN" for s in eg)
        mode = "then" if then_ok else ("else" if else_ok else "none")
        mstat[mode] += 1
        return dict(idx=idx, cidx=idx, mode=mode, then_ok=then_ok,
                    else_ok=else_ok, then_g=tg, else_g=eg,
                    box=box_lit([box_frac(c) for c in leaf["box"]]))

    idx = skip
    while idx < total and len(rows) < k:
        rows.append(census_leaf(idx))
        idx += stride
    # else 补样：继续 stride 扫描直至 want_else 个 else 叶或 extra_cap 封顶
    if want_else > 0:
        have = sum(1 for r in rows if r["mode"] == "else")
        while idx < total and extra_scanned < extra_cap and have < want_else:
            r = census_leaf(idx)
            extra_scanned += 1
            if r["mode"] != "none":
                rows.append(r)
                if r["mode"] == "else":
                    have += 1
            idx += stride
        print(f"extra scan for else: scanned {extra_scanned}, got {have} else total")

    meta = dict(schema="census549", case=case_path, cert=cert_path, j=j,
                k=k, stride=stride, skip=skip, total=total, n=n,
                counts=[nsqrt, ndiv, ntrans], guards_then=len(gt),
                guards_else=len(ge), sampled=len(rows))
    with open(out_path, "w") as f:
        f.write(json.dumps(meta) + "\n")
        for r in rows:
            f.write(json.dumps(r) + "\n")
    ns = len(rows)
    print(f"sampled {ns}: mode then={mstat['then']} ({mstat['then']/ns:.1%}) "
          f"else={mstat['else']} ({mstat['else']/ns:.1%}) "
          f"none={mstat['none']} ({mstat['none']/ns:.1%})")
    print(f"guard signs (all paths): {gstat}")
    print(f"wrote {out_path}")


# ---- stage-A 批量探针（逐探针毫秒计时版） ----

STAGEA3_TMPL = """/-  emit_mono.py batched stage-A probe driver, ms-timed (scratch). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Kepler.Interval

namespace Probe{mod}

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

instance : Inhabited (IExpr {n}) := ⟨.const ⟨0, 0⟩⟩

def Exprs : Array (IExpr {n}) := #[
    {exprs}
]

def Ps (nsqrt ndiv ntrans : ℕ) : TMParams :=
  ⟨List.replicate nsqrt ⟨0, 0, 0, ({gran}), ({gran})⟩,
   List.replicate ndiv ⟨({gran}), ({gran}), ({gran})⟩,
   List.replicate ntrans ⟨({gran}), ({gran})⟩⟩

/-- probes: (exprIdx, box, nsqrt, ndiv, ntrans) -/
def Probes : Array (ℕ × (Fin {n} → DInterval) × ℕ × ℕ × ℕ) := #[
    {probes}
]

end Probe{mod}

open Probe{mod} in
def main : List String → IO UInt32 := fun _ => do
  IO.println "RUNG mono3"
  for i in [0:Probes.size] do
    let (ei, bx, ns, ni, nt) := Probes[i]!
    let t0 ← IO.monoMsNow
    match tmHullLeafProbe Exprs[ei]! bx (Ps ns ni nt) with
    | some (p, m, e, l) =>
        let t1 ← IO.monoMsNow
        let v : String := if p then "PASS" else "NEG"
        let trip := String.intercalate " " (l.map fun t => s!"{{t.1}} {{t.2.1}} {{t.2.2}}")
        IO.println s!"{{i}} {{v}} {{m}} {{e}} {{t1-t0}} {{trip}}"
    | none =>         IO.println s!"{{i}} FAIL 0 0 0"
  return 0
"""


def run_stagea3(mod, n, exprs, probes, gran, tmpdir="/tmp/opencode"):
    """批量 stage-A（ms 计时）。probes: (expr_idx, box_text, ns, ni, nt)。
    返回 rows: list of (verdict, lo_m, lo_e, ms, triples)。"""
    path = f"{tmpdir}/{mod}_stagea.lean"
    text = STAGEA3_TMPL.format(
        mod=mod, n=n,
        exprs=",\n    ".join(f"({e} : IExpr {n})" for e in exprs),
        gran=gran,
        probes=",\n    ".join(f"({ei}, ({bt} : Fin {n} → DInterval), {ns}, {ni}, {nt})"
                              for ei, bt, ns, ni, nt in probes))
    with open(path, "w") as f:
        f.write(text)
    lean_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean")
    proc = subprocess.run(["lake", "env", "lean", "--run", path], cwd=lean_root,
                          capture_output=True, text=True, timeout=7200)
    out = proc.stdout
    if "RUNG mono3" not in out:
        die(f"stage-A {mod} failed: {proc.stderr[-2000:]}")
    rows = []
    for ln in out.splitlines():
        tk = ln.split()
        if len(tk) >= 5 and tk[0].isdigit():
            if tk[1] == "FAIL":
                rows.append(("FAIL", 0, 0, int(tk[4]), []))
            else:
                trip = [int(x) for x in tk[5:]]
                rows.append((tk[1], int(tk[2]), int(tk[3]), int(tk[4]),
                             [tuple(trip[q:q + 3]) for q in range(0, len(trip), 3)]))
    if len(rows) != len(probes):
        die(f"stage-A rows {len(rows)} != probes {len(probes)}")
    return rows


# ---- cert 层瘦身工位：裸区间（evalIParams）定号探针 ----
# guard/div/sqrt 证书叶的区间路线对照：evalIParamsFill 是已证 sound 的
# evalIParams 的编译镜像（CertTM.lean），探针回传区间端点 mantissa 与
# sqrt 证书三元组（烘回内核侧 sqrtCerts 后内核 evalIParams 复现同一区间）。

STAGEA4_TMPL = """/-  emit_mono.py interval-probe driver (scratch). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Kepler.Interval

namespace Probe{mod}

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

instance : Inhabited (IExpr {n}) := ⟨.const ⟨0, 0⟩⟩

def Exprs : Array (IExpr {n}) := #[
    {exprs}
]

def Ps (nsqrt ndiv ntrans : ℕ) : TMParams :=
  ⟨List.replicate nsqrt ⟨0, 0, 0, ({gran}), ({gran})⟩,
   List.replicate ndiv ⟨({gran}), ({gran}), ({gran})⟩,
   List.replicate ntrans ⟨({gran}), ({gran})⟩⟩

/-- probes: (exprIdx, box, nsqrt, ndiv, ntrans) -/
def Probes : Array (ℕ × (Fin {n} → DInterval) × ℕ × ℕ × ℕ) := #[
    {probes}
]

/-- 裸区间探针：区间端点 mantissa/exponent + sqrt 证书三元组（实验对照）。 -/
def iLeafProbe {{n : ℕ}} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) :
    Option (Int × Int × Int × Int × List (Int × Int × Int)) :=
  (evalIParamsFill box e ps).map fun (I, _, l) =>
    (I.lo.m, I.lo.e, I.hi.m, I.hi.e, l)

end Probe{mod}

open Probe{mod} in
def main : List String → IO UInt32 := fun _ => do
  IO.println "RUNG mono4"
  for i in [0:Probes.size] do
    let (ei, bx, ns, ni, nt) := Probes[i]!
    let t0 ← IO.monoMsNow
    match iLeafProbe Exprs[ei]! bx (Ps ns ni nt) with
    | some (lm, le, hm, he, l) =>
        let t1 ← IO.monoMsNow
        let trip := String.intercalate " " (l.map fun t => s!"{{t.1}} {{t.2.1}} {{t.2.2}}")
        IO.println s!"{{i}} IV {{lm}} {{le}} {{hm}} {{he}} {{t1-t0}} {{trip}}"
    | none =>         IO.println s!"{{i}} FAIL 0 0 0 0 0"
  return 0
"""


def run_stagea4(mod, n, exprs, probes, gran, tmpdir="/tmp/opencode"):
    """裸区间批量探针。probes: (expr_idx, box_text, ns, ni, nt)。
    返回 rows: list of (verdict, lo_m, lo_e, hi_m, hi_e, ms, triples)。"""
    path = f"{tmpdir}/{mod}_stagea.lean"
    text = STAGEA4_TMPL.format(
        mod=mod, n=n,
        exprs=",\n    ".join(f"({e} : IExpr {n})" for e in exprs),
        gran=gran,
        probes=",\n    ".join(f"({ei}, ({bt} : Fin {n} → DInterval), {ns}, {ni}, {nt})"
                              for ei, bt, ns, ni, nt in probes))
    with open(path, "w") as f:
        f.write(text)
    lean_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean")
    proc = subprocess.run(["lake", "env", "lean", "--run", path], cwd=lean_root,
                          capture_output=True, text=True, timeout=7200)
    out = proc.stdout
    if "RUNG mono4" not in out:
        die(f"stage-A interval {mod} failed: {proc.stderr[-2000:]}")
    rows = []
    for ln in out.splitlines():
        tk = ln.split()
        if len(tk) >= 7 and tk[0].isdigit():
            trip = [int(x) for x in tk[7:]]
            rows.append((tk[1], int(tk[2]), int(tk[3]), int(tk[4]), int(tk[5]),
                         int(tk[6]),
                         [tuple(trip[q:q + 3]) for q in range(0, len(trip), 3)]))
    if len(rows) != len(probes):
        die(f"stage-A interval rows {len(rows)} != probes {len(probes)}")
    return rows


def read_jsonl(path):
    rows = []
    with open(path) as f:
        for ln in f:
            ln = ln.strip()
            if ln:
                rows.append(json.loads(ln))
    return rows


def cmd_probe(case_path, census_path, stage, der_path, from_, to_, gran,
              rung_n, rung_out, out_path, tag, route="tm"):
    from emit_lean import box_frac, box_lit
    case = json.load(open(case_path))
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    tree = parse_sexpr(expr)
    src = expr
    meta = read_jsonl(census_path)[0]
    rows = [r for r in read_jsonl(census_path) if "mode" in r][from_:to_]
    j = int(meta["j"])

    # 模式缓存：导数表达式与证书清单
    dexprs = {"then": dtext_then(tree, src, j),
              "else": dtextM(tree, src, j, "else")}
    dcounts = {m: node_counts(d) for m, d in dexprs.items()}
    certs = {m: cert_list(tree, src, m) for m in ("then", "else")}

    exprs, expr_idx = [], {}

    def eid(t):
        if t not in expr_idx:
            expr_idx[t] = len(exprs)
            exprs.append(t)
        return expr_idx[t]

    probes, meta_tags = [], []

    def add_probe(tagl, text, box, ns, ni, nt):
        probes.append((eid(text), box, ns, ni, nt))
        meta_tags.append(tagl)

    if stage == "der":
        for r in rows:
            if r["mode"] == "none":
                continue
            d = dexprs[r["mode"]]
            ns, ni, nt = dcounts[r["mode"]]
            add_probe((r["idx"], "lo"), d, r["box"], ns, ni, nt)
            add_probe((r["idx"], "hi"), f"(.neg {d})", r["box"], ns, ni, nt)
    elif stage == "cert":
        for r in rows:
            if r["mode"] == "none":
                continue
            if route == "interval":
                # 裸区间路线：每证书只探首选形（iteNeg→neg / divNe→pos /
                # sqrtPos→pos；即发射侧将采用的形式）。
                for ci, c in enumerate(certs[r["mode"]]):
                    fl, ft = c["forms"][0]
                    fs, fi, ftn = node_counts(ft)
                    add_probe((r["idx"], ci, fl), ft, r["box"], fs, fi, ftn)
            else:
                for ci, c in enumerate(certs[r["mode"]]):
                    for fl, ft in c["forms"]:
                        fs, fi, ftn = node_counts(ft)
                        add_probe((r["idx"], ci, fl), ft, r["box"], fs, fi, ftn)
    elif stage == "full":
        for r in rows:
            add_probe((r["idx"], "full"), expr, r["box"], nsqrt, ndiv, ntrans)
    elif stage == "face":
        if not der_path:
            die("face stage needs --der")
        by_leaf = {}
        for d in read_jsonl(der_path):
            if d["v"] == "PASS":
                by_leaf.setdefault(d["idx"], set()).add(d["dir"])
        for r in rows:
            dirs = by_leaf.get(r["idx"], set())
            if not dirs:
                continue
            dl = "lo" if "lo" in dirs else "hi"
            fb = face_box_lit(re.findall(r"⟨⟨[^⟨⟩]*⟩, ⟨[^⟨⟩]*⟩⟩", r["box"]),
                              int(meta["j"]), hi=(dl == "hi"))
            add_probe((r["idx"], dl), expr, fb, nsqrt, ndiv, ntrans)
    else:
        die(f"unknown stage {stage}")

    print(f"probe {stage}{tag}[{route}]: {len(rows)} leaves, {len(probes)} probes, "
          f"{len(exprs)} distinct exprs")
    if not probes:
        die("no probes")
    if stage == "cert" and route == "interval":
        res = run_stagea4(f"I{stage}{tag}", n, exprs, probes, gran)
    else:
        res = run_stagea3(f"M{stage}{tag}", n, exprs, probes, gran)
    with open(out_path, "w") as f:
        f.write(json.dumps(dict(schema=f"probe549-{stage}", case=case_path,
                                census=census_path, j=meta["j"], gran=gran,
                                route=route, counts=meta.get("counts"),
                                tag=tag)) + "\n")
        for mt, rr in zip(meta_tags, res):
            if stage == "cert" and route == "interval":
                vv, lm, le, hm, he, ms, trip = rr
                # 与 TM 路线同构：form 文本（(.neg g)/(.abs den)/裸式）的区间
                # 下端 > 0 即 PASS（checkPosI 语义）。
                v = ("PASS" if lm > 0 else "NEG") if vv == "IV" else "FAIL"
                rec = dict(idx=mt[0], v=v, ms=ms, trip=trip, iv=[lm, le, hm, he])
                rec["ci"], rec["form"] = mt[1], mt[2]
                f.write(json.dumps(rec) + "\n")
                continue
            v, m_, e_, ms, trip = rr
            rec = dict(idx=mt[0], v=v, ms=ms, trip=trip)
            if stage == "der":
                rec["dir"] = mt[1]
                rec["dcounts"] = list(dcounts[r_mode_of(rows, mt[0])])
            elif stage == "cert":
                rec["ci"], rec["form"] = mt[1], mt[2]
            elif stage == "face":
                rec["dir"] = mt[1]
            if v != "FAIL":
                # Taylor 下界 (mantissa, exponent)——归因/相关性分析用
                # （loBound ≤ 0 的 NEG 叶给出余项肥瘦的直接度量）。
                rec["lb_m"], rec["lb_e"] = m_, e_
            f.write(json.dumps(rec) + "\n")
    npass = sum(1 for r in res if r[0] in ("PASS", "IV"))
    ms_all = [r[5] if (stage == "cert" and route == "interval") else r[3]
              for r in res if r[0] != "FAIL"]
    print(f"probe {stage}{tag}: PASS {npass}/{len(res)}"
          + (f"  ms med={sorted(ms_all)[len(ms_all)//2]} max={max(ms_all)}"
             if ms_all else ""))
    print(f"wrote {out_path}")


def r_mode_of(rows, idx):
    for r in rows:
        if r["idx"] == idx:
            return r["mode"]
    die(f"idx {idx} not in census rows")


# ---- 全量评估出题（shard / baseline / native 对照 / 三层阶梯） ----

def gather_complete(case_path, census_path, der_path, face_path, cert_path,
                    full_path, gran, rung_n, rung_out):
    """汇总各 stage 判定，选出全链完备叶；返回 (meta, expr, counts, tree, src,
    j, complete_leaves, stats)。complete_leaves 项:
    dict(idx, mode, dir, box, fbox, pf, dp, dexpr, dcounts,
         certs=[(ci, kind, sub, form, form_text, trip, counts, ms)],
         ms={face,der,cert,full}, full=None|trip)"""
    case = json.load(open(case_path))
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    tree = parse_sexpr(expr)
    src = expr
    meta = read_jsonl(census_path)[0]
    j = int(meta["j"])
    rows = {r["idx"]: r for r in read_jsonl(census_path) if "mode" in r}

    def load_stage(path):
        if not path:
            return {}
        out = {}
        for r in read_jsonl(path)[1:]:
            out.setdefault(r["idx"], []).append(r)
        return out

    der = load_stage(der_path)
    face = load_stage(face_path)
    cert = load_stage(cert_path)
    full = load_stage(full_path)

    dexprs = {"then": dtext_then(tree, src, j), "else": dtextM(tree, src, j, "else")}
    dcounts = {m: node_counts(d) for m, d in dexprs.items()}
    certs_by_mode = {m: cert_list(tree, src, m) for m in ("then", "else")}

    complete = []
    stats = dict(n=len(rows), mode_then=0, mode_else=0, mode_none=0,
                 der_ok=0, face_ok=0, cert_ok=0, all_ok=0,
                 ms=dict(face=0, der=0, cert=0, full=0), ms_fullbox=[])
    for idx, r in sorted(rows.items()):
        if r["mode"] == "none":
            stats["mode_none"] += 1
            continue
        stats[f"mode_{r['mode']}"] += 1
        drs = [d for d in der.get(idx, []) if d["v"] == "PASS"]
        dirs = {d["dir"] for d in drs}
        dl = "lo" if "lo" in dirs else ("hi" if "hi" in dirs else None)
        if dl is None:
            continue
        stats["der_ok"] += 1
        drec = next(d for d in drs if d["dir"] == dl)
        frc = [f for f in face.get(idx, []) if f["dir"] == dl and f["v"] == "PASS"]
        if not frc:
            continue
        stats["face_ok"] += 1
        frec = frc[0]
        by_ci = {}
        for c in cert.get(idx, []):
            by_ci.setdefault(c["ci"], []).append(c)
        picked, ok, ms_cert = [], True, 0
        for ci, c in enumerate(certs_by_mode[r["mode"]]):
            forms_rank = [fl for fl, _ in c["forms"]]
            cands = [x for x in by_ci.get(ci, []) if x["v"] == "PASS"]
            cands.sort(key=lambda x: forms_rank.index(x["form"]))
            if not cands:
                ok = False
                break
            x = cands[0]
            form_text = [ft for fl, ft in c["forms"] if fl == x["form"]][0]
            picked.append((ci, c["kind"], c["sub"], x["form"], form_text,
                           x["trip"], node_counts(form_text), x["ms"]))
            ms_cert += x["ms"]
        if not ok:
            continue
        stats["cert_ok"] += 1
        stats["all_ok"] += 1
        coords = re.findall(r"⟨⟨[^⟨⟩]*⟩, ⟨[^⟨⟩]*⟩⟩", r["box"])
        fbox = face_box_lit(coords, j, hi=(dl == "hi"))
        frecs_full = full.get(idx) or []
        full_rec = frecs_full[0] if frecs_full and frecs_full[0]["v"] == "PASS" \
            else (frecs_full[0] if frecs_full else None)
        item = dict(idx=idx, mode=r["mode"], dir=dl, box=r["box"], fbox=fbox,
                    pf=frec["trip"], dp=drec["trip"],
                    dexpr=dexprs[r["mode"]], dcounts=dcounts[r["mode"]],
                    certs=picked,
                    ms=dict(face=frec["ms"], der=drec["ms"], cert=ms_cert,
                            full=(full_rec["ms"] if full_rec else None)),
                    full=(full_rec["trip"] if full_rec else None),
                    full_v=(full_rec["v"] if full_rec else None))
        stats["ms"]["face"] += item["ms"]["face"]
        stats["ms"]["der"] += item["ms"]["der"]
        stats["ms"]["cert"] += item["ms"]["cert"]
        if item["ms"]["full"] is not None:
            stats["ms"]["full"] += item["ms"]["full"]
            if item["full_v"] == "PASS":
                stats["ms_fullbox"].append(item["ms"]["full"])
        complete.append(item)
    return meta, expr, (nsqrt, ndiv, ntrans), tree, src, j, complete, stats


CERT_LEMMA = {("divNe", "pos"): "safeDivPos", ("divNe", "neg"): "safeDivNeg",
              ("divNe", "abs"): "safeDivAbs", ("lnNe", "pos"): "safeDivPos",
              ("lnNe", "neg"): "safeDivNeg", ("lnNe", "abs"): "safeDivAbs",
              ("sqrtPos", "pos"): "safeSqrtPos", ("iteNeg", "neg"): "safeIteNeg",
              ("iteNN", "pos"): "safeIteNN"}

# 裸区间路线（C549CertSlimDefs）：discharge 引理 + Bool 检查器。
# 只走已证 sound 路径（checkPosI_sound 等由 evalIParams_mem 组装，标准三公理）。
# 关键同构：form 文本已携带 neg/abs 包裹（(.neg guard)/(.abs den)），而
# checkPosTMHull 与 checkPosI 一样断言"给定表达式 > 0"——故所有形统一走
# checkPosI；discharge 引理按 (kind, form) 选同型包装（safeIteNegI 等）。
CERT_ROUTE_I = {("divNe", "pos"): ("safeDivPosI", "checkPosI"),
                ("divNe", "neg"): ("safeDivNegI", "checkPosI"),
                ("divNe", "abs"): ("safeDivAbsI", "checkPosI"),
                ("lnNe", "pos"): ("safeDivPosI", "checkPosI"),
                ("lnNe", "neg"): ("safeDivNegI", "checkPosI"),
                ("lnNe", "abs"): ("safeDivAbsI", "checkPosI"),
                ("sqrtPos", "pos"): ("safeSqrtPosI", "checkPosI"),
                ("iteNeg", "neg"): ("safeIteNegI", "checkPosI"),
                ("iteNN", "pos"): ("safeIteNNI", "checkPosI")}


def cert_target(kind, sub):
    if kind in ("divNe", "lnNe"):
        return f"IExpr.evalReal ({sub}) ρ ≠ 0"
    if kind == "sqrtPos":
        return f"0 < IExpr.evalReal ({sub}) ρ"
    if kind == "iteNeg":
        return f"IExpr.evalReal ({sub}) ρ < 0"
    return f"0 ≤ IExpr.evalReal ({sub}) ρ"


def shard_module_text(ns, n, expr, leaves, j, gran, ndiv, ntrans, decide_tac,
                      layers, tag, cert_route="tm"):
    """全链 shard 模块文本。layers ⊆ {"cert","der","face","fold"}（阶梯计时用
    子集）；decide_tac 为 "decide" 或 "native_decide"（实验对照）；
    cert_route 为 "tm"（checkPosTMHull 叶，原口径）或 "interval"
    （checkNegI/checkPosI/checkNeI 裸区间叶，C549CertSlimDefs 路线）。"""
    imports = "import Kepler.Interval.Cases.C549Mono\n"
    if cert_route == "interval":
        imports += "import Kepler.Interval.Cases.C549CertSlimDefs\n"
    parts = [imports,
             "/-! ## 549 facePos 全量评估（emit_mono.py 生成；勿手改）。\n\n"
             f"{ns} — {tag}\n"
             "每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 DSafe ⇒\n"
             "checkPosFace*_sound ⇒ 全盒语义正性 0 < evalReal ρ。\n"
             f"本模块层级：{sorted(layers)}；decide 战术：{decide_tac}。 -/\n",
             "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n",
             f"namespace Kepler.Interval.{ns}\n\nopen Kepler.Interval\n",
             "/-- case 549 表达式（本模块自包含副本）. -/",
             f"def E549 : IExpr {n} :=\n  {expr}"]
    for L in leaves:
        i = L["idx"]
        mode, dl = L["mode"], L["dir"]
        E = "E" if mode == "else" else ""
        dircap = "Lo" if dl == "lo" else "Hi"
        dref = f"(derivIExpr{E} E549 {j})"
        derx = dref if dl == "lo" else f"(IExpr.neg {dref})"
        parts.append(f"/-- 叶 {i}（{mode} 支，{dl} 面）原盒. -/")
        parts.append(f"def B{i} : Fin {n} → DInterval :=\n  {L['box']}")
        if "cert" in layers:
            for (ci, kind, sub, form, form_text, trip, (fs, fi, ft), _ms) in L["certs"]:
                if cert_route == "interval":
                    lemma, checker = CERT_ROUTE_I[(kind, form)]
                    parts.append(f"/-- 证书叶 {i}.C{ci}（{kind}，{form} 形，"
                                 f"裸区间 {checker}）. -/")
                    parts.append(f"def S{i}C{ci}P : TMParams :=\n  "
                                 f"{params_lit(trip, 0, 0, gran)}")
                    parts.append(f"theorem S{i}C{ci} :\n    {checker}\n"
                                 f"    ({form_text}) B{i} S{i}C{ci}P = true := by\n"
                                 f"  {decide_tac}")
                else:
                    lemma = CERT_LEMMA[(kind, form)]
                    parts.append(f"/-- 证书叶 {i}.C{ci}（{kind}，{form} 形）. -/")
                    parts.append(f"def S{i}C{ci}P : TMParams :=\n  "
                                 f"{params_lit(trip, fi, ft, gran)}")
                    parts.append(f"theorem S{i}C{ci} :\n    checkPosTMHull "
                                 f"({form_text}) B{i} S{i}C{ci}P = true := by\n"
                                 f"  {decide_tac}")
                parts.append(f"/-- 逐节点前提（{lemma}）叶 {i}.C{ci}. -/")
                parts.append(f"theorem S{i}D{ci} (ρ : Fin {n} → ℝ) "
                             f"(hρ : boxMem B{i} ρ) :\n    "
                             f"{cert_target(kind, sub)} :=\n"
                             f"  {lemma} S{i}C{ci} ρ hρ")
        if "der" in layers:
            parts.append(f"/-- 导数叶 {i}（{'+' if dl == 'lo' else '−'}∂x{j+1}f，"
                         f"{mode} 支，全盒）. -/")
            parts.append(f"def DP{i} : TMParams :=\n  "
                         f"{params_lit(L['dp'], L['dcounts'][1], L['dcounts'][2], gran)}")
            parts.append(f"theorem Der{i} :\n    checkPosTMHull {derx} B{i} DP{i}"
                         f"\n    = true := by\n  {decide_tac}")
        if "face" in layers:
            parts.append(f"/-- 面叶 {i}（{dl} 面）. -/")
            parts.append(f"def FB{i} : Fin {n} → DInterval := faceBox{dircap} B{i} {j}")
            parts.append(f"def PF{i} : TMParams :=\n  "
                         f"{params_lit(L['pf'], ndiv, ntrans, gran)}")
            parts.append(f"theorem Face{i} :\n    checkPosTMHull E549 FB{i} PF{i}"
                         f"\n    = true := by\n  {decide_tac}")
        if "fold" in layers:
            cnames = {(kind, sub): f"S{i}D{ci}"
                      for (ci, kind, sub, form, form_text, trip, cnts, _ms)
                      in L["certs"]}
            parts.append(f"/-- DerivSafeOn 证书发射（叶 {i}，{mode} 支）. -/")
            parts.append(f"def DSafe{i} : DerivSafeOn{E} B{i} E549 :=\n  "
                         f"{dsafe_term(parse_sexpr(expr), expr, mode, cnames)}")
            parts.append(f"/-- mono 折叠组合（叶 {i}，两叶引用零重算）. -/")
            parts.append(f"theorem Fold{i} :\n    checkPosFace{dircap} E549 "
                         f"{dref}\n    B{i} {j} PF{i} DP{i} = true := by\n"
                         f"  have h1 : checkPosTMHull {derx} B{i} DP{i} = true := Der{i}\n"
                         f"  have h2 : checkPosTMHull E549 (faceBox{dircap} B{i} {j}) "
                         f"PF{i} = true := Face{i}\n"
                         f"  show (checkPosTMHull {derx} B{i} DP{i}"
                         f"\n      && checkPosTMHull E549 (faceBox{dircap} B{i} {j}) "
                         f"PF{i}) = true\n"
                         f"  rw [h1, h2, Bool.and_true]")
            parts.append(f"/-- 全链 fold（叶 {i}）：面叶+导数叶+证书 ⇒ 语义正性. -/")
            parts.append(f"theorem Sem{i} (ρ : Fin {n} → ℝ) (hρ : boxMem B{i} ρ) :"
                         f"\n    0 < E549.evalReal ρ :=\n  "
                         f"checkPosFace{dircap}{E}_sound DSafe{i} Fold{i} hρ")
            parts.append(f"#print axioms Sem{i}")
    parts.append(f"\nend Kepler.Interval.{ns}\n")
    return "\n\n".join(parts)


def baseline_module_text(ns, n, expr, leaves, j, gran, ndiv, ntrans):
    """同批叶原盒全叶 decide 基线模块（对照口径）。"""
    parts = ["import Kepler.Interval.CertTM\n",
             "/-! ## 549 facePos 全量评估基线（emit_mono.py 生成；勿手改）。\n\n"
             f"{ns} — 同批叶的原盒全叶 checkPosTMHull（现口径对照；decide 口径）。"
             f" -/\n",
             "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n",
             f"namespace Kepler.Interval.{ns}\n\nopen Kepler.Interval\n",
             f"def E549 : IExpr {n} :=\n  {expr}"]
    for L in leaves:
        i = L["idx"]
        parts.append(f"/-- 基线全叶 {i}（原盒）. -/")
        parts.append(f"def B{i} : Fin {n} → DInterval :=\n  {L['box']}")
        parts.append(f"def BP{i} : TMParams :=\n  "
                     f"{params_lit(L['full'], ndiv, ntrans, gran)}")
        parts.append(f"theorem Full{i} : checkPosTMHull E549 B{i} BP{i} = true "
                     f":= by\n  decide")
    parts.append(f"\nend Kepler.Interval.{ns}\n")
    return "\n\n".join(parts)


def cmd_census(case_path, j):
    case = json.load(open(case_path))
    expr, nsqrt, ndiv, ntrans = hull_expr(case, 128, -80)
    tree = parse_sexpr(expr)
    src = expr
    for mode in ("then", "else"):
        certs = []
        walk_dsafe_path(tree, src, mode, certs)
        print(f"== mode {mode} (x{j+1}, var {j}) ==")
        for c in certs:
            ns, ni, nt = node_counts(c["forms"][0][1])
            print(f"  {c['kind']}: {node_counts(c['sub'])[0]} sqrt in sub, "
                  f"cert-expr nodes~{c['forms'][0][1].count('(.')}, forms={[f[0] for f in c['forms']]}")
    d = dtext_then(tree, src, j)
    de = dtextM(tree, src, j, "else")
    print(f"der(then) nodes: {d.count('(.')}")
    print(f"der(else) nodes: {de.count('(.')}")


def cmd_pilot2(case_path, lean_path, j, k, gran, rung_n, rung_out, out_path,
               direction="lo", mode="then"):
    case = json.load(open(case_path))
    n = len(case["vars"])
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    boxes, params, verdicts = parse_leaf_defs(lean_path)
    leaves = []
    for thm, (box, par) in verdicts.items():
        if box in boxes and par in params:
            leaves.append((thm, boxes[box], params[par]))
        if len(leaves) == k:
            break
    if not leaves:
        die("no leaves found in lean file")
    print(f"pilot2 leaves: {[t[0] for t in leaves]} (j={j}, dir={direction}, mode={mode})")

    tree = parse_sexpr(expr)
    src = expr

    # 符号微分（模式镜像）与面盒
    dexpr = dtextM(tree, src, j, mode)
    d_ns, d_ni, d_nt = node_counts(dexpr)
    box_coords = []
    for b in (bl for _, bl, _ in leaves):
        coords = re.findall(r"⟨⟨[^⟨⟩]*⟩, ⟨[^⟨⟩]*⟩⟩", b)
        if len(coords) != n:
            die(f"box coord parse: got {len(coords)}, want {n}")
        box_coords.append(coords)
    face_lits = [face_box_lit(bc, j, hi=(direction == "hi")) for bc in box_coords]

    # 证书收集
    certs = []
    walk_dsafe_path(tree, src, mode, certs)

    # 批量 stage-A 探针清单
    exprs, expr_idx = [], {}

    def eid(t):
        if t not in expr_idx:
            expr_idx[t] = len(exprs)
            exprs.append(t)
        return expr_idx[t]

    probes, meta = [], []

    def add_probe(tag, text, box, ns, ni, nt):
        probes.append((eid(text), box, ns, ni, nt))
        meta.append(tag)

    for i in range(len(leaves)):
        add_probe(("face", i), expr, face_lits[i], nsqrt, ndiv, ntrans)
        add_probe(("der", i), dexpr, leaves[i][1], d_ns, d_ni, d_nt)
    for c in certs:
        for form_label, form_text in c["forms"]:
            fs, fi, ft = node_counts(form_text)
            for i in range(len(leaves)):
                add_probe((c["kind"], c["sub"], form_label, i), form_text,
                          leaves[i][1], fs, fi, ft)

    print(f"stage-A: {len(exprs)} exprs, {len(probes)} probes")
    rows = run_stagea2("Mono2", n, exprs, probes, gran)
    R = dict(zip(meta, rows))

    # 汇总各叶证书形态择优
    leaf_certs = []  # per leaf: list of dict(cert, form_label, verdict, triples, thmname)
    all_ok = True
    for c in certs:
        picked = []
        for i in range(len(leaves)):
            ok_forms = [(fl, R[(c["kind"], c["sub"], fl, i)])
                        for fl, _ft in c["forms"]
                        if R[(c["kind"], c["sub"], fl, i)][0] == "PASS"]
            if not ok_forms:
                picked.append(None)
                all_ok = False
                verdicts_seen = [R[(c["kind"], c["sub"], fl, i)][0]
                                 for fl, _ft in c["forms"]]
                print(f"  cert {c['kind']} leaf {i}: no PASS form {verdicts_seen}")
            else:
                picked.append((ok_forms[0][0], ok_forms[0][1]))
        leaf_certs.append(picked)

    fv = [R[("face", i)] for i in range(len(leaves))]
    dv = [R[("der", i)] for i in range(len(leaves))]

    # ---- Lean 生成 ----
    dircap = "Lo" if direction == "lo" else "Hi"
    dirsign = "+" if direction == "lo" else "-"
    dref = f"(derivIExpr C549M2Expr {j})" if mode == "then" \
        else f"(derivIExprE C549M2Expr {j})"
    sound_thm = f"checkPosFace{dircap}{'E' if mode == 'else' else ''}_sound"
    parts = []
    parts.append("import Kepler.Interval.Cases.C549Mono\n")
    parts.append("""/-! ## 549 mono 全链试点（pipeline/interval/emit_mono.py 生成；勿手改）。

每叶：面叶 + 导数叶 + DerivSafeOn 证书叶 ⇒ 嵌套 `DerivSafeOnM` 证明项 ⇒
`checkPosFace*_sound` ⇒ 全盒语义正性 `0 < e.evalReal ρ`。
自包含性：import C549Mono（facePos/derivIExprM/safe* 基础设施）+ CertTM（传递）。 -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases2

open Kepler.Interval
""")
    parts.append(f"/-- The case expression（逐字复制 C549Hull200.lean 的 "
                 f"C549Hull200Expr，本模块自包含副本）. -/")
    parts.append(f"def C549M2Expr : IExpr {n} :=")
    parts.append(f"  {expr}")
    for idx, (thm, bl, pl) in enumerate(leaves):
        parts.append(f"/-- Cert leaf {idx}（{thm}）原盒（逐字复制）. -/")
        parts.append(f"def C549M2Box{idx+1} : Fin {n} → DInterval :=")
        parts.append(f"  {bl}")

    # 证书叶（每叶独立盒 ⇒ 定理逐叶特化；同名证书跨叶共享子表达式）
    for ci, c in enumerate(certs):
        for idx in range(len(leaves)):
            pk = leaf_certs[ci][idx]
            if pk is None:
                continue
            form_label, (verd, m_, e_, trip) = pk
            form_text = [f[1] for f in c["forms"] if f[0] == form_label][0]
            cthm = f"C549M2S{idx+1}C{ci}"
            dthm = f"C549M2S{idx+1}D{ci}"
            fs, fi, ft = node_counts(form_text)
            sub = c["sub"]
            if c["kind"] in ("divNe", "lnNe"):
                lemma = {"pos": "safeDivPos", "neg": "safeDivNeg",
                         "abs": "safeDivAbs"}[form_label]
                target = f"IExpr.evalReal ({sub}) ρ ≠ 0"
            elif c["kind"] == "sqrtPos":
                lemma, target = "safeSqrtPos", f"0 < IExpr.evalReal ({sub}) ρ"
            elif c["kind"] == "iteNeg":
                lemma, target = "safeIteNeg", f"IExpr.evalReal ({sub}) ρ < 0"
            else:  # iteNN
                lemma, target = "safeIteNN", f"0 ≤ IExpr.evalReal ({sub}) ρ"
            parts.append(f"""/-- 证书叶 {ci}（{c['kind']}，{form_label} 形；stage-A {verd}）. -/
def {cthm}P : TMParams :=
  {params_lit(trip, fi, ft, gran)}

theorem {cthm} :
    checkPosTMHull ({form_text}) C549M2Box{idx+1} {cthm}P = true := by
  decide

/-- 逐节点前提（discharge 引理 `{lemma}`）. -/
theorem {dthm} (ρ : Fin {n} → ℝ) (hρ : boxMem C549M2Box{idx+1} ρ) :
    {target} :=
  {lemma} {cthm} ρ hρ""")

    # 每叶：面盒/参数/两叶/DSafe/fold/semantic
    for idx in range(len(leaves)):
        cnames = {}
        for ci, c in enumerate(certs):
            if leaf_certs[ci][idx] is None:
                cnames[(c["kind"], c["sub"])] = None
            else:
                cnames[(c["kind"], c["sub"])] = f"C549M2S{idx+1}D{ci}"
        leaf_complete = (fv[idx][0] == "PASS" and dv[idx][0] == "PASS"
                         and all(v is not None for v in cnames.values()))
        fv_ = fv[idx]
        dv_ = dv[idx]
        parts.append(f"""/-- Cert leaf {idx}（{leaves[idx][0]}）的 {direction} 面盒（x{j+1} 钉端点）. -/
def C549M2FaceBox{idx+1} : Fin {n} → DInterval :=
  {face_lits[idx]}

/-- 面叶参数（stage-A 收割，verdict {fv_[0]}）. -/
def C549M2PF{idx+1} : TMParams :=
  {params_lit(fv_[3], ndiv, ntrans, gran)}

/-- 导数叶参数（stage-A 收割，verdict {dv_[0]}）. -/
def C549M2DP{idx+1} : TMParams :=
  {params_lit(dv_[3], d_ni, d_nt, gran)}

/-- 面叶（原表达式于 {direction} 面盒）. -/
theorem C549M2Face{idx+1} :
    checkPosTMHull C549M2Expr (faceBox{dircap} C549M2Box{idx+1} {j}) C549M2PF{idx+1} = true := by
  decide

/-- 导数定号叶（{dirsign}∂x{j+1}f，{'then' if mode == 'then' else 'else'} 支，全盒）. -/
theorem C549M2Der{idx+1} :
    checkPosTMHull ({dref_neg(dref, direction)})
      C549M2Box{idx+1} C549M2DP{idx+1} = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549M2Fold{idx+1} :
    checkPosFace{dircap} C549M2Expr {dref}
      C549M2Box{idx+1} {j} C549M2PF{idx+1} C549M2DP{idx+1} = true := by
  simp only [checkPosFace{dircap}, Bool.and_eq_true]
  exact ⟨C549M2Der{idx+1}, C549M2Face{idx+1}⟩
""")
        if not leaf_complete:
            parts.append(f"""/-- 叶 {idx}：证书/两叶不完备（诚实 NEG）——不发射 DSafe/Sem. -/
""")
            continue
        dsafe = dsafe_term(tree, src, mode, cnames)
        sound_thm = f"checkPosFace{dircap}{'E' if mode == 'else' else ''}_sound"
        parts.append(f"""/-- **DerivSafeOn 证书发射**：逐节点拼装（证书叶 discharge；模式 {mode}）. -/
def C549M2DSafe{idx+1} : DerivSafeOn{'E' if mode == 'else' else ''} C549M2Box{idx+1} C549M2Expr :=
  {dsafe}

/-- **全链 fold**：面叶 + 导数叶 + DSafe 证书 ⇒ 全盒语义正性. -/
theorem C549M2Sem{idx+1} (ρ : Fin {n} → ℝ) (hρ : boxMem C549M2Box{idx+1} ρ) :
    0 < C549M2Expr.evalReal ρ :=
  {sound_thm} C549M2DSafe{idx+1} C549M2Fold{idx+1} hρ

#print axioms C549M2Sem{idx+1}""")

    parts.append("\nend Kepler.Interval.Cases2\n")
    out = "\n\n".join(parts)
    if bal(dexpr) != 0:
        die("emitted DExpr unbalanced")
    if out_path:
        with open(out_path, "w") as f:
            f.write(out)
        print(f"wrote {out_path}")
    for i in range(len(leaves)):
        cs = sum(1 for ci in range(len(certs)) if leaf_certs[ci][i] is not None)
        print(f"leaf {i} ({leaves[i][0]}): face {fv[i][0]}  der {dv[i][0]}  "
              f"certs {cs}/{len(certs)}  SEM {'OK' if all(x is not None for x in (leaf_certs[ci][i] for ci in range(len(certs)))) and fv[i][0]=='PASS' and dv[i][0]=='PASS' else 'INCOMPLETE'}")


def dref_neg(dref, direction):
    return f"(IExpr.neg {dref})" if direction == "hi" else dref


def cmd_emit(case_path, census_path, der_path, face_path, cert_path, full_path,
             out_dir, shard_size, name, do_baseline, do_native, do_ladder,
             gran, rung_n, rung_out, cert_route="tm", ns_prefix=None):
    meta, expr, (nsqrt, ndiv, ntrans), tree, src, j, comp, stats = \
        gather_complete(case_path, census_path, der_path, face_path, cert_path,
                        full_path, gran, rung_n, rung_out)
    n = int(meta["n"])
    print(f"emit: census {stats['n']} = then {stats['mode_then']} + "
          f"else {stats['mode_else']} + none {stats['mode_none']}; "
          f"der_ok {stats['der_ok']}  face_ok {stats['face_ok']}  "
          f"cert_ok {stats['cert_ok']}  ALL {stats['all_ok']}")
    print(f"emit: per-layer ms totals over ALL_OK leaves: {stats['ms']}")
    if not comp:
        die("no complete leaves")
    os.makedirs(out_dir, exist_ok=True)
    base = ns_prefix or f"C549MonoEval{name}"
    import math
    nsh = max(1, math.ceil(len(comp) / shard_size))
    manifest = []
    for s in range(nsh):
        batch = comp[s * shard_size:(s + 1) * shard_size]
        ns = f"{base}{s+1}"
        text = shard_module_text(ns, n, expr, batch, j, gran, ndiv, ntrans,
                                 "decide", ("cert", "der", "face", "fold"),
                                 f"全量评估 shard {s+1}/{nsh}（{len(batch)} 叶；"
                                 f"modes {sorted(set(b['mode'] for b in batch))}）",
                                 cert_route=cert_route)
        path = os.path.join(out_dir, f"{ns}.lean")
        with open(path, "w") as f:
            f.write(text)
        print(f"wrote {path} ({len(batch)} leaves)")
        for L in batch:
            manifest.append(dict(shard=s + 1, **{k: L[k] for k in
                                                 ("idx", "mode", "dir", "ms")}))
    with open(os.path.join(out_dir, f"{name}.manifest.json"), "w") as f:
        json.dump(manifest, f, indent=1)
    first = comp[:shard_size]
    if do_baseline:
        need = [L for L in first if L["full"] is not None]
        if not need:
            print("baseline: skipped (no full harvest)")
        else:
            ns = f"C549MonoEval{name}Base"
            text = baseline_module_text(ns, n, expr, need, j, gran, ndiv, ntrans)
            path = os.path.join(out_dir, f"{ns}.lean")
            with open(path, "w") as f:
                f.write(text)
            print(f"wrote {path} ({len(need)} baseline leaves)")
    if do_native:
        ns = f"C549MonoEval{name}NativeCtl"
        text = shard_module_text(ns, n, expr, first, j, gran, ndiv, ntrans,
                                 "native_decide", ("cert", "der", "face", "fold"),
                                 "**实验对照模块**（native_decide 对照，不进主结论；"
                                 "axioms 含 Lean.ofReduceBool 属预期）")
        path = os.path.join(out_dir, f"{ns}.lean")
        with open(path, "w") as f:
            f.write(text)
        print(f"wrote {path} ({len(first)} leaves, native_decide)")
    if do_ladder:
        for mode in ("then", "else"):
            L = next((x for x in comp if x["mode"] == mode), None)
            if L is None:
                continue
            for li, layers in enumerate((("cert",), ("cert", "der"),
                                         ("cert", "der", "face", "fold"))):
                ns = f"{base}Ladder{mode.capitalize()}{li+1}"
                text = shard_module_text(ns, n, expr, [L], j, gran, ndiv,
                                         ntrans, "decide", layers,
                                         f"三层阶梯 L{li+1}（叶 {L['idx']}，"
                                         f"{mode} 支；层集 {sorted(layers)}）",
                                         cert_route=cert_route)
                path = os.path.join(out_dir, f"{ns}.lean")
                with open(path, "w") as f:
                    f.write(text)
                print(f"wrote {path}")
    with open(os.path.join(out_dir, f"{name}.emitstats.json"), "w") as f:
        json.dump(stats, f, indent=1)


def main():
    args = sys.argv[1:]
    if not args:
        die(__doc__)
    cmd = args[0]
    opts = {}
    for a in args[1:]:
        if a.startswith("--"):
            mm = re.match(r"--([\w-]+)=(.*)", a)
            if mm:
                opts[mm.group(1).replace("-", "_")] = mm.group(2)
    flags = {a[2:] for a in args[1:] if a.startswith("--") and "=" not in a}
    pos = [a for a in args[1:] if not a.startswith("--")]
    if cmd == "census":
        cmd_census(pos[0], int(opts.get("j", 2)))
    elif cmd == "pilot2":
        cmd_pilot2(pos[0], pos[1], int(opts.get("j", 2)), int(opts.get("k", 3)),
                   int(opts.get("gran", -80)), int(opts.get("rung", 128)),
                   int(opts.get("rung_out", -80)),
                   opts.get("out", "pipeline/interval/out/p549hull/C549Mono2Gen.lean"),
                   opts.get("dir", "lo"), opts.get("mode", "then"))
    elif cmd == "boxes":
        cmd_boxes(pos[0], pos[1], int(opts.get("j", 2)), int(opts.get("k", 220)),
                  int(opts.get("stride", 0)), int(opts.get("skip", 0)),
                  int(opts.get("want_else", 8)), int(opts.get("extra_cap", 6000)),
                  opts.get("out", "/tmp/opencode/mv/census549.jsonl"),
                  int(opts.get("rung", 128)), int(opts.get("rung_out", -80)))
    elif cmd == "probe":
        cmd_probe(pos[0], pos[1], pos[2], opts.get("der"),
                  int(opts.get("from", 0)), int(opts.get("to", 10**9)),
                  int(opts.get("gran", -80)), int(opts.get("rung", 128)),
                  int(opts.get("rung_out", -80)),
                  opts["out"] if "out" in opts else die("probe needs --out"),
                  opts.get("tag", ""), opts.get("route", "tm"))
    elif cmd == "emit":
        cmd_emit(pos[0], pos[1], opts["der"], opts.get("face"), opts.get("cert"),
                 opts.get("full"), opts.get("out_dir", "lean/Kepler/Interval/Cases"),
                 int(opts.get("shard", 20)), opts.get("name", "Shard"),
                 "baseline" in flags, ("native_ctl" in flags or "native-ctl" in flags), "ladder" in flags,
                 int(opts.get("gran", -80)), int(opts.get("rung", 128)),
                 int(opts.get("rung_out", -80)), opts.get("cert_route", "tm"),
                 opts.get("ns_prefix"))
    else:
        die(f"unknown cmd {cmd}")


if __name__ == "__main__":
    main()

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

用法：在 pipeline/interval/ 下 `python3 emit_mono.py ...`；
stage-A 运行在 lean/ 包根下 `lake env lean --run`。
"""
import json
import os
import re
import subprocess
import sys

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


def main():
    args = sys.argv[1:]
    if not args:
        die(__doc__)
    cmd = args[0]
    opts = dict(re.match(r"--(\w+)=(.*)", a).groups() for a in args[1:] if a.startswith("--"))
    pos = [a for a in args[1:] if not a.startswith("--")]
    if cmd == "census":
        cmd_census(pos[0], int(opts.get("j", 2)))
    elif cmd == "pilot2":
        cmd_pilot2(pos[0], pos[1], int(opts.get("j", 2)), int(opts.get("k", 3)),
                   int(opts.get("gran", -80)), int(opts.get("rung", 128)),
                   int(opts.get("rung-out", -80)),
                   opts.get("out", "pipeline/interval/out/p549hull/C549Mono2Gen.lean"),
                   opts.get("dir", "lo"), opts.get("mode", "then"))
    else:
        die(f"unknown cmd {cmd}")


if __name__ == "__main__":
    main()

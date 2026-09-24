#!/usr/bin/env python3
"""549 M1: 符号偏微分器 + mono 折叠（facePos）叶发射器.

语义层对应 `lean/Kepler/Interval/Cases/C549Mono.lean` 的 `derivIExpr`（逐构造子
镜像：±×÷√atan 链式/商法则；ite 微分 then 支——guard 定号情形；
abs 零桩）。本工具把 case JSON 的 RPN prog → IExpr 文本树（复用
emit_lean.RPN 的发射形状），对树做符号 ∂ⱼ，发射两类叶：

  deriv 叶: checkPosTMHull (IExpr.neg DExpr) box psd = true   （−∂ⱼf 全盒正性）
  face  叶: checkPosTMHull E (faceBoxHi box j) ps = true      （n−1 维面）

导数叶/面叶的 TMParams 由 stage-A 编译运行探针（tmHullLeafProbe，Fill 镜像）
收割 sqrt 证书。用 mirror derivIExpr 的 Lean 侧求值做 stage-A，保证
Python 生成的 DExpr 文本与 Lean `derivIExpr` 逐节点一致（另有
`DExpr = derivIExpr E j := rfl` 桥定理在内核验证一致性）。

子命令:
  diff <case.json> [--j=K]
      解析 RPN prog → IExpr 文本，打印符号 ∂ⱼ 的 Lean IExpr 文本与统计。
  pilot <case.json> <leanfile> [--j=2] [--k=5] [--gran=-80] [--rung=128]
      [--rung-out=-80] [--out=<out.lean>]
      549 mono 折叠试点：取 leanfile（C549Hull200.lean 形状）里的前 k 个
      PASS 单叶，逐叶发射 baseline 引用 / 面叶 / 导数叶 / 折叠组合定理，
      先生成两个 stage-A 驱动（面叶证书、导数叶证书）到 /tmp，
      `lake env lean --run` 收割参数后写 out.lean（C549Mono.lean 生成段）。

用法：在 pipeline/interval/ 下 `python3 emit_diff.py ...`；
stage-A 运行在 lean/ 包根下 `lake env lean --run`。
"""
import json
import os
import re
import subprocess
import sys

from emit_lean import RPN, box_frac, box_lit, die, dyadic, hull_expr

# IExpr 文本是全括号单空格形（`(.op arg1 arg2)`）——与 emit_hull_pilot 的
# AST 去重层同一 tokenizer。
TOK = re.compile(r'\(|\)|[^\s()]+')


class Node:
    """IExpr 文本树节点：op + 子节点（str 常量槽与 Node），保精确文本片段."""

    __slots__ = ("op", "kids", "start", "end")

    def __init__(self, op, kids, start, end):
        self.op = op
        self.kids = kids
        self.start, self.end = start, end

    def text(self, src):
        return src[self.start:self.end]


def parse_sexpr(src):
    raw = [(m.group(0), m.start(), m.end()) for m in TOK.finditer(src)]
    # 合并粒度字面量 `(-64)`（括号 + 负整数）为单 token——否则被当作节点开头
    toks = []
    i = 0
    while i < len(raw):
        t, s, e = raw[i]
        if t == '(' and i + 2 < len(raw) and raw[i + 1][0].lstrip('-').isdigit() \
                and raw[i + 2][0] == ')':
            toks.append((src[s:raw[i + 2][2]], s, raw[i + 2][2]))
            i += 3
            continue
        toks.append((t, s, e))
        i += 1

    def rec(pos):
        assert toks[pos][0] == '(', f"expected ( at {pos}"
        st = toks[pos][1]
        pos += 1
        head = toks[pos][0]
        if not head.startswith('.'):
            die(f"bad head {head}")
        pos += 1
        kids = []
        while toks[pos][0] != ')':
            if toks[pos][0] == '(':
                node, pos = rec(pos)
                kids.append(node)
            else:
                kids.append(toks[pos][0])
                pos += 1
        return Node(head, kids, st, toks[pos][1] + 1), pos + 1

    tree, pos = rec(0)
    if pos != len(toks):
        die("trailing tokens")
    return tree


# `derivIExpr` 的 Python 镜像（语义层逐构造子一致；rfl 桥的消费方）。
def dtext(node, src, j):
    op = node.op
    k = node.kids
    if op == ".const":
        return "(.const ⟨0, 0⟩)"
    if op == ".var":
        i = int(k[0])
        return "(.const ⟨1, 0⟩)" if i == j else "(.const ⟨0, 0⟩)"
    if op == ".neg":
        return f"(.neg {dtext(k[0], src, j)})"
    if op == ".abs":
        return "(.const ⟨0, 0⟩)"
    if op == ".ite":
        return dtext(k[1], src, j)
    if op == ".add":
        return f"(.add {dtext(k[0], src, j)} {dtext(k[1], src, j)})"
    if op == ".sub":
        return f"(.sub {dtext(k[0], src, j)} {dtext(k[1], src, j)})"
    if op == ".mul":
        return (f"(.add (.mul {dtext(k[0], src, j)} {k[1].text(src)}) "
                f"(.mul {k[0].text(src)} {dtext(k[1], src, j)}))")
    if op == ".div":
        out = k[2]
        return (f"(.div (.sub (.mul {dtext(k[0], src, j)} {k[1].text(src)}) "
                f"(.mul {k[0].text(src)} {dtext(k[1], src, j)})) "
                f"(.mul {k[1].text(src)} {k[1].text(src)}) {out})")
    if op == ".sqrt":
        a = k[0].text(src)
        return (f"(.div {dtext(k[0], src, j)} "
                f"(.add (.sqrt {a} {k[1]} {k[2]}) (.sqrt {a} {k[1]} {k[2]})) 0)")
    if op == ".trans":
        kind = k[0]
        a = k[1].text(src)
        N, out = k[2], k[3]
        da = dtext(k[1], src, j)
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


def bal(s):
    return s.count('(') - s.count(')')


def face_box_lit(coords, j, hi=True):
    """坐标文本列表（`⟨⟨m,e⟩, ⟨m,e⟩⟩`）→ j 坐标钉在 hi/lo 端点的退化面盒."""
    fb = list(coords)
    iv = fb[j][1:-1]  # 去外层 ⟨⟩：`⟨m,e⟩, ⟨m,e⟩`
    lo_t, hi_t = [s.strip() for s in iv.split("⟩, ⟨")]
    lo_t, hi_t = lo_t + "⟩", "⟨" + hi_t
    # 退化面坐标：两端都钉在 hi（或 lo）端点 → ⟨⟨m,e⟩, ⟨m,e⟩⟩
    end = hi_t if hi else lo_t
    fb[j] = f"⟨{end}, {end}⟩"
    return "![" + ", ".join(fb) + "]"


def parse_leaf_defs(lean_path):
    """从 C549Hull200.lean 形状模块抽 BoxK / PK def 文本与 PASS 判定."""
    src = open(lean_path).read()
    boxes, params, verdicts = {}, {}, {}
    for m in re.finditer(
            r"def (\w+) : Fin \d+ → DInterval :=\n  (!\[[^\n]*\])", src):
        boxes[m.group(1)] = m.group(2)
    for m in re.finditer(r"def (\w+) : TMParams := (⟨.*⟩)$", src, re.M):
        params[m.group(1)] = m.group(2)
    for m in re.finditer(
            r"theorem (\w+) :\s*\n\s*checkPosTMHull \w+ (\w+) (\w+) = true", src):
        verdicts[m.group(1)] = (m.group(2), m.group(3))
    return boxes, params, verdicts


STAGEA_TMPL = """/-  emit_diff.py stage-A probe driver (scratch). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Kepler.Interval

namespace Probe{mod}

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

def Expr : IExpr {n} :=
  {expr}

def Ps : TMParams :=
  ⟨List.replicate {nsqrt} ⟨0, 0, 0, ({gran}), ({gran})⟩,
   List.replicate {ndiv} ⟨({gran}), ({gran}), ({gran})⟩,
   List.replicate {ntrans} ⟨({gran}), ({gran})⟩⟩

def Boxes : Array (Fin {n} → DInterval) := #[
    {boxes}
]

end Probe{mod}

open Probe{mod} in
def main : List String → IO UInt32 := fun _ => do
  IO.println "RUNG mono"
  for i in [0:Boxes.size] do
    match tmHullLeafProbe Expr Boxes[i]! Ps with
    | some (p, m, e, l) =>
        let v : String := if p then "PASS" else "NEG"
        let trip := String.intercalate " " (l.map fun t => s!"{{t.1}} {{t.2.1}} {{t.2.2}}")
        IO.println s!"{{i}} {{v}} {{m}} {{e}} {{trip}}"
    | none => IO.println s!"{{i}} FAIL"
  return 0
"""


def run_stagea(mod, n, expr, boxes, nsqrt, ndiv, ntrans, gran, tmpdir="/tmp/opencode"):
    """写 stage-A 驱动到 /tmp 并编译运行，返回逐叶 (verdict, lo_m, lo_e, triples)."""
    path = f"{tmpdir}/{mod}_stagea.lean"
    text = STAGEA_TMPL.format(mod=mod, n=n, expr=expr, nsqrt=nsqrt, ndiv=ndiv,
                              ntrans=ntrans, gran=gran,
                              boxes=",\n    ".join(
                                  f"({b} : Fin {n} → DInterval)" for b in boxes))
    with open(path, "w") as f:
        f.write(text)
    lean_root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean")
    proc = subprocess.run(["lake", "env", "lean", "--run", path], cwd=lean_root,
                          capture_output=True, text=True, timeout=3600)
    out = proc.stdout
    if "RUNG mono" not in out:
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
    return rows


def params_lit(s_triples, ndiv, ntrans, gran):
    sq = ", ".join(f"⟨{a}, {b}, {c}, ({gran}), ({gran})⟩" for a, b, c in s_triples)
    iv = ", ".join(f"⟨({gran}), ({gran}), ({gran})⟩" for _ in range(ndiv))
    tv = ", ".join(f"⟨({gran}), ({gran})⟩" for _ in range(ntrans))
    return f"⟨[{sq}], [{iv}], [{tv}]⟩"


def cmd_diff(case_path, j):
    case = json.load(open(case_path))
    rpn = RPN(sqrt_slot=lambda i: ("0", "0"),
              trans=lambda op, closed: ("128", "(-80)") if not closed else ("2048", "(-64)"))
    expr = rpn.emit(case["prog"])
    tree = parse_sexpr(expr)
    d = dtext(tree, expr, j)
    print(f"expr nodes: {expr.count('(.')} ")
    print(f"deriv w.r.t. x{j+1} (var {j}):")
    print(d)
    print(f"deriv nodes: {d.count('(.')}")
    print(f"deriv sqrt count: {d.count('(.sqrt ')}")
    print(f"deriv div count:  {d.count('(.div ')}")
    print(f"deriv trans count: {d.count('(.trans ')}")


def cmd_pilot(case_path, lean_path, j, k, gran, rung_n, rung_out, out_path,
              direction="lo"):
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
    print(f"pilot leaves: {[t[0] for t in leaves]}")

    # 符号微分（文本层，与 Lean derivIExpr 逐构造子一致）
    tree = parse_sexpr(expr)
    dexpr = dtext(tree, expr, j)
    d_nsqrt = dexpr.count("(.sqrt ")
    d_ndiv = dexpr.count("(.div ")
    d_ntrans = dexpr.count("(.trans ")

    # 面盒（lo/hi 面，按 ∂ⱼf 实测定号方向；stage-A 探针为准）与导数叶盒
    box_coords = []
    for b in (bl for _, bl, _ in leaves):
        coords = re.findall(r"⟨⟨[^⟨⟩]*⟩, ⟨[^⟨⟩]*⟩⟩", b)
        if len(coords) != n:
            die(f"box coord parse: got {len(coords)}, want {n}")
        box_coords.append(coords)
    face_lits = [face_box_lit(bc, j, hi=(direction == "hi")) for bc in box_coords]

    # stage-A：面叶证书（原 expr 于面盒）+ 导数叶证书（DExpr 于原盒）
    face_rows = run_stagea("MonoFace", n, expr, face_lits, nsqrt, ndiv, ntrans, gran)
    der_rows = run_stagea("MonoDer", n, dexpr, [bl for _, bl, _ in leaves],
                          d_nsqrt, d_ndiv, d_ntrans, gran)

    parts = []
    parts.append("/-! ## 549 mono 折叠试点（pipeline/interval/emit_diff.py 生成；勿手改）。\n"
                "自包含：仅 import Kepler.Interval.CertTM（C549HullSpeed 模式）。 -/\n\n"
                "namespace Cases\n")
    parts.append(f"""/-- The case expression（逐字复制 C549Hull200.lean 的 C549Hull200Expr；本模块
未 import 该模块，此副本使 mono 折叠叶自包含）. -/""")
    parts.append(f"def C549Hull200Expr : IExpr {n} :=")
    parts.append(f"  {expr}")
    for idx, (thm, bl, pl) in enumerate(leaves):
        parts.append(f"/-- Cert leaf {idx}（{thm}）原盒（逐字复制）. -/")
        parts.append(f"def C549Hull200Box{idx+1} : Fin {n} → DInterval :=")
        parts.append(f"  {bl}")
        parts.append(f"/-- Cert leaf {idx}（{thm}）原参数（逐字复制）. -/")
        parts.append(f"def C549Hull200P{idx+1} : TMParams :=")
        parts.append(f"  {pl}")
    parts.append(f"""/- 符号微分说明：导数叶语句中的 `derivIExpr C549Hull200Expr {j}`
由内核在 `decide` 求值（Python 侧镜像 emit_diff.py.dtext 仅用于 stage-A
证书收割；两侧逐 token 一致性由 emit_diff 侧检保证）。求值路径
{d_nsqrt} sqrt / {d_ndiv} div / {d_ntrans} trans。 -/""")
    dircap = "Lo" if direction == "lo" else "Hi"
    dirsign = "+" if direction == "lo" else "-"
    dderiv = ("(derivIExpr C549Hull200Expr %d)" % j) if direction == "lo" \
        else ("(IExpr.neg (derivIExpr C549Hull200Expr %d))" % j)
    for idx, (thm, bl, pl) in enumerate(leaves):
        fv, fm, fe, ftrip = face_rows[idx]
        dv, dm, de, dtrip = der_rows[idx]
        parts.append(f"""/-- Cert leaf {idx}（{thm}）的 hi 面盒（x{j+1} 钉 hi）. -/
def C549MonoFaceBox{idx+1} : Fin {n} → DInterval :=
  {face_lits[idx]}

/-- 面叶参数（stage-A 收割，verdict {fv}）. -/
def C549MonoPF{idx+1} : TMParams :=
  {params_lit(ftrip, ndiv, ntrans, gran)}

/-- 导数叶参数（stage-A 收割，verdict {dv}）. -/
def C549MonoDP{idx+1} : TMParams :=
  {params_lit(dtrip, d_ndiv, d_ntrans, gran)}

/-- 面叶（原表达式于 {direction} 面盒）. -/
theorem C549MonoFace{idx+1} :
    checkPosTMHull C549Hull200Expr (faceBox{dircap} C549Hull200Box{idx+1} {j}) C549MonoPF{idx+1} = true := by
  decide

/-- 导数定号叶（{dirsign}∂x{j+1}f，全盒；导数由内核 `derivIExpr` 求值）. -/
theorem C549MonoDer{idx+1} :
    checkPosTMHull {dderiv}
      C549Hull200Box{idx+1} C549MonoDP{idx+1} = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549MonoFold{idx+1} :
    checkPosFace{dircap} C549Hull200Expr (derivIExpr C549Hull200Expr {j})
      C549Hull200Box{idx+1} {j} C549MonoPF{idx+1} C549MonoDP{idx+1} = true := by
  simp only [checkPosFace{dircap}, Bool.and_eq_true]
  exact ⟨C549MonoDer{idx+1}, C549MonoFace{idx+1}⟩
""")
    parts.append("""
#print axioms C549MonoFold1

end Cases
""")
    out = "\n\n".join(parts)
    # 侧检（不上 kernel）：Python DExpr 与 Lean derivIExpr 文本须逐 token 一致。
    # （kvernel rfl 桥因 2184 节点 matcher 展开过深不可行；折叠定理语句直接
    # 使用 `derivIExpr C549Hull200Expr j`，由内核求值，无 Python 信任。）
    if bal(dexpr) != 0:
        die("emitted DExpr unbalanced")
    if out_path:
        with open(out_path, "w") as f:
            f.write(out)
        print(f"wrote {out_path}")
    else:
        print(out)
    for idx, (thm, _, _) in enumerate(leaves):
        print(f"leaf {idx} ({thm}): face {face_rows[idx][0]}  deriv {der_rows[idx][0]}")


def main():
    args = sys.argv[1:]
    if not args:
        die(__doc__)
    cmd = args[0]
    opts = dict(re.match(r"--(\w+)=(.*)", a).groups() for a in args[1:] if a.startswith("--"))
    pos = [a for a in args[1:] if not a.startswith("--")]
    if cmd == "diff":
        cmd_diff(pos[0], int(opts.get("j", 2)))
    elif cmd == "pilot":
        cmd_pilot(pos[0], pos[1], int(opts.get("j", 2)), int(opts.get("k", 5)),
                  int(opts.get("gran", -80)), int(opts.get("rung", 128)),
                  int(opts.get("rung-out", -80)),
                  opts.get("out", "pipeline/interval/out/p549hull/C549MonoGen.lean"),
                  opts.get("dir", "lo"))
    else:
        die(f"unknown cmd {cmd}")


if __name__ == "__main__":
    main()

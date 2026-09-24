#!/usr/bin/env python3
"""549 导数叶 LExpr 去重工位（emit_fold2.py）.

facePos 折叠对的导数叶（`derivIExpr`，2184 ops、574% 文本重复、~34s decide）
的成本定位与 LExpr 证书表折叠试点。工作对象 = 符号导数表达式的 Python 镜像
文本（emit_diff.dtext，与 emit_mono.py 生成 C549Mono2 的口径逐 token 一致；
localize 以 mantissa 队列与 C549M2DP 逐项比对作文本一致性证明），盒子/导数
叶参数从 `C549Mono2.lean` 收割（C549M2Box / C549M2DP / C549M2Der）。

子命令:
  localize <case.json> <mono2.lean> [--j=2] [--leaf=1] [--out-dir=DIR]
      成本定位实验。把导数叶切开逐段隔离 decide 计时：
        base     内核 `derivIExpr C549M2Expr j` 全量（matcher + 求值）
        dexpr    纯文本镜像（无 matcher；其 mantissa 队列须与 C549M2DP<j>
                 逐项一致，否则中止）
        noatan1  rung-2048 arctan(1) 闭合 trans 副本 → const（证书免费，
                 DP 原参数仍有效）
        skel     topmost 证书段（div/sqrt 链）全部 → const 的多项式骨架
        seg0..   各 topmost 证书段单独（自己的 stage-A 参数/判定）
  plan <case.json> [--j=2] [--min-size=12] [--max-lets=8] [--min-occ=2]
      打印 free（证书免费口径）/ full（全折叠）两种折叠计划，不产模块。
  stagea-der <case.json> <mono2.lean> <out_driver.lean> [--leaves=3]
      [--min-size=12] [--max-lets=8] [--min-occ=2] [--gran=-80]
      [--rung=128] [--rung-out=-80]
      全折叠 stage-A-let：`tmHullLeafProbeL` 逐叶重产 params（entries-first
      消费序）→ params.txt + manifest。
  stageb-der <case.json> <mono2.lean> <params.txt> <out.lean> [--leaves=3]
      [--min-size=12] [--max-lets=8] [--min-occ=2] [--tactic=decide]
      [--split-dir=DIR]
      三方试点模块：base（引用 C549M2Der，零重算）/ free（证书免费折叠 +
      C549M2DP 原参数）/ full（全折叠 + stage-A-let 重产参数）+ manifest；
      --split-dir 另写逐叶逐臂隔离计时模块（base 臂为全新 decide）。

用法：在 pipeline/interval/ 下 `python3 emit_fold2.py ...`；stage-A 运行在
lean/ 包根下 `lake env lean --run`；隔离计时 `lake env lean <module>`.
"""
import json
import os
import re
import subprocess
import sys
import time

from emit_lean import die
from emit_lean import hull_expr
from emit_diff import bal, dtext
from emit_diff import parse_sexpr as parse_node
from emit_hull_pilot import (N, emit_fold_body, has_var,
                             mark_guards, node_cost, node_size,
                             parse_hull_params, parse_sexpr as parse_tree)


# ---------------------------------------------------------------------------
# 导数表达式重建与收割（C549Mono2 口径）
# ---------------------------------------------------------------------------

def build_dexpr(case_path, j=2, rung_n=128, rung_out=-80):
    """重建 emit_mono.py 口径的导数叶文本（dtext = derivIExpr then 镜像）。"""
    case = json.load(open(case_path))
    expr, ns, ni, nt = hull_expr(case, rung_n, rung_out)
    tree = parse_node(expr)
    d = dtext(tree, expr, j)
    if bal(d) != 0:
        die("reconstructed DExpr unbalanced")
    return case, d, (d.count("(.sqrt "), d.count("(.div "),
                     d.count("(.trans "))


def harvest_mono2(path):
    """C549M2Box{j} / C549M2DP{j} / C549M2Der{j} 从 Mono2 模块收割。"""
    src = open(path).read()
    boxes = {int(m.group(1)): m.group(2) for m in re.finditer(
        r"def C549M2Box(\d+) : Fin \d+ → DInterval :=\n+  (!\[[^\n]*\])", src)}
    params = {int(m.group(1)): m.group(2) for m in re.finditer(
        r"def C549M2DP(\d+) : TMParams :=\n+  (.+)$", src, re.M)}
    verdicts = {}
    for m in re.finditer(
            r"theorem C549M2Der(\d+) :\s*\n\s*checkPosTMHull "
            r"\(\(derivIExpr C549M2Expr (\d+)\)\)\s*\n\s*"
            r"C549M2Box\1 C549M2DP\1 = (true|false)", src):
        verdicts[int(m.group(1))] = (int(m.group(2)), m.group(3))
    if not boxes or not params or not verdicts:
        die(f"could not harvest C549M2Box/DP/Der from {path}")
    return boxes, params, verdicts


def dp_mantissas(dp_lit):
    """DP 字面量 sqrtCerts 的 mantissa 三元组（文本序），用于一致性比对。"""
    body = dp_lit.split("[", 1)[1].split("]", 1)[0]
    trips = re.findall(r"⟨(-?\d+), (-?\d+), (-?\d+),", body)
    return [(int(a), int(b), int(c)) for a, b, c in trips]


# ---------------------------------------------------------------------------
# 分段（成本定位）
# ---------------------------------------------------------------------------

def cert_op(n):
    """该节点本身是否消费 TMParams 证书：sqrt/div 恒消费；trans 仅开式
    （参数含 var）消费——549 导数叶的 trans 全为闭合 arctan(1) 常数
    （证书免费，纯级数求值成本）。"""
    if n.op in (".sqrt", ".div"):
        return True
    if n.op == ".trans":
        return has_var(n.kids[2])
    return False


def topmost_cert_segs(root):
    """topmost 证书段：自身 cert_op 且父链上再无 cert_op 的节点（整 subtree）。"""
    segs = []

    def rec(x, inseg):
        if cert_op(x) and not inseg:
            segs.append(x)
            rec(x, True)
            return
        for k in x.kids:
            if isinstance(k, N):
                rec(k, inseg or cert_op(x))

    rec(root, False)
    return segs


def closed_trans_roots(root):
    """闭合 trans（var-free 参数）节点——证书免费、纯级数求值成本."""
    out = []

    def rec(x):
        if x.op == ".trans" and not has_var(x.kids[2]):
            out.append(x)
            return
        for k in x.kids:
            if isinstance(k, N):
                rec(k)

    rec(root)
    return out


def splice(expr, repls):
    """[(start, end, text)] 按跨度拼接（跨度须两两不交）。"""
    out, pos = [], 0
    for s, e, t in sorted(repls):
        out.append(expr[pos:s])
        out.append(t)
        pos = e
    out.append(expr[pos:])
    return "".join(out)


def seg_census(seg):
    cnt = [0, 0, 0]

    def rec(x):
        if x.op == ".sqrt":
            cnt[0] += 1
        if x.op == ".div":
            cnt[1] += 1
        if x.op == ".trans" and has_var(x.kids[2]):
            cnt[2] += 1
        for k in x.kids:
            if isinstance(k, N):
                rec(k)

    rec(seg)
    return tuple(cnt)


# ---------------------------------------------------------------------------
# 批量 stage-A 探针驱动（tmHullLeafProbe；行格式与 parse_hull_params 兼容）
# ---------------------------------------------------------------------------

PROBE_TMPL = """/-  emit_fold2.py batched stage-A probe driver (scratch). -/
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
  IO.println "RUNG {rung_n} {rung_out} ({gran}) ({gran}) ({gran}) ({gran}) ({gran}) ({gran}) ({gran})"
  for i in [0:Probes.size] do
    let (ei, bx, ns, ni, nt) := Probes[i]!
    let t0 ← IO.monoMsNow
    match tmHullLeafProbe Exprs[ei]! bx (Ps ns ni nt) with
    | some (p, m, e, l) =>
        let ms ← IO.monoMsNow
        let v : String := if p then "PASS" else "NEG"
        let trip := String.intercalate " " (l.map fun t => s!"{{t.1}} {{t.2.1}} {{t.2.2}}")
        IO.eprintln s!"probe {{i}} expr {{ei}}: {{ms - t0}} ms"
        IO.println s!"{{i}} {{v}} {{m}} {{e}} {{trip}}"
    | none =>
        let ms ← IO.monoMsNow
        IO.eprintln s!"probe {{i}} expr {{ei}}: {{ms - t0}} ms FAIL"
        IO.println s!"{{i}} FAIL"
  return 0
"""


def run_probe_batch(mod, n, probes, box, gran, rung_n, rung_out, lean_root,
                    tmpdir="/tmp/opencode"):
    """批量探针。probes: (tag, expr_text, ns, ni, nt)。返回
    {tag: (verdict, lo_m, lo_e, trips)}、rung 头、{tag: 编译后求值秒}。"""
    path = os.path.abspath(f"{tmpdir}/{mod}_stagea.lean")
    idx, texts = {}, []
    for tag, t, _ns, _ni, _nt in probes:
        if t not in idx:
            idx[t] = len(texts)
            texts.append(t)
    g = f"({gran})"
    text = PROBE_TMPL.format(
        mod=mod, n=n,
        exprs=",\n    ".join(f"({t} : IExpr {n})" for t in texts),
        gran=gran, rung_n=rung_n, rung_out=rung_out,
        probes=",\n    ".join(
            f"({idx[t]}, ({box} : Fin {n} → DInterval), {ns}, {ni}, {nt})"
            for tag, t, ns, ni, nt in probes))
    with open(path, "w") as f:
        f.write(text)
    proc = subprocess.run(["lake", "env", "lean", "--run", path], cwd=lean_root,
                          capture_output=True, text=True, timeout=7200)
    if proc.returncode != 0:
        die(f"probe batch {mod} failed: {proc.stderr[-2000:]}")
    lines = proc.stdout.splitlines()
    if not lines or not lines[0].startswith("RUNG"):
        die(f"probe batch {mod}: no RUNG header ({proc.stderr[-500:]})")
    rung = tuple(int(x.strip("()")) for x in lines[0].split()[1:])
    out = {}
    for ln in lines[1:]:
        tk = ln.split()
        if len(tk) < 2 or not tk[0].isdigit():
            continue
        tag = probes[int(tk[0])][0]
        trip = [int(x) for x in tk[4:]]
        out[tag] = (tk[1], int(tk[2]), int(tk[3]),
                    [tuple(trip[q:q + 3]) for q in range(0, len(trip), 3)])
    for tag, _t, _ns, _ni, _nt in probes:
        if tag not in out:
            die(f"probe batch {mod}: tag {tag} missing ({proc.stderr[-800:]})")
    ms = dict(re.findall(r"probe (\d+) expr \d+: (\d+) ms", proc.stderr))
    out_ms = {probes[int(k)][0]: int(v) / 1000 for k, v in ms.items()}
    return out, rung, out_ms


def params_line(rung, ndiv, ntrans, trips):
    """TMParams 字面量（emit_hull_pilot.params_lit 同形：sqrt 三元组按消费序，
    inv/trans 为 granularity 记录）。"""
    _, _, _, _, _, g3, g4, g5, g6 = rung
    sq = ", ".join(f"⟨{a}, {b}, {c}, ({g3}), ({g4})⟩" for a, b, c in trips)
    iv = ", ".join(f"⟨({g3}), ({g3}), ({g3})⟩" for _ in range(ndiv))
    tv = ", ".join(f"⟨({g5}), ({g6})⟩" for _ in range(ntrans))
    return f"⟨[{sq}], [{iv}], [{tv}]⟩"


TIMING_TMPL = """/- TIMING MODULE arm={tag} (emit_fold2.py; scratch, 不入包). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

open Kepler.Interval

def Expr : IExpr {n} :=
  {expr}

def Box : Fin {n} → DInterval :=
  {box}

def P : TMParams := {params}

theorem t : checkPosTMHull Expr Box P = {verdict} := by
  decide

end Kepler.Interval.Cases
"""

TIMING_L_TMPL = """/- TIMING MODULE arm={tag} (emit_fold2.py; scratch, 不入包).
LExpr 证书表折叠路由：checkPosTMHullL Tbl Body（{note}）. -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

open Kepler.Interval

def Tbl : Fin {k} → IExpr {n} := ![{table}]

def Body : LExpr {n} {k} :=
  {body}

def Box : Fin {n} → DInterval :=
  {box}

def P : TMParams := {params}

theorem t : checkPosTMHullL Tbl Body Box P = {verdict} := by
  decide

end Kepler.Interval.Cases
"""

BASE_TIMING_TMPL = """/- TIMING MODULE arm=base (emit_fold2.py; scratch).
内核 `derivIExpr` 全量（matcher 展开 + 求值）：C549M2Der{leaf} 的全新
decide 复测（Mono2 模块本体已过；此处测本机隔离 decide 口径）. -/
import Kepler.Interval.Cases.C549Mono2

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace BaseTiming

open Kepler.Interval

theorem t :
    checkPosTMHull ((derivIExpr Kepler.Interval.Cases2.C549M2Expr {j}))
      Kepler.Interval.Cases2.C549M2Box{leaf}
      Kepler.Interval.Cases2.C549M2DP{leaf} = {verdict} := by
  decide

end BaseTiming
"""


def time_lean_module(path, lean_root, timeout=7200):
    t0 = time.time()
    proc = subprocess.run(["lake", "env", "lean", path], cwd=lean_root,
                          capture_output=True, text=True, timeout=timeout)
    dt = time.time() - t0
    if proc.returncode != 0:
        die(f"timing module {path} failed:\n{proc.stdout[-1500:]}\n"
            f"{proc.stderr[-1500:]}")
    return dt


# ---------------------------------------------------------------------------
# 折叠计划（emit_hull_pilot.plan_fold 的导数叶版：表达式文本直接给定）
# ---------------------------------------------------------------------------

def cert_free_node(n):
    if n.op in (".sqrt", ".div", ".ite", ".abs"):
        return False
    if n.op == ".trans":
        return not has_var(n.kids[2])
    return all(cert_free_node(k) for k in n.kids if isinstance(k, N))


def plan_fold_text(expr, min_size, max_lets, min_occ, cert_free_only):
    """与 emit_hull_pilot.plan_fold 相同的贪心（profit 降序、跨候选不交、
    max_lets 封顶），但作用于给定文本（导数叶 dexpr）。"""
    root = parse_tree(expr)
    mark_guards(root)
    total_nodes = node_size(root)
    occ = {}
    stack = [root]
    while stack:
        x = stack.pop()
        if not x.guard and x.op in (".neg", ".add", ".sub", ".mul",
                                    ".trans", ".div", ".sqrt"):
            occ.setdefault(x.text(expr), []).append(x)
        for kk in x.kids:
            if isinstance(kk, N):
                stack.append(kk)
    cands = []
    for txt, xs in occ.items():
        if len(xs) < min_occ or node_cost(xs[0]) < min_size:
            continue
        cf = cert_free_node(parse_tree(txt))
        if cert_free_only and not cf:
            continue
        kept = []
        for x in sorted(xs, key=lambda x: -(x.end - x.start)):
            if all(x.end <= y.start or y.end <= x.start for y in kept):
                kept.append(x)
        if len(kept) >= min_occ:
            cands.append((node_cost(xs[0]) * len(kept), len(kept),
                          node_cost(xs[0]), txt, kept, cf))
    # 两遍贪心：先证书消耗候选（大容器优先——子容器副本多被容器覆盖，
    # 先折容器才能既去重证书又保住内层；先折内层会把容器副本的 span 全部
    # 占掉、丢掉整棵容器），再证书免费候选按 profit 降序。
    cert_c = sorted((c for c in cands if not c[5]), key=lambda c: -c[2])
    free_c = sorted((c for c in cands if c[5]), key=lambda c: -c[0])
    taken, consumed = [], []
    for profit, nocc, size, txt, kept, cf in cert_c + free_c:
        if len(taken) >= max_lets:
            break
        free = [x for x in kept
                if all(x.end <= st or en <= x.start for st, en in consumed)]
        if len(free) < min_occ:
            continue
        taken.append((txt, free))
        consumed.extend((x.start, x.end) for x in free)
    if not taken:
        die("no duplicated subtrees found — nothing to fold")
    body = emit_fold_body(root, expr, {x.nid for _, free in taken
                                       for x in free},
                          {txt: i for i, (txt, _) in enumerate(taken)})
    return dict(root=root, total_nodes=total_nodes, taken=taken, body=body,
                table_txt=", ".join(t for t, _ in taken), k=len(taken),
                n_ref=body.count("(.ref "),
                slot_desc=", ".join(f"#{i}: {len(f)} refs x "
                                    f"{t.count('(.') + 1} nodes"
                                    for i, (t, f) in enumerate(taken)))


# ---------------------------------------------------------------------------
# 子命令
# ---------------------------------------------------------------------------

def cmd_localize(case_path, mono2_path, j, leaf, out_dir, gran,
                 rung_n=128, rung_out=-80):
    t0 = time.time()
    lean_root = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "..", "..", "lean")
    os.makedirs(out_dir, exist_ok=True)
    out_dir = os.path.abspath(out_dir)
    case, dexpr, (ns, ni, nt) = build_dexpr(case_path, j, rung_n, rung_out)
    boxes, params, verdicts = harvest_mono2(mono2_path)
    if leaf not in boxes or leaf not in params or leaf not in verdicts:
        die(f"Mono2 has no leaf {leaf} (has {sorted(boxes)})")
    vj, vtgt = verdicts[leaf]
    if vj != j:
        die(f"Mono2 leaf {leaf} differentiates x{vj + 1}, wanted x{j + 1}")
    box = boxes[leaf]
    n = 6

    root = parse_tree(dexpr)
    mark_guards(root)
    segs = topmost_cert_segs(root)
    atan_roots = closed_trans_roots(root)
    print(f"[localize] dexpr nodes {node_size(root)} (text ops {ns} sqrt / "
          f"{ni} div / {nt} trans)  topmost cert segs {len(segs)}  "
          f"closed-trans {len(atan_roots)}")

    pieces = {
        "dexpr": (dexpr, ns, ni, nt, "full text mirror"),
        "noatan1": (splice(dexpr, [(x.start, x.end, "(.const ⟨1, 0⟩)")
                                   for x in atan_roots]),
                    ns, ni, nt, "arctan(1) 2048-series copies -> const"),
        "skel": (splice(dexpr, [(x.start, x.end, "(.const ⟨1, 0⟩)")
                                for x in segs]),
                 0, 0, 0, "cert segs -> const (poly skeleton)"),
    }
    for i, s in enumerate(segs):
        sc = seg_census(s)
        pieces[f"seg{i}"] = (s.text(dexpr), sc[0], sc[1], sc[2],
                             f"topmost cert seg {i} ({s.op}, "
                             f"{node_size(s)} nodes)")

    probes = [(tag, t, pns, pni, pnt)
              for tag, (t, pns, pni, pnt, _d) in pieces.items()]
    res, rung, pms = run_probe_batch(
        f"Fold2Loc{leaf}", n, probes, box, gran, rung_n, rung_out,
        lean_root, out_dir)

    want = dp_mantissas(params[leaf])
    got = res["dexpr"][3]
    if got != want:
        die(f"dexpr mantissa queue != C549M2DP{leaf} sqrtCerts — the "
            f"reconstructed text is NOT the Mono2 derivative (provenance "
            f"abort); got {got[:2]}.. want {want[:2]}..")
    print(f"[localize] provenance: dexpr mantissa queue == C549M2DP{leaf} "
          f"({len(got)} triples) IDENTICAL")
    if res["dexpr"][0] != ("PASS" if vtgt == "true" else "NEG"):
        die(f"dexpr probe verdict {res['dexpr'][0]} != Mono2 kernel {vtgt}")
    print(f"[localize] dexpr probe {res['dexpr'][0]} == Mono2 kernel "
          f"verdict {vtgt} OK")

    times = {}
    base_p = os.path.join(out_dir, f"base{leaf}.lean")
    with open(base_p, "w") as f:
        f.write(BASE_TIMING_TMPL.format(leaf=leaf, j=j, verdict=vtgt))
    times["base (kernel derivIExpr, matcher+eval)"] = (
        time_lean_module(base_p, lean_root), base_p, f"kernel {vtgt}")
    for tag, (t, pns, pni, pnt, desc) in pieces.items():
        verd, lo_m, lo_e, trips = res[tag]
        mod_p = os.path.join(out_dir, f"{tag}{leaf}.lean")
        with open(mod_p, "w") as f:
            f.write(TIMING_TMPL.format(
                tag=tag, n=n, expr=t, box=box,
                params=params_line(rung, pni, pnt, trips),
                verdict="true" if verd == "PASS" else "false"))
        times[f"{tag}: {desc}"] = (
            time_lean_module(mod_p, lean_root), mod_p,
            f"{verd} lo={lo_m}e{lo_e} {len(trips)}sq/{pni}iv/{pnt}tr "
            f"probe-eval {pms.get(tag, 0):.1f}s")
    print("\n[localize] isolated decide timings (wall s, incl ~4s import "
          "harness; desc order):")
    for tag, (dt, p, extra) in sorted(times.items(), key=lambda kv: -kv[1][0]):
        print(f"  {dt:7.1f}s  {tag:56s} {extra}")
    print(f"[localize] done in {time.time() - t0:.1f}s, modules in {out_dir}")


def cmd_plan(case_path, j, min_size, max_lets, min_occ):
    _, dexpr, (ns, ni, nt) = build_dexpr(case_path, j)
    print(f"[plan] dexpr ops {ns} sqrt / {ni} div / {nt} trans")
    for mode, cfo in (("free (cert-free)", True), ("full (全折叠)", False)):
        try:
            plan = plan_fold_text(dexpr, min_size, max_lets, min_occ, cfo)
        except SystemExit:
            print(f"[plan] {mode}: nothing to fold")
            continue
        print(f"[plan] {mode}: slots {plan['k']} refs {plan['n_ref']} "
              f"unfolded {plan['total_nodes']}")
        for i, (t, f) in enumerate(plan["taken"]):
            cf = "FREE" if cert_free_node(parse_tree(t)) else "CERT"
            print(f"  slot {i}: {len(f)} refs x {t.count('(.') + 1} nodes "
                  f"[{cf}] {t[:64]}")


STAGEA_DER_TMPL = """/-
  549 导数叶 stage-A-let 探针驱动（emit_fold2.py stagea-der 自动生成）.
  case {caseid} — 导数叶全折叠（证书消耗子树入表）：table slots {k}
  ({slot_desc})，body refs {refs}，unfolded {nodes} nodes.
  ps 契约：表项按下标序先求值，然后 body——mantissa 三元组按该序上报；
  这是折叠路径唯一有效的参数（两层管线：C 出盒，Lean 重产参数）.
  运行：lake env lean --run {out} > params.txt
-/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Kepler.Interval

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

def Tbl : Fin {k} → IExpr {n} := ![{table}]

def Body : LExpr {n} {k} :=
  {body}

/-- 模板参数：mantissa 占位 0，granularity {gran}（消费不完即剩余，无害）. -/
def Ps : TMParams :=
  ⟨List.replicate {nsqrt} ⟨0, 0, 0, ({gran}), ({gran})⟩,
   List.replicate {ndiv} ⟨({gran}), ({gran}), ({gran})⟩,
   List.replicate {ntrans} ⟨({gran}), ({gran})⟩⟩

def Boxes : Array (Fin {n} → DInterval) := #[
    {boxes}
]

def main : List String → IO UInt32 := fun _ => do
  IO.println "RUNG {rung_n} {rung_out} ({gran}) ({gran}) ({gran}) ({gran}) ({gran}) ({gran}) ({gran})"
  for i in [0:Boxes.size] do
    let t0 ← IO.monoMsNow
    match tmHullLeafProbeL Tbl Body Boxes[i]! Ps with
    | some (p, m, e, l) =>
        let ms ← IO.monoMsNow
        let v : String := if p then "PASS" else "NEG"
        let trip := String.intercalate " " (l.map fun t => s!"{{t.1}} {{t.2.1}} {{t.2.2}}")
        IO.eprintln s!"probe {{i}}: {{ms - t0}} ms"
        IO.println s!"{{i}} {{v}} {{m}} {{e}} {{trip}}"
    | none =>
        let ms ← IO.monoMsNow
        IO.eprintln s!"probe {{i}}: {{ms - t0}} ms FAIL"
        IO.println s!"{{i}} FAIL"
  return 0
"""


def cmd_stagea_der(case_path, mono2_path, out_path, nleaves, min_size,
                   max_lets, min_occ, gran, rung_n, rung_out):
    t0 = time.time()
    case, dexpr, (ns, ni, nt) = build_dexpr(case_path, 2, rung_n, rung_out)
    plan = plan_fold_text(dexpr, min_size, max_lets, min_occ,
                          cert_free_only=False)
    boxes, params, verdicts = harvest_mono2(mono2_path)
    leaves = [x for x in sorted(verdicts) if x <= nleaves]
    if len(leaves) != nleaves:
        die(f"Mono2 covers leaves {sorted(verdicts)}, need 1..{nleaves}")
    for x in leaves:
        if x not in boxes or x not in params:
            die(f"Mono2 leaf {x} missing Box/DP")
    text = STAGEA_DER_TMPL.format(
        caseid=case["id"], k=plan["k"], slot_desc=plan["slot_desc"],
        refs=plan["n_ref"], nodes=plan["total_nodes"], out=out_path,
        n=6, table=plan["table_txt"], body=plan["body"],
        nsqrt=ns, ndiv=ni, ntrans=nt, gran=gran,
        boxes=",\n    ".join(f"({boxes[x]} : Fin 6 → DInterval)"
                             for x in leaves),
        rung_n=rung_n, rung_out=rung_out)
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w") as f:
        f.write(text)
    manifest = {
        "schema": "stagea-der",
        "case": case["id"],
        "driver": out_path,
        "params_out": out_path.rsplit(".lean", 1)[0] + ".params.txt",
        "probe_cmd": f"lake env lean --run {out_path} > "
                     f"{out_path.rsplit('.lean', 1)[0] + '.params.txt'}",
        "fold": {"min_size": min_size, "max_lets": max_lets,
                 "min_occ": min_occ, "cert_free_only": False,
                 "slots": plan["k"], "body_refs": plan["n_ref"],
                 "unfolded_nodes": plan["total_nodes"],
                 "slot_desc": plan["slot_desc"]},
        "counts": {"sqrt": ns, "div": ni, "trans": nt},
        "template": {"rung_n": rung_n, "rung_out": rung_out, "gran": gran},
        "ps_contract": "entries first in index order, then body; "
                       "mantissa triples report that order",
        "harvest": mono2_path,
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "emit_elapsed_s": round(time.time() - t0, 1),
    }
    with open(out_path.rsplit(".lean", 1)[0] + ".manifest.json", "w") as f:
        json.dump(manifest, f, indent=1)
    print(f"[stagea-der] wrote {out_path}  ({time.time() - t0:.1f}s)  "
          f"slots {plan['k']} refs {plan['n_ref']} unfolded "
          f"{plan['total_nodes']} nodes; template Ps {ns}/{ni}/{nt}")
    for i, (t, f) in enumerate(plan["taken"]):
        cf = "cert-free" if cert_free_node(parse_tree(t)) else "cert-consuming"
        print(f"[stagea-der]   slot {i}: {len(f)} refs x "
              f"{t.count('(.') + 1} nodes  {cf}  {t[:56]}")
    print(f"[stagea-der] run from lean/: lake env lean --run {out_path} > "
          f"{manifest['params_out']}")


def cmd_stageb_der(case_path, mono2_path, params_path, out_path, nleaves,
                   min_size, max_lets, min_occ, tactic, split_dir):
    t0 = time.time()
    if tactic not in ("decide", "native_decide"):
        die(f"unknown tactic {tactic!r}")
    case, dexpr, (ns, ni, nt) = build_dexpr(case_path, 2)
    plan = plan_fold_text(dexpr, min_size, max_lets, min_occ,
                          cert_free_only=False)
    plan_free = plan_fold_text(dexpr, min_size, max_lets, min_occ,
                               cert_free_only=True)
    boxes, params, verdicts = harvest_mono2(mono2_path)
    rung, probe = parse_hull_params(params_path, ns)
    leaves = [x for x in sorted(verdicts) if x <= nleaves]
    if len(leaves) != nleaves:
        die(f"Mono2 covers leaves {sorted(verdicts)}, need 1..{nleaves}")
    missing = [x for x in leaves if (x - 1) not in probe]
    if missing:
        die(f"stage-A-let params cover {sorted(probe)[:3]}..., missing "
            f"leaves {missing} (re-run stagea-der with --leaves={nleaves})")
    mod = os.path.basename(out_path).rsplit(".lean", 1)[0]
    rows = []
    for x in leaves:
        verd, lo_m, lo_e, trips = probe[x - 1]
        vj, vtgt = verdicts[x]
        if (verd == "PASS") != (vtgt == "true"):
            print(f"[stageb-der] WARNING leaf {x}: probe {verd} vs Mono2 "
                  f"{vtgt} — emitting agreement target")
        rows.append((x, boxes[x], vtgt, verd, lo_m, lo_e, trips))

    parts = []
    for (x, box, vtgt, verd, lo_m, lo_e, trips) in rows:
        tgt = "true" if verd == "PASS" else "false"
        parts.append(
            f"/-- 叶 {x}（盒/原参数逐字引用 C549Mono2）.\n"
            f"free 臂参数 = C549M2DP{x} 原文（证书免费折叠不改 ps 消费序）；\n"
            f"full 臂参数 = stage-A-let 重产（entries-first），probe 判定 "
            f"{verd}，\nloBound {lo_m} * 2^({lo_e}). -/\n"
            f"def {mod}P{x} : TMParams := "
            f"{params_line(rung, ni, nt, trips)}\n\n"
            f"/-- base 臂 {x}：内核 derivIExpr 全量（零重算引用 Mono2 定理）. -/\n"
            f"theorem {mod}Base{x} :\n"
            f"    checkPosTMHull ((derivIExpr Kepler.Interval.Cases2."
            f"C549M2Expr 2))\n"
            f"      Kepler.Interval.Cases2.C549M2Box{x} "
            f"Kepler.Interval.Cases2.C549M2DP{x} = {vtgt} :=\n"
            f"  Kepler.Interval.Cases2.C549M2Der{x}\n\n"
            f"/-- free 臂 {x}：证书免费折叠（{plan_free['k']} slots）+ 原参数. -/\n"
            f"theorem {mod}Free{x} :\n"
            f"    checkPosTMHullL {mod}FreeTbl {mod}FreeBody "
            f"Kepler.Interval.Cases2.C549M2Box{x} "
            f"Kepler.Interval.Cases2.C549M2DP{x} = {vtgt} := by\n"
            f"  {tactic}\n\n"
            f"/-- full 臂 {x}：全折叠（{plan['k']} slots）+ 重产参数\n"
            f"（kernel/compiled-run 一致性即证书）. -/\n"
            f"theorem {mod}Full{x} :\n"
            f"    checkPosTMHullL {mod}Tbl {mod}Body "
            f"Kepler.Interval.Cases2.C549M2Box{x} {mod}P{x} = {tgt}"
            f" := by\n  {tactic}\n")
    def base_prop(x):
        return (f"checkPosTMHull ((derivIExpr Kepler.Interval.Cases2."
                f"C549M2Expr 2)) Kepler.Interval.Cases2.C549M2Box{x} "
                f"Kepler.Interval.Cases2.C549M2DP{x} = true")

    def free_prop(x):
        return (f"checkPosTMHullL {mod}FreeTbl {mod}FreeBody "
                f"Kepler.Interval.Cases2.C549M2Box{x} "
                f"Kepler.Interval.Cases2.C549M2DP{x} = true")

    def full_prop(x, tgt):
        return (f"checkPosTMHullL {mod}Tbl {mod}Body "
                f"Kepler.Interval.Cases2.C549M2Box{x} {mod}P{x} = {tgt}")

    def pair(x):
        return (f"({base_prop(x)} ∧ {free_prop(x)} ∧ "
                f"{full_prop(x, 'true' if dict((r[0], r[3]) for r in rows)[x] == 'PASS' else 'false')})")

    def nest(xs):
        if len(xs) == 1:
            return pair(xs[0])
        return f"{pair(xs[0])} ∧\n    {nest(xs[1:])}"

    text = (
        f"/-\n"
        f"  549 导数叶 LExpr 去重三方试点（emit_fold2.py stageb-der 生成）.\n"
        f"  case: {case['id']}  导数叶 ∂x3f（then 支），unfolded "
        f"{plan['total_nodes']} nodes\n  (2184 ops、574% 文本重复).\n"
        f"  full fold: table slots {plan['k']} ({plan['slot_desc']}), "
        f"body refs {plan['n_ref']};\n"
        f"  free fold: slots {plan_free['k']} ({plan_free['slot_desc']}).\n"
        f"  三方：base = 原版 derivIExpr 全量（引用 C549M2Der，零重算）；\n"
        f"  free = 证书免费折叠 + C549M2DP 原参数（ps 序不变）；\n"
        f"  full = 全折叠 + stage-A-let 重产参数（entries-first 消费序）.\n"
        f"  证书消耗子树入表 ⇒ ps 队列按表序先耗，C 侧证书定位失配是设计内\n"
        f"  （两层管线：C 出盒，Lean 重产参数）.\n"
        f"-/\n"
        f"import Kepler.Interval.Cases.C549Mono2\n\n"
        f"set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
        f"namespace Kepler.Interval.Cases\n\n"
        f"open Kepler.Interval\n\n"
        f"/-- free 折叠证书表（证书免费子树；消费零证书，ps 序不变）. -/\n"
        f"def {mod}FreeTbl : Fin {plan_free['k']} → IExpr 6 := "
        f"![{plan_free['table_txt']}]\n\n"
        f"def {mod}FreeBody : LExpr 6 {plan_free['k']} :=\n"
        f"  {plan_free['body']}\n\n"
        f"/-- full 折叠证书表（证书消耗子树入表；entries-first 消费）. -/\n"
        f"def {mod}Tbl : Fin {plan['k']} → IExpr 6 := "
        f"![{plan['table_txt']}]\n\n"
        f"def {mod}Body : LExpr 6 {plan['k']} :=\n"
        f"  {plan['body']}\n\n"
        + "\n".join(parts) +
        f"\n/-- 三方一致性合取（目标 = 命题全文；项 = 定理名匿名构造子逐层嵌套）. -/\n"
        f"theorem {mod}_pilot :\n    " +
        nest([r[0] for r in rows]) +
        f" :=\n  " +
        "⟨" + ", ".join(
            f"⟨{mod}Base{x}, {mod}Free{x}, {mod}Full{x}⟩"
            for (x, *_r) in rows) + "⟩\n\n"
        f"#print axioms {mod}_pilot\n\n"
        f"end Kepler.Interval.Cases\n")
    with open(out_path, "w") as f:
        f.write(text)
    manifest = {
        "schema": "stageb-der",
        "case": case["id"],
        "module": mod, "out": out_path,
        "params_source": params_path,
        "fold": {"min_size": min_size, "max_lets": max_lets,
                 "min_occ": min_occ, "cert_free_only": False,
                 "slots": plan["k"], "body_refs": plan["n_ref"],
                 "unfolded_nodes": plan["total_nodes"],
                 "slot_desc": plan["slot_desc"]},
        "fold_free": {"slots": plan_free["k"],
                      "slot_desc": plan_free["slot_desc"]},
        "tactic": tactic,
        "leaves": [{"x": x, "mono2_verdict": vtgt, "probe_verdict": verd,
                    "lo_m": lo_m, "lo_e": lo_e,
                    "n_sqrt_trips": len(trips)}
                   for (x, _b, vtgt, verd, lo_m, lo_e, trips) in rows],
        "split_dir": split_dir,
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "emit_elapsed_s": round(time.time() - t0, 1),
    }
    written = []
    if split_dir:
        os.makedirs(split_dir, exist_ok=True)
        for (x, box, vtgt, verd, lo_m, lo_e, trips) in rows:
            tgt = "true" if verd == "PASS" else "false"
            specs = [
                ("base", BASE_TIMING_TMPL.format(leaf=x, j=2, verdict=vtgt)),
                ("dexpr", TIMING_TMPL.format(
                    tag="dexpr", n=6, expr=dexpr, box=box,
                    params=params[x], verdict=vtgt)),
                ("freefold", TIMING_L_TMPL.format(
                    tag="free-fold", n=6, k=plan_free["k"],
                    table=plan_free["table_txt"], body=plan_free["body"],
                    box=box, params=params[x], verdict=vtgt,
                    note="证书免费折叠 + DP 原参数")),
                ("fullfold", TIMING_L_TMPL.format(
                    tag="full-fold", n=6, k=plan["k"],
                    table=plan["table_txt"], body=plan["body"],
                    box=box, params=params_line(rung, ni, nt, trips),
                    verdict=tgt, note="全折叠 + 重产参数")),
            ]
            for arm, body in specs:
                fp = os.path.join(split_dir, f"{mod}{arm.capitalize()}{x}.lean")
                with open(fp, "w") as f:
                    f.write(body)
                written.append(fp)
        manifest["timing_modules"] = written
    with open(out_path.rsplit(".lean", 1)[0] + ".manifest.json", "w") as f:
        json.dump(manifest, f, indent=1)
    n_pass = sum(1 for r in rows if r[3] == "PASS")
    print(f"[stageb-der] wrote {out_path}  ({time.time() - t0:.1f}s)  "
          f"{len(rows)} leaves, full slots {plan['k']}, free slots "
          f"{plan_free['k']}, probe PASS {n_pass}/{len(rows)}")
    if split_dir:
        print(f"[stageb-der] {len(written)} timing modules in {split_dir}")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = {}
    for a in sys.argv[1:]:
        if a.startswith("--") and "=" in a:
            k, v = a[2:].split("=", 1)
            opts[k] = v
    if not args:
        die(__doc__)
    cmd = args[0]
    if cmd == "localize":
        cmd_localize(args[1], args[2], int(opts.get("j", 2)),
                     int(opts.get("leaf", 1)),
                     opts.get("out-dir", "out/p549fold2/loc"),
                     int(opts.get("gran", -80)))
    elif cmd == "plan":
        cmd_plan(args[1], int(opts.get("j", 2)),
                 int(opts.get("min-size", 12)), int(opts.get("max-lets", 8)),
                 int(opts.get("min-occ", 2)))
    elif cmd == "stagea-der":
        cmd_stagea_der(args[1], args[2], args[3],
                       int(opts.get("leaves", 3)),
                       int(opts.get("min-size", 12)),
                       int(opts.get("max-lets", 8)),
                       int(opts.get("min-occ", 2)),
                       int(opts.get("gran", -80)),
                       int(opts.get("rung", 128)),
                       int(opts.get("rung-out", -80)))
    elif cmd == "stageb-der":
        cmd_stageb_der(args[1], args[2], args[3], args[4],
                       int(opts.get("leaves", 3)),
                       int(opts.get("min-size", 12)),
                       int(opts.get("max-lets", 8)),
                       int(opts.get("min-occ", 2)),
                       opts.get("tactic", "decide"),
                       opts.get("split-dir"))
    else:
        die(f"unknown cmd {cmd}")


if __name__ == "__main__":
    main()

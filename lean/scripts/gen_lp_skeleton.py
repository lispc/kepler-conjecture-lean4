#!/usr/bin/env python3
"""gen_lp_skeleton.py — LP 终端 per-record 骨架层生成器（T2 波，2026-10-08）。

镜像 P6-C 先例（gen_goodlist_shards.py / gen_idlists.py 形制：数据全库
确定性重导，产物机器生成勿手改）。生成（lean/Kepler/Text/LP/ 下）：

  LPIds.lean           记录清单数据（chunk=250/def，IdLists 230/def 同款量级）
  LPLeafInfeas*.lean   infeasible 记录叶（189 条，PLACEHOLDER(LP-infeas) 语义）
  LPLeafRoot*.lean     root 批叶（19,237 feasible）
  LPLeafEasy*.lean     easy 批叶（4,362 feasible）
  LPLeafHard*.lean     hard 批叶（19,290 feasible）
  LPAll.lean           分段/总量化装配（内核真证，逐叶具名分发）

语义核心 LPCert.lean 为手写件（不在本生成器范围）。
chunk/文件/分发单元 1:1:1 对齐（250 条）。

记录清单来源（全在库，零编造）：reference/flyspeck/formal_lp/glpk/binary/
{easy,hard}_*.dat（hard_7 为 .tar.gz，解到临时目录），经已提交读器
pipeline/lp/parse_lpcert.py 解析，证书树 DFS 序即 ti 序（与
make_tasks2a.py / make_tasks_hard.py 同一口径；easy 批 4,403/41 与
hard 批 19,438/148 可用二者 --stats 交叉复核）。

盘点基线（2026-10-08 T2 侦察）：19,715 图 / 43,078 终端
（root 19,237 + easy 4,403 + hard 19,438）/ infeasible 189。
盘点数与基线不符时脚本退出码 2（清单漂移须人工裁决，不静默落盘）。

用法：
  python3 lean/scripts/gen_lp_skeleton.py [--limit N]   # 试点批/全量
  python3 lean/scripts/gen_lp_skeleton.py --check       # 只盘点，不落盘

探针（每生成文件，逐错迭代到零；依赖 olean 的先 lake build 单模块）：
  cd lean && ~/.elan/bin/lake env lean Kepler/Text/LP/<file>.lean
"""
import argparse
import json
import sys
import tarfile
import tempfile
import threading
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
sys.setrecursionlimit(2_000_000)
threading.stack_size(512 * 1024 * 1024)
sys.path.insert(0, str(REPO / "pipeline" / "lp"))
import parse_lpcert as P  # noqa: E402

BIN = REPO / "reference" / "flyspeck" / "formal_lp" / "glpk" / "binary"
OUTDIR = REPO / "lean" / "Kepler" / "Text" / "LP"

# 盘点基线（STATUS.md 2026-09-24 LP 收官口径 + P6-C STATUS 19,715 图口径）
# root/easy/hard = 原始批终端数（infeasible 重分类前）；
# rootF/easyF/hardF = 各批 feasible 终端数（入 bound 形定义域）。
EXPECT = {
    "graphs": 19715,
    "terminals": 43078,
    "root": 19237,
    "easy": 4403,
    "hard": 19438,
    "infeasible": 189,
    "rootF": 19237,
    "easyF": 4362,
    "hardF": 19290,
}

CHUNK = 250   # 每文件/每 chunk 记录数（IdLists 230/def 同量级；超 512 深 literal
              # 会撞 elaborator maxRecDepth 默认值）
SEGS = ("infeas", "root", "easy", "hard")
PRED = {"infeas": "AllLpTerminalInfeasibleCertified",
        "root": "AllLpTerminalCertified",
        "easy": "AllLpTerminalCertified",
        "hard": "AllLpTerminalCertified"}
SEGWHAT = {"infeas": "infeasible 记录叶（PLACEHOLDER(LP-infeas) 语义）",
           "root": "root 批叶（单终端图根 LP）",
           "easy": "easy 批叶（多终端 easy 图分支终端）",
           "hard": "hard 批叶（hard 图分支终端）"}
SEGCAP = {"infeas": "Infeas", "root": "Root", "easy": "Easy", "hard": "Hard"}


def chunk_def(seg, i):
    return f"lp{SEGCAP[seg]}Ids{i:02d}"


def seg_def(seg):
    return f"lp{SEGCAP[seg]}Ids"


def seg_total(seg):
    return f"lpAll{SEGCAP[seg]}"


def leaf_file_stem(seg, i):
    return f"LPLeaf{SEGCAP[seg]}{i:02d}"


HEADER = """\
/-
  {mod} — LP 终端 per-record 骨架层（T2 波 2026-10-08，机器生成，勿手改）。

  生成器：`lean/scripts/gen_lp_skeleton.py`（{what}；再生成会覆盖本文件）。
  记录清单来源：reference/flyspeck/formal_lp/glpk/binary
  的 {{easy,hard}}_*.dat 确定性重放（parse_lpcert.py 已提交读器，
  DFS 序 = ti 序）。信任模型：叶 = open `sorry` 骨架（deferred-compute），
  闭合 = LP 重跑产物模块（`socert.py --col-major` 形，PilotCM204880136538
  在库样板）转发；语义核心与退化防线见 `Kepler.Text.LP.LPCert`。
-/
{imports}
set_option maxRecDepth 4096

namespace Kepler.Text.LP

"""


def hypermap_id(hs: str) -> str:
    return hs.replace("_", "").split()[0]


def dat_paths(tmp: Path):
    paths = sorted(str(p) for p in BIN.glob("*.dat"))
    tgz = BIN / "hard_7.tar.gz"
    if tgz.exists():
        with tarfile.open(tgz) as tf:
            tf.extractall(tmp)
        paths.append(str(tmp / "hard_7.dat"))
    return paths


def collect_flags(case, out):
    if case[1] == 0:  # Lp_terminal: block (precision, infeasible, nconstr, ...)
        t = case[2][0]
        assert t[0] == "block" and len(t[2]) == 5
        out.append(bool(t[2][1]))
        return
    assert case[1] == 1, f"bad case tag {case[1]}"
    for c in P.to_list(case[2][1]):
        collect_flags(c, out)


def scan(tmp: Path):
    """全库盘点：每证书树 DFS 枚举终端记录（零 LP 求解，纯 ID 枚举）。"""
    records, graphs = [], set()
    for path in dat_paths(tmp):
        name = Path(path).stem
        certs = [P.to_cert(v) for v in P.to_list(P.read_marshal(path))]
        for gi, cert in enumerate(certs):
            hid = hypermap_id(cert["hypermap_string"])
            assert hid not in graphs, f"duplicate graph id {hid}"
            graphs.add(hid)
            flags = []
            collect_flags(cert["root_case"], flags)
            for ti, infl in enumerate(flags):
                orig = "hard" if name.startswith("hard") else "easy"
                if orig == "easy" and len(flags) == 1:
                    orig = "root"
                batch = "infeas" if infl else orig
                records.append({"id": f"{hid}_t{ti:04d}", "batch": batch,
                                "orig": orig, "dat": name, "gi": gi})
    return records, graphs


def chunks(lst, n):
    return [lst[i:i + n] for i in range(0, len(lst), n)]


def leaf_name(rec):
    return "lpT" + rec["id"].replace("_", "")


def emit_leaf(f, rec):
    if rec["batch"] == "infeas":
        f.write(
            f"/-- `{rec['id']}`（{rec['dat']}#{rec['gi']} · infeasible 支）\n"
            f"NEEDS(deferred-compute): 不可行性证书通道（PLACEHOLDER(LP-infeas)，"
            f"退化防线见 LPCert）定形后转发闭合。 -/\n"
            f"theorem {leaf_name(rec)} : "
            f"LpTerminalInfeasibleCertified \"{rec['id']}\" := by\n  sorry\n\n")
    else:
        f.write(
            f"/-- `{rec['id']}`（{rec['dat']}#{rec['gi']}）\n"
            f"NEEDS(deferred-compute): LP 重跑（SoPlex 主批/glpsol 对偶尾部）"
            f"产物转发闭合。 -/\n"
            f"theorem {leaf_name(rec)} : "
            f"LpTerminalCertified \"{rec['id']}\" := by\n  sorry\n\n")


def write_leaf_file(path, recs, seg, i):
    list_def = chunk_def(seg, i)
    total_name = f"lpAll{SEGCAP[seg]}{i:02d}"
    pred = PRED[seg]
    with open(path, "w") as f:
        f.write(HEADER.format(mod=f"Kepler/Text/LP/{path.stem}",
                              what=SEGWHAT[seg],
                              imports="import Kepler.Text.LP.LPIds"))
        for r in recs:
            emit_leaf(f, r)
        f.write(f"/-- 本片量化装配（真实推导，逐叶具名分发；{len(recs)} 条）。 -/\n"
                f"theorem {total_name} : {pred} {list_def} := by\n"
                f"  intro id hid\n"
                f"  simp only [{list_def}, List.mem_cons] at hid\n")
        for r in recs[:-1]:
            f.write(f"  rcases hid with rfl | hid\n"
                    f"  · exact {leaf_name(r)}\n")
        f.write(f"  · exact {leaf_name(recs[-1])}\n\n")


def emit_ids(path, segrecs):
    """LPIds.lean：chunk 数据（250/def）+ 段 concat + 长度定理（norm_num 链）。"""
    out = [HEADER.format(mod="Kepler/Text/LP/LPIds",
                         what="记录清单数据（段序 infeas→root→easy→hard）",
                         imports="import Kepler.Text.LP.LPCert")]
    for seg in SEGS:
        recs = segrecs.get(seg, [])
        cs = chunks(recs, CHUNK)
        for i, c in enumerate(cs):
            items = ",\n".join(f"    \"{r['id']}\"" for r in c)
            out.append(f"/-- `{seg}` 段记录 chunk {i:02d}（{len(c)} 条）。 -/\n"
                       f"def {chunk_def(seg, i)} : List String :=\n  [\n{items}\n  ]\n\n"
                       f"theorem {chunk_def(seg, i)}_length : "
                       f"{chunk_def(seg, i)}.length = {len(c)} := rfl\n\n")
        defs = [chunk_def(seg, i) for i in range(len(cs))]
        rhs = " ++\n".join(f"  {d}" for d in defs) if defs else "  []"
        lenlemmas = ", ".join(f"{d}_length" for d in defs) if defs else ""
        simpset = f"[{seg_def(seg)}, List.length_append{', ' + lenlemmas if lenlemmas else ''}]"
        out.append(f"/-- `{seg}` 段全清单 = {max(len(defs), 1)} chunk 之并"
                   f"（{len(recs)} 条）。 -/\n"
                   f"def {seg_def(seg)} : List String :=\n{rhs}\n\n"
                   f"theorem {seg_def(seg)}_length : {seg_def(seg)}.length = {len(recs)} := by\n"
                   f"  simp only {simpset}\n"
                   f"  all_goals norm_num\n\n")
    n_root = len(segrecs.get("root", []))
    n_easy = len(segrecs.get("easy", []))
    n_hard = len(segrecs.get("hard", []))
    n_inf = len(segrecs.get("infeas", []))
    out.append("/-- bound 形定义域 = 三 feasible 段之并。 -/\n"
               "def lpTerminalBoundIds : List String :=\n"
               "  lpRootIds ++ lpEasyIds ++ lpHardIds\n\n"
               "theorem lpTerminalBoundIds_length : "
               f"lpTerminalBoundIds.length = {n_root + n_easy + n_hard} := by\n"
               "  simp only [lpTerminalBoundIds, List.length_append, "
               "lpRootIds_length, lpEasyIds_length, lpHardIds_length]\n"
               "  all_goals norm_num\n\n"
               "/-- master 清单 = infeasible 段 ++ bound 形定义域"
               "（覆盖盘点基线全体记录）。 -/\n"
               "def lpTerminalIds : List String :=\n"
               "  lpInfeasIds ++ lpTerminalBoundIds\n\n"
               "theorem lpTerminalIds_length : "
               f"lpTerminalIds.length = {n_root + n_easy + n_hard + n_inf} := by\n"
               "  simp only [lpTerminalIds, List.length_append, "
               "lpInfeasIds_length, lpTerminalBoundIds_length]\n"
               "  all_goals norm_num\n")
    path.write_text("".join(out))


def emit_chain(f, names, depth, inline=False):
    """mem_append 析取为左结合：((c0 ∨ c1) ∨ c2)... 首支复分解、末支直达。"""
    ind = "" if inline else "  " * depth
    if len(names) == 1:
        f.write(f"{ind}exact {names[0]} id hid\n")
        return
    f.write(f"{ind}rcases hid with hid | hid\n")
    f.write(f"{'  ' * depth}· ")
    emit_chain(f, names[:-1], depth + 1, inline=True)
    f.write(f"{'  ' * depth}· exact {names[-1]} id hid\n")


def emit_segment_total(f, seg, defs):
    """段总量化装配：chunk 链分发（真实推导；chunk 总量按点应用）。"""
    pred = PRED[seg]
    f.write(f"/-- `{seg}` 段总量（真实推导；{max(len(defs), 1)} chunk 链分发）。 -/\n"
            f"theorem {seg_total(seg)} : {pred} {seg_def(seg)} := by\n")
    if len(defs) == 0:
        f.write("  intro id hid\n"
                "  exact absurd hid (by simp)\n\n")
    elif len(defs) == 1:
        f.write("  intro id hid\n"
                f"  exact lpAll{SEGCAP[seg]}00 id hid\n\n")
    else:
        f.write("  intro id hid\n"
                f"  simp only [{seg_def(seg)}, List.mem_append] at hid\n")
        emit_chain(f, [f"lpAll{SEGCAP[seg]}{d[-2:]}" for d in defs], 1)
        f.write("\n")


def emit_all(path, segrecs, seg_chunk_defs):
    """LPAll.lean：段总量 + bound 总量（内核真证；逐叶分发经各叶文件）。"""
    imports = []
    for seg in SEGS:
        for i in range(len(seg_chunk_defs[seg])):
            imports.append(f"import Kepler.Text.LP.{leaf_file_stem(seg, i)}")
    with open(path, "w") as f:
        f.write(HEADER.format(mod="Kepler/Text/LP/LPAll",
                              what="量化装配：段总量 + bound 总量（内核真证）",
                              imports="\n".join(imports)))
        for seg in SEGS:
            emit_segment_total(f, seg, seg_chunk_defs[seg])
        n_root = len(segrecs.get("root", []))
        n_easy = len(segrecs.get("easy", []))
        n_hard = len(segrecs.get("hard", []))
        f.write("/-- bound 形总量（真实推导；三段分发，左结合递归）。 -/\n"
                "theorem lpTerminalBoundAll : AllLpTerminalCertified "
                "lpTerminalBoundIds := by\n"
                "  intro id hid\n"
                "  simp only [lpTerminalBoundIds, List.mem_append] at hid\n")
        emit_chain(f, [seg_total("root"), seg_total("easy"), seg_total("hard")], 1)
        f.write("\n"
                "/- 记录覆盖对账（数据层）：master 清单 = infeasible 段 ++ bound 段，\n"
                "两总量分治覆盖；长度定理见 LPIds（盘点基线 43,078 = 189 + 42,889）。\n"
                "NEEDS(deferred-compute): 42,889 bound 叶逐条重跑转发 + 189\n"
                "infeasible 证书通道定形；接口级消费 = Assembly §2d' 记账段。 -/\n")
    text = path.read_text().rstrip() + "\n"
    path.write_text(text)


RESULT = {"exit": 0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None,
                    help="试点批：每段只取前 N 条（默认全量 43,078）")
    ap.add_argument("--check", action="store_true", help="只盘点，不落盘")
    args = ap.parse_args()

    with tempfile.TemporaryDirectory() as td:
        records, graphs = scan(Path(td))

    summary = {
        "graphs": len(graphs),
        "terminals": len(records),
        "root": sum(1 for r in records if r["orig"] == "root"),
        "easy": sum(1 for r in records if r["orig"] == "easy"),
        "hard": sum(1 for r in records if r["orig"] == "hard"),
        "infeasible": sum(1 for r in records if r["batch"] == "infeas"),
        "rootF": sum(1 for r in records if r["batch"] == "root"),
        "easyF": sum(1 for r in records if r["batch"] == "easy"),
        "hardF": sum(1 for r in records if r["batch"] == "hard"),
    }
    print("[gen_lp_skeleton] inventory:", json.dumps(summary))
    bad = {k: (summary[k], EXPECT[k]) for k in EXPECT if summary[k] != EXPECT[k]}
    if bad:
        print(f"[gen_lp_skeleton] INVENTORY MISMATCH (got, expected): {bad}", flush=True)
        RESULT["exit"] = 2
        return
    if args.check:
        return

    recs = sorted(records, key=lambda r: SEGS.index(r["batch"]))
    if args.limit:
        byseg0 = {}
        for r in recs:
            byseg0.setdefault(r["batch"], []).append(r)
        recs = []
        for seg in SEGS:
            recs.extend(byseg0.get(seg, [])[: args.limit])

    OUTDIR.mkdir(parents=True, exist_ok=True)
    segrecs = {}
    for r in recs:
        segrecs.setdefault(r["batch"], []).append(r)
    seg_chunk_defs = {seg: [chunk_def(seg, i)
                            for i in range(len(chunks(segrecs.get(seg, []), CHUNK)))]
                      for seg in SEGS}

    emit_ids(OUTDIR / "LPIds.lean", segrecs)
    print("[gen_lp_skeleton] wrote LPIds.lean", flush=True)

    total_counts = {}
    for seg in SEGS:
        cs = chunks(segrecs.get(seg, []), CHUNK)
        for i, c in enumerate(cs):
            path = OUTDIR / f"{leaf_file_stem(seg, i)}.lean"
            write_leaf_file(path, c, seg, i)
            total_counts[seg] = total_counts.get(seg, 0) + len(c)
        if cs:
            print(f"[gen_lp_skeleton] wrote {len(cs)} leaf file(s) for {seg} "
                  f"({total_counts.get(seg, 0)} records)", flush=True)

    emit_all(OUTDIR / "LPAll.lean", segrecs, seg_chunk_defs)
    print("[gen_lp_skeleton] wrote LPAll.lean", flush=True)
    print("[gen_lp_skeleton] totals:", json.dumps(total_counts), flush=True)


if __name__ == "__main__":
    t = threading.Thread(target=main)
    t.start()
    t.join()
    sys.exit(RESULT["exit"])

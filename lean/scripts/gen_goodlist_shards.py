#!/usr/bin/env python3
"""Generate the P6-C `good_list` mass-production shards for the assembly spine.

Reads the four archive data modules (`Kepler/Graphs/ArchiveData/{Tri,Quad,Pent,Hex}.lean`),
counts the fgraphs in each `{Cls}Data` list, and emits:

- `lean/Kepler/Assembly/GoodListShard{Cls}{ii}.lean` — one `native_decide`
  theorem per slice of `SLICE` graphs:
      theorem goodList{Cls}{ii} : (({Cls}Data.drop k).take m).all goodListB = true
  (last slice: `{Cls}Data.drop k`, single-slice class: `{Cls}Data` itself);
- `lean/Kepler/Assembly/GoodListAll.lean` — kernel-only combiner chaining the
  shard theorems with `all_of_take_drop` into per-class totals and finally
  `goodListArchiveAll : AllGoodList tameArchiveLists`.

Trust model: shards carry `native_decide` (per-theorem
`*._native.native_decide.ax_*`, same footprint as `Kepler.Graphs.Cert*`;
DECISIONS.md 2026-08-10 scoped exception, extended to `Kepler.Assembly.GoodList*`
on 2026-09-19).  The combiner is pure kernel.

Usage:  python3 lean/scripts/gen_goodlist_shards.py [repo_root] [slice_size]
"""
import os
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SLICE = int(sys.argv[2]) if len(sys.argv) > 2 else 1000

CLASSES = ["Tri", "Quad", "Pent", "Hex"]
DATA_DIR = os.path.join(ROOT, "lean", "Kepler", "Graphs", "ArchiveData")
OUT_DIR = os.path.join(ROOT, "lean", "Kepler", "Assembly")


def count_graphs(cls):
    """Count top-level entries of `def {cls}Data : List ... := [ ... ]`
    by bracket depth (entries are `[[...], ...]` fgraph literals)."""
    path = os.path.join(DATA_DIR, f"{cls}.lean")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    anchor = f"def {cls}Data"
    i = text.index(anchor)
    i = text.index("[", text.index(":=", i))  # opening bracket of the list
    depth, count, j = 0, 0, i
    seen_content = False
    while True:
        c = text[j]
        if c == "[":
            depth += 1
            if depth == 2:
                seen_content = True
        elif c == "]":
            if depth == 2 and seen_content:
                pass
            depth -= 1
            if depth == 1 and seen_content:
                count += 1
                seen_content = False
            if depth == 0:
                break
        j += 1
    return count


SHARD_HEADER = """/-
  Kepler/Assembly/{mod} — good_list 量产分片（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`（slice={slice}）；请勿手改，
  重新生成会覆盖。覆盖 {cls}Data 第 [{lo}, {hi}) 图（全类 {total} 图）。
  信任模型：native_decide（DECISIONS.md 2026-08-10 scoped exception，
  2026-09-19 扩展至 Kepler.Assembly.GoodList*）。
-/
import Kepler.Assembly.GoodListDefs

open Kepler.Graphs

namespace Kepler.Assembly

/-- 分片闭合：`{expr}` 上 `goodListB` 全真。 -/
theorem {thm} : ({expr}).all goodListB = true := by
  native_decide

#print axioms {thm}

end Kepler.Assembly
"""


def shard_mod(cls, i):
    return f"GoodListShard{cls}{i:02d}"


def shard_thm(cls, i):
    return f"goodList{cls}{i:02d}"


def slice_expr(cls, i, k):
    """List expression covered by slice i of k (each SLICE graphs)."""
    if k == 1:
        return f"{cls}Data"
    lo = i * SLICE
    if i == k - 1:
        return f"{cls}Data.drop {lo}"
    base = f"{cls}Data" if lo == 0 else f"({cls}Data.drop {lo})"
    return f"{base}.take {SLICE}"


def gen_shard(cls, i, k, total):
    expr = slice_expr(cls, i, k)
    lo, hi = i * SLICE, min((i + 1) * SLICE, total)
    body = SHARD_HEADER.format(mod=shard_mod(cls, i), slice=SLICE, cls=cls,
                               lo=lo, hi=hi, total=total, expr=expr,
                               thm=shard_thm(cls, i))
    path = os.path.join(OUT_DIR, f"{shard_mod(cls, i)}.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write(body)


def class_total_term(cls, k):
    """Nested `all_of_take_drop` term combining the k shard theorems."""
    if k == 1:
        return shard_thm(cls, 0)
    # all_of_take_drop (h1 := shard_i) (h2 := rest), implicit l/n inferred
    term = shard_thm(cls, k - 1)
    for i in range(k - 2, -1, -1):
        term = f"all_of_take_drop {shard_thm(cls, i)}\n      ({term})"
    return term


def gen_combiner(counts):
    ks = {c: max(1, -(-counts[c] // SLICE)) for c in CLASSES}
    imports = "\n".join(
        f"import Kepler.Assembly.{shard_mod(c, i)}"
        for c in CLASSES for i in range(ks[c]))
    parts = ["/-",
             "  Kepler/Assembly/GoodListAll — 全 archive good_list 组合定理"
             "（P6-C，机器生成）。",
             "",
             "  生成器：`lean/scripts/gen_goodlist_shards.py`；请勿手改。",
             "  本模块纯内核：把各分片 `native_decide` 定理经 `all_of_take_drop`",
             "  串成逐类总定理，最终 `goodListArchiveAll : AllGoodList "
             "tameArchiveLists`",
             "  （HOL `ALL good_list tame_archive_lists`，"
             "the_kepler_conjecture.hl 装配的 good_list 支）。",
             "-/", imports, "",
             "open Kepler.Graphs", "",
             "namespace Kepler.Assembly", ""]
    zh = {"Tri": "Tri（三角形种子）", "Quad": "Quad", "Pent": "Pent", "Hex": "Hex"}
    for c in CLASSES:
        parts.append(f"set_option maxRecDepth 1000000 in")
        parts.append(f"/-- {c} 类闭合：{counts[c]} 图，{ks[c]} 分片。 -/")
        parts.append(f"theorem allGood{c} : {c}Data.all goodListB = true :=")
        parts.append(f"  {class_total_term(c, ks[c])}")
        parts.append("")
    parts.append("""/-- HOL `ALL good_list tame_archive_lists`：全 archive 逐图 `good_list`。 -/
theorem goodListArchiveAll : AllGoodList tameArchiveLists := by
  intro L hL
  rw [tameArchiveLists, List.mem_append, List.mem_append, List.mem_append] at hL
  -- 重写后 hL 为左嵌套：((L ∈ TriData ∨ L ∈ QuadData) ∨ L ∈ PentData) ∨ L ∈ HexData
  cases hL with
  | inl hL => cases hL with
    | inl hL => cases hL with
      | inl hT => exact good_of_all allGoodTri L hT
      | inr hQ => exact good_of_all allGoodQuad L hQ
    | inr hP => exact good_of_all allGoodPent L hP
  | inr hH => exact good_of_all allGoodHex L hH

#print axioms goodListArchiveAll

end Kepler.Assembly
""")
    path = os.path.join(OUT_DIR, "GoodListAll.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(parts))


def main():
    counts = {c: count_graphs(c) for c in CLASSES}
    total = sum(counts.values())
    nshards = 0
    for c in CLASSES:
        k = max(1, -(-counts[c] // SLICE))
        for i in range(k):
            gen_shard(c, i, k, counts[c])
        nshards += k
    gen_combiner(counts)
    print(f"graphs: " + " ".join(f"{c}={counts[c]}" for c in CLASSES) +
          f" total={total}")
    print(f"slice={SLICE} shards={nshards} -> {OUT_DIR}")


if __name__ == "__main__":
    main()

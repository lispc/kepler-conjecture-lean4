#!/usr/bin/env python3
"""Generate kernel-reshard shards for the 16 `*_top_*` / `*_archive_pre` axioms.

For each (class, kind) pair we emit
  - one file per slice of `SLICE[(cls,kind)]` list items, whose theorem is
    the *statement* of the corresponding `Cert{Cls}.lean` native theorem
    restricted to `(l.drop lo).take sl` (last slice `l.drop lo`), proved by
    `decide +kernel`; and
  - one per-(class,kind) combiner module `{Kind}{Cls}.lean` chaining the
    slices with the generic `all_of_take_drop_b`.

The combiner statement is the original Cert statement verbatim (whitespace
normalised); the Cert file's theorem body is then replaced by a reference to
the combiner.

Usage: gen_top_shards.py <repo_root> <out_root> [cls:kind=slice ...]
"""
import os
import re
import sys

ROOT = sys.argv[1]
OUT = sys.argv[2]
OVERRIDE = {}
for a in sys.argv[3:]:
    k, v = a.split("=")
    OVERRIDE[tuple(k.split(":"))] = int(v)

CLASSES = ["Tri", "Quad", "Pent", "Hex"]
SEED = {"Tri": 0, "Quad": 1, "Pent": 2, "Hex": 3}
KINDS = ["archivePre", "topFinals", "topBounds", "topReplay"]
DEFAULT_SLICE = 100

CERT = {c: os.path.join(ROOT, "lean/Kepler/Graphs", f"Cert{c}.lean") for c in CLASSES}


def slice_size(cls, kind):
    return OVERRIDE.get((cls, kind), DEFAULT_SLICE)


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def cert_statement(cls, thm):
    """Text of `theorem <thm> : <stmt> := by` (normalised)."""
    text = open(CERT[cls], encoding="utf-8").read()
    m = re.search(r"theorem " + re.escape(thm) + r" :(.*?):= by", text, re.S)
    assert m, (cls, thm)
    return norm(m.group(1))


# list expression + `.all` predicate, extracted from the Cert statement
def split_stmt(cls, kind):
    """Return (base_list_expr, pred) such that the Cert statement is defeq to
    `(<base_list_expr>).all <pred> = true`."""
    thm = {"archivePre": f"{cls.lower()}_archive_pre",
           "topFinals": f"{cls.lower()}_top_no_finals",
           "topBounds": f"{cls.lower()}_top_bounds",
           "topReplay": f"{cls.lower()}_top_replay"}[kind]
    stmt = cert_statement(cls, thm)
    if kind == "archivePre":
        prefix, lst, tail = f"({cls}Data.all ", f"{cls}Data", ") = true"
    elif kind == "topFinals":
        prefix, lst, tail = f"({cls}Top.all ", f"{cls}Top", ") = true"
    elif kind == "topBounds":
        lst = f"List.range {cls}TopChildren.length"
        prefix, tail = f"({lst}).all ", " = true"
    else:
        lst = f"List.range {cls}Top.length"
        prefix, tail = f"({lst}).all ", " = true"
    assert stmt.startswith(prefix), (cls, kind, stmt[:90])
    assert stmt.endswith(tail), (cls, kind, stmt[-90:])
    pred = stmt[len(prefix):-len(tail)]
    assert pred.startswith("(fun "), (cls, kind, pred[:60])
    return lst, pred


def count_data(cls):
    path = os.path.join(ROOT, "lean/Kepler/Graphs/ArchiveData", f"{cls}.lean")
    text = open(path, encoding="utf-8").read()
    anchor = f"def {cls}Data"
    i = text.index(anchor)
    i = text.index("[", text.index(":=", i))
    depth, count, j = 0, 0, i
    seen_content = False
    while True:
        c = text[j]
        if c == "[":
            depth += 1
            if depth == 2:
                seen_content = True
        elif c == "]":
            depth -= 1
            if depth == 1 and seen_content:
                count += 1
                seen_content = False
            if depth == 0:
                break
        j += 1
    return count


def count_top(cls, name, entry="⟨"):
    path = os.path.join(ROOT, "lean/Kepler/Graphs/CertData", f"{cls}Top.lean")
    text = open(path, encoding="utf-8").read()
    i = text.index(f"def {name} ")
    k = text.index("[", text.index(":=", i))
    depth, end = 0, None
    for t in range(k, len(text)):
        if text[t] == "[":
            depth += 1
        elif text[t] == "]":
            depth -= 1
            if depth == 0:
                end = t
                break
    block = text[k:end + 1]
    return len([l for l in block.split("\n") if l.startswith("  " + entry)])


def counts():
    out = {}
    for c in CLASSES:
        out[(c, "archivePre")] = count_data(c)
        out[(c, "topFinals")] = count_top(c, f"{c}Top")
        out[(c, "topBounds")] = count_top(c, f"{c}TopChildren", entry="[")
        out[(c, "topReplay")] = count_top(c, f"{c}Top")
    return out


def camel(kind):
    return kind[0].upper() + kind[1:]


def mod_name(kind, cls, i=None):
    if i is None:
        return f"{camel(kind)}{cls}"
    return f"{camel(kind)}{cls}ShardS{i:03d}"


def thm_name(kind, cls, i=None):
    base = f"{kind}{cls}"
    return base + (f"S{i:03d}" if i is not None else "") + ("" if i is not None else "All")


def imports(kind, cls):
    if kind == "archivePre":
        return ["import Kepler.Graphs.CertCheck",
                f"import Kepler.Graphs.ArchiveData.{cls}",
                "import Kepler.Graphs.ReshardDefs"]
    return ["import Kepler.Graphs.CertCheck",
            f"import Kepler.Graphs.CertData.{cls}Top",
            "import Kepler.Graphs.ReshardDefs"]


def shard_file(kind, cls, i, k, total):
    lst, pred = split_stmt(cls, kind)
    sl = slice_size(cls, kind)
    lo = i * sl
    atom = lst if " " not in lst else f"({lst})"
    if k == 1:
        expr = lst
        cov = f"全类 {total} 项（单片）"
    elif i == k - 1:
        expr = f"{atom}.drop {lo}"
        cov = f"第 [{lo}, {total}) 项（末片）"
    elif lo == 0:
        expr = f"{atom}.take {sl}"
        cov = f"第 [0, {sl}) 项"
    else:
        expr = f"({atom}.drop {lo}).take {sl}"
        cov = f"第 [{lo}, {lo + sl}) 项"
    name = thm_name(kind, cls, i)
    body = f"""/-
  Kepler/Graphs/{mod_name(kind, cls, i)} — `{kind}` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `{kind}` / {cls}：覆盖 {cov}。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
""" + "\n".join(imports(kind, cls)) + f"""

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`{kind}` on slice {i}/{k} of {cls}. -/
theorem {name} : ({expr}).all {pred} = true := by
  decide +kernel

#print axioms {name}

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
"""
    return mod_name(kind, cls, i), body


def combiner_file(kind, cls, k, total):
    lst, pred = split_stmt(cls, kind)
    name = thm_name(kind, cls)
    if k == 1:
        body = f"""/-
  Kepler/Graphs/{mod_name(kind, cls)} — `{kind}` / {cls} 全类闭合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  单片：全类 {total} 项一次 `decide +kernel`（纯内核，无 native_decide）。
-/
""" + "\n".join(imports(kind, cls)) + f"""

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- {cls} `{kind}` 全类闭合：{total} 项，单片。 -/
theorem {name} : ({lst}).all {pred} = true := by
  decide +kernel

#print axioms {name}

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
"""
        return mod_name(kind, cls), body
    mods = [mod_name(kind, cls, i) for i in range(k)]
    imps = "\n".join(f"import Kepler.Graphs.{m}" for m in mods)
    term = thm_name(kind, cls, k - 1)
    for i in range(k - 2, 0, -1):
        term = (f"all_drop_of_split_b {thm_name(kind, cls, i)}\n"
                f"      ({term})")
    term = f"all_of_take_drop_b {thm_name(kind, cls, 0)}\n      ({term})"
    body = f"""/-
  Kepler/Graphs/{mod_name(kind, cls)} — `{kind}` / {cls} 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：{k} 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
{imps}

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- {cls} `{kind}` 全类闭合：{total} 项，{k} 分片。 -/
theorem {name} : ({lst}).all {pred} = true :=
  {term}

#print axioms {name}

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
"""
    return mod_name(kind, cls), body


DEFS = """/-
  Kepler/Graphs/ReshardDefs — `*_top_*` / `*_archive_pre` 内核重切的通用组合子。

  纯内核引理：`List.all` 在 `take`/`drop` 两片上都真，则整表真。
  （`Kepler.Assembly.all_of_take_drop` 的谓词泛化版；后者写死了 `goodListB`
  且作用在 `List (fgraph ℕ)` 上。）
-/
import Kepler.Graphs.Graph

namespace Kepler.Graphs

/-- 分片组合器（任意 Bool 谓词）：`take`/`drop` 两片各自 `all f`，则整表 `all f`。 -/
theorem all_of_take_drop_b {α : Type} {l : List α} {n : Nat} {f : α → Bool}
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) :
    l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]
  rfl

/-- 逐片链（符号版）：`l` 从 `m` 起的第一片 `n` 个元素全真，且 `l` 从 `m + n`
起的尾巴全真，则 `l` 从 `m` 起的整段全真。

与 `Kepler.Assembly.all_drop_of_split` 同构（谓词泛化）。**必须**用符号链：朴素的
`all_of_take_drop_b` 右嵌套在 k=161 时要证 `(D.drop (100*i)).drop 100 =?=
D.drop (100*(i+1))` 的大具体列表 defeq，实测 92.58 s 冲 8.03 GB 被杀。 -/
theorem all_drop_of_split_b {α : Type} {l : List α} {f : α → Bool} {m n : Nat}
    (h1 : ((l.drop m).take n).all f = true)
    (h2 : (l.drop (m + n)).all f = true) :
    (l.drop m).all f = true := by
  rw [← List.take_append_drop n (l.drop m), List.drop_drop, List.all_append, h1, h2]
  rfl

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
"""


def main():
    totals = counts()
    os.makedirs(os.path.join(OUT, "lean/Kepler/Graphs"), exist_ok=True)
    with open(os.path.join(OUT, "lean/Kepler/Graphs/ReshardDefs.lean"), "w",
              encoding="utf-8") as f:
        f.write(DEFS)
    summary = []
    for kind in KINDS:
        for cls in CLASSES:
            total = totals[(cls, kind)]
            sl = slice_size(cls, kind)
            k = max(1, -(-total // sl))
            if k > 1:
                for i in range(k):
                    n, body = shard_file(kind, cls, i, k, total)
                    with open(os.path.join(OUT, "lean/Kepler/Graphs", n + ".lean"), "w",
                              encoding="utf-8") as f:
                        f.write(body)
            n, body = combiner_file(kind, cls, k, total)
            with open(os.path.join(OUT, "lean/Kepler/Graphs", n + ".lean"), "w",
                      encoding="utf-8") as f:
                f.write(body)
            summary.append(f"{kind:11s} {cls:5s} items={total:5d} slice={sl:3d} shards={k}")
    print("\n".join(summary))
    print("files:", 1 + sum(max(1, -(-totals[(c, kd)] // slice_size(c, kd)))
                           + 1 for kd in KINDS for c in CLASSES))


if __name__ == "__main__":
    main()

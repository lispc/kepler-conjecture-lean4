#!/usr/bin/env python3
"""L1 探针（549 加速项目 Phase 0）——采样 cert 叶 → bb_arb --probe → 定号率统计.

Phase 0 三个探针里两个在此落地:
  探针 B: mono 定号率（盒上 ∃i: ∂ᵢf 区间不跨 0）→ L1 叶数削减上界
  探针 C: 叶宽深度直方图 → rung 分布 / 单叶成本模型
(探针 A: ite 普查已在 cases stats 层完成——全语料 0.26%, 风险撤销.)

用法:
  python3 probe_l1.py sample  <cert.json> <out_boxes.json> [--k=600] [--seed=42]
  python3 probe_l1.py analyze <probe_out.jsonl> [--report]
"""
import json
import math
import mmap
import random
import re
import sys
from collections import Counter

LEAF_PAT = re.compile(rb'(?<=\n    )\{"box"')


def frac_to_f(x):
    return int(x["num"]) / int(x["den"])


def sample_leaves(cert_path, out_path, k=600, seed=42):
    """字节偏移随机采样叶对象（674MB 不整读）."""
    with open(cert_path, "rb") as f:
        mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        starts = [m.start() for m in LEAF_PAT.finditer(mm)]
        total = len(starts)
        rng = random.Random(seed)
        picks = sorted(rng.sample(range(total), min(k, total)))
        dec = json.JSONDecoder()
        leaves = []
        for idx in picks:
            off = starts[idx]
            obj, _ = dec.raw_decode(mm[off:mm.size()].decode("utf-8", "replace"), 0)
            leaves.append(obj)
        mm.close()
    boxes = [l["box"] for l in leaves]
    json.dump({"boxes": boxes}, open(out_path, "w"))
    # 探针 C: 宽度 → 深度直方图（root 宽按 cert 首 leaf 维折算不可得，改用
    # 绝对 log2 宽度分布；rung-12 高阶叶特征 = 宽度 ~2^-12 量级）
    hist = Counter()
    for b in boxes:
        w = max(frac_to_f(d[1]) - frac_to_f(d[0]) for d in b)
        hist[int(math.floor(math.log2(w))) if w > 0 else -99] += 1
    print(f"[sample] 总叶 {total}  采样 {len(boxes)}  → {out_path}")
    print("[sample] max 维 log2 宽度直方图 (exp:count):")
    for e in sorted(hist):
        print(f"  2^{e:4d}: {hist[e]}")
    return total


def analyze(out_path, report=False):
    lines = [json.loads(l) for l in open(out_path) if l.startswith("{\"i\"")]
    meta = None
    for l in open(out_path):
        if l.startswith("{\"case\""):
            meta = json.loads(l)
            break
    n = len(lines)
    valid = [l for l in lines if l.get("valid")]
    inv = [l for l in lines if not l.get("valid")]
    print(f"[analyze] case={meta['case'] if meta else '?'}  n={n}  "
          f"TM valid={len(valid)} ({len(valid)/n:.1%})  invalid={len(inv)}")
    failc = Counter(l.get("fail") for l in inv)
    if failc:
        names = {1: "guard-INDET", 2: "guard跨0", 3: "div越零",
                 4: "abs跨0", 5: "sqrt/log底非正", 6: "未知"}
        print("[analyze] invalid 原因:",
              {names.get(k, k): v for k, v in sorted(failc.items())})
    # mono 定号率: ∂ᵢf ⊆ dfᵢ ± σᵢ; 定号 = 区间不跨 0
    nv = len(valid[0]["df"]) if valid else 0
    per_var_pos = [0] * nv
    per_var_neg = [0] * nv
    mono_boxes = 0
    mono_dir = Counter()
    closed_tm = sum(1 for l in valid if l.get("closed"))
    for l in valid:
        dirs = []
        for i in range(nv):
            lo, hi = l["df"][i]
            s = l["sig"][i]
            ilo, ihi = lo - s, hi + s
            if ilo > 0:
                per_var_pos[i] += 1
                dirs.append((i, +1))
            elif ihi < 0:
                per_var_neg[i] += 1
                dirs.append((i, -1))
        if dirs:
            mono_boxes += 1
            for d in dirs:
                mono_dir[d] += 1
    print(f"[analyze] closed-by-TM@原宽: {closed_tm}/{n} "
          f"({closed_tm/n:.1%})")
    print(f"[analyze] mono(∂ᵢf 定号, ∃i): {mono_boxes}/{len(valid)} "
          f"= {mono_boxes/max(len(valid),1):.1%} of valid, "
          f"{mono_boxes/n:.1%} of all")
    for i in range(nv):
        print(f"  var{i}: pos {per_var_pos[i]:4d}  neg {per_var_neg[i]:4d}"
              f"  → {per_var_pos[i]+per_var_neg[i]:4d}"
              f" ({(per_var_pos[i]+per_var_neg[i])/max(len(valid),1):.1%})")
    if report:
        top = mono_dir.most_common(6)
        print("[analyze] 最常定号 (var,dir):", top)
    return mono_boxes / max(n, 1)


if __name__ == "__main__":
    cmd = sys.argv[1]
    args = [a for a in sys.argv[2:] if not a.startswith("--")]
    opts = {}
    for a in sys.argv[2:]:
        if a.startswith("--") and "=" in a:
            k, v = a[2:].split("=", 1)
            opts[k] = v
    if cmd == "sample":
        sample_leaves(args[0], args[1],
                      k=int(opts.get("k", 600)), seed=int(opts.get("seed", 42)))
    elif cmd == "analyze":
        analyze(args[0], report=("--report" in sys.argv))
    else:
        sys.exit(__doc__)

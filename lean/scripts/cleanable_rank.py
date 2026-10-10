#!/usr/bin/env python3
"""cleanable_rank.py — 贪心触达排名器（census v3 管线第 3 段，PLAN §5 会师修订）

输入: /tmp/dep_edges.txt（dep_sweep.sh 产物，DEP\\tname\\ttaint\\tdeps(;分隔)）
模型: 有向图 G，节点=Kepler 常量；节点 tainted 当且仅当 collectAxioms 报 sorryAx。
      直接边 = 源码级 Kepler→Kepler 依赖（taint 沿边传播，可穿净节点）。
cleanable(L): 假设 L 被神奇证毕，不动点传播——M 变净 ⟺ M 的全部 tainted
      直接依赖已净；数出连带变净的 tainted 常量总数（含 L）。
输出: 按单叶连带收益降序的排名表（top N），附模块分布。
"""
import sys
from collections import defaultdict

EDGE_FILE = sys.argv[1] if len(sys.argv) > 1 else "/tmp/dep_edges.txt"
TOP_N = int(sys.argv[2]) if len(sys.argv) > 2 else 30

deps = defaultdict(set)   # node -> set(direct kepler deps)
tainted = set()
nodes = set()
cur_mod = None

def fix(n, mod):
    """块内 _stdin 私有名重写回真实模块名(_private._stdin.0.X → _private.<mod>.0.X)"""
    if mod and n.startswith("_private._stdin.0."):
        return "_private." + mod + ".0." + n[len("_private._stdin.0."):]
    return n

for line in open(EDGE_FILE, encoding="utf-8"):
    if line.startswith("SCAN_MODULE "):
        cur_mod = line.split(None, 1)[1].strip()
        continue
    if not line.startswith("DEP\t"):
        continue
    _, name, t, d = line.rstrip("\n").split("\t")
    name = fix(name, cur_mod)
    ds = set(fix(x, cur_mod) for x in d.split(";") if x)
    deps[name] = ds
    nodes.add(name)
    if t == "1":
        tainted.add(name)

# 自验证: 从字面 taint 沿边做闭包, 应与 collectAxioms 的 taint 标志一致
closure = set(x for x in nodes if x in tainted and not deps[x])
changed = True
while changed:
    changed = False
    for m in nodes:
        if m in closure:
            continue
        if deps[m] & closure:
            closure.add(m)
            changed = True
reported_taint = set(x for x in nodes if x in tainted)
mismatch_c = len(reported_taint - closure)   # collectAxioms 报 tainted 但闭包推不出 → 缺边(跨模块漏扫)
print(f"nodes={len(nodes)} tainted(collectAxioms)={len(reported_taint)} "
      f"closure-from-leaves={len(closure)} missing_edges={mismatch_c}")

def cleanable(leaf, tainted):
    T = tainted - {leaf}
    removed = 1  # leaf 本身
    changed = True
    while changed:
        changed = False
        for m in list(T):
            if not (tdeps[m] & T):
                T.discard(m)
                removed += 1
                changed = True
    return removed

# taint 子图内边（模拟只在 tainted 节点集上跑）
tdeps = {m: (deps[m] & tainted) for m in tainted}
# 候选 = taint 子图真叶（无 tainted 直接依赖的 tainted 节点）
cands = sorted(x for x in tainted if not tdeps[x])
print(f"candidates(taint-leaves)={len(cands)}")
rows = []
for i, L in enumerate(cands):
    rows.append((cleanable(L, tainted), L))
    if (i + 1) % 50 == 0:
        print(f"  ...ranked {i+1}/{len(cands)}", file=sys.stderr)
rows.sort(reverse=True)
print("\n=== TOP by single-leaf upward-clean (cleanable\\tmodule\\tname) ===")
for k, (c, L) in enumerate(rows[:TOP_N], 1):
    mod = ".".join(L.split(".")[:-1])
    print(f"{k}\t{c}\t{mod}\t{L}")

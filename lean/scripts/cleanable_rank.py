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

# taint 子图内边（模拟只在 tainted 节点集上跑）
tdeps = {m: (deps[m] & tainted) for m in tainted}
# 两类 tainted: 字面 sorry 叶(tdeps 空, sorryAx 直接在体内, 不产生常量依赖边)
# vs 依赖型 tainted(taint 来自被消费的 tainted 常量)。只有后者可被传播清除;
# 字面叶是永久债, 除非它自己就是被填的 L。
leaves = set(x for x in tainted if not tdeps[x])
dep_tainted = tainted - leaves

# 自验证: 从全部字面叶沿依赖边传播, 应覆盖全部 tainted
closure = set(leaves)
changed = True
while changed:
    changed = False
    for m in dep_tainted:
        if m not in closure and (tdeps[m] & closure):
            closure.add(m)
            changed = True
missing = len(tainted - closure)
print(f"nodes={len(nodes)} tainted={len(tainted)} literal-leaves={len(leaves)} "
      f"dep-tainted={len(dep_tainted)} closure={len(closure)} missing_edges={missing}")

def cleanable(leaf):
    """假设 leaf 证毕(变净), 依赖型 tainted 按『全部 tainted 依赖已净』传播清除
    (工作表+反向边+计数器, 只触可达); 其它字面叶保持 tainted。含 leaf 本身。"""
    cnt = {m: len(tdeps[m] & dep_tainted) for m in dep_tainted}
    leafdep = {m: bool(tdeps[m] & leaves) for m in dep_tainted}
    from collections import deque
    q = deque([leaf])
    removed = 1
    while q:
        x = q.popleft()
        for m in rdeps.get(x, ()):  # 消费者
            if m == leaf or m not in dep_tainted:
                continue
            cnt[m] -= 1
            if cnt[m] == 0 and not leafdep[m]:
                removed += 1
                q.append(m)
    return removed

# 反向边(仅 dep_tainted 消费者)
rdeps = defaultdict(set)
for m in dep_tainted:
    for d in tdeps[m]:
        rdeps[d].add(m)

# 候选 = 全部 tainted(字面叶可直接填; 依赖型 tainted 的"填证"= 直接证它,
# 绕过其上游——同样合法的派工对象)
cands = sorted(tainted)
print(f"candidates(taint-leaves)={len(cands)}")
rows = []
for i, L in enumerate(cands):
    rows.append((cleanable(L), L))
    if (i + 1) % 50 == 0:
        print(f"  ...ranked {i+1}/{len(cands)}", file=sys.stderr)
rows.sort(reverse=True)
print("\n=== TOP by single-leaf upward-clean (cleanable\\tmodule\\tname) ===")
for k, (c, L) in enumerate(rows[:TOP_N], 1):
    mod = ".".join(L.split(".")[:-1])
    print(f"{k}\t{c}\t{mod}\t{L}")

#!/usr/bin/env python3
"""
Phase 4 92-prep 族成分画像 — 分类器
对 /tmp/p4wave1/ineqs_prep_ast.json 的 812 条 prep 记录做表达式 AST 节点类型分类。

分类规则（从 FormalVerifier.tex 支持的函数集出发：sqrt/atn/acs/pi）：
  特征旗标（递归展开 defs.json 函数体后收集）：
    sqrt   : 表达式含 sqrt 节点（含 via 函数体展开）
    atnacs : 含 atn/atn2/acs 节点
    ite    : 含 if/cond 分支或 abs（guard 类）
    otherf : 其他超越原语（asn/sin/cos/log/exp/azim 等，异常标注）
    unknown: 展开遇到的未解析 app（名单另列）
  记录类别 = 旗标集合：
    {}                 -> poly     （纯多项式/有理；pi 常数与 / 除法不排除）
    {sqrt}             -> sqrt
    {atnacs}           -> atn-acs
    {ite}              -> ite
    >=2 类             -> mixed
输出 /tmp/p4profile/records_classified.json（逐记录）与摘要打印。
确定性脚本：数据只读，无 API 调用。
"""
import json
import re
import sys
from collections import Counter

PREP = "/tmp/p4wave1/ineqs_prep_ast.json"
DEFS = "/Users/zhangzhuo/repos/kepler-conjecture-lean4/pipeline/interval/out/defs.json"
OUT = "/tmp/p4profile/records_classified.json"

SQRT_PRIMS = {"sqrt"}
ATNACS_PRIMS = {"atn", "atn2", "acs"}
ITE_PRIMS = {"abs"}          # abs = ite(x<0, --x, x)，按任务口径归 guard
OTHER_PRIMS = {"asn", "sin", "cos", "tan", "ln", "log", "exp", "azim", "inv", "sgn", "dist", "norm"}

def load_defs():
    d = json.load(open(DEFS))
    return {k: v.get("body_ast") for k, v in d.items()}

def make_feature_walker(defs):
    """返回 walk(node, flags, unknown, depth)：递归收集特征旗标。
    flags: set in {'sqrt','atnacs','ite','otherf'}; unknown: set of unresolved app names."""
    memo = {}   # defname -> its own flag set (structural, args-independent)
    unknown_global = Counter()

    def prim_flags(name):
        f = set()
        if name in SQRT_PRIMS: f.add("sqrt")
        elif name in ATNACS_PRIMS: f.add("atnacs")
        elif name in ITE_PRIMS: f.add("ite")
        elif name in OTHER_PRIMS: f.add("otherf")
        return f

    def walk(n, flags, unknown, depth=0):
        if depth > 60:
            return
        if isinstance(n, dict):
            if "op" in n:
                for v in n.get("args", []):
                    walk(v, flags, unknown, depth + 1)
                return
            if "app" in n:
                name = n["app"]
                if name in defs:
                    if name in memo:
                        flags |= memo[name]
                    else:
                        memo[name] = set()  # 占位防环
                        sub = set()
                        walk(defs[name], sub, unknown, depth + 1)
                        memo[name] = sub
                        flags |= sub
                else:
                    f = prim_flags(name)
                    if f:
                        flags |= f
                    else:
                        unknown.add(name)
                        unknown_global[name] += 1
                for v in n.get("args", []):
                    walk(v, flags, unknown, depth + 1)
                return
            if "if" in n:   # {'if': cond, 'then':..., 'else':...} 或嵌套
                flags.add("ite")
                for k in ("if", "cond", "then", "else"):
                    if k in n:
                        walk(n[k], flags, unknown, depth + 1)
                return
            if "let" in n:
                let = n["let"]
                walk(let.get("val"), flags, unknown, depth + 1)
                walk(let.get("body"), flags, unknown, depth + 1)
                return
            if "lambda" in n:
                lam = n["lambda"]
                if isinstance(lam, dict):
                    for v in lam.values():
                        walk(v, flags, unknown, depth + 1)
                return
            for v in n.values():
                walk(v, flags, unknown, depth + 1)
            return
        if isinstance(n, list):
            for v in n:
                walk(v, flags, unknown, depth + 1)

    return walk, unknown_global

# pi 常数与除法：poly 类允许（有理含 pi 常数系数）。
# 记录级 '\/'（析取）算 guard 吗？——R2 定义是 ite/guard；析取是顶层布尔结构
# 而非表达式内部 guard。单独记 'disj' 旗标供报告，不并入类别判定。
def classify(flags):
    core = flags & {"sqrt", "atnacs", "ite"}
    if not core: return "poly"
    if len(core) == 1: return {"sqrt": "sqrt", "atnacs": "atn-acs", "ite": "ite"}[next(iter(core))]
    return "mixed"

def main():
    defs = load_defs()
    walk, unknown_global = make_feature_walker(defs)
    recs = json.load(open(PREP))["records"]
    out = []
    for r in recs:
        fam = r["idv"][len("prep-"):].strip().split()[0]
        flags, unknown = set(), set()
        walk(r["body_ast"], flags, unknown)
        cls = classify(flags)
        out.append({
            "idv": r["idv"], "family": fam, "line": r["line"],
            "class": cls,
            "flags": sorted(flags),
            "disj": "\\/" in json.dumps(r["body_ast"]) or True and any(
                isinstance(n, dict) and n.get("op") == "\\/" for n in [r["body_ast"]]) or False,
            "unknown_apps": sorted(unknown),
            "nvars": len(r["bounds"]),
        })
    # disj 旗标单独扫一遍（顶层布尔析取）
    def has_disj(n):
        if isinstance(n, dict):
            if n.get("op") == "\\/": return True
            return any(has_disj(v) for v in n.values())
        if isinstance(n, list):
            return any(has_disj(v) for v in n)
        return False
    for o, r in zip(out, recs):
        o["disj"] = has_disj(r["body_ast"])

    json.dump(out, open(OUT, "w"), ensure_ascii=False, indent=1)

    # 摘要
    cc = Counter(o["class"] for o in out)
    print("== 记录类别分布 (812) ==")
    for k in ["poly", "ite", "sqrt", "atn-acs", "mixed"]:
        print(f"  {k:8s} {cc.get(k,0):4d}  ({cc.get(k,0)/len(out)*100:.1f}%)")
    fc = Counter(tuple(sorted(o["flags"])) for o in out)
    print("== 旗标组合 ==")
    for k, v in fc.most_common():
        print(f"  {','.join(k) or '(none)':24s} {v:4d}")
    print("== 未解析 app（展开中遇到）==")
    for k, v in unknown_global.most_common(20):
        print(f"  {k}: {v}")
    disj = sum(1 for o in out if o["disj"])
    print(f"含顶层析取 \\/ 的记录: {disj}")

if __name__ == "__main__":
    main()

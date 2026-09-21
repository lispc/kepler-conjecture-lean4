#!/usr/bin/env python3
"""orig_tree_probe.py — 导入 Flyspeck 原始分割树, 把叶盒喂给 pinned-rung 判定。

用法:
  orig_tree_probe.py parse  <idv>           # 解析 break_case_log 树 → 叶盒 JSON
  orig_tree_probe.py driver <case.json> <leafbox.json> <name>  # 生成驱动+boxes.txt

背景: break_case_log.hl 的 Iarg_facet ((i,side),frac,msec,sub) 语义
(break_case_exec.hl mk_rec / 头部注释):
  side=false: cut=lo+frac·(hi−lo), 左半 [lo,cut] 是已验证叶, 递归右半
  side=true : cut=lo+(1−frac)·(hi−lo), 右半 [cut,hi] 是已验证叶, 递归左半
  Iarg_leaf n: 当前域为最后一个叶。msec 是 C++ 运行时(毫秒), 与盒无关。
原始域: prep.hl 条目 ineq bounds, hminus 按 1.26 常数计(与 split 边界
(2·1.26)²=6.3504 一致); x 空间为平方变量(xi = yi²)。
嵌入: 我们的 case 是 7 维(hminus∈[6/5,13/10] 为 dim0)+ 外扩盒; 原始 6 维
叶盒嵌入为 dim0 全区间 × 叶盒, 端点外扩到 2^-30 dyadic 网格。
"""
import json
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
G4E = os.path.dirname(os.path.dirname(HERE))
MAIN = "/home/scroll/repos/kepler-conjecture-lean4"
BREAK_LOG = os.path.join(MAIN, "reference/flyspeck/text_formalization/nonlinear/break_case_log.hl")
OUT_DIR = os.path.join(HERE, "out", "orig_tree")

HMINUS = Fraction(126, 100)  # 原始验证语义: hminus 是 choice 常数, split 边界用 1.26
Q30 = 1 << 30


def f2(x):
    """#1.3254 风格十进制 → Fraction"""
    return Fraction(x)


# ---------- 原始域(prep.hl bounds, hminus=1.26) ----------
def orig_domain(idv):
    hm2 = (2 * HMINUS) ** 2          # (2·1.26)² = 6.3504
    hp2 = (2 * Fraction(13254, 10000)) ** 2  # (2·1.3254)² = 7.02667...
    if idv.endswith("split(1/2)"):
        # [hp? no: x1∈[(2·1.26)²,(2·1.3254)²], x4∈[(2·1.3254)²,8], 其余 [4,(2hminus)²]
        return [[hm2, hp2], [Fraction(4), hm2], [Fraction(4), hm2],
                [hp2, Fraction(8)], [Fraction(4), hm2], [Fraction(4), hm2]]
    if idv.endswith("split(0/2)"):
        # x1∈[(2hminus)²,(2·1.26)²]: hminus 取域 lo=1.2 → 5.76(与 case 盒一致)
        lo1 = (2 * Fraction(12, 10)) ** 2
        return [[lo1, hm2], [Fraction(4), hm2], [Fraction(4), hm2],
                [hp2, Fraction(8)], [Fraction(4), hm2], [Fraction(4), hm2]]
    raise ValueError(idv)


# ---------- break_case_log 树解析 ----------
def extract_tree(idv):
    raw = open(BREAK_LOG, encoding="utf-8", errors="replace").read()
    i = raw.find(f'add_case ("{idv}"')
    if i < 0:
        return None
    j = raw.index("Iarg_", i)
    # 平衡括号截取到 ";;"
    k = raw.index(";;", j)
    return raw[j:k].strip()


def parse_tree(s):
    s = s.strip()
    if s.startswith("Iarg_leaf"):
        m = re.match(r"Iarg_leaf\s+(\d+)", s)
        return ("leaf", int(m.group(1)))
    if s.startswith("Iarg_bisect"):
        m = re.match(r"Iarg_bisect\s*\(\s*(\d+)\s*,", s)
        i = int(m.group(1))
        a, b = split_two(s[m.end():])
        return ("bisect", i, parse_tree(a), parse_tree(b))
    m = re.match(r"Iarg_facet\s*\(\s*\(\s*(\d+)\s*,\s*(true|false)\s*\)\s*,\s*([0-9.]+)\s*,\s*(\d+)\s*,", s)
    if not m:
        raise ValueError("bad tree node: " + s[:80])
    i, side, frac, msec = int(m.group(1)), m.group(2) == "true", Fraction(m.group(3)), int(m.group(4))
    sub = s[m.end():].strip()
    assert sub.endswith(")"), sub[-20:]
    return ("facet", i, side, frac, msec, parse_tree(sub[:-1]))


def split_two(s):
    """bisect 的两个子树(顶层逗号分割)"""
    depth = 0
    for k, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced")
        elif ch == "," and depth == 0:
            return s[:k], s[k + 1:s.rindex(")")]
    raise ValueError("no top comma")


def expand(tree, domain):
    """mk_rec 语义展开 → [(box6, msec|None)]"""
    leaves = []

    def rec(dom, t):
        if t[0] == "leaf":
            leaves.append((dom, t[1]))
            return
        if t[0] == "bisect":
            _, i, a, b = t
            lo, hi = dom[i]
            mid = (lo + hi) / 2
            rec(dom[:i] + [[lo, mid]] + dom[i + 1:], a)
            rec(dom[:i] + [[mid, hi]] + dom[i + 1:], b)
            return
        _, i, side, frac, msec, sub = t
        lo, hi = dom[i]
        if side:  # true: 右半是叶, 递归左半
            cut = lo + (1 - frac) * (hi - lo)
            leaves.append((dom[:i] + [[cut, hi]] + dom[i + 1:], msec))
            rec(dom[:i] + [[lo, cut]] + dom[i + 1:], sub)
        else:     # false: 左半是叶, 递归右半
            cut = lo + frac * (hi - lo)
            leaves.append((dom[:i] + [[lo, cut]] + dom[i + 1:], msec))
            rec(dom[:i] + [[cut, hi]] + dom[i + 1:], sub)

    rec(domain, tree)
    return leaves


# ---------- dyadic 外扩 + 7 维嵌入 ----------
def dy_out(fr, is_lo):
    """向外取整到 2^-30 网格, 返回 (m, e)"""
    v = fr * Q30
    m = v.numerator // v.denominator if is_lo else -(-v.numerator // v.denominator)
    return (m, -30)


def embed7(box6, hminus_iv):
    full = [hminus_iv] + box6
    out = []
    for lo, hi in full:
        out.append((dy_out(lo, True), dy_out(hi, False)))
    return out


def boxes_txt_line(box7):
    return " ".join(f"{lo[0]} {lo[1]} {hi[0]} {hi[1]}" for lo, hi in box7)


def cmd_parse(idv):
    s = extract_tree(idv)
    dom = orig_domain(idv)
    if s is None:
        leaves = [(dom, None)]
        print(f"parse: {idv}: break_case_log 无条目 → 单叶(全域)")
    else:
        leaves = expand(parse_tree(s), dom)
        print(f"parse: {idv}: {len(leaves)} 叶")
    os.makedirs(OUT_DIR, exist_ok=True)
    tag = re.sub(r"[^A-Za-z0-9]+", "_", idv).strip("_")
    out = {"idv": idv, "domain": [[[str(lo), str(hi)] for lo, hi in dom]],
           "leaves": [[[str(lo), str(hi)] for lo, hi in b] for b, _ in leaves],
           "msec": [m for _, m in leaves]}
    p = os.path.join(OUT_DIR, tag + ".leaves.json")
    json.dump(out, open(p, "w"), indent=1)
    for k, (b, m) in enumerate(leaves):
        print(f"  leaf {k} (msec={m}): " + ", ".join(f"x{d+1}∈[{float(lo):.4f},{float(hi):.4f}]" for d, (lo, hi) in enumerate(b)))
    print("wrote", p)


def cmd_driver(case_path, leafbox_path, name):
    sys.path.insert(0, HERE)
    import emit_lean as E
    case = json.load(open(case_path))
    lb = json.load(open(leafbox_path))
    n = len(case["vars"])
    leaves6 = [[[Fraction(lo), Fraction(hi)] for lo, hi in b] for b in lb["leaves"]]
    hminus_iv = [Fraction(case["box"][0][0]["num"], case["box"][0][0]["den"]),
                 Fraction(case["box"][0][1]["num"], case["box"][0][1]["den"])]
    boxes7 = [embed7(b, hminus_iv) for b in leaves6]
    d = os.path.join(OUT_DIR, name + ".d")
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "boxes.txt"), "w") as f:
        for b in boxes7:
            f.write(boxes_txt_line(b) + "\n")
    mkexprs, terms, goals = E.fill_goals(case)
    drv = E.stage_a_driver_disj(n, mkexprs, terms)
    open(os.path.join(d, "driver.lean"), "w").write(
        drv.format(caseid=case["id"], origop="", vars="", nleaves=len(boxes7),
                   prec=None, extra=""))
    json.dump({"goals": goals}, open(os.path.join(d, "goals.json"), "w"))
    print(f"driver: wrote {d}/ (driver.lean + boxes.txt, {len(boxes7)} leaves, "
          f"{len(mkexprs)} pos goals)")


if __name__ == "__main__":
    if sys.argv[1] == "parse":
        cmd_parse(sys.argv[2])
    elif sys.argv[1] == "driver":
        cmd_driver(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        sys.exit(__doc__)

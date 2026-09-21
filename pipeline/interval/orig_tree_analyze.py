#!/usr/bin/env python3
"""analyze_probe.py — 解析探针 run.log, 报告 PASS/FAIL 与 FAIL 叶边界贴合特征。

用法: analyze_probe.py <name>
读 out/orig_tree/<name>.run.log + <name>.d/boxes.txt + 对应 leaves.json。
"""
import json
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out", "orig_tree")


def main(name):
    log = open(os.path.join(OUT, name + ".run.log")).read()
    base = re.sub(r"^probe", "prep_BIXPCGW_", name)  # probe7274157868s1 -> prep_BIXPCGW_7274157868s1
    base = re.sub(r"s([01])$", r"_a_split_\1_2", base)
    tag = base
    lb = json.load(open(os.path.join(OUT, tag + ".leaves.json")))
    domain = [(Fraction(a), Fraction(b)) for a, b in lb["domain"][0]]
    goals = json.load(open(os.path.join(OUT, name + ".d", "goals.json")))["goals"]
    verdicts = {}
    for ln in log.splitlines():
        p = ln.split()
        if len(p) >= 2 and p[0].isdigit() and p[1] in ("PASS", "PASSV", "FAIL"):
            verdicts[int(p[0])] = (p[1], p[2] if len(p) > 2 else None)
    m = re.search(r"rung N=(\d+) out=(-?\d+): (\d+)/(\d+) failures", log)
    if m:
        print(f"rung N={m.group(1)} out={m.group(2)}: {m.group(3)}/{m.group(4)} failures")
    glabel = {g["index"]: g["label"] for g in goals}
    npass = sum(1 for v in verdicts.values() if v[0] in ("PASS", "PASSV"))
    print(f"leaves: {len(lb['leaves'])}, judged: {len(verdicts)}, "
          f"PASS: {npass}, FAIL: {len(verdicts) - npass}")
    for i, (box, msec) in enumerate(zip(lb["leaves"], lb["msec"])):
        v = verdicts.get(i, ("?", None))
        hit = glabel.get(int(v[1]), v[1]) if v[1] is not None and str(v[1]).isdigit() else v[1]
        line = f"leaf {i} (msec={msec}): {v[0]}" + (f" hit={hit}" if hit else "")
        if v[0] == "FAIL":
            touch = []
            for d, (lo, hi) in enumerate(box):
                lo, hi = Fraction(lo), Fraction(hi)
                if lo == domain[d][0]:
                    touch.append(f"x{d+1}=lo({float(lo):.4f})")
                if hi == domain[d][1]:
                    touch.append(f"x{d+1}=hi({float(hi):.4f})")
            line += "  贴边界: " + (", ".join(touch) if touch else "无(内部叶)")
        print(" ", line)


if __name__ == "__main__":
    main(sys.argv[1])

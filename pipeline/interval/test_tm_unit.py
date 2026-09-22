#!/usr/bin/env python3
"""TM1 单元验收（任务书验收 a）：已知解析导数的小函数，TM 区间界 vs 真实值域。

判定：
  1. 包住：loBound <= 真 min，hiBound >= 真 max（容差 1e-9）；
  2. 过估 O(w^2)：过估量 ov = (hiBound-loBound) - (max-min) 随盒宽减半
     比值 ≈ 4（f1/f2，Hessian 余项主导），≈ 8（f3 = x - sin x，一阶项
     在中心恰好为 0，余项 O(w^3) 主导）。
  3. 驱动级：f4 > 0 的盒根叶一步 TM 闭合（hit "tm"）。

用法：python3 test_tm_unit.py   （在 pipeline/interval/ 下运行）
输出案例 JSON 到 out/tm_c/。
"""
import json
import math
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BB = os.path.join(HERE, "bb_arb")
OUT = os.path.join(HERE, "out", "tm_c")
os.makedirs(OUT, exist_ok=True)

TOL = 1e-9


def rat(num, den=1):
    return {"num": num, "den": den}


def write_case(cid, vars_, box, prog):
    """box: [(lo_num, hi_num, den), ...]（dyadic）"""
    d = {
        "id": cid,
        "orig_op": ">",
        "vars": vars_,
        "box": [[rat(lo, den), rat(hi, den)] for lo, hi, den in box],
        "q": -30,
        "prog": prog,
    }
    p = os.path.join(OUT, cid + ".json")
    with open(p, "w") as f:
        json.dump(d, f)
    return p


def tm_debug(path):
    r = subprocess.run([BB, path, "--tm-debug"], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"bb_arb 退出码 {r.returncode}: {r.stderr[:400]}")
    lo = hi = None
    for line in r.stdout.splitlines():
        if "INVALID" in line:
            raise RuntimeError(f"TM 不可用: {line}")
        if line.startswith("[tm] loBound="):
            lo = float(line.split()[1].split("=")[1])
            hi = float(line.split()[2].split("=")[1])
    if lo is None:
        raise RuntimeError(f"无 loBound 输出: {r.stdout[:400]}")
    return lo, hi


def check(name, prog, nvars, dens, box_of, trange, ratio_lo, ratio_hi):
    """dens: 分母列表（盒宽 ~1/den）；box_of(den) -> [(lo_num, hi_num, den), ...]；
    trange(float_box) -> (true_min, true_max)。"""
    ovs = []
    for den in dens:
        box = box_of(den)
        path = write_case(f"tm_unit_{name}_{den}", ["x", "y"][:nvars], box, prog)
        lo, hi = tm_debug(path)
        fb = [(a / d, b / d) for a, b, d in box]
        tmin, tmax = trange(fb)
        assert lo <= tmin + TOL, f"{name} den={den}: loBound {lo} > 真min {tmin}"
        assert hi >= tmax - TOL, f"{name} den={den}: hiBound {hi} < 真max {tmax}"
        ov = (hi - lo) - (tmax - tmin)
        assert ov > -TOL, f"{name} den={den}: 过估为负 {ov}"
        ovs.append(ov)
        print(f"  [{name}] w=1/{den}: TM=[{lo:.10f},{hi:.10f}] "
              f"真=[{tmin:.10f},{tmax:.10f}] 过估={ov:.3e}")
    for i in range(len(ovs) - 1):
        r = ovs[i] / ovs[i + 1]
        assert ratio_lo <= r <= ratio_hi, (
            f"{name}: 过估比 {r:.2f} 不在 [{ratio_lo},{ratio_hi}]（O(w²) 期望 ~4）")
        print(f"  [{name}] 过估比 {ovs[i]:.3e}/{ovs[i+1]:.3e} = {r:.2f}  OK")


def main():
    # f1 = x^2 + sqrt(y+1) - 3，盒 [1,1+1/den]x[0,1/den]；两维单调增
    prog1 = [["push_var", 0], ["push_var", 0], ["mul"],
             ["push_var", 1], ["push_const", rat(1)], ["add"], ["sqrt"],
             ["add"], ["push_const", rat(3)], ["sub"]]
    check("f1_x2+sqrt-3", prog1, 2, [16, 32, 64],
          lambda d: [(d, d + 1, d), (0, 1, d)],
          lambda b: (b[0][0] ** 2 + math.sqrt(b[1][0] + 1) - 3,
                     b[0][1] ** 2 + math.sqrt(b[1][1] + 1) - 3),
          2.5, 6.5)

    # f2 = atan(x*y) + x/(y+2) - sin(y)，盒 [1/2,1/2+1/den]x[1/4,1/4+1/den]；
    # x 增、y 减 -> min 在 (x_lo,y_hi)，max 在 (x_hi,y_lo)
    prog2 = [["push_var", 0], ["push_var", 1], ["mul"], ["atan"],
             ["push_var", 0], ["push_var", 1], ["push_const", rat(2)],
             ["add"], ["div"], ["add"],
             ["push_var", 1], ["sin"], ["sub"]]

    def f2(x, y):
        return math.atan(x * y) + x / (y + 2) - math.sin(y)

    check("f2_atan+div-sin", prog2, 2, [32, 64, 128],
          lambda d: [(d // 2, d // 2 + 1, d), (d // 4, d // 4 + 1, d)],
          lambda b: (f2(b[0][0], b[1][1]), f2(b[0][1], b[1][0])),
          2.5, 6.5)

    # f3 = x - sin(x)，盒 [-1/den, 1/den]（一元）；真值域 [f(-w), f(w)]
    prog3 = [["push_var", 0], ["push_var", 0], ["sin"], ["sub"]]
    check("f3_x-sinx", prog3, 1, [16, 32, 64],
          lambda d: [(-1, 1, d)],
          lambda b: (b[0][0] - math.sin(b[0][0]), b[0][1] - math.sin(b[0][1])),
          5.0, 12.0)

    # f4 = x^2 + sqrt(y+1) - 1 > 0（min=1）：驱动级根叶 TM 一步闭合
    prog4 = [["push_var", 0], ["push_var", 0], ["mul"],
             ["push_var", 1], ["push_const", rat(1)], ["add"], ["sqrt"],
             ["add"], ["push_const", rat(1)], ["sub"]]
    p4 = write_case("tm_unit_f4_close", ["x", "y"],
                    [(1 * 16, 17, 16), (0, 1, 16)], prog4)
    cert = os.path.join(OUT, "tm_unit_f4_close.cert.json")
    r = subprocess.run([BB, p4, "--tm", "--cert", cert],
                       capture_output=True, text=True)
    assert r.returncode == 0, f"f4 未闭合: {r.stdout} {r.stderr}"
    assert "closed=1" in r.stdout and "nodes=1" in r.stdout, r.stdout
    with open(cert) as f:
        cj = json.load(f)
    assert cj["leaves"][0]["hit"] == "tm", cj["leaves"][0]
    print("  [f4] 根叶一步 TM 闭合，cert hit=\"tm\"  OK")

    print("TM 单元验收全部通过")


if __name__ == "__main__":
    sys.exit(main())

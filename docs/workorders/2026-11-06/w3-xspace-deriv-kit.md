# WORK ORDER — `xspace-deriv-kit`（用户已批：x-空间导数包络，600–1,200 行）

> 状态：**用户 2026-11-06 已批准**（"3. 做吧"）。
> 前置必读：`~/c17_backup/lane_snapshots/nli-banks-close/`（三个角点值已证、六轴单调性缺什么）。

## 0. 一句话

三条银行的**角点值都已证**，卡的全是**六轴单调性**；而 `Gamma4Deriv3..8` 只覆盖 **y-空间**
（`y = x²` 之后的变量），需要的是 **x-空间**（对 `xᵢ` 求导）。全树对
`HasDerivAt … matan / solEulerXDivSqrtdelta / dihXDivSqrtdeltaPosbranch / ldih…` **0 条命中**。

## 1. 目标（三条，按顺序）

| # | 银行 | 已证 | 还缺 |
|---|---|---|---|
| T1 | `nliTskGXSA`（`Assembly:913`） | `0 < gxsaMain 7.84 4 4 7.84 4 4`（下界 0.00462094，真值 4.8582751e−3） | 6 轴单调性（x-空间） |
| T2 | `nliCell3QZECFICwt0sqrt8`（`Assembly:389`） | `0 < c3Main (2hplus) 2 2` ≥ 0.00280684（真值 3.7446884e−3）；kernel 已降到 y4/y5/y6 三维（`mk456`） | 同（且变元在盒内**变号**：`Δ ∈ [−34.24,+13.68]`） |
| T3 | `nliCell3QZECFICwt0corner`（`Assembly:383`） | 顶点值**精确为 0**（dps=90 → 7.7e−93） | **不是**常数精度问题：需要顶点**精确恒等式** + 零值顶点的单调性；`mm1/mm2` 收到 1e−9 也不够（带只缩到 ±2.4e−10） |

## 2. 要建什么（x-空间 kit）

1. `matan`（`= atan` 包装）的 **x-空间导数**，且要缝三支：
   `t < 0 / t = 0 / t > 0`（因为 `Δ` 在 T2 的盒里跨零，`arcV/atan` 的变元变号）。
2. `solEulerXDivSqrtdelta` / `dihXDivSqrtdeltaPosbranch` / `ldih…` 的 `HasDerivAt`（x-空间）。
3. 把 6 条 `∂main/∂xᵢ` 的符号在各自盒上**认证**（区间算术 + 显式余项界，或单调性传递）。
4. 逐轴走到角点（`NliBanks11` 的 `nb11_corner_walk` / `nb11_box_update` 已是引擎，复用）。

**已有的可复用资产**：`NliBanks10/11`（866 行：`nb10_arctan_le_self` / `nb10_arctan_ge_sub` /
`nb10_matan_ge/le_one` / `nb10_solEuler_le` / `nb10_dihDiv_ge` / `corner_walk` / `box_update`）、
`Gamma4Val*`（值链）、`Gamma4Concave`（`volY` 二阶导闭式）、`Gamma4WideKink`（折点两支）。

## 3. 硬纪律

- 主仓 tracked 零改动；`/tmp/xskit/` 工作；产物 → `~/c17_backup/lane_snapshots/xspace-deriv-kit/`。
- 只跑独立 `nice -n 19 lake env lean <单文件>`；并发 ≤3；禁 `lake build`/`auto_gate.sh`/`git commit`。
- 新模块从 `NliBanks12.lean` 起（≤450 行/文件），**必须 `-o`**；每件 `#print axioms`。
- 禁 `axiom`/`sorry`/`admit`/`native_decide`；不许改既有陈述。
- **符号判定必须认证**（区间/闭式）；内点采样只能当 hint——这条已翻车四次。
- 每完成一条银行就存可编译中间态快照，别整波推倒。

## 4. 交付

`~/c17_backup/lane_snapshots/xspace-deriv-kit/{*.lean,patch.diff,DELIVERY.md,Evidence.md,logs/}`。
回我 ≤15 行：T1/T2/T3 逐项 DONE/GAP、六轴符号与关键界值、kit 的行数与件数、axioms、
`sorry` 净变化、以及一句「剩下 47 条里有没有被这套 kit 顺带解锁的」。

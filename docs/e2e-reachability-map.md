# 主定理 e2e 可达性地图（2026-10-22 生成）

> 根 = `Kepler.Assembly.the_kepler_conjecture_from_interfaces`（即
> `Kepler.Final.the_kepler_conjecture_e2e` 的直接证明项）。
> 方法 = Lean proof-term 常量遍历（`lean/scripts/e2e_reach_map.lean`），
> 只跟踪 `Kepler.*` / `_private.Kepler.*`，统计：
> ①可达 Kepler 声明；②值里**直接**含 `sorryAx` 的声明（债务源）；
> ③可达 Kepler 公理；④每个债务源的第一个 BFS 父声明。
> 原始 TSV：[`docs/e2e-reachability-map.tsv`](e2e-reachability-map.tsv)。

## 0. 头版

| 指标 | 数值 |
|---|---:|
| 可达 Kepler 声明 | **8,305** |
| 直接 sorryAx 债务源 | **149** |
| 可达 Kepler 公理 | **624**（全部 `native_decide`，与 DEBT 脊柱探针 624 完全一致） |

**结论：主定理当前的实际债务源是 149 个声明，不是“3 个接口”。** 3 个接口是
顶层归因；149 个 direct sorry 源分布在 Assembly（83）、PA25（39）、TameLp（6）、
PA15（3）、PA11（3）、PA21/PA18/PA14/PA13（各 2）、PA7/PA3/PA2/PA10/
LocalAuto16/LocalAuto1/ContraFan（各 1）。

## 1. 债务源按模块

| 模块 | direct sorry 源 | 代表声明 |
|---|---:|---|
| `Kepler.Assembly` | 83 | 79 个 `nli*`（59 个父为 `nliPackNonlinearRest`、8 个 `nliTskBank`、7 个 `nliCell3Bank`、5 个直挂 `nonlinearInequalities`）+ `fcdjdot` / `jcajydu` / `tameCorrespondenceIso`（父 `textCapstone`）+ `lpArchiveCertificatesDebt`（父 `lpArchiveCertificates`） |
| `Kepler.Text.PackingAuto25` | 39 | 25 个 `real_model_*`（父 `pkrmQu/Qx/Qy` 等）+ `LEAF_RANK_PROPS` 4 + `MCELL4_BARV_FI`/`MCELL4_FULL_WEDGE` 等 + `ox3q1hP25` |
| `Kepler.Text.TameLp` | 6 | `fully_surrounded_perimeter_bound`、`ineq_tau{3,4,5,6}_tauVEF_std`、`sum_tauVEF_upper_bound` |
| `Kepler.Text.PackingAuto15` | 3 | `DIHX_SYM`、`MCELL_ID_MXI_2`、`MCELL_ID_OMEGA_LIST_N` |
| `Kepler.Text.PackingAuto11` | 3 | private `k2Case`、`k3Subset`、`rogersInterVLemma` |
| `Kepler.Text.PackingAuto21` | 2 | `TSKAJXY_034`、`mi_gamma3f_gamma3f_x_div_sqrtdelta` |
| `Kepler.Text.PackingAuto18` | 2 | `cc_pe_exists`、private `pa18_ccCell_swap` |
| `Kepler.Text.PackingAuto14` | 2 | `QZKSYKG1`、`QZKSYKG2` |
| `Kepler.Text.PackingAuto13` | 2 | `SLTSTLO2`、`DDZUPHJ` |
| `Kepler.Text.PackingAuto7` | 1 | `YIFVQDV_1` |
| `Kepler.Text.PackingAuto3` | 1 | `GRHIDFA_concl` |
| `Kepler.Text.PackingAuto2` | 1 | `UPFZBZM_concl` |
| `Kepler.Text.PackingAuto10` | 1 | `RVFXZBU` |
| `Kepler.Text.LocalAuto16` | 1 | `JEJTVGB_p16` |
| `Kepler.Text.LocalAuto1` | 1 | `main_nonlinear_terminal_v11` |
| `Kepler.Text.ContraFan` | 1 | `LEMMA_4_POINTS_FINAL` |

**零 direct 源的关键模块**：`PackingAuto17`（AJRIPQN 本体真装配）、
`PackingAuto12`（B1 后）、`PackingAuto9`、`PackingAuto24`、`PackingConcl`
（不在锥内）。B9 后 PA10 的可测链三件也从地图上消失，只剩 `RVFXZBU` 一根。

## 2. 最大消费簇（父边）

| 父声明 | 直接子债务源数 | 说明 |
|---|---:|---|
| `Assembly.nliPackNonlinearRest` | **59** | 非线性不等式 rest bank；当前最大单簇 |
| `Text.pkrmQu/Qy/Qx` | 25 | PA25 packing chapter 的 `real_model_*` 数据 |
| `Assembly.nliTskBank` | 8 | TSKAJXY 银行 |
| `Assembly.nliCell3Bank` | 7 | cell3 银行 |
| `Assembly.textCapstone` | 5 | `fcdjdot` / `jcajydu` / `tameCorrespondenceIso` 等 |
| `Assembly.nonlinearInequalities` | 5 | 六分量接口直挂节点 |
| `TameLp.MQMSMAB_adm1` | 4 | TameLp 不等式 |
| `Text.LEAF_RANK_PROPS` | 4 | PA25 leaf rank 数据 |
| `private.PackingAuto17.p17_ajripqn_of_tailfix` | 3 | **QZKSYKG1 / SLTSTLO2 / DDZUPHJ** |
| `private.PackingAuto17.qzksykg2_p17` | 1 | **QZKSYKG2** |
| 其余（pkrmAzim / cc_4_cc_ke4 / MCELL4_BARV_FI / MCELL2_DIHX 等） | 各 1-2 | 见 TSV |

## 3. 关键结论与纠错

1. **AJRIPQN 链确认在 e2e 锥内**：`QZKSYKG1`、`SLTSTLO2`、`DDZUPHJ` 的
   父声明都是 `p17_ajripqn_of_tailfix`；`QZKSYKG2` 的父是
   `qzksykg2_p17`。所以在飞的 QZKSYKG2 k=2 与 SLTSTLO2 车道是**直接削减
   主定理债务**，不是旁支。
2. **PA10 `RVFXZBU` 仍在 e2e 锥内，父 = PA25 `MCELL4_BARV_FI`**
   （PA25:3184，使用点 :5455），不是 PA17。B2 的 PA17 `hRV` 改接只把它从
   **AJRIPQN 的装配路径**移除；PA25 的 packing chapter 仍直接消费 PA10
   源件。纠正：B2 提交信息与审计文档中的“off-path orphan”应限定为
   “AJRIPQN hRV off-path”。建议小批把 `MCELL4_BARV_FI` 改接 PA14
   `RVFXZBU_p14`（同陈述，already clean），即可从 e2e 去掉这根源。
3. **PA24 / PackingConcl 零可达**：确认它们是邻近的 pack_concl 合并层，
   不在当前 e2e 锥。REUHADY1(d) 的债务不阻塞当前主定理。
4. **最大的下一块不是 AJRIPQN，是 Assembly 的 59 个
   `nliPackNonlinearRest` 源**；其次是 PA25 的 25 个 `real_model_*`。
   QZKSYKG2/SLTSTLO2 收工后，建议按这张图的簇顺序派工。
5. **624 条公理 = 23 条 `Assembly.GoodListShard*` + 601 条
   `Graphs.CertShards.*`/`CertTri/Quad/Pent/Hex`**，全部
   `native_decide` 生成，模块分布见 §4。与 DEBT 脊柱探针的 624 完全一致，
   这是遍历正确性的交叉验证。
6. **B9 验证**：PA9/PA12 零直接源，PA10 只剩 `RVFXZBU` 一根；
   BOUNDED/MEASURABLE 链已从地图消失。

## 4. 624 条可达公理的模块分布

| 模块 | 公理数 |
|---|---:|
| `Kepler.Graphs.CertShards.HexR` | 219 |
| `Kepler.Graphs.CertShards.Pent` | 142 |
| `Kepler.Graphs.CertShards.QuadR` | 80 |
| `Kepler.Graphs.CertShards.Hex` | 66 |
| `Kepler.Graphs.CertShards.PentR2` | 30 |
| `Kepler.Assembly.GoodListShard*` | 23 |
| `Kepler.Graphs.CertShards.PentR` | 16 |
| `Kepler.Graphs.CertShards.Quad` | 12 |
| `Kepler.Graphs.CertShards.PentR3` | 10 |
| `Kepler.Graphs.CertTri` | 9 |
| `Kepler.Graphs.CertShards.HexR2` | 5 |
| `Kepler.Graphs.CertQuad` | 4 |
| `Kepler.Graphs.CertPent` | 4 |
| `Kepler.Graphs.CertHex` | 4 |
| **合计** | **624** |

全部名称含 `_native.native_decide.ax_1_1`，无其它非标准公理。

## 5. 口径与再生成

- 静态 proof-term 遍历；`ConstantInfo.value? true`（theorem/opaque 值都展开，
  与 `#print axioms` 的闭包一致）。
- 只统计**直接**含 `sorryAx` 的声明；间接 taint 通过父边体现。
- 父边是第一个 BFS 父，不是唯一父；一个源可在多条路径上。
- 证明项里的死分支也会被计入（与 `#print axioms` 一致，因为内核仍要检查）。
- 再生成：
  ```bash
  cd lean && lake env lean scripts/e2e_reach_map.lean > /tmp/reachmap.out
  cp /tmp/reachmap.out docs/e2e-reachability-map.tsv
  ```
  首次运行会重建 `Assembly.olean`；后续热缓存约数秒。每次落库后重跑并 diff
  149 行清单，就是最直接的 e2e 债务刻度。

## 6. 建议的下一步

0. **P0 — SF-49（假陈述）**：rest 19 `bank_BIXPCGW9455898160` 的符号纠正
   （HOL `ineq.hl:985` `> -0.00569` vs Lean `> +0.00569`）。已立案待批；
   批准前不要发该件的 nli 批次。
1. **P0 小批**：把 PA25 `MCELL4_BARV_FI` 的 `RVFXZBU` 改接 `RVFXZBU_p14`，
   重跑地图确认 PA10 源消失（−1）。
2. **当前两条 AJRIPQN 车道收工后**重跑地图：QZKSYKG2（k=2 分支）与
   SLTSTLO2 的源应消失或缩小；以 diff 为准，不看提交信息自述。
3. **按簇派工**：59 `nliPackNonlinearRest` → 25 PA25 `real_model_*` →
   8 `nliTskBank` → 7 `nliCell3Bank`。
4. **624 公理 manifest + 抽样 replay**（审计文档 P0 第 2 项）。

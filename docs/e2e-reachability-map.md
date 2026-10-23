# 主定理 e2e 可达性地图（2026-10-23 重跑；AJRIPQN 归零后）

> 根 = `Kepler.Assembly.the_kepler_conjecture_from_interfaces`（即
> `Kepler.Final.the_kepler_conjecture_e2e` 的直接证明项）。
> 方法 = Lean proof-term 常量遍历（`lean/scripts/e2e_reach_map.lean`），
> 只跟踪 `Kepler.*` / `_private.Kepler.*`，统计：
> ①可达 Kepler 声明；②值里**直接**含 `sorryAx` 的声明（债务源）；
> ③可达 Kepler 公理；④每个债务源的第一个 BFS 父声明。
> 原始 TSV：[`docs/e2e-reachability-map.tsv`](e2e-reachability-map.tsv)。

## 0. 头版

| 指标 | 2026-10-22 | 2026-10-23 | 变化 |
|---|---:|---:|---|
| 可达 Kepler 声明 | 8,305 | **216,032** | +207,727（nli A1 把 CFWGKMBZ 证书接入 Assembly，证书闭包 ~206k 声明进锥；另加 PA25/PA15/PA11/N2 证明体。全部内核检查、零新公理） |
| 直接 sorryAx 债务源 | 149 | **133** | −16（euler PA21 `mi_gamma3f`、P0 PA10 `RVFXZBU`、B3 `YIFVQDV_1`+`QZKSYKG1`、B4 `QZKSYKG2`、B7 `DDZUPHJ`、B8f `SLTSTLO2`、nli A1 `nliRestFWGKMBZ`、PA25 `cc_bool_model_data`、nli N2 `nliRest6096597438b`、PA15 `MCELL_ID_MXI_2`+`MCELL_ID_OMEGA_LIST_N`+`DIHX_SYM`、PA11 `k2Case`+`k3Subset`+`rogersInterVLemma`） |
| 可达 Kepler 公理 | 624 | **624** | 0（全部 `native_decide` 图 shard；interval 证书用内核 decide，不新增公理） |

**结论：主定理当前的实际债务源是 133 个声明。** AJRIPQN 的五个名字
（`QZKSYKG1` / `QZKSYKG2` / `SLTSTLO2` / `DDZUPHJ` / `YIFVQDV_1`）、nli
`nliRestFWGKMBZ`/`nliRest6096597438b`、PA25 `cc_bool_model_data`、PA15
`MCELL_ID_MXI_2`/`MCELL_ID_OMEGA_LIST_N`/`DIHX_SYM` 与 PA11
`k2Case`/`k3Subset`/`rogersInterVLemma` 已从清单消失；
`#print axioms Kepler.Text.AJRIPQN` = `[propext, Classical.choice, Quot.sound]`。

> **PA25 口径注**：`cc_bool_model_data` 的证明体已无 `sorryAx`（`#valax3`
> 证明调用图 19,858 节点，仅标准三），故地图按其值把它移出 source。但它的
> 冻结陈述类型经 `cc_data_v8 → ccCell → ccUh → cc_uh_exists → cc_pe_exists`
> 仍触达 PA18 既存 sorry，因此字面 `#print axioms cc_bool_model_data` 仍会
> 打印 `sorryAx`；该类型债由 **`cc_pe_exists` 自身**作为独立 source 记账，
> 未被掩盖。闸的 rule 5 自 2026-09-28 起本就允许 `sorryAx`。

## 1. 债务源按模块

| 模块 | direct sorry 源 | 代表声明 |
|---|---:|---|
| `Kepler.Assembly` | 81 | 77 个 `nli*`（57 个父为 `nliPackNonlinearRest`、8 个 `nliTskBank`、7 个 `nliCell3Bank`、5 个直挂 `nonlinearInequalities`）+ `fcdjdot` / `jcajydu` / `tameCorrespondenceIso`（父 `textCapstone`）+ `lpArchiveCertificatesDebt`（父 `lpArchiveCertificates`） |
| `Kepler.Text.PackingAuto25` | 38 | 28 个 `real_model_*`（父 `pkrmQu/Qx/Qy` 等）+ `LEAF_RANK_PROPS` 4 + `MCELL4_FULL_WEDGE` 等 + `ox3q1hP25` |
| `Kepler.Text.TameLp` | 6 | `fully_surrounded_perimeter_bound`、`ineq_tau{3,4,5,6}_tauVEF_std`、`sum_tauVEF_upper_bound` |
| `Kepler.Text.PackingAuto18` | 2 | `cc_pe_exists`、private `pa18_ccCell_swap` |
| `Kepler.Text.PackingAuto3` | 1 | `GRHIDFA_concl` |
| `Kepler.Text.PackingAuto21` | 1 | `TSKAJXY_034` |
| `Kepler.Text.PackingAuto2` | 1 | `UPFZBZM_concl` |
| `Kepler.Text.LocalAuto16` | 1 | `JEJTVGB_p16` |
| `Kepler.Text.LocalAuto1` | 1 | `main_nonlinear_terminal_v11` |
| `Kepler.Text.ContraFan` | 1 | `LEMMA_4_POINTS_FINAL` |

**零 direct 源的关键模块**：`PackingAuto11`（LEPJBDJ 三私件后）、
`PackingAuto15`（DIHX_SYM 后）、
`PackingAuto17`（AJRIPQN 本体真装配）、
`PackingAuto13`（B8f 后）、`PackingAuto14`（B4 后）、`PackingAuto7`（B3 后）、
`PackingAuto12`、`PackingAuto9`、`PackingAuto10`（P0 后）、`PackingAuto24`、
`PackingConcl`（不在锥内）。

## 2. 最大消费簇（父边）

| 父声明 | 直接子债务源数 | 说明 |
|---|---:|---|
| `Assembly.nliPackNonlinearRest` | **58** | 非线性不等式 rest bank；A1 后 59→58，仍是最大单簇 |
| `Text.pkrmQu` | 9 | PA25 packing chapter 的 `real_model_*` 数据 |
| `Text.pkrmQy` | 8 | 同上 |
| `Text.pkrmQx` | 8 | 同上 |
| `Assembly.nliTskBank` | 8 | TSKAJXY 银行 |
| `Assembly.nliCell3Bank` | 7 | cell3 银行 |
| `Assembly.textCapstone` | 5 | `fcdjdot` / `jcajydu` / `tameCorrespondenceIso` 等 |
| `Assembly.nonlinearInequalities` | 5 | 六分量接口直挂节点 |
| `TameLp.MQMSMAB_adm1` | 4 | TameLp 不等式 |
| `Text.LEAF_RANK_PROPS` | 4 | PA25 leaf rank 数据 |
| `Text.pkrmAzim` | 2 | PA25 real_model 切片 |
| `Text.cc_4_cc_ke4` | 2 | PA25 cc 链 |
| 其余（MCELL2_DIHX / MCELL4_BARV_FI 等） | 各 1 | 见 TSV |

## 3. 关键结论与纠错

1. **AJRIPQN 已归零（2026-10-23）**：四个承重根
   `QZKSYKG1`（B3 `ce71abd3`）、`QZKSYKG2`（B4 `c7b67c9b`）、
   `DDZUPHJ`（B7 `c8b43895`）、`SLTSTLO2`（B8f `cb268b64`）全部真证；
   `#print axioms Kepler.Text.AJRIPQN` = `[propext, Classical.choice, Quot.sound]`。
   `WQPRRDY`（PA7:3976）仍是 sorry，但 B4 证明 QZKSYKG2 时不消费它，
   已退出 e2e 锥。
2. **首个 nli rest 源接线（nli A1 `286d11b8`）**：`nliRestFWGKMBZ` 由
   `Kepler.Interval.Cases.CFWGKMBZ`（605 分片 + Base，205,418 叶，探针标准三）
   直接导出；证书闭包 ~206k 声明进入锥，但**零新公理**。这是 57 个
   `nliPackNonlinearRest` 源的可复制样板（A2 rest 9 含 sqrt/atan/ite，
   不能照搬 glue，且冷构建外推 40–45h）。N2 rest 1 先用 hybrid sin 编码 +
   CertGD/BBTreeGD 绕开损坏的 CertG，达到 78 叶闭合。
3. **PA10 `RVFXZBU` 已由 P0（`760a192a`）解决**：PA25 `MCELL4_BARV_FI`/
   `MCELL4_LEAF3` 改接 PA14 `RVFXZBU_p14`，PA10 源已离场（PA20 的两处消费
   不在 e2e 锥）。
4. **PA24 / PackingConcl 零可达**：仍是邻近的 pack_concl 合并层，
   不在当前 e2e 锥；REUHADY1(d) 不阻塞当前主定理。
5. **最大的下一块是 Assembly 的 57 个 `nliPackNonlinearRest` 源**；
   其次是 PA25 的 38 个源（28 `real_model_*` + 10 其他）。
6. **624 条公理 = 23 条 `Assembly.GoodListShard*` + 601 条
   `Graphs.CertShards.*`/`CertTri/Quad/Pent/Hex`**，全部 `native_decide`
   生成，模块分布见 §4，与 DEBT 脊柱探针的 624 完全一致。
7. **口径警告**：可达声明数从 8,305 跳到 216,032 不是债务增加，而是
   CFWGKMBZ 证书（内核可检查的 shard 树）进入了证明项闭包；比较债务时
   看 direct sorry 源（133）与公理（624），不要看可达声明总数。

## 4. 624 条可达公理的模块分布

| 模块族 | 公理数 |
|---|---:|
| `Kepler.Graphs.CertShards.HexR*` | 224 |
| `Kepler.Graphs.CertShards.Pent*` | 202 |
| `Kepler.Graphs.CertShards.Quad*` | 95 |
| `Kepler.Graphs.CertShards.Hex*` | 66 |
| `Kepler.Assembly.GoodListShard*` | 23 |
| `Kepler.Graphs.CertTri/Quad/Pent/Hex` | 21 |
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
  首次运行会重建 `Assembly.olean`；后续热缓存约数秒。每次落库后重跑并
  diff 133 行清单，就是最直接的 e2e 债务刻度。

## 6. 建议的下一步

1. **P0 — nli 样板复用**：把 A1 的“证书 → `CFWGKMBZ_pos` → Assembly glue”
   固化成模板；A2（rest 9，2,775 分片/96 万叶）先解决预构建 oleans/分机，
   再接线。
2. **P0 — 624 公理 manifest + 抽样 replay**（审计文档 P0 第 2 项）。
3. **按簇派工**：58 `nliPackNonlinearRest` → 39 PA25（28 `real_model_*`）→
   8 `nliTskBank` → 7 `nliCell3Bank`。
4. **LP 端到端审计**：在填 `lpArchiveCertificatesDebt` 之前完成
   （`leanprover/lp-verify` + 原始 `formal_lp` 证书，见
   `docs/scouts/lean4-ecosystem-scout.md`）。
5. **WQPRRDY 记账**：PA7:3976 仍是 sorry 但不在锥；若未来有消费者，
   会被拉回地图，届时按 B4 的 private kit 逐 k 处理。

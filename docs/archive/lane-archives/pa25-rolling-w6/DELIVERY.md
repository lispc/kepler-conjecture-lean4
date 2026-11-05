# DELIVERY — pa25-rolling-w6

基线：主仓 HEAD `7cdf4570`（工作期间其他车道把 HEAD 推进到 `873d2a2c`，
但 `lean/Kepler/Text/PackingAuto25.lean` 未变，仍为
`4f6fa20d2c0887efbe435299a8af764b` / 14,868 行 / 19 裸 sorry /
20 编译器 sorry 警告 / 0 error）。本车道只改 `lean/Kepler/Text/PackingAuto25.lean`。

## 1. 闭合件（7 件，全部真证零 sorryAx）

| # | 件 | Work.lean 行 | 证法（一句） |
|---|---|---|---|
| 1 | `MCELL3_008` | 13429 | `MCELL3_EDGE_FIRST` 把任意 `ul` 归一为 `[u0,u1,v1,v2]`；`gammaX_gamma3f`（第 8/5 合取支）+ `MCELL3_CRITICAL_WEIGHT` + `MCELL_BUMP_0` 消 beta，数值核 = 新桥 `p25w6_cell3_008_aux`（wt1/wt2A/CIHTIUM 三银行 + `p25w6_undiv_gamma3_nn`，y2 二分支 × wtcount3Y=1/2） |
| 2 | `real_model_008` | 13508 | `Finset.sum_le_sum` 逐胞；`EDGE_IMP_K23` 给 `k=2∨k=3`：k=2 用 `MCELL2_CRITICAL_WEIGHT1`（cw=1）+ `CC_2_PROPS`（`0.008*dih < gammaX`），k=3 用 `MCELL3_008`；beta=0 由 `MCELL_BUMP_0` |
| 3 | `real_model_cell23_008` | 13681 | `CC_3_SUM_fn` 两次实例（fn=`dihX` 与 `gammaX*cw+beta`）拆 azim/gg 为两 cc 胞 + 余项和；余项用 `real_model_008`，`Finset.mul_sum` 提出 `0.008`；`CC_3_PROPS` 供两胞 beta=0；`linarith` |
| 4 | `GAMMAX_008a` | 13731 | `CC_3_PROPS`（`ccKe=3`/`barV`/`beta=0`/`leaf`）+ `EL_CC_UH` 把 `STEM_EDGEX` 的 getD 对钉成 `{u0,u1}` + `MCELL3_008`（hX 由 `unfold ccCell; rw [hk3a]; MCELL3.symm`） |
| 5 | `GAMMAX_008b` | 13757 | 同上 b-侧 `ccCell [u1,u0,f(i+1)]`；stem 边 `{u1,u0}={u0,u1}` 用 `ext; tauto` 换向（无需 `DIHX_SYM`，边是集合） |
| 6 | `real_model_gr` | 13827 | `real_model_cell23_008` + `GAMMAX_008a` + `GAMMAX_008b`，`linarith`（两 cc 胞差项非负 ⇒ `0.008*azim ≤ gg`） |
| 7 | `real_model_sum_azim` | 9811 | 前置私拷贝 `p25w6_order_azim_sum2pi0`（= 本文件末尾 `ORDER_AZIM_SUM2Pi0` 同体，因声明位置早于它）+ `GBEWYFX` 供非共线 + `LEAF_RANK_REUHADY` 逐项换 `azim_mcell=azim`；`hplus < √2` 由 `nlinarith` + `Real.sq_sqrt` |

## 2. 新增 private kit（9 枚，全零 sorry / 零 admit / 零 native_decide）

`p25w6_dihY_swap`、`p25w6_matan`、`p25w6_dihXf_atn`、`p25w6_dihalg`、
`p25w6_dihXf_bridge`、`p25w6_dihY_bridge`、`p25w6_undiv_gamma3_nn`、
`p25w6_cell3_008_aux`、`p25w6_order_azim_sum2pi0`。

其中 `p25w6_cell3_008_aux` 是 HOL `cell3_008_from_ineq_ALT` 的 Lean 实装：
`pack_nonlinear_non_ox3q1h` 下三银行 ⇒ `0.008*dih_y ≤ gamma3f/wtcount3_y`，
w7 可直接消费（w5 的 `p25w5_QITNPEA_9063653052` 同款地位）。

## 3. 整文件读数（命令原文 + 读数）

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q logs/w6c-full.log lean $S/Work.lean
RC=0
tr -d '\r' < logs/w6c-full.log | grep -c ': error:'                 -> 0
tr -d '\r' < logs/w6c-full.log | grep -c ': warning:'               -> 175
tr -d '\r' < logs/w6c-full.log | grep -c 'declaration uses `sorry`' -> 13
wc -l -> 15417 ; md5 -> 766b6b2a86f6aacce24190a14d9a6077
```

基线同口径：14,868 行 / 0 error / 170 warning / 20 sorry 警告
（= `ox3q1hP25` + 19 裸）。**own-sorry 19 → 12**。
非 sorry 警告 150 → 162（+12）：全部是本波 7 件证明体的 unused-variable
linter 提示（签名冻结、参数必须保留），无新语义警告。`ox3q1hP25` 定义体
（第 90 行）与基线逐字一致，624 shard 面未触碰（diff 只落 9 个 hunk：
9743 / 9752 / 13062 / 13070 / 13088 / 13217 / 13229 / 13241 / 13289 区）。

## 4. 补丁与陈述冻结

- `patch-pa25-rolling-w6.diff`：`git apply --stat` → 1 file changed,
  **556 insertions(+), 7 deletions(-)**（7 条 `sorry` 体被替换）；
  对主仓当前 HEAD `git apply --check` → **PASS**（只读，未改主仓）。
- 7 件签名与 HEAD `cmp` 逐字一致（脚本抽取 `theorem <name> … := by`
  之前整段，输出 `IDENTICAL ×7`）。

## 5. 公理面（原文见 `Evidence.md`）

7 件 + 4 枚核心私件 `#print axioms` 全部
`[propext, Classical.choice, Quot.sound]`（零 sorryAx）。

## 6. 残件精确缺口（12 裸 sorry，行号为 Work.lean）

| # | 件 | 行 | 缺口 |
|---|---|---|---|
| 1–2 | `real_model_pema` / `pemb` | 13883 / 13895 | **最高杠杆**：008 家族已闭后只剩装配。HOL OXLZLEZ3.hl:8296-8419：`real_model_cell23_008` + `GAMMAX_008a/b` + `CC_3_PROPS` 的 `∃y4` + `JSP_BOUNDS` + `PEMKWU` 银行（`proj_bank_PEMKWU` 在库）+ `mi_gamma3_x_gamma3f` + `MCELL2_CRITICAL_WEIGHT1` + `mcell3_gammaX_gamma3f` + `mcell3_dihX_dih_y`，全在库 |
| 3–4 | `real_model_txq` / `tew` | 14569 / 14580 | `real_model_cell23_008` + `TXQTPVC_MERGED` / `TEWNSCJ_MERGED`（均在库）+ `LEAF_DOMAIN`/`JSP_BOUNDS` 型装配 |
| 5–6 | `real_model_gamma10` / `gamma11` | 12201 / 12221 | HOL `gamma10_gamma11_ALT`(:4071) 不在 Lean；上游 `gamma10_gamma11` 亦不在。缺 `rad2_eta2`（rad2_y<2 ⇒ eta_y²<2）与 `beta_bump_lb`/`beta_bumpA_lb1` 两桥；`quarter_norm2hh` 可用 PA25 `ztg4w1_quarter_norm2hh`；四银行（GLFVCVK4/QITNPEA5400790175a,b/FWGKMBZ）在库 |
| 7–8 | `real_model_quqy` / `quqy_sym` | 10581 / 10598 | 尚未侦察（HOL `g_quqya_goal` 区：FHBVYXZ a/b + FWGKMBZ + cell3_from_ineq） |
| 9 | `pkLeafRankCriticalEdge` | 9877 | 深水（`CELL_CLUSTER_*` 链） |
| 10–11 | `CELL_CLUSTER_ESTIMATE_REDUCE` / `CELL_CLUSTER_N_LE_1` | 6155 / 6503 | 深水（锥外大件） |
| 12 | `real_model_ox3q1h_merge` | 9954 | 需 `hox : ox3q1hP25`（DEF-FIX 冻结） |
| — | `ox3q1hP25` | 90 | DEF-FIX 专属，冻结 |

**未建 `Kit-draft-pa25-rolling-w6.lean`**：所有改动都在 `Work.lean` 内且
整文件 RC=0 / 0 error；无「修不完的件」需移出 kit。

## 7. 搬债审计

- 逐个 `grep` 新增 556 行对 12 个仍-sorry 声明 + `ox3q1hP25` 的引用：
  **全部 0**（脚本逐名跑，无输出）。
- 新引用依赖面全为既证件：`gammaX_gamma3f`、`MCELL3_EDGE_FIRST`、
  `MCELL3_CRITICAL_WEIGHT`、`MCELL_BUMP_0`、`EDGE_IMP_K23`、`CC_2_PROPS`、
  `CC_3_PROPS`、`CC_3_SUM_fn`、`STEM_EDGEX`、`EL_CC_UH`、
  `cell3_from_ineq_thm`、`mi_gamma3f_gamma3f_x_div_sqrtdelta`、
  `mi_ETA_Y_BOUNDS`、`mi_ETA_Y_LE_IMP_LT_ALL`、`mi_gamma3f_sym`、
  `LEAF_RANK_REUHADY`、`GBEWYFX`、`FINITE_EDGE_X2`。
- **零搬债**；K-SORRIED 地图快照仍写 119（过时），w7 若刷地图应见 119 → 112。

## 8. 预算自报

- 调用 ~82（上限 120）；墙钟 ~1h55m（上限 3h）。
- 探针：`probe1-w6a.lean`（W6-A 桥 + 7 件全量，单文件 RC=0）、
  `probe-ax.lean`（依赖公理面）、`probe-mini.lean`（setSum 线性核）；
  全部单进程串行，未触 `lake`，未写其它车道 scratch。
- 整文件 standalone 编译 5 次（基线 / w6a（4 err 定位）/ w6b（3 err）/ 
  w6c（绿）/ axioms-probe），每次 ~5–6 min。

## 9. 交付物清单（`$S = /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w6/`）

```
patch-pa25-rolling-w6.diff        556+/7-，git apply --check PASS
Work.lean                         15417 行，RC=0 / 0 error / 13 sorry-warning
axioms-probe-pa25-rolling-w6.lean  （= Work.lean + 11 条 #print axioms）
WORKORDER-w7.md
DELIVERY.md（本文件）
Evidence.md
logs/                             baseline / probe1 / mini / ax1 / w6a-full / w6b-full / w6c-full / w6-axioms
probe1-w6a.lean / probe-ax.lean / probe-mini.lean（探针，仅取证）
```

归档（仓内，显式要求的未跟踪工件）：`docs/archive/lane-archives/pa25-rolling-w6/`
（patch + DELIVERY + Evidence + WORKORDER-w7；Work.lean 不入库）。

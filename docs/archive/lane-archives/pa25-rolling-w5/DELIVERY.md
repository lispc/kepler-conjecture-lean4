# DELIVERY — pa25-rolling-w5

基线：主仓 HEAD `c831efac`（PA25 `2fe12c2150f5aee916d5fd89efda08ca`，14,547 行，
22 裸 sorry / 23 编译器 sorry 警告 / 0 error）。本车道只改
`lean/Kepler/Text/PackingAuto25.lean`。

## 1. 闭合件（3 件，全部锥内 / K-REACH 内）

| 件 | 终稿行 | 锥内 | 证法（一句） |
|---|---|---|---|
| `real_model_gamma8` | 12260 区 | Y（map 行 `parent=Kepler.Text.pkrmQx`） | `GG_MCELL_NONBETA` 塌缩（`hnot` 直接由第三合取 `¬(d03 小 ∧ d13 小)` 供，`hnot5` 不用）+ 新私件 `p25w5_QITNPEA_9063653052`（HOL `QITNPEA4_9063653052_weak_ALT` 的 Lean 重推：六张 `QITNPEA1_{1,2}×{0,1,2}` 银行按 y3/y4 临界性分六支 + `wtcount6Y = 1+[y3 crit]+[y4 crit]` 记账 + 权重单调化）+ `leaf_CIHTIUM` 把 `f(i+1)` 侧唯一非小边换到 y3 槽（`gamma4fgcy_sym26`/`wtcount6Y_sym26`/`rad2YP25_sym26` 运回原序） |
| `real_model_gamma8b` | 12287 区 | Y（`parent=Kepler.Text.pkrmQx`） | 同核件；`¬(d02 小 ∧ d12 小)` 的两支：`d02 小` 支用 `(2 5)(3 6)` 复合换位（新私件 `p25w5_gamma4fgcy_perm`/`wtcount6Y_perm`/`rad2YP25_perm`），`¬(d02 小)` 支用 `leaf_CIHTIUM` 反证得 `d12 小` 后走 sym23 |
| `real_model_gckb` | 9730 区 | Y（`parent=Kepler.Text.pkrmAzim`） | `cc_4` 支：`c_4_azim_mcell_dih_y` + `MCELL4_DOMAIN` 盒 → `proj_bank_GCKBQEA`（`dihY > 0.606`）；`¬cc_4` 支：`CC_3_PROPS` 的 `∃ y4`（`dihY … y4 ≤ azim`）→ 同一银行在 `(d01,d02,d03,y4,d13,d12)` 上实例化 + `linarith` |

own-sorry 22 → **19**（3 件闭合）。三件 `#print axioms` 均为
`[propext, Classical.choice, Quot.sound]`（原文见 `Evidence.md`）。

新增 **8 个 private 助件**（全部 `p25w5_` 前缀，零 sorry / 零 admit /
零 native_decide）：`p25w5_wtcount6Y_sym26`、`p25w5_wtcount6Y_sym23`、
`p25w5_QITNPEA_9063653052`、`p25w5_rhoX_sym26`、`p25w5_rad2YP25_sym26`、
`p25w5_wtcount6Y_perm`、`p25w5_gamma4fgcy_perm`、`p25w5_rad2YP25_perm`。
**零新 import**；未新增 `open Classical`（新内核件内用 `classical` tactic 取得
`Decidable (criticalEdgeY _)`，`open` 面一字未动）。

## 2. 整文件读数（命令原文 + 读数）

基线（HEAD 文件，日志 `logs/base-full.log`）：

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q logs/base-full.log lean <repo>/lean/Kepler/Text/PackingAuto25.lean
RC=0
tr -d '\r' < logs/base-full.log | grep -c ': error:'                       -> 0
tr -d '\r' < logs/base-full.log | grep -c ': warning:'                     -> 173
tr -d '\r' < logs/base-full.log | grep -c 'declaration uses `sorry`'        -> 23
wc -l  -> 14547 ;  md5 -> 2fe12c2150f5aee916d5fd89efda08ca
```

终稿（`Work.lean`，日志 `logs/w5b-full.log`）：

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q logs/w5b-full.log lean $S/Work.lean
RC=0
grep -c ': error:'                       -> 0
grep -c ': warning:'                     -> 170
grep -c 'declaration uses `sorry`'        -> 20      (= ox3q1hP25 + 19 裸)
非 sorry 警告谱面逐条一致（150 条 == 基线 150 条，Counter 相等）
wc -l -> 14868 ;  md5 -> 4f6fa20d2c0887efbe435299a8af764b
```

补丁：`patch-pa25-rolling-w5.diff`
`git apply --stat` → `lean/Kepler/Text/PackingAuto25.lean | 327 +++`, `1 file changed, 324 insertions(+), 3 deletions(-)`；
对 HEAD `git apply --check` → **PASS**（只读，未改主仓）。陈述冻结：三件签名与 HEAD
`cmp` 逐字一致（脚本比对 `theorem <name> … := by` 之前整段，输出 STMT IDENTICAL ×3）。

## 3. 残件精确缺口（诚实口径，均为「搬债 → BLOCKED」或「清单外」）

剩余 19 裸 sorry（行号为终稿）：

| # | 件 | 行 | 缺口（精确到 API / 银行） |
|---|---|---|---|
| 1 | `MCELL3_008` | 13067 | HOL `Merge_ineq.cell3_008_from_ineq_ALT`(:4588) **不在 Lean**；其上游 `cell3_008_from_ineq_thm`(:4455) 亦不在。需 y2 二分支（`h0cut`）+ 权重案子 + 银行 `bank_QZECFICwt1`/`wt2A`/`CIHTIUM`（三张在 PA21 在库），并缺 `undiv_gamma3_nn`、`cell3_from_ineq_thm_ALT` 两桥（Lean 无）。→ **008 簇的唯一闸门** |
| 2 | `GAMMAX_008a` | 13223 | 只差 `MCELL3_008`（HOL 证明 = `CC_3_PROPS` 供 `X = mcell3 (ccUh …)` + `STEM_EDGEX` 的边成员 + `betaBumpV1 = 0` 后 `x + 0 = x`） |
| 3 | `GAMMAX_008b` | 13235 | 同上 + `DIHX_SYM`（Lean 待查 `CC_CELL_IN_MCELL_SET` 对应件） |
| 4 | `real_model_008` | 13077 | 只差 `MCELL3_008`（逐胞求和 + `GAMMAX_NO_BETA`/`TSKAJXY_2` 已在库，与已真证 `real_model_cell23` 同型装配） |
| 5 | `real_model_cell23_008` | 13206 | 只差 2/4 + `GAMMAX_008a/b` + `c_4_azim_mcell_dih_y` |
| 6 | `real_model_gr` | 13285 | 只差 3/5（`0.008·azim` 三分拆：两 cc 胞各一 `GAMMAX_008`，余项由 `CC_3_PROPS` 的 `dihY ≤ azim` 非负） |
| 7–10 | `real_model_pema` / `pemb` / `txq` / `tew` | 13325 / 13337 / 14011 / 14023 | 四件全消费 `real_model_cell23_008`（+ `bank_PEMKWU` / `TXQTPVC_MERGED` / `TEWNSCJ_MERGED` / `JSP_BOUNDS` 均已在库，**仅差闸门 5**） |
| 11–12 | `real_model_gamma10` / `gamma11` | 12110 / 12130 | HOL `Merge_ineq.gamma10_gamma11_ALT`(:4071) 不在 Lean；其上游 `gamma10_gamma11` 亦不在。四张银行（`GLFVCVK4…`、`QITNPEA5400790175a/b`、`FWGKMBZ`）在库；`beta_bumpA_y_sym23` 在库。装配件（`critical_weight1a/b` + `GG_MCELL_GENERAL` + `mcell3_gammaX_gamma3f` + `mcell3_gammaXb_gamma3f`）全部已真证 |
| 13–14 | `real_model_quqy` / `quqy_sym` | 10494 / 10510 | w5 清单外，未侦察 |
| 15 | `real_model_sum_azim` | 9749 | 深水（w5 工单明令不碰）。**新发现**：`LEAF_RANK_GRUTOTI` 已在 PA25 真证，HOL 证明只需它 + `HL_2` 化简 + `0 < √2 − hplus`（Flyspeck_constants 界），w6 可试 |
| 16 | `real_model_ox3q1h_merge` | 9856 | 需 `hox : ox3q1hP25`（DEF-FIX 冻结件） |
| 17 | `pkLeafRankCriticalEdge` | 9795 | 深水（`CELL_CLUSTER_ESTIMATE_REDUCE` + `CELL_CLUSTER_N_LE_1`） |
| 18–19 | `CELL_CLUSTER_ESTIMATE_REDUCE` / `CELL_CLUSTER_N_LE_1` | 6150 / 6498 | 深水（锥外大件） |
| — | `ox3q1hP25` | 90 | DEF-FIX 专属，冻结 |

**未建 `Kit-draft-pa25-rolling-w5.lean`**：本波所有改动都在 `Work.lean` 内且整文件
RC=0 / 0 error，无「修不完的件」需要移出 kit；kit 为空即最优。

## 4. 搬债审计（`docs/e2e-reachability-map.tsv` 地图行为准）

- 三件均**在锥**（`grep` 行）：
  - `Kepler.Text.PackingAuto25  Kepler.Text.real_model_gamma8   parent=Kepler.Text.pkrmQx`
  - `Kepler.Text.PackingAuto25  Kepler.Text.real_model_gamma8b  parent=Kepler.Text.pkrmQx`
  - `Kepler.Text.PackingAuto25  Kepler.Text.real_model_gckb     parent=Kepler.Text.pkrmAzim`
- **体内新引用的 sorried 件 = 0**：把终稿仍在-sorry 的 20 个声明名逐个
  `grep -c "^+.*\b<name>\b" patch-pa25-rolling-w5.diff`，全部 0（脚本逐行跑，无输出）。
  新引用的依赖面全是既证件：`GG_MCELL_NONBETA`、`MCELL4_DOMAIN`、`leaf_CIHTIUM`、
  `CC_3_PROPS`、`c_4_azim_mcell_dih_y`、`gamma4fgcy_sym26`、`LEAF_RANK_LEAF`、
  `mi_sqrt8_eq`、`mi_hminus_prop`、六张 `proj_bank_QITNPEA1_*`、`proj_bank_GCKBQEA`
  （后两者是 `pack_nonlinear_non_ox3q1h` 假设的投影，非 sorry）。
- 故本波**零搬债**；K-SORRIED 地图快照仍写 119（过时：w1–w4 + 本波 3 件已闭），
  w6 若刷地图应见 119 → 116。

## 5. 预算自报

- 调用：~62（上限 120）；墙钟 ~1h10m（上限 3h）。
- 探针：3 个（`probe0` 名字核对 / `probe1` 内核件 / `probe2` 双目标 / `probe3` gckb），
  全部单进程串行，未触 `lake`，未写其它车道 scratch。
- 整文件 standalone 编译 4 次（基线 / W5-A / W5-A+gckb / axioms-probe），每次 ~3–4 min。

## 6. 交付物清单（`$S = /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w5/`）

```
patch-pa25-rolling-w5.diff      324+/3-，git apply --check PASS
Work.lean                       14868 行，RC=0 / 0 error / 20 sorry-warning
WORKORDER-w6.md
DELIVERY.md（本文件）
Evidence.md                     #print axioms 原文 + 读数
axioms-probe-pa25-rolling-w5.lean  （= Work.lean + 4 条 #print axioms，仅取证用）
logs/                           base-full / w5a-full / w5a-mod / w5b-full / w5-axioms
```
归档（仓内，未跟踪）：`docs/archive/lane-archives/pa25-rolling-w5/{patch-pa25-rolling-w5.diff,DELIVERY.md,Evidence.md,WORKORDER-w6.md}`

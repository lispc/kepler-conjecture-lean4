# DELIVERY — lane pa25-farm-plan（PA25 30 e2e 直源排产/备料波）

- 主仓 `/Users/zhangzhuo/repos/kepler-conjecture-lean4`，任务基线 HEAD = **1c0b328f**（map-metrics-v2）。
- **交付时实测 HEAD = a34cb699**（并发车道 pa19-rdwkarc 落库）；`1c0b328f..a34cb699` 只改
  `docs/priority-queue.md` + `lean/Kepler/Text/PackingAuto19.lean`，**PA25 blob 逐字相同**
  （`1c0b328f:PA25` 与 `HEAD:PA25` 的 git blob 都是 `1ce617cc…`；`git diff --numstat` 为空）。
  本报告所有 PA25 行号/读数对两个 HEAD 都成立。
- 目标文件 `lean/Kepler/Text/PackingAuto25.lean`（12,566 行；MD5 `a72280c8…`）。
- 本波性质：**排产/备料波，零重型计算**。未改主仓 tracked，未跑 `lake`，未跑 G4，未发射，
  未构建重片；只读解析 + 一个只读 `lean` API 探针（导入既有 olean，见 Evidence E5）。
- 预算自报：约 **44 调用 / 1h50m**（上限 120 / 3h）。

## 0. 结论摘要（TL;DR）

1. **计数口径对上了，任务书的 57 是旧数**：HEAD 源级 `sorry` 项 = **56** = **55 个 theorem +
   1 个 def（`ox3q1hP25`）**；ztg4-w1 前是 58 项（57 theorem + 1 def），所以任务书
   "57 declaration-level" = ztg4-w1 前的 theorem 计数。HEAD 的 theorem 级 = 55。
2. **30 个 e2e 直源 = 29 theorem + 1 def**：26 个 `real_model_*` + `cc_prep_model_data` /
   `pkLeafRankCriticalEdge` / `pkLeafRankAzimPointwise` 三 theorem + `ox3q1hP25` def。
   与 `docs/e2e-reachability-map.tsv` 的 `parent=` 行逐字对上（30 行，见 `logs/map_pa25_30.tsv`）。
3. **最大的可执行发现：11/30 已有"验证过的重放备料"**。poolc-w4（7 闭）+ poolc-w5（2 闭）+
   poolc-w6（2 闭）在旧基线 76771f7e 上合成过候选件，**21/21 探针标准三、0 error**；
   poolc-w6-replay 已判 16/16 AS-IS。本波把该候选与 HEAD 做三方合并：
   **0 冲突、+841/−16、删除面恰 16 行裸 `sorry`、`git apply --check` PASS**。
   产物 `kit-pa25-replay-w4w5w6.diff`。**未在 HEAD 编译，不得据此声称关闭**；落库前必须
   过整文件 RC=0 + 闸 + axioms 复探。
4. **26 条 `real_model_*` 不是 26 张待发射证书**：其中 11 条已由 poolc 波用**在库 bank 投影 +
   几何塌缩**真证（无新发射）；其余 15 条里，10 条卡的是**文件内 3-胞 kit 的 sorry**
   （`real_model_008` / `cell23_008` / `GAMMAX_008a/b` / `MCELL3_008` 等），2 条卡
   **Merge_ineq ALT 引理未移植**（`gamma10_gamma11_ALT` / `g_quqya_g_quqyb_ALT` /
   `QITNPEA4_9063653052_weak_ALT`），2 条深水（`real_model_gckb` 3-胞支、
   `real_model_sum_azim` 扇形和），1 条外部锚（`real_model_ox3q1h_merge` ← `ox3q1hP25`）。
   **本机冻结下 0 条需要跑 G4**；唯一可能的"新 bank/新证书"缺口是 `real_model_gamma8b`（NO-GO）。
5. **4 个非/半 farm 件**：`cc_prep_model_data` 是**唯一真闭包候选**（HOL 100 行 MESON 脚本，
   全部依赖已在库且已证；估 4–8 agent-h）；`pkLeafRankAzimPointwise` /
   `pkLeafRankCriticalEdge` 只能做**搬债式装配**（分别暴露 `MCELL_WEDGE_UNIQUE` /
   `CELL_CLUSTER_ESTIMATE_REDUCE`+`CELL_CLUSTER_N_LE_1`），不减少文件级 sorry 数；
   `ox3q1hP25` **NO-GO**（`Oxl_def.hl` 本体不在仓内，230 record×5 支）。
6. **PackingConcl c1 关系**：`rdwkarcConcl_pc` / `RDWKARC_concl_discharged` **0/30** 依赖
   PA25 30 源（只吃 PA19 `UPFZBZM` + 把 `hcc`/`hT` 当参数）；但
   `PACKING_CHAPTER_MAIN_CONCLUSION_discharged` 的 `hcc := OXLZLEZ` 使 **30/30 全在其祖先锥**，
   关任意一条都会削它的 `sorryAx`。Assembly.textCapstone 的 c1 rewire 只是把消费端点从
   PA25 `PACKING_CHAPTER_MAIN_CONCLUSION` 换到 PackingConcl `_discharged`，未改 30 源的 parent 边。

## 1. 口径与计数对账

### 1.1 源级 sorry 计数（HEAD）

| 口径 | 读数 | 命令/说明 |
|---|---|---|
| 源文件行首/裸 `sorry` 项（去注释/字符串） | **56** | 自写只读 lexer，见 Evidence E2 |
| 其中 theorem | **55** | 同上 |
| 其中 `def` | **1**（`ox3q1hP25 : Prop := sorry`，:90） | 同上 |
| 原始 `grep -c sorry`（含注释/docstring） | 74 行 | 注释里 18 处 "sorry" 字样 |
| ztg4-w1 前（a3de6b76^） | **58** = 57 theorem + 1 def | 见 Evidence E2；这解释了任务书的 "57" |
| ztg4-w1 后（a3de6b76） | **56** = 55 theorem + 1 def | HEAD 同值（a3de6b76 是最后一次改 PA25 的提交） |

> 结论：任务书 "57 declaration-level" 与 HEAD 的 56 项并不矛盾，是**旧 theorem 计数**
> （57）与 HEAD 全项计数（56）的口径差；**HEAD theorem 级 = 55**。本波统一用
> "56 body sorry（55 theorem + 1 def）" 记账。

### 1.2 30 直源与 map 对账

```
$ awk -F'\t' 'NF==3 && $3 ~ /^parent=/ && $1=="Kepler.Text.PackingAuto25"' \
    docs/e2e-reachability-map.tsv | wc -l
30
```

30 = 26 `real_model_*` + `cc_prep_model_data` + `pkLeafRankAzimPointwise` +
`pkLeafRankCriticalEdge` + `ox3q1hP25`。逐行见 `logs/map_pa25_30.tsv`。

> 任务书写 `ox3q1hP25(:4563)`；实际 `def ox3q1hP25` 在 **:90**（`:4563` 是
> `p25r_mcell4_reparam` 的体内行）。本表一律用 HEAD 实测行号；triage TSV 里
> gamma10/gamma11 等行号（10071/10091）也被 SF-76/ztg4-w1 的行漂推到 10923/10943。

## 2. 30 源逐条全表

列说明：
- **证书 ID / HOL 锚** = HOL 证明体实际消费的 bank / lemma（`get_pack_nonlinear_non_ox3q1h "..."`、
  `Merge_ineq.*`、结构件）。数字 ID 是 HOL `ineq.hl` 的 idv；无数字 ID 的是结构件/引理。
- **盒 & 模板** = Lean `bank_*` def 的 12 参盒（PA21），或"结构装配"。
- **在库** = 需要的 bank/lemma 是否已在 Lean 库（PA21 def+proj / PA25 已证件 / 快照证体）。
- **需发射** = 本波口径（hnl 合取内 bank 消费）下是否需要新 G4 发射；"否"≠"证书已在库"，
  而是"Lean 闭包不需要证书，bank 由 `pack_nonlinear_non_ox3q1h` 承载"。
- **glue** = 目标行 → 消费点（hub 行号）。
- **工时** = agent 工时（1 agent，含读 API/试错；不含 gate 等待）；"0(备料)" = 证体已在
  poolc 快照，只需落库；括号内为从零重推的参考。
- **G4 机时** = 若该条真化到证书层所需机器时（runbook 5–10 机器时/证书 + 2–4h 粘合）；
  0 = 不需要新证书。

### 2.1 26 个 `real_model_*`（:8807 起）

| # | 源（行） | 陈述一句 | 证书 ID / HOL 锚 | 盒 & 模板 | 在库 | 需发射 | glue（消费点） | 依赖（in-file sorry / in-lib） | 工时 | G4 机时 | 风险 | 状态 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `real_model_gamma_qu` :8807 | `qu i → −0.0057 ≤ gg_mcell i` | BIXPCGW **9455898160**（`bank_BIXPCGW9455898160`） | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4 > −0.00569` | 在库（PA21:601/proj）；证体 poolc-w4 | 否 | 8807 → `pkrmQu` 合取9 :12004 | 无 in-file sorry；`GG_MCELL_QUARTER`+`MCELL4_DOMAIN` | 0(备料)/2–4 | 0 | 低 | **B0 replay** |
| 2 | `real_model_fhbv2_sym` :8930 | `0.0057 ≤ gg`（fhbv2 镜像支） | FHBVYXZv2**a**（`bank_FHBVYXZv2a`） | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4>0.0057 ∨ rad2>2 ∨ eta(y1,y3,y5)²<1.34²` | 在库（PA21:638/proj）；证体 poolc-w4 | 否 | 8930 → `pkrmQu` 合取10 :12010 | 无；`GG_MCELL_QUARTER`+`MCELL4_DOMAIN`+23-换位私件 | 0(备料)/2–4 | 0 | 低–中 | **B0 replay** |
| 3 | `real_model_gckb` :9056 | `0.606 ≤ azim_mcell i` | GCKBQEA（`bank_GCKBQEA`） | `[2hmin,2hplus]×[2,√8]⁵`；`dihY > 0.606` | 在库（PA21:920/proj）；证体缺 | 否 | 9056 → `pkrmAzim` 合取5 :11921 | 无 in-file sorry；4-胞支机械，3-胞支几何来源未定位 | 8–16 | 0 | 高 | B5 |
| 4 | `real_model_sum_azim` :9065 | `∑_{i<n} azim_mcell i = 2π` | 无 bank；HOL 消费 `LEAF_RANK_GRUTOTI`（OXLZLEZ3:6086） | —（扇形和恒等式） | 缺（无在库恒等式） | 否 | 9065 → `pkrmAzim` 合取7 :11930；`LEAF_RANK_PROPS` :9157 | `LEAF_RANK_GRUTOTI` :2767（sorry） | 16–40 | 0 | 极高 | B5 |
| 5 | `real_model_ox3q1h_merge` :9168 | `n=4` quarter 模式 → `0 ≤ ∑ gg` | `ox3q1hP25`（外部锚；无数字 ID） | Oxl_def.hl 230 record×5 支（本体缺） | 缺（def 本体） | 否（本波冻结） | 9168 → `pkrmQuarter` :11957 | `ox3q1hP25`（直源）；`GG_MCELL_*`（已证） | 4–8（body 到位后） | 0–10（A2 另计） | 高 | B5/no-go |
| 6 | `real_model_quqy` :9560 | `qu i ∧ qy(i+1) → 0 ≤ gg i + gg3a(i+1)` | `g_quqya_g_quqyb_ALT`（Merge_ineq；未移植） | quarter+3-胞组合；ALT 盒未落 Lean | 部分 | 否（需 Lean 引理移植） | 9560 → `pkrmQu` 合取12 :12022 | `gamma4fgcy_POS`、`critical_weight1a/1b`、3-胞 kit | 4–8 | 0 | 中–高 | B3 |
| 7 | `real_model_quqy_sym` :9576 | `qu(i+1) ∧ qy i → 0 ≤ gg3b i + gg(i+1)` | 同上 | 同上 | 部分 | 否 | 9576 → `pkrmQu` 合取13 :12028 | 同上 | 4–8 | 0 | 中–高 | B3 |
| 8 | `real_model_azim1` :9603 | `qu i → −0.0659+0.042·azim ≤ gg` | QITNPEA **5653753305**（`bank_QITNPEA5653753305`） | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4+0.0659−0.042·dihY>0` | 在库（PA21:591/proj）；证体 poolc-w4 | 否 | 9603 → `pkrmQu` 合取15 :12037 | 无；`GG_MCELL_QUARTER`+`MCELL4_DOMAIN` | 0(备料)/2–4 | 0 | 低 | **B0 replay** |
| 9 | `real_model_gaz4` :9616 | `qu i → −0.0142852+0.00609451·azim ≤ gg` | QITNPEA **6206775865**（`bank_QITNPEA6206775865`） | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4+0.0142852−0.00609451·dihY>0` | 在库（PA21:581/proj）；证体 poolc-w4 | 否 | 9616 → `pkrmQu` 合取16 :12042 | 无 | 0(备料)/2–4 | 0 | 低 | **B0 replay** |
| 10 | `real_model_gaz6` :9629 | `qu i → 0.161517−0.119482·azim ≤ gg` | QITNPEA **3848804089**（`bank_QITNPEA3848804089`） | `[2hmin,2hplus]×[2,2hmin]⁵`；`γ4−0.161517+0.119482·dihY>0` | 在库（PA21:563/proj）；证体 poolc-w4 | 否 | 9629 → `pkrmQu` 合取17 :12047 | 无 | 0(备料)/2–4 | 0 | 低 | **B0 replay** |
| 11 | `real_model_gamma_qx` :9642 | `qx i → 0 ≤ gg i` | `gamma_qx_ALT`（Merge_ineq；Lean 走 `GLFVCVK4` / `GLFVCVK4a8328676778`） | `[2hmin,2hplus]×[2,√8]⁵`（GLFVCVK4） | 在库（bank+proj）；证体 poolc-w4 | 否 | 9642 → `pkrmQx` 合取18 :12095 | 无；`GG_MCELL_BETA/NONBETA`+GLFVCVK4 banks | 0(备料)/3–6 | 0 | 低–中 | **B0 replay** |
| 12 | `real_model_g_qxd` :9655 | `qx i ∧ 2.3<azim i → 0.0057 ≤ gg i` | `g_qxd_ALT`（Merge_ineq；Lean 走 BIXPCGW **1738910218a2/7080972881a2/7274157868a**） | 三 bank 盒（PA21:741–758） | 在库（bank+proj）；证体 poolc-w5 | 否 | 9655 → `pkrmQx` 合取19 :12101 | 无；`p25w4_dihY_sym23/26` 私件 | 0(备料)/3–6 | 0 | 低–中 | **B0 replay** |
| 13 | `real_model_gamma10` :10923 | `qx i ∧ ¬(all small) ∧ small_i ∧ ¬cc_4(i+1) → 0.0057 ≤ gg i + γ(ccCell B)·W` | `gamma10_gamma11_ALT`（Merge_ineq；未移植） | 3-胞组合；ALT 盒未落 Lean | 部分 | 否（需 ALT 移植） | 10923 → `pkrmQx` 合取20 :12107 | `critical_weight1a/1b`、3-胞 kit（cell23/008/3a/3b） | 6–10 | 0 | 高 | B3 |
| 14 | `real_model_gamma11` :10943 | `qx(i+1) ∧ … ∧ ¬cc_4 i → 0.0057 ≤ γ(ccCell B)·W + gg(i+1)` | `gamma10_gamma11_ALT` + GLFVCVK4 **2477216213** + CIHTIUM | `[2hmin,2hplus]×[2,√8]⁵` | 部分 | 否（ALT 移植） | 10943 → `pkrmQx` 合取21 :12114 | `critical_weight1a/1b`、`leaf_CIHTIUM`、3-胞 kit | 6–10 | 0 | 高 | B3 |
| 15 | `real_model_gamma8` :11035 | `qx i ∧ ¬(all small) ∧ small_i ∧ ¬small(i+1) → 0.0057 ≤ gg i` | `QITNPEA4 9063653052_weak_ALT`（未移植）+ `gamma4fgcy_POS` | QITNPEA1 模板（i3,i4∈{1,2}×{0,1,2}） | 部分 | 否（ALT 移植；可能需多 bank 剥案） | 11035 → `pkrmQx` 合取22 :12121 | `leaf_CIHTIUM`、`gamma4fgcy_POS`、3-胞 kit | 8–16 | 0–5 | 高 | B4（条件） |
| 16 | `real_model_gamma8b` :11051 | `qx i ∧ ¬(all small) ∧ small(i+1) ∧ ¬small i → 0.0057 ≤ gg i` | 同上 | 同上；w5 记 **bank 级缺口**（`¬(y3,y5 small)` 形无现成盒） | 缺（bank 级） | **是**（若真化需新 bank/证书） | 11051 → `pkrmQx` 合取23 :12127 | `leaf_CIHTIUM`、`gamma4fgcy_POS`、3-胞 kit | 8–16 | 5–10 | 极高 | **B4/no-go** |
| 17 | `real_model_gaz9` :11067 | `qx i ∧ ¬(all small) ∧ small_i → 0.213849−0.119482·azim ≤ gg` | QITNPEA **2134082733** + QITNPEA **9939613598** + `gamma4fgcy_POS` | `[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]²` | 在库（bank+proj）；证体 poolc-w5 | 否 | 11067 → `pkrmQx` 合取24 :12133 | 无；`p25w5_bump_mem` 私件 | 0(备料)/3–6 | 0 | 低–中 | **B0 replay** |
| 18 | `real_model_azim2` :11083 | `qx i ∧ … ∧ 2hplus<d(i,i+1) → 0.00457511+0.00609451·azim ≤ gg` | QITNPEA **9939613598** | `[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]²` | 在库（PA21:711/proj）；证体 poolc-w4 | 否 | 11083 → `pkrmQx` 合取25 :12139 | 无；`GG_MCELL_NONBETA` | 0(备料)/3–6 | 0 | 低–中 | **B0 replay** |
| 19 | `real_model_cell23` :11203 | `¬cc_4 i → γ(A)W + γ(B)W ≤ gg i` | 结构：`CC_3_PROPS` + `CC_3_SUM_fn`（OXLZLEZ3:7924） | — | 部分（`CC_3_PROPS` 已证；`real_model_008` 缺） | 否 | 11203 → `pkrmQy` 合取26 :12187 | `real_model_008`、`CC_3_SUM_fn` | 2–4（008 后） | 0 | 中 | B3 |
| 20 | `real_model_3a` :11258 | `¬cc_4 i → 0 ≤ γ(A)W` | 结构：`TSKAJXY_3` + `cell3_bank` + `CC_3_PROPS` | — | 在库（PA21 `cell3_from_ineq_thm`）；证体 poolc-w6 | 否 | 11258 → `pkrmQy` 合取27 :12191 | 无；`mcell3_gammaX_gamma3f` | 0(备料)/2–4 | 0 | 低 | **B0 replay** |
| 21 | `real_model_3b` :11269 | `¬cc_4 i → 0 ≤ γ(B)W` | 同上 b 侧 | — | 在库；证体 poolc-w6 | 否 | 11269 → `pkrmQy` 合取28 :12195 | 无；`mcell3_gammaXb_gamma3f` | 0(备料)/2–4 | 0 | 低 | **B0 replay** |
| 22 | `real_model_gr` :11280 | `¬cc_4 i → 0.008·azim ≤ gg i` | 结构：`real_model_cell23_008` + `GAMMAX_008a/b` | — | 部分 | 否 | 11280 → `pkrmQy` 合取29 :12199 | `real_model_cell23_008`、`GAMMAX_008a/b` | 2–4（kit 后） | 0 | 中 | B3 |
| 23 | `real_model_pema` :11320 | `¬cc_4 i ∧ hl i<1.34 ∧ ¬hl(i+1)<1.34 ∧ azim<1.074 → spine5 ≤ gg` | PEMKWU（`bank_PEMKWU`） | `[2hmin,2hplus]×[2,√8]×[2,2hmin]×[2,√8]×[2,2hmin]×[2,√8]` | 在库（PA21:516/proj） | 否 | 11320 → `pkrmQy` 合取30 :12204 | `real_model_cell23_008` | 3–6（kit 后） | 0 | 中 | B3 |
| 24 | `real_model_pemb` :11332 | `¬cc_4 i ∧ ¬hl i<1.34 ∧ hl(i+1)<1.34 ∧ azim<1.074 → spine5 ≤ gg` | PEMKWU + IXPOTPA/TXQTPVC/TEWNSCJ + FCHKUGT | 同上 | 在库（bank+proj） | 否 | 11332 → `pkrmQy` 合取31 :12209 | `real_model_cell23_008` | 3–6 | 0 | 中 | B3 |
| 25 | `real_model_txq` :11780 | `qy i ∧ small_eta i ∧ small_eta(i+1) ∧ 1.946≤azim≤2.089 → 3cc_eps ≤ gg` | TXQTPVC（`bank_TXQTPVC`） | `[2hmin,2hplus]×[2,2hmin]²×[2,√8]×[2,2hmin]²` | 在库（PA21:485/proj） | 否 | 11780 → `pkrmQy` 合取33 :12220 | `real_model_cell23_008`、`GDRQXLGv3`、`TXQTPVC_MERGED` | 3–6 | 0 | 中 | B3 |
| 26 | `real_model_tew` :11792 | `qy i ∧ small_eta i ∧ small_eta(i+1) → spine5 ≤ gg` | TEWNSCJ（`bank_TEWNSCJ`） | `[2hmin,2hplus]×[2,2hmin]³×[2,√8]×[2,2hmin]²` | 在库（PA21:531/proj） | 否 | 11792 → `pkrmQy` 合取32 :12214 | `real_model_cell23_008`、`TEWNSCJ_MERGED` | 3–6 | 0 | 中 | B3 |

> 注：第 11/12 行的"证书 ID"是 HOL 的 `*_ALT` 引理；poolc-w4/w5 已实证 Lean 可以**绕过**
> 这些未移植引理，直接用 PA21 的 `proj_bank_*` + `GG_MCELL_*` 塌缩完成。第 13/14/15/16 行
> 的 ALT 引理尚未找到等价的 Lean 绕行，故列为"部分"。
>
> 另：任务书说的 `NEEDS: ...逐条证书` 注记在 PA25 里是 **hub 级**（`pkrmAzim` :11905、
> `pkrmQuarter` :11937、`pkrmQu` :11966、`pkrmQx` :12053、`pkrmQy` :12145），**不是逐源级**；
> 逐源的证书 ID/盒由本表从 HOL `OXLZLEZ3.hl` 的 `real_model_*` 证明块反推（见 Evidence E4.1）。

### 2.2 4 个非/半 farm 件

| # | 源（行） | 陈述一句 | 证书/锚 | 在库 | 需发射 | glue（消费点） | 依赖 | 工时 | G4 机时 | 风险 | 状态 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 27 | `cc_prep_model_data` :5870 | `leaf_rank → cc_bool_prep_v11 (cc_data_v8)`，即**相邻两位不能同时 qy**（`¬cc_4`） | 无 bank；HOL 结构（OXLZLEZ3:4021，~100 行 MESON） | **在库：全部依赖已证**（`K4_CC_WI_ALT/WIM`、`CC_KE_34`、`EL_CC_UH`、`STEM_EDGEX`、`ZASUVOR`、`s_leaf_leaf`、`LEAF_RANK_S_LEAF/TRUNCATE`、`PERIODIC_EQ_IMAGE`） | 否 | 5870 → `LEAF_RANK_PROPS` :9165 | 无 in-file sorry | **4–8** | 0 | 中 | **B1 GO（唯一真闭包候选）** |
| 28 | `pkLeafRankCriticalEdge` :9111 | `¬cellClusterInequality → ∃ 临界茎 + 负 gg 和` | 无 bank；HOL Oxl_real.hl（**不在仓内**） | 部分（`LEAF_RANKING_LEMMA` 已证；两上游 sorry） | 否 | 9111 → `LEAF_RANK_PROPS` :9153 | `CELL_CLUSTER_ESTIMATE_REDUCE` :5714、`CELL_CLUSTER_N_LE_1` :5986 | 3–6（搬债）/20–40（真证） | 0 | 高 | B5（defer） |
| 29 | `pkLeafRankAzimPointwise` :9127 | `∀i, azim_mcell i = azim u0 u1 (f i) (f(i+1))` | 无 bank；HOL Oxl_real.hl（不在仓内） | 部分（`CC_3_PROPS`、`c_4_azim_mcell_dih_y` 已证；`MCELL_WEDGE_UNIQUE` 缺） | 否 | 9127 → `LEAF_RANK_PROPS` :9160 | `MCELL_WEDGE_UNIQUE` :2448 | 2–4（搬债）/12–20（真证） | 0 | 高 | B5（defer） |
| 30 | `ox3q1hP25` :90 | opaque def：cc_v11 4-quarter 认证 bank | `ox3q1hP25`（Oxl_def.hl；**本体不在仓内**） | 缺（外部锚） | 否（本波冻结） | 90 → `real_model_ox3q1h_merge` :9169；`OXLZLEZ` :12284 | 自身是锚 | 16–40（body 转录+A2 接线） | 0–10（A2 若重发） | 极高 | **B5/no-go** |

## 3. 消费图（glue 行号）

```
OXLZLEZ (:12284, hox : ox3q1hP25)
 └─ CELL_CLUSTER_ESTIMATE_PROPS (:12260)
     ├─ LEAF_RANK_PROPS (:9140)                       [已证，真装配]
     │   ├─ pkLeafRankCriticalEdge (:9111)  ← #28      [直源]
     │   ├─ real_model_sum_azim (:9065)     ← #4       [直源]
     │   ├─ pkLeafRankAzimPointwise (:9127) ← #29      [直源]
     │   ├─ cc_bool_model_data (:5752)                 [已证]
     │   └─ cc_prep_model_data (:5870)      ← #27      [直源]
     └─ cc_real_model_data (:12228)                   [已证装配]
         ├─ pkrmPeriodic (:11885)                      [已证]
         ├─ pkrmAzim (:11907)   ← gckb #3 / azim_c4 / sum_azim #4
         ├─ pkrmQuarter (:11938)← ox3q1h_merge #5
         ├─ pkrmQu (:11967)     ← gamma_qu #1 / fhbv2_sym #2 / quqy #6 / quqy_sym #7 / azim1 #8 / gaz4 #9 / gaz6 #10
         ├─ pkrmQx (:12054)     ← gamma_qx #11 / g_qxd #12 / gamma10 #13 / gamma11 #14 / gamma8 #15 / gamma8b #16 / gaz9 #17 / azim2 #18
         └─ pkrmQy (:12146)     ← cell23 #19 / 3a #20 / 3b #21 / gr #22 / pema #23 / pemb #24 / tew #26 / txq #25
```

`PACKING_CHAPTER_MAIN_CONCLUSION` (:12302) = `RDWKARC_concl` + `OXLZLEZ` + `TSKAJXY`。
c1 后 Assembly 消费的是 `PackingConcl.PACKING_CHAPTER_MAIN_CONCLUSION_discharged`，
其 `hcc` 支 = 本图的 `OXLZLEZ`，所以 **30/30 都在 c1 端点的祖先锥**（见 §6）。

## 4. 56 项 sorry 与 30 直源的关系（26 项非直源逐条）

HEAD 56 = **30 直源** + **26 非直源**。26 非直源**当前 Lean 源里零引用**（只出现在
docstring/注释或自身声明处；见 Evidence E9），所以不在 map 的直源表；但按 HOL 证明图，
它们几乎全是这 30 条的**前置 kit**。分类如下：

| 非直源（行） | 角色 | HOL 消费它的位置 | 归到哪条直源 | 现状 |
|---|---|---|---|---|
| `MCELL_WEDGE_UNIQUE` :2448 | 楔唯一性 | `LEAF_RANK_BIJ`（1472） | `pkLeafRankAzimPointwise` 链 | kit |
| `LEAF_RANK_BIJ` :2756 | leaf-rank 双射 | `LEAF_RANK_GG_SUM`（1558） | 同上 | kit |
| `LEAF_RANK_GG_SUM` :2778 | gg 和 | `LEAF_RANK_PROPS`（4758） | 同上 | kit |
| `LEAF_RANK_GRUTOTI` :2767 | azim 和 = 2π | `real_model_sum_azim`（6086）、`LEAF_RANK_PROPS`（4768） | `real_model_sum_azim` #4 | kit |
| `MCELL3_DOMAIN` :3168 | 3-胞域 | `MCELL3_008`（7833） | 008 链 | kit |
| `TSKAJXY_3` :3176 | 3-胞 TSKAJXY | `real_model_3a/3b`（8150/8185） | #20/#21（**但 B0 用 `cell3_from_ineq_thm` 绕开**） | **树外死 kit（B0 路线下）** |
| `CELL_CLUSTER_ESTIMATE_REDUCE` :5714 | 逐边化 | `pkLeafRankCriticalEdge`（docstring） | #28 | kit（深） |
| `CELL_CLUSTER_N_LE_1` :5986 | 退化茎非负 | `pkLeafRankCriticalEdge`（docstring） | #28 | kit（深） |
| `critical_weight1` :9535 | 临界权 | `real_model_quqy`（6524） | #6/#7/#13/#14 | **B0 关闭** |
| `critical_weight1a` :9546 | 同上 | quqy/gamma10/11（6590/6978） | #6/#7/#13/#14 | **B0 关闭** |
| `critical_weight1b` :9557 | 同上 | quqy/gamma10/11（6643/7040） | #6/#7/#13/#14 | **B0 关闭** |
| `leaf_CIHTIUM` :10967 | 长叶不可能 | `real_model_gamma8/8b/gamma11`（7180/7265/7078） | #14/#15/#16 | kit |
| `gamma4fgcy_POS` :11032 | γ 正性 | `gamma8/8b/gaz9`（7198/7283/7361） | #15/#16/#17 | kit |
| `CC_3_SUM_SET` :11114 | 3-胞集合拆分 | `real_model_008` | #19/#22–#26 | kit |
| `CC_3_SUM_fn` :11129 | 3-胞求和拆分 | `real_model_cell23`（7949） | #19 | kit |
| `EDGE_IMP_K23` :11143 | k=2/3 | `real_model_008`（7891） | #19/#22–#26 | kit |
| `CC_2_PROPS` :11156 | 2-胞性质 | `real_model_008` | #19/#22–#26 | kit |
| `MCELL2_CRITICAL_WEIGHT1` :11164 | 权=1 | `real_model_008` | 同上 | **B0 关闭** |
| `MCELL3_CRITICAL_WEIGHT` :11173 | 权=1/wtcount | `real_model_008` | 同上 | **B0 关闭** |
| `MCELL3_008` :11182 | `0.008·dihX ≤ γW` | `real_model_008`（7924） | 同上 | kit |
| `real_model_008` :11200 | 剩余项 0.008 | `real_model_cell23_008`（8042） | #19/#22–#26 | kit |
| `real_model_cell23_008` :11231 | cell23+008 | `gr/pema/pemb/txq/tew`（8215/8281/8392/8736/8858） | #22–#26 | kit |
| `GAMMAX_008a` :11243 | 0.008 下界 | `real_model_gr`（8223） | #22 | kit |
| `GAMMAX_008b` :11255 | 同上 | `real_model_gr`（8225） | #22 | kit |
| `CC_3_AZIM_LT_PI_COPLANAR` :11777 | azim<π 共面 | `real_model_txq`（8760） | #25 | kit |
| `HL_IMP_BARV` :12564 | barV 2→3 | HOL `RAD_PI_IMP_WEDGE4`（4279）；**Lean `RAD_PI_IMP_WEDGE4` 已证且不消费它** | 无（死 kit） | **树外** |

**结论**：
- 30 直源里 29 theorem 的体都是 `sorry`，所以它们**当前不消费任何 kit**；上表的"归到哪条"
  是**填体后按 HOL 图会消费**的关系。
- 26 非直源中 **24 条**是 30 源的直接/传递前置；**2 条是树外死 kit**：
  `HL_IMP_BARV`（Lean `RAD_PI_IMP_WEDGE4` 已证且不消费它）与 `TSKAJXY_3`
  （B0 的 3a/3b 走 `cell3_from_ineq_thm` + `mcell3_gammaX*_gamma3f`，不消费它；
  若将来重推 3a/3b 的 HOL 路线才会复活）。
- **5 条非直源（`critical_weight1/1a/1b`、`MCELL2_CRITICAL_WEIGHT1`、`MCELL3_CRITICAL_WEIGHT`）
  会被 B0 replay kit 一并关闭**，所以 B0 的实际文件级收益 = 56 → 40（−16：11 直源 + 5 kit）。

## 5. 4 个非/半 farm 件：可行性与 kit 判定

### 5.1 `cc_prep_model_data`（:5870）——唯一真闭包候选，**备料到可消费**

- 陈述展开：`cc_bool_prep_v11 (cc_data_v8 V f u0 u1)` = `∀ i, cc_qy_v11 … i → ¬cc_qy_v11 … (i+1)`；
  由 `cc_real_dat_def`（探针已核）`cc_qy_v11 (cc_data_v8 …) = fun i => ¬cc_4 … i`，
  目标等价于 **`∀ i, ¬cc_4 i → cc_4 (i+1)`**（相邻两位不能同时非 4-胞）。
- HOL 证法（OXLZLEZ3:4021–4128）：取 `i`，反设 `¬cc_4 i` 且 `¬cc_4 (i+1)`；用
  `cc_uh V [u0,u1,f(i+1)]` 造 4-胞见证；`CC_KE_34` 分 k=4 / k=3：
  - k=4：`ccCell = mcell4 (ccUh)`，`EL_CC_UH` + `STEM_EDGEX` + **`K4_CC_WI_ALT`**（在 i+1）
    给 `ccCell ⊆ wedgeGe … (f(i+1)) (f(i+2))`，即 `cc_4 (i+1)`，矛盾；
  - k=3：证 `ccKe V [u1,u0,f(i+1)] = 4`，再用 **`K4_CC_WIM`**（在 i+1）+ 周期性
    `f(i+1+n-1) = f i` 给 `ccCell V [u1,u0,f(i+1)] ⊆ wedgeGe u0 u1 (f i) (f(i+1))`，
    即 `cc_4 (i+1)`，矛盾。
- **所有依赖已在库且已证**（探针 E5 逐个 `#check` 通过）：`K4_CC_WI_ALT`(:5219)、
  `K4_CC_WIM`(:5320)、`CC_KE_34`(PA18:3038)、`EL_CC_UH`(PA18:3220)、
  `STEM_EDGEX`(PA18:7388)、`ZASUVOR`(PA18:2345)、`s_leaf_leaf`(:1913)、
  `LEAF_RANK_S_LEAF`(:4728)、`LEAF_RANK_TRUNCATE`(:4721)、`PERIODIC_EQ_IMAGE`(:883)、
  `CC_CELL_NOT_NULLSET`(PA18)、`cc_uh_exists`(PA18:1080)。
- **无 in-file sorry 依赖 → 真闭包，不是搬债**。估 **4–8 agent-h**，~150–250 行；
  风险中（Lean 侧周期/index 算术 + `ccKe`/`ccCell` 定义展开）。
- 本波**未交 diff**：按 §0 硬约束不能整文件编译，未验证的证体不得进 kit。已交的是
  **可消费的 API 清单 + 证法映射 + 探针原文**（Evidence E5），下一车道可直接开工。

### 5.2 `pkLeafRankAzimPointwise`（:9127）——搬债式，**不建议本波做 kit**

- 陈述：`∀ i, azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f(i+1))`。
- 依赖：`CC_3_PROPS`（已证）、`c_4_azim_mcell_dih_y`（已证）、**`MCELL_WEDGE_UNIQUE`（:2448 sorry）**。
- 若只用 `MCELL_WEDGE_UNIQUE` 做装配：可把本直源变成真证明，但 `MCELL_WEDGE_UNIQUE` 会成为
  新的直源（当前不在 map 直源表，因为没人引用它）；**文件级 sorry 56→55，map SORRIED
  可能不降（搬债）**。真闭包需先证 `MCELL_WEDGE_UNIQUE`（HOL 1109–1443，~334 行）。
- 估：搬债装配 2–4h；真证 12–20h。**B5 defer**。

### 5.3 `pkLeafRankCriticalEdge`（:9111）——搬债式，**不建议本波做 kit**

- 陈述：`¬cellClusterInequality → ∃ u0 u1 n w0 f, … ∧ ∑ gg < 0`。
- 依赖：`CELL_CLUSTER_ESTIMATE_REDUCE`（:5714 sorry，HOL ~326 行）、
  `CELL_CLUSTER_N_LE_1`（:5986 sorry，HOL ~500 行）、`LEAF_RANKING_LEMMA`（已证）。
- 搬债装配 3–6h；真证 20–40h（两件 HOL Oxl_real.hl 深几何，且 Oxl_real.hl 不在仓内）。
  **B5 defer**。

### 5.4 `ox3q1hP25`（:90）——**NO-GO**

- 现体：`def ox3q1hP25 : Prop := sorry`；PA25 头注："NEEDS: exact Oxl_def.hl body"；
  triage："230 record×5 支"。
- `Oxl_def.hl` **不在仓内**（`reference/flyspeck/text_formalization/packing/` 只有
  `OXLZLEZ1.hl`；`Oxl_def.hl`/`Oxl_real.hl`/`Merge_ineq.hl` 均缺）。
- 仓内唯一可见的近似是 `OXLZLEZ1.hl` 里 `cc_real_model_v11` 的 n=4 conjunct（注释 `// ox3q1h`），
  但**不能据此断言** `ox3q1hP25` 的完整本体（230×5 支）就是这一条；陈述冻结纪律下不得猜。
- 结论：**不交 kit、不排产**；需先补 `Oxl_def.hl` 正本 + A2 证书/接线。

## 6. 与 PackingConcl c1 的关系（D）

| c1 定理 | 位置 | 30 源中的祖先数 | 说明 |
|---|---|---|---|
| `rdwkarcConcl_pc` | `PackingConcl.lean:591` | **0/30** | 只消费 PA19 `UPFZBZM` + `JGXZYGW_KY` + 三个私 kit；`hcc`/`hT` 是**参数**，不引用 PA25 的 30 源。 |
| `RDWKARC_concl_discharged` | `PackingConcl.lean:703` | **0/30** | 体 = `rdwkarcConcl_pc`（c1 把原来的假 `:= RDWKARC` 修掉）。 |
| `PACKING_CHAPTER_MAIN_CONCLUSION_discharged` | `PackingConcl.lean:716` | **30/30** | `hcc` 支 = `OXLZLEZ`（PA25:12284）→ `CELL_CLUSTER_ESTIMATE_PROPS` → `LEAF_RANK_PROPS` + `cc_real_model_data` → 全部 30 源；`hT` 支 = PA21 `TSKAJXY`（不涉 30 源）。 |
| `Assembly.textCapstone` | `Assembly.lean:6989` | 30/30（经上一条） | c1 把消费端点从 PA25 `PACKING_CHAPTER_MAIN_CONCLUSION` 换成 `PACKING_CHAPTER_MAIN_CONCLUSION_discharged`；30 源的 parent 边未变。 |

**哪些"不会"被 c1 影响**：
- `rdwkarcConcl_pc` / `RDWKARC_concl_discharged` 的 axiom 面**不含任何 PA25 30 源**；
  关不关 30 源都不改这两个定理的 `sorryAx`。
- 30 源中没有任何一条是 c1 的**下游**（c1 在它们上面，不在下面）；c1 不改它们的陈述/证明/父边。
- `PACKING_CHAPTER_MAIN_CONCLUSION_discharged` 的 `hT` 支（PA21 `TSKAJXY`）与 30 源无关；
  但同一条定理的 `hcc` 支把 30 源全部拉进祖先锥，所以**整体上 30/30 都会削它的 `sorryAx`**。
- c1 的 map 变化（123→129，新增 PA15×5 + PA16 `QZYZMJC` + PA2 `GRUTOTI1_concl`，
  `UPFZBZM_concl` 出锥）**没有增删 30 源的行**；30 源仍是 30 行（本波实测 `logs/map_pa25_30.tsv`）。

## 7. 分批排产（6 批）与 go/no-go

### B0（立即，最高 ROI）：poolc-w4+w5+w6 replay（11 直源 + 5 kit）

- **备料已就绪**：`kit-pa25-replay-w4w5w6.diff`（+841/−16；删除面恰 16 行裸 `sorry`；
  `git apply --check` PASS；三方合并 0 冲突；候选在旧基线 76771f7e 上 0 error、21/21 标准三）。
- 关闭：`real_model_gamma_qu`、`fhbv2_sym`、`azim1`、`gaz4`、`gaz6`、`gamma_qx`、`g_qxd`、
  `gaz9`、`azim2`、`3a`、`3b`（11 直源）+ `critical_weight1/1a/1b`、
  `MCELL2_CRITICAL_WEIGHT1`、`MCELL3_CRITICAL_WEIGHT`（5 kit）。
- 预期：PA25 文件级 sorry **56 → 40**；PA25 直源 **30 → 19**；无新 import；无 G4。
- 机时：整文件 standalone 复编 ~37 s（replay 旧日志实测）+ 闸/下游 ~20–40 min；
  **必须在 HEAD 复探 21 项 axioms**（旧基线证据不能直接外推 ztg4-w1 交互）。
- 风险：低–中。唯一已知雷 = G1 `p25w5_bump_mem` 与 SF-76 副本去重（replay 已处理）；
  ztg4-w1 新增的 `gamma4fgcy_sym23P25`/`ztg4w1_*` 与本 kit 的 11 处证明无陈述交集，
  但落库前要按 lane-brief 做整文件 RC=0 + `#print axioms` 逐件。
- **GO**（下一编译窗第一件）。

### B1（非 farm 真闭包）：`cc_prep_model_data`

- 估 4–8 agent-h；无 in-file sorry 依赖；真闭包（不是搬债）。
- 机时：落库闸 ~20–40 min；无 G4。
- 风险：中（周期/index + `ccKe`/`ccCell` 展开）。
- **GO**（与 B0 可并行备料，落库排 B0 后）。

### B2（3-胞 kit 地基）：`MCELL3_008`、`CC_3_SUM_SET/fn`、`EDGE_IMP_K23`、`CC_2_PROPS`、
`real_model_008`、`real_model_cell23_008`、`GAMMAX_008a/b`、`MCELL3_DOMAIN`、
`CC_3_AZIM_LT_PI_COPLANAR`、`leaf_CIHTIUM`、`gamma4fgcy_POS`

- 这些是 B3 十件的公共前置；无 bank 发射（`MCELL3_008` 用 PA21 的 cell3 bank；
  `gamma4fgcy_POS` 用 `gamma4fgcy_sym23P25`/`MCELL4_DOMAIN` 已证件）。
- 估 30–60 agent-h；机时 1–2 机器时（分段 gate）；无 G4。
- 风险：中–高（`MCELL3_008` / `real_model_008` 是 HOL 多 bank 分案；`gamma4fgcy_POS`
  需 `rad2YP25`/`criticalEdgeY` 盒算术）。
- **GO**（B0 落库后开）。

### B3（10 条依赖源）：`cell23`、`gr`、`pema`、`pemb`、`txq`、`tew`、`gamma10`、`gamma11`、
`quqy`、`quqy_sym`

- 前置：B2 的 kit + B0 的 3a/3b/critical_weight1a/1b；`gamma10/11` 另需
  `gamma10_gamma11_ALT` 的 Lean 移植（或从 B2 kit 重推）；`quqy(_sym)` 需
  `g_quqya_g_quqyb_ALT` 的移植（或从 GG_MCELL_QUARTER + 3-胞 kit 重推）。
- 估 30–60 agent-h；机时 1–2 机器时；无 G4。
- 风险：中–高（ALT 引理移植是唯一不确定项；`gamma10/11` 的 3-胞组合账最重）。
- **GO after B2**。

### B4（bank 缺口）：`gamma8` / `gamma8b`

- `gamma8b`：w5 已定级 **bank 级缺口**（`¬(y3,y5 small)` 形没有现成 bank 盒）；
  真化需**新增 bank 陈述 + 新 G4 证书**（5–10 机器时 + 2–4h 粘合）。
- `gamma8`：可用 `QITNPEA4 9063653052_weak_ALT`（未移植）+ 多 bank 剥案；8–16h，
  但 `gamma8b` 的新 bank 会同时影响它，建议成对处理。
- **NO-GO under 本机冻结**（不发射、不加 bank 陈述）；若用户解冻，单独立项。
- 若只做 `gamma8` 且找到现有 bank 组合，可降级为 **GO-with-risk**，但本波不备料。

### B5（深水/阻塞）：`gckb`、`sum_azim`、`ox3q1h_merge`、`pkLeafRankCriticalEdge`、
`pkLeafRankAzimPointwise`

- `gckb`：4-胞支机械（`bank_GCKBQEA` + `c_4_azim`），3-胞支（全称无 `cc_4` 前提）
  的 0.606 下界几何来源未定位；8–16h；**GO-with-risk**（需先侦察 3-胞支）。
- `sum_azim`：扇形和恒等式无在库件；HOL 用 `LEAF_RANK_GRUTOTI`；16–40h；**GO-with-risk**
  （建议先证 `LEAF_RANK_GRUTOTI`，它同时是 `LEAF_RANK_PROPS` 的 kit）。
- `ox3q1h_merge`：**NO-GO**（`ox3q1hP25` body 缺；需 `Oxl_def.hl` 正本）。
- `pkLeafRankCriticalEdge` / `pkLeafRankAzimPointwise`：**defer**；先证
  `CELL_CLUSTER_ESTIMATE_REDUCE`/`CELL_CLUSTER_N_LE_1`/`MCELL_WEDGE_UNIQUE`，否则只是搬债。
- 机时：1–2 机器时 gate；无 G4（除非 ox3q1h 的 A2 证书重发）。

### 排产总表

> 机器时口径：Lean 闭包路线下**逐源没有独立机器时**——一次 PA25 整文件 standalone 复编
> ~37 s（replay 旧日志实测），闸/下游按批 0.5–2 h；表里的"G4 机时"只在把某条真化到
> 证书层（新 bank/新发射）时才有独立成本。

| 批 | 件数 | 直源关闭 | kit 关闭 | agent-h | 机器时（gate） | G4 | 判定 |
|---|---|---|---|---|---|---|---|
| B0 replay | 16 | 11 | 5 | 0（已备料） | 0.5–1 h | 0 | **GO（下一窗）** |
| B1 cc_prep | 1 | 1 | 0 | 4–8 | 0.3–0.7 h | 0 | **GO** |
| B2 3-胞 kit | ~12 | 0 | ~10 | 30–60 | 1–2 h | 0 | **GO after B0** |
| B3 依赖 10 | 10 | 10 | 0 | 30–60 | 1–2 h | 0 | **GO after B2** |
| B4 gamma8/8b | 2 | 2 | 0 | 16–32 | 1 h + 5–10 h cert | 5–10 | **NO-GO（冻结）** |
| B5 深水 | 5 | 2–3 | 0 | 27–76 | 1–2 h | 0 | **部分 GO-with-risk / ox3q1h NO-GO** |

> B0+B1+B2+B3 合计：直源 30 → 8（剩 gckb、sum_azim、ox3q1h_merge、gamma8、gamma8b、
> pkCriticalEdge、pkAzimPointwise、ox3q1hP25）；文件级 sorry 56 → 约 14–16；
> agent 64–128h；机器 3–6h gate；**G4 = 0**。

## 8. 交付物与复现

- `kit-pa25-replay-w4w5w6.diff`：**可选 replay kit**（11 直源 + 5 kit）。
  `git apply --stat` 目标 = `lean/Kepler/Text/PackingAuto25.lean`；`git apply --check` PASS；
  +841/−16；删除面 = 16 行裸 `sorry`。**未在 HEAD 编译；不得据此声称关闭**。
- `logs/map_pa25_30.tsv`：map 的 30 行直源。
- `logs/probe_api.log`：只读 `lean` 探针（导入既有 PA25 olean；唯一 error =
  `Kepler.Text.MCELL4` 不存在，非本计划依赖）。
- `logs/git_apply_check.txt`、`logs/merge_check.txt`。
- `Evidence.md`：全部命令原文与读数。

## 9. 诚实度备注 / 不声称的事

1. **不声称关闭任何 `real_model_*`**。B0 是"已验证候选的重放备料"，落库前必须在 HEAD
   整文件 RC=0 + 闸 + 逐件 `#print axioms`。
2. **不声称 26 条证书已发射/已在库**。本波口径是"hnl 合取内 bank 消费"；证书层
   （G4）状态只按 PA21 bank 是否存在 + poolc 证据分级，未逐张核 `Kepler/Interval/Cases`。
3. **不声称 `cc_prep_model_data` 已证**。只交可消费的 API/证法映射；真证需下一车道
   整文件编译验证。
4. **`ox3q1hP25` 的 230×5 本体未在仓内**；任何"补 body"的提议都必须先拿到 `Oxl_def.hl` 正本。
5. **57 vs 56**：任务书的 57 是 ztg4-w1 前 theorem 计数；HEAD 是 55 theorem + 1 def = 56。
6. 本波**未跑 G4、未跑 `lake`、未改主仓 tracked、未构建重片**；唯一编译类动作是
   只读 `lean` 探针导入既有 olean（Evidence E5）。

—— 完 ——

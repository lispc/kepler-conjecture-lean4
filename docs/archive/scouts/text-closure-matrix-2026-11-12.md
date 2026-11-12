# MATRIX — 剩余 16 条锥内 Text `sorry`：HOL 直接引用闭包 × Lean 现状

只读侦察车道 `text-closure-w1`。**主仓 tracked 零改动、未落库、未 commit、未装 olean、未跑 `lake build` / `auto_gate.sh` / 地图仪器。**

- 侦察起点 HEAD：`981d8d7c`；交付时 HEAD：`915151a3`（期间 5 笔 docs；`git diff --stat 981d8d7c..HEAD -- lean/` 为空，探针基线不受影响；`git status --porcelain` = 0）
- 权威名单：`docs/e2e-reachability-map.tsv` `--- SORRIED ---` 段 Text 16 条（实测：16 条全部存在且体内 `sorry`）
- 探针：**225** 条唯一 `#print axioms`（`/tmp/text-closure-w1/logs/P1..P11`；快照在 `logs/`），一次一个 `nice -n 19 lake env lean`
- HOL 闭包：自建 `reference/flyspeck/**/*.hl` 全量 `let NAME =` 索引（26,879 decl / 17,088 名），取证明体（`prove`/`prove_by_refinement`/`section_proof` 段）**一层**出现的仓库内声明名；HOL 核心规则（`SET_RULE`/`ARITH_RULE`/`MOD_REFL` 等）、tactic、局部 binder 不计。

## 0. 判词口径（先声明）

| 判词 | 定义（本报告一致使用） |
|---|---|
| **GO** | 一层直接上游**零红零缺**（引理 `#print axioms` ⊆ 标准三；定义在树内存在），且所需模块从目标模块**无环可达**。 |
| **PARTIAL** | 一层上游的红/缺**全部落在一个已点名的有界 kit 内**（§2.1b 有 EST，或本报告给出体量），kit 本身无 import 环；列出 kit 清单与体量。 |
| **BLOCKED** | 至少一条一层上游 `sorryAx` / 无陈述 / import 环，且该红件**不是**有界 kit（是章级巨件、无界阶梯、或 DAG 反向边）。点名到声明 + 证据行。 |

- **绿数** = 一层上游中「Lean 声明存在，且引理 `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`（或子集）」的条数；定义只验存在（`def`/结构字段），不跑 axioms。
- **直接上游总数** = 一层 HOL 声明名去重后的总数（引理 + 定义）。OCBICBY 的 `arrow_rewrite_list` 是 HOL 局部 list 值，按它实际展开的 14 条 `empty_*` 计（否则会把 11 条缺陈述藏起来）。
- **红名单**只写 Lean 侧名字（`#print axioms` 实测）；HOL 原名在逐条小节里给。
- **重要前提**：16 条的红上游**无一在 TSV 的 16 条名单内**（见 §3），即没有「目标互相阻塞」；所有红件都是**锥外 sorry**，证目标会把它们拉进锥（`SORRIED` 会先涨）。

---

## 1. 16 行大表

> `Lean 位置` 为当前 HEAD 的 statement 行；`HOL 位置` 的「行数」含 statement + 证明体。
> `红`/`缺` 列只列一层；二阶红在逐条小节里点名。

| # | 目标 | Lean 位置 | HOL 位置（文件:行，行数） | 判词 | 直接上游总数 | 绿数 | 红名单（一层，`#print axioms`） | 缺陈述清单 | 备注 |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `JCYFMRP_p27` | `lean/Kepler/Text/LocalAuto27.lean:495` | `local/JCYFMRP.hl:256-608`（353） | **BLOCKED** | 39 | **39** | **无** | 无 | **全部一层上游绿，但 import 环**：`CUXVZOZ_p21`(LA21)、`MMS_IMP_BBS/BBPRIME/CHANGE_*/ODXLSTCv2/WL_IN_V`(LA28)、`DIST_EDGE_IN_BB_LE_2/BB_RHO_NODE_IVS`(LA26)、`BBS_IMP_CONVEX_LOCAL_FAN`(LA34) 所在模块全在 LA27 **上方**（`LA16:103→LA27`、`LA18:105→LA27`、`LA26:102→LA27`）。LA27 闭包内无 acyclic 供体；`LocalAnchors.scsTerminalEdgeEq2Anchor` 本身 `sorry` |
| 2 | `TFITSKC_p27` | `LocalAuto27.lean:331` | `local/TFITSKC.hl:649-659`（11） | **BLOCKED** | 3 | 2 | `TFITSKCv1_p27` = `[propext, sorryAx, …]` | 无 | 同文件；门是 K2（HOL 491 行，EST 500–650） |
| 3 | `LFLACKU_p23` | `LocalAuto23.lean:303` | `local/JOTSWIX.hl:191-212`（22） | **BLOCKED** | 11 | 10 | `TAUM_STD_POS_p23` = `[propext, sorryAx, …]` | 无 | 双重阻塞：① hNL 注册表（用户保留区）；② `pos_imp_scs_arrow_empty_p22`(LA22) 与 `taustar_taum_dfun`/`FUNLIST_EXPLICIT`(LA38) 均在 LA23 **上方**（`LA22:85→LA23`、`LA38:129→LA23`），import 即环 |
| 4 | `MIQMCSN_p32` | `LocalAuto32.lean:1576` | `local/MIQMCSN.hl:3436-3462`（27） | **BLOCKED** | 21 | 17 | `SCS_4M8_ARROW_STEP_ONE_p32`、`SET_STAB_4M8_ARROW_3T4_p32`、`SCS_4M8_13_ARROW_3T7_p32`、`SCS_4M8_02_ARROW_3T7_p32`（均 `sorryAx`） | 无 | 二阶红 **13 条**（P10 实测全 `sorryAx`：`BB/MM_4M8_IMP_4M6_23/01`、`MIN_NOT_STAND_4M8`、`BB/MM_4M8_IMP_scs_4M8_02/13`、`MM_4M8_IMP_STAB_4M8`、`STAB_4M8_02/13_SCS`、`SCS_4M8_02_ARROW_4M8_13`）；4M8 阶梯共 17 红。K8 235–600 下沿 UNRESOLVED ⇒ BLOCKED |
| 5 | `NWDGKXH_p32` | `LocalAuto32.lean:1030` | `local/MIQMCSN.hl:2110-2122`（13） | **BLOCKED** | 11 | 9 | `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`、`SCS_4T3_IS_SCS_p32` | 无 | kit = K6 的 5 条（另 3 条二阶红：`EXTREMAL_SCS_4M6_p32`、`BB_4M6_IMP_scs_4T3_p32`、`MM_4M6_IMP_MM_4T3_p32`）。**K6 不是有界 kit**：`EXTREMAL_SCS_4M6` 的 HOL 体（`MIQMCSN.hl:1855-1990`）实引 `VASYYAU`(:1887,:1922)/`TUAPYYU`(:1953)，而 LA1 三条 master 全 `sorryAx` ⇒ 与 K7/K8 同闸 |
| 6 | `YOBIMPP_p32` | `LocalAuto32.lean:1241` | `local/MIQMCSN.hl:2453-2484`（32） | **BLOCKED** | 23 | 21 | `SCS_4M7_ARROW_STAB_4M7_4M6_p32`、`STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32` | 无 | 二阶红 6（P10 实测：`MIN_NOT_STAND_4M7`、`BB/MM_4M7_IMP_4M6_12/01`、`MM_4M7_IMP_STAB_4M7`）+ `VASYYAU_concl`/`TUAPYYU_concl`/`WKZZEEH_concl`（LA1，全 `sorryAx`）⇒ K7 原报「无 sorry 门」**不成立** |
| 7 | `OCBICBY_p22` | `LocalAuto22.lean:4093` | `local/OCBICBY.hl:4755-4778`（24） | **BLOCKED** | 28 | 14 | `empty_6T1_p22`、`empty_5T1_p22`（LA22 同文件）、`empty_3T2`（LA38） | **11 条**：`empty_3T1`、`empty_3T3`、`empty_3T4`、`empty_3T5`、`empty_3T6'`、`empty_3T7`、`empty_4T1`、`empty_4T2`、`empty_4T3`、`empty_4T4`、`empty_4T5` | 一层的 `pos_imp_scs_arrow_empty_p22` 绿；14 个合取经 `arrow_rewrite_list`（OCBICBY.hl:4746-4751）展开。`empty_3T2` 在 LA38，`LA38→…→LA22` 反向可达 ⇒ LA22 不能 import LA38（环）。11 条无陈述 + K10 1,400–1,900 |
| 8 | `MM_4I2_IMP_4T2_4T1_p33` | `LocalAuto33.lean:2450` | `local/ARDBZYE.hl:2339-2510`（172） | **PARTIAL** | 34 | 33 | `EDGE_EQ_2_4I2_ALL_p33` | 无 | kit = K3 的 6 条 EDGE 簇（另 5 条二阶红：`EDGE_EQ_2_4I2_p33`、`EXPAND_DIAG_4_DIST_p33`、`EDGE_EQ_2_4I2_1/2/3_p33`），EST 360–520。簇内 `CUXVZOZ_p21` 已绿；全在 LA33 同文件、无环 |
| 9 | `SCS_4I1_IMP_SCS_4I2_p33` | `LocalAuto33.lean:2487` | `local/ARDBZYE.hl:2575-2639`（65） | **BLOCKED** | 28 | 26 | `JCYFMRP_V3_p29`、`JLXFDMJ_p27`（均 `sorryAx`） | 无 | K4b `JLXFDMJ_p27` 600–800（无界巨件）；`JCYFMRP_V3_p29` 又依赖 `JCYFMRP_p27`（第 1 行，import 环）。LA33 能 import LA27/LA29（`LA33:162/163`），DAG 无问题——纯粹内容红 |
| 10 | `SCS_4I2_IMP_SCS_4T1_p33` | `LocalAuto33.lean:1817` | `local/ARDBZYE.hl:1357-1430`（74） | **BLOCKED** | 30 | 28 | 同 #9：`JCYFMRP_V3_p29`、`JLXFDMJ_p27` | 无 | 与 #9 同一前置三元组，一次摊薄；但仍需 K4b |
| 11 | `SCS_5M2_IMP_SCS_5T1_p29` | `LocalAuto29.lean:3651` | `local/HIJQAHA.hl:3579-3945`（367） | **BLOCKED** | 59 | 53 | `JCYFMRP_V3_p29`、`JLXFDMJ_p27`、`IUNBUIG_p18`、`coplanar_aff_gt_simple_p18`、`xrr_le_1553_BB_p29` | `PROPERTIES_GENERIC`（HOL NKEZBFC.hl:460；Lean 无陈述，可由已绿 `PROPERTIES_GENERIC_LOCAL_FAN_p9` 两行得出） | K4b 600–800 + K4c 300–500 + LA18 两条；原报 `EGHNAVX_COLL_SCS_p18` 未出现在一层体（`grep HIJQAHA.hl` 零命中）⇒ 勘误 |
| 12 | `SCS_6I1_BERAK_BY_CSTAB` | `LocalAuto20.lean:1647` | `local/hexagons.hl:1831-1888`（58） | **BLOCKED** | 15 | 14 | `SCS_6I1_IMP_SCS_6T1`（同文件） | 无 | 二阶：`SCS_6M1_IMP_SCS_6T1` 红 → 三条 LA1 wire `RRCWNSJ_concl`/`JCYFMRP_concl`/`JLXFDMJ_concl` 全红。**且 LA20 无法 import LA27/LA26**（`LA27:124→LA24:47→LA20`、`LA26:102→LA27`）⇒ K11「wire 可由 p26/p27 转接」在现 DAG 不成立 |
| 13 | `UAGHHBM_p30` | `LocalAuto30.lean:1204` | `local/UAGHHBM.hl:2501-4085`（1,585） | **PARTIAL** | 28 | **28** | **无** | 2 条 inline 缺口：`isScsV39 (restrictionCs1V39 s i j c)`、`isScsV39 (restrictionCs2V39 s i j c)`（全树无陈述；HOL 体内联 `RESA_TAC`，非具名引理） | 13 条一层引理全绿（5 条 `MM_IS_NOT_*`、`C_LE_2/C_LT_2_IS_SCS`、`PERIODIC_PSORT/CASE_PSORT`、`psort_sym`、`PERIODIC_PROPERTY`、`set_of_list2_explicit`、`IMP_SUC_MOD_EQ`）；kit 120–250；但本体 1,585 HOL / EST 800–1,300 ⇒ 实际冻结 |
| 14 | `URRPHBZ2` | `PackingAuto13.lean:361` | `packing/URRPHBZ2.hl:215-969`（755） | **PARTIAL** | 49 | 47 | `CLOSED_MCELL`、`U0_NOT_IN_CONVEX_HULL_FROM_ROGERS` | 子件缺：`IsClosed (affGe …)`（`Geom/Aff`，CLOSED_MCELL 的 k=2 分支，30–60 行） | `CLOSED_MCELL` 已证 k=0,1,3,≥4，仅 k=2 sorried（读体确认）；K13 180–310；本体 EST 650–950 |
| 15 | `TameLp.fully_surrounded_perimeter_bound` | `TameLp.lean:925` | `formal_lp/hypermap/ineqs/lp_main_estimate-compiled.hl:1530-1538`（9） | **BLOCKED** | 9 | 7 | `WSEWPCH` = `[propext, sorryAx, …]` | `f_surr_localization`（HOL OneFace 节；Lean 无陈述；`f_surr_localization_convex_local` 已由绿 `p22dJ_convexLocalFan` 覆盖） | `Face_representation`→`Hypermap.face_representation` 绿；`sum_face_rho_node1`→`perimSumFaceArc` 绿；`FAN_PERIMETER` 绿。唯一红是 WSEWPCH（章级 1,150 HOL，EST 1,000–1,500） |
| 16 | `real_model_ox3q1h_merge` | `PackingAuto25.lean:10378` | `packing/OXLZLEZ3.hl:6099-6238`（140） | **GO** | 22 | **22** | **无** | 无 | 9 条一层引理全 `[propext, Classical.choice, Quot.sound]`；13 个 Lean 定义/假设参数全部在树（`pack_nonlinear_non_ox3q1h`/`ox3q1hP25` 为 `def`，`hox`/`hnl` 是**假设参数**）。HOL 的 `Merge_ineq.ox3q1h_merge` 在 Lean 由 `hox : ox3q1hP25` 假设替代，不是门 |

**计数**：GO **1**；PARTIAL **3**（#8、#13、#14）；BLOCKED **12**。

---

## 2. 逐条（一层上游明细 / 二阶点名 / 机器证据）

> 每条给：Lean statement、HOL 段、一层引理清单（绿/红）、定义存在性、import 状态、判词理由。
> `g`=标准三，`R`=sorryAx，`x`=定义存在。探针原始输出见 `Evidence.md` 与 `logs/`。

### 1. `JCYFMRP_p27` — BLOCKED（import 环；上游全绿）

- Lean：`LocalAuto27.lean:495`（`:= by sorry` :510）。
- HOL：`JCYFMRP.hl:256-608`（353 行；concl :240）。
- 一层引理 26 条，**全部 g**：`CUXVZOZ_p21`、`MMS_IMP_BBS_p28`、`DIST_EDGE_IN_BB_LE_2_p26`、`J_EMPY_CASES_A_EQ_2_p27`、`BBS_IMP_CONVEX_LOCAL_FAN_p34`、`CVLF_LF_F`、`MMS_IMP_BBPRIME_p28`、`JKQEWGV2_p23`、`CIZMRRH`、`CHANGE_W_IN_BBS_MOD_IS_SCS_p28`、`CHANGE_A_SCS_MOD_p28`、`ODXLSTCv2_p28`、`SCS_M_LE_1_p27`、`SYNQIWN_p22`、`CHANGE_B_SCS_MOD_p28`、`IMP_SUC_MOD_EQ_p25`、`MOD_EQ_MOD_SHIFT_p22`、`WL_IN_V_p28`、`BB_RHO_NODE_IVS_p26`、`IN_V_IMP_AZIM_LESS_PI`、`CARD_MINUS_ONE`→`ncard_diff_singleton_mem`（`Hypermap.lean:3591`，g）、`SUC_MOD_NOT_EQ_p35`、`AURSIPD_p18`、`scs_diag_2_p22`、`EQ_W_L_IN_BBS_p34`、`DIST_EDGE_LE_CSTAB_CASE_LE3_p27`。
- 定义 13 条全 x：`scsGeneric`、`BBprimeV39`、`isScsV39`、`scsDiag`、`scsIsStr`、`cstab`、`ivsRhoNode1_p2`、`lunar_p3`、`ScsV39.k/a/b`（HOL 的 `scs_k/a/b_v39` 是结构字段）、`BBsV39`、`interiorAngle1`。
- **BLOCKED 理由（唯一）**：DAG。上游模块 `LocalAuto21`/`LocalAuto28`/`LocalAuto26`/`LocalAuto34` 都反向可达 LA27：
  `LocalAuto21.lean:102 → LocalAuto16.lean:103 → LocalAuto27`；
  `LocalAuto28.lean:65 → LocalAuto34.lean:86/90 → LocalAuto18.lean:105 → LocalAuto27`；
  `LocalAuto26.lean:102 → LocalAuto27`。
  LA27 现有闭包（100 模块）不含 LA21/LA26/LA28/LA34；LA27 闭包内也无替代供体（`LocalAnchors.scsTerminalEdgeEq2Anchor` 自身 `sorry`）。
- 交叉证据：`jcyfmrp-w1` 同 HEAD 机器实测同一结论（其 `DELIVERY.md` §0/§1.3；DAG 切割后 shadow 编译 RC=0）。

### 2. `TFITSKC_p27` — BLOCKED（K2）

- Lean：`LocalAuto27.lean:331`；HOL `TFITSKC.hl:649-659`（11）。
- 一层：`TFITSKCv1_p27`（**R**）、`ScsV39`（x）、`scsBasicV39`（x）。
- 门：`TFITSKCv1_p27` = `[propext, sorryAx, Classical.choice, Quot.sound]`（`logs/P1.log`）。HOL 体 491 行，EST 500–650。

### 3. `LFLACKU_p23` — BLOCKED（hNL + import 环）

- Lean：`LocalAuto23.lean:303`；HOL `JOTSWIX.hl:191-212`（22）。
- 一层引理：`pos_imp_scs_arrow_empty_p22`（g）、`taustar_taum_dfun`（g）、`FUNLIST_EXPLICIT`（g）、`TAUM_STD_POS_p23`（**R**）。
- 定义 7 条 x：`scsArrowV39`、`scs3I1`、`mkUnadornedV39`、`isEarV39`、`dTame`、`csAdj`、`h0`。
- 红：`TAUM_STD_POS_p23` = `[propext, sorryAx, …]`（`logs/P6.log`）；其根在 `main_nonlinear_terminal_v11` 的 109 项注册表（hNL，用户保留）。
- **附加阻塞（新）**：`pos_imp_scs_arrow_empty_p22` 在 LA22，而 `LocalAuto22.lean:85` 已 `import LocalAuto23` ⇒ LA23 不能 import LA22；`taustar_taum_dfun`/`FUNLIST_EXPLICIT` 在 LA38，而 `LocalAuto38.lean:129` 已 `import LocalAuto23` ⇒ 也不能 import。二者在 LA23 闭包内**无重复件**（全库唯一声明）。

### 4. `MIQMCSN_p32` — BLOCKED（K8 无界）

- Lean：`LocalAuto32.lean:1576`；HOL `MIQMCSN.hl:3436-3462`（27）。
- 一层引理 12：g 8 = `FZIOTEF_TRANS`、`FZIOTEF_UNION`、`FZIOTEF_REFL`、`SCS_4M6_IS_SCS_p29`、`K_SCS_OPP_4M6_p32`、`SCS_4M6_OPP_IS_SCS_p32`、`SCS_OPP_REFL_fb`（p13 版红，但 `FanBaseKit` 版绿且 LA32 可达）、`YXIONXL2_p33`（p13 版红，p33 版绿）。
- 红 4：`SCS_4M8_ARROW_STEP_ONE_p32`、`SET_STAB_4M8_ARROW_3T4_p32`、`SCS_4M8_13_ARROW_3T7_p32`、`SCS_4M8_02_ARROW_3T7_p32`（均 `[propext, sorryAx, …]`，`logs/P2.log`）。
- 二阶红 13（`P10.log` 实测，全 `[propext, sorryAx, …]`）：`BB_4M8_IMP_4M6_23_p32`、`MM_4M8_IMP_MM_4M6_23_p32`、`BB_4M8_IMP_4M6_01_p32`、`MM_4M8_IMP_MM_4M6_01_p32`、`MIN_NOT_STAND_4M8_p32`、`BB_4M8_IMP_scs_4M8_02_p32`、`MM_4M8_IMP_MM_4M8_02_p32`、`BB_4M8_IMP_scs_4M8_13_p32`、`MM_4M8_IMP_MM_4M8_13_p32`、`MM_4M8_IMP_STAB_4M8_p32`、`STAB_4M8_02_SCS_p32`、`STAB_4M8_13_SCS_p32`、`SCS_4M8_02_ARROW_4M8_13_p32`；加 4 条一层红 = 4M8 阶梯共 17 红。K8 原报下沿 235–600 且标 UNRESOLVED ⇒ 判 BLOCKED。

### 5. `NWDGKXH_p32` — BLOCKED（K6 继承 VASYYAU 闸）

- Lean：`LocalAuto32.lean:1030`；HOL `MIQMCSN.hl:2110-2122`（13）。
- 一层引理 6：g 4 = `FZIOTEF_TRANS`、`FZIOTEF_UNION`、`FZIOTEF_REFL`、`SET_STAB_4M6_ARROW_4T5_p33`；R 2 = `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`、`SCS_4T3_IS_SCS_p32`。
- 二阶红 3（K6 其余）：`EXTREMAL_SCS_4M6_p32`、`BB_4M6_IMP_scs_4T3_p32`、`MM_4M6_IMP_MM_4T3_p32`（`P10.log` 全 `sorryAx`）。
- **K6 不是有界 kit**：HOL `EXTREMAL_SCS_4M6`（`MIQMCSN.hl:1855-1990`）实引 `VASYYAU`（:1887、:1922）与 `TUAPYYU`（:1953），二者是 `LocalAuto1` 的 `_concl` shim，探针 `sorryAx`。⇒ 与 K7/K8 同一条 LA1 master 闸（编排者 `10202d55` ERRATA 同向）。判 BLOCKED。

### 6. `YOBIMPP_p32` — BLOCKED（K7 不成立）

- Lean：`LocalAuto32.lean:1241`；HOL `MIQMCSN.hl:2453-2484`（32）。
- 一层引理 14：g 12（`FZIOTEF_TRANS/UNION/REFL`、`SCS_4M6_IS_SCS_p29`、`PRO_EQU_ID1`、`K_SCS_4M6`、`K_SCS_OPP_4M6_p32`、`SCS_4M6_OPP_IS_SCS_p32`、`YXIONXL3`、`PROP_EQU_IS_SCS`、`SCS_OPP_REFL_fb`、`YXIONXL2_p33`）；R 2 = `SCS_4M7_ARROW_STAB_4M7_4M6_p32`、`STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32`。
- 二阶红 6（`P10.log` 实测，全 `sorryAx`）：`MIN_NOT_STAND_4M7_p32`、`BB_4M7_IMP_4M6_12_p32`、`MM_4M7_IMP_MM_4M6_12_p32`、`BB_4M7_IMP_4M6_01_p32`、`MM_4M7_IMP_MM_4M6_01_p32`、`MM_4M7_IMP_STAB_4M7_p32` + `VASYYAU_concl`/`TUAPYYU_concl`/`WKZZEEH_concl`（LA1 三条 master，全 `sorryAx`；`yobimpp-w1` `DELIVERY.md` §1 机器证据）。
- 结论：K7 的 110–165 估算只覆盖中层，不覆盖 LA1 三条 master ⇒ **ERRATA**。

### 7. `OCBICBY_p22` — BLOCKED（11 缺陈述 + 3 红 + 环）

- Lean：`LocalAuto22.lean:4093`（原报 3856 是旧 HEAD，**ERRATA**）；HOL `OCBICBY.hl:4755-4778`（24）。
- 一层真正被 `prove_by_refinement` 用的引理只有 `pos_imp_scs_arrow_empty_p22`（g）；14 个合取由 `arrow_rewrite_list`（`OCBICBY.hl:4746-4751`）展开成 14 条 `empty_*`。
- 14 条中：g 0、R 3（`empty_6T1_p22`、`empty_5T1_p22`、`empty_3T2`）、**缺 11**（`empty_3T1`、`empty_3T3`、`empty_3T4`、`empty_3T5`、`empty_3T6'`、`empty_3T7`、`empty_4T1`–`empty_4T5`）。
- `empty_3T2` 在 LA38；`LA38.lean:129→LA23`，且 `LA22.lean:85→LA23`，`LA38→LA18→LA27→LA24→LA20→LA22` ⇒ LA22 不能 import LA38（环）。
- 定义 13 条全 x；`scs3T6'` 存在（`LocalAuto1.lean:3558`）。

### 8. `MM_4I2_IMP_4T2_4T1_p33` — PARTIAL（K3 360–520）

- Lean：`LocalAuto33.lean:2450`；HOL `ARDBZYE.hl:2339-2510`（172）。
- 一层引理 23：g 22；R 1 = `EDGE_EQ_2_4I2_ALL_p33`。
- 二阶红 5：`EDGE_EQ_2_4I2_p33`、`EXPAND_DIAG_4_DIST_p33`、`EDGE_EQ_2_4I2_1/2/3_p33`（`LocalAuto33` 扫描器实测 9 条 sorried decl，其中 6 条属 EDGE 簇）。
- 簇内 `CUXVZOZ_p21` 绿（已证），全在 LA33 同文件、无环。EST 360–520。

### 9. `SCS_4I1_IMP_SCS_4I2_p33` — BLOCKED（K4b）

- Lean：`LocalAuto33.lean:2487`；HOL `ARDBZYE.hl:2575-2639`（65）。
- 一层引理 18：g 16；R 2 = `JCYFMRP_V3_p29`、`JLXFDMJ_p27`。
- `JLXFDMJ_p27`（`LocalAuto27.lean:559`）本身是巨件（HOL `JLXFDMJ.hl:227-818`，591 行，EST 600–800）；`JCYFMRP_V3_p29` 依赖 `JCYFMRP_p27`（第 1 行，import 环）。
- DAG：LA33 已 import LA27/LA29（`LocalAuto33.lean:162/163`），**不是** DAG 问题；纯内容红。

### 10. `SCS_4I2_IMP_SCS_4T1_p33` — BLOCKED（同 #9）

- Lean：`LocalAuto33.lean:1817`；HOL `ARDBZYE.hl:1357-1430`（74）。
- 一层引理 20：g 18；R 2 = 同 `JCYFMRP_V3_p29`、`JLXFDMJ_p27`。

### 11. `SCS_5M2_IMP_SCS_5T1_p29` — BLOCKED（K4b+K4c）

- Lean：`LocalAuto29.lean:3651`；HOL `HIJQAHA.hl:3579-3945`（367）。
- 一层引理 40：g 34；R 5 = `JCYFMRP_V3_p29`、`JLXFDMJ_p27`、`IUNBUIG_p18`、`coplanar_aff_gt_simple_p18`、`xrr_le_1553_BB_p29`；缺 1 = `PROPERTIES_GENERIC`。
- `PROPERTIES_GENERIC`（NKEZBFC.hl:460）是 `PROPERTIES_GENERIC_LOCAL_FAN`（Lean `PROPERTIES_GENERIC_LOCAL_FAN_p9`，g）的两行推论；只差一个声明壳。
- 勘误：原报的 `EGHNAVX_COLL_SCS_p18` 在 `HIJQAHA.hl` 一层体内**零命中**（`grep EGHNAVX HIJQAHA.hl` 空）；`coplanar_aff_gt_simple_p18` 实测 `sorryAx`。
- EST：K4b 600–800 + K4c 300–500；本体 330–480。

### 12. `SCS_6I1_BERAK_BY_CSTAB` — BLOCKED（DAG + 红链）

- Lean：`LocalAuto20.lean:1647`；HOL `hexagons.hl:1831-1888`（58）。
- 一层引理 7：g 6 = `SCS_6T1_IS_SCS`、`STAB_IS_SCS_p17`、`SCS_6I1_IS_SCS`、`K_SCS_6I1`、`SCS_6I1_BASIC`、`PEDSLGV1`；R 1 = `SCS_6I1_IMP_SCS_6T1`。
- 二阶红：`SCS_6M1_IMP_SCS_6T1`（R）→ `RRCWNSJ_concl`/`JCYFMRP_concl`/`JLXFDMJ_concl`（LA1 三条 wire，全 R）。
- **DAG 阻塞（新）**：`SCS_6M1_IMP_SCS_6T1` 需要 `JCYFMRP_p27`/`JLXFDMJ_p27`，但 LA20 不能 import LA27/LA26：
  `LocalAuto27.lean:124 → LocalAuto24.lean:47 → LocalAuto20`、`LocalAuto26.lean:102 → LocalAuto27`。
  K11 原报「三条 wire 各 15–30 行，可由 p26/p27 转接」在现 DAG **不成立**（LA1 是底部，也无法反向 import）。
- 判 BLOCKED；解锁需把 SCS_6M1/6I1 链上移到 LA27 之后的模块，或做 DAG 切割（与 `jcyfmrp-w1` 的解锁配方同源）。

### 13. `UAGHHBM_p30` — PARTIAL（K14 120–250）

- Lean：`LocalAuto30.lean:1204`；HOL `UAGHHBM.hl:2501-4085`（1,585）。
- 一层引理 13，**全部 g**：`MM_IS_NOT_2EMPTY_SUBDIVISION_C_EQ_AM_p30`、`MM_IS_NOT_1EMPTY_SUBDIVISION_p30`、`MM_IS_NOT_2EMPTY_SUBDIVISION_p30`、`MM_IS_NOT_2EMPTY_SUBDIVISION1_p30`、`MM_IS_NOT_1EMPTY_SUBDIVISION1_p30`、`C_LE_2_IS_SCS_p30`、`C_LT_2_IS_SCS_p30`、`PERIODIC_PSORT_p30`、`CASE_PSORT_p30`、`psort_sym`、`PERIODIC_PROPERTY`、`BumpP4.set_of_list2_explicit`、`IMP_SUC_MOD_EQ_p25`。
- 定义 15 条全 x（`scsArrowV39`、`subdivV39`、`restrictionCs1/2V39`、`override`、`Periodic2`、`psort`、`Periodic`、`MMsV39`、`BBprime/BBprime2/BBs`…）。
- **缺 kit 2**：`isScsV39 (restrictionCs1V39 s i j c)` / `isScsV39 (restrictionCs2V39 s i j c)`。全树无陈述（`grep -rn "isScsV39 *(restriction"` 只命中注释与 `restrictionTyp1/2`）；HOL 在 `UAGHHBM.hl` 体内是 `REWRITE_TAC[is_scs_v39;scs_v39_explicit;override]` 的 inline 子目标（不是具名 `let`）。`LocalAuto30.lean:1201-1202` 自己的注释也这么说。EST 120–250。
- 本体 1,585 HOL / EST 800–1,300 ⇒ 即使 kit 落地也远超 §7；判 PARTIAL（可派发级别：冻结）。

### 14. `URRPHBZ2` — PARTIAL（K13 180–310）

- Lean：`PackingAuto13.lean:361`；HOL `URRPHBZ2.hl:215-969`（755）。
- 一层引理 34：g 32；R 2 = `CLOSED_MCELL`、`U0_NOT_IN_CONVEX_HULL_FROM_ROGERS`；定义 15 条全 x；两个候选 `p12_omega2_eq_circumcenter`/`w13_in_affine_ky_lemma1` 是 PA12/LA14 的 **private** 件（不可 import，需在本文件重导；后者是 `subset_affineSpan` 一行）。
- `CLOSED_MCELL` 读体：k=0/1/3/≥4 分支已证，只有 k=2 分支 sorried；缺 `IsClosed (affGe …)`（`Geom/Aff`，30–60 行）。
- `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS` = Rogers giant（150–250）。本体 EST 650–950。判 PARTIAL（kit 有界，本体 XL）。

### 15. `fully_surrounded_perimeter_bound` — BLOCKED（WSEWPCH）

- Lean：`TameLp.lean:925`；HOL `lp_main_estimate-compiled.hl:1530-1538`（9）。
- 一层引理 6：g 4 = `perimSumFaceArc`（=`sum_face_rho_node1`）、`FAN_PERIMETER`、`p22dJ_convexLocalFan`（覆盖 `f_surr_localization_convex_local`）、`Hypermap.face_representation`（=`lemma_face_representation`）；R 1 = `WSEWPCH`；缺 1 = `f_surr_localization`（HOL OneFace 节，Lean 全树无同名/同义声明）。
- 定义 3 条 x：`PerimeterBound`、`faceSetOfFan`、`ePrime`。
- `WSEWPCH` = `[propext, sorryAx, …]`（`logs/P5.log`），HOL `polar_fan.hl:2213-3363` = 1,150 行，EST 1,000–1,500 ⇒ BLOCKED。`TameLp` 已 import LA16→LA7（`TameLp→LocalAuto16→LocalAuto7`），DAG 可达。
- 注：`MQMSMAB` 探针也红，但它是**下游**（消费本目标），不计入上游；`yk10/yk11` 是 `private`，`#print axioms` 不可达（`logs/P5.log` UNKNOWN），无法独立复核。

### 16. `real_model_ox3q1h_merge` — GO

- Lean：`PackingAuto25.lean:10378`；HOL `OXLZLEZ3.hl:6099-6238`（140）。
- 一层引理 9，**全部 g**：`real_model_sum_azim`、`NUMSEG_LT`、`periodic_sum`、`real_periodic_data`、`LEAF_RANK_PERIODIC`、`GG_MCELL_BETA`、`GG_MCELL_QUARTER`、`MCELL4_DOMAIN`、`c_4_azim_mcell_dih_y`（`logs/P4.log`）。
- 定义 13 条全 x：`Packing`、`saturated`、`s_leaf`、`periodic`、`criticalEdgeY`、`leaf_rank`、`cc_4`、`hminus`、`hplus`、`gg_mcell`、`azim_mcell`、`betaBumpForceY`、`ox3q1hP25`（`hox` 假设）/`pack_nonlinear_non_ox3q1h`（`hnl` 假设）。
- HOL 的 `Merge_ineq.ox3q1h_merge`（`nonlinear/merge_ineq.hl:536`）在 Lean 由 `hox : ox3q1hP25` 假设替代——**不是**上游门（陈述编码选择）。
- 同一文件、无 import 问题。**唯一 strict GO。**

---

## 3. 关键交叉结论

1. **零 intra-list 阻塞**：16 条的任何红上游都不在 TSV 的 16 条名单内（程序化交集 = 空）。所有红件都是**锥外** sorry；证目标会把它们拉进锥（`SORRIED` 先涨后降），这正是 §2.1c「自身只占 ~1/3」的机制。
2. **DAG 反向边是新的硬阻塞类别**（原估算报告未系统检查）：
   - `JCYFMRP_p27`（LA27 ← LA21/LA26/LA28/LA34）；
   - `LFLACKU_p23`（LA23 ← LA22/LA38）；
   - `SCS_6I1_BERAK_BY_CSTAB`（LA20 ← LA27/LA26）；
   - `OCBICBY_p22`（LA22 ← LA38，`empty_3T2`）。
   这四条不是「再证一点」能解的，必须先做 DAG 切割/声明上移（`jcyfmrp-w1` 已给出 LA27 的两处切割配方）。
3. **strict GO 只有 1 条**：`real_model_ox3q1h_merge`（22/22 绿，零缺，同文件）。PARTIAL 3 条（MM_4I2、UAGHHBM、URRPHBZ2）可作为「kit 先行」派发；其余 12 条按 BLOCKED 处理。
4. **`TameLp` 的 `MQMSMAB` 红是下游污染**，不是目标的上游红；审计时不要把它当门。
5. **`UAGHHBM` 的「外部阻塞」其实比原报窄**：13 条具名 HOL 引理全绿，缺的只是 2 条 inline `isScs` 事实（可作 private helper），但本体 1,585 HOL 行使它仍然不可派发。
6. **K6/K7/K8 共用 LA1 master 闸**：`EXTREMAL_SCS_4M6`/`MIN_NOT_STAND_4M7`/`MIN_NOT_STAND_4M8` 的 HOL 体都实引 `VASYYAU`/`TUAPYYU`/`WKZZEEH`，因此 4M6/4M7/4M8 三条梯子**全部**继承同一笔 LA1 债；只有 K3（EDGE 簇，ARDBZYE 无 `VASYYAU`）是干净有界 kit。

---

## 4. ERRATA（相对 `docs/archive/scouts/text-sorry-estimates-2026-11-12.md` / pq §2.1）

> 以本报告探针为准。原文不改，勘误在此。交付时编排者已把 K6/K7/K8 的 VASYYAU 闸记入 `docs/priority-queue.md`（`10202d55`），与本报告 E2/E10 同向。

| # | 原结论 | 本报告实测（HEAD `981d8d7c`） |
|---|---|---|
| E1 | `JCYFMRP_p27`「无外部阻塞」「ROI 最高」 | **BLOCKED（import 环）**：LA21/LA26/LA28/LA34→LA27 反向可达；上游 26 条引理全绿，但 LA27 无法 import 它们。`jcyfmrp-w1` 同结论（编排者 `915151a3` 已入账）。 |
| E2 | `YOBIMPP` K7「无 sorry 门 / 4M7 BB·MM 子件已证或短」 | **不成立**：`MIN_NOT_STAND_4M7_p32` → `VASYYAU`/`TUAPYYU`/`WKZZEEH`（LA1）全 `sorryAx`（`yobimpp-w1` 机器证据）。 |
| E3 | `SCS_6I1` K11「3 条 wire 各 15–30 行，可由 `RRCWNSJ_p26`/`JCYFMRP_p27`/`JLXFDMJ_p27` 转接」 | **在现 DAG 不成立**：LA20 不能 import LA27/LA26（`LA27→LA24→LA20`）；LA1 是最底层，也不能反向 import。需上移/切割。 |
| E4 | `OCBICBY_p22` 位置 `LA22:3856` | 现 HEAD 为 **`LA22:4093`**（旧行号漂移）。 |
| E5 | `SCS_5M2` 新拉入含 `EGHNAVX_COLL_SCS_p18` | `HIJQAHA.hl` 一层体内 **零命中**；实际红件是 `coplanar_aff_gt_simple_p18`（`sorryAx`）+ `IUNBUIG_p18` + `xrr_le_1553_BB_p29`。 |
| E6 | `MIQMCSN`「无外部阻塞」，K8 235–600 下沿 | 4M8 阶梯有 **13 条**二阶声明经 `P10` 实测全 `sorryAx`（`BB/MM_4M8_IMP_*`、`MIN_NOT_STAND_4M8`、`STAB_4M8_*`、`SCS_4M8_02_ARROW_4M8_13`），加 4 条一层红共 17 红；K8 下沿仍 UNRESOLVED ⇒ 判 BLOCKED（原报告也标了 UNRESOLVED，此处只是升级判词）。 |
| E7 | `UAGHHBM`「2 条 isScs 限制件无陈述（外部阻塞）」 | 缺口确认，但不是「外部模块缺件」：是 **2 条 inline 子目标**，可作 private helper；13 条具名一层引理全绿。判 PARTIAL 而非 BLOCKED。 |
| E8 | `LFLACKU` 仅 hNL 阻塞 | 追加 **两条 import 环**（`pos_imp_scs_arrow_empty_p22`@LA22、`taustar_taum_dfun`/`FUNLIST_EXPLICIT`@LA38 都在 LA23 上方）。 |
| E9 | `SCS_OPP_REFL`/`YXIONXL2` 用 `YXIONXL2_p33` 替代 | 确认：`p13` 两件红；`SCS_OPP_REFL_fb`（FanBaseKit）与 `YXIONXL2_p33` 绿，且 LA32 可达 FanBaseKit / 可无环 import LA33。 |
| E10 | `NWDGKXH`「无外部阻塞」，K6 400–565 | **不成立**：HOL `EXTREMAL_SCS_4M6`（`MIQMCSN.hl:1855-1990`）实引 `VASYYAU`(:1887,:1922)/`TUAPYYU`(:1953)，LA1 三条 master 全 `sorryAx` ⇒ K6 与 K7/K8 同闸。判 BLOCKED。（编排者 `10202d55` 已入账同向 ERRATA。） |

---

## 5. UNRESOLVED / 不可探针项

1. `TameLp.yk10_convexLocalFan` / `yk11_perimeterBound_of_core` 是 **private**，`#print axioms` 不可达；本报告对 TameLp 的判词只依赖 `WSEWPCH` 红 + `f_surr_localization` 缺陈述（两者都足够判 BLOCKED）。
2. `UAGHHBM` 的 2 条 `isScs (restrictionCs*)` 体量（120–250）沿用原 EST，未独立重估；HOL 是 1,585 行 `RESA_TAC` bash，实际可能更高。
3. `MIQMCSN` 的 K8 二阶 13 条已逐条探针确认红（`P10.log`），但其**三阶**闭包与总行数仍 UNRESOLVED（4M8 阶梯可能还拉 `BB/MM_4M8_IMP_*` 的更下层）。
4. `NWDGKXH` 的 K6 已确认继承 `VASYYAU`/`TUAPYYU` 闸（E10），不再是「能否拆两笔」的问题；LA1 三条 master 的真实体量未估（HOL `VASYYAU.hl`/`TUAPYYU.hl`/`WKZZEEH.hl`，属 mnt11 lane）。
5. `URRPHBZ2` 的 `p12_omega2_eq_circumcenter`/`w13_in_affine_ky_lemma1` 是上游 private 件，需在 PA13 内重导；后者一行，前者体量未估。

# Text 层锥内 sorry 估算报告（18 条）— lane `text-est-w1`

只读侦察。未改主仓、未落库、未 commit、未编译。

- **读时 HEAD：`d73bc595`**（任务给定基线）
- **交付时 HEAD：`0a1ff76d`**（`g482-482-w4` 落库，`general_482_deformation_p21` 本体真证收口）
- 两 HEAD 之间 Text 层只有 `LocalAuto21.lean` 变动（+764/−5），其余 17 条行号仍按 `d73bc595`/`0a1ff76d` 一致有效。
- 主仓 `git status --porcelain` = 0 行（交付时实测）。

> **最重要的一条动态**：清单第 17 条 `general_482_deformation_p21` 在侦察期间被另一车道真证闭掉
> （`0a1ff76d`，Lean 体 4489–5272 = **784 行**，删除面 = 1 行 `sorry`）。它不是"待估"了，
> 而是**已兑现的校准样本**：HOL 639 行 → Lean 784 行 = **1.23×**。同时它是 6 条下游件的总闸，
> 闸已开——本报告 §C 的施工顺序按"g482 已闭"重排。

---

## 0. 口径与方法（先声明）

### 0.1 目标清单来源

`docs/e2e-reachability-map.tsv` 的 `--- SORRIED ---` 段（第 16–90 行，74 行 = Assembly 56 + Text 18），
Text 段恰为第 73–90 行，与本任务给的 18 条逐一吻合（含 `parent=` 消费方）。已用
`grep -n` 逐条确认，无增无漏。

### 0.2 静态扫描器（本报告的核心证据工具）

`/tmp/textest_w1/scan2.py`：对 `lean/Kepler/Text/*.lean` 逐文件按列 0 的
`theorem|lemma|def|abbrev|instance` 切 decl 区段，**先剥离嵌套块注释 `/- … -/`、行注释 `--` 与字符串**
再判 `\bsorry\b`。第一版未剥注释，把 docstring 里的 "sorry" 误判为体内 sorry（例如
`LEPJBDJ`、`AYQJTMD_p27` 被误报），已修正；本报告所有 sorry 状态均来自剥注释版。
共扫 17,845 个 decl。注意：该扫描只判「体内是否出现字面 `sorry`」，**不判传递依赖**；
传递依赖靠正文 token 交集（`depscan.py`）与 `NEEDS/DISCHARGES` 注释交叉。

### 0.3 移植系数（标定）

采用**分类系数**，不是单一数字：

| 类别 | 系数 | 证据（实测/估） |
|---|---|---|
| 策略 bash / 几何-分析真证 | **1.2–1.45×** | `general_482` HOL 639 → Lean **784**（1.23×，实测 `0a1ff76d`）；rrw HOL 614 → 878（1.43×）；deform_684 270 → 353（1.31×）；`deform_684` 族 |
| 解析/几何搬运（azim/dihV、ear 角） | **1.8–2.0×** | `SCS_4I2_STRAIGHT_p33` HOL 106 → Lean **210**（1.98×，实测） |
| 纯装配 / 定义级折叠（箭头记录、FZIOTEF、集合相等） | **0.4–0.9×** | `ARDBZYE_p33` HOL ~60 → Lean **24**（0.4×）；`SCS_4I1_ARROW_…` HOL ~40 → 27；`RRCWNSJ_p26` HOL 624 → Lean **378**（0.61×，实测） |
| VasTuaKit 型（已有逐字 kit） | 1.0× | 149 → 149 |

每条 EST 给区间，区间下沿取"装配档"、上沿取"bash/搬运档"，并注明选用理由。
**所有数字标 `EST`；静态无法判定的标 `UNRESOLVED`。**

### 0.4 并发约束（协调者补充）

侦察期间本机常驻 2 个真实 `lean` 进程（`la22emptykit-w1` 等），因此**全程未跑 `#print axioms`、
未跑单文件编译**。依赖关系全部由「HOL 证明体实引 + Lean NEEDS 注释 + Lean 正文 token」三路静态互证。
置信度按此下调一档：静态能证"引用存在"，不能证"Lean 侧类型能对上"。

---

## (A) 逐条表

> 列含义：`自身增量 EST` **不含任何 sorry 依赖**（a 依赖 b ⇒ a 不含 b 的成本）。
> `新拉入` 指当前不在 SORRIED、证明后会入锥的 sorry 件（逐条点名）。

### 1. `LocalAuto27.JCYFMRP_p27`

- **位置**：`lean/Kepler/Text/LocalAuto27.lean:495`（陈述 495–509，`:= by sorry` 510）
- **HOL 原件**：`reference/flyspeck/text_formalization/local/JCYFMRP.hl:256-618`（**362 行**证明体；concl 在 `:240`）
- **数学含义**：设 `s` 是 `k > 3` 的 SCS、`v` 是其 MMs 实现且 `scsGeneric`，所有对角边 `b > 4h0`
  且 `a ≤ cstab < dist`，且 `scs_M` 基数 ≤ 1、所有相邻边 `a = 2`。结论：**存在一条相邻边距离恰为 2**。
  它是"钉边存在性"引理：把 `scs_M`（被 `a,b` 夹住的边集）的基数约束翻译成一条真实的欧氏等式，
  供下游箭头（`4I1→4I2`、`5M2→5T1`）拿到 `MMs` 非空见证。
- **依赖（Text sorry 内）**：**无直接 sorry 依赖**。HOL 体首步 `MP_TAC CUXVZOZ`，而
  `CUXVZOZ_p21`（LA21:5273）**已真证**（`0a1ff76d` 后 token 扫描 0 个 Text sorry 引用）。
  其余 25 个引用（`SCS_M_LE_1_p27`、`CIZMRRH`、`CVLF_LF_F`、`BBS_IMP_CONVEX_LOCAL_FAN_p34`、
  `MMS_IMP_BBS_p28`、`JKQEWGV2_p23`、`SYNQIWN_p22`、`AURSIPD_p18`、`CHANGE_A/B_SCS_MOD_p28`…）全已真证。
  → **当前是"零 sorry 门"件**。
- **被依赖**：`JCYFMRP_V3_p29`（LA29:3601，**当前不在 SORRIED，证明后会入锥**）的 HOL 体
  `HIJQAHA.hl:3487-3515` 首步 `MP_TAC Jcyfmrp.JCYFMRP`；而 `JCYFMRP_V3_p29` 又被
  `SCS_4I1_IMP_SCS_4I2_p33`、`SCS_4I2_IMP_SCS_4T1_p33`、`SCS_5M2_IMP_SCS_5T1_p29` 三件共用。
  另有 `LocalConcl.JCYFMRP_discharged`（线的正常出口）。
- **自身增量 EST**：**300–430 行**。置信度 **中**。依据：362 HOL 行；25/26 引用已绿 ⇒ 主体是
  既有引理的装配 + `scs_M` 两分支；下沿取 `RRCWNSJ` 0.61× 的装配档、上沿取 1.2× bash 档。
- **外部阻塞**：无（`CUXVZOZ` 已闭后）。**这是当前 ROI 最高的一条。**

### 2. `LocalAuto23.LFLACKU_p23`

- **位置**：`LocalAuto23.lean:303`（陈述 303–304）
- **HOL 原件**：`local/JOTSWIX.hl:191-215`（**24 行**）
- **数学含义**：`scsArrowV39 {scs3I1} ∅` —— 三边系统 `3I1` 的 MMs 实现集为空。
  证明路线是 `MMsV39 scs3I1 = ∅` 归结为 `taustar < 0` 与 `TAUM_STD_POS`（`taum ≥ 0` 在箱上）的矛盾。
- **依赖（Text sorry 内）**：无 18 内依赖。新拉入：`TAUM_STD_POS_p23`（LA23:292，sorry，
  **当前不在 SORRIED、证明后入锥**）；后者又 `NEEDS TAUM_EXTREMAL_p23`（LA23:280，sorry，
  同样新入锥）+ 终端注册表项 `5541487347` / `OMKYNLT 3336871894`（hNL 终端银行，非 Text）。
  `taustar_taum_dfun`（LA38:1617）、`FUNLIST_EXPLICIT`（LA38:1677）、`pos_imp_scs_arrow_empty_p22`
  （LA22:3834）均已真证。
- **被依赖**：`LocalAuto16.JEJTVGB_case_breakdown_p16`（LA16:394，已证，体内 `exact … LFLACKU_p23 h`）。
- **自身增量 EST**：**25–45 行**。置信度 **高**（24 HOL 行，单箭头 + 一次 `pos_imp` 应用）。
- **外部阻塞**：**hNL 终端注册表（用户保留区）**。`TAUM_EXTREMAL_p23`/`TAUM_STD_POS_p23`
  的根在 `main_nonlinear_terminal_v11` 的 109 项注册表，属 hNL，不是 Text 能单方面清的。
  → 判 **BLOCKED（外部）**，本体再便宜也无意义。

### 3. `LocalAuto32.MIQMCSN_p32`

- **位置**：`LocalAuto32.lean:1576`
- **HOL 原件**：`local/MIQMCSN.hl:3436-3470`（**34 行**）
- **数学含义**：`scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4}` —— 4M8（4 边、8 个 M 型约束）
  系统沿"先塌到 4M6′/4M8_02/4M8_13，再落到 3T7"的箭头链，最终覆盖三个目标系统。
  本质是 `FZIOTEF_TRANS` 把 4 条子箭头串起来 + 每个目标的 `isScs` 半边。
- **依赖（Text sorry 内）**：无 18 内依赖。新拉入（全部**当前不在 SORRIED、证明后入锥**）：
  `SCS_4M8_ARROW_STEP_ONE_p32`(LA32:1419)、`SET_STAB_4M8_ARROW_3T4_p32`(LA32:896)、
  `SCS_4M8_02_ARROW_3T7_p32`(LA32:1569)→`SCS_4M8_02_ARROW_4M8_13_p32`(LA32:1562)、
  `SCS_4M8_13_ARROW_3T7_p32`(LA32:1494)、以及二阶层 `STAB_4M8_02_SCS_p32`/`STAB_4M8_13_SCS_p32`
  (LA32:1443/1451) 与 `MIN_NOT_STAND_4M8_p32`(LA32:1366)。
- **被依赖**：`LocalConcl.MIQMCSN_discharged`（线出口）。
- **自身增量 EST**：**45–80 行**。置信度 **中**（34 HOL 行 × 装配档 0.6–1.5×；集合并/成员逐槽是
  Lean 侧 verbose 点）。
- **外部阻塞**：无。**但注意"装债陷阱"**：只填本体 → 锥内 SORRIED **+5 左右**；
  `SCS_OPP_REFL_p13`/`YXIONXL2_p13` 一类旧注记已可被 **已真证** 的 `YXIONXL2_p33`
  （LA33:495，`ScsV39` 版，标准三）替代（LA33 不在 LA32 的 import 闭包里，但 LA33 也不 import
  LA32，加 import 无环——已核 import 表）。

### 4. `LocalAuto33.MM_4I2_IMP_4T2_4T1_p33`

- **位置**：`LocalAuto33.lean:2450`
- **HOL 原件**：`local/ARDBZYE.hl:2339-2513`（**174 行**）
- **数学含义**：4I2 的 MMs 实现若在一条对角边上 `dist ≤ cstab`（"对角闭合"分支），则
  **4T1 或 4T2 的 MMs 非空**。证明分两路：对角边恰为 3 时走 `XWNHLMD_MM` 得 4T2；
  对角边 > 3 时用 `EDGE_EQ_2_4I2_ALL`（所有边 = 2）再走 `XWNHLMD_MM` 得 4T1。
  它是 `ARDBZYE_p33`（已证）的 diag-closed 叶。
- **依赖（Text sorry 内）**：无 18 内直接依赖。新拉入：`EDGE_EQ_2_4I2_ALL_p33`（LA33:2442，sorry，
  **当前不在 SORRIED、会入锥**），它再拉 `EDGE_EQ_2_4I2_p33`(2396)、`EXPAND_DIAG_4_DIST_p33`(2403)、
  `EDGE_EQ_2_4I2_1/2/3_p33`(2421/2428/2435) —— **簇共 6 件**（HOL 体 118+22+116+20+25+56 = **357 行**）。
  `EDGE_EQ_2_4I2` 体首步 `MP_TAC CUXVZOZ`；`CUXVZOZ_p21` 已真证 ⇒ 簇内**无 18 内 sorry**。
  `ASSUME_MIN_DIAG_p33`、`SCS_4I2_STRAIGHT_ALL_p33`(2161/2372 均真)、`XWNHLMD_MM` 已绿。
- **被依赖**：`ARDBZYE_p33`（LA33:2462，已证，体内 `rcases MM_4I2_IMP_4T2_4T1_p33 …`）。
- **自身增量 EST**：**180–260 行**。置信度 **中**（174 HOL × 1.0–1.5×；两分支 + 4 个 residue 槽）。
- **外部阻塞**：无。杠杆：EDGE 簇 360–520 行是 MM 的**唯一**门。

### 5. `LocalAuto32.NWDGKXH_p32`

- **位置**：`LocalAuto32.lean:1030`
- **HOL 原件**：`local/MIQMCSN.hl:2110-2129`（**19 行**）
- **数学含义**：`scsArrowV39 {scs4M6'} {scs4T3, scs4T5}` —— 4M6′ 沿"4T3 + stab-diag 族"再并到 4T5。
  纯 `FZIOTEF_TRANS` 装配：`SCS_4M6_ARROW_SCS_4T3_STAB_4M6` + hexagons 的 stab→{4T3,4T5} 箭头。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`（LA32:1020，sorry）
  → `EXTREMAL_SCS_4M6_p32`(993，sorry) → `BB_4M6_IMP_scs_4T3_p32`(1003，sorry)、
  `MM_4M6_IMP_MM_4T3_p32`(1012，sorry)；另有 `SCS_4T3_IS_SCS_p32`(247，sorry，22 合取展开)。
  `SCS_4M6_STAND_OR_PRO_p32`(960)、`VASYYAU_p25`(LA25:2543)、`SET_STAB_4M6_ARROW_4T5_p33`(LA33:4622) 已证。
- **被依赖**：`LocalConcl.NWDGKXH_discharged`。
- **自身增量 EST**：**25–45 行**。置信度 **中**（19 HOL；但集合并逐槽 + `∪` 的成员证在 Lean 侧偏贵）。
- **外部阻塞**：无。**杠杆件**：自身 25–45，但需要 ~425–610 行的 4M6 梯子（见 §B-K6）。

### 6. `LocalAuto22.OCBICBY_p22`

- **位置**：`LocalAuto22.lean:3856`
- **HOL 原件**：`local/OCBICBY.hl:4755-4789`（**34 行**）；本体是 `pos_imp_scs_arrow_empty` 的
  14 次 `GMATCH_SIMP_TAC` + `arrow_rewrite_list`
- **数学含义**：14 个 T-系统（6T1, 5T1, 4T1–4T5, 3T1–3T7）到空集的箭头**合取**。
  每支的内容是：该系统上 `taustar ≥ 0`（空性），于是 `scsArrowV39 {s} ∅`。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`empty_6T1_p22`(LA22:2319，sorry)、
  `empty_5T1_p22`(LA22:2324，sorry)、`empty_3T2`(LA38:3121，sorry) —— 共 3 条已存在 sorry；
  **另 11 条 `empty_*`（3T3–3T7、4T1–4T5）在 Lean 全树无陈述**（HOL 在 `terminal.hl:2575-4134`，
  合计 **1,381 行**证明体：3T3 22/3T3′ 19/3T4 25/3T5 23/3T6 27/3T7 24/4T1 44/4T2 180/4T3 191/4T4 106/4T5 104；
  另 empty_6T1 275 + empty_5T1 344 在 `OCBICBY.hl`）。
- **被依赖**：`LocalAuto16.JEJTVGB_case_breakdown_p16`（LA16:425，已证，体内 `OCBICBY_p22 h`）。
- **自身增量 EST**：**70–110 行**。置信度 **中**（14 个合取 × 5–8 行）。
- **外部阻塞**：**11 条 empty_* 无陈述**（语句级缺口，不是"没证"）+ `terminal_hex_taum` 类无陈述件
  （`docs/priority-queue.md` 2026-11-12 的 `empty-la22 BLOCKED` 判词同向）。→ 判 **BLOCKED（外部）**。

### 7. `LocalAuto33.SCS_4I1_IMP_SCS_4I2_p33`

- **位置**：`LocalAuto33.lean:2487`
- **HOL 原件**：`local/ARDBZYE.hl:2575-2641`（**66 行**）
- **数学含义**：4I1 的 MMs 实现若所有对角 `> cstab`，则 4I2 的 MMs 非空。
  证明是 `RRCWNSJ`（generic）+ `JCYFMRP_V3`（钉边）+ `JLXFDMJ`（把钉边扩散到所有非 `scs_M` 边）
  三件串联，最后逐 BB 表项对 4I2 的 21 合取。
- **依赖（Text sorry 内）**：无 18 内直接依赖。新拉入：`JCYFMRP_V3_p29`（LA29:3601，sorry）
  → `JCYFMRP_p27`（**在 18 内**）；`JLXFDMJ_p27`（LA27:559，sorry，**会入锥**）。
  `RRCWNSJ_p26`（LA26:1343）**已真证**（旧 triage 的"锥内 S"已过期）。
- **被依赖**：`SCS_4I1_ARROW_SCS_4I2_STAB_4I1_p33`（LA33:2519，已证，all-diags-open 分支）。
- **自身增量 EST**：**75–110 行**。置信度 **中**（66 HOL × 1.1–1.7×；最后一段 21 合取表展开贵）。
- **外部阻塞**：无。

### 8. `LocalAuto33.SCS_4I2_IMP_SCS_4T1_p33`

- **位置**：`LocalAuto33.lean:1817`
- **HOL 原件**：`local/ARDBZYE.hl:1357-1438`（**81 行**）
- **数学含义**：4I2 的 MMs 实现（所有对角 `> cstab`）⇒ 4T1 的 MMs 非空。
  **与第 7 条同一前置三元组**（`RRCWNSJ` + `JCYFMRP_V3` + `JLXFDMJ`），只是目标表换成 4T1。
- **依赖（Text sorry 内）**：同第 7 条：`JCYFMRP_V3_p29` → `JCYFMRP_p27`（18 内）；
  `JLXFDMJ_p27`（新入锥）。`RRCWNSJ_p26` 已真证。
- **被依赖**：`ARDBZYE_p33`（已证，all-diags-open 分支）。
- **自身增量 EST**：**90–130 行**。置信度 **中**（81 HOL × 1.1–1.6×）。
- **外部阻塞**：无。**与第 7 条同车道一次交两笔**，前置（V3+JLXFDMJ）一次摊薄。

### 9. `LocalAuto29.SCS_5M2_IMP_SCS_5T1_p29`

- **位置**：`LocalAuto29.lean:3651`
- **HOL 原件**：`local/HIJQAHA.hl:3579-3948`（**369 行**）
- **数学含义**：5M2 的 MMs 实现若所有对角 `> cstab`，则 5T1 的 MMs 非空 —— 即
  "5M2 实现可重排成 5T1（负 taustar）"的终端非线性不等式机制。这是本章最重的本体。
- **依赖（Text sorry 内）**：无 18 内直接依赖。新拉入 5 件（全部**会入锥**）：
  `IUNBUIG_p18`(LA18:1483)、`JCYFMRP_V3_p29`(LA29:3601)→`JCYFMRP_p27`（18 内）、
  `JLXFDMJ_p27`(LA27:559)、`xrr_le_1553_BB_p29`(LA29:3636)、`EGHNAVX_COLL_SCS_p18`(LA18:534)。
  `RRCWNSJ_p26` 已真证；`B_LE_CSTAB_5M2_A_LT_B_p29` 等 35 件已绿。
- **被依赖**：`HIJ_STEP_1_p29`（LA29:3816，已证，体内 `SCS_5M2_IMP_SCS_5T1_p29 hmnt …`）。
- **自身增量 EST**：**330–480 行**。置信度 **低**（369 HOL 行；HOL 是 `MRESA_TAC`/`REAL_ARITH` 密集
  的终端不等式 bash，1.2× 即 443，上沿 1.3× = 480，逼近 AGENTS §7 的 ~450 行止损线；
  可能需拆 2 个子件）。
- **外部阻塞**：无（但 `IUNBUIG_p18`/`EGHNAVX_COLL_SCS_p18` 是 LA18 的两条深件，见 §B-K4b）。

### 10. `LocalAuto20.SCS_6I1_BERAK_BY_CSTAB`

- **位置**：`LocalAuto20.lean:1647`
- **HOL 原件**：`local/hexagons.hl:1831-1890`（**59 行**）
- **数学含义**：`scsArrowV39 {scs6I1} ({scs6T1} ∪ {stab-diag of 6I1})` —— 6I1 去掉对角稳定化
  后落到 6T1。箭头 = `SCS_6I1_IMP_SCS_6T1`（MMs 包含）+ 每个对角稳定系统的 `isScs`。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`SCS_6I1_IMP_SCS_6T1`(LA20:1638，sorry)
  → `SCS_6M1_IMP_SCS_6T1`(LA20:1627，sorry)；后者 `NEEDS` **LocalAuto1 的 3 个注册表孪生**
  `RRCWNSJ_concl`(LA1:3652)、`JCYFMRP_concl`(LA1:3660)、`JLXFDMJ_concl`(LA1:3699) —— 三条全 sorry
  且**当前不在 SORRIED、证明后会入锥**（`MXQTIED_concl` 已证；`PEDSLGV2` 已证）。
- **被依赖**：`OEHDBEN_PRIME`（LA20:1910，已证，体内 `FZIOTEF_TRANS … (SCS_6I1_BERAK_BY_CSTAB hmn)`）。
- **自身增量 EST**：**65–95 行**。置信度 **中**（59 HOL；箭头记录 + stab 分支的 `isScs` 半）。
- **外部阻塞**：**无硬外部**，但债面前移到 LA1 注册表孪生（3 条 wire，各 ~15–30 行，可由已证的
  `RRCWNSJ_p26` / `JCYFMRP_p27` / `JLXFDMJ_p27` 直接转接）。整链成本见 §B-K11。

### 11. `LocalAuto27.TFITSKC_p27`

- **位置**：`LocalAuto27.lean:331`
- **HOL 原件**：`local/TFITSKC.hl:649-666`（**17 行**；concl 在 `:636`）
- **数学含义**：已知边 `i→i+1` 距离 = 2、边 `i+1→i+2` 被钉（`a=2, b≤2h0`）、且
  `b(i,i+1) > 2`、`a(i+2,i+3) < b(i+2,i+3)`，则 `dist(v(i+1),v(i+2)) = 2`。
  即"钉边沿链传递"—— 用 `TFITSKCv1` 的 mod-diag 坍缩把 `2 < b` 变成相邻等式。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`TFITSKCv1_p27`(LA27:311，sorry，
  **会入锥**)，其 HOL 体 `TFITSKC.hl:144-635` = **491 行**，实引 `CUXVZOZ`/`CJBDXXN`（均**已真证**）、
  `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE`(LA7:1174，**已真证**)、`NUXCOEA`/`ODXLSTC`（已证）。
- **被依赖**：`LocalConcl.TFITSKC_discharged`。
- **自身增量 EST**：**20–35 行**。置信度 **高**（17 HOL；历史上 13 行草稿被拒仅因装债）。
- **外部阻塞**：无。**杠杆件**：自身 20–35，但门是 `TFITSKCv1_p27`（EST **500–650**，置信 中；
  其注释提到的 "a,b near-diagonal linear program missing from the module's port" 是否真缺
  **UNRESOLVED**——HOL 体未直接引用该 LP，疑为 `mnт11` 注册表内的成分）。

### 12. `TameLp.fully_surrounded_perimeter_bound`

- **位置**：`lean/Kepler/Text/TameLp.lean:925`
- **HOL 原件**：`formal_lp/hypermap/ineqs/lp_main_estimate-compiled.hl:1530-1540`（**10 行**；
  §PerimeterBound 段 `:1473-1543`）
- **数学含义**：全被包围的平面扇（`FAN 0 V E` + `FullySurrounded V E`）的**周长 ≤ 2π**。
  Lean 陈述是通用 `E`；它被 `MQMSMAB`（TameLp:10895）以 `E := ESTD V` 消费。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`WSEWPCH`（LA7:7676，sorry，
  **会入锥**）= 极扇章核心，HOL `polar_fan.hl:2213-3363` = **1,150 行**。
  树内已有 **`yk11_perimeterBound_of_core`**（TameLp:10961，已证，标准三）把 `PerimeterBound`
  收敛成单锚 `hcore`（face-和 ≤ 2π，`ConvexLocalFan`），且 `yk10_convexLocalFan` 已覆盖
  `f_surr_localization_convex_local`；三分支中 circular/lunar 已收口
  （`FAN_PERIMETER_LE_2PI_OF_CIRCULAR`/`_LUNAR`），generic 分支 `BGMIFTE` 已真证。
  **残余 = WSEWPCH 核**（HOL 1150 行 → EST 1,000–1,500）。
- **被依赖**：`MQMSMAB`（TameLp:10895，已证，体内 `fully_surrounded_perimeter_bound V (ESTD V) …`）。
- **自身增量 EST**：**10–20 行**（`yk11_perimeterBound_of_core` 的单行装配）。
  置信度 **高**（对装配本身）/ **UNRESOLVED**（对通用 `E` 陈述：yk11 桥只给 `ESTD`；
  要闭**原陈述**必须真证 WSEWPCH 本身，或走 SF 通道把消费方改吃 ESTD 版）。
- **外部阻塞**：**WSEWPCH 极扇/局部扇深章**（LocalAuto7 章级，AGENTS §7 单件上限；非 LP 证书，
  但属"整章"量级）。→ 判 **冻结（章级）**。

### 13. `LocalAuto30.UAGHHBM_p30`

- **位置**：`LocalAuto30.lean:1204`
- **HOL 原件**：`local/UAGHHBM.hl:2501-4099`（**1,598 行**）
- **数学含义**：给定 SCS `s` 和边 `(i,j)` 上的常数 `c ∈ [a,b]`，若 `c ≠ am` 且边非 J、
  做一次 `subdivV39 s i j c`（在 `(i,j)` 上插入子分点），则从 `{s}` 到
  `{t | t ∈ subdivV39 s i j c}` 有 SCS 箭头 —— 即**子分保持 SCS 结构**。
- **依赖（Text sorry 内）**：无 18 内。新拉入：**2 条 Lean 全树无陈述的 `isScs` 件**
  `isScsV39 (restrictionCs1V39 s i j c)` / `isScsV39 (restrictionCs2V39 s i j c)`
  （定义在 LA1:915/921 已有，**证明不存在**，各需 ~100–200 行 psort/override 重写）；
  16 个 HOL 引用已证（`PERIODIC_PROPERTY`、`CASE_PSORT`、`C_EQ_AM`、`C_LE_2_IS_SCS`…）。
- **被依赖**：`LocalConcl.UAGHHBM_discharged`。
- **自身增量 EST**：**800–1,300 行**（1,598 HOL × 0.5–0.8×：HOL 是单个 `RESA_TAC` bash，
  Lean 侧必须拆成具名子件，故低于 1:1；但仍远超 §7 止损）。置信度 **高**（"XL"这一档很确定）。
- **外部阻塞**：**2 条缺失的 isScs 限制件（语句级缺口）**，无任何可导入 lane。→ 判 **BLOCKED（外部）**。

### 14. `PackingAuto13.URRPHBZ2`

- **位置**：`PackingAuto13.lean:361`
- **HOL 原件**：`packing/URRPHBZ2.hl:215-973`（**758 行**）
- **数学含义**：3 维 Marchal cell 的**最终径向性**：对饱和、`Packing`、`barV 3 ul` 的 `V`，
  任意 `v ∈ V`，`EventuallyRadial v (mcell k V ul)`（沿任意小扰动保持径向）。
  按 `k = 0,1,2,3,≥4` 分五支：`k=0` 走 Rogers 交集；`k=1` 是三交集（rogers/cball/rcone）；
  `k=2` 走两个 `rcone_ge` + `aff_ge` 楔；`k≥3` 走 Voronoi-list + 单纯形最远点。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`CLOSED_MCELL`（PA12:797，sorry —— **只差 k=2 的
  `IsClosed (affGe …)`**，上游 `Geom/Aff` 缺件，见 PA12:852 `NEEDS`）、
  `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS`（PA12:1060，sorry，几何 giant）。
  其余 `EVENTUALLY_RADIAL_*` 6 件、`LEPJBDJ`(PA11:858)、`SIMPLEX_FURTHEST_LT_2`、`MXI_EXPLICIT`、
  `MHFTTZN1`、`OMEGA_LIST_IN_VORONOI_LIST` **均已真证**（旧 TAINTED 名单全部过期；
  `LEPJBDJ` 第一版扫描误报，剥注释后确认无 sorry）。
- **被依赖**：`QZYZMJC`（PackingAuto16:625，已证）。
- **自身增量 EST**：**650–950 行**。置信度 **中**（758 HOL × 0.9–1.25×；五分支结构清晰但每支多子引理）。
- **外部阻塞**：`CLOSED_MCELL` k=2 的 `IsClosed affGe`（**上游 Geom 缺口**，需先补 Geom/Aff 的
  闭性引理 ~30–60 行）+ `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS`（Rogers 几何 giant，EST 150–250）。

### 15. `LocalAuto15.VPWSHTO_p15`

- **位置**：`LocalAuto15.lean:398`
- **HOL 原件**：`local/VPWSHTO.hl:1978-2113`（**135 行**）
- **数学含义**：单位五边形（5 条边 = 2）且任意三点不共线 ⇒ **存在一个顶点**，
  它到两个"隔一个"顶点的两条五边形对角线都 ≤ `1 + √5`。
  证明用 `MAX_COPLANAR_4POINT`/`SUM_4ANGLE_4POINT_EQ_2PI` 等把最大对角线放到共面四点，
  再用 `EQ_DIAGONAL_MIN`/`TWO_DIAGONAL_AT_MOST` 的极值论证。
- **依赖（Text sorry 内）**：无 18 内。新拉入：**LA15 章内 10 条**（全部**会入锥**）：
  `MAX_COPLANAR_4POINT_p15`(222)、`SUM_4ANGLE_4POINT_EQ_2PI_p15`(233)、`EQ_DIAGONAL_MIN_p15`(242)、
  `TWO_DIAGONAL_AT_MOST_p15`(256)、`MAX_IF_COPLANAR_p15`(267)、`MAX_IF_COPLANAR1_p15`(280)、
  `TWO_DIAGONAL_AT_MOST1_p15`(293)、`VPWSHTO1_p15`(303)、`VPWSHTO200_p15`(315)、`VPWSHTO2_p15`(334)。
  `VPWSHTO_PRIME_p15`(591) 已证；12 条 `MOD_ADD_*` 已证。
- **被依赖**：`LocalAuto15` 内的某个下游出口（LA15:604 `refine VPWSHTO_p15 …`）。
- **自身增量 EST**：**150–230 行**。置信度 **中**（135 HOL × 1.1–1.7×；实分析/角度界，Lean 侧
  `norm`/`sqrt` 计算偏贵）。
- **外部阻塞**：无外部缺口，但**整章 11 件自成闭环**，净收益仅 −1，代价 11 件。→ 判 **冻结（低 ROI）**。

### 16. `LocalAuto32.YOBIMPP_p32`

- **位置**：`LocalAuto32.lean:1241`
- **HOL 原件**：`local/MIQMCSN.hl:2453-2490`（**37 行**）
- **数学含义**：`scsArrowV39 {scs4M7} {scs4M6', scs3T3, scs3M1, scs3T4}` —— 4M7 经
  "4M6′ / 3T3,3M1,3T4" 两条子箭头的 `FZIOTEF_TRANS` 合并。是 4M7 dichotomy 的出口。
- **依赖（Text sorry 内）**：无 18 内。新拉入：`SCS_4M7_ARROW_STAB_4M7_4M6_p32`（LA32:1162，sorry，
  HOL 81 行）、`STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32`（LA32:680，sorry，HOL 12 行）；
  以及 `BB_4M7_IMP_4M6_01_p32`(1162 区) 等 4M7 子件。`SCS_OPP_REFL`/`YXIONXL2` 可由
  **已真证** 的 `YXIONXL2_p33`(LA33:495) 替代（`ScsV39` 版；LA33 不 import LA32，加 import 无环）。
- **被依赖**：`LocalConcl.YOBIMPP_discharged`。
- **自身增量 EST**：**45–80 行**。置信度 **中**（37 HOL × 1.2–2.0×；4 个目标的集合并逐槽）。
- **外部阻塞**：无。

### 17. `LocalAuto21.general_482_deformation_p21` —— **已在侦察期间真证闭掉**

- **位置**：`LocalAuto21.lean:4489`（`0a1ff76d` 后；`CUXVZOZ_p21` 移到 5273，`CJBDXXN_p21` 5297）
- **HOL 原件**：`local/CUXVZOZ.hl:3649-4288`（**639 行**）
- **数学含义**：482-cell 形变主定理 —— SCS 实现 `v` 在一条对角线上距离 ≥ 3、内角 < π 的
  前提下，沿 `p0,p1,p2` 三元组做 482 形变，把 `dist(v p1, v(p1+1)) = 2` 逼出来。
  它是 `CUXVZOZ`/`CJBDXXN`（check-completeness）的引擎，也是 `JCYFMRP`、`TFITSKCv1`、
  `EDGE_EQ_2_4I2`、`JCYFMRP_V3` 的总闸。
- **依赖（Text sorry 内）**：无。`0a1ff76d` 后 token 扫描：体内 **0 个 sorried Text 引用**。
- **被依赖**：`CUXVZOZ_p21`(已证)、`CJBDXXN_p21`(已证) → 再向上 `JCYFMRP_p27`(18 内)、
  `TFITSKCv1_p27`、`EDGE_EQ_2_4I2_p33`、`JCYFMRP_V3_p29`。
- **自身增量 EST**：**已兑现 784 行**（HOL 639 → Lean 784 = **1.23×**）。
  事前 EST 800–1,000 略偏高；校准意义：本域"策略 bash"系数取 **1.2–1.3×** 是稳的。
- **外部阻塞**：无（已闭）。

### 18. `PackingAuto25.real_model_ox3q1h_merge`

- **位置**：`PackingAuto25.lean:10378`
- **HOL 原件**：`packing/OXLZLEZ3.hl:6099-6241`（**142 行**）
- **数学含义**：`0 ≤ ∑_{i<n} gg_mcell V f u0 u1 i` 的**认证 4 季界**：在
  `ox3q1hP25` 作为**假设参数**（`hox`）、`Packing`/`saturated`/`HasSizeP25`/`periodic`/
  `leaf_rank` 等前件下，28 行大合取（4 个季度各 4 条 `cc_4` + 距离界）成立时，
  mcell 的 `gg` 和取非负。
- **依赖（Text sorry 内）**：无。16 个引用全已证（`real_model_sum_azim`(PA25:9811)、
  `GG_MCELL_QUARTER`、`GG_MCELL_BETA`、`MCELL4_DOMAIN`、`c_4_azim_mcell_dih_y`、
  `LEAF_RANK_PERIODIC`、`periodic_sum`、`s_leaf`/`gg_mcell`/`azim_mcell`/`leaf_rank` 的 def、
  `pack_nonlinear_non_ox3q1h`）。`hox : ox3q1hP25` 是**假设参数，不要求证**。
- **被依赖**：`pkrmQuarter`（PA25:15936，已证，体内 `refine real_model_ox3q1h_merge …`）。
- **自身增量 EST**：**170–240 行**。置信度 **中-高**（142 HOL × 1.2–1.7×；大合取逐项 but
  每项都是已证叶的直接应用）。
- **外部阻塞**：无。**全清单最干净的"可立即闭"件**（零 sorry 前置、零证书、零 hNL）。

---

## (B) 共享 kit 单列（一次性成本，不重复计入各条）

> `受益条目` 指该 kit 闭掉后能直接解锁的 18 内条目数。

| # | kit | 一次性 EST | 置信度 | 受益条目 | 说明 |
|---|---|---|---|---|---|
| K1 | `INTERIOR_ANGLE1_AZIM_p22`（LA22:1635，HOL OCBICBY.hl:2369-2413 = 44 行） | 60–120 | 中 | 0（g482 新证已不引用它；仅当某下游显式要用时才需） | 仍 sorry；**不在锥**，是"可选拉入" |
| K2 | `TFITSKCv1_p27`（LA27:311；HOL 491 行） | 500–650 | 中 | 1（TFITSKC_p27） | `CUXVZOZ`/`CJBDXXN` 已证，理论门已开；残留疑点见 (A)11 `UNRESOLVED` |
| K3 | `EDGE_EQ_2_4I2` 簇 6 件（LA33:2396/2403/2421/2428/2435/2442；HOL 357 行） | 360–520 | 中 | 1（MM_4I2） | 6 件互相引用；`_2`/`_3` 是短 `prove`（20/25 行），可先闭 |
| K4a | `JCYFMRP_V3_p29`（LA29:3601；HOL 25 行） | 30–50 | 高 | 3（SCS_4I1/4I2/5M2） | 体是 `MP_TAC JCYFMRP` + `JCYFMRP_V2`，**依赖 (A)1** |
| K4b | `JLXFDMJ_p27`（LA27:559；HOL JLXFDMJ.hl:227-818 = 591 行） | 600–800 | 中-低 | 3（同上） | 只差 `j % k ∉ scsM` 的 mod 转移；`SCS_M_EQ_1_p27`(537)、`CHANGE_A/B_SCS_MOD_p28` 已证 ⇒ **无 sorry 门** |
| K4c | `IUNBUIG_p18`(LA18:1483) + `EGHNAVX_COLL_SCS_p18`(LA18:534) + `xrr_le_1553_BB_p29`(LA29:3636) | 300–500（未逐件细估） | 低 | 1（SCS_5M2） | LA18 两条深件；`xrr_le_1553_BB` 是 15.53 的 annulus 应用 |
| K5 | `SCS_OPP_REFL`（`ScsV39` 版） | 0–30 | 中 | 0 | **已发现可绕过**：`YXIONXL2_p33`(LA33:495) 已真证且是 `ScsV39` 版；LA32→LA33 加 import 无环（已核 import 表）。旧 triage 的 "LA13 共享件" 前提作废 |
| K6 | LA32 4M6 梯子：`SCS_4T3_IS_SCS_p32`(247, HOL 106) + `EXTREMAL_SCS_4M6_p32`(993, HOL 136) + `BB_4M6_IMP_scs_4T3_p32`(1003, ~39) + `MM_4M6_IMP_MM_4T3_p32`(1012, ~17) + `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`(1020, HOL 61) | 400–565 | 中 | 1（NWDGKXH） | 全部无 sorry 门（`SCS_4M6_STAND_OR_PRO`/`VASYYAU_p25` 已证）；`SCS_4T3_IS_SCS` 是 22 合取展开，最贵 |
| K7 | LA32 4M7 梯子：`SCS_4M7_ARROW_STAB_4M7_4M6_p32`(1162, HOL 81) + `STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32`(680, HOL 12) | 110–165 | 中 | 1（YOBIMPP） | 4M7 的 BB/MM 子件已证或短 |
| K8 | LA32 4M8 梯子：`SCS_4M8_ARROW_STEP_ONE_p32`(1419, HOL 141) + `SET_STAB_4M8_ARROW_3T4_p32`(896, HOL 12) + `SCS_4M8_02_ARROW_4M8_13_p32`(1562, HOL 17) + `SCS_4M8_02_ARROW_3T7_p32`(1569, HOL 7) + `SCS_4M8_13_ARROW_3T7_p32`(1494, HOL 9) + `STAB_4M8_02/13_SCS_p32`(1443/1451) + `MIN_NOT_STAND_4M8_p32`(1366) | 235–360（**下沿**） | 低 | 1（MIQMCSN） | **UNRESOLVED**：`SCS_4M8_ARROW_STEP_ONE` 自己还会拉 `BB/MM_4M8_IMP_*` 子件，未逐件展开；真实簇可能 400–600 |
| K9 | `TAUM_STD_POS_p23`(292, HOL 82) + `TAUM_EXTREMAL_p23`(280, HOL 59) | 160–240 | 中 | 1（LFLACKU） | 根在 hNL 注册表（`5541487347`/`OMKYNLT`）→ **外部阻塞**，估了也不能单干 |
| K10 | 13 条 `empty_*`：现有 3（`empty_6T1` 275 / `empty_5T1` 344 / `empty_3T2` 16）+ **11 条无陈述**（3T3 22/3T3′ 19/3T4 25/3T5 23/3T6 27/3T7 24/4T1 44/4T2 180/4T3 191/4T4 106/4T5 104） | 1,400–1,900 + 11 条语句定义 | 中 | 1（OCBICBY） | 语句级缺口是硬阻塞；HOL 合计 1,381 行证明体 |
| K11 | SCS_6I1 链：`SCS_6M1_IMP_SCS_6T1`(1627) + `SCS_6I1_IMP_SCS_6T1`(1638) + 3 条 LA1 wire（`RRCWNSJ_concl`/`JCYFMRP_concl`/`JLXFDMJ_concl`） | 200–320 | 中 | 1（SCS_6I1_BERAK） | 3 条 wire 各 15–30 行，分别由 `RRCWNSJ_p26`(已证)/`JCYFMRP_p27`/`JLXFDMJ_p27` 转接 |
| K12 | WSEWPCH（LA7:7676；HOL polar_fan.hl:2213-3363 = 1,150 行） | 1,000–1,500 | 低-中 | 1（TameLp） | yk11 已把装配免掉；残余就是这一个核；circular/lunar 分支已收口，generic 分支需 `p12a/p12b` 续波 |
| K13 | `CLOSED_MCELL` k=2 的 `IsClosed affGe`（上游 Geom 缺件）+ `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS`(PA12:1060) | 180–310 | 中 | 1（URRPHBZ2） | 前者是 Geom/Aff 的闭性引理（30–60），后者是 Rogers giant（150–250） |
| K14 | `isScsV39 (restrictionCs1V39 …)` / `isScsV39 (restrictionCs2V39 …)`（**无陈述**） | 120–250 | 中 | 1（UAGHHBM） | 定义已有（LA1:915/921），证明需 21 合取 × psort/override 重写 |

**关键判断**：真正"可立即开工且门全绿"的 kit 只有 **K3、K4a、K6、K7、K11（部分）**；
K9/K10/K12/K13/K14 都有语句级或章级外部阻塞。

---

## (C) 总账

### C.1 自身增量求和（naive sum）

| 集合 | 下沿 | 上沿 |
|---|---|---|
| 17 条（不含已闭的 `general_482`） | **3,050** | **4,640** |
| `general_482`（已兑现，参考） | 784（实测） | 784（实测） |
| **18 条合计（含 g482 实测）** | **3,834** | **5,424** |

### C.2 按 DAG 去重后的总成本

去重 = 18 条自身 + 共享 kit + 新拉入的 sorry 件成本（不含已闭的 g482，不含 K1 可选项）：

| 桶 | 下沿 | 上沿 |
|---|---|---|
| 17 条自身 | 3,050 | 4,640 |
| K2 TFITSKCv1 | 500 | 650 |
| K3 EDGE 簇 | 360 | 520 |
| K4a JCYFMRP_V3 | 30 | 50 |
| K4b JLXFDMJ_p27 | 600 | 800 |
| K4c LA18/LA29 三件 | 300 | 500 |
| K5 opp（可绕过） | 0 | 30 |
| K6 4M6 梯子 | 400 | 565 |
| K7 4M7 梯子 | 110 | 165 |
| K8 4M8 梯子（下沿，未完全展开） | 235 | 360 |
| K9 TAUM（外部阻塞） | 160 | 240 |
| K10 empty_*（外部阻塞） | 1,400 | 1,900 |
| K11 SCS_6I1 链 | 200 | 320 |
| K12 WSEWPCH（章级） | 1,000 | 1,500 |
| K13 URRPHBZ2 门 | 180 | 310 |
| K14 UAGHHBM 限制件 | 120 | 250 |
| **去重总计** | **≈ 8,545** | **≈ 12,800** |
| 加 g482 实测 784 | **≈ 9,330** | **≈ 13,580** |

**去重前后差**：naive 3,050–4,640 → 去重 8,545–12,800。**差 ≈ +5,500 至 +8,200 行**，
即"自身增量"只占真实总成本 **~30–36%**；**~2/3 的成本在共享 kit 和装债**。
这与历史教训一致（MIQMCSN 本体 45–80，但簇 400–600；TFITSKC 本体 20–35，但门 500–650）。

### C.3 杠杆件（自身小 / 解锁多）

| 排名 | 件 | 自身 EST | 直接解锁 | 杠杆说明 |
|---|---|---|---|---|
| 1 | `JCYFMRP_p27` | 300–430 | 1 直接 + 3 经 `JCYFMRP_V3`（SCS_4I1/4I2/5M2） | **g482 已闭 ⇒ 它是当前唯一"门全绿且解锁 4 条"的件** |
| 2 | `general_482_deformation_p21` | 784（已兑现） | 6（JCYFMRP/TFITSKC/MM/SCS_4I1/4I2/5M2） | 总闸，已开 |
| 3 | `JLXFDMJ_p27` | 600–800 | 3（SCS_4I1/4I2/5M2） | 自身无 sorry 门，但体量大；与 K4a 同一车道 |
| 4 | `SCS_4T3_IS_SCS_p32` | 110–170 | 1（NWDGKXH）+ 4M6 梯子 | 22 合取展开，是 4M6 簇的地基 |
| 5 | `EDGE_EQ_2_4I2_ALL` 簇 | 360–520 | 1（MM） | 簇内 `_2`/`_3` 极短，可先闭 |
| 6 | `real_model_ox3q1h_merge` | 170–240 | 1，**零前置** | 不是杠杆，但是**最快的真还债**（−1 立即） |

### C.4 建议施工顺序（3 车道）

> 前提：**g482 已闭**（`0a1ff76d`）。以下按"门全绿优先 + 杠杆前置优先 + 外部阻塞后置"。

**Wave 0（立即发车，3 车道并行）**

- **车道 A（快赢 + 杠杆）**：`real_model_ox3q1h_merge`（170–240）→ 交一笔 −1；
  随后 `JCYFMRP_p27`（300–430）→ 交一笔 −1。两件都零 sorry 前置。
- **车道 B（4M6 簇）**：`SCS_4T3_IS_SCS_p32`（110–170）→ `EXTREMAL_SCS_4M6`（150–220）→
  `BB_4M6`/`MM_4M6`（70–115）→ `SCS_4M6_ARROW`（70–100）→ `NWDGKXH_p32`（25–45）。
  总 425–650，换 1 条锥内 −1；簇内可拆两个子车道。
- **车道 C（EDGE 簇）**：`EDGE_EQ_2_4I2_2/_3`（短）→ `EDGE_EQ_2_4I2`（118 HOL，最贵）→
  `EXPAND_DIAG_4_DIST` → `_1` → `_ALL` → `MM_4I2`（180–260）。总 540–780，换 1 条 −1。
  注意 `EDGE_EQ_2_4I2` 依赖已证的 `CUXVZOZ_p21`，无新 sorry。

**Wave 1（Wave 0 的杠杆一落地就发）**

- **车道 A**：`JCYFMRP_V3_p29`（30–50）+ `JLXFDMJ_p27`（600–800）→ 然后
  `SCS_4I2_IMP_SCS_4T1`（90–130）+ `SCS_4I1_IMP_SCS_4I2`（75–110）**同一车道一次交两笔**
  （前置三元组完全相同，一次摊薄）。→ −3 条（SCS_4I2/4I1/5M2 中的 2 条 + V3 不计数）。
- **车道 B**：`TFITSKCv1_p27`（500–650）→ `TFITSKC_p27`（20–35）。→ −1。
- **车道 C**：4M7 梯子（110–165）→ `YOBIMPP_p32`（45–80）；随后 4M8 梯子（235–600）→
  `MIQMCSN_p32`（45–80）。→ −2。

**Wave 2（重件/章级，单车道长跑）**

- `SCS_5M2_IMP_SCS_5T1_p29`（330–480）+ `IUNBUIG_p18`/`EGHNAVX_COLL_SCS_p18`/`xrr_le_1553_BB`
  （300–500）→ −1。建议按 §7 拆 2 子件。
- `SCS_6I1_BERAK_BY_CSTAB`（65–95）+ 3 条 LA1 wire（60–90）+ `SCS_6M1/6I1`（100–140）→ −1。

**Wave 3 / 冻结（外部阻塞，不要排期）**

- `LFLACKU_p23`：hNL 注册表（用户保留）→ BLOCKED。
- `OCBICBY_p22`：11 条 empty_* 无陈述 → BLOCKED。
- `UAGHHBM_p30`：2 条 isScs 限制件无陈述 + 1,598 HOL 行 → BLOCKED/XL。
- `TameLp.fully_surrounded_perimeter_bound`：WSEWPCH 1,150 HOL 行（章级）→ 冻结；
  若走 SF 通道把消费方改吃 ESTD 版，装配可降到 10–20 行，但那是陈述/消费面变更，需用户裁决。
- `URRPHBZ2`：Geom/Aff 闭性缺件 + Rogers giant → 冻结至 Geom 补件。
- `VPWSHTO_p15`：整章 11 件，净 −1 → 低 ROI 冻结。

### C.5 建议的"三条车道"一句话版

1. **车道 A（价值最高）**：real_model → JCYFMRP → V3 + JLXFDMJ → SCS_4I2/4I1；
2. **车道 B（独立闭环）**：4M6 梯子 → NWDGKXH → 4M7/4M8 → YOBIMPP/MIQMCSN；
3. **车道 C（总闸后续）**：EDGE 簇 → MM → TFITSKCv1 → TFITSKC；之后转 SCS_5M2/SCS_6I1。
   冻结项（LFLACKU/OCBICBY/UAGHHBM/TameLp/URRPHBZ2/VPWSHTO）不进车道。

---

## (D) 方法与证据

### D.1 实际使用的命令（摘要）

- `git log -1` / `git status --porcelain` / `git diff --stat d73bc595..HEAD -- lean/Kepler/Text`
- `grep -n`/`sed -n` 读：`lean/Kepler/Text/{LocalAuto15,20,21,22,23,27,29,30,32,33,TameLp,
  PackingAuto13,PackingAuto25,LocalConcl,LocalAuto1}.lean`
- HOL：`reference/flyspeck/text_formalization/local/*.hl`、`packing/*.hl`、
  `formal_lp/hypermap/ineqs/lp_main_estimate-compiled.hl`
- `python3 -I /tmp/textest_w1/{scan2,depscan,holspan,len,q}.py`（只读；脚本在 /tmp，不在被读目录内）
- 权威清单：`docs/e2e-reachability-map.tsv` 第 16–90 行（SORRIED 74 = 56 Assembly + 18 Text）
- 历史对照：`~/c17_backup/lane_snapshots/textside-triage/TEXT.tsv`（2026-11-06，23 条）、
  `docs/archive/lane-archives/cone-text-triage-w1/RANKED.md`、`docs/workorders/2026-11-06/w4-textside-26-triage.md`

### D.2 未做的事（纪律）

- **未** `lake build`、**未**整文件 `lean` 编译、**未**跑 `auto_gate.sh`、**未**跑地图仪器。
- **未**跑 `#print axioms`：侦察期间常驻 2 个 lean 进程，遵守"≥2 即等待/不启动"的约束。
  因此"谁依赖谁"全部是**静态三路互证**（HOL 实引 + Lean NEEDS + Lean 正文 token），
  没有内核级确认。这是本报告置信度普遍取"中"而非"高"的主因。
- 主仓 `git status --porcelain` 在交付时 = **0 行**。

### D.3 与旧 triage 的勘误（重要）

| 旧结论（2026-11-06 TEXT.tsv / RANKED） | 本报告实测（HEAD `0a1ff76d`） |
|---|---|
| `general_482` 自身 11 红 | **已真证**（784 行，0 Text sorry 引用）；11 红中只剩 `INTERIOR_ANGLE1_AZIM_p22` 仍 sorry 且未被引用 |
| `CUXVZOZ_p21` 体内无 sorry 但←general_482 | 同上，现已**完全干净** |
| `RRCWNSJ_p26` 锥内 SORRIED | **已真证**（LA26:1343） |
| `SCS_4I2_STRAIGHT(_ALL)` sorry | **已真证**（LA33:2161/2372） |
| `LEPJBDJ` 已证（TSV） | 确认已证（第一版扫描误报，剥注释后 sorry=False） |
| MIQMCSN/YOBIMPP 需 LA13 `SCS_OPP_REFL_p13`/`YXIONXL2_p13` | **可用已证的 `YXIONXL2_p33`（ScsV39 版）替代**；LA13 两条是 `ScsV39P13` 类型，本来也不能直接用 |
| `TFITSKC_p27` 门 = gen482 + LA7:954 | gen482 已闭；LA7:954 的 `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE` 现已真证（LA7:1174）⇒ 门只剩 `TFITSKCv1_p27` |
| `fully_surrounded_perimeter_bound` 三桥未移植 | yk11 波已把三桥免除，残余 = WSEWPCH 核（1,150 HOL 行） |

### D.4 UNRESOLVED 清单

1. `TFITSKCv1_p27` 的 "a,b near-diagonal linear program missing" 是否真缺件 —— HOL 体未直接引用，
   疑为 `mnт11` 注册表成分；需一次 100 行以内探针确认。
2. LA32 4M8 梯子的完整闭包（`SCS_4M8_ARROW_STEP_ONE` 的下游 `BB/MM_4M8_IMP_*` 未逐件展开）。
3. `SCS_5M2_IMP_SCS_5T1_p29` 是否能在 ~450 行内完成，或必须拆件。
4. TameLp 通用 `E` 陈述与 yk11 的 `ESTD` 专用桥之间的 gap：是否走 SF 通道（需用户裁决）。
5. `JLXFDMJ_p27` 的 `P_BBQUESTION` 步骤在 Lean 侧对应物（HOL 是原理而非具名引理）。

---

## 附：紧凑总表

| # | sorry | 位置 | 数学含义（一句） | 依赖（18 内 / 新拉入） | 被依赖 | 自身 EST | 置信 | 主要阻塞 |
|---|---|---|---|---|---|---|---|---|
| 1 | JCYFMRP_p27 | LA27:495 | 钉边存在性：∃ 相邻边 dist=2 | 18 内无 / 无（CUXVZOZ 已证） | JCYFMRP_V3→3 件 | 300–430 | 中 | 无 |
| 2 | LFLACKU_p23 | LA23:303 | `{3I1}→∅` 箭头 | 无 / TAUM_STD_POS+TAUM_EXTREMAL | JEJTVGB_p16 | 25–45 | 高 | hNL 注册表 |
| 3 | MIQMCSN_p32 | LA32:1576 | 4M8→{4M6',3T7,3T4} 箭头 | 无 / 5 条 LA32 + 2 条二阶 | MIQMCSN_discharged | 45–80 | 中 | 无（装债陷阱） |
| 4 | MM_4I2_IMP_4T2_4T1_p33 | LA33:2450 | 对角闭合 ⇒ 4T1∨4T2 非空 | 无 / EDGE 簇 6 件 | ARDBZYE_p33 | 180–260 | 中 | 无 |
| 5 | NWDGKXH_p32 | LA32:1030 | 4M6'→{4T3,4T5} 箭头 | 无 / 4M6 梯子 5 件 | NWDGKXH_discharged | 25–45 | 中 | 无 |
| 6 | OCBICBY_p22 | LA22:3856 | 14 个 T-系统→∅ | 无 / 3 现有 + 11 无陈述 | JEJTVGB_p16 | 70–110 | 中 | 11 条 empty_* 无陈述 |
| 7 | SCS_4I1_IMP_SCS_4I2_p33 | LA33:2487 | 4I1⇒4I2 非空 | 无 / V3_p29 + JLXFDMJ_p27 | SCS_4I1_ARROW… | 75–110 | 中 | 无 |
| 8 | SCS_4I2_IMP_SCS_4T1_p33 | LA33:1817 | 4I2⇒4T1 非空 | 无 / 同上（同一三元组） | ARDBZYE_p33 | 90–130 | 中 | 无 |
| 9 | SCS_5M2_IMP_SCS_5T1_p29 | LA29:3651 | 5M2⇒5T1 非空（终端不等式） | 无 / V3 + JLXFDMJ + IUNBUIG + xrr + EGHNAVX | HIJ_STEP_1_p29 | 330–480 | 低 | 无（体量/拆件） |
| 10 | SCS_6I1_BERAK_BY_CSTAB | LA20:1647 | 6I1→{6T1}+stab 箭头 | 无 / 2 条 hexagons + 3 条 LA1 wire | OEHDBEN_PRIME | 65–95 | 中 | LA1 注册表孪生（可转接） |
| 11 | TFITSKC_p27 | LA27:331 | 钉边沿链传递 ⇒ dist=2 | 无 / TFITSKCv1_p27 | TFITSKC_discharged | 20–35 | 高 | TFITSKCv1（500–650） |
| 12 | fully_surrounded_perimeter_bound | TameLp:925 | 全被包围扇周长 ≤ 2π | 无 / WSEWPCH（1150 HOL） | MQMSMAB | 10–20 | 高/UNRESOLVED | WSEWPCH 章级 |
| 13 | UAGHHBM_p30 | LA30:1204 | 子分保持 SCS 结构 | 无 / 2 条 isScs 限制件无陈述 | UAGHHBM_discharged | 800–1300 | 高 | 语句级缺口 + 1598 HOL |
| 14 | URRPHBZ2 | PA13:361 | Marchal cell 最终径向 | 无 / CLOSED_MCELL k=2 + U0_NOT… | QZYZMJC | 650–950 | 中 | Geom/Aff 缺件 + Rogers giant |
| 15 | VPWSHTO_p15 | LA15:398 | 五边形存在顶点两对角线 ≤1+√5 | 无 / 同章 10 件 | LA15 下游 | 150–230 | 中 | 整章 11 件（低 ROI） |
| 16 | YOBIMPP_p32 | LA32:1241 | 4M7→{4M6',3T3,3M1,3T4} | 无 / 2 条 LA32 + 4M7 子件 | YOBIMPP_discharged | 45–80 | 中 | 无 |
| 17 | general_482_deformation_p21 | LA21:4489 | 482 形变主定理 | — | 6 条下游 | **784（已兑现）** | — | 已闭（0a1ff76d） |
| 18 | real_model_ox3q1h_merge | PA25:10378 | ox3q1h 4 季界 | 无 / 无 | pkrmQuarter | 170–240 | 中-高 | 无 |

**一句话结论**：18 条里 **1 条已在侦察期真证**（g482，784 行），剩 17 条自身合计 3,050–4,640 行；
但按 DAG 去重后真实成本 **≈8,500–12,800 行**（自身只占 ~1/3），其中 **WSEWPCH（1,000–1,500）、
empty_*（1,400–1,900）、UAGHHBM（800–1,300）、URRPHBZ2（650–950）、JLXFDMJ（600–800）、
TFITSKCv1（500–650）** 是六个主要成本块。**当前门全绿、可立即开工的只有 5 组**：
real_model、JCYFMRP、EDGE 簇→MM、4M6 梯子→NWDGKXH、4M7→YOBIMPP；其余要么等杠杆，要么外部阻塞。

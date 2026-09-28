# mqmsmab-scout — 脊柱接口 A10（`Kepler.Assembly.mqmsmab`）深度侦察报告

> 2026-09-28 只读侦察交付物。对照基准 `reference/flyspeck`（HOL Light Flyspeck）。
> 纪律：零 .lean 改动；本文件为唯一新建。所有 file:line 均经 grep/sed 实测核对。
> 核心结论先行：**A10 的"章本体"（桥 + 装配）可单 lane 一波填完（预估 250–350 行，
> 机械接线为主）；真正的重量已不在 MQMSMAB 章**——KCBLRQC 桥与 JGTDEBU/CDTETAT/
> SZIPOAS/BDJYFFB 群已在 `Kepler/Text/TameLp.lean` 被先期波次全部真化，剩余 7 枚
> 上游 sorry（formal_lp 侧 + CRTTXAT）是独立子工程；**最大结构阻塞 = Assembly 侧
> `KcblrqcIneqDef := True` 弱编码占位，不清除则 mqmsmab 无法诚实填实**（§6.1）。

---

## 0. 接口与消费点定位

- **陈述**：`Kepler/Assembly.lean:466-471`
  ```lean
  theorem mqmsmab (V : Set V3) (hkcblrqc : KcblrqcIneqDef) (hmain : lp_main_estimate)
      (hfan : FAN 0 V (ESTD V)) (hc : Contravening V) :
      TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfan) := by
    sorry
  ```
- **HOL 原形**：`Mqmsmab.MQMSMAB`（`text_formalization/tame/ssreflect/MQMSMAB-compiled.hl:30-80`，
  17,025 字节；section 前提 `ineqs := kcblrqc_ineq_def` :24、`h_main := lp_main_estimate` :25，
  结论 `contravening V ==> tame_planar_hypermap (hypermap_of_fan (V,ESTD V))` :29-31，
  finalize :82）。
- **消费点**：`Assembly.lean:854`（textCapstone 内注记「contravening V →
  tame_planar_hypermap (fan-H V)（MQMSMAB）」），实际调用 `:857`
  `mqmsmab V hkcblrqc hmain hfanV hcV`；上游 `contraveningFan`（:457，已真化）供 `hfanV`。
- **HOL 消费侧**：`kepler_conjecture_with_assumptions`（the_main_statement.hl:170-251）中
  与 Lean textCapstone :857 同位。
- **债务图行**：`docs/e2e-debt-map.md:21`（A10，分级「中大」，否重型机）、`:44`
  （"MQMSMAB 章（A10）：ssreflect 17KB，相对小"）。**该行注记已过时**：`+ KCBLRQC 桥`
  部分已于 TameLp 波次清偿（见 §2）。

---

## 1. 逐名对照表（HOL ↔ Lean，陈述内涉及的每个名字）

### 1.1 陈述层

| HOL 名 | Lean 名（Assembly 侧，陈述所用） | Lean 名（TameLp 侧，填证所用） | 锚点 |
|---|---|---|---|
| `Mqmsmab.MQMSMAB` | `mqmsmab` | — | Assembly.lean:466；MQMSMAB-compiled.hl:30 |
| `contravening` | `Contravening` | `Contravening`（同体镜像） | Assembly.lean:68；TameLp.lean:325；tame_defs.hl:248 |
| `kcblrqc_ineq_def` | `KcblrqcIneqDef` **:= True 占位** | `KcblrqcIneqDef`（四切片真形） | Assembly.lean:189；TameLp.lean:510；tame_lemmas-compiled.hl:34-46 |
| `lp_main_estimate` | `lp_main_estimate` = `JEJTVGB_concl` | 同一（复用，无孪生） | LocalAuto16.lean:185；LocalAuto1.lean:563；JEJTVGB.hl:232 |
| `tame_planar_hypermap` | `TamePlanarHypermap`（§2b，orbitSet 版） | `TamePlanarHypermap`（Hypermap.node/face 版） | Assembly.lean:406；TameLp.lean:483；tame_defs.hl:180-184 |
| `hypermap_of_fan (V,ESTD V)` | `hypermapOfFan 0 V (ESTD V) hfan`（裸版，`instDecidableEqProd` 实例） | `hypermapOfFanTl V (ESTD V) hfan`（`dartDecEq2` 重标版） | Fan.lean:1169；TameLp.lean:62-84；TameLp.lean:86-99 字段相等桥 |
| `FAN (vec 0,V,E)` 前提 | `FAN 0 V (ESTD V)` | 同一 | 折算注记 Assembly.lean:122-126 |

`tame_planar_hypermap` 十二合取（tame_defs.hl:180-184 = `tame_1 ∧ tame_2 ∧ tame_3 ∧
tame_4 ∧ tame_5a ∧ tame_8 ∧ tame_9a ∧ tame_10 ∧ tame_11a ∧ tame_11b ∧ tame_12o ∧ tame_13a`）：

| 合取项 | Assembly §2b（orbitSet/setSumSpec 版） | TameLp（Hypermap 版） | HOL |
|---|---|---|---|
| tame_1 | `Tame1` Assembly.lean:377（PlainHypermap :271 / PlanarHypermap :274） | `Tame1` TameLp.lean:451 | tame_defs.hl:136 |
| tame_2 | `Tame2` :379（ConnectedHypermap :279 / SimpleHypermap :282） | `Tame2` :453 | :140 |
| tame_3 | `Tame3` :381 | `Tame3` :455 | :144 |
| tame_4 | `Tame4` :382（NoLoops :289） | `Tame4` :457（NoLoops :363） | :146 |
| tame_5a | `Tame5a` :383（IsNoDoubleJoins :293） | `Tame5a` :459 | :148 |
| tame_8 | `Tame8` :384 | `Tame8` :461 | :153 |
| tame_9a | `Tame9a` :389（faceOrbit :265） | `Tame9a` :463 | :156 |
| tame_10 | `Tame10` :392 | `Tame10` :466 | :160 |
| tame_11a | `Tame11a` :395（nodeOrbit :264） | `Tame11a` :469 | :164 |
| tame_11b | `Tame11b` :397 | `Tame11b` :472 | :168 |
| tame_12o | `Tame12o` :399（NodeTypeExceptionalFace :323 / NodeExceptionalFace :327） | `Tame12o` :475（:398/:402） | :172 |
| tame_13a | `Tame13a` :402 | `Tame13a` :478 | :176 |

### 1.2 MQMSMAB 证明体消费件（按 compiled.hl tactic 步序）

| HOL 名 | Lean 名 | 状态 | 锚点（HOL / Lean） |
|---|---|---|---|
| `contravening_lp_fan`（section Contravening finalized） | `contravening_lp_fan` | ★真证明 | lp_ineqs_proofs-compiled.hl:385,533 / TameLp.lean:825（内核 `contravening_lp_fan_of_fan` :808 + `contravening_fanTl` :795） |
| `lp_fan`（def） | `LpFan` | def 已镜像 | lp_ineqs_proofs-compiled.hl:9-12 / TameLp.lean:338 |
| `COMPONENTS_HYPERMAP_OF_FAN` | `COMPONENTS_HYPERMAP_OF_FAN` | ★真证明 | hypermap_and_fan.hl:495 / TameLp.lean:541 |
| `CRTTXAT`（assumption 形） | `CRTTXAT` | **sorry** | CRTTXAT.hl:311-320（证明体 :320-470，>250 行） / TameLp.lean:1999-2005 |
| `JGTDEBU4`（simple） | `JGTDEBU4` | ★ | JGTDEBU.hl:81 / TameLp.lean:1040 |
| `fully_surrounded_perimeter_bound` | 同名 | **sorry** | lp_main_estimate-compiled.hl:1530-1543 / TameLp.lean:832-837 |
| `tame_9a`（结论重写） | `Tame9a` | def | tame_defs.hl:156 / TameLp.lean:463 |
| `JGTDEBU10`（tame_10） | `JGTDEBU10` | ★ | JGTDEBU.hl:215 / TameLp.lean:1164 |
| `JGTDEBU11`（tame_11a） | `JGTDEBU11` | ★ | JGTDEBU.hl:241 / TameLp.lean:1226 |
| `SZIPOAS`（tame_11b） | `SZIPOAS` | ★ | CDTETAT.hl:306 / TameLp.lean:1808 |
| `BDJYFFB1`（tame_12o） | `BDJYFFB1` | ★ | KCBLRQC-compiled.hl:917 / TameLp.lean:1906 |
| `JGTDEBU1/2`（tame_1） | 同名 | ★ | JGTDEBU.hl:49,61 / TameLp.lean:1013,1021 |
| `JGTDEBU3/4`（tame_2） | 同名 | ★ | JGTDEBU.hl:69,81 / TameLp.lean:1033,1040 |
| `JGTDEBU5`（tame_3） | 同名 | ★ | JGTDEBU.hl:93 / TameLp.lean:1049 |
| `JGTDEBU6`（tame_4） | 同名 | ★ | JGTDEBU.hl:101 / TameLp.lean:1064 |
| `JGTDEBU7`（tame_5a） | 同名 | ★ | JGTDEBU.hl:109 / TameLp.lean:1090 |
| `JGTDEBU8`（tame_8） | 同名 | ★ | JGTDEBU.hl:133 / TameLp.lean:1118 |
| `tame_13a` + `admissible_weight` + `total_weight` | `Tame13a`/`AdmissibleWeight`/`totalWeight` | def | tame_defs.hl:176,129,112 / TameLp.lean:478,442,421 |
| `tgt` | `Kepler.Text.tgt`（LocalAuto1.lean:198）；Assembly 自有 `tgt` :331（同值 1.541） | def | appendix.hl:106 |
| `sum_tauVEF_upper_bound` | 同名 | **sorry** | tame_lemmas-compiled.hl:529-538（section FullySurrounded :286-290，finalize :638） / TameLp.lean:912-917 |
| `Flyspeck_constants.bounds`（4π−20sol0 < tgt 算术） | `sol0Bounds_p19`（LocalAuto19.lean:330，0.551285 < sol0 < 0.551286）+ π 区间（`Real.pi_gt_d4` 等，CDTETAT 已用） | ★可用 | MQMSMAB-compiled.hl 步 18 / LocalAuto19.lean:330 |
| `darts_k` | `dartsK` | def | list_hypermap-compiled.hl:19 / TameLp.lean:355 |
| `d_tame` | `Kepler.Text.dTame`（LocalAuto1.lean:200）；Assembly 自有 :334（同值表） | def | appendix.hl:108 |
| `ineq_tau3_tauVEF_std` | 同名（前提 `JEJTVGB_std3_concl`） | **sorry** | lp_main_estimate-compiled.hl:714-731 / TameLp.lean:927-932 |
| `ineq_tau4_tauVEF_std` | 同名（前提 `JEJTVGB_std_concl`） | **sorry** | :796-817 / TameLp.lean:935-940 |
| `ineq_tau5_tauVEF_std` | 同名 | **sorry** | :889-915 / TameLp.lean:943-948 |
| `ineq_tau6_tauVEF_std` | 同名 | **sorry** | :988-1015 / TameLp.lean:951-956 |
| `adm_1/2/3` | `Adm1/Adm2/Adm3` | def（Assembly `Adm3` :369 为 **True 占位**；TameLp `Adm3` :437-439 为忠实原形） | tame_defs.hl:115,118,124 / TameLp.lean:425,429,437；Assembly.lean:358,362,369 |
| `KCBLRQC` | `KCBLRQC` | ★ | KCBLRQC-compiled.hl:868-873 / TameLp.lean:1877 |
| `BDJYFFB2` | `BDJYFFB2` | ★ | KCBLRQC-compiled.hl:962-967 / TameLp.lean:1979 |
| `a_tame` / `b_tame` | `aTame`（:406）/`bTame`（:409；Assembly :339 同值表） | def | tame_defs.hl:110,81-100 |
| `type_of_node` | `typeOfNode` | def | tame_defs.hl:62 / TameLp.lean:391；Assembly.lean:317 |
| `set_of_triangles_meeting_node` / `set_of_face_meeting_node` / `set_of_exceptional_meeting_node` | 同名驼峰版 | def | tame_defs.hl:46,58,54 / TameLp.lean:371,386,381；Assembly.lean:301,313,309 |
| `tauVEF` | `Kepler.Text.tauVEF_p2`（无孪生） | def | localization.hl:1559 / LocalAuto2.lean:354 |
| `NODE_TYPE_lemma`（KCBLRQC/BDJYFFB1 内核） | `NODE_TYPE_lemma` | ★ | tame_general.hl:488-495 / TameLp.lean:841-915 |
| `JEJTVGB_std_concl` / `JEJTVGB_std3_concl`（ineq_tauK 群前提） | 同名（`lp_main_estimate` = 六合取，`hmain.1`/`hmain.2.1` 直接供给） | def | appendix.hl:116,126 / LocalAuto1.lean:502,511 |

★ = TameLp.lean 中已有真证明（0 error，无 sorry）。TameLp 全文件 85 条 theorem，
**仅 7 枚 sorry**（DEBT.md:67 在账）：`:837 fully_surrounded_perimeter_bound`、
`:917 sum_tauVEF_upper_bound`、`:932/:940/:948/:956 ineq_tau3/4/5/6_tauVEF_std`、
`:2005 CRTTXAT`。

---

## 2. TameLp.lean 骨架盘点（`lean/Kepler/Text/TameLp.lean`，2039 行）

**已有真证明（含重型件，全部 0 error）**：
- §0 重标层：`hypermapOfFanTl` + 字段相等桥（:86-99）+ 逐谓词 congr 家族
  （`numberOfNodes/Edges/Faces/Components_congr_inst` :160-190、`Planar/Connected/
  Simple_congr_inst` :200-226、`SimpleTl/PlanarTl/ConnectedTl` :264-283、
  `faceInjOn_of_node` :288）——**裸版 ↔ Tl 版实例重标转移已备好**。
- §1 原语 def 层（:305-509，忠实镜像，无 sorry）：ESTD/ECTC/scriptL/Contravening/
  FullySurrounded/LpFan/PerimeterBound/dartsK/NoLoops/set_of_*_meeting_node/
  typeOfNode/aTame/bTame/totalWeight/Adm1-3/Tame1-13a/TamePlanarHypermap/
  `KcblrqcIneqDef` 四切片真形（:510-532）。
- §2 dart 层（:534-795 全真）：`COMPONENTS_HYPERMAP_OF_FAN`、e/n/f 点态 apply、
  轨道显式形（`edgeMapTl_iterate`/`nodeMapTl_iterate`）、`DART_EXISTS_TL`、
  `SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL`、`SURROUNDED_IMP_CARD_NODE_GE_3_TL`、
  `nodeTl_eq_image`。
- §3 边界件（:795-956）：`contravening_fanTl`★、`contravening_lp_fan`★；
  **sorry 6 枚**（perimeter bound / sum_tauVEF / ineq_tauK×4）。
- §4 JGTDEBU 群（:966-1235 全真）：`contraveningConformingTl` + JGTDEBU1-8/10/11。
- §4b/5（:1242-1852 全真）：setSum 计数辅助、`CDTETAT_lemma1`（21 情形算术）、
  `CDTETAT`、`SZIPOAS`、`NODE_TYPE_lemma`、`CARD_NODE_EQ_SUM_NODE_TYPE_TL`。
- §6（:1877-1991 全真）：`KCBLRQC`、`BDJYFFB1`、`BDJYFFB2`（b_tame 表 20+6 情形
  算术已由 `cdTetatPairs_*` 系消化）。
- §7（:1999-2005）：`CRTTXAT` **sorry**（最重单件）。
- §8 债务图锚点备忘（:2008-2036）已预写 mqmsmab 消费映射（与本次侦察一致）。

**结论**：e2e-debt-map A10 行所注「+ KCBLRQC 桥」的桥章部分**已清偿**。A10 剩余
= ①Assembly 侧桥/装配层（本报告 §4 作战计划）②TameLp 7 枚上游 sorry（formal_lp
侧子工程，独立 lane）。

---

## 3. HOL 证明体步序 → Lean 形态（MQMSMAB-compiled.hl 步 1-46）

HOL 脚本分五段：
1. **步 1** 展开 `tame_planar_hypermap` → 十二合取目标；
2. **步 2-12** 结构合取：`contravening_lp_fan contrV`（→fanV/f_surr/subV/packV）+
   `CRTTXAT (JGTDEBU4 contrV) (fully_surrounded_perimeter_bound fanV f_surr)`
   收 tame_9a；`JGTDEBU10/11/SZIPOAS/BDJYFFB1` 收 tame_10/11a/11b/12o；
   `JGTDEBU1-8` 收 tame_1/2/3/4/5a/8；
3. **步 13-19** tame_13a：`∃w. w := \f. tauVEF (V,ESTD V,f)`；`sum_tauVEF_upper_bound`
   + `REAL_LT_IMP_LE`（contrV 的 scriptL > 12）+ Flyspeck 常数算术收
   `total_weight < tgt`；
4. **步 20-36** adm_1：`d ∈ darts_k k H` 辅助 + `3 ≤ a ≤ 6 → a∈{3,4,5,6}` 枚举 ×
   `ineq_tauK_tauVEF_std`（每条内嵌 `lp_main_estimate` 侧目标 —— Lean 侧折算为
   直接喂 `hmain.1`/`hmain.2.1`，见 §1.2 末行注）；
5. **步 37-46** adm_2（`KCBLRQC` let-形，r=0 分支）+ adm_3（`BDJYFFB2` +
   `set_of_triangles_meeting_node = {f ∈ set_of_face_meeting_node d | card f = 3}`
   的 EXTENSION 集合等换元）。

Lean 的 mqmsmab 本体就是把这五段翻译成 `refine ⟨?_,?_,…⟩` + TameLp 定理调用 +
§4 桥层改写，**无新数学**。

---

## 4. 证明作战计划（有序步骤，每步带锚点与预期 Lean 形态）

### Step 0（前置决策，编排者拍板）：`KcblrqcIneqDef` 统一 —— 阻塞件
- 现状：Assembly.lean:189 `def KcblrqcIneqDef : Prop := True`（PLACEHOLDER(P6-E)）；
  TameLp.lean:510-532 已有「本章消费切片」真形（azim 双边界 + b_tame r=0 表 +
  6 类型矛盾 + (5,0,1) 行 ≥0.6366），TameLp.lean:506 注记自认「两处接口在 G4
  落地后统一」。
- 消费链事实：`KCBLRQC/BDJYFFB1/BDJYFFB2/SZIPOAS/CDTETAT` 的 `hineq` 前提是真
  内容（DIH_Y_INEQ 等机器不等式），**不可能从 `True` 推出**。不改陈述则 A10 永远
  无法诚实填实。
- 动作（二选一，推荐 a）：
  a. Assembly.lean 加 `import Kepler.Text.TameLp`，`def KcblrqcIneqDef : Prop :=
     Kepler.Text.TameLp.KcblrqcIneqDef`（一行 def 替换 + 一行 import）。消费方
     `TheNonlinearInequalities`（:199）第 6 分量自动带真内容；占位定理
     `nonlinearInequalities`（:823 sorry，A11）仍 sorry，不破坏现状。
  b. 不 import，在 Assembly 内逐字抄 TameLp:510-532 切片（新增 ~25 行，零跨模块
     风险，但制造受控孪生，TameLp.lean:507 注记预设了此路：「两处接口在 G4 落地
     后统一」）。
- 闸门性质：def 行是结构行，替换须走 **STATEMENT-FIX 模式**（GATE_MODE=STATEMENT-FIX
  + SF_PATCH 归档 + docs/statement-fix-proposals.md 挂项，HOL 引证
  `kcblrqc_ineq_def = tame_lemmas-compiled.hl:34-46` 的 mk_conj 过滤大合取，
  Lean 折算 = 其 MQMSMAB/KCBLRQC/BDJYFFB 消费切片，保真论证可直接引
  TameLp.lean:495-509 的四切片注记）。

### Step 1：Assembly 桥层（~80-120 行，全部机械）
在 Assembly.lean §2c 附近新增私件（或直接内联在 mqmsmab 证明里）：
- B1 `ESTD/ECTC/scriptL/Contravening` 恒等：Assembly:58-75 与 TameLp:309-330 两处
  def 体逐句相同（`Packing`/`ballAnnulus`/`surroundedNode` 同源），预期
  `rfl` 或一次 `unfold` 后 `rfl`；
- B2 轨道桥：`orbitSet p x = Hypermap.orbitMap p x`（Assembly:260
  `Set.range (n ↦ p^n x)` vs Hypermap.lean:708 `{y | ∃ n, (p^n) x = y}`；
  `Set.mem_range` 一步；TameLp.lean:362 注记已预判「可相互 defeq 折算」）；
- B3 十二合取桥 `tamePlanarHypermap_tl {H} (h : TameLp.TamePlanarHypermap H) :
    Assembly 语义的 TamePlanarHypermap H`：逐合取 `unfold`+`exact`（B2 代入
  faceOrbit/nodeOrbit；`setSumSpec` Assembly:350 与 `setSum` PackingAuto2.lean:124
  体恒等 → `Tame13a` 的 `totalWeight`/`tgt`/`dTame`/`bTame` 全 rfl 级；
  `Adm3` 方向 TL→A 落到 True，免证）；
- B4 实例重标桥（**最易翻车，先单独验编译**）：裸 `hypermapOfFan 0 V (ESTD V)
  hfan`（`instDecidableEqProd`）上的 `TamePlanarHypermap` ↔ Tl 版。装配 §0b congr
  家族（TameLp:110-226）+ 字段相等（:87-99）拼 12 条短引理（估 60-100 行）；
  AzimBridge.lean:64-72 是同型先例。

### Step 2：mqmsmab 组装（~150-220 行，纯接线）
按 §3 五段翻译，骨架：
```lean
theorem mqmsmab V hkcblrqc hmain hfan hc := by
  obtain ⟨hlpfan⟩-ish := contravening_lp_fan V hc      -- TameLp:825 ★
  have h9a := CRTTXAT (fun V hfan hc => B4(JGTDEBU4 …)) V hc hfan
      (fully_surrounded_perimeter_bound … hlpfan.2.1)  -- 上游 sorry 流动
  refine B3 ⟨JGTDEBU1…, JGTDEBU3+4…, JGTDEBU5…, JGTDEBU6…, JGTDEBU7…,
    JGTDEBU8…, h9a, JGTDEBU10…, JGTDEBU11…, SZIPOAS hkcblrqc'…,
    BDJYFFB1 hmain hkcblrqc'…, ?_⟩
  -- tame_13a：
  refine ⟨fun f => tauVEF_p2 V (ESTD V) f, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- Adm1：rcases Tame9a → a∈{3,4,5,6} → ineq_tauK_tauVEF_std hlpfan hmain.2.1/.1 d dartsK-成员
  · -- Adm2：r=0 归约 + KCBLRQC hmain hkcblrqc' Or.inr 分支
  · -- Adm3：BDJYFFB2 + setSum 集合等换元（setOfTriangles vs 限定子集）
  · -- total_weight：sum_tauVEF_upper_bound（12 ≤ scriptL V = hc.2.2.1.le）
  --   + sol0Bounds_p19/π 区间 norm_num-linarith 收 4π−20sol0 < 1.541
```
注意点：`d ∈ dartOfFan` 从 `d ∈ H.darts` 经 `dartsTl_coe`（TameLp:561）+
`Set.mem_union_right`（CDTETAT :1694 内部同款两行）；`hkcblrqc'` = Step 0 统一后
的切片（或 B1 系 defeq 直传）。

### Step 3（收尾）：DEBT/债务图更新
- e2e-debt-map.md A10 行改「已闭合（上游 7 枚 sorry 流动）」；DEBT B 表增 TameLp
  上游行（若编排者愿细列）。Assembly `Adm3` 真化（抄 TameLp:437-439 三行）建议
  顺带入同一 STATEMENT-FIX 补丁——**可选项**，A9 才真正消费它（见 §6.2）。

### Step 4（独立 lane，不在 A10 关键路径）：TameLp 7 枚上游
按 TameLp.lean:2020-2036 §8 优先序：`fully_surrounded_perimeter_bound`（Polar_fan
章移植，FAN_PERIMETER/WSEWPCH/f_surr_localization_convex_local）→
`sum_tauVEF_upper_bound`（tauVEF_alt2_alt + fully_surrounded_sum_sol + HRXEFDM_lemma1，
HOL 仅 ~9 步但依赖 HRXEFDM 章）→ `ineq_tauK_tauVEF_std`×4（FaceK 分支不等式链，
各 ~15-30 步 HOL tactic）→ `CRTTXAT`（最重，CRTTXAT_lemma1/2/1' + arc_properties
章 + per 周长轨道和，HOL :320-470）。

---

## 5. 分级复核

- **「中大」：成立，但内涵需修正。** debt-map 行注「MQMSMAB 章（ssreflect 17KB）
  + KCBLRQC 桥」——实测：MQMSMAB-compiled.hl 17,025 字节确为小章；KCBLRQC 桥
  （KCBLRQC-compiled.hl 139KB 的消费切片）**已被 TameLp 波次清偿**。剩余真实工作
  = 桥/装配层 250-350 行（**中**）+ 7 枚上游 sorry（**中大**，其中 CRTTXAT 单件
  ~200-300 行 Lean、formal_lp 四件合计 500-900 行，均可各自独立立项）。
- **行数预估**：
  - A10 本 lane（Step 0-3，Assembly.lean 单文件）：**250-350 行**（桥 80-120 +
    组装 150-220 + def/import 变更 ~15-30）。
  - 上游清零（TameLp.lean，另计）：CRTTXAT 200-300 + perimeter/sum_tauVEF 200-350
    + ineq_tauK×4 350-600 ≈ **750-1250 行**，属 formal_lp 侧子工程，不阻塞 A10
    「接线完成」（sorry 合法流动，同 ContraFan/T5 先例：Assembly.lean:449-451 注记
    明示该模式已被接受）。

---

## 6. 阻塞与风险

### 6.1 结构阻塞（最大件）
1. **`KcblrqcIneqDef := True` 弱编码**（Assembly.lean:189）：无它则 mqmsmab 不可
   诚实填实（KCBLRQC/BDJYFFB1/2/SZIPOAS 需真前提）。修复 = Step 0，需编排者拍板
   + STATEMENT-FIX 豁免。这属于「前提侧弱编码」：与 planar-encoding-fix §1.2
   polyhedronC「换谓词」不同，它是「省略内容」，修复方向单一（换入 TameLp 真切片），
   无语义分歧风险——但**必须**在填证前落地，否则填出的「真证明」是空壳
   （facetOfC 前科自查：占位会让下游定理**空洞化**；此处占位让定理**不可证**，
   两类病，后者反而安全——填不动就会暴露）。
2. **`Adm3` True 尾**（Assembly.lean:369-371）：`TamePlanarHypermap_A` 严格弱于
   HOL 原形。对 A10 无害（TL→A 桥单向、下游 tamePlanarHypermapRestricted :482 只
   拆 9a/11a/8），但 **A9 `jcajydu` 填实时必须同步真化**（抄 TameLp:437-439），
   否则 weak encoding 隐患后移。同族：`GoodGraphV4` 四 True（:445-455），
   A7-A9 债务，不在本 lane。

### 6.2 ssreflect/计数结构译解难点（实测评估）
- **ssreflect 用量近零**：MQMSMAB 脚本是 HOL Light 经典 rewrite 链（use_arg_then2/
  new_rewrite/case/move + inE/IN_ELIM_THM/EXTENSION/GSPEC-set_tac），无 `/set`
  bigop 重排。所有 CARD 计数论证（SIMPLE_HYPERMAP_lemma、NODE_SET_AS_IMAGE 等）
  已在 TameLp §2/§4 移植完毕。
- 真正要小心的四点：
  a. **实例重标**（§4 B4）：`mqmsmab` 结论用裸 `hypermapOfFan`，TameLp 定理全在
     `hypermapOfFanTl` 上；dot 投影实例合成两侧烤定不同（AzimBridge.lean:64-72
     注记）。B4 必须最先单独验编译。
  b. **let-形定理消费**：HOL `let_RULE KCBLRQC/BDJYFFB2` 的双层 let；Lean 版已
     encode 为 `intro H p q r` 前提形（TameLp:1877 KCBLRQC 自证即示范），照抄
     `show` 归一即可。
  c. **adm_3 的 setSum 集合等换元**（HOL 末步 EXTENSION）：`setSum {f ∈ S | ncard f
     = 3} w = setSum (setOfTrianglesMeetingNode H d) w`，`Set (Set V3)` 上 ext+
     `Set.mem_setOf_eq`，TameLp setSum 系（:1252-1300）有同型先例。
  d. **4π − 20·sol0 < 1.541 算术**：`sol0Bounds_p19`（LocalAuto19.lean:330）+
     π 区间 + `norm_num`/`linarith`，低风险。
- **dartsK 情形枚举**（HOL `repeat_tactic 1 9 case` ×4 情形）：Lean `rcases` +
  `omega` + `dTame` if-展开 `split_ifs`，机械。

### 6.3 移植保真自查（planar-encoding-fix 前科对照）
- 常数表核对无误：dTame（0/0.206/0.4819/0.712/tgt）、bTame 15 行表、aTame 0.63、
  tgt 1.541、0.6366 = 0.626·6.28319 − 0.7199 − 3.85（TameLp:502-504 注记）在
  Assembly 与 TameLp 两侧同值（rfl 级孪生，非分歧）。
- 已知偏差（均为注记在案的**有意**折算，非误移植）：`hypermapOfFan` proof-
  parameterized（Assembly:122-126 注记）；darts = dart1_of_fan（孤立 dart 在
  contravening 语境排除，TameLp:537-540 注记）；HOL `ineq_tauK` 的 lp_main_estimate
  侧目标在 Lean 改为显式 `JEJTVGB_*_concl` 前提（更干净，喂 `hmain` 分量即可）。
- **无 SUM_INTER 式 junk 语义分叉**：两侧 `sum` 均折算为同一支撑约定
  （`setSum`/`setSumSpec` 同体）。

---

## 7. lane 拆分建议

- **推荐单 lane**：lane 文件 = `lean/Kepler/Assembly.lean`，目标 = Step 0-3。
  理由：桥层与组装强耦合（B3/B4 的形状由组装需要反推），拆两波要重复编译启动成本；
  250-350 行对一波填证工人是正常负载（对照 playbook §2「~70% 机械题」节奏）。
- **auto_gate 用法**：`FILE=Kepler/Assembly.lean`；`LANE_FILES=lean/Kepler/Assembly.lean`
  （**替换式**白名单，playbook §6 防再犯条：勿忘带 lane 文件自身）。本机无其他
  lane 并行时缺省即含 FILE。
- **闸门模式二分**（若 Step 0 与 Step 1-3 同波）：def 行替换走 STATEMENT-FIX
  （SF_PATCH 归档补丁 + proposals 挂项 + HOL 引证），其余为纯新增行。若编排者求
  稳可拆两波：波 1 = Step 0（STATEMENT-FIX 闸，~30 行）；波 2 = Step 1-3（普通
  fill 闸，~250-320 行）。**纯新增行里不得出现 sorry**（上游 7 枚以「消费含 sorry
  定理」的形式流动，不在本文件新增 sorry 行，合规）。
- **上游 7 枚拆分**（独立立项，均 lane 文件 = `lean/Kepler/Text/TameLp.lean`）：
  lane U1 = `CRTTXAT`（单件最重）；lane U2 = `fully_surrounded_perimeter_bound` +
  `sum_tauVEF_upper_bound`（Polar_fan/HRXEFDM 章）；lane U3 = `ineq_tauK`×4 群
  （FaceK 链）。均不与 A10 lane 抢文件（一个在 Assembly 一个在 TameLp），理论上
  可并行，但编排者需注意 TameLp 是 U1-U3 的共同 lane 文件——**串行轮换**。
- **与 KCBLRQC 桥的先后关系**：无先后——桥已真化，A10 lane 只消费。唯一前置 =
  Step 0 的 KcblrqcIneqDef 统一决策（编排者拍板 + 豁免），以及把
  `import Kepler.Text.TameLp` 加进 Assembly（TameLp 不 import Assembly，无环，
  已核实全树当前无人 import TameLp）。

## 8. 侦察结论一句话

A10 已从「中大盲盒」降维为「一笔机械接线（250-350 行，单 lane 一波）+ 一个陈述
统一决策（KcblrqcIneqDef，STATEMENT-FIX 豁免）」；真数学余量在 TameLp 上游 7 枚
（formal_lp 侧，另立 U1-U3，约 750-1250 行），不阻塞脊柱接线。

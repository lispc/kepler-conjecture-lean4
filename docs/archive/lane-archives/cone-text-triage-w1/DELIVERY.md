# DELIVERY — 锥内 Text 层（除 PA25）SORRIED 分诊结论

车道：`cone-text-triage-w1`（只读；零证明、零仓内改动）
读时 HEAD：`8a91eaaa`（任务书给定）→ 期间其他车道推进到 `b49461bb`；行号按 `b49461bb` 工作树复核。
输入快照：`docs/e2e-reachability-map.tsv` 基线 N @ `7c59149c`。

---

## 1. 口径（写进 TRIAGE.tsv 的 class / dep_status 定义）

- **dep_status**：按该声明 DISCHARGES/NEEDS 注记点名的每个件 `grep -n` 到声明处并读体，递归 ≥2 层。
  - `CLEAN` = 全部依赖成 `:= by` 且递归闭包无 sorry；
  - `TAINTED:<n>` = n 个直接依赖仍 sorry（括号内列名+行号）；
  - `MISSING` = 依赖名全仓 0 命中或来源不在仓内；
  - `MNT11` = 签名或依赖真的吃 `main_nonlinear_terminal_v11` 的 sorryAx。
- **class**：可证性闸门。
  - 依赖链全绿 → 按本体尺度 `S`（≤120 行）/ `M`（120–450）/ `L`（>450 或需新 kit）；
  - 任一依赖仍 sorry/MISSING → `BLOCKED`，根节点名字+行号写进 dep_status，本体尺度与最近前置写进 next_action；
  - `DEFHOLE` = 陈述/定义为洞或假。
  - `CLOSED`（本表新增的对账值，仅 1 行）= TSV 快照过时、HEAD 已证。

---

## 2. 计数

从 TSV `--- SORRIED ---` 节取 `Kepler.Text.*` 行，按任务书排除 PA25（19 条）、LocalAuto11 `PQCSXWG2_WITHINREAL_p11`（in flight）、LocalAuto18 `AURSIPD_p18`（已闭）、LocalConcl 两条 anchor（`_private.Kepler.Text.LocalConcl.0.*`），**得 19 行**。

| 档 | 条数 | 名单 |
|---|---:|---|
| **S** | **0** | — |
| **M** | **1** | `RRCWNSJ_p26`（LocalAuto26:829，deps 全绿） |
| **L** | **1** | `SCS_5M2_IMP_SCS_5T1_p29`（LocalAuto29:3651，deps 全绿但重型/需新 kit） |
| **BLOCKED** | **16** | `MM_4I2_IMP_4T2_4T1_p33`、`SCS_4I1_IMP_SCS_4I2_p33`、`SCS_4I2_IMP_SCS_4T1_p33`、`JCYFMRP_p27`、`TFITSKC_p27`、`NWDGKXH_p32`、`YOBIMPP_p32`、`MIQMCSN_p32`、`LFLACKU_p23`、`OCBICBY_p22`、`SCS_6I1_BERAK_BY_CSTAB`、`UAGHHBM_p30`、`general_482_deformation_p21`、`VPWSHTO_p15`、`URRPHBZ2`、`TameLp.fully_surrounded_perimeter_bound` |
| **DEFHOLE** | **0** | —（本批无 `ox3q1hP25` 型陈述/定义洞） |
| **CLOSED**（快照过时） | **1** | `NUXCOEAv2_p28`（LocalAuto28:8037；HEAD 由 `ad7e9dba` 闭合，探针标准三） |
| 合计 | **19** | |

---

## 3. 关键修正：MNT11 口径已死（本车道最重要的机器发现）

任务书与 `docs/axiom-ledger.md` §2.3a 都假定「陈述提及 `main_nonlinear_terminal_v11` ⇒ `#print axioms` 必含 sorryAx（常量级污染）」。**该结论在 HEAD 已失效**：

- `main_nonlinear_terminal_v11` 已由 terminal11-T0（`a522078c`）从 `def … := sorry` 物化为真定义
  `def main_nonlinear_terminal_v11 : Prop := ∀ id ∈ mainNonlinearTerminalV11Ids_t11, get_main_nonlinear id`
  （`lean/Kepler/Text/LocalAuto1.lean:2139`），访问器返回的 109 条 `mainEstimate_*` 都是**具体 Prop 定义**
  （例：`noncomputable def mainEstimate_4717061266 : Prop := ∀ y1…y6, … deltaY … > 0`，`LocalAuto1.lean:1894-1897`），
  不是 sorry 项。
- 探针（standalone lean，`LEAN_PATH=/tmp/lfainteg/asm_check/leanpath.txt`，RC=0）：
  `theorem tiny_probe (_h : main_nonlinear_terminal_v11) : True := trivial`
  → `'Kepler.Text.tiny_probe' depends on axioms: [propext, Classical.choice, Quot.sound]`（**无 sorryAx**）。

**后果**：TRIAGE.tsv 里 **没有任何一行判 MNT11**。13 条签名含 mnt11 的件不再是「银行债不可清」——它们的阻塞全部来自具体依赖（`general_482` 链、`JLXFDMJ`、`TFITSKCv1`、`RRCWNSJ`、`TAUM_STD_POS`、`SCS_6M1_IMP_SCS_6T1` 等）。**真正剩下的银行锚**是 `LocalConcl.lean:1988 mnt11_anchor` / `:1994 p21_anchor`（装配层 `:= sorry`），以及 `Assembly.nliMainNonlinearTerminalV11`；它们不在本层 19 条的直接依赖里。

---

## 4. 无重型计算下真正可做的总量

「可做」= 依赖链无 bank/MISSING，且本体 ≤450 行、不需新 kit。

- **立即可发车（TSV 行）**：**1 条** — `RRCWNSJ_p26`（M，250–400 行）。但带风险：HOL 证明另引 `JCYFMRP_V3_p29`/`JLXFDMJ_p27`（均 sorry），NEEDS 未列；若确需，则降级 BLOCKED（见 RANKED 车道 1）。
- **再闭 2 条 S 前置即可发车（TSV 行）**：**1 条** — `MM_4I2_IMP_4T2_4T1_p33`（本体 M），前置 `SCS_4I2_STRAIGHT_p33` + `SCS_4I2_STRAIGHT_ALL_p33`（各 S，合计 ~150 行）。
- **再闭 4 条 S/M 前置即可发车（TSV 行）**：**1 条** — `NWDGKXH_p32`（本体 S），前置梯子 `EXTREMAL_SCS_4M6_p32`（M）→ `BB_4M6_IMP_scs_4T3_p32`/`SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`（S/M）→ `MM_4M6_IMP_MM_4T3_p32`（S），合计 ~260–340 行。
- **结论**：**无重型计算可清 3 条锥内 Text 行 / 约 8 个证明项 / ~700–1000 行**。其余 15 条（含 1 条已闭对账行）需银行债、MISSING 移植或巨型几何链，**不在「最大证明子树」里**。

作为对照：TSV 全库 SORRIED 119，Text 层 19（本批）只占 16%；即便 3 条全清，K_SORRIED 上限收益 ≈ 3 行（且 `NWDGKXH_p32` 需 5 件全闭才不掉 sorryAx，搬债中态为 0 收益）。**编排者回答「最大证明子树」时不应把 Text 层当主战场。**

---

## 5. BLOCKED 根节点归并（16 条 → 3 个根 + 3 个 MISSING 簇）

1. **`general_482_deformation_p21`（`LocalAuto21.lean:1178`，L，640 HOL 行，自身 7 条前置全 sorry）**
   —— 直接/间接卡 **5 条**：`JCYFMRP_p27`、`SCS_4I1_IMP_SCS_4I2_p33`、`SCS_4I2_IMP_SCS_4T1_p33`、`TFITSKC_p27`（经 `TFITSKCv1_p27`）、`general_482` 自身。
   根下第二层：`JCYFMRP_V3_p29`（LA29:3601）、`JLXFDMJ_p27`（LA27:559）、`CUXVZOZ_p21`（LA21:1203 已证，仅转债）。
2. **LA32 4M7/4M8 箭头叶族（`SCS_4M7_SLICE_13_ARROW_3T4_p32:657` / `SCS_4M8_SLICE_13_ARROW_3T4_p32:882` / `SCS_4M8_ARROW_STEP_ONE_p32:1419` 等）**
   —— 卡 **2 条**：`YOBIMPP_p32`、`MIQMCSN_p32`。这些叶子本身又是 4-5 层箭头塔，每层都 `sorry`。
3. **`RRCWNSJ_p26`（`LocalAuto26.lean:829`）+ `SCS_6M1_IMP_SCS_6T1`（`LocalAuto20:1627`）**
   —— 卡 **1 条**：`SCS_6I1_BERAK_BY_CSTAB`（经 `SCS_6I1_IMP_SCS_6T1:1638`；再往下是 LocalAuto1 `RRCWNSJ_concl:3652`/`JCYFMRP_concl:3660`/`JLXFDMJ_concl:3699`）。
4. **MISSING 簇（不在仓内/无可导入件）**：`UAGHHBM_p30`（`isScsV39 (restrictionCs1/2V39 …)` 0 命中）、`TameLp.fully_surrounded_perimeter_bound`（`f_surr_localization_convex_local`/`lemma_face_representation`/`sum_face_rho_node1` 0 命中）、`OCBICBY_p22`（12 个 T-系统的 `empty_*` 只有 2 条在库）。
5. **独立深链**：`VPWSHTO_p15`（LA15 整章 11 sorries）、`URRPHBZ2`（PA12 `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS` giant）、`LFLACKU_p23`（`TAUM_STD_POS_p23` + `taustar_taum_dfun`）。

---

## 6. 对账与提醒

- `NUXCOEAv2_p28` 是 TSV 快照过时行（`ad7e9dba` 已闭，`#print axioms` = 标准三）。同理任务书已列的 `AURSIPD_p18`（`b89ee8b4`）、`real_model_cell23`（`bb7ce305`）也过时；TSV 的 119 是 `7c59149c` 读数。
- `SCS_4I2_IMP_SCS_4T1_p33` 的 NEEDS 注记（「consumes `ear_acute_p33`/`EDGE_EQ_2_4I2_*`」）与 HOL 证明体（`ARDBZYE.hl:1357-1439` 实引 `RRCWNSJ/JCYFMRP_V3/JLXFDMJ/XWNHLMD_MM`）不一致，标 UNRESOLVED；本表按 HOL 证据记依赖。
- `SCS_6I1_IMP_SCS_6T1` 的 NEEDS 称 `PEDSLGV2 (LocalAuto1, proof pending)`，实测 `PEDSLGV2` 在 `LocalAuto20:824` 已证——该注记也过时。
- 本车道未改任何仓内文件；`git status --porcelain` 为空（读时 `b49461bb`）。

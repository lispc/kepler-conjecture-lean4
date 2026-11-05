# WORKORDER — `la32-miqmcsn-w1` 解堵工单（LA32 / `MIQMCSN.hl` 三条 in-cone 箭头）

**基线**：`b89ee8b4`；`LocalAuto32.lean` sha256 `385fa907…81779`（1583 行，own-sorry 60）。
**本文件是"将来解堵的最小前置集"**，按"必须先闭"拓扑排序；不含任何证明，只是路线。
**证据来源**：`RECON.md` §2–§7（依赖树 / 全仓孪生搜索 / `#print axioms` 实测）。

## 0. 判据定义

- **可证（unlocked）**：目标的 `:= by` 体内**不出现任何 `sorry` 支撑的名字**，
  且 `#print axioms Kepler.Text.<目标>` = `[propext, Classical.choice, Quot.sound]`。
- **搬债**：用仍为 `sorry` 的 in-file 件（或带 `sorryAx` 的外部件）拼出目标——AGENTS §2 作废，不落库。
- **干净前置（clean）**：实测 `#print axioms` 无 `sorryAx`（见 RECON §7 表）。
- **缺口（gap）**：全仓无干净证明，必须新证。

## 1. Stage 0 — 根（不在 `LocalAuto32` 内，须先由上游/跨车道解决）

| # | 件 | 位置 | HOL 锚 | 状态 | 影响的 in-file 件 |
|---|---|---|---|---|---|
| R1 | `VASYYAU_concl` | `LocalAuto1.lean:4913`（`sorry` :4922） | appendix.hl:1489 | **根 SORRY** | `EXTREMAL_SCS_4M6_p32`、`MIN_NOT_STAND_4M7_p32`、`MIN_NOT_STAND_4M8_p32` |
| R2 | `LKGRQUI_concl` | `LocalAuto1.lean:2884`（`sorry` :2888） | LKGRQUI.hl:86-89 | **根 SORRY** | 4 条 `SCS_{4M7,4M8}_SLICE_*` + `SCS_4M8_13_SLICE_13_p32` |
| R3 | `YXIONXL2_concl` | `LocalAuto1.lean:2578`（`sorry` :2580） | YXIONXL.hl `YXIONXL2` | **根 SORRY** | 全部 opp 箭头（`STAB_4M8_02_ARROW_4M8_13`、`SCS_4M8_02_ARROW_4M8_13`、`YOBIMPP`/`MIQMCSN` 末支） |
| R4 | `YXIONXL3_concl` | `LocalAuto1.lean:2876`（`sorry` :2878） | YXIONXL.hl:2573 | **根 SORRY** | `SCS_4M7_SLICE_13_ARROW_3T4`、`SCS_4M8_13_ARROW_3T7`、prop-equ 坍缩 |
| R5 | `isScsV39 scs4T3` | `LocalAuto32.lean:247`（`sorry` :248） | hexagons SCS_TAC | **缺口**（全仓无干净孪生） | `NWDGKXH`、`SCS_3T4_prime2_ARROW_MM_3T4` |
| R6 | `isScsV39 scs3T7` | `LocalAuto32.lean:279`（`sorry` :280） | hexagons SCS_TAC | **缺口**（全仓无干净孪生） | `MIQMCSN`、`SCS_4M8_02_ARROW_3T7` |
| R7 | `isScsV39 scs3T3` | 无干净证明（LA22:2324 `is_scs_3T3_p22` 带 `sorryAx`） | hexagons SCS_TAC | **缺口** | `YOBIMPP`、`STAB_SCS_4M7_ARROW_3T3_3M1_3T4` |

**判据**：R1–R7 任一未闭，三条目标都必然带 `sorryAx`（实测：R1/R2 的 `#print axioms` 含 `sorryAx`；
R5/R6 是目标陈述 S2 合取的直接义务；R7 是 `YOBIMPP` 的 S2 义务）。

> 关键事实：除 R1–R7 之外，链上所有节点实测**公理干净**（RECON §7）。所以"闭完仍带 sorryAx"
> 不是必然——只要这 7 个根真证，三条目标即可达 `[propext, Classical.choice, Quot.sound]`。

## 2. Stage 1 — 干净但不在 import 闭包的前置（移植，零新 import 路线）

`LocalAuto32` 的 import 闭包是 `{LA1, LA17, LA20, LA23, LA29, Mathlib}`（+ LA29 传递的 LA24/26/28/PA18）。
下列件已证且 clean，但不在该闭包内，需**逐字移植**（`private` + `w32_` 前缀，避免与已落库件重名），
或经审批后走 import 路线（简报 §0 要求 BFS 无环 + 全文件漂移核，代价另计）。

| # | 件（源） | 源位置 | 移植闭包规模（实测） | 用途 |
|---|---|---|---|---|
| P1 | `SET_STAB_4M6_ARROW_4T5_p33` | LA33:4298 | **46 decls / ~771 行**（含 `SET_EQ_DIAG_STAB_4M6`、`FZIOTEF_BOTH`、`STAB_4M6_{02,13}_ARROW_4T5`、`SCS_4T5_IS_SCS`） | `NWDGKXH` 右支 |
| P2 | `SCS_4T5_IS_SCS_p33` | LA33:1492 | 4 decls / ~49 行 | `NWDGKXH` S2 义务 |
| P3 | `SCS_3T3_IS_SCS_p33` | LA33:1617 | 4 decls / ~48 行 | `YOBIMPP` S2 义务（替代 R7） |
| P4 | `STAB_4M7_SCS_p33` | LA33:3077 | 12 decls / ~126 行 | `SCS_4M7_SLICE_13/02` |
| P5 | `SCS_DIAG_SCS_4M7_13_p33` | LA33:3143 | 1 decl / 2 行 | `SCS_4M7_SLICE_13` |
| P6 | `SCS_DIAG_SCS_4M7_02_p33` | LA33:3139 | 1 decl / 2 行 | `SCS_4M7_SLICE_02` |
| P7 | `STAB_4M8_SCS_p33` | LA33:3084 | 12 decls / ~129 行 | `SCS_4M8_SLICE_13` |
| P8 | `OPP_IS_SCS_p33` | LA33 | 7 decls / ~113 行 | opp 箭头 S2 义务 |
| P9 | `YXIONXL2_p33` | LA33:481 | 9 decls / ~307 行 | opp 箭头主体 |
| P10 | `PRO_EQU_ID1`（LA12:1010） | LA12 | 15 decls / ~197 行 | prop-equ 坍缩 |
| P11 | `YXIONXL3`（LA12:1224） | LA12 | 39 decls / ~835 行（含 P10） | prop-equ 箭头 |
| P12 | `SCS_OPP_REFL_fb` | FanBaseKit:3135 | 待核（FanBaseKit 未 import） | `YOBIMPP` 末支 |

**替代路线（成本更低，需审批）**：新增 `import Kepler.Text.LocalAuto33`（它 import 了
`LocalAuto1/12/17/18/20/22/26/27/29` + `FanBaseKit` + `SphereKit`，**不 import `LocalAuto32`**，
方向无环）。这样 P1–P9 直接可用；P10/P11 也随 LA33 的 import 闭包到位。
代价：须补齐简报 §0 的「BFS 无环证明 + 全文件漂移核（import 前后 warning 谱面逐条一致 +
≥10 件既有件 `#print axioms` 零漂移）+ grep 新进闭包模块公开名与下游重名」。
**2026-11-05 编排者裁定：本波不批准新增 import**，故默认走逐字移植。

## 3. Stage 2 — `LocalAuto32` in-file 中间件（拓扑序）

标注：`HOL` = `MIQMCSN.hl` 行段；`Lean` = 预估新增/替换行数（按同文件已证件经验，HOL 行数 × 2–3，仅估算）；
`孪生` = 全仓是否有已证孪生（`grep -rn` 实测）。

### 3.1 目标 1 链（`NWDGKXH_p32`，最便宜）

| 序 | 件 | LA32 行 | HOL 行段 | Lean 估 | 孪生 | 前置 |
|---|---|---|---|---|---|---|
| 1 | `SCS_4T3_IS_SCS_p32` | 247（sorry 248） | hexagons SCS_TAC | 30–60 | 无（R5） | 无 |
| 2 | `EXTREMAL_SCS_4M6_p32` | 993（sorry 998） | 1855-1991（137） | 250–350 | 无 | **R1**、`MMS_IMP_BBS_p28`、`BB_VV_FUN_EQ_p26`、`SCS_4M6_STAND_OR_PRO_p32` |
| 3 | `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32` | 1020（sorry 1025） | 2048-2109（62） | 120–180 | 无 | 1、2、`STAB_MOD`、`YRTAFYH_concl`、P2 |
| 4 | `SET_STAB_4M6_ARROW_4T5`（新 `w32_*`） | — | :2894 起 | 见 P1 | LA33 `_p33` clean | P1 |
| 5 | **`NWDGKXH_p32`** | 1030（sorry 1032） | 2110-2129（20） | 20–35 | — | 3、4、1 |

**解锁判据（T1）**：`NWDGKXH_p32` 变为可证 ⟺
`SCS_4T3_IS_SCS_p32` ∧ `EXTREMAL_SCS_4M6_p32` ∧ `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32` 三件全闭
∧ `isScsV39 scs4T5` 干净可用 ∧ `SET_STAB_4M6_ARROW_4T5` 可用。
**唯一硬闸是 `EXTREMAL_SCS_4M6_p32 → VASYYAU_concl`（R1）**——R1 不闭，T1 永远 BLOCKED。

### 3.2 目标 2 链（`YOBIMPP_p32`）

| 序 | 件 | LA32 行 | HOL 行段 | Lean 估 | 孪生 | 前置 |
|---|---|---|---|---|---|---|
| 1 | `SCS_4T3_IS_SCS_p32` | 247 | — | 30–60 | 无 | 无 |
| 2 | `SCS_3T4_prime2_IS_SCS_p32` | 264 | SCS_TAC | 20–40 | 无 | 无 |
| 3 | `SCS_3T3_prime_IS_SCS_p32` | 269 | SCS_TAC | 20–40 | 无 | 无 |
| 4 | `SCS_3M1_prime_IS_SCS_p32` | 274 | SCS_TAC | 20–40 | 无 | 无 |
| 5 | `SCS_3T4_prime2_ARROW_MM_3T4_p32` | 388（sorry 390） | 943-972（30） | 50–80 | 无 | 1、2、`XWNHLMD_MM_p26` |
| 6 | `SCS_3T3_prime_ARROW_MM_3T3_p32` | 408（sorry 410） | — | 50–80 | 无 | 3 |
| 7 | `SCS_3M1_prime_ARROW_MM_3M1_p32` | 428（sorry 430） | — | 50–80 | 无 | 4 |
| 8 | `SCS_4M7_SLICE_13_p32` | 649（sorry 652） | 1182-1307（126） | 200–300 | 无 | **R2**、P4、P5 |
| 9 | `SCS_4M7_SLICE_02_p32` | 665（sorry 668） | 1326-1453（128） | 200–300 | 无 | **R2**、P4、P6 |
| 10 | `SCS_4M7_SLICE_13_ARROW_3T4_p32` | 657（sorry 659） | 1308-1325（18） | 25–40 | 无 | 5、8、P10/P11 |
| 11 | `SCS_4M7_SLICE_02_ARROW_3T3_3M1_p32` | 673（sorry 675） | 1454-1483（30） | 40–60 | 无 | 6、7、9、P10 |
| 12 | `STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32` | 680（sorry 683） | 1484-1496（13） | 20–35 | 无 | 10、11、`SET_EQ_DIAG_STAB_4M7_p32`、`FZIOTEF_UNION` |
| 13 | `MIN_NOT_STAND_4M7_p32` | 1118（sorry 1122） | — | 100–160 | 无 | **R1**、`SCS_4M7_STAND_OR_PRO_p32` |
| 14 | `BB_4M7_IMP_4M6_12_p32` | 1127（sorry 1131） | — | 60–100 | 无 | 13 |
| 15 | `MM_4M7_IMP_MM_4M6_12_p32` | 1135（sorry 1139） | — | 30–50 | 无 | 14 |
| 16 | `BB_4M7_IMP_4M6_01_p32` | 1143（sorry 1148） | — | 60–100 | 无 | 13 |
| 17 | `MM_4M7_IMP_MM_4M6_01_p32` | 1153（sorry 1158） | — | 30–50 | 无 | 16 |
| 18 | `MM_4M7_IMP_STAB_4M7_p32` | 510（sorry 514） | — | 40–70 | 无 | `STAB_MOD` |
| 19 | `SCS_4M7_ARROW_STAB_4M7_4M6_p32` | 1162（sorry 1167） | 2361-2442（82） | 120–180 | 无 | 13–18、`YRTAFYH_concl` |
| 20 | **`YOBIMPP_p32`** | 1241（sorry 1244） | 2453-2490（38） | 30–50 | — | 12、19、P8–P12、R3/R4、R7（或 P3） |

**解锁判据（T2）**：`YOBIMPP_p32` 变为可证 ⟺ 上表 1–19 全闭 ∧ opp 套件
（`YXIONXL2`、`YXIONXL3`、`PRO_EQU_ID1`、`SCS_OPP_REFL`、`OPP_IS_SCS`）可用 ∧
`isScsV39 scs3T3` 干净（R7 或 P3）。
**硬闸**：R1（经 13）、R2（经 8/9）、R3/R4（末支）、R7。

### 3.3 目标 3 链（`MIQMCSN_p32`）

| 序 | 件 | LA32 行 | HOL 行段 | Lean 估 | 孪生 | 前置 |
|---|---|---|---|---|---|---|
| 1 | `SCS_3T4_prime2_IS_SCS_p32` | 264 | — | 20–40 | 无 | 无 |
| 2 | `SCS_4M8_02_IS_SCS_p32` | 254 | — | 20–40 | 无 | 无 |
| 3 | `SCS_4M8_13_IS_SCS_p32` | 259 | — | 20–40 | 无 | 无 |
| 4 | `SCS_3T7_IS_SCS_p32` | 279 | — | 20–40 | 无（R6） | 无 |
| 5 | `SCS_3T4_prime2_ARROW_MM_3T4_p32` | 388 | 943-972（30） | 50–80 | 无 | 1、`SCS_4T3_IS_SCS` |
| 6 | `STAB_4M8_13_SCS_p32` | 1451（sorry 1454） | 3042-3053（12） | 20–35 | 无 | `YRTAFYH_concl`（已证） |
| 7 | `SCS_4M8_13_SLICE_13_p32` | 1487（sorry 1489） | 3207-3335（129） | 200–300 | 无 | **R2**、6、`SCS_DIAG_SCS_4M8_13_13_p32` |
| 8 | `SCS_4M8_13_ARROW_3T7_p32` | 1494（sorry 1496） | 3336-3345（10） | 20–30 | 无 | 7、P10/P11 |
| 9 | `SCS_4M8_SLICE_13_p32` | 875（sorry 877） | 1655-1783（129） | 200–300 | 无 | **R2**、P7 |
| 10 | `SCS_4M8_SLICE_13_ARROW_3T4_p32` | 882（sorry 884） | 1784-1791（8） | 15–25 | 无 | 5、9 |
| 11 | `STAB_4M8_02_ARROW_4M8_13_p32` | 868（sorry 870） | 1637-1654（18） | 25–40 | 无 | `PROP_OPP_DIAG_4M8_13_p32`、P8/P9 |
| 12 | `SCS_4M8_SLICE_02_ARROW_3T4_p32` | 889（sorry 891） | 1792-1798（7） | 15–25 | 无 | 10、11 |
| 13 | `SET_STAB_4M8_ARROW_3T4_p32` | 896（sorry 899） | 1799-1811（13） | 20–35 | 无 | 10、12、`SET_EQ_DIAG_STAB_4M8_p32`、`FZIOTEF_UNION` |
| 14 | `SCS_4M8_02_ARROW_4M8_13_p32` | 1562（sorry 1564） | 3410-3427（18） | 25–40 | 无 | `PROP_OPP_4M8_13_p32`、P8/P9、2、3 |
| 15 | `SCS_4M8_02_ARROW_3T7_p32` | 1569（sorry 1571） | 3428-3435（8） | 15–25 | 无 | 8、14、4 |
| 16 | `MIN_NOT_STAND_4M8_p32` | 1366（sorry 1372） | — | 100–160 | 无 | **R1**、`SCS_4M8_STAND_OR_PRO_p32`、`SCS_4M8_STAND_p32` |
| 17 | `BB_4M8_IMP_4M6_23_p32` | 1252（sorry 1256） | — | 60–100 | 无 | 16 |
| 18 | `MM_4M8_IMP_MM_4M6_23_p32` | 1261（sorry 1265） | — | 30–50 | 无 | 17 |
| 19 | `BB_4M8_IMP_4M6_01_p32` | 1269（sorry 1273） | — | 60–100 | 无 | 16 |
| 20 | `MM_4M8_IMP_MM_4M6_01_p32` | 1278（sorry 1282） | — | 30–50 | 无 | 19 |
| 21 | `BB_4M8_IMP_scs_4M8_02_p32` | 1377（sorry 1383） | — | 60–100 | 无 | 16 |
| 22 | `MM_4M8_IMP_MM_4M8_02_p32` | 1388（sorry 1394） | — | 30–50 | 无 | 21 |
| 23 | `BB_4M8_IMP_scs_4M8_13_p32` | 1398（sorry 1404） | — | 60–100 | 无 | 16 |
| 24 | `MM_4M8_IMP_MM_4M8_13_p32` | 1409（sorry 1415） | — | 30–50 | 无 | 23 |
| 25 | `MM_4M8_IMP_STAB_4M8_p32` | 697（sorry 701） | — | 40–70 | 无 | `STAB_MOD` |
| 26 | `SCS_4M8_ARROW_STEP_ONE_p32` | 1419（sorry 1424） | 2874-3015（142） | 250–350 | 无 | 16–25、`YRTAFYH_concl` |
| 27 | **`MIQMCSN_p32`** | 1576（sorry 1579） | 3436-3470（35） | 30–50 | — | 13、15、26、P8–P11、R3/R4 |

**解锁判据（T3）**：`MIQMCSN_p32` 变为可证 ⟺ 上表 1–26 全闭 ∧ opp 套件可用 ∧
`isScsV39 scs3T7` 干净（R6）。
**硬闸**：R1（经 16）、R2（经 7/9）、R3/R4（14/11 与末支）、R6。

## 4. 三目标解锁判据汇总

| 目标 | in-file 必闭件数 | 硬闸（根） | 干净前置（需移植） | 备注 |
|---|---|---|---|---|
| `NWDGKXH_p32` | **3** | R1、R5 | P1、P2 | 最便宜；R1 是唯一实质闸 |
| `YOBIMPP_p32` | **19** | R1、R2、R3、R4、R7（或 P3） | P4–P6、P8–P12 | 与 T3 共享 opp 套件与 P5/P6 |
| `MIQMCSN_p32` | **26** | R1、R2、R3、R4、R6 | P7–P11 | 与 T2 共享 `SCS_3T4_prime2_ARROW_MM_3T4`、opp 套件 |

（in-file 件数含 S2 合取的 `isScs` 义务；不含 R1–R7 与 P1–P12。）

## 5. 建议排序（若下一波获准解堵）

1. **先解 R1（`VASYYAU_concl`）**：它同时是 T1/T2/T3 的硬闸，且是唯一"纯上游"的根。
   R1 不闭，任何 in-file 工作都无法让目标脱离 `sorryAx`。
2. 并行解 R2（`LKGRQUI_concl`）——T2/T3 的另外 5 条 SLICE 全依赖它。
3. R5/R6（`isScsV39 scs4T3` / `scs3T7`）：纯机械 21 合取验证，可独立完成，
   建议直接参照 `LocalAuto20:214 SCS_3M1_IS_SCS` / `LocalAuto29:1103 SCS_4M6_IS_SCS_p29` 的骨架。
4. R3/R4（`YXIONXL2_concl`/`YXIONXL3_concl`）：可用 P9/P11 的 LA33/LA12 证体**逐字真证**替代
   （它们 clean，实测），无需再等 LA1。
5. 然后按 §3.1 → §3.2/§3.3（T2/T3 共享 P5/P6 与 opp 套件，可同波并行）。
6. 最后三条目标装配（各 20–50 行）。

**一句话结论**：`NWDGKXH_p32` 的解锁判据只有 3 件 in-file + R1/R5；`YOBIMPP`/`MIQMCSN`
分别 19/26 件，且共享同一 opp 套件——建议把 T1 单独作为下一波（最小可验证收益），
T2/T3 合并为一波（共享前置多）。

## 6. 验证闸（每波收尾）

1. 整文件 `lean` RC=0、`grep -c ': error:'` = 0。
2. `grep -c 'declaration uses \`sorry\`'` 单调下降（本波 60）。
3. 每个闭合件 `#print axioms Kepler.Text.<name>` = `[propext, Classical.choice, Quot.sound]`。
4. 陈述冻结：目标签名逐字不变（本工单不改任何陈述）。
5. 零新 import（或附简报 §0 的 BFS + 漂移核）。
6. `open Classical` 零新增；新件零 `sorry`/`admit`/`native_decide`。
7. 搬债审计：体内新引用的每个 sorried 件逐个 `grep <name> docs/e2e-reachability-map.tsv`
   （0 行 = 不在锥，须在 DELIVERY 记录）。

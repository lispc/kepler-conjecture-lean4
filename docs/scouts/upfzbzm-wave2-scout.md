# upfzbzm-wave2-scout — Pack2.hl 测度桥四件套体量评估（零改动，只读侦察）

> 2026-09-29 波 2 前置侦察 lane 交付，编排者落库。对照 `lean/scripts/packing/pack2.hl`
> （与 `reference/flyspeck/text_formalization/packing/` 逐字节同）。纪律：零 repo 改动、
> 零 git、未跑 auto_gate；轻量验证 = `/tmp/upfzbzm_w2_check.lean`（import 既有 olean，
> 单 lake 进程，全绿可复跑）。

**核心结论先行**：测度桥四件套的"最大未知"实测**降维为"一件免费 + 三件需自组且均已
有编译验证的 Mathlib 路线"**——
①`MEASURABLE_VORONOI_CLOSED` 全树已免费（PA5 closed-cell kit 全套 proved，含 TIWWFYQ）；
②③④开/闭体积相等、闭胞交零测、a.e.-不相交有限并，三件在 Mathlib v4.32.2 各有精确
对位（`Convex.addHaar_frontier`、`Measure.addHaar_affineSubspace`、
`measure_biUnion_null_iff` + `measure_union_add_inter`），本 lane 已在 /tmp 把**超平面
零测原型（55 行）与 a.e.-disjoint 有限并原型（50 行）完整编译通过**。桥合计
**~240-350 行 Lean**。
但侦察发现**两个被波计划漏记的隐藏输入**：KIZHLTL1 还需 **AJRIPQN**（KIZHLTL.hl:92，
PA17 sorried GIANT）；KIZHLTL4 还需 **GRUTOTI**（KIZHLTL.hl:907，**HL 8005 行**的巨物）。
据此，原方案"一个 lane 连做 PA15+PA16 ~450-700 行"**实测应修正为 ~1030-1650 行，
建议拆分**。

---

## 0. 接口定位

- PA16 sorried 骨架：`KIZHLTL1 :250-255`、`KIZHLTL2 :268-273`、`KIZHLTL4 :310-323`
  （文件 323 行）。
- PA15 sorried 骨架：`FINITE_MCELL_SET_LEMMA :229`、`FINITE_MCELL_SET_lemma1 :216-219`、
  `HD_IN_MCELL :213`、`MCELL_SUBSET_BALL_4 :254`、`PACKING_BALL_BOUNDARY :250`、
  `DIHX_SYM :831-833`、`FINITE_EDGE_X2 :382`、`SUM_PAIR_2_SET :852`（文件 1026 行）。
- 消费点（波 1 落账 `abfd2fcb`）：PA19.NEGLIGIBLE_FUNC（:754-929，已真证）以
  `KIZHLTL1 V :763 / KIZHLTL2 V :764 / KIZHLTL4 V :765 / FINITE_MCELL_SET_LEMMA V r hp hs
  :771-772` 四个 obtain 消费。副产品接线：`PackingConcl.lean:456-462`
  （`KIZHLTL1_concl_discharged := KIZHLTL1`，voronoiOpenP16 delta 桥）与 `:470-477`
  （`KIZHLTL2_concl_discharged := KIZHLTL2`，shape-verbatim）——**一行式已存在，PA16
  真化瞬间自动变真，零额外接线（确认）**。

## 1. 测度桥四件套全图（pack2.hl）

| 件 | 行号 | HL 规模 | 依赖（向上一层） | Lean 侧现状 |
|---|---|---|---|---|
| `MEASURABLE_VORONOI_CLOSED` | :272-274 | 3 行 | `MEASURABLE_COMPACT` + `COMPACT_VORONOI_CLOSED`(:100-103) | **免费**：PA5:749 `CLOSED_VORONOI_CLOSED`（proved）`.measurableSet`；PA5:765-767 `DRUQUFE` 三连全 proved；PA1:1250 同款亦 proved |
| `MEASURE_VORONOI_CLOSED_OPEN` | :325-335 | 11 行 | `CLOSURE_VORONOI_OPEN`(:289-301) + `MEASURE_NEGLIGIBLE_SYMDIFF` + `NEGLIGIBLE_CONVEX_FRONTIER` | 需自组（§2 件1） |
| `NEGLIGIBLE_INTER_VORONOI_CLOSED` | :354-362 | 9 行 | `INTER_VORONOI_SUBSET_BISECTOR`(:337-352) + `NEGLIGIBLE_HYPERPLANE` | 需自组（§2 件3；PA1:1302-1316 有同款 sorried 陈述可抄） |
| `MEASURE_NEGLIGIBLE_UNIONS_IMAGE` | （HOL measure.ml 库件） | — | FINITE 源集（KIUMVTC）+ 逐像可测 + 两两交零测 | 需自组（§2 件4） |

**KIZHLTL1 的五步消费图**（KIZHLTL.hl:46-279）：
- **Step A** :58-69 sum vol = vol(UNIONS)：`MEASURE_NEGLIGIBLE_UNIONS`——FINITE
  （`FINITE_MCELL_SET_LEMMA`:63）+ 逐件可测（`MEASURABLE_MCELL`:68，PA10:517 已真证）+
  两两交零测（:72-121，正体积 ⇒ s=t，即 **`Ajripqn.AJRIPQN`:92**——PA16 header 漏记）。
- **Step C1** :168-175：**件1**。
- **Step C2** :179-191：**件4+件2+件3** 一次性消费（FINITE 由
  `Statement.Packing.finite_inter_ball` 已真证）。
- **Step C3** :193-238：`TIWWFYQ`:214（**PA5:614 已真证**）+ 三角不等式算术——纯机械。
- **Step C4** :196-205：FINITE_IMAGE_EXPAND + **件2**。
- **Step B/D/E/F**：VOLUME_BALL + witness `c = -(24/3)π` 实数算术 + 退化分支——全机械
  （JGXZ `jg_volume_ball`:139 范本）。

## 2. Mathlib v4.32.2 对位盘点

**件2 `MEASURABLE_VORONOI_CLOSED` — 直译，≈0**。`PA5.CLOSED_VORONOI_CLOSED …
|>.measurableSet`（或整件取 PA5.DRUQUFE:765）。PA16 加 `import Kepler.Text.PackingAuto5`
无环。

**件1 `MEASURE_VORONOI_CLOSED_OPEN` — 需自组，~80-130 行**。Mathlib 精确对位（实测类型
检查通过）：`Convex.addHaar_frontier (μ:=volume)`（Analysis/Convex/Measure.lean:35）+
`measure_symmDiff_eq_zero_iff`（OuterMeasure/AE.lean:180）+ `measure_congr`（同:270）。
路线比 HL 短：**不需要 `CLOSURE_VORONOI_OPEN`**——`closed \ open ⊆ frontier(open)`
只需 open⊆closed（PA1:1260 范本）+ closure(open)⊆closed（PA5:749）+ open 开 ⇒
open = interior(open)。缺的只有 **IsOpen (voronoiOpen) ~50 行**（JGXZ
`jg_open_voronoi`:280-343 完整 proved 范本，`jg_*` private 不可 import，需 `_p16`
重写）+ 凸性 ~10 行 + toReal 有限性桥（closed ⊆ ball v 2，PA5.VORONOI_BALL2:691 范本）。
**JGXZ 的 `jg_measure_unions_sum_voronoi` 只覆盖 open-cell 真不相交情形**，对 closed-cell
a.e.-不相交**不能直接借**；`jg_biUnion_toFinset_eq`/`jg_volume_ball` 系列可作技术范本。

**件3 `NEGLIGIBLE_INTER_VORONOI_CLOSED` — 需自组，~60-90 行**。(a)
`INTER_VORONOI_SUBSET_BISECTOR`：消两层 `≤` 得等式超平面，~20 行（PA1:1298-1306 可抄）；
(b) `hyperplane_null`：**/tmp 实测 55 行完整编译通过**——`AffineSubspace.mk' p
((span ℝ {a})ᗮ)`（p = (b/⟪a,a⟫)•a）接 `Measure.addHaar_affineSubspace`
（EqHaar.lean:199）。PA1:1308-1311 已备陈述位。

**件4 `MEASURE_NEGLIGIBLE_UNIONS_IMAGE` — 需自组，~45-70 行（一次覆盖两个用法）**。
Mathlib 无 a.e.-不相交有限并等式。**/tmp 实测 50 行完整编译通过**：`Finset.induction_on`
+ `measure_union_add_inter`（MeasureSpace.lean:135）+ `measure_biUnion_null_iff`。
同一引理实例化两次：Step C2 的 IMAGE 形与 Step A 的细胞族形。

**桥合计：~240-350 行**。无结构性缺口。

## 3. KIZHLTL1 全链定级（HL :46-279，234 行）

| 块 | Lean 估 |
|---|---|
| 测度桥四件 + open-cell 开性/凸性 kit | **240-350** |
| Step A（AJRIPQN 消费 + a.e.-disjoint 实例化） | 40-70 |
| Step C2-C4（件4 实例化 + covering + TIWWFYQ） | 60-100 |
| Step B/D/E/F（VOLUME_BALL 算术 + 组合 + 退化支） | 60-100 |
| **合计** | **~400-620** |

除桥外硬点：①AJRIPQN（§5 风险①）；②IsOpen(voronoiOpen) 重建（JGXZ 范本 ~50 行）；
③KIZHLTL1 不消费 mm1/mm2 常数（witness 是 `-(24/3)π`）——无常数风险。

## 4. KIZHLTL2 / FINITE_MCELL_SET_LEMMA 定级

**FINITE_MCELL_SET_LEMMA 包——原估 "~100-150" 偏低，实测 ~330-600**。三件：
- Lemma 5 本体（HL marchal3:329-441）：空胞删除 + mcell_set 枚举为 `(i∈0..4)×(4 点表⊆
  V∩ball(0,r+6))` 的像 + FINITE_PRODUCT——Lean 100-180。
- `FINITE_MCELL_SET_lemma1`（PA15:216；HL :231-327）：i=0 用 `ROGERS_SUBSET_VORONOI_
  CLOSED`（PA15:178 已真证）+ `barV3ImpFinite2`（PA16:161 私有范本自拷 ~50 行）；i≠0
  需 **HD_IN_MCELL**。Lean 60-120。
- **`HD_IN_MCELL`**（PA15:213；HL marchal3:101-约230，case-bash i=1/2/3/4）：i=1 用
  `HD_IN_ROGERS`（PA15:172 已真证）；i=2 球/锥算术；i=3/4 aff_ge 凸包。Lean 120-250
  ——该包真正硬核。

**KIZHLTL2（PA16:268-273；HL :285-527）——~300-450 行**。输入盘点：`QZYZMJC`（sorried
合法流动）、`HDTFNFZ`（PA10 已真证）、`finite_inter_ball`（已真证）、
`FINITE_MCELL_SET_LEMMA`、`PACKING_BALL_BOUNDARY`（HL :737-829，真化再 +150-250 或先
sorried 流动）、`MCELL_SUBSET_BALL_4`（真化再 +100-200）、`URRPHBZ2`（PA13 sorried
流动）、setSum 版 `SUM_SUM_RESTRICT`（PA19 kit 范本 ~30-50）、**`#1.012080 < mm1`**
（全树无 Lean 证；PA19:151-339 π-Taylor 机器是范本，不可反向 import，lane 内重证
~60-120）。

## 5. 波 2 切法裁定

**建议拆分，不连做。** 全量连做 ≈ **1030-1650 行**（原估 450-700 漏计 HD_IN_MCELL、
MCELL_SUBSET_BALL_4/PACKING_BALL_BOUNDARY、mm1 常数、KIZHLTL2 本体）。

- **推荐三切**（PA16→PA15/17/5 import 均无环，已核对）：
  1. **Lane 2A（PA15 包）**：`HD_IN_MCELL` + `lemma1` + `FINITE_MCELL_SET_LEMMA`
     （+可选 `MCELL_SUBSET_BALL_4`/`PACKING_BALL_BOUNDARY`），~350-600。
  2. **Lane 2B（PA16，KIZHLTL1）**：测度桥四件 + IsOpen kit + KIZHLTL1 本体，~400-620；
     消费 2A/QZYZMJC/AJRIPQN 的 sorried 合法流动。**副产品确认**：真化瞬间
     PackingConcl:456 `KIZHLTL1_concl_discharged` 自动变真。
  3. **Lane 2C（PA16，KIZHLTL2）**：~300-450（含 mm1 常数；PACKING_BALL_BOUNDARY/
     MCELL_SUBSET_BALL_4 真化可并入 2A）。副产品 PackingConcl:470 同上。
- 若只开两个：**Lane A = PA15 包；Lane B = PA16 连做 KIZHLTL1+2**（桥一次建成两件
  共享），B 约 700-1070，重 lane 但结构风险低。

**风险与勘误**：①**AJRIPQN 是 KIZHLTL1 隐藏第五输入**（KIZHLTL.hl:92；PA16 header
:74-81 NEEDS 表漏记）——以 PA17:310 sorried 合法流动（PA16 加 import 无环），但其
真化（5-stage covering，架构文档化于 PA17:260-318）是 UPFZBZM 全链公理干净的新增
前置，应进波 3 排期。②PA17 docstring 称 TIWWFYQ（PA5）sorry **已过时**——PA5:614
现为完整实证明（连带 PA16 header :80 的 NEEDS TIWWFYQ 已满足）。③JGXZ 可借件全部
private，只能作范本重写不能 import。④PA1 的 pack2 链（MEASURE_VORONOI_CLOSED_OPEN
:1293、NEGLIGIBLE_INTER_VORONOI_CLOSED:1313、hyperplane_null:1308 陈述 +
MEASURABLE_VORONOI_CLOSED:1250 proved）是现成抄写模板，但 PA1 olean 未建不可 import，
命名 `Space3`/`voronoi` 可平移。

## 6. 波 3 预告（快速复核）

- **KIZHLTL4**（PA16:310-323；HL :548-1032 ~500 行）：可复用 = `gamma_y_pos_le`
  （PA15:865）、`H0_LT_SQRT2`（PA15:859）、`FINITE_LIST_KY_LEMMA_2`（PA15:675）、
  `HDTFNFZ`、`HL_2`（PA15:257）。缺件：`DIHX_SYM`（PA15:831 ★）、`FINITE_EDGE_X2`
  （:382 ★）、`SUM_PAIR_2_SET`（:852 ★）、`SUM_SUM_PRODUCT`（无范本 ~40）、
  `ZERO_LE_MM2_LEMMA`（PA19 proved 不可反向，重证 ~30-60）、
  **`GRUTOTI`（KIZHLTL.hl:907 唯一直接消费；GRUTOTI.hl 共 8005 行——波 3 必须作为
  独立 GIANT 排期，否则 KIZHLTL4 永远带该 taint）**。自身折算（不含 GRUTOTI）：
  ~500-900。
- **SUM_GAMMAX_LMFUN_ESTIMATE**（PA18:2538 ★；HL ~1400 行）：PA18 骨架实测 **78 处
  sorry**。已证覆盖：复数角/单位圆 kit。仍 sorried 支柱：`arc_derivative` 系/
  `YSSKQOY`（:654-687）、coplanar 系（:700-829）、`cc_pe_exists` 系（:136-154）、
  `BOUND_GAMMA_X_lmfun`（PA15:1022）、`CARD_MCELL_CONTAINS_POINT_klemma`（PA15:945）。
  维持 GIANT×最重；波 3 须先清 PA18 内部支柱再上 capstone。

**一句话结论**：波 2 的真正形状 = "一件免费 + 三件有已验证 Mathlib 路线的自组桥
（~240-350 行）+ 两个漏记的 sorried 流动输入（AJRIPQN、波 3 的 GRUTOTI）+ PA15 包
比原估大 2-4 倍（HD_IN_MCELL 是硬核）"。建议三切（或两切），KIZHLTL1/2 真化后
`PackingConcl:456/:470` 两个 discharge 零成本自动变真。

**验证脚本**（可复跑）：`/tmp/upfzbzm_w2_check.lean`——5 个 Mathlib 关键引理类型
检查 + 两个完整原型，`lake env lean` 编译零错误。

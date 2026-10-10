# upfzbzm-scout — UPFZBZM 链侦察结案报告（零填证，只读交付）

> 2026-09-29 侦察 lane 交付，编排者落库。对照基准
> `reference/flyspeck/text_formalization/packing/`（HOL Light Flyspeck；`lean/scripts/packing/`
> 与之 `diff -q` 逐字节相同）。纪律：零 repo 改动、零 git 操作、未跑 auto_gate；验证仅
> /tmp scratch × 2（`lake env lean`，单进程，import 既有 olean）。

**核心结论先行**：`UPFZBZM_concl` 的债务不是"缺装配"，而是**装配已 100% 完成且只剩一个洞**。
PA19 的 capstone `UPFZBZM`（本体无 sorry 字面）+ FCC 半边（**已真证、#print axioms 干净**）+
装配章 `PackingConcl.UPFZBZM_concl_discharged`（已接线，一行式）全部在树。全链唯一缺口 =
`PA19.NEGLIGIBLE_FUNC`（PackingAuto19.lean:631 一个 bare sorry）；其四个输入全部在树上
（PA16 KIZHLTL1/2/4、PA18 SUM_GAMMAX、PA15 FINITE_MCELL_SET_LEMMA，全 sorry）+ 第五个输入
`Statement.Packing.finite_inter_ball` **已真证干净**。上轮 lane 报告"真实内容 = PA19 侧
NEGLIGIBLE_FUNC GIANT，架构已有"**属实且偏保守**——NEGLIGIBLE_FUNC 本体（给定输入）只是
中等规模的 setSum 重排（HL 108 行 tactic），真正 GIANT 在上游四件。

---

## 0. 接口与消费点定位

- **PA2 接口**：`Kepler/Text/PackingAuto2.lean:959-962`
  ```lean
  theorem UPFZBZM_concl : ∀ V : Set V3, saturated V → Packing V →
      cellClusterInequality V → TSKAJXY_statement → lmfunInequality V →
      ∃ G : V3 → ℝ, negligibleFun0 G V ∧ fccCompatible G V := by
    sorry
  ```
- **HOL 原形**：`UPFZBZM.hl:52-56`（`UPFZBZM_concl`，五前提合取 →
  `?G. negligible_fun_0 G V /\ fcc_compatible G V`）；capstone `UPFZBZM` :227-235。
- **消费点**：PA2.RDWKARC_concl（:1124，**已真证装配**，见 §2.3）；装配章
  `PackingConcl.UPFZBZM_concl_discharged`（`Kepler/Text/PackingConcl.lean:510-514`，
  `fun V hs hp hcc hT hlm => UPFZBZM V hs hp hcc hT hlm`）。PA19 的唯一下游消费者就是
  PackingConcl（全树 grep 实测）。

## 1. HOL 侧链全图（逐件行号 + 定级）

### 1.1 UPFZBZM.hl（238 行）

| 件 | 行号 | 内容 | 定级 |
|---|---|---|---|
| `UPFZBZM_concl` | :52-56 | 结论陈述 | — |
| `FCC_COMPATABILITY_FUNC_concl` | :58-64 | part 1 陈述（G 显式给） | — |
| `NEGLIGIBLE_FUNC_concl` | :66-79 | part 2 陈述（同 G） | — |
| `FCC_COMPATABILITY_FUNC` | :87-105（~19 行 tactic） | `sqrt32 = 8(mm1−12mm2) ≤ 8mm1 − 8mm2·S ≤ 8mm1 − y`；用 `MEASURE_VORONOI_CLOSED_OPEN`、`SQRT_OF_32_lemma`、`m1_minus_12m2`、`ZERO_LE_MM2_LEMMA` | **机械**（纯实数算术，无浮点硬点） |
| `NEGLIGIBLE_FUNC` | :113-220（~108 行 tactic） | 拆 `sum(V∩ball) G = Σf1 + Σf3 − Σf4`；B = `{X \| X ⊆ ball(0,r) ∧ mcell_set V X}` 上 T1/T2/T3 重聚 = `ΣB (gammaX V X lmfun)`；witness `C = −c''' − c − c' − c''`（:138） | **中等**（给定输入；setSum 代数+重排） |
| `UPFZBZM`（capstone） | :227-235（9 行） | `EXISTS_TAC G` + `ASM_MESON_TAC[NEGLIGIBLE_FUNC; FCC_COMPATABILITY_FUNC]` | **机械** |

**硬点归类**：NEGLIGIBLE_FUNC 本体无测度论、无极限、无浮点——全部难度在其四个输入；
`gammaX` 的 `\{u,v}. if {u,v} IN edgeX V X then ... else &0` guard（:169-172）与 Lean
`gammaX` 的 epsilon 编码（PA2:448-455）已同形对齐。

### 1.2 UPFZBZM_support_lemmas.hl（374 行）——Lean 侧已全部落地

`pos_lemma` :345-364、`negligible_fun_any_C` :366-369（= `negligible_fun_0` 定义 +
`pos_lemma` 剥 `0≤C`）；数值界 `tau0_not_zero` :91-96（`#1.54065`）、`ZERO_LT_MM2_LEMMA`
:100-103（`#0.02541`）；sqrt 演算 `SQRT_RULE_Euler_lemma` :127-132、`SQRT_OF_32_lemma`
:134-141；`m1_minus_12m2` :147-188；`FINITE_edgeX` :200-223、`FINITE_critical_edgeX`
:229-238；`DIHV_LE_0` :244-250、`DIHV_SYM` :256-312、`DIHX_POS` :317-329；
`SUM_SET_OF_2_ELEMENTS` :334-343。`KIZHLTL3_new_concl` :71-84 仅陈述无证（本 lane 死支——
NEGLIGIBLE_FUNC 只用 KIZHLTL4，不用 KIZHLTL3）。

### 1.3 上游输入（真实 GIANT 所在）

| HL 件 | 位置 | 规模 | 定级 / 硬点 |
|---|---|---|---|
| `KIZHLTL1` | KIZHLTL.hl:46-279（concl :9-44） | ~234 行 | **GIANT / 测度论**：`MEASURE_VORONOI_CLOSED_OPEN`、`MEASURABLE_VORONOI_CLOSED`、`NEGLIGIBLE_INTER_VORONOI_CLOSED`、`MEASURE_NEGLIGIBLE_UNIONS_IMAGE` 全在 Pack2.hl（**Lean 侧无移植**，PA16:77-79、PA19:66-68 双注记） |
| `KIZHLTL2` | KIZHLTL.hl:285-527 | ~243 行 | **GIANT**：消费 QZYZMJC（:260）+ card 边界计数（PACKING_BALL_BOUNDARY）+ `#1.012080 < mm1` |
| `KIZHLTL4` | KIZHLTL.hl:533-1032（concl :530-548） | ~500 行 | **GIANT**：和重排（DIHX_SYM、FINITE_MCELL_SET_LEMMA、MCELL_SUBSET_BALL_4）+ KIZHLTL3 架构复用 |
| `SUM_GAMMAX_LMFUN_ESTIMATE` | sum_gamma.hl:62-1465（concl :53-60） | **~1400 行** | **GIANT×最重**：BOUND_GAMMA_X_lmfun + CARD_MCELL_CONTAINS_POINT + beta-bump + T1/T2/T3 聚类拆分（leaf-cell 链） |
| `FINITE_MCELL_SET_LEMMA` | marchal3.hl:329-332 | 小 | **中等偏小**（PA15:229 有忠实陈述 skeleton） |
| `FINITE_PACK_LEMMA`（= Packing3.KIUMVTC） | — | — | **已真证**：`Statement.Packing.finite_inter_ball`（Kepler/Statement.lean:46-47，体积计数实证明） |

定义落点（pack_defs.hl）：`negligible_fun_p` :18、`negligible_fun_0` :20、
`fcc_compatible` :22、`gammaX` :143-145。

## 2. 树内存量盘点

### 2.1 PA19（`Kepler/Text/PackingAuto19.lean`，795 行；真 sorry 恰 3 个：:631、:665、:793）

**已证（scratch `#print axioms` 实测 = `[propext, Classical.choice, Quot.sound]`，零
sorryAx）**：

- **`FCC_COMPATABILITY_FUNC` :580-609** —— part 1 全真证（含 `p19_fcc_congr` :569-571
  私有 voronoiOpen 桥）；
- 数值链：`p19_mono/antitone` + Taylor 括号链 :151-290、`p19_arcsin_bounds` :292-316、
  `p19_sol0_eq` :320-324、`tau0_gt_p19` :333-339、`mm2_gt_p19` :347-376（**Flyspeck 常数界
  从 Mathlib π 区间+9 阶 Taylor 真证，零浮点 axiom**）；
- support kit：`tau0_not_zero` :379、`ZERO_LT/LE_MM2_LEMMA` :384/:389、
  `SQRT_RULE_Euler_lemma` :393、`SQRT_OF_32_lemma` :398、`m1_minus_12m2` :412、
  `FINITE_edgeX` :458、`FINITE_critical_edgeX` :474、`DIHV_LE_0` :481、`DIHX_POS` :493、
  `SUM_SET_OF_2_ELEMENTS` :503、`pos_lemma` :513、`negligible_fun_any_C` :528；
- RDWKARC 平移件：`JGXZYGW_KY` :669、`PACKING_SUBSET` :678、`PACKING_TRANS` :685、
  `SATURATED_TRANS` :695、`RADV_TRANS_EQ` :768。

**sorried（3）**：`NEGLIGIBLE_FUNC` :625-631（**全链唯一 UPFZBZM 缺口**）；`JGXZYGW_p19`
:659-665（private，PA1 lane 债）；`RDWKARC` :789-793（**已冗余**，见 §3.3）。

**shim（1）**：`SUM_GAMMAX_LMFUN_ESTIMATE_p19` :549-554 →
`PackingAuto18.SUM_GAMMAX_LMFUN_ESTIMATE`（陈述逐字相同；上游 sorry，taint 流动——实测
sorryAx）。

**Capstone `UPFZBZM` :638-646**：本体无 sorry 字面，
`refine ⟨G-witness, NEGLIGIBLE_FUNC …, FCC_COMPATABILITY_FUNC …⟩`。

**与 PA2.UPFZBZM_concl 陈述差异 = 零**：仅 currying（命名前提 vs 显式 ∀）。scratch 实测：
类型断言 `#check (UPFZBZM : ∀ V …)` 通过，且 `theorem d V : … := UPFZBZM V` 一行编译通过。
**junk 约定零分叉**：两侧的 `negligibleFun0`/`fccCompatible`/`setSum`（无穷集 junk=0，
PA2:124-125）/`Metric.ball`（开球，同 HOL `ball`）全是 PA2 同一常量；`negligibleFun0` 展开
（PA2:285-289）忠实保留 HOL 的 `0 ≤ C` 合取（PA19:528-532 的 `negligible_fun_any_C` 是剥壳
形式，由 `pos_lemma` :513-523 桥接，PA2 的 faithful def 不受影响）。注意 Lean
`fccCompatible` 用 `voronoi_open`（非 HOL 的 `voronoi_closed`）——PA19:100-102 注记在案，
这正是 Lean part 1 免 `MEASURE_VORONOI_CLOSED_OPEN` 的原因。

### 2.2 PA2 侧定义落点

`voronoiOpen` :189-190（private，体与 voronoiOpenP19/P16 逐字同）、`setSum` :124-125、
`negligibleFunP` :285-286、`negligibleFun0` :289、`fccCompatible` :293-294、
`cellClusterInequality` :524-525、`lmfunInequality` :528-530、`gammaX` :448-455、`lmfun`
:464、`TSKAJXY_statement` :954-956、`UPFZBZM_concl` :959-962、`KIZHLTL1/2/3_concl`
:917/:925/:933、`OXLZLEZ_concl` :948。

### 2.3 关键新发现：PA2.RDWKARC_concl 已真证装配

PA2:1106-1212 是**完整实证明**（unpack ¬keplerConjecture → UPFZBZM_concl + JGXZYGW_KY_p2
导出矛盾 → u∈V 边和>12 → 平移∩annulus witness → `setSumImage_p2`/`hlPairAdd_p2` 重编
annulus 和），taint 只来自两处：`UPFZBZM_concl`（:1124）+ private `JGXZYGW_KY_p2`
:1091-1097（sorry，PA1.JGXZYGW 链）。_p2 kit：`packingTrans_p2` :969、`hlPairAdd_p2` :1049、
`setSumCongr_p2` :1061、`setSumImage_p2` :1072。**任务背景"RDWKARC_concl 真化、密度上界
半边上移 UPFZBZM_concl"实测确认。**

### 2.4 装配章与依赖 lane 状态

`PackingConcl.lean`（777 行）：`UPFZBZM_concl_discharged` :510-514 已接 PA19.UPFZBZM；
`KIZHLTL1/2/3_concl_discharged` :456/:470/:480 已接 PA16（KIZHLTL1 带 voronoiOpenP16
delta 桥）。**docstring 过时两处**：① :508 称 "leans on the sorried
NEGLIGIBLE_FUNC/FCC_COMPATABILITY_FUNC pair"——FCC 实为干净；② 行号 `Auto2:854` 等已漂移
（实际 959，文件因 _p2 段增长）。上游 lane 现状：PA16
`KIZHLTL1 :250-255 / KIZHLTL2 :268-273 / KIZHLTL4 :310-323`、`QZYZMJC :224-226` 全 sorry；
PA15 `FINITE_MCELL_SET_LEMMA :229`（`FINITE_MCELL_SET_lemma1 :213-219`、`MCELLS_BOUNDED
:521` 亦 sorry）；PA18 `SUM_GAMMAX_LMFUN_ESTIMATE :2538-2539` sorry；PA13 `URRPHBZ2 :340-343`
sorry（KIZHLTL2 的下游件）。**PA19 header :51-52 "PA15/16 olean unbuilt" 已过时**——五个
olean 均在 `.lake/build`（2026-09-29 13:37 新鲜）；PA19 加 `import PA15/PA16` 无环
（PA15←PA2,5-13；PA16←PA2,12；PA19 仅被 PackingConcl 消费）。

## 3. 通路裁定

1. **"几乎免费装配"已经发生完了**：PA2 → PackingConcl discharge 一行式存在且编译（scratch
   复算通过）。PA19 侧**不需要再加任何装配行**。PA19.UPFZBZM 与 PA2 接口零字差、零 junk
   分叉。
2. **缺口精确定义**：`PA19.NEGLIGIBLE_FUNC`（:631 bare sorry）。给定四输入 + 有限性件，其
   填充是**中等**级机械活：HL 108 行 tactic 的 Lean 折算，预估 **150-250 行**（setSum 代数
   kit 40-80 + 主体 110-170）。FCC 半边零缺口。
3. **真化路径**（#print axioms 全干净）还欠五件：KIZHLTL1（GIANT，测度论 + Pack2.hl 整章桥
   是隐藏银行）、KIZHLTL2（GIANT）、KIZHLTL4（GIANT）、SUM_GAMMAX_LMFUN_ESTIMATE
   （GIANT×最重）、FINITE_MCELL_SET_LEMMA（中小）。
4. **bookkeeping**：`PackingConcl.RDWKARC_concl_discharged`（:518-524）现走 PA19.RDWKARC
   （bare sorry），**劣于** PA2 自身真装配体（PA2:1106-1212，taint 更少）——merge 时应改
   接线为 PA2 原件并删 PA19.RDWKARC:789-793。

## 4. 波计划

**Wave 1（lane 文件 = PA19，~180-280 行，中等，零新 sorry）**：填 `NEGLIGIBLE_FUNC` 架构。

- +2 行 import（PA15/PA16）；setSum 代数 kit（add/sub/neg/const/smul，dif-Finite 桥，先例
  `SUM_SET_OF_2_ELEMENTS`:503 与 `setSumCongr_p2` PA2:1061；TameLp:1253-1300 有部分公共件
  但建议本地写）；
- 主体：f1/f3/f4/f5 拆分 → B 有限性（PA15）→ `T1+T2+T3 = ΣB (gammaX V X lmfun)`（gammaX
  PA2:448 defeq + setSum_add）→ 四输入逐个 MP → witness `−c''' − c − c' − c''` 的实数算术。
- 风险：①voronoiOpenP16→P19 的 summand congr（`p19_fcc_congr` 同法，低）；②KIZHLTL4
  epsilon-guard 与 gammaX 内层的 `let q` 对齐（PA2:453 同形，中）；③`Σf3 = Nat.card · 8mm1`
  的 SUM_CONST 折算（低）；④KIZHLTL2/KIZHLTL4 若改从 PA16 import 而非留 shim，注意语句含
  `voronoiOpenP16` 的 KIZHLTL1 桥（低）。收尾：更正 PackingConcl:506-508 与 PA19 header
  过时注记。
- 交付后 `UPFZBZM_concl` 从"1 个裸 sorry"变为"忠实架构 + 4 个具名上游 taint"。

**Wave 2（lane 文件 = PA15+PA16，中-GIANT，~450-700 行）**：`FINITE_MCELL_SET_LEMMA`
（~100-150，消费已证的 finite_inter_ball + lemma1:213）→ `KIZHLTL1`（~250-350；**先做
Pack2.hl 测度桥四件套移植评估**，这是本波最大未知）→ `KIZHLTL2`（~150-250；QZYZMJC 仍
sorry 合法流动）。副产品：PA2.KIZHLTL1/2_concl 的 PackingConcl 接线自动变真。

**Wave 3（两个独立 lane，真银行）**：`KIZHLTL4`（PA16，HL ~500 行 → Lean 400-700）；
`SUM_GAMMAX_LMFUN_ESTIMATE`（PA18，HL ~1400 行 → Lean 600-1000；PA18 已有 2542 行 leaf-cell
骨架）。完成 + Wave 2 = UPFZBZM_concl 全链 axioms 干净。

## 5. 一句话结论

UPFZBZM 链已从"GIANT 盲盒"降维为：**一处 bare sorry（PA19:631 NEGLIGIBLE_FUNC，中等
150-250 行即可变成忠实架构）+ 四件已定位、已陈述、被两条装配线（PackingConcl 的
KIZHLTL1/2_discharged 与 PA19 的 shim）预接好的上游 GIANT（KIZHLTL1/2/4 + SUM_GAMMAX，
合计 HL ~2400 行）**；FCC 半边、数值常数、capstone、discharge、平移件全部真证在树，无任何
隐藏结构阻塞；Wave 1 可立即开工，Wave 2 的唯一未知量是 Pack2.hl 测度桥的移植体量。

验证脚本（可复跑）：`/tmp/upfzbzm_scout_check.lean`（axioms 审计 + 逐字差 + 一行
discharge）、`/tmp/upfzbzm_scout_check2.lean`（PA2 消费方 taint 审计）；scratch 实测输出
已在上文逐条引用。

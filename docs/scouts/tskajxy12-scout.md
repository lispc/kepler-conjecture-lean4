# tskajxy12-scout — TSKAJXY_1 / TSKAJXY_2（1/2 胞臂）侦察结案报告

> 2026-09-29 侦察 lane 交付，编排者落库。纪律记录：零 repo 文件改动、零 git 操作
> （仅 `git status/log` 只读）、未跑 auto_gate；轻量验证仅 /tmp scratch ×2 +
> `lake env lean`（单 lake 进程，PA21 olean 已在库，未触发任何仓库模块编译）。
> 所有 file:line 经 grep/sed 实测核对；公理审计经 `#print axioms` 实测。

**核心结论先行**：

① **两臂半山状态，定级双 GIANT 但已证一半**：PA21 两臂合计 53 件（HOL 逐件对账），
已证 32 件（含共享件 GAMMAX_NULLSET 与两臂全部 BIS_*/SDIFF_*/RCONE_*/点积代数——
**机械半场已清**），剩 **32 枚 sorry**（1 胞臂 11 + 2 胞臂 21），加 1 件**缺移植**
（`MCELL2_HL_LT_SQRT2`，HOL TSKAJXY3.hl:1678，PA21 NEEDS 清单漏登）。1 胞臂 ≈790
HOL 行折算 **~900–1600 行 Lean**（2 波）；2 胞臂 ≈1400 HOL 行折算 **~1700–2600 行
Lean**（3 波）。

② **解析侧零新债**：`gamma2_x_div_azim_v2`（PA21:125-128 ↔ TSKAJXY3.hl:2065-2068）
逐字忠实（sqrt8→`Real.sqrt 8` 内联，per PA21:43-44 编码注记）；
`0 ≤ gamma2_x_div_azim_v2 (h0cut y) (y*y)` 的解析不等式**不在本通道重证**——它经
`grk_bank → GRKIBMP`（PA21:465，波 1 已证、公理审计 sorry-free）到达，Phase 4
非线性银行仅以 `bank_GRKIBMPAV2/BV2`（:336/:343）假设叶挂账，**无新增牵扯**。

③ **真正的硬点在 vol1 体积层，不在解析层**：`MCELL2_VOL_SPLIT_EXPLICIT`（:2409）与
`MCELL2_SOL`（:2488）需要 frustt∩wedge 与 conic_cap∩wedge 两个楔形体积闭式（HOL 里
是 `volume_props` 公理级给定，vol1.hl:118/:133；**树内无对位**）。但
`Kepler.Geom.WedgeVolume` 已有全套切片模板（`lintegral_parabola`:660、
`measurePreserving_proj`:450、`volume_ball_wedge`:831 已证）+
`SolidAngle.volume_solid_triangle`:870 已证——照抄模板可组，非从零积分。

④ **共享件三条红线**：(a) 波 2a `mi_*` kit + `p21_*` 私件**全部现成可直接用**（逐件
见 §3）；(b) `HDTFNFZ_ALT`(PA4:1240)、`WEDGE_WEDGE_GE`/`WEDGE_SUBSET_WEDGE_GE`
(PA18:873/2457)、`WEDGE_GE_EQ_AFF_GE`(LocalAuto5:2157) 在树内但**在 PA21 import
闭包之外**（/tmp `#check` 实证 unknown identifier）——PA4/PA18 均为无环增量
import，PA18 的同名 `MCELL2_SUBSET_AFF_GE` 冲突已被 `_p21` 后缀预留（PA21:24-26）；
(c) `jg_*`（PackingJGXZYGW）的 negligible 系与 `GAMMAX_NULLSET` 类**不同构不复用**
（前者是 packing 求和上界族，后者是定义折叠，见 §3.3）。

⑤ **上游 tilt 一枚**：`MEASURABLE_MCELL`（PA10:517）经 `rogers_measurableSet_p10`
（PA10:402 private sorry）染 sorryAx，连带已证件 `MCELL1_VOL_RESTRICT`（:1564）与
`MCELL2_INTER_BIS_LE_MEASURABLE`（:1818）公理不净（/tmp 实测）。不阻塞两臂收口，
但 capstone 公理审计会暴露，需在报告/闸门口径预登记。

---

## §0 定位与消费链（Lean 侧实测）

```
HOL: TSKAJXY3.hl (2288 行, 1 def + 66 thm)
  ├─ 1 胞臂 :23-839   GAMMAX_NULLSET … TSKAJXY_1(:780)   [HJKDESR1a_1cell:766 已 dedup→PA20]
  ├─ 2 胞臂 :841-2238 MCELL_CELL_PARAMETERS_D_EXIST … TSKAJXY_2(:2181)
  └─ capstone TSKAJXY :2251（消费 TSKAJXY_034 + _1 + _2 + tsk_required_ineq:2240）
Lean: PA21 = lean/Kepler/Text/PackingAuto21.lean (2557 行, 35 sorry)
  ├─ 1 胞臂 :1425-1710（12 证 / 11 sorry）
  ├─ 2 胞臂 :1712-2510（20 证 + 1 def / 21 sorry + 1 缺件）
  └─ capstone TSKAJXY :2532-2555 已证（装配真：by_cases 分派 _1/_2/TSKAJXY_034）
消费者：PA25:71 `import Kepler.Text.PackingAuto21`（PACKING_CHAPTER_MAIN_CONCLUSION 链）——
  只填 sorry 不动陈述则下游 elaboration 零扰动（merge-ineq 波 0-3 已实证同型操作安全）。
capstone 行号复核：TSKAJXY_1 sorry 在 **:1710**（任务背景"2492 一带"实为
  GAMMAX_GAMMA2_X :2492-2503），TSKAJXY_2 sorry 在 **:2510**（:2507 是 docstring 行）。
```

## §1 树内存量盘点

**1 胞臂（mcell1 measure/split kit，PA21 :1425-1710）**——23 件，12 证（52%）/
11 ★；证毕件公理全净除 MCELL1_VOL_RESTRICT（† 经 MEASURABLE_MCELL）：

| 件 | PA21 行 | HOL 行 | 状态 | 备注 |
|---|---|---|---|---|
| GAMMAX_NULLSET | :1426 | :23 | ☆ 净 | nullSet→gammaX=0，setSum 折叠 |
| GAMMAX_MCELL1 | :1444 | :48 | ★ | 需 VX={u0}+edgeX=∅（V_CELL1_SINGLE 链） |
| BALL_DIFF_RCONE_GT | :1471 | :176 | ☆ 净 | 纯内积代数 |
| BALL_DIFF_RCONE_GT_BISECTOR | :1499 | :201 | ☆ 净 | + p21_dist_le_half2 :1390 |
| MCELL1_EXPLICIT | :1530 | :226 | ☆ 净 | mcell1 if-展开 |
| MCELL1_VOL_RESTRICT | :1564 | :244 | ☆† | 球面薄片 null（addHaar_sphere） |
| MCELL1_SOL_RESTRICT | :1613 | :285 | ★ | URRPHBZ2-k1 径向 + sol_spec |
| CONV_CONVEX_HULL | :1621 | :328 | ☆ 净 | |
| CONVEX_HULL_4_AFF_GE | :1630 | :336 | ★ | polytope：hull = 双 affGe 交 |
| CONVEX_HULL_SCALE | :1637 | :363 | ★ | 消费上件 |
| IMAGE_4_EXPLICIT | :1645 | :394 | ☆ 净 | |
| NULLSET_MCELL1 | :1549 | :405 | ☆ 净 | 测度单调 |
| NOT_COPLANAR_OMEGA_LIST_N | :1655 | :422 | ★ | 4 omega 点非共面 |
| NOT_COPLANAR_R3 | :1662 | :452 | ★ | aff_dim=3 → span=⊤ |
| BARV_DISTINCT | :1667 | :464 | ★ | barV1 → u0≠u1 |
| OMEGA_LIST_BISECTOR | :1672 | :495 | ★ | **臂内最大几何件**（HOL 93 行） |
| DIFF_INTER | :1679 | :589 | ☆ 净 | |
| RCONE_GT_SCALE | :1840 | :597 | ☆ 净 | |
| BARV3_TRUNC1 | :1685 | :612 | ☆ 净 | |
| MCELL1_RADIAL | :1691 | :624 | ★ | HOL 106 行，消费 4 件 kit |
| MCELL1_VOL | :1698 | :731 | ★ | 组装件，依赖齐后机械 |
| HJKDESR1a_1cell | (dedup) | :766 | ☆（PA20:237） | 数值种子 |
| **TSKAJXY_1（capstone）** | :1708-1710 | :780 | ★ | `∀ V ul, saturated→Packing→barV V 3 ul → gammaX V (mcell1 V ul) lmfun ≥ 0` |

**2 胞臂（cell_params_d / BIS / SDIFF / FRUSTT / vol-sol 归约，PA21 :1712-2510）**——
43 项（42 thm + 1 def），20 证（47%）/21 ★ + 1 缺件：

| 件 | PA21 行 | HOL 行 | 状态 | 备注 |
|---|---|---|---|---|
| MCELL_CELL_PARAMETERS_D_EXIST | :1713 | :841 | ★ | epsilon 见证判定 |
| INITIAL_SUBLIST_2 | :1720 | :868 | ☆ 净 | |
| MCELL2_CELL_PARAMETERS_EXIST | :1733 | :884 | ★ | |
| MCELL_PARAM_D_UL | :1739 | :897 | ★ | |
| MCELL2_PARAM_D_UL | :1747 | :923 | ★ | |
| MCELL2_DIHX | :1755 | :936 | ★ | dihX=dihu2 折叠 + 见证迁移 |
| BIS_LE_INTER / BIS_LE_UNION / BIS_HYPERPLANE | :1762/:1772/:1792 | :978/:987/:996 | ☆ 净×3 | |
| MCELL2_INTER_BIS_LE_MEASURABLE | :1818 | :1007 | ☆† | 经 MEASURABLE_MCELL |
| MCELL2_VOL_SPLIT | :2204 | :1031 | ★ | 依赖已全备（p21_hyperplane_null） |
| RCONE_GE_COS | :1889 | :1067 | ☆ 净 | |
| DIST_LAW_OF_COS_ALT | :1947 | :1093 | ☆ 净 | |
| ATN_DIV / REAL_DIV_NEG / ATN2_Y_NEG | :1965/:1974/:1979 | :1103/:1119/:1128 | ☆ 净×3 | |
| RCONE_PAIR | :2053 | :1153 | ☆ 净 | 二次型代数 125 行已清 |
| MCELL2_SPLIT | :2196 | :1231 | ★ | NEEDS 注记 :2179-2195 有弃稿路线 |
| FRUSTT_RCONE_GE | :2211 | :1275 | ★ | 锥面 Fubini-null 是唯一新数学 |
| SDIFF_SUBSET / SDIFF_TRANS / NULL_SDIFF_TRANS / SDIFF_SYM | :2217/:2224/:2230/:2397 | :1339/:1348/:1357/:1546 | ☆ 净×4 | |
| FRUSTT_WEDGE_RCONE_GE | :2241 | :1368 | ★ | 组装件（消 FRUSTT_RCONE_GE+wedge kit） |
| MCELL2_SUBSET_AFF_GE_p21 | :2253 | :1419 | ☆ 净 | `_p21` 后缀防 PA18 撞名 |
| NOT_COPLANAR_EXTREME_MCELL2 | :2273 | :1434 | ★ | |
| MCELL2_DIHV_LT_PI / MCELL2_DIHV_AZIM | :2279/:2286 | :1456/:1477 | ★×2 | |
| BIS_LE_NORM / BIS_LT_NORM | :2296/:2361 | :1510/:1528 | ☆ 净×2 | |
| MCELL2_VOL_SPLIT_EXPLICIT | :2403 | :1555 | ★ | **GIANT**：需 frustt∩wedge 体积闭式（树内缺） |
| — MCELL2_HL_LT_SQRT2 — | **缺** | :1678 | **未移植** | 15 行 trivial；GAMMAX_GAMMA2_X/TSKAJXY_2 的 HOL 证明都消费它；PA21:78-89 NEEDS 清单漏登 |
| LEFT_ACTION_LIST_1_PROPERTIES_ALT | :2414 | :1694 | ★ | HOL 本体=一行 rewrite；Lean 侧 PA14 对位 kit 仍 sorry（PA14:231/258/286） |
| MCELL2_PERMUTE_01 | :2426 | :1714 | ★ | 消费上件 |
| MCELL2_VOL | :2435 | :1774 | ★ | =VOL_SPLIT+VOL_SPLIT_EXPLICIT×2 半 |
| BALL_SUBSET_BIS_LE / BALL_SUBSET_BIS_LT | :2444/:2457 | :1817/:1833 | ☆ 净×2 | |
| RADIAL_LE | :2469 | :1849 | ☆ 净 | |
| MCELL2_SOL | :2481 | :1859 | ★ | **臂内最大单件**（HOL 205 行） |
| gamma2_x_div_azim_v2 (def) | :125 | :2065 | ☆ 忠实 | sqrt8 内联 |
| GAMMAX_GAMMA2_X | :2492 | :2070 | ★ | 装配件（几何依赖齐后中等） |
| **TSKAJXY_2（capstone）** | :2507-2510 | :2181 | ★ | sorry 即 :2510 单点 |

**两臂合计：66 项，32 证（约 48%）/ 32 ★ + 1 缺件。** PA21 全文件 sorry 账（grep
实测 35 枚）= 两臂 32 + 0/3/4 臂 2（TSKAJXY_034 :1310、mi_gamma3f :947，界外）+
`pack_nonlinear_rest` :370（G4 占位叶）。capstone `TSKAJXY` :2532 已证（公理含
sorryAx——来自三臂，装配逻辑本身真）。

## §2 HOL 侧链全图

**1 胞臂（TSKAJXY3.hl :23-839，≈790 行）**——测度/立体角链：
主干 `¬NULLSET(mcell1)` → `MCELL1_EXPLICIT`(:226) 三路分流：(a) 体积路
`MCELL1_VOL_RESTRICT`(:244 √2-球面切片 null) + (b) 立体角路
`MCELL1_SOL_RESTRICT`(:285 URRPHBZ2-k1 径向 + sol_spec) + (c) 径向路
`MCELL1_RADIAL`(:624) → `MCELL1_VOL`(:731, sol_spec 合成 vol = √2³/3·sol) →
`TSKAJXY_1`(:780 系数比对，数值种子 HJKDESR1a_1cell 已在 PA20)。
硬点排序：OMEGA_LIST_BISECTOR（93 行，affGe 锥=二分半空间，真几何）>
MCELL1_RADIAL（106 行 kit 组装）> MCELL1_SOL_RESTRICT（rogers 尾巴可能拖 Auto11
债）> CONVEX_HULL_4_AFF_GE/SCALE（polytope）> GAMMAX_MCELL1。**无浮点、无解析
gamma2**。

**2 胞臂（TSKAJXY3.hl :841-2238，≈1400 行）**——体积/立体角归约链：
记账层（cellParamsD epsilon 四件 + MCELL2_DIHX + MCELL2_VX_PROPS）→ 可略性层
（MCELL2_VOL_SPLIT 二分半空间并 + 双曲平面 null → MCELL2_SPLIT 胞=双 cone∩wedge
具体化，退路 u=v→2 维仿射子空间 null → FRUSTT_RCONE_GE 锥面 Fubini-null →
FRUSTT_WEDGE_RCONE_GE）→ 体积/立体角层（`MCELL2_VOL_SPLIT_EXPLICIT`:1555 需要
VOLUME_FRUSTT_WEDGE=vol1.hl:473 公理级闭式 `azim·h³(1/a²−1)/6`；`MCELL2_SOL`
205 行：URRPHBZ2-k2 径向 + VOLUME_CONIC_CAP(_WEDGE) 闭式 + SDIFF 账）→ 解析桥
`GAMMAX_GAMMA2_X`(:2070)：GAMMAX_MCELL2 + MCELL2_VOL + MCELL2_SOL(+PERMUTE_01)
+ MCELL2_DIHX + DIHV_EQ_DIH_Y + DIHV_RANGE + lmfun_h0cut + sqrt8_sqrt2 →
`TSKAJXY_2`(:2181) = GAMMAX_GAMMA2_X + GRKIBMP + y_bounds + 实数账。
**Phase 4 牵扯：无新增**——解析不等式本体即 grk_bank 两叶，本通道只消费
`proj_grk_bank`。

## §3 与前波的共享件

**3.1 波 2a `mi_*` kit + GRKIBMP 分发器（PA21 内，公理全净）——直接复用**：
`GRKIBMP`(:465)、`mi_lmfun_h0cut`(:665)、`mi_sqrt8_eq`(:513)、`mi_y_bounds`(:823)、
`mi_two_*`/`mi_201_*` 数值族(:798-816)、`p21_h0cutA/B`(:437/:442)、
`p21_nonf_gamma2x1DivAV2(_yOfX)`(:452/:458)。1 胞臂从 mi_* 只需 HJKDESR1a_1cell
（PA20 经 import 到手）。

**3.2 `p21_*` 私件（全净）——直接复用**：点积代数 14 件(:1314-1423)、
`p21_sq_eq`(:1779)、`p21_smul_dotP`(:1831)、`p21_cos_arcV` 三件(:1863/:1928/:1939)、
**`p21_hyperplane_null`(:1995)**（MCELL2_VOL_SPLIT 与 FRUSTT 系的现成引擎）、
`p21_pivot_lt_aux`(:2347)。需自带的副本/新件：`p15_dihV_range`(PA15:147 private
不可见，~10 行重抄)、`p38_dihV_eq_dihY`(LocalAuto38:1114 private 未 import；
dihV 平移协变 → 推广到 apex u0 近乎 rfl，~40-80 行)、`p21_hl2 : hl [a,b] =
dist a b / 2`（HOL `Marchal_cells_3.HL_2` 对位，树内无现成件，被 5+ 处消费）。

**3.3 jg_*（PackingJGXZYGW）与 GAMMAX_NULLSET 类可略性——不同构，零复用**：
`jg_negligible_fun_p` 是 packing 求和上界族，GAMMAX_NULLSET 是定义折叠，FRUSTT/BIS
可略性是超平面/锥面/球面零测——仅共享 Mathlib 测度习语。PA19 setSum kit 不值得为
它拖闭包（PA21 不 import PA19；GAMMAX_NULLSET :1436 已示范 `simp [setSum]`）。

**3.4 闭包外现成件（建议增量 import，均无环）**：
- `HDTFNFZ_ALT`(PA4:1240 已证)：MCELL2_VX_PROPS / GAMMAX_MCELL2 / TSKAJXY_2 需要；
  PA4 imports {PA2,PA3,PA11}，加入 PA21 无环。
- `WEDGE_WEDGE_GE`(PA18:873)、`WEDGE_SUBSET_WEDGE_GE`(PA18:2457)：FRUSTT_WEDGE_
  RCONE_GE / MCELL2_SOL 需要；PA18 无环；撞名已由 `_p21` 后缀预案。
- `WEDGE_GE_EQ_AFF_GE`(LocalAuto5:2157) 若要则连 LocalAuto5，或经 PA18 变通。
- `MEASURABLE_MCELL`(PA10:517 已在闭包，†tilt)、`BARV_IMP_HL_1_POS_LT`(PA12:757
  已在闭包)、`azim_dihv_same`/`volume_ball_wedge`/`volume_solid_triangle`/`sol_spec`
  （Kepler.Geom，全净）。

## §4 定级与波计划

**Mathlib 对位速查**：现成——超平面 null（addHaar_affineSubspace）、球面 null
（addHaar_sphere）、finrank 维数账、affineIndependent→span=⊤、测度加性/单调。
要自组——锥面 Fubini-null（FRUSTT_RCONE_GE；固定 z-切片 + measure_prod_null
路线）、楔形体积双闭式（WedgeVolume 切片模板克隆）、HL_2 micro-helper、dihV↔dihY
桥适配。

**1 胞臂：定级 GIANT，~900–1600 行，切 2 波**

- **波 A1「1 胞几何层」**：BARV_DISTINCT、NOT_COPLANAR_R3、CONVEX_HULL_4_AFF_GE、
  CONVEX_HULL_SCALE、NOT_COPLANAR_OMEGA_LIST_N。目标 ~350–650 行。纯隔离几何风险。
- **波 A2「1 胞测度-立体角-装配」**：OMEGA_LIST_BISECTOR、GAMMAX_MCELL1、
  MCELL1_SOL_RESTRICT、MCELL1_RADIAL、MCELL1_VOL、TSKAJXY_1。目标 ~550–950 行。
  风险：OMEGA_LIST_BISECTOR 臂内唯一深几何（先证 face ⊆ bis 平面 + 维数/半空间
  双向夹逼）；MCELL1_SOL_RESTRICT rogers 尾巴备选 k=1 具体化绕 URRPHBZ2 capstone；
  MEASURABLE tilt（†）口径预登记。

**2 胞臂：定级 GIANT，~1700–2600 行，切 3 波**

- **波 B1「2 胞记账 + 可略性」**：补缺件 MCELL2_HL_LT_SQRT2（~15 行）、
  MCELL_CELL_PARAMETERS_D_EXIST、MCELL2_CELL_PARAMETERS_EXIST、MCELL_PARAM_D_UL、
  MCELL2_PARAM_D_UL、MCELL2_DIHX、MCELL2_VX_PROPS（需 import PA4 取 HDTFNFZ_ALT）、
  MCELL2_VOL_SPLIT、FRUSTT_RCONE_GE。目标 ~600–1000 行。风险：epsilon 四件的
  Classical.choice 记账；FRUSTT_RCONE_GE 锥面 Fubini-null 唯一新数学（~100-200 行）；
  MCELL2_SPLIT 退格 null 论证顺手落地。
- **波 B2「楔形体积库 + mcell2 几何」**：新建 wedge-volume 双件
  （`volume (frustt∩wedge) = azim·h³(1/a²−1)/6`、`volume (ball∩rconeGe∩wedge) =
  azim(1−c)r³/3`，照 WedgeVolume 切片模板）；FRUSTT_WEDGE_RCONE_GE、
  NOT_COPLANAR_EXTREME_MCELL2、MCELL2_DIHV_LT_PI、MCELL2_DIHV_AZIM、
  LEFT_ACTION_LIST_1_PROPERTIES_ALT、MCELL2_PERMUTE_01（需 import PA18 或自证
  WEDGE_SUBSET_WEDGE_GE ~40 行）。目标 ~500–900 行。风险：楔形体积两件是真积分
  工作（lintegral_parabola 改被积函数 `t²(1/a²−1)θ/2`）；LEFT_ACTION 链需自证
  ~80-150 行。
- **波 B3「vol-sol 归约 + 解析装配」**：MCELL2_VOL、MCELL2_SOL、GAMMAX_GAMMA2_X、
  TSKAJXY_2（附 dihV↔dihY 桥适配 + p15_dihV_range 副本 + p21_hl2 helper）。目标
  ~300–600 行。风险：MCELL2_SOL 链内最大单件但 B1/B2 落地后为组装-中等；
  BARV_DISTINCT 跨臂依赖注意波序（A1→B3）；解析侧零风险。

**总量**：两臂 5 波 ~2600–4200 行；波间依赖 A1→A2、B1→B2→B3 严格链。压波次选项：
A1 可与 B1 并行（零相交），B2 可拆出 wedge-volume 独立小波先行。

## §5 风险与口径附注

1. **缺件预警**：`MCELL2_HL_LT_SQRT2` 未移植且不在 PA21:78-89 NEEDS 清单——按
   NEEDS 清单施工会在 GAMMAX_GAMMA2_X/TSKAJXY_2 处卡死。
2. **NEEDS 清单过时项**：`RCONE_PAIR`、`MCELL2_INTER_BIS_LE_MEASURABLE`、`TSKAJXY`
   已证（waves 2/3 落账），实际余债 33 件 sorries + 1 缺件。
3. **公理口径**：现 capstone `TSKAJXY`/`TSKAJXY_1`/`TSKAJXY_2`/`GAMMAX_GAMMA2_X`
   均含 sorryAx；收口后仍会因 `MEASURABLE_MCELL`←PA10 rogers sorry 与
   `pack_nonlinear_rest`（G4）残留 sorryAx——两臂「局部清零」≠「公理净」，闸门
   报告按 merge-ineq 章程 §4.3 口径写。
4. **`_p21` 撞名预案**：import PA18 后 PA18 的 `MCELL2_SUBSET_AFF_GE` 与本文件
   `_p21` 后缀件并存——已备案，勿"顺手去重"（两者陈述不同，plan §6 明文禁止）。
5. 轻量验证产物：/tmp/tskajxy12_check.lean、/tmp/tskajxy12_ax2.lean（一次性
   scratch，未写 repo）。

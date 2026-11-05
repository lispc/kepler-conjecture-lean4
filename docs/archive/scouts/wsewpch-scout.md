# WSEWPCH 核测绘（2026-10-23，Lane BH 交付）

> 快照：`lane_snapshots/wsewpch-scout/`。**关键发现**：WSEWPCH 的 Lean 渲染**已在树内**
> （LocalAuto7:698 完整陈述 + FAN_PERIMETER:694 + BGMIFTE:662，全 faithful sorry，DISCHARGES
> 契约），且 **LocalAuto7 整闭包（71 模块）是 TameLp 闭包（129 模块）的子集**——LA5 型
> "不可 import"地雷在 LA7 上不存在（唯一撞名 1 枚且未被消费）。LA5 的 local-fan foundation
> 章 26+ 件全真证（_p2 词表），LA7 的 34 桩里约半数可经 AzimBridge（808 行零 sorry）+ _p2↔_p3
> rfl 桥**换形白拿**。真实剩余 = 纯几何 14 件（~200 HOL 行）+ 真数学四巨件
> （BGMIFTE 1050 / KCHMAMG 280 / CIZMRRH 275 / HALP_CIRCLE 165）+ WSEWPCH 本体装配。
> 总量 ~2570–4740 行，6 大波（可拆 9 小波），4 波立即可开。**零误植**（六件逐前提核对全对齐，
> ykit11 hcore 为已文档化的合法换形，非漂移）。

---

# WSEWPCH 核侦察报告（SCOUT）

> 车道：BH 只读侦察（完全只读，零构建、零 tracked 写、零 git 操作）。
> 基线：main @ `9ba6beea`（ykit11 入仓 2b1c9f60 之后）。交付：本文件、`DEP_MAP.tsv`、
> `WAVES.md`、`MD5SUMS`。
> 方法：polar_fan.hl:2213-3360 + BGMIFTE(:1065-2115) 逐段读；WRGCVDR.hl:2902-3331
> （circular/lunar/generic 定义 + CIZMRRH）；local_lemmas.hl:3197-3476/:4557-4700/:5653-5818/
> :6027-6071 + local_lemmas1.hl:3056-3068 读证；lp_main_estimate-compiled.hl:1473-1543
> 五步逐段读；LA1/2/3/5/6/7 + AzimBridge 全 sorry 普查（python 逐件判定）；TameLp 全
> 闭包 import 实测（python BFS 129 模块）；全库（Text+Geom）按名普查 90+ 件真证/sorry 状态。

## 0. 结论速览

1. **WSEWPCH 实测比 ykit11 交付图大、但比它"更可拆"。** HOL 本体 :2213-**3360**（1148 行，
   非 ykit11 所记 :2213-2560）；其 Lean 渲染**已在树内**：LA7:698 `WSEWPCH`（陈述与 HOL
   逐字同）、:694 `FAN_PERIMETER`、:680/:688 `FAN_PERIMETER_INVARIANT(_CARD_V)`、:662
   `BGMIFTE`、:651 `fanPerimeter`(=IQCPCGW 折算)——LA7 头注 :81-83 明言这 34 桩是
   "polar-fan chapter contract"，由 Local-Fan foundation 落地时 DISCHARGE。
2. **import 可达性（本侦察最重要增量）：TameLp ← LocalAuto7 无地雷。** python BFS 实测：
   TameLp 闭包 129 模块，LA7 闭包 71 模块，`LA7 \ TameLp = {LA7 本身}`（LA1 经 LA16 已在
   TameLp 闭包内！）。LA7 全部 65 件导出名与 TameLp 闭包仅 **1 枚撞名**
   （LOCAL_FAN_ORBIT_MAP_EXPLICIT，LA7:444 vs LA2:1488，且 TameLp 不消费该名，同命名空间
   不消费即无歧义错）。对照：LA5 撞 3 枚（AFF_GE_MONO_TRANS/CONDS_IN_CONV2/
   FINITE_CARD1_IMP_SINGLETON ← PA18:3267/:4018/:5413，AT 车道实录复核属实）；
   **LA3、LA6 零撞名**。结论：LA7/LA3/LA6 都可本地 import，"deferred 到合并期"成本归零。
3. **LA5 foundation 章是金矿**：WSEWPCH 证明要吃的 ~30 件 local_lemmas 件里 **26 件在
   LA5 真证**（_p2 词表；DEP_MAP E 区全表），含全部轨道/双射/内角 kit。LA7 的 LocalFan-世界
   桩多数是"MESON/LA5 换形"件。**唯一成规模的缺环 = 桥本身**：
   `LocalFan(LA1) → localFan_p3 → localFan_p2` 正向打包（AzimBridge 只有反向
   `LocalFan.of_localFan_p3`:739 + 正向数据抽取 `localFan_data`:660，均真证；
   p2↔p3 rfl 桥照 §1 _p4↔_p3 配方未写）。
4. **真数学缺口仅四件**（+WSEWPCH 本体装配）：BGMIFTE（HOL 1050 行，极扇对偶）、
   KCHMAMG（280，circular 支）、CIZMRRH（275，三分前提）、HALP_CIRCLE_IS_INTERSECTION
   （165，lunar 支）。ykit11 点名的五桩里 **CARD_IS_LEAST_CYCLE 是 21 行近机械件**
   （唯一实质前提 LOFA_IMP_DIS_ELMS23 已真 LA5:6263）。
5. **2π 求和引擎就位**：PA25:10090 `ORDER_AZIM_SUM2Pi0`（真证）↔ LA7:498
   `ORDER_AZIM_SUM2Pi_0`（桩）只差 n↦n+1 指标平移；PA22:7562 同族 1-index 版亦真证；
   TopologyFan:1105 `sum4_azim_fan`、CA7:543 node-和 2π 邻族全真。circular/lunar 两支的
   求和收口**零新数学**。
6. **分类汇总**：(a) 已证/树内可换形 **41 件**；(b) 机械移植 **~20 件**（LA7 纯几何 14 +
   LA6 轨道 6）；(c) 桥 **3 件**（p2↔p3 rfl、localFan_p3.of_LocalFan 打包、dart-和桥）；
   (d) 真数学缺口 **4 件 + WSEWPCH 三分支装配本体**。
7. **消费面**：终点消费 = TameLp:835-848 `fully_surrounded_perimeter_bound`（文件唯一残源，
   e2e map:49 认定为"唯一残源·单锚 WSEWPCH 核"），下游 MQMSMAB(:10479 经 CRTTXAT)→
   tame_planar_hypermap。grep 全库无其他 NEEDS 消费者；docs/scouts/conforming-wall-scout.md
   :79/:230/:282 与 mqmsmab-scout.md:242 仅注记引用。**无第二消费方，W6 闭合即解锁 e2e 直源。**

## 1. WSEWPCH 数学内容拆解（三分结构）

**陈述**（polar_fan.hl:2213）：`∀ V E FF, convex_local_fan(V,E,FF) → fan_perimeter(V,E,FF) ≤ 2π`，
其中 fan_perimeter（IQCPCGW :2115）= 从 ε-顶点出发 rho_node1 轨道逐步 arcV(0,·,·) 求和
（CARD FF 截断；FAN_PERIMETER :2184 把它重表达为 `sum V (v ↦ arcV 0 v (rho_node1 FF v))`）。

**证明骨架**（:2253 起，CARD V 良基归纳 + CIZMRRH 三分 WRGCVDR.hl:3056）：
- **circular 分支**（:2273-2339，当 circular V E）：前提 KCHMAMG（local_lemmas.hl:3197，
  280 行）给出全顶点 interior_angle1=π + 过 0 平面 A ⊇ V + 法向 e + `azim_cycle V 0 e v =
  rho_node1 FF v` + 逐点 `azim 0 e v (rho_node1 v) = arcV 0 v (rho_node1 v)`。于是
  fan_perimeter = azim 轨道和 → **ORDER_AZIM_SUM2Pi_0**（:488）收口 = 2π（再 REAL_EQ_IMP_LE）。
  真缺口 = KCHMAMG 本体（平面性 + cyclic_set 特征；azim_cycle kit 在 LA5 已全真：
  FIRST_AZIM_CYCLE_EQ_RHO_NODE:2509 / AZIM_LAST_POINT_IN_RHO_SET(2):2668/:3040 /
  KOMWBWC:3054 / V_AZIM_SMALLEST_ELMS:2624）。
- **lunar 分支**（:2340-2549，∃ 共线对 (w,z)）：共线对把 V 劈成 w-片与 z-片
  （HKIRPEP local_lemmas.hl:6027 给 i/j 轨道指数与半圆交集合）、CARD V = m+n
  （**CARD_IS_LEAST_CYCLE** local_lemmas1.hl:3056 + LOFA_IMP_ITER_RHO_NODE_ID）、
  周长和 = 两片 azim 望远镜和（sum4_azim_fan，逐项 AZIM_ARCV:31 + lemma1/lemma2
  共面性），每片 ≤ π（COLLINEAR_AZIM_0_OR_PI 收口）→ ≤ π+π ≤ 2π。
  真缺口 = HALP_CIRCLE_IS_INTERSECTION（:5653，165 行）；
  **RHO_NODE1_MONO_WITH_AZIM**（:4557，144 行，全树未移植）供两支单调性。
- **generic 分支**（:2550-3360）两段：
  (i) 全内角 < π：走**极扇对偶** BGMIFTE（:1065，1050 行巨件）——polar_fan(V,E,FF)
  （JNVXCRC :1053 定义，v ↦ v × rho_node1 v）仍是 convex_local_fan，且
  arcV(0, prime' v, prime'(r v)) = π − interior_angle1(0,FF,r v)（双向）；由
  NKEZBFC（sol ≥ 0）+ SOL_LOFA_EQ_SUM_INANGLE 得 sum V arcV ≤ 2π（SUM_IMAGE 需
  prime' 单射，GENERIC_LOCAL_FAN_AZIM_POS :408 的 sin>0 引擎）。
  (ii) 存在 interior_angle1 = π 顶点：GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE（:188）把 v 放进
  aff_ge{0}{ivs,rho}，dart 分裂成 V' = V∖{v} 的小扇（E' = {{v,r v}}、FF' = {(v,r v)}），
  `fan_perimeter = sum V' arcV = [arcs at u] + arcV 0 u v + arcV 0 v rho`（ANGLES_ADD_AFF_GE
  :74 拆角），**良基归纳**（CARD V' < CARD V）收口。
- **三分前提 CIZMRRH**（WRGCVDR.hl:3056，275 行）：local_fan ⟹ generic/circular/lunar
  三态互斥完备。hypermap_lemma（Hypermap.lean:789 真）为主动机。

每支的缺口性质：circular = 球面组合（cyclic_set 特征）；lunar = 平面几何（半圆-锥交）；
generic = 极扇对偶（cross-构造的对偶凸性）；三分前提 = hypermap 组合。无一件是"轨道计数"
型新引擎——轨道 kit 全部已在 LA5 真证。

## 2. 资产真实边界（普查表全文见 DEP_MAP.tsv，96 行）

- **LA7（702 行，56 定理）**：15 机械件 PROVED（DIHV_ARCV/AZIM_ARCV/PLANE_AFFINE_HULL_3/
  AZIM_CYCLE_*/nnOfHyp3 等），34 桩 = 纯几何 14 + LocalFan 世界 12 + 终件 3
  （BGMIFTE/FAN_PERIMETER/WSEWPCH）+ 2π/轨道 5。
- **LA5（8098 行，265 定理，6 桩）**：桩 = KCHMAMG:5018、HKIRPEP:7986、
  HALP_CIRCLE_IS_INTERSECTION:7670、LOFA_V_SUBSET_AFF_HULL:4895、
  NOT_COLLINEAR_CONV0 相关 :4156/:4886/:4900 三件。**foundation 章全真**。
- **LA6（1238 行，118 定理，60 桩）**：WSEWPCH 相关子集 8 件全桩
  （CARD_IS_LEAST_CYCLE:831、LOCAL_RHO_NODE_PAIR_E:716、LOFA_IMP_ITER_RHO_NODE_ID2:728、
  IVS_RHO_NODE_DIFF_ID:892、LOCAL_FAN_RHO_NODE_IVS:860、POINT_PRESENTED_IN_RHOND1:897、
  LT_CARD_MONO_LOFA:953、CROSS_PAIR_NOT_IN_FF:733）；ARCV_BOUNDS:373 真。
- **LA3（1885 行，113 定理，11 桩）**：CIZMRRH:1881 桩；CYCLIC_SET_IMP_NOT_COLLINEAR:761
  **真**；HYP_LEMMA 族 :1293/:1302/:1310 三桩（= LocalFan→_p3 打包的实质缺口）。
- **LA1/LA2/AzimBridge**：LA1 ConvexLocalFan/LocalFan 定义真（orbitMap 版，:167/:169）；
  LA2 localFan_p2 定义真（Hypermap 版 :195）+ NKEZBFC:1606 桩；**AzimBridge 808 行 51 件
  零 sorry**（§2 主桥 ee/nn/ffOfHyp_p3 = hypermapOfFan 映射、§4 azimInFan/wedgeInFanGe
  渲染桥、§5 FAN 的 HYP 存在性、§6 localFan_data + LocalFan.of_localFan_p3 全真）。
- **ConformingAuto1-23（25,357 行）**：grep `arcV/perimeter/circular/lunar/polar/
  interiorAngle` **零命中**——该章是 conforming/wedge 词表，与 WSEWPCH 无共用件。
  邻族真件仅 CA7:543 `SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN`（node-和 2π，FAN 词表）。
  **任务假设"ConformingAuto 可能藏 WSEWPCH 相邻件"实测为否。**
- **PA 系**：PA25:10090/PA22:7562（2π 引擎，真）、PA18:6694 AZIM_BASE_SHIFT_LE（真，
  PA25 证明料）、PA7:574 ANGLE_SUM_BOUND（真）、PA3:163/PA25:7983（cc_azim/azim_mcell
  2π 和，真）。
- **"缺口其实树内已有（改名/换形即可）"清单**（本侦察核心增量，11 件）：
  ① ORDER_AZIM_SUM2Pi_0（LA7:498 ← PA25:10090）；② RHO_NODE1_INJECTIVE（LA7:427，HOL
  本身就是 MESON[IVS_RHO_IDD]，LA5:7578 真）；③ IVS_RHO_NODE1_IN_V（LA7:432，HOL=
  MESON[LOCAL_FAN_ITER_RHO_NODE_IN_V:LA5:1238 真, ITER_CARD_MINUS1_EQ_IVS_RN1:LA5:8026 真]）；
  ④ FAN_PERIMETER_INVARIANT_CARD_V（=INVARIANT+LOFA_IMP_CARD_FF_V_EQ:LA5:6041 真）；
  ⑤ CARD_IS_LEAST_CYCLE（LA6:831，前提单件真）；⑥ LOFA_IMP_ITER_RHO_NODE_ID2（LA6:728，
  主料 LOOP_SET_DETER_FIRTS_ELMS:LA5:4998/ITER_CYCLIC_ORBIT:LA10:355 真）；
  ⑦ LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V、⑧ ITER_IVS_RHO_IDD、⑨ ITER_RHO_IVS_IDD、
  ⑩ LOFA_IMP_ITER_IVS_RHO_NODE_ID（同 kit 换形）；⑪ LOCAL_FAN_NOT_EMPTY_FF/
  NOT_CARD_FF_GE_2（LA1.LocalFan 定义直接推）。
  前提是 W2 桥（LocalFan→_p2 迁移）落地——除 ①⑥⑪ 可直接在 LA7 世界独立证外，
  ②③④⑦⑧⑨⑩ 的"白拿"走桥。

## 3. 误植检查（零容忍，逐前提对照）

| 件 | Lean 前提 vs HOL | 结论 | 判定 |
|---|---|---|---|
| LA7:698 WSEWPCH | 1/1（ConvexLocalFan = convex_local_fan） | fanPerimeter ≤ 2π 一致 | **无误植** |
| LA7:662 BGMIFTE | 4/4（hcl/hg/hia/hp；hp 对称形式 = HOL (V',E',FF')=polar_fan） | 5 段逐字（prime' v = cross3 v (rhoNode1 FF v)，prime'(r v) = cross3 (r v) (r (r v))，π−interiorAngle1 双向，0<arc<π，CARD V'=CARD V） | **无误植** |
| LA7:694 FAN_PERIMETER | 1/1 | setSum V 形一致 | **无误植** |
| LA3:1881 CIZMRRH | 1/1（localFan_p3） | 三分 exclusive-or 三合取逐字 | **无误植** |
| LA5:5018 KCHMAMG | 2/2（convexLocalFan_p2 ∧ circular_p2） | 7 合取逐字（plane_p2/0∈A/V⊆A/∃e 正交/cyclicSet_p3/azimCycle=ρ/azim=dihV=arcV<π） | **无误植** |
| LA5:7986 HKIRPEP | 2/2 | 5 段逐字（i/j < CARD V、i,j∉{0,1}、半圆 image 集合等式） | **无误植** |
| TameLp:357 PerimeterBound | tame_defs.hl:295-297 逐字 | ∀f∈faceSetOfFan, setSum f (d↦arcV 0 d.1 d.2) ≤ 2π | **无误植** |
| **TameLp:10500 hcore（yk11 锚）** | **非逐字——有意换形** | 把 HOL 的 FAN_PERIMETER(:2184) + sum_face_rho_node1(:1509-1521) 折进锚内 | **合法换形，已文档化（DELIVERY §1/注释 :10488-10499），非漂移** |

hcore 换形的等价性论证（可复核）：对 local fan 的面 g，(α) HOL `face_eq_image_rho_node1`
（lp_main_estimate-compiled.hl:1502-1521）证 `f = IMAGE (v↦(v, rho_node1 f v)) (v_prime V f)`，
即 dart∈g ⟺ dart=(d.1, rho_node1 g d.1)；Lean 侧对应物 = LA5:6037 `LOFA_IMP_BIJ_FF_V`
（BijOn Prod.fst FF V，真证）+ LA5:875 `LOCAL_FAN_CHARACTER_OF_RHO_NODE`（真证）——
两件齐全，dart-和 = fanPerimeter 的换桥是**小件**（~100-150 行）而非缺口。
(β) `arcV 0 d.1 d.2` 的 0 = **根点/顶点 apex**（HOL `vec 0`；arcV u v w = arccos((v−u)·(w−u)/
(|v−u||w−u|))，角在第一变元处，Geom/LuneVolume.lean:30——即"在原点处 d.1 与 d.2 的张角"）；
`d.1`/`d.2` = dart 的 FST/SND（面轨道中相继两顶点）。三处语义全对齐。
(γ) 唯一已文档化偏差：LA1 的 azimInFan/wedgeInFanGe 用 `sigmaFan` 渲染 HOL 的
`azim_cycle`——AzimBridge §4（:§4，azimInFan_eq_azimInFan_p3 等）已给出 FAN 条件下
的桥（真证），LocalFan 蕴含 FAN，偏差闭合。

**结论：本核零误植**（对照本项目 CFFONNL/bank_TSKAJXYGXSA/OEHDBEN 三次教训：本次未发现
前提序漂移、量词漂移或词表错接；LA7 的 `_p7` 词表副本与 LA1 词表逐件核对同构）。

## 4. LA3/LA5/LA6/LA7 import 可达性实测

| 模块 | 闭包规模 | vs TameLp 闭包(129) | 撞名明细 | 判定 |
|---|---|---|---|---|
| LA7 | 71 | **子集**（差集={LA7}） | 1 枚：LOCAL_FAN_ORBIT_MAP_EXPLICIT ← LA2:1488（TameLp 不消费） | **可 import，加一行**；W2 顺带改名消根 |
| LA3 | — | 零撞名（142 导出名全查） | 无 | **可 import** |
| LA6 | — | 零撞名（121 导出名全查） | 无 | **可 import** |
| LA5 | — | 3 枚撞 PA18:3267/:4018/:5413 | AFF_GE_MONO_TRANS / CONDS_IN_CONV2 / FINITE_CARD1_IMP_SINGLETON | **不可 import**（AT 实录复核）；用 W2 桥消费其真证内容，或合并期统一改名 |

注：LA7 imports = {Geom.Aff, Geom.LuneVolume, Text.Fan, Text.LocalAuto1,
Text.PackingAuto5, Mathlib}，全部已在 TameLp 闭包；TameLp 无被 import 者（grep 全库零命中），
无环。**"本地复制带前缀"路线作废，全部走 import 或单枚改名。**

## 5. 桥链与 no-isolated 自动性（W2 可行性）

- AzimBridge:739 `LocalFan.of_localFan_p3` 需 `hno : dartsOfHyp_p3 E V = dart1OfFan V E`
  （无孤立顶点）。**在 yk10 面实例上 hno 自动**：yk10 面的局部扇
  (vPrime_p2 V f, ePrime_p2 (ESTD V) f, f) 满足 U = ⋃₀ E'——每个 dart (v,w) ∈ f ⊆
  dart1OfFan V (ESTD V) 落在边 {v,w} ∈ ESTD V 上（Fan.lean:86 `dart1OfFan = {d | {d.1,d.2} ∈ E}`），
  故 v ∈ ⋃ ePrime；反包含 trivial。孤立点只能来自 selfPairs 的 (v,v) 型 dart，面上没有。
- 正向打包 `localFan_p3.of_LocalFan` 的全部零件已真：localFan_data（AzimBridge:660，
  9 合取全数据）+ §2 三主桥 + `dih2k_p3_of_Dih2k`/`Dih2k_of_dih2k_p3`（:682/:710 双向）。
- p2↔p3：LA2:195 与 LA3:178 定义体逐字同构（本侦察 diff 实证，11 对词表 rfl）；
  AzimBridge §1 已有 _p4↔_p3 同配方先例。

## 6. 波次与工作量（详见 WAVES.md）

| 波 | 内容 | 行数区间 | 成功率 | 前置 | 立即 |
|---|---|---|---|---|---|
| W1 | LA7 纯几何 14 桩 | 280–520 | ~90% | 无 | **是** |
| W2 | p2↔p3 rfl 桥 + of_LocalFan 打包 | 180–350 | ~85% | 无 | **是** |
| W3 | LA6 轨道 6-8 件 + CIZMRRH | 350–650 | 75–85% | 无(可拆) | **是** |
| W4 | lunar 支（MONO_WITH_AZIM+HALP+HKIRPEP） | 400–750 | 70–80% | W1–W3 | 否 |
| W5a | SOL/NKEZBFC kit | 200–400 | ~80% | 无 | **是** |
| W5b | BGMIFTE | 700–1400 | 60–70% | W1,W2,W5a | 否 |
| W6 | foundation 换形 + KCHMAMG + WSEWPCH 装配 + dart-和桥 + TameLp:848 闭合 | 1160–2070（拆 3 小波） | 65–80% | W1–W5 | 否 |
| 合计 | | **~2570–4740（中位 ~3600）** | | | |

## 7. 消费面与在飞冲突

- 消费者：仅 TameLp `fully_surrounded_perimeter_bound`（:835-848，经 CRTTXAT 喂 MQMSMAB
  → tame_planar_hypermap）；grep NEEDS 全库无第二方。conforming-wall-scout.md:79 的
  "墙是三桥之一"注记已过时（ykit11 §1 修正：三桥中两桥半已免，单锚形）。
- 在飞车道文件所有权实测（lane_snapshots 近 14 波扫描）：poolc-edgefirst=PA18、
  pa2-rvfxzbu2=PA2/PA24、la16-jejtvgb=LA16+LA20/22/23/26/27/28+PA12、pa14=PA14、
  pa10=PA10——**无一触碰 LA1/2/3/5/6/7/AzimBridge/TameLp**。TameLp 上波（ykit11）已交付；
  LA7 自 09-19、LA6 自 09-19、LA3 自 10-09、LA5 自 10-13（车道自述"让出名额"）无在飞。
  **W1/W2/W3/W5a 全部立即可开**；唯 AzimBridge 若作为 W2 施工面，需编排者确认其无主状态
  （最后触碰 c3b2ea73 09-20"清零 3→0"）。

## 8. 立项时机

1. **现在立**：W1（LA7 纯几何，快赢，一枚文件纯追加）；W5a（LA2/LA9 SOL kit）；
   W3a（LA6 近机械件，CARD_IS_LEAST_CYCLE 打头）。
2. **次波**：W2（桥，决定"换形白拿"清单兑现率）；W3b（CIZMRRH）。
3. **W1–W3 后**：W4、W5b 并行（不同文件）；W6 收官三小波。
4. 合并期债务：LA5 三枚 PA18 撞名建议届时统一改名（非本核阻塞项）。

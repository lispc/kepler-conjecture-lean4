# PA24 私件 × PA20/公共层 重复件地图（只读侦察，2026-10-08 盘面）

> 侦察结论：PA24 共 81 个声明（60 private：59 个 p24_* + azim_eq_zero_of_collinearY + GRUTOTI1_concl_p24；21 公共）。
> **全仓撞名扫描：81 名与其余所有模块零同名**——将来公共化无撞名雷（含 PA20 新迁入的 MCELL_CELL_PARAMETERS_D_EXIST/MCELL_PARAM_D_UL）。
> PA24 只被 PackingConcl import；加 import PA15/PA18/PA20/PA23 均无环。
> A 级（逐字同形+可达，直接删换）5 件；B 级（同形但源私有/不可达）约 18 件。

## 1. import 可达性

**直接 import**：PA2、PA5、PA6、PA12、ConicCapVolume、Polytope、TopologyFan、Kepler.Geom.Azim、Kepler.Geom.LuneVolume、Mathlib。

**传递闭包（43 模块）**：Geom 全层 + Statement + PA2/5/6/7/8/10/11/12 + ConformingDefs/ConicCapVolume/Fan/Hypermap/PackingJGXZYGW + Planarity 系全部 + Polytope/TopologyFan。

**不可见**：PA13–PA25（除已列）、SphereKit、全部 LocalAuto*、TameLp。可见模块里的 private 件不可见。

## 2. A 级：逐字同形 + 公共 + 可达（可直接换用）

| PA24 私件 | 可达公共孪生 | 换用点 |
|---|---|---|
| p24_norm_sq_dot :311 | Kepler.Geom.Azim.norm_sq_eq_dot (Azim.lean:74) | 删 6 行；2 处调用改名 |
| p24_azim_sub_self :1474 | Planarity.azim_sub_self (Planarity.lean:2840, public) | 删 ~11 行；4 处 |
| p24_zeta_add :2008 | AzimLemmas.zOf_add (:25) | 3 处 |
| p24_zeta_smul :2034 | AzimLemmas.zOf_smul (:34) | 5 处 |
| GRUTOTI1_concl_p24 :3260 + _pub :3274 | PA2.GRUTOTI1_concl (PA2.lean:5368, public) | 删 ~28 行；PackingConcl:605 改引 PA2 名（p24 体即纯转发 shim） |

## 3. B 级

### 3a. 源可达但 private（方案=源侧去 private/上移 Geom 层）

| PA24 私件 | 孪生 | 方案 |
|---|---|---|
| p24_pythI :290、p24_hsmL :296 | PA12.p12_pythI :1148、p12_hsmL :1154 | PA12 去 private；省 ~10 行 |
| p24_collinear3_zero_sub :1455、p24_azimSubSpec :1465 | WedgeVolume :33/:43、CCV :81/:91、Planarity :2822/:2830（第 3/4 份克隆） | 归 Kepler.Geom.Azim 公共化，四处克隆全灭；省 ~20 行 |
| azim_eq_zero_of_collinearY :147 | CCV :132 (private)、PA15 :1416 (不可达) | 归 Geom；省 ~6 行 |
| wedgeSimple :158 (公共) | CCV.ccv_wedge_simple :139 (private；CCV 看不见 PA24) | 上移 Azim/WedgeVolume |
| p24_setSum_congr :951 | PA2.setSumCongr_p2 :5150 (private，junk 约定同构) | PA2 去 private → PA24/PA23:291/LocalAuto1:1447 三克隆皆灭 |
| p24_mem_affineSpan_triple :1283 | LuneVolume.mem_affineSpan_triple_of_eq :694 (private) | 公共化；省 ~23 行 |
| p24_finrank_span_pair_le_two :1306 | LuneVolume :656、SolidAngle :354 (private)；PA21 :3972 (不可达) | 公共化；省 ~9 行 |
| p24_affineSpan_triple_ne_top :1315 | LuneVolume.affineSpan_three_ne_top :667 | 同上；省 ~31 行 |
| p24_norm_sq_decomp :2058、p24_zeta_e3 :2050、p24_norm_e3 :2045 | WedgeVolume :370/:345/:363、CCV :251/:266、PA21 :3779 (自认 copy) | WedgeVolume 三件公共化；p24_norm_sq_decomp (7 用) 变 2 行推论；省 ~30 行 |
| p24_dotR :300、p24_finrank_ker_dot :317 | Polytope.dotRight :193 (private) | Polytope 公共化+抽 finrank 引理；省 ~43 行 |
| p24_affGt_subset_affGe :1653 | PlanarityNotCut :138、PlanarityAuto13 :161 (private)；PA23:3113、ConformingAuto11:140 (不可达)——全仓第 5 份 | 归 Kepler.Geom.Aff；省 ~7 行 |

### 3b. 源公共但不可达（方案=PA24 加 import，无环）

| PA24 私件 | 孪生 | 方案 |
|---|---|---|
| p24_azim_base_shift :877 | PA18.AZIM_BASE_SHIFT_LE :2171 (public，逐字同) | +import PA18；省 ~13 行 |
| p24_wedge_ge_split :890 | PA18.WEDGE_GE_SPLIT :2183 (public，逐字同) | 同上；**省 ~61 行（本文件最大单项）** |
| p24_hl_pair :265 | PA15.HL_2 :553 (public)；PA11.hlPair :97 (弱化版 C) | 方案 a：+import PA15；方案 b（优）：HL_2 下移公共层 |

### 3c. 双方皆私有（提升一份两处删）

| PA24 私件 | 私有孪生 | 方案 |
|---|---|---|
| p24_exists_azim_point :1203 | PA23.p23_exists_azim_point :355 (PA23:350 自认 kit 抄自 PA24) | 提升到 AzimLemmas；PA24 省 **~80 行** + PA23 ~30 行 |
| p24_coplanar_measure_null :1346 | PA23.p23 同款 :461 | 归 Geom.Coplanar；省 ~18 行 |
| p24_coplanar_affineSpan_triple :1364 | PA23 :479 | 同上；省 ~22 行 |
| coplanarAzimEq :1386 (公共) | PA23.p23_coplanarAzimEq :501 (private，:3983 自认 copy) | 提升后 PA23 删 |

## 4. PA20 撞名核对

零同名。p24_cellParamsD_spec (:994) vs PA17:93 cellParams_spec_p17 vs PA20:916/:936 是同一 epsilon-模式的三种投影，各保其形，无雷。

## 5. C/D 级（保留清单）

- 近 A 可改写：p24_affDim_voronoiList2 :372（PA6.VORONOI_LIST_AFF_DIM 实例化 i=1 两行推出，现 ~26 行）；p24_zeta_sub :2021（LuneVolume.zOf_sub :240 随 3a 批）。
- p24_hl_pair_lt_sqrt2 :1893、p24_elV_mem :1853（12 用，Mathlib 一行可得但 churn 大）、p24_REUHADY_extract :1907（11 用）等全仓无孪生——**保留**。
- p24_barV1 :727 是真证明，方向是将来下移回填 PA15.HL_LE_SQRT2_IMP_BARV_1 的 sorry，不是反向。
- p24_gltvhum3/p24_leaf_singleton/p24_voronoi_pair_split 非重复（PA6:1109/PA12:1677 上游已合成，第三子句形状不同）。
- p24_cc_exists/p24_radV_extract/p24_tri_data/p24_tri_gamma/p24_nondeg_azim_ne/p24_exists_mcell_not_flat 等全仓无孪生，保留。

## 6. dedup 波优先级建议

1. A 级五连（零风险，~90 行）
2. p24_wedge_ge_split + p24_azim_base_shift + import PA18（~75 行）
3. p24_exists_azim_point + coplanar 对提升 Geom 层（PA24 ~120 行 + PA23 ~100 行）
4. 平移桥三件套 + zeta/norm_sq 家族归一 WedgeVolume/Azim（跨 5 模块灭 ~10 份克隆）
5. PA2.setSumCongr_p2 一行公共化（三文件连带）
6. p24_hl_pair 随 HL_2 下移（连带 PA11、PA23 消费点）

风险提示：GRUTOTI1_concl_p24_pub 是 PackingConcl 装配具名接口，删除须同步改 PackingConcl:605 引用名；其余 A/B 项纯改名/纯删除，无陈述强度变化。

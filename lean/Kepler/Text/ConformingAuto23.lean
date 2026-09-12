/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 23
(Conforming.hl:14795-17029, the FINAL batch).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 23, Conforming.hl:14795-17029):
- `aff_gt_subset_dartset_leads_into_fan_union_aff_gt` (14795)
- `aff_gt_1_2_subset_aff_1_3111` (14865)
- `AFF_GT_1_3_SUBSET_AFF_GT_1_3` (14917)
- `lemma_connect_hypermap` (14956)
- `WGVWSKE` (16858)
- `CARD_EDGE_SET_FAN` (16921)
- `REP_CARD_EDGE_SET_FAN` (16959)
- `GGRLKHP` (17007)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings; same conventions as
batches 16-22):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  HOL `(real^3->bool)` ↔ `Set V3`; HOL darts
  `real^3#real^3#real^3#real^3` ↔ pair darts `V3 × V3` (the quadruple dart
  `(x,v,u,sigma_fan x V E v u)` contracts to the pair `(v,u)`; see the
  batch-21 header); HOL scalar multiple `t % p` ↔ `t • p`; HOL `t + t' % q`
  point arithmetic ↔ `+` in `V3`.
- FAN-witness arguments: `hypermapOfFan` (Kepler/Text/Fan.lean:1169) and the
  ConformingDefs predicate `conformingFan` (Kepler/Text/ConformingDefs.lean:184)
  need an explicit `FAN` witness, so each theorem mentioning them carries an
  extra explicit `(hfan : FAN x V E)`. This is the only deviation from the
  HOL signatures.
- `hypermap1_of_fanx (x,V,E)` ↦ `hypermapOfFan x V E hfan`;
  `face_set`/`edge_set`/`dart` ↦ `H.faceSet`/`H.edgeSet`/`H.darts`
  (Kepler/Text/Hypermap.lean:1002,1008,765); `d_fan(x,V,E)` ↦ `dartOfFan V E`
  (Kepler/Text/Fan.lean:90); `connected_hypermap` ↦ `Hypermap.Connected`
  (Kepler/Text/Hypermap.lean:1633); `planar_hypermap` ↦ `Hypermap.Planar`
  (Kepler/Text/Hypermap.lean:1053); `set_of_components` ↦
  `H.setOfComponents` (Kepler/Text/Hypermap.lean:1033); `comb_component` ↦
  `H.combComponent` (Kepler/Text/Hypermap.lean:917);
  `number_of_components` ↦ `H.numberOfComponents`
  (Kepler/Text/Hypermap.lean:1035); HOL `CARD e = 2` ↔ `e.ncard = 2`; HOL
  `&(CARD s)` (nonzero natural card as a real) ↔ `↑s.ncard : ℝ` / `↑s.card`.
- `aff_gt`/`aff_ge` ↦ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39,42);
  `segment [y,z]` ↔ `segment ℝ y z`; `(:real^3)` ↦ `(Set.univ : Set V3)`;
  `(:real^3) DIFF (UNIONS {aff_ge {x} {v}| v IN V})` ↦
  `(Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v}` (same convention
  as `connected_in_dartset_leads_into_fan_union_aff_gt`,
  Kepler/Text/ConformingAuto22.lean:381).
- HOL notions used by the HOL proofs but NOT ported that the pool proofs must
  work around: `hypermap_of_fan_rep`, `dartset_fully_surrounded_is_non_
  isolated_fan` (closest existing: `dartOfFan_eq_dart1_of_surrounded`,
  Kepler/Text/Fan.lean:1084), `remark1_fan` (fan.hl:423),
  `sigma_fan_in_set_of_edge`, the component lemmas `lemma_component_subset`/
  `lemma_component_identity`/`lemma_powers_in_component`/
  `lemma_face_subset_component`, `into_domain_power_efn_fan`,
  `plain_hypermap_fan`, `e_fan_no_fix_point`, `EDGE_FINITE`,
  `lemma_edge_identity`, `collinear1_fan`, `th3` (fan.hl:388; disjointness
  from non-collinearity), `imp_norm_gl_zero_fan`,
  `AZIM_EQ_0_PI_EQ_COPLANAR`, `AZIM_EQ_0_ALT`, `AFF_GT_SUBSET_AFF_GE`,
  `AFF_GT_1_1`/`AFF_GT_1_2`/`AFF_GT_1_3`/`AFF_GE_1_1` as named lemmas
  (member-form representatives exist, cf. Kepler/Text/PlanarityAuto8.lean:41
  and `affGe_singleton_pair_subset_affineSpan_auto3`,
  Kepler/Text/ConformingAuto3.lean:311). No new definition is introduced
  for any of them.
- None of the eight statements is Mathlib-general: each mentions the
  repo-specific `FAN`/`conformingFan`/`affGt`/`affGe`/`dartsetLeadsIntoFan`/
  `hypermapOfFan`/`dartOfFan`/`Hypermap` vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto22

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical
open MeasureTheory

/-! ## 线段逃逸引理与 aff_gt 的凸性拼接（Conforming.hl:14795-14947） -/

/-- HOL Conforming.hl :14795-14864 `aff_gt_subset_dartset_leads_into_fan_union_aff_gt`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds ds1 Z y z .
FAN(x,V,E)
/\ conforming_fan (x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ ds1 IN face_set(hypermap1_of_fanx (x,V,E))
/\ Z=(:real^3) DIFF (UNIONS {aff_ge {x} {v}| v IN V})
/\ y IN dartset_leads_into_fan x V E ds
/\ z IN dartset_leads_into_fan x V E ds1
/\ ~(x=y) /\ ~(x=z)
/\ segment[y,z] SUBSET Z
==> aff_gt {x} {y,z} SUBSET Z
```

编码说明：`Z = (:real^3) DIFF (UNIONS {…})` ↦
`(Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v}`（同
`connected_in_dartset_leads_into_fan_union_aff_gt` 的约定）；
`conforming_fan` ↦ `conformingFan x V E hfan`；`segment [y,z]` ↦
`segment ℝ y z`；`~(x=y) /\ ~(x=z)` ↦ 两条独立假设 `x ≠ y`、`x ≠ z`。

证明思路：HOL 先由 FAN 展开取 `x ∉ V`，用 `AFF_GT_1_2` 展开
`affGt {x} {y,z}` 的坐标参数 `t2 % y + t3 % z`（`t2,t3 > 0`）；任取
`t1 % x + t2' % v`（`v ∈ V`）型点拼出线段上的点 `v123`，由
`segment [y,z] ⊆ Z` 与 `Z` 的定义导出 `v123 ∈ aff_ge {x} {v}`；再用
`inv (t2+t3)` 的系数恒等式与 `REAL_LE_MUL`/`REAL_LE_INV` 验证
`v123` 的坐标非负，最后由 `y` 处的 LABEL_TAC 假设（`v123` 属于线段）
与 `v ∈ V` 使 `aff_ge {x} {v}` 整块被 `Z` 排除而收口。

候选已有引理：
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `affGe`（Kepler/Geom/Aff.lean:42）、`affGt`（Kepler/Geom/Aff.lean:39）
- `connected_in_dartset_leads_into_fan_union_aff_gt`
  （Kepler/Text/ConformingAuto22.lean:381，产出 `Z` 中线段的前置）
- 缺口：HOL `AFF_GT_1_2`/`AFF_GE_1_1` 未以该名移植（成员形式替代见
  Kepler/Text/PlanarityAuto8.lean:41、
  `affGe_singleton_pair_subset_affineSpan_auto3`，
  Kepler/Text/ConformingAuto3.lean:311） -/
theorem aff_gt_subset_dartset_leads_into_fan_union_aff_gt (x : V3) (V : Set V3)
    (E : Set (Set V3)) (ds ds1 : Set (V3 × V3)) (Z : Set V3) (y z : V3)
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds1 : ds1 ∈ (hypermapOfFan x V E hfan).faceSet)
    (hZ : Z = (Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v})
    (hy : y ∈ dartsetLeadsIntoFan x V E ds)
    (hz : z ∈ dartsetLeadsIntoFan x V E ds1)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hseg : segment ℝ y z ⊆ Z) :
    affGt ({x} : Set V3) {y, z} ⊆ Z := by
  sorry

/-- HOL Conforming.hl :14865-14914 `aff_gt_1_2_subset_aff_1_3111`

（名字中的 `1111` 是 HOL 自己的后缀，照抄。）

HOL 原文：
```
!x y z v u w:real^3.
~coplanar {x,v,u,w}
/\ y IN aff_gt {x} {v,u}
/\ z IN aff_gt {x} {v,w}
==> aff_gt {x} {y,z} SUBSET aff_gt {x} {v,u,w}
```

证明思路：HOL 由 `notcoplanar_imp_notcollinear_fan` 与 `th3`（未移植，
非共线 ⇒ 分离性）建立各点两两不同，`properties_of_collinear4_points_fan`
处理 `y`/`z` 分别落在过 `x,v` 的直线上的退化组合；再展开三个
`AFF_GT_1_2` 与目标 `AFF_GT_1_3` 的坐标参数，对
`t2''*(t1'%x+t2'%v+t3'%u)+t3''*(…)` 重新配系数
（`x`,`v`,`u`,`w` 系数分别取四组乘积和），正性由
`REAL_LT_MUL`/正数相加收口。

候选已有引理：
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_of_collinear4_points_fan`（Kepler/Text/Planarity.lean:3087）
- `affGt`（Kepler/Geom/Aff.lean:39）
- 缺口：HOL `th3`（fan.hl:388）、`AFF_GT_1_2`/`AFF_GT_1_3` 未以该名移植 -/
theorem aff_gt_1_2_subset_aff_1_3111 (x y z v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hy : y ∈ affGt ({x} : Set V3) {v, u})
    (hz : z ∈ affGt ({x} : Set V3) {v, w}) :
    affGt ({x} : Set V3) {y, z} ⊆ affGt ({x} : Set V3) {v, u, w} := by
  sorry

/-- HOL Conforming.hl :14917-14947 `AFF_GT_1_3_SUBSET_AFF_GT_1_3`

HOL 原文：
```
!x v u w:real^3 t:real.
~coplanar {x,v,u,w}/\ &0< t/\ t< &1
==> aff_gt {x} {v,u,(&1-t) %u+ t %w} SUBSET aff_gt {x} {v,u,w}
```

证明思路：HOL 由 `continuous_coplanar_fan`（在 `t` 处求值）得
`{x,v,u,(1-t)%u+t%w}` 仍不共面，配合
`notcoplanar_imp_notcollinear_fan`/`th3` 建立分离性；展开内外两个
`AFF_GT_1_3` 后按 `t3 + t4*(1-t)`、`t4*t` 重新配 `u`、`w` 的系数
（`x`,`v` 系数不变），和式恰好 `t1+t2+t3+t4`；正性由
`REAL_LT_MUL`（`0 < 1-t` 由 `t < 1`）收口。

候选已有引理：
- `continuous_coplanar_fan`（Kepler/Text/Planarity.lean:1142）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `affGt`（Kepler/Geom/Aff.lean:39）
- 缺口：HOL `th3`、`AFF_GT_1_3` 未以该名移植 -/
theorem AFF_GT_1_3_SUBSET_AFF_GT_1_3 (x v u w : V3) (t : ℝ)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (ht0 : 0 < t) (ht1 : t < 1) :
    affGt ({x} : Set V3) {v, u, (1 - t) • u + t • w} ⊆
      affGt ({x} : Set V3) {v, u, w} := by
  sorry

/-! ## 超图连通性（Conforming.hl:14956-17029） -/

/-- HOL Conforming.hl :14956-16852 `lemma_connect_hypermap`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) f1 f2.
FAN(x,V,E)
/\ conforming_fan (x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ f1 IN d_fan(x,V,E) /\ f2 IN d_fan(x,V,E)
==> ?D. D IN set_of_components(hypermap1_of_fanx (x,V,E))
/\ f1 IN D /\ f2 IN D
```

编码说明：`d_fan(x,V,E)` ↦ `dartOfFan V E`（Kepler/Text/Fan.lean:90；
配合 `dartOfFan_eq_dart1_of_surrounded`，Kepler/Text/Fan.lean:1084，
桥接到 `hypermapOfFan` 的 dart 集）；`set_of_components` ↦
`(hypermapOfFan x V E hfan).setOfComponents`；四元组 dart 折叠为二元组
（见文件头）。

证明思路（HOL 证明块约 1900 行，14967-16851；按 REWRITE/MRESA 簇采样）：
- 取面簇：`dartset_fully_surrounded_is_non_isolated_fan` +
  `hypermap_of_fan_rep` 后取 `ds = face H f1`、`ds1 = face H f2`，
  证 `ds,ds1 ∈ face_set`、`f1 ∈ ds`、`f2 ∈ ds1`（orbit 的 0 次幂），
  再取 `D = comb_component H f1`，用 `lemma_component_subset` 得
  `D ∈ set_of_components`、`f1 ∈ D`（14967-15022）。
- 连通段：`connected_in_dartset_leads_into_fan_union_aff_gt` 给出
  `y,z` 与 `Z` 中线段；定义 `TA = {t | 0 ≤ t ≤ 1 ∧ ∃ f ∈ D,
  (1-t)%y + t%z ∈ dartset_leads_into_fan x V E (face H f)}`，
  `t1 = sup TA`，证 `0 ∈ TA`、`TA` 有上界 `&1`（15023-15130；
  `SUP` 引理 + 二分 `t1 ∈ TA`与否，15131-15220）。
- `y = z` 分支与 `t1 = 1` 分支：反复用
  `dartset_leads_into_is_topological_component_yfan` +
  `CONNECTED_COMPONENT_EQ` 把不同的 `dartsetLeadsIntoFan` 块对应到
  `yfan` 的同一连通分量，再展开 `conforming_fan` 的
  `conforming_bijection_fan`（EXISTS_UNIQUE）得两块相等
  （15170-15320、16858-16918 一带同型）。
- `t1 < 1` 分支：`OPEN_TOPOLOGICAL_COMPONENT_YFAN` + 
  `imp_norm_gl_zero_fan`/`imp_norm_not_zero_fan` 在 `t1` 右侧取开球，
  球内点 `f'` 仍属 `D`（REMOVE_THEN "LINH/LINH1"）（15220-15360、
  15440-15490）；随后长段几何：`yfan_union_aff_gt_fan`、
  `aff_ge_eq_aff_gt_union_aff_ge`、`decomposition_planar_by_angle_fan`、
  `sum4/5_azim_fan`、`cross_dot_fully_surrounded_fan`、
  `condition_4point_aff_gt_1_2inter_aff_gt_1_2`、
  `aff_gt_1_3_eq_unions_aff_gt_1_2`、
  `aff_gt_1_3_subset_dart_leads_into_fan`、
  `AFF_GT_1_1_SUBSET_DARTSET_LEADS_INTO_FAN`、
  `scale_aff_gt_fan`/`scale_in_edges_fan`、
  `aff_gt_1_2_subset_aff_1_3111` + `AFF_GT_1_3_SUBSET_AFF_GT_1_3`
  （本批上文，16320-16540 一带）把 `(1-t')%…` 型点推入
  `dartset_leads_into_fan x V E (face H (x,v,w,σ v w))`。
- q.e.d. 组装（16780-16851）：由 `into_domain_power_efn_fan` +
  `INVERSE1_SIGMA_FAN` + `lemma_component_identity`/
  `lemma_powers_in_component` 证 `(x,w,v,σ w v) ∈ D`，把新点纳入
  `TA` 得 `t1 + (1-t1)*t''' ∈ TA`，与 `∀ a ∈ TA, a ≤ t1` 及
  `t1 ∉ TA`（此处分支）矛盾，`REAL_ARITH_TAC` 收口。

候选已有引理：
- `connected_in_dartset_leads_into_fan_union_aff_gt`
  （Kepler/Text/ConformingAuto22.lean:381）
- `AFF_GT_1_1_SUBSET_DARTSET_LEADS_INTO_FAN`
  （Kepler/Text/ConformingAuto22.lean:444）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）、`DARTSET_LEADS_INTO_FAN`
  （Kepler/Text/PlanarityComponent.lean:375）、
  `dartset_leads_into_subset_yfan`（Kepler/Text/PlanarityComponent.lean:583）
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN`（Kepler/Text/ConformingAuto6.lean:317）、
  `version_JUTSTKG`（Kepler/Text/ConformingAuto2.lean:114）、
  `yfan_union_aff_gt_fan`（Kepler/Text/ConformingAuto21.lean:1200）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）、
  `point_in_aff_ge_1_1`（Kepler/Text/PlanarityAuto13.lean:463）
- `exists_inf_element_fix_fan`（Kepler/Text/Planarity.lean:2608）、
  `imp_norm_not_zero_fan`（Kepler/Text/Planarity.lean:1306，private）、
  `exists_open_not_collinear`（Kepler/Text/Planarity.lean:125）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）、
  `not_collinear_is_properties_fully_surrounded`
  （Kepler/Text/Planarity.lean:2559）、
  `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）、
  `aff_gt2_subset_aff_ge`（Kepler/Text/Planarity.lean:3927）、
  `aff_ge1_subset_aff_ge`（Kepler/Text/Planarity.lean:4041）、
  `aff_gt3_subset_aff_gt`（Kepler/Text/Planarity.lean:4023）、
  `decomposition_planar_by_angle_fan`（Kepler/Text/Planarity.lean:4203）、
  `scale_aff_gt_fan`（Kepler/Text/Planarity.lean:759）、
  `properties_of_collinear4_points_fan`（Kepler/Text/Planarity.lean:3087）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）、
  `sum5_azim_fan`（Kepler/Text/TopologyFan.lean:1175）
- `condition_4point_aff_gt_1_2inter_aff_gt_1_2`
  （Kepler/Text/PlanarityAuto11.lean:272）、
  `aff_gt_1_2_cross_dotr_4point_neg`（Kepler/Text/PlanarityAuto10.lean:410）
- `aff_gt_1_3_eq_unions_aff_gt_1_2`（Kepler/Text/PlanarityAuto12.lean:117）、
  `aff_gt_1_3_subset_dart_leads_into_fan`
  （Kepler/Text/PlanarityAuto12.lean:270）、
  `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `scale_in_edges_fan`（Kepler/Text/PlanarityAngle.lean:1006）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）、
  `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）、
  `Hypermap.combComponent`/`setOfComponents`/`face`
  （Kepler/Text/Hypermap.lean:917,1033）、
  `Hypermap.Connected`（Kepler/Text/Hypermap.lean:1633）、
  `orbit_cyclic`（Kepler/Text/Hypermap.lean:1102）
- `aff_gt_1_2_subset_aff_1_3111`、`AFF_GT_1_3_SUBSET_AFF_GT_1_3`
  （本文件上文）
- 缺口：HOL `hypermap_of_fan_rep`、`dartset_fully_surrounded_is_non_
  isolated_fan`、`remark1_fan`、`sigma_fan_in_set_of_edge`、组件四引理
  （`lemma_component_*`）、`into_domain_power_efn_fan`、
  `collinear1_fan`、`th3`、`imp_norm_gl_zero_fan`、`AFF_GT_SUBSET_AFF_GE`
  未以该名移植 -/
theorem lemma_connect_hypermap (x : V3) (V : Set V3) (E : Set (Set V3))
    (f1 f2 : V3 × V3) (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hf1 : f1 ∈ dartOfFan V E) (hf2 : f2 ∈ dartOfFan V E) :
    ∃ D : Set (V3 × V3), D ∈ (hypermapOfFan x V E hfan).setOfComponents ∧
      f1 ∈ D ∧ f2 ∈ D := by
  sorry

/-- HOL Conforming.hl :16858-16918 `WGVWSKE`

HOL 原文：
```
!x V E.
         FAN (x,V,E) /\
         conforming_fan (x,V,E)
==> connected_hypermap(hypermap1_of_fanx (x,V,E))
```

编码说明：`connected_hypermap` ↦ `Hypermap.Connected`
（Kepler/Text/Hypermap.lean:1633，定义为
`numberOfComponents = 1`）。

证明思路：HOL 展开 `connected_hypermap`/`number_of_components` 后需证
分量集为单点集：由 FAN 取 `v ∈ V`，`exists_inf_element_fix_fan` +
`remark1_fan`（未移植）造 dart `f1 = (x,v,u,σ v u)`；取
`D = comb_component H f1` 得 `D ∈ set_of_components`；再对任意分量 `D'`
用 `lemma_connect_hypermap`（本文件上文）连 `f1` 与 `D'` 中任一 dart，
`lemma_component_identity` 得 `D' = D`，故分量集 `= {D}`，基数 `1`。

候选已有引理：
- `lemma_connect_hypermap`（本文件上文）
- `exists_inf_element_fix_fan`（Kepler/Text/Planarity.lean:2608）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Hypermap.Connected`/`setOfComponents`/`combComponent`
  （Kepler/Text/Hypermap.lean:1633,1033,917）
- 缺口：HOL `remark1_fan`、`lemma_component_identity`、
  `hypermap_of_fan_rep` 未以该名移植 -/
theorem WGVWSKE (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan) :
    (hypermapOfFan x V E hfan).Connected := by
  sorry

/-- HOL Conforming.hl :16921-16958 `CARD_EDGE_SET_FAN`

HOL 原文：
```
!x V E e.
         FAN (x,V,E)
/\ e IN edge_set (hypermap1_of_fanx (x,V,E))
/\ conforming_fan (x,V,E)
         ==> CARD e= 2
```

编码说明：`e IN edge_set H` ↦
`e ∈ (hypermapOfFan x V E hfan).edgeSet`；`CARD e = 2` ↦ `e.ncard = 2`。

证明思路：HOL 展开 `edge_set`/`set_of_orbits` 后 `e` 是某 dart `x'` 的
`e_fan`-轨道；`into_domain_power_efn_fan`（`SUC (SUC 0)` 次幂）+
`plain_hypermap_fan`（`e_fan^2 = I`）+ `orbit_cyclic` 把轨道归约为
`{x', e_fan x'}` 两点集；`e_fan_no_fix_point` 排除不动点使两点不同，
`CARD_2_FAN` 收口 `CARD e = 2`。

候选已有引理：
- `orbit_cyclic`（Kepler/Text/Hypermap.lean:1102）
- `CARD_2_FAN`（Kepler/Text/Planarity.lean:4975）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Hypermap.edgeSet`/`Plain`（Kepler/Text/Hypermap.lean:1002,1039）
- 缺口：HOL `into_domain_power_efn_fan`、`plain_hypermap_fan`、
  `e_fan_no_fix_point`、`hypermap_of_fan_rep` 未以该名移植 -/
theorem CARD_EDGE_SET_FAN (x : V3) (V : Set V3) (E : Set (Set V3))
    (e : Set (V3 × V3)) (hfan : FAN x V E)
    (he : e ∈ (hypermapOfFan x V E hfan).edgeSet)
    (hconf : conformingFan x V E hfan) :
    e.ncard = 2 := by
  sorry

/-- HOL Conforming.hl :16959-17006 `REP_CARD_EDGE_SET_FAN`

HOL 原文：
```
!x V E.
         FAN (x,V,E)
/\ conforming_fan (x,V,E)
         ==> &(CARD (edge_set (hypermap1_of_fanx (x,V,E)))) * &2= &(CARD (dart (hypermap1_of_fanx (x,V,E))))
```

编码说明：`&(CARD (edge_set H)) * &2` ↦
`((H.edgeSet.ncard : ℝ) * 2)`；`&(CARD (dart H))` ↦
`((H.darts.card : ℝ))`（`dart` = dart 集，Kepler/Text/Hypermap.lean:765
的 `darts : Finset`）。

证明思路：HOL 用 `DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET` 把 dart 集
写成 edge_set 的并；每个边集有限（`EDGE_FINITE`，未移植，可用
`Hypermap.edgeSet_finite` + 轨道有限）且不同边两两不交（公共 dart 由
`lemma_edge_identity` 推出两边相等）；再由 `CARD_EDGE_SET_FAN` 每边
基数为 `2`，套 `HAS_SIZE_UNIONS`（Mathlib 对应
`Set.Finite.biUnion`/`ncard_biUnion`）得并集基数 `= 2 * 边数`。

候选已有引理：
- `DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET`
  （Kepler/Text/ConformingAuto6.lean:768）
- `CARD_EDGE_SET_FAN`（本文件上文）
- `Hypermap.edgeSet_finite`/`setOfOrbits_finite`
  （Kepler/Text/Hypermap.lean:1010,981）
- `CARD_2_FAN`（Kepler/Text/Planarity.lean:4975）
- 缺口：HOL `EDGE_FINITE`、`lemma_edge_identity`、`HAS_SIZE_UNIONS`
  未以该名移植（Mathlib 侧用 `Set.ncard_biUnion` 替代） -/
theorem REP_CARD_EDGE_SET_FAN (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) :
    ((hypermapOfFan x V E hfan).edgeSet.ncard : ℝ) * (2 : ℝ) =
      ((hypermapOfFan x V E hfan).darts.card : ℝ) := by
  sorry

/-- HOL Conforming.hl :17007-17029 `GGRLKHP`

HOL 原文：
```
!x V E.
         FAN (x,V,E) /\ conforming_fan (x,V,E)
         ==> planar_hypermap (hypermap1_of_fanx (x,V,E))
```

编码说明：`planar_hypermap` ↦ `Hypermap.Planar`
（Kepler/Text/Hypermap.lean:1053，Euler 公式）。

证明思路：HOL 由 `SUM_CARD_FACE_NODE_DART_FAN`（面/节点基数和恒等式）
与 `REP_CARD_EDGE_SET_FAN`（本文件上文）改写 `A+B-C=D` 为
`A+B+C=D+2*C`，再套 `WGVWSKE`（本文件上文，连通 ⇒ 分量数 `1`）；
展开 `planar_hypermap`/`number_of_*` 后四则运算归约为
`N+E+F = D+2`（`REAL_OF_NUM_ADD`/`ARITH_RULE`）。

候选已有引理：
- `SUM_CARD_FACE_NODE_DART_FAN`（Kepler/Text/ConformingAuto8.lean:165）
- `REP_CARD_EDGE_SET_FAN`、`WGVWSKE`（本文件上文）
- `Hypermap.Planar`/`numberOfNodes`/`numberOfEdges`/`numberOfFaces`/
  `numberOfComponents`（Kepler/Text/Hypermap.lean:1053,1024-1035）
- `Hypermap.Connected`（Kepler/Text/Hypermap.lean:1633） -/
theorem GGRLKHP (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan) :
    (hypermapOfFan x V E hfan).Planar := by
  sorry

end Kepler.Text

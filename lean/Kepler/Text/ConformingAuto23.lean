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
  have hxV : x ∉ V := hfan.2.2.2.1
  have hdis : Disjoint ({x} : Set V3) {y, z} := by simp [hxy, hxz]
  intro p hp
  rw [aff_gt_1_2 hdis] at hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hpdef⟩ := hp
  rw [hZ]
  simp only [Set.mem_sdiff, Set.mem_univ, true_and]
  intro hu
  rcases Set.mem_iUnion₂.mp hu with ⟨v, hv, hpv⟩
  have hxv : x ≠ v := by
    intro he
    apply hxV
    rw [he]
    exact hv
  rw [mem_affGe_singleton hxv] at hpv
  obtain ⟨s1, s2, hs2, hssum, hpvdef⟩ := hpv
  have key : t1 • x + t2 • y + t3 • z = s1 • x + s2 • v := hpdef.symm.trans hpvdef
  have hs0 : t2 + t3 ≠ 0 := by linarith
  set u : ℝ := (t2 + t3)⁻¹ with hudef
  have hu0 : 0 < u := by rw [hudef]; exact inv_pos.mpr (by linarith)
  have huinv : u * (t2 + t3) = 1 := by rw [hudef]; exact inv_mul_cancel₀ hs0
  have hsc : s1 - t1 + s2 = t2 + t3 := by linarith
  have heq : t2 • y + t3 • z = (s1 - t1) • x + s2 • v := by
    calc t2 • y + t3 • z
        = (t1 • x + t2 • y + t3 • z) - t1 • x := by module
      _ = (s1 • x + s2 • v) - t1 • x := by rw [key]
      _ = (s1 - t1) • x + s2 • v := by rw [sub_smul]; module
  have h31 : u * t3 ≤ 1 := by
    have h : u * t3 ≤ u * (t2 + t3) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hu0)
    rwa [huinv] at h
  have hqseg : u • (t2 • y + t3 • z) ∈ segment ℝ y z := by
    rw [segment_eq_image]
    refine ⟨u * t3, ⟨mul_nonneg (le_of_lt hu0) (le_of_lt ht3), h31⟩, ?_⟩
    show (1 - u * t3) • y + (u * t3) • z = u • (t2 • y + t3 • z)
    rw [show (1 : ℝ) - u * t3 = u * t2 from by rw [← huinv]; ring]
    module
  have hqge : u • (t2 • y + t3 • z) ∈ affGe ({x} : Set V3) {v} := by
    rw [mem_affGe_singleton hxv]
    refine ⟨u * (s1 - t1), u * s2, mul_nonneg (le_of_lt hu0) hs2, ?_, ?_⟩
    · rw [← mul_add, hsc, huinv]
    · show u • (t2 • y + t3 • z) = (u * (s1 - t1)) • x + (u * s2) • v
      rw [heq]
      module
  have hZq : u • (t2 • y + t3 • z) ∈ Z := hseg hqseg
  rw [hZ] at hZq
  simp only [Set.mem_sdiff, Set.mem_univ, true_and] at hZq
  exact hZq (Set.mem_iUnion₂.mpr ⟨v, hv, hqge⟩)

/-! ### 辅助引理：affGt 成员点与 x 相异（由非共面性） -/

private theorem affineSpanSet_mem {s : Set V3} {p : V3} (hp : p ∈ s) :
    p ∈ (affineSpan ℝ s : Set V3) :=
  SetLike.mem_coe.mpr (mem_affineSpan ℝ hp)

private theorem affineSpanSet_mono {s t : Set V3} (hst : s ⊆ t) {p : V3}
    (hp : p ∈ (affineSpan ℝ s : Set V3)) : p ∈ (affineSpan ℝ t : Set V3) :=
  SetLike.mem_coe.mpr (affineSpan_mono ℝ hst (SetLike.mem_coe.mp hp))

/-- 四点 `{x,a,b,c}` 不共面时，`x` 不落在 `{a,b,c}` 中任意两点
`v,u` 所在的直线上（否则四点共面）。 -/
private theorem not_mem_line_of_notCoplanar {x v u a b c : V3}
    (hcop : ¬ Coplanar ({x, a, b, c} : Set V3))
    (hv : v ∈ ({a, b, c} : Set V3)) (hu : u ∈ ({a, b, c} : Set V3)) :
    x ∉ (affineSpan ℝ ({v, u} : Set V3) : Set V3) := by
  have hsub : ({v, u} : Set V3) ⊆ ({a, b, c} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hv
    · exact hu
  intro hmem
  refine hcop ⟨a, b, c, ?_⟩
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact affineSpanSet_mono hsub hmem
  · exact affineSpanSet_mem (by simp)
  · exact affineSpanSet_mem (by simp)
  · exact affineSpanSet_mem (by simp)

/-- 若 `p ∈ aff_gt {x} {v,u}`（即 `x ≠ v`、`x ≠ u`）且 `x` 不落在
过 `v,u` 的直线上，则 `x ≠ p`：否则 `x = p` 落在该直线上。
（HOL `th3`（fan.hl:388）+ `properties_of_collinear4_points_fan` 的
成员形式替代。） -/
private theorem ne_of_mem_affGt_of_not_on_line {x v u p : V3}
    (hxv : x ≠ v) (hxu : x ≠ u)
    (hp : p ∈ affGt ({x} : Set V3) ({v, u} : Set V3))
    (hnc : x ∉ (affineSpan ℝ ({v, u} : Set V3) : Set V3)) : x ≠ p := by
  rw [aff_gt_1_2 (x := x) (v := v) (w := u)
    (by simp [hxv, hxu])] at hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨a1, a2, a3, ha2, ha3, ha1sum, hpdef⟩ := hp
  intro he
  rw [← he] at hpdef
  have hab : a2 + a3 ≠ 0 := by linarith
  have h0' : x - a1 • x = a2 • v + a3 • u := by
    have key := congrArg (fun q => q - a1 • x) hpdef
    rw [key]
    module
  have h0 : (1 - a1) • x = a2 • v + a3 • u := by
    rw [← h0']
    module
  have h1 : (a2 + a3) • (x - v) = a3 • (u - v) := by
    have e : (1 : ℝ) - a1 = a2 + a3 := by linarith
    rw [← e, smul_sub, h0, e, add_smul, smul_sub]
    module
  have hxa : x - v = (a3 / (a2 + a3)) • (u - v) := by
    have h2 := congrArg (fun c => (a2 + a3)⁻¹ • c) h1
    rw [inv_smul_smul₀ hab, smul_smul] at h2
    rw [div_eq_inv_mul]
    exact h2
  have hxmem : x ∈ (affineSpan ℝ ({v, u} : Set V3) : Set V3) := by
    refine SetLike.mem_coe.mpr
      (mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨a3 / (a2 + a3), ?_⟩)
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hxa, sub_add_cancel]
  exact hnc hxmem

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
本证明：以成员形式引理 `aff_gt_1_2`、
`AFF_GT_1_3` 直接展开三组坐标参数，配系数后正性收口；互异性
（`x ≠ y`、`x ≠ z`）由辅助引理 `ne_of_mem_affGt_of_not_on_line`
与 `not_mem_line_of_notCoplanar` 给出。

候选已有引理：
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_of_collinear4_points_fan`（Kepler/Text/Planarity.lean:3087）
- `affGt`（Kepler/Geom/Aff.lean:39）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）、`AFF_GT_1_3`
  （Kepler/Text/PlanarityAuto11.lean:1029）
- `ne_of_mem_affGt_of_not_on_line`、`not_mem_line_of_notCoplanar`
  （本文件上文）
- 缺口：HOL `th3`（fan.hl:388）、`AFF_GT_1_2`/`AFF_GT_1_3` 未以该名移植 -/
theorem aff_gt_1_2_subset_aff_1_3111 (x y z v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hy : y ∈ affGt ({x} : Set V3) {v, u})
    (hz : z ∈ affGt ({x} : Set V3) {v, w}) :
    affGt ({x} : Set V3) {y, z} ⊆ affGt ({x} : Set V3) {v, u, w} := by
  obtain ⟨hxv, hxu, hxw, -, -, -⟩ := notcoplanar_disjoint x v u w hcop
  have hxline1 : x ∉ (affineSpan ℝ ({v, u} : Set V3) : Set V3) :=
    not_mem_line_of_notCoplanar hcop (by simp) (by simp)
  have hxline2 : x ∉ (affineSpan ℝ ({v, w} : Set V3) : Set V3) :=
    not_mem_line_of_notCoplanar hcop (by simp) (by simp)
  have hxy : x ≠ y := ne_of_mem_affGt_of_not_on_line hxv hxu hy hxline1
  have hxz : x ≠ z := ne_of_mem_affGt_of_not_on_line hxv hxw hz hxline2
  have hdis6 : Disjoint ({x} : Set V3) {v, u} := by simp [hxv, hxu]
  have hdisvw : Disjoint ({x} : Set V3) {v, w} := by simp [hxv, hxw]
  have hdisyz : Disjoint ({x} : Set V3) {y, z} := by simp [hxy, hxz]
  have hdis4 : Disjoint ({x} : Set V3) {v, u, w} := by simp [hxv, hxu, hxw]
  rw [aff_gt_1_2 hdis6] at hy
  rw [aff_gt_1_2 hdisvw] at hz
  simp only [Set.mem_setOf_eq] at hy hz
  obtain ⟨a1, a2, a3, ha2, ha3, ha1sum, hydef⟩ := hy
  obtain ⟨b1, b2, b3, hb2, hb3, hb1sum, hzdef⟩ := hz
  intro p hp
  rw [aff_gt_1_2 hdisyz] at hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨c1, c2, c3, hc2, hc3, hc1sum, hpdef⟩ := hp
  rw [AFF_GT_1_3 x v u w hdis4]
  simp only [Set.mem_setOf_eq]
  refine ⟨c1 + c2 * a1 + c3 * b1, c2 * a2 + c3 * b2, c2 * a3, c3 * b3, ?_, ?_, ?_, ?_, ?_⟩
  · have g1 : 0 < c2 * a2 := mul_pos hc2 ha2
    have g2 : 0 < c3 * b2 := mul_pos hc3 hb2
    linarith
  · exact mul_pos hc2 ha3
  · exact mul_pos hc3 hb3
  · have key : c2 * (a1 + a2 + a3) + c3 * (b1 + b2 + b3) =
        c2 * a1 + c3 * b1 + (c2 * a2 + c3 * b2) + (c2 * a3 + c3 * b3) := by ring
    rw [ha1sum, hb1sum] at key
    linarith
  · rw [hpdef, hydef, hzdef]
    module

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
本证明：点
`(1-t)%u+t%w` 属于 `aff_gt {x} {u,w}`（`Affsign.of_triple`），从而
`x ≠ (1-t)%u+t%w`（`ne_of_mem_affGt_of_not_on_line`）；内外两个
`AFF_GT_1_3` 成员形式展开后按 `t3 + t4*(1-t)`、`t4*t` 配系数收口。

候选已有引理：
- `continuous_coplanar_fan`（Kepler/Text/Planarity.lean:1142）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `affGt`（Kepler/Geom/Aff.lean:39）
- `AFF_GT_1_3`（Kepler/Text/PlanarityAuto11.lean:1029）、
  `Affsign.of_triple`（Kepler/Geom/Aff.lean:168）
- `ne_of_mem_affGt_of_not_on_line`、`not_mem_line_of_notCoplanar`
  （本文件上文）
- 缺口：HOL `th3`、`AFF_GT_1_3` 未以该名移植 -/
theorem AFF_GT_1_3_SUBSET_AFF_GT_1_3 (x v u w : V3) (t : ℝ)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (ht0 : 0 < t) (ht1 : t < 1) :
    affGt ({x} : Set V3) {v, u, (1 - t) • u + t • w} ⊆
      affGt ({x} : Set V3) {v, u, w} := by
  obtain ⟨hxv, hxu, hxw, -, -, huw⟩ := notcoplanar_disjoint x v u w hcop
  have hdis4 : Disjoint ({x} : Set V3) {v, u, w} := by simp [hxv, hxu, hxw]
  have hmem : (1 - t) • u + t • w ∈ affGt ({x} : Set V3) ({u, w} : Set V3) :=
    Affsign.of_triple (sgn := fun r => (0 : ℝ) < r) (1 - t) t
      (by linarith) ht0 (by module) hxu hxw huw
  have hxline : x ∉ (affineSpan ℝ ({u, w} : Set V3) : Set V3) :=
    not_mem_line_of_notCoplanar hcop (by simp) (by simp)
  have hxu' : x ≠ (1 - t) • u + t • w :=
    ne_of_mem_affGt_of_not_on_line hxu hxw hmem hxline
  have hdis' : Disjoint ({x} : Set V3) {v, u, (1 - t) • u + t • w} := by
    simp [hxv, hxu, hxu']
  intro p hp
  rw [AFF_GT_1_3 x v u ((1 - t) • u + t • w) hdis'] at hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨c1, c2, c3, c4, hc2, hc3, hc4, hc1sum, hpdef⟩ := hp
  rw [AFF_GT_1_3 x v u w hdis4]
  simp only [Set.mem_setOf_eq]
  refine ⟨c1, c2, c3 + c4 * (1 - t), c4 * t, hc2, ?_, ?_, ?_, ?_⟩
  · have g1 : 0 < c4 * (1 - t) := mul_pos hc4 (by linarith)
    linarith
  · exact mul_pos hc4 ht0
  · have e : c4 * (1 - t) + c4 * t = c4 := by ring
    linarith
  · rw [hpdef]
    module

/-! ## 超图连通性（Conforming.hl:14956-17029） -/

/-! ### W1 私有辅助引理（为 `lemma_connect_hypermap` 备料；均已证明） -/

/-- `hypermapOfFan` 的 dart 集就是 `dart1OfFan`（PlanarityComponent.lean:541-548 模式）。 -/
private theorem hypermapOfFan_darts_coe (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) :
    (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E := by
  change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
  exact (finite_dart1_fan hfan).coe_toFinset

/-- `setOfComponents` 的成员形式（Hypermap.lean:1029-1033 的展开 + `Set.mem_image`）。 -/
private theorem hypermapOfFan_mem_setOfComponents (H : Hypermap (V3 × V3)) {x : V3 × V3}
    (hx : x ∈ H.darts) : H.combComponent x ∈ H.setOfComponents := by
  have h : H.setOfComponents =
      (fun y : V3 × V3 => H.combComponent y) '' (↑H.darts : Set (V3 × V3)) := by
    ext t
    simp [Hypermap.setOfComponents, Hypermap.setPartComponents]
  rw [h]
  exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hx)

/-- `f1Fan` 与 `fFanPair` 在 `dart1OfFan` 上一致（ConformingAuto14:111 为 private，
此处本地副本，同 ConformingAuto18:671 的做法）。 -/
private theorem f1Fan_eq_fFanPair_of_dart1_ca23 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    f1Fan x V E d = fFanPair x V E d := by
  have hba : ({d.2, d.1} : Set V3) ∈ E := by
    have h : ({d.1, d.2} : Set V3) ∈ E := hd
    rwa [Set.pair_comm] at h
  simp only [f1Fan, fFanPair]
  rw [inverse_sigma_fan_eq_inverse1 hfan hba]

/-- `f1Fan` 的迭代保持 `dart1OfFan`（ConformingAuto14:324 为 private，本地副本）。 -/
private theorem f1Fan_iterate_mem_dart1OfFan_ca23 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    (f1Fan x V E)^[k] d ∈ dart1OfFan V E := by
  induction k with
  | zero => simpa using hd
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [f1Fan_eq_fFanPair_of_dart1_ca23 hfan ih]
      exact fFanPair_mem_dart1 hfan ih

/-- `hypermapOfFan` 的 `faceMap` 在 `dart1OfFan` 上等于 `f1Fan`（本地副本）。 -/
private theorem hypermapOfFan_faceMap_eq_f1Fan_ca23 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = f1Fan x V E d := by
  have hface : (hypermapOfFan x V E hfan).faceMap d = fFanPair x V E d := by
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [if_pos (by simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]
  rw [hface, f1Fan_eq_fFanPair_of_dart1_ca23 hfan hd]

/-- Auto14:344 `hypermapOfFan_faceMap_pow_eq_iterate`（彼处 private）的本地副本：
`faceMap` 的幂在 `dart1OfFan` 上等于 `f1Fan` 的迭代。 -/
private theorem hypermapOfFan_faceMap_iterate {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    ((hypermapOfFan x V E hfan).faceMap ^ k) d = (f1Fan x V E)^[k] d := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply']
      exact hypermapOfFan_faceMap_eq_f1Fan_ca23 hfan
        (f1Fan_iterate_mem_dart1OfFan_ca23 hfan hd k)

/-- HOL fan.hl:423 `remark1_fan` 的互异性分量（`edge_ne_of_fan` + `fan_not_collinear`
经 `Collinear3` 自反性收口）。 -/
private theorem edge_distinct_of_mem {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (he : {v, u} ∈ E) : v ≠ u ∧ x ≠ v ∧ x ≠ u := by
  have h1 : v ≠ u := edge_ne_of_fan hfan he
  have h2 : x ≠ v := by
    intro hex
    exact fan_not_collinear hfan he (collinear3_of_eq hex.symm)
  have h3 : x ≠ u := by
    intro hex
    apply fan_not_collinear hfan he
    rw [hex]
    exact (collinear3_iff_smul h1).mpr ⟨0, by simp⟩
  exact ⟨h1, h2, h3⟩

/-- HOL fan.hl:388 `th3` 的替代：三点不共线给出两两互异（`Collinear3` 的
`collinear3_iff_smul` 特征 + 自反情形）。 -/
private theorem ne_of_not_collinear3 {x a b : V3} (h : ¬ Collinear3 x a b) :
    x ≠ a ∧ x ≠ b ∧ a ≠ b := by
  have h1 : x ≠ a := fun he => h (collinear3_of_eq he.symm)
  have h3 : a ≠ b := by
    intro he
    apply h
    exact (collinear3_iff_smul (Ne.symm h1)).mpr ⟨1, by rw [he]; simp⟩
  have h2 : x ≠ b := by
    intro he
    apply h
    rw [he]
    exact (collinear3_iff_smul h3).mpr ⟨0, by simp⟩
  exact ⟨h1, h2, h3⟩

/-- HOL `imp_norm_not_zero_fan`（planarity.hl；Planarity.lean:1305 的同名引理为
private，不可跨文件引用，故复制）。 -/
private theorem imp_norm_not_zero_fan {a b : V3} (h : a ≠ b) : ‖b - a‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm h))

/-- HOL `collinear1_fan`（fan.hl:392）在 Conforming.hl:15416-15440 使用形态的替代。
与 HOL 的差异（delta）：HOL 中 `~(y ∈ aff {x,z})` 的矛盾来自
`dartsetLeadsIntoFan` 的开区域性（`y1` 避开有限个平面的选取），且 `v1 = x` 情形由
系数分析（`v' = &0` 分支）排除；此处将非共线性作为显式假设 `hnc`、并显式要求
`v1 ≠ x`。`x ≠ y` 由 `yfan = univ \ xfan` 与 `x_in_xfan` 导出（即
`point_in_yfan_not_x_fan` 的非拓扑分量弱化版）。 -/
private theorem not_collinear3_of_segment_inter_ray {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hne : E ≠ ∅) {w y z v1 : V3}
    (hy : y ∈ yfan x V E) (hyz : y ≠ z) (hxw : x ≠ w) (hnc : ¬ Collinear3 x w y)
    (hv1seg : v1 ∈ segment ℝ y z)
    (hv1ray : v1 ∈ affGe ({x} : Set V3) ({w} : Set V3))
    (hv1x : v1 ≠ x) : ¬ Collinear3 x y z := by
  have hxy : x ≠ y := by
    intro hexc
    rw [yfan, Set.mem_sdiff] at hy
    exact hy.2 (hexc ▸ x_in_xfan hfan hne)
  intro hcol
  obtain ⟨c0, hc0⟩ := (collinear3_iff_smul (Ne.symm hxy)).mp hcol
  obtain ⟨a, b, ha, hb, hab, hv1⟩ := hv1seg
  have expand : ∀ s t : ℝ, ∀ p q r : V3,
      s • p + t • q - r = s • (p - r) + t • (q - r) + (s + t - 1) • r := by
    intro s t p q r
    module
  have hv1' : v1 - x = (a + b * c0) • (y - x) := by
    rw [← hv1, expand, hc0, hab]
    module
  obtain ⟨t1, t2, ht2pos, ht12, hv1w⟩ := (mem_affGe_singleton hxw).mp hv1ray
  have hv1w' : v1 - x = t2 • (w - x) := by
    rw [hv1w, expand, ht12]
    module
  have hne0 : v1 - x ≠ 0 := sub_ne_zero.mpr hv1x
  have ht2ne : t2 ≠ 0 := by
    intro he
    apply hne0
    rw [hv1w', he, zero_smul]
  have hwx : ∃ c : ℝ, w - x = c • (y - x) := by
    refine ⟨(a + b * c0) / t2, ?_⟩
    have h1 : t2 • (w - x) = t2 • (((a + b * c0) / t2) • (y - x)) := by
      rw [smul_smul, mul_div_cancel₀ _ ht2ne, ← hv1w', hv1']
    have h2 : t2 • ((w - x) - ((a + b * c0) / t2) • (y - x)) = (0 : V3) := by
      rw [smul_sub, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ht2ne
    · exact sub_eq_zero.mp h3
  have hperm : Collinear3 x y w → Collinear3 x w y := by
    intro hcperm
    have hc1 : Collinear ℝ ({x, y, w} : Set V3) := hcperm
    have hset : ({x, y, w} : Set V3) = {x, w, y} := by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hc2 : Collinear ℝ ({x, w, y} : Set V3) := hset ▸ hc1
    exact hc2
  exact hnc (hperm ((collinear3_iff_smul (Ne.symm hxy)).mpr hwx))

/-- HOL `AFF_GT_1_1` 的成员形式。注意本仓编码中 `affGt` 的符号约束在第二个集合上，
故可证的成员是 `v`-侧（系数 `1`）；`x ∈ affGt {x} {v}` 在该编码下不成立（缺口已在
文件头记录）。 -/
private theorem mem_affGt_1_1 {x v : V3} (hxv : x ≠ v) :
    v ∈ affGt ({x} : Set V3) ({v} : Set V3) := by
  have hfin : ({x} ∪ {v} : Set V3).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton v)
  have hset : hfin.toFinset = ({x, v} : Finset V3) := by
    apply Finset.ext
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  simp only [affGt, Set.mem_setOf_eq, Affsign]
  refine ⟨fun q => if q = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [hset]
    simp only [Finset.sum_insert (Finset.mem_singleton.not.mpr hxv), Finset.sum_singleton, if_neg hxv,
      eq_self_iff_true, if_true]
    module
  · intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    simp
  · rw [hset]
    simp only [Finset.sum_insert (Finset.mem_singleton.not.mpr hxv), Finset.sum_singleton, if_neg hxv,
      eq_self_iff_true, if_true]
    ring

/-- `hypermapOfFan` 的 `edgeMap` 在 `dart1OfFan` 上等于 `eFanPair`（本文件
`hypermapOfFan_faceMap_eq_f1Fan_ca23` 的 e-版本）。 -/
private theorem hypermapOfFan_edgeMap_eq_eFanPair_ca23 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).edgeMap d = eFanPair V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-! ### W5：下方 cluster（`azim x v1 v y ∈ (0,π)` 侧），为 `connect_geom_aux` 备料 -/

/-- W5 备料：混合积轮换 `(a × b) · c = (c × a) · b`。 -/
private theorem connect_below_cyclic {a b c : Fin 3 → ℝ} :
    (crossProduct a b) ⬝ᵥ c = (crossProduct c a) ⬝ᵥ b := by
  calc (crossProduct a b) ⬝ᵥ c = c ⬝ᵥ crossProduct a b := dotProduct_comm _ _
    _ = a ⬝ᵥ crossProduct b c := triple_product_permutation c a b
    _ = b ⬝ᵥ crossProduct c a := triple_product_permutation a b c
    _ = (crossProduct c a) ⬝ᵥ b := dotProduct_comm _ _

/-- W5 备料：末两个向量交换时混合积变号。 -/
private theorem connect_below_swap_dot {a b c : Fin 3 → ℝ} :
    (crossProduct a c) ⬝ᵥ b = -((crossProduct a b) ⬝ᵥ c) := by
  rw [← cross_anticomm c a, neg_dotProduct, connect_below_cyclic (a := c) (b := a) (c := b),
    connect_below_cyclic (a := b) (b := c) (c := a)]

/-- W5 备料：两向量差的组合为零且首系数非零给出三点共线。 -/
private theorem connect_below_collinear_of_smul {x p q : V3} {b1 b2 : ℝ} (hb1 : b1 ≠ 0)
    (h : b1 • (p - x) + b2 • (q - x) = (0 : V3)) : Collinear3 x p q := by
  rcases eq_or_ne p x with rfl | hpx
  · exact collinear3_of_eq rfl
  rcases eq_or_ne b2 0 with rfl | hb2
  · have h1 : b1 • (p - x) = 0 := by simpa using h
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hb1
    · exact absurd (sub_eq_zero.mp h2) hpx
  · refine (collinear3_iff_smul (v := x) (w := p) (w1 := q) hpx).mpr
      ⟨-(b1 / b2), ?_⟩
    have h4 : b2 • ((q - x) + (b1 / b2) • (p - x)) = (0 : V3) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ hb2,
        add_comm (b2 • (q - x)) (b1 • (p - x)), ← h]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 hb2
    · rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h5

/-- W5 备料：`a • u = d • p`、`a ≠ 0` 给出方向重参数化。 -/
private theorem connect_below_smul_div {u p : V3} {a d : ℝ} (ha : a ≠ 0)
    (h : a • u = d • p) : ∃ κ : ℝ, u = κ • p := by
  refine ⟨d / a, ?_⟩
  have h2 : a • (u - (d / a) • p) = (0 : V3) := by
    rw [smul_sub, h, smul_smul, mul_div_cancel₀ _ ha, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 ha
  · exact sub_eq_zero.mp h3

/-- W5 备料：闭锥组合点属于 `xfan`（边 `{v,w}` 的锥盖住从 `x` 出发的
非负组合方向）。 -/
private theorem connect_below_cone_xfan {x v w u : V3} {V : Set V3} {E : Set (Set V3)}
    (hvw : ({v, w} : Set V3) ∈ E) (hxv : x ≠ v) (hxw : x ≠ w) (hvwne : v ≠ w)
    {e2 e3 : ℝ} (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hueq : u - x = e2 • (v - x) + e3 • (w - x)) :
    u ∈ xfan x V E := by
  refine ⟨({v, w} : Set V3), hvw, ?_⟩
  simp only [affGe, Set.mem_setOf_eq]
  refine Affsign.of_triple (sgn := fun r => (0 : ℝ) ≤ r) e2 e3 he2 he3 ?_ hxv hxw hvwne
  have h2 : u = x + (e2 • (v - x) + e3 • (w - x)) := by rw [← hueq]; module
  rw [h2]; module

/-- W5：下方 cluster——`azim x v1 v y ∈ (0,π)` 时 `v1` 朝 `y` 一侧的线段点落入
`face (w, v)`（经 dart `(v, inverse1SigmaFan x V E v w)`）的引导块。
HOL Conforming.hl:15717-16300 下方 cluster 的打包；非共线性由锥论证
（`connect_below_cone_xfan` + `y ∈ yfan`/`z ∈ yfan`）而非 `collinear1_fan`。 -/
private theorem connect_geom_below (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    (hcard : ∀ u : V3, u ∈ V → 1 < (setOfEdge u V E).ncard) (hfan80 : fan80 x V E)
    (heE : E ≠ ∅) {y z v1 w v : V3} {t1 : ℝ}
    (hv : v ∈ V) (hw : w ∈ V) (hvw : ({v, w} : Set V3) ∈ E) (hyz : y ≠ z)
    (hy : y ∈ yfan x V E) (hz : z ∈ yfan x V E)
    (hv1t : v1 = (1 - t1) • y + t1 • z) (ht1pos : 0 < t1) (ht1lt : t1 < 1)
    (hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (1 - s) • y + s • z ∈ (Set.univ : Set V3) \ ⋃ v' ∈ V, affGe ({x} : Set V3) {v'})
    (hv1 : v1 ∈ affGt ({x} : Set V3) ({v, w} : Set V3))
    (hazim : azim x v1 v y ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s ≤ δ → s ≤ t1 →
      (1 - (t1 - s)) • y + (t1 - s) • z ∈
        dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (w, v)) := by
  -- ## 基础层：互异性与 σ-预备
  obtain ⟨hvwn, hxvn, hxwn⟩ := edge_distinct_of_mem hfan hvw
  have hvwSwap : ({w, v} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hvw
  have hvwn_col : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  have hxy : x ≠ y := by
    intro he
    rw [yfan, Set.mem_sdiff] at hy
    exact hy.2 (he ▸ x_in_xfan hfan heE)
  obtain ⟨u123, hu123edge, hu123sig, hu123def⟩ :
      ∃ g : V3, ({v, g} : Set V3) ∈ E ∧ sigmaFan x V E v g = w ∧
        g = inverse1SigmaFan x V E v w :=
    ⟨_, (INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := v) hfan).1 w hvw,
      (INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := v) hfan).2.1 w hvw, rfl⟩
  have hvu123_col : ¬ Collinear3 x v u123 := fan_not_collinear hfan hu123edge
  obtain ⟨hθ0, hθπ⟩ := hfan80 v u123 hu123edge
  rw [hu123sig] at hθ0 hθπ
  -- ## v1 的锥分解（aff_gt_1_2 形式）
  have hv1dis : Disjoint ({x} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxvn, hxwn⟩
  have hv1mem := hv1
  rw [aff_gt_1_2 hv1dis] at hv1
  simp only [Set.mem_setOf_eq] at hv1
  obtain ⟨a1, a2, a3, ha2, ha3, hsum, hv1eq⟩ := hv1
  have hsum1 : a1 = 1 - a2 - a3 := by linarith
  have hrep : v1 - x = a2 • (v - x) + a3 • (w - x) := by
    rw [hv1eq, hsum1]; module
  have hv1x : v1 ≠ x := by
    intro he
    refine hvwn_col ?_
    rw [he, sub_self] at hrep
    exact connect_below_collinear_of_smul (b1 := a2) (ne_of_gt ha2) hrep.symm
  -- ## 非共线束（锥论证 + yfan/xfan 互斥）
  have hcol_xyz : ¬ Collinear3 x y z := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := x) (w := y) (w1 := z) (Ne.symm hxy)).mp hcol
    have hstep : v1 - x = (1 - t1) • (y - x) + t1 • (z - x) := by rw [hv1t]; module
    have hv1k : v1 - x = (1 - t1 + t1 * c) • (y - x) := by rw [hstep, hc]; module
    have hk0 : (1 - t1 + t1 * c) ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hv1k
      exact hv1x (sub_eq_zero.mp hv1k)
    by_cases hkpos : (0:ℝ) < 1 - t1 + t1 * c
    · have hk' : y - x = (1 - t1 + t1 * c)⁻¹ • (v1 - x) := by
        rw [hv1k, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      have hmu : y - x = ((1 - t1 + t1 * c)⁻¹ * a2) • (v - x) +
          ((1 - t1 + t1 * c)⁻¹ * a3) • (w - x) := by rw [hk', hrep]; module
      rw [yfan, Set.mem_sdiff] at hy
      exact hy.2 (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (mul_nonneg (inv_nonneg.mpr hkpos.le) ha2.le)
        (mul_nonneg (inv_nonneg.mpr hkpos.le) ha3.le) hmu)
    · have hk0le : (1 - t1 + t1 * c) ≤ 0 := not_lt.mp hkpos
      have h2 : t1 * c < 0 := by
        have h1 : t1 * c = (1 - t1 + t1 * c) - (1 - t1) := by ring
        rw [h1]; linarith
      by_cases hcle : (0:ℝ) ≤ c
      · exact absurd (mul_nonneg (le_of_lt ht1pos) hcle) (not_le.mpr h2)
      · have hcneg : c < 0 := lt_of_not_ge hcle
        have hkinv : (1 - t1 + t1 * c)⁻¹ ≤ 0 := inv_nonpos'.mpr hk0le
        have hk' : y - x = (1 - t1 + t1 * c)⁻¹ • (v1 - x) := by
          rw [hv1k, smul_smul, inv_mul_cancel₀ hk0, one_smul]
        have hmu : z - x = (c * (1 - t1 + t1 * c)⁻¹ * a2) • (v - x) +
            (c * (1 - t1 + t1 * c)⁻¹ * a3) • (w - x) := by
          rw [hc, hk', hrep]; module
        rw [yfan, Set.mem_sdiff] at hz
        have hcoef : (0:ℝ) ≤ c * (1 - t1 + t1 * c)⁻¹ := by
          have h1 := mul_nonneg (neg_nonneg.mpr hcneg.le) (neg_nonneg.mpr hkinv)
          ring_nf at h1 ⊢
          exact h1
        exact hz.2 (connect_below_cone_xfan hvw hxvn hxwn hvwn
          (e2 := c * (1 - t1 + t1 * c)⁻¹ * a2) (e3 := c * (1 - t1 + t1 * c)⁻¹ * a3)
          (mul_nonneg hcoef ha2.le) (mul_nonneg hcoef ha3.le) hmu)
  have hv1nc : ¬ Collinear3 x v1 y := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := x) (w := v1) (w1 := y) hv1x).mp hcol
    by_cases hcle : (0:ℝ) ≤ c
    · have hmu : y - x = (c * a2) • (v - x) + (c * a3) • (w - x) := by rw [hc, hrep]; module
      rw [yfan, Set.mem_sdiff] at hy
      exact hy.2 (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (mul_nonneg hcle ha2.le) (mul_nonneg hcle ha3.le) hmu)
    · have hclt : c < 0 := lt_of_not_ge hcle
      have hstep : v1 - x = (1 - t1) • (y - x) + t1 • (z - x) := by rw [hv1t]; module
      have h0 : t1 • (z - x) = v1 - x - (1 - t1) • (y - x) := by rw [hstep]; module
      have h1 : t1 • (z - x) = (1 - (1 - t1) * c) • (v1 - x) := by rw [h0, hc]; module
      have hz' : z - x = ((1 - (1 - t1) * c) / t1) • (v1 - x) := by
        have h2 : t1 • (z - x - ((1 - (1 - t1) * c) / t1) • (v1 - x)) = (0 : V3) := by
          rw [smul_sub, h1, smul_smul, mul_div_cancel₀ _ ht1pos.ne', sub_self]
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 ht1pos.ne'
        · exact sub_eq_zero.mp h3
      have hmu : z - x = (((1 - (1 - t1) * c) / t1) * a2) • (v - x) +
          (((1 - (1 - t1) * c) / t1) * a3) • (w - x) := by rw [hz', hrep]; module
      rw [yfan, Set.mem_sdiff] at hz
      have hsign : (0:ℝ) ≤ 1 - (1 - t1) * c := by
        have hm : (0:ℝ) ≤ (1 - t1) * (-c) := mul_nonneg (by linarith) (neg_nonneg.mpr hclt.le)
        have hm2 : (1 - t1) * c = -((1 - t1) * (-c)) := by ring
        linarith
      exact hz.2 (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (e2 := ((1 - (1 - t1) * c) / t1) * a2) (e3 := ((1 - (1 - t1) * c) / t1) * a3)
        (mul_nonneg (div_nonneg hsign ht1pos.le) ha2.le)
        (mul_nonneg (div_nonneg hsign ht1pos.le) ha3.le) hmu)
  have hv1v_col : ¬ Collinear3 x v1 v := by
    intro hcol
    obtain ⟨μ, hμ⟩ := (collinear3_iff_smul (v := x) (w := v1) (w1 := v) hv1x).mp hcol
    rcases eq_or_ne μ 0 with rfl | hμ0
    · rw [zero_smul, sub_eq_zero] at hμ
      exact hxvn hμ.symm
    · refine hvwn_col ?_
      have h6 : v1 - x = μ⁻¹ • (v - x) := by rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      have h7a : a3 • (w - x) = v1 - x - a2 • (v - x) := by rw [hrep]; module
      have h7 : a3 • (w - x) = (μ⁻¹ - a2) • (v - x) := by rw [h7a, h6]; module
      obtain ⟨κ, hκ⟩ := connect_below_smul_div (a := a3) (d := μ⁻¹ - a2) (ne_of_gt ha3) h7
      exact (collinear3_iff_smul (v := x) (w := v) (w1 := w) (Ne.symm hxvn)).mpr ⟨κ, hκ⟩
  -- ## 符号层
  have hsign1 : 0 < (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u123 - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := v) (v := u123) (u1 := w)
      hvwn_col hvu123_col hθ0 hθπ
  have hsignCone : 0 < (crossProduct ((w - x : V3) : Fin 3 → ℝ)
      ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((u123 - x : V3) : Fin 3 → ℝ) := by
    rw [connect_below_cyclic, connect_below_cyclic]; exact hsign1
  have hsign2 : 0 < (crossProduct ((v1 - x : V3) : Fin 3 → ℝ)
      ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := v1) (v := v) (u1 := y)
      hv1nc hv1v_col hazim.1 hazim.2
  have hneg : 0 < -((crossProduct ((v1 - x : V3) : Fin 3 → ℝ)
      ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) := by
    rw [← connect_below_swap_dot]; exact hsign2
  have hsign4 : 0 < (crossProduct ((v1 - x : V3) : Fin 3 → ℝ)
      ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) :=
    aff_gt_1_2_cross_dotr_4point_neg x v1 y v w hvwn_col hv1mem hneg
  have hsignWedge : 0 < (crossProduct ((w - x : V3) : Fin 3 → ℝ)
      ((v1 - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) := by
    rw [connect_below_cyclic, connect_below_cyclic]; exact hsign4
  -- ## condition_4point：楔形内的交点
  have hv1mem' : v1 ∈ affGt ({x} : Set V3) ({w, v} : Set V3) := by
    rw [Set.pair_comm]; exact hv1mem
  have hncwv : ¬ Collinear3 x w v := by
    intro hc
    refine hvwn_col ?_
    have h2 : Collinear ℝ ({x, w, v} : Set V3) := hc
    have h3 : ({x, w, v} : Set V3) = ({x, v, w} : Set V3) := by ext q; simp; tauto
    rw [h3] at h2
    exact h2
  have hNCline' : ∀ h : ℝ, 0 < h → h < 1 / 2 →
      ¬ Collinear3 x w ((1 - h) • v + h • u123) := fun h hh0 hh =>
    not_collinear_is_properties_fully_surrounded1 hfan hvwSwap hu123edge hθ0 hθπ h
      (le_of_lt hh0) (le_trans (le_of_lt hh) (by norm_num))
  obtain ⟨t4, ht40, ht41, hAP⟩ := condition_4point_aff_gt_1_2inter_aff_gt_1_2
    x v1 y w v u123 (1 / 2) hncwv hvu123_col hv1nc (by norm_num) (by norm_num) hv1mem'
    hsignCone hNCline' hsignWedge
  obtain ⟨ap, hap⟩ := Set.nonempty_iff_ne_empty.mpr (hAP (t4 / 2) (by linarith) (by linarith))
  obtain ⟨hap1, hap2⟩ := hap
  -- ## a-点沿射线 x→ap 缩回线段 (v1, y)：点 b
  have hdisap : Disjoint ({x} : Set V3) ({v1, y} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hv1x, hxy⟩
  obtain ⟨a', t', ha'0, ht'0, ht'1, hscale⟩ := scale_in_edges_fan hdisap hap1
  set b : V3 := (1 - t') • v1 + t' • y with hbdef
  set c : V3 := (1 - t4 / 2) • v + (t4 / 2) • u123 with hcdef
  have hxc : x ≠ c := by
    intro he
    refine hvu123_col ?_
    have h2 : (0:V3) = (1 - t4 / 2) • (v - x) + (t4 / 2) • (u123 - x) := by
      rw [he, hcdef]; module
    exact connect_below_collinear_of_smul (b1 := 1 - t4 / 2) (by linarith) h2.symm
  have hdisc : Disjoint ({x} : Set V3) ({w, c} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxwn, hxc⟩
  have hbmem : b ∈ affGt ({x} : Set V3) ({w, c} : Set V3) := by
    have h := scale_aff_gt_fan (x := x) (v := w) (u := c) hdisc ap a' hap2 ha'0
    have h2 : b = a' • (ap - x) + x := by rw [hbdef, hscale]; module
    rw [h2]; exact h
  have hxb : x ≠ b := by
    intro he
    refine hv1nc ?_
    have hb2 := hap1
    rw [aff_gt_1_2 hdisap] at hb2
    simp only [Set.mem_setOf_eq] at hb2
    obtain ⟨g1, g2, g3, hg2, hg3, hgsum, hapeq⟩ := hb2
    have hg1 : g1 = 1 - g2 - g3 := by linarith
    rw [hg1] at hapeq
    have h3 : b - x = a' • (ap - x) := by rw [hbdef, hscale]
    have h5 : (0 : V3) = a' • (ap - x) := by
      have hz : b - x = (0 : V3) := by rw [he]; module
      exact hz.symm.trans h3
    rw [hapeq] at h5
    have h6 : (a' * g2) • (v1 - x) + (a' * g3) • (y - x) = (0 : V3) := by
      rw [h5]; module
    exact connect_below_collinear_of_smul (b1 := a' * g2)
      (mul_ne_zero (ne_of_gt ha'0) (ne_of_gt hg2)) h6
  -- ## 块链：affGt {x} {b, v1} ⊆ affGt {x} {w,v,u123} ⊆ dartLeadsInto v u123 = 面 (w,v) 的块
  have hcop4 : ¬ Coplanar ({x, w, v, u123} : Set V3) :=
    properties_fully_surrounded hfan hvwSwap hu123edge hθ0 hθπ
  have hcopWedge : ¬ Coplanar ({x, w, v, c} : Set V3) :=
    continuous_coplanar_fan x w v u123 hcop4 (t4 / 2) (by linarith)
  have hsetreorder : ({x, w, v, c} : Set V3) = ({x, w, c, v} : Set V3) := by
    ext q; simp; tauto
  have hsub1 : affGt ({x} : Set V3) ({b, v1} : Set V3) ⊆
      affGt ({x} : Set V3) ({w, c, v} : Set V3) :=
    aff_gt_1_2_subset_aff_1_3111 x b v1 w c v (hsetreorder ▸ hcopWedge) hbmem hv1mem'
  have hreorder2 : ({w, c, v} : Set V3) = ({w, v, c} : Set V3) := by
    ext q; simp; tauto
  have hsub2 : affGt ({x} : Set V3) ({w, c, v} : Set V3) ⊆
      affGt ({x} : Set V3) ({w, v, u123} : Set V3) := by
    intro q hq
    rw [hreorder2] at hq
    exact AFF_GT_1_3_SUBSET_AFF_GT_1_3 x w v u123 (t4 / 2) hcop4
      (by linarith) (by linarith) hq
  have hsub3 : affGt ({x} : Set V3) ({w, v, u123} : Set V3) ⊆ dartLeadsInto x V E v u123 :=
    aff_gt_1_3_subset_dart_leads_into_fan x V E w v u123 hfan hvwSwap hu123edge hu123sig
      hcard hfan80
  have hdwv : (w, v) ∈ dart1OfFan V E := by simpa [dart1OfFan] using hvwSwap
  have hdwvd : (w, v) ∈ (hypermapOfFan x V E hfan).darts :=
    (finite_dart1_fan hfan).mem_toFinset.mpr hdwv
  have hfaceset : (hypermapOfFan x V E hfan).face (w, v) ∈
      (hypermapOfFan x V E hfan).faceSet :=
    ((hypermapOfFan x V E hfan).mem_darts_iff_face_mem (w, v)).mp hdwvd
  have hface : (v, u123) ∈ (hypermapOfFan x V E hfan).face (w, v) := by
    rw [Hypermap.face, orbitMap]
    simp only [Set.mem_setOf_eq]
    refine ⟨1, ?_⟩
    rw [hypermapOfFan_faceMap_iterate hfan hdwv 1]
    simp [f1Fan, hu123def]
  have hblock : dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (w, v)) =
      dartLeadsInto x V E v u123 :=
    DARTSET_LEADS_INTO_FAN hfan hcard hfan80 hfaceset (v, u123) hface
  -- ## 组装：δ = t1·t'/2，线段点 = (1-β)·v1 + β·b，β = s/(t1·t')
  refine ⟨t1 * t' / 2, div_pos (mul_pos ht1pos ht'0) two_pos, ?_⟩
  intro s hs0 hsδ hs1
  have hdisbv : Disjoint ({x} : Set V3) ({b, v1} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxb, Ne.symm hv1x⟩
  have hM0 : (0:ℝ) < t1 * t' := mul_pos ht1pos ht'0
  have hβlt : (t1 * t')⁻¹ * s < 1 := by
    rw [← div_eq_inv_mul, div_lt_iff₀ hM0]
    have hbrid : (t1:ℝ) * t' / 2 = 1 / 2 * (t1 * t') := by ring
    linarith
  have hαpos : 0 < 1 - (t1 * t')⁻¹ * s := by linarith
  have hp : (1 - (t1 - s)) • y + (t1 - s) • z ∈
      affGt ({x} : Set V3) ({b, v1} : Set V3) := by
    have hvecM : (t1 * t') • ((1 - (t1 - s)) • y + (t1 - s) • z)
        = (t1 * t' - s) • v1 + s • b := by
      rw [hbdef, hv1t]; module
    have hveq : (1 - (t1 - s)) • y + (t1 - s) • z
        = (0:ℝ) • x + ((t1 * t')⁻¹ * s) • b + (1 - (t1 * t')⁻¹ * s) • v1 := by
      calc (1 - (t1 - s)) • y + (t1 - s) • z
          = (t1 * t')⁻¹ • ((t1 * t') • ((1 - (t1 - s)) • y + (t1 - s) • z)) :=
            (inv_smul_smul₀ hM0.ne' _).symm
        _ = (t1 * t')⁻¹ • ((t1 * t' - s) • v1 + s • b) := by rw [hvecM]
        _ = ((t1 * t')⁻¹ * (t1 * t' - s)) • v1 + ((t1 * t')⁻¹ * s) • b := by
            rw [smul_add, smul_smul, smul_smul]
        _ = (0:ℝ) • x + ((t1 * t')⁻¹ * s) • b + (1 - (t1 * t')⁻¹ * s) • v1 := by
            have hsc : (t1 * t')⁻¹ * (t1 * t' - s) = 1 - (t1 * t')⁻¹ * s := by
              rw [mul_sub, inv_mul_cancel₀ hM0.ne']
            rw [hsc, zero_smul, zero_add, add_comm]
    rw [aff_gt_1_2 hdisbv]
    simp only [Set.mem_setOf_eq]
    refine ⟨0, (t1 * t')⁻¹ * s, 1 - (t1 * t')⁻¹ * s,
      mul_pos (inv_pos.mpr hM0) hs0, hαpos, by ring, hveq⟩
  rw [hblock]
  exact hsub3 (hsub2 (hsub1 hp))

/-- W6 备料：`connect_geom_aux` 的退化 azim 消去核。`y - x = c•(a-x) + h•(v1-x)`
（`c > 0`，来自 `azim_eq_azim_iff` + `affGt_pair_iff`）在 `h = 0` 侧直接给出
`y` 落入 `{a,b}` 闭锥；`h ≠ 0` 侧由线段横越（`hseg` 型假设）或 `z` 入闭锥
导出矛盾。 -/
private theorem connect_aux_degen {x a b y z v1 : V3} {t1 s t c h : ℝ}
    (hxa : x ≠ a)
    (hseg1 : v1 - x = (1 - t1) • (y - x) + t1 • (z - x)) (ht1 : 0 < t1) (ht1' : t1 < 1)
    (hcone : v1 - x = s • (a - x) + t • (b - x)) (hs : 0 < s) (ht : 0 < t)
    (hyrel : y - x = c • (a - x) + h • (v1 - x)) (hc : 0 < c)
    (hnotA : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (1 - u) • y + u • z ∉ affGe ({x} : Set V3) ({a}))
    (hyexit : ∀ e1 e2 : ℝ, 0 ≤ e1 → 0 ≤ e2 →
      y - x = e1 • (a - x) + e2 • (b - x) → False)
    (hzexit : ∀ e1 e2 : ℝ, 0 ≤ e1 → 0 ≤ e2 →
      z - x = e1 • (a - x) + e2 • (b - x) → False) : False := by
  have hyAB : y - x = (c + h * s) • (a - x) + (h * t) • (b - x) := by
    rw [hyrel, hcone]; module
  have hzvec : t1 • (z - x) = (v1 - x) - (1 - t1) • (y - x) := by
    rw [hseg1]; module
  rcases le_or_gt 0 h with hpos | hneg
  · -- h ≥ 0：y 已在 {a,b} 闭锥内
    refine hyexit (c + h * s) (h * t) ?_ ?_ hyAB
    · show (0:ℝ) ≤ c + h * s
      have := mul_nonneg hpos hs.le
      linarith
    · show (0:ℝ) ≤ h * t
      exact mul_nonneg hpos ht.le
  · -- h < 0：h*t < 0，y 在 b 侧之外；线段必横越 a-射线
    -- 关键归一：t1*(h*t) - Q = t*(h-1)，故取 u = t1*h/(h-1)
    set Q := t - (1 - t1) * (h * t) with hQdef
    have hDsimp : t1 * (h * t) - Q = t * (h - 1) := by rw [hQdef]; ring
    have hDne : (h:ℝ) - 1 ≠ 0 := by linarith
    have hDneg : t * (h - 1) < 0 := by
      calc t * (h - 1) = t * h - t := by ring
        _ < 0 := by have := mul_neg_of_neg_of_pos hneg ht; linarith
    have hprod : (h:ℝ) * (1 - t1) ≤ 0 := by
      calc h * (1 - t1) = -((-h) * (1 - t1)) := by ring
        _ ≤ 0 := neg_nonpos.mpr
            (mul_nonneg (neg_nonneg.mpr hneg.le) (by linarith))
    set u := t1 * h / (h - 1) with hudef
    have hu0 : (0:ℝ) < u := by
      have h1 := div_pos
        (by have := mul_neg_of_neg_of_pos hneg ht1; linarith : (0:ℝ) < -(t1 * h))
        (by linarith [hDneg] : (0:ℝ) < -(h - 1))
      have h2 : -(t1 * h) / -(h - 1) = u := by rw [hudef]; field_simp
      rwa [h2] at h1
    have hu1 : u < 1 := by
      have h1 := (div_lt_one (by linarith [hDneg] : (0:ℝ) < -(h - 1))).mpr
        (show -(t1 * h) < -(h - 1) by linarith [hprod])
      have h2 : -(t1 * h) / -(h - 1) = u := by rw [hudef]; field_simp
      rwa [h2] at h1
    have hb0 : (1 - u) * (t1 * (h * t)) + u * Q = 0 := by
      have hXQ : u * (t * (h - 1)) = t1 * (h * t) := by
        rw [hudef]; field_simp [hDne]
      calc (1 - u) * (t1 * (h * t)) + u * Q
          = t1 * (h * t) - u * (t1 * (h * t) - Q) := by ring
        _ = t1 * (h * t) - u * (t * (h - 1)) := by rw [hDsimp]
        _ = 0 := by rw [hXQ]; ring
    set A' := (1 - u) * (t1 * (c + h * s)) + u * (s - (1 - t1) * (c + h * s)) with hA'def
    have hsplit : t1 • ((1 - u) • (y - x) + u • (z - x))
        = A' • (a - x) + ((1 - u) * (t1 * (h * t)) + u * Q) • (b - x) := by
      have e1 : t1 • ((1 - u) • (y - x) + u • (z - x))
          = (t1 * (1 - u)) • (y - x) + (t1 * u) • (z - x) := by
        rw [smul_add, smul_smul, smul_smul]
      have e2 : (t1 * u) • (z - x) = u • (t1 • (z - x)) := by
        rw [smul_smul, mul_comm]
      have e3 : u • (t1 • (z - x)) = u • ((v1 - x) - (1 - t1) • (y - x)) := by
        rw [hzvec]
      have e4 : u • ((v1 - x) - (1 - t1) • (y - x))
          = u • ((s • (a - x) + t • (b - x))
            - (1 - t1) • ((c + h * s) • (a - x) + (h * t) • (b - x))) := by
        rw [hcone, hyAB]
      rw [hA'def, e1, hyAB, e2, e3, e4]
      module
    have hA'pos : (0:ℝ) < A' := by
      have hkey : A' = t1 * t * c / (t - t * h) := by
        rw [hA'def, hudef]
        field_simp [hDne]
        linear_combination (c *
          (mul_inv_cancel₀ (show (1:ℝ) - h ≠ 0 by linarith)))
      rw [hkey]
      exact div_pos (mul_pos (mul_pos ht1 ht) hc)
        (by have := mul_pos ht (by linarith [hneg] : (0:ℝ) < 1 - h); linarith)
    have hvec : t1 • ((1 - u) • y + u • z - x)
        = t1 • ((1 - u) • (y - x) + u • (z - x)) := by
      module
    have hfinal : t1 • ((1 - u) • y + u • z - x) = A' • (a - x) := by
      rw [hvec, hsplit, hb0]
      simp
    have hlast : (1 - u) • y + u • z - x = (t1⁻¹ * A') • (a - x) := by
      have h1 := congrArg (fun v => (t1)⁻¹ • v) hfinal
      rw [inv_smul_smul₀ ht1.ne', smul_smul] at h1
      exact h1
    refine hnotA u (le_of_lt hu0) (le_of_lt hu1) ?_
    have hpt : (1 - u) • y + u • z = (t1⁻¹ * A') • (a - x) + x := by
      rw [← hlast]; module
    exact (mem_affGe_singleton hxa).mpr
      ⟨1 - t1⁻¹ * A', t1⁻¹ * A',
        le_of_lt (mul_pos (inv_pos.mpr ht1) hA'pos),
        by ring, by rw [hpt]; module
      ⟩
/-- W6：上方 cluster——`azim x v1 w z ∈ (0,π)`（`sum5_azim_fan` 侧）时
`v1` 朝 `z` 一侧的点落入 `face (v, w)`（经 dart `(w, inverse1SigmaFan x V E w v)`）
的引导块。`connect_geom_below` 在 (y,z)、(v,w) 对换、`t1 ↦ 1 - t1` 下的实例。 -/
private theorem connect_geom_above (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    (hcard : ∀ u : V3, u ∈ V → 1 < (setOfEdge u V E).ncard) (hfan80 : fan80 x V E)
    (heE : E ≠ ∅) {y z v1 w v : V3} {t1 : ℝ}
    (hv : v ∈ V) (hw : w ∈ V) (hvw : ({v, w} : Set V3) ∈ E) (hyz : y ≠ z)
    (hy : y ∈ yfan x V E) (hz : z ∈ yfan x V E)
    (hv1t : v1 = (1 - t1) • y + t1 • z) (ht1pos : 0 < t1) (ht1lt : t1 < 1)
    (hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (1 - s) • y + s • z ∈ (Set.univ : Set V3) \ ⋃ v' ∈ V, affGe ({x} : Set V3) {v'})
    (hv1 : v1 ∈ affGt ({x} : Set V3) ({v, w} : Set V3))
    (hazim : azim x v1 w z ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ∃ t''' : ℝ, 0 < t''' ∧ t''' ≤ 1 ∧
      (1 - t''') • v1 + t''' • z ∈
        dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (v, w)) := by
  have hvwSwap : ({w, v} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hvw
  have hv1pair : v1 ∈ affGt ({x} : Set V3) ({w, v} : Set V3) := by
    rw [Set.pair_comm]; exact hv1
  have hseg' : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (1 - s) • z + s • y ∈ (Set.univ : Set V3) \ ⋃ v' ∈ V, affGe ({x} : Set V3) {v'} := by
    intro s hs0 hs1
    have h := hseg (1 - s) (by linarith) (by linarith)
    have he : (1 - (1 - s)) • y + (1 - s) • z = (1 - s) • z + s • y := by
      rw [show ((1:ℝ) - (1 - s)) = s from by ring]
      module
    rwa [he] at h
  have hv1t' : v1 = (1 - (1 - t1)) • z + (1 - t1) • y := by
    rw [hv1t]; module
  obtain ⟨δ, hδ0, hblock⟩ := connect_geom_below x V E hfan hconf hcard hfan80 heE
    (y := z) (z := y) (v := w) (w := v) (t1 := 1 - t1) hw hv hvwSwap (Ne.symm hyz) hz hy
    hv1t' (by linarith) (by linarith) hseg' hv1pair hazim
  have ht1ne : (1:ℝ) - t1 ≠ 0 := by linarith
  refine ⟨min δ (1 - t1) / 2 / (1 - t1), ?_, ?_, ?_⟩
  · exact div_pos (div_pos (lt_min hδ0 (by linarith)) two_pos) (by linarith)
  · rw [div_le_one₀ (by linarith : (0:ℝ) < 1 - t1)]
    have h1 := min_le_right δ (1 - t1)
    linarith
  · set s₀ := min δ (1 - t1) / 2 with hs0def
    have hs00 : (0:ℝ) < s₀ := by
      rw [hs0def]; exact div_pos (lt_min hδ0 (by linarith)) two_pos
    have hs0δ : s₀ ≤ δ := by rw [hs0def]; have := min_le_left δ (1 - t1); linarith
    have hs0t : s₀ ≤ 1 - t1 := by rw [hs0def]; have := min_le_right δ (1 - t1); linarith
    have hmul : (1 - t1) * (s₀ / (1 - t1)) = s₀ := mul_div_cancel₀ _ ht1ne
    have hpt : (1 - s₀ / (1 - t1)) • v1 + (s₀ / (1 - t1)) • z
        = (1 - ((1 - t1) - s₀)) • z + ((1 - t1) - s₀) • y := by
      generalize hκ : s₀ / (1 - t1) = κ
      have hκ' : s₀ = (1 - t1) * κ := by
        have h2 : (1 - t1) * (s₀ / (1 - t1)) = s₀ := mul_div_cancel₀ _ ht1ne
        rw [hκ] at h2
        exact h2.symm
      rw [hκ', hv1t]
      module
    rw [hpt]
    exact hblock s₀ hs00 hs0δ hs0t


/-- W4 修复版几何链（HOL Conforming.hl:15460-16750 长几何段的打包接口）。

W2 冻结版断言 `v1` 两侧的点都落在 `face (w, σFan w v)` 的引导块中——该面与边
`{v,w}` 不相邻，陈述为假（正四面体反例，W3 确认）。真实几何（W4 用
`sum4/5_azim_fan` 的符号核对 + 数值验证确认）：
- `azim x v1 v y ∈ (0, π)` 时，`v1` 下方（朝 `y` 侧）的点落入边 `{v,w}` 的
  相邻面 `face (w, v)` 的引导块（经 `dart (v, inverse1SigmaFan x V E v w)`），
  `v1` 上方（朝 `z` 侧）的点落入另一相邻面 `face (v, w)` 的引导块；
- `azim x v1 v y ∈ (π, 2π)` 时两侧对调。

调用方（`lemma_connect_hypermap`）据下方点证 `face fd = face F1` 得
`F1 ∈ D`，再用组件对 `edgeMap` 的封闭性（`goOneStep` 含 `edgeMap` 步）得
`F2 = edgeMap F1 ∈ D`，上方点即以 `F2` 见证 `t1 + (1-t1)*t''' ∈ TA`。 -/
private theorem connect_geom_aux (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    (hcard : ∀ u : V3, u ∈ V → 1 < (setOfEdge u V E).ncard) (hfan80 : fan80 x V E)
    (heE : E ≠ ∅) {y z v1 w v : V3} {t1 : ℝ}
    (hv : v ∈ V) (hw : w ∈ V) (hvw : ({v, w} : Set V3) ∈ E) (hyz : y ≠ z)
    (hy : y ∈ yfan x V E) (hz : z ∈ yfan x V E)
    (hv1t : v1 = (1 - t1) • y + t1 • z) (ht1pos : 0 < t1) (ht1lt : t1 < 1)
    (hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (1 - s) • y + s • z ∈ (Set.univ : Set V3) \ ⋃ v' ∈ V, affGe ({x} : Set V3) {v'})
    (hv1 : v1 ∈ affGt ({x} : Set V3) ({v, w} : Set V3)) :
    ∃ δ t''' : ℝ, 0 < δ ∧ 0 < t''' ∧ t''' ≤ 1 ∧
      (((∀ s : ℝ, 0 < s → s ≤ δ → s ≤ t1 →
            (1 - (t1 - s)) • y + (t1 - s) • z ∈
              dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (w, v))) ∧
          (1 - t''') • v1 + t''' • z ∈
              dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (v, w))) ∨
        ((∀ s : ℝ, 0 < s → s ≤ δ → s ≤ t1 →
            (1 - (t1 - s)) • y + (t1 - s) • z ∈
              dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (v, w))) ∧
          (1 - t''') • v1 + t''' • z ∈
              dartsetLeadsIntoFan x V E ((hypermapOfFan x V E hfan).face (w, v)))) := by
  -- W4 阻断报告（几何链子步骤）：真实几何是"交叉"形态——azim x v1 v y ∈ (0,π)
  -- 时下方点落 block(face (w,v))、上方点落 block(face (v,w))；azim ∈ (π,2π) 时对调。
  -- 本证明：基础层（非共线束）+ 反极性 azim 记账（v1 ∈ affGt {x}{y,z} 与
  -- v1 ∈ affGt {x}{v,w} 给出 azim x v1 y z = azim x v1 v w = π）+ sum4/sum3/sum5
  -- 的号志传递 + 退化 azim 消去（connect_aux_degen）+ 两条 cluster 实例。
  -- ## 基础层：互异性与锥分解
  obtain ⟨hvwn, hxvn, hxwn⟩ := edge_distinct_of_mem hfan hvw
  have hvwSwap : ({w, v} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hvw
  have hvwn_col : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  have hv1dis : Disjoint ({x} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxvn, hxwn⟩
  have hyxf : y ∉ xfan x V E := by rw [yfan, Set.mem_sdiff] at hy; exact hy.2
  have hzxf : z ∉ xfan x V E := by rw [yfan, Set.mem_sdiff] at hz; exact hz.2
  have hxy : x ≠ y := by
    intro he
    exact hyxf (he ▸ x_in_xfan hfan heE)
  have hxz : x ≠ z := by
    intro he
    exact hzxf (he ▸ x_in_xfan hfan heE)
  have hv1mem' := hv1
  rw [aff_gt_1_2 hv1dis] at hv1mem'
  simp only [Set.mem_setOf_eq] at hv1mem'
  obtain ⟨a1, a2, a3, ha2, ha3, hsum, hv1eq⟩ := hv1mem'
  have hsum1 : a1 = 1 - a2 - a3 := by linarith
  have hrep : v1 - x = a2 • (v - x) + a3 • (w - x) := by
    rw [hv1eq, hsum1]; module
  have hv1x : v1 ≠ x := by
    intro he
    refine hvwn_col ?_
    rw [he, sub_self] at hrep
    exact connect_below_collinear_of_smul (b1 := a2) (ne_of_gt ha2) hrep.symm
  have hv1seg : v1 - x = (1 - t1) • (y - x) + t1 • (z - x) := by
    rw [hv1t]; module
  have ht1ne : (1:ℝ) - t1 ≠ 0 := by linarith
  -- ## 非共线束（锥论证 + yfan/xfan 互斥；below 的 :739-779 复制/镜像）
  have hv1nc_y : ¬ Collinear3 x v1 y := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := x) (w := v1) (w1 := y) hv1x).mp hcol
    by_cases hcle : (0:ℝ) ≤ c
    · have hmu : y - x = (c * a2) • (v - x) + (c * a3) • (w - x) := by
        rw [hc, hrep]; module
      exact hyxf (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (mul_nonneg hcle ha2.le) (mul_nonneg hcle ha3.le) hmu)
    · have hclt : c < 0 := lt_of_not_ge hcle
      have h0 : t1 • (z - x) = v1 - x - (1 - t1) • (y - x) := by rw [hv1seg]; module
      have h1 : t1 • (z - x) = (1 - (1 - t1) * c) • (v1 - x) := by rw [h0, hc]; module
      have hz' : z - x = ((1 - (1 - t1) * c) / t1) • (v1 - x) := by
        have h2 : t1 • (z - x - ((1 - (1 - t1) * c) / t1) • (v1 - x)) = (0 : V3) := by
          rw [smul_sub, h1, smul_smul, mul_div_cancel₀ _ ht1pos.ne', sub_self]
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 ht1pos.ne'
        · exact sub_eq_zero.mp h3
      have hmu : z - x = (((1 - (1 - t1) * c) / t1) * a2) • (v - x) +
          (((1 - (1 - t1) * c) / t1) * a3) • (w - x) := by rw [hz', hrep]; module
      have hsign : (0:ℝ) ≤ 1 - (1 - t1) * c := by
        have hm : (0:ℝ) ≤ (1 - t1) * (-c) := mul_nonneg (by linarith) (neg_nonneg.mpr hclt.le)
        have hm2 : (1 - t1) * c = -((1 - t1) * (-c)) := by ring
        linarith
      exact hzxf (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (e2 := ((1 - (1 - t1) * c) / t1) * a2) (e3 := ((1 - (1 - t1) * c) / t1) * a3)
        (mul_nonneg (div_nonneg hsign ht1pos.le) ha2.le)
        (mul_nonneg (div_nonneg hsign ht1pos.le) ha3.le) hmu)
  have hv1nc_z : ¬ Collinear3 x v1 z := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := x) (w := v1) (w1 := z) hv1x).mp hcol
    by_cases hcle : (0:ℝ) ≤ c
    · have hmu : z - x = (c * a2) • (v - x) + (c * a3) • (w - x) := by
        rw [hc, hrep]; module
      exact hzxf (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (mul_nonneg hcle ha2.le) (mul_nonneg hcle ha3.le) hmu)
    · have hclt : c < 0 := lt_of_not_ge hcle
      have h0 : (1 - t1) • (y - x) = v1 - x - t1 • (z - x) := by rw [hv1seg]; module
      have h1 : (1 - t1) • (y - x) = (1 - t1 * c) • (v1 - x) := by rw [h0, hc]; module
      have hy' : y - x = ((1 - t1 * c) / (1 - t1)) • (v1 - x) := by
        have h2 : (1 - t1) • (y - x - ((1 - t1 * c) / (1 - t1)) • (v1 - x)) = (0 : V3) := by
          rw [smul_sub, h1, smul_smul, mul_div_cancel₀ _ ht1ne, sub_self]
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 ht1ne
        · exact sub_eq_zero.mp h3
      have hsign : (0:ℝ) ≤ 1 - t1 * c := by
        have hm : (0:ℝ) < t1 * (-c) := mul_pos ht1pos (neg_pos.mpr hclt)
        have hm2 : t1 * c = -(t1 * (-c)) := by ring
        linarith
      have hmu : y - x = (((1 - t1 * c) / (1 - t1)) * a2) • (v - x) +
          (((1 - t1 * c) / (1 - t1)) * a3) • (w - x) := by rw [hy', hrep]; module
      exact hyxf (connect_below_cone_xfan hvw hxvn hxwn hvwn
        (e2 := ((1 - t1 * c) / (1 - t1)) * a2) (e3 := ((1 - t1 * c) / (1 - t1)) * a3)
        (mul_nonneg (div_nonneg hsign (by linarith)) ha2.le)
        (mul_nonneg (div_nonneg hsign (by linarith)) ha3.le) hmu)
  have hv1v_col : ¬ Collinear3 x v1 v := by
    intro hcol
    obtain ⟨μ, hμ⟩ := (collinear3_iff_smul (v := x) (w := v1) (w1 := v) hv1x).mp hcol
    rcases eq_or_ne μ 0 with rfl | hμ0
    · rw [zero_smul, sub_eq_zero] at hμ
      exact hxvn hμ.symm
    · refine hvwn_col ?_
      have h6 : v1 - x = μ⁻¹ • (v - x) := by rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      have h7a : a3 • (w - x) = v1 - x - a2 • (v - x) := by rw [hrep]; module
      have h7 : a3 • (w - x) = (μ⁻¹ - a2) • (v - x) := by rw [h7a, h6]; module
      obtain ⟨κ, hκ⟩ := connect_below_smul_div (a := a3) (d := μ⁻¹ - a2) (ne_of_gt ha3) h7
      exact (collinear3_iff_smul (v := x) (w := v) (w1 := w) (Ne.symm hxvn)).mpr ⟨κ, hκ⟩
  have hv1w_col : ¬ Collinear3 x v1 w := by
    intro hcol
    obtain ⟨μ, hμ⟩ := (collinear3_iff_smul (v := x) (w := v1) (w1 := w) hv1x).mp hcol
    rcases eq_or_ne μ 0 with rfl | hμ0
    · rw [zero_smul, sub_eq_zero] at hμ
      exact hxwn hμ.symm
    · refine hvwn_col ?_
      have h6 : v1 - x = μ⁻¹ • (w - x) := by rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      have h7a : a2 • (v - x) = v1 - x - a3 • (w - x) := by rw [hrep]; module
      have h7 : a2 • (v - x) = (μ⁻¹ - a3) • (w - x) := by rw [h7a, h6]; module
      obtain ⟨κ, hκ⟩ := connect_below_smul_div (a := a2) (d := μ⁻¹ - a3) (ne_of_gt ha2) h7
      have hcol2 : Collinear ℝ ({x, w, v} : Set V3) :=
        (collinear3_iff_smul (v := x) (w := w) (w1 := v) (Ne.symm hxwn)).mpr ⟨κ, hκ⟩
      have hset : ({x, w, v} : Set V3) = ({x, v, w} : Set V3) := by ext q; simp; tauto
      rw [hset] at hcol2
      exact hcol2
  have hv1ne_v : v ≠ v1 := by
    intro he
    refine hvwn_col ?_
    have h3 : v - x = a2 • (v - x) + a3 • (w - x) := by
      rw [← he] at hrep
      exact hrep
    have h4 : a3 • (w - x) = (1 - a2) • (v - x) := by
      have h5 : v - x - a2 • (v - x) = a3 • (w - x) := by
        nth_rewrite 1 [h3]
        module
      rw [← h5]; module
    obtain ⟨κ, hκ⟩ := connect_below_smul_div (a := a3) (d := 1 - a2) (ne_of_gt ha3) h4
    exact (collinear3_iff_smul (v := x) (w := v) (w1 := w) (Ne.symm hxvn)).mpr ⟨κ, hκ⟩
  have hv1ne_w : w ≠ v1 := by
    intro he
    refine hvwn_col ?_
    have h3 : w - x = a2 • (v - x) + a3 • (w - x) := by
      rw [← he] at hrep
      exact hrep
    have h4 : a2 • (v - x) = (1 - a3) • (w - x) := by
      have h5 : w - x - a3 • (w - x) = a2 • (v - x) := by
        nth_rewrite 1 [h3]
        module
      rw [← h5]; module
    obtain ⟨κ, hκ⟩ := connect_below_smul_div (a := a2) (d := 1 - a3) (ne_of_gt ha2) h4
    have hcol2 : Collinear ℝ ({x, w, v} : Set V3) :=
      (collinear3_iff_smul (v := x) (w := w) (w1 := v) (Ne.symm hxwn)).mpr ⟨κ, hκ⟩
    have hset : ({x, w, v} : Set V3) = ({x, v, w} : Set V3) := by ext q; simp; tauto
    rw [hset] at hcol2
    exact hcol2
  -- ## 反极性：v1 ∈ affGt {x}{y,z}（t1 ∈ (0,1)）与 v1 ∈ affGt {x}{v,w} 都给出 π
  have hdisyz : Disjoint ({x} : Set V3) ({y, z} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxy, hxz⟩
  have hv1yz : v1 ∈ affGt ({x} : Set V3) ({y, z} : Set V3) := by
    rw [aff_gt_1_2 hdisyz]
    simp only [Set.mem_setOf_eq]
    exact ⟨0, 1 - t1, t1, by linarith, by linarith, by ring, by rw [hv1t]; module⟩
  have hF1 : azim x v1 y z = Real.pi := aff_gt2_subset_aff_ge hdisyz hv1nc_z hv1nc_y hv1yz
  have hF1' : azim x v1 z y = Real.pi := by
    have hd : Disjoint ({x} : Set V3) ({z, y} : Set V3) := by
      rw [Set.pair_comm]; exact hdisyz
    have hm : v1 ∈ affGt ({x} : Set V3) ({z, y} : Set V3) := by
      rw [Set.pair_comm]; exact hv1yz
    exact aff_gt2_subset_aff_ge hd hv1nc_y hv1nc_z hm
  have hF2 : azim x v1 v w = Real.pi := aff_gt2_subset_aff_ge hv1dis hv1w_col hv1v_col hv1
  have hF2' : azim x v1 w v = Real.pi := by
    have hd : Disjoint ({x} : Set V3) ({w, v} : Set V3) := by
      rw [Set.pair_comm]; exact hv1dis
    have hm : v1 ∈ affGt ({x} : Set V3) ({w, v} : Set V3) := by
      rw [Set.pair_comm]; exact hv1
    exact aff_gt2_subset_aff_ge hd hv1v_col hv1w_col hm
  have hβ0 : 0 ≤ azim x v1 v y := azim_nonneg x v1 v y
  have hβ2π : azim x v1 v y < 2 * Real.pi := azim_lt_two_pi x v1 v y
  -- ## azim x v1 v y 的四分与退化消去
  rcases lt_or_ge (azim x v1 v y) Real.pi with hβltπ | hβgeπ
  · rcases lt_trichotomy (azim x v1 v y) 0 with hβneg | hβz | hβpos
    · exact absurd hβneg (not_lt.mpr hβ0)
    · -- 退化：azim x v1 v y = 0 ⇒ azim x v1 w y = π ⇒ y ∈ affGt {x,v1}{v}，矛盾
      have hγ : azim x v1 w y = Real.pi := by
        have hsum := sum5_azim_fan (x := x) (v := v1) (u := w) (w1 := v) (w2 := y)
          hv1x hv1w_col hv1v_col hv1nc_y (by rw [hβz]; exact azim_nonneg x v1 w y)
        rw [hF2', hβz, add_zero] at hsum
        exact hsum
      have hmem : y ∈ affGt ({x, v1} : Set V3) ({v} : Set V3) := by
        have hiff := azim_eq_azim_iff (v0 := x) (v1 := v1) (w := w) (x := v) (y := y)
          hv1w_col hv1v_col hv1nc_y
        rw [hF2', hγ] at hiff
        exact hiff.mp rfl
      obtain ⟨c₀, hc₀, h₀, hyrel⟩ :=
        affGt_pair_iff (v0 := x) (v1 := v1) (x := v) (y := y)
          (hv0v1 := Ne.symm hv1x) (hx0 := Ne.symm hxvn) (hx1 := hv1ne_v)
        |>.mp hmem
      exact (connect_aux_degen (x := x) (a := v) (b := w) (y := y) (z := z) (v1 := v1)
        (t1 := t1) (s := a2) (t := a3) (c := c₀) (h := h₀)
        hxvn hv1seg ht1pos ht1lt hrep ha2 ha3 hyrel hc₀
        (fun u hu0 hu1 hm =>
          (hseg u hu0 hu1).2 (Set.mem_iUnion₂.2 ⟨v, hv, hm⟩))
        (fun e1 e2 he1 he2 hEq =>
          hyxf (connect_below_cone_xfan hvw hxvn hxwn hvwn he1 he2 hEq))
        (fun e1 e2 he1 he2 hEq =>
          hzxf (connect_below_cone_xfan hvw hxvn hxwn hvwn he1 he2 hEq))).elim
    · -- 情形 1：β ∈ (0,π)：sum4/sum3 给 γ = π + β，再 compl + sum4 得 azim x v1 w z = β
      have hγ : azim x v1 w y = Real.pi + azim x v1 v y := by
        rcases le_or_gt Real.pi (azim x v1 w y) with hγπ | hγlt
        · rw [sum4_azim_fan (x := x) (v := v1) (u := w) (w1 := v) (w2 := y)
            hv1x hv1w_col hv1v_col hv1nc_y (by rw [hF2']; exact hγπ), hF2']
        · exfalso
          have hsum := sum3_azim_fan (x := x) (v := v1) (u := w) (w1 := v) (w2 := y)
            hv1x hv1w_col hv1v_col hv1nc_y (by rw [hF2']; linarith)
          rw [hF2'] at hsum
          linarith
      have hγne : azim x v1 w y ≠ 0 := by rw [hγ]; linarith
      have hδ : azim x v1 y w = Real.pi - azim x v1 v y := by
        rw [azim_compl hv1w_col hv1nc_y, if_neg hγne, hγ]; ring
      have hzβ : azim x v1 w z = azim x v1 v y := by
        have hsum := sum4_azim_fan (x := x) (v := v1) (u := y) (w1 := w) (w2 := z)
          hv1x hv1nc_y hv1w_col hv1nc_z (by rw [hδ, hF1]; linarith)
        rw [hF1, hδ] at hsum
        linarith
      obtain ⟨δ, hδ0, hbelow⟩ := connect_geom_below x V E hfan hconf hcard hfan80 heE
        hv hw hvw hyz hy hz hv1t ht1pos ht1lt hseg hv1 ⟨hβpos, hβltπ⟩
      obtain ⟨t''', ht0, ht1b, habove⟩ := connect_geom_above x V E hfan hconf hcard hfan80 heE
        hv hw hvw hyz hy hz hv1t ht1pos ht1lt hseg hv1
        ⟨by rw [hzβ]; exact hβpos, by rw [hzβ]; exact hβltπ⟩
      exact ⟨δ, t''', hδ0, ht0, ht1b, Or.inl ⟨hbelow, habove⟩⟩
  · rcases lt_trichotomy (azim x v1 v y) Real.pi with hβltπ | hβπ | hβgtπ
    · exact absurd hβltπ (by linarith)
    · -- 退化：azim x v1 v y = π ⇒ sum4 给 azim x v1 w y = 0 ⇒ y ∈ affGt {x,v1}{w}，矛盾
      have hγ : azim x v1 w y = 0 := by
        have hsum := sum4_azim_fan (x := x) (v := v1) (u := v) (w1 := w) (w2 := y)
          hv1x hv1v_col hv1w_col hv1nc_y (by rw [hF2, hβπ])
        rw [hF2, hβπ] at hsum
        linarith
      have hmem : y ∈ affGt ({x, v1} : Set V3) ({w} : Set V3) := by
        have hiff := azim_eq_azim_iff (v0 := x) (v1 := v1) (w := v) (x := w) (y := y)
          hv1v_col hv1w_col hv1nc_y
        rw [hF2, hβπ] at hiff
        exact hiff.mp rfl
      obtain ⟨c₀, hc₀, h₀, hyrel⟩ :=
        affGt_pair_iff (v0 := x) (v1 := v1) (x := w) (y := y)
          (hv0v1 := Ne.symm hv1x) (hx0 := Ne.symm hxwn) (hx1 := hv1ne_w)
        |>.mp hmem
      exact (connect_aux_degen (x := x) (a := w) (b := v) (y := y) (z := z) (v1 := v1)
        (t1 := t1) (s := a3) (t := a2) (c := c₀) (h := h₀)
        hxwn hv1seg ht1pos ht1lt
        (show v1 - x = a3 • (w - x) + a2 • (v - x) from by rw [hrep]; module)
        ha3 ha2 hyrel hc₀
        (fun u hu0 hu1 hm =>
          (hseg u hu0 hu1).2 (Set.mem_iUnion₂.2 ⟨w, hw, hm⟩))
        (fun e1 e2 he1 he2 hEq =>
          hyxf (connect_below_cone_xfan hvw hxvn hxwn hvwn he2 he1 (by rw [hEq]; module)))
        (fun e1 e2 he1 he2 hEq =>
          hzxf (connect_below_cone_xfan hvw hxvn hxwn hvwn he2 he1 (by rw [hEq]; module)))).elim
    · -- 情形 2：π < β：γ = β - π 与 azim x v1 v z = β - π，两侧对调
      have hγ : azim x v1 w y = azim x v1 v y - Real.pi := by
        have hsum := sum4_azim_fan (x := x) (v := v1) (u := v) (w1 := w) (w2 := y)
          hv1x hv1v_col hv1w_col hv1nc_y (by rw [hF2]; exact hβgeπ)
        rw [hF2] at hsum
        linarith
      have hγIoo : azim x v1 w y ∈ Set.Ioo (0:ℝ) Real.pi :=
        ⟨by rw [hγ]; linarith, by rw [hγ]; linarith [hβ2π]⟩
      have hzβ : azim x v1 v z = azim x v1 v y - Real.pi := by
        rcases le_or_gt (azim x v1 v z) (azim x v1 v y) with hle | hlt
        · have hsum := sum4_azim_fan (x := x) (v := v1) (u := v) (w1 := z) (w2 := y)
            hv1x hv1v_col hv1nc_z hv1nc_y hle
          rw [hF1'] at hsum
          linarith
        · exfalso
          have hsum := sum4_azim_fan (x := x) (v := v1) (u := v) (w1 := y) (w2 := z)
            hv1x hv1v_col hv1nc_y hv1nc_z hlt.le
          rw [hF1] at hsum
          have := azim_lt_two_pi x v1 v z
          linarith
      have hzβIoo : azim x v1 v z ∈ Set.Ioo (0:ℝ) Real.pi :=
        ⟨by rw [hzβ]; linarith [hβgtπ], by rw [hzβ]; linarith [hβ2π]⟩
      have hv1pair : v1 ∈ affGt ({x} : Set V3) ({w, v} : Set V3) := by
        rw [Set.pair_comm]; exact hv1
      obtain ⟨δ, hδ0, hbelow⟩ := connect_geom_below x V E hfan hconf hcard hfan80 heE
        (v := w) (w := v) hw hv hvwSwap hyz hy hz hv1t ht1pos ht1lt hseg hv1pair hγIoo
      obtain ⟨t''', ht0, ht1b, habove⟩ := connect_geom_above x V E hfan hconf hcard hfan80 heE
        (v := w) (w := v) hw hv hvwSwap hyz hy hz hv1t ht1pos ht1lt hseg hv1pair hzβIoo
      exact ⟨δ, t''', hδ0, ht0, ht1b, Or.inr ⟨hbelow, habove⟩⟩


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
  -- ### P1：dart 集、面簇、组件
  have hd1 : dartOfFan V E = dart1OfFan V E := dartOfFan_eq_dart1_of_surrounded hfan hcard
  have hf1d : f1 ∈ dart1OfFan V E := hd1 ▸ hf1
  have hf2d : f2 ∈ dart1OfFan V E := hd1 ▸ hf2
  have hf1H : f1 ∈ (hypermapOfFan x V E hfan).darts := by
    show f1 ∈ (finite_dart1_fan hfan).toFinset
    exact (finite_dart1_fan hfan).mem_toFinset.mpr hf1d
  have hf2H : f2 ∈ (hypermapOfFan x V E hfan).darts := by
    show f2 ∈ (finite_dart1_fan hfan).toFinset
    exact (finite_dart1_fan hfan).mem_toFinset.mpr hf2d
  set H := hypermapOfFan x V E hfan with hHdef
  have hds : H.face f1 ∈ H.faceSet := (H.mem_darts_iff_face_mem f1).mp hf1H
  have hds1 : H.face f2 ∈ H.faceSet := (H.mem_darts_iff_face_mem f2).mp hf2H
  refine ⟨H.combComponent f1, hypermapOfFan_mem_setOfComponents H hf1H,
    H.mem_combComponent_self f1, ?_⟩
  -- 同一面内的 dart 与面代表连通（face = faceMap-轨道即路径）
  have hfacecomp : ∀ g : V3 × V3, g ∈ H.darts → ∀ y ∈ H.face g, H.isInComponent g y := by
    intro g hg y hy
    obtain ⟨k, hk⟩ := hy
    refine ⟨fun i => (H.faceMap ^ i) g, k, rfl, hk, ?_⟩
    rw [H.isPath_iff]
    intro i _
    exact Or.inr (Or.inr (Function.iterate_succ_apply' H.faceMap i g))
  -- 面块公共点 ⇒ 块相等（yfan 的两拓扑分量相交则重合）
  have hblockEq : ∀ B₁ B₂ : Set (V3 × V3), B₁ ∈ H.faceSet → B₂ ∈ H.faceSet →
      (∃ p : V3, p ∈ dartsetLeadsIntoFan x V E B₁ ∧ p ∈ dartsetLeadsIntoFan x V E B₂) →
        dartsetLeadsIntoFan x V E B₁ = dartsetLeadsIntoFan x V E B₂ := by
    intro B₁ B₂ hB₁ hB₂ hp
    obtain ⟨p, hp₁, hp₂⟩ := hp
    have h₁ := dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hB₁
    rw [topologicalComponentYfan, Set.mem_setOf_eq] at h₁
    obtain ⟨b₁, hb₁, heq₁⟩ := h₁
    have h₂ := dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hB₂
    rw [topologicalComponentYfan, Set.mem_setOf_eq] at h₂
    obtain ⟨b₂, hb₂, heq₂⟩ := h₂
    have hp₁' : p ∈ connectedComponentIn (yfan x V E) b₁ := by rw [heq₁]; exact hp₁
    have hp₂' : p ∈ connectedComponentIn (yfan x V E) b₂ := by rw [heq₂]; exact hp₂
    have hpy : p ∈ yfan x V E := connectedComponentIn_subset (yfan x V E) b₁ hp₁'
    have hb₁Y : b₁ ∈ yfan x V E := connectedComponentIn_nonempty_iff.mp ⟨p, hp₁'⟩
    have hb₂Y : b₂ ∈ yfan x V E := connectedComponentIn_nonempty_iff.mp ⟨p, hp₂'⟩
    have s₁ : connectedComponentIn (yfan x V E) b₁ ⊆ connectedComponentIn (yfan x V E) p :=
      IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn hp₁'
        (connectedComponentIn_subset (yfan x V E) b₁)
    have s₁' : connectedComponentIn (yfan x V E) p ⊆ connectedComponentIn (yfan x V E) b₁ :=
      IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
        (s₁ (mem_connectedComponentIn hb₁Y)) (connectedComponentIn_subset (yfan x V E) p)
    have s₂ : connectedComponentIn (yfan x V E) b₂ ⊆ connectedComponentIn (yfan x V E) p :=
      IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn hp₂'
        (connectedComponentIn_subset (yfan x V E) b₂)
    have s₂' : connectedComponentIn (yfan x V E) p ⊆ connectedComponentIn (yfan x V E) b₂ :=
      IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
        (s₂ (mem_connectedComponentIn hb₂Y)) (connectedComponentIn_subset (yfan x V E) p)
    rw [← heq₁, ← heq₂, subset_antisymm s₁ s₁', subset_antisymm s₂ s₂']
  -- conforming 双射限制在 faceSet 上是单射
  have hbij : ∀ B₁ B₂ : Set (V3 × V3), B₁ ∈ H.faceSet → B₂ ∈ H.faceSet →
      dartsetLeadsIntoFan x V E B₁ = dartsetLeadsIntoFan x V E B₂ → B₁ = B₂ := by
    intro B₁ B₂ hB₁ hB₂ heq
    have ht₁ : dartsetLeadsIntoFan x V E B₁ ∈ topologicalComponentYfan x V E :=
      dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hB₁
    obtain ⟨g, hgprop, hgu⟩ := hconf.2.2.1 _ ht₁
    obtain ⟨hgS, hgeq⟩ := hgprop
    have h1 : B₁ = g := hgu B₁ ⟨hB₁, rfl⟩
    have h2 : B₂ = g := hgu B₂ ⟨hB₂, heq⟩
    rw [h1, h2]
  -- ### P2：连通段 y,z 与 TA、t1 = sup TA
  obtain ⟨y, z, hy, hz, hseg⟩ := connected_in_dartset_leads_into_fan_union_aff_gt x V E
    (H.face f1) (H.face f2) ((Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v})
    hfan hconf hcard hfan80 hds hds1 rfl
  set TA := {t : ℝ | 0 ≤ t ∧ t ≤ 1 ∧ ∃ f ∈ H.combComponent f1,
    (1 - t) • y + t • z ∈ dartsetLeadsIntoFan x V E (H.face f)} with hTAdef
  set t1 := sSup TA with ht1def
  have h0TA : (0:ℝ) ∈ TA :=
    ⟨by norm_num, by norm_num, f1, H.mem_combComponent_self f1, by simpa using hy⟩
  have hmemTA1 : ∀ t ∈ TA, t ≤ 1 := fun t ht => by
    have ht' : t ∈ {t : ℝ | 0 ≤ t ∧ t ≤ 1 ∧ ∃ f ∈ H.combComponent f1,
      (1 - t) • y + t • z ∈ dartsetLeadsIntoFan x V E (H.face f)} := ht
    exact ht'.2.1
  have ht1le1 : t1 ≤ 1 := by
    rw [ht1def]
    exact csSup_le ⟨0, h0TA⟩ hmemTA1
  have hbd : BddAbove TA := ⟨(1:ℝ), hmemTA1⟩
  have h0le : (0:ℝ) ≤ t1 := by
    rw [ht1def]
    exact le_csSup hbd h0TA
  have hbdd : ∀ t ∈ TA, t ≤ t1 := fun t ht => by
    rw [ht1def]
    exact le_csSup hbd ht
  -- 沿 [y,z] 的参数平移恒等式
  have hstep : ∀ u : ℝ,
      ((1 - u) • y + u • z) - ((1 - t1) • y + t1 • z) = (u - t1) • (z - y) := by
    intro u
    module
  have hstepn : ∀ u : ℝ,
      dist ((1 - u) • y + u • z) ((1 - t1) • y + t1 • z) = |u - t1| * ‖z - y‖ := by
    intro u
    rw [dist_eq_norm, hstep, norm_smul, Real.norm_eq_abs]
  by_cases hyz : y = z
  · -- ### P3(i)：y = z，块 face f1 与块 face f2 共享点
    have h₂ : y ∈ dartsetLeadsIntoFan x V E (H.face f2) := by rw [hyz]; exact hz
    have hEq := hblockEq (H.face f1) (H.face f2) hds hds1 ⟨y, hy, h₂⟩
    have hFEq : H.face f1 = H.face f2 := hbij _ _ hds hds1 hEq
    have hmem : f2 ∈ H.face f1 := by rw [hFEq]; exact H.mem_face_self f2
    exact hfacecomp f1 hf1H f2 hmem
  · -- y ≠ z
    have hzyne : ‖z - y‖ ≠ 0 := imp_norm_not_zero_fan hyz
    by_cases ht1 : t1 ∈ TA
    · -- ### P3(ii)：t1 ∈ TA：f2 与该 TA 见证同面
      obtain ⟨-, ht₁₁, f, hfD, hv1m⟩ := ht1
      have hfDd : f ∈ H.darts := Finset.mem_coe.mp (H.combComponent_subset_darts hf1H hfD)
      have hfs : H.face f ∈ H.faceSet := (H.mem_darts_iff_face_mem f).mp hfDd
      rcases eq_or_lt_of_le ht₁₁ with h1 | hlt
      · -- t1 = 1：v1 = z 为公共点
        have hzz : (1 - t1) • y + t1 • z = z := by rw [h1]; simp
        have hEq := hblockEq (H.face f) (H.face f2) hfs hds1 ⟨z, by rw [← hzz]; exact hv1m, hz⟩
        have hFEq : H.face f = H.face f2 := hbij _ _ hfs hds1 hEq
        have hmem : f2 ∈ H.face f := by rw [hFEq]; exact H.mem_face_self f2
        exact H.isInComponent_trans hfD (hfacecomp f hfDd f2 hmem)
      · -- t1 < 1：分量的开性把 TA 推过 t1
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
          (OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan hconf
            (dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hfs))
          ((1 - t1) • y + t1 • z) hv1m
        have hε2 : 0 < ε / (2 * ‖z - y‖) := div_pos hε (by positivity)
        have hdl0 : 0 < min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2) :=
          lt_min hε2 (by linarith)
        have hdl1 : t1 + min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2) ≤ 1 := by
          have h2 : min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2) ≤ (1 - t1) / 2 := min_le_right _ _
          linarith
        have hdlmem : (1 - (t1 + min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2))) • y +
            (t1 + min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2)) • z ∈
            dartsetLeadsIntoFan x V E (H.face f) := by
          refine hball (Metric.mem_ball.mpr ?_)
          rw [hstepn (t1 + _)]
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t1 + _ - t1)]
          calc (t1 + _ - t1) * ‖z - y‖ = (min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2)) * ‖z - y‖ := by
                ring
            _ ≤ (ε / (2 * ‖z - y‖)) * ‖z - y‖ :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ = ε / 2 := by field_simp
            _ < ε := by linarith
        exact absurd (hbdd _ ⟨by linarith, hdl1, f, hfD, hdlmem⟩)
          (by have h := hbdd _ ⟨by linarith, hdl1, f, hfD, hdlmem⟩
              have hp : 0 < min (ε / (2 * ‖z - y‖)) ((1 - t1) / 2) := hdl0
              linarith)
    · -- ### P3(iii)/(iv)：t1 ∉ TA
      have hv1seg : (1 - t1) • y + t1 • z ∈ segment ℝ y z :=
        ⟨1 - t1, t1, by linarith, by linarith, by ring, rfl⟩
      have hv1Z : (1 - t1) • y + t1 • z ∈
          (Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v} := hseg hv1seg
      have hunion := yfan_union_aff_gt_fan x V E ⟨hfan, hcard, hfan80⟩
      rw [← hunion] at hv1Z
      rcases hv1Z with hv1y | hv1G
      · -- v1 ∈ yfan：开性 + 步退给 t1 ∈ TA，矛盾
        obtain ⟨f₀, hf₀S, heq₀⟩ := version_JUTSTKG x V E
          (connectedComponentIn (yfan x V E) ((1 - t1) • y + t1 • z)) hfan hcard hfan80
          ⟨(1 - t1) • y + t1 • z, hv1y, rfl⟩
        have hopen : IsOpen (connectedComponentIn (yfan x V E) ((1 - t1) • y + t1 • z)) := by
          rw [← heq₀]
          exact OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan hconf
            (dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hf₀S)
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen ((1 - t1) • y + t1 • z)
          (mem_connectedComponentIn hv1y)
        have hε2 : 0 < ε / (2 * ‖z - y‖) := div_pos hε (by positivity)
        obtain ⟨a, haTA, ha1⟩ : ∃ a ∈ TA, t1 - ε / (2 * ‖z - y‖) < a := by
          by_contra hcon
          push_neg at hcon
          have hs := csSup_le ⟨0, h0TA⟩ hcon
          rw [ht1def] at hs
          linarith
        have haTAmem := haTA
        obtain ⟨hage0, -, f₃, hf₃D, hy₃⟩ := haTA
        have hf₃d : f₃ ∈ H.darts := Finset.mem_coe.mp (H.combComponent_subset_darts hf1H hf₃D)
        have hf₃S : H.face f₃ ∈ H.faceSet := (H.mem_darts_iff_face_mem f₃).mp hf₃d
        have hclt : a < t1 :=
          lt_of_le_of_ne (hbdd a haTAmem) fun heq => ht1 (by rw [← heq]; exact haTAmem)
        have hdist : dist ((1 - a) • y + a • z) ((1 - t1) • y + t1 • z) < ε := by
          rw [hstepn a, abs_of_nonpos (by linarith : a - t1 ≤ 0), neg_sub]
          calc (t1 - a) * ‖z - y‖ < (ε / (2 * ‖z - y‖)) * ‖z - y‖ :=
              mul_lt_mul_of_pos_right (by linarith) (by positivity)
            _ = ε / 2 := by field_simp
            _ < ε := by linarith
        have hy₃' : (1 - a) • y + a • z ∈ dartsetLeadsIntoFan x V E f₀ := by
          rw [heq₀]
          exact hball (Metric.mem_ball.mpr hdist)
        have hEq := hblockEq f₀ (H.face f₃) hf₀S hf₃S ⟨(1 - a) • y + a • z, hy₃', hy₃⟩
        suffices hcontra : t1 ∈ TA by exact absurd hcontra ht1
        refine ⟨h0le, ht1le1, f₃, hf₃D, ?_⟩
        rw [← hEq, heq₀]
        exact mem_connectedComponentIn hv1y
      · -- v1 ∈ affGt {x} {e}：几何链主分支
        simp only [Set.mem_iUnion, Set.mem_iUnion₂] at hv1G
        obtain ⟨e, heE, hv1e⟩ := hv1G
        obtain ⟨hfin, hcard2⟩ := hfan.2.1 e heE
        obtain ⟨p, q, hpq, he⟩ := Finset.card_eq_two.mp hcard2
        have heqE : e = ({p, q} : Set V3) := by
          rw [← hfin.coe_toFinset, he]
          simp
        rw [heqE] at hv1e
        have hv1e' : (1 - t1) • y + t1 • z ∈ affGt ({x} : Set V3) ({p, q} : Set V3) := hv1e
        have hpV : p ∈ V := hfan.1 (Set.mem_sUnion.mpr ⟨e, heE, by rw [heqE]; simp⟩)
        have hqV : q ∈ V := hfan.1 (Set.mem_sUnion.mpr ⟨e, heE, by rw [heqE]; simp⟩)
        have hpqE : ({p, q} : Set V3) ∈ E := by rw [← heqE]; exact heE
        rcases eq_or_lt_of_le ht1le1 with h1 | hlt1
        · -- t1 = 1：v1 = z ∈ affGt ⇒ z ∈ xfan，与 z ∈ yfan 矛盾
          have hzY : z ∈ yfan x V E := dartset_leads_into_subset_yfan hfan hcard hfan80 hds1 hz
          have hzG : z ∈ affGt ({x} : Set V3) ({p, q} : Set V3) := by
            have hzz : (1 - t1) • y + t1 • z = z := by rw [h1]; simp
            rw [← hzz]; exact hv1e'
          have hGGt : ∀ r : Set V3, affGt ({x} : Set V3) r ⊆ affGe ({x} : Set V3) r := by
            intro r w hw
            simp only [affGt, Set.mem_setOf_eq, Affsign] at hw
            simp only [affGe, Set.mem_setOf_eq, Affsign]
            obtain ⟨f, hfin2, hcomb, hpos, hone⟩ := hw
            exact ⟨f, hfin2, hcomb, fun u hu => le_of_lt (hpos u hu), hone⟩
          have hzxfan : z ∈ xfan x V E := ⟨({p, q} : Set V3), hpqE, hGGt _ hzG⟩
          rw [yfan, Set.mem_sdiff] at hzY
          exact absurd hzxfan hzY.2
        · -- t1 < 1：几何链 + 组件链 ⇒ 相邻面 dart ∈ D，再由 TA 反推
          have heEne : E ≠ ∅ := by
            intro h
            have hmem : ({f1.1, f1.2} : Set V3) ∈ E := by simpa [dart1OfFan] using hf1d
            rw [h] at hmem
            simp at hmem
          have hyY : y ∈ yfan x V E := dartset_leads_into_subset_yfan hfan hcard hfan80 hds hy
          have hzY : z ∈ yfan x V E := dartset_leads_into_subset_yfan hfan hcard hfan80 hds1 hz
          have ht1pos : 0 < t1 := lt_of_le_of_ne h0le fun he => ht1 (he ▸ h0TA)
          have hv1t : (1 - t1) • y + t1 • z = (1 - t1) • y + t1 • z := rfl
          obtain ⟨δ, t''', hδ0, ht0, ht1b, hcases⟩ :=
            connect_geom_aux x V E hfan hconf hcard hfan80 heEne
              (v := p) (w := q) (t1 := t1) hpV hqV hpqE hyz hyY hzY rfl ht1pos hlt1
              (fun s hs0 hs1 => hseg ⟨1 - s, s, by linarith, by linarith, by ring, rfl⟩) hv1e'
          -- 相邻面 dart (q,p), (p,q) 属于 dart 集与 faceSet
          have hpqE' : ({q, p} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hpqE
          have hdqp : (q, p) ∈ dart1OfFan V E := by simpa [dart1OfFan] using hpqE'
          have hdpq : (p, q) ∈ dart1OfFan V E := by simpa [dart1OfFan] using hpqE
          have hdqpd : (q, p) ∈ H.darts :=
            (finite_dart1_fan hfan).mem_toFinset.mpr hdqp
          have hdpqd : (p, q) ∈ H.darts :=
            (finite_dart1_fan hfan).mem_toFinset.mpr hdpq
          have hdqpS : H.face (q, p) ∈ H.faceSet := (H.mem_darts_iff_face_mem _).mp hdqpd
          have hdpqS : H.face (p, q) ∈ H.faceSet := (H.mem_darts_iff_face_mem _).mp hdpqd
          -- sup 密度取 a ∈ TA 靠近 t1
          obtain ⟨a, haTA, ha1⟩ : ∃ a ∈ TA, t1 - δ < a := by
            by_contra hcon
            push_neg at hcon
            have hs := csSup_le ⟨0, h0TA⟩ hcon
            rw [ht1def] at hs
            linarith
          have haTAmem := haTA
          obtain ⟨hage0, -, fd, hfdD, hyd⟩ := haTA
          have hcltB : a < t1 :=
            lt_of_le_of_ne (hbdd a haTAmem) fun heq => ht1 (by rw [← heq]; exact haTAmem)
          have hfdd : fd ∈ H.darts := Finset.mem_coe.mp (H.combComponent_subset_darts hf1H hfdD)
          have hfdS : H.face fd ∈ H.faceSet := (H.mem_darts_iff_face_mem fd).mp hfdd
          -- 下方点 ⇒ face fd = face F1 ⇒ F1 ∈ 组件
          have hwinOf : ∀ F1 : V3 × V3, F1 ∈ H.darts → H.face F1 ∈ H.faceSet →
              (∀ s : ℝ, 0 < s → s ≤ δ → s ≤ t1 →
                (1 - (t1 - s)) • y + (t1 - s) • z ∈
                  dartsetLeadsIntoFan x V E (H.face F1)) →
              F1 ∈ H.combComponent f1 := by
            intro F1 hF1d hF1S hbelow
            have hcp : t1 - (t1 - a) = a := by ring
            have hcommon : (1 - a) • y + a • z ∈
                dartsetLeadsIntoFan x V E (H.face F1) := by
              have h := hbelow (t1 - a) (by linarith) (by linarith) (by linarith)
              rwa [hcp] at h
            have hEq := hblockEq (H.face fd) (H.face F1) hfdS hF1S
              ⟨(1 - a) • y + a • z, hyd, hcommon⟩
            have hFEq : H.face fd = H.face F1 := hbij _ _ hfdS hF1S hEq
            have h₂ : F1 ∈ H.face fd := by rw [hFEq]; exact H.mem_face_self F1
            exact H.isInComponent_trans hfdD (hfacecomp fd hfdd _ h₂)
          -- 组件对 edgeMap 封闭：F2 = edgeMap F1 ∈ 组件
          have hstep : ∀ {A B : V3 × V3}, A ∈ H.combComponent f1 → H.edgeMap A = B →
              B ∈ H.combComponent f1 := by
            intro A B hA hE
            refine H.isInComponent_trans hA ⟨fun i => if i = 0 then A else B, 1, ?_, ?_, ?_⟩
            · simp
            · simp
            · rw [H.isPath_succ]
              exact ⟨True.intro, Or.inl hE.symm⟩
          have hE1 : H.edgeMap (q, p) = (p, q) :=
            hypermapOfFan_edgeMap_eq_eFanPair_ca23 hfan hdqp
          have hE2 : H.edgeMap (p, q) = (q, p) :=
            hypermapOfFan_edgeMap_eq_eFanPair_ca23 hfan hdpq
          -- t' = t1 + (1-t1)*t''' ∈ TA ⇒ 与 hbdd 矛盾
          have hid : (1 - t''') • ((1 - t1) • y + t1 • z) + t''' • z
              = (1 - (t1 + (1 - t1) * t''')) • y + (t1 + (1 - t1) * t''') • z := by
            module
          have hb0 : 0 ≤ t1 + (1 - t1) * t''' := by
            have hA : 0 ≤ 1 - t1 := by linarith
            have hB : 0 ≤ t''' := le_of_lt ht0
            have hp := mul_nonneg hA hB
            linarith
          have hb1 : t1 + (1 - t1) * t''' ≤ 1 := by
            have hA : 0 ≤ 1 - t1 := by linarith
            have hp : (1 - t1) * t''' ≤ (1 - t1) * 1 := mul_le_mul_of_nonneg_left ht1b hA
            linarith
          rcases hcases with ⟨hbelow, habove⟩ | ⟨hbelow, habove⟩
          · have hwin2 : (p, q) ∈ H.combComponent f1 :=
              hstep (hwinOf (q, p) hdqpd hdqpS hbelow) hE1
            have hpt : (1 - (t1 + (1 - t1) * t''')) • y + (t1 + (1 - t1) * t''') • z
                ∈ dartsetLeadsIntoFan x V E (H.face (p, q)) := by
              rw [← hid]; exact habove
            exact absurd (hbdd _ ⟨hb0, hb1, (p, q), hwin2, hpt⟩)
              (by have h := hbdd _ ⟨hb0, hb1, (p, q), hwin2, hpt⟩
                  have hprod : 0 < (1 - t1) * t''' := mul_pos (by linarith) ht0
                  linarith)
          · have hwin2 : (q, p) ∈ H.combComponent f1 :=
              hstep (hwinOf (p, q) hdpqd hdpqS hbelow) hE2
            have hpt : (1 - (t1 + (1 - t1) * t''')) • y + (t1 + (1 - t1) * t''') • z
                ∈ dartsetLeadsIntoFan x V E (H.face (q, p)) := by
              rw [← hid]; exact habove
            exact absurd (hbdd _ ⟨hb0, hb1, (q, p), hwin2, hpt⟩)
              (by have h := hbdd _ ⟨hb0, hb1, (q, p), hwin2, hpt⟩
                  have hprod : 0 < (1 - t1) * t''' := mul_pos (by linarith) ht0
                  linarith)

/-- `setOfComponents` 成员形式的逆（HOL `lemma_component_identity` 的来源之一）：
分量集中的分量都是某 dart 的 `combComponent`。 -/
private theorem hypermapOfFan_setOfComponents_inv_ca23 (H : Hypermap (V3 × V3))
    {S : Set (V3 × V3)} (hS : S ∈ H.setOfComponents) :
    ∃ z ∈ H.darts, H.combComponent z = S := by
  have h : H.setOfComponents =
      (fun y : V3 × V3 => H.combComponent y) '' (↑H.darts : Set (V3 × V3)) := by
    ext t
    simp [Hypermap.setOfComponents, Hypermap.setPartComponents]
  rw [h] at hS
  simp only [Set.mem_image] at hS
  obtain ⟨z, hz, hzS⟩ := hS
  exact ⟨z, Finset.mem_coe.mp hz, hzS⟩

/-- HOL `lemma_component_identity`：`setOfComponents` 中两个含公共 dart 的分量相等
（`partition_components` 的二分 + 非空交排除）。 -/
private theorem hypermapOfFan_component_identity_ca23 (H : Hypermap (V3 × V3))
    {D₁ D₂ : Set (V3 × V3)} (h₁ : D₁ ∈ H.setOfComponents) (h₂ : D₂ ∈ H.setOfComponents)
    {w : V3 × V3} (hw₁ : w ∈ D₁) (hw₂ : w ∈ D₂) : D₁ = D₂ := by
  obtain ⟨z₁, -, rfl⟩ := hypermapOfFan_setOfComponents_inv_ca23 H h₁
  obtain ⟨z₂, -, rfl⟩ := hypermapOfFan_setOfComponents_inv_ca23 H h₂
  rcases H.partition_components z₁ z₂ with heq | hdis
  · exact heq
  · have hcap : (H.combComponent z₁ ∩ H.combComponent z₂).Nonempty := ⟨w, hw₁, hw₂⟩
    rw [hdis] at hcap
    exact absurd hcap Set.not_nonempty_empty

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
  -- P1：取 dart `f1 = (v,u)`（`fan1` 给 `V` 非空，边度 `> 1` 给邻居 `u`）
  have hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard := hconf.1
  have hdart_eq : dartOfFan V E = dart1OfFan V E :=
    dartOfFan_eq_dart1_of_surrounded hfan hcard
  obtain ⟨v, hvV⟩ := Set.nonempty_iff_ne_empty.mpr hfan.2.2.1.2
  obtain ⟨u, huE, -⟩ := exists_inf_element_fix_fan x v v V E hfan hvV (hcard v hvV)
  have hf1 : (v, u) ∈ dart1OfFan V E := by
    simp only [dart1OfFan, Set.mem_setOf_eq]
    exact huE.1
  have hf1H : (v, u) ∈ (hypermapOfFan x V E hfan).darts := by
    show (v, u) ∈ (finite_dart1_fan hfan).toFinset
    exact (finite_dart1_fan hfan).mem_toFinset.mpr hf1
  set H := hypermapOfFan x V E hfan with hHdef
  have hDmem : H.combComponent (v, u) ∈ H.setOfComponents :=
    hypermapOfFan_mem_setOfComponents H hf1H
  -- P2：任何 dart `y` 与 `f1` 同分量（`lemma_connect_hypermap` + 组件恒等）
  have hconn : ∀ y ∈ H.darts, y ∈ H.combComponent (v, u) := by
    intro y hyH
    have hy1 : y ∈ dart1OfFan V E := by
      rw [← hypermapOfFan_darts_coe x V E hfan]
      exact hyH
    obtain ⟨D₀, hD₀mem, hf1D₀, hyD₀⟩ :=
      lemma_connect_hypermap x V E (v, u) y hfan hconf hcard hconf.2.1
        (hdart_eq ▸ hf1) (hdart_eq ▸ hy1)
    have hD₀eq : D₀ = H.combComponent (v, u) :=
      hypermapOfFan_component_identity_ca23 H hD₀mem hDmem hf1D₀
        (H.mem_combComponent_self (v, u))
    rw [hD₀eq] at hyD₀
    exact hyD₀
  -- P3：分量集为单点集 `{combComponent (v,u)}`
  have hset : H.setOfComponents = {H.combComponent (v, u)} := by
    ext S
    constructor
    · intro hS
      obtain ⟨z, hzH, hzS⟩ := hypermapOfFan_setOfComponents_inv_ca23 H hS
      rw [← hzS, Set.mem_singleton_iff]
      exact hypermapOfFan_component_identity_ca23 H
        (hypermapOfFan_mem_setOfComponents H hzH) hDmem
        (H.mem_combComponent_self z) (hconn z hzH)
    · intro hS
      rw [Set.mem_singleton_iff] at hS
      rw [hS]
      exact hDmem
  -- P4：连通 = 分量数为 1
  show H.numberOfComponents = 1
  show H.setOfComponents.ncard = 1
  rw [hset, Set.ncard_singleton]

/-- `hypermapOfFan` 的 dart 集合即 `dart1OfFan`（二元组 dart 集）。 -/
private theorem hypermapOfFan_coe_darts_ca (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) :
    (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E :=
  (finite_dart1_fan hfan).coe_toFinset

/-- `hypermapOfFan` 的 `edgeMap` 在 dart 上就是 `eFanPair`
（对应 HOL `hypermap_of_fan_rep` 的 e-分量）。 -/
private theorem hypermapOfFan_edgeMap_eq_ca (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).edgeMap d = eFanPair V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-- dart 集外 `edgeMap` 恒等。 -/
private theorem hypermapOfFan_edgeMap_fix_out_ca (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∉ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).edgeMap d = d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_neg (by simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-- HOL `plain_hypermap_fan`：`hypermapOfFan` 的 `edgeMap` 是对合。 -/
private theorem plainEdgeMap_fan_ca (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E) :
    (hypermapOfFan x V E hfan).edgeMap * (hypermapOfFan x V E hfan).edgeMap = 1 := by
  refine Equiv.Perm.ext fun d => ?_
  by_cases hd : d ∈ dart1OfFan V E
  · have h1 := hypermapOfFan_edgeMap_eq_ca x V E hfan hd
    have h2 := hypermapOfFan_edgeMap_eq_ca x V E hfan (eFanPair_mem_dart1 hd)
    simp only [Equiv.Perm.mul_apply, h1, h2, eFanPair_sq d hd, Equiv.Perm.one_apply]
  · simp only [Equiv.Perm.mul_apply, hypermapOfFan_edgeMap_fix_out_ca x V E hfan hd,
      Equiv.Perm.one_apply]

/-- HOL `e_fan_no_fix_point`（hypermapOfFan 打包形态）。 -/
private theorem edgeNoFix_fan_ca (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E) :
    ∀ d ∈ (hypermapOfFan x V E hfan).darts, (hypermapOfFan x V E hfan).edgeMap d ≠ d := by
  intro d hd
  have hd1 : d ∈ dart1OfFan V E := by
    rw [← hypermapOfFan_coe_darts_ca x V E hfan]
    exact hd
  rw [hypermapOfFan_edgeMap_eq_ca x V E hfan hd1]
  exact e_fan_no_fix hfan d hd1

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
  have hmem : e ∈ setOfOrbits (hypermapOfFan x V E hfan).darts
      (hypermapOfFan x V E hfan).edgeMap := he
  simp only [setOfOrbits] at hmem
  obtain ⟨d, hd, rfl⟩ := hmem
  exact (orbitMap_finite_ncard_two
    (hypermapOfFan x V E hfan).edgeMap_permutes
    (plainEdgeMap_fan_ca x V E hfan)
    (edgeNoFix_fan_ca x V E hfan) hd).2

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
  set H := hypermapOfFan x V E hfan
  have hedge : ∀ d ∈ H.darts, (orbitMap H.edgeMap d).ncard = 2 := fun d hd =>
    (orbitMap_finite_ncard_two H.edgeMap_permutes
      (plainEdgeMap_fan_ca x V E hfan) (edgeNoFix_fan_ca x V E hfan) hd).2
  have h := ncard_eq_mul_numberOfOrbits H.edgeMap_permutes hedge
  rw [Set.ncard_coe_finset] at h
  rw [h]
  have hE : numberOfOrbits H.darts H.edgeMap = H.edgeSet.ncard := rfl
  rw [hE]
  push_cast
  ring

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

/-
Port of the HOL Light Flyspeck polyhedron theory (Packing chapter), slice 7
(FINAL batch): skeleton pass of `scripts/polyhedron.hl` :1823-:3200 — the
theorems whose `let ... = prove` starts in :1823-:3200, exactly 10.

Source: `lean/scripts/polyhedron.hl` (persistent copy of Flyspeck book
formalization `text_formalization/packing/polyhedron.hl`, John Harrison +
Hoang Le Truong, 2010-2011).

Coverage (batch 7, FINAL):
- `SUR_FCHANGED` (:1823)
- `AMHFNXP` (:1855)
- `AMHFNXP_BIJ` (:1875)
- `EXPAND_EDGE_POLYTOPE` (:1893)
- `EXISTS_EDGE_AT_VERTICES` (:1932)
- `FLVNSME` (:2005-:2995, batch centerpiece — the file's ~1000-line giant:
  every vertex lies on an edge reaching into the open halfspace opposite
  the facet normal)
- `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON` (:2996)
- `BSXAQBQ` (:3028)
- `POLYTOPE_FAN80` (:3090)
- `WBLARHH` (:3158)
Not assigned: `WBLARHH_BIJ` (:3189-:3200) is a `prove_by_refinement`
corollary of WBLARHH + `PIIJBJK` (ConformingAuto21.lean:903); it does not
start a `let = prove` in the assigned window and is left to the fill-in
pass of whichever batch owns the WBLARHH proof.

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs are `by sorry`, to be filled by the auto_loop harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  `t % v` ↔ `t • v`; `vec 0` ↔ `(0 : V3)`; `dot` ↔ `⬝ᵥ` (Kepler/Geom/
  Azim.lean:40).
- HOL `relative_interior s` ↔ `intrinsicInterior ℝ s`
  (Mathlib/Analysis/Convex/Intrinsic.lean:61; precedent: PolyAuto4 header).
- HOL `bounded s` ↔ `Bornology.IsBounded s`; HOL `interior` ↔ Mathlib
  `interior`.
- `fchanged` (:512), `polyhedron` (polytope1.ml:2546), `face_of`
  (polytope1.ml:22), `facet_of` (polytope1.ml:1506) and `aff_dim` are
  ported here VERBATIM as private `_p7` copies `fchanged_p7`/
  `polyhedron_p7`/`FaceOf_p7`/`FacetOf_p7`/`affDim_p7` because the
  concurrent batch 3/4 lanes own the public names (PolyAuto3/PolyAuto4 are
  NOT imported: batches are parallel lanes; the bodies are token-identical
  to the polytope1.ml originals). Merge note: when the public copies land,
  delete these `_p7` copies and re-point; nothing else in this file needs
  to change.
- `vertices s = {x | x extreme_point_of s}` (flyspeck_multivariate.ml:6884)
  is INLINED as `Set.extremePoints ℝ p` (Mathlib Analysis/Convex/
  Extreme.lean:68), following the PolyAuto3 POLYHEDRON_FAN precedent —
  this file's statements share V/E with PolyAuto3.POLYHEDRON_FAN verbatim,
  so the fill-in proofs can instantiate it without bridging.
- `edges s = {{v,w} | segment[v,w] edge_of s}` (flyspeck_multivariate.ml
  :6887) is ported as `edges_p7`: `edge_of` (polytope.ml:2847:
  `e face_of s /\ aff_dim e = &1`) is inlined, the face_of body verbatim
  (PolyAuto3 precedent) and the affine-dimension condition `aff_dim
  (segment[v,w]) = &1` encoded by its segment-equivalent `v ≠ w` (this
  Mathlib has no affine-dimension API on segments; PolyAuto3 made the same
  call inside POLYHEDRON_FAN).
- HOL `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); `set_of_edge` ↔ `setOfEdge` (Fan.lean:62);
  `azim_fan` ↔ `azimFan` (Fan.lean:177); `fan80` ↔ `fan80` (Fan.lean:227);
  `FAN` ↔ `FAN` (Fan.lean:56); `CARD s > 1` ↔ `1 < s.ncard`.
- HOL `d_fan (x,V,E) = d1_fan ∪ d20_fan` (fan.hl:2302) ↦ `dartOfFan V E`
  (Fan.lean:90; apex dropped, pair darts — ConformingDefs.lean header
  precedent); `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`.
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL `hypermap1_of_fanx
  (x,V,E)` is NOT ported: `face_set (hypermap1_of_fanx ...)` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` with pair darts, carrying an
  explicit `hfan : FAN x V E` witness (ConformingDefs.lean header
  precedent; the only signature deviation from HOL, affecting WBLARHH).
- HOL `BIJ f s t` (INJ + SURJ) ↔ `Set.BijOn f s t`.
- HOL `?!x. P x` ↔ `∃! x, P x`.
- Imports: `PlanarityAuto16` + `ConformingDefs` per batch plan, plus
  `PolyAuto5`（诚实 FCHANGED 三件套 `FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`/
  `EXISTS_EDGE_POLYTOPE` + `AFF_DIM_INTERIOR_EQ_3`；Polytope.lean 公开
  面论基座随之引入，其公开 `FaceOf`/`FacetOf`/`affDim`/`fchanged` 与本
  文件 `_p7` 私有副本逐字定义等价——`exact`/`apply` 按定义等价直接互
  通）、`PolyAuto3`（`POLYHEDRON_FAN`，V/E 编码逐字一致、语句冻结可
  用）与 `Mathlib` for `intrinsicInterior`, `Set.extremePoints`,
  `segment`, `interior`。构建注意：lane 的 `.lake` 缺 Polytope/PolyAuto5/
  PolyAuto3 新鲜 olean 时，以
  `lake env lean -o <olean> Kepler/Text/<模块>.lean` 单模块补建（本
  lane 已按此补建三枚；未动 `lake build`）。

Difficulty scale (for the fill-in pass): zuzhuang = assembly of already
ported lemmas; liangou = coefficient/rewriting bookkeeping; fenxi =
geometric content.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.PolyAuto5
import Kepler.Text.PolyAuto3
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 上游定义私有副本（HOL 原文逐字移植；见文件头「合并去重」说明） -/

/-- HOL `aff_dim`（polytope1.ml，逐字；∅ ↦ -1，否则仿射包方向的维数）。
私有副本：公开名 `affDim` 在并发批 4 lane（PolyAuto4.lean:90），本 lane
不导入 PolyAuto*。 -/
noncomputable def affDim_p7 (s : Set V3) : ℤ :=
  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)

/-- HOL `t face_of s`（polytope1.ml:22，flyspeck Definition 4.7 QLITJET）：
```
t SUBSET s /\ convex t /\
!a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t
```
（HOL `segment(a,b)` 为开段 ↦ `openSegment ℝ a b`。）私有副本：公开名
`FaceOf` 在并发批 4 lane（PolyAuto4.lean:99）。 -/
def FaceOf_p7 (t s : Set V3) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : V3, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t

/-- HOL `f facet_of s`（polytope1.ml:1506）：
```
f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1
```
私有副本：公开名 `FacetOf` 在并发批 4 lane（PolyAuto4.lean:108）。 -/
def FacetOf_p7 (f s : Set V3) : Prop :=
  FaceOf_p7 f s ∧ f ≠ ∅ ∧ affDim_p7 f = affDim_p7 s - 1

/-- HOL `polyhedron s`（polytope1.ml:2546，flyspeck Definition 4.8 QSRHLXB）：
```
polyhedron s <=> ?f. FINITE f /\ s = INTERS f /\
  (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})
```
私有副本：公开名 `polyhedron` 在并发批 4 lane（PolyAuto4.lean:117）。 -/
def polyhedron_p7 (s : Set V3) : Prop :=
  ∃ F : Set (Set V3), F.Finite ∧ s = ⋂₀ F ∧
    ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}

/-- HOL `fchanged`（polyhedron.hl:512，`new_definition`，逐字移植）：
```
fchanged f={v| ?v1 t. v=t% v1 /\ v1 IN (relative_interior f)/\ t> &0}
```
即 `f` 相对内部各点出发的正射线之并。私有副本：公开名 `fchanged` 在并发
批 4 lane（PolyAuto4.lean:126，同样逐字移植自 :512）；合并时删一份并
重指。 -/
def fchanged_p7 (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-- HOL `edges s`（flyspeck_multivariate.ml:6887）：
```
edges s = {{v,w} | segment[v,w] edge_of s}
```
`edge_of`（polytope.ml:2847：`e face_of s /\ aff_dim e = &1`）就地内联：
face_of 条件按 `polytope1.ml:22` 逐字展开（PolyAuto3 POLYHEDRON_FAN 的
E-编码），`aff_dim (segment[v,w]) = &1` 以段上等价 `v ≠ w` 编码（本
Mathlib 无仿射维数 API；与 POLYHEDRON_FAN 完全一致，填充证明可直接
实例化之）。`vertices s`（flyspeck_multivariate.ml:6884）就地内联为
`Set.extremePoints ℝ p`。 -/
def edges_p7 (p : Set V3) : Set (Set V3) :=
  {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
    segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
    ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
      y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w}

/-! ## 填充辅助（session 1）：紧凸共线集为段（HOL COMPACT_CONVEX_COLLINEAR_SEGMENT
的 Mathlib 重建；供 EXPAND_EDGE_POLYTOPE 与 FLVNSME 阶段 6 共用） -/

/-- `vectorSpan ℝ {a, b} = ℝ ∙ (b - a)`（Mathlib 无现成对偶引理）。 -/
private theorem vectorSpan_pair_p7 (a b : V3) :
    vectorSpan ℝ {a, b} = ℝ ∙ (b - a) := by
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    intro z hz
    rw [Set.mem_vsub] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rw [vsub_self]
      exact Submodule.zero_mem _
    · refine Submodule.mem_span_singleton.2 ⟨-1, ?_⟩
      rw [neg_one_smul, vsub_eq_sub]
      module
    · refine Submodule.mem_span_singleton.2 ⟨1, ?_⟩
      rw [one_smul, vsub_eq_sub]
    · rw [vsub_self]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    have h := vsub_rev_mem_vectorSpan_pair ℝ a b
    rw [vsub_eq_sub] at h
    exact SetLike.mem_coe.2 h

/-- 直线 `affineSpan ℝ {a, b}` 的显式参数化。 -/
private theorem mem_affineSpan_pair_p7 {a b x : V3} :
    x ∈ (affineSpan ℝ {a, b} : Set V3) ↔ ∃ t : ℝ, x = a + t • (b - a) := by
  constructor
  · intro hx
    have ha : a ∈ (affineSpan ℝ {a, b} : Set V3) :=
      subset_affineSpan ℝ {a, b} (Set.mem_insert a {b})
    have hxa : (x - a) + a ∈ (affineSpan ℝ {a, b} : Set V3) := by
      rw [show (x - a) + a = x from by abel]
      exact hx
    have hx2 : x - a ∈ (affineSpan ℝ {a, b}).direction :=
      (AffineSubspace.vadd_mem_iff_mem_direction (v := x - a) (p := a) ha).1 hxa
    rw [direction_affineSpan, vectorSpan_pair_p7] at hx2
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hx2
    refine ⟨t, ?_⟩
    rw [show x = (x - a) + a from by abel, ht]
    abel
  · rintro ⟨t, rfl⟩
    have ha : a ∈ (affineSpan ℝ {a, b} : Set V3) :=
      subset_affineSpan ℝ {a, b} (Set.mem_insert a {b})
    have h2 : t • (b - a) ∈ (affineSpan ℝ {a, b}).direction := by
      rw [direction_affineSpan, vectorSpan_pair_p7]
      exact Submodule.mem_span_singleton.2 ⟨t, rfl⟩
    have hmem : t • (b - a) + a ∈ (affineSpan ℝ {a, b} : Set V3) :=
      (AffineSubspace.vadd_mem_iff_mem_direction
        (v := t • (b - a)) (p := a) ha).2 h2
    rw [add_comm] at hmem
    exact hmem

/-- 仿射参数化直线的区间像是段（仿射重参数化；t1 = t2 退化情形单独处理）。 -/
private theorem image_Icc_eq_segment_p7 (a e : V3) {t1 t2 : ℝ} (hle : t1 ≤ t2) :
    (fun t : ℝ => a + t • e) '' Set.Icc t1 t2 =
      segment ℝ (a + t1 • e) (a + t2 • e) := by
  rw [segment_eq_image_lineMap]
  refine Set.ext fun x => ?_
  by_cases h12 : t1 = t2
  · subst h12
    rw [Set.Icc_self, Set.image_singleton]
    constructor
    · intro hx
      refine ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [AffineMap.lineMap_same_apply]
      exact hx.symm
    · intro hx
      obtain ⟨lam, -, hlx⟩ := hx
      rw [AffineMap.lineMap_same_apply] at hlx
      rw [Set.mem_singleton_iff.2 hlx.symm]
      exact Set.mem_singleton _
  · have hpos : 0 < t2 - t1 := sub_pos.mpr (lt_of_le_of_ne hle h12)
    have hlamIcc : ∀ t ∈ Set.Icc t1 t2, (t - t1) / (t2 - t1) ∈ Set.Icc (0:ℝ) 1 := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith)⟩
    have hlammul : ∀ t : ℝ, (t - t1) / (t2 - t1) * (t2 - t1) = t - t1 :=
      fun t => by field_simp
    have hsub2 : a + t2 • e - (a + t1 • e) = (t2 - t1) • e := by
      module
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(t - t1) / (t2 - t1), hlamIcc t ht, ?_⟩
      rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, hsub2, smul_smul,
        hlammul t]
      module
    · rintro ⟨lam, hlamI, rfl⟩
      refine ⟨t1 + lam * (t2 - t1), ?_, ?_⟩
      · constructor
        · nlinarith [(Set.mem_Icc.mp hlamI).1, hle]
        · nlinarith [(Set.mem_Icc.mp hlamI).2, hle]
      · rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, hsub2, smul_smul]
        module

/-- 紧凸共线集是（可退化）段（HOL `COMPACT_CONVEX_COLLINEAR_SEGMENT`，
polytope.ml）。非空性必须显式（空集无端点）。 -/
private theorem compact_convex_subset_line {s : Set V3} (hcomp : IsCompact s)
    (hconv : Convex ℝ s) (hne : s.Nonempty) {a b : V3} (hab : a ≠ b)
    (hsub : s ⊆ affineSpan ℝ {a, b}) : ∃ c d, s = segment ℝ c d := by
  classical
  set e : V3 := b - a with he
  set F : ℝ → V3 := fun t => a + t • e with hFdef
  have he0 : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hFcont : Continuous F := by fun_prop
  set T : Set ℝ := F ⁻¹' s with hTdef
  have hmemT : ∀ t : ℝ, F t ∈ s ↔ t ∈ T := fun _ => Iff.rfl
  have hpre : ∀ x ∈ s, ∃ t : ℝ, F t = x ∧ t ∈ T := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_p7.1 (hsub hx)
    refine ⟨t, ht.symm, ?_⟩
    have hx2 : F t ∈ s := by
      rw [show F t = x from ht.symm]
      exact hx
    exact (hmemT t).mpr hx2
  have hsFT : s = F '' T := by
    refine Set.ext fun x => ?_
    constructor
    · intro hx
      obtain ⟨t, ht1, ht2⟩ := hpre x hx
      exact ⟨t, ht2, ht1⟩
    · rintro ⟨t, ht, rfl⟩
      exact (hmemT t).mp ht
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨t, -, ht2⟩ := hpre x hx
    exact ⟨t, ht2⟩
  have hTconv : Convex ℝ T := by
    intro u hu v hv α β hα hβ hab
    refine (hmemT _).mpr ?_
    have key : α • F u + β • F v = F (α * u + β * v) := by
      have e1 : α • a + β • a = a := by rw [← add_smul, hab, one_smul]
      have e2 : (α * u) • e + (β * v) • e = (α * u + β * v) • e := by
        rw [← add_smul]
      simp only [hFdef, smul_add, smul_smul, add_assoc, add_left_comm,
        ← add_smul, hab, one_smul]
      rw [← add_assoc, ← add_smul, hab, one_smul]
    have hmem' : α • F u + β • F v ∈ s :=
      hconv ((hmemT u).mp hu) ((hmemT v).mp hv) hα hβ hab
    rwa [key] at hmem'
  have hTclosed : IsClosed T := (hcomp.isClosed).preimage hFcont
  have hTbd : Bornology.IsBounded T := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : V3)).mp hcomp.isBounded
    rw [Metric.isBounded_iff_subset_ball (0 : ℝ)]
    refine ⟨(R + ‖a‖) / ‖e‖ + 1, fun t ht => ?_⟩
    have hFts : F t ∈ s := (hmemT t).mp ht
    have h1 : ‖F t‖ < R := by
      have h1' := Metric.mem_ball.1 (hR hFts)
      rwa [dist_zero_right] at h1'
    have hpos' : 0 < ‖e‖ := norm_pos_iff.mpr he0
    have h2 : ‖F t - a‖ ≤ ‖F t‖ + ‖a‖ := norm_sub_le _ _
    have h3 : ‖F t - a‖ = |t| * ‖e‖ := by
      simp only [hFdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h5 : |t| * ‖e‖ < R + ‖a‖ := by rw [h3.symm]; linarith
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    have h6 : |t| ≤ (R + ‖a‖) / ‖e‖ := by
      rw [le_div_iff₀ hpos']
      linarith
    linarith
  have hTcomp : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTclosed hTbd
  obtain ⟨t1, h1T, h1min⟩ := hTcomp.exists_isMinOn hTne continuousOn_id
  obtain ⟨t2, h2T, h2max⟩ := hTcomp.exists_isMaxOn hTne continuousOn_id
  have hle : t1 ≤ t2 := h1min h2T
  have hTIcc : ∀ t ∈ T, t ∈ Set.Icc t1 t2 := fun t ht => ⟨h1min ht, h2max ht⟩
  have hIccT : ∀ t ∈ Set.Icc t1 t2, t ∈ T := by
    intro t ht
    rw [← segment_eq_Icc hle, segment_eq_image_lineMap] at ht
    obtain ⟨lam, hlamI, rfl⟩ := ht
    exact hTconv.lineMap_mem h1T h2T hlamI
  have hTeq : T = Set.Icc t1 t2 :=
    Set.ext fun t => ⟨fun ht => hTIcc t ht, fun ht => hIccT t ht⟩
  refine ⟨F t1, F t2, ?_⟩
  rw [hsFT, hTeq, image_Icc_eq_segment_p7 a e hle]

/-- HOL polyhedron.hl :1893-:1930 `EXPAND_EDGE_POLYTOPE`

HOL 原文（对 `real^N` 一般陈述；本 lane 按仓库惯例特化到 `V3`）：
```
!f p:real^N->bool.
polytope p /\ f face_of p /\ aff_dim f= &1
==> ?a b. f= segment[a,b]
```

编码说明：HOL `polytope p`（`?t. FINITE t /\ p = convex hull t`，见
flyspeck_multivariate.ml:1579 `REWRITE_TAC[polytope]` 的用法）内联为
`∃ t : Set V3, t.Finite ∧ p = convexHull ℝ t`；`face_of`/`aff_dim` ↦
本文件 `FaceOf_p7`/`affDim_p7`；闭段 `segment[a,b]` ↦ `segment ℝ a b`。

证明思路（HOL）：`AFF_DIM f = &1` 给仿射基 `b` 且 `CARD b = 2`
（`AFF_DIM` 展开 + `INT_OF_NUM_EQ`）；`AFFINE_INDEPENDENT_IMP_FINITE` +
`CARD_EXISTS_2` 得 `b = {v,w}`；`FACE_OF_POLYTOPE_POLYTOPE`（面的多胞体
性）+ `POLYTOPE_IMP_COMPACT`/`POLYTOPE_IMP_CONVEX` 后
`f ⊆ affine hull {v,w}`（`HULL_SUBSET`），即 f 共线；最后
`COMPACT_CONVEX_COLLINEAR_SEGMENT`（polytope.ml）给
`f = segment[v,w]`（退化情形 `b = {v}` 由维数算术排除）。

候选已有引理：
- `FaceOf_p7`（本文件，展开即 `f ⊆ p`、`Convex ℝ f`）
- `convexHull`（Mathlib Analysis/Convex/Basic）
- 缺口：`AFF_DIM`-类展开、`COMPACT_CONVEX_COLLINEAR_SEGMENT`
  （「紧凸共线集是（可退化）段」）repo/Mathlib 均无现成引理；
  Mathlib 侧可由 `vectorSpan` 维数分类 + `segment` 的凸包刻画
  `convexHull_two` 重建
- 位置说明（本 hour）：原在 :1893 节；批 6 诚实核心的
  `yfan_subset_unions_fchanged_p7` 需前向引用本引理，故整块（语句 +
  docstring 原文）上移到核心节之前；`sorry` 保留（配额内 2 处之一）。 -/
theorem EXPAND_EDGE_POLYTOPE {f p : Set V3}
    (hp : ∃ t : Set V3, t.Finite ∧ p = convexHull ℝ t)
    (hf : FaceOf_p7 f p) (hdim : affDim_p7 f = 1) :
    ∃ a b : V3, f = segment ℝ a b := by
  classical
  obtain ⟨t, htfin, hpt⟩ := hp
  have hfconv : Convex ℝ f := hf.2.1
  -- p 凸、紧（多胞形）
  have hpconv : Convex ℝ p := by rw [hpt]; exact convex_convexHull ℝ t
  have hpcomp : IsCompact p := by rw [hpt]; exact htfin.isCompact_convexHull ℝ
  -- f 非空（否则维数 -1）
  have hfne : f ≠ ∅ := by
    intro h
    have h1 : affDim f = 1 := hdim
    rw [h, affDim_empty] at h1
    omega
  -- 维数 1 → vectorSpan 一维
  have hfvr : Module.finrank ℝ (vectorSpan ℝ f) = 1 := by
    have h1 : affDim f = 1 := hdim
    simp only [affDim, if_neg hfne] at h1
    exact_mod_cast h1
  have hnebot : vectorSpan ℝ f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfvr
    omega
  -- 取方向向量 d ≠ 0
  obtain ⟨d, hd, hd0⟩ : ∃ d : V3, d ∈ vectorSpan ℝ f ∧ d ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnebot ((Submodule.eq_bot_iff _).2 hcon)
  have h1 : (ℝ ∙ d : Submodule ℝ V3) ≤ vectorSpan ℝ f :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hd)
  have h2 : Module.finrank ℝ (ℝ ∙ d : Submodule ℝ V3) = 1 :=
    finrank_span_singleton hd0
  have hspan : (ℝ ∙ d : Submodule ℝ V3) = vectorSpan ℝ f :=
    Submodule.eq_of_le_of_finrank_eq h1 (by rw [h2, hfvr])
  -- f 闭（面 = affineSpan f ∩ p）→ 紧
  have haffclosed : IsClosed (affineSpan ℝ f : Set V3) := by
    obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hfne
    have hqaff : q ∈ (affineSpan ℝ f : Set V3) := subset_affineSpan ℝ f hq
    have hsetEq : (affineSpan ℝ f : Set V3) =
        (fun w : V3 => w - q) ⁻¹' ((affineSpan ℝ f).direction : Set V3) := by
      ext w
      rw [Set.mem_preimage]
      refine ⟨fun hw => ?_, fun hd' => ?_⟩
      · refine (AffineSubspace.vadd_mem_iff_mem_direction (v := w - q) (p := q) hqaff).1 ?_
        rw [vadd_eq_add, sub_add_cancel]
        exact hw
      · rw [SetLike.mem_coe] at hd'
        rw [← AffineSubspace.vadd_mem_iff_mem_direction (v := w - q) (p := q) hqaff] at hd'
        rw [vadd_eq_add, sub_add_cancel] at hd'
        exact hd'
    rw [hsetEq]
    exact IsClosed.preimage (continuous_sub_right q)
      (Submodule.closed_of_finiteDimensional _)
  have hfclosed : IsClosed f := by
    have hfeq : f = (affineSpan ℝ f : Set V3) ∩ p := by
      refine Set.ext fun x => ?_
      constructor
      · intro hx
        exact ⟨subset_affineSpan ℝ f hx, hf.1 hx⟩
      · rintro ⟨hxaff, hxp⟩
        exact faceOf_eq_affineInter hpconv hf ⟨hxaff, hxp⟩
    rw [hfeq]
    exact haffclosed.inter hpcomp.isClosed
  have hfcomp : IsCompact f :=
    Metric.isCompact_of_isClosed_isBounded hfclosed (hpcomp.isBounded.subset hf.1)
  -- KM 链：extremePoints f ⊆ extremePoints p ⊆ t ⇒ 有限（与 EXISTS_EDGE_AT_VERTICES
  -- 同构；末段用紧凸性直接下潜，此链作为 f 多胞形性的见证保留）
  have hfext : (Set.extremePoints ℝ f).Finite := by
    have h1 : Set.extremePoints ℝ f ⊆ Set.extremePoints ℝ p :=
      fun x hx => faceOf_sing.1 (FaceOf.trans (faceOf_sing.2 hx) hf)
    have h2 : Set.extremePoints ℝ p ⊆ t := by
      intro y hy
      rw [hpt] at hy
      exact extremePoints_convexHull_subset hy
    exact Set.Finite.subset htfin fun x hx => h2 (h1 hx)
  -- 共线：vectorSpan 一维 ⇒ f ⊆ affineSpan {a, a + d}
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hfne
  have hab : a ≠ a + d := by
    intro h
    have h2 : d = 0 := by
      have h3 := congrArg (fun z : V3 => z - a) h
      rw [sub_self, add_sub_cancel_left] at h3
      exact h3.symm
    exact hd0 h2
  have hsubline : f ⊆ affineSpan ℝ {a, a + d} := by
    intro x hx
    have hxv : x - a ∈ vectorSpan ℝ f := vsub_mem_vectorSpan ℝ hx ha
    rw [← hspan] at hxv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hxv
    rw [mem_affineSpan_pair_p7]
    refine ⟨t, ?_⟩
    rw [show (a + d) - a = d from by rw [add_sub_cancel_left], ht]
    abel
  exact compact_convex_subset_line hfcomp hfconv
    (Set.nonempty_iff_ne_empty.mpr hfne) hab hsubline

/-! ## 批 6 诚实核心（polyhedron.hl :1315-:1821，面向 `_p7` 编码就地重建）

原「冻结桥」依赖的批 6 私有副本编码已废弃：装配后 `Polytope.lean` 提供公开
逐字定义（`FaceOf`/`FacetOf`/`affDim`/`fchanged`/`polyhedron`，与本文件
`_p7` 副本 `exact` 按定义等价互通），PolyAuto5 提供诚实
`FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`/`EXISTS_EDGE_POLYTOPE`。批 6 模块
（PolyAuto6.lean）因批 4 闭段 `FacetOf` 与 Polytope 公开定义重名冲突已
不可导入，本节按各定理 docstring 的 HOL 原思路重建所需链条：
`⋃fchanged ⊆ yfan`（POLYHEDRON_COLLINEAR_FACES 两分支）、
`yfan ⊆ ⋃fchanged`（射线-前沿 = REDUCE_POINT_FACET_EXISTS 核心 + facet
相对内部分二分 + 一维面经 EXPAND_EDGE_POLYTOPE 下潜成边——按
EXISTS_EDGE_AT_VERTICES 既有先例作黑箱），拼装 `FCHANGED_EQ_YFAN`，
再以连通性（批 4 CONNECTED_FCHANGED 移植）+ 开二分分解得
`FCHANGED_IN_COMPONENT`。 -/

/-- 连通分量的对称性（批 4 `ccIn_symm` 移植）。 -/
private theorem ccIn_symm_p7 {F : Set V3} {a b : V3}
    (h : a ∈ connectedComponentIn F b) : b ∈ connectedComponentIn F a := by
  have hF : b ∈ F := connectedComponentIn_nonempty_iff.mp ⟨a, h⟩
  rw [← connectedComponentIn_eq h]
  exact mem_connectedComponentIn hF

/-- 连通分量的传递性（批 4 `CONNECTED_COMPONENT_TRANS` 移植）。 -/
private theorem ccIn_trans_p7 {F : Set V3} {a b c : V3}
    (h1 : a ∈ connectedComponentIn F b) (h2 : b ∈ connectedComponentIn F c) :
    a ∈ connectedComponentIn F c := by
  rw [connectedComponentIn_eq h2]
  exact h1

/-- 正射线 `{t • y | t > 0}` 连通（批 4 `CONNECTED_HALF_LINE1` 移植；
退化射线为单点，一般情形作 `Ioi 0` 在连续映射 `t ↦ t • y` 下的像）。 -/
private theorem isConnected_ray_p7 (y : V3) :
    IsConnected {v : V3 | ∃ t : ℝ, 0 < t ∧ v = t • y} := by
  by_cases hy : y = 0
  · subst hy
    have h0 : {v : V3 | ∃ t : ℝ, 0 < t ∧ v = t • (0 : V3)} = {0} := by
      ext v
      simp only [Set.mem_setOf_eq, smul_zero]
      constructor
      · rintro ⟨t, -, rfl⟩
        rfl
      · rintro rfl
        exact ⟨1, zero_lt_one, rfl⟩
    rw [h0]
    exact isConnected_singleton
  · have hset : {v : V3 | ∃ t : ℝ, 0 < t ∧ v = t • y}
        = (fun t : ℝ => t • y) '' Set.Ioi 0 := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, rfl⟩
    rw [hset]
    exact ((convex_Ioi 0).isConnected ⟨1, zero_lt_one⟩).image _
      ((continuous_id.smul continuous_const).continuousOn)

/-- facet 的 `fchanged` 连通（批 4 `CONNECTED_FCHANGED` 移植；`FacetOf`
只消耗凸性与非空性，对 face 编码的开/闭段分歧无差别）。 -/
private theorem isConnected_fchanged_p7 {P f : Set V3} (hf : FacetOf_p7 f P) :
    IsConnected (fchanged_p7 f) := by
  have hfne : f.Nonempty := Set.nonempty_iff_ne_empty.mpr hf.2.1
  have hiiConn : IsConnected (intrinsicInterior ℝ f) :=
    (convex_intrinsicInterior hf.1.2.1).isConnected
      (Set.Nonempty.intrinsicInterior hf.1.2.1 hfne)
  have key : ∀ u ∈ fchanged_p7 f, ∀ w ∈ fchanged_p7 f,
      u ∈ connectedComponentIn (fchanged_p7 f) w := by
    intro u hu w hw
    obtain ⟨v1, t, rfl, hv1, ht⟩ := hu
    obtain ⟨v1', t', rfl, hv1', ht'⟩ := hw
    -- 中段：v1 与 v1' 在 rint f 中同分量，搬进 fchanged f
    have h1mid : v1' ∈ connectedComponentIn (intrinsicInterior (𝕜 := ℝ) f) v1 :=
      hiiConn.2.subset_connectedComponentIn hv1 subset_rfl hv1'
    have hsubRI : intrinsicInterior (𝕜 := ℝ) f ⊆ fchanged_p7 f := fun v hv =>
      ⟨v, 1, by rw [one_smul], hv, zero_lt_one⟩
    have cMid : v1' ∈ connectedComponentIn (fchanged_p7 f) v1 := by
      refine connectedComponentIn_mono (x := v1) hsubRI ?_
      exact h1mid
    -- 左段：t • v1 与 v1 同分量（过 v1 的开射线连通）
    have cLeft : (t : ℝ) • v1 ∈ connectedComponentIn (fchanged_p7 f) v1 := by
      have hsub : {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1} ⊆ fchanged_p7 f := by
        rintro z ⟨s, hs, rfl⟩
        exact ⟨v1, s, rfl, hv1, hs⟩
      have hRay : v1 ∈
          connectedComponentIn {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1} (t • v1) :=
        (isConnected_ray_p7 v1).2.subset_connectedComponentIn ⟨t, ht, rfl⟩ subset_rfl
          ⟨1, zero_lt_one, by rw [one_smul]⟩
      exact ccIn_symm_p7 (connectedComponentIn_mono (t • v1) hsub hRay)
    -- 右段：t' • v1' 与 v1' 同分量
    have cRight : v1' ∈ connectedComponentIn (fchanged_p7 f) (t' • v1') := by
      have hsub : {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1'} ⊆ fchanged_p7 f := by
        rintro z ⟨s, hs, rfl⟩
        exact ⟨v1', s, rfl, hv1', hs⟩
      have hRay : v1' ∈
          connectedComponentIn {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1'} (t' • v1') :=
        (isConnected_ray_p7 v1').2.subset_connectedComponentIn ⟨t', ht', rfl⟩ subset_rfl
          ⟨1, zero_lt_one, by rw [one_smul]⟩
      exact connectedComponentIn_mono (t' • v1') hsub hRay
    exact ccIn_trans_p7 (ccIn_trans_p7 cLeft (ccIn_symm_p7 cMid)) cRight
  -- 取定点收尾：某点分量等于全集合
  obtain ⟨v0, hv0ii⟩ := Set.Nonempty.intrinsicInterior hf.1.2.1 hfne
  have hv0 : v0 ∈ fchanged_p7 f := ⟨v0, 1, by rw [one_smul], hv0ii, zero_lt_one⟩
  have hcc : connectedComponentIn (fchanged_p7 f) v0 = fchanged_p7 f :=
    Set.eq_of_subset_of_subset (connectedComponentIn_subset _ _)
      (fun z hz => key z hz v0 hv0)
  rw [← hcc]
  exact isConnected_connectedComponentIn_iff.mpr hv0

/-- 内点存在 ⇒ 仿射包全空间时 `rint = interior`（`mem_rint_iff` +
`INTERIOR_AFFINIE_HUL_EQ_UNIV`；HOL `RELATIVE_INTERIOR_INTERIOR` 的特例）。 -/
private theorem mem_rint_iff_interior_p7 {p : Set V3} (h0 : (0 : V3) ∈ interior p)
    {z : V3} : z ∈ intrinsicInterior ℝ p ↔ z ∈ interior p := by
  have haff : (affineSpan ℝ p : Set V3) = Set.univ := INTERIOR_AFFINIE_HUL_EQ_UNIV 0 p h0
  constructor
  · intro hmem
    obtain ⟨hzp, ε, hε, hball⟩ := mem_rint_iff.mp hmem
    exact mem_interior.mpr ⟨Metric.ball z ε,
      fun w hw => hball ⟨hw, by rw [haff]; trivial⟩, Metric.isOpen_ball,
      Metric.mem_ball_self hε⟩
  · intro hmem
    obtain ⟨t, htsub, htopen, hzt⟩ := mem_interior.mp hmem
    obtain ⟨ε, hε, hballt⟩ := Metric.isOpen_iff.mp htopen z hzt
    refine mem_rint_iff.mpr ⟨htsub hzt, ε, hε, ?_⟩
    intro w hw
    rw [haff] at hw
    exact htsub (hballt hw.1)

/-- 极点不含于内点集合（`faceOf_sing` + `faceOf_disjoint_rinterior` +
`AFF_DIM_INTERIOR_EQ_3`）。 -/
private theorem extremePoint_ne_zero_of_interior {p : Set V3} {v : V3}
    (hz : (0 : V3) ∈ interior p) (hv : v ∈ Set.extremePoints ℝ p) : v ≠ 0 := by
  intro hcon
  have h1 : FaceOf {v} p := faceOf_sing.mpr hv
  have h2 : (0 : V3) ∈ intrinsicInterior ℝ p := interior_subset_intrinsicInterior hz
  have h3 : ({v} : Set V3) ≠ p := by
    intro hcon2
    have h4 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
    rw [← hcon2, affDim_singleton] at h4
    norm_num at h4
  have h0v : (0 : V3) ∈ ({v} : Set V3) := by
    rw [Set.mem_singleton_iff]
    exact hcon.symm
  exact Set.disjoint_left.mp (faceOf_disjoint_rinterior h1 h3) h0v h2

/-- 开段点落在闭段相对内部（HOL `RELATIVE_INTERIOR_SEGMENT` 的成员形态）：
`affineSpan (segment a b) = affineSpan {a,b}` 上的球论证。 -/
private theorem openSegment_mem_rint_segment {a b z : V3} (hab : a ≠ b)
    (hz : z ∈ openSegment ℝ a b) : z ∈ intrinsicInterior ℝ (segment ℝ a b) := by
  obtain ⟨l, m, hl, hm, hlm, hze⟩ := hz
  have hlm' : l = 1 - m := by linarith
  have hsegsub : (segment ℝ a b : Set V3) ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := by
    intro w hw
    obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hw
    rw [AffineSubspace.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨d, ?_⟩
    have hcd' : c = 1 - d := by linarith
    rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, smul_sub, hcd',
      sub_smul, one_smul]
    abel
  have habsub : ({a, b} : Set V3) ⊆ (segment ℝ a b : Set V3) := by
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact left_mem_segment _ _ _
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact right_mem_segment _ _ _
  have hsegaff : (affineSpan ℝ (segment ℝ a b) : Set V3)
      = (affineSpan ℝ ({a, b} : Set V3) : Set V3) :=
    le_antisymm (affineSpan_le.mpr hsegsub) (affineSpan_mono ℝ habsub)
  have hmlt1 : m < 1 := by linarith
  rw [mem_rint_iff]
  refine ⟨⟨l, m, hl.le, hm.le, hlm, hze⟩, min m (1 - m) * ‖b - a‖,
    mul_pos (lt_min hm (by linarith)) (norm_sub_pos_iff.mpr (Ne.symm hab)), ?_⟩
  intro w hwb
  obtain ⟨hwball, hwaff⟩ := hwb
  rw [hsegaff, AffineSubspace.mem_coe,
    mem_affineSpan_pair_iff_exists_lineMap_eq] at hwaff
  obtain ⟨r, rfl⟩ := hwaff
  have hzlm : z = AffineMap.lineMap a b m := by
    have h1 : z = l • a + m • b := hze.symm
    rw [hlm'] at h1
    rw [h1, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, sub_smul, one_smul,
      smul_sub]
    abel
  have hbaneq : dist (AffineMap.lineMap a b r) z < min m (1 - m) * ‖b - a‖ := hwball
  rw [hzlm, dist_eq_norm] at hbaneq
  have hline : AffineMap.lineMap a b r - AffineMap.lineMap a b m
      = (r - m) • (b - a) := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply, vadd_eq_add, vadd_eq_add,
      vsub_eq_sub, add_sub_add_right_eq_sub, ← sub_smul]
  rw [hline, norm_smul, Real.norm_eq_abs] at hbaneq
  have hba0 : (0:ℝ) < ‖b - a‖ := norm_sub_pos_iff.mpr (Ne.symm hab)
  have hrm : |r - m| < min m (1 - m) := by
    rw [mul_comm |r - m| ‖b - a‖, mul_comm (min m (1 - m)) ‖b - a‖] at hbaneq
    exact lt_of_mul_lt_mul_left hbaneq hba0.le
  have hr1 : 0 < r := by
    have h2 := (abs_lt.mp hrm).1
    have h3 := min_le_left m (1 - m)
    linarith
  have hr2 : r < 1 := by
    have h2 := (abs_lt.mp hrm).2
    have h3 := min_le_right m (1 - m)
    linarith
  exact ⟨1 - r, r, by linarith, by linarith, by ring, by
    rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, sub_smul, one_smul,
      smul_sub]
    abel⟩

/-- 极点不落在异于其单点的面的相对内部（HOL `EXTREME_POINT_NOT_IN_
RELATIVE_INTERIOR` 的最小重建：沿仿射包对称逃逸）。 -/
private theorem extreme_notMem_rint_p7 {p f : Set V3} {e : V3}
    (he : e ∈ Set.extremePoints ℝ p) (hef : e ∈ intrinsicInterior ℝ f)
    (hff : FaceOf f p) (hfne : f ≠ {e}) : False := by
  have hef' : e ∈ f := (mem_rint_iff.mp hef).1
  obtain ⟨u, huf, hue⟩ : ∃ u ∈ f, u ≠ e := by
    by_contra hcon
    push_neg at hcon
    exact hfne (Set.eq_singleton_iff_unique_mem.mpr
      ⟨hef', fun z hz => hcon z hz⟩)
  obtain ⟨-, ε, hε, hball⟩ := mem_rint_iff.mp hef
  have hηp : (0:ℝ) < ‖u - e‖ := norm_sub_pos_iff.mpr hue
  set δ : ℝ := ε / (2 * ‖u - e‖) with hδ
  have hδp : 0 < δ := div_pos hε (mul_pos two_pos hηp)
  have hη0 : u - e ≠ 0 := sub_ne_zero.mpr hue
  -- e ± δ•(u-e) ∈ affineSpan f 且在球内，故 ∈ f ⊆ p
  have hsub2 : ({e, u} : Set V3) ⊆ f := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hef'
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact huf
  have hsub3 : ({e, u} : Set V3) ⊆ (affineSpan ℝ f : Set V3) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact subset_affineSpan ℝ f hef'
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact subset_affineSpan ℝ f huf
  have haff1 : e + δ • (u - e) ∈ (affineSpan ℝ f : Set V3) := by
    have h1 : AffineMap.lineMap e u δ ∈ affineSpan ℝ ({e, u} : Set V3) :=
      AffineMap.lineMap_mem_affineSpan_pair δ e u
    have h2 : AffineMap.lineMap e u δ = e + δ • (u - e) := by
      rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    rw [← h2]
    exact affineSpan_le.mpr hsub3 h1
  have haff2 : e - δ • (u - e) ∈ (affineSpan ℝ f : Set V3) := by
    have h1 : AffineMap.lineMap e u (-δ) ∈ affineSpan ℝ ({e, u} : Set V3) :=
      AffineMap.lineMap_mem_affineSpan_pair (-δ) e u
    have h2 : AffineMap.lineMap e u (-δ) = e - δ • (u - e) := by
      rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, neg_smul,
        sub_eq_add_neg]
    rw [← h2]
    exact affineSpan_le.mpr hsub3 h1
  have hd1 : dist (e + δ • (u - e)) e = δ * ‖u - e‖ := by
    rw [dist_eq_norm]
    have hv : e + δ • (u - e) - e = δ • (u - e) := by rw [add_sub_cancel_left]
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hδp]
  have hd2 : dist (e - δ • (u - e)) e = δ * ‖u - e‖ := by
    rw [dist_eq_norm]
    have hv : e - δ • (u - e) - e = -(δ • (u - e)) := by abel
    rw [hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδp]
  have hηne : ‖u - e‖ ≠ 0 := ne_of_gt hηp
  have hp1 : e + δ • (u - e) ∈ p := by
    refine hff.1 (hball ⟨?_, haff1⟩)
    rw [Metric.mem_ball, hd1, hδ]
    field_simp
    norm_num
  have hp2 : e - δ • (u - e) ∈ p := by
    refine hff.1 (hball ⟨?_, haff2⟩)
    rw [Metric.mem_ball, hd2, hδ]
    field_simp
    norm_num
  have hseg : e ∈ openSegment ℝ (e + δ • (u - e)) (e - δ • (u - e)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_sub ((1:ℝ)/2) e (δ • (u - e)), smul_sub δ u e, add_assoc]
    have hPQ : ((1:ℝ)/2) • (δ • u - δ • e)
        + (((1:ℝ)/2) • e - ((1:ℝ)/2) • (δ • u - δ • e)) = ((1:ℝ)/2) • e := by abel
    rw [hPQ, ← add_smul, add_halves, one_smul]
  have hseg' : e ∈ segment ℝ (e + δ • (u - e)) (e - δ • (u - e)) := by
    obtain ⟨a₁, a₂, h₁, h₂, h₃, h₄⟩ := hseg
    exact ⟨a₁, a₂, h₁.le, h₂.le, h₃, h₄⟩
  obtain ⟨mem, hcond⟩ := mem_extremePoints_iff_forall_segment.mp he
  rcases hcond (e + δ • (u - e)) hp1 (e - δ • (u - e)) hp2 hseg' with hcon | hcon
  · have hz0 : δ • (u - e) = δ • (0:V3) := by rw [add_eq_left.mp hcon, smul_zero]
    exact hη0 (smul_right_injective V3 (ne_of_gt hδp) hz0)
  · have h1 : e + δ • (u - e) = e := (sub_eq_iff_eq_add.mp hcon).symm
    have hz0 : δ • (u - e) = δ • (0:V3) := by
      have h2 : (e + δ • (u - e)) - e = (0:V3) := by rw [h1, sub_self]
      rw [add_sub_cancel_left] at h2
      rw [h2, smul_zero]
    exact hη0 (smul_right_injective V3 (ne_of_gt hδp) hz0)


/-- 射线-前沿引理（HOL `REDUCE_POINT_FACET_EXISTS` 的核心重建）：非零点的
过原点射线离开紧多面体的最后一点必落在某 facet 上。参数集合为闭集，上确界
可达；上确界点在 `p \ rint p` 中（全维数下 `rint = interior`），经
`RELATIVE_INTERIOR_OF_POLYHEDRON` 落入某 facet。 -/
private theorem exists_facet_ray_p7 {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) {y : V3} (hy : y ≠ 0) :
    ∃ f : Set V3, ∃ t : ℝ, 0 < t ∧ FacetOf_p7 f p ∧ t • y ∈ f := by
  classical
  have hpc : IsClosed p := POLYHEDRON_IMP_CLOSED hp
  have hyn : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  set S : Set ℝ := {t : ℝ | t • y ∈ p} with hS
  have hmemS : ∀ t : ℝ, t ∈ S ↔ t • y ∈ p := fun _ => Iff.rfl
  have h0S : (0 : ℝ) ∈ S := (hmemS 0).mpr (by simpa using interior_subset hz)
  -- 上有界：`p ⊆ ball 0 R`
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : V3)
  have hbdd : BddAbove S := by
    refine ⟨R / ‖y‖, fun t ht => ?_⟩
    have htn : ‖t • y‖ < R := by
      have h1 : dist (t • y) (0 : V3) < R := hR ((hmemS t).mp ht)
      rwa [dist_zero_right] at h1
    have h2 : t * ‖y‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs] at htn
      calc t * ‖y‖ ≤ |t| * ‖y‖ := mul_le_mul_of_nonneg_right (le_abs_self t) hyn.le
        _ ≤ R := by linarith
    exact (le_div_iff₀ hyn).mpr h2
  -- 含正参数（0 的内点球）
  obtain ⟨e, he, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hz
  have htpos : ∃ t ∈ S, 0 < t := by
    refine ⟨e / 2 / ‖y‖, ?_, by positivity⟩
    have hmem : (e / 2 / ‖y‖) • y ∈ Metric.ball (0 : V3) e := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < e / 2 / ‖y‖)]
      field_simp
      linarith
    exact (hmemS _).mpr (interior_subset (hsub hmem))
  have hne : S.Nonempty := ⟨0, h0S⟩
  -- 上确界可达（S 闭：闭集在连续映射下的原像）
  have hcS : IsClosed S := by
    rw [hS]
    exact hpc.preimage (continuous_id.smul continuous_const)
  have hsup : sSup S ∈ S := by
    have hinc : sSup S ∈ closure S := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hlt : sSup S - ε / 2 < sSup S := by linarith
      obtain ⟨t, ht, hgt⟩ : ∃ t ∈ S, sSup S - ε / 2 < t := by
        by_contra hcon
        push_neg at hcon
        exact absurd (csSup_le hne fun t ht => hcon t ht)
          (by intro hcon'; linarith)
      refine ⟨t, ht, ?_⟩
      have htt : t ≤ sSup S := le_csSup hbdd ht
      rw [Real.dist_eq, abs_of_nonneg (by linarith :
        (0:ℝ) ≤ sSup S - t)]
      linarith
    rw [hcS.closure_eq] at hinc
    exact hinc
  have ht0pos : 0 < sSup S := by
    obtain ⟨t, htS, ht0⟩ := htpos
    exact ht0.trans_le (le_csSup hbdd htS)
  have hw : sSup S • y ∈ p := (hmemS _).mp hsup
  -- 上确界点不在 interior（否则可沿射线延拓）
  have hwnint : sSup S • y ∉ interior p := by
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
    have hδ : 0 < ε / (2 * ‖y‖) := div_pos hε (mul_pos two_pos hyn)
    have hmem : sSup S • y + (ε / (2 * ‖y‖)) • y ∈ Metric.ball (sSup S • y) ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδ]
      have hpos : (0:ℝ) < ‖y‖ := hyn
      field_simp
      linarith
    have hS' : sSup S + ε / (2 * ‖y‖) ∈ S := by
      refine (hmemS _).mpr ?_
      have hv : (sSup S + ε / (2 * ‖y‖)) • y
          = sSup S • y + (ε / (2 * ‖y‖)) • y := add_smul _ _ _
      rw [hv]
      exact interior_subset (hball hmem)
    exact absurd (le_csSup hbdd hS') (by linarith)
  -- 全维数下 rint = interior
  have hwrint : sSup S • y ∉ intrinsicInterior ℝ p := fun h =>
    hwnint ((mem_rint_iff_interior_p7 hz).1 h)
  -- `RELATIVE_INTERIOR_OF_POLYHEDRON`：rint p = p \ ⋃₀ facets
  rw [RELATIVE_INTERIOR_OF_POLYHEDRON hp] at hwrint
  have hwu : sSup S • y ∈ ⋃₀ {f : Set V3 | FacetOf f p} := by
    by_contra hcon
    exact hwrint ((Set.mem_sdiff _).mpr ⟨hw, hcon⟩)
  obtain ⟨f, hf, hwf⟩ := Set.mem_sUnion.mp hwu
  exact ⟨f, sSup S, ht0pos, hf, hwf⟩

/-- `⋃{fchanged f | f facet_of p} ⊆ yfan`（HOL `FCHANGED_SUBSET_YFAN`
的诚实重建）：反设 `x = t•v1 ∈ affGe {0} {a,b}`（`{a,b}` 为边，即闭段
`[a,b]` 是真面），则 `v1` 与 `w := (1/s)•v1 ∈ [a,b]` 是过原点正倍数点，
`POLYHEDRON_COLLINEAR_FACES`（batch 4 语义，`f`、`[a,b]` 均真面）迫
`s = 1`，即 `v1 ∈ [a,b]`；内点分支 `FACE_OF_EQ` 导出 `f = [a,b]` 与
`affDim` 矛盾，端点分支与 `SEGMENT_FACE_OF` 的极点性 + 极点不在
facet 相对内部矛盾。零分支由 `0 ∈ rint f ∩ rint p` 排除。 -/
private theorem fchanged_subset_yfan_p7 {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    (⋃ f ∈ {f : Set V3 | FacetOf_p7 f p}, fchanged_p7 f) ⊆
      yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p) := by
  intro x hx
  obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨v1, t, hvx, hv1, ht⟩ := hxf
  have hfp : FacetOf f p := hf
  have h3p : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
  have h2f : affDim f = 2 := by rw [hfp.2.2, h3p]; norm_num
  have hfpp : f ≠ p := by
    intro h
    rw [h] at h2f
    omega
  have hv1f : v1 ∈ f := intrinsicInterior_subset hv1
  -- 反设 x ∈ xfan
  show x ∈ Set.univ \ xfan (0:V3) (Set.extremePoints ℝ p) (edges_p7 p)
  rw [Set.mem_sdiff]
  refine ⟨Set.mem_univ _, fun hcon => ?_⟩
  obtain ⟨e, heE, hex⟩ := hcon
  obtain ⟨a, b, rfl, hab, hsub, hconv, hchord⟩ := heE
  have hsegedge : edgeOf (segment ℝ a b) p :=
    ⟨⟨hsub, hconv, hchord⟩, (affDim_segment a b).mpr hab⟩
  obtain ⟨-, haext, hbext⟩ := SEGMENT_EDGE_OF hsegedge
  have hsegface : FaceOf (segment ℝ a b) p := ⟨hsub, hconv, hchord⟩
  have ha0 : a ≠ 0 := extremePoint_ne_zero_of_interior hz haext
  have hb0 : b ≠ 0 := extremePoint_ne_zero_of_interior hz hbext
  have hpp : polyhedron p := hp
  have hdisj : Disjoint ({(0:V3)} : Set V3) {a, b} := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [Set.mem_singleton_iff] at hz1
    rcases Set.mem_insert_iff.mp hz2 with h | h
    · exact ha0 (h.symm.trans hz1)
    · rw [Set.mem_singleton_iff] at h
      exact hb0 (h.symm.trans hz1)
  have hexp : x ∈ {y : V3 | ∃ t1 t2 t3 : ℝ, 0 ≤ t2 ∧ 0 ≤ t3 ∧ t1 + t2 + t3 = 1 ∧
      y = t1 • (0:V3) + t2 • a + t3 • b} := by
    rw [← aff_ge_1_2 hdisj]
    exact hex
  obtain ⟨t1, c1, c2, hc10, hc20, hsum1, hcxe⟩ := hexp
  have hxeq : x = c1 • a + c2 • b := by rw [hcxe]; simp
  by_cases hcc : c1 = 0 ∧ c2 = 0
  · -- x = 0 ⟹ v1 = 0 ∈ rint f ∩ rint p ⟹ 与 Disjoint 矛盾
    have hx0 : x = 0 := by simp [hxeq, hcc]
    have hv10 : v1 = 0 := by
      have hprod : t • v1 = 0 := by rw [← hx0, hvx]
      exact (smul_eq_zero.mp hprod).resolve_left ht.ne'
    have hv1f0 : (0:V3) ∈ f := by rw [← hv10]; exact hv1f
    exact Set.disjoint_left.mp (faceOf_disjoint_rinterior hfp.1 hfpp) hv1f0
      (interior_subset_intrinsicInterior hz)
  · -- 主情形
    have hcpos : 0 < c1 + c2 := by
      by_contra hcon
      push_neg at hcon
      have h1 : c1 ≤ 0 := le_trans (le_add_of_nonneg_right hc20) hcon
      have h2 : c2 ≤ 0 := le_trans (le_add_of_nonneg_left hc10) hcon
      exact hcc ⟨le_antisymm h1 hc10, le_antisymm h2 hc20⟩
    have hv1eq : v1 = (c1 / t) • a + (c2 / t) • b := by
      apply smul_right_injective V3 ht.ne'
      show t • v1 = t • ((c1 / t) • a + (c2 / t) • b)
      have hsum : t • v1 = t • ((c1 / t) • a + (c2 / t) • b) := by
        rw [smul_add, smul_smul, mul_div_cancel₀ _ ht.ne', smul_smul,
          mul_div_cancel₀ _ ht.ne', hvx.symm.trans hxeq]
      rw [hsum]
    have h1' : 0 ≤ c1 / t := div_nonneg hc10 ht.le
    have h2' : 0 ≤ c2 / t := div_nonneg hc20 ht.le
    have hs' : 0 < c1 / t + c2 / t := by
      by_contra hcon
      push_neg at hcon
      have hzz1 : c1 / t = 0 := by linarith
      have hzz2 : c2 / t = 0 := by linarith
      exact hcc ⟨(div_eq_zero_iff).mp hzz1 |>.resolve_right ht.ne',
        (div_eq_zero_iff).mp hzz2 |>.resolve_right ht.ne'⟩
    set s : ℝ := c1 / t + c2 / t with hsdef
    have hceq : ∀ (q : ℝ) (z : V3), (1 / s) • (q • z) = (q / s) • z := by
      intro q z
      rw [smul_smul]
      congr 1
      field_simp
    have hsmem : (1 / s) • v1 ∈ segment ℝ a b := by
      rw [hv1eq, smul_add, hceq (c1 / t) a, hceq (c2 / t) b]
      exact ⟨(c1 / t) / s, (c2 / t) / s,
        div_nonneg h1' hs'.le, div_nonneg h2' hs'.le, by rw [← add_div, hsdef,
        div_self hs'.ne'], rfl⟩
    -- POLYHEDRON_COLLINEAR_FACES：1•v1 = s•((1/s)•v1) ⟹ 1 = s ⟹ v1 ∈ [a,b]
    have hsgne : (segment ℝ a b : Set V3) ≠ p := by
      intro h
      have h3 : affDim (segment ℝ a b) = 1 := hsegedge.2
      rw [h] at h3
      omega
    have hsEq : (1:ℝ) = s :=
      POLYHEDRON_COLLINEAR_FACES hpp hz hfp.1 hfpp hsegface hsgne hv1f hsmem
        one_pos hs' (by rw [one_smul, smul_smul, div_eq_mul_inv, one_mul,
          mul_inv_cancel₀ hs'.ne', one_smul])
    have hv1seg : v1 ∈ segment ℝ a b := by
      rw [hsEq] at hsmem
      rw [div_self hs'.ne', one_smul] at hsmem
      exact hsmem
    obtain ⟨l, m, hl, hm, hlm, hv1eq2⟩ := hv1seg
    have hfne_sing : ∀ z : V3, f ≠ {z} := by
      intro z h
      rw [h, affDim_singleton] at h2f
      norm_num at h2f
    have hm1ub : m ≤ 1 := le_trans (le_add_of_nonneg_left hl) hlm.le
    rcases eq_or_lt_of_le hm with hm0 | hm0
    · have hv1a : v1 = a := by
        have hl1 : l = 1 := by linarith
        rw [hl1, one_smul, ← hm0, zero_smul, add_zero] at hv1eq2
        exact hv1eq2.symm
      have hv1a' : a ∈ intrinsicInterior ℝ f := by
        rw [← hv1a]
        exact hv1
      exact extreme_notMem_rint_p7 haext hv1a' hfp.1 (hfne_sing a)
    · rcases eq_or_lt_of_le hm1ub with hm1 | hm1lt
      · have hv1b : v1 = b := by
          have hl0 : l = 0 := by linarith
          rw [hl0, zero_smul, hm1, one_smul, zero_add] at hv1eq2
          exact hv1eq2.symm
        have hv1b' : b ∈ intrinsicInterior ℝ f := by
          rw [← hv1b]
          exact hv1
        exact extreme_notMem_rint_p7 hbext hv1b' hfp.1 (hfne_sing b)
      · have hlm2 : l = 1 - m := by linarith
        have hv1open : v1 ∈ openSegment ℝ a b := by
          rw [hlm2] at hv1eq2
          exact ⟨1 - m, m, by linarith, hm0, by linarith, hv1eq2⟩
        have hv1rint : v1 ∈ intrinsicInterior ℝ (segment ℝ a b) :=
          openSegment_mem_rint_segment hab hv1open
        have hfeq : f = segment ℝ a b :=
          faceOf_eq hfp.1 hsegface
            (Set.not_disjoint_iff_nonempty_inter.mpr ⟨v1, hv1, hv1rint⟩)
        rw [hfeq] at h2f
        exact absurd h2f (by rw [hsegedge.2]; norm_num)

/-- `yfan ⊆ ⋃{fchanged f | f facet_of p}`（HOL `YFAN_SUBSET_UNIONS_FCHANGED`
的诚实重建）：`REDUCE_POINT_FACET` 路线——射线-前沿引理取 facet `f` 与
`t•y ∈ f`；`t•y ∈ rint f` 时直接落入并集；否则 `t•y ∈ f \ rint f`，经
`RELATIVE_INTERIOR_OF_POLYHEDRON` 下潜到 `f` 的 facet `g ∋ t•y`（维数
1），按 `EXISTS_EDGE_AT_VERTICES` 的 Krein–Milman 先例 +
`EXPAND_EDGE_POLYTOPE`（本文件冻结语句，作黑箱）写成 `segment[a,b]`，
于是 `y ∈ affGe {0}{a,b} ⊆ xfan`，与 `y ∈ yfan` 矛盾。0 ∉ yfan 由
`EXISTS_EDGE_POLYTOPE`（边存在 ⟹ 0 ∈ xfan）排除。 -/
private theorem yfan_subset_unions_fchanged_p7 {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    {y : V3} (hy : y ∈ yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p)) :
    y ∈ ⋃ f ∈ {f : Set V3 | FacetOf_p7 f p}, fchanged_p7 f := by
  have hpp : polyhedron p := hp
  -- 0 ∉ yfan：边存在 ⟹ 0 ∈ xfan
  have hy0 : y ≠ 0 := by
    rintro rfl
    obtain ⟨e0, he0⟩ := EXISTS_EDGE_POLYTOPE p hb hpp hz
    obtain ⟨v, w, rfl, hedge⟩ := he0
    obtain ⟨⟨hsub, hconv, hchord⟩, hdim⟩ := hedge
    have hvw : v ≠ w := (affDim_segment v w).mp hdim
    have hsegface : FaceOf (segment ℝ v w) p := ⟨hsub, hconv, hchord⟩
    have hznot0 : ∀ z ∈ segment ℝ v w, z ≠ 0 := by
      intro z hzm hz0
      have h2 : (segment ℝ v w : Set V3) ≠ p := by
        intro hcon
        have h3 : affDim (segment ℝ v w) = 1 := (affDim_segment v w).mpr hvw
        rw [hcon] at h3
        have h4 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
        omega
      have h0seg : (0:V3) ∈ segment ℝ v w := by
        rw [← hz0]
        exact hzm
      exact Set.disjoint_left.mp (faceOf_disjoint_rinterior hsegface h2) h0seg
        (interior_subset_intrinsicInterior hz)
    have hdisj : Disjoint ({(0:V3)} : Set V3) {v, w} := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      rw [Set.mem_singleton_iff] at hz1
      rcases Set.mem_insert_iff.mp hz2 with h | h
      · exact hznot0 v (left_mem_segment (𝕜 := ℝ) v w) (h.symm.trans hz1)
      · rw [Set.mem_singleton_iff] at h
        exact hznot0 w (right_mem_segment _ _ _) (h.symm.trans hz1)
    have h0cone : (0:V3) ∈ affGe {(0:V3)} {v, w} := by
      rw [aff_ge_1_2 hdisj]
      exact ⟨1, 0, 0, le_refl 0, le_refl 0, by norm_num, by simp⟩
    have hxfan : (0:V3) ∈ xfan (0:V3) (Set.extremePoints ℝ p) (edges_p7 p) :=
      ⟨{v, w}, ⟨v, w, rfl, hvw, hsub, hconv, hchord⟩, h0cone⟩
    obtain ⟨-, hnot⟩ := (Set.mem_sdiff _).mp hy
    exact hnot hxfan
  -- 主线：射线-前沿引理
  obtain ⟨f, t0, ht00, hf, hwy⟩ := exists_facet_ray_p7 hb hp hz hy0
  have hfp : FacetOf f p := hf
  by_cases hwrint : t0 • y ∈ intrinsicInterior ℝ f
  · exact Set.mem_iUnion₂.mpr ⟨f, hf, t0 • y, 1 / t0,
      by rw [smul_smul, show (1:ℝ) / t0 * t0 = 1 by
        field_simp, one_smul], hwrint,
      div_pos zero_lt_one ht00⟩
  · -- 下降分支：t0•y 落在 f 的某 facet g（维数 1）
    have hwf : t0 • y ∈ f := hwy
    have hfpoly : polyhedron f := by
      obtain ⟨a₁, b₁, ha₁, -, hfeq⟩ := FACET_OF_POLYHEDRON hpp hfp
      rw [hfeq]
      exact POLYHEDRON_INTER hpp (POLYHEDRON_HYPERPLANE ha₁ b₁)
    have hw' : t0 • y ∉ intrinsicInterior ℝ f := hwrint
    rw [RELATIVE_INTERIOR_OF_POLYHEDRON hfpoly] at hw'
    have hwu : t0 • y ∈ ⋃₀ {g : Set V3 | FacetOf g f} := by
      by_contra hcon
      exact hw' ((Set.mem_sdiff _).mpr ⟨hwf, hcon⟩)
    obtain ⟨g, hg, hwg⟩ := Set.mem_sUnion.mp hwu
    have h2f : affDim f = 2 := by rw [hfp.2.2, AFF_DIM_INTERIOR_EQ_3 0 p hz]; norm_num
    have h1g : affDim g = 1 := by rw [hg.2.2, h2f]; norm_num
    have hgp : FaceOf g p := FaceOf.trans hg.1 hfp.1
    have hgne : g ≠ ∅ := hg.2.1
    have hgne2 : g ≠ p := by
      intro h
      rw [h] at h1g
      have h3 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
      omega
    have hgpp : polyhedron g := by
      rw [FACE_OF_POLYHEDRON hpp hgp hgne hgne2]
      refine POLYHEDRON_INTERS ?_ ?_
      · exact Set.Finite.subset (FINITE_POLYHEDRON_FACETS hpp) fun _ hx => hx.1
      · intro h' hh'
        obtain ⟨a', b', ha0', -, hhe⟩ := FACET_OF_POLYHEDRON hpp hh'.1
        rw [hhe]
        exact POLYHEDRON_INTER hpp (POLYHEDRON_HYPERPLANE ha0' b')
    have hgpconv : Convex ℝ g := hgp.2.1
    have hgb : Bornology.IsBounded g := hb.subset hgp.1
    have hgcl : IsClosed g := POLYHEDRON_IMP_CLOSED hgpp
    have hgcomp : IsCompact g := Metric.isCompact_of_isClosed_isBounded hgcl hgb
    have hext : (Set.extremePoints ℝ g).Finite := FINITE_POLYHEDRON_EXTREME_POINTS hgpp
    have hcch : IsClosed (convexHull ℝ (Set.extremePoints ℝ g)) :=
      (hext.isCompact_convexHull ℝ).isClosed
    have hgkm : g = convexHull ℝ (Set.extremePoints ℝ g) := by
      have h1 := closure_convexHull_extremePoints hgcomp hgpconv
      rw [hcch.closure_eq] at h1
      exact h1.symm
    obtain ⟨a, b, hgseg⟩ :=
      EXPAND_EDGE_POLYTOPE (f := g) (p := g) ⟨Set.extremePoints ℝ g, hext, hgkm⟩
        (FaceOf.refl (s := g) hgpconv) h1g
    have hab : a ≠ b := by
      rintro rfl
      rw [hgseg, segment_same, affDim_singleton] at h1g
      norm_num at h1g
    have heE : {a, b} ∈ edges_p7 p := by
      refine ⟨a, b, rfl, hab, ?_, ?_, ?_⟩
      · rw [← hgseg]; exact hgp.1
      · rw [← hgseg]; exact hgp.2.1
      · rw [← hgseg]; exact hgp.2.2
    have hsf : FaceOf (segment ℝ a b) p := by rw [← hgseg]; exact hgp
    obtain ⟨haext, hbext⟩ := SEGMENT_FACE_OF hsf
    have ha0 : a ≠ 0 := extremePoint_ne_zero_of_interior hz haext
    have hb0 : b ≠ 0 := extremePoint_ne_zero_of_interior hz hbext
    have hdisj2 : Disjoint ({(0:V3)} : Set V3) {a, b} := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      rw [Set.mem_singleton_iff] at hz1
      rcases Set.mem_insert_iff.mp hz2 with h | h
      · exact ha0 (h.symm.trans hz1)
      · rw [Set.mem_singleton_iff] at h
        exact hb0 (h.symm.trans hz1)
    have hwseg : t0 • y ∈ segment ℝ a b := by rw [← hgseg]; exact hwg
    obtain ⟨l, m, hl, hm, hlm, heq⟩ := hwseg
    have ht00ne : t0 ≠ 0 := ht00.ne'
    have hyc : y ∈ affGe {(0:V3)} {a, b} := by
      rw [aff_ge_1_2 hdisj2]
      refine ⟨1 - 1 / t0, l / t0, m / t0, div_nonneg hl ht00.le,
        div_nonneg hm ht00.le, ?_, ?_⟩
      · field_simp
        linarith
      · have hysc : y = (1 / t0) • (t0 • y) := by
          rw [smul_smul, show (1:ℝ) / t0 * t0 = 1 from by field_simp, one_smul]
        rw [hysc, ← heq, smul_add, smul_smul, smul_smul, smul_zero, zero_add]
        congr 1
        · field_simp
        · field_simp
    have hxfan : y ∈ xfan (0:V3) (Set.extremePoints ℝ p) (edges_p7 p) :=
      ⟨{a, b}, heE, hyc⟩
    exact absurd hxfan ((Set.mem_sdiff _).mp hy).2

/-- `FCHANGED_EQ_YFAN` 的 `_p7` 诚实重建（两包含拼装；HOL
polyhedron.hl :1685-:1695）。 -/
private theorem fchanged_eq_yfan_p7 {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    (⋃ f ∈ {f : Set V3 | FacetOf_p7 f p}, fchanged_p7 f)
      = yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p) := by
  refine Set.eq_of_subset_of_subset (fchanged_subset_yfan_p7 hb hp hz) ?_
  intro y hy
  exact yfan_subset_unions_fchanged_p7 hb hp hz hy


/-- `FCHANGED_IN_COMPONENT` 的 `_p7` 诚实重建（HOL polyhedron.hl
:1715-:1821）：`fchanged f` 连通且含于 `yfan`，在 `yfan` 中开
（`FCHANGED_OPEN`），其余 facet 的 `fchanged` 之并（`FCHANGED_EQ_YFAN`
覆盖 yfan 的其余部分）亦开且与之不交（`FCHANGED_ONE_TO_ONE` 逆否），
故 `fchanged f` 恰为含其任一点的 yfan-连通分量（开二分 + 连通性）。 -/
private theorem fchanged_in_component_p7 {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    {f : Set V3} (hf : FacetOf_p7 f p) :
    fchanged_p7 f ∈ topologicalComponentYfan (0 : V3) (Set.extremePoints ℝ p)
      (edges_p7 p) := by
  have hfp : FacetOf f p := hf
  have hpp : polyhedron p := hp
  have hfne : f.Nonempty := Set.nonempty_iff_ne_empty.mpr hfp.2.1
  obtain ⟨v0, hv0⟩ := Set.Nonempty.intrinsicInterior hfp.1.2.1 hfne
  have hb0 : v0 ∈ fchanged_p7 f := ⟨v0, 1, by rw [one_smul], hv0, zero_lt_one⟩
  have hfsub : fchanged_p7 f ⊆ yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p) :=
    fun w hw => fchanged_subset_yfan_p7 hb hp hz
      (Set.mem_iUnion₂.mpr ⟨f, hf, hw⟩)
  have hyfan0 : v0 ∈ yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p) := hfsub hb0
  have hconn : IsConnected (fchanged_p7 f) := isConnected_fchanged_p7 hf
  have hbig : fchanged_p7 f ⊆
      connectedComponentIn (yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p)) v0 :=
    hconn.2.subset_connectedComponentIn hb0 hfsub
  have hUopen : IsOpen (fchanged_p7 f) := FCHANGED_OPEN p f hb hpp hz hfp
  have hVopen : IsOpen
      (⋃₀ {T : Set V3 | ∃ g : Set V3, FacetOf_p7 g p ∧ g ≠ f ∧ T = fchanged_p7 g}) :=
    by
      refine isOpen_sUnion ?_
      rintro T ⟨g, hg, hne2, rfl⟩
      exact FCHANGED_OPEN p g hb hpp hz hg
  have hsplit : ∀ z ∈ yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p),
      z ∈ fchanged_p7 f ∪
        ⋃₀ {T : Set V3 | ∃ g : Set V3, FacetOf_p7 g p ∧ g ≠ f ∧ T = fchanged_p7 g} := by
    intro z hzy
    have hzu : z ∈ ⋃ g ∈ {g : Set V3 | FacetOf_p7 g p}, fchanged_p7 g :=
      (Eq.subset (fchanged_eq_yfan_p7 hb hp hz).symm) hzy
    obtain ⟨g, hg, hzg⟩ := Set.mem_iUnion₂.mp hzu
    rcases eq_or_ne g f with hgf | hne
    · rw [hgf] at hzg
      exact Or.inl hzg
    · exact Or.inr (Set.mem_sUnion.mpr
        ⟨fchanged_p7 g, ⟨g, hg, hne, rfl⟩, hzg⟩)
  have hDU : Disjoint (fchanged_p7 f)
      (⋃₀ {T : Set V3 | ∃ g : Set V3, FacetOf_p7 g p ∧ g ≠ f ∧ T = fchanged_p7 g}) := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨T, ⟨g, hg, hne, rfl⟩, hzg⟩ := Set.mem_sUnion.mp hzV
    refine absurd (FCHANGED_ONE_TO_ONE p f g hb hpp hz hfp hg ?_).symm hne
    refine Set.nonempty_iff_ne_empty.mpr ⟨z, hzU, hzg⟩
  have hcompU : connectedComponentIn
      (yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p)) v0 ⊆ fchanged_p7 f := by
    by_contra hcon
    rw [Set.not_subset] at hcon
    obtain ⟨z, hzc, hzU⟩ := hcon
    have hzy : z ∈ yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p) :=
      connectedComponentIn_subset _ _ hzc
    have hzV : z ∈ ⋃₀ {T : Set V3 | ∃ g : Set V3, FacetOf_p7 g p ∧ g ≠ f ∧
        T = fchanged_p7 g} := (hsplit z hzy).resolve_left hzU
    have hpre : IsPreconnected (connectedComponentIn
      (yfan (0 : V3) (Set.extremePoints ℝ p) (edges_p7 p)) v0) :=
      (isConnected_connectedComponentIn_iff.mpr hyfan0).2
    obtain ⟨w, hw1, hw2⟩ := hpre (fchanged_p7 f)
      (⋃₀ {T : Set V3 | ∃ g : Set V3, FacetOf_p7 g p ∧ g ≠ f ∧
        T = fchanged_p7 g}) hUopen hVopen
      (fun x hx => hsplit x (connectedComponentIn_subset _ _ hx))
      ⟨v0, mem_connectedComponentIn hyfan0, hb0⟩ ⟨z, hzc, hzV⟩
    exact hDU ⟨w, hw1, hw2⟩
  refine ⟨v0, hyfan0, ?_⟩
  exact subset_antisymm hcompU hbig

/-! ## polyhedron.hl :1823-:2004（面的 fchanged-参数化） -/

/-- HOL polyhedron.hl :1823-:1839 `SUR_FCHANGED`

HOL 原文：
```
!s p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p /\
 s IN topological_component_yfan(vec 0:real^3,vertices (p:real^3->bool),edges (p:real^3->bool))
==> ?f. f facet_of p /\ s= fchanged f
```

编码说明：`topological_component_yfan` ↦ `topologicalComponentYfan`
（Kepler/Text/Fan.lean:199）；`vertices`/`edges` 见 `edges_p7` 与批头
（`Set.extremePoints ℝ p`）；`facet_of`/`fchanged` ↦ 本文件私有副本。

证明思路（HOL，诚实执行）：`FCHANGED_EQ_YFAN`（上文 `fchanged_eq_yfan_p7`
两包含）把 `fchanged` 侧化入 yfan-语言；`topological_component_subset_yfan`
（PlanarityConnect.lean:189）与 `connectedComponentIn_nonempty_iff` 取
`z ∈ s ⊆ yfan`；`yfan_subset_unions_fchanged_p7` 给 facet `f` 与
`z ∈ fchanged f`；`fchanged_in_component_p7`（上文：facet 的 fchanged 是
yfan-连通分量）与共享点 `z` 的分量唯一性
（`connectedComponentIn_eq`，HOL `CONNECTED_COMPONENT_OVERLAP`）迫使
`s = fchanged f`。原冻结桥（批 6 闭段编码爆炸）已随批 6 模块废弃，
本证明为 PolyAuto6.lean 中心链的就地诚实重建（见批 6 诚实核心节头）。 -/
theorem SUR_FCHANGED {s p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    (hs : s ∈ topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) :
    ∃ f : Set V3, FacetOf_p7 f p ∧ s = fchanged_p7 f := by
  rcases hs with ⟨b, hby, rfl⟩
  have hsub : connectedComponentIn (yfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) b ⊆
      yfan 0 (Set.extremePoints ℝ p) (edges_p7 p) :=
    topological_component_subset_yfan ⟨b, hby, rfl⟩
  obtain ⟨z, hzs⟩ := connectedComponentIn_nonempty_iff.mpr hby
  obtain ⟨f, hf, hzfc⟩ :=
    Set.mem_iUnion₂.mp (yfan_subset_unions_fchanged_p7 hb hp hz (hsub hzs))
  obtain ⟨z', hz'y, hzeq⟩ := fchanged_in_component_p7 hb hp hz hf
  have e1 : connectedComponentIn (yfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) b
      = connectedComponentIn (yfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) z :=
    connectedComponentIn_eq hzs
  have hzz' : z ∈ connectedComponentIn (yfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) z' := by
    rw [hzeq]
    exact hzfc
  have e2 : connectedComponentIn (yfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) z'
      = connectedComponentIn (yfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) z :=
    connectedComponentIn_eq hzz'
  exact ⟨f, hf, e1.trans (e2.symm.trans hzeq.symm)⟩

/-- HOL polyhedron.hl :1855-:1873 `AMHFNXP`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>
(!s. s IN topological_component_yfan (vec 0,vertices (p:real^3->bool),edges (p:real^3->bool)) ==> (?!f. f facet_of p /\
							 s = fchanged f))
```

编码说明：`?!f. P f` ↦ `∃! f, P f`（ConformingDefs.lean 先例）。

证明思路（HOL，诚实执行）：存在性即 `SUR_FCHANGED`；唯一性：设
`s = fchanged f = fchanged y`，`FCHANGED_ONE_TO_ONE`（PolyAuto5，诚实版）
化归为 `fchanged f ∩ fchanged y ≠ ∅`；交点由 `f` 的非空凸性给相对内部
非空（Mathlib `Set.Nonempty.intrinsicInterior`，即 HOL
`EXISTS_POINT_IN_FCHANGED` 的就地重建，`t = 1` 见证）。 -/
theorem AMHFNXP {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    ∀ s ∈ topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p),
      ∃! f : Set V3, FacetOf_p7 f p ∧ s = fchanged_p7 f := by
  intro s hs
  obtain ⟨f, hf, hseq⟩ := SUR_FCHANGED hb hp hz hs
  refine ⟨f, ⟨hf, hseq⟩, ?_⟩
  rintro y ⟨hfy, hseqy⟩
  have hpp : polyhedron p := hp
  have hfne : f.Nonempty := Set.nonempty_iff_ne_empty.mpr hf.2.1
  obtain ⟨v0, hv0⟩ := Set.Nonempty.intrinsicInterior hf.1.2.1 hfne
  have hv0f : v0 ∈ fchanged_p7 f := ⟨v0, 1, by rw [one_smul], hv0, zero_lt_one⟩
  have hint : fchanged_p7 f ∩ fchanged_p7 y ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mpr ⟨v0, hv0f, hv0y⟩
  have hv0y : v0 ∈ fchanged_p7 y := by
    rw [← hseqy, hseq]
    exact hv0f
  exact FCHANGED_ONE_TO_ONE p f y hb hpp hz hf hfy hint

/-- HOL polyhedron.hl :1875-:1891 `AMHFNXP_BIJ`

HOL 原文：
```
!p:real^3->bool. bounded p /\ polyhedron p /\ vec 0 IN interior p ==>
  (BIJ fchanged (\f. f facet_of p) (topological_component_yfan (vec 0,vertices p,edges p)))
```

编码说明：HOL `BIJ f s t`（INJ + SURJ）↦ `Set.BijOn f s t`；像函数
`\f. f facet_of p` 编码为集合 `{f : Set V3 | FacetOf_p7 f p}`。

证明思路（HOL，prove_by_refinement 原文仅 7 步；诚实执行）：三分量——
MapsTo 即诚实版 `FCHANGED_IN_COMPONENT`（上文 `fchanged_in_component_p7`，
PolyAuto6.lean 废弃后的就地重建）；InjOn 由 PolyAuto5 诚实版
`FCHANGED_ONE_TO_ONE` + facet 非空凸性给 `fchanged` 非空
（`t = 1` 见证）；SurjOn 即 `SUR_FCHANGED`。 -/
theorem AMHFNXP_BIJ {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    Set.BijOn (fun f : Set V3 => fchanged_p7 f) {f : Set V3 | FacetOf_p7 f p}
      (topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) := by
  have hpp : polyhedron p := hp
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact fchanged_in_component_p7 hb hp hz hf
  · intro f hf y hfy heq
    have hfne : f.Nonempty := Set.nonempty_iff_ne_empty.mpr hf.2.1
    obtain ⟨v0, hv0⟩ := Set.Nonempty.intrinsicInterior hf.1.2.1 hfne
    have hv0f : v0 ∈ fchanged_p7 f := ⟨v0, 1, by rw [one_smul], hv0, zero_lt_one⟩
    have hint : fchanged_p7 f ∩ fchanged_p7 y ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mpr ⟨v0, hv0f, hv0y⟩
    have hv0y : v0 ∈ fchanged_p7 y := by
      rw [show fchanged_p7 y = fchanged_p7 f from Eq.symm heq]
      exact hv0f
    exact FCHANGED_ONE_TO_ONE p f y hb hpp hz hf hfy hint
  · intro s hs
    obtain ⟨f, hf, hseq⟩ := SUR_FCHANGED hb hp hz hs
    refine ⟨f, hf, ?_⟩
    exact hseq.symm

/-! ## polyhedron.hl :1893-:2004（边上的顶点） -/

/-- HOL polyhedron.hl :1932-:2003 `EXISTS_EDGE_AT_VERTICES`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>  (!v. v IN vertices p ==> ~(set_of_edge v (vertices p) (edges p) ={}) )
```

编码说明：`vertices p` ↦ `Set.extremePoints ℝ p`；
`~(s = {})` ↦ `s ≠ ∅`；`set_of_edge` ↦ `setOfEdge`
（Kepler/Text/Fan.lean:62）；`edges p` ↦ `edges_p7`（本文件）。

证明思路（HOL）：`vertices` 展开 + `GSYM FACE_OF_SING` 把 `v ∈ vertices p`
写成 `{v} face_of p`；`AFF_DIM_SING` + `AFF_DIM_INTERIOR_EQ_3`（含内点的
有界多面体维数 3，未移植）排除 `p = {v}`；`FACE_OF_POLYHEDRON_SUBSET_FACET`
（未移植）把 `{v}` 嵌入 facet `f`；`EXTREME_POINT_OF_FACE` 传递极点性，
`FACE_OF_POLYHEDRON_POLYHEDRON` 保持多面体性；再降一维取 `f` 的过 `v`
facet `f'`（`AFF_DIM f = 2`），`EXPAND_EDGE_POLYTOPE` 给
`f' = segment[a,b]`，`EXTREME_POINT_OF_SEGMENT` 得 `v ∈ {a,b}`；
`SEGMENT_EDGE_OF`（segment[a,b] edge_of p）把 `{a,b}` 送入 `edges p`，
取异于 `v` 的端点为 `w`，`setOfEdge` 展开收口。

候选已有引理：
- `Set.extremePoints`、`mem_extremePoints`（Mathlib Analysis/Convex/Extreme.lean:68,133）
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `EXPAND_EDGE_POLYTOPE`（本文件上文）
- 缺口：`AFF_DIM_INTERIOR_EQ_3`、`FACE_OF_POLYHEDRON_SUBSET_FACET`、
  `EXTREME_POINT_OF_FACE`、`EXTREME_POINT_OF_SEGMENT`、`SEGMENT_EDGE_OF`
  等上游面论引理 repo 未移植（Mathlib 有 `Set.extremePoints` 的段刻画
  与 `IsExtremePoint` 传递性可部分重建） -/
theorem EXISTS_EDGE_AT_VERTICES {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    ∀ v ∈ Set.extremePoints ℝ p,
      setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p) ≠ ∅ := by
  intro v hv
  -- `{v} face_of p`（`FACE_OF_SING` 展开，`faceOf_sing`）
  have hvsing : FaceOf_p7 {v} p := (faceOf_sing (x := v) (s := p)).mpr hv
  have h3p : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
  -- 排除 `p = {v}`（否则维数 0 ≠ 3）
  have hpvne : p ≠ {v} := by
    intro h
    have hz' : (0:V3) ∈ interior {v} := by rw [← h]; exact hz
    have h3 := AFF_DIM_INTERIOR_EQ_3 0 {v} hz'
    rw [affDim_singleton] at h3
    omega
  -- 顶点嵌入某个 facet `f`（维数 2），`f` 显式化为超平面切片故为多面体
  obtain ⟨f, hf, hvf⟩ :=
    FACE_OF_POLYHEDRON_SUBSET_FACET (s := p) hp hvsing (Set.singleton_ne_empty v) (Ne.symm hpvne)
  obtain ⟨a1, b1, ha1, -, hfeq⟩ := FACET_OF_POLYHEDRON hp hf
  have hfp : polyhedron f := by
    rw [hfeq]
    exact POLYHEDRON_INTER hp (POLYHEDRON_HYPERPLANE ha1 b1)
  have hfvf : FaceOf_p7 {v} f := faceOf_subset hvsing hvf hf.1.1
  have h2f : affDim f = 2 := by rw [hf.2.2, h3p]; norm_num
  have hvne : {v} ≠ f := by
    intro h
    rw [← h, affDim_singleton] at h2f
    omega
  -- 降一维：过 `v` 的 facet `g`（维数 1），`g face_of p`
  obtain ⟨g, hg, hvg⟩ := FACE_OF_POLYHEDRON_SUBSET_FACET hfp hfvf (Set.singleton_ne_empty v) hvne
  have hgne : g ≠ ∅ := hg.2.1
  have hgaff : affDim g = 1 := by rw [hg.2.2, h2f]; norm_num
  have hgp : FaceOf_p7 g p := FaceOf.trans hg.1 hf.1
  have hgne2 : g ≠ p := by
    intro h
    rw [h] at hgaff
    omega
  -- `g` 为多面体（面 = 含它的 facets 之交）
  have hgpp : polyhedron g := by
    rw [FACE_OF_POLYHEDRON hp hgp hgne hgne2]
    refine POLYHEDRON_INTERS ?_ ?_
    · exact Set.Finite.subset (FINITE_POLYHEDRON_FACETS hp) fun _ hx => hx.1
    · intro h' hh'
      obtain ⟨a', b', ha0', -, hhe⟩ := FACET_OF_POLYHEDRON hp hh'.1
      rw [hhe]
      exact POLYHEDRON_INTER hp (POLYHEDRON_HYPERPLANE ha0' b')
  -- `g` 是多胞形（Krein–Milman + 极点有限）
  have hgpconv : Convex ℝ g := hgp.2.1
  have hgb : Bornology.IsBounded g := hb.subset hgp.1
  have hgcl : IsClosed g := POLYHEDRON_IMP_CLOSED hgpp
  have hgcomp : IsCompact g := Metric.isCompact_of_isClosed_isBounded hgcl hgb
  have hext : (Set.extremePoints ℝ g).Finite := FINITE_POLYHEDRON_EXTREME_POINTS hgpp
  have hcch : IsClosed (convexHull ℝ (Set.extremePoints ℝ g)) :=
    (hext.isCompact_convexHull ℝ).isClosed
  have hgkm : g = convexHull ℝ (Set.extremePoints ℝ g) := by
    have h1 := closure_convexHull_extremePoints hgcomp hgpconv
    rw [hcch.closure_eq] at h1
    exact h1.symm
  -- 退化边：`g = segment[a,b]`（EXPAND_EDGE_POLYTOPE，冻结语句）
  obtain ⟨a, b, hgseg⟩ :=
    EXPAND_EDGE_POLYTOPE (f := g) (p := g) ⟨Set.extremePoints ℝ g, hext, hgkm⟩
      (FaceOf.refl (s := g) hgpconv) hgaff
  have hsegedge : edgeOf (segment ℝ a b) p :=
    ⟨by rw [← hgseg]; exact hgp, by rw [← hgseg]; exact hgaff⟩
  obtain ⟨hab, haV, hbV⟩ := SEGMENT_EDGE_OF hsegedge
  have hvseg : v ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    have hvsegr : v ∈ segment ℝ a b := by rw [← hgseg]; exact hvg (by simp)
    have hsubp : segment ℝ a b ⊆ p := by rw [← hgseg]; exact hgp.1
    refine mem_extremePoints.mpr ⟨hvsegr, ?_⟩
    intro x₁ hx₁ x₂ hx₂ hx
    have e1 := hv.2 (hsubp hx₁) (hsubp hx₂) hx
    have e2 := hv.2 (hsubp hx₂) (hsubp hx₁) (by rw [openSegment_symm]; exact hx)
    exact ⟨e1, e2⟩
  have heE1 : {a, b} ∈ edges_p7 p :=
    ⟨a, b, rfl, hab, hsegedge.1.1, hsegedge.1.2.1, hsegedge.1.2.2⟩
  have heE2 : {b, a} ∈ edges_p7 p := by
    refine ⟨b, a, rfl, hab.symm, ?_, ?_, ?_⟩
    · intro z hz
      rw [segment_symm] at hz
      exact hsegedge.1.1 hz
    · rw [segment_symm]
      exact hsegedge.1.2.1
    · intro c d y hc hd hy hopen
      rw [segment_symm] at hy ⊢
      exact hsegedge.1.2.2 c d y hc hd hy hopen
  rcases (EXTREME_POINT_OF_SEGMENT a b v).mp hvseg with heq | heq
  · rw [heq]
    refine Set.nonempty_iff_ne_empty.mp ⟨b, ?_, hbV⟩
    exact heE1
  · rw [heq]
    refine Set.nonempty_iff_ne_empty.mp ⟨a, ?_, haV⟩
    exact heE2

/-! ## 填充辅助（session 1）：FLVNSME 阶段 0-3 的通用事实 -/

/-- V3 点积第二变元的加法性（Polytope.lean 私有 `dot_add` 的就地重述）。 -/
private theorem p7_dot_add (a x y : V3) : a ⬝ᵥ (x + y) = a ⬝ᵥ x + a ⬝ᵥ y := by
  show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
  rw [dotProduct_add]

/-- V3 点积第二变元的齐次性（Polytope.lean 私有 `dot_smul` 的就地重述）。 -/
private theorem p7_dot_smul (a : V3) (r : ℝ) (x : V3) : a ⬝ᵥ (r • x) = r * (a ⬝ᵥ x) := by
  show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
  rw [dotProduct_smul, RingHom.id_apply, smul_eq_mul]

/-- 支撑超平面切片是面（HOL `FACE_OF_INTER_SUPPORTING_HYPERPLANE`；Polytope.lean
私有 `faceOf_hyperplane_slice` 的显式参数重述，供 P4-P6 下潜用）。 -/
private theorem faceOf_hyperplane_slice {s : Set V3} (hconv : Convex ℝ s) (a : V3) (c : ℝ)
    (hsub : s ⊆ {x : V3 | a ⬝ᵥ x ≤ c}) : FaceOf (s ∩ {x : V3 | a ⬝ᵥ x = c}) s := by
  have hcvxH : Convex ℝ {x : V3 | a ⬝ᵥ x = c} := by
    intro x hx y hy u v hu hv hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have h : a ⬝ᵥ (u • x + v • y) = u * (a ⬝ᵥ x) + v * (a ⬝ᵥ y) := by
      rw [p7_dot_add, p7_dot_smul, p7_dot_smul]
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, h, hx, hy]
    have h3 : u * c + v * c = c := by
      have h4 : (u + v) * c = c := by rw [hab, one_mul]
      rwa [add_mul] at h4
    exact h3
  refine ⟨Set.inter_subset_left, hconv.inter hcvxH, ?_⟩
  intro u v x hu hv hx hseg
  obtain ⟨l, m, hl, hm, hlm, hxe⟩ := hseg
  have hxe' : l • u.ofLp + m • v.ofLp = x.ofLp :=
    congrArg (fun z : V3 => z.ofLp) hxe
  have hu0 : a ⬝ᵥ u ≤ c := hsub hu
  have hv0 : a ⬝ᵥ v ≤ c := hsub hv
  have hkey : a ⬝ᵥ (l • u + m • v) = l * (a ⬝ᵥ u) + m * (a ⬝ᵥ v) := by
    rw [p7_dot_add, p7_dot_smul, p7_dot_smul]
  have hx0 : a.ofLp ⬝ᵥ (l • u.ofLp + m • v.ofLp) = c := by
    rw [hxe']
    exact hx.2
  rw [hkey] at hx0
  have hcom : l * (a ⬝ᵥ u) + m * (a ⬝ᵥ v) = l * c + m * c := by
    rw [← add_mul, hlm, one_mul]
    exact hx0
  have h1 : l * (a ⬝ᵥ u) ≤ l * c := mul_le_mul_of_nonneg_left hu0 hl.le
  have h2 : m * (a ⬝ᵥ v) ≤ m * c := mul_le_mul_of_nonneg_left hv0 hm.le
  have hu' : a ⬝ᵥ u = c := mul_left_cancel₀ hl.ne' (by linarith)
  have hv' : a ⬝ᵥ v = c := mul_left_cancel₀ hm.ne' (by linarith)
  exact ⟨⟨hu, hu'⟩, ⟨hv, hv'⟩⟩

/-- 极点不在拓扩内部（HOL `EXTREME_POINT_NOT_IN_INTERIOR`）。 -/
private theorem extremePoint_not_mem_interior {s : Set V3} {x : V3}
    (hx : x ∈ Set.extremePoints ℝ s) : x ∉ interior s := by
  intro hint
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hint
  set u : V3 := EuclideanSpace.single (0 : Fin 3) (1:ℝ) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu]
    simp [PiLp.norm_single]
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu1
    norm_num at hu1
  set δ := ε / 2 with hδdef
  have hδ0 : 0 < δ := by linarith
  have hyb : x + δ • u ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hδ0, hδdef, hu1, mul_one]
    linarith
  have hy : x + δ • u ∈ s := interior_subset (hball hyb)
  have hzb : x - δ • u ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, show x - δ • u - x = -(δ • u) from by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ0, hδdef, hu1, mul_one]
    linarith
  have hz : x - δ • u ∈ s := interior_subset (hball hzb)
  have hxm : x ∈ segment ℝ (x + δ • u) (x - δ • u) := by
    apply openSegment_subset_segment
    refine ⟨1 / 2, 1 / 2, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · rw [smul_add, smul_sub]
      module
  rcases (mem_extremePoints_iff_forall_segment.1 hx).2 (x + δ • u) hy
    (x - δ • u) hz hxm with heq | heq
  · have h1 : (x + δ • u) - x = 0 := by rw [heq, sub_self]
    rw [add_sub_cancel_left] at h1
    exact hu0 (smul_right_injective _ hδ0.ne' (h1.trans (smul_zero δ).symm))
  · have h1 : (x - δ • u) - x = -( δ • u) := by abel
    rw [heq, sub_self] at h1
    exact hu0 (smul_right_injective _ hδ0.ne'
      ((neg_eq_zero.mp h1.symm).trans (smul_zero δ).symm))

/-- 紧凸凸集与 aff_ge 射线的交是自顶点出发的段（HOL
`HALFLINE_INTER_COMPACT_SEGMENT` 的 V3 移植；供 FLVNSME 阶段 6 用）。 -/
private theorem affGe_inter_compact_segment {s : Set V3} (hcomp : IsCompact s)
    (hconv : Convex ℝ s) {v w : V3} (hv : v ∈ s) :
    ∃ c, s ∩ affGe {v} {w} = segment ℝ v c := by
  classical
  by_cases hvw : v = w
  · subst hvw
    refine ⟨v, ?_⟩
    have haff : (affGe {v} {v} : Set V3) = {v} := by
      apply Set.ext fun y => ?_
      constructor
      · rintro ⟨f, hfin, hsum, -, hone⟩
        have hsub : hfin.toFinset = {v} := by
          rw [Finset.eq_singleton_iff_unique_mem]
          refine ⟨by simp, fun z hz => ?_⟩
          have h2 : z ∈ ({v} ∪ {v} : Set V3) := hfin.mem_toFinset.mp hz
          simp at h2
          exact h2
        simp only [hsub, Finset.sum_singleton] at hsum hone
        rw [hone, one_smul] at hsum
        exact Set.mem_singleton_iff.2 hsum
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have hfin : ({v} ∪ {v} : Set V3).Finite :=
          (Set.finite_singleton v).union (Set.finite_singleton v)
        have hsub : hfin.toFinset = {v} := by
          rw [Finset.eq_singleton_iff_unique_mem]
          refine ⟨by simp, fun z hz => ?_⟩
          have h2 : z ∈ ({v} ∪ {v} : Set V3) := hfin.mem_toFinset.mp hz
          simp at h2
          exact h2
        refine ⟨fun _ => (1:ℝ), hfin, ?_, ?_, ?_⟩
        · rw [hsub]; simp
        · intro z _; norm_num
        · rw [hsub]; simp
    rw [haff]
    have h2 : s ∩ {v} = {v} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩
    rw [h2, segment_same]
  · set e : V3 := w - v with he
    set F : ℝ → V3 := fun t => v + t • e with hFdef
    have he0 : e ≠ 0 := sub_ne_zero.mpr (fun h : w = v => hvw h.symm)
    have hFcont : Continuous F := by fun_prop
    set T : Set ℝ := F ⁻¹' s with hTdef
    have hmemT : ∀ t : ℝ, F t ∈ s ↔ t ∈ T := fun _ => Iff.rfl
    have h0T : 0 ∈ T := by
      have hF0 : F 0 ∈ s := by
        have : F 0 = v := by simp [hFdef]
        rw [this]; exact hv
      exact (hmemT 0).mpr hF0
    have hTconv : Convex ℝ T := by
      intro u1 hu1 u2 hu2 α β hα hβ hab
      refine (hmemT _).mpr ?_
      have key : α • F u1 + β • F u2 = F (α * u1 + β * u2) := by
        simp only [hFdef, smul_add, smul_smul, add_assoc, add_left_comm,
          ← add_smul, hab, one_smul]
        rw [← add_assoc, ← add_smul, hab, one_smul]
      have hmem' : α • F u1 + β • F u2 ∈ s :=
        hconv ((hmemT u1).mp hu1) ((hmemT u2).mp hu2) hα hβ hab
      rwa [key] at hmem'
    have hTclosed : IsClosed T := (hcomp.isClosed).preimage hFcont
    have hTbd : Bornology.IsBounded T := by
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : V3)).mp hcomp.isBounded
      rw [Metric.isBounded_iff_subset_ball (0 : ℝ)]
      refine ⟨(R + ‖v‖) / ‖e‖ + 1, fun t ht => ?_⟩
      have hFts : F t ∈ s := (hmemT t).mp ht
      have h1 : ‖F t‖ < R := by
        have h1' := Metric.mem_ball.1 (hR hFts)
        rwa [dist_zero_right] at h1'
      have hpos' : 0 < ‖e‖ := norm_pos_iff.mpr he0
      have h2 : ‖F t - v‖ ≤ ‖F t‖ + ‖v‖ := norm_sub_le _ _
      have h3 : ‖F t - v‖ = |t| * ‖e‖ := by
        simp only [hFdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have h5 : |t| * ‖e‖ < R + ‖v‖ := by rw [h3.symm]; linarith
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      have h6 : |t| ≤ (R + ‖v‖) / ‖e‖ := by
        rw [le_div_iff₀ hpos']
        linarith
      linarith
    have hTcomp : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTclosed hTbd
    have hTne : T.Nonempty := ⟨0, h0T⟩
    obtain ⟨t2, h2T, h2max⟩ := hTcomp.exists_isMaxOn hTne continuousOn_id
    have ht20 : (0:ℝ) ≤ t2 := h2max h0T
    have h0T' : 0 ∈ T := by
      have hF0v : F 0 = v := by simp [hFdef]
      have hv' : F 0 ∈ s := by rw [hF0v]; exact hv
      exact (hmemT 0).mpr hv'
    have hray : affGe {v} {w} = insert v {x : V3 | ∃ t : ℝ, 0 < t ∧ x = v + t • e} := by
      rw [AFF_GE_SING_CONVEX_HULL_ALT (Set.finite_singleton w) (fun h => hvw h)]
      congr 1
      ext x
      simp [convexHull_singleton, he]
    have hIci : T ∩ Set.Ici 0 = Set.Icc 0 t2 := by
      apply Set.ext fun t => ?_
      constructor
      · rintro ⟨ht, ht0⟩
        exact ⟨ht0, h2max ht⟩
      · intro ht
        obtain ⟨ht0, ht2le⟩ := ht
        by_cases ht20' : t2 = 0
        · have ht0' : t = 0 := by linarith
          rw [ht0']
          exact ⟨h0T, by norm_num⟩
        · have hpos2 : 0 < t2 := by
            rcases eq_or_lt_of_le ht20 with h | h
            · exact absurd h.symm ht20'
            · exact h
          have hlo : (0:ℝ) ≤ t / t2 := div_nonneg ht0 hpos2.le
          have hhi : t / t2 ≤ 1 := (div_le_one hpos2).2 ht2le
          have hlamt : (t / t2 : ℝ) * t2 = t := by field_simp
          have hA1 : (0:ℝ) ≤ 1 - t / t2 := sub_nonneg.mpr hhi
          have hA2 : 1 - t / t2 ≤ 1 := by
            have : (0:ℝ) ≤ t / t2 := hlo
            linarith
          have hmemT2 : (1 - t / t2 : ℝ) • (0 : ℝ) + (t / t2 : ℝ) • t2 ∈ T :=
            hTconv h0T h2T hA1 hlo (by ring)
          rw [smul_zero, zero_add, smul_eq_mul, hlamt] at hmemT2
          refine ⟨hmemT2, ?_⟩
          exact ht0
    refine ⟨v + t2 • e, ?_⟩
    have hkey : s ∩ affGe {v} {w} = F '' (T ∩ Set.Ici 0) := by
      rw [hray]
      refine Set.ext fun x => ?_
      constructor
      · rintro ⟨hxs, hx | ⟨t, ht0, rfl⟩⟩
        · refine ⟨0, ⟨h0T', by norm_num⟩, ?_⟩
          rw [hx]
          simp [hFdef]
        · exact ⟨t, ⟨(hmemT t).mp hxs, le_of_lt ht0⟩, rfl⟩
      · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
        refine ⟨(hmemT t).mp ht, ?_⟩
        rcases lt_or_eq_of_le (Set.mem_Ici.mp ht0) with hlt | hle0
        · exact Or.inr ⟨t, hlt, rfl⟩
        · left
          rw [← hle0]
          simp [hFdef]
    rw [hkey, hIci, image_Icc_eq_segment_p7 v e ht20]
    simp [hFdef]

/-- FLVNSME 阶段 1（P1）：过顶点 `v` 取得暴露 facet 的显式超平面形式
（HOL `EXPOSED_FACE_OF_POLYHEDRON` + `FACE_OF_POLYHEDRON_SUBSET_FACET` 链；
内部含 P0：`{v}` face 与 `p ≠ {v}` 的排除）。 -/
private theorem flvns_p1_exposed {v : V3} {p : Set V3}
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    (hv : v ∈ Set.extremePoints ℝ p) :
    ∃ f : Set V3, ∃ a' : V3, ∃ b' : ℝ,
      FacetOf f p ∧ f ≠ p ∧ f = p ∩ {x : V3 | a' ⬝ᵥ x = b'} ∧
      p ⊆ {x : V3 | a' ⬝ᵥ x ≤ b'} ∧ a' ≠ 0 ∧ 0 ≤ b' ∧ v ∈ f := by
  classical
  -- P0：{v} 是 p 的面，且 p ≠ {v}（否则与维数 3 矛盾）
  have hvsing : FaceOf {v} p := faceOf_sing.2 hv
  have h3p : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
  have hpvne : p ≠ {v} := by
    intro h
    have hz2 : (0:V3) ∈ interior {v} := by rw [h] at hz; exact hz
    have h3 := AFF_DIM_INTERIOR_EQ_3 0 {v} hz2
    rw [affDim_singleton] at h3
    omega
  obtain ⟨f, hf, hvf⟩ := FACE_OF_POLYHEDRON_SUBSET_FACET (s := p) hp hvsing
    (Set.singleton_ne_empty v) (Ne.symm hpvne)
  obtain ⟨a', b', ha0, hsub, hfeq⟩ := FACET_OF_POLYHEDRON hp hf
  refine ⟨f, a', b', hf, ?_, hfeq, hsub, ha0, ?_, hvf (Set.mem_singleton v)⟩
  · intro h
    rw [h] at hf
    have h2 := hf.2.2
    omega
  · have h0p : (0:V3) ∈ p := interior_subset hz
    have h01 : a' ⬝ᵥ (0:V3) ≤ b' := hsub h0p
    have h02 : a' ⬝ᵥ (0:V3) = 0 := by
      rw [← inner_eq_dot]
      exact inner_zero_right _
    rw [h02] at h01
    exact h01

/-- FLVNSME 阶段 2（P2）：原点在内部时，内部含深入开半空间
`{x | a⋅x < 0}` 的点（显式见证 y = -t•a，HOL `OPEN_HALFSPACE_LT` +
`IN_INTERIOR` 步骤的 V3 内联版）。 -/
private theorem flvns_p2_yint {p : Set V3} {a : V3}
    (hz : (0 : V3) ∈ interior p) (ha : a ≠ 0) :
    ∃ y, y ∈ interior p ∧ a ⬝ᵥ y < 0 := by
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.1 isOpen_interior (0 : V3) hz
  have haapos : 0 < a ⬝ᵥ a := by
    have h1 : 0 ≤ a ⬝ᵥ a := by
      show 0 ≤ (a.ofLp : Fin 3 → ℝ) ⬝ᵥ a.ofLp
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : a ⬝ᵥ a ≠ 0 := by
      intro h
      have h3 : (a.ofLp : Fin 3 → ℝ) ⬝ᵥ a.ofLp = 0 := h
      exact ha ((WithLp.ofLp_eq_zero 2).mp (dotProduct_self_eq_zero.mp h3))
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have ha0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnp : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  set t : ℝ := ε / (2 * ‖a‖) with ht
  have ht0 : 0 < t := by
    refine div_pos hε0 ?_
    linarith
  refine ⟨-t • a, ?_, ?_⟩
  · have hmem : -t • a ∈ Metric.ball (0 : V3) ε := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_neg, abs_of_pos ht0, ht, div_mul_eq_mul_div]
      have h2' : (0:ℝ) < 2 * ‖a‖ := by linarith [hnp]
      rw [div_lt_iff₀ h2']
      nlinarith [norm_pos_iff.mpr ha, hε0]
    exact hball hmem
  · have h4 : a ⬝ᵥ (-t • a) < 0 := by
      rw [p7_dot_smul, neg_mul]
      linarith [mul_pos ht0 haapos]
    exact h4

/-- FLVNSME 阶段 3（P3）：穿越点 z：给定 `a⋅y < 0 = a⋅v`，段 `[y,v]`
中点处于 p 且深入开半空间且异于 v（显式见证 z = lineMap y v (1/2)）。 -/
private theorem flvns_p3_cross {p : Set V3} (hconv : Convex ℝ p) {a y v : V3}
    (hy : y ∈ p) (hv : v ∈ p) (hay : a ⬝ᵥ y < 0) (hav : a ⬝ᵥ v = 0) :
    ∃ z, z ∈ segment ℝ y v ∧ z ∈ p ∧ a ⬝ᵥ z < 0 ∧ z ≠ v := by
  have h12 : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hay' : inner ℝ a y < 0 := by rw [inner_eq_dot]; exact hay
  have hav' : inner ℝ a v = 0 := by rw [inner_eq_dot]; exact hav
  refine ⟨AffineMap.lineMap y v (1 / 2 : ℝ), ?_, ?_, ?_⟩
  · exact lineMap_mem_segment (a := y) (b := v) (ht := h12)
  · exact hconv.lineMap_mem hy hv h12
  · constructor
    · rw [← inner_eq_dot, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub,
        inner_add_right, inner_smul_right, inner_sub_right, hav']
      linarith
    · intro h
      apply hay'.ne
      have h3 : inner ℝ a (AffineMap.lineMap y v (1 / 2 : ℝ)) = inner ℝ a v :=
        congrArg (fun z : V3 => inner ℝ a z) h
      rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, inner_add_right,
        inner_smul_right, inner_sub_right, hav'] at h3
      linarith

/-! ## polyhedron.hl :2005-:2995（FLVNSME，本批主菜） -/

/-- P4：切片暴露面底 `w` 与支撑泛函 `a2/b2`（HOL polyhedron.hl :2330-:2560
的核心代数）。在 `p` 内暴露顶点 `{w}` 得 `a'''/b''`（`p ⊆ {a'''·x ≤ b''}`、
`{w} = p ∩ {a'''·x = b''}`），令 `a2 = ((v-w)·a')•a''' - ((v-w)·a''')•a'`、
`b2 = a2·w`：由 `0 < (v-w)·a' = b'-b1` 乘开，`a2/b2` 在切片
`{a'·x = b1}` 上支撑且于 `w` 处取等，且 `a2·(v-w) = 0`——沿 `v-w` 方向
消失、在 `w` 处取等的支撑泛函（FLVNSME 阶段 6 收口用）。 -/
private theorem flvns_p4_descent
    {p : Set V3} (hpoly : polyhedron_p7 p)
    {a' : V3} {b1 b' : ℝ} (hbb : b1 < b')
    {v w : V3} (hw : w ∈ Set.extremePoints ℝ p)
    (ha'w : a' ⬝ᵥ w = b1) (ha'v : a' ⬝ᵥ v = b') :
    ∃ a2 : V3, ∃ b2 : ℝ,
      (∀ x ∈ p, x ∈ {x : V3 | a' ⬝ᵥ x = b1} → a2 ⬝ᵥ x ≤ b2) ∧
      a2 ⬝ᵥ w = b2 ∧ a2 ⬝ᵥ (v - w) = 0 ∧ a' ⬝ᵥ w = b1 := by
  classical
  -- V3 点积代数（Polytope.lean 私有 dot 引理的就地重述，inner 桥接）
  have dot_comm : ∀ x y : V3, x ⬝ᵥ y = y ⬝ᵥ x := fun x y => by
    rw [← inner_eq_dot, ← inner_eq_dot, real_inner_comm]
  have dot_sub_left : ∀ x y z : V3, (x - y) ⬝ᵥ z = x ⬝ᵥ z - y ⬝ᵥ z := fun x y z => by
    rw [← inner_eq_dot, ← inner_eq_dot, ← inner_eq_dot, inner_sub_left]
  have dot_sub_right : ∀ x y z : V3, x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z := fun x y z => by
    have hpi : ∀ (p : V3) (q r : Fin 3 → ℝ),
        p.ofLp ⬝ᵥ (q - r) = p.ofLp ⬝ᵥ q - p.ofLp ⬝ᵥ r := by
      intro p q r
      rw [show q - r = q + (-1 : ℝ) • r from by rw [sub_eq_add_neg, neg_one_smul],
        dotProduct_add, dotProduct_smul]
      ring
    exact hpi x y.ofLp z.ofLp
  have dot_lin : ∀ (u1 u2 : V3) (c1 c2 : ℝ) (z : V3),
      (c1 • u1 - c2 • u2) ⬝ᵥ z = c1 * (u1 ⬝ᵥ z) - c2 * (u2 ⬝ᵥ z) := by
    intro u1 u2 c1 c2 z
    rw [← inner_eq_dot, ← inner_eq_dot, ← inner_eq_dot,
      inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  -- EXPOSED_FACE_OF_POLYHEDRON：在 `p` 内暴露顶点 `{w}`
  have hpoly' : polyhedron p := hpoly
  obtain ⟨-, a''', b'', hpsub, hweq⟩ :=
    (EXPOSED_FACE_OF_POLYHEDRON (s := p) hpoly').2 (faceOf_sing.2 hw)
  have ha3w : a''' ⬝ᵥ w = b'' := by
    have h1 : w ∈ (p ∩ {x : V3 | a''' ⬝ᵥ x = b''} : Set V3) := by
      rw [← hweq]; exact Set.mem_singleton w
    simpa using h1.2
  set c1 : ℝ := (v - w) ⬝ᵥ a' with hc1
  set c2 : ℝ := (v - w) ⬝ᵥ a''' with hc2
  set a2 : V3 := c1 • a''' - c2 • a' with ha2
  -- 关键系数：`c1 = b' - b1 > 0`（0 < b' - b1 乘开用）
  have hs : c1 = b' - b1 := by
    rw [hc1, dot_sub_left, dot_comm v a', dot_comm w a', ha'v, ha'w]
  have hsp : 0 < c1 := by rw [hs]; linarith
  have hc2e : c2 = a''' ⬝ᵥ v - b'' := by
    rw [hc2, dot_sub_left, dot_comm v a''', dot_comm w a''', ha3w]
  have ha3vw : a''' ⬝ᵥ (v - w) = c2 := by rw [dot_sub_right, ha3w, ← hc2e]
  have ha1vw : a' ⬝ᵥ (v - w) = b' - b1 := by rw [dot_sub_right, ha'v, ha'w]
  refine ⟨a2, a2 ⬝ᵥ w, ?_, rfl, ?_, ha'w⟩
  · -- 切片上支撑：a2·x = c1·(a'''·x) - c2·b1 ≤ c1·b'' - c2·b1 = b2
    intro x hx hxs
    simp only [Set.mem_setOf_eq] at hxs
    have e1 : a2 ⬝ᵥ x = c1 * (a''' ⬝ᵥ x) - c2 * b1 := by
      rw [ha2, dot_lin a''' a' c1 c2 x, hxs]
    have e2 : a2 ⬝ᵥ w = c1 * b'' - c2 * b1 := by
      rw [ha2, dot_lin a''' a' c1 c2 w, ha3w, ha'w]
    have hmul : c1 * (a''' ⬝ᵥ x) ≤ c1 * b'' :=
      mul_le_mul_of_nonneg_left (hpsub hx) hsp.le
    rw [e1, e2]
    linarith
  -- 沿 v-w 方向消失：a2·(v-w) = c1·c2 - c2·(b'-b1) = 0
  · show (c1 • a''' - c2 • a') ⬝ᵥ (v - w) = 0
    rw [dot_lin, ha3vw, ha1vw, hs]
    ring

/-- HOL polyhedron.hl :2005-:2995 `FLVNSME`（HOL 文件最大证明块，约
1000 行）

HOL 原文：
```
!v A a b p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
 /\ A={x| a dot x < b } /\ ~(a= vec 0)
/\ v IN {x| a dot x = b } /\ vec 0 IN {x| a dot x = b }
/\ v IN vertices p
==> ?w. w IN vertices p /\ w IN A/\ {v,w} IN edges p
```

几何含义：过顶点 `v` 的支撑超平面 `{a·x = b}`（原点也在其上）是某个
facet 的所在平面；从 `v` 出发必有一条（真）边 `≥v,w≥` 深入开半空间
`A = {a·x < b}`。

编码说明：`vertices p` ↦ `Set.extremePoints ℝ p`、`edges p` ↦
`edges_p7`（本文件）；`A`/`v`/`a`/`b`/`p` 保持显式参数（HOL 全称；
`A` 的定义式作为假设 `hA` 冻结）。

证明思路（HOL 原证按本 lane 采样复述——窗口 :2005-:2104 全读、
:2104-:2136 / :2215-:2330 / :2400-:2520 / :2560-:2680 采样、
:2890-:2995 全读；六个阶段）：

1. **setup（:2005-:2104）**：`vertices` 展开 + `GSYM FACE_OF_SING` 得
   `{v} face_of p`；`AFF_DIM_SING` + `AFF_DIM_INTERIOR_EQ_3` 排除
   `p = {v}`；`FACE_OF_POLYHEDRON_SUBSET_FACET` + `EXPOSED_FACE_OF_
   POLYHEDRON` 取过 `v` 的暴露 facet `f = p ∩ {a'·x = b'}`；令
   `s = {--a'·w | w ∈ vertices p, w ≠ v}`，由 `EXISTS_EDGE_AT_VERTICES`
   于 `v` 知其非空，`FINITE_IMAGE` 知其有限；内引理（`INF_FINITE`）取
   最小元 `--a''`；若 `--a'' ≥ b'` 则 `a'·w = b'`，由 facet 等式
   `{v} = p ∩ {a'·x = b'}` 迫 `w = v`，矛盾，故 `--a'' < b'`；
   `INTERIOR_SUBSET` 给 `0 ≤ b'`。
2. **归一化（:2104-:2136）**：`b' = 0` 迫 `v = vec 0`，与
   `EXTREME_POINT_NOT_IN_INTERIOR` 矛盾，故 `0 < b'`；取
   `b1 = max(--a'',0) + (b'-max(--a'',0))/2`，有 `--a'' < b1 < b'`、
   `0 < b1`；证明 `vertices p ∩ {a'·x ≥ b1} = {v}`；令
   `p' = p ∩ {a'·x = b1}`；`OPEN_HALFSPACE_LT` + `IN_INTERIOR` +
   `CLOSURE_HALFSPACE_LT` + `CLOSURE_APPROACHABLE` 在
   `ball(0, min e e'/2)` 内取 `y ∈ interior p ∩ A`（`0 < a·y < b`）。
3. **截线（:2215-:2330）**：显式参数
   `t = inv(a'·v - a'·y)·(b1 - a'·y) ∈ (0,1)` 给
   `z ∈ segment[y,v] ∩ {a'·x = b1} ∧ z ≠ v`；`POLYHEDRON_IMP_CONVEX` +
   `SUBSET_HULL` + `SEGMENT_CONVEX_HULL` 给 `segment[y,v] ⊆ p`；
   `CONVEX_HALFSPACE_LE` 给 `segment[v,y] ⊆ {a·x ≤ b}`，由 `z ≠ v` 分支
   得 `a·z < b`，即 `z ∈ A`。
4. **暴露面下潜（:2330-:2560，采样 :2400-:2520）**：`p1 :=
   p ∩ {a'·x ≥ b1}`（凸紧），`FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`
   + `EXPOSED_FACE_OF_POLYHEDRON` 两次下潜取 `{w} = p' ∩ {a'''·x =
   b''}`；令 `a2 = (v-w) × (a''' × a')`、`b2 = a2·w`，
   `CROSS_LADD`/`CROSS_LAGRANGE`/`DOT_*` 系数簿记证明
   `{a'·x = b1} ∩ {a'''·x ≤ b''} = {a'·x = b1} ∩ {a2·x ≤ b2}`（= 变体
   同理），关键用 `0 < b'-b1` 乘开 `REAL_LE_MUL`。
5. **重心迁移（:2560-:2890，采样 :2560-:2680）**：`KREIN_MILMAN_
   MINKOWSKI`（`GSYM vertices`）把 `v` 写成有限 `s' ⊆ vertices p` 上的
   凸组合 `Σ u(x)%x`；`s1 = s' \ {v}`，`SUM_DELETE_CASES`/
   `VSUM_DELETE_CASES` + `SUM_POS_EQ_0`/`VSUM_EQ_0` 处理 `t12 = 0` 分支；
   重权 `inv t12 % v12 ∈ p`（凸组合系数非负）、
   `a'·(inv t12 % v12) ≤ b1`（逐点 `a'·x < b1` 求和）、
   `inv t12 % v12 ≠ v`；`AFF_GE_1_1` + 显式系数（`t1 - t2·inv t12·u v`
   等）证 `aff_ge {v}{inv t12 % v12} = aff_ge {v}{w}`。
6. **收口（:2890-:2995）**：`aff_ge {v}{w} ⊆ {a2·x = b2}`（AFF_GE_1_1 +
   点积线性）；由 4 的等式得 `p ∩ {a2·x = b2} ⊆ aff_ge {v}{w}`；
   `POLYTOPE_IMP_COMPACT` + `HALFLINE_INTER_COMPACT_SEGMENT` 给
   `p ∩ {a2·x = b2} = segment[v,c]`；`FACE_OF_INTER_SUPPORTING_
   HYPERPLANE_LE_STRONG` + `SEGMENT_FACE_OF` 使其为 `p` 的面；
   `w ∈ segment[v,c]`、`w ≠ v` ⇒ `v ≠ c`（`SEGMENT_EQ_SING`）；取见证
   `w ∈ A`（`t2 > 0` 时 `REAL_LT_LMUL`），最后 `{v,c} IN edges p` 由
   `edge_of` 内联 + `AFFINE_HULL_SEGMENT` + `AFF_DIM_2` 收口。

候选已有引理：
- `EXISTS_EDGE_AT_VERTICES`（本文件上文；阶段 1 非空性）
- `segment`/`openSegment`/`convex_segment`（Mathlib Analysis/Convex/Segment）
- `isOpen_halfspace_lt`、`closure_halfspace_lt`-类（Mathlib
  Analysis/Convex/ Halfspace；对应 `OPEN/CLOSURE_HALFSPACE_LT`）、
  `Metric.ball`、`interior`（Mathlib）
- `Convex ℝ`、`convexHull`（Mathlib；对应 `SUBSET_HULL`/
  `SEGMENT_CONVEX_HULL`、`KREIN_MILMAN_MINKOWSKI`）
- 缺口（上游未移植，填充时需先建）：`AFF_DIM_INTERIOR_EQ_3`、
  `FACE_OF_POLYHEDRON_SUBSET_FACET`、`EXPOSED_FACE_OF_POLYHEDRON`、
  `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE/LE_STRONG`、
  `HALFLINE_INTER_COMPACT_SEGMENT`、`SEGMENT_FACE_OF`、
  `SEGMENT_EQ_SING`、`EXTREME_POINT_NOT_IN_INTERIOR`、
  `KREIN_MILMAN_MINKOWSKI`、`SUM_DELETE_CASES`/`VSUM_DELETE_CASES` -/
theorem FLVNSME {v : V3} {A : Set V3} {a : V3} {b : ℝ} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p)
    (hz : (0 : V3) ∈ interior p) (hA : A = {x : V3 | a ⬝ᵥ x < b})
    (ha : a ≠ 0) (hv : v ∈ {x : V3 | a ⬝ᵥ x = b})
    (h0 : (0 : V3) ∈ {x : V3 | a ⬝ᵥ x = b})
    (hv' : v ∈ Set.extremePoints ℝ p) :
    ∃ w : V3, w ∈ Set.extremePoints ℝ p ∧ w ∈ A ∧ {v, w} ∈ edges_p7 p := by
  sorry

/-! ## polyhedron.hl :2996-:3200（fan 性质与 conforming 桥） -/

/-- HOL polyhedron.hl :2996-:3026 `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>  (!v. v IN vertices p ==>CARD (set_of_edge v (vertices p) (edges p)) >1)
```

编码说明：`CARD s > 1` ↔ `1 < s.ncard`（ConformingDefs.lean 头先例，
无限集 ncard = 0 约定与 HOL 有限性前提相容）。

证明思路（HOL）：`EXISTS_EDGE_AT_VERTICES` 给一个邻居 `w`；
`POLYHEDRON_FAN`（Kepler/Text/PolyAuto3.lean:279，签名与本文件 V/E 编码
逐字一致）得 fan 结构；`remark1_fan`（fan.hl，未移植）+ `properties_
coordinate`（fan.hl，未移植）取 `v,w` 处标准正交基
`e1_fan/e2_fan/e3_fan`（↦ `e1Fan/e2Fan/e3Fan`，Kepler/Text/TopologyFan
.lean:2268-2272，`orthonormal_e1Fan_e2Fan_e3Fan` :3499）并以
`a = e2_fan 0 v w` 实例化 `FLVNSME`（`A = {x | a·x < 0}`，
`DOT_RZERO`）；得 `w'` 顶点、`a·w' < 0`、`{v,w'} ∈ edges p`；
`w' ≠ w`（否则 `0 < a·w` 与 `< 0` 矛盾，`ONCE_REWRITE_TAC[DOT_SYM]`）；
`{w,w'} ⊆ setOfEdge v V E` + `CARD_SUBSET` + `CARD_2_FAN`
（Kepler/Text/Planarity.lean:4975）给 `CARD ≥ 2 > 1`。

候选已有引理：
- `EXISTS_EDGE_AT_VERTICES`、`FLVNSME`（本文件上文）
- `POLYHEDRON_FAN`（Kepler/Text/PolyAuto3.lean:279；跨批依赖，签名兼容）
- `e1Fan`/`e2Fan`/`e3Fan`、`orthonormal_e1Fan_e2Fan_e3Fan`、
  `ORTHONORMAL`-非零（Kepler/Text/TopologyFan.lean:2268-2272,3499）
- `CARD_2_FAN`（Kepler/Text/Planarity.lean:4975）、`Set.ncard_le`/
  `ncard_mono`（Mathlib；对应 `CARD_SUBSET`）
- 缺口：`remark1_fan`、`properties_coordinate`（fan.hl）未移植 -/
theorem CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p)
    (hz : (0 : V3) ∈ interior p) :
    ∀ v ∈ Set.extremePoints ℝ p,
      1 < (setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p)).ncard := by
  intro v hv
  -- fan 结构（POLYHEDRON_FAN，PolyAuto3 冻结语句；编码逐字一致）
  have hfan : FAN 0 (Set.extremePoints ℝ p) (edges_p7 p) :=
    POLYHEDRON_FAN hb hp hz
  have hvz : v ≠ 0 := fun he => hfan.2.2.2.1 (by rw [he] at hv; exact hv)
  -- 一个邻居（EXISTS_EDGE_AT_VERTICES）
  obtain ⟨w, hwE, hwV⟩ :=
    Set.nonempty_iff_ne_empty.mpr (EXISTS_EDGE_AT_VERTICES hb hp hz v hv)
  have hnc := fan_not_collinear hfan hwE
  -- 法向 `n = v × w`（V3 侧）
  set n : V3 := WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) with hn
  have hv0p : (v : Fin 3 → ℝ) ≠ 0 := by
    intro he
    refine hvz ?_
    exact (WithLp.ofLp_eq_zero 2).mp he
  have ha0 : n ≠ 0 := by
    intro hne
    apply hnc
    have h2 : (n : Fin 3 → ℝ) = (0 : Fin 3 → ℝ) := by rw [hne, WithLp.ofLp_zero]
    have hcp : (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) = (0 : Fin 3 → ℝ) := by
      rw [hn] at h2
      rwa [coe_toLp] at h2
    have hli : ¬LinearIndependent ℝ ![(v : Fin 3 → ℝ), (w : Fin 3 → ℝ)] := fun hl =>
      ((crossProduct_ne_zero_iff_linearIndependent (v := (v : Fin 3 → ℝ))
        (w := (w : Fin 3 → ℝ))).mpr hl) hcp
    rw [LinearIndependent.pair_iff' hv0p] at hli
    push_neg at hli
    obtain ⟨c, hc⟩ := hli
    refine (collinear3_iff_smul hvz).mpr ⟨c, ?_⟩
    apply WithLp.ofLp_injective
    simp [hc]
  have hnv : n ⬝ᵥ v = 0 := by
    rw [hn, dot_toLp, dotProduct_comm, dot_self_cross]
  have hnw : n ⬝ᵥ w = 0 := by
    rw [hn, dot_toLp, dotProduct_comm, dot_cross_self]
  have hn0 : n ⬝ᵥ (0 : V3) = 0 := by
    rw [dot_toLp, WithLp.ofLp_zero, dotProduct_zero]
  -- FLVNSME：从 `v` 深入开半空间 `{n·x < 0}` 的边到达 `w'`
  obtain ⟨w', hw'V, hw'A, hw'E⟩ :=
    FLVNSME (v := v) (a := n) (b := 0) hb hp hz rfl ha0
      (by simpa using hnv) (by simpa using hn0) hv
  simp only [Set.mem_setOf_eq] at hw'A
  have hnnv : (n : Fin 3 → ℝ) ⬝ᵥ (v : Fin 3 → ℝ) = 0 := by
    rw [← dot_toLp]; exact hnv
  -- `w'` 是与 `w` 不同的邻居
  have hww : w ≠ w' := by
    intro he
    rw [← he] at hw'A
    linarith
  have hcard : ({w, w'} : Set V3).ncard = 2 := CARD_2_FAN hww
  have hsub : ({w, w'} : Set V3) ⊆
      setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p) := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | rfl
    · exact ⟨hwE, hwV⟩
    · exact ⟨hw'E, hw'V⟩
  have hVfin : (Set.extremePoints ℝ p).Finite := FINITE_POLYHEDRON_EXTREME_POINTS hp
  have hsefin : (setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p)).Finite :=
    Set.Finite.subset hVfin fun x hx => hx.2
  have h2 : (2 : ℕ) ≤ (setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p)).ncard := by
    refine le_trans (le_of_eq hcard.symm) (Set.ncard_le_ncard hsub hsefin)
  omega

/-! ## 填充辅助：V3-叉积簿记（liangou） -/

/-- V3 点积的 Pi-侧展开。 -/
private theorem p7_dot_pi {n y : V3} :
    n ⬝ᵥ y = (n : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
  have h1 : n = WithLp.toLp 2 (n : Fin 3 → ℝ) := (WithLp.toLp_ofLp 2 n).symm
  rw [h1, dot_toLp]

/-- 任意 `n` 与原点的点积为零。 -/
private theorem p7_dot_zero (n : V3) : n ⬝ᵥ (0 : V3) = 0 := by
  rw [p7_dot_pi, WithLp.ofLp_zero, dotProduct_zero]

/-- 负号的点积。 -/
private theorem p7_neg_dot {n y : V3} : (-n) ⬝ᵥ y = -(n ⬝ᵥ y) := by
  rw [p7_dot_pi, WithLp.ofLp_neg, neg_dotProduct, ← p7_dot_pi]

/-- `v × w` 与 `v` 的点积为零（`DOT_SELF_CROSS`）。 -/
private theorem p7_cross_dot_v (v w : V3) :
    (WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3) ⬝ᵥ v = 0 := by
  rw [dot_toLp, dotProduct_comm, dot_self_cross]

/-- `v × w` 与 `w` 的点积为零（`DOT_CROSS_SELF`）。 -/
private theorem p7_cross_dot_w (v w : V3) :
    (WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3) ⬝ᵥ w = 0 := by
  rw [dot_toLp, dotProduct_comm, dot_cross_self]

/-- 非零性：`¬Collinear3 0 v w` 给 `v × w ≠ 0`。 -/
private theorem p7_cross_ne {v w : V3} (hnc : ¬ Collinear3 0 v w) :
    (WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3) ≠ 0 := by
  intro hne
  apply hnc
  have hvz : v ≠ 0 := by
    intro he
    apply hnc
    rw [he]
    exact collinear3_of_eq rfl
  have h2 : ((WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ)
      = ((0 : V3) : Fin 3 → ℝ) := by rw [hne]
  have hcp : (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) = (0 : Fin 3 → ℝ) := by
    rwa [coe_toLp, WithLp.ofLp_zero] at h2
  have hv0p : (v : Fin 3 → ℝ) ≠ 0 := by
    intro he
    exact hvz ((WithLp.ofLp_eq_zero 2).mp he)
  have hli : ¬LinearIndependent ℝ ![(v : Fin 3 → ℝ), (w : Fin 3 → ℝ)] := fun hl =>
    ((crossProduct_ne_zero_iff_linearIndependent (v := (v : Fin 3 → ℝ))
      (w := (w : Fin 3 → ℝ))).mpr hl) hcp
  rw [LinearIndependent.pair_iff' hv0p] at hli
  push_neg at hli
  obtain ⟨c, hc⟩ := hli
  refine (collinear3_iff_smul hvz).mpr ⟨c, ?_⟩
  apply WithLp.ofLp_injective
  simp [hc]

/-- 共线性消灭点积：`0,v,w'` 共线且 `n ⊥ v` ⇒ `n ⬝ᵥ w' = 0`。 -/
private theorem p7_collinear_dot {v w' n : V3} (hvz : v ≠ 0)
    (hcol : Collinear3 0 v w') (hnv : n ⬝ᵥ v = 0) : n ⬝ᵥ w' = 0 := by
  obtain ⟨c, hc⟩ := (collinear3_iff_smul hvz).mp hcol
  have hpi : (w' : Fin 3 → ℝ) = c • (v : Fin 3 → ℝ) := by
    have h2 := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hc
    simp at h2
    exact h2
  have h5 : n ⬝ᵥ w' = (n : Fin 3 → ℝ) ⬝ᵥ (w' : Fin 3 → ℝ) := p7_dot_pi
  have h6 : (n : Fin 3 → ℝ) ⬝ᵥ (v : Fin 3 → ℝ) = 0 := by rw [← p7_dot_pi]; exact hnv
  rw [h5, hpi, dotProduct_smul, h6]
  simp

/-- sin 为正 + azim 值域 ⇒ `azim 0 v u w < π`（JBDNJJB 的收口）。 -/
private theorem p7_azim_lt_pi {v u w : V3} (h1 : ¬ Collinear3 0 v u)
    (h2 : ¬ Collinear3 0 v w)
    (hpos : 0 < (crossProduct (v : Fin 3 → ℝ) (u : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)) :
    azim 0 v u w < Real.pi := by
  obtain ⟨t, ht, hs⟩ := JBDNJJB h1 h2
  by_cases hle : azim 0 v u w < Real.pi
  · exact hle
  · exfalso
    have hnn := azim_nonneg 0 v u w
    have hπle : Real.pi ≤ azim 0 v u w := le_of_not_gt hle
    have hlt2 : azim 0 v u w < 2 * Real.pi := azim_lt_two_pi 0 v u w
    have hsn : 0 ≤ Real.sin (azim 0 v u w - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsplit : Real.sin (azim 0 v u w)
        = -Real.sin (azim 0 v u w - Real.pi) := by
      have hadd := Real.sin_add (azim 0 v u w - Real.pi) Real.pi
      rw [Real.sin_pi, Real.cos_pi] at hadd
      have heq : (azim 0 v u w - Real.pi) + Real.pi = azim 0 v u w := by linarith
      rw [heq] at hadd
      linarith
    have hK : t * ((crossProduct (v : Fin 3 → ℝ) (u : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)) ≤ 0 := by
      rw [← hs, hsplit]
      linarith
    have hKpos : 0 < t * ((crossProduct (v : Fin 3 → ℝ) (u : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)) := by
      nlinarith
    exact absurd hKpos (by intro hh; linarith)

/-! ## polyhedron.hl :3028-:3088 `BSXAQBQ` -/

/-- HOL polyhedron.hl :3028-:3088 `BSXAQBQ`

HOL 原文：
```
!p:real^3->bool x.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
/\ x IN d_fan((vec 0),(vertices p),(edges p))
==> azim_fan (vec 0) (vertices p) (edges p) (pr2 x) (pr3 x) < pi
```

编码说明：`d_fan` ↦ `dartOfFan V E`（Fan.lean:90，apex 丢弃、二元组
dart，ConformingDefs.lean 头先例）；`pr2 x`/`pr3 x` ↦ `x.1`/`x.2`；
`azim_fan` ↦ `azimFan`（Fan.lean:177）。

证明思路（HOL）：`CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`（LABEL_TAC "LINH"）
+ `POLYHEDRON_FAN` + `dartset_fully_surrounded_is_non_isolated_fan`
（↦ `dartOfFan_eq_dart1_of_surrounded`，Kepler/Text/Fan.lean:1084，把
`d_fan` 化为 `d1_fan`，即 `x = (v,w)`、`{v,w} ∈ E`）；`remark1_fan` +
`FLVNSME`（`a = v × w` 的反向、`b = 0`）取 `w'`：
`--(v×w)·w' < 0` 即 `(v×w)·w' > 0`；`w' = w` 时 `DOT_CROSS_SELF`
（`CROSS_EQ_0`）矛盾；否则 `SIGMA_FAN`（Fan.lean:317）取
`σ_fan v w`-邻域内 `azim` 极小者，`JBDNJJB`（Kepler/Text/Planarity
.lean:2702）给 `t·(a·w') > 0` 型正性，`azim < 2π` 分支用
`SIN_POS_PI_LE`（`SIN_SUB`/`SIN_PI`/`COS_PI` 簿记）排除
`azim - π ≥ 0`。

候选已有引理：
- `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`（本文件上文）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）、`azimFan`（Fan.lean:177）
- `JBDNJJB`（Kepler/Text/Planarity.lean:2702）
- `Real.sin_sub`、`Real.sin_pi`、`Real.cos_pi`（Mathlib）
- 缺口：`remark1_fan`（fan.hl）未移植 -/
theorem BSXAQBQ {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) {x : V3 × V3}
    (hx : x ∈ dartOfFan (Set.extremePoints ℝ p) (edges_p7 p)) :
    azimFan 0 (Set.extremePoints ℝ p) (edges_p7 p) x.1 x.2 < Real.pi := by
  have hfan : FAN 0 (Set.extremePoints ℝ p) (edges_p7 p) :=
    POLYHEDRON_FAN hb hp hz
  have hcard := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hz
  rw [dartOfFan, Set.mem_union] at hx
  rcases hx with ⟨h11, hx1V, hse⟩ | hx1
  · refine absurd (hcard x.1 hx1V) ?_
    intro hc
    rw [hse, Set.ncard_empty] at hc
    norm_num at hc
  · simp only [dart1OfFan, Set.mem_setOf_eq] at hx1
    have hx1V : x.1 ∈ Set.extremePoints ℝ p := (fan_mem_of_edge hfan hx1).1
    rw [azimFan, if_pos (hcard x.1 hx1V)]
    have hu : x.2 ∈ setOfEdge x.1 (Set.extremePoints ℝ p) (edges_p7 p) :=
      (properties_of_setOfEdge_fan 0 (Set.extremePoints ℝ p) (edges_p7 p) x.1 x.2 hfan).mp hx1
    have hne : setOfEdge x.1 (Set.extremePoints ℝ p) (edges_p7 p) ≠ {x.2} := by
      intro he
      have hc := hcard x.1 hx1V
      rw [he, Set.ncard_singleton] at hc
      omega
    obtain ⟨hσ, hσu, hmin⟩ := SIGMA_FAN hne hfan hu
    set n : V3 := WithLp.toLp 2 (crossProduct (x.1 : Fin 3 → ℝ) (x.2 : Fin 3 → ℝ)) with hndef
    have hnc : ¬ Collinear3 0 x.1 x.2 := fan_not_collinear hfan hx1
    have ha0 : (-n) ≠ 0 := neg_ne_zero.2 (p7_cross_ne hnc)
    have hnv : n ⬝ᵥ x.1 = 0 := p7_cross_dot_v x.1 x.2
    obtain ⟨w', hw'V, hw'A, hw'E⟩ :=
      FLVNSME (v := x.1) (a := -n) (b := 0) hb hp hz rfl ha0
        (by simp only [Set.mem_setOf_eq]; rw [p7_neg_dot, hnv]; simp)
        (by simp only [Set.mem_setOf_eq]; rw [p7_neg_dot, p7_dot_zero]; simp) hx1V
    simp only [Set.mem_setOf_eq] at hw'A
    have hpos : 0 < n ⬝ᵥ w' := by
      have h9 := p7_neg_dot (n := n) (y := w')
      have h10 := hw'A
      rw [h9] at h10
      linarith
    have hvz : x.1 ≠ 0 := fun he => hfan.2.2.2.1 (by rw [he] at hx1V; exact hx1V)
    have hncw : ¬ Collinear3 0 x.1 w' := by
      intro hcol
      linarith [p7_collinear_dot hvz hcol hnv, hpos]
    have hlt := p7_azim_lt_pi hnc hncw hpos
    have hw'u : w' ≠ x.2 := by
      intro he
      have h2 := p7_cross_dot_w x.1 x.2
      rw [he] at hpos
      linarith
    have := hmin w'
      ((properties_of_setOfEdge_fan 0 (Set.extremePoints ℝ p) (edges_p7 p) x.1 w' hfan).mp hw'E)
      hw'u
    linarith

/-- HOL polyhedron.hl :3090-:3156 `POLYTOPE_FAN80`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==> fan80 (vec 0,vertices p,edges p)
```

编码说明：`fan80` ↦ `fan80`（Kepler/Text/Fan.lean:227）。

证明思路（HOL）：与 `BSXAQBQ` 孪生（差异仅在方向 `a = v × u` 与收口多
一层 σ-传递）：展开 `fan80` 后对 `{v,u} ∈ E`；`CARD_SET_OF_EDGE_INEQ_1_
POLYHEDRON` + `POLYHEDRON_FAN` + `remark1_fan`；`FLVNSME`（`a = --(v×u)`、
`b = 0`）给 `w`：`(v×u)·w > 0` 且 `{v,w} ∈ E`；`u = w` 由
`DOT_CROSS_SELF` 排除；`SIGMA_FAN` + `JBDNJJB` + `REAL_LT_MUL` 得
`azim 0 v u w < 2π` 的上界，`SIN_POS_PI_LE` 分支排除 `azim ≥ π`；
再由 `azim 0 v u σ ≤ azim 0 v u w < π`（σ 的极小性）与
`UNIQUE_AZIM_0_POINT_FAN`（↦ `unique_azim0_point_fan`，
Kepler/Text/Fan.lean:456）收口 `0 < azim 0 v u σ < π`。

候选已有引理：
- `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`、`FLVNSME`（本文件上文）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）、`sigmaFan`（Fan.lean:66）
- `unique_azim0_point_fan`（Kepler/Text/Fan.lean:456）
- `JBDNJJB`（Kepler/Text/Planarity.lean:2702）
- `azim` 基础（Kepler/Geom/Azim.lean）
- 缺口：`remark1_fan`（fan.hl）未移植 -/
theorem POLYTOPE_FAN80 {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    fan80 0 (Set.extremePoints ℝ p) (edges_p7 p) := by
  have hfan : FAN 0 (Set.extremePoints ℝ p) (edges_p7 p) :=
    POLYHEDRON_FAN hb hp hz
  have hcard := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hz
  intro v u hu
  have hvV : v ∈ Set.extremePoints ℝ p := (fan_mem_of_edge hfan hu).1
  have h1 := hcard v hvV
  have hu' : u ∈ setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p) :=
    (properties_of_setOfEdge_fan 0 (Set.extremePoints ℝ p) (edges_p7 p) v u hfan).mp hu
  have hne : setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p) ≠ {u} := by
    intro he
    rw [he, Set.ncard_singleton] at h1
    omega
  obtain ⟨hσ, hσu, hmin⟩ := SIGMA_FAN hne hfan hu'
  set n : V3 := WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (u : Fin 3 → ℝ)) with hndef
  have hnc : ¬ Collinear3 0 v u := fan_not_collinear hfan hu
  have ha0 : (-n) ≠ 0 := neg_ne_zero.2 (p7_cross_ne hnc)
  have hnv : n ⬝ᵥ v = 0 := p7_cross_dot_v v u
  obtain ⟨w', hw'V, hw'A, hw'E⟩ :=
    FLVNSME (v := v) (a := -n) (b := 0) hb hp hz rfl ha0
      (by simp only [Set.mem_setOf_eq]; rw [p7_neg_dot, hnv]; simp)
      (by simp only [Set.mem_setOf_eq]; rw [p7_neg_dot, p7_dot_zero]; simp) hvV
  simp only [Set.mem_setOf_eq] at hw'A
  have hpos : 0 < n ⬝ᵥ w' := by
    have h9 := p7_neg_dot (n := n) (y := w')
    have h10 := hw'A
    rw [h9] at h10
    linarith
  have hvz : v ≠ 0 := fun he => hfan.2.2.2.1 (by rw [he] at hvV; exact hvV)
  have hncw : ¬ Collinear3 0 v w' := by
    intro hcol
    linarith [p7_collinear_dot hvz hcol hnv, hpos]
  have hlt := p7_azim_lt_pi hnc hncw hpos
  have hw'u : w' ≠ u := by
    intro he
    have h2 := p7_cross_dot_w v u
    rw [he] at hpos
    linarith
  have hmin' := hmin w'
    ((properties_of_setOfEdge_fan 0 (Set.extremePoints ℝ p) (edges_p7 p) v w' hfan).mp hw'E)
    hw'u
  refine ⟨?_, ?_⟩
  · have hnn := azim_nonneg 0 v u (sigmaFan 0 (Set.extremePoints ℝ p) (edges_p7 p) v u)
    rcases lt_or_eq_of_le hnn with h0 | h0
    · exact h0
    · have hσE : {v, sigmaFan 0 (Set.extremePoints ℝ p) (edges_p7 p) v u} ∈ edges_p7 p :=
        (properties_of_setOfEdge_fan 0 (Set.extremePoints ℝ p) (edges_p7 p) v
          (sigmaFan 0 (Set.extremePoints ℝ p) (edges_p7 p) v u) hfan).mpr hσ
      exact absurd (unique_azim0_point_fan hfan hu hσE h0.symm).symm hσu
  · linarith

/-- HOL polyhedron.hl :3158-:3187 `WBLARHH`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>
 (!f. f IN face_set (hypermap1_of_fanx  (vec 0,vertices p,edges p)) ==> (?!f1. f1 facet_of p /\
							 dartset_leads_into_fan (vec 0) (vertices p) (edges p) f = fchanged f1))
```

编码说明：`hypermap1_of_fanx` 未移植——`face_set` 编码为
`(hypermapOfFan 0 V E hfan).faceSet`（pair darts），按 ConformingDefs
头先例携带显式 `hfan : FAN 0 V E` 见证（唯一签名偏差）；`f` 类型为
`Set (V3 × V3)`；`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`
（Kepler/Text/PlanarityComponent.lean:348）。

证明思路（HOL）：`POLYHEDRON_FAN` + `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`
（LINH）+ `POLYTOPE_FAN80`（本文件上文）凑齐 conforming 三前提；
`dartset_leads_into_is_topological_component_yfan`
（Kepler/Text/PlanarityComponent.lean:535）把
`s = dartsetLeadsIntoFan ... f` 送入 `topologicalComponentYfan`；
`PIIJBJK`（Kepler/Text/ConformingAuto21.lean:903，需 conforming_fan/
conforming_bijection_fan 展开）保证每个 yfan-分量恰为某面的
dartsetLeadsInto 像；最后 `AMHFNXP`（本文件上文）给出唯一 facet
`f1` 使 `s = fchanged_p7 f1`。

候选已有引理：
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535；签名即按本文件 hfan 约定）
- `PIIJBJK`（Kepler/Text/ConformingAuto21.lean:903）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）、`Hypermap.faceSet`
  （Kepler/Text/Hypermap.lean:1008）
- `AMHFNXP`（本文件上文）
- 跨批依赖：`PIIJBJK` 需 ConformingAuto 链（经 PlanarityAuto16 传递可
  用）；HOL 证明中的 `REMOVE_ASSUM_TAC`-清理不进陈述 -/
theorem WBLARHH {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    (hfan : FAN 0 (Set.extremePoints ℝ p) (edges_p7 p))
    {f : Set (V3 × V3)}
    (hf : f ∈ (hypermapOfFan 0 (Set.extremePoints ℝ p) (edges_p7 p) hfan).faceSet) :
    ∃! f1 : Set V3, FacetOf_p7 f1 p ∧
      dartsetLeadsIntoFan 0 (Set.extremePoints ℝ p) (edges_p7 p) f = fchanged_p7 f1 := by
  have hcard := CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON hb hp hz
  have h80 := POLYTOPE_FAN80 hb hp hz
  -- dartsetLeadsInto 像是 yfan-拓扑分量（conforming 三前提齐备）
  have hcomp : dartsetLeadsIntoFan 0 (Set.extremePoints ℝ p) (edges_p7 p) f ∈
      topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p) :=
    dartset_leads_into_is_topological_component_yfan hfan hcard h80 hf
  -- AMHFNXP 给出唯一 facet
  exact AMHFNXP hb hp hz _ hcomp

end Kepler.Text

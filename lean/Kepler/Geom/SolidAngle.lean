/-
Kepler.Geom.SolidAngle — HOL Light `VOLUME_SOLID_TRIANGLE`
（`Multivariate/flyspeck.ml:5883`）。

目标：
`volume (Metric.ball v0 r ∩ affGt {v0} {v1,v2,v3})
   = ofReal ((dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 - π) * r^3 / 3)`
在 `0 < r`、`¬ Coplanar {v0,v1,v2,v3}` 下。

路线（与 HOL 略不同但等价，避免完整的 `AFF_GT_SHUFFLE` 六步分解）：
1. `MEASURABLE_BALL_AFF_GT`：凸集可测。
2. 特殊 `AFF_GT_SHUFFLE`（`s = {0}`）：
   `affGt {v,0} {w1,w2} = affGt {0}{v,w1,w2} ∪ affGt {0}{-v,w1,w2} ∪ affGt {0}{w1,w2}`。
3. `MEASURE_LUNE_DECOMPOSITION`：由 (2) + 中间项零测 + `volume_ball_affGt_simple`。
4. `SOLID_TRIANGLE_CONGRUENT_NEG`：整体取负的等距不变性。
5. 四条 lune 分解（三条绕轴 + 一条把第三个方向取负，
   `dihV 0 v1 v2 (-v3) = π - dihV 0 v1 v2 v3`）线性组合即得结论。
-/

import Kepler.Geom.LuneVolume
import Kepler.Geom.WedgeVolume
import Kepler.Geom.Aff
import Kepler.Geom.Azim
import Kepler.Geom.Coplanar

open Classical MeasureTheory
open Module
open scoped Topology Pointwise

noncomputable section

namespace Kepler.Geom

/-! ## 凸性与可测性（HOL `MEASURABLE_BALL_AFF_GT`，flyspeck.ml:5637） -/

/-- HOL `CONVEX_AFF_GT`：`affGt s t` 是凸集。 -/
private theorem convex_affGt (s t : Set V3) : Convex ℝ (affGt s t) := by
  rw [convex_iff_forall_pos]
  intro y hy z hz a b ha hb hab
  obtain ⟨f, hfin, hyeq, hfpos, hfsum⟩ := hy
  obtain ⟨g, hfin', hzeq, hgpos, hgsum⟩ := hz
  have hfs : hfin'.toFinset = hfin.toFinset := by
    rw [Subsingleton.elim hfin' hfin]
  rw [hfs] at hzeq hgsum
  refine ⟨fun w => a * f w + b * g w, hfin, ?_, ?_, ?_⟩
  · rw [hyeq, hzeq, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [smul_smul, smul_smul, ← add_smul]
  · intro w hw
    exact add_pos (mul_pos ha (hfpos w hw)) (mul_pos hb (hgpos w hw))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hfsum, hgsum, mul_one, mul_one, hab]

/-- HOL `MEASURABLE_BALL_AFF_GT`：球与 `affGt` 之交可测（凸集在有限维空间可测）。 -/
private theorem nullMeasurableSet_ball_inter_affGt (z : V3) (r : ℝ) (s t : Set V3) :
    NullMeasurableSet (Metric.ball z r ∩ affGt s t) volume :=
  ((convex_ball z r).inter (convex_affGt s t)).nullMeasurableSet volume

/-! ## 不共面 ⟹ 线性无关（HOL `NOT_COPLANAR_0_4_IMP_INDEPENDENT`） -/

/-- 由 `a • v1 + b • v2 + c • v3 = 0` 且 `a ≠ 0` 得 `v1 ∈ span{v2,v3}`。 -/
private theorem mem_span_pair_of_combo {v1 v2 v3 : V3} {a b c : ℝ}
    (h : a • v1 + b • v2 + c • v3 = 0) (ha : a ≠ 0) :
    v1 ∈ Submodule.span ℝ ({v2, v3} : Set V3) := by
  have h' : a • v1 = -(b • v2 + c • v3) := by
    rw [eq_neg_iff_add_eq_zero, ← h]; abel
  have h'' : v1 = a⁻¹ • (-(b • v2 + c • v3)) := by
    rw [← h', smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [h'']
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.neg_mem _ ?_
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- 不共面四点 `{0,v1,v2,v3}` 蕴含 `{v1,v2,v3}` 线性无关。 -/
private theorem linearIndependent_of_not_coplanar {v1 v2 v3 : V3}
    (hcop : ¬ Coplanar ({0, v1, v2, v3} : Set V3)) :
    LinearIndependent ℝ ![v1, v2, v3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra h
  simp only [not_forall] at h
  obtain ⟨i, hi⟩ := h
  have hg' : g 0 • v1 + g 1 • v2 + g 2 • v3 = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have hcop' : Coplanar ({0, v1, v2, v3} : Set V3) := by
    fin_cases i
    · have hv1 : v1 ∈ (affineSpan ℝ ({0, v2, v3} : Set V3) : Set V3) := by
        rw [affineSpan_insert_zero]
        exact mem_span_pair_of_combo hg' hi
      exact ⟨0, v2, v3, fun p hp => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact hv1
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)⟩
    · have hrel : g 1 • v2 + g 0 • v1 + g 2 • v3 = 0 := by rw [← hg']; abel
      have hv2 : v2 ∈ (affineSpan ℝ ({0, v1, v3} : Set V3) : Set V3) := by
        rw [affineSpan_insert_zero]
        exact mem_span_pair_of_combo hrel hi
      exact ⟨0, v1, v3, fun p hp => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
        · exact hv2
        · exact mem_affineSpan ℝ (by simp)⟩
    · have hrel : g 2 • v3 + g 0 • v1 + g 1 • v2 = 0 := by rw [← hg']; abel
      have hv3 : v3 ∈ (affineSpan ℝ ({0, v1, v2} : Set V3) : Set V3) := by
        rw [affineSpan_insert_zero]
        exact mem_span_pair_of_combo hrel hi
      exact ⟨0, v1, v2, fun p hp => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
        · exact hv3⟩
  exact hcop hcop'

/-- 线性无关时线性组合的系数唯一。 -/
private theorem coeff_unique {v1 v2 v3 : V3}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) {p q r p' q' r' : ℝ}
    (h : p • v1 + q • v2 + r • v3 = p' • v1 + q' • v2 + r' • v3) :
    p = p' ∧ q = q' ∧ r = r' := by
  have hzero : (p - p') • v1 + (q - q') • v2 + (r - r') • v3 = 0 := by
    have hsub : (p • v1 + q • v2 + r • v3) - (p' • v1 + q' • v2 + r' • v3) = 0 :=
      sub_eq_zero.mpr h
    have heq : (p - p') • v1 + (q - q') • v2 + (r - r') • v3 =
        (p • v1 + q • v2 + r • v3) - (p' • v1 + q' • v2 + r' • v3) := by
      module
    rw [heq]; exact hsub
  rw [Fintype.linearIndependent_iff] at hlin
  have hg := hlin ![p - p', q - q', r - r']
    (by simpa [Fin.sum_univ_three] using hzero)
  have h0 : p - p' = 0 := by simpa using hg 0
  have h1 : q - q' = 0 := by simpa using hg 1
  have h2 : r - r' = 0 := by simpa using hg 2
  exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-! ## `affGt` 在源含 `0` 时的显式刻画

HOL 用 `AFFINE_HULL_FINITE_STEP_GEN` 消去 `0` 的系数；此处直接对
`{0} ∪ t` 的有限和展开，得到「`0` 的系数自由、`t` 上严格正」的刻画。 -/

private lemma sum4_s (f : V3 → ℝ) {a b c d : V3}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ z ∈ ({a, b, c, d} : Finset V3), f z = f a + f b + f c + f d := by
  have h1 : a ∉ ({b, c, d} : Finset V3) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Finset V3) := by simp [hbc, hbd]
  have h3 : c ∉ ({d} : Finset V3) := by simp [hcd]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  ring

private lemma sum4_v (f : V3 → ℝ) {a b c d : V3}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ z ∈ ({a, b, c, d} : Finset V3), f z • z = f a • a + f b • b + f c • c + f d • d := by
  have h1 : a ∉ ({b, c, d} : Finset V3) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Finset V3) := by simp [hbc, hbd]
  have h3 : c ∉ ({d} : Finset V3) := by simp [hcd]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  abel

private lemma sum3_s (f : V3 → ℝ) {a b c : V3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ z ∈ ({a, b, c} : Finset V3), f z = f a + f b + f c := by
  have h1 : a ∉ ({b, c} : Finset V3) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset V3) := by simp [hbc]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  ring

private lemma sum3_v (f : V3 → ℝ) {a b c : V3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ z ∈ ({a, b, c} : Finset V3), f z • z = f a • a + f b • b + f c • c := by
  have h1 : a ∉ ({b, c} : Finset V3) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset V3) := by simp [hbc]
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  abel

private lemma toFinset_zero_union_triple {a b c : V3}
    (h : ({0} ∪ ({a, b, c} : Set V3)).Finite) :
    h.toFinset = ({0, a, b, c} : Finset V3) := by
  apply Finset.ext
  intro z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] <;> tauto

private lemma toFinset_pair_zero_union_pair {v w1 w2 : V3}
    (h : ({v, 0} ∪ ({w1, w2} : Set V3)).Finite) :
    h.toFinset = ({v, 0, w1, w2} : Finset V3) := by
  apply Finset.ext
  intro z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] <;> tauto

private lemma toFinset_zero_union_pair {w1 w2 : V3}
    (h : ({0} ∪ ({w1, w2} : Set V3)).Finite) :
    h.toFinset = ({0, w1, w2} : Finset V3) := by
  apply Finset.ext
  intro z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] <;> tauto

/-- `affGt {0} {a,b,c}` 的刻画（四点互异）：`0` 系数自由，其余严格正。 -/
private theorem mem_affGt_zero_triple {a b c y : V3}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    y ∈ affGt ({0} : Set V3) {a, b, c} ↔
      ∃ p q r : ℝ, 0 < p ∧ 0 < q ∧ 0 < r ∧ y = p • a + q • b + r • c := by
  constructor
  · rintro ⟨f, hfin, hyeq, hfpos, hone⟩
    rw [toFinset_zero_union_triple hfin,
      sum4_v f (Ne.symm ha0) (Ne.symm hb0) (Ne.symm hc0) hab hac hbc] at hyeq
    refine ⟨f a, f b, f c, hfpos a (by simp), hfpos b (by simp), hfpos c (by simp), ?_⟩
    rw [hyeq]; simp
  · rintro ⟨p, q, r, hp, hq, hr, rfl⟩
    have hfin : ({0} ∪ ({a, b, c} : Set V3)).Finite :=
      (Set.finite_singleton (0 : V3)).union (((Set.finite_singleton c).insert b).insert a)
    refine ⟨fun z => if z = a then p else if z = b then q else if z = c then r
      else 1 - p - q - r, hfin, ?_, ?_, ?_⟩
    · rw [toFinset_zero_union_triple hfin,
        sum4_v _ (Ne.symm ha0) (Ne.symm hb0) (Ne.symm hc0) hab hac hbc]
      simp only [if_neg (Ne.symm ha0), if_neg (Ne.symm hb0), if_neg (Ne.symm hc0),
        if_neg (Ne.symm hab), if_neg (Ne.symm hac), if_neg (Ne.symm hbc),
        if_true, if_false, smul_zero]
      abel
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simpa using hp
      · simp only [if_neg (Ne.symm hab), if_pos rfl]; exact hq
      · simp only [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos rfl]; exact hr
    · rw [toFinset_zero_union_triple hfin,
        sum4_s _ (Ne.symm ha0) (Ne.symm hb0) (Ne.symm hc0) hab hac hbc]
      simp only [if_neg (Ne.symm ha0), if_neg (Ne.symm hb0), if_neg (Ne.symm hc0),
        if_neg (Ne.symm hab), if_neg (Ne.symm hac), if_neg (Ne.symm hbc),
        if_true, if_false]
      ring

/-- `affGt {v,0} {w1,w2}` 的刻画（四点互异）：`v` 系数自由，`w1,w2` 严格正。 -/
private theorem mem_affGt_pair_zero_pair {v w1 w2 y : V3}
    (hv0 : v ≠ 0) (hw10 : w1 ≠ 0) (hw20 : w2 ≠ 0)
    (hvw1 : v ≠ w1) (hvw2 : v ≠ w2) (hw12 : w1 ≠ w2) :
    y ∈ affGt ({v, 0} : Set V3) {w1, w2} ↔
      ∃ p q r : ℝ, 0 < q ∧ 0 < r ∧ y = p • v + q • w1 + r • w2 := by
  constructor
  · rintro ⟨f, hfin, hyeq, hfpos, hone⟩
    rw [toFinset_pair_zero_union_pair hfin,
      sum4_v f hv0 hvw1 hvw2 (Ne.symm hw10) (Ne.symm hw20) hw12] at hyeq
    refine ⟨f v, f w1, f w2, hfpos w1 (by simp), hfpos w2 (by simp), ?_⟩
    rw [hyeq]; simp
  · rintro ⟨p, q, r, hq, hr, rfl⟩
    have hfin : ({v, 0} ∪ ({w1, w2} : Set V3)).Finite :=
      ((Set.finite_singleton (0 : V3)).insert v).union
        ((Set.finite_singleton w2).insert w1)
    refine ⟨fun z => if z = v then p else if z = w1 then q else if z = w2 then r
      else 1 - p - q - r, hfin, ?_, ?_, ?_⟩
    · rw [toFinset_pair_zero_union_pair hfin,
        sum4_v _ hv0 hvw1 hvw2 (Ne.symm hw10) (Ne.symm hw20) hw12]
      simp only [if_neg (Ne.symm hvw1), if_neg (Ne.symm hvw2),
        if_neg (Ne.symm hw10), if_neg (Ne.symm hw20), if_neg (Ne.symm hw12),
        if_true, if_false, smul_zero]
      abel
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simp only [if_neg (Ne.symm hvw1), if_pos rfl]; exact hq
      · simp only [if_neg (Ne.symm hvw2), if_neg (Ne.symm hw12), if_true, if_false]
        exact hr
    · rw [toFinset_pair_zero_union_pair hfin,
        sum4_s _ hv0 hvw1 hvw2 (Ne.symm hw10) (Ne.symm hw20) hw12]
      simp only [if_neg (Ne.symm hv0), if_neg (Ne.symm hvw1), if_neg (Ne.symm hvw2),
        if_neg (Ne.symm hw10), if_neg (Ne.symm hw20), if_neg (Ne.symm hw12),
        if_true, if_false]
      ring

/-- `affGt {0} {w1,w2}` 的刻画（三点互异）：`0` 系数自由，`w1,w2` 严格正。 -/
private theorem mem_affGt_zero_pair {w1 w2 y : V3}
    (hw10 : w1 ≠ 0) (hw20 : w2 ≠ 0) (hw12 : w1 ≠ w2) :
    y ∈ affGt ({0} : Set V3) {w1, w2} ↔
      ∃ q r : ℝ, 0 < q ∧ 0 < r ∧ y = q • w1 + r • w2 := by
  constructor
  · rintro ⟨f, hfin, hyeq, hfpos, hone⟩
    rw [toFinset_zero_union_pair hfin,
      sum3_v f (Ne.symm hw10) (Ne.symm hw20) hw12] at hyeq
    refine ⟨f w1, f w2, hfpos w1 (by simp), hfpos w2 (by simp), ?_⟩
    rw [hyeq]; simp
  · rintro ⟨q, r, hq, hr, rfl⟩
    have hfin : ({0} ∪ ({w1, w2} : Set V3)).Finite :=
      (Set.finite_singleton (0 : V3)).union ((Set.finite_singleton w2).insert w1)
    refine ⟨fun z => if z = w1 then q else if z = w2 then r else 1 - q - r,
      hfin, ?_, ?_, ?_⟩
    · rw [toFinset_zero_union_pair hfin,
        sum3_v _ (Ne.symm hw10) (Ne.symm hw20) hw12]
      simp only [if_neg (Ne.symm hw12), if_neg (Ne.symm hw10),
        if_neg (Ne.symm hw20), if_true, if_false, smul_zero]
      abel
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simp only [if_pos rfl]; exact hq
      · simp only [if_neg (Ne.symm hw12), if_true, if_false]
        exact hr
    · rw [toFinset_zero_union_pair hfin,
        sum3_s _ (Ne.symm hw10) (Ne.symm hw20) hw12]
      simp only [if_neg (Ne.symm hw12), if_neg (Ne.symm hw10),
        if_neg (Ne.symm hw20), if_true, if_false]
      ring

/-! ## 特殊 `AFF_GT_SHUFFLE`（`s = {0}`） -/

/-- `AFF_GT_SHUFFLE` 在 `s = {0}` 时的特例：
`affGt {v,0} {w1,w2} = affGt {0}{v,w1,w2} ∪ affGt {0}{-v,w1,w2} ∪ affGt {0}{w1,w2}`。
证明：由三个显式刻画，按 `v` 的系数符号分类。 -/
private theorem affGt_insert_zero_shuffle {v w1 w2 : V3}
    (hv0 : v ≠ 0) (hw10 : w1 ≠ 0) (hw20 : w2 ≠ 0)
    (hvw1 : v ≠ w1) (hvw2 : v ≠ w2) (hw12 : w1 ≠ w2)
    (hnvw1 : -v ≠ w1) (hnvw2 : -v ≠ w2) :
    affGt ({v, 0} : Set V3) {w1, w2} =
      affGt ({0} : Set V3) {v, w1, w2} ∪
      affGt ({0} : Set V3) {-v, w1, w2} ∪
      affGt ({0} : Set V3) {w1, w2} := by
  have hnv0 : -v ≠ 0 := neg_ne_zero.mpr hv0
  ext y
  rw [Set.mem_union, Set.mem_union, or_assoc,
    mem_affGt_pair_zero_pair hv0 hw10 hw20 hvw1 hvw2 hw12,
    mem_affGt_zero_triple hv0 hw10 hw20 hvw1 hvw2 hw12,
    mem_affGt_zero_triple hnv0 hw10 hw20 hnvw1 hnvw2 hw12,
    mem_affGt_zero_pair hw10 hw20 hw12]
  constructor
  · rintro ⟨p, q, r, hq, hr, rfl⟩
    rcases lt_trichotomy p 0 with hp | hp | hp
    · right; left
      exact ⟨-p, q, r, by linarith, hq, hr, by module⟩
    · right; right
      exact ⟨q, r, hq, hr, by rw [hp, zero_smul, zero_add]⟩
    · left
      exact ⟨p, q, r, hp, hq, hr, rfl⟩
  · rintro (⟨p, q, r, hp, hq, hr, rfl⟩ | ⟨p, q, r, hp, hq, hr, h⟩ |
      ⟨q, r, hq, hr, rfl⟩)
    · exact ⟨p, q, r, hq, hr, rfl⟩
    · exact ⟨-p, q, r, hq, hr, by rw [h]; module⟩
    · exact ⟨0, q, r, hq, hr, by rw [zero_smul, zero_add]⟩

/-! ## 中间项（二维锥）零测 -/

private theorem finrank_span_pair_le_two (a b : V3) :
    finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h
  have h2 : ({a, b} : Finset V3).card ≤ 2 := by
    calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
      _ = 2 := by simp
  omega

private theorem span_pair_ne_top (a b : V3) :
    Submodule.span ℝ ({a, b} : Set V3) ≠ ⊤ := by
  intro h
  have hle := finrank_span_pair_le_two a b
  rw [h, finrank_top] at hle
  have h3 : finrank ℝ V3 = 3 := by
    simp [V3, finrank_euclideanSpace_fin]
  omega

/-- `affGt {0} {w1,w2}` 含于二维子空间 `span{w1,w2}`。 -/
private theorem affGt_zero_pair_subset_span (w1 w2 : V3) :
    affGt ({0} : Set V3) {w1, w2} ⊆
      (Submodule.span ℝ ({w1, w2} : Set V3) : Set V3) := by
  intro y hy
  obtain ⟨f, hfin, hyeq, hfpos, hone⟩ := hy
  rw [hyeq]
  refine Submodule.sum_mem _ fun w hw => ?_
  have hw' : w ∈ ({0} ∪ ({w1, w2} : Set V3) : Set V3) := by simpa using hw
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
  rcases hw' with rfl | rfl | rfl
  · rw [smul_zero]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- `affGt {0} {w1,w2}` 零测（含于一个真子空间）。 -/
private theorem volume_affGt_zero_pair (w1 w2 : V3) :
    volume (affGt ({0} : Set V3) {w1, w2}) = 0 :=
  measure_mono_null (affGt_zero_pair_subset_span w1 w2)
    (MeasureTheory.Measure.addHaar_submodule volume _ (span_pair_ne_top w1 w2))

/-! ## 四点不共面的互异性 -/

private theorem not_coplanar_distinct {v1 v2 v3 : V3}
    (hcop : ¬ Coplanar ({0, v1, v2, v3} : Set V3)) :
    v1 ≠ 0 ∧ v2 ≠ 0 ∧ v3 ≠ 0 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 := by
  have hsub : ∀ {x y z : V3}, ({0, v1, v2, v3} : Set V3) ⊆ ({x, y, z} : Set V3) →
      Coplanar ({0, v1, v2, v3} : Set V3) :=
    fun {x y z} h => (coplanar_triple x y z).subset h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hcop (hsub (x := 0) (y := v2) (z := v3) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v1) (z := v3) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v1) (z := v2) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v1) (z := v3) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v1) (z := v2) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v1) (z := v2) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))

/-- `¬ Coplanar {0,v1,v2,v3}` 蕴含 `-v1 ∉ {0,v2,v3}`。 -/
private theorem neg_not_mem_of_not_coplanar {v1 v2 v3 : V3}
    (hcop : ¬ Coplanar ({0, v1, v2, v3} : Set V3)) :
    -v1 ≠ 0 ∧ -v1 ≠ v2 ∧ -v1 ≠ v3 := by
  obtain ⟨hv10, hv20, hv30, hv12, hv13, hv23⟩ := not_coplanar_distinct hcop
  have hlin := linearIndependent_of_not_coplanar hcop
  rw [Fintype.linearIndependent_iff] at hlin
  refine ⟨neg_ne_zero.mpr hv10, ?_, ?_⟩
  · intro h
    have hrel : (1 : ℝ) • v1 + (1 : ℝ) • v2 + (0 : ℝ) • v3 = 0 := by
      simp only [one_smul, zero_smul, add_zero]
      exact neg_eq_iff_add_eq_zero.mp h
    have h0 := hlin ![1, 1, 0] (by simpa [Fin.sum_univ_three] using hrel) 0
    norm_num at h0
  · intro h
    have hrel : (1 : ℝ) • v1 + (0 : ℝ) • v2 + (1 : ℝ) • v3 = 0 := by
      simp only [one_smul, zero_smul, add_zero, zero_add]
      exact neg_eq_iff_add_eq_zero.mp h
    have h0 := hlin ![1, 0, 1] (by simpa [Fin.sum_univ_three] using hrel) 0
    norm_num at h0

/-! ## 三个八分体的两两不交 -/

private theorem disjoint_octants_aux {v1 v2 v3 : V3}
    (hlin : LinearIndependent ℝ ![v1, v2, v3])
    (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hn1 : -v1 ≠ 0) (hn12 : -v1 ≠ v2) (hn13 : -v1 ≠ v3) :
    Disjoint (affGt ({0} : Set V3) {v1, v2, v3})
      (affGt ({0} : Set V3) {-v1, v2, v3}) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [mem_affGt_zero_triple h1 h2 h3 h12 h13 h23] at hy1
  rw [mem_affGt_zero_triple hn1 h2 h3 hn12 hn13 h23] at hy2
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hy1
  obtain ⟨p', q', r', hp', hq', hr', hy2⟩ := hy2
  have h' : p • v1 + q • v2 + r • v3 = (-p') • v1 + q' • v2 + r' • v3 := by
    rw [hy2]; module
  obtain ⟨hpp, -, -⟩ := coeff_unique hlin h'
  linarith

private theorem disjoint_octant_zero {v1 v2 v3 : V3}
    (hlin : LinearIndependent ℝ ![v1, v2, v3])
    (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    Disjoint (affGt ({0} : Set V3) {v1, v2, v3})
      (affGt ({0} : Set V3) {v2, v3}) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [mem_affGt_zero_triple h1 h2 h3 h12 h13 h23] at hy1
  rw [mem_affGt_zero_pair h2 h3 h23] at hy2
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hy1
  obtain ⟨q', r', hq', hr', hy2⟩ := hy2
  have h' : p • v1 + q • v2 + r • v3 = (0 : ℝ) • v1 + q' • v2 + r' • v3 := by
    rw [hy2]; simp
  obtain ⟨hpp, -, -⟩ := coeff_unique hlin h'
  linarith

private theorem disjoint_octant_zero_neg {v1 v2 v3 : V3}
    (hlin : LinearIndependent ℝ ![v1, v2, v3])
    (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hn1 : -v1 ≠ 0) (hn12 : -v1 ≠ v2) (hn13 : -v1 ≠ v3) :
    Disjoint (affGt ({0} : Set V3) {-v1, v2, v3})
      (affGt ({0} : Set V3) {v2, v3}) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [mem_affGt_zero_triple hn1 h2 h3 hn12 hn13 h23] at hy1
  rw [mem_affGt_zero_pair h2 h3 h23] at hy2
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hy1
  obtain ⟨q', r', hq', hr', hy2⟩ := hy2
  have h' : p • (-v1) + q • v2 + r • v3 = (0 : ℝ) • v1 + q' • v2 + r' • v3 := by
    rw [hy2]; simp
  have h'' : (-p) • v1 + q • v2 + r • v3 = (0 : ℝ) • v1 + q' • v2 + r' • v3 := by
    rw [← h']; module
  obtain ⟨hpp, -, -⟩ := coeff_unique hlin h''
  linarith

/-! ## `MEASURE_LUNE_DECOMPOSITION`（flyspeck.ml:5833） -/

private theorem measure_lune_decomposition {v1 v2 v3 : V3} {r : ℝ}
    (hr : 0 ≤ r) (hcop : ¬ Coplanar ({0, v1, v2, v3} : Set V3)) :
    volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3}) +
      volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, v3}) =
      ENNReal.ofReal (dihV 0 v1 v2 v3 * 2 * r ^ 3 / 3) := by
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := not_coplanar_distinct hcop
  obtain ⟨hn1, hn12, hn13⟩ := neg_not_mem_of_not_coplanar hcop
  have hlin := linearIndependent_of_not_coplanar hcop
  have hshuffle : affGt ({v1, 0} : Set V3) {v2, v3} =
      affGt ({0} : Set V3) {v1, v2, v3} ∪
      affGt ({0} : Set V3) {-v1, v2, v3} ∪
      affGt ({0} : Set V3) {v2, v3} :=
    affGt_insert_zero_shuffle h1 h2 h3 h12 h13 h23 hn12 hn13
  have hwedge : volume (Metric.ball 0 r ∩ affGt ({v1, 0} : Set V3) {v2, v3}) =
      ENNReal.ofReal (dihV 0 v1 v2 v3 * 2 * r ^ 3 / 3) := by
    have h := volume_ball_affGt_simple (z := 0) (w := v1) (w1 := v2) (w2 := v3) hr hcop
    rwa [show ({0, v1} : Set V3) = {v1, 0} from Set.pair_comm 0 v1] at h
  have hdis12 := disjoint_octants_aux hlin h1 h2 h3 h12 h13 h23 hn1 hn12 hn13
  have hdis1N := disjoint_octant_zero hlin h1 h2 h3 h12 h13 h23
  have hdis2N := disjoint_octant_zero_neg hlin h1 h2 h3 h12 h13 h23 hn1 hn12 hn13
  have hNnull : volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v2, v3}) = 0 :=
    measure_mono_null Set.inter_subset_right (volume_affGt_zero_pair v2 v3)
  have hmeas1 : NullMeasurableSet
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3}) volume :=
    nullMeasurableSet_ball_inter_affGt 0 r _ _
  have hmeas2 : NullMeasurableSet
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, v3}) volume :=
    nullMeasurableSet_ball_inter_affGt 0 r _ _
  have hmeasN : NullMeasurableSet
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v2, v3}) volume :=
    nullMeasurableSet_ball_inter_affGt 0 r _ _
  have haedis12 : AEDisjoint volume
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3})
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, v3}) :=
    (hdis12.mono Set.inter_subset_right Set.inter_subset_right).aedisjoint
  have haedis1N : AEDisjoint volume
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3})
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v2, v3}) :=
    (hdis1N.mono Set.inter_subset_right Set.inter_subset_right).aedisjoint
  have haedis2N : AEDisjoint volume
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, v3})
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v2, v3}) :=
    (hdis2N.mono Set.inter_subset_right Set.inter_subset_right).aedisjoint
  have hset : Metric.ball 0 r ∩ affGt ({v1, 0} : Set V3) {v2, v3} =
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3}) ∪
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, v3}) ∪
      (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v2, v3}) := by
    rw [hshuffle]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  have hcalc : volume (Metric.ball 0 r ∩ affGt ({v1, 0} : Set V3) {v2, v3}) =
      volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3}) +
      volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, v3}) := by
    rw [hset]
    rw [measure_union₀ hmeasN (AEDisjoint.union_left haedis1N haedis2N)]
    rw [hNnull, add_zero]
    rw [measure_union₀ hmeas2 haedis12]
  rw [← hcalc, hwedge]

/-! ## 取负等距（HOL `SOLID_TRIANGLE_CONGRUENT_NEG`，flyspeck.ml:5855） -/

private theorem volume_image_neg (S : Set V3) :
    volume ((fun x : V3 => -x) '' S) = volume S := by
  have h : (fun x : V3 => -x) '' S = (-1 : ℝ) • S := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp⟩
  rw [h]
  simpa using (Measure.addHaar_smul volume (-1 : ℝ) S)

/-- `volume (ball 0 r ∩ affGt {0}{-a,-b,-c}) = volume (ball 0 r ∩ affGt {0}{a,b,c})`。 -/
private theorem volume_ball_affGt_neg {a b c : V3} {r : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-a, -b, -c}) =
      volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {a, b, c}) := by
  have hna0 : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hnb0 : -b ≠ 0 := neg_ne_zero.mpr hb0
  have hnc0 : -c ≠ 0 := neg_ne_zero.mpr hc0
  have hnab : -a ≠ -b := fun h => hab (neg_inj.mp h)
  have hnac : -a ≠ -c := fun h => hac (neg_inj.mp h)
  have hnbc : -b ≠ -c := fun h => hbc (neg_inj.mp h)
  have hset : Metric.ball 0 r ∩ affGt ({0} : Set V3) {-a, -b, -c} =
      (fun x : V3 => -x) '' (Metric.ball 0 r ∩ affGt ({0} : Set V3) {a, b, c}) := by
    ext y
    constructor
    · rintro ⟨hyball, hyO⟩
      rw [mem_affGt_zero_triple hna0 hnb0 hnc0 hnab hnac hnbc] at hyO
      obtain ⟨p, q, s, hp, hq, hs, hyO⟩ := hyO
      refine ⟨-y, ⟨?_, ?_⟩, by simp⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hyball ⊢
        simpa using hyball
      · rw [mem_affGt_zero_triple ha0 hb0 hc0 hab hac hbc]
        refine ⟨p, q, s, hp, hq, hs, ?_⟩
        rw [hyO]; module
    · rintro ⟨x, ⟨hxball, hxO⟩, rfl⟩
      rw [mem_affGt_zero_triple ha0 hb0 hc0 hab hac hbc] at hxO
      obtain ⟨p, q, s, hp, hq, hs, hxO⟩ := hxO
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hxball ⊢
        simpa using hxball
      · rw [mem_affGt_zero_triple hna0 hnb0 hnc0 hnab hnac hnbc]
        refine ⟨p, q, s, hp, hq, hs, ?_⟩
        rw [hxO]; module
  rw [hset, volume_image_neg]

/-! ## `dihV 0 v1 v2 (-v3) = π - dihV 0 v1 v2 v3` -/

private theorem arcV_zero_neg (u w : V3) :
    arcV 0 u (-w) = Real.pi - arcV 0 u w := by
  have h1 : arcV 0 u w = Real.arccos (u ⬝ᵥ w / (‖u‖ * ‖w‖)) := by
    simp only [arcV, dist_zero_right]
    congr 1
    simp
  have h2 : arcV 0 u (-w) = Real.arccos (-(u ⬝ᵥ w / (‖u‖ * ‖w‖))) := by
    simp only [arcV, dist_zero_right, norm_neg]
    congr 1
    simp only [WithLp.ofLp_zero, sub_zero, WithLp.ofLp_neg, dotProduct_neg]
    ring
  rw [h1, h2, Real.arccos_neg]

private theorem dihV_zero_neg_right (v1 v2 v3 : V3) :
    dihV 0 v1 v2 (-v3) = Real.pi - dihV 0 v1 v2 v3 := by
  have hb : ((v1 ⬝ᵥ v1) • (-v3) - ((-v3) ⬝ᵥ v1) • v1)
      = -((v1 ⬝ᵥ v1) • v3 - (v3 ⬝ᵥ v1) • v1) := by
    rw [WithLp.ofLp_neg, neg_dotProduct]
    module
  simp only [dihV, sub_zero]
  rw [hb]
  exact arcV_zero_neg _ _

/-! ## 取负不改变共面性 -/

private theorem not_coplanar_neg_right {v1 v2 v3 : V3}
    (hcop : ¬ Coplanar ({0, v1, v2, v3} : Set V3)) :
    ¬ Coplanar ({0, v1, v2, -v3} : Set V3) := by
  intro h
  apply hcop
  obtain ⟨u, w, x, hsub⟩ := h
  refine ⟨u, w, x, fun p hp => ?_⟩
  have h0 : (0 : V3) ∈ (affineSpan ℝ ({u, w, x} : Set V3) : Set V3) := hsub (by simp)
  have hneg3 : -v3 ∈ (affineSpan ℝ ({u, w, x} : Set V3) : Set V3) := hsub (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | h4
  · exact h0
  · exact hsub (by simp)
  · exact hsub (by simp)
  · rw [h4]
    have hdir : v3 -ᵥ (0 : V3) ∈ (affineSpan ℝ ({u, w, x} : Set V3)).direction := by
      have h1 : (-v3) -ᵥ (0 : V3) ∈ (affineSpan ℝ ({u, w, x} : Set V3)).direction :=
        AffineSubspace.vsub_mem_direction hneg3 h0
      have h2 := Submodule.neg_mem _ h1
      simpa using h2
    have := AffineSubspace.vadd_mem_of_mem_direction hdir h0
    simpa using this

/-! ## `dihV` 的非负性 -/

private theorem dihV_nonneg (a b c d : V3) : 0 ≤ dihV a b c d := by
  unfold dihV
  exact Real.arccos_nonneg _

/-! ## 一般顶点 `v0` 的平移归约 -/

private lemma toFinset_single_union_triple {v0 v1 v2 v3 : V3}
    (h : ({v0} ∪ ({v1, v2, v3} : Set V3)).Finite) :
    h.toFinset = ({v0, v1, v2, v3} : Finset V3) := by
  apply Finset.ext
  intro z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] <;> tauto

/-- `affGt {v0} {v1,v2,v3}` 的显式刻画（以 `v0` 为基点，四点互异）。 -/
private theorem mem_affGt_base_triple {v0 v1 v2 v3 y : V3}
    (h10 : v1 ≠ v0) (h20 : v2 ≠ v0) (h30 : v3 ≠ v0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    y ∈ affGt ({v0} : Set V3) {v1, v2, v3} ↔
      ∃ p q r : ℝ, 0 < p ∧ 0 < q ∧ 0 < r ∧
        y - v0 = p • (v1 - v0) + q • (v2 - v0) + r • (v3 - v0) := by
  constructor
  · rintro ⟨f, hfin, hyeq, hfpos, hone⟩
    rw [toFinset_single_union_triple hfin,
      sum4_v f (Ne.symm h10) (Ne.symm h20) (Ne.symm h30) h12 h13 h23] at hyeq
    rw [toFinset_single_union_triple hfin,
      sum4_s f (Ne.symm h10) (Ne.symm h20) (Ne.symm h30) h12 h13 h23] at hone
    refine ⟨f v1, f v2, f v3, hfpos v1 (by simp), hfpos v2 (by simp),
      hfpos v3 (by simp), ?_⟩
    have hf0 : f v0 = 1 - f v1 - f v2 - f v3 := by linarith
    rw [hyeq, hf0]
    module
  · rintro ⟨p, q, r, hp, hq, hr, hy⟩
    have hfin : ({v0} ∪ ({v1, v2, v3} : Set V3)).Finite :=
      (Set.finite_singleton v0).union (((Set.finite_singleton v3).insert v2).insert v1)
    refine ⟨fun z => if z = v0 then 1 - p - q - r else if z = v1 then p
      else if z = v2 then q else r, hfin, ?_, ?_, ?_⟩
    · rw [toFinset_single_union_triple hfin,
        sum4_v _ (Ne.symm h10) (Ne.symm h20) (Ne.symm h30) h12 h13 h23]
      simp only [if_pos rfl, if_neg h10, if_neg h20, if_neg h30,
        if_neg (Ne.symm h12), if_neg (Ne.symm h13), if_neg (Ne.symm h23),
        if_true, if_false]
      have hy' : y = v0 + (p • (v1 - v0) + q • (v2 - v0) + r • (v3 - v0)) := by
        rw [← hy]; abel
      rw [hy']; module
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simp only [if_neg h10, if_pos rfl]; exact hp
      · simp only [if_neg h20, if_neg (Ne.symm h12), if_pos rfl]; exact hq
      · simp only [if_neg h30, if_neg (Ne.symm h13), if_neg (Ne.symm h23),
          if_pos rfl]; exact hr
    · rw [toFinset_single_union_triple hfin,
        sum4_s _ (Ne.symm h10) (Ne.symm h20) (Ne.symm h30) h12 h13 h23]
      simp only [if_pos rfl, if_neg h10, if_neg h20, if_neg h30,
        if_neg (Ne.symm h12), if_neg (Ne.symm h13), if_neg (Ne.symm h23),
        if_true, if_false]
      ring

/-- 平移 `v0` 把 `affGt {v0}{v1,v2,v3}` 化为原点处的 `affGt`。 -/
private theorem affGt_translate {v0 v1 v2 v3 : V3}
    (h10 : v1 ≠ v0) (h20 : v2 ≠ v0) (h30 : v3 ≠ v0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    affGt ({v0} : Set V3) {v1, v2, v3} =
      (fun y : V3 => v0 + y) '' affGt ({0} : Set V3) {v1 - v0, v2 - v0, v3 - v0} := by
  have h10' : v1 - v0 ≠ 0 := sub_ne_zero.mpr h10
  have h20' : v2 - v0 ≠ 0 := sub_ne_zero.mpr h20
  have h30' : v3 - v0 ≠ 0 := sub_ne_zero.mpr h30
  have h12' : v1 - v0 ≠ v2 - v0 := by
    intro hh; apply h12
    have := congrArg (fun x : V3 => x + v0) hh; simpa using this
  have h13' : v1 - v0 ≠ v3 - v0 := by
    intro hh; apply h13
    have := congrArg (fun x : V3 => x + v0) hh; simpa using this
  have h23' : v2 - v0 ≠ v3 - v0 := by
    intro hh; apply h23
    have := congrArg (fun x : V3 => x + v0) hh; simpa using this
  ext y
  constructor
  · intro hy
    rw [mem_affGt_base_triple h10 h20 h30 h12 h13 h23] at hy
    obtain ⟨p, q, r, hp, hq, hr, hy⟩ := hy
    exact ⟨y - v0, by
      rw [mem_affGt_zero_triple h10' h20' h30' h12' h13' h23']
      exact ⟨p, q, r, hp, hq, hr, hy⟩, by abel⟩
  · rintro ⟨z, hz, rfl⟩
    rw [mem_affGt_zero_triple h10' h20' h30' h12' h13' h23'] at hz
    obtain ⟨p, q, r, hp, hq, hr, hz⟩ := hz
    rw [mem_affGt_base_triple h10 h20 h30 h12 h13 h23]
    exact ⟨p, q, r, hp, hq, hr, by rw [hz]; module⟩

/-- `dihV` 平移不变。 -/
private theorem dihV_sub_self (v0 v1 v2 v3 : V3) :
    dihV v0 v1 v2 v3 = dihV 0 (v1 - v0) (v2 - v0) (v3 - v0) := by
  unfold dihV
  simp only [sub_zero]

/-- 平移保持共面性。 -/
private theorem coplanar_translate (v0 : V3) {s : Set V3} (h : Coplanar s) :
    Coplanar ((fun y : V3 => v0 + y) '' s) := by
  obtain ⟨u, w, x, hsub⟩ := h
  refine ⟨v0 + u, v0 + w, v0 + x, ?_⟩
  rintro p ⟨q, hq, rfl⟩
  have hq' : q ∈ (affineSpan ℝ ({u, w, x} : Set V3) : Set V3) := hsub hq
  have hspan := AffineSubspace.map_span
    (f := (AffineEquiv.constVAdd ℝ V3 v0).toAffineMap) ({u, w, x} : Set V3)
  have himg : ((AffineEquiv.constVAdd ℝ V3 v0).toAffineMap : V3 → V3) '' ({u, w, x} : Set V3) =
      ({v0 + u, v0 + w, v0 + x} : Set V3) := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add, eq_comm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl | rfl <;> simp
    · intro hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨u, by simp, rfl⟩
      · exact ⟨w, by simp, rfl⟩
      · exact ⟨x, by simp, rfl⟩
  rw [himg] at hspan
  have hmem : (v0 + q) ∈ (affineSpan ℝ ({u, w, x} : Set V3)).map
      (AffineEquiv.constVAdd ℝ V3 v0).toAffineMap :=
    ⟨q, hq', by simp [AffineEquiv.constVAdd_apply, vadd_eq_add]⟩
  rw [hspan] at hmem
  exact hmem

/-! ## `v0 = 0` 版本的 `VOLUME_SOLID_TRIANGLE` -/

private theorem volume_solid_triangle_zero {v1 v2 v3 : V3} {r : ℝ}
    (hr : 0 < r) (hcop : ¬ Coplanar ({0, v1, v2, v3} : Set V3)) :
    volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3}) =
      ENNReal.ofReal ((dihV 0 v1 v2 v3 + dihV 0 v2 v3 v1 + dihV 0 v3 v1 v2 - Real.pi)
        * r ^ 3 / 3) := by
  have hrle : 0 ≤ r := le_of_lt hr
  have hcop231 : ¬ Coplanar ({0, v2, v3, v1} : Set V3) := by
    rwa [show ({0, v2, v3, v1} : Set V3) = {0, v1, v2, v3} from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hcop312 : ¬ Coplanar ({0, v3, v1, v2} : Set V3) := by
    rwa [show ({0, v3, v1, v2} : Set V3) = {0, v1, v2, v3} from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hcop12n3 : ¬ Coplanar ({0, v1, v2, -v3} : Set V3) := not_coplanar_neg_right hcop
  obtain ⟨hv10, hv20, hv30, hv12, hv13, hv23⟩ := not_coplanar_distinct hcop
  obtain ⟨hn1, hn12, hn13⟩ := neg_not_mem_of_not_coplanar hcop
  obtain ⟨-, hn2_3, -⟩ := neg_not_mem_of_not_coplanar hcop231
  have hl2 := measure_lune_decomposition (v1 := v2) (v2 := v3) (v3 := v1) hrle hcop231
  have hl3 := measure_lune_decomposition (v1 := v3) (v2 := v1) (v3 := v2) hrle hcop312
  have hl4 := measure_lune_decomposition (v1 := v1) (v2 := v2) (v3 := -v3) hrle hcop12n3
  rw [show ({v2, v3, v1} : Set V3) = {v1, v2, v3} from by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto,
      show ({-v2, v3, v1} : Set V3) = {v1, -v2, v3} from by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hl2
  rw [show ({v3, v1, v2} : Set V3) = {v1, v2, v3} from by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto,
      show ({-v3, v1, v2} : Set V3) = {v1, v2, -v3} from by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hl3
  have hneg : volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, -(-v2), -v3}) =
      volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, -v2, v3}) :=
    volume_ball_affGt_neg (a := v1) (b := -v2) (c := v3) (r := r) hv10
      (neg_ne_zero.mpr hv20) hv30 (fun hh => hn12 (by rw [hh]; simp)) hv13 hn2_3
  simp only [neg_neg] at hneg
  have hball_ne : volume (Metric.ball (0 : V3) r) ≠ ⊤ := by
    rw [EuclideanSpace.volume_ball_fin_three (0 : V3) r]
    finiteness
  have hfin : ∀ S : Set V3, volume (Metric.ball 0 r ∩ S) ≠ ⊤ :=
    fun S => ne_top_of_le_ne_top hball_ne (measure_mono (μ := volume) Set.inter_subset_left)
  set A1 := (volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3})).toReal with hA1
  set A3 := (volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, -v2, v3})).toReal with hA3
  set A4 := (volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, -v3})).toReal with hA4
  set A5 := (volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {-v1, v2, -v3})).toReal with hA5
  have hr2 : A1 + A3 = dihV 0 v2 v3 v1 * 2 * r ^ 3 / 3 := by
    have h := congrArg ENNReal.toReal hl2
    rw [ENNReal.toReal_add (hfin _) (hfin _),
      ENNReal.toReal_ofReal (by have := dihV_nonneg 0 v2 v3 v1; positivity)] at h
    simpa only [hA1, hA3] using h
  have hr3 : A1 + A4 = dihV 0 v3 v1 v2 * 2 * r ^ 3 / 3 := by
    have h := congrArg ENNReal.toReal hl3
    rw [ENNReal.toReal_add (hfin _) (hfin _),
      ENNReal.toReal_ofReal (by have := dihV_nonneg 0 v3 v1 v2; positivity)] at h
    simpa only [hA1, hA4] using h
  have h5 : A5 = A3 := by
    rw [hA5, hA3, hneg]
  have h4 : A4 + A5 = (Real.pi - dihV 0 v1 v2 v3) * 2 * r ^ 3 / 3 := by
    have h := congrArg ENNReal.toReal hl4
    rw [ENNReal.toReal_add (hfin _) (hfin _),
      ENNReal.toReal_ofReal (by have := dihV_nonneg 0 v1 v2 (-v3); positivity)] at h
    rw [dihV_zero_neg_right] at h
    simpa only [hA4, hA5] using h
  have hx : A1 = (dihV 0 v1 v2 v3 + dihV 0 v2 v3 v1 + dihV 0 v3 v1 v2 - Real.pi)
      * r ^ 3 / 3 := by
    nlinarith [hr2, hr3, h4, h5]
  rw [show volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3}) =
      ENNReal.ofReal ((volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1, v2, v3})).toReal)
      from (ENNReal.ofReal_toReal (hfin _)).symm]
  exact congrArg ENNReal.ofReal (hA1.symm.trans hx)

/-! ## 最终定理 `VOLUME_SOLID_TRIANGLE`（flyspeck.ml:5883） -/

theorem volume_solid_triangle {v0 v1 v2 v3 : V3} {r : ℝ}
    (hr : 0 < r) (hcop : ¬ Coplanar ({v0, v1, v2, v3} : Set V3)) :
    volume (Metric.ball v0 r ∩ affGt ({v0} : Set V3) {v1, v2, v3})
      = ENNReal.ofReal
          ((dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 - Real.pi)
            * r ^ 3 / 3) := by
  have himg : (fun y : V3 => v0 + y) '' ({0, v1 - v0, v2 - v0, v3 - v0} : Set V3) =
      ({v0, v1, v2, v3} : Set V3) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with h0 | h1 | h2 | h3
      · rw [h0]; simp
      · rw [h1]; simp
      · rw [h2]; simp
      · rw [h3]; simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h0 | h1 | h2 | h3
      · exact ⟨0, by simp, by rw [h0]; simp⟩
      · exact ⟨v1 - v0, by simp, by rw [h1]; abel⟩
      · exact ⟨v2 - v0, by simp, by rw [h2]; abel⟩
      · exact ⟨v3 - v0, by simp, by rw [h3]; abel⟩
  have hcop0 : ¬ Coplanar ({0, v1 - v0, v2 - v0, v3 - v0} : Set V3) := by
    intro h
    apply hcop
    rw [← himg]
    exact coplanar_translate v0 h
  obtain ⟨hd10, hd20, hd30, hd12, hd13, hd23⟩ := not_coplanar_distinct hcop0
  have h10 : v1 ≠ v0 := fun h => hd10 (by rw [h]; simp)
  have h20 : v2 ≠ v0 := fun h => hd20 (by rw [h]; simp)
  have h30 : v3 ≠ v0 := fun h => hd30 (by rw [h]; simp)
  have h12 : v1 ≠ v2 := by
    intro h; apply hd12
    have := congrArg (fun x : V3 => x - v0) h; simpa using this
  have h13 : v1 ≠ v3 := by
    intro h; apply hd13
    have := congrArg (fun x : V3 => x - v0) h; simpa using this
  have h23 : v2 ≠ v3 := by
    intro h; apply hd23
    have := congrArg (fun x : V3 => x - v0) h; simpa using this
  have hset : affGt ({v0} : Set V3) {v1, v2, v3} =
      (fun y : V3 => v0 + y) '' affGt ({0} : Set V3) {v1 - v0, v2 - v0, v3 - v0} :=
    affGt_translate h10 h20 h30 h12 h13 h23
  have hball : Metric.ball v0 r = (fun y : V3 => v0 + y) '' Metric.ball 0 r := by
    ext z
    constructor
    · intro hz
      refine ⟨z - v0, ?_, by abel⟩
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      simpa using hz
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
      simpa using hy
  have hvol : volume (Metric.ball v0 r ∩ affGt ({v0} : Set V3) {v1, v2, v3}) =
      volume (Metric.ball 0 r ∩ affGt ({0} : Set V3) {v1 - v0, v2 - v0, v3 - v0}) := by
    rw [hball, hset,
      ← Set.image_inter (f := fun y : V3 => v0 + y) (fun a b h => add_left_cancel h),
      volume_image_add_left]
  have hdih : dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 =
      dihV 0 (v1 - v0) (v2 - v0) (v3 - v0) + dihV 0 (v2 - v0) (v3 - v0) (v1 - v0) +
        dihV 0 (v3 - v0) (v1 - v0) (v2 - v0) := by
    rw [dihV_sub_self v0 v1 v2 v3, dihV_sub_self v0 v2 v3 v1,
      dihV_sub_self v0 v3 v1 v2]
  rw [hvol, volume_solid_triangle_zero hr hcop0]
  congr 1
  rw [← hdih]

end Kepler.Geom

/-
Kepler/Text/LocalFanStepW6K3.lean — wave C-W6-K3（步骤 ①）：`affGt{0}{v,u,w}` 非空见证
+ 两个本地复制的指示函数（Finset）助手。

件目：
* §1 `pW6k3_finset_sum_indicators_v`（复制 PlanarityAuto11:836 private 版）。
* §2 `pW6k2_affGt_nonempty`：互异前提 ⇒ `affGt{0}{v,u,w} ∩ ball 0 1` 非空。
  见证 `t = 1/(3(‖v+u+w‖+1))`、`X = t•(v+u+w)`、系数 `(1-3t, t, t, t)`。

**未交**：② `IsOpen (affGt{0}{v,u,w})`——工单用 `aff_gt_3_1_rep_cross_dot`
只覆盖 **3_1 形** `affGt{x,v,u}{w}`，本目标是 **1_3 形** `affGt{0}{v,u,w}`，
两者不同（见 DELIVERY §2 的精确不对齐点）。③④ 依赖 ②。
-/
import Kepler.Text.LocalFanStepW6

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical MeasureTheory

open scoped Matrix Topology

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 本地复制：指示函数向量和（PlanarityAuto11:836 private 版） -/

/-- 复制件（源：`PlanarityAuto11:836` private）：4 点指示函数向量和。 -/
private theorem pW6k3_finset_sum_indicators_v (t1 t2 t3 t4 : ℝ) (x v u w : V3) :
    (∑ z ∈ ({x, v, u, w} : Finset V3),
      (((if z = x then t1 else 0) + (if z = v then t2 else 0) +
        (if z = u then t3 else 0) + (if z = w then t4 else 0)) • z))
      = t1 • x + t2 • v + t3 • u + t4 • w := by
  have h : ∀ z : V3,
      (((if z = x then t1 else 0) + (if z = v then t2 else 0) +
        (if z = u then t3 else 0) + (if z = w then t4 else 0)) • z)
      = ((if z = x then t1 • z else 0) + (if z = v then t2 • z else 0) +
         (if z = u then t3 • z else 0) + (if z = w then t4 • z else 0)) := by
    intro z
    rw [add_smul, add_smul, add_smul]
    by_cases hx : z = x <;> by_cases hv : z = v <;> by_cases hu : z = u <;>
      by_cases hw : z = w <;> simp [hx, hv, hu, hw]
  rw [Finset.sum_congr rfl (fun z _ => h z)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-! ## §2 ① 非空见证 -/

/-- **`affGt{0}{v,u,w}` 与单位球的交非空**（K 段体积步骤的第一子件）。 -/
theorem pW6k2_affGt_nonempty {v u w : V3}
    (hv0 : v ≠ 0) (hu0 : u ≠ 0) (hw0 : w ≠ 0)
    (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w) :
    (affGt ({0} : Set V3) {v, u, w} ∩ Metric.ball (0 : V3) 1).Nonempty := by
  set s : V3 := v + u + w with hs
  have hspos : 0 < ‖s‖ + 1 := by positivity
  set t : ℝ := 1 / (3 * (‖s‖ + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hthree : 3 * t = 1 / (‖s‖ + 1) := by
    rw [ht]; field_simp
  have hthree_le : 3 * t ≤ 1 := by
    rw [hthree, div_le_one hspos]
    nlinarith [norm_nonneg s]
  set X : V3 := t • s with hX
  have hXnorm : X ∈ Metric.ball (0 : V3) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hX, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    have h1 : t * ‖s‖ = ‖s‖ / (3 * (‖s‖ + 1)) := by
      rw [ht]; ring
    rw [h1, div_lt_one (by positivity)]
    nlinarith [norm_nonneg s]
  have hXaff : X ∈ affGt ({0} : Set V3) {v, u, w} := by
    have hfin : (({0} : Set V3) ∪ {v, u, w}).Finite := by simp
    have hset : hfin.toFinset = ({0, v, u, w} : Finset V3) := by
      apply Finset.ext
      intro z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    have hf0 : (0 : V3) ≠ v := Ne.symm hv0
    have hfu : (0 : V3) ≠ u := Ne.symm hu0
    have hfw : (0 : V3) ≠ w := Ne.symm hw0
    refine ⟨fun z => if z = 0 then 1 - 3 * t else t, hfin, ?_, ?_, ?_⟩
    · rw [hX, hs, hset]
      have hcongr : (∑ z ∈ ({0, v, u, w} : Finset V3),
          ((if z = 0 then 1 - 3 * t else t) • z))
          = ∑ z ∈ ({0, v, u, w} : Finset V3),
            (((if z = 0 then (1 - 3 * t) else 0) + (if z = v then t else 0) +
              (if z = u then t else 0) + (if z = w then t else 0)) • z) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;>
          simp [hf0, hfu, hfw, hv0, hu0, hw0, hvu, hvw, huw,
            Ne.symm hvu, Ne.symm hvw, Ne.symm huw]
      rw [hcongr, pW6k3_finset_sum_indicators_v (1 - 3 * t) t t t 0 v u w]
      simp only [smul_zero, zero_add]
      module
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simp [hv0, htpos]
      · simp [hu0, htpos]
      · simp [hw0, htpos]
    · rw [hset]
      rw [Finset.sum_insert (by simp [hf0, hfu, hfw])]
      rw [Finset.sum_insert (by simp [hvu, hvw])]
      rw [Finset.sum_insert (by simp [huw])]
      rw [Finset.sum_singleton]
      simp [hv0, hu0, hw0]
      linarith
  exact ⟨X, hXaff, hXnorm⟩

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6k2_affGt_nonempty
#print axioms Kepler.Text.pW6k2_affGt_nonempty

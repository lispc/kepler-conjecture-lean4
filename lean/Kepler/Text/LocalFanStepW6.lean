/-
Kepler/Text/LocalFanStepW6.lean — wave C-W6：两个本地重证件（`MEASURABLE_BALL_AFF_GT` /
`NOT_COPLANAR_NOT_COLLINEAR`）+ K 段装配骨架说明。

件目：
* §1 `pW6_convex_affGt`：`affGt s t` 凸（`Geom/SolidAngle.lean:38` 的 private 版，
  本地重证；它是 measurable 版的前置件——**coordinator 估的 5 行里没算它**，
  实际 ~30 行）。
* §2 `pW6_measurable_ball_affGt`：HOL `MEASURABLE_BALL_AFF_GT`
  = `NullMeasurableSet (ball z r ∩ affGt s t) volume`（3 行，吃 §1）。
* §3 `pW6_notCollinear3_of_notCoplanar`：HOL `NOT_COPLANAR_NOT_COLLINEAR`
  （`PackingAuto22:11489` 的 private 版，本地重证，~45 行）。
* §4 装配骨架：K 段输入链见 DELIVERY §3（本波不写 K 本体；按 300 行/3 轮止损）。

不消费任何 sorry 桩；不引入新公理。
-/
import Kepler.Geom.SolidAngle
import Kepler.Text.LocalFanStepW5B2

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical MeasureTheory

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 `affGt` 凸（SolidAngle private 版本地重证） -/

/-- HOL `CONVEX_AFF_GT`：`affGt s t` 是凸集。 -/
theorem pW6_convex_affGt (s t : Set V3) : Convex ℝ (affGt s t) := by
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

/-! ## §2 `MEASURABLE_BALL_AFF_GT` -/

/-- HOL `MEASURABLE_BALL_AFF_GT`：球与 `affGt` 之交可测。 -/
theorem pW6_measurable_ball_affGt (z : V3) (r : ℝ) (s t : Set V3) :
    NullMeasurableSet (Metric.ball z r ∩ affGt s t) volume :=
  ((convex_ball z r).inter (pW6_convex_affGt s t)).nullMeasurableSet volume

/-! ## §3 `NOT_COPLANAR_NOT_COLLINEAR` -/

/-- HOL `NOT_COPLANAR_NOT_COLLINEAR`：`¬ Coplanar {0,u0,u1,u2}` ⇒
`¬ Collinear3 u0 u1 u2`（`PackingAuto22:11489` private 版本地重证）。 -/
theorem pW6_notCollinear3_of_notCoplanar {u0 u1 u2 : V3}
    (hcp : ¬ Coplanar ({0, u0, u1, u2} : Set V3)) : ¬ Collinear3 u0 u1 u2 := by
  intro hc
  apply hcp
  rw [Collinear3, collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨p₀, v, hv⟩ := hc
  have hsub3 : ({p₀, p₀ + v} : Set V3) ⊆ ({p₀, p₀ + v, 0} : Set V3) := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  have hmono : ∀ q : V3, q ∈ (affineSpan ℝ ({p₀, p₀ + v} : Set V3) : Set V3) →
      q ∈ (affineSpan ℝ ({p₀, p₀ + v, 0} : Set V3) : Set V3) := by
    intro q hq
    exact affineSpan_mono ℝ hsub3 hq
  have hid (w : V3) (hw : w ∈ ({u0, u1, u2} : Set V3)) :
      ∃ r : ℝ, w = AffineMap.lineMap (p₀ : V3) (p₀ + v) r ∧
        AffineMap.lineMap (p₀ : V3) (p₀ + v) r ∈
          (affineSpan ℝ ({p₀, p₀ + v} : Set V3) : Set V3) := by
    obtain ⟨r, hr⟩ := hv w hw
    refine ⟨r, ?_, AffineMap.lineMap_mem_affineSpan_pair r p₀ (p₀ + v)⟩
    rw [AffineMap.lineMap_apply]
    have hvsub : (p₀ + v) -ᵥ p₀ = v := by simp only [vsub_eq_sub]; abel
    rw [hvsub]
    exact hr
  refine ⟨p₀, p₀ + v, (0 : V3), fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp0 | hpu0 | hpu1 | hpu2
  · rw [hp0]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  · obtain ⟨r, hid0, hlm⟩ := hid u0 (by simp)
    rw [hpu0, hid0]
    exact hmono _ hlm
  · obtain ⟨r, hid1, hlm⟩ := hid u1 (by simp)
    rw [hpu1, hid1]
    exact hmono _ hlm
  · obtain ⟨r, hid2, hlm⟩ := hid u2 (by simp)
    rw [hpu2, hid2]
    exact hmono _ hlm

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6_convex_affGt
#print axioms Kepler.Text.pW6_convex_affGt
#check @Kepler.Text.pW6_measurable_ball_affGt
#print axioms Kepler.Text.pW6_measurable_ball_affGt
#check @Kepler.Text.pW6_notCollinear3_of_notCoplanar
#print axioms Kepler.Text.pW6_notCollinear3_of_notCoplanar

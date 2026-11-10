/-
Kepler/Text/LocalFanStepW22C2.lean — wave W22-②：C2 的代数核心（径向序 ⟺ 行列式符号）。

C2（W5a-ii 在案硬点）= `vv n ∈ affGt{0, vv(n-1)}{v}`。机器代数化：
两个 run 点在同一半平面基 `(v, r)` 下写成 `vv m = b_m • v + g_m • r`（`g_m > 0`），
则
  C2 ⟺ `b_y * g_a - b_a * g_y > 0`（2×2 行列式 = 「径向序」的精确陈述）。
该化约定双 run 段通用（u 段 `r := vv 1`、w 段 `r := ιv`，两者都天然给共同基表示）。

件目：
* §1 `pW22_rep_unique`：(v, r) 非共面方向下的表示唯一性。
* §2 `pW22_c2_iff_det`：C2 ⟺ 行列式正（affGt_pair_iff 两向 + 系数解）。
-/
import Kepler.Text.LocalFanStepW22

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 (v, r) 表示唯一性 -/

/-- `v, r`（均非零且不与原点共线）为基时的表示唯一性。 -/
theorem pW22_rep_unique {v r : V3} (hv0 : v ≠ 0) (hr0 : r ≠ 0)
    (hnc : ¬ Collinear3 (0 : V3) v r)
    {b1 g1 b2 g2 : ℝ} (h : b1 • v + g1 • r = b2 • v + g2 • r) :
    b1 = b2 ∧ g1 = g2 := by
  have hdiff : (b1 - b2) • v + (g1 - g2) • r = 0 := by
    rw [sub_smul, sub_smul]
    rw [show b1 • v - b2 • v + (g1 • r - g2 • r)
      = (b1 • v + g1 • r) - (b2 • v + g2 • r) by abel]
    rw [h, sub_self]
  have hb : b1 - b2 = 0 := by
    by_contra hbne
    have hv_eq : v = (-(g1 - g2) / (b1 - b2)) • r := by
      have h1 : (b1 - b2) • v = -((g1 - g2) • r) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hdiff
      have hscalar : (b1 - b2) * (-(g1 - g2) / (b1 - b2)) = -(g1 - g2) := by
        field_simp
      have h4 : (b1 - b2) • ((-(g1 - g2) / (b1 - b2)) • r) = -((g1 - g2) • r) := by
        rw [smul_smul, hscalar, neg_smul]
      have h5 : (b1 - b2) • v = (b1 - b2) • ((-(g1 - g2) / (b1 - b2)) • r) := by
        rw [h1, h4]
      calc v = (b1 - b2)⁻¹ • ((b1 - b2) • v) := by
            rw [smul_smul, inv_mul_cancel₀ hbne, one_smul]
        _ = (b1 - b2)⁻¹ • ((b1 - b2) • ((-(g1 - g2) / (b1 - b2)) • r)) := by
            rw [h5]
        _ = (-(g1 - g2) / (b1 - b2)) • r := by
            rw [smul_smul, inv_mul_cancel₀ hbne, one_smul]
    have hk0 : -(g1 - g2) / (b1 - b2) ≠ 0 := by
      intro hk
      rw [hk, zero_smul] at hv_eq
      exact hv0 hv_eq
    apply hnc
    rw [collinear3_iff_smul (v := (0 : V3)) (w := v) (w1 := r) hv0]
    exact ⟨(-(g1 - g2) / (b1 - b2))⁻¹, by
      rw [sub_zero, sub_zero, hv_eq, inv_smul_smul₀ hk0]⟩
  have hg : g1 - g2 = 0 := by
    have h2 : (b1 - b2) • v = 0 := by rw [hb, zero_smul]
    rw [h2, zero_add] at hdiff
    rcases smul_eq_zero.mp hdiff with h3 | h3
    · exact h3
    · exact absurd h3 hr0
  constructor <;> linarith

/-! ## §2 C2 ⟺ 行列式正 -/

/-- **C2 的代数核心**：共同基 `(v, r)` 表示下
`y ∈ affGt{0, a}{v} ↔ 0 < b1 * g2 - b2 * g1`（`a, y` 的基表示系数分别为
`(b2,g2)`、`(b1,g1)`，`g1, g2 > 0`）。 -/
theorem pW22_c2_iff_det {v r a y : V3} {b1 g1 b2 g2 : ℝ}
    (hv0 : v ≠ 0) (hr0 : r ≠ 0) (hnc : ¬ Collinear3 (0 : V3) v r)
    (ha0 : a ≠ 0) (hva : v ≠ a)
    (hy : y = b1 • v + g1 • r) (hg1 : 0 < g1)
    (ha : a = b2 • v + g2 • r) (hg2 : 0 < g2) :
    y ∈ affGt ({0, a} : Set V3) {v} ↔ 0 < b1 * g2 - b2 * g1 := by
  have h0a : (0 : V3) ≠ a := Ne.symm ha0
  have h0v : (0 : V3) ≠ v := Ne.symm hv0
  constructor
  · intro hm
    obtain ⟨c, hc, h, hyc⟩ :=
      (affGt_pair_iff (v0 := (0 : V3)) (v1 := a) (x := v) (y := y)
        h0a hv0 hva).mp hm
    have hyc' : y = c • v + h • a := by simpa using hyc
    have hrep : y = (c + h * b2) • v + (h * g2) • r := by
      rw [hyc', ha, smul_add, smul_smul, smul_smul]
      module
    have heq : b1 • v + g1 • r = (c + h * b2) • v + (h * g2) • r :=
      hy.symm.trans hrep
    obtain ⟨h1, h2⟩ := pW22_rep_unique hv0 hr0 hnc heq
    have hcval : c = (b1 * g2 - b2 * g1) / g2 := by
      rw [h1, h2]
      field_simp
      ring
    rw [hcval] at hc
    exact (div_pos_iff_of_pos_right hg2).mp hc
  · intro hdet
    have hsub : ((b1 * g2 - b2 * g1) / g2) • v + (g1 / g2) • a
        = b1 • v + g1 • r := by
      rw [ha, smul_add, smul_smul, smul_smul]
      have hs1 : (g1 / g2) * g2 = g1 := by field_simp
      rw [hs1]
      have hc : (b1 * g2 - b2 * g1) / g2 + g1 / g2 * b2 = b1 := by
        field_simp
        ring
      rw [← add_assoc, ← add_smul, hc]
    refine (affGt_pair_iff (v0 := (0 : V3)) (v1 := a) (x := v) (y := y)
      h0a hv0 hva).mpr
      ⟨(b1 * g2 - b2 * g1) / g2,
        (div_pos_iff_of_pos_right hg2).mpr hdet, g1 / g2, ?_⟩
    simp only [sub_zero]
    rw [hy, ← hsub]

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW22_rep_unique
#print axioms Kepler.Text.pW22_c2_iff_det

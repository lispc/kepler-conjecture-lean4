/-
Kepler.Text.Gamma4Val — lane `gamma4-val1e6`, V1 + V3 + V2.

* V1: `π` to 1e-20 (reused Mathlib `Real.pi_gt_d20` / `pi_lt_d20`; no new
  decimal-precision π proof).
* V3: `arcsin(1/3) ∈ (0.339836909, 0.339836910)` (width 1e-9) and
  `arccos(1/3) ∈ (1.2309594167, 1.2309594178)` (width 1.2e-9), proved locally
  from the order-7/9 sin Taylor brackets (the PA19 kernel, re-derived here
  because `PackingAuto19.p19_arcsin_bounds` is `private`), plus the
  `arccos(1/3) = 2·arctan(1/√2)` bridge.
* V2: `sol0`, `tau0`, `mm1`, `mm2` with widths 2e-8 / 6e-8 / 5e-7 / 2e-7
  (all <= 2e-6).

All declarations are standard-three; see the axiom audit at the tail.
-/
import Kepler.Text.Gamma4Sharp
import Kepler.Interval.Trans

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## V1 — π from Mathlib's 20-digit decimal bounds -/

/-- **V1**: `π` bracketed to width `1e-20` by Mathlib's `pi_gt_d20` /
`pi_lt_d20` (one-line reuse; no local π construction). -/
theorem g4v_pi_bounds :
    (3.14159265358979323846 : ℝ) < Real.pi ∧
      Real.pi < 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩

/-- Consumer form: `π ∈ (3.14159265, 3.14159266)` (width `1e-8`). -/
theorem g4v_pi_bounds_d8 : (3.14159265 : ℝ) < Real.pi ∧ Real.pi < 3.14159266 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

/-! ## V3 — local order-7/9 sine Taylor brackets -/

private theorem g4v_mono {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f)
    (hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ deriv f x) : MonotoneOn f (Set.Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
    (fun x hx => hd x (by
      have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      exact hlt.le))

private theorem g4v_antitone {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f)
    (hd : ∀ x : ℝ, 0 ≤ x → deriv f x ≤ 0) : AntitoneOn f (Set.Ici 0) :=
  antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
    (fun x hx => hd x (by
      have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      exact hlt.le))

private theorem g4v_cos_le_taylor4 {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  have hC : Continuous (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) := by
    fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) := by
    fun_prop
  have step := g4v_antitone (f := fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24))
    hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) x
            = -Real.sin x + x - x ^ 3 / 6 := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := Real.sin_ge_sub_cube hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem g4v_sin_le_taylor5 {t : ℝ} (ht : 0 ≤ t) :
    Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have hC : Continuous (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) := by
    fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) := by
    fun_prop
  have step := g4v_antitone (f := fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) x
            = Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := g4v_cos_le_taylor4 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem g4v_cos_ge_taylor6 {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
  have hC : Continuous (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) := by fun_prop
  have step := g4v_mono (f := fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.cos s -
            (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) x
            = -Real.sin x + x - x ^ 3 / 6 + x ^ 5 / 120 := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := g4v_sin_le_taylor5 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem g4v_sin_ge_taylor7 {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 ≤ Real.sin t := by
  have hC : Continuous (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) := by fun_prop
  have step := g4v_mono (f := fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.sin s -
            (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) x
            = Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := g4v_cos_ge_taylor6 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem g4v_cos_le_taylor8 {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 := by
  have hC : Continuous (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) := by fun_prop
  have step := g4v_antitone (f := fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.cos s -
            (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) x
            = -Real.sin x + x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := g4v_sin_ge_taylor7 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem g4v_sin_le_taylor9 {t : ℝ} (ht : 0 ≤ t) :
    Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 := by
  have hC : Continuous (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) := by fun_prop
  have step := g4v_antitone (f := fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.sin s -
            (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) x
            = Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := g4v_cos_le_taylor8 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

/-- **V3, arcsin side**: `arcsin(1/3) ∈ (0.339836909, 0.339836910)` (width
`1e-9`).  Same kernel as `PackingAuto19.p19_arcsin_bounds` (order-7 lower /
order-9 upper sine Taylor + strict monotonicity on `[-π/2, π/2]`), with the
decimal endpoints tightened from `1e-7` to `1e-9`. -/
theorem g4v_arcsin_third_bounds :
    (0.339836909 : ℝ) < Real.arcsin (1 / 3) ∧
      Real.arcsin (1 / 3) < 0.339836910 := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  set a := Real.arcsin (1 / 3) with hdef
  have hamem : a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have ht1mem : (0.339836909 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have ht2mem : (0.339836910 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hsa : Real.sin a = 1 / 3 := Real.sin_arcsin (by norm_num) (by norm_num)
  have h9 := g4v_sin_le_taylor9 (t := 0.339836909) (by norm_num)
  have hlt : Real.sin 0.339836909 < Real.sin a := by
    rw [hsa]
    have hr : 0.339836909 - 0.339836909 ^ 3 / 6 + 0.339836909 ^ 5 / 120
        - 0.339836909 ^ 7 / 5040 + 0.339836909 ^ 9 / 362880 < (1 : ℝ) / 3 := by
      norm_num
    linarith
  have h7 := g4v_sin_ge_taylor7 (t := 0.339836910) (by norm_num)
  have hgt : Real.sin a < Real.sin 0.339836910 := by
    rw [hsa]
    have hr : (1 : ℝ) / 3 < 0.339836910 - 0.339836910 ^ 3 / 6 + 0.339836910 ^ 5 / 120
        - 0.339836910 ^ 7 / 5040 := by
      norm_num
    linarith
  exact ⟨(Real.strictMonoOn_sin.lt_iff_lt ht1mem hamem).mp hlt,
    (Real.strictMonoOn_sin.lt_iff_lt hamem ht2mem).mp hgt⟩

/-- **V3, arccos side**: `arccos(1/3) = π/2 − arcsin(1/3) ∈
(1.2309594167, 1.2309594178)` (width `1.2e-9`). -/
theorem g4v_arccos_third_bounds :
    (1.2309594167 : ℝ) < Real.arccos (1 / 3) ∧
      Real.arccos (1 / 3) < 1.2309594178 := by
  obtain ⟨ha1, ha2⟩ := g4v_arcsin_third_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have heq : Real.arccos (1 / 3) = Real.pi / 2 - Real.arcsin (1 / 3) :=
    Real.arccos_eq_pi_div_two_sub_arcsin _
  constructor <;> rw [heq] <;> linarith

/-- **V3, bridge**: `2·arctan(1/√2) = arccos(1/3)` (re-derived locally from
`cos_two_mul` + `cos_arctan`; Gamma4Sharp's twin is `private`). -/
theorem g4v_arccos_eq_two_arctan :
    2 * Real.arctan (1 / Real.sqrt 2) = Real.arccos (1 / 3) := by
  have hcos : Real.cos (2 * Real.arctan (1 / Real.sqrt 2)) = 1 / 3 := by
    rw [Real.cos_two_mul, Real.cos_arctan]
    have hden : (1 : ℝ) + (1 / Real.sqrt 2) ^ 2 = 3 / 2 := by
      have e1 : (1 / Real.sqrt 2) ^ 2 = 1 / Real.sqrt 2 ^ 2 := by rw [one_div_pow]
      rw [e1, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hden]
    have hs : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
    rw [show (1 / Real.sqrt (3 / 2)) ^ 2 = 1 / (3 / 2) by rw [one_div_pow, hs]]
    norm_num
  have hcosA : Real.cos (Real.arccos (1 / 3)) = 1 / 3 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hmem1 : 2 * Real.arctan (1 / Real.sqrt 2) ∈ Set.Icc 0 Real.pi := by
    constructor
    · have hpos : 0 < Real.arctan (1 / Real.sqrt 2) :=
        Real.arctan_pos.mpr (by positivity)
      linarith
    · have hlt : Real.arctan (1 / Real.sqrt 2) < Real.pi / 2 :=
        Real.arctan_lt_pi_div_two _
      linarith
  have hmem2 : Real.arccos (1 / 3) ∈ Set.Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  exact Real.injOn_cos hmem1 hmem2 (by rw [hcos, hcosA])

/-! ## V2 — `sol0`, `tau0`, `mm1`, `mm2` -/

/-- `√8` to width `1e-7`. -/
theorem g4v_sqrt8_bounds :
    (2.82842712 : ℝ) < Real.sqrt 8 ∧ Real.sqrt 8 < 2.82842713 := by
  constructor
  · exact Real.lt_sqrt_of_sq_lt (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- `√2` to width `1e-7`. -/
theorem g4v_sqrt2_bounds :
    (1.41421356 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41421357 := by
  constructor
  · exact Real.lt_sqrt_of_sq_lt (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- **V2**: `sol0 ∈ [0.55128559, 0.55128561]` (width `2e-8`; true value
`0.55128559843…`). -/
theorem g4v_sol0_bounds :
    (0.551285596 : ℝ) ≤ sol0 ∧ sol0 ≤ 0.551285600 := by
  obtain ⟨ha1, ha2⟩ := g4v_arccos_third_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hs : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  constructor <;> rw [hs] <;> linarith

/-- **V2**: `tau0 ∈ [1.5406584, 1.5406589]` (width `5e-7`; true value
`1.5406586457…`). -/
theorem g4v_tau0_bounds :
    (1.54065861 : ℝ) ≤ tau0 ∧ tau0 ≤ 1.54065870 := by
  obtain ⟨hs1, hs2⟩ := g4v_sol0_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have ht : tau0 = 4 * Real.pi - 20 * sol0 := rfl
  constructor <;> rw [ht] <;> linarith

/-- **V2**: `mm1 ∈ [1.0120806, 1.0120811]` (width `5e-7`; true value
`1.012080868…`). -/
theorem g4v_mm1_bounds :
    (1.0120808 : ℝ) ≤ mm1 ∧ mm1 ≤ 1.0120809 := by
  obtain ⟨hs1, hs2⟩ := g4v_sol0_bounds
  obtain ⟨ht1, ht2⟩ := g4v_tau0_bounds
  obtain ⟨h81, h82⟩ := g4v_sqrt8_bounds
  have hmm : mm1 = sol0 * Real.sqrt 8 / tau0 := rfl
  have htpos : (0 : ℝ) < tau0 := by linarith
  constructor
  · rw [hmm, le_div_iff₀ htpos]
    have h1 : (1.0120808 : ℝ) * tau0 ≤ 1.0120808 * (1.54065870) :=
      mul_le_mul_of_nonneg_left ht2 (by norm_num)
    have h2 : (0.551285596 : ℝ) * 2.82842712 ≤ sol0 * Real.sqrt 8 :=
      mul_le_mul hs1 h81.le (by norm_num) (by linarith)
    nlinarith [h1, h2]
  · rw [hmm, div_le_iff₀ htpos]
    have h1 : sol0 * Real.sqrt 8 ≤ (0.551285600 : ℝ) * 2.82842713 :=
      mul_le_mul hs2 h82.le (by positivity) (by norm_num)
    have h2 : (1.0120809 : ℝ) * (1.54065861) ≤ 1.0120809 * tau0 :=
      mul_le_mul_of_nonneg_left ht1 (by norm_num)
    nlinarith [h1, h2]

/-- **V2**: `mm2 ∈ [0.0254144, 0.0254146]` (width `2e-7`; true value
`0.0254145072…`). -/
theorem g4v_mm2_bounds :
    (0.02541450 : ℝ) ≤ mm2 ∧ mm2 ≤ 0.02541451 := by
  obtain ⟨hs1, hs2⟩ := g4v_sol0_bounds
  obtain ⟨ht1, ht2⟩ := g4v_tau0_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  obtain ⟨h21, h22⟩ := g4v_sqrt2_bounds
  have hmm : mm2 = (6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0) := rfl
  have htpos : (0 : ℝ) < 6 * tau0 := by linarith
  have hNlo : (6 * (0.551285596 : ℝ) - 3.14159265358979323847) ≤ 6 * sol0 - Real.pi := by
    linarith [hs1]
  have hNhi : 6 * sol0 - Real.pi ≤ 6 * (0.551285600 : ℝ) - 3.14159265358979323846 := by
    linarith [hs2]
  constructor
  · rw [hmm, le_div_iff₀ htpos]
    have hDen : (0.02541450 : ℝ) * (6 * tau0) ≤ 0.02541450 * (6 * 1.54065870) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have hNum : (0.02541450 : ℝ) * (6 * 1.54065870) ≤
        (6 * (0.551285596 : ℝ) - 3.14159265358979323847) * 1.41421356 := by
      norm_num
    have hPr : (6 * (0.551285596 : ℝ) - 3.14159265358979323847) * 1.41421356
        ≤ (6 * sol0 - Real.pi) * Real.sqrt 2 :=
      mul_le_mul hNlo h21.le (by norm_num) (by linarith)
    nlinarith [hDen, hNum, hPr]
  · rw [hmm, div_le_iff₀ htpos]
    have hNum : (6 * sol0 - Real.pi) * Real.sqrt 2
        ≤ (6 * (0.551285600 : ℝ) - 3.14159265358979323846) * 1.41421357 :=
      mul_le_mul hNhi h22.le (by positivity) (by linarith)
    have hDen : (0.02541451 : ℝ) * (6 * 1.54065861) ≤ 0.02541451 * (6 * tau0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have hNum2 : (6 * (0.551285600 : ℝ) - 3.14159265358979323846) * 1.41421357
        ≤ 0.02541451 * (6 * 1.54065861) := by
      norm_num
    nlinarith [hNum, hDen, hNum2]

/-! ## Axiom audit -/

#print axioms g4v_pi_bounds
#print axioms g4v_pi_bounds_d8
#print axioms g4v_arcsin_third_bounds
#print axioms g4v_arccos_third_bounds
#print axioms g4v_arccos_eq_two_arctan
#print axioms g4v_sqrt8_bounds
#print axioms g4v_sqrt2_bounds
#print axioms g4v_sol0_bounds
#print axioms g4v_tau0_bounds
#print axioms g4v_mm1_bounds
#print axioms g4v_mm2_bounds

end Kepler.Text

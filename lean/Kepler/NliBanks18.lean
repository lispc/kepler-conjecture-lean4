/-
Kepler.NliBanks18 — lane `math5-w1`, item 1: the bank `bank_QZECFICwt0corner`
(Assembly debt `nliCell3QZECFICwt0corner`, HOL ineq.hl:1389 `QZECFIC wt0 corner`,
tags [Sharp; Eps 1.0e-8]) closed by hand math.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks11
import Kepler.NliBanks13

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks18
open Kepler.Text
open Kepler.NliBanks11
open Kepler.NliBanks12
open Kepler.NliBanks13

/-! ## 0. Generic monotonicity helper -/

/-- `f` with `f 0 = 0` and `f' ≥ 0` on `[0,∞)` is nonnegative there. -/
private theorem nb18_nonneg_of_deriv {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ deriv f x) : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
      (fun x hx => by
        have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
        exact hd x hlt.le)
  intro s hs
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  rwa [h0] at h

/-- No odd multiple of `π/2` lies in an interval strictly inside `(0, π/2)`. -/
private theorem nb18_not_halfpi {x : ℝ} (hx : 0 < x) (hx' : x < Real.pi / 2) :
    ∀ k : ℤ, x ≠ (2 * k + 1) * Real.pi / 2 := by
  intro k hk
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hx2 : (0:ℝ) < ((2:ℝ) * (k : ℝ) + 1) * Real.pi / 2 := by rw [← hk]; exact hx
  have hx3 : ((2:ℝ) * (k : ℝ) + 1) * Real.pi / 2 < Real.pi / 2 := by rw [← hk]; exact hx'
  rcases Int.lt_trichotomy k 0 with h | h | h
  · have hkr : ((2:ℝ) * (k : ℝ) + 1) ≤ -(1:ℝ) := by
      have hk0 : (k:ℤ) ≤ -1 := by omega
      have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast hk0
      linarith
    have hpos : (0:ℝ) < ((2:ℝ) * (k : ℝ) + 1) * Real.pi := by
      have hid : ((2:ℝ)*(k:ℝ)+1)*Real.pi/2 + ((2:ℝ)*(k:ℝ)+1)*Real.pi/2 =
        ((2:ℝ)*(k:ℝ)+1)*Real.pi := by ring
      nlinarith [hx2, hid, hpi]
    have hprod : ((2:ℝ) * (k : ℝ) + 1) * Real.pi ≤ -(1:ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hkr (le_of_lt hpi)
    linarith [hpos, hprod, hpi]
  · subst h
    norm_num at hx3
  · have hkr : (2:ℝ) * (k : ℝ) + 1 ≥ 3 := by
      have hk' : (k:ℝ) ≥ 1 := by exact_mod_cast h
      linarith
    have hx3' : ((2:ℝ) * (k : ℝ) + 1) * Real.pi / 2 ≥ Real.pi / 2 := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith [hkr, hpi]
    exact absurd hx3 (not_lt.mpr hx3')

/-! ## 1. The order-33 arctan series bracket -/

/-- The 17-term alternating arctan partial sum `Σ (−1)^k x^{2k+1}/(2k+1)`. -/
private noncomputable def nb18P (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)

/-- Its derivative sum `Σ (−1)^k x^{2k}`. -/
private noncomputable def nb18Q (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * k)

private theorem nb18_hd_term (x : ℝ) (k : ℕ) :
    HasDerivAt (fun y : ℝ => y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) (x ^ (2 * k)) x := by
  have hp : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
      (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) x :=
    hasDerivAt_pow (2 * k + 1) x
  have hc : (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) / ((2 * k + 1 : ℕ) : ℝ) = x ^ (2 * k) := by
    field_simp
  rw [← hc]
  exact hp.div_const ((2 * k + 1 : ℕ) : ℝ)

private theorem nb18_hasDerivAt_P (x : ℝ) : HasDerivAt nb18P (nb18Q x) x := by
  unfold nb18P
  refine HasDerivAt.fun_sum ?_
  intro k _
  refine (HasDerivAt.const_mul ((-1 : ℝ) ^ (k : ℕ)) (nb18_hd_term x k)).congr_of_eventuallyEq ?_
  filter_upwards with y
  ring

private theorem nb18_deriv_P (x : ℝ) : deriv nb18P x = nb18Q x :=
  (nb18_hasDerivAt_P x).deriv

/-- Induction step core: `(1+x²)·Σ_{k<n+1} = 1 + (−1)^n x^{2n+2}`. -/
private theorem nb18_Q_mul_go (x : ℝ) (n : ℕ) :
    (1 + x ^ 2) * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * k))
      = 1 + (-1 : ℝ) ^ n * x ^ (2 * n + 2) := by
  induction n with
  | zero => rw [Finset.sum_range_succ]; norm_num
  | succ n ih =>
    have hsg : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
      rw [pow_succ]; ring
    rw [Finset.sum_range_succ, mul_add, ih, hsg]
    ring

/-- `(1+x²)·Σ = 1+x³⁴`. -/
private theorem nb18_Q_mul (x : ℝ) : (1 + x ^ 2) * nb18Q x = 1 + x ^ 34 := by
  rw [nb18Q]
  have h := nb18_Q_mul_go x 16
  norm_num [pow_succ] at h
  linarith

private theorem nb18_cont_P : Continuous nb18P := by
  unfold nb18P; fun_prop

private theorem nb18_diff_P : Differentiable ℝ nb18P := by
  unfold nb18P; fun_prop

private theorem nb18_cont_f35 :
    Continuous (fun y : ℝ => Real.arctan y - nb18P y + y ^ 35 / (35:ℝ)) :=
  (Real.continuous_arctan.sub nb18_cont_P).add ((continuous_pow 35).div_const (35:ℝ))

private theorem nb18_diff_f35 :
    Differentiable ℝ (fun y : ℝ => Real.arctan y - nb18P y + y ^ 35 / (35:ℝ)) :=
  (Real.differentiable_arctan.sub nb18_diff_P).add ((differentiable_pow 35).div_const (35:ℝ))

private theorem nb18_P_strictMonoOn : StrictMonoOn nb18P (Set.Ici 0) := by
  refine strictMonoOn_of_deriv_pos (D := Set.Ici (0:ℝ)) (f := nb18P)
    (convex_Ici (0:ℝ)) nb18_cont_P.continuousOn ?_
  intro x hx
  have hx' : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
  rw [nb18_deriv_P]
  have h := nb18_Q_mul x
  have h2 : (0:ℝ) < 1 + x ^ 2 := by positivity
  by_contra hneg
  push_neg at hneg
  have hprod : (1 + x ^ 2) * nb18Q x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2.le hneg
  have hge0 : (0:ℝ) ≤ x ^ 34 := by positivity
  linarith [h, hprod, hge0]

/-- Upper bracket: `arctan s ≤ nb18P s` for `s ≥ 0`. -/
private theorem nb18_atan_le_P {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ nb18P s := by
  have h := nb18_nonneg_of_deriv
    (f := fun y : ℝ => nb18P y - Real.arctan y)
    (hC := nb18_cont_P.sub Real.continuous_arctan)
    (hD := nb18_diff_P.sub Real.differentiable_arctan)
    (h0 := by rw [nb18P]; simp)
    (hd := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => nb18P y - Real.arctan y)
          (nb18Q x - 1 / (1 + x ^ 2)) x :=
        (nb18_hasDerivAt_P x).sub (Real.hasDerivAt_arctan x)
      have hq : nb18Q x - 1 / (1 + x ^ 2) = x ^ 34 / (1 + x ^ 2) := by
        field_simp
        linarith [nb18_Q_mul x]
      rw [h1.deriv, hq]
      positivity) s hs
  linarith

/-- Lower bracket: `nb18P s − s³⁵/35 ≤ arctan s` for `s ≥ 0`. -/
private theorem nb18_series_le {s : ℝ} (hs : 0 ≤ s) :
    nb18P s - s ^ 35 / 35 ≤ Real.arctan s := by
  have h := nb18_nonneg_of_deriv
    (f := fun y : ℝ => Real.arctan y - nb18P y + y ^ 35 / 35)
    (hC := nb18_cont_f35)
    (hD := nb18_diff_f35)
    (h0 := by rw [nb18P]; simp)
    (hd := by
      intro x hx
      have h35 : HasDerivAt (fun y : ℝ => y ^ 35 / (35 : ℝ)) (x ^ 34) x := by
        simpa [pow_succ] using ((hasDerivAt_pow 35 x).div_const (35 : ℝ))
      have h1 : HasDerivAt (fun y : ℝ => Real.arctan y - nb18P y + y ^ 35 / (35 : ℝ))
          (1 / (1 + x ^ 2) - nb18Q x + x ^ 34) x :=
        ((Real.hasDerivAt_arctan x).sub (nb18_hasDerivAt_P x)).add h35
      have hq : 1 / (1 + x ^ 2) - nb18Q x + x ^ 34 = x ^ 36 / (1 + x ^ 2) := by
        field_simp
        rw [nb18_Q_mul x]
        ring
      rw [h1.deriv, hq]
      positivity) s hs
  linarith

/-! ## 2. `arctan s + arctan (1/s) = π/2` -/

/-- `arctan s + arctan (1/s) = π/2` for `s > 0`. -/
private theorem nb18_atan_add_inv {s : ℝ} (hs : 0 < s) :
    Real.arctan s + Real.arctan (1 / s) = Real.pi / 2 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hatanpos : (0:ℝ) < Real.arctan s := by rw [Real.arctan_pos]; linarith
  have hθlt : Real.pi / 2 - Real.arctan s < Real.pi / 2 := by linarith
  have hθrange : -(Real.pi / 2) < Real.pi / 2 - Real.arctan s := by
    have h2 : Real.arctan s < Real.pi / 2 := by
      obtain ⟨_, h2⟩ := Real.arctan_mem_Ioo s
      exact h2
    linarith
  have htan : Real.tan (Real.pi / 2 - Real.arctan s) = 1 / s := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
      Real.cos_arctan, Real.sin_arctan]
    field_simp
  have hinv : Real.arctan (1 / s) = Real.pi / 2 - Real.arctan s := by
    rw [← htan]
    exact Real.arctan_tan (by linarith) hθlt
  rw [hinv]
  ring

/-! ## 3. Rational base brackets and the two corner identities -/

/-- `√2` bracket. -/
private theorem nb18_sqrt2 : (1.41421356 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.4142136 := by
  refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
  · norm_num
  · rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 1.4142136)]
    norm_num

/-- `π` bracket (Mathlib decimal bounds). -/
private theorem nb18_pi : (3.141592 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 3.141593 :=
  ⟨Real.pi_gt_d6.le, Real.pi_lt_d6.le⟩

/-- `α = arctan (√2)` bracket. -/
private theorem nb18_alpha : (0.955316 : ℝ) ≤ Real.arctan (Real.sqrt 2) ∧
    Real.arctan (Real.sqrt 2) ≤ 0.955317 := by
  have hw : (0.7071067 : ℝ) ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 ≤ 0.7071068 := by
    have hs := nb18_sqrt2
    have h2pos : (0:ℝ) < Real.sqrt 2 := by positivity
    constructor
    · rw [le_div_iff₀ h2pos]
      have h1 := mul_le_mul_of_nonneg_left hs.1 (by norm_num : (0:ℝ) ≤ 0.7071067)
      linarith
    · rw [div_le_iff₀ h2pos]
      have h1 := mul_le_mul_of_nonneg_left hs.1 (by norm_num : (0:ℝ) ≤ 0.7071068)
      linarith
  have hwpos : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
  have hwle : 1 / Real.sqrt 2 ≤ 0.7071068 := hw.2
  have hwge : 0.7071067 ≤ 1 / Real.sqrt 2 := hw.1
  have hid : Real.arctan (Real.sqrt 2) = Real.pi / 2 - Real.arctan (1 / Real.sqrt 2) := by
    have h := nb18_atan_add_inv (show (0:ℝ) < Real.sqrt 2 by positivity)
    linarith
  rw [hid]
  constructor
  · -- arctan w ≤ P(0.7071068) ≤ 0.6154804
    have hP : Real.arctan (1 / Real.sqrt 2) ≤ nb18P 0.7071068 := by
      refine le_trans (nb18_atan_le_P hwpos.le) ?_
      exact nb18_P_strictMonoOn.monotoneOn (Set.mem_Ici.mpr hwpos.le)
        (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.7071068)) hwle
    have ev : nb18P 0.7071068 ≤ 0.61548 := by
      norm_num [nb18P]
    have hpi := nb18_pi
    nlinarith [hP.trans ev, hpi.1, hpi.2, Real.pi_pos]
  · -- arctan w ≥ P(0.7071067) − 0.7071068^35/35 ≥ 0.6154796
    have hP : nb18P (0.7071067 : ℝ) - (0.7071068 : ℝ) ^ 35 / 35 ≤
        Real.arctan (1 / Real.sqrt 2) := by
      have h1 := nb18_series_le (show (0:ℝ) ≤ 1 / Real.sqrt 2 by positivity)
      have hmono := nb18_P_strictMonoOn.monotoneOn
        (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.7071067))
        (Set.mem_Ici.mpr hwpos.le) hwge
      have hPmono : nb18P (0.7071067 : ℝ) ≤ nb18P (1 / Real.sqrt 2) :=
        nb18_P_strictMonoOn.monotoneOn
          (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.7071067))
          (Set.mem_Ici.mpr hwpos.le) hwge
      have hw35 : (1 / Real.sqrt 2) ^ 35 ≤ (0.7071068 : ℝ) ^ 35 := by
        gcongr
        all_goals { first | exact hwle | positivity | nlinarith [hwle, hwpos] }
      calc nb18P (0.7071067 : ℝ) - (0.7071068 : ℝ) ^ 35 / 35
          ≤ nb18P (1 / Real.sqrt 2) - (1 / Real.sqrt 2) ^ 35 / 35 := by
            nlinarith [hPmono, hw35]
        _ ≤ Real.arctan (1 / Real.sqrt 2) := h1
    have ev : (0.6154797 : ℝ) ≤ nb18P 0.7071067 := by
      norm_num [nb18P]
    have hrem : (0.7071068 : ℝ) ^ 35 / 35 ≤ 0.00000016 := by
      norm_num
    have hpi := nb18_pi
    nlinarith [hP, ev, hrem, hpi.1, hpi.2, Real.pi_pos]

/-- Corner identity 1: `arccos (1/3) = π − 2·arctan (√2)`. -/
private theorem nb18_arccos13 :
    Real.arccos (1 / 3) = Real.pi - 2 * Real.arctan (Real.sqrt 2) := by
  have hal := nb18_alpha
  have hrange : (0:ℝ) ≤ Real.pi - 2 * Real.arctan (Real.sqrt 2) ∧
      Real.pi - 2 * Real.arctan (Real.sqrt 2) ≤ Real.pi := by
    constructor
    · nlinarith [hal.1, hal.2, nb18_pi.1, nb18_pi.2, Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi - 2 * Real.arctan (Real.sqrt 2)) = 1 / 3 := by
    rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan]
    have hsq : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [hsq]
    norm_num [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [← Real.arccos_cos hrange.1 hrange.2, hcos]

/-- Corner identity 2: `arctan (3 − 2√2) = arctan (√2) − π/4`. -/
private theorem nb18_beta :
    Real.arctan (3 - 2 * Real.sqrt 2) = Real.arctan (Real.sqrt 2) - Real.pi / 4 := by
  have hs := nb18_sqrt2
  have halpha : (0:ℝ) < Real.arctan (Real.sqrt 2) := by
    rw [Real.arctan_pos]; nlinarith [hs.1]
  have halpha' : Real.arctan (Real.sqrt 2) < Real.pi / 2 := by
    obtain ⟨_, h2⟩ := Real.arctan_mem_Ioo (Real.sqrt 2)
    exact h2
  have hbeta_pos : (0:ℝ) < Real.arctan (3 - 2 * Real.sqrt 2) := by
    rw [Real.arctan_pos]
    nlinarith [hs.1, hs.2]
  have hbeta' : Real.arctan (3 - 2 * Real.sqrt 2) < Real.pi / 2 := by
    obtain ⟨_, h2⟩ := Real.arctan_mem_Ioo (3 - 2 * Real.sqrt 2)
    exact h2
  have hhalf := nb18_not_halfpi halpha halpha'
  have hhalf2 := nb18_not_halfpi hbeta_pos hbeta'
  have hsub : Real.arctan (Real.sqrt 2) - Real.arctan (3 - 2 * Real.sqrt 2) = Real.pi / 4 := by
    have htan := Real.tan_sub' (⟨hhalf, hhalf2⟩ :
      (∀ k : ℤ, Real.arctan (Real.sqrt 2) ≠ (2 * k + 1) * Real.pi / 2) ∧
      ∀ l : ℤ, Real.arctan (3 - 2 * Real.sqrt 2) ≠ (2 * l + 1) * Real.pi / 2)
    have hne : (1:ℝ) + Real.sqrt 2 * (3 - 2 * Real.sqrt 2) ≠ 0 := by
      intro h
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have h2 : Real.sqrt 2 * (2 * Real.sqrt 2) = 4 := by
        ring_nf
        linarith [hsq]
      rw [mul_sub, h2] at h
      linarith [hs.1]
    have hv : Real.tan (Real.arctan (Real.sqrt 2) - Real.arctan (3 - 2 * Real.sqrt 2)) = 1 := by
      rw [htan, Real.tan_arctan, Real.tan_arctan]
      have hEq : Real.sqrt 2 - (3 - 2 * Real.sqrt 2) =
          (1:ℝ) + Real.sqrt 2 * (3 - 2 * Real.sqrt 2) := by
        have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
        have h4 : Real.sqrt 2 * (2 * Real.sqrt 2) = 4 := by
          rw [show Real.sqrt 2 * (2 * Real.sqrt 2) = 2 * (Real.sqrt 2 ^ 2) from by ring, hsq2]
          norm_num
        rw [mul_sub, h4]
        linarith
      rw [hEq, div_self hne]
    have hrange : -(Real.pi / 2) < Real.arctan (Real.sqrt 2) -
        Real.arctan (3 - 2 * Real.sqrt 2) ∧
        Real.arctan (Real.sqrt 2) - Real.arctan (3 - 2 * Real.sqrt 2) < Real.pi / 2 := by
      constructor
      · linarith
      · linarith
    have hval : Real.arctan (Real.tan (Real.arctan (Real.sqrt 2) -
        Real.arctan (3 - 2 * Real.sqrt 2))) =
        Real.arctan (Real.sqrt 2) - Real.arctan (3 - 2 * Real.sqrt 2) :=
      Real.arctan_tan hrange.1 hrange.2
    rw [hv, Real.arctan_one] at hval
    linarith
  linarith

/-! ## 4. Constant brackets `K1 = 2·mm1/π`, `K2 = 8·mm2/π` -/

private theorem nb18_sol0_br : (0.551281:ℝ) ≤ sol0 ∧ sol0 ≤ 0.551291 := by
  have h := nb18_arccos13
  have hpi := nb18_pi
  have halpha := nb18_alpha
  unfold sol0
  constructor <;> nlinarith [h, halpha.1, halpha.2, hpi.1, hpi.2]

private theorem nb18_tau0_br : (1.540547:ℝ) ≤ tau0 ∧ tau0 ≤ 1.540753 := by
  obtain ⟨hlo, hhi⟩ := nb18_sol0_br
  have hpi := nb18_pi
  unfold tau0
  constructor <;> nlinarith [hlo, hhi, hpi.1, hpi.2, Real.pi_pos]

private theorem nb18_sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private theorem nb18_sqrt2_ne : Real.sqrt 2 ≠ 0 := fun h => by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [h] at hsq2
  norm_num at hsq2

private theorem nb18_k1 : (0.64425:ℝ) ≤ 2 * mm1 / Real.pi ∧ 2 * mm1 / Real.pi ≤ 0.64437 := by
  obtain ⟨slo, shi⟩ := nb18_sol0_br
  obtain ⟨tlo, thi⟩ := nb18_tau0_br
  have hpi := nb18_pi
  have hsq2 := nb18_sqrt2
  have tpos : (0:ℝ) < tau0 := lt_of_lt_of_le (by norm_num) tlo
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  unfold mm1
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  constructor
  · rw [le_div_iff₀ hpipos]
    rw [show (2:ℝ) * (sol0 * Real.sqrt 8 / tau0) = 2 * sol0 * Real.sqrt 8 / tau0 from by ring]
    rw [le_div_iff₀ tpos, hs8]
    nlinarith [slo, hsq2.1, hpi.2, thi]
  · rw [div_le_iff₀ hpipos]
    rw [show (2:ℝ) * (sol0 * Real.sqrt 8 / tau0) = 2 * sol0 * Real.sqrt 8 / tau0 from by ring]
    rw [div_le_iff₀ tpos, hs8]
    nlinarith [shi, hsq2.2, hpi.1, tlo]

private theorem nb18_k2 : (0.06468:ℝ) ≤ 8 * mm2 / Real.pi ∧ 8 * mm2 / Real.pi ≤ 0.06476 := by
  obtain ⟨slo, shi⟩ := nb18_sol0_br
  obtain ⟨tlo, thi⟩ := nb18_tau0_br
  have hpi := nb18_pi
  have hsq2 := nb18_sqrt2
  have tpos : (0:ℝ) < tau0 := lt_of_lt_of_le (by norm_num) tlo
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hs6 : (6:ℝ) * sol0 - Real.pi ≥ 0.16608 := by linarith
  have h6t : (0:ℝ) < 6 * tau0 := by linarith
  unfold mm2
  constructor
  · rw [le_div_iff₀ hpipos]
    rw [show (8:ℝ) * ((6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0)) =
      (8 * ((6 * sol0 - Real.pi) * Real.sqrt 2)) / (6 * tau0) from by ring]
    rw [le_div_iff₀ h6t]
    nlinarith [slo, hsq2.1, hpi.2, thi, hs6]
  · rw [div_le_iff₀ hpipos]
    rw [show (8:ℝ) * ((6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0)) =
      (8 * ((6 * sol0 - Real.pi) * Real.sqrt 2)) / (6 * tau0) from by ring]
    rw [div_le_iff₀ h6t]
    nlinarith [shi, hsq2.2, hpi.1, tlo, hs6]

/-! ## 5. The cell-3 corner kernel -/

/-- The `QZECFIC wt0 corner` kernel on the free coordinates. -/
noncomputable def pc3 (y4 y5 y6 : ℝ) : ℝ :=
  yOfX (gamma3fXDivSqrtdelta 1 1 1) 1 1 1 y4 y5 y6

/-- Explicit form of `gamma3fXDivSqrtdelta 1 1 1` (all three dihedral
coefficients `m4 = m5 = m6 = 1`). -/
theorem nb18_unfold (x1 x2 x3 x4 x5 x6 : ℝ) :
    gamma3fXDivSqrtdelta 1 1 1 x1 x2 x3 x4 x5 x6 =
      1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta x5 2 x4 2 x6 2 + solEulerXDivSqrtdelta x6 2 x5 2 x4 2 +
          solEulerXDivSqrtdelta x4 2 x6 2 x5 2) +
        (8 * mm2 / Real.pi) *
          (lfun (Real.sqrt x4 * 0.5) * dihXDivSqrtdeltaPosbranch x4 2 x6 2 x5 2 +
            lfun (Real.sqrt x5 * 0.5) * dihXDivSqrtdeltaPosbranch x5 2 x4 2 x6 2 +
            lfun (Real.sqrt x6 * 0.5) * dihXDivSqrtdeltaPosbranch x6 2 x5 2 x4 2) := by
  simp only [gamma3fXDivSqrtdelta, scalar6, uni, mk456, compose6, projX4, projX5, projX6,
    projY4, projY5, projY6, constant6, two6, rotate4, rotate5, rotate6,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- The kernel does not depend on `y1, y2, y3`. -/
theorem nb18_indep (y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX (gamma3fXDivSqrtdelta 1 1 1) y1 y2 y3 y4 y5 y6 = pc3 y4 y5 y6 := by
  simp only [pc3, yOfX, nb18_unfold, one_mul]

/-- Cyclic symmetry of the kernel in its three free coordinates. -/
theorem nb18_cycle (a b c : ℝ) : pc3 b c a = pc3 a b c := by
  simp only [pc3, yOfX, nb18_unfold]
  ring

private theorem nb18_matan2 : matan 2 = Real.arctan (Real.sqrt 2) / Real.sqrt 2 := by
  unfold matan
  rw [if_neg (show (2:ℝ) ≠ 0 by norm_num), if_pos (by norm_num : (0:ℝ) < 2)]

/-- Corner sol-slot exact value (`a = 8+6√2`, `Δ = 32`, matan-arg `(3−2√2)²`). -/
private theorem nb18_sol_corner :
    solEulerXDivSqrtdelta 4 2 4 2 4 2 =
      Real.arctan (3 - 2 * Real.sqrt 2) / (2 * Real.sqrt 2) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hD : deltaX 4 2 4 2 4 2 = 32 := by norm_num [deltaX]
  have hs32 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    rw [show (32:ℝ) = 16 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
      show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs4 : Real.sqrt 4 = 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpos : (0:ℝ) < 3 - 2 * Real.sqrt 2 := by nlinarith [nb18_sqrt2.1, nb18_sqrt2.2]
  simp only [solEulerXDivSqrtdelta]
  rw [hD]
  rw [show ((4:ℝ) * 2 * 4) = 32 by norm_num, hs32]
  simp only [hs4]
  rw [show (2 + 4 - 2:ℝ) = 4 by norm_num, show (4 + 4 - 4:ℝ) = 4 by norm_num,
    show (4 + 2 - 2:ℝ) = 4 by norm_num]
  have ha : (4:ℝ) * Real.sqrt 2 + 2 * 4 / 2 + Real.sqrt 2 * 4 / 2 + 2 * 4 / 2 =
      8 + 6 * Real.sqrt 2 := by linarith
  rw [ha]
  have hq : (3 - 2 * Real.sqrt 2) ^ 2 = 32 / (4 * (8 + 6 * Real.sqrt 2) ^ 2) := by
    have e1 : (8 + 6 * Real.sqrt 2) ^ 2 = 136 + 96 * Real.sqrt 2 := by
      ring_nf
      rw [hsq2]
      linarith
    have e2 : (3 - 2 * Real.sqrt 2) ^ 2 = 17 - 12 * Real.sqrt 2 := by
      ring_nf
      rw [hsq2]
      linarith
    rw [e1, e2, eq_div_iff (ne_of_gt (by nlinarith : (0:ℝ) < 4 * (136 + 96 * Real.sqrt 2)))]
    ring_nf
    rw [hsq2]
    linarith
  have hmatan : matan ((3 - 2 * Real.sqrt 2) ^ 2) =
      Real.arctan (3 - 2 * Real.sqrt 2) / (3 - 2 * Real.sqrt 2) := by
    have hp2 : (0:ℝ) < (3 - 2 * Real.sqrt 2) ^ 2 := by nlinarith [hpos]
    have hsqrt : Real.sqrt ((3 - 2 * Real.sqrt 2) ^ 2) = 3 - 2 * Real.sqrt 2 :=
      Real.sqrt_sq hpos.le
    unfold matan
    rw [if_neg (ne_of_gt hp2), if_pos hp2, hsqrt]
  rw [← hq, hmatan]
  have hden : (3 - 2 * Real.sqrt 2) * (8 + 6 * Real.sqrt 2) = 2 * Real.sqrt 2 := by
    ring_nf
    rw [hsq2]
    linarith
  field_simp [hden, hsq2]
  ring_nf
  rw [hsq2]
  linarith

/-- Corner dihedral-slot exact value (`Δ₄ = 16`, matan-argument `2`). -/
private theorem nb18_dih_corner :
    dihXDivSqrtdeltaPosbranch 4 2 4 2 4 2 =
      Real.arctan (Real.sqrt 2) / (4 * Real.sqrt 2) := by
  have hD4 : deltaX4 4 2 4 2 4 2 = 16 := by norm_num [deltaX4]
  have hD : deltaX 4 2 4 2 4 2 = 32 := by norm_num [deltaX]
  have hs16 : Real.sqrt (4 * 4) = 4 := by
    rw [show (4:ℝ) * 4 = 16 by norm_num, show (16:ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [hD4, hD]
  show Real.sqrt (4 * 4) / 16 * matan (4 * 4 * 32 / 16 ^ 2) =
    Real.arctan (Real.sqrt 2) / (4 * Real.sqrt 2)
  norm_num
  rw [nb18_matan2]
  field_simp

/-- **The corner value is exactly zero** (`pc3 2 2 2 = 0`). -/
private theorem nb18_corner_zero : pc3 2 2 2 = 0 := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs2 := nb18_sqrt2
  have halpha := nb18_alpha
  have hpi := nb18_pi
  have hsol := nb18_sol_corner
  have hdih := nb18_dih_corner
  have hpine : (Real.pi:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := nb18_sqrt2_ne
  have hsol0ne : sol0 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 0.551281) nb18_sol0_br.1)
  have htau0ne : tau0 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1.540547) nb18_tau0_br.1)
  simp only [pc3, yOfX, nb18_unfold]
  norm_num
  simp only [nb11_lfun_one, one_mul]
  rw [hsol, hdih]
  simp only [nb18_beta]
  have hsol0 : sol0 = 2 * Real.pi - 6 * Real.arctan (Real.sqrt 2) := by
    unfold sol0
    rw [nb18_arccos13]
    ring
  have htau0 : tau0 = 120 * Real.arctan (Real.sqrt 2) - 36 * Real.pi := by
    unfold tau0
    rw [hsol0]
    ring
  unfold mm1 mm2
  rw [hsol0, htau0]
  rw [show Real.sqrt 8 = 2 * Real.sqrt 2 from by
    rw [show (8:ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring_nf
  have ht0ne : (120:ℝ) * Real.arctan (Real.sqrt 2) - 36 * Real.pi ≠ 0 :=
    ne_of_gt (by nlinarith [halpha.1, halpha.2, hpi.1, hpi.2])
  have hD6 : (720:ℝ) * Real.arctan (Real.sqrt 2) - 216 * Real.pi ≠ 0 :=
    ne_of_gt (by nlinarith [halpha.1, halpha.2, hpi.1, hpi.2])
  have htf : (-(Real.pi * 36) + Real.arctan (Real.sqrt 2) * 120) ≠ 0 := by
    rw [show (-(Real.pi * 36) + Real.arctan (Real.sqrt 2) * 120) =
      120 * Real.arctan (Real.sqrt 2) - 36 * Real.pi from by ring]
    exact ht0ne
  have hD6f : (-(Real.pi * 216) + Real.arctan (Real.sqrt 2) * 720) ≠ 0 := by
    rw [show (-(Real.pi * 216) + Real.arctan (Real.sqrt 2) * 720) =
      720 * Real.arctan (Real.sqrt 2) - 216 * Real.pi from by ring]
    exact hD6
  field_simp [hpine, hsqrt2ne, htf, hD6f]
  ring

/-! ## 6. Generic derivative chains -/

/-- Sol-slot chain: `w ↦ matan (Δf w / (4·af w²)) / af w`. -/
private theorem nb18_hasDerivAt_sol {Δf af : ℝ → ℝ} {t δ κ : ℝ}
    (hΔ : HasDerivAt Δf δ t) (ha : HasDerivAt af κ t) (hapos : 0 < af t)
    (harg : 0 < Δf t / (4 * (af t * af t))) :
    HasDerivAt (fun s => matan (Δf s / (4 * (af s * af s))) / af s)
      (matanDerivPos (Δf t / (4 * (af t * af t))) *
          (δ / (4 * (af t * af t)) - Δf t * κ / (2 * af t ^ 3)) / af t
        - matan (Δf t / (4 * (af t * af t))) * κ / af t ^ 2) t := by
  have hafpos2 : (0:ℝ) < 4 * (af t * af t) := by nlinarith [hapos]
  have hd : HasDerivAt (fun s : ℝ => 4 * (af s * af s)) (4 * (κ * af t + af t * κ)) t := by
    refine ((ha.mul ha).const_mul (4:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [Pi.mul_apply]
  have hin : HasDerivAt (fun s => Δf s / (4 * (af s * af s)))
      (δ / (4 * (af t * af t)) - Δf t * κ / (2 * af t ^ 3)) t := by
    refine (hΔ.fun_div hd (ne_of_gt hafpos2)).congr_deriv ?_
    have hDp : (4:ℝ) * (af t * af t) = 4 * af t ^ 2 := by ring
    rw [hDp]
    field_simp
    ring
  have hcomp : HasDerivAt (fun s => matan (Δf s / (4 * (af s * af s))))
      (matanDerivPos (Δf t / (4 * (af t * af t))) *
        (δ / (4 * (af t * af t)) - Δf t * κ / (2 * af t ^ 3))) t :=
    HasDerivAt.comp (h := fun s => Δf s / (4 * (af s * af s))) (x := t)
      (nb13_hasDerivAt_matan_pos harg) hin
  refine (hcomp.fun_div ha (ne_of_gt hapos)).congr_deriv ?_
  field_simp

/-- Dihedral-slot chain: `w ↦ Wf w · matan (Gf w)`. -/
private theorem nb18_hasDerivAt_dih {Wf Gf : ℝ → ℝ} {t ω γ : ℝ}
    (hW : HasDerivAt Wf ω t) (hG : HasDerivAt Gf γ t) (hGpos : 0 < Gf t) :
    HasDerivAt (fun s => Wf s * matan (Gf s))
      (ω * matan (Gf t) + Wf t * matanDerivPos (Gf t) * γ) t := by
  have hcomp : HasDerivAt (fun s => matan (Gf s)) (matanDerivPos (Gf t) * γ) t :=
    HasDerivAt.comp (h := Gf) (x := t) (nb13_hasDerivAt_matan_pos hGpos) hG
  exact (hW.fun_mul hcomp).congr_deriv (by ring)

/-! ## 7. Box and ingredient brackets -/

/-- Squared-coordinate box. -/
private theorem nb18_box2 {y : ℝ} (h : 2 ≤ y) (h' : y ≤ 2.01) :
    (4:ℝ) ≤ y * y ∧ y * y ≤ 4.0401 := by
  constructor <;> nlinarith

/-- Shared `deltaX` slice bounds: `Δ(w) = −2w⁴ + (4u+4v−uv)w² − 2(u−v)²`. -/
private theorem nb18_Delta_br (u v s : ℝ) (hu : 4 ≤ u) (hu' : u ≤ 4.0401)
    (hv : 4 ≤ v) (hv' : v ≤ 4.0401) (hs : 2 ≤ s) (hs' : s ≤ 2.01) :
    (31.669:ℝ) ≤
      -2 * ((s * s) * (s * s)) + (4 * u + 4 * v - u * v) * (s * s) - 2 * (u - v) ^ 2 ∧
      -2 * ((s * s) * (s * s)) + (4 * u + 4 * v - u * v) * (s * s) - 2 * (u - v) ^ 2 ≤
      32.0005 := by
  have hs2 := nb18_box2 hs hs'
  -- coefficient c = 4u+4v-uv = 16 - (u-4)(v-4)
  have hprod : (0:ℝ) ≤ (u - 4) * (v - 4) := by nlinarith
  have hprod2 : (u - 4) * (v - 4) ≤ 0.0401 * 0.0401 :=
    mul_le_mul_of_nonneg (by linarith) (by linarith) (by linarith) (by linarith)
  have hc1 : (4:ℝ) * u + 4 * v - u * v ≤ 16 := by
    have hid : (4:ℝ) * u + 4 * v - u * v = 16 - (u - 4) * (v - 4) := by ring
    rw [hid]; linarith
  have hc2 : (15.9983:ℝ) ≤ 4 * u + 4 * v - u * v := by
    have hid : (4:ℝ) * u + 4 * v - u * v = 16 - (u - 4) * (v - 4) := by ring
    rw [hid]; nlinarith [hprod2]
  have hc2' : (4:ℝ) * u + 4 * v - u * v - 2 * (s * s) ≥ 7.9181 := by
    nlinarith [hc2, hs2.2]
  have huv2 : (0:ℝ) ≤ (u - v) ^ 2 := by positivity
  have huv2' : (u - v) ^ 2 ≤ 0.0401 * 0.0401 := by nlinarith [hu, hu', hv, hv']
  have hsq4 : (0:ℝ) ≤ (s * s - 4) * (s * s - 4) := by nlinarith [hs2.1]
  constructor
  · -- E = t·(c - 2t) - 2(u-v)²  with t = s²
    have hsplit : -2 * ((s * s) * (s * s)) + (4 * u + 4 * v - u * v) * (s * s)
        - 2 * (u - v) ^ 2 =
        (s * s) * ((4 * u + 4 * v - u * v) - 2 * (s * s)) - 2 * (u - v) ^ 2 := by ring
    have hpair : (31.6724:ℝ) ≤ (s * s) * ((4 * u + 4 * v - u * v) - 2 * (s * s)) := by
      have hc2'2 : (7.9181:ℝ) ≤ 4 * u + 4 * v - u * v - 2 * (s * s) := hc2'
      have h4 : (31.6724:ℝ) = 4 * 7.9181 := by norm_num
      rw [h4]
      exact mul_le_mul_of_nonneg hs2.1 hc2'2 (by norm_num)
        (le_of_lt (by linarith [hc2'] : (0:ℝ) < 4 * u + 4 * v - u * v - 2 * (s * s)))
    nlinarith [hpair, huv2']
  · -- E = 32 - 2(t-4)² - t·(16-c) - 2(u-v)²
    have hsplit : -2 * ((s * s) * (s * s)) + (4 * u + 4 * v - u * v) * (s * s)
        - 2 * (u - v) ^ 2 =
        32 - 2 * (s * s - 4) * (s * s - 4) - (s * s) * (16 - (4 * u + 4 * v - u * v))
          - 2 * (u - v) ^ 2 := by
      ring
    have hnon : (0:ℝ) ≤ s * s := by linarith [hs2.1]
    have hnon2 : (0:ℝ) ≤ 16 - (4 * u + 4 * v - u * v) := by linarith [hc1]
    have hpair : (s * s) * (16 - (4 * u + 4 * v - u * v)) ≤ 4.0401 * 0.0401 := by
      have hle : 16 - (4 * u + 4 * v - u * v) ≤ 0.0401 := by nlinarith [hprod2]
      have h3 : (s * s) * (16 - (4 * u + 4 * v - u * v)) ≤ (s * s) * 0.0401 :=
        mul_le_mul_of_nonneg_left hle hnon
      have h4 : (s * s) * 0.0401 ≤ 4.0401 * 0.0401 :=
        mul_le_mul_of_nonneg_right hs2.2 (by norm_num)
      linarith [h3, h4]
    nlinarith [hnon, hnon2, hsq4, huv2, hpair]

/-- Shared `deltaX` slice derivative bounds: `δ(w) = −8w³ + (4u+4v−uv)·2w`. -/
private theorem nb18_ds_br (u v s : ℝ) (hu : 4 ≤ u) (hu' : u ≤ 4.0401)
    (hv : 4 ≤ v) (hv' : v ≤ 4.0401) (hs : 2 ≤ s) (hs' : s ≤ 2.01) :
    (-0.6513:ℝ) ≤ -8 * s * (s * s) + (4 * u + 4 * v - u * v) * (2 * s) ∧
    -8 * s * (s * s) + (4 * u + 4 * v - u * v) * (2 * s) ≤ 0 := by
  have hs2 := nb18_box2 hs hs'
  have hprod : (0:ℝ) ≤ (u - 4) * (v - 4) := by nlinarith
  have hprod2 : (u - 4) * (v - 4) ≤ 0.0401 * 0.0401 :=
    mul_le_mul_of_nonneg (by linarith) (by linarith) (by linarith) (by linarith)
  have hc1 : (4:ℝ) * u + 4 * v - u * v ≤ 16 := by
    have hid : (4:ℝ) * u + 4 * v - u * v = 16 - (u - 4) * (v - 4) := by ring
    rw [hid]; linarith
  have hc2 : (15.9983:ℝ) ≤ 4 * u + 4 * v - u * v := by
    have hid : (4:ℝ) * u + 4 * v - u * v = 16 - (u - 4) * (v - 4) := by ring
    rw [hid]; nlinarith [hprod2]
  have hsplit : -8 * s * (s * s) + (4 * u + 4 * v - u * v) * (2 * s) =
      s * (2 * (4 * u + 4 * v - u * v) - 8 * (s * s)) := by ring
  have hmid1 : (2:ℝ) * (4 * u + 4 * v - u * v) - 8 * (s * s) ≤ 0 := by linarith [hc1, hs2.1]
  have hmid2 : (2:ℝ) * (4 * u + 4 * v - u * v) - 8 * (s * s) ≥ -(0.3242) := by
    nlinarith [hc2, hs2.2]
  rw [hsplit]
  have hphi : s * (2 * (4 * u + 4 * v - u * v) - 8 * (s * s)) ≤ 0 := by
    have h1q : s * (2 * (4 * u + 4 * v - u * v) - 8 * (s * s)) ≤ s * 0 :=
      mul_le_mul_of_nonneg_left hmid1 (by linarith : (0:ℝ) ≤ s)
    linarith [h1q, mul_zero s]
  constructor
  · -- δ = 2s·(c − 4s²) ≥ 2·2.01·(15.998392 − 16.1604) = −0.6512721
    have hc4 : (4:ℝ) * (s * s) ≤ 16.1604 := by linarith [hs2.2]
    have hc3 : (15.998391:ℝ) ≤ 4 * u + 4 * v - u * v := by
      have hid : (4:ℝ) * u + 4 * v - u * v = 16 - (u - 4) * (v - 4) := by ring
      rw [hid]
      have h3 : (0.0401:ℝ) * 0.0401 ≤ 0.001609 := by norm_num
      have h4 : (16:ℝ) - 0.001609 ≤ 16 - (u - 4) * (v - 4) := by linarith [hprod2]
      linarith
    have hlow : (4:ℝ) * u + 4 * v - u * v - 4 * (s * s) ≥ -(0.162009:ℝ) := by
      linarith [hc3, hc4]
    rw [show s * (2 * (4 * u + 4 * v - u * v) - 8 * (s * s)) =
      2 * s * ((4 * u + 4 * v - u * v) - 4 * (s * s)) from by ring]
    have h1 : 2 * s * -(0.162009:ℝ) ≤ 2 * s * ((4 * u + 4 * v - u * v) - 4 * (s * s)) :=
      mul_le_mul_of_nonneg_left hlow (by linarith : (0:ℝ) ≤ 2 * s)
    have h2 : (2:ℝ) * 2.01 * -(0.162009:ℝ) ≤ 2 * s * -(0.162009:ℝ) := by linarith [hs']
    have h3 : (-(0.6513:ℝ)) ≤ (2:ℝ) * 2.01 * -(0.162009:ℝ) := by norm_num
    linarith [h3, h2, h1]
  · linarith [hphi, mul_zero s]

/-- a-slice bracket for the `A`/`C` sol slots (`ya` moves with the axis). -/
private theorem nb18_aA_br (ya yb s : ℝ) (hya : 2 ≤ ya) (hya' : ya ≤ 2.01)
    (hyb : 2 ≤ yb) (hyb' : yb ≤ 2.01) (hs : 2 ≤ s) (hs' : s ≤ 2.01) :
    (16.4569:ℝ) ≤
      ((ya + Real.sqrt 2) / 2) * (s * s) + (ya * ya / 2 + ya * Real.sqrt 2) * s +
        Real.sqrt 2 * (ya * ya - yb * yb) / 2 ∧
    ((ya + Real.sqrt 2) / 2) * (s * s) + (ya * ya / 2 + ya * Real.sqrt 2) * s +
      Real.sqrt 2 * (ya * ya - yb * yb) / 2 ≤ 16.7194 := by
  have h2lo : (1.41421356:ℝ) ≤ Real.sqrt 2 := nb18_sqrt2.1
  have h2hi : Real.sqrt 2 ≤ 1.4142136 := nb18_sqrt2.2
  have hsumlo : (2:ℝ) + Real.sqrt 2 ≤ ya + Real.sqrt 2 := by linarith
  have hsumhi : ya + Real.sqrt 2 ≤ (2.01:ℝ) + Real.sqrt 2 := by linarith
  have hs2lo : (4:ℝ) ≤ s * s := by nlinarith
  have hs2hi : s * s ≤ 4.0401 := by nlinarith
  have hyasq : ya * ya ≤ 4.0401 := by nlinarith
  have hybsq : yb * yb ≤ 4.0401 := by nlinarith
  have hyasqlo : (4:ℝ) ≤ ya * ya := by nlinarith [hya]
  have hybsqlo : (4:ℝ) ≤ yb * yb := by nlinarith [hyb]
  have hA1lo : ya * ya / 2 + ya * Real.sqrt 2 ≥ 4 / 2 + 2 * 1.41421356 := by
    nlinarith [hya, hya', h2lo]
  have hA1hi : ya * ya / 2 + ya * Real.sqrt 2 ≤ 4.0401 / 2 + 2.01 * 1.4142136 := by
    nlinarith [hya, hya', hyasq, h2hi]
  have hT1lo : ((ya + Real.sqrt 2) / 2) * (s * s) ≥ (2 + 1.41421356) * 4 / 2 := by
    have hprod : (2 + 1.41421356:ℝ) * 4 ≤ (ya + Real.sqrt 2) * (s * s) :=
      mul_le_mul_of_nonneg (by linarith [hsumlo, h2lo]) hs2lo (le_of_lt (by norm_num))
        (by nlinarith : (0:ℝ) ≤ s * s)
    nlinarith [hprod]
  have hT1hi : ((ya + Real.sqrt 2) / 2) * (s * s) ≤ (2.01 + 1.4142136) * 4.0401 / 2 := by
    have hprod : (ya + Real.sqrt 2) * (s * s) ≤ (2.01 + 1.4142136:ℝ) * 4.0401 :=
      mul_le_mul_of_nonneg (by linarith [hsumhi, h2hi]) hs2hi (le_of_lt (by linarith))
        (by norm_num : (0:ℝ) ≤ 4.0401)
    nlinarith [hprod]
  have hT2lo : (ya * ya / 2 + ya * Real.sqrt 2) * s ≥ (4 / 2 + 2 * 1.41421356) * 2 := by
    have c1 : (4 / 2 + 2 * 1.41421356:ℝ) * 2 ≤ (4 / 2 + 2 * 1.41421356) * s :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    have c2 : (4 / 2 + 2 * 1.41421356:ℝ) * s ≤ (ya * ya / 2 + ya * Real.sqrt 2) * s :=
      mul_le_mul_of_nonneg_right hA1lo (by linarith : (0:ℝ) ≤ s)
    linarith [c1, c2]
  have hT2hi : (ya * ya / 2 + ya * Real.sqrt 2) * s ≤ (4.0401 / 2 + 2.01 * 1.4142136) * 2.01 := by
    have c1 : (ya * ya / 2 + ya * Real.sqrt 2) * s ≤ (ya * ya / 2 + ya * Real.sqrt 2) * 2.01 :=
      mul_le_mul_of_nonneg_left hs' (by nlinarith [hya, h2lo])
    have c2 : (ya * ya / 2 + ya * Real.sqrt 2) * 2.01 ≤ (4.0401 / 2 + 2.01 * 1.4142136) * 2.01 :=
      mul_le_mul_of_nonneg_right hA1hi (le_of_lt (by norm_num))
    linarith [c1, c2]
  have hT3lo : Real.sqrt 2 * (ya * ya - yb * yb) / 2 ≥ -(0.0284:ℝ) := by
    nlinarith [h2lo, h2hi, hyasq, hybsq, hyasqlo, hybsqlo]
  have hT3hi : Real.sqrt 2 * (ya * ya - yb * yb) / 2 ≤ 0.0284 := by
    nlinarith [h2lo, h2hi, hyasq, hybsq, hyasqlo, hybsqlo]
  constructor
  · nlinarith [hT1lo, hT2lo, hT3lo]
  · nlinarith [hT1hi, hT2hi, hT3hi]

/-- `aB`-slice bracket (the `x4`-slot moves in position 5). -/
private theorem nb18_aB_br (y5 y6 s : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (hs : 2 ≤ s) (hs' : s ≤ 2.01) :
    (16.4569:ℝ) ≤
      Real.sqrt 2 * (y6 * y5) + y6 * (y5 * y5 / 2) +
        Real.sqrt 2 * ((y5 * y5) + (y6 * y6) - (s * s)) / 2 + y5 * ((y6 * y6) / 2) ∧
    Real.sqrt 2 * (y6 * y5) + y6 * (y5 * y5 / 2) +
      Real.sqrt 2 * ((y5 * y5) + (y6 * y6) - (s * s)) / 2 + y5 * ((y6 * y6) / 2) ≤
      16.7194 := by
  have h2lo : (1.41421356:ℝ) ≤ Real.sqrt 2 := nb18_sqrt2.1
  have h2hi : Real.sqrt 2 ≤ 1.4142136 := nb18_sqrt2.2
  have hy5sq : y5 * y5 ≤ 4.0401 := by nlinarith
  have hy6sq : y6 * y6 ≤ 4.0401 := by nlinarith
  have hy5y6 : y6 * y5 ≤ 2.01 * 2.01 := by nlinarith
  have hy5y6lo : (4:ℝ) ≤ y6 * y5 := by nlinarith
  have hs2 := nb18_box2 hs hs'
  have hT1lo : Real.sqrt 2 * (y6 * y5) ≥ 1.41421356 * 4 :=
    mul_le_mul_of_nonneg h2lo hy5y6lo (le_of_lt (by norm_num)) (by nlinarith : (0:ℝ) ≤ y6 * y5)
  have hT1hi : Real.sqrt 2 * (y6 * y5) ≤ 1.4142136 * (2.01 * 2.01) :=
    mul_le_mul_of_nonneg h2hi hy5y6 (le_of_lt (by norm_num)) (le_of_lt (by norm_num))
  have hT3faclo : (3.9599:ℝ) ≤ (y5 * y5) + (y6 * y6) - (s * s) := by
    nlinarith [hy5, hy6, hy5sq, hy6sq, hs2.2]
  have hT3fachi : (y5 * y5) + (y6 * y6) - (s * s) ≤ 4.0802 := by
    linarith [hy5sq, hy6sq, hs2.1]
  constructor
  · nlinarith [hT1lo, hT3faclo, hy5, hy5', hy6, hy6', hs, hs', h2lo, h2hi]
  · nlinarith [hT1hi, hT3fachi, hy5, hy5', hy6, hy6', hs, hs', h2lo, h2hi]

/-- kA-bracket for the `A`/`C` sol slots. -/
private theorem nb18_kA_br (ya s : ℝ) (hya : 2 ≤ ya) (hya' : ya ≤ 2.01)
    (hs : 2 ≤ s) (hs' : s ≤ 2.01) :
    (11.6568:ℝ) ≤ (ya + Real.sqrt 2) * s + ya * ya / 2 + ya * Real.sqrt 2 ∧
    (ya + Real.sqrt 2) * s + ya * ya / 2 + ya * Real.sqrt 2 ≤ 11.7454 := by
  have h2lo : (1.41421356:ℝ) ≤ Real.sqrt 2 := nb18_sqrt2.1
  have h2hi : Real.sqrt 2 ≤ 1.4142136 := nb18_sqrt2.2
  have hyasq : ya * ya ≤ 4.0401 := by nlinarith
  constructor
  · nlinarith [hya, hya', hs, h2lo]
  · nlinarith [hya, hya', hs', h2hi, hyasq]

/-- θ-atom bracket (sol-slot matan argument). -/
private theorem nb18_theta_br {D a : ℝ} (hD1 : (31.669:ℝ) ≤ D) (hD2 : D ≤ 32.0005)
    (ha1 : (16.4569:ℝ) ≤ a) (ha2 : a ≤ 16.7194) :
    (0.02832:ℝ) ≤ D / (4 * (a * a)) ∧ D / (4 * (a * a)) ≤ 0.02954 := by
  have hapos : (0:ℝ) < 4 * (a * a) := by nlinarith [ha1]
  constructor
  · rw [le_div_iff₀ hapos]
    nlinarith [hD1, ha2]
  · rw [div_le_iff₀ hapos]
    nlinarith [hD2, ha1]

/-- Mt bracket via the NliBanks12 quadratic bracket. -/
private theorem nb18_mt_br {θ : ℝ} (hθ1 : (0.02832:ℝ) ≤ θ) (hθ2 : θ ≤ 0.02954) :
    (0.98992:ℝ) ≤ matan θ ∧ matan θ ≤ 0.99080 := by
  have hθpos : (0:ℝ) < θ := lt_of_lt_of_le (by norm_num) hθ1
  obtain ⟨hm1, hm2⟩ := nb12_matan_pos_bracket hθpos
  constructor
  · have h1 : (0.98992:ℝ) ≤ 1 - θ / 3 := by nlinarith [hθ2]
    exact le_trans h1 hm1
  · calc matan θ ≤ 1 - θ / 3 + θ ^ 2 / 5 := hm2
      _ ≤ 1 - 0.02832 / 3 + (0.02954:ℝ) ^ 2 / 5 := by nlinarith [hθ1, hθ2]
      _ ≤ 0.99080 := by norm_num

/-- Mp-bracket via the order-5 atan series bounds at `√θ`. -/
private theorem nb18_mp_br {θ : ℝ} (hθ1 : (0.02832:ℝ) ≤ θ) (hθ2 : θ ≤ 0.02954) :
    -(0.344:ℝ) ≤ matanDerivPos θ ∧ matanDerivPos θ ≤ -(0.3189:ℝ) := by
  have hθpos : (0:ℝ) < θ := lt_of_lt_of_le (by norm_num) hθ1
  have hs0 : (0.168285:ℝ) ≤ Real.sqrt θ := by
    have h1 : (0.168285:ℝ) ^ 2 ≤ 0.02832 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (0.168285:ℝ))]
    exact Real.sqrt_le_sqrt (h1.trans hθ1)
  have hs1 : Real.sqrt θ ≤ 0.17188 := by
    have h1 : (0.02954:ℝ) ≤ (0.17188:ℝ) ^ 2 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (0.17188:ℝ))]
    exact Real.sqrt_le_sqrt (hθ2.trans h1)
  have hwpos : (0:ℝ) < Real.sqrt θ := Real.sqrt_pos.mpr hθpos
  have hs2p : (0:ℝ) ≤ Real.sqrt θ * Real.sqrt θ := mul_nonneg (le_of_lt hwpos) (le_of_lt hwpos)
  have hs2 : Real.sqrt θ * Real.sqrt θ = θ := by
    rw [← pow_two]
    exact Real.sq_sqrt hθpos.le
  -- s² / s³ / s⁵ / s⁷ brackets against the numeric anchors
  have hsq0 : (0.168285:ℝ) * (0.168285:ℝ) ≤ Real.sqrt θ * Real.sqrt θ :=
    mul_le_mul_of_nonneg hs0 hs0 (by norm_num) (le_of_lt hwpos)
  have hsq1 : Real.sqrt θ * Real.sqrt θ ≤ 0.17188 * 0.17188 :=
    mul_le_mul_of_nonneg hs1 hs1 (le_of_lt hwpos) (by norm_num)
  have h3lo : (0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ) ≤
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ := by
    have e1 : (0.168285:ℝ) * (0.168285 * 0.168285) ≤
        (0.168285:ℝ) * (Real.sqrt θ * Real.sqrt θ) :=
      mul_le_mul_of_nonneg_left hsq0 (by norm_num : (0:ℝ) ≤ (0.168285:ℝ))
    have e2 : (0.168285:ℝ) * (Real.sqrt θ * Real.sqrt θ) ≤
        Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) :=
      mul_le_mul_of_nonneg_right hs0 hs2p
    linarith [e1, e2]
  have h3hi : Real.sqrt θ * Real.sqrt θ * Real.sqrt θ ≤
      0.17188 * 0.17188 * 0.17188 := by
    have e1 : Real.sqrt θ * Real.sqrt θ * Real.sqrt θ ≤
        (0.17188:ℝ) * (0.17188:ℝ) * Real.sqrt θ :=
      mul_le_mul_of_nonneg_right hsq1 (le_of_lt hwpos)
    have e2 : (0.17188:ℝ) * (0.17188:ℝ) * Real.sqrt θ ≤
        (0.17188:ℝ) * (0.17188:ℝ) * (0.17188:ℝ) :=
      mul_le_mul_of_nonneg_left hs1 (by norm_num)
    linarith [e1, e2]
  have hp2 : (0:ℝ) ≤ Real.sqrt θ * Real.sqrt θ * Real.sqrt θ := by
    have h2p : (0:ℝ) < Real.sqrt θ * Real.sqrt θ := mul_pos hwpos hwpos
    nlinarith [h2p, hwpos]
  have h5lo : (0:ℝ) ≤ Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
      (Real.sqrt θ * Real.sqrt θ) := mul_nonneg hp2 hs2p
  have h5lo2 : (0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ) *
      ((0.168285:ℝ) * (0.168285:ℝ)) ≤
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) :=
    mul_le_mul_of_nonneg h3lo hsq0 (by norm_num) hs2p
  have h5hi : Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) ≤
      0.17188 * 0.17188 * 0.17188 * (0.17188 * 0.17188) :=
    mul_le_mul_of_nonneg h3hi hsq1 hp2 (by norm_num)
  have h7hi : Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) *
      (Real.sqrt θ * Real.sqrt θ) ≤
      0.17188 * 0.17188 * 0.17188 * (0.17188 * 0.17188) * (0.17188 * 0.17188) :=
    mul_le_mul_of_nonneg h5hi hsq1 h5lo (by norm_num)
  -- atan series bounds (nb12 order-5)
  have hatlo : Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3 ≤
      Real.arctan (Real.sqrt θ) := by
    have h := nb12_arctan_ge_sub hwpos.le
    have hshape : Real.sqrt θ - Real.sqrt θ ^ 3 / 3 =
        Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3 := by ring
    rw [hshape] at h
    exact h
  have hathi : Real.arctan (Real.sqrt θ) ≤
      Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3 +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) / 5 := by
    have h := nb12_arctan_le_sub5 hwpos.le
    have hshape : Real.sqrt θ - Real.sqrt θ ^ 3 / 3 + Real.sqrt θ ^ 5 / 5 =
        Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3 +
          Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) / 5 := by
      ring
    rw [hshape] at h
    exact h
  -- θ·s³ = s⁵ and θ·s⁵ = s⁷ rewriting facts
  have hθs3 : θ * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) =
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) := by
    rw [hs2]; ring
  have hθs5 : θ * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
      (Real.sqrt θ * Real.sqrt θ)) =
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) *
        (Real.sqrt θ * Real.sqrt θ) := by
    rw [hs2]; ring
  -- distributed-shape stage facts
  have hA2 : (1 + θ) * Real.sqrt θ =
      Real.sqrt θ + Real.sqrt θ * Real.sqrt θ * Real.sqrt θ := by
    rw [show (1 + θ) * Real.sqrt θ = Real.sqrt θ + θ * Real.sqrt θ by ring, hs2]
  have hA3 : (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) =
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) := by
    rw [show (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) =
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ +
        θ * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) by ring, hθs3]
  have hA5 : (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
      (Real.sqrt θ * Real.sqrt θ)) =
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) *
          (Real.sqrt θ * Real.sqrt θ) := by
    rw [show (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
      (Real.sqrt θ * Real.sqrt θ)) =
      Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) +
        θ * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ)) by
      ring, hθs5]
  unfold matanDerivPos
  have hden : (0:ℝ) < 2 * Real.sqrt θ ^ 3 * (1 + θ) := by
    rw [pow_succ]
    nlinarith [hwpos, hs2p]
  -- num bounds (num = s − (1+θ)·atan s)
  have hm1 : (1 + θ) * Real.sqrt θ - (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) / 3 ≤
      (1 + θ) * Real.arctan (Real.sqrt θ) := by
    have h : (1 + θ) * (Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3) ≤
        (1 + θ) * Real.arctan (Real.sqrt θ) :=
      mul_le_mul_of_nonneg_left hatlo (by linarith : (0:ℝ) ≤ 1 + θ)
    have hd : (1 + θ) * (Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3) =
        (1 + θ) * Real.sqrt θ - (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) / 3 := by
      ring
    rw [hd] at h
    exact h
  have hnumub : Real.sqrt θ - (1 + θ) * Real.arctan (Real.sqrt θ) ≤
      -(2 / 3) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ)) +
        (0.17188:ℝ) * (0.17188:ℝ) * (0.17188:ℝ) *
          ((0.17188:ℝ) * (0.17188:ℝ)) / 3 := by
    linarith [hm1, hA2, hA3, h3lo, h5hi]
  have hm2 : (1 + θ) * Real.arctan (Real.sqrt θ) ≤
      (1 + θ) * Real.sqrt θ - (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) / 3 +
        (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
          (Real.sqrt θ * Real.sqrt θ)) / 5 := by
    have h0 : (1 + θ) * Real.arctan (Real.sqrt θ) ≤
        (1 + θ) * (Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3 +
          Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) / 5) :=
      mul_le_mul_of_nonneg_left hathi (by linarith : (0:ℝ) ≤ 1 + θ)
    have hd : (1 + θ) * (Real.sqrt θ - Real.sqrt θ * Real.sqrt θ * Real.sqrt θ / 3 +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ) / 5) =
        (1 + θ) * Real.sqrt θ - (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) / 3 +
          (1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
            (Real.sqrt θ * Real.sqrt θ)) / 5 := by
      ring
    rw [hd] at h0
    exact h0
  have hnumlb : -(2 / 3) * ((0.17188:ℝ) * (0.17188:ℝ) * (0.17188:ℝ)) +
      (2 / 15) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ) *
        ((0.168285:ℝ) * (0.168285:ℝ))) -
      (0.17188:ℝ) * (0.17188:ℝ) * (0.17188:ℝ) * ((0.17188:ℝ) * (0.17188:ℝ)) *
        ((0.17188:ℝ) * (0.17188:ℝ)) / 5 ≤
      Real.sqrt θ - (1 + θ) * Real.arctan (Real.sqrt θ) := by
    linarith [hm2, hA2, hA3, hA5, h3hi, h5lo2, h7hi]
  -- den = 2·s³·(1+θ) = 2·(s³ + s⁵) exactly
  have hdenform : 2 * Real.sqrt θ ^ 3 * (1 + θ) =
      2 * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ)) := by
    rw [show Real.sqrt θ ^ 3 = Real.sqrt θ * Real.sqrt θ * Real.sqrt θ by ring, hs2]
    ring
  constructor
  · rw [le_div_iff₀ hden, hdenform]
    have hx : -(0.344:ℝ) * (2 * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ))) =
      -(0.688:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) -
        (0.688:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
          (Real.sqrt θ * Real.sqrt θ)) := by ring
    rw [hx]
    have hC3 : (0.688:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) ≥
        (0.688:ℝ) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ)) :=
      mul_le_mul_of_nonneg_left h3lo (by norm_num)
    have hD3 : (0.688:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
        (Real.sqrt θ * Real.sqrt θ)) ≥
        (0.688:ℝ) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ) *
          ((0.168285:ℝ) * (0.168285:ℝ))) :=
      mul_le_mul_of_nonneg_left h5lo2 (by norm_num)
    have e3 : -(0.688:ℝ) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ)) -
        (0.688:ℝ) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ) *
          ((0.168285:ℝ) * (0.168285:ℝ))) ≤
      -(2 / 3) * ((0.17188:ℝ) * (0.17188:ℝ) * (0.17188:ℝ)) +
        (2 / 15) * ((0.168285:ℝ) * (0.168285:ℝ) * (0.168285:ℝ) *
          ((0.168285:ℝ) * (0.168285:ℝ))) -
        (0.17188:ℝ) * (0.17188:ℝ) * (0.17188:ℝ) * ((0.17188:ℝ) * (0.17188:ℝ)) *
          ((0.17188:ℝ) * (0.17188:ℝ)) / 5 := by norm_num
    linarith [hC3, hD3, e3, hnumlb]
  · rw [div_le_iff₀ hden, hdenform]
    have hx : -(0.3189:ℝ) * (2 * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ +
        Real.sqrt θ * Real.sqrt θ * Real.sqrt θ * (Real.sqrt θ * Real.sqrt θ))) =
      -(0.6378:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) -
        (0.6378:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ *
          (Real.sqrt θ * Real.sqrt θ)) := by ring
    rw [hx, ← hθs3]
    have hθ2le : θ ≤ 0.0297247 := by linarith [hθ2]
    have hθb : θ * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) ≤
        (0.0297247:ℝ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) :=
      mul_le_mul_of_nonneg_right hθ2le hp2
    have h2n : Real.sqrt θ - (1 + θ) * Real.arctan (Real.sqrt θ) ≤
        -(2 / 3) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ) +
          ((1 + θ) * (Real.sqrt θ * Real.sqrt θ * Real.sqrt θ)) / 3 := by
      linarith [hm1, hA2]
    rw [hA3] at h2n
    rw [← hθs3] at h2n
    linarith [h2n, hθb, hp2]

/-- MU/MPU brackets for the dihedral matan atom `G ∈ [1.8831, 2.0409]`. -/
private theorem nb18_mu_mpu_br {G : ℝ} (hG1 : (1.8831:ℝ) ≤ G) (hG2 : G ≤ 2.0409) :
    (0.65860:ℝ) ≤ matan G ∧ matan G ≤ 0.69990 ∧
    -(0.096:ℝ) ≤ matanDerivPos G ∧ matanDerivPos G ≤ -(0.079:ℝ) := by
  have hGpos : (0:ℝ) < G := lt_of_lt_of_le (by norm_num) hG1
  have hG2pos : (0:ℝ) < 1 + G := by linarith
  -- √G anchors
  have hsGlo : (1.3722:ℝ) ≤ Real.sqrt G := by
    have h1 : (1.3722:ℝ) ^ 2 ≤ 1.8831 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1.3722:ℝ))]
    exact Real.sqrt_le_sqrt (h1.trans hG1)
  have hsGhi : Real.sqrt G ≤ 1.42861 := by
    have h1 : (2.0409:ℝ) ≤ (1.42861:ℝ) ^ 2 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (1.42861:ℝ))]
    exact Real.sqrt_le_sqrt (hG2.trans h1)
  have h0pos : (0:ℝ) < Real.sqrt G := Real.sqrt_pos.mpr hGpos
  have hsGne : Real.sqrt G ≠ 0 := ne_of_gt h0pos
  -- w = 1/√G ∈ [0.6999, 0.72876]
  set W : ℝ := 1 / Real.sqrt G with hW_def
  have hw1 : (0.6999:ℝ) ≤ W ∧ W ≤ 0.72876 := by
    constructor
    · rw [hW_def, le_div_iff₀ h0pos]
      have h1 : (0.6999:ℝ) * 1.42861 ≤ 1 := by norm_num
      have h2 : 0.6999 * Real.sqrt G ≤ 0.6999 * 1.42861 :=
        mul_le_mul_of_nonneg_left hsGhi (by norm_num : (0:ℝ) ≤ 0.6999)
      linarith [h1, h2]
    · rw [hW_def, div_le_iff₀ h0pos]
      have h1 : (1:ℝ) ≤ 0.72876 * 1.3722 := by norm_num
      have h2 : 0.72876 * 1.3722 ≤ 0.72876 * Real.sqrt G :=
        mul_le_mul_of_nonneg_left hsGlo (by norm_num : (0:ℝ) ≤ 0.72876)
      linarith [h1, h2]
  have hwpos : (0:ℝ) < W := by rw [hW_def]; positivity
  -- P-series numeric anchors and the atan-W brackets
  have hP0 : (0.610658:ℝ) ≤ nb18P 0.6999 ∧ nb18P 0.6999 ≤ 0.610660 := by norm_num [nb18P]
  have hP1 : (0.629768:ℝ) ≤ nb18P 0.72876 ∧ nb18P 0.72876 ≤ 0.629770 := by norm_num [nb18P]
  have hrem : (0.72876:ℝ) ^ 35 / 35 ≤ 0.0000005 := by norm_num
  have hAwlo : nb18P 0.6999 - 0.0000005 ≤ Real.arctan W := by
    have hmono := nb18_P_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.6999))
      (Set.mem_Ici.mpr (le_of_lt hwpos)) hw1.1
    have hw35 : W ^ 35 ≤ (0.72876:ℝ) ^ 35 :=
      pow_le_pow_left₀ hwpos.le hw1.2 35
    have hser := nb18_series_le hwpos.le
    calc nb18P 0.6999 - 0.0000005
        ≤ nb18P W - W ^ 35 / 35 := by nlinarith [hmono, hrem, hw35]
      _ ≤ Real.arctan W := by linarith [hser]
  have hAwhi : Real.arctan W ≤ nb18P 0.72876 := by
    have hmono := nb18_P_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr (le_of_lt hwpos))
      (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.72876)) hw1.2
    exact le_trans (nb18_atan_le_P hwpos.le) hmono
  have hidr : Real.arctan (Real.sqrt G) = Real.pi / 2 - Real.arctan W := by
    rw [hW_def]
    linarith [nb18_atan_add_inv h0pos]
  have hMtval : matan G = W * (Real.pi / 2 - Real.arctan W) := by
    unfold matan
    rw [if_neg (ne_of_gt hGpos), if_pos hGpos, hidr, hW_def]
    field_simp
  -- shared π/2 − atan W brackets
  have hpi2 : (2:ℝ) * (Real.pi / 2) = Real.pi := by ring
  have hloπ : (0.94100:ℝ) ≤ Real.pi / 2 - Real.arctan W := by
    linarith [hAwhi, hP1.2, nb18_pi.1, hpi2]
  have hhiπ : Real.pi / 2 - Real.arctan W ≤ 0.9601390 := by
    linarith [hAwlo, hP0.1, nb18_pi.2, hpi2]
  have hposπ : (0:ℝ) ≤ Real.pi / 2 - Real.arctan W := le_of_lt (by linarith)
  -- x ↦ x/(1+x²) is decreasing for x ≥ 1: (t−s)(st−1) ≥ 0 certificates
  have hdec1 : Real.sqrt G / (1 + G) ≥ (1.42861:ℝ) / (1 + (1.42861:ℝ) ^ 2) := by
    set Sg : ℝ := Real.sqrt G with hSg_def
    have hGeq : G = Sg * Sg := by rw [hSg_def, ← pow_two]; exact (Real.sq_sqrt hGpos.le).symm
    rw [hGeq, ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 1 + (1.42861:ℝ) ^ 2)
      (by positivity : (0:ℝ) < 1 + Sg * Sg)]
    have e1 : (0:ℝ) ≤ ((1.42861:ℝ) - Sg) * (Sg * (1.42861:ℝ) - 1) := by
      apply mul_nonneg <;> nlinarith [hsGlo, hsGhi]
    linarith [e1]
  have hdec1d : (0.46979:ℝ) ≤ Real.sqrt G / (1 + G) :=
    le_trans (by norm_num : (0.46979:ℝ) ≤ (1.42861:ℝ) / (1 + (1.42861:ℝ) ^ 2)) hdec1
  have hdec2 : Real.sqrt G / (1 + G) ≤ (1.3722:ℝ) / (1 + (1.3722:ℝ) ^ 2) := by
    set Sg : ℝ := Real.sqrt G with hSg_def
    have hGeq : G = Sg * Sg := by rw [hSg_def, ← pow_two]; exact (Real.sq_sqrt hGpos.le).symm
    rw [hGeq, div_le_div_iff₀ (by positivity : (0:ℝ) < 1 + Sg * Sg)
      (by norm_num : (0:ℝ) < 1 + (1.3722:ℝ) ^ 2)]
    have e1 : (0:ℝ) ≤ (Sg - (1.3722:ℝ)) * (Sg * (1.3722:ℝ) - 1) := by
      apply mul_nonneg <;> nlinarith [hsGlo]
    linarith [e1]
  have hdec2d : Real.sqrt G / (1 + G) ≤ (0.475975:ℝ) := by
    have hGeq : G = Real.sqrt G * Real.sqrt G := by
      rw [← pow_two]
      exact (Real.sq_sqrt hGpos.le).symm
    have h3 : Real.sqrt G / (1 + G) ≤ 1.3722 / (1 + (1.3722:ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 1 + G)
        (by norm_num : (0:ℝ) < 1 + (1.3722:ℝ) ^ 2)]
      have e1 : (0:ℝ) ≤ (Real.sqrt G - (1.3722:ℝ)) *
          (Real.sqrt G * (1.3722:ℝ) - 1) := by
        apply mul_nonneg <;> nlinarith [hsGlo]
      linarith [e1]
    have h4 : (1.3722:ℝ) / (1 + (1.3722:ℝ) ^ 2) ≤ (0.475975:ℝ) := by norm_num
    linarith [h3, h4, hGeq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- MU lower
    rw [hMtval]
    have h1 : (0.6999:ℝ) * 0.94100 ≤ W * (Real.pi / 2 - Real.arctan W) :=
      mul_le_mul hw1.1 hloπ (le_of_lt (by norm_num)) hwpos.le
    linarith [h1]
  · -- MU upper
    rw [hMtval]
    have h1 : W * (Real.pi / 2 - Real.arctan W) ≤ (0.72876:ℝ) * 0.9601390 := by
      have ha : W * (Real.pi / 2 - Real.arctan W) ≤
          (0.72876:ℝ) * (Real.pi / 2 - Real.arctan W) :=
        mul_le_mul_of_nonneg_right hw1.2 hposπ
      have hb : (0.72876:ℝ) * (Real.pi / 2 - Real.arctan W) ≤
          (0.72876:ℝ) * 0.9601390 :=
        mul_le_mul_of_nonneg_left hhiπ (by norm_num : (0:ℝ) ≤ 0.72876)
      linarith [ha, hb]
    have h3 : (0.72876:ℝ) * 0.9601390 ≤ 0.69990 := by norm_num
    linarith [h1, h3]
  · -- MPU lower: −0.096 ≤ matanDerivPos G
    unfold matanDerivPos
    have hden : (0:ℝ) < 2 * Real.sqrt G ^ 3 * (1 + G) := by
      rw [pow_succ]
      have h2p : (0:ℝ) < Real.sqrt G * Real.sqrt G := mul_pos h0pos h0pos
      have h3p : (0:ℝ) < Real.sqrt G * (Real.sqrt G * Real.sqrt G) := mul_pos h0pos h2p
      nlinarith [h3p, hG2pos]
    have hkey : Real.arctan (Real.sqrt G) ≤
        Real.sqrt G / (1 + G) + (0.192:ℝ) * Real.sqrt G ^ 3 := by
      rw [hidr]
      have hge2 : (0.192:ℝ) * ((1.3722:ℝ) ^ 3) ≤ (0.192:ℝ) * Real.sqrt G ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact pow_le_pow_left₀ (by norm_num) hsGlo 3
      linarith [hdec1d, hge2, hhiπ]
    have hconv : Real.sqrt G - (1 + G) * Real.arctan (Real.sqrt G) ≥
        -(0.192:ℝ) * Real.sqrt G ^ 3 * (1 + G) := by
      have h2 := mul_le_mul_of_nonneg_left hkey (le_of_lt hG2pos)
      rw [mul_add] at h2
      have hcc : (1 + G) * (Real.sqrt G / (1 + G)) = Real.sqrt G := by field_simp
      have hdd : (1 + G) * ((0.192:ℝ) * Real.sqrt G ^ 3) =
          (0.192:ℝ) * Real.sqrt G ^ 3 * (1 + G) := by ring
      rw [hcc, hdd] at h2
      linarith [h2]
    rw [le_div_iff₀ hden]
    rw [show (-(0.096:ℝ)) * (2 * Real.sqrt G ^ 3 * (1 + G)) =
      -(0.192:ℝ) * Real.sqrt G ^ 3 * (1 + G) by ring]
    linarith [hconv]
  · -- MPU upper: matanDerivPos G ≤ −0.079
    unfold matanDerivPos
    have hden : (0:ℝ) < 2 * Real.sqrt G ^ 3 * (1 + G) := by
      rw [pow_succ]
      have h2p : (0:ℝ) < Real.sqrt G * Real.sqrt G := mul_pos h0pos h0pos
      have h3p : (0:ℝ) < Real.sqrt G * (Real.sqrt G * Real.sqrt G) := mul_pos h0pos h2p
      nlinarith [h3p, hG2pos]
    have hkey2 : Real.sqrt G / (1 + G) + (0.158:ℝ) * Real.sqrt G ^ 3 ≤
        Real.arctan (Real.sqrt G) := by
      rw [hidr]
      have hle2 : (0.158:ℝ) * Real.sqrt G ^ 3 ≤ (0.158:ℝ) * ((1.42861:ℝ) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact pow_le_pow_left₀ (le_of_lt h0pos) hsGhi 3
      linarith [hdec2d, hle2, hloπ]
    have hconv2 : Real.sqrt G + (0.158:ℝ) * Real.sqrt G ^ 3 * (1 + G) ≤
        (1 + G) * Real.arctan (Real.sqrt G) := by
      have h2 := mul_le_mul_of_nonneg_left hkey2 (le_of_lt hG2pos)
      rw [mul_add] at h2
      have hcc : (1 + G) * (Real.sqrt G / (1 + G)) = Real.sqrt G := by field_simp
      have hdd : (1 + G) * ((0.158:ℝ) * Real.sqrt G ^ 3) =
          (0.158:ℝ) * Real.sqrt G ^ 3 * (1 + G) := by ring
      rw [hcc, hdd] at h2
      linarith [h2]
    rw [div_le_iff₀ hden]
    rw [show (-(0.079:ℝ)) * (2 * Real.sqrt G ^ 3 * (1 + G)) =
      -(0.158:ℝ) * Real.sqrt G ^ 3 * (1 + G) by ring]
    linarith [hconv2]/-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -//-! ## 8. The y4-axis monotonicity (split into independent lemmas) -/
/-! ## 8. The y4-axis monotonicity (split into independent lemmas) -/

-- Axis-slice abbreviations.  These are plain (noncomputable) definitions, so the
-- elaborator treats them as opaque atoms; all rewriting happens through explicit
-- rfl-unfold lemmas below.  No `set` commands are used anywhere in this section.

/-- Axis Delta-polynomial: `-2w^4 + (4u+4v-uv)w^2 - 2(u-v)^2` with `u = y5*y5`,
`v = y6*y6`. -/
private noncomputable def nb18dA (y5 y6 w : ℝ) : ℝ :=
  -2 * ((w * w) * (w * w)) +
    (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)) * (w * w) -
    2 * ((y5 * y5) - (y6 * y6)) ^ 2

/-- Its derivative value at `t`. -/
private noncomputable def nb18dA' (y5 y6 t : ℝ) : ℝ :=
  -8 * t * (t * t) +
    (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)) * (2 * t)

/-- Sol-slot-A denominator along the axis. -/
private noncomputable def nb18afA (y5 y6 w : ℝ) : ℝ :=
  ((y5 + Real.sqrt 2) / 2) * (w * w) + (y5 * y5 / 2 + y5 * Real.sqrt 2) * w +
    Real.sqrt 2 * ((y5 * y5) - (y6 * y6)) / 2

/-- Sol-slot-B denominator along the axis. -/
private noncomputable def nb18afB (y5 y6 w : ℝ) : ℝ :=
  Real.sqrt 2 * (y6 * y5) + y6 * (y5 * y5 / 2) +
    Real.sqrt 2 * ((y5 * y5) + (y6 * y6) - (w * w)) / 2 + y5 * (y6 * y6 / 2)

/-- Sol-slot-C denominator along the axis. -/
private noncomputable def nb18afC (y5 y6 w : ℝ) : ℝ :=
  ((y6 + Real.sqrt 2) / 2) * (w * w) + (y6 * y6 / 2 + y6 * Real.sqrt 2) * w +
    Real.sqrt 2 * ((y6 * y6) - (y5 * y5)) / 2

/-- Unfold `nb18dA`. -/
private theorem nb18dA_eq (y5 y6 w : ℝ) : nb18dA y5 y6 w =
    -2 * ((w * w) * (w * w)) +
      (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)) * (w * w) -
      2 * ((y5 * y5) - (y6 * y6)) ^ 2 := rfl

/-- Unfold `nb18dA'`. -/
private theorem nb18dA'_eq (y5 y6 t : ℝ) : nb18dA' y5 y6 t =
    -8 * t * (t * t) +
      (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)) * (2 * t) := rfl

/-- Unfold `nb18afA`. -/
private theorem nb18afA_eq (y5 y6 w : ℝ) : nb18afA y5 y6 w =
    ((y5 + Real.sqrt 2) / 2) * (w * w) + (y5 * y5 / 2 + y5 * Real.sqrt 2) * w +
      Real.sqrt 2 * ((y5 * y5) - (y6 * y6)) / 2 := rfl

/-- Unfold `nb18afB`. -/
private theorem nb18afB_eq (y5 y6 w : ℝ) : nb18afB y5 y6 w =
    Real.sqrt 2 * (y6 * y5) + y6 * (y5 * y5 / 2) +
      Real.sqrt 2 * ((y5 * y5) + (y6 * y6) - (w * w)) / 2 + y5 * (y6 * y6 / 2) := rfl

/-- Unfold `nb18afC`. -/
private theorem nb18afC_eq (y5 y6 w : ℝ) : nb18afC y5 y6 w =
    ((y6 + Real.sqrt 2) / 2) * (w * w) + (y6 * y6 / 2 + y6 * Real.sqrt 2) * w +
      Real.sqrt 2 * ((y6 * y6) - (y5 * y5)) / 2 := rfl

/-- A/C-slot kappa: derivative of the A/C denominator at `t`. -/
private noncomputable def nb18kA (ya t : ℝ) : ℝ :=
  (ya + Real.sqrt 2) * t + ya * ya / 2 + ya * Real.sqrt 2

/-- Unfold `nb18kA`. -/
private theorem nb18kA_eq (ya t : ℝ) : nb18kA ya t =
    (ya + Real.sqrt 2) * t + ya * ya / 2 + ya * Real.sqrt 2 := rfl

/-- DA slot Q-factor `u + v - w^2`. -/
private noncomputable def nb18axQ (y5 y6 w : ℝ) : ℝ := (y5 * y5) + (y6 * y6) - (w * w)

/-- Unfold `nb18axQ`. -/
private theorem nb18axQ_eq (y5 y6 w : ℝ) : nb18axQ y5 y6 w =
    (y5 * y5) + (y6 * y6) - (w * w) := rfl

/-- DA slot W-factor `2 / (w*Q)`. -/
private noncomputable def nb18W (y5 y6 w : ℝ) : ℝ := 2 / (w * nb18axQ y5 y6 w)

/-- Unfold `nb18W`. -/
private theorem nb18W_eq (y5 y6 w : ℝ) : nb18W y5 y6 w = 2 / (w * nb18axQ y5 y6 w) := rfl

/-- DA slot G-atom `4Δ/(w^2*Q^2)`. -/
private noncomputable def nb18G (y5 y6 w : ℝ) : ℝ :=
  4 * nb18dA y5 y6 w / ((w * w) * (nb18axQ y5 y6 w * nb18axQ y5 y6 w))

/-- Unfold `nb18G`. -/
private theorem nb18G_eq (y5 y6 w : ℝ) : nb18G y5 y6 w =
    4 * nb18dA y5 y6 w / ((w * w) * (nb18axQ y5 y6 w * nb18axQ y5 y6 w)) := rfl

/-- DB/DC slot Q-factor `w^2 + yb^2 - ya^2`. -/
private noncomputable def nb18RY (ya yb w : ℝ) : ℝ := (w * w) + (yb * yb) - (ya * ya)

/-- Unfold `nb18RY`. -/
private theorem nb18RY_eq (ya yb w : ℝ) : nb18RY ya yb w =
    (w * w) + (yb * yb) - (ya * ya) := rfl

/-- DB/DC slot W-factor `2ya/(ya^2*R)`. -/
private noncomputable def nb18WY (ya yb w : ℝ) : ℝ :=
  2 * ya / ((ya * ya) * nb18RY ya yb w)

/-- Unfold `nb18WY`. -/
private theorem nb18WY_eq (ya yb w : ℝ) : nb18WY ya yb w =
    2 * ya / ((ya * ya) * nb18RY ya yb w) := rfl

/-- DB/DC slot G-atom `4Δ/(ya^2*R^2)`. -/
private noncomputable def nb18GY (ya yb w : ℝ) : ℝ :=
  4 * nb18dA ya yb w / ((ya * ya) * (nb18RY ya yb w * nb18RY ya yb w))

/-- Unfold `nb18GY`. -/
private theorem nb18GY_eq (ya yb w : ℝ) : nb18GY ya yb w =
    4 * nb18dA ya yb w / ((ya * ya) * (nb18RY ya yb w * nb18RY ya yb w)) := rfl

/-- The square function has derivative `2t`. -/
private theorem nb18_sq_deriv (t : ℝ) : HasDerivAt (fun w : ℝ => w * w) (2 * t) t := by
  have h0' : HasDerivAt (fun w : ℝ => id w * id w) (1 * id t + id t * 1) t :=
    (hasDerivAt_id t).fun_mul (hasDerivAt_id t)
  have h1 : (1:ℝ) * id t + id t * 1 = 2 * t := by
    simp only [id_eq, one_mul, mul_one]
    ring
  rw [h1] at h0'
  exact h0'

/-- Tighter axis-Delta lower bound: `31.987` (vs the coarse `31.669`). -/
private theorem nb18_ax_D2 (u v t : ℝ) (hu : (4:ℝ) ≤ u) (hu' : u ≤ 4.0401)
    (hv : (4:ℝ) ≤ v) (hv' : v ≤ 4.0401) (ht : (2:ℝ) ≤ t) (ht' : t ≤ 2.01) :
    (31.987:ℝ) ≤ -2 * ((t * t) * (t * t)) + (4 * u + 4 * v - u * v) * (t * t) -
      2 * (u - v) ^ 2 := by
  have ht2 := nb18_box2 ht ht'
  have hprod4 : (0:ℝ) ≤ (u - 4) * (v - 4) := by nlinarith
  have hprod5 : (u - 4) * (v - 4) ≤ 0.0401 * 0.0401 :=
    mul_le_mul_of_nonneg (by linarith) (by linarith) (by linarith) (by linarith)
  have huv2 : (u - v) ^ 2 ≤ 0.0401 * 0.0401 := by nlinarith [hu, hu', hv, hv']
  have hsplit : -2 * ((t * t) * (t * t)) + (4 * u + 4 * v - u * v) * (t * t) -
      2 * (u - v) ^ 2 =
      32 - 2 * (t * t - 4) * (t * t - 4) - (t * t) * (16 - (4 * u + 4 * v - u * v)) -
        2 * (u - v) ^ 2 := by ring
  have hc4 : t * t - 4 ≤ 0.0401 := by linarith
  have hc5 : (0:ℝ) ≤ t * t - 4 := by linarith
  have hc6 : (t * t - 4) * (t * t - 4) ≤ 0.0401 * 0.0401 :=
    mul_le_mul_of_nonneg hc4 hc4 hc5 (by norm_num)
  have hcu : (16:ℝ) - (4 * u + 4 * v - u * v) ≤ 0.00160801 := by
    have hid : (16:ℝ) - (4 * u + 4 * v - u * v) = (u - 4) * (v - 4) := by ring
    rw [hid]
    linarith
  have hnu : (0:ℝ) ≤ (16:ℝ) - (4 * u + 4 * v - u * v) := by
    have hid : (16:ℝ) - (4 * u + 4 * v - u * v) = (u - 4) * (v - 4) := by ring
    rw [hid]
    exact hprod4
  rw [hsplit]
  nlinarith [hc6, hcu, hnu, huv2, ht2.2]

/-- Shared axis core: coarse and tight Delta brackets, derivative bracket and
the `HasDerivAt` of the axis Delta-polynomial. -/
private theorem nb18_ax_core (y5 y6 t : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    (31.669:ℝ) ≤ nb18dA y5 y6 t ∧ nb18dA y5 y6 t ≤ 32.0005 ∧
      (31.987:ℝ) ≤ nb18dA y5 y6 t ∧
      (-0.6513:ℝ) ≤ nb18dA' y5 y6 t ∧ nb18dA' y5 y6 t ≤ 0 ∧
      HasDerivAt (nb18dA y5 y6) (nb18dA' y5 y6 t) t := by
  have hu2 := nb18_box2 hy5 hy5'
  have hv2 := nb18_box2 hy6 hy6'
  have hΔbr := nb18_Delta_br (y5 * y5) (y6 * y6) t hu2.1 hu2.2 hv2.1 hv2.2 ht ht'
  have hδbr := nb18_ds_br (y5 * y5) (y6 * y6) t hu2.1 hu2.2 hv2.1 hv2.2 ht ht'
  have hD2 := nb18_ax_D2 (y5 * y5) (y6 * y6) t hu2.1 hu2.2 hv2.1 hv2.2 ht ht'
  have hΔraw : HasDerivAt
      (fun w : ℝ => -2 * ((w * w) * (w * w)) +
        (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)) * (w * w) -
        2 * ((y5 * y5) - (y6 * y6)) ^ 2) (nb18dA' y5 y6 t) t := by
    have p4 : HasDerivAt (fun w : ℝ => (w * w) * (w * w)) (4 * t * (t * t)) t :=
      ((nb18_sq_deriv t).fun_mul (nb18_sq_deriv t)).congr_deriv (by ring)
    have hsum := HasDerivAt.fun_add (p4.const_mul (-2))
      ((nb18_sq_deriv t).const_mul (4 * (y5 * y5) + 4 * (y6 * y6) -
        (y5 * y5) * (y6 * y6)))
    have hfin := hsum.add (hasDerivAt_const t (-(2 * ((y5 * y5) - (y6 * y6)) ^ 2)))
    rw [nb18dA'_eq]
    exact hfin.congr_deriv (by ring)
  refine ⟨hΔbr.1, hΔbr.2, hD2, hδbr.1, hδbr.2, ?_⟩
  exact hΔraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun w => rfl))

/-- A/C-slot kappa bracket (`nb18_kA_br` restated on `nb18kA`). -/
private theorem nb18_kA_def_br (ya t : ℝ) (hya : 2 ≤ ya) (hya' : ya ≤ 2.01)
    (hs : 2 ≤ t) (hs' : t ≤ 2.01) :
    (11.6568:ℝ) ≤ nb18kA ya t ∧ nb18kA ya t ≤ 11.7454 := by
  rw [nb18kA_eq]
  exact nb18_kA_br ya t hya hya' hs hs'

/-- `lfun (w/2)` is affine: `(63 - 25w)/13`, derivative `-(25/13)`. -/
private theorem nb18_lfun_half_deriv (t : ℝ) :
    HasDerivAt (fun w : ℝ => lfun (w / 2)) (-(25 / 13 : ℝ)) t := by
  have hfun : (fun w : ℝ => lfun (w / 2)) = (fun w : ℝ => (63 - 25 * w) / 13) := by
    funext w
    show (h0 - w / 2) / (h0 - 1) = (63 - 25 * w) / 13
    rw [show h0 = (1.26:ℝ) from rfl]
    ring
  rw [hfun]
  refine (((hasDerivAt_const t (63:ℝ)).sub
    ((hasDerivAt_id t).const_mul 25)).div_const 13).congr_deriv ?_
  ring

/-- `lfun (x/2) ∈ [0.980769, 1]` on the box `[2, 2.01]`. -/
private theorem nb18_lfun_half_br {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 2.01) :
    (0.980769:ℝ) ≤ lfun (x / 2) ∧ lfun (x / 2) ≤ 1 := by
  have hfun : lfun (x / 2) = (63 - 25 * x) / 13 := by
    show (h0 - x / 2) / (h0 - 1) = (63 - 25 * x) / 13
    rw [show h0 = (1.26:ℝ) from rfl]
    ring
  rw [hfun]
  constructor
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 13)]
    linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 13)]
    linarith

/-- The symmetric 3-coordinate slice of `deltaX` at `x2 = x4 = x6 = 2`. -/
private theorem nb18_deltaX_tri (x1 x3 x5 : ℝ) : deltaX x1 2 x3 2 x5 2 =
    -2 * (x1 * x1) - 2 * (x3 * x3) - 2 * (x5 * x5) +
      4 * (x1 * x3) + 4 * (x1 * x5) + 4 * (x3 * x5) - (x1 * x3 * x5) := by
  simp only [deltaX]
  ring

/-- The symmetric 3-coordinate slice of `deltaX4` at `x2 = x4 = x6 = 2`. -/
private theorem nb18_deltaX4_tri (x1 x3 x5 : ℝ) : deltaX4 x1 2 x3 2 x5 2 =
    x1 * (x3 + x5 - x1) := by
  simp only [deltaX4]
  ring

/-- Slot-A value identity. -/
private theorem nb18_solA_eq (ya yb w : ℝ) (hya : 0 ≤ ya) (hw : 0 < w) :
    solEulerXDivSqrtdelta (ya * ya) 2 (w * w) 2 (yb * yb) 2 =
      matan (nb18dA ya yb w / (4 * (nb18afA ya yb w * nb18afA ya yb w))) /
        nb18afA ya yb w := by
  have hw0 : (0:ℝ) ≤ w := le_of_lt hw
  have hD : deltaX (ya * ya) 2 (w * w) 2 (yb * yb) 2 = nb18dA ya yb w := by
    rw [nb18_deltaX_tri, nb18dA_eq]
    ring
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ha : (Real.sqrt ((ya * ya) * 2 * (w * w)) +
      Real.sqrt (ya * ya) * (2 + (w * w) - 2) / 2 +
      Real.sqrt 2 * ((ya * ya) + (w * w) - (yb * yb)) / 2 +
      Real.sqrt (w * w) * ((ya * ya) + 2 - 2) / 2) = nb18afA ya yb w := by
    rw [nb18afA_eq]
    simp only [show ((ya:ℝ) * (ya)) = (ya:ℝ) ^ 2 from (sq ya).symm,
      Real.sqrt_sq (hya),
      show ((w:ℝ) * (w)) = (w:ℝ) ^ 2 from (sq w).symm, Real.sqrt_sq hw0]
    rw [show ((ya:ℝ) ^ 2 * 2 * (w:ℝ) ^ 2) = ((ya:ℝ) * Real.sqrt 2 * w) ^ 2 from by
        simp only [mul_pow, hsq2],
      Real.sqrt_sq (mul_nonneg (mul_nonneg hya
        (le_of_lt (Real.sqrt_pos.mpr (by norm_num)))) hw.le),
      show ((2:ℝ) + (w:ℝ) ^ 2 - 2) = (w:ℝ) ^ 2 from by ring,
      show (((ya:ℝ) ^ 2) + 2 - 2) = (ya:ℝ) ^ 2 from by ring]
    ring
  simp only [solEulerXDivSqrtdelta]
  rw [hD, ← pow_two (nb18afA ya yb w), ha]

/-- Slot-B value identity. -/
private theorem nb18_solB_eq (y5 y6 w : ℝ) (hy5 : 0 ≤ y5) (hy6 : 0 ≤ y6) (hw : 0 < w) :
    solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (w * w) 2 =
      matan (nb18dA y5 y6 w / (4 * (nb18afB y5 y6 w * nb18afB y5 y6 w))) /
        nb18afB y5 y6 w := by
  have hw0 : (0:ℝ) ≤ w := le_of_lt hw
  have hD : deltaX (y6 * y6) 2 (y5 * y5) 2 (w * w) 2 = nb18dA y5 y6 w := by
    rw [nb18_deltaX_tri, nb18dA_eq]
    ring
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ha : (Real.sqrt ((y6 * y6) * 2 * (y5 * y5)) +
      Real.sqrt (y6 * y6) * (2 + (y5 * y5) - 2) / 2 +
      Real.sqrt 2 * ((y6 * y6) + (y5 * y5) - (w * w)) / 2 +
      Real.sqrt (y5 * y5) * ((y6 * y6) + 2 - 2) / 2) = nb18afB y5 y6 w := by
    rw [nb18afB_eq]
    simp only [show ((y5:ℝ) * (y5)) = (y5:ℝ) ^ 2 from (sq y5).symm,
      Real.sqrt_sq (hy5),
      show ((y6:ℝ) * (y6)) = (y6:ℝ) ^ 2 from (sq y6).symm,
      Real.sqrt_sq (hy6),
      show ((w:ℝ) * (w)) = (w:ℝ) ^ 2 from (sq w).symm, Real.sqrt_sq hw0]
    rw [show ((y6:ℝ) ^ 2 * 2 * (y5:ℝ) ^ 2) = ((y6:ℝ) * Real.sqrt 2 * y5) ^ 2 from by
        simp only [mul_pow, hsq2],
      Real.sqrt_sq (mul_nonneg (mul_nonneg hy6
        (le_of_lt (Real.sqrt_pos.mpr (by norm_num)))) hy5),
      show ((2:ℝ) + (y5:ℝ) ^ 2 - 2) = (y5:ℝ) ^ 2 from by ring,
      show (((y6:ℝ) ^ 2) + 2 - 2) = (y6:ℝ) ^ 2 from by ring]
    ring
  simp only [solEulerXDivSqrtdelta]
  rw [hD, ← pow_two (nb18afB y5 y6 w), ha]

/-- Slot-C value identity. -/
private theorem nb18_solC_eq (y5 y6 w : ℝ) (hy6 : 0 ≤ y6) (hw : 0 < w) :
    solEulerXDivSqrtdelta (w * w) 2 (y6 * y6) 2 (y5 * y5) 2 =
      matan (nb18dA y5 y6 w / (4 * (nb18afC y5 y6 w * nb18afC y5 y6 w))) /
        nb18afC y5 y6 w := by
  have hw0 : (0:ℝ) ≤ w := le_of_lt hw
  have hD : deltaX (w * w) 2 (y6 * y6) 2 (y5 * y5) 2 = nb18dA y5 y6 w := by
    rw [nb18_deltaX_tri, nb18dA_eq]
    ring
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ha : (Real.sqrt ((w * w) * 2 * (y6 * y6)) +
      Real.sqrt (w * w) * (2 + (y6 * y6) - 2) / 2 +
      Real.sqrt 2 * ((w * w) + (y6 * y6) - (y5 * y5)) / 2 +
      Real.sqrt (y6 * y6) * ((w * w) + 2 - 2) / 2) = nb18afC y5 y6 w := by
    rw [nb18afC_eq]
    simp only [show ((y5:ℝ) * (y5)) = (y5:ℝ) ^ 2 from (sq y5).symm,
      show ((y6:ℝ) * (y6)) = (y6:ℝ) ^ 2 from (sq y6).symm,
      Real.sqrt_sq (hy6),
      show ((w:ℝ) * (w)) = (w:ℝ) ^ 2 from (sq w).symm, Real.sqrt_sq hw0]
    rw [show ((w:ℝ) ^ 2 * 2 * (y6:ℝ) ^ 2) = ((w:ℝ) * Real.sqrt 2 * y6) ^ 2 from by
        simp only [mul_pow, hsq2],
      Real.sqrt_sq (mul_nonneg (mul_nonneg hw0
        (le_of_lt (Real.sqrt_pos.mpr (by norm_num)))) hy6),
      show ((2:ℝ) + (y6:ℝ) ^ 2 - 2) = (y6:ℝ) ^ 2 from by ring,
      show (((w:ℝ) ^ 2) + 2 - 2) = (w:ℝ) ^ 2 from by ring]
    ring
  simp only [solEulerXDivSqrtdelta]
  rw [hD, ← pow_two (nb18afC y5 y6 w), ha]

/-- The W-factor shape conversion `2z/((z*z)*r) = 2/(z*r)` for `z ≠ 0`. -/
private theorem nb18_hfac (z r : ℝ) (hz : z ≠ 0) :
    (2:ℝ) * z / ((z * z) * r) = 2 / (z * r) := by
  rw [mul_comm 2 z, mul_assoc z z r]
  exact mul_div_mul_left 2 (z * r) hz

/-- DA-slot value identity (dihedral at the moving coordinate). -/
private theorem nb18_dihA_eq (y5 y6 w : ℝ) (hw : 0 < w) :
    dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2 (y5 * y5) 2 =
      nb18W y5 y6 w * matan (nb18G y5 y6 w) := by
  have hs4 : Real.sqrt (4 * (w * w)) = 2 * w := by
    rw [show ((4:ℝ) * (w * w)) = (2 * w) ^ 2 from by ring]
    exact Real.sqrt_sq (show (0:ℝ) ≤ 2 * w by linarith)
  have hD4 : deltaX4 (w * w) 2 (y6 * y6) 2 (y5 * y5) 2 = (w * w) * nb18axQ y5 y6 w := by
    rw [nb18_deltaX4_tri, nb18axQ_eq]
    ring
  have hD : deltaX (w * w) 2 (y6 * y6) 2 (y5 * y5) 2 = nb18dA y5 y6 w := by
    rw [nb18_deltaX_tri, nb18dA_eq]
    ring
  have harg : (4:ℝ)*(w*w)*(nb18dA y5 y6 w)/(((w*w)*(nb18axQ y5 y6 w))^2) =
      (4:ℝ)*(nb18dA y5 y6 w)/((w*w)*(nb18axQ y5 y6 w*nb18axQ y5 y6 w)) := by
    rw [sq]
    field_simp
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [hD4, hD, hs4, harg, nb18G_eq, nb18_hfac w (nb18axQ y5 y6 w) (ne_of_gt hw), nb18W_eq]

/-- DB/DC-slot value identity (dihedral at the third slot). -/
private theorem nb18_dihY_eq (ya yb w : ℝ) (hya : 0 < ya) (hw : 0 < w) :
    dihXDivSqrtdeltaPosbranch (ya * ya) 2 (w * w) 2 (yb * yb) 2 =
      nb18WY ya yb w * matan (nb18GY ya yb w) := by
  have hsya : Real.sqrt (4 * (ya * ya)) = 2 * ya := by
    rw [show ((4:ℝ) * (ya * ya)) = (2 * ya) ^ 2 from by ring]
    exact Real.sqrt_sq (show (0:ℝ) ≤ 2 * ya by linarith)
  have hD4 : deltaX4 (ya * ya) 2 (w * w) 2 (yb * yb) 2 =
      (ya * ya) * nb18RY ya yb w := by
    rw [nb18_deltaX4_tri, nb18RY_eq]
  have hD : deltaX (ya * ya) 2 (w * w) 2 (yb * yb) 2 = nb18dA ya yb w := by
    rw [nb18_deltaX_tri, nb18dA_eq]
    ring
  have harg : (4:ℝ)*(ya*ya)*(nb18dA ya yb w)/(((ya*ya)*(nb18RY ya yb w))^2) =
      (4:ℝ)*(nb18dA ya yb w)/((ya*ya)*(nb18RY ya yb w*nb18RY ya yb w)) := by
    rw [sq]
    field_simp
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [hD4, hD, hsya, harg, nb18GY_eq, nb18_hfac ya (nb18RY ya yb w) (ne_of_gt hya),
    nb18WY_eq, ← nb18_hfac ya (nb18RY ya yb w) (ne_of_gt hya)]

/-- The `pc3` kernel along the y4-axis, unfolded to the six raw slots. -/
private theorem nb18_pc3_unfold (y5 y6 w : ℝ) (hw : 0 < w) (hy5 : 0 < y5) (hy6 : 0 < y6) :
    pc3 w y5 y6 =
      1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta (y5 * y5) 2 (w * w) 2 (y6 * y6) 2 +
          solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (w * w) 2 +
          solEulerXDivSqrtdelta (w * w) 2 (y6 * y6) 2 (y5 * y5) 2) +
        (8 * mm2 / Real.pi) *
          (lfun (w / 2) * dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2 (y5 * y5) 2 +
            lfun (y5 / 2) * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (w * w) 2 (y6 * y6) 2 +
            lfun (y6 / 2) * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (w * w) 2) := by
  have e4 : Real.sqrt ((w:ℝ) * (w)) = w := by
    rw [show ((w:ℝ) * (w)) = (w:ℝ) ^ 2 from (sq w).symm]
    exact Real.sqrt_sq (show (0:ℝ) ≤ w by linarith)
  have e5 : Real.sqrt ((y5:ℝ) * (y5)) = y5 := by
    rw [show ((y5:ℝ) * (y5)) = (y5:ℝ) ^ 2 from (sq y5).symm]
    exact Real.sqrt_sq (show (0:ℝ) ≤ y5 by linarith)
  have e6 : Real.sqrt ((y6:ℝ) * (y6)) = y6 := by
    rw [show ((y6:ℝ) * (y6)) = (y6:ℝ) ^ 2 from (sq y6).symm]
    exact Real.sqrt_sq (show (0:ℝ) ≤ y6 by linarith)
  have e1 := nb18_indep 1 1 1 w y5 y6
  rw [← e1]
  simp only [yOfX, nb18_unfold, scalar6, uni, mk456, compose6, projX4, projX5, projX6,
    projY4, projY5, projY6, constant6, two6, rotate4, rotate5, rotate6,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply, one_mul, mul_one]
  rw [e4, e5, e6]
  simp only [show ((w:ℝ) * 0.5) = w / 2 from by ring,
    show ((y5:ℝ) * 0.5) = y5 / 2 from by ring,
    show ((y6:ℝ) * 0.5) = y6 / 2 from by ring]

/-- The `dih` slots are invariant under swapping the second and third
edge-pairs (on the `x2 = x4 = x6 = 2` slice both `deltaX` and `deltaX4`
are symmetric in `(x3, x5)`). -/
private theorem nb18_dih_swap23 (x1 x3 x5 : ℝ) :
    dihXDivSqrtdeltaPosbranch x1 2 x3 2 x5 2 =
      dihXDivSqrtdeltaPosbranch x1 2 x5 2 x3 2 := by
  simp only [dihXDivSqrtdeltaPosbranch, nb18_deltaX_tri, nb18_deltaX4_tri]
  ring

set_option maxHeartbeats 800000 in
/-- Sol-slot-A derivative along the axis with its upper bound. -/
private theorem nb18_solA_slot (y5 y6 t : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    ∃ d : ℝ, HasDerivAt
        (fun w => solEulerXDivSqrtdelta (y5 * y5) 2 (w * w) 2 (y6 * y6) 2) d t ∧
      d ≤ -(0.0403:ℝ) := by
  obtain ⟨hD1, hD2, hD3, hδ1, hδ2, hΔf⟩ := nb18_ax_core y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  have haA : (16.4569:ℝ) ≤ nb18afA y5 y6 t ∧ nb18afA y5 y6 t ≤ 16.7194 :=
    nb18_aA_br y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  have hafpos : (0:ℝ) < nb18afA y5 y6 t := lt_of_lt_of_le (by norm_num) haA.1
  have ha2 : (270.82:ℝ) ≤ nb18afA y5 y6 t * nb18afA y5 y6 t ∧
      nb18afA y5 y6 t * nb18afA y5 y6 t ≤ 279.54 := by
    constructor
    · have h := mul_le_mul haA.1 haA.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul haA.2 haA.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have h4a2 : (1083.28:ℝ) ≤ 4 * (nb18afA y5 y6 t * nb18afA y5 y6 t) ∧
      4 * (nb18afA y5 y6 t * nb18afA y5 y6 t) ≤ 1118.2 := ⟨by linarith, by linarith⟩
  have h4apos : (0:ℝ) < 4 * (nb18afA y5 y6 t * nb18afA y5 y6 t) :=
    mul_pos (by norm_num) (mul_pos hafpos hafpos)
  have hDQ : (-0.000602:ℝ) ≤
      nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) ∧
      nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) ≤ 0 := by
    constructor
    · rw [le_div_iff₀ h4apos]
      have hAtom : (0.000602:ℝ) * (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) ≤
          (0.000602:ℝ) * 1118.2 := mul_le_mul_of_nonneg_left h4a2.2 (by norm_num)
      linarith [hAtom, hδ1]
    · rw [div_le_iff₀ h4apos]
      linarith [hδ2]
  have hκbr := nb18_kA_def_br y5 t hy5 hy5' ht ht'
  have hDk : (372.82:ℝ) ≤ nb18dA y5 y6 t * nb18kA y5 t ∧
      nb18dA y5 y6 t * nb18kA y5 t ≤ 375.87 := by
    constructor
    · have h := mul_le_mul hD3 hκbr.1 (by linarith) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul hD2 hκbr.2 (by linarith) (by linarith)
      norm_num at h
      linarith [h]
  have h2a3 : (8912:ℝ) ≤
      2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t) ∧
      2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t) ≤ 9348 := by
    constructor
    · have h := mul_le_mul ha2.1 haA.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul ha2.2 haA.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hKQpos : (0:ℝ) < 2 *
      (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t) :=
    mul_pos (by norm_num) (mul_pos (mul_pos hafpos hafpos) hafpos)
  have hKQlo : (0.0398:ℝ) ≤
      nb18dA y5 y6 t * nb18kA y5 t /
        (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)) := by
    rw [le_div_iff₀ hKQpos]
    have hAtom : (0.0398:ℝ) *
        (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)) ≤
        (0.0398:ℝ) * 9348 := mul_le_mul_of_nonneg_left h2a3.2 (by norm_num)
    linarith [hAtom, hDk.1]
  have hKQhi : nb18dA y5 y6 t * nb18kA y5 t /
      (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)) ≤
      (0.0422:ℝ) := by
    rw [div_le_iff₀ hKQpos]
    have hAtom : (0.0422:ℝ) *
        (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)) ≥
        (0.0422:ℝ) * 8912 := mul_le_mul_of_nonneg_left h2a3.1 (by norm_num)
    linarith [hAtom, hDk.2]
  have hdt : (-0.0429:ℝ) ≤
      nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
        nb18dA y5 y6 t * nb18kA y5 t /
          (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)) ∧
      nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
        nb18dA y5 y6 t * nb18kA y5 t /
          (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)) ≤
      -(0.0398:ℝ) := by
    constructor <;> linarith [hDQ.1, hDQ.2, hKQlo, hKQhi]
  have hθ := nb18_theta_br hD1 hD2 haA.1 haA.2
  have hmt := nb18_mt_br hθ.1 hθ.2
  have hmp := nb18_mp_br hθ.1 hθ.2
  have hmpd : (0.0126:ℝ) ≤
      matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t))) ∧
      matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t))) ≤
      (0.0148:ℝ) := by
    have hnegMP : (0.3189:ℝ) ≤
        -(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)))) ∧
        -(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)))) ≤
        (0.344:ℝ) := ⟨by linarith [hmp.2], by linarith [hmp.1]⟩
    have hnegdt : (0.0398:ℝ) ≤
        -(nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t))) ∧
        -(nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t))) ≤
        (0.0429:ℝ) := ⟨by linarith [hdt.2], by linarith [hdt.1]⟩
    have heq : matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t))) =
      (-matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)))) *
        (-(nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t)))) := by ring
    constructor
    · rw [heq]
      have h := mul_le_mul hnegMP.1 hnegdt.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · rw [heq]
      have h := mul_le_mul hnegMP.2 hnegdt.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hmtk : (11.538:ℝ) ≤
      matan (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        nb18kA y5 t ∧
      matan (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        nb18kA y5 t ≤ (11.638:ℝ) := by
    constructor
    · have h := mul_le_mul hmt.1 hκbr.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul hmt.2 hκbr.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hκ : HasDerivAt (nb18afA y5 y6) (nb18kA y5 t) t := by
    have h1 : HasDerivAt (fun w : ℝ => ((y5 + Real.sqrt 2) / 2) * (w * w))
        (((y5 + Real.sqrt 2) / 2) * (2 * t)) t :=
      ((hasDerivAt_const t _).fun_mul (nb18_sq_deriv t)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun w : ℝ => (y5 * y5 / 2 + y5 * Real.sqrt 2) * w)
        (y5 * y5 / 2 + y5 * Real.sqrt 2) t :=
      ((hasDerivAt_const t _).fun_mul (hasDerivAt_id t)).congr_deriv (by ring)
    have h3 : HasDerivAt
        (fun w : ℝ => Real.sqrt 2 * ((y5 * y5) - (y6 * y6)) / 2) 0 t :=
      hasDerivAt_const t _
    have hb := h1.add (h2.add h3)
    have hb2 : HasDerivAt (nb18afA y5 y6)
        (((y5 + Real.sqrt 2) / 2) * (2 * t) + (y5 * y5 / 2 + y5 * Real.sqrt 2 + 0)) t := by
      refine hb.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w _
      rw [nb18afA_eq]
      simp only [Pi.add_apply]
      ring
    exact hb2.congr_deriv (by rw [nb18kA_eq]; ring)
  have harg : (0:ℝ) < nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) :=
    div_pos (by linarith) (mul_pos (by norm_num) (mul_pos hafpos hafpos))
  have hchain := nb18_hasDerivAt_sol hΔf hκ hafpos harg
  refine ⟨(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t / (2 * nb18afA y5 y6 t ^ 3)) /
      nb18afA y5 y6 t -
    matan (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) * nb18kA y5 t /
      nb18afA y5 y6 t ^ 2), ?_, ?_⟩
  · refine hchain.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    exact nb18_solA_eq y5 y6 w (by linarith) hw
  · rw [show nb18afA y5 y6 t ^ 2 = nb18afA y5 y6 t * nb18afA y5 y6 t from pow_two _,
      show nb18afA y5 y6 t ^ 3 =
        nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t from by
        rw [pow_succ, pow_two]]
    have hT1 : matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y5 t /
            (2 * (nb18afA y5 y6 t * nb18afA y5 y6 t * nb18afA y5 y6 t))) /
      nb18afA y5 y6 t ≤ (0.0009:ℝ) := by
      rw [div_le_iff₀ hafpos]
      have hAtom : (0.0009:ℝ) * 16.4569 ≤ (0.0009:ℝ) * nb18afA y5 y6 t :=
        mul_le_mul_of_nonneg_left haA.1 (by norm_num)
      norm_num at hAtom
      linarith [hmpd.2, hAtom]
    have hT2 : (0.0412:ℝ) ≤
        matan (nb18dA y5 y6 t / (4 * (nb18afA y5 y6 t * nb18afA y5 y6 t))) *
          nb18kA y5 t / (nb18afA y5 y6 t * nb18afA y5 y6 t) := by
      rw [le_div_iff₀ (mul_pos hafpos hafpos)]
      have hAtom : (0.0412:ℝ) * 270.82 ≤
          (0.0412:ℝ) * (nb18afA y5 y6 t * nb18afA y5 y6 t) :=
        mul_le_mul_of_nonneg_left ha2.1 (by norm_num)
      linarith [hmtk.1, hAtom]
    linarith [hT1, hT2]

set_option maxHeartbeats 800000 in
/-- Sol-slot-C derivative along the axis with its upper bound. -/
private theorem nb18_solC_slot (y5 y6 t : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    ∃ d : ℝ, HasDerivAt
        (fun w => solEulerXDivSqrtdelta (w * w) 2 (y6 * y6) 2 (y5 * y5) 2) d t ∧
      d ≤ -(0.0403:ℝ) := by
  obtain ⟨hD1, hD2, hD3, hδ1, hδ2, hΔf⟩ := nb18_ax_core y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  have haC : (16.4569:ℝ) ≤ nb18afC y5 y6 t ∧ nb18afC y5 y6 t ≤ 16.7194 :=
    nb18_aA_br y6 y5 t hy6 hy6' hy5 hy5' ht ht'
  have hafpos : (0:ℝ) < nb18afC y5 y6 t := lt_of_lt_of_le (by norm_num) haC.1
  have ha2 : (270.82:ℝ) ≤ nb18afC y5 y6 t * nb18afC y5 y6 t ∧
      nb18afC y5 y6 t * nb18afC y5 y6 t ≤ 279.54 := by
    constructor
    · have h := mul_le_mul haC.1 haC.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul haC.2 haC.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have h4a2 : (1083.28:ℝ) ≤ 4 * (nb18afC y5 y6 t * nb18afC y5 y6 t) ∧
      4 * (nb18afC y5 y6 t * nb18afC y5 y6 t) ≤ 1118.2 := ⟨by linarith, by linarith⟩
  have h4apos : (0:ℝ) < 4 * (nb18afC y5 y6 t * nb18afC y5 y6 t) :=
    mul_pos (by norm_num) (mul_pos hafpos hafpos)
  have hDQ : (-0.000602:ℝ) ≤
      nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) ∧
      nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) ≤ 0 := by
    constructor
    · rw [le_div_iff₀ h4apos]
      have hAtom : (0.000602:ℝ) * (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) ≤
          (0.000602:ℝ) * 1118.2 := mul_le_mul_of_nonneg_left h4a2.2 (by norm_num)
      linarith [hAtom, hδ1]
    · rw [div_le_iff₀ h4apos]
      linarith [hδ2]
  have hκbr := nb18_kA_def_br y6 t hy6 hy6' ht ht'
  have hDk : (372.82:ℝ) ≤ nb18dA y5 y6 t * nb18kA y6 t ∧
      nb18dA y5 y6 t * nb18kA y6 t ≤ 375.87 := by
    constructor
    · have h := mul_le_mul hD3 hκbr.1 (by linarith) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul hD2 hκbr.2 (by linarith) (by linarith)
      norm_num at h
      linarith [h]
  have h2a3 : (8912:ℝ) ≤
      2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t) ∧
      2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t) ≤ 9348 := by
    constructor
    · have h := mul_le_mul ha2.1 haC.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul ha2.2 haC.2 (by linarith) (by linarith)
      norm_num at h
      linarith [h]
  have hKQpos : (0:ℝ) < 2 *
      (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t) :=
    mul_pos (by norm_num) (mul_pos (mul_pos hafpos hafpos) hafpos)
  have hKQlo : (0.0398:ℝ) ≤
      nb18dA y5 y6 t * nb18kA y6 t /
        (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)) := by
    rw [le_div_iff₀ hKQpos]
    have hAtom : (0.0398:ℝ) *
        (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)) ≤
        (0.0398:ℝ) * 9348 := mul_le_mul_of_nonneg_left h2a3.2 (by norm_num)
    linarith [hAtom, hDk.1]
  have hKQhi : nb18dA y5 y6 t * nb18kA y6 t /
      (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)) ≤
      (0.0422:ℝ) := by
    rw [div_le_iff₀ hKQpos]
    have hAtom : (0.0422:ℝ) *
        (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)) ≥
        (0.0422:ℝ) * 8912 := mul_le_mul_of_nonneg_left h2a3.1 (by norm_num)
    linarith [hAtom, hDk.2]
  have hdt : (-0.0429:ℝ) ≤
      nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
        nb18dA y5 y6 t * nb18kA y6 t /
          (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)) ∧
      nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
        nb18dA y5 y6 t * nb18kA y6 t /
          (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)) ≤
      -(0.0398:ℝ) := by
    constructor <;> linarith [hDQ.1, hDQ.2, hKQlo, hKQhi]
  have hθ := nb18_theta_br hD1 hD2 haC.1 haC.2
  have hmt := nb18_mt_br hθ.1 hθ.2
  have hmp := nb18_mp_br hθ.1 hθ.2
  have hmpd : (0.0126:ℝ) ≤
      matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t))) ∧
      matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t))) ≤
      (0.0148:ℝ) := by
    have hnegMP : (0.3189:ℝ) ≤
        -(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)))) ∧
        -(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)))) ≤
        (0.344:ℝ) := ⟨by linarith [hmp.2], by linarith [hmp.1]⟩
    have hnegdt : (0.0398:ℝ) ≤
        -(nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t))) ∧
        -(nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t))) ≤
        (0.0429:ℝ) := ⟨by linarith [hdt.2], by linarith [hdt.1]⟩
    have heq : matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t))) =
      (-matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)))) *
        (-(nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t)))) := by ring
    constructor
    · rw [heq]
      have h := mul_le_mul hnegMP.1 hnegdt.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · rw [heq]
      have h := mul_le_mul hnegMP.2 hnegdt.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hmtk : (11.538:ℝ) ≤
      matan (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        nb18kA y6 t ∧
      matan (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        nb18kA y6 t ≤ (11.638:ℝ) := by
    constructor
    · have h := mul_le_mul hmt.1 hκbr.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul hmt.2 hκbr.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hκ : HasDerivAt (nb18afC y5 y6) (nb18kA y6 t) t := by
    have h1 : HasDerivAt (fun w : ℝ => ((y6 + Real.sqrt 2) / 2) * (w * w))
        (((y6 + Real.sqrt 2) / 2) * (2 * t)) t :=
      ((hasDerivAt_const t _).fun_mul (nb18_sq_deriv t)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun w : ℝ => (y6 * y6 / 2 + y6 * Real.sqrt 2) * w)
        (y6 * y6 / 2 + y6 * Real.sqrt 2) t :=
      ((hasDerivAt_const t _).fun_mul (hasDerivAt_id t)).congr_deriv (by ring)
    have h3 : HasDerivAt
        (fun w : ℝ => Real.sqrt 2 * ((y6 * y6) - (y5 * y5)) / 2) 0 t :=
      hasDerivAt_const t _
    have hb := h1.add (h2.add h3)
    have hb2 : HasDerivAt (nb18afC y5 y6)
        (((y6 + Real.sqrt 2) / 2) * (2 * t) + (y6 * y6 / 2 + y6 * Real.sqrt 2 + 0)) t := by
      refine hb.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w _
      rw [nb18afC_eq]
      simp only [Pi.add_apply]
      ring
    exact hb2.congr_deriv (by rw [nb18kA_eq]; ring)
  have harg : (0:ℝ) < nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) :=
    div_pos (by linarith) (mul_pos (by norm_num) (mul_pos hafpos hafpos))
  have hchain := nb18_hasDerivAt_sol hΔf hκ hafpos harg
  refine ⟨(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t / (2 * nb18afC y5 y6 t ^ 3)) /
      nb18afC y5 y6 t -
    matan (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) * nb18kA y6 t /
      nb18afC y5 y6 t ^ 2), ?_, ?_⟩
  · refine hchain.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    exact nb18_solC_eq y5 y6 w (by linarith) hw
  · rw [show nb18afC y5 y6 t ^ 2 = nb18afC y5 y6 t * nb18afC y5 y6 t from pow_two _,
      show nb18afC y5 y6 t ^ 3 =
        nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t from by
        rw [pow_succ, pow_two]]
    have hT1 : matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t)) -
          nb18dA y5 y6 t * nb18kA y6 t /
            (2 * (nb18afC y5 y6 t * nb18afC y5 y6 t * nb18afC y5 y6 t))) /
      nb18afC y5 y6 t ≤ (0.0009:ℝ) := by
      rw [div_le_iff₀ hafpos]
      have hAtom : (0.0009:ℝ) * 16.4569 ≤ (0.0009:ℝ) * nb18afC y5 y6 t :=
        mul_le_mul_of_nonneg_left haC.1 (by norm_num)
      norm_num at hAtom
      linarith [hmpd.2, hAtom]
    have hT2 : (0.0412:ℝ) ≤
        matan (nb18dA y5 y6 t / (4 * (nb18afC y5 y6 t * nb18afC y5 y6 t))) *
          nb18kA y6 t / (nb18afC y5 y6 t * nb18afC y5 y6 t) := by
      rw [le_div_iff₀ (mul_pos hafpos hafpos)]
      have hAtom : (0.0412:ℝ) * 270.82 ≤
          (0.0412:ℝ) * (nb18afC y5 y6 t * nb18afC y5 y6 t) :=
        mul_le_mul_of_nonneg_left ha2.1 (by norm_num)
      linarith [hmtk.1, hAtom]
    linarith [hT1, hT2]

set_option maxHeartbeats 800000 in
/-- Sol-slot-B derivative along the axis with its upper bound. -/
private theorem nb18_solB_slot (y5 y6 t : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    ∃ d : ℝ, HasDerivAt
        (fun w => solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (w * w) 2) d t ∧
      d ≤ (0.0104:ℝ) := by
  obtain ⟨hD1, hD2, hD3, hδ1, hδ2, hΔf⟩ := nb18_ax_core y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  have haB : (16.4569:ℝ) ≤ nb18afB y5 y6 t ∧ nb18afB y5 y6 t ≤ 16.7194 :=
    nb18_aB_br y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  have hafpos : (0:ℝ) < nb18afB y5 y6 t := lt_of_lt_of_le (by norm_num) haB.1
  have ha2 : (270.82:ℝ) ≤ nb18afB y5 y6 t * nb18afB y5 y6 t ∧
      nb18afB y5 y6 t * nb18afB y5 y6 t ≤ 279.54 := by
    constructor
    · have h := mul_le_mul haB.1 haB.1 (by norm_num) (by linarith)
      linarith [h]
    · have h := mul_le_mul haB.2 haB.2 (by linarith) (by norm_num)
      linarith [h]
  have hDQ : (-0.000602:ℝ) ≤
      nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) ∧
      nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) ≤ 0 := by
    have h4apos : (0:ℝ) < 4 * (nb18afB y5 y6 t * nb18afB y5 y6 t) :=
      mul_pos (by norm_num) (mul_pos hafpos hafpos)
    have h4a2 : (1083.28:ℝ) ≤ 4 * (nb18afB y5 y6 t * nb18afB y5 y6 t) ∧
        4 * (nb18afB y5 y6 t * nb18afB y5 y6 t) ≤ 1118.2 := ⟨by linarith, by linarith⟩
    constructor
    · rw [le_div_iff₀ h4apos]
      have hAtom : (0.000602:ℝ) * (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) ≤
          (0.000602:ℝ) * 1118.2 := mul_le_mul_of_nonneg_left h4a2.2 (by norm_num)
      linarith [hAtom, hδ1]
    · rw [div_le_iff₀ h4apos]
      linarith [hδ2]
  have hs2 := nb18_sqrt2
  have hsqrt2t : (2.8284:ℝ) ≤ Real.sqrt 2 * t ∧ Real.sqrt 2 * t ≤ (2.8426:ℝ) := by
    constructor
    · have h := mul_le_mul ht hs2.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul ht' hs2.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hkB : (-2.8426:ℝ) ≤ -(Real.sqrt 2 * t) ∧ -(Real.sqrt 2 * t) ≤ -(2.8284:ℝ) :=
    ⟨by linarith [hsqrt2t.2], by linarith [hsqrt2t.1]⟩
  have hDkPos : (90.99:ℝ) ≥ nb18dA y5 y6 t * (Real.sqrt 2 * t) := by
    have h := mul_le_mul hD2 hsqrt2t.2 (by linarith) (by norm_num)
    norm_num at h
    linarith [h]
  have hDkNeg : (90.47:ℝ) ≤ nb18dA y5 y6 t * (Real.sqrt 2 * t) := by
    have h := mul_le_mul hD3 hsqrt2t.1 (by norm_num) (by linarith)
    norm_num at h
    linarith [h]
  have hDk : (-90.99:ℝ) ≤ nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) ∧
      nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) ≤ -90.47 :=
    ⟨by linarith [hDkPos], by linarith [hDkNeg]⟩
  have h2a3 : (8912:ℝ) ≤
      2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t) ∧
      2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t) ≤ 9348 := by
    constructor
    · have h := mul_le_mul ha2.1 haB.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul ha2.2 haB.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hKQpos : (0:ℝ) < 2 *
      (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t) :=
    mul_pos (by norm_num) (mul_pos (mul_pos hafpos hafpos) hafpos)
  have hKQlo : (-0.0103:ℝ) ≤
      nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
        (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)) := by
    rw [le_div_iff₀ hKQpos]
    have hAtom : (0.0103:ℝ) *
        (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)) ≥
        (0.0103:ℝ) * 8912 := mul_le_mul_of_nonneg_left h2a3.1 (by norm_num)
    linarith [hAtom, hDk.1]
  have hKQhi : nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
      (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)) ≤
      -(0.0096:ℝ) := by
    rw [div_le_iff₀ hKQpos]
    have hAtom : (0.00967:ℝ) *
        (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)) ≤
        (0.00967:ℝ) * 9348 := mul_le_mul_of_nonneg_left h2a3.2 (by norm_num)
    norm_num at hAtom
    linarith [hAtom, hDk.2]
  have hdt : (0.0089:ℝ) ≤
      nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
        nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
          (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)) ∧
      nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
        nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
          (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)) ≤
      (0.0103:ℝ) := by
    constructor <;> linarith [hDQ.1, hDQ.2, hKQlo, hKQhi]
  have hθ := nb18_theta_br hD1 hD2 haB.1 haB.2
  have hmt := nb18_mt_br hθ.1 hθ.2
  have hmp := nb18_mp_br hθ.1 hθ.2
  have hmpd : (-0.00355:ℝ) ≤
      matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
          nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
            (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t))) ∧
      matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
          nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
            (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t))) ≤
      -(0.0028:ℝ) := by
    have hnegMP : (0.3189:ℝ) ≤
        -(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)))) ∧
        -(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)))) ≤
        (0.344:ℝ) := ⟨by linarith [hmp.2], by linarith [hmp.1]⟩
    have heq : matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
          nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
            (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t))) =
      -(-(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)))) *
        (nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
          nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
            (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t)))) := by ring
    constructor
    · rw [heq]
      have h := mul_le_mul hnegMP.2 hdt.2 (by linarith [hdt.1]) (by linarith [hnegMP.1])
      linarith [h, show (0.344:ℝ) * 0.0103 ≤ (0.00355:ℝ) from by norm_num]
    · rw [heq]
      have h := mul_le_mul hnegMP.1 hdt.1 (by linarith [hdt.1]) (by linarith [hnegMP.1])
      linarith [h, show (0.3189:ℝ) * 0.0089 ≥ (0.0028:ℝ) from by norm_num]
  have hmtk : (-2.817:ℝ) ≤
      matan (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (-(Real.sqrt 2 * t)) ∧
      matan (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (-(Real.sqrt 2 * t)) ≤ -2.799 := by
    have hnegkB : (2.8284:ℝ) ≤ Real.sqrt 2 * t ∧ Real.sqrt 2 * t ≤ 2.8426 :=
      ⟨by linarith [hsqrt2t.1], by linarith [hsqrt2t.2]⟩
    have heq : matan (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (-(Real.sqrt 2 * t)) =
      -(matan (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (Real.sqrt 2 * t)) := by ring
    constructor
    · rw [heq]
      have h := mul_le_mul hmt.2 hnegkB.2 (by linarith [hnegkB.1]) (by norm_num)
      norm_num at h
      linarith [h]
    · rw [heq]
      have h := mul_le_mul hmt.1 hnegkB.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
  have hκ : HasDerivAt (nb18afB y5 y6) (-(Real.sqrt 2 * t)) t := by
    have hA' : HasDerivAt
        (fun w : ℝ => (Real.sqrt 2 / 2) * ((y5 * y5) + (y6 * y6)) +
          -(Real.sqrt 2 / 2) * (w * w)) (0 + -(Real.sqrt 2 / 2) * (2 * t)) t :=
      HasDerivAt.fun_add (hasDerivAt_const t _)
        ((nb18_sq_deriv t).const_mul (-(Real.sqrt 2 / 2)))
    have hA : HasDerivAt
        (fun w : ℝ => Real.sqrt 2 * ((y5 * y5) + (y6 * y6) - (w * w)) / 2)
        (-(Real.sqrt 2 / 2) * (2 * t)) t := by
      refine hA'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun w => by ring)) |>.congr_deriv (by ring)
    have hc1 : HasDerivAt (fun w : ℝ => Real.sqrt 2 * (y6 * y5)) 0 t :=
      hasDerivAt_const t _
    have hc2 : HasDerivAt
        (fun w : ℝ => y6 * (y5 * y5 / 2) + y5 * (y6 * y6 / 2)) 0 t :=
      hasDerivAt_const t _
    have hb2 : HasDerivAt (nb18afB y5 y6)
        (0 + (0 + -(Real.sqrt 2 / 2) * (2 * t))) t := by
      refine (hc1.add (hc2.add hA)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w _
      rw [nb18afB_eq]
      simp only [Pi.add_apply]
      ring
    exact hb2.congr_deriv (by ring)
  have harg : (0:ℝ) < nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) :=
    div_pos (by linarith) (mul_pos (by norm_num) (mul_pos hafpos hafpos))
  have hchain := nb18_hasDerivAt_sol hΔf hκ hafpos harg
  refine ⟨(matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
          nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) / (2 * nb18afB y5 y6 t ^ 3)) /
      nb18afB y5 y6 t -
    matan (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (-(Real.sqrt 2 * t)) / nb18afB y5 y6 t ^ 2), ?_, ?_⟩
  · refine hchain.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    exact nb18_solB_eq y5 y6 w (by linarith) (by linarith) hw
  · rw [show nb18afB y5 y6 t ^ 2 = nb18afB y5 y6 t * nb18afB y5 y6 t from pow_two _,
      show nb18afB y5 y6 t ^ 3 =
        nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t from by
        rw [pow_succ, pow_two]]
    have hT1 : matanDerivPos (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
        (nb18dA' y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t)) -
          nb18dA y5 y6 t * (-(Real.sqrt 2 * t)) /
            (2 * (nb18afB y5 y6 t * nb18afB y5 y6 t * nb18afB y5 y6 t))) /
      nb18afB y5 y6 t ≤ -(0.0001:ℝ) := by
      rw [div_le_iff₀ hafpos]
      have hAtom : (0.0001:ℝ) * nb18afB y5 y6 t ≤ (0.0001:ℝ) * 16.7194 :=
        mul_le_mul_of_nonneg_left haB.2 (by norm_num)
      linarith [hmpd.2, hAtom]
    have hT2 : -(0.0105:ℝ) ≤
        matan (nb18dA y5 y6 t / (4 * (nb18afB y5 y6 t * nb18afB y5 y6 t))) *
          (-(Real.sqrt 2 * t)) / (nb18afB y5 y6 t * nb18afB y5 y6 t) := by
      rw [le_div_iff₀ (mul_pos hafpos hafpos)]
      have hAtom : (0.0105:ℝ) * 270.82 ≤
          (0.0105:ℝ) * (nb18afB y5 y6 t * nb18afB y5 y6 t) :=
        mul_le_mul_of_nonneg_left ha2.1 (by norm_num)
      norm_num at hAtom
      linarith [hmtk.1, hAtom]
    linarith [hT1, hT2]

set_option maxHeartbeats 800000 in
/-- DA-slot derivative along the axis with its lower bound
(includes the `lfun (w/2)` product factor). -/
private theorem nb18_dihA_slot (y5 y6 t : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    ∃ d : ℝ, HasDerivAt
        (fun w => lfun (w / 2) * dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2
          (y5 * y5) 2) d t ∧
      -(0.3174:ℝ) ≤ d := by
  obtain ⟨hD1, hD2, hD3, hδ1, hδ2, hΔf⟩ := nb18_ax_core y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  have hu2 := nb18_box2 hy5 hy5'
  have hv2 := nb18_box2 hy6 hy6'
  have ht2 := nb18_box2 ht ht'
  have hlfun := nb18_lfun_half_br ht ht'
  have hQ : (3.9599:ℝ) ≤ nb18axQ y5 y6 t ∧ nb18axQ y5 y6 t ≤ 4.0802 := by
    constructor <;> rw [nb18axQ_eq] <;> linarith [hu2.1, hu2.2, hv2.1, hv2.2, ht2.1, ht2.2]
  have htQpos : (0:ℝ) < t * nb18axQ y5 y6 t :=
    mul_pos (lt_of_lt_of_le (by norm_num) ht) (lt_of_lt_of_le (by norm_num) hQ.1)
  have htQ : (7.9198:ℝ) ≤ t * nb18axQ y5 y6 t ∧ t * nb18axQ y5 y6 t ≤ 8.201202 := by
    constructor
    · have h := mul_le_mul ht hQ.1 (by norm_num) (by linarith)
      norm_num at h
      linarith [h]
    · have h := mul_le_mul ht' hQ.2 (by linarith) (by norm_num)
      norm_num at h
      linarith [h]
  have hQ2pos : (0:ℝ) < (t * nb18axQ y5 y6 t) ^ 2 := pow_pos htQpos 2
  have hQ2 : (62.7232:ℝ) ≤ (t * nb18axQ y5 y6 t) ^ 2 ∧
      (t * nb18axQ y5 y6 t) ^ 2 ≤ 67.2601 := by
    constructor
    · have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 7.9198) htQ.1
      norm_num at h
      rw [pow_two]
      linarith [h]
    · have h := mul_self_le_mul_self htQpos.le htQ.2
      norm_num at h
      rw [pow_two]
      linarith [h]
  have hW : (0.2438:ℝ) ≤ nb18W y5 y6 t ∧ nb18W y5 y6 t ≤ 0.2526 := by
    rw [nb18W_eq]
    constructor
    · rw [le_div_iff₀ htQpos]
      have hAtom : (0.2438:ℝ) * (t * nb18axQ y5 y6 t) ≤ (0.2438:ℝ) * 8.201202 :=
        mul_le_mul_of_nonneg_left htQ.2 (by norm_num)
      linarith [hAtom, show (0.2438:ℝ) * 8.201202 ≤ (2:ℝ) from by norm_num]
    · rw [div_le_iff₀ htQpos]
      have hAtom : (0.2526:ℝ) * 7.9198 ≤ (0.2526:ℝ) * (t * nb18axQ y5 y6 t) :=
        mul_le_mul_of_nonneg_left htQ.1 (by norm_num)
      linarith [hAtom, show (2:ℝ) ≤ (0.2526:ℝ) * 7.9198 from by norm_num]
  have hP : (-4.1203:ℝ) ≤ nb18axQ y5 y6 t - 2 * t * t ∧
      nb18axQ y5 y6 t - 2 * t * t ≤ -(3.9198:ℝ) := by
    constructor <;> rw [nb18axQ_eq] <;>
      nlinarith [hu2.1, hu2.2, hv2.1, hv2.2, ht2.1, ht2.2]
  have hN : (7.8396:ℝ) ≤ -2 * (nb18axQ y5 y6 t - 2 * t * t) ∧
      -2 * (nb18axQ y5 y6 t - 2 * t * t) ≤ 8.2406 :=
    ⟨by linarith [hP.2], by linarith [hP.1]⟩
  have hω : (0.1165:ℝ) ≤ -2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) ∧
      -2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) ≤ (0.1314:ℝ) := by
    constructor
    · rw [le_div_iff₀ hQ2pos]
      have hAtom : (0.1165:ℝ) * ((t * nb18axQ y5 y6 t) ^ 2) ≤ (0.1165:ℝ) * 67.2601 :=
        mul_le_mul_of_nonneg_left hQ2.2 (by norm_num)
      linarith [hAtom, hN.1, show (7.8358:ℝ) ≤ (0.1165:ℝ) * 67.2601 from by norm_num]
    · rw [div_le_iff₀ hQ2pos]
      have hAtom : (0.1314:ℝ) * 62.7232 ≤ (0.1314:ℝ) * ((t * nb18axQ y5 y6 t) ^ 2) :=
        mul_le_mul_of_nonneg_left hQ2.1 (by norm_num)
      linarith [hAtom, hN.2, show (8.2406:ℝ) ≤ (0.1314:ℝ) * 62.7232 from by norm_num]
  have hdenEQ : ((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t) =
      (t * nb18axQ y5 y6 t) * (t * nb18axQ y5 y6 t) := by ring
  have hdenbr : (62.7232:ℝ) ≤
      ((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t) ∧
      ((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t) ≤ 67.2601 := by
    rw [hdenEQ, ← pow_two]
    exact hQ2
  have hdenpos : (0:ℝ) < ((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t) :=
    lt_of_lt_of_le (by norm_num) hdenbr.1
  have hGbr : (1.8831:ℝ) ≤ nb18G y5 y6 t ∧ nb18G y5 y6 t ≤ 2.0409 := by
    rw [nb18G_eq]
    have h4D : (126.676:ℝ) ≤ 4 * nb18dA y5 y6 t ∧ 4 * nb18dA y5 y6 t ≤ 128.002 :=
      ⟨by linarith [hD1], by linarith [hD2]⟩
    constructor
    · rw [le_div_iff₀ hdenpos]
      have hAtom : (1.8831:ℝ) * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ≤
          (1.8831:ℝ) * 67.2601 := mul_le_mul_of_nonneg_left hdenbr.2 (by norm_num)
      linarith [hAtom, h4D.1, show (1.8831:ℝ) * 67.2601 ≤ (126.676:ℝ) from by norm_num]
    · rw [div_le_iff₀ hdenpos]
      have hAtom : (2.0409:ℝ) * 62.7232 ≤
          (2.0409:ℝ) * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) :=
        mul_le_mul_of_nonneg_left hdenbr.1 (by norm_num)
      linarith [hAtom, h4D.2, show (128.002:ℝ) ≤ (2.0409:ℝ) * 62.7232 from by norm_num]
  obtain ⟨hmu1, hmu2, hmpu1, hmpu2⟩ := nb18_mu_mpu_br hGbr.1 hGbr.2
  -- derivative chains
  have hQ' : HasDerivAt (nb18axQ y5 y6) (-(2 * t)) t := by
    have hr : HasDerivAt (fun w : ℝ => (y5 * y5) + (y6 * y6) - w * w) (0 - 2 * t) t :=
      HasDerivAt.fun_sub (hasDerivAt_const t _) (nb18_sq_deriv t)
    refine hr.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => rfl)) |>.congr_deriv ?_
    ring
  have hdW : HasDerivAt (nb18W y5 y6)
      (-2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2)) t := by
    have hQd : HasDerivAt (fun w : ℝ => w * nb18axQ y5 y6 w)
        (nb18axQ y5 y6 t + t * (-(2 * t))) t :=
      ((hasDerivAt_id t).fun_mul hQ').congr_deriv (by simp only [id_eq]; ring)
    have hb := (hasDerivAt_const t (2:ℝ)).fun_div hQd (ne_of_gt htQpos)
    refine hb.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => rfl)) |>.congr_deriv ?_
    ring
  have hdG : HasDerivAt (nb18G y5 y6)
      ((4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
        4 * nb18dA y5 y6 t *
          (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
        ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2)) t := by
    have hQQ : HasDerivAt (fun w : ℝ => nb18axQ y5 y6 w * nb18axQ y5 y6 w)
        (nb18axQ y5 y6 t * (-(2 * t)) + nb18axQ y5 y6 t * (-(2 * t))) t :=
      (hQ'.fun_mul hQ').congr_deriv (by ring)
    have hden' : HasDerivAt
        (fun w : ℝ => (w * w) * (nb18axQ y5 y6 w * nb18axQ y5 y6 w))
        (2 * t * (nb18axQ y5 y6 t * nb18axQ y5 y6 t) +
          ((t:ℝ) * t) * (nb18axQ y5 y6 t * (-(2 * t)) + nb18axQ y5 y6 t * (-(2 * t)))) t :=
      ((nb18_sq_deriv t).fun_mul hQQ).congr_deriv (by ring)
    refine ((hΔf.const_mul (4:ℝ)).fun_div hden'
      (ne_of_gt hdenpos)).congr_deriv ?_
    ring
  have hchain := nb18_hasDerivAt_dih hdW hdG
    (lt_of_lt_of_le (by norm_num) hGbr.1)
  have hfull : HasDerivAt
      (fun w : ℝ => lfun (w / 2) * (nb18W y5 y6 w * matan (nb18G y5 y6 w)))
      (-(25 / 13:ℝ) * (nb18W y5 y6 t * matan (nb18G y5 y6 t)) +
        lfun (t / 2) *
          (-2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) *
              matan (nb18G y5 y6 t) +
            nb18W y5 y6 t * matanDerivPos (nb18G y5 y6 t) *
              ((4 * nb18dA' y5 y6 t *
                  (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
                4 * nb18dA y5 y6 t *
                  (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
                ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2)))) t := by
    refine (nb18_lfun_half_deriv t).fun_mul hchain |>.congr_deriv ?_
    ring
  -- numeric stages
  have hrawub : nb18W y5 y6 t * matan (nb18G y5 y6 t) ≤ (0.1769:ℝ) := by
    have h0 : (0:ℝ) ≤ matan (nb18G y5 y6 t) := by linarith [hmu1]
    have h := mul_le_mul hW.2 hmu2 (by linarith [hmu2]) (by norm_num)
    linarith [h, show (0.2526:ℝ) * 0.6999 ≤ (0.1769:ℝ) from by norm_num]
  have hωmu : (0.0767:ℝ) ≤
      -2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) *
        matan (nb18G y5 y6 t) := by
    have h := mul_le_mul hω.1 hmu1 (by linarith [hmu1]) (by linarith [hω.1])
    linarith [h, show (0.0767:ℝ) ≤ (0.1165:ℝ) * 0.6586 from by norm_num]
  have hA : (-175.3:ℝ) ≤
      4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ∧
      4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ≤ 0 := by
    have h4δ : (4:ℝ) * nb18dA' y5 y6 t ≤ 0 := by linarith
    have h4δlo : (-(2.6052:ℝ)) ≤ 4 * nb18dA' y5 y6 t := by linarith
    constructor
    · have h1 := mul_le_mul_of_nonneg_right h4δlo hdenpos.le
      linarith [h1, show (-175.3:ℝ) ≤ (-2.6052:ℝ) * 67.2601 from by norm_num]
    · linarith [mul_le_mul_of_nonneg_right h4δ hdenpos.le]
  have hp1A : (15.8396:ℝ) ≤ 2 * t * nb18axQ y5 y6 t ∧
      2 * t * nb18axQ y5 y6 t ≤ 16.4025 := by
    have h2t : (4:ℝ) ≤ 2 * t ∧ 2 * t ≤ 4.02 := ⟨by linarith, by linarith⟩
    constructor
    · have h := mul_le_mul h2t.1 hQ.1 (by norm_num) (by linarith)
      linarith [h, show (15.8396:ℝ) ≤ (4:ℝ) * 3.9599 from by norm_num]
    · have h := mul_le_mul h2t.2 hQ.2 (by linarith) (by norm_num)
      linarith [h, show (4.02:ℝ) * 4.0802 ≤ (16.4025:ℝ) from by norm_num]
  have hddA : (-67.5844:ℝ) ≤
      (2 * t * nb18axQ y5 y6 t) * (nb18axQ y5 y6 t - 2 * t * t) ∧
      (2 * t * nb18axQ y5 y6 t) * (nb18axQ y5 y6 t - 2 * t * t) ≤ -(62.0876:ℝ) := by
    constructor
    · have hcS : (0:ℝ) ≤ 2 * t * nb18axQ y5 y6 t := by linarith [hp1A.1]
      have h1 := mul_le_mul_of_nonneg_right hP.1 hcS
      linarith [h1, show (-67.5844:ℝ) ≤ (-4.1203:ℝ) * 16.4025 from by norm_num]
    · have hcR0 : nb18axQ y5 y6 t - 2 * t * t ≤ 0 := by linarith [hP.2]
      have h1 := mul_le_mul_of_nonpos_right hp1A.1 hcR0
      linarith [h1, show (-3.9198:ℝ) * 15.8396 ≤ (-62.0876:ℝ) from by norm_num]
  have hB : (-8652:ℝ) ≤
      4 * nb18dA y5 y6 t * ((2 * t * nb18axQ y5 y6 t) * (nb18axQ y5 y6 t - 2 * t * t)) ∧
      4 * nb18dA y5 y6 t * ((2 * t * nb18axQ y5 y6 t) * (nb18axQ y5 y6 t - 2 * t * t)) ≤
      -(7865:ℝ) := by
    have h4D : (126.676:ℝ) ≤ 4 * nb18dA y5 y6 t ∧ 4 * nb18dA y5 y6 t ≤ 128.002 :=
      ⟨by linarith [hD1], by linarith [hD2]⟩
    have hc4D : (0:ℝ) ≤ 4 * nb18dA y5 y6 t := by linarith [hD1]
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hddA.1 hc4D
      linarith [h1, show (-8652:ℝ) ≤ (-67.5844:ℝ) * 128.002 from by norm_num]
    · have hcR : (2 * t * nb18axQ y5 y6 t) * (nb18axQ y5 y6 t - 2 * t * t) ≤ 0 :=
        by linarith [hddA.2]
      have h1 := mul_le_mul_of_nonpos_right h4D.1 hcR
      have h2 := mul_le_mul_of_nonneg_left hddA.2 hc4D
      linarith [h1, h2, show (126.676:ℝ) * (-62.0876:ℝ) ≤ (-7865:ℝ) from by norm_num]
  have hden2 : (3934.19:ℝ) ≤
      ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2) ∧
      ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2) ≤ 4523.93 := by
    constructor
    · have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 62.7232) hdenbr.1
      linarith [h, show (3934.19:ℝ) ≤ (62.7232:ℝ) * 62.7232 from by norm_num]
    · have h := mul_self_le_mul_self hdenpos.le hdenbr.2
      linarith [h, show (67.2601:ℝ) * 67.2601 ≤ (4523.93:ℝ) from by norm_num]
  have hden2pos : (0:ℝ) < ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hden2.1
  have hgam : (0:ℝ) ≤
      (4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
        4 * nb18dA y5 y6 t *
          (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
        ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2) ∧
      (4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
        4 * nb18dA y5 y6 t *
          (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
        ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2) ≤
      (2.2:ℝ) := by
    constructor
    · rw [le_div_iff₀ hden2pos]
      linarith [hA.1, hB.2]
    · rw [div_le_iff₀ hden2pos]
      have hAtom : (2.2:ℝ) * 3934.19 ≤
          (2.2:ℝ) * ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2) :=
        mul_le_mul_of_nonneg_left hden2.1 (by norm_num)
      norm_num at hAtom
      linarith [hAtom, hA.2, hB.1]
  have hraw' : (0.0233:ℝ) ≤
      -2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) *
          matan (nb18G y5 y6 t) +
        nb18W y5 y6 t * matanDerivPos (nb18G y5 y6 t) *
          ((4 * nb18dA' y5 y6 t *
              (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
            4 * nb18dA y5 y6 t *
              (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
            ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2)) := by
    have hMp : (0:ℝ) ≤ -(matanDerivPos (nb18G y5 y6 t)) ∧
        -(matanDerivPos (nb18G y5 y6 t)) ≤ (0.096:ℝ) :=
      ⟨by linarith [hmpu1], by linarith [hmpu2]⟩
    have hWMP : (0:ℝ) ≤ nb18W y5 y6 t * -(matanDerivPos (nb18G y5 y6 t)) :=
      mul_nonneg (by linarith [hW.1]) hMp.1
    have hWMPub : nb18W y5 y6 t * -(matanDerivPos (nb18G y5 y6 t)) ≤
        (0.2526:ℝ) * 0.096 := mul_le_mul hW.2 hMp.2 (by linarith [hMp.2]) (by norm_num)
    have hprodγ : nb18W y5 y6 t * -(matanDerivPos (nb18G y5 y6 t)) *
        ((4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
          4 * nb18dA y5 y6 t *
            (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
          ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2)) ≤
        (0.2526:ℝ) * 0.096 * 2.2 :=
      mul_le_mul hWMPub hgam.2 (by linarith [hgam.1]) (by norm_num)
    norm_num at hprodγ
    have heq : nb18W y5 y6 t * matanDerivPos (nb18G y5 y6 t) *
        ((4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
          4 * nb18dA y5 y6 t *
            (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
          ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2)) =
      -(nb18W y5 y6 t * -(matanDerivPos (nb18G y5 y6 t)) *
        ((4 * nb18dA' y5 y6 t * (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
          4 * nb18dA y5 y6 t *
            (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
          ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2))) := by ring
    rw [heq]
    linarith [hωmu, hprodγ]
  have hderiv : HasDerivAt
      (fun w => lfun (w / 2) * dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2
        (y5 * y5) 2)
      (-(25 / 13:ℝ) * (nb18W y5 y6 t * matan (nb18G y5 y6 t)) +
        lfun (t / 2) *
          (-2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) *
              matan (nb18G y5 y6 t) +
            nb18W y5 y6 t * matanDerivPos (nb18G y5 y6 t) *
              ((4 * nb18dA' y5 y6 t *
                  (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
                4 * nb18dA y5 y6 t *
                  (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
                ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2)))) t := by
    refine hfull.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    rw [nb18_dihA_eq y5 y6 w hw]
  refine ⟨(
      (-(25 / 13:ℝ) * (nb18W y5 y6 t * matan (nb18G y5 y6 t)) +
        lfun (t / 2) *
          (-2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) *
              matan (nb18G y5 y6 t) +
            nb18W y5 y6 t * matanDerivPos (nb18G y5 y6 t) *
              ((4 * nb18dA' y5 y6 t *
                  (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
                4 * nb18dA y5 y6 t *
                  (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
                ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2))))), hderiv, ?_⟩
  have hTerm1 : (25 / 13:ℝ) * (nb18W y5 y6 t * matan (nb18G y5 y6 t)) ≤
      (25 / 13:ℝ) * 0.1769 := mul_le_mul_of_nonneg_left hrawub (by norm_num)
  have hlfunraw : (0.980769:ℝ) * 0.0233 ≤ lfun (t / 2) *
      (-2 * (nb18axQ y5 y6 t - 2 * t * t) / ((t * nb18axQ y5 y6 t) ^ 2) *
          matan (nb18G y5 y6 t) +
        nb18W y5 y6 t * matanDerivPos (nb18G y5 y6 t) *
          ((4 * nb18dA' y5 y6 t *
              (((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) -
            4 * nb18dA y5 y6 t *
              (2 * t * nb18axQ y5 y6 t * (nb18axQ y5 y6 t - 2 * t * t))) /
            ((((t:ℝ) * t) * (nb18axQ y5 y6 t * nb18axQ y5 y6 t)) ^ 2))) :=
    mul_le_mul hlfun.1 hraw' (by norm_num) (by linarith [hlfun.1])
  linarith [hTerm1, hlfunraw,
    show (0.0228:ℝ) ≤ (0.980769:ℝ) * 0.0233 from by norm_num]

set_option maxHeartbeats 2400000 in
/-- DB/DC-slot derivative along the axis with its lower bound
(the `lfun (ya/2)` factor is constant along the axis). -/
private theorem nb18_dihY_slot (ya yb t : ℝ) (hya : 2 ≤ ya) (hya' : ya ≤ 2.01)
    (hyb : 2 ≤ yb) (hyb' : yb ≤ 2.01) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    ∃ d : ℝ, HasDerivAt
        (fun w => lfun (ya / 2) * dihXDivSqrtdeltaPosbranch (ya * ya) 2 (w * w) 2
          (yb * yb) 2) d t ∧
      -(0.1143:ℝ) ≤ d := by
  obtain ⟨hD1, hD2, hD3, hδ1, hδ2, hΔf⟩ := nb18_ax_core ya yb t hya hya' hyb hyb' ht ht'
  have hya2 := nb18_box2 hya hya'
  have hyb2 := nb18_box2 hyb hyb'
  have ht2 := nb18_box2 ht ht'
  have hlfun := nb18_lfun_half_br hya hya'
  have hRY : (3.9599:ℝ) ≤ nb18RY ya yb t ∧ nb18RY ya yb t ≤ 4.0802 := by
    constructor <;> rw [nb18RY_eq] <;> linarith
  have hRYpos : (0:ℝ) < nb18RY ya yb t := lt_of_lt_of_le (by norm_num) hRY.1
  have hya2pos : (0:ℝ) < ya * ya := lt_of_lt_of_le (by norm_num) hya2.1
  have hYaR : (7.9198:ℝ) ≤ ya * nb18RY ya yb t ∧ ya * nb18RY ya yb t ≤ 8.201202 := by
    constructor
    · have h := mul_le_mul hya hRY.1 (by norm_num) (by linarith)
      linarith [h, show (7.9198:ℝ) ≤ (2:ℝ) * 3.9599 from by norm_num]
    · have h := mul_le_mul hya' hRY.2 (by linarith) (by norm_num)
      linarith [h, show (2.01:ℝ) * 4.0802 ≤ (8.201202:ℝ) from by norm_num]
  have hYaRpos : (0:ℝ) < ya * nb18RY ya yb t :=
    mul_pos (lt_of_lt_of_le (by norm_num) hya) hRYpos
  have hYdenbr : (15.8396:ℝ) ≤ (ya * ya) * nb18RY ya yb t ∧
      (ya * ya) * nb18RY ya yb t ≤ 16.485 := by
    constructor
    · have h := mul_le_mul hya2.1 hRY.1 (by norm_num) (by linarith)
      linarith [h, show (15.8396:ℝ) ≤ (4:ℝ) * 3.9599 from by norm_num]
    · have h := mul_le_mul hya2.2 hRY.2 (by linarith) (by norm_num)
      linarith [h, show (4.0401:ℝ) * 4.0802 ≤ (16.485:ℝ) from by norm_num]
  have hYdenpos : (0:ℝ) < (ya * ya) * nb18RY ya yb t :=
    lt_of_lt_of_le (by norm_num) hYdenbr.1
  have hWYbr : (0.2426:ℝ) ≤ nb18WY ya yb t ∧ nb18WY ya yb t ≤ 0.2538 := by
    rw [nb18WY_eq]
    constructor
    · rw [le_div_iff₀ hYdenpos]
      have hAtom : (0.2426:ℝ) * ((ya * ya) * nb18RY ya yb t) ≤
          (0.2426:ℝ) * 16.485 := mul_le_mul_of_nonneg_left hYdenbr.2 (by norm_num)
      linarith [hAtom, hya, show (0.2426:ℝ) * 16.485 ≤ (4:ℝ) from by norm_num]
    · rw [div_le_iff₀ hYdenpos]
      have hAtom : (0.2538:ℝ) * 15.8396 ≤
          (0.2538:ℝ) * ((ya * ya) * nb18RY ya yb t) :=
        mul_le_mul_of_nonneg_left hYdenbr.1 (by norm_num)
      linarith [hAtom, show (2:ℝ) ≤ (0.2538:ℝ) * 15.8396 from by norm_num]
  have hYden2 : (250.89:ℝ) ≤ ((ya * ya) * nb18RY ya yb t) ^ 2 ∧
      ((ya * ya) * nb18RY ya yb t) ^ 2 ≤ 271.76 := by
    constructor
    · have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 15.8396) hYdenbr.1
      linarith [h, show (250.89:ℝ) ≤ (15.8396:ℝ) * 15.8396 from by norm_num]
    · have h := mul_self_le_mul_self hYdenpos.le hYdenbr.2
      linarith [h, show (16.485:ℝ) * 16.485 ≤ (271.76:ℝ) from by norm_num]
  have hYden2pos : (0:ℝ) < ((ya * ya) * nb18RY ya yb t) ^ 2 :=
    lt_of_lt_of_le (by norm_num) hYden2.1
  have hNY : (64:ℝ) ≤ 2 * ya * ((ya * ya) * (2 * t)) ∧
      2 * ya * ((ya * ya) * (2 * t)) ≤ 65.291 := by
    have h2t : (4:ℝ) ≤ 2 * t ∧ 2 * t ≤ 4.02 := ⟨by linarith [ht], by linarith⟩
    have hsqr : (16:ℝ) ≤ (ya * ya) * (2 * t) ∧
        (ya * ya) * (2 * t) ≤ 16.2413 := by
      constructor
      · have h := mul_le_mul hya2.1 h2t.1 (by linarith) (by linarith [hya2.1])
        linarith [h, show (16:ℝ) ≤ (4:ℝ) * 4 from by norm_num]
      · have h := mul_le_mul hya2.2 h2t.2 (by linarith) (by norm_num)
        linarith [h, show (4.02:ℝ) * 4.02 ≤ (16.2413:ℝ) from by norm_num]
    have h2ya : (4:ℝ) ≤ 2 * ya ∧ 2 * ya ≤ 4.02 := ⟨by linarith, by linarith⟩
    constructor
    · have h := mul_le_mul h2ya.1 hsqr.1 (by norm_num) (by linarith)
      linarith [h, show (64:ℝ) ≤ (4:ℝ) * 16 from by norm_num]
    · have h := mul_le_mul h2ya.2 hsqr.2 (by linarith) (by norm_num)
      linarith [h, show (4.02:ℝ) * 16.2413 ≤ (65.291:ℝ) from by norm_num]
  have hω : (-0.2603:ℝ) ≤
      -(2 * ya * ((ya * ya) * (2 * t))) / (((ya * ya) * nb18RY ya yb t) ^ 2) ∧
      -(2 * ya * ((ya * ya) * (2 * t))) / (((ya * ya) * nb18RY ya yb t) ^ 2) ≤
      -(0.2355:ℝ) := by
    constructor
    · rw [le_div_iff₀ hYden2pos]
      have hAtom : (0.2603:ℝ) * 250.89 ≤
          (0.2603:ℝ) * (((ya * ya) * nb18RY ya yb t) ^ 2) :=
        mul_le_mul_of_nonneg_left hYden2.1 (by norm_num)
      linarith [hAtom, hNY.2, show (65.291:ℝ) ≤ (0.2603:ℝ) * 250.89 from by norm_num]
    · rw [div_le_iff₀ hYden2pos]
      have hAtom : (0.2355:ℝ) * (((ya * ya) * nb18RY ya yb t) ^ 2) ≤
          (0.2355:ℝ) * 271.76 :=
        mul_le_mul_of_nonneg_left hYden2.2 (by norm_num)
      linarith [hAtom, hNY.1, show (0.2355:ℝ) * 271.76 ≤ (64:ℝ) from by norm_num]
  have hdenEQ : ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) =
      (ya * nb18RY ya yb t) * (ya * nb18RY ya yb t) := by ring
  have hGYdenbr : (62.7232:ℝ) ≤
      (ya * ya) * (nb18RY ya yb t * nb18RY ya yb t) ∧
      (ya * ya) * (nb18RY ya yb t * nb18RY ya yb t) ≤ 67.2601 := by
    rw [hdenEQ]
    constructor
    · have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 7.9198) hYaR.1
      norm_num at h
      rw [← pow_two]
      linarith [h]
    · have h := mul_self_le_mul_self hYaRpos.le hYaR.2
      norm_num at h
      rw [← pow_two]
      linarith [h]
  have hGYdenpos : (0:ℝ) < (ya * ya) * (nb18RY ya yb t * nb18RY ya yb t) :=
    lt_of_lt_of_le (by norm_num) hGYdenbr.1
  have hGbr : (1.8831:ℝ) ≤ nb18GY ya yb t ∧ nb18GY ya yb t ≤ 2.0409 := by
    rw [nb18GY_eq]
    have h4D : (126.676:ℝ) ≤ 4 * nb18dA ya yb t ∧ 4 * nb18dA ya yb t ≤ 128.002 :=
      ⟨by linarith [hD1], by linarith [hD2]⟩
    constructor
    · rw [le_div_iff₀ hGYdenpos]
      have hAtom : (1.8831:ℝ) * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ≤
          (1.8831:ℝ) * 67.2601 := mul_le_mul_of_nonneg_left hGYdenbr.2 (by norm_num)
      norm_num at hAtom
      linarith [hAtom, h4D.1]
    · rw [div_le_iff₀ hGYdenpos]
      have hAtom : (2.0409:ℝ) * 62.7232 ≤
          (2.0409:ℝ) * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) :=
        mul_le_mul_of_nonneg_left hGYdenbr.1 (by norm_num)
      norm_num at hAtom
      linarith [hAtom, h4D.2]
  obtain ⟨hmu1, hmu2, hmpu1, hmpu2⟩ := nb18_mu_mpu_br hGbr.1 hGbr.2
  have hRY' : HasDerivAt (nb18RY ya yb) ((2:ℝ) * t) t := by
    have hr := HasDerivAt.fun_sub
      ((nb18_sq_deriv t).add (hasDerivAt_const t (yb * yb)))
      (hasDerivAt_const t (ya * ya))
    refine hr.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => rfl)) |>.congr_deriv ?_
    ring
  have hdWY : HasDerivAt (nb18WY ya yb)
      (-(2 * ya * ((ya * ya) * (2 * t))) /
        (((ya * ya) * nb18RY ya yb t) ^ 2)) t := by
    have hQd : HasDerivAt (fun w : ℝ => (ya * ya) * nb18RY ya yb w)
        ((ya * ya) * (2 * t)) t :=
      ((hasDerivAt_const t _).fun_mul hRY').congr_deriv (by ring)
    have hb := (hasDerivAt_const t (2 * ya)).fun_div hQd (ne_of_gt hYdenpos)
    refine hb.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => rfl)) |>.congr_deriv ?_
    ring
  have hdGY : HasDerivAt (nb18GY ya yb)
      ((4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
        4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
        (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)) t := by
    have hRR : HasDerivAt (fun w : ℝ => nb18RY ya yb w * nb18RY ya yb w)
        (nb18RY ya yb t * (2 * t) + nb18RY ya yb t * (2 * t)) t :=
      (hRY'.fun_mul hRY').congr_deriv (by ring)
    have hden' : HasDerivAt
        (fun w : ℝ => (ya * ya) * (nb18RY ya yb w * nb18RY ya yb w))
        ((ya * ya) * (nb18RY ya yb t * (2 * t) + nb18RY ya yb t * (2 * t))) t :=
      ((hasDerivAt_const t ((ya:ℝ) * ya)).fun_mul hRR).congr_deriv (by ring)
    refine ((hΔf.const_mul (4:ℝ)).fun_div hden'
      (ne_of_gt hGYdenpos)).congr_deriv ?_
    ring
  have hchain := nb18_hasDerivAt_dih hdWY hdGY
    (lt_of_lt_of_le (by norm_num) hGbr.1)
  have hfull : HasDerivAt
      (fun w : ℝ => lfun (ya / 2) * (nb18WY ya yb w * matan (nb18GY ya yb w)))
      (lfun (ya / 2) *
          (-(2 * ya * ((ya * ya) * (2 * t))) /
              (((ya * ya) * nb18RY ya yb t) ^ 2) * matan (nb18GY ya yb t) +
            nb18WY ya yb t * matanDerivPos (nb18GY ya yb t) *
              ((4 * nb18dA' ya yb t *
                  ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
                4 * nb18dA ya yb t *
                  ((ya * ya) * (4 * t * nb18RY ya yb t))) /
                (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)))) t := by
    refine (hasDerivAt_const t (lfun (ya / 2))).fun_mul hchain |>.congr_deriv ?_
    ring
  have hωmu : (-0.1823:ℝ) ≤
      -(2 * ya * ((ya * ya) * (2 * t))) / (((ya * ya) * nb18RY ya yb t) ^ 2) *
        matan (nb18GY ya yb t) := by
    have hmupos : (0:ℝ) ≤ matan (nb18GY ya yb t) := by linarith [hmu1]
    have hstep1 := mul_le_mul_of_nonneg_right hω.1 hmupos
    have hc0 : (-0.2603:ℝ) ≤ 0 := by norm_num
    have hstep2 := mul_le_mul_of_nonpos_right hmu2 hc0
    linarith [hstep1, hstep2,
      show (-(0.1823:ℝ)) ≤ (-(0.2603:ℝ)) * 0.6999 from by norm_num]
  have hA' : (-175.3:ℝ) ≤
      4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ∧
      4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ≤ 0 := by
    have h4δ : (4:ℝ) * nb18dA' ya yb t ≤ 0 := by linarith
    have h4δlo : (-(2.6052:ℝ)) ≤ 4 * nb18dA' ya yb t := by linarith
    constructor
    · have h1 := mul_le_mul_of_nonpos_left hGYdenbr.2 (by norm_num : (-(2.6052:ℝ)) ≤ 0)
      have h2 := mul_le_mul_of_nonneg_right h4δlo hGYdenpos.le
      linarith [h1, h2]
    · linarith [mul_le_mul_of_nonneg_right h4δ hGYdenpos.le]
  have h4tRY : (31.6792:ℝ) ≤ 4 * t * nb18RY ya yb t ∧
      4 * t * nb18RY ya yb t ≤ 32.8049 := by
    constructor
    · have h := mul_le_mul (show (8:ℝ) ≤ 4 * t by linarith) hRY.1 (by norm_num)
        (by linarith)
      linarith [h, show (31.6792:ℝ) ≥ (8:ℝ) * 3.9599 from by norm_num]
    · have h := mul_le_mul (show (4:ℝ) * t ≤ 8.04 by linarith) hRY.2 (by linarith)
        (by linarith)
      linarith [h, show (8.04:ℝ) * 4.0802 ≤ (32.8049:ℝ) from by norm_num]
  have hYa4 : (126.716:ℝ) ≤ (ya * ya) * (4 * t * nb18RY ya yb t) ∧
      (ya * ya) * (4 * t * nb18RY ya yb t) ≤ 132.537 := by
    constructor
    · have h := mul_le_mul hya2.1 h4tRY.1 (by linarith) (by linarith [hya2.1])
      linarith [h, show (126.716:ℝ) ≤ (4:ℝ) * 31.6792 from by norm_num]
    · have h := mul_le_mul hya2.2 h4tRY.2 (by linarith) (by norm_num)
      linarith [h, show (4.0401:ℝ) * 32.8049 ≤ (132.537:ℝ) from by norm_num]
  have hB' : (16210:ℝ) ≤
      4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t)) ∧
      4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t)) ≤ 16973 := by
    have h4D : (127.948:ℝ) ≤ 4 * nb18dA ya yb t ∧
        4 * nb18dA ya yb t ≤ 128.002 := ⟨by linarith [hD3], by linarith [hD2]⟩
    constructor
    · have h := mul_le_mul h4D.1 hYa4.1 (by linarith) (by linarith [h4D.1])
      linarith [h, show (16210:ℝ) ≤ (127.948:ℝ) * 126.716 from by norm_num]
    · have h := mul_le_mul h4D.2 hYa4.2 (by linarith) (by norm_num)
      linarith [h, show (128.002:ℝ) * 132.537 ≤ (16973:ℝ) from by norm_num]
  have hGYden2 : (3934.19:ℝ) ≤
      (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) ∧
      (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) ≤ 4523.93 := by
    constructor
    · have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 62.7232) hGYdenbr.1
      linarith [h, show (3934.19:ℝ) ≤ (62.7232:ℝ) * 62.7232 from by norm_num]
    · have h := mul_self_le_mul_self hGYdenpos.le hGYdenbr.2
      linarith [h, show (67.2601:ℝ) * 67.2601 ≤ (4523.93:ℝ) from by norm_num]
  have hGYden2pos : (0:ℝ) < (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hGYden2.1
  have hgam : (-4.36:ℝ) ≤
      (4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
        4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
        (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) ∧
      (4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
        4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
        (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) ≤
      -(3.58:ℝ) := by
    constructor
    · rw [le_div_iff₀ hGYden2pos]
      have hAtom : (4.36:ℝ) * 3934.19 ≤
          (4.36:ℝ) * (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) :=
        mul_le_mul_of_nonneg_left hGYden2.1 (by norm_num)
      linarith [hAtom, hA'.1, hB'.2]
    · rw [div_le_iff₀ hGYden2pos]
      have hAtom : (3.58:ℝ) * 3934.19 ≤
          (3.58:ℝ) * (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2) :=
        mul_le_mul_of_nonneg_left hGYden2.1 (by norm_num)
      linarith [hAtom, hA'.2, hB'.1]
  have hraw' : (-0.114:ℝ) ≤
      -(2 * ya * ((ya * ya) * (2 * t))) / (((ya * ya) * nb18RY ya yb t) ^ 2) *
          matan (nb18GY ya yb t) +
        nb18WY ya yb t * matanDerivPos (nb18GY ya yb t) *
          ((4 * nb18dA' ya yb t *
              ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
            4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
          (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)) := by
    have hMp : (0.079:ℝ) ≤ -(matanDerivPos (nb18GY ya yb t)) ∧
        -(matanDerivPos (nb18GY ya yb t)) ≤ (0.096:ℝ) :=
      ⟨by linarith [hmpu1], by linarith [hmpu2]⟩
    have hnegγ : (3.58:ℝ) ≤
        -((4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
            4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
          (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)) ∧
        -((4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
            4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
          (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)) ≤ (4.36:ℝ) :=
      ⟨by linarith [hgam.2], by linarith [hgam.1]⟩
    have hpg1 : (0.079:ℝ) * 3.58 ≤
        -(matanDerivPos (nb18GY ya yb t)) *
          -((4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
              4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
            (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)) :=
      mul_le_mul hMp.1 hnegγ.1 (by linarith) (by linarith [hMp.1])
    norm_num at hpg1
    have hpg2 : -(matanDerivPos (nb18GY ya yb t)) *
        -((4 * nb18dA' ya yb t * ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
            4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
          (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)) ≤
        (0.096:ℝ) * 4.36 :=
      mul_le_mul hMp.2 hnegγ.2 (by linarith [hnegγ.2]) (by norm_num)
    norm_num at hpg2
    have hpg3 := mul_le_mul hWYbr.1 hpg1 (by linarith) (by linarith [hWYbr.1])
    norm_num at hpg3
    linarith [hωmu, hpg1, hpg3]
  have hderiv : HasDerivAt
      (fun w => lfun (ya / 2) * dihXDivSqrtdeltaPosbranch (ya * ya) 2 (w * w) 2
        (yb * yb) 2)
      (lfun (ya / 2) *
          (-(2 * ya * ((ya * ya) * (2 * t))) /
              (((ya * ya) * nb18RY ya yb t) ^ 2) * matan (nb18GY ya yb t) +
            nb18WY ya yb t * matanDerivPos (nb18GY ya yb t) *
              ((4 * nb18dA' ya yb t *
                  ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
                4 * nb18dA ya yb t *
                  ((ya * ya) * (4 * t * nb18RY ya yb t))) /
                (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2)))) t := by
    refine hfull.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    rw [nb18_dihY_eq ya yb w (by linarith) hw]
  refine ⟨(
      (lfun (ya / 2) *
          (-(2 * ya * ((ya * ya) * (2 * t))) /
              (((ya * ya) * nb18RY ya yb t) ^ 2) * matan (nb18GY ya yb t) +
            nb18WY ya yb t * matanDerivPos (nb18GY ya yb t) *
              ((4 * nb18dA' ya yb t *
                  ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
                4 * nb18dA ya yb t *
                  ((ya * ya) * (4 * t * nb18RY ya yb t))) /
                (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2))))), hderiv, ?_⟩
  have hstep1 : lfun (ya / 2) *
      (-(2 * ya * ((ya * ya) * (2 * t))) / (((ya * ya) * nb18RY ya yb t) ^ 2) *
          matan (nb18GY ya yb t) +
        nb18WY ya yb t * matanDerivPos (nb18GY ya yb t) *
          ((4 * nb18dA' ya yb t *
              ((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) -
            4 * nb18dA ya yb t * ((ya * ya) * (4 * t * nb18RY ya yb t))) /
          (((ya * ya) * (nb18RY ya yb t * nb18RY ya yb t)) ^ 2))) ≥
      lfun (ya / 2) * -(0.114:ℝ) :=
    mul_le_mul_of_nonneg_left hraw' (by linarith [hlfun.1])
  have hstep2 : (-(0.114:ℝ)) ≤ -(0.114:ℝ) * lfun (ya / 2) := by
    have h := mul_le_mul_of_nonpos_left hlfun.2 (by norm_num : (-(0.114:ℝ)) ≤ 0)
    rw [mul_one] at h
    linarith
  linarith [hstep1, hstep2]

set_option maxHeartbeats 800000 in
/-- **The y4-axis derivative exists and is bounded below by `0.0094 > 0`.** -/
private theorem nb18_axis_deriv (y5 y6 : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) (t : ℝ) (ht : 2 ≤ t) (ht' : t ≤ 2.01) :
    (∃ dv : ℝ, HasDerivAt (fun w => pc3 w y5 y6) dv t ∧
        (0.0094:ℝ) ≤ deriv (fun w => pc3 w y5 y6) t) := by
  obtain ⟨dA, hdA, hAb⟩ := nb18_solA_slot y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  obtain ⟨dB, hdB, hBb⟩ := nb18_solB_slot y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  obtain ⟨dC, hdC, hCb⟩ := nb18_solC_slot y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  obtain ⟨eA, heA, eAb⟩ := nb18_dihA_slot y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  obtain ⟨eB, heB, eBb⟩ := nb18_dihY_slot y5 y6 t hy5 hy5' hy6 hy6' ht ht'
  obtain ⟨eC0, heC0, eCb⟩ := nb18_dihY_slot y6 y5 t hy6 hy6' hy5 hy5' ht ht'
  have heC : HasDerivAt
      (fun w : ℝ => lfun (y6 / 2) *
        dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (w * w) 2) eC0 t := by
    refine heC0.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    rw [nb18_dih_swap23 (y6 * y6) (w * w) (y5 * y5)]
  have hK1 := nb18_k1
  have hK2 := nb18_k2
  have hsolsum : HasDerivAt
      (fun w : ℝ => solEulerXDivSqrtdelta (y5 * y5) 2 (w * w) 2 (y6 * y6) 2 +
        (solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (w * w) 2 +
          solEulerXDivSqrtdelta (w * w) 2 (y6 * y6) 2 (y5 * y5) 2)) (dA + (dB + dC)) t :=
    hdA.add (hdB.add hdC)
  have hdihsum : HasDerivAt
      (fun w : ℝ => lfun (w / 2) * dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2
            (y5 * y5) 2 +
        (lfun (y5 / 2) * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (w * w) 2 (y6 * y6) 2 +
          lfun (y6 / 2) * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2
            (w * w) 2)) (eA + (eB + eC0)) t :=
    heA.add (heB.add heC)
  have hcomb : HasDerivAt
      (fun w : ℝ => 1 / 12 - (2 * mm1 / Real.pi) *
          (solEulerXDivSqrtdelta (y5 * y5) 2 (w * w) 2 (y6 * y6) 2 +
            solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (w * w) 2 +
            solEulerXDivSqrtdelta (w * w) 2 (y6 * y6) 2 (y5 * y5) 2) +
        (8 * mm2 / Real.pi) *
          (lfun (w / 2) * dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2
              (y5 * y5) 2 +
            lfun (y5 / 2) * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (w * w) 2
              (y6 * y6) 2 +
            lfun (y6 / 2) * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2
              (w * w) 2))
      (-(2 * mm1 / Real.pi) * (dA + (dB + dC)) +
        (8 * mm2 / Real.pi) * (eA + (eB + eC0))) t := by
    have h1 := hsolsum.const_mul (-(2 * mm1 / Real.pi))
    have h2 := hdihsum.const_mul ((8:ℝ) * mm2 / Real.pi)
    have hc := (hasDerivAt_const t ((1:ℝ) / 12)).add (h1.add h2)
    have hc2 : HasDerivAt
        (fun w : ℝ => 1 / 12 - (2 * mm1 / Real.pi) *
            (solEulerXDivSqrtdelta (y5 * y5) 2 (w * w) 2 (y6 * y6) 2 +
              solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (w * w) 2 +
              solEulerXDivSqrtdelta (w * w) 2 (y6 * y6) 2 (y5 * y5) 2) +
          (8 * mm2 / Real.pi) *
            (lfun (w / 2) * dihXDivSqrtdeltaPosbranch (w * w) 2 (y6 * y6) 2
                (y5 * y5) 2 +
              lfun (y5 / 2) * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (w * w) 2
                (y6 * y6) 2 +
              lfun (y6 / 2) * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2
                (w * w) 2))
      (-(2 * mm1 / Real.pi) * (dA + (dB + dC)) +
        (8 * mm2 / Real.pi) * (eA + (eB + eC0))) t := by
      refine hc.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w _
        simp only [Pi.add_apply]
        ring
      · ring
    exact hc2.congr_deriv (by ring)
  have hpc : HasDerivAt (fun w => pc3 w y5 y6)
      (-(2 * mm1 / Real.pi) * (dA + (dB + dC)) +
        (8 * mm2 / Real.pi) * (eA + (eB + eC0))) t := by
    refine hcomb.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t by linarith)] with w hw
    exact nb18_pc3_unfold y5 y6 w hw (by linarith) (by linarith)
  have hbound : (0.0094:ℝ) ≤ -(2 * mm1 / Real.pi) * (dA + (dB + dC)) +
      (8 * mm2 / Real.pi) * (eA + (eB + eC0)) := by
    have hS : dA + (dB + dC) ≤ -(0.0702:ℝ) := by linarith
    have hT : -(0.546:ℝ) ≤ eA + (eB + eC0) := by linarith
    have hp1 : (0.64425:ℝ) * 0.0702 ≤
        (2 * mm1 / Real.pi) * (-(dA + (dB + dC))) := by
      have hK1pos : (0:ℝ) ≤ 2 * mm1 / Real.pi := by linarith
      have hs_nonneg : (0.0702:ℝ) ≤ -(dA + (dB + dC)) := by linarith
      have h0702pos : (0:ℝ) ≤ (0.0702:ℝ) := by norm_num
      calc (0.64425:ℝ) * 0.0702 ≤ (2 * mm1 / Real.pi) * 0.0702 :=
          mul_le_mul_of_nonneg_right hK1.1 h0702pos
        _ ≤ (2 * mm1 / Real.pi) * (-(dA + (dB + dC))) :=
          mul_le_mul_of_nonneg_left hs_nonneg hK1pos
    have hp2 : (8 * mm2 / Real.pi) * (eA + (eB + eC0)) ≥
        -(0.06476:ℝ) * 0.546 := by
      have hK2pos : (0:ℝ) ≤ 8 * mm2 / Real.pi := by linarith
      have hstep1 : (8 * mm2 / Real.pi) * (eA + (eB + eC0)) ≥
          (8 * mm2 / Real.pi) * (-(0.546:ℝ)) := mul_le_mul_of_nonneg_left hT hK2pos
      have hstep2 : (8 * mm2 / Real.pi) * (-(0.546:ℝ)) ≥
          (0.06476:ℝ) * (-(0.546:ℝ)) := by
        have h := mul_le_mul_of_nonpos_left hK2.2 (by norm_num : (-(0.546:ℝ)) ≤ 0)
        linarith [h]
      linarith [hstep1, hstep2]
    have hnf1 : (0.64425:ℝ) * 0.0702 ≥ (0.0452:ℝ) := by norm_num
    have hnf2 : (0.06476:ℝ) * 0.546 ≤ (0.03536:ℝ) := by norm_num
    linarith [hp1, hp2, hnf1, hnf2]
  exact ⟨(-(2 * mm1 / Real.pi) * (dA + (dB + dC)) +
      (8 * mm2 / Real.pi) * (eA + (eB + eC0))), hpc, hbound.trans hpc.deriv.ge⟩

/-! ## 9. Axis monotonicity and cyclic transfer -/

/-- step0: the kernel is monotone (increasing) along the first free coordinate. -/
private theorem nb18_step0 (y5 y6 : ℝ) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) :
    MonotoneOn (fun w => pc3 w y5 y6) (Set.Icc 2 2.01) := by
  have hdiff : ∀ x ∈ Set.Icc 2 2.01, DifferentiableAt ℝ (fun w => pc3 w y5 y6) x := by
    intro x hx
    obtain ⟨dv, hdv, -⟩ := nb18_axis_deriv y5 y6 hy5 hy5' hy6 hy6' x hx.1 hx.2
    exact hdv.differentiableAt
  have hcont : ContinuousOn (fun w => pc3 w y5 y6) (Set.Icc 2 2.01) := by
    intro x hx
    obtain ⟨dv, hdv, -⟩ := nb18_axis_deriv y5 y6 hy5 hy5' hy6 hy6' x hx.1 hx.2
    exact hdv.continuousAt.continuousWithinAt
  have hdiffint : DifferentiableOn ℝ (fun w => pc3 w y5 y6)
      (interior (Set.Icc 2 2.01)) := by
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨dv, hdv, -⟩ := nb18_axis_deriv y5 y6 hy5 hy5' hy6 hy6' x
      (le_of_lt hx.1) (le_of_lt hx.2)
    exact hdv.differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc (2:ℝ) 2.01) hcont hdiffint ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨dv, hdv, hdvpos⟩ := nb18_axis_deriv y5 y6 hy5 hy5' hy6 hy6' x
    (le_of_lt hx.1) (le_of_lt hx.2)
  rw [hdv.deriv] at hdvpos ⊢
  linarith

/-- step 1/2: cyclic transfer of the axis monotonicity. -/
private theorem nb18_step1 (y4 y5 y6 : ℝ) (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2.01)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) :
    pc3 y4 2 y6 ≤ pc3 y4 y5 y6 := by
  have e1 : pc3 y4 2 y6 = pc3 y6 y4 2 := nb18_cycle y6 y4 2
  have e0 : pc3 y6 y4 2 = pc3 2 y6 y4 := nb18_cycle 2 y6 y4
  have hmono := nb18_step0 y6 y4 hy6 hy6' hy4 hy4'
  have hma : (2:ℝ) ∈ Set.Icc 2 2.01 := ⟨le_rfl, by norm_num⟩
  have hmb : y5 ∈ Set.Icc 2 2.01 := ⟨hy5, hy5'⟩
  have e2 : pc3 2 y6 y4 ≤ pc3 y5 y6 y4 := hmono hma hmb hy5
  have e3 : pc3 y5 y6 y4 = pc3 y4 y5 y6 := nb18_cycle y4 y5 y6
  rw [e1, e0]
  exact e2.trans e3.le

/-- step 2/2: cyclic transfer of the axis monotonicity. -/
private theorem nb18_step2 (y4 y5 y6 : ℝ) (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2.01)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2.01) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2.01) :
    pc3 y4 y5 2 ≤ pc3 y4 y5 y6 := by
  have e1 : pc3 y4 y5 2 = pc3 2 y4 y5 := nb18_cycle 2 y4 y5
  have hmono := nb18_step0 y4 y5 hy4 hy4' hy5 hy5'
  have hma : (2:ℝ) ∈ Set.Icc 2 2.01 := ⟨le_rfl, by norm_num⟩
  have hmb : y6 ∈ Set.Icc 2 2.01 := ⟨hy6, hy6'⟩
  have e2 : pc3 2 y4 y5 ≤ pc3 y6 y4 y5 := hmono hma hmb hy6
  have e3 : pc3 y6 y4 y5 = pc3 y4 y5 y6 :=
    (nb18_cycle y5 y6 y4).trans (nb18_cycle y4 y5 y6)
  rw [e1]
  exact e2.trans e3.le

/-! ## 10. The bank -/

theorem nb18_bank_of_mono :
    bank_QZECFICwt0corner := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  rw [nb18_indep]
  have hw1 : pc3 2 2 2 ≤ pc3 y4 2 2 := by
    have hmono := nb18_step0 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hmono (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) (Set.mem_Icc.mpr ⟨h4, h4'⟩) h4
  have hw2 : pc3 y4 2 2 ≤ pc3 y4 y5 2 :=
    nb18_step1 y4 y5 2 h4 h4' h5 h5' (by norm_num) (by norm_num)
  have hw3 := nb18_step2 y4 y5 y6 h4 h4' h5 h5' h6 h6'
  have hcorner : pc3 2 2 2 = 0 := nb18_corner_zero
  linarith [hcorner, hw1, hw2, hw3]

/-- **The bank `QZECFIC wt0 corner` is proved: the cell-3 kernel is
nonnegative on `[1,1]³ × [2,2.01]³`.** -/
theorem nb18_bank : bank_QZECFICwt0corner := nb18_bank_of_mono

/-! ## 11. Axiom audit -/

#print axioms nb18_bank_of_mono
#print axioms nb18_bank


/-
Kepler.NliBanks20 — lanes `cell3-wt2a-core-w1` (machinery draft) and
`cell3-wt2a-core-w2` (machine-layer fixes + certificate): the 3D certificate
of the wt2A core `0 < w2aF` on `{deltaX ≥ 0}` over the Lean box, closing
`bank_QZECFICwt2A` via `Kepler.NliBanks19.bank_QZECFICwt2A_of_core`.

Route: 3D cells `(y4,y5) rectangle × y6 layer`; the generic `w2a_cell` lemma
takes the box, `0 ≤ deltaX`, and the rational corner bounds of one cell; each
cell is discharged by the corner monotonicity lemmas plus one rational
certificate checked by `norm_num`.  No derivative slot machinery.
w2 fixed: `nb20_not_halfpi`, `nb20_arctan_ge`, `nb20_matan_ge_taylor`,
`sol_euler5/6_eq` (ring-ordered sums), `dlt_anti_b/c` (true `4·b·c` family),
the nine `√2·(…)/2` mono sites, the `lfun` lemmas (Lean `lfun` has no ite),
and completed `dlt_corner` (was an interrupted stub).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks19

set_option maxHeartbeats 16000000

namespace Kepler.NliBanks20
open Kepler.Text
open Kepler.NliBanks19

/-! ## 1. `arctan` Taylor brackets and the constant brackets (K1, K2) -/

/-- The 17-term alternating arctan partial sum `Σ (−1)^k x^{2k+1}/(2k+1)`. -/
private noncomputable def nb20P (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)

/-- Its derivative sum `Σ (−1)^k x^{2k}`. -/
private noncomputable def nb20Q (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * k)

private theorem nb20_hd_term (x : ℝ) (k : ℕ) :
    HasDerivAt (fun y : ℝ => y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) (x ^ (2 * k)) x := by
  have hp : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
      (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) x :=
    hasDerivAt_pow (2 * k + 1) x
  have hc : (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) / ((2 * k + 1 : ℕ) : ℝ) = x ^ (2 * k) := by
    field_simp
  rw [← hc]
  exact hp.div_const ((2 * k + 1 : ℕ) : ℝ)

private theorem nb20_hasDerivAt_P (x : ℝ) : HasDerivAt nb20P (nb20Q x) x := by
  unfold nb20P
  refine HasDerivAt.fun_sum ?_
  intro k _
  refine (HasDerivAt.const_mul ((-1 : ℝ) ^ (k : ℕ)) (nb20_hd_term x k)).congr_of_eventuallyEq ?_
  filter_upwards with y
  ring

private theorem nb20_deriv_P (x : ℝ) : deriv nb20P x = nb20Q x :=
  (nb20_hasDerivAt_P x).deriv

private theorem nb20_Q_mul_go (x : ℝ) (n : ℕ) :
    (1 + x ^ 2) * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * k))
      = 1 + (-1 : ℝ) ^ n * x ^ (2 * n + 2) := by
  induction n with
  | zero => rw [Finset.sum_range_succ]; norm_num
  | succ n ih =>
    have hsg : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
      rw [pow_succ]; ring
    rw [Finset.sum_range_succ, mul_add, ih, hsg]
    ring

private theorem nb20_Q_mul (x : ℝ) : (1 + x ^ 2) * nb20Q x = 1 + x ^ 34 := by
  rw [nb20Q]
  have h := nb20_Q_mul_go x 16
  norm_num [pow_succ] at h
  linarith

private theorem nb20_cont_P : Continuous nb20P := by
  unfold nb20P; fun_prop

private theorem nb20_diff_P : Differentiable ℝ nb20P := by
  unfold nb20P; fun_prop

private theorem nb20_cont_f35 :
    Continuous (fun y : ℝ => Real.arctan y - nb20P y + y ^ 35 / (35:ℝ)) :=
  (Real.continuous_arctan.sub nb20_cont_P).add ((continuous_pow 35).div_const (35:ℝ))

private theorem nb20_diff_f35 :
    Differentiable ℝ (fun y : ℝ => Real.arctan y - nb20P y + y ^ 35 / (35:ℝ)) :=
  (Real.differentiable_arctan.sub nb20_diff_P).add ((differentiable_pow 35).div_const (35:ℝ))

private theorem nb20_P_strictMonoOn : StrictMonoOn nb20P (Set.Ici 0) := by
  refine strictMonoOn_of_deriv_pos (D := Set.Ici (0:ℝ)) (f := nb20P)
    (convex_Ici (0:ℝ)) nb20_cont_P.continuousOn ?_
  intro x hx
  have hx' : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
  rw [nb20_deriv_P]
  have h := nb20_Q_mul x
  have h2 : (0:ℝ) < 1 + x ^ 2 := by positivity
  by_contra hneg
  push_neg at hneg
  have hprod : (1 + x ^ 2) * nb20Q x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2.le hneg
  have hge0 : (0:ℝ) ≤ x ^ 34 := by positivity
  linarith [h, hprod, hge0]

/-- Upper bracket: `arctan s ≤ nb20P s` for `s ≥ 0`. -/
private theorem nb20_atan_le_P {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ nb20P s := by
  have h := Kepler.NliBanks12.nb12_nonneg_of_deriv
    (f := fun y : ℝ => nb20P y - Real.arctan y)
    (hC := nb20_cont_P.sub Real.continuous_arctan)
    (hD := nb20_diff_P.sub Real.differentiable_arctan)
    (h0 := by rw [nb20P]; simp)
    (hd := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => nb20P y - Real.arctan y)
          (nb20Q x - 1 / (1 + x ^ 2)) x :=
        (nb20_hasDerivAt_P x).sub (Real.hasDerivAt_arctan x)
      have hq : nb20Q x - 1 / (1 + x ^ 2) = x ^ 34 / (1 + x ^ 2) := by
        field_simp
        linarith [nb20_Q_mul x]
      rw [h1.deriv, hq]
      positivity) s hs
  linarith

/-- Lower bracket: `nb20P s − s³⁵/35 ≤ arctan s` for `s ≥ 0`. -/
private theorem nb20_series_le {s : ℝ} (hs : 0 ≤ s) :
    nb20P s - s ^ 35 / 35 ≤ Real.arctan s := by
  have h := Kepler.NliBanks12.nb12_nonneg_of_deriv
    (f := fun y : ℝ => Real.arctan y - nb20P y + y ^ 35 / 35)
    (hC := nb20_cont_f35)
    (hD := nb20_diff_f35)
    (h0 := by rw [nb20P]; simp)
    (hd := by
      intro x hx
      have h35 : HasDerivAt (fun y : ℝ => y ^ 35 / (35 : ℝ)) (x ^ 34) x := by
        simpa [pow_succ] using ((hasDerivAt_pow 35 x).div_const (35 : ℝ))
      have h1 : HasDerivAt (fun y : ℝ => Real.arctan y - nb20P y + y ^ 35 / (35 : ℝ))
          (1 / (1 + x ^ 2) - nb20Q x + x ^ 34) x :=
        ((Real.hasDerivAt_arctan x).sub (nb20_hasDerivAt_P x)).add h35
      have hq : 1 / (1 + x ^ 2) - nb20Q x + x ^ 34 = x ^ 36 / (1 + x ^ 2) := by
        field_simp
        rw [nb20_Q_mul x]
        ring
      rw [h1.deriv, hq]
      positivity) s hs
  linarith

/-- `arctan s + arctan (1/s) = π/2` for `s > 0`. -/
private theorem nb20_atan_add_inv {s : ℝ} (hs : 0 < s) :
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

/-- No odd multiple of `π/2` lies in an interval strictly inside `(0, π/2)`. -/
private theorem nb20_not_halfpi {x : ℝ} (hx : 0 < x) (hx' : x < Real.pi / 2) :
    ∀ k : ℤ, x ≠ (2 * k + 1) * Real.pi / 2 := by
  intro k hk
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rcases Int.lt_trichotomy k 0 with h | h | h
  · have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show (k:ℤ) ≤ -1 by omega)
    have hco : (2:ℝ) * (k:ℝ) + 1 ≤ -1 := by linarith
    have hxle : x ≤ -(Real.pi) / 2 := by
      rw [hk]
      have hmul : (2 * (k:ℝ) + 1) * Real.pi ≤ -(1:ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hco (le_of_lt hpi)
      linarith
    linarith
  · subst h
    norm_num at hk
    linarith
  · have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
    have hco : (3:ℝ) ≤ 2 * (k:ℝ) + 1 := by linarith
    have hxge : Real.pi / 2 ≤ x := by
      rw [hk]
      have h1 : (3:ℝ) * Real.pi ≤ (2 * (k:ℝ) + 1) * Real.pi :=
        mul_le_mul_of_nonneg_right hco (le_of_lt hpi)
      nlinarith [h1, hpi]
    linarith

/-- `√2` bracket. -/
private theorem nb20_sqrt2 : (1.41421356 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.4142136 := by
  refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
  · norm_num
  · rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 1.4142136)]
    norm_num

/-- `π` bracket (Mathlib decimal bounds). -/
private theorem nb20_pi : (3.141592 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 3.141593 :=
  ⟨Real.pi_gt_d6.le, Real.pi_lt_d6.le⟩

/-- `α = arctan (√2)` bracket. -/
private theorem nb20_alpha : (0.955316 : ℝ) ≤ Real.arctan (Real.sqrt 2) ∧
    Real.arctan (Real.sqrt 2) ≤ 0.955317 := by
  have hw : (0.7071067 : ℝ) ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 ≤ 0.7071068 := by
    have hs := nb20_sqrt2
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
    have h := nb20_atan_add_inv (show (0:ℝ) < Real.sqrt 2 by positivity)
    linarith
  rw [hid]
  constructor
  · have hP : Real.arctan (1 / Real.sqrt 2) ≤ nb20P 0.7071068 := by
      refine le_trans (nb20_atan_le_P hwpos.le) ?_
      exact nb20_P_strictMonoOn.monotoneOn (Set.mem_Ici.mpr hwpos.le)
        (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.7071068)) hwle
    have ev : nb20P 0.7071068 ≤ 0.61548 := by
      norm_num [nb20P]
    have hpi := nb20_pi
    nlinarith [hP.trans ev, hpi.1, hpi.2, Real.pi_pos]
  · have hP : nb20P (0.7071067 : ℝ) - (0.7071068 : ℝ) ^ 35 / 35 ≤
        Real.arctan (1 / Real.sqrt 2) := by
      have h1 := nb20_series_le (show (0:ℝ) ≤ 1 / Real.sqrt 2 by positivity)
      have hPmono : nb20P (0.7071067 : ℝ) ≤ nb20P (1 / Real.sqrt 2) :=
        nb20_P_strictMonoOn.monotoneOn
          (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 0.7071067))
          (Set.mem_Ici.mpr hwpos.le) hwge
      have hw35 : (1 / Real.sqrt 2) ^ 35 ≤ (0.7071068 : ℝ) ^ 35 := by
        gcongr
        all_goals { first | exact hwle | positivity | nlinarith [hwle, hwpos] }
      calc nb20P (0.7071067 : ℝ) - (0.7071068 : ℝ) ^ 35 / 35
          ≤ nb20P (1 / Real.sqrt 2) - (1 / Real.sqrt 2) ^ 35 / 35 := by
            nlinarith [hPmono, hw35]
        _ ≤ Real.arctan (1 / Real.sqrt 2) := h1
    have ev : (0.6154797 : ℝ) ≤ nb20P 0.7071067 := by
      norm_num [nb20P]
    have hrem : (0.7071068 : ℝ) ^ 35 / 35 ≤ 0.00000016 := by
      norm_num
    have hpi := nb20_pi
    nlinarith [hP, ev, hrem, hpi.1, hpi.2, Real.pi_pos]

/-- Corner identity 1: `arccos (1/3) = π − 2·arctan (√2)`. -/
private theorem nb20_arccos13 :
    Real.arccos (1 / 3) = Real.pi - 2 * Real.arctan (Real.sqrt 2) := by
  have hal := nb20_alpha
  have hrange : (0:ℝ) ≤ Real.pi - 2 * Real.arctan (Real.sqrt 2) ∧
      Real.pi - 2 * Real.arctan (Real.sqrt 2) ≤ Real.pi := by
    constructor
    · nlinarith [hal.1, hal.2, nb20_pi.1, nb20_pi.2, Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi - 2 * Real.arctan (Real.sqrt 2)) = 1 / 3 := by
    rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan]
    have hsq : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [hsq]
    norm_num [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [← Real.arccos_cos hrange.1 hrange.2, hcos]

private theorem nb20_sol0_br : (0.551281:ℝ) ≤ sol0 ∧ sol0 ≤ 0.551291 := by
  have h := nb20_arccos13
  have hpi := nb20_pi
  have halpha := nb20_alpha
  unfold sol0
  constructor <;> nlinarith [h, halpha.1, halpha.2, hpi.1, hpi.2]

private theorem nb20_tau0_br : (1.540547:ℝ) ≤ tau0 ∧ tau0 ≤ 1.540753 := by
  obtain ⟨hlo, hhi⟩ := nb20_sol0_br
  have hpi := nb20_pi
  unfold tau0
  constructor <;> nlinarith [hlo, hhi, hpi.1, hpi.2, Real.pi_pos]

theorem nb20_k1 : (2 * mm1 / Real.pi) ≤ (0.64437:ℝ) := by
  obtain ⟨slo, shi⟩ := nb20_sol0_br
  obtain ⟨tlo, thi⟩ := nb20_tau0_br
  have hpi := nb20_pi
  have hsq2 := nb20_sqrt2
  have tpos : (0:ℝ) < tau0 := lt_of_lt_of_le (by norm_num) tlo
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  unfold mm1
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [div_le_iff₀ hpipos]
  rw [show (2:ℝ) * (sol0 * Real.sqrt 8 / tau0) = 2 * sol0 * Real.sqrt 8 / tau0 from by ring]
  rw [div_le_iff₀ tpos, hs8]
  nlinarith [shi, hsq2.2, hpi.1, tlo]

theorem nb20_k2 : (0.06468:ℝ) ≤ 8 * mm2 / Real.pi := by
  obtain ⟨slo, shi⟩ := nb20_sol0_br
  obtain ⟨tlo, thi⟩ := nb20_tau0_br
  have hpi := nb20_pi
  have hsq2 := nb20_sqrt2
  have tpos : (0:ℝ) < tau0 := lt_of_lt_of_le (by norm_num) tlo
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hs6 : (6:ℝ) * sol0 - Real.pi ≥ 0.16608 := by linarith
  have h6t : (0:ℝ) < 6 * tau0 := by linarith
  unfold mm2
  rw [le_div_iff₀ hpipos]
  rw [show (8:ℝ) * ((6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0)) =
    (8 * ((6 * sol0 - Real.pi) * Real.sqrt 2)) / (6 * tau0) from by ring]
  rw [le_div_iff₀ h6t]
  nlinarith [slo, hsq2.1, hpi.2, thi, hs6]

/-! ## 2. `matan` bounds on the nonnegative branch -/

/-- `matan t ≤ 1` for `t ≥ 0` (the `arctan x ≤ x` bound). -/
theorem nb20_matan_le_one {t : ℝ} (ht : 0 ≤ t) : matan t ≤ 1 := by
  by_cases h0 : t = 0
  · rw [h0]
    unfold matan
    rw [if_pos rfl]
  · have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht'
    unfold matan
    rw [if_neg (ne_of_gt ht'), if_pos ht']
    have hatan : Real.arctan (Real.sqrt t) ≤ Real.sqrt t := by
      have h1 : 0 ≤ Real.arctan (Real.sqrt t) :=
        Real.arctan_nonneg.mpr (Real.sqrt_nonneg t)
      have h2 := Real.le_tan h1 (Real.arctan_mem_Ioo (Real.sqrt t)).2
      rwa [Real.tan_arctan] at h2
    rw [div_le_one hsqrt]
    exact hatan

/-- `arctan x ≥ x − x³/3` for `x ≥ 0`. -/
theorem nb20_arctan_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  have h := Kepler.NliBanks12.nb12_nonneg_of_deriv
    (f := fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
    (hC := Real.continuous_arctan.sub continuous_id |>.add
      ((continuous_pow 3).div_const (3:ℝ)))
    (hD := Real.differentiable_arctan.sub differentiable_id |>.add
      ((differentiable_pow 3).div_const (3:ℝ)))
    (h0 := by norm_num)
    (hd := by
      intro x hx
      have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / ((3:ℕ):ℝ)) (x ^ (2:ℕ)) x := by
        have hp : HasDerivAt (fun y : ℝ => y ^ 3) (((3:ℕ):ℝ) * x ^ (2:ℕ)) x :=
          hasDerivAt_pow 3 x
        have hc : (((3:ℕ):ℝ) * x ^ (2:ℕ)) / ((3:ℕ):ℝ) = x ^ (2:ℕ) := by
          field_simp
        rw [← hc]
        exact hp.div_const ((3:ℕ):ℝ)
      have h1 : HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
          (1 / (1 + x ^ 2) - 1 + x ^ 2) x :=
        ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).add h3
      have hq : 1 / (1 + x ^ 2) - 1 + x ^ 2 = x ^ 4 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [h1.deriv, hq]
      positivity) x hx
  linarith

/-- `1 − t/3 ≤ matan t` for `0 ≤ t`. -/
theorem nb20_matan_ge_taylor {t : ℝ} (ht : 0 ≤ t) : 1 - t / 3 ≤ matan t := by
  by_cases h0 : t = 0
  · rw [h0]
    unfold matan
    rw [if_pos rfl]
    norm_num
  · have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht'
    unfold matan
    rw [if_neg (ne_of_gt ht'), if_pos ht']
    have h := nb20_arctan_ge (Real.sqrt_nonneg t)
    have hcube : Real.sqrt t ^ 3 = t * Real.sqrt t := by
      rw [pow_three, ← pow_two, Real.sq_sqrt ht]
      ring
    rw [hcube] at h
    rw [le_div_iff₀ hsqrt]
    have hring : (1 - t / 3) * Real.sqrt t = Real.sqrt t - t * Real.sqrt t / 3 := by ring
    rw [hring]
    exact h

/-! ## 3. Explicit forms of the six kernel pieces -/

/-- eulerA of `solEulerXDivSqrtdelta a 2 c 2 b 2` at three squares. -/
noncomputable def ea4X (a b c : ℝ) : ℝ :=
  Real.sqrt (2 * a * c) + c * Real.sqrt a / 2 + Real.sqrt 2 * (a + c - b) / 2
    + a * Real.sqrt c / 2

/-- eulerA of `solEulerXDivSqrtdelta b 2 a 2 c 2` at three squares. -/
noncomputable def ea5X (a b c : ℝ) : ℝ :=
  Real.sqrt (2 * a * b) + a * Real.sqrt b / 2 + Real.sqrt 2 * (a + b - c) / 2
    + b * Real.sqrt a / 2

/-- eulerA of `solEulerXDivSqrtdelta c 2 b 2 a 2` at three squares. -/
noncomputable def ea6X (a b c : ℝ) : ℝ :=
  Real.sqrt (2 * b * c) + b * Real.sqrt c / 2 + Real.sqrt 2 * (b + c - a) / 2
    + c * Real.sqrt b / 2

/-- connect `solEulerXDivSqrtdelta a 2 c 2 b 2` to the `ea4X` form. -/
theorem sol_euler4_eq (a b c : ℝ) :
    solEulerXDivSqrtdelta a 2 c 2 b 2 =
      matan (deltaX a 2 c 2 b 2 / (4 * ea4X a b c ^ 2)) / ea4X a b c := by
  have e1 : Real.sqrt (a * 2 * c) = Real.sqrt (2 * a * c) := by congr 1; ring
  have e2 : Real.sqrt a * (2 + c - 2) / 2 = c * Real.sqrt a / 2 := by ring
  have e3 : Real.sqrt c * (a + 2 - 2) / 2 = a * Real.sqrt c / 2 := by ring
  unfold solEulerXDivSqrtdelta
  show matan (deltaX a 2 c 2 b 2 /
      (4 * (Real.sqrt (a * 2 * c) + Real.sqrt a * (2 + c - 2) / 2
        + Real.sqrt 2 * (a + c - b) / 2 + Real.sqrt c * (a + 2 - 2) / 2) ^ 2))
    / (Real.sqrt (a * 2 * c) + Real.sqrt a * (2 + c - 2) / 2
        + Real.sqrt 2 * (a + c - b) / 2 + Real.sqrt c * (a + 2 - 2) / 2)
    = matan (deltaX a 2 c 2 b 2 / (4 * ea4X a b c ^ 2)) / ea4X a b c
  rw [e1, e2, e3]
  rfl

/-- connect `solEulerXDivSqrtdelta b 2 a 2 c 2` to the `ea5X` form. -/
theorem sol_euler5_eq (a b c : ℝ) :
    solEulerXDivSqrtdelta b 2 a 2 c 2 =
      matan (deltaX b 2 a 2 c 2 / (4 * ea5X a b c ^ 2)) / ea5X a b c := by
  unfold solEulerXDivSqrtdelta
  have hS : Real.sqrt (b * 2 * a) + Real.sqrt b * (2 + a - 2) / 2
      + Real.sqrt 2 * (b + a - c) / 2 + Real.sqrt a * (b + 2 - 2) / 2 = ea5X a b c := by
    unfold ea5X
    ring
  rw [hS]

/-- connect `solEulerXDivSqrtdelta c 2 b 2 a 2` to the `ea6X` form. -/
theorem sol_euler6_eq (a b c : ℝ) :
    solEulerXDivSqrtdelta c 2 b 2 a 2 =
      matan (deltaX c 2 b 2 a 2 / (4 * ea6X a b c ^ 2)) / ea6X a b c := by
  unfold solEulerXDivSqrtdelta
  have hS : Real.sqrt (c * 2 * b) + Real.sqrt c * (2 + b - 2) / 2
      + Real.sqrt 2 * (c + b - a) / 2 + Real.sqrt b * (c + 2 - 2) / 2 = ea6X a b c := by
    unfold ea6X
    ring
  rw [hS]

/-- the three sol/dih Delta's equal `deltaX a 2 b 2 c 2` (symmetry at x₂=x₄=x₆=2). -/
theorem dlt4_eq (a b c : ℝ) : deltaX a 2 c 2 b 2 = deltaX a 2 b 2 c 2 := by
  rw [deltaX, deltaX]; ring

theorem dlt5_eq (a b c : ℝ) : deltaX b 2 a 2 c 2 = deltaX a 2 b 2 c 2 := by
  rw [deltaX, deltaX]; ring

theorem dlt6_eq (a b c : ℝ) : deltaX c 2 b 2 a 2 = deltaX a 2 b 2 c 2 := by
  rw [deltaX, deltaX]; ring

/-- `deltaX4 a 2 c 2 b 2 = a * (b + c - a)`. -/
theorem dx4_eq (a b c : ℝ) : deltaX4 a 2 c 2 b 2 = a * (b + c - a) := by
  rw [deltaX4]
  ring

theorem dx5_eq (a b c : ℝ) : deltaX4 b 2 a 2 c 2 = b * (a + c - b) := by
  rw [deltaX4]
  ring

theorem dx6_eq (a b c : ℝ) : deltaX4 c 2 b 2 a 2 = c * (a + b - c) := by
  rw [deltaX4]
  ring

/-- connect `dihXDivSqrtdeltaPosbranch a 2 c 2 b 2` to explicit form. -/
theorem dih4_eq (a b c : ℝ) (ha : 0 ≤ a) :
    dihXDivSqrtdeltaPosbranch a 2 c 2 b 2 =
      2 * Real.sqrt a / (a * (b + c - a)) *
        matan (4 * a * deltaX a 2 c 2 b 2 / (a * (b + c - a)) ^ 2) := by
  unfold dihXDivSqrtdeltaPosbranch
  rw [dx4_eq]
  have h4a : Real.sqrt (4 * a) = 2 * Real.sqrt a := by
    rw [show (4 * a : ℝ) = 2 ^ 2 * a by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h4a]

theorem dih5_eq (a b c : ℝ) (hb : 0 ≤ b) :
    dihXDivSqrtdeltaPosbranch b 2 a 2 c 2 =
      2 * Real.sqrt b / (b * (a + c - b)) *
        matan (4 * b * deltaX b 2 a 2 c 2 / (b * (a + c - b)) ^ 2) := by
  unfold dihXDivSqrtdeltaPosbranch
  rw [dx5_eq]
  have h4b : Real.sqrt (4 * b) = 2 * Real.sqrt b := by
    rw [show (4 * b : ℝ) = 2 ^ 2 * b by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h4b]

theorem dih6_eq (a b c : ℝ) (hc : 0 ≤ c) :
    dihXDivSqrtdeltaPosbranch c 2 b 2 a 2 =
      2 * Real.sqrt c / (c * (a + b - c)) *
        matan (4 * c * deltaX c 2 b 2 a 2 / (c * (a + b - c)) ^ 2) := by
  unfold dihXDivSqrtdeltaPosbranch
  rw [dx6_eq]
  have h4c : Real.sqrt (4 * c) = 2 * Real.sqrt c := by
    rw [show (4 * c : ℝ) = 2 ^ 2 * c by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h4c]

/-! ## 4. Corner monotonicity -/

/-- `Dlt a b c := deltaX a 2 b 2 c 2` is antitone in `a` on the wt2A box. -/
theorem dlt_anti_a {a a' b c : ℝ} (ha : (6.06883225:ℝ) ≤ a) (ha' : a' ≤ 8)
    (hb : (6.06883225:ℝ) ≤ b) (hc : (4:ℝ) ≤ c) (hcc : c ≤ (6.06992999:ℝ))
    (h : a ≤ a') :
    (2 * (4 * b * c - (a' - b - c) ^ 2) - a' * b * c) ≤
      (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c) := by
  have hkey : (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c)
      - (2 * (4 * b * c - (a' - b - c) ^ 2) - a' * b * c)
      = (a - a') * (-(2 * (a + a' - 2 * (b + c))) - b * c) := by ring
  have hc4 : (0:ℝ) ≤ c - 4 := by linarith
  have hbc : (6.06883225:ℝ) * (c - 4) ≤ b * (c - 4) :=
    mul_le_mul_of_nonneg_right hb hc4
  have hB : -(2 * (a + a' - 2 * (b + c))) - b * c ≤ 0 := by
    nlinarith [h, ha, ha', hb, hc, hbc, mul_nonneg (by linarith : (0:ℝ) ≤ b) (by linarith : (0:ℝ) ≤ c)]
  have haa : a - a' ≤ 0 := by linarith
  have hprod : 0 ≤ (a - a') * (-(2 * (a + a' - 2 * (b + c))) - b * c) :=
    mul_nonneg_of_nonpos_of_nonpos haa hB
  linarith

/-- `Dlt` antitone in `b` (true family: cross product `4·b·c`). -/
theorem dlt_anti_b {b b' a c : ℝ} (hb : (6.06883225:ℝ) ≤ b) (ha : (6.06883225:ℝ) ≤ a)
    (hc : (4:ℝ) ≤ c) (h : b ≤ b') :
    (2 * (4 * b' * c - (a - b' - c) ^ 2) - a * b' * c) ≤
      (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c) := by
  have hkey : (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c)
      - (2 * (4 * b' * c - (a - b' - c) ^ 2) - a * b' * c)
      = (b - b') * (4 * a + 4 * c - 2 * (b + b') - a * c) := by ring
  have hb'lo : (6.06883225:ℝ) ≤ b' := hb.trans h
  have hc4 : (0:ℝ) ≤ c - 4 := by linarith
  have hac : (6.06883225:ℝ) * (c - 4) ≤ a * (c - 4) :=
    mul_le_mul_of_nonneg_right ha hc4
  have hB : 4 * a + 4 * c - 2 * (b + b') - a * c ≤ 0 := by
    linarith [hac, hb, hb'lo, hc]
  have hbb : b - b' ≤ 0 := by linarith
  have hprod : 0 ≤ (b - b') * (4 * a + 4 * c - 2 * (b + b') - a * c) :=
    mul_nonneg_of_nonpos_of_nonpos hbb hB
  linarith

/-- `Dlt` antitone in `c` (true family: cross product `4·b·c`). -/
theorem dlt_anti_c {c c' a b : ℝ} (ha : (6.06883225:ℝ) ≤ a) (hb : (6.06883225:ℝ) ≤ b)
    (hc : (4:ℝ) ≤ c) (h : c ≤ c') :
    (2 * (4 * b * c' - (a - b - c') ^ 2) - a * b * c') ≤
      (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c) := by
  have hkey : (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c)
      - (2 * (4 * b * c' - (a - b - c') ^ 2) - a * b * c')
      = (c - c') * (4 * a + 4 * b - 2 * (c + c') - a * b) := by ring
  have hc'lo : (4:ℝ) ≤ c' := hc.trans h
  have hb4 : (0:ℝ) ≤ b - 4 := by linarith
  have hab : (6.06883225:ℝ) * (b - 4) ≤ a * (b - 4) :=
    mul_le_mul_of_nonneg_right ha hb4
  have hB : 4 * a + 4 * b - 2 * (c + c') - a * b ≤ 0 := by
    linarith [hab, hb, hc, hc'lo]
  have hcc : c - c' ≤ 0 := by linarith
  have hprod : 0 ≤ (c - c') * (4 * a + 4 * b - 2 * (c + c') - a * b) :=
    mul_nonneg_of_nonpos_of_nonpos hcc hB
  linarith

/-- `ea4X` monotone in `a` (needs `0 ≤ c`). -/
theorem ea4X_mono_a {a a' b c : ℝ} (hc : 0 ≤ c) (h : a ≤ a') :
    ea4X a b c ≤ ea4X a' b c := by
  unfold ea4X
  have h1 : Real.sqrt (2 * a * c) ≤ Real.sqrt (2 * a' * c) :=
    Real.sqrt_le_sqrt (by nlinarith [h, hc])
  have h2 : c * Real.sqrt a ≤ c * Real.sqrt a' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) hc
  have h3 : Real.sqrt 2 * (a + c - b) / 2 ≤ Real.sqrt 2 * (a' + c - b) / 2 := by
    have hin : a + c - b ≤ a' + c - b := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  have h4 : a * Real.sqrt c ≤ a' * Real.sqrt c :=
    mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg c)
  linarith

/-- `ea4X` antitone in `b`. -/
theorem ea4X_anti_b {b b' a c : ℝ} (h : b ≤ b') :
    ea4X a b' c ≤ ea4X a b c := by
  unfold ea4X
  have h3 : Real.sqrt 2 * (a + c - b') / 2 ≤ Real.sqrt 2 * (a + c - b) / 2 := by
    have hin : a + c - b' ≤ a + c - b := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  linarith

/-- `ea4X` monotone in `c` (needs `0 ≤ a`). -/
theorem ea4X_mono_c {c c' a b : ℝ} (ha : 0 ≤ a) (h : c ≤ c') :
    ea4X a b c ≤ ea4X a b c' := by
  unfold ea4X
  have h1 : Real.sqrt (2 * a * c) ≤ Real.sqrt (2 * a * c') :=
    Real.sqrt_le_sqrt (by nlinarith [h, ha])
  have h2 : c * Real.sqrt a ≤ c' * Real.sqrt a :=
    mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg a)
  have h3 : Real.sqrt 2 * (a + c - b) / 2 ≤ Real.sqrt 2 * (a + c' - b) / 2 := by
    have hin : a + c - b ≤ a + c' - b := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  have h4 : a * Real.sqrt c ≤ a * Real.sqrt c' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) ha
  linarith

/-- `ea5X` monotone in `a` (needs `0 ≤ b`). -/
theorem ea5X_mono_a {a a' b c : ℝ} (hb : 0 ≤ b) (h : a ≤ a') :
    ea5X a b c ≤ ea5X a' b c := by
  unfold ea5X
  have h1 : Real.sqrt (2 * a * b) ≤ Real.sqrt (2 * a' * b) :=
    Real.sqrt_le_sqrt (by nlinarith [h, hb])
  have h2 : a * Real.sqrt b ≤ a' * Real.sqrt b :=
    mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg b)
  have h3 : Real.sqrt 2 * (a + b - c) / 2 ≤ Real.sqrt 2 * (a' + b - c) / 2 := by
    have hin : a + b - c ≤ a' + b - c := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  have h4 : b * Real.sqrt a ≤ b * Real.sqrt a' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) hb
  linarith

/-- `ea5X` monotone in `b` (needs `0 ≤ a`). -/
theorem ea5X_mono_b {b b' a c : ℝ} (ha : 0 ≤ a) (h : b ≤ b') :
    ea5X a b c ≤ ea5X a b' c := by
  unfold ea5X
  have h1 : Real.sqrt (2 * a * b) ≤ Real.sqrt (2 * a * b') :=
    Real.sqrt_le_sqrt (by nlinarith [h, ha])
  have h2 : a * Real.sqrt b ≤ a * Real.sqrt b' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) ha
  have h3 : Real.sqrt 2 * (a + b - c) / 2 ≤ Real.sqrt 2 * (a + b' - c) / 2 := by
    have hin : a + b - c ≤ a + b' - c := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  have h4 : b * Real.sqrt a ≤ b' * Real.sqrt a :=
    mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg a)
  linarith

/-- `ea5X` antitone in `c`. -/
theorem ea5X_anti_c {c c' a b : ℝ} (h : c ≤ c') :
    ea5X a b c' ≤ ea5X a b c := by
  unfold ea5X
  have h3 : Real.sqrt 2 * (a + b - c') / 2 ≤ Real.sqrt 2 * (a + b - c) / 2 := by
    have hin : a + b - c' ≤ a + b - c := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  linarith

/-- `ea6X` antitone in `a`. -/
theorem ea6X_anti_a {a a' b c : ℝ} (h : a ≤ a') :
    ea6X a' b c ≤ ea6X a b c := by
  unfold ea6X
  have h3 : Real.sqrt 2 * (b + c - a') / 2 ≤ Real.sqrt 2 * (b + c - a) / 2 := by
    have hin : b + c - a' ≤ b + c - a := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  linarith

/-- `ea6X` monotone in `b` (needs `0 ≤ c`). -/
theorem ea6X_mono_b {b b' a c : ℝ} (hc : 0 ≤ c) (h : b ≤ b') :
    ea6X a b c ≤ ea6X a b' c := by
  unfold ea6X
  have h1 : Real.sqrt (2 * b * c) ≤ Real.sqrt (2 * b' * c) :=
    Real.sqrt_le_sqrt (by nlinarith [h, hc])
  have h2 : b * Real.sqrt c ≤ b' * Real.sqrt c :=
    mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg c)
  have h3 : Real.sqrt 2 * (b + c - a) / 2 ≤ Real.sqrt 2 * (b' + c - a) / 2 := by
    have hin : b + c - a ≤ b' + c - a := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  have h4 : c * Real.sqrt b ≤ c * Real.sqrt b' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) hc
  linarith

/-- `ea6X` monotone in `c` (needs `0 ≤ b`). -/
theorem ea6X_mono_c {c c' a b : ℝ} (hb : 0 ≤ b) (h : c ≤ c') :
    ea6X a b c ≤ ea6X a b c' := by
  unfold ea6X
  have h1 : Real.sqrt (2 * b * c) ≤ Real.sqrt (2 * b * c') :=
    Real.sqrt_le_sqrt (by nlinarith [h, hb])
  have h2 : b * Real.sqrt c ≤ b * Real.sqrt c' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) hb
  have h3 : Real.sqrt 2 * (b + c - a) / 2 ≤ Real.sqrt 2 * (b + c' - a) / 2 := by
    have hin : b + c - a ≤ b + c' - a := by linarith
    have h3' := mul_le_mul_of_nonneg_left hin (Real.sqrt_nonneg 2)
    linarith
  have h4 : c * Real.sqrt b ≤ c' * Real.sqrt b :=
    mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg b)
  linarith

/-! ## 5. `dX4` product corners -/

theorem dx4_ge {a b c al bl cl ah : ℝ} (ha : al ≤ a) (hb : bl ≤ b) (hc : cl ≤ c)
    (ha' : a ≤ ah) (hinner : (0:ℝ) ≤ bl + cl - ah) (hal : (0:ℝ) ≤ al) :
    al * (bl + cl - ah) ≤ a * (b + c - a) := by
  have h1 : bl + cl - ah ≤ b + c - a := by linarith
  have h2 : (0:ℝ) ≤ b + c - a := hinner.trans h1
  have h3 : al * (bl + cl - ah) ≤ al * (b + c - a) :=
    mul_le_mul_of_nonneg_left h1 hal
  have h4 : al * (b + c - a) ≤ a * (b + c - a) :=
    mul_le_mul_of_nonneg_right ha h2
  exact h3.trans h4

theorem dx4_le {a b c ah bh ch al : ℝ} (ha : a ≤ ah) (hb : b ≤ bh) (hc : c ≤ ch)
    (hal : al ≤ a) (hpos : (0:ℝ) ≤ b + c - a) (hah : (0:ℝ) ≤ ah) :
    a * (b + c - a) ≤ ah * (bh + ch - al) := by
  have h1 : b + c - a ≤ bh + ch - al := by linarith
  have h2 : a * (b + c - a) ≤ ah * (b + c - a) :=
    mul_le_mul_of_nonneg_right ha hpos
  have h3 : ah * (b + c - a) ≤ ah * (bh + ch - al) :=
    mul_le_mul_of_nonneg_left h1 hah
  exact h2.trans h3

theorem dx5_ge {b a c bl al cl bh : ℝ} (hb : bl ≤ b) (ha : al ≤ a) (hc : cl ≤ c)
    (hb' : b ≤ bh) (hinner : (0:ℝ) ≤ al + cl - bh) (hbl : (0:ℝ) ≤ bl) :
    bl * (al + cl - bh) ≤ b * (a + c - b) := by
  have h1 : al + cl - bh ≤ a + c - b := by linarith
  have h2 : (0:ℝ) ≤ a + c - b := hinner.trans h1
  have h3 : bl * (al + cl - bh) ≤ bl * (a + c - b) :=
    mul_le_mul_of_nonneg_left h1 hbl
  have h4 : bl * (a + c - b) ≤ b * (a + c - b) :=
    mul_le_mul_of_nonneg_right hb h2
  exact h3.trans h4

theorem dx5_le {b a c bh ah ch bl : ℝ} (hb : b ≤ bh) (ha : a ≤ ah) (hc : c ≤ ch)
    (hbl : bl ≤ b) (hpos : (0:ℝ) ≤ a + c - b) (hbh : (0:ℝ) ≤ bh) :
    b * (a + c - b) ≤ bh * (ah + ch - bl) := by
  have h1 : a + c - b ≤ ah + ch - bl := by linarith
  have h2 : b * (a + c - b) ≤ bh * (a + c - b) :=
    mul_le_mul_of_nonneg_right hb hpos
  have h3 : bh * (a + c - b) ≤ bh * (ah + ch - bl) :=
    mul_le_mul_of_nonneg_left h1 hbh
  exact h2.trans h3

theorem dx6_ge {c a b cl al bl ch : ℝ} (hc : cl ≤ c) (ha : al ≤ a) (hb : bl ≤ b)
    (hc' : c ≤ ch) (hinner : (0:ℝ) ≤ al + bl - ch) (hcl : (0:ℝ) ≤ cl) :
    cl * (al + bl - ch) ≤ c * (a + b - c) := by
  have h1 : al + bl - ch ≤ a + b - c := by linarith
  have h2 : (0:ℝ) ≤ a + b - c := hinner.trans h1
  have h3 : cl * (al + bl - ch) ≤ cl * (a + b - c) :=
    mul_le_mul_of_nonneg_left h1 hcl
  have h4 : cl * (a + b - c) ≤ c * (a + b - c) :=
    mul_le_mul_of_nonneg_right hc h2
  exact h3.trans h4

theorem dx6_le {c a b ch ah bh cl : ℝ} (hc : c ≤ ch) (ha : a ≤ ah) (hb : b ≤ bh)
    (hcl : cl ≤ c) (hpos : (0:ℝ) ≤ a + b - c) (hch : (0:ℝ) ≤ ch) :
    c * (a + b - c) ≤ ch * (ah + bh - cl) := by
  have h1 : a + b - c ≤ ah + bh - cl := by linarith
  have h2 : c * (a + b - c) ≤ ch * (a + b - c) :=
    mul_le_mul_of_nonneg_right hc hpos
  have h3 : ch * (a + b - c) ≤ ch * (ah + bh - cl) :=
    mul_le_mul_of_nonneg_left h1 hch
  exact h2.trans h3

/-! ## 6. `h0cut`/`lfun` pins -/

/-- `lfun (q·½) ≤ lfun (y·½)` for `y ≤ q` (`lfun` is plain linear, no ite). -/
theorem lfun_half_ge {y q : ℝ} (h : y ≤ q) (hq : q * 0.5 ≤ h0) :
    lfun (q * 0.5) ≤ lfun (y * 0.5) := by
  have h1 : y * 0.5 ≤ q * 0.5 := by linarith
  have h2 : y * 0.5 ≤ h0 := h1.trans hq
  have h01 : (0:ℝ) < h0 - 1 := by
    have h0v : h0 = (1.26:ℝ) := rfl
    linarith
  unfold lfun
  rw [div_le_div_iff₀ h01 h01]
  exact mul_le_mul_of_nonneg_right (show h0 - q * 0.5 ≤ h0 - y * 0.5 by linarith) h01.le

/-- `h0cut y * lfun (y·½) ≥ lfun (p·½)` when `y ≤ p ≤ 2h0`. -/
theorem h0cut_lfun_ge {y p : ℝ} (h : y ≤ p) (hp : p ≤ 2 * h0) :
    lfun (p * 0.5) ≤ h0cut y * lfun (y * 0.5) := by
  have hy : y ≤ 2 * h0 := h.trans hp
  rw [nb19_h0cut_eq_one hy, one_mul]
  have hq : p * 0.5 ≤ h0 := by
    have h2 : 2 * h0 = (2.52:ℝ) := nb19_two_h0
    linarith
  exact lfun_half_ge h hq

/-- `lfun` at the box lower edge. -/
theorem lfun_123175 : lfun ((2.4635:ℝ) * 0.5) ≤ (0.108654:ℝ) := by
  have h0v : h0 = (1.26:ℝ) := rfl
  have hhalf : (2.4635:ℝ) * 0.5 = (1.23175:ℝ) := by norm_num
  have hnum : (1.26:ℝ) - (1.23175:ℝ) = (0.02825:ℝ) := by norm_num
  have hden : (0:ℝ) < (1.26:ℝ) - 1 := by norm_num
  have hmul : (0.108654:ℝ) * ((1.26:ℝ) - 1) = (0.02825004:ℝ) := by norm_num
  unfold lfun
  rw [h0v, hhalf, hnum, div_le_iff₀ hden, hmul]
  norm_num

/-- `h0cut y * lfun (y·½) ≤ 0.108654` on the box (`y ≥ 2.4635`). -/
theorem h0cut_lfun_le {y : ℝ} (hy : (2.4635:ℝ) ≤ y) :
    h0cut y * lfun (y * 0.5) ≤ (0.108654:ℝ) := by
  by_cases h2h : y ≤ 2 * h0
  · rw [nb19_h0cut_eq_one h2h, one_mul]
    have h1 : lfun (y * 0.5) ≤ lfun ((2.4635:ℝ) * 0.5) := by
      apply lfun_half_ge
      · linarith
      · have h2 : 2 * h0 = (2.52:ℝ) := nb19_two_h0
        linarith
    exact h1.trans lfun_123175
  · rw [nb19_h0cut_eq_zero (lt_of_not_ge h2h)]
    norm_num

/-- `K2` upper bracket. -/
theorem nb20_k2_upper : 8 * mm2 / Real.pi ≤ (0.06476:ℝ) := by
  obtain ⟨slo, shi⟩ := nb20_sol0_br
  obtain ⟨tlo, thi⟩ := nb20_tau0_br
  have hpi := nb20_pi
  have hsq2 := nb20_sqrt2
  have tpos : (0:ℝ) < tau0 := lt_of_lt_of_le (by norm_num) tlo
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have h6t : (0:ℝ) < 6 * tau0 := by linarith
  unfold mm2
  rw [div_le_iff₀ hpipos]
  rw [show (8:ℝ) * ((6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0)) =
    (8 * ((6 * sol0 - Real.pi) * Real.sqrt 2)) / (6 * tau0) from by ring]
  rw [div_le_iff₀ h6t]
  nlinarith [shi, hsq2.2, hpi.1, tlo]

/-! ## 7. Box square facts and the corner kit -/

/-- the square facts derivable from the wt2A box hypotheses. -/
theorem box_sq {y4 y5 y6 : ℝ} (h4l : (2.4635:ℝ) ≤ y4) (h4h : y4 ≤ Real.sqrt 8)
    (h5l : (2.4635:ℝ) ≤ y5) (h5h : y5 ≤ Real.sqrt 8) (h6l : (2:ℝ) ≤ y6)
    (h6h : y6 ≤ 2.46352) :
    (6.06883225:ℝ) ≤ y4 * y4 ∧ y4 * y4 ≤ 8 ∧ (6.06883225:ℝ) ≤ y5 * y5 ∧
      y5 * y5 ≤ 8 ∧ (4:ℝ) ≤ y6 * y6 ∧ y6 * y6 ≤ 6.06992999 ∧
      (0:ℝ) ≤ y4 ∧ (0:ℝ) ≤ y5 ∧ (0:ℝ) ≤ y6 := by
  have hsw : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have h4p : (0:ℝ) ≤ y4 := by linarith
  have h5p : (0:ℝ) ≤ y5 := by linarith
  have h6p : (0:ℝ) ≤ y6 := by linarith
  have h4u : y4 * y4 ≤ 8 := by
    have h := mul_self_le_mul_self h4p h4h
    rw [hsw] at h
    exact h
  have h5u : y5 * y5 ≤ 8 := by
    have h := mul_self_le_mul_self h5p h5h
    rw [hsw] at h
    exact h
  have h4l2 : (6.06883225:ℝ) ≤ y4 * y4 := by
    have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) h4l
    linarith [h]
  have h5l2 : (6.06883225:ℝ) ≤ y5 * y5 := by
    have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) h5l
    linarith [h]
  have h6l2 : (4:ℝ) ≤ y6 * y6 := by nlinarith [h6l]
  have h6u : y6 * y6 ≤ 6.06992999 := by
    have h := mul_self_le_mul_self h6p h6h
    linarith [h]
  exact ⟨h4l2, h4u, h5l2, h5u, h6l2, h6u, h4p, h5p, h6p⟩

/-- `dX4` inner term positivity, uniform on the box. -/
theorem dx4_inner_pos {bl cl ah : ℝ} (hbl : (6.06883225:ℝ) ≤ bl) (hcl : (4:ℝ) ≤ cl)
    (hah : ah ≤ 8) : (0:ℝ) ≤ bl + cl - ah := by linarith

theorem dx5_inner_pos {al cl bh : ℝ} (hal : (6.06883225:ℝ) ≤ al) (hcl : (4:ℝ) ≤ cl)
    (hbh : bh ≤ 8) : (0:ℝ) ≤ al + cl - bh := by linarith

theorem dx6_inner_pos {al bl ch : ℝ} (hal : (6.06883225:ℝ) ≤ al) (hbl : (6.06883225:ℝ) ≤ bl)
    (hch : ch ≤ 6.06992999) : (0:ℝ) ≤ al + bl - ch := by linarith

/-- Delta upper corner: max of `deltaX` on a cell is at the `(P4L,P5L,Q6L)` corner. -/
theorem dlt_corner {y4 y5 y6 P4L P5L Q6L : ℝ}
    (h4l : (2.4635:ℝ) ≤ y4) (h4h : y4 ≤ Real.sqrt 8)
    (h5l : (2.4635:ℝ) ≤ y5) (h5h : y5 ≤ Real.sqrt 8)
    (h6l : (2:ℝ) ≤ y6) (h6h : y6 ≤ 2.46352)
    (h4c : P4L ≤ y4) (h5c : P5L ≤ y5) (h6c : Q6L ≤ y6)
    (h4ge : (2.4635:ℝ) ≤ P4L) (h5ge : (2.4635:ℝ) ≤ P5L)
    (h6ge : (2:ℝ) ≤ Q6L) (h6le : Q6L ≤ 2.46352) :
    deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤
      2 * (4 * (P5L^2) * (Q6L^2) - (P4L^2 - P5L^2 - Q6L^2)^2)
        - (P4L^2) * (P5L^2) * (Q6L^2) := by
  obtain ⟨h4l2, h4u, h5l2, h5u, h6l2, h6u, h4p, h5p, h6p⟩ :=
    box_sq h4l h4h h5l h5h h6l h6h
  have hP4Lp : (0:ℝ) ≤ P4L := by nlinarith [h4ge]
  have hP5Lp : (0:ℝ) ≤ P5L := by nlinarith [h5ge]
  have hQ6Lp : (0:ℝ) ≤ Q6L := by nlinarith [h6ge]
  have hP4L2 : (6.06883225:ℝ) ≤ P4L^2 := by
    have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) h4ge
    rw [pow_two]
    linarith [h]
  have hP5L2 : (6.06883225:ℝ) ≤ P5L^2 := by
    have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) h5ge
    rw [pow_two]
    linarith [h]
  have hP4Lle : P4L^2 ≤ y4 * y4 := by
    rw [pow_two]
    exact mul_self_le_mul_self hP4Lp h4c
  have hP5Lle : P5L^2 ≤ y5 * y5 := by
    rw [pow_two]
    exact mul_self_le_mul_self hP5Lp h5c
  have hQ6Lle : Q6L^2 ≤ y6 * y6 := by
    rw [pow_two]
    exact mul_self_le_mul_self hQ6Lp h6c
  have e : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      = 2 * (4 * (y5*y5) * (y6*y6) - (y4*y4 - y5*y5 - y6*y6)^2)
        - (y4*y4) * (y5*y5) * (y6*y6) := by
    rw [nb19_dlt_eq, nb19_ups_eq]
  rw [e]
  have s1 := dlt_anti_a (a := P4L^2) (a' := y4*y4) (b := y5*y5) (c := y6*y6)
    hP4L2 h4u h5l2 h6l2 h6u hP4Lle
  have s2 := dlt_anti_b (b := P5L^2) (b' := y5*y5) (a := P4L^2) (c := y6*y6)
    hP5L2 hP4L2 h6l2 hP5Lle
  have hQ6L2 : (4:ℝ) ≤ Q6L^2 := by
    have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2) h6ge
    rw [pow_two]
    linarith [h]
  have s3 := dlt_anti_c (c := Q6L^2) (c' := y6*y6) (a := P4L^2) (b := P5L^2)
    hP4L2 hP5L2 hQ6L2 hQ6Lle
  exact s1.trans (s2.trans s3)

/-! ## 8. Extra machinery for the cell certificate -/

/-- `√8` bracket (same pattern as `nb20_sqrt2`). -/
private theorem nb20_sqrt8 : (2.82842712 : ℝ) ≤ Real.sqrt 8 ∧ Real.sqrt 8 ≤ 2.82842713 := by
  refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
  · norm_num
  · rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2.82842713)]
    norm_num

/-- `K1 = 2·mm1/π > 0`. -/
theorem nb20_k1_pos : (0:ℝ) < 2 * mm1 / Real.pi := by
  have h1 : (0:ℝ) < sol0 := by have := nb20_sol0_br.1; linarith
  have h2 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (0:ℝ) < tau0 := by have := nb20_tau0_br.1; linarith
  have hs : (0:ℝ) < sol0 * Real.sqrt 8 := mul_pos h1 h2
  have hd : (0:ℝ) < sol0 * Real.sqrt 8 / tau0 := div_pos hs h3
  unfold mm1
  exact div_pos (by linarith) Real.pi_pos

/-- `matan t ≥ 0` for `t ≥ 0`. -/
theorem nb20_matan_nonneg {t : ℝ} (ht : 0 ≤ t) : (0:ℝ) ≤ matan t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    unfold matan
    rw [if_pos rfl]
    norm_num
  · unfold matan
    rw [if_neg (ne_of_gt h), if_pos h]
    have hs : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have h1 : (0:ℝ) ≤ Real.arctan (Real.sqrt t) := Real.arctan_nonneg.mpr hs
    exact div_nonneg h1 hs

/-- Delta slot symmetry: swapping the first and third squares. -/
theorem dlt_swap (a b c : ℝ) : deltaX b 2 a 2 c 2 = deltaX a 2 b 2 c 2 := by
  rw [deltaX, deltaX]
  ring

/-- Box-level positivity of the three `dihX` denominators at a box point. -/
theorem inner_pos_box {y4 y5 y6 : ℝ}
    (h4l : (2.4635:ℝ) ≤ y4) (h4h : y4 ≤ Real.sqrt 8)
    (h5l : (2.4635:ℝ) ≤ y5) (h5h : y5 ≤ Real.sqrt 8)
    (h6l : (2:ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    (0:ℝ) < y4*y4*(y5*y5 + y6*y6 - y4*y4) ∧
    (0:ℝ) < y5*y5*(y4*y4 + y6*y6 - y5*y5) ∧
    (0:ℝ) < y6*y6*(y4*y4 + y5*y5 - y6*y6) := by
  obtain ⟨h4l2, h4u, h5l2, h5u, h6l2, h6u, h4p, h5p, h6p⟩ :=
    box_sq h4l h4h h5l h5h h6l h6h
  have hs4 : (0:ℝ) < y5*y5 + y6*y6 - y4*y4 := by linarith
  have hs5 : (0:ℝ) < y4*y4 + y6*y6 - y5*y5 := by linarith
  have hs6 : (0:ℝ) < y4*y4 + y5*y5 - y6*y6 := by linarith
  have hy4 : (0:ℝ) < y4 := by linarith
  have hy5 : (0:ℝ) < y5 := by linarith
  have hy6 : (0:ℝ) < y6 := by linarith
  exact ⟨mul_pos (mul_pos hy4 hy4) hs4, mul_pos (mul_pos hy5 hy5) hs5,
    mul_pos (mul_pos hy6 hy6) hs6⟩

/-- Product bound via one-sided chains (avoids `mul_le_mul` argument-order
pitfalls). -/
private theorem nb20_mul4 {a b c d : ℝ} (h1 : a ≤ c) (h2 : b ≤ d)
    (ha : (0:ℝ) ≤ a) (hb : (0:ℝ) ≤ b) (hc : (0:ℝ) ≤ c) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_right h1 hb).trans (mul_le_mul_of_nonneg_left h2 hc)

/-! ## 9. The generic per-cell certificate -/

/-- **Generic cell lemma**.  At a box point with `0 ≤ deltaX` (the hcore
hypothesis), corner-derived piece bounds and a positive rational margin give
`0 < w2aF`.  The margin is the design formula
`layered3.cell_lb`: every `w2aG` term is bounded in the lossy-but-valid
direction — `solEuler` slots via `matan ≤ 1` on the nonnegative branch,
`dih` slots via the Taylor lower bound `1 − v/3` (needs `v ≤ 3`), the `d4`
slot one-sided at the `DU` corner since its combined coefficient
`(K2L/2)·m4 − 0.008` is nonpositive. -/
theorem w2a_cell {y4 y5 y6 p4h p5l p5h q6l q6h Dh ea4L ea5L ea6L
    dx4L dx5L dx5H dx6L dx6H m4 m5 l6v : ℝ}
    (hb4 : (2.4635:ℝ) ≤ y4) (hb4' : y4 ≤ Real.sqrt 8)
    (hb5 : (2.4635:ℝ) ≤ y5) (hb5' : y5 ≤ Real.sqrt 8)
    (hq6l : (2:ℝ) ≤ q6l) (hq6h : q6h ≤ (2.46352:ℝ))
    (hc4' : y4 ≤ p4h) (hc5 : p5l ≤ y5) (hc5' : y5 ≤ p5h)
    (hc6 : q6l ≤ y6) (hc6' : y6 ≤ q6h) (hp5l : (0:ℝ) ≤ p5l)
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2)
    (hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ Dh) (hdhp : (0:ℝ) ≤ Dh)
    (hea4 : ea4L ≤ ea4X (y5*y5) (y6*y6) (y4*y4)) (hea4p : (0:ℝ) < ea4L)
    (hea5 : ea5L ≤ ea5X (y5*y5) (y6*y6) (y4*y4)) (hea5p : (0:ℝ) < ea5L)
    (hea6 : ea6L ≤ ea6X (y5*y5) (y6*y6) (y4*y4)) (hea6p : (0:ℝ) < ea6L)
    (hdx4 : dx4L ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4)) (hdx4p : (0:ℝ) < dx4L)
    (hdx5 : dx5L ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5)) (hdx5p : (0:ℝ) < dx5L)
    (hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5) ≤ dx5H) (hdx5p' : (0:ℝ) < dx5H)
    (hdx6 : dx6L ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6)) (hdx6p : (0:ℝ) < dx6L)
    (hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6) ≤ dx6H) (hdx6p' : (0:ℝ) < dx6H)
    (hm4 : m4 ≤ lfun (y4 * 0.5) * h0cut y4) (hm4p : (0:ℝ) ≤ m4)
    (hm5 : m5 ≤ lfun (y5 * 0.5) * h0cut y5) (hm5p : (0:ℝ) ≤ m5)
    (hl6 : l6v ≤ lfun (y6 * 0.5)) (hl6p : (0:ℝ) ≤ l6v)
    (hv5 : (4:ℝ) * (p5h * p5h) * Dh ≤ (3:ℝ) * dx5L * dx5L)
    (hv6 : (4:ℝ) * (q6h * q6h) * Dh ≤ (3:ℝ) * dx6L * dx6L)
    (hcoef : (0.06468:ℝ) / 2 * m4 ≤ (0.008:ℝ))
    (hmargin : (0:ℝ) < (1:ℝ)/24
        - (0.64437:ℝ)/2 * ((1:ℝ)/ea4L + (1:ℝ)/ea5L + (1:ℝ)/ea6L)
        + (0.06468:ℝ)/2 * (m4 * ((2:ℝ) * p4h / dx4L)
            + m5 * ((2:ℝ) * p5l / dx5H
              * ((1:ℝ) - (4:ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3:ℝ)))
            + l6v * ((2:ℝ) * q6l / dx6H
              * ((1:ℝ) - (4:ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3:ℝ))))
        - (0.008:ℝ) * ((2:ℝ) * p4h / dx4L)) :
    0 < w2aF y4 y5 y6 := by
  -- 0. point facts
  have hy4 : (0:ℝ) < y4 := by linarith
  have hy5 : (0:ℝ) < y5 := by linarith
  have hy6 : (0:ℝ) < y6 := by linarith
  have hy4sq : (0:ℝ) ≤ y4 * y4 := mul_nonneg hy4.le hy4.le
  have hy5sq : (0:ℝ) ≤ y5 * y5 := mul_nonneg hy5.le hy5.le
  have hy6sq : (0:ℝ) ≤ y6 * y6 := mul_nonneg hy6.le hy6.le
  have hy6h : y6 ≤ (2.46352:ℝ) := hc6'.trans hq6h
  have hy5p5 : y5 ≤ p5h := hc5'
  have hy5p5sq : y5 * y5 ≤ p5h * p5h :=
    mul_self_le_mul_self hy5.le hy5p5
  have hy6q6 : y6 * y6 ≤ q6h * q6h :=
    mul_self_le_mul_self hy6.le hc6'
  obtain ⟨hdx4nn, hdx5nn, hdx6nn⟩ :=
    inner_pos_box hb4 hb4' hb5 hb5' (by linarith) hy6h
  -- 1. the three `solEuler` slots: `s_i = matan u_i / ea_i ≤ 1 / ea_iL`
  have hE4 : (0:ℝ) < ea4X (y5*y5) (y6*y6) (y4*y4) := lt_of_lt_of_le hea4p hea4
  have hE5 : (0:ℝ) < ea5X (y5*y5) (y6*y6) (y4*y4) := lt_of_lt_of_le hea5p hea5
  have hE6 : (0:ℝ) < ea6X (y5*y5) (y6*y6) (y4*y4) := lt_of_lt_of_le hea6p hea6
  have hu4 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      / (4 * ea4X (y5*y5) (y6*y6) (y4*y4) ^ 2) :=
    div_nonneg hd0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hu5 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      / (4 * ea5X (y5*y5) (y6*y6) (y4*y4) ^ 2) :=
    div_nonneg hd0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hu6 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      / (4 * ea6X (y5*y5) (y6*y6) (y4*y4) ^ 2) :=
    div_nonneg hd0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hs4 : solEulerXDivSqrtdelta (y5*y5) 2 (y4*y4) 2 (y6*y6) 2
      ≤ (1:ℝ) / ea4L := by
    rw [sol_euler4_eq, dlt_swap, div_le_div_iff₀ hE4 hea4p]
    have hm := nb20_matan_le_one hu4
    exact (mul_le_mul_of_nonneg_right hm hea4p.le).trans
      (mul_le_mul_of_nonneg_left hea4 (by norm_num : (0:ℝ) ≤ 1))
  have hs5 : solEulerXDivSqrtdelta (y6*y6) 2 (y5*y5) 2 (y4*y4) 2
      ≤ (1:ℝ) / ea5L := by
    rw [sol_euler5_eq, dlt6_eq, div_le_div_iff₀ hE5 hea5p]
    have hm := nb20_matan_le_one hu5
    exact (mul_le_mul_of_nonneg_right hm hea5p.le).trans
      (mul_le_mul_of_nonneg_left hea5 (by norm_num : (0:ℝ) ≤ 1))
  have hs6 : solEulerXDivSqrtdelta (y4*y4) 2 (y6*y6) 2 (y5*y5) 2
      ≤ (1:ℝ) / ea6L := by
    rw [sol_euler6_eq, dlt4_eq, div_le_div_iff₀ hE6 hea6p]
    have hm := nb20_matan_le_one hu6
    exact (mul_le_mul_of_nonneg_right hm hea6p.le).trans
      (mul_le_mul_of_nonneg_left hea6 (by norm_num : (0:ℝ) ≤ 1))
  have hs4nn : (0:ℝ) ≤ solEulerXDivSqrtdelta (y5*y5) 2 (y4*y4) 2 (y6*y6) 2 := by
    rw [sol_euler4_eq, dlt_swap]
    exact div_nonneg (nb20_matan_nonneg hu4) hE4.le
  have hs5nn : (0:ℝ) ≤ solEulerXDivSqrtdelta (y6*y6) 2 (y5*y5) 2 (y4*y4) 2 := by
    rw [sol_euler5_eq, dlt6_eq]
    exact div_nonneg (nb20_matan_nonneg hu5) hE5.le
  have hs6nn : (0:ℝ) ≤ solEulerXDivSqrtdelta (y4*y4) 2 (y6*y6) 2 (y5*y5) 2 := by
    rw [sol_euler6_eq, dlt4_eq]
    exact div_nonneg (nb20_matan_nonneg hu6) hE6.le
  -- 2. the `dih` slots in explicit form
  have hd4form : dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2
      = 2 * y4 / (y4*y4*(y5*y5 + y6*y6 - y4*y4))
        * matan (4 * (y4*y4) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
          / (y4*y4*(y5*y5 + y6*y6 - y4*y4)) ^ 2) := by
    rw [dih4_eq _ _ _ hy4sq, dlt4_eq, Real.sqrt_mul_self hy4.le]
  have hd5form : dihXDivSqrtdeltaPosbranch (y5*y5) 2 (y4*y4) 2 (y6*y6) 2
      = 2 * y5 / (y5*y5*(y4*y4 + y6*y6 - y5*y5))
        * matan (4 * (y5*y5) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
          / (y5*y5*(y4*y4 + y6*y6 - y5*y5)) ^ 2) := by
    rw [dih5_eq _ _ _ hy5sq, dlt_swap, Real.sqrt_mul_self hy5.le]
  have hd6form : dihXDivSqrtdeltaPosbranch (y6*y6) 2 (y5*y5) 2 (y4*y4) 2
      = 2 * y6 / (y6*y6*(y4*y4 + y5*y5 - y6*y6))
        * matan (4 * (y6*y6) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
          / (y6*y6*(y4*y4 + y5*y5 - y6*y6)) ^ 2) := by
    rw [dih6_eq _ _ _ hy6sq, dlt6_eq, Real.sqrt_mul_self hy6.le]
  -- signs of the matan arguments and of the dih slots
  have hv4nn : (0:ℝ) ≤ 4 * (y4*y4) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      / (y4*y4*(y5*y5 + y6*y6 - y4*y4)) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy4sq) hd0)
      (sq_nonneg (y4*y4*(y5*y5 + y6*y6 - y4*y4)))
  have hv5nn : (0:ℝ) ≤ 4 * (y5*y5) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      / (y5*y5*(y4*y4 + y6*y6 - y5*y5)) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy5sq) hd0)
      (sq_nonneg (y5*y5*(y4*y4 + y6*y6 - y5*y5)))
  have hv6nn : (0:ℝ) ≤ 4 * (y6*y6) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      / (y6*y6*(y4*y4 + y5*y5 - y6*y6)) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy6sq) hd0)
      (sq_nonneg (y6*y6*(y4*y4 + y5*y5 - y6*y6)))
  have hd4nn : (0:ℝ) ≤ dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2 := by
    rw [hd4form]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hy4.le) hdx4nn.le)
      (nb20_matan_nonneg hv4nn)
  have hd5nn : (0:ℝ) ≤ dihXDivSqrtdeltaPosbranch (y5*y5) 2 (y4*y4) 2 (y6*y6) 2 := by
    rw [hd5form]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hy5.le) hdx5nn.le)
      (nb20_matan_nonneg hv5nn)
  have hd6nn : (0:ℝ) ≤ dihXDivSqrtdeltaPosbranch (y6*y6) 2 (y5*y5) 2 (y4*y4) 2 := by
    rw [hd6form]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hy6.le) hdx6nn.le)
      (nb20_matan_nonneg hv6nn)
  -- 3. `d4 <= DU := 2*p4h/dx4L`
  have hd4ub : dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2
      ≤ (2:ℝ) * p4h / dx4L := by
    rw [hd4form]
    have hF : 2 * y4 / (y4*y4*(y5*y5 + y6*y6 - y4*y4)) ≤ (2:ℝ) * p4h / dx4L := by
      rw [div_le_div_iff₀ hdx4nn hdx4p]
      exact nb20_mul4 (by linarith) hdx4 (mul_nonneg (by norm_num) hy4.le)
        hdx4p.le (mul_nonneg (by norm_num) (by linarith))
    have hM := nb20_matan_le_one hv4nn
    have hprod := nb20_mul4 hF hM
      (div_nonneg (mul_nonneg (by norm_num) hy4.le) hdx4nn.le)
      (nb20_matan_nonneg hv4nn)
      (div_nonneg (mul_nonneg (by norm_num) (by linarith)) hdx4p.le)
    linarith [hprod]
  -- 4. the Taylor remainders' nonnegativity (`v <= 3` corners)
  have hW5 : (4:ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) ≤ (3:ℝ) := by
    rw [div_le_iff₀ (show (0:ℝ) < dx5L * dx5L by nlinarith [hdx5p])]
    linarith [hv5]
  have hC5 : (0:ℝ) ≤ (1:ℝ) - (4:ℝ) * (p5h * p5h) * Dh
      / (dx5L * dx5L) / (3:ℝ) := by linarith [hW5]
  have hW6 : (4:ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) ≤ (3:ℝ) := by
    rw [div_le_iff₀ (show (0:ℝ) < dx6L * dx6L by nlinarith [hdx6p])]
    linarith [hv6]
  have hC6 : (0:ℝ) ≤ (1:ℝ) - (4:ℝ) * (q6h * q6h) * Dh
      / (dx6L * dx6L) / (3:ℝ) := by linarith [hW6]
  -- 5. `d5` lower bound: `(2*p5l/dx5H)*(1-v5h/3) <= d5`
  have hd5lb : (2:ℝ) * p5l / dx5H * ((1:ℝ) - (4:ℝ) * (p5h * p5h) * Dh
        / (dx5L * dx5L) / (3:ℝ))
      ≤ dihXDivSqrtdeltaPosbranch (y5*y5) 2 (y4*y4) 2 (y6*y6) 2 := by
    rw [hd5form]
    have hp5h : (0:ℝ) ≤ p5h := by linarith
    have hnum : (y5*y5) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
        ≤ (p5h * p5h) * Dh :=
      nb20_mul4 hy5p5sq hdh (mul_nonneg hy5.le hy5.le) hd0
        (mul_nonneg hp5h hp5h)
    have hden : (dx5L) * (dx5L)
        ≤ (y5*y5*(y4*y4 + y6*y6 - y5*y5)) ^ 2 := by
      have hp : (0:ℝ) < y5*y5*(y4*y4 + y6*y6 - y5*y5) + dx5L := by
        have := hdx5nn; linarith [hdx5p]
      nlinarith [hdx5, hp]
    have hv5le : (4:ℝ) * (y5*y5) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
        / (y5*y5*(y4*y4 + y6*y6 - y5*y5)) ^ 2
        ≤ (4:ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) := by
      rw [div_le_div_iff₀ (pow_pos hdx5nn 2)
        (show (0:ℝ) < dx5L * dx5L by nlinarith [hdx5p])]
      exact nb20_mul4 (by linarith [hnum]) hden
        (mul_nonneg (mul_nonneg (by norm_num) hy5sq) hd0)
        (mul_nonneg hdx5p.le hdx5p.le)
        (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hp5h hp5h)) hdhp)
    have hT5 := nb20_matan_ge_taylor hv5nn
    have hM : (1:ℝ) - (4:ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3:ℝ)
        ≤ matan (4 * (y5*y5) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
          / (y5*y5*(y4*y4 + y6*y6 - y5*y5)) ^ 2) := by
      linarith [hT5, hv5le]
    have hF : (2:ℝ) * p5l / dx5H ≤ (2:ℝ) * y5
        / (y5*y5*(y4*y4 + y6*y6 - y5*y5)) := by
      rw [div_le_div_iff₀ hdx5p' hdx5nn]
      exact nb20_mul4 (by linarith) hdx5'
        (mul_nonneg (by norm_num) hp5l)
        hdx5nn.le (mul_nonneg (by norm_num) hy5.le)
    exact nb20_mul4 hF hM
      (div_nonneg (mul_nonneg (by norm_num) hp5l) hdx5p'.le) hC5
      (div_nonneg (mul_nonneg (by norm_num) hy5.le) hdx5nn.le)
  -- 6. `d6` lower bound: `(2*q6l/dx6H)*(1-v6h/3) <= d6`
  have hd6lb : (2:ℝ) * q6l / dx6H * ((1:ℝ) - (4:ℝ) * (q6h * q6h) * Dh
        / (dx6L * dx6L) / (3:ℝ))
      ≤ dihXDivSqrtdeltaPosbranch (y6*y6) 2 (y5*y5) 2 (y4*y4) 2 := by
    rw [hd6form]
    have hq6l0 : (0:ℝ) ≤ q6l := by linarith
    have hq6h0 : (0:ℝ) ≤ q6h := by linarith
    have hnum : (y6*y6) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
        ≤ (q6h * q6h) * Dh :=
      nb20_mul4 hy6q6 hdh hy6sq hd0 (mul_nonneg hq6h0 hq6h0)
    have hden : (dx6L) * (dx6L)
        ≤ (y6*y6*(y4*y4 + y5*y5 - y6*y6)) ^ 2 := by
      have hp : (0:ℝ) < y6*y6*(y4*y4 + y5*y5 - y6*y6) + dx6L := by
        have := hdx6nn; linarith [hdx6p]
      nlinarith [hdx6, hp]
    have hv6le : (4:ℝ) * (y6*y6) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
        / (y6*y6*(y4*y4 + y5*y5 - y6*y6)) ^ 2
        ≤ (4:ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) := by
      rw [div_le_div_iff₀ (pow_pos hdx6nn 2)
        (show (0:ℝ) < dx6L * dx6L by nlinarith [hdx6p])]
      exact nb20_mul4 (by linarith [hnum]) hden
        (mul_nonneg (mul_nonneg (by norm_num) hy6sq) hd0)
        (mul_nonneg hdx6p.le hdx6p.le)
        (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hq6h0 hq6h0)) hdhp)
    have hT6 := nb20_matan_ge_taylor hv6nn
    have hM : (1:ℝ) - (4:ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3:ℝ)
        ≤ matan (4 * (y6*y6) * deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
          / (y6*y6*(y4*y4 + y5*y5 - y6*y6)) ^ 2) := by
      linarith [hT6, hv6le]
    have hF : (2:ℝ) * q6l / dx6H ≤ (2:ℝ) * y6
        / (y6*y6*(y4*y4 + y5*y5 - y6*y6)) := by
      rw [div_le_div_iff₀ hdx6p' hdx6nn]
      exact nb20_mul4 (by linarith) hdx6'
        (mul_nonneg (by norm_num) hq6l0)
        hdx6nn.le (mul_nonneg (by norm_num) hy6.le)
    exact nb20_mul4 hF hM
      (div_nonneg (mul_nonneg (by norm_num) hq6l0) hdx6p'.le) hC6
      (div_nonneg (mul_nonneg (by norm_num) hy6.le) hdx6nn.le)
  -- 7. the `w2aF` identity
  have hG := nb19_w2aG_explicit y4 y5 y6 hy4.le hy5.le hy6.le
  have hD := nb19_w2aD_explicit y4 y5 y6
  have hev : w2aF y4 y5 y6 =
      (1:ℝ)/12/2
      - (2*mm1/Real.pi)/2 * (solEulerXDivSqrtdelta (y5*y5) 2 (y4*y4) 2 (y6*y6) 2
        + solEulerXDivSqrtdelta (y6*y6) 2 (y5*y5) 2 (y4*y4) 2
        + solEulerXDivSqrtdelta (y4*y4) 2 (y6*y6) 2 (y5*y5) 2)
      + (8*mm2/Real.pi)/2 * (lfun (y4*0.5) * h0cut y4
            * dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2)
      + (8*mm2/Real.pi)/2 * (lfun (y5*0.5) * h0cut y5
            * dihXDivSqrtdeltaPosbranch (y5*y5) 2 (y4*y4) 2 (y6*y6) 2)
      + (8*mm2/Real.pi)/2 * (lfun (y6*0.5) * 1
            * dihXDivSqrtdeltaPosbranch (y6*y6) 2 (y5*y5) 2 (y4*y4) 2)
      - (0.008:ℝ) * dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2 := by
    unfold w2aF
    rw [hG, hD]
    ring
  -- 8. part bounds
  have hpart1 : (2*mm1/Real.pi)/2 * (solEulerXDivSqrtdelta (y5*y5) 2 (y4*y4) 2 (y6*y6) 2
        + solEulerXDivSqrtdelta (y6*y6) 2 (y5*y5) 2 (y4*y4) 2
        + solEulerXDivSqrtdelta (y4*y4) 2 (y6*y6) 2 (y5*y5) 2)
      ≤ (0.64437:ℝ)/2 * ((1:ℝ)/ea4L + (1:ℝ)/ea5L + (1:ℝ)/ea6L) :=
    nb20_mul4 (by linarith [nb20_k1])
      (by linarith [hs4, hs5, hs6])
      (by linarith [nb20_k1_pos]) (by linarith [hs4nn, hs5nn, hs6nn])
      (by norm_num)
  have hA4 : (0.06468:ℝ)/2 * m4 ≤ (8*mm2/Real.pi)/2 * (lfun (y4*0.5) * h0cut y4) :=
    nb20_mul4 (by linarith [nb20_k2]) hm4 (by norm_num) hm4p
      (by linarith [nb20_k2])
  have hB4 : (0:ℝ) ≤ (8*mm2/Real.pi)/2 * (lfun (y4*0.5) * h0cut y4) := by
    apply mul_nonneg <;> linarith [nb20_k2, nb19_h0cut_lfun_nonneg hy4.le]
  have hd4part : (0.06468:ℝ)/2 * (m4 * ((2:ℝ)*p4h/dx4L))
        - (0.008:ℝ) * ((2:ℝ)*p4h/dx4L)
      ≤ (8*mm2/Real.pi)/2 * (lfun (y4*0.5) * h0cut y4
          * dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2)
        - (0.008:ℝ) * dihXDivSqrtdeltaPosbranch (y4*y4) 2 (y6*y6) 2 (y5*y5) 2 := by
    have hB := mul_le_mul_of_nonneg_right hA4 hd4nn
    have hcoef' : (0.06468:ℝ)/2 * m4 - (0.008:ℝ) ≤ 0 := by linarith [hcoef]
    have hC := mul_le_mul_of_nonpos_right hd4ub hcoef'
    linarith [hB, hC]
  have hA5 : (0.06468:ℝ)/2 * m5 ≤ (8*mm2/Real.pi)/2 * (lfun (y5*0.5) * h0cut y5) :=
    nb20_mul4 (by linarith [nb20_k2]) hm5 (by norm_num) hm5p
      (by linarith [nb20_k2])
  have hB5 : (0:ℝ) ≤ (8*mm2/Real.pi)/2 * (lfun (y5*0.5) * h0cut y5) := by
    apply mul_nonneg <;> linarith [nb20_k2, nb19_h0cut_lfun_nonneg hy5.le]
  have hd5part : (0.06468:ℝ)/2 * (m5 * ((2:ℝ)*p5l/dx5H
          * ((1:ℝ) - (4:ℝ)*(p5h*p5h)*Dh/(dx5L*dx5L)/(3:ℝ))))
      ≤ (8*mm2/Real.pi)/2 * (lfun (y5*0.5) * h0cut y5
          * dihXDivSqrtdeltaPosbranch (y5*y5) 2 (y4*y4) 2 (y6*y6) 2) := by
    have hD5nn : (0:ℝ) ≤ (2:ℝ)*p5l/dx5H
        * ((1:ℝ) - (4:ℝ)*(p5h*p5h)*Dh/(dx5L*dx5L)/(3:ℝ)) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (by linarith : (0:ℝ) ≤ p5l)) hdx5p'.le) hC5
    have hchain := (mul_le_mul_of_nonneg_right hA5 hD5nn).trans
      (mul_le_mul_of_nonneg_left hd5lb hB5)
    linarith [hchain]
  have hA6 : (0.06468:ℝ)/2 * l6v ≤ (8*mm2/Real.pi)/2 * (lfun (y6*0.5)) :=
    nb20_mul4 (by linarith [nb20_k2]) hl6 (by norm_num) hl6p
      (by linarith [nb20_k2])
  have hB6 : (0:ℝ) ≤ (8*mm2/Real.pi)/2 * (lfun (y6*0.5)) := by
    apply mul_nonneg <;> linarith [nb20_k2, hl6p, hl6]
  have hd6part : (0.06468:ℝ)/2 * (l6v * ((2:ℝ)*q6l/dx6H
          * ((1:ℝ) - (4:ℝ)*(q6h*q6h)*Dh/(dx6L*dx6L)/(3:ℝ))))
      ≤ (8*mm2/Real.pi)/2 * (lfun (y6*0.5)
          * dihXDivSqrtdeltaPosbranch (y6*y6) 2 (y5*y5) 2 (y4*y4) 2) := by
    have hD6nn : (0:ℝ) ≤ (2:ℝ)*q6l/dx6H
        * ((1:ℝ) - (4:ℝ)*(q6h*q6h)*Dh/(dx6L*dx6L)/(3:ℝ)) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (by linarith : (0:ℝ) ≤ q6l)) hdx6p'.le) hC6
    have hchain := (mul_le_mul_of_nonneg_right hA6 hD6nn).trans
      (mul_le_mul_of_nonneg_left hd6lb hB6)
    linarith [hchain]
  -- 9. final assembly
  rw [hev]
  linarith [hpart1, hd4part, hd5part, hd6part, hmargin]

/-! ## 10. Vacuity -/

/-- Vacuity criterion: a negative lower-corner Delta makes the cell's core
obligation vacuous (`0 ≤ deltaX` fails everywhere on the cell). -/
theorem cell_vacuous {y4 y5 y6 P4L P5L Q6L : ℝ}
    (h4l : (2.4635:ℝ) ≤ y4) (h4h : y4 ≤ Real.sqrt 8)
    (h5l : (2.4635:ℝ) ≤ y5) (h5h : y5 ≤ Real.sqrt 8)
    (h6l : (2:ℝ) ≤ y6) (h6h : y6 ≤ 2.46352)
    (h4c : P4L ≤ y4) (h5c : P5L ≤ y5) (h6c : Q6L ≤ y6)
    (h4ge : (2.4635:ℝ) ≤ P4L) (h5ge : (2.4635:ℝ) ≤ P5L)
    (h6ge : (2:ℝ) ≤ Q6L) (h6le : Q6L ≤ 2.46352)
    (hdlt : 2 * (4 * (P5L^2) * (Q6L^2) - (P4L^2 - P5L^2 - Q6L^2)^2)
        - (P4L^2) * (P5L^2) * (Q6L^2) < 0) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  intro h0
  have h := dlt_corner h4l h4h h5l h5h h6l h6h h4c h5c h6c h4ge h5ge h6ge h6le
  linarith

/-- Demo: one of the 9 design-vacuous cells (truncated corner 2.75132034,
the midpoint of `√2 + 1.26` and `√8`). -/
theorem cell_vac_demo {y4 y5 y6 : ℝ}
    (hc4 : (2.75132034:ℝ) ≤ y4) (hc4' : y4 ≤ Real.sqrt 8)
    (hc5 : (2.4635:ℝ) ≤ y5) (hc5' : y5 ≤ Real.sqrt 8)
    (hc6 : (2:ℝ) ≤ y6) (hc6' : y6 ≤ (2.058:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  refine cell_vacuous (by linarith) hc4' hc5 hc5' hc6 (by linarith)
    hc4 hc5 hc6 (by norm_num) (by norm_num) le_rfl (by norm_num) ?_
  norm_num

/-! ## 11. The representative real cell (design cell[0], truncated corners) -/

/-- **Representative real cell**: design cell[0]
`y4 ∈ [√2 + 1.26, √8]`, `y5 ∈ [2.52, √8]`, `y6 ∈ [2, 2.058]` with truncated
decimal corners; the core obligation `0 < w2aF` holds on it wherever
`0 ≤ deltaX` — machine-checked via `w2a_cell` with the
`layered3.cell_lb` certificate (margin `+0.0012138…`). -/
theorem cell00_core {y4 y5 y6 : ℝ}
    (hc4 : (2.67421356:ℝ) ≤ y4) (hc4' : y4 ≤ Real.sqrt 8)
    (hc5 : (2.52:ℝ) ≤ y5) (hc5' : y5 ≤ Real.sqrt 8)
    (hc6 : (2:ℝ) ≤ y6) (hc6' : y6 ≤ (2.058:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  -- corner facts
  have hy4 : (0:ℝ) < y4 := by linarith
  have hy5 : (0:ℝ) < y5 := by linarith
  have hy6 : (0:ℝ) < y6 := by linarith
  have hP4Lle : (2.67421356:ℝ) * 2.67421356 ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356) hc4
  have hP5Lle : (2.52:ℝ) * 2.52 ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5
  have hQ6Lle : (2:ℝ) * 2 ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2) hc6
  have hQ6Hge : y6 * y6 ≤ (2.058:ℝ) * 2.058 :=
    mul_self_le_mul_self hy6.le hc6'
  have hP4Hge : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4.le hc4'
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hP5Hge : y5 * y5 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy5.le hc5'
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  -- Delta upper corner via dlt_corner (exact expression form)
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
      ≤ 2 * (4 * (2.52^2) * (2^2) - (2.67421356^2 - 2.52^2 - 2^2)^2)
        - (2.67421356^2) * (2.52^2) * (2^2) :=
    dlt_corner (by linarith) hc4' (by linarith) hc5' hc6 (by linarith)
      hc4 hc5 hc6 (by norm_num) (by norm_num) le_rfl (by norm_num)
  -- exact square roots at the corners
  have hsq52 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq67 : Real.sqrt ((2.67421356:ℝ) * 2.67421356) = 2.67421356 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356)]
  have hsq2 : Real.sqrt ((2:ℝ) * 2) = 2 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  -- ea4 (s4-slot) corner minimum at (2.52², 2.058², 2.67421356²)
  have hea4min : (33.5847:ℝ)
      ≤ ea4X (2.52*2.52) (2.058*2.058) (2.67421356*2.67421356) := by
    unfold ea4X
    rw [hsq52, hsq67]
    have hr : (9.53041:ℝ)
        ≤ Real.sqrt (2 * (2.52*2.52) * (2.67421356*2.67421356)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := nb20_sqrt2.1
    have hX : (0:ℝ) ≤ ((2.52*2.52) + (2.67421356*2.67421356)
        - (2.058*2.058)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (9.010786:ℝ) ≤ (2.67421356:ℝ) * 2.67421356 * 2.52 / 2 := by norm_num
    have hC2 : (8.491162:ℝ) ≤ (2.52:ℝ) * 2.52 * 2.67421356 / 2 := by norm_num
    have hT3 : (6.552372:ℝ) ≤ Real.sqrt 2 * ((2.52*2.52) + (2.67421356*2.67421356)
        - (2.058*2.058)) / 2 := by
      have hval : (6.552372:ℝ) ≤ (1.41421356:ℝ) * ((2.52*2.52)
          + (2.67421356*2.67421356) - (2.058*2.058)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X (2.52*2.52) (2.058*2.058) (2.67421356*2.67421356)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X (2.52*2.52) (2.058*2.058) (2.67421356*2.67421356)
        ≤ ea4X (y5*y5) (2.058*2.058) (2.67421356*2.67421356) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ 2.67421356*2.67421356) hP5Lle
    have s2 : ea4X (y5*y5) (2.058*2.058) (2.67421356*2.67421356)
        ≤ ea4X (y5*y5) (y6*y6) (2.67421356*2.67421356) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) (2.67421356*2.67421356)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  -- ea5 (s5-slot) corner minimum at (2.52², 4, 8)
  have hea5min : (20.18:ℝ) ≤ ea5X (2.52*2.52) ((2:ℝ)*2) ((8:ℝ)) := by
    unfold ea5X
    rw [hsq52, hsq2]
    have hr : (7.127636:ℝ) ≤ Real.sqrt (2 * (2.52*2.52) * ((2:ℝ)*2)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := nb20_sqrt2.1
    have hX : (0:ℝ) ≤ ((2.52*2.52) + ((2:ℝ)*2) - (8:ℝ)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.350399:ℝ) ≤ (2.52:ℝ) * 2.52 * 2 / 2 := by norm_num
    have hC2 : (5.04:ℝ) ≤ ((2:ℝ)*2) * 2.52 / 2 := by norm_num
    have hT3 : (1.661983:ℝ) ≤ Real.sqrt 2 * ((2.52*2.52) + ((2:ℝ)*2) - (8:ℝ)) / 2 := by
      have hval : (1.661983:ℝ) ≤ (1.41421356:ℝ) * ((2.52*2.52)
          + ((2:ℝ)*2) - (8:ℝ)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X (2.52*2.52) ((2:ℝ)*2) ((8:ℝ))
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X (2.52*2.52) ((2:ℝ)*2) ((8:ℝ))
        ≤ ea5X (y5*y5) ((2:ℝ)*2) ((8:ℝ)) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2:ℝ)*2) hP5Lle
    have s2 : ea5X (y5*y5) ((2:ℝ)*2) ((8:ℝ))
        ≤ ea5X (y5*y5) (y6*y6) ((8:ℝ)) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((8:ℝ))
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  -- ea6 (s6-slot) corner minimum at (8, 4, 2.67421356²)
  have hea6min : (22.292:ℝ)
      ≤ ea6X ((8:ℝ)) ((2:ℝ)*2) (2.67421356*2.67421356) := by
    unfold ea6X
    rw [hsq67, hsq2]
    have hr : (7.563818:ℝ)
        ≤ Real.sqrt (2 * ((2:ℝ)*2) * (2.67421356*2.67421356)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := nb20_sqrt2.1
    have hX : (0:ℝ) ≤ (((2:ℝ)*2) + (2.67421356*2.67421356) - (8:ℝ)) / 2 := by
      norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.348427:ℝ) ≤ ((2:ℝ)*2) * 2.67421356 / 2 := by norm_num
    have hC2 : (7.151418:ℝ) ≤ (2.67421356:ℝ) * 2.67421356 * 2 / 2 := by norm_num
    have hT3 : (2.228389:ℝ) ≤ Real.sqrt 2 * (((2:ℝ)*2)
        + (2.67421356*2.67421356) - (8:ℝ)) / 2 := by
      have hval : (2.228389:ℝ) ≤ (1.41421356:ℝ) * (((2:ℝ)*2)
          + (2.67421356*2.67421356) - (8:ℝ)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2:ℝ)*2) (2.67421356*2.67421356)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2:ℝ)*2) (2.67421356*2.67421356)
        ≤ ea6X (y5*y5) ((2:ℝ)*2) (2.67421356*2.67421356) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2:ℝ)*2) (2.67421356*2.67421356)
        ≤ ea6X (y5*y5) (y6*y6) (2.67421356*2.67421356) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ 2.67421356*2.67421356) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) (2.67421356*2.67421356)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  -- dx corners
  have hdx4 : (2.67421356:ℝ) * 2.67421356
        * ((2.52:ℝ) * 2.52 + (2:ℝ) * 2 - (8:ℝ))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < (2.67421356:ℝ) * 2.67421356
      * ((2.52:ℝ) * 2.52 + (2:ℝ) * 2 - (8:ℝ)) := by norm_num
  have hdx5 : (2.52:ℝ) * 2.52
        * ((2.67421356:ℝ) * 2.67421356 + (2:ℝ) * 2 - (8:ℝ))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < (2.52:ℝ) * 2.52
      * ((2.67421356:ℝ) * 2.67421356 + (2:ℝ) * 2 - (8:ℝ)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ (8:ℝ) * ((8:ℝ) + (2.058:ℝ) * 2.058 - (2.52:ℝ) * 2.52) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < (8:ℝ) * ((8:ℝ) + (2.058:ℝ) * 2.058 - (2.52:ℝ) * 2.52) := by
    norm_num
  have hdx6 : (2:ℝ) * 2
        * ((2.67421356:ℝ) * 2.67421356 + (2.52:ℝ) * 2.52 - (2.058:ℝ) * 2.058)
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < (2:ℝ) * 2
      * ((2.67421356:ℝ) * 2.67421356 + (2.52:ℝ) * 2.52 - (2.058:ℝ) * 2.058) := by
    norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ (2.058:ℝ) * 2.058 * ((8:ℝ) + (8:ℝ) - (2:ℝ) * 2) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < (2.058:ℝ) * 2.058 * ((8:ℝ) + (8:ℝ) - (2:ℝ) * 2) := by
    norm_num
  -- smoothing factors
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.88846153:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6' (by rw [h0v]; norm_num)
    have h2 : (0.88846153:ℝ) ≤ lfun (2.058 * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  -- the certificate
  refine w2a_cell (p4h := (2.82842713:ℝ)) (p5l := (2.52:ℝ)) (p5h := (8:ℝ))
    (q6l := (2:ℝ)) (q6h := (2.058:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2^2) - (2.67421356^2 - 2.52^2 - 2^2)^2)
        - (2.67421356^2) * (2.52^2) * (2^2))
    (ea4L := (33.5847:ℝ)) (ea5L := (20.18:ℝ)) (ea6L := (22.292:ℝ))
    (dx4L := (2.67421356:ℝ) * 2.67421356
        * ((2.52:ℝ) * 2.52 + (2:ℝ) * 2 - (8:ℝ)))
    (dx5L := (2.52:ℝ) * 2.52
        * ((2.67421356:ℝ) * 2.67421356 + (2:ℝ) * 2 - (8:ℝ)))
    (dx5H := (8:ℝ) * ((8:ℝ) + (2.058:ℝ) * 2.058 - (2.52:ℝ) * 2.52))
    (dx6L := (2:ℝ) * 2
        * ((2.67421356:ℝ) * 2.67421356 + (2.52:ℝ) * 2.52 - (2.058:ℝ) * 2.058))
    (dx6H := (2.058:ℝ) * 2.058 * ((8:ℝ) + (8:ℝ) - (2:ℝ) * 2))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.88846153:ℝ))
    (hb4 := by linarith) (hb4' := hc4') (hb5 := by linarith) (hb5' := hc5')
    (hq6l := le_rfl) (hq6h := by norm_num)
    (hc4' := hc4'.trans nb20_sqrt8.2) (hc5 := hc5) (hc5' := (hc5'.trans nb20_sqrt8.2).trans (by norm_num : (2.82842713:ℝ) ≤ (8:ℝ)))
    (hc6 := hc6) (hc6' := hc6') (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := le_rfl)
    (hm5 := hm5zero) (hm5p := le_rfl)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

/-! ## 12. Consumption of the reduction interface -/

/-- **Consumption demo**: `Kepler.NliBanks19.bank_QZECFICwt2A_of_core`
applied to the hcore built from the cell-00 piece plus a residual covering
all points outside cell[0] (the other 61 design cells' obligations).  This
is the exact production pattern: 52 more real-cell instances like
`cell00_core` and 9 more vacuity instances like `cell_vac_demo` close the
residual. -/
theorem bank_wt2A_of_cell00
    (hrest : ∀ y4 y5 y6 : ℝ, (2.4635:ℝ) ≤ y4 → y4 ≤ Real.sqrt 8 →
      (2.4635:ℝ) ≤ y5 → y5 ≤ Real.sqrt 8 → (2:ℝ) ≤ y6 → y6 ≤ 2.46352 →
      (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 →
      ¬ ((2.67421356:ℝ) ≤ y4 ∧ (2.52:ℝ) ≤ y5 ∧ y6 ≤ (2.058:ℝ)) →
      (0:ℝ) < w2aF y4 y5 y6) :
    bank_QZECFICwt2A := by
  refine bank_QZECFICwt2A_of_core (fun y4 y5 y6 h4 h4' h5 h5' h6 h6' hd => ?_)
  by_cases hcell : ((2.67421356:ℝ) ≤ y4 ∧ (2.52:ℝ) ≤ y5 ∧ y6 ≤ (2.058:ℝ))
  · exact cell00_core hcell.1 h4' hcell.2.1 h5' h6 hcell.2.2 hd
  · exact hrest y4 y5 y6
      (by linarith [h4, Kepler.NliBanks17.nb17_two_hminus_bounds.1]) h4'
      (by linarith [h5, Kepler.NliBanks17.nb17_two_hminus_bounds.1]) h5' h6
      (by linarith [h6', Kepler.NliBanks17.nb17_two_hminus_bounds.2]) hd hcell

/-! ## 13. Axiom audit -/

#print axioms nb20_k1_pos
#print axioms nb20_matan_nonneg
#print axioms dlt_swap
#print axioms inner_pos_box
#print axioms dlt_corner
#print axioms w2a_cell
#print axioms cell_vacuous
#print axioms cell_vac_demo
#print axioms cell00_core
#print axioms bank_wt2A_of_cell00

end Kepler.NliBanks20

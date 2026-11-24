import Kepler.NliBanks21
import Kepler.Text.Wt1TowerTower

set_option maxHeartbeats 4000000

namespace Kepler.Text
open Kepler.NliBanks12
open Kepler.NliBanks17
open Kepler.NliBanks19
open Kepler.NliBanks20
open Kepler.NliBanks21

/-
Kepler.Text.Wt1Edges — lane `wt1-edges-cert-w1` (2026-11-24): the matan
bracket suite + sharper constants for the wt1 Route-B gap G6 (the three 1D
edge certificates `hE00`/`hE01`/`hE11` consumed by `bank_QZECFICwt1_from_tower`,
Wt1TowerTower.lean:142).

STATUS (honest): the bracket INFRASTRUCTURE is complete and compiles
(RC=0, every theorem exactly `[propext, Classical.choice, Quot.sound]`):

* `wt1e_atan_le_p13` / `wt1e_atan_ge_p15` — alternating arctan partials of
  orders 13/15 (valid for all `s ≥ 0`; no small-`s` restriction), plus
  `wt1e_p15_mono`;
* `wt1e_matan_ub_big` / `wt1e_matan_lb_big` — two-sided `matan` brackets for
  large positive arguments (`t ≥ 4`, the E00/E01/E11 D4 slot), via
  `arctan s = π/2 − arctan(1/s)` (`wt1e_atan_add_inv`) and `wt1eP15`/`wt1eP13`;
* `wt1e_matan_ub_neg` — `matan` upper bracket for negative arguments
  down to `−0.36` (the E11 D4 slot), via the artanh tail
  `nb12w_artanh_le_sub7`;
* `wt1e_matan_ub_small` / `wt1e_matan_lb_small` / `wt1e_matan_br_small_neg` —
  re-exports of the `nb12w` cubic brackets;
* `wt1e_alpha_br` — `arctan(√2) ∈ [0.95531638, 0.95531671]` via the
  tangent-addition route `arctan(√2) = π/4 + arctan(3−2√2)`
  (`wt1e_w_br`, `wt1e_alpha_split`, `wt1e_not_halfpi`, `wt1e_atan_add_inv`).

NOT yet in this file (remaining emission work, fully designed and
numerics-verified in `scripts/model.py` + `scripts/check_all.py` of the lane
snapshot): the three top-level edge theorems themselves

  `wt1e_E00 : ∀ y4 ∈ [2*hminus, 2*hplus], 0 < w1aF y4 2 2`
  `wt1e_E01 : ∀ y4 ∈ [2*hminus, 2*hplus], 0 < w1aF y4 2 (2*hminus)`
  `wt1e_E11 : ∀ y4 ∈ [2*hminus, 2*hplus], 0 < w1aF y4 (2*hminus) (2*hminus)`

which are assembled from 37/7/7 rational pieces (`wt1e_E00_pNN` etc.), each
proven by: explicit-kernel rewrite (`wt1e_E00_explicit`-shaped lemma, to be
emitted) + corner bounds + the bracket suite above + one `linarith`.  The
complete per-piece literal tables (37/7/7 pieces, every margin positive,
worst E00 `L = +1.1·10⁻⁵` at `[2.518, 2.519]`), the soundness sweep and the
data-lane cross-checks are in `out/selfcheck.json` / `DELIVERY.md`.  The
assembly-lemma template (`wt1e_E00_aux`-shaped, one per edge) and the two
piece-independent aux proofs are specified in `scripts/gen_lean.py` +
`ASSEMBLY_SPEC.md` §G6.

Also unfinished: sharper `K1`/`K2` closing `nlinarith`s — see the NOTE in
§5bis; until restored, thin E00 kink pieces need `nb20_k1`/`nb20_k2` with
~2× finer slicing (width ≤ 0.0005 at `|y4 − 2.52| ≤ 0.01`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/

/-! ## 1. √2 and π literals -/

/-- `√2 ∈ [1.41421356, 1.4142136]`. -/
theorem wt1e_sqrt2_br : (1.41421356 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.4142136 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num : (1.41421356 : ℝ) ^ 2 ≤ 2)
  · rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1.4142136)]
    norm_num

/-- `π ∈ [3.141592, 3.141593]`. -/
theorem wt1e_pi_br : (3.141592 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 3.141593 :=
  ⟨Real.pi_gt_d6.le, Real.pi_lt_d6.le⟩

/-- `1 ≤ √2`. -/
theorem wt1e_sqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
  have := wt1e_sqrt2_br
  linarith

/-- `Real.sqrt 4 = 2`. -/
theorem wt1e_sqrt4 : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)

/-! ## 2. Alternating arctan partials of order 13 and 15 -/

/-- Order-13 alternating partial (ends `+s¹³/13`). -/
noncomputable def wt1eP13 (s : ℝ) : ℝ :=
  s - s ^ 3 / 3 + s ^ 5 / 5 - s ^ 7 / 7 + s ^ 9 / 9 - s ^ 11 / 11 + s ^ 13 / 13

/-- Order-15 alternating partial (ends `−s¹⁵/15`). -/
noncomputable def wt1eP15 (s : ℝ) : ℝ :=
  s - s ^ 3 / 3 + s ^ 5 / 5 - s ^ 7 / 7 + s ^ 9 / 9 - s ^ 11 / 11 + s ^ 13 / 13 - s ^ 15 / 15

/-- `arctan s ≤ wt1eP13 s` for `s ≥ 0` (gap derivative `s¹⁴/(1+s²) ≥ 0`). -/
theorem wt1e_atan_le_p13 (s : ℝ) (hs : 0 ≤ s) : Real.arctan s ≤ wt1eP13 s := by
  have h := nb12_nonneg_of_deriv
    (f := fun x : ℝ => wt1eP13 x - Real.arctan x)
    (hC := by unfold wt1eP13; fun_prop)
    (hD := (by fun_prop : Differentiable ℝ (fun x : ℝ =>
      x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 + x ^ 9 / 9 - x ^ 11 / 11
        + x ^ 13 / 13)).sub Real.differentiable_arctan)
    (h0 := by norm_num [wt1eP13])
    (hd := by
      intro x _
      have hP : HasDerivAt (fun y : ℝ => wt1eP13 y)
          (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12) x := by
        have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
          simpa [pow_succ] using (hasDerivAt_pow 3 x).div_const 3
        have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
          simpa [pow_succ] using (hasDerivAt_pow 5 x).div_const 5
        have h7 : HasDerivAt (fun y : ℝ => y ^ 7 / 7) (x ^ 6) x := by
          simpa [pow_succ] using (hasDerivAt_pow 7 x).div_const 7
        have h9 : HasDerivAt (fun y : ℝ => y ^ 9 / 9) (x ^ 8) x := by
          simpa [pow_succ] using (hasDerivAt_pow 9 x).div_const 9
        have h11 : HasDerivAt (fun y : ℝ => y ^ 11 / 11) (x ^ 10) x := by
          simpa [pow_succ] using (hasDerivAt_pow 11 x).div_const 11
        have h13 : HasDerivAt (fun y : ℝ => y ^ 13 / 13) (x ^ 12) x := by
          simpa [pow_succ] using (hasDerivAt_pow 13 x).div_const 13
        exact (((((((hasDerivAt_id x).sub h3).add h5).sub h7).add h9).sub h11).add h13)
      have h2 : HasDerivAt (fun y : ℝ => wt1eP13 y - Real.arctan y)
          (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - 1 / (1 + x ^ 2)) x :=
        hP.sub (Real.hasDerivAt_arctan x)
      rw [h2.deriv]
      have hq : 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - 1 / (1 + x ^ 2)
          = x ^ 14 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [hq]
      positivity)
    s hs
  linarith

/-- `wt1eP15 s ≤ arctan s` for `s ≥ 0` (gap derivative `s¹⁶/(1+s²) ≥ 0`). -/
theorem wt1e_atan_ge_p15 (s : ℝ) (hs : 0 ≤ s) : wt1eP15 s ≤ Real.arctan s := by
  have h := nb12_nonneg_of_deriv
    (f := fun x : ℝ => Real.arctan x - wt1eP15 x)
    (hC := by unfold wt1eP15; fun_prop)
    (hD := Real.differentiable_arctan.sub (by fun_prop : Differentiable ℝ (fun x : ℝ =>
      x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 + x ^ 9 / 9 - x ^ 11 / 11 + x ^ 13 / 13
        - x ^ 15 / 15)))
    (h0 := by norm_num [wt1eP15])
    (hd := by
      intro x _
      have hP : HasDerivAt (fun y : ℝ => wt1eP15 y)
          (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14) x := by
        have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
          simpa [pow_succ] using (hasDerivAt_pow 3 x).div_const 3
        have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
          simpa [pow_succ] using (hasDerivAt_pow 5 x).div_const 5
        have h7 : HasDerivAt (fun y : ℝ => y ^ 7 / 7) (x ^ 6) x := by
          simpa [pow_succ] using (hasDerivAt_pow 7 x).div_const 7
        have h9 : HasDerivAt (fun y : ℝ => y ^ 9 / 9) (x ^ 8) x := by
          simpa [pow_succ] using (hasDerivAt_pow 9 x).div_const 9
        have h11 : HasDerivAt (fun y : ℝ => y ^ 11 / 11) (x ^ 10) x := by
          simpa [pow_succ] using (hasDerivAt_pow 11 x).div_const 11
        have h13 : HasDerivAt (fun y : ℝ => y ^ 13 / 13) (x ^ 12) x := by
          simpa [pow_succ] using (hasDerivAt_pow 13 x).div_const 13
        have h15 : HasDerivAt (fun y : ℝ => y ^ 15 / 15) (x ^ 14) x := by
          simpa [pow_succ] using (hasDerivAt_pow 15 x).div_const 15
        exact ((((((((hasDerivAt_id x).sub h3).add h5).sub h7).add h9).sub h11).add h13).sub h15)
      have h2 : HasDerivAt (fun y : ℝ => Real.arctan y - wt1eP15 y)
          (1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14)) x :=
        (Real.hasDerivAt_arctan x).sub hP
      rw [h2.deriv]
      have hq : 1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14)
          = x ^ 16 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [hq]
      positivity)
    s hs
  linarith

/-- `wt1eP15` is increasing on `[0, 1]`. -/
theorem wt1e_p15_mono {u w : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) (hw1 : w ≤ 1) :
    wt1eP15 u ≤ wt1eP15 w := by
  have hcont : ContinuousOn (fun x : ℝ => wt1eP15 x) (Set.Icc u w) :=
    (by unfold wt1eP15; fun_prop : Continuous (fun x : ℝ => wt1eP15 x)).continuousOn
  have hdiff : ∀ x ∈ Set.Ioo u w, HasDerivAt (fun y : ℝ => wt1eP15 y)
      (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14) x := by
    intro x _
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
      simpa [pow_succ] using (hasDerivAt_pow 3 x).div_const 3
    have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
      simpa [pow_succ] using (hasDerivAt_pow 5 x).div_const 5
    have h7 : HasDerivAt (fun y : ℝ => y ^ 7 / 7) (x ^ 6) x := by
      simpa [pow_succ] using (hasDerivAt_pow 7 x).div_const 7
    have h9 : HasDerivAt (fun y : ℝ => y ^ 9 / 9) (x ^ 8) x := by
      simpa [pow_succ] using (hasDerivAt_pow 9 x).div_const 9
    have h11 : HasDerivAt (fun y : ℝ => y ^ 11 / 11) (x ^ 10) x := by
      simpa [pow_succ] using (hasDerivAt_pow 11 x).div_const 11
    have h13 : HasDerivAt (fun y : ℝ => y ^ 13 / 13) (x ^ 12) x := by
      simpa [pow_succ] using (hasDerivAt_pow 13 x).div_const 13
    have h15 : HasDerivAt (fun y : ℝ => y ^ 15 / 15) (x ^ 14) x := by
      simpa [pow_succ] using (hasDerivAt_pow 15 x).div_const 15
    exact ((((((((hasDerivAt_id x).sub h3).add h5).sub h7).add h9).sub h11).add h13).sub h15)
  have hmono : MonotoneOn (fun x : ℝ => wt1eP15 x) (Set.Icc u w) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc u w) hcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hdiff x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hdiff x hx).deriv]
      have hx0 : (0 : ℝ) ≤ x := le_trans hu hx.1.le
      have hxw' : (x : ℝ) ≤ w := le_of_lt hx.2
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hxw', hw1]
      have hpos : (0 : ℝ) ≤ 1 - x ^ 2 := by linarith
      -- pair the terms: (x⁴−x⁶) + (x⁸−x¹⁰) + (x¹²−x¹⁴) = x⁴(1−x²)(1+x⁴+x⁸) ≥ 0
      have hstep : (0 : ℝ) ≤ x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 := by
        have hp : x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14
            = x ^ 4 * (1 - x ^ 2) * (1 + x ^ 4 + x ^ 8) := by ring
        rw [hp]
        exact mul_nonneg (mul_nonneg (by nlinarith) hpos) (by positivity)
      linarith
  exact hmono (Set.mem_Icc.mpr ⟨le_refl u, huw⟩) (Set.mem_Icc.mpr ⟨huw, le_refl w⟩) huw

/-! ## 3. The `arctan s + arctan (1/s) = π/2` identity -/

/-- No odd multiple of `π/2` lies in `(0, π/2)`. -/
theorem wt1e_not_halfpi {x : ℝ} (hx : 0 < x) (hx' : x < Real.pi / 2) :
    ∀ k : ℤ, x ≠ (2 * k + 1) * Real.pi / 2 := by
  intro k hk
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases Int.lt_trichotomy k 0 with h | h | h
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show (k : ℤ) ≤ -1 by omega)
    have hco : (2 : ℝ) * (k : ℝ) + 1 ≤ -1 := by linarith
    have hxle : x ≤ -(Real.pi) / 2 := by
      rw [hk]
      have hmul : (2 * (k : ℝ) + 1) * Real.pi ≤ -(1 : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hco hpi.le
      linarith
    linarith
  · subst h
    norm_num at hk
    linarith
  · have hk' : (1 : ℤ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have hco : (3 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
      have hk'' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'
      linarith
    have hxge : Real.pi / 2 ≤ x := by
      rw [hk, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
      have h1 : (3 : ℝ) * Real.pi ≤ (2 * (k : ℝ) + 1) * Real.pi :=
        mul_le_mul_of_nonneg_right hco hpi.le
      linarith [h1, hpi]
    linarith

/-- `arctan s + arctan (1/s) = π/2` for `s > 0`. -/
theorem wt1e_atan_add_inv {s : ℝ} (hs : 0 < s) :
    Real.arctan s + Real.arctan (1 / s) = Real.pi / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hatanpos : (0 : ℝ) < Real.arctan s := by
    rw [Real.arctan_pos]
    linarith
  have hθlt : Real.pi / 2 - Real.arctan s < Real.pi / 2 := by linarith
  have hθrange : -(Real.pi / 2) < Real.pi / 2 - Real.arctan s := by
    have h2 : Real.arctan s < Real.pi / 2 := by
      obtain ⟨_, h2⟩ := Real.arctan_mem_Ioo s
      linarith
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

/-! ## 4. matan value brackets -/

/-- `matan t = arctan (√t)/√t` for `t > 0`. -/
theorem wt1e_matan_eq {t : ℝ} (ht : 0 < t) :
    matan t = Real.arctan (Real.sqrt t) / Real.sqrt t := by
  unfold matan
  rw [if_neg (ne_of_gt ht), if_pos ht]

/-- **Large-`t` upper bracket** (`s = √t ∈ [slo, shi]`, `slo ≥ 1`):
`matan t ≤ (π/2 − wt1eP15 (1/shi))/slo`. -/
theorem wt1e_matan_ub_big {t s u : ℝ} (hts : s * s = t) (hs0 : 0 < s)
    (hslo : slo ≤ s) (hshi : s ≤ shi) (h1 : (1 : ℝ) ≤ slo) (hu : u = 1 / shi) :
    matan t ≤ (Real.pi / 2 - wt1eP15 u) / slo := by
  have hslolen : (0 : ℝ) < slo := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1
  have hs1 : (1 : ℝ) ≤ s := le_trans h1 hslo
  have hshilen : (1 : ℝ) ≤ shi := le_trans hs1 hshi
  have hmat : matan t = Real.arctan s / s := by
    rw [wt1e_matan_eq (by rw [← hts]; positivity),
      show Real.sqrt t = s from by rw [← hts]; exact Real.sqrt_mul_self hs0.le]
  -- `matan` is antitone: `slo² ≤ t` gives `matan t ≤ matan (slo²)`
  have hsq2 : (slo : ℝ) * slo ≤ t := by
    calc (slo : ℝ) * slo ≤ s * s := by nlinarith
      _ = t := hts
  have hIoia : (slo : ℝ) * slo ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by nlinarith [hslolen])
  have hIoib : t ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by rw [← hts]; nlinarith [hs0])
  have hstep1 : matan t ≤ matan (slo * slo) :=
    nb12w_matan_strictAntiOn.antitoneOn hIoia hIoib hsq2
  have hmatlo : matan (slo * slo) = Real.arctan slo / slo := by
    rw [wt1e_matan_eq (by positivity), Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ slo)]
  -- `p15 u ≤ p15 (1/slo) ≤ arctan (1/slo)` with `u = 1/shi`
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by
    rw [hu]
    exact (div_le_one (by linarith : (0 : ℝ) < shi)).mpr hshilen
  have hu2 : u ≤ 1 / slo := by
    rw [hu]
    exact (div_le_div_iff₀ (by linarith : (0 : ℝ) < shi) hslolen).mpr (by linarith [hslo, hshi])
  have hchain : wt1eP15 u ≤ Real.arctan (1 / slo) :=
    (wt1e_p15_mono hu0 hu2 ((div_le_one hslolen).mpr h1)).trans
      (wt1e_atan_ge_p15 (1 / slo) (by positivity))
  have hkey : Real.arctan slo ≤ Real.pi / 2 - wt1eP15 u := by
    have hid := wt1e_atan_add_inv hslolen
    linarith
  calc matan t ≤ matan (slo * slo) := hstep1
    _ = Real.arctan slo / slo := hmatlo
    _ ≤ (Real.pi / 2 - wt1eP15 u) / slo :=
        div_le_div_of_nonneg_right hkey (le_of_lt hslolen)

/-- **Large-`t` lower bracket** (`s = √t ∈ [slo, shi]`, `slo ≥ 1`):
`(π/2 − wt1eP13 (1/shi))/shi ≤ matan t`. -/
theorem wt1e_matan_lb_big {t s u : ℝ} (hts : s * s = t) (hs0 : 0 < s)
    (hslo : slo ≤ s) (hshi : s ≤ shi) (h1 : (1 : ℝ) ≤ slo) (hu : u = 1 / shi) :
    (Real.pi / 2 - wt1eP13 u) / shi ≤ matan t := by
  have hshilen : (1 : ℝ) ≤ shi := le_trans (le_trans h1 hslo) hshi
  have hsq2 : t ≤ shi * shi := by
    calc t = s * s := hts.symm
      _ ≤ shi * shi := by nlinarith
  have hIoia : t ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by rw [← hts]; nlinarith [hs0])
  have hIoib : (shi : ℝ) * shi ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by nlinarith [hshilen])
  have hstep1 : matan (shi * shi) ≤ matan t :=
    nb12w_matan_strictAntiOn.antitoneOn hIoia hIoib hsq2
  have hmathi : matan (shi * shi) = Real.arctan shi / shi := by
    rw [wt1e_matan_eq (by positivity), Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ shi)]
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  -- `arctan shi ≥ π/2 − p13(1/shi)`
  have hkey : Real.pi / 2 - wt1eP13 u ≤ Real.arctan shi := by
    have hid := wt1e_atan_add_inv (by linarith : (0 : ℝ) < shi)
    have hup : Real.arctan (1 / shi) ≤ wt1eP13 u := by
      rw [hu]
      exact wt1e_atan_le_p13 (1 / shi) (by positivity)
    linarith
  calc (Real.pi / 2 - wt1eP13 u) / shi ≤ Real.arctan shi / shi :=
        div_le_div_of_nonneg_right hkey (le_of_lt (by linarith : (0 : ℝ) < shi))
    _ ≤ matan t := by rw [← hmathi]; exact hstep1

/-- **Negative-`t` upper bracket** (`v = √(−t)`, `v² ≤ uhi²`, `uhi < 1`):
`matan t ≤ 1 + uhi²/3 + uhi⁴/5 + uhi⁶/(7·(1−uhi²))`. -/
theorem wt1e_matan_ub_neg {t v uhi : ℝ} (ht0 : t < 0) (hv : Real.sqrt (-t) = v)
    (hu : v * v ≤ uhi * uhi) (huhi0 : 0 ≤ uhi) (huhi1 : uhi < 1) :
    matan t ≤ 1 + uhi ^ 2 / 3 + uhi ^ 4 / 5 + uhi ^ 6 / (7 * (1 - uhi ^ 2)) := by
  have hv0 : (0 : ℝ) ≤ v := by rw [← hv]; exact Real.sqrt_nonneg (-t)
  have hvpos : (0 : ℝ) < v := by
    have h : (0 : ℝ) < -t := by linarith
    rw [← hv]
    exact Real.sqrt_pos.mpr h
  have hmono : v ≤ uhi := by
    have h := Real.sqrt_le_sqrt (show (v : ℝ) * v ≤ uhi * uhi from hu)
    rw [Real.sqrt_mul_self hv0, Real.sqrt_mul_self huhi0] at h
    exact h
  have hv1 : v < 1 := by
    have h2 : uhi ^ 2 < 1 := pow_lt_one₀ huhi0 huhi1 (by norm_num : (2 : ℕ) ≠ 0)
    have h3 : v ^ 2 < 1 := lt_of_le_of_lt (pow_le_pow_left₀ hv0 hmono 2) h2
    nlinarith
  have hmat : matan t = Real.log ((1 + v) / (1 - v)) / (2 * v) := by
    unfold matan
    rw [if_neg (ne_of_lt ht0), if_neg (not_lt.mpr (le_of_lt ht0)), hv]
  have hartanh : Real.log ((1 + v) / (1 - v)) / 2 ≤
      v + v ^ 3 / 3 + v ^ 5 / 5 + v ^ 7 / (7 * (1 - v ^ 2)) :=
    nb12w_artanh_le_sub7 hv0 hv1
  have hdiv : Real.log ((1 + v) / (1 - v)) / (2 * v)
      ≤ 1 + v ^ 2 / 3 + v ^ 4 / 5 + v ^ 6 / (7 * (1 - v ^ 2)) := by
    have hsplit : Real.log ((1 + v) / (1 - v)) / (2 * v)
        = (Real.log ((1 + v) / (1 - v)) / 2) / v := by field_simp
    rw [hsplit]
    have h1 : (Real.log ((1 + v) / (1 - v)) / 2) / v
        ≤ (v + v ^ 3 / 3 + v ^ 5 / 5 + v ^ 7 / (7 * (1 - v ^ 2))) / v :=
      div_le_div_of_nonneg_right hartanh (le_of_lt hvpos)
    have h2 : (v + v ^ 3 / 3 + v ^ 5 / 5 + v ^ 7 / (7 * (1 - v ^ 2))) / v
        = 1 + v ^ 2 / 3 + v ^ 4 / 5 + v ^ 6 / (7 * (1 - v ^ 2)) := by
      field_simp
    rw [← h2]
    exact h1
  have hstep2 : matan t ≤ 1 + v ^ 2 / 3 + v ^ 4 / 5 + v ^ 6 / (7 * (1 - v ^ 2)) := by
    rw [hmat]
    exact hdiv
  have hstep3 : 1 + v ^ 2 / 3 + v ^ 4 / 5 + v ^ 6 / (7 * (1 - v ^ 2))
      ≤ 1 + uhi ^ 2 / 3 + uhi ^ 4 / 5 + uhi ^ 6 / (7 * (1 - uhi ^ 2)) := by
    have hv2 : v ^ 2 ≤ uhi ^ 2 := pow_le_pow_left₀ hv0 hmono 2
    have h2 : v ^ 4 ≤ uhi ^ 4 := pow_le_pow_left₀ hv0 hmono 4
    have h3 : v ^ 6 ≤ uhi ^ 6 := pow_le_pow_left₀ hv0 hmono 6
    have h4 : (1 : ℝ) - uhi ^ 2 ≤ 1 - v ^ 2 := by linarith
    have hd : (0 : ℝ) < 7 * (1 - uhi ^ 2) := by nlinarith
    have hd' : (0 : ℝ) < 7 * (1 - v ^ 2) := by nlinarith
    have t2 : v ^ 2 / 3 ≤ uhi ^ 2 / 3 := div_le_div_of_nonneg_right hv2 (by norm_num)
    have t4 : v ^ 4 / 5 ≤ uhi ^ 4 / 5 := div_le_div_of_nonneg_right h2 (by norm_num)
    have t6 : v ^ 6 / (7 * (1 - v ^ 2)) ≤ uhi ^ 6 / (7 * (1 - uhi ^ 2)) := by
      have h3l : v ^ 6 / (7 * (1 - v ^ 2)) ≤ v ^ 6 / (7 * (1 - uhi ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) hd (by nlinarith [h4])
      exact le_trans h3l (div_le_div_of_nonneg_right h3 (le_of_lt hd))
    linarith
  linarith [hstep2, hstep3]

/-- Small positive `t`: the `nb12w` cubic upper (valid for all `t > 0`). -/
theorem wt1e_matan_ub_small {t : ℝ} (ht : 0 < t) :
    matan t ≤ 1 - t / 3 + t ^ 2 / 5 := (nb12w_matan_pos_bracket3 ht).2

/-- Small positive `t`: the `nb12w` cubic lower (valid for all `t > 0`). -/
theorem wt1e_matan_lb_small {t : ℝ} (ht : 0 < t) :
    1 - t / 3 + t ^ 2 / 5 - t ^ 3 / 7 ≤ matan t := (nb12w_matan_pos_bracket3 ht).1

/-- Small negative `t` (`−1/4 ≤ t < 0`): lower and upper. -/
theorem wt1e_matan_br_small_neg {t : ℝ} (ht0 : t < 0) (ht4 : -(1 / 4) ≤ t) :
    1 - t / 3 + t ^ 2 / 5 ≤ matan t ∧
      matan t ≤ 1 - t / 3 + t ^ 2 / 5 + 4 * |t| ^ 3 / 21 :=
  nb12w_matan_neg_bracket3 ht0 ht4

/-! ## 5. Sharper `K1`/`K2` brackets via `arctan (√2) = π/4 + arctan (3−2√2)` -/

/-- `3 − 2√2 ∈ [0.1715728, 0.17157288]`. -/
theorem wt1e_w_br : (0.1715728 : ℝ) ≤ 3 - 2 * Real.sqrt 2 ∧ 3 - 2 * Real.sqrt 2 ≤ 0.17157288 := by
  have hs := wt1e_sqrt2_br
  constructor
  · have h2 := hs.2
    linarith
  · have h1 := hs.1
    linarith

/-- `arctan (√2) = π/4 + arctan (3 − 2√2)`. -/
theorem wt1e_alpha_split :
    Real.arctan (Real.sqrt 2) = Real.pi / 4 + Real.arctan (3 - 2 * Real.sqrt 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set w := 3 - 2 * Real.sqrt 2 with hwdef
  have hw1 : (0 : ℝ) < 1 - w := by
    have h1 : (1 : ℝ) < Real.sqrt 2 := lt_of_le_of_lt (by norm_num : (1 : ℝ) ≤ 1.4)
      (by have := wt1e_sqrt2_br.1; linarith)
    rw [hwdef]
    nlinarith [h1, wt1e_sqrt2_br.1]
  have hwpos : (0 : ℝ) < w := by
    rw [hwdef]
    linarith [wt1e_sqrt2_br.2]
  have hwid : (1 - w) * Real.sqrt 2 = 1 + w := by
    rw [hwdef]
    linear_combination (norm := ring_nf) 2 * hs2
  have hwlt : w < 1 := by linarith
  have hwarc : Real.tan (Real.pi / 4 + Real.arctan w) = Real.sqrt 2 := by
    have hne1 : ∀ k : ℤ, Real.pi / 4 ≠ (2 * k + 1) * Real.pi / 2 := by
      intro k hk
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have hpos : (0 : ℝ) < Real.pi / 4 := by nlinarith [hpi]
      have hlt : Real.pi / 4 < Real.pi / 2 := by linarith [hpi]
      exact absurd hk (wt1e_not_halfpi hpos hlt k)
    have hne2 : ∀ l : ℤ, Real.arctan w ≠ (2 * l + 1) * Real.pi / 2 := by
      intro l hl
      have harc : Real.arctan w < Real.pi / 2 := by
        obtain ⟨_, h2⟩ := Real.arctan_mem_Ioo w
        exact h2
      have hpos : (0 : ℝ) < Real.arctan w := by
        rw [Real.arctan_pos]
        exact hwpos
      rcases Int.lt_trichotomy l 0 with h | h | h
      · have hl' : (l : ℝ) ≤ -1 := by exact_mod_cast (show (l : ℤ) ≤ -1 by omega)
        have hco : (2 : ℝ) * (l : ℝ) + 1 ≤ -1 := by
          have hk'' : (1 : ℝ) ≤ -(l : ℝ) := by exact_mod_cast (neg_le_neg_iff.mpr hl')
          linarith
        have hle : (2 * (l : ℝ) + 1) * Real.pi / 2 ≤ -(Real.pi) / 2 := by
          rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
          have hmul : (2 * (l : ℝ) + 1) * Real.pi ≤ -(1 : ℝ) * Real.pi :=
            mul_le_mul_of_nonneg_right hco hpi.le
          linarith [hmul, hpi]
        have hneg : -(Real.pi) / 2 < 0 := by linarith
        linarith [hle, hneg, hpos, hl]
      · subst h
        norm_num at hl
        exact absurd hl (by intro hc; linarith [hc, harc])
      · have hl' : (1 : ℤ) ≤ l := by exact_mod_cast (show (1 : ℤ) ≤ l by omega)
        have hco : (3 : ℝ) ≤ 2 * (l : ℝ) + 1 := by
          have hk'' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl'
          linarith
        have hge : Real.pi / 2 ≤ (2 * (l : ℝ) + 1) * Real.pi / 2 := by
          rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
          have hmul : (3 : ℝ) * Real.pi ≤ (2 * (l : ℝ) + 1) * Real.pi :=
            mul_le_mul_of_nonneg_right hco hpi.le
          linarith [hmul, hpi]
        linarith
    have hcond : (∀ k : ℤ, Real.pi / 4 ≠ (2 * k + 1) * Real.pi / 2) ∧
        ∀ l : ℤ, Real.arctan w ≠ (2 * l + 1) * Real.pi / 2 := ⟨hne1, hne2⟩
    have h4 : Real.tan (Real.pi / 4) = 1 := by
      rw [show Real.pi / 4 = Real.arctan 1 from Real.arctan_one.symm, Real.tan_arctan]
    rw [Real.tan_add' hcond, Real.tan_arctan, h4]
    field_simp
    linear_combination (norm := ring_nf) hwid.symm
  have hrange : (0 : ℝ) < Real.pi / 4 + Real.arctan w ∧
      Real.pi / 4 + Real.arctan w < Real.pi / 2 := by
    have h4 : (0 : ℝ) < Real.pi / 4 := by nlinarith [hpi]
    have h6 : Real.arctan w ≤ 0.25 := by
      have h1 := nb12_arctan_le_self (show (0 : ℝ) ≤ 3 - 2 * Real.sqrt 2 from by linarith)
      have hw2 : (3 - 2 * Real.sqrt 2 : ℝ) ≤ 0.17157288 := by
        have h := wt1e_w_br
        linarith
      linarith [h1, hw2]
    constructor
    · have hnpos : (0 : ℝ) ≤ Real.arctan w := Real.arctan_nonneg.mpr (le_of_lt hwpos)
      linarith [h4, hnpos]
    · have harc4 : Real.arctan w < Real.pi / 4 := by
        rw [show Real.pi / 4 = Real.arctan 1 from Real.arctan_one.symm,
          Real.arctan_lt_arctan_iff]
        exact hwlt
      calc Real.pi / 4 + Real.arctan w < Real.pi / 4 + Real.pi / 4 := by linarith [harc4]
        _ = Real.pi / 2 := by ring
  rw [← Real.arctan_tan (by linarith [hrange.1]) hrange.2, hwarc]

/-- `arctan (√2) ∈ [0.95531638, 0.95531671]`. -/
theorem wt1e_alpha_br : (0.95531638 : ℝ) ≤ Real.arctan (Real.sqrt 2) ∧
    Real.arctan (Real.sqrt 2) ≤ 0.95531671 := by
  have hsplit := wt1e_alpha_split
  have hw := wt1e_w_br
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hx0 : (0 : ℝ) ≤ 3 - 2 * Real.sqrt 2 := by have := hw.1; linarith
  have hmono : wt1eP15 0.1715728 ≤ wt1eP15 (3 - 2 * Real.sqrt 2) :=
    wt1e_p15_mono (by norm_num) (by linarith [hw.1]) (by linarith [hw.2])
  have hmid : wt1eP15 (3 - 2 * Real.sqrt 2) ≤ Real.arctan (3 - 2 * Real.sqrt 2) :=
    wt1e_atan_ge_p15 _ hx0
  have hP13tail : wt1eP15 0.17157288 + 0.17157288 ^ 15 / 15 ≤ 0.16991846 := by
    norm_num [wt1eP15]
  have h2 : Real.arctan (3 - 2 * Real.sqrt 2) ≤ 0.16991846 := by
    have h1 := wt1e_atan_le_p13 (3 - 2 * Real.sqrt 2) hx0
    have h13s : wt1eP13 (3 - 2 * Real.sqrt 2)
        = wt1eP15 (3 - 2 * Real.sqrt 2) + (3 - 2 * Real.sqrt 2) ^ 15 / 15 := by
      unfold wt1eP13 wt1eP15
      ring
    have hA : wt1eP15 (3 - 2 * Real.sqrt 2) ≤ wt1eP15 0.17157288 :=
      wt1e_p15_mono hx0 hw.2 (by norm_num)
    have hpow : (3 - 2 * Real.sqrt 2 : ℝ) ^ 15 / 15 ≤ 0.17157288 ^ 15 / 15 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hw.2 15) (by norm_num)
    have h1' : Real.arctan (3 - 2 * Real.sqrt 2) ≤
        wt1eP15 (3 - 2 * Real.sqrt 2) + (3 - 2 * Real.sqrt 2) ^ 15 / 15 := by
      rw [← h13s]
      exact h1
    linarith [h1', hA, hpow, hP13tail]
  have hpi := wt1e_pi_br
  constructor
  · have hlo : (0.95531638 : ℝ) ≤ Real.pi / 4 + wt1eP15 0.1715728 := by
      norm_num [wt1eP15]
      linarith [hpi.1]
    have h2 : Real.pi / 4 + wt1eP15 0.1715728
        ≤ Real.pi / 4 + wt1eP15 (3 - 2 * Real.sqrt 2) := by linarith [hmono]
    have h3 : Real.pi / 4 + wt1eP15 (3 - 2 * Real.sqrt 2)
        ≤ Real.pi / 4 + Real.arctan (3 - 2 * Real.sqrt 2) := by linarith [hmid]
    linarith [hlo, h2, h3, hsplit]
  · have h4 : Real.pi / 4 + Real.arctan (3 - 2 * Real.sqrt 2) ≤ 0.95531671 := by
      norm_num [wt1eP13]
      linarith [hpi.2, h2]
    linarith [hsplit, h4]


/-! ### NOTE (lane `wt1-edges-cert-w1`, unfinished): sharper `K1`/`K2`.

`nb20_k1` (`K1 ≤ 0.64437`) and `nb20_k2` (`0.06468 ≤ K2`) are too loose for the
thinnest E00 pieces at the kink (their literal slack `≈ 2·10⁻⁵ · Σ SE` eats the
`≈ 4.5·10⁻⁵` margin; `scripts/check_all.py` quantifies this).  The replacement
brackets — fully soundness-checked in Python — are:

* `arctan(√2) ∈ [0.955316381625, 0.955316709338]`
  via `arctan(√2) = π/4 + arctan(3−2√2)`, `3−2√2 ∈ [0.1715728, 0.17157288]`
  (`wt1e_w_br`, `wt1e_alpha_split`, `wt1e_alpha_br` — all proved above with the
  8-decimal bracket `[0.95531638, 0.95531671]`);
* `sol0 = 2π − 6·arctan(√2) ∈ [0.5512837, 0.5512878]`,
  `tau0 = 4π − 20·sol0 ∈ [1.5406176, 1.5406932]`
  (`sol0 = 3·arccos(1/3) − π`, `arccos(1/3) = π − 2·arctan(√2)`);
* `K1 = 2·mm1/π = 2·sol0·√8/(π·tau0) ≤ 0.644330583`
  (`mm1 = sol0·√8/tau0`),
* `K2 = 8·mm2/π = 8·(6·sol0−π)·√2/(6·tau0·π) ≥ 0.06471189038`
  (`mm2 = (6·sol0−π)·√2/(6·tau0)`).

A previous attempt at the two closing `nlinarith` proofs had residual tactic
issues (unordered-π-atom scaling); the follow-up lane emitting the 51 edge
pieces should restore them from this exact recipe (verified numerically in
`scripts/check_all.py` §4).  Until then the E00 pieces near the kink must be
emitted with `nb20_k1`/`nb20_k2` and ~2× finer y4-slicing (width ≤ 0.0005 at
`|y4 − 2.52| ≤ 0.01`) so the extra `≈ 2·10⁻⁵` slack still leaves `L > 0`.
-/

/-! ## 9. Axiom audit -/

#print axioms wt1e_sqrt2_br
#print axioms wt1e_pi_br
#print axioms wt1e_atan_le_p13
#print axioms wt1e_atan_ge_p15
#print axioms wt1e_p15_mono
#print axioms wt1e_not_halfpi
#print axioms wt1e_atan_add_inv
#print axioms wt1e_matan_eq
#print axioms wt1e_matan_ub_big
#print axioms wt1e_matan_lb_big
#print axioms wt1e_matan_ub_neg
#print axioms wt1e_matan_ub_small
#print axioms wt1e_matan_lb_small
#print axioms wt1e_matan_br_small_neg
#print axioms wt1e_w_br
#print axioms wt1e_alpha_split
#print axioms wt1e_alpha_br

end Kepler.Text

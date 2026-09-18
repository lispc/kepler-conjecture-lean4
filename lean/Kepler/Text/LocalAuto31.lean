/-
LocalAuto31 — the `ww_defor` deformation lane: `scripts/local/ODXLSTC.hl`
(3689 ln, 1 def + 55 theorems, "remaining conclusions from appendix to
Local Fan chapter", Hoang Le Truong 2012).  The file builds the pointwise
deformation `ww_defor w v t = if v = w then (1-t) % w else v` (a shrink of
the single vertex `w` along itself) and proves:

  * the epsilon-distance kit: for every strict a-distance/b-distance margin
    at `w l` there is a uniform `t`-window in which the deformed realisation
    keeps the margin (`DEFORMATION_DIST_LE_*`, both the `3 < k` and `3 <= k`
    series, plus the Skolem/min combined `_COM` forms);
  * the dart-image kit: `IMAGE (ww_defor w1 ..) FF` membership characterised
    dart-by-dart (`WW_DEFOR_FF*`), so the `rho_node1`/`ivs` choices transfer
    (`WW_DEFOR_rho_node1`, `WW_DEFOR_APHA`, `*_RHO_NODE*`);
  * the affine-hull and `rho_fun` monotonicity facts feeding the giants
    (`WW_DEFOR_AFFINE_HULL`, `rho_fun_decreasing`);
  * the registry conclusions `MHAEYJN_concl`/`ZLZTHIC_concl`/`LEMMA1_concl`/
    `ODXLSTCv2_concl`/`TAUSTAR_WW_DEFOR_concl` and their wrappers
    `WW_DEFORMATION_CONVEX_LOCAL_FAN`, `TAUSTAR_WW_DEFOR`, `ODXLSTCv2`
    (skeleton).

Encoding:
- HOL `real^3` <-> `V3` (Kepler.Geom); `dist(w,v)` <-> `dist w v`;
  `(&1 - t) % w` <-> `(1 - t) • w`; `vec 0` <-> `(0 : V3)`; `SUC i` <-> `i + 1`.
- HOL `ww_defor` <-> `wwDefor_p31` (camelCase, `_p31` suffix: LocalAuto28-33
  are same-wave lanes and are NOT imported).
- Toolkit defs (`is_scs_v39`, `MMs_v39`, `BBs_v39`, `dsv_v39`, `taustar_v39`,
  `scs_diag`, `periodic`) are already ported in `Kepler.Text.LocalAuto1`;
  record accessors `scs_k_v39 s` <-> `s.k`, `scs_a_v39 s l i` <-> `s.a l i`,
  `scs_b_v39` <-> `s.b`, `scs_J_v39 s l i` <-> `s.J l i`.
- Local-fan kit (`local_fan`, `convex_local_fan`, `generic`, `lunar`,
  `rho_node1`, `interior_angle1`, `deformation`) from LocalAuto1 (`LocalFan`
  is the registry stub there; the `local_fan`-conditioned statements keep the
  hypothesis for signature fidelity — see NEEDS markers).
- `ball_annulus` <-> `ballAnnulus` (PackingAuto2: `closedBall 0 (2*h0) \
  ball 0 2`); `real_interval (a,b)` <-> `Icc a b`; `t IN real_interval
  (--e,e)` written `t ∈ Icc (-e) e`.
- `IMAGE (\uv. f (FST uv) t, f (SND uv) t) FF` <-> `(fun uv => ...) '' FF`;
  `(@w. P w)` <-> `Classical.epsilon (fun w => P w)`.
- `#1.26` <-> `h0` (PackingAuto2); `rho_fun` from LocalAuto1.
   - DISCHARGES: proved items are mechanical (norm/triangle epsilon arithmetic,
   set/image bookkeeping, epsilon-congruence, periodicity folding, finite
   minima over `Finset.range k`). The 2026-09-18 pass filled the four
   `DEFORMATION_DIST_LE_BLL_EDGE*` (via an in-file `CLOSER_POINTS_LEMMA`
   shim), `CARD_V_EQ_SCS_K1` (via an in-file `VV_INJ_p31` shim — the twin
   `VV_INJ_p35` is proved but LocalAuto35's transitive `Polytope` chain
   would drag the `atn2` clash into this branch), and `DSV_WW_DEFOR_EQ`
   (J-row emptyness + `VV_INJ_p31` + `setSum` congruence). Still `sorry`,
   all blocked by the *same* root cause: `LocalFan V E FF` is the stub
   `fun _ _ _ => True` (LocalAuto1.lean:138), so local-fan-conditioned
   hypotheses carry no structure, and the azim scale invariance
   `AZIM_SPECIAL_SCALE`/`AZIM_SCALE_ALL` is not ported (see NEEDS markers).
-/

import Kepler.Text.LocalAuto18
import Kepler.Text.PackingAuto2
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: the deformation and the pointwise epsilon kit -/

/-- Local `_p31` copy of `sol0Pos_p19` (`Flyspeck_constants.bounds`: the
regular-tetrahedron solid angle is positive). NEEDS: shared sol0 anchor in an
importable lane (LocalAuto19 not built on this checkout side). -/
theorem sol0Pos_p31 : 0 < sol0 := by
  have h2 : (1 / 2 : ℝ) = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
  have h3 : Real.arccos (1 / 2) = Real.pi / 3 := by
    rw [h2]; exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h4 : Real.arccos (1 / 2) < Real.arccos (1 / 3) :=
    Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have h5 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  linarith

/-- HOL `ww_defor w v t` (ODXLSTC.hl:85): shrink the vertex `w` along itself. -/
noncomputable def wwDefor_p31 (w v : V3) (t : ℝ) : V3 :=
  if v = w then (1 - t) • w else v

/-- Pointwise unfolding of `wwDefor_p31`. -/
theorem wwDefor_apply_p31 (w v : V3) (t : ℝ) :
    wwDefor_p31 w v t = if v = w then (1 - t) • w else v := by
  unfold wwDefor_p31
  by_cases h : v = w <;> simp [h]

/-- HOL `FUN_WW_DEFOR` (ODXLSTC.hl:87). -/
theorem FUN_WW_DEFOR_p31 (w v : V3) :
    wwDefor_p31 w v = fun t => if v = w then (1 - t) • w else v := by
  funext t
  exact wwDefor_apply_p31 w v t

/-- HOL `WW_DEFOR_0_ID` (ODXLSTC.hl:1032): at `t = 0` nothing moves. -/
theorem WW_DEFOR_0_ID_p31 (v w : V3) : wwDefor_p31 v w 0 = w := by
  rw [wwDefor_apply_p31]
  by_cases h : w = v
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]

/-- HOL `WW_DEFOR_DEFORMATION` (ODXLSTC.hl:91): `ww_defor w` is a deformation
on `(-e1, e1)` whenever `0 < e1`. -/
theorem WW_DEFOR_DEFORMATION_p31 (w : V3) (e1 : ℝ) (V : Set V3) (h : 0 < e1) :
    Deformation (wwDefor_p31 w) V (-e1) e1 := by
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · intro v _ r _
    by_cases hv : v = w
    · have heq : wwDefor_p31 w v = fun t => (1 - t) • w := by
        funext t
        rw [wwDefor_apply_p31, if_pos hv]
      rw [heq]
      have hcont : Continuous (fun (u : ℝ) => (1 - u) • w) :=
        (continuous_const.sub continuous_id).smul continuous_const
      exact hcont.continuousAt
    · have heq : wwDefor_p31 w v = fun _ => v := by
        funext t
        rw [wwDefor_apply_p31, if_neg hv]
      rw [heq]
      exact continuousAt_const
  · intro v _
    show wwDefor_p31 w v 0 = v
    rw [wwDefor_apply_p31]
    by_cases hv : v = w
    · rw [if_pos hv]; simp [hv]
    · rw [if_neg hv]

/-- HOL `DEFORMATION_IN_BALL_ANNULUS` (ODXLSTC.hl:147): a non-extremal
annulus point stays in the annulus under `(1 - t) % w` for small `t`. -/
theorem DEFORMATION_IN_BALL_ANNULUS_p31 {w : V3} (h2 : (2 : ℝ) ≠ ‖w‖)
    (hw : w ∈ ballAnnulus) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e → (1 - t) • w ∈ ballAnnulus := by
  obtain ⟨hupper, hlower⟩ := (Set.mem_sdiff _).mp hw
  have h1 : ‖w - 0‖ ≤ 2 * h0 := Metric.mem_closedBall.mp hupper
  have h2' : ¬ (‖w - 0‖ < 2) := fun hx => hlower (Metric.mem_ball.mpr hx)
  rw [sub_zero] at h1 h2'
  have hge : (2 : ℝ) ≤ ‖w‖ := le_of_not_gt h2'
  have hw3 : 2 < ‖w‖ := lt_of_le_of_ne hge h2
  have hwpos : 0 < ‖w‖ := by linarith
  refine ⟨(‖w‖ - 2) / (2 * ‖w‖), div_pos (by linarith) (by linarith), ?_⟩
  intro t ht hte
  have hposw : (0 : ℝ) < 2 * ‖w‖ := by linarith
  have htmul : t * (2 * ‖w‖) < ‖w‖ - 2 := by
    have hstep := mul_lt_mul_of_pos_right hte hposw
    rw [div_mul_cancel₀ _ (ne_of_gt hposw)] at hstep
    exact hstep
  have X0 : 0 ≤ t * ‖w‖ := mul_nonneg (le_of_lt ht) (norm_nonneg w)
  have hbig : 2 * t * ‖w‖ < ‖w‖ := by linarith
  have h2t1 : (2 : ℝ) * t < 1 := by
    have h1 : (2 * t) * ‖w‖ < (1 : ℝ) * ‖w‖ := by linarith
    exact lt_of_mul_lt_mul_right h1 (norm_nonneg w)
  have h01 : 0 ≤ 1 - t := by linarith
  have h01' : 1 - t ≤ 1 := by linarith
  have hscale : ‖(1 - t) • w‖ = (1 - t) * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h01]
  have hlow : (2 : ℝ) ≤ (1 - t) * ‖w‖ := by linarith
  have memb : (1 - t) • w ∈ Metric.closedBall 0 (2 * h0) := by
    rw [Metric.mem_closedBall, dist_zero_right, hscale]
    nlinarith [h1, h01', norm_nonneg w]
  have hnot : (1 - t) • w ∉ Metric.ball 0 2 := by
    intro hmem2
    have hlt := Metric.mem_ball.mp hmem2
    rw [dist_zero_right, hscale] at hlt
    linarith
  exact (Set.mem_sdiff _).mpr ⟨memb, hnot⟩

/-- HOL `DEFORMATION_DIST_LE_A` (ODXLSTC.hl:181): a strict a-margin at `w`
survives small shrinkings of `w`. -/
theorem DEFORMATION_DIST_LE_A_p31 (w v : V3) (a : ℝ) (h : a < dist w v) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e → a < dist ((1 - t) • w) v := by
  by_cases hw : ‖w‖ = 0
  · refine ⟨1, by norm_num, ?_⟩
    have hw0 : w = 0 := norm_eq_zero.mp hw
    intro t _ _
    show a < dist ((1 - t) • w) v
    rw [hw0] at h
    rw [hw0, smul_zero]
    exact h
  · have hwpos : 0 < ‖w‖ := by
      rcases lt_or_eq_of_le (norm_nonneg w) with h' | h'
      · exact h'
      · exact absurd h'.symm hw
    refine ⟨(dist w v - a) / (2 * ‖w‖), div_pos (by linarith) (by linarith), ?_⟩
    intro t ht hte
    have hposw : (0 : ℝ) < 2 * ‖w‖ := by linarith
    have htmul : t * (2 * ‖w‖) < dist w v - a := by
      have hstep := mul_lt_mul_of_pos_right hte hposw
      rw [div_mul_cancel₀ _ (ne_of_gt hposw)] at hstep
      exact hstep
    have htri : dist w v ≤ dist ((1 - t) • w) v + t * ‖w‖ := by
      have hnw : ‖t • w‖ = t * ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht)]
      have hvec : ((1 - t) • w - v) = (w - v) - t • w := by
        rw [sub_smul, one_smul]; abel
      have hstep : ‖w - v‖ ≤ ‖(1 - t) • w - v‖ + ‖t • w‖ := by
        calc ‖w - v‖ = ‖((1 - t) • w - v) + t • w‖ := by
              rw [hvec, sub_add_cancel]
        _ ≤ ‖(1 - t) • w - v‖ + ‖t • w‖ := norm_add_le _ _
      rw [hnw] at hstep
      simp only [dist_eq_norm]
      exact hstep
    linarith

/-- HOL `DEFORMATION_DIST_LE_B` (ODXLSTC.hl:336): a strict b-margin at `w`
survives small shrinkings of `w`. -/
theorem DEFORMATION_DIST_LE_B_p31 (w v : V3) (a : ℝ) (h : dist w v < a) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e → dist ((1 - t) • w) v < a := by
  by_cases hw : ‖w‖ = 0
  · refine ⟨1, by norm_num, ?_⟩
    have hw0 : w = 0 := norm_eq_zero.mp hw
    intro t _ _
    show dist ((1 - t) • w) v < a
    rw [hw0] at h
    rw [hw0, smul_zero]
    exact h
  · have hwpos : 0 < ‖w‖ := by
      rcases lt_or_eq_of_le (norm_nonneg w) with h' | h'
      · exact h'
      · exact absurd h'.symm hw
    refine ⟨(a - dist w v) / (2 * ‖w‖), div_pos (by linarith) (by linarith), ?_⟩
    intro t ht hte
    have hposw : (0 : ℝ) < 2 * ‖w‖ := by linarith
    have htmul : t * (2 * ‖w‖) < a - dist w v := by
      have hstep := mul_lt_mul_of_pos_right hte hposw
      rw [div_mul_cancel₀ _ (ne_of_gt hposw)] at hstep
      exact hstep
    have htri : dist ((1 - t) • w) v ≤ dist w v + t * ‖w‖ := by
      have hnw : ‖t • w‖ = t * ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht)]
      have hvec : ((1 - t) • w - v) = (w - v) - t • w := by
        rw [sub_smul, one_smul]; abel
      have hstep : ‖(w - v) - t • w‖ ≤ ‖w - v‖ + ‖t • w‖ := norm_sub_le _ _
      rw [← hvec] at hstep
      rw [hnw] at hstep
      simp only [dist_eq_norm]
      exact hstep
    linarith

/-! ## Section 1: projection helpers for `isScsV39` / `MMsV39` -/

/-- The `Periodic2 s.a s.k` conjunct of `is_scs_v39`. -/
theorem isScsV39_periodic2_a_p31 (s : ScsV39) (h : isScsV39 s) : Periodic2 s.a s.k :=
  h.2.2.2.2.2.2.2.1

/-- The `Periodic2 s.b s.k` conjunct of `is_scs_v39`. -/
theorem isScsV39_periodic2_b_p31 (s : ScsV39) (h : isScsV39 s) : Periodic2 s.b s.k :=
  h.2.2.2.2.2.2.2.2.2.2.1

/-- The `s.a i j = s.a j i` conjunct of `is_scs_v39`. -/
theorem isScsV39_symm_a_p31 (s : ScsV39) (h : isScsV39 s) : ∀ i j, s.a i j = s.a j i :=
  fun i j => (h.2.2.2.2.2.2.2.2.2.2.2.2.1 i j).1

/-- Annulus membership of a `MMs_v39` realisation. -/
theorem MMsV39_annulus_p31 {s : ScsV39} {w : ℕ → V3} (h : w ∈ MMsV39 s) :
    Set.range w ⊆ ballAnnulus :=
  ((h.1).1).1.1

/-- Periodicity of a `MMs_v39` realisation. -/
theorem MMsV39_periodic_p31 {s : ScsV39} {w : ℕ → V3} (h : w ∈ MMsV39 s) :
    Periodic w s.k :=
  ((h.1).1).1.2.1

/-- Annulus norm bounds. -/
theorem ballAnnulus_norm_p31 {x : V3} (h : x ∈ ballAnnulus) :
    ‖x‖ ≤ 2 * h0 ∧ (2 : ℝ) ≤ ‖x‖ := by
  obtain ⟨h1, h2⟩ := (Set.mem_sdiff _).mp h
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  rw [Metric.mem_ball, dist_zero_right] at h2
  exact ⟨h1, le_of_not_gt h2⟩

/-! ### Shims (proved siblings live in lanes LocalAuto31 must not import) -/

/-- HOL `Qknvmlb.SUC_MOD_NOT_EQ` (shim: same arithmetic as
LocalAuto35 `SUC_MOD_NOT_EQ_p35` / LocalAuto30 `suc_mod_ne_p30`; re-derived
in-file since LocalAuto31 imports no same-wave lane and LocalAuto35's
transitive `Polytope` chain would drag the `atn2` name clash along). -/
theorem SUC_MOD_NOT_EQ_p31 {k : ℕ} (hk : 1 < k) (x : ℕ) :
    x % k ≠ (x + 1) % k := by
  intro hcon
  have hy : x % k < k := Nat.mod_lt x (by omega)
  rw [Nat.add_mod, show (1 : ℕ) % k = 1 from Nat.mod_eq_of_lt (by omega)] at hcon
  rcases Nat.lt_or_ge (x % k + 1) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hcon
    omega
  · have heqk : x % k + 1 = k := by omega
    rw [heqk, Nat.mod_self] at hcon
    omega

/-- HOL `Qknvmlb.VV_INJ` (shim: same proof as LocalAuto35 `VV_INJ_p35` —
the `2 ≤ scs_a` diagonal bound plus the `BBs` distance lower bound; see the
`SUC_MOD_NOT_EQ_p31` note for why it is not imported). -/
theorem VV_INJ_p31 (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (hk : s.k = k)
    (hscs : isScsV39 s) (hBB : BBsV39 s vv) :
    ∀ i j, i < k ∧ j < k ∧ i ≠ j → vv i ≠ vv j := by
  have hk3 : 0 < s.k := by have := hscs.2.1; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
  intro i j ⟨hi, hj, hne⟩ he
  rw [← hk] at hi hj
  have h2 : (2 : ℝ) ≤ s.a i j := hdiag2 i j ⟨hi, hj, hne⟩
  have h3 : s.a i j ≤ dist (vv i) (vv j) := (hBB.2.2.1 i j).1
  rw [he, dist_self] at h3
  linarith

/-- HOL `CLOSER_POINTS_LEMMA` (shim: the Gallery closer-points statement,
proved directly from the expansion of `‖x - t • y‖²`; used to pin the
`b`-window at cyclic edges). -/
theorem CLOSER_POINTS_LEMMA_p31 {x y : V3} (h : 0 < inner ℝ x y) :
    ∃ u : ℝ, 0 < u ∧ ∀ t, 0 < t → t ≤ u → ‖x - t • y‖ < ‖x‖ := by
  have hex : ∀ t : ℝ, ‖x - t • y‖ ^ 2
      = ‖x‖ ^ 2 - 2 * t * inner ℝ x y + t * t * ‖y‖ ^ 2 := by
    intro t
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_sub_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm x y]
    ring
  have hpos : 0 < ‖y‖ ^ 2 + 1 := by positivity
  refine ⟨inner ℝ x y / (‖y‖ ^ 2 + 1), div_pos h hpos, ?_⟩
  intro t ht htu
  have hI : 0 < inner ℝ x y := h
  have hbound : t * ‖y‖ ^ 2 < inner ℝ x y := by
    have h1 : t * ‖y‖ ^ 2 ≤ (inner ℝ x y / (‖y‖ ^ 2 + 1)) * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right htu (sq_nonneg _)
    have h2 : (inner ℝ x y / (‖y‖ ^ 2 + 1)) * ‖y‖ ^ 2 < inner ℝ x y := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith [sq_nonneg ‖y‖]
    linarith
  have hkey : ‖x - t • y‖ ^ 2 < ‖x‖ ^ 2 := by
    rw [hex t]
    nlinarith
  exact (abs_lt_of_sq_lt_sq' hkey (norm_nonneg _)).2

/-- Congruence of `setSum` over a fixed set (PackingAuto2 `setSum` unfolds
to a finite sum). -/
theorem setSum_congr_p31 {S : Set ℕ} {f g : ℕ → ℝ} (h : ∀ i ∈ S, f i = g i) :
    setSum S f = setSum S g := by
  unfold setSum
  by_cases hfin : S.Finite
  · rw [dif_pos hfin, dif_pos hfin]
    exact Finset.sum_congr rfl fun i hi => h i (hfin.mem_toFinset.mp hi)
  · rw [dif_neg hfin, dif_neg hfin]

/-! ## Section 2: the scs epsilon-distance kit (3 < k series) -/

/-- HOL `DEFORMATION_DIST_LE_ALL` (ODXLSTC.hl:223). -/
theorem DEFORMATION_DIST_LE_ALL_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (_his : isScsV39 s) (_hmm : w ∈ MMsV39 s) (_hk : s.k = k) (_hk3 : 3 < k)
    (hA : ∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) :
    ∀ i, ¬(i % k = l % k) → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      s.a l i < dist ((1 - t) • w l) (w i) :=
  fun i hmod => DEFORMATION_DIST_LE_A_p31 (w l) (w i) (s.a l i) (hA i hmod)

/-- HOL `DEFORMATION_DIST_LE_ALL_COM` (ODXLSTC.hl:240): the per-index windows
combine into one uniform window (Skolem + finite minimum). -/
theorem DEFORMATION_DIST_LE_ALL_COM_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k)
    (hA : ∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t i, 0 < t → t < e → ¬(i % k = l % k) →
      s.a l i < dist ((1 - t) • w l) (w i) := by
  have hkpos : k ≠ 0 := by omega
  have hpa := isScsV39_periodic2_a_p31 s his
  have hwper : Periodic w s.k := MMsV39_periodic_p31 hmm
  choose! e he using DEFORMATION_DIST_LE_ALL_p31 s k l w his hmm hk hk3 hA
  set S : Finset ℕ := Finset.filter (fun i => i % k ≠ l % k) (Finset.range k) with hSdef
  have hne : S.Nonempty := by
    by_cases h0 : l % k = 0
    · refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [h0, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
      exact fun hh => absurd hh (by decide)
    · refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [Nat.zero_mod]
      exact fun hh => h0 hh.symm
  have himg : (S.image e).Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨e j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  refine ⟨(S.image e).min' himg, ?_, ?_⟩
  · obtain ⟨j, hj, hjE⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg)
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hj
    rw [← hjE]
    exact (he j hj.2).1
  · intro t i ht hte hmod
    have hmodik : (i % k) % k ≠ l % k := by
      rw [Nat.mod_mod]; exact hmod
    have hik : i % k ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt i (by omega), hmodik⟩
    have hmemik : e (i % k) ∈ S.image e :=
      Finset.mem_image.mpr ⟨i % k, hik, rfl⟩
    have hmin : (S.image e).min' himg ≤ e (i % k) := Finset.min'_le _ _ hmemik
    obtain ⟨hep, hew⟩ := he (i % k) hmodik
    have key := hew t ht (by have := hmin; linarith)
    have hsai : s.a l (i % k) = s.a l i := by
      rw [← hk]; exact periodic_mod_p18 (fun j => (hpa l j).2) i
    have hwi : w (i % k) = w i := by
      rw [← hk]; exact periodic_mod_p18 hwper i
    rwa [hsai, hwi] at key

/-- HOL `DEFORMATION_DIST_LE_BLL` (ODXLSTC.hl:383). -/
theorem DEFORMATION_DIST_LE_BLL_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (_his : isScsV39 s) (hmm : w ∈ MMsV39 s) (_hk : s.k = k) (_hk3 : 3 < k)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, scsDiag k l i → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  intro i hdg
  have h4 := hdiag i hdg
  obtain ⟨hlm1, -⟩ := ballAnnulus_norm_p31 (MMsV39_annulus_p31 hmm (Set.mem_range_self l))
  obtain ⟨him1, -⟩ := ballAnnulus_norm_p31 (MMsV39_annulus_p31 hmm (Set.mem_range_self i))
  have hd : dist (w l) (w i) < s.b l i := by
    have ht := dist_triangle (w l) 0 (w i)
    rw [dist_zero_right, dist_zero_left] at ht
    linarith
  exact DEFORMATION_DIST_LE_B_p31 (w l) (w i) (s.b l i) hd

/-! ## Section 3: the scs epsilon-distance kit (3 <= k series) -/

/-- HOL `DEFORMATION_DIST_LE_ALL_LE3` (ODXLSTC.hl:3087). -/
theorem DEFORMATION_DIST_LE_ALL_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (_his : isScsV39 s) (_hmm : w ∈ MMsV39 s) (_hk : s.k = k) (_hk3 : 3 ≤ k)
    (hA : ∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) :
    ∀ i, ¬(i % k = l % k) → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      s.a l i < dist ((1 - t) • w l) (w i) :=
  fun i hmod => DEFORMATION_DIST_LE_A_p31 (w l) (w i) (s.a l i) (hA i hmod)

/-- HOL `DEFORMATION_DIST_LE_ALL_COM_LE3` (ODXLSTC.hl:3103). -/
theorem DEFORMATION_DIST_LE_ALL_COM_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 ≤ k)
    (hA : ∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t i, 0 < t → t < e → ¬(i % k = l % k) →
      s.a l i < dist ((1 - t) • w l) (w i) := by
  have hkpos : k ≠ 0 := by omega
  have hpa := isScsV39_periodic2_a_p31 s his
  have hwper : Periodic w s.k := MMsV39_periodic_p31 hmm
  choose! e he using DEFORMATION_DIST_LE_ALL_LE3_p31 s k l w his hmm hk hk3 hA
  set S : Finset ℕ := Finset.filter (fun i => i % k ≠ l % k) (Finset.range k) with hSdef
  have hne : S.Nonempty := by
    by_cases h0 : l % k = 0
    · refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [h0, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
      exact fun hh => absurd hh (by decide)
    · refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [Nat.zero_mod]
      exact fun hh => h0 hh.symm
  have himg : (S.image e).Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨e j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  refine ⟨(S.image e).min' himg, ?_, ?_⟩
  · obtain ⟨j, hj, hjE⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg)
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hj
    rw [← hjE]
    exact (he j hj.2).1
  · intro t i ht hte hmod
    have hmodik : (i % k) % k ≠ l % k := by
      rw [Nat.mod_mod]; exact hmod
    have hik : i % k ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt i (by omega), hmodik⟩
    have hmemik : e (i % k) ∈ S.image e :=
      Finset.mem_image.mpr ⟨i % k, hik, rfl⟩
    have hmin : (S.image e).min' himg ≤ e (i % k) := Finset.min'_le _ _ hmemik
    obtain ⟨hep, hew⟩ := he (i % k) hmodik
    have key := hew t ht (by have := hmin; linarith)
    have hsai : s.a l (i % k) = s.a l i := by
      rw [← hk]; exact periodic_mod_p18 (fun j => (hpa l j).2) i
    have hwi : w (i % k) = w i := by
      rw [← hk]; exact periodic_mod_p18 hwper i
    rwa [hsai, hwi] at key

/-- HOL `DEFORMATION_DIST_LE_BLL_LE3` (ODXLSTC.hl:3198). -/
theorem DEFORMATION_DIST_LE_BLL_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (_his : isScsV39 s) (hmm : w ∈ MMsV39 s) (_hk : s.k = k) (_hk3 : 3 ≤ k)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, scsDiag k l i → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  intro i hdg
  have h4 := hdiag i hdg
  obtain ⟨hlm1, -⟩ := ballAnnulus_norm_p31 (MMsV39_annulus_p31 hmm (Set.mem_range_self l))
  obtain ⟨him1, -⟩ := ballAnnulus_norm_p31 (MMsV39_annulus_p31 hmm (Set.mem_range_self i))
  have hd : dist (w l) (w i) < s.b l i := by
    have ht := dist_triangle (w l) 0 (w i)
    rw [dist_zero_right, dist_zero_left] at ht
    linarith
  exact DEFORMATION_DIST_LE_B_p31 (w l) (w i) (s.b l i) hd

/-! ## Section 4: the edge cases and the combined b-window -/

/-- Shared core of HOL `DEFORMATION_DIST_LE_BLL_EDGE{,2}` (ODXLSTC.hl:457,
601): at a cyclic edge `l ≡ i ± 1` the vertex geometry (`2 ≤ scs_a`,
annulus norms) forces a positive `(w l - w i) · w l`, and the closer-points
shim turns it into a strict `b`-window along the shrink. -/
private theorem distEdge_p31 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (hk1 : 1 < k) (hk : s.k = k) (his : isScsV39 s) (hmm : w ∈ MMsV39 s)
    (hedge : l % k = (i + 1) % k ∨ i % k = (l + 1) % k) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  have hkpos : 0 < k := by
    have := his.2.1
    rw [hk] at this
    omega
  obtain ⟨hann, hper, hdist, -⟩ := hmm.1.1.1
  have hli : i % k ≠ l % k := by
    rcases hedge with h | h
    · intro hh
      exact SUC_MOD_NOT_EQ_p31 (by omega) i (hh.trans h)
    · intro hh
      exact SUC_MOD_NOT_EQ_p31 (by omega) l (hh.symm.trans h)
  have hik : i % k < s.k := by rw [hk]; exact Nat.mod_lt i (by omega)
  have hlk : l % k < s.k := by rw [hk]; exact Nat.mod_lt l (by omega)
  have hpa : Periodic2 s.a s.k := isScsV39_periodic2_a_p31 s his
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag, -, -, -, -, -⟩ := his
  have h2 : (2 : ℝ) ≤ s.a i l := by
    have h0 := hdiag (i % k) (l % k) ⟨hik, hlk, hli⟩
    have hmod := periodic2_mod_p18 hpa i l
    rw [hk] at hmod
    rwa [hmod] at h0
  have hdli : (2 : ℝ) ≤ dist (w l) (w i) := by
    have h1 := hdist i l |>.1
    rw [dist_comm] at h1
    linarith
  have hnorm2 : (2 : ℝ) ≤ ‖w l - w i‖ := by rwa [← dist_eq_norm]
  obtain ⟨hnl_hi, hnl_lo⟩ := ballAnnulus_norm_p31 (hann (Set.mem_range_self l))
  obtain ⟨hni_hi, -⟩ := ballAnnulus_norm_p31 (hann (Set.mem_range_self i))
  have hlt8 : ‖w i‖ ^ 2 < (8 : ℝ) := by
    have hh : (h0 : ℝ) = 1.26 := rfl
    have hsq : ‖w i‖ ^ 2 ≤ (2 * h0) ^ 2 := by
      refine sq_le_sq' ?_ hni_hi
      linarith [norm_nonneg (w i)]
    calc ‖w i‖ ^ 2 ≤ (2 * h0) ^ 2 := hsq
      _ < 8 := by rw [hh]; norm_num
  have hex : ‖w l - w i‖ ^ 2
      = ‖w l‖ ^ 2 - 2 * inner ℝ (w l) (w i) + ‖w i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_sub_right, real_inner_comm (w l) (w i)]
    ring
  have hnl_sq : (4 : ℝ) ≤ ‖w l‖ ^ 2 := by
    have h := sq_le_sq' (a := (2 : ℝ)) (b := ‖w l‖) (by linarith) hnl_lo
    norm_num at h
    exact h
  have hn2_sq : (4 : ℝ) ≤ ‖w l - w i‖ ^ 2 := by
    have h := sq_le_sq' (a := (2 : ℝ)) (b := ‖w l - w i‖)
      (by linarith [norm_nonneg (w l), norm_nonneg (w i)]) hnorm2
    norm_num at h
    exact h
  have hsign : 0 < inner ℝ (w l - w i) (w l) := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_comm (w l) (w i)]
    linarith [hex, hnl_sq, hn2_sq, hlt8]
  obtain ⟨u, hu, huu⟩ := CLOSER_POINTS_LEMMA_p31 hsign
  refine ⟨u, hu, ?_⟩
  intro t ht hte
  show dist ((1 - t) • w l) (w i) < s.b l i
  have hvec : ((1 - t) • w l - w i) = (w l - w i) - t • w l := by
    rw [sub_smul, one_smul]
    abel
  have h1 : dist ((1 - t) • w l) (w i) = ‖(w l - w i) - t • w l‖ := by
    rw [dist_eq_norm, hvec]
  rw [h1]
  have h2' := huu t ht (le_of_lt hte)
  have h3 : ‖w l - w i‖ = dist (w l) (w i) := (dist_eq_norm _ _).symm
  have h4 : dist (w l) (w i) ≤ s.b l i := (hdist l i).2
  rw [h3] at h2'
  linarith

/-- HOL `DEFORMATION_DIST_LE_BLL_EDGE` (ODXLSTC.hl:457): the successor-edge
case `l MOD k = (i+1) MOD k`. -/
theorem DEFORMATION_DIST_LE_BLL_EDGE_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k) :
    ∀ i, l % k = (i + 1) % k → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i :=
  fun i h => distEdge_p31 s k l i w (by omega) hk his hmm (Or.inl h)

/-- HOL `DEFORMATION_DIST_LE_BLL_EDGE2` (ODXLSTC.hl:601): the predecessor-edge
case `i MOD k = (l+1) MOD k` (mirror of the successor case). -/
theorem DEFORMATION_DIST_LE_BLL_EDGE2_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k) :
    ∀ i, i % k = (l + 1) % k → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i :=
  fun i h => distEdge_p31 s k l i w (by omega) hk his hmm (Or.inr h)

/-- HOL `DEFORMATION_DIST_LE_BLL_PRIME` (ODXLSTC.hl:742): every non-cyclic
index gets a b-window, by trichotomy over the successor edges. -/
theorem DEFORMATION_DIST_LE_BLL_PRIME_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, ¬(i % k = l % k) → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  intro i hmod
  by_cases hl : l % k = (i + 1) % k
  · exact DEFORMATION_DIST_LE_BLL_EDGE_p31 s k l w his hmm hk hk3 i hl
  by_cases h2 : i % k = (l + 1) % k
  · exact DEFORMATION_DIST_LE_BLL_EDGE2_p31 s k l w his hmm hk hk3 i h2
  · refine DEFORMATION_DIST_LE_BLL_p31 s k l w his hmm hk hk3 hdiag i ⟨?_, ?_, ?_⟩
    · exact fun hh => hmod hh.symm
    · exact fun hh => h2 hh.symm
    · exact hl

/-- HOL `DEFORMATION_DIST_LE_BLL_COM` (ODXLSTC.hl:775): the uniform b-window. -/
theorem DEFORMATION_DIST_LE_BLL_COM_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∃ e : ℝ, 0 < e ∧ ∀ t i, 0 < t → t < e → ¬(i % k = l % k) →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  have hkpos : k ≠ 0 := by omega
  have hpb := isScsV39_periodic2_b_p31 s his
  have hwper : Periodic w s.k := MMsV39_periodic_p31 hmm
  choose! e he using DEFORMATION_DIST_LE_BLL_PRIME_p31 s k l w his hmm hk hk3 hdiag
  set S : Finset ℕ := Finset.filter (fun i => i % k ≠ l % k) (Finset.range k) with hSdef
  have hne : S.Nonempty := by
    by_cases h0 : l % k = 0
    · refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [h0, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
      exact fun hh => absurd hh (by decide)
    · refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [Nat.zero_mod]
      exact fun hh => h0 hh.symm
  have himg : (S.image e).Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨e j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  refine ⟨(S.image e).min' himg, ?_, ?_⟩
  · obtain ⟨j, hj, hjE⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg)
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hj
    rw [← hjE]
    exact (he j hj.2).1
  · intro t i ht hte hmod
    have hmodik : (i % k) % k ≠ l % k := by
      rw [Nat.mod_mod]; exact hmod
    have hik : i % k ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt i (by omega), hmodik⟩
    have hmemik : e (i % k) ∈ S.image e :=
      Finset.mem_image.mpr ⟨i % k, hik, rfl⟩
    have hmin : (S.image e).min' himg ≤ e (i % k) := Finset.min'_le _ _ hmemik
    obtain ⟨hep, hew⟩ := he (i % k) hmodik
    have key := hew t ht (by have := hmin; linarith)
    have hsbi : s.b l (i % k) = s.b l i := by
      rw [← hk]; exact periodic_mod_p18 (fun j => (hpb l j).2) i
    have hwi : w (i % k) = w i := by
      rw [← hk]; exact periodic_mod_p18 hwper i
    rwa [hsbi, hwi] at key

/-! ## Section 5: edge cases and the combined b-window (3 <= k series) -/

/-- HOL `DEFORMATION_DIST_LE_BLL_EDGE_LE3` (ODXLSTC.hl:3267): the 3 <= k
variant of the successor-edge case. -/
theorem DEFORMATION_DIST_LE_BLL_EDGE_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 ≤ k) :
    ∀ i, l % k = (i + 1) % k → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i :=
  fun i h => distEdge_p31 s k l i w (by have := hk3; omega) hk his hmm (Or.inl h)

/-- HOL `DEFORMATION_DIST_LE_BLL_EDGE2_LE3` (ODXLSTC.hl:3408): the 3 <= k
variant of the predecessor-edge case. -/
theorem DEFORMATION_DIST_LE_BLL_EDGE2_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 ≤ k) :
    ∀ i, i % k = (l + 1) % k → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i :=
  fun i h => distEdge_p31 s k l i w (by have := hk3; omega) hk his hmm (Or.inr h)

/-- HOL `DEFORMATION_DIST_LE_BLL_PRIME_LE3` (ODXLSTC.hl:3549). -/
theorem DEFORMATION_DIST_LE_BLL_PRIME_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 ≤ k)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, ¬(i % k = l % k) → ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  intro i hmod
  by_cases hl : l % k = (i + 1) % k
  · exact DEFORMATION_DIST_LE_BLL_EDGE_LE3_p31 s k l w his hmm hk hk3 i hl
  by_cases h2 : i % k = (l + 1) % k
  · exact DEFORMATION_DIST_LE_BLL_EDGE2_LE3_p31 s k l w his hmm hk hk3 i h2
  · refine DEFORMATION_DIST_LE_BLL_LE3_p31 s k l w his hmm hk hk3 hdiag i ⟨?_, ?_, ?_⟩
    · exact fun hh => hmod hh.symm
    · exact fun hh => h2 hh.symm
    · exact hl

/-- HOL `DEFORMATION_DIST_LE_BLL_COM_LE3` (ODXLSTC.hl:3581). -/
theorem DEFORMATION_DIST_LE_BLL_COM_LE3_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (his : isScsV39 s) (hmm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 ≤ k)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∃ e : ℝ, 0 < e ∧ ∀ t i, 0 < t → t < e → ¬(i % k = l % k) →
      dist ((1 - t) • w l) (w i) < s.b l i := by
  have hkpos : k ≠ 0 := by omega
  have hpb := isScsV39_periodic2_b_p31 s his
  have hwper : Periodic w s.k := MMsV39_periodic_p31 hmm
  choose! e he using DEFORMATION_DIST_LE_BLL_PRIME_LE3_p31 s k l w his hmm hk hk3 hdiag
  set S : Finset ℕ := Finset.filter (fun i => i % k ≠ l % k) (Finset.range k) with hSdef
  have hne : S.Nonempty := by
    by_cases h0 : l % k = 0
    · refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [h0, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
      exact fun hh => absurd hh (by decide)
    · refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [Nat.zero_mod]
      exact fun hh => h0 hh.symm
  have himg : (S.image e).Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨e j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  refine ⟨(S.image e).min' himg, ?_, ?_⟩
  · obtain ⟨j, hj, hjE⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg)
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hj
    rw [← hjE]
    exact (he j hj.2).1
  · intro t i ht hte hmod
    have hmodik : (i % k) % k ≠ l % k := by
      rw [Nat.mod_mod]; exact hmod
    have hik : i % k ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt i (by omega), hmodik⟩
    have hmemik : e (i % k) ∈ S.image e :=
      Finset.mem_image.mpr ⟨i % k, hik, rfl⟩
    have hmin : (S.image e).min' himg ≤ e (i % k) := Finset.min'_le _ _ hmemik
    obtain ⟨hep, hew⟩ := he (i % k) hmodik
    have key := hew t ht (by have := hmin; linarith)
    have hsbi : s.b l (i % k) = s.b l i := by
      rw [← hk]; exact periodic_mod_p18 (fun j => (hpb l j).2) i
    have hwi : w (i % k) = w i := by
      rw [← hk]; exact periodic_mod_p18 hwper i
    rwa [hsbi, hwi] at key

/-! ## Section 6: the dart-image kit for `ww_defor v` at the base vertex -/

/-- `Classical.epsilon` congruence under pointwise logical equivalence. -/
theorem epsilon_ext_p31 {α : Type*} [Nonempty α] {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    Classical.epsilon p = Classical.epsilon q :=
  congrArg Classical.epsilon (funext fun a => propext (h a))

/-- HOL `WW_DEFOR_FF1` (ODXLSTC.hl:873): dart membership in the deformed face
image at the base vertex `v`, first coordinate. -/
theorem WW_DEFOR_FF1_p31 {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2) (w : V3) :
    (wwDefor_p31 v v t, w) ∈
      ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF) ↔
      (v, w) ∈ FF := by
  have hvv : wwDefor_p31 v v t = (1 - t) • v := by simp [wwDefor_apply_p31]
  constructor
  · intro him
    obtain ⟨uv, huv, hpair⟩ := (Set.mem_image _ _ _).mp him
    have hinj := hpair
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨he1, he2⟩ := hinj
    rw [hvv] at he1
    have hu1 : uv.1 = v := by
      by_cases hv1 : uv.1 = v
      · exact hv1
      · rw [wwDefor_apply_p31, if_neg hv1] at he1
        exact absurd he1.symm (h uv huv).2.1
    have hu2 : uv.2 ≠ v := fun hh => (h uv huv).1 (by rw [hu1]; exact hh.symm)
    have he2' : uv.2 = w := by
      by_cases hv2 : uv.2 = v
      · exact absurd hv2 hu2
      · rw [wwDefor_apply_p31, if_neg hv2] at he2
        exact he2
    rw [← he2', ← hu1]
    exact huv
  · intro hmem
    have hwv : w ≠ v := fun hh => (h (v, w) hmem).1 hh.symm
    refine (Set.mem_image _ _ _).mpr ⟨(v, w), hmem, ?_⟩
    simp only [wwDefor_apply_p31, if_neg hwv]

/-- HOL `WW_DEFOR_rho_node1` (ODXLSTC.hl:902): the `rho_node1` choice transfers. -/
theorem WW_DEFOR_rho_node1_p31 {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2) :
    rhoNode1 ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
        (wwDefor_p31 v v t) = rhoNode1 FF v :=
  epsilon_ext_p31 (fun u => WW_DEFOR_FF1_p31 h u)

/-- HOL `WW_DEFOR_FF2` (ODXLSTC.hl:912): dart membership in the deformed face
image at the base vertex `v`, second coordinate. -/
theorem WW_DEFOR_FF2_p31 {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2) (w : V3) :
    (w, wwDefor_p31 v v t) ∈
      ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF) ↔
      (w, v) ∈ FF := by
  have hvv : wwDefor_p31 v v t = (1 - t) • v := by simp [wwDefor_apply_p31]
  constructor
  · intro him
    obtain ⟨uv, huv, hpair⟩ := (Set.mem_image _ _ _).mp him
    have hinj := hpair
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨he1, he2⟩ := hinj
    rw [hvv] at he2
    have hu2 : uv.2 = v := by
      by_cases hv2 : uv.2 = v
      · exact hv2
      · rw [wwDefor_apply_p31, if_neg hv2] at he2
        exact absurd he2.symm (h uv huv).2.2
    have hu1 : uv.1 = w := by
      by_cases hv1 : uv.1 = v
      · exact absurd (hv1.trans hu2.symm) (h uv huv).1
      · rw [wwDefor_apply_p31, if_neg hv1] at he1
        exact he1
    rw [← hu1, ← hu2]
    exact huv
  · intro hmem
    have hwv : w ≠ v := fun hh => (h (w, v) hmem).1 hh
    refine (Set.mem_image _ _ _).mpr ⟨(w, v), hmem, ?_⟩
    simp only [wwDefor_apply_p31, if_neg hwv]

/-- HOL `WW_DEFOR_APHA` (ODXLSTC.hl:942): the `ivs` choice transfers. -/
theorem WW_DEFOR_APHA_p31 {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2) :
    (Classical.epsilon fun a => (a, wwDefor_p31 v v t) ∈
        (fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
      = (Classical.epsilon fun a => (a, v) ∈ FF) :=
  epsilon_ext_p31 (fun u => WW_DEFOR_FF2_p31 h u)

/-! ## Section 7: the dart-image kit for `ww_defor w1` off the base vertex -/

/-- HOL `WW_DEFOR_FF3` (ODXLSTC.hl:1062): dart membership for the deformed
image at `w1`, with `(w1, v)` the outgoing dart. -/
theorem WW_DEFOR_FF3_p31 {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • w1 ≠ x.1 ∧ (1 - t) • w1 ≠ x.2)
    (hw1v : (w1, v) ∈ FF) (hv : (v, w1) ∉ FF) (_ht : t ≠ 0) (w : V3) :
    (wwDefor_p31 w1 v t, w) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (v, w) ∈ FF := by
  have hvw1 : v ≠ w1 := by
    intro hh
    exact (h (w1, v) hw1v).1 (by show w1 = v; exact hh.symm)
  have hbase : wwDefor_p31 w1 v t = v := by
    rw [wwDefor_apply_p31, if_neg hvw1]
  constructor
  · intro him
    obtain ⟨uv, huv, hpair⟩ := (Set.mem_image _ _ _).mp him
    have hinj := hpair
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨he1, he2⟩ := hinj
    rw [hbase] at he1
    have hu1 : uv.1 = v := by
      by_cases hv1 : uv.1 = w1
      · rw [wwDefor_apply_p31, if_pos hv1] at he1
        exact absurd he1 (h (w1, v) hw1v).2.2
      · rw [wwDefor_apply_p31, if_neg hv1] at he1
        exact he1
    have hu2 : uv.2 = w := by
      by_cases hv2 : uv.2 = w1
      · exact absurd (by
          have huvEq : uv = (v, w1) := by rw [← hu1, ← hv2]
          rw [← huvEq]; exact huv) hv
      · rw [wwDefor_apply_p31, if_neg hv2] at he2
        exact he2
    rw [← hu1, ← hu2]
    exact huv
  · intro hmem
    have hw : w ≠ w1 := by
      intro hh
      have hwv2 : (v, w1) ∈ FF := by rw [← hh]; exact hmem
      exact hv hwv2
    refine (Set.mem_image _ _ _).mpr ⟨(v, w), hmem, ?_⟩
    rw [hbase]
    simp only [Prod.mk.injEq, hbase, wwDefor_apply_p31, if_neg hw, if_neg hvw1,
      and_true]

/-- HOL `WW_DEFOR_RHO_NODE1` (ODXLSTC.hl:1115): the `rho_node1` choice
transfers through the `w1`-deformation. -/
theorem WW_DEFOR_RHO_NODE1_p31 {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • w1 ≠ x.1 ∧ (1 - t) • w1 ≠ x.2)
    (hw1v : (w1, v) ∈ FF) (hv : (v, w1) ∉ FF) (ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = rhoNode1 FF v :=
  epsilon_ext_p31 (fun u => WW_DEFOR_FF3_p31 h hw1v hv ht u)

/-- HOL `WW_DEFOR_FF4` (ODXLSTC.hl:1222): the local-fan version of `FF3` for
the incoming dart `(v, w1)`. -/
theorem WW_DEFOR_FF4_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (hvw : (v, w1) ∈ FF)
    (_ht : t ≠ 0) (w : V3) :
    (w, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (w, v) ∈ FF := by
  sorry
  -- NEEDS (still): the local-fan distinctness kit — `LOCAL_FAN_IMP_IN_V2`,
  -- `IVS_RHO_NODE1_DETE`, `DETER_RHO_NODE`, `LOFA_IMP_EE_TWO_ELMS_INS_ND`,
  -- `LOFA_CARD_EE_V_2`. Root blocker: `LocalFan V E FF` is the registry
  -- stub `fun _ _ _ => True` (LocalAuto1.lean:138), so the hypotheses carry
  -- no fan structure; the named HOL lemmas exist in this repo only against
  -- the different predicate `localFan_p2` (LocalAuto5).

/-- HOL `WW_DEFOR_RHO_NODE2` (ODXLSTC.hl:1306): the `ivs` choice transfers. -/
theorem WW_DEFOR_RHO_NODE2_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hvw : (v, w1) ∈ FF) (ht : t ≠ 0) :
    (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = (Classical.epsilon fun a => (a, v) ∈ FF) :=
  epsilon_ext_p31 (fun u => WW_DEFOR_FF4_p31 hlf hg hvw ht u)

/-- HOL `WW_DEFOR_FF5` (ODXLSTC.hl:1393): neither edge case, outgoing. -/
theorem WW_DEFOR_FF5_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (hv : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (_hvw : (v, w1) ∉ FF) (_ht : t ≠ 0)
    (_hvV : v ∈ V) (_hw1V : w1 ∈ V) (w : V3) :
    (wwDefor_p31 w1 v t, w) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (v, w) ∈ FF := by
  sorry
  -- NEEDS (still): `GENERIC_HYPOTHESIS_WW_DEFOR` kit +
  -- `PROPERTIES_GENERIC_LOCAL_FAN` (genericity puts `v` off the
  -- `affGt {0} {w1}` line, excluding the `(1 - t) % w1 = v` alignment).
  -- Root blocker: `LocalFan` stub (`True`, LocalAuto1.lean:138).

/-- HOL `GENERIC_WW_DEFOR_RHO_NODE1_NOT_EDGE` (ODXLSTC.hl:1454). -/
theorem GENERIC_WW_DEFOR_RHO_NODE1_NOT_EDGE_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hv : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (hvw : (v, w1) ∉ FF) (ht : t ≠ 0)
    (hvV : v ∈ V) (hw1V : w1 ∈ V) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = rhoNode1 FF v :=
  epsilon_ext_p31 (fun u =>
    WW_DEFOR_FF5_p31 hlf hg hv hwv hvw ht hvV hw1V u)

/-- HOL `WW_DEFOR_FF6` (ODXLSTC.hl:1470): neither edge case, incoming. -/
theorem WW_DEFOR_FF6_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (hv : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (_hvw : (v, w1) ∉ FF) (_ht : t ≠ 0)
    (_hvV : v ∈ V) (_hw1V : w1 ∈ V) (w : V3) :
    (w, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (w, v) ∈ FF := by
  sorry
  -- NEEDS (still): same kit as WW_DEFOR_FF5_p31 (mirror case) — root
  -- blocker the `LocalFan` stub (`True`, LocalAuto1.lean:138).

/-- HOL `GENERIC_WW_DEFOR_RHO_NODE1_NOT_EDGE2` (ODXLSTC.hl:1527). -/
theorem GENERIC_WW_DEFOR_RHO_NODE1_NOT_EDGE2_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hv : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (hvw : (v, w1) ∉ FF) (ht : t ≠ 0)
    (hvV : v ∈ V) (hw1V : w1 ∈ V) :
    (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = (Classical.epsilon fun a => (a, v) ∈ FF) :=
  epsilon_ext_p31 (fun u =>
    WW_DEFOR_FF6_p31 hlf hg hv hwv hvw ht hvV hw1V u)

/-! ## Section 8: genericity hypothesis and the azimuth transfer -/

/-- HOL `GENERIC_HYPOTHESIS_WW_DEFOR` (ODXLSTC.hl:973): under `local_fan` +
genericity the deformed base point `(1 - t) % v` misses every dart end. -/
theorem GENERIC_HYPOTHESIS_WW_DEFOR_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_ht : t ≠ 0) (_hv : v ∈ V) (_hg : Generic V E) :
    ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2 := by
  sorry
  -- NEEDS (still): `LOCAL_FAN_IN_FF_DISTINCT` (darts have distinct ends) and
  -- `LOFA_IMP_V_DIFF` + `PROPERTIES_GENERIC_LOCAL_FAN`/`AFF2` (genericity
  -- puts `v` off `affGt {0} {x.1}` unless `t = 0`). Root blocker: the
  -- `LocalFan` registry stub is `True` (LocalAuto1.lean:138); the named HOL
  -- lemmas exist here only against `localFan_p2` (LocalAuto5).

/-- HOL `WW_DEFOR_AZIM` (ODXLSTC.hl:954): the interior azimuth at the
deformed base point equals the original (azimuth scale invariance). -/
theorem WW_DEFOR_AZIM_p31 {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2) (ht : t < 1) :
    azim 0 (wwDefor_p31 v v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
        (wwDefor_p31 v v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 v v t) ∈
        (fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  sorry
  -- NEEDS (still): `AZIM_SPECIAL_SCALE` — azimuth invariance under
  -- `(1 - t) % v`, `0 < 1 - t` — is NOT ported anywhere (PlanarityAuto8
  -- documents the gap; Kepler.Geom.Azim/AzimLemmas have no scale lemma).
  -- With it, the transfers WW_DEFOR_rho_node1_p31 / WW_DEFOR_APHA_p31
  -- (both proved above) finish this.

/-- HOL `GENEIRC_WW_DEFOR_AZIM` (ODXLSTC.hl:1039): the local-fan generic
version of WW_DEFOR_AZIM (with the `t = 0` identity case). -/
theorem GENEIRC_WW_DEFOR_AZIM_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V) (_hg : Generic V E) (_ht : t < 1) :
    azim 0 (wwDefor_p31 v v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
        (wwDefor_p31 v v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 v v t) ∈
        (fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  sorry
  -- NEEDS (still): WW_DEFOR_AZIM_p31 via GENERIC_HYPOTHESIS_WW_DEFOR_p31
  -- (both `sorry`: azim scale lemma unported + `LocalFan` stub `True`);
  -- the `t = 0` case is WW_DEFOR_0_ID + IMAGE_ID.

/-- HOL `AZIM_DEFOR_EDGE1` (ODXLSTC.hl:1189): azimuth transfer for the
outgoing edge dart `(w1, v)`. -/
theorem AZIM_DEFOR_EDGE1_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hw : (w1, v) ∈ FF)
    (_ht : t < 1) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  sorry
  -- NEEDS (still): WW_DEFOR_ALPHA3 (`CHOICE_LEMMA`) +
  -- GENERIC_WW_DEFOR_RHO_NODE1 + `AZIM_SCALE_ALL` — root blocker the
  -- `LocalFan` stub (`True`, LocalAuto1.lean:138); `AZIM_SCALE_ALL` unported.

/-- HOL `AZIM_DEFOR_EDGE2` (ODXLSTC.hl:1365): azimuth transfer for the
incoming edge dart `(v, w1)`. -/
theorem AZIM_DEFOR_EDGE2_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hv : (v, w1) ∈ FF)
    (_ht : t < 1) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  sorry
  -- NEEDS (still): WW_DEFOR_RHO_NODE2 + GENERIC_WW_DEFOR_RHO_NODE2 +
  -- `AZIM_SCALE_ALL` — root blocker the `LocalFan` stub (`True`,
  -- LocalAuto1.lean:138); `AZIM_SCALE_ALL` unported.

/-- HOL `AZIM_DEFOR_EDGE3` (ODXLSTC.hl:1540): azimuth transfer when `(v, w1)`
is not a dart of the fan in either order. -/
theorem AZIM_DEFOR_EDGE3_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hv : v ≠ w1)
    (_hwv : (w1, v) ∉ FF) (_hvw : (v, w1) ∉ FF)
    (_hvV : v ∈ V) (_hw1V : w1 ∈ V) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  sorry
  -- NEEDS (still): GENERIC_WW_DEFOR_RHO_NODE1_NOT_EDGE{,2} (from
  -- WW_DEFOR_FF5/FF6) + AZIM_SPECIAL_SCALE — root blocker the `LocalFan`
  -- stub (`True`, LocalAuto1.lean:138); azim scale lemma unported.

/-- HOL `AZIM_DEFORMATION_GENERIC` (ODXLSTC.hl:1566): azimuth transfer under
`ww_defor w1` for arbitrary `v, w1 ∈ V` — trichotomy over the edge cases.
DISCHARGES: composition of AZIM_DEFOR_EDGE{1,2,3}_p31 and
GENEIRC_WW_DEFOR_AZIM_p31 (each itself skeleton). -/
theorem AZIM_DEFORMATION_GENERIC_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hv : v ∈ V) (hw1 : w1 ∈ V)
    (ht : t < 1) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  by_cases hw : w1 = v
  · subst hw
    exact GENEIRC_WW_DEFOR_AZIM_p31 hlf hv hg ht
  by_cases h1 : (w1, v) ∈ FF
  · exact AZIM_DEFOR_EDGE1_p31 hlf hg h1 ht
  by_cases h2 : (v, w1) ∈ FF
  · exact AZIM_DEFOR_EDGE2_p31 hlf hg h2 ht
  · exact AZIM_DEFOR_EDGE3_p31 hlf hg (Ne.symm hw) h1 h2 hv hw1

/-! ## Section 9: V/E/F image identities, hull and rho_fun facts -/

/-- HOL `V_DEFORMATION_WW_DEFOR` (ODXLSTC.hl:1595). -/
theorem V_DEFORMATION_WW_DEFOR_p31 (w1 : V3) (w : ℕ → V3) (t : ℝ) :
    (fun v => wwDefor_p31 w1 v t) '' Set.range w
      = Set.range (fun i => wwDefor_p31 w1 (w i) t) := by
  ext x
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self i
  · intro hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨w i, Set.mem_range_self i, rfl⟩

/-- HOL `E_DEFORMATION_WW_DEFOR` (ODXLSTC.hl:1602). -/
theorem E_DEFORMATION_WW_DEFOR_p31 (w1 : V3) (w : ℕ → V3) (t : ℝ) :
    Set.range (fun i => {wwDefor_p31 w1 (w i) t, wwDefor_p31 w1 (w (i + 1)) t})
      = (fun S => (fun v => wwDefor_p31 w1 v t) '' S) ''
          Set.range (fun i => {w i, w (i + 1)}) := by
  ext S
  constructor
  · rintro ⟨i, rfl⟩
    refine (Set.mem_image _ _ _).mpr ⟨{w i, w (i + 1)}, Set.mem_range_self i, ?_⟩
    simp [Set.image_pair]
  · rintro ⟨S', hS', rfl⟩
    rw [Set.mem_range] at hS'
    obtain ⟨i, rfl⟩ := hS'
    have hf : (fun v => wwDefor_p31 w1 v t) '' {w i, w (i + 1)}
        = {wwDefor_p31 w1 (w i) t, wwDefor_p31 w1 (w (i + 1)) t} := by
      simp [Set.image_pair]
    show (fun v => wwDefor_p31 w1 v t) '' {w i, w (i + 1)} ∈
        (Set.range (fun j => {wwDefor_p31 w1 (w j) t, wwDefor_p31 w1 (w (j + 1)) t}) :
          Set (Set V3))
    rw [hf]
    exact Set.mem_range_self i

/-- HOL `F_DEFORMATION_WW_DEFOR` (ODXLSTC.hl:1620). -/
theorem F_DEFORMATION_WW_DEFOR_p31 (w1 : V3) (w : ℕ → V3) (t : ℝ) :
    Set.range (fun i => (wwDefor_p31 w1 (w i) t, wwDefor_p31 w1 (w (i + 1)) t))
      = (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) ''
          Set.range (fun i => (w i, w (i + 1))) := by
  ext d
  constructor
  · rintro ⟨i, rfl⟩
    refine (Set.mem_image _ _ _).mpr ⟨(w i, w (i + 1)), Set.mem_range_self i, ?_⟩
    simp
  · rintro ⟨d', hd', rfl⟩
    rw [Set.mem_range] at hd'
    obtain ⟨i, rfl⟩ := hd'
    show (wwDefor_p31 w1 (w i) t, wwDefor_p31 w1 (w (i + 1)) t) ∈
        (Set.range (fun j => (wwDefor_p31 w1 (w j) t, wwDefor_p31 w1 (w (j + 1)) t)) :
          Set (V3 × V3))
    exact Set.mem_range_self i

/-- HOL `WW_DEFOR_AFFINE_HULL` (ODXLSTC.hl:1639): the moving base point stays
in `affine hull {0, v, w', w1}`. -/
theorem WW_DEFOR_AFFINE_HULL_p31 (w1 v w' : V3) (e t : ℝ) (_ht : t ∈ Icc (-e) e) :
    wwDefor_p31 w1 w1 t ∈ affineSpan ℝ ({0, v, w', w1} : Set V3) := by
  have hvv : wwDefor_p31 w1 w1 t = (1 - t) • w1 := by simp [wwDefor_apply_p31]
  rw [hvv]
  have h0 : (0:V3) ∈ (affineSpan ℝ ({0, v, w', w1} : Set V3) : AffineSubspace ℝ V3) :=
    subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hw1 : (w1:V3) ∈ (affineSpan ℝ ({0, v, w', w1} : Set V3) : AffineSubspace ℝ V3) :=
    subset_affineSpan ℝ _ (by simp)
  have hlm := AffineMap.lineMap_mem (1 - t) h0 hw1
  rw [AffineMap.lineMap_apply_module] at hlm
  simpa using hlm

/-- HOL `rho_fun_decreasing` (ODXLSTC.hl:2521): shrinking `wl` strictly
decreases `rho_fun (norm .)`. -/
theorem rho_fun_decreasing_p31 (wl : V3) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hw : wl ≠ 0) :
    rhoFun (norm (wwDefor_p31 wl wl t)) < rhoFun (norm wl) := by
  have hvv : wwDefor_p31 wl wl t = (1 - t) • wl := by simp [wwDefor_apply_p31]
  have h01 : 0 ≤ 1 - t := by linarith
  have hnorm : norm ((1 - t) • wl) = (1 - t) * norm wl := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h01]
  have hpos : 0 < norm wl := norm_pos_iff.mpr hw
  have hlt : (1 - t) * norm wl < norm wl := by nlinarith
  have hsub : 0 < norm wl - (1 - t) * norm wl := by linarith
  unfold rhoFun
  rw [hvv, hnorm]
  have hslope : (0:ℝ) < 1 / (2 * h0 - 2) * (1 / Real.pi) * sol0 := by
    have hh : (h0:ℝ) = 1.26 := rfl
    have h2 : (0:ℝ) < 2 * h0 - 2 := by norm_num [hh]
    have hpi : (0:ℝ) < 1 / Real.pi := by
      rw [one_div]; exact inv_pos.mpr Real.pi_pos
    have hinv : (0:ℝ) < 1 / (2 * h0 - 2) := by
      rw [one_div]; exact inv_pos.mpr h2
    exact mul_pos (mul_pos hinv hpi) sol0Pos_p31
  nlinarith [hslope, hsub]

/-! ## Section 10: the registry conclusions and the ODXLSTC giants -/

/-- HOL `MHAEYJN_concl` (ODXLSTC.hl:1657): a lunar-symmetric deformation of a
convex local fan keeps it a convex local fan (lunar case). -/
def MHAEYJN_concl_p31 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (v w u : V3),
    ConvexLocalFan V E FF →
    Lunar v w V E →
    Deformation f V a b →
    interiorAngle1 0 FF v < Real.pi →
    u ∈ V → u ≠ v → u ≠ w →
    (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
    (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
    ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t → t < e →
      ConvexLocalFan ((fun x => f x t) '' V)
        ((fun S => (fun x => f x t) '' S) '' E)
        ((fun uv => (f uv.1 t, f uv.2 t)) '' FF) ∧
      Lunar v w ((fun x => f x t) '' V) ((fun S => (fun x => f x t) '' S) '' E)

/-- HOL `ZLZTHIC_concl` (ODXLSTC.hl:1676): under the non-obtuse interior
angle transfer hypothesis a deformation keeps the fan convex and generic. -/
def ZLZTHIC_concl_p31 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3),
    ConvexLocalFan V E FF →
    Generic V E →
    Deformation f V a b →
    (∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun uv => (f uv.1 t, f uv.2 t)) '' FF) (f v t) ≤ Real.pi) →
    ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t → t < e →
      ConvexLocalFan ((fun x => f x t) '' V)
        ((fun S => (fun x => f x t) '' S) '' E)
        ((fun uv => (f uv.1 t, f uv.2 t)) '' FF) ∧
      Generic ((fun x => f x t) '' V) ((fun S => (fun x => f x t) '' S) '' E)

/-- HOL `LEMMA1_concl` (ODXLSTC.hl:1711): the ww_defor deformation of a
non-ear vertex keeps a convex local fan. -/
def LEMMA1_concl_p31 : Prop :=
  ∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3),
    isScsV39 s → w ∈ MMsV39 s → s.k = k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    ‖w l‖ ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬ s.J l i) →
    (∀ V : Set V3, ∀ E : Set (Set V3), ∀ v : V3, V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬ Lunar v (w l) V E) →
    ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t → t < e →
      ConvexLocalFan (Set.range (fun i => wwDefor_p31 (w l) (w i) t))
        (Set.range (fun i => {wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t}))
        (Set.range (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t)))

/-- HOL `ODXLSTCv2_concl` (ODXLSTC.hl:1695): the conjunction is contradictory
(the deformation would produce a valid non-lunar realisation). -/
def ODXLSTCv2_concl_p31 : Prop :=
  ∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3),
    isScsV39 s → w ∈ MMsV39 s → s.k = k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    ‖w l‖ ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬ s.J l i) →
    (∀ V : Set V3, ∀ E : Set (Set V3), ∀ v : V3, V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬ Lunar v (w l) V E) →
    False

/-- HOL `TAUSTAR_WW_DEFOR_concl` (ODXLSTC.hl:1736): the deformation strictly
decreases taustar. -/
def TAUSTAR_WW_DEFOR_concl_p31 : Prop :=
  ∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (e1 : ℝ),
    isScsV39 s → w ∈ MMsV39 s → s.k = k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    ‖w l‖ ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬ s.J l i) →
    (∀ t, 0 < t → t < e1 → BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t)) →
    0 < e1 → e1 < 1 →
    (∀ V : Set V3, ∀ E : Set (Set V3), ∀ v : V3, V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬ Lunar v (w l) V E) →
    ∃ e : ℝ, 0 < e ∧ ∀ t, 0 < t → t < e →
      taustarV39 s (fun i => wwDefor_p31 (w l) (w i) t) < taustarV39 s w

/-- HOL `WW_DEFORMATION_CONVEX_LOCAL_FAN` (ODXLSTC.hl:1758): ZLZTHIC + MHAEYJN
imply LEMMA1. -/
theorem WW_DEFORMATION_CONVEX_LOCAL_FAN_p31 (hz : ZLZTHIC_concl_p31)
    (_hm : MHAEYJN_concl_p31) : LEMMA1_concl_p31 := by
  sorry
  -- NEEDS (still): `JKQEWGV2` (MMs realisation is a convex local fan) —
  -- proved only as the `sorry` stubs `JKQEWGV2_concl` (LocalAuto1) /
  -- `JKQEWGV2_p23` (LocalAuto23, itself needing the `sorry`
  -- `JKQEWGV2_CASE_*_p23`), plus `Deformation.XRECQNS`,
  -- `Wrgcvdr_cizmrrh.CIZMRRH`, the interior-angle transfer via
  -- AZIM_DEFORMATION_GENERIC_p31, CARD_V_EQ_SCS_K1_p31 (now proved above)
  -- and the annulus pin DEFORMATION_IN_BALL_ANNULUS_p31 (proved above).

/-- HOL `CARD_V_EQ_SCS_K1` (ODXLSTC.hl:1961): a BBs realisation image has
cardinality exactly `scs_k_v39 s`. The HOL route (`IS_SCS_STABLE_SYSTEM` +
`SCS_K_LE_6` + `V_E_FF_IS_SCS_CASES_{4,5,6}`, themselves `sorry`s in the
importable lanes) is replaced by `VV_INJ_p31` + periodicity: the image of
`{i | i < k}` under a periodic, mod-k-injective family has exactly `k`
points. -/
theorem CARD_V_EQ_SCS_K1_p31 (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (V : Set V3)
    (hk : s.k = k) (hV : Set.range vv = V) (his : isScsV39 s) (_hk3 : 3 < k)
    (hbb : BBsV39 s vv) : V.ncard = k := by
  have hkpos : 0 < k := by
    have := his.2.1
    rw [hk] at this
    omega
  have hper : Periodic vv s.k := hbb.2.1
  have pm : ∀ a, vv (a % k) = vv a := by
    intro a
    have hm := periodic_mod_p18 hper a
    rwa [hk] at hm
  have hinj : ∀ a b, a < k → b < k → a ≠ b → vv a ≠ vv b :=
    fun a b ha hb hab => VV_INJ_p31 s k vv hk his hbb a b ⟨ha, hb, hab⟩
  have hVe : V = (fun i => vv i) '' {i | i < k} := by
    rw [← hV]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a % k, Nat.mod_lt a (by omega), pm a⟩
    · rintro ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
  rw [hVe]
  have hco : {i | i < k} = ((Finset.range k : Finset ℕ) : Set ℕ) :=
    (Finset.coe_range k).symm
  rw [hco, ← Finset.coe_image, Set.ncard_coe_finset, Finset.card_image_of_injOn,
    Finset.card_range]
  intro a ha b hb heq
  by_contra hne
  rw [Finset.mem_coe, Finset.mem_range] at ha hb
  exact hinj a b ha hb hne heq

/-- HOL `CARD_FF_EQ_WW_DEFORMATION` (ODXLSTC.hl:2089). -/
theorem CARD_FF_EQ_WW_DEFORMATION_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (e1 : ℝ)
    (_hk : s.k = k) (_his : isScsV39 s) (_hk3 : 3 < k) (_hbb : BBsV39 s w)
    (_hbb' : ∀ t, 0 < t → t < e1 → BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t)) :
    ∀ t, 0 < t → t < e1 →
      (Set.range (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))).ncard
        = (Set.range (fun i => (w i, w (i + 1)))).ncard := by
  sorry
  -- NEEDS (still): CARD_V_EQ_SCS_K1_p31 (proved above) +
  -- `LOFA_IMP_CARD_FF_V_EQ` (FF-cardinality from V-cardinality; local-fan
  -- kit — root blocker the `LocalFan` stub `True`, LocalAuto1.lean:138).

/-- HOL `DSV_WW_DEFOR_EQ` (ODXLSTC.hl:2126): dsv is invariant under the
deformation when the l-row of J is empty. The J-darts avoid the vertex `l`
cyclically (`_hJ` + J-symmetry + `Periodic2 s.J`), so `VV_INJ_p31` makes
the deformation fix every J-dart pointwise and the summand functions agree
on the J-set. -/
theorem DSV_WW_DEFOR_EQ_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (t : ℝ)
    (hk : s.k = k) (his : isScsV39 s) (hbb : BBsV39 s w)
    (hJ : ∀ i, ¬ s.J l i) :
    dsvV39 s (fun i => wwDefor_p31 (w l) (w i) t) = dsvV39 s w := by
  have hkpos : 0 < k := by
    have := his.2.1
    rw [hk] at this
    omega
  obtain ⟨-, hper, -, -⟩ := id hbb
  have hpa : Periodic2 s.a s.k := isScsV39_periodic2_a_p31 s his
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hJper, hJsym, _, _, _, _, _, _, _, _⟩ := id his
  have hJs : ∀ i j, s.J i j = s.J j i := fun i j => (hJsym i j).2.2.2.2
  have hjmod : ∀ i j, s.J (i % k) (j % k) = s.J i j := by
    intro i j
    have hm := periodic2_mod_p18 hJper i j
    rwa [hk] at hm
  have pm : ∀ a, w (a % k) = w a := by
    intro a
    have hm := periodic_mod_p18 hper a
    rwa [hk] at hm
  have hinj : ∀ a b, a < k → b < k → a ≠ b → w a ≠ w b :=
    fun a b ha hb hab => VV_INJ_p31 s k w hk his hbb a b ⟨ha, hb, hab⟩
  -- a J-dart never has `w m = w l` at its tail
  have hne_l : ∀ m, s.J m (m + 1) → w m ≠ w l := by
    intro m hmJ heq
    by_cases hml : m % k = l % k
    · have hmeq : (m + 1) % k = (l + 1) % k := Nat.ModEq.add_right 1 hml
      have h1 : s.J (l % k) ((l + 1) % k) := by
        rw [← hml, ← hmeq, hjmod m (m + 1)]
        exact hmJ
      have h2 : s.J l (l + 1) := by
        rw [← hjmod l (l + 1)]
        exact h1
      exact hJ (l + 1) h2
    · have h1 : w (m % k) ≠ w (l % k) := hinj _ _ (Nat.mod_lt m (by omega))
        (Nat.mod_lt l (by omega)) hml
      apply h1
      rw [pm m, pm l]
      exact heq
  -- ... nor at its head
  have hne_l1 : ∀ m, s.J m (m + 1) → w (m + 1) ≠ w l := by
    intro m hmJ heq
    by_cases hml : (m + 1) % k = l % k
    · have h1m : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
      have e1 : (m + 1) % k = (m % k + 1) % k := by rw [Nat.add_mod, h1m]
      have hA : (m % k + 1) % k = l % k := by rw [← e1]; exact hml
      have hkey : m % k = (l + k - 1) % k := by
        have hB := Nat.ModEq.add_right (k - 1) hA
        rw [show m % k + 1 + (k - 1) = m % k + k by omega] at hB
        have hB' : (m % k + k) % k = (l + (k - 1)) % k := hB
        rw [Nat.add_mod_right, Nat.mod_mod] at hB'
        have heq1 : l + (k - 1) = l + k - 1 := by omega
        rwa [heq1] at hB'
      have hJ1 : s.J ((l + k - 1) % k) (l % k) := by
        have hm := hjmod m (m + 1)
        rw [hkey, hml] at hm
        exact hm.symm ▸ hmJ
      have hJ2 : s.J (l % k) ((l + k - 1) % k) := hJs _ _ ▸ hJ1
      have hJ3 : s.J l ((l + k - 1) % k) := by
        have hm := hjmod l ((l + k - 1) % k)
        rw [Nat.mod_mod] at hm
        rw [← hm]
        exact hJ2
      exact hJ ((l + k - 1) % k) hJ3
    · have h1 : w ((m + 1) % k) ≠ w (l % k) := hinj _ _ (Nat.mod_lt _ (by omega))
        (Nat.mod_lt l (by omega)) hml
      apply h1
      rw [pm (m + 1), pm l]
      exact heq
  have hcong : setSum {i | i < s.k ∧ s.J i (i + 1)}
      (fun i => cstab - dist (wwDefor_p31 (w l) (w i) t)
        (wwDefor_p31 (w l) (w (i + 1)) t))
      = setSum {i | i < s.k ∧ s.J i (i + 1)}
        (fun i => cstab - dist (w i) (w (i + 1))) := by
    refine setSum_congr_p31 fun i hi => ?_
    obtain ⟨-, hmJ⟩ := hi
    rw [wwDefor_apply_p31, if_neg (hne_l i hmJ), wwDefor_apply_p31,
      if_neg (hne_l1 i hmJ)]
  unfold dsvV39
  rw [hcong]

/-- HOL `INTERIOR_ANGLE_SAME_WW_DEFOR0` (ODXLSTC.hl:2264). -/
theorem INTERIOR_ANGLE_SAME_WW_DEFOR0_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (t : ℝ) (FF : Set (V3 × V3))
    (_hk3 : 3 < k) (_his : isScsV39 s) (_hk : s.k = k) (_hbb : BBsV39 s w)
    (_hbb' : BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t))
    (_hFF : Set.range (fun i => (w i, w (i + 1))) = FF) (_ht : t < 1) :
    interiorAngle1 0
      (Set.range (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t)))
      (wwDefor_p31 (w l) (w (l % k)) t)
      = interiorAngle1 0 FF (w (l % k)) := by
  sorry
  -- NEEDS (still): `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS`,
  -- `ITER_CARD_MINUS1_EQ_IVS_RN1`, `VV_SUC_EQ_RHO_NODE_PRIME`,
  -- `LOFA_IMP_DIS_ELMS23`, `AZIM_SCALE_ALL` — root blocker the `LocalFan`
  -- stub (`True`, LocalAuto1.lean:138); azim scale lemma unported.

/-- HOL `INTERIOR_ANGLE_SAME_WW_DEFOR1` (ODXLSTC.hl:2359): the iterated
rho_node1 version. -/
theorem INTERIOR_ANGLE_SAME_WW_DEFOR1_p31 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (t : ℝ) (FF : Set (V3 × V3))
    (_hk3 : 3 < k) (_his : isScsV39 s) (_hk : s.k = k) (_hbb : BBsV39 s w)
    (_hbb' : BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t))
    (_hFF : Set.range (fun i => (w i, w (i + 1))) = FF) (_ht : t < 1)
    (_hi1 : 1 ≤ i) (_hik : i < k) :
    interiorAngle1 0
      (Set.range (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t)))
      ((rhoNode1 (Set.range
          (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))))^[i]
        (wwDefor_p31 (w l) (w (l % k)) t))
      = interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k))) := by
  sorry
  -- NEEDS (still): same kit as INTERIOR_ANGLE_SAME_WW_DEFOR0_p31 plus
  -- `LOCAL_FAN_ITER_RHO_NODE_IN_V` and the `i = 1 / i = k-1 / interior`
  -- trichotomy (LocalFan stub `True`, LocalAuto1.lean:138).

/-- HOL `TAUSTAR_WW_DEFOR` (ODXLSTC.hl:2557): ZLZTHIC + MHAEYJN imply the
taustar decrease. -/
theorem TAUSTAR_WW_DEFOR_p31 (hz : ZLZTHIC_concl_p31) (_hm : MHAEYJN_concl_p31) :
    TAUSTAR_WW_DEFOR_concl_p31 := by
  sorry
  -- NEEDS (still): CARD_FF_EQ_WW_DEFORMATION_p31, DSV_WW_DEFOR_EQ_p31
  -- (proved above), `SUM_AZIM_EQ_ANGLE_LE4` (unported; LocalAuto12/18
  -- document the gap — only the `_FUN_p18` variant exists),
  -- INTERIOR_ANGLE_SAME_WW_DEFOR{0,1}_p31 (still `sorry`), and
  -- `INTERIOR_ANGLE1_POS` — chain-blocked by the `LocalFan` stub
  -- (`True`, LocalAuto1.lean:138).

/-- HOL `ODXLSTCv2` (ODXLSTC.hl:2692): ZLZTHIC + MHAEYJN imply the
contradiction ODXLSTCv2_concl. -/
theorem ODXLSTCv2_p31 (hz : ZLZTHIC_concl_p31) (_hm : MHAEYJN_concl_p31) :
    ODXLSTCv2_concl_p31 := by
  sorry
  -- NEEDS (still): WW_DEFORMATION_CONVEX_LOCAL_FAN_p31 + TAUSTAR_WW_DEFOR_p31
  -- (both still `sorry` above); DEFORMATION_DIST_LE_ALL_COM_p31 /
  -- DEFORMATION_DIST_LE_BLL_COM_p31 / DEFORMATION_IN_BALL_ANNULUS_p31 (all
  -- proved above) are ready to be composed into the BBs-viability
  -- contradiction once the two wrappers land.

/-- HOL `GENERIC_WW_DEFOR_RHO_NODE1` (ODXLSTC.hl:1126): the `rho_node1`
transfer for the outgoing edge dart under `local_fan`. -/
theorem GENERIC_WW_DEFOR_RHO_NODE1_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hw : (w1, v) ∈ FF)
    (_ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = rhoNode1 FF v := by
  sorry
  -- NEEDS (still): WW_DEFOR_RHO_NODE1_p31 via GENERIC_HYPOTHESIS_WW_DEFOR_p31
  -- plus `IVS_RHO_NODE1_DETE`, `DETER_RHO_NODE`, `LOFA_IMP_EE_TWO_ELMS_INS_ND`,
  -- `LOFA_CARD_EE_V_2` — root blocker the `LocalFan` stub (`True`,
  -- LocalAuto1.lean:138).

/-- HOL `WW_DEFOR_ALPHA3` (ODXLSTC.hl:1144): the `ivs` choice at the deformed
point is `(1 - t) % w1` for the outgoing edge case. -/
theorem WW_DEFOR_ALPHA3_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hw : (w1, v) ∈ FF)
    (_ht : t ≠ 0) :
    (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = (1 - t) • w1 := by
  sorry
  -- NEEDS (still): `Hypermap_and_fan.CHOICE_LEMMA` + GENERIC_HYPOTHESIS kit +
  -- `FST_EQ_IF_SAME_SND` — root blocker the `LocalFan` stub (`True`,
  -- LocalAuto1.lean:138).

/-- HOL `GENERIC_WW_DEFOR_RHO_NODE2` (ODXLSTC.hl:1317): the `rho_node1` at
the deformed point is `(1 - t) % w1` for the incoming edge case. -/
theorem GENERIC_WW_DEFOR_RHO_NODE2_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hv : (v, w1) ∈ FF)
    (_ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = (1 - t) • w1 := by
  sorry
  -- NEEDS (still): same kit as WW_DEFOR_ALPHA3_p31 (mirror case,
  -- `CHOICE_LEMMA` + `DETER_RHO_NODE`) — root blocker the `LocalFan` stub
  -- (`True`, LocalAuto1.lean:138).

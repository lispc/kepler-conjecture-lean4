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
   (J-row emptyness + `VV_INJ_p31` + `setSum` congruence). The
   2026-09-19 pass filled `CARD_FF_EQ_WW_DEFORMATION` (shim: both dart
   ranges counted to `k` by the in-file `dartRange_ncard_p31` core —
   `VV_INJ_p31` injectivity for the original family, dart-by-dart
   residue case analysis for the deformed one; the HOL route's
   `LOFA_IMP_CARD_FF_V_EQ` local-fan kit is unavailable). Still `sorry`,
   all blocked by the *same* root cause: `LocalFan V E FF` is the stub
   `fun _ _ _ => True` (LocalAuto1.lean:138), so local-fan-conditioned
   hypotheses carry no structure, and the azim scale invariance
   `AZIM_SPECIAL_SCALE`/`AZIM_SCALE_ALL` is not ported (see NEEDS markers).

   ERRATUM (2026-11-03, scsgeneric-w5cC probe): every "root blocker:
   `LocalFan` stub (`True`, LocalAuto1.lean:138)" NEEDS marker below is
   OBSOLETE — `LocalFan` has been the real encoding since the lf-alpha
   wave (LocalAuto1.lean:161: FAN witness + `hypermapOfFan` dart orbit +
   `Dih2k` + 2-regularity `(ee u E).ncard = 2`), and the azim scale
   invariance is ported as `w5cC_azim_scale` (Section 8 head).  The import
   closure of this file reaches LocalAuto5/9/12/23/35 and AzimBridge, so
   the LA5 fan-rho kit, `JKQEWGV2_p23` (standard-three) and
   `SUM_AZIM_EQ_ANGLE_LE4_p35` are directly citable without new imports.
-/

import Kepler.Text.LocalAuto21
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto9
import Kepler.Text.AzimBridge
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto35
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

/-- Genericity keeps every other vertex off the line `0u`. -/
theorem w5cC_gen_excl {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : LocalFan V E FF) (hg : Generic V E) {u x : V3} (hu : u ∈ V)
    (hx : x ∈ V) (hne : x ≠ u) : ¬ Collinear ℝ ({0, u, x} : Set V3) :=
  PROPERTIES_GENERIC_LOCAL_FAN_p9 (w5cC_lf2_of_LocalFan hlf)
    (fun _ _ => True.intro) hg u hu x hx hne

/-- Off-base genericity kit (the repeated block of HOL
`GENERIC_HYPOTHESIS_WW_DEFOR`-style arguments at the shrunk vertex `w1`). -/
theorem w5cC_generic_hyp_offbase {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (ht : t ≠ 0) (hw1V : w1 ∈ V) :
    ∀ u ∈ V, (1 - t) • w1 ≠ u := by
  obtain ⟨HS, hd, he, hn, hf, hfan2, hface, hd2⟩ := w5cC_lf2_of_LocalFan hlf
  have hf0 : (0:V3) ∉ V := hfan2.2.2.2.1
  intro u hu hhe
  by_cases huu : u = w1
  · rw [huu] at hhe
    have e1 : (t:ℝ) • w1 = w1 - (1 - t) • w1 := by module
    rw [hhe] at e1
    have hz : t • w1 = (0:V3) := by simpa using e1
    have hz0 : w1 = 0 := (smul_eq_zero.mp hz).resolve_left ht
    have hw1V' : w1 ∈ V := huu ▸ hu
    exact hf0 (hz0 ▸ hw1V')
  · refine PROPERTIES_GENERIC_LOCAL_FAN_p9 (w5cC_lf2_of_LocalFan hlf)
      (fun _ _ => True.intro) hg w1 hw1V u hu huu ?_
    exact (collinear_triple_iff (x := (0:V3)) (v := w1) (u := u)).mpr
      (Or.inl (by
        rw [← hhe]
        exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
          ⟨1 - t, by rw [AffineMap.lineMap_apply]; simp⟩))

/-- The no-2-cycle exclusion. -/
theorem w5cC_no2cycle {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w1 : V3} (hlf : LocalFan V E FF) (hvw : (v, w1) ∈ FF)
    (hwv : (w1, v) ∈ FF) : False := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hlf' := hlf
  obtain ⟨hfan, x, hx, -, -, hreg⟩ := hlf'
  obtain ⟨hVsub, -, -, hf0, hfan6, -⟩ := hfan
  have hvV : v ∈ V := (LOCAL_FAN_IMP_IN_V2 h2 hvw).1
  have hr1 : rhoNode1_p2 FF v = w1 := DETER_RHO_NODE h2 hvw
  have hr2 : rhoNode1_p2 FF w1 = v := DETER_RHO_NODE h2 hwv
  have hind : ∀ n : ℕ, (rhoNode1_p2 FF)^[n] v ∈ ({v, w1} : Set V3) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases Set.mem_insert_iff.mp ih with hz | hz
      · rw [hz, hr1]; simp
      · rw [hz, hr2]; simp
  have hmem : ∀ u ∈ V, u = v ∨ u = w1 := by
    intro u hu
    have huo : u ∈ orbitF_p2 (rhoNode1_p2 FF) v := by
      rw [LOCAL_FAN_ORBIT_MAP_V h2 hvV]
      exact hu
    obtain ⟨n, hn⟩ := huo
    have hm := hind n
    rw [hn] at hm
    rcases Set.mem_insert_iff.mp hm with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
  have hsub : ∀ z ∈ (ee v E), z = w1 := by
    intro z hz
    have hE : ({v, z} : Set V3) ∈ E := hz
    have hzV : z ∈ V := by
      refine hVsub ?_
      exact Set.mem_sUnion.mpr ⟨({v, z} : Set V3), hE, by simp⟩
    rcases hmem z hzV with hzv | hzw
    · rw [hzv] at hE
      have hvE : ({v} : Set V3) ∈ E := by simpa using hE
      have hcol : Collinear ℝ ({0, v} : Set V3) := by
        have h := (collinear_triple_iff (x := (0:V3)) (v := v) (u := v)).mpr
          (Or.inl (mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
            ⟨1, by rw [AffineMap.lineMap_apply]; simp⟩))
        simpa using h
      have hc2 : Collinear ℝ (insert 0 ({v} : Set V3)) := by
        rw [show insert (0:V3) ({v} : Set V3) = ({0, v} : Set V3) from rfl]
        exact hcol
      exact (hfan6 {v} hvE hc2).elim
    · exact hzw
  have hnc : (ee v E).ncard = 2 := hreg v hvV
  have hle : (ee v E).ncard ≤ ({w1} : Set V3).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton] at hle
  omega

/-- HOL `GENERIC_HYPOTHESIS_WW_DEFOR` (ODXLSTC.hl:973). -/
theorem w5cC_GENERIC_HYPOTHESIS_WW_DEFOR {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (ht : t ≠ 0) (hv : v ∈ V) (hg : Generic V E) :
    ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2 := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hkey : ∀ u ∈ V, (1 - t) • v ≠ u :=
    w5cC_generic_hyp_offbase hlf hg ht hv
  intro x hx
  exact ⟨LOCAL_FAN_IN_FF_DISTINCT h2 hx, hkey x.1 ((LOCAL_FAN_IMP_IN_V2 h2 hx).1),
    hkey x.2 ((LOCAL_FAN_IMP_IN_V2 h2 hx).2)⟩


/-! ## The FF4/FF5/FF6 dart-image kit off the base vertex -/

theorem w5cC_WW_DEFOR_FF4 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hvw : (v, w1) ∈ FF)
    (ht : t ≠ 0) (w : V3) :
    (w, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (w, v) ∈ FF := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hvV : v ∈ V := (LOCAL_FAN_IMP_IN_V2 h2 hvw).1
  have hne : v ≠ w1 := fun hh => LOCAL_FAN_IN_FF_DISTINCT h2 hvw hh
  have hgen := w5cC_generic_hyp_offbase hlf hg ht ((LOCAL_FAN_IMP_IN_V2 h2 hvw).2)
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
  constructor
  · rintro ⟨x, hx, hpair⟩
    have hinj := hpair
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hxa, hxb⟩ := hinj
    rw [hvw'] at hxb
    by_cases hyw : x.2 = w1
    · rw [hyw, wwDefor_apply_p31, if_pos rfl] at hxb
      exact (hgen v hvV hxb).elim
    · rw [wwDefor_apply_p31, if_neg hyw] at hxb
      have hd0 : (x.1, x.2) ∈ FF := hx
      rw [hxb] at hd0
      by_cases hxw1 : x.1 = w1
      · exact absurd (by rw [hxw1] at hd0; exact hd0)
          (fun hx' => w5cC_no2cycle hlf hx' hvw)
      · rw [wwDefor_apply_p31, if_neg hxw1] at hxa
        rw [← hxa, ← hxb]
        simpa using hx
  · intro hmem
    have haw : w ≠ w1 := by
      intro hcon
      rw [hcon] at hmem
      exact w5cC_no2cycle hlf hmem hvw
    refine ⟨(w, v), hmem, ?_⟩
    simp only [wwDefor_apply_p31, if_neg haw, if_neg hne]

theorem w5cC_WW_DEFOR_FF5 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hnev : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (hvw : (v, w1) ∉ FF) (ht : t ≠ 0)
    (hvV : v ∈ V) (hw1V : w1 ∈ V) (w : V3) :
    (wwDefor_p31 w1 v t, w) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (v, w) ∈ FF := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hgen := w5cC_generic_hyp_offbase hlf hg ht hw1V
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hnev]
  constructor
  · rintro ⟨x, hx, hpair⟩
    have hinj := hpair
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hxa, hxb⟩ := hinj
    rw [hvw'] at hxa
    by_cases hxw1 : x.1 = w1
    · rw [hxw1, wwDefor_apply_p31, if_pos rfl] at hxa
      exact (hgen v hvV hxa).elim
    · rw [wwDefor_apply_p31, if_neg hxw1] at hxa
      have hxv : x.1 = v := hxa
      have hd0 : (x.1, x.2) ∈ FF := hx
      rw [hxv] at hd0
      have hru : rhoNode1_p2 FF v = x.2 := DETER_RHO_NODE h2 hd0
      have hrne : rhoNode1_p2 FF v ≠ w1 := by
        intro hcon
        rw [hcon] at hru
        exact hvw (by rw [hru]; exact hd0)
      have hx2w : x.2 ≠ w1 := by rw [← hru]; exact hrne
      rw [wwDefor_apply_p31, if_neg hx2w] at hxb
      rw [← hxb]
      exact hd0
  · intro hmem
    have hbw : w ≠ w1 := by
      intro hcon
      rw [hcon] at hmem
      exact hvw hmem
    refine ⟨(v, w), hmem, ?_⟩
    simp only [wwDefor_apply_p31, if_neg hnev, if_neg hbw]

theorem w5cC_WW_DEFOR_FF6 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hnev : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (hvw : (v, w1) ∉ FF) (ht : t ≠ 0)
    (hvV : v ∈ V) (hw1V : w1 ∈ V) (w : V3) :
    (w, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (w, v) ∈ FF := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hgen := w5cC_generic_hyp_offbase hlf hg ht hw1V
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hnev]
  constructor
  · rintro ⟨x, hx, hpair⟩
    have hinj := hpair
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hxa, hxb⟩ := hinj
    rw [hvw'] at hxb
    by_cases hyw : x.2 = w1
    · rw [hyw, wwDefor_apply_p31, if_pos rfl] at hxb
      exact (hgen v hvV hxb).elim
    · rw [wwDefor_apply_p31, if_neg hyw] at hxb
      have hd0 : (x.1, x.2) ∈ FF := hx
      rw [hxb] at hd0
      have hd : (x.1, v) ∈ FF := hd0
      have hivs : ivsRhoNode1_p2 FF v = x.1 := PRE_IVS_RHO_NODE1_DETE h2 hd
      have hwv' : ivsRhoNode1_p2 FF v ≠ w1 := by
        intro hcon
        have hx1 : x.1 = w1 := hivs.symm.trans hcon
        exact hwv (by rw [← hx1]; exact hd)
      have hx1w : x.1 ≠ w1 := fun hh => hwv' (hivs.trans hh)
      rw [wwDefor_apply_p31, if_neg hx1w] at hxa
      rw [← hxa, ← hxb]
      simpa using hx
  · intro hmem
    have haw : w ≠ w1 := by
      intro hcon
      rw [hcon] at hmem
      exact hwv hmem
    refine ⟨(w, v), hmem, ?_⟩
    simp only [wwDefor_apply_p31, if_neg haw, if_neg hnev]


/-- HOL `WW_DEFOR_FF4` (ODXLSTC.hl:1222): the local-fan version of `FF3` for
the incoming dart `(v, w1)`. -/
theorem WW_DEFOR_FF4_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (hvw : (v, w1) ∈ FF)
    (_ht : t ≠ 0) (w : V3) :
    (w, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (w, v) ∈ FF := by
  exact w5cC_WW_DEFOR_FF4 _hlf _hg hvw _ht w

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
  exact w5cC_WW_DEFOR_FF5 _hlf _hg hv hwv _hvw _ht _hvV _hw1V w

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
  exact w5cC_WW_DEFOR_FF6 _hlf _hg hv hwv _hvw _ht _hvV _hw1V w

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






open Kepler.Geom Set Classical

/-- Collinearity through the origin is preserved by independent nonzero
scalings of the two non-origin points (collinearity leg of the HOL
`AZIM_SCALE_ALL`). -/
theorem w5cC_lineMem_smul {v x : V3} (h : x ∈ affineSpan ℝ ({0, v} : Set V3)) :
    ∃ r : ℝ, x = r • v := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  refine ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply] at hr
  simpa using hr.symm

theorem w5cC_smul_lineMem (r : ℝ) (v : V3) :
    (r • v) ∈ affineSpan ℝ ({0, v} : Set V3) := by
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply]
  simp

theorem w5cC_collinear3_smul2_fwd {v x : V3} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcol : Collinear3 0 v x) : Collinear3 0 (a • v) (b • x) := by
  classical
  rcases (collinear_triple_iff (x := (0:V3)) (v := v) (u := x)).mp hcol with hu | h0
  · obtain ⟨r, hr⟩ := w5cC_lineMem_smul hu
    have hbv : b • x = (b * r / a) • (a • v) := by
      rw [hr, smul_smul, smul_smul]
      exact congrArg (fun (s : ℝ) => s • v)
        (show b * r = (b * r / a) * a from by field_simp)
    refine (collinear_triple_iff (x := (0:V3)) (v := a • v) (u := b • x)).mpr
      (Or.inl ?_)
    rw [hbv]
    exact w5cC_smul_lineMem _ _
  · refine (collinear_triple_iff (x := (0:V3)) (v := a • v) (u := b • x)).mpr
      (Or.inr ?_)
    rw [← h0, smul_zero]

/-- Collinearity through the origin is invariant under independent nonzero
scalings of the two non-origin points. -/
theorem w5cC_collinear3_smul2 {v x : V3} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Collinear3 0 v x ↔ Collinear3 0 (a • v) (b • x) := by
  constructor
  · exact w5cC_collinear3_smul2_fwd ha hb
  · intro hcol
    have h := w5cC_collinear3_smul2_fwd (a := a⁻¹) (b := b⁻¹)
      (inv_ne_zero ha) (inv_ne_zero hb) hcol
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, smul_smul, inv_mul_cancel₀ hb, one_smul] at h
    exact h

/-- HOL `AZIM_SCALE_ALL` (azimuth scale invariance): with every scale
positive, the azimuth at the origin is unchanged by independently scaling the
axis and the two ray points.  This is the missing `AZIM_SPECIAL_SCALE` /
`AZIM_SCALE_ALL` recorded in the LocalAuto31 NEEDS markers. -/
theorem w5cC_azim_scale {v w1 w2 : V3} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    azim 0 (a • v) (b • w1) (c • w2) = azim 0 v w1 w2 := by
  classical
  have hiff1 := w5cC_collinear3_smul2 (v := v) (x := w1) (a := a) (b := b)
    (ne_of_gt ha) (ne_of_gt hb)
  have hiff2 := w5cC_collinear3_smul2 (v := v) (x := w2) (a := a) (b := c)
    (ne_of_gt ha) (ne_of_gt hc)
  show (if Collinear3 0 (a • v) (b • w1) ∨ Collinear3 0 (a • v) (c • w2) then (0:ℝ)
      else Classical.epsilon (AzimSpec 0 (a • v) (b • w1) (c • w2)))
    = (if Collinear3 0 v w1 ∨ Collinear3 0 v w2 then (0:ℝ)
      else Classical.epsilon (AzimSpec 0 v w1 w2))
  by_cases hcol : Collinear3 0 v w1 ∨ Collinear3 0 v w2
  · rcases hcol with h | h
    · rw [if_pos (Or.inl (hiff1.mp h)), if_pos (Or.inl h)]
    · rw [if_pos (Or.inr (hiff2.mp h)), if_pos (Or.inr h)]
  · push_neg at hcol
    have hn1 : ¬ Collinear3 0 (a • v) (b • w1) := fun hh => hcol.1 (hiff1.mpr hh)
    have hn2 : ¬ Collinear3 0 (a • v) (c • w2) := fun hh => hcol.2 (hiff2.mpr hh)
    obtain ⟨h0θ, h2piθ, hh1, hh2, hframes⟩ := azim_master 0 v w1 w2
    have hvne : v ≠ 0 := by
      intro hzz
      apply hcol.1
      rw [hzz]
      exact (collinear_triple_iff (x := (0:V3)) (v := (0:V3)) (u := w1)).mpr (Or.inr rfl)
    have hav0 : (a • v) ≠ 0 := by
      intro hzz
      apply hn1
      rw [hzz]
      exact (collinear_triple_iff (x := (0:V3)) (v := (0:V3)) (u := b • w1)).mpr (Or.inr rfl)
    refine azim_eq_of_spec (θ := azim 0 v w1 w2) hn1 hn2
      ⟨h0θ, h2piθ, b * hh1 / a, c * hh2 / a, ?_⟩
    intro e1 e2 e3 horth hax _
    have hax' : v = dist v 0 • e3 := by
      have hna : dist (a • v) 0 = a * dist v 0 := by
        rw [dist_zero_right, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ha]
      rw [hna, sub_zero] at hax
      exact smul_right_injective V3 (ne_of_gt ha)
        (show a • (dist v 0 • e3) = a • v by rw [smul_smul]; exact hax.symm) |>.symm
    obtain ⟨psi, r1, r2, hs1, hs2, hr1, hr2⟩ :=
      hframes e1 e2 e3 horth (by rw [sub_zero]; exact hax') hvne
    rw [sub_zero, sub_zero] at hs1 hs2
    have hb1 : (b * hh1 / a) • ((a • v : V3) - 0) = b • (hh1 • v) := by
      rw [sub_zero, smul_smul, smul_smul]
      exact congrArg (fun (s : ℝ) => s • v)
        (show (b * hh1 / a) * a = b * hh1 from by field_simp)
    have hb2 : (c * hh2 / a) • ((a • v : V3) - 0) = c • (hh2 • v) := by
      rw [sub_zero, smul_smul, smul_smul]
      exact congrArg (fun (s : ℝ) => s • v)
        (show (c * hh2 / a) * a = c * hh2 from by field_simp)
    have hdisp1 : b • w1 = (b * (r1 * Real.cos psi)) • e1
        + (b * (r1 * Real.sin psi)) • e2 + b • (hh1 • v) := by
      rw [hs1, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    have hdisp2 : c • w2 = (c * (r2 * Real.cos (psi + azim 0 v w1 w2))) • e1
        + (c * (r2 * Real.sin (psi + azim 0 v w1 w2))) • e2 + c • (hh2 • v) := by
      conv_lhs => rw [hs2]
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    refine ⟨psi, b * r1, c * r2, ?_, ?_, ?_, ?_⟩
    · rw [show ((b • w1 : V3) - 0) = b • w1 from by rw [sub_zero], hdisp1, hb1,
        mul_assoc b r1 (Real.cos psi), mul_assoc b r1 (Real.sin psi)]
    · rw [show ((c • w2 : V3) - 0) = c • w2 from by rw [sub_zero], hdisp2, hb2,
        mul_assoc c r2 (Real.cos (psi + azim 0 v w1 w2)),
        mul_assoc c r2 (Real.sin (psi + azim 0 v w1 w2))]
    · exact mul_pos hb (hr1 hcol.1)
    · exact mul_pos hc (hr2 hcol.2)

/- The `AZIM_SPECIAL_SCALE` / `AZIM_SCALE_ALL` gap recorded in the NEEDS
markers above is closed by `w5cC_azim_scale` (lane scsgeneric-w5cC); the
transfers `WW_DEFOR_rho_node1_p31` / `WW_DEFOR_APHA_p31` plus this lemma are
the ready ingredients for `WW_DEFOR_AZIM_p31`. -/


/-- `azim` is congruent in its three ray arguments. -/
theorem w5cC2_azim_congr {x x' y y' z z' : V3} (hx : x = x') (hy : y = y')
    (hz : z = z') : azim 0 x y z = azim 0 x' y' z' := by
  rw [hx, hy, hz]

/-! ## Bridge kit: LA1 `LocalFan` → LA5 `localFan_p2` -/


theorem w5cC_WW_DEFOR_AZIM {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (h : ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2) (ht : t < 1) :
    azim 0 (wwDefor_p31 v v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
        (wwDefor_p31 v v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 v v t) ∈
        (fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  have hpos : 0 < 1 - t := by linarith
  have hvv : wwDefor_p31 v v t = (1 - t) • v := by simp [wwDefor_apply_p31]
  have key := w5cC2_azim_congr (x := wwDefor_p31 v v t) (x' := (1 - t) • v)
    (y := rhoNode1 ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
      (wwDefor_p31 v v t))
    (y' := rhoNode1 FF v)
    (z := Classical.epsilon fun a => (a, wwDefor_p31 v v t) ∈
      (fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
    (z' := Classical.epsilon fun a => (a, v) ∈ FF)
    hvv (WW_DEFOR_rho_node1_p31 h) (WW_DEFOR_APHA_p31 h)
  rw [key]
  simpa using w5cC_azim_scale (a := 1 - t) (b := 1) (c := 1) hpos one_pos one_pos

theorem w5cC_GENEIRC_WW_DEFOR_AZIM {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hv : v ∈ V) (hg : Generic V E) (ht : t < 1) :
    azim 0 (wwDefor_p31 v v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
        (wwDefor_p31 v v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 v v t) ∈
        (fun uv => (wwDefor_p31 v uv.1 t, wwDefor_p31 v uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  by_cases h0 : t = 0
  · subst h0
    have himg : (fun uv => (wwDefor_p31 v uv.1 (0:ℝ), wwDefor_p31 v uv.2 (0:ℝ))) '' FF = FF := by
      have hF : (fun uv => (wwDefor_p31 v uv.1 (0:ℝ), wwDefor_p31 v uv.2 (0:ℝ))) = id := by
        funext uv
        simp [WW_DEFOR_0_ID_p31]
      rw [hF, Set.image_id]
    rw [himg, WW_DEFOR_0_ID_p31 v v]
  · exact w5cC_WW_DEFOR_AZIM
      (w5cC_GENERIC_HYPOTHESIS_WW_DEFOR hlf h0 hv hg) ht


/-! ## The azimuth transfer family -/

theorem w5cC_GENERIC_WW_DEFOR_RHO_NODE1 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hw : (w1, v) ∈ FF)
    (ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = rhoNode1 FF v := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hwV : w1 ∈ V := (LOCAL_FAN_IMP_IN_V2 h2 hw).1
  have hvV : v ∈ V := (LOCAL_FAN_IMP_IN_V2 h2 hw).2
  have hne : v ≠ w1 := fun hh => LOCAL_FAN_IN_FF_DISTINCT h2 hw hh.symm
  have hgen := w5cC_generic_hyp_offbase hlf hg ht hwV
  have hrv : rhoNode1_p2 FF v ≠ w1 := by
    intro hcon
    have hd : (v, w1) ∈ FF := by
      rw [← hcon]
      exact (LOCAL_FAN_RHO_NODE_PROS h2).1 v hvV
    exact w5cC_no2cycle hlf hd hw
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
  have hkey : ∀ u, (v, u) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      (v, u) ∈ FF := by
    intro u
    constructor
    · rintro ⟨x, hx, hpair⟩
      have hinj := hpair
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨hxa, hxb⟩ := hinj
      have hxv : x.1 = v := by
        by_cases hxw1 : x.1 = w1
        · rw [hxw1, wwDefor_apply_p31, if_pos rfl] at hxa
          exact (hgen v hvV hxa).elim
        · rw [wwDefor_apply_p31, if_neg hxw1] at hxa
          exact hxa
      by_cases hxw2 : x.2 = w1
      · have hd0 : (x.1, x.2) ∈ FF := hx
        rw [hxv, hxw2] at hd0
        exact absurd hd0 (fun hd' => w5cC_no2cycle hlf hd' hw)
      · rw [wwDefor_apply_p31, if_neg hxw2] at hxb
        have hd0 : (x.1, x.2) ∈ FF := hx
        rw [hxv] at hd0
        rw [← hxb]
        exact hd0
    · intro hmem
      have hru : rhoNode1_p2 FF v = u := DETER_RHO_NODE h2 hmem
      rw [← hru] at hmem
      refine ⟨(v, rhoNode1_p2 FF v), hmem, ?_⟩
      simp only [wwDefor_apply_p31]
      rw [if_neg hne, if_neg hrv, hru]
  rw [hvw']
  exact epsilon_ext_p31 hkey

theorem w5cC_WW_DEFOR_ALPHA3 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hw : (w1, v) ∈ FF)
    (ht : t ≠ 0) :
    (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = (1 - t) • w1 := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hvV : v ∈ V := (LOCAL_FAN_IMP_IN_V2 h2 hw).2
  have hne : v ≠ w1 := fun hh => LOCAL_FAN_IN_FF_DISTINCT h2 hw hh.symm
  have hgen := w5cC_generic_hyp_offbase hlf hg ht ((LOCAL_FAN_IMP_IN_V2 h2 hw).1)
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
  have hc : (1 - t) • w1 ≠ v := hgen v hvV
  have hkey : ∀ a, (a, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      a = (1 - t) • w1 := by
    intro a
    constructor
    · rintro ⟨x, hx, hpair⟩
      have hinj := hpair
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨hxa, hxb⟩ := hinj
      rw [hvw'] at hxb
      by_cases hyw : x.2 = w1
      · rw [hyw, wwDefor_apply_p31, if_pos rfl] at hxb
        exact (hc hxb).elim
      · rw [wwDefor_apply_p31, if_neg hyw] at hxb
        have hd0 : (x.1, x.2) ∈ FF := hx
        rw [hxb] at hd0
        have hd : (x.1, v) ∈ FF := hd0
        have hivs : ivsRhoNode1_p2 FF v = x.1 := PRE_IVS_RHO_NODE1_DETE h2 hd
        have hw1 : ivsRhoNode1_p2 FF v = w1 := PRE_IVS_RHO_NODE1_DETE h2 hw
        rw [hw1] at hivs
        rw [show x.1 = w1 from hivs.symm, wwDefor_apply_p31, if_pos rfl] at hxa
        exact hxa.symm
    · intro hae
      refine ⟨(w1, v), hw, ?_⟩
      have h1 : wwDefor_p31 w1 w1 t = (1 - t) • w1 := by simp [wwDefor_apply_p31]
      have h2 : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
      show (wwDefor_p31 w1 w1 t, wwDefor_p31 w1 v t) = (a, wwDefor_p31 w1 v t)
      rw [h1, h2, hae]
  refine (hkey (Classical.epsilon
    (fun a => (a, wwDefor_p31 w1 v t) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)))).mp ?_
  exact Classical.epsilon_spec (p := fun a => (a, wwDefor_p31 w1 v t) ∈
    ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF))
    ⟨(1 - t) • w1, (hkey _).mpr rfl⟩

theorem w5cC_GENERIC_WW_DEFOR_RHO_NODE2 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hv : (v, w1) ∈ FF)
    (ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = (1 - t) • w1 := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hvV : v ∈ V := (LOCAL_FAN_IMP_IN_V2 h2 hv).1
  have hne : v ≠ w1 := fun hh => LOCAL_FAN_IN_FF_DISTINCT h2 hv hh
  have hgen := w5cC_generic_hyp_offbase hlf hg ht ((LOCAL_FAN_IMP_IN_V2 h2 hv).2)
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
  have hkey : ∀ u, (v, u) ∈
      ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
      u = (1 - t) • w1 := by
    intro u
    constructor
    · rintro ⟨x, hx, hpair⟩
      have hinj := hpair
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨hxa, hxb⟩ := hinj
      have hxv : x.1 = v := by
        by_cases hxw1 : x.1 = w1
        · rw [hxw1, wwDefor_apply_p31, if_pos rfl] at hxa
          exact (hgen v hvV hxa).elim
        · rw [wwDefor_apply_p31, if_neg hxw1] at hxa
          exact hxa
      have hd0 : (x.1, x.2) ∈ FF := hx
      rw [hxv] at hd0
      have hru : rhoNode1_p2 FF v = x.2 := DETER_RHO_NODE h2 hd0
      have hrw : rhoNode1_p2 FF v = w1 := DETER_RHO_NODE h2 hv
      rw [hrw] at hru
      rw [← hru] at hxb
      rw [wwDefor_apply_p31, if_pos rfl] at hxb
      exact hxb.symm
    · intro hae
      refine ⟨(v, w1), hv, ?_⟩
      have h1 : wwDefor_p31 w1 w1 t = (1 - t) • w1 := by simp [wwDefor_apply_p31]
      have h2 : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
      show (wwDefor_p31 w1 v t, wwDefor_p31 w1 w1 t) = (v, u)
      rw [h1, h2, hae]
  rw [hvw']
  refine (hkey (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
    v)).mp ?_
  exact Classical.epsilon_spec (p := fun a => (v, a) ∈
    ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF))
    ⟨(1 - t) • w1, (hkey _).mpr rfl⟩

/-! ## The three edge-case azimuth transfers -/

theorem w5cC_AZIM_DEFOR_EDGE1 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hw : (w1, v) ∈ FF)
    (ht : t < 1) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hne : v ≠ w1 := fun hh => LOCAL_FAN_IN_FF_DISTINCT h2 hw hh.symm
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
  have hivs : ivsRhoNode1_p2 FF v = w1 := PRE_IVS_RHO_NODE1_DETE h2 hw
  by_cases h0 : t = 0
  · subst h0
    have himg : (fun uv => (wwDefor_p31 w1 uv.1 (0:ℝ), wwDefor_p31 w1 uv.2 (0:ℝ))) '' FF = FF := by
      have hF : (fun uv => (wwDefor_p31 w1 uv.1 (0:ℝ), wwDefor_p31 w1 uv.2 (0:ℝ))) = id := by
        funext uv
        simp [WW_DEFOR_0_ID_p31]
      rw [hF, Set.image_id]
    rw [himg, WW_DEFOR_0_ID_p31 w1 v]
  · have hpos : 0 < 1 - t := by linarith
    have key := w5cC2_azim_congr (x := wwDefor_p31 w1 v t) (x' := v)
      (y := rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (y' := rhoNode1 FF v)
      (z := Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      (z' := (1 - t) • w1)
      hvw' (w5cC_GENERIC_WW_DEFOR_RHO_NODE1 hlf hg hw h0)
      (w5cC_WW_DEFOR_ALPHA3 hlf hg hw h0)
    rw [key, show (Classical.epsilon fun a => (a, v) ∈ FF) = w1 from hivs]
    simpa using w5cC_azim_scale (a := 1) (b := 1) (c := 1 - t) one_pos one_pos hpos

theorem w5cC_AZIM_DEFOR_EDGE2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hv : (v, w1) ∈ FF)
    (ht : t < 1) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  have hne : v ≠ w1 := fun hh => LOCAL_FAN_IN_FF_DISTINCT h2 hv hh
  have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hne]
  have hrw : rhoNode1_p2 FF v = w1 := DETER_RHO_NODE h2 hv
  by_cases h0 : t = 0
  · subst h0
    have himg : (fun uv => (wwDefor_p31 w1 uv.1 (0:ℝ), wwDefor_p31 w1 uv.2 (0:ℝ))) '' FF = FF := by
      have hF : (fun uv => (wwDefor_p31 w1 uv.1 (0:ℝ), wwDefor_p31 w1 uv.2 (0:ℝ))) = id := by
        funext uv
        simp [WW_DEFOR_0_ID_p31]
      rw [hF, Set.image_id]
    rw [himg, WW_DEFOR_0_ID_p31 w1 v]
  · have hpos : 0 < 1 - t := by linarith
    have key := w5cC2_azim_congr (x := wwDefor_p31 w1 v t) (x' := v)
      (y := rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (y' := (1 - t) • w1)
      (z := Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      (z' := Classical.epsilon fun a => (a, v) ∈ FF)
      hvw' (w5cC_GENERIC_WW_DEFOR_RHO_NODE2 hlf hg hv h0)
      (WW_DEFOR_RHO_NODE2_p31 hlf hg hv h0)
    rw [key, show rhoNode1 FF v = w1 from hrw]
    simpa using w5cC_azim_scale (a := 1) (b := 1 - t) (c := 1) one_pos hpos one_pos

theorem w5cC_AZIM_DEFOR_EDGE3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (hlf : LocalFan V E FF) (hg : Generic V E) (hned : v ≠ w1)
    (hwv : (w1, v) ∉ FF) (hvw : (v, w1) ∉ FF)
    (hvV : v ∈ V) (hw1V : w1 ∈ V) :
    azim 0 (wwDefor_p31 w1 v t)
      (rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t))
      (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = azim 0 v (rhoNode1 FF v)
        (Classical.epsilon fun a => (a, v) ∈ FF) := by
  have h2 := w5cC_lf2_of_LocalFan hlf
  by_cases h0 : t = 0
  · subst h0
    have himg : (fun uv => (wwDefor_p31 w1 uv.1 (0:ℝ), wwDefor_p31 w1 uv.2 (0:ℝ))) '' FF = FF := by
      have hF : (fun uv => (wwDefor_p31 w1 uv.1 (0:ℝ), wwDefor_p31 w1 uv.2 (0:ℝ))) = id := by
        funext uv
        simp [WW_DEFOR_0_ID_p31]
      rw [hF, Set.image_id]
    rw [himg, WW_DEFOR_0_ID_p31 w1 v]
  · have hgen := w5cC_generic_hyp_offbase hlf hg h0 hw1V
    have hvw' : wwDefor_p31 w1 v t = v := by simp [wwDefor_apply_p31, hned]
    have hkey1 : ∀ u, (v, u) ∈
        ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
        (v, u) ∈ FF := by
      intro u
      constructor
      · rintro ⟨x, hx, hpair⟩
        have hinj := hpair
        simp only [Prod.mk.injEq] at hinj
        obtain ⟨hxa, hxb⟩ := hinj
        have hxv : x.1 = v := by
          by_cases hxw1 : x.1 = w1
          · rw [hxw1, wwDefor_apply_p31, if_pos rfl] at hxa
            exact (hgen v hvV hxa).elim
          · rw [wwDefor_apply_p31, if_neg hxw1] at hxa
            exact hxa
        by_cases hxw2 : x.2 = w1
        · exact (hvw (by rw [← hxv, ← hxw2]; simpa using hx)).elim
        · rw [wwDefor_apply_p31, if_neg hxw2] at hxb
          rw [← hxb, ← hxv]
          simpa using hx
      · intro hmem
        have hru : rhoNode1_p2 FF v = u := DETER_RHO_NODE h2 hmem
        rw [← hru] at hmem
        have hrne : rhoNode1_p2 FF v ≠ w1 := by
          intro hcon
          exact hvw (by rw [← hcon]; exact (LOCAL_FAN_RHO_NODE_PROS h2).1 v hvV)
        refine ⟨(v, rhoNode1_p2 FF v), hmem, ?_⟩
        simp only [wwDefor_apply_p31]
        rw [if_neg hned, if_neg hrne, hru]
    have hkey2 : ∀ a, (a, wwDefor_p31 w1 v t) ∈
        ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
        (a, v) ∈ FF := by
      intro a
      constructor
      · rintro ⟨x, hx, hpair⟩
        have hinj := hpair
        simp only [Prod.mk.injEq] at hinj
        obtain ⟨hxa, hxb⟩ := hinj
        rw [hvw'] at hxb
        by_cases hyw : x.2 = w1
        · rw [hyw, wwDefor_apply_p31, if_pos rfl] at hxb
          exact (hgen v hvV hxb).elim
        · rw [wwDefor_apply_p31, if_neg hyw] at hxb
          have hxv2 : x.1 ≠ w1 := by
            intro hxx
            exact hwv (by
              have hx' : (x.1, x.2) ∈ FF := by simpa using hx
              rw [hxx, hxb] at hx'
              exact hx')
          rw [wwDefor_apply_p31, if_neg hxv2] at hxa
          rw [← hxa, ← hxb]
          simpa using hx
      · intro hmem
        have haw : a ≠ w1 := by
          intro hcon
          rw [hcon] at hmem
          exact hwv hmem
        refine ⟨(a, v), hmem, ?_⟩
        simp only [wwDefor_apply_p31, if_neg haw, if_neg hned]
    have hkey1' : ∀ a, (wwDefor_p31 w1 v t, a) ∈
        ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF) ↔
        (v, a) ∈ FF := by
      intro a; rw [hvw']; exact hkey1 a
    exact w5cC2_azim_congr hvw' (epsilon_ext_p31 hkey1') (epsilon_ext_p31 hkey2)


/-! ## Section 8: genericity hypothesis and the azimuth transfer -/

/-- HOL `GENERIC_HYPOTHESIS_WW_DEFOR` (ODXLSTC.hl:973): under `local_fan` +
genericity the deformed base point `(1 - t) % v` misses every dart end. -/
theorem GENERIC_HYPOTHESIS_WW_DEFOR_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_ht : t ≠ 0) (_hv : v ∈ V) (_hg : Generic V E) :
    ∀ x ∈ FF, x.1 ≠ x.2 ∧ (1 - t) • v ≠ x.1 ∧ (1 - t) • v ≠ x.2 := by
  exact w5cC_GENERIC_HYPOTHESIS_WW_DEFOR _hlf _ht _hv _hg

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
  exact w5cC_WW_DEFOR_AZIM h ht

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
  exact w5cC_GENEIRC_WW_DEFOR_AZIM _hlf _hv _hg _ht

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
  exact w5cC_AZIM_DEFOR_EDGE1 _hlf _hg _hw _ht

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
  exact w5cC_AZIM_DEFOR_EDGE2 _hlf _hg _hv _ht

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
  exact w5cC_AZIM_DEFOR_EDGE3 _hlf _hg _hv _hwv _hvw _hvV _hw1V

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
  -- DISCHARGES (la31-tower-w1 2026-11-05): source ODXLSTC.hl:1758-1957.
  -- Route (identical to the LA34 `V3_DEFOR` twin): the `BBs_v39` disjunct
  -- gives `ConvexLocalFan`; `JKQEWGV2_p23` kills `Circular`; `CIZMRRH`
  -- (via the `localFan_p3.of_LocalFan` / `hno_of_no_isolated` bridge) gives
  -- the generic/circular/lunar trichotomy; the generic branch is the
  -- `hz` (ZLZTHIC) arrow applied to `wwDefor (w l)` with the interior-angle
  -- transfer `AZIM_DEFORMATION_GENERIC_p31`, the lunar branch is the `hm`
  -- (MHAEYJN) arrow with `JKQEWGV3_p23` for the `< pi` bound and
  -- `WW_DEFOR_AFFINE_HULL_p31` for the hull pin; both branches rewrite the
  -- images with `V_/E_/F_DEFORMATION_WW_DEFOR_p31`.
  intro s k l w his hmm hk hk3 hdiag hnorm hlt hJ hlunar
  set w1 : V3 := w l with hw1
  set V : Set V3 := Set.range w with hV
  set E : Set (Set V3) := Set.range (fun i => {w i, w (i + 1)}) with hE
  set FF : Set (V3 × V3) := Set.range (fun i => (w i, w (i + 1))) with hFF
  have hbb : BBsV39 s w := ((hmm.1).1).1
  have hta : taustarV39 s w < 0 := ((hmm.1).1).2.2
  have hsk : ¬ s.k ≤ 3 := by omega
  have hw1V : w1 ∈ V := by rw [hV, hw1]; exact ⟨l, rfl⟩
  have hcirc : ¬ Circular V E := by
    have h := JKQEWGV2_p23 s w his (by omega) hbb hta
    simpa only [← hV, ← hE, Set.image_univ] using h
  have hclf : ConvexLocalFan V E FF := by
    rcases hbb.2.2.2 with h3 | hcf
    · exact absurd h3 hsk
    · simpa only [← hV, ← hE, ← hFF] using hcf
  -- the generic/circular/lunar trichotomy of a local fan
  have hlf : LocalFan V E FF := hclf.1
  have hno : dartsOfHyp_p3 E V = Fan.dart1OfFan V E :=
    hno_of_no_isolated (w5cC_hedge_of_LocalFan hlf)
  have hlf3 : localFan_p3 V E FF := localFan_p3.of_LocalFan hlf hno
  have htri := CIZMRRH hlf3
  -- the deformation, restricted to the half window used by the HOL proof
  have hdef1 : Deformation (wwDefor_p31 w1) V (-1) 1 :=
    WW_DEFOR_DEFORMATION_p31 w1 1 V one_pos
  have hdefh : Deformation (wwDefor_p31 w1) V (-(1 / 2)) (1 / 2) := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, hdef1.2.2⟩
    intro v hv r hr
    exact hdef1.2.1 v hv r ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hfixh : ∀ u' ∈ V, w1 ≠ u' → ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      wwDefor_p31 w1 u' t = u' := by
    intro u' _ hu' t _ht
    rw [wwDefor_apply_p31, if_neg]
    exact fun h => hu' h.symm
  rcases htri with hgen | hcirc3 | hlun3
  · -- (1) generic: the ZLZTHIC arrow applies
    have hgen0 : Generic V E := by simpa only [generic_p3, Generic] using hgen.1
    have hang1 : ∀ v ∈ V, ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
        interiorAngle1 0 FF v = Real.pi →
        interiorAngle1 0 ((fun d : V3 × V3 =>
          (wwDefor_p31 w1 d.1 t, wwDefor_p31 w1 d.2 t)) '' FF)
          (wwDefor_p31 w1 v t) ≤ Real.pi := by
      intro v hv t ht hpi
      have hIA : interiorAngle1 0 ((fun d : V3 × V3 =>
          (wwDefor_p31 w1 d.1 t, wwDefor_p31 w1 d.2 t)) '' FF) (wwDefor_p31 w1 v t)
          = interiorAngle1 0 FF v :=
        AZIM_DEFORMATION_GENERIC_p31 (V := V) (E := E) (FF := FF) hlf hgen0 hv hw1V
          (by linarith [ht.2])
      rw [hIA, hpi]
    obtain ⟨eZ, heZ, hZ⟩ := hz (-(1 / 2)) (1 / 2) V E FF (wwDefor_p31 w1)
      hclf hgen0 hdefh hang1
    have hpos : 0 < min eZ (1 / 2) / 2 := by
      have h2 : 0 < min eZ (1 / 2) := lt_min heZ (by norm_num)
      linarith
    refine ⟨min eZ (1 / 2) / 2, hpos, ?_⟩
    intro t ht1 ht2
    have hle : min eZ (1 / 2) ≤ eZ := min_le_left _ _
    have hz1 : -eZ < t := by nlinarith
    have hz2 : t < eZ := by nlinarith
    have h := (hZ t hz1 hz2).1
    rw [hV, hE, hFF, V_DEFORMATION_WW_DEFOR_p31 w1 w t,
      ← E_DEFORMATION_WW_DEFOR_p31 w1 w t,
      ← F_DEFORMATION_WW_DEFOR_p31 w1 w t] at h
    exact h
  · -- (2) circular: excluded by JKQEWGV2
    exact absurd (by simpa only [circular_p3, Circular] using hcirc3.1) hcirc
  · -- (3) lunar: the MHAEYJN arrow applies
    obtain ⟨v, w', hlun3'⟩ := hlun3.1
    have hlun : Lunar v w' V E := by
      simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hlun3'
    have hlun_comm : Lunar w' v V E := by
      obtain ⟨hnc, hsub, hne, hcol⟩ := hlun
      exact ⟨hnc, by simpa only [Set.pair_comm] using hsub, hne.symm,
        by simpa only [Set.pair_comm] using hcol⟩
    have hang_lt : interiorAngle1 0 FF v < Real.pi := by
      have h := JKQEWGV3_p23 s w v w' his hbb (by omega) hta
        (by simpa only [← hV, ← hE, Set.image_univ] using hlun)
      have h2 : interiorAngle1 0 FF v < Real.pi / 2 := by
        simpa only [← hFF, Set.image_univ] using h
      linarith [Real.pi_pos]
    have hw1ne_v : w1 ≠ v := by
      intro heq
      exact hlunar V E w' rfl rfl (heq ▸ hlun_comm)
    have hw1ne_w' : w1 ≠ w' := by
      intro heq
      exact hlunar V E v rfl rfl (heq ▸ hlun)
    have haffine : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
        wwDefor_p31 w1 w1 t ∈ affineSpan ℝ ({0, v, w', w1} : Set V3) := by
      intro t ht
      exact WW_DEFOR_AFFINE_HULL_p31 w1 v w' (1 / 2) t ht
    obtain ⟨eM, heM, hM⟩ := _hm (-(1 / 2)) (1 / 2) V E FF (wwDefor_p31 w1) v w' w1
      hclf hlun hdefh hang_lt hw1V hw1ne_v hw1ne_w' hfixh haffine
    have hpos : 0 < min eM (1 / 2) / 2 := by
      have h2 : 0 < min eM (1 / 2) := lt_min heM (by norm_num)
      linarith
    refine ⟨min eM (1 / 2) / 2, hpos, ?_⟩
    intro t ht1 ht2
    have hle : min eM (1 / 2) ≤ eM := min_le_left _ _
    have hm1 : -eM < t := by nlinarith
    have hm2 : t < eM := by nlinarith
    have h := (hM t hm1 hm2).1
    rw [hV, hE, hFF, V_DEFORMATION_WW_DEFOR_p31 w1 w t,
      ← E_DEFORMATION_WW_DEFOR_p31 w1 w t,
      ← F_DEFORMATION_WW_DEFOR_p31 w1 w t] at h
    exact h

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

/-- Counting core: the dart range of a periodic, residue-injective family has
exactly `k` points (the same counting method as `CARD_V_EQ_SCS_K1_p31`,
applied to the dart map). -/
private theorem dartRange_ncard_p31 {k : ℕ} (hk0 : 0 < k) (f : ℕ → V3)
    (hper : ∀ a, f (a % k) = f a)
    (hinj : ∀ a b, a < k → b < k → a ≠ b → (f a, f (a + 1)) ≠ (f b, f (b + 1))) :
    (Set.range (fun i => (f i, f (i + 1)))).ncard = k := by
  have hpm1 : ∀ n, f (n % k) = f n := hper
  have hpm2 : ∀ n, f (n % k + 1) = f (n + 1) := by
    intro n
    have h1 : (n % k + 1) % k = (n + 1) % k := Nat.mod_add_mod n k 1
    rw [← hper (n % k + 1), h1, hper (n + 1)]
  have hV : Set.range (fun i => (f i, f (i + 1)))
      = (fun i => (f i, f (i + 1))) '' {i | i < k} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a % k, Nat.mod_lt a hk0, ?_⟩
      dsimp only
      rw [hpm1 a, hpm2 a]
    · rintro ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
  have hco : {i | i < k} = ((Finset.range k : Finset ℕ) : Set ℕ) :=
    (Finset.coe_range k).symm
  rw [hV, hco, ← Finset.coe_image, Set.ncard_coe_finset, Finset.card_image_of_injOn,
    Finset.card_range]
  intro a ha b hb heq
  by_contra hne
  rw [Finset.mem_coe, Finset.mem_range] at ha hb
  exact hinj a b ha hb hne heq

/-- HOL `CARD_FF_EQ_WW_DEFORMATION` (ODXLSTC.hl:2089). DISCHARGED (shim): the
HOL route (`LOFA_IMP_CARD_FF_V_EQ`, local-fan kit) is replaced by direct
counting — both dart ranges have `ncard = k` by `dartRange_ncard_p31`. The
original family is residue-injective by `VV_INJ_p31`; for the deformed family
the shrink at `w l` is handled dart-by-dart: if a deformed head/tail lands on
`(1 - t) % w l` its residue is `l % k`, and the two head/tail equations force
`a = b` unless `k ∤ 2` is violated (excluded by `3 < k`). -/
theorem CARD_FF_EQ_WW_DEFORMATION_p31 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (e1 : ℝ)
    (hk : s.k = k) (his : isScsV39 s) (_hk3 : 3 < k) (hbb : BBsV39 s w)
    (_hbb' : ∀ t, 0 < t → t < e1 → BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t)) :
    ∀ t, 0 < t → t < e1 →
      (Set.range (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))).ncard
        = (Set.range (fun i => (w i, w (i + 1)))).ncard := by
  intro t _ht _hte
  have hper : Periodic w s.k := hbb.2.1
  have pm : ∀ a, w (a % k) = w a := by
    intro a
    have hm := periodic_mod_p18 hper a
    rwa [hk] at hm
  have hinj : ∀ a b, a < k → b < k → a ≠ b → w a ≠ w b :=
    fun a b ha hb hab => VV_INJ_p31 s k w hk his hbb a b ⟨ha, hb, hab⟩
  have horig := dartRange_ncard_p31 (by omega) (fun i => w i) pm
    (fun a b ha hb hab heq => hinj a b ha hb hab (congrArg Prod.fst heq))
  set me := l % k with hme
  set c := (1 - t) • w l with hc
  have hmeK : me < k := Nat.mod_lt l (by omega)
  have hwme : w me = w l := by rw [hme, pm l]
  have hwil : ∀ i, i < k → (w i = w l ↔ i = me) := by
    intro i hi
    constructor
    · intro hh
      by_contra hne
      exact hinj i me hi hmeK hne (hh.trans hwme.symm)
    · intro hh
      rw [hh]
      exact hwme
  have hA : ∀ i, i < k → wwDefor_p31 (w l) (w i) t = if i = me then c else w i := by
    intro i hi
    rw [wwDefor_apply_p31]
    by_cases h : w i = w l
    · rw [if_pos h, if_pos ((hwil i hi).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hwil i hi).mpr hh))]
  have hF2 : ∀ n, wwDefor_p31 (w l) (w (n % k)) t = wwDefor_p31 (w l) (w n) t :=
    fun n => by rw [pm n]
  have hsucc_eq : ∀ x y, x < k → y < k → (x + 1) % k = (y + 1) % k → x = y := by
    intro x y hx hy heq
    have hmod : x % k = y % k := Nat.ModEq.add_right_cancel' 1 heq
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
    exact hmod
  have hsucc_ne : ∀ m, m < k → (m + 1) % k ≠ m := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have h1 : m + 1 = k := by omega
      rw [h1, Nat.mod_self]
      omega
  have htwo_ne : ∀ m, m < k → (m + 2) % k ≠ m := by
    intro m hm
    rcases Nat.lt_or_ge (m + 2) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have h3 : m + 2 - k < k := by omega
      have he : m + 2 = m + 2 - k + k := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt h3]
      omega
  -- the deformed dart map is injective on the residues
  have hfinj : ∀ a b, a < k → b < k → a ≠ b →
      (wwDefor_p31 (w l) (w a) t, wwDefor_p31 (w l) (w (a + 1)) t) ≠
        (wwDefor_p31 (w l) (w b) t, wwDefor_p31 (w l) (w (b + 1)) t) := by
    intro a b ha hb hab hne
    have heq : (wwDefor_p31 (w l) (w a) t, wwDefor_p31 (w l) (w (a + 1)) t)
        = (wwDefor_p31 (w l) (w b) t, wwDefor_p31 (w l) (w (b + 1)) t) := hne
    rw [Prod.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    have ha' : (a + 1) % k < k := Nat.mod_lt _ (by omega)
    have hb' : (b + 1) % k < k := Nat.mod_lt _ (by omega)
    have hsa : wwDefor_p31 (w l) (w (a + 1)) t
        = wwDefor_p31 (w l) (w ((a + 1) % k)) t := (hF2 (a + 1)).symm
    have hsb : wwDefor_p31 (w l) (w (b + 1)) t
        = wwDefor_p31 (w l) (w ((b + 1) % k)) t := (hF2 (b + 1)).symm
    rw [hsa, hsb] at he2
    by_cases haml : (a + 1) % k = me
    · -- a's head is the moved point; b's head is not (else a = b)
      have hbml : (b + 1) % k ≠ me := fun hh =>
        hab (hsucc_eq a b ha hb (haml.trans hh.symm))
      have hda' : wwDefor_p31 (w l) (w ((a + 1) % k)) t = c := by
        rw [hA _ ha', if_pos haml]
      have hdb' : wwDefor_p31 (w l) (w ((b + 1) % k)) t = w ((b + 1) % k) := by
        rw [hA _ hb', if_neg hbml]
      rw [hda', hdb'] at he2
      by_cases ham : a = me
      · have hbne : b ≠ me := fun hh => hab (hh ▸ ham)
        have hda : wwDefor_p31 (w l) (w a) t = c := by
          rw [hA a ha, if_pos ham]
        have hdb : wwDefor_p31 (w l) (w b) t = w b := by
          rw [hA b hb, if_neg hbne]
        rw [hda, hdb] at he1
        -- c = w b and c = w b' → w b = w b' → b = b' → contra hsucc_ne
        have hwb : w b = w ((b + 1) % k) := by rw [← he1, ← he2]
        have hbb2 : b = (b + 1) % k := by
          by_contra hne
          exact hinj b _ hb hb' hne hwb
        exact hsucc_ne b hb hbb2.symm
      · have hda : wwDefor_p31 (w l) (w a) t = w a := by
          rw [hA a ha, if_neg ham]
        by_cases hbm : b = me
        · have hdb : wwDefor_p31 (w l) (w b) t = c := by
            rw [hA b hb, if_pos hbm]
          rw [hda, hdb] at he1
          -- w a = c = w b' → if a = b' then (b+2)%k = me, contra htwo_ne
          have hwa : w a = w ((b + 1) % k) := he1.trans he2
          by_cases hab' : a = (b + 1) % k
          · have hkey2 : me = (b + 2) % k := by
              rw [← haml, hab', Nat.mod_add_mod (b + 1) k 1]
            exact htwo_ne me hmeK (by rw [hbm] at hkey2; exact hkey2.symm)
          · exact hinj a _ ha hb' hab' hwa
        · have hdb : wwDefor_p31 (w l) (w b) t = w b := by
            rw [hA b hb, if_neg hbm]
          rw [hda, hdb] at he1
          exact hinj a b ha hb hab he1
    · by_cases hbml : (b + 1) % k = me
      · -- b's head is the moved point; then b = me is impossible outright
        have hbm0 : b ≠ me := by
          intro hh
          exact hsucc_ne b hb (hbml.trans hh.symm)
        have hdb' : wwDefor_p31 (w l) (w ((b + 1) % k)) t = c := by
          rw [hA _ hb', if_pos hbml]
        have hda' : wwDefor_p31 (w l) (w ((a + 1) % k)) t = w ((a + 1) % k) := by
          rw [hA _ ha', if_neg haml]
        rw [hda', hdb'] at he2
        have hdb : wwDefor_p31 (w l) (w b) t = w b := by
          rw [hA b hb, if_neg hbm0]
        rw [hdb] at he1
        by_cases ham : a = me
        · have hda : wwDefor_p31 (w l) (w a) t = c := by
            rw [hA a ha, if_pos ham]
          rw [hda] at he1
          -- w b = c = w a' → b = a' → (b+1)%k = (me+2)%k ≠ me, contra
          have hwb : w b = w ((a + 1) % k) := by rw [← he1, ← he2]
          by_cases hba : b = (a + 1) % k
          · have hkey : (b + 1) % k = (me + 2) % k := by
              have h2 : (b + 1) % k = ((a + 1) % k + 1) % k := by rw [hba]
              rw [h2, Nat.mod_add_mod (a + 1) k 1]
              rw [show a + 1 + 1 = me + 2 from by rw [ham]]
            exact htwo_ne me hmeK (hkey.symm.trans hbml)
          · exact hinj b _ hb ha' hba hwb
        · have hda : wwDefor_p31 (w l) (w a) t = w a := by
            rw [hA a ha, if_neg ham]
          rw [hda] at he1
          exact hinj a b ha hb hab he1
      · rw [hA _ ha', hA _ hb', if_neg haml, if_neg hbml] at he2
        by_cases hab' : (a + 1) % k = (b + 1) % k
        · exact hab (hsucc_eq a b ha hb hab')
        · exact hinj _ _ ha' hb' hab' he2
  have hdef := dartRange_ncard_p31 (by omega)
    (fun i => wwDefor_p31 (w l) (w i) t) (fun a => by rw [pm a]) hfinj
  rw [hdef, horig]

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

/-- Proof twin of `INTERIOR_ANGLE_SAME_WW_DEFOR0_p31` (HOL ODXLSTC.hl:2264). -/
theorem w5cC_INTERIOR_ANGLE_SAME_WW_DEFOR0 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (t : ℝ) (FF : Set (V3 × V3))
    (hk3 : 3 < k) (his : isScsV39 s) (hk : s.k = k) (hbb : BBsV39 s w)
    (hbb' : BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t))
    (hFF : Set.range (fun i => (w i, w (i + 1))) = FF) (ht : t < 1) :
    interiorAngle1 0
      (Set.range (fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t)))
      (wwDefor_p31 (w l) (w (l % k)) t)
      = interiorAngle1 0 FF (w (l % k)) := by
  have hk3' : ¬ (k ≤ 3) := by omega
  have hk1 : 1 < k := by omega
  have hper : Periodic w k := by rw [← hk]; exact hbb.2.1
  have hpl : l % k < k := Nat.mod_lt _ (by omega)
  have hinj := VV_INJ_p31 s k w hk his hbb
  have hwp : w (l % k) = w l := periodic_mod_p18 hper l
  -- the two fans
  have hlf : LocalFan (Set.range w) (Set.range fun i => {w i, w (i + 1)}) FF := by
    have h4 := hbb.2.2.2
    rcases h4 with hle | hc
    · omega
    · rw [← hFF]; exact hc.1
  have h2 : localFan_p2 (Set.range w) (Set.range fun i => {w i, w (i + 1)}) FF :=
    w5cC_lf2_of_LocalFan hlf
  have hlf' : LocalFan (Set.range fun i => wwDefor_p31 (w l) (w i) t)
      (Set.range fun i => {wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t})
      (Set.range fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t)) := by
    have h4 := hbb'.2.2.2
    rcases h4 with hle | hc
    · omega
    · exact hc.1
  have h2' := w5cC_lf2_of_LocalFan hlf'
  have hVn : (Set.range w).ncard = k :=
    CARD_V_EQ_SCS_K1_p31 s k w (Set.range w) hk rfl his hk3 hbb
  have hVn' : (Set.range fun i => wwDefor_p31 (w l) (w i) t).ncard = k :=
    CARD_V_EQ_SCS_K1_p31 s k (fun i => wwDefor_p31 (w l) (w i) t) _ hk rfl his hk3 hbb'
  -- index progression, original fan
  have hstep : ∀ m, (rhoNode1 FF)^[m] (w (l % k)) = w (m + l % k) :=
    VV_SUC_EQ_RHO_NODE_PRIME_p35 (s := s) (k := k) (p1 := l % k) (p := 0) (q := 0)
      (u := w (l % k))
      (V := Set.range w) (E := Set.range fun i => {w i, w (i + 1)}) (FF := FF) (vv := w)
      hk rfl rfl rfl hFF his hk3' hbb
  have hrho : rhoNode1 FF (w (l % k)) = w (1 + l % k) := by
    simpa using hstep 1
  have hivs : ivsRhoNode1 FF (w (l % k)) = w (k - 1 + l % k) := by
    have h := ITER_CARD_MINUS1_EQ_IVS_RN1 h2 (v := w (l % k)) ⟨l % k, rfl⟩
    rw [hVn] at h
    exact h.symm.trans (hstep (k - 1))
  -- index progression, deformed fan
  have hstep' : ∀ m, (rhoNode1
      (Set.range fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t)))^[m]
      (wwDefor_p31 (w l) (w (l % k)) t) = wwDefor_p31 (w l) (w (m + l % k)) t := by
    intro m
    exact VV_SUC_EQ_RHO_NODE_PRIME_p35 (s := s) (k := k) (p1 := l % k) (p := 0) (q := 0)
      (u := wwDefor_p31 (w l) (w (l % k)) t)
      (V := Set.range fun i => wwDefor_p31 (w l) (w i) t)
      (E := Set.range fun i =>
        {wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t})
      (FF := Set.range fun i =>
        (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))
      (vv := fun i => wwDefor_p31 (w l) (w i) t) hk rfl rfl rfl rfl his hk3' hbb' m
  have hrho' : rhoNode1 (Set.range fun i =>
      (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))
      (wwDefor_p31 (w l) (w (l % k)) t) = wwDefor_p31 (w l) (w (1 + l % k)) t := by
    simpa using hstep' 1
  have hivs' : ivsRhoNode1 (Set.range fun i =>
      (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))
      (wwDefor_p31 (w l) (w (l % k)) t) = wwDefor_p31 (w l) (w (k - 1 + l % k)) t := by
    have h := ITER_CARD_MINUS1_EQ_IVS_RN1 h2'
      (v := wwDefor_p31 (w l) (w (l % k)) t) ⟨l % k, rfl⟩
    rw [hVn'] at h
    exact h.symm.trans (hstep' (k - 1))
  have hL : interiorAngle1 0
      (Set.range fun i => (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))
      (wwDefor_p31 (w l) (w (l % k)) t)
      = azim 0 (wwDefor_p31 (w l) (w (l % k)) t)
          (wwDefor_p31 (w l) (w (1 + l % k)) t)
          (wwDefor_p31 (w l) (w (k - 1 + l % k)) t) := by
    show azim 0 (wwDefor_p31 (w l) (w (l % k)) t)
      (rhoNode1 (Set.range fun i =>
        (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))
        (wwDefor_p31 (w l) (w (l % k)) t))
      (ivsRhoNode1 (Set.range fun i =>
        (wwDefor_p31 (w l) (w i) t, wwDefor_p31 (w l) (w (i + 1)) t))
        (wwDefor_p31 (w l) (w (l % k)) t)) = _
    rw [hrho', hivs']
  have hR : interiorAngle1 0 FF (w (l % k))
      = azim 0 (w (l % k)) (w (1 + l % k)) (w (k - 1 + l % k)) := by
    show azim 0 (w (l % k)) (rhoNode1 FF (w (l % k))) (ivsRhoNode1 FF (w (l % k))) = _
    rw [hrho, hivs]
  rw [hL, hR]
  -- the base point is the only scaled one
  have hne1 : w (1 + l % k) ≠ w l := by
    intro hcon
    have h2' : w (l % k + 1) = w (l % k) := by
      rw [Nat.add_comm (1 : ℕ) (l % k)] at hcon
      rw [hcon]; exact hwp.symm
    have h3 : w ((l % k + 1) % k) = w (l % k) :=
      (periodic_mod_p18 hper (l % k + 1)).trans h2'
    have hidx : (l % k + 1) % k = l % k := by
      by_contra hne
      exact hinj ((l % k + 1) % k) (l % k)
        ⟨Nat.mod_lt _ (by omega), hpl, hne⟩ h3
    exact (SUC_MOD_NOT_EQ_p31 hk1 (l % k))
      (by rw [Nat.mod_eq_of_lt hpl, hidx])
  have hne2 : w (k - 1 + l % k) ≠ w l := by
    intro hcon
    have h3 : w ((k - 1 + l % k) % k) = w (l % k) := by
      rw [periodic_mod_p18 hper (k - 1 + l % k), hcon, hwp]
    have hidx : (k - 1 + l % k) % k = l % k := by
      by_contra hne
      exact hinj ((k - 1 + l % k) % k) (l % k)
        ⟨Nat.mod_lt _ (by omega), hpl, hne⟩ h3
    have hmod : (k - 1 + l % k) % k ≠ l % k := by
      rcases Nat.eq_zero_or_pos (l % k) with hp0 | hp1
      · rw [hp0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
        omega
      · have hge : k ≤ k - 1 + l % k := by omega
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
        omega
    exact hmod hidx
  have hA : wwDefor_p31 (w l) (w (l % k)) t = (1 - t) • (w (l % k)) := by
    rw [wwDefor_apply_p31, if_pos hwp, hwp]
  have hB : wwDefor_p31 (w l) (w (1 + l % k)) t = w (1 + l % k) := by
    rw [wwDefor_apply_p31, if_neg hne1]
  have hC : wwDefor_p31 (w l) (w (k - 1 + l % k)) t = w (k - 1 + l % k) := by
    rw [wwDefor_apply_p31, if_neg hne2]
  rw [hA, hB, hC]
  simpa using w5cC_azim_scale (v := w (l % k)) (w1 := w (1 + l % k))
    (w2 := w (k - 1 + l % k)) (a := 1 - t) (b := 1) (c := 1)
    (by linarith) one_pos one_pos

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
  exact w5cC_INTERIOR_ANGLE_SAME_WW_DEFOR0 s k l w t FF _hk3 _his _hk _hbb _hbb' _hFF _ht

/-- `x + p` keeps the residue `p` only when `x = 0` (mod `k`). -/
private theorem w5cC2_mod_shift_ne {k p x : ℕ} (hk : 0 < k) (hp : p < k)
    (hx0 : 0 < x) (hx : x < k) : (x + p) % k ≠ p := by
  rcases Nat.lt_or_ge (x + p) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega

/-- `k - 1 + (x + p)` keeps the residue `p` only when `x = 1` (mod `k`). -/
private theorem w5cC2_mod_pred_ne {k p x : ℕ} (hk : 1 < k) (hp : p < k)
    (hx1 : 1 < x) (hx : x < k) : (k - 1 + (x + p)) % k ≠ p := by
  rcases Nat.lt_or_ge (k - 1 + (x + p)) (2 * k) with hlt | hge
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- `1 + (k - 1 + p)` sits at residue `p`. -/
private theorem w5cC2_mod_succ_eq {k p : ℕ} (hp : p < k) : (1 + (k - 1 + p)) % k = p := by
  have e : 1 + (k - 1 + p) = k + p := by omega
  rw [e, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hp]

/-- `k - 1 + (1 + p)` sits at residue `p`. -/
private theorem w5cC2_mod_pred_eq {k p : ℕ} (hp : p < k) : (k - 1 + (1 + p)) % k = p := by
  have e : k - 1 + (1 + p) = k + p := by omega
  rw [e, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hp]

/-- Proof twin of `INTERIOR_ANGLE_SAME_WW_DEFOR1_p31` (HOL ODXLSTC.hl:2359). -/
theorem w5cC_INTERIOR_ANGLE_SAME_WW_DEFOR1 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (t : ℝ) (FF : Set (V3 × V3))
    (hk3 : 3 < k) (his : isScsV39 s) (hk : s.k = k) (hbb : BBsV39 s w)
    (hbb' : BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t))
    (hFF : Set.range (fun i => (w i, w (i + 1))) = FF) (ht : t < 1)
    (hi1 : 1 ≤ i) (hik : i < k) :
    interiorAngle1 0
      (Set.range (fun j => (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t)))
      ((rhoNode1 (Set.range fun j =>
        (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t)))^[i]
        (wwDefor_p31 (w l) (w (l % k)) t))
      = interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k))) := by
  have hk3' : ¬ (k ≤ 3) := by omega
  have hk1 : 1 < k := by omega
  have hper : Periodic w k := by rw [← hk]; exact hbb.2.1
  have hpl : l % k < k := Nat.mod_lt _ (by omega)
  have hinj := VV_INJ_p31 s k w hk his hbb
  have hwp : w (l % k) = w l := periodic_mod_p18 hper l
  have hlf : LocalFan (Set.range w) (Set.range fun j => {w j, w (j + 1)}) FF := by
    have h4 := hbb.2.2.2
    rcases h4 with hle | hc
    · omega
    · rw [← hFF]; exact hc.1
  have h2 : localFan_p2 (Set.range w) (Set.range fun j => {w j, w (j + 1)}) FF :=
    w5cC_lf2_of_LocalFan hlf
  have hlf' : LocalFan (Set.range fun j => wwDefor_p31 (w l) (w j) t)
      (Set.range fun j => {wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t})
      (Set.range fun j => (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t)) := by
    have h4 := hbb'.2.2.2
    rcases h4 with hle | hc
    · omega
    · exact hc.1
  have h2' := w5cC_lf2_of_LocalFan hlf'
  have hVn : (Set.range w).ncard = k :=
    CARD_V_EQ_SCS_K1_p31 s k w (Set.range w) hk rfl his hk3 hbb
  have hVn' : (Set.range fun j => wwDefor_p31 (w l) (w j) t).ncard = k :=
    CARD_V_EQ_SCS_K1_p31 s k (fun j => wwDefor_p31 (w l) (w j) t) _ hk rfl his hk3 hbb'
  -- orbit from `l % k` (original and deformed)
  have hstep : ∀ m, (rhoNode1 FF)^[m] (w (l % k)) = w (m + l % k) :=
    VV_SUC_EQ_RHO_NODE_PRIME_p35 (s := s) (k := k) (p1 := l % k) (p := 0) (q := 0)
      (u := w (l % k)) (V := Set.range w) (E := Set.range fun j => {w j, w (j + 1)})
      (FF := FF) (vv := w) hk rfl rfl rfl hFF his hk3' hbb
  have hstep' : ∀ m, (rhoNode1
      (Set.range fun j => (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t)))^[m]
      (wwDefor_p31 (w l) (w (l % k)) t) = wwDefor_p31 (w l) (w (m + l % k)) t := by
    intro m
    exact VV_SUC_EQ_RHO_NODE_PRIME_p35 (s := s) (k := k) (p1 := l % k) (p := 0) (q := 0)
      (u := wwDefor_p31 (w l) (w (l % k)) t)
      (V := Set.range fun j => wwDefor_p31 (w l) (w j) t)
      (E := Set.range fun j => {wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t})
      (FF := Set.range fun j =>
        (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
      (vv := fun j => wwDefor_p31 (w l) (w j) t) hk rfl rfl rfl rfl his hk3' hbb' m
  -- orbit restart at `w (i + l % k)`
  have hstep2 : ∀ m, (rhoNode1 FF)^[m] (w (i + l % k)) = w (m + (i + l % k)) :=
    VV_SUC_EQ_RHO_NODE_PRIME_p35 (s := s) (k := k) (p1 := i + l % k) (p := 0) (q := 0)
      (u := w (i + l % k)) (V := Set.range w) (E := Set.range fun j => {w j, w (j + 1)})
      (FF := FF) (vv := w) hk rfl rfl rfl hFF his hk3' hbb
  have hstep2' : ∀ m, (rhoNode1
      (Set.range fun j => (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t)))^[m]
      (wwDefor_p31 (w l) (w (i + l % k)) t)
      = wwDefor_p31 (w l) (w (m + (i + l % k))) t := by
    intro m
    exact VV_SUC_EQ_RHO_NODE_PRIME_p35 (s := s) (k := k) (p1 := i + l % k) (p := 0) (q := 0)
      (u := wwDefor_p31 (w l) (w (i + l % k)) t)
      (V := Set.range fun j => wwDefor_p31 (w l) (w j) t)
      (E := Set.range fun j => {wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t})
      (FF := Set.range fun j =>
        (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
      (vv := fun j => wwDefor_p31 (w l) (w j) t) hk rfl rfl rfl rfl his hk3' hbb' m
  -- transport the iterated base points
  have hb : (rhoNode1 FF)^[i] (w (l % k)) = w (i + l % k) := hstep i
  have hb' : (rhoNode1 (Set.range fun j =>
      (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t)))^[i]
      (wwDefor_p31 (w l) (w (l % k)) t) = wwDefor_p31 (w l) (w (i + l % k)) t := hstep' i
  rw [hb', hb]
  -- angles at the restarted base point
  have hrhoI : rhoNode1 FF (w (i + l % k)) = w (1 + (i + l % k)) := by
    simpa using hstep2 1
  have hivsI : ivsRhoNode1 FF (w (i + l % k)) = w (k - 1 + (i + l % k)) := by
    have h := ITER_CARD_MINUS1_EQ_IVS_RN1 h2 (v := w (i + l % k)) ⟨i + l % k, rfl⟩
    rw [hVn] at h
    exact h.symm.trans (hstep2 (k - 1))
  have hrhoI' : rhoNode1 (Set.range fun j =>
      (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
      (wwDefor_p31 (w l) (w (i + l % k)) t)
      = wwDefor_p31 (w l) (w (1 + (i + l % k))) t := by
    simpa using hstep2' 1
  have hivsI' : ivsRhoNode1 (Set.range fun j =>
      (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
      (wwDefor_p31 (w l) (w (i + l % k)) t)
      = wwDefor_p31 (w l) (w (k - 1 + (i + l % k))) t := by
    have h := ITER_CARD_MINUS1_EQ_IVS_RN1 h2'
      (v := wwDefor_p31 (w l) (w (i + l % k)) t) ⟨i + l % k, rfl⟩
    rw [hVn'] at h
    exact h.symm.trans (hstep2' (k - 1))
  have hL : interiorAngle1 0
      (Set.range fun j => (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
      (wwDefor_p31 (w l) (w (i + l % k)) t)
      = azim 0 (wwDefor_p31 (w l) (w (i + l % k)) t)
          (wwDefor_p31 (w l) (w (1 + (i + l % k))) t)
          (wwDefor_p31 (w l) (w (k - 1 + (i + l % k))) t) := by
    show azim 0 (wwDefor_p31 (w l) (w (i + l % k)) t)
      (rhoNode1 (Set.range fun j =>
        (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
        (wwDefor_p31 (w l) (w (i + l % k)) t))
      (ivsRhoNode1 (Set.range fun j =>
        (wwDefor_p31 (w l) (w j) t, wwDefor_p31 (w l) (w (j + 1)) t))
        (wwDefor_p31 (w l) (w (i + l % k)) t)) = _
    rw [hrhoI', hivsI']
  have hR : interiorAngle1 0 FF (w (i + l % k))
      = azim 0 (w (i + l % k)) (w (1 + (i + l % k))) (w (k - 1 + (i + l % k))) := by
    show azim 0 (w (i + l % k)) (rhoNode1 FF (w (i + l % k)))
      (ivsRhoNode1 FF (w (i + l % k))) = _
    rw [hrhoI, hivsI]
  rw [hL, hR]
  -- residue facts
  have hwne : ∀ {x : ℕ}, x % k ≠ l % k → w x ≠ w l := by
    intro x hmod hcon
    have h3 : w (x % k) = w (l % k) := by
      rw [periodic_mod_p18 hper x, hcon, hwp]
    exact hmod (by
      by_contra hne
      exact hinj (x % k) (l % k) ⟨Nat.mod_lt _ (by omega), hpl, hne⟩ h3)
  have hqne : w (i + l % k) ≠ w l :=
    hwne (x := i + l % k)
      (w5cC2_mod_shift_ne (k := k) (p := l % k) (x := i) (by omega) hpl (by omega) hik)
  by_cases hik1 : i = k - 1
  · -- the successor point sits on the base line: it is the scaled one
    have hgt : 1 < i := by omega
    have h2q_ne : w (k - 1 + (i + l % k)) ≠ w l := by
      refine hwne (x := k - 1 + (i + l % k)) ?_
      exact w5cC2_mod_pred_ne (k := k) (p := l % k) (x := i) hk1 hpl hgt hik
    have hres : (1 + (i + l % k)) % k = l % k := by
      rw [hik1]
      exact w5cC2_mod_succ_eq hpl
    have hweq : w (1 + (i + l % k)) = w l := by
      have h3 : w ((1 + (i + l % k)) % k) = w (l % k) := by rw [hres]
      rw [periodic_mod_p18 hper (1 + (i + l % k)), hwp] at h3
      exact h3
    have hA : wwDefor_p31 (w l) (w (i + l % k)) t = w (i + l % k) := by
      rw [wwDefor_apply_p31, if_neg hqne]
    have hB : wwDefor_p31 (w l) (w (1 + (i + l % k))) t = (1 - t) • w (1 + (i + l % k)) := by
      rw [wwDefor_apply_p31, if_pos hweq, hweq]
    have hC : wwDefor_p31 (w l) (w (k - 1 + (i + l % k))) t = w (k - 1 + (i + l % k)) := by
      rw [wwDefor_apply_p31, if_neg h2q_ne]
    rw [hA, hB, hC]
    simpa using w5cC_azim_scale (v := w (i + l % k)) (w1 := w (1 + (i + l % k)))
      (w2 := w (k - 1 + (i + l % k))) (a := 1) (b := 1 - t) (c := 1)
      one_pos (by linarith) one_pos
  · by_cases hi1' : i = 1
    · -- the predecessor point sits on the base line: it is the scaled one
      have hgt : 0 < i + 1 := by omega
      have hlt : i + 1 < k := by omega
      have h1q : 1 + (i + l % k) = (i + 1) + l % k := by omega
      have h1q_ne : w (1 + (i + l % k)) ≠ w l := by
        refine hwne (x := 1 + (i + l % k)) ?_
        rw [h1q]
        exact w5cC2_mod_shift_ne (k := k) (p := l % k) (x := i + 1) (by omega) hpl hgt hlt
      have hres : (k - 1 + (i + l % k)) % k = l % k := by
        rw [hi1']
        exact w5cC2_mod_pred_eq hpl
      have hweq : w (k - 1 + (i + l % k)) = w l := by
        have h3 : w ((k - 1 + (i + l % k)) % k) = w (l % k) := by rw [hres]
        rw [periodic_mod_p18 hper (k - 1 + (i + l % k)), hwp] at h3
        exact h3
      have hA : wwDefor_p31 (w l) (w (i + l % k)) t = w (i + l % k) := by
        rw [wwDefor_apply_p31, if_neg hqne]
      have hB : wwDefor_p31 (w l) (w (1 + (i + l % k))) t = w (1 + (i + l % k)) := by
        rw [wwDefor_apply_p31, if_neg h1q_ne]
      have hC : wwDefor_p31 (w l) (w (k - 1 + (i + l % k))) t
          = (1 - t) • w (k - 1 + (i + l % k)) := by
        rw [wwDefor_apply_p31, if_pos hweq, hweq]
      rw [hA, hB, hC]
      simpa using w5cC_azim_scale (v := w (i + l % k)) (w1 := w (1 + (i + l % k)))
        (w2 := w (k - 1 + (i + l % k))) (a := 1) (b := 1) (c := 1 - t)
        one_pos one_pos (by linarith)
    · -- nothing is scaled
      have hgt : 0 < i + 1 := by omega
      have hlt : i + 1 < k := by omega
      have h1q : 1 + (i + l % k) = (i + 1) + l % k := by omega
      have h1q_ne : w (1 + (i + l % k)) ≠ w l := by
        refine hwne (x := 1 + (i + l % k)) ?_
        rw [h1q]
        exact w5cC2_mod_shift_ne (k := k) (p := l % k) (x := i + 1) (by omega) hpl hgt hlt
      have h2q_ne : w (k - 1 + (i + l % k)) ≠ w l := by
        refine hwne (x := k - 1 + (i + l % k)) ?_
        exact w5cC2_mod_pred_ne (k := k) (p := l % k) (x := i) hk1 hpl (by omega) hik
      have hA : wwDefor_p31 (w l) (w (i + l % k)) t = w (i + l % k) := by
        rw [wwDefor_apply_p31, if_neg hqne]
      have hB : wwDefor_p31 (w l) (w (1 + (i + l % k))) t = w (1 + (i + l % k)) := by
        rw [wwDefor_apply_p31, if_neg h1q_ne]
      have hC : wwDefor_p31 (w l) (w (k - 1 + (i + l % k))) t = w (k - 1 + (i + l % k)) := by
        rw [wwDefor_apply_p31, if_neg h2q_ne]
      rw [hA, hB, hC]

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
  exact w5cC_INTERIOR_ANGLE_SAME_WW_DEFOR1 s k l i w t FF _hk3 _his _hk _hbb _hbb' _hFF _ht _hi1 _hik

/-- HOL `TAUSTAR_WW_DEFOR` (ODXLSTC.hl:2557): ZLZTHIC + MHAEYJN imply the
taustar decrease. -/
theorem TAUSTAR_WW_DEFOR_p31 (hz : ZLZTHIC_concl_p31) (_hm : MHAEYJN_concl_p31) :
    TAUSTAR_WW_DEFOR_concl_p31 := by
  -- DISCHARGES (la31-tower-w1 2026-11-05): source ODXLSTC.hl:2557-2684.
  -- `hz`/`hm` are carried for HOL signature fidelity but never consumed: the
  -- HOL proof is the `tau_fun` sum comparison only (CARD_FF_EQ_WW_DEFORMATION +
  -- DSV_WW_DEFOR_EQ + SUM_AZIM_EQ_ANGLE_LE4 + INTERIOR_ANGLE_SAME_WW_DEFOR{0,1}
  -- + rho_fun_decreasing + INTERIOR_ANGLE1_POS), all std-3/proved here.
  intro s k l w e1 his hmm hk hk3 hdiag hnorm hlt hJ hbbt he1pos he1lt1 hlunar
  -- ## unpack the `MMs_v39` hypothesis
  have hbb : BBsV39 s w := ((hmm.1).1).1
  have hann : Set.range w ⊆ ballAnnulus := MMsV39_annulus_p31 hmm
  have hkpos : 0 < k := by have := his.2.1; omega
  have hsk : ¬ s.k ≤ 3 := by omega
  have hperk : Periodic w k := hk ▸ hbb.2.1
  have hinj : ∀ a b, a < k → b < k → a ≠ b → w a ≠ w b :=
    fun a b ha hb hne => VV_INJ_p31 s k w hk his hbb a b ⟨ha, hb, hne⟩
  have hwl0 : w l ≠ 0 := by
    have h2 := ballAnnulus_norm_p31 (hann (Set.mem_range_self l))
    intro hzero
    rw [hzero, norm_zero] at h2
    linarith [h2.2]
  have hlk : l % s.k = l % k := by rw [hk]
  have hwlm_k : w (l % k) = w l := periodic_mod_p18 hperk l
  have hwlm : w (l % s.k) = w l := by rw [hlk]; exact hwlm_k
  -- ## the answer window is exactly the `BBs` window
  refine ⟨e1, he1pos, ?_⟩
  intro t ht0 hte1
  have ht1 : t < 1 := lt_trans hte1 he1lt1
  have hbbtt : BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t) := hbbt t ht0 hte1
  -- ## abbreviations
  set wd : ℕ → V3 := fun i => wwDefor_p31 (w l) (w i) t with hwd
  set V : Set V3 := Set.range w with hV
  set Vd : Set V3 := Set.range wd with hVd
  set E : Set (Set V3) := Set.range (fun i => {w i, w (i + 1)}) with hE
  set Ed : Set (Set V3) := Set.range (fun i => {wd i, wd (i + 1)}) with hEd
  set FF : Set (V3 × V3) := Set.range (fun i => (w i, w (i + 1))) with hFF
  set FFd : Set (V3 × V3) := Set.range (fun i => (wd i, wd (i + 1))) with hFFd
  -- ## `dsv` and the face count do not move
  have hdsv : dsvV39 s wd = dsvV39 s w := by
    have h := DSV_WW_DEFOR_EQ_p31 s k l w t hk his hbb hJ
    simpa only [hwd] using h
  have hcard : FFd.ncard = FF.ncard := by
    have h := CARD_FF_EQ_WW_DEFORMATION_p31 s k l w e1 hk his hk3 hbb hbbt t ht0 hte1
    simpa only [hwd, ← hFFd, ← hFF] using h
  -- ## the fan structure and the base interior angle
  have hclf : ConvexLocalFan V E FF := by
    rcases hbb.2.2.2 with hle | hcl
    · exact absurd hle hsk
    · simpa only [← hV, ← hE, ← hFF] using hcl
  have hlf2 : localFan_p2 V E FF := w5cC_lf2_of_LocalFan hclf.1
  have hbase : w (l % s.k) ∈ V := by
    rw [hV]; exact ⟨l % s.k, rfl⟩
  have hangpos : 0 < interiorAngle1 0 FF (w (l % s.k)) := by
    have h := INTERIOR_ANGLE1_POS (V := V) (E := E) (FF := FF) hlf2 hbase
    simpa only [interiorAngle1, interiorAngle1_p2, rhoNode1, rhoNode1_p2,
      ivsRhoNode1, ivsRhoNode1_p2] using h
  -- ## both `tau_fun` sums rewritten to the cyclic `range s.k` form
  have hsetSum : ∀ f : ℕ → ℝ, setSum {i | i < s.k} f = ∑ i ∈ Finset.range s.k, f i := by
    intro f
    rw [setSum]
    have hfin : {i : ℕ | i < s.k}.Finite := Set.finite_Iio s.k
    rw [dif_pos hfin]
    have hEq : hfin.toFinset = Finset.range s.k := by
      ext i
      simp [Set.mem_toFinset, Finset.mem_range]
    rw [hEq]
  have hsumd := SUM_AZIM_EQ_ANGLE_LE4_p35 s l l (wd (l % s.k)) Vd Ed FFd wd
    hsk hbbtt his rfl rfl rfl rfl
  have hsumo := SUM_AZIM_EQ_ANGLE_LE4_p35 s l l (w (l % s.k)) V E FF w
    hsk hbb his rfl rfl rfl rfl
  -- ## the whole comparison sits on the single non-fixed vertex `w l`
  have hfix : ∀ i, 1 ≤ i → i < k → wd (i + l % s.k) = w (i + l % s.k) := by
    intro i hi1 hik
    have hmod : (i + l % s.k) % k ≠ l % k := by
      have hp : l % s.k < k := by
        have h0 : 0 < s.k := by omega
        have h1 := Nat.mod_lt l h0
        omega
      have h := w5cC2_mod_shift_ne (k := k) (p := l % s.k) (x := i) hkpos hp (by omega) hik
      rw [hlk] at h ⊢
      exact h
    have hne : w (i + l % s.k) ≠ w l := by
      intro hcon
      have h1 : w ((i + l % s.k) % k) = w (l % k) := by
        rw [periodic_mod_p18 hperk (i + l % s.k), periodic_mod_p18 hperk l, hcon]
      exact hinj ((i + l % s.k) % k) (l % k)
        (Nat.mod_lt _ hkpos) (Nat.mod_lt _ hkpos) hmod h1
    show wwDefor_p31 (w l) (w (i + l % s.k)) t = w (i + l % s.k)
    rw [wwDefor_apply_p31, if_neg hne]
  have hang1 : ∀ i, 1 ≤ i → i < k →
      interiorAngle1 0 FFd ((rhoNode1 FFd)^[i] (wd (l % s.k)))
        = interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % s.k))) := by
    intro i hi1 hik
    have h := INTERIOR_ANGLE_SAME_WW_DEFOR1_p31 s k l i w t FF
      hk3 his hk hbb hbbtt hFF.symm ht1 hi1 hik
    simpa only [hFFd, hwd, hlk] using h
  have hterm : ∀ i, 1 ≤ i → i < k →
      rhoFun (norm (wd (i + l % s.k))) *
          interiorAngle1 0 FFd ((rhoNode1 FFd)^[i] (wd (l % s.k)))
        = rhoFun (norm (w (i + l % s.k))) *
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % s.k))) := by
    intro i hi1 hik
    rw [hfix i hi1 hik, hang1 i hi1 hik]
  have hstrict0 :
      rhoFun (norm (wd (l % s.k))) * interiorAngle1 0 FFd (wd (l % s.k))
        < rhoFun (norm (w (l % s.k))) * interiorAngle1 0 FF (w (l % s.k)) := by
    have hwd_eq : wd (l % s.k) = wwDefor_p31 (w l) (w l) t := by
      show wwDefor_p31 (w l) (w (l % s.k)) t = wwDefor_p31 (w l) (w l) t
      rw [hwlm]
    have hrho : rhoFun (norm (wd (l % s.k))) < rhoFun (norm (w (l % s.k))) := by
      rw [hwd_eq, hwlm]
      exact rho_fun_decreasing_p31 (w l) t ht0 ht1 hwl0
    have hang0 : interiorAngle1 0 FFd (wd (l % s.k))
        = interiorAngle1 0 FF (w (l % s.k)) := by
      have h := INTERIOR_ANGLE_SAME_WW_DEFOR0_p31 s k l w t FF
        hk3 his hk hbb hbbtt hFF.symm ht1
      simpa only [hFFd, hwd, hlk] using h
    rw [hang0]
    exact mul_lt_mul_of_pos_right hrho hangpos
  -- ## the strict sum inequality
  have hkey : setSum FFd (fun e => rhoFun (norm e.1) * azimInFan e Ed)
      < setSum FF (fun e => rhoFun (norm e.1) * azimInFan e E) := by
    rw [← hsumd, ← hsumo, hsetSum, hsetSum]
    refine Finset.sum_lt_sum ?_ ⟨0, ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_range] at hi
      by_cases hi0 : i = 0
      · subst hi0
        simpa only [Nat.zero_add, Function.iterate_zero, id_eq] using le_of_lt hstrict0
      · have hi1 : 1 ≤ i := by omega
        have hik : i < k := by rw [← hk]; exact hi
        exact le_of_eq (hterm i hi1 hik)
    · rw [Finset.mem_range]; omega
    · simpa only [Nat.zero_add, Function.iterate_zero, id_eq] using hstrict0
  -- ## assemble `tau_fun` and `taustar_v39`
  have htau : tauFun Vd Ed FFd < tauFun V E FF := by
    unfold tauFun
    rw [hcard]
    linarith [hkey]
  have hfin : taustarV39 s wd < taustarV39 s w := by
    have h1 : taustarV39 s wd = tauFun Vd Ed FFd - dsvV39 s wd := by
      rw [taustarV39, if_neg hsk]
    have h2 : taustarV39 s w = tauFun V E FF - dsvV39 s w := by
      rw [taustarV39, if_neg hsk]
    rw [h1, h2, hdsv]
    exact sub_lt_sub_right htau (dsvV39 s w)
  exact hfin

/-- HOL `ODXLSTCv2` (ODXLSTC.hl:2692): ZLZTHIC + MHAEYJN imply the
contradiction ODXLSTCv2_concl. -/
theorem ODXLSTCv2_p31 (hz : ZLZTHIC_concl_p31) (_hm : MHAEYJN_concl_p31) :
    ODXLSTCv2_concl_p31 := by
  -- DISCHARGES (la31-tower-w1 2026-11-05): source ODXLSTC.hl:2692-3078.
  -- Route: assemble the `BBs_v39` kit of the deformed family on the window
  -- `e1 = min (min (min (min eA eB) eC) eD) 1 / 2` (annulus `eA`, a-bound
  -- `eB`, b-bound `eC`, convexity `eD`), feed it to `TAUSTAR_WW_DEFOR`
  -- (HOL ODXLSTC.hl:3042 `MP_TAC TAUSTAR_WW_DEFOR`), and contradict the
  -- `taustar` minimality carried by `MMs_v39 s w`.
  intro s k l w hs hmw hk hk3 hdiag hnorm hlt hJ hlunar
  have hbb : BBsV39 s w := ((hmw.1).1).1
  have hmin : ∀ ww, BBsV39 s ww → taustarV39 s w ≤ taustarV39 s ww := ((hmw.1).1).2.1
  have hkpos : 0 < k := by have := hs.2.1; omega
  have hann : Set.range w ⊆ ballAnnulus := MMsV39_annulus_p31 hmw
  have hwlann : w l ∈ ballAnnulus := hann (Set.mem_range_self l)
  -- ## the index kit
  have hper : Periodic w k := hk ▸ hbb.2.1
  have hpm : ∀ a, w (a % k) = w a := fun a => periodic_mod_p18 hper a
  have hpl : l % k < k := Nat.mod_lt _ hkpos
  have hfinj : ∀ a b, a < k → b < k → a ≠ b → w a ≠ w b :=
    fun a b ha hb hne => VV_INJ_p31 s k w hk hs hbb a b ⟨ha, hb, hne⟩
  have hwliff : ∀ i, w i = w l ↔ i % k = l % k := by
    intro i
    constructor
    · intro h
      have h1 : w (i % k) = w (l % k) := by rw [hpm i, hpm l, h]
      by_contra hne
      exact hfinj (i % k) (l % k) (Nat.mod_lt _ hkpos) hpl hne h1
    · intro h
      rw [← hpm i, ← hpm l, h]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsym, hchain, hdiag0, _, _, _, _, _, _⟩ := id hs
  have hpa : Periodic2 s.a s.k := isScsV39_periodic2_a_p31 s hs
  have hpb : Periodic2 s.b s.k := isScsV39_periodic2_b_p31 s hs
  have ham : ∀ i j, s.a i j = s.a (i % k) (j % k) := by
    intro i j
    have h := (periodic2_mod_p18 hpa i j).symm
    rwa [hk] at h
  have hbm : ∀ i j, s.b i j = s.b (i % k) (j % k) := by
    intro i j
    have h := (periodic2_mod_p18 hpb i j).symm
    rwa [hk] at h
  -- ## the four windows
  obtain ⟨eA, heA, hannA⟩ := DEFORMATION_IN_BALL_ANNULUS_p31 (Ne.symm hnorm) hwlann
  obtain ⟨eB, heB, hAll⟩ := DEFORMATION_DIST_LE_ALL_COM_p31 s k l w hs hmw hk hk3 hlt
  obtain ⟨eC, heC, hBll⟩ := DEFORMATION_DIST_LE_BLL_COM_p31 s k l w hs hmw hk hk3 hdiag
  obtain ⟨eD, heD, hcf⟩ :=
    WW_DEFORMATION_CONVEX_LOCAL_FAN_p31 hz _hm s k l w hs hmw hk hk3 hdiag hnorm hlt hJ hlunar
  set e1 : ℝ := min (min (min (min eA eB) eC) eD) 1 / 2 with he1def
  have he1pos : 0 < e1 := by
    have h2 : 0 < min (min (min (min eA eB) eC) eD) 1 :=
      lt_min (lt_min (lt_min (lt_min heA heB) heC) heD) one_pos
    rw [he1def]; linarith
  have he1lt1 : e1 < 1 := by
    have h2 : min (min (min (min eA eB) eC) eD) 1 ≤ 1 := min_le_right _ _
    rw [he1def]; nlinarith
  have he1A : e1 < eA := by
    have h2 : min (min (min (min eA eB) eC) eD) 1 ≤ eA :=
      (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    rw [he1def]; nlinarith
  have he1B : e1 < eB := by
    have h2 : min (min (min (min eA eB) eC) eD) 1 ≤ eB :=
      (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    rw [he1def]; nlinarith
  have he1C : e1 < eC := by
    have h2 : min (min (min (min eA eB) eC) eD) 1 ≤ eC :=
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [he1def]; nlinarith
  have he1D : e1 < eD := by
    have h2 : min (min (min (min eA eB) eC) eD) 1 ≤ eD :=
      (min_le_left _ _).trans (min_le_right _ _)
    rw [he1def]; nlinarith
  -- ## the `BBs_v39` kit of the deformed family
  have hbbs : ∀ t, 0 < t → t < e1 → BBsV39 s (fun i => wwDefor_p31 (w l) (w i) t) := by
    intro t ht0 ht1
    have hfix : ∀ i, w i = w l → wwDefor_p31 (w l) (w i) t = (1 - t) • (w l) := by
      intro i hi; rw [wwDefor_apply_p31, if_pos hi]
    have hkeep : ∀ i, w i ≠ w l → wwDefor_p31 (w l) (w i) t = w i := by
      intro i hi; rw [wwDefor_apply_p31, if_neg hi]
    have htA : t < eA := lt_trans ht1 he1A
    have htB : t < eB := lt_trans ht1 he1B
    have htC : t < eC := lt_trans ht1 he1C
    have htD : t < eD := lt_trans ht1 he1D
    refine ⟨?ann, ?per, ?dist, ?conv⟩
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      change wwDefor_p31 (w l) (w i) t ∈ ballAnnulus
      by_cases hi : w i = w l
      · rw [hfix i hi]; exact hannA t ht0 htA
      · rw [hkeep i hi]; exact hann (Set.mem_range_self i)
    · intro i
      show wwDefor_p31 (w l) (w (i + s.k)) t = wwDefor_p31 (w l) (w i) t
      rw [hbb.2.1 i]
    · intro i j
      by_cases hi : i % k = l % k
      · by_cases hj : j % k = l % k
        · -- both indices sit at the moving vertex
          have hwi : w i = w l := (hwliff i).mpr hi
          have hwj : w j = w l := (hwliff j).mpr hj
          have hd0 : dist (wwDefor_p31 (w l) (w i) t) (wwDefor_p31 (w l) (w j) t) = 0 := by
            rw [hfix i hwi, hfix j hwj, dist_self]
          have haij : s.a i j = 0 := by
            rw [ham i j, hi, hj]; exact hdiag0 (l % k)
          have hab : s.a i j ≤ s.b i j :=
            le_trans (hchain i j).1 (le_trans (hchain i j).2.1 (hchain i j).2.2)
          constructor
          · rw [hd0, haij]
          · rw [hd0]; exact le_trans (le_of_eq haij.symm) hab
        · -- only `i` is at the moving vertex
          have hwi : w i = w l := (hwliff i).mpr hi
          have hwj : w j ≠ w l := fun h => hj ((hwliff j).mp h)
          have haij : s.a i j = s.a l j := by rw [ham i j, ham l j, hi]
          have hbij : s.b i j = s.b l j := by rw [hbm i j, hbm l j, hi]
          have hdist : dist (wwDefor_p31 (w l) (w i) t) (wwDefor_p31 (w l) (w j) t)
              = dist ((1 - t) • (w l)) (w j) := by rw [hfix i hwi, hkeep j hwj]
          constructor
          · rw [haij, hdist]; exact le_of_lt (hAll t j ht0 htB hj)
          · rw [hbij, hdist]; exact le_of_lt (hBll t j ht0 htC hj)
      · by_cases hj : j % k = l % k
        · -- only `j` is at the moving vertex (symmetric case)
          have hwj : w j = w l := (hwliff j).mpr hj
          have hwi : w i ≠ w l := fun h => hi ((hwliff i).mp h)
          have haij : s.a i j = s.a l i := by
            rw [ham i j, ham l i, hj]; exact (hsym (i % k) (l % k)).1
          have hbij : s.b i j = s.b l i := by
            rw [hbm i j, hbm l i, hj]; exact (hsym (i % k) (l % k)).2.2.2.1
          have hdist : dist (wwDefor_p31 (w l) (w i) t) (wwDefor_p31 (w l) (w j) t)
              = dist ((1 - t) • (w l)) (w i) := by
            rw [hfix j hwj, hkeep i hwi]; exact dist_comm _ _
          constructor
          · rw [haij, hdist]; exact le_of_lt (hAll t i ht0 htB hi)
          · rw [hbij, hdist]; exact le_of_lt (hBll t i ht0 htC hi)
        · -- neither index moves
          have hwi : w i ≠ w l := fun h => hi ((hwliff i).mp h)
          have hwj : w j ≠ w l := fun h => hj ((hwliff j).mp h)
          have hdist : dist (wwDefor_p31 (w l) (w i) t) (wwDefor_p31 (w l) (w j) t)
              = dist (w i) (w j) := by rw [hkeep i hwi, hkeep j hwj]
          rw [hdist]
          exact hbb.2.2.1 i j
    · exact Or.inr (hcf t (by linarith) htD)
  -- ## strict `taustar` decrease vs. `taustar` minimality
  obtain ⟨e2, he2, htau⟩ :=
    TAUSTAR_WW_DEFOR_p31 hz _hm s k l w e1 hs hmw hk hk3 hdiag hnorm hlt hJ hbbs
      he1pos he1lt1 hlunar
  set t0 : ℝ := min e1 e2 / 2 with ht0def
  have ht0pos : 0 < t0 := by
    have h2 : 0 < min e1 e2 := lt_min he1pos he2
    rw [ht0def]; linarith
  have ht0e1 : t0 < e1 := by
    have h2 : min e1 e2 ≤ e1 := min_le_left _ _
    rw [ht0def]; nlinarith
  have ht0e2 : t0 < e2 := by
    have h2 : min e1 e2 ≤ e2 := min_le_right _ _
    rw [ht0def]; nlinarith
  have hlt_tau : taustarV39 s (fun i => wwDefor_p31 (w l) (w i) t0) < taustarV39 s w :=
    htau t0 ht0pos ht0e2
  have hge : taustarV39 s w ≤ taustarV39 s (fun i => wwDefor_p31 (w l) (w i) t0) :=
    hmin (fun i => wwDefor_p31 (w l) (w i) t0) (hbbs t0 ht0pos ht0e1)
  linarith

/-- HOL `GENERIC_WW_DEFOR_RHO_NODE1` (ODXLSTC.hl:1126): the `rho_node1`
transfer for the outgoing edge dart under `local_fan`. -/
theorem GENERIC_WW_DEFOR_RHO_NODE1_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hw : (w1, v) ∈ FF)
    (_ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = rhoNode1 FF v := by
  exact w5cC_GENERIC_WW_DEFOR_RHO_NODE1 _hlf _hg _hw _ht

/-- HOL `WW_DEFOR_ALPHA3` (ODXLSTC.hl:1144): the `ivs` choice at the deformed
point is `(1 - t) % w1` for the outgoing edge case. -/
theorem WW_DEFOR_ALPHA3_p31 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hw : (w1, v) ∈ FF)
    (_ht : t ≠ 0) :
    (Classical.epsilon fun a => (a, wwDefor_p31 w1 v t) ∈
        (fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
      = (1 - t) • w1 := by
  exact w5cC_WW_DEFOR_ALPHA3 _hlf _hg _hw _ht

/-- HOL `GENERIC_WW_DEFOR_RHO_NODE2` (ODXLSTC.hl:1317): the `rho_node1` at
the deformed point is `(1 - t) % w1` for the incoming edge case. -/
theorem GENERIC_WW_DEFOR_RHO_NODE2_p31 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {w1 v : V3} {t : ℝ}
    (_hlf : LocalFan V E FF) (_hg : Generic V E) (_hv : (v, w1) ∈ FF)
    (_ht : t ≠ 0) :
    rhoNode1 ((fun uv => (wwDefor_p31 w1 uv.1 t, wwDefor_p31 w1 uv.2 t)) '' FF)
        (wwDefor_p31 w1 v t) = (1 - t) • w1 := by
  exact w5cC_GENERIC_WW_DEFOR_RHO_NODE2 _hlf _hg _hv _ht

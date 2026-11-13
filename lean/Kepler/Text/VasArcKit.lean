/-
VasArcKit — VASYYAU wave 2 (lane `vasgate-w2`): the `norm (v p)` split tail (2b).

HOL source: `reference/flyspeck/text_formalization/local/VASYYAU.hl:2594-2844`
(the tail after `MP_TAC(SET_RULE `~(&2=norm (v p)) \/ norm (v p)= &2`)`).

## Branch semantics (measured against the HOL script, not the SCOUT labels)

`prove_by_refinement` applies each list element to the *head* goal only
(`by`/`refine` on `hd gls`, HOL Light `tactics.ml:802`), so after the norm
split the two goals are processed in order, one script element at a time:

* goal 1 = `~(2 = norm (v p))` (i.e. `norm (v p) ≠ 2`): the elements
  `:2601-:2663` build `azim = π` (`AZIM_COND_FOR_COPLANAR`), the wedge
  membership `v p ∈ aff_gt {0} {v(p+1), v(p+3)}` (`coplanar_aff_gt_simple`
  at `p+3`), the diagonal bound (`CONDTION_A_LT_B`), and close the goal with
  `IMJXPHRv2` (`hnorm = ~(2 = norm (v p))` is one of its hypotheses).
* goal 2 = `norm (v p) = 2`: the elements `:2667-:2844` never touch `azim`;
  they are the arc chain: `ARCV_ADD_AFF_GE` + `KEITDWB` (arc triangle
  inequality) + `arclength_xrr` + `xrr_increasing/decreasing` + `ACS_MONO`,
  ending in a linear-arithmetic contradiction.

So the SCOUT attribution ("2b-i = norm = 2") is reversed; here goal 1 is the
`IMJXPHRv2` branch and goal 2 is the arc-chain branch.  Moreover the real
entry context of the norm split is the *inner* branch `2 < a(p+3) p`
(HOL `:2565` MP_TAC assumes both `2 < a p (p+1)` and `2 < a (p+3) p`);
the `a(p+3) p = 2` sub-branch is closed earlier (`:2558` `NUXCOEAv2`) and
never reaches the norm split.

## What this file provides

* `vasArcKit_2b_norm_ne`  — 2b / `norm (v p) ≠ 2` (HOL `:2601-2663`):
  proves the two distance equalities via `IMJXPHRv2_p28`.
* `vasArcKit_2b_norm_eq`  — 2b / `norm (v p) = 2` (HOL `:2667-2844`):
  proves `False` (the arc-chain contradiction).
* `vasArcKit_2b`          — both branches, yielding VASYYAU's two equalities.

The arc chain avoids the private `p22w5_arcV_eq_arclength22`/`arclength_xrr`
detour by the *definitional* bridge `arcV 0 a b = acs (1 - xrr ‖a‖ ‖b‖ d / 8)`
(`vasArcKit_arcV_eq_acs`, cosine law); `arclength_xrr`'s content is consumed
through the public `xrr_*_p22` monotonicity kit instead.
-/
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto25
import Kepler.Text.LocalAuto28
import Kepler.Text.PackingAuto25
import Kepler.Text.YebwjngKit
import Mathlib

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Bridges (public kit pieces) -/

/-- `arcV 0 a b` in `acs`/`xrr` form.  Direct from the definition of `arcV`
(`arccos` of the cosine-law quotient) and `xrr = 8 (1 - (y1²+y2²-y6²)/(2 y1 y2))`;
the `atn2`-based `arclength` route (`p22w5_arcV_eq_arclength22`, private in
`PackingAuto22`) is not needed. -/
theorem vasArcKit_arcV_eq_acs (a b : V3) (ha : a ≠ 0) (hb : b ≠ 0) :
    arcV 0 a b = Real.arccos (1 - xrr ‖a‖ ‖b‖ (dist a b) / 8) := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hdot : a ⬝ᵥ b = inner ℝ a b := by
    rw [PiLp.inner_apply, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by
      simp [RCLike.inner_apply, mul_comm]
  have hcos : 2 * (a ⬝ᵥ b) = ‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ - dist a b * dist a b := by
    have h := norm_sub_sq_real a b
    rw [dist_eq_norm, hdot]
    nlinarith [h]
  simp only [arcV, sub_zero, WithLp.ofLp_zero, dist_zero_right]
  have harg : (a ⬝ᵥ b) / (‖a‖ * ‖b‖) = 1 - xrr ‖a‖ ‖b‖ (dist a b) / 8 := by
    unfold xrr
    field_simp
    nlinarith [hcos]
  rw [harg]

/-- `affGt ⊆ affGe` (same `Affsign` witness, sign condition weakened; private
copies: `p23_affGt_sub_affGe` PackingAuto23:3359, LocalAuto3:2429,
LocalAuto14:1741). -/
theorem vasArcKit_affGt_sub_affGe (s t : Set V3) : affGt s t ⊆ affGe s t := by
  intro x hx
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hx
  exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- `BBsV39` puts every vertex in `ball_annulus`, i.e. `2 ≤ ‖v i‖ ≤ 2 h0`
(HOL `WL_IN_BALL_ANNULUS` / `in_ball_annulus`, NUXCOEA.hl:192). -/
theorem vasArcKit_annulus (s : ScsV39) (v : ℕ → V3) (hv : v ∈ MMsV39 s)
    (i : ℕ) : 2 ≤ ‖v i‖ ∧ ‖v i‖ ≤ 2 * h0 := by
  have h := (MMS_IMP_BBS_p28 s v hv).1 (Set.mem_range.mpr ⟨i, rfl⟩)
  simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    not_lt, dist_zero_right] at h
  exact ⟨h.2, h.1⟩

/-! ## 2b, `norm (v p) ≠ 2` branch (HOL `VASYYAU.hl:2601-2663`) -/

/-- HOL `VASYYAU.hl:2601-2663` (`norm (v p) ≠ 2`): the two adjacent distances
equal the registry values, straight from `IMJXPHRv2` (NUXCOEA.hl:7717).

Consumed early-branch products (producers):
* `hnc` — `PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14` (LA14:4277) + `scsGeneric`
  of `JKQEWGV2_p23` (HOL `:2632-2647`);
* `haff` — `coplanar_aff_gt_simple_p18` at `i = p+3` (LA18:1144), with the
  coplanarity from `AZIM_COND_FOR_COPLANAR` (LA6:6480) (HOL `:2651`);
* `hlunar` — `CIZMRRH` trichotomy (LA3:2734) + `JKQEWGV2_p23` (HOL `:2608-2619`);
* `hdiag1`/`hdiag2`/`hJ` are projections of the VASYYAU premises
  (`hdiag`, `scsBasicV39`). -/
theorem vasArcKit_2b_norm_ne (s : ScsV39) (v : ℕ → V3) (p : ℕ)
    (his : isScsV39 s) (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hstr : scsIsStr s v p)
    (hnc : ¬ Collinear3 0 (v (p + 1)) (v (p + 3)))
    (haff : v p ∈ affGt {0} {v (p + 1), v (p + 3)})
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v1 : V3),
      V = Set.range v → E = (Set.range fun i : ℕ => {v i, v (i + 1)}) →
        ¬ Lunar v1 (v p) V E)
    (hnorm : ‖v p‖ ≠ 2) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∧
      dist (v p) (v (p + 3)) = s.a p (p + 3) := by
  have hnc' : ¬ Collinear ℝ ({0, v (p + 1), v (p + (s.k - 1))} : Set V3) := by
    rw [hk]
    simpa only [Collinear3] using hnc
  have haff' : v p ∈ affGt {0} {v (p + 1), v (p + (s.k - 1))} := by
    rw [hk]
    simpa using haff
  obtain ⟨h1, h2⟩ := IMJXPHRv2_p28 s 4 v p hk his hv hstr (by norm_num) hnc' haff'
    (fun i hi => (hdiag p i hi).2.2) hnorm
    (fun i hi => lt_of_le_of_lt (hdiag p i hi).1 (hdiag p i hi).2.1)
    (fun i => by simp [BASIC_IMP_NOT_J_p25 s hbasic p i]) hlunar
  exact ⟨h1.symm, h2.symm⟩

/-! ## 2b, `norm (v p) = 2` branch (HOL `VASYYAU.hl:2667-2844`) -/

/-- HOL `VASYYAU.hl:2667-2844` (`norm (v p) = 2`): the arc chain
`ARCV_ADD_AFF_GE` + `KEITDWB` + `arclength_xrr` + `xrr_increasing/decreasing`
+ `ACS_MONO` is contradictory.

Notation: `n1 = ‖v (p+1)‖`, `n2 = ‖v (p+2)‖`, `n3 = ‖v (p+3)‖`,
`d1 = dist (v p) (v (p+1))`, `d3 = dist (v p) (v (p+3))`.

The chain (HOL `:2724-2844`):
`acs(1-X₁₂/8) < acs(1-X₁₁/8)`, `acs(1-X₃₂/8) < acs(1-X₃₁/8)`,
`acs(1-X₁₃/8) ≤ acs(1-X₁₂/8)`, `acs(1-X₂₃/8) ≤ acs(1-X₃₂/8)` together with
`acs(1-X₁₁/8) + acs(1-X₃₁/8) ≤ acs(1-X₁₃/8) + acs(1-X₂₃/8)`.

`a = 2 h0` / `b = cstab` on the two adjacent edges are re-derived here from
the registry + `A_NOT_EQ2_IMP_B_p25`; `h12`/`h23` (the two unit edges) are
early-branch products (`YEBWJNG_kit` at `p+1`/`p+2`, i.e. HOL `:2579-2584`). -/
theorem vasArcKit_2b_norm_eq (s : ScsV39) (v : ℕ → V3) (p : ℕ)
    (his : isScsV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hval : ∀ i : ℕ, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h2a : 2 < s.a p (p + 1)) (h2b : 2 < s.a (p + 3) p)
    (h12 : dist (v (p + 1)) (v (p + 2)) = 2)
    (h23 : dist (v (p + 2)) (v (p + 3)) = 2)
    (haff : v p ∈ affGt {0} {v (p + 1), v (p + 3)})
    (hnorm : ‖v p‖ = 2) : False := by
  -- (0) registry consequences on the two adjacent edges: a = 2h0, b = cstab
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, hpb, -, hsym, -, -, -, -, -, -, -, -⟩ := his
  have hpne : ¬(s.a p (p + 1) = 2) := by linarith
  obtain ⟨ha01, hb01⟩ := A_NOT_EQ2_IMP_B_p25 s p hval hpne
  have hpne3 : ¬(s.a (p + 3) ((p + 3) + 1) = 2) := by
    intro he
    have hper := (hpa (p + 3) p).2
    rw [hk] at hper
    rw [hper] at he
    linarith
  obtain ⟨ha3', hb3'⟩ := A_NOT_EQ2_IMP_B_p25 s (p + 3) hval hpne3
  have hperA := (hpa (p + 3) p).2
  rw [hk] at hperA
  have hperB := (hpb (p + 3) p).2
  rw [hk] at hperB
  have ha03 : s.a p (p + 3) = 2 * h0 := by
    calc s.a p (p + 3) = s.a (p + 3) p := (hsym p (p + 3)).1
      _ = s.a (p + 3) (p + 4) := hperA.symm
      _ = 2 * h0 := ha3'
  have hb03 : s.b p (p + 3) = cstab := by
    calc s.b p (p + 3) = s.b (p + 3) p := (hsym p (p + 3)).2.2.2.1
      _ = s.b (p + 3) (p + 4) := hperB.symm
      _ = cstab := hb3'
  -- (1) BBs-level interval bounds
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hbd01 := hBB.2.2.1 p (p + 1)
  have hbd03 := hBB.2.2.1 p (p + 3)
  have hd01lo : 2 * h0 ≤ dist (v p) (v (p + 1)) := ha01 ▸ hbd01.1
  have hd01hi : dist (v p) (v (p + 1)) ≤ cstab := hb01 ▸ hbd01.2
  have hd03lo : 2 * h0 ≤ dist (v p) (v (p + 3)) := ha03 ▸ hbd03.1
  have hd03hi : dist (v p) (v (p + 3)) ≤ cstab := hb03 ▸ hbd03.2
  -- (2) numeric constants (HOL `h0_CSTAB_LT_4`)
  obtain ⟨h2h0, hc4, -, -, h2h04, -⟩ := h0_CSTAB_LT_4_p25
  have hd01_2 : 2 < dist (v p) (v (p + 1)) := by linarith
  have hd03_2 : 2 < dist (v p) (v (p + 3)) := by linarith
  have hd01_4 : dist (v p) (v (p + 1)) < 4 := by linarith
  have hd03_4 : dist (v p) (v (p + 3)) < 4 := by linarith
  -- (3) radii: annulus membership, positivity, `< 4`
  have hn1 := vasArcKit_annulus s v hv (p + 1)
  have hn2 := vasArcKit_annulus s v hv (p + 2)
  have hn3 := vasArcKit_annulus s v hv (p + 3)
  have hn1pos : 0 < ‖v (p + 1)‖ := by linarith [hn1.1]
  have hn2pos : 0 < ‖v (p + 2)‖ := by linarith [hn2.1]
  have hn3pos : 0 < ‖v (p + 3)‖ := by linarith [hn3.1]
  have hn1lt : ‖v (p + 1)‖ < 4 := by linarith [hn1.2]
  have hn2lt : ‖v (p + 2)‖ < 4 := by linarith [hn2.2]
  have hn3lt : ‖v (p + 3)‖ < 4 := by linarith [hn3.2]
  -- (4) nonzero vertices
  have hne0 : v p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hne1 : v (p + 1) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    linarith [hn1.1]
  have hne2 : v (p + 2) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn2
    linarith [hn2.1]
  have hne3 : v (p + 3) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn3
    linarith [hn3.1]
  -- (5) `0 < upsX` for the four triangles (HOL `DIST_IMP_UPS_X_POS` x4)
  have hd0_1 : dist (0 : V3) (v p) = ‖v p‖ := by rw [dist_eq_norm, zero_sub, norm_neg]
  have hd0_2 : dist (0 : V3) (v (p + 1)) = ‖v (p + 1)‖ := by
    rw [dist_eq_norm, zero_sub, norm_neg]
  have hd0_3 : dist (0 : V3) (v (p + 2)) = ‖v (p + 2)‖ := by
    rw [dist_eq_norm, zero_sub, norm_neg]
  have hd0_4 : dist (0 : V3) (v (p + 3)) = ‖v (p + 3)‖ := by
    rw [dist_eq_norm, zero_sub, norm_neg]
  have h2le1 : 2 ≤ dist (0 : V3) (v p) := by rw [hd0_1]; exact hnorm.ge
  have h2le2 : 2 ≤ dist (0 : V3) (v (p + 1)) := by rw [hd0_2]; exact hn1.1
  have h2le3 : 2 ≤ dist (0 : V3) (v (p + 2)) := by rw [hd0_3]; exact hn2.1
  have h2le4 : 2 ≤ dist (0 : V3) (v (p + 3)) := by rw [hd0_4]; exact hn3.1
  have h4lt1 : dist (0 : V3) (v p) < 4 := by rw [hd0_1, hnorm]; norm_num
  have h4lt2 : dist (0 : V3) (v (p + 1)) < 4 := by rw [hd0_2]; exact hn1lt
  have h4lt3 : dist (0 : V3) (v (p + 2)) < 4 := by rw [hd0_3]; exact hn2lt
  have h4lt4 : dist (0 : V3) (v (p + 3)) < 4 := by rw [hd0_4]; exact hn3lt
  have h2le12 : 2 ≤ dist (v (p + 1)) (v (p + 2)) := le_of_eq h12.symm
  have h2le23 : 2 ≤ dist (v (p + 2)) (v (p + 3)) := le_of_eq h23.symm
  have h4lt12 : dist (v (p + 1)) (v (p + 2)) < 4 := by rw [h12]; norm_num
  have h4lt23 : dist (v (p + 2)) (v (p + 3)) < 4 := by rw [h23]; norm_num
  have hu1 : 0 < upsX (2 * 2) (‖v (p + 1)‖ * ‖v (p + 1)‖)
      (dist (v p) (v (p + 1)) * dist (v p) (v (p + 1))) := by
    have h := DIST_IMP_UPS_X_POS 0 (v p) (v (p + 1))
      h2le1 h2le2 (le_of_lt hd01_2) h4lt1 h4lt2 hd01_4
    rw [hd0_1, hnorm, hd0_2] at h
    simpa only [pow_two] using h
  have hu3 : 0 < upsX (2 * 2) (‖v (p + 3)‖ * ‖v (p + 3)‖)
      (dist (v p) (v (p + 3)) * dist (v p) (v (p + 3))) := by
    have h := DIST_IMP_UPS_X_POS 0 (v p) (v (p + 3))
      h2le1 h2le4 (le_of_lt hd03_2) h4lt1 h4lt4 hd03_4
    rw [hd0_1, hnorm, hd0_4] at h
    simpa only [pow_two] using h
  have hu12 : 0 < upsX (‖v (p + 1)‖ * ‖v (p + 1)‖) (‖v (p + 2)‖ * ‖v (p + 2)‖)
      (2 * 2) := by
    have h := DIST_IMP_UPS_X_POS 0 (v (p + 1)) (v (p + 2))
      h2le2 h2le3 h2le12 h4lt2 h4lt3 h4lt12
    rw [hd0_2, hd0_3, h12] at h
    simpa only [pow_two] using h
  have hu23 : 0 < upsX (‖v (p + 2)‖ * ‖v (p + 2)‖) (‖v (p + 3)‖ * ‖v (p + 3)‖)
      (2 * 2) := by
    have h := DIST_IMP_UPS_X_POS 0 (v (p + 2)) (v (p + 3))
      h2le3 h2le4 h2le23 h4lt3 h4lt4 h4lt23
    rw [hd0_3, hd0_4, h23] at h
    simpa only [pow_two] using h
  -- (6) xrr bounds (HOL `xrr_bounds` / `xrr_bounds_2` x4)
  have hX1 : 0 < xrr 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) ∧
      xrr 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) < 16 :=
    xrr_bounds_p22 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) (by norm_num) hn1pos
      (by linarith) hu1
  have hX3 : 0 < xrr 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) ∧
      xrr 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) < 16 :=
    xrr_bounds_p22 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) (by norm_num) hn3pos
      (by linarith) hu3
  have hX13 : 0 < xrr ‖v (p + 1)‖ ‖v (p + 2)‖ 2 ∧
      xrr ‖v (p + 1)‖ ‖v (p + 2)‖ 2 < 16 :=
    xrr_bounds_p22 ‖v (p + 1)‖ ‖v (p + 2)‖ 2 hn1pos hn2pos (by norm_num) hu12
  have hX23 : 0 < xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 ∧
      xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 < 16 :=
    xrr_bounds_p22 ‖v (p + 2)‖ ‖v (p + 3)‖ 2 hn2pos hn3pos (by norm_num) hu23
  -- (7) xrr monotonicity (HOL `xrr_increasing` x2, `xrr_decreasing` x2)
  have him1 : xrr 2 ‖v (p + 1)‖ 2 < xrr 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) :=
    xrr_increasing_p22 2 ‖v (p + 1)‖ 2 (dist (v p) (v (p + 1))) (by norm_num) hn1pos
      (by norm_num) (by linarith)
  have him3 : xrr 2 ‖v (p + 3)‖ 2 < xrr 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) :=
    xrr_increasing_p22 2 ‖v (p + 3)‖ 2 (dist (v p) (v (p + 3))) (by norm_num) hn3pos
      (by norm_num) (by linarith)
  have hde1 : xrr ‖v (p + 2)‖ ‖v (p + 1)‖ 2 ≤ xrr 2 ‖v (p + 1)‖ 2 :=
    xrr_decreasing_p22 2 ‖v (p + 2)‖ ‖v (p + 1)‖ 2 (by norm_num) hn2.1 hn1.1
      (by norm_num) hn1.2 hn2.1
  have hde3 : xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 ≤ xrr 2 ‖v (p + 3)‖ 2 :=
    xrr_decreasing_p22 2 ‖v (p + 2)‖ ‖v (p + 3)‖ 2 (by norm_num) hn2.1 hn3.1
      (by norm_num) hn3.2 hn2.1
  have hD1 : xrr ‖v (p + 1)‖ ‖v (p + 2)‖ 2 ≤ xrr 2 ‖v (p + 1)‖ 2 := by
    rw [xrr_sym_p22 ‖v (p + 1)‖ ‖v (p + 2)‖ 2]
    exact hde1
  -- (8) arc chain: `ARCV_ADD_AFF_GE` + `KEITDWB` (HOL `:2715-2724`, `:2675`)
  have hge : v p ∈ affGe {0} {v (p + 1), v (p + 3)} := vasArcKit_affGt_sub_affGe _ _ haff
  have hadd := ARCV_ADD_AFF_GE_p18 0 (v (p + 1)) (v (p + 3)) (v p) hne1 hne3 hne0 hge
  have hkei := KEITDWB_kit 0 (v (p + 1)) (v (p + 3)) (v (p + 2)) hne2 hne1 hne3
  have harc : arcV 0 (v (p + 1)) (v p) + arcV 0 (v p) (v (p + 3)) ≤
      arcV 0 (v (p + 1)) (v (p + 2)) + arcV 0 (v (p + 2)) (v (p + 3)) := by
    linarith
  -- (9) arcV → acs/xrr (HOL `arcVarc` + `arclength_xrr` x4)
  have e1 : arcV 0 (v (p + 1)) (v p) =
      Real.arccos (1 - xrr 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) / 8) := by
    have h := vasArcKit_arcV_eq_acs (v (p + 1)) (v p) hne1 hne0
    rw [dist_comm (v (p + 1)) (v p), hnorm,
      xrr_sym_p22 ‖v (p + 1)‖ 2 (dist (v p) (v (p + 1)))] at h
    exact h
  have e2 : arcV 0 (v p) (v (p + 3)) =
      Real.arccos (1 - xrr 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) / 8) := by
    have h := vasArcKit_arcV_eq_acs (v p) (v (p + 3)) hne0 hne3
    rw [hnorm] at h
    exact h
  have e3 : arcV 0 (v (p + 1)) (v (p + 2)) =
      Real.arccos (1 - xrr ‖v (p + 1)‖ ‖v (p + 2)‖ 2 / 8) := by
    have h := vasArcKit_arcV_eq_acs (v (p + 1)) (v (p + 2)) hne1 hne2
    rw [h12] at h
    exact h
  have e4 : arcV 0 (v (p + 2)) (v (p + 3)) =
      Real.arccos (1 - xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 / 8) := by
    have h := vasArcKit_arcV_eq_acs (v (p + 2)) (v (p + 3)) hne2 hne3
    rw [h23] at h
    exact h
  -- (10) `ACS_MONO_LT` x2, `ACS_MONO_LE` x2 (HOL `:2828-2839`)
  have hA : Real.arccos (1 - xrr 2 ‖v (p + 1)‖ 2 / 8) <
      Real.arccos (1 - xrr 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) / 8) := by
    refine Real.arccos_lt_arccos
      (x := 1 - xrr 2 ‖v (p + 1)‖ (dist (v p) (v (p + 1))) / 8)
      (y := 1 - xrr 2 ‖v (p + 1)‖ 2 / 8) ?_ ?_ ?_
    · linarith [hX1.2]
    · linarith [him1]
    · have hpos : 0 < xrr 2 ‖v (p + 1)‖ 2 := by
        have h1 : 0 < xrr ‖v (p + 2)‖ ‖v (p + 1)‖ 2 := by
          rw [← xrr_sym_p22 ‖v (p + 1)‖ ‖v (p + 2)‖ 2]
          exact hX13.1
        linarith [hde1]
      linarith
  have hB : Real.arccos (1 - xrr 2 ‖v (p + 3)‖ 2 / 8) <
      Real.arccos (1 - xrr 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) / 8) := by
    refine Real.arccos_lt_arccos
      (x := 1 - xrr 2 ‖v (p + 3)‖ (dist (v p) (v (p + 3))) / 8)
      (y := 1 - xrr 2 ‖v (p + 3)‖ 2 / 8) ?_ ?_ ?_
    · linarith [hX3.2]
    · linarith [him3]
    · have hpos : 0 < xrr 2 ‖v (p + 3)‖ 2 := by
        have h1 : 0 < xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 := hX23.1
        linarith [hde3]
      linarith
  have hC : Real.arccos (1 - xrr ‖v (p + 1)‖ ‖v (p + 2)‖ 2 / 8) ≤
      Real.arccos (1 - xrr 2 ‖v (p + 1)‖ 2 / 8) := by
    refine Real.arccos_le_arccos
      (x := 1 - xrr 2 ‖v (p + 1)‖ 2 / 8)
      (y := 1 - xrr ‖v (p + 1)‖ ‖v (p + 2)‖ 2 / 8) ?_
    linarith [hD1]
  have hE : Real.arccos (1 - xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 / 8) ≤
      Real.arccos (1 - xrr 2 ‖v (p + 3)‖ 2 / 8) := by
    refine Real.arccos_le_arccos
      (x := 1 - xrr 2 ‖v (p + 3)‖ 2 / 8)
      (y := 1 - xrr ‖v (p + 2)‖ ‖v (p + 3)‖ 2 / 8) ?_
    linarith [hde3]
  -- (11) linear-arithmetic close (HOL `:2840-2844` `REAL_ARITH_TAC`)
  rw [e1, e2, e3, e4] at harc
  linarith [harc, hA, hB, hC, hE]

/-! ## The assembled 2b tail -/

/-- VASYYAU `VASYYAU.hl:2594-2844` — the `norm (v p)` split tail, both
branches, yielding VASYYAU's two distance equalities (the statement of
`VASYYAU_concl`, LA1:5303).

Entry context: the outer `2 < s.a p (p+1)` branch together with its inner
`2 < s.a (p+3) p` branch (HOL `:2565`); `scsIsStr s v p` is VASYYAU's own
`scs_is_str` premise (its 4th defining conjunct; HOL `:2623`/`:2603`).

Early-branch products consumed (HOL `:2606-2590`, all before the split):
* `hnc`, `haff`, `hlunar` — as in `vasArcKit_2b_norm_ne`;
* `h12`, `h23` — `YEBWJNG_kit` (YebwjngKit:36) at `p+1`/`p+2`, whose `a = 2`
  premises come from `B_LE_2h0_2_SCS_M_4_p25` (LA25:2320) +
  `B_LE_2h0_IMP_B_p25` (LA25:2441) and whose non-straight premises from
  `NOT_STR_IN_CASES_4_p25` (LA25:2463). -/
theorem vasArcKit_2b (s : ScsV39) (v : ℕ → V3) (p : ℕ)
    (his : isScsV39 s) (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i : ℕ, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hstr : scsIsStr s v p)
    (h2a : 2 < s.a p (p + 1)) (h2b : 2 < s.a (p + 3) p)
    (hnc : ¬ Collinear3 0 (v (p + 1)) (v (p + 3)))
    (haff : v p ∈ affGt {0} {v (p + 1), v (p + 3)})
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v1 : V3),
      V = Set.range v → E = (Set.range fun i : ℕ => {v i, v (i + 1)}) →
        ¬ Lunar v1 (v p) V E)
    (h12 : dist (v (p + 1)) (v (p + 2)) = 2)
    (h23 : dist (v (p + 2)) (v (p + 3)) = 2) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∧
      dist (v p) (v (p + 3)) = s.a p (p + 3) := by
  by_cases hnorm : ‖v p‖ = 2
  · exfalso
    exact vasArcKit_2b_norm_eq s v p his hk hv hval h2a h2b h12 h23 haff hnorm
  · exact vasArcKit_2b_norm_ne s v p his hbasic hk hv hdiag hstr hnc haff hlunar hnorm

end Kepler.Text

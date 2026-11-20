/-
Kepler.Text.ZTGJoint0000Corners — lane `ztg-joint6-build-w1`, W1 part 1:
the corner-value certificates of the `0_0_0_0` debt, in margin order.

The debt's slice-corners assembly (`ztg_main_pos_of_slice_corners`, in
`ZTGJointKit`) needs `0 < ztgMain 0 0 0 0 c0 … c5` at every corner of the
candidate product `y1 ∈ {2hminus, 2.52, 2hplus}`, `y2…y6 ∈ {2, 2hminus}`
(96 corners; probe `w1_corner_table.py`, [sampled]).  This module carries
the two certificates that anchor the library's two consumption patterns:

* `ztgc0000_2h0_pos` — the **razor corner** `(2h0, 2⁵)`, rank 1 by margin
  (true main ≈ +7.8e-4, the family's tightest point).  Closed entirely on
  the in-tree fold-corner chain (`Gamma4ValCorner0`: the γ4 bracket
  `[-5.559154e-3, -5.558778e-3]` and the slot reduction
  `g4v_2h0_dih_eq1`) plus the in-tree `B1` bracket — via the W0 pointwise
  two-scalar assembly `ztg_main_pos_of_gD` with `G = -0.005559154`,
  `D = 1.3990024`.  This is the exact template for every rational corner
  of the library.
* `ztgc0000_2hminus_pos` — the corner `(2*hminus, 2⁵)`, rank 2 by margin
  (true main ≈ +5.4e-3), the **template for all 32 hminus-class corners**:
  its dihY evaluations carry the symbolic `2*hminus` slot, so the chain is
  the W0 branch reduction `ztg_dihY_eq_br1` at polynomial-in-`hminus`
  arguments, bracketed over the five-digit envelope
  `hminus ∈ [1.23175, 1.23176]` (`nb17_hminus_bounds`) by endpoint
  monotonicity; the γ4 side uses the V5 kit `g4v_corner_value_bounds` with
  the so-bracketed `volY`/`S`/`D` sums.

The `(2*hplus, 2⁵)` corner (rank 3) is already in tree as the W0 smoke
`ztg_smoke_0000_2hplus_pos` (`ZTGJointKit`).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.ZTGJointKit
import Kepler.Text.Gamma4ValCorner0

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

/-! ## 1. The razor corner `(2h0, 2⁵)` — rank 1 (margin +7.8e-4) -/

/-- The family's tightest corner is positive, on the in-tree fold-corner
chain alone: `γ4 ≥ -0.005559154` (`g4v_corner_2h0_bounds`),
`dihY ≥ π/2 - 0.171793879 ≥ 1.3990024` (`g4v_2h0_dih_eq1` +
`g4v_atan_B1_bounds` + `g4v_pi_bounds`), and the side condition
`0.0560305 - 0.0445813·1.3990024 = -0.0063388… < -0.005559154` closes by
`norm_num`.  Certified slack ≈ 7.8e-4, matching the sampled margin. -/
theorem ztgc0000_2h0_pos : 0 < ztgMain 0 0 0 0 (2 * h0) 2 2 2 2 2 := by
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * h0) 2 2 2 2 2 (-0.005559154) 1.3990024
    ?_ ?_ ?_
  · exact g4v_corner_2h0_bounds.1
  · rw [g4v_2h0_dih_eq1]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    obtain ⟨ha1, ha2⟩ := g4v_atan_B1_bounds
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## 2. The hminus-slot envelopes

The corner `(2*hminus, 2⁵)` carries the symbolic `2*hminus` slot.  Every
transcendental input below is a polynomial in `hminus` over the five-digit
envelope `hminus ∈ [1.23175, 1.23176]` (`nb17_hminus_bounds`); the three
polynomial identities that drive everything are
`Δ = 64·h²·(3−h²)`, `Δ4(slot 1) = 16·h²·(2−h²)`,
`Δ4(slots 2,3,5,6) = 16·h²`, `Δ4(slot 4) = 16·(3−2h²)`. -/

theorem ztgc0000_hm_pos : (0:ℝ) < hminus := by
  have h := Kepler.NliBanks17.nb17_hminus_bounds
  linarith

theorem ztgc0000_hm_sq :
    (24275329 / 16000000 : ℝ) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ 237067609 / 156250000 := by
  have h := Kepler.NliBanks17.nb17_hminus_bounds
  have h0 : (0:ℝ) ≤ hminus := by linarith
  constructor
  · nlinarith [h.1, h0]
  · nlinarith [h.2, h0]

theorem ztgc0000_hm_n :
    (75432391 / 156250000 : ℝ) ≤ 2 - hminus ^ 2 ∧ 2 - hminus ^ 2 ≤ 7724671 / 16000000 := by
  have h := ztgc0000_hm_sq
  constructor <;> linarith

theorem ztgc0000_hm_m :
    (231682391 / 156250000 : ℝ) ≤ 3 - hminus ^ 2 ∧ 3 - hminus ^ 2 ≤ 23724671 / 16000000 := by
  have h := ztgc0000_hm_sq
  constructor <;> linarith

theorem ztgc0000_hm_sqrt :
    (121768932917 / 100000000000 : ℝ) ≤ Real.sqrt (3 - hminus ^ 2) ∧
      Real.sqrt (3 - hminus ^ 2) ≤ 60884972233 / 50000000000 :=
  by
    have hm := ztgc0000_hm_m
    have h1 : (121768932917 / 100000000000 : ℝ) ^ 2 ≤ 231682391 / 156250000 := by
      norm_num
    have h2 : 23724671 / 16000000 ≤ (60884972233 / 50000000000 : ℝ) ^ 2 := by
      norm_num
    exact ztg_sqrt_bounds (by norm_num) (by norm_num)
      (by linarith [h1, hm.1]) (by linarith [h2, hm.2])

/-! ## 3. The three canonical dihedral values at the corner -/

/-- The canonical slot-1 value `π/2 + arctan (−(2−h²)/2 / √(3−h²))`. -/
theorem ztgc0000_hm_valA_bounds :
    (1.3750926 : ℝ) ≤
        Real.pi / 2 + Real.arctan ((-(2 - hminus ^ 2) / 2) / Real.sqrt (3 - hminus ^ 2)) ∧
      Real.pi / 2 + Real.arctan ((-(2 - hminus ^ 2) / 2) / Real.sqrt (3 - hminus ^ 2))
        ≤ 1.3751040 := by
  have hs := ztgc0000_hm_sqrt
  have hn := ztgc0000_hm_n
  have ht : -(2 - hminus ^ 2) / 2 < 0 := by linarith
  have hw := g4v_atan_ratio_neg_bounds (t := -(2 - hminus ^ 2) / 2)
    (d := 3 - hminus ^ 2) (dlo := 121768932917 / 100000000000)
    (dhi := 60884972233 / 50000000000)
    (ulo := -0.1982410152) (uhi := -0.1982292528)
    (lo := -0.1957036597) (hi := -0.1956923379)
    (by norm_num) hs.1 hs.2 ht ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith

  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 121768932917 / 100000000000)]
    have h2 := ztgc0000_hm_n
    norm_num
    linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 60884972233 / 50000000000)]
    have h2 := ztgc0000_hm_n
    norm_num
    linarith
  · have hpos := g4v_atan_pos_bounds (x := 0.1982410152)
      (lo := 0.195703655612) (hi := 0.195703659612)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hneg := g4v_atan_neg_bounds hpos
    linarith
  · have hpos := g4v_atan_pos_bounds (x := 0.1982292528)
      (lo := 0.195692337963) (hi := 0.195692341963)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hneg := g4v_atan_neg_bounds hpos
    linarith

/-- The canonical slots-2,3,5,6 value `π/2 + arctan (−h/2 / √(3−h²))`. -/
theorem ztgc0000_hm_valB_bounds :
    (1.1025373 : ℝ) ≤
        Real.pi / 2 + Real.arctan ((-hminus / 2) / Real.sqrt (3 - hminus ^ 2)) ∧
      Real.pi / 2 + Real.arctan ((-hminus / 2) / Real.sqrt (3 - hminus ^ 2))
        ≤ 1.1025440 := by
  have hs := ztgc0000_hm_sqrt
  have hp := ztgc0000_hm_pos
  have ht : -hminus / 2 < 0 := by linarith
  have hw := g4v_atan_ratio_neg_bounds (t := -hminus / 2)
    (d := 3 - hminus ^ 2) (dlo := 121768932917 / 100000000000)
    (dhi := 60884972233 / 50000000000)
    (ulo := -0.5057776113) (uhi := -0.5057693034)
    (lo := -0.4682590102) (hi := -0.4682523905)
    (by norm_num) hs.1 hs.2 ht ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith

  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 121768932917 / 100000000000)]
    have hp := ztgc0000_hm_pos
    have h := Kepler.NliBanks17.nb17_hminus_bounds
    norm_num
    linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 60884972233 / 50000000000)]
    have hp := ztgc0000_hm_pos
    have h := Kepler.NliBanks17.nb17_hminus_bounds
    norm_num
    linarith
  · have hpos := g4v_atan_pos_bounds (x := 0.5057776113)
      (lo := 0.468259006129) (hi := 0.468259010129)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hneg := g4v_atan_neg_bounds hpos
    linarith
  · have hpos := g4v_atan_pos_bounds (x := 0.5057693034)
      (lo := 0.468252390541) (hi := 0.468252394541)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hneg := g4v_atan_neg_bounds hpos
    linarith

/-- The canonical slot-4 value `π/2 + arctan ((2h²−3)/(2h) / √(3−h²))`. -/
theorem ztgc0000_hm_valC_bounds :
    (1.5822685 : ℝ) ≤
        Real.pi / 2 +
          Real.arctan (((2 * hminus ^ 2 - 3) / (2 * hminus)) / Real.sqrt (3 - hminus ^ 2)) ∧
      Real.pi / 2 +
          Real.arctan (((2 * hminus ^ 2 - 3) / (2 * hminus)) / Real.sqrt (3 - hminus ^ 2))
        ≤ 1.5822852 := by
  have hs := ztgc0000_hm_sqrt
  have hq := ztgc0000_hm_sq
  have hp := ztgc0000_hm_pos
  have htpos : (0:ℝ) < 2 * hminus := by linarith
  have ht : (0:ℝ) < (2 * hminus ^ 2 - 3) / (2 * hminus) :=
    div_pos (by linarith) htpos
  have hw := g4v_atan_ratio_pos_bounds (t := (2 * hminus ^ 2 - 3) / (2 * hminus))
    (d := 3 - hminus ^ 2) (dlo := 121768932917 / 100000000000)
    (dhi := 60884972233 / 50000000000)
    (ulo := 0.0114727034) (uhi := 0.0114893166)
    (lo := 0.0114721980) (hi := 0.0114888131)
    (by norm_num) hs.1 hs.2 ht ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith

  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 60884972233 / 50000000000)]
    -- goal: ulo * dhi <= t'
    have hhi : hminus ≤ 123176 / 100000 := by
      have h := Kepler.NliBanks17.nb17_hminus_bounds
      linarith
    have hcomp : (0.0114727034 : ℝ) * (60884972233 / 50000000000)
        ≤ (2 * (24275329 / 16000000 : ℝ) - 3) / (2 * 123176 / 100000) := by
      norm_num
    have hlo : (2 * (24275329 / 16000000 : ℝ) - 3) / (2 * 123176 / 100000)
        ≤ (2 * hminus ^ 2 - 3) / (2 * hminus) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2 * 123176 / 100000) htpos]
      linarith [hq.1, hhi]
    linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 121768932917 / 100000000000)]
    -- goal: t' <= uhi * dlo
    have hlo : 123175 / 100000 ≤ hminus := by
      have h := Kepler.NliBanks17.nb17_hminus_bounds
      linarith
    have hcomp : (2 * hminus ^ 2 - 3) / (2 * hminus)
        ≤ (2 * (237067609 / 156250000 : ℝ) - 3) / (2 * 123175 / 100000) := by
      rw [div_le_div_iff₀ htpos (by norm_num : (0:ℝ) < 2 * 123175 / 100000)]
      linarith [hq.2, hlo]
    have hfin : (2 * (237067609 / 156250000 : ℝ) - 3) / (2 * 123175 / 100000)
        ≤ (0.0114893166 : ℝ) * (121768932917 / 100000000000) := by
      norm_num
    linarith
  · have hpos := g4v_atan_pos_bounds (x := 0.0114727034)
      (lo := 0.011472198083) (hi := 0.011472202083)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    linarith
  · have hpos := g4v_atan_pos_bounds (x := 0.0114893166)
      (lo := 0.011488809093) (hi := 0.011488813093)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    linarith

/-! ## 4. The six tuple reductions (branch 1, symbolic hminus) -/

/-- Slot-1 tuple: `dihY (2*hminus) 2⁵ = valA`. -/
theorem ztgc0000_hm_dihA_eq :
    dihY (2 * hminus) 2 2 2 2 2 =
      Real.pi / 2 +
        Real.arctan ((-(2 - hminus ^ 2) / 2) / Real.sqrt (3 - hminus ^ 2)) := by
  have hD : deltaY (2 * hminus) 2 2 2 2 2 = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaY deltaX; ring
  have h4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * 2)
      = 16 * hminus ^ 2 * (2 - hminus ^ 2) := by
    unfold deltaX4; ring
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)
      (2 * 2))| <
      Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 2) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [abs_neg, sq_abs, h4, hD]
    have hq := ztgc0000_hm_sq
    have hu_le : 2 - hminus ^ 2 ≤ 7724671 / 16000000 := by linarith
    have hu_nn : (0:ℝ) ≤ 2 - hminus ^ 2 := by linarith
    have hm_ge : 231682391 / 156250000 ≤ 3 - hminus ^ 2 := by linarith
    have hu2 : (2 - hminus ^ 2) ^ 2 ≤ (7724671 / 16000000 : ℝ) ^ 2 := by
      nlinarith [hu_le, hu_nn, (by norm_num : (0:ℝ) ≤ 7724671 / 16000000)]
    have hE1 : (16 * hminus ^ 2 * (2 - hminus ^ 2)) ^ 2
        = hminus ^ 4 * (256 * (2 - hminus ^ 2) ^ 2) := by ring
    have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = hminus ^ 4 * (1024 * (3 - hminus ^ 2)) := by ring
    have hpos4 : (0:ℝ) < hminus ^ 4 := by
      have hp := ztgc0000_hm_pos
      positivity
    have hkey : (256:ℝ) * (2 - hminus ^ 2) ^ 2 < 1024 * (3 - hminus ^ 2) := by
      linarith [hu2, hm_ge]
    rw [hE1, hE2]
    nlinarith [hkey, hpos4]
  rw [ztg_dihY_eq_br1 hbr, h4, hD]
  have hsq : Real.sqrt (4 * ((2 * hminus) * (2 * hminus))
      * (64 * hminus ^ 2 * (3 - hminus ^ 2)))
      = 32 * hminus ^ 2 * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 4 * ((2 * hminus) * (2 * hminus)) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = (32 * hminus ^ 2) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hne1 : hminus ^ 2 ≠ 0 := by
    have hp := ztgc0000_hm_pos
    exact pow_ne_zero _ (by linarith)
  have hne2 : Real.sqrt (3 - hminus ^ 2) ≠ 0 := by
    have hq := ztgc0000_hm_sq
    have hm : (0:ℝ) < 3 - hminus ^ 2 := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hm)
  have harg : (-(16 * hminus ^ 2 * (2 - hminus ^ 2)))
      / (32 * hminus ^ 2 * Real.sqrt (3 - hminus ^ 2))
      = (-(2 - hminus ^ 2) / 2) / Real.sqrt (3 - hminus ^ 2) := by
    have hc : (32 * hminus ^ 2 * Real.sqrt (3 - hminus ^ 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hne1) hne2
    rw [div_eq_div_iff hc hne2]
    ring
  rw [harg]

/-- Slot-3 tuple: `dihY 2 2 (2*hminus) 2 2 2 = valB`. -/
theorem ztgc0000_hm_dihB1_eq :
    dihY 2 2 (2 * hminus) 2 2 2 =
      Real.pi / 2 +
        Real.arctan ((-hminus / 2) / Real.sqrt (3 - hminus ^ 2)) := by
  have hD : deltaY 2 2 (2 * hminus) 2 2 2 = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaY deltaX; ring
  have h4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)
      = 16 * hminus ^ 2 := by
    unfold deltaX4; ring
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)
      (2 * 2))| <
      Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 2 2) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [abs_neg, sq_abs, h4, hD]
    have hm_ge : 231682391 / 156250000 ≤ 3 - hminus ^ 2 := by
      have h := ztgc0000_hm_sq
      linarith
    have hE1 : (16 * hminus ^ 2) ^ 2 = hminus ^ 4 * 256 := by ring
    have hE2 : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = hminus ^ 2 * (1024 * (3 - hminus ^ 2)) := by ring
    have hpos2 : (0:ℝ) < hminus ^ 2 := by
      have hp := ztgc0000_hm_pos
      positivity
    have hkey : (256:ℝ) * hminus ^ 2 < 1024 * (3 - hminus ^ 2) := by
      have hq := ztgc0000_hm_sq
      linarith
    rw [hE1, hE2]
    nlinarith [hkey, hpos2]
  rw [ztg_dihY_eq_br1 hbr, h4, hD]
  have hsq : Real.sqrt (4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2)))
      = 32 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = (32 * hminus) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hne1 : hminus ≠ 0 := by
    have hp := ztgc0000_hm_pos
    linarith
  have hne2 : Real.sqrt (3 - hminus ^ 2) ≠ 0 := by
    have hq := ztgc0000_hm_sq
    have hm : (0:ℝ) < 3 - hminus ^ 2 := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hm)
  have harg : (-(16 * hminus ^ 2))
      / (32 * hminus * Real.sqrt (3 - hminus ^ 2))
      = (-hminus / 2) / Real.sqrt (3 - hminus ^ 2) := by
    have hc : (32 * hminus * Real.sqrt (3 - hminus ^ 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hne1) hne2
    rw [div_eq_div_iff hc hne2]
    ring
  rw [harg]

/-- Slot-2 tuple: `dihY 2 (2*hminus) 2 2 2 2 = valB`. -/
theorem ztgc0000_hm_dihB2_eq :
    dihY 2 (2 * hminus) 2 2 2 2 =
      Real.pi / 2 +
        Real.arctan ((-hminus / 2) / Real.sqrt (3 - hminus ^ 2)) := by
  have hD : deltaY 2 (2 * hminus) 2 2 2 2 = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaY deltaX; ring
  have h4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)
      = 16 * hminus ^ 2 := by
    unfold deltaX4; ring
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)
      (2 * 2))| <
      Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 2 2) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [abs_neg, sq_abs, h4, hD]
    have hm_ge : 231682391 / 156250000 ≤ 3 - hminus ^ 2 := by
      have h := ztgc0000_hm_sq
      linarith
    have hE1 : (16 * hminus ^ 2) ^ 2 = hminus ^ 4 * 256 := by ring
    have hE2 : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = hminus ^ 2 * (1024 * (3 - hminus ^ 2)) := by ring
    have hpos2 : (0:ℝ) < hminus ^ 2 := by
      have hp := ztgc0000_hm_pos
      positivity
    have hkey : (256:ℝ) * hminus ^ 2 < 1024 * (3 - hminus ^ 2) := by
      have hq := ztgc0000_hm_sq
      linarith
    rw [hE1, hE2]
    nlinarith [hkey, hpos2]
  rw [ztg_dihY_eq_br1 hbr, h4, hD]
  have hsq : Real.sqrt (4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2)))
      = 32 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = (32 * hminus) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hne1 : hminus ≠ 0 := by
    have hp := ztgc0000_hm_pos
    linarith
  have hne2 : Real.sqrt (3 - hminus ^ 2) ≠ 0 := by
    have hq := ztgc0000_hm_sq
    have hm : (0:ℝ) < 3 - hminus ^ 2 := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hm)
  have harg : (-(16 * hminus ^ 2))
      / (32 * hminus * Real.sqrt (3 - hminus ^ 2))
      = (-hminus / 2) / Real.sqrt (3 - hminus ^ 2) := by
    have hc : (32 * hminus * Real.sqrt (3 - hminus ^ 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hne1) hne2
    rw [div_eq_div_iff hc hne2]
    ring
  rw [harg]

/-- Slot-6 tuple: `dihY 2 2 2 2 2 (2*hminus) = valB`. -/
theorem ztgc0000_hm_dihB3_eq :
    dihY 2 2 2 2 2 (2 * hminus) =
      Real.pi / 2 +
        Real.arctan ((-hminus / 2) / Real.sqrt (3 - hminus ^ 2)) := by
  have hD : deltaY 2 2 2 2 2 (2 * hminus) = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaY deltaX; ring
  have h4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))
      = 16 * hminus ^ 2 := by
    unfold deltaX4; ring
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * 2)
      ((2 * hminus) * (2 * hminus)))| <
      Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 2 2 (2 * hminus)) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [abs_neg, sq_abs, h4, hD]
    have hm_ge : 231682391 / 156250000 ≤ 3 - hminus ^ 2 := by
      have h := ztgc0000_hm_sq
      linarith
    have hE1 : (16 * hminus ^ 2) ^ 2 = hminus ^ 4 * 256 := by ring
    have hE2 : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = hminus ^ 2 * (1024 * (3 - hminus ^ 2)) := by ring
    have hpos2 : (0:ℝ) < hminus ^ 2 := by
      have hp := ztgc0000_hm_pos
      positivity
    have hkey : (256:ℝ) * hminus ^ 2 < 1024 * (3 - hminus ^ 2) := by
      have hq := ztgc0000_hm_sq
      linarith
    rw [hE1, hE2]
    nlinarith [hkey, hpos2]
  rw [ztg_dihY_eq_br1 hbr, h4, hD]
  have hsq : Real.sqrt (4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2)))
      = 32 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = (32 * hminus) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hne1 : hminus ≠ 0 := by
    have hp := ztgc0000_hm_pos
    linarith
  have hne2 : Real.sqrt (3 - hminus ^ 2) ≠ 0 := by
    have hq := ztgc0000_hm_sq
    have hm : (0:ℝ) < 3 - hminus ^ 2 := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hm)
  have harg : (-(16 * hminus ^ 2))
      / (32 * hminus * Real.sqrt (3 - hminus ^ 2))
      = (-hminus / 2) / Real.sqrt (3 - hminus ^ 2) := by
    have hc : (32 * hminus * Real.sqrt (3 - hminus ^ 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hne1) hne2
    rw [div_eq_div_iff hc hne2]
    ring
  rw [harg]

/-- Slot-5 tuple: `dihY 2 2 2 2 (2*hminus) 2 = valB`. -/
theorem ztgc0000_hm_dihB4_eq :
    dihY 2 2 2 2 (2 * hminus) 2 =
      Real.pi / 2 +
        Real.arctan ((-hminus / 2) / Real.sqrt (3 - hminus ^ 2)) := by
  have hD : deltaY 2 2 2 2 (2 * hminus) 2 = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaY deltaX; ring
  have h4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)
      = 16 * hminus ^ 2 := by
    unfold deltaX4; ring
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))
      (2 * 2))| <
      Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 2 (2 * hminus) 2) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [abs_neg, sq_abs, h4, hD]
    have hm_ge : 231682391 / 156250000 ≤ 3 - hminus ^ 2 := by
      have h := ztgc0000_hm_sq
      linarith
    have hE1 : (16 * hminus ^ 2) ^ 2 = hminus ^ 4 * 256 := by ring
    have hE2 : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = hminus ^ 2 * (1024 * (3 - hminus ^ 2)) := by ring
    have hpos2 : (0:ℝ) < hminus ^ 2 := by
      have hp := ztgc0000_hm_pos
      positivity
    have hkey : (256:ℝ) * hminus ^ 2 < 1024 * (3 - hminus ^ 2) := by
      have hq := ztgc0000_hm_sq
      linarith
    rw [hE1, hE2]
    nlinarith [hkey, hpos2]
  rw [ztg_dihY_eq_br1 hbr, h4, hD]
  have hsq : Real.sqrt (4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2)))
      = 32 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = (32 * hminus) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hne1 : hminus ≠ 0 := by
    have hp := ztgc0000_hm_pos
    linarith
  have hne2 : Real.sqrt (3 - hminus ^ 2) ≠ 0 := by
    have hq := ztgc0000_hm_sq
    have hm : (0:ℝ) < 3 - hminus ^ 2 := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hm)
  have harg : (-(16 * hminus ^ 2))
      / (32 * hminus * Real.sqrt (3 - hminus ^ 2))
      = (-hminus / 2) / Real.sqrt (3 - hminus ^ 2) := by
    have hc : (32 * hminus * Real.sqrt (3 - hminus ^ 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hne1) hne2
    rw [div_eq_div_iff hc hne2]
    ring
  rw [harg]

/-- Slot-4 tuple: `dihY 2 2 2 (2*hminus) 2 2 = valC`. -/
theorem ztgc0000_hm_dihC_eq :
    dihY 2 2 2 (2 * hminus) 2 2 =
      Real.pi / 2 +
        Real.arctan (((2 * hminus ^ 2 - 3) / (2 * hminus))
          / Real.sqrt (3 - hminus ^ 2)) := by
  have hD : deltaY 2 2 2 (2 * hminus) 2 2 = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaY deltaX; ring
  have h4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)
      = 48 - 32 * hminus ^ 2 := by
    unfold deltaX4; ring
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)
      (2 * 2))| <
      Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) 2 2) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [abs_neg, sq_abs, h4, hD]
    have hq := ztgc0000_hm_sq
    have hm_ge : 231682391 / 156250000 ≤ 3 - hminus ^ 2 := by linarith
    have hw_le : 48 - 32 * hminus ^ 2 ≤ 1 := by linarith
    have hpos2 : (0:ℝ) < hminus ^ 2 := by
      have h := Kepler.NliBanks17.nb17_hminus_bounds
      nlinarith
    have hE1 : (48 - 32 * hminus ^ 2) ^ 2
        = hminus ^ 2 * ((48 - 32 * hminus ^ 2) ^ 2 / hminus ^ 2) := by
      rw [mul_div_cancel₀ _ (ne_of_gt hpos2)]
    have hE2 : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = hminus ^ 2 * (1024 * (3 - hminus ^ 2)) := by ring
    have hw_ge : (-1:ℝ) ≤ 48 - 32 * hminus ^ 2 := by
      have hq := ztgc0000_hm_sq
      linarith
    have hkey : ((48 - 32 * hminus ^ 2) ^ 2 / hminus ^ 2) < 1024 * (3 - hminus ^ 2) := by
      rw [div_lt_iff₀ hpos2]
      have hq := ztgc0000_hm_sq
      nlinarith [hw_le, hw_ge, hpos2, hm_ge]
    rw [hE1, hE2]
    nlinarith [hkey, hpos2]
  rw [ztg_dihY_eq_br1 hbr, h4, hD]
  have hsq : Real.sqrt (4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2)))
      = 32 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 4 * (2 * 2) * (64 * hminus ^ 2 * (3 - hminus ^ 2))
        = (32 * hminus) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hne1 : hminus ≠ 0 := by
    have hp := ztgc0000_hm_pos
    linarith
  have hne2 : Real.sqrt (3 - hminus ^ 2) ≠ 0 := by
    have hq := ztgc0000_hm_sq
    have hm : (0:ℝ) < 3 - hminus ^ 2 := by linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hm)
  have harg : (-(48 - 32 * hminus ^ 2))
      / (32 * hminus * Real.sqrt (3 - hminus ^ 2))
      = ((2 * hminus ^ 2 - 3) / (2 * hminus)) / Real.sqrt (3 - hminus ^ 2) := by
    have hc : (32 * hminus * Real.sqrt (3 - hminus ^ 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hne1) hne2
    rw [div_eq_div_iff hc hne2]
    rw [div_mul_eq_mul_div]
    field_simp
    ring
  rw [harg]

/-! ## 5. `S` / `D` / `volY` bounds and the γ4 kit call -/

theorem ztgc0000_hm_S_bounds :
    (2.1686179 : ℝ) ≤ solY (2 * hminus) 2 2 2 2 2 + solY (2 * hminus) 2 2 2 2 2 +
        solY 2 2 2 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 2 ∧
      solY (2 * hminus) 2 2 2 2 2 + solY (2 * hminus) 2 2 2 2 2 +
        solY 2 2 2 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 2 ≤ 2.1687915 := by
  have hA : (1.3750926 : ℝ) ≤ dihY (2 * hminus) 2 2 2 2 2 ∧
      dihY (2 * hminus) 2 2 2 2 2 ≤ 1.3751040 := by
    rw [ztgc0000_hm_dihA_eq]; exact ztgc0000_hm_valA_bounds
  have hB1 : (1.1025373 : ℝ) ≤ dihY 2 2 (2 * hminus) 2 2 2 ∧
      dihY 2 2 (2 * hminus) 2 2 2 ≤ 1.1025440 := by
    rw [ztgc0000_hm_dihB1_eq]; exact ztgc0000_hm_valB_bounds
  have hB2 : (1.1025373 : ℝ) ≤ dihY 2 (2 * hminus) 2 2 2 2 ∧
      dihY 2 (2 * hminus) 2 2 2 2 ≤ 1.1025440 := by
    rw [ztgc0000_hm_dihB2_eq]; exact ztgc0000_hm_valB_bounds
  have hB3 : (1.1025373 : ℝ) ≤ dihY 2 2 2 2 2 (2 * hminus) ∧
      dihY 2 2 2 2 2 (2 * hminus) ≤ 1.1025440 := by
    rw [ztgc0000_hm_dihB3_eq]; exact ztgc0000_hm_valB_bounds
  have hB4 : (1.1025373 : ℝ) ≤ dihY 2 2 2 2 (2 * hminus) 2 ∧
      dihY 2 2 2 2 (2 * hminus) 2 ≤ 1.1025440 := by
    rw [ztgc0000_hm_dihB4_eq]; exact ztgc0000_hm_valB_bounds
  have hC : (1.5822685 : ℝ) ≤ dihY 2 2 2 (2 * hminus) 2 2 ∧
      dihY 2 2 2 (2 * hminus) 2 2 ≤ 1.5822852 := by
    rw [ztgc0000_hm_dihC_eq]; exact ztgc0000_hm_valC_bounds
  have hSA : solY (2 * hminus) 2 2 2 2 2
      = dihY (2 * hminus) 2 2 2 2 2 + dihY 2 2 (2 * hminus) 2 2 2
        + dihY 2 (2 * hminus) 2 2 2 2 - Real.pi := by
    simp only [solY]
  have hSC : solY 2 2 2 (2 * hminus) 2 2
      = dihY 2 2 2 (2 * hminus) 2 2 + dihY 2 2 2 2 2 (2 * hminus)
        + dihY 2 2 2 2 (2 * hminus) 2 - Real.pi := by
    simp only [solY]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  rw [hSA, hSC]
  constructor <;> nlinarith [hA.1, hA.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2,
    hB4.1, hB4.2, hC.1, hC.2, hp1, hp2]

theorem ztgc0000_hm_D_bounds :
    (6.1417600 : ℝ) ≤ lmfun (2 * hminus / 2) * dihY (2 * hminus) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2 ∧
      lmfun (2 * hminus / 2) * dihY (2 * hminus) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 2 ≤ 6.1418849 := by
  have hlm := ztg_lmfun_hminus_bounds
  have hA : (1.3750926 : ℝ) ≤ dihY (2 * hminus) 2 2 2 2 2 ∧
      dihY (2 * hminus) 2 2 2 2 2 ≤ 1.3751040 := by
    rw [ztgc0000_hm_dihA_eq]; exact ztgc0000_hm_valA_bounds
  have hB1 : (1.1025373 : ℝ) ≤ dihY 2 2 (2 * hminus) 2 2 2 ∧
      dihY 2 2 (2 * hminus) 2 2 2 ≤ 1.1025440 := by
    rw [ztgc0000_hm_dihB1_eq]; exact ztgc0000_hm_valB_bounds
  have hB2 : (1.1025373 : ℝ) ≤ dihY 2 (2 * hminus) 2 2 2 2 ∧
      dihY 2 (2 * hminus) 2 2 2 2 ≤ 1.1025440 := by
    rw [ztgc0000_hm_dihB2_eq]; exact ztgc0000_hm_valB_bounds
  have hC : (1.5822685 : ℝ) ≤ dihY 2 2 2 (2 * hminus) 2 2 ∧
      dihY 2 2 2 (2 * hminus) 2 2 ≤ 1.5822852 := by
    rw [ztgc0000_hm_dihC_eq]; exact ztgc0000_hm_valC_bounds
  have hlone : lmfun (2 / 2) = 1 := by
    norm_num [lmfun, h0]
  have hslot : 2 * hminus / 2 = hminus := by ring
  rw [hslot, hlone]
  have hprod_lo : (0.108615 : ℝ) * 1.3750926
      ≤ lmfun hminus * dihY (2 * hminus) 2 2 2 2 2 :=
    mul_le_mul hlm.1 hA.1 (by linarith [hlm.1]) (by linarith [hA.1])
  have hprod_hi : lmfun hminus * dihY (2 * hminus) 2 2 2 2 2
      ≤ (0.108654 : ℝ) * 1.3751040 :=
    mul_le_mul hlm.2 hA.2 (by linarith [hlm.1]) (by linarith [hA.1])
  constructor <;> nlinarith [hprod_lo, hprod_hi, hB1.1, hB1.2, hB2.1, hB2.2, hC.1, hC.2]

theorem ztgc0000_hm_volY_bounds :
    (0.9999258874 : ℝ) ≤ volY (2 * hminus) 2 2 2 2 2 ∧
      volY (2 * hminus) 2 2 2 2 2 ≤ 0.9999423120 := by
  have hs := ztgc0000_hm_sqrt
  have hDx : deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * 2)
      = 64 * hminus ^ 2 * (3 - hminus ^ 2) := by
    unfold deltaX; ring
  unfold volY volXf
  rw [hDx]
  have hsq : Real.sqrt (64 * hminus ^ 2 * (3 - hminus ^ 2))
      = 8 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    have hE : 64 * hminus ^ 2 * (3 - hminus ^ 2)
        = (8 * hminus) ^ 2 * (3 - hminus ^ 2) := by ring
    rw [hE, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by have hp := ztgc0000_hm_pos; positivity)]
  rw [hsq]
  have hlo : (2 * 123175 / 100000 * (121768932917 / 100000000000 : ℝ)) / 3
      ≤ (2 * hminus * Real.sqrt (3 - hminus ^ 2)) / 3 := by
    have hp := ztgc0000_hm_pos
    have h := Kepler.NliBanks17.nb17_hminus_bounds
    have h1 := h.1
    have h2 : (121768932917 / 100000000000 : ℝ) ≤ Real.sqrt (3 - hminus ^ 2) := hs.1
    have h3 : (0:ℝ) ≤ Real.sqrt (3 - hminus ^ 2) := by positivity
    have h4 : (0:ℝ) ≤ 121768932917 / 100000000000 := by norm_num
    have h5 : (0:ℝ) ≤ 123175 / 100000 := by norm_num
    nlinarith
  have hhi : (2 * hminus * Real.sqrt (3 - hminus ^ 2)) / 3
      ≤ (2 * 123176 / 100000 * (60884972233 / 50000000000 : ℝ)) / 3 := by
    have hp := ztgc0000_hm_pos
    have h := Kepler.NliBanks17.nb17_hminus_bounds
    have h1 := h.2
    have h2 : Real.sqrt (3 - hminus ^ 2) ≤ 60884972233 / 50000000000 := hs.2
    have h3 : (0:ℝ) ≤ Real.sqrt (3 - hminus ^ 2) := by positivity
    have h4 : (0:ℝ) ≤ 60884972233 / 50000000000 := by norm_num
    have h5 : (0:ℝ) ≤ hminus := by linarith
    nlinarith
  have hclear : (2 * hminus * Real.sqrt (3 - hminus ^ 2)) / 3 * 3
      = 2 * hminus * Real.sqrt (3 - hminus ^ 2) := by
    field_simp
  constructor
  · have hnum : (0.9999258874 : ℝ) * 3
        ≤ (2 * 123175 / 100000 * (121768932917 / 100000000000 : ℝ)) / 3 * 3 := by
      norm_num
    have h3 : (0:ℝ) < 3 := by norm_num
    have hfinal : (0.9999258874 : ℝ) * 3
        ≤ (2 * hminus * Real.sqrt (3 - hminus ^ 2)) / 3 * 3 :=
      le_trans hnum (by nlinarith [hlo, h3])
    rw [hclear] at hfinal
    linarith
  · have hnum : (2 * 123176 / 100000 * (60884972233 / 50000000000 : ℝ)) / 3 * 3
        ≤ (0.9999423120 : ℝ) * 3 := by
      norm_num
    have h3 : (0:ℝ) < 3 := by norm_num
    have hfinal : (2 * hminus * Real.sqrt (3 - hminus ^ 2)) / 3 * 3
        ≤ (0.9999423120 : ℝ) * 3 :=
      le_trans (by nlinarith [hhi, h3]) hnum
    rw [hclear] at hfinal
    linarith

/-- The V5 kit call: `γ4 (2*hminus, 2⁵) ∈ [0.0000296, 0.0001663]`
(true value `9.88216e-5`; the lower side is what the corner certificate
consumes, with certified slack `5.30e-3` against the sampled margin
`5.37e-3`). -/
theorem ztgc0000_hm_g4_bounds :
    (0.0000296 : ℝ) ≤ gamma4fgcy (2 * hminus) 2 2 2 2 2 lmfun ∧
      gamma4fgcy (2 * hminus) 2 2 2 2 2 lmfun ≤ 0.0001663 := by
  have h := g4v_corner_value_bounds
    (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := 0.9999258874) (Vhi := 0.9999423120)
    (Slo := 2.1686179) (Shi := 2.1687915)
    (Dlo := 6.1417600) (Dhi := 6.1418849)
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    ztgc0000_hm_volY_bounds ztgc0000_hm_S_bounds ztgc0000_hm_D_bounds
    ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heval_lo : (0.0000296 : ℝ) ≤ 0.9999258874 - 0.6443107122 * 2.1687915
      + 0.0647174928 * 6.1417600 := by norm_num
  have heval_hi : 0.9999423120 - 0.6443106485 * 2.1686179
      + 0.0647175183 * 6.1418849 ≤ (0.0001663 : ℝ) := by norm_num
  constructor <;> linarith [h.1, h.2, heval_lo, heval_hi]

/-! ## 6. The corner certificate -/

/-- **Rank-2 corner** `(2*hminus, 2⁵)`: positive with certified slack
`5.30e-3` against the sampled margin `5.37e-3`.  This is the template for
all 32 hminus-class corners of the debt. -/
theorem ztgc0000_2hminus_pos :
    0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 2 2 2 := by
  have hA : (1.3750926 : ℝ) ≤ dihY (2 * hminus) 2 2 2 2 2 := by
    rw [ztgc0000_hm_dihA_eq]; exact ztgc0000_hm_valA_bounds.1
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 2 2 2 0.0000296 1.3750926
    ?_ ?_ ?_
  · exact ztgc0000_hm_g4_bounds.1
  · exact hA
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## Axiom audit (house style) -/

#print axioms ztgc0000_2h0_pos
#print axioms ztgc0000_hm_pos
#print axioms ztgc0000_hm_sq
#print axioms ztgc0000_hm_n
#print axioms ztgc0000_hm_m
#print axioms ztgc0000_hm_sqrt
#print axioms ztgc0000_hm_valA_bounds
#print axioms ztgc0000_hm_valB_bounds
#print axioms ztgc0000_hm_valC_bounds
#print axioms ztgc0000_hm_dihA_eq
#print axioms ztgc0000_hm_dihB1_eq
#print axioms ztgc0000_hm_dihB2_eq
#print axioms ztgc0000_hm_dihB3_eq
#print axioms ztgc0000_hm_dihB4_eq
#print axioms ztgc0000_hm_dihC_eq
#print axioms ztgc0000_hm_S_bounds
#print axioms ztgc0000_hm_D_bounds
#print axioms ztgc0000_hm_volY_bounds
#print axioms ztgc0000_hm_g4_bounds
#print axioms ztgc0000_2hminus_pos

end Kepler.Text

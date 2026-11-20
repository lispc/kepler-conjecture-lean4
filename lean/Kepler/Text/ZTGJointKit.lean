/-
Kepler.Text.ZTGJointKit — lane `ztg-joint6-build-w1`, W0: the L0 kit of the
ZTG joint-6 corner-table campaign (scout verdict `ztg-joint6-scout-w1`,
route B GO, 2026-11-19).

The six joint debts `nliRestZTGIJCF4_<bits>` reduce (`ztg_of_main`, in tree)
to `ztgMain > 0` on `ztgBox`.  Route B closes each debt by (i) per-slice
concavity or monotonicity certificates collapsing every coordinate onto the
kink-augmented alphabet, and (ii) corner-value certificates at the collapsed
corners.  This module is the reusable layer between those two certificate
families and the bank:

* `ztg_atn2_le` — the upper mirror of `ZTGDihKit.ztg_atn2_ge` (same branch
  analysis, opposite direction), with the `dihY`-level corollary
  `ztg_dihY_le_arctan`;
* `ztg_dihY_eq_br1 / _br2 / _br3` — the three branch-faithful exact
  reductions of `dihY` at a point.  The V4 corner chain
  (`Gamma4ValCorner`) does this inline per corner with 30 lines of
  `norm_num`; here the branch analysis is done once, generically, and the
  corner certificate only supplies the ground branch comparison.  The
  joint-6 corner sweep (probe `corner_atn2_probe.py`, [sampled]) found all
  three branches live: branch 1 carries all of the trio and `0_0_0_0`,
  branch 3 carries 54 evaluations of `1_0_0_1` and 52 of `0_1_0_0`
  (including the `1_0_0_1` main term at its own argmin), branch 2 fires
  twice in `0_1_0_0`;
* `ztg_sqrt_bounds`, `ztg_atan_sqrt_div_bounds` — the shared bracket
  kit: two-sided `√d` brackets from squared rational endpoints and
  `arctan (√d / t)` brackets (the mirror of `g4v_atan_ratio_pos_bounds`,
  which handles `t / √d` only);
* the certified-`D` arctan brackets via the addition split
  `arctan y = π/4 + arctan ((y − 1) / (y + 1))` (`ztg_atan_shift_add`):
  the small ratios `5/133`, `19/119`, `21/179` are direct order-32 Taylor
  brackets, and `ztg_arctan_69_64_bounds` (trio), `ztg_arctan_69_50_bounds`
  (`0_0_0_0`), `ztg_arctan_79_100_bounds` (`0_1_0_0`) and
  `ztg_arctan_9_13_bounds` (`1_0_0_1`) are assembled from them.  These
  serve the uniform-`D` shortcuts and the optional `ztgG` root-leaf
  insurance route (scout §4.A), not the per-corner chain;
* `ztg_dihY_ge_arctan_of_Gpos` — the polynomial-to-dihedral bridge: the
  `ztgG`-shaped hypothesis `0 ≤ 4·y1²·Δ − s²·Δ4²` (with `0 < 4·y1²·Δ`)
  gives `arctan s ≤ dihY`, wrapping `ztg_dihY_ge_arctan` (Kit A);
* the slice kit in the `NliBanks9.boxInf` world: `ztg_main_fun` (the
  `Fin 6` packaging of `ztgMain`), `ztg_main_fun_cons`, the per-coordinate
  step lemmas `ztg_step_of_concave_pair` (kink triple), `ztg_step_of_concave`
  (endpoint pair), `ztg_step_of_mono_up_pair / _mono_dn_pair` (the
  singleton candidates for the 2.2-cut regular coordinates of `0_1_0_0`),
  the positivity bridge `ztg_boxInf_pos` (via `Finset.inf'_mem`), and the
  assembly `ztg_main_pos_of_slice_corners` — mixed candidate sets per
  coordinate, corner positivity stated as a nested six-fold bounded `∀`
  over the candidate sets so that consumers discharge it by
  `Finset.mem_insert` case splits;
* `ztg_main_pos_of_gD` — the pointwise two-scalar form of
  `ztg_of_global_bounds` consumed by every corner-value certificate
  (per-corner `G` and `D` are the corner's own tight brackets, so nothing
  is lost against the razor margin of `0_0_0_0`);
* box-edge constants of the alphabet (`ztg_two_hminus_le_kink`,
  `ztg_kink_le_two_hplus`, `ztg_kink_le_sqrt8`, `ztg_hminus_lt_h0`) and the
  `lmfun` values at `2·hminus` (`ztg_lmfun_hminus_eq/_bounds`) and at the
  kink half-argument (`ztg_lmfun_kink_zero`).  `lmfun (√8 / 2) = 0` is
  already in tree (`lmfun_sqrt8_div_two`, `Gamma4Sharp`).

Two smoke tests validate the consumer interfaces end to end:
`ztg_smoke_0000_2hplus_pos` (a genuine W3 corner of `0_0_0_0`, `(2hplus,
2⁵)`, closed through `ztg_main_pos_of_gD` on the in-tree V5 corner bound
`g4v_corner_2hplus_bounds` and the in-tree slot reduction
`g4v_2hp_dih_eq1`), and `ztg_smoke_slice_assembly` (the degenerate box
`lo = hi = (2hplus, 2⁵)` through the full slice-corners template).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.ZTGDihKit
import Kepler.Text.Gamma4ValCornerKit
import Kepler.NliBanks9
import Kepler.NliBanksZTGIJCF4Route
import Kepler.NliBanksZTGIJCF4Bounds

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

/-! ## 1. The generic `atn2` upper bound (mirror of `ztg_atn2_ge`) -/

/-- For `0 < x`, `0 < s` and `|y| ≤ s·x`: `atn2 x y ≤ arctan s`.
The branch analysis mirrors `ztg_atn2_ge` (`ZTGDihKit`).  On the `|y| < x`
branch `atn2 = arctan (y / x) ≤ arctan s`; on the `0 < y` branch
`atn2 = π/2 − arctan (x / y)` with `x / y ≥ 1/s`, and
`arctan (1/s) + arctan s = π/2`; on the `y < 0` branch `atn2 < 0`. -/
theorem ztg_atn2_le {x y s : ℝ} (hx : 0 < x) (hs : 0 < s) (h : |y| ≤ s * x) :
    atn2 x y ≤ Real.arctan s := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  unfold atn2
  split_ifs with h1 h2 h3
  · -- the `|y| < x` branch
    have hyx : y / x ≤ s := by
      rw [div_le_iff₀ hx]
      have habs : y ≤ |y| := le_abs_self y
      linarith
    exact Real.arctan_le_arctan_iff.mpr hyx
  · -- the `0 < y` branch
    have hyabs : |y| = y := abs_of_pos h2
    rw [hyabs] at h
    have hinv : 1 / s ≤ x / y := by
      rw [div_le_div_iff₀ hs h2]
      linarith
    have hsum : Real.arctan s + Real.arctan (1 / s) = Real.pi / 2 := by
      have h := Real.arctan_inv_of_pos hs
      rw [inv_eq_one_div] at h
      linarith
    have hmono := Real.arctan_le_arctan_iff.mpr hinv
    linarith
  · -- the `y < 0` branch
    have hxy : x / y < 0 := div_neg_of_pos_of_neg hx h3
    have ha : Real.arctan (x / y) < 0 := by
      have hp := Real.arctan_pos.mpr (neg_pos.mpr hxy)
      rw [Real.arctan_neg] at hp
      linarith
    have hb : -(Real.pi / 2) < Real.arctan (x / y) := by
      have hp := Real.arctan_lt_pi_div_two (-(x / y))
      rw [Real.arctan_neg] at hp
      linarith
    have hsa : (0:ℝ) < Real.arctan s := Real.arctan_pos.mpr hs
    linarith
  · -- `y = 0` with `¬ (|y| < x)` contradicts `0 < x`
    exfalso
    have hy0 : y = 0 := le_antisymm (by linarith) (by linarith)
    subst hy0
    rw [abs_zero] at h1
    exact h1 (by linarith)

/-- The `dihY` form of the upper mirror: `|−Δ4| ≤ s·A` gives
`dihY ≤ π/2 + arctan s`. -/
theorem ztg_dihY_le_arctan {y1 y2 y3 y4 y5 y6 s : ℝ} (hs : 0 < s)
    (hA : 0 < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
    (h : |deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)| ≤
      s * Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)) :
    dihY y1 y2 y3 y4 y5 y6 ≤ Real.pi / 2 + Real.arctan s := by
  have hh : |-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))| ≤
      s * Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    rw [abs_neg]; exact h
  have key := ztg_atn2_le hA hs hh
  simp only [deltaY] at key
  unfold dihY dihXf
  linarith

/-! ## 2. Branch-faithful `dihY` reductions at a point -/

/-- Branch 1 (`|−Δ4| < A` with `A = √(4·y1²·Δ)`):
`dihY = π/2 + arctan (−Δ4 / A)`. -/
theorem ztg_dihY_eq_br1 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h : |-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))| <
      Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)) :
    dihY y1 y2 y3 y4 y5 y6 =
      Real.pi / 2 + Real.arctan (-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3)
          (y4 * y4) (y5 * y5) (y6 * y6)) /
        Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)) := by
  unfold deltaY at h ⊢
  unfold dihY dihXf
  rw [atn2, if_pos h]

/-- Branch 2 (`Δ4 < 0`, `A ≤ −Δ4`): `dihY = π − arctan (A / (−Δ4))`. -/
theorem ztg_dihY_eq_br2 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h0 : (0:ℝ) < -(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
    (h1 : Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) ≤
      -(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))) :
    dihY y1 y2 y3 y4 y5 y6 = Real.pi - Real.arctan
      (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) /
        -(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))) := by
  unfold deltaY at h1 ⊢
  have hbr : ¬ (|-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6))| <
      Real.sqrt (4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6))) := by
    rw [abs_of_pos h0]
    exact not_lt.mpr h1
  unfold dihY dihXf
  rw [atn2, if_neg hbr, if_pos h0]
  ring

/-- Branch 3 (`0 < Δ4`, `A ≤ Δ4`): `dihY = arctan (A / Δ4)`. -/
theorem ztg_dihY_eq_br3 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h0 : (0:ℝ) < deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    (h1 : Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) ≤
      deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) :
    dihY y1 y2 y3 y4 y5 y6 = Real.arctan
      (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) /
        deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) := by
  unfold deltaY at h1 ⊢
  have hyn : -(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6)) < 0 := by linarith
  have hbr : ¬ (|-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6))| <
      Real.sqrt (4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6))) := by
    have hneg : |-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
        (y6 * y6))| = deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
        (y5 * y5) (y6 * y6) := by
      rw [abs_of_neg hyn]
      ring
    rw [hneg]
    exact not_lt.mpr h1
  have hn2 : ¬ (0 < -(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6))) := by linarith
  unfold dihY dihXf
  rw [atn2, if_neg hbr, if_neg hn2, if_pos hyn]
  have hd4 : deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≠ 0 :=
    ne_of_gt h0
  have hsplit : (Real.sqrt (4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6)) /
      -(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))) =
      -(Real.sqrt (4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6)) /
        deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) := by
    field_simp
  rw [hsplit, Real.arctan_neg]
  ring

/-! ## 3. Shared sqrt and `arctan (√d / t)` brackets -/

/-- Two-sided `√d` bracket from squared rational endpoints. -/
theorem ztg_sqrt_bounds {d a b : ℝ} (_ha : 0 < a) (hb : 0 ≤ b)
    (h1 : a ^ 2 ≤ d) (h2 : d ≤ b ^ 2) :
    a ≤ Real.sqrt d ∧ Real.sqrt d ≤ b :=
  ⟨Real.le_sqrt_of_sq_le h1, (Real.sqrt_le_left hb).mpr h2⟩

/-- For `0 < t` and `dlo ≤ √d ≤ dhi`: `arctan (√d / t)` is bracketed by the
`arctan` brackets of the endpoint quotients `dlo / t`, `dhi / t`.  The
mirror of `g4v_atan_ratio_pos_bounds` (which handles `t / √d` only);
branches 2 and 3 of the `dihY` reduction have `√d` in the numerator. -/
theorem ztg_atan_sqrt_div_bounds {d t dlo dhi ulo uhi lo hi : ℝ}
    (ht : 0 < t) (hslo : dlo ≤ Real.sqrt d) (hshi : Real.sqrt d ≤ dhi)
    (hu1 : ulo ≤ dlo / t) (hu2 : dhi / t ≤ uhi)
    (ha1 : lo ≤ Real.arctan ulo) (ha2 : Real.arctan uhi ≤ hi) :
    lo ≤ Real.arctan (Real.sqrt d / t) ∧ Real.arctan (Real.sqrt d / t) ≤ hi := by
  have h1 : dlo / t ≤ Real.sqrt d / t := by
    rw [div_le_div_iff₀ ht ht]
    exact mul_le_mul_of_nonneg_right hslo ht.le
  have h2 : Real.sqrt d / t ≤ dhi / t := by
    rw [div_le_div_iff₀ ht ht]
    exact mul_le_mul_of_nonneg_right hshi ht.le
  constructor
  · exact le_trans ha1 (Real.arctan_mono (le_trans hu1 h1))
  · exact le_trans (Real.arctan_mono (le_trans h2 hu2)) ha2

/-! ## 4. The certified-`D` arctan brackets -/

/-- The π/4 shift: `arctan y = π/4 + arctan ((y − 1) / (y + 1))` for
`−1 < y`.  (The in-tree precedent `cvp_atan_shift` is `private` in
`Ox3q1hCornerPilot`; this is the public generic form, by `Real.arctan_add`
at `−1`, covering both the `y < 1` and `y > 1` sides.) -/
theorem ztg_atan_shift_add {y : ℝ} (hy : (-1:ℝ) < y) :
    Real.arctan y = Real.pi / 4 + Real.arctan ((y - 1) / (y + 1)) := by
  have hcond : (-1:ℝ) * y < 1 := by linarith
  have h2 := Real.arctan_add (x := (-1:ℝ)) (y := y) hcond
  rw [Real.arctan_neg, Real.arctan_one] at h2
  have hne1 : (y:ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hne2 : (1:ℝ) - (-1) * y ≠ 0 := ne_of_gt (by linarith)
  have hdiv : (y - 1) / (y + 1) = ((-1:ℝ) + y) / (1 - (-1) * y) := by
    rw [div_eq_div_iff hne1 hne2]
    ring
  rw [hdiv]
  linarith

/-- `arctan (5/133) ∈ [0.0375762883427, 0.0375762903427]` (order-32
alternating Taylor; tail `1e-11`). -/
theorem ztg_arctan_5_133_bounds :
    (0.0375762883427 : ℝ) ≤ Real.arctan (5 / 133) ∧
      Real.arctan (5 / 133) ≤ 0.0375762903427 :=
  g4v_atan_pos_bounds (x := (5 / 133 : ℝ)) (lo := 0.0375762883427)
    (hi := 0.0375762903427) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `arctan (19/119) ∈ [0.158327499808, 0.158327501808]`. -/
theorem ztg_arctan_19_119_bounds :
    (0.158327499808 : ℝ) ≤ Real.arctan (19 / 119) ∧
      Real.arctan (19 / 119) ≤ 0.158327501808 :=
  g4v_atan_pos_bounds (x := (19 / 119 : ℝ)) (lo := 0.158327499808)
    (hi := 0.158327501808) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `arctan (21/179) ∈ [0.11678459447, 0.11678459647]`. -/
theorem ztg_arctan_21_179_bounds :
    (0.11678459447 : ℝ) ≤ Real.arctan (21 / 179) ∧
      Real.arctan (21 / 179) ≤ 0.11678459647 :=
  g4v_atan_pos_bounds (x := (21 / 179 : ℝ)) (lo := 0.11678459447)
    (hi := 0.11678459647) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `arctan (9/13) ∈ [0.605544662605, 0.605544664605]` — the certified `D`
value of `1_0_0_1` (scout §3: `atan (9/13) = 0.60554`), direct Taylor. -/
theorem ztg_arctan_9_13_bounds :
    (0.605544662605 : ℝ) ≤ Real.arctan (9 / 13) ∧
      Real.arctan (9 / 13) ≤ 0.605544664605 :=
  g4v_atan_pos_bounds (x := (9 / 13 : ℝ)) (lo := 0.605544662605)
    (hi := 0.605544664605) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `arctan (69/64) = π/4 + arctan (5/133) ∈ [0.8229744517, 0.8229744538]` —
the certified `D` value of the trio (scout §3: `atan (69/64) = 0.82297`). -/
theorem ztg_arctan_69_64_bounds :
    (0.8229744517 : ℝ) ≤ Real.arctan (69 / 64) ∧
      Real.arctan (69 / 64) ≤ 0.8229744538 := by
  have hfrac : ((69 / 64 : ℝ) - 1) / ((69 / 64) + 1) = 5 / 133 := by norm_num
  rw [ztg_atan_shift_add (by norm_num : (-1:ℝ) < 69 / 64), hfrac]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  obtain ⟨ha1, ha2⟩ := ztg_arctan_5_133_bounds
  constructor <;> linarith

/-- `arctan (69/50) = π/4 + arctan (19/119) ∈ [0.9437256632, 0.9437256653]` —
the certified `D` value of `0_0_0_0` (scout §3: `atan (69/50) = 0.94373`). -/
theorem ztg_arctan_69_50_bounds :
    (0.9437256632 : ℝ) ≤ Real.arctan (69 / 50) ∧
      Real.arctan (69 / 50) ≤ 0.9437256653 := by
  have hfrac : ((69 / 50 : ℝ) - 1) / ((69 / 50) + 1) = 19 / 119 := by norm_num
  rw [ztg_atan_shift_add (by norm_num : (-1:ℝ) < 69 / 50), hfrac]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  obtain ⟨ha1, ha2⟩ := ztg_arctan_19_119_bounds
  constructor <;> linarith

/-- `arctan (79/100) = π/4 − arctan (21/179) ∈ [0.6686135669, 0.6686135690]` —
the certified `D` value of `0_1_0_0` (scout §3: `atan (79/100) = 0.66861`). -/
theorem ztg_arctan_79_100_bounds :
    (0.6686135669 : ℝ) ≤ Real.arctan (79 / 100) ∧
      Real.arctan (79 / 100) ≤ 0.6686135690 := by
  have hfrac : ((79 / 100 : ℝ) - 1) / ((79 / 100) + 1) = -(21 / 179) := by norm_num
  rw [ztg_atan_shift_add (by norm_num : (-1:ℝ) < 79 / 100), hfrac, Real.arctan_neg]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  obtain ⟨ha1, ha2⟩ := ztg_arctan_21_179_bounds
  constructor <;> linarith

/-! ## 5. The polynomial-to-dihedral bridge -/

/-- From the `ztgG`-shaped polynomial certificate
`0 ≤ 4·y1²·Δ − s²·Δ4²` (with `0 < 4·y1²·Δ`): `arctan s ≤ dihY`.
Convenience bridge over Kit A's `ztg_dihY_ge_arctan`; consumed by any
uniform-`D` shortcut on a box whose `ztgG` root leaf (scout §4.A) is
available. -/
theorem ztg_dihY_ge_arctan_of_Gpos {y1 y2 y3 y4 y5 y6 s : ℝ} (hs : 0 < s)
    (hpos : (0:ℝ) < 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)
    (hG : (0:ℝ) ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 -
        s * s * (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
          (y6 * y6)) ^ 2) :
    Real.arctan s ≤ dihY y1 y2 y3 y4 y5 y6 := by
  have hA : (0:ℝ) < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) :=
    Real.sqrt_pos.mpr hpos
  have hsq : s * s * (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)) ^ 2 ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
    linarith
  have hsq2 : (s * |deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)|) ^ 2 ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
    have e1 : (s * |deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
        (y5 * y5) (y6 * y6)|) ^ 2 = s * s * (deltaX4 (y1 * y1) (y2 * y2)
        (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2 := by
      rw [mul_pow, sq_abs]
      ring
    rw [e1]
    linarith
  have hfin : s * |deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)| ≤
      Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    have hmono := Real.sqrt_le_sqrt hsq2
    rwa [Real.sqrt_sq (mul_nonneg hs.le (abs_nonneg _))] at hmono
  exact ztg_dihY_ge_arctan hs hA hfin

/-! ## 6. Box-edge and `lmfun` constants of the corner alphabet -/

/-- The kink `2.52` sits above the whole `y1` and critical-slot ranges. -/
theorem ztg_two_hminus_le_kink : 2 * hminus ≤ 2.52 := by
  have h := Kepler.NliBanks17.nb17_two_hminus_bounds
  linarith

theorem ztg_kink_le_two_hplus : (2.52 : ℝ) ≤ 2 * hplus := by
  rw [hplus]; norm_num

theorem ztg_kink_le_sqrt8 : (2.52 : ℝ) ≤ Real.sqrt 8 := by
  have h : (2.52 : ℝ) < Real.sqrt 8 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

theorem ztg_hminus_lt_h0 : hminus < h0 := by
  have h := Kepler.NliBanks17.nb17_hminus_bounds
  have hh : h0 = 1.26 := rfl
  rw [hh]; linarith

/-- On the lower branch of the kink: `lmfun hminus = (h0 − hminus)/(h0 − 1)`. -/
theorem ztg_lmfun_hminus_eq : lmfun hminus = (h0 - hminus) / (h0 - 1) := by
  rw [lmfun, if_pos ztg_hminus_lt_h0.le]

/-- `lmfun hminus ∈ [0.108615, 0.108654]` (from the five-digit envelope
`hminus ∈ [1.23175, 1.23176]`, `nb17_hminus_bounds`). -/
theorem ztg_lmfun_hminus_bounds :
    (0.108615 : ℝ) ≤ lmfun hminus ∧ lmfun hminus ≤ 0.108654 := by
  have h := Kepler.NliBanks17.nb17_hminus_bounds
  have hh : (h0 : ℝ) = 1.26 := rfl
  rw [ztg_lmfun_hminus_eq, hh,
    show ((1.26 : ℝ) - 1) = 0.26 from by norm_num]
  constructor
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 0.26)]
    linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 0.26)]
    linarith

/-- At the kink half-argument (`2.52 / 2 = h0`): `lmfun = 0` exactly. -/
theorem ztg_lmfun_kink_zero : lmfun (2.52 / 2) = 0 := by
  have hh : h0 = 1.26 := rfl
  rw [lmfun, if_pos (by rw [hh]; norm_num), hh]
  norm_num

/-! ## 7. The slice kit (the `NliBanks9.boxInf` world) -/

/-- The `Fin 6` packaging of `ztgMain`. -/
noncomputable def ztg_main_fun (i3 i4 i5 i6 : ℕ) (x : Fin 6 → ℝ) : ℝ :=
  ztgMain i3 i4 i5 i6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-- Bridge from the `Fin 6` world back to the six-argument form. -/
theorem ztg_main_fun_cons (i3 i4 i5 i6 : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    ztg_main_fun i3 i4 i5 i6 ![y1, y2, y3, y4, y5, y6] =
      ztgMain i3 i4 i5 i6 y1 y2 y3 y4 y5 y6 := by
  simp [ztg_main_fun]

/-- Kink coordinate: per-slice piecewise concavity on `[lo, k]` and
`[k, hi]` gives the kink triple `{lo, k, hi}` as non-increasing
candidates for the slice minimum. -/
theorem ztg_step_of_concave_pair (i3 i4 i5 i6 : ℕ) (i : Fin 6)
    (x : Fin 6 → ℝ) {lo k hi : ℝ} (hlk : lo ≤ k) (hkh : k ≤ hi)
    (hxi : x i ∈ Set.Icc lo hi)
    (hl : ConcaveOn ℝ (Set.Icc lo k)
      (fun t => ztg_main_fun i3 i4 i5 i6 (Function.update x i t)))
    (hr : ConcaveOn ℝ (Set.Icc k hi)
      (fun t => ztg_main_fun i3 i4 i5 i6 (Function.update x i t))) :
    ∃ c ∈ ({lo, k, hi} : Finset ℝ),
      ztg_main_fun i3 i4 i5 i6 (Function.update x i c) ≤
      ztg_main_fun i3 i4 i5 i6 x := by
  have hmin := Kepler.NliBanks9.min_of_piecewise_concave hlk hkh hl hr hxi
  rw [Function.update_eq_self i x] at hmin
  rcases min_cases (ztg_main_fun i3 i4 i5 i6 (Function.update x i lo))
      (min (ztg_main_fun i3 i4 i5 i6 (Function.update x i k))
        (ztg_main_fun i3 i4 i5 i6 (Function.update x i hi))) with hA | hA
  · refine ⟨lo, by simp, ?_⟩
    rw [hA.1] at hmin
    exact hmin
  · rcases min_cases (ztg_main_fun i3 i4 i5 i6 (Function.update x i k))
        (ztg_main_fun i3 i4 i5 i6 (Function.update x i hi)) with hB | hB
    · refine ⟨k, by simp, ?_⟩
      rw [hA.1, hB.1] at hmin
      exact hmin
    · refine ⟨hi, by simp, ?_⟩
      rw [hA.1, hB.1] at hmin
      exact hmin

/-- Non-kink coordinate: whole-interval concavity gives the endpoint pair
`{lo, hi}`. -/
theorem ztg_step_of_concave (i3 i4 i5 i6 : ℕ) (i : Fin 6) (x : Fin 6 → ℝ)
    {lo hi : ℝ} (hxi : x i ∈ Set.Icc lo hi)
    (hconc : ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => ztg_main_fun i3 i4 i5 i6 (Function.update x i t))) :
    ∃ c ∈ ({lo, hi} : Finset ℝ),
      ztg_main_fun i3 i4 i5 i6 (Function.update x i c) ≤
      ztg_main_fun i3 i4 i5 i6 x := by
  have hlohi : lo ≤ hi := le_trans hxi.1 hxi.2
  have hmin := Kepler.NliBanks9.concaveOn_min_endpoints hlohi hconc hxi
  rw [Function.update_eq_self i x] at hmin
  rcases min_cases (ztg_main_fun i3 i4 i5 i6 (Function.update x i lo))
      (ztg_main_fun i3 i4 i5 i6 (Function.update x i hi)) with hA | hA
  · refine ⟨lo, by simp, ?_⟩
    rw [hA.1] at hmin
    exact hmin
  · refine ⟨hi, by simp, ?_⟩
    rw [hA.1] at hmin
    exact hmin

/-- Two-piece mono-up coordinate (the 2.2-cut regular slots of `0_1_0_0`):
the low endpoint alone is a non-increasing candidate. -/
theorem ztg_step_of_mono_up_pair (i3 i4 i5 i6 : ℕ) (i : Fin 6) (x : Fin 6 → ℝ)
    {lo k hi : ℝ} (hlk : lo ≤ k) (_hkh : k ≤ hi)
    (hxi : x i ∈ Set.Icc lo hi)
    (hlo : ∀ t ∈ Set.Icc lo k, ztg_main_fun i3 i4 i5 i6 (Function.update x i lo) ≤
      ztg_main_fun i3 i4 i5 i6 (Function.update x i t))
    (hk : ∀ t ∈ Set.Icc k hi, ztg_main_fun i3 i4 i5 i6 (Function.update x i k) ≤
      ztg_main_fun i3 i4 i5 i6 (Function.update x i t)) :
    ∃ c ∈ ({lo} : Finset ℝ),
      ztg_main_fun i3 i4 i5 i6 (Function.update x i c) ≤
      ztg_main_fun i3 i4 i5 i6 x := by
  have hklo : ztg_main_fun i3 i4 i5 i6 (Function.update x i lo) ≤
      ztg_main_fun i3 i4 i5 i6 (Function.update x i k) :=
    hlo k ⟨hlk, le_rfl⟩
  by_cases hxi_le : x i ≤ k
  · refine ⟨lo, by simp, ?_⟩
    have h1 := hlo (x i) ⟨hxi.1, hxi_le⟩
    rwa [Function.update_eq_self i x] at h1
  · have hxk : k ≤ x i := (not_le.mp hxi_le).le
    refine ⟨lo, by simp, ?_⟩
    calc ztg_main_fun i3 i4 i5 i6 (Function.update x i lo) ≤
          ztg_main_fun i3 i4 i5 i6 (Function.update x i k) := hklo
      _ ≤ ztg_main_fun i3 i4 i5 i6 (Function.update x i (x i)) :=
          hk (x i) ⟨hxk, hxi.2⟩
      _ = ztg_main_fun i3 i4 i5 i6 x := by rw [Function.update_eq_self i x]

/-- Two-piece mono-dn coordinate (the mirror): on both pieces the slice is
decreasing, so the high endpoint alone is a non-increasing candidate. -/
theorem ztg_step_of_mono_dn_pair (i3 i4 i5 i6 : ℕ) (i : Fin 6) (x : Fin 6 → ℝ)
    {lo k hi : ℝ} (_hlk : lo ≤ k) (hkh : k ≤ hi)
    (hxi : x i ∈ Set.Icc lo hi)
    (hhi : ∀ t ∈ Set.Icc k hi, ztg_main_fun i3 i4 i5 i6 (Function.update x i hi) ≤
      ztg_main_fun i3 i4 i5 i6 (Function.update x i t))
    (hk : ∀ t ∈ Set.Icc lo k, ztg_main_fun i3 i4 i5 i6 (Function.update x i k) ≤
      ztg_main_fun i3 i4 i5 i6 (Function.update x i t)) :
    ∃ c ∈ ({hi} : Finset ℝ),
      ztg_main_fun i3 i4 i5 i6 (Function.update x i c) ≤
      ztg_main_fun i3 i4 i5 i6 x := by
  have hkh' : ztg_main_fun i3 i4 i5 i6 (Function.update x i hi) ≤
      ztg_main_fun i3 i4 i5 i6 (Function.update x i k) :=
    hhi k ⟨le_rfl, hkh⟩
  by_cases hxi_ge : k ≤ x i
  · refine ⟨hi, by simp, ?_⟩
    have h1 := hhi (x i) ⟨hxi_ge, hxi.2⟩
    rwa [Function.update_eq_self i x] at h1
  · have hxk : x i ≤ k := (not_le.mp hxi_ge).le
    refine ⟨hi, by simp, ?_⟩
    calc ztg_main_fun i3 i4 i5 i6 (Function.update x i hi) ≤
          ztg_main_fun i3 i4 i5 i6 (Function.update x i k) := hkh'
      _ ≤ ztg_main_fun i3 i4 i5 i6 (Function.update x i (x i)) :=
          hk (x i) ⟨hxi.1, hxk⟩
      _ = ztg_main_fun i3 i4 i5 i6 x := by rw [Function.update_eq_self i x]

/-- All candidate values positive ⇒ the `boxInf` is positive
(via `Finset.inf'_mem` on the set of positive reals, closed under `min`). -/
theorem ztg_boxInf_pos {n : ℕ} {cands : Fin n → Finset ℝ}
    (hne : ∀ i, (cands i).Nonempty) {f : (Fin n → ℝ) → ℝ}
    (h : ∀ s ∈ Finset.univ.pi cands,
      0 < f (fun i => s i (Finset.mem_univ i))) :
    0 < Kepler.NliBanks9.boxInf cands hne f := by
  unfold Kepler.NliBanks9.boxInf
  refine Finset.inf'_mem {r : ℝ | 0 < r} ?_ _ _ _ h
  intro a ha b hb
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]; exact ha
  · rw [min_eq_right hab]; exact hb

/-- **The slice-corners assembly** (route B, per debt): per-coordinate
`hstep` candidates plus positivity at every corner of the candidate product
give `ztgMain > 0` through the whole box.  The corner hypothesis is a
nested six-fold bounded `∀` over the candidate sets (consumable by
`Finset.mem_insert` case splits); the bridge to the `Finset.pi` world of
`boxInf_le_of_slice_min` is done once, here. -/
theorem ztg_main_pos_of_slice_corners (i3 i4 i5 i6 : ℕ)
    (lo hi : Fin 6 → ℝ) (cands : Fin 6 → Finset ℝ)
    (hne : ∀ i, (cands i).Nonempty)
    (hsub : ∀ i, ∀ c ∈ cands i, c ∈ Set.Icc (lo i) (hi i))
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      ∃ c ∈ cands i, ztg_main_fun i3 i4 i5 i6 (Function.update x i c)
        ≤ ztg_main_fun i3 i4 i5 i6 x)
    (hcorner : ∀ c0 ∈ cands 0, ∀ c1 ∈ cands 1, ∀ c2 ∈ cands 2,
      ∀ c3 ∈ cands 3, ∀ c4 ∈ cands 4, ∀ c5 ∈ cands 5,
      0 < ztgMain i3 i4 i5 i6 c0 c1 c2 c3 c4 c5) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      0 < ztg_main_fun i3 i4 i5 i6 x := by
  have hpos : ∀ s ∈ Finset.univ.pi cands,
      0 < ztg_main_fun i3 i4 i5 i6 (fun i => s i (Finset.mem_univ i)) := by
    intro s hs
    have hmem := Finset.mem_pi.mp hs
    show 0 < ztgMain i3 i4 i5 i6 (s 0 _) (s 1 _) (s 2 _) (s 3 _) (s 4 _) (s 5 _)
    exact hcorner (s 0 (Finset.mem_univ 0)) (hmem 0 (Finset.mem_univ 0))
      (s 1 (Finset.mem_univ 1)) (hmem 1 (Finset.mem_univ 1))
      (s 2 (Finset.mem_univ 2)) (hmem 2 (Finset.mem_univ 2))
      (s 3 (Finset.mem_univ 3)) (hmem 3 (Finset.mem_univ 3))
      (s 4 (Finset.mem_univ 4)) (hmem 4 (Finset.mem_univ 4))
      (s 5 (Finset.mem_univ 5)) (hmem 5 (Finset.mem_univ 5))
  have h0 : 0 < Kepler.NliBanks9.boxInf cands hne (ztg_main_fun i3 i4 i5 i6) :=
    ztg_boxInf_pos hne hpos
  intro x hx
  exact lt_of_lt_of_le h0
    (Kepler.NliBanks9.boxInf_le_of_slice_min lo hi cands hne hsub hstep hx)

/-! ## 8. The pointwise two-scalar assembly -/

/-- Pointwise corner form of `ztg_of_global_bounds`: separate `γ4` and
`dihY` lower bounds at one point plus the numeric side condition give
`ztgMain > 0` there.  Consumed once per corner-value certificate; the
per-corner `G` and `D` are the corner's own tight brackets, so no margin
is lost against the razor `0_0_0_0` case. -/
theorem ztg_main_pos_of_gD (i3 i4 i5 i6 : ℕ) (y1 y2 y3 y4 y5 y6 G D : ℝ)
    (hG : G ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (hD : D ≤ dihY y1 y2 y3 y4 y5 y6)
    (hnum : aSpine5 + bSpine5 * D <
      G / ztgW i3 i4 i5 i6 + ztgM i3 i4 i5 i6 * betaBumpLb) :
    0 < ztgMain i3 i4 i5 i6 y1 y2 y3 y4 y5 y6 := by
  have hw : (0:ℝ) < ztgW i3 i4 i5 i6 := ztgW_pos i3 i4 i5 i6
  have hdiv : G / ztgW i3 i4 i5 i6 ≤
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / ztgW i3 i4 i5 i6 :=
    div_le_div_of_nonneg_right hG hw.le
  have hb5 : bSpine5 < 0 := by rw [bSpine5]; norm_num
  have hbnd : aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6 ≤
      aSpine5 + bSpine5 * D := by nlinarith [hD, hb5]
  unfold ztgMain
  linarith

/-! ## 9. Smoke tests (consumer interfaces, end to end) -/

/-- **W3 corner smoke**: the `(2hplus, 2⁵)` corner of `0_0_0_0` (the `hi`
endpoint of its `y1` piece) is positive through the pointwise two-scalar
assembly, consuming the in-tree V5 corner bound `g4v_corner_2hplus_bounds`,
the in-tree slot reduction `g4v_2hp_dih_eq1` and the in-tree `A1` bracket.
This is exactly the per-corner shape the W1–W4 corner certificates use. -/
theorem ztg_smoke_0000_2hplus_pos :
    0 < ztgMain 0 0 0 0 (2 * hplus) 2 2 2 2 2 := by
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hplus) 2 2 2 2 2
    0.00000223 1.46212033 ?_ ?_ ?_
  · exact g4v_corner_2hplus_bounds.1
  · rw [g4v_2hp_dih_eq1]
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    obtain ⟨ha1, ha2⟩ := g4v_atan_A1_bounds
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-- **Slice-assembly smoke**: the degenerate box `lo = hi = (2hplus, 2⁵)`
through the full slice-corners template, exercising the `hstep` and
`hcorner` consumer patterns (singleton candidate sets, `Finset.mem_singleton`
substitutions). -/
theorem ztg_smoke_slice_assembly :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc
        (![2 * hplus, 2, 2, 2, 2, 2] j) (![2 * hplus, 2, 2, 2, 2, 2] j)) →
      0 < ztg_main_fun 0 0 0 0 x := by
  refine ztg_main_pos_of_slice_corners 0 0 0 0
    ![2 * hplus, 2, 2, 2, 2, 2] ![2 * hplus, 2, 2, 2, 2, 2]
    (fun i => {![2 * hplus, 2, 2, 2, 2, 2] i}) ?_ ?_ ?_ ?_
  · intro i
    exact ⟨![2 * hplus, 2, 2, 2, 2, 2] i, by simp⟩
  · intro i c hc
    simp only [Finset.mem_singleton] at hc
    obtain rfl := hc
    exact ⟨le_rfl, le_rfl⟩
  · intro i x hx
    refine ⟨![2 * hplus, 2, 2, 2, 2, 2] i, by simp, ?_⟩
    have hxi : x i = ![2 * hplus, 2, 2, 2, 2, 2] i :=
      (hx i).2.antisymm (hx i).1
    have h1 : Function.update x i (![2 * hplus, 2, 2, 2, 2, 2] i) = x := by
      rw [← hxi, Function.update_eq_self]
    calc ztg_main_fun 0 0 0 0 (Function.update x i (![2 * hplus, 2, 2, 2, 2, 2] i))
        = ztg_main_fun 0 0 0 0 x := by rw [h1]
      _ ≤ ztg_main_fun 0 0 0 0 x := le_rfl
  · intro c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5
    simp only [Finset.mem_singleton] at hc0 hc1 hc2 hc3 hc4 hc5
    obtain rfl := hc0
    obtain rfl := hc1
    obtain rfl := hc2
    obtain rfl := hc3
    obtain rfl := hc4
    obtain rfl := hc5
    simpa using ztg_smoke_0000_2hplus_pos

/-! ## Axiom audit (house style) -/

#print axioms ztg_atn2_le
#print axioms ztg_dihY_le_arctan
#print axioms ztg_dihY_eq_br1
#print axioms ztg_dihY_eq_br2
#print axioms ztg_dihY_eq_br3
#print axioms ztg_sqrt_bounds
#print axioms ztg_atan_sqrt_div_bounds
#print axioms ztg_atan_shift_add
#print axioms ztg_arctan_5_133_bounds
#print axioms ztg_arctan_19_119_bounds
#print axioms ztg_arctan_21_179_bounds
#print axioms ztg_arctan_9_13_bounds
#print axioms ztg_arctan_69_64_bounds
#print axioms ztg_arctan_69_50_bounds
#print axioms ztg_arctan_79_100_bounds
#print axioms ztg_dihY_ge_arctan_of_Gpos
#print axioms ztg_two_hminus_le_kink
#print axioms ztg_kink_le_two_hplus
#print axioms ztg_kink_le_sqrt8
#print axioms ztg_hminus_lt_h0
#print axioms ztg_lmfun_hminus_eq
#print axioms ztg_lmfun_hminus_bounds
#print axioms ztg_lmfun_kink_zero
#print axioms ztg_main_fun
#print axioms ztg_main_fun_cons
#print axioms ztg_step_of_concave_pair
#print axioms ztg_step_of_concave
#print axioms ztg_step_of_mono_up_pair
#print axioms ztg_step_of_mono_dn_pair
#print axioms ztg_boxInf_pos
#print axioms ztg_main_pos_of_slice_corners
#print axioms ztg_main_pos_of_gD
#print axioms ztg_smoke_0000_2hplus_pos
#print axioms ztg_smoke_slice_assembly

end Kepler.Text

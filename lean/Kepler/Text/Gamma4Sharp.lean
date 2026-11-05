/-
Kepler.Text.Gamma4Sharp — corner values of the fake 4-cell volume deficit
`gamma4fgcy` at the two extreme configurations of the TSKAJXY sharp boxes,
plus the `lmfun (√2) = 0` cutoff branch.

Lane `gamma4-sharp` (ticket: `bank_TSKAJXYRIBCYXUsharp` /
`bank_TSKAJXYIYOUOBFsharpv2`, HOL ineq.hl:165 / :242).  The two bank boxes
`[2,2.001]^6` and `[2hplus,√8]×[2,2.001]²×[2,2hmin]×[2,2.001]²` both touch
the corner where every edge length is `2` (and the second also the corner
where one edge length is `√8` and five are `2`); at those corners the
deficit is *exactly* zero, which is the anchor of the
"corner value + per-variable monotonicity" route.

Contents (all standard-three, no certificate data):
* `gamma4_at_regular`: `gamma4fgcy 2 2 2 2 2 2 lmfun = 0`.  The regular
  tetrahedron: `dihY 2^6 = arccos(1/3)`, `solY 2^6 = sol0`,
  `volY 2^6 = √8/3`, `lmfun 1 = 1`; the `vol4f` side collapses to
  `(8√2/(π·tau0))·(2·sol0² − (6·sol0−π)·arccos(1/3))`, and
  `12·(2·sol0² − (6·sol0−π)·arccos(1/3)) = π·tau0` with
  `sol0 = 3·arccos(1/3) − π`, `tau0 = 4π − 20·sol0`.
* `gamma4_at_sqrt8`: `gamma4fgcy (√8) 2 2 2 2 2 lmfun = 0`.  The flat-family
  corner `y1 = √8`: the four `solY` summands are `3(π−2a)` and the six
  weighted `dihY` summands `3(π−a)` with `a = arccos(1/3)`, and
  `lmfun (√8/2) = lmfun (√2) = 0` (`√2 > h0 = 1.26`).
-/
import Kepler.Text.PackingAuto21

set_option maxHeartbeats 5000000

namespace Kepler.Text

/-! ## Square-root normalisations -/

private theorem g4s_sqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2)]
  rw [show Real.sqrt ((2 : ℝ) ^ 2) = 2 from Real.sqrt_sq (by norm_num)]

private theorem g4s_sqrt128 : Real.sqrt 128 = 8 * Real.sqrt 2 := by
  rw [show (128 : ℝ) = 8 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 ^ 2)]
  rw [show Real.sqrt ((8 : ℝ) ^ 2) = 8 from Real.sqrt_sq (by norm_num)]

/-! ## `dihY` at the regular configuration -/

/-- The regular-tetrahedron dihedral: `dih_y 2 2 2 2 2 2 = arccos (1/3)`.
Proof route as PA38 (`p38_dihY222222`): `delta_x = 128`, `delta_x4 = 16`,
the `atn2` argument pair is `(32√2, −16)` on the `|y| < x` branch, and
`arctan (1/(2√2)) = arcsin (1/3)`. -/
private theorem g4s_dihY222222 : dihY 2 2 2 2 2 2 = Real.arccos (1 / 3) := by
  have hdx : (deltaX 4 4 4 4 4 4 : ℝ) = 128 := by norm_num [deltaX]
  have hdx4 : (deltaX4 4 4 4 4 4 4 : ℝ) = 16 := by norm_num [deltaX4]
  have hd : dihY 2 2 2 2 2 2 = Real.pi / 2 + atn2 (Real.sqrt 2048) (-16) := by
    simp only [dihY, dihXf]
    norm_num [hdx, hdx4]
  have hsqrt2 : Real.sqrt (2048 : ℝ) = 32 * Real.sqrt 2 := by
    rw [show (2048 : ℝ) = 1024 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Real.sin (Real.arctan (1 / (2 * Real.sqrt 2))) = 1 / 3 := by
    rw [Real.sin_arctan]
    have hden : (1 : ℝ) + (1 / (2 * Real.sqrt 2)) ^ 2 = 9 / 8 := by
      have e1 : (1 / (2 * Real.sqrt 2)) ^ 2 = 1 / (2 * Real.sqrt 2) ^ 2 := by
        rw [one_div_pow]
      have e2 : (2 * Real.sqrt 2) ^ 2 = 8 := by rw [mul_pow, hsq2]; norm_num
      rw [e1, e2]
      norm_num
    have hr8 : Real.sqrt (9 / 8) = 3 / (2 * Real.sqrt 2) := by
      have hval : (9 / 8 : ℝ) = (3 / (2 * Real.sqrt 2)) ^ 2 := by
        rw [div_pow, mul_pow, hsq2]
        norm_num
      rw [hval, Real.sqrt_sq (by positivity)]
    rw [hden, hr8]
    field_simp
  have hθ : Real.arcsin (1 / 3) = Real.arctan (1 / (2 * Real.sqrt 2)) := by
    rw [← hs]
    obtain ⟨hm1, hm2⟩ := Real.arctan_mem_Ioo (1 / (2 * Real.sqrt 2))
    exact Real.arcsin_sin' ⟨le_of_lt hm1, le_of_lt hm2⟩
  have hv : atn2 (32 * Real.sqrt 2) (-16) = -(Real.arcsin (1 / 3)) := by
    have h1s : (1 : ℝ) < Real.sqrt 2 :=
      (Real.lt_sqrt (x := (1 : ℝ)) (by norm_num)).mpr (by norm_num)
    have hbr : |(-16 : ℝ)| < 32 * Real.sqrt 2 := by
      rw [abs_of_neg (by norm_num : (-16 : ℝ) < 0), neg_neg]
      calc (16 : ℝ) = 16 * 1 := by ring
        _ < 16 * (2 * Real.sqrt 2) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
        _ = 32 * Real.sqrt 2 := by ring
    have hconv : (-16 : ℝ) / (32 * Real.sqrt 2) = -(1 / (2 * Real.sqrt 2)) := by
      field_simp
      ring
    simp only [atn2, hbr, if_true, hconv, Real.arctan_neg, ← hθ]
  rw [hd, hsqrt2, hv, Real.arccos_eq_pi_div_two_sub_arcsin (1 / 3)]
  ring

/-! ## The `arctan (1/√2) = arccos(1/3)/2` bridge -/

/-- `2 · arctan (1/√2) = arccos (1/3)`: both sides lie in `[0, π]` and have
cosine `1/3` (`cos_two_mul` + `cos_arctan`). -/
private theorem g4s_arctan_half :
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

/-! ## `lmfun` at the cutoff -/

private theorem g4s_lmfun_one : lmfun (2 / 2) = 1 := by
  norm_num [lmfun, h0]

/-- `tau0 = 4π − 20·sol0 > 0`, from `arccos(1/3) ≤ π/2 − 1/3` (the same
`sin x < x` chain PA20 `HJKDESR1a_1cell` runs). -/
private theorem g4s_tau0_pos : 0 < tau0 := by
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have ha : Real.arccos (1 / 3) ≤ Real.pi / 2 - 1 / 3 := by
    have hsin : Real.sin (1 / 3) ≤ 1 / 3 := le_of_lt (Real.sin_lt (by norm_num))
    have hcw : Real.cos (Real.pi / 2 - 1 / 3) = Real.sin (1 / 3) :=
      Real.cos_pi_div_two_sub (1 / 3)
    have hstep : Real.arccos (1 / 3)
        ≤ Real.arccos (Real.cos (Real.pi / 2 - 1 / 3)) :=
      Real.arccos_le_arccos (hcw.trans_le hsin)
    rw [Real.arccos_cos (by linarith) (by linarith)] at hstep
    exact hstep
  have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
  have h0' : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  rw [h0, h0']
  linarith

/-- `lmfun (√2) = 0`: the `√2 > h0 = 1.26` branch. -/
theorem lmfun_sqrt8_div_two : lmfun (Real.sqrt 8 / 2) = 0 := by
  have hs : Real.sqrt 8 / 2 = Real.sqrt 2 := by
    rw [g4s_sqrt8]; ring
  rw [hs]
  have hgt : h0 < Real.sqrt 2 := by
    have hsq : h0 ^ 2 < 2 := by norm_num [h0]
    exact Real.lt_sqrt_of_sq_lt hsq
  show (if Real.sqrt 2 ≤ h0 then (h0 - Real.sqrt 2) / (h0 - 1) else 0) = 0
  rw [if_neg (by linarith)]

/-! ## Corner 1: the all-2s configuration -/

/-- The `vol4f` side at the all-2s point, in factored form. -/
private theorem g4s_vol4f_regular :
    vol4f 2 2 2 2 2 2 lmfun =
      (8 * Real.sqrt 2 / (Real.pi * tau0)) *
        (2 * sol0 ^ 2 - (6 * sol0 - Real.pi) * Real.arccos (1 / 3)) := by
  have ha : dihY 2 2 2 2 2 2 = Real.arccos (1 / 3) := g4s_dihY222222
  have hsol : solY 2 2 2 2 2 2 = sol0 := by
    simp only [solY, ha, sol0]; ring
  have hl : lmfun (2 / 2) = 1 := g4s_lmfun_one
  have htau : tau0 ≠ 0 := ne_of_gt g4s_tau0_pos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold vol4f
  simp only [hsol, ha, hl]
  unfold mm1 mm2
  rw [g4s_sqrt8]
  field_simp
  ring

/-- The closing arithmetic identity of the regular corner:
`12·(2·sol0² − (6·sol0−π)·arccos(1/3)) = π·tau0`. -/
private theorem g4s_key_regular :
    2 * sol0 ^ 2 - (6 * sol0 - Real.pi) * Real.arccos (1 / 3) =
      Real.pi * tau0 / 12 := by
  have h : 12 * (2 * sol0 ^ 2 - (6 * sol0 - Real.pi) * Real.arccos (1 / 3))
      = Real.pi * tau0 := by
    simp only [sol0, tau0]
    ring
  rw [eq_div_iff (by norm_num : (12 : ℝ) ≠ 0), mul_comm]
  exact h

theorem gamma4_at_regular : gamma4fgcy 2 2 2 2 2 2 lmfun = 0 := by
  have hvY : volY 2 2 2 2 2 2 = Real.sqrt 8 / 3 := by
    unfold volY volXf
    norm_num [deltaX]
    rw [g4s_sqrt128, g4s_sqrt8]
    ring
  have htau : tau0 ≠ 0 := ne_of_gt g4s_tau0_pos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold gamma4fgcy
  rw [hvY, g4s_vol4f_regular, g4s_key_regular, g4s_sqrt8]
  field_simp
  ring

/-! ## Corner 2: the `y1 = √8` configuration

At `y = (√8, 2, 2, 2, 2, 2)` the `x`-space edge squares are `(8,4,4,4,4,4)`
up to permutation; three dihedral values occur, according to the slot of
the `8` (all with `delta_x = 128`):

* slot 1 (`delta_x4 = 0`): `dih = π/2`;
* slots 2,3,5,6 (`delta_x4 = 32`): `dih = π/2 − arccos(1/3)/2`
  (the `|y| < x` branch gives `arctan (1/√2)`, and
  `2·arctan(1/√2) = arccos(1/3)`);
* slot 4 (`delta_x4 = −16`): `dih = π − arccos(1/3)`
  (`arctan (1/(2√2)) = arcsin(1/3)`). -/

/-- `arcsin (1/3) = arctan (1/(2√2))` (PA38 kernel). -/
private theorem g4s_arcsin_third :
    Real.arcsin (1 / 3) = Real.arctan (1 / (2 * Real.sqrt 2)) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Real.sin (Real.arctan (1 / (2 * Real.sqrt 2))) = 1 / 3 := by
    rw [Real.sin_arctan]
    have hden : (1 : ℝ) + (1 / (2 * Real.sqrt 2)) ^ 2 = 9 / 8 := by
      have e1 : (1 / (2 * Real.sqrt 2)) ^ 2 = 1 / (2 * Real.sqrt 2) ^ 2 := by
        rw [one_div_pow]
      have e2 : (2 * Real.sqrt 2) ^ 2 = 8 := by rw [mul_pow, hsq2]; norm_num
      rw [e1, e2]
      norm_num
    have hr8 : Real.sqrt (9 / 8) = 3 / (2 * Real.sqrt 2) := by
      have hval : (9 / 8 : ℝ) = (3 / (2 * Real.sqrt 2)) ^ 2 := by
        rw [div_pow, mul_pow, hsq2]
        norm_num
      rw [hval, Real.sqrt_sq (by positivity)]
    rw [hden, hr8]
    field_simp
  rw [← hs]
  obtain ⟨hm1, hm2⟩ := Real.arctan_mem_Ioo (1 / (2 * Real.sqrt 2))
  exact Real.arcsin_sin' ⟨le_of_lt hm1, le_of_lt hm2⟩

/-- Class A: the `8` in slot 1 (`delta_x = 128`, `delta_x4 = 0`). -/
private theorem g4s_dihXf_A {x2 x3 x4 x5 x6 : ℝ}
    (hd : deltaX 8 x2 x3 x4 x5 x6 = 128)
    (hd4 : deltaX4 8 x2 x3 x4 x5 x6 = 0) :
    dihXf 8 x2 x3 x4 x5 x6 = Real.pi / 2 := by
  have hs : Real.sqrt (4 * 8 * deltaX 8 x2 x3 x4 x5 x6) = 64 := by
    rw [hd, show (4 : ℝ) * 8 * 128 = 64 ^ 2 by norm_num,
      show Real.sqrt ((64 : ℝ) ^ 2) = 64 from Real.sqrt_sq (by norm_num)]
  unfold dihXf
  rw [hs, hd4, neg_zero, atn2, if_pos (by norm_num), zero_div, Real.arctan_zero]
  ring

/-- Class B: the `8` in a slot `≠ 1,4` (`delta_x = 128`, `delta_x4 = 32`). -/
private theorem g4s_dihXf_B {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : x1 = 4)
    (hd : deltaX x1 x2 x3 x4 x5 x6 = 128)
    (hd4 : deltaX4 x1 x2 x3 x4 x5 x6 = 32) :
    dihXf x1 x2 x3 x4 x5 x6 = Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  subst h1
  have hs : Real.sqrt (4 * 4 * deltaX 4 x2 x3 x4 x5 x6) = 32 * Real.sqrt 2 := by
    rw [hd, show (4 : ℝ) * 4 * 128 = 32 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 32 ^ 2),
      show Real.sqrt ((32 : ℝ) ^ 2) = 32 from Real.sqrt_sq (by norm_num)]
  unfold dihXf
  rw [hs, hd4]
  have h1s : (1 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (x := (1 : ℝ)) (by norm_num)).mpr (by norm_num)
  have hbr : |(-32 : ℝ)| < 32 * Real.sqrt 2 := by
    rw [abs_of_neg (by norm_num : (-32 : ℝ) < 0), neg_neg]
    calc (32 : ℝ) = 32 * 1 := by ring
      _ < 32 * Real.sqrt 2 := mul_lt_mul_of_pos_left h1s (by norm_num)
  rw [atn2, if_pos hbr]
  have hconv : (-32 : ℝ) / (32 * Real.sqrt 2) = -(1 / Real.sqrt 2) := by
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  rw [hconv, Real.arctan_neg, ← g4s_arctan_half]
  ring

/-- Class C: the `8` in slot 4 (`delta_x = 128`, `delta_x4 = -16`). -/
private theorem g4s_dihXf_C {x1 x2 x3 x5 x6 : ℝ} (h1 : x1 = 4)
    (hd : deltaX x1 x2 x3 8 x5 x6 = 128)
    (hd4 : deltaX4 x1 x2 x3 8 x5 x6 = -16) :
    dihXf x1 x2 x3 8 x5 x6 = Real.pi - Real.arccos (1 / 3) := by
  subst h1
  have hs : Real.sqrt (4 * 4 * deltaX 4 x2 x3 8 x5 x6) = 32 * Real.sqrt 2 := by
    rw [hd, show (4 : ℝ) * 4 * 128 = 32 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 32 ^ 2),
      show Real.sqrt ((32 : ℝ) ^ 2) = 32 from Real.sqrt_sq (by norm_num)]
  unfold dihXf
  rw [hs, hd4, neg_neg]
  have hbr : |(16 : ℝ)| < 32 * Real.sqrt 2 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)]
    have h1s : (1 : ℝ) < Real.sqrt 2 :=
      (Real.lt_sqrt (x := (1 : ℝ)) (by norm_num)).mpr (by norm_num)
    calc (16 : ℝ) = 16 * 1 := by ring
      _ < 16 * (2 * Real.sqrt 2) := mul_lt_mul_of_pos_left (by linarith) (by norm_num)
      _ = 32 * Real.sqrt 2 := by ring
  rw [atn2, if_pos hbr]
  have hconv : (16 : ℝ) / (32 * Real.sqrt 2) = 1 / (2 * Real.sqrt 2) := by
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    norm_num
  rw [hconv, ← g4s_arcsin_third, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

/-! ### The six `dihY` values at `(√8, 2, 2, 2, 2, 2)` -/

private theorem g4s_dihY_r1 : dihY (Real.sqrt 8) 2 2 2 2 2 = Real.pi / 2 := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  simp only [dihY, h88, h4]
  exact g4s_dihXf_A (by norm_num [deltaX]) (by norm_num [deltaX4])

private theorem g4s_dihY_r2 : dihY 2 2 (Real.sqrt 8) 2 2 2 =
    Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  simp only [dihY, h88, h4]
  exact g4s_dihXf_B rfl (by norm_num [deltaX]) (by norm_num [deltaX4])

private theorem g4s_dihY_r3 : dihY 2 (Real.sqrt 8) 2 2 2 2 =
    Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  simp only [dihY, h88, h4]
  exact g4s_dihXf_B rfl (by norm_num [deltaX]) (by norm_num [deltaX4])

private theorem g4s_dihY_r4 : dihY 2 2 2 (Real.sqrt 8) 2 2 =
    Real.pi - Real.arccos (1 / 3) := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  simp only [dihY, h88, h4]
  exact g4s_dihXf_C rfl (by norm_num [deltaX]) (by norm_num [deltaX4])

private theorem g4s_dihY_r5 : dihY 2 2 2 2 (Real.sqrt 8) 2 =
    Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  simp only [dihY, h88, h4]
  exact g4s_dihXf_B rfl (by norm_num [deltaX]) (by norm_num [deltaX4])

private theorem g4s_dihY_r6 : dihY 2 2 2 2 2 (Real.sqrt 8) =
    Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  simp only [dihY, h88, h4]
  exact g4s_dihXf_B rfl (by norm_num [deltaX]) (by norm_num [deltaX4])

/-! ### The `solY` summands at the `√8` corner -/

private theorem g4s_solY_sqrt8_near : solY (Real.sqrt 8) 2 2 2 2 2 =
    Real.pi / 2 - Real.arccos (1 / 3) := by
  have h : solY (Real.sqrt 8) 2 2 2 2 2 =
      dihY (Real.sqrt 8) 2 2 2 2 2 + dihY 2 2 (Real.sqrt 8) 2 2 2 +
        dihY 2 (Real.sqrt 8) 2 2 2 2 - Real.pi := rfl
  rw [h, g4s_dihY_r1, g4s_dihY_r2, g4s_dihY_r3]
  ring

private theorem g4s_solY_sqrt8_far : solY 2 2 2 (Real.sqrt 8) 2 2 =
    Real.pi - 2 * Real.arccos (1 / 3) := by
  have h : solY 2 2 2 (Real.sqrt 8) 2 2 =
      dihY 2 2 2 (Real.sqrt 8) 2 2 + dihY 2 2 2 2 2 (Real.sqrt 8) +
        dihY 2 2 2 2 (Real.sqrt 8) 2 - Real.pi := rfl
  rw [h, g4s_dihY_r4, g4s_dihY_r6, g4s_dihY_r5]
  ring

/-- The `vol4f` side at the `√8` corner, in factored form. -/
private theorem g4s_vol4f_sqrt8 :
    vol4f (Real.sqrt 8) 2 2 2 2 2 lmfun =
      (2 * Real.sqrt 2 / (Real.pi * tau0)) *
        (6 * sol0 * (Real.pi - 2 * Real.arccos (1 / 3)) -
          2 * (6 * sol0 - Real.pi) * (Real.pi - Real.arccos (1 / 3))) := by
  have hl1 : lmfun (2 / 2) = 1 := g4s_lmfun_one
  have hl8 : lmfun (Real.sqrt 8 / 2) = 0 := lmfun_sqrt8_div_two
  have htau : tau0 ≠ 0 := ne_of_gt g4s_tau0_pos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold vol4f
  rw [g4s_solY_sqrt8_near, g4s_solY_sqrt8_far]
  simp only [g4s_dihY_r1, g4s_dihY_r2, g4s_dihY_r3, g4s_dihY_r4, hl1, hl8,
    zero_mul]
  unfold mm1 mm2
  rw [g4s_sqrt8]
  field_simp
  ring

/-- The closing arithmetic identity of the `√8` corner. -/
private theorem g4s_key_sqrt8 :
    6 * sol0 * (Real.pi - 2 * Real.arccos (1 / 3)) -
      2 * (6 * sol0 - Real.pi) * (Real.pi - Real.arccos (1 / 3)) =
      Real.pi * tau0 / 3 := by
  have h : 18 * sol0 * (Real.pi - 2 * Real.arccos (1 / 3)) -
      6 * (6 * sol0 - Real.pi) * (Real.pi - Real.arccos (1 / 3)) =
      Real.pi * tau0 := by
    simp only [sol0, tau0]
    ring
  rw [eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)]
  linarith

theorem gamma4_at_sqrt8 : gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun = 0 := by
  have h88 : Real.sqrt 8 * Real.sqrt 8 = (8 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h4 : (2 * 2 : ℝ) = 4 := by norm_num
  have hvY : volY (Real.sqrt 8) 2 2 2 2 2 = Real.sqrt 8 / 3 := by
    unfold volY volXf
    simp only [h88, h4]
    norm_num [deltaX]
    rw [g4s_sqrt128, g4s_sqrt8]
    ring
  have htau : tau0 ≠ 0 := ne_of_gt g4s_tau0_pos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold gamma4fgcy
  rw [hvY, g4s_vol4f_sqrt8, g4s_key_sqrt8, g4s_sqrt8]
  field_simp
  ring

/-! ## Axiom audit (house style) -/

#print axioms Kepler.Text.gamma4_at_regular
#print axioms Kepler.Text.gamma4_at_sqrt8
#print axioms Kepler.Text.lmfun_sqrt8_div_two

end Kepler.Text

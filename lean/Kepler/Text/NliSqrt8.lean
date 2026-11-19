/-
Kepler.Text.NliSqrt8 — lane `cell3-sqrt8-build-w1` (2026-11-19): the
cone-interior debt `nliCell3QZECFICwt0sqrt8` (Assembly.lean:419; bank
`PackingAuto21.lean:221`, HOL ineq.hl:1406).

Box `[1,1]³ × [2hplus,√8] × [2,2hminus]²`, second disjunct `eta_y^2 > 2`.
Route (per the sqrt8 card fallback chain): the `w2a_cell` twin battery
`perSlot + prodMin` — the S0 chain of the reevaluation scout, zero new
mathematics:

* right disjunct: `deltaX (y4²) 2 (y5²) 2 (y6²) 2 < 0 → eta_y^2 > 2`
  (reproof of the private NliBanks18 §12 stone, ~70 lines);
* left disjunct: `0 ≤ δ` at the point, then a 26-cell certificate battery
  (30 adaptive leaves, halved by the y5↔y6 kernel symmetry), each cell closed
  by the generic `s8_cell`:

    c3Main = 1/12 − K1·(SE₁+SE₂+SE₃) + K2·(lfun(y5/2)·dih₅ + lfun(y6/2)·dih₆)

    SE_i ≤ 1/ea_iL   (matan ≤ 1 on the nonnegative branch; per-slot
                      minimum corners of the `ea*X` bodies)
    dih₅ ≥ (2/(p5h·S5H))·(1 − 4·p5h²·Dh/(3·dx5L²))
                    (prefactor product corner; matan ≥ 1−t/3 Taylor with the
                    per-cell sup of the matan argument)
    δ ≤ Dh           (δ antitone in each coordinate — clean factorizations
                      δ(A')−δ(A) = −(A'−A)·((B−4)(C−4)+2(A+A'−8)) etc.)
    margin > 0 by exact rational arithmetic (norm_num), K via the landed
    `g4v_AB_bounds` brackets.

Design/soundness data (work/ in the lane snapshot): worst cell margin
+2.6398e-4 in exact arithmetic; 22³-per-cell true-value scan of the exact
certificate, 0 violations, worst gap +0.0029; global left-branch true
minimum +3.7447e-3 (the certified corner value).

No new `axiom`/`sorry`/`native_decide`; consumed pieces all landed and
axioms-clean (`NliBanks11`, `NliBanks17`, `NliBanks20`).
-/
import Kepler.Text.PackingAuto21
import Kepler.NliBanks11
import Kepler.NliBanks17
import Kepler.NliBanks20

set_option maxHeartbeats 8000000

namespace Kepler.Text.NliSqrt8

open Kepler.Text

/-! ## 1. The kernel in slot form -/

/-- The sqrt8 cell-3 kernel on the free coordinates, in explicit slot form
(`nb11_c3_unfold` at the squared slots; the `m4 = 0` slot is killed). -/
theorem s8_c3_unfold_sq {y4 y5 y6 : ℝ} (hy4 : 0 ≤ y4) (hy5 : 0 ≤ y5)
    (hy6 : 0 ≤ y6) :
    Kepler.NliBanks11.c3Main y4 y5 y6 =
      1 / 12 - (2 * mm1 / Real.pi) *
          (solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
            solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 +
            solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2) +
        (8 * mm2 / Real.pi) *
          (lfun (y5 * 0.5) *
              dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
            lfun (y6 * 0.5) *
              dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2) :=
  by
  simp only [Kepler.NliBanks11.c3Main, yOfX, Kepler.NliBanks11.nb11_c3_unfold,
    one_mul, Real.sqrt_mul_self hy4, Real.sqrt_mul_self hy5, Real.sqrt_mul_self hy6]
  ring

/-! ## 2. Delta antitone (clean factorizations on the sqrt8 box) -/

/-- The three-coordinate Delta in square variables. -/
theorem s8_dlt_eq (A B C : ℝ) :
    deltaX A 2 B 2 C 2 = 2 * (4 * B * C - (A - B - C) ^ 2) - A * B * C := by
  rw [deltaX]
  ring

/-- `Dlt` is antitone in `A` when `B, C ≥ 4` and `A + A' ≥ 8`. -/
theorem s8_dlt_anti_a {a a' b c : ℝ} (hb : (4 : ℝ) ≤ b) (hc : (4 : ℝ) ≤ c)
    (haa : (8 : ℝ) ≤ a + a') (h : a ≤ a') :
    2 * (4 * b * c - (a' - b - c) ^ 2) - a' * b * c ≤
      2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c := by
  have hkey : (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c) -
      (2 * (4 * b * c - (a' - b - c) ^ 2) - a' * b * c)
      = (a' - a) * ((b - 4) * (c - 4) + 2 * (a + a' - 8)) := by ring
  have h1 : (0 : ℝ) ≤ b - 4 := by linarith
  have h2 : (0 : ℝ) ≤ c - 4 := by linarith
  have hbr : (0 : ℝ) ≤ (b - 4) * (c - 4) + 2 * (a + a' - 8) := by
    nlinarith [h1, h2, mul_nonneg h1 h2]
  have hpos : (0 : ℝ) ≤ a' - a := by linarith
  have hprod : (0 : ℝ) ≤ (a' - a) * ((b - 4) * (c - 4) + 2 * (a + a' - 8)) :=
    mul_nonneg hpos hbr
  linarith

/-- `Dlt` is antitone in `B` when `A, C ≥ 4` and `B + B' ≥ 8`. -/
theorem s8_dlt_anti_b {b b' a c : ℝ} (ha : (4 : ℝ) ≤ a) (hc : (4 : ℝ) ≤ c)
    (hbb : (8 : ℝ) ≤ b + b') (h : b ≤ b') :
    2 * (4 * b' * c - (a - b' - c) ^ 2) - a * b' * c ≤
      2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c := by
  have hkey : (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c) -
      (2 * (4 * b' * c - (a - b' - c) ^ 2) - a * b' * c)
      = (b' - b) * ((a - 4) * (c - 4) + 2 * (b + b' - 8)) := by ring
  have h1 : (0 : ℝ) ≤ a - 4 := by linarith
  have h2 : (0 : ℝ) ≤ c - 4 := by linarith
  have hbr : (0 : ℝ) ≤ (a - 4) * (c - 4) + 2 * (b + b' - 8) := by
    nlinarith [h1, h2, mul_nonneg h1 h2]
  have hpos : (0 : ℝ) ≤ b' - b := by linarith
  have hprod : (0 : ℝ) ≤ (b' - b) * ((a - 4) * (c - 4) + 2 * (b + b' - 8)) :=
    mul_nonneg hpos hbr
  linarith

/-- `Dlt` is antitone in `C` when `A, B ≥ 4` and `C + C' ≥ 8`. -/
theorem s8_dlt_anti_c {c c' a b : ℝ} (ha : (4 : ℝ) ≤ a) (hb : (4 : ℝ) ≤ b)
    (hcc : (8 : ℝ) ≤ c + c') (h : c ≤ c') :
    2 * (4 * b * c' - (a - b - c') ^ 2) - a * b * c' ≤
      2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c := by
  have hkey : (2 * (4 * b * c - (a - b - c) ^ 2) - a * b * c) -
      (2 * (4 * b * c' - (a - b - c') ^ 2) - a * b * c')
      = (c' - c) * ((a - 4) * (b - 4) + 2 * (c + c' - 8)) := by ring
  have h1 : (0 : ℝ) ≤ a - 4 := by linarith
  have h2 : (0 : ℝ) ≤ b - 4 := by linarith
  have hbr : (0 : ℝ) ≤ (a - 4) * (b - 4) + 2 * (c + c' - 8) := by
    nlinarith [h1, h2, mul_nonneg h1 h2]
  have hpos : (0 : ℝ) ≤ c' - c := by linarith
  have hprod : (0 : ℝ) ≤ (c' - c) * ((a - 4) * (b - 4) + 2 * (c + c' - 8)) :=
    mul_nonneg hpos hbr
  linarith

/-- Delta corner: on the sqrt8 box, `δ(y) ≤ δ(P4L, p5l², q6l²)` — the cell
lower corner is the Delta maximum. -/
theorem s8_dlt_corner {y4 y5 y6 P4L p5l q6l : ℝ}
    (hy4 : (2 : ℝ) ≤ y4) (hy5 : (2 : ℝ) ≤ y5) (hy6 : (2 : ℝ) ≤ y6)
    (hp5l : (2 : ℝ) ≤ p5l) (hq6l : (2 : ℝ) ≤ q6l)
    (hP4L : (4 : ℝ) ≤ P4L)
    (hc4 : P4L ≤ y4 * y4) (hc5 : p5l * p5l ≤ y5 * y5)
    (hc6 : q6l * q6l ≤ y6 * y6) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      2 * (4 * (p5l * p5l) * (q6l * q6l)
        - (P4L - p5l * p5l - q6l * q6l) ^ 2)
        - P4L * (p5l * p5l) * (q6l * q6l) := by
  have hy4sq : (4 : ℝ) ≤ y4 * y4 := by nlinarith [hy4]
  have hy5sq : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hy6sq : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hp5sq : (4 : ℝ) ≤ p5l * p5l := by nlinarith [hp5l]
  rw [s8_dlt_eq]
  have s1 := s8_dlt_anti_a (a := P4L) (a' := y4 * y4) (b := y5 * y5)
    (c := y6 * y6) hy5sq hy6sq (by linarith) hc4
  have s2 := s8_dlt_anti_b (b := p5l * p5l) (b' := y5 * y5) (a := P4L)
    (c := y6 * y6) hP4L hy6sq (by nlinarith) hc5
  have s3 := s8_dlt_anti_c (c := q6l * q6l) (c' := y6 * y6) (a := P4L)
    (b := p5l * p5l) hP4L hp5sq (by nlinarith) hc6
  exact s1.trans (s2.trans s3)

/-! ## 3. `ea` corner bodies and per-slot minimum corners -/

/-- `ea4X (y5²) (y6²) (y4²)` in length form (nonnegative y's). -/
noncomputable def s8a1 (y4 y5 y6 : ℝ) : ℝ :=
  Real.sqrt 2 * (y4 * y5 + (y4 * y4 + y5 * y5 - y6 * y6) / 2) +
    (y4 * y4 * y5 + y4 * y5 * y5) / 2

theorem s8a1_eq {y4 y5 y6 : ℝ} (hy4 : 0 ≤ y4) (hy5 : 0 ≤ y5) :
    Kepler.NliBanks20.ea4X (y5 * y5) (y6 * y6) (y4 * y4) = s8a1 y4 y5 y6 := by
  have e1 : Real.sqrt (2 * (y5 * y5) * (y4 * y4)) = Real.sqrt 2 * (y4 * y5) := by
    rw [show 2 * (y5 * y5) * (y4 * y4) = 2 * (y4 * y5) ^ 2 from by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq (mul_nonneg hy4 hy5)]
  unfold Kepler.NliBanks20.ea4X s8a1
  rw [e1, Real.sqrt_mul_self hy5, Real.sqrt_mul_self hy4]
  ring

/-- `ea5X (y5²) (y6²) (y4²)` in square form (the `y4` slot enters as its
square, so the top corner `P4H = 8` needs no irrational length). -/
noncomputable def s8a2sq (Y4sq p5 q6 : ℝ) : ℝ :=
  Real.sqrt 2 * (p5 * q6 + (p5 * p5 + q6 * q6 - Y4sq) / 2) +
    (p5 * p5 * q6 + q6 * q6 * p5) / 2

theorem s8a2sq_eq {p5 q6 : ℝ} (hp5 : 0 ≤ p5) (hq6 : 0 ≤ q6) (Y4sq : ℝ) :
    Kepler.NliBanks20.ea5X (p5 * p5) (q6 * q6) Y4sq = s8a2sq Y4sq p5 q6 := by
  have e1 : Real.sqrt (2 * (p5 * p5) * (q6 * q6)) = Real.sqrt 2 * (p5 * q6) := by
    rw [show 2 * (p5 * p5) * (q6 * q6) = 2 * (p5 * q6) ^ 2 from by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq (mul_nonneg hp5 hq6)]
  unfold Kepler.NliBanks20.ea5X s8a2sq
  rw [e1, Real.sqrt_mul_self hq6, Real.sqrt_mul_self hp5]
  ring

/-- `ea6X (y5²) (y6²) (y4²)` in length form. -/
noncomputable def s8a3 (y4 y5 y6 : ℝ) : ℝ :=
  Real.sqrt 2 * (y4 * y6 + (y4 * y4 + y6 * y6 - y5 * y5) / 2) +
    (y4 * y6 * y6 + y4 * y4 * y6) / 2

theorem s8a3_eq {y4 y5 y6 : ℝ} (hy4 : 0 ≤ y4) (hy6 : 0 ≤ y6) :
    Kepler.NliBanks20.ea6X (y5 * y5) (y6 * y6) (y4 * y4) = s8a3 y4 y5 y6 := by
  have e1 : Real.sqrt (2 * (y6 * y6) * (y4 * y4)) = Real.sqrt 2 * (y4 * y6) := by
    rw [show 2 * (y6 * y6) * (y4 * y4) = 2 * (y4 * y6) ^ 2 from by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq (mul_nonneg hy4 hy6)]
  unfold Kepler.NliBanks20.ea6X s8a3
  rw [e1, Real.sqrt_mul_self hy6, Real.sqrt_mul_self hy4]
  ring

/-- `ea4X` at the slot-1 minimum corner `(bl, ch, al)` (squares). -/
theorem s8_ea4_min {A B C al bl ch : ℝ} (hal : (0 : ℝ) ≤ al) (hB : (0 : ℝ) ≤ B)
    (hA : al ≤ A) (hB' : bl ≤ B) (hC : C ≤ ch) :
    Kepler.NliBanks20.ea4X bl ch al ≤ Kepler.NliBanks20.ea4X B C A := by
  have s1 : Kepler.NliBanks20.ea4X bl ch al ≤ Kepler.NliBanks20.ea4X B ch al :=
    Kepler.NliBanks20.ea4X_mono_a (a := bl) (a' := B) (b := ch) (c := al) hal hB'
  have s2 : Kepler.NliBanks20.ea4X B ch al ≤ Kepler.NliBanks20.ea4X B C al :=
    Kepler.NliBanks20.ea4X_anti_b (b := C) (b' := ch) (a := B) (c := al) hC
  have s3 : Kepler.NliBanks20.ea4X B C al ≤ Kepler.NliBanks20.ea4X B C A :=
    Kepler.NliBanks20.ea4X_mono_c (c := al) (c' := A) (a := B) (b := C) hB hA
  exact s1.trans (s2.trans s3)

/-- `ea5X` at the slot-2 minimum corner `(bl, cl, ah)` (squares). -/
theorem s8_ea5_min {A B C al bl cl ah : ℝ} (hcl : (0 : ℝ) ≤ cl)
    (hB : (0 : ℝ) ≤ B) (hA : A ≤ ah) (hB' : bl ≤ B) (hC : cl ≤ C) :
    Kepler.NliBanks20.ea5X bl cl ah ≤ Kepler.NliBanks20.ea5X B C A := by
  have s1 : Kepler.NliBanks20.ea5X bl cl ah ≤ Kepler.NliBanks20.ea5X B cl ah :=
    Kepler.NliBanks20.ea5X_mono_a (a := bl) (a' := B) (b := cl) (c := ah) hcl hB'
  have s2 : Kepler.NliBanks20.ea5X B cl ah ≤ Kepler.NliBanks20.ea5X B C ah :=
    Kepler.NliBanks20.ea5X_mono_b (b := cl) (b' := C) (a := B) (c := ah) hB hC
  have s3 : Kepler.NliBanks20.ea5X B C ah ≤ Kepler.NliBanks20.ea5X B C A :=
    Kepler.NliBanks20.ea5X_anti_c (c := A) (c' := ah) (a := B) (b := C) hA
  exact s1.trans (s2.trans s3)

/-- `ea6X` at the slot-3 minimum corner `(bh, cl, al)` (squares). -/
theorem s8_ea6_min {A B C al bh cl : ℝ} (hal : (0 : ℝ) ≤ al)
    (hC : (0 : ℝ) ≤ C) (hB : B ≤ bh) (hC' : cl ≤ C) (hA : al ≤ A) :
    Kepler.NliBanks20.ea6X bh cl al ≤ Kepler.NliBanks20.ea6X B C A := by
  have s1 : Kepler.NliBanks20.ea6X bh cl al ≤ Kepler.NliBanks20.ea6X B cl al :=
    Kepler.NliBanks20.ea6X_anti_a (a := B) (a' := bh) (b := cl) (c := al) hB
  have s2 : Kepler.NliBanks20.ea6X B cl al ≤ Kepler.NliBanks20.ea6X B C al :=
    Kepler.NliBanks20.ea6X_mono_b (b := cl) (b' := C) (a := B) (c := al) hal hC'
  have s3 : Kepler.NliBanks20.ea6X B C al ≤ Kepler.NliBanks20.ea6X B C A :=
    Kepler.NliBanks20.ea6X_mono_c (c := al) (c' := A) (a := B) (b := C) hC hA
  exact s1.trans (s2.trans s3)

/-! ## 4. The generic per-cell certificate -/

/-- **Generic cell lemma** (the `w2a_cell` twin, sqrt8 kernel).  At a box
point with `0 ≤ δ` (left branch), corner-derived piece bounds and a positive
exact-rational margin give `0 < c3Main`.  Every bound is per-factor valid:
`matan ≤ 1` for the `solEuler` slots, the product prefactor corner plus the
1-term Taylor lower bound `1 − t/3` for the `dih` slots. -/
theorem s8_cell {y4 y5 y6 P4L P4H p5l p5h q6l q6h Dh ea1L ea2L ea3L dx5L dx6L
    l5 l6 D5b D6b : ℝ}
    (hy4 : (2 : ℝ) ≤ y4) (hy5 : (2 : ℝ) ≤ y5) (hy6 : (2 : ℝ) ≤ y6)
    (hy5len : y5 ≤ p5h) (hy6len : y6 ≤ q6h)
    (hc4 : P4L ≤ y4 * y4) (hc4' : y4 * y4 ≤ P4H)
    (hc5 : p5l * p5l ≤ y5 * y5) (hc5' : y5 * y5 ≤ p5h * p5h)
    (hc6 : q6l * q6l ≤ y6 * y6) (hc6' : y6 * y6 ≤ q6h * q6h)
    (hP4L : (0 : ℝ) ≤ P4L)
    (hd0 : (0 : ℝ) ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2)
    (hdh : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤ Dh)
    (hdhp : (0 : ℝ) ≤ Dh)
    (hea1 : ea1L ≤ Kepler.NliBanks20.ea4X (y5 * y5) (y6 * y6) (y4 * y4))
    (hea1p : (0 : ℝ) < ea1L)
    (hea2 : ea2L ≤ Kepler.NliBanks20.ea5X (y5 * y5) (y6 * y6) (y4 * y4))
    (hea2p : (0 : ℝ) < ea2L)
    (hea3 : ea3L ≤ Kepler.NliBanks20.ea6X (y5 * y5) (y6 * y6) (y4 * y4))
    (hea3p : (0 : ℝ) < ea3L)
    (hdx5 : dx5L ≤ y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5))
    (hdx5p : (0 : ℝ) < dx5L)
    (hdx6 : dx6L ≤ y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6))
    (hdx6p : (0 : ℝ) < dx6L)
    (hl5 : l5 ≤ lfun (y5 * 0.5)) (hl5p : (0 : ℝ) ≤ l5)
    (hl6 : l6 ≤ lfun (y6 * 0.5)) (hl6p : (0 : ℝ) ≤ l6)
    (hS5H : (0 : ℝ) < p5h * (P4H + q6h * q6h - p5l * p5l))
    (hS6H : (0 : ℝ) < q6h * (P4H + p5h * p5h - q6l * q6l))
    (hv5 : (4 : ℝ) * (p5h * p5h) * Dh ≤ (3 : ℝ) * dx5L * dx5L)
    (hv6 : (4 : ℝ) * (q6h * q6h) * Dh ≤ (3 : ℝ) * dx6L * dx6L)
    (hD5b : D5b = (2 : ℝ) / (p5h * (P4H + q6h * q6h - p5l * p5l)) *
        ((1 : ℝ) - (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ)))
    (hD6b : D6b = (2 : ℝ) / (q6h * (P4H + p5h * p5h - q6l * q6l)) *
        ((1 : ℝ) - (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ)))
    (hmargin : (0 : ℝ) < 1 / 12
        - (0.6443107122 : ℝ) * ((1 : ℝ) / ea1L + (1 : ℝ) / ea2L + (1 : ℝ) / ea3L)
        + (0.0647174928 : ℝ) * (l5 * D5b + l6 * D6b)) :
    (0 : ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  -- 0. point facts
  have hy4n : (0 : ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0 : ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0 : ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hy4sq : (0 : ℝ) ≤ y4 * y4 := mul_nonneg hy4n hy4n
  have hy5sq : (0 : ℝ) ≤ y5 * y5 := mul_nonneg hy5n hy5n
  have hy6sq : (0 : ℝ) ≤ y6 * y6 := mul_nonneg hy6n hy6n
  have hD5nn : (0 : ℝ) < y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5) := by
    have := hdx5p
    linarith
  have hD6nn : (0 : ℝ) < y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6) := by
    have := hdx6p
    linarith
  -- 1. the three solEuler slots: `s_i = matan u_i / ea_i ≤ 1 / ea_iL`
  have hE1 : (0 : ℝ) < Kepler.NliBanks20.ea4X (y5 * y5) (y6 * y6) (y4 * y4) :=
    lt_of_lt_of_le hea1p hea1
  have hE2 : (0 : ℝ) < Kepler.NliBanks20.ea5X (y5 * y5) (y6 * y6) (y4 * y4) :=
    lt_of_lt_of_le hea2p hea2
  have hE3 : (0 : ℝ) < Kepler.NliBanks20.ea6X (y5 * y5) (y6 * y6) (y4 * y4) :=
    lt_of_lt_of_le hea3p hea3
  have hu1 : (0 : ℝ) ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
      (4 * Kepler.NliBanks20.ea4X (y5 * y5) (y6 * y6) (y4 * y4) ^ 2) :=
    div_nonneg hd0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hu2 : (0 : ℝ) ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
      (4 * Kepler.NliBanks20.ea5X (y5 * y5) (y6 * y6) (y4 * y4) ^ 2) :=
    div_nonneg hd0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hu3 : (0 : ℝ) ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
      (4 * Kepler.NliBanks20.ea6X (y5 * y5) (y6 * y6) (y4 * y4) ^ 2) :=
    div_nonneg hd0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hm1 := Kepler.NliBanks20.nb20_matan_le_one hu1
  have hm2 := Kepler.NliBanks20.nb20_matan_le_one hu2
  have hm3 := Kepler.NliBanks20.nb20_matan_le_one hu3
  have hs1 : solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 ≤
      (1 : ℝ) / ea1L := by
    rw [Kepler.NliBanks20.sol_euler4_eq, Kepler.NliBanks20.dlt_swap,
      div_le_div_iff₀ hE1 hea1p]
    exact (mul_le_mul_of_nonneg_right hm1 hea1p.le).trans
      (mul_le_mul_of_nonneg_left hea1 (by norm_num : (0 : ℝ) ≤ 1))
  have hs2 : solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 ≤
      (1 : ℝ) / ea2L := by
    rw [Kepler.NliBanks20.sol_euler5_eq, Kepler.NliBanks20.dlt6_eq,
      div_le_div_iff₀ hE2 hea2p]
    exact (mul_le_mul_of_nonneg_right hm2 hea2p.le).trans
      (mul_le_mul_of_nonneg_left hea2 (by norm_num : (0 : ℝ) ≤ 1))
  have hs3 : solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 ≤
      (1 : ℝ) / ea3L := by
    rw [Kepler.NliBanks20.sol_euler6_eq, Kepler.NliBanks20.dlt4_eq,
      div_le_div_iff₀ hE3 hea3p]
    exact (mul_le_mul_of_nonneg_right hm3 hea3p.le).trans
      (mul_le_mul_of_nonneg_left hea3 (by norm_num : (0 : ℝ) ≤ 1))
  -- 2. the dih slots in explicit form
  have hd5form : dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2
      = 2 * y5 / (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) *
        matan (4 * (y5 * y5) *
          deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
          (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) ^ 2) := by
    rw [Kepler.NliBanks20.dih5_eq _ _ _ hy5sq, Kepler.NliBanks20.dlt_swap,
      Real.sqrt_mul_self hy5n]
  have hd6form : dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2
      = 2 * y6 / (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) *
        matan (4 * (y6 * y6) *
          deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
          (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) ^ 2) := by
    rw [Kepler.NliBanks20.dih6_eq _ _ _ hy6sq, Kepler.NliBanks20.dlt6_eq,
      Real.sqrt_mul_self hy6n]
  have hv5nn : (0 : ℝ) ≤ 4 * (y5 * y5) *
      deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
      (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy5sq) hd0)
      (sq_nonneg _)
  have hv6nn : (0 : ℝ) ≤ 4 * (y6 * y6) *
      deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
      (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy6sq) hd0)
      (sq_nonneg _)
  -- 3. `d5` lower bound
  have hB5 : y5 * y5 ≤ p5h * p5h := by nlinarith [hy5, hc5']
  have hC6 : y6 * y6 ≤ q6h * q6h := by nlinarith [hy6, hc6']
  have hd5lb : ((2 : ℝ) / (p5h * (P4H + q6h * q6h - p5l * p5l))) *
      ((1 : ℝ) - (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ)) ≤
      dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    rw [hd5form]
    -- prefactor corner
    have hsum5le : y4 * y4 + y6 * y6 - y5 * y5 ≤
        P4H + q6h * q6h - p5l * p5l := by linarith
    have hsum5pos : (0 : ℝ) < y4 * y4 + y6 * y6 - y5 * y5 := by
      have hy5sqpos : (0 : ℝ) < y5 * y5 := by nlinarith [hy5]
      by_cases h : y4 * y4 + y6 * y6 - y5 * y5 ≤ 0
      · nlinarith [hD5nn, h, hy5sqpos.le]
      · linarith
    have hp5hpos : (0 : ℝ) ≤ p5h := by linarith
    have hprod1 : y5 * (y4 * y4 + y6 * y6 - y5 * y5) ≤
        p5h * (P4H + q6h * q6h - p5l * p5l) :=
      mul_le_mul hy5len hsum5le hsum5pos.le hp5hpos
    have hprod2 : y5 * (y5 * (y4 * y4 + y6 * y6 - y5 * y5)) ≤
        y5 * (p5h * (P4H + q6h * q6h - p5l * p5l)) :=
      mul_le_mul_of_nonneg_left hprod1 hy5n
    have hF : ((2 : ℝ) / (p5h * (P4H + q6h * q6h - p5l * p5l))) ≤
        2 * y5 / (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) := by
      rw [div_le_div_iff₀ hS5H hD5nn]
      linarith [hprod2]
    -- matan argument corner
    have hv5le : (4 : ℝ) * (y5 * y5) *
        deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
        (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) ^ 2 ≤
        (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) := by
      rw [div_le_div_iff₀ (pow_pos hD5nn 2)
        (show (0 : ℝ) < dx5L * dx5L by nlinarith [hdx5p])]
      have hnum : (y5 * y5) * deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
          (p5h * p5h) * Dh :=
        mul_le_mul hB5 hdh hd0 (mul_nonneg hp5hpos hp5hpos)
      have hden : dx5L * dx5L ≤
          (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) ^ 2 := by
        have hp : (0 : ℝ) < y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5) + dx5L := by
          have := hD5nn
          linarith
        nlinarith [hdx5, hp]
      have hC1 : (0 : ℝ) ≤ (4 : ℝ) * (p5h * p5h) * Dh := by
        rw [mul_assoc]
        exact mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg hp5hpos hp5hpos) hdhp)
      have hB1 : (0 : ℝ) ≤ dx5L * dx5L := mul_nonneg hdx5p.le hdx5p.le
      exact mul_le_mul (by linarith [hnum]) hden hB1 hC1
    have hT5 := Kepler.NliBanks20.nb20_matan_ge_taylor hv5nn
    have hM : ((1 : ℝ) - (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ)) ≤
        matan (4 * (y5 * y5) *
          deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
          (y5 * y5 * (y4 * y4 + y6 * y6 - y5 * y5)) ^ 2) := by
      linarith [hT5, hv5le]
    have hTb : (0 : ℝ) ≤ ((1 : ℝ) - (4 : ℝ) * (p5h * p5h) * Dh
        / (dx5L * dx5L) / (3 : ℝ)) := by
      have hX : (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ) ≤ 1 := by
        rw [show (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ) =
            (4 : ℝ) * (p5h * p5h) * Dh / (3 * (dx5L * dx5L)) from by ring]
        rw [div_le_iff₀ (show (0 : ℝ) < 3 * (dx5L * dx5L) by nlinarith [hdx5p])]
        linarith [hv5]
      linarith [hX]
    exact mul_le_mul hF hM hTb
      (div_nonneg (mul_nonneg (by norm_num) hy5n) hD5nn.le)
  -- 4. `d6` lower bound
  have hd6lb : ((2 : ℝ) / (q6h * (P4H + p5h * p5h - q6l * q6l))) *
      ((1 : ℝ) - (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ)) ≤
      dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    rw [hd6form]
    have hsum6le : y4 * y4 + y5 * y5 - y6 * y6 ≤
        P4H + p5h * p5h - q6l * q6l := by linarith
    have hsum6pos : (0 : ℝ) < y4 * y4 + y5 * y5 - y6 * y6 := by
      have hy6sqpos : (0 : ℝ) < y6 * y6 := by nlinarith [hy6]
      by_cases h : y4 * y4 + y5 * y5 - y6 * y6 ≤ 0
      · nlinarith [hD6nn, h, hy6sqpos.le]
      · linarith
    have hq6hpos : (0 : ℝ) ≤ q6h := by linarith
    have hprod1 : y6 * (y4 * y4 + y5 * y5 - y6 * y6) ≤
        q6h * (P4H + p5h * p5h - q6l * q6l) :=
      mul_le_mul hy6len hsum6le hsum6pos.le hq6hpos
    have hprod2 : y6 * (y6 * (y4 * y4 + y5 * y5 - y6 * y6)) ≤
        y6 * (q6h * (P4H + p5h * p5h - q6l * q6l)) :=
      mul_le_mul_of_nonneg_left hprod1 hy6n
    have hF : ((2 : ℝ) / (q6h * (P4H + p5h * p5h - q6l * q6l))) ≤
        2 * y6 / (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) := by
      rw [div_le_div_iff₀ hS6H hD6nn]
      linarith [hprod2]
    have hv6le : (4 : ℝ) * (y6 * y6) *
        deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
        (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) ^ 2 ≤
        (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) := by
      rw [div_le_div_iff₀ (pow_pos hD6nn 2)
        (show (0 : ℝ) < dx6L * dx6L by nlinarith [hdx6p])]
      have hnum : (y6 * y6) * deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
          (q6h * q6h) * Dh :=
        mul_le_mul hC6 hdh hd0 (mul_nonneg hq6hpos hq6hpos)
      have hden : dx6L * dx6L ≤
          (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) ^ 2 := by
        have hp : (0 : ℝ) < y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6) + dx6L := by
          have := hD6nn
          linarith
        nlinarith [hdx6, hp]
      have hC1 : (0 : ℝ) ≤ (4 : ℝ) * (q6h * q6h) * Dh := by
        rw [mul_assoc]
        exact mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg hq6hpos hq6hpos) hdhp)
      have hB1 : (0 : ℝ) ≤ dx6L * dx6L := mul_nonneg hdx6p.le hdx6p.le
      exact mul_le_mul (by linarith [hnum]) hden hB1 hC1
    have hT6 := Kepler.NliBanks20.nb20_matan_ge_taylor hv6nn
    have hM : ((1 : ℝ) - (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ)) ≤
        matan (4 * (y6 * y6) *
          deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 /
          (y6 * y6 * (y4 * y4 + y5 * y5 - y6 * y6)) ^ 2) := by
      linarith [hT6, hv6le]
    have hTb : (0 : ℝ) ≤ ((1 : ℝ) - (4 : ℝ) * (q6h * q6h) * Dh
        / (dx6L * dx6L) / (3 : ℝ)) := by
      have hX : (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ) ≤ 1 := by
        rw [show (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ) =
            (4 : ℝ) * (q6h * q6h) * Dh / (3 * (dx6L * dx6L)) from by ring]
        rw [div_le_iff₀ (show (0 : ℝ) < 3 * (dx6L * dx6L) by nlinarith [hdx6p])]
        linarith [hv6]
      linarith [hX]
    exact mul_le_mul hF hM hTb
      (div_nonneg (mul_nonneg (by norm_num) hy6n) hD6nn.le)
  -- 5. part products
  have hlf5 : (0 : ℝ) ≤ lfun (y5 * 0.5) := by linarith
  have hlf6 : (0 : ℝ) ≤ lfun (y6 * 0.5) := by linarith
  have hD5bpos : (0 : ℝ) ≤ D5b := by
    rw [hD5b]
    have hX : (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ) ≤ 1 := by
      rw [show (4 : ℝ) * (p5h * p5h) * Dh / (dx5L * dx5L) / (3 : ℝ) =
          (4 : ℝ) * (p5h * p5h) * Dh / (3 * (dx5L * dx5L)) from by ring]
      rw [div_le_iff₀ (show (0 : ℝ) < 3 * (dx5L * dx5L) by nlinarith [hdx5p])]
      linarith [hv5]
    exact mul_nonneg (div_nonneg (by norm_num) hS5H.le) (by linarith [hX])
  have hD6bpos : (0 : ℝ) ≤ D6b := by
    rw [hD6b]
    have hX : (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ) ≤ 1 := by
      rw [show (4 : ℝ) * (q6h * q6h) * Dh / (dx6L * dx6L) / (3 : ℝ) =
          (4 : ℝ) * (q6h * q6h) * Dh / (3 * (dx6L * dx6L)) from by ring]
      rw [div_le_iff₀ (show (0 : ℝ) < 3 * (dx6L * dx6L) by nlinarith [hdx6p])]
      linarith [hv6]
    exact mul_nonneg (div_nonneg (by norm_num) hS6H.le) (by linarith [hX])
  have hd5b' : D5b ≤
      dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    rw [hD5b]
    exact hd5lb
  have hd6b' : D6b ≤
      dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    rw [hD6b]
    exact hd6lb
  have hprod5 : l5 * D5b ≤
      lfun (y5 * 0.5) *
        dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 :=
    (mul_le_mul_of_nonneg_right hl5 hD5bpos).trans
      (mul_le_mul_of_nonneg_left hd5b' hlf5)
  have hprod6 : l6 * D6b ≤
      lfun (y6 * 0.5) *
        dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 :=
    (mul_le_mul_of_nonneg_right hl6 hD6bpos).trans
      (mul_le_mul_of_nonneg_left hd6b' hlf6)
  -- 6. final assembly
  obtain ⟨hA1, hA2, hB1, hB2⟩ := g4v_AB_bounds
  have hK1pos : (0 : ℝ) < 2 * mm1 / Real.pi := by linarith
  have hK2pos : (0 : ℝ) < 8 * mm2 / Real.pi := by linarith
  have hsumSE : solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
      solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 +
      solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 ≤
      (1 : ℝ) / ea1L + (1 : ℝ) / ea2L + (1 : ℝ) / ea3L :=
    add_le_add (add_le_add hs1 hs2) hs3
  have hsum1pos : (0 : ℝ) ≤ (1 : ℝ) / ea1L + (1 : ℝ) / ea2L + (1 : ℝ) / ea3L :=
    add_nonneg
      (add_nonneg (div_nonneg (by norm_num) (le_of_lt hea1p))
        (div_nonneg (by norm_num) (le_of_lt hea2p)))
      (div_nonneg (by norm_num) (le_of_lt hea3p))
  have hpart1 : (2 * mm1 / Real.pi) *
      (solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
        solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 +
        solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2) ≤
      (0.6443107122 : ℝ) * ((1 : ℝ) / ea1L + (1 : ℝ) / ea2L + (1 : ℝ) / ea3L) :=
    (mul_le_mul_of_nonneg_left hsumSE hK1pos.le).trans
      (mul_le_mul_of_nonneg_right hA2 hsum1pos)
  have hsumdb : l5 * D5b + l6 * D6b ≤
      lfun (y5 * 0.5) *
        dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
      lfun (y6 * 0.5) *
        dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 :=
    add_le_add hprod5 hprod6
  have hdbpos : (0 : ℝ) ≤ l5 * D5b + l6 * D6b :=
    add_nonneg (mul_nonneg hl5p hD5bpos) (mul_nonneg hl6p hD6bpos)
  have hpart2 : (0.0647174928 : ℝ) * (l5 * D5b + l6 * D6b) ≤
      (8 * mm2 / Real.pi) *
      (lfun (y5 * 0.5) *
          dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
        lfun (y6 * 0.5) *
          dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2) :=
    (mul_le_mul_of_nonneg_right hB1 hdbpos).trans
      (mul_le_mul_of_nonneg_left hsumdb hK2pos.le)
  rw [s8_c3_unfold_sq hy4n hy5n hy6n]
  linarith [hpart1, hpart2, hmargin]

/-! ## 5. The y5 ↔ y6 kernel symmetry -/

/-- `solEuler` slot symmetry (x1 ↔ x3 at the 2-slots). -/
theorem s8_se_swap13 (x1 x3 x5 : ℝ) :
    solEulerXDivSqrtdelta x3 2 x1 2 x5 2 =
      solEulerXDivSqrtdelta x1 2 x3 2 x5 2 := by
  have ed : deltaX x3 2 x1 2 x5 2 = deltaX x1 2 x3 2 x5 2 := by
    rw [deltaX, deltaX]
    ring
  have e1 : Real.sqrt (x3 * 2 * x1) = Real.sqrt (x1 * 2 * x3) := by
    congr 1
    ring
  unfold solEulerXDivSqrtdelta
  show matan (deltaX x3 2 x1 2 x5 2 /
      (4 * (Real.sqrt (x3 * 2 * x1) + Real.sqrt x3 * (2 + x1 - 2) / 2 +
        Real.sqrt 2 * (x3 + x1 - x5) / 2 + Real.sqrt x1 * (x3 + 2 - 2) / 2) ^ 2)) /
      (Real.sqrt (x3 * 2 * x1) + Real.sqrt x3 * (2 + x1 - 2) / 2 +
        Real.sqrt 2 * (x3 + x1 - x5) / 2 + Real.sqrt x1 * (x3 + 2 - 2) / 2) =
    matan (deltaX x1 2 x3 2 x5 2 /
      (4 * (Real.sqrt (x1 * 2 * x3) + Real.sqrt x1 * (2 + x3 - 2) / 2 +
        Real.sqrt 2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + 2 - 2) / 2) ^ 2)) /
      (Real.sqrt (x1 * 2 * x3) + Real.sqrt x1 * (2 + x3 - 2) / 2 +
        Real.sqrt 2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + 2 - 2) / 2)
  rw [ed, e1]
  ring

/-- `dih` slot symmetry (x3 ↔ x5 at the 2-slots). -/
theorem s8_dih_swap35 (x1 x3 x5 : ℝ) :
    dihXDivSqrtdeltaPosbranch x1 2 x5 2 x3 2 =
      dihXDivSqrtdeltaPosbranch x1 2 x3 2 x5 2 := by
  have e4 : deltaX4 x1 2 x5 2 x3 2 = deltaX4 x1 2 x3 2 x5 2 := by
    rw [deltaX4, deltaX4]
    ring
  have ed : deltaX x1 2 x5 2 x3 2 = deltaX x1 2 x3 2 x5 2 := by
    rw [deltaX, deltaX]
    ring
  unfold dihXDivSqrtdeltaPosbranch
  rw [e4, ed]

/-- **Kernel symmetry**: `c3Main y4 y5 y6 = c3Main y4 y6 y5`. -/
theorem s8_c3_symm {y4 y5 y6 : ℝ} (hy4 : 0 ≤ y4) (hy5 : 0 ≤ y5) (hy6 : 0 ≤ y6) :
    Kepler.NliBanks11.c3Main y4 y5 y6 = Kepler.NliBanks11.c3Main y4 y6 y5 := by
  rw [s8_c3_unfold_sq hy4 hy5 hy6, s8_c3_unfold_sq hy4 hy6 hy5]
  rw [s8_se_swap13 (y4 * y4) (y6 * y6) (y5 * y5),
    s8_se_swap13 (y6 * y6) (y5 * y5) (y4 * y4),
    s8_se_swap13 (y5 * y5) (y4 * y4) (y6 * y6),
    s8_dih_swap35 (y6 * y6) (y5 * y5) (y4 * y4),
    s8_dih_swap35 (y5 * y5) (y4 * y4) (y6 * y6)]
  ring

/-! ## 6. The right disjunct (reproof of the NliBanks18 §12 stone) -/

private theorem s8_ups_eq (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c) =
      4 * (b * b) * (c * c) - (a * a - b * b - c * c) ^ 2 := by
  rw [upsX]
  ring

private theorem s8_dlt_ups_eq (a b c : ℝ) :
    deltaX (a * a) 2 (b * b) 2 (c * c) 2 =
      2 * upsX (a * a) (b * b) (c * c) - a * a * (b * b) * (c * c) := by
  rw [deltaX, upsX]
  ring

private theorem s8_ups_pos {y4 y5 y6 : ℝ} (hy4 : 2 * hplus ≤ y4)
    (hy4' : y4 ≤ Real.sqrt 8) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * hminus)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus) :
    0 < upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
  have hhm : 2 * hminus ≤ 2.46352 :=
    Kepler.NliBanks17.nb17_two_hminus_bounds.2
  have hw8 : y4 * y4 ≤ 8 := by
    have hsq : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hy4pos : (0 : ℝ) ≤ y4 := by
      have hhp : (0 : ℝ) < 2 * hplus := by norm_num [hplus]
      linarith
    have hpm : y4 * y4 ≤ Real.sqrt 8 * Real.sqrt 8 :=
      mul_le_mul hy4' hy4' (by linarith) (Real.sqrt_nonneg 8)
    rw [hsq] at hpm
    exact hpm
  have hw7 : (2 * hplus) * (2 * hplus) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num [hplus] : (0 : ℝ) ≤ 2 * hplus) hy4
  have hw7' : (7.02 : ℝ) ≤ y4 * y4 := by
    have h := hw7
    rw [show (2 * hplus) * (2 * hplus) = 7.02674064 from by norm_num [hplus]] at h
    linarith [h]
  have hb5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hb6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hy5b : y5 ≤ 2.46352 := by linarith [hy5', hhm]
  have hy6b : y6 ≤ 2.46352 := by linarith [hy6', hhm]
  have h5sq := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ y5) hy5b
  have h6sq := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ y6) hy6b
  rw [s8_ups_eq]
  have hsum0 : (0 : ℝ) ≤ y5 * y5 + y6 * y6 - y4 * y4 := by linarith
  have hsumub : y5 * y5 + y6 * y6 - y4 * y4 ≤ 5.12 := by
    linarith [h5sq, h6sq, hw7']
  have hsqle : (y5 * y5 + y6 * y6 - y4 * y4) * (y5 * y5 + y6 * y6 - y4 * y4)
      ≤ (5.12 : ℝ) * (5.12 : ℝ) := mul_self_le_mul_self hsum0 hsumub
  have hprod : (64 : ℝ) ≤ 4 * (y5 * y5) * (y6 * y6) := by
    have h16 : (16 : ℝ) ≤ y5 * y5 * (y6 * y6) := by nlinarith [hb5, hb6]
    linarith
  have hsqub : (5.12 : ℝ) * (5.12 : ℝ) ≤ (26.25 : ℝ) := by norm_num
  linarith [hprod, hsqle, hsqub]

/-- **Right disjunct of `QZECFIC wt0 sqrt8`**: a negative three-coordinate
Delta puts the point on the `eta_y ^ 2 > 2` branch. -/
theorem s8_eta_dlt_neg {y4 y5 y6 : ℝ} (hy4 : 2 * hplus ≤ y4)
    (hy4' : y4 ≤ Real.sqrt 8) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * hminus)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus)
    (hd : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 < 0) :
    eta_y y4 y5 y6 ^ 2 > 2 := by
  have hups := s8_ups_pos hy4 hy4' hy5 hy5' hy6 hy6'
  have htri := s8_dlt_ups_eq y4 y5 y6
  have hy4pos : (0 : ℝ) ≤ y4 := by
    have hhp : (0 : ℝ) < 2 * hplus := by norm_num [hplus]
    linarith
  have hy5pos : (0 : ℝ) ≤ y5 := by linarith [hy5]
  have hy6pos : (0 : ℝ) ≤ y6 := by linarith [hy6]
  have hP : (0 : ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6) :=
    mul_nonneg (mul_nonneg (mul_nonneg hy4pos hy4pos)
      (mul_nonneg hy5pos hy5pos)) (mul_nonneg hy6pos hy6pos)
  have hrel : 2 * upsX (y4 * y4) (y5 * y5) (y6 * y6)
      < y4 * y4 * (y5 * y5) * (y6 * y6) := by linarith
  have hquo : (0 : ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6)
      / upsX (y4 * y4) (y5 * y5) (y6 * y6) := div_nonneg hP hups.le
  have hrw : eta_y y4 y5 y6 ^ 2
      = y4 * y4 * (y5 * y5) * (y6 * y6)
        / upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [eta_y, etaY, etaX, pow_two, Real.mul_self_sqrt hquo]
  rw [hrw, gt_iff_lt, lt_div_iff₀ hups]
  exact hrel
/-! ## 7. The design cells (generated; exact margins pre-audited) -/
/-- Design cell 0: margin 0.000740 (exact). -/
theorem s8_cell00 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.683:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.02897:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.02897:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.683:ℝ) * (2.683:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.02897:ℝ) * (2.02897:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.02897:ℝ) * (2.02897:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (24.71205:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.02897:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    have hbr : (24.71205:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.02897:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.02897:ℝ) * (2.02897:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.2236:ℝ) ≤ s8a2sq ((2.683:ℝ) * (2.683:ℝ)) (2:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := by norm_num
    have hbr : (14.2236:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.683:ℝ) * (2.683:ℝ)) (2:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.683:ℝ) * (2.683:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.683:ℝ) * (2.683:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (24.71205:ℝ) ≤ s8a3 (2.6508:ℝ) (2.02897:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    have hbr : (24.71205:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.02897:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.02897:ℝ) * (2.02897:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.94428846:ℝ) ≤ lfun ((2.02897:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.94428846:ℝ) ≤ lfun ((2.02897:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.02897:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.02897:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.02897:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.02897:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.683:ℝ) * (2.683:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.02897:ℝ)) (q6l := (2:ℝ)) (q6h := (2.02897:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (24.71205:ℝ)) (ea2L := (14.2236:ℝ)) (ea3L := (24.71205:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))
    (l5 := (0.94428846:ℝ)) (l6 := (0.94428846:ℝ))
    (D5b := (2:ℝ) / ((2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (24.71205:ℝ) + (1:ℝ) / (14.2236:ℝ) + (1:ℝ) / (24.71205:ℝ))
      + (0.0647174928:ℝ) * ((0.94428846:ℝ) * (((2:ℝ) / ((2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ)))) + (0.94428846:ℝ) * (((2:ℝ) / ((2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ))))))

/-- Design cell 1: margin 0.001653 (exact). -/
theorem s8_cell01 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.683:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.02897:ℝ))
    (hc6l : (2.02897:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.683:ℝ) * (2.683:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.02897:ℝ) * (2.02897:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.02897:ℝ) * (2.02897:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.02897:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.02897:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (24.62833:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (24.62833:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.56273:ℝ) ≤ s8a2sq ((2.683:ℝ) * (2.683:ℝ)) (2:ℝ) (2.02897:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.02897:ℝ) + ((2:ℝ) * (2:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := by norm_num
    have hbr : (14.56273:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.02897:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.02897:ℝ) + ((2:ℝ) * (2:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.02897:ℝ) + ((2:ℝ) * (2:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.02897:ℝ) + ((2:ℝ) * (2:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.02897:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.02897:ℝ) + ((2:ℝ) * (2:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.02897:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.02897:ℝ) + ((2:ℝ) * (2:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.02897:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.683:ℝ) * (2.683:ℝ)) (2:ℝ) (2.02897:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ)) ((2.683:ℝ) * (2.683:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.02897:ℝ) * (2.02897:ℝ))
      (ah := (2.683:ℝ) * (2.683:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ) * (2.02897:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.15967:ℝ) ≤ s8a3 (2.6508:ℝ) (2.02897:ℝ) (2.02897:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    have hbr : (25.15967:ℝ) ≤ ((2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.02897:ℝ) (2.02897:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2.02897:ℝ) * (2.02897:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.02897:ℝ) * (2.02897:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.02897:ℝ) * (2.02897:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ) * (2.02897:ℝ))
  have hl5v : (0.94428846:ℝ) ≤ lfun ((2.02897:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.02897:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.02897:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.683:ℝ) * (2.683:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.02897:ℝ)) (q6l := (2.02897:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))
    (ea1L := (24.62833:ℝ)) (ea2L := (14.56273:ℝ)) (ea3L := (25.15967:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) (dx6L := (2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.94428846:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))
    (by norm_num : (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))) ≤ (3:ℝ) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (24.62833:ℝ) + (1:ℝ) / (14.56273:ℝ) + (1:ℝ) / (25.15967:ℝ))
      + (0.0647174928:ℝ) * ((0.94428846:ℝ) * (((2:ℝ) / ((2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.02897:ℝ) * (2.02897:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 2: margin 0.000878 (exact). -/
theorem s8_cell02 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.683:ℝ))
    (hc5l : (2.02897:ℝ) ≤ y5) (hc5h : y5 ≤ (2.05794:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.683:ℝ) * (2.683:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2.02897:ℝ) * (2.02897:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.02897:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.02897:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.07595:ℝ) ≤ s8a1 (2.6508:ℝ) (2.02897:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.07595:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.02897:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.02897:ℝ) + (2.6508:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.02897:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.02897:ℝ) * (2.02897:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.56273:ℝ) ≤ s8a2sq ((2.683:ℝ) * (2.683:ℝ)) (2.02897:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := by norm_num
    have hbr : (14.56273:ℝ) ≤ ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) ≤
        ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.683:ℝ) * (2.683:ℝ)) / 2) := add_le_add_right h1 (((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.683:ℝ) * (2.683:ℝ)) (2.02897:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.683:ℝ) * (2.683:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.683:ℝ) * (2.683:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (24.62833:ℝ) ≤ s8a3 (2.6508:ℝ) (2.05794:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (24.62833:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.05794:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.02897:ℝ) * (2.02897:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ) * (2.02897:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.02897:ℝ) * (2.02897:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.683:ℝ) * (2.683:ℝ))
    (p5l := (2.02897:ℝ)) (p5h := (2.05794:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (25.07595:ℝ)) (ea2L := (14.56273:ℝ)) (ea3L := (24.62833:ℝ))
    (dx5L := (2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.88857692:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.07595:ℝ) + (1:ℝ) / (14.56273:ℝ) + (1:ℝ) / (24.62833:ℝ))
      + (0.0647174928:ℝ) * ((0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 3: margin 0.000359 (exact). -/
theorem s8_cell03 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.683:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.02897:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.683:ℝ) * (2.683:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.683:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.02897:ℝ) * (2.02897:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.077:ℝ) ≤ s8a1 (2.683:ℝ) (2:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.077:ℝ) ≤ ((2.683:ℝ) * (2.683:ℝ) * (2:ℝ) + (2.683:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.683:ℝ) * (2.683:ℝ) * (2:ℝ) + (2.683:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.683:ℝ) * (2.683:ℝ) * (2:ℝ) + (2.683:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.683:ℝ) * (2.683:ℝ) * (2:ℝ) + (2.683:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.683:ℝ) (2:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.683:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.683:ℝ) * (2.683:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.08224:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (14.08224:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.16072:ℝ) ≤ s8a3 (2.683:ℝ) (2.02897:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    have hbr : (25.16072:ℝ) ≤ ((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤
        ((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := add_le_add_right h1 (((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.683:ℝ) (2.02897:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.683:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.683:ℝ) * (2.683:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.683:ℝ) * (2.683:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.683:ℝ) * (2.683:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.94428846:ℝ) ≤ lfun ((2.02897:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.02897:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.02897:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.683:ℝ) * (2.683:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.02897:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (25.077:ℝ)) (ea2L := (14.08224:ℝ)) (ea3L := (25.16072:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.94428846:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.077:ℝ) + (1:ℝ) / (14.08224:ℝ) + (1:ℝ) / (25.16072:ℝ))
      + (0.0647174928:ℝ) * ((0.94428846:ℝ) * (((2:ℝ) / ((2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 4: margin 0.001300 (exact). -/
theorem s8_cell04 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.683:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2.02897:ℝ) ≤ y5) (hc5h : y5 ≤ (2.05794:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.683:ℝ) * (2.683:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.683:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2.02897:ℝ) * (2.02897:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.02897:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.02897:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.53031:ℝ) ≤ s8a1 (2.683:ℝ) (2.02897:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.683:ℝ) * (2.02897:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.53031:ℝ) ≤ ((2.683:ℝ) * (2.683:ℝ) * (2.02897:ℝ) + (2.683:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2.02897:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.683:ℝ) * (2.02897:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.683:ℝ) * (2.02897:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.683:ℝ) * (2.683:ℝ) * (2.02897:ℝ) + (2.683:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2.02897:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.683:ℝ) * (2.683:ℝ) * (2.02897:ℝ) + (2.683:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.683:ℝ) * (2.02897:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.683:ℝ) * (2.683:ℝ) * (2.02897:ℝ) + (2.683:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.683:ℝ) (2.02897:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.683:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))]
    exact s8_ea4_min (al := (2.683:ℝ) * (2.683:ℝ)) (bl := (2.02897:ℝ) * (2.02897:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.42138:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.02897:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (14.42138:ℝ) ≤ ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.02897:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.077:ℝ) ≤ s8a3 (2.683:ℝ) (2.05794:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.077:ℝ) ≤ ((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.683:ℝ) * (2:ℝ) + ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.683:ℝ) * (2:ℝ) * (2:ℝ) + (2.683:ℝ) * (2.683:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.683:ℝ) (2.05794:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.683:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.683:ℝ) * (2.683:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.02897:ℝ) * (2.02897:ℝ)) (al := (2.683:ℝ) * (2.683:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ) * (2.02897:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.683:ℝ) * (2.683:ℝ))
      (bl := (2.02897:ℝ) * (2.02897:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.683:ℝ) * (2.683:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2.02897:ℝ)) (p5h := (2.05794:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (25.53031:ℝ)) (ea2L := (14.42138:ℝ)) (ea3L := (25.077:ℝ))
    (dx5L := (2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.88857692:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.683:ℝ) * (2.683:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.53031:ℝ) + (1:ℝ) / (14.42138:ℝ) + (1:ℝ) / (25.077:ℝ))
      + (0.0647174928:ℝ) * ((0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.683:ℝ) * (2.683:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.683:ℝ) * (2.683:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.683:ℝ) * (2.683:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 5: margin 0.000264 (exact). -/
theorem s8_cell05 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.05794:ℝ))
    (hc6l : (2.05794:ℝ) ≤ y6) (hc6h : y6 ≤ (2.11588:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.05794:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (24.45733:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (24.45733:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.76337:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (14.76337:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.52698:ℝ) ≤ s8a3 (2.6508:ℝ) (2.05794:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.52698:ℝ) ≤ ((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.05794:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.05794:ℝ) * (2.05794:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hl5v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.05794:ℝ)) (q6l := (2.05794:ℝ)) (q6h := (2.11588:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))
    (ea1L := (24.45733:ℝ)) (ea2L := (14.76337:ℝ)) (ea3L := (25.52698:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) (dx6L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (l5 := (0.88857692:ℝ)) (l6 := (0.77715384:ℝ))
    (D5b := (2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (24.45733:ℝ) + (1:ℝ) / (14.76337:ℝ) + (1:ℝ) / (25.52698:ℝ))
      + (0.0647174928:ℝ) * ((0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))) + (0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))))))

/-- Design cell 6: margin 0.000264 (exact). -/
theorem s8_cell06 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2.05794:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.52698:ℝ) ≤ s8a1 (2.6508:ℝ) (2.05794:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.52698:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.05794:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.76337:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.05794:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (14.76337:ℝ) ≤ ((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.05794:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (24.45733:ℝ) ≤ s8a3 (2.6508:ℝ) (2.11588:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (24.45733:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.11588:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2.05794:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (25.52698:ℝ)) (ea2L := (14.76337:ℝ)) (ea3L := (24.45733:ℝ))
    (dx5L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.52698:ℝ) + (1:ℝ) / (14.76337:ℝ) + (1:ℝ) / (24.45733:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 7: margin 0.002093 (exact). -/
theorem s8_cell07 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2.05794:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.05794:ℝ) ≤ y6) (hc6h : y6 ≤ (2.11588:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.05794:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.35598:ℝ) ≤ s8a1 (2.6508:ℝ) (2.05794:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (25.35598:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.05794:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.46287:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.05794:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (15.46287:ℝ) ≤ ((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.05794:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.35598:ℝ) ≤ s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (25.35598:ℝ) ≤ ((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.05794:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.05794:ℝ) * (2.05794:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hdx6 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2.05794:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.05794:ℝ)) (q6h := (2.11588:ℝ))
    (Dh := 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))
    (ea1L := (25.35598:ℝ)) (ea2L := (15.46287:ℝ)) (ea3L := (25.35598:ℝ))
    (dx5L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.77715384:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.35598:ℝ) + (1:ℝ) / (15.46287:ℝ) + (1:ℝ) / (25.35598:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))))))

/-- Design cell 8: margin 0.000365 (exact). -/
theorem s8_cell08 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ (2.78:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.02897:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.78:ℝ) * (2.78:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.02897:ℝ) * (2.02897:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.59692:ℝ) ≤ s8a1 (2.72:ℝ) (2:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.59692:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (13.8489:ℝ) ≤ s8a2sq ((2.78:ℝ) * (2.78:ℝ)) (2:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) := by norm_num
    have hbr : (13.8489:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.78:ℝ) * (2.78:ℝ)) (2:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.78:ℝ) * (2.78:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.78:ℝ) * (2.78:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.68064:ℝ) ≤ s8a3 (2.72:ℝ) (2.02897:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    have hbr : (25.68064:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.02897:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.02897:ℝ) * (2.02897:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.94428846:ℝ) ≤ lfun ((2.02897:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.02897:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.02897:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (2.78:ℝ) * (2.78:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.02897:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (25.59692:ℝ)) (ea2L := (13.8489:ℝ)) (ea3L := (25.68064:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.94428846:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.02897:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.02897:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.59692:ℝ) + (1:ℝ) / (13.8489:ℝ) + (1:ℝ) / (25.68064:ℝ))
      + (0.0647174928:ℝ) * ((0.94428846:ℝ) * (((2:ℝ) / ((2.02897:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 9: margin 0.001338 (exact). -/
theorem s8_cell09 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ (2.78:ℝ))
    (hc5l : (2.02897:ℝ) ≤ y5) (hc5h : y5 ≤ (2.05794:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.78:ℝ) * (2.78:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2.02897:ℝ) * (2.02897:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.02897:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.02897:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (26.0568:ℝ) ≤ s8a1 (2.72:ℝ) (2.02897:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.02897:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (26.0568:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2.02897:ℝ) + (2.72:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.02897:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.02897:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.02897:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2.02897:ℝ) + (2.72:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.02897:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2.02897:ℝ) + (2.72:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.02897:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2.02897:ℝ) + (2.72:ℝ) * (2.02897:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2.02897:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2.02897:ℝ) * (2.02897:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.18803:ℝ) ≤ s8a2sq ((2.78:ℝ) * (2.78:ℝ)) (2.02897:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) := by norm_num
    have hbr : (14.18803:ℝ) ≤ ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + (1.41421356:ℝ) * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) ≤
        ((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2 + Real.sqrt 2 * ((2.02897:ℝ) * (2:ℝ) + ((2.02897:ℝ) * (2.02897:ℝ) + (2:ℝ) * (2:ℝ) - (2.78:ℝ) * (2.78:ℝ)) / 2) := add_le_add_right h1 (((2.02897:ℝ) * (2.02897:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.02897:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.78:ℝ) * (2.78:ℝ)) (2.02897:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.02897:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.78:ℝ) * (2.78:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.02897:ℝ) * (2.02897:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.78:ℝ) * (2.78:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.59692:ℝ) ≤ s8a3 (2.72:ℝ) (2.05794:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (25.59692:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.05794:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.02897:ℝ) * (2.02897:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.02897:ℝ) * (2.02897:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2.02897:ℝ) * (2.02897:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (2.78:ℝ) * (2.78:ℝ))
    (p5l := (2.02897:ℝ)) (p5h := (2.05794:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (26.0568:ℝ)) (ea2L := (14.18803:ℝ)) (ea3L := (25.59692:ℝ))
    (dx5L := (2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.88857692:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (26.0568:ℝ) + (1:ℝ) / (14.18803:ℝ) + (1:ℝ) / (25.59692:ℝ))
      + (0.0647174928:ℝ) * ((0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.02897:ℝ) * (2.02897:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2.02897:ℝ) * (2.02897:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.02897:ℝ) * (2.02897:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.02897:ℝ) * (2.02897:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.02897:ℝ) * (2.02897:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 10: margin 0.000650 (exact). -/
theorem s8_cell10 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.78:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.05794:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.78:ℝ) * (2.78:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.78:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.78:ℝ) * (2.78:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (26.44997:ℝ) ≤ s8a1 (2.78:ℝ) (2:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (26.44997:ℝ) ≤ ((2.78:ℝ) * (2.78:ℝ) * (2:ℝ) + (2.78:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.78:ℝ) * (2.78:ℝ) * (2:ℝ) + (2.78:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.78:ℝ) * (2.78:ℝ) * (2:ℝ) + (2.78:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.78:ℝ) * (2.78:ℝ) * (2:ℝ) + (2.78:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.78:ℝ) (2:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.78:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.78:ℝ) * (2.78:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.78:ℝ) * (2.78:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (13.65685:ℝ) ≤ s8a2sq ((8:ℝ)) (2:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (13.65685:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2:ℝ) + ((2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (26.44997:ℝ) ≤ s8a3 (2.78:ℝ) (2.05794:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (26.44997:ℝ) ≤ ((2.78:ℝ) * (2:ℝ) * (2:ℝ) + (2.78:ℝ) * (2.78:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.78:ℝ) * (2:ℝ) * (2:ℝ) + (2.78:ℝ) * (2.78:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.78:ℝ) * (2:ℝ) * (2:ℝ) + (2.78:ℝ) * (2.78:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.78:ℝ) * (2:ℝ) + ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.78:ℝ) * (2:ℝ) * (2:ℝ) + (2.78:ℝ) * (2.78:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.78:ℝ) (2.05794:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.78:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.78:ℝ) * (2.78:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.78:ℝ) * (2.78:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.78:ℝ) * (2.78:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.78:ℝ) * (2.78:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.78:ℝ) * (2.78:ℝ)) (P4H := (8:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.05794:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (26.44997:ℝ)) (ea2L := (13.65685:ℝ)) (ea3L := (26.44997:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.88857692:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.78:ℝ) * (2.78:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (26.44997:ℝ) + (1:ℝ) / (13.65685:ℝ) + (1:ℝ) / (26.44997:ℝ))
      + (0.0647174928:ℝ) * ((0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.78:ℝ) * (2.78:ℝ) - (2:ℝ) * (2:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.78:ℝ) * (2.78:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.78:ℝ) * (2.78:ℝ) + (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 11: margin 0.000559 (exact). -/
theorem s8_cell11 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.05794:ℝ))
    (hc6l : (2.05794:ℝ) ≤ y6) (hc6h : y6 ≤ (2.11588:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.05794:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.42592:ℝ) ≤ s8a1 (2.72:ℝ) (2:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (25.42592:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.33798:ℝ) ≤ s8a2sq ((8:ℝ)) (2:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (14.33798:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.05794:ℝ) + ((2:ℝ) * (2:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (26.52014:ℝ) ≤ s8a3 (2.72:ℝ) (2.05794:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (26.52014:ℝ) ≤ ((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.05794:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2.05794:ℝ) * (2.05794:ℝ)) (bh := (2.05794:ℝ) * (2.05794:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hl5v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (8:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.05794:ℝ)) (q6l := (2.05794:ℝ)) (q6h := (2.11588:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))
    (ea1L := (25.42592:ℝ)) (ea2L := (14.33798:ℝ)) (ea3L := (26.52014:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) (dx6L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (l5 := (0.88857692:ℝ)) (l6 := (0.77715384:ℝ))
    (D5b := (2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.42592:ℝ) + (1:ℝ) / (14.33798:ℝ) + (1:ℝ) / (26.52014:ℝ))
      + (0.0647174928:ℝ) * ((0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))) + (0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))))))

/-- Design cell 12: margin 0.000559 (exact). -/
theorem s8_cell12 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.05794:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.05794:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.05794:ℝ) * (2.05794:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (26.52014:ℝ) ≤ s8a1 (2.72:ℝ) (2.05794:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    have hbr : (26.52014:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2.05794:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (14.33798:ℝ) ≤ s8a2sq ((8:ℝ)) (2.05794:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (14.33798:ℝ) ≤ ((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) ≤
        ((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.05794:ℝ) * (2:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.05794:ℝ) * (2.05794:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.05794:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.42592:ℝ) ≤ s8a3 (2.72:ℝ) (2.11588:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (25.42592:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.11588:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.05794:ℝ) * (2.05794:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.88857692:ℝ) ≤ lfun ((2.05794:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.05794:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.05794:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.05794:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2:ℝ)) (q6h := (2.05794:ℝ))
    (Dh := 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (26.52014:ℝ)) (ea2L := (14.33798:ℝ)) (ea3L := (25.42592:ℝ))
    (dx5L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.88857692:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (0:ℝ) < (2.05794:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (26.52014:ℝ) + (1:ℝ) / (14.33798:ℝ) + (1:ℝ) / (25.42592:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.88857692:ℝ) * (((2:ℝ) / ((2.05794:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))))) / (3:ℝ))))))

/-- Design cell 13: margin 0.002481 (exact). -/
theorem s8_cell13 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.05794:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.05794:ℝ) ≤ y6) (hc6h : y6 ≤ (2.11588:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.05794:ℝ) * (2.05794:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.05794:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (26.34914:ℝ) ≤ s8a1 (2.72:ℝ) (2.05794:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (26.34914:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2.05794:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.03748:ℝ) ≤ s8a2sq ((8:ℝ)) (2.05794:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (15.03748:ℝ) ≤ ((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) ≤
        ((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.05794:ℝ) * (2.05794:ℝ) + ((2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.05794:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.05794:ℝ) * (2.05794:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (26.34914:ℝ) ≤ s8a3 (2.72:ℝ) (2.11588:ℝ) (2.05794:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (26.34914:ℝ) ≤ ((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.05794:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.05794:ℝ) * (2.05794:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.05794:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.11588:ℝ) (2.05794:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.05794:ℝ) * (2.05794:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2.05794:ℝ) * (2.05794:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hdx6 : (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.05794:ℝ) * (2.05794:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2.05794:ℝ) * (2.05794:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.05794:ℝ) * (2.05794:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.05794:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.05794:ℝ)) (q6h := (2.11588:ℝ))
    (Dh := 2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))
    (ea1L := (26.34914:ℝ)) (ea2L := (15.03748:ℝ)) (ea3L := (26.34914:ℝ))
    (dx5L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.77715384:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) ≤ (3:ℝ) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (26.34914:ℝ) + (1:ℝ) / (15.03748:ℝ) + (1:ℝ) / (26.34914:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.05794:ℝ) * (2.05794:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.05794:ℝ) * (2.05794:ℝ) - (2.05794:ℝ) * (2.05794:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.05794:ℝ) * (2.05794:ℝ)) * ((2.05794:ℝ) * (2.05794:ℝ)))) / ((((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2.05794:ℝ) * (2.05794:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.05794:ℝ) * (2.05794:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))))))

/-- Design cell 14: margin 0.000648 (exact). -/
theorem s8_cell14 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.11588:ℝ) ≤ y6) (hc6h : y6 ≤ (2.17382:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.17382:ℝ) * (2.17382:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.11588:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (24.28158:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.17382:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    have hbr : (24.28158:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.17382:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.17382:ℝ) * (2.17382:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.45596:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (15.45596:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (26.26827:ℝ) ≤ s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (26.26827:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.11588:ℝ) * (2.11588:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.17382:ℝ) * (2.17382:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.66573076:ℝ) ≤ lfun ((2.17382:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.17382:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.17382:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.11588:ℝ)) (q6h := (2.17382:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))
    (ea1L := (24.28158:ℝ)) (ea2L := (15.45596:ℝ)) (ea3L := (26.26827:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.66573076:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (24.28158:ℝ) + (1:ℝ) / (15.45596:ℝ) + (1:ℝ) / (26.26827:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.66573076:ℝ) * (((2:ℝ) / ((2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ))))))

/-- Design cell 15: margin 0.002239 (exact). -/
theorem s8_cell15 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.17382:ℝ) ≤ y6) (hc6h : y6 ≤ (2.23176:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.17382:ℝ) * (2.17382:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.17382:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.17382:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (24.10109:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (24.10109:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (16.16002:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2.17382:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (16.16002:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2:ℝ) (2.17382:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.17382:ℝ) * (2.17382:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ) * (2.17382:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (27.19421:ℝ) ≤ s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.17382:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.17382:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (27.19421:ℝ) ≤ ((2.6508:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.17382:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.17382:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.17382:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.17382:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.17382:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.17382:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.17382:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.17382:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.17382:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.17382:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.17382:ℝ) * (2.17382:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.17382:ℝ) * (2.17382:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.17382:ℝ) * (2.17382:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ) * (2.17382:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.17382:ℝ)) (q6h := (2.23176:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))
    (ea1L := (24.10109:ℝ)) (ea2L := (16.16002:ℝ)) (ea3L := (27.19421:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.55430769:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.23176:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) ≤ (3:ℝ) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (24.10109:ℝ) + (1:ℝ) / (16.16002:ℝ) + (1:ℝ) / (27.19421:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))))))

/-- Design cell 16: margin 0.001131 (exact). -/
theorem s8_cell16 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.11588:ℝ) ≤ y6) (hc6h : y6 ≤ (2.17382:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.17382:ℝ) * (2.17382:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.11588:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.25017:ℝ) ≤ s8a1 (2.72:ℝ) (2:ℝ) (2.17382:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    have hbr : (25.25017:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2:ℝ) (2.17382:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.17382:ℝ) * (2.17382:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.03057:ℝ) ≤ s8a2sq ((8:ℝ)) (2:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (15.03057:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.11588:ℝ) + ((2:ℝ) * (2:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (27.28624:ℝ) ≤ s8a3 (2.72:ℝ) (2.11588:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (27.28624:ℝ) ≤ ((2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.11588:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2.11588:ℝ) * (2.11588:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.17382:ℝ) * (2.17382:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.66573076:ℝ) ≤ lfun ((2.17382:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.17382:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.17382:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (8:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.11588:ℝ)) (q6h := (2.17382:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))
    (ea1L := (25.25017:ℝ)) (ea2L := (15.03057:ℝ)) (ea3L := (27.28624:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.66573076:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.17382:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.17382:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.25017:ℝ) + (1:ℝ) / (15.03057:ℝ) + (1:ℝ) / (27.28624:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.66573076:ℝ) * (((2:ℝ) / ((2.17382:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ))))))

/-- Design cell 17: margin 0.002807 (exact). -/
theorem s8_cell17 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.17382:ℝ) ≤ y6) (hc6h : y6 ≤ (2.23176:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.17382:ℝ) * (2.17382:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.17382:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.17382:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.06968:ℝ) ≤ s8a1 (2.72:ℝ) (2:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (25.06968:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2:ℝ) + (2.72:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.73462:ℝ) ≤ s8a2sq ((8:ℝ)) (2:ℝ) (2.17382:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (15.73462:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (8:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.17382:ℝ) + ((2:ℝ) * (2:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.17382:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2:ℝ) (2.17382:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.17382:ℝ) * (2.17382:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ) * (2.17382:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (28.23722:ℝ) ≤ s8a3 (2.72:ℝ) (2.11588:ℝ) (2.17382:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.17382:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (28.23722:ℝ) ≤ ((2.72:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.17382:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.17382:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.17382:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.17382:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.17382:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.17382:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.17382:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.17382:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.17382:ℝ) * (2.17382:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2.17382:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.11588:ℝ) (2.17382:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.17382:ℝ) * (2.17382:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2.17382:ℝ) * (2.17382:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.17382:ℝ) * (2.17382:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.17382:ℝ) * (2.17382:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (8:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.17382:ℝ)) (q6h := (2.23176:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))
    (ea1L := (25.06968:ℝ)) (ea2L := (15.73462:ℝ)) (ea3L := (28.23722:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.55430769:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) ≤ (3:ℝ) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.06968:ℝ) + (1:ℝ) / (15.73462:ℝ) + (1:ℝ) / (28.23722:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.17382:ℝ) * (2.17382:ℝ)))) / ((((2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.17382:ℝ) * (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))))))

/-- Design cell 18: margin 0.000648 (exact). -/
theorem s8_cell18 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ (2.72:ℝ))
    (hc5l : (2.11588:ℝ) ≤ y5) (hc5h : y5 ≤ (2.17382:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.11588:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (2.72:ℝ) * (2.72:ℝ) :=
    mul_self_le_mul_self hy4n hc4h
  have hB5sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.17382:ℝ) * (2.17382:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (26.26827:ℝ) ≤ s8a1 (2.6508:ℝ) (2.11588:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (26.26827:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.11588:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.45596:ℝ) ≤ s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.11588:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    have hbr : (15.45596:ℝ) ≤ ((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) ≤
        ((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (2.72:ℝ) * (2.72:ℝ)) / 2) := add_le_add_right h1 (((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((2.72:ℝ) * (2.72:ℝ)) (2.11588:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((2.72:ℝ) * (2.72:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (2.72:ℝ) * (2.72:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (24.28158:ℝ) ≤ s8a3 (2.6508:ℝ) (2.17382:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    have hbr : (24.28158:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.17382:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.17382:ℝ) * (2.17382:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.17382:ℝ) * (2.17382:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.66573076:ℝ) ≤ lfun ((2.17382:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.17382:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.17382:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (2.72:ℝ) * (2.72:ℝ))
    (p5l := (2.11588:ℝ)) (p5h := (2.17382:ℝ)) (q6l := (2:ℝ)) (q6h := (2.11588:ℝ))
    (Dh := 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (26.26827:ℝ)) (ea2L := (15.45596:ℝ)) (ea3L := (24.28158:ℝ))
    (dx5L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (l5 := (0.66573076:ℝ)) (l6 := (0.77715384:ℝ))
    (D5b := (2:ℝ) / ((2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (26.26827:ℝ) + (1:ℝ) / (15.45596:ℝ) + (1:ℝ) / (24.28158:ℝ))
      + (0.0647174928:ℝ) * ((0.66573076:ℝ) * (((2:ℝ) / ((2.17382:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ)))) + (0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))))))

/-- Design cell 20: margin 0.001131 (exact). -/
theorem s8_cell20 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.72:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.11588:ℝ) ≤ y5) (hc5h : y5 ≤ (2.17382:ℝ))
    (hc6l : (2:ℝ) ≤ y6) (hc6h : y6 ≤ (2.11588:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.72:ℝ) * (2.72:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.72:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.17382:ℝ) * (2.17382:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2:ℝ) * (2:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (2:ℝ) ≤ (2:ℝ)) (by norm_num : (4:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (27.28624:ℝ) ≤ s8a1 (2.72:ℝ) (2.11588:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (27.28624:ℝ) ≤ ((2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2.11588:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2.72:ℝ) * (2.11588:ℝ) + (2.72:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.72:ℝ) (2.11588:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea4_min (al := (2.72:ℝ) * (2.72:ℝ)) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (15.03057:ℝ) ≤ s8a2sq ((8:ℝ)) (2.11588:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (15.03057:ℝ) ≤ ((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) ≤
        ((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.11588:ℝ) * (2:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2:ℝ) * (2:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.11588:ℝ) * (2.11588:ℝ) * (2:ℝ) + (2:ℝ) * (2:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.11588:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.25017:ℝ) ≤ s8a3 (2.72:ℝ) (2.17382:ℝ) (2:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    have hbr : (25.25017:ℝ) ≤ ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) ≤
        ((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.72:ℝ) * (2:ℝ) + ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) / 2) := add_le_add_right h1 (((2.72:ℝ) * (2:ℝ) * (2:ℝ) + (2.72:ℝ) * (2.72:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.72:ℝ) (2.17382:ℝ) (2:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.72:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea6_min (al := (2.72:ℝ) * (2.72:ℝ)) (bh := (2.17382:ℝ) * (2.17382:ℝ)) (cl := (2:ℝ) * (2:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (cl := (2:ℝ) * (2:ℝ)) (bh := (2.17382:ℝ) * (2.17382:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hdx6 : (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2:ℝ) * (2:ℝ)) (al := (2.72:ℝ) * (2.72:ℝ))
      (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.11588:ℝ) * (2.11588:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hl5v : (0.66573076:ℝ) ≤ lfun ((2.17382:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.17382:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.17382:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.72:ℝ) * (2.72:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.11588:ℝ)) (p5h := (2.17382:ℝ)) (q6l := (2:ℝ)) (q6h := (2.11588:ℝ))
    (Dh := 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))
    (ea1L := (27.28624:ℝ)) (ea2L := (15.03057:ℝ)) (ea3L := (25.25017:ℝ))
    (dx5L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))) (dx6L := (2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (l5 := (0.66573076:ℝ)) (l6 := (0.77715384:ℝ))
    (D5b := (2:ℝ) / ((2.17382:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.72:ℝ) * (2.72:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.17382:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (27.28624:ℝ) + (1:ℝ) / (15.03057:ℝ) + (1:ℝ) / (25.25017:ℝ))
      + (0.0647174928:ℝ) * ((0.66573076:ℝ) * (((2:ℝ) / ((2.17382:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.17382:ℝ) * (2.17382:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2:ℝ) * (2:ℝ) - (2.17382:ℝ) * (2.17382:ℝ))))) / (3:ℝ)))) + (0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.17382:ℝ) * (2.17382:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)) - ((2.72:ℝ) * (2.72:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2:ℝ) * (2:ℝ)) ^ 2) - (2.72:ℝ) * (2.72:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2:ℝ) * (2:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.72:ℝ) * (2.72:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))))))

/-- Design cell 22: margin 0.001352 (exact). -/
theorem s8_cell22 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.11588:ℝ) ≤ y5) (hc5h : y5 ≤ (2.23176:ℝ))
    (hc6l : (2.11588:ℝ) ≤ y6) (hc6h : y6 ≤ (2.23176:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.11588:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.91203:ℝ) ≤ s8a1 (2.6508:ℝ) (2.11588:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (25.91203:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.11588:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (16.47855:ℝ) ≤ s8a2sq ((8:ℝ)) (2.11588:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.11588:ℝ) * (2.11588:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (16.47855:ℝ) ≤ ((2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.11588:ℝ) * (2.11588:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) ≤
        ((2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.11588:ℝ) * (2.11588:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.11588:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.91203:ℝ) ≤ s8a3 (2.6508:ℝ) (2.23176:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (25.91203:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.23176:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.23176:ℝ) * (2.23176:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.11588:ℝ) * (2.11588:ℝ)) (bh := (2.23176:ℝ) * (2.23176:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hdx6 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hl5v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.11588:ℝ)) (p5h := (2.23176:ℝ)) (q6l := (2.11588:ℝ)) (q6h := (2.23176:ℝ))
    (Dh := 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))
    (ea1L := (25.91203:ℝ)) (ea2L := (16.47855:ℝ)) (ea3L := (25.91203:ℝ))
    (dx5L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) (dx6L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (l5 := (0.55430769:ℝ)) (l6 := (0.55430769:ℝ))
    (D5b := (2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.91203:ℝ) + (1:ℝ) / (16.47855:ℝ) + (1:ℝ) / (25.91203:ℝ))
      + (0.0647174928:ℝ) * ((0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))) + (0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))))))

/-- Design cell 23: margin 0.000878 (exact). -/
theorem s8_cell23 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.11588:ℝ))
    (hc6l : (2.23176:ℝ) ≤ y6) (hc6h : y6 ≤ (2.34764:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.11588:ℝ) * (2.11588:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.23176:ℝ) * (2.23176:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.34764:ℝ) * (2.34764:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.23176:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (23.72586:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.34764:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := by norm_num
    have hbr : (23.72586:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.34764:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.34764:ℝ) * (2.34764:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (16.45014:ℝ) ≤ s8a2sq ((8:ℝ)) (2:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.23176:ℝ) + ((2:ℝ) * (2:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (16.45014:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.23176:ℝ) + ((2:ℝ) * (2:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.23176:ℝ) + ((2:ℝ) * (2:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.23176:ℝ) + ((2:ℝ) * (2:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.23176:ℝ) + ((2:ℝ) * (2:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.23176:ℝ) + ((2:ℝ) * (2:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.23176:ℝ) * (2.23176:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (28.1338:ℝ) ≤ s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    have hbr : (28.1338:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.11588:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.23176:ℝ) * (2.23176:ℝ)) (bh := (2.11588:ℝ) * (2.11588:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.23176:ℝ) * (2.23176:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.34764:ℝ) * (2.34764:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ))
  have hl5v : (0.77715384:ℝ) ≤ lfun ((2.11588:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.33146153:ℝ) ≤ lfun ((2.34764:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.11588:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.11588:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.34764:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.34764:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (8:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.11588:ℝ)) (q6l := (2.23176:ℝ)) (q6h := (2.34764:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))
    (ea1L := (23.72586:ℝ)) (ea2L := (16.45014:ℝ)) (ea3L := (28.1338:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) (dx6L := (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))
    (l5 := (0.77715384:ℝ)) (l6 := (0.33146153:ℝ))
    (D5b := (2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.34764:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.11588:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.34764:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (by norm_num : (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) ≤ (3:ℝ) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (23.72586:ℝ) + (1:ℝ) / (16.45014:ℝ) + (1:ℝ) / (28.1338:ℝ))
      + (0.0647174928:ℝ) * ((0.77715384:ℝ) * (((2:ℝ) / ((2.11588:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))))) / (3:ℝ)))) + (0.33146153:ℝ) * (((2:ℝ) / ((2.34764:ℝ) * ((8:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))))) / (3:ℝ))))))

/-- Design cell 24: margin 0.004481 (exact). -/
theorem s8_cell24 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.11588:ℝ) ≤ y5) (hc5h : y5 ≤ (2.23176:ℝ))
    (hc6l : (2.23176:ℝ) ≤ y6) (hc6h : y6 ≤ (2.34764:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.23176:ℝ) * (2.23176:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.34764:ℝ) * (2.34764:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.23176:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (25.5368:ℝ) ≤ s8a1 (2.6508:ℝ) (2.11588:ℝ) (2.34764:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := by norm_num
    have hbr : (25.5368:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.11588:ℝ) (2.34764:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.34764:ℝ) * (2.34764:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (17.97393:ℝ) ≤ s8a2sq ((8:ℝ)) (2.11588:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.11588:ℝ) * (2.23176:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (17.97393:ℝ) ≤ ((2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2.23176:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.11588:ℝ) * (2.23176:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.11588:ℝ) * (2.23176:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.11588:ℝ) * (2.23176:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) ≤
        ((2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.11588:ℝ) * (2.23176:ℝ) + ((2.11588:ℝ) * (2.11588:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.11588:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.11588:ℝ) * (2.11588:ℝ)) (cl := (2.23176:ℝ) * (2.23176:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (27.77756:ℝ) ≤ s8a3 (2.6508:ℝ) (2.23176:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (27.77756:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.23176:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.23176:ℝ) * (2.23176:ℝ)) (cl := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.23176:ℝ) * (2.23176:ℝ)) (bh := (2.23176:ℝ) * (2.23176:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hdx6 : (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.23176:ℝ) * (2.23176:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.11588:ℝ) * (2.11588:ℝ)) (ch := (2.34764:ℝ) * (2.34764:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ))
  have hl5v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.33146153:ℝ) ≤ lfun ((2.34764:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.34764:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.34764:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.11588:ℝ)) (p5h := (2.23176:ℝ)) (q6l := (2.23176:ℝ)) (q6h := (2.34764:ℝ))
    (Dh := 2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))
    (ea1L := (25.5368:ℝ)) (ea2L := (17.97393:ℝ)) (ea3L := (27.77756:ℝ))
    (dx5L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) (dx6L := (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))
    (l5 := (0.55430769:ℝ)) (l6 := (0.33146153:ℝ))
    (D5b := (2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.34764:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (0:ℝ) < (2.34764:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) ≤ (3:ℝ) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (25.5368:ℝ) + (1:ℝ) / (17.97393:ℝ) + (1:ℝ) / (27.77756:ℝ))
      + (0.0647174928:ℝ) * ((0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))) + (0.33146153:ℝ) * (((2:ℝ) / ((2.34764:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.11588:ℝ) * (2.11588:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.11588:ℝ) * (2.11588:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))))) / (3:ℝ))))))

/-- Design cell 25: margin 0.001729 (exact). -/
theorem s8_cell25 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2:ℝ) ≤ y5) (hc5h : y5 ≤ (2.23176:ℝ))
    (hc6l : (2.34764:ℝ) ≤ y6) (hc6h : y6 ≤ (2.46352:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2:ℝ) * (2:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.34764:ℝ) * (2.34764:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.34764:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.46352:ℝ) * (2.46352:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.34764:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (23.33163:ℝ) ≤ s8a1 (2.6508:ℝ) (2:ℝ) (2.46352:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := by norm_num
    have hbr : (23.33163:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2:ℝ) + (2.6508:ℝ) * (2:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2:ℝ) (2.46352:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2:ℝ) * (2:ℝ)) (ch := (2.46352:ℝ) * (2.46352:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (17.91555:ℝ) ≤ s8a2sq ((8:ℝ)) (2:ℝ) (2.34764:ℝ) := by
    have hs : (0:ℝ) ≤ ((2:ℝ) * (2.34764:ℝ) + ((2:ℝ) * (2:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (17.91555:ℝ) ≤ ((2:ℝ) * (2:ℝ) * (2.34764:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.34764:ℝ) + ((2:ℝ) * (2:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2:ℝ) * (2.34764:ℝ) + ((2:ℝ) * (2:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2:ℝ) * (2.34764:ℝ) + ((2:ℝ) * (2:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2:ℝ) * (2:ℝ) * (2.34764:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) * (2:ℝ)) / 2 + (1.41421356:ℝ) * ((2:ℝ) * (2.34764:ℝ) + ((2:ℝ) * (2:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (8:ℝ)) / 2) ≤
        ((2:ℝ) * (2:ℝ) * (2.34764:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) * (2:ℝ)) / 2 + Real.sqrt 2 * ((2:ℝ) * (2.34764:ℝ) + ((2:ℝ) * (2:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2:ℝ) * (2:ℝ) * (2.34764:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) * (2:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2:ℝ) (2.34764:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.34764:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2:ℝ) * (2:ℝ)) (cl := (2.34764:ℝ) * (2.34764:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.34764:ℝ) * (2.34764:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (29.69767:ℝ) ≤ s8a3 (2.6508:ℝ) (2.23176:ℝ) (2.34764:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.34764:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (29.69767:ℝ) ≤ ((2.6508:ℝ) * (2.34764:ℝ) * (2.34764:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.34764:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.34764:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.34764:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.34764:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.34764:ℝ) * (2.34764:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.34764:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.34764:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.34764:ℝ) * (2.34764:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.34764:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.34764:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.34764:ℝ) * (2.34764:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.34764:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.23176:ℝ) (2.34764:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.34764:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.23176:ℝ) * (2.23176:ℝ)) (cl := (2.34764:ℝ) * (2.34764:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2:ℝ) * (2:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.34764:ℝ) * (2.34764:ℝ)) (bh := (2.23176:ℝ) * (2.23176:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2:ℝ) * (2:ℝ))
  have hdx6 : (2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.34764:ℝ) * (2.34764:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2:ℝ) * (2:ℝ)) (ch := (2.46352:ℝ) * (2.46352:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.34764:ℝ) * (2.34764:ℝ))
  have hl5v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.10861538:ℝ) ≤ lfun ((2.46352:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.46352:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.46352:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (8:ℝ))
    (p5l := (2:ℝ)) (p5h := (2.23176:ℝ)) (q6l := (2.34764:ℝ)) (q6h := (2.46352:ℝ))
    (Dh := 2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))
    (ea1L := (23.33163:ℝ)) (ea2L := (17.91555:ℝ)) (ea3L := (29.69767:ℝ))
    (dx5L := (2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) (dx6L := (2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))
    (l5 := (0.55430769:ℝ)) (l6 := (0.10861538:ℝ))
    (D5b := (2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.46352:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))) / ((((2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2:ℝ) * (2:ℝ)))
    (by norm_num : (0:ℝ) < (2.46352:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))) ≤ (3:ℝ) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))) ≤ (3:ℝ) * (((2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (23.33163:ℝ) + (1:ℝ) / (17.91555:ℝ) + (1:ℝ) / (29.69767:ℝ))
      + (0.0647174928:ℝ) * ((0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2:ℝ) * (2:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))) / ((((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2:ℝ) * (2:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))) + (0.10861538:ℝ) * (((2:ℝ) / ((2.46352:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2:ℝ) * (2:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2:ℝ) * (2:ℝ)) * ((2.34764:ℝ) * (2.34764:ℝ)))) / ((((2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.34764:ℝ) * (2.34764:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2:ℝ) * (2:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))))) / (3:ℝ))))))

/-- Design cell 27: margin 0.004481 (exact). -/
theorem s8_cell27 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.23176:ℝ) ≤ y5) (hc5h : y5 ≤ (2.34764:ℝ))
    (hc6l : (2.11588:ℝ) ≤ y6) (hc6h : y6 ≤ (2.23176:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.23176:ℝ) * (2.23176:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.34764:ℝ) * (2.34764:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.11588:ℝ) * (2.11588:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.23176:ℝ) * (2.23176:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.23176:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.11588:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (27.77756:ℝ) ≤ s8a1 (2.6508:ℝ) (2.23176:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    have hbr : (27.77756:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.23176:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.23176:ℝ) * (2.23176:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (17.97393:ℝ) ≤ s8a2sq ((8:ℝ)) (2.23176:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.23176:ℝ) * (2.11588:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (17.97393:ℝ) ≤ ((2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.23176:ℝ) * (2.11588:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.23176:ℝ) * (2.11588:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.23176:ℝ) * (2.11588:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.23176:ℝ) * (2.11588:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) ≤
        ((2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.23176:ℝ) * (2.11588:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.23176:ℝ) * (2.23176:ℝ) * (2.11588:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.23176:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.23176:ℝ) * (2.23176:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (25.5368:ℝ) ≤ s8a3 (2.6508:ℝ) (2.34764:ℝ) (2.11588:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := by norm_num
    have hbr : (25.5368:ℝ) ≤ ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.11588:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.11588:ℝ) * (2.11588:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.11588:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.34764:ℝ) (2.11588:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.34764:ℝ) * (2.34764:ℝ)) (cl := (2.11588:ℝ) * (2.11588:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.23176:ℝ) * (2.23176:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.11588:ℝ) * (2.11588:ℝ)) (bh := (2.34764:ℝ) * (2.34764:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ))
  have hdx6 : (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.11588:ℝ) * (2.11588:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.23176:ℝ) * (2.23176:ℝ)) (ch := (2.23176:ℝ) * (2.23176:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.11588:ℝ) * (2.11588:ℝ))
  have hl5v : (0.33146153:ℝ) ≤ lfun ((2.34764:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.55430769:ℝ) ≤ lfun ((2.23176:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.34764:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.34764:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.23176:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.23176:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.23176:ℝ)) (p5h := (2.34764:ℝ)) (q6l := (2.11588:ℝ)) (q6h := (2.23176:ℝ))
    (Dh := 2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))
    (ea1L := (27.77756:ℝ)) (ea2L := (17.97393:ℝ)) (ea3L := (25.5368:ℝ))
    (dx5L := (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))) (dx6L := (2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (l5 := (0.33146153:ℝ)) (l6 := (0.55430769:ℝ))
    (D5b := (2:ℝ) / ((2.34764:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.34764:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (by norm_num : (0:ℝ) < (2.23176:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)))
    (by norm_num : (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) ≤ (3:ℝ) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (27.77756:ℝ) + (1:ℝ) / (17.97393:ℝ) + (1:ℝ) / (25.5368:ℝ))
      + (0.0647174928:ℝ) * ((0.33146153:ℝ) * (((2:ℝ) / ((2.34764:ℝ) * ((8:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.34764:ℝ) * (2.34764:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.11588:ℝ) * (2.11588:ℝ) - (2.34764:ℝ) * (2.34764:ℝ))))) / (3:ℝ)))) + (0.55430769:ℝ) * (((2:ℝ) / ((2.23176:ℝ) * ((8:ℝ) + (2.34764:ℝ) * (2.34764:ℝ) - (2.11588:ℝ) * (2.11588:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.11588:ℝ) * (2.11588:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.11588:ℝ) * (2.11588:ℝ)))) / ((((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))) * (((2.11588:ℝ) * (2.11588:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))))) / (3:ℝ))))))

/-- Design cell 29: margin 0.003834 (exact). -/
theorem s8_cell29 {y4 y5 y6 : ℝ}
    (hy4 : (2:ℝ) ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : (2:ℝ) ≤ y5) (hy5' : y5 ≤ (2.46352:ℝ))
    (hy6 : (2:ℝ) ≤ y6) (hy6' : y6 ≤ (2.46352:ℝ))
    (hc4l : (2.6508:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.23176:ℝ) ≤ y5) (hc5h : y5 ≤ (2.46352:ℝ))
    (hc6l : (2.23176:ℝ) ≤ y6) (hc6h : y6 ≤ (2.46352:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have hy4n : (0:ℝ) ≤ y4 := le_trans (by norm_num) hy4
  have hy5n : (0:ℝ) ≤ y5 := le_trans (by norm_num) hy5
  have hy6n : (0:ℝ) ≤ y6 := le_trans (by norm_num) hy6
  have hP4Lsq : (2.6508:ℝ) * (2.6508:ℝ) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.6508:ℝ)) hc4l
  have hP4Hsq : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4n hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hB5sq : (2.23176:ℝ) * (2.23176:ℝ) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) hc5l
  have hB5hsq : y5 * y5 ≤ (2.46352:ℝ) * (2.46352:ℝ) :=
    mul_self_le_mul_self hy5n hc5h
  have hC6sq : (2.23176:ℝ) * (2.23176:ℝ) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) hc6l
  have hC6hsq : y6 * y6 ≤ (2.46352:ℝ) * (2.46352:ℝ) :=
    mul_self_le_mul_self hy6n hc6h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) :=
    s8_dlt_corner hy4 hy5 hy6 (by norm_num : (2:ℝ) ≤ (2.23176:ℝ))
      (by norm_num : (2:ℝ) ≤ (2.23176:ℝ)) (by norm_num : (4:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ))
      hP4Lsq hB5sq hC6sq
  have hb2 : (1.41421356:ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hea1v : (27.0081:ℝ) ≤ s8a1 (2.6508:ℝ) (2.23176:ℝ) (2.46352:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := by norm_num
    have hbr : (27.0081:ℝ) ≤ ((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := by norm_num
    unfold s8a1
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea1c : s8a1 (2.6508:ℝ) (2.23176:ℝ) (2.46352:ℝ) ≤
      Kepler.NliBanks20.ea4X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a1_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))]
    exact s8_ea4_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bl := (2.23176:ℝ) * (2.23176:ℝ)) (ch := (2.46352:ℝ) * (2.46352:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Lsq hB5sq hC6hsq
  have hea2v : (19.54668:ℝ) ≤ s8a2sq ((8:ℝ)) (2.23176:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.23176:ℝ) * (2.23176:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := by norm_num
    have hbr : (19.54668:ℝ) ≤ ((2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := by norm_num
    unfold s8a2sq
    have h1 : (1.41421356:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.23176:ℝ) * (2.23176:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) ≤
        ((2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.23176:ℝ) * (2.23176:ℝ) + ((2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (8:ℝ)) / 2) := add_le_add_right h1 (((2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea2c : s8a2sq ((8:ℝ)) (2.23176:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea5X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a2sq_eq (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ)) ((8:ℝ))]
    exact s8_ea5_min (al := y4*y4) (bl := (2.23176:ℝ) * (2.23176:ℝ)) (cl := (2.23176:ℝ) * (2.23176:ℝ))
      (ah := (8:ℝ)) (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ)) (mul_nonneg hy5n hy5n)
      hP4Hsq hB5sq hC6sq
  have hea3v : (27.0081:ℝ) ≤ s8a3 (2.6508:ℝ) (2.46352:ℝ) (2.23176:ℝ) := by
    have hs : (0:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := by norm_num
    have hbr : (27.0081:ℝ) ≤ ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := by norm_num
    unfold s8a3
    have h1 : (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) ≤ Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right hb2 hs
    have hstep : ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + (1.41421356:ℝ) * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) ≤
        ((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2 + Real.sqrt 2 * ((2.6508:ℝ) * (2.23176:ℝ) + ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) / 2) := add_le_add_right h1 (((2.6508:ℝ) * (2.23176:ℝ) * (2.23176:ℝ) + (2.6508:ℝ) * (2.6508:ℝ) * (2.23176:ℝ)) / 2)
    linarith [hbr, hstep]
  have hea3c : s8a3 (2.6508:ℝ) (2.46352:ℝ) (2.23176:ℝ) ≤
      Kepler.NliBanks20.ea6X (y5*y5) (y6*y6) (y4*y4) := by
    rw [← s8a3_eq (by norm_num : (0:ℝ) ≤ (2.6508:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ))]
    exact s8_ea6_min (al := (2.6508:ℝ) * (2.6508:ℝ)) (bh := (2.46352:ℝ) * (2.46352:ℝ)) (cl := (2.23176:ℝ) * (2.23176:ℝ))
      (A := y4*y4) (B := y5*y5) (C := y6*y6)
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) (mul_nonneg hy6n hy6n)
      hB5hsq hC6sq hP4Lsq
  have hdx5 : (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    Kepler.NliBanks20.dx5_ge (bl := (2.23176:ℝ) * (2.23176:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (cl := (2.23176:ℝ) * (2.23176:ℝ)) (bh := (2.46352:ℝ) * (2.46352:ℝ)) hB5sq hP4Lsq hC6sq hB5hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ))
  have hdx6 : (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)) ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    Kepler.NliBanks20.dx6_ge (cl := (2.23176:ℝ) * (2.23176:ℝ)) (al := (2.6508:ℝ) * (2.6508:ℝ))
      (bl := (2.23176:ℝ) * (2.23176:ℝ)) (ch := (2.46352:ℝ) * (2.46352:ℝ)) hC6sq hP4Lsq hB5sq hC6hsq
      (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))
      (by norm_num : (0:ℝ) ≤ (2.23176:ℝ) * (2.23176:ℝ))
  have hl5v : (0.10861538:ℝ) ≤ lfun ((2.46352:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl6v : (0.10861538:ℝ) ≤ lfun ((2.46352:ℝ) * 0.5) := by norm_num [lfun, h0]
  have hl5' : lfun ((2.46352:ℝ) * 0.5) ≤ lfun (y5 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc5h (by norm_num [h0] : (2.46352:ℝ) * 0.5 ≤ h0)
  have hl6' : lfun ((2.46352:ℝ) * 0.5) ≤ lfun (y6 * 0.5) :=
    Kepler.NliBanks20.lfun_half_ge hc6h (by norm_num [h0] : (2.46352:ℝ) * 0.5 ≤ h0)
  exact s8_cell (P4L := (2.6508:ℝ) * (2.6508:ℝ)) (P4H := (8:ℝ))
    (p5l := (2.23176:ℝ)) (p5h := (2.46352:ℝ)) (q6l := (2.23176:ℝ)) (q6h := (2.46352:ℝ))
    (Dh := 2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))
    (ea1L := (27.0081:ℝ)) (ea2L := (19.54668:ℝ)) (ea3L := (27.0081:ℝ))
    (dx5L := (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))) (dx6L := (2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))
    (l5 := (0.10861538:ℝ)) (l6 := (0.10861538:ℝ))
    (D5b := (2:ℝ) / ((2.46352:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))))) / (3:ℝ))) (D6b := (2:ℝ) / ((2.46352:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))))) / (3:ℝ)))
    hy4 hy5 hy6 hc5h hc6h hP4Lsq hP4Hsq hB5sq hB5hsq hC6sq hC6hsq
    (by norm_num : (0:ℝ) ≤ (2.6508:ℝ) * (2.6508:ℝ)) hd0 hdh (le_trans hd0 hdh)
    (hea1v.trans hea1c) (by norm_num) (hea2v.trans hea2c) (by norm_num)
    (hea3v.trans hea3c) (by norm_num)
    hdx5 (by norm_num) hdx6 (by norm_num)
    (hl5v.trans hl5') (by norm_num) (hl6v.trans hl6') (by norm_num)
    (by norm_num : (0:ℝ) < (2.46352:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (by norm_num : (0:ℝ) < (2.46352:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)))
    (by norm_num : (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) ≤ (3:ℝ) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))))
    (by norm_num : (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) ≤ (3:ℝ) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))))
    rfl rfl
    (by norm_num : (0:ℝ) < 1 / 12 - (0.6443107122:ℝ) *
      ((1:ℝ) / (27.0081:ℝ) + (1:ℝ) / (19.54668:ℝ) + (1:ℝ) / (27.0081:ℝ))
      + (0.0647174928:ℝ) * ((0.10861538:ℝ) * (((2:ℝ) / ((2.46352:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))))) / (3:ℝ)))) + (0.10861538:ℝ) * (((2:ℝ) / ((2.46352:ℝ) * ((8:ℝ) + (2.46352:ℝ) * (2.46352:ℝ) - (2.23176:ℝ) * (2.23176:ℝ))) * ((1:ℝ) - (4:ℝ) * ((2.46352:ℝ) * (2.46352:ℝ)) * ((2 * (4 * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)) - ((2.6508:ℝ) * (2.6508:ℝ) - (2.23176:ℝ) * (2.23176:ℝ) - (2.23176:ℝ) * (2.23176:ℝ)) ^ 2) - (2.6508:ℝ) * (2.6508:ℝ) * ((2.23176:ℝ) * (2.23176:ℝ)) * ((2.23176:ℝ) * (2.23176:ℝ)))) / ((((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ)))) * (((2.23176:ℝ) * (2.23176:ℝ) * ((2.6508:ℝ) * (2.6508:ℝ) + (2.23176:ℝ) * (2.23176:ℝ) - (2.46352:ℝ) * (2.46352:ℝ))))) / (3:ℝ))))))

/-! ## 8. The dispatch tree -/
/-- Left disjunct on the normalized half `y5 ≤ y6`: the 30-leaf cover
(26 half cells + 4 off-half absurd leaves). -/
theorem s8_half {y4 y5 y6 : ℝ} (h4 : 2 * hplus ≤ y4)
    (h4' : y4 ≤ Real.sqrt 8) (h5 : (2:ℝ) ≤ y5) (h5' : y5 ≤ 2 * hminus)
    (h6 : (2:ℝ) ≤ y6) (h6' : y6 ≤ 2 * hminus) (hy56 : y5 ≤ y6)
    (hdlt : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  have h4d : (2.6508:ℝ) ≤ y4 := by
    have h := h4
    rw [show (2:ℝ) * hplus = (2.6508:ℝ) from by norm_num [hplus]] at h
    exact h
  have hhm5 : y5 ≤ (2.46352:ℝ) :=
    h5'.trans Kepler.NliBanks17.nb17_two_hminus_bounds.2
  have hhm6 : y6 ≤ (2.46352:ℝ) :=
    h6'.trans Kepler.NliBanks17.nb17_two_hminus_bounds.2
  by_cases h51 : y5 ≤ (2.23176:ℝ)
  · by_cases h62 : y6 ≤ (2.23176:ℝ)
    · by_cases h53 : y5 ≤ (2.11588:ℝ)
      · by_cases h64 : y6 ≤ (2.11588:ℝ)
        · by_cases h45 : y4 ≤ (2.72:ℝ)
          · by_cases h56 : y5 ≤ (2.05794:ℝ)
            · by_cases h67 : y6 ≤ (2.05794:ℝ)
              · by_cases h48 : y4 ≤ (2.683:ℝ)
                · by_cases h59 : y5 ≤ (2.02897:ℝ)
                  · by_cases h610 : y6 ≤ (2.02897:ℝ)
                    · exact s8_cell00 (hy4 := by linarith) (hy4' := h4')
                        (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                        (hc4l := h4d) (hc4h := (by linarith))
                        (hc5l := by linarith) (hc5h := by linarith)
                        (hc6l := by linarith) (hc6h := by linarith)
                        (hd0 := hdlt)
                    · exact s8_cell01 (hy4 := by linarith) (hy4' := h4')
                        (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                        (hc4l := h4d) (hc4h := (by linarith))
                        (hc5l := by linarith) (hc5h := by linarith)
                        (hc6l := by linarith) (hc6h := by linarith)
                        (hd0 := hdlt)
                  · exact s8_cell02 (hy4 := by linarith) (hy4' := h4')
                      (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                      (hc4l := h4d) (hc4h := (by linarith))
                      (hc5l := by linarith) (hc5h := by linarith)
                      (hc6l := by linarith) (hc6h := by linarith)
                      (hd0 := hdlt)
                · by_cases h511 : y5 ≤ (2.02897:ℝ)
                  · exact s8_cell03 (hy4 := by linarith) (hy4' := h4')
                      (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                      (hc4l := (by linarith)) (hc4h := (by linarith))
                      (hc5l := by linarith) (hc5h := by linarith)
                      (hc6l := by linarith) (hc6h := by linarith)
                      (hd0 := hdlt)
                  · exact s8_cell04 (hy4 := by linarith) (hy4' := h4')
                      (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                      (hc4l := (by linarith)) (hc4h := (by linarith))
                      (hc5l := by linarith) (hc5h := by linarith)
                      (hc6l := by linarith) (hc6h := by linarith)
                      (hd0 := hdlt)
              · exact s8_cell05 (hy4 := by linarith) (hy4' := h4')
                  (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                  (hc4l := h4d) (hc4h := (by linarith))
                  (hc5l := by linarith) (hc5h := by linarith)
                  (hc6l := by linarith) (hc6h := by linarith)
                  (hd0 := hdlt)
            · by_cases h612 : y6 ≤ (2.05794:ℝ)
              · exact s8_cell06 (hy4 := by linarith) (hy4' := h4')
                  (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                  (hc4l := h4d) (hc4h := (by linarith))
                  (hc5l := by linarith) (hc5h := by linarith)
                  (hc6l := by linarith) (hc6h := by linarith)
                  (hd0 := hdlt)
              · exact s8_cell07 (hy4 := by linarith) (hy4' := h4')
                  (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                  (hc4l := h4d) (hc4h := (by linarith))
                  (hc5l := by linarith) (hc5h := by linarith)
                  (hc6l := by linarith) (hc6h := by linarith)
                  (hd0 := hdlt)
          · by_cases h513 : y5 ≤ (2.05794:ℝ)
            · by_cases h614 : y6 ≤ (2.05794:ℝ)
              · by_cases h415 : y4 ≤ (2.78:ℝ)
                · by_cases h516 : y5 ≤ (2.02897:ℝ)
                  · exact s8_cell08 (hy4 := by linarith) (hy4' := h4')
                      (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                      (hc4l := (by linarith)) (hc4h := (by linarith))
                      (hc5l := by linarith) (hc5h := by linarith)
                      (hc6l := by linarith) (hc6h := by linarith)
                      (hd0 := hdlt)
                  · exact s8_cell09 (hy4 := by linarith) (hy4' := h4')
                      (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                      (hc4l := (by linarith)) (hc4h := (by linarith))
                      (hc5l := by linarith) (hc5h := by linarith)
                      (hc6l := by linarith) (hc6h := by linarith)
                      (hd0 := hdlt)
                · exact s8_cell10 (hy4 := by linarith) (hy4' := h4')
                    (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                    (hc4l := (by linarith)) (hc4h := h4')
                    (hc5l := by linarith) (hc5h := by linarith)
                    (hc6l := by linarith) (hc6h := by linarith)
                    (hd0 := hdlt)
              · exact s8_cell11 (hy4 := by linarith) (hy4' := h4')
                  (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                  (hc4l := (by linarith)) (hc4h := h4')
                  (hc5l := by linarith) (hc5h := by linarith)
                  (hc6l := by linarith) (hc6h := by linarith)
                  (hd0 := hdlt)
            · by_cases h617 : y6 ≤ (2.05794:ℝ)
              · exact s8_cell12 (hy4 := by linarith) (hy4' := h4')
                  (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                  (hc4l := (by linarith)) (hc4h := h4')
                  (hc5l := by linarith) (hc5h := by linarith)
                  (hc6l := by linarith) (hc6h := by linarith)
                  (hd0 := hdlt)
              · exact s8_cell13 (hy4 := by linarith) (hy4' := h4')
                  (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                  (hc4l := (by linarith)) (hc4h := h4')
                  (hc5l := by linarith) (hc5h := by linarith)
                  (hc6l := by linarith) (hc6h := by linarith)
                  (hd0 := hdlt)
        · by_cases h418 : y4 ≤ (2.72:ℝ)
          · by_cases h619 : y6 ≤ (2.17382:ℝ)
            · exact s8_cell14 (hy4 := by linarith) (hy4' := h4')
                (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                (hc4l := h4d) (hc4h := (by linarith))
                (hc5l := by linarith) (hc5h := by linarith)
                (hc6l := by linarith) (hc6h := by linarith)
                (hd0 := hdlt)
            · exact s8_cell15 (hy4 := by linarith) (hy4' := h4')
                (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                (hc4l := h4d) (hc4h := (by linarith))
                (hc5l := by linarith) (hc5h := by linarith)
                (hc6l := by linarith) (hc6h := by linarith)
                (hd0 := hdlt)
          · by_cases h620 : y6 ≤ (2.17382:ℝ)
            · exact s8_cell16 (hy4 := by linarith) (hy4' := h4')
                (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                (hc4l := (by linarith)) (hc4h := h4')
                (hc5l := by linarith) (hc5h := by linarith)
                (hc6l := by linarith) (hc6h := by linarith)
                (hd0 := hdlt)
            · exact s8_cell17 (hy4 := by linarith) (hy4' := h4')
                (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                (hc4l := (by linarith)) (hc4h := h4')
                (hc5l := by linarith) (hc5h := by linarith)
                (hc6l := by linarith) (hc6h := by linarith)
                (hd0 := hdlt)
      · by_cases h621 : y6 ≤ (2.11588:ℝ)
        · by_cases h422 : y4 ≤ (2.72:ℝ)
          · by_cases h523 : y5 ≤ (2.17382:ℝ)
            · exact s8_cell18 (hy4 := by linarith) (hy4' := h4')
                (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                (hc4l := h4d) (hc4h := (by linarith))
                (hc5l := by linarith) (hc5h := by linarith)
                (hc6l := by linarith) (hc6h := by linarith)
                (hd0 := hdlt)
            · exact absurd (le_trans (by linarith : (2.17382:ℝ) ≤ y5) (le_trans hy56 (by linarith : y6 ≤ (2.11588:ℝ)))) (by norm_num : ¬ (2.17382:ℝ) ≤ (2.11588:ℝ))
          · by_cases h524 : y5 ≤ (2.17382:ℝ)
            · exact s8_cell20 (hy4 := by linarith) (hy4' := h4')
                (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
                (hc4l := (by linarith)) (hc4h := h4')
                (hc5l := by linarith) (hc5h := by linarith)
                (hc6l := by linarith) (hc6h := by linarith)
                (hd0 := hdlt)
            · exact absurd (le_trans (by linarith : (2.17382:ℝ) ≤ y5) (le_trans hy56 (by linarith : y6 ≤ (2.11588:ℝ)))) (by norm_num : ¬ (2.17382:ℝ) ≤ (2.11588:ℝ))
        · exact s8_cell22 (hy4 := by linarith) (hy4' := h4')
            (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
            (hc4l := h4d) (hc4h := h4')
            (hc5l := by linarith) (hc5h := by linarith)
            (hc6l := by linarith) (hc6h := by linarith)
            (hd0 := hdlt)
    · by_cases h625 : y6 ≤ (2.34764:ℝ)
      · by_cases h526 : y5 ≤ (2.11588:ℝ)
        · exact s8_cell23 (hy4 := by linarith) (hy4' := h4')
            (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
            (hc4l := h4d) (hc4h := h4')
            (hc5l := by linarith) (hc5h := by linarith)
            (hc6l := by linarith) (hc6h := by linarith)
            (hd0 := hdlt)
        · exact s8_cell24 (hy4 := by linarith) (hy4' := h4')
            (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
            (hc4l := h4d) (hc4h := h4')
            (hc5l := by linarith) (hc5h := by linarith)
            (hc6l := by linarith) (hc6h := by linarith)
            (hd0 := hdlt)
      · exact s8_cell25 (hy4 := by linarith) (hy4' := h4')
          (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
          (hc4l := h4d) (hc4h := h4')
          (hc5l := by linarith) (hc5h := by linarith)
          (hc6l := by linarith) (hc6h := by linarith)
          (hd0 := hdlt)
  · by_cases h627 : y6 ≤ (2.23176:ℝ)
    · by_cases h528 : y5 ≤ (2.34764:ℝ)
      · by_cases h629 : y6 ≤ (2.11588:ℝ)
        · exact absurd (le_trans (by linarith : (2.23176:ℝ) ≤ y5) (le_trans hy56 (by linarith : y6 ≤ (2.11588:ℝ)))) (by norm_num : ¬ (2.23176:ℝ) ≤ (2.11588:ℝ))
        · exact s8_cell27 (hy4 := by linarith) (hy4' := h4')
            (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
            (hc4l := h4d) (hc4h := h4')
            (hc5l := by linarith) (hc5h := by linarith)
            (hc6l := by linarith) (hc6h := by linarith)
            (hd0 := hdlt)
      · exact absurd (le_trans (by linarith : (2.34764:ℝ) ≤ y5) (le_trans hy56 (by linarith : y6 ≤ (2.23176:ℝ)))) (by norm_num : ¬ (2.34764:ℝ) ≤ (2.23176:ℝ))
    · exact s8_cell29 (hy4 := by linarith) (hy4' := h4')
        (hy5 := h5) (hy5' := hhm5) (hy6 := h6) (hy6' := hhm6)
        (hc4l := h4d) (hc4h := h4')
        (hc5l := by linarith) (hc5h := by linarith)
        (hc6l := by linarith) (hc6h := by linarith)
        (hd0 := hdlt)

/-! ## 9. The bank -/
/-- **`nliCell3QZECFICwt0sqrt8` closed**: the disjunctive bank over the
sqrt8 box.  Right disjunct via the Delta-to-eta stone; left disjunct via
the kernel symmetry and the 26-cell certificate battery. -/
theorem s8_bank : bank_QZECFICwt0sqrt8 := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  by_cases hdlt : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
  · left
    rw [Kepler.NliBanks11.nb11_c3_indep]
    by_cases hy56 : y5 ≤ y6
    · exact s8_half h4 h4' h5 h5' h6 h6' hy56 hdlt
    · rw [s8_c3_symm (le_trans (by norm_num [hplus] : (0:ℝ) ≤ 2 * hplus) h4)
        (le_trans (by norm_num : (0:ℝ) ≤ (2:ℝ)) h5)
        (le_trans (by norm_num : (0:ℝ) ≤ (2:ℝ)) h6)]
      exact s8_half h4 h4' h6 h6' h5 h5' (by linarith)
        (by rw [Kepler.NliBanks20.dlt4_eq]; exact hdlt)
  · right
    exact s8_eta_dlt_neg h4 h4' h5 h5' h6 h6' (lt_of_not_ge hdlt)

/-! ## 10. Axiom audit -/
#print axioms s8_c3_unfold_sq
#print axioms s8_dlt_corner
#print axioms s8_ea4_min
#print axioms s8_ea5_min
#print axioms s8_ea6_min
#print axioms s8_cell
#print axioms s8_se_swap13
#print axioms s8_dih_swap35
#print axioms s8_c3_symm
#print axioms s8_eta_dlt_neg
#print axioms s8_half
#print axioms s8_bank

end Kepler.Text.NliSqrt8

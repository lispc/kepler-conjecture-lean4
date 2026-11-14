/-
  TSKAJXY-XLLIPLS (HOL ineq entry `TSKAJXY-XLLIPLS`, ineq.hl:304) — G4 glue.

  `bank_TSKAJXYXLLIPLS` (PackingAuto21:308) is
  `∀ y ∈ [2*hplus, sqrt 8] x [2,2.01]^2 x [2*hplus,2.8] x [2,2.01]^2,
     0 < gamma4fgcy y1..y6 lmfun`.

  This module supplies the **real identity** between the certificate
  expression (`Kepler.Interval.Cases.TskXLLIPLSExpr`, the `bb_arb` case
  program of `pipeline/interval/out/cases/TSKAJXY-XLLIPLS.json`, 19,614 AST
  nodes / 60 `ite` / 79 `sqrt` / 143 `atan`) and the Lean definition
  `gamma4fgcy`, plus the box membership.  The certificate itself (a
  `checkPosTMHullC` full-coverage hull tree over 6,512 leaves) is a separate
  generated module; `packIneqTskXLLIPLS_of_hull` below is the conditional
  closer that consumes it.

  The identity holds **for every point of ℝ⁶** — no box hypothesis: the case
  program is a node-for-node transcription of `gamma4fgcy`'s definition
  (`pipeline/interval/emit_rpn.py` expands `pi → 4*atan 1`, `acos` by the
  half-angle, `h0` as `63/50`, and encodes each `if c then t else e` as the
  strict RPN `ite(c_as_sub < 0, …)`), so after normalising those four
  constant/guard forms both sides are the same term.

  No new axiom / sorry / native_decide; no new mathematics (the only real
  facts used are `arctan 1 = pi/4` and the `arccos` half-angle, both in
  Mathlib / `TskXLLIPLSLemmas`).
-/
import Kepler.Text.PackingAuto21
import Kepler.Text.TskXLLIPLSLemmas
import Kepler.Interval.Cases.TskXLLIPLSBase
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option pp.deepTerms true
set_option pp.maxSteps 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Kepler.Text

open Kepler.Interval

/-! ## The certificate box -/

/-- The TM-certificate root box, exactly the `bb_arb` case box of
`pipeline/interval/out/cases/TSKAJXY-XLLIPLS.json`:
`[2846274827/2^30, 759250125/2^28] x [2, 2158221067/2^30]^2
 x [2846274827/2^30, 751619277/2^28] x [2, 2158221067/2^30]^2`.

`2846274827/2^30 = 2.6507999999…` is the dyadic floor of `2*hplus = 2.6508`,
`759250125/2^28 = 2.8284271247…` the dyadic ceiling of `sqrt 8`,
`2158221067/2^30` that of `2.01`, `751619277/2^28` that of `2.8`, so the
certificate box strictly contains the bank box.  The literals are the
**normalised** dyadic form (odd mantissas) — `checkPosTMHullC`'s
`boxCenter`/`DInterval.mid` and `Dyadic.sqrtI` are sensitive to unnormalised
representations (biefjhu-tm-w2 DELIVERY §4.4). -/
def tskCertBox : Fin 6 → DInterval :=
  ![⟨⟨2846274827, -30⟩, ⟨759250125, -28⟩⟩, ⟨⟨2, 0⟩, ⟨2158221067, -30⟩⟩,
    ⟨⟨2, 0⟩, ⟨2158221067, -30⟩⟩, ⟨⟨2846274827, -30⟩, ⟨751619277, -28⟩⟩,
    ⟨⟨2, 0⟩, ⟨2158221067, -30⟩⟩, ⟨⟨2, 0⟩, ⟨2158221067, -30⟩⟩]

/-! ## The real identity -/

/-- **The certificate expression evaluates to `gamma4fgcy`.**

Both sides are unfolded to raw real arithmetic and then normalised:
* the certificate's dyadic/int literals (`IExpr.const ⟨m, e⟩` is `m * 2^e`),
* `pi = 4 * atan 1` (`emit_rpn.py` inlines the named constant `pi`),
* `h0 = 63/50` inside `lmfun`'s branch (the RPN program writes the exact
  rational),
* `acos (1/3)` by its half-angle (the RPN program inlines `sol0`'s `acos`),
* every RPN `ite(c < 0, t, e)` guard `c = lhs - rhs` becomes `lhs < rhs`
  (`sub_lt_zero`), which is exactly `atn2`'s / `lmfun`'s `if` condition,
* the trailing `- 0` of the `>`-encoded program (`orig_op: ">"`) is
  `sub_zero`.

The result is literal term equality (`rfl` closes it). -/
theorem tsk_eval (ρ : Fin 6 → ℝ) :
    Kepler.Interval.Cases.TskXLLIPLSExpr.evalReal ρ =
      gamma4fgcy (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) lmfun := by
  have hacos : Real.arccos (1 / 3) =
      2 * Real.arctan (Real.sqrt (1 - (1 / 3) * (1 / 3)) / (1 + 1 / 3)) :=
    tsk_acos (1 / 3) (by norm_num) (by norm_num)
  unfold gamma4fgcy volY vol4f volXf solY dihY dihXf atn2 mm1 mm2 tau0 sol0
  unfold deltaX deltaX4
  dsimp only [Kepler.Interval.Cases.TskXLLIPLSExpr,
    Kepler.Interval.IExpr.evalReal, Kepler.Interval.transReal]
  simp only [Kepler.Interval.Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite]

/-! ## Box membership -/

/-- `2846274827/2^30 ≤ 2*hplus` (the certificate box's lower corner is the
dyadic floor of `2*hplus = 2.6508`). -/
theorem tsk_lo_hplus :
    ((2846274827 : ℝ) / 1073741824) ≤ 2 * hplus := by
  unfold hplus; norm_num

/-- `sqrt 8 ≤ 759250125/2^28` (dyadic ceiling of `sqrt 8`). -/
theorem tsk_hi_sqrt8 :
    Real.sqrt 8 ≤ (759250125 : ℝ) / 268435456 := by
  have hr : (0 : ℝ) < 759250125 / 268435456 := by norm_num
  rw [← Real.sqrt_sq hr.le]
  apply Real.sqrt_le_sqrt
  norm_num

/-- `2.01 ≤ 2158221067/2^30` (dyadic ceiling). -/
theorem tsk_hi_201 : (2.01 : ℝ) ≤ (2158221067 : ℝ) / 1073741824 := by
  norm_num

/-- `2.8 ≤ 751619277/2^28` (dyadic ceiling). -/
theorem tsk_hi_28 : (2.8 : ℝ) ≤ (751619277 : ℝ) / 268435456 := by
  norm_num

/-- The bank-box hypotheses place the point in the certificate box. -/
theorem tsk_mem (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1l : 2 * hplus ≤ y1) (h1h : y1 ≤ Real.sqrt 8)
    (h2l : 2 ≤ y2) (h2h : y2 ≤ 2.01)
    (h3l : 2 ≤ y3) (h3h : y3 ≤ 2.01)
    (h4l : 2 * hplus ≤ y4) (h4h : y4 ≤ 2.8)
    (h5l : 2 ≤ y5) (h5h : y5 ≤ 2.01)
    (h6l : 2 ≤ y6) (h6h : y6 ≤ 2.01) :
    boxMem tskCertBox ![y1, y2, y3, y4, y5, y6] := by
  intro i
  fin_cases i <;>
    simp only [tskCertBox, Kepler.Interval.DInterval.mem,
      Kepler.Interval.Dyadic.toReal_def, hplus, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Fin.isValue, Int.cast_ofNat, Nat.cast_ofNat,
      zpow_zero, pow_two, Nat.reducePow] <;>
    constructor <;> norm_num <;>
    linarith [tsk_lo_hplus, tsk_hi_sqrt8, tsk_hi_201, tsk_hi_28]

/-! ## Conditional closer -/

/-- **TSKAJXY-XLLIPLS closed, modulo the hull certificate's positivity
lemma.**

`hpos` is exactly what the schema-v3 hull certificate module proves —
`∀ ρ, boxMem TskXLLIPLSBox ρ → 0 < TskXLLIPLSExpr.evalReal ρ` (the
`HullTreeC.sound` corollary of its 6,512-leaf `checkPosTMHullC` tree); the
closer `Kepler.Text.PackIneqTskXLLIPLSClose` supplies it from
`Kepler.Interval.Cases.TskXLLIPLS._pos`. -/
theorem packIneqTskXLLIPLS_of_hull
    (hpos : ∀ ρ : Fin 6 → ℝ, boxMem tskCertBox ρ →
      0 < Kepler.Interval.Cases.TskXLLIPLSExpr.evalReal ρ) :
    bank_TSKAJXYXLLIPLS := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem := tsk_mem y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h
    h5l h5h h6l h6h
  have hp := hpos ![y1, y2, y3, y4, y5, y6] hmem
  rw [tsk_eval] at hp
  simpa using hp

#print axioms tsk_eval
#print axioms tsk_mem
#print axioms packIneqTskXLLIPLS_of_hull

end Kepler.Text

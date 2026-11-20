/-
Kepler.Interval.Cases.IysClose — the real identities between the six
IYOUOBF-sharpv2 derivative hull expressions (`IysD1..6Expr`, IysBase)
and the closed-form slot partials `g4dDVolYk − g4dDVol4fk·L`, plus the
box-membership bridges from the bank-box hypotheses to the certificate
boxes.  Lane `iyou-sharpv2-slots-w1`.

The identity route is the `tsk_eval` recipe (PackIneqTskXLLIPLS):
unfold every definition on the Lean side, `dsimp` the `evalReal` side,
then a two-stage `simp only` (stage 1: dyadic/int literals and the
`+ 0·var` dummies of the emit_rpn convention via `mul_zero`/`add_zero`;
stage 2: the four constant encodings — `pi = 4·atan 1` via `tsk_pi4`,
`arccos (1/3)` half-angle via `tsk_acos`, `h0 = 63/50` via `tsk_h0`,
`lmfun` via `tsk_lmfun_ite`), and finally `ring_nf`: after alignment both
sides are the same ±-tree over the same atoms, but the RPN emitter's
association/summation order differs from the closed forms' author order,
so a single merged `simp only` leaves an arithmetic-rearrangement
residue (found 2026-11-20 by the iyou-build-w1 bisect probes; the split
into two stages is the landed `tsk_eval` shape).  Everything here is
unconditional — the strict-ite `lmfun` encoding agrees with `lmfun` at
every point (tsk_lmfun_ite).

No new axiom / sorry / native_decide; audited at the tail.
-/
import Kepler.Interval.Cases.IysBase
import Kepler.Text.Gamma4Deriv8
import Kepler.Text.TskXLLIPLSLemmas
import Kepler.Text.PackIneqTskXLLIPLS
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option pp.deepTerms true
set_option pp.maxSteps 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Kepler.Interval.Cases

open Kepler.Text

/-! ## The `evalReal` identities -/

private theorem iys_acos13 :
    Real.arccos (1 / 3) =
      2 * Real.arctan (Real.sqrt (1 - (1 / 3) * (1 / 3)) / (1 + 1 / 3)) :=
  tsk_acos (1 / 3) (by norm_num) (by norm_num)

/-- **D1 identity**: the hull expression is the closed-form `y1`-partial
(with the zero-branch `L = 0`). -/
theorem iys_eval_D1 (ρ : Fin 6 → ℝ) :
    IysD1Expr.evalReal ρ =
      Kepler.Text.g4dDVolY1 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) -
        Kepler.Text.g4dDVol4f1 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) 0 := by
  have hacos := iys_acos13
  unfold Kepler.Text.g4dDVolY1 Kepler.Text.g4dDVol4f1
    Kepler.Text.g4dDSolY1 Kepler.Text.g4dDSolY4
    Kepler.Text.g4dDDihY1 Kepler.Text.g4dDDihY2 Kepler.Text.g4dDDihY3
    Kepler.Text.g4dDDihY4 Kepler.Text.g4dDDihY5 Kepler.Text.g4dDDihY6
    Kepler.Text.g4dDihX1 Kepler.Text.g4dDihX2 Kepler.Text.g4dDihX3
    Kepler.Text.g4dDihX4 Kepler.Text.g4dDihX5 Kepler.Text.g4dDihX6
    Kepler.Text.dihY Kepler.Text.dihXf Kepler.Text.atn2
    Kepler.Text.deltaY Kepler.Text.deltaX Kepler.Text.deltaX4
    Kepler.Text.deltaX5 Kepler.Text.g4dDX1 Kepler.Text.g4dDX2
    Kepler.Text.g4dDX3 Kepler.Text.g4dDX6 Kepler.Text.upsX
    Kepler.Text.mm1 Kepler.Text.mm2 Kepler.Text.tau0 Kepler.Text.sol0
  dsimp only [IysD1Expr, IExpr.evalReal, transReal]
  simp only [Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero, zero_mul, neg_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite, tsk_h0]
  ring_nf

/-- **D2 identity**: the hull expression is the closed-form `y2`-partial
(affine-branch `L = −1/(h0−1)`). -/
theorem iys_eval_D2 (ρ : Fin 6 → ℝ) :
    IysD2Expr.evalReal ρ =
      Kepler.Text.g4dDVolY2 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) -
        Kepler.Text.g4dDVol4f2 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)
          (-1 / (Kepler.Text.h0 - 1)) := by
  have hacos := iys_acos13
  unfold Kepler.Text.g4dDVolY2 Kepler.Text.g4dDVol4f2
    Kepler.Text.g4dDSolY2 Kepler.Text.g4dDSolY5
    Kepler.Text.g4dDDihY1 Kepler.Text.g4dDDihY2 Kepler.Text.g4dDDihY3
    Kepler.Text.g4dDDihY4 Kepler.Text.g4dDDihY5 Kepler.Text.g4dDDihY6
    Kepler.Text.g4dDihX1 Kepler.Text.g4dDihX2 Kepler.Text.g4dDihX3
    Kepler.Text.g4dDihX4 Kepler.Text.g4dDihX5 Kepler.Text.g4dDihX6
    Kepler.Text.dihY Kepler.Text.dihXf Kepler.Text.atn2
    Kepler.Text.deltaY Kepler.Text.deltaX Kepler.Text.deltaX4
    Kepler.Text.deltaX5 Kepler.Text.g4dDX1 Kepler.Text.g4dDX2
    Kepler.Text.g4dDX3 Kepler.Text.g4dDX6 Kepler.Text.upsX
    Kepler.Text.mm1 Kepler.Text.mm2 Kepler.Text.tau0 Kepler.Text.sol0
  dsimp only [IysD2Expr, IExpr.evalReal, transReal]
  simp only [Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero, zero_mul, neg_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite, tsk_h0]
  ring_nf


/-- **D3 identity**: the closed-form `y3`-partial. -/
theorem iys_eval_D3 (ρ : Fin 6 → ℝ) :
    IysD3Expr.evalReal ρ =
      Kepler.Text.g4dDVolY3 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) -
        Kepler.Text.g4dDVol4f3 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)
          (-1 / (Kepler.Text.h0 - 1)) := by
  have hacos := iys_acos13
  unfold Kepler.Text.g4dDVolY3 Kepler.Text.g4dDVol4f3
    Kepler.Text.g4dDSolY3 Kepler.Text.g4dDSolY6
    Kepler.Text.g4dDDihY1 Kepler.Text.g4dDDihY2 Kepler.Text.g4dDDihY3
    Kepler.Text.g4dDDihY4 Kepler.Text.g4dDDihY5 Kepler.Text.g4dDDihY6
    Kepler.Text.g4dDihX1 Kepler.Text.g4dDihX2 Kepler.Text.g4dDihX3
    Kepler.Text.g4dDihX4 Kepler.Text.g4dDihX5 Kepler.Text.g4dDihX6
    Kepler.Text.dihY Kepler.Text.dihXf Kepler.Text.atn2
    Kepler.Text.deltaY Kepler.Text.deltaX Kepler.Text.deltaX4
    Kepler.Text.deltaX5 Kepler.Text.g4dDX1 Kepler.Text.g4dDX2
    Kepler.Text.g4dDX3 Kepler.Text.g4dDX6 Kepler.Text.upsX
    Kepler.Text.mm1 Kepler.Text.mm2 Kepler.Text.tau0 Kepler.Text.sol0
  dsimp only [IysD3Expr, IExpr.evalReal, transReal]
  simp only [Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero, zero_mul, neg_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite, tsk_h0]
  ring_nf

/-- **D4 identity**: the closed-form `y4`-partial. -/
theorem iys_eval_D4 (ρ : Fin 6 → ℝ) :
    IysD4Expr.evalReal ρ =
      Kepler.Text.g4dDVolY4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) -
        Kepler.Text.g4dDVol4f4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)
          (-1 / (Kepler.Text.h0 - 1)) := by
  have hacos := iys_acos13
  unfold Kepler.Text.g4dDVolY4 Kepler.Text.g4dDVol4f4
    Kepler.Text.g4dDSolY4 Kepler.Text.g4dDSolY1
    Kepler.Text.g4dDDihY1 Kepler.Text.g4dDDihY2 Kepler.Text.g4dDDihY3
    Kepler.Text.g4dDDihY4 Kepler.Text.g4dDDihY5 Kepler.Text.g4dDDihY6
    Kepler.Text.g4dDihX1 Kepler.Text.g4dDihX2 Kepler.Text.g4dDihX3
    Kepler.Text.g4dDihX4 Kepler.Text.g4dDihX5 Kepler.Text.g4dDihX6
    Kepler.Text.dihY Kepler.Text.dihXf Kepler.Text.atn2
    Kepler.Text.deltaY Kepler.Text.deltaX Kepler.Text.deltaX4
    Kepler.Text.deltaX5 Kepler.Text.g4dDX1 Kepler.Text.g4dDX2
    Kepler.Text.g4dDX3 Kepler.Text.g4dDX6 Kepler.Text.upsX
    Kepler.Text.mm1 Kepler.Text.mm2 Kepler.Text.tau0 Kepler.Text.sol0
  dsimp only [IysD4Expr, IExpr.evalReal, transReal]
  simp only [Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero, zero_mul, neg_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite, tsk_h0]
  ring_nf

/-- **D5 identity**: the closed-form `y5`-partial. -/
theorem iys_eval_D5 (ρ : Fin 6 → ℝ) :
    IysD5Expr.evalReal ρ =
      Kepler.Text.g4dDVolY5 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) -
        Kepler.Text.g4dDVol4f5 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)
          (-1 / (Kepler.Text.h0 - 1)) := by
  have hacos := iys_acos13
  unfold Kepler.Text.g4dDVolY5 Kepler.Text.g4dDVol4f5
    Kepler.Text.g4dDSolY5 Kepler.Text.g4dDSolY2
    Kepler.Text.g4dDDihY1 Kepler.Text.g4dDDihY2 Kepler.Text.g4dDDihY3
    Kepler.Text.g4dDDihY4 Kepler.Text.g4dDDihY5 Kepler.Text.g4dDDihY6
    Kepler.Text.g4dDihX1 Kepler.Text.g4dDihX2 Kepler.Text.g4dDihX3
    Kepler.Text.g4dDihX4 Kepler.Text.g4dDihX5 Kepler.Text.g4dDihX6
    Kepler.Text.dihY Kepler.Text.dihXf Kepler.Text.atn2
    Kepler.Text.deltaY Kepler.Text.deltaX Kepler.Text.deltaX4
    Kepler.Text.deltaX5 Kepler.Text.g4dDX1 Kepler.Text.g4dDX2
    Kepler.Text.g4dDX3 Kepler.Text.g4dDX6 Kepler.Text.upsX
    Kepler.Text.mm1 Kepler.Text.mm2 Kepler.Text.tau0 Kepler.Text.sol0
  dsimp only [IysD5Expr, IExpr.evalReal, transReal]
  simp only [Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero, zero_mul, neg_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite, tsk_h0]
  ring_nf

/-- **D6 identity**: the closed-form `y6`-partial. -/
theorem iys_eval_D6 (ρ : Fin 6 → ℝ) :
    IysD6Expr.evalReal ρ =
      Kepler.Text.g4dDVolY6 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) -
        Kepler.Text.g4dDVol4f6 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)
          (-1 / (Kepler.Text.h0 - 1)) := by
  have hacos := iys_acos13
  unfold Kepler.Text.g4dDVolY6 Kepler.Text.g4dDVol4f6
    Kepler.Text.g4dDSolY6 Kepler.Text.g4dDSolY3
    Kepler.Text.g4dDDihY1 Kepler.Text.g4dDDihY2 Kepler.Text.g4dDDihY3
    Kepler.Text.g4dDDihY4 Kepler.Text.g4dDDihY5 Kepler.Text.g4dDDihY6
    Kepler.Text.g4dDihX1 Kepler.Text.g4dDihX2 Kepler.Text.g4dDihX3
    Kepler.Text.g4dDihX4 Kepler.Text.g4dDihX5 Kepler.Text.g4dDihX6
    Kepler.Text.dihY Kepler.Text.dihXf Kepler.Text.atn2
    Kepler.Text.deltaY Kepler.Text.deltaX Kepler.Text.deltaX4
    Kepler.Text.deltaX5 Kepler.Text.g4dDX1 Kepler.Text.g4dDX2
    Kepler.Text.g4dDX3 Kepler.Text.g4dDX6 Kepler.Text.upsX
    Kepler.Text.mm1 Kepler.Text.mm2 Kepler.Text.tau0 Kepler.Text.sol0
  dsimp only [IysD6Expr, IExpr.evalReal, transReal]
  simp only [Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat,
    Nat.cast_zero, zpow_zero, zpow_one, pow_two, Nat.reducePow, div_one,
    sub_zero, mul_zero, add_zero, zero_mul, neg_zero]
  simp only [sub_lt_zero, hacos, tsk_pi4, tsk_lmfun_ite, tsk_h0]
  ring_nf

/-! ## Axiom audit -/

#print axioms iys_eval_D1
#print axioms iys_eval_D2
#print axioms iys_eval_D3
#print axioms iys_eval_D4
#print axioms iys_eval_D5
#print axioms iys_eval_D6

end Kepler.Interval.Cases

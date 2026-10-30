/-
  A2QITNPEAGlue — nli rest 9/62 glue (lane A2, landed 2026-10-28).
  Case: HOL ineq `QITNPEA 3725403817` (ineq.hl:1221),
  bank_QITNPEA3725403817 (PackingAuto21.lean:498): dihY y1..y6 < 1.56 on
  [2hminus,2hplus]x[2,2hminus]^3 x[2,2.1] x[2,2hminus]^2.

  Certificate: the in-repo G4 module `Kepler.Interval.Cases.CQITNPEAx3725403817`
  (964,984 leaves / 2,775 shards, prec 64 bb_arb), built in the A2 lane clone
  and olean-backfilled into the main repo (sources md5-identical, 2,777 files).
  This file consumes only Base's three defs (`CQITNPEAx3725403817MkExpr` /
  `Expr` / `Box`); the top module's `CQITNPEAx3725403817_pos` is the named
  premise slot of `nliRestQITNPEA3725403817_slot`, filled at the Assembly
  substitution site (one-line application).

  Numerical sanity (lane A2-W1, Python): the emitted Expr evaluated with
  `IExpr.evalReal` semantics equals `39/25 - dihY(y1..y6)` exactly
  (400 interior + 64 corner box points, max abs diff 0.0; component checks
  A = deltaX4(x), sqrt-arg = 4*x1*deltaX(x) exact).

  No placeholder bodies anywhere in this file: every lemma is fully proved.
-/
import Kepler.Interval.Cases.CQITNPEAx3725403817.Base
import Kepler.Text.PackingAuto21

namespace A2Rest9W1

open Kepler.Interval Kepler.Text

/-! ## 1. Bridge: the emitted `ite` tree is exactly `atn2 S (-A)`

The certificate expression's branch structure (emitted by emit_lean.py from
the case prog) is, over `evalReal`:
  if |(-A)| - S < 0 then arctan((-A)/S)
  else if 0 - (-A) < 0 then (4*arctan 1)/2 - arctan(S/(-A))
  else if (-A) - 0 < 0 then -((4*arctan 1)/2) - arctan(S/(-A))
  else 4*arctan 1
which is branch-for-branch the Lean `atn2 x y = if |y| < x then arctan (y/x)
else if 0 < y then pi/2 - arctan (x/y) else if y < 0 then -pi/2 - arctan (x/y)
else pi` (SphereKit.lean:37) at `x := S`, `y := -A`, plus
`4 * arctan 1 = pi`. -/

private theorem iteTree_eq_atn2 (A S : ℝ) :
    (if |(-A)| - S < 0 then Real.arctan ((-A) / S)
      else if 0 - (-A) < 0 then 4 * Real.arctan 1 / 2 - Real.arctan (S / (-A))
      else if (-A) - 0 < 0 then -(4 * Real.arctan 1 / 2) - Real.arctan (S / (-A))
      else 4 * Real.arctan 1)
      = atn2 S (-A) := by
  have hpi : (4 : ℝ) * Real.arctan 1 = Real.pi := by rw [Real.arctan_one]; ring
  unfold atn2
  split
  · rename_i h1
    have h1' : |(-A)| < S := by simpa using h1
    rw [if_pos h1']
  · rename_i h1
    have h1' : ¬ |(-A)| < S := by simpa using h1
    rw [if_neg h1']
    split
    · rename_i h2
      have h2' : 0 < -A := by simpa using h2
      rw [if_pos h2', hpi]
    · rename_i h2
      have h2' : ¬ 0 < -A := by simpa using h2
      rw [if_neg h2']
      split
      · rename_i h3
        have h3' : (-A) < 0 := by simpa using h3
        rw [if_pos h3', hpi]
      · rename_i h3
        have h3' : ¬ (-A) < 0 := by simpa using h3
        rw [if_neg h3', hpi]

/-! ## 2. evalReal identity: certificate expression = 39/25 - dihY -/

private theorem evalReal_eq_dihY (ρ : Fin 7 → ℝ) :
    (Kepler.Interval.Cases.CQITNPEAx3725403817Expr).evalReal ρ
      = 39 / 25 - dihY (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) (ρ 6) := by
  have hpi : (4 : ℝ) * Real.arctan 1 = Real.pi := by rw [Real.arctan_one]; ring
  dsimp only [Kepler.Interval.Cases.CQITNPEAx3725403817Expr,
    Kepler.Interval.Cases.CQITNPEAx3725403817MkExpr,
    Kepler.Interval.IExpr.evalReal, Kepler.Interval.transReal]
  simp only [Kepler.Interval.Dyadic.toReal_int, Int.cast_ofNat, Int.cast_one,
    Int.cast_zero]
  rw [iteTree_eq_atn2]
  unfold dihY dihXf deltaX deltaX4
  simp only [hpi]

/-! ## 3. Endpoint embedding + final shape with the named premise slot

Box of the certificate (dim0 is the `hminus` slot, unused by the prog):
  dim0 hminus-slot ∈ [322122547·2^-28, 348966093·2^-28]  (∋ hminus, mi_hminus_prop)
  dim1 y1          ∈ [2576980377·2^-30, 711568707·2^-28]  (=[2hminus,2hplus] outward)
  dim2..6 y_i      ∈ [2, 2hminus] ⊆ [2, 2.6000000006] / dim4 ⊆ [2, 2.1000000006]
-/

theorem nliRestQITNPEA3725403817_slot
    (QITNPEA3725403817_pos : ∀ ρ : Fin 7 → ℝ,
      Kepler.Interval.boxMem Kepler.Interval.Cases.CQITNPEAx3725403817Box ρ →
        0 < (Kepler.Interval.Cases.CQITNPEAx3725403817Expr).evalReal ρ) :
    bank_QITNPEA3725403817 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : Kepler.Interval.boxMem Kepler.Interval.Cases.CQITNPEAx3725403817Box
      ![hminus, y1, y2, y3, y4, y5, y6] := by
    intro i
    fin_cases i
    · show (⟨⟨322122547, -28⟩, ⟨348966093, -28⟩⟩ : Kepler.Interval.DInterval).mem hminus
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [mi_hminus_prop.1]
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [mi_hminus_prop.2.1]
    · show (⟨⟨2576980377, -30⟩, ⟨711568707, -28⟩⟩ : Kepler.Interval.DInterval).mem y1
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [mi_hminus_prop.1]
      · rw [Kepler.Interval.Dyadic.toReal_def]
        norm_num [hplus] at h1h ⊢
        linarith
    · show (⟨⟨2, 0⟩, ⟨2791728743, -30⟩⟩ : Kepler.Interval.DInterval).mem y2
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        exact h2l
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [h2h, mi_hminus_prop.2.1]
    · show (⟨⟨2, 0⟩, ⟨2791728743, -30⟩⟩ : Kepler.Interval.DInterval).mem y3
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        exact h3l
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [h3h, mi_hminus_prop.2.1]
    · show (⟨⟨2, 0⟩, ⟨2254857831, -30⟩⟩ : Kepler.Interval.DInterval).mem y4
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        exact h4l
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [h4h]
    · show (⟨⟨2, 0⟩, ⟨2791728743, -30⟩⟩ : Kepler.Interval.DInterval).mem y5
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        exact h5l
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [h5h, mi_hminus_prop.2.1]
    · show (⟨⟨2, 0⟩, ⟨2791728743, -30⟩⟩ : Kepler.Interval.DInterval).mem y6
      constructor
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        exact h6l
      · rw [Kepler.Interval.Dyadic.toReal_def]; norm_num
        linarith [h6h, mi_hminus_prop.2.1]
  have hpos := QITNPEA3725403817_pos ![hminus, y1, y2, y3, y4, y5, y6] hmem
  rw [evalReal_eq_dihY] at hpos
  have hkey : dihY y1 y2 y3 y4 y5 y6 < (39 : ℝ) / 25 := by simpa using hpos
  have hconv : (39 : ℝ) / 25 = 1.56 := by norm_num
  rwa [hconv] at hkey

#print axioms iteTree_eq_atn2
#print axioms evalReal_eq_dihY
#print axioms nliRestQITNPEA3725403817_slot

end A2Rest9W1

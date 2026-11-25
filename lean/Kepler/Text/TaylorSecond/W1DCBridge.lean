/-
Kepler.Text.TaylorSecond.W1DCBridge — lane `wt1-glue-bridge-w1` (2026-11-25).

Bridges the **landed** zero-mode DC tree of `W1DC15873` (`d806ff72`,
`Top_pos : ∀ x ∈ D, 0 < fTop x`) to the generic `W1aFJet` layer.

Contents

  §1 the slot chain `W1DC15873.f… = f…`: **24 of the 25 failing slots are
     pure `rfl`**; the single non-definitional leaf is
     `W1DC15873.fCN2 = fun x => ((-2 : ℤ) : ℝ)` vs `fCN2 = fun _ => (-2 : ℝ)`
     (`Int.cast` of a *negative* numeral does not reduce in the kernel to the
     `Neg`-of-`OfNat` form, while the positive casts `fC2/fC4/fC8` do).
     `rfl` on the top therefore fails; the 25-lemma chain below replaces it
     and costs ≈ 0 s over the baseline import;
  §2 **Bridge A (function level)**: `fTop = w1F3Z`;
  §3 the **exact** decomposition on `D` (no hypothesis on `x 0`):
     `w1F3 x = fTop x + fK2 x * (fLf4 x * h0cut (x 0) * fDihC x)`
     — the `pq1` term is *alive* on the sub-sliver `x 0 < 2 h0`;
  §4 `D`'s coordinate bounds `0 ≤ x0, 0 < x1, 0 ≤ x2`;
  §5 **Bridge A (zero mode, on `D`)**: `2 h0 ≤ x 0 → w1F3 x = fTop x`;
  §6 the **mode-split bridge on `D`**:
     `w1F3 x = if 2 h0 ≤ x 0 then fTop x else w1F3O x`;
  §7 the **honest correction of the lane spec**: `I4.lo * 2^-200 = 2.52 −
     0.52·2^-200 < 2 h0 = 2.52`, so `D` contains points below the kink and the
     *unconditional* statement `∀ x ∈ D, w1F3 x = fTop x` is **false**; the
     formal witness `exists_D_lt_2h0` below machine-checks the gap.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.

## PER-BOX BRIDGE TEMPLATE (copy verbatim into every leaf module)

The bridge is **box-independent**: one compiled copy of this module serves all
221 boxes, so the per-box cost is one lemma application, not a proof.

    -- zero-mode leaf (`l4 >= 2 * h0`, the box's own DC tree was emitted on
    -- `W1aFJet.w1F3Z` / `W1aFJet.JTopR`, as in `W1DC15873`):
    theorem Top_pos_w1F3 {x : Fin 3 → ℝ} (hx : x ∈ D) (hcut : 2 * h0 ≤ x 0) :
        0 < w1F3 x :=
      w1F3_pos_of_ge hx hcut          -- = Top_pos + fTop_eq_w1F3Z + §5

    -- one-mode leaf (`u4 <= 2 * h0`, tree emitted on `W1aFJet.w1F3O`):
    theorem Top_pos_w1F3 {x : Fin 3 → ℝ} (hx : x ∈ D) (hcut : x 0 ≤ 2 * h0) :
        0 < w1F3 x := by
      obtain ⟨h4, h5, h6⟩ := D_bounds hx
      rw [w1F3_eq_w1F3O x h4 h5 h6 hcut]
      exact Top_pos_w1F3O x hx        -- the box's own DC T2 terminal on `w1F3O`

    -- straddling leaf (`l4 < 2 * h0 < u4`, e.g. box `15873`, §7): split the
    -- box at `2 * h0` in the tiling, or discharge the inequality route
    -- `fTop <= w1F3` (`0 < k2`, `0 <= lfun` below the kink, `0 <= fDihC` on D).

Both `Top_pos` (zero mode) and the one-mode `Top_pos_w1F3O` are the *only*
box-specific inputs; the two `rw`/`exact` lines above are the whole glue.
-/
import Kepler.Text.TaylorSecond.W1DC15873
import Kepler.Text.TaylorSecond.W1aFJet

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond

noncomputable section

open Kepler.Text
open Kepler.NliBanks21

/-! ## 1. The slot chain `W1DC15873.f… = f…` -/

/-- The one non-definitional leaf: `((-2 : ℤ) : ℝ)` vs `(-2 : ℝ)`. -/
theorem dc_fCN2 : W1DC15873.fCN2 = fCN2 := by
  funext x
  simp only [W1DC15873.fCN2, fCN2]
  norm_num

theorem dc_fDlt : W1DC15873.fDlt = fDlt := by
  funext x
  simp only [W1DC15873.fDlt, W1DC15873.fDltA, W1DC15873.fCN2S2, W1DC15873.fC4S1,
    W1DC15873.fX4X5X6, W1DC15873.fX4X5, fDlt, dc_fCN2]
  rfl

theorem dc_fTA : W1DC15873.fTA = fTA := by
  funext x
  simp only [W1DC15873.fTA, fTA, dc_fDlt]
  rfl
theorem dc_fTB : W1DC15873.fTB = fTB := by
  funext x
  simp only [W1DC15873.fTB, fTB, dc_fDlt]
  rfl
theorem dc_fTC : W1DC15873.fTC = fTC := by
  funext x
  simp only [W1DC15873.fTC, fTC, dc_fDlt]
  rfl

theorem dc_fGA : W1DC15873.fGA = fGA := by
  funext x
  simp only [W1DC15873.fGA, W1DC15873.fKDltA, fGA, dc_fDlt]
  rfl
theorem dc_fGB : W1DC15873.fGB = fGB := by
  funext x
  simp only [W1DC15873.fGB, W1DC15873.fKDltB, fGB, dc_fDlt]
  rfl
theorem dc_fGC : W1DC15873.fGC = fGC := by
  funext x
  simp only [W1DC15873.fGC, W1DC15873.fKDltC, fGC, dc_fDlt]
  rfl

theorem dc_fMtA : W1DC15873.fMtA = fMtA := by
  funext x
  simp only [W1DC15873.fMtA, fMtA, dc_fTA]
theorem dc_fMtB : W1DC15873.fMtB = fMtB := by
  funext x
  simp only [W1DC15873.fMtB, fMtB, dc_fTB]
theorem dc_fMtC : W1DC15873.fMtC = fMtC := by
  funext x
  simp only [W1DC15873.fMtC, fMtC, dc_fTC]

theorem dc_fMgA : W1DC15873.fMgA = fMgA := by
  funext x
  simp only [W1DC15873.fMgA, fMgA, dc_fGA]
theorem dc_fMgB : W1DC15873.fMgB = fMgB := by
  funext x
  simp only [W1DC15873.fMgB, fMgB, dc_fGB]
theorem dc_fMgC : W1DC15873.fMgC = fMgC := by
  funext x
  simp only [W1DC15873.fMgC, fMgC, dc_fGC]

theorem dc_fDihA : W1DC15873.fDihA = fDihA := by
  funext x
  simp only [W1DC15873.fDihA, fDihA, dc_fMgA]
  rfl
theorem dc_fDihB : W1DC15873.fDihB = fDihB := by
  funext x
  simp only [W1DC15873.fDihB, fDihB, dc_fMgB]
  rfl
theorem dc_fDihC : W1DC15873.fDihC = fDihC := by
  funext x
  simp only [W1DC15873.fDihC, fDihC, dc_fMgC]
  rfl

theorem dc_fSeA : W1DC15873.fSeA = fSeA := by
  funext x
  simp only [W1DC15873.fSeA, fSeA, dc_fMtA]
  rfl
theorem dc_fSeB : W1DC15873.fSeB = fSeB := by
  funext x
  simp only [W1DC15873.fSeB, fSeB, dc_fMtB]
  rfl
theorem dc_fSeC : W1DC15873.fSeC = fSeC := by
  funext x
  simp only [W1DC15873.fSeC, fSeC, dc_fMtC]
  rfl

theorem dc_fSe : W1DC15873.fSe = fSe := by
  funext x
  simp only [W1DC15873.fSe, W1DC15873.fSe1, fSe, dc_fSeA, dc_fSeB, dc_fSeC]

theorem dc_fFirst : W1DC15873.fFirst = fFirst := by
  funext x
  simp only [W1DC15873.fFirst, W1DC15873.fK1Se, fFirst, dc_fSe]
  rfl

theorem dc_fPos : W1DC15873.fPos = fPos := by
  funext x
  simp only [W1DC15873.fPos, W1DC15873.fPosA, W1DC15873.fLf5DihA, W1DC15873.fLf6DihB,
    fPos, dc_fDihA, dc_fDihB]
  rfl

theorem dc_fNeg2 : W1DC15873.fNeg2 = fNeg2 := by
  funext x
  simp only [W1DC15873.fNeg2, fNeg2, dc_fDihC]
  rfl

/-! ## 2. Bridge A at function level -/

/-- **`fTop = w1F3Z`**: the landed DC tree function of `W1DC15873` *is* the
generic tree function of `W1aFJet` (the only obstruction is the negative
numeral cast in `fCN2`, §1). -/
theorem fTop_eq_w1F3Z : W1DC15873.fTop = w1F3Z := by
  funext x
  simp only [W1DC15873.fTop, W1DC15873.fFirstPos, w1F3Z, dc_fFirst, dc_fPos, dc_fNeg2]

/-! ## 3. The exact `pq1` decomposition (every `x`, no cut hypothesis) -/

/-- **Exact decomposition**: `w1aF` differs from the zero-mode tree function by
*exactly* the `pq1` term `fK2 * (fLf4 * h0cut (x 0) * fDihC)`.  No hypothesis on
`x 0`: this is the statement that stays true on the sliver `x 0 < 2 h0`, where
the two sides genuinely differ. -/
theorem w1F3_eq_fTop_add (x : Fin 3 → ℝ)
    (h4 : 0 ≤ x 0) (h5 : 0 < x 1) (h6 : 0 ≤ x 2) :
    w1F3 x = W1DC15873.fTop x + fK2 x * (fLf4 x * h0cut (x 0) * fDihC x) := by
  rw [fTop_eq_w1F3Z]
  unfold w1F3
  rw [w1aF, nb21_w1aG_explicit (x 0) (x 1) (x 2) h4 h5.le h6, nb21_w1aD_explicit]
  rw [w1_seA_unfold (x 0) (x 1) (x 2) h4 h5.le,
    w1_seB_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_seC_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_dihA_unfold (x 0) (x 1) (x 2) h5.le,
    w1_dihB_unfold (x 0) (x 1) (x 2) h6,
    w1_dihC_unfold (x 0) (x 1) (x 2) h4]
  simp only [w1F3Z, fFirst, fPos, fNeg2, fSe, fSeA, fSeB, fSeC, fDihA, fDihB, fDihC,
    fMtA, fMtB, fMtC, fMgA, fMgB, fMgC, fK1_eq x, fK2_eq x, fLf4_eq x, fLf5_eq x,
    fLf6_eq x, fTA_eq x, fTB_eq x, fTC_eq x, fGA_eq x, fGB_eq x, fGC_eq x, fWA_eq x,
    fWB_eq x, fWC_eq x, fC112, fC008, fIA, fIB, fIC, fA_eq x, fB_eq x, fC_eq x]
  ring

/-! ## 4. The box bounds read off `D` -/

/-- `D`'s lower edge, as a literal. -/
theorem D_x0_ge {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D) :
    ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) ≤ x 0 := by
  have h := hx.1.1
  simpa only [W1DC15873.D, DCKit.DC.mem, W1DC15873.I4] using h

/-- `D`'s middle edge, as a literal. -/
theorem D_x1_ge {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D) :
    ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) ≤ x 1 := by
  have h := hx.2.1.1
  simpa only [W1DC15873.D, DCKit.DC.mem, W1DC15873.I5] using h

/-- `D`'s upper edge, as a literal. -/
theorem D_x2_ge {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D) :
    ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) ≤ x 2 := by
  have h := hx.2.2.1
  simpa only [W1DC15873.D, DCKit.DC.mem, W1DC15873.I6] using h

/-- Positivity/nonnegativity of the three coordinates on `D` (the side
conditions of `w1F3_eq_w1F3Z` / `w1F3_eq_w1F3O`). -/
theorem D_bounds {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D) :
    0 ≤ x 0 ∧ 0 < x 1 ∧ 0 ≤ x 2 := by
  have h0 := D_x0_ge hx
  have h1 := D_x1_ge hx
  have h2 := D_x2_ge hx
  have p0 : (0 : ℝ) ≤ ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) := by positivity
  have p1 : (0 : ℝ) < ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) := by positivity
  have p2 : (0 : ℝ) ≤ ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) := by positivity
  exact ⟨le_trans p0 h0, lt_of_lt_of_le p1 h1, le_trans p2 h2⟩

/-! ## 5. Bridge A on the box, zero mode -/

/-- **Bridge A (zero mode)**: on `D`, above the kink, the original kernel
`w1aF` equals the landed DC tree function `fTop`. -/
theorem w1F3_eq_fTop_of_ge {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D)
    (hcut : 2 * h0 ≤ x 0) : w1F3 x = W1DC15873.fTop x := by
  obtain ⟨h4, h5, h6⟩ := D_bounds hx
  rw [w1F3_eq_w1F3Z x h4 h5 h6 hcut, fTop_eq_w1F3Z]

/-- **The zero-mode terminal the assembly uses**: the landed `Top_pos`
(`0 < fTop` on `D`) transported to the original wt1 kernel `w1aF`, on the part
of `D` above the kink.  This is the whole per-box bridge step. -/
theorem w1F3_pos_of_ge {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D)
    (hcut : 2 * h0 ≤ x 0) : 0 < w1F3 x := by
  rw [w1F3_eq_fTop_of_ge hx hcut]
  exact W1DC15873.Top_pos x hx

/-! ## 6. The mode-split bridge on the box -/

/-- **Mode-split bridge**: on `D`, each point is in exactly one of the two
modes, and in each mode the original kernel equals the corresponding tree
function — `fTop` (zero mode) above the kink, `w1F3O` (one mode) at/below it.
This is the statement the 221-box assembly should use: box `15873` straddles
the kink (§7), so neither single-mode form covers it. -/
theorem w1F3_eq_fTop_ite {x : Fin 3 → ℝ} (hx : x ∈ W1DC15873.D) :
    w1F3 x = if 2 * h0 ≤ x 0 then W1DC15873.fTop x else w1F3O x := by
  obtain ⟨h4, h5, h6⟩ := D_bounds hx
  by_cases h : 2 * h0 ≤ x 0
  · rw [if_pos h]
    exact w1F3_eq_w1F3Z x h4 h5 h6 h ▸ (fTop_eq_w1F3Z ▸ rfl)
  · rw [if_neg h]
    exact w1F3_eq_w1F3O x h4 h5 h6 (le_of_lt (lt_of_not_ge h))

/-! ## 7. The kink gap: the unconditional `∀ x ∈ D, w1F3 x = fTop x` is false

`I4.lo * 2^-200 = 2.52 − 0.52·2^-200` (the leaf's lower edge is the outward
rounding of `2 h0 = 2.52`), so the box `D` is **not** contained in the
`h0cut = 0` region; it contains a 0.52-grid-unit sliver below the kink where
`h0cut = 1` and the `pq1` term of §3 is alive.  Consequence for `M8`: box
`15873` must be **split at `2 h0`** (lower part → one-mode tree `w1F3O`,
upper part → zero-mode tree `fTop`), or the two-mode `ite` bridge of §6 must
be combined with the tree bound on the *whole* box. -/

/-- The lower edge of `I4` is strictly below `2 h0 = 2.52`. -/
theorem I4lo_lt_two_h0 :
    ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) < 2 * h0 := by
  norm_num [Kepler.Text.h0]

/-- The upper edge of `I4` is strictly above `2 h0 = 2.52`. -/
theorem two_h0_lt_I4hi :
    2 * h0 < ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) *
      (2 : ℝ) ^ (-(200 : ℤ)) := by
  norm_num [Kepler.Text.h0]

/-- **Witness**: `D` has a point strictly below the kink. -/
theorem exists_D_lt_2h0 : ∃ x ∈ W1DC15873.D, x 0 < 2 * h0 := by
  let p0 : ℝ := ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) *
    (2 : ℝ) ^ (-(200 : ℤ))
  let p1 : ℝ := ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) *
    (2 : ℝ) ^ (-(200 : ℤ))
  let p2 : ℝ := ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) *
    (2 : ℝ) ^ (-(200 : ℤ))
  have hs : (0 : ℝ) < (2 : ℝ) ^ (-(200 : ℤ)) := by positivity
  have hm0 : W1DC15873.I4.mem p0 := by
    refine ⟨le_refl p0, ?_⟩
    have h : ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) ≤
        ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) := by
      norm_num
    exact mul_le_mul_of_nonneg_right h hs.le
  have hm1 : W1DC15873.I5.mem p1 := by
    refine ⟨le_refl p1, ?_⟩
    have h : ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) ≤
        ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) := by
      norm_num
    exact mul_le_mul_of_nonneg_right h hs.le
  have hm2 : W1DC15873.I6.mem p2 := by
    refine ⟨le_refl p2, ?_⟩
    have h : ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) ≤
        ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) := by
      norm_num
    exact mul_le_mul_of_nonneg_right h hs.le
  refine ⟨![p0, p1, p2], ⟨?_, ?_, ?_⟩, ?_⟩
  · show W1DC15873.I4.mem (![p0, p1, p2] 0)
    simpa using hm0
  · show W1DC15873.I5.mem (![p0, p1, p2] 1)
    simpa using hm1
  · show W1DC15873.I6.mem (![p0, p1, p2] 2)
    simpa using hm2
  · simpa only [p0, Matrix.cons_val_zero] using I4lo_lt_two_h0

/-! ## 8. Audit -/

#print axioms dc_fCN2
#print axioms dc_fDlt
#print axioms dc_fTA
#print axioms dc_fGA
#print axioms dc_fMtA
#print axioms dc_fMgA
#print axioms dc_fDihA
#print axioms dc_fSeA
#print axioms dc_fSe
#print axioms dc_fFirst
#print axioms dc_fPos
#print axioms dc_fNeg2
#print axioms fTop_eq_w1F3Z
#print axioms w1F3_eq_fTop_add
#print axioms D_bounds
#print axioms w1F3_eq_fTop_of_ge
#print axioms w1F3_pos_of_ge
#print axioms w1F3_eq_fTop_ite
#print axioms I4lo_lt_two_h0
#print axioms two_h0_lt_I4hi
#print axioms exists_D_lt_2h0

end

end Kepler.Text.TaylorSecond

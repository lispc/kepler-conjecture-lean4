/-
  549 acceleration — range-composition straddle verdict (the err-semantics ×2
  root fix, pilot lane).

  Root cause (十二更): the df-hull straddle composite (`iteHullTM2`) anchors at
  the *true center value* `f(y)`, so its `err` must pay
  `max err_b + jumpBound(fB_t, fB_e)` — the jump term is the full fB distance,
  i.e. 2× the C-side stored-anchor half-width — and stacked nested composites
  multiply it.  99/99真 df-hull 双支 straddle leaves NEG with needed
  contraction factors 0.049–0.453.

  This module does NOT change the `Valid` semantics.  It observes that:

  * `TaylorM.Valid` puts every box value `f(ρ)` inside the model's
    *value range* `[fB.lo − W, fB.hi + W]` (`Valid.valueRange_mem` below —
    the two-liner extracted from `valid_iteHull`'s `hIn` helper), and
  * at an `ite` node the guard selects one branch at each point, so the ite's
    pointwise values lie in the **hull of the two branch value ranges** —
    zero jump term, zero err doubling, and the guard needs no decision.

  `evalRangeHull` therefore composes RANGES: base operators recurse (plain
  interval arithmetic above/between `ite` nodes — exactly the hybrid
  fallback's mechanism), while every `ite` node contributes the hull of its
  branches' TM value ranges (the branches themselves evaluated by the
  existing `evalTMHullD2`, so decided sub-guards keep their single-branch
  tightness and all TM/sqrt/div/trans certificates are consumed in the very
  same order — the production `TMParams` work verbatim).  A straddling `ite`
  at any depth now contributes exactly its true value hull instead of a
  fat-err Taylor model.

  `checkPosRange` is the resulting leaf checker and `checkPosRange_sound`
  its soundness: a PASS (`final range lo > 0`) forces `0 < e.evalReal ρ` on
  the whole box.  Parameter/certificate compatibility with `evalTMHullD2`
  (guard-first sqrt queue; `DInterval.div`/`transOn` consume nothing) means
  per-leaf certificates generated for the HullD2 route revalidate as-is.
-/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

/-! ## The pointwise value-range lemma (the insight, 2 lines) -/

namespace TaylorM

/-- **Value-range containment**: a valid model's `valueRange` contains `f ρ`
at every box point.  `f(y) ∈ fB` plus the amplitude bound
`|f(ρ) − f(y)| ≤ W` (`Valid.abs_sub_le_W`) — this is the `hIn` helper of
`valid_iteHull`, extracted.  Zero jump term, zero err doubling. -/
theorem Valid.valueRange_mem {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) {ρ : Fin n → ℝ}
    (hρ : boxMem box ρ) : M.valueRange.mem (f ρ) := by
  have hV0 := hV
  obtain ⟨_, _, hfB, hrem⟩ := hV
  obtain ⟨a, ha, hbound⟩ := hrem ρ hρ
  have hW := TaylorM.Valid.abs_sub_le_W hV0 hρ ha hbound
  rw [abs_le] at hW
  constructor
  · show Dyadic.toReal (M.fB.lo.add (-M.W)) ≤ f ρ
    rw [Dyadic.toReal_add, Dyadic.toReal_neg]
    linarith [hfB.1, hW.1]
  · show f ρ ≤ Dyadic.toReal (M.fB.hi.add M.W)
    rw [Dyadic.toReal_add]
    linarith [hfB.2, hW.2]

end TaylorM

/-! ## The range-composition evaluator -/

/-- **Range-composition evaluation** (new; no existing evaluator touched).
Every successful evaluation returns an interval `R` with

    ∀ ρ ∈ box, e.evalReal ρ ∈ R

(see `evalRangeHull_mem`).  Recursion structure:

* non-`ite` nodes: plain `DInterval` arithmetic on the children's ranges
  (`const`/`var`/`neg`/`abs`/`add`/`sub`/`mul`/`div`/`sqrt`/`trans` — the
  certified hybrid-fallback mechanism; `div`/`sqrt` consume **no**
  reciprocal certificates and `sqrt` clamps a negative lower radicand end to
  `0`, both exactly as `evalIParams`);
* `ite` nodes: the certified guard interval decides
  (`C.hi.isNeg` → then / `C.lo.isNN` → else, the C-side `take_then`), and
  the selected branch is evaluated by the existing `evalTMHullD2` — its
  `valueRange` is the tight branch range (`Valid.valueRange_mem`);
  a guard-straddling node contributes the **hull of the two branch value
  ranges** — no composite model, no jump term in any `err`, the guard never
  enters any decision (a failing *branch* still fails the node, as on the
  C side).

Certificate layout is a sub-queue of the `evalTMHullD2` layout: the guard
`sqrt` mantissas are consumed guard-first at each `ite` and the branch
evaluations consume in branch AST order; `DInterval.div`/`transOn` here
consume nothing where `evalTMHullD2`'s TM arms consume one reciprocal
certificate.  With the all-uniform production granularities the HullD2
per-leaf `TMParams` revalidate verbatim. -/
def evalRangeHull {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (DInterval × TMParams)
  | .const d, ps => some (⟨d, d⟩, ps)
  | .var k, ps => some (box k, ps)
  | .neg e, ps => (evalRangeHull box e ps).map fun (R, ps') => (R.neg, ps')
  | .abs e, ps => (evalRangeHull box e ps).map fun (R, ps') => (R.abs, ps')
  | .add e₁ e₂, ps =>
      (evalRangeHull box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHull box e₂ ps₁).map fun (R₂, ps₂) => (R₁.add R₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalRangeHull box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHull box e₂ ps₁).map fun (R₂, ps₂) => (R₁.sub R₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalRangeHull box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHull box e₂ ps₁).map fun (R₂, ps₂) => (R₁.mul R₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalRangeHull box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHull box e₂ ps₁).bind fun (R₂, ps₂) =>
      (DInterval.div R₁ R₂ out).map fun R => (R, ps₂)
  | .sqrt e _ _, ps =>
      (evalRangeHull box e ps).bind fun (R, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun t =>
      if R.hi.isNeg then none
      else
        (Dyadic.sqrtI R.hi t.shi).bind fun Jh =>
        (if R.lo.isNN then (Dyadic.sqrtI R.lo t.slo).map fun Jl => Jl.lo
          else some (⟨0, 0⟩ : Dyadic)).map fun L =>
          (⟨L, Jh.hi⟩, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩)
  | .trans k e N out, ps =>
      (evalRangeHull box e ps).bind fun (R, ps₀) =>
      (transOn k R N out).map fun J => (J, ps₀)
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then
        (evalTMHullD2 box t ps₀).map fun (M, ps') => (M.valueRange, ps')
      else if C.lo.isNN then
        (evalTMHullD2 box e ps₀).map fun (M, ps') => (M.valueRange, ps')
      else
        (evalTMHullD2 box t ps₀).bind fun (Mt, ps₁) =>
        (evalTMHullD2 box e ps₁).map fun (Me, ps₂) =>
          ((Mt.valueRange).hull Me.valueRange, ps₂)

/-- **Soundness invariant of `evalRangeHull`**: every successful evaluation
returns an interval containing the real value at every box point.  The
non-`ite` cases repeat `evalIParams_mem`'s interval arguments, and the `ite`
case transports `evalTMHullD2_sound`'s branch validity through
`TaylorM.Valid.valueRange_mem` (decided guard) or the branch-range hull
(straddle) — no jump term anywhere. -/
theorem evalRangeHull_mem {n : ℕ} {box : Fin n → DInterval} {ρ : Fin n → ℝ}
    (hwf : ∀ i, (box i).wf = true) (hρ : boxMem box ρ) :
    ∀ (e : IExpr n) (ps ps' : TMParams) (R : DInterval),
      evalRangeHull box e ps = some (R, ps') → R.mem (e.evalReal ρ) := by
  intro e
  induction e with
  | const d =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨le_rfl, le_rfl⟩
  | var k =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact hρ k
  | neg e ih =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_neg (ih ps ps₀ J he)
  | abs e ih =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_abs (ih ps ps₀ J he)
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨R₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨R₂, ps₂⟩, h₂, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_add (ih₁ ps ps₁ R₁ h₁) (ih₂ ps₁ ps₂ R₂ h₂)
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨R₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨R₂, ps₂⟩, h₂, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_sub (ih₁ ps ps₁ R₁ h₁) (ih₂ ps₁ ps₂ R₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨R₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨R₂, ps₂⟩, h₂, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.mem_mul (ih₁ ps ps₁ R₁ h₁) (ih₂ ps₁ ps₂ R₂ h₂)
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨R₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨R₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨K, hK, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact DInterval.div_sound hK (ih₁ ps ps₁ R₁ h₁) (ih₂ ps₁ ps₂ R₂ h₂)
  | sqrt e _ _ ih =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, h⟩ := h
      dsimp only at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      by_cases hneg : J.hi.isNeg = true
      · rw [if_pos hneg] at h; simp at h
      · rw [if_neg hneg] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨Jh, hh, h⟩ := h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨L, hl, hI⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
        obtain ⟨hy1, hy2⟩ := ih ps ps₀ J he
        have hhi0 : ¬ (J.hi.toReal < 0) := fun hlt0 =>
          hneg ((Dyadic.isNeg_iff J.hi).mpr hlt0)
        obtain ⟨_, hh2⟩ := Dyadic.sqrtI_sound hh
        have hJh0 : 0 ≤ Jh.hi.toReal :=
          le_trans (Real.sqrt_nonneg _) hh2
        constructor
        · show L.toReal ≤ Real.sqrt (e.evalReal ρ)
          by_cases hnn : J.lo.isNN = true
          · rw [if_pos hnn, Option.map_eq_some_iff] at hl
            obtain ⟨Jl, hJl, hL⟩ := hl
            subst hL
            obtain ⟨hl1, _⟩ := Dyadic.sqrtI_sound hJl
            exact le_trans hl1 (Real.sqrt_le_sqrt hy1)
          · rw [if_neg hnn] at hl
            obtain rfl : L = ⟨0, 0⟩ := (Option.some.inj hl).symm
            rw [Dyadic.toReal_zero]
            by_cases hx : e.evalReal ρ < 0
            · have hs : Real.sqrt (e.evalReal ρ) = 0 :=
                Real.sqrt_eq_zero_of_nonpos (by linarith)
              linarith
            · exact Real.sqrt_nonneg _
        · show Real.sqrt (e.evalReal ρ) ≤ Jh.hi.toReal
          by_cases hx : e.evalReal ρ < 0
          · have hs : Real.sqrt (e.evalReal ρ) = 0 :=
              Real.sqrt_eq_zero_of_nonpos (by linarith)
            linarith
          · exact le_trans (Real.sqrt_le_sqrt (by linarith)) hh2
  | trans k e N out ih =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨J, ps₀⟩, he, h⟩ := h
      dsimp only at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨K, hK, hI⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
      exact IExpr.transOn_sound k (ih ps ps₀ J he) hK
  | ite c t e _ihc _iht _ihe =>
      intro ps ps' R h
      simp only [evalRangeHull] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, ps₀⟩, hc, h⟩ := h
      dsimp only at h
      have hC := evalIParams_mem hρ c ps ps₀ C hc
      by_cases hneg : C.hi.isNeg = true
      · rw [if_pos hneg] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨M, ps₁⟩, hm, hI⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
        have hlt : c.evalReal ρ < 0 :=
          lt_of_le_of_lt hC.2 ((Dyadic.isNeg_iff C.hi).mp hneg)
        have hV := (evalTMHullD2_sound t ps₀ ps₁ M hwf hm).1
        show M.valueRange.mem
          (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
        rw [if_pos hlt]
        exact TaylorM.Valid.valueRange_mem hV hρ
      · rw [if_neg hneg] at h
        by_cases hnn : C.lo.isNN = true
        · rw [if_pos hnn] at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨M, ps₁⟩, hm, hI⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
          have hge : 0 ≤ c.evalReal ρ :=
            le_trans ((Dyadic.isNN_iff C.lo).mp hnn) hC.1
          have hnot : ¬ c.evalReal ρ < 0 := not_lt.mpr hge
          have hV := (evalTMHullD2_sound e ps₀ ps₁ M hwf hm).1
          show M.valueRange.mem
            (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
          rw [if_neg hnot]
          exact TaylorM.Valid.valueRange_mem hV hρ
        · rw [if_neg hnn] at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨Mt, ps₁⟩, ht, h⟩ := h
          dsimp only at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨Me, ps₂⟩, he', hI⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hI
          have hVt := (evalTMHullD2_sound t ps₀ ps₁ Mt hwf ht).1
          have hVe := (evalTMHullD2_sound e ps₁ ps₂ Me hwf he').1
          show ((Mt.valueRange).hull Me.valueRange).mem
            (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
          by_cases hlt : c.evalReal ρ < 0
          · rw [if_pos hlt]
            exact DInterval.mem_hull_left (TaylorM.Valid.valueRange_mem hVt hρ)
          · rw [if_neg hlt]
            exact DInterval.mem_hull_right (TaylorM.Valid.valueRange_mem hVe hρ)

/-! ## The range-composition leaf checker -/

/-- The range-composition positivity checker (same shape as
`checkPosTMHull`): box well-formedness, successful range evaluation, and a
strictly positive final range lower bound.  This is the 549 straddle-lane
entry replacing the df-hull composite check: the straddling `ite` now
contributes its true branch-range hull, so the `err` ×2 semantics
(`jumpBound`-in-`W`) never enters the verdict chain. -/
def checkPosRange {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalRangeHull box e ps with
    | some (R, _) => R.lo.isPos
    | none => false)

/-- **Soundness of the range-composition checker** (same conclusion as
`checkPosTMHull_sound`): a PASS forces strict positivity at every real
assignment pointwise inside the box. -/
theorem checkPosRange_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {ps : TMParams}
    (h : checkPosRange e box ps = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal ρ := by
  unfold checkPosRange at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hwfB, h⟩ := h
  have hwf : ∀ i, (box i).wf = true := fun i => hwfB i (List.mem_finRange i)
  cases hE : evalRangeHull box e ps with
  | none => rw [hE] at h; simp at h
  | some Rp =>
    obtain ⟨R, ps'⟩ := Rp
    rw [hE] at h
    have hpos := Dyadic.toReal_pos_of_isPos h
    have hmem := evalRangeHull_mem hwf hρ e ps ps' R hE
    exact lt_of_lt_of_le hpos hmem.1

/-! ### Smoke tests: straddle pass, decided-guard pass -/

/-- The `exIteHullChk` miniature: straddling guard `x − 9/4`, branches
`2x` / `x + 2`, box `[2, 5/2]`. -/
def exRangeStraddleE : IExpr 1 :=
  .ite (.sub (.var 0) (.const ⟨9, -2⟩)) (.mul (.var 0) (.const ⟨2, 0⟩))
    (.add (.var 0) (.const ⟨2, 0⟩))

/-- Box `[2, 5/2]`. -/
def exRangeStraddleBox : Fin 1 → DInterval := fun _ => ⟨⟨2, 0⟩, ⟨5, -1⟩⟩

/-- The range checker closes the straddling miniature. -/
theorem exIteHullChk_checkPosRange :
    checkPosRange exRangeStraddleE exRangeStraddleBox TMParams.empty = true := by
  decide

/-- `ite(x, −x, x)` (pointwise `|x|`) on box `[-3, -5/2]`: the guard
interval is strictly negative, so the decided-then arm runs and the `−x`
branch value range is positive — the range checker closes it. -/
def exRangeAbsE : IExpr 1 := .ite (.var 0) (.neg (.var 0)) (.var 0)

def exRangeAbsBox : Fin 1 → DInterval := fun _ => ⟨⟨-3, 0⟩, ⟨-5, -1⟩⟩

theorem exIteAbs_checkPosRange :
    checkPosRange exRangeAbsE exRangeAbsBox TMParams.empty = true := by
  decide

#print axioms TaylorM.Valid.valueRange_mem
#print axioms evalRangeHull_mem
#print axioms checkPosRange_sound
#print axioms exIteHullChk_checkPosRange
#print axioms exIteAbs_checkPosRange

end Kepler.Interval.Cases

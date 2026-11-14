/-
  Div2/loa: the certified-magnitude division rule of the Taylor-model checker
  (`--tm-div2` channel 1, opt-in).

  C-side counterpart: `pipeline/interval/bb_arb.c` `tm_div2_salvage`
  (`:1228-1305`).  A TM node's own model range `[fB.lo − W, fB.hi + W]` can
  straddle zero even when the true denominator `g` is sign-definite on the
  box: the linear envelope `W = Σᵢ|dfBᵢ|·wᵢ + err` fattens along deep chains.
  The C side therefore tracks a *separate* certified magnitude lower bound
  `loa ≤ |g(x)|` on each TM slot, injected exactly where a rule's own success
  condition already certifies it:

  * `sqrt`: `loa := √c` with `c = fB.lo − W > 0` of the radicand model — the
    sqrt rule's success condition itself (`bb_arb.c:2075-2085`);
  * `abs`: the sign-definite value-range endpoint (`:1995-2030`);
  * `push_var`/`push_const`: the box/constant endpoint (`:1535-1555`);
  * `neg` preserves it; an `ite` hull takes the min of the two branch bounds;
  * all other arithmetic ops and `trans` reset it to `0` (conservative).

  Consumption (`tm_div2_salvage`): `M := 1/loa` dominates `1/|g|` on the box,
  so the reciprocal rule runs unchanged with `M` in place of the value-range
  lower bound.  In Lean that is exactly `TaylorM.invCore c p` with `c := loa`:
  `valid_invCore` accepts an *arbitrary* certified lower bound
  `c.toReal ≤ |g ρ|` with `0 < c.toReal` and produces a valid model of `1/g`,
  so the (I1)-(I4) argument is unchanged.

  This module is opt-in: `evalTMHullD3C` / `checkPosTMHullD` are new
  definitions; `evalTMHullD2C` / `checkPosTMHullC` (and every existing
  certificate) are untouched and byte-identical.

  `loa` sources in the Lean evaluator (one `Dyadic` per node, `0` = none):
  * `const`/`var`: `DInterval.loaLower` of the point cell / box cell;
  * `sqrt`: `Jc.lo` where `Jc = sqrtRel c p.sc`, `c = fB.lo − W` of the
    argument model (the certificate `p.sc` the sqrt rule already consumes);
  * `abs`: `DInterval.loaLower` of the sub-model's `valueRange`;
  * `neg`: unchanged; `ite` single branch: unchanged; `ite` hull:
    `Dyadic.dmin` of the two branch bounds;
  * fallback arms (`div`/`sqrt`/`abs`/`trans`): `DInterval.loaLower` of the
    plain interval enclosure `I` (`I.mem x → I.loaLower ≤ |x|`);
  * `add`/`sub`/`mul`/`div` results and `trans` results: `0`.

  The `evalTMHullFill2D` mirror below is the compiled-run twin used to
  produce per-leaf `TMParams.sqrtCerts` (mantissa triples in traversal
  order), exactly as `evalTMHullFill2C` does for the C checker.
-/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval

namespace DInterval

/-- Certified magnitude lower bound of a range: the distance of the
sign-definite endpoint to zero, else `0`.  For `x ∈ I`, `loaLower I ≤ |x|`
(`loaLower_le_abs`).  Lean counterpart of the C-side `mag_lower(·)`
injections at `push_var`/`push_const`/`abs` (`bb_arb.c:1535-1555`,
`:1995-2030`). -/
def loaLower (I : DInterval) : Dyadic :=
  if I.lo.isNN then I.lo else if I.hi.isNeg then -I.hi else ⟨0, 0⟩

/-- **Soundness of `loaLower`**: any point of the range has magnitude at
least `loaLower`. -/
theorem loaLower_le_abs {I : DInterval} {x : ℝ} (h : I.mem x) :
    I.loaLower.toReal ≤ |x| := by
  unfold DInterval.loaLower
  by_cases h1 : I.lo.isNN = true
  · rw [if_pos h1]
    have hl : 0 ≤ I.lo.toReal := (Dyadic.isNN_iff I.lo).mp h1
    rw [abs_of_nonneg (le_trans hl h.1)]
    exact h.1
  · rw [if_neg h1]
    by_cases h2 : I.hi.isNeg = true
    · rw [if_pos h2]
      have hh : I.hi.toReal < 0 := (Dyadic.isNeg_iff I.hi).mp h2
      rw [Dyadic.toReal_neg, abs_of_neg (lt_of_le_of_lt h.2 hh)]
      linarith [h.2]
    · rw [if_neg h2]
      show (⟨0, 0⟩ : Dyadic).toReal ≤ |x|
      rw [Dyadic.toReal_zero]
      exact abs_nonneg x

end DInterval

/-- `l` lower-bounds `|f|` on the box — the `loa` contract carried by the
div2 evaluator (`l = 0` is always valid). -/
def LowerAbs {n : ℕ} (box : Fin n → DInterval) (l : Dyadic)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ρ, boxMem box ρ → l.toReal ≤ |f ρ|

/-- Transport of the `loa` contract along pointwise equality on the box. -/
theorem LowerAbs.congr {n : ℕ} {box : Fin n → DInterval} {l : Dyadic}
    {f g : (Fin n → ℝ) → ℝ} (h : LowerAbs box l f)
    (hEq : ∀ ρ, boxMem box ρ → g ρ = f ρ) : LowerAbs box l g :=
  fun ρ hρ => by rw [hEq ρ hρ]; exact h ρ hρ

namespace TaylorM

/-- `TaylorM.sqrt` plus the certified magnitude lower bound of its result:
`Jc.lo` with `Jc = sqrtRel (fB.lo − W) p.sc`, the very certificate the sqrt
rule's success gate consumes.  Since `c = fB.lo − W ≤ f ρ` on the box and
`0 < c`, monotonicity of `√` gives `Jc.lo ≤ √c ≤ √(f ρ) = |√(f ρ)|`.  The
model component is `M.sqrt p` verbatim (`valid_sqrt` applies unchanged). -/
def sqrtL {n : ℕ} (M : TaylorM n) (p : SqrtTMP) : Option (TaylorM n × Dyadic) :=
  (M.sqrt p).bind fun M' =>
    (Dyadic.sqrtRel (M.fB.lo.add (-M.W)) p.sc).map fun Jc => (M', Jc.lo)

end TaylorM

/-- **Validity and `loa` contract of `sqrtL`**. -/
theorem valid_sqrtL {n : ℕ} {M : TaylorM n} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} (hV : M.Valid box f) {p : SqrtTMP}
    {M' : TaylorM n} {l : Dyadic} (h : M.sqrtL p = some (M', l)) :
    M'.Valid box (fun ρ => Real.sqrt (f ρ)) ∧
      LowerAbs box l (fun ρ => Real.sqrt (f ρ)) ∧ M'.y = M.y ∧ M'.w = M.w := by
  unfold TaylorM.sqrtL at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨M₀, hs, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨Jc, hJc, hpair⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
  obtain ⟨hV', hyy, hww⟩ := valid_sqrt hV p hs
  -- the sqrt success gate: `c := fB.lo − W` is certified positive
  have hc : (M.fB.lo.add (-M.W)).isPos = true := by
    unfold TaylorM.sqrt at hs
    by_cases hh : (M.fB.lo.add (-M.W)).isPos = true
    · exact hh
    · rw [if_neg hh] at hs
      exact absurd hs (by simp)
  have hc0 : 0 < (M.fB.lo.add (-M.W)).toReal := (Dyadic.isPos_iff _).mp hc
  have hJc1 : Jc.lo.toReal ≤ Real.sqrt (M.fB.lo.add (-M.W)).toReal :=
    (Dyadic.sqrtRel_sound hJc).1
  refine ⟨hV', ?_, hyy, hww⟩
  intro ρ hρ
  have hge : (M.fB.lo.add (-M.W)).toReal ≤ f ρ :=
    (TaylorM.Valid.valueRange_mem hV ρ hρ).1
  have hfρ : 0 < f ρ := lt_of_lt_of_le hc0 hge
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_trans hJc1 (Real.sqrt_le_sqrt hge)

/-- **Validity of the div2 salvage rule**: `f · (1/g)` with the reciprocal's
denominator lower bound `c` supplied directly (the C-side
`tm_div2_salvage` channel: `M := 1/loa`).  Reduces to `valid_invCore` (whose
`c` is an arbitrary certified lower bound of `|g|`) composed with `mul`. -/
theorem valid_div2 {n : ℕ} {box : Fin n → DInterval} {Mf Mg : TaylorM n}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : Mf.Valid box f) (hg : Mg.Valid box g)
    (hy : Mf.y = Mg.y) (hw : Mf.w = Mg.w) {c : Dyadic} (hc0 : 0 < c.toReal)
    (hcle : ∀ ρ, boxMem box ρ → c.toReal ≤ |g ρ|) (p : InvTMP) {Mi : TaylorM n}
    (hi : Mg.invCore c p = some Mi) :
    (Mf.mul Mi).Valid box (fun ρ => f ρ / g ρ) := by
  obtain ⟨hVi, hyi, hwi⟩ := valid_invCore hg p hc0 hcle hi
  have h := valid_mul hf hVi (by rw [hy, hyi]) (by rw [hw, hwi])
  convert h using 2
  rw [div_eq_mul_inv]

/-- **One `div` node of the div2 checker**: try the ordinary value-range
reciprocal (`Mg.inv`), then the certified-magnitude salvage
(`Mg.invCore loa`, the C-side channel 1), then the plain interval fallback
(the D2C behavior — the only arm that can produce a model when the
denominator's *interval* evaluation crosses zero). -/
def divNode {n : ℕ} (box : Fin n → DInterval) (e₁ e₂ : IExpr n) (out : Int)
    (Mf Mg : TaylorM n) (l : Dyadic) (p : InvTMP) :
    Option (TaylorM n × Dyadic) :=
  ((Mg.inv p).map fun Mi => (Mf.mul Mi, (⟨0, 0⟩ : Dyadic))).orElse
    (fun _ =>
      if l.isPos then
        ((Mg.invCore l p).map fun Mi => (Mf.mul Mi, (⟨0, 0⟩ : Dyadic))).orElse
          (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
            (fallbackTM box I, I.loaLower))
      else
        ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, I.loaLower))

/-- **Soundness of `divNode`**: every arm yields a valid model of `e₁/e₂`
and a valid magnitude bound (positive arms: `0`; fallback: the interval's
`loaLower`). -/
theorem divNode_sound {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    {out : Int} {Mf Mg : TaylorM n} {l : Dyadic} {p : InvTMP}
    (hcell : CellOK box)
    (hf : Mf.Valid box (fun ρ => e₁.evalReal ρ))
    (hg : Mg.Valid box (fun ρ => e₂.evalReal ρ))
    (hy : Mf.y = Mg.y) (hw : Mf.w = Mg.w)
    (hl : LowerAbs box l (fun ρ => e₂.evalReal ρ))
    (hym : Mf.y = boxCenter box) (hwm : Mf.w = boxW box)
    {Mi : TaylorM n} {lo : Dyadic}
    (h : divNode box e₁ e₂ out Mf Mg l p = some (Mi, lo)) :
    Mi.Valid box (fun ρ => e₁.evalReal ρ / e₂.evalReal ρ) ∧
      LowerAbs box lo (fun ρ => e₁.evalReal ρ / e₂.evalReal ρ) ∧
      Mi.y = boxCenter box ∧ Mi.w = boxW box := by
  unfold divNode at h
  cases hi : Mg.inv p with
  | some M' =>
      rw [hi] at h
      rw [Option.map_some, Option.orElse_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
      exact ⟨valid_div hf hg hy hw p hi,
        (fun ρ _ => by rw [Dyadic.toReal_zero]; exact abs_nonneg _), hym, hwm⟩
  | none =>
      rw [hi] at h
      rw [Option.map_none, Option.orElse_none] at h
      by_cases hpos : l.isPos = true
      · rw [if_pos hpos] at h
        cases hc : Mg.invCore l p with
        | some M' =>
            rw [hc] at h
            rw [Option.map_some, Option.orElse_some] at h
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj h)
            refine ⟨valid_div2 hf hg hy hw ((Dyadic.isPos_iff l).mp hpos) hl p hc, ?_,
              hym, hwm⟩
            intro ρ _
            rw [Dyadic.toReal_zero]
            exact abs_nonneg _
        | none =>
            rw [hc] at h
            rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
            obtain ⟨I, hI, hfinal⟩ := h
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
            refine ⟨valid_fallback hcell hI, ?_, rfl, rfl⟩
            intro ρ hρ
            exact DInterval.loaLower_le_abs
              (IExpr.eval_mem (IExpr.div e₁ e₂ out) box ρ hρ I hI)
      · rw [if_neg hpos] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfinal
        refine ⟨valid_fallback hcell hI, ?_, rfl, rfl⟩
        intro ρ hρ
        exact DInterval.loaLower_le_abs
          (IExpr.eval_mem (IExpr.div e₁ e₂ out) box ρ hρ I hI)

/-- The div2/loa evaluator: `evalTMHullD2C` plus a certified magnitude lower
bound `loa` per node (see the module header).  `div` nodes retry the
reciprocal as `TaylorM.invCore loa` when the value-range reciprocal fails and
`loa > 0` (`divNode`, the C-side `tm_div2_salvage` channel 1); every other
node's model coincides with `evalTMHullD2C` (the only observable difference
is the extra `loa` component). -/
def evalTMHullD3C {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams → Option (TaylorM n × Dyadic × TMParams)
  | .const d, ps => some (constTM box d, (⟨d, d⟩ : DInterval).loaLower, ps)
  | .var k, ps => some (varTM box k, (box k).loaLower, ps)
  | .neg e, ps =>
      (evalTMHullD3C box e ps).map fun (M, l, ps') => (M.neg, l, ps')
  | .add e₁ e₂, ps =>
      (evalTMHullD3C box e₁ ps).bind fun (M₁, _, ps₁) =>
      (evalTMHullD3C box e₂ ps₁).map fun (M₂, _, ps₂) =>
        (M₁.add M₂, (⟨0, 0⟩ : Dyadic), ps₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullD3C box e₁ ps).bind fun (M₁, _, ps₁) =>
      (evalTMHullD3C box e₂ ps₁).map fun (M₂, _, ps₂) =>
        (M₁.sub M₂, (⟨0, 0⟩ : Dyadic), ps₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullD3C box e₁ ps).bind fun (M₁, _, ps₁) =>
      (evalTMHullD3C box e₂ ps₁).map fun (M₂, _, ps₂) =>
        (M₁.mul M₂, (⟨0, 0⟩ : Dyadic), ps₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullD3C box e₁ ps).bind fun (M₁, _, ps₁) =>
      (evalTMHullD3C box e₂ ps₁).bind fun (M₂, l₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      (divNode box e₁ e₂ out M₁ M₂ l₂ p).map fun (M', l') =>
        (M', l', ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩)
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullD3C box e ps).bind fun (M₀, _, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((M₀.sqrtL p).map fun (M', l') =>
          (M', l', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩)).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, I.loaLower,
            ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩))
  | .abs e, ps =>
      ((evalTMHullD3C box e ps).bind fun (M₀, _, ps₀) =>
        if M₀.valueRange.lo.isNN then
          some (M₀, (M₀.valueRange).loaLower, ps₀)
        else if M₀.valueRange.hi.isNeg then
          some (M₀.neg, (M₀.valueRange).loaLower, ps₀)
        else ((IExpr.abs e).eval box).map fun I =>
          (fallbackTM box I, I.loaLower, ps₀)).orElse
        (fun _ => ((IExpr.abs e).eval box).map fun I =>
          (fallbackTM box I, I.loaLower, ps))
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I =>
          (closedTM box I, I.loaLower, ps)
      else
        (evalTMHullD3C box e ps).bind fun (M₀, _, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', (⟨0, 0⟩ : Dyadic),
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I, I.loaLower,
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩))
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then evalTMHullD3C box t ps₀
      else if C.lo.isNN then evalTMHullD3C box e ps₀
      else
        (evalTMHullD3C box t ps₀).bind fun (Mt, lt, ps₁) =>
        (evalTMHullD3C box e ps₁).map fun (Me, le, ps₂) =>
          (iteHullTM2 Mt Me, Dyadic.dmin lt le, ps₂)

/-- **Soundness of `evalTMHullD3C`**: a successful evaluation produces a
valid model of the real semantics (centered at the box midpoint with the
midpoint envelope) *and* a certified magnitude lower bound of the same
function over the box. -/
theorem evalTMHullD3C_sound {n : ℕ} {box : Fin n → DInterval} :
    ∀ (e : IExpr n) (ps ps' : TMParams) (M : TaylorM n) (l : Dyadic),
      (∀ i, (box i).wf = true) →
      evalTMHullD3C box e ps = some (M, l, ps') →
      M.Valid box (fun ρ => e.evalReal ρ) ∧
        LowerAbs box l (fun ρ => e.evalReal ρ) ∧
        M.y = boxCenter box ∧ M.w = boxW box := by
  intro e
  induction e with
  | const d =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
      refine ⟨valid_const (cellOK_of_wf hwf) d, ?_, rfl, rfl⟩
      intro ρ _
      exact DInterval.loaLower_le_abs (I := (⟨d, d⟩ : DInterval)) ⟨le_rfl, le_rfl⟩
  | var k =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
      refine ⟨valid_var (cellOK_of_wf hwf) k, ?_, rfl, rfl⟩
      intro ρ hρ
      exact DInterval.loaLower_le_abs (hρ k)
  | neg e ih =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₀, l₀, ps₀⟩, he, hfinal⟩ := h
      obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
      obtain ⟨hV, hL, hy, hw⟩ := ih ps ps₀ M₀ l₀ hwf he
      refine ⟨valid_neg hV, ?_, hy, hw⟩
      intro ρ hρ
      show l₀.toReal ≤ |-(e.evalReal ρ)|
      rw [abs_neg]
      exact hL ρ hρ
  | add e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, l₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, l₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
      obtain ⟨hV₁, _, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ l₁ hwf h₁
      obtain ⟨hV₂, _, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ l₂ hwf h₂
      refine ⟨valid_add hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]), ?_, hy₁, hw₁⟩
      intro ρ _
      rw [Dyadic.toReal_zero]
      exact abs_nonneg _
  | sub e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, l₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, l₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
      obtain ⟨hV₁, _, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ l₁ hwf h₁
      obtain ⟨hV₂, _, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ l₂ hwf h₂
      refine ⟨valid_sub hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]), ?_, hy₁, hw₁⟩
      intro ρ _
      rw [Dyadic.toReal_zero]
      exact abs_nonneg _
  | mul e₁ e₂ ih₁ ih₂ =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, l₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M₂, l₂, ps₂⟩, h₂, hfinal⟩ := h
      obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
      obtain ⟨hV₁, _, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ l₁ hwf h₁
      obtain ⟨hV₂, _, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ l₂ hwf h₂
      refine ⟨valid_mul hV₁ hV₂ (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]), ?_, hy₁, hw₁⟩
      intro ρ _
      rw [Dyadic.toReal_zero]
      exact abs_nonneg _
  | div e₁ e₂ out ih₁ ih₂ =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₁, l₁, ps₁⟩, h₁, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₂, l₂, ps₂⟩, h₂, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨M', l'⟩, hdiv, hfinal⟩ := h
      obtain ⟨hM, hpair⟩ := Prod.ext_iff.mp hfinal
      obtain ⟨hl, _hps⟩ := Prod.ext_iff.mp hpair
      have hM' : M' = M := hM
      have hl' : l' = l := hl
      obtain ⟨hV₁, _, hy₁, hw₁⟩ := ih₁ ps ps₁ M₁ l₁ hwf h₁
      obtain ⟨hV₂, hL₂, hy₂, hw₂⟩ := ih₂ ps₁ ps₂ M₂ l₂ hwf h₂
      obtain ⟨hMi, hLi, hyi, hwi⟩ := divNode_sound (cellOK_of_wf hwf) hV₁ hV₂
        (by rw [hy₁, hy₂]) (by rw [hw₁, hw₂]) hL₂ hy₁ hw₁ hdiv
      rw [← hM', ← hl']
      exact ⟨hMi, hLi, hyi, hwi⟩
  | sqrt e s₁ s₂ ih =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨M₀, l₀, ps₀⟩, he, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _hp, h⟩ := h
      obtain ⟨hV, hL, hy, hw⟩ := ih ps ps₀ M₀ l₀ hwf he
      cases hs : M₀.sqrtL p with
      | none =>
          rw [hs] at h
          rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
          obtain ⟨I, hI, hfinal⟩ := h
          obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
          refine ⟨valid_fallback (cellOK_of_wf hwf) hI, ?_, rfl, rfl⟩
          intro ρ hρ
          exact DInterval.loaLower_le_abs
            (IExpr.eval_mem (IExpr.sqrt e s₁ s₂) box ρ hρ I hI)
      | some Ml =>
          obtain ⟨M', l'⟩ := Ml
          rw [hs] at h
          rw [Option.map_some, Option.orElse_some] at h
          obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
          obtain ⟨hV', hL', hy', hw'⟩ := valid_sqrtL hV hs
          exact ⟨hV', hL', hy'.trans hy, hw'.trans hw⟩
  | abs e ih =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      cases he : evalTMHullD3C box e ps with
      | none =>
          simp only [he, Option.bind_none, Option.orElse_none,
            Option.map_eq_some_iff] at h
          obtain ⟨I, hI, hfinal⟩ := h
          obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
          refine ⟨valid_fallback (cellOK_of_wf hwf) hI, ?_, rfl, rfl⟩
          intro ρ hρ
          exact DInterval.loaLower_le_abs
            (IExpr.eval_mem (IExpr.abs e) box ρ hρ I hI)
      | some Mp =>
          obtain ⟨M₀, l₀, ps₀⟩ := Mp
          simp only [he, Option.bind_some] at h
          obtain ⟨hV, hL, hy, hw⟩ := ih ps ps₀ M₀ l₀ hwf he
          by_cases hnn : M₀.valueRange.lo.isNN = true
          · simp only [if_pos hnn, Option.orElse_some] at h
            obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
            have hge : 0 ≤ M₀.valueRange.lo.toReal := (Dyadic.isNN_iff _).mp hnn
            refine ⟨hV.congr_box ?_, ?_, hy, hw⟩
            · intro ρ hρ
              show |e.evalReal ρ| = e.evalReal ρ
              exact abs_of_nonneg
                (le_trans hge (TaylorM.Valid.valueRange_mem hV ρ hρ).1)
            · intro ρ hρ
              show (M₀.valueRange).loaLower.toReal ≤ |(IExpr.abs e).evalReal ρ|
              rw [show (IExpr.abs e).evalReal ρ = |e.evalReal ρ| from rfl,
                abs_of_nonneg (abs_nonneg _)]
              exact DInterval.loaLower_le_abs (TaylorM.Valid.valueRange_mem hV ρ hρ)
          · simp only [if_neg hnn] at h
            by_cases hneg : M₀.valueRange.hi.isNeg = true
            · simp only [if_pos hneg, Option.orElse_some] at h
              obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
              obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
              have hlt : M₀.valueRange.hi.toReal < 0 := (Dyadic.isNeg_iff _).mp hneg
              refine ⟨(valid_neg hV).congr_box ?_, ?_, hy, hw⟩
              · intro ρ hρ
                show |e.evalReal ρ| = -e.evalReal ρ
                exact abs_of_neg
                  (lt_of_le_of_lt (TaylorM.Valid.valueRange_mem hV ρ hρ).2 hlt)
              · intro ρ hρ
                show (M₀.valueRange).loaLower.toReal ≤ |(IExpr.abs e).evalReal ρ|
                rw [show (IExpr.abs e).evalReal ρ = |e.evalReal ρ| from rfl,
                  abs_of_nonneg (abs_nonneg _)]
                exact DInterval.loaLower_le_abs (TaylorM.Valid.valueRange_mem hV ρ hρ)
            · simp only [if_neg hneg] at h
              cases hI : (IExpr.abs e).eval box with
              | none => simp [hI] at h
              | some I =>
                  simp only [hI, Option.map_some, Option.orElse_some] at h
                  obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
                  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
                  refine ⟨valid_fallback (cellOK_of_wf hwf) hI, ?_, rfl, rfl⟩
                  intro ρ hρ
                  exact DInterval.loaLower_le_abs
                    (IExpr.eval_mem (IExpr.abs e) box ρ hρ I hI)
  | trans k e N out ih =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      by_cases hcl : e.isClosed = true
      · rw [if_pos hcl] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨I, hI, hfinal⟩ := h
        obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
        refine ⟨valid_closed (cellOK_of_wf hwf) hcl hI, ?_, rfl, rfl⟩
        intro ρ hρ
        exact DInterval.loaLower_le_abs
          (IExpr.eval_mem (IExpr.trans k e N out) box ρ hρ I hI)
      · rw [if_neg hcl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨⟨M₀, l₀, ps₀⟩, he, h⟩ := h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨p, _hp, h⟩ := h
        obtain ⟨hV, hL, hy, hw⟩ := ih ps ps₀ M₀ l₀ hwf he
        cases ht : M₀.trans k N out p with
        | none =>
            rw [ht] at h
            rw [Option.map_none, Option.orElse_none, Option.map_eq_some_iff] at h
            obtain ⟨I, hI, hfinal⟩ := h
            obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
            refine ⟨valid_fallback (cellOK_of_wf hwf) hI, ?_, rfl, rfl⟩
            intro ρ hρ
            exact DInterval.loaLower_le_abs
              (IExpr.eval_mem (IExpr.trans k e N out) box ρ hρ I hI)
        | some M' =>
            rw [ht] at h
            rw [Option.map_some, Option.orElse_some] at h
            obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp (Option.some.inj h)
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
            obtain ⟨hV', hyy, hww⟩ := valid_trans hV N out p ht
            refine ⟨hV', ?_, hyy.trans hy, hww.trans hw⟩
            intro ρ _
            rw [Dyadic.toReal_zero]
            exact abs_nonneg _
  | ite c t e _ihc iht ihe =>
      intro ps ps' M l hwf h
      simp only [evalTMHullD3C] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, ps₀⟩, hc, h⟩ := h
      by_cases hneg : C.hi.isNeg = true
      · rw [if_pos hneg] at h
        obtain ⟨hVt, hLt, hyt, hwt⟩ := iht ps₀ ps' M l hwf h
        refine ⟨valid_iteHullD hVt (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc) hneg,
          hLt.congr ?_, hyt, hwt⟩
        intro ρ hρ
        show (IExpr.ite c t e).evalReal ρ = t.evalReal ρ
        show (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ) = t.evalReal ρ
        rw [if_pos (lt_of_le_of_lt (evalIParams_mem hρ c ps ps₀ C hc).2
          ((Dyadic.isNeg_iff C.hi).mp hneg))]
      · rw [if_neg hneg] at h
        by_cases hnn : C.lo.isNN = true
        · rw [if_pos hnn] at h
          obtain ⟨hVe, hLe, hye, hwe⟩ := ihe ps₀ ps' M l hwf h
          refine ⟨valid_iteHullD_else hVe
            (fun ρ hρ => evalIParams_mem hρ c ps ps₀ C hc) hnn, hLe.congr ?_, hye, hwe⟩
          intro ρ hρ
          show (IExpr.ite c t e).evalReal ρ = e.evalReal ρ
          show (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ) = e.evalReal ρ
          rw [if_neg (not_lt.mpr (le_trans ((Dyadic.isNN_iff C.lo).mp hnn)
            (evalIParams_mem hρ c ps ps₀ C hc).1))]
        · rw [if_neg hnn] at h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨Mt, lt, ps₁⟩, ht, h⟩ := h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨Me, le, ps₂⟩, he, hfinal⟩ := h
          obtain ⟨rfl, hpair⟩ := Prod.ext_iff.mp hfinal
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpair
          obtain ⟨hVt, hLt, hyt, hwt⟩ := iht ps₀ ps₁ Mt lt hwf ht
          obtain ⟨hVe, hLe, hye, hwe⟩ := ihe ps₁ ps₂ Me le hwf he
          refine ⟨valid_iteHull2 c hVt hVe (hyt.trans hye.symm)
            (hwt.trans hwe.symm), ?_, hyt, hwt⟩
          intro ρ hρ
          have hd : (Dyadic.dmin lt le).toReal = min lt.toReal le.toReal :=
            Dyadic.toReal_dmin lt le
          rw [hd]
          show min lt.toReal le.toReal ≤ |(IExpr.ite c t e).evalReal ρ|
          by_cases hlt : c.evalReal ρ < 0
          · rw [show (IExpr.ite c t e).evalReal ρ = t.evalReal ρ from by
              show (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
                = t.evalReal ρ
              rw [if_pos hlt]]
            exact le_trans (min_le_left _ _) (hLt ρ hρ)
          · rw [show (IExpr.ite c t e).evalReal ρ = e.evalReal ρ from by
              show (if c.evalReal ρ < 0 then t.evalReal ρ else e.evalReal ρ)
                = e.evalReal ρ
              rw [if_neg hlt]]
            exact le_trans (min_le_right _ _) (hLe ρ hρ)

/-- The div2 positivity checker (opt-in; same shape as `checkPosTMHullC`):
box well-formedness, successful div2/loa evaluation, and a strictly positive
Taylor lower bound. -/
def checkPosTMHullD {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) : Bool :=
  (List.finRange n).all (fun i => (box i).wf) &&
    (match evalTMHullD3C box e ps with
    | some (M, _, _) => (M.loBound box).isPos
    | none => false)

/-- **Soundness of the div2 checker** (`evalTMHullD3C_sound` + the Taylor
lower bound lemma, the same composition as `checkPosTMHullC_sound`). -/
theorem checkPosTMHullD_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {ps : TMParams}
    (h : checkPosTMHullD e box ps = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal ρ := by
  unfold checkPosTMHullD at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hwfB, h⟩ := h
  have hwf : ∀ i, (box i).wf = true := fun i => hwfB i (List.mem_finRange i)
  cases hE : evalTMHullD3C box e ps with
  | none => rw [hE] at h; simp at h
  | some Mp =>
      obtain ⟨M, l, ps'⟩ := Mp
      rw [hE] at h
      have hpos := Dyadic.toReal_pos_of_isPos h
      obtain ⟨hV, _, _, _⟩ := evalTMHullD3C_sound e ps ps' M l hwf hE
      exact lt_of_lt_of_le hpos (M.loBound_sound hV hρ)

/-! ## Compiled-run mirror (certificate production only, no proof role)

`evalTMHullFill2D` is the div2 twin of `evalTMHullFill2C`: same control flow
and same `TMParams` threading, except that sqrt mantissas are *computed*
(`sqrtMantissaRel`) and reported as triples in traversal order, and `div`
nodes use the div2 salvage (`divNode`).  It additionally counts the salvage
events (`Nat` component) so a probe can prove that the div2 channel fired.
-/

/-- Tracing mirror of `evalTMHullD3C` (compiled runs only: `Nat.sqrt` does
not kernel-reduce). -/
def evalTMHullFill2D {n : ℕ} (box : Fin n → DInterval) :
    IExpr n → TMParams →
      Option (TaylorM n × Dyadic × TMParams × List (Int × Int × Int) × Nat)
  | .const d, ps => some (constTM box d, (⟨d, d⟩ : DInterval).loaLower, ps, [], 0)
  | .var k, ps => some (varTM box k, (box k).loaLower, ps, [], 0)
  | .neg e, ps =>
      (evalTMHullFill2D box e ps).map fun (M, l, ps', tr, s) =>
        (M.neg, l, ps', tr, s)
  | .add e₁ e₂, ps =>
      (evalTMHullFill2D box e₁ ps).bind fun (M₁, _, ps₁, t₁, s₁) =>
      (evalTMHullFill2D box e₂ ps₁).map fun (M₂, _, ps₂, t₂, s₂) =>
        (M₁.add M₂, (⟨0, 0⟩ : Dyadic), ps₂, t₁ ++ t₂, s₁ + s₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullFill2D box e₁ ps).bind fun (M₁, _, ps₁, t₁, s₁) =>
      (evalTMHullFill2D box e₂ ps₁).map fun (M₂, _, ps₂, t₂, s₂) =>
        (M₁.sub M₂, (⟨0, 0⟩ : Dyadic), ps₂, t₁ ++ t₂, s₁ + s₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullFill2D box e₁ ps).bind fun (M₁, _, ps₁, t₁, s₁) =>
      (evalTMHullFill2D box e₂ ps₁).map fun (M₂, _, ps₂, t₂, s₂) =>
        (M₁.mul M₂, (⟨0, 0⟩ : Dyadic), ps₂, t₁ ++ t₂, s₁ + s₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullFill2D box e₁ ps).bind fun (M₁, _, ps₁, t₁, s₁) =>
      (evalTMHullFill2D box e₂ ps₁).bind fun (M₂, l₂, ps₂, t₂, s₂) =>
      ps₂.invCerts.head?.bind fun p =>
      let tps : TMParams := ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩
      ((M₂.inv p).map fun Mi => (M₁.mul Mi, (⟨0, 0⟩ : Dyadic), tps,
          t₁ ++ t₂, s₁ + s₂)).orElse
        (fun _ =>
          if l₂.isPos then
            ((M₂.invCore l₂ p).map fun Mi => (M₁.mul Mi, (⟨0, 0⟩ : Dyadic), tps,
                t₁ ++ t₂, s₁ + s₂ + 1)).orElse
              (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
                (fallbackTM box I, I.loaLower, tps, t₁ ++ t₂, s₁ + s₂))
          else
            ((IExpr.div e₁ e₂ out).eval box).map fun I =>
              (fallbackTM box I, I.loaLower, tps, t₁ ++ t₂, s₁ + s₂))
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullFill2D box e ps).bind fun (M₀, _, ps₀, tr, s) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((if (M₀.fB.lo.add (-M₀.W)).isPos = true then
          let sl := sqrtMantissaRel M₀.fB.lo
          let sh := sqrtMantissaRel M₀.fB.hi
          let sc := sqrtMantissaRel (M₀.fB.lo.add (-M₀.W))
          match M₀.sqrt ⟨sl, sh, sc, p.o1, p.o2⟩ with
          | none => none
          | some M' =>
              (Dyadic.sqrtRel (M₀.fB.lo.add (-M₀.W)) sc).map fun Jc =>
                (M', Jc.lo, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩,
                  tr ++ [(sl, sh, sc)], s)
        else none).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, I.loaLower,
            ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩, tr, s)))
  | .abs e, ps =>
      ((evalTMHullFill2D box e ps).bind fun (M₀, _, ps₀, tr, s) =>
        if M₀.valueRange.lo.isNN then some (M₀, (M₀.valueRange).loaLower, ps₀, tr, s)
        else if M₀.valueRange.hi.isNeg then
          some (M₀.neg, (M₀.valueRange).loaLower, ps₀, tr, s)
        else ((IExpr.abs e).eval box).map fun I =>
          (fallbackTM box I, I.loaLower, ps₀, tr, s)).orElse
        (fun _ => ((IExpr.abs e).eval box).map fun I =>
          (fallbackTM box I, I.loaLower, ps, [], 0))
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I =>
          (closedTM box I, I.loaLower, ps, [], 0)
      else
        (evalTMHullFill2D box e ps).bind fun (M₀, _, ps₀, tr, s) =>
        ps₀.transCerts.head?.bind fun p =>
        ((M₀.trans k N out p).map fun M' =>
            (M', (⟨0, 0⟩ : Dyadic),
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, tr, s)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I, I.loaLower,
              ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩, tr, s))
  | .ite c t e, ps =>
      (evalIParamsFill box c ps).bind fun (C, ps₀, lg) =>
      if C.hi.isNeg then
        (evalTMHullFill2D box t ps₀).map fun (M, l, ps', tr, s) =>
          (M, l, ps', lg ++ tr, s)
      else if C.lo.isNN then
        (evalTMHullFill2D box e ps₀).map fun (M, l, ps', tr, s) =>
          (M, l, ps', lg ++ tr, s)
      else
        (evalTMHullFill2D box t ps₀).bind fun (Mt, lt, ps₁, t₁, s₁) =>
        (evalTMHullFill2D box e ps₁).map fun (Me, le, ps₂, t₂, s₂) =>
          (iteHullTM2 Mt Me, Dyadic.dmin lt le, ps₂, lg ++ t₁ ++ t₂, s₁ + s₂)

/-- One compiled-run div2 leaf probe: PASS flag, the Taylor lower bound
(mantissa, exponent), the mantissa triples to bake into the kernel-side
`TMParams.sqrtCerts`, and the number of div2 salvage events. -/
def tmHullLeafProbeD {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ps : TMParams) :
    Option (Bool × Int × Int × List (Int × Int × Int) × Nat) :=
  (evalTMHullFill2D box e ps).map fun (M, _, _, tr, s) =>
    let lb := M.loBound box
    (lb.isPos, lb.m, lb.e, tr, s)

/-! ## Smoke tests: the div2 channel fires end-to-end and stays sound -/

/-- A box straddling zero: the div fallback's plain interval evaluation
cannot produce a model, so any `some` from `divNode` must be a TM branch. -/
def exBoxStrad : Fin 1 → DInterval := fun _ => ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩

/-- Hand-made argument model `fB = [16, 16]`, `df = 0`, `err = 15`:
`W = 15`, so the sqrt rule's `c = fB.lo − W = 1 > 0` and the sqrt model's
envelope `W' = err·J + W²·K = 15/8 + 225/8 = 30` dwarfs `fB' = [4, 4]` —
its value range straddles zero, the div2 shape. -/
def exArgM : TaylorM 1 :=
  ⟨fun _ => ⟨0, 0⟩, fun _ => ⟨1, 0⟩, ⟨⟨16, 0⟩, ⟨16, 0⟩⟩,
    fun _ => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨15, 0⟩⟩

/-- Exact root mantissas for the radicands `16` (`slo`/`shi`) and `1` (`sc`):
`⌊√(16·2^160)⌋ = 2^82`, `⌊√(2^160)⌋ = 2^80`. -/
def exSqrtP : SqrtTMP :=
  ⟨4835703278458516698824704, 4835703278458516698824704,
    1208925819614629174706176, -80, -80⟩

theorem exSqrtLM_some : (exArgM.sqrtL exSqrtP).isSome = true := by decide

/-- The sqrt result's certified magnitude lower bound is positive (`√c = 1`). -/
theorem exSqrtLM_loa_pos :
    (exArgM.sqrtL exSqrtP).map (fun r => r.2.isPos) = some true := by decide

/-- ... while its value range straddles zero (`4 − 30 = −26 < 0`), so the
ordinary reciprocal gate must fail. -/
theorem exSqrtLM_straddle :
    (exArgM.sqrtL exSqrtP).map (fun r => r.1.valueRange.lo.isNN) = some false := by
  decide

theorem exSqrtLM_inv_fails :
    (exArgM.sqrtL exSqrtP).map (fun r => (r.1.inv ⟨-80, -80, -80⟩).isSome) = some false := by
  decide

/-- The fallback interval path really fails on the straddling box (so the
`isSome` test below can only be satisfied by a TM arm). -/
theorem exDiv2_fallback_fails :
    (IExpr.div (.const ⟨1, 0⟩) (.var 0) 0).eval exBoxStrad = none := by decide

/-- The div2 channel fires: the fallback interval path fails (the divisor
interval straddles zero) and `inv` fails (the model range straddles), yet
`divNode` returns a model — only `invCore loa` can. -/
theorem exDiv2_fires :
    ((exArgM.sqrtL exSqrtP).bind fun r =>
      divNode exBoxStrad (.const ⟨1, 0⟩) (.var 0) 0 (constTM exBoxStrad ⟨1, 0⟩)
        r.1 r.2 ⟨-80, -80, -80⟩).isSome = true := by decide

/-- **Kernel replay of the div2 channel** (`decide +kernel`): the same
`isSome` claim as `exDiv2_fires`, closed by the kernel evaluator (the
certificate-side reduction is kernel-cheap: literal `2^82`/`2^80` root
mantissas). -/
theorem exDiv2_fires_kernel :
    ((exArgM.sqrtL exSqrtP).bind fun r =>
      divNode exBoxStrad (.const ⟨1, 0⟩) (.var 0) 0 (constTM exBoxStrad ⟨1, 0⟩)
        r.1 r.2 ⟨-80, -80, -80⟩).isSome = true := by decide +kernel

/-- The div2 checker agrees with the C checker on an `ite`-hull leaf that
contains no division (no behavior change where the new channel is silent). -/
theorem exDiv2_agrees_no_div :
    checkPosTMHullD exIteHullChk exBoxHullChk TMParams.empty = true := by decide

/-- **Kernel replay of the full div2 checker** on that leaf
(`decide +kernel`). -/
theorem exDiv2_agrees_no_div_kernel :
    checkPosTMHullD exIteHullChk exBoxHullChk TMParams.empty = true := by
  decide +kernel

/-- The existing C checker still accepts the same leaf (opt-in boundary). -/
theorem exDiv2_old_checker_unchanged :
    checkPosTMHullC exIteHullChk exBoxHullChk TMParams.empty = true := by decide

#print axioms DInterval.loaLower_le_abs
#print axioms valid_sqrtL
#print axioms valid_div2
#print axioms divNode_sound
#print axioms evalTMHullD3C_sound
#print axioms checkPosTMHullD_sound
#print axioms exDiv2_fires
#print axioms exDiv2_fires_kernel
#print axioms exDiv2_agrees_no_div_kernel

end Kepler.Interval

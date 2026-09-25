/-
  549 range-composition work station — curvature-headroom SIMULATION
  (exploratory; companion of C549RangeBatchBase.lean).

  The 99-leaf NEG diagnosis (see C549RangeDbg2 trace, leaf 4): the binding
  constraint is NOT the ite err semantics (root jumpBound ≈ 2⁻⁸·³, the C¹
  join is real) but the `arctanK` TM-trans curvature bound
  `W² · 2(|fB| + W)` — on the reciprocal branch the atan argument enclosure
  is ≈ [-2.7, -1.3], where `2(|fB|+W)` ≈ 5.41 over-certifies the true
  `|atan''|` sup `2|x|/(1+x²)²` ≈ 0.075 by ~72×, contributing ≈ 2.67 of the
  root err 2.727 (98%).

  This probe measures the headroom: the same 160 leaves under a *certifiable*
  exact-sup curvature bound `sup 2|x|/(1+x²)²` over the argument enclosure
  (attained at an endpoint, or at |x| = 1/√3 when inside — elementary,
  provable; NOT yet certified in this pilot):

    D2   = production `evalTMHullD2` (baseline, agrees with the shards),
    D2T  = clone with the exact-sup arctan curvature bound,
    RNG  = range-composition `evalRangeHull` (branch valueRange hull),
    RNGT = range-composition over the D2T branch models.
-/
import Kepler.Interval.Cases.C549RangeBatchBase
import Kepler.Interval.Cases.C549StraddleBatchBase

set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
instance : Inhabited TMParams := ⟨⟨[], [], []⟩⟩
instance : Inhabited ((Fin 6 → DInterval) × TMParams × Bool × Bool × Float) :=
  ⟨(default, default, default, default, 0)⟩

/-! ### exact-sup arctan curvature (exploratory bound) -/

/-- `2|x|/(1+x²)²` at dyadic `t ≥ 0` — the arctan second-derivative
magnitude at `±t`. -/
def curvAt (t : Dyadic) : Dyadic :=
  match (DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add (t.mul t),
    (⟨1, 0⟩ : Dyadic).add (t.mul t)⟩ (-80)) with
  | some J => Dyadic.mul (Dyadic.mul ⟨2, 0⟩ t) (Dyadic.mul J.hi J.hi)
  | none => ⟨2, 0⟩

/-- Certified upper bound of the peak value `9√3/16 ≈ 0.974279` of
`2|x|/(1+x²)²` (attained at |x| = 1/√3). -/
def curvPeak : Dyadic := ⟨7982, -13⟩

/-- Upper bound of `sup_{|x| ∈ [a, b]} 2|x|/(1+x²)²`: max of the endpoint
values (the function increases on [0, 1/√3], decreases after) plus the peak
constant when the enclosure crosses 1/√3 (tested against an upper bound of
1/√3, so the test is conservative-inclusive). -/
def supCurv (fB : DInterval) : Dyadic :=
  let a := fB.abs.lo
  let b := fB.abs.hi
  let cross := Dyadic.ble a ⟨4730, -13⟩ && Dyadic.ble ⟨4730, -13⟩ b
  Dyadic.dmax (Dyadic.dmax (curvAt a) (curvAt b)) (if cross then curvPeak else ⟨0, 0⟩)

/-- `TaylorM.trans` clone for `arctanK` with the exact-sup curvature bound
(other kinds delegate).  Exploratory — the residual soundness for the new
bound is elementary but not certified in this pilot. -/
def transT {n : ℕ} (k : TKind) (M : TaylorM n) (N : ℕ) (out : Int)
    (p : TransTMP) : Option (TaylorM n) :=
  match k with
  | .arctanK =>
      (transOn .arctanK ⟨M.fB.lo, M.fB.hi⟩ N out).bind fun V =>
      (DInterval.recip ⟨(⟨1, 0⟩ : Dyadic).add (M.fB.abs.lo.mul M.fB.abs.lo),
        (⟨1, 0⟩ : Dyadic).add (M.fB.abs.hi.mul M.fB.abs.hi)⟩ p.o1).map fun J =>
      ⟨M.y, M.w, V, fun i => (M.dfB i).mul J,
        ((M.err.mul J.abs.hi).add
          ((M.W.mul M.W).mul (supCurv M.fB))).chopCeilTo M.errScale⟩
  | .sinK => M.trans .sinK N out p
  | .cosK => none
  | .lnK => M.trans .lnK N out p

/-- D2 clone with the tight-curvature arctan trans. -/
def evalTMHullD2T (box : Fin 6 → DInterval) :
    IExpr 6 → TMParams → Option (TaylorM 6 × TMParams)
  | .const d, ps => some (constTM box d, ps)
  | .var k, ps => some (varTM box k, ps)
  | .neg e, ps => (evalTMHullD2T box e ps).map fun (M, ps') => (M.neg, ps')
  | .add e₁ e₂, ps =>
      (evalTMHullD2T box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2T box e₂ ps₁).map fun (M₂, ps₂) => (M₁.add M₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalTMHullD2T box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2T box e₂ ps₁).map fun (M₂, ps₂) => (M₁.sub M₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalTMHullD2T box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2T box e₂ ps₁).map fun (M₂, ps₂) => (M₁.mul M₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalTMHullD2T box e₁ ps).bind fun (M₁, ps₁) =>
      (evalTMHullD2T box e₂ ps₁).bind fun (M₂, ps₂) =>
      ps₂.invCerts.head?.bind fun p =>
      ((M₂.inv p).map fun Mi => (M₁.mul Mi, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail,
          ps₂.transCerts⟩)).orElse
        (fun _ => ((IExpr.div e₁ e₂ out).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₂.sqrtCerts, ps₂.invCerts.tail, ps₂.transCerts⟩))
  | .sqrt e s₁ s₂, ps =>
      (evalTMHullD2T box e ps).bind fun (M₀, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun p =>
      ((M₀.sqrt p).map fun M' => (M', ⟨ps₀.sqrtCerts.tail, ps₀.invCerts,
          ps₀.transCerts⟩)).orElse
        (fun _ => ((IExpr.sqrt e s₁ s₂).eval box).map fun I =>
          (fallbackTM box I, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩))
  | .abs e, ps => ((IExpr.abs e).eval box).map fun I => (fallbackTM box I, ps)
  | .trans k e N out, ps =>
      if e.isClosed then
        ((IExpr.trans k e N out).eval box).map fun I => (closedTM box I, ps)
      else
        (evalTMHullD2T box e ps).bind fun (M₀, ps₀) =>
        ps₀.transCerts.head?.bind fun p =>
        ((transT k M₀ N out p).map fun M' =>
            (M', ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩)).orElse
          (fun _ => ((IExpr.trans k e N out).eval box).map fun I =>
            (fallbackTM box I, ⟨ps₀.sqrtCerts, ps₀.invCerts, ps₀.transCerts.tail⟩))
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then evalTMHullD2T box t ps₀
      else if C.lo.isNN then evalTMHullD2T box e ps₀
      else
        (evalTMHullD2T box t ps₀).bind fun (Mt, ps₁) =>
        (evalTMHullD2T box e ps₁).map fun (Me, ps₂) => (iteHullTM2 Mt Me, ps₂)

/-- Range-composition clone over the tight-curvature branch models. -/
def evalRangeHullT (box : Fin 6 → DInterval) :
    IExpr 6 → TMParams → Option (DInterval × TMParams)
  | .const d, ps => some (⟨d, d⟩, ps)
  | .var k, ps => some (box k, ps)
  | .neg e, ps => (evalRangeHullT box e ps).map fun (R, ps') => (R.neg, ps')
  | .abs e, ps => (evalRangeHullT box e ps).map fun (R, ps') => (R.abs, ps')
  | .add e₁ e₂, ps =>
      (evalRangeHullT box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHullT box e₂ ps₁).map fun (R₂, ps₂) => (R₁.add R₂, ps₂)
  | .sub e₁ e₂, ps =>
      (evalRangeHullT box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHullT box e₂ ps₁).map fun (R₂, ps₂) => (R₁.sub R₂, ps₂)
  | .mul e₁ e₂, ps =>
      (evalRangeHullT box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHullT box e₂ ps₁).map fun (R₂, ps₂) => (R₁.mul R₂, ps₂)
  | .div e₁ e₂ out, ps =>
      (evalRangeHullT box e₁ ps).bind fun (R₁, ps₁) =>
      (evalRangeHullT box e₂ ps₁).bind fun (R₂, ps₂) =>
      (DInterval.div R₁ R₂ out).map fun R => (R, ps₂)
  | .sqrt e _ _, ps =>
      (evalRangeHullT box e ps).bind fun (R, ps₀) =>
      ps₀.sqrtCerts.head?.bind fun t =>
      if R.hi.isNeg then none
      else
        (Dyadic.sqrtI R.hi t.shi).bind fun Jh =>
        (if R.lo.isNN then (Dyadic.sqrtI R.lo t.slo).map fun Jl => Jl.lo
          else some (⟨0, 0⟩ : Dyadic)).map fun L =>
          (⟨L, Jh.hi⟩, ⟨ps₀.sqrtCerts.tail, ps₀.invCerts, ps₀.transCerts⟩)
  | .trans k e N out, ps =>
      (evalRangeHullT box e ps).bind fun (R, ps₀) =>
      (transOn k R N out).map fun J => (J, ps₀)
  | .ite c t e, ps =>
      (evalIParams box c ps).bind fun (C, ps₀) =>
      if C.hi.isNeg then
        (evalTMHullD2T box t ps₀).map fun (M, ps') => (M.valueRange, ps')
      else if C.lo.isNN then
        (evalTMHullD2T box e ps₀).map fun (M, ps') => (M.valueRange, ps')
      else
        (evalTMHullD2T box t ps₀).bind fun (Mt, ps₁) =>
        (evalTMHullD2T box e ps₁).map fun (Me, ps₂) =>
          ((Mt.valueRange).hull Me.valueRange, ps₂)

def curvSimMain : List String → IO UInt32 := fun _ => do
  IO.println "g d2 d2T rng rngT"
  let mut d2pass := 0
  let mut d2tpass := 0
  let mut rngpass := 0
  let mut rngtpass := 0
  for i in [0:rangeLeaves.size] do
    let (box, ps, d2exp, _, _) := rangeLeaves[i]!
    let d2t := match evalTMHullD2T box C549StraddleBatchExpr ps with
      | some (M, _) => (M.loBound box).isPos
      | none => false
    let rngt := match evalRangeHullT box C549StraddleBatchExpr ps with
      | some (R, _) => R.lo.isPos
      | none => false
    -- D2 baseline = the shard theorems' verdict (d2exp)
    if d2t then d2tpass := d2tpass + 1
    if rngt then rngtpass := rngtpass + 1
    IO.println s!"{i+1} {if d2exp then 1 else 0} {if d2t then 1 else 0} {if rngt then 1 else 0}"
  IO.println s!"AGG d2(shards) on-file d2T {d2tpass}/160 rngT {rngtpass}/160"
  return 0

end Kepler.Interval.Cases

def main : List String → IO UInt32 := Kepler.Interval.Cases.curvSimMain

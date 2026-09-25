/-
  549 range-composition BATCH probe — compiled-run three-way measurement
  (companion of C549RangeBatchBase.lean).

  For each of the 160 production straddle leaves (same expression, boxes and
  TMParams as the committed C549StraddleBatchS1..S8 shards):

    D2    = kernel evaluator `evalTMHullD2` + `loBound` (the df-hull
            composite route; its verdict must agree with the shard `decide`
            theorems — asserted per leaf as D2-MISMATCH);
    RANGE = range-composition `evalRangeHull` (`checkPosRange`'s evaluator;
            the same TMParams — certificate layout compatible).

  Per-leaf line (integers are exact dyadic mantissa/exponent pairs):
    g d2 d2lo_m d2lo_e rng rnglo_m rnglo_e rnghi_m rnghi_e flags
  Aggregates: PASS counts, flips (rng PASS / d2 NEG), regressions
  (d2 PASS / rng NEG), D2/shard agreement.
-/
import Kepler.Interval.Cases.C549RangeBatchBase
import Kepler.Interval.Cases.C549StraddleBatchBase

set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

instance : Inhabited TMParams := ⟨⟨[], [], []⟩⟩

instance : Inhabited ((Fin 6 → DInterval) × TMParams × Bool × Bool × Float) :=
  ⟨(default, default, default, default, 0)⟩

def probeMain : List String → IO UInt32 := fun _ => do
  IO.println "g d2 d2lo_m d2lo_e rng rnglo_m rnglo_e rnghi_m rnghi_e f0 flags"
  let mut d2pass := 0
  let mut rngpass := 0
  let mut rsN := 0
  let mut rsPass := 0
  let mut flips := 0
  let mut regrs := 0
  let mut mismatch := 0
  for i in [0:rangeLeaves.size] do
    let (box, ps, d2exp, rs, f0) := rangeLeaves[i]!
    let g := i + 1
    let d2lo := match evalTMHullD2 box C549StraddleBatchExpr ps with
      | some (M, _) => M.loBound box
      | none => ⟨0, -999⟩
    let d2 := d2lo.isPos
    let rng := match evalRangeHull box C549StraddleBatchExpr ps with
      | some (R, _) => R
      | none => ⟨⟨0, -999⟩, ⟨0, -999⟩⟩
    let rngpos := rng.lo.isPos
    let mut flags := ""
    if d2 != d2exp then
      flags := flags ++ "D2-MISMATCH "
      mismatch := mismatch + 1
    if d2 then d2pass := d2pass + 1
    if rngpos then rngpass := rngpass + 1
    if rs then
      rsN := rsN + 1
      if rngpos then rsPass := rsPass + 1
      if rngpos && !d2 then
        flips := flips + 1
        flags := flags ++ "FLIP "
    if d2 && !rngpos then
      regrs := regrs + 1
      flags := flags ++ "REGR "
    IO.println s!"{g} {if d2 then 1 else 0} {d2lo.m} {d2lo.e} \
      {if rngpos then 1 else 0} {rng.lo.m} {rng.lo.e} {rng.hi.m} {rng.hi.e} \
      {f0} {flags}"
  IO.println s!"AGG d2 {d2pass}/160 range {rngpass}/160 rootstraddle \
    {rsPass}/{rsN} flips {flips} regr {regrs} d2mismatch {mismatch}"
  return 0

end Kepler.Interval.Cases

def main : List String → IO UInt32 :=
  Kepler.Interval.Cases.probeMain

/-
  Phase 4, G4: **FillParams** — per-leaf certificate-parameter computation
  for the `BBTreeG` pipeline (compile-time evaluation only; no proof
  obligations here).

  `IExpr.sqrt` bakes the two root mantissas `s₁ s₂` into the expression, but
  the radicand interval varies from leaf to leaf of a bisection tree, so the
  mantissas must be computed *per leaf*.  `Nat.sqrt` does not kernel-reduce
  (that is why `Dyadic.sqrtI` takes a certificate in the first place), but
  it runs fine under the interpreter/`--run` — so this tool recomputes the
  exact mantissas at certificate-production time and the kernel later only
  verifies `s² ≤ n < (s+1)²` in `Int`.

  ## Semantics contract (what makes the output trustworthy)

  `evalFill` is a **tracing evaluator**: it mirrors `IExpr.eval` exactly —
  same `DInterval` ops, same `ite` resolution by interval sign, node-supplied
  `div`/`trans` parameters — except at `.sqrt` nodes, where it *computes*
  the exact floor mantissas `s = Nat.sqrt (d.m * 2^(d.e % 2))` from the
  radicand interval and then runs the same `Dyadic.sqrtI` check.  Hence

    `evalFill e box = (some I, ms)`  ⟹  `IExpr.eval (fill e ms) box = some I`

  (the filled expression puts `ms` back into the sqrt slots), so the tool's
  PASS (`I.lo.isPos`) predicts the kernel `checkPos` of the filled leaf
  expression.  Nested square roots fall out bottom-up for free.

  The `ms` list is in **RPN/post order** (subterms before the node itself,
  left to right) — the same order the generator (`emit_lean.py --fill`)
  assigns parameter slots.  Subtrees the evaluator never visits (untaken
  `ite` branches, anything past a failure) contribute `(0, 0)` placeholders;
  the kernel's `eval` never visits them either, so any value there is
  semantically inert.

  ## atan rung ladder

  `trans` parameters (`N` Taylor terms, `2^out` granularity) are likewise
  certificate-only (`evalReal` ignores them).  `runLadder` walks a ladder of
  `(N, out)` rungs and reports the first rung on which every leaf PASSes;
  the per-rung failure counts go to stderr, the winning rung and the
  per-leaf mantissa lists to stdout:

    RUNG <N> <out>
    <leafIdx> PASS s₁ t₁ s₂ t₂ …

  If no rung passes, the best (fewest-failures) rung is printed with
  per-leaf PASS/FAIL marks after a `BESTFAIL` header and the exit code is 1.

  Checking layer: `Int` only. No `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.Expr

namespace Kepler.Interval

namespace IExpr

/-- Number of `.sqrt` nodes (static count; fixes the parameter-list length
and the generator's `Vector (Int × Int) k` index). -/
def countSqrt {n : ℕ} : IExpr n → ℕ
  | .const _ => 0
  | .var _ => 0
  | .neg e => e.countSqrt
  | .abs e => e.countSqrt
  | .ite c t e => c.countSqrt + t.countSqrt + e.countSqrt
  | .add e₁ e₂ => e₁.countSqrt + e₂.countSqrt
  | .sub e₁ e₂ => e₁.countSqrt + e₂.countSqrt
  | .mul e₁ e₂ => e₁.countSqrt + e₂.countSqrt
  | .div e₁ e₂ _ => e₁.countSqrt + e₂.countSqrt
  | .sqrt e _ _ => e.countSqrt + 1
  | .trans _ e _ _ => e.countSqrt

end IExpr

namespace Dyadic

/-- Exact floor-root mantissa for a nonnegative dyadic, computed off-kernel:
`sqrtFloor d = ⌊√(d.m · 2^(d.e % 2))⌋`, so `Dyadic.sqrtI d (sqrtFloor d)`
passes its kernel check whenever `d.m ≥ 0`.  Returns `0` for `d.m < 0`
(`sqrtI` fails there for every certificate, exactly as `IExpr.eval` does). -/
def sqrtFloor (d : Dyadic) : Int :=
  if 0 ≤ d.m then Int.ofNat (Nat.sqrt (d.m * 2 ^ (d.e % 2).toNat).toNat) else 0

end Dyadic

namespace Tools

/-- **Tracing evaluator**: identical semantics to `IExpr.eval`, but computes
the `.sqrt` certificate mantissas from the radicand interval (see the module
docstring for the contract) and collects them, in RPN/post order, as the
second component. -/
def evalFill {n : ℕ} : IExpr n → (Fin n → DInterval) → Option DInterval × List (Int × Int)
  | .const d, _ => (some ⟨d, d⟩, [])
  | .var i, box => (some (box i), [])
  | .neg e, box =>
      let (o, l) := evalFill e box
      (o.map DInterval.neg, l)
  | .abs e, box =>
      let (o, l) := evalFill e box
      (o.map DInterval.abs, l)
  | .ite c t e, box =>
      let (oC, lc) := evalFill c box
      match oC with
      | some C =>
          if C.hi.isNeg then
            let (oT, lt) := evalFill t box
            (oT, lc ++ lt ++ List.replicate (IExpr.countSqrt e) (0, 0))
          else if C.lo.isNN then
            let (oE, le) := evalFill e box
            (oE, lc ++ List.replicate (IExpr.countSqrt t) (0, 0) ++ le)
          else
            (none, lc ++ List.replicate (IExpr.countSqrt t + IExpr.countSqrt e) (0, 0))
      | none => (none, lc ++ List.replicate (IExpr.countSqrt t + IExpr.countSqrt e) (0, 0))
  | .add e₁ e₂, box =>
      let (o₁, l₁) := evalFill e₁ box
      let (o₂, l₂) := evalFill e₂ box
      (match o₁, o₂ with
       | some I, some J => some (I.add J)
       | _, _ => none, l₁ ++ l₂)
  | .sub e₁ e₂, box =>
      let (o₁, l₁) := evalFill e₁ box
      let (o₂, l₂) := evalFill e₂ box
      (match o₁, o₂ with
       | some I, some J => some (I.sub J)
       | _, _ => none, l₁ ++ l₂)
  | .mul e₁ e₂, box =>
      let (o₁, l₁) := evalFill e₁ box
      let (o₂, l₂) := evalFill e₂ box
      (match o₁, o₂ with
       | some I, some J => some (I.mul J)
       | _, _ => none, l₁ ++ l₂)
  | .div e₁ e₂ out, box =>
      let (o₁, l₁) := evalFill e₁ box
      let (o₂, l₂) := evalFill e₂ box
      (match o₁, o₂ with
       | some I, some J => DInterval.div I J out
       | _, _ => none, l₁ ++ l₂)
  | .sqrt e _ _, box =>
      let (oJ, l) := evalFill e box
      match oJ with
      | some J =>
          let s₁ := J.lo.sqrtFloor
          let s₂ := J.hi.sqrtFloor
          (match Dyadic.sqrtI J.lo s₁, Dyadic.sqrtI J.hi s₂ with
           | some Jl, some Jh => some ⟨Jl.lo, Jh.hi⟩
           | _, _ => none, l ++ [(s₁, s₂)])
      | none => (none, l ++ [(0, 0)])
  | .trans k e N out, box =>
      let (oJ, l) := evalFill e box
      (match oJ with
       | some I => transOn k I N out
       | none => none, l)

/-- Per-leaf result: did the (filled) interval evaluation succeed with a
positive lower endpoint, plus the mantissa list (length `countSqrt e`). -/
structure LeafResult where
  pass : Bool
  params : List (Int × Int)

/-- Fill the parameters for one leaf and check positivity (predicts the
kernel `checkPos` of the filled expression). -/
def checkLeaf {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) : LeafResult :=
  let (o, l) := evalFill e box
  match o with
  | some I => ⟨I.lo.isPos, l⟩
  | none => ⟨false, l⟩

/-- The `(N, out)` rung ladder for `.trans` nodes: raise the Taylor order
first (the alternating-series remainder at boundary arguments like
`arctan 1` is `1/(2N+1)`, so the ladder must reach far), then the output
granularity. -/
def ladder : Array (ℕ × Int) :=
  #[(12, -64), (16, -64), (20, -64), (24, -64), (32, -64), (48, -64), (64, -64),
    (96, -64), (128, -64), (128, -80), (128, -100)]

/-- Evaluate all leaves at one rung; returns the failure count and the
per-leaf results. -/
def runRung {n : ℕ} (mkExpr : ℕ → Int → IExpr n) (boxes : Array (Fin n → DInterval))
    (N : ℕ) (out : Int) : IO (ℕ × Array LeafResult) := do
  let e := mkExpr N out
  let mut results := #[]
  let mut fails := 0
  for box in boxes do
    let r := checkLeaf e box
    if !r.pass then fails := fails + 1
    results := results.push r
  return (fails, results)

/-- Print one `i PASS/FAIL s₁ t₁ …` line per leaf. -/
def printResults (results : Array LeafResult) : IO Unit := do
  let mut i := 0
  for r in results do
    let params := " ".intercalate (r.params.map fun (s, t) => s!"{s} {t}")
    IO.println s!"{i} {if r.pass then "PASS" else "FAIL"} {params}"
    i := i + 1

/-- Stage-A entry point: walk the rung ladder; on the first all-PASS rung
print `RUNG N out` plus the per-leaf mantissa lines and exit 0; otherwise
print the best rung under a `BESTFAIL` header and exit 1. -/
def runLadder {n : ℕ} (mkExpr : ℕ → Int → IExpr n)
    (boxes : Array (Fin n → DInterval)) : IO UInt32 := do
  let mut best : Option (ℕ × ℕ × Int × Array LeafResult) := none
  for (N, out) in ladder do
    let (fails, results) ← runRung mkExpr boxes N out
    IO.eprintln s!"rung N={N} out={out}: {fails}/{boxes.size} failures"
    if fails == 0 then
      IO.println s!"RUNG {N} {out}"
      printResults results
      return 0
    if best.all (fun (b, _, _, _) => fails < b) then
      best := some (fails, N, out, results)
  match best with
  | some (fails, N, out, results) =>
      IO.println s!"BESTFAIL N={N} out={out} failures={fails}/{boxes.size}"
      printResults results
  | none => IO.println "BESTFAIL no-rungs"
  return 1

end Tools

end Kepler.Interval

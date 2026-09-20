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
  same `DInterval` ops, same `ite` resolution by interval sign (with the
  guard-straddle hull fallback: both branches then contribute REAL
  mantissas), node-supplied
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

instance : Hashable Dyadic := ⟨fun d => mixHash (Hashable.hash d.m) (Hashable.hash d.e)⟩

/-- Tag for hashing `TKind`. -/
def TKind.toTag : TKind → UInt64
  | .sinK => 0 | .cosK => 1 | .arctanK => 2 | .lnK => 3

instance : Hashable TKind := ⟨fun k => k.toTag⟩

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

/-- Variable-freedom (leaf-constant) predicate; mirrors the emitter's
`closed` tracking.  A closed subterm evaluates to the same interval and the
same sqrt-parameter list at every leaf and every rung — the memo table
(`Tools.FillCache`) keys on this. -/
def isClosed {n : ℕ} : IExpr n → Bool
  | .const _ => true
  | .var _ => false
  | .neg e => e.isClosed
  | .abs e => e.isClosed
  | .ite c t e => c.isClosed && t.isClosed && e.isClosed
  | .add e₁ e₂ => e₁.isClosed && e₂.isClosed
  | .sub e₁ e₂ => e₁.isClosed && e₂.isClosed
  | .mul e₁ e₂ => e₁.isClosed && e₂.isClosed
  | .div e₁ e₂ _ => e₁.isClosed && e₂.isClosed
  | .sqrt e _ _ => e.isClosed
  | .trans _ e _ _ => e.isClosed

/-- Structural equality (memo-table keys only; the kernel never sees this). -/
protected def beq {n : ℕ} : IExpr n → IExpr n → Bool
  | .const a, .const b => a == b
  | .var i, .var j => i == j
  | .neg a, .neg b => IExpr.beq a b
  | .abs a, .abs b => IExpr.beq a b
  | .ite c₁ t₁ e₁, .ite c₂ t₂ e₂ => IExpr.beq c₁ c₂ && IExpr.beq t₁ t₂ && IExpr.beq e₁ e₂
  | .add a₁ b₁, .add a₂ b₂ => IExpr.beq a₁ a₂ && IExpr.beq b₁ b₂
  | .sub a₁ b₁, .sub a₂ b₂ => IExpr.beq a₁ a₂ && IExpr.beq b₁ b₂
  | .mul a₁ b₁, .mul a₂ b₂ => IExpr.beq a₁ a₂ && IExpr.beq b₁ b₂
  | .div a₁ b₁ o₁, .div a₂ b₂ o₂ => o₁ == o₂ && IExpr.beq a₁ a₂ && IExpr.beq b₁ b₂
  | .sqrt a₁ s₁ t₁, .sqrt a₂ s₂ t₂ => s₁ == s₂ && t₁ == t₂ && IExpr.beq a₁ a₂
  | .trans k₁ a₁ N₁ o₁, .trans k₂ a₂ N₂ o₂ =>
      k₁ == k₂ && N₁ == N₂ && o₁ == o₂ && IExpr.beq a₁ a₂
  | _, _ => false
  termination_by a b => sizeOf a + sizeOf b

/-- Structural hash (memo-table keys only). -/
protected def hash {n : ℕ} : IExpr n → UInt64
  | .const d => mixHash 1 (Hashable.hash d)
  | .var i => mixHash 2 (Hashable.hash i)
  | .neg a => mixHash 3 (IExpr.hash a)
  | .abs a => mixHash 4 (IExpr.hash a)
  | .ite c t e => mixHash 5 (mixHash (IExpr.hash c) (mixHash (IExpr.hash t) (IExpr.hash e)))
  | .add a b => mixHash 6 (mixHash (IExpr.hash a) (IExpr.hash b))
  | .sub a b => mixHash 7 (mixHash (IExpr.hash a) (IExpr.hash b))
  | .mul a b => mixHash 8 (mixHash (IExpr.hash a) (IExpr.hash b))
  | .div a b o => mixHash 9 (mixHash (Hashable.hash o) (mixHash (IExpr.hash a) (IExpr.hash b)))
  | .sqrt a s₁ s₂ =>
      mixHash 10 (mixHash (Hashable.hash s₁) (mixHash (Hashable.hash s₂) (IExpr.hash a)))
  | .trans k a N o =>
      mixHash 11 (mixHash (Hashable.hash k) (mixHash (Hashable.hash N)
        (mixHash (Hashable.hash o) (IExpr.hash a))))

instance : BEq (IExpr n) := ⟨IExpr.beq⟩
instance : Hashable (IExpr n) := ⟨IExpr.hash⟩

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
            -- guard straddles 0: hull of both branches (bb_arb `ufall`
            -- union fallback, mirrors `IExpr.eval`); BOTH branches are
            -- genuinely evaluated, so both contribute real mantissas.
            let (oT, lt) := evalFill t box
            let (oE, le) := evalFill e box
            (match oT, oE with
             | some T, some E => some (DInterval.hull T E)
             | _, _ => none, lc ++ lt ++ le)
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

/-! ### Closed-subterm memoization (W2.5)

A *closed* (var-free, `IExpr.isClosed`) `.trans` node carries fixed
certificate parameters (the emitter gives closed trans nodes the literal
`(2048, -64)` regardless of the rung arguments), so its `evalFill` result —
interval value AND sqrt-parameter list — is identical at every leaf and
every rung.  Yet `evalFill` recomputed it per leaf: the BIXPCGW main prog
carries 89 reachable closed `atan` nodes at N=2048 ≈ 220s of the ~255s
per-leaf cost.  The runners below therefore build a memo table once per
driver run (`buildCache`) and evaluate with `evalFillC`, which answers
closed-argument `.trans` nodes from the table.

Only `.trans` nodes are memoized: they are the expensive leaves of the
interval semantics (Taylor sums), and restricting the per-leaf guard to
trans nodes keeps the memo overhead negligible (a full `isClosed` check at
*every* node costs O(|expr|²) per leaf and ate the entire speedup in the
first W2.5 attempt).  The table maps the trans node to the full
`(value, params)` pair of `evalFill`, so per-leaf output (including
parameter lists) is bit-identical to the unmemoized run.  Cache misses fall
back to plain `evalFill`, so correctness never depends on which subterms
were pre-collected. -/

/-- Memo table: closed-argument `.trans` node ↦ its `evalFill` result. -/
abbrev FillCache (n : ℕ) := Std.HashMap (IExpr n) (Option DInterval × List (Int × Int))

/-- Memoized tracing evaluator: identical to `evalFill`, except `.trans`
nodes with closed (var-free) arguments are answered from `cache` (miss =
plain `evalFill`, same value). -/
def evalFillC {n : ℕ} (cache : FillCache n) :
    IExpr n → (Fin n → DInterval) → Option DInterval × List (Int × Int)
  | .const d, _ => (some ⟨d, d⟩, [])
  | .var i, box => (some (box i), [])
  | .neg e, box =>
      let (o, l) := evalFillC cache e box
      (o.map DInterval.neg, l)
  | .abs e, box =>
      let (o, l) := evalFillC cache e box
      (o.map DInterval.abs, l)
  | .ite c t e, box =>
      let (oC, lc) := evalFillC cache c box
      match oC with
      | some C =>
          if C.hi.isNeg then
            let (oT, lt) := evalFillC cache t box
            (oT, lc ++ lt ++ List.replicate (IExpr.countSqrt e) (0, 0))
          else if C.lo.isNN then
            let (oE, le) := evalFillC cache e box
            (oE, lc ++ List.replicate (IExpr.countSqrt t) (0, 0) ++ le)
          else
            -- guard straddle: hull of both branches (see `evalFill`)
            let (oT, lt) := evalFillC cache t box
            let (oE, le) := evalFillC cache e box
            (match oT, oE with
             | some T, some E => some (DInterval.hull T E)
             | _, _ => none, lc ++ lt ++ le)
      | none => (none, lc ++ List.replicate (IExpr.countSqrt t + IExpr.countSqrt e) (0, 0))
  | .add e₁ e₂, box =>
      let (o₁, l₁) := evalFillC cache e₁ box
      let (o₂, l₂) := evalFillC cache e₂ box
      (match o₁, o₂ with
       | some I, some J => some (I.add J)
       | _, _ => none, l₁ ++ l₂)
  | .sub e₁ e₂, box =>
      let (o₁, l₁) := evalFillC cache e₁ box
      let (o₂, l₂) := evalFillC cache e₂ box
      (match o₁, o₂ with
       | some I, some J => some (I.sub J)
       | _, _ => none, l₁ ++ l₂)
  | .mul e₁ e₂, box =>
      let (o₁, l₁) := evalFillC cache e₁ box
      let (o₂, l₂) := evalFillC cache e₂ box
      (match o₁, o₂ with
       | some I, some J => some (I.mul J)
       | _, _ => none, l₁ ++ l₂)
  | .div e₁ e₂ out, box =>
      let (o₁, l₁) := evalFillC cache e₁ box
      let (o₂, l₂) := evalFillC cache e₂ box
      (match o₁, o₂ with
       | some I, some J => DInterval.div I J out
       | _, _ => none, l₁ ++ l₂)
  | .sqrt e _ _, box =>
      let (oJ, l) := evalFillC cache e box
      match oJ with
      | some J =>
          let s₁ := J.lo.sqrtFloor
          let s₂ := J.hi.sqrtFloor
          (match Dyadic.sqrtI J.lo s₁, Dyadic.sqrtI J.hi s₂ with
           | some Jl, some Jh => some ⟨Jl.lo, Jh.hi⟩
           | _, _ => none, l ++ [(s₁, s₂)])
      | none => (none, l ++ [(0, 0)])
  | .trans k a N out, box =>
      if a.isClosed then
        match cache.get? (.trans k a N out) with
        | some v => v
        | none => evalFill (.trans k a N out) box
      else
        let (oJ, l) := evalFillC cache a box
        (match oJ with
         | some I => transOn k I N out
         | none => none, l)

/-- Collect every maximal closed-argument `.trans` node of `e` into the memo
table, evaluating each once with plain `evalFill` against a dummy box
(the node is var-free and never consults the box). -/
def buildCache {n : ℕ} (cache : FillCache n) (e : IExpr n) : FillCache n :=
  match e with
  | .trans _ a _ _ =>
      if a.isClosed then cache.insert e (evalFill e fun _ => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩)
      else buildCache cache a
  | .const _ | .var _ => cache
  | .neg a | .abs a | .sqrt a _ _ => buildCache cache a
  | .ite c t a => buildCache (buildCache (buildCache cache c) t) a
  | .add a b | .sub a b | .mul a b | .div a b _ => buildCache (buildCache cache a) b
termination_by e

/-- Memoized variant of `checkLeaf`. -/
def checkLeafC {n : ℕ} (cache : FillCache n) (e : IExpr n)
    (box : Fin n → DInterval) : LeafResult :=
  let (o, l) := evalFillC cache e box
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
per-leaf results.  Closed subterms are served from the chunk-level memo
table `cache` (built once per driver run by `runLadder`/`runSingle`). -/
def runRung {n : ℕ} (cache : FillCache n) (mkExpr : ℕ → Int → IExpr n)
    (boxes : Array (Fin n → DInterval)) (N : ℕ) (out : Int)
    : IO (ℕ × Array LeafResult) := do
  let e := mkExpr N out
  let mut results := #[]
  let mut fails := 0
  for box in boxes do
    let r := checkLeafC cache e box
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
  let cache := buildCache ∅ (mkExpr 0 0)
  IO.eprintln s!"memoized {cache.size} closed subterms"
  let mut best : Option (ℕ × ℕ × Int × Array LeafResult) := none
  for (N, out) in ladder do
    let (fails, results) ← runRung cache mkExpr boxes N out
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

/-- Evaluate a single pinned rung; print the per-leaf lines and exit 0 when
every leaf passes, else print a `BESTFAIL` header and exit 1.  Sharded
stage-A phase 2 uses this to recompute params at the global rung. -/
def runSingle {n : ℕ} (mkExpr : ℕ → Int → IExpr n)
    (boxes : Array (Fin n → DInterval)) (N : ℕ) (out : Int) : IO UInt32 := do
  let cache := buildCache ∅ (mkExpr N out)
  IO.eprintln s!"memoized {cache.size} closed subterms"
  let (fails, results) ← runRung cache mkExpr boxes N out
  IO.eprintln s!"rung N={N} out={out}: {fails}/{boxes.size} failures"
  if fails == 0 then
    IO.println s!"RUNG {N} {out}"
    printResults results
    return 0
  IO.println s!"BESTFAIL N={N} out={out} failures={fails}/{boxes.size}"
  printResults results
  return 1

/-- Stage-A main with argv dispatch: no args walks the rung ladder;
`N out` evaluates that pinned rung (sharded stage-A phase 2). -/
def runMain {n : ℕ} (mkExpr : ℕ → Int → IExpr n)
    (boxes : Array (Fin n → DInterval)) : List String → IO UInt32
  | [ns, outs] =>
    match ns.toNat?, outs.toInt? with
    | some N, some out => runSingle mkExpr boxes N out
    | _, _ => runLadder mkExpr boxes
  | _ => runLadder mkExpr boxes

/-! ### Data-file drivers

Boxes as runtime data instead of source literals: the elaboration of a
million-leaf box array does not scale (the monolithic driver needed
11.5h+), while parsing a text file at runtime is seconds.  One line per
leaf, `lm le hm he` per dimension (emitted dyadic form, no normalization). -/

/-- Parse one box line (`4*n` ints, single-space separated) into a
`Fin n → DInterval`. -/
def parseBoxLine (n : ℕ) (ln : String) : Option (Fin n → DInterval) :=
  let ws := (ln.trim.splitOn " ").filter (!·.isEmpty)
  if ws.length != 4 * n then none
  else
    let rec go : List String → Array DInterval → Option (Array DInterval)
      | [], acc => some acc
      | a :: b :: c :: d :: rest, acc =>
        match a.toInt?, b.toInt?, c.toInt?, d.toInt? with
        | some lm, some le, some hm, some he =>
          go rest (acc.push ⟨⟨lm, le⟩, ⟨hm, he⟩⟩)
        | _, _, _, _ => none
      | _, _ => none
    (go ws #[]).map fun arr (i : Fin n) => arr.getD i ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Stream a boxes data file into memory; dies on the first malformed line. -/
def readBoxes (n : ℕ) (path : String) : IO (Array (Fin n → DInterval)) := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.read
  let mut out : Array (Fin n → DInterval) := #[]
  repeat
    let ln ← h.getLine
    if ln.isEmpty then break
    match parseBoxLine n ln with
    | some b => out := out.push b
    | none => throw (IO.userError s!"malformed box line: {ln.take 80}")
  IO.eprintln s!"read {out.size} boxes from {path}"
  return out

/-- Data-file stage-A main: `boxes.txt` walks the ladder, `boxes.txt N out`
evaluates the pinned rung. -/
def runMainFile {n : ℕ} (mkExpr : ℕ → Int → IExpr n) : List String → IO UInt32
  | [path] => do
      let boxes ← readBoxes n path
      runLadder mkExpr boxes
  | [path, ns, outs] =>
    match ns.toNat?, outs.toInt? with
    | some N, some out => do
        let boxes ← readBoxes n path
        runSingle mkExpr boxes N out
    | _, _ => throw (IO.userError "usage: driver <boxes.txt> [N out]")
  | _ => throw (IO.userError "usage: driver <boxes.txt> [N out]")

/-! ### Disjunctive stage A (schema v2)

Disjunctive goals (`emit_rpn.py` `disj` field): a leaf certificate only needs
*some* disjunct to hold, so the stage-A driver carries **all** goal
expressions (main prog first, then each disj entry in case order) and
decides per leaf which branch holds, recomputing the bb_arb `hit` rather
than trusting it (design D2: the cert hit is a first-hit-wins witness at
FLINT precision, not a unique branch).

Judgement order per leaf (cheap first): every `.varLt` goal by the exact box
check `Dyadic.blt (box i).hi (box j).lo` (the same test as
`DisjGoal.check`), then every `.pos` goal in goal order via `checkLeaf`;
the first branch that holds wins.  Output per leaf (params schema v2):

  `<i> PASSV <k>`         — varLt goal `k` hit, no parameters
  `<i> PASS <k> s₁ t₁ …`  — pos goal `k` hit, `2·countSqrt (goals[k])` ints
  `<i> FAIL`              — no branch holds at this rung

The rung ladder is global and unchanged: the first rung at which every leaf
has *some* passing branch wins (only pos branches consume the rung; varLt
checks are rung-independent).  The goal index `k` refers to the full goals
list (main = 0, disj entry `j` = `j+1`). -/

/-- One goal of a disjunctive stage-A driver: a pos branch (expression
factory over the rung arguments, dummy sqrt slots) or a varLt branch
(exact box check, no parameters). -/
inductive FillGoal (n : ℕ) : Type where
  | pos (mk : ℕ → Int → IExpr n)
  | varLt (i j : Fin n)

/-- Per-leaf disjunctive result: the winning goal index (none = FAIL),
whether it was a varLt goal (no params), and the sqrt mantissa list. -/
structure DisjLeafResult where
  hit : Option ℕ
  hitVarLt : Bool
  params : List (Int × Int)

/-- Per-leaf disjunctive judgement: all varLt goals (goal order) by exact box
check, then all pos goals (goal order) by `checkLeafC` at rung `(N, out)`;
first branch that holds wins.  `cache` is the union memo table over all pos
goals' closed subterms (`goalsCache`). -/
def checkLeafDisj {n : ℕ} (cache : FillCache n) (goals : List (FillGoal n))
    (box : Fin n → DInterval) (N : ℕ) (out : Int) : DisjLeafResult :=
  match findVarLt goals 0 with
  | some k => ⟨some k, true, []⟩
  | none =>
    match findPos goals 0 with
    | some (k, params) => ⟨some k, false, params⟩
    | none => ⟨none, false, []⟩
where
  findVarLt : List (FillGoal n) → ℕ → Option ℕ
    | [], _ => none
    | .varLt i j :: gs, k =>
        if Dyadic.blt (box i).hi (box j).lo then some k else findVarLt gs (k + 1)
    | .pos _ :: gs, k => findVarLt gs (k + 1)
  findPos : List (FillGoal n) → ℕ → Option (ℕ × List (Int × Int))
    | [], _ => none
    | .pos mk :: gs, k =>
        let r := checkLeafC cache (mk N out) box
        if r.pass then some (k, r.params) else findPos gs (k + 1)
    | .varLt _ _ :: gs, k => findPos gs (k + 1)

/-- Union memo table over all pos goals (each built from `mk 0 0` — closed
subterms are rung-independent, and a miss falls back to plain evaluation, so
correctness never depends on the factory's rung arguments). -/
def goalsCache {n : ℕ} (goals : List (FillGoal n)) : FillCache n :=
  goals.foldl (fun c g => match g with
    | .pos mk => buildCache c (mk 0 0)
    | .varLt _ _ => c) ∅

/-- Print one schema-v2 line per leaf: `i PASSV k` / `i PASS k s₁ t₁ …` /
`i FAIL`. -/
def printResultsDisj (results : Array DisjLeafResult) : IO Unit := do
  let mut i := 0
  for r in results do
    match r.hit with
    | some k =>
      if r.hitVarLt then
        IO.println s!"{i} PASSV {k}"
      else
        let params := " ".intercalate (r.params.map fun (s, t) => s!"{s} {t}")
        IO.println s!"{i} PASS {k} {params}"
    | none => IO.println s!"{i} FAIL"
    i := i + 1

/-- Evaluate all leaves at one rung against all goals; returns the failure
count (leaves with no passing branch) and the per-leaf results. -/
def runRungDisj {n : ℕ} (cache : FillCache n) (goals : List (FillGoal n))
    (boxes : Array (Fin n → DInterval)) (N : ℕ) (out : Int)
    : IO (ℕ × Array DisjLeafResult) := do
  let mut results := #[]
  let mut fails := 0
  for box in boxes do
    let r := checkLeafDisj cache goals box N out
    if r.hit.isNone then fails := fails + 1
    results := results.push r
  return (fails, results)

/-- Disjunctive stage-A entry point: walk the rung ladder; on the first rung
where every leaf has a passing branch print `RUNG N out` plus the schema-v2
per-leaf lines and exit 0; otherwise print the best rung under a `BESTFAIL`
header and exit 1. -/
def runLadderDisj {n : ℕ} (goals : List (FillGoal n))
    (boxes : Array (Fin n → DInterval)) : IO UInt32 := do
  let cache := goalsCache goals
  IO.eprintln s!"memoized {cache.size} closed subterms"
  let mut best : Option (ℕ × ℕ × Int × Array DisjLeafResult) := none
  for (N, out) in ladder do
    let (fails, results) ← runRungDisj cache goals boxes N out
    IO.eprintln s!"rung N={N} out={out}: {fails}/{boxes.size} failures"
    if fails == 0 then
      IO.println s!"RUNG {N} {out}"
      printResultsDisj results
      return 0
    if best.all (fun (b, _, _, _) => fails < b) then
      best := some (fails, N, out, results)
  match best with
  | some (fails, N, out, results) =>
      IO.println s!"BESTFAIL N={N} out={out} failures={fails}/{boxes.size}"
      printResultsDisj results
  | none => IO.println "BESTFAIL no-rungs"
  return 1

/-- Pinned-rung disjunctive evaluation (sharded stage-A phase 2). -/
def runSingleDisj {n : ℕ} (goals : List (FillGoal n))
    (boxes : Array (Fin n → DInterval)) (N : ℕ) (out : Int) : IO UInt32 := do
  let cache := goalsCache goals
  IO.eprintln s!"memoized {cache.size} closed subterms"
  let (fails, results) ← runRungDisj cache goals boxes N out
  IO.eprintln s!"rung N={N} out={out}: {fails}/{boxes.size} failures"
  if fails == 0 then
    IO.println s!"RUNG {N} {out}"
    printResultsDisj results
    return 0
  IO.println s!"BESTFAIL N={N} out={out} failures={fails}/{boxes.size}"
  printResultsDisj results
  return 1

/-- Disjunctive stage-A main with argv dispatch: no args walks the ladder,
`N out` evaluates that pinned rung. -/
def runMainDisj {n : ℕ} (goals : List (FillGoal n))
    (boxes : Array (Fin n → DInterval)) : List String → IO UInt32
  | [ns, outs] =>
    match ns.toNat?, outs.toInt? with
    | some N, some out => runSingleDisj goals boxes N out
    | _, _ => runLadderDisj goals boxes
  | _ => runLadderDisj goals boxes

/-- Data-file disjunctive stage-A main: `boxes.txt` walks the ladder,
`boxes.txt N out` evaluates the pinned rung. -/
def runMainFileDisj {n : ℕ} (goals : List (FillGoal n)) : List String → IO UInt32
  | [path] => do
      let boxes ← readBoxes n path
      runLadderDisj goals boxes
  | [path, ns, outs] =>
    match ns.toNat?, outs.toInt? with
    | some N, some out => do
        let boxes ← readBoxes n path
        runSingleDisj goals boxes N out
    | _, _ => throw (IO.userError "usage: driver <boxes.txt> [N out]")
  | _ => throw (IO.userError "usage: driver <boxes.txt> [N out]")

end Tools

end Kepler.Interval

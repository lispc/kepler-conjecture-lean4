import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval

/-! ## Node census (the certificate queue layout) -/

/-- `(sqrt, div, trans)` node counts of an expression in traversal order —
the number of certificates a leaf's `TMParams` must supply. -/
def IExpr.nodeCensus {n : ℕ} : IExpr n → Nat × Nat × Nat
  | .const _ => (0, 0, 0)
  | .var _ => (0, 0, 0)
  | .neg e => e.nodeCensus
  | .abs e => e.nodeCensus
  | .add a b => ⟨a.nodeCensus.1 + b.nodeCensus.1,
                 a.nodeCensus.2.1 + b.nodeCensus.2.1,
                 a.nodeCensus.2.2 + b.nodeCensus.2.2⟩
  | .sub a b => ⟨a.nodeCensus.1 + b.nodeCensus.1,
                 a.nodeCensus.2.1 + b.nodeCensus.2.1,
                 a.nodeCensus.2.2 + b.nodeCensus.2.2⟩
  | .mul a b => ⟨a.nodeCensus.1 + b.nodeCensus.1,
                 a.nodeCensus.2.1 + b.nodeCensus.2.1,
                 a.nodeCensus.2.2 + b.nodeCensus.2.2⟩
  | .div a b _ => ⟨a.nodeCensus.1 + b.nodeCensus.1,
                   a.nodeCensus.2.1 + b.nodeCensus.2.1 + 1,
                   a.nodeCensus.2.2 + b.nodeCensus.2.2⟩
  | .sqrt e _ _ => ⟨e.nodeCensus.1 + 1, e.nodeCensus.2.1, e.nodeCensus.2.2⟩
  | .trans _ e _ _ => ⟨e.nodeCensus.1, e.nodeCensus.2.1, e.nodeCensus.2.2 + 1⟩
  | .ite c t e => ⟨c.nodeCensus.1 + t.nodeCensus.1 + e.nodeCensus.1,
                   c.nodeCensus.2.1 + t.nodeCensus.2.1 + e.nodeCensus.2.1,
                   c.nodeCensus.2.2 + t.nodeCensus.2.2 + e.nodeCensus.2.2⟩

/-- The number of `sqrt` nodes = the required `sqrtCerts` length. -/
def IExpr.nSqrt {n : ℕ} (e : IExpr n) : Nat := e.nodeCensus.1

/-! ## Baking the per-leaf `TMParams` from the mirror's triples -/

/-- Replace the template's `sqrtCerts` by the mirror's mantissa triples,
keeping the template's reciprocal granularities (`o1`/`o2` of its first
`sqrtCerts` entry — the stage-A driver's template is uniform) and its
`invCerts` / `transCerts` verbatim. -/
def bakeTMParams (tmpl : TMParams) (l : List (Int × Int × Int)) : TMParams :=
  let o := match tmpl.sqrtCerts.head? with
    | some t => (t.o1, t.o2)
    | none => ((0 : Int), (0 : Int))
  ⟨l.map (fun t => ⟨t.1, t.2.1, t.2.2, o.1, o.2⟩), tmpl.invCerts, tmpl.transCerts⟩

/-! ## The sound probe -/

/-- Result of one sound probe: the exact parameter block to emit plus the
**kernel** verdict and the kernel Taylor lower bound (diagnostics). -/
structure ProbeResult where
  /-- The `TMParams` to bake into the certificate. -/
  P : TMParams
  /-- `evalTMHullD2`'s positivity verdict on `P`. -/
  verdict : Bool
  /-- Kernel lower bound mantissa (`loM * 2^loE`). -/
  loM : Int
  /-- Kernel lower bound exponent. -/
  loE : Int
  deriving Repr

/-- **Sound stage-A probe.**  `some r` where `r.P` is the exact parameter block
to emit and `r.verdict` is the **kernel** evaluator's (`evalTMHullD2`)
positivity verdict on it; `r.loM * 2^r.loE` is the kernel Taylor lower bound.

`none` means "not a certificate": the mirror failed, or it produced a number of
`sqrt` triples different from the expression's `sqrt` node count — i.e. some
`sqrt` node went through the mirror-only dummy-slot fallback, which the kernel
cannot reproduce.  Such leaves are **rejected**, never promoted. -/
def hullProbeSound {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (tmpl : TMParams) : Option ProbeResult :=
  (evalTMHullFill2 box e tmpl).bind fun (_, _, l) =>
    if l.length = e.nSqrt then
      let P := bakeTMParams tmpl l
      match evalTMHullD2 box e P with
      | some (M, _) =>
        let lb := M.loBound box
        some ⟨P, lb.isPos, lb.m, lb.e⟩
      | none => some ⟨P, false, 0, 0⟩
    else none

/-- **The gate lemma**: a `true` verdict from `hullProbeSound` on a well-formed
box *is* a kernel `checkPosTMHull` certificate for the baked parameters.  This
is the formal content of "probe PASS ⇒ kernel PASS". -/
theorem hullProbeSound_checkPosTMHull {n : ℕ} {e : IExpr n}
    {box : Fin n → DInterval} {tmpl : TMParams} {r : ProbeResult}
    (hwf : ∀ i, (box i).wf = true)
    (h : hullProbeSound e box tmpl = some r)
    (hv : r.verdict = true) :
    checkPosTMHull e box r.P = true := by
  unfold hullProbeSound at h
  cases hF : evalTMHullFill2 box e tmpl with
  | none => rw [hF] at h; simp at h
  | some Mpl =>
  obtain ⟨M₀, ps₀, l⟩ := Mpl
  rw [hF] at h
  simp only [Option.bind_some] at h
  by_cases hlen : l.length = e.nSqrt
  · rw [if_pos hlen] at h
    cases hE : evalTMHullD2 box e (bakeTMParams tmpl l) with
    | none =>
      rw [hE] at h
      have hr : r = ⟨bakeTMParams tmpl l, false, 0, 0⟩ := (Option.some.inj h).symm
      rw [hr] at hv
      simp at hv
    | some Mp =>
      obtain ⟨M, ps⟩ := Mp
      rw [hE] at h
      have hr : r = ⟨bakeTMParams tmpl l, (M.loBound box).isPos,
          (M.loBound box).m, (M.loBound box).e⟩ := (Option.some.inj h).symm
      rw [hr] at hv ⊢
      unfold checkPosTMHull
      simp only [Bool.and_eq_true, List.all_eq_true]
      refine ⟨fun i _ => hwf i, ?_⟩
      rw [hE]
      simpa using hv
  · rw [if_neg hlen] at h
    simp at h

end Kepler.Interval

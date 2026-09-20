/-
  Phase 4, G4: **Bool-valued cover checker** for branch-and-bound certificates.

  `Kepler.Interval.Cert` defines the `Prop`-level `BBTree.covers` /
  `splitOK`, whose concrete instances are tedious to prove by hand
  (the `∀ i, i ≠ d → …` component has no `Decidable` instance in scope).
  For machine-generated certificates we want a *single* kernel `decide`
  over the whole tree.  This file provides the Bool-valued mirrors

  - `splitOKB` — split certificate as a `Bool` computation
    (endpoint equalities via `decide` on decidable props, the ∀-part as a
    fold over `List.finRange n`);
  - `BBTree.coversB` — recursive Bool cover checker;

  plus their soundness bridges to the `Prop` forms.  No new axioms, no
  `native_decide`; the checking layer stays in `Int` comparisons.
-/
import Kepler.Interval.Cert
import Kepler.Interval.CertDisj

namespace Kepler.Interval

/-- Bool-valued split certificate: `bl`/`br` are the exact dyadic halves of
`box` along `d` (mirrors `splitOK`; all comparisons are decidable). -/
def splitOKB {n : ℕ} (box : Fin n → DInterval) (d : Fin n)
    (bl br : Fin n → DInterval) : Bool :=
  ((List.finRange n).all fun i =>
      decide (i ≠ d → bl i = box i ∧ br i = box i)) &&
    decide ((bl d).lo = (box d).lo ∧ (bl d).hi = (box d).mid ∧
      (br d).lo = (box d).mid ∧ (br d).hi = (box d).hi)

/-- **Soundness of `splitOKB`**: a passing Bool check yields the `Prop`
split certificate. -/
theorem splitOKB_sound {n : ℕ} {box : Fin n → DInterval} {d : Fin n}
    {bl br : Fin n → DInterval} (h : splitOKB box d bl br = true) :
    splitOK box d bl br := by
  simp only [splitOKB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h2' := of_decide_eq_true h2
  refine ⟨?_, h2'.1, h2'.2.1, h2'.2.2.1, h2'.2.2.2⟩
  intro i hi
  have hi2 := h1 i (List.mem_finRange i)
  exact of_decide_eq_true hi2 hi

namespace BBTree

/-- Bool-valued cover checker (mirrors `covers`): every internal node's
children are its exact halves, recursively. -/
def coversB {n : ℕ} {e : IExpr n} : BBTree n e → Bool
  | .leaf _ _ => true
  | .node b d l r => Bool.and (splitOKB b d l.box r.box) (Bool.and (coversB l) (coversB r))

/-- **Soundness of `coversB`**: a passing Bool check yields the `Prop`
cover certificate. -/
theorem coversB_sound {n : ℕ} {e : IExpr n} (t : BBTree n e)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b hcert => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

end BBTree

namespace BBTreeD

/-- Bool-valued cover checker for disjunctive trees (mirrors `BBTreeD.covers`;
same box-splitting layer as `BBTree.coversB`). -/
def coversB {n : ℕ} {goals : List (DisjGoal n)} : BBTreeD n goals → Bool
  | .leaf _ _ _ => true
  | .node b d l r => Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `BBTreeD.coversB`**: a passing Bool check yields the
`Prop` cover certificate. -/
theorem coversB_sound {n : ℕ} {goals : List (DisjGoal n)} (t : BBTreeD n goals)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b k hcert => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

end BBTreeD

/-! ## Pilot: the two-leaf bisection of `Cert.lean`, checked by one `decide` -/

/-- The whole covering structure of `Cert.exTree` is verified by a single
kernel `decide` through the Bool checker. -/
theorem exTree_coversB : exTree.coversB = true := by decide

/-- … and bridges to the `Prop` form. -/
theorem exTree_covers_via_B : exTree.covers := BBTree.coversB_sound _ exTree_coversB

end Kepler.Interval

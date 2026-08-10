/-
Generic worklist-layer for the certificate checker: a fuel-bounded worklist
loop over `succs : Graph → List Graph`, plus pure kernel proofs that a
`some true` result certifies `check` on the whole `RTranCl` closure of the
initial worklist.

This file is a pure kernel proof layer; the fuel truncation is
justified separately (see DECISIONS.md, 2026-08-10).
-/

import Kepler.Graphs.PlaneProps

namespace Kepler.Graphs

/-- Fuel-bounded worklist loop: pop x, require `check x`, prepend `succs x`.
No dedup on purpose: exact-duplicate pops are empirically ~0 for this
enumerator, and the closure proof stays trivial. -/
def loop (succs : Graph → List Graph) (check : Graph → Bool) :
    Nat → List Graph → Option Bool
  | 0, _ => none
  | _ + 1, [] => some true
  | fuel + 1, x :: work =>
      if check x then loop succs check fuel (succs x ++ work) else some false

/-- Single-step left peeling of `RTranCl`: either the target is the source
itself, or the path goes through a one-step successor. -/
private theorem RTranCl_head {succs : Graph → List Graph} {x g : Graph}
    (h : RTranCl succs x g) :
    g = x ∨ ∃ y ∈ succs x, RTranCl succs y g := by
  cases h with
  | refl => exact Or.inl rfl
  | succs hy hr => exact Or.inr ⟨_, hy, hr⟩

/-- Core closure theorem: if the fuel-bounded loop returns `some true`,
then `check` holds on every graph reachable (`RTranCl`) from the initial
worklist. -/
theorem loop_some_true {succs : Graph → List Graph} {check : Graph → Bool}
    {fuel : Nat} {ws : List Graph}
    (h : loop succs check fuel ws = some true) :
    ∀ g, (∃ w ∈ ws, RTranCl succs w g) → check g = true := by
  induction fuel generalizing ws with
  | zero => simp [loop] at h
  | succ fuel ih =>
    cases ws with
    | nil =>
      intro g hg
      obtain ⟨w, hw, _⟩ := hg
      simp at hw
    | cons x work =>
      rw [loop] at h
      cases hcx : check x with
      | false => rw [hcx] at h; simp at h
      | true =>
        rw [hcx] at h
        simp only [ite_true] at h
        intro g hg
        obtain ⟨w, hw, hr⟩ := hg
        rcases List.mem_cons.mp hw with rfl | hw'
        · -- w = x: peel one step off `RTranCl succs x g`
          rcases RTranCl_head hr with rfl | ⟨y, hy, hr'⟩
          · exact hcx
          · exact ih h g ⟨y, List.mem_append_left work hy, hr'⟩
        · exact ih h g ⟨w, List.mem_append_right _ hw', hr⟩

/-- One-step right extension of `RTranCl` (the `succs` constructor prepends,
so extending at the end needs induction on the path). -/
private theorem RTranCl_succs_right {succs : Graph → List Graph} {a b c : Graph}
    (hr : RTranCl succs a b) (hc : c ∈ succs b) : RTranCl succs a c := by
  induction hr with
  | refl => exact RTranCl.succs hc RTranCl.refl
  | succs hy _ ih => exact RTranCl.succs hy (ih hc)

/-- Frontier cut: if `S` is closed under `succs` up to a frontier `F`, then
every graph reachable from a seed `s0 ∈ S` either lies in `S` or is reachable
from a frontier element. Used to glue sharded enumeration runs. -/
theorem frontier_cut {succs : Graph → List Graph} (S F : List Graph)
    {s0 : Graph} (hseed : s0 ∈ S)
    (hclosed : ∀ x ∈ S, ∀ c ∈ succs x, c ∈ S ∨ c ∈ F)
    {g : Graph} (hr : RTranCl succs s0 g) :
    g ∈ S ∨ ∃ h ∈ F, RTranCl succs h g := by
  refine RTranCl_induct (P := fun g => g ∈ S ∨ ∃ h ∈ F, RTranCl succs h g)
    hr (Or.inl hseed) ?_
  intro a c hca ha
  rcases ha with haS | ⟨h, hF, hh⟩
  · rcases hclosed a haS c hca with hcS | hcF
    · exact Or.inl hcS
    · exact Or.inr ⟨c, hcF, RTranCl.refl⟩
  · exact Or.inr ⟨h, hF, RTranCl_succs_right hh hca⟩

end Kepler.Graphs

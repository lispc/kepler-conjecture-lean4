/-
Contingency splitting lemmas for the worklist loop (not yet used by any
certificate).  If a single frontier root's closure exceeds the fuel cap of
its shard file, these lemmas allow splitting that root into its children:
each child gets its own shard, and the results are re-assembled into a
certificate for the parent root.  Pure kernel proofs; no `native_decide`.
-/

import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Monotonicity in fuel: a successful run stays successful with more fuel. -/
theorem loop_mono {succs : Graph → List Graph} {check : Graph → Bool}
    {fuel : Nat} {ws : List Graph}
    (h : loop succs check fuel ws = some true) (k : Nat) :
    loop succs check (fuel + k) ws = some true := by
  induction fuel generalizing ws with
  | zero => simp [loop] at h
  | succ fuel ih =>
    cases ws with
    | nil =>
      have : fuel + 1 + k = fuel + k + 1 := by omega
      rw [this, loop]
    | cons x work =>
      rw [loop] at h
      cases hcx : check x with
      | false => rw [hcx] at h; simp at h
      | true =>
        rw [hcx] at h
        have : fuel + 1 + k = fuel + k + 1 := by omega
        rw [this, loop, hcx]
        exact ih h

/-- Append: closures of two worklists combine, with fuel adding up. -/
theorem loop_append {succs : Graph → List Graph} {check : Graph → Bool}
    {fuel1 fuel2 : Nat} {ws1 ws2 : List Graph}
    (h1 : loop succs check fuel1 ws1 = some true)
    (h2 : loop succs check fuel2 ws2 = some true) :
    loop succs check (fuel1 + fuel2) (ws1 ++ ws2) = some true := by
  induction fuel1 generalizing ws1 with
  | zero => simp [loop] at h1
  | succ fuel1 ih =>
    cases ws1 with
    | nil =>
      have : fuel1 + 1 + fuel2 = fuel2 + (fuel1 + 1) := by omega
      rw [this]; exact loop_mono h2 _
    | cons x work =>
      rw [loop] at h1
      cases hcx : check x with
      | false => rw [hcx] at h1; simp at h1
      | true =>
        rw [hcx] at h1
        simp only [ite_true] at h1
        have : fuel1 + 1 + fuel2 = fuel1 + fuel2 + 1 := by omega
        rw [List.cons_append, this, loop, hcx]
        simp only [ite_true]
        rw [← List.append_assoc]
        exact ih h1

/-- List version: if every element of `cs` closes (with its own fuel),
then the whole list closes. -/
theorem loop_list_of_forall {succs : Graph → List Graph} {check : Graph → Bool}
    (cs : List Graph) (h : ∀ c ∈ cs, ∃ fuel, loop succs check fuel [c] = some true) :
    ∃ fuel, loop succs check fuel cs = some true := by
  induction cs with
  | nil => exact ⟨1, rfl⟩
  | cons x xs ih =>
    obtain ⟨f1, h1⟩ := h x List.mem_cons_self
    obtain ⟨f2, h2⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    exact ⟨f1 + f2, loop_append h1 h2⟩

/-- Split a root into its children: if `check r` holds and every child
closes, then `[r]` closes. -/
theorem loop_singleton_of_children {succs : Graph → List Graph} {check : Graph → Bool}
    {r : Graph} (hr : check r = true)
    (h : ∀ c ∈ succs r, ∃ fuel, loop succs check fuel [c] = some true) :
    ∃ fuel, loop succs check fuel [r] = some true := by
  obtain ⟨F, hF⟩ := loop_list_of_forall (succs r) h
  refine ⟨F + 1, ?_⟩
  rw [loop, hr]
  simp only [ite_true, List.append_nil]
  exact hF

end Kepler.Graphs

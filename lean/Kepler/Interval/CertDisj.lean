/-
  Phase 4, G4: **disjunctive branch-and-bound certificates**.

  `Kepler.Interval.Cert` proves positivity `0 < e.evalReal ρ` from a bisection
  tree whose leaves pass `checkPos e box`.  But 58 of the 176 Flyspeck
  nonlinear records are *disjunctions* (`e₀ > 0 ∨ e₁ > 0 ∨ …`, or include a
  pure variable ordering `yᵢ < yⱼ`), which `emit_rpn.py` records in the
  `disj` field.  This file generalises the certificate to a disjunctive goal
  list.

  ## Design

  - `DisjGoal n` is one disjunct: either `pos e` (`0 < e.evalReal ρ`) or
    `varLt i j` (`ρ i < ρ j`).
  - `DisjGoal.check box` is the kernel-decidable leaf test: `checkPos e box`
    for `pos e`, or `Dyadic.blt (box i).hi (box j).lo` for `varLt i j`
    (the whole box satisfies the ordering).
  - `DisjGoal.check_sound` turns a passing leaf test into the real-valued
    disjunct.
  - `BBTreeD n goals` is the bisection tree over the *same* exact-dyadic
    splitting as `Cert.BBTree`, but a leaf carries an index `k : Fin
    goals.length` into the goal list together with the checked certificate of
    `goals.get k`.
  - `bb_sound_disj`: a covering tree whose root contains the target box yields
    `∃ g ∈ goals, g.eval ρ` for every `ρ` in the target.

  Kernel checks only: no `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.Cert

namespace Kepler.Interval

/-- One disjunct of a disjunctive nonlinear goal. -/
inductive DisjGoal (n : ℕ) : Type where
  | pos (e : IExpr n) : DisjGoal n
  | varLt (i j : Fin n) : DisjGoal n
  deriving Repr

namespace DisjGoal

/-- Real semantics of a disjunct. -/
noncomputable def eval {n : ℕ} : DisjGoal n → (Fin n → ℝ) → Prop
  | .pos e, ρ => 0 < e.evalReal ρ
  | .varLt i j, ρ => ρ i < ρ j

/-- Kernel-decidable leaf test for a disjunct on a box. -/
def check {n : ℕ} : DisjGoal n → (Fin n → DInterval) → Bool
  | .pos e, box => checkPos e box
  | .varLt i j, box => Dyadic.blt (box i).hi (box j).lo

/-- Soundness of the leaf test. -/
theorem check_sound {n : ℕ} (g : DisjGoal n) (box : Fin n → DInterval)
    (h : g.check box = true) (ρ : Fin n → ℝ) (hρ : boxMem box ρ) : g.eval ρ := by
  cases g with
  | pos e => exact checkPos_sound e box h ρ hρ
  | varLt i j =>
    exact lt_of_le_of_lt (hρ i).2
      (lt_of_lt_of_le (Dyadic.blt_toReal h) (hρ j).1)

end DisjGoal

/-- Disjunctive bisection tree: leaves carry a checked disjunct, internal
nodes carry the exact-dyadic split (same shape as `Cert.BBTree`). -/
inductive BBTreeD (n : ℕ) (goals : List (DisjGoal n)) : Type where
  | leaf (box : Fin n → DInterval) (k : Fin goals.length)
      (hcert : (goals.get k).check box = true) : BBTreeD n goals
  | node (box : Fin n → DInterval) (d : Fin n) (l r : BBTreeD n goals) : BBTreeD n goals

namespace BBTreeD

/-- The box of a node (root included). -/
def box {n : ℕ} {goals : List (DisjGoal n)} : BBTreeD n goals → (Fin n → DInterval)
  | .leaf b _ _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop-level): every internal node's children are its
exact halves, recursively. -/
def covers {n : ℕ} {goals : List (DisjGoal n)} : BBTreeD n goals → Prop
  | .leaf _ _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- **Point-coverage**: a covering disjunctive tree places every real point of
its own box inside some leaf (with that leaf's checked disjunct). -/
theorem covers_point {n : ℕ} {goals : List (DisjGoal n)} (t : BBTreeD n goals)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval) (k : Fin goals.length),
      (goals.get k).check box = true ∧ boxMem box ρ := by
  induction t with
  | leaf box k hcert => exact ⟨box, k, hcert, hρ⟩
  | node box d l r ihl ihr =>
    obtain ⟨hsplit, hlcov, hrcov⟩ := hcov
    by_cases hcase : ρ d ≤ (box d).mid.toReal
    · have hρl : boxMem l.box ρ := by
        intro i
        by_cases hid : i = d
        · subst hid
          constructor
          · show (l.box i).lo.toReal ≤ ρ i
            rw [hsplit.2.1]
            exact (hρ i).1
          · show ρ i ≤ (l.box i).hi.toReal
            rw [hsplit.2.2.1]
            exact hcase
        · have hli : l.box i = box i := (hsplit.1 i hid).1
          rw [hli]
          exact hρ i
      exact ihl hlcov hρl
    · have hρr : boxMem r.box ρ := by
        intro i
        by_cases hid : i = d
        · subst hid
          constructor
          · show (r.box i).lo.toReal ≤ ρ i
            rw [hsplit.2.2.2.1]
            exact le_of_lt (lt_of_not_ge hcase)
          · show ρ i ≤ (r.box i).hi.toReal
            rw [hsplit.2.2.2.2]
            exact (hρ i).2
        · have hri : r.box i = box i := (hsplit.1 i hid).2
          rw [hri]
          exact hρ i
      exact ihr hrcov hρr

end BBTreeD

/-- **Soundness of disjunctive branch-and-bound certificates**: a covering
tree whose root contains the target box proves the disjunction at every point
of the target. -/
theorem bb_sound_disj {n : ℕ} {goals : List (DisjGoal n)} (t : BBTreeD n goals)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) :
    ∃ g ∈ goals, g.eval ρ := by
  obtain ⟨box, k, hcert, hmem⟩ := t.covers_point hcov (boxSub_mem hsub hρ)
  exact ⟨goals.get k, List.get_mem _ _, DisjGoal.check_sound _ box hcert ρ hmem⟩

/-! ## Pilot: disjunction `x > 1 ∨ x < 0` on `[2,3]` (first disjunct hits) -/

/-- Goals: `pos (x - 1)` then `pos (-x)`. -/
def exGoalsDisj : List (DisjGoal 1) :=
  [.pos (.sub (.var 0) (.const ⟨1, 0⟩)), .pos (.neg (.var 0))]

/-- Box `[2,3]`. -/
def exBoxDisj : Fin 1 → DInterval := fun _ => ⟨⟨2, 0⟩, ⟨3, 0⟩⟩

/-- Leaf certificate for the first disjunct (`x - 1 > 0` on `[2,3]`). -/
theorem exGoal0_check : (exGoalsDisj.get ⟨0, by decide⟩).check exBoxDisj = true := by
  decide

/-- The one-leaf disjunctive tree. -/
def exTreeDisj : BBTreeD 1 exGoalsDisj :=
  .leaf exBoxDisj ⟨0, by decide⟩ exGoal0_check

/-- Covering is trivial for a leaf. -/
theorem exTreeDisj_covers : exTreeDisj.covers := trivial

/-- End-to-end: `0 < x - 1 ∨ 0 < -x` for every `x ∈ [2,3]`. -/
theorem exDisj_end_to_end (x : ℝ) (hx1 : 2 ≤ x) (hx2 : x ≤ 3) :
    0 < x - 1 ∨ 0 < -x := by
  have hmem : ∀ i : Fin 1, (exBoxDisj i).mem ((fun _ => x) i) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨2, 0⟩ ≤ x
      rw [Dyadic.toReal_int]
      exact_mod_cast hx1
    · show x ≤ Dyadic.toReal ⟨3, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  have hsub : boxSub exBoxDisj exTreeDisj.box := by
    intro i
    fin_cases i
    constructor <;> decide
  obtain ⟨g, hgmem, hg⟩ :=
    bb_sound_disj exTreeDisj exBoxDisj exTreeDisj_covers hsub (fun _ => x) hmem
  simp only [exGoalsDisj] at hgmem
  simp at hgmem
  rcases hgmem with rfl | rfl
  · left
    simpa [DisjGoal.eval, IExpr.evalReal, Dyadic.toReal_def] using hg
  · right
    simpa [DisjGoal.eval, IExpr.evalReal, Dyadic.toReal_def] using hg

end Kepler.Interval

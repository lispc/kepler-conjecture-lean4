/-
  Phase 4, G4 (wave 2, design D1): **hybrid disjunctive/generalised
  branch-and-bound certificates** (`BBTreeGD` = `BBTreeG` × `BBTreeD`).

  `BBTreeD` (CertDisj) covers disjunctive goals, but its leaf references the
  *global* goal expression `(goals.get k)` directly — there is no per-leaf
  parameter slot, so a hit `pos` branch containing certificate-parameterised
  nodes (`.sqrt e s₁ s₂`, `.trans k e …`) cannot be certified leaf-by-leaf.
  `BBTreeG` (CertG) has the per-leaf specialisation mechanism (`el` +
  `hsame : el.evalReal = e.evalReal`, closed by `rfl` since `evalReal`
  ignores certificate parameters) but only for a single global expression.

  `BBTreeGD` combines both: each leaf is one of

  - `posLeaf box k e el hk hsame hcert` — the hit disjunct is `pos e`
    (`hk : goals.get k = .pos e`), and the leaf carries a *specialised*
    expression `el` with the same real semantics (`hsame`) whose parameters
    are filled per-leaf, plus the kernel check `checkPos el box = true`;
  - `varLtLeaf box k hcert` — the hit disjunct is checked by the plain box
    test (`DisjGoal.check`, i.e. `Dyadic.blt (box i).hi (box j).lo`); no
    parameter slot is needed.

  Internal nodes are exactly as in `Cert.BBTree` (box + split dimension).

  Soundness (`bb_sound_disjG`): a covering tree whose root contains the
  target box yields `∃ g ∈ goals, g.eval ρ` at every point of the target —
  the proof is the `BBTreeG` per-leaf bridge spliced into the `BBTreeD`
  disjunction collection, no new mathematics.

  Kernel checks only: no `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.CertBool

namespace Kepler.Interval

/-- Hybrid disjunctive bisection tree with per-leaf specialised expressions
on the `pos` branches. -/
inductive BBTreeGD (n : ℕ) (goals : List (DisjGoal n)) : Type where
  /-- `pos` branch hit: the disjunct `goals.get k` is `.pos e`, and the leaf
  carries a specialised `el` (same real semantics, per-leaf certificate
  parameters) passing `checkPos`. -/
  | posLeaf (box : Fin n → DInterval) (k : Fin goals.length) (e el : IExpr n)
      (hk : goals.get k = .pos e)
      (hsame : el.evalReal = e.evalReal)
      (hcert : checkPos el box = true) : BBTreeGD n goals
  /-- `varLt` branch hit: the disjunct `goals.get k` is certified directly by
  the box test `DisjGoal.check` (no parameters needed). -/
  | varLtLeaf (box : Fin n → DInterval) (k : Fin goals.length)
      (hcert : (goals.get k).check box = true) : BBTreeGD n goals
  | node (box : Fin n → DInterval) (d : Fin n) (l r : BBTreeGD n goals) :
      BBTreeGD n goals

namespace BBTreeGD

/-- The box of a node (root included). -/
def box {n : ℕ} {goals : List (DisjGoal n)} : BBTreeGD n goals → (Fin n → DInterval)
  | .posLeaf b _ _ _ _ _ _ => b
  | .varLtLeaf b _ _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop-level), same shape as `BBTreeD.covers`. -/
def covers {n : ℕ} {goals : List (DisjGoal n)} : BBTreeGD n goals → Prop
  | .posLeaf _ _ _ _ _ _ _ => True
  | .varLtLeaf _ _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- **Point-coverage**: a covering tree places every real point of its own
box inside some leaf whose checked disjunct holds at that point. -/
theorem covers_point {n : ℕ} {goals : List (DisjGoal n)} (t : BBTreeGD n goals)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval) (k : Fin goals.length),
      boxMem box ρ ∧ (goals.get k).eval ρ := by
  induction t with
  | posLeaf box k e el hk hsame hcert =>
    refine ⟨box, k, hρ, ?_⟩
    rw [hk]
    show 0 < e.evalReal ρ
    rw [← hsame]
    exact checkPos_sound el box hcert ρ hρ
  | varLtLeaf box k hcert =>
    exact ⟨box, k, hρ, DisjGoal.check_sound _ box hcert ρ hρ⟩
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

/-- Bool-valued cover checker (same shape as `BBTreeG.coversB`): one kernel
`decide` over the whole tree. -/
def coversB {n : ℕ} {goals : List (DisjGoal n)} : BBTreeGD n goals → Bool
  | .posLeaf _ _ _ _ _ _ _ => true
  | .varLtLeaf _ _ _ => true
  | .node b d l r => Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `coversB`**. -/
theorem coversB_sound {n : ℕ} {goals : List (DisjGoal n)} (t : BBTreeGD n goals)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | posLeaf b k e el hk hsame hcert => trivial
  | varLtLeaf b k hcert => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

end BBTreeGD

/-- **Soundness of hybrid disjunctive branch-and-bound certificates**: a
covering tree whose root contains the target box proves the disjunction at
every point of the target. -/
theorem bb_sound_disjG {n : ℕ} {goals : List (DisjGoal n)} (t : BBTreeGD n goals)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) :
    ∃ g ∈ goals, g.eval ρ := by
  obtain ⟨box, k, hmem, heval⟩ := t.covers_point hcov (boxSub_mem hsub hρ)
  exact ⟨goals.get k, List.get_mem _ _, heval⟩

/-! ## Pilot: a mixed two-leaf tree (specialised `pos` leaf + `varLt` leaf)

Goals: `√x − x/4 > 0` (certificate-parameterised) or `x < y`, over
`[1,2] × [3,4]`.  The bisection splits `x` at `3/2`; the left leaf certifies
the positivity branch with per-leaf sqrt mantissas (as in `CertG`), the
right leaf certifies `x < y` by the pure box test (`2 < 3`).  The covering
structure is verified by a single kernel `decide` via `coversB`. -/

/-- The global `pos` expression `√x − x/4` (dummy sqrt parameters;
`evalReal` ignores them). -/
def exGDPosExpr : IExpr 2 :=
  .sub (.sqrt (.var 0) 0 0) (.div (.var 0) (.const ⟨4, 0⟩) (-64))

/-- Goals: positivity of `√x − x/4`, or the variable ordering `x < y`. -/
def exGDGoals : List (DisjGoal 2) := [.pos exGDPosExpr, .varLt 0 1]

/-- Root box `[1,2] × [3,4]` and its halves along dimension 0. -/
def exGDBox : Fin 2 → DInterval := ![⟨⟨1, 0⟩, ⟨2, 0⟩⟩, ⟨⟨3, 0⟩, ⟨4, 0⟩⟩]
def exGDBoxL : Fin 2 → DInterval := ![⟨⟨1, 0⟩, ⟨3, -1⟩⟩, ⟨⟨3, 0⟩, ⟨4, 0⟩⟩]
def exGDBoxR : Fin 2 → DInterval := ![⟨⟨3, -1⟩, ⟨2, 0⟩⟩, ⟨⟨3, 0⟩, ⟨4, 0⟩⟩]

/-- Left leaf `[1, 3/2]`: specialised sqrt mantissas `1 = ⌊√1⌋`,
`2 = ⌊√6⌋` (`3/2 = ⟨3,-1⟩` scales to `3·2 = 6`), as in `CertG`. -/
def exGDLeafL : IExpr 2 :=
  .sub (.sqrt (.var 0) 1 2) (.div (.var 0) (.const ⟨4, 0⟩) (-64))

/-- The specialised expression has the same real semantics as the global one
(definitionally — only certificate parameters differ). -/
theorem exGDLeafL_same : exGDLeafL.evalReal = exGDPosExpr.evalReal := rfl

/-- Left leaf certificate: on `[1, 3/2] × [3,4]`, `√x − x/4` has lo > 0. -/
theorem exGDLeafL_cert : checkPos exGDLeafL exGDBoxL = true := by decide

/-- Right leaf certificate: the whole box satisfies `x < y` (`2 < 3`). -/
theorem exGDVarLt_cert : (exGDGoals.get ⟨1, by decide⟩).check exGDBoxR = true := by
  decide

/-- The two-leaf hybrid tree. -/
def exGDTree : BBTreeGD 2 exGDGoals :=
  .node exGDBox 0
    (.posLeaf exGDBoxL ⟨0, by decide⟩ exGDPosExpr exGDLeafL rfl exGDLeafL_same exGDLeafL_cert)
    (.varLtLeaf exGDBoxR ⟨1, by decide⟩ exGDVarLt_cert)

/-- Covering via the Bool checker, one `decide`. -/
theorem exGDTree_covers : exGDTree.covers :=
  BBTreeGD.coversB_sound _ (by decide)

/-- End-to-end: `0 < √x − x/4 ∨ x < y` for every `(x, y) ∈ [1,2] × [3,4]`. -/
theorem exGD_end_to_end (ρ : Fin 2 → ℝ) (hρ : boxMem exGDBox ρ) :
    0 < Real.sqrt (ρ 0) - ρ 0 / 4 ∨ ρ 0 < ρ 1 := by
  have hsub : boxSub exGDBox exGDTree.box := by
    intro i
    fin_cases i <;> exact ⟨by decide, by decide⟩
  obtain ⟨g, hgmem, hg⟩ := bb_sound_disjG exGDTree exGDBox exGDTree_covers hsub ρ hρ
  simp only [exGDGoals] at hgmem
  simp at hgmem
  rcases hgmem with rfl | rfl
  · left
    have hsimp : exGDPosExpr.evalReal ρ = Real.sqrt (ρ 0) - ρ 0 / 4 := by
      simp only [exGDPosExpr, IExpr.evalReal]
      rw [Dyadic.toReal_int]
      norm_num
    simpa only [DisjGoal.eval, hsimp] using hg
  · right
    exact hg

#print axioms bb_sound_disjG
#print axioms exGD_end_to_end

end Kepler.Interval

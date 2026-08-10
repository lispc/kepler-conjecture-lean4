/-
Generic certificate-checker layer: hash bucketing of the archive plus the
`checkFinal` worklist predicate and its correctness proof.

This file is a pure kernel proof layer: no native evaluation, no holes, no
new axioms.  The evaluation-side certificates live in `CertTri.lean` etc.
(see DECISIONS.md, 2026-08-10).

Source correspondence:
- `reference/afp-flyspeck-tame/ArchCompAux.thy` lines 17–27 (`nof_vertices`,
  `hash`; `qsort` is replaced by `List.mergeSort`) and lines 44–46
  (`pre_iso_test`).
-/
import Kepler.Graphs.RelativeCompleteness

namespace Kepler.Graphs

/-! ### Hash (ArchCompAux.thy L17–27) -/

/-- ArchCompAux.thy: `nof_vertices` (`length ∘ remdups ∘ concat`). -/
def nofVertices (fs : fgraph Nat) : Nat := fs.flatten.eraseDups.length

/-- ArchCompAux.thy: `hash` (`qsort` replaced by `List.mergeSort`,
descending).  No correctness proof is needed: the same function is used for
building and querying buckets. -/
def graphHash (fs : fgraph Nat) : List Nat :=
  let n := nofVertices fs
  [n, fs.length] ++ ((List.range n).map fun i =>
    ((fs.filter fun f => i ∈ f).map List.length).sum).mergeSort (fun a b => b ≤ a)

/-! ### Boolean `pre_iso_test` and reflection -/

/-- Boolean counterpart of `pre_iso_test` (ArchCompAux.thy L44–46). -/
def preIsoTestB (Fs : fgraph Nat) : Bool :=
  decide ([] ∉ Fs) && Fs.all (fun F => decide F.Nodup) &&
    decide (Fs.map rotate_min).Nodup

/-- Reflection: the Boolean test implies the propositional `pre_iso_test`. -/
theorem preIsoTestB_correct {Fs : fgraph Nat} (h : preIsoTestB Fs = true) :
    pre_iso_test Fs := by
  simp only [preIsoTestB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ### Buckets -/

/-- Insert `a` into the bucket with key `h` (creating it if absent). -/
def insertBucket (h : List Nat) (a : fgraph Nat) :
    List (List Nat × List (fgraph Nat)) → List (List Nat × List (fgraph Nat))
  | [] => [(h, [a])]
  | (h', l) :: rest =>
      if h' == h then (h', a :: l) :: rest else (h', l) :: insertBucket h a rest

/-- Bucket `xs` by `graphHash`. -/
def buildBuckets : List (fgraph Nat) → List (List Nat × List (fgraph Nat))
  | [] => []
  | a :: xs => insertBucket (graphHash a) a (buildBuckets xs)

/-- Looking up the just-inserted key returns the element prepended to the
previous bucket contents. -/
theorem lookup_insertBucket_same (h : List Nat) (a : fgraph Nat)
    (acc : List (List Nat × List (fgraph Nat))) :
    (insertBucket h a acc).lookup h = some (a :: (acc.lookup h).getD []) := by
  induction acc with
  | nil => simp [insertBucket]
  | cons p rest ih =>
    obtain ⟨h', l⟩ := p
    rw [insertBucket]
    cases hbeq : (h' == h) with
    | true =>
      have hh : h' = h := eq_of_beq hbeq
      subst hh
      simp [List.lookup_cons]
    | false =>
      have hsym : (h == h') = false :=
        beq_eq_false_iff_ne.mpr (fun e => beq_eq_false_iff_ne.mp hbeq e.symm)
      simp [List.lookup_cons, hbeq, hsym, ih]

/-- Looking up a different key is unaffected by the insertion. -/
theorem lookup_insertBucket_of_ne {k h : List Nat} (hne : k ≠ h) (a : fgraph Nat)
    (acc : List (List Nat × List (fgraph Nat))) :
    (insertBucket h a acc).lookup k = acc.lookup k := by
  induction acc with
  | nil =>
    have hk : (k == h) = false := beq_eq_false_iff_ne.mpr hne
    simp [insertBucket, List.lookup_cons, hk]
  | cons p rest ih =>
    obtain ⟨h', l⟩ := p
    rw [insertBucket]
    cases hbeq : (h' == h) with
    | true =>
      have hh : h' = h := eq_of_beq hbeq
      have hk : (k == h') = false := beq_eq_false_iff_ne.mpr (fun e => hne (e.trans hh))
      simp [List.lookup_cons, hbeq, hk]
    | false =>
      have hsym : (h == h') = false :=
        beq_eq_false_iff_ne.mpr (fun e => beq_eq_false_iff_ne.mp hbeq e.symm)
      cases hkeq : (k == h') with
      | true => simp [List.lookup_cons, hbeq, hkeq]
      | false => simp [List.lookup_cons, hbeq, hkeq, ih]

/-- Every element of every bucket came from the input list. -/
theorem mem_of_lookup_buildBuckets {xs : List (fgraph Nat)} {h : List Nat}
    {l : List (fgraph Nat)} {a : fgraph Nat}
    (hlk : (buildBuckets xs).lookup h = some l) (ha : a ∈ l) : a ∈ xs := by
  induction xs generalizing l a with
  | nil => simp [buildBuckets] at hlk
  | cons x xs ih =>
    rw [buildBuckets] at hlk
    by_cases heq : h = graphHash x
    · subst heq
      rw [lookup_insertBucket_same] at hlk
      have e := Option.some.inj hlk
      subst e
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact List.mem_cons_self
      · cases hlk' : (buildBuckets xs).lookup (graphHash x) with
        | none => rw [hlk'] at ha'; simp at ha'
        | some l' =>
          rw [hlk'] at ha'
          simp only [Option.getD_some] at ha'
          exact List.mem_cons_of_mem _ (ih hlk' ha')
    · rw [lookup_insertBucket_of_ne heq] at hlk
      exact List.mem_cons_of_mem _ (ih hlk ha)

/-- Every input element lands in the bucket of its own hash. -/
theorem lookup_buildBuckets_of_mem {xs : List (fgraph Nat)} {a : fgraph Nat}
    (ha : a ∈ xs) : ∃ l, (buildBuckets xs).lookup (graphHash a) = some l ∧ a ∈ l := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [buildBuckets]
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, lookup_insertBucket_same _ _ _, List.mem_cons_self⟩
    · obtain ⟨l, hlk, hal⟩ := ih ha'
      by_cases heq : graphHash a = graphHash x
      · rw [heq] at hlk ⊢
        rw [lookup_insertBucket_same, hlk]
        exact ⟨x :: l, rfl, List.mem_cons_of_mem _ hal⟩
      · rw [lookup_insertBucket_of_ne heq]
        exact ⟨l, hlk, hal⟩

/-! ### `checkFinal` -/

/-- Worklist predicate: non-final graphs pass; final graphs must have a
`preIsoTestB`-passing fgraph isomorphic to some archive entry of the same
hash bucket. -/
def checkFinal (buckets : List (List Nat × List (fgraph Nat))) (g : Graph) : Bool :=
  !g.final || (preIsoTestB g.fgraph &&
    match buckets.lookup (graphHash g.fgraph) with
    | some l => l.any (fun a => iso_test g.fgraph a)
    | none => false)

/-- Correctness: a final graph passing `checkFinal` against the buckets of
`arch` is isomorphic to some member of `arch`. -/
theorem checkFinal_correct {arch : List (fgraph Nat)} {g : Graph}
    (harch : ∀ a ∈ arch, pre_iso_test a)
    (hg : checkFinal (buildBuckets arch) g = true) (hfin : g.final = true) :
    ∃ a ∈ arch, g.fgraph ≃ a := by
  simp only [checkFinal, hfin, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg
  obtain ⟨hpre, hany⟩ := hg
  have hpreP : pre_iso_test g.fgraph := preIsoTestB_correct hpre
  split at hany
  next l hlk =>
    rw [List.any_eq_true] at hany
    obtain ⟨a, hal, hiso⟩ := hany
    have ha : a ∈ arch := mem_of_lookup_buildBuckets hlk hal
    exact ⟨a, ha, (iso_test_correct hpreP (harch a ha)).mp hiso⟩
  next => simp at hany

end Kepler.Graphs

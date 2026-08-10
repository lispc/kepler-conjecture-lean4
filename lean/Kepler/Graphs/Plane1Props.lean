/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Plane1Props.thy`.

Source: `reference/afp-flyspeck-tame/Plane1Props.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Also includes `RTranCl_subset2` (RTranCl.thy), needed here and by the
final Completeness assembly.
-/
import Kepler.Graphs.Plane1
import Kepler.Graphs.PlaneProps
import Kepler.Graphs.TameProps

namespace Kepler.Graphs

/-- Plane1Props.thy: next_plane_subset. The set inclusion is rendered as a
membership implication (project convention). -/
theorem next_plane_subset {p : Nat} {g : Graph}
    (h : ∀ f ∈ g.faces, f.vertices ≠ []) {g' : Graph}
    (hg' : g' ∈ next_plane p g) : g' ∈ next_plane0 p g := by
  have hfs : nonFinals g ≠ [] := by
    intro hfs
    unfold next_plane at hg'
    dsimp only at hg'
    rw [hfs] at hg'
    simp only [List.isEmpty_nil, if_true, List.not_mem_nil] at hg'
  have hfmem : minimalFace (nonFinals g) ∈ nonFinals g :=
    minimal_in_set _ hfs
  have hvne : (minimalFace (nonFinals g)).vertices ≠ [] :=
    h _ (List.mem_filter.mp hfmem).1
  have hvmem : minimalVertex g (minimalFace (nonFinals g)) ∈
      (minimalFace (nonFinals g)).vertices := minimal_in_set _ hvne
  have hbool : (nonFinals g).isEmpty = false := by
    simp only [Bool.eq_false_iff, List.isEmpty_iff, ne_eq]
    exact hfs
  have hg'' := hg'
  unfold next_plane at hg''
  dsimp only at hg''
  rw [hbool] at hg''
  simp only [Bool.false_eq_true, ↓reduceIte] at hg''
  rw [List.mem_flatMap] at hg''
  obtain ⟨i, hi, hg'''⟩ := hg''
  unfold next_plane0
  have hfin : g.final = false := by
    unfold Graph.final
    exact hbool
  rw [hfin]
  simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
  exact ⟨minimalFace (nonFinals g), hfmem, _, hvmem, i, hi, hg'''⟩

/-- Plane1Props.thy: mgp_next_plane0_if_next_plane. Isabelle's one-step
`g [next_plane_p]→ g'` is `g' ∈ next_plane p g`. -/
theorem mgp_next_plane0_if_next_plane {p : Nat} {g g' : Graph}
    (hmgp : minGraphProps g) (hstep : g' ∈ next_plane p g) :
    g' ∈ next_plane0 p g :=
  next_plane_subset (fun f hf => mgp_vertices_nonempty hmgp hf) hstep

/-- Plane1Props.thy: inv_inv_next_plane. Unfolded invariance form, same
reason as `inv_inv_next_plane0` (`invariant` takes `P : Graph → Bool` while
`inv` is a `Prop`). -/
theorem inv_inv_next_plane {p : Nat} :
    ∀ g g', g' ∈ next_plane p g → inv g → inv g' :=
  fun g g' hg' hinv =>
    inv_inv_next_plane0 g g' (mgp_next_plane0_if_next_plane (inv_mgp hinv) hg') hinv

/-- RTranCl.thy: RTranCl_subset2. The subset premise is rendered pointwise
(project convention). -/
theorem RTranCl_subset2 {f h : Graph → List Graph} {s g : Graph}
    (a : RTranCl f s g)
    (hh : ∀ g', RTranCl f s g' → ∀ x ∈ f g', x ∈ h g') : RTranCl h s g := by
  induction a with
  | refl => exact .refl
  | succs hs _ ih =>
    exact .succs (hh _ .refl _ hs)
      (ih (fun g' hg' => hh g' (.succs hs hg')))

end Kepler.Graphs

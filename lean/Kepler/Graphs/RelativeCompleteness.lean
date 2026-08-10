/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Relative_Completeness.thy`,
plus the two pure proof-assembly lemmas from `ArchCompProps.thy`
(`mgp_pre_iso_test`, `iso_test_correct`) and the definitions `fgraph` and
`pre_iso_test` from `ArchCompAux.thy`.

Sources:
- `reference/afp-flyspeck-tame/Relative_Completeness.thy`
- `reference/afp-flyspeck-tame/ArchCompProps.thy` (lines 8–21)
- `reference/afp-flyspeck-tame/ArchCompAux.thy` (lines 20–21, 44–46)
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

## Deviations

- The locale `archive_by_computation` is NOT ported: its trie/worklist
  machinery (`samet`, `tameEnumFilter`, `hash`) is replaced by certificates.
  Its four `same*` assumptions become four pointwise hypotheses
  `same0`–`same3` (explicit theorem arguments); the four `pre_iso_test*`
  assumptions are handled on the checker side and do not appear here.
- `TameEnum_Archive` is stated in the pointwise form
  `∀ g, TameEnum g → inIso g.fgraph Archive`; the Isabelle set form
  `subsetIso (Graph.fgraph '' {g | TameEnum g}) Archive` is recovered as
  `TameEnum_Archive_subset`.
-/
import Kepler.Graphs.TameEnumProps
import Kepler.Graphs.Plane1Props
import Kepler.Graphs.GeneratorProps
import Kepler.Graphs.PlaneGraphIso
import Kepler.Graphs.RotationLemmas
import Kepler.Graphs.ArchiveData.Tri
import Kepler.Graphs.ArchiveData.Quad
import Kepler.Graphs.ArchiveData.Pent
import Kepler.Graphs.ArchiveData.Hex

namespace Kepler.Graphs

/-! ### `fgraph` and `pre_iso_test` (ArchCompAux.thy) -/

/-- ArchCompAux.thy: `fgraph g = map vertices (faces g)`. -/
def Graph.fgraph (g : Graph) : fgraph Nat := g.faces.map Face.vertices

/-- ArchCompAux.thy: `pre_iso_test`
(`[] ∉ set Fs ∧ (∀ F ∈ set Fs. distinct F) ∧ distinct (map rotate_min Fs)`). -/
def pre_iso_test (Fs : fgraph Nat) : Prop :=
  [] ∉ Fs ∧ (∀ F ∈ Fs, F.Nodup) ∧ (Fs.map rotate_min).Nodup

/-! ### `ArchCompProps.thy` -/

/-- ArchCompProps.thy: `mgp_pre_iso_test`. -/
theorem mgp_pre_iso_test {g : Graph} (h : minGraphProps g) : pre_iso_test g.fgraph := by
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hm
    exact mgp_vertices_nonempty h hf hfe
  · intro F hF
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
    exact minGraphProps3 h hf
  · have h11 : (g.faces.map normFace).Nodup := minGraphProps11 h
    show ((g.faces.map Face.vertices).map rotate_min).Nodup
    rw [List.map_map]
    convert h11 using 2
    funext f
    rfl

/-- Auxiliary: from `(l.map f).Nodup` and `l.Nodup`, `f` is injective on the
members of `l`. -/
private theorem eq_of_nodup_map {α β : Type*} {f : α → β} {l : List α}
    (hm : (l.map f).Nodup) (hd : l.Nodup) :
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hm hd
    intro x hx y hy hxy
    rcases List.mem_cons.mp hx with rfl | hxl
    · rcases List.mem_cons.mp hy with rfl | hyl
      · rfl
      · exact (hm.1 (List.mem_map.mpr ⟨y, hyl, hxy.symm⟩)).elim
    · rcases List.mem_cons.mp hy with rfl | hyl
      · exact (hm.1 (List.mem_map.mpr ⟨x, hxl, hxy⟩)).elim
      · exact ih hm.2 hd.2 x hxl y hyl hxy

/-- `pre_iso_test Fs` implies `Fs.Nodup`: `rotate_min` collapses congruent
faces, so injectivity of the mapped list gives nodup of the original. -/
theorem nodup_of_pre_iso_test {Fs : fgraph Nat} (h : pre_iso_test Fs) : Fs.Nodup :=
  List.Nodup.of_map rotate_min h.2.2

/-- `pre_iso_test Fs` implies `noncong Fs`: members with equal `rotate_min`
are congruent (`norm_eq_iff_face_cong`), hence equal by injectivity. -/
theorem noncong_of_pre_iso_test {Fs : fgraph Nat} (h : pre_iso_test Fs) : noncong Fs := by
  obtain ⟨hnil, hdist, hrot⟩ := h
  intro F₁ hF₁ F₂ hF₂ hc
  have hne₁ : F₁ ≠ [] := fun e => hnil (e ▸ hF₁)
  have hne₂ : F₂ ≠ [] := fun e => hnil (e ▸ hF₂)
  have heq : rotate_min F₁ = rotate_min F₂ :=
    (norm_eq_iff_face_cong (hdist F₁ hF₁) hne₁ hne₂).mpr hc
  exact eq_of_nodup_map hrot (List.Nodup.of_map rotate_min hrot) F₁ hF₁ F₂ hF₂ heq

/-- ArchCompProps.thy: `iso_test_correct` (corollary of `iso_correct`). -/
theorem iso_test_correct {Fs₁ Fs₂ : fgraph Nat}
    (h₁ : pre_iso_test Fs₁) (h₂ : pre_iso_test Fs₂) :
    iso_test Fs₁ Fs₂ = true ↔ Fs₁ ≃ Fs₂ :=
  iso_correct h₁.2.1 h₂.2.1 h₂.1
    (nodup_of_pre_iso_test h₁) (nodup_of_pre_iso_test h₂)
    (noncong_of_pre_iso_test h₁) (noncong_of_pre_iso_test h₂)

/-! ### `Relative_Completeness.thy` -/

/-- Relative_Completeness.thy: `Archive ≡ set (Tri @ Quad @ Pent @ Hex)`. -/
def Archive : Set (fgraph Nat) := {x | x ∈ TriData ++ QuadData ++ PentData ++ HexData}

section Completeness

/-- Relative_Completeness.thy: `TameEnum_comp`. -/
theorem TameEnum_comp {p : Nat} {g : Graph}
    (hr : RTranCl (next_plane p) (Seed p) g) (hfin : g.final = true) (ht : tame g) :
    RTranCl (next_tame p) (Seed p) g :=
  next_tame_comp ht hfin (next_tame0_comp hr hfin ht)

/-- Relative_Completeness.thy: `tame5`. -/
theorem tame5 {p : Nat} {g : Graph}
    (hr : RTranCl (next_plane0 p) (Seed p) g) (_hfin : g.final = true) (ht : tame g) :
    p ≤ 3 := by
  have bound : ∀ f ∈ g.faces, f.vertices.length ≤ 6 := by
    intro f hf
    have h9 : tame9a g = true := ht.1
    unfold tame9a at h9
    rw [List.all_eq_true] at h9
    have hb := h9 f hf
    simp only [decide_eq_true_eq] at hb
    exact hb.2
  by_contra hp
  obtain ⟨f, hf, hlen⟩ := max_face_ex hr
  have hfg : f ∈ g.faces := (List.mem_filter.mp hf).1
  have h6 : 6 < f.vertices.length := by
    rw [hlen, show maxGon p = p + 3 from rfl]
    omega
  exact absurd (bound f hfg) (not_le_of_gt h6)

/- The four `same*` assumptions of locale `archive_by_computation`, in
pointwise certificate form: every graph enumerated at stage `p` has (up to
improper isomorphism) its fgraph in the Archive. -/
variable
  (same0 : ∀ g : Graph, TameEnumP 0 g → inIso g.fgraph Archive)
  (same1 : ∀ g : Graph, TameEnumP 1 g → inIso g.fgraph Archive)
  (same2 : ∀ g : Graph, TameEnumP 2 g → inIso g.fgraph Archive)
  (same3 : ∀ g : Graph, TameEnumP 3 g → inIso g.fgraph Archive)

include same0 same1 same2 same3

/-- Relative_Completeness.thy: `TameEnum_Archive` (pointwise form). -/
theorem TameEnum_Archive (g : Graph) (h : TameEnum g) : inIso g.fgraph Archive := by
  obtain ⟨p, hp, htep⟩ := h
  have hc : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact same0 g htep
  · exact same1 g htep
  · exact same2 g htep
  · exact same3 g htep

/-- Relative_Completeness.thy: `TameEnum_Archive` (Isabelle set form:
`fgraph '' TameEnum ⊆ₛ Archive`). -/
theorem TameEnum_Archive_subset :
    subsetIso (Graph.fgraph '' {g | TameEnum g}) Archive := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact TameEnum_Archive same0 same1 same2 same3 g hg

/-- Relative_Completeness.thy: `completeness`. -/
theorem completeness {g : Graph} (hpg : PlaneGraphs g) (ht : tame g) :
    inIso g.fgraph Archive := by
  obtain ⟨p, hr, hfin⟩ := hpg
  have hinv : ∀ g', RTranCl (next_plane p) (Seed p) g' → inv g' :=
    fun g' hg' =>
      RTranCl_induct hg' inv_Seed (fun a b hab ha => inv_inv_next_plane a b hab ha)
  have hr0 : RTranCl (next_plane0 p) (Seed p) g :=
    RTranCl_subset2 hr
      (fun g' hg' x hx => mgp_next_plane0_if_next_plane (inv_mgp (hinv g' hg')) hx)
  have hp : p ≤ 3 := tame5 hr0 hfin ht
  exact TameEnum_Archive same0 same1 same2 same3 g
    ⟨p, hp, TameEnum_comp hr hfin ht, hfin⟩

end Completeness

end Kepler.Graphs

/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `GeneratorProps.thy`
("Properties of Tame Graph Enumeration (1)").

Source: `reference/afp-flyspeck-tame/GeneratorProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Conventions (as elsewhere in this development):
- Isabelle `set xs ⊆ set ys` inclusions are rendered pointwise
  (`∀ x ∈ xs, x ∈ ys`); `vertex set` becomes `Vertex → Prop`.
- Isabelle's `Max` over (finite) sets of `nat` is rendered as `sSup`
  (`Nat` is a `ConditionallyCompleteLinearOrderBot`; `sSup ∅ = 0 = Max ∅`).
- The set comprehension `{∑ p ∈ P, snd p | P. P ⊆ set ps ∧ separated g (fst ` P)}`
  becomes the set of Finset subset sums `exSums g ps` (see below).
-/
import Kepler.Graphs.Plane1Props
import Kepler.Graphs.Generator
import Kepler.Graphs.TameProps
import Kepler.Graphs.LowerBound
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Kepler.Graphs

/-- GeneratorProps.thy: genPolyTame_spec -/
theorem genPolyTame_spec (n : Nat) (v : Vertex) (f : Face) (g : Graph) :
    generatePolygonTame n v f g =
      (generatePolygon n v f g).filter (fun g' => !notame g') := rfl

/-- GeneratorProps.thy: genPolyTame_subset_genPoly -/
theorem genPolyTame_subset_genPoly {i : Nat} {v : Vertex} {f : Face} {g g' : Graph}
    (h : g' ∈ generatePolygonTame i v f g) : g' ∈ generatePolygon i v f g := by
  rw [genPolyTame_spec] at h
  exact (List.mem_filter.mp h).1

/-- Auxiliary: membership in `polysizes` (Isabelle unfolds `polysizes_def`
by `simp`). -/
theorem mem_polysizes {p n : Nat} {g : Graph} :
    n ∈ polysizes p g ↔
      n ∈ List.range' 3 (maxGon p - 2) ∧
        squanderLowerBound g + squanderFace n < squanderTarget := by
  simp only [polysizes, List.mem_filter, decide_eq_true_eq]

/-- GeneratorProps.thy: next_tame0_subset_plane (pointwise form) -/
theorem next_tame0_subset_plane {p : Nat} {g g' : Graph} (h : g' ∈ next_tame0 p g) :
    g' ∈ next_plane p g := by
  have hfs : nonFinals g ≠ [] := by
    intro hfs
    unfold next_tame0 at h
    dsimp only at h
    rw [hfs] at h
    simp only [List.isEmpty_nil, if_true, List.not_mem_nil] at h
  have hbool : (nonFinals g).isEmpty = false := by
    simp only [Bool.eq_false_iff, List.isEmpty_iff, ne_eq]
    exact hfs
  unfold next_tame0 at h
  dsimp only at h
  rw [hbool] at h
  simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at h
  obtain ⟨i, hi, hg'⟩ := h
  unfold next_plane
  dsimp only
  rw [hbool]
  simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
  exact ⟨i, (mem_polysizes.mp hi).1, genPolyTame_subset_genPoly hg'⟩

/-- GeneratorProps.thy: genPoly_new_face -/
theorem genPoly_new_face {g g' : Graph} {f : Face} {v : Vertex} {n : Nat}
    (hg' : g' ∈ generatePolygon n v f g) (mgp : minGraphProps g)
    (hf : f ∈ nonFinals g) (hv : v ∈ f.vertices) (hn : 3 ≤ n) :
    ∃ f' ∈ finals g', f' ∉ finals g ∧ f'.vertices.length = n := by
  simp only [generatePolygon, List.mem_map] at hg'
  obtain ⟨vol, ⟨is, his, rfl⟩, rfl⟩ := hg'
  rw [List.mem_filter] at his
  obtain ⟨his_enum, his_nd⟩ := his
  have hlen : is.length = n := enumerator_length2 his_enum (by omega)
  have hcontains : containsDuplicateEdge g f v is ≠ true := by
    intro hcon
    rw [hcon] at his_nd
    exact Bool.noConfusion his_nd
  have hpre : pre_subdivFace g f v (indexToVertexList f v is) :=
    pre_subdivFace_indexToVertexList mgp hf hv his_enum hcontains (by omega)
  have hne : indexToVertexList f v is ≠ [] := by
    intro e
    have h0 := congrArg List.length e
    rw [length_indexToVertexList, hlen] at h0
    simp at h0
    omega
  have hpre' : pre_subdivFace' g f v v 0 (indexToVertexList f v is).tail :=
    pre_subdivFace_pre_subdivFace' hv ((List.cons_head!_tail hne).symm ▸ hpre)
  have hfg : f ∈ g.faces := (List.mem_filter.mp hf).1
  have hmt : (indexToVertexList f v is).tail = [] →
      0 = 0 ∧ v = (verticesFrom f v).getLast! := by
    intro e
    obtain ⟨hfin', hv', hram, hvnin, hdistf, hmain⟩ := hpre'
    rcases hmain with hbig | ⟨e', hne'⟩
    · exact absurd e hbig.2.2.2.1
    · exact absurd rfl hne'
  obtain ⟨f', hf'fin, hf'old, -, hlen'⟩ := final_subdivFace' mgp hpre' hfg hmt
  have heq : subdivFace g f (indexToVertexList f v is) =
      subdivFace' g f v 0 (indexToVertexList f v is).tail :=
    subdivFace_subdivFace'_eq hpre
  refine ⟨f', by rw [heq]; exact hf'fin, hf'old, ?_⟩
  rw [if_pos rfl] at hlen'
  have h1 : (indexToVertexList f v is).tail.length + 1 = n := by
    have h2 := congrArg List.length (List.cons_head!_tail hne)
    rw [List.length_cons, length_indexToVertexList, hlen] at h2
    exact h2
  omega

/-- GeneratorProps.thy: genPoly_incr_facesquander_lb -/
theorem genPoly_incr_facesquander_lb {g g' : Graph} {f : Face} {v : Vertex} {n : Nat}
    (hg' : g' ∈ generatePolygon n v f g) (pl : inv g) (hf : f ∈ nonFinals g)
    (hv : v ∈ f.vertices) (hn : 3 ≤ n) :
    faceSquanderLowerBound g + squanderFace n ≤ faceSquanderLowerBound g' := by
  obtain ⟨f', hf'new, hf'old, hsize⟩ := genPoly_new_face hg' (inv_mgp pl) hf hv hn
  have hnp0 : g' ∈ next_plane0 (n - 3) g := in_next_plane0I hg' hf hv hn (by omega)
  have dist : g.faces.Nodup := minGraphProps11' (inv_mgp pl)
  have pl' : inv g' := inv_inv_next_plane0 g g' hnp0 pl
  have dist' : g'.faces.Nodup := minGraphProps11' (inv_mgp pl')
  have hsub : {f | f ∈ finals g} ⊆ {f | f ∈ finals g'} := next_plane0_finals_subset hnp0
  rw [faceSquanderLowerBound_eq_ListSum, faceSquanderLowerBound_eq_ListSum]
  rw [ListSum_conv_sum (xs := finals g) (dist.filter Face.final),
    ListSum_conv_sum (xs := finals g') (dist'.filter Face.final)]
  rw [← hsize]
  have hnotin : f' ∉ (finals g).toFinset := by
    rw [List.mem_toFinset]; exact hf'old
  have hsub2 : insert f' (finals g).toFinset ⊆ (finals g').toFinset := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact List.mem_toFinset.mpr hf'new
    · exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hx))
  calc ∑ f ∈ (finals g).toFinset, squanderFace f.vertices.length
        + squanderFace f'.vertices.length
      = ∑ f ∈ insert f' (finals g).toFinset, squanderFace f.vertices.length := by
        rw [Finset.sum_insert hnotin, Nat.add_comm]
    _ ≤ ∑ f ∈ (finals g').toFinset, squanderFace f.vertices.length :=
        Finset.sum_le_sum_of_subset hsub2

/-- GeneratorProps.thy: close -/
def close (g : Graph) (u v : Vertex) : Prop :=
  ∃ f ∈ g.facesAt u,
    if f.vertices.length = 4 then v = f.nextVertex u ∨ v = f.nextVertex (f.nextVertex u)
    else v = f.nextVertex u

noncomputable instance (g : Graph) (u v : Vertex) : Decidable (close g u v) :=
  Classical.propDecidable _

/-- GeneratorProps.thy: delAround_def -/
theorem delAround_def (g : Graph) (u : Vertex) (ps : List (Vertex × Nat)) :
    deleteAround g u ps = ps.filter (fun p => !decide (close g u p.1)) := by
  induction ps with
  | nil => rw [deleteAround_empty, List.filter_nil]
  | cons p ps ih =>
    rw [deleteAroundCons]
    by_cases hc : close g u p.1
    · have hcond : ∃ f ∈ g.facesAt u,
          (f.vertices.length = 4 ∧
            (p.1 = f.nextVertex u ∨ p.1 = f.nextVertex (f.nextVertex u))) ∨
          (f.vertices.length ≠ 4 ∧ p.1 = f.nextVertex u) := by
        obtain ⟨f, hf, hif⟩ := hc
        by_cases h4 : f.vertices.length = 4
        · exact ⟨f, hf, Or.inl ⟨h4, by rwa [if_pos h4] at hif⟩⟩
        · exact ⟨f, hf, Or.inr ⟨h4, by rwa [if_neg h4] at hif⟩⟩
      rw [if_pos hcond]
      have hpf : (!decide (close g u p.1)) = false := by simp [decide_eq_true hc]
      rw [List.filter_cons_of_neg (by simp [hpf]), ih]
    · have hcond : ¬ ∃ f ∈ g.facesAt u,
          (f.vertices.length = 4 ∧
            (p.1 = f.nextVertex u ∨ p.1 = f.nextVertex (f.nextVertex u))) ∨
          (f.vertices.length ≠ 4 ∧ p.1 = f.nextVertex u) := by
        rintro ⟨f, hf, ⟨h4, hif⟩ | ⟨h4, hif⟩⟩
        · exact hc ⟨f, hf, by rw [if_pos h4]; exact hif⟩
        · exact hc ⟨f, hf, by rw [if_neg h4]; exact hif⟩
      rw [if_neg hcond]
      have hpt : (!decide (close g u p.1)) = true := by simp [decide_eq_false hc]
      rw [List.filter_cons_of_pos (by simp [hpt]), ih]

/-- GeneratorProps.thy: close_sym -/
theorem close_sym {g : Graph} {u v : Vertex} (mgp : minGraphProps g) (ug : u ∈ g.vertices)
    (cl : close g u v) : close g v u := by
  obtain ⟨f, hf, hif⟩ := cl
  have uf : u ∈ f.vertices := minGraphProps6 mgp ug hf
  have distf : f.vertices.Nodup := minGraphProps3 mgp (minGraphProps5 mgp ug hf)
  by_cases h4 : f.vertices.length = 4
  · rw [if_pos h4] at hif
    rcases hif with hif | hif
    · obtain ⟨f', hf', hf'v⟩ := mgp_nextVertex_face_ex2 mgp ug hf
      refine ⟨f', ?_, ?_⟩
      · rw [hif]; exact hf'
      · have hf'v' : f'.nextVertex v = u := by rwa [← hif] at hf'v
        by_cases h4' : f'.vertices.length = 4
        · rw [if_pos h4']; exact Or.inl hf'v'.symm
        · rw [if_neg h4']; exact hf'v'.symm
    · have h1 : f.nextVertex (f.nextVertex v) = u := by
        have h := quad_next4_id h4 distf uf
        rwa [← hif] at h
      have hvf : v ∈ f.vertices := by
        rw [hif]; exact nextVertex_in_face (nextVertex_in_face uf)
      refine ⟨f, minGraphProps7 mgp (minGraphProps5 mgp ug hf) hvf, ?_⟩
      rw [if_pos h4]; exact Or.inr h1.symm
  · rw [if_neg h4] at hif
    obtain ⟨f', hf', hf'v⟩ := mgp_nextVertex_face_ex2 mgp ug hf
    refine ⟨f', ?_, ?_⟩
    · rw [hif]; exact hf'
    · have hf'v' : f'.nextVertex v = u := by rwa [← hif] at hf'v
      by_cases h4' : f'.vertices.length = 4
      · rw [if_pos h4']; exact Or.inl hf'v'.symm
      · rw [if_neg h4']; exact hf'v'.symm

/-- GeneratorProps.thy: sep_conv. The set inclusion `V ⊆ 𝒱 g` and the
bounded universal are rendered pointwise. -/
theorem sep_conv {g : Graph} {V : Vertex → Prop} (mgp : minGraphProps g)
    (hV : ∀ v, V v → v ∈ g.vertices) :
    separated g V ↔ ∀ u, V u → ∀ v, V v → u ≠ v → ¬ close g u v := by
  constructor
  · rintro ⟨hsep2, hsep3⟩ u hu v hv huv hcl
    obtain ⟨f, hf, hif⟩ := hcl
    have hug : u ∈ g.vertices := hV u hu
    have huf : u ∈ f.vertices := minGraphProps6 mgp hug hf
    by_cases h4 : f.vertices.length = 4
    · rw [if_pos h4] at hif
      rcases hif with hif | hif
      · have hVnu : V (f.nextVertex u) := by rw [← hif]; exact hv
        exact hsep2 u hu f hf hVnu
      · have hvf : v ∈ f.vertices := by
          rw [hif]; exact nextVertex_in_face (nextVertex_in_face huf)
        have hlen : f.vertices.length ≤ 4 := by omega
        have hvu : v = u := (hsep3 u hu f hf hlen v).mp ⟨hvf, hv⟩
        exact huv hvu.symm
    · rw [if_neg h4] at hif
      have hVnu : V (f.nextVertex u) := by rw [← hif]; exact hv
      exact hsep2 u hu f hf hVnu
  · intro hcl
    constructor
    · intro v hv f hf hnext
      have hvg : v ∈ g.vertices := hV v hv
      exact hcl v hv (f.nextVertex v) hnext (Ne.symm (mgp_facesAt_no_loop mgp hvg hf))
        ⟨f, hf, by
          by_cases h4 : f.vertices.length = 4
          · rw [if_pos h4]; exact Or.inl rfl
          · rw [if_neg h4]⟩
    · intro v hv f hf hlen x
      have hvg : v ∈ g.vertices := hV v hv
      have hfg : f ∈ g.faces := minGraphProps5 mgp hvg hf
      have hvf : v ∈ f.vertices := minGraphProps6 mgp hvg hf
      have distf : f.vertices.Nodup := minGraphProps3 mgp hfg
      constructor
      · rintro ⟨hxf, hxV⟩
        have h3or4 : f.vertices.length = 3 ∨ f.vertices.length = 4 := by
          have h3 := mgp_vertices3 mgp hfg
          omega
        rcases h3or4 with h3 | h4
        · have hset := vertices_triangle h3 hvf distf
          have hxmem : x ∈
              ({v, f.nextVertex v, f.nextVertex (f.nextVertex v)} : Set Vertex) := by
            rw [← hset]; exact hxf
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
          rcases hxmem with rfl | rfl | rfl
          · rfl
          · by_contra hxv
            exact hcl v hv _ hxV (Ne.symm hxv)
              ⟨f, hf, by rw [if_neg (show ¬ f.vertices.length = 4 by omega)]⟩
          · have hnv : f.nextVertex (f.nextVertex (f.nextVertex v)) = v :=
              tri_next3_id h3 distf hvf
            have hedge : (f.nextVertex (f.nextVertex v), v) ∈ f.edges := by
              have h := nextVertex_in_edges hxf
              rwa [hnv] at h
            obtain ⟨f', hf', hedge'⟩ := mgp_edge_face_ex mgp hvg hf hedge
            have hnx : f'.nextVertex v = f.nextVertex (f.nextVertex v) :=
              (edges_face_eq.mp hedge').1
            by_contra hxv
            exact hcl v hv _ hxV (Ne.symm hxv)
              ⟨f', hf', by
                by_cases h4' : f'.vertices.length = 4
                · rw [if_pos h4']; exact Or.inl hnx.symm
                · rw [if_neg h4']; exact hnx.symm⟩
        · have hset := vertices_quad h4 hvf distf
          have hxmem : x ∈
              ({v, f.nextVertex v, f.nextVertex (f.nextVertex v),
                f.nextVertex (f.nextVertex (f.nextVertex v))} : Set Vertex) := by
            rw [← hset]; exact hxf
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
          rcases hxmem with rfl | rfl | rfl | rfl
          · rfl
          · by_contra hxv
            exact hcl v hv _ hxV (Ne.symm hxv)
              ⟨f, hf, by rw [if_pos h4]; exact Or.inl rfl⟩
          · by_contra hxv
            exact hcl v hv _ hxV (Ne.symm hxv)
              ⟨f, hf, by rw [if_pos h4]; exact Or.inr rfl⟩
          · have hnv : f.nextVertex (f.nextVertex (f.nextVertex (f.nextVertex v))) = v :=
              quad_next4_id h4 distf hvf
            have hedge : (f.nextVertex (f.nextVertex (f.nextVertex v)), v) ∈ f.edges := by
              have h := nextVertex_in_edges hxf
              rwa [hnv] at h
            obtain ⟨f', hf', hedge'⟩ := mgp_edge_face_ex mgp hvg hf hedge
            have hnx : f'.nextVertex v = f.nextVertex (f.nextVertex (f.nextVertex v)) :=
              (edges_face_eq.mp hedge').1
            by_contra hxv
            exact hcl v hv _ hxV (Ne.symm hxv)
              ⟨f', hf', by
                by_cases h4' : f'.vertices.length = 4
                · rw [if_pos h4']; exact Or.inl hnx.symm
                · rw [if_neg h4']; exact hnx.symm⟩
      · intro hxv
        subst hxv
        exact ⟨hvf, hv⟩

/-- GeneratorProps.thy: sep_ne. Rendered with Finsets: the separating set
`fst ` P` becomes the pointwise predicate `fun v => ∃ q ∈ P, q.1 = v`. -/
theorem sep_ne (g : Graph) (M : Finset (Vertex × Nat)) :
    ∃ P : Finset (Vertex × Nat), P ⊆ M ∧ separated g (fun v => ∃ q ∈ P, q.1 = v) := by
  refine ⟨∅, Finset.empty_subset M, ?_, ?_⟩
  · intro v hv
    simp only [Finset.notMem_empty, false_and, exists_false] at hv
  · intro v hv
    simp only [Finset.notMem_empty, false_and, exists_false] at hv

/-! ### The `Max`-characterisation of `ExcessNotAtRec`

Isabelle's `ExcessNotAtRec_conv_Max` identifies `ExcessNotAtRec ps g` with
`Max {∑ p∈P. snd p |P. P ⊆ set ps ∧ separated g (fst ` P)}`. We render the
set of subset sums as `exSums g ps` (and the variant with a mandatory
element as `exSumsIn g p ps`), and the `Max` as `sSup` on `Set Nat`. -/

/-- The set of separated subset sums of `ps` (Isabelle set comprehension). -/
private def exSums (g : Graph) (ps : List (Vertex × Nat)) : Set Nat :=
  {s | ∃ P : Finset (Vertex × Nat), (∀ q ∈ P, q ∈ ps) ∧
    separated g (fun v => ∃ q ∈ P, q.1 = v) ∧ ∑ q ∈ P, q.2 = s}

/-- Variant of `exSums` with a mandatory element `p`. -/
private def exSumsIn (g : Graph) (p : Vertex × Nat) (ps : List (Vertex × Nat)) : Set Nat :=
  {s | ∃ P : Finset (Vertex × Nat), (∀ q ∈ P, q ∈ p :: ps) ∧ p ∈ P ∧
    separated g (fun v => ∃ q ∈ P, q.1 = v) ∧ ∑ q ∈ P, q.2 = s}

private theorem exSums_nonempty (g : Graph) (ps : List (Vertex × Nat)) :
    (exSums g ps).Nonempty := by
  obtain ⟨P, hP, hsep⟩ := sep_ne g ps.toFinset
  exact ⟨∑ q ∈ P, q.2, P, fun q hq => List.mem_toFinset.mp (hP hq), hsep, rfl⟩

private theorem exSums_finite (g : Graph) (ps : List (Vertex × Nat)) :
    (exSums g ps).Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun P : Finset (Vertex × Nat) => ∑ q ∈ P, q.2)
    (Finset.finite_toSet ps.toFinset.powerset)) ?_
  rintro s ⟨P, hP, -, rfl⟩
  exact ⟨P, Finset.mem_coe.mpr (Finset.mem_powerset.mpr
    fun q hq => List.mem_toFinset.mpr (hP q hq)), rfl⟩

private theorem exSumsIn_nonempty {g : Graph} (mgp : minGraphProps g) (p : Vertex × Nat)
    (ps : List (Vertex × Nat)) (hp : p.1 ∈ g.vertices) : (exSumsIn g p ps).Nonempty := by
  have hsep : separated g (fun v => v = p.1) := by
    constructor
    · intro v hv f hf hnext
      subst hv
      exact mgp_facesAt_no_loop mgp hp hf hnext
    · intro v hv f hf h4 x
      subst hv
      constructor
      · rintro ⟨-, hx⟩; exact hx
      · intro hx; subst hx
        exact ⟨minGraphProps6 mgp hp hf, rfl⟩
  have hconv : (fun v => ∃ q ∈ ({p} : Finset (Vertex × Nat)), q.1 = v) =
      (fun v => v = p.1) := by
    funext v
    apply propext
    constructor
    · rintro ⟨q, hq, hq1⟩
      rw [Finset.mem_singleton] at hq
      subst hq
      exact hq1.symm
    · intro hv
      exact ⟨p, Finset.mem_singleton_self p, hv.symm⟩
  refine ⟨∑ q ∈ {p}, q.2, {p}, ?_, Finset.mem_singleton_self p, ?_, rfl⟩
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact List.mem_cons_self
  · rw [hconv]
    exact hsep

private theorem exSumsIn_finite (g : Graph) (p : Vertex × Nat) (ps : List (Vertex × Nat)) :
    (exSumsIn g p ps).Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun P : Finset (Vertex × Nat) => ∑ q ∈ P, q.2)
    (Finset.finite_toSet (p :: ps).toFinset.powerset)) ?_
  rintro s ⟨P, hP, -, -, rfl⟩
  exact ⟨P, Finset.mem_coe.mpr (Finset.mem_powerset.mpr
    fun q hq => List.mem_toFinset.mpr (hP q hq)), rfl⟩

/-- `Max_add_commute` for `sSup` on `Set Nat`. -/
private theorem sSup_image_add_nat {s : Set Nat} (c : Nat) (hne : s.Nonempty)
    (hfin : s.Finite) : sSup ((fun x => x + c) '' s) = sSup s + c := by
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro b ⟨a, ha, rfl⟩
    exact Nat.add_le_add_right (le_csSup hfin.bddAbove ha) c
  · have hm : sSup s ∈ s := hne.csSup_mem hfin
    exact le_csSup (hfin.image _).bddAbove ⟨sSup s, hm, rfl⟩

/-- `Max_Un` for `sSup` on `Set Nat`. -/
private theorem sSup_union_eq_max_nat {s t : Set Nat} (hs : s.Nonempty) (ht : t.Nonempty)
    (hfs : s.Finite) (hft : t.Finite) : sSup (s ∪ t) = max (sSup s) (sSup t) := by
  have hbd : BddAbove (s ∪ t) := by
    obtain ⟨bs, hbs⟩ := hfs.bddAbove
    obtain ⟨bt, hbt⟩ := hft.bddAbove
    exact ⟨max bs bt, fun x hx => by
      rcases hx with hx | hx
      · exact le_max_of_le_left (hbs hx)
      · exact le_max_of_le_right (hbt hx)⟩
  apply le_antisymm
  · apply csSup_le (by exact ⟨hs.some, Or.inl hs.some_mem⟩)
    intro b hb
    rcases hb with hb | hb
    · exact le_max_of_le_left (le_csSup hfs.bddAbove hb)
    · exact le_max_of_le_right (le_csSup hft.bddAbove hb)
  · rcases le_total (sSup s) (sSup t) with h | h
    · rw [max_eq_right h]
      exact le_csSup hbd (Set.mem_union_right s (ht.csSup_mem hft))
    · rw [max_eq_left h]
      exact le_csSup hbd (Set.mem_union_left t (hs.csSup_mem hfs))

/-- Adding `y` to every separated subset sum amounts to inserting `(x, y)`
into the subset (valid since `x` does not occur among the keys of `ps`). -/
private theorem exSums_image_add {g : Graph} {x : Vertex} {y : Nat}
    {ps : List (Vertex × Nat)} (hx : x ∉ ps.map Prod.fst) :
    (fun s => s + y) '' exSums g ps =
      {s | ∃ P : Finset (Vertex × Nat), (∀ q ∈ P, q ∈ ps) ∧
        separated g (fun v => ∃ q ∈ P, q.1 = v) ∧ ∑ q ∈ insert (x, y) P, q.2 = s} := by
  ext s
  have hnotin : ∀ P : Finset (Vertex × Nat), (∀ q ∈ P, q ∈ ps) → (x, y) ∉ P := by
    intro P hP hm
    exact hx (List.mem_map.mpr ⟨(x, y), hP _ hm, rfl⟩)
  constructor
  · rintro ⟨s', ⟨P, hP, hsep, rfl⟩, rfl⟩
    exact ⟨P, hP, hsep, by rw [Finset.sum_insert (hnotin P hP)]; exact Nat.add_comm _ _⟩
  · rintro ⟨P, hP, hsep, rfl⟩
    exact ⟨∑ q ∈ P, q.2, ⟨P, hP, hsep, rfl⟩,
      by rw [Finset.sum_insert (hnotin P hP)]; exact (Nat.add_comm _ _).symm⟩

/-- The insert-sum set equals `exSumsIn`. The hypotheses say that the keys
of `ps` lie in `𝒱 g` and none of them is `close` to `x` (this is the
`sep_conv`/`close_sym` step of Isabelle's proof). -/
private theorem exSums_insert_eq_exSumsIn {g : Graph} {x : Vertex} {y : Nat}
    {ps : List (Vertex × Nat)} (mgp : minGraphProps g)
    (hsub : ∀ q ∈ ps, q.1 ∈ g.vertices) (hxg : x ∈ g.vertices)
    (hnc : ∀ q ∈ ps, ¬ close g x q.1) :
    {s | ∃ P : Finset (Vertex × Nat), (∀ q ∈ P, q ∈ ps) ∧
      separated g (fun v => ∃ q ∈ P, q.1 = v) ∧ ∑ q ∈ insert (x, y) P, q.2 = s} =
    exSumsIn g (x, y) ps := by
  ext s
  constructor
  · rintro ⟨P, hP, hsep, rfl⟩
    have hV2 : ∀ v, (∃ q ∈ P, q.1 = v) → v ∈ g.vertices := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := hv
      exact hsub q (hP q hq)
    have hV1 : ∀ v, (∃ q ∈ insert (x, y) P, q.1 = v) → v ∈ g.vertices := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := hv
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hxg
      · exact hsub q (hP q hq)
    have hsep1 : separated g (fun v => ∃ q ∈ insert (x, y) P, q.1 = v) := by
      refine (sep_conv mgp hV1).mpr ?_
      intro u hu v hv huv hcl
      obtain ⟨qu, hqu, rfl⟩ := hu
      obtain ⟨qv, hqv, rfl⟩ := hv
      rcases Finset.mem_insert.mp hqu with rfl | hqu
      · rcases Finset.mem_insert.mp hqv with rfl | hqv
        · exact absurd rfl huv
        · exact hnc qv (hP qv hqv) hcl
      · rcases Finset.mem_insert.mp hqv with rfl | hqv
        · exact hnc qu (hP qu hqu) (close_sym mgp (hsub qu (hP qu hqu)) hcl)
        · exact (sep_conv mgp hV2).mp hsep qu.1 ⟨qu, hqu, rfl⟩ qv.1 ⟨qv, hqv, rfl⟩ huv hcl
    refine ⟨insert (x, y) P, ?_, Finset.mem_insert_self _ _, hsep1, rfl⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hP q hq')
  · rintro ⟨P, hP, hpin, hsep, rfl⟩
    refine ⟨P.erase (x, y), ?_, ?_, ?_⟩
    · intro q hq
      have hqP : q ∈ P := Finset.mem_of_mem_erase hq
      have hqne : q ≠ (x, y) := by
        intro e
        subst e
        exact Finset.notMem_erase (x, y) P hq
      rcases List.mem_cons.mp (hP q hqP) with e | e
      · exact absurd e hqne
      · exact e
    · exact separated_subset (fun v hv => by
        obtain ⟨q, hq, hq1⟩ := hv
        exact ⟨q, Finset.mem_of_mem_erase hq, hq1⟩) hsep
    · rw [Finset.insert_erase hpin]

/-- The key step: over separated subsets containing `(x, y)`, the other
elements are exactly those surviving `deleteAround g x`. -/
private theorem exSumsIn_deleteAround {g : Graph} {x : Vertex} {y : Nat}
    {ps : List (Vertex × Nat)} (mgp : minGraphProps g) (hx : x ∉ ps.map Prod.fst)
    (hsub : ∀ q ∈ (x, y) :: ps, q.1 ∈ g.vertices) :
    exSumsIn g (x, y) (deleteAround g x ps) = exSumsIn g (x, y) ps := by
  ext s
  constructor
  · rintro ⟨P, hP, hpin, hsep, rfl⟩
    refine ⟨P, fun q hq => ?_, hpin, hsep, rfl⟩
    rcases List.mem_cons.mp (hP q hq) with e | e
    · exact List.mem_cons.mpr (Or.inl e)
    · exact List.mem_cons.mpr (Or.inr (deleteAround_subset g x ps e))
  · rintro ⟨P, hP, hpin, hsep, rfl⟩
    have hV : ∀ v, (∃ q ∈ P, q.1 = v) → v ∈ g.vertices := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := hv
      exact hsub q (hP q hq)
    have hsep' := (sep_conv mgp hV).mp hsep
    refine ⟨P, fun q hq => ?_, hpin, hsep, rfl⟩
    rcases List.mem_cons.mp (hP q hq) with e | e
    · exact List.mem_cons.mpr (Or.inl e)
    · refine List.mem_cons.mpr (Or.inr ?_)
      rw [delAround_def, List.mem_filter]
      refine ⟨e, ?_⟩
      have hqne : x ≠ q.1 := by
        intro hxq
        have h1 : q.1 ∈ ps.map Prod.fst := List.mem_map.mpr ⟨q, e, rfl⟩
        rw [← hxq] at h1
        exact hx h1
      have hclose : ¬ close g x q.1 := hsep' x ⟨(x, y), hpin, rfl⟩ q.1 ⟨q, hq, rfl⟩ hqne
      show (!decide (close g x q.1)) = true
      simp [decide_eq_false hclose]

/-- Split of `exSums` on a `cons` (Isabelle: the final `?U = ?M ps0` step). -/
private theorem exSums_cons {g : Graph} {p : Vertex × Nat} {ps : List (Vertex × Nat)} :
    exSums g (p :: ps) = exSums g ps ∪ exSumsIn g p ps := by
  ext s
  constructor
  · rintro ⟨P, hP, hsep, rfl⟩
    by_cases hpin : p ∈ P
    · exact Or.inr ⟨P, hP, hpin, hsep, rfl⟩
    · refine Or.inl ⟨P, fun q hq => ?_, hsep, rfl⟩
      rcases List.mem_cons.mp (hP q hq) with e | e
      · exact absurd (e ▸ hq) hpin
      · exact e
  · rintro (⟨P, hP, hsep, rfl⟩ | ⟨P, hP, hpin, hsep, rfl⟩)
    · exact ⟨P, fun q hq => List.mem_cons_of_mem p (hP q hq), hsep, rfl⟩
    · exact ⟨P, hP, hsep, rfl⟩

private theorem conv_Max_nil (g : Graph) :
    ExcessNotAtRec [] g = sSup (exSums g []) := by
  rw [ExcessNotAtRec_nil]
  apply le_antisymm
  · exact Nat.zero_le _
  · apply csSup_le (exSums_nonempty g [])
    rintro s ⟨P, hP, -, rfl⟩
    have hP' : P = ∅ := by
      by_contra hne
      obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      exact List.not_mem_nil (hP q hq)
    rw [hP']
    simp

private theorem ExcessNotAtRec_conv_Max_aux {g : Graph} (mgp : minGraphProps g) :
    ∀ n : Nat, ∀ ps : List (Vertex × Nat), ps.length ≤ n →
      (∀ q ∈ ps, q.1 ∈ g.vertices) → (ps.map Prod.fst).Nodup →
      ExcessNotAtRec ps g = sSup (exSums g ps) := by
  intro n
  induction n with
  | zero =>
    intro ps hlen hsub hdist
    have hps : ps = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hps
    exact conv_Max_nil g
  | succ n ih =>
    intro ps hlen hsub hdist
    cases ps with
    | nil => exact conv_Max_nil g
    | cons p ps =>
      obtain ⟨x, y⟩ := p
      rw [List.map_cons, List.nodup_cons] at hdist
      obtain ⟨hxnin, hdist'⟩ := hdist
      have hsub' : ∀ q ∈ ps, q.1 ∈ g.vertices :=
        fun q hq => hsub q (List.mem_cons_of_mem _ hq)
      have hple : ps.length ≤ n := by
        have hll : ((x, y) :: ps).length = ps.length + 1 := rfl
        omega
      have e1 := ih ps hple hsub' hdist'
      have hdle : (deleteAround g x ps).length ≤ n :=
        Nat.le_trans (length_deleteAround g x ps) hple
      have hdsub : ∀ q ∈ deleteAround g x ps, q.1 ∈ g.vertices :=
        fun q hq => hsub' q (deleteAround_subset g x ps hq)
      have hddist : ((deleteAround g x ps).map Prod.fst).Nodup :=
        distinct_deleteAround g x hdist'
      have e2 := ih _ hdle hdsub hddist
      have hxnin' : x ∉ (deleteAround g x ps).map Prod.fst := by
        intro hm
        obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hm
        have h1 : q.1 ∈ ps.map Prod.fst :=
          List.mem_map.mpr ⟨q, deleteAround_subset g x ps hq, rfl⟩
        rw [hqx] at h1
        exact hxnin h1
      have hnc : ∀ q ∈ deleteAround g x ps, ¬ close g x q.1 := by
        intro q hq hcl
        rw [delAround_def, List.mem_filter] at hq
        have hb : (!decide (close g x q.1)) = true := hq.2
        rw [decide_eq_true hcl] at hb
        exact Bool.noConfusion hb
      have hxg : x ∈ g.vertices := hsub (x, y) List.mem_cons_self
      have step1 : y + sSup (exSums g (deleteAround g x ps)) =
          sSup (exSumsIn g (x, y) ps) := by
        rw [← exSumsIn_deleteAround mgp hxnin hsub,
          ← exSums_insert_eq_exSumsIn mgp hdsub hxg hnc,
          ← exSums_image_add hxnin',
          sSup_image_add_nat y (exSums_nonempty g (deleteAround g x ps))
            (exSums_finite g (deleteAround g x ps))]
        exact Nat.add_comm _ _
      rw [ExcessNotAtRec_cons x y ps g, e1, e2, step1, exSums_cons]
      exact (sSup_union_eq_max_nat (exSums_nonempty g ps)
        (exSumsIn_nonempty mgp (x, y) ps (hsub (x, y) List.mem_cons_self))
        (exSums_finite g ps) (exSumsIn_finite g (x, y) ps)).symm

/-- GeneratorProps.thy: ExcessNotAtRec_conv_Max. Isabelle's
`set (map fst ps) ⊆ 𝒱 g` is rendered pointwise and `Max` as `sSup`. -/
theorem ExcessNotAtRec_conv_Max {g : Graph} (mgp : minGraphProps g)
    {ps : List (Vertex × Nat)} (hsub : ∀ q ∈ ps, q.1 ∈ g.vertices)
    (hdist : (ps.map Prod.fst).Nodup) :
    ExcessNotAtRec ps g = sSup (exSums g ps) :=
  ExcessNotAtRec_conv_Max_aux mgp _ ps (Nat.le_refl _) hsub hdist

/-- GeneratorProps.thy: dist_ExcessTab -/
theorem dist_ExcessTab (g : Graph) : ((ExcessTable g g.vertices).map Prod.fst).Nodup :=
  distinct_ExcessTable (vs := g.vertices) List.nodup_range

/-- Auxiliary: `ExcessTable` as filter-map (combines `ExcessTable_eq` and
`ExcessTable_cont_eq` from ScoreProps). -/
theorem ExcessTable_filter_map_eq (g : Graph) (vs : List Vertex) :
    ExcessTable g vs =
      ((vs.filter fun v => 0 < ExcessAt g v).map fun v => (v, ExcessAt g v)) := by
  rw [ExcessTable_eq]
  exact ExcessTable_cont_eq _ _

/-- Auxiliary: membership in `ExcessTable`. -/
theorem mem_ExcessTable {g : Graph} {vs : List Vertex} {p : Vertex × Nat} :
    p ∈ ExcessTable g vs ↔ p.1 ∈ vs ∧ 0 < ExcessAt g p.1 ∧ p.2 = ExcessAt g p.1 := by
  rw [ExcessTable_filter_map_eq, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [List.mem_filter] at ha
    exact ⟨ha.1, of_decide_eq_true ha.2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p.1, List.mem_filter.mpr ⟨h1, decide_eq_true h2⟩, Prod.ext_iff.mpr ⟨rfl, h3.symm⟩⟩

/-- GeneratorProps.thy: mono_ExcessTab (pointwise form) -/
theorem mono_ExcessTab {p : Nat} {g g' : Graph} (h : g' ∈ next_plane0 p g) (pl : inv g) :
    ∀ q ∈ ExcessTable g g.vertices, q ∈ ExcessTable g' g'.vertices := by
  intro q hq
  have mgp := inv_mgp pl
  obtain ⟨hv, hpos, hq2⟩ := mem_ExcessTable.mp hq
  have hfv : finalVertex g q.1 = true := by
    by_contra hc
    have hf : (!finalVertex g q.1) = true := by
      cases hff : finalVertex g q.1 with
      | false => rfl
      | true => exact absurd hff hc
    unfold ExcessAt at hpos
    rw [if_pos hf] at hpos
    exact Nat.lt_irrefl 0 hpos
  have pl' : inv g' := inv_inv_next_plane0 g g' h pl
  have hvg' : q.1 ∈ g'.vertices := next_plane0_vertices_subset h mgp q.1 hv
  have hfv' : finalVertex g' q.1 = true := next_plane0_finalVertex_mono h pl hv hfv
  have htri : tri g' q.1 = tri g q.1 :=
    next_plane0_len_filter_eq (fun f => f.final && f.vertices.length == 3) h pl hv hfv
  have hquad : quad g' q.1 = quad g q.1 :=
    next_plane0_len_filter_eq (fun f => f.final && f.vertices.length == 4) h pl hv hfv
  have hex : except g' q.1 = except g q.1 :=
    next_plane0_len_filter_eq (fun f => f.final && decide (5 ≤ f.vertices.length))
      h pl hv hfv
  have hexa : ExcessAt g' q.1 = ExcessAt g q.1 := by
    unfold ExcessAt
    have hn1 : ¬ ((!finalVertex g' q.1) = true) := by simp [hfv']
    have hn2 : ¬ ((!finalVertex g q.1) = true) := by simp [hfv]
    rw [if_neg hn1, if_neg hn2, htri, hquad, hex]
  exact mem_ExcessTable.mpr ⟨hvg', by rw [hexa]; exact hpos, by rw [hexa]; exact hq2⟩

/-- GeneratorProps.thy: close_antimono -/
theorem close_antimono {p : Nat} {g g' : Graph} {u v : Vertex} (h : g' ∈ next_plane0 p g)
    (pl : inv g) (hu : u ∈ g.vertices) (hfv : finalVertex g u = true)
    (hcl : close g' u v) : close g u v := by
  obtain ⟨f, hf, hif⟩ := hcl
  have heq := next_plane0_finalVertex_facesAt_eq h pl hu hfv
  exact ⟨f, (Set.ext_iff.mp heq f).mp hf, hif⟩

/-- GeneratorProps.thy: ExcessTab_final -/
theorem ExcessTab_final {g : Graph} {p : Vertex × Nat}
    (h : p ∈ ExcessTable g g.vertices) : finalVertex g p.1 = true := by
  obtain ⟨-, hpos, -⟩ := mem_ExcessTable.mp h
  by_contra hc
  have hf : (!finalVertex g p.1) = true := by
    cases hff : finalVertex g p.1 with
    | false => rfl
    | true => exact absurd hff hc
  unfold ExcessAt at hpos
  rw [if_pos hf] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- GeneratorProps.thy: ExcessTab_vertex -/
theorem ExcessTab_vertex {g : Graph} {p : Vertex × Nat}
    (h : p ∈ ExcessTable g g.vertices) : p.1 ∈ g.vertices :=
  (mem_ExcessTable.mp h).1

/-- GeneratorProps.thy: fst_set_ExcessTable_subset (pointwise form) -/
theorem fst_set_ExcessTable_subset {g : Graph} :
    ∀ v ∈ (ExcessTable g g.vertices).map Prod.fst, v ∈ g.vertices := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact ExcessTab_vertex hp

/-- GeneratorProps.thy: next_plane0_incr_ExcessNotAt -/
theorem next_plane0_incr_ExcessNotAt {p : Nat} {g g' : Graph} (h : g' ∈ next_plane0 p g)
    (pl : inv g) : ExcessNotAt g none ≤ ExcessNotAt g' none := by
  have pl' : inv g' := inv_inv_next_plane0 g g' h pl
  have mgp := inv_mgp pl
  have mgp' := inv_mgp pl'
  simp only [ExcessNotAt]
  rw [ExcessNotAtRec_conv_Max mgp (fun q hq => (mem_ExcessTable.mp hq).1)
      (dist_ExcessTab g),
    ExcessNotAtRec_conv_Max mgp' (fun q hq => (mem_ExcessTable.mp hq).1)
      (dist_ExcessTab g')]
  apply csSup_le (exSums_nonempty g _)
  rintro s ⟨P, hP, hsep, rfl⟩
  apply le_csSup (exSums_finite g' _).bddAbove
  have hVg : ∀ v, (∃ q ∈ P, q.1 = v) → v ∈ g.vertices := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := hv
    exact ExcessTab_vertex (hP q hq)
  have hVg' : ∀ v, (∃ q ∈ P, q.1 = v) → v ∈ g'.vertices := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := hv
    exact (mem_ExcessTable.mp (mono_ExcessTab h pl q (hP q hq))).1
  refine ⟨P, fun q hq => mono_ExcessTab h pl q (hP q hq), ?_, rfl⟩
  refine (sep_conv mgp' hVg').mpr ?_
  intro u hu v hv huv hcl
  obtain ⟨qu, hqu, rfl⟩ := hu
  have hclg : close g qu.1 v :=
    close_antimono h pl (ExcessTab_vertex (hP qu hqu)) (ExcessTab_final (hP qu hqu)) hcl
  exact (sep_conv mgp hVg).mp hsep qu.1 ⟨qu, hqu, rfl⟩ v hv huv hclg

/-- GeneratorProps.thy: next_plane0_incr_squander_lb -/
theorem next_plane0_incr_squander_lb {p : Nat} {g g' : Graph} (h : g' ∈ next_plane0 p g)
    (pl : inv g) : squanderLowerBound g ≤ squanderLowerBound g' := by
  have h1 := next_plane0_incr_ExcessNotAt h pl
  obtain ⟨f, hf, v, hv, i, hi, hg'⟩ := next_plane0_ex h
  have h3 : 3 ≤ i := by
    rw [List.mem_range'_1] at hi
    omega
  have h2 := genPoly_incr_facesquander_lb hg' pl hf hv h3
  unfold squanderLowerBound
  omega

/-- GeneratorProps.thy: inv_notame -/
theorem inv_notame {p : Nat} {g g' : Graph} (h : g' ∈ next_plane0 p g) (pl : inv g)
    (hn : notame7 g = true) : notame7 g' = true := by
  have mgp := inv_mgp pl
  by_cases hA : tame10ub g = true
  · by_cases hB : tame11b g = true
    · by_cases hC : is_tame13a g = true
      · unfold notame7 at hn
        rw [hA, hB, hC] at hn
        exact Bool.noConfusion hn
      · have hCf : is_tame13a g = false := Bool.eq_false_iff.mpr hC
        have h2 : ¬ squanderLowerBound g < squanderTarget :=
          of_decide_eq_false (by simpa [is_tame13a] using hCf)
        have hlb : squanderTarget ≤ squanderLowerBound g' := by
          have h3 := next_plane0_incr_squander_lb h pl
          omega
        have hCf' : is_tame13a g' = false := by
          have hnl : ¬ squanderLowerBound g' < squanderTarget := by omega
          unfold is_tame13a
          rw [decide_eq_false hnl]
        unfold notame7
        rw [hCf']
        simp
    · have hBf : tame11b g = false := Bool.eq_false_iff.mpr hB
      have hex : ∃ v ∈ g.vertices,
          decide (degree g v ≤ if except g v = 0 then 7 else 6) = false := by
        by_contra hc
        push_neg at hc
        have ht : tame11b g = true := by
          unfold tame11b
          rw [List.all_eq_true]
          intro v hv
          have hne := hc v hv
          show decide (degree g v ≤ if except g v = 0 then 7 else 6) = true
          cases hb : decide (degree g v ≤ if except g v = 0 then 7 else 6) with
          | false => exact absurd hb hne
          | true => rfl
        rw [hBf] at ht
        exact Bool.noConfusion ht
      obtain ⟨v, hv, hcond⟩ := hex
      have hcond' : ¬ (degree g v ≤ if except g v = 0 then 7 else 6) :=
        of_decide_eq_false hcond
      have hvg' : v ∈ g'.vertices := next_plane0_vertices_subset h mgp v hv
      have hdeg : degree g v ≤ degree g' v := next_plane0_incr_degree h mgp hv
      have hex2 : except g v ≤ except g' v := next_plane0_incr_except h pl hv
      have hB' : tame11b g' = false := by
        rw [Bool.eq_false_iff, ne_eq]
        unfold tame11b
        rw [List.all_eq_true]
        push_neg
        refine ⟨v, hvg', ?_⟩
        intro hle
        have hle' := of_decide_eq_true hle
        by_cases he0 : except g' v = 0
        · rw [if_pos he0] at hle'
          have he0' : except g v = 0 := by omega
          rw [if_pos he0'] at hcond'
          omega
        · rw [if_neg he0] at hle'
          by_cases he1 : except g v = 0
          · rw [if_pos he1] at hcond'
            omega
          · rw [if_neg he1] at hcond'
            omega
      unfold notame7
      rw [hB']
      simp
  · have hAf : tame10ub g = false := Bool.eq_false_iff.mpr hA
    have hcnt : 15 < g.countVertices := by
      have h2 : ¬ g.countVertices ≤ 15 :=
        of_decide_eq_false (by simpa [tame10ub] using hAf)
      omega
    have hcv : g.countVertices ≤ g'.countVertices := by
      have hlen := List.Subperm.length_le (List.Nodup.subperm List.nodup_range
        (fun v hv => next_plane0_vertices_subset h mgp v hv) :
        List.Subperm (List.range g.countVertices) (List.range g'.countVertices))
      rwa [List.length_range, List.length_range] at hlen
    have hA' : tame10ub g' = false := by
      have hnl : ¬ g'.countVertices ≤ 15 := by omega
      unfold tame10ub
      rw [decide_eq_false hnl]
    unfold notame7
    rw [hA']
    simp

/-- GeneratorProps.thy: inv_inv_notame. Unfolded invariance form (same
reason as `inv_inv_next_plane0`: `invariant` takes `P : Graph → Bool` while
`inv` is a `Prop`). -/
theorem inv_inv_notame {p : Nat} :
    ∀ g g', g' ∈ next_plane p g → inv g → notame7 g = true → inv g' ∧ notame7 g' = true :=
  fun g g' hg' hinv hn =>
    ⟨inv_inv_next_plane g g' hg' hinv,
      inv_notame (mgp_next_plane0_if_next_plane (inv_mgp hinv) hg') hinv hn⟩

/-- GeneratorProps.thy: untame_notame. Rendered for the `Prop`-valued `inv`
(see `inv_inv_notame`). -/
theorem untame_notame (g : Graph) (hfin : g.final = true) (pl : inv g)
    (hn : notame7 g = true) : ¬ tame g := by
  intro htame
  obtain ⟨h9a, h10, h11a, h11b, h12o, h13a⟩ := htame
  by_cases hA : tame10ub g = true
  · by_cases hB : tame11b g = true
    · by_cases hC : is_tame13a g = true
      · unfold notame7 at hn
        rw [hA, hB, hC] at hn
        exact Bool.noConfusion hn
      · have hCf : is_tame13a g = false := Bool.eq_false_iff.mpr hC
        have h2 : ¬ squanderLowerBound g < squanderTarget :=
          of_decide_eq_false (by simpa [is_tame13a] using hCf)
        obtain ⟨w, hadm, hwsum⟩ := h13a
        have htw : squanderLowerBound g ≤ (g.faces.map w).sum := by
          rw [← ListSum_eq_sum_map]
          exact total_weight_lowerbound pl hfin ⟨h9a, h10, h11a, h11b, h12o, ⟨w, hadm, hwsum⟩⟩
            hadm (by rwa [ListSum_eq_sum_map])
        omega
    · exact absurd h11b hB
  · have hcnt : 15 < g.countVertices := by
      have h2 : ¬ g.countVertices ≤ 15 := of_decide_eq_false (by
        simpa [tame10ub] using Bool.eq_false_iff.mpr hA)
      omega
    have h10' : 13 ≤ g.countVertices ∧ g.countVertices ≤ 15 := of_decide_eq_true h10
    omega

/-- GeneratorProps.thy: polysizes_tame -/
theorem polysizes_tame {p n : Nat} {g g' : Graph} {f : Face} {v : Vertex}
    (hg' : g' ∈ generatePolygon n v f g) (pl : inv g) (hf : f ∈ nonFinals g)
    (hv : v ∈ f.vertices) (h3 : 3 ≤ n) (hn : n < 4 + p) (hnp : n ∉ polysizes p g) :
    notame7 g' = true := by
  have hnp0 : g' ∈ next_plane0 p g := in_next_plane0I hg' hf hv h3 hn
  have h1 := genPoly_incr_facesquander_lb hg' pl hf hv h3
  have h2 := next_plane0_incr_ExcessNotAt hnp0 pl
  have hnr : n ∈ List.range' 3 (maxGon p - 2) := by
    rw [List.mem_range'_1]
    unfold maxGon
    omega
  have h3' : ¬ squanderLowerBound g + squanderFace n < squanderTarget :=
    fun hc => hnp (mem_polysizes.mpr ⟨hnr, hc⟩)
  have h4 : squanderTarget ≤ squanderLowerBound g' := by
    unfold squanderLowerBound at h3' ⊢
    omega
  have hC : is_tame13a g' = false := by
    have hnl : ¬ squanderLowerBound g' < squanderTarget := by omega
    unfold is_tame13a
    rw [decide_eq_false hnl]
  unfold notame7
  rw [hC]
  simp

/-- GeneratorProps.thy: genPolyTame_notame -/
theorem genPolyTame_notame {n : Nat} {g g' : Graph} {f : Face} {v : Vertex}
    (hg' : g' ∈ generatePolygon n v f g) (ht : g' ∉ generatePolygonTame n v f g)
    (_pl : inv g) (_h3 : 3 ≤ n) : notame7 g' = true := by
  rw [genPolyTame_spec, List.mem_filter] at ht
  have hnot : notame g' = true := by
    by_contra hc
    have hnt : (!notame g') = true := by
      cases hb : notame g' with
      | false => rfl
      | true => exact absurd hb hc
    exact ht ⟨hg', hnt⟩
  unfold notame at hnot
  unfold notame7
  cases hb : (tame10ub g' && tame11b g') with
  | false => simp
  | true =>
    rw [hb] at hnot
    exact Bool.noConfusion hnot

/-- GeneratorProps.thy: excess_notame -/
theorem excess_notame {p : Nat} {g g' : Graph} (pl : inv g) (hg' : g' ∈ next_plane p g)
    (ht : g' ∉ next_tame0 p g) : notame7 g' = true := by
  have mgp := inv_mgp pl
  have hnp0 : g' ∈ next_plane0 p g := mgp_next_plane0_if_next_plane mgp hg'
  have hnf : nonFinals g ≠ [] := next_plane0_nonfinals hnp0
  have hbool : (nonFinals g).isEmpty = false := by
    simp only [Bool.eq_false_iff, List.isEmpty_iff, ne_eq]
    exact hnf
  unfold next_plane at hg'
  dsimp only at hg'
  rw [hbool] at hg'
  simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at hg'
  obtain ⟨n, hn, hgn⟩ := hg'
  have h3 : 3 ≤ n := by
    rw [List.mem_range'_1] at hn
    omega
  have h4 : n < 4 + p := by
    rw [List.mem_range'_1] at hn
    unfold maxGon at hn
    omega
  have hfm : minimalFace (nonFinals g) ∈ nonFinals g := minimal_in_set _ hnf
  have hfg : minimalFace (nonFinals g) ∈ g.faces := (List.mem_filter.mp hfm).1
  have hvm : minimalVertex g (minimalFace (nonFinals g)) ∈
      (minimalFace (nonFinals g)).vertices :=
    minimal_in_set _ (mgp_vertices_nonempty mgp hfg)
  by_cases hcase : n ∈ polysizes p g
  · have hnot : g' ∉ generatePolygonTame n (minimalVertex g (minimalFace (nonFinals g)))
        (minimalFace (nonFinals g)) g := by
      intro hin
      apply ht
      unfold next_tame0
      dsimp only
      rw [hbool]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
      exact ⟨n, hcase, hin⟩
    exact genPolyTame_notame hgn hnot pl h3
  · exact polysizes_tame hgn pl hfm hvm h3 h4 hcase

/-- `TameProps.filterout_untame_succs` with the `P` argument a `Prop`
(here: `inv`). The proof mirrors the `Bool` version, using `RTranCl_induct`
in place of `RTranCl_inv`. -/
private theorem filterout_untame_succs' {P : Graph → Prop} {U : Graph → Bool}
    {f f' : Graph → List Graph}
    (invP : ∀ g g', g' ∈ f g → P g → P g')
    (invPU : ∀ g g', g' ∈ f g → P g → U g = true → U g' = true)
    (huntame : ∀ g, g.final = true → P g → U g = true → ¬ tame g)
    (new_untame : ∀ g g', P g → g' ∈ f g → g' ∉ f' g → U g' = true)
    {g g' : Graph} (gg' : RTranCl f g g') :
    P g → g'.final = true → tame g' → RTranCl f' g g' := by
  induction gg' with
  | refl => exact fun _ _ _ => .refl
  | succs hh' h'h'' ih =>
    rename_i h h' h''
    intro hP hfin htame
    have hP' : P h' := invP _ _ hh' hP
    by_cases hm : h' ∈ f' h
    · exact .succs hm (ih hP' hfin htame)
    · have hU' : U h' = true := new_untame h h' hP hh' hm
      have hPU'' : P h'' ∧ U h'' = true :=
        RTranCl_induct (P := fun g0 => P g0 ∧ U g0 = true) h'h'' ⟨hP', hU'⟩
          fun a b hab hr => ⟨invP a b hab hr.1, invPU a b hab hr.1 hr.2⟩
      exact absurd htame (huntame h'' hfin hPU''.1 hPU''.2)

/-- GeneratorProps.thy: next_tame0_comp -/
theorem next_tame0_comp {p : Nat} {g : Graph}
    (hr : RTranCl (next_plane p) (Seed p) g) (hfin : g.final = true) (ht : tame g) :
    RTranCl (next_tame0 p) (Seed p) g :=
  filterout_untame_succs'
    (fun g g' hg' => inv_inv_next_plane g g' hg')
    (fun g g' hg' hinv hn => (inv_inv_notame g g' hg' hinv hn).2)
    untame_notame
    (fun _ _ hinv hg' hn => excess_notame hinv hg' hn)
    hr inv_Seed hfin ht

/-- GeneratorProps.thy: inv_inv_next_tame0. Unfolded invariance form
(`inv_subset` of `inv_inv_next_plane` and `next_tame0_subset_plane`). -/
theorem inv_inv_next_tame0 {p : Nat} :
    ∀ g g', g' ∈ next_tame0 p g → inv g → inv g' :=
  fun g g' hg' hinv => inv_inv_next_plane g g' (next_tame0_subset_plane hg') hinv

/-- GeneratorProps.thy: inv_inv_next_tame. Unfolded invariance form. -/
theorem inv_inv_next_tame {p : Nat} :
    ∀ g g', g' ∈ next_tame p g → inv g → inv g' := by
  intro g g' hg' hinv
  unfold next_tame at hg'
  exact inv_inv_next_tame0 g g' (List.mem_filter.mp hg').1 hinv

/-- GeneratorProps.thy: mgp_TameEnum -/
theorem mgp_TameEnum {p : Nat} {g : Graph} (h : TameEnumP p g) : minGraphProps g := by
  obtain ⟨hr, -⟩ := h
  exact inv_mgp (RTranCl_induct hr inv_Seed fun a b hab ha => inv_inv_next_tame a b hab ha)

end Kepler.Graphs

/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `PlaneProps.thy`.

Source: `reference/afp-flyspeck-tame/PlaneProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Conventions follow `InvariantsA.lean`: `f ∈ ℱ g` ↦ `f ∈ g.faces`,
`v ∈ 𝒱 f` ↦ `v ∈ f.vertices`, `v ∈ 𝒱 g` ↦ `v ∈ g.vertices`,
`f ∈ set (facesAt g v)` ↦ `f ∈ g.facesAt v`,
`final f` / `¬ final f` ↦ `f.final = true` / `f.final = false`,
`g [next_plane0_p]→ g'` ↦ `g' ∈ next_plane0 p g`.
-/
import Kepler.Graphs.InvariantsC

namespace Kepler.Graphs

/-! ### `final` -/

/-- Graph.thy: finalGraph_face (helper for `plane_final_facesAt`; this
`Graph.thy` lemma was not needed by the earlier ported theories). -/
theorem finalGraph_face {g : Graph} {f : Face} (fin : g.final = true)
    (hf : f ∈ g.faces) : f.final = true := by
  unfold Graph.final nonFinals at fin
  rw [List.isEmpty_iff] at fin
  by_contra hnf
  have hb : f.final = false := by
    cases h : f.final with
    | false => rfl
    | true => exact absurd h hnf
  have hmem : f ∈ g.faces.filter (fun f => !f.final) :=
    List.mem_filter.mpr ⟨hf, by simp [hb]⟩
  rw [fin] at hmem
  exact List.not_mem_nil hmem

/-- PlaneProps.thy: plane_final_facesAt -/
theorem plane_final_facesAt {g : Graph} {v : Vertex} {f : Face}
    (pl : inv g) (fin : g.final = true) (hv : v ∈ g.vertices)
    (hf : f ∈ g.facesAt v) : f.final = true :=
  finalGraph_face fin (minGraphProps5 (inv_mgp pl) hv hf)

/-- PlaneProps.thy: finalVertexI -/
theorem finalVertexI {g : Graph} {v : Vertex} (pl : inv g) (fin : g.final = true)
    (hv : v ∈ g.vertices) : finalVertex g v = true := by
  unfold finalVertex
  rw [List.all_eq_true]
  intro f hf
  exact plane_final_facesAt pl fin hv hf

/-- Auxiliary (no direct Isabelle counterpart): on a `Nodup` list, a map is
injective on the list's elements. -/
private theorem inj_on_of_map_nodup {α β : Type*} {l : List α} {m : α → β}
    {x y : α} (hd : (l.map m).Nodup) (hx : x ∈ l) (hy : y ∈ l)
    (h : m x = m y) : x = y := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at hd
    rw [List.mem_cons] at hx hy
    obtain ⟨hna, hnd⟩ := hd
    rcases hx with hxa | hx
    · rcases hy with hya | hy
      · rw [hxa, hya]
      · subst hxa
        exact absurd (List.mem_map.mpr ⟨y, hy, h.symm⟩) hna
    · rcases hy with hya | hy
      · subst hya
        exact absurd (List.mem_map.mpr ⟨x, hx, h⟩) hna
      · exact ih hnd hx hy

/-- PlaneProps.thy: setFinal_notin_finals -/
theorem setFinal_notin_finals {g : Graph} {f : Face}
    (hfg : f ∈ g.faces) (hfin : f.final = false) (mgp : minGraphProps g) :
    setFinal f ∉ finals g := by
  intro h
  obtain ⟨hf1, hf2⟩ := List.mem_filter.mp h
  have hne : f ≠ setFinal f := by
    intro e
    rw [e, hf2] at hfin
    exact Bool.noConfusion hfin
  have hnorm : normFace f = normFace (setFinal f) := rfl
  have hd := minGraphProps11 mgp
  exact hne (inj_on_of_map_nodup hd hfg hf1 hnorm)

/-! ### `degree` -/

/-- PlaneProps.thy: planeN4 -/
theorem planeN4 {g : Graph} {f : Face} (pl : inv g) (hf : f ∈ g.faces) :
    3 ≤ f.vertices.length :=
  mgp_vertices3 (inv_mgp pl) hf

/-- Auxiliary for `degree_eq`: a list of faces whose vertex counts are all
3, 4 or ≥ 5 splits into the three length filters. -/
private theorem length_eq_filter_partition {l : List Face}
    (h : ∀ f ∈ l, f.vertices.length = 3 ∨ f.vertices.length = 4 ∨
      5 ≤ f.vertices.length) :
    l.length =
      (l.filter (fun f => decide (f.vertices.length = 3))).length +
      (l.filter (fun f => decide (f.vertices.length = 4))).length +
      (l.filter (fun f => decide (5 ≤ f.vertices.length))).length := by
  induction l with
  | nil => simp
  | cons f fs ih =>
    have hf := h f (List.mem_cons_self)
    have hfs : ∀ x ∈ fs, x.vertices.length = 3 ∨ x.vertices.length = 4 ∨
        5 ≤ x.vertices.length :=
      fun x hx => h x (List.mem_cons_of_mem f hx)
    rw [List.length_cons, ih hfs]
    rcases hf with h3 | h4 | h5
    · have e1 : (f :: fs).filter (fun f => decide (f.vertices.length = 3)) =
          f :: fs.filter (fun f => decide (f.vertices.length = 3)) :=
        List.filter_cons_of_pos (by simp [h3])
      have e2 : (f :: fs).filter (fun f => decide (f.vertices.length = 4)) =
          fs.filter (fun f => decide (f.vertices.length = 4)) :=
        List.filter_cons_of_neg (by simp [h3])
      have e3 : (f :: fs).filter (fun f => decide (5 ≤ f.vertices.length)) =
          fs.filter (fun f => decide (5 ≤ f.vertices.length)) :=
        List.filter_cons_of_neg (by simp [h3])
      rw [e1, e2, e3, List.length_cons]
      omega
    · have e1 : (f :: fs).filter (fun f => decide (f.vertices.length = 3)) =
          fs.filter (fun f => decide (f.vertices.length = 3)) :=
        List.filter_cons_of_neg (by simp [h4])
      have e2 : (f :: fs).filter (fun f => decide (f.vertices.length = 4)) =
          f :: fs.filter (fun f => decide (f.vertices.length = 4)) :=
        List.filter_cons_of_pos (by simp [h4])
      have e3 : (f :: fs).filter (fun f => decide (5 ≤ f.vertices.length)) =
          fs.filter (fun f => decide (5 ≤ f.vertices.length)) :=
        List.filter_cons_of_neg (by simp [h4])
      rw [e1, e2, e3, List.length_cons]
      omega
    · have e1 : (f :: fs).filter (fun f => decide (f.vertices.length = 3)) =
          fs.filter (fun f => decide (f.vertices.length = 3)) :=
        List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; omega)
      have e2 : (f :: fs).filter (fun f => decide (f.vertices.length = 4)) =
          fs.filter (fun f => decide (f.vertices.length = 4)) :=
        List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; omega)
      have e3 : (f :: fs).filter (fun f => decide (5 ≤ f.vertices.length)) =
          f :: fs.filter (fun f => decide (5 ≤ f.vertices.length)) :=
        List.filter_cons_of_pos (by simp [h5])
      rw [e1, e2, e3, List.length_cons]
      omega

/-- PlaneProps.thy: degree_eq -/
theorem degree_eq {g : Graph} {v : Vertex} (pl : inv g) (fin : g.final = true)
    (hv : v ∈ g.vertices) :
    degree g v = tri g v + quad g v + except g v := by
  have hfin : ∀ f ∈ g.facesAt v, f.final = true :=
    fun f hf => plane_final_facesAt pl fin hv hf
  have h3 : ∀ f ∈ g.facesAt v,
      f.vertices.length = 3 ∨ f.vertices.length = 4 ∨ 5 ≤ f.vertices.length := by
    intro f hf
    have hfg : f ∈ g.faces := minGraphProps5 (inv_mgp pl) hv hf
    have hge := mgp_vertices3 (inv_mgp pl) hfg
    omega
  have etri : tri g v =
      ((g.facesAt v).filter (fun f => decide (f.vertices.length = 3))).length := by
    show ((g.facesAt v).filter (fun f => f.final && (f.vertices.length == 3))).length
        = _
    congr 1
    refine List.filter_congr ?_
    intro f hf
    rw [hfin f hf, Bool.true_and]
    by_cases h : f.vertices.length = 3
    · simp [h]
    · rw [show (f.vertices.length == 3) = false from by simp [beq_iff_eq, h]]
      simp [h]
  have equad : quad g v =
      ((g.facesAt v).filter (fun f => decide (f.vertices.length = 4))).length := by
    show ((g.facesAt v).filter (fun f => f.final && (f.vertices.length == 4))).length
        = _
    congr 1
    refine List.filter_congr ?_
    intro f hf
    rw [hfin f hf, Bool.true_and]
    by_cases h : f.vertices.length = 4
    · simp [h]
    · rw [show (f.vertices.length == 4) = false from by simp [beq_iff_eq, h]]
      simp [h]
  have eexcept : except g v =
      ((g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length))).length := by
    show ((g.facesAt v).filter
        (fun f => f.final && decide (5 ≤ f.vertices.length))).length = _
    congr 1
    refine List.filter_congr ?_
    intro f hf
    rw [hfin f hf, Bool.true_and]
  show (g.facesAt v).length = _
  rw [etri, equad, eexcept]
  exact length_eq_filter_partition h3

/-- PlaneProps.thy: plane_fin_exceptionalVertex_def -/
theorem plane_fin_exceptionalVertex_def {g : Graph} {v : Vertex}
    (pl : inv g) (fin : g.final = true) (hv : v ∈ g.vertices) :
    exceptionalVertex g v =
      (((g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length))).length
        != 0) := by
  have hfin : ∀ f ∈ g.facesAt v, f.final = true :=
    fun f hf => plane_final_facesAt pl fin hv hf
  have e : except g v =
      ((g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length))).length := by
    show ((g.facesAt v).filter
        (fun f => f.final && decide (5 ≤ f.vertices.length))).length = _
    congr 1
    refine List.filter_congr ?_
    intro f hf
    rw [hfin f hf, Bool.true_and]
  show (except g v != 0) = _
  rw [e]

/-- PlaneProps.thy: not_exceptional -/
theorem not_exceptional {g : Graph} {v : Vertex} {f : Face}
    (pl : inv g) (fin : g.final = true) (hv : v ∈ g.vertices)
    (hf : f ∈ g.facesAt v) (hne : exceptionalVertex g v = false) :
    f.vertices.length ≤ 4 := by
  by_contra h
  push_neg at h
  rw [plane_fin_exceptionalVertex_def pl fin hv] at hne
  have hmem : f ∈ (g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length)) :=
    List.mem_filter.mpr ⟨hf, by simp only [decide_eq_true_eq]; omega⟩
  have hpos : 0 <
      ((g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length))).length :=
    List.length_pos_of_mem hmem
  have htrue : (((g.facesAt v).filter
      (fun f => decide (5 ≤ f.vertices.length))).length != 0) = true :=
    bne_iff_ne.mpr (Nat.ne_of_gt hpos)
  rw [htrue] at hne
  exact Bool.noConfusion hne

/-! ### Misc -/

/-- PlaneProps.thy: in_next_plane0I -/
theorem in_next_plane0I {g g' : Graph} {f : Face} {v : Vertex} {n p : Nat}
    (hg' : g' ∈ generatePolygon n v f g) (hf : f ∈ nonFinals g)
    (hv : v ∈ f.vertices) (h3 : 3 ≤ n) (hn : n < 4 + p) :
    g' ∈ next_plane0 p g := by
  have hfin : ¬ g.final = true := by
    intro h
    unfold Graph.final at h
    rw [List.isEmpty_iff] at h
    rw [h] at hf
    exact List.not_mem_nil hf
  have hr : n ∈ List.range' 3 (maxGon p - 2) :=
    List.mem_range'.mpr ⟨n - 3, by unfold maxGon; omega, by omega⟩
  unfold next_plane0
  rw [if_neg hfin]
  exact List.mem_flatMap.mpr ⟨f, hf,
    List.mem_flatMap.mpr ⟨v, hv, List.mem_flatMap.mpr ⟨n, hr, hg'⟩⟩⟩

/-- PlaneProps.thy: next_plane0_nonfinals -/
theorem next_plane0_nonfinals {p : Nat} {g g' : Graph}
    (h : g' ∈ next_plane0 p g) : nonFinals g ≠ [] := by
  unfold next_plane0 at h
  by_cases hf : g.final = true
  · rw [if_pos hf] at h
    exact absurd h List.not_mem_nil
  · rw [if_neg hf] at h
    intro hnf
    rw [hnf, List.flatMap_nil] at h
    exact List.not_mem_nil h

/-- PlaneProps.thy: next_plane0_ex -/
theorem next_plane0_ex {p : Nat} {g g' : Graph}
    (h : g' ∈ next_plane0 p g) :
    ∃ f ∈ nonFinals g, ∃ v ∈ f.vertices,
      ∃ i ∈ List.range' 3 (maxGon p - 2), g' ∈ generatePolygon i v f g := by
  have hfin : ¬ g.final = true := by
    intro hf
    unfold next_plane0 at h
    rw [if_pos hf] at h
    exact List.not_mem_nil h
  unfold next_plane0 at h
  rw [if_neg hfin] at h
  simp only [List.mem_flatMap] at h
  exact h

/-- PlaneProps.thy: step_outside2 -/
theorem step_outside2 {p : Nat} {g g' : Graph}
    (pl : inv g) (h : g' ∈ next_plane0 p g) (hfin : ¬ g'.final = true) :
    g'.faces.length ≠ 2 := by
  have mgp := inv_mgp pl
  have h2 := inv_two_faces pl
  have hne := inv_finals_nonempty pl
  have s1 := len_faces_sum g
  have s2 := len_faces_sum g'
  have hn0 : (nonFinals g).length ≠ 0 := by
    intro e
    exact next_plane0_nonfinals h (List.length_eq_zero_iff.mp e)
  have hn0' : (nonFinals g').length ≠ 0 := by
    intro e
    apply hfin
    unfold Graph.final
    rw [List.isEmpty_iff]
    exact List.length_eq_zero_iff.mp e
  have hfg : (finals g).length ≠ 0 := by
    intro e
    exact hne (List.length_eq_zero_iff.mp e)
  obtain ⟨hfi, hnf⟩ := next_plane0_incr_faces mgp h
  omega

/-! ### Increasing final faces -/

/-- PlaneProps.thy: set_finals_splitFace (membership form of the set equality) -/
theorem set_finals_splitFace {g : Graph} {u v : Vertex} {f : Face} {vs : List Vertex}
    (hf : f ∈ g.faces) (hfin : f.final = false) (x : Face) :
    x ∈ finals (splitFace g u v f vs).2.2 ↔ x ∈ finals g := by
  have h1 : (splitFace g u v f vs).2.2.faces =
      replace f [(split_face f u v vs).2] g.faces ++ [(split_face f u v vs).1] := rfl
  have hf2 : Face.final (split_face f u v vs).2 = false := rfl
  have hf1 : Face.final (split_face f u v vs).1 = false := rfl
  constructor
  · intro hx
    simp only [finals, h1, List.filter_append, List.mem_append, List.mem_filter] at hx
    rcases hx with ⟨hx, hxf⟩ | ⟨hx, hxf⟩
    · rcases replace5 hx with hxs | hx2
      · exact List.mem_filter.mpr ⟨hxs, hxf⟩
      · rw [List.mem_singleton] at hx2
        subst hx2
        rw [hf2] at hxf
        exact Bool.noConfusion hxf
    · rw [List.mem_singleton] at hx
      subst hx
      rw [hf1] at hxf
      exact Bool.noConfusion hxf
  · intro hx
    rw [finals, List.mem_filter] at hx
    have hne : f ≠ x := by
      intro e
      subst e
      rw [hx.2] at hfin
      exact Bool.noConfusion hfin
    simp only [finals, h1, List.filter_append, List.mem_append, List.mem_filter]
    exact Or.inl ⟨replace4 hx.1 hne, hx.2⟩

/-- PlaneProps.thy: next_plane0_finals_incr -/
theorem next_plane0_finals_incr {p : Nat} {g g' : Graph} {f : Face}
    (h : g' ∈ next_plane0 p g) (hf : f ∈ finals g) : f ∈ finals g' := by
  obtain ⟨fn, hfn, v, -, i, -, hg'⟩ := next_plane0_ex h
  have hfnf : fn.final = false := by
    have h2 := (List.mem_filter.mp hfn).2
    cases hb : fn.final with
    | false => rfl
    | true => rw [hb] at h2; exact Bool.noConfusion h2
  simp only [generatePolygon, List.mem_map] at hg'
  obtain ⟨ovs, -, hgs⟩ := hg'
  subst hgs
  exact subdivFace_pres_finals hf hfnf

/-- PlaneProps.thy: next_plane0_finals_subset -/
theorem next_plane0_finals_subset {p : Nat} {g g' : Graph}
    (h : g' ∈ next_plane0 p g) :
    {f | f ∈ finals g} ⊆ {f | f ∈ finals g'} :=
  fun f hf => next_plane0_finals_incr h hf

/-- PlaneProps.thy: next_plane0_final_mono -/
theorem next_plane0_final_mono {p : Nat} {g g' : Graph} {f : Face}
    (h : g' ∈ next_plane0 p g) (hf : f ∈ g.faces) (hfin : f.final = true) :
    f ∈ g'.faces :=
  (List.mem_filter.mp (next_plane0_finals_incr h (List.mem_filter.mpr ⟨hf, hfin⟩))).1

/-! ### Increasing vertices -/

/-- PlaneProps.thy: next_plane0_vertices_subset (membership form of the
inclusion `𝒱 g ⊆ 𝒱 g'`) -/
theorem next_plane0_vertices_subset {p : Nat} {g g' : Graph}
    (h : g' ∈ next_plane0 p g) (mgp : minGraphProps g) :
    ∀ v ∈ g.vertices, v ∈ g'.vertices := by
  refine next_plane0_incr (P := fun g g' => ∀ v ∈ g.vertices, v ∈ g'.vertices)
    (Q := fun g g' => ∀ v ∈ g.vertices, v ∈ g'.vertices) ?_ ?_ ?_ mgp h
  · intro x y z hxy hyz v hv
    exact hyz v (hxy v hv)
  · intro f' g' hf' hfin' v hv
    rw [vertices_makeFaceFinal]
    exact hv
  · intro g' u' v' f' vs' hpre v hv
    have hvr : v ∈ List.range g'.countVertices := hv
    have hlt := List.mem_range.mp hvr
    show v ∈ List.range (g'.countVertices + vs'.length)
    exact List.mem_range.mpr (by omega)

/-! ### Increasing vertex degrees -/

/-- Auxiliary (no direct Isabelle counterpart; in Isabelle the length
computations go through by `simp`): `replace` with a nonempty replacement
list does not decrease the length. -/
private theorem length_le_length_replace {α : Type*} [BEq α] {x : α} {ys : List α}
    (h : 1 ≤ ys.length) : ∀ xs : List α, xs.length ≤ (replace x ys xs).length := by
  intro xs
  induction xs with
  | nil => simp [replace]
  | cons z zs ih =>
    simp only [replace, List.length_cons]
    by_cases hz : (z == x) = true
    · rw [if_pos hz, List.length_append]
      omega
    · rw [if_neg hz, List.length_cons]
      omega

/-- Auxiliary: `replacefacesAt2` with a nonempty replacement list does not
decrease the length of any entry. -/
private theorem length_le_replacefacesAt2 {ns : List Nat} {oldf : Face}
    {newfs : List Face} (hnew : 1 ≤ newfs.length) (F : List (List Face)) (v : Nat) :
    F[v]!.length ≤ (replacefacesAt2 ns oldf newfs F)[v]!.length := by
  induction ns generalizing F with
  | nil => exact le_refl _
  | cons n ns ih =>
    simp only [replacefacesAt2]
    by_cases h : n < F.length
    · rw [if_pos h]
      by_cases hvn : v = n
      · subst hvn
        refine le_trans ?_ (ih (F.set v (replace oldf newfs F[v]!)))
        rw [getElem!_set_self h]
        exact length_le_length_replace hnew _
      · refine le_trans ?_ (ih (F.set n (replace oldf newfs F[n]!)))
        rw [getElem!_set_ne hvn]
    · rw [if_neg h]
      exact ih F

/-- Auxiliary: `replacefacesAt` with a nonempty replacement list does not
decrease the length of any entry. -/
private theorem length_le_replacefacesAt {ns : List Nat} {oldf : Face}
    {newfs : List Face} (hnew : 1 ≤ newfs.length) (F : List (List Face)) (v : Nat) :
    F[v]!.length ≤ (replacefacesAt ns oldf newfs F)[v]!.length := by
  rw [replacefacesAt_eq]
  exact length_le_replacefacesAt2 hnew F v

/-- Auxiliary: `replacefacesAt` preserves the list length. -/
private theorem length_replacefacesAt {ns : List Nat} {oldf : Face}
    {newfs : List Face} (F : List (List Face)) :
    (replacefacesAt ns oldf newfs F).length = F.length := by
  rw [replacefacesAt_eq, replacefacesAt2_length]

/-- Auxiliary: the `faceListAt` of a `splitFace` result dominates the original
one, entrywise. -/
private theorem faceListAt_splitFace_ge {g : Graph} {u v : Vertex} {f : Face}
    {vs : List Vertex} :
    g.faceListAt.length ≤ (splitFace g u v f vs).2.2.faceListAt.length ∧
      ∀ i < g.faceListAt.length,
        g.faceListAt[i]!.length ≤ (splitFace g u v f vs).2.2.faceListAt[i]!.length := by
  have key : (splitFace g u v f vs).2.2.faceListAt =
      replacefacesAt [v] f [(split_face f u v vs).1, (split_face f u v vs).2]
        (replacefacesAt [u] f [(split_face f u v vs).2, (split_face f u v vs).1]
          (replacefacesAt (between f.vertices v u) f [(split_face f u v vs).2]
            (replacefacesAt (between f.vertices u v) f [(split_face f u v vs).1]
              g.faceListAt))) ++
        List.replicate vs.length [(split_face f u v vs).1, (split_face f u v vs).2] :=
    rfl
  rw [key]
  constructor
  · rw [List.length_append]
    have e := length_replacefacesAt (ns := [v]) (oldf := f)
      (newfs := [(split_face f u v vs).1, (split_face f u v vs).2])
    simp only [e, length_replacefacesAt]
    omega
  · intro i hi
    have hlen : i < (replacefacesAt [v] f
        [(split_face f u v vs).1, (split_face f u v vs).2]
        (replacefacesAt [u] f [(split_face f u v vs).2, (split_face f u v vs).1]
          (replacefacesAt (between f.vertices v u) f [(split_face f u v vs).2]
            (replacefacesAt (between f.vertices u v) f [(split_face f u v vs).1]
              g.faceListAt)))).length := by
      simp only [length_replacefacesAt]
      exact hi
    have e : (replacefacesAt [v] f [(split_face f u v vs).1, (split_face f u v vs).2]
          (replacefacesAt [u] f [(split_face f u v vs).2, (split_face f u v vs).1]
            (replacefacesAt (between f.vertices v u) f [(split_face f u v vs).2]
              (replacefacesAt (between f.vertices u v) f [(split_face f u v vs).1]
                g.faceListAt))) ++
          List.replicate vs.length
            [(split_face f u v vs).1, (split_face f u v vs).2])[i]! =
        (replacefacesAt [v] f [(split_face f u v vs).1, (split_face f u v vs).2]
          (replacefacesAt [u] f [(split_face f u v vs).2, (split_face f u v vs).1]
            (replacefacesAt (between f.vertices v u) f [(split_face f u v vs).2]
              (replacefacesAt (between f.vertices u v) f [(split_face f u v vs).1]
                g.faceListAt))))[i]! := by
      rw [getElem!_pos _ i (by rw [List.length_append]; omega),
        List.getElem_append_left hlen, ← getElem!_pos _ i hlen]
    rw [e]
    exact (length_le_replacefacesAt (by simp) g.faceListAt i).trans
      ((length_le_replacefacesAt (by simp) _ i).trans
        ((length_le_replacefacesAt (by simp) _ i).trans
          (length_le_replacefacesAt (by simp) _ i)))

/-- PlaneProps.thy: next_plane0_incr_faceListAt -/
theorem next_plane0_incr_faceListAt {p : Nat} {g g' : Graph}
    (h : g' ∈ next_plane0 p g) (mgp : minGraphProps g) :
    g.faceListAt.length ≤ g'.faceListAt.length ∧
      ∀ v < g.faceListAt.length,
        g.faceListAt[v]!.length ≤ g'.faceListAt[v]!.length := by
  refine next_plane0_incr
    (P := fun g g' => g.faceListAt.length ≤ g'.faceListAt.length ∧
      ∀ v < g.faceListAt.length, g.faceListAt[v]!.length ≤ g'.faceListAt[v]!.length)
    (Q := fun g g' => g.faceListAt.length ≤ g'.faceListAt.length ∧
      ∀ v < g.faceListAt.length, g.faceListAt[v]!.length ≤ g'.faceListAt[v]!.length)
    ?_ ?_ ?_ mgp h
  · intro x y z hxy hyz
    obtain ⟨h1, h2⟩ := hxy
    obtain ⟨h3, h4⟩ := hyz
    exact ⟨h1.trans h3, fun v hv => (h2 v hv).trans (h4 v (hv.trans_le h1))⟩
  · intro f' g' hf' hfin'
    constructor
    · show g'.faceListAt.length ≤ (g'.faceListAt.map (makeFaceFinalFaceList f')).length
      rw [List.length_map]
    · intro v hv
      show g'.faceListAt[v]!.length ≤
        (g'.faceListAt.map (makeFaceFinalFaceList f'))[v]!.length
      rw [getElem!_pos _ v hv, getElem!_pos _ v (by rw [List.length_map]; exact hv),
        List.getElem_map, makeFaceFinalFaceList, length_replace1]
  · intro g' u' v' f' vs' hpre
    exact faceListAt_splitFace_ge

/-- PlaneProps.thy: next_plane0_incr_degree -/
theorem next_plane0_incr_degree {p : Nat} {g g' : Graph} {v : Vertex}
    (h : g' ∈ next_plane0 p g) (mgp : minGraphProps g) (hv : v ∈ g.vertices) :
    degree g v ≤ degree g' v := by
  obtain ⟨hlen, hle⟩ := next_plane0_incr_faceListAt h mgp
  have hlt : v < g.faceListAt.length := by
    rw [minGraphProps4 mgp]
    exact List.mem_range.mp hv
  have hlt' : v < g'.faceListAt.length := hlt.trans_le hlen
  have e1 : g.facesAt v = g.faceListAt[v]! :=
    (List.getElem_eq_getD ([] : List Face)).symm.trans (getElem!_pos _ v hlt).symm
  have e2 : g'.facesAt v = g'.faceListAt[v]! :=
    (List.getElem_eq_getD ([] : List Face)).symm.trans (getElem!_pos _ v hlt').symm
  show (g.facesAt v).length ≤ (g'.facesAt v).length
  rw [e1, e2]
  exact hle v hlt

/-! ### Increasing `except` -/

/-- PlaneProps.thy: next_plane0_incr_except -/
theorem next_plane0_incr_except {p : Nat} {g g' : Graph} {v : Vertex}
    (h : g' ∈ next_plane0 p g) (pl : inv g) (hv : v ∈ g.vertices) :
    except g v ≤ except g' v := by
  have inv' : inv g' := inv_inv_next_plane0 g g' h pl
  have mgp := inv_mgp pl
  have mgp' := inv_mgp inv'
  have hvg' : v ∈ g'.vertices := next_plane0_vertices_subset h mgp v hv
  have dist : ((g.facesAt v).filter
      (fun f => f.final && decide (5 ≤ f.vertices.length))).Nodup :=
    (mgp_dist_facesAt mgp hv).filter _
  show ((g.facesAt v).filter
      (fun f => f.final && decide (5 ≤ f.vertices.length))).length ≤
    ((g'.facesAt v).filter (fun f => f.final && decide (5 ≤ f.vertices.length))).length
  apply List.Subperm.length_le
  apply List.Nodup.subperm dist
  intro f hf
  rw [List.mem_filter] at hf
  obtain ⟨hfAt, hPf⟩ := hf
  rw [Bool.and_eq_true] at hPf
  obtain ⟨hfin, h5⟩ := hPf
  have hfg : f ∈ g.faces := minGraphProps5 mgp hv hfAt
  have hvf : v ∈ f.vertices := minGraphProps6 mgp hv hfAt
  have hfin' : f ∈ finals g := List.mem_filter.mpr ⟨hfg, hfin⟩
  have hfg' : f ∈ g'.faces :=
    (List.mem_filter.mp (next_plane0_finals_incr h hfin')).1
  exact List.mem_filter.mpr ⟨minGraphProps7 mgp' hfg' hvf, by
    rw [Bool.and_eq_true]; exact ⟨hfin, h5⟩⟩

/-! ### Increasing edges -/

/-- PlaneProps.thy: next_plane0_set_edges_subset -/
theorem next_plane0_set_edges_subset {p : Nat} {g g' : Graph}
    (mgp : minGraphProps g) (h : g' ∈ next_plane0 p g) :
    g.edges ⊆ g'.edges := by
  refine next_plane0_incr (P := fun g g' => g.edges ⊆ g'.edges)
    (Q := fun g g' => g.edges ⊆ g'.edges) ?_ ?_ ?_ mgp h
  · intro x y z hxy hyz
    exact Set.Subset.trans hxy hyz
  · intro f' g' hf' hfin'
    rw [edges_makeFaceFinal]
  · intro g' u' v' f' vs' hpre
    exact snd_snd_splitFace_edges_incr hpre

/-! ### Increasing final vertices -/

/-- PlaneProps.thy: next_plane0_incr_finV -/
theorem next_plane0_incr_finV {p : Nat} {g g' : Graph}
    (h : g' ∈ next_plane0 p g) (mgp : minGraphProps g) :
    ∀ v ∈ g.vertices, v ∈ g'.vertices ∧
      ((∀ f ∈ g.faces, v ∈ f.vertices → f.final = true) →
        ∀ f ∈ g'.faces, v ∈ f.vertices → f ∈ g.faces) := by
  refine next_plane0_incr
    (P := fun g g' => ∀ v ∈ g.vertices, v ∈ g'.vertices ∧
      ((∀ f ∈ g.faces, v ∈ f.vertices → f.final = true) →
        ∀ f ∈ g'.faces, v ∈ f.vertices → f ∈ g.faces))
    (Q := fun g g' => ∀ v ∈ g.vertices, v ∈ g'.vertices ∧
      ((∀ f ∈ g.faces, v ∈ f.vertices → f.final = true) →
        ∀ f ∈ g'.faces, v ∈ f.vertices → f ∈ g.faces))
    ?_ ?_ ?_ mgp h
  · intro x y z hxy hyz w hw
    obtain ⟨h1, h2⟩ := hxy w hw
    obtain ⟨h3, h4⟩ := hyz w h1
    refine ⟨h3, fun H f' hf' hw' => ?_⟩
    have h5 : ∀ f ∈ y.faces, w ∈ f.vertices → f.final = true :=
      fun f hf hwf => H f (h2 H f hf hwf) hwf
    exact h2 H f' (h4 h5 f' hf' hw') hw'
  · intro f' g' hf' hfin' w hw
    refine ⟨by rw [vertices_makeFaceFinal]; exact hw, ?_⟩
    intro H f'' hf'' hw''
    show f'' ∈ g'.faces
    rcases replace5 hf'' with hf2 | hf2
    · exact hf2
    · rw [List.mem_singleton] at hf2
      subst hf2
      exfalso
      have h1 := H f' hf' hw''
      rw [hfin'] at h1
      exact Bool.noConfusion h1
  · intro g' u' v' f' vs' hpre
    obtain ⟨hfg', hfin', -, -, hgnin, -, hu, hv', -, -⟩ := hpre
    intro w hw
    have hlt : w < g'.countVertices := List.mem_range.mp hw
    have hpart1 : w ∈ (splitFace g' u' v' f' vs').2.2.vertices := by
      show w ∈ List.range (g'.countVertices + vs'.length)
      exact List.mem_range.mpr (Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _))
    refine ⟨hpart1, ?_⟩
    intro H f'' hf'' hw''
    have hfaces : (splitFace g' u' v' f' vs').2.2.faces =
        replace f' [(split_face f' u' v' vs').2] g'.faces ++
          [(split_face f' u' v' vs').1] := rfl
    rw [hfaces] at hf''
    have contra : w ∈ f'.vertices → False := fun hx => by
      have h1 := H f' hfg' hx
      rw [hfin'] at h1
      exact Bool.noConfusion h1
    have hnotvs : w ∉ vs' := hgnin w hw
    rcases List.mem_append.mp hf'' with hf'' | hf''
    · rcases replace5 hf'' with hf2 | hf2
      · exact hf2
      · rw [List.mem_singleton] at hf2
        subst hf2
        exfalso
        have hverts : (split_face f' u' v' vs').2.vertices =
            ([v'] ++ between f'.vertices v' u' ++ [u']) ++ vs' := rfl
        rw [hverts] at hw''
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at hw''
        rcases hw'' with ((rfl | hb) | rfl) | hvs
        · exact contra hv'
        · exact contra (inbetween_inset hb)
        · exact contra hu
        · exact hnotvs hvs
    · rw [List.mem_singleton] at hf''
      subst hf''
      exfalso
      have hverts : (split_face f' u' v' vs').1.vertices =
          vs'.reverse ++ ([u'] ++ between f'.vertices u' v' ++ [v']) := rfl
      rw [hverts] at hw''
      simp only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, List.mem_reverse] at hw''
      rcases hw'' with hvs | ((rfl | hb) | rfl)
      · exact hnotvs hvs
      · exact contra hu
      · exact contra (inbetween_inset hb)
      · exact contra hv'

/-- PlaneProps.thy: next_plane0_finalVertex_mono -/
theorem next_plane0_finalVertex_mono {p : Nat} {g g' : Graph} {u : Vertex}
    (h : g' ∈ next_plane0 p g) (pl : inv g) (hu : u ∈ g.vertices)
    (hfv : finalVertex g u = true) : finalVertex g' u = true := by
  have inv' : inv g' := inv_inv_next_plane0 g g' h pl
  have mgp := inv_mgp pl
  have hug' : u ∈ g'.vertices := next_plane0_vertices_subset h mgp u hu
  rw [finalVertex, List.all_eq_true] at hfv ⊢
  intro f hf
  have hf1 : f ∈ g'.faces ∧ u ∈ f.vertices :=
    Set.ext_iff.mp (minGraphProps_facesAt_eq (inv_mgp inv') hug') f |>.mp hf
  have H : ∀ f' ∈ g.faces, u ∈ f'.vertices → f'.final = true := by
    intro f' hf' hu'
    have hmem : f' ∈ g.facesAt u :=
      Set.ext_iff.mp (minGraphProps_facesAt_eq mgp hu) f' |>.mpr ⟨hf', hu'⟩
    exact hfv f' hmem
  have hfin2 : f ∈ g.faces := (next_plane0_incr_finV h mgp u hu).2 H f hf1.1 hf1.2
  exact H f hfin2 hf1.2

/-! ### Preservation of `facesAt` at final vertices -/

/-- PlaneProps.thy: next_plane0_finalVertex_facesAt_eq -/
theorem next_plane0_finalVertex_facesAt_eq {p : Nat} {g g' : Graph} {v : Vertex}
    (h : g' ∈ next_plane0 p g) (pl : inv g) (hv : v ∈ g.vertices)
    (hfv : finalVertex g v = true) :
    {f | f ∈ g'.facesAt v} = {f | f ∈ g.facesAt v} := by
  have inv' : inv g' := inv_inv_next_plane0 g g' h pl
  have mgp := inv_mgp pl
  have hvg' : v ∈ g'.vertices := next_plane0_vertices_subset h mgp v hv
  rw [minGraphProps_facesAt_eq (inv_mgp inv') hvg', minGraphProps_facesAt_eq mgp hv]
  rw [finalVertex, List.all_eq_true] at hfv
  ext f
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hf
    have H : ∀ f' ∈ g.faces, v ∈ f'.vertices → f'.final = true := by
      intro f' hf' hv'
      have hmem : f' ∈ g.facesAt v :=
        Set.ext_iff.mp (minGraphProps_facesAt_eq mgp hv) f' |>.mpr ⟨hf', hv'⟩
      exact hfv f' hmem
    exact ⟨(next_plane0_incr_finV h mgp v hv).2 H f hf.1 hf.2, hf.2⟩
  · intro hf
    have hmem : f ∈ g.facesAt v :=
      Set.ext_iff.mp (minGraphProps_facesAt_eq mgp hv) f |>.mpr ⟨hf.1, hf.2⟩
    exact ⟨next_plane0_final_mono h hf.1 (hfv f hmem), hf.2⟩

/-- PlaneProps.thy: next_plane0_len_filter_eq -/
theorem next_plane0_len_filter_eq {p : Nat} {g g' : Graph} {v : Vertex}
    (P : Face → Bool)
    (h : g' ∈ next_plane0 p g) (pl : inv g) (hv : v ∈ g.vertices)
    (hfv : finalVertex g v = true) :
    ((g'.facesAt v).filter P).length = ((g.facesAt v).filter P).length := by
  have inv' : inv g' := inv_inv_next_plane0 g g' h pl
  have mgp := inv_mgp pl
  have hvg' : v ∈ g'.vertices := next_plane0_vertices_subset h mgp v hv
  have heq := next_plane0_finalVertex_facesAt_eq h pl hv hfv
  have d1 : (g.facesAt v).Nodup := mgp_dist_facesAt mgp hv
  have d2 : (g'.facesAt v).Nodup := mgp_dist_facesAt (inv_mgp inv') hvg'
  have hts : (g'.facesAt v).toFinset = (g.facesAt v).toFinset := by
    apply Finset.ext
    intro f
    simp only [List.mem_toFinset]
    exact Set.ext_iff.mp heq f
  rw [← List.toFinset_card_of_nodup (d1.filter P),
    ← List.toFinset_card_of_nodup (d2.filter P),
    List.toFinset_filter, List.toFinset_filter, hts]

/-! ### `maxGon` faces along `next_plane0` -/

/-- RTranCl.thy: RTranCl_induct (one-step induction form; specialized to
`Graph` like `Kepler.Graphs.RTranCl` itself). -/
theorem RTranCl_induct {succs : Graph → List Graph} {P : Graph → Prop}
    {h h' : Graph} (hr : RTranCl succs h h') (hh : P h)
    (step : ∀ g g', g' ∈ succs g → P g → P g') : P h' := by
  revert hh
  induction hr with
  | refl => exact id
  | succs hg _ ih => exact fun hh => ih (step _ _ hg hh)

/-- PlaneProps.thy: Seed_max_final_ex -/
theorem Seed_max_final_ex {p : Nat} :
    ∃ f ∈ finals (Seed p), f.vertices.length = maxGon p :=
  graph_max_final_ex (maxGon p)

/-- PlaneProps.thy: max_face_ex -/
theorem max_face_ex {p : Nat} {g : Graph}
    (h : RTranCl (next_plane0 p) (Seed p) g) :
    ∃ f ∈ finals g, f.vertices.length = maxGon p := by
  refine RTranCl_induct (P := fun g => ∃ f ∈ finals g, f.vertices.length = maxGon p)
    h Seed_max_final_ex ?_
  intro g g' hg' hf
  obtain ⟨f, hf, hlen⟩ := hf
  exact ⟨f, next_plane0_finals_incr hg' hf, hlen⟩

/-! ### `between` and `verticesFrom` -/

/-- ListAux.thy: fst_splitAt_last (helper for `between_last`; the `ListAux.thy`
lemma was not needed by the earlier ported theories). -/
private theorem fst_splitAt_last {α : Type*} [BEq α] [LawfulBEq α] [Inhabited α]
    {vs : List α} (hd : vs.Nodup) : (splitAt vs.getLast! vs).1 = vs.dropLast := by
  induction vs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x _ =>
    rw [getLast!_concat]
    have hxs : x ∉ xs := fun xm =>
      (List.nodup_append.mp hd).2.2 x xm x (List.mem_singleton_self x) rfl
    have hs : splitAt x [x] = ([], []) := by
      show splitAtRec x [] [x] = ([], [])
      rw [splitAtRec, if_pos (beq_self_eq_true x)]
    rw [splitAt_append_of_not_mem hxs [x], hs]
    show xs ++ [] = (xs ++ [x]).dropLast
    rw [List.append_nil, List.dropLast_concat]

/-- PlaneProps.thy: between_last -/
theorem between_last {f : Face} {u : Vertex}
    (hd : f.vertices.Nodup) (hu : u ∈ f.vertices) :
    between f.vertices u (verticesFrom f u).getLast! =
      (verticesFrom f u).tail.dropLast := by
  obtain ⟨a, b, hab⟩ : ∃ a b, (a, b) = splitAt u f.vertices := ⟨_, _, rfl⟩
  have hsplit : f.vertices = a ++ u :: b := splitAt_split hu hab
  have hd' : (a ++ u :: b).Nodup := hsplit ▸ hd
  obtain ⟨hda, hdub, hdisj⟩ := List.nodup_append.mp hd'
  obtain ⟨hub, hdb⟩ := List.nodup_cons.mp hdub
  have ha1 : (splitAt u f.vertices).1 = a := congrArg Prod.fst hab.symm
  have hb2 : (splitAt u f.vertices).2 = b := congrArg Prod.snd hab.symm
  have hvf : verticesFrom f u = (u :: b) ++ a := by
    show u :: (splitAt u f.vertices).2 ++ (splitAt u f.vertices).1 = _
    rw [ha1, hb2]
  have htail : ((u :: b) ++ a).tail = b ++ a := by
    rw [List.cons_append, List.tail_cons]
  rw [hvf, between_def, ha1, hb2, htail]
  by_cases ha : a = []
  · subst ha
    rw [List.append_nil, List.append_nil]
    by_cases hb : b = []
    · subst hb
      rw [if_neg (by rw [List.contains_iff_mem]; exact List.not_mem_nil)]
      rfl
    · have hgl : (u :: b).getLast! = b.getLast! := getLast!_cons_of_ne_nil hb
      rw [hgl, if_pos (by rw [List.contains_iff_mem]; exact getLast!_mem hb),
        fst_splitAt_last hdb]
  · have hgl : ((u :: b) ++ a).getLast! = a.getLast! := getLast!_append_right _ ha
    have hwa : a.getLast! ∈ a := getLast!_mem ha
    have hwb : a.getLast! ∉ b := fun hm =>
      hdisj _ hwa _ (List.mem_cons_of_mem u hm) rfl
    rw [hgl, if_neg (by rw [List.contains_iff_mem]; exact hwb), fst_splitAt_last hda,
      List.dropLast_append_of_ne_nil ha]

/- Not yet ported (left for a follow-up run; the file compiles without them):
- `new_edge_subdivFace'` (PlaneProps.thy lines 358–500)
- `dist_edges_subdivFace'` (lines 503–515, depends on `new_edge_subdivFace'`)
- `final_subdivFace'` (lines 529–669)
All other lemmas of `PlaneProps.thy` are ported above. -/

end Kepler.Graphs

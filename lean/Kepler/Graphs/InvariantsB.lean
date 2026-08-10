/-
Port of block B (lines 716–1912) of the Isabelle AFP "Flyspeck-Tame" theory
`Invariants.thy`: `subsection Invariants of splitFace`.

Source: `reference/afp-flyspeck-tame/Invariants.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Conventions follow `InvariantsA.lean`.
-/
import Kepler.Graphs.InvariantsA

namespace Kepler.Graphs

/-! ### Invariants of `splitFace` -/

/-- Auxiliary (inline in `splitFace_holds_minGraphProps'` via
`pre_FaceDiv_between1`): the first new face of `split_face` has more than two
vertices. -/
theorem splitFace_length_f12 {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {vs : List Vertex} (pre : pre_splitFace g ram₁ ram₂ oldF vs) :
    2 < (split_face oldF ram₁ ram₂ vs).1.vertices.length := by
  show 2 < (vs.reverse ++ (ram₁ :: between oldF.vertices ram₁ ram₂ ++ [ram₂])).length
  by_cases hvs : vs = []
  · subst hvs
    have hpos : 0 < (between oldF.vertices ram₁ ram₂).length :=
      List.length_pos_iff.mpr (pre_FaceDiv_between1 pre)
    simp only [List.reverse_nil, List.nil_append, List.length_cons, List.length_append,
      List.length_nil]
    omega
  · have hpos : 0 < vs.length := List.length_pos_iff.mpr hvs
    simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
    omega

/-- Auxiliary (inline in `splitFace_holds_minGraphProps'` via
`pre_FaceDiv_between2`): the second new face of `split_face` has more than two
vertices. -/
theorem splitFace_length_f21 {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {vs : List Vertex} (pre : pre_splitFace g ram₁ ram₂ oldF vs) :
    2 < (split_face oldF ram₁ ram₂ vs).2.vertices.length := by
  show 2 < ((ram₂ :: between oldF.vertices ram₂ ram₁ ++ [ram₁]) ++ vs).length
  by_cases hvs : vs = []
  · subst hvs
    have hpos : 0 < (between oldF.vertices ram₂ ram₁).length :=
      List.length_pos_iff.mpr (pre_FaceDiv_between2 pre)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · have hpos : 0 < vs.length := List.length_pos_iff.mpr hvs
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Invariants.thy: splitFace_holds_minGraphProps' -/
theorem splitFace_holds_minGraphProps' {g' : Graph} {v a : Vertex} {f' : Face}
    {vs : List Vertex} (hpre : pre_splitFace g' v a f' vs) (hmgp : minGraphProps' g') :
    minGraphProps' (splitFace g' v a f' vs).2.2 := by
  intro f hf
  rcases splitFace_split hf with h | h12 | h21
  · exact hmgp f h
  · rw [h12]
    exact ⟨splitFace_length_f12 hpre, splitFace_distinct2 hpre⟩
  · rw [h21]
    exact ⟨splitFace_length_f21 hpre, splitFace_distinct1 hpre⟩

/-- Invariants.thy: splitFace_holds_faceListAt_len -/
theorem splitFace_holds_faceListAt_len {g' : Graph} {v a : Vertex} {f' : Face}
    {vs : List Vertex} (_hpre : pre_splitFace g' v a f' vs) (hmgp : minGraphProps g') :
    faceListAt_len (splitFace g' v a f' vs).2.2 := by
  have h4 : g'.faceListAt.length = g'.countVertices := minGraphProps4 hmgp
  show ((replacefacesAt [a] f' [(split_face f' v a vs).1, (split_face f' v a vs).2]
      (replacefacesAt [v] f' [(split_face f' v a vs).2, (split_face f' v a vs).1]
        (replacefacesAt (between f'.vertices a v) f' [(split_face f' v a vs).2]
          (replacefacesAt (between f'.vertices v a) f' [(split_face f' v a vs).1]
            g'.faceListAt)))) ++
      List.replicate vs.length [(split_face f' v a vs).1, (split_face f' v a vs).2]).length =
    g'.countVertices + vs.length
  simp only [List.length_append, List.length_replicate, replacefacesAt_eq,
    replacefacesAt2_length]
  rw [h4]

/-- Invariants.thy: splitFace_new_f12 -/
theorem splitFace_new_f12 {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF newVs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    f12 ∉ g.faces := by
  intro hf12
  cases newVs with
  | nil =>
    have h1 : (ram₂, ram₁) ∉ g.edges := by
      rcases pre.2.2.2.2.2.2.2.2.2 with ⟨-, -, -, h4⟩ | hne
      · exact h4
      · exact absurd rfl hne
    have h2 : (ram₂, ram₁) ∈ f12.edges := splitFace_empty_ram2_ram1_in_f12 pre spl
    exact h1 ⟨f12, hf12, h2⟩
  | cons v vs' =>
    have hv1 : v ∉ g.vertices := fun hv => pre.2.2.2.2.1 v hv List.mem_cons_self
    have hv2 : v ∈ f12.vertices := splitFace_f12_new_vertices spl List.mem_cons_self
    exact hv1 (minGraphProps9 props hf12 hv2)

/-- Invariants.thy: splitFace_new_f12_norm -/
theorem splitFace_new_f12_norm {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF newVs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    normFace f12 ∉ normFaces g.faces := by
  intro hn
  cases newVs with
  | nil =>
    have h1 : (ram₂, ram₁) ∉ g.edges := by
      rcases pre.2.2.2.2.2.2.2.2.2 with ⟨-, -, -, h4⟩ | hne
      · exact h4
      · exact absurd rfl hne
    have e1 : f12 = (splitFace g ram₁ ram₂ oldF []).1 := congrArg Prod.fst spl
    have dist_f12 : f12.vertices.Nodup := e1 ▸ splitFace_distinct2 pre
    have h2 : (ram₂, ram₁) ∈ f12.edges := splitFace_empty_ram2_ram1_in_f12 pre spl
    have hne12 : f12.vertices ≠ [] := List.ne_nil_of_mem (edges_face_eq.mp h2).2
    obtain ⟨f', hf', hcong⟩ := normFace_in_cong hne12 props hn
    have hed : (ram₂, ram₁) ∈ f'.edges := by
      have hins : is_nextElem f12.vertices ram₂ ram₁ := (is_nextElem_edges_eq dist_f12).mp h2
      have hins' : is_nextElem f'.vertices ram₂ ram₁ := (is_nextElem_congs_eq hcong).mp hins
      exact (is_nextElem_edges_eq ((cong_distinct hcong).mp dist_f12)).mpr hins'
    exact h1 ⟨f', hf', hed⟩
  | cons v vs' =>
    have hv1 : v ∉ g.vertices := fun hv => pre.2.2.2.2.1 v hv List.mem_cons_self
    have hv2 : v ∈ f12.vertices := splitFace_f12_new_vertices spl List.mem_cons_self
    obtain ⟨f', hf', hcong⟩ := normFace_in_cong (List.ne_nil_of_mem hv2) props hn
    have hv3 : v ∈ f'.vertices := (cong_mem hcong).mp hv2
    exact hv1 (minGraphProps9 props hf' hv3)

/-- Invariants.thy: splitFace_new_f21 -/
theorem splitFace_new_f21 {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF newVs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    f21 ∉ g.faces := by
  intro hf21
  cases newVs with
  | nil =>
    have h1 : (ram₁, ram₂) ∉ g.edges := by
      rcases pre.2.2.2.2.2.2.2.2.2 with ⟨-, -, h3, -⟩ | hne
      · exact h3
      · exact absurd rfl hne
    have h2 : (ram₁, ram₂) ∈ f21.edges := splitFace_empty_ram1_ram2_in_f21 pre spl
    exact h1 ⟨f21, hf21, h2⟩
  | cons v vs' =>
    have hv1 : v ∉ g.vertices := fun hv => pre.2.2.2.2.1 v hv List.mem_cons_self
    have hv2 : v ∈ f21.vertices := splitFace_f21_new_vertices spl List.mem_cons_self
    exact hv1 (minGraphProps9 props hf21 hv2)

/-- Invariants.thy: splitFace_new_f21_norm -/
theorem splitFace_new_f21_norm {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF newVs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    normFace f21 ∉ normFaces g.faces := by
  intro hn
  cases newVs with
  | nil =>
    have h1 : (ram₁, ram₂) ∉ g.edges := by
      rcases pre.2.2.2.2.2.2.2.2.2 with ⟨-, -, h3, -⟩ | hne
      · exact h3
      · exact absurd rfl hne
    have e2 : f21 = (splitFace g ram₁ ram₂ oldF []).2.1 := congrArg (fun p => p.2.1) spl
    have dist_f21 : f21.vertices.Nodup := e2 ▸ splitFace_distinct1 pre
    have h2 : (ram₁, ram₂) ∈ f21.edges := splitFace_empty_ram1_ram2_in_f21 pre spl
    have hne21 : f21.vertices ≠ [] := List.ne_nil_of_mem (edges_face_eq.mp h2).2
    obtain ⟨f', hf', hcong⟩ := normFace_in_cong hne21 props hn
    have hed : (ram₁, ram₂) ∈ f'.edges := by
      have hins : is_nextElem f21.vertices ram₁ ram₂ := (is_nextElem_edges_eq dist_f21).mp h2
      have hins' : is_nextElem f'.vertices ram₁ ram₂ := (is_nextElem_congs_eq hcong).mp hins
      exact (is_nextElem_edges_eq ((cong_distinct hcong).mp dist_f21)).mpr hins'
    exact h1 ⟨f', hf', hed⟩
  | cons v vs' =>
    have hv1 : v ∉ g.vertices := fun hv => pre.2.2.2.2.1 v hv List.mem_cons_self
    have hv2 : v ∈ f21.vertices := splitFace_f21_new_vertices spl List.mem_cons_self
    obtain ⟨f', hf', hcong⟩ := normFace_in_cong (List.ne_nil_of_mem hv2) props hn
    have hv3 : v ∈ f'.vertices := (cong_mem hcong).mp hv2
    exact hv1 (minGraphProps9 props hf' hv3)

/-- Invariants.thy: splitFace_f21_oldF_neq -/
theorem splitFace_f21_oldF_neq {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF newVs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    oldF ≠ f21 :=
  fun h => splitFace_new_f21 pre props spl (h ▸ pre.1)

/-- Invariants.thy: splitFace_f12_oldF_neq -/
theorem splitFace_f12_oldF_neq {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF newVs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    oldF ≠ f12 :=
  fun h => splitFace_new_f12 pre props spl (h ▸ pre.1)

/-- Invariants.thy: splitFace_f12_f21_neq_norm -/
theorem splitFace_f12_f21_neq_norm {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {vs : List Vertex}
    (pre : pre_splitFace g ram₁ ram₂ oldF vs) (props : minGraphProps g)
    (spl : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF vs) :
    normFace f12 ≠ normFace f21 := by
  have hsplit : (f12, f21) = split_face oldF ram₁ ram₂ vs :=
    splitFace_split_face pre.1 spl
  have e1 : f12 = (split_face oldF ram₁ ram₂ vs).1 := congrArg Prod.fst hsplit
  have e2 : f21 = (split_face oldF ram₁ ram₂ vs).2 := congrArg Prod.snd hsplit
  exact split_face_f12_f21_neq_norm (pre_splitFace_pre_split_face pre)
    (minGraphProps2 props pre.1) (e1 ▸ splitFace_length_f12 pre)
    (e2 ▸ splitFace_length_f21 pre) hsplit

/-- Invariants.thy: set_faces_splitFace (membership form of the set equality) -/
theorem set_faces_splitFace {g g' : Graph} {v₁ v₂ : Vertex} {f f₁ f₂ : Face}
    {vs : List Vertex} (mgp : minGraphProps g) (hf : f ∈ g.faces)
    (pre : pre_splitFace g v₁ v₂ f vs)
    (fdg : (f₁, f₂, g') = splitFace g v₁ v₂ f vs) (x : Face) :
    x ∈ g'.faces ↔ x = f₁ ∨ x = f₂ ∨ x ∈ g.faces ∧ x ≠ f := by
  have e1 : f₁ = (split_face f v₁ v₂ vs).1 := congrArg Prod.fst fdg
  have e2 : f₂ = (split_face f v₁ v₂ vs).2 := congrArg (fun p => p.2.1) fdg
  have hfs : g'.faces =
      replace f [(split_face f v₁ v₂ vs).2] g.faces ++ [(split_face f v₁ v₂ vs).1] :=
    congrArg (fun p => p.2.2.faces) fdg
  constructor
  · intro hx
    have hx0 := hx
    rw [hfs] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases replace5 hx with hx | hx
      · refine Or.inr (Or.inr ⟨hx, fun hxf => ?_⟩)
        exact splitFace_delete_oldF fdg (splitFace_f12_oldF_neq pre mgp fdg)
          (splitFace_f21_oldF_neq pre mgp fdg) (minGraphProps11' mgp) (hxf ▸ hx0)
      · exact Or.inr (Or.inl ((List.mem_singleton.mp hx).trans e2.symm))
    · exact Or.inl ((List.mem_singleton.mp hx).trans e1.symm)
  · rintro (rfl | rfl | ⟨hx, hxf⟩)
    · rw [hfs]
      exact List.mem_append_right _ (List.mem_singleton.mpr e1)
    · rw [hfs]
      exact List.mem_append_left _ (replace3 hf (List.mem_singleton.mpr e2))
    · rw [hfs]
      exact List.mem_append_left _ (replace4 hx (Ne.symm hxf))

/-- Invariants.thy: splitFace_holds_faces_subset -/
theorem splitFace_holds_faces_subset {g' : Graph} {v a : Vertex} {f' : Face} {n : Nat}
    (pre_F : pre_splitFace g' v a f' (List.range' g'.countVertices n))
    (mgp : minGraphProps g') :
    faces_subset (splitFace g' v a f' (List.range' g'.countVertices n)).2.2 := by
  have hfs : (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faces =
      replace f' [(split_face f' v a (List.range' g'.countVertices n)).2] g'.faces ++
        [(split_face f' v a (List.range' g'.countVertices n)).1] := rfl
  intro f hf x hx
  rw [splitFace_add_vertices_direct g' v a f' n]
  rw [hfs] at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases replace5 hf with hf | hf
    · exact List.mem_append_left _ (minGraphProps9 mgp hf hx)
    · rw [List.mem_singleton.mp hf] at hx
      have hx' : x ∈ (a :: between f'.vertices a v ++ [v]) ++
          List.range' g'.countVertices n := hx
      rcases List.mem_append.mp hx' with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_append_left _
              (minGraphProps9 mgp pre_F.1 pre_F.2.2.2.2.2.2.2.1)
          · exact List.mem_append_left _ (minGraphProps9 mgp pre_F.1 (inbetween_inset hx))
        · rw [List.mem_singleton.mp hx]
          exact List.mem_append_left _ (minGraphProps9 mgp pre_F.1 pre_F.2.2.2.2.2.2.1)
      · exact List.mem_append_right _ hx
  · rw [List.mem_singleton.mp hf] at hx
    have hx' : x ∈ (List.range' g'.countVertices n).reverse ++
        (v :: between f'.vertices v a ++ [a]) := hx
    rcases List.mem_append.mp hx' with hx | hx
    · exact List.mem_append_right _ (List.mem_reverse.mp hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_append_left _ (minGraphProps9 mgp pre_F.1 pre_F.2.2.2.2.2.2.1)
      · rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ (minGraphProps9 mgp pre_F.1 (inbetween_inset hx))
        · rw [List.mem_singleton.mp hx]
          exact List.mem_append_left _ (minGraphProps9 mgp pre_F.1 pre_F.2.2.2.2.2.2.2.1)

/-- Invariants.thy: splitFace_holds_faces_distinct -/
theorem splitFace_holds_faces_distinct {g' : Graph} {v a : Vertex} {f' : Face} {n : Nat}
    (pre_F : pre_splitFace g' v a f' (List.range' g'.countVertices n))
    (mgp : minGraphProps g') :
    faces_distinct (splitFace g' v a f' (List.range' g'.countVertices n)).2.2 := by
  have hfs : (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faces =
      replace f' [(split_face f' v a (List.range' g'.countVertices n)).2] g'.faces ++
        [(split_face f' v a (List.range' g'.countVertices n)).1] := rfl
  unfold faces_distinct
  rw [hfs]
  show ((replace f' [(split_face f' v a (List.range' g'.countVertices n)).2] g'.faces ++
      [(split_face f' v a (List.range' g'.countVertices n)).1]).map normFace).Nodup
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, List.nodup_singleton _, ?_⟩
  · apply distinct_replace_norm (minGraphProps11 mgp)
    · exact List.nodup_singleton _
    · intro x hx hne
      have hx2 : x = normFace (split_face f' v a (List.range' g'.countVertices n)).2 :=
        List.mem_singleton.mp hne
      exact splitFace_new_f21_norm pre_F mgp rfl (hx2 ▸ hx)
  · intro x hx y hy hxy
    have hy2 : y = normFace (split_face f' v a (List.range' g'.countVertices n)).1 :=
      List.mem_singleton.mp hy
    rw [hxy, hy2] at hx
    rcases normFace_replace_in hx with h | h
    · have h1 : normFace (split_face f' v a (List.range' g'.countVertices n)).1 =
          normFace (split_face f' v a (List.range' g'.countVertices n)).2 :=
        List.mem_singleton.mp h
      exact splitFace_f12_f21_neq_norm pre_F mgp rfl h1
    · exact splitFace_new_f12_norm pre_F mgp rfl h

/-- Invariants.thy: splitFace_holds_edges_sym -/
theorem splitFace_holds_edges_sym {g' : Graph} {v a : Vertex} {f' : Face}
    {ws : List Vertex} (pre_F : pre_splitFace g' v a f' ws) (mgp : minGraphProps g') :
    edges_sym (splitFace g' v a f' ws).2.2 := by
  have hpre : pre_split_face f' v a ws := pre_splitFace_pre_split_face pre_F
  have hfs : (splitFace g' v a f' ws).2.2.faces =
      replace f' [(split_face f' v a ws).2] g'.faces ++ [(split_face f' v a ws).1] := rfl
  have hf' : f' ∈ g'.faces := pre_F.1
  -- An edge of `g'` still occurs (symmetrically placed) in the new graph:
  -- its witness face is transported, replacing `f'` by `f12`/`f21` if needed.
  have transport : ∀ e : Vertex × Vertex, e ∈ g'.edges →
      e ∈ (splitFace g' v a f' ws).2.2.edges := by
    rintro ⟨p, q⟩ hpq
    obtain ⟨G, hG, hpqG⟩ := hpq
    by_cases hGf : G = f'
    · rcases split_face_edges_or (Prod.eta (split_face f' v a ws)) hpre (hGf ▸ hpqG) with h | h
      · exact ⟨(split_face f' v a ws).1, by
          rw [hfs]; exact List.mem_append_right _ List.mem_cons_self, h⟩
      · exact ⟨(split_face f' v a ws).2, by
          rw [hfs]; exact List.mem_append_left _ (replace3 hf' List.mem_cons_self), h⟩
    · exact ⟨G, by rw [hfs]; exact List.mem_append_left _ (replace4 hG (Ne.symm hGf)), hpqG⟩
  have newedge : ∀ e : Vertex × Vertex,
      (e ∈ (split_face f' v a ws).1.edges ∨ e ∈ (split_face f' v a ws).2.edges) →
      e ∈ (splitFace g' v a f' ws).2.2.edges := by
    rintro ⟨p, q⟩ (h | h)
    · exact ⟨(split_face f' v a ws).1, by
        rw [hfs]; exact List.mem_append_right _ List.mem_cons_self, h⟩
    · exact ⟨(split_face f' v a ws).2, by
        rw [hfs]; exact List.mem_append_left _ (replace3 hf' List.mem_cons_self), h⟩
  intro x y hxy
  obtain ⟨F, hF, hxyF⟩ := hxy
  have hiff := split_face_edges_f12_f21_sym hf' hpre (Prod.eta (split_face f' v a ws)) (a := x) (b := y)
  rcases splitFace_split hF with hFg | hF12 | hF21
  · exact transport _ (minGraphProps10 mgp ⟨F, hFg, hxyF⟩)
  · subst hF12
    have h12 : (x, y) ∈ (split_face f' v a ws).1.edges ∨
        (x, y) ∈ (split_face f' v a ws).2.edges := Or.inl hxyF
    rcases hiff.mp h12 with hxyf' | ⟨hyx, -⟩
    · exact transport _ (minGraphProps10 mgp ⟨f', hf', hxyf'⟩)
    · exact newedge _ hyx
  · subst hF21
    have h12 : (x, y) ∈ (split_face f' v a ws).1.edges ∨
        (x, y) ∈ (split_face f' v a ws).2.edges := Or.inr hxyF
    rcases hiff.mp h12 with hxyf' | ⟨hyx, -⟩
    · exact transport _ (minGraphProps10 mgp ⟨f', hf', hxyf'⟩)
    · exact newedge _ hyx

/-- Invariants.thy: vertices_conv_Union_edges2 -/
theorem vertices_conv_Union_edges2 {f : Face} (hd : f.vertices.Nodup) :
    {x | x ∈ f.vertices} = ⋃ p ∈ f.edges, ({p.2} : Set Vertex) := by
  ext x
  constructor
  · intro hx
    exact Set.mem_biUnion (x := (f.prevVertex x, x)) (prevVertex_in_edges hd hx) rfl
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hx
    exact (in_edges_in_vertices hp).2

/-- Invariants.thy: help (1) -/
theorem ne_head!_of_not_mem [Inhabited α] {xs : List α} {x : α} (hxs : xs ≠ [])
    (hx : x ∉ xs) : x ≠ xs.head! :=
  fun h => hx (h.symm ▸ head!_mem hxs)

/-- Invariants.thy: help (2) -/
theorem ne_getLast!_of_not_mem [Inhabited α] {xs : List α} {x : α} (hxs : xs ≠ [])
    (hx : x ∉ xs) : x ≠ xs.getLast! :=
  fun h => hx (h.symm ▸ getLast!_mem hxs)

/-- Invariants.thy: help (3) -/
theorem head!_ne_of_not_mem [Inhabited α] {xs : List α} {x : α} (hxs : xs ≠ [])
    (hx : x ∉ xs) : xs.head! ≠ x :=
  fun h => hx (h ▸ head!_mem hxs)

/-- Invariants.thy: help (4) -/
theorem getLast!_ne_of_not_mem [Inhabited α] {xs : List α} {x : α} (hxs : xs ≠ [])
    (hx : x ∉ xs) : xs.getLast! ≠ x :=
  fun h => hx (h ▸ getLast!_mem hxs)

end Kepler.Graphs

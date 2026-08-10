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

/-- Auxiliary for `splitFace_holds_facesAt_distinct` (the Isabelle proof
case-splits on `x = w`, `x = v` and `x ∈ 𝒱 g ∖ {v, w}`): at an old vertex `x`
of `g`, the face list of the split graph still has distinct normal forms. The
two new faces are abstracted as parameters `f12 f21`. -/
private theorem nodup_normFaces_splitFace_faceListAt {g : Graph} {v w : Vertex}
    {f f12 f21 : Face} (mgp : minGraphProps g) (hvw : v ≠ w)
    (hdf : f.vertices.Nodup) (hv : v < g.countVertices) (hw : w < g.countVertices)
    (new12 : normFace f12 ∉ normFaces g.faces)
    (new21 : normFace f21 ∉ normFaces g.faces) (neq12 : normFace f12 ≠ normFace f21)
    {x : Nat} (hx : x < g.countVertices) :
    (normFaces ((replacefacesAt [w] f [f12, f21]
      (replacefacesAt [v] f [f21, f12]
        (replacefacesAt (between f.vertices w v) f [f21]
          (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt))))[x]!)).Nodup := by
  have hlen1 : (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt).length =
      g.countVertices := by
    rw [replacefacesAt_length]; exact minGraphProps4 mgp
  have hlen2 : (replacefacesAt (between f.vertices w v) f [f21]
      (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt)).length =
      g.countVertices := by
    rw [replacefacesAt_length]; exact hlen1
  have hlen3 : (replacefacesAt [v] f [f21, f12]
      (replacefacesAt (between f.vertices w v) f [f21]
        (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt))).length =
      g.countVertices := by
    rw [replacefacesAt_eq, replacefacesAt2_length]; exact hlen2
  have hmemF : ∀ {y : Nat}, y < g.countVertices → ∀ {F : Face},
      F ∈ g.faceListAt[y]! → F ∈ g.faces := by
    intro y hy F hF
    have hlt : y < g.faceListAt.length := by rw [minGraphProps4 mgp]; exact hy
    rw [getElem!_pos g.faceListAt y hlt] at hF
    have hd : g.facesAt y = g.faceListAt[y] := (List.getElem_eq_getD []).symm
    exact minGraphProps5 mgp (List.mem_range.mpr hy) (hd ▸ hF)
  by_cases hxw : x = w
  · subst x
    have e : (replacefacesAt [w] f [f12, f21]
        (replacefacesAt [v] f [f21, f12]
          (replacefacesAt (between f.vertices w v) f [f21]
            (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt))))[w]! =
        replace f [f12, f21] (g.faceListAt[w]!) := by
      rw [replacefacesAt_nth2 (by rw [hlen3]; exact hw),
        replacefacesAt_notin (show w ∉ [v] from fun h => hvw (List.mem_singleton.mp h).symm),
        replacefacesAt_notin (between_not_r1 hdf),
        replacefacesAt_notin (between_not_r2 hdf)]
    rw [e]
    apply distinct_replace_norm (minGraphProps8a' mgp hw)
    · apply List.nodup_cons.mpr
      refine ⟨?_, List.nodup_singleton _⟩
      simp only [normFaces, List.map_cons, List.map_nil, List.mem_singleton]
      exact neq12
    · intro y hy hyN
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hy
      have hFg : F ∈ g.faces := hmemF hw hF
      simp only [normFaces, List.map_cons, List.map_nil, List.mem_pair]
        at hyN
      rcases hyN with heq | heq
      · exact new12 (heq ▸ normFace_in hFg)
      · exact new21 (heq ▸ normFace_in hFg)
  · by_cases hxv : x = v
    · subst x
      have e : (replacefacesAt [w] f [f12, f21]
          (replacefacesAt [v] f [f21, f12]
            (replacefacesAt (between f.vertices w v) f [f21]
              (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt))))[v]! =
          replace f [f21, f12] (g.faceListAt[v]!) := by
        rw [replacefacesAt_notin (show v ∉ [w] from fun h => hvw (List.mem_singleton.mp h)),
          replacefacesAt_nth2 (by rw [hlen2]; exact hv),
          replacefacesAt_notin (between_not_r2 hdf),
          replacefacesAt_notin (between_not_r1 hdf)]
      rw [e]
      apply distinct_replace_norm (minGraphProps8a' mgp hv)
      · apply List.nodup_cons.mpr
        refine ⟨?_, List.nodup_singleton _⟩
        simp only [normFaces, List.map_cons, List.map_nil, List.mem_singleton]
        exact Ne.symm neq12
      · intro y hy hyN
        obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hy
        have hFg : F ∈ g.faces := hmemF hv hF
        simp only [normFaces, List.map_cons, List.map_nil, List.mem_pair]
          at hyN
        rcases hyN with heq | heq
        · exact new21 (heq ▸ normFace_in hFg)
        · exact new12 (heq ▸ normFace_in hFg)
    · have e : (replacefacesAt [w] f [f12, f21]
          (replacefacesAt [v] f [f21, f12]
            (replacefacesAt (between f.vertices w v) f [f21]
              (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt))))[x]! =
          (replacefacesAt (between f.vertices w v) f [f21]
            (replacefacesAt (between f.vertices v w) f [f12] g.faceListAt))[x]! := by
        rw [replacefacesAt_notin (show x ∉ [w] from fun h => hxw (List.mem_singleton.mp h)),
          replacefacesAt_notin (show x ∉ [v] from fun h => hxv (List.mem_singleton.mp h))]
      rw [e]
      apply distinct_replacefacesAt_norm
      · rw [hlen1]; exact hx
      · exact between_distinct hdf
      · apply distinct_replacefacesAt_norm
        · rw [minGraphProps4 mgp]; exact hx
        · exact between_distinct hdf
        · exact minGraphProps8a' mgp hx
        · exact List.nodup_singleton _
        · intro y hy
          obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hy
          have hFg : F ∈ g.faces := hmemF hx hF
          simp only [normFaces, List.map_cons, List.map_nil, List.mem_singleton]
          exact fun heq => new12 (heq ▸ normFace_in hFg)
      · exact List.nodup_singleton _
      · intro y hy
        have hy' : y = normFace f12 ∨ y ∈ normFaces (g.faceListAt[x]!) := by
          by_cases hx1 : x ∈ between f.vertices v w
          · rw [replacefacesAt_in hx1 (between_distinct hdf)
              (by rw [minGraphProps4 mgp]; exact hx)] at hy
            obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hy
            rcases replace5 hF with hF | hF
            · exact Or.inr (normFace_in hF)
            · exact Or.inl (congrArg normFace (List.mem_singleton.mp hF))
          · rw [replacefacesAt_notin hx1] at hy
            exact Or.inr hy
        simp only [normFaces, List.map_cons, List.map_nil, List.mem_singleton]
        intro heq
        rcases hy' with hy1 | hy1
        · exact neq12 (hy1.symm.trans heq)
        · obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hy1
          exact new21 (heq ▸ normFace_in (hmemF hx hF))

/-- Invariants.thy: splitFace_holds_facesAt_distinct -/
theorem splitFace_holds_facesAt_distinct {g : Graph} {v w : Vertex} {f : Face} {n : Nat}
    (pre : pre_splitFace g v w f (List.range' g.countVertices n)) (mgp : minGraphProps g) :
    facesAt_distinct (splitFace g v w f (List.range' g.countVertices n)).2.2 := by
  have hvw : v ≠ w := pre.2.2.2.2.2.2.2.2.1
  have hdf : f.vertices.Nodup := pre.2.2.1
  have hv : v < g.countVertices := minGraphProps9' mgp pre.1 pre.2.2.2.2.2.2.1
  have hw : w < g.countVertices := minGraphProps9' mgp pre.1 pre.2.2.2.2.2.2.2.1
  have new12 : normFace (split_face f v w (List.range' g.countVertices n)).1 ∉
      normFaces g.faces := splitFace_new_f12_norm pre mgp rfl
  have new21 : normFace (split_face f v w (List.range' g.countVertices n)).2 ∉
      normFaces g.faces := splitFace_new_f21_norm pre mgp rfl
  have neq12 : normFace (split_face f v w (List.range' g.countVertices n)).1 ≠
      normFace (split_face f v w (List.range' g.countVertices n)).2 :=
    splitFace_f12_f21_neq_norm pre mgp rfl
  have hFL : (splitFace g v w f (List.range' g.countVertices n)).2.2.faceListAt =
      replacefacesAt [w] f [(split_face f v w (List.range' g.countVertices n)).1,
          (split_face f v w (List.range' g.countVertices n)).2]
        (replacefacesAt [v] f [(split_face f v w (List.range' g.countVertices n)).2,
            (split_face f v w (List.range' g.countVertices n)).1]
          (replacefacesAt (between f.vertices w v) f
            [(split_face f v w (List.range' g.countVertices n)).2]
            (replacefacesAt (between f.vertices v w) f
              [(split_face f v w (List.range' g.countVertices n)).1] g.faceListAt))) ++
        List.replicate (List.range' g.countVertices n).length
          [(split_face f v w (List.range' g.countVertices n)).1,
            (split_face f v w (List.range' g.countVertices n)).2] := rfl
  have hlen4 : (replacefacesAt [w] f [(split_face f v w (List.range' g.countVertices n)).1,
          (split_face f v w (List.range' g.countVertices n)).2]
        (replacefacesAt [v] f [(split_face f v w (List.range' g.countVertices n)).2,
            (split_face f v w (List.range' g.countVertices n)).1]
          (replacefacesAt (between f.vertices w v) f
            [(split_face f v w (List.range' g.countVertices n)).2]
            (replacefacesAt (between f.vertices v w) f
              [(split_face f v w (List.range' g.countVertices n)).1] g.faceListAt)))).length =
      g.countVertices := by
    rw [replacefacesAt_eq, replacefacesAt2_length, replacefacesAt_eq, replacefacesAt2_length,
      replacefacesAt_length, replacefacesAt_length]
    exact minGraphProps4 mgp
  intro x hx
  rw [splitFace_add_vertices_direct g v w f n] at hx
  have hxlt : x < (splitFace g v w f (List.range' g.countVertices n)).2.2.faceListAt.length := by
    rw [hFL, List.length_append, hlen4, List.length_replicate, List.length_range']
    rcases List.mem_append.mp hx with hx | hx
    · have h1 := List.mem_range.mp hx
      exact lt_of_lt_of_le h1 (Nat.le_add_right _ _)
    · obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      rw [Nat.one_mul]
      exact Nat.add_lt_add_left hi _
  have ex : (splitFace g v w f (List.range' g.countVertices n)).2.2.faceListAt.getD x [] =
      (splitFace g v w f (List.range' g.countVertices n)).2.2.faceListAt[x]! := by
    rw [getElem!_pos _ x hxlt]
    exact (List.getElem_eq_getD []).symm
  show (normFaces ((splitFace g v w f (List.range' g.countVertices n)).2.2.faceListAt.getD
      x [])).Nodup
  rw [ex, hFL]
  by_cases hxg : x < g.countVertices
  · rw [getElem!_append_left (by rw [hlen4]; exact hxg)]
    exact nodup_normFaces_splitFace_faceListAt mgp hvw hdf hv hw new12 new21 neq12 hxg
  · have hxn : x - g.countVertices < (List.range' g.countVertices n).length := by
      rw [List.length_range']
      rcases List.mem_append.mp hx with hx | hx
      · exact absurd (List.mem_range.mp hx) hxg
      · obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
        rw [Nat.one_mul, Nat.add_sub_cancel_left]
        exact hi
    rw [getElem!_append_right (by rw [hlen4]; exact Nat.le_of_not_lt hxg)
      (by rw [hlen4, List.length_replicate]; exact hxn)]
    rw [hlen4, getElem!_pos _ _ (by rw [List.length_replicate]; exact hxn),
      List.getElem_replicate]
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [normFaces, List.map_cons, List.map_nil, List.mem_singleton]
    exact neq12

/-- Auxiliary (ListAux.thy `replace6`, as an iff for nodup lists containing
the replaced element). -/
private theorem mem_replace_of_nodup {x y : α} {newfs : List α} {xs : List α}
    [BEq α] [LawfulBEq α] (hd : xs.Nodup) (hx : x ∈ xs) :
    y ∈ replace x newfs xs ↔ y ∈ newfs ∨ y ∈ xs ∧ y ≠ x := by
  induction xs with
  | nil => exact absurd hx List.not_mem_nil
  | cons a as ih =>
    rw [List.mem_cons] at hx
    have hd' : as.Nodup := (List.nodup_cons.mp hd).2
    have ha : a ∉ as := (List.nodup_cons.mp hd).1
    by_cases hax : a = x
    · subst a
      simp only [replace, beq_self_eq_true, ↓reduceIte, List.mem_append, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h, fun h' => ha (h' ▸ h)⟩
      · rintro (h | ⟨h, hne⟩)
        · exact Or.inl h
        · rcases h with rfl | h
          · exact absurd rfl hne
          · exact Or.inr h
    · have hb : ¬ (a == x) = true := fun h => hax (beq_iff_eq.mp h)
      simp only [replace, if_neg hb, List.mem_cons]
      have hxs : x ∈ as := hx.resolve_left (fun h => hax h.symm)
      rw [ih hd' hxs]
      constructor
      · rintro (rfl | h | ⟨h, hne⟩)
        · exact Or.inr ⟨Or.inl rfl, hax⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h, hne⟩
      · rintro (h | ⟨h, hne⟩)
        · exact Or.inr (Or.inl h)
        · rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨h, hne⟩)

/-- Invariants.thy: splitFace_holds_facesAt_eq -/
theorem splitFace_holds_facesAt_eq {g' : Graph} {v a : Vertex} {f' : Face} {n : Nat}
    (pre_F : pre_splitFace g' v a f' (List.range' g'.countVertices n))
    (mgp : minGraphProps g') :
    facesAt_eq (splitFace g' v a f' (List.range' g'.countVertices n)).2.2 := by
  have hva : v ≠ a := pre_F.2.2.2.2.2.2.2.2.1
  have hdf : f'.vertices.Nodup := pre_F.2.2.1
  have hf' : f' ∈ g'.faces := pre_F.1
  have hv : v < g'.countVertices := minGraphProps9' mgp hf' pre_F.2.2.2.2.2.2.1
  have ha : a < g'.countVertices := minGraphProps9' mgp hf' pre_F.2.2.2.2.2.2.2.1
  have hpre : pre_split_face f' v a (List.range' g'.countVertices n) :=
    pre_splitFace_pre_split_face pre_F
  have hpb : pre_between f'.vertices v a := pre_split_face_p_between hpre
  have hd1 : (between f'.vertices v a).Nodup := between_distinct hdf
  have hd2 : (between f'.vertices a v).Nodup := between_distinct hdf
  have vert12 : (split_face f' v a (List.range' g'.countVertices n)).1.vertices =
      (List.range' g'.countVertices n).reverse ++
        (v :: between f'.vertices v a ++ [a]) := rfl
  have vert21 : (split_face f' v a (List.range' g'.countVertices n)).2.vertices =
      (a :: between f'.vertices a v ++ [v]) ++ List.range' g'.countVertices n := rfl
  have vertFrom : verticesFrom f' v =
      v :: between f'.vertices v a ++ a :: between f'.vertices a v :=
    verticesFrom_ram1 hpre
  have vert_f' : ∀ x, x ∈ f'.vertices ↔
      x ∈ between f'.vertices v a ∨ x ∈ between f'.vertices a v ∨ x = a ∨ x = v := by
    intro x
    rw [cong_mem (verticesFrom_congs pre_F.2.2.2.2.2.2.1), vertFrom]
    simp only [List.mem_cons, List.mem_append]
    tauto
  have hfs : (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faces =
      replace f' [(split_face f' v a (List.range' g'.countVertices n)).2] g'.faces ++
        [(split_face f' v a (List.range' g'.countVertices n)).1] := rfl
  have hmem_faces : ∀ F, F ∈ (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faces ↔
      F = (split_face f' v a (List.range' g'.countVertices n)).1 ∨
        F = (split_face f' v a (List.range' g'.countVertices n)).2 ∨
        F ∈ g'.faces ∧ F ≠ f' := by
    intro F
    rw [hfs, List.mem_append, List.mem_singleton,
      mem_replace_of_nodup (minGraphProps11' mgp) hf', List.mem_singleton]
    tauto
  have hf'At : ∀ {x}, x ∈ f'.vertices → f' ∈ g'.faceListAt[x]! :=
    fun hx => minGraphProps7' mgp hf' hx
  have hmemF : ∀ {x : Nat}, x < g'.countVertices → ∀ {F : Face},
      F ∈ g'.faceListAt[x]! → F ∈ g'.faces ∧ x ∈ F.vertices := by
    intro x hx F hF
    have hlt : x < g'.faceListAt.length := by rw [minGraphProps4 mgp]; exact hx
    rw [getElem!_pos g'.faceListAt x hlt] at hF
    have hd : g'.facesAt x = g'.faceListAt[x] := (List.getElem_eq_getD []).symm
    have hxF : F ∈ g'.facesAt x := hd ▸ hF
    exact ⟨minGraphProps5 mgp (List.mem_range.mpr hx) hxF,
      minGraphProps6 mgp (List.mem_range.mpr hx) hxF⟩
  have hnotR : ∀ y < g'.countVertices, y ∉ List.range' g'.countVertices n := by
    intro y hy hr
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hr
    rw [Nat.one_mul] at hy
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hy) (Nat.lt_irrefl _)
  have hFL : (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faceListAt =
      replacefacesAt [a] f' [(split_face f' v a (List.range' g'.countVertices n)).1,
          (split_face f' v a (List.range' g'.countVertices n)).2]
        (replacefacesAt [v] f' [(split_face f' v a (List.range' g'.countVertices n)).2,
            (split_face f' v a (List.range' g'.countVertices n)).1]
          (replacefacesAt (between f'.vertices a v) f'
            [(split_face f' v a (List.range' g'.countVertices n)).2]
            (replacefacesAt (between f'.vertices v a) f'
              [(split_face f' v a (List.range' g'.countVertices n)).1] g'.faceListAt))) ++
        List.replicate (List.range' g'.countVertices n).length
          [(split_face f' v a (List.range' g'.countVertices n)).1,
            (split_face f' v a (List.range' g'.countVertices n)).2] := rfl
  have hlen1 : (replacefacesAt (between f'.vertices v a) f'
        [(split_face f' v a (List.range' g'.countVertices n)).1] g'.faceListAt).length =
      g'.countVertices := by
    rw [replacefacesAt_length]; exact minGraphProps4 mgp
  have hlen2 : (replacefacesAt (between f'.vertices a v) f'
        [(split_face f' v a (List.range' g'.countVertices n)).2]
        (replacefacesAt (between f'.vertices v a) f'
          [(split_face f' v a (List.range' g'.countVertices n)).1] g'.faceListAt)).length =
      g'.countVertices := by
    rw [replacefacesAt_length]; exact hlen1
  have hlen3 : (replacefacesAt [v] f' [(split_face f' v a (List.range' g'.countVertices n)).2,
          (split_face f' v a (List.range' g'.countVertices n)).1]
        (replacefacesAt (between f'.vertices a v) f'
          [(split_face f' v a (List.range' g'.countVertices n)).2]
          (replacefacesAt (between f'.vertices v a) f'
            [(split_face f' v a (List.range' g'.countVertices n)).1] g'.faceListAt))).length =
      g'.countVertices := by
    rw [replacefacesAt_eq, replacefacesAt2_length]; exact hlen2
  have hlen4 : (replacefacesAt [a] f' [(split_face f' v a (List.range' g'.countVertices n)).1,
          (split_face f' v a (List.range' g'.countVertices n)).2]
        (replacefacesAt [v] f' [(split_face f' v a (List.range' g'.countVertices n)).2,
            (split_face f' v a (List.range' g'.countVertices n)).1]
          (replacefacesAt (between f'.vertices a v) f'
            [(split_face f' v a (List.range' g'.countVertices n)).2]
            (replacefacesAt (between f'.vertices v a) f'
              [(split_face f' v a (List.range' g'.countVertices n)).1]
                g'.faceListAt)))).length = g'.countVertices := by
    rw [replacefacesAt_eq, replacefacesAt2_length]; exact hlen3
  intro x hx F
  rw [splitFace_add_vertices_direct g' v a f' n] at hx
  have hxlt : x < (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faceListAt.length := by
    rw [hFL, List.length_append, hlen4, List.length_replicate, List.length_range']
    rcases List.mem_append.mp hx with hx | hx
    · exact lt_of_lt_of_le (List.mem_range.mp hx) (Nat.le_add_right _ _)
    · obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      rw [Nat.one_mul]
      exact Nat.add_lt_add_left hi _
  have ex : (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faceListAt.getD x [] =
      (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faceListAt[x]! := by
    rw [getElem!_pos _ x hxlt]
    exact (List.getElem_eq_getD []).symm
  show F ∈ (splitFace g' v a f' (List.range' g'.countVertices n)).2.2.faceListAt.getD x [] ↔ _
  rw [ex, hFL]
  by_cases hxg : x < g'.countVertices
  · rw [getElem!_append_left (by rw [hlen4]; exact hxg)]
    by_cases hxa : x = a
    · subst x
      have e : (replacefacesAt [a] f' [(split_face f' v a (List.range' g'.countVertices n)).1,
            (split_face f' v a (List.range' g'.countVertices n)).2]
          (replacefacesAt [v] f' [(split_face f' v a (List.range' g'.countVertices n)).2,
              (split_face f' v a (List.range' g'.countVertices n)).1]
            (replacefacesAt (between f'.vertices a v) f'
              [(split_face f' v a (List.range' g'.countVertices n)).2]
              (replacefacesAt (between f'.vertices v a) f'
                [(split_face f' v a (List.range' g'.countVertices n)).1]
                  g'.faceListAt))))[a]! =
          replace f' [(split_face f' v a (List.range' g'.countVertices n)).1,
            (split_face f' v a (List.range' g'.countVertices n)).2] (g'.faceListAt[a]!) := by
        rw [replacefacesAt_nth2 (by rw [hlen3]; exact ha),
          replacefacesAt_notin (show a ∉ [v] from fun h => hva (List.mem_singleton.mp h).symm),
          replacefacesAt_notin (between_not_r1 hdf),
          replacefacesAt_notin (between_not_r2 hdf)]
      rw [e, mem_replace_of_nodup (normFaces_distinct (minGraphProps8a' mgp ha))
        (hf'At pre_F.2.2.2.2.2.2.2.1), List.mem_pair]
      constructor
      · rintro ((rfl | rfl) | ⟨hF, hne⟩)
        · exact ⟨(hmem_faces _).mpr (Or.inl rfl), by
            rw [vert12]
            exact List.mem_append_right _ (List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_singleton_self _)))⟩
        · exact ⟨(hmem_faces _).mpr (Or.inr (Or.inl rfl)), by
            rw [vert21]
            exact List.mem_append_left _ List.mem_cons_self⟩
        · obtain ⟨hFg, haF⟩ := hmemF ha hF
          exact ⟨(hmem_faces _).mpr (Or.inr (Or.inr ⟨hFg, hne⟩)), haF⟩
      · rintro ⟨hFg, haF⟩
        rw [hmem_faces] at hFg
        rcases hFg with rfl | rfl | ⟨hFg, hne⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨minGraphProps7' mgp hFg haF, hne⟩
    · by_cases hxv : x = v
      · subst x
        have e : (replacefacesAt [a] f' [(split_face f' v a (List.range' g'.countVertices n)).1,
              (split_face f' v a (List.range' g'.countVertices n)).2]
            (replacefacesAt [v] f' [(split_face f' v a (List.range' g'.countVertices n)).2,
                (split_face f' v a (List.range' g'.countVertices n)).1]
              (replacefacesAt (between f'.vertices a v) f'
                [(split_face f' v a (List.range' g'.countVertices n)).2]
                (replacefacesAt (between f'.vertices v a) f'
                  [(split_face f' v a (List.range' g'.countVertices n)).1]
                    g'.faceListAt))))[v]! =
            replace f' [(split_face f' v a (List.range' g'.countVertices n)).2,
              (split_face f' v a (List.range' g'.countVertices n)).1] (g'.faceListAt[v]!) := by
          rw [replacefacesAt_notin (show v ∉ [a] from fun h => hva (List.mem_singleton.mp h)),
            replacefacesAt_nth2 (by rw [hlen2]; exact hv),
            replacefacesAt_notin (between_not_r2 hdf),
            replacefacesAt_notin (between_not_r1 hdf)]
        rw [e, mem_replace_of_nodup (normFaces_distinct (minGraphProps8a' mgp hv))
          (hf'At pre_F.2.2.2.2.2.2.1), List.mem_pair]
        constructor
        · rintro ((rfl | rfl) | ⟨hF, hne⟩)
          · exact ⟨(hmem_faces _).mpr (Or.inr (Or.inl rfl)), by
              rw [vert21]
              exact List.mem_append_left _ (List.mem_cons_of_mem _
                (List.mem_append_right _ List.mem_cons_self))⟩
          · exact ⟨(hmem_faces _).mpr (Or.inl rfl), by
              rw [vert12]
              exact List.mem_append_right _ List.mem_cons_self⟩
          · obtain ⟨hFg, hvF⟩ := hmemF hv hF
            exact ⟨(hmem_faces _).mpr (Or.inr (Or.inr ⟨hFg, hne⟩)), hvF⟩
        · rintro ⟨hFg, hvF⟩
          rw [hmem_faces] at hFg
          rcases hFg with rfl | rfl | ⟨hFg, hne⟩
          · exact Or.inl (Or.inr rfl)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨minGraphProps7' mgp hFg hvF, hne⟩
      · have e : (replacefacesAt [a] f' [(split_face f' v a (List.range' g'.countVertices n)).1,
              (split_face f' v a (List.range' g'.countVertices n)).2]
            (replacefacesAt [v] f' [(split_face f' v a (List.range' g'.countVertices n)).2,
                (split_face f' v a (List.range' g'.countVertices n)).1]
              (replacefacesAt (between f'.vertices a v) f'
                [(split_face f' v a (List.range' g'.countVertices n)).2]
                (replacefacesAt (between f'.vertices v a) f'
                  [(split_face f' v a (List.range' g'.countVertices n)).1]
                    g'.faceListAt))))[x]! =
            (replacefacesAt (between f'.vertices a v) f'
              [(split_face f' v a (List.range' g'.countVertices n)).2]
              (replacefacesAt (between f'.vertices v a) f'
                [(split_face f' v a (List.range' g'.countVertices n)).1] g'.faceListAt))[x]! := by
          rw [replacefacesAt_notin (show x ∉ [a] from fun h => hxa (List.mem_singleton.mp h)),
            replacefacesAt_notin (show x ∉ [v] from fun h => hxv (List.mem_singleton.mp h))]
        rw [e]
        by_cases hx1 : x ∈ between f'.vertices v a
        · have hx2 : x ∉ between f'.vertices a v := between_inter_empty hpb hx1
          have e2 : (replacefacesAt (between f'.vertices a v) f'
                [(split_face f' v a (List.range' g'.countVertices n)).2]
                (replacefacesAt (between f'.vertices v a) f'
                  [(split_face f' v a (List.range' g'.countVertices n)).1]
                    g'.faceListAt))[x]! =
              replace f' [(split_face f' v a (List.range' g'.countVertices n)).1]
                (g'.faceListAt[x]!) := by
            rw [replacefacesAt_notin hx2,
              replacefacesAt_in hx1 hd1 (by rw [minGraphProps4 mgp]; exact hxg)]
          rw [e2, mem_replace_of_nodup (normFaces_distinct (minGraphProps8a' mgp hxg))
            (hf'At (inbetween_inset hx1)), List.mem_singleton]
          constructor
          · rintro (rfl | ⟨hF, hne⟩)
            · exact ⟨(hmem_faces _).mpr (Or.inl rfl), by
                rw [vert12]
                exact List.mem_append_right _ (List.mem_cons_of_mem _
                  (List.mem_append_left _ hx1))⟩
            · obtain ⟨hFg, hxF⟩ := hmemF hxg hF
              exact ⟨(hmem_faces _).mpr (Or.inr (Or.inr ⟨hFg, hne⟩)), hxF⟩
          · rintro ⟨hFg, hxF⟩
            rw [hmem_faces] at hFg
            rcases hFg with rfl | rfl | ⟨hFg, hne⟩
            · exact Or.inl rfl
            · exfalso
              rw [vert21] at hxF
              rcases List.mem_append.mp hxF with hxF | hxF
              · rcases List.mem_cons.mp hxF with h | hxF
                · exact hxa h
                · rcases List.mem_append.mp hxF with hxF | hxF
                  · exact hx2 hxF
                  · exact hxv (List.mem_singleton.mp hxF)
              · exact hnotR x hxg hxF
            · exact Or.inr ⟨minGraphProps7' mgp hFg hxF, hne⟩
        · by_cases hx2 : x ∈ between f'.vertices a v
          · have e2 : (replacefacesAt (between f'.vertices a v) f'
                  [(split_face f' v a (List.range' g'.countVertices n)).2]
                  (replacefacesAt (between f'.vertices v a) f'
                    [(split_face f' v a (List.range' g'.countVertices n)).1]
                      g'.faceListAt))[x]! =
                replace f' [(split_face f' v a (List.range' g'.countVertices n)).2]
                  (g'.faceListAt[x]!) := by
              rw [replacefacesAt_in hx2 hd2 (by rw [hlen1]; exact hxg),
                replacefacesAt_notin hx1]
            rw [e2, mem_replace_of_nodup (normFaces_distinct (minGraphProps8a' mgp hxg))
              (hf'At (inbetween_inset hx2)), List.mem_singleton]
            constructor
            · rintro (rfl | ⟨hF, hne⟩)
              · exact ⟨(hmem_faces _).mpr (Or.inr (Or.inl rfl)), by
                  rw [vert21]
                  exact List.mem_append_left _ (List.mem_cons_of_mem _
                    (List.mem_append_left _ hx2))⟩
              · obtain ⟨hFg, hxF⟩ := hmemF hxg hF
                exact ⟨(hmem_faces _).mpr (Or.inr (Or.inr ⟨hFg, hne⟩)), hxF⟩
            · rintro ⟨hFg, hxF⟩
              rw [hmem_faces] at hFg
              rcases hFg with rfl | rfl | ⟨hFg, hne⟩
              · exfalso
                rw [vert12] at hxF
                rcases List.mem_append.mp hxF with hxF | hxF
                · exact hnotR x hxg (List.mem_reverse.mp hxF)
                · rcases List.mem_cons.mp hxF with h | hxF
                  · exact hxv h
                  · rcases List.mem_append.mp hxF with hxF | hxF
                    · exact hx1 hxF
                    · exact hxa (List.mem_singleton.mp hxF)
              · exact Or.inl rfl
              · exact Or.inr ⟨minGraphProps7' mgp hFg hxF, hne⟩
          · have e2 : (replacefacesAt (between f'.vertices a v) f'
                  [(split_face f' v a (List.range' g'.countVertices n)).2]
                  (replacefacesAt (between f'.vertices v a) f'
                    [(split_face f' v a (List.range' g'.countVertices n)).1]
                      g'.faceListAt))[x]! = g'.faceListAt[x]! := by
              rw [replacefacesAt_notin hx2, replacefacesAt_notin hx1]
            rw [e2]
            constructor
            · intro hF
              obtain ⟨hFg, hxF⟩ := hmemF hxg hF
              have hne : F ≠ f' := by
                intro hFe
                subst hFe
                rcases (vert_f' x).mp hxF with h | h | h | h
                · exact hx1 h
                · exact hx2 h
                · exact hxa h
                · exact hxv h
              exact ⟨(hmem_faces _).mpr (Or.inr (Or.inr ⟨hFg, hne⟩)), hxF⟩
            · rintro ⟨hFg, hxF⟩
              rw [hmem_faces] at hFg
              rcases hFg with rfl | rfl | ⟨hFg, hne⟩
              · exfalso
                rw [vert12] at hxF
                rcases List.mem_append.mp hxF with hxF | hxF
                · exact hnotR x hxg (List.mem_reverse.mp hxF)
                · rcases List.mem_cons.mp hxF with h | hxF
                  · exact hxv h
                  · rcases List.mem_append.mp hxF with hxF | hxF
                    · exact hx1 hxF
                    · exact hxa (List.mem_singleton.mp hxF)
              · exfalso
                rw [vert21] at hxF
                rcases List.mem_append.mp hxF with hxF | hxF
                · rcases List.mem_cons.mp hxF with h | hxF
                  · exact hxa h
                  · rcases List.mem_append.mp hxF with hxF | hxF
                    · exact hx2 hxF
                    · exact hxv (List.mem_singleton.mp hxF)
                · exact hnotR x hxg hxF
              · exact minGraphProps7' mgp hFg hxF
  · have hxn : x - g'.countVertices < (List.range' g'.countVertices n).length := by
      rw [List.length_range']
      rcases List.mem_append.mp hx with hx | hx
      · exact absurd (List.mem_range.mp hx) hxg
      · obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
        rw [Nat.one_mul, Nat.add_sub_cancel_left]
        exact hi
    rw [getElem!_append_right (by rw [hlen4]; exact Nat.le_of_not_lt hxg)
      (by rw [hlen4, List.length_replicate]; exact hxn)]
    rw [hlen4, getElem!_pos _ _ (by rw [List.length_replicate]; exact hxn),
      List.getElem_replicate, List.mem_pair]
    have hxR : x ∈ List.range' g'.countVertices n := by
      rcases List.mem_append.mp hx with hx | hx
      · exact absurd (List.mem_range.mp hx) hxg
      · exact hx
    constructor
    · rintro (rfl | rfl)
      · exact ⟨(hmem_faces _).mpr (Or.inl rfl), by
          rw [vert12]
          exact List.mem_append_left _ (List.mem_reverse.mpr hxR)⟩
      · exact ⟨(hmem_faces _).mpr (Or.inr (Or.inl rfl)), by
          rw [vert21]
          exact List.mem_append_right _ hxR⟩
    · rintro ⟨hFg, hxF⟩
      rw [hmem_faces] at hFg
      rcases hFg with rfl | rfl | ⟨hFg, hne⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (List.mem_range.mp (minGraphProps9 mgp hFg hxF)) hxg

/-- Auxiliary (cf. FaceDivisionProps3 `nodup_not_is_sublist_self`, kept
`private` there): a nodup list cannot contain `[x, x]` as a sublist. -/
private theorem nodup_not_is_sublist_self' {x : Vertex} {L : List Vertex} (hd : L.Nodup) :
    ¬ is_sublist [x, x] L := by
  rintro ⟨as, bs, h⟩
  have hd' : (as ++ [x, x] ++ bs).Nodup := h ▸ hd
  have h1 : (as ++ [x, x]).Nodup := (List.nodup_append.mp hd').1
  have h2 : [x, x].Nodup := (List.nodup_append.mp h1).2.1
  exact (List.nodup_cons.mp h2).1 List.mem_cons_self

/-- Auxiliary: if `[x, y]` is a sublist of `x :: M ++ [y]` with `y ∉ M` and
`x ∉ M` (and `x ≠ y`), then `M = []`. -/
private theorem eq_nil_of_is_sublist {x y : Vertex} {M : List Vertex}
    (hy : y ∉ M) (hx : x ∉ M) (hxy : x ≠ y)
    (h : is_sublist [x, y] (x :: M ++ [y])) : M = [] := by
  obtain ⟨as, bs, hL⟩ := h
  cases as with
  | nil =>
    simp only [List.nil_append, List.cons_append] at hL
    have h2 := (List.cons.inj hL).2
    cases M with
    | nil => rfl
    | cons c cs =>
      simp only [List.cons_append] at h2
      have h3 : c = y := (List.cons.inj h2).1
      exact absurd (h3 ▸ (List.mem_cons_self : c ∈ c :: cs)) hy
  | cons c as' =>
    simp only [List.cons_append] at hL
    have h2 := (List.cons.inj hL).2
    have hmem : x ∈ M ++ [y] := by
      rw [h2]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact absurd hmem hx
    · exact absurd (List.mem_singleton.mp hmem) hxy

/-- Invariants.thy: split_face_edge_disj (membership form of the empty
intersection `ℰ f₁ ∩ ℰ f₂ = {}`) -/
theorem split_face_edge_disj {f f₁ f₂ : Face} {a b : Vertex} {vs : List Vertex}
    (hp : pre_split_face f a b vs) (hsplit : (f₁, f₂) = split_face f a b vs)
    (hlen : 3 ≤ f.vertices.length)
    (hvs : vs = [] → (a, b) ∉ f.edges ∧ (b, a) ∉ f.edges) :
    ∀ e ∈ f₁.edges, e ∉ f₂.edges := by
  have hdf : f.vertices.Nodup := hp.1
  have hdvs : vs.Nodup := hp.2.1
  have hdisj : ∀ x ∈ f.vertices, x ∉ vs := hp.2.2.1
  have ha : a ∈ f.vertices := hp.2.2.2.1
  have hb : b ∈ f.vertices := hp.2.2.2.2.1
  have hab : a ≠ b := hp.2.2.2.2.2
  have havs : a ∉ vs := hdisj a ha
  have hbvs : b ∉ vs := hdisj b hb
  have hB12mem : ∀ x ∈ between f.vertices a b, x ∈ f.vertices :=
    fun x hx => inbetween_inset hx
  have hB21mem : ∀ x ∈ between f.vertices b a, x ∈ f.vertices :=
    fun x hx => inbetween_inset hx
  have e1 : f₁ = (split_face f a b vs).1 := congrArg Prod.fst hsplit
  have e2 : f₂ = (split_face f a b vs).2 := congrArg Prod.snd hsplit
  have hE1 : f₁.edges = Edges (b :: vs.reverse ++ [a]) ∪
      Edges (a :: between f.vertices a b ++ [b]) := e1 ▸ edges_split_face1 hp
  have hE2 : f₂.edges = Edges (a :: vs ++ [b]) ∪
      Edges (b :: between f.vertices b a ++ [a]) := e2 ▸ edges_split_face2 hp
  have hN1 : (b :: vs.reverse ++ [a]).Nodup := by
    rw [List.cons_append]
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_append, List.mem_reverse, List.mem_singleton, not_or]
      exact ⟨fun hm => hbvs hm, fun hm => hab hm.symm⟩
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_reverse.mpr hdvs, List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      have hxa : x = a := hxy.trans (List.mem_singleton.mp hy)
      exact havs (hxa ▸ List.mem_reverse.mp hx)
  have hN2 : (a :: vs ++ [b]).Nodup := by
    rw [List.cons_append]
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun hm => havs hm, fun hm => hab hm⟩
    · apply List.nodup_append.mpr
      refine ⟨hdvs, List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      have hxb : x = b := hxy.trans (List.mem_singleton.mp hy)
      exact hbvs (hxb ▸ hx)
  have hNQ1 : (a :: between f.vertices a b ++ [b]).Nodup := between_distinct_r12 hdf hab
  have hNQ2 : (b :: between f.vertices b a ++ [a]).Nodup :=
    between_distinct_r12 hdf hab.symm
  have hglP : (b :: vs.reverse ++ [a]).getLast! = a := getLast!_concat _ _
  intro e he1 he2
  obtain ⟨x, y⟩ := e
  rw [hE1] at he1
  rw [hE2] at he2
  rcases he1 with hP1 | hQ1 <;> rcases he2 with hP2 | hQ2
  · -- `Edges (b :: vs.reverse ++ [a])` vs `Edges (a :: vs ++ [b])`: reverses
    have hrev : (a :: vs ++ [b]).reverse = b :: vs.reverse ++ [a] := by
      simp [List.reverse_cons, List.reverse_append]
    rw [← hrev] at hP1
    have hcon : (x, y) ∈ Edges (a :: vs ++ [b]).reverse ∩ Edges (a :: vs ++ [b]) :=
      ⟨hP1, hP2⟩
    rw [Edges_rev_disj hN2] at hcon
    exact (Set.mem_empty_iff_false _).mp hcon
  · -- `Edges (b :: vs.reverse ++ [a])` vs `Edges (b :: between f.vertices b a ++ [a])`
    have hx : x = a ∨ x = b := by
      have hx1 := (in_Edges_in_set hP1).1
      have hx2 := (in_Edges_in_set hQ2).1
      rcases List.mem_cons.mp hx1 with h | hx1
      · exact Or.inr h
      · rcases List.mem_append.mp hx1 with hx1 | hx1
        · have hxv : x ∈ vs := List.mem_reverse.mp hx1
          rcases List.mem_cons.mp hx2 with h | hx2
          · exact absurd (h ▸ hxv) hbvs
          · rcases List.mem_append.mp hx2 with hx2 | hx2
            · exact absurd hxv (hdisj x (hB21mem x hx2))
            · exact absurd ((List.mem_singleton.mp hx2) ▸ hxv) havs
        · exact Or.inl (List.mem_singleton.mp hx1)
    have hy : y = a ∨ y = b := by
      have hy1 := (in_Edges_in_set hP1).2
      have hy2 := (in_Edges_in_set hQ2).2
      rcases List.mem_cons.mp hy1 with h | hy1
      · exact Or.inr h
      · rcases List.mem_append.mp hy1 with hy1 | hy1
        · have hyv : y ∈ vs := List.mem_reverse.mp hy1
          rcases List.mem_cons.mp hy2 with h | hy2
          · exact absurd (h ▸ hyv) hbvs
          · rcases List.mem_append.mp hy2 with hy2 | hy2
            · exact absurd hyv (hdisj y (hB21mem y hy2))
            · exact absurd ((List.mem_singleton.mp hy2) ▸ hyv) havs
        · exact Or.inl (List.mem_singleton.mp hy1)
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst x <;> subst y
    · exact nodup_not_is_sublist_self' hN1 hP1
    · exact is_sublist_notlast hN1 hglP.symm hP1
    · have hB21nil : between f.vertices b a = [] :=
        eq_nil_of_is_sublist (between_not_r2 hdf) (between_not_r1 hdf) hab.symm hQ2
      have hvsnil : vs = [] := by
        have h : vs.reverse = [] :=
          eq_nil_of_is_sublist (fun hm => havs (List.mem_reverse.mp hm))
            (fun hm => hbvs (List.mem_reverse.mp hm)) hab.symm hP1
        cases vs with
        | nil => rfl
        | cons c cs => simp at h
      have hne : is_nextElem f.vertices b a :=
        is_nextElem_between_empty' hB21nil hdf hb ha hab.symm
      exact (hvs hvsnil).2 ((is_nextElem_edges_eq hdf).mpr hne)
    · exact nodup_not_is_sublist_self' hN1 hP1
  · -- `Edges (a :: between f.vertices a b ++ [b])` vs `Edges (a :: vs ++ [b])`
    have hx : x = a ∨ x = b := by
      have hx1 := (in_Edges_in_set hQ1).1
      have hx2 := (in_Edges_in_set hP2).1
      rcases List.mem_cons.mp hx1 with h | hx1
      · exact Or.inl h
      · rcases List.mem_append.mp hx1 with hx1 | hx1
        · rcases List.mem_cons.mp hx2 with h | hx2
          · exact absurd (h ▸ hx1) (between_not_r1 hdf)
          · rcases List.mem_append.mp hx2 with hx2 | hx2
            · exact absurd hx2 (hdisj x (hB12mem x hx1))
            · exact absurd ((List.mem_singleton.mp hx2) ▸ hx1) (between_not_r2 hdf)
        · exact Or.inr (List.mem_singleton.mp hx1)
    have hy : y = a ∨ y = b := by
      have hy1 := (in_Edges_in_set hQ1).2
      have hy2 := (in_Edges_in_set hP2).2
      rcases List.mem_cons.mp hy1 with h | hy1
      · exact Or.inl h
      · rcases List.mem_append.mp hy1 with hy1 | hy1
        · rcases List.mem_cons.mp hy2 with h | hy2
          · exact absurd (h ▸ hy1) (between_not_r1 hdf)
          · rcases List.mem_append.mp hy2 with hy2 | hy2
            · exact absurd hy2 (hdisj y (hB12mem y hy1))
            · exact absurd ((List.mem_singleton.mp hy2) ▸ hy1) (between_not_r2 hdf)
        · exact Or.inr (List.mem_singleton.mp hy1)
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst x <;> subst y
    · exact nodup_not_is_sublist_self' hNQ1 hQ1
    · have hB12nil : between f.vertices a b = [] :=
        eq_nil_of_is_sublist (between_not_r2 hdf) (between_not_r1 hdf) hab hQ1
      have hvsnil : vs = [] :=
        eq_nil_of_is_sublist hbvs havs hab hP2
      have hne : is_nextElem f.vertices a b :=
        is_nextElem_between_empty' hB12nil hdf ha hb hab
      exact (hvs hvsnil).1 ((is_nextElem_edges_eq hdf).mpr hne)
    · have hglQ1 : (a :: between f.vertices a b ++ [b]).getLast! = b := getLast!_concat _ _
      exact is_sublist_notlast hNQ1 hglQ1.symm hQ1
    · exact nodup_not_is_sublist_self' hNQ1 hQ1
  · -- `Edges (a :: between f.vertices a b ++ [b])` vs
    -- `Edges (b :: between f.vertices b a ++ [a])`: `Edges_compl`
    have hcon : (x, y) ∈ Edges (a :: between f.vertices a b ++ [b]) ∩
        Edges (b :: between f.vertices b a ++ [a]) := ⟨hQ1, hQ2⟩
    rw [Edges_compl hdf ha hb hab] at hcon
    exact (Set.mem_empty_iff_false _).mp hcon

/-- Invariants.thy: splitFace_edge_disj -/
theorem splitFace_edge_disj {g g' : Graph} {u v : Vertex} {f f₁ f₂ : Face}
    {vs : List Vertex} (mgp : minGraphProps g) (pre : pre_splitFace g u v f vs)
    (FDG : (f₁, f₂, g') = splitFace g u v f vs) : edges_disj g' := by
  have disj : edges_disj g := mgp.2.2.2.2.2.2.2.1
  have hfg : f ∈ g.faces := pre_splitFace_oldF pre
  have hsplit : (f₁, f₂) = split_face f u v vs := splitFace_split_face hfg FDG
  have hpsf : pre_split_face f u v vs := pre_splitFace_pre_split_face pre
  have h12 : ∀ e ∈ f₁.edges, e ∉ f₂.edges :=
    split_face_edge_disj hpsf hsplit (mgp_vertices3 mgp hfg) (by
      intro hvsnil
      rcases pre.2.2.2.2.2.2.2.2.2 with ⟨h1, h2, -, -⟩ | hne
      · exact ⟨h1, h2⟩
      · exact absurd hvsnil hne)
  have h21 : ∀ e ∈ f₂.edges, e ∉ f₁.edges := fun e he2 he1 => h12 e he1 he2
  -- the edges of the two new faces avoid the edges of every old face ≠ f
  have hold : ∀ f' ∈ g.faces, f' ≠ f → (f₁.edges ∪ f₂.edges) ∩ f'.edges = ∅ := by
    intro f' hf' hf'f
    ext e
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro he12 hef'
    have hcontra1 : ∀ {p q : Vertex}, p ∈ vs → (p, q) ∈ f'.edges → False :=
      fun hpvs he => pre.2.2.2.2.1 _ (minGraphProps9 mgp hf' (in_edges_in_vertices he).1) hpvs
    have hcontra2 : ∀ {p q : Vertex}, q ∈ vs → (p, q) ∈ f'.edges → False :=
      fun hqvs he => pre.2.2.2.2.1 _ (minGraphProps9 mgp hf' (in_edges_in_vertices he).2) hqvs
    by_cases hvsnil : vs = []
    · subst hvsnil
      have hE := split_face_edges_f12_f21_vs hpsf hsplit
      obtain ⟨p, q⟩ := e
      rw [hE] at he12
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        at he12
      have huv : (u, v) ∉ g.edges ∧ (v, u) ∉ g.edges := by
        rcases pre.2.2.2.2.2.2.2.2.2 with ⟨-, -, h3, h4⟩ | hne
        · exact ⟨h3, h4⟩
        · exact absurd rfl hne
      rcases he12 with hef | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mgp_edges_disj mgp hf'f hf' hfg hef' hef
      · exact huv.2 ⟨f', hf', hef'⟩
      · exact huv.1 ⟨f', hf', hef'⟩
    · have hE := split_face_edges_f12_f21 hpsf hsplit hvsnil
      obtain ⟨p, q⟩ := e
      rw [hE] at he12
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        at he12
      rcases he12 with ((hef | h) | h) | h
      · exact mgp_edges_disj mgp hf'f hf' hfg hef' hef
      · rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hcontra1 (head!_mem hvsnil) hef'
        · exact hcontra2 (head!_mem hvsnil) hef'
        · exact hcontra1 (getLast!_mem hvsnil) hef'
        · exact hcontra2 (getLast!_mem hvsnil) hef'
      · exact hcontra1 (in_Edges_in_set h).1 hef'
      · exact hcontra1 (List.mem_reverse.mp (in_Edges_in_set h).1) hef'
  -- assemble: case split on whether each face is new or old
  intro F hF F' hF' hFF' e heF heF'
  have hFd := (set_faces_splitFace mgp hfg pre FDG F).mp hF
  have hF'd := (set_faces_splitFace mgp hfg pre FDG F').mp hF'
  rcases hFd with hFd | hFd | ⟨hFold, hFf⟩ <;> rcases hF'd with hF'd | hF'd | ⟨hF'old, hF'f⟩
  · subst F; subst F'; exact absurd rfl hFF'
  · subst F; subst F'; exact h12 e heF heF'
  · subst F
    have hcon : e ∈ (f₁.edges ∪ f₂.edges) ∩ F'.edges := ⟨Set.mem_union_left _ heF, heF'⟩
    rw [hold F' hF'old hF'f] at hcon
    exact (Set.mem_empty_iff_false _).mp hcon
  · subst F; subst F'; exact h21 e heF heF'
  · subst F; subst F'; exact absurd rfl hFF'
  · subst F
    have hcon : e ∈ (f₁.edges ∪ f₂.edges) ∩ F'.edges := ⟨Set.mem_union_right _ heF, heF'⟩
    rw [hold F' hF'old hF'f] at hcon
    exact (Set.mem_empty_iff_false _).mp hcon
  · subst F'
    have hcon : e ∈ (f₁.edges ∪ f₂.edges) ∩ F.edges := ⟨Set.mem_union_left _ heF', heF⟩
    rw [hold F hFold hFf] at hcon
    exact (Set.mem_empty_iff_false _).mp hcon
  · subst F'
    have hcon : e ∈ (f₁.edges ∪ f₂.edges) ∩ F.edges := ⟨Set.mem_union_right _ heF', heF⟩
    rw [hold F hFold hFf] at hcon
    exact (Set.mem_empty_iff_false _).mp hcon
  · exact disj F hFold F' hF'old hFF' e heF heF'

/-- Invariants.thy: splitFace_edges_disj2 -/
theorem splitFace_edges_disj2 {g : Graph} {u v : Vertex} {f : Face} {vs : List Vertex}
    (mgp : minGraphProps g) (pre : pre_splitFace g u v f vs) :
    edges_disj (splitFace g u v f vs).2.2 :=
  splitFace_edge_disj mgp pre rfl

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

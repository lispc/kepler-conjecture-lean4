/-
Port of block C (lines 1913–2827) of the Isabelle AFP "Flyspeck-Tame" theory
`Invariants.thy`: `subsection Invariants of makeFaceFinal`,
`subsection Invariants of subdivFace'`, `subsection Invariants of Seed`,
`subsection Increasing properties of subdivFace'` and
`subsection Main invariant theorems`.

Source: `reference/afp-flyspeck-tame/Invariants.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Conventions follow `InvariantsA.lean` / `InvariantsB.lean`.

Porting status (second pass): ported are the `makeFaceFinal` subsection
(1913–2063, complete), `subdivFace'_holds_minGraphProps` (2066),
`FaceDivsionGraph_one_final_but` (2106), `one_final_but_makeFaceFinal` (2320),
`one_final_subdivFace'` (2340), `neighbors_edges` (2419), `no_self_edges`
(2434), `duplicateEdge_is_duplicateEdge_eq` (2442),
`incrIndexList_less_eq` / `incrIndexList_less` (2471–2481), and the
increasing-properties subsection (2631–2775: `subdivFace'_incr`,
`splitFace_incr_faces`, `subdivFace'_incr_faces`, `two_faces_subdivFace'`).

Still to port (continuation): the `Seed` subsection (2483–2547;
`Seed_holds_facesAt_distinct`/`faces_distinct` need the unported ListAux
lemmas `fst/snd_splitAt_upt`, `fst/snd_splitAt_rev`, `upt_conv_Cons`),
`pre_subdivFace_indexToVertexList` (2550), `next_plane0_via_subdivFace'`
(2678), `next_plane0_incr` (2703), `next_plane0_incr_faces` (2753), and the
main theorems `inv_genPoly` (2778) and `inv_inv_next_plane0` (2817), which
depend on the above. (`inv_inv_next_plane0`: this project's `invariant`
takes `P : Graph → Bool` while `inv` is a `Prop`, so use the unfolded form
`∀ g g', g' ∈ next_plane0 p g → inv g → inv g'` with a comment.)
-/
import Kepler.Graphs.InvariantsB

namespace Kepler.Graphs

/-! ### Invariants of `makeFaceFinal` -/

/-- Auxiliary (ListAux.thy `replace6`, as an iff for nodup lists containing
the replaced element; same statement as the private `mem_replace_of_nodup`
in `InvariantsB.lean`). -/
private theorem mem_replace_iff [BEq α] [LawfulBEq α] {x y : α} {newfs : List α}
    {xs : List α} (hd : xs.Nodup) (hx : x ∈ xs) :
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

/-- Invariants.thy: MakeFaceFinal_minGraphProps' -/
theorem MakeFaceFinal_minGraphProps' {g : Graph} {f : Face} (hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : minGraphProps' (makeFaceFinal f g) := by
  intro f' hf'
  have h2 : 2 < f.vertices.length ∧ f.vertices.Nodup :=
    ⟨minGraphProps2 hmgp hf, minGraphProps3 hmgp hf⟩
  simp only [makeFaceFinal, makeFaceFinalFaceList] at hf'
  rcases replace5 hf' with h | h
  · exact ⟨minGraphProps2 hmgp h, minGraphProps3 hmgp h⟩
  · simp only [List.mem_singleton] at h
    subst h
    exact h2

/-- Auxiliary: `facesAt` of `makeFaceFinal` at an in-range vertex. -/
private theorem facesAt_makeFaceFinal {g : Graph} {f : Face} {v : Vertex}
    (hlen : v < g.faceListAt.length) :
    (makeFaceFinal f g).facesAt v = makeFaceFinalFaceList f (g.facesAt v) := by
  have hlen2 : v < (g.faceListAt.map (makeFaceFinalFaceList f)).length := by
    rw [List.length_map]; exact hlen
  show (g.faceListAt.map (makeFaceFinalFaceList f)).getD v [] = _
  calc (g.faceListAt.map (makeFaceFinalFaceList f)).getD v []
      = (g.faceListAt.map (makeFaceFinalFaceList f))[v]'hlen2 :=
          (List.getElem_eq_getD _).symm
    _ = makeFaceFinalFaceList f g.faceListAt[v] := List.getElem_map _
    _ = makeFaceFinalFaceList f (g.faceListAt.getD v []) := by
          rw [List.getElem_eq_getD]

/-- Invariants.thy: MakeFaceFinal_facesAt_eq -/
theorem MakeFaceFinal_facesAt_eq {g : Graph} {f : Face} (hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : facesAt_eq (makeFaceFinal f g) := by
  intro v hv x
  have hvg : v ∈ g.vertices := hv
  have hlen : v < g.faceListAt.length := minGraphProps4 hmgp ▸ List.mem_range.mp hvg
  have hdist : (g.facesAt v).Nodup := normFaces_distinct (minGraphProps8 hmgp hvg)
  have hFg : g.faces.Nodup := minGraphProps11' hmgp
  rw [facesAt_makeFaceFinal hlen]
  show x ∈ replace f [setFinal f] (g.facesAt v) ↔
    x ∈ replace f [setFinal f] g.faces ∧ v ∈ x.vertices
  by_cases hfv : f ∈ g.facesAt v
  · rw [mem_replace_iff hdist hfv, mem_replace_iff hFg hf]
    constructor
    · rintro (h | ⟨h, hne⟩)
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨Or.inl (List.mem_singleton_self _), minGraphProps6 (f := f) hmgp hvg hfv⟩
      · have hx := (hmgp.2.1 v hvg x).mp h
        exact ⟨Or.inr ⟨hx.1, hne⟩, hx.2⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with h | ⟨h, hne⟩
      · simp only [List.mem_singleton] at h
        subst h
        exact Or.inl (List.mem_singleton_self _)
      · exact Or.inr ⟨(hmgp.2.1 v hvg x).mpr ⟨h, h2⟩, hne⟩
  · rw [replace2 hfv, mem_replace_iff hFg hf]
    constructor
    · intro h
      have hx := (hmgp.2.1 v hvg x).mp h
      exact ⟨Or.inr ⟨hx.1, fun h' => hfv (h' ▸ h)⟩, hx.2⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with h | ⟨h, -⟩
      · simp only [List.mem_singleton] at h
        subst h
        exact absurd (minGraphProps7 hmgp hf h2) hfv
      · exact (hmgp.2.1 v hvg x).mpr ⟨h, h2⟩

/-- Invariants.thy: MakeFaceFinal_faceListAt_len -/
theorem MakeFaceFinal_faceListAt_len {g : Graph} {f : Face} (_hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : faceListAt_len (makeFaceFinal f g) := by
  show (g.faceListAt.map (makeFaceFinalFaceList f)).length = g.countVertices
  rw [List.length_map]
  exact minGraphProps4 hmgp

/-- Invariants.thy: normFaces_makeFaceFinalFaceList -/
theorem normFaces_makeFaceFinalFaceList (f : Face) (fs : List Face) :
    normFaces (makeFaceFinalFaceList f fs) = normFaces fs := by
  induction fs with
  | nil => rfl
  | cons a as ih =>
    simp only [makeFaceFinalFaceList, replace]
    split
    · rename_i hcond
      have haf : a = f := beq_iff_eq.mp hcond
      subst haf
      rfl
    · show normFace a :: (replace f [setFinal f] as).map normFace =
        normFace a :: as.map normFace
      exact congrArg (normFace a :: ·) ih

/-- Invariants.thy: MakeFaceFinal_facesAt_distinct -/
theorem MakeFaceFinal_facesAt_distinct {g : Graph} {f : Face} (_hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : facesAt_distinct (makeFaceFinal f g) := by
  intro v hv
  have hvg : v ∈ g.vertices := hv
  have hlen : v < g.faceListAt.length := minGraphProps4 hmgp ▸ List.mem_range.mp hvg
  show (normFaces ((g.faceListAt.map (makeFaceFinalFaceList f)).getD v [])).Nodup
  rw [show (g.faceListAt.map (makeFaceFinalFaceList f)).getD v [] =
      makeFaceFinalFaceList f (g.facesAt v) from facesAt_makeFaceFinal hlen,
    normFaces_makeFaceFinalFaceList]
  exact minGraphProps8 hmgp hvg

/-- Invariants.thy: MakeFaceFinal_faces_subset -/
theorem MakeFaceFinal_faces_subset {g : Graph} {f : Face} (hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : faces_subset (makeFaceFinal f g) := by
  intro f' hf' v hv
  simp only [makeFaceFinal, makeFaceFinalFaceList] at hf'
  rcases replace5 hf' with h | h
  · exact minGraphProps9 (g := g) hmgp h hv
  · simp only [List.mem_singleton] at h
    subst h
    exact minGraphProps9 (g := g) hmgp hf hv

/-- Invariants.thy: MakeFaceFinal_edges_sym (via `edges_makeFaceFinal`) -/
theorem MakeFaceFinal_edges_sym {g : Graph} {f : Face} (_hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : edges_sym (makeFaceFinal f g) := by
  intro a b hab
  rw [edges_makeFaceFinal] at hab ⊢
  exact minGraphProps10 hmgp hab

/-- Invariants.thy: MakeFaceFinal_faces_distinct -/
theorem MakeFaceFinal_faces_distinct {g : Graph} {f : Face} (_hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : faces_distinct (makeFaceFinal f g) := by
  show (normFaces (makeFaceFinalFaceList f g.faces)).Nodup
  rw [normFaces_makeFaceFinalFaceList]
  exact minGraphProps11 hmgp

/-- Invariants.thy: MakeFaceFinal_edges_disj -/
theorem MakeFaceFinal_edges_disj {g : Graph} {f : Face} (hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : edges_disj (makeFaceFinal f g) := by
  have hFg : g.faces.Nodup := minGraphProps11' hmgp
  intro f₁ hf₁ f₂ hf₂ hne e he
  simp only [makeFaceFinal, makeFaceFinalFaceList] at hf₁ hf₂
  rw [mem_replace_iff hFg hf] at hf₁ hf₂
  rcases hf₁ with h1 | ⟨h1, h1ne⟩ <;> rcases hf₂ with h2 | ⟨h2, h2ne⟩
  · simp only [List.mem_singleton] at h1 h2
    exact absurd (h1.trans h2.symm) hne
  · simp only [List.mem_singleton] at h1
    subst h1
    exact mgp_edges_disj hmgp h2ne.symm hf h2 he
  · simp only [List.mem_singleton] at h2
    subst h2
    exact mgp_edges_disj (f' := f) hmgp h1ne h1 hf he
  · exact mgp_edges_disj hmgp hne h1 h2 he

/-- Invariants.thy: MakeFaceFinal_face_face_op -/
theorem MakeFaceFinal_face_face_op {g : Graph} {f : Face} (hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : face_face_op (makeFaceFinal f g) := by
  have hFg : g.faces.Nodup := minGraphProps11' hmgp
  have hff : face_face_op g := hmgp.2.2.2.2.2.2.2.2
  intro hlen f₁ hf₁ f₂ hf₂ hne
  have hlen' : g.faces.length ≠ 2 := by
    intro h2
    exact hlen (by
      show (makeFaceFinalFaceList f g.faces).length = 2
      rw [makeFaceFinalFaceList, length_replace1]; exact h2)
  simp only [makeFaceFinal, makeFaceFinalFaceList] at hf₁ hf₂
  rw [mem_replace_iff hFg hf] at hf₁ hf₂
  rcases hf₁ with h1 | ⟨h1, h1ne⟩ <;> rcases hf₂ with h2 | ⟨h2, h2ne⟩
  · simp only [List.mem_singleton] at h1 h2
    exact absurd (h1.trans h2.symm) hne
  · simp only [List.mem_singleton] at h1
    subst h1
    rcases hff hlen' f hf f₂ h2 h2ne.symm with ⟨e, he | he⟩
    · exact ⟨e, Or.inl he⟩
    · exact ⟨e, Or.inr he⟩
  · simp only [List.mem_singleton] at h2
    subst h2
    rcases hff hlen' f₁ h1 f hf h1ne with ⟨e, he | he⟩
    · exact ⟨e, Or.inl he⟩
    · exact ⟨e, Or.inr he⟩
  · exact hff hlen' f₁ h1 f₂ h2 hne

/-- Invariants.thy: MakeFaceFinal_minGraphProps -/
theorem MakeFaceFinal_minGraphProps {g : Graph} {f : Face} (hf : f ∈ g.faces)
    (hmgp : minGraphProps g) : minGraphProps (makeFaceFinal f g) :=
  ⟨MakeFaceFinal_minGraphProps' hf hmgp, MakeFaceFinal_facesAt_eq hf hmgp,
    MakeFaceFinal_faceListAt_len hf hmgp, MakeFaceFinal_facesAt_distinct hf hmgp,
    MakeFaceFinal_faces_distinct hf hmgp, MakeFaceFinal_faces_subset hf hmgp,
    MakeFaceFinal_edges_sym hf hmgp, MakeFaceFinal_edges_disj hf hmgp,
    MakeFaceFinal_face_face_op hf hmgp⟩

/-! ### Invariants of `subdivFace'` -/

/-- Invariants.thy: subdivFace'_holds_minGraphProps -/
theorem subdivFace'_holds_minGraphProps {v' : Vertex} :
    ∀ {g : Graph} {f : Face} {v : Vertex} {n : Nat} {ovl : List (Option Vertex)},
      pre_subdivFace' g f v' v n ovl → f ∈ g.faces → minGraphProps g →
        minGraphProps (subdivFace' g f v n ovl) := by
  intro g f v n ovl
  induction ovl generalizing g f v n with
  | nil =>
    intro _ hf hmgp
    rw [subdivFace'_nil]
    exact MakeFaceFinal_minGraphProps hf hmgp
  | cons ov ovl ih =>
    intro hpre hf hmgp
    cases ov with
    | none =>
      rw [subdivFace'_cons_none]
      exact ih (pre_subdivFace'_None hpre) hf hmgp
    | some w =>
      rw [subdivFace'_cons_some]
      by_cases h : (f.nextVertex v == w && n == 0) = true
      · rw [if_pos h]
        have h2 : n = 0 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
        subst h2
        exact ih (pre_subdivFace'_Some2 hpre) hf hmgp
      · rw [if_neg h]
        have hnext : f.nextVertex v = w → n ≠ 0 := by
          intro h1 h2
          apply h
          rw [h1, h2]
          simp
        have hsubg : ∀ x ∈ f.vertices, x ∈ g.vertices :=
          fun x hx => minGraphProps9 hmgp hf hx
        have pre_fdg := pre_subdivFace'_preFaceDiv hpre hf hnext hsubg
        have mgp' := splitFace_holds_minGraphProps pre_fdg hmgp
        have f2inF := splitFace_add_f21' (v := v) (a := w)
          (nvl := List.range' g.countVertices n) hf
        have pre' := pre_subdivFace'_Some1 hpre hf hnext hsubg rfl rfl
        exact ih pre' f2inF mgp'

/-- Invariants.thy: Edges_if (input abbreviation) -/
private def Edges_if (f : Face) (u v : Vertex) : Set (Vertex × Vertex) :=
  if u = v then ∅ else Edges (u :: between f.vertices u v ++ [v])

/-- Invariants.thy: FaceDivsionGraph_one_final_but -/
theorem FaceDivsionGraph_one_final_but {g g' : Graph} {u v r : Vertex}
    {f f₁ f₂ : Face} {vs : List Vertex}
    (mgp : minGraphProps g) (pre : pre_splitFace g u v f vs)
    (fdg : (f₁, f₂, g') = splitFace g u v f vs)
    (nrv : r ≠ v) (ruv : before (verticesFrom f r) u v) (rf : r ∈ f.vertices)
    (h1 : one_final_but g (Edges_if f r u)) :
    one_final_but g' (Edges (r :: between f₂.vertices r v ++ [v])) := by
  have hf₁ : f₁ = (split_face f u v vs).1 := congrArg Prod.fst fdg
  have hf₂ : f₂ = (split_face f u v vs).2 := congrArg (Prod.fst ∘ Prod.snd) fdg
  have hF0 : g'.faces =
      replace f [(split_face f u v vs).2] g.faces ++ [(split_face f u v vs).1] :=
    congrArg (Graph.faces ∘ Prod.snd ∘ Prod.snd) fdg
  rw [← hf₁, ← hf₂] at hF0
  have pre_split := pre_splitFace_pre_split_face pre
  have nf : f.final = false := pre.2.1
  have fg : f ∈ g.faces := pre.1
  have nuv : u ≠ v := pre_split.2.2.2.2.2
  have uinf : u ∈ f.vertices := pre_split.2.2.2.1
  have vinf : v ∈ f.vertices := pre_split.2.2.2.2.1
  have distf : f.vertices.Nodup := minGraphProps3 mgp fg
  have distFg : g.faces.Nodup := minGraphProps11' mgp
  have fvu : r ≠ u → between f.vertices v u =
      between f.vertices v r ++ r :: between f.vertices r u := by
    intro nru
    rcases before_between2 ruv distf rf with h | h
    · exact absurd h nru
    · have h2 := split_between distf vinf uinf h
      rw [if_neg (fun e => nrv e.symm)] at h2
      rw [h2, List.append_assoc]
      rfl
  have E₁ : f₁.edges = Edges (v :: vs.reverse ++ [u]) ∪
      Edges (u :: between f.vertices u v ++ [v]) := by
    rw [hf₁]
    exact edges_split_face1 pre_split
  have vf₂ : f₂.vertices = (v :: between f.vertices v u ++ [u]) ++ vs := by
    rw [hf₂]
    rfl
  have vinf₂ : v ∈ f₂.vertices := by
    rw [vf₂]
    exact List.mem_append_left _ List.mem_cons_self
  have rinf₂ : r ∈ f₂.vertices := by
    by_cases hru : r = u
    · subst hru
      rw [vf₂]
      exact List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
    · rw [vf₂, fvu hru]
      simp
  have distf₂ : f₂.vertices.Nodup := by
    rw [hf₂]
    exact split_face_distinct2' pre_split
  have evf₂r : r ≠ u → f₂.vertices =
      (v :: between f.vertices v r) ++ r :: (between f.vertices r u ++ u :: vs) := by
    intro nru
    rw [vf₂, fvu nru]
    simp [List.append_assoc]
  have f₂uv : between f₂.vertices u v = vs := by
    have hvin : v ∉ vs := pre_split.2.2.1 v vinf
    have evf₂ : f₂.vertices = (v :: between f.vertices v u) ++ u :: vs := by
      rw [vf₂]
      simp [List.append_assoc]
    have hsp := splitAt_dist_ram distf₂ evf₂
    rw [between_def, ← hsp]
    show (if vs.contains v then (splitAt v vs).1
        else vs ++ (splitAt v (v :: between f.vertices v u)).1) = vs
    rw [if_neg (mt List.contains_iff_mem.mp hvin)]
    have hdn : (v :: between f.vertices v u).Nodup := by
      have h : ((v :: between f.vertices v u) ++ u :: vs).Nodup := evf₂ ▸ distf₂
      exact (List.nodup_append.mp h).1
    have hsp2 : ([], between f.vertices v u) = splitAt v (v :: between f.vertices v u) :=
      splitAt_dist_ram hdn rfl
    rw [← hsp2]
    exact List.append_nil vs
  have f₂ru : r ≠ u → between f₂.vertices r u = between f.vertices r u := by
    intro nru
    have hsp := splitAt_dist_ram distf₂ (evf₂r nru)
    rw [between_def, ← hsp]
    show (if (between f.vertices r u ++ u :: vs).contains u then
        (splitAt u (between f.vertices r u ++ u :: vs)).1
      else (between f.vertices r u ++ u :: vs) ++
        (splitAt u (v :: between f.vertices v r)).1) = between f.vertices r u
    rw [if_pos (List.contains_iff_mem.mpr (List.mem_append_right _ List.mem_cons_self))]
    have hdn : (between f.vertices r u ++ u :: vs).Nodup := by
      have h : ((v :: between f.vertices v r) ++ r ::
          (between f.vertices r u ++ u :: vs)).Nodup := (evf₂r nru) ▸ distf₂
      exact (List.nodup_cons.mp (List.nodup_append.mp h).2.1).2
    have hsp2 : (between f.vertices r u, vs) =
        splitAt u (between f.vertices r u ++ u :: vs) := splitAt_dist_ram hdn rfl
    rw [← hsp2]
  have f₂rv : between f₂.vertices r v =
      (if r = u then [] else between f.vertices r u ++ [u]) ++ vs := by
    by_cases nru : r = u
    · subst nru
      rw [if_pos rfl]
      show between f₂.vertices r v = [] ++ vs
      rw [f₂uv]
      rfl
    · rw [if_neg nru]
      have u_bet_rv₂ : u ∈ between f₂.vertices r v := by
        have hsp := splitAt_dist_ram distf₂ (evf₂r nru)
        rw [between_def, ← hsp]
        show u ∈ (if (between f.vertices r u ++ u :: vs).contains v then
            (splitAt v (between f.vertices r u ++ u :: vs)).1
          else (between f.vertices r u ++ u :: vs) ++
            (splitAt v (v :: between f.vertices v r)).1)
        have hvin2 : v ∉ between f.vertices r u ++ u :: vs := by
          intro h
          have hd' : ((v :: between f.vertices v r) ++ r ::
              (between f.vertices r u ++ u :: vs)).Nodup := (evf₂r nru) ▸ distf₂
          obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hd'
          exact hdisj _ List.mem_cons_self _ (List.mem_cons_of_mem _ h) rfl
        rw [if_neg (mt List.contains_iff_mem.mp hvin2)]
        exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      have h2 := split_between distf₂ rinf₂ vinf₂ u_bet_rv₂
      rw [if_neg nru, f₂ru nru, f₂uv] at h2
      exact h2
  have E₂rv : Edges (r :: between f₂.vertices r v ++ [v]) =
      Edges_if f r u ∪ Edges (u :: vs ++ [v]) := by
    by_cases hru : r = u
    · have e1 : r :: between f₂.vertices r v ++ [v] = u :: vs ++ [v] := by
        rw [f₂rv, if_pos hru, List.nil_append, hru]
      rw [e1, hru]
      show Edges (u :: vs ++ [v]) =
        (if u = u then (∅ : Set (Vertex × Vertex))
          else Edges (u :: between f.vertices u u ++ [u])) ∪ Edges (u :: vs ++ [v])
      rw [if_pos rfl, Set.empty_union]
    · have hne2 : ((u :: vs) ++ [v]) ≠ [] :=
        List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _
      have e1 : (r :: between f₂.vertices r v) ++ [v] =
          (r :: between f.vertices r u) ++ ((u :: vs) ++ [v]) := by
        rw [f₂rv, if_neg hru]
        simp [List.append_assoc]
      rw [e1, Edges_append, if_neg (List.cons_ne_nil _ _), if_neg hne2,
        List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
      have e3 : Edges [u] = (∅ : Set (Vertex × Vertex)) := by
        rw [Edges_Cons, if_pos rfl]
      have e2 : Edges ((r :: between f.vertices r u) ++ [u]) =
          Edges (r :: between f.vertices r u) ∪
            {((r :: between f.vertices r u).getLast!, u)} := by
        rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
          List.head!_cons, e3, Set.union_empty]
      rw [show Edges_if f r u = Edges ((r :: between f.vertices r u) ++ [u]) from
          if_neg hru]
      rw [e2]
      ext ⟨a, b⟩
      simp only [Set.mem_union, Set.mem_singleton_iff]
      tauto
  have lift : ∀ f'' : Face, f'' ∈ g.faces → f''.final = true → f'' ∈ g'.faces := by
    intro f'' hf'' hfin''
    have hne : f'' ≠ f := fun e => by
      subst e
      rw [nf] at hfin''
      exact Bool.noConfusion hfin''
    rw [hF0]
    exact List.mem_append_left _ ((mem_replace_iff distFg fg).mpr (Or.inr ⟨hf'', hne⟩))
  intro f' hf' hfin' a b habf' hnab
  rw [hF0, List.mem_append, mem_replace_iff distFg fg] at hf'
  rcases hf' with (hf2 | ⟨hfg, hnfne⟩) | hf1
  · -- `f' = f₂`: the new second face
    simp only [List.mem_singleton] at hf2
    subst f'
    have hconv := edges_conv_Un_Edges distf₂ rinf₂ vinf₂ nrv
    rw [hconv, Set.mem_union] at habf'
    rcases habf' with h | h
    · exact absurd h hnab
    · have eq : between f₂.vertices v r = between f.vertices v r := by
        by_cases hru : r = u
        · subst hru
          have e : f₂.vertices = v :: (between f.vertices v r ++ r :: vs) := by
            rw [vf₂]
            simp [List.append_assoc]
          rw [e]
          exact between_front (between_not_r2 distf)
        · have e : f₂.vertices =
              v :: (between f.vertices v r ++ r :: (between f.vertices r u ++ u :: vs)) := by
            rw [vf₂, fvu hru]
            simp [List.append_assoc]
          rw [e]
          exact between_front (between_not_r2 distf)
      have abfvr : (a, b) ∈ Edges (v :: between f.vertices v r ++ [r]) := eq ▸ h
      have hprevr : pre_split_face f v r [] :=
        ⟨distf, List.nodup_nil, fun x _ hx => List.not_mem_nil hx, vinf, rf,
          fun e => nrv e.symm⟩
      have abf : (a, b) ∈ f.edges := Edges_between_edges abfvr hprevr
      by_cases hru : r = u
      · have hnot : (a, b) ∉ Edges_if f r u := by
          rw [hru]
          show (a, b) ∉ (if u = u then (∅ : Set (Vertex × Vertex)) else _)
          rw [if_pos rfl]
          exact Set.notMem_empty _
        rcases h1 f fg nf a b abf hnot with hE | ⟨f'', hf'', hfin'', hf''e⟩
        · rw [hru, show Edges_if f u u = (∅ : Set (Vertex × Vertex)) from if_pos rfl] at hE
          exact absurd hE (Set.notMem_empty _)
        · exact Or.inr ⟨f'', lift f'' hf'' hfin'', hfin'', hf''e⟩
      · have uvr : before (verticesFrom f v) r u := rotate_before_vFrom distf rf hru ruv
        have bet : r ∈ between f.vertices v u :=
          before_between uvr distf vinf (fun e => nrv e.symm)
        have hdisj : Edges (v :: between f.vertices v r ++ [r]) ∩
            Edges (r :: between f.vertices r u ++ [u]) = ∅ :=
          Edges_disj distf vinf uinf (fun e => nrv e.symm) hru bet
        have hnot1 : (a, b) ∉ Edges (r :: between f.vertices r u ++ [u]) := fun he => by
          have hm : (a, b) ∈ (∅ : Set (Vertex × Vertex)) := hdisj ▸ ⟨abfvr, he⟩
          exact hm
        have hnot2 : (b, a) ∉ Edges (r :: between f.vertices r u ++ [u]) := by
          intro he
          have hpre : pre_split_face f r u [] :=
            ⟨distf, List.nodup_nil, fun x _ hx => List.not_mem_nil hx, rf, uinf, hru⟩
          exact minGraphProps12 mgp fg abf (Edges_between_edges he hpre)
        have eif : Edges_if f r u = Edges (r :: between f.vertices r u ++ [u]) :=
          if_neg hru
        rcases h1 f fg nf a b abf (eif.symm ▸ hnot1) with hE | ⟨f'', hf'', hfin'', hf''e⟩
        · exact absurd (eif ▸ hE) hnot2
        · exact Or.inr ⟨f'', lift f'' hf'' hfin'', hfin'', hf''e⟩
  · -- `f' ∈ g.faces`, `f' ≠ f`
    have hsub : Edges_if f r u ⊆ f.edges := by
      intro p hp
      have hp2 : p ∈ (if r = u then (∅ : Set (Vertex × Vertex)) else
          Edges ((r :: between f.vertices r u) ++ [u])) := hp
      by_cases hru : r = u
      · rw [if_pos hru] at hp2
        exact absurd hp2 (Set.notMem_empty _)
      · rw [if_neg hru] at hp2
        exact Edges_between_edges hp2
          ⟨distf, List.nodup_nil, fun x _ hx => List.not_mem_nil hx, rf, uinf, hru⟩
    have hnot : (a, b) ∉ Edges_if f r u := by
      intro he
      exact absurd habf' (mgp_edges_disj mgp hnfne.symm fg hfg (hsub he))
    rcases h1 f' hfg hfin' a b habf' hnot with hE | ⟨f'', hf'', hfin'', hf''e⟩
    · exact Or.inl (by
        rw [E₂rv]
        exact Set.mem_union_left _ hE)
    · exact Or.inr ⟨f'', lift f'' hf'' hfin'', hfin'', hf''e⟩
  · -- `f' = f₁`: the new first face
    simp only [List.mem_singleton] at hf1
    subst f'
    rw [E₁, Set.mem_union] at habf'
    rcases habf' with hab | abfuv
    · have hba : (b, a) ∈ Edges (u :: vs ++ [v]) := by
        have h := in_Edges_rev.mpr hab
        rwa [show (v :: vs.reverse ++ [u]).reverse = u :: vs ++ [v] from by
          simp [List.reverse_append]] at h
      exact Or.inl (by
        rw [E₂rv]
        exact Set.mem_union_right _ hba)
    · have abf : (a, b) ∈ f.edges := Edges_between_edges abfuv pre_split
      by_cases hru : r = u
      · have hnot : (a, b) ∉ Edges_if f r u := by
          rw [hru]
          show (a, b) ∉ (if u = u then (∅ : Set (Vertex × Vertex)) else _)
          rw [if_pos rfl]
          exact Set.notMem_empty _
        rcases h1 f fg nf a b abf hnot with hE | ⟨f'', hf'', hfin'', hf''e⟩
        · rw [hru, show Edges_if f u u = (∅ : Set (Vertex × Vertex)) from if_pos rfl] at hE
          exact absurd hE (Set.notMem_empty _)
        · exact Or.inr ⟨f'', lift f'' hf'' hfin'', hfin'', hf''e⟩
      · have hdisj : Edges (r :: between f.vertices r u ++ [u]) ∩
            Edges (u :: between f.vertices u v ++ [v]) = ∅ :=
          Edges_disj distf rf vinf hru nuv (before_between ruv distf rf hru)
        have hnot1 : (a, b) ∉ Edges (r :: between f.vertices r u ++ [u]) := fun h => by
          have hm : (a, b) ∈ (∅ : Set (Vertex × Vertex)) := hdisj ▸ ⟨h, abfuv⟩
          exact hm
        have hnot2 : (b, a) ∉ Edges (r :: between f.vertices r u ++ [u]) := by
          intro h
          have hpre : pre_split_face f r u [] :=
            ⟨distf, List.nodup_nil, fun x _ hx => List.not_mem_nil hx, rf, uinf, hru⟩
          exact minGraphProps12 mgp fg abf (Edges_between_edges h hpre)
        have eif : Edges_if f r u = Edges (r :: between f.vertices r u ++ [u]) :=
          if_neg hru
        rcases h1 f fg nf a b abf (eif.symm ▸ hnot1) with hE | ⟨f'', hf'', hfin'', hf''e⟩
        · exact absurd (eif ▸ hE) hnot2
        · exact Or.inr ⟨f'', lift f'' hf'' hfin'', hfin'', hf''e⟩

/-- Invariants.thy: one_final_but_makeFaceFinal -/
theorem one_final_but_makeFaceFinal {g : Graph} {E : Set (Vertex × Vertex)} {f : Face}
    (mgp : minGraphProps g) (h1 : one_final_but g E) (hE : E ⊆ f.edges)
    (hf : f ∈ g.faces) (hnf : f.final = false) : one_final (makeFaceFinal f g) := by
  have hFg : g.faces.Nodup := minGraphProps11' mgp
  intro f' hf' hfin' a b hab _
  simp only [makeFaceFinal, makeFaceFinalFaceList] at hf'
  rw [mem_replace_iff hFg hf] at hf'
  rcases hf' with hf' | ⟨hf', hne⟩
  · simp only [List.mem_singleton] at hf'
    subst hf'
    exact Bool.noConfusion hfin'
  · have hnotE : (a, b) ∉ E := by
      intro he
      have hfe : (a, b) ∈ f.edges := hE he
      exact mgp_edges_disj mgp hne.symm hf hf' hfe hab
    rcases h1 f' hf' hfin' a b hab hnotE with hE' | ⟨f'', hf'', hfin'', hf''e⟩
    · exact Or.inr ⟨setFinal f,
        (mem_replace_iff hFg hf).mpr (Or.inl (List.mem_singleton_self _)), rfl, hE hE'⟩
    · have hne2 : f'' ≠ f := fun e => by
        subst e
        rw [hnf] at hfin''
        exact Bool.noConfusion hfin''
      exact Or.inr ⟨f'', (mem_replace_iff hFg hf).mpr (Or.inr ⟨hf'', hne2⟩), hfin'', hf''e⟩

/-! ### Increasing properties of `subdivFace'` -/

/-- Invariants.thy: one_final_subdivFace' -/
theorem one_final_subdivFace' {u : Vertex} :
    ∀ {g : Graph} {f : Face} {v : Vertex} {n : Nat} {ovs : List (Option Vertex)},
      pre_subdivFace' g f u v n ovs → minGraphProps g → f ∈ g.faces →
        one_final_but g (Edges_if f u v) → one_final (subdivFace' g f v n ovs) := by
  intro g f v n ovs
  induction ovs generalizing g f v n with
  | nil =>
    intro hpre hmgp hf h1
    rw [subdivFace'_nil]
    obtain ⟨hfin, huinf, hvinf, -, hdist, hbig⟩ := hpre
    rcases hbig with ⟨-, -, -, hcontra, -, -, -⟩ | ⟨-, hunev⟩
    · exact absurd rfl hcontra
    · have hpre' : pre_split_face f u v [] :=
        ⟨hdist, List.nodup_nil, fun x _ hx => List.not_mem_nil hx, huinf, hvinf, hunev⟩
      have hsub : Edges_if f u v ⊆ f.edges := by
        intro p hp
        have hp2 : p ∈ (if u = v then (∅ : Set (Vertex × Vertex)) else
            Edges ((u :: between f.vertices u v) ++ [v])) := hp
        rw [if_neg hunev] at hp2
        exact Edges_between_edges hp2 hpre'
      exact one_final_but_makeFaceFinal hmgp h1 hsub hf hfin
  | cons ov ovs ih =>
    intro hpre hmgp hf h1
    cases ov with
    | none =>
      rw [subdivFace'_cons_none]
      exact ih (pre_subdivFace'_None hpre) hmgp hf h1
    | some w =>
      rw [subdivFace'_cons_some]
      have uw : u ≠ w := by
        have h := hpre.2.2.2.1
        rw [removeNones_hd] at h
        intro e
        subst e
        exact h List.mem_cons_self
      by_cases h : (f.nextVertex v == w && n == 0) = true
      · rw [if_pos h]
        have hnvw : f.nextVertex v = w := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
        have h2n : n = 0 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
        subst h2n
        have uf : u ∈ f.vertices := hpre.2.1
        have vf : v ∈ f.vertices := hpre.2.2.1
        have hdist : f.vertices.Nodup := hpre.2.2.2.2.1
        have hsub : Edges_if f u v ⊆ Edges_if f u w := by
          intro p hp
          have hp2 : p ∈ (if u = v then (∅ : Set (Vertex × Vertex)) else
              Edges ((u :: between f.vertices u v) ++ [v])) := hp
          show p ∈ (if u = w then (∅ : Set (Vertex × Vertex)) else
              Edges ((u :: between f.vertices u w) ++ [w]))
          by_cases huv : u = v
          · rw [if_pos huv] at hp2
            exact absurd hp2 (Set.notMem_empty _)
          · rw [if_neg uw]
            rw [if_neg huv] at hp2
            have hpb : pre_between f.vertices u v := ⟨hdist, uf, vf, huv⟩
            have hbw : between f.vertices u w = between f.vertices u v ++ [v] := by
              rw [← hnvw]
              exact between_nextElem hpb
            rw [hbw, Edges_append, if_neg (List.cons_ne_nil _ _),
              if_neg (List.cons_ne_nil _ _)]
            exact Set.mem_union_left _ (Set.mem_union_left _ hp2)
        exact ih (pre_subdivFace'_Some2 hpre) hmgp hf (one_final_but_antimono h1 hsub)
      · rw [if_neg h]
        have hnext : f.nextVertex v = w → n ≠ 0 := by
          intro h1' h2'
          apply h
          rw [h1', h2']
          simp
        have fsubg : ∀ x ∈ f.vertices, x ∈ g.vertices :=
          fun x hx => minGraphProps9 hmgp hf hx
        have pre_fdg := pre_subdivFace'_preFaceDiv hpre hf hnext fsubg
        have uf : u ∈ f.vertices := hpre.2.1
        have bet : before (verticesFrom f u) v w := by
          rcases hpre.2.2.2.2.2 with ⟨-, hb, -, -, -, -, -⟩ | ⟨hcontra, -⟩
          · rw [removeNones_hd, List.head!_cons] at hb
            exact hb
          · exact absurd hcontra (List.cons_ne_nil _ _)
        have h2raw := FaceDivsionGraph_one_final_but
          (f₁ := (splitFace g v w f (List.range' g.countVertices n)).1)
          (f₂ := (splitFace g v w f (List.range' g.countVertices n)).2.1)
          (g' := (splitFace g v w f (List.range' g.countVertices n)).2.2)
          hmgp pre_fdg rfl uw bet uf h1
        have h2 : one_final_but (splitFace g v w f (List.range' g.countVertices n)).2.2
            (Edges_if (splitFace g v w f (List.range' g.countVertices n)).2.1 u w) := by
          rw [show Edges_if (splitFace g v w f (List.range' g.countVertices n)).2.1 u w =
              Edges ((u :: between
                (splitFace g v w f (List.range' g.countVertices n)).2.1.vertices u w) ++ [w])
              from if_neg uw]
          exact h2raw
        exact ih (pre_subdivFace'_Some1 hpre hf hnext fsubg rfl rfl)
          (splitFace_holds_minGraphProps pre_fdg hmgp)
          (splitFace_add_f21' (v := v) (a := w) (nvl := List.range' g.countVertices n) hf)
          h2

/-- Invariants.thy: subdivFace'_incr -/
theorem subdivFace'_incr {P Q : Graph → Graph → Prop} {v' : Vertex}
    (Ptrans : ∀ x y z, Q x y → P y z → P x z)
    (mkFin : ∀ f g, f ∈ g.faces → f.final = false → P g (makeFaceFinal f g))
    (fdg_incr : ∀ g u v f vs, pre_splitFace g u v f vs →
      Q g (splitFace g u v f vs).2.2) :
    ∀ {g : Graph} {f : Face} {v : Vertex} {n : Nat} {ovl : List (Option Vertex)},
      pre_subdivFace' g f v' v n ovl → minGraphProps g → f ∈ g.faces →
        P g (subdivFace' g f v n ovl) := by
  intro g f v n ovl
  induction ovl generalizing g f v n with
  | nil =>
    intro hpre _ hf
    rw [subdivFace'_nil]
    exact mkFin f g hf hpre.1
  | cons ov ovl ih =>
    intro hpre hmgp hf
    cases ov with
    | none =>
      rw [subdivFace'_cons_none]
      exact ih (pre_subdivFace'_None hpre) hmgp hf
    | some w =>
      rw [subdivFace'_cons_some]
      by_cases h : (f.nextVertex v == w && n == 0) = true
      · rw [if_pos h]
        have h2 : n = 0 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
        subst h2
        exact ih (pre_subdivFace'_Some2 hpre) hmgp hf
      · rw [if_neg h]
        have hnext : f.nextVertex v = w → n ≠ 0 := by
          intro h1 h2
          apply h
          rw [h1, h2]
          simp
        have hsubg : ∀ x ∈ f.vertices, x ∈ g.vertices :=
          fun x hx => minGraphProps9 hmgp hf hx
        have pre_fdg := pre_subdivFace'_preFaceDiv hpre hf hnext hsubg
        exact Ptrans _ _ _ (fdg_incr _ _ _ _ _ pre_fdg)
          (ih (pre_subdivFace'_Some1 hpre hf hnext hsubg rfl rfl)
            (splitFace_holds_minGraphProps pre_fdg hmgp)
            (splitFace_add_f21' (v := v) (a := w)
              (nvl := List.range' g.countVertices n) hf))

/-- Auxiliary: filtering after a single replacement by an element failing the
predicate leaves the filter unchanged (inline `simp` step of
`splitFace_incr_faces` in the source). -/
private theorem filter_replace_singleton_of_false {P : α → Bool} [BEq α] [LawfulBEq α]
    {x y : α} {xs : List α} (hx : P x = false) (hy : P y = false) :
    (replace x [y] xs).filter P = xs.filter P := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      have e1 : replace z [y] (z :: zs) = [y] ++ zs := by
        simp only [replace, beq_self_eq_true, ↓reduceIte]
      have e2 : [y].filter P = [] := by
        rw [List.filter_cons, if_neg (by simp [hy]), List.filter_nil]
      have e3 : (z :: zs).filter P = zs.filter P := by
        rw [List.filter_cons, if_neg (by simp [hx])]
      rw [e1, List.filter_append, e2, List.nil_append, e3]
    · have e1 : replace x [y] (z :: zs) = z :: replace x [y] zs := by
        simp only [replace, if_neg (fun h => hzx (beq_iff_eq.mp h))]
      rw [e1, List.filter_cons, List.filter_cons]
      by_cases hpz : P z = true
      · rw [if_pos hpz, if_pos hpz, ih]
      · rw [if_neg hpz, if_neg hpz, ih]

/-- Invariants.thy: splitFace_incr_faces -/
theorem splitFace_incr_faces {g : Graph} {u v : Vertex} {f : Face} {vs : List Vertex}
    (pre : pre_splitFace g u v f vs) :
    finals (splitFace g u v f vs).2.2 = finals g ∧
      (nonFinals (splitFace g u v f vs).2.2).length = (nonFinals g).length + 1 := by
  obtain ⟨hf, hfin, -, -, -, -, -, -, -, -⟩ := pre
  have hf1 : (split_face f u v vs).1.final = false := rfl
  have hf2 : (split_face f u v vs).2.final = false := rfl
  refine ⟨?_, ?_⟩
  · show (replace f [(split_face f u v vs).2] g.faces ++
        [(split_face f u v vs).1]).filter Face.final = g.faces.filter Face.final
    rw [List.filter_append,
      show ([(split_face f u v vs).1].filter Face.final) = [] from by
        simp [hf1],
      List.append_nil]
    exact filter_replace_singleton_of_false hfin hf2
  · show ((replace f [(split_face f u v vs).2] g.faces ++
        [(split_face f u v vs).1]).filter fun f => !f.final).length =
      (g.faces.filter fun f => !f.final).length + 1
    rw [List.filter_append,
      show ([(split_face f u v vs).1].filter fun f => !f.final) =
          [(split_face f u v vs).1] from by
        simp [hf1],
      List.length_append, List.length_singleton]
    have e2 := length_filter_replace2 (P := fun f => !f.final) (x := f)
      (ys := [(split_face f u v vs).2]) (xs := g.faces) hf (by simp [hfin])
    rw [show ([(split_face f u v vs).2].filter fun f => !f.final) =
        [(split_face f u v vs).2] from by simp [hf2], List.length_singleton] at e2
    omega

/-- Invariants.thy: subdivFace'_incr_faces -/
theorem subdivFace'_incr_faces {g : Graph} {f : Face} {u v : Vertex} {n : Nat}
    {ovs : List (Option Vertex)}
    (pre : pre_subdivFace' g f u v n ovs) (hmgp : minGraphProps g) (hf : f ∈ g.faces) :
    (finals (subdivFace' g f v n ovs)).length = (finals g).length + 1 ∧
      (nonFinals g).length - 1 ≤ (nonFinals (subdivFace' g f v n ovs)).length :=
  subdivFace'_incr (v' := u)
    (P := fun g g' =>
      (finals g').length = (finals g).length + 1 ∧
        (nonFinals g).length - 1 ≤ (nonFinals g').length)
    (Q := fun g g' =>
      finals g' = finals g ∧ (nonFinals g').length = (nonFinals g).length + 1)
    (fun x y z hxy hyz => by
      obtain ⟨h1, h2⟩ := hxy
      obtain ⟨h3, h4⟩ := hyz
      exact ⟨by rw [h3, h1], by omega⟩)
    (fun f' g' hf' hfin' =>
      ⟨len_finals_makeFaceFinal hf' hfin',
        by rw [len_nonFinals_makeFaceFinal hfin' hf']⟩)
    (fun g' u' v' f' vs' hpre => splitFace_incr_faces hpre)
    pre hmgp hf

/-- Invariants.thy: two_faces_subdivFace' -/
theorem two_faces_subdivFace' {g : Graph} {f : Face} {u v : Vertex} {n : Nat}
    {ovs : List (Option Vertex)}
    (pre : pre_subdivFace' g f u v n ovs) (hmgp : minGraphProps g) (hf : f ∈ g.faces)
    (h2 : 2 ≤ g.faces.length) : 2 ≤ (subdivFace' g f v n ovs).faces.length := by
  obtain ⟨h1, h2'⟩ := subdivFace'_incr_faces pre hmgp hf
  have s1 := len_faces_sum g
  have s2 := len_faces_sum (subdivFace' g f v n ovs)
  omega

/-- Invariants.thy: incrIndexList_less_eq -/
theorem incrIndexList_less_eq {ls : List Nat} {m nmax n : Nat}
    (h : incrIndexList ls m nmax) (hn : n + 1 < ls.length) : ls[n]! ≤ ls[n + 1]! := by
  have hinc : increasing ls := h.2.2.2.2.2.2
  have hn0 : n < ls.length := by omega
  have e2 : ls.drop (n + 1) = ls[n + 1]! :: ls.drop (n + 2) := by
    show ls.drop (n + 1) = ls[n + 1]! :: ls.drop (n + 1 + 1)
    rw [List.drop_eq_getElem_cons hn, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hn]
    rfl
  have e : ls = ls.take n ++ ls[n]! :: ([] ++ ls[n + 1]! :: ls.drop (n + 2)) := by
    rw [List.nil_append, ← e2]
    exact id_take_nth_drop hn0
  exact increasing1 hinc e

/-- Invariants.thy: incrIndexList_less -/
theorem incrIndexList_less {ls : List Nat} {m nmax n : Nat}
    (h : incrIndexList ls m nmax) (hn : n + 1 < ls.length)
    (hne : ls[n]! ≠ ls[n + 1]!) : ls[n]! < ls[n + 1]! :=
  lt_of_le_of_ne (incrIndexList_less_eq h hn) hne

/-- Invariants.thy: neighbors_edges -/
theorem neighbors_edges {g : Graph} {a b : Vertex} (mgp : minGraphProps g)
    (ha : a ∈ g.vertices) : b ∈ neighbors g a ↔ (a, b) ∈ g.edges := by
  constructor
  · intro h
    simp only [neighbors, List.mem_map] at h
    obtain ⟨f, hf, hfb⟩ := h
    exact ⟨f, minGraphProps5 mgp ha hf,
      edges_face_eq.mpr ⟨hfb, minGraphProps6 mgp ha hf⟩⟩
  · intro h
    obtain ⟨f, hf, hab⟩ := h
    obtain ⟨hba, hav⟩ := edges_face_eq.mp hab
    exact List.mem_map.mpr ⟨f, minGraphProps7 mgp hf hav, hba⟩

/-- Invariants.thy: no_self_edges -/
theorem no_self_edges {g : Graph} {a : Vertex} (hmgp' : minGraphProps' g) :
    (a, a) ∉ g.edges := by
  rintro ⟨f, hf, haa⟩
  obtain ⟨hlen, hd⟩ := hmgp' f hf
  rw [is_nextElem_edges_eq hd] at haa
  rcases haa with hsub | ⟨hne, h1, h2⟩
  · obtain ⟨as, bs, hvs⟩ := hsub
    have hd' : (as ++ [a, a] ++ bs).Nodup := hvs ▸ hd
    have h2 : [a, a].Nodup := (List.nodup_append.mp (List.nodup_append.mp hd').1).2.1
    exact (List.nodup_cons.mp h2).1 List.mem_cons_self
  · obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
    rw [hxs] at hlen hd h1 h2
    have hxsne : xs ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨hxnin, -⟩ := List.nodup_cons.mp hd
    have e1 : (x :: xs).head! = x := List.head!_cons x xs
    have e2 : (x :: xs).getLast! = xs.getLast! := getLast!_cons_of_ne_nil hxsne
    rw [e1] at h2
    rw [e2] at h1
    exact hxnin (h2 ▸ h1.symm ▸ getLast!_mem hxsne)

/-- Invariants.thy: duplicateEdge_is_duplicateEdge_eq -/
theorem duplicateEdge_is_duplicateEdge_eq {g : Graph} {f : Face} {a b : Vertex}
    (mgp : minGraphProps g) (hf : f ∈ g.faces) (ha : a ∈ f.vertices)
    (hb : b ∈ f.vertices) :
    (duplicateEdge g f a b = true) ↔ is_duplicateEdge g f a b := by
  have hdist : f.vertices.Nodup := minGraphProps3 mgp hf
  have hag : a ∈ g.vertices := minGraphProps9 mgp hf ha
  simp only [duplicateEdge, decide_eq_true_iff]
  rw [neighbors_edges mgp hag]
  have aux : (a, b) ∈ g.edges → (a, b) ∉ f.edges → (b, a) ∉ f.edges →
      2 ≤ directedLength f a b ∧ 2 ≤ directedLength f b a ∧ (a, b) ∈ g.edges := by
    intro hab hnab hnba
    have hne : a ≠ b := by
      intro e
      subst e
      exact absurd hab (no_self_edges mgp.1)
    have hbta : between f.vertices a b ≠ [] := by
      intro e
      exact hnab ((is_nextElem_edges_eq hdist).mpr
        (is_nextElem_between_empty' e hdist ha hb hne))
    have hbtb : between f.vertices b a ≠ [] := by
      intro e
      exact hnba ((is_nextElem_edges_eq hdist).mpr
        (is_nextElem_between_empty' e hdist hb ha (fun h' => hne h'.symm)))
    refine ⟨?_, ?_, hab⟩
    · unfold directedLength
      rw [if_neg (fun h => hne (beq_iff_eq.mp h))]
      have := List.length_pos_iff.mpr hbta
      omega
    · unfold directedLength
      rw [if_neg (fun h => hne (beq_iff_eq.mp h).symm)]
      have := List.length_pos_iff.mpr hbtb
      omega
  constructor
  · rintro ⟨h1, h2, hab⟩
    have hba : (b, a) ∈ g.edges := minGraphProps10 mgp hab
    by_cases heq : a = b
    · subst heq
      exact absurd hab (no_self_edges mgp.1)
    have hnab : (a, b) ∉ f.edges := by
      intro he
      have hbt : between f.vertices a b = [] :=
        is_nextElem_between_empty hdist ((is_nextElem_edges_eq hdist).mp he)
      have hdl : directedLength f a b = 1 := by
        unfold directedLength
        rw [if_neg (fun h => heq (beq_iff_eq.mp h)), hbt]
        rfl
      omega
    have hnba : (b, a) ∉ f.edges := by
      intro he
      have hbt : between f.vertices b a = [] :=
        is_nextElem_between_empty hdist ((is_nextElem_edges_eq hdist).mp he)
      have hdl : directedLength f b a = 1 := by
        unfold directedLength
        rw [if_neg (fun h => heq (beq_iff_eq.mp h).symm), hbt]
        rfl
      omega
    exact Or.inl ⟨hab, hnab, hnba⟩
  · rintro (⟨hab, hnab, hnba⟩ | ⟨hba, hnba, hnab⟩)
    · exact aux hab hnab hnba
    · exact aux (minGraphProps10 mgp hba) hnab hnba

end Kepler.Graphs

/-
Port of block C (lines 1913–2827) of the Isabelle AFP "Flyspeck-Tame" theory
`Invariants.thy`: `subsection Invariants of makeFaceFinal`,
`subsection Invariants of subdivFace'`, `subsection Invariants of Seed`,
`subsection Increasing properties of subdivFace'` and
`subsection Main invariant theorems`.

Source: `reference/afp-flyspeck-tame/Invariants.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Conventions follow `InvariantsA.lean` / `InvariantsB.lean`.

Porting status (time-boxed first pass): ported are the `makeFaceFinal`
subsection (1913–2063, complete), `subdivFace'_holds_minGraphProps` (2066),
`one_final_but_makeFaceFinal` (2320), the increasing-properties subsection
(2631–2775, complete: `subdivFace'_incr`, `splitFace_incr_faces`,
`subdivFace'_incr_faces`, `two_faces_subdivFace'`) and
`incrIndexList_less_eq` / `incrIndexList_less` (2471–2481).

Still to port (continuation): `FaceDivsionGraph_one_final_but` (2106–2317),
`one_final_subdivFace'` (2340), `neighbors_edges` (2419), `no_self_edges`
(2434), `duplicateEdge_is_duplicateEdge_eq` (2442), the `Seed` subsection
(2483–2547; `Seed_holds_facesAt_distinct`/`faces_distinct` need the unported
ListAux lemmas `fst/snd_splitAt_upt`, `fst/snd_splitAt_rev`,
`upt_conv_Cons`), `pre_subdivFace_indexToVertexList` (2550),
`next_plane0_via_subdivFace'` (2678), `next_plane0_incr` (2703),
`next_plane0_incr_faces` (2753), and the main theorems `inv_genPoly` (2778)
and `inv_inv_next_plane0` (2817), which depend on the above.
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

end Kepler.Graphs

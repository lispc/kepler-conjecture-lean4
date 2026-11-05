/-
P22EdgeCount: the dart/edge cardinality (`#darts = 2 * #edges`) and the
incidence-counting bound `#{(f,e)} ≤ 2 * #edges`, feeding
`polyhedron_edge_sum` (#9 of PackingAuto22).

`p22_incidences_le_two_mul_edges` takes the `SEGMENT_EDGE_ONTO` direction as a
hypothesis; `PackingAuto22.SEGMENT_EDGE_ONTO` supplies it at the call site.
-/
import Kepler.Text.P22EdgeFacets

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Dart / edge cardinality and the incidence bound -/

/-- Every edge of a fan contributes exactly two darts. -/
theorem p22_dart1OfFan_ncard_eq_two_mul (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : Fan.FAN x V E) :
    (Fan.dart1OfFan V E).ncard = 2 * E.ncard := by
  classical
  set T : Set V3 → Set (V3 × V3) := fun e => {d : V3 × V3 | ({d.1, d.2} : Set V3) = e}
    with hT
  have hEfin : E.Finite := Fan.setEdgesFiniteFan hfan
  have hdecomp : Fan.dart1OfFan V E = ⋃ e ∈ E, T e := by
    ext d
    simp only [Fan.dart1OfFan, Set.mem_setOf_eq, hT, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨e, he, hde⟩
      rw [← hde] at he
      exact he
  have hfin : ∀ e ∈ E, (T e).Finite := by
    intro e he
    obtain ⟨hf, -⟩ := hfan.2.1 e he
    refine (hf.prod hf).subset ?_
    rintro ⟨a, b⟩ hab
    have ha : a ∈ e := hab ▸ Set.mem_insert a {b}
    have hb : b ∈ e := hab ▸ Set.mem_insert_of_mem a (Set.mem_singleton b)
    exact ⟨ha, hb⟩
  have hterm : ∀ e ∈ E, (T e).ncard = 2 := by
    intro e he
    obtain ⟨hf, hc⟩ := hfan.2.1 e he
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.1 hc
    have heq : e = ({a, b} : Set V3) := by
      rw [← hf.coe_toFinset, hset]
      simp
    have hTe : T e = ({(a, b), (b, a)} : Set (V3 × V3)) := by
      ext d
      obtain ⟨d1, d2⟩ := d
      rw [hT]
      simp only [Set.mem_setOf_eq, heq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq]
      constructor
      · intro h
        rcases Set.pair_eq_pair_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rw [h1, h2]
        · rw [h1, h2]
          exact (Set.pair_comm a b).symm
    rw [hTe, Set.ncard_pair]
    intro h
    exact hab (by simpa using congrArg Prod.fst h)
  have hdisj : E.PairwiseDisjoint T := by
    intro e1 he1 e2 he2 hne
    refine Set.disjoint_left.2 ?_
    rintro d hd1 hd2
    rw [hT] at hd1 hd2
    simp only [Set.mem_setOf_eq] at hd1 hd2
    exact hne (hd1 ▸ hd2)
  rw [hdecomp, Set.Finite.ncard_biUnion hEfin hfin hdisj]
  rw [finsum_mem_eq_finite_toFinset_sum _ hEfin]
  have hcongr : ∀ e ∈ hEfin.toFinset, (T e).ncard = 2 := fun e he =>
    hterm e ((Set.Finite.mem_toFinset hEfin).1 he)
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul,
    Set.ncard_eq_toFinset_card E hEfin]
  ring

/-- `edges P` is finite: every edge is a two-element subset of the (finite)
extreme point set. -/
theorem p22F_edges_finite {P : Set V3} (hp : polyhedron P) : (edges P).Finite := by
  refine (FINITE_POLYHEDRON_EXTREME_POINTS hp).powerset.subset ?_
  rintro e ⟨v, w, rfl, hedge⟩
  obtain ⟨-, hv, hw⟩ := SEGMENT_EDGE_OF hedge
  intro x hx
  rcases Set.mem_insert_iff.1 hx with rfl | hx
  · exact hv
  · rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hw

/-- A facet of a facet is an edge (no boundedness needed). -/
private theorem edge_of_facet_edge {p c e : Set V3} (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p) (he : FacetOf e c) : edgeOf e p := by
  have hdc : affDim c = 2 := p22F_facet_affDim_two p c hp hi hc
  refine ⟨FaceOf.trans he.1 hc.1, ?_⟩
  rw [he.2.2, hdc]
  norm_num

/-- Incidence count `#{(f,e) : e facet of f, f facet of P} ≤ 2 * #edges(P)`.
The hypothesis `hseg` is exactly the `SEGMENT_EDGE_ONTO` direction (available in
`PackingAuto22`): every 1-dimensional face is a closed segment. -/
theorem p22_incidences_le_two_mul_edges (P : Set V3) (hp : polyhedron P)
    (hb : Bornology.IsBounded P) (hi : (0 : V3) ∈ interior P)
    (hseg : ∀ e : Set V3, edgeOf e P → ∃ p : V3 × V3, e = segment ℝ p.1 p.2) :
    ({fe : Set V3 × Set V3 | FacetOf fe.1 P ∧ FacetOf fe.2 fe.1}).ncard
      ≤ 2 * (edges P).ncard := by
  classical
  set D : Set (Set V3) := {e : Set V3 | edgeOf e P} with hD
  set Gg : Set V3 → Set (Set V3) := fun e => {f : Set V3 | FacetOf f P ∧ FacetOf e f}
    with hG
  set Ff : Set V3 → Set (Set V3 × Set V3) := fun e => Gg e ×ˢ ({e} : Set (Set V3))
    with hF
  have hDfin : D.Finite := by
    rw [hD]
    exact (FINITE_POLYHEDRON_FACES hp).subset (fun e he => he.1)
  -- step 1: `D` injects into `edges P`
  have hDle : D.ncard ≤ (edges P).ncard := by
    set φ : Set V3 → Set V3 := fun e =>
      if h : edgeOf e P then
        ({(Classical.choose (hseg e h)).1, (Classical.choose (hseg e h)).2} : Set V3)
      else e with hφ
    have hφspec : ∀ e (h : edgeOf e P),
        φ e = ({(Classical.choose (hseg e h)).1,
          (Classical.choose (hseg e h)).2} : Set V3) := by
      intro e h
      rw [hφ]
      exact dif_pos h
    have hmem : ∀ e ∈ D, φ e ∈ edges P := by
      intro e he
      have heo : edgeOf e P := he
      rw [hφspec e heo, edges, Set.mem_setOf_eq]
      refine ⟨_, _, rfl, ?_⟩
      rw [← Classical.choose_spec (hseg e heo)]
      exact heo
    have hinj : Set.InjOn φ D := by
      intro e1 he1 e2 he2 heq
      have he1o : edgeOf e1 P := he1
      have he2o : edgeOf e2 P := he2
      have h1 := Classical.choose_spec (hseg e1 he1o)
      have h2 := Classical.choose_spec (hseg e2 he2o)
      rw [hφspec e1 he1o, hφspec e2 he2o] at heq
      have hseg_eq : segment ℝ (Classical.choose (hseg e1 he1o)).1
            (Classical.choose (hseg e1 he1o)).2
          = segment ℝ (Classical.choose (hseg e2 he2o)).1
            (Classical.choose (hseg e2 he2o)).2 := by
        rcases Set.pair_eq_pair_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]
          exact (segment_symm ℝ _ _).symm
      rw [h1, h2, hseg_eq]
    exact Set.ncard_le_ncard_of_injOn φ hmem hinj (p22F_edges_finite hp)
  -- step 2: `M ≤ 2 * D.ncard`
  have hdecomp : ({fe : Set V3 × Set V3 | FacetOf fe.1 P ∧ FacetOf fe.2 fe.1})
      = ⋃ e ∈ D, Ff e := by
    ext fe
    simp only [Set.mem_setOf_eq, hF, hG, Set.mem_iUnion, exists_prop, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hfe1, hfe2⟩
      exact ⟨fe.2, by rw [hD]; exact edge_of_facet_edge hp hi hfe1 hfe2, ⟨hfe1, hfe2⟩, rfl⟩
    · rintro ⟨e, -, ⟨h1, h3⟩, h2⟩
      rw [← h2] at h3
      exact ⟨h1, h3⟩
  have hfinF : ∀ e ∈ D, (Ff e).Finite := by
    intro e _
    exact ((FINITE_POLYHEDRON_FACETS hp).subset (fun f hf => hf.1)).prod
      (Set.finite_singleton e)
  have hle1 : ({fe : Set V3 × Set V3 | FacetOf fe.1 P ∧ FacetOf fe.2 fe.1}).ncard
      ≤ ∑ᶠ e ∈ D, (Ff e).ncard := by
    rw [hdecomp]
    exact Set.Finite.ncard_biUnion_le hDfin Ff
  have hterm : ∀ e ∈ D, (Ff e).ncard ≤ 2 := by
    intro e _
    have hGF : (Ff e).ncard = (Gg e).ncard := by
      rw [Set.ncard_prod, Set.ncard_singleton, mul_one]
    rw [hGF]
    exact p22_edge_facets_ncard_le_two P e hp hb hi
  have hsum_le : ∑ᶠ e ∈ D, (Ff e).ncard ≤ ∑ᶠ e ∈ D, (2 : ℕ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hDfin,
      finsum_mem_eq_finite_toFinset_sum _ hDfin]
    exact Finset.sum_le_sum (fun e he =>
      hterm e ((Set.Finite.mem_toFinset hDfin).1 he))
  have htwo : ∑ᶠ e ∈ D, (2 : ℕ) = 2 * D.ncard := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hDfin, Finset.sum_const, smul_eq_mul,
      Set.ncard_eq_toFinset_card D hDfin, mul_comm]
  calc ({fe : Set V3 × Set V3 | FacetOf fe.1 P ∧ FacetOf fe.2 fe.1}).ncard
      ≤ ∑ᶠ e ∈ D, (Ff e).ncard := hle1
    _ ≤ ∑ᶠ e ∈ D, (2 : ℕ) := hsum_le
    _ = 2 * D.ncard := htwo
    _ ≤ 2 * (edges P).ncard := Nat.mul_le_mul_left 2 hDle

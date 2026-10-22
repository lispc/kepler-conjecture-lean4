/-
Packing chapter, Marchal-cells measure lane: cell symmetries, `VX`, and
measurability.

HOL sources (VU KHAC KY, "Packing (Marchal cells)"):
- `scripts/packing/RVFXZBU.hl` (198 lines): `RVFXZBU` — the Marchal cell
  `mcell i V ul` is invariant under the left action of a permutation of
  `0..i-1` (case split `i = 0,1,2,3`, else 4).
- `scripts/packing/HDTFNFZ.hl` (114 lines): `HDTFNFZ` — for a non-null cell
  `X = mcell k V ul`, the vertex set `VX V X` is `V ∩ X` (via `LEPJBDJ`).
- `scripts/packing/YNHYJIT.hl` (107 lines): `YNHYJIT` — left-action
  invariance of `barV` and of the omega points at levels `i-1..3` in the
  small-truncation regime.
- `scripts/packing/URRPHBZ1.hl` (688 lines, emailed Ky→Hales 2011-07-14):
  geometry lemmas `INTER_RCONE_GE_IMP_BETWEEN_PROJ_POINT`,
  `INTER_RCONE_GE_LE_lemma`, `MCELL_2_PROPERTIES_lemma1`, `BOUNDED_MCELL`,
  the re-export `MEASURABLE_MCELL` (compact ⇒ measurable) and `URRPHBZ1`
  (= `MEASURABLE_MCELL`).

Encoding notes.
- HOL `real^3` ↔ `V3` (Kepler.Geom = `EuclideanSpace ℝ (Fin 3)`); `dot` ↔
  `⬝ᵥ` (bridged to `inner ℝ` by `Kepler.Geom.inner_eq_dot`); `dist (a,b)` ↔
  `dist a b`; `ball` ↔ `Metric.ball`; `midpoint (a,b)` ↔ `midpoint ℝ a b`.
- `truncate_simplex`/`omega_list_n`/`hl`/`barV`/`saturated`/`set_of_list`/
  `mxi`/`rogers`/`rcone_ge`/`rcone_gt`/`mcell*`/`VX`/`cell_params`/`NULLSET`
  ↔ the PackingAuto2 definitions (`truncateSimplex`, `omegaListN`, `hl`,
  `barV`, `saturated`, `setOfList`, `mxi`, `rogers`, `rconeGe`, `rconeGt`,
  `mcell*`, `VX`, `cellParams`, `nullSet`).
- HOL `proj_point` and `between` are absent from the port; private `_p10`
  copies are added here (HL: `proj_point v w = v % ((w dot v)/(v dot v))`,
  `between x (a,b) = dist(a,x) + dist(x,b) = dist(a,b)`).
- Encoding caveat (weak `permutes`) — RULING 2026-09-18, verdict (b) TOO
  STRONG: `PackingAuto2.permutes` is the pointwise-membership relation
  `∀ x, x ∈ s ↔ p x ∈ s`, whereas HOL-Light `permutes` (`Library/perms.ml`)
  is complement-fixing, `p permutes s := ∀ x, x ∉ s → p x = x`; for the
  typed `Equiv.Perm ℕ` this means `p permutes 0..(i-1)` is *exactly*
  `∀ j, i ≤ j → p j = j` (the earlier `≥ i-1` guess here was off by one:
  the block `0..i-1` itself remains free to move). The first drafts of
  `RVFXZBU`/`YNHYJIT` carried only the weak relation and were false as
  encoded (e.g. `i = 2` with `p` the transposition of `2,3` weakly permutes
  `Icc 0 1` but changes `hl ul`, hence `mcell4`, on `[u0;u1;u2;u3]`).
  ENCODING-FIX: both statements now carry the explicit tail-fixedness
  hypothesis `∀ j, i ≤ j → p j = j`, restoring faithfulness; see their
  docstrings for proof status and the affected Auto2 interface.
- DISCHARGES convention: theorems matching a `pack_concl` interface of
  PackingAuto2 are marked `DISCHARGES: PackingAuto2.<name>` in their
  docstrings (faithful statements here; the interfaces stay in Auto2).
- Parallel workers own Auto9 (EMNWUUS/NJIUTIU/TEZFFSK) and Auto11
  (LEPJBDJ); neither is imported. `HDTFNFZ` depends on `LEPJBDJ` and is
  therefore `sorry`ed (see docstring).
- Imports: `Kepler.Text.PackingAuto2` (mcell defs + pack_concl interfaces),
  `Kepler.Text.PackingAuto5` (truncation/left-action kit),
  `Kepler.Text.PackingAuto6`, `Kepler.Text.PackingAuto7`
  (`BARV_IMP_LENGTH_EQ_CARD`, Rogers), `Kepler.Text.PackingAuto8`
  (`BARV_3_EXPLICIT`, truncation explicits), `Kepler.Text.Polytope`,
  `Mathlib`.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto11
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ### Tail-fixed permutation kit (added with the ENCODING-FIX) -/

/-- Membership in a list via `getD` (used to see through `leftActionList`). -/
private theorem mem_iff_getD_p10 {α : Type*} [Inhabited α] {ul : List α} {x : α} :
    x ∈ ul ↔ ∃ k, k < ul.length ∧ ul.getD k default = x := by
  induction ul with
  | nil => simp
  | cons a tl ih =>
    constructor
    · intro hmem
      rcases List.mem_cons.1 hmem with hax | hm
      · have h0 : (a :: tl).getD 0 default = a := rfl
        exact ⟨0, by simp only [List.length_cons]; omega, h0.trans hax.symm⟩
      · obtain ⟨k, hk, hx⟩ := ih.1 hm
        refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
        simpa using hx
    · rintro ⟨k, hk, hx⟩
      cases k with
      | zero =>
        have hax : a = x := hx
        subst hax
        simp
      | succ k =>
        refine List.mem_cons_of_mem _ (ih.2 ⟨k, ?_, ?_⟩)
        · simpa using hk
        · simpa using hx

/-- A permutation weakly permuting `Icc 0 (i-1)` and fixing every `j ≥ i`
maps `m < i` into `[0, i)` and conversely (it bijects the initial block). -/
private theorem p_lt_i_iff_p10 {p : Equiv.Perm ℕ} {i : ℕ}
    (hperm : permutes p (Set.Icc 0 (i - 1))) (hfix : ∀ j, i ≤ j → p j = j)
    (m : ℕ) : m < i ↔ p m < i := by
  constructor
  · intro hm
    by_cases hge : i ≤ m
    · rw [hfix m hge]; exact hm
    · have hmem : m ∈ Set.Icc 0 (i - 1) := ⟨by omega, by omega⟩
      have hp := (hperm m).mp hmem
      simp only [Set.mem_Icc] at hp
      omega
  · intro hm
    by_cases hge : i ≤ m
    · rw [hfix m hge] at hm; omega
    · omega

/-- Same, for the inverse permutation. -/
private theorem psymm_lt_i_p10 {p : Equiv.Perm ℕ} {i : ℕ}
    (_hperm : permutes p (Set.Icc 0 (i - 1))) (hfix : ∀ j, i ≤ j → p j = j)
    {m : ℕ} (hm : m < i) : p.symm m < i := by
  by_contra hge
  have h1 : p (p.symm m) = p.symm m := hfix _ (by omega)
  rw [Equiv.apply_symm_apply] at h1
  omega

/-- Under the ENCODING-FIX hypotheses the left action only permutes the
entries of a length-`i` list, so the point set is unchanged. -/
private theorem setOfList_leftActionList_fix_p10 {p : Equiv.Perm ℕ} {ul : List V3}
    {i : ℕ} (hlen : ul.length = i)
    (hperm : permutes p (Set.Icc 0 (i - 1))) (hfix : ∀ j, i ≤ j → p j = j) :
    setOfList (leftActionList p ul) = setOfList ul := by
  have hpu : ∀ m, m < ul.length → p.symm m < ul.length := by
    intro m hm
    have h1 : m < i := by rw [← hlen]; exact hm
    have h2 : p.symm m < i := psymm_lt_i_p10 hperm hfix h1
    rw [← hlen] at h2
    exact h2
  have hpk : ∀ k, k < ul.length → p k < ul.length := by
    intro k hk
    have h1 : k < i := by rw [← hlen]; exact hk
    have h2 : p k < i := (p_lt_i_iff_p10 hperm hfix k).1 h1
    rw [← hlen] at h2
    exact h2
  ext x
  have e : leftActionList p ul
      = (List.range ul.length).map (fun j => ul.getD (p.symm j) default) := rfl
  simp only [setOfList, e, List.mem_map, List.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hx⟩
    exact mem_iff_getD_p10.2 ⟨p.symm j, hpu j hj, hx⟩
  · intro hmem
    obtain ⟨k, hk, hx⟩ := mem_iff_getD_p10.1 hmem
    refine ⟨p k, hpk k hk, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hx

/-- The identity permutation acts trivially. -/
private theorem leftActionList_refl_p10 {α : Type*} [Inhabited α] (ul : List α) :
    leftActionList (Equiv.refl ℕ) ul = ul := by
  apply List.ext_get
  · simp [leftActionList]
  · intro n _ h2
    simp [leftActionList, Equiv.refl_symm, h2]

/-- A typed permutation fixing `0` and every `j ≥ 1` is the identity. -/
private theorem eq_refl_of_fix_p10 {p : Equiv.Perm ℕ}
    (h0 : p 0 = 0) (hfix : ∀ j, 1 ≤ j → p j = j) : p = Equiv.refl ℕ :=
  Equiv.ext fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact h0
    · simpa using hfix j hj

/-! ### The `{0,1}`-swap invariance kit (ports the core of marchal2.hl:5848
`LEFT_ACTION_LIST_1_PROPERTIES` for the `i = 2` case of `RVFXZBU`)

Geometric heart: the omega tower points `ω₂, ω₃` of a `barV V 3` list lie in
`voronoiList V (truncateSimplex 1 ul)` (PA5 `OMEGA_LIST_N_IN_VORONOI_LIST`,
monotone in the truncation), and every point of the pair cell is equidistant
from the two pair points — so the `mxi` selection predicate (hull of
`{ω₂, ω₃}` at `√2` from the head) reads the same at `u0` and `u1`. -/

/-- `closestPoint` only sees the query point through distances on `K`. -/
private theorem closestPoint_congr_p10 {K : Set V3} {x x' : V3}
    (h : ∀ y ∈ K, dist x y = dist x' y) : closestPoint K x = closestPoint K x' := by
  show Classical.epsilon (fun y => y ∈ K ∧ ∀ z ∈ K, dist x y ≤ dist x z)
      = Classical.epsilon (fun y => y ∈ K ∧ ∀ z ∈ K, dist x' y ≤ dist x' z)
  congr 1
  funext y
  refine propext ⟨fun h1 => ⟨h1.1, ?_⟩, fun h1 => ⟨h1.1, ?_⟩⟩
  · intro z hz
    rw [← h z hz, ← h y h1.1]
    exact h1.2 z hz
  · intro z hz
    rw [h z hz, h y h1.1]
    exact h1.2 z hz

/-- Every point of the pair Voronoi cell is equidistant from the pair. -/
private theorem voronoiList2_dist_p10 {V : Set V3} {a b x : V3}
    (haV : a ∈ V) (hbV : b ∈ V) (hx : x ∈ voronoiList V [a, b]) :
    dist x a = dist x b := by
  have hmem : x ∈ ⋂₀ {voronoiClosed V v | v ∈ (setOfList [a, b] : Set V3)} := hx
  have ha : x ∈ voronoiClosed V a :=
    Set.mem_sInter.1 hmem _ ⟨a, by simp [setOfList], rfl⟩
  have hb : x ∈ voronoiClosed V b :=
    Set.mem_sInter.1 hmem _ ⟨b, by simp [setOfList], rfl⟩
  simp only [voronoiClosed, Set.mem_setOf_eq] at ha hb
  exact le_antisymm (ha b hbV) (hb a haV)

/-- `voronoiList` only sees the list through its point set. -/
private theorem voronoiList_setOfList_p10 {V : Set V3} {ul vl : List V3}
    (h : setOfList ul = setOfList vl) : voronoiList V ul = voronoiList V vl := by
  show voronoiSet V (setOfList ul) = voronoiSet V (setOfList vl)
  exact congrArg (voronoiSet V) h

/-- Swapping the first two entries does not change the point set. -/
private theorem setOfList_swap_head_p10 {a b : V3} {l : List V3} :
    setOfList (a :: b :: l) = setOfList (b :: a :: l) := by
  ext x
  simp only [setOfList, Set.mem_setOf_eq, List.mem_cons]
  tauto

/-- Enlarging the point set shrinks the cell. -/
private theorem voronoiList_mono_p10 {V : Set V3} {ul vl : List V3}
    (hsub : setOfList ul ⊆ setOfList vl) : voronoiList V vl ⊆ voronoiList V ul := by
  intro x hx
  have hmem : x ∈ ⋂₀ {voronoiClosed V v | v ∈ (setOfList vl : Set V3)} := hx
  refine Set.mem_sInter.2 fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := hw
  exact Set.mem_sInter.1 hmem (voronoiClosed V v) ⟨v, hsub hv, rfl⟩

/-- `omega_list_n V · 1` is invariant under swapping the first two entries:
the closest point of the pair cell is read through equidistance, so the
query head `u1` vs `u0` does not matter. -/
private theorem omegaListN1_swap_p10 (V : Set V3) (u0 u1 u2 u3 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) :
    omegaListN V [u1, u0, u2, u3] 1 = omegaListN V [u0, u1, u2, u3] 1 := by
  show closestPoint (voronoiList V (truncateSimplex 1 [u1, u0, u2, u3]))
      (hdV [u1, u0, u2, u3]) =
    closestPoint (voronoiList V (truncateSimplex 1 [u0, u1, u2, u3]))
      (hdV [u0, u1, u2, u3])
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u1 u0 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
      show hdV [u1, u0, u2, u3] = u1 from rfl,
      show hdV [u0, u1, u2, u3] = u0 from rfl,
      voronoiList_setOfList_p10 setOfList_swap_head_p10]
  refine closestPoint_congr_p10 fun y hy => ?_
  rw [dist_comm u1 y, dist_comm u0 y]
  exact (voronoiList2_dist_p10 hu0 hu1 hy).symm

/-- `omega_list_n V · 2` is invariant under the `{0,1}`-swap (same 3-point
cell, same query after the level-1 invariance). -/
private theorem omegaListN2_swap_p10 (V : Set V3) (u0 u1 u2 u3 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) :
    omegaListN V [u1, u0, u2, u3] 2 = omegaListN V [u0, u1, u2, u3] 2 := by
  show closestPoint (voronoiList V (truncateSimplex 2 [u1, u0, u2, u3]))
      (omegaListN V [u1, u0, u2, u3] 1) =
    closestPoint (voronoiList V (truncateSimplex 2 [u0, u1, u2, u3]))
      (omegaListN V [u0, u1, u2, u3] 1)
  rw [omegaListN1_swap_p10 V u0 u1 u2 u3 hu0 hu1,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 u1 u0 u2 u3).2,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2,
      voronoiList_setOfList_p10 setOfList_swap_head_p10]

/-- `omega_list_n V · 3` is invariant under the `{0,1}`-swap (same 4-point
cell, same query after the level-2 invariance). -/
private theorem omegaListN3_swap_p10 (V : Set V3) (u0 u1 u2 u3 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) :
    omegaListN V [u1, u0, u2, u3] 3 = omegaListN V [u0, u1, u2, u3] 3 := by
  show closestPoint (voronoiList V (truncateSimplex 3 [u1, u0, u2, u3]))
      (omegaListN V [u1, u0, u2, u3] 2) =
    closestPoint (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]))
      (omegaListN V [u0, u1, u2, u3] 2)
  rw [omegaListN2_swap_p10 V u0 u1 u2 u3 hu0 hu1,
      TRUNCATE_SIMPLEX_EXPLICIT_3 u1 u0 u2 u3,
      TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3,
      voronoiList_setOfList_p10 setOfList_swap_head_p10]

/-- `mxi` is invariant under the `{0,1}`-swap: the branch condition reads
`hl` of equal point sets, the true branch is the level-2 invariance, and in
the epsilon branch the selection predicate is the same function — the hull
of `{ω₂, ω₃}` sits in the pair cell, where `u0` and `u1` are equidistant.
(The geometric core of HL `LEFT_ACTION_LIST_1_PROPERTIES`,
marchal2.hl:5848, minus the `barV` persistence clause, which `RVFXZBU`
does not need.) -/
private theorem mxi_swap_p10 (V : Set V3) (u0 u1 u2 u3 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hbar : barV V 3 [u0, u1, u2, u3]) :
    mxi V [u1, u0, u2, u3] = mxi V [u0, u1, u2, u3] := by
  have hhl : hl (truncateSimplex 2 [u1, u0, u2, u3])
      = hl (truncateSimplex 2 [u0, u1, u2, u3]) := by
    show radV (setOfList (truncateSimplex 2 [u1, u0, u2, u3]))
        = radV (setOfList (truncateSimplex 2 [u0, u1, u2, u3]))
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u1 u0 u2 u3).2,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
    exact congrArg _ setOfList_swap_head_p10
  -- both omega points sit in the pair cell (equidistant from `u0` and `u1`)
  have hω2 : omegaListN V [u0, u1, u2, u3] 2 ∈ voronoiList V [u0, u1] := by
    have h := OMEGA_LIST_N_IN_VORONOI_LIST (V := V) (ul := [u0, u1, u2, u3]) (k := 3)
      (i := 2) hbar (by omega)
    have hsub : setOfList (truncateSimplex 1 [u0, u1, u2, u3])
        ⊆ setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
        (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
      simp [setOfList]
    have h2 := voronoiList_mono_p10 hsub h
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at h2
    exact h2
  have hω3 : omegaListN V [u0, u1, u2, u3] 3 ∈ voronoiList V [u0, u1] := by
    have h := OMEGA_LIST_N_IN_VORONOI_LIST (V := V) (ul := [u0, u1, u2, u3]) (k := 3)
      (i := 3) hbar (by omega)
    rw [TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3] at h
    have hsub : setOfList (truncateSimplex 1 [u0, u1, u2, u3])
        ⊆ setOfList [u0, u1, u2, u3] := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
      simp [setOfList]
    have h2 := voronoiList_mono_p10 hsub h
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at h2
    exact h2
  have heq : ∀ y ∈ voronoiList V [u0, u1], dist y u0 = dist y u1 :=
    fun y hy => voronoiList2_dist_p10 hu0 hu1 hy
  by_cases hcond : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3])
  · simp only [mxi]
    rw [if_pos (by rw [hhl]; exact hcond), if_pos hcond,
      omegaListN2_swap_p10 V u0 u1 u2 u3 hu0 hu1]
  · simp only [mxi]
    rw [if_neg (by rw [hhl]; exact hcond), if_neg hcond]
    refine congrArg Classical.epsilon ?_
    funext q
    have h2r : hdV [u1, u0, u2, u3] = u1 := rfl
    have h2l : hdV [u0, u1, u2, u3] = u0 := rfl
    have hull2 : ∀ q' ∈ convexHull ℝ {omegaListN V [u0, u1, u2, u3] 2,
        omegaListN V [u0, u1, u2, u3] 3}, q' ∈ voronoiList V [u0, u1] := fun q' hq' =>
      convexHull_min (Set.pair_subset_iff.mpr ⟨hω2, hω3⟩)
        (CONVEX_VORONOI_LIST V [u0, u1]) hq'
    rw [omegaListN2_swap_p10 V u0 u1 u2 u3 hu0 hu1,
      omegaListN3_swap_p10 V u0 u1 u2 u3 hu0 hu1, h2r, h2l]
    exact propext ⟨fun hq => ⟨hq.1, by rw [heq q (hull2 q hq.1)]; exact hq.2⟩,
      fun hq => ⟨hq.1, by rw [← heq q (hull2 q hq.1)]; exact hq.2⟩⟩

/-- `mcell 2` is invariant under swapping the first two entries: the
dispatch condition reads `hl` of equal point sets, the two mutual
`rconeGe` factors trade places, and the `affGe` wedge only sees the base
as a point set — with the `mxi`/`ω₃` invariances above. (HL `RVFXZBU.hl`
core case, via marchal2.hl:5848.) -/
private theorem mcell2_swap_p10 (V : Set V3) (u0 u1 u2 u3 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hbar : barV V 3 [u0, u1, u2, u3]) :
    mcell 2 V [u1, u0, u2, u3] = mcell 2 V [u0, u1, u2, u3] := by
  have eL : mcell 2 V [u1, u0, u2, u3] = mcell2 V [u1, u0, u2, u3] := by
    rw [mcell, if_neg (show (2:ℕ) ≠ 0 by decide), if_neg (show (2:ℕ) ≠ 1 by decide),
      if_pos rfl]
  have eR : mcell 2 V [u0, u1, u2, u3] = mcell2 V [u0, u1, u2, u3] := by
    rw [mcell, if_neg (show (2:ℕ) ≠ 0 by decide), if_neg (show (2:ℕ) ≠ 1 by decide),
      if_pos rfl]
  rw [eL, eR]
  simp only [mcell2]
  rw [show hdV [u1, u0, u2, u3].tail = u0 from rfl,
    show hdV [u0, u1, u2, u3].tail = u1 from rfl,
    show hdV [u1, u0, u2, u3] = u1 from rfl,
    show hdV [u0, u1, u2, u3] = u0 from rfl]
  have hhl1 : hl (truncateSimplex 1 [u1, u0, u2, u3])
      = hl (truncateSimplex 1 [u0, u1, u2, u3]) := by
    show radV (setOfList (truncateSimplex 1 [u1, u0, u2, u3]))
        = radV (setOfList (truncateSimplex 1 [u0, u1, u2, u3]))
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u1 u0 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
    exact congrArg _ setOfList_swap_head_p10
  have hhl0 : hl [u1, u0, u2, u3] = hl [u0, u1, u2, u3] := by
    show radV (setOfList [u1, u0, u2, u3]) = radV (setOfList [u0, u1, u2, u3])
    exact congrArg _ setOfList_swap_head_p10
  by_cases hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3]
  · have hcondL : hl (truncateSimplex 1 [u1, u0, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u1, u0, u2, u3] :=
      ⟨by rw [hhl1]; exact hcond.1, by rw [hhl0]; exact hcond.2⟩
    rw [if_pos hcondL, if_pos hcond, hhl1,
      mxi_swap_p10 V u0 u1 u2 u3 hu0 hu1 hbar,
      omegaListN3_swap_p10 V u0 u1 u2 u3 hu0 hu1,
      Set.inter_comm (rconeGe u1 u0 _) (rconeGe u0 u1 _),
      show ({u1, u0} : Set V3) = {u0, u1} from Set.pair_comm u1 u0]
  · rw [if_neg (fun hc => hcond ⟨by rw [← hhl1]; exact hc.1, by rw [← hhl0]; exact hc.2⟩),
      if_neg hcond]

/-! ## RVFXZBU (RVFXZBU.hl:32-195): cell invariance under the left action -/
/-! ## RVFXZBU (RVFXZBU.hl:32-195): cell invariance under the left action -/
/-! ## RVFXZBU (RVFXZBU.hl:32-195): cell invariance under the left action -/
/-! ## RVFXZBU (RVFXZBU.hl:32-195): cell invariance under the left action -/

/-- HOL `RVFXZBU_concl` (RVFXZBU.hl:32-36): permuting the first `i` points
of a `barV V 3` list by `p` leaves the cell `mcell i` unchanged.
DISCHARGES: PackingAuto2.RVFXZBU3_concl — but only modulo the tail-fixedness
side condition added below: the Auto2 interface (weak `permutes`, no `hfix`)
is false as stated and needs the same ENCODING-FIX (owned elsewhere).

-- ENCODING-FIX 2026-09-17: added tail-fixedness hypothesis per HOL source.
HOL-Light `permutes` (`Library/perms.ml`) is complement-fixing
(`p permutes s := ∀ x, x ∉ s → p x = x`), so `p permutes 0..(i-1)` for the
typed `Equiv.Perm ℕ` is exactly `∀ j ≥ i, p j = j`; with only the weak
pointwise `permutes` the statement is false (`p` a transposition of `2,3`
weakly permutes `Icc 0 1` yet changes `hl ul`, hence `mcell4`, on
`[u0;u1;u2;u3]`).

Proof status: cases `i = 0, 1` (`p` forced to `Equiv.refl`), `i = 2`
(CLOSED 2026-10-19 wave: the `{0,1}`-swap kit above ports the geometric
core of `LEFT_ACTION_LIST_1_PROPERTIES` (marchal2.hl:5848) — `mxi` reads
only the hull of `{ω₂, ω₃}` in the pair Voronoi cell where `u0`/`u1` are
equidistant, plus `omegaListN` 1/2/3 invariance by closest-point
congruence) and `i = 4` (`mcell4` depends only on `setOfList`/`hl`) are
proved; case `i = 3` remains `sorry`: it needs the ported
`LEFT_ACTION_LIST_PROPERTIES` (marchal2.hl:4460) — `ω₂` invariance under
the `S₃`-action (the closest point of the 3-point cell is read through the
circumaxis projection, a genuine geometry bite). -/
theorem RVFXZBU {V : Set V3} {ul : List V3} {i : ℕ} {p : Equiv.Perm ℕ}
    (hi : i ∈ ({0, 1, 2, 3, 4} : Set ℕ))
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hperm : permutes p (Set.Icc 0 (i - 1)))
    (hfix : ∀ j, i ≤ j → p j = j) :
    mcell i V (leftActionList p ul) = mcell i V ul := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · -- i = 0: hfix forces p = refl
    have hp : p = Equiv.refl ℕ :=
      eq_refl_of_fix_p10 (hfix 0 (Nat.zero_le 0))
        (fun j hj => hfix j (by omega))
    subst hp
    rw [leftActionList_refl_p10]
  · -- i = 1: hperm forces p 0 = 0, hfix the tail, so p = refl
    have h0 : p 0 = 0 := by
      have hin : (0:ℕ) ∈ Set.Icc 0 (1 - 1) := Set.mem_Icc.2 (by omega)
      have hp0 := (hperm 0).mp hin
      simp only [Set.mem_Icc] at hp0
      omega
    have hp : p = Equiv.refl ℕ := eq_refl_of_fix_p10 h0 hfix
    subst hp
    rw [leftActionList_refl_p10]
  · -- i = 2: CLOSED (2026-10-19 wave). p is the identity or the {0,1}-swap;
    -- in both cases mcell2 is invariant (mcell2_swap_p10 above, via the
    -- bisector-blind mxi kit porting marchal2.hl:5848).
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    have hVsub : (setOfList [u0, u1, u2, u3] : Set V3) ⊆ V := BARV_SUBSET V 3 _ hbar
    have hu0 : u0 ∈ V := hVsub (by simp [setOfList])
    have hu1 : u1 ∈ V := hVsub (by simp [setOfList])
    have hp0m : p 0 ∈ Set.Icc 0 (2 - 1) := (hperm 0).mp (by simp [Set.mem_Icc])
    have hp0' : p 0 = 0 ∨ p 0 = 1 := by
      simp only [Set.mem_Icc] at hp0m; omega
    rcases hp0' with h0 | h0
    · -- p fixes 0, so p 1 = 1 (injectivity on the block) and p = refl
      have hp1 : p 1 = 1 := by
        have hp1m : p 1 ∈ Set.Icc 0 (2 - 1) := (hperm 1).mp (by simp [Set.mem_Icc])
        simp only [Set.mem_Icc] at hp1m
        rcases Nat.eq_zero_or_pos (p 1) with hz | hp
        · exact absurd (Equiv.injective p (hz.trans h0.symm)) (by decide)
        · omega
      have hpr : p = Equiv.refl ℕ := eq_refl_of_fix_p10 h0 (fun j hj => by
        rcases Nat.lt_or_ge j 2 with hlt | hge
        · have hj1 : j = 1 := by omega
          rw [hj1]; exact hp1
        · exact hfix j hge)
      subst hpr
      rw [leftActionList_refl_p10]
    · -- p swaps 0 and 1: leftActionList p ul = [u1, u0, u2, u3]
      have hp1 : p 1 = 0 := by
        have hp1m : p 1 ∈ Set.Icc 0 (2 - 1) := (hperm 1).mp (by simp [Set.mem_Icc])
        simp only [Set.mem_Icc] at hp1m
        rcases Nat.eq_zero_or_pos (p 1) with hz | hp
        · exact hz
        · have h11 : p 1 = 1 := by omega
          exact absurd (Equiv.injective p (h11.trans h0.symm)) (by decide)
      have hs0 : p.symm 0 = 1 := by rw [← hp1]; exact Equiv.symm_apply_apply p 1
      have hs1 : p.symm 1 = 0 := by rw [← h0]; exact Equiv.symm_apply_apply p 0
      have hs2 : p.symm 2 = 2 := by
        rw [show p.symm 2 = p.symm (p 2) by rw [hfix 2 (le_refl 2)]]
        exact Equiv.symm_apply_apply p 2
      have hs3 : p.symm 3 = 3 := by
        rw [show p.symm 3 = p.symm (p 3) by rw [hfix 3 (by omega)]]
        exact Equiv.symm_apply_apply p 3
      have hxl : leftActionList p [u0, u1, u2, u3] = [u1, u0, u2, u3] := by
        show (List.range [u0, u1, u2, u3].length).map
          (fun i => [u0, u1, u2, u3].getD (p.symm i) default) = [u1, u0, u2, u3]
        rw [show [u0, u1, u2, u3].length = 4 from rfl,
          show List.range 4 = [0, 1, 2, 3] from rfl,
          List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil]
        simp [hs0, hs1, hs2, hs3]
      rw [hxl]
      exact mcell2_swap_p10 V u0 u1 u2 u3 hu0 hu1 hbar
  · -- i = 3: needs LEFT_ACTION_LIST_PROPERTIES (marchal2.hl:4460)
    sorry
    -- NEEDS: mcell3/mcell4 dispatch invariance under the S3-action
    -- (LEFT_ACTION_LIST_PROPERTIES, marchal2.hl:4460). Not ported.
  · -- i = 4: mcell4 depends only on setOfList and hl
    have h4 : ul.length = 3 + 1 := hbar.1
    have hlen : ul.length = 4 := by omega
    have hset := setOfList_leftActionList_fix_p10 hlen hperm hfix
    have hhl : hl (leftActionList p ul) = hl ul := by rw [hl, hl, hset]
    have hL : mcell 4 V (leftActionList p ul) = mcell4 V (leftActionList p ul) := by
      rw [mcell, if_neg (show (4:ℕ) ≠ 0 by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    have hR : mcell 4 V ul = mcell4 V ul := by
      rw [mcell, if_neg (show (4:ℕ) ≠ 0 by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    rw [hL, hR, mcell4, mcell4, hhl, hset]

/-! ## HDTFNFZ (HDTFNFZ.hl:32-111): vertices of a non-null cell -/

/-- HOL `HDTFNFZ_concl` (HDTFNFZ.hl:32-38): for a non-null cell,
`VX V X = V ∩ X`.
DISCHARGES: PackingAuto2.HDTFNFZ_concl.

FULLY PROVED (2026-09-30) by consuming the PackingAuto11 `LEPJBDJ` /
`LEPJBDJ_0` interfaces (audit-upgrade; the k = 2, 3 geometry bites
`k2Case`/`k3Subset` remain `sorry`ed upstream in Auto11). The HL proof
unfolds `VX` through `cell_params` and applies them at
`(if k ≤ 3 then k else 4, ul)`; here the epsilon selection
`cellParams V X = (m, wl)` is read through `Classical.epsilon_spec` (the
predicate is satisfiable at `(min k 4, ul)` via the `mcell` dispatch),
`¬nullSet X` gives `X ≠ ∅`, and `LEPJBDJ`/`LEPJBDJ_0` at `(m, wl)` identify
`V ∩ X` with the truncated list point set — exactly the `VX` body. -/
theorem HDTFNFZ {V : Set V3} {ul : List V3} {k : ℕ} {v : V3} {X : Set V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hX : X = mcell k V ul) (hnull : ¬nullSet X) :
    VX V X = V ∩ X := by
  classical
  -- the cell-parameters selection is satisfiable: (min k 4, ul) works
  have hwit : (min k 4 : ℕ) ≤ 4 ∧ barV V 3 ul ∧ X = mcell (min k 4) V ul := by
    refine ⟨by omega, hbar, ?_⟩
    rcases le_or_gt k 4 with hle | hgt
    · rw [min_eq_left hle]; exact hX
    · rw [min_eq_right (by omega : (4:ℕ) ≤ k), hX, mcell,
        if_neg (show k ≠ 0 by omega), if_neg (show k ≠ 1 by omega),
        if_neg (show k ≠ 2 by omega), if_neg (show k ≠ 3 by omega),
        mcell, if_neg (show (4:ℕ) ≠ 0 by omega), if_neg (show (4:ℕ) ≠ 1 by omega),
        if_neg (show (4:ℕ) ≠ 2 by omega), if_neg (show (4:ℕ) ≠ 3 by omega)]
  -- the selected parameters satisfy the same predicate
  set pp := cellParams V X with hpc
  have hsel : pp.1 ≤ 4 ∧ barV V 3 pp.2 ∧ X = mcell pp.1 V pp.2 :=
    Classical.epsilon_spec
      (p := fun p : ℕ × List V3 => p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2)
      ⟨(min k 4, ul), hwit⟩
  -- X is nonempty (positive volume)
  have hXne : X ≠ ∅ := by
    intro he
    exact hnull (by rw [nullSet, he]; exact MeasureTheory.measure_empty)
  -- dispatch on the selected level
  by_cases hm0 : pp.1 = 0
  · -- VX V X = ∅ and V ∩ X = ∅ (LEPJBDJ_0)
    have hvx : VX V X = ∅ := by
      rw [VX, if_neg hnull]
      show (if pp.1 = 0 then ∅ else setOfList (truncateSimplex (pp.1 - 1) pp.2)) = ∅
      rw [hm0]
      simp
    rw [hvx, hsel.2.2, hm0]
    exact (LEPJBDJ_0 V pp.2 hsat hpack hsel.2.1).symm
  · -- VX V X = setOfList (truncateSimplex (pp.1 - 1) pp.2) and V ∩ X via LEPJBDJ
    have hm1 : 1 ≤ pp.1 := by omega
    have hvx : VX V X = setOfList (truncateSimplex (pp.1 - 1) pp.2) := by
      rw [VX, if_neg hnull]
      show (if pp.1 = 0 then ∅ else setOfList (truncateSimplex (pp.1 - 1) pp.2))
        = setOfList (truncateSimplex (pp.1 - 1) pp.2)
      rw [if_neg hm0]
    have hmX' : X = mcell pp.1 V pp.2 := hsel.2.2
    have hne : mcell pp.1 V pp.2 ≠ ∅ := by
      rw [← hmX']; exact hXne
    rw [hvx, hmX']
    exact (LEPJBDJ V pp.2 pp.1 hsat hpack hsel.2.1 hm1 hsel.1 hne).symm

/-! ## YNHYJIT (YNHYJIT.hl:33-103): left-action invariance of omega points -/

/-- HOL `YNHYJIT_concl` (YNHYJIT.hl:33-40): when the level `i-1`
truncation is small and the whole simplex is large, the left action of a
permutation of `0..i-1` preserves `barV` and the omega points at levels
`i-1..3`.

-- ENCODING-FIX 2026-09-17: added tail-fixedness hypothesis per HOL source.
Same weak-`permutes` gap as `RVFXZBU`: the HL proof applies
`LEFT_ACTION_LIST_1_PROPERTIES`/`LEFT_ACTION_LIST_PROPERTIES`, whose
`p permutes 0..(i-1)` (complement-fixing `Library/perms.ml` semantics)
fixes every index `≥ i`; with only the pointwise-membership `permutes`
the conclusion fails, e.g. at `j = i-1` for permutations moving later
in-range indices. The faithful side condition is `∀ j ≥ i, p j = j`
(the earlier `≥ i-1` guess was off by one: the block `0..i-1` moves).

Proof status: case `i = 4` is discharged by contradiction
(`truncate_simplex 3 ul = ul` via `BARV_3_EXPLICIT` +
`TRUNCATE_SIMPLEX_EXPLICIT_3`, so `h1` contradicts `h2`); cases
`i = 2, 3` remain `sorry`: they need the ported
`LEFT_ACTION_LIST_1_PROPERTIES`/`LEFT_ACTION_LIST_PROPERTIES`
(marchal2.hl:5848/4460) — `barV` persistence of the swapped list and
`omegaListN` invariance under the `{0,1}`-swap resp. the `S₃`-action. -/
theorem YNHYJIT {V : Set V3} {ul vl : List V3} {i : ℕ} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hi : i ∈ ({2, 3, 4} : Set ℕ))
    (h1 : hl (truncateSimplex (i - 1) ul) < Real.sqrt 2)
    (h2 : Real.sqrt 2 ≤ hl ul)
    (hperm : permutes p (Set.Icc 0 (i - 1)))
    (hfix : ∀ j, i ≤ j → p j = j)
    (hvl : vl = leftActionList p ul) :
    barV V 3 vl ∧
      ∀ j : ℕ, i - 1 ≤ j → j ≤ 3 → omegaListN V vl j = omegaListN V ul j := by
  subst hvl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl
  · -- i = 2: needs LEFT_ACTION_LIST_1_PROPERTIES (marchal2.hl:5848)
    sorry
    -- NEEDS: barV persistence of the swapped list + omegaListN invariance
    -- under the {0, 1}-swap (LEFT_ACTION_LIST_1_PROPERTIES). Not ported.
  · -- i = 3: needs LEFT_ACTION_LIST_PROPERTIES (marchal2.hl:4460)
    sorry
    -- NEEDS: barV persistence + omegaListN invariance under the S3-action
    -- (LEFT_ACTION_LIST_PROPERTIES, marchal2.hl:4460). Not ported.
  · -- i = 4: hypotheses are contradictory
    exfalso
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    rw [TRUNCATE_SIMPLEX_EXPLICIT_3] at h1
    linarith

/-! ## URRPHBZ1 (URRPHBZ1.hl): geometry kit and measurability of cells -/

/-- HOL `proj_point` (vectors.hl): the orthogonal projection of `w` onto
the line spanned by `v`, `v % ((w dot v) / (v dot v))`. Private `_p10`
copy: the port has no `proj_point` yet (delete at merge). -/
private noncomputable def projPoint_p10 (v w : V3) : V3 :=
  ((w ⬝ᵥ v) / (v ⬝ᵥ v)) • v

/-- HOL `between` (define_between): `dist(a,x) + dist(x,b) = dist(a,b)`.
Private `_p10` copy: absent from the port (delete at merge). -/
private def betweenP10 (x a b : V3) : Prop := dist a x + dist x b = dist a b

/-- HOL `INTER_RCONE_GE_IMP_BETWEEN_PROJ_POINT` (URRPHBZ1.hl:24-66): a point
in two mutually opposite `rcone_ge`s projects (orthogonally) onto the closed
segment between the cone tips. -/
theorem INTER_RCONE_GE_IMP_BETWEEN_PROJ_POINT {a b p : V3} {r : ℝ}
    (hab : ¬(a = b)) (hr : 0 ≤ r)
    (h : p ∈ rconeGe a b r ∩ rconeGe b a r) :
    betweenP10 (projPoint_p10 (b - a) (p - a) + a) a b := by
  obtain ⟨h1, h2⟩ := h
  simp only [rconeGe, Set.mem_setOf_eq] at h1 h2
  have h1i : inner ℝ (p - a) (b - a) ≥ dist p a * dist b a * r := by
    rw [inner_eq_dot]; exact h1
  have h2i : inner ℝ (p - b) (a - b) ≥ dist p b * dist a b * r := by
    rw [inner_eq_dot]; exact h2
  set v : V3 := b - a with hv
  have hv0 : v ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  -- the projection parameter `t` is squeezed into `[0,1]`
  have hprod : 0 ≤ dist p a * dist b a * r :=
    mul_nonneg (mul_nonneg dist_nonneg dist_nonneg) hr
  have hpos : 0 ≤ inner ℝ (p - a) v := le_trans hprod h1i
  have h2' : inner ℝ (p - b) (a - b) = inner ℝ v v - inner ℝ (p - a) v := by
    have ea : (p - b : V3) = (p - a) - v := by rw [hv]; abel
    have eb : (a - b : V3) = -v := by rw [hv]; abel
    rw [ea, eb, inner_sub_left, inner_neg_right, inner_neg_right]
    ring
  have hle : inner ℝ (p - a) v ≤ inner ℝ v v := by
    have hprod2 : 0 ≤ dist p b * dist a b * r :=
      mul_nonneg (mul_nonneg dist_nonneg dist_nonneg) hr
    rw [h2'] at h2i
    linarith [le_trans hprod2 h2i]
  set t : ℝ := inner ℝ (p - a) v / inner ℝ v v with ht
  have hsq0 : 0 < inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq, sq_pos_iff]; exact norm_ne_zero_iff.mpr hv0
  have ht0 : 0 ≤ t := div_nonneg hpos hsq0.le
  have ht1 : t ≤ 1 := (div_le_one hsq0).2 hle
  have hproj : projPoint_p10 v (p - a) = t • v := by
    simp only [projPoint_p10, ← inner_eq_dot, ht]
  rw [hproj]
  have e1 : dist a (t • v + a) = t * ‖v‖ := by
    rw [dist_eq_norm]
    have hsub : a - (t • v + a) = -(t • v) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have e2 : dist (t • v + a) b = (1 - t) * ‖v‖ := by
    rw [dist_eq_norm]
    have hsub : (t • v + a) - b = -((1 - t) • v) := by
      rw [sub_smul, one_smul, hv]
      abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hab' : dist a b = ‖v‖ := by
    rw [dist_eq_norm, hv, norm_sub_rev]
  unfold betweenP10
  rw [e1, e2, hab']
  ring

private theorem inter_rcone_ge_le_aux_p10 {a b p s : V3} {r : ℝ}
    (hab : ¬(a = b)) (hs : s = midpoint ℝ a b) (hr : 0 < r)
    (hpa : ¬(p = a)) (hpb : ¬(p = b)) (hinv : 1 / 2 ≤ r ^ 2)
    (hmem : p ∈ rconeGe a b r ∩ rconeGe b a r) :
    dist s p ≤ dist s a := by
  obtain ⟨h1, h2⟩ := hmem
  simp only [rconeGe, Set.mem_setOf_eq] at h1 h2
  have h1i : inner ℝ (p - a) (b - a) ≥ dist p a * dist b a * r := by
    rw [inner_eq_dot]; exact h1
  have h2i : inner ℝ (p - b) (a - b) ≥ dist p b * dist a b * r := by
    rw [inner_eq_dot]; exact h2
  set v : V3 := b - a with hv
  have hv0 : v ≠ 0 := by
    rw [hv]; exact sub_ne_zero.mpr (Ne.symm hab)
  have hnvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hvvpos : 0 < v ⬝ᵥ v := by
    rw [← norm_sq_eq_dot]
    exact pow_pos hnvpos 2
  have hvvne : v ⬝ᵥ v ≠ 0 := ne_of_gt hvvpos
  set τ : ℝ := ((p - a) ⬝ᵥ v) / (v ⬝ᵥ v) with hτ
  have hpa_dot : (p - a) ⬝ᵥ v = τ * (v ⬝ᵥ v) := by
    rw [hτ]
    exact (div_mul_cancel₀ _ hvvne).symm
  have hpa_inner : inner ℝ (p - a) v = τ * ‖v‖ ^ 2 := by
    rw [inner_eq_dot, hpa_dot, norm_sq_eq_dot]
  set A : ℝ := τ * ‖v‖ with hAdef
  set B : ℝ := (1 - τ) * ‖v‖ with hBdef
  have hAB : A + B = ‖v‖ := by rw [hAdef, hBdef]; ring
  have h1v : inner ℝ (p - a) v ≥ ‖p - a‖ * ‖v‖ * r := by
    simpa only [dist_eq_norm] using h1i
  have hA_ge : ‖p - a‖ * r ≤ A := by
    have hmul : (‖p - a‖ * r) * ‖v‖ ≤ A * ‖v‖ := by
      have hleft : A * ‖v‖ = inner ℝ (p - a) v := by
        rw [hAdef, hpa_inner]; ring
      rw [hleft]
      nlinarith [h1v]
    exact le_of_mul_le_mul_right hmul hnvpos
  have hApos : 0 < A := by
    have hnormpa : 0 < ‖p - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpa)
    have hpos : 0 < ‖p - a‖ * r := mul_pos hnormpa hr
    linarith
  have h2v : inner ℝ (p - b) (a - b) ≥ ‖p - b‖ * ‖v‖ * r := by
    have h := h2i
    have habv : a - b = -v := by rw [hv]; abel
    have hdist : ‖a - b‖ = ‖v‖ := by rw [habv, norm_neg]
    rw [dist_eq_norm, dist_eq_norm, hdist] at h
    exact h
  have hpb_inner : inner ℝ (p - b) (a - b) = ‖v‖ ^ 2 - inner ℝ (p - a) v := by
    have habv : a - b = -v := by rw [hv]; abel
    have e1 : p - b = (p - a) - v := by rw [hv]; abel
    rw [e1, habv, inner_sub_left, inner_neg_right, inner_neg_right,
      real_inner_self_eq_norm_sq]
    ring
  have hB_ge : ‖p - b‖ * r ≤ B := by
    have hleft : B * ‖v‖ = inner ℝ (p - b) (a - b) := by
      rw [hBdef, hpb_inner, hpa_inner]
      ring
    have hmul : (‖p - b‖ * r) * ‖v‖ ≤ B * ‖v‖ := by
      rw [hleft]
      nlinarith [h2v]
    exact le_of_mul_le_mul_right hmul hnvpos
  have hBpos : 0 < B := by
    have hnormpb : 0 < ‖p - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpb)
    have hpos : 0 < ‖p - b‖ * r := mul_pos hnormpb hr
    linarith
  set hsq : ℝ := ‖p - a‖ ^ 2 - A ^ 2 with hsq_def
  have hA_le : A ≤ ‖p - a‖ := by
    have hinnerle := real_inner_le_norm (p - a) v
    have hAeq : A = inner ℝ (p - a) v / ‖v‖ := by
      rw [hAdef, hpa_inner]; field_simp
    rw [hAeq]
    calc inner ℝ (p - a) v / ‖v‖ ≤ (‖p - a‖ * ‖v‖) / ‖v‖ :=
          div_le_div_of_nonneg_right hinnerle hnvpos.le
      _ = ‖p - a‖ := by field_simp
  have hsq_nonneg : 0 ≤ hsq := by
    rw [hsq_def]
    have h2 := pow_le_pow_left₀ hApos.le hA_le 2
    linarith
  have hcone1 : r ^ 2 * (A ^ 2 + hsq) ≤ A ^ 2 := by
    have h1sq : (‖p - a‖ * r) ^ 2 ≤ A ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg (norm_nonneg _) hr.le),
        abs_of_nonneg hApos.le]
      exact hA_ge
    have hexp : (‖p - a‖ * r) ^ 2 = r ^ 2 * ‖p - a‖ ^ 2 := by ring
    rw [hexp] at h1sq
    have hsqn : ‖p - a‖ ^ 2 = A ^ 2 + hsq := by rw [hsq_def]; ring
    nlinarith
  have hpb_norm : ‖p - b‖ ^ 2 = B ^ 2 + hsq := by
    have e1 : p - b = (p - a) - v := by rw [hv]; abel
    rw [e1, norm_sub_sq_real, hpa_inner]
    rw [hBdef, hsq_def]
    ring
  have hcone2 : r ^ 2 * (B ^ 2 + hsq) ≤ B ^ 2 := by
    have h2sq : (‖p - b‖ * r) ^ 2 ≤ B ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg (norm_nonneg _) hr.le),
        abs_of_nonneg hBpos.le]
      exact hB_ge
    have hexp : (‖p - b‖ * r) ^ 2 = r ^ 2 * ‖p - b‖ ^ 2 := by ring
    rw [hexp, hpb_norm] at h2sq
    nlinarith
  have hsq_le_AB : hsq ≤ A * B := by
    rcases le_or_gt (r ^ 2) 1 with hr2 | hr2
    · have hr2pos : 0 < r ^ 2 := by positivity
      have hb1 : r ^ 2 * hsq ≤ (1 - r ^ 2) * A ^ 2 := by nlinarith [hcone1]
      have hb2 : r ^ 2 * hsq ≤ (1 - r ^ 2) * B ^ 2 := by nlinarith [hcone2]
      have hdiv1 : hsq ≤ ((1 - r ^ 2) / r ^ 2) * A ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr2pos]
        nlinarith [hb1]
      have hdiv2 : hsq ≤ ((1 - r ^ 2) / r ^ 2) * B ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr2pos]
        nlinarith [hb2]
      have hbeta_le : (1 - r ^ 2) / r ^ 2 ≤ 1 := by
        rw [div_le_one hr2pos]
        linarith
      have hsqA : hsq ≤ A ^ 2 := by
        calc hsq ≤ ((1 - r ^ 2) / r ^ 2) * A ^ 2 := hdiv1
          _ ≤ 1 * A ^ 2 := mul_le_mul_of_nonneg_right hbeta_le (sq_nonneg A)
          _ = A ^ 2 := one_mul _
      have hsqB : hsq ≤ B ^ 2 := by
        calc hsq ≤ ((1 - r ^ 2) / r ^ 2) * B ^ 2 := hdiv2
          _ ≤ 1 * B ^ 2 := mul_le_mul_of_nonneg_right hbeta_le (sq_nonneg B)
          _ = B ^ 2 := one_mul _
      rcases le_total A B with hle | hle
      · calc hsq ≤ A ^ 2 := hsqA
          _ = A * A := (sq A)
          _ ≤ A * B := mul_le_mul_of_nonneg_left hle hApos.le
      · calc hsq ≤ B ^ 2 := hsqB
          _ = B * B := (sq B)
          _ ≤ B * A := mul_le_mul_of_nonneg_left hle hBpos.le
          _ = A * B := mul_comm B A
    · exfalso
      have hA2pos : 0 < A ^ 2 := by positivity
      have hr2A : A ^ 2 < r ^ 2 * A ^ 2 := by nlinarith
      have hr2hsq : 0 ≤ r ^ 2 * hsq := mul_nonneg (by linarith) hsq_nonneg
      nlinarith [hcone1]
  have hsa : s - a = (1 / 2 : ℝ) • v := by
    rw [hs, hv]
    rw [midpoint_sub_left]
    norm_num
  have hps_sq : ‖p - s‖ ^ 2 = hsq + ((A - B) / 2) ^ 2 := by
    have e : p - s = (p - a) - (s - a) := by abel
    rw [e, norm_sub_sq_real, hsa, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), real_inner_smul_right]
    rw [hpa_inner, hsq_def, hAdef, hBdef]
    ring
  have hsa_sq : ‖a - s‖ ^ 2 = ((A + B) / 2) ^ 2 := by
    rw [norm_sub_rev, hsa, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    rw [← hAB]
    ring
  have hsq_dists : dist s p ^ 2 ≤ dist s a ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev s p, norm_sub_rev s a]
    rw [hps_sq, hsa_sq]
    nlinarith [hsq_le_AB]
  have h := sq_le_sq.mp hsq_dists
  rwa [abs_of_nonneg (dist_nonneg), abs_of_nonneg (dist_nonneg)] at h

/-- HOL `INTER_RCONE_GE_LE_lemma` (URRPHBZ1.hl:70-363): for a point in two
mutually opposite `rcone_ge`s with `inv 2 ≤ r^2`, if the perpendicular foot
lies between `a` and the midpoint `s`, then `p` is no further from `s` than
`a` (the key "edge cell is capped" estimate). The 300-line HL proof (rhombus
comparison via `SIMPLEX_FURTHEST_LE`) is out of budget here. -/
theorem INTER_RCONE_GE_LE_lemma {a b p s : V3} {r : ℝ}
    (hab : ¬(a = b)) (hs : s = midpoint ℝ a b) (hr : 0 < r)
    (hpa : ¬(p = a)) (hpb : ¬(p = b)) (hinv : 1 / 2 ≤ r ^ 2)
    (hbet : betweenP10 (projPoint_p10 (b - a) (p - a) + a) a s)
    (hmem : p ∈ rconeGe a b r ∩ rconeGe b a r) :
    dist s p ≤ dist s a := by
  exact inter_rcone_ge_le_aux_p10 hab hs hr hpa hpb hinv hmem

private theorem HL_2_p10 (u v : V3) : hl [u, v] = dist u v / 2 := by
  have hset : setOfList [u, v] = ({u, v} : Set V3) := by
    ext x
    simp [setOfList]
  have hcc : circumcenter ({u, v} : Set V3) = midpoint ℝ u v := CIRCUMCENTER_2 u v
  have hexi : ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w := by
    refine ⟨dist (midpoint ℝ u v) u, ?_⟩
    rw [hcc]
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw'
    · rfl
    · rcases Set.mem_singleton_iff.mp hw' with rfl
      simp
  have key : radV ({u, v} : Set V3) = dist (circumcenter ({u, v} : Set V3)) u :=
    (Classical.epsilon_spec (p := fun c : ℝ => ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w) hexi) u (Set.mem_insert u {v})
  have hhl : hl [u, v] = dist (circumcenter ({u, v} : Set V3)) u := by
    show radV (setOfList [u, v]) = _
    rw [hset, key]
  rw [hhl, hcc]
  simp
  ring

/-- HOL `MCELL_2_PROPERTIES_lemma1` (URRPHBZ1.hl:366-589): every point of the
edge cell `mcell2` is within `hl (truncate_simplex 1 ul)` of the midpoint of
the first edge (drives the `BOUNDED_MCELL` case `k = 2`). -/
theorem MCELL_2_PROPERTIES_lemma1 {V : Set V3} {ul : List V3} {p : V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hp : p ∈ mcell2 V ul) :
    dist (midpoint ℝ (hdV ul) (hdV ul.tail)) p ≤ hl (truncateSimplex 1 ul) := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
  subst hul
  have hT : truncateSimplex 1 [u0, u1, u2, u3] = [u0, u1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2
  have hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra hc
    rw [mcell2, if_neg hc] at hp
    exact hp
  have hmem := hp
  rw [mcell2, if_pos hcond] at hmem
  dsimp only at hmem
  obtain ⟨hcones, hwedge⟩ := hmem
  rw [hT] at hcones
  change dist (midpoint ℝ u0 u1) p ≤ hl (truncateSimplex 1 [u0, u1, u2, u3])
  rw [hT]
  -- distinctness of u0 and u1
  have hb1 : barV V 1 [u0, u1] := by
    have h := TRUNCATE_SIMPLEX_BARV V 1 3 [u0, u1, u2, u3] hbar (by omega)
    rwa [hT] at h
  have hcard1 := BARV_IMP_LENGTH_EQ_CARD V [u0, u1] 1 hpack hb1
  have hab : ¬(u0 = u1) := by
    intro he
    subst he
    have hc : Nat.card (setOfList [u0, u0]) = 1 := by simp [setOfList]
    omega
  have hhl : hl [u0, u1] = dist u0 u1 / 2 := HL_2_p10 u0 u1
  by_cases hp0 : p = u0
  · rw [hp0, hhl, dist_midpoint_left]
    have h2 : ‖(2:ℝ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  by_cases hp1 : p = u1
  · rw [hp1, hhl, dist_midpoint_right]
    have h2 : ‖(2:ℝ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  have hsub : setOfList [u0, u1] ⊆ V := BARV_SUBSET V 1 [u0, u1] hb1
  have hu0V : u0 ∈ V := hsub (by simp [setOfList])
  have hu1V : u1 ∈ V := hsub (by simp [setOfList])
  have hle2 : 2 ≤ dist u0 u1 := Packing.dist_ge_two hpack hu0V hu1V hab
  have hhl1 : 1 ≤ hl [u0, u1] := by rw [hhl]; linarith
  have hdistpos : 0 < dist u0 u1 := dist_pos.mpr hab
  have hr : 0 < hl [u0, u1] / Real.sqrt 2 := by
    have hpos : 0 < hl [u0, u1] := by rw [hhl]; linarith
    exact div_pos hpos (Real.sqrt_pos.mpr (by norm_num))
  have hinv : 1 / 2 ≤ (hl [u0, u1] / Real.sqrt 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : (1:ℝ) ≤ hl [u0, u1] ^ 2 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hhl1 2
    linarith
  have hres := inter_rcone_ge_le_aux_p10 (a := u0) (b := u1) (p := p)
    (s := midpoint ℝ u0 u1) (r := hl [u0, u1] / Real.sqrt 2)
    hab rfl hr hp0 hp1 hinv hcones
  have hsu0 : dist (midpoint ℝ u0 u1) u0 = hl [u0, u1] := by
    rw [hhl, dist_midpoint_left]
    have h2 : ‖(2:ℝ)‖ = 2 := by norm_num
    rw [h2]
    ring
  rwa [hsu0] at hres

/-! ### The Rogers simplex: finiteness, boundedness, measurability -/

/-- The omega-point image defining `rogers` is finite. -/
private theorem finite_omega_image_p10 (V : Set V3) (ul : List V3) :
    (omegaListN V ul '' {j : ℕ | j < ul.length}).Finite :=
  Set.Finite.image _ (Set.finite_Iio ul.length)

private theorem rogers_isCompact_p10 (V : Set V3) (ul : List V3) :
    IsCompact (rogers V ul) :=
  Set.Finite.isCompact_convexHull (𝕜 := ℝ) (hs := finite_omega_image_p10 V ul)

private theorem rogers_isBounded_p10 (V : Set V3) (ul : List V3) :
    Bornology.IsBounded (rogers V ul) :=
  (rogers_isCompact_p10 V ul).isBounded

private theorem rogers_measurableSet_p10 (V : Set V3) (ul : List V3) :
    MeasurableSet (rogers V ul) :=
  (rogers_isCompact_p10 V ul).measurableSet

private theorem finite_setOfList_p10 (ul : List V3) : (setOfList ul).Finite := by
  classical
  exact Set.Finite.ofFinset ul.toFinset (fun x => by simp [setOfList])

/-- HOL `BOUNDED_MCELL` (URRPHBZ1.hl:593-669): every Marchal cell is bounded.
Cases `k = 0,1` are subsets of the Rogers simplex (finite hull); `k = 3,4`
are finite hulls or empty; `k = 2` is the ball estimate around the edge
midpoint via `MCELL_2_PROPERTIES_lemma1` (still `sorry`ed above). -/
theorem BOUNDED_MCELL (V : Set V3) (ul : List V3) (k : ℕ)
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul) :
    Bornology.IsBounded (mcell k V ul) := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k
    · -- k = 0: rogers \ ball
      show Bornology.IsBounded (mcell0 V ul)
      rw [mcell0]
      exact Bornology.IsBounded.subset (rogers_isBounded_p10 V ul) (fun x hx => hx.1)
    · -- k = 1: subset of rogers
      show Bornology.IsBounded (mcell1 V ul)
      by_cases hcond : Real.sqrt 2 ≤ hl ul
      · rw [mcell1, if_pos hcond]
        exact Bornology.IsBounded.subset (rogers_isBounded_p10 V ul)
          (fun x hx => hx.1.1)
      · rw [mcell1, if_neg hcond]
        exact Bornology.isBounded_empty
    · -- k = 2: ball estimate via MCELL_2_PROPERTIES_lemma1
      show Bornology.IsBounded (mcell2 V ul)
      by_cases hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
      · rw [mcell2, if_pos hcond]
        refine Bornology.IsBounded.subset
          (Metric.isBounded_ball (x := midpoint ℝ (hdV ul) (hdV ul.tail))
            (r := hl (truncateSimplex 1 ul) + 1)) ?_
        intro x hx
        have hx2 : x ∈ mcell2 V ul := by rw [mcell2, if_pos hcond]; exact hx
        rw [Metric.mem_ball, dist_comm x]
        exact lt_add_of_le_of_pos
          (MCELL_2_PROPERTIES_lemma1 hsat hpack hbar hx2) one_pos
      · rw [mcell2, if_neg (by tauto)]
        exact Bornology.isBounded_empty
    · -- k = 3: finite hull or empty
      show Bornology.IsBounded (mcell3 V ul)
      by_cases hcond : hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
      · rw [mcell3, if_pos hcond]
        exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ)
          (hs := (finite_setOfList_p10 (truncateSimplex 2 ul)).union
            (Set.finite_singleton (mxi V ul)))).isBounded
      · rw [mcell3, if_neg (by tauto)]
        exact Bornology.isBounded_empty
  · -- k ≥ 4: mcell4, finite hull or empty
    have h4 : mcell k V ul = mcell4 V ul := by
      rw [mcell, if_neg (show k ≠ 0 by omega), if_neg (show k ≠ 1 by omega),
        if_neg (show k ≠ 2 by omega), if_neg (show k ≠ 3 by omega)]
    rw [h4, mcell4]
    split_ifs with hc
    · exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ)
          (hs := finite_setOfList_p10 ul)).isBounded
    · exact Bornology.isBounded_empty

/-! ### Measurability (HL `MEASURABLE_MCELL`, URRPHBZ1.hl:673-682) -/

private theorem continuous_dot_p10 (v w : V3) :
    Continuous fun x : V3 => (x - v) ⬝ᵥ (w - v) := by
  have h : Continuous fun x : V3 => inner ℝ (x - v) (w - v) :=
    (continuous_id.sub continuous_const).inner continuous_const
  have heq : (fun x : V3 => inner ℝ (x - v) (w - v)) =
      fun x : V3 => (x - v) ⬝ᵥ (w - v) := by
    funext x
    exact inner_eq_dot (x - v) (w - v)
  rw [← heq]
  exact h

private theorem continuous_rcone_p10 (v w : V3) (a : ℝ) :
    Continuous fun x : V3 => (x - v) ⬝ᵥ (w - v) - (dist x v * dist w v * a) :=
  (continuous_dot_p10 v w).sub (by fun_prop)

/-- `rconeGe v w a` is a closed halfspace-like region, hence measurable. -/
private theorem measurableSet_rconeGe_p10 (v w : V3) (a : ℝ) :
    MeasurableSet (rconeGe v w a) := by
  have hset : rconeGe v w a =
      (fun x : V3 => (x - v) ⬝ᵥ (w - v) - (dist x v * dist w v * a)) ⁻¹' (Set.Ici 0) := by
    ext x
    simp only [rconeGe, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, sub_nonneg]
  rw [hset]
  exact ((isClosed_Ici).preimage (continuous_rcone_p10 v w a)).measurableSet

/-- `rconeGt v w a` is an open region, hence measurable. -/
private theorem measurableSet_rconeGt_p10 (v w : V3) (a : ℝ) :
    MeasurableSet (rconeGt v w a) := by
  have hset : rconeGt v w a =
      (fun x : V3 => (x - v) ⬝ᵥ (w - v) - (dist x v * dist w v * a)) ⁻¹' (Set.Ioi 0) := by
    ext x
    simp only [rconeGt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, sub_pos]
  rw [hset]
  exact ((isOpen_Ioi).preimage (continuous_rcone_p10 v w a)).measurableSet

private lemma sum_subtype_finset_p10 {M : Type*} [AddCommMonoid M]
    (S : Finset V3) (F : V3 → M) :
    (∑ w : S, F w) = ∑ w ∈ S, F w := by
  rw [Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_attach S F

private lemma sum_ite_subtype_p10 {M : Type*} [AddCommMonoid M]
    (S : Finset V3) (g : S → M) :
    (∑ z ∈ S, (if hz : z ∈ S then g ⟨z, hz⟩ else 0)) = ∑ w : S, g w := by
  rw [← Finset.sum_attach (s := S)
    (f := fun z => if hz : z ∈ S then g ⟨z, hz⟩ else 0)]
  rw [Finset.sum_coe_sort_eq_attach (s := S) (f := g)]
  apply Finset.sum_congr rfl
  intro z _
  simp only [dif_pos z.property]

private lemma affGe_finset_coeff_p10 {s t : Set V3} (S : Finset V3)
    (hS : (S : Set V3) = s ∪ t) :
    affGe s t = {v : V3 | ∃ g : S → ℝ,
      (∀ w : S, (w : V3) ∈ t → 0 ≤ g w) ∧
      (∑ w, g w = 1) ∧
      v = ∑ w, g w • (w : V3)} := by
  ext v
  constructor
  · rintro ⟨f, h, hveq, hpos, hsum⟩
    have hEqS : h.toFinset = S := by
      ext x
      rw [Set.Finite.mem_toFinset, ← hS, Finset.mem_coe]
    refine ⟨fun w => f w, ?_, ?_, ?_⟩
    · intro w hwt
      exact hpos w hwt
    · calc (∑ w : S, f (w : V3)) = ∑ w ∈ S, f w := sum_subtype_finset_p10 S f
        _ = ∑ w ∈ h.toFinset, f w := by rw [hEqS]
        _ = 1 := hsum
    · calc v = ∑ w ∈ h.toFinset, f w • w := hveq
        _ = ∑ w ∈ S, f w • w := by rw [hEqS]
        _ = ∑ w : S, f w • (w : V3) :=
            (sum_subtype_finset_p10 S (fun w => f w • w)).symm
  · rintro ⟨g, hgpos, hgsum, rfl⟩
    have hfin : (s ∪ t).Finite := by
      rw [← hS]; exact S.finite_toSet
    have hEqS : hfin.toFinset = S := by
      ext x
      rw [Set.Finite.mem_toFinset, ← hS, Finset.mem_coe]
    refine ⟨fun z => if hz : z ∈ S then g ⟨z, hz⟩ else 0, hfin, ?_, ?_, ?_⟩
    · have h0 : (∑ z ∈ S, (if hz : z ∈ S then g ⟨z, hz⟩ else 0) • z)
          = ∑ w : S, g w • (w : V3) := by
        rw [← sum_ite_subtype_p10 S (fun w => g w • (w : V3))]
        apply Finset.sum_congr rfl
        intro z hz
        simp only [dif_pos hz]
      rw [hEqS]
      exact h0.symm
    · intro z hzt
      have hzS : z ∈ S := by
        rw [← Finset.mem_coe, hS]
        exact Set.mem_union_right s hzt
      simp only [dif_pos hzS]
      exact hgpos ⟨z, hzS⟩ hzt
    · calc (∑ z ∈ hfin.toFinset, (if hz : z ∈ S then g ⟨z, hz⟩ else 0))
          = ∑ z ∈ S, (if hz : z ∈ S then g ⟨z, hz⟩ else 0) := by rw [hEqS]
        _ = ∑ w : S, g w := sum_ite_subtype_p10 S g
        _ = 1 := hgsum

private theorem measurableSet_affGe_finite_p10 {s t : Set V3}
    (hs : s.Finite) (ht : t.Finite) : MeasurableSet (affGe s t) := by
  classical
  let S : Finset V3 := (hs.union ht).toFinset
  have hS : (S : Set V3) = s ∪ t := by
    ext x
    simp [S]
  let K : ℕ → Set (S → ℝ) := fun n => {g | (∀ w : S, (w : V3) ∈ t → 0 ≤ g w) ∧
      (∑ w, g w = 1) ∧ (∀ w : S, |g w| ≤ (n : ℝ))}
  let φ : (S → ℝ) → V3 := fun g => ∑ w : S, g w • (w : V3)
  have hφcont : Continuous φ := by
    rw [show φ = fun g : S → ℝ => ∑ w : S, g w • (w : V3) from rfl]
    exact continuous_finsetSum _ (fun w _ => (continuous_apply w).smul continuous_const)
  have hEq : affGe s t = ⋃ n : ℕ, φ '' K n := by
    rw [affGe_finset_coeff_p10 S hS]
    ext v
    constructor
    · rintro ⟨g, hgpos, hgsum, rfl⟩
      let n : ℕ := Finset.univ.sup (fun w : S => ⌈|g w|⌉₊)
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      have hbound : ∀ w : S, |g w| ≤ (n : ℝ) := by
        intro w
        calc |g w| ≤ (⌈|g w|⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by
              exact_mod_cast Finset.le_sup (s := (Finset.univ : Finset S))
                (f := fun w : S => ⌈|g w|⌉₊) (Finset.mem_univ w)
      exact Set.mem_image_of_mem φ ⟨hgpos, hgsum, hbound⟩
    · intro hv
      obtain ⟨n, hv⟩ := Set.mem_iUnion.mp hv
      obtain ⟨g, hgK, hφg⟩ := hv
      rw [← hφg]
      exact ⟨g, hgK.1, hgK.2.1, rfl⟩
  rw [hEq]
  apply MeasurableSet.iUnion
  intro n
  have hclosed1 : IsClosed {g : S → ℝ | ∀ w : S, (w : V3) ∈ t → 0 ≤ g w} := by
    have hset : {g : S → ℝ | ∀ w : S, (w : V3) ∈ t → 0 ≤ g w}
        = ⋂ w : S, ⋂ (_ : (w : V3) ∈ t), {g : S → ℝ | 0 ≤ g w} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter (fun w => isClosed_iInter (fun _ =>
      isClosed_Ici.preimage (continuous_apply w)))
  have hclosed2 : IsClosed {g : S → ℝ | (∑ w, g w) = 1} := by
    have hcont : Continuous (fun g : S → ℝ => ∑ w, g w) :=
      continuous_finsetSum _ (fun w _ => continuous_apply w)
    have hset : {g : S → ℝ | (∑ w, g w) = 1}
        = (fun g : S → ℝ => ∑ w, g w) ⁻¹' ({1} : Set ℝ) := rfl
    rw [hset]
    exact isClosed_singleton.preimage hcont
  have hclosed3 : IsClosed {g : S → ℝ | ∀ w : S, |g w| ≤ (n : ℝ)} := by
    have hset : {g : S → ℝ | ∀ w : S, |g w| ≤ (n : ℝ)}
        = ⋂ w : S, {g : S → ℝ | |g w| ≤ (n : ℝ)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter (fun w =>
      isClosed_Iic.preimage ((continuous_apply w).abs))
  have hKclosed : IsClosed (K n) := by
    show IsClosed {g : S → ℝ | (∀ w : S, (w : V3) ∈ t → 0 ≤ g w) ∧
      (∑ w, g w = 1) ∧ (∀ w : S, |g w| ≤ (n : ℝ))}
    exact hclosed1.inter (hclosed2.inter hclosed3)
  have hKbounded : Bornology.IsBounded (K n) := by
    show Bornology.IsBounded {g : S → ℝ | (∀ w : S, (w : V3) ∈ t → 0 ≤ g w) ∧
      (∑ w, g w = 1) ∧ (∀ w : S, |g w| ≤ (n : ℝ))}
    rw [Metric.isBounded_iff_subset_closedBall (0 : S → ℝ)]
    refine ⟨(n : ℝ), ?_⟩
    intro g hg
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg n)]
    intro w
    simpa [Real.norm_eq_abs] using hg.2.2 w
  haveI : ProperSpace (S → ℝ) := FiniteDimensional.proper ℝ _
  have hKcompact : IsCompact (K n) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbounded⟩
  exact (hKcompact.image hφcont).measurableSet

/-- Measurability of the `mcell2` wedge `aff_ge {u0, u1} {p, q}`.
NEEDS: an explicit wedge/bisector representation of `affGe` — the port's
closedness lemmas (`TopologyFan.closed_aff_ge_2_1`) require `¬Collinear3`
and cover only 2-1/1-2 shapes, and the `Affsign`-existence definition is
not directly measurable. Filled in when a general `affGe` Borel lemma
lands (Auto9/Auto11 merge). -/
private theorem measurableSet_affGe_wedge_p10 (u0 u1 p q : V3) :
    MeasurableSet (affGe {u0, u1} {p, q}) := by
  exact measurableSet_affGe_finite_p10 (by simp) (by simp)

/-- HOL `MEASURABLE_MCELL` (URRPHBZ1.hl:673-682): every Marchal cell is
measurable. HL reaches this via `MEASURABLE_COMPACT` (`CLOSED_MCELL` +
`BOUNDED_MCELL`); here each cell is instead decomposed directly into
Borel pieces of its `if-then-else` definition (balls, cones, finite
hulls, and the `mcell2` wedge above), so the `¬Collinear3`-gated
closedness lemmas are not needed. -/
theorem MEASURABLE_MCELL (V : Set V3) (ul : List V3) (k : ℕ)
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul) :
    MeasurableSet (mcell k V ul) := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k
    · -- k = 0: rogers \ ball
      show MeasurableSet (mcell0 V ul)
      rw [mcell0]
      exact (rogers_measurableSet_p10 V ul).diff
        (Metric.isOpen_ball).measurableSet
    · -- k = 1: (rogers ∩ closedBall) \ rconeGt or empty
      show MeasurableSet (mcell1 V ul)
      by_cases hcond : Real.sqrt 2 ≤ hl ul
      · rw [mcell1, if_pos hcond]
        exact ((rogers_measurableSet_p10 V ul).inter
          (Metric.isClosed_closedBall).measurableSet).diff
          (measurableSet_rconeGt_p10 (hdV ul) (hdV ul.tail)
            (hl (truncateSimplex 1 ul) / Real.sqrt 2))
      · rw [mcell1, if_neg hcond]
        exact MeasurableSet.empty
    · -- k = 2: cones ∩ wedge, or empty
      show MeasurableSet (mcell2 V ul)
      by_cases hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
      · rw [mcell2, if_pos hcond]
        exact ((measurableSet_rconeGe_p10 (hdV ul) (hdV ul.tail)
              (hl (truncateSimplex 1 ul) / Real.sqrt 2)).inter
            (measurableSet_rconeGe_p10 (hdV ul.tail) (hdV ul)
              (hl (truncateSimplex 1 ul) / Real.sqrt 2))).inter
          (measurableSet_affGe_wedge_p10 (hdV ul) (hdV ul.tail) (mxi V ul)
            (omegaListN V ul 3))
      · rw [mcell2, if_neg (by tauto)]
        exact MeasurableSet.empty
    · -- k = 3: finite hull or empty
      show MeasurableSet (mcell3 V ul)
      by_cases hcond : hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
      · rw [mcell3, if_pos hcond]
        exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ)
          (hs := (finite_setOfList_p10 (truncateSimplex 2 ul)).union
            (Set.finite_singleton (mxi V ul)))).measurableSet
      · rw [mcell3, if_neg (by tauto)]
        exact MeasurableSet.empty
  · -- k ≥ 4: mcell4, finite hull or empty
    have h4 : mcell k V ul = mcell4 V ul := by
      rw [mcell, if_neg (show k ≠ 0 by omega), if_neg (show k ≠ 1 by omega),
        if_neg (show k ≠ 2 by omega), if_neg (show k ≠ 3 by omega)]
    rw [h4, mcell4]
    split_ifs with hc
    · exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ)
          (hs := finite_setOfList_p10 ul)).measurableSet
    · exact MeasurableSet.empty

/-- HOL `URRPHBZ1` (URRPHBZ1.hl:686; `pack_concl.hl:172-174`): the Marchal
cells are measurable. In HL this is literally
`REWRITE_TAC[MEASURABLE_MCELL]`.
DISCHARGES: PackingAuto2.URRPHBZ1_concl. -/
theorem URRPHBZ1 (V : Set V3) (ul : List V3) (k : ℕ) (hsat : saturated V)
    (hpack : Packing V) (hbar : barV V 3 ul) : MeasurableSet (mcell k V ul) :=
  MEASURABLE_MCELL V ul k hsat hpack hbar


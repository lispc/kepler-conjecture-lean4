/-
Packing chapter, Rogers-cell geometry over omega chains (S14 stage): the
`QZKSYKG` lane.

HOL source: `scripts/packing/QZKSYKG.hl` (2255 lines, 7 theorems; VU KHAC KY,
book lemma `QZKSYKG`, chapter Packing). It supplies the auxiliary kit
`CONVEX_HULL_4_IMP_3_1`, `BARV_2_EXPLICIT`, `ROGERS_EXPLICIT_2`,
`TWO_REARRANGEMENT_LEMMA`, `SET_SUBSET_AFFINE_HULL` and the two capstones
`QZKSYKG1`/`QZKSYKG2`: a left action of a permutation of `0..k-1`
(`k ∈ {0,1,2,3,4}`) on a `barV V 3` list keeps it `barV` (whenever the cell
`mcell k V ul` is nonempty), and `mcell k V ul` is covered by the union of
the Rogers simplices of all the permuted lists. The results feed
marchal3/KIZHLTL downstream; `QZKSYKG` has no `pack_concl` interface, so
nothing here is marked DISCHARGES.

Encoding notes.
- HOL `real^3` ↔ `V3` (Kepler.Geom); `convex hull` ↔ `convexHull ℝ`;
  `HD ul` ↔ `hdV ul`; `omega_list_n` ↔ `omegaListN`; `truncate_simplex` ↔
  `truncateSimplex`; `left_action_list` ↔ `leftActionList`; `rogers`, `mcell`,
  `mxi`, `hl`, `barV`, `set_of_list` are the PackingAuto2 definitions.
- HOL `0..(k-1)` ↔ `Set.Icc 0 (k-1)`; `k IN {0,1,2,3,4}` ↔ the explicit
  `Set ℕ` literal; HOL `~(mcell k V ul = {})` ↔ `mcell k V ul ≠ ∅`.
- `permutes` is the weak pointwise-membership encoding
  `PackingAuto2.permutes` (`∀ x, x ∈ s ↔ p x ∈ s`), not the
  complement-fixing HL relation. This matters for `QZKSYKG1`: the HL proof
  at `k = 2, 3` goes through `YNHYJIT`, whose HL proof uses
  `LEFT_ACTION_LIST_PROPERTIES` (permutations fixing indices `≥ i-1`). The
  pointwise-membership `permutes` encoding alone is too weak (PA10 ruling:
  HL `permutes` is complement-fixing, so the faithful encoding carries the
  tail-fixedness side condition `∀ j, i ≤ j → p j = j`).
  ENCODING-FIX 2026-09-19: private `ynhyjit_p14` now carries `hfix`,
  matching the PA10 fix; `QZKSYKG1`/`QZKSYKG2` keep the plain `permutes`
  form (verbatim to HOL concl) — at discharge time their HL proofs must
  supply the tail-fixedness from `LEFT_ACTION_LIST_PROPERTIES`.
- `MXI_EXPLICIT` (marchal2.hl:2516): MERGED 2026-09-19 — PA12's proved
  public `MXI_EXPLICIT` is importable; the unused private `mxiExplicit_p14`
  copy was deleted (PA11 still holds its own private copy, out of scope).
- Proof status (2026-09-30 wave): the five supporting lemmas are proved;
  `ynhyjit_p14` is closed for i = 2 (the LEFT_ACTION bridge, via the
  private 01-swap kit below) and i = 4 (contradiction); i = 3 remains
  `sorry`ed (the `LEFT_ACTION_LIST_PROPERTIES` S₃ giant). The two public
  named bridges `LEFT_ACTION_LIST_1_PROPERTIES_ALT` and
  `MCELL2_PERMUTE_01` are proved (sorry-free; the LEFT_ACTION copy carries
  the PA10-style tail-fixedness side condition, see its ENCODING-FIX note).
  `QZKSYKG1`/`QZKSYKG2` remain `sorry`ed with NEEDS accounting (statement
  unprovable as weak-`permutes` encoded for k ≤ 3; k = 4 is the YIFVQDV_1
  giant; ~1900 HOL lines for QZKSYKG2).
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto12
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Supporting lemmas (QZKSYKG.hl:26-240) -/

/-- HOL `SET_SUBSET_AFFINE_HULL` (QZKSYKG.hl:234-240): a set sits inside its
affine hull. -/
private theorem setSubsetAffineHull (S : Set V3) : S ⊆ affineSpan ℝ S :=
  subset_affineSpan ℝ S

/-- HOL `BARV_2_EXPLICIT` (QZKSYKG.hl:78-98): a `barV V 2` list has exactly
three entries. -/
private theorem barV2Explicit {V : Set V3} {ul : List V3} (h : barV V 2 ul) :
    ∃ u0 u1 u2 : V3, ul = [u0, u1, u2] := by
  have hlen : ul.length = 3 := h.1
  cases ul with
  | nil => simp at hlen
  | cons u0 tl =>
    cases tl with
    | nil => simp at hlen
    | cons u1 tl2 =>
      cases tl2 with
      | nil => simp at hlen
      | cons u2 tl3 =>
        cases tl3 with
        | nil => exact ⟨u0, u1, u2, rfl⟩
        | cons _ tl4 => simp at hlen

/-- HOL `TWO_REARRANGEMENT_LEMMA` (QZKSYKG.hl:131-231): for a `barV V 3`
list, the swap of the first two entries is realized by the left action of a
permutation of `0..1`. (The HL proof only uses the list hypotheses.) -/
private theorem twoRearrangementLemma {V : Set V3} {ul : List V3} {u0 u1 u2 u3 : V3}
    (_hpack : Packing V) (_hsat : saturated V) (_hbar : barV V 3 ul)
    (hul : ul = [u0, u1, u2, u3]) :
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Icc 0 1) ∧
      [u1, u0, u2, u3] = leftActionList p ul := by
  refine ⟨Equiv.swap 0 1, ?_, ?_⟩
  · intro x
    rcases Nat.lt_or_ge x 2 with hx | hx
    · have hx' : x = 0 ∨ x = 1 := by omega
      rcases hx' with rfl | rfl
      · show 0 ∈ Set.Icc 0 1 ↔ (Equiv.swap 0 1) 0 ∈ Set.Icc 0 1
        rw [Equiv.swap_apply_left]
        simp
      · show 1 ∈ Set.Icc 0 1 ↔ (Equiv.swap 0 1) 1 ∈ Set.Icc 0 1
        rw [Equiv.swap_apply_right]
        simp
    · have h0 : x ≠ 0 := by omega
      have h1 : x ≠ 1 := by omega
      show x ∈ Set.Icc 0 1 ↔ (Equiv.swap 0 1) x ∈ Set.Icc 0 1
      rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
  · subst hul
    simp only [leftActionList]
    have e2 : (Equiv.swap 0 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have e3 : (Equiv.swap 0 1) 3 = 3 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    simp [List.range_succ, List.range_zero, e2, e3]

/-- HOL `ROGERS_EXPLICIT_2` (QZKSYKG.hl:100-129): for a `barV V 2` list the
Rogers simplex is the hull of the first three omega points (the length-3
list makes the `omegaListN` image over `{j | j < 3}` explicit). -/
private theorem rogersExplicit2 {V : Set V3} {ul : List V3} (_hsat : saturated V)
    (_hpack : Packing V) (hbar : barV V 2 ul) :
    rogers V ul = convexHull ℝ {hdV ul, omegaListN V ul 1, omegaListN V ul 2} := by
  have hlen : ul.length = 3 := hbar.1
  have hset : {j : ℕ | j < ul.length} = {0, 1, 2} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  unfold rogers
  rw [hset]
  simp [Set.image_insert_eq, omegaListN]


/-- HOL `CONVEX_HULL_4_IMP_3_1` (QZKSYKG.hl:26-75): every point of the hull
of a tetrahedron is a combination of a hull point of the opposite face and
the fourth vertex. -/
private theorem convexHull4Imp31 {a b c d x : V3}
    (hx : x ∈ convexHull ℝ ({a, b, c, d} : Set V3)) :
    ∃ x1 : V3, ∃ t1 t2 : ℝ, x1 ∈ convexHull ℝ ({a, b, c} : Set V3) ∧
      0 ≤ t1 ∧ 0 ≤ t2 ∧ t1 + t2 = 1 ∧ x = t1 • x1 + t2 • d := by
  classical
  have hy4 : ∀ y : V3, y ∈ ({a, b, c, d} : Set V3) → y = a ∨ y = b ∨ y = c ∨ y = d :=
    fun y hy => by simpa using hy
  by_cases hd : d ∈ ({a, b, c} : Set V3)
  · have hd' : d = a ∨ d = b ∨ d = c := by simpa using hd
    refine ⟨x, 1, 0, convexHull_mono ?_ hx, by norm_num, by norm_num, by norm_num, by simp⟩
    intro y hy
    rcases hy4 y hy with rfl | rfl | rfl | rfl <;> simp
    · exact hd
  · -- main case: split off the `d`-weight of a convex combination
    have h4 : x ∈ convexHull ℝ
        ((insert d ({a, b, c} : Finset V3) : Finset V3) : Set V3) := by
      refine convexHull_mono ?_ hx
      intro y hy
      rcases hy4 y hy with rfl | rfl | rfl | rfl <;> simp
    rw [Finset.convexHull_eq] at h4
    obtain ⟨w, hwpos, hwsum, hwx⟩ := h4
    rw [Finset.centerMass_eq_of_sum_1 _ id hwsum] at hwx
    simp only [id_eq] at hwx
    have hnd : d ∉ ({a, b, c} : Finset V3) := by simpa using hd
    rw [Finset.sum_insert hnd] at hwx hwsum
    have hwd0 : 0 ≤ w d := hwpos d (Finset.mem_insert_self d ({a, b, c} : Finset V3))
    have h3 : ∑ y ∈ ({a, b, c} : Finset V3), w y = 1 - w d := by linarith
    by_cases hpos1 : 0 < 1 - w d
    · -- the `d`-weight is a proper fraction: peel it off
      have hsum1 : ∑ y ∈ ({a, b, c} : Finset V3),
          (if y ∈ ({a, b, c} : Finset V3) then (1 - w d)⁻¹ * w y else 0) = 1 := by
        rw [Finset.sum_congr rfl fun y hy => if_pos hy, ← Finset.mul_sum, h3,
          inv_mul_cancel₀ hpos1.ne']
      have hw' : ∀ y ∈ ({a, b, c} : Finset V3), 0 ≤
          (if y ∈ ({a, b, c} : Finset V3) then (1 - w d)⁻¹ * w y else 0) := by
        intro y hy
        rw [if_pos hy]
        exact mul_nonneg (inv_nonneg.2 (by linarith)) (hwpos y (Finset.mem_insert_of_mem hy))
      have hcm : ({a, b, c} : Finset V3).centerMass
          (fun y => if y ∈ ({a, b, c} : Finset V3) then (1 - w d)⁻¹ * w y else 0) id
          = (1 - w d)⁻¹ • ∑ y ∈ ({a, b, c} : Finset V3), w y • y := by
        rw [Finset.centerMass_eq_of_sum_1 _ id hsum1]
        simp only [id_eq]
        have hsplit : (1 - w d)⁻¹ • ∑ y ∈ ({a, b, c} : Finset V3), w y • y
            = ∑ y ∈ ({a, b, c} : Finset V3), (1 - w d)⁻¹ • (w y • y) := by
          rw [Finset.smul_sum]
        rw [hsplit]
        exact Finset.sum_congr rfl fun y hy => by rw [if_pos hy, ← smul_smul]
      have hset3 : ({a, b, c} : Set V3) = (({a, b, c} : Finset V3) : Set V3) := by
        ext y
        simp
      refine ⟨(1 - w d)⁻¹ • ∑ y ∈ ({a, b, c} : Finset V3), w y • y, 1 - w d, w d,
        by rw [hset3, Finset.convexHull_eq]; exact ⟨_, hw', hsum1, hcm⟩,
        by linarith, hwd0, by linarith, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hpos1.ne', one_smul, ← hwx]
      abel
    · -- the `d`-weight is `1`: `x = d`
      push Not at hpos1
      have hwd1 : w d = 1 := by
        have hpos : ∀ y ∈ ({a, b, c} : Finset V3), 0 ≤ w y := fun y hy =>
          hwpos y (Finset.mem_insert_of_mem hy)
        linarith [Finset.sum_nonneg hpos]
      have hwz : ∀ y ∈ ({a, b, c} : Finset V3), w y = 0 := by
        intro y hy
        have hpos : ∀ y ∈ ({a, b, c} : Finset V3), 0 ≤ w y := fun z hz =>
          hwpos z (Finset.mem_insert_of_mem hz)
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg hpos).mp (by linarith)
        exact h0 y hy
      have hxd : x = d := by
        have hsum0 : ∑ y ∈ ({a, b, c} : Finset V3), w y • y = 0 :=
          Finset.sum_eq_zero fun y hy => by rw [hwz y hy, zero_smul]
        rw [← hwx, hwd1, hsum0, one_smul, add_zero]
      exact ⟨a, 0, 1, subset_convexHull ℝ _ (by simp), by norm_num, by norm_num,
        by norm_num, by rw [hxd]; simp⟩

/-! ## Private 01-swap kit (PA14 named-bridge wave 2026-09-30) -/

/-- A prefix of `ul` is the take of its length (induction on `ul`). -/
private theorem p14_prefix_len {α : Type*} :
    ∀ (ul w yl : List α), ul = w ++ yl → w = ul.take (ul.length - yl.length) := by
  intro ul w yl h
  induction ul generalizing w yl with
  | nil =>
    cases w with
    | nil =>
      subst h
      simp
    | cons x t => simp at h
  | cons u ul' ih =>
    cases w with
    | nil =>
      rw [List.nil_append] at h
      subst h
      simp
    | cons x w' =>
      rw [List.cons_append] at h
      obtain ⟨rfl, h2⟩ := List.cons.inj h
      have hle : yl.length ≤ ul'.length := by rw [h2]; simp
      by_cases hk0 : ul'.length - yl.length = 0
      · have hw'0 : w' = [] := by
          by_contra hc
          have hpos : 0 < w'.length := List.length_pos_of_ne_nil hc
          have hlen2 : w'.length = ul'.length - yl.length := by rw [h2]; simp
          omega
        subst hw'0
        have hidx1 : ((u :: ul').length - yl.length) = 1 := by
          simp only [List.length_cons]; omega
        rw [hidx1]
        simp
      · have hidx : ((u :: ul').length - yl.length) = (ul'.length - yl.length) + 1 := by
          simp only [List.length_cons]; omega
        rw [ih w' yl h2, hidx, List.take_cons (by omega), Nat.add_sub_cancel]

/-- shape of a nonempty initial sublist of a 4-list -/
private theorem p14_init_sub_four {a b c d : V3} {w : List V3}
    (hw : initialSublist w [a, b, c, d]) (hne : w ≠ []) :
    w = [a] ∨ w = [a, b] ∨ w = [a, b, c] ∨ w = [a, b, c, d] := by
  obtain ⟨yl, hy⟩ := hw
  have h1 : w.length ≠ 0 := by
    intro hc
    apply hne
    rwa [List.length_eq_zero_iff] at hc
  have hlen : 4 = w.length + yl.length := by
    have hc := congrArg List.length hy
    rw [List.length_append] at hc
    simpa using hc
  have hyle : yl.length ≤ 4 := by omega
  have hwlen : w.length = 4 - yl.length := by omega
  have hwtake : w = [a, b, c, d].take (4 - yl.length) := by
    rw [p14_prefix_len _ _ _ hy]
    rfl
  interval_cases yl.length
  · exact Or.inr (Or.inr (Or.inr (by rw [hwtake]; simp)))
  · exact Or.inr (Or.inr (Or.inl (by rw [hwtake]; simp)))
  · exact Or.inr (Or.inl (by rw [hwtake]; simp))
  · exact Or.inl (by rw [hwtake]; simp)
  · exact absurd hwlen h1

/-- `voronoiNondg` only depends on the point set and the length. -/
private theorem p14_voronoiNondg_congr {V : Set V3} {a b : List V3}
    (hs : setOfList a = setOfList b) (hl : a.length = b.length) :
    voronoiNondg V a ↔ voronoiNondg V b := by
  simp only [voronoiNondg, voronoiList, hs, hl]

/-- `voronoi_list` of a singleton is the cell. -/
private theorem p14_voronoiList_sing (V : Set V3) (u : V3) :
    voronoiList V [u] = voronoiClosed V u := by
  rw [voronoiList, voronoiSet]
  ext x
  simp [setOfList]

/-- Voronoi cells are closed. -/
private theorem p14_isClosed_voronoiClosed (V : Set V3) (v : V3) :
    IsClosed (voronoiClosed V v) := by
  have h : voronoiClosed V v = ⋂ w : V3, {x : V3 | w ∈ V → dist x v ≤ dist x w} := by
    ext x
    simp only [voronoiClosed, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  refine isClosed_iInter fun w => ?_
  by_cases hw : w ∈ V
  · have h2 : {x : V3 | w ∈ V → dist x v ≤ dist x w} = {x : V3 | dist x v ≤ dist x w} := by
      ext x; simp [hw]
    rw [h2]
    exact isClosed_le (Continuous.dist continuous_id continuous_const)
      (Continuous.dist continuous_id continuous_const)
  · have h2 : {x : V3 | w ∈ V → dist x v ≤ dist x w} = (univ : Set V3) := by
      ext x; simp [hw]
    rw [h2]
    exact isClosed_univ

/-- Voronoi lists are closed. -/
private theorem p14_isClosed_voronoiList (V : Set V3) (wl : List V3) :
    IsClosed (voronoiList V wl) := by
  rw [voronoiList, voronoiSet]
  exact isClosed_sInter fun K hK => by
    obtain ⟨w, _, rfl⟩ := hK
    exact p14_isClosed_voronoiClosed V w

/-- The selected closest point of a nonempty closed set belongs to it. -/
private theorem p14_closestPoint_mem {K : Set V3} {x : V3} (hne : K.Nonempty)
    (hc : IsClosed K) : closestPoint K x ∈ K := by
  obtain ⟨k0, hk0⟩ := hne
  have hcomp : IsCompact (K ∩ Metric.closedBall x (dist k0 x)) :=
    IsCompact.inter_left (isCompact_closedBall x (dist k0 x)) hc
  have hne2 : (K ∩ Metric.closedBall x (dist k0 x)).Nonempty :=
    ⟨k0, hk0, Metric.mem_closedBall.2 le_rfl⟩
  obtain ⟨y, hy, hmin⟩ := hcomp.exists_isMinOn hne2
    (Continuous.continuousOn (Continuous.dist continuous_const continuous_id))
  simp only [IsMinOn, IsMinFilter, Filter.eventually_principal] at hmin
  have hmin' : ∀ z ∈ K, dist x y ≤ dist x z := by
    intro z hz
    by_cases hz' : z ∈ Metric.closedBall x (dist k0 x)
    · exact hmin z ⟨hz, hz'⟩
    · have hgt : dist k0 x < dist x z := by
        by_contra hc'
        push Not at hc'
        exact hz' (Metric.mem_closedBall.2 (by rwa [dist_comm]))
      have h2 : dist x y ≤ dist x (k0 : V3) :=
        hmin (k0 : V3) ⟨hk0, Metric.mem_closedBall.2 le_rfl⟩
      rw [dist_comm x k0] at h2
      exact h2.trans hgt.le
  have hsat : ∃ w : V3, w ∈ K ∧ ∀ z ∈ K, dist x w ≤ dist x z := ⟨y, hy.1, hmin'⟩
  exact (Classical.epsilon_spec
    (p := fun w : V3 => w ∈ K ∧ ∀ z ∈ K, dist x w ≤ dist x z) hsat).1

/-- Membership in two Voronoi cells forces equidistance. -/
private theorem p14_dist_eq_of_mem {V : Set V3} {a b x : V3} (ha : a ∈ V) (hb : b ∈ V)
    (h0 : x ∈ voronoiClosed V a) (h1 : x ∈ voronoiClosed V b) : dist x a = dist x b :=
  le_antisymm (h0 b hb) (h1 a ha)

/-- Nonemptiness from a nonnegative affine dimension. -/
private theorem p14_nonempty_of_affDim {S : Set V3} (h : 0 ≤ affDim S) : S.Nonempty := by
  by_contra hcon
  have he : S = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hcon ⟨x, hx⟩
  rw [he, affDim_empty] at h
  norm_num at h

/-- the squared norm is the self dot product. -/
private theorem p14_norm_sq_dot (v : V3) :
    ‖v‖ ^ 2 = (v : Fin 3 → ℝ) ⬝ᵥ (v : Fin 3 → ℝ) := by
  have h := real_inner_self_eq_norm_sq v
  rw [← h, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- A Voronoi cell around a packing point has affine dimension 3. -/
private theorem p14_affDim_voronoiClosed {V : Set V3} {u : V3} (hp : Packing V)
    (hu : u ∈ V) : affDim (voronoiClosed V u) = 3 := by
  have hne : (voronoiClosed V u).Nonempty := ⟨u, fun w _ => by simp⟩
  have h1 : (⊤ : Submodule ℝ V3) ≤ vectorSpan ℝ (voronoiClosed V u) := by
    rw [vectorSpan_def, ← (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.span_eq]
    refine Submodule.span_le.2 ?_
    rintro e ⟨i, rfl⟩
    refine Submodule.subset_span ?_
    refine Set.mem_vsub.2 ?_
    refine ⟨u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3), ?_, u, ?_,
      by simp [vsub_eq_sub]⟩
    · intro w hw
      show dist (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) u ≤
        dist (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) w
      rcases eq_or_ne w u with rfl | hne
      · exact le_refl _
      · have hsep : (2 : ℝ) ≤ dist u w := Packing.dist_ge_two hp hu hw hne.symm
        have hnorm1 : dist (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) u = 1 := by
          rw [dist_eq_norm, add_sub_cancel_left]
          have hcoe : ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)
              = EuclideanSpace.basisFun (Fin 3) ℝ i := rfl
          rw [hcoe, EuclideanSpace.basisFun_apply, PiLp.norm_single]
          simp
        have htri : dist u w ≤ dist u (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) +
            dist (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) w :=
          dist_triangle u _ _
        rw [dist_comm u (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)), hnorm1] at htri
        show dist (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) u ≤
          dist (u + ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i : V3)) w
        rw [hnorm1]
        linarith
    · intro w _
      show dist u u ≤ dist u w
      simp
  have h2 : vectorSpan ℝ (voronoiClosed V u) = ⊤ :=
    (le_antisymm h1 le_top).symm
  simp only [affDim, if_neg (nonempty_iff_ne_empty.1 hne)]
  rw [h2, finrank_top]
  norm_cast
  exact finrank_euclideanSpace_fin

/-- `voronoiNondg V [u]` for a packing point. -/
private theorem p14_voronoiNondg_sing {V : Set V3} {u : V3} (hp : Packing V) (hu : u ∈ V) :
    voronoiNondg V [u] := by
  have hd := p14_affDim_voronoiClosed (V := V) (u := u) hp hu
  refine ⟨by norm_num, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact hu
    · exact absurd hx' (by simp)
  · show affDim (voronoiList V [u]) + ((1 : ℕ) : ℤ) = 4
    rw [p14_voronoiList_sing, hd]
    norm_num

/-- Membership of the omega points in their truncation's Voronoi list. -/
private theorem p14_omega_mem {V : Set V3} {ul : List V3} {j : ℕ} (hj : 1 ≤ j)
    (hne : (voronoiList V (truncateSimplex j ul)).Nonempty) :
    omegaListN V ul j ∈ voronoiList V (truncateSimplex j ul) := by
  cases j with
  | zero => exact absurd hj (by omega)
  | succ j => exact p14_closestPoint_mem hne (p14_isClosed_voronoiList V _)

/-- `convex hull {a, b} = segment ℝ a b`. -/
private theorem p14_hull_pair (a b : V3) : convexHull ℝ {a, b} = segment ℝ a b := by
  refine Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · refine convexHull_min (fun w hw => ?_) (convex_segment (𝕜 := ℝ) a b) hz
    rcases hw with rfl | hw'
    · exact left_mem_segment ℝ _ _
    · rw [hw']
      exact right_mem_segment ℝ _ _
  · rcases hz with ⟨u, w, hu, hw, huw, rfl⟩
    have hconv := convex_convexHull (𝕜 := ℝ) (s := ({a, b} : Set V3))
    exact hconv (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
      hu hw huw

/-- left action of a permutation swapping `0` and `1` and fixing the tail. -/
private theorem p14_leftActionList_swap01 (u0 u1 u2 u3 : V3) (p : Equiv.Perm ℕ)
    (h0 : p 0 = 1) (h1 : p 1 = 0) (hfix : ∀ j : ℕ, 2 ≤ j → p j = j) :
    leftActionList p [u0, u1, u2, u3] = [u1, u0, u2, u3] := by
  simp only [leftActionList]
  have e0 : p.symm 0 = 1 := (Equiv.symm_apply_eq p).2 (by rw [h1])
  have e1 : p.symm 1 = 0 := (Equiv.symm_apply_eq p).2 (by rw [h0])
  have e2 : p.symm 2 = 2 := (Equiv.symm_apply_eq p).2 (by rw [hfix 2 le_rfl])
  have e3 : p.symm 3 = 3 := (Equiv.symm_apply_eq p).2 (by rw [hfix 3 (by omega)])
  simp [List.range_succ, List.range_zero, e0, e1, e2, e3]

/-- left action of a permutation fixing `0`, `1` and the tail. -/
private theorem p14_leftActionList_refl01 (u0 u1 u2 u3 : V3) (p : Equiv.Perm ℕ)
    (h0 : p 0 = 0) (h1 : p 1 = 1) (hfix : ∀ j : ℕ, 2 ≤ j → p j = j) :
    leftActionList p [u0, u1, u2, u3] = [u0, u1, u2, u3] := by
  simp only [leftActionList]
  have e0 : p.symm 0 = 0 := (Equiv.symm_apply_eq p).2 (by rw [h0])
  have e1 : p.symm 1 = 1 := (Equiv.symm_apply_eq p).2 (by rw [h1])
  have e2 : p.symm 2 = 2 := (Equiv.symm_apply_eq p).2 (by rw [hfix 2 le_rfl])
  have e3 : p.symm 3 = 3 := (Equiv.symm_apply_eq p).2 (by rw [hfix 3 (by omega)])
  simp [List.range_succ, List.range_zero, e0, e1, e2, e3]

/-- equidistant endpoints propagate along the segment. -/
private theorem p14_seg_dist_eq {a b x y : V3} (h1 : dist a x = dist a y)
    (h2 : dist b x = dist b y) {p : V3} (hp : p ∈ segment ℝ a b) : dist p x = dist p y := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  have hbrin : ∀ u v w : Fin 3 → ℝ, u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := dotProduct_sub
  have hcomm : ∀ u v : Fin 3 → ℝ, u ⬝ᵥ v = v ⬝ᵥ u := dotProduct_comm
  have haddl : ∀ u v w : Fin 3 → ℝ, (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := add_dotProduct
  have hsmull : ∀ (r : ℝ) (u w : Fin 3 → ℝ), (r • u) ⬝ᵥ w = r * (u ⬝ᵥ w) := smul_dotProduct
  have hsqrw : ∀ u v : Fin 3 → ℝ, (u - v) ⬝ᵥ (u - v) = u ⬝ᵥ u - 2 * (v ⬝ᵥ u) + v ⬝ᵥ v := by
    intro u v
    rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, hcomm v u]
    ring
  have key : ∀ z : V3, dist z x ^ 2 - dist z y ^ 2
      = 2 * ((z : Fin 3 → ℝ) ⬝ᵥ ((y : Fin 3 → ℝ) - (x : Fin 3 → ℝ)))
        + (((x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ)) - ((y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ))) := by
    intro z
    rw [dist_eq_norm, dist_eq_norm, p14_norm_sq_dot (z - x), p14_norm_sq_dot (z - y),
      WithLp.ofLp_sub, WithLp.ofLp_sub,
      hsqrw (z : Fin 3 → ℝ) (x : Fin 3 → ℝ), hsqrw (z : Fin 3 → ℝ) (y : Fin 3 → ℝ),
      hbrin (z : Fin 3 → ℝ) (y : Fin 3 → ℝ) (x : Fin 3 → ℝ),
      hcomm (x : Fin 3 → ℝ) (z : Fin 3 → ℝ), hcomm (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)]
    ring
  have hlin : (α • a + β • b : V3) ⬝ᵥ ((y : Fin 3 → ℝ) - (x : Fin 3 → ℝ))
      = α * ((a : Fin 3 → ℝ) ⬝ᵥ ((y : Fin 3 → ℝ) - (x : Fin 3 → ℝ)))
        + β * ((b : Fin 3 → ℝ) ⬝ᵥ ((y : Fin 3 → ℝ) - (x : Fin 3 → ℝ))) := by
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, haddl, hsmull, hsmull]
  have haff : dist (α • a + β • b) x ^ 2 - dist (α • a + β • b) y ^ 2 = 0 := by
    have hsum : (α + β) * ((x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ)
              - (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ))
        = ((x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) - (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)) := by
      rw [hαβ, one_mul]
    have φa : dist a x ^ 2 - dist a y ^ 2 = 0 := by rw [h1]; ring
    have φb : dist b x ^ 2 - dist b y ^ 2 = 0 := by rw [h2]; ring
    have e4t : 2 * ((a : Fin 3 → ℝ) ⬝ᵥ ((y : Fin 3 → ℝ) - (x : Fin 3 → ℝ)))
        + ((x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) - (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)) = 0 := by
      rw [← key a]
      exact φa
    have e5t : 2 * ((b : Fin 3 → ℝ) ⬝ᵥ ((y : Fin 3 → ℝ) - (x : Fin 3 → ℝ)))
        + ((x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) - (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)) = 0 := by
      rw [← key b]
      exact φb
    rw [key (α • a + β • b), hlin]
    linear_combination α * e4t + β * e5t - hsum
  have hsq : dist (α • a + β • b) x ^ 2 = dist (α • a + β • b) y ^ 2 :=
    sub_eq_zero.1 haff
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at hsq
  exact hsq

/-- `initialSublist` reflexivity. -/
private theorem p14_initialSublist_self (ul : List V3) : initialSublist ul ul :=
  ⟨[], (List.append_nil ul).symm⟩

/-- the packing points of a `barV V 3` list lie in `V`. -/
private theorem p14_mem_V_of_barV {V : Set V3} {u0 u1 u2 u3 : V3}
    (hb : barV V 3 [u0, u1, u2, u3]) :
    u0 ∈ V ∧ u1 ∈ V ∧ u2 ∈ V ∧ u3 ∈ V := by
  have hfull := hb.2 [u0, u1, u2, u3] ⟨p14_initialSublist_self [u0, u1, u2, u3], by simp⟩
  obtain ⟨_, hsub, _⟩ := hfull
  refine ⟨hsub (by simp [setOfList]), hsub (by simp [setOfList]), hsub (by simp [setOfList]),
    hsub (by simp [setOfList])⟩

/-- `barV` persists under the swap of the first two entries. -/
private theorem p14_barV_swap01 {V : Set V3} {u0 u1 u2 u3 : V3} (hp : Packing V)
    (hb : barV V 3 [u0, u1, u2, u3]) : barV V 3 [u1, u0, u2, u3] := by
  have hV := p14_mem_V_of_barV hb
  refine ⟨rfl, fun w hw => ?_⟩
  obtain ⟨hw, hwne⟩ := hw
  have hset1 : setOfList [u1, u0] = setOfList [u0, u1] := by
    ext x; simp [setOfList]; tauto
  have hset2 : setOfList [u1, u0, u2] = setOfList [u0, u1, u2] := by
    ext x; simp [setOfList]; tauto
  have hset4 : setOfList [u1, u0, u2, u3] = setOfList [u0, u1, u2, u3] := by
    ext x; simp [setOfList]; tauto
  rcases p14_init_sub_four hw (List.length_pos_iff.mp hwne) with rfl | rfl | rfl | rfl
  · exact p14_voronoiNondg_sing hp hV.2.1
  · exact (p14_voronoiNondg_congr (a := [u1, u0]) (b := [u0, u1]) hset1 rfl).2
      (hb.2 [u0, u1] ⟨INITIAL_SUBLIST_APPEND [u0, u1] [u2, u3], by simp⟩)
  · exact (p14_voronoiNondg_congr (a := [u1, u0, u2]) (b := [u0, u1, u2]) hset2 rfl).2
      (hb.2 [u0, u1, u2] ⟨INITIAL_SUBLIST_APPEND [u0, u1, u2] [u3], by simp⟩)
  · exact (p14_voronoiNondg_congr (a := [u1, u0, u2, u3]) (b := [u0, u1, u2, u3]) hset4 rfl).2
      (hb.2 [u0, u1, u2, u3] ⟨p14_initialSublist_self [u0, u1, u2, u3], by simp⟩)

/-- omega points of a truncation are equidistant from the truncation's points. -/
private theorem p14_omega_dist_eq {V : Set V3} {wl : List V3} {j : ℕ} {u0 u1 : V3}
    (hmem : omegaListN V wl j ∈ voronoiList V (truncateSimplex j wl))
    (hu0 : u0 ∈ setOfList (truncateSimplex j wl)) (hu1 : u1 ∈ setOfList (truncateSimplex j wl))
    (hu0V : u0 ∈ V) (hu1V : u1 ∈ V) :
    dist (omegaListN V wl j) u0 = dist (omegaListN V wl j) u1 := by
  rw [voronoiList, voronoiSet, Set.mem_sInter] at hmem
  have h0 : omegaListN V wl j ∈ voronoiClosed V u0 := hmem _ (Set.mem_setOf.2 ⟨u0, hu0, rfl⟩)
  have h1 : omegaListN V wl j ∈ voronoiClosed V u1 := hmem _ (Set.mem_setOf.2 ⟨u1, hu1, rfl⟩)
  exact p14_dist_eq_of_mem hu0V hu1V h0 h1

/-- `mxi` is invariant under the swap of the first two entries. -/
private theorem p14_mxi_swap {V : Set V3} {u0 u1 u2 u3 : V3}
    (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hω2 : omegaListN V [u1, u0, u2, u3] 2 = omegaListN V [u0, u1, u2, u3] 2)
    (hω3 : omegaListN V [u1, u0, u2, u3] 3 = omegaListN V [u0, u1, u2, u3] 3) :
    mxi V [u1, u0, u2, u3] = mxi V [u0, u1, u2, u3] := by
  have hV := p14_mem_V_of_barV hb
  have hT1 := (TRUNCATE_SIMPLEX_EXPLICIT_2 u1 u0 u2 u3).2
  have hT2 := (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hset : setOfList (truncateSimplex 2 [u1, u0, u2, u3])
      = setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by
    rw [hT1, hT2]
    ext x
    simp [setOfList]; tauto
  have hhl : hl (truncateSimplex 2 [u1, u0, u2, u3]) = hl (truncateSimplex 2 [u0, u1, u2, u3]) := by
    rw [hl, hl, hset]
  show (if Real.sqrt 2 ≤ hl (truncateSimplex 2 [u1, u0, u2, u3]) then
      omegaListN V [u1, u0, u2, u3] 2
    else Classical.epsilon fun q : V3 => q ∈
        convexHull ℝ {omegaListN V [u1, u0, u2, u3] 2, omegaListN V [u1, u0, u2, u3] 3} ∧
        dist q (hdV [u1, u0, u2, u3]) = Real.sqrt 2)
    = (if Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3]) then
      omegaListN V [u0, u1, u2, u3] 2
    else Classical.epsilon fun q : V3 => q ∈
        convexHull ℝ {omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} ∧
        dist q (hdV [u0, u1, u2, u3]) = Real.sqrt 2)
  rw [hhl, hω2, hω3]
  by_cases hc : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3])
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
    have hT3 : truncateSimplex 3 [u0, u1, u2, u3] = [u0, u1, u2, u3] :=
      TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3
    have hK2ne : (voronoiList V (truncateSimplex 2 [u0, u1, u2, u3])).Nonempty := by
      rw [hT2]
      refine p14_nonempty_of_affDim ?_
      have hnd := hb.2 [u0, u1, u2] ⟨INITIAL_SUBLIST_APPEND [u0, u1, u2] [u3], by simp⟩
      have hnd' : affDim (voronoiList V [u0, u1, u2]) + ((3 : ℕ) : ℤ) = 4 := hnd.2.2
      omega
    have hK3ne : (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3])).Nonempty := by
      rw [hT3]
      refine p14_nonempty_of_affDim ?_
      have hnd := hb.2 [u0, u1, u2, u3] ⟨p14_initialSublist_self [u0, u1, u2, u3], by simp⟩
      have hnd' : affDim (voronoiList V [u0, u1, u2, u3]) + ((4 : ℕ) : ℤ) = 4 := hnd.2.2
      omega
    have hω2mem : omegaListN V [u0, u1, u2, u3] 2
        ∈ voronoiList V (truncateSimplex 2 [u0, u1, u2, u3]) := p14_omega_mem (by omega) hK2ne
    have hω3mem : omegaListN V [u0, u1, u2, u3] 3
        ∈ voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]) := p14_omega_mem (by omega) hK3ne
    have hu0m : u0 ∈ setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by rw [hT2]; simp [setOfList]
    have hu1m : u1 ∈ setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by rw [hT2]; simp [setOfList]
    have heq2 : dist (omegaListN V [u0, u1, u2, u3] 2) u0
        = dist (omegaListN V [u0, u1, u2, u3] 2) u1 :=
      p14_omega_dist_eq hω2mem hu0m hu1m hV.1 hV.2.1
    have heq3 : dist (omegaListN V [u0, u1, u2, u3] 3) u0
        = dist (omegaListN V [u0, u1, u2, u3] 3) u1 :=
      p14_omega_dist_eq hω3mem (by rw [hT3]; simp [setOfList]) (by rw [hT3]; simp [setOfList])
        hV.1 hV.2.1
    have hseg : ∀ q : V3, q ∈ convexHull ℝ
        {omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} →
        dist q u0 = dist q u1 := by
      intro q hq
      rw [p14_hull_pair] at hq
      exact p14_seg_dist_eq heq2 heq3 hq
    have hpointwise : ∀ q : V3,
        (q ∈ convexHull ℝ {omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} ∧
            dist q (hdV [u1, u0, u2, u3]) = Real.sqrt 2) ↔
        (q ∈ convexHull ℝ {omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} ∧
            dist q (hdV [u0, u1, u2, u3]) = Real.sqrt 2) := by
      intro q
      constructor
      · rintro ⟨hm, hd⟩
        rw [show hdV [u1, u0, u2, u3] = u1 from rfl] at hd
        rw [show hdV [u0, u1, u2, u3] = u0 from rfl]
        rw [hseg q hm]
        exact ⟨hm, hd⟩
      · rintro ⟨hm, hd⟩
        rw [show hdV [u0, u1, u2, u3] = u0 from rfl] at hd
        rw [show hdV [u1, u0, u2, u3] = u1 from rfl]
        rw [← hseg q hm]
        exact ⟨hm, hd⟩
    exact congrArg Classical.epsilon (funext fun q => propext (hpointwise q))

/-- the full `{0,1}`-swap invariance pack (barV, omega 1..3, mxi). -/
private theorem p14_swap_pack {V : Set V3} {u0 u1 u2 u3 : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hhl : hl [u0, u1] < Real.sqrt 2) (hsq : Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) :
    barV V 3 [u1, u0, u2, u3] ∧
      omegaListN V [u1, u0, u2, u3] 1 = omegaListN V [u0, u1, u2, u3] 1 ∧
      omegaListN V [u1, u0, u2, u3] 2 = omegaListN V [u0, u1, u2, u3] 2 ∧
      omegaListN V [u1, u0, u2, u3] 3 = omegaListN V [u0, u1, u2, u3] 3 ∧
      mxi V [u1, u0, u2, u3] = mxi V [u0, u1, u2, u3] := by
  have hbV : barV V 3 [u1, u0, u2, u3] := p14_barV_swap01 hp hb
  have hhl1 : hl [u1, u0] = hl [u0, u1] := by
    rw [hl, hl]
    congr 1
    ext x
    simp [setOfList]
    tauto
  have h1a := OMEGA_LIST_1_EXPLICIT_NEW u1 u0 u2 u3 V [u1, u0, u2, u3] hs hp hbV rfl
    (by rw [hhl1]; exact hhl)
  have h1b := OMEGA_LIST_1_EXPLICIT_NEW u0 u1 u2 u3 V [u0, u1, u2, u3] hs hp hb rfl hhl
  have hw1 : omegaListN V [u1, u0, u2, u3] 1 = omegaListN V [u0, u1, u2, u3] 1 := by
    rw [h1a, h1b]
    exact congrArg circumcenter (by ext x; simp; tauto)
  have hT1 := (TRUNCATE_SIMPLEX_EXPLICIT_2 u1 u0 u2 u3).2
  have hT2 := (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hs2 : setOfList [u1, u0, u2] = setOfList [u0, u1, u2] := by
    ext x
    simp [setOfList]
    tauto
  have hw2 : omegaListN V [u1, u0, u2, u3] 2 = omegaListN V [u0, u1, u2, u3] 2 := by
    show closestPoint (voronoiList V (truncateSimplex 2 [u1, u0, u2, u3]))
        (omegaListN V [u1, u0, u2, u3] 1) =
      closestPoint (voronoiList V (truncateSimplex 2 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 1)
    rw [hT1, hT2]
    simp only [voronoiList, hs2]
    exact congrArg _ hw1
  have hT3a := TRUNCATE_SIMPLEX_EXPLICIT_3 u1 u0 u2 u3
  have hT3b := TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3
  have hs4 : setOfList [u1, u0, u2, u3] = setOfList [u0, u1, u2, u3] := by
    ext x
    simp [setOfList]
    tauto
  have hw3 : omegaListN V [u1, u0, u2, u3] 3 = omegaListN V [u0, u1, u2, u3] 3 := by
    show closestPoint (voronoiList V (truncateSimplex 3 [u1, u0, u2, u3]))
        (omegaListN V [u1, u0, u2, u3] 2) =
      closestPoint (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 2)
    rw [hT3a, hT3b]
    simp only [voronoiList, hs4]
    exact congrArg _ hw2
  exact ⟨hbV, hw1, hw2, hw3, p14_mxi_swap hp hb hw2 hw3⟩

/-! ## NEEDS copies (parallel-owned sources not importable here) -/

/-- NEEDS: `YNHYJIT` (YNHYJIT.hl:33-103) — parallel-owned by PackingAuto10,
whose olean is not available in this checkout. Left-action invariance of
`barV` and of the omega points at levels `i-1..3` in the small-truncation
regime.

Encoding caveat (same as the PackingAuto10 copy): with the weak
pointwise-membership `PackingAuto2.permutes`, `p` need not fix indices
`≥ i-1`, whereas the HL proof goes through
`LEFT_ACTION_LIST_PROPERTIES`/`LEFT_ACTION_LIST_1_PROPERTIES`
(complement-fixing), so the statement may be false as pointwise-encoded
(e.g. a transposition moving an index `≥ i-1`); `sorry`ed pending an
explicit side condition `∀ j ≥ i-1, p j = j`.

Status 2026-09-30: closed for i = 2 (the p14_swap_pack 01-bridge) and
i = 4 (contradiction `hl (truncate 3 ul) < √2` vs `√2 ≤ hl ul`); i = 3
remains `sorry`ed (see NEEDS inline). -/
private theorem ynhyjit_p14 {V : Set V3} {ul vl : List V3} {i : ℕ} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hi : i ∈ ({2, 3, 4} : Set ℕ))
    (h1 : hl (truncateSimplex (i - 1) ul) < Real.sqrt 2)
    (h2 : Real.sqrt 2 ≤ hl ul)
    (hperm : permutes p (Set.Icc 0 (i - 1)))
    (hfix : ∀ j : ℕ, i ≤ j → p j = j)
    (hvl : vl = leftActionList p ul) :
    barV V 3 vl ∧
      ∀ j : ℕ, i - 1 ≤ j → j ≤ 3 → omegaListN V vl j = omegaListN V ul j := by
  subst hvl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl
  · -- i = 2: the 01-swap bridge
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at h1
    have hp0 : p 0 = 0 ∨ p 0 = 1 := by
      have h0 : p 0 ∈ Set.Icc 0 1 := (hperm 0).1 (by simp)
      obtain ⟨_, h02⟩ := h0
      rcases Nat.lt_or_ge (p 0) 1 with hc | hc
      · exact Or.inl (Nat.lt_one_iff.mp hc)
      · exact Or.inr (Nat.le_antisymm h02 hc)
    rcases hp0 with h0 | h0
    · have hp1 : p 1 = 1 := by
        have h1' : p 1 ∈ Set.Icc 0 1 := (hperm 1).1 (by simp)
        obtain ⟨_, h12⟩ := h1'
        have hne : p 1 ≠ 0 := fun hc => absurd (p.injective (h0.trans hc.symm)) (by decide)
        rcases Nat.lt_or_ge (p 1) 1 with hc | hc
        · exact absurd (Nat.lt_one_iff.mp hc) hne
        · exact Nat.le_antisymm h12 hc

      rw [p14_leftActionList_refl01 u0 u1 u2 u3 p h0 hp1 hfix]
      exact ⟨hbar, fun j _ _ => rfl⟩
    · have hp1 : p 1 = 0 := by
        have h1' : p 1 ∈ Set.Icc 0 1 := (hperm 1).1 (by simp)
        obtain ⟨_, h12⟩ := h1'
        have hne : p 1 ≠ 1 := fun hc => absurd (p.injective (h0.trans hc.symm)) (by decide)
        rcases Nat.lt_or_ge (p 1) 1 with hc | hc
        · exact Nat.lt_one_iff.mp hc
        · exact absurd (Nat.le_antisymm h12 hc) hne
      rw [p14_leftActionList_swap01 u0 u1 u2 u3 p h0 hp1 hfix]
      obtain ⟨hbarV, hw1, hw2, hw3, _⟩ := p14_swap_pack hsat hpack hbar h1 h2
      refine ⟨hbarV, fun j hj1 hj2 => ?_⟩
      interval_cases j
      · exact hw1
      · exact hw2
      · exact hw3
  · -- i = 3: the S₃-action case.
    -- NEEDS: port `LEFT_ACTION_LIST_PROPERTIES` (marchal2.hl:4460). The
    -- rotations of `{0,1,2}` require `voronoiNondg` for the non-initial
    -- pairs `{u0,u2}`/`{u1,u2}` (facet dimensions of the truncated voronoi
    -- complex), a genuine geometry bite beyond the 01-swap kit. Blocks only
    -- the i = 3 instances; the i = 2 bridge above is fully closed.
    sorry
  · -- i = 4: hypotheses contradictory (`hl (truncate 3 ul) < √2` vs `√2 ≤ hl ul`)
    exfalso
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    rw [TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3] at h1
    linarith

/- `MXI_EXPLICIT` (marchal2.hl:2516) is PA12's proved public theorem
(imported below); the unused private `mxiExplicit_p14` copy was deleted
DEDUP 2026-09-19. Under the `mcell3` regime the `mxi` point is realized on
the segment from `omegaListN V ul 2` to `omegaListN V ul 3` at distance
`sqrt 2` from `u0` (`SEGMENT_INTER_CBALL_LEMMA` + `@`-definition). -/

/-- HOL `LEFT_ACTION_LIST_1_PROPERTIES_ALT` (TSKAJXY3.hl:1694), the PA14
named LEFT_ACTION bridge for PackingAuto21's theorem of the same name.
Left action of a permutation of `{0,1}` on a `barV V 3` list keeps it `barV`
and preserves the omega points at levels 1..3 and `mxi`.

-- ENCODING-FIX 2026-09-30 (mirror of the PA10 ruling): HOL `permutes`
(`Library/perms.ml`) is complement-fixing, so the faithful Lean form carries
the tail-fixedness side condition `∀ j ≥ 2, p j = j` explicitly; the weak
pointwise-membership `permutes` hypothesis alone would make the statement
false (a permutation moving index `≥ 2` injects junk `getD`-default entries
into `xl`, breaking `voronoiNondg`). PA21's copy must carry the same extra
hypothesis before the one-line migration. -/
theorem LEFT_ACTION_LIST_1_PROPERTIES_ALT (V : Set V3) (ul : List V3) (xl : List V3)
    (p : Equiv.Perm ℕ) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hperm : permutes p {0, 1}) (hfix : ∀ j : ℕ, 2 ≤ j → p j = j)
    (hhl : hl (truncateSimplex 1 ul) < Real.sqrt 2)
    (hsq : Real.sqrt 2 ≤ hl ul) (hxl : xl = leftActionList p ul) :
    barV V 3 xl ∧
      omegaListN V xl 1 = omegaListN V ul 1 ∧
      omegaListN V xl 2 = omegaListN V ul 2 ∧
      omegaListN V xl 3 = omegaListN V ul 3 ∧
      mxi V xl = mxi V ul := by
  subst hxl
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  subst hul
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at hhl
  have hp0 : p 0 = 0 ∨ p 0 = 1 := by
    have h0 : p 0 ∈ ({0, 1} : Set ℕ) := (hperm 0).1 (by simp)
    simpa using h0
  rcases hp0 with h0 | h0
  · have hp1 : p 1 = 1 := by
      have h1' : p 1 ∈ ({0, 1} : Set ℕ) := (hperm 1).1 (by simp)
      rcases (by simpa using h1' : p 1 = 0 ∨ p 1 = 1) with hc | hc
      · exact absurd (p.injective (h0.trans hc.symm)) (by decide)
      · exact hc
    rw [p14_leftActionList_refl01 u0 u1 u2 u3 p h0 hp1 hfix]
    exact ⟨hb, rfl, rfl, rfl, rfl⟩
  · have hp1 : p 1 = 0 := by
      have h1' : p 1 ∈ ({0, 1} : Set ℕ) := (hperm 1).1 (by simp)
      rcases (by simpa using h1' : p 1 = 0 ∨ p 1 = 1) with hc | hc
      · exact hc
      · exact absurd (p.injective (h0.trans hc.symm)) (by decide)
    rw [p14_leftActionList_swap01 u0 u1 u2 u3 p h0 hp1 hfix]
    exact p14_swap_pack hs hp hb hhl hsq

/-- HOL `MCELL2_PERMUTE_01` (TSKAJXY3.hl:1714), the PA14 named PERMUTE_01
bridge for PackingAuto21's theorem of the same name: the `{0,1}`-swap of a
`barV V 3` list whose `mcell2` is non-null yields the mirrored list with the
same `mcell2`, `mxi`, omega point 3, truncation height and `barV` property. -/
theorem MCELL2_PERMUTE_01 (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    ∃ vl : List V3, elV ul 0 = elV vl 1 ∧ elV ul 1 = elV vl 0 ∧
      mxi V ul = mxi V vl ∧ omegaListN V ul 3 = omegaListN V vl 3 ∧
      hl (truncateSimplex 1 ul) = hl (truncateSimplex 1 vl) ∧
      mcell2 V ul = mcell2 V vl ∧ barV V 3 vl := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  subst hul
  have hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra hc
    rcases not_and_or.mp hc with hc1 | hc2
    · rw [mcell2, if_neg (by simp [hc1])] at hn
      exact hn (by simp [nullSet])
    · rw [mcell2, if_neg (by simp [hc2])] at hn
      exact hn (by simp [nullSet])
  obtain ⟨h1, h2⟩ := hcond
  have hhl' : hl [u0, u1] < Real.sqrt 2 := by
    rwa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at h1
  obtain ⟨hbV, _, _, hw3, hmxi⟩ := p14_swap_pack hs hp hb hhl' h2
  have hs1 : hl [u1, u0] = hl [u0, u1] := by
    rw [hl, hl]
    congr 1
    ext x
    simp [setOfList]
    tauto
  have hsul : setOfList [u1, u0, u2, u3] = setOfList [u0, u1, u2, u3] := by
    ext x
    simp [setOfList]
    tauto
  have hhlv : hl (truncateSimplex 1 [u1, u0, u2, u3])
      = hl (truncateSimplex 1 [u0, u1, u2, u3]) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u1 u0 u2 u3).2.2,
        (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2, hs1]
  have hhlv' : hl (truncateSimplex 1 [u1, u0, u2, u3]) < Real.sqrt 2 := by rwa [hhlv]
  have h2v : Real.sqrt 2 ≤ hl [u1, u0, u2, u3] := by
    show Real.sqrt 2 ≤ radV (setOfList [u1, u0, u2, u3])
    rwa [hsul]
  have hpair : ({hdV [u1, u0, u2, u3], hdV [u1, u0, u2, u3].tail} : Set V3)
      = {hdV [u0, u1, u2, u3], hdV [u0, u1, u2, u3].tail} := by
    ext x
    simp [hdV]
    tauto
  have hlv : elV [u0, u1, u2, u3] 0 = elV [u1, u0, u2, u3] 1 := rfl
  have hlv2 : elV [u0, u1, u2, u3] 1 = elV [u1, u0, u2, u3] 0 := rfl
  have hm2 : mcell2 V [u0, u1, u2, u3] = mcell2 V [u1, u0, u2, u3] := by
    ext x
    simp only [mcell2, hhlv, if_pos (And.intro h1 h2), if_pos (And.intro h1 h2v),
      Set.mem_inter_iff, Set.mem_setOf_eq, hpair, hmxi.symm, hw3.symm]
    tauto
  exact ⟨[u1, u0, u2, u3], hlv, hlv2, hmxi.symm, hw3.symm,
    by rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u1 u0 u2 u3).2.2, hs1], hm2, hbV⟩

/-! ## The two QZKSYKG capstones (QZKSYKG.hl:266-2251) -/

/-- HOL `QZKSYKG1` (QZKSYKG.hl:244-253 concl, proof 266-320): a left action
of a permutation of `0..k-1` on a `barV V 3` list keeps it `barV`, provided
the cell `mcell k V ul` is nonempty.

HL proof shape: `k = 0, 1` — `PERMUTES_TRIVIAL` (`p = id`) +
`LEFT_ACTION_LIST_I`; `k = 4` — `mcell4` unfolding + `YIFVQDV_1`
(itself `sorry`ed in PackingAuto7); `k = 2, 3` — `mcell2`/`mcell3`
unfoldings + `YNHYJIT` (`ynhyjit_p14` above; its i = 2 case is closed by
the 01-swap bridge, i = 3 open).

Status 2026-09-30: still `sorry`ed. The k ≤ 3 cases are unprovable as
encoded (weak `permutes` lets p move tail indices into `getD`-junk slots),
so the frozen statement would need the PA10-style tail-fixedness side
condition; the k = 4 case is the `YIFVQDV_1` giant (full rearrangement
invariance of `barV`).
DISCHARGES: none (`QZKSYKG` has no `pack_concl` interface; the results feed
marchal3/KIZHLTL downstream). -/
theorem QZKSYKG1 {V : Set V3} {ul vl : List V3} {k : ℕ} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hne : mcell k V ul ≠ ∅)
    (hperm : permutes p (Set.Icc 0 (k - 1))) (hvl : vl = leftActionList p ul) :
    barV V 3 vl := by
  -- NEEDS: (a) k ≤ 3 — the statement is false under the weak pointwise
  -- `permutes` encoding (p may throw `getD`-default junk into tail slots:
  -- k = 1, p 1 ↦ 7 gives leftActionList p ul = [u0, default, u2, u3] whose
  -- point set leaves V); the faithful encoding needs the PA10-style
  -- tail-fixedness side condition `∀ j ≥ k, p j = j` added to the frozen
  -- statement. (b) k = 4 — the `YIFVQDV_1` giant (barV-invariance under the
  -- full rearrangement of 0..3: voronoiNondg for all pair/triple facets).
  sorry

/-- HOL `QZKSYKG2` (QZKSYKG.hl:255-262 concl, proof 325-2251): `mcell k V ul`
is covered by the union of the Rogers simplices of all left-action
permutations of `ul` of `0..k-1`.

GIANT (~1900 HL lines): case `k = 0` — `mcell0 ⊆ rogers V ul` (`mcell0` def,
identity permutation); `k = 1` — `mcell1 ⊆ rogers V ul`; `k = 4` —
`WQPRRDY` + `mcell4` hull = union over permutations of `0..3`; `k = 3` —
`mcell3` = hull of `{u0, u1, u2, mxi}` covered via `CONVEX_HULL_4_IMP_3_1`,
`TRUNCATE_SIMPLEX`/`OMEGA_LIST_N` kit, `WAUFCHE1`, `MXI_EXPLICIT`
(`mxiExplicit_p14`), `MHFTTZN4`, `XNHPWAB1`, `CLOSEST_POINT_LE` and
Pythagoras on the Voronoi lists; `k = 2` — edge cell between the two mutual
`rcone_ge`s covered by the two Rogers simplices `rogers V ul` and
`rogers V [u1; u0; u2; u3]` (via `TWO_REARRANGEMENT_LEMMA`, `YNHYJIT`,
`ROGERS_EXPLICIT`, `OMEGA_LIST_1_EXPLICIT_NEW`, and a long rcone/rcone
computation on the `rcone_ge` inequality `a = hl (truncate_simplex 1 ul) /
sqrt 2`). `sorry`ed as a giant; several ingredients (`WAUFCHE1` etc.) are
proved in PackingAuto6/7/8, but `MXI_EXPLICIT` and
`OMEGA_LIST_1_EXPLICIT_NEW` are marchal2 material not importable here, and
the `k = 2, 3` cases again go through `YNHYJIT` (its i = 2 case is closed
by `MCELL2_PERMUTE_01` above, i = 3 open).

Status 2026-09-30: still `sorry`ed (giant).
DISCHARGES: none (feeds marchal3/KIZHLTL downstream). -/
theorem QZKSYKG2 {V : Set V3} {ul : List V3} {k : ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
    mcell k V ul ⊆
      ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1))}) := by
  -- NEEDS: giant (QZKSYKG.hl:325-2251, ~1900 HOL lines). Case status:
  -- k = 2 — the 01-swap mirror is now available (MCELL2_PERMUTE_01 above);
  -- k = 3 — blocked by LEFT_ACTION_LIST_PROPERTIES (ynhyjit_p14's i = 3
  -- NEEDS); k = 0/1 — mcell0/mcell1 coverings; k = 4 — `YIFVQDV_1` (also
  -- blocking QZKSYKG1's k = 4 case).
  sorry

end Kepler.Text

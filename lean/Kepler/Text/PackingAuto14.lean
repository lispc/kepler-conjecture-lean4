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
  matching the PA10 fix; `QZKSYKG1`/`QZKSYKG2` were frozen with the plain
  `permutes` form — at discharge time their HL proofs must
  supply the tail-fixedness from `LEFT_ACTION_LIST_PROPERTIES`.
  STATEMENT-FIX 项 20 (2026-09-30, `QZKSYKG1` 补 `hfix` 前提) / 项 38
  (2026-10-12, `QZKSYKG2` comprehension 补 `∧ ∀ n, k ≤ n → p n = n`) 已把
  两件冻结陈述先后补到 HOL-faithful 形（HL `permutes` 本为
  complement-fixing，azure/hol-light-nat/Library/permutations.ml:9）。
- `MXI_EXPLICIT` (marchal2.hl:2516): MERGED 2026-09-19 — PA12's proved
  public `MXI_EXPLICIT` is importable; the unused private `mxiExplicit_p14`
  copy was deleted (PA11 still holds its own private copy, out of scope).
- Proof status (2026-09-30 wave; 措辞降级 2026-10-14 #print axioms 核查):
  the five supporting lemmas are proved; `ynhyjit_p14` is closed for
  i = 2 (the LEFT_ACTION bridge, via the private 01-swap kit below) and
  i = 4 (contradiction); i = 3 remains `sorry`ed (the
  `LEFT_ACTION_LIST_PROPERTIES` S₃ giant). The two public named bridges
  `LEFT_ACTION_LIST_1_PROPERTIES_ALT` and `MCELL2_PERMUTE_01` are **NOT
  sorry-free**（2026-10-14 核查 axiom 面均含 sorryAx）: 二者消费
  `p14_swap_pack`，其 i = 3 情形即上述 S₃ giant `sorry`（:763）——
  "证法落地、债经 01-swap kit 上行"；the LEFT_ACTION copy carries
  the PA10-style tail-fixedness side condition, see its ENCODING-FIX note.
  `QZKSYKG1`/`QZKSYKG2` remain `sorry`ed with NEEDS accounting (statements
  now HOL-faithful via SF-20/38; k ≤ 3 is the LEFT_ACTION_LIST_PROPERTIES
  S₃ giant; k = 4 is the YIFVQDV_1 giant; ~1900 HOL lines for QZKSYKG2).
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

/-! ### Permutation kit for `RVFXZBU_p14` / `ynhyjit_i3_p14`

Private copies of the tail-fixedness toolkit owned by PackingAuto10/12
(`mem_iff_getD_p10`, `p_lt_i_iff_p10`, `p12_setOfList_trunc2_leftAction` and
the `p12_leftActionList_four_explicit` helpers), renamed `p14_`. They are
rebuilt here rather than imported because the PA10/PA12 copies are
`private`. -/

/-- A typed permutation fixing `0` and every `j ≥ 1` is the identity. -/
private theorem p14_eqRefl_of_fix {p : Equiv.Perm ℕ}
    (h0 : p 0 = 0) (hfix : ∀ j, 1 ≤ j → p j = j) : p = Equiv.refl ℕ :=
  Equiv.ext fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact h0
    · simpa using hfix j hj

/-- The identity permutation acts trivially. -/
private theorem p14_leftActionList_refl {α : Type*} [Inhabited α] (ul : List α) :
    leftActionList (Equiv.refl ℕ) ul = ul := by
  apply List.ext_get
  · simp [leftActionList]
  · intro n _ h2
    simp [leftActionList, Equiv.refl_symm, h2]

/-- A permutation weakly permuting `Icc 0 (i-1)` and fixing every `j ≥ i`
bijects the initial block `{j | j < i}`. -/
private theorem p14_permutes_lt {p : Equiv.Perm ℕ} {i : ℕ}
    (hperm : permutes p (Set.Icc 0 (i - 1))) (hfix : ∀ j, i ≤ j → p j = j) :
    permutes p {j : ℕ | j < i} := by
  intro m
  constructor
  · intro hm
    have hm' : m < i := hm
    have hi0 : i ≠ 0 := by omega
    have hmem : m ∈ Set.Icc 0 (i - 1) := ⟨Nat.zero_le _, Nat.le_sub_one_of_lt hm'⟩
    have hp := (hperm m).mp hmem
    simp only [Set.mem_Icc] at hp
    exact lt_of_le_of_lt hp.2 (Nat.sub_one_lt hi0)
  · intro hm
    have hm' : p m < i := hm
    by_cases hlt : m < i
    · exact hlt
    · exfalso
      have hfixm : p m = m := hfix m (Nat.le_of_not_lt hlt)
      rw [hfixm] at hm'
      exact hlt hm'

/-- A permutation weakly permuting `Icc 0 2` and fixing every `j ≥ 3`
bijects `{0,1,2,3}` (PA12 `p12_permutes_four`, renamed). -/
private theorem p14_permutes_four (p : Equiv.Perm ℕ) (hperm : permutes p (Set.Icc 0 2))
    (hfix : ∀ j : ℕ, 3 ≤ j → p j = j) : permutes p {i : ℕ | i < 4} := by
  intro x
  constructor
  · intro hx
    by_cases hx3 : x < 3
    · have hp := (hperm x).1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.lt_succ_iff.mp hx3⟩)
      exact Nat.lt_of_le_of_lt (Set.mem_Icc.mp hp).2 (by norm_num)
    · have hx3' : 3 ≤ x := Nat.le_of_not_lt hx3
      have hx3'' : x = 3 := le_antisymm (Nat.lt_succ_iff.mp hx) hx3'
      rw [hx3'', hfix 3 (by norm_num)]
      norm_num
  · intro hpx
    by_contra hx
    have hx4 : 4 ≤ x := Nat.le_of_not_lt hx
    rw [hfix x (le_trans (by norm_num) hx4)] at hpx
    exact absurd hpx (Nat.not_lt.mpr hx4)

/-- Under the tail-fixed hypotheses the left action only permutes the
entries of a length-`i` list, so the point set is unchanged (via the public
`SET_OF_LIST_LEFT_ACTION_LIST`). -/
private theorem p14_setOfList_leftActionList {p : Equiv.Perm ℕ} {ul : List V3} {i : ℕ}
    (hlen : ul.length = i) (hperm : permutes p (Set.Icc 0 (i - 1)))
    (hfix : ∀ j, i ≤ j → p j = j) :
    setOfList (leftActionList p ul) = setOfList ul := by
  rw [← hlen] at hperm hfix
  exact SET_OF_LIST_LEFT_ACTION_LIST ul p (p14_permutes_lt hperm hfix)

/-- The inverse of a tail-fixed permutation maps `j < 3` into `{0,1,2}`. -/
private theorem p14_symm_lt3 {p : Equiv.Perm ℕ}
    (hfix : ∀ j : ℕ, 3 ≤ j → p j = j) {j : ℕ} (hj : j < 3) : p.symm j < 3 := by
  by_contra h
  have h3 : 3 ≤ p.symm j := Nat.le_of_not_lt h
  have h4 := hfix (p.symm j) h3
  rw [Equiv.apply_symm_apply] at h4
  omega

/-- Explicit shape of the left action on a four-element list. -/
private theorem p14_leftActionList_four_explicit (p : Equiv.Perm ℕ) (u0 u1 u2 u3 : V3) :
    leftActionList p [u0, u1, u2, u3]
      = [[u0, u1, u2, u3].getD (p.symm 0) default, [u0, u1, u2, u3].getD (p.symm 1) default,
         [u0, u1, u2, u3].getD (p.symm 2) default,
         [u0, u1, u2, u3].getD (p.symm 3) default] := by
  simp only [leftActionList]
  norm_num [List.range_succ, List.range_zero]

/-- The first three entries of the acting list are drawn from `{u0,u1,u2}`. -/
private theorem p14_getD_symm_mem (p : Equiv.Perm ℕ) (u0 u1 u2 u3 : V3)
    (hfix : ∀ j : ℕ, 3 ≤ j → p j = j) {j : ℕ} (hj : j < 3) :
    [u0, u1, u2, u3].getD (p.symm j) default ∈ ({u0, u1, u2} : Set V3) := by
  have hs := p14_symm_lt3 hfix hj
  interval_cases h : p.symm j <;> simp

/-- HOL `SET_OF_LIST_TRUN2_LEFT_ACTION_LIST2`: the truncated point set of the
acting list is the same triple (PA12 private copy, renamed). -/
private theorem p14_setOfList_trunc2_leftAction (p : Equiv.Perm ℕ) (u0 u1 u2 u3 : V3)
    (hperm : permutes p (Set.Icc 0 2)) (hfix : ∀ j : ℕ, 3 ≤ j → p j = j) :
    setOfList (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3])) = {u0, u1, u2} := by
  rw [p14_leftActionList_four_explicit]
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_2
    ([u0, u1, u2, u3].getD (p.symm 0) default) ([u0, u1, u2, u3].getD (p.symm 1) default)
    ([u0, u1, u2, u3].getD (p.symm 2) default)
    ([u0, u1, u2, u3].getD (p.symm 3) default)).2]
  ext x
  simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact p14_getD_symm_mem p u0 u1 u2 u3 hfix (by norm_num)
    · exact p14_getD_symm_mem p u0 u1 u2 u3 hfix (by norm_num)
    · exact p14_getD_symm_mem p u0 u1 u2 u3 hfix (by norm_num)
  · rintro (hx | hx | hx)
    · rw [hx]
      have hp0 : p 0 < 3 := by
        have h := (hperm 0).1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, by norm_num⟩)
        exact Nat.lt_of_le_of_lt (Set.mem_Icc.mp h).2 (by norm_num)
      have e : [u0, u1, u2, u3].getD (p.symm (p 0)) default = u0 := by
        rw [Equiv.symm_apply_apply]; rfl
      interval_cases h : p 0
      · exact Or.inl e.symm
      · exact Or.inr (Or.inl e.symm)
      · exact Or.inr (Or.inr e.symm)
    · rw [hx]
      have hp1 : p 1 < 3 := by
        have h := (hperm 1).1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, by norm_num⟩)
        exact Nat.lt_of_le_of_lt (Set.mem_Icc.mp h).2 (by norm_num)
      have e : [u0, u1, u2, u3].getD (p.symm (p 1)) default = u1 := by
        rw [Equiv.symm_apply_apply]; rfl
      interval_cases h : p 1
      · exact Or.inl e.symm
      · exact Or.inr (Or.inl e.symm)
      · exact Or.inr (Or.inr e.symm)
    · rw [hx]
      have hp2 : p 2 < 3 := by
        have h := (hperm 2).1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, by norm_num⟩)
        exact Nat.lt_of_le_of_lt (Set.mem_Icc.mp h).2 (by norm_num)
      have e : [u0, u1, u2, u3].getD (p.symm (p 2)) default = u2 := by
        rw [Equiv.symm_apply_apply]; rfl
      interval_cases h : p 2
      · exact Or.inl e.symm
      · exact Or.inr (Or.inl e.symm)
      · exact Or.inr (Or.inr e.symm)

/-- `mcell 2` is invariant under the `{0,1}`-swap (the `i = 2` case of
`RVFXZBU`), via the `p14_swap_pack` 01-kit. Both branches of the `mcell2`
dispatch are handled: the branch condition only reads `hl` of point sets,
which the swap preserves. -/
private theorem p14_mcell2_swap {V : Set V3} {u0 u1 u2 u3 : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3]) :
    mcell 2 V [u1, u0, u2, u3] = mcell 2 V [u0, u1, u2, u3] := by
  rw [(MCELL_EXPLICIT 2 V [u1, u0, u2, u3]).2.2.1,
    (MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1]
  simp only [mcell2]
  rw [show hdV [u1, u0, u2, u3].tail = u0 from rfl,
    show hdV [u0, u1, u2, u3].tail = u1 from rfl,
    show hdV [u1, u0, u2, u3] = u1 from rfl,
    show hdV [u0, u1, u2, u3] = u0 from rfl]
  have hhl1 : hl (truncateSimplex 1 [u1, u0, u2, u3])
      = hl (truncateSimplex 1 [u0, u1, u2, u3]) := by
    rw [hl, hl, (TRUNCATE_SIMPLEX_EXPLICIT_1 u1 u0 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
    congr 1
    ext x
    simp [setOfList]
    tauto
  have hs4 : setOfList [u1, u0, u2, u3] = setOfList [u0, u1, u2, u3] := by
    ext x
    simp [setOfList]
    tauto
  have hhlfull : hl [u1, u0, u2, u3] = hl [u0, u1, u2, u3] := by
    rw [hl, hl, hs4]
  by_cases hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3]
  · have hcond' : hl (truncateSimplex 1 [u1, u0, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u1, u0, u2, u3] :=
      ⟨by rw [hhl1]; exact hcond.1, by rw [hhlfull]; exact hcond.2⟩
    have hhl : hl [u0, u1] < Real.sqrt 2 := by
      have h := hcond.1
      rwa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at h
    obtain ⟨-, -, -, hw3, hmxi⟩ := p14_swap_pack hs hp hb hhl hcond.2
    rw [if_pos hcond', if_pos hcond, hhl1, hmxi, hw3,
      Set.inter_comm (rconeGe u1 u0 (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2))
        (rconeGe u0 u1 (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2)),
      show ({u1, u0} : Set V3) = {u0, u1} from Set.pair_comm u1 u0]
  · have hcond' : ¬(hl (truncateSimplex 1 [u1, u0, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u1, u0, u2, u3]) := by
      rintro ⟨h1', h2'⟩
      exact hcond ⟨by rwa [hhl1] at h1', by rwa [hhlfull] at h2'⟩
    rw [if_neg hcond', if_neg hcond]

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

/-- HOL `RVFXZBU_concl` (RVFXZBU.hl:32-36), PA14 copy: permuting the first
`i` points of a `barV V 3` list by `p` leaves the cell `mcell i` unchanged.

This is the B2 landing of the AJRIPQN lane: the PA10 source (`RVFXZBU`,
PackingAuto10:413) proves `i = 0, 1, 2, 4` and leaves `i = 3` open behind
the missing S₃ kit. Here the whole statement is proved; the `i = 3` case is
closed by the public B1 kit `LEFT_ACTION_LIST_PROPERTIES` (PackingAuto12),
which supplies `mxi` invariance and the truncated point set is compared by
the private `p14_setOfList_trunc2_leftAction` (the HOL
`SET_OF_LIST_TRUN2_LEFT_ACTION_LIST2` copy). The other cases copy the PA10
proof structure with the PA10 private helpers rebuilt as `p14_` copies.

-- ENCODING-FIX 2026-09-17 (inherited from PA10): the tail-fixedness
hypothesis is the faithful HOL `permutes` (complement-fixing) content; the
weak pointwise `permutes` alone makes the statement false at `i = 2` (a
transposition of `2,3` weakly permutes `Icc 0 1` yet changes `hl ul`, hence
`mcell4`).

DISCHARGES: none (the Auto2 interface `RVFXZBU3_concl` is the all-`i` twin
with a different shape, owned elsewhere). -/
theorem RVFXZBU_p14 {V : Set V3} {ul : List V3} {i : ℕ} {p : Equiv.Perm ℕ}
    (hi : i ∈ ({0, 1, 2, 3, 4} : Set ℕ))
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hperm : permutes p (Set.Icc 0 (i - 1)))
    (hfix : ∀ j, i ≤ j → p j = j) :
    mcell i V (leftActionList p ul) = mcell i V ul := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · -- i = 0: hfix forces p = refl
    have hp : p = Equiv.refl ℕ :=
      p14_eqRefl_of_fix (hfix 0 (Nat.zero_le 0))
        (fun j hj => hfix j (by omega))
    subst hp
    rw [p14_leftActionList_refl]
  · -- i = 1: hperm forces p 0 = 0, hfix the tail, so p = refl
    have h0 : p 0 = 0 := by
      have hin : (0:ℕ) ∈ Set.Icc 0 (1 - 1) := Set.mem_Icc.2 (by omega)
      have hp0 := (hperm 0).mp hin
      simp only [Set.mem_Icc] at hp0
      omega
    have hp : p = Equiv.refl ℕ := p14_eqRefl_of_fix h0 hfix
    subst hp
    rw [p14_leftActionList_refl]
  · -- i = 2: p is the identity or the {0,1}-swap; mcell2 is swap-invariant
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
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
      rw [p14_leftActionList_refl01 u0 u1 u2 u3 p h0 hp1 hfix]
    · -- p swaps 0 and 1: leftActionList p ul = [u1, u0, u2, u3]
      have hp1 : p 1 = 0 := by
        have hp1m : p 1 ∈ Set.Icc 0 (2 - 1) := (hperm 1).mp (by simp [Set.mem_Icc])
        simp only [Set.mem_Icc] at hp1m
        rcases Nat.eq_zero_or_pos (p 1) with hz | hp
        · exact hz
        · have h11 : p 1 = 1 := by omega
          exact absurd (Equiv.injective p (h11.trans h0.symm)) (by decide)
      rw [p14_leftActionList_swap01 u0 u1 u2 u3 p h0 hp1 hfix]
      exact p14_mcell2_swap hsat hpack hbar
  · -- i = 3: the S₃-action case, closed by the B1 kit
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    have hperm2 : permutes p (Set.Icc 0 2) := hperm
    have hsetFull : setOfList (leftActionList p [u0, u1, u2, u3])
        = setOfList [u0, u1, u2, u3] :=
      SET_OF_LIST_LEFT_ACTION_LIST [u0, u1, u2, u3] p
        (p14_permutes_four p hperm2 hfix)
    have hsetTr2 : setOfList (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3]))
        = setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by
      rw [p14_setOfList_trunc2_leftAction p u0 u1 u2 u3 hperm2 hfix,
        (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
      ext x; simp [setOfList]
    have hhl2 : hl (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3]))
        = hl (truncateSimplex 2 [u0, u1, u2, u3]) := by
      rw [hl, hl, hsetTr2]
    have hhlfull : hl (leftActionList p [u0, u1, u2, u3]) = hl [u0, u1, u2, u3] := by
      rw [hl, hl, hsetFull]
    rw [(MCELL_EXPLICIT 3 V (leftActionList p [u0, u1, u2, u3])).2.2.2.1,
      (MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1]
    simp only [mcell3]
    by_cases hcond : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3]
    · have hcond' : hl (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3]))
          < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl (leftActionList p [u0, u1, u2, u3]) :=
        ⟨by rw [hhl2]; exact hcond.1, by rw [hhlfull]; exact hcond.2⟩
      rw [if_pos hcond', if_pos hcond]
      obtain ⟨-, -, -, hmxi⟩ :=
        LEFT_ACTION_LIST_PROPERTIES hpack hsat hbar hcond.1 hcond.2 hperm2 hfix rfl
      rw [hsetTr2, hmxi]
    · have hcond' : ¬(hl (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3]))
          < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl (leftActionList p [u0, u1, u2, u3])) := by
        rintro ⟨h1', h2'⟩
        exact hcond ⟨by rwa [hhl2] at h1', by rwa [hhlfull] at h2'⟩
      rw [if_neg hcond', if_neg hcond]
  · -- i = 4: mcell4 depends only on setOfList and hl
    have h4 : ul.length = 3 + 1 := hbar.1
    have hlen : ul.length = 4 := by omega
    have hset := p14_setOfList_leftActionList hlen hperm hfix
    have hhl : hl (leftActionList p ul) = hl ul := by rw [hl, hl, hset]
    have hL : mcell 4 V (leftActionList p ul) = mcell4 V (leftActionList p ul) := by
      rw [mcell, if_neg (show (4:ℕ) ≠ 0 by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    have hR : mcell 4 V ul = mcell4 V ul := by
      rw [mcell, if_neg (show (4:ℕ) ≠ 0 by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    rw [hL, hR, mcell4, mcell4, hhl, hset]

/-- HOL `YNHYJIT_concl` (YNHYJIT.hl:33-40), `i = 3` specialization: in the
small-truncation regime the left action of a permutation of `0..2` fixing
the tail preserves `barV V 3` and the omega points at levels `2, 3`.

This is the B2 landing: it is a direct projection of the B1 kit
`LEFT_ACTION_LIST_PROPERTIES` (its `barV`/`ω₂`/`ω₃` conjuncts); `h2` is
retained in the frozen statement but not consumed. The general PA10
`YNHYJIT` still has its `i = 2` case open (owned elsewhere); this landing
covers exactly the `i = 3` instance needed downstream. -/
theorem ynhyjit_i3_p14 {V : Set V3} {ul vl : List V3} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (h1 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (h2 : Real.sqrt 2 ≤ hl ul)
    (hperm : permutes p (Set.Icc 0 2))
    (hfix : ∀ j : ℕ, 3 ≤ j → p j = j)
    (hvl : vl = leftActionList p ul) :
    barV V 3 vl ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ 3 → omegaListN V vl j = omegaListN V ul j := by
  subst hvl
  obtain ⟨hbarV, hω2, hω3, -⟩ :=
    LEFT_ACTION_LIST_PROPERTIES hpack hsat hbar h1 h2 hperm hfix rfl
  refine ⟨hbarV, fun j hj1 hj2 => ?_⟩
  interval_cases j
  · exact hω2
  · exact hω3

/-! ## QZKSYKG2 `k = 2`: the two-Rogers cover (B5b/B5c/B5d)

The HOL proof (`QZKSYKG.hl:325-2251`) reduces `mcell2` to the lens cut out by
the two mutual `rcone_ge`s at `a = hl (truncate_simplex 1 ul) / sqrt 2` and
the wedge towards `mxi`/`omega_3`, then proves the lens sits in
`convex hull {u0,u1,omega_2,omega_3}` and that this tetrahedron is covered by
`rogers V ul ∪ rogers V [u1,u0,u2,u3]`.  The private lemmas below formalize
that route; the key algebraic observation is that the two cone inequalities
bound the coefficients of the `aff_ge` representation in terms of
`|z - omega_1|`, and the Voronoi projection gives
`|z - omega_1| ≥ sqrt (2 - hl [u0,u1]^2)`. -/

/-- Membership in `voronoiList V wl` gives equidistance from any two list
points. -/
private theorem p14_dist_eq_of_voronoiList {V : Set V3} {wl : List V3} {p u0 u1 : V3}
    (hp : p ∈ voronoiList V wl) (h0 : u0 ∈ setOfList wl) (h1 : u1 ∈ setOfList wl)
    (hu0V : u0 ∈ V) (hu1V : u1 ∈ V) : dist p u0 = dist p u1 := by
  rw [voronoiList, voronoiSet, Set.mem_sInter] at hp
  have h0' : p ∈ voronoiClosed V u0 := hp _ (Set.mem_setOf.2 ⟨u0, h0, rfl⟩)
  have h1' : p ∈ voronoiClosed V u1 := hp _ (Set.mem_setOf.2 ⟨u1, h1, rfl⟩)
  exact le_antisymm (h0' u1 hu1V) (h1' u0 hu0V)

/-- The closest point is a distance minimizer (minimality half). -/
private theorem p14_closestPoint_le {K : Set V3} {x : V3} (hne : K.Nonempty)
    (hc : IsClosed K) : ∀ z ∈ K, dist x (closestPoint K x) ≤ dist x z := by
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
    (p := fun w : V3 => w ∈ K ∧ ∀ z ∈ K, dist x w ≤ dist x z) hsat).2

/-- Variational inequality for the closest point of a convex closed set. -/
private theorem p14_closestPoint_inner_le {K : Set V3} {x : V3} (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hc : IsClosed K) :
    ∀ z ∈ K, (x - closestPoint K x) ⬝ᵥ (z - closestPoint K x) ≤ 0 := by
  haveI : Nonempty K := hne.to_subtype
  have hmem : closestPoint K x ∈ K := p14_closestPoint_mem hne hc
  have hmin' : ∀ z ∈ K, ‖x - closestPoint K x‖ ≤ ‖x - z‖ := by
    intro z hz
    have h := p14_closestPoint_le (x := x) hne hc z hz
    rwa [dist_eq_norm, dist_eq_norm] at h
  have hiInf : ‖x - closestPoint K x‖ = ⨅ w : K, ‖x - (w : V3)‖ := by
    refine le_antisymm ?_ ?_
    · exact le_ciInf fun w => hmin' w w.2
    · have hbdd : BddBelow (Set.range fun w : K => ‖x - (w : V3)‖) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hbdd ⟨closestPoint K x, hmem⟩
  have h := (norm_eq_iInf_iff_real_inner_le_zero hconv hmem).1 hiInf
  intro z hz
  have hz' := h z hz
  rw [inner_eq_dot] at hz'
  exact hz'

/-- Median formula on the triangle `(u0, u1, m)`: equality version. -/
private theorem p14_median_eq {u0 u1 m s1 : V3} (hs1 : s1 = midpoint ℝ u0 u1)
    (h0 : dist m u0 = Real.sqrt 2) (h1 : dist m u1 = Real.sqrt 2)
    (hd : dist u0 u1 = 2 * h) :
    ‖m - s1‖ ^ 2 = 2 - h ^ 2 := by
  have hm0 : ‖m - u0‖ = Real.sqrt 2 := by
    rw [← dist_eq_norm]; exact h0
  have hm1 : ‖m - u1‖ = Real.sqrt 2 := by
    rw [← dist_eq_norm]; exact h1
  have hdu : ‖u1 - u0‖ = 2 * h := by
    rw [← dist_eq_norm, dist_comm]; exact hd
  have hpar := parallelogram_law_with_norm ℝ (m - u0) (m - u1)
  have ha : (m - u0) + (m - u1) = (2:ℝ) • (m - s1) := by
    rw [hs1, midpoint_eq_smul_add]
    norm_num
    module
  have hb : (m - u0) - (m - u1) = u1 - u0 := by abel
  rw [ha, hb, hdu, hm0, hm1] at hpar
  rw [norm_smul, Real.norm_ofNat] at hpar
  rw [Real.sq_sqrt (by norm_num)] at hpar
  nlinarith

/-- Median formula on the triangle `(u0, u1, m)`: inequality version. -/
private theorem p14_median_ge {u0 u1 m s1 : V3} (hs1 : s1 = midpoint ℝ u0 u1)
    (h0 : Real.sqrt 2 ≤ dist m u0) (h1 : Real.sqrt 2 ≤ dist m u1)
    (hd : dist u0 u1 = 2 * h) :
    2 - h ^ 2 ≤ ‖m - s1‖ ^ 2 := by
  have hm0 : Real.sqrt 2 ≤ ‖m - u0‖ := by
    rw [← dist_eq_norm]; exact h0
  have hm1 : Real.sqrt 2 ≤ ‖m - u1‖ := by
    rw [← dist_eq_norm]; exact h1
  have hdu : ‖u1 - u0‖ = 2 * h := by
    rw [← dist_eq_norm, dist_comm]; exact hd
  have hpar := parallelogram_law_with_norm ℝ (m - u0) (m - u1)
  have ha : (m - u0) + (m - u1) = (2:ℝ) • (m - s1) := by
    rw [hs1, midpoint_eq_smul_add]
    norm_num
    module
  have hb : (m - u0) - (m - u1) = u1 - u0 := by abel
  rw [ha, hb, hdu] at hpar
  rw [norm_smul, Real.norm_ofNat] at hpar
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : (0:ℝ) ≤ Real.sqrt 2 := le_of_lt (Real.sqrt_pos.2 (by norm_num))
  have h0' : 2 ≤ ‖m - u0‖ ^ 2 := by
    have := mul_self_le_mul_self hspos hm0
    nlinarith [hsq]
  have h1' : 2 ≤ ‖m - u1‖ ^ 2 := by
    have := mul_self_le_mul_self hspos hm1
    nlinarith [hsq]
  nlinarith

/-- The norm from `x` is monotone along the ray `s2 + t (s3 - s2)` under the
variational inequality at `s2`. -/
private theorem p14_norm_mono_segment {x s2 s3 : V3}
    (hvar : (x - s2) ⬝ᵥ (s3 - s2) ≤ 0) {μ ν : ℝ}
    (hμ0 : 0 ≤ μ) (hμν : μ ≤ ν) :
    ‖x - (s2 + μ • (s3 - s2))‖ ≤ ‖x - (s2 + ν • (s3 - s2))‖ := by
  have e1 : x - (s2 + μ • (s3 - s2)) = (x - s2) - μ • (s3 - s2) := by abel
  have e2 : x - (s2 + ν • (s3 - s2)) = (x - s2) - ν • (s3 - s2) := by abel
  rw [e1, e2]
  have hsq : ‖(x - s2) - μ • (s3 - s2)‖ ^ 2 ≤
      ‖(x - s2) - ν • (s3 - s2)‖ ^ 2 := by
    have h1 := norm_sub_sq_real (x - s2) (μ • (s3 - s2))
    have h2 := norm_sub_sq_real (x - s2) (ν • (s3 - s2))
    rw [h1, h2]
    have hi : ∀ r : ℝ, inner ℝ (x - s2) (r • (s3 - s2))
        = r * ((x - s2) ⬝ᵥ (s3 - s2)) := by
      intro r
      rw [real_inner_smul_right, inner_eq_dot]
      simp only [WithLp.ofLp_sub]
    rw [hi μ, hi ν, norm_smul, norm_smul]
    have h1' : (‖μ‖ * ‖s3 - s2‖) ^ 2 = μ ^ 2 * ‖s3 - s2‖ ^ 2 := by
      rw [mul_pow, Real.norm_eq_abs, sq_abs]
    have h2' : (‖ν‖ * ‖s3 - s2‖) ^ 2 = ν ^ 2 * ‖s3 - s2‖ ^ 2 := by
      rw [mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1', h2']
    have hfac : ν ^ 2 - μ ^ 2 = (ν - μ) * (ν + μ) := by ring
    have h1 : 0 ≤ (ν - μ) * (-2 * ((x - s2) ⬝ᵥ (s3 - s2))) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (ν - μ) * (ν + μ) * ‖s3 - s2‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
    nlinarith [hfac]
  have h1 : 0 ≤ ‖(x - s2) - μ • (s3 - s2)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖(x - s2) - ν • (s3 - s2)‖ := norm_nonneg _
  rw [sq_le_sq, abs_of_nonneg h1, abs_of_nonneg h2] at hsq
  exact hsq

/-- Coefficient bound at one endpoint: the `rcone_ge` inequality at `u0`
forces the `u1`-coefficient of the `aff_ge` representation to be nonnegative,
using `|z - s1| ≥ sqrt (2 - h^2)`. -/
private theorem p14_rcone_coeff {u0 u1 s1 z x : V3} {t1 t2 t5 h : ℝ}
    (hs1 : s1 = midpoint ℝ u0 u1)
    (hh : h = ‖s1 - u0‖) (hhpos : 0 < h) (hhlt : h ^ 2 < 2)
    (horth : (z - s1) ⬝ᵥ (u1 - u0) = 0)
    (hsum : t1 + t2 + t5 = 1) (ht5 : 0 ≤ t5)
    (hx : x = t1 • u0 + t2 • u1 + t5 • z)
    (hcone : (x - u0) ⬝ᵥ (u1 - u0) ≥
      ‖x - u0‖ * ‖u1 - u0‖ * (h / Real.sqrt 2))
    (hw : 2 - h ^ 2 ≤ ‖z - s1‖ ^ 2) :
    0 ≤ t2 := by
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num)
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have ht1 : t1 = 1 - t2 - t5 := by linarith
  have hmid : s1 = (1/2 : ℝ) • (u0 + u1) := by
    rw [hs1, midpoint_eq_smul_add]
    norm_num
  have he : u1 - u0 = (2:ℝ) • (s1 - u0) := by
    rw [hmid]
    module
  have hen : ‖u1 - u0‖ = 2 * h := by
    rw [he, norm_smul, hh, Real.norm_ofNat]
  have hxde : x - u0 =
      ((2 * t2 + t5) / 2) • (u1 - u0) + t5 • (z - s1) := by
    rw [hx, ht1, hmid]
    module
  have hdot : (x - u0) ⬝ᵥ (u1 - u0) =
      ((2 * t2 + t5) / 2) * ‖u1 - u0‖ ^ 2 := by
    rw [hxde]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul]
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, horth]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rw [p14_norm_sq_dot (u1 - u0)]
    simp only [WithLp.ofLp_sub]
  have hcone' : ((2 * t2 + t5) / 2) * ‖u1 - u0‖ ^ 2 ≥
      ‖x - u0‖ * ‖u1 - u0‖ * (h / Real.sqrt 2) := by
    rwa [← hdot]
  set B : ℝ := 2 * t2 + t5 with hBdef
  have hconeB : ‖x - u0‖ * 2 * h ^ 2 / Real.sqrt 2 ≤ 2 * B * h ^ 2 := by
    have hdiv : 2 * h * (h / Real.sqrt 2) = 2 * h ^ 2 / Real.sqrt 2 := by
      field_simp
    have := hcone'
    rw [hen] at this
    calc ‖x - u0‖ * 2 * h ^ 2 / Real.sqrt 2
        = ‖x - u0‖ * (2 * h) * (h / Real.sqrt 2) := by ring_nf
      _ ≤ B / 2 * (2 * h) ^ 2 := this
      _ = 2 * B * h ^ 2 := by ring
  have hB0 : 0 ≤ B := by
    have hrhs : 0 ≤ ‖x - u0‖ * 2 * h ^ 2 / Real.sqrt 2 :=
      div_nonneg (by positivity) hsqrt2pos.le
    have h2h : 0 < 2 * h ^ 2 := by nlinarith [hhpos]
    have hprod : 0 ≤ 2 * B * h ^ 2 := le_trans hrhs hconeB
    nlinarith [hprod, h2h]
  have hxub : ‖x - u0‖ ≤ Real.sqrt 2 * B := by
    have hmul : ‖x - u0‖ * (2 * h ^ 2) ≤ (Real.sqrt 2 * B) * (2 * h ^ 2) := by
      have hm := mul_le_mul_of_nonneg_right hconeB hsqrt2pos.le
      have hleft : (‖x - u0‖ * 2 * h ^ 2 / Real.sqrt 2) * Real.sqrt 2
          = ‖x - u0‖ * 2 * h ^ 2 := by
        field_simp
      have hright : (2 * B * h ^ 2) * Real.sqrt 2
          = (Real.sqrt 2 * B) * (2 * h ^ 2) := by ring
      rw [hleft, hright] at hm
      nlinarith [hm]
    exact le_of_mul_le_mul_right hmul (by nlinarith [hhpos])
  have horth' : (u1 - u0) ⬝ᵥ (z - s1) = 0 := by
    rw [dotProduct_comm]
    exact horth
  have hpyth' : ((B / 2) • (u1 - u0)) ⬝ᵥ (t5 • (z - s1)) = 0 := by
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sub]
    rw [smul_dotProduct, dotProduct_smul]
    simp only [WithLp.ofLp_sub] at horth' ⊢
    rw [horth']
    simp
  have hnsq : ‖x - u0‖ ^ 2 = B ^ 2 * h ^ 2 + t5 ^ 2 * ‖z - s1‖ ^ 2 := by
    rw [hxde]
    have hzero : inner ℝ ((B / 2) • (u1 - u0)) (t5 • (z - s1)) = 0 := by
      rw [inner_eq_dot]
      simpa only [WithLp.ofLp_smul, WithLp.ofLp_sub] using hpyth'
    rw [norm_add_sq_real, hzero, norm_smul, norm_smul, hen, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have e1 : (|B / 2| * (2 * h)) ^ 2 = B ^ 2 * h ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    have e2 : (|t5| * ‖z - s1‖) ^ 2 = t5 ^ 2 * ‖z - s1‖ ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [e1, e2]
    ring
  have hupper : ‖x - u0‖ ^ 2 ≤ 2 * B ^ 2 := by
    have hxl : 0 ≤ ‖x - u0‖ := norm_nonneg _
    have hsB : 0 ≤ Real.sqrt 2 * B := mul_nonneg hsqrt2pos.le hB0
    have hs := mul_self_le_mul_self hxl hxub
    nlinarith [hs, hsqrt2]
  have hkey : t5 ^ 2 * (2 - h ^ 2) ≤ B ^ 2 * (2 - h ^ 2) := by
    have h1 : t5 ^ 2 * (2 - h ^ 2) ≤ t5 ^ 2 * ‖z - s1‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hw (sq_nonneg t5)
    nlinarith [hnsq, hupper, h1]
  have hpos : 0 < 2 - h ^ 2 := by linarith
  have hsq : t5 ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_right hkey hpos
  have ht5le : t5 ≤ B := by
    nlinarith [hsq, ht5, hB0]
  linarith

/-- Orthogonality of a point of `voronoiList V [u0,u1]` to the edge: the
median from the circumcenter is perpendicular to the edge. -/
private theorem p14_orth_of_voronoi {V : Set V3} {u0 u1 z s1 : V3}
    (hs1 : s1 = midpoint ℝ u0 u1) (hb1 : barV V 1 [u0, u1]) (hp : Packing V)
    (hz : z ∈ voronoiList V [u0, u1]) :
    (z - s1) ⬝ᵥ (u1 - u0) = 0 := by
  have hz_aff : z ∈ (affineSpan ℝ (voronoiList V [u0, u1]) : Set V3) :=
    subset_affineSpan ℝ _ hz
  have hu0_aff : u0 ∈ (affineSpan ℝ (setOfList [u0, u1]) : Set V3) :=
    subset_affineSpan ℝ _ (by simp [setOfList])
  have hcc := MHFTTZN4 V [u0, u1] 1 z u0 hp hb1 hz_aff hu0_aff
  have hsetpair : setOfList [u0, u1] = ({u0, u1} : Set V3) := by
    ext y; simp [setOfList]
  rw [hsetpair, CIRCUMCENTER_2, ← hs1] at hcc
  have hmid : (u0 : V3) - s1 = (1/2 : ℝ) • (u0 - u1) := by
    rw [hs1, midpoint_eq_smul_add]
    norm_num
    module
  have hmidc : (u0 : Fin 3 → ℝ) - s1.ofLp
      = (1/2 : ℝ) • ((u0 : Fin 3 → ℝ) - u1.ofLp) := by
    have h := congrArg (fun v : V3 => (v : Fin 3 → ℝ)) hmid
    simpa only [WithLp.ofLp_sub, WithLp.ofLp_smul] using h
  rw [hmidc, dotProduct_smul] at hcc
  have h3 : (z - s1).ofLp ⬝ᵥ ((u0 : Fin 3 → ℝ) - u1.ofLp) = 0 := by
    rcases smul_eq_zero.mp hcc with h | h
    · norm_num at h
    · exact h
  have hneg : (u1 : Fin 3 → ℝ) - u0.ofLp
      = -((u0 : Fin 3 → ℝ) - u1.ofLp) := by abel
  rw [hneg, dotProduct_neg, h3, neg_zero]

/-- `mcell2` is covered by the two Rogers simplices of the identity and the
`{0,1}`-swap (QZKSYKG.hl:325-2251, `k = 2` case). -/
private theorem mcell2_subset_rogers_pair {V : Set V3}
    {u0 u1 u2 u3 s1 s2 s3 m : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3])
    (hs1eq : s1 = omegaListN V [u0, u1, u2, u3] 1)
    (hs2eq : s2 = omegaListN V [u0, u1, u2, u3] 2)
    (hs3eq : s3 = omegaListN V [u0, u1, u2, u3] 3)
    (hmeq : m = mxi V [u0, u1, u2, u3]) :
    mcell2 V [u0, u1, u2, u3] ⊆
      rogers V [u0, u1, u2, u3] ∪ rogers V [u1, u0, u2, u3] := by
  intro x hx
  have htr1 : truncateSimplex 1 [u0, u1, u2, u3] = [u0, u1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2
  have htr2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hhl : hl [u0, u1] < Real.sqrt 2 := by
    rw [← htr1]
    exact hcond.1
  have hsq : Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := hcond.2
  obtain ⟨hu0V, hu1V, hu2V, hu3V⟩ := p14_mem_V_of_barV hb
  have hb1 : barV V 1 [u0, u1] := by
    have h := TRUNCATE_SIMPLEX_BARV V 1 3 [u0, u1, u2, u3] hb (by omega)
    rwa [htr1] at h
  have hb2 : barV V 2 [u0, u1, u2] := by
    have h := TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
    rwa [htr2] at h
  have hhpos : 0 < hl [u0, u1] := by
    have h := BARV_IMP_HL_1_POS_LT V [u0, u1, u2, u3] hs hp hb
    rwa [htr1] at h
  have hhlt : (hl [u0, u1]) ^ 2 < 2 := by
    have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hspos := Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)
    have hmul := mul_pos (sub_pos.mpr hhl) (by linarith : 0 < Real.sqrt 2 + hl [u0, u1])
    nlinarith
  have hs1c : s1 = circumcenter ({u0, u1} : Set V3) := by
    rw [hs1eq]
    exact OMEGA_LIST_1_EXPLICIT_NEW u0 u1 u2 u3 V [u0, u1, u2, u3] hs hp hb rfl hhl
  have hs1m : s1 = midpoint ℝ u0 u1 := by
    rw [hs1c, CIRCUMCENTER_2]
  have hh : hl [u0, u1] = ‖s1 - u0‖ := by
    have hd := HL_EQ_DIST0 V 1 [u0, u1] hp hb1
    have hsetpair : setOfList [u0, u1] = ({u0, u1} : Set V3) := by
      ext y; simp [setOfList]
    rw [hsetpair, CIRCUMCENTER_2, ← hs1m] at hd
    rw [hd, dist_eq_norm]
    simp [hdV]
  have hd2 : dist u0 u1 = 2 * hl [u0, u1] := by
    have h := dist_midpoint_left (𝕜 := ℝ) u0 u1
    rw [← hs1m, Real.norm_ofNat] at h
    have hdist : dist s1 u0 = hl [u0, u1] := by rw [dist_eq_norm, ← hh]
    rw [hdist] at h
    norm_num at h
    linarith
  have hu01 : u0 ≠ u1 := by
    intro e
    have h := hd2
    rw [e, dist_self] at h
    have hp' : 0 < hl [u1, u1] := by simpa [e] using hhpos
    linarith
  have hposdist : 0 < dist u0 u1 := by rw [hd2]; linarith
  have hs2K : s2 ∈ voronoiList V [u0, u1, u2] := by
    rw [hs2eq]
    have h := OMEGA_LIST_N_IN_VORONOI_LIST_GEN V [u0, u1, u2, u3] 3 2 2 hp hs hb le_rfl (by norm_num)
    rwa [htr2] at h
  have hs3K : s3 ∈ voronoiList V [u0, u1, u2] := by
    rw [hs3eq]
    have h := OMEGA_LIST_N_IN_VORONOI_LIST_GEN V [u0, u1, u2, u3] 3 2 3 hp hs hb (by norm_num) (by norm_num)
    rwa [htr2] at h
  have hs2K1 : s2 ∈ voronoiList V [u0, u1] := by
    rw [hs2eq]
    have h := OMEGA_LIST_N_IN_VORONOI_LIST_GEN V [u0, u1, u2, u3] 3 1 2 hp hs hb (by norm_num) (by norm_num)
    rwa [htr1] at h
  have hs3K1 : s3 ∈ voronoiList V [u0, u1] := by
    rw [hs3eq]
    have h := OMEGA_LIST_N_IN_VORONOI_LIST_GEN V [u0, u1, u2, u3] 3 1 3 hp hs hb (by norm_num) (by norm_num)
    rwa [htr1] at h
  have hmsegS23 : m ∈ segment ℝ s2 s3 := by
    by_cases h2 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2
    · obtain ⟨s, hseg, hdist, hms⟩ :=
        MXI_EXPLICIT V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl h2 hsq
      rw [hmeq, ← hms]
      simpa only [← hs2eq, ← hs3eq] using hseg
    · have hge : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3]) := not_lt.mp h2
      have hm : m = s2 := by
        rw [hmeq, mxi, if_pos hge, ← hs2eq]
      rw [hm]
      exact left_mem_segment ℝ s2 s3
  have hmK1 : m ∈ voronoiList V [u0, u1] := by
    by_cases h2 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2
    · exact (CONVEX_VORONOI_LIST V [u0, u1]).segment_subset hs2K1 hs3K1 hmsegS23
    · have hge : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3]) := not_lt.mp h2
      have hm : m = s2 := by
        rw [hmeq, mxi, if_pos hge, ← hs2eq]
      rw [hm]
      exact hs2K1
  have hw_m : 2 - (hl [u0, u1]) ^ 2 ≤ ‖m - s1‖ ^ 2 := by
    by_cases h2 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2
    · obtain ⟨s, hseg, hdist, hms⟩ :=
        MXI_EXPLICIT V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl h2 hsq
      have hmd : dist m u0 = Real.sqrt 2 := by
        rw [hmeq, ← hms]
        have hdVu : hdV [u0, u1, u2, u3] = u0 := rfl
        rw [hdVu, dist_comm] at hdist
        exact hdist
      have hmu1 : dist m u1 = dist m u0 :=
        (p14_dist_eq_of_voronoiList (V := V) (wl := [u0, u1]) (p := m)
          (u0 := u0) (u1 := u1) hmK1
          (by simp [setOfList]) (by simp [setOfList]) hu0V hu1V).symm
      rw [hmd] at hmu1
      exact (p14_median_eq (h := hl [u0, u1]) hs1m hmd hmu1 hd2).ge
    · have hge : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3]) := not_lt.mp h2
      have hge2 : Real.sqrt 2 ≤ hl [u0, u1, u2] := by rwa [← htr2]
      have hm : m = s2 := by
        rw [hmeq, mxi, if_pos hge, ← hs2eq]
      have hom : omegaList V [u0, u1, u2] = s2 := by
        rw [← OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3, ← hs2eq]
      have hw1 := WAUFCHE1 V [u0, u1, u2] 2 hp hb2
      rw [hom, show hdV [u0, u1, u2] = u0 from rfl] at hw1
      have hdu0 : Real.sqrt 2 ≤ dist s2 u0 := le_trans hge2 hw1
      have hdu1 : dist s2 u1 = dist s2 u0 :=
        (p14_dist_eq_of_voronoiList (V := V) (wl := [u0, u1]) (p := s2) (u0 := u0) (u1 := u1) hs2K1 (by simp [setOfList]) (by simp [setOfList]) hu0V hu1V).symm
      rw [hm]
      exact p14_median_ge (h := hl [u0, u1]) hs1m hdu0 (by rwa [hdu1]) hd2
  have hconvK : Convex ℝ (voronoiList V [u0, u1, u2]) := CONVEX_VORONOI_LIST V _
  have hclosedK : IsClosed (voronoiList V [u0, u1, u2]) := CLOSED_VORONOI_LIST V _
  have hneK : (voronoiList V [u0, u1, u2]).Nonempty := ⟨s2, hs2K⟩
  have hs2cp : s2 = closestPoint (voronoiList V [u0, u1, u2]) s1 := by
    rw [hs2eq, hs1eq]
    show closestPoint (voronoiList V (truncateSimplex 2 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 1) =
      closestPoint (voronoiList V [u0, u1, u2]) (omegaListN V [u0, u1, u2, u3] 1)
    rw [htr2]
  have hvar : (s1 - s2) ⬝ᵥ (s3 - s2) ≤ 0 := by
    have h := p14_closestPoint_inner_le (x := s1) hconvK hneK hclosedK s3 hs3K
    rwa [← hs2cp] at h
  rw [mcell2, if_pos hcond] at hx
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
  obtain ⟨⟨hxr0, hxr1⟩, hxaff⟩ := hx
  have hxr0' : (x - u0) ⬝ᵥ (u1 - u0) ≥
      dist x u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2) := by
    have h := hxr0
    rw [rconeGe, Set.mem_setOf_eq] at h
    simpa [hdV, htr1] using h
  have hxr1' : (x - u1) ⬝ᵥ (u0 - u1) ≥
      dist x u1 * dist u0 u1 * (hl [u0, u1] / Real.sqrt 2) := by
    have h := hxr1
    rw [rconeGe, Set.mem_setOf_eq] at h
    simpa [hdV, htr1] using h
  have hxaff' : x ∈ affGe ({u0, u1} : Set V3) ({m, s3} : Set V3) := by
    simpa [hdV, ← hmeq, ← hs3eq] using hxaff
  have hmne0 : m ≠ u0 := by
    intro e
    have h := p14_dist_eq_of_voronoiList (V := V) (wl := [u0, u1]) (p := m) (u0 := u0) (u1 := u1) hmK1 (by simp [setOfList]) (by simp [setOfList]) hu0V hu1V
    rw [e, dist_self] at h
    linarith [hposdist]
  have hmne1 : m ≠ u1 := by
    intro e
    have h := p14_dist_eq_of_voronoiList (V := V) (wl := [u0, u1]) (p := m) (u0 := u0) (u1 := u1) hmK1 (by simp [setOfList]) (by simp [setOfList]) hu0V hu1V
    rw [e, dist_self, dist_comm] at h
    linarith [hposdist]
  have hs3ne0 : s3 ≠ u0 := by
    intro e
    have h := p14_dist_eq_of_voronoiList (V := V) (wl := [u0, u1]) (p := s3) (u0 := u0) (u1 := u1) hs3K1 (by simp [setOfList]) (by simp [setOfList]) hu0V hu1V
    rw [e, dist_self] at h
    linarith [hposdist]
  have hs3ne1 : s3 ≠ u1 := by
    intro e
    have h := p14_dist_eq_of_voronoiList (V := V) (wl := [u0, u1]) (p := s3) (u0 := u0) (u1 := u1) hs3K1 (by simp [setOfList]) (by simp [setOfList]) hu0V hu1V
    rw [e, dist_self, dist_comm] at h
    linarith [hposdist]
  have hdis : Disjoint ({u0, u1} : Set V3) ({m, s3} : Set V3) := by
    rw [Set.disjoint_left]
    intro a ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ha with rfl | rfl
    · intro h
      rcases h with h | h
      · exact hmne0 h.symm
      · exact hs3ne0 h.symm
    · intro h
      rcases h with h | h
      · exact hmne1 h.symm
      · exact hs3ne1 h.symm
  obtain ⟨t1, t2, t3, t4, ht3, ht4, hsum, hxrep⟩ := by
    have := hxaff'
    rw [AFF_GE_2_2 u0 u1 m s3 hdis] at this
    simpa only [Set.mem_setOf_eq] using this
  have hsum5 : t1 + t2 + (t3 + t4) = 1 := by linarith
  have ht5nonneg : 0 ≤ t3 + t4 := add_nonneg ht3 ht4
  obtain ⟨z, hxrep_z, hzsegS23, hw_z⟩ : ∃ z : V3,
      x = t1 • u0 + t2 • u1 + (t3 + t4) • z ∧
      z ∈ segment ℝ s2 s3 ∧
      2 - (hl [u0, u1]) ^ 2 ≤ ‖z - s1‖ ^ 2 := by
    by_cases ht5z : t3 + t4 = 0
    · have ht3z : t3 = 0 := by linarith
      have ht4z : t4 = 0 := by linarith
      refine ⟨m, ?_, hmsegS23, hw_m⟩
      rw [hxrep, ht3z, ht4z]
      simp
    · have ht5pos : 0 < t3 + t4 := lt_of_le_of_ne ht5nonneg (Ne.symm ht5z)
      have hzseg_m : (t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3
          ∈ segment ℝ m s3 := by
        refine ⟨t3 / (t3 + t4), t4 / (t3 + t4), div_nonneg ht3 ht5pos.le,
          div_nonneg ht4 ht5pos.le, ?_, rfl⟩
        field_simp
      have hzsegS23' : (t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3
          ∈ segment ℝ s2 s3 := by
        obtain ⟨a, b, ha, hb, hab, hzexp⟩ := hzseg_m
        obtain ⟨c, d, hc, hd, hcd, hmexp⟩ := hmsegS23
        refine ⟨a * c, a * d + b, mul_nonneg ha hc,
          add_nonneg (mul_nonneg ha hd) hb, ?_, ?_⟩
        · nlinarith
        · calc (a * c) • s2 + (a * d + b) • s3
              = a • (c • s2 + d • s3) + b • s3 := by module
            _ = a • m + b • s3 := by rw [← hmexp]
            _ = (t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3 := hzexp
      have hw_z' : 2 - (hl [u0, u1]) ^ 2
          ≤ ‖(t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3 - s1‖ ^ 2 := by
        by_cases h2 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2
        · obtain ⟨c, d, hc, hd, hcd, hmexp⟩ := hmsegS23
          obtain ⟨a, b, ha, hb, hab, hzexp⟩ := hzseg_m
          have hmv : m = s2 + d • (s3 - s2) := by
            rw [← hmexp]
            have hc1 : c = 1 - d := by linarith
            rw [hc1]
            module
          have hab1 : a = 1 - b := by linarith
          have hzv : (t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3
              = s2 + (a * d + b) • (s3 - s2) := by
            rw [← hzexp, hmv, hab1]
            module
          have hdlam : d ≤ a * d + b := by nlinarith
          have hmono := p14_norm_mono_segment (x := s1) (s2 := s2) (s3 := s3) hvar
            (μ := d) (ν := a * d + b) hd hdlam
          rw [← hmv, ← hzv] at hmono
          have hsqle : ‖s1 - m‖ ^ 2 ≤
              ‖s1 - ((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3)‖ ^ 2 := by
            have := mul_self_le_mul_self (norm_nonneg (s1 - m)) hmono
            nlinarith
          calc 2 - (hl [u0, u1]) ^ 2 ≤ ‖m - s1‖ ^ 2 := hw_m
            _ = ‖s1 - m‖ ^ 2 := by rw [norm_sub_rev]
            _ ≤ ‖s1 - ((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3)‖ ^ 2 := hsqle
            _ = ‖((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3) - s1‖ ^ 2 := by
                rw [norm_sub_rev]
        · have hge : Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3]) := not_lt.mp h2
          have hm : m = s2 := by
            rw [hmeq, mxi, if_pos hge, ← hs2eq]
          obtain ⟨a, b, ha, hb, hab, hzexp⟩ := hzseg_m
          have hab1 : a = 1 - b := by linarith
          have hzv : (t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3
              = s2 + b • (s3 - s2) := by
            rw [← hzexp, hm, hab1]
            module
          have hmono := p14_norm_mono_segment (x := s1) (s2 := s2) (s3 := s3) hvar
            (μ := 0) (ν := b) (le_refl 0) hb
          have hmono' : ‖s1 - s2‖ ≤
              ‖s1 - ((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3)‖ := by
            rw [← hzv] at hmono
            simpa using hmono
          have hsqle : ‖s1 - s2‖ ^ 2 ≤
              ‖s1 - ((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3)‖ ^ 2 := by
            have := mul_self_le_mul_self (norm_nonneg (s1 - s2)) hmono'
            nlinarith
          have hw2 : 2 - (hl [u0, u1]) ^ 2 ≤ ‖s2 - s1‖ ^ 2 := by
            rw [← hm]; exact hw_m
          calc 2 - (hl [u0, u1]) ^ 2 ≤ ‖s2 - s1‖ ^ 2 := hw2
            _ = ‖s1 - s2‖ ^ 2 := by rw [norm_sub_rev]
            _ ≤ ‖s1 - ((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3)‖ ^ 2 := hsqle
            _ = ‖((t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3) - s1‖ ^ 2 := by
                rw [norm_sub_rev]
      refine ⟨(t3 / (t3 + t4)) • m + (t4 / (t3 + t4)) • s3, ?_, hzsegS23', hw_z'⟩
      rw [hxrep, smul_add, smul_smul, smul_smul]
      field_simp
      module
  have hzK1 : z ∈ voronoiList V [u0, u1] :=
    (CONVEX_VORONOI_LIST V [u0, u1]).segment_subset hs2K1 hs3K1 hzsegS23
  have horth_z : (z - s1) ⬝ᵥ (u1 - u0) = 0 :=
    p14_orth_of_voronoi hs1m hb1 hp hzK1
  have hcone0 : (x - u0) ⬝ᵥ (u1 - u0) ≥
      ‖x - u0‖ * ‖u1 - u0‖ * (hl [u0, u1] / Real.sqrt 2) := by
    rw [dist_eq_norm, dist_eq_norm] at hxr0'
    exact hxr0'
  have ht2 : 0 ≤ t2 := p14_rcone_coeff hs1m hh hhpos hhlt horth_z hsum5 ht5nonneg
    hxrep_z hcone0 hw_z
  have horth_z1 : (z - s1) ⬝ᵥ (u0 - u1) = 0 := by
    have hneg : (u0 : Fin 3 → ℝ) - u1.ofLp
        = -((u1 : Fin 3 → ℝ) - u0.ofLp) := by abel
    rw [hneg, dotProduct_neg, horth_z, neg_zero]
  have hs1m1 : s1 = midpoint ℝ u1 u0 := by
    rw [hs1m, midpoint_comm]
  have hh1 : hl [u0, u1] = ‖s1 - u1‖ := by
    rw [hh]
    have hneg : s1 - u1 = -(s1 - u0) := by
      rw [hs1m, midpoint_eq_smul_add]
      norm_num
      module
    rw [hneg, norm_neg]
  have hcone1 : (x - u1) ⬝ᵥ (u0 - u1) ≥
      ‖x - u1‖ * ‖u0 - u1‖ * (hl [u0, u1] / Real.sqrt 2) := by
    rw [dist_eq_norm, dist_eq_norm] at hxr1'
    exact hxr1'
  have hxrep_z1 : x = t2 • u1 + t1 • u0 + (t3 + t4) • z := by
    rw [hxrep_z]; module
  have ht1 : 0 ≤ t1 := p14_rcone_coeff hs1m1 hh1 hhpos hhlt horth_z1
    (by linarith [hsum5]) ht5nonneg hxrep_z1 hcone1 hw_z
  -- the two Rogers simplices in explicit form
  have hrog : rogers V [u0, u1, u2, u3] = convexHull ℝ ({u0, s1, s2, s3} : Set V3) := by
    have h := ROGERS_EXPLICIT V [u0, u1, u2, u3] hs hp hb
    rw [h, show ({hdV [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 1,
        omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} : Set V3)
        = {u0, s1, s2, s3} from by
      simp [hdV, hs1eq, hs2eq, hs3eq]]
  obtain ⟨hbswap, hsw1, hsw2, hsw3, -⟩ := p14_swap_pack hs hp hb hhl hsq
  have hrogswap : rogers V [u1, u0, u2, u3] = convexHull ℝ ({u1, s1, s2, s3} : Set V3) := by
    have h := ROGERS_EXPLICIT V [u1, u0, u2, u3] hs hp hbswap
    rw [h, show ({hdV [u1, u0, u2, u3], omegaListN V [u1, u0, u2, u3] 1,
        omegaListN V [u1, u0, u2, u3] 2, omegaListN V [u1, u0, u2, u3] 3} : Set V3)
        = {u1, s1, s2, s3} from by
      simp [hdV, hsw1, hsw2, hsw3, hs1eq, hs2eq, hs3eq]]
  have hzconv : z ∈ convexHull ℝ ({s2, s3} : Set V3) :=
    segment_subset_convexHull (by simp) (by simp) hzsegS23
  have hzrog : z ∈ rogers V [u0, u1, u2, u3] := by
    rw [hrog]
    exact convexHull_mono (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto) hzconv
  have hzrogswap : z ∈ rogers V [u1, u0, u2, u3] := by
    rw [hrogswap]
    exact convexHull_mono (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto) hzconv
  have hsum3 : t1 + t2 + (t3 + t4) = 1 := hsum5
  rcases le_total t2 t1 with hle | hle
  · left
    rw [hrog]
    have hsplit : x = (t1 - t2) • u0 + (2 * t2) • s1 + (t3 + t4) • z := by
      rw [hxrep_z, hs1m, midpoint_eq_smul_add]
      norm_num
      module
    rw [hsplit]
    have hc := convex_convexHull (𝕜 := ℝ) ({u0, s1, s2, s3} : Set V3)
    have hmem := hc.sum_mem (t := Finset.univ)
      (w := fun i : Fin 3 => ![t1 - t2, 2 * t2, t3 + t4] i)
      (z := fun i : Fin 3 => ![u0, s1, z] i)
      (by
        intro i _
        fin_cases i
        · simp; linarith
        · simp; linarith
        · simp; linarith)
      (by simp [Fin.sum_univ_three]; linarith)
      (by
        intro i _
        fin_cases i
        · exact subset_convexHull ℝ _ (by simp)
        · exact subset_convexHull ℝ _ (by simp)
        · exact convexHull_mono (by
            intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
            tauto) hzconv)
    simpa [Fin.sum_univ_three] using hmem
  · right
    rw [hrogswap]
    have hsplit : x = (t2 - t1) • u1 + (2 * t1) • s1 + (t3 + t4) • z := by
      rw [hxrep_z, hs1m, midpoint_eq_smul_add]
      norm_num
      module
    rw [hsplit]
    have hc := convex_convexHull (𝕜 := ℝ) ({u1, s1, s2, s3} : Set V3)
    have hmem := hc.sum_mem (t := Finset.univ)
      (w := fun i : Fin 3 => ![t2 - t1, 2 * t1, t3 + t4] i)
      (z := fun i : Fin 3 => ![u1, s1, z] i)
      (by
        intro i _
        fin_cases i
        · simp; linarith
        · simp; linarith
        · simp; linarith)
      (by simp [Fin.sum_univ_three]; linarith)
      (by
        intro i _
        fin_cases i
        · exact subset_convexHull ℝ _ (by simp)
        · exact subset_convexHull ℝ _ (by simp)
        · exact convexHull_mono (by
            intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
            tauto) hzconv)
    simpa [Fin.sum_univ_three] using hmem

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
    (hperm : permutes p (Set.Icc 0 (k - 1)))
    (hfix : ∀ j : ℕ, k ≤ j → p j = j) (hvl : vl = leftActionList p ul) :
    barV V 3 vl := by
  subst hvl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · -- k = 0: `hfix` forces the identity permutation
    have hp : p = Equiv.refl ℕ :=
      Equiv.ext fun j => hfix j (Nat.zero_le j)
    subst hp
    rw [p14_leftActionList_refl]
    exact hbar
  · -- k = 1: `hperm` fixes 0 and `hfix` fixes the tail
    have h0 : p 0 = 0 := by
      have hmem : (0:ℕ) ∈ Set.Icc 0 (1 - 1) :=
        Set.mem_Icc.mpr ⟨Nat.zero_le _, by norm_num⟩
      have h := (hperm 0).mp hmem
      simpa [Set.mem_Icc] using h
    have hp : p = Equiv.refl ℕ :=
      p14_eqRefl_of_fix h0 (fun j hj => hfix j (by omega))
    subst hp
    rw [p14_leftActionList_refl]
    exact hbar
  · -- k = 2: the 01-swap bridge
    have hm : mcell 2 V ul = mcell2 V ul := (MCELL_EXPLICIT 2 V ul).2.2.1
    rw [hm, mcell2] at hne
    have hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl ul := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    have hperm' : permutes p ({0, 1} : Set ℕ) := by
      intro x
      have hx := hperm x
      simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      omega
    have hfix' : ∀ j : ℕ, 2 ≤ j → p j = j := fun j hj => hfix j (by omega)
    exact (LEFT_ACTION_LIST_1_PROPERTIES_ALT V ul (leftActionList p ul) p hpack hsat
      hbar hperm' hfix' hcond.1 hcond.2 rfl).1
  · -- k = 3: the S₃ left-action kit
    have hm : mcell 3 V ul = mcell3 V ul := (MCELL_EXPLICIT 3 V ul).2.2.2.1
    rw [hm, mcell3] at hne
    have hcond : hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl ul := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    have hperm' : permutes p (Set.Icc 0 2) := by simpa using hperm
    have hfix' : ∀ j : ℕ, 3 ≤ j → p j = j := fun j hj => hfix j (by omega)
    exact (LEFT_ACTION_LIST_PROPERTIES hpack hsat hbar hcond.1 hcond.2
      hperm' hfix' rfl).1
  · -- k = 4: nonemptiness of `mcell4` gives `hl ul < sqrt 2`; `YIFVQDV_1`
    have hm : mcell 4 V ul = mcell4 V ul :=
      (MCELL_EXPLICIT 4 V ul).2.2.2.2 (by norm_num)
    rw [hm, mcell4] at hne
    have hhl : hl ul < Real.sqrt 2 := by
      by_contra hc
      rw [if_neg hc] at hne
      exact hne rfl
    have hperm' : permutes p (Set.Icc 0 3) := by simpa using hperm
    exact YIFVQDV_1 V ul 3 p hpack hbar hhl hperm'



/-! ## Barycentric coordinates on a finite range -/

private theorem p14_bary {n : ℕ} {v : Fin n → V3} (hinj : Function.Injective v)
    {x : V3} (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧ (∑ i, lam i • v i = x) := by
  have hx' : x ∈ convexHull ℝ ((Finset.univ.image v : Finset V3) : Set V3) := by
    rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [Finset.mem_convexHull'] at hx'
  obtain ⟨w, hw0, hw1, hwx⟩ := hx'
  have hsum : ∑ y ∈ Finset.univ.image v, w y = ∑ i, w (v i) :=
    Finset.sum_image (fun i _ j _ h => hinj h)
  have hsum' : ∑ y ∈ Finset.univ.image v, w y • y = ∑ i, w (v i) • v i :=
    Finset.sum_image (fun i _ j _ h => hinj h)
  exact ⟨fun i => w (v i), fun i => hw0 _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)),
    by rw [← hsum]; exact hw1, by rw [← hsum']; exact hwx⟩

/-! ## Abstract face decomposition -/

private theorem p14_face_decomp {n : ℕ} {v : Fin n → V3} {x c : V3} {lam mu : Fin n → ℝ}
    (hlam0 : ∀ i, 0 ≤ lam i) (hmu0 : ∀ i, 0 ≤ mu i)
    (hlam1 : ∑ i, lam i = 1) (hmu1 : ∑ i, mu i = 1)
    (hx : ∑ i, lam i • v i = x) (hc : ∑ i, mu i • v i = c)
    (hne : x ≠ c) :
    ∃ (i0 : Fin n) (t : ℝ) (y : V3) (nu : Fin n → ℝ), 0 ≤ t ∧ t < 1 ∧ 0 < mu i0 ∧
      x = t • c + (1 - t) • y ∧
      (∀ i, 0 ≤ nu i) ∧ (∑ i, nu i = 1) ∧ y = ∑ i, nu i • v i ∧ nu i0 = 0 ∧
      y ∈ convexHull ℝ (v '' {i | i ≠ i0}) := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < mu i) with hS
  have hSne : S.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hz : ∀ i, mu i = 0 := by
      intro i
      have hi : i ∉ S := by rw [hcon]; exact Finset.notMem_empty i
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hmu0 i)
    have hsum0 : ∑ i, mu i = 0 := Finset.sum_eq_zero fun i _ => hz i
    rw [hmu1] at hsum0
    exact one_ne_zero hsum0
  obtain ⟨i0, hi0S, hi0min⟩ := Finset.exists_min_image S (fun i => lam i / mu i) hSne
  have hi0pos : 0 < mu i0 := (Finset.mem_filter.mp hi0S).2
  set t : ℝ := lam i0 / mu i0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hlam0 i0) (le_of_lt hi0pos)
  have hex : ∃ j, lam j < mu j := by
    by_contra hcon
    push Not at hcon
    have hnonneg : ∀ i, 0 ≤ lam i - mu i := fun i => by linarith [hcon i]
    have hsumz : ∑ i, (lam i - mu i) = 0 := by
      rw [Finset.sum_sub_distrib, hlam1, hmu1, sub_self]
    have hzero : ∀ i, lam i - mu i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun i _ => hnonneg i)).mp hsumz i (Finset.mem_univ i)
    have hxc : x = c := by
      rw [← hx, ← hc]
      exact Finset.sum_congr rfl fun i _ => by rw [sub_eq_zero.mp (hzero i)]
    exact hne hxc
  obtain ⟨j, hj⟩ := hex
  have hjpos : 0 < mu j := lt_of_le_of_lt (hlam0 j) hj
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjpos⟩
  have ht1 : t < 1 := by
    have h1 := hi0min j hjS
    have h2 : lam j / mu j < 1 := by rw [div_lt_one hjpos]; exact hj
    linarith
  have h1t : (1 : ℝ) - t ≠ 0 := by linarith
  set nu : Fin n → ℝ := fun i => (1 - t)⁻¹ * (lam i - t * mu i) with hnu
  have hnu0 : ∀ i, 0 ≤ nu i := by
    intro i
    by_cases hi : 0 < mu i
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have hle := hi0min i hiS
      have hti : t * mu i ≤ lam i := (le_div_iff₀ hi).mp (by simpa [ht] using hle)
      exact mul_nonneg (inv_nonneg.mpr (by linarith)) (by linarith)
    · have hz : mu i = 0 := le_antisymm (le_of_not_gt hi) (hmu0 i)
      simp only [hnu, hz, mul_zero, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr (by linarith)) (hlam0 i)
  have hnu_i0 : nu i0 = 0 := by
    have hz : lam i0 - t * mu i0 = 0 := by
      rw [ht, div_mul_cancel₀ (lam i0) (ne_of_gt hi0pos), sub_self]
    simp only [hnu, hz, mul_zero]
  have hnu1 : ∑ i, nu i = 1 := by
    have h1 : ∑ i, nu i = (1 - t)⁻¹ * ∑ i, (lam i - t * mu i) := by
      simp only [hnu, Finset.mul_sum]
    have h2 : ∑ i, (lam i - t * mu i) = 1 - t := by
      rw [Finset.sum_sub_distrib, hlam1, ← Finset.mul_sum, hmu1, mul_one]
    rw [h1, h2, inv_mul_cancel₀ h1t]
  refine ⟨i0, t, ∑ i, nu i • v i, nu, ht0, ht1, hi0pos, ?_, hnu0, hnu1, rfl, hnu_i0, ?_⟩
  have hyx : (1 - t) • (∑ i, nu i • v i) = x - t • c := by
    have h1 : (1 - t) • (∑ i, nu i • v i) = ∑ i, ((1 - t) * nu i) • v i := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    rw [h1]
    have hterm : ∀ i, ((1 - t) * nu i) • v i = (lam i - t * mu i) • v i := by
      intro i
      rw [hnu]
      have hc : (1 - t) * ((1 - t)⁻¹ * (lam i - t * mu i)) = lam i - t * mu i := by
        rw [← mul_assoc, mul_inv_cancel₀ h1t, one_mul]
      rw [hc]
    rw [show ∑ i, ((1 - t) * nu i) • v i = ∑ i, (lam i - t * mu i) • v i from
      Finset.sum_congr rfl fun i _ => hterm i]
    rw [show ∑ i, (lam i - t * mu i) • v i
        = ∑ i, (lam i • v i - (t * mu i) • v i) from
      Finset.sum_congr rfl fun i _ => sub_smul (lam i) (t * mu i) (v i)]
    rw [Finset.sum_sub_distrib]
    have hsmul : ∑ i, (t * mu i) • v i = t • c := by
      rw [← hc, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    rw [hx, hsmul]
  · calc x = t • c + (x - t • c) := by module
      _ = t • c + (1 - t) • (∑ i, nu i • v i) := by rw [hyx]
  · have hsum' : ∑ i, nu i • v i = ∑ i ∈ Finset.univ.erase i0, nu i • v i := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0), hnu_i0, zero_smul, add_zero]
    rw [hsum']
    have hcoef1 : ∑ i ∈ Finset.univ.erase i0, nu i = 1 := by
      have h := Finset.sum_erase_add (s := Finset.univ) (f := nu) (a := i0)
        (Finset.mem_univ i0)
      rw [hnu_i0, add_zero] at h
      rw [h, hnu1]
    exact (convex_convexHull ℝ (v '' {i | i ≠ i0})).sum_mem
      (t := Finset.univ.erase i0)
      (w := nu) (z := v)
      (fun i _ => hnu0 i)
      hcoef1
      (fun i hi => subset_convexHull ℝ _ (Set.mem_image_of_mem v (by
        simp only [Set.mem_setOf_eq]
        exact Finset.ne_of_mem_erase hi)))

/-! ## The 2D segment split -/

private theorem p14_in_tri_pair {A B M cc x y : V3} {t s : ℝ}
    (hM : M = midpoint ℝ A B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hy : y = (1 - s) • A + s • B)
    (hx : x = t • cc + (1 - t) • y) :
    x ∈ convexHull ℝ ({A, M, cc} : Set V3) ∨
      x ∈ convexHull ℝ ({B, M, cc} : Set V3) := by
  by_cases hle : s ≤ 1 / 2
  · have hmid : midpoint ℝ A B = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
      rw [midpoint_eq_smul_add]; norm_num
    have hyseg : y ∈ segment ℝ A M := by
      rw [segment_eq_image]
      refine ⟨2 * s, ⟨by linarith, by linarith⟩, ?_⟩
      rw [hM, hmid, hy]
      module
    have hseg : y ∈ convexHull ℝ ({A, M, cc} : Set V3) :=
      segment_subset_convexHull (s := ({A, M, cc} : Set V3)) (by simp) (by simp) hyseg
    have hconv := convex_convexHull ℝ ({A, M, cc} : Set V3)
    have hmem := hconv.sum_mem (t := Finset.univ)
      (w := fun i : Fin 2 => ![t, 1 - t] i) (z := fun i : Fin 2 => ![cc, y] i)
      (by
        intro i _
        fin_cases i
        simpa using ht0
        simpa using sub_nonneg.mpr ht1)
      (by simp [Fin.sum_univ_two])
      (by
        intro i _
        fin_cases i
        exact subset_convexHull ℝ _ (by simp)
        exact hseg)
    exact Or.inl (by simpa [Fin.sum_univ_two, hx] using hmem)
  · have hs2 : (1 : ℝ) / 2 ≤ s := le_of_lt (lt_of_not_ge hle)
    have hmid : midpoint ℝ B A = (1 / 2 : ℝ) • B + (1 / 2 : ℝ) • A := by
      rw [midpoint_eq_smul_add]; norm_num
    have hyseg : y ∈ segment ℝ B M := by
      rw [segment_eq_image]
      refine ⟨2 - 2 * s, ⟨by linarith, by linarith⟩, ?_⟩
      rw [show midpoint ℝ A B = midpoint ℝ B A from midpoint_comm A B] at hM
      rw [hM, hmid, hy]
      module
    have hseg : y ∈ convexHull ℝ ({B, M, cc} : Set V3) :=
      segment_subset_convexHull (s := ({B, M, cc} : Set V3)) (by simp) (by simp) hyseg
    have hMba : M = midpoint ℝ B A := by rw [hM, midpoint_comm]
    have hconv := convex_convexHull ℝ ({B, M, cc} : Set V3)
    have hmem := hconv.sum_mem (t := Finset.univ)
      (w := fun i : Fin 2 => ![t, 1 - t] i) (z := fun i : Fin 2 => ![cc, y] i)
      (by
        intro i _
        fin_cases i
        simpa using ht0
        simpa using sub_nonneg.mpr ht1)
      (by simp [Fin.sum_univ_two])
      (by
        intro i _
        fin_cases i
        exact subset_convexHull ℝ _ (by simp)
        exact hseg)
    exact Or.inr (by simpa [Fin.sum_univ_two, hx] using hmem)

/-! ## Generic convex-combination closure -/

private theorem p14_convex_comb {C : Set V3} (hC : Convex ℝ C) {x y cc : V3} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hy : y ∈ C) (hc : cc ∈ C)
    (hx : x = t • cc + (1 - t) • y) : x ∈ C := by
  have h := hC.sum_mem (t := Finset.univ)
    (w := fun i : Fin 2 => ![t, 1 - t] i) (z := fun i : Fin 2 => ![cc, y] i)
    (by
      intro i _
      fin_cases i
      simpa using ht0
      simpa using sub_nonneg.mpr ht1)
    (by simp [Fin.sum_univ_two])
    (by
      intro i _
      fin_cases i
      simpa using hc
      simpa using hy)
  simpa [Fin.sum_univ_two, hx] using h

/-! ## Affine 2D cover -/

private theorem p14_affine_tri_cover {v : Fin 3 → V3} {x cc : V3}
    (hinj : Function.Injective v)
    (hx : x ∈ convexHull ℝ (Set.range v))
    (hc : cc ∈ convexHull ℝ (Set.range v)) :
    ∃ i j : Fin 3, i ≠ j ∧
      x ∈ convexHull ℝ ({v i, midpoint ℝ (v i) (v j), cc} : Set V3) := by
  by_cases hxc : x = cc
  · subst hxc
    exact ⟨0, 1, by decide, subset_convexHull ℝ _ (by simp)⟩
  obtain ⟨lam, hlam0, hlam1, hx'⟩ := p14_bary hinj hx
  obtain ⟨mu, hmu0, hmu1, hc'⟩ := p14_bary hinj hc
  obtain ⟨i0, t, y, nu, ht0, ht1, hi0pos, hxdec, hnu0, hnu1, hy, hnu_i0, hyface⟩ :=
    p14_face_decomp hlam0 hmu0 hlam1 hmu1 hx' hc' hxc
  have htle : t ≤ 1 := le_of_lt ht1
  fin_cases i0
  · -- i0 = 0: pair (1,2) or (2,1)
    have hz : nu 0 = 0 := by simpa using hnu_i0
    have hsum : nu 1 + nu 2 = 1 := by
      have h := hnu1
      rw [Fin.sum_univ_three] at h
      linarith
    have hy' : y = (1 - nu 2) • v 1 + nu 2 • v 2 := by
      rw [hy, Fin.sum_univ_three]
      rw [hz, zero_smul, zero_add]
      rw [show nu 1 = 1 - nu 2 by linarith]
    rcases p14_in_tri_pair (A := v 1) (B := v 2) (M := midpoint ℝ (v 1) (v 2))
      (cc := cc) (x := x) (y := y) (t := t) (s := nu 2) rfl ht0 htle (hnu0 2)
      (by linarith [hnu0 1]) hy' hxdec with h | h
    · exact ⟨1, 2, by decide, h⟩
    · exact ⟨2, 1, by decide, by simpa [midpoint_comm] using h⟩
  · -- i0 = 1: pair (0,2) or (2,0)
    have hz : nu 1 = 0 := by simpa using hnu_i0
    have hsum : nu 0 + nu 2 = 1 := by
      have h := hnu1
      rw [Fin.sum_univ_three] at h
      linarith
    have hy' : y = (1 - nu 2) • v 0 + nu 2 • v 2 := by
      rw [hy, Fin.sum_univ_three]
      rw [hz, zero_smul]
      rw [show nu 0 = 1 - nu 2 by linarith]
      abel
    rcases p14_in_tri_pair (A := v 0) (B := v 2) (M := midpoint ℝ (v 0) (v 2))
      (cc := cc) (x := x) (y := y) (t := t) (s := nu 2) rfl ht0 htle (hnu0 2)
      (by linarith [hnu0 0]) hy' hxdec with h | h
    · exact ⟨0, 2, by decide, h⟩
    · exact ⟨2, 0, by decide, by simpa [midpoint_comm] using h⟩
  · -- i0 = 2: pair (0,1) or (1,0)
    have hz : nu 2 = 0 := by simpa using hnu_i0
    have hsum : nu 0 + nu 1 = 1 := by
      have h := hnu1
      rw [Fin.sum_univ_three] at h
      linarith
    have hy' : y = (1 - nu 1) • v 0 + nu 1 • v 1 := by
      rw [hy, Fin.sum_univ_three]
      rw [hz, zero_smul, add_zero]
      rw [show nu 0 = 1 - nu 1 by linarith]
    rcases p14_in_tri_pair (A := v 0) (B := v 1) (M := midpoint ℝ (v 0) (v 1))
      (cc := cc) (x := x) (y := y) (t := t) (s := nu 1) rfl ht0 htle (hnu0 1)
      (by linarith [hnu0 0]) hy' hxdec with h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨1, 0, by decide, by simpa [midpoint_comm] using h⟩

/-! ## Affine 3D cover -/

private theorem p14_affine_tetra_cover {v : Fin 4 → V3} {x cc : V3} (cf : Fin 4 → V3)
    (hinj : Function.Injective v)
    (hx : x ∈ convexHull ℝ (Set.range v))
    (hc : cc ∈ convexHull ℝ (Set.range v))
    (hcf : ∀ l : Fin 4, cf l ∈ convexHull ℝ (v '' {i | i ≠ l})) :
    ∃ i j l : Fin 4, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      x ∈ convexHull ℝ ({v i, midpoint ℝ (v i) (v j), cf l, cc} : Set V3) := by
  by_cases hxc : x = cc
  · subst hxc
    refine ⟨0, 1, 2, by decide, by decide, by decide, ?_⟩
    exact subset_convexHull ℝ _ (by simp)
  obtain ⟨lam, hlam0, hlam1, hx'⟩ := p14_bary hinj hx
  obtain ⟨mu, hmu0, hmu1, hc'⟩ := p14_bary hinj hc
  obtain ⟨l, t, y, nu, ht0, ht1, hlpos, hxdec, hnu0, hnu1, hy, hnu_l, hyface⟩ :=
    p14_face_decomp hlam0 hmu0 hlam1 hmu1 hx' hc' hxc
  have hinj' : Function.Injective (fun i : Fin 3 => v (l.succAbove i)) :=
    fun a b h => l.succAbove_right_injective (hinj h)
  have hrange : Set.range (fun i : Fin 3 => v (l.succAbove i)) = v '' {i | i ≠ l} := by
    change Set.range (v ∘ l.succAbove) = v '' {i | i ≠ l}
    rw [Set.range_comp, Fin.range_succAbove]
    rfl
  have hy' : y ∈ convexHull ℝ (Set.range (fun i : Fin 3 => v (l.succAbove i))) :=
    hrange ▸ hyface
  have hcf' : cf l ∈ convexHull ℝ (Set.range (fun i : Fin 3 => v (l.succAbove i))) :=
    hrange ▸ hcf l
  obtain ⟨i', j', hne, hmem⟩ := p14_affine_tri_cover hinj' hy' hcf'
  refine ⟨l.succAbove i', l.succAbove j', l, ?_, ?_, ?_, ?_⟩
  · intro h; exact hne (l.succAbove_right_injective h)
  · exact l.succAbove_ne i'
  · exact l.succAbove_ne j'
  · have hsub : convexHull ℝ
        ({v (l.succAbove i'), midpoint ℝ (v (l.succAbove i')) (v (l.succAbove j')),
          cf l} : Set V3) ⊆
        convexHull ℝ ({v (l.succAbove i'), midpoint ℝ (v (l.succAbove i')) (v (l.succAbove j')),
          cf l, cc} : Set V3) :=
      convexHull_mono (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto)
    exact p14_convex_comb (convex_convexHull ℝ _) ht0 (le_of_lt ht1) (hsub hmem)
      (subset_convexHull ℝ _ (by simp)) hxdec




private theorem p14_omega1_mid {V : Set V3} {a b c d : V3} (hp : Packing V)
    (hb : barV V 3 [a, b, c, d]) (hhl : hl [a, b] < Real.sqrt 2) :
    omegaListN V [a, b, c, d] 1 = midpoint ℝ a b := by
  have hb1 : barV V 1 [a, b] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [a, b, c, d] [a, b] hb
      (INITIAL_SUBLIST_APPEND [a, b] [c, d]) (by simp)
  rw [OMEGA_LIST_TRUNCATE_1, XNHPWAB1 V [a, b] 1 hp hb1 hhl,
    show setOfList [a, b] = ({a, b} : Set V3) from by ext x; simp [setOfList],
    CIRCUMCENTER_2]

private theorem p14_omega2_cc {V : Set V3} {a b c d : V3} (hp : Packing V)
    (hb : barV V 3 [a, b, c, d]) (hhl : hl [a, b, c] < Real.sqrt 2) :
    omegaListN V [a, b, c, d] 2 = circumcenter ({a, b, c} : Set V3) := by
  have hb2 : barV V 2 [a, b, c] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [a, b, c, d] [a, b, c] hb
      (INITIAL_SUBLIST_APPEND [a, b, c] [d]) (by simp)
  rw [OMEGA_LIST_TRUNCATE_2, XNHPWAB1 V [a, b, c] 2 hp hb2 hhl,
    show setOfList [a, b, c] = ({a, b, c} : Set V3) from by ext x; simp [setOfList]]

-- range of a vector
example (u0 u1 u2 : V3) : Set.range ![u0, u1, u2] = ({u0, u1, u2} : Set V3) := by
  ext x; simp; tauto

example (u0 u1 u2 u3 : V3) :
    Set.range ![u0, u1, u2, u3] = ({u0, u1, u2, u3} : Set V3) := by
  ext x; simp; tauto

-- remaining index completion
private theorem p14_fin4_complete {i j l : Fin 4} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    ∃ k : Fin 4, k ≠ i ∧ k ≠ j ∧ k ≠ l ∧ Function.Bijective ![i, j, k, l] := by
  have hsub : ({i, j, l} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
  have hcard : ({i, j, l} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hil]),
      Finset.card_insert_of_notMem (by simp [hjl]), Finset.card_singleton]
  have hk : ∃ k : Fin 4, k ∉ ({i, j, l} : Finset (Fin 4)) := by
    by_contra hcon
    push Not at hcon
    have hle : (Finset.univ : Finset (Fin 4)) ⊆ {i, j, l} := by
      intro t _; exact hcon t
    have hcard2 : (Finset.univ : Finset (Fin 4)).card ≤ 3 :=
      (Finset.card_le_card hle).trans_eq hcard
    simp at hcard2
  obtain ⟨k, hk⟩ := hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hki, hkj, hkl⟩ := hk
  refine ⟨k, hki, hkj, hkl, ?_⟩
  have hinj : Function.Injective ![i, j, k, l] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩




private noncomputable def p14_natEquiv (n : ℕ) : Fin n ⊕ ℕ ≃ ℕ :=
  Equiv.ofBijective
    (Sum.elim (fun i : Fin n => (i : ℕ)) (fun k : ℕ => n + k)) <| by
    constructor
    · intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          simp only [Sum.elim_inl, Fin.val_eq_val] at h
          exact congrArg Sum.inl h
        | inr j =>
          simp only [Sum.elim_inl, Sum.elim_inr] at h
          have hi : (i : ℕ) < n := i.isLt
          omega
      | inr i =>
        cases b with
        | inl j =>
          simp only [Sum.elim_inl, Sum.elim_inr] at h
          have hj : (j : ℕ) < n := j.isLt
          omega
        | inr j =>
          simp only [Sum.elim_inr] at h
          exact congrArg Sum.inr (Nat.add_left_cancel h)
    · intro m
      by_cases hm : m < n
      · exact ⟨Sum.inl ⟨m, hm⟩, by simp [Sum.elim]⟩
      · exact ⟨Sum.inr (m - n), by simp [Sum.elim]; omega⟩

private theorem p14_natEquiv_apply_inl (n : ℕ) (i : Fin n) :
    p14_natEquiv n (Sum.inl i) = (i : ℕ) := rfl

private theorem p14_natEquiv_apply_inr (n : ℕ) (k : ℕ) :
    p14_natEquiv n (Sum.inr k) = n + k := rfl

private theorem p14_natEquiv_symm_apply_lt (n : ℕ) (i : Fin n) :
    (p14_natEquiv n).symm (i : ℕ) = Sum.inl i := by
  rw [← p14_natEquiv_apply_inl n i, Equiv.symm_apply_apply]

private theorem p14_natEquiv_symm_apply_ge (n : ℕ) {j : ℕ} (hj : n ≤ j) :
    (p14_natEquiv n).symm j = Sum.inr (j - n) := by
  have h : p14_natEquiv n (Sum.inr (j - n)) = j := by
    rw [p14_natEquiv_apply_inr, Nat.add_sub_cancel' hj]
  calc (p14_natEquiv n).symm j
      = (p14_natEquiv n).symm (p14_natEquiv n (Sum.inr (j - n))) := by rw [h]
    _ = Sum.inr (j - n) := Equiv.symm_apply_apply _ _

private noncomputable def p14_natPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ :=
  ((p14_natEquiv n).symm.trans (σ.sumCongr (Equiv.refl ℕ))).trans (p14_natEquiv n)

private theorem p14_natPerm_apply_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    p14_natPerm σ (i : ℕ) = (σ i : ℕ) := by
  rw [p14_natPerm, Equiv.trans_apply, Equiv.trans_apply, p14_natEquiv_symm_apply_lt,
    Equiv.sumCongr_apply, Sum.map_inl, p14_natEquiv_apply_inl]

private theorem p14_natPerm_symm_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (p14_natPerm σ).symm (i : ℕ) = (σ.symm i : ℕ) := by
  have h : p14_natPerm σ ((σ.symm i : Fin n) : ℕ) = (i : ℕ) := by
    rw [p14_natPerm_apply_lt]
    simp
  rw [← h, Equiv.symm_apply_apply]

private theorem p14_natPerm_apply_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {j : ℕ}
    (hj : n ≤ j) : p14_natPerm σ j = j := by
  rw [p14_natPerm, Equiv.trans_apply, Equiv.trans_apply, p14_natEquiv_symm_apply_ge n hj,
    Equiv.sumCongr_apply, Sum.map_inr, p14_natEquiv_apply_inr]
  simp only [Equiv.refl_apply]
  omega

private theorem p14_natPerm_permutes {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permutes (p14_natPerm σ) {j : ℕ | j < n} := by
  intro j
  constructor
  · intro hj
    have := p14_natPerm_apply_lt σ ⟨j, hj⟩
    rw [this]
    exact (σ ⟨j, hj⟩).isLt
  · intro hj
    by_contra hcon
    have hge : n ≤ j := Nat.le_of_not_lt hcon
    rw [p14_natPerm_apply_ge σ hge] at hj
    exact absurd hj (Nat.not_lt.mpr hge)


/-! ## Range/set bridges for the finite-index vectors -/

private theorem p14_image_three {v : Fin 3 → V3} {i j k : Fin 3}
    (hbij : Function.Bijective ![i, j, k]) :
    v '' ({i, j, k} : Set (Fin 3)) = Set.range v := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact Set.mem_range_self t
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hbij.2 t
    refine ⟨![i, j, k] s, ?_, rfl⟩
    fin_cases s <;> simp

private theorem p14_three_set {v : Fin 3 → V3} {i j k : Fin 3}
    (hbij : Function.Bijective ![i, j, k]) :
    ({v i, v j, v k} : Set V3) = Set.range v := by
  ext z
  constructor
  · intro hz
    rcases hz with h | h | h
    · exact ⟨i, h.symm⟩
    · exact ⟨j, h.symm⟩
    · exact ⟨k, h.symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hbij.2 t
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem p14_four_set {v : Fin 4 → V3} {i j k l : Fin 4}
    (hbij : Function.Bijective ![i, j, k, l]) :
    ({v i, v j, v k, v l} : Set V3) = Set.range v := by
  ext z
  constructor
  · intro hz
    rcases hz with h | h | h | h
    · exact ⟨i, h.symm⟩
    · exact ⟨j, h.symm⟩
    · exact ⟨k, h.symm⟩
    · exact ⟨l, h.symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hbij.2 t
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

private theorem p14_triple_set (a b c : V3) :
    setOfList [a, b, c] = ({a, b, c} : Set V3) := by
  ext z; simp [setOfList]

private theorem p14_quad_set (a b c d : V3) :
    setOfList [a, b, c, d] = ({a, b, c, d} : Set V3) := by
  ext z; simp [setOfList]

private theorem p14_range_three (a b c : V3) :
    Set.range ![a, b, c] = ({a, b, c} : Set V3) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    fin_cases t
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro hz
    rcases hz with h | h | h
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨2, by simpa using h.symm⟩

private theorem p14_range_four (a b c d : V3) :
    Set.range ![a, b, c, d] = ({a, b, c, d} : Set V3) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    fin_cases t
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro hz
    rcases hz with h | h | h | h
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨2, by simpa using h.symm⟩
    · exact ⟨3, by simpa using h.symm⟩

private theorem p14_face_range {v : Fin 4 → V3} (l : Fin 4) :
    v '' {t | t ≠ l} = Set.range (fun s : Fin 3 => v (l.succAbove s)) := by
  change v '' {t | t ≠ l} = Set.range (v ∘ l.succAbove)
  rw [Set.range_comp, Fin.range_succAbove]
  rfl

private theorem p14_fin3_complete {i j : Fin 3} (hij : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ Function.Bijective ![i, j, k] := by
  have hcard : ({i, j} : Finset (Fin 3)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
  have hk : ∃ k : Fin 3, k ∉ ({i, j} : Finset (Fin 3)) := by
    by_contra hcon
    push Not at hcon
    have hle : (Finset.univ : Finset (Fin 3)) ⊆ {i, j} := fun t _ => hcon t
    have hcard2 : (Finset.univ : Finset (Fin 3)).card ≤ 2 :=
      (Finset.card_le_card hle).trans_eq hcard
    simp at hcard2
  obtain ⟨k, hk⟩ := hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hki, hkj⟩ := hk
  refine ⟨k, hki, hkj, ?_⟩
  have hinj : Function.Injective ![i, j, k] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩

/-! ## k = 3 branch prototype -/

private theorem p14_k3_branch {V : Set V3} {u0 u1 u2 u3 x : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (h1 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2)
    (h2 : Real.sqrt 2 ≤ hl [u0, u1, u2, u3])
    (hx : x ∈ mcell3 V [u0, u1, u2, u3]) :
    x ∈ ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p [u0, u1, u2, u3])) ''
      {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 2) ∧ ∀ n : ℕ, 3 ≤ n → p n = n}) := by
  classical
  have htr2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have htr1 : truncateSimplex 1 [u0, u1, u2, u3] = [u0, u1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2
  rw [mcell3, if_pos ⟨h1, h2⟩] at hx
  have hset : setOfList (truncateSimplex 2 [u0, u1, u2, u3]) ∪ {mxi V [u0, u1, u2, u3]}
      = ({u0, u1, u2, mxi V [u0, u1, u2, u3]} : Set V3) := by
    rw [htr2, p14_triple_set]
    ext z; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset] at hx
  obtain ⟨x1, t1, t2, hx1, ht1, ht2, hsum, hxdec⟩ :=
    convexHull4Imp31 (a := u0) (b := u1) (c := u2) (d := mxi V [u0, u1, u2, u3]) hx
  -- membership and distinctness
  have hmemV : ∀ t ∈ ({u0, u1, u2, u3} : Set V3), t ∈ V := by
    intro t ht
    have hsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
    exact hsub (by simpa [setOfList] using ht)
  have hu0V : u0 ∈ V := hmemV u0 (by simp)
  have hu1V : u1 ∈ V := hmemV u1 (by simp)
  have hu2V : u2 ∈ V := hmemV u2 (by simp)
  have hu3V : u3 ∈ V := hmemV u3 (by simp)
  have hcard : Nat.card (setOfList [u0, u1, u2, u3]) = 4 :=
    (BARV_IMP_LENGTH_EQ_CARD V [u0, u1, u2, u3] 3 hp hb).2
  have hdist := CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT [u0, u1, u2, u3]
    (by rw [hcard]; rfl)
  have hu01 : u0 ≠ u1 := by simpa [elV] using hdist 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hu02 : u0 ≠ u2 := by simpa [elV] using hdist 0 2 (by norm_num) (by norm_num) (by norm_num)
  have hu03 : u0 ≠ u3 := by simpa [elV] using hdist 0 3 (by norm_num) (by norm_num) (by norm_num)
  have hu12 : u1 ≠ u2 := by simpa [elV] using hdist 1 2 (by norm_num) (by norm_num) (by norm_num)
  have hu13 : u1 ≠ u3 := by simpa [elV] using hdist 1 3 (by norm_num) (by norm_num) (by norm_num)
  have hu23 : u2 ≠ u3 := by simpa [elV] using hdist 2 3 (by norm_num) (by norm_num) (by norm_num)
  -- the truncated triangle
  have hbar2 : barV V 2 [u0, u1, u2] := by
    have h := TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by norm_num)
    rwa [htr2] at h
  have hlt2 : hl [u0, u1, u2] < Real.sqrt 2 := by rwa [← htr2]
  have hcc2mem : circumcenter ({u0, u1, u2} : Set V3) ∈
      convexHull ℝ ({u0, u1, u2} : Set V3) := by
    have homega := XNHPWAB2 V [u0, u1, u2] 2 hp hbar2 hlt2
    rw [XNHPWAB1 V [u0, u1, u2] 2 hp hbar2 hlt2,
      show setOfList [u0, u1, u2] = ({u0, u1, u2} : Set V3) from by
        ext z; simp [setOfList]] at homega
    exact homega
  -- the 2D cover
  have hinj3 : Function.Injective ![u0, u1, u2] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have hx1' : x1 ∈ convexHull ℝ (Set.range ![u0, u1, u2]) := by
    rw [p14_range_three]; exact hx1
  have hcc2' : circumcenter ({u0, u1, u2} : Set V3) ∈
      convexHull ℝ (Set.range ![u0, u1, u2]) := by
    rw [p14_range_three]; exact hcc2mem
  obtain ⟨i, j, hij, hx1mem⟩ := p14_affine_tri_cover hinj3 hx1' hcc2'
  obtain ⟨k, hki, hkj, hbij⟩ := p14_fin3_complete hij
  -- the permutation
  let σ : Equiv.Perm (Fin 3) :=
    (Equiv.ofBijective (fun t : Fin 3 => ![i, j, k] t) hbij).symm
  let p : Equiv.Perm ℕ := p14_natPerm σ
  have hp0 : p.symm 0 = (i : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨0, by norm_num⟩ : Fin 3)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hp1 : p.symm 1 = (j : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨1, by norm_num⟩ : Fin 3)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hp2 : p.symm 2 = (k : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨2, by norm_num⟩ : Fin 3)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hp3 : p.symm 3 = 3 := by
    have h3 : p 3 = 3 := p14_natPerm_apply_ge σ (by norm_num : 3 ≤ 3)
    calc p.symm 3 = p.symm (p 3) := by rw [h3]
      _ = 3 := Equiv.symm_apply_apply p 3
  have hperm : permutes p (Set.Icc 0 2) := by
    have h := p14_natPerm_permutes σ
    intro m
    have h' := h m
    simpa [Set.Icc, Nat.lt_succ_iff] using h'
  have hfix : ∀ n : ℕ, 3 ≤ n → p n = n := fun n hn => p14_natPerm_apply_ge σ hn
  set vl : List V3 := leftActionList p [u0, u1, u2, u3] with hvl
  have hvl_eq : vl = [![u0, u1, u2] i, ![u0, u1, u2] j, ![u0, u1, u2] k, u3] := by
    rw [hvl, p14_leftActionList_four_explicit]
    have hgd : ∀ t : Fin 3, [u0, u1, u2, u3].getD (t : ℕ) default = ![u0, u1, u2] t := by
      intro t; fin_cases t <;> simp
    rw [hp0, hp1, hp2, hp3]
    simp only [hgd]
    rfl
  have hprops := LEFT_ACTION_LIST_PROPERTIES (V := V) (ul := [u0, u1, u2, u3]) (xl := vl)
    (p := p) hp hs hb h1 h2 hperm hfix rfl
  obtain ⟨hbvl, hω2, hω3, hmxi⟩ := hprops
  have hrog := ROGERS_EXPLICIT V vl hs hp hbvl
  -- omega 1 is the midpoint of the first two entries
  have hhlpair : hl [![u0, u1, u2] i, ![u0, u1, u2] j] < Real.sqrt 2 := by
    have hvl2eq : truncateSimplex 2 vl
        = [![u0, u1, u2] i, ![u0, u1, u2] j, ![u0, u1, u2] k] := by
      rw [hvl_eq]; exact (TRUNCATE_SIMPLEX_EXPLICIT_2 _ _ _ _).2
    have hvl1eq : truncateSimplex 1 vl = [![u0, u1, u2] i, ![u0, u1, u2] j] := by
      rw [hvl_eq]; exact (TRUNCATE_SIMPLEX_EXPLICIT_1 _ _ _ _).2.2
    have hsetvl2 : setOfList (truncateSimplex 2 vl) = ({u0, u1, u2} : Set V3) := by
      rw [hvl2eq, p14_triple_set, p14_three_set (v := ![u0, u1, u2]) hbij,
        p14_range_three]
    have hhlvl2 : hl (truncateSimplex 2 vl) < Real.sqrt 2 := by
      have he : hl (truncateSimplex 2 vl) = hl [u0, u1, u2] := by
        rw [hl, hl, hsetvl2]
        congr 1
        rw [show setOfList [u0, u1, u2] = ({u0, u1, u2} : Set V3) from by
          ext z; simp [setOfList]]
      rw [he]; exact hlt2
    have hbarvl2 : barV V 2 (truncateSimplex 2 vl) :=
      TRUNCATE_SIMPLEX_BARV V 2 3 vl hbvl (by norm_num)
    have hne : setOfList (truncateSimplex 1 vl) ≠ ∅ := by
      rw [hvl1eq]
      exact Set.nonempty_iff_ne_empty.mp ⟨![u0, u1, u2] i, by simp [setOfList]⟩
    have hsub12 : setOfList (truncateSimplex 1 vl) ⊆ setOfList (truncateSimplex 2 vl) := by
      rw [hvl1eq, hvl2eq, p14_triple_set,
        show setOfList [![u0, u1, u2] i, ![u0, u1, u2] j]
          = ({![u0, u1, u2] i, ![u0, u1, u2] j} : Set V3) from by ext z; simp [setOfList]]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    have hle := RADV_MONO (setOfList (truncateSimplex 2 vl))
      (setOfList (truncateSimplex 1 vl))
      (BARV_AFFINE_INDEPENDENT V (truncateSimplex 2 vl) 2 hp hbarvl2)
      hsub12 hne
    rw [hvl1eq] at hle
    have hfin : radV (setOfList [![u0, u1, u2] i, ![u0, u1, u2] j]) < Real.sqrt 2 :=
      lt_of_le_of_lt hle hhlvl2
    simpa [hl] using hfin
  have hω1vl : omegaListN V vl 1 = midpoint ℝ (![u0, u1, u2] i) (![u0, u1, u2] j) := by
    rw [hvl_eq]
    exact p14_omega1_mid hp (by rw [← hvl_eq]; exact hbvl) hhlpair
  have hω2vl : omegaListN V vl 2 = circumcenter ({u0, u1, u2} : Set V3) := by
    rw [hω2]
    exact p14_omega2_cc hp hb hlt2
  have hhdvl : hdV vl = ![u0, u1, u2] i := by rw [hvl_eq]; rfl
  -- x1 lands in the Rogers simplex
  have hx1rog : x1 ∈ rogers V vl := by
    rw [hrog]
    apply convexHull_mono ?_ hx1mem
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl
    · exact Or.inl hhdvl.symm
    · exact Or.inr (Or.inl (by rw [hω1vl]))
    · exact Or.inr (Or.inr (Or.inl (by rw [hω2vl])))
  -- mxi lands in the Rogers simplex
  have hmrog : mxi V [u0, u1, u2, u3] ∈ rogers V vl := by
    obtain ⟨s, hseg, hdist, hms⟩ :=
      MXI_EXPLICIT V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl h1 h2
    rw [hrog]
    have hseg' : mxi V [u0, u1, u2, u3] ∈
        segment ℝ (omegaListN V vl 2) (omegaListN V vl 3) := by
      rw [← hms, hω2, hω3]
      exact hseg
    exact segment_subset_convexHull (x := omegaListN V vl 2) (y := omegaListN V vl 3)
      (s := ({hdV vl, omegaListN V vl 1, omegaListN V vl 2,
        omegaListN V vl 3} : Set V3))
      (by simp)
      (by simp)
      hseg'
  -- glue
  have hxrog : x ∈ rogers V vl := by
    rw [rogers]
    have hconv := convex_convexHull ℝ (omegaListN V vl '' {j : ℕ | j < vl.length})
    have hmem := hconv.sum_mem (t := Finset.univ)
      (w := fun t : Fin 2 => ![t1, t2] t) (z := fun t : Fin 2 => ![x1, mxi V [u0, u1, u2, u3]] t)
      (by
        intro t _
        fin_cases t
        simpa using ht1
        simpa using ht2)
      (by simp [Fin.sum_univ_two]; linarith)
      (by
        intro t _
        fin_cases t
        · change x1 ∈ convexHull ℝ (omegaListN V vl '' {j : ℕ | j < vl.length})
          exact hx1rog
        · change mxi V [u0, u1, u2, u3] ∈
            convexHull ℝ (omegaListN V vl '' {j : ℕ | j < vl.length})
          exact hmrog)
    have heq : t1 • x1 + t2 • mxi V [u0, u1, u2, u3] = x := by
      rw [hxdec]
    simpa [Fin.sum_univ_two, heq] using hmem
  exact Set.mem_sUnion.2 ⟨rogers V vl, Set.mem_image_of_mem _ ⟨hperm, hfix⟩, hxrog⟩

/-! ## help for the k = 4 branch -/

private theorem p14_face_set (v : Fin 4 → V3) (l : Fin 4) :
    setOfList [v (l.succAbove 0), v (l.succAbove 1), v (l.succAbove 2)] =
      Set.range (fun s : Fin 3 => v (l.succAbove s)) := by
  ext z
  constructor
  · intro hz
    simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  · rintro ⟨s, rfl⟩
    fin_cases s <;> simp [setOfList]

private theorem p14_erase_eq {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({i, j, k} : Finset (Fin 4)) = Finset.univ.erase l := by
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hil, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hjl, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ _⟩
  · have hc1 : ({i, j, k} : Finset (Fin 4)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
        Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
    have hc2 : (Finset.univ.erase l).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ l)]
      simp
    omega

private theorem p14_index_set {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({i, j, k} : Set (Fin 4)) = {t | t ≠ l} := by
  have hEq := p14_erase_eq hij hik hil hjk hjl hkl
  calc ({i, j, k} : Set (Fin 4))
      = ((Finset.univ.erase l : Finset (Fin 4)) : Set (Fin 4)) := by
        rw [← hEq]
        simp
    _ = {t | t ≠ l} := by ext t; simp

private theorem p14_face_set3 {v : Fin 4 → V3} {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    ({v i, v j, v k} : Set V3) = Set.range (fun s : Fin 3 => v (l.succAbove s)) := by
  have himg : ({v i, v j, v k} : Set V3) = v '' ({i, j, k} : Set (Fin 4)) := by
    ext z
    constructor
    · intro hz
      rcases hz with h | h | h
      · exact ⟨i, by simp, h.symm⟩
      · exact ⟨j, by simp, h.symm⟩
      · exact ⟨k, by simp, h.symm⟩
    · rintro ⟨t, ht, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl <;> simp
  rw [himg, p14_index_set hij hik hil hjk hjl hkl, p14_face_range]

/-! ## k = 4 branch prototype -/

private theorem p14_k4_branch {V : Set V3} {u0 u1 u2 u3 x : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hhl : hl [u0, u1, u2, u3] < Real.sqrt 2)
    (hx : x ∈ mcell4 V [u0, u1, u2, u3]) :
    x ∈ ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p [u0, u1, u2, u3])) ''
      {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 3) ∧ ∀ n : ℕ, 4 ≤ n → p n = n}) := by
  classical
  rw [mcell4, if_pos hhl] at hx
  -- distinctness of the four points
  have hmemV : ∀ t ∈ ({u0, u1, u2, u3} : Set V3), t ∈ V := by
    intro t ht
    exact BARV_SUBSET V 3 [u0, u1, u2, u3] hb (by simpa [setOfList] using ht)
  have hcard : Nat.card (setOfList [u0, u1, u2, u3]) = 4 :=
    (BARV_IMP_LENGTH_EQ_CARD V [u0, u1, u2, u3] 3 hp hb).2
  have hdist := CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT [u0, u1, u2, u3]
    (by rw [hcard]; rfl)
  have hu01 : u0 ≠ u1 := by simpa [elV] using hdist 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hu02 : u0 ≠ u2 := by simpa [elV] using hdist 0 2 (by norm_num) (by norm_num) (by norm_num)
  have hu03 : u0 ≠ u3 := by simpa [elV] using hdist 0 3 (by norm_num) (by norm_num) (by norm_num)
  have hu12 : u1 ≠ u2 := by simpa [elV] using hdist 1 2 (by norm_num) (by norm_num) (by norm_num)
  have hu13 : u1 ≠ u3 := by simpa [elV] using hdist 1 3 (by norm_num) (by norm_num) (by norm_num)
  have hu23 : u2 ≠ u3 := by simpa [elV] using hdist 2 3 (by norm_num) (by norm_num) (by norm_num)
  have hinj4 : Function.Injective ![u0, u1, u2, u3] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have hx' : x ∈ convexHull ℝ (Set.range ![u0, u1, u2, u3]) := by
    rw [p14_quad_set, ← p14_range_four] at hx
    exact hx
  -- the circumcenter of the whole tetrahedron
  let cc4 : V3 := circumcenter (Set.range ![u0, u1, u2, u3])
  have hcc4mem : cc4 ∈ convexHull ℝ (Set.range ![u0, u1, u2, u3]) := by
    have h1 : setOfList [u0, u1, u2, u3] = Set.range ![u0, u1, u2, u3] := by
      rw [p14_quad_set, ← p14_range_four]
    have homega := XNHPWAB2 V [u0, u1, u2, u3] 3 hp hb hhl
    have hcc := XNHPWAB1 V [u0, u1, u2, u3] 3 hp hb hhl
    rw [hcc, h1] at homega
    exact homega
  -- the face circumcenters
  let cf : Fin 4 → V3 := fun l =>
    circumcenter (Set.range (fun s : Fin 3 => ![u0, u1, u2, u3] (l.succAbove s)))
  have hcf : ∀ l : Fin 4, cf l ∈
      convexHull ℝ (![u0, u1, u2, u3] '' {i | i ≠ l}) := by
    intro l
    let τ : Fin 4 → Fin 4 :=
      ![l.succAbove 0, l.succAbove 1, l.succAbove 2, l]
    have hτ : Function.Bijective τ := by
      fin_cases l <;> decide
    let σl : Equiv.Perm (Fin 4) := (Equiv.ofBijective τ hτ).symm
    let pl : Equiv.Perm ℕ := p14_natPerm σl
    have hs0 : pl.symm 0 = (l.succAbove 0 : ℕ) := by
      have h := p14_natPerm_symm_lt σl (⟨0, by norm_num⟩ : Fin 4)
      simpa [σl, τ, Equiv.ofBijective_apply] using h
    have hs1 : pl.symm 1 = (l.succAbove 1 : ℕ) := by
      have h := p14_natPerm_symm_lt σl (⟨1, by norm_num⟩ : Fin 4)
      simpa [σl, τ, Equiv.ofBijective_apply] using h
    have hs2 : pl.symm 2 = (l.succAbove 2 : ℕ) := by
      have h := p14_natPerm_symm_lt σl (⟨2, by norm_num⟩ : Fin 4)
      simpa [σl, τ, Equiv.ofBijective_apply] using h
    have hs3 : pl.symm 3 = (l : ℕ) := by
      have h := p14_natPerm_symm_lt σl (⟨3, by norm_num⟩ : Fin 4)
      simpa [σl, τ, Equiv.ofBijective_apply] using h
    have hperm_l : permutes pl (Set.Icc 0 3) := by
      have h := p14_natPerm_permutes σl
      intro m
      simpa [Set.Icc, Nat.lt_succ_iff] using h m
    have hvl_eq : leftActionList pl [u0, u1, u2, u3] =
        [![u0, u1, u2, u3] (l.succAbove 0), ![u0, u1, u2, u3] (l.succAbove 1),
         ![u0, u1, u2, u3] (l.succAbove 2), ![u0, u1, u2, u3] l] := by
      rw [p14_leftActionList_four_explicit]
      have hgd : ∀ t : Fin 4, [u0, u1, u2, u3].getD (t : ℕ) default = ![u0, u1, u2, u3] t := by
        intro t; fin_cases t <;> simp
      rw [hs0, hs1, hs2, hs3]
      simp only [hgd]
    have hbvl : barV V 3 (leftActionList pl [u0, u1, u2, u3]) :=
      YIFVQDV_1 V [u0, u1, u2, u3] 3 pl hp hb hhl hperm_l
    have htr2 : truncateSimplex 2 (leftActionList pl [u0, u1, u2, u3]) =
        [![u0, u1, u2, u3] (l.succAbove 0), ![u0, u1, u2, u3] (l.succAbove 1),
         ![u0, u1, u2, u3] (l.succAbove 2)] := by
      rw [hvl_eq]; exact (TRUNCATE_SIMPLEX_EXPLICIT_2 _ _ _ _).2
    have hbar2 : barV V 2 (truncateSimplex 2 (leftActionList pl [u0, u1, u2, u3])) :=
      TRUNCATE_SIMPLEX_BARV V 2 3 _ hbvl (by norm_num)
    have hsetvl : setOfList (leftActionList pl [u0, u1, u2, u3])
        = setOfList [u0, u1, u2, u3] := by
      rw [hvl_eq, p14_quad_set, p14_four_set (v := ![u0, u1, u2, u3]) hτ,
        p14_range_four, ← p14_quad_set]
    have hhlvl : hl (leftActionList pl [u0, u1, u2, u3]) = hl [u0, u1, u2, u3] := by
      rw [hl, hl, hsetvl]
    have hhl2 : hl (truncateSimplex 2 (leftActionList pl [u0, u1, u2, u3])) < Real.sqrt 2 := by
      have hle := HL_DECREASE V (leftActionList pl [u0, u1, u2, u3]) 3 2 hp hbvl (by norm_num)
      rw [hhlvl] at hle
      exact lt_of_le_of_lt hle hhl
    have homega := XNHPWAB2 V (truncateSimplex 2 (leftActionList pl [u0, u1, u2, u3])) 2 hp hbar2 hhl2
    have hcc := XNHPWAB1 V (truncateSimplex 2 (leftActionList pl [u0, u1, u2, u3])) 2 hp hbar2 hhl2
    rw [hcc] at homega
    rw [htr2, p14_face_set] at homega
    rw [p14_face_range]
    exact homega
  -- the affine tetrahedron cover
  obtain ⟨i, j, l, hij, hil, hjl, hxmem⟩ :=
    p14_affine_tetra_cover (v := ![u0, u1, u2, u3]) cf hinj4 hx' hcc4mem hcf
  obtain ⟨k, hki, hkj, hkl, hbij⟩ := p14_fin4_complete hij hil hjl
  -- the permutation bringing `(i,j,k,l)` to the front
  let σ : Equiv.Perm (Fin 4) :=
    (Equiv.ofBijective (fun t : Fin 4 => ![i, j, k, l] t) hbij).symm
  let p : Equiv.Perm ℕ := p14_natPerm σ
  have hp0 : p.symm 0 = (i : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨0, by norm_num⟩ : Fin 4)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hp1 : p.symm 1 = (j : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨1, by norm_num⟩ : Fin 4)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hp2 : p.symm 2 = (k : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨2, by norm_num⟩ : Fin 4)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hp3 : p.symm 3 = (l : ℕ) := by
    have h := p14_natPerm_symm_lt σ (⟨3, by norm_num⟩ : Fin 4)
    simpa [σ, Equiv.ofBijective_apply] using h
  have hperm : permutes p (Set.Icc 0 3) := by
    have h := p14_natPerm_permutes σ
    intro m
    simpa [Set.Icc, Nat.lt_succ_iff] using h m
  have hfix : ∀ n : ℕ, 4 ≤ n → p n = n := fun n hn => p14_natPerm_apply_ge σ hn
  set vl : List V3 := leftActionList p [u0, u1, u2, u3] with hvl
  have hvl_eq : vl = [![u0, u1, u2, u3] i, ![u0, u1, u2, u3] j,
      ![u0, u1, u2, u3] k, ![u0, u1, u2, u3] l] := by
    rw [hvl, p14_leftActionList_four_explicit]
    have hgd : ∀ t : Fin 4, [u0, u1, u2, u3].getD (t : ℕ) default = ![u0, u1, u2, u3] t := by
      intro t; fin_cases t <;> simp
    rw [hp0, hp1, hp2, hp3]
    simp only [hgd]
  have hik : i ≠ k := hki.symm
  have hjk : j ≠ k := hkj.symm
  have hbvl : barV V 3 vl := YIFVQDV_1 V [u0, u1, u2, u3] 3 p hp hb hhl hperm
  have hsetvl : setOfList vl = setOfList [u0, u1, u2, u3] := by
    rw [hvl_eq, p14_quad_set, p14_four_set (v := ![u0, u1, u2, u3]) hbij,
      p14_range_four, ← p14_quad_set]
  have hhlvl : hl vl = hl [u0, u1, u2, u3] := by rw [hl, hl, hsetvl]
  have hrog := ROGERS_EXPLICIT V vl hs hp hbvl
  have hltvl : hl vl < Real.sqrt 2 := by rw [hhlvl]; exact hhl
  have hω1vl : omegaListN V vl 1 = midpoint ℝ (![u0, u1, u2, u3] i) (![u0, u1, u2, u3] j) := by
    rw [OMEGA_LIST_1_EXPLICIT (![u0, u1, u2, u3] i) (![u0, u1, u2, u3] j)
      (![u0, u1, u2, u3] k) (![u0, u1, u2, u3] l) V vl hs hp hbvl hltvl hvl_eq,
      CIRCUMCENTER_2]
  have hcf_eq : cf l = circumcenter ({![u0, u1, u2, u3] i, ![u0, u1, u2, u3] j,
      ![u0, u1, u2, u3] k} : Set V3) := by
    dsimp only [cf]
    congr 1
    exact (p14_face_set3 hij hik hil hjk hjl hkl).symm
  have hω2vl : omegaListN V vl 2 = cf l := by
    rw [OMEGA_LIST_2_EXPLICIT (![u0, u1, u2, u3] i) (![u0, u1, u2, u3] j)
      (![u0, u1, u2, u3] k) (![u0, u1, u2, u3] l) V vl hs hp hbvl hltvl hvl_eq,
      hcf_eq]
  have hω3vl : omegaListN V vl 3 = cc4 := by
    rw [OMEGA_LIST_3_EXPLICIT (![u0, u1, u2, u3] i) (![u0, u1, u2, u3] j)
      (![u0, u1, u2, u3] k) (![u0, u1, u2, u3] l) V vl hs hp hbvl hltvl hvl_eq]
    dsimp only [cc4]
    congr 1
    exact p14_four_set (v := ![u0, u1, u2, u3]) hbij
  have hhdvl : hdV vl = ![u0, u1, u2, u3] i := by rw [hvl_eq]; rfl
  have hxrog : x ∈ rogers V vl := by
    rw [hrog]
    have hseteq : ({hdV vl, omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} : Set V3)
        = ({![u0, u1, u2, u3] i, midpoint ℝ (![u0, u1, u2, u3] i) (![u0, u1, u2, u3] j),
            cf l, cc4} : Set V3) := by
      rw [hhdvl, hω1vl, hω2vl, hω3vl]
    rw [hseteq]
    exact hxmem
  exact Set.mem_sUnion.2 ⟨rogers V vl, Set.mem_image_of_mem _ ⟨hperm, hfix⟩, hxrog⟩

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

Statement 2026-10-12 (STATEMENT-FIX 项 38 立项起草): comprehension 补
tail-fixed 合取项 `∧ ∀ n, k ≤ n → p n = n`——弱 `permutes` 编码下 junk 尾
排列把 getD-default 点甩进 `leftActionList`，弱式并集含下游（`QZKSYKG1`/
`RVFXZBU` 均带 `hfix`）无法消费的 junk simplex；PA17
`p17_ajripqn_of_tailfix` 的 `hQ2` 消费形即补后式。补后式 ⇒ 原冻结式
（image/sUnion 单调），现有弱式消费者可单调回退。
Status 2026-09-30: still `sorry`ed (giant).
DISCHARGES: none (feeds marchal3/KIZHLTL downstream). -/
theorem QZKSYKG2 {V : Set V3} {ul : List V3} {k : ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
    mcell k V ul ⊆
      ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧
          ∀ n : ℕ, k ≤ n → p n = n}) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · -- k = 0: `mcell0 = rogers \ ball`, covered by the identity permutation
    refine Set.mem_sUnion.2 ⟨rogers V (leftActionList (Equiv.refl ℕ) ul), ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      exact ⟨fun m => by simp, fun n _ => rfl⟩
    · rw [p14_leftActionList_refl]
      have hm : mcell 0 V ul = mcell0 V ul := (MCELL_EXPLICIT 0 V ul).1
      rw [hm, mcell0] at hx
      exact hx.1
  · -- k = 1: `mcell1` is a subset of `rogers`
    refine Set.mem_sUnion.2 ⟨rogers V (leftActionList (Equiv.refl ℕ) ul), ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      exact ⟨fun m => by simp, fun n _ => rfl⟩
    · rw [p14_leftActionList_refl]
      have hm : mcell 1 V ul = mcell1 V ul := (MCELL_EXPLICIT 1 V ul).2.1
      rw [hm, mcell1] at hx
      split_ifs at hx
      · exact hx.1.1
      · exact absurd hx (by simp)
  · -- k = 2: B5b/c/d, the two-Rogers cover
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    have hmcell : mcell 2 V [u0, u1, u2, u3] = mcell2 V [u0, u1, u2, u3] :=
      (MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1
    rw [hmcell] at hx
    have hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
      by_contra hc
      rcases not_and_or.mp hc with h1 | h2
      · rw [mcell2, if_neg (by simp [h1])] at hx
        exact absurd hx (by simp)
      · rw [mcell2, if_neg (by simp [h2])] at hx
        exact absurd hx (by simp)
    have hcov := mcell2_subset_rogers_pair
      (s1 := omegaListN V [u0, u1, u2, u3] 1)
      (s2 := omegaListN V [u0, u1, u2, u3] 2)
      (s3 := omegaListN V [u0, u1, u2, u3] 3)
      (m := mxi V [u0, u1, u2, u3])
      hsat hpack hbar hcond rfl rfl rfl rfl hx
    have hperm_swap : permutes (Equiv.swap 0 1) (Set.Icc 0 1) := by
      intro m
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have hm' : m = 0 ∨ m = 1 := by omega
        rcases hm' with rfl | rfl
        · show (0:ℕ) ∈ Set.Icc 0 1 ↔ (Equiv.swap 0 1) 0 ∈ Set.Icc 0 1
          rw [Equiv.swap_apply_left]; simp
        · show (1:ℕ) ∈ Set.Icc 0 1 ↔ (Equiv.swap 0 1) 1 ∈ Set.Icc 0 1
          rw [Equiv.swap_apply_right]; simp
      · have h0 : m ≠ 0 := by omega
        have h1 : m ≠ 1 := by omega
        show m ∈ Set.Icc 0 1 ↔ (Equiv.swap 0 1) m ∈ Set.Icc 0 1
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    rcases hcov with hleft | hright
    · refine Set.mem_sUnion.2
        ⟨rogers V (leftActionList (Equiv.refl ℕ) [u0, u1, u2, u3]), ?_, ?_⟩
      · refine Set.mem_image_of_mem _ ?_
        exact ⟨fun m => by simp, fun n _ => rfl⟩
      · rw [p14_leftActionList_refl]
        exact hleft
    · refine Set.mem_sUnion.2
        ⟨rogers V (leftActionList (Equiv.swap 0 1) [u0, u1, u2, u3]), ?_, ?_⟩
      · refine Set.mem_image_of_mem _ ?_
        exact ⟨hperm_swap, fun n hn =>
          Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)⟩
      · have hleft_swap : leftActionList (Equiv.swap 0 1) [u0, u1, u2, u3]
            = [u1, u0, u2, u3] :=
          p14_leftActionList_swap01 u0 u1 u2 u3 (Equiv.swap 0 1) (by simp) (by simp)
            (fun j hj => Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))
        rw [hleft_swap]
        exact hright
  · -- k = 3: the `mcell3` cover (B4 lane 2026-10-22)
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    have hm : mcell 3 V [u0, u1, u2, u3] = mcell3 V [u0, u1, u2, u3] :=
      (MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1
    rw [hm] at hx
    have hcond : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
      by_contra hc
      rw [mcell3, if_neg hc] at hx
      exact hx
    exact p14_k3_branch hsat hpack hbar hcond.1 hcond.2 hx
  · -- k = 4: the `mcell4` cover (B4 lane 2026-10-22)
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbar
    subst hul
    have hm : mcell 4 V [u0, u1, u2, u3] = mcell4 V [u0, u1, u2, u3] :=
      (MCELL_EXPLICIT 4 V [u0, u1, u2, u3]).2.2.2.2 (by norm_num)
    rw [hm] at hx
    have hhl : hl [u0, u1, u2, u3] < Real.sqrt 2 := by
      by_contra hc
      rw [mcell4, if_neg hc] at hx
      exact hx
    exact p14_k4_branch hsat hpack hbar hhl hx


end Kepler.Text

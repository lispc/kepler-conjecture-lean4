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
- Proof status: the five supporting lemmas are proved (mechanical);
  `QZKSYKG1`/`QZKSYKG2` are stated faithfully and `sorry`ed (giants; the HL
  proofs are ~1900 lines through `WQPRRDY`, `MXI_EXPLICIT`,
  `OMEGA_LIST_1_EXPLICIT_NEW`, `mcell2`/`mcell3`/`mcell4` unfolding).
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
explicit side condition `∀ j ≥ i-1, p j = j`. -/
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
  sorry

/- `MXI_EXPLICIT` (marchal2.hl:2516) is PA12's proved public theorem
(imported below); the unused private `mxiExplicit_p14` copy was deleted
DEDUP 2026-09-19. Under the `mcell3` regime the `mxi` point is realized on
the segment from `omegaListN V ul 2` to `omegaListN V ul 3` at distance
`sqrt 2` from `u0` (`SEGMENT_INTER_CBALL_LEMMA` + `@`-definition). -/

/-! ## The two QZKSYKG capstones (QZKSYKG.hl:266-2251) -/

/-- HOL `QZKSYKG1` (QZKSYKG.hl:244-253 concl, proof 266-320): a left action
of a permutation of `0..k-1` on a `barV V 3` list keeps it `barV`, provided
the cell `mcell k V ul` is nonempty.

HL proof shape: `k = 0, 1` — `PERMUTES_TRIVIAL` (`p = id`) +
`LEFT_ACTION_LIST_I`; `k = 4` — `mcell4` unfolding + `YIFVQDV_1`
(itself `sorry`ed in PackingAuto7); `k = 2, 3` — `mcell2`/`mcell3`
unfoldings + `YNHYJIT` (`ynhyjit_p14` above, possibly false under the weak
pointwise `permutes` encoding — same caveat). Every case therefore rests on
an upstream `sorry`/caveat, so the faithful statement is `sorry`ed here.
DISCHARGES: none (`QZKSYKG` has no `pack_concl` interface; the results feed
marchal3/KIZHLTL downstream). -/
theorem QZKSYKG1 {V : Set V3} {ul vl : List V3} {k : ℕ} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hne : mcell k V ul ≠ ∅)
    (hperm : permutes p (Set.Icc 0 (k - 1))) (hvl : vl = leftActionList p ul) :
    barV V 3 vl := by
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
the `k = 2, 3` cases again go through `YNHYJIT` (caveat above).
DISCHARGES: none (feeds marchal3/KIZHLTL downstream). -/
theorem QZKSYKG2 {V : Set V3} {ul : List V3} {k : ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
    mcell k V ul ⊆
      ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1))}) := by
  sorry

end Kepler.Text

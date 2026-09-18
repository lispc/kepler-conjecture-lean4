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

Proof status: cases `i = 0, 1` (`p` forced to `Equiv.refl`) and `i = 4`
(`mcell4` depends only on `setOfList`/`hl`) are proved via the tail-fixed
kit above; cases `i = 2, 3` remain `sorry`: they need the ported
`LEFT_ACTION_LIST_1_PROPERTIES`/`LEFT_ACTION_LIST_PROPERTIES`
(marchal2.hl:5848/4460) — `mxi`/`omegaListN` invariance under the
`{0,1}`-swap resp. the `S₃`-action, a genuine geometry bite. -/
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
  · -- i = 2: needs LEFT_ACTION_LIST_1_PROPERTIES (marchal2.hl:5848)
    sorry
  · -- i = 3: needs LEFT_ACTION_LIST_PROPERTIES (marchal2.hl:4460)
    sorry
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

NEEDS: `LEPJBDJ`/`LEPJBDJ_0` (owned by the PackingAuto11 worker) to
identify `V ∩ mcell k V ul` with the truncated list point set; the HL
proof unfolds `VX` through `cell_params` and applies them at
`(if k ≤ 3 then k else 4, ul)`. -/
theorem HDTFNFZ {V : Set V3} {ul : List V3} {k : ℕ} {v : V3} {X : Set V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hX : X = mcell k V ul) (hnull : ¬nullSet X) :
    VX V X = V ∩ X := by
  sorry

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
  · -- i = 3: needs LEFT_ACTION_LIST_PROPERTIES (marchal2.hl:4460)
    sorry
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
  sorry

/-- HOL `MCELL_2_PROPERTIES_lemma1` (URRPHBZ1.hl:366-589): every point of the
edge cell `mcell2` is within `hl (truncate_simplex 1 ul)` of the midpoint of
the first edge (drives the `BOUNDED_MCELL` case `k = 2`). -/
theorem MCELL_2_PROPERTIES_lemma1 {V : Set V3} {ul : List V3} {p : V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hp : p ∈ mcell2 V ul) :
    dist (midpoint ℝ (hdV ul) (hdV ul.tail)) p ≤ hl (truncateSimplex 1 ul) := by
  sorry

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

/-- Measurability of the `mcell2` wedge `aff_ge {u0, u1} {p, q}`.
NEEDS: an explicit wedge/bisector representation of `affGe` — the port's
closedness lemmas (`TopologyFan.closed_aff_ge_2_1`) require `¬Collinear3`
and cover only 2-1/1-2 shapes, and the `Affsign`-existence definition is
not directly measurable. Filled in when a general `affGe` Borel lemma
lands (Auto9/Auto11 merge). -/
private theorem measurableSet_affGe_wedge_p10 (u0 u1 p q : V3) :
    MeasurableSet (affGe {u0, u1} {p, q}) := by
  sorry

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


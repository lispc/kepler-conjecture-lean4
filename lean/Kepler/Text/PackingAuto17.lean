import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto14
import Kepler.Text.Polytope
import Mathlib
/-!
Packing chapter, Marchal-cells lane: cell clearance `URRPHBZ3` and the
distinct-cell theorem `AJRIPQN`.

HOL sources (VU KHAC KY, chapter "Packing"):
- `scripts/packing/URRPHBZ3.hl` (71 lines, 0 defs): the chapter capstone —
  away from the packing vertices a non-null Marchal cell keeps its distance:
  for `v` a packing point outside `VX V (mcell k V ul)` there is `t > 0`
  with `t < dist p v` for all `p` in the cell. HL proof: rewrite `VX` by
  `HDTFNFZ`, note `(V DIFF X)` is open (`CLOSED_MCELL`), take a `cball`
  around `v` inside it (`OPEN_CONTAINS_CBALL`), halve the radius.
- `scripts/packing/AJRIPQN.hl` (1051 lines, 4 `prove` items): two Marchal
  cells `mcell i V ul`, `mcell j V vl` (`i,j ∈ {0..4}`) whose intersection
  has positive volume must coincide (`i = j` and the cells are equal).
  The HL proof is a five-stage covering argument: (1) the intersection `S`
  is measurable/bounded and covered by finitely many closed-Voronoi pieces
  (`TIWWFYQ`, `DRUQUFE`, `KIUMVTC`, `BOUNDED_MCELL`), one of positive
  measure; (2) each closed Voronoi cell is covered by finitely many Rogers
  simplices rooted at `v` (`GLTVHUM`, `BARV_3_EXPLICIT`,
  `OMEGA_LIST_IN_VORONOI_LIST`, `BARV_SUBSET`), one piece `S2 ⊆ rogers V wl`
  of positive measure; (3) `S2` is trimmed to `S3` avoiding every *other*
  Rogers simplex meeting it (`DUUNHOR` kills the pairwise intersections,
  `MEASURE_NEGLIGIBLE_SYMDIFF` keeps the volume); (4) `S3` is covered by
  the five `mcell k V wl` (`SLTSTLO1`), one `S4` of positive measure; (5)
  off the null set of `SLTSTLO2` the cell index is unique, giving `S5`
  with `S5 ∩ mcell h V wl = ∅` for `h ≠ k`; a point `x ∈ S5` lies in
  `mcell i V ul ⊆ ⋃ rogers V (left_action_list p ul)` (`QZKSYKG2`), forces
  `rogers V kl = rogers V wl`, hence `mcell i V ul = mcell i V wl` by
  `RVFXZBU` + `DDZUPHJ`, and likewise `mcell j V vl = mcell j V wl`;
  uniqueness of the index at `x` gives `i = j = k`.

Encoding: HOL `real^3` ↔ `V3` (Kepler.Geom); `dist (a,b)` ↔ `dist a b`;
`ball`/`cball` ↔ `Metric.ball`/`Metric.closedBall`; `measurable` ↔
`MeasurableSet`; `vol`/`measure` ↔ `MeasureTheory.volume`; `NULLSET` ↔
`nullSet` (`volume X = 0`, PackingAuto2); `negligible` ↔ null/volume-zero
arguments; `aff_dim` ↔ `affDim` (Polytope, `∅ ↦ -1`); `bounded` ↔
`Bornology.IsBounded`; `left_action_list` ↔ `leftActionList`;
`permutes` ↔ the pointwise `PackingAuto2.permutes` (see the Auto10 caveat);
`truncate_simplex`/`omega_list`/`set_of_list` ↔ `truncateSimplex`/
`omegaListN`/`setOfList`.

Assembly status.
- `URRPHBZ3` is assembled honestly from Auto11's `LEPJBDJ`/`LEPJBDJ_0`
  (the private `hdtfnfz_p17` re-proves Auto10's sorried `HDTFNFZ`, whose
  missing ingredient landed in Auto11) plus Auto12's `CLOSED_MCELL`.
  DISCHARGES: PackingAuto2.URRPHBZ3_concl.
- `AJRIPQN`: the supporting lemmas `volPosLtAffDim3_p17`
  (`VOL_POS_LT_AFF_DIM_3`, via Mathlib `addHaar_affineSubspace`),
  `upTo4KyLemma_p17` (`UP_TO_4_KY_LEMMA`) and `finiteSetListLemma_p17`
  (`FINITE_SET_LIST_LEMMA`) are proved; the capstone `AJRIPQN` is stated
  faithfully and `sorry`ed (DISCHARGES: none — it has no `pack_concl`
  interface); see its docstring for the precise missing pieces.
- `qzksykg1_p17`/`qzksykg2_p17`: SHIMMED (2026-09-19) to the
  parallel-owned `PackingAuto14.QZKSYKG1`/`QZKSYKG2` via the new import
  (those remain `sorry`ed upstream in Auto14); delete the `_p17` copies at
  merge into Auto14's results.
- Imports: `Kepler.Text.PackingAuto2` (defs + pack_concl interfaces),
  `Kepler.Text.PackingAuto5` (KIUMVTC/TIWWFYQ/DRUQUFE/VORONOI_BALL2/
  BARV_SUBSET), `Kepler.Text.PackingAuto7` (Rogers kit),
  `Kepler.Text.PackingAuto8` (`BARV_3_EXPLICIT`),
  `Kepler.Text.PackingAuto10` (`MEASURABLE_MCELL`, `URRPHBZ1`,
  `BOUNDED_MCELL`, `RVFXZBU`), `Kepler.Text.PackingAuto11`
  (`LEPJBDJ`/`LEPJBDJ_0`), `Kepler.Text.PackingAuto12`
  (`MEASURABLE_ROGERS`, `CLOSED_MCELL`, `MCELL_EXPLICIT`),
  `Kepler.Text.PackingAuto13` (`SLTSTLO1`, `SLTSTLO2`, `DDZUPHJ`),
  `Kepler.Text.Polytope` (`affDim`), `Mathlib`.
-/


set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## URRPHBZ3.hl -/

/-- The `cell_params` pair of a non-null candidate cell `X = mcell k V ul`
satisfies the defining predicate (HL HDTFNFZ.hl:53-78: `SELECT_AX` applied
at the witness `((if k ≤ 3 then k else 4), ul)`, with `MCELL_EXPLICIT`
dispatching `k ≥ 4` to `mcell4`). -/
private theorem cellParams_spec_p17 {V : Set V3} {ul : List V3} {k : ℕ} {X : Set V3}
    (hbar : barV V 3 ul) (hX : X = mcell k V ul) :
    (cellParams V X).1 ≤ 4 ∧ barV V 3 (cellParams V X).2 ∧
      X = mcell (cellParams V X).1 V (cellParams V X).2 := by
  have hex : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 := by
    rcases Nat.lt_or_ge k 4 with hk | hk
    · exact ⟨(k, ul), by omega, hbar, hX⟩
    · refine ⟨(4, ul), le_refl 4, hbar, ?_⟩
      rw [hX, (MCELL_EXPLICIT k V ul).2.2.2.2 hk]
      rfl
  exact Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2) hex

/-- HOL `HDTFNFZ` (HDTFNFZ.hl:44-111): for a non-null cell `X = mcell k V ul`
the vertex set is `VX V X = V ∩ X`. Private `_p17` copy: Auto10's `HDTFNFZ`
is still `sorry`ed there, pending exactly the `LEPJBDJ`/`LEPJBDJ_0` pieces
that Auto11 has now discharged; the HL case split `cell_params V X = k',ul'`
is replaced by `cellParams_spec_p17`, the `k' = 0` branch goes through
`LEPJBDJ_0` (HL:79-92), the `k' > 0` branch through `LEPJBDJ` with the
empty-cell branch killed by `nullSet ∅` (HL:93-111). -/
private theorem hdtfnfz_p17 {V : Set V3} {ul : List V3} {k : ℕ} {X : Set V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hX : X = mcell k V ul) (hnull : ¬nullSet X) :
    VX V X = V ∩ X := by
  obtain ⟨h4, hbar', hX'⟩ := cellParams_spec_p17 hbar hX
  set N := cellParams V X with hN
  have hne : mcell N.1 V N.2 ≠ ∅ := by
    intro hc
    refine hnull ?_
    show volume X = 0
    rw [hX', hc]
    exact measure_empty
  have hvx : VX V X = (if N.1 = 0 then ∅
      else setOfList (truncateSimplex (N.1 - 1) N.2)) := by
    simp only [VX, if_neg hnull, ← hN]
  rw [hvx, hX']
  rcases Nat.eq_zero_or_pos N.1 with h0 | h0
  · rw [if_pos h0, h0, LEPJBDJ_0 V N.2 hsat hpack hbar']
  · rw [if_neg (by omega : N.1 ≠ 0),
      LEPJBDJ V N.2 N.1 hsat hpack hbar' (by omega) h4 hne]

/-- HOL `URRPHBZ3` (URRPHBZ3.hl:31-68): away from the packing vertices a
non-null Marchal cell has positive clearance.
DISCHARGES: PackingAuto2.URRPHBZ3_concl.

Assembly (HL:35-68). `HDTFNFZ` (the private `hdtfnfz_p17` above; HL:35-39)
turns `v ∈ V \ VX V X` into `v ∉ X`; the cell is closed (`CLOSED_MCELL`,
Auto12; HL:42-45) so the complement is open and a `Metric.ball` around `v`
fits inside (`Metric.isOpen_iff`; HL uses `OPEN_CONTAINS_CBALL` + `cball`);
half the radius is the clearance `t` (HL:46-68, `DIST_SYM` + arithmetic). -/
theorem URRPHBZ3 {V : Set V3} {ul : List V3} {k : ℕ} {v : V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hnull : ¬nullSet (mcell k V ul)) (hv : v ∈ V \ VX V (mcell k V ul)) :
    ∃ t : ℝ, t > 0 ∧ ∀ p ∈ mcell k V ul, t < dist p v := by
  have hhdt : VX V (mcell k V ul) = V ∩ mcell k V ul :=
    hdtfnfz_p17 hsat hpack hbar rfl hnull
  have hvX : v ∉ mcell k V ul := fun hc =>
    hv.2 (by rw [hhdt]; exact ⟨hv.1, hc⟩)
  obtain ⟨e, he, hsub⟩ := Metric.isOpen_iff.1
    ((CLOSED_MCELL V ul hsat hpack hbar k).isOpen_compl) v (by simpa using hvX)
  refine ⟨e / 2, by linarith, fun p hp => ?_⟩
  have hge : e ≤ dist p v := le_of_not_gt fun hcon =>
    hsub (Metric.mem_ball.2 hcon) hp
  linarith

/-! ## AJRIPQN.hl: supporting lemmas -/

/-- Measure-theoretic interface for the HL `MEASURABLE_MEASURE_POS_LT`
steps (`&0 < measure S <=> ~NULLSET S` for measurable `S`), used six times
in the AJRIPQN.hl covering argument. -/
private theorem measurePosIff_p17 {S : Set V3} (_hs : MeasurableSet S) :
    0 < volume S ↔ ¬nullSet S := by
  constructor
  · intro h hc
    rw [nullSet] at hc
    exact absurd hc h.ne'
  · intro h
    rcases eq_zero_or_pos (volume S) with hc | hc
    · exact absurd hc h
    · exact hc

/-- HOL `VOL_POS_LT_AFF_DIM_3` (AJRIPQN.hl:42-60): a measurable set of
positive volume is full-dimensional (`aff_dim S = 3`). HL: `AFF_DIM_LE_UNIV`
+ `COPLANAR_IMP_NEGLIGIBLE`; here: `affDim S = finrank (vectorSpan ℝ S)`, a
direction of rank `< 3` makes the affine span a proper affine subspace, null
by Mathlib `addHaar_affineSubspace`, and rank `3` forces
`vectorSpan = ⊤` (`Submodule.eq_top_of_finrank_eq`). -/
private theorem volPosLtAffDim3_p17 (S : Set V3) (hs : MeasurableSet S)
    (hv : 0 < volume S) : affDim S = 3 := by
  rcases Set.eq_empty_or_nonempty S with rfl | hne
  · rw [measure_empty] at hv
    exact absurd hv (by norm_num)
  · by_contra hcon
    have hne' : S ≠ ∅ := (Set.nonempty_iff_ne_empty).mp hne
    have hfr : (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) = affDim S := by
      rw [affDim, if_neg hne']
    have hV3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    have hle : Module.finrank ℝ (vectorSpan ℝ S) ≤ 3 := by
      simpa [hV3] using Submodule.finrank_le (vectorSpan ℝ S)
    rcases Nat.lt_or_ge (Module.finrank ℝ (vectorSpan ℝ S)) 3 with hlt' | h3
    · have htop : (vectorSpan ℝ S : Submodule ℝ V3) ≠ ⊤ := by
        intro htop
        rw [htop] at hlt'
        simp [finrank_top, hV3] at hlt'
      have htop_aff : (affineSpan ℝ S : AffineSubspace ℝ V3) ≠ ⊤ := by
        intro hE
        exact htop (AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 hE)
      have h0 : volume ((affineSpan ℝ S : AffineSubspace ℝ V3) : Set V3) = 0 :=
        MeasureTheory.Measure.addHaar_affineSubspace volume (affineSpan ℝ S) htop_aff
      have hmono : volume S ≤ volume ((affineSpan ℝ S : AffineSubspace ℝ V3) : Set V3) :=
        measure_mono (subset_affineSpan ℝ S)
      rw [h0] at hmono
      exact absurd hmono (not_le.mpr hv)
    · exact hcon (by rw [← hfr]; exact_mod_cast le_antisymm hle h3)

/-- HOL `UP_TO_4_KY_LEMMA` (AJRIPQN.hl:62-64). -/
private theorem upTo4KyLemma_p17 (i : ℕ) : i ≤ 4 ↔ i ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- HOL `FINITE_SET_LIST_LEMMA` (AJRIPQN.hl:66-84): the `barV`-shaped 4-point
lists drawn from a finite set form a finite set (HL: `FINITE_PRODUCT_DEPENDENT`
along `CONS`). -/
private theorem finiteSetListLemma_p17 {s : Set V3} (hs : s.Finite) :
    {y : List V3 | ∃ u0 ∈ s, ∃ u1 ∈ s, ∃ u2 ∈ s, ∃ u3 ∈ s, y = [u0, u1, u2, u3]}.Finite := by
  refine Set.Finite.subset (Set.Finite.image
    (fun q : V3 × V3 × V3 × V3 => [q.1, q.2.1, q.2.2.1, q.2.2.2])
    (hs.prod (hs.prod (hs.prod hs)))) ?_
  rintro y ⟨u0, hu0, u1, hu1, u2, hu2, u3, hu3, rfl⟩
  exact ⟨(u0, u1, u2, u3), ⟨hu0, hu1, hu2, hu3⟩, rfl⟩

/-! ## QZKSYKG kit (`_p17` copies; originals are parallel-owned) -/

/-- HOL `QZKSYKG1` (QZKSYKG.hl:244-253): a left action of a permutation of
`0..k-1` on a `barV V 3` list keeps it `barV`, provided `mcell k V ul ≠ ∅`.

SHIM (2026-09-19): the parallel-owned PackingAuto14 olean HAS landed in this
checkout, so the verbatim `_p17` copy discharges to
`Kepler.Text.PackingAuto14.QZKSYKG1` (still `sorry`ed upstream there — a
documented transitive shim, deleting the statement duplication; delete the
copy at merge when Auto14's giants land).
STATEMENT-FIX 项 20 (2026-09-30): 上游 `QZKSYKG1` 补 tail-fixedness `hfix`
前提（弱 permutes 编码下原陈述为假），本 shim 同步透传。 -/
private theorem qzksykg1_p17 {V : Set V3} {ul vl : List V3} {k : ℕ} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hne : mcell k V ul ≠ ∅)
    (hperm : permutes p (Set.Icc 0 (k - 1))) (hfix : ∀ j : ℕ, k ≤ j → p j = j)
    (hvl : vl = leftActionList p ul) :
    barV V 3 vl :=
  QZKSYKG1 hsat hpack hbar hk hne hperm hfix hvl

/-- HOL `QZKSYKG2` (QZKSYKG.hl:255-262): `mcell k V ul` is covered by the
union of the Rogers simplices of all left-action permutations of `ul` over
`0..k-1` (giant, ~1900 HL lines).

SHIM (2026-09-19): the parallel-owned PackingAuto14 olean HAS landed in this
checkout, so the verbatim `_p17` copy discharges to
`Kepler.Text.PackingAuto14.QZKSYKG2` (still `sorry`ed upstream there — a
documented transitive shim, deleting the statement duplication; delete the
copy at merge when Auto14's giants land).
STATEMENT-FIX 项 38 (2026-10-12): 上游 `QZKSYKG2` comprehension 补
tail-fixed 合取项 `∧ ∀ n, k ≤ n → p n = n`（HOL `permutes` 为
complement-fixing，azure/hol-light-nat/Library/permutations.ml:9；弱式并集
含 junk simplex，`p17_ajripqn_of_tailfix` 的 `hQ2` 无法从弱式供给），本
shim 同步透传（项 20 `qzksykg1_p17` 先例；全树无本 shim 代码调用点，同步
零波及）。 -/
private theorem qzksykg2_p17 {V : Set V3} {ul : List V3} {k : ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
    mcell k V ul ⊆
      ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧
          ∀ n : ℕ, k ≤ n → p n = n}) :=
  QZKSYKG2 hsat hpack hbar hk

/-! ### measure pigeonhole helpers -/

/-- A finite union of measure-zero sets is measure-zero (HL
`NEGLIGIBLE_UNIONS`, measure-side). -/
private theorem p17_sUnion_null {fam : Set (Set V3)} (hfin : fam.Finite)
    (h : ∀ T ∈ fam, volume T = 0) : volume (⋃₀ fam) = 0 := by
  have hle : volume (⋃₀ fam) ≤ ∑ T ∈ Set.Finite.toFinset hfin, volume T := by
    refine le_trans (measure_mono ?_) (measure_biUnion_finset_le _ _)
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Set.mem_sUnion.1 hx
    exact Set.mem_biUnion (by simpa using hT) hxT
  rw [Finset.sum_eq_zero (fun T hT => h T (by simpa using hT))] at hle
  simpa using le_antisymm hle zero_le

/-- Pigeonhole: a positive-measure set covered by a finite family has a
positive-measure member (HL `?S1 IN SPP /\ ~negligible S1` steps). -/
private theorem p17_pick_pos {X : Set V3} {fam : Set (Set V3)}
    (hcover : X ⊆ ⋃₀ fam) (hfin : fam.Finite) (hpos : 0 < volume X) :
    ∃ T ∈ fam, 0 < volume T := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ T ∈ fam, volume T = 0 := fun T hT =>
    le_antisymm (hcon T hT) zero_le
  have h1 : volume X ≤ 0 := (measure_mono hcover).trans_eq (p17_sUnion_null hfin hzero)
  have h2 : volume X = 0 := le_antisymm h1 zero_le
  exact absurd h2 (ne_of_gt hpos)

/-- Removing a measure-zero set does not decrease measure (HL
`MEASURE_NEGLIGIBLE_SYMDIFF` content; measurability-free). -/
private theorem p17_measure_sdiff_ge {s t : Set V3} (ht : volume t = 0) :
    volume s ≤ volume (s \ t) := by
  have hun : (s \ t) ∪ (s ∩ t) = s := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    by_cases hx : x ∈ t
    · by_cases hx' : x ∈ s
      · simp [hx, hx']
      · simp [hx, hx']
    · simp [hx]
  have h1 : volume s ≤ volume (s \ t) + volume (s ∩ t) := by
    conv_lhs => rw [← hun]
    exact (measure_union_le (s \ t) (s ∩ t) (μ := volume))
  have h2 : volume (s ∩ t) = 0 := by
    refine le_antisymm ?_ zero_le
    calc volume (s ∩ t) ≤ volume t := measure_mono (fun _ hx => hx.2)
      _ = 0 := ht
  rw [h2] at h1
  simpa using h1

/-! ### AJRIPQN.hl: shared geometric helpers -/

private theorem p17_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h2 := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h2
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h2
  refine h2.trans ?_
  calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

/-- HOL `COPLANAR_IMP_NEGLIGIBLE` content (Geom `Coplanar` form; PA24 keeps a
root-`Coplanar` twin): subsets of a coplanar set are Lebesgue-null. -/
private theorem p17_coplanar_null {s t : Set V3} (hcop : Coplanar s) (hsub : t ⊆ s) :
    volume t = 0 := by
  obtain ⟨u, v, w, hsp⟩ := hcop
  have hvs : vectorSpan ℝ ({u, v, w} : Set V3)
      = Submodule.span ℝ ({v - u, w - u} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show u ∈ ({u, v, w} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.subset_span ⟨v, by simp, rfl⟩
      · exact Submodule.subset_span ⟨w, by simp, rfl⟩
  have hne : (affineSpan ℝ ({u, v, w} : Set V3) : AffineSubspace ℝ V3) ≠ ⊤ := by
    intro htop
    have hdir : (affineSpan ℝ ({u, v, w} : Set V3)).direction = ⊤ := by
      rw [htop]; exact AffineSubspace.direction_top ℝ V3 V3
    have hle : Module.finrank ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction ≤ 2 := by
      rw [direction_affineSpan, hvs]
      exact p17_finrank_span_pair_le_two (v - u) (w - u)
    rw [hdir, finrank_top] at hle
    exact absurd hle (by norm_num)
  exact measure_mono_null (hsub.trans hsp)
    (Measure.addHaar_affineSubspace volume _ hne)

/-- Points of `voronoiList V ul` lie in the closed Voronoi cell of every list
entry (`voronoi_list` = `INTERS` of the entry cells). -/
private theorem p17_mem_voronoiList {V : Set V3} {ul : List V3} {z w : V3}
    (hz : z ∈ voronoiList V ul) (hw : w ∈ setOfList ul) : z ∈ voronoiClosed V w := by
  rw [voronoiList, voronoiSet] at hz
  exact Set.mem_sInter.1 hz (voronoiClosed V w) ⟨w, hw, rfl⟩

/-! ### Stage 1 (HL:108-244): pigeonhole over Voronoi cells -/

/-- AJRIPQN.hl:108-244, stage 1. The cell intersection is bounded
(`BOUNDED_MCELL`), so only finitely many packing points `v` carry a
`voronoiClosed V v` meeting it (`KIUMVTC`); the intersection is their union of
slices (`TIWWFYQ`), so one slice has positive measure. -/
private theorem p17_stage1 {V : Set V3} {ul vl : List V3} {i j : ℕ}
    (hs : saturated V) (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hvol : 0 < volume (mcell i V ul ∩ mcell j V vl)) :
    ∃ v : V3, v ∈ V ∧ ∃ S1 : Set V3, S1 ⊆ voronoiClosed V v ∧
      S1 ⊆ mcell i V ul ∩ mcell j V vl ∧ 0 < volume S1 := by
  have hb : Bornology.IsBounded (mcell i V ul ∩ mcell j V vl) :=
    (BOUNDED_MCELL V ul i hs hp hb1).subset (fun _ hx => hx.1)
  obtain ⟨a, haS⟩ := (Metric.isBounded_iff_subset_closedBall (0 : V3)).1 hb
  -- the finite family of nonempty slices
  have hidxsub : {v : V3 | v ∈ V ∧
      (voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)).Nonempty} ⊆
      V ∩ Metric.ball (0 : V3) (a + 2) := by
    rintro z ⟨hzV, ⟨x, hxV, hxS⟩⟩
    have hxn : dist x (0 : V3) ≤ a := Metric.mem_closedBall.1 (haS hxS)
    have hzd : dist x z < 2 := Metric.mem_ball.1 (VORONOI_BALL2 V z hs hxV)
    have hzd' : dist z x < 2 := by rw [dist_comm]; exact hzd
    refine ⟨hzV, Metric.mem_ball.2 ?_⟩
    have htri : dist z (0 : V3) ≤ dist z x + dist x (0 : V3) := dist_triangle z x 0
    linarith
  have hfamfin : ((fun v : V3 => voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)) ''
      {v : V3 | v ∈ V ∧ (voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)).Nonempty}).Finite :=
    Set.Finite.image _ (Set.Finite.subset (KIUMVTC (0 : V3) (a + 2) V hp) hidxsub)
  have hcover : (mcell i V ul ∩ mcell j V vl) ⊆ ⋃₀
      ((fun v : V3 => voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)) ''
        {v : V3 | v ∈ V ∧ (voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)).Nonempty}) := by
    intro x hx
    obtain ⟨v, hvV, hvx⟩ := TIWWFYQ V x hp hs
    exact Set.mem_sUnion.2 ⟨voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl),
      Set.mem_image_of_mem _ ⟨hvV, ⟨x, hvx, hx⟩⟩, ⟨hvx, hx⟩⟩
  have hchar : ∀ T ∈ (fun v : V3 => voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)) ''
      {v : V3 | v ∈ V ∧ (voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl)).Nonempty},
      ∃ v : V3, v ∈ V ∧ T = voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl) := by
    rintro T ⟨v, hv, rfl⟩
    exact ⟨v, hv.1, rfl⟩
  obtain ⟨T, hTin, hTpos⟩ := p17_pick_pos hcover hfamfin hvol
  obtain ⟨v, hvV, rfl⟩ := hchar T hTin
  exact ⟨v, hvV, voronoiClosed V v ∩ (mcell i V ul ∩ mcell j V vl),
    inter_subset_left, inter_subset_right, hTpos⟩

/-! ### Stage 2 (HL:248-451): pigeonhole over Rogers simplices rooted at v -/

/-- AJRIPQN.hl:248-451, stage 2. The Rogers simplices rooted at `v`
(`truncateSimplex 0 wl = [v]`) meeting `S1` are finitely many: a `barV V 3`
list is a 4-tuple of packing points all within 4 of `v` (the omega point of
the list is in every entry cell, and saturation keeps entry distances below
2), and 4-tuples from a ball-bounded set are finite (`KIUMVTC` +
`FINITE_SET_LIST_LEMMA`). The slices cover `S1` by `GLTVHUM_concl`, so one has
positive measure. -/
private theorem p17_stage2 {V : Set V3} {v : V3} {S1 : Set V3}
    (hs : saturated V) (hp : Packing V) (hv : v ∈ V)
    (hvol1 : 0 < volume S1) (hsub1 : S1 ⊆ voronoiClosed V v) :
    ∃ wl : List V3, barV V 3 wl ∧ ∃ S2 : Set V3, S2 ⊆ S1 ∧ S2 ⊆ rogers V wl ∧
      0 < volume S2 := by
  -- the 4-ball neighborhood carrying all rooted simplices
  have hHfin : ({z : V3 | z ∈ V ∧ dist z v ≤ 4} : Set V3).Finite :=
    Set.Finite.subset (KIUMVTC v 5 V hp) (by
      intro z hz
      exact ⟨hz.1, Metric.mem_ball.2 (by linarith [hz.2] : dist z v < 5)⟩)
  -- the index set of rooted simplices meeting S1 is finite
  have hidxfin : {wl : List V3 | barV V 3 wl ∧ truncateSimplex 0 wl = [v] ∧
      (rogers V wl ∩ S1).Nonempty}.Finite := by
    refine Set.Finite.subset (finiteSetListLemma_p17 hHfin) ?_
    rintro wl ⟨hbar, htr, ⟨x, hxR, hxS1⟩⟩
    obtain ⟨u0, u1, u2, u3, hkl⟩ := BARV_3_EXPLICIT V wl hbar
    subst hkl
    have h0 : truncateSimplex 0 [u0, u1, u2, u3] = [u0] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2
    rw [h0] at htr
    have hu0 : u0 = v := by simpa using htr
    have hVsub : setOfList [u0, u1, u2, u3] ⊆ V := BARV_SUBSET V 3 [u0, u1, u2, u3] hbar
    have hom : omegaList V [u0, u1, u2, u3] ∈ voronoiList V [u0, u1, u2, u3] :=
      OMEGA_LIST_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 hbar
    have homV : ∀ z ∈ setOfList [u0, u1, u2, u3],
        dist (omegaList V [u0, u1, u2, u3]) z < 2 := by
      intro z hz
      have hzcl : omegaList V [u0, u1, u2, u3] ∈ voronoiClosed V z :=
        p17_mem_voronoiList hom hz
      obtain ⟨y, hyV, hyd⟩ := hs (omegaList V [u0, u1, u2, u3])
      have hle := hzcl y hyV
      linarith
    have hbd : ∀ z ∈ setOfList [u0, u1, u2, u3], dist z v ≤ 4 := by
      intro z hz
      have hdω : dist z (omegaList V [u0, u1, u2, u3]) < 2 := by
        rw [dist_comm]
        exact homV z hz
      have hd0 : dist (omegaList V [u0, u1, u2, u3]) v < 2 := by
        rw [← hu0]
        exact homV u0 (by simp [setOfList])
      have htri : dist z v ≤ dist z (omegaList V [u0, u1, u2, u3]) +
        dist (omegaList V [u0, u1, u2, u3]) v := dist_triangle z _ v
      linarith
    exact ⟨u0, ⟨hVsub (by simp [setOfList]), hbd u0 (by simp [setOfList])⟩,
      u1, ⟨hVsub (by simp [setOfList]), hbd u1 (by simp [setOfList])⟩,
      u2, ⟨hVsub (by simp [setOfList]), hbd u2 (by simp [setOfList])⟩,
      u3, ⟨hVsub (by simp [setOfList]), hbd u3 (by simp [setOfList])⟩, rfl⟩
  -- the slices cover S1 (GLTVHUM_concl) and one is positive
  have hcover : S1 ⊆ ⋃₀ ((fun wl : List V3 => rogers V wl ∩ S1) ''
      {wl : List V3 | barV V 3 wl ∧ truncateSimplex 0 wl = [v] ∧
        (rogers V wl ∩ S1).Nonempty}) := by
    intro x hx
    obtain ⟨w, hbarw, hxR, htrw⟩ := (GLTVHUM_concl V v x ⟨hp, hs⟩ hv).1 (hsub1 hx)
    exact Set.mem_sUnion.2 ⟨rogers V w ∩ S1,
      Set.mem_image_of_mem _ ⟨hbarw, htrw, ⟨x, hxR, hx⟩⟩, ⟨hxR, hx⟩⟩
  obtain ⟨T, hTin, hTpos⟩ := p17_pick_pos hcover (Set.Finite.image _ hidxfin) hvol1
  obtain ⟨wl, hwl, rfl⟩ := hTin
  obtain ⟨hbarw, htrw, hx⟩ := hwl
  exact ⟨wl, hbarw, rogers V wl ∩ S1, inter_subset_right, inter_subset_left, hTpos⟩

/-! ### Stage 3 (HL:457-732): trim away the other Rogers simplices -/

/-- AJRIPQN.hl:457-732, stage 3. Remove from `S2` the intersection with every
`rogers V kl` that meets `S2` but differs from `rogers V wl`: those kl are
finitely many (their entries lie within 12 of `hdV wl`), their pairwise
intersections with `rogers V wl` are coplanar (`DUUNHOR_concl`) hence null, so
the trimmed set keeps positive measure and avoids all of them. -/
private theorem p17_stage3 {V : Set V3} {wl : List V3} {S2 : Set V3}
    (hs : saturated V) (hp : Packing V) (hbar : barV V 3 wl)
    (hvol2 : 0 < volume S2) (hsub2 : S2 ⊆ rogers V wl) :
    ∃ S3 : Set V3, S3 ⊆ S2 ∧ 0 < volume S3 ∧
      ∀ kl : List V3, barV V 3 kl → rogers V kl ≠ rogers V wl →
        S3 ∩ rogers V kl = ∅ := by
  obtain ⟨w0, w1, w2, w3, hwl⟩ := BARV_3_EXPLICIT V wl hbar
  subst hwl
  have hVsubW : setOfList [w0, w1, w2, w3] ⊆ V := BARV_SUBSET V 3 [w0, w1, w2, w3] hbar
  -- entries of a kl meeting S2 are within 12 of the root of wl
  have hidxsub : ∀ kl ∈ {kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty},
      ∃ a ∈ {z : V3 | z ∈ V ∧ dist z (hdV [w0, w1, w2, w3]) ≤ 12},
        ∃ b ∈ {z : V3 | z ∈ V ∧ dist z (hdV [w0, w1, w2, w3]) ≤ 12},
          ∃ c ∈ {z : V3 | z ∈ V ∧ dist z (hdV [w0, w1, w2, w3]) ≤ 12},
            ∃ d ∈ {z : V3 | z ∈ V ∧ dist z (hdV [w0, w1, w2, w3]) ≤ 12},
              kl = [a, b, c, d] := by
    rintro kl ⟨hbarK, ⟨p, hpK, hpS2⟩⟩
    obtain ⟨u0, u1, u2, u3, hkl⟩ := BARV_3_EXPLICIT V kl hbarK
    subst hkl
    have hVsubK : setOfList [u0, u1, u2, u3] ⊆ V := BARV_SUBSET V 3 [u0, u1, u2, u3] hbarK
    have hu0V : u0 ∈ V := hVsubK (by simp [setOfList])
    have hom : omegaList V [u0, u1, u2, u3] ∈ voronoiList V [u0, u1, u2, u3] :=
      OMEGA_LIST_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 hbarK
    have hd4 : ∀ z ∈ setOfList [u0, u1, u2, u3], dist z u0 ≤ 4 := by
      intro z hz
      have hzV : z ∈ V := hVsubK hz
      have homz : omegaList V [u0, u1, u2, u3] ∈ voronoiClosed V z :=
        p17_mem_voronoiList hom hz
      have hom0 : omegaList V [u0, u1, u2, u3] ∈ voronoiClosed V u0 :=
        p17_mem_voronoiList hom (by simp [setOfList])
      obtain ⟨y, hyV, hyd⟩ := hs (omegaList V [u0, u1, u2, u3])
      have h1 : dist (omegaList V [u0, u1, u2, u3]) z ≤
        dist (omegaList V [u0, u1, u2, u3]) y := homz y hyV
      have h2 : dist (omegaList V [u0, u1, u2, u3]) u0 ≤
        dist (omegaList V [u0, u1, u2, u3]) y := hom0 y hyV
      have hwz : dist (omegaList V [u0, u1, u2, u3]) z < 2 := by linarith
      have hw0 : dist (omegaList V [u0, u1, u2, u3]) u0 < 2 := by linarith
      have hzω : dist z (omegaList V [u0, u1, u2, u3]) < 2 := by
        rw [dist_comm]; exact hwz
      have h3 : dist z u0 ≤ dist z (omegaList V [u0, u1, u2, u3]) +
        dist (omegaList V [u0, u1, u2, u3]) u0 := dist_triangle z _ _
      linarith
    have htr0K : truncateSimplex 0 [u0, u1, u2, u3] = [u0] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2
    have hpKu0 : p ∈ voronoiClosed V u0 :=
      (GLTVHUM_concl V u0 p ⟨hp, hs⟩ hu0V).2 ⟨[u0, u1, u2, u3], hbarK, hpK, htr0K⟩
    have hpW : p ∈ rogers V [w0, w1, w2, w3] := hsub2 hpS2
    have htr0W : truncateSimplex 0 [w0, w1, w2, w3] = [hdV [w0, w1, w2, w3]] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_0 w0 w1 w2 w3).2.2.2
    have hpW0 : p ∈ voronoiClosed V (hdV [w0, w1, w2, w3]) :=
      (GLTVHUM_concl V (hdV [w0, w1, w2, w3]) p ⟨hp, hs⟩
        (hVsubW (show w0 ∈ setOfList [w0, w1, w2, w3] from (by simp [setOfList])))).2
        ⟨[w0, w1, w2, w3], hbar, hpW, htr0W⟩
    obtain ⟨yp, hypV, hypd⟩ := hs p
    have hpu0 : dist p u0 ≤ dist p yp := hpKu0 yp hypV
    have hdu0p : dist u0 p ≤ 4 := by
      rw [dist_comm]; linarith
    have hpw0 : dist p (hdV [w0, w1, w2, w3]) ≤ dist p yp := hpW0 yp hypV
    have hdpw0 : dist p (hdV [w0, w1, w2, w3]) ≤ 4 := by linarith
    have h12 : ∀ z ∈ setOfList [u0, u1, u2, u3],
        dist z (hdV [w0, w1, w2, w3]) ≤ 12 := by
      intro z hz
      have ht1 : dist z (hdV [w0, w1, w2, w3]) ≤
        dist z u0 + dist u0 (hdV [w0, w1, w2, w3]) :=
        dist_triangle z u0 (hdV [w0, w1, w2, w3])
      have ht2 : dist u0 (hdV [w0, w1, w2, w3]) ≤
        dist u0 p + dist p (hdV [w0, w1, w2, w3]) :=
        dist_triangle u0 p (hdV [w0, w1, w2, w3])
      linarith [hd4 z hz, ht1, ht2, hdu0p, hdpw0]
    exact ⟨u0, ⟨hu0V, h12 u0 (by simp [setOfList])⟩,
      u1, ⟨hVsubK (by simp [setOfList]), h12 u1 (by simp [setOfList])⟩,
      u2, ⟨hVsubK (by simp [setOfList]), h12 u2 (by simp [setOfList])⟩,
      u3, ⟨hVsubK (by simp [setOfList]), h12 u3 (by simp [setOfList])⟩, rfl⟩
  have hHfin : ({z : V3 | z ∈ V ∧ dist z (hdV [w0, w1, w2, w3]) ≤ 12} : Set V3).Finite :=
    Set.Finite.subset (KIUMVTC (hdV [w0, w1, w2, w3]) 15 V hp) (by
      intro z hz
      exact ⟨hz.1, Metric.mem_ball.2 (by
        linarith [hz.2] : dist z (hdV [w0, w1, w2, w3]) < 15)⟩)
  have hidxfin : {kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty}.Finite :=
    Set.Finite.subset (finiteSetListLemma_p17 hHfin) hidxsub
  -- the trimmed set
  have hbadnull : ∀ T ∈ (fun kl : List V3 => rogers V kl ∩ rogers V [w0, w1, w2, w3]) ''
      ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
        {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]}),
      volume T = 0 := by
    rintro T ⟨kl, hkl, rfl⟩
    obtain ⟨hklidx, hkln⟩ := hkl
    exact p17_coplanar_null (DUUNHOR_concl V kl [w0, w1, w2, w3] hp hs hklidx.1 hbar
      (fun h => hkln h)) (subset_refl _)
  have hidxbadfin : ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
      {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]}).Finite :=
    Set.Finite.subset hidxfin (fun x hx => ((Set.mem_sdiff x).1 hx).1)
  have hunion : ⋃₀ ((fun kl : List V3 => rogers V kl ∩ rogers V [w0, w1, w2, w3]) ''
      ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
        {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]})) ⊆
      rogers V [w0, w1, w2, w3] := by
    rintro x ⟨T, ⟨kl, hkl, rfl⟩, hxT⟩
    exact hxT.2
  have hXnull : volume (rogers V [w0, w1, w2, w3] ∩ ⋃₀
      ((fun kl : List V3 => rogers V kl ∩ rogers V [w0, w1, w2, w3]) ''
        ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
          {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]}))) = 0 := by
    refine le_antisymm ?_ zero_le
    have h1 : volume (rogers V [w0, w1, w2, w3] ∩ ⋃₀
        ((fun kl : List V3 => rogers V kl ∩ rogers V [w0, w1, w2, w3]) ''
          ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
            {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]}))) ≤
        volume (⋃₀ ((fun kl : List V3 => rogers V kl ∩ rogers V [w0, w1, w2, w3]) ''
          ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
            {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]}))) :=
      measure_mono (fun _ hx => hx.2)
    rw [p17_sUnion_null (Set.Finite.image _ hidxbadfin) hbadnull] at h1
    exact h1
  refine ⟨S2 \ (rogers V [w0, w1, w2, w3] ∩ ⋃₀
    ((fun kl : List V3 => rogers V kl ∩ rogers V [w0, w1, w2, w3]) ''
      ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
        {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]}))),
    Set.sdiff_subset, lt_of_lt_of_le hvol2 (p17_measure_sdiff_ge hXnull), ?_⟩
  intro kl hbarK hne
  by_contra hcon
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hcon
  obtain ⟨hxS3, hxK⟩ := hx
  have hxS2 : x ∈ S2 := ((Set.mem_sdiff x).1 hxS3).1
  have hxW : x ∈ rogers V [w0, w1, w2, w3] := hsub2 hxS2
  have hklidx : kl ∈ ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} :
      Set (List V3)) := ⟨hbarK, ⟨x, hxK, hxS2⟩⟩
  have hxX : x ∈ rogers V [w0, w1, w2, w3] ∩ ⋃₀
      ((fun kll : List V3 => rogers V kll ∩ rogers V [w0, w1, w2, w3]) ''
        ({kl : List V3 | barV V 3 kl ∧ (rogers V kl ∩ S2).Nonempty} \
          {zl : List V3 | rogers V zl = rogers V [w0, w1, w2, w3]})) :=
    ⟨hxW, Set.mem_sUnion.2 ⟨rogers V kl ∩ rogers V [w0, w1, w2, w3],
      Set.mem_image_of_mem _ ⟨hklidx, hne⟩, ⟨hxK, hxW⟩⟩⟩
  exact ((Set.mem_sdiff x).1 hxS3).2 hxX

/-! ### Stage 4 (HL:737-837): pigeonhole over the five Marchal cells -/

/-- AJRIPQN.hl:737-837, stage 4. `S3 ⊆ rogers V wl` is covered by the five
cells `mcell k V wl` (`SLTSTLO1`), so a positive-measure `S4` sits inside one
of them. -/
private theorem p17_stage4 {V : Set V3} {wl : List V3} {S3 : Set V3}
    (hs : saturated V) (hp : Packing V) (hbar : barV V 3 wl)
    (hvol3 : 0 < volume S3) (hsub3 : S3 ⊆ rogers V wl) :
    ∃ k : ℕ, k ≤ 4 ∧ ∃ S4 : Set V3, S4 ⊆ S3 ∧ S4 ⊆ mcell k V wl ∧ 0 < volume S4 := by
  have hSPfin : {k : ℕ | k ≤ 4 ∧ (mcell k V wl ∩ S3).Nonempty}.Finite :=
    Set.Finite.subset (Set.finite_le_nat 4) (fun k hk => hk.1)
  have hcover : S3 ⊆ ⋃₀ ((fun k : ℕ => mcell k V wl ∩ S3) ''
    {k : ℕ | k ≤ 4 ∧ (mcell k V wl ∩ S3).Nonempty}) := by
    intro x hx
    obtain ⟨i, hi4, hxi⟩ := SLTSTLO1 V wl x hs hp hbar (hsub3 hx)
    exact Set.mem_sUnion.2 ⟨mcell i V wl ∩ S3,
      Set.mem_image_of_mem _ ⟨hi4, ⟨x, hxi, hx⟩⟩, ⟨hxi, hx⟩⟩
  obtain ⟨T, hTin, hTpos⟩ := p17_pick_pos hcover (Set.Finite.image _ hSPfin) hvol3
  obtain ⟨k, hkin, rfl⟩ := hTin
  exact ⟨k, hkin.1, mcell k V wl ∩ S3, inter_subset_right, inter_subset_left, hTpos⟩

/-! ### Stage 5 (HL:842-896): uniqueness off a null set -/

/-- AJRIPQN.hl:842-896, stage 5a. Removing the SLTSTLO2 null set keeps
positive measure and pins the cell index: off `Z` a point of `rogers V wl`
lies in exactly one `mcell h V wl` (`h ≤ 4`), so `S4 \ Z` misses all `h ≠ k`. -/
private theorem p17_stage5 {V : Set V3} {wl : List V3} {S4 : Set V3} {k : ℕ}
    (hs : saturated V) (hp : Packing V) (hbar : barV V 3 wl) (hk : k ≤ 4)
    (hvol4 : 0 < volume S4) (hsub4 : S4 ⊆ rogers V wl ∩ mcell k V wl)
    (hZ : ∃ Z : Set V3, volume Z = 0 ∧ ∀ p : V3, p ∈ rogers V wl \ Z →
      ∃! h : ℕ, h ≤ 4 ∧ p ∈ mcell h V wl) :
    ∃ S5 : Set V3, S5 ⊆ S4 ∧ S5 ⊆ mcell k V wl ∧ 0 < volume S5 ∧
      ∀ h : ℕ, h ≤ 4 → h ≠ k → S5 ∩ mcell h V wl = ∅ := by
  obtain ⟨Z, hZnull, hZuniq⟩ := hZ
  refine ⟨S4 \ Z, Set.sdiff_subset, ?_,
    lt_of_lt_of_le hvol4 (p17_measure_sdiff_ge hZnull), ?_⟩
  · intro x hx
    exact (hsub4 ((Set.mem_sdiff x).1 hx).1).2
  · intro h hh4 hhk
    by_contra hcon
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hcon
    obtain ⟨⟨hxS4, hxZ⟩, hxh⟩ := hx
    obtain ⟨i', hi'⟩ := hZuniq x ⟨(hsub4 hxS4).1, hxZ⟩
    have hki : k = i' := hi'.2 k ⟨hk, (hsub4 hxS4).2⟩
    have hhi : h = i' := hi'.2 h ⟨hh4, hxh⟩
    rw [hhi, ← hki] at hhk
    exact hhk rfl

/-! ### Assembly: AJRIPQN from its five stages and the upstream pieces -/

/-- The full AJRIPQN covering assembly (HL:89-1048), parameterized over the
five upstream pieces that are still open in their home files (PA13
`SLTSTLO2`/`DDZUPHJ`, PA10 `RVFXZBU`, PA14 `QZKSYKG1`/`QZKSYKG2`). Every
hypothesis is a verbatim-or-stronger form of a frozen upstream statement; when
the upstreams land, the capstone `AJRIPQN` closes by direct application.

Note on `hQ2`: HOL's `permutes` carries tail-fixedness, so the coverage
quantifies over tail-fixed permutations; the frozen weak-`permutes` encoding
of PA14's `QZKSYKG2` is NOT enough to satisfy `hQ2` (a junk tail cannot be
handed to `hQ1`, which needs `∀ n ≥ k, p n = n`). `hQ2` is the faithful HOL
content; PA14's statement needs the SF-20-style `hfix` in the comprehension. -/
private theorem p17_ajripqn_of_pieces {V : Set V3} {ul vl : List V3} {i j : ℕ}
    (hs : saturated V) (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hi : i ≤ 4) (hj : j ≤ 4)
    (hvol : 0 < volume (mcell i V ul ∩ mcell j V vl))
    (hSLT2 : ∀ w : List V3, barV V 3 w → ∃ Z : Set V3, volume Z = 0 ∧
      ∀ p : V3, p ∈ rogers V w \ Z → ∃! h : ℕ, h ≤ 4 ∧ p ∈ mcell h V w)
    (hQ1 : ∀ (w : List V3) (k : ℕ) (p : Equiv.Perm ℕ), barV V 3 w → k ≤ 4 →
      mcell k V w ≠ ∅ → permutes p (Set.Icc 0 (k - 1)) →
      (∀ n : ℕ, k ≤ n → p n = n) → barV V 3 (leftActionList p w))
    (hQ2 : ∀ (w : List V3) (k : ℕ), barV V 3 w → k ≤ 4 →
      mcell k V w ⊆ ⋃₀ ((fun p => rogers V (leftActionList p w)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧
          ∀ n : ℕ, k ≤ n → p n = n}))
    (hRV : ∀ (w : List V3) (k : ℕ) (p : Equiv.Perm ℕ), barV V 3 w → k ≤ 4 →
      permutes p (Set.Icc 0 (k - 1)) → (∀ n : ℕ, k ≤ n → p n = n) →
      mcell k V (leftActionList p w) = mcell k V w)
    (hDD : ∀ (w t : List V3) (k : ℕ), k ≤ 4 → barV V 3 w → barV V 3 t →
      rogers V w = rogers V t → affDim (rogers V w) = 3 → mcell k V w ≠ ∅ →
      mcell k V w = mcell k V t) :
    i = j ∧ mcell i V ul = mcell j V vl := by
  -- stages 1-5 build a nonempty S5 off the SLTSTLO2 null set
  obtain ⟨v, hvV, S1, hS1cl, hS1cell, hS1pos⟩ := p17_stage1 hs hp hb1 hb2 hvol
  obtain ⟨wl, hbarw, S2, hS2S1, hS2R, hS2pos⟩ :=
    p17_stage2 hs hp hvV hS1pos hS1cl
  obtain ⟨S3, hS3S2, hS3pos, hS3disj⟩ := p17_stage3 hs hp hbarw hS2pos hS2R
  obtain ⟨k, hk4, S4, hS4S3, hS4cell, hS4pos⟩ :=
    p17_stage4 hs hp hbarw hS3pos (hS3S2.trans hS2R)
  obtain ⟨S5, hS5S4, hS5cell, hS5pos, hS5disj⟩ :=
    p17_stage5 hs hp hbarw hk4 hS4pos
      (fun x hx => ⟨hS2R (hS3S2 (hS4S3 hx)), hS4cell hx⟩) (hSLT2 wl hbarw)
  have hS5R : S5 ⊆ rogers V wl := fun x hx => hS2R (hS3S2 (hS4S3 (hS5S4 hx)))
  have hS5ij : S5 ⊆ mcell i V ul ∩ mcell j V vl := fun x hx =>
    hS1cell (hS2S1 (hS3S2 (hS4S3 (hS5S4 hx))))
  rcases Set.eq_empty_or_nonempty S5 with hE | ⟨x₀, hx₀⟩
  · rw [hE, measure_empty] at hS5pos
    exact absurd hS5pos (by norm_num)
  have hx₀i : x₀ ∈ mcell i V ul := (hS5ij hx₀).1
  have hx₀j : x₀ ∈ mcell j V vl := (hS5ij hx₀).2
  -- coverage for ul: a tail-fixed left action carrying x₀ in its Rogers simplex
  obtain ⟨p, hpIcc, hpfix, hx₀R⟩ :
      ∃ p : Equiv.Perm ℕ, permutes p (Set.Icc 0 (i - 1)) ∧
        (∀ n : ℕ, i ≤ n → p n = n) ∧ x₀ ∈ rogers V (leftActionList p ul) := by
    have hxu := hQ2 ul i hb1 hi hx₀i
    rw [Set.mem_sUnion] at hxu
    obtain ⟨T, ⟨p, hpS, rfl⟩, hxT⟩ := hxu
    exact ⟨p, hpS.1, hpS.2, hxT⟩
  have hnei : mcell i V ul ≠ ∅ := fun hE => by
    rw [hE] at hx₀i
    exact Set.notMem_empty x₀ hx₀i
  have hbarK : barV V 3 (leftActionList p ul) :=
    hQ1 ul i p hb1 hi hnei hpIcc hpfix
  -- the stage-3 disjointness forces the same Rogers simplex
  have hReq : rogers V (leftActionList p ul) = rogers V wl := by
    by_contra hneq
    have hE := hS3disj (leftActionList p ul) hbarK hneq
    have hcontra : x₀ ∈ S3 ∩ rogers V (leftActionList p ul) :=
      ⟨hS4S3 (hS5S4 hx₀), hx₀R⟩
    rw [hE] at hcontra
    exact Set.notMem_empty x₀ hcontra
  have hRVi : mcell i V (leftActionList p ul) = mcell i V ul := hRV ul i p hb1 hi hpIcc hpfix
  have hdim : affDim (rogers V wl) = 3 :=
    volPosLtAffDim3_p17 (rogers V wl) (MEASURABLE_ROGERS V wl hs hp hbarw)
      (lt_of_lt_of_le hS5pos (measure_mono hS5R))
  have hneik : mcell i V (leftActionList p ul) ≠ ∅ := by
    rw [hRVi]
    exact hnei
  have hdimK : affDim (rogers V (leftActionList p ul)) = 3 := by
    rw [hReq]
    exact hdim
  have hDDi : mcell i V (leftActionList p ul) = mcell i V wl :=
    hDD (leftActionList p ul) wl i hi hbarK hbarw hReq hdimK hneik
  have hcelli : mcell i V ul = mcell i V wl := hRVi.symm.trans hDDi
  -- likewise for vl
  obtain ⟨q, hqIcc, hqfix, hx₀R2⟩ :
      ∃ q : Equiv.Perm ℕ, permutes q (Set.Icc 0 (j - 1)) ∧
        (∀ n : ℕ, j ≤ n → q n = n) ∧ x₀ ∈ rogers V (leftActionList q vl) := by
    have hxu := hQ2 vl j hb2 hj hx₀j
    rw [Set.mem_sUnion] at hxu
    obtain ⟨T, ⟨q, hqS, rfl⟩, hxT⟩ := hxu
    exact ⟨q, hqS.1, hqS.2, hxT⟩
  have hnej : mcell j V vl ≠ ∅ := fun hE => by
    rw [hE] at hx₀j
    exact Set.notMem_empty x₀ hx₀j
  have hbarSl : barV V 3 (leftActionList q vl) :=
    hQ1 vl j q hb2 hj hnej hqIcc hqfix
  have hReq2 : rogers V (leftActionList q vl) = rogers V wl := by
    by_contra hneq
    have hE := hS3disj (leftActionList q vl) hbarSl hneq
    have hcontra : x₀ ∈ S3 ∩ rogers V (leftActionList q vl) :=
      ⟨hS4S3 (hS5S4 hx₀), hx₀R2⟩
    rw [hE] at hcontra
    exact Set.notMem_empty x₀ hcontra
  have hRVj : mcell j V (leftActionList q vl) = mcell j V vl := hRV vl j q hb2 hj hqIcc hqfix
  have hnejk : mcell j V (leftActionList q vl) ≠ ∅ := by
    rw [hRVj]
    exact hnej
  have hdimSl : affDim (rogers V (leftActionList q vl)) = 3 := by
    rw [hReq2]
    exact hdim
  have hDDj : mcell j V (leftActionList q vl) = mcell j V wl :=
    hDD (leftActionList q vl) wl j hj hbarSl hbarw hReq2 hdimSl hnejk
  have hcellj : mcell j V vl = mcell j V wl := hRVj.symm.trans hDDj
  -- the indices agree with k
  have hx₀iw : x₀ ∈ mcell i V wl := by rw [← hcelli]; exact hx₀i
  have hx₀jw : x₀ ∈ mcell j V wl := by rw [← hcellj]; exact hx₀j
  have hik : i = k := by
    by_contra hcon
    have hE := hS5disj i hi hcon
    have hcontra : x₀ ∈ S5 ∩ mcell i V wl := ⟨hx₀, hx₀iw⟩
    rw [hE] at hcontra
    exact Set.notMem_empty x₀ hcontra
  have hjk : j = k := by
    by_contra hcon
    have hE := hS5disj j hj hcon
    have hcontra : x₀ ∈ S5 ∩ mcell j V wl := ⟨hx₀, hx₀jw⟩
    rw [hE] at hcontra
    exact Set.notMem_empty x₀ hcontra
  refine ⟨hik.trans hjk.symm, ?_⟩
  rw [hcelli, hcellj, hik, hjk]

/-- The capstone step, isolated: the frozen `AJRIPQN` interface (the `≤ 4` /
measure conversions) reduces to the five-stage assembly plus the frozen
PA13/PA10/PA14 statements and exactly one assumption — the tail-fixed
coverage `hQ2`, i.e. PA14 `QZKSYKG2` with the HOL-faithful comprehension.
Flyspeck `permutes` (azure/hol-light-nat/Library/permutations.ml:9) is a
complement-fixing bijection (`!x. ~(x IN s) ==> p x = x` conjunct;
`PERMUTES_TRIVIAL`: `p permutes 0..0 <=> p = I`), so the frozen weak
comprehension of PA14 `QZKSYKG2` does not suffice: junk-tail lists enter the
union, and neither `QZKSYKG1` nor `RVFXZBU` can consume them. This is a
STATEMENT-FIX candidate mirroring SF-20: once the comprehension conjunct
`∧ ∀ n, k ≤ n → p n = n` lands in PA14 `QZKSYKG2` (statement-only change;
its body stays open upstream, sharing the two marchal2 blockers
LEFT_ACTION_LIST_1_PROPERTIES marchal2.hl:5848 and
LEFT_ACTION_LIST_PROPERTIES marchal2.hl:4460 with `RVFXZBU`'s i = 2/3
cases and `QZKSYKG1`'s k ≤ 3 case), the capstone `AJRIPQN` below closes by
`exact p17_ajripqn_of_tailfix … (QZKSYKG2-with-fixed-comprehension …)` —
consuming the open-body PA13/PA10/PA14 statements as in-tree debt (the
SF-20 shim precedent; verify with `lake build`, not env-lean).

Upstream status corrected 2026-10-12 (supersedes the stale bullets in the
capstone docstring below): `TIWWFYQ` (PA5:663) and `SLTSTLO1` (PA13:597)
are proved and already consumed by stages 1/4; `RVFXZBU` (PA10:197)
carries the tail-fixedness hypothesis itself (PA10:183 complement-fixing
ruling); `SLTSTLO2` (PA13:820) takes only `(V w)` — saturated/packing/barV
sit inside the ∃ body. -/
private theorem p17_ajripqn_of_tailfix (V : Set V3) (ul vl : List V3) (i j : ℕ)
    (hs : saturated V) (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hi : i ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hj : j ∈ ({0, 1, 2, 3, 4} : Set ℕ))
    (hvol : ¬nullSet (mcell i V ul ∩ mcell j V vl))
    (hQ2 : ∀ (w : List V3) (k : ℕ), barV V 3 w → k ≤ 4 →
      mcell k V w ⊆ ⋃₀ ((fun p => rogers V (leftActionList p w)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧
          ∀ n : ℕ, k ≤ n → p n = n})) :
    i = j ∧ mcell i V ul = mcell j V vl := by
  refine p17_ajripqn_of_pieces hs hp hb1 hb2 ((upTo4KyLemma_p17 i).2 hi)
    ((upTo4KyLemma_p17 j).2 hj)
    ((measurePosIff_p17 ((MEASURABLE_MCELL V ul i hs hp hb1).inter
      (MEASURABLE_MCELL V vl j hs hp hb2))).2 hvol)
    (fun w hbw => by
      obtain ⟨Z, hZ⟩ := SLTSTLO2 V w
      have key : ∀ q : V3, q ∈ rogers V w \ Z → ∃! h : ℕ, h ≤ 4 ∧ q ∈ mcell h V w :=
        fun q hq => (hZ q hs hp hbw).2 hq
      exact ⟨Z, (hZ (0 : V3) hs hp hbw).1, key⟩)
    (fun w k p hbw hk4 hne hperm hfix =>
      QZKSYKG1 hs hp hbw ((upTo4KyLemma_p17 k).1 hk4) hne hperm hfix rfl)
    hQ2
    (fun w k p hbw hk4 hperm hfix =>
      RVFXZBU ((upTo4KyLemma_p17 k).1 hk4) hs hp hbw hperm hfix)
    (fun w t k hk4 hbw hbt hreq hdim hne =>
      DDZUPHJ V w t k hs hp hk4 hbw hbt hreq hdim hne)

/-! ## AJRIPQN.hl: main theorem -/

/- UPDATE 2026-10-12 (AJRIPQN wave). The five-stage covering assembly is now
proved in this file, as `p17_ajripqn_of_pieces` above: stages 1-4 (measure
pigeonhole over Voronoi cells; over rooted Rogers simplices; the DUUNHOR trim;
the SLTSTLO1 cell-index pinning) are unconditional, and stage 5 plus the final
identification are parameterized over the five upstream statements. Closing
the capstone = one application of `p17_ajripqn_of_pieces` with

- `hvol` := `(measurePosIff_p17 ((MEASURABLE_MCELL V ul i hs hp hb1).inter
  (MEASURABLE_MCELL V vl j hs hp hb2))).2 hvol`,
- `hi`/`hj` := `(upTo4KyLemma_p17 i).1` / `(upTo4KyLemma_p17 j).1`,
- `hSLT2` := per-`w` destructure of `SLTSTLO2 V w` (PA13; statement as-is),
- `hQ1` := `QZKSYKG1` (PA14; statement as-is),
- `hRV` := `RVFXZBU` (PA10; statement as-is),
- `hDD` := `DDZUPHJ` (PA13; statement as-is),
- `hQ2` := PA14 `QZKSYKG2` **in the tail-fixed (HOL-faithful) form** - the
  frozen weak-`permutes` comprehension does NOT suffice (a junk tail cannot be
  handed to `QZKSYKG1`, whose `hfix` is already part of its frozen statement);
  this is a STATEMENT-FIX candidate mirroring SF-20. -/


/-- HOL `AJRIPQN` (AJRIPQN.hl:32-37, proof 89-1048): two Marchal cells of
index `≤ 4` whose intersection has positive volume are equal.

`sorry`ed capstone (it has NO `pack_concl` interface; DISCHARGES: none).
The supporting chain proved in this file: `measurePosIff_p17`
(`MEASURABLE_MEASURE_POS_LT` interface), `volPosLtAffDim3_p17`
(`VOL_POS_LT_AFF_DIM_3`, feeds `DDZUPHJ`'s `affDim = 3` side condition),
`upTo4KyLemma_p17` (`UP_TO_4_KY_LEMMA`), `finiteSetListLemma_p17`
(`FINITE_SET_LIST_LEMMA`), `qzksykg1_p17`/`qzksykg2_p17` (Auto14 copies).

Missing pieces (all statements importable; internal `sorry` upstream):
- `TIWWFYQ` (PackingAuto5:581, sorry): every point lies in a closed Voronoi
  cell — stage 1 covering.
- CLOSED (2026-10-08): `GLTVHUM_concl` is term-proved in place
  (PackingAuto2:3458; twin `PackingAuto6.GLTVHUM`): closed Voronoi cell =
  union of Rogers simplices rooted at `u0` — stage 2 covering.
- CLOSED (2026-10-08): `DUUNHOR_concl` is term-proved in place
  (PackingAuto2:3500 r2 form; twin `PackingAuto6.DUUNHOR`); the
  `Coplanar`-implies-null bridge remains open — distinct Rogers simplices
  meet in a null set — stage 3 trimming
  (with `MEASURE_NEGLIGIBLE_SYMDIFF`, HL:646-732).
- `SLTSTLO1` (PackingAuto13:307, sorry): Rogers simplex covered by
  `mcell 0..4 V wl` — stage 4 covering.
- `SLTSTLO2` (PackingAuto13:333, sorry): the unique-cell null set `Z` —
  stage 5 refinement `S5 = S4 \ Z`.
- `RVFXZBU` (PackingAuto10:79, sorry, weak-`permutes` caveat):
  `mcell i V kl = mcell i V ul` for `kl = left_action_list p ul`.
- `DDZUPHJ` (PackingAuto13:362, sorry): same Rogers simplex + positive
  dimension ⇒ `mcell i V kl = mcell i V wl`.
- `qzksykg1_p17`/`qzksykg2_p17` (above, Auto14 copies).

Proved and consumed as-is: `MEASURABLE_MCELL`/`URRPHBZ1`/`BOUNDED_MCELL`
(PackingAuto10), `MEASURABLE_ROGERS`/`CLOSED_MCELL`/`MCELL_EXPLICIT`
(PackingAuto12), `DRUQUFE`/`VORONOI_BALL2`/`KIUMVTC`/`BARV_SUBSET`/
`OMEGA_LIST_IN_VORONOI_LIST` (PackingAuto5), `BARV_3_EXPLICIT`
(PackingAuto8), `BARV_IMP_LENGTH_EQ_CARD` (PackingAuto7).

Remaining obligation once the pieces land: the five-stage covering
assembly itself (HL:100-1048): (1) `S = mcell i V ul ∩ mcell j V vl` is
measurable and bounded (`MEASURABLE_MCELL`, `BOUNDED_MCELL`), so
`S ⊆ ball 0 a` and the vertex set `{v ∈ V | voronoiClosed V v ∩ S ≠ ∅}` is
finite inside `V ∩ ball 0 (a+2)` (`KIUMVTC`, `VORONOI_BALL2`);
(2) per `v ∈ V`, `x ∈ voronoiClosed V v` splits `x ∈ rogers V wl`,
`truncateSimplex 0 wl = [v]` over the finitely many lists with entries in
`{u ∈ V | dist (u, v) ≤ 4}` (`BARV_3_EXPLICIT`,
`OMEGA_LIST_IN_VORONOI_LIST`, `BARV_SUBSET`, `saturated`); (3) trim by the
other Rogers simplices meeting `S2` (finite, bound 12 via
`GLTVHUM_concl` + `saturated`; `DUUNHOR_concl` + null-set union); (4)
`SLTSTLO1` gives `k ≤ 4` with `mcell k V wl ∩ S3` of positive measure;
(5) `SLTSTLO2`'s `Z` is null, `S5 = S4 \ Z` keeps positive measure and
avoids `mcell h V wl` for `h ≠ k`; a point `x ∈ S5` (via `qzksykg2_p17`,
`qzksykg1_p17`, `RVFXZBU`, `DDZUPHJ` + `volPosLtAffDim3_p17`) forces
`mcell i V ul = mcell i V wl = mcell j V vl` and `i = j = k`. -/
theorem AJRIPQN (V : Set V3) (ul vl : List V3) (i j : ℕ)
    (hs : saturated V) (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hi : i ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hj : j ∈ ({0, 1, 2, 3, 4} : Set ℕ))
    (hvol : ¬nullSet (mcell i V ul ∩ mcell j V vl)) :
    i = j ∧ mcell i V ul = mcell j V vl := by
  sorry

end Kepler.Text

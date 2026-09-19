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
copy at merge when Auto14's giants land). -/
private theorem qzksykg1_p17 {V : Set V3} {ul vl : List V3} {k : ℕ} {p : Equiv.Perm ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hne : mcell k V ul ≠ ∅)
    (hperm : permutes p (Set.Icc 0 (k - 1))) (hvl : vl = leftActionList p ul) :
    barV V 3 vl :=
  QZKSYKG1 hsat hpack hbar hk hne hperm hvl

/-- HOL `QZKSYKG2` (QZKSYKG.hl:255-262): `mcell k V ul` is covered by the
union of the Rogers simplices of all left-action permutations of `ul` over
`0..k-1` (giant, ~1900 HL lines).

SHIM (2026-09-19): the parallel-owned PackingAuto14 olean HAS landed in this
checkout, so the verbatim `_p17` copy discharges to
`Kepler.Text.PackingAuto14.QZKSYKG2` (still `sorry`ed upstream there — a
documented transitive shim, deleting the statement duplication; delete the
copy at merge when Auto14's giants land). -/
private theorem qzksykg2_p17 {V : Set V3} {ul : List V3} {k : ℕ}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
    mcell k V ul ⊆
      ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1))}) :=
  QZKSYKG2 hsat hpack hbar hk

/-! ## AJRIPQN.hl: main theorem -/

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
- `GLTVHUM_concl` (PackingAuto2:550, sorry): closed Voronoi cell = union of
  Rogers simplices rooted at `u0` — stage 2 covering.
- `DUUNHOR_concl` (PackingAuto2:557, sorry) + a `Coplanar`-implies-null
  bridge: distinct Rogers simplices meet in a null set — stage 3 trimming
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

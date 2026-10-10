/-
Kepler Text lane, stage 18: the leaf-cell calculus (`leaf_cell.hl`), the
`sum_gamma` cluster-inequality scaffold (`sum_gamma.hl` /
`SUM_GAMMAX_LMFUN_ESTIMATE`, a supported lemma behind book lemma UPFZBZM), and
the counting-spheres bank of `YSSKQOY.hl`.

HOL sources (flyspeck text_formalization / packing):
- `leaf_cell.hl` (4306 ln): the "leaf" Voronoi faces (`leaf`, `stem`,
  `cc_pe1/2`, `cc_uh`, `cc_ke`, `cc_A0`, `cc_cell`) and 116 lemmas around
  Marchal cells attached to a leaf stem `{EL 0 ul, EL 1 ul}` (coplanarity,
  azimuth/wedge splitting, cell-compatibility `BDXKHTW`/`EWYBJUA`, `CFFONNL`).
- `sum_gamma.hl` (1465 ln): `TSKAJXY_statement` (already encoded in
  PackingAuto2) and the giant estimate `SUM_GAMMAX_LMFUN_ESTIMATE`
  (ported `sorry`; its HL proof is a 1400-line lemma chain over
  `mcell_set`, `gammaX`, `beta_bump_v1` bounds and the cluster sum).
- `YSSKQOY.hl` (551 ln): `selectd`, `normalize`, complex-argument helpers and
  the arclength monotonicity chain ending in `YSSKQOY`.

Encoding notes:
- HOL `real^3` ↔ `V3`; `set_of_list` ↔ `setOfList`, `barV`/`hl`/`mxi`/
  `omega_list`/`voronoi_list`/`radV`/`circumcenter` come from PackingAuto2.
- `chi_msb ul p = ((EL 1 ul - EL 0 ul) cross (EL 2 ul - EL 0 ul)) dot
  (p - EL 0 ul)` is rendered with Mathlib `CrossProduct` on `Fin 3 → ℝ`
  (the `V3 → Fin 3 → ℝ` coercion is the identity type-synonym lift; addition,
  subtraction and scalar multiplication commute with it by `rfl`, as used in
  TopologyFan).
- `cc_pe1`/`cc_pe2`/`cc_uh` are HOL `new_specification` (Skolem) constants;
  they are rendered by `Classical.choose` over the (sorry'd) existence
  theorems `cc_pe_exists` / `cc_uh_exists`, mirroring `SKOLEM_THM`.
- `re_eqvl` (trig2.hl:4238), `conv0` (sphere.hl:294) and `arclength`
  (sphere.hl:258) are ported here because the ported lemmas quantify over
  them; `arclength` uses flyspeck `atn2(x, y) = Real.atan2 y x` (the
  flyspeck branch structure coincides with Mathlib's `Real.atan2` off the
  degenerate origin pair).
- atn2-merge (docs/atn2-merge-plan.md §5.1): the sphere.hl/collect_geom.hl
  kit `delta_x`/`delta`/`ups_x`/`atn2` (and `chi_msb`) is single-sourced in
  `Kepler.Text.SphereKit`, which declares it in this same `Kepler.Text`
  namespace, so the plain names keep resolving for every downstream lemma
  quantifying over them.
  `arclength` has no canonical home yet (SphereKit wave 1 omitted it) and
  stays defined here.
- YSSKQOY's `dot`/`vector_angle` on `:complex` are the real^2 structures
  under the standard complex identification; `complexDot` is that dot
  product. `COS_ARG_VECTOR_ANGLE` is stated in the ℂ identification (the
  HOL `vector_angle` of the pair); `SEC_DOT` is stated over `V3` with
  Kepler.Text's `vectorAngle`.
- `pack_ineq_def_a` (YSSKQOY.hl:24-31) is HOL reflection machinery: it builds
  the conjunction of the `UKBRPFE`/`WAZLDCD`/`BIEFJHU` flypaper inequalities
  out of `Ineq.ineqs` at load time. It is not a mathematical constant of the
  development and has no Lean counterpart; the three lemmas that reference
  such hypotheses are out of scope here.
- DISCHARGE check vs PackingAuto2 concl theorems: `TSKAJXY_statement` is
  byte-identical to PackingAuto2's encoding (reused, not redefined).
  `SUM_GAMMAX_LMFUN_ESTIMATE` is only a *support* lemma for UPFZBZM; it does
  not match `UPFZBZM_concl`, `RDWKARC_concl`, `GOTCJAH_concl` or
  `TIWWFYQ_concl`, which remain `sorry` in PackingAuto2.
- `AJRIPQN_0` (leaf_cell.hl:2132) discharges against PackingAuto17.AJRIPQN
  (its HOL twin), losing only the redundant `i = j` conjunct.

STATUS (2026-09-20 fill wave): 26 of the 120 skeleton sorries proved:
`ARG_CNJ`, `CONDS_IN_CONV2`, `FINITE_CARD1_IMP_SINGLETON`, `SET2_INSERT1`,
`SET2_INSERT2` (finite-set kit); `chi_msb_swap_01/12/23`,
`chi_msb_additive_a/d`, `CHI_MSB_ADDITIVE`, `CHI_MSB_CONVEX` (chi_msb is the
row determinant `det ![d-a, b-a, c-a]`, private `chiMsb_det`);
`DIST_LE_HALF_PLANE`, `DIST_EQ_HALF_PLANE` (inner-product algebra,
`dist_sq_diff`); `affine_invert`, `AFF_GE_MONO_TRANS` (Affsign/finset-sum
regrouping); `CARD4_ALL_DISTINCT`, `LENGTH4_SET2`, `LENGTH4_SET2_SWAP01`;
`BARV3_TRUNC2`, `STEM_OF_LEAF`, `truncate_set_of_list` (via PA5's
`TRUNCATE_SIMPLEX_INITIAL_SUBLIST` kit); `LIST_OF_CC_UH`,
`SET_OF_LIST_CC_UH`, `EL_CC_UH` (from `cc_uh_exists`);
`MIDPOINT_IN_CONV0`.

Verdict correction (2026-09-20, false-statement tribunal): the earlier claim
that `AFF_GT_0_2` is FALSE as ported was wrong.  HOL `affsign` sums over the
*set* `s ∪ t` and therefore already dedups at `v = w` exactly like the Lean
`Affsign` `toFinset` sum; at `v = w` both sides of the claimed equality are
`{v}`.  The HOL lemma (leaf_cell.hl:3589) carries no `v ≠ w` hypothesis, and
`AFF_GT_0_2` is now proved outright, statement unchanged.  Same wave proved:
the internal `finrank ≤ 2` step of `AFF_DIM_3` (`finrank_span_le_card`),
`AFFINE_IMP_CHI_MSB_0` (affine-span extraction + determinant multilinearity),
`AZIM_BASE_SHIFT_LE` (two `sum4_azim_fan` + linear arithmetic) and
`AZIM_POS_IMP_SUM_2PI_ALT` (the Geom `azim_compl` complement formula).  The
giants stay `sorry`: the leaf-cell chain (`YBZFUPO`, `NWVRFMF`, `CFFONNL`,
`BDXKHTW`, `EWYBJUA`, ...), the arclength derivative/monotonicity chain
(`arc_derivative*`, `YSSKQOY`) and `SUM_GAMMAX_LMFUN_ESTIMATE` (PA19 shim
target; needs the full 1400-line HL lemma chain).

STATUS (2026-10-10 cc-chain wave, PA18 lane): 17 further sorries proved,
unbundling the ccPe1/ccUh/ccKe/ccCell closure to a single GIANT root.
Now derived: `CC_PE_FACET_OF` (moved above `cc_uh_exists`) and
`cc_uh_exists` = NWVRFMF (proved) at p := cc_pe1 -- the Skolem taint
flows only through `cc_pe_exists`; `COPLANAR_INSERT` via a re-spliced
`pa18_affDim_insert` (PA6's private p6_affDim_insert); `MXI_IN_VORONOI_LIST`
(MXI_EXPLICIT + OMEGA_LIST_N_IN_VORONOI_LIST_GEN + CONVEX_VORONOI_LIST);
`NOT_COL_IMP_RADV` via the new bridge `pa18_ncol3_affDep`
(not-collinear -> not affineDependent, affineIndependent_iff_le_finrank_vectorSpan)
and OAPVION2_concl; `MCELL3_NONPLANAR` (HOL 1698-1794: mxi off the stem span
via OAPVION3 + NOT_COL_IMP_RADV radius sqrt 2 vs hl < sqrt 2, then the
AFF_DIM_INSERT +1 dimension jump); `K4_CHI_MSB_EQVL`/`K4_CHI_MSB_POS`
(XNHPWAB2 + CONVEX_HULL_4 + chi_msb_additive_d); `MXI_BETWEEN`
(MXI_EXPLICIT); `CELL3_NONDEG` (omega_list_n 2 = circumcenter via
OMEGA_LIST_N_LEMMA + XNHPWAB1, JDHAWAY_1, affine_invert); `CELL_NN`
(CHI_MSB_CONVEX + CC_CELL34); `CC_CELL_IN_MCELL_SET`; and the nonplanarity
cascade `CC_CELL_NOT_COPLANAR` (new `pa18_mcell4_nonplanar` +
MCELL3_NONPLANAR), `CC_CELL_NOT_COPLANAR_EXTREME`, `CC_CELL_EXTREME_CARD`
(pa18_card4_of_distinct / pa18_coplanar4_of_card_ne4),
`CC_CELL_INDEPENDENT` (affineIndependent_iff_not_finrank_vectorSpan_le),
`CC_CELL_CONVEX_HULL_INJ` (CONVEX_HULL_EQ_EQ_SET_EQ).
Still sorry (see the per-site `-- NEEDS` notes): the root `cc_pe_exists`
(single blocking input FUZBZGI_1 -> XYOFCGX@PA7), YBZFUPO,
FUZBZGI_0/1, the chi_msb-coplanarity pair + JDHAWAY_0/JDWAWAY, ZWVCBMN ->
CC_CELL_NOT_NULLSET -> FUEIMOV_K, CFFONNL, the FUEIMOV/EXTREME/V-block and
the MCELL*_EDGE_FIRST/STEM_EDGEX/FCHKUGT rigidity kit.
STATUS: skeleton port; statements faithful, mechanical lemmas proved,
the giant leaf-cell/sum-gamma chains carry `sorry`.
-/

import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto17
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto4
import Kepler.Text.SphereKit
import Kepler.Text.Polytope
import Kepler.Text.TopologyFan
import Mathlib
-- SUM_GAMMAX wave (2026-09-30): `PackingAuto15` (proved marchal3 counting kit:
-- `MCELL_SUBSET_BALL8_2`, `DIHX_RANGE`/`DIHX_LE_PI`, `HL_2`, `lmfun_bounded`,
-- `FINITE_VX`, `MEASURABLE_MCELL` via PA10, `gamma_y_lmfun_bound2` shape) and
-- `PackingAuto4` (`BumpP4.BOUND_BETA_BUMP`/`BumpP4.SUM_BETA_BUMP_LEMMA`, both
-- proved, about the closed-form `betaBump`) join the import set. Closure check:
-- PA15 ← {PA2, PA5-8, PA10-13, Polytope, LuneVolume} and PA4 ← {PA2, PA3,
-- PA11, Polytope, Statement} — neither reaches PA18/PA17/PA14 (acyclic);
-- PA19/PA21/PA25/PackingConcl already co-import both files, so no consumer
-- closure changes; public-name intersections PA15/PA4 vs PA13/PA17/PA18 are
-- empty (checked 2026-09-30).

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical ComplexConjugate

-- atn2-merge (docs/atn2-merge-plan.md §5.1): the kit bodies live in the
-- canonical module Kepler.Text.SphereKit, which declares them in this same
-- `Kepler.Text` namespace (`atn2`, `chiMsb`, `deltaP`, `deltaX`, `upsX`).
-- With the local definitions deleted, every plain kit name keeps resolving
-- for this lane and its importers exactly as when PA18 hosted them.

noncomputable section

/-! ## Definitions (leaf_cell.hl:17-1142, sphere/collect-geom helpers) -/

/-- HOL `leaf` (leaf_cell.hl:17): a leaf Voronoi face over the bar pair. -/
def leaf (V : Set V3) (ul : List V3) : Prop := barV V 2 ul ∧ hl ul < Real.sqrt 2

/-- HOL `stem` (leaf_cell.hl:19): the pair of vertices carried by the leaf. -/
def stem (ul : List V3) : Set V3 := setOfList (truncateSimplex 1 ul)

/-- HOL `re_eqvl` (trig2.hl:4238): equality up to a positive real factor. -/
def reEqvl (a b : ℝ) : Prop := ∃ t : ℝ, 0 < t ∧ a = t * b

/-- HOL `conv0` (sphere.hl:294): `affsign sgn_gt {} S`, the open cone on `S`. -/
def conv0 (S : Set V3) : Set V3 := affGt ∅ S

/-- The `V3` cross product (TopologyFan.cross3, non-private copy): Mathlib
`crossProduct` on the `Fin 3 → ℝ` identification. -/
noncomputable def cross3 (a b : V3) : V3 :=
  WithLp.toLp 2 (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))

-- atn2-merge: `chiMsb` (leaf_cell.hl:781-782, the `chi_msb` signed volume
-- functional) moved verbatim to Kepler.Text.SphereKit (same namespace).

/-- HOL `cc_pe_exists` (leaf_cell.hl:1052-1084), from `YBZFUPO`. -/
theorem cc_pe_exists (V : Set V3) (ul : List V3) :
    ∃ p1 p2 : V3, Packing V → saturated V → leaf V ul →
      voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧ p1 ≠ p2 ∧
        0 < chiMsb ul p1 := by
-- NEEDS (GIANT root, 2026-10-10 wave): the whole ccPe1/ccUh/ccKe/ccCell
-- taint closure (280 downstream) now flows through THIS sorry alone.
-- HOL proof (leaf_cell.hl:1052-1084) = FUZBZGI_1 + JDWAWAY sign-split;
-- FUZBZGI_1 consumes PA7's still-sorry XYOFCGX (outside this file) and
-- YBZFUPO needs a 1-dim polytope = segment classification (no repo/Mathlib
-- lemma; cf. PolyAuto7's note on EXPAND_EDGE_POLYTOPE). Everything else in
-- the PA18 cc-chain is now derived.
  sorry

/-- HOL `cc_pe1` (leaf_cell.hl:1082, `new_specification` via `SKOLEM_THM`). -/
noncomputable def ccPe1 (V : Set V3) (ul : List V3) : V3 :=
  Classical.choose (cc_pe_exists V ul)

/-- HOL `cc_pe2` (leaf_cell.hl:1082, `new_specification` via `SKOLEM_THM`). -/
noncomputable def ccPe2 (V : Set V3) (ul : List V3) : V3 :=
  Classical.choose (Classical.choose_spec (cc_pe_exists V ul))

/-- HOL `FACET_OF_SEGMENT` (leaf_cell.hl:1085-1104): the endpoints are the
1-dimensional faces of the closed segment (via the extreme-point kit of
Polytope and `affDim_segment`). -/
theorem FACET_OF_SEGMENT (a b : V3) (h : a ≠ b) :
    FacetOf {a} (segment ℝ a b) := by
  refine ⟨faceOf_sing.2 ((EXTREME_POINT_OF_SEGMENT a b a).2 (Or.inl rfl)), by simp, ?_⟩
  rw [affDim_singleton, (affDim_segment a b).2 h]
  norm_num

/-- HOL `CC_PE_FACET_OF` (leaf_cell.hl:1105-1119): the `cc_pe1` endpoint is a
facet of the leaf's Voronoi segment (needs only the `cc_pe_exists` hull
equation plus `FACET_OF_SEGMENT`). -/
theorem CC_PE_FACET_OF {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    FacetOf {ccPe1 V ul} (voronoiList V ul) := by
  have hq := Classical.choose_spec (Classical.choose_spec (cc_pe_exists V ul)) hp hs hl'
  obtain ⟨hhull, hne, -⟩ := hq
  rw [hhull, convexHull_pair]
  exact FACET_OF_SEGMENT _ _ hne

/-- HOL `NWVRFMF` (leaf_cell.hl:342-359), a direct port over the Rogers
`IDBEZAL` facet characterization and `OMEGA_LIST_IN_VORONOI_LIST`. -/
theorem NWVRFMF {V : Set V3} {ul : List V3} {p : V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul)
    (hf : FacetOf {p} (voronoiList V ul)) :
    ∃ vl, barV V 3 vl ∧ truncateSimplex 2 vl = ul ∧ omegaList V vl = p := by
  have hbar : barV V 2 ul := hl'.1
  obtain ⟨vl, hF, hbar3, htr⟩ :=
    (IDBEZAL V ul 2 {p} hs hp hbar (by norm_num)).1 hf
  refine ⟨vl, hbar3, htr, ?_⟩
  have hom : omegaList V vl ∈ voronoiList V vl := OMEGA_LIST_IN_VORONOI_LIST V vl 3 hbar3
  rw [← hF] at hom
  exact Set.mem_singleton_iff.1 hom

/-- HOL `cc_uh_exists` (leaf_cell.hl:1120-1132), from `NWVRFMF` (proved)
applied at `p := ccPe1 V ul` via `CC_PE_FACET_OF`; the taint now flows
solely through the `cc_pe_exists` root. -/
theorem cc_uh_exists (V : Set V3) (ul : List V3) :
    ∃ vl : List V3, Packing V → saturated V → leaf V ul →
      barV V 3 vl ∧ truncateSimplex 2 vl = ul ∧ omegaList V vl = ccPe1 V ul := by
  by_cases hx : Packing V ∧ saturated V ∧ leaf V ul
  · obtain ⟨hp, hs, hl'⟩ := hx
    obtain ⟨vl, hbar, htr, hom⟩ := NWVRFMF (V := V) (ul := ul) (p := ccPe1 V ul) hp hs hl'
      (CC_PE_FACET_OF hp hs hl')
    exact ⟨vl, fun _ _ _ => ⟨hbar, htr, hom⟩⟩
  · refine ⟨[0, 0, 0, 0], fun hp hs hl' => ?_⟩
    exact absurd ⟨hp, hs, hl'⟩ hx

/-- HOL `cc_uh` (leaf_cell.hl:1133, `new_specification` via `SKOLEM_THM`):
the four-point list whose Marchal cell is `cc_cell`. -/
noncomputable def ccUh (V : Set V3) (ul : List V3) : List V3 :=
  Classical.choose (cc_uh_exists V ul)

/-- HOL `cc_ke` (leaf_cell.hl:1136-1137): 4 when the cc_uh list is itself a
leaf (tetrahedron cell), else 3 (prism-with-apex cell). -/
def ccKe (V : Set V3) (ul : List V3) : ℕ :=
  if hl (ccUh V ul) < Real.sqrt 2 then 4 else 3

/-- HOL `cc_A0` (leaf_cell.hl:1139-1141). -/
def ccA0 (ul : List V3) : Set V3 :=
  affGt {ul[0]!, ul[1]!} {ul[2]!}

/-- HOL `cc_cell` (leaf_cell.hl:1142): the Marchal cell over `cc_uh`. -/
def ccCell (V : Set V3) (ul : List V3) : Set V3 := mcell (ccKe V ul) V (ccUh V ul)

-- atn2-merge (plan §5.1): `deltaX` (sphere.hl `delta_x`), `deltaP`
-- (collect_geom.hl `delta`), `upsX` (sphere.hl `ups_x`) and `atn2`
-- (sphere.hl:48-52) moved verbatim to Kepler.Text.SphereKit, which
-- declares them in this same `Kepler.Text` namespace.

/-- HOL `arclength` (sphere.hl:258-260).  Stays in PackingAuto18 for now:
SphereKit's wave-1 kit does not carry `arclength` (plan §3 said "move" but
the move target does not exist yet), so deleting it would orphan the
YSSKQOY monotonicity chain below and the LocalAuto lane's plain
`arcLength` uses. -/
noncomputable def arcLength (a b c : ℝ) : ℝ :=
  Real.pi / 2 +
    atn2 (Real.sqrt (upsX (a * a) (b * b) (c * c))) (c * c - a * a - b * b)

/-- HOL `selectd` (YSSKQOY.hl:39-40): a default-carrying choice operator
(the `Nonempty` constraint is a rendering artifact of `Classical.epsilon`,
which HOL's `@` does not need since HOL types are inhabited). -/
def selectd {α : Type*} [Nonempty α] (P : α → Prop) (d : α) : α :=
  if ∃ r, P r then Classical.epsilon P else d

/-- The real^2 dot product under the complex identification (YSSKQOY.hl:66
`DOT_COMPLEX`'s `dot` on `complex`). -/
def complexDot (z1 z2 : ℂ) : ℝ := z1.re * z2.re + z1.im * z2.im

/-- HOL `normalize` (YSSKQOY.hl:187). -/
noncomputable def normalize (v : V3) : V3 := (‖v‖ : ℝ)⁻¹ • v

/-- HOL `SUM_GAMMAX_LMFUN_ESTIMATE_concl` (sum_gamma.hl:53-60): there is a
constant bounding the cluster `gammaX` sum of an annulus-restricted cluster;
the supporting estimate for book lemma UPFZBZM. -/
def SUM_GAMMAX_LMFUN_ESTIMATE_concl : Prop :=
  ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V → 1 ≤ r →
    cellClusterInequality V → TSKAJXY_statement →
    c * r ^ 2 ≤ setSum {X | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
      (fun X => gammaX V X lmfun)

/-! ## Private azimuth–affine bridge kit (for the leaf-cell wedge lemmas) -/

private theorem pa18_toFinset3 {v0 v1 w : V3} (h01 : v0 ≠ v1) (h0w : v0 ≠ w) (h1w : v1 ≠ w)
    (hfin : ({v0, v1} ∪ {w} : Set V3).Finite) :
    hfin.toFinset = insert v0 (insert v1 ({w} : Finset V3)) := by
  ext z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem pa18_collinear3_line_affGe {v0 v1 w x : V3} (hcolx : Collinear3 v0 v1 x)
    (hw : ¬Collinear3 v0 v1 w) : x ∈ affGe ({v0, v1} : Set V3) ({w} : Set V3) := by
  have h01 : v0 ≠ v1 := ne₁₂_of_not_collinear hw
  have h0w : v0 ≠ w := ne₁₃_of_not_collinear hw
  have h1w : v1 ≠ w := ne₂₃_of_not_collinear hw
  have hfin : ({v0, v1} ∪ {w} : Set V3).Finite :=
    Set.Finite.union (Set.Finite.insert v0 (Set.finite_singleton v1)) (Set.finite_singleton w)
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := v0) (w := v1) h01.symm).1 hcolx
  have hv0 : v0 ∉ insert v1 ({w} : Finset V3) := by
    intro hcon
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
    rcases hcon with h | h
    · exact h01 h
    · exact h0w h
  have hv1 : v1 ∉ ({w} : Finset V3) := by
    intro hcon
    simp only [Finset.mem_singleton] at hcon
    exact h1w hcon
  rw [affGe, Set.mem_setOf_eq, Affsign]
  refine ⟨fun z => if z = v0 then 1 - c else if z = v1 then c else 0, hfin, ?_, ?_, ?_⟩
  · rw [pa18_toFinset3 h01 h0w h1w hfin, Finset.sum_insert hv0, Finset.sum_insert hv1,
      Finset.sum_singleton]
    simp only [h01, h0w, h1w, h0w.symm, h1w.symm, if_neg (Ne.symm h01), if_neg (Ne.symm h0w),
      if_neg (Ne.symm h1w), if_pos rfl, reduceIte]
    linear_combination (norm := module) hc
  · intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    simp only [h0w.symm, h1w.symm, if_neg, reduceIte]
    norm_num
  · rw [pa18_toFinset3 h01 h0w h1w hfin, Finset.sum_insert hv0, Finset.sum_insert hv1,
      Finset.sum_singleton]
    simp only [h01, h0w, h1w, h0w.symm, h1w.symm, if_neg (Ne.symm h01), if_neg (Ne.symm h0w),
      if_neg (Ne.symm h1w), if_pos rfl, reduceIte]
    norm_num

/-- A point of `affGe {v0,v1} {w}` off the base line lies in `affGt`: expand
the combination and split on the coefficient of `w`. -/
private theorem pa18_affGe_affGt_of_ncol {v0 v1 w x : V3} (hw : ¬Collinear3 v0 v1 w)
    (hx : ¬Collinear3 v0 v1 x) (hmem : x ∈ affGe ({v0, v1} : Set V3) ({w} : Set V3)) :
    x ∈ affGt ({v0, v1} : Set V3) ({w} : Set V3) := by
  have h01 : v0 ≠ v1 := ne₁₂_of_not_collinear hw
  have h0w : v0 ≠ w := ne₁₃_of_not_collinear hw
  have h1w : v1 ≠ w := ne₂₃_of_not_collinear hw
  have hfin : ({v0, v1} ∪ {w} : Set V3).Finite :=
    Set.Finite.union (Set.Finite.insert v0 (Set.finite_singleton v1)) (Set.finite_singleton w)
  have hv0 : v0 ∉ insert v1 ({w} : Finset V3) := by
    intro hcon
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
    rcases hcon with h | h
    · exact h01 h
    · exact h0w h
  have hv1 : v1 ∉ ({w} : Finset V3) := by
    intro hcon
    simp only [Finset.mem_singleton] at hcon
    exact h1w hcon
  rw [affGe, Set.mem_setOf_eq, Affsign] at hmem
  obtain ⟨f, hf, hvec, hpos, hone⟩ := hmem
  have hvec3 := hvec
  have hone3 := hone
  rw [pa18_toFinset3 h01 h0w h1w hf] at hvec3 hone3
  simp only [Finset.sum_insert hv0, Finset.sum_insert hv1, Finset.sum_singleton] at hvec3 hone3
  rw [affGt, Set.mem_setOf_eq, Affsign]
  refine ⟨f, hf, hvec, ?_, hone⟩
  intro z hz
  have hzw : z = w := Set.mem_singleton_iff.1 hz
  have hle := hpos z hz
  rw [hzw] at hle ⊢
  by_cases hfw : f w = 0
  · exfalso
    apply hx
    simp only [hfw, zero_smul, add_zero] at hvec3
    have hsum1 : f v0 + f v1 = 1 := by rw [← hone3, hfw, add_zero]
    rw [collinear3_iff_smul (Ne.symm h01)]
    refine ⟨f v1, ?_⟩
    show x - v0 = f v1 • (v1 - v0)
    have h2 : ((f v0 + f v1 - 1 : ℝ)) • v0 = 0 := by rw [hsum1]; norm_num
    linear_combination (norm := module) hvec3 + h2
  · exact lt_of_le_of_ne hle (Ne.symm hfw)

private theorem pa18_azim_zero_affGe {v0 v1 w x : V3} (hw : ¬Collinear3 v0 v1 w) :
    azim v0 v1 w x = 0 ↔ x ∈ affGe ({v0, v1} : Set V3) ({w} : Set V3) := by
  constructor
  · intro h0
    by_cases hcolx : Collinear3 v0 v1 x
    · exact pa18_collinear3_line_affGe hcolx hw
    · have hgt : x ∈ affGt ({v0, v1} : Set V3) ({w} : Set V3) :=
        (azim_eq_zero_iff_alt hw hcolx).1 h0
      rcases hgt with ⟨f, hf, hvec, hpos, hone⟩
      rw [affGe, Set.mem_setOf_eq, Affsign]
      exact ⟨f, hf, hvec, fun z hz => le_of_lt (hpos z hz), hone⟩
  · intro hmem
    by_cases hcolx : Collinear3 v0 v1 x
    · rw [azim, if_pos (Or.inr hcolx)]
    · exact (azim_eq_zero_iff_alt hw hcolx).2 (pa18_affGe_affGt_of_ncol hw hcolx hmem)

/-! ## YSSKQOY.hl: general lemmas -/

/-- HOL `selectd_cases` (YSSKQOY.hl:42-53). -/
theorem selectd_cases {α : Type*} [Nonempty α] (P : α → Prop) (d : α) :
    P (selectd P d) ∨ selectd P d = d := by
  by_cases h : ∃ r, P r
  · left
    simp only [selectd, if_pos h]
    exact Classical.epsilon_spec h
  · right; simp [selectd, h]

/-- HOL `selectd_exists` (YSSKQOY.hl:55-63). -/
theorem selectd_exists {α : Type*} [Nonempty α] {P : α → Prop} {d : α}
    (h : ∃ r, P r) : P (selectd P d) := by
  simp only [selectd, if_pos h]
  exact Classical.epsilon_spec h

/-- HOL `DOT_COMPLEX` (YSSKQOY.hl:66-72). -/
theorem DOT_COMPLEX (x y x' y' : ℝ) :
    complexDot (x + y * Complex.I) (x' + y' * Complex.I) = x * x' + y * y' := by
  simp [complexDot, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]

/-- HOL `DOT_RE` (YSSKQOY.hl:74-81). -/
theorem DOT_RE (z1 z2 : ℂ) : complexDot z1 z2 = (z1 * conj z2).re := by
  simp only [complexDot, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- HOL `ARG_0_DIV` (YSSKQOY.hl:99-105). -/
theorem ARG_0_DIV (u v : ℂ) : u / v = 0 ↔ u = 0 ∨ v = 0 := by
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · exact div_eq_zero_iff

/-- HOL `RE_CEXP_CX` (YSSKQOY.hl:198-204). -/
theorem RE_CEXP_CX (x : ℝ) : (Complex.exp (Complex.I * x)).re = Real.cos x := by
  rw [show Complex.I * x = x * Complex.I from mul_comm _ _]
  exact Complex.exp_ofReal_mul_I_re x

/-- HOL `ARG_CNJ` (YSSKQOY.hl:83-97). -/
theorem ARG_CNJ (z w : ℂ) (hw : w ≠ 0) :
    Complex.arg (z / w) = Complex.arg (z * conj w) := by
  have hr : (0:ℝ) < ‖w‖ ^ 2 := by positivity
  have h2 : (‖w‖ ^ 2 : ℝ) ≠ 0 := hr.ne'
  have h3 : (w * conj w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hwinv : (w⁻¹ : ℂ) = (((‖w‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) * conj w := by
    refine mul_left_cancel₀ hw ?_
    rw [mul_inv_cancel₀ hw, mul_comm (((‖w‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) (conj w), ← mul_assoc,
      h3, ← Complex.ofReal_mul, mul_comm, inv_mul_cancel₀ h2, Complex.ofReal_one]
  rw [div_eq_inv_mul, mul_comm (w⁻¹ : ℂ) z, hwinv,
    mul_left_comm z (((‖w‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) (conj w), Complex.arg_real_mul _ (inv_pos.2 hr)]

/-- HOL `RE_NORM_1` (YSSKQOY.hl:216-224). -/
theorem RE_NORM_1 (z : ℂ) (h : ‖z‖ = 1) : z.re = Real.cos (Complex.arg z) := by
  have hz : z ≠ 0 := by
    intro hc; rw [hc] at h; simpa using h.symm
  have := Complex.cos_arg hz
  rw [h] at this
  simp at this
  linarith

/-- HOL `COS_ARG_VECTOR_ANGLE` (YSSKQOY.hl:226-261), stated with the real^2
`vector_angle` under the complex identification. -/
theorem COS_ARG_VECTOR_ANGLE (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.cos (Complex.arg (u / v)) =
      Real.cos (Real.arccos (complexDot u v / (‖u‖ * ‖v‖))) := by
  have huv : u / v ≠ 0 := by
    rw [ne_eq, div_eq_zero_iff]
    simp [hv, hu]
  have h1 : Real.cos (Complex.arg (u / v)) = (u / v).re / ‖u / v‖ :=
    Complex.cos_arg huv
  have hnorm : ‖u / v‖ = ‖u‖ / ‖v‖ := by
    rw [show u / v = u * v⁻¹ from by ring, norm_mul, norm_inv]; ring
  have hre : (u / v).re = complexDot u v / ‖v‖ ^ 2 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [complexDot]
    ring
  have hcs : |complexDot u v| ≤ ‖u‖ * ‖v‖ := by
    rw [DOT_RE]
    refine le_trans (Complex.abs_re_le_norm (u * conj v)) ?_
    refine le_trans (norm_mul_le u (conj v)) ?_
    rw [Complex.norm_conj]
  have hdiv : |complexDot u v / (‖u‖ * ‖v‖)| ≤ 1 := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity),
      div_le_iff₀ (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity)]
    linarith
  have hbound := abs_le.1 hdiv
  rw [h1, hnorm, hre]
  have h2 : complexDot u v / ‖v‖ ^ 2 / (‖u‖ / ‖v‖) = complexDot u v / (‖u‖ * ‖v‖) := by
    have hu' : ‖u‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hu)
    have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
    field_simp
  rw [h2, Real.cos_arccos hbound.1 hbound.2]

/-- HOL `norm_normalize` (YSSKQOY.hl:189-196; the HL file carries it twice). -/
theorem norm_normalize (v : V3) (h : v ≠ 0) : ‖normalize v‖ = 1 := by
  simp only [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (fun hc => h (by rw [← norm_eq_zero]; exact hc))

/-- HOL `CARD_UNION_EQ` (YSSKQOY.hl:107-110). -/
theorem CARD_UNION_EQ {α : Type*} {s t u : Set α} (hu : u.Finite)
    (hst : s ∩ t = ∅) (huni : s ∪ t = u) :
    Nat.card s + Nat.card t = Nat.card u := by
  have hs : s.Finite := hu.subset (by rw [← huni]; exact subset_union_left)
  have ht : t.Finite := hu.subset (by rw [← huni]; exact subset_union_right)
  have key : (s ∪ t).ncard = s.ncard + t.ncard :=
    Set.ncard_union_eq (by rw [Set.disjoint_iff_inter_eq_empty]; exact hst) hs ht
  rw [_root_.Nat.card_coe_set_eq, _root_.Nat.card_coe_set_eq,
    _root_.Nat.card_coe_set_eq, ← huni]
  exact key.symm

/-- HOL `INJ_SURJ` (YSSKQOY.hl:112-155). The HOL `INJ f a b` splits into
`Set.InjOn f a` plus the codomain membership of `f` on `a`, which is stated
explicitly here. -/
theorem INJ_SURJ {α β : Type*} {a : Set α} {b : Set β} {f : α → β}
    (ha : a.Finite) (hb : b.Finite) (hcard : Nat.card a = Nat.card b)
    (hi : Set.InjOn f a) (hmem : ∀ x ∈ a, f x ∈ b) :
    ∀ y ∈ b, ∃ x, x ∈ a ∧ f x = y := by
  have him : (f '' a).Finite := ha.image f
  have hcardimg : (f '' a).ncard = a.ncard := by
    have he := hi.encard_image
    rw [← him.cast_ncard_eq, ← ha.cast_ncard_eq] at he
    simpa using he
  have himsub : f '' a ⊆ b := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hmem x hx
  have hsub2 : b ∩ f '' a = f '' a := Set.inter_eq_right.2 himsub
  have hun : b ∩ f '' a ∪ (b \ f '' a) = b := Set.inter_union_sdiff b (f '' a)
  rw [hsub2, Set.union_comm] at hun
  have hdiff : (b \ f '' a).Finite := hb.subset Set.sdiff_subset
  have hdisj : Disjoint (b \ f '' a) (f '' a) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact h1.2 h2
  have key := Set.ncard_union_eq hdisj hdiff him
  rw [hun] at key
  rw [_root_.Nat.card_coe_set_eq] at hcard
  have hcard' : a.ncard = b.ncard := hcard
  have hzero : (b \ f '' a).ncard = 0 := by
    have h1 := key
    have h2 := hcardimg
    omega
  have hempty : b \ f '' a = ∅ := (Set.ncard_eq_zero hdiff).1 hzero
  intro y hy
  have hmem2 : y ∈ f '' a := by
    by_contra hc
    exact absurd (Set.mem_sdiff y |>.2 ⟨hy, hc⟩) (by rw [hempty]; simp)
  obtain ⟨x, hx, hfx⟩ := (Set.mem_image f a y).1 hmem2
  exact ⟨x, hx, hfx⟩


/-- HOL `INJ_IFF_SURJ` (YSSKQOY.hl:157-185); same explicit codomain-membership
splitting of `INJ` as `INJ_SURJ`. -/
theorem INJ_IFF_SURJ {α β : Type*} {a : Set α} {b : Set β} {f : α → β}
    (ha : a.Finite) (hb : b.Finite) (hcard : Nat.card a = Nat.card b)
    (hmem : ∀ x ∈ a, f x ∈ b) :
    Set.InjOn f a ↔ ∀ y ∈ b, ∃ x, x ∈ a ∧ f x = y := by
  constructor
  · intro hi
    exact INJ_SURJ ha hb hcard hi hmem
  · intro hsurj
    have himg : f '' a = b := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨x, hx, rfl⟩
        exact hmem x hx
      · intro y hy
        obtain ⟨x, hx, hfx⟩ := hsurj y hy
        exact ⟨x, hx, hfx⟩
    have hcardimg : (f '' a).ncard = a.ncard := by
      rw [himg]
      exact hcard.symm
    exact Set.injOn_of_ncard_image_eq hcardimg ha

private theorem upsX_sq_factor (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c)
      = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  simp only [upsX]
  ring

/-- HOL `TRI_UPS_X_STRICT_POS` (YSSKQOY.hl:340-346). -/
theorem TRI_UPS_X_STRICT_POS (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (h1 : c < a + b) (h2 : a < b + c) (h3 : b < c + a) :
    0 < upsX (a * a) (b * b) (c * c) := by
  rw [upsX_sq_factor]
  refine mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    (by linarith)

/-- HOL `ups_x_pos` (YSSKQOY.hl:348-357). -/
theorem ups_x_pos (a b : ℝ) (h1 : 2 ≤ a) (h2 : a ≤ 2.52) (h3 : 2 ≤ b)
    (h4 : b ≤ 2.52) : 0 < upsX (a ^ 2) (b ^ 2) 4 := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  rw [sq a, sq b, show (4:ℝ) = 2 * 2 from by norm_num]
  exact TRI_UPS_X_STRICT_POS a b 2 ha hb (by norm_num) (by linarith) (by linarith)
    (by linarith)

/-- HOL `SEC_DOT` (YSSKQOY.hl:263-285), over `V3` with Kepler.Text's
`vector_angle`. -/
theorem SEC_DOT (u v : V3) (r ψ : ℝ) (hr : 0 < r) (hψ1 : 0 ≤ ψ)
    (hψ2 : ψ < Real.pi / 2) (hv : ‖v‖ = r / Real.cos ψ) (hu : ‖u‖ = r)
    (hcos : Real.cos (vectorAngle u v) = Real.cos ψ) :
    u ⬝ᵥ (v - u) = 0 := by
  have hcosψ : 0 < Real.cos ψ :=
    Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, norm_zero, eq_comm, div_eq_zero_iff] at hv
    exact hcosψ.ne' (hv.resolve_left hr.ne')
  have hu0 : u ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hu
    exact hr.ne' hu.symm
  have hsplit : vectorAngle u v =
      Real.arccos ((u ⬝ᵥ v) / (‖u‖ * ‖v‖)) := by
    rw [vectorAngle, if_neg (by simp [hu0, hv0])]
  have hcs : |(u ⬝ᵥ v : ℝ)| ≤ ‖u‖ * ‖v‖ := by
    have := abs_real_inner_le_norm (x := u) (y := v)
    rwa [Kepler.Geom.inner_eq_dot] at this
  have hcs1 : -1 ≤ (u ⬝ᵥ v) / (‖u‖ * ‖v‖) ∧ (u ⬝ᵥ v) / (‖u‖ * ‖v‖) ≤ 1 := by
    obtain ⟨hn1, hn2⟩ := abs_le.1 hcs
    constructor
    · rw [le_div_iff₀ (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity)]
      linarith
    · rw [div_le_iff₀ (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity)]
      linarith
  have hval : Real.cos (Real.arccos ((u ⬝ᵥ v) / (‖u‖ * ‖v‖))) =
      (u ⬝ᵥ v) / (‖u‖ * ‖v‖) := Real.cos_arccos hcs1.1 hcs1.2
  have hkey : (u ⬝ᵥ v : ℝ) = r ^ 2 := by
    have h1 : Real.cos ψ = (u ⬝ᵥ v) / (‖u‖ * ‖v‖) := by
      rw [← Real.cos_arccos hcs1.1 hcs1.2, ← hsplit, eq_comm]
      exact hcos
    rw [hu, hv] at h1
    have ht0 : (u ⬝ᵥ v : ℝ) ≠ 0 := by
      intro hc
      rw [hc, zero_div] at h1
      exact hcosψ.ne' h1
    have hden : r * (r / Real.cos ψ) ≠ 0 :=
      mul_ne_zero hr.ne' (div_ne_zero hr.ne' hcosψ.ne')
    have h3 : Real.cos ψ * (r * (r / Real.cos ψ))
        = (u ⬝ᵥ v) / (r * (r / Real.cos ψ)) * (r * (r / Real.cos ψ)) :=
      congrArg (fun x : ℝ => x * (r * (r / Real.cos ψ))) h1
    have h2 : Real.cos ψ * (r * (r / Real.cos ψ)) = u ⬝ᵥ v := by
      rw [h3]
      exact div_mul_cancel₀ _ hden
    rw [← h2]
    field_simp
  rw [dotProduct_sub, hkey]
  rw [← Kepler.Geom.norm_sq_eq_dot, hu]
  ring

/-- HOL `Arc_properties.arc_sym` (the `arclength` symmetry in its first two
arguments; used by `yssk_reduction`). -/
theorem arc_sym (a b c : ℝ) : arcLength a b c = arcLength b a c := by
  have hu : upsX (a * a) (b * b) (c * c) = upsX (b * b) (a * a) (c * c) := by
    simp only [upsX]; ring
  have hy : c * c - a * a - b * b = c * c - b * b - a * a := by ring
  rw [arcLength, arcLength, hu, hy]

/-- HOL `arclength2` (YSSKQOY.hl:297-313): `arclength 2 (2 h) 2 = acs (h/2)`
on the flyspeck range `1 ≤ h ≤ h0`. -/
theorem arclength2 {h : ℝ} (h1 : 1 ≤ h) (h2 : h ≤ h0) :
    arcLength 2 (2 * h) 2 = Real.arccos (h / 2) := by
  have hv : h0 = 1.26 := rfl
  have hh : (0:ℝ) < h := by linarith
  have h126 : h ≤ 1.26 := by linarith
  have hp : (0:ℝ) < 4 - h * h := by nlinarith
  have hx : Real.sqrt (upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2))
      = 4 * h * Real.sqrt (4 - h * h) := by
    have hup : upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2) = (4 * h) ^ 2 * (4 - h * h) := by
      simp only [upsX]; ring
    have h4 : (0:ℝ) ≤ 4 * h := by nlinarith
    rw [hup, Real.sqrt_mul (sq_nonneg (4 * h)), Real.sqrt_sq h4]
  have hneg : (2 * 2 - 2 * 2 - (2 * h) * (2 * h) : ℝ) < 0 := by nlinarith
  have hyx : |2 * 2 - 2 * 2 - (2 * h) * (2 * h)| < 4 * h * Real.sqrt (4 - h * h) := by
    rw [abs_of_neg hneg]
    have hsqrt : h < Real.sqrt (4 - h * h) :=
      Real.lt_sqrt_of_sq_lt (by nlinarith)
    have hstep : h * h < h * Real.sqrt (4 - h * h) :=
      mul_lt_mul_of_pos_left hsqrt hh
    nlinarith
  have hatn : atn2 (Real.sqrt (upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2)))
      (2 * 2 - 2 * 2 - (2 * h) * (2 * h))
      = Real.arctan (-(h / Real.sqrt (4 - h * h))) := by
    rw [atn2, hx, if_pos hyx, show (2 * 2 - 2 * 2 - (2 * h) * (2 * h) : ℝ) = -(4 * h * h) from
      by ring]
    congr 1
    field_simp
  have hten : (1:ℝ) + (h / Real.sqrt (4 - h * h)) ^ 2 = 4 / (4 - h * h) := by
    rw [div_pow, Real.sq_sqrt hp.le, one_add_div hp.ne']
    congr 1
    ring
  have htsqrt : Real.sqrt (1 + (h / Real.sqrt (4 - h * h)) ^ 2)
      = 2 / Real.sqrt (4 - h * h) := by
    rw [hten, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  calc arcLength 2 (2 * h) 2
      = Real.pi / 2 + atn2 (Real.sqrt (upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2)))
          (2 * 2 - 2 * 2 - (2 * h) * (2 * h)) := rfl
    _ = Real.pi / 2 + Real.arctan (-(h / Real.sqrt (4 - h * h))) := by rw [hatn]
    _ = Real.pi / 2 - Real.arcsin (h / 2) := by
        rw [show Real.pi / 2 + Real.arctan (-(h / Real.sqrt (4 - h * h)))
            = Real.pi / 2 - Real.arctan (h / Real.sqrt (4 - h * h)) from by
              rw [Real.arctan_neg]; ring,
          Real.arctan_eq_arcsin, htsqrt, div_div_div_comm]
        have hd0 : Real.sqrt (4 - h * h) ≠ 0 := (Real.sqrt_ne_zero hp.le).2 hp.ne'
        rw [div_self hd0, div_one]
    _ = Real.arccos (h / 2) := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]

/-- HOL `yssk_reduction` (YSSKQOY.hl:316-338): `YSSKQOY` reduces to the
four-point monotonicity of `arclength`. -/
theorem yssk_reduction
    (hmono : ∀ a1 a2 b1 b2 : ℝ, 2 ≤ a1 → a1 ≤ a2 → a2 ≤ 2 * h0 →
      2 ≤ b1 → b1 ≤ b2 → b2 ≤ 2 * h0 →
      0 ≤ arcLength a2 b2 2 - arcLength a1 b2 2 - arcLength a2 b1 2 +
        arcLength a1 b1 2)
    {h h' : ℝ} (hh1 : 1 ≤ h) (hh2 : h ≤ h0) (hh1' : 1 ≤ h') (hh2' : h' ≤ h0) :
    Real.arccos (h / 2) + Real.arccos (h' / 2) - Real.pi / 3 ≤
      arcLength (2 * h) (2 * h') 2 := by
  have h2h : 2 ≤ 2 * h := by linarith
  have h2h0 : 2 * h ≤ 2 * h0 := by linarith
  have h2h' : 2 ≤ 2 * h' := by linarith
  have h2h0' : 2 * h' ≤ 2 * h0 := by linarith
  have hstep := hmono 2 (2 * h) 2 (2 * h') le_rfl h2h h2h0 le_rfl h2h' h2h0'
  have e1 : arcLength 2 (2 * h') 2 = Real.arccos (h' / 2) := arclength2 hh1' hh2'
  have e2 : arcLength (2 * h) 2 2 = arcLength 2 (2 * h) 2 := arc_sym _ _ _
  have e3 : arcLength 2 (2 * h) 2 = Real.arccos (h / 2) := arclength2 hh1 hh2
  have e4 : arcLength 2 2 2 = Real.pi / 3 := by
    have h1' : arcLength 2 (2 * 1) 2 = Real.arccos (1 / 2) :=
      arclength2 (by norm_num)
        (by have hv : h0 = 1.26 := rfl; linarith)
    rw [show 2 * 1 = (2:ℝ) from by ring] at h1'
    rw [h1', Real.arccos_eq_pi_div_two_sub_arcsin, ← Real.sin_pi_div_six,
      Real.arcsin_sin] <;> linarith [Real.pi_pos]
  rw [e1, e2, e3, e4] at hstep
  linarith

/-- HOL `arc_derivative` (YSSKQOY.hl:365-398); the `Arc_properties`
derivative theory is out of scope here. -/
theorem arc_derivative (a b : ℝ) (h : 2 ≤ a ∧ a ≤ 2.52 ∧ 2 ≤ b ∧ b ≤ 2.52) :
    HasDerivWithinAt (fun x => arcLength x b 2)
      (-(4 + a ^ 2 - b ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (b ^ 2) 4)))
      (Icc 2 2.52) a := by
  sorry

/-- HOL `arc_derivative2` (YSSKQOY.hl:400-443); requires the automated
`Calc_derivative` machinery (out of scope here). -/
theorem arc_derivative2 (a b : ℝ) (h : 2 ≤ a ∧ a ≤ 2.52 ∧ 2 ≤ b ∧ b ≤ 2.52) :
    HasDerivWithinAt
      (fun x => -(4 + a ^ 2 - x ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (x ^ 2) 4)))
      (32 * a * b / (Real.sqrt (upsX (a ^ 2) (b ^ 2) 4)) ^ 3) (Icc 2 2.52) b := by
  sorry

/-- HOL `arc_length2_increasing` (YSSKQOY.hl:447-489). -/
theorem arc_length2_increasing (a b1 b2 : ℝ)
    (h : 2 ≤ a ∧ a ≤ 2.52 ∧ 2 ≤ b1 ∧ b1 ≤ 2.52 ∧ 2 ≤ b2 ∧ b2 ≤ 2.52 ∧ b1 ≤ b2) :
    (fun x => -(4 + a ^ 2 - x ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (x ^ 2) 4))) b1 ≤
      (fun x => -(4 + a ^ 2 - x ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (x ^ 2) 4))) b2 := by
  sorry

/-- HOL `arc_length1_increasing` (YSSKQOY.hl:491-529). -/
theorem arc_length1_increasing (a1 a2 b1 b2 : ℝ)
    (h : 2 ≤ a1 ∧ a1 ≤ a2 ∧ a2 ≤ 2.52 ∧ 2 ≤ b1 ∧ b1 ≤ b2 ∧ b2 ≤ 2.52) :
    arcLength a1 b2 2 - arcLength a1 b1 2 ≤ arcLength a2 b2 2 - arcLength a2 b1 2 := by
  sorry

/-- HOL `YSSKQOY` (YSSKQOY.hl:531-549): the counting-spheres arclength
inequality. -/
theorem YSSKQOY {h h' : ℝ} (hh1 : 1 ≤ h) (hh2 : h ≤ h0) (hh1' : 1 ≤ h')
    (hh2' : h' ≤ h0) :
    Real.arccos (h / 2) + Real.arccos (h' / 2) - Real.pi / 3 ≤
      arcLength (2 * h) (2 * h') 2 := by
  sorry

/-! ## leaf_cell.hl: generic lemmas -/

/-- HOL `plane` (collect_geom.hl:217-218). -/
def Plane (x : Set V3) : Prop :=
  ∃ u v w : V3, ¬Collinear3 u v w ∧ x = affineSpan ℝ {u, v, w}

/-- HOL `coplanar_alt` (collect_geom.hl:222). -/
def CoplanarAlt (S : Set V3) : Prop := ∃ x : Set V3, Plane x ∧ S ⊆ x

/-- HOL `coplanar_eq_coplanar_alt` (leaf_cell.hl:23-27); the ← direction
needs a non-collinear triple spanning the hull of a collinear one. -/
theorem coplanar_eq_coplanar_alt {s : Set V3} : Coplanar s ↔ CoplanarAlt s := by
  sorry

/-- HOL `RE_EQVL_IMP_SYM` (leaf_cell.hl:28-41). -/
theorem RE_EQVL_IMP_SYM {a b : ℝ} (h : reEqvl a b) : reEqvl b a := by
  obtain ⟨t, ht, hab⟩ := h
  exact ⟨t⁻¹, inv_pos.2 ht, by rw [hab]; field_simp⟩

/-- HOL `RE_EQVL_SYM` (leaf_cell.hl:42-49). -/
theorem RE_EQVL_SYM (a b : ℝ) : reEqvl a b ↔ reEqvl b a :=
  ⟨RE_EQVL_IMP_SYM, RE_EQVL_IMP_SYM⟩

/-- HOL `RE_EQVL_SCALE1` (leaf_cell.hl:50-71). -/
theorem RE_EQVL_SCALE1 (a b t : ℝ) (ht : 0 < t) :
    reEqvl (t * a) b ↔ reEqvl a b := by
  constructor
  · rintro ⟨s, hs, hsa⟩
    exact ⟨s / t, div_pos hs ht, by
      rw [show s / t * b = s * b / t from by field_simp, eq_div_iff ht.ne', mul_comm]
      exact hsa⟩
  · rintro ⟨u, hu, hua⟩
    exact ⟨t * u, mul_pos ht hu, by rw [hua]; ring⟩

/-- HOL `RE_EQVL_SCALE2` (leaf_cell.hl:72-79). -/
theorem RE_EQVL_SCALE2 (a b t : ℝ) (ht : 0 < t) :
    reEqvl a (t * b) ↔ reEqvl a b := by
  constructor
  · rintro ⟨s, hs, hsa⟩
    exact ⟨s * t, mul_pos hs ht, by rw [hsa]; ring⟩
  · rintro ⟨u, hu, hua⟩
    exact ⟨u / t, div_pos hu ht, by
      rw [show u / t * (t * b) = u * b from by field_simp]
      exact hua⟩

/-- HOL `RE_EQVL_REFL` (leaf_cell.hl:80-90). -/
theorem RE_EQVL_REFL (a : ℝ) : reEqvl a a := ⟨1, one_pos, by ring⟩

/-- HOL `AFF_DIM_3` (leaf_cell.hl:209-226 intermediate). -/
theorem AFF_DIM_3 (a b c : V3) : affDim {a, b, c} ≤ 2 := by
  rw [affDim]
  split
  · norm_num
  · have hsub : vectorSpan ℝ {a, b, c} ≤ Submodule.span ℝ ({a - b, a - c} : Set V3) := by
      rw [vectorSpan_eq_span_vsub_set_left (k := ℝ) (Set.mem_insert a ({b, c} : Set V3)),
        Submodule.span_le]
      rintro d ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · show x -ᵥ x ∈ Submodule.span ℝ ({x - b, x - c} : Set V3)
        rw [vsub_self]
        exact Submodule.zero_mem _
      · show a - x ∈ Submodule.span ℝ ({a - x, a - c} : Set V3)
        exact Submodule.subset_span (Set.mem_insert (a - x) {a - c})
      · show a - x ∈ Submodule.span ℝ ({a - b, a - x} : Set V3)
        exact Submodule.subset_span (by
          rw [Set.mem_insert_iff]
          exact Or.inr (Set.mem_singleton _))
    have hcard : (Module.finrank ℝ
        (Submodule.span ℝ ({a - b, a - c} : Set V3))) ≤ 2 := by
      refine le_trans (finrank_span_le_card (R := ℝ) (M := V3)
        (s := ({a - b, a - c} : Set V3))) ?_
      have hncard : ({a - b, a - c} : Set V3).toFinset.card
          ≤ ({a - c} : Set V3).ncard + 1 := by
        have h1 : ({a - b, a - c} : Set V3).ncard ≤ ({a - c} : Set V3).ncard + 1 :=
          Set.ncard_insert_le (a - b) ({a - c} : Set V3)
        have h2 : ({a - b, a - c} : Set V3).ncard = ({a - b, a - c} : Set V3).toFinset.card :=
          Set.ncard_eq_toFinset_card' _
        omega
      have h3 : ({a - c} : Set V3).ncard = 1 := Set.ncard_singleton _
      omega
    have h1 : Module.finrank ℝ (vectorSpan ℝ {a, b, c})
        ≤ Module.finrank ℝ (Submodule.span ℝ ({a - b, a - c} : Set V3)) :=
      Submodule.finrank_mono hsub
    linarith

/-- HOL `COPLANAR_IMP_AFF_DIM` (leaf_cell.hl:209-226): a coplanar set lives in
a three-point affine span, whose direction has dimension at most 2. -/
theorem COPLANAR_IMP_AFF_DIM {s : Set V3} (h : Coplanar s) : affDim s ≤ 2 := by
  obtain ⟨u, v, w, hsub⟩ := h
  by_cases hse : s = ∅
  · rw [hse, affDim_empty]
    norm_num
  · have h3 : ({u, v, w} : Set V3) ≠ ∅ := fun hc =>
      absurd (Set.mem_insert u ({v, w} : Set V3))
        (by rw [hc]; simp)
    have h2 := AFF_DIM_3 u v w
    rw [affDim, if_neg h3] at h2
    have hspanne : ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) ≠ ∅ := fun hc =>
      absurd (SetLike.mem_coe.2
        (mem_affineSpan ℝ (Set.mem_insert u ({v, w} : Set V3))))
        (by rw [hc]; simp)
    have hveq : vectorSpan ℝ ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3))
        = vectorSpan ℝ ({u, v, w} : Set V3) := by
      rw [← AffineSubspace.direction_eq_vectorSpan, direction_affineSpan]
    have hmono : affDim s ≤ affDim ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) :=
      affDim_mono hsub (Set.nonempty_iff_ne_empty.2 hse)
    rw [affDim, if_neg hse] at hmono
    have hspaneq : affDim ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3))
        = (Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) : ℤ) := by
      rw [affDim, if_neg hspanne]
      congr 1
      rw [hveq]
    rw [affDim, if_neg hse]
    rw [hspaneq] at hmono
    exact hmono.trans h2

/-- HOL `NOT_COLLINEAR_AFF_DIM2` (leaf_cell.hl:3913-3926). -/
theorem NOT_COLLINEAR_AFF_DIM2 (a b c : V3) (h : ¬Collinear3 a b c) :
    affDim {a, b, c} = 2 := by
  have hne : ({a, b, c} : Set V3) ≠ ∅ := by
    intro hc
    have hm : a ∈ ({a, b, c} : Set V3) := Set.mem_insert a ({b, c} : Set V3)
    rw [hc] at hm
    exact hm
  have hle := AFF_DIM_3 a b c
  have hge : ¬(Module.finrank ℝ (vectorSpan ℝ {a, b, c}) ≤ 1) := by
    intro h1
    exact h (show Collinear ℝ ({a, b, c} : Set V3) from
      (collinear_iff_finrank_le_one (s := ({a, b, c} : Set V3))).2 h1)
  rw [affDim, if_neg hne] at hle ⊢
  have h2 := hge
  push_neg at h2
  have hcast : (1:ℤ) < (Module.finrank ℝ (vectorSpan ℝ {a, b, c}) : ℤ) :=
    by exact_mod_cast h2
  omega

/-- Re-splice of PackingAuto6's private `p6_affDim_insert` (HOL
`AFF_DIM_INSERT` content): inserting a point outside the affine span raises
the affine dimension by one. -/
private theorem pa18_affDim_insert (S : Set V3) (y : V3) (hne : S.Nonempty)
    (hy : y ∉ (affineSpan ℝ S : Set V3)) :
    affDim (insert y S) = affDim S + 1 := by
  obtain ⟨y0, hy0⟩ := hne
  have hy0S : y0 ∈ (affineSpan ℝ S : Set V3) := subset_affineSpan ℝ S hy0
  set D := vectorSpan ℝ S with hD
  have mD : ∀ a ∈ S, ∀ b ∈ S, (a - b) ∈ D := by
    intro a ha b hb
    rw [hD, vectorSpan_def]
    exact Submodule.subset_span (Set.mem_vsub.2 ⟨a, ha, b, hb, rfl⟩)
  have hvec : vectorSpan ℝ (insert y S) = D ⊔ Submodule.span ℝ {y - y0} := by
    have hgen : (y - y0) ∈ vectorSpan ℝ (insert y S) := by
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨y, Set.mem_insert _ _,
        y0, Set.mem_insert_of_mem _ hy0, rfl⟩)
    have hmono : vectorSpan ℝ S ≤ vectorSpan ℝ (insert y S) :=
      vectorSpan_mono (k := ℝ) (Set.subset_insert y S)
    have hsb : ∀ r ∈ Submodule.span ℝ {y - y0}, r ∈ vectorSpan ℝ (insert y S) := by
      intro r hm
      rw [Submodule.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      exact Submodule.smul_mem _ s hgen
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      intro g hg
      obtain ⟨x, hx, x', hx', rfl⟩ := Set.mem_vsub.1 hg
      rw [SetLike.mem_coe]
      rcases Set.mem_insert_iff.1 hx with hxe | hx
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe, hxe', vsub_self]
          exact Submodule.zero_mem _
        · rw [hxe, vsub_eq_sub]
          have hv : (y - x' : V3) = (y - y0) + -(x' - y0) := by abel
          have hA : (x' - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x' hx' y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hC
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hA)
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe', vsub_eq_sub]
          have hv : (x - y : V3) = (x - y0) + -(y - y0) := by abel
          have hA : (x - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x hx y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hA
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hC)
        · exact Submodule.mem_sup_left (mD x hx x' hx')
    · intro w hw
      rcases Submodule.mem_sup.1 hw with ⟨a, ha, b, hb, hab⟩
      have haD : a ∈ vectorSpan ℝ (insert y S) := hmono ha
      have hbD : b ∈ vectorSpan ℝ (insert y S) := hsb b hb
      rw [← hab]
      exact add_mem haD hbD
  have hvD : y - y0 ∉ D := by
    intro h
    apply hy
    have hmem : (y - y0) +ᵥ y0 ∈ (affineSpan ℝ S : Set V3) :=
      AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact h) hy0S
    have h2 : (y - y0 : V3) +ᵥ y0 = y := by rw [vadd_eq_add]; abel
    rw [h2] at hmem
    exact hmem
  have hinf : D ⊓ Submodule.span ℝ {y - y0} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwK : w ∈ D := (Submodule.mem_inf.1 hw).1
    have hwS := (Submodule.mem_inf.1 hw).2
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hwS
    have hs0 : s = 0 := by
      by_contra hs0
      have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
      have h2 : (s⁻¹ • (s • (y - y0)) : V3) ∈ D := Submodule.smul_mem _ _ hwK
      rw [smul_smul, hinv, one_smul] at h2
      exact hvD h2
    rw [hs0, zero_smul]
  have hvyne : (y - y0 : V3) ≠ 0 := by
    intro h0
    rw [h0] at hvD
    exact hvD (Submodule.zero_mem D)
  have hfr : Module.finrank ℝ (vectorSpan ℝ (insert y S))
      = Module.finrank ℝ (vectorSpan ℝ S) + 1 := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq D (Submodule.span ℝ {y - y0})
    rw [hinf, finrank_bot] at h2
    have h3 : Module.finrank ℝ (Submodule.span ℝ {y - y0}) = 1 :=
      finrank_span_singleton hvyne
    rw [h3] at h2
    rw [hvec]
    omega
  have hneI : (insert y S).Nonempty := ⟨y0, Set.mem_insert_of_mem _ hy0⟩
  have hneI' : insert y S ≠ ∅ := Set.nonempty_iff_ne_empty.mp hneI
  simp only [affDim, if_neg hneI', if_neg (Set.nonempty_iff_ne_empty.mp ⟨y0, hy0⟩)]
  rw [hfr]
  omega

/-- HOL `COPLANAR_INSERT` (leaf_cell.hl:227-240): a point whose insertion
stays coplanar already sits in the affine span (contrapositive of the
`+1` dimension jump of `pa18_affDim_insert`). -/
theorem COPLANAR_INSERT {s : Set V3} (p : V3) (h : affDim s = 2)
    (hc : Coplanar (insert p s)) : p ∈ affineSpan ℝ s := by
  by_contra hcon
  have hne : s.Nonempty := by
    by_contra h0
    by_cases h0' : s = ∅
    · rw [affDim, h0'] at h
      norm_num at h
    · exact absurd (Set.nonempty_iff_ne_empty.2 h0') h0
  have hins := pa18_affDim_insert s p hne hcon
  have hle := COPLANAR_IMP_AFF_DIM hc
  rw [hins, h] at hle
  norm_num at hle

/-- HOL `COPLANAR_UNION` (leaf_cell.hl:241-303). -/
theorem COPLANAR_UNION {P Q : Set V3} {a b : V3} (hP : P ≠ ∅) (hQ : Q ≠ ∅)
    (h1 : ∀ p ∈ P, ¬Collinear3 p a b) (h2 : ∀ q ∈ Q, ¬Collinear3 q a b)
    (h3 : ∀ p ∈ P, ∀ q ∈ Q, Coplanar ({p, q, a, b} : Set V3)) :
    Coplanar (P ∪ Q ∪ {a, b} : Set V3) := by
  sorry

/-- HOL `CONNECTED_SEGMENT_NOT_COVERED` (leaf_cell.hl:304-327): a segment is
preconnected, so two disjoint open sets cannot separate its endpoints. -/
theorem CONNECTED_SEGMENT_NOT_COVERED {A B : Set V3} {a b : V3}
    (hA : IsOpen A) (hB : IsOpen B) (ha : a ∈ A) (hb : b ∈ B) (hd : A ∩ B = ∅) :
    ∃ x, x ∈ segment ℝ a b ∧ x ∉ A ∧ x ∉ B := by
  by_contra hcon
  push_neg at hcon
  have hconn := (convex_segment a b).isPreconnected
  have hsub : (segment ℝ a b) ⊆ A ∪ B := fun y hy => by
    by_cases hyA : y ∈ A
    · exact Set.mem_union_left _ hyA
    · exact Set.mem_union_right _ (hcon y hy hyA)
  obtain ⟨x, hxmem, hxAB⟩ := hconn A B hA hB hsub
    ⟨a, left_mem_segment ℝ a b, ha⟩ ⟨b, right_mem_segment ℝ a b, hb⟩
  rw [hd, Set.mem_empty_iff_false] at hxAB
  exact hxAB

/-- HOL `WEDGE_GE_NULL` (leaf_cell.hl:91-106): when the second ray coincides
with the first in azimuth, the closed wedge is the half-plane `aff_ge`. -/
theorem WEDGE_GE_NULL (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) (haz : azim u0 u1 v1 v2 = 0) :
    wedgeGe u0 u1 v1 v2 = affGe {u0, u1} {v1} := by
  refine Set.ext (fun z => ?_)
  constructor
  · intro hz
    rw [wedgeGe, Set.mem_setOf_eq, haz] at hz
    exact (pa18_azim_zero_affGe h1).1 (le_antisymm hz.2 hz.1)
  · intro hz
    rw [wedgeGe, Set.mem_setOf_eq]
    have h0 : azim u0 u1 v1 z = 0 := (pa18_azim_zero_affGe h1).2 hz
    refine ⟨azim_nonneg u0 u1 v1 z, ?_⟩
    rw [h0, haz]

/-- HOL `WEDGE_WEDGE_GE` (leaf_cell.hl:107-153): the closed wedge splits into
the open wedge and the two bounding half-planes. -/
theorem WEDGE_WEDGE_GE (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) :
    wedgeGe u0 u1 v1 v2 ⊆ wedge u0 u1 v1 v2 ∪ affGe {u0, u1} {v1} ∪
      affGe {u0, u1} {v2} := by
  intro z hz
  rw [wedgeGe, Set.mem_setOf_eq] at hz
  by_cases h0 : azim u0 u1 v1 z = 0
  · exact Set.mem_union_left _ (Or.inr ((pa18_azim_zero_affGe h1).1 h0))
  · by_cases hcol : Collinear3 u0 u1 z
    · exact absurd (by rw [azim, if_pos (Or.inr hcol)] : azim u0 u1 v1 z = 0) h0
    · rcases lt_or_eq_of_le hz.2 with hlt | heq
      · refine Set.mem_union_left _ (Or.inl ⟨hcol, ?_, hlt⟩)
        exact lt_of_le_of_ne (azim_nonneg u0 u1 v1 z) (Ne.symm h0)
      · have hiff := azim_eq_azim_iff h1 h2 hcol
        have hgt : z ∈ affGt ({u0, u1} : Set V3) ({v2} : Set V3) := hiff.1 heq.symm
        rcases hgt with ⟨f, hf, hvec, hpos, hone⟩
        exact Set.mem_union_right _ (by
          rw [affGe, Set.mem_setOf_eq, Affsign]
          exact ⟨f, hf, hvec, fun w2 hw2 => le_of_lt (hpos w2 hw2), hone⟩)

/-- HOL `WEDGE_GE_ALMOST_DISJOINT` (leaf_cell.hl:154-208). -/
theorem WEDGE_GE_ALMOST_DISJOINT (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) :
    wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
      affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} := by
  sorry

/-- HOL `GBEWYFX` (leaf_cell.hl:328-341), via `MHFTTZN1` (affine dimension of
a `barV` list) and Mathlib's `collinear_iff_finrank_le_one`. -/
theorem GBEWYFX {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V ul) : ¬Collinear3 ul[0]! ul[1]! ul[2]! := by
  have h3 : ul.length = 3 := hl'.1.1
  have hbar : barV V 2 ul := hl'.1
  have hdim0 : affDim (setOfList ul) = 2 := MHFTTZN1 V ul 2 hp hbar
  obtain ⟨a, b, c, hlist⟩ : ∃ a b c, ul = [a, b, c] := by
    cases ul with
    | nil => exact absurd h3 (by simp)
    | cons x t =>
      cases t with
      | nil => exact absurd h3 (by simp)
      | cons y t2 =>
        cases t2 with
        | nil => exact absurd h3 (by simp)
        | cons z t3 =>
          cases t3 with
          | nil => exact ⟨x, y, z, rfl⟩
          | cons _ _ => exact absurd h3 (by simp)
  rw [hlist] at hdim0
  have hset : setOfList [a, b, c] = ({a, b, c} : Set V3) := by
    ext t
    simp [setOfList]
  rw [hset] at hdim0
  have hget : [a, b, c][0]! = a ∧ [a, b, c][1]! = b ∧ [a, b, c][2]! = c := by simp
  obtain ⟨e0, e1, e2⟩ := hget
  have hne : ({a, b, c} : Set V3) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.1 ⟨a, by simp⟩
  rw [affDim, if_neg hne] at hdim0
  intro hcol
  rw [hlist, e0, e1, e2] at hcol
  have h1 : Module.finrank ℝ (vectorSpan ℝ ({a, b, c} : Set V3)) ≤ 1 :=
    (collinear_iff_finrank_le_one (s := ({a, b, c} : Set V3))).1 hcol
  omega

/-- HOL `YBZFUPO` (leaf_cell.hl:360-423). -/
theorem YBZFUPO {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V ul) :
    ∃ p1 p2 : V3, voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧ p1 ≠ p2 ∧
      ∀ f, FacetOf f (voronoiList V ul) → f = {p1} ∨ f = {p2} := by
-- NEEDS (GIANT): voronoi_list of a leaf is a segment. HOL (leaf_cell.hl:360-423)
-- = AFF_DIM_VORONOI_LIST (PA5, proved) + a 1-dim polytope = segment
-- classification (EXPAND_EDGE_POLYTOPE analogue, absent from repo/Mathlib)
-- + segment facet kit (FACET_OF_SEGMENT here, proved).
  sorry

/-- HOL `permutes` (HOL Light sets.ml): `p` maps the set into itself, fixes
every point outside it, and is globally injective. -/
def Permutes (p : ℕ → ℕ) (s : Set ℕ) : Prop :=
  (∀ x ∈ s, p x ∈ s) ∧ (∀ x ∉ s, p x = x) ∧ ∀ x y : ℕ, p x = p y → x = y

/-- HOL `PERMUTES_a_PERMUTES_b` (leaf_cell.hl:424-462); HOL `0..a` is
`Finset.range (a+1)` as a set. -/
theorem PERMUTES_a_PERMUTES_b {p : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (h : Permutes p ((Finset.range (a + 1) : Finset ℕ))) :
    Permutes p ((Finset.range (b + 1) : Finset ℕ)) := by
  have hmid : ∀ x ∉ ((Finset.range (b + 1) : Finset ℕ) : Set ℕ), p x = x := by
    intro x hx
    refine h.2.1 x ?_
    intro hmem
    rw [Finset.mem_coe, Finset.mem_range] at hmem
    have hx1 : x < b + 1 := by omega
    exact hx (by rw [Finset.mem_coe, Finset.mem_range]; exact hx1)
  refine ⟨?_, hmid, h.2.2⟩
  intro x hx
  rw [Finset.mem_coe, Finset.mem_range] at hx ⊢
  rcases le_or_gt x a with hle | hgt
  · have hx' : p x ∈ ((Finset.range (a + 1) : Finset ℕ) : Set ℕ) :=
      h.1 x (by rw [Finset.mem_coe]; exact Finset.mem_range.2 (by omega))
    rw [Finset.mem_coe, Finset.mem_range] at hx'
    omega
  · have hfx := h.2.1 x (by
      intro hmem
      rw [Finset.mem_coe, Finset.mem_range] at hmem
      omega)
    omega

/-- HOL `PERMUTE_BARV3` (leaf_cell.hl:463-529). -/
theorem PERMUTE_BARV3 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hhl : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    {p : Equiv.Perm ℕ} (hp' : permutes p (Finset.range 2)) :
    barV V 3 (leftActionList p ul) := by
  sorry

/-- HOL `ZASUVOR` (leaf_cell.hl:530-?). -/
theorem ZASUVOR {V : Set V3} {u0 u1 u2 : V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V [u0, u1, u2]) :
    leaf V [u1, u0, u2] ∧ stem [u0, u1, u2] = stem [u1, u0, u2] := by
  sorry

/-- HOL `truncate_set_of_list` (leaf_cell.hl:530-554). -/
theorem truncate_set_of_list {vl : List V3} {k : ℕ}
    (hk : 0 < k) (hlen : vl.length = k + 1) :
    setOfList vl ⊆ setOfList (truncateSimplex (k - 1) vl) ∪ {vl.getD k 0} := by
  have hle : (k - 1) + 1 ≤ vl.length := by omega
  have hspec : ((truncateSimplex (k - 1) vl).length = (k - 1) + 1 ∧
      initialSublist (truncateSimplex (k - 1) vl) vl) :=
    Classical.epsilon_spec (p := fun xl : List V3 => xl.length = (k - 1) + 1 ∧ initialSublist xl vl)
      ⟨vl.take ((k - 1) + 1), List.length_take_of_le (by omega),
        ⟨vl.drop ((k - 1) + 1), (List.take_append_drop ((k - 1) + 1) vl).symm⟩⟩
  obtain ⟨yl, hyl⟩ := hspec.2
  have htrlen : (truncateSimplex (k - 1) vl).length = k := by omega
  have hyl1 : yl.length = 1 := by
    have hsum : vl.length = (truncateSimplex (k - 1) vl).length + yl.length := by
      conv_lhs => rw [hyl]
      rw [List.length_append]
    rw [htrlen, hlen] at hsum
    omega
  obtain ⟨y, hyy⟩ : ∃ y, yl = [y] := by
    cases yl with
    | nil => exact absurd hyl1 (by simp)
    | cons z t =>
      cases t with
      | nil => exact ⟨z, rfl⟩
      | cons z2 t2 => exact absurd hyl1 (by simp)
  have hyk : vl.getD k 0 = y := by
    rw [hyy] at hyl
    rw [hyl, List.getD_append_right _ _ _ _ (by rw [htrlen]), htrlen]
    simp
  intro x hx
  rw [hyl] at hx
  rcases List.mem_append.1 hx with hx' | hx'
  · exact Set.mem_union_left _ hx'
  · rw [Set.mem_union, Set.mem_singleton_iff, hyk]
    rw [hyy] at hx'
    simp at hx'
    exact Or.inr hx'

private theorem sub_dot18 (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem list3_eq (ul : List V3) (h : ul.length = 3) :
    ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := by
  cases ul with
  | nil => exact absurd h (by simp)
  | cons a t =>
    cases t with
    | nil => exact absurd h (by simp)
    | cons b t2 =>
      cases t2 with
      | nil => exact absurd h (by simp)
      | cons c t3 =>
        cases t3 with
        | nil => rfl
        | cons _ _ => exact absurd h (by simp)

private theorem dot_sub18 (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_smul18 (t : ℝ) (a b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_comm18 (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem coe_smul18 (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem coe_sub18 (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

/-- `chi_msb` on an explicit triple as a row determinant. -/
private theorem chiMsb_det (a b c d : V3) :
    chiMsb [a, b, c] d
      = Matrix.det ![((d - a : V3) : Fin 3 → ℝ), ((b - a : V3) : Fin 3 → ℝ),
        ((c - a : V3) : Fin 3 → ℝ)] := by
  have h1 : chiMsb [a, b, c] d
      = ((d - a : V3) : Fin 3 → ℝ) ⬝ᵥ (crossProduct ((b - a : V3) : Fin 3 → ℝ)
          ((c - a : V3) : Fin 3 → ℝ)) := by
    simp only [chiMsb, List.getElem!_cons_succ, List.getElem!_cons_zero, List.getD_cons_succ,
      List.getD_cons_zero]
    exact dotProduct_comm _ _
  rw [h1, triple_product_eq_det]

private theorem coe_add18 (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

/-- norm-squares equal implies norms equal (helper for DIST_EQ_HALF_PLANE). -/
private theorem norm_eq_of_sq_eq {u v : V3} (h : ‖u‖ ^ 2 = ‖v‖ ^ 2) : ‖u‖ = ‖v‖ := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg (R := ℝ)).1 h with h1 | h1
  · exact h1
  · have hnu : (0:ℝ) ≤ ‖u‖ := norm_nonneg u
    have hnv : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
    have hu : ‖u‖ = 0 := by linarith
    have hv : ‖v‖ = 0 := by linarith
    rw [norm_eq_zero.1 hu, norm_eq_zero.1 hv]

private theorem dist_sq_diff (x a b : V3) :
    (a - b) ⬝ᵥ (2 • x - (a + b)) = ‖x - b‖ ^ 2 - ‖x - a‖ ^ 2 := by
  rw [Kepler.Geom.norm_sq_eq_dot (x - b), Kepler.Geom.norm_sq_eq_dot (x - a)]
  simp only [coe_sub18, coe_add18, coe_smul18, dotProduct_sub, sub_dotProduct,
    dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_comm]
  ring

/-- HOL `DIST_LE_HALF_PLANE` (leaf_cell.hl:555-573). -/
theorem DIST_LE_HALF_PLANE (x a b : V3) :
    dist x a ≤ dist x b ↔ 0 ≤ (a - b) ⬝ᵥ (2 • x - (a + b)) := by
  rw [dist_eq_norm, dist_eq_norm, dist_sq_diff]
  have h1 := norm_nonneg (x - a)
  have h2 := norm_nonneg (x - b)
  constructor <;> intro h <;> nlinarith

/-- HOL `DIST_EQ_HALF_PLANE` (leaf_cell.hl:574-780). -/
theorem DIST_EQ_HALF_PLANE (x a b : V3) :
    dist x a = dist x b ↔ (a - b) ⬝ᵥ (2 • x - (a + b)) = 0 := by
  rw [dist_eq_norm, dist_eq_norm, dist_sq_diff]
  constructor
  · intro h
    rw [h]
    linarith
  · intro h
    exact norm_eq_of_sq_eq (u := x - a) (v := x - b) (by linarith)

/-- HOL `FUZBZGI_0` (leaf_cell.hl:781-835). -/
theorem FUZBZGI_0 {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
    (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
    (hfac : ∀ f, FacetOf f (voronoiList V ul) → f = {p1} ∨ f = {p2}) :
    0 < t2 := by
-- NEEDS (GIANT): the positive-coefficient half. HOL (leaf_cell.hl:588-731)
-- consumes Rogers.XYOFCGX, which is still sorry in PackingAuto7 (out of
-- PA18 scope); DIST_LT/eq_HALF_PLANE are proved here.
  sorry

/-- HOL `FUZBZGI_1` (leaf_cell.hl:781-835). -/
theorem FUZBZGI_1 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    ∃ p1 p2 : V3, ∃ t1 t2 : ℝ, voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧
      p1 ≠ p2 ∧ circumcenter (setOfList ul) = t1 • p1 + t2 • p2 ∧ t1 + t2 = 1 ∧
      0 < t1 ∧ 0 < t2 := by
-- NEEDS (GIANT): waits on FUZBZGI_0 (XYOFCGX@PA7); the YBZFUPO half plus
-- the MHFTTZN3 circumcenter-affinity are mechanical once that lands.
  sorry

/-- HOL `chi_msb_swap_01` (leaf_cell.hl:803-835). -/
theorem chi_msb_swap_01 (a b c d : V3) :
    chiMsb [a, b, c] d = -chiMsb [b, a, c] d := by
  rw [chiMsb_det, chiMsb_det]
  simp only [Matrix.det_fin_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val',
    coe_sub18, Pi.sub_apply]
  ring

/-- HOL `chi_msb_swap_23` (leaf_cell.hl:803-835). -/
theorem chi_msb_swap_23 (a b c d : V3) :
    chiMsb [a, b, c] d = -chiMsb [a, b, d] c := by
  rw [chiMsb_det, chiMsb_det]
  simp only [Matrix.det_fin_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val',
    coe_sub18, Pi.sub_apply]
  ring

/-- HOL `chi_msb_swap_12` (leaf_cell.hl:803-835). -/
theorem chi_msb_swap_12 (a b c d : V3) :
    chiMsb [a, b, c] d = -chiMsb [a, c, b] d := by
  rw [chiMsb_det, chiMsb_det]
  simp only [Matrix.det_fin_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val',
    coe_sub18, Pi.sub_apply]
  ring

/-- HOL `chi_msb_additive_a` (leaf_cell.hl:836-861). -/
theorem chi_msb_additive_a (a b c d : V3) (t1 t2 t3 t4 : ℝ) (ht : t1 + t2 + t3 + t4 = 1) :
    chiMsb [t1 • a + t2 • b + t3 • c + t4 • d, b, c] d
      = t1 * chiMsb [a, b, c] d := by
  have ht4 : t4 = 1 - t1 - t2 - t3 := by linarith
  subst ht4
  rw [chiMsb_det, chiMsb_det]
  simp only [Matrix.det_fin_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val',
    coe_sub18, coe_smul18, coe_add18, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- HOL `chi_msb_additive_d` (leaf_cell.hl:862-878). -/
theorem chi_msb_additive_d (a b c d : V3) (t1 t2 t3 t4 : ℝ) (ht : t1 + t2 + t3 + t4 = 1) :
    chiMsb [a, b, c] (t1 • a + t2 • b + t3 • c + t4 • d)
      = t4 * chiMsb [a, b, c] d := by
  have ht4 : t4 = 1 - t1 - t2 - t3 := by linarith
  subst ht4
  rw [chiMsb_det, chiMsb_det]
  simp only [Matrix.det_fin_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val',
    coe_sub18, coe_smul18, coe_add18, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- HOL `CHI_MSB_ADDITIVE` (leaf_cell.hl:879-890). -/
theorem CHI_MSB_ADDITIVE (ul : List V3) (p1 p2 : V3) (t1 t2 : ℝ) (ht : t1 + t2 = 1) :
    chiMsb ul (t1 • p1 + t2 • p2)
      = t1 * chiMsb ul p1 + t2 * chiMsb ul p2 := by
  have key : ((t1 • p1 + t2 • p2 - ul[0]! : V3) : Fin 3 → ℝ)
      = t1 • ((p1 - ul[0]! : V3) : Fin 3 → ℝ)
        + t2 • ((p2 - ul[0]! : V3) : Fin 3 → ℝ) := by
    simp only [coe_sub18, coe_add18, coe_smul18]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((ul[0]! : Fin 3 → ℝ) i) * ht
  simp only [chiMsb]
  rw [key, dotProduct_add, dotProduct_smul, dotProduct_smul]
  ring

/-- HOL `CHI_MSB_CONVEX` (leaf_cell.hl:891-934). -/
theorem CHI_MSB_CONVEX (ul : List V3) :
    Convex ℝ {p | 0 ≤ chiMsb ul p} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq]
  rw [CHI_MSB_ADDITIVE ul x y a b hab]
  have h1 : 0 ≤ a * chiMsb ul x := mul_nonneg ha hx
  have h2 : 0 ≤ b * chiMsb ul y := mul_nonneg hb hy
  linarith

/-- HOL `AFFINE_IMP_CHI_MSB_0` (leaf_cell.hl:935-942): `chi_msb` is the signed
volume over the stem triple, so it vanishes on the triple's affine span
(linearity of the first determinant row + the two degenerate rows). -/
theorem AFFINE_IMP_CHI_MSB_0 (ul : List V3) (p : V3) (hlen : ul.length = 3)
    (hp : p ∈ affineSpan ℝ (setOfList ul)) : chiMsb ul p = 0 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, ul = [a, b, c] := ⟨_, _, _, list3_eq ul hlen⟩
  have hset : setOfList [a, b, c] = ({a, b, c} : Set V3) := by
    ext t
    simp [setOfList]
    all_goals tauto
  rw [hset] at hp
  have hdir : (p -ᵥ a : V3) ∈ (affineSpan ℝ ({a, b, c} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction hp
      (mem_affineSpan ℝ (Set.mem_insert a ({b, c} : Set V3)))
  rw [direction_affineSpan] at hdir
  have hsub : vectorSpan ℝ ({a, b, c} : Set V3) ≤
      Submodule.span ℝ ({a - b, a - c} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_left (k := ℝ) (Set.mem_insert a ({b, c} : Set V3)),
      Submodule.span_le]
    rintro d ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx1 | hx1 | hx1
    · rw [hx1]
      show (a -ᵥ a : V3) ∈ Submodule.span ℝ ({a - b, a - c} : Set V3)
      rw [vsub_self]
      exact Submodule.zero_mem _
    · rw [hx1]
      exact Submodule.subset_span (Set.mem_insert (a - b) ({a - c} : Set V3))
    · rw [hx1]
      exact Submodule.subset_span (Or.inr (Set.mem_singleton (a - c)))
  obtain ⟨r2, r3, hv2⟩ := Submodule.mem_span_pair.1 (hsub hdir)
  have hpa : (p - a : V3) = p -ᵥ a := rfl
  have hrow : ((p - a : V3) : Fin 3 → ℝ)
      = (-r2) • ((b - a : V3) : Fin 3 → ℝ) + (-r3) • ((c - a : V3) : Fin 3 → ℝ) := by
    rw [hpa, ← hv2, coe_add18, coe_smul18, coe_smul18, coe_sub18, coe_sub18]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, coe_sub18]
    ring
  rw [chiMsb_det, hrow]
  simp only [Matrix.det_fin_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val',
    coe_sub18, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- HOL `CHI_MSB_IMP_COPLANAR` (leaf_cell.hl:935-942). -/
theorem CHI_MSB_IMP_COPLANAR (ul : List V3) (p : V3) (h : chiMsb ul p = 0) :
    Coplanar ({ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, p} : Set V3) := by
-- NEEDS: coplanar <-> chi_msb = 0 needs the cross-dot equivalence
-- (local_lemmas.hl:203; LocalAuto5 has a lane-local copy built on its
-- private kit); unlocks JDHAWAY_0/JDWAWAY and CFFONNL.
  sorry

/-- HOL `CHI_MSB_COPLANAR` (leaf_cell.hl:943-1011). -/
theorem CHI_MSB_COPLANAR (a b c d : V3) :
    Coplanar ({a, b, c, d} : Set V3) ↔ chiMsb [a, b, c] d = 0 := by
-- NEEDS: same cross-dot equivalence as CHI_MSB_IMP_COPLANAR.
  sorry

/-- HOL `JDHAWAY_0` (leaf_cell.hl:1012-1051). -/
theorem JDHAWAY_0 {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
    (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
    (hpos : 0 < t1 ∧ 0 < t2) : chiMsb ul p1 ≠ 0 := by
-- NEEDS: waits on CHI_MSB_IMP_COPLANAR + CHI_MSB_ADDITIVE; the remaining
-- half (COPLANAR_INSERT now proved + MHFTTZN1/MHFTTZN3 +
-- BARV_CIRCUMCENTER_EXISTS) is mechanical.
  sorry

/-- HOL `JDHAWAY_1` (leaf_cell.hl:1012-1051): the circumcenter of the stem
lies in the stem's affine span, where `chi_msb` vanishes. -/
theorem JDHAWAY_1 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    chiMsb ul (circumcenter (setOfList ul)) = 0 := by
  have h3 : ul.length = 3 := hl'.1.1
  have hmem : circumcenter (setOfList ul) ∈ (affineSpan ℝ (setOfList ul) : Set V3) :=
    BARV_CIRCUMCENTER_EXISTS V ul 2 hp hl'.1
  exact AFFINE_IMP_CHI_MSB_0 ul (circumcenter (setOfList ul)) h3 hmem

/-- HOL `JDWAWAY` (leaf_cell.hl:1012-1051). -/
theorem JDWAWAY {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
    (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
    (hpos : 0 < t1 ∧ 0 < t2) :
    chiMsb ul p1 ≠ 0 ∧ chiMsb ul p2 ≠ 0 ∧ (chiMsb ul p1 < 0 ↔ 0 < chiMsb ul p2) := by
-- NEEDS: waits on JDHAWAY_0; the sign flip is JDHAWAY_1 +
-- CHI_MSB_ADDITIVE arithmetic (both proved).
  sorry

/-- HOL `CC_CELL4` (leaf_cell.hl:1143-?): the 4-case Marchal cell is the
Delaunay tetrahedron over `cc_uh`. -/
theorem CC_CELL4 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h4 : ccKe V ul = 4) :
    ccCell V ul = convexHull ℝ (setOfList (ccUh V ul)) := by
  unfold ccCell ccKe at *
  rw [h4]
  have hif : hl (ccUh V ul) < Real.sqrt 2 := by
    by_contra hc
    rw [if_neg hc] at h4
    exact absurd h4 (by norm_num)
  have hd : mcell 4 V (ccUh V ul) = mcell4 V (ccUh V ul) := by
    rw [mcell]; simp
  rw [hd, mcell4, if_pos hif]

/-- HOL `CC_KE_34` (leaf_cell.hl:1245-?): the dispatch value is 3 or 4. -/
theorem CC_KE_34 (V : Set V3) (ul : List V3) : ccKe V ul = 3 ∨ ccKe V ul = 4 := by
  unfold ccKe
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem pa18_trunc2_setOfList {L : List V3} (h4 : L.length = 4) :
    setOfList (truncateSimplex 2 L)
      = ({L.getD 0 0, L.getD 1 0, L.getD 2 0} : Set V3) := by
  obtain ⟨a, b, c, d, hL⟩ : ∃ a b c d, L = [a, b, c, d] := by
    cases L with
    | nil => exact absurd h4 (by simp)
    | cons x t =>
      cases t with
      | nil => exact absurd h4 (by simp)
      | cons y t2 =>
        cases t2 with
        | nil => exact absurd h4 (by simp)
        | cons z t3 =>
          cases t3 with
          | nil => exact absurd h4 (by simp)
          | cons w t4 =>
            cases t4 with
            | nil => exact ⟨x, y, z, w, rfl⟩
            | cons _ _ => exact absurd h4 (by simp)
  subst hL
  have hinit : initialSublist [a, b, c] [a, b, c, d] := ⟨[d], rfl⟩
  have htr : truncateSimplex 2 [a, b, c, d] = [a, b, c] :=
    ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST 2 _ _).2 ⟨hinit, by simp⟩).1
  rw [htr]
  ext t
  simp [setOfList]

private theorem pa18_list4_setOfList {L : List V3} (h4 : L.length = 4) :
    setOfList L = ({L.getD 0 0, L.getD 1 0, L.getD 2 0, L.getD 3 0} : Set V3) := by
  obtain ⟨a, b, c, d, hL⟩ : ∃ a b c d, L = [a, b, c, d] := by
    cases L with
    | nil => exact absurd h4 (by simp)
    | cons x t =>
      cases t with
      | nil => exact absurd h4 (by simp)
      | cons y t2 =>
        cases t2 with
        | nil => exact absurd h4 (by simp)
        | cons z t3 =>
          cases t3 with
          | nil => exact absurd h4 (by simp)
          | cons w t4 =>
            cases t4 with
            | nil => exact ⟨x, y, z, w, rfl⟩
            | cons _ _ => exact absurd h4 (by simp)
  subst hL
  ext t
  simp [setOfList]

/-- HOL `CC_CELL3` (leaf_cell.hl:1180-1210): the dispatch value 3 selects
`mcell3`, whose defining condition holds for a leaf stem (`hl` bounds from
`leaf` and from `ccKe = 3`). -/
theorem CC_CELL3 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    ccCell V ul = convexHull ℝ (setOfList (truncateSimplex 2 (ccUh V ul)) ∪
      {mxi V (ccUh V ul)}) := by
  have hbar := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  have htrunc : truncateSimplex 2 (ccUh V ul) = ul := hbar.2.1
  unfold ccCell ccKe at *
  rw [h3]
  have hif : ¬(hl (ccUh V ul) < Real.sqrt 2) := by
    intro hc
    rw [if_pos hc] at h3
    exact absurd h3 (by norm_num)
  have hle : Real.sqrt 2 ≤ hl (ccUh V ul) := le_of_not_gt hif
  have hlt : hl (truncateSimplex 2 (ccUh V ul)) < Real.sqrt 2 := by
    rw [htrunc]
    exact hl'.2
  have hd : mcell 3 V (ccUh V ul) = mcell3 V (ccUh V ul) := by
    rw [mcell]
    simp
  rw [hd, mcell3, if_pos ⟨hlt, hle⟩]

/-- HOL `CC_CELL34` (leaf_cell.hl:1210-1244): case split on the dispatch value,
then reduce both hulls to the four extreme points. -/
theorem CC_CELL34 {V : Set V3} {ul : List V3} {pp : V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    ccCell V ul = convexHull ℝ ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, pp} : Set V3) := by
  have hbar := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  by_cases h3 : ccKe V ul = 3
  · have hpp' : pp = mxi V (ccUh V ul) := by rw [hpp, if_pos h3]
    have hlen : (ccUh V ul).length = 4 := hbar.1.1
    rw [CC_CELL3 hp hs hl' h3, hpp', pa18_trunc2_setOfList hlen]
    congr 1
    ext t
    simp
    tauto
  · have h4 : ccKe V ul = 4 := by
      rcases CC_KE_34 V ul with h | h
      · exact absurd h h3
      · exact h
    have hpp' : pp = (ccUh V ul).getD 3 0 := by rw [hpp, if_neg h3]
    have hlen : (ccUh V ul).length = 4 := hbar.1.1
    rw [CC_CELL4 hp hs hl' h4, pa18_list4_setOfList hlen, hpp']

/-- HOL `U2_IN_CC_CELL` (leaf_cell.hl:1245-?): the third stem point is an
extreme point of the cc cell. -/
theorem U2_IN_CC_CELL {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    (ccUh V ul).getD 2 0 ∈ ccCell V ul := by
  have h34 := CC_CELL34 (V := V) (ul := ul)
    (pp := if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0)
    hp hs hl' rfl
  rw [h34]
  exact subset_convexHull ℝ _ (by simp)

/-- HOL `U2_IN_AFF_GT` (leaf_cell.hl:1250-1276): a point is trivially a
positive combination of itself (the indicator function of the singleton). -/
theorem U2_IN_AFF_GT {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    (ccUh V ul).getD 2 0 ∈ affGt {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0}
      {(ccUh V ul).getD 2 0} := by
  set a := (ccUh V ul).getD 0 0 with ha
  set b := (ccUh V ul).getD 1 0 with hb
  set c := (ccUh V ul).getD 2 0 with hc
  rw [affGt, Set.mem_setOf_eq, Affsign]
  have hfin : ({a, b} ∪ {c} : Set V3).Finite :=
    Set.Finite.union (Set.Finite.insert a (Set.finite_singleton b)) (Set.finite_singleton c)
  refine ⟨fun w => if w = c then (1 : ℝ) else 0, hfin, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single c]
    · simp
    · intro w _ hw
      simp [hw]
    · intro hcon
      exact absurd (hfin.mem_toFinset.2 (Set.mem_union_right _ (Set.mem_singleton c))) hcon
  · intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    simp
  · rw [Finset.sum_eq_single c]
    · simp
    · intro w _ hw
      simp [hw]
    · intro hcon
      exact absurd (hfin.mem_toFinset.2 (Set.mem_union_right _ (Set.mem_singleton c))) hcon


/-- HOL `MCELL_EDGE_FIRST` (leaf_cell.hl:3338-3374). -/
theorem MCELL_EDGE_FIRST {V : Set V3} {ul : List V3} {k : ℕ} {u v : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell k V ul)) :
    ∃ vl, barV V 3 vl ∧ mcell k V vl = mcell k V ul ∧ u = vl.getD 0 0 ∧
      v = vl.getD 1 0 := by
-- NEEDS: leaf_cell.hl:3338-3374 family (see MCELL2/3/4_EDGE_FIRST).
  sorry

private theorem list4_eq (ul : List V3) (h : ul.length = 4) :
    ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, ul.getD 3 0] := by
  cases ul with
  | nil => exact absurd h (by simp)
  | cons a t =>
    cases t with
    | nil => exact absurd h (by simp)
    | cons b t2 =>
      cases t2 with
      | nil => exact absurd h (by simp)
      | cons c t3 =>
        cases t3 with
        | nil => exact absurd h (by simp)
        | cons d t4 =>
          cases t4 with
          | nil => rfl
          | cons _ _ => exact absurd h (by simp)

/-- HOL `BARV3_TRUNC2` (leaf_cell.hl:3375-?). -/
theorem BARV3_TRUNC2 {V : Set V3} {ul : List V3} (hb : barV V 3 ul) :
    truncateSimplex 2 ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := by
  have h4 := hb.1
  rw [list4_eq ul h4]
  have hinit : initialSublist [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0]
      [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, ul.getD 3 0] := ⟨[ul.getD 3 0], rfl⟩
  exact ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST 2 _ _).2 ⟨hinit, by simp⟩).1

/-- HOL `EL_CC_UH` (leaf_cell.hl:1277-1313): the first three entries of
`cc_uh` agree with `ul`. -/
theorem EL_CC_UH {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    (ccUh V ul).getD 0 0 = ul.getD 0 0 ∧ (ccUh V ul).getD 1 0 = ul.getD 1 0 ∧
      (ccUh V ul).getD 2 0 = ul.getD 2 0 := by
  have hb := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  have h3 : ul.length = 3 := hl'.1.1
  have hbar : barV V 3 (ccUh V ul) := hb.1
  have htrunc : truncateSimplex 2 (ccUh V ul) = ul := hb.2.1
  rw [BARV3_TRUNC2 hbar] at htrunc
  injection htrunc.trans (list3_eq ul h3) with h1 ht1
  injection ht1 with h2 ht2
  injection ht2 with h3' _
  exact ⟨h1, h2, h3'⟩

/-- HOL `NUNRRDS_0` (leaf_cell.hl:1314-?): `cc_A0` meets `cc_cell` because the
third stem point lies in both. -/
theorem NUNRRDS_0 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    ccA0 ul ∩ ccCell V ul ≠ ∅ := by
  have hA := U2_IN_AFF_GT (V := V) (ul := ul) hp hs hl'
  have hC := U2_IN_CC_CELL (V := V) (ul := ul) hp hs hl'
  have hE := EL_CC_UH (V := V) (ul := ul) hp hs hl'
  have h3 : ul.length = 3 := hl'.1.1
  have hget : ul[0]! = ul.getD 0 0 ∧ ul[1]! = ul.getD 1 0 ∧ ul[2]! = ul.getD 2 0 := by
    cases ul with
    | nil => exact absurd h3 (by simp)
    | cons x t =>
      cases t with
      | nil => exact absurd h3 (by simp)
      | cons y t2 =>
        cases t2 with
        | nil => exact absurd h3 (by simp)
        | cons z t3 =>
          cases t3 with
          | nil => simp
          | cons _ _ => exact absurd h3 (by simp)
  obtain ⟨g0, g1, g2⟩ := hget
  have hmem : (ccUh V ul).getD 2 0 ∈ ccA0 ul := by
    unfold ccA0
    rw [g0, g1, g2, ← hE.1, ← hE.2.1, ← hE.2.2]
    exact hA
  have hmemC : (ccUh V ul).getD 2 0 ∈ ccA0 ul ∩ ccCell V ul := Set.mem_inter hmem hC
  intro hcon
  rw [hcon] at hmemC
  exact hmemC

/-- HOL `AFF_GE_MONO_TRANS` (leaf_cell.hl:1314-1390). -/
theorem AFF_GE_MONO_TRANS {X Y S : Set V3} (h : S ⊆ X) :
    affGe (X \ S) (Y ∪ S) ⊆ affGe X Y := by
  intro v hv
  simp only [affGe, Affsign, Set.mem_setOf_eq] at hv
  obtain ⟨f, hfin, hvsum, hsgn, hone⟩ := hv
  set E : Set V3 := (X \ S) ∪ (Y ∪ S) with hE
  have hEsub : X ∪ Y ⊆ E := by
    intro w hw
    rcases (Set.mem_union w X Y).1 hw with hw' | hw'
    · by_cases hwS : w ∈ S
      · exact Set.mem_union_right _ (Set.mem_union_right Y hwS)
      · exact Set.mem_union_left _ ((Set.mem_sdiff w).2 ⟨hw', hwS⟩)
    · exact Set.mem_union_right _ (Set.mem_union_left _ hw')
  have hfinXY : (X ∪ Y).Finite := hfin.subset hEsub
  set g : V3 → ℝ := fun w => if w ∈ E then f w else 0 with hg
  have hgg : ∀ w ∈ E, g w = f w := by intro w hw; simp only [hg, if_pos hw]
  have hsub2 : hfin.toFinset ⊆ hfinXY.toFinset := by
    intro w hw
    refine hfinXY.mem_toFinset.2 ?_
    rcases (Set.mem_union w _ _).1 (hfin.mem_toFinset.1 hw) with hw' | hw'
    · exact Set.mem_union_left _ ((Set.mem_sdiff w).1 hw').1
    · rcases (Set.mem_union w Y S).1 hw' with hw'' | hw''
      · exact Set.mem_union_right X hw''
      · exact Set.mem_union_left Y (h hw'')
  have hsumE : ∑ w ∈ hfin.toFinset, g w • w = v := by
    rw [hvsum]
    exact Finset.sum_congr rfl fun w hw => by rw [hgg w (hfin.mem_toFinset.1 hw)]
  have h1 : ∑ w ∈ hfin.toFinset, g w • w = ∑ w ∈ hfinXY.toFinset, g w • w := by
    refine Finset.sum_subset hsub2 ?_
    intro w _ hw
    simp only [hg, if_neg (hfin.mem_toFinset.not.1 hw), zero_smul]
  have hsumV : v = ∑ w ∈ hfinXY.toFinset, g w • w := (h1.symm.trans hsumE).symm
  have hsgnY : ∀ w ∈ Y, 0 ≤ g w := by
    intro w hw
    have hwE : w ∈ E := Set.mem_union_right _ (Set.mem_union_left _ hw)
    rw [hgg w hwE]
    exact hsgn w (Set.mem_union_left _ hw)
  have honeE : ∑ w ∈ hfin.toFinset, g w = 1 := by
    rw [← hone]
    exact Finset.sum_congr rfl fun w hw => by rw [hgg w (hfin.mem_toFinset.1 hw)]
  have h2 : ∑ w ∈ hfin.toFinset, g w = ∑ w ∈ hfinXY.toFinset, g w := by
    refine Finset.sum_subset hsub2 ?_
    intro w _ hw
    simp only [hg, if_neg (hfin.mem_toFinset.not.1 hw)]
  have honeG : ∑ w ∈ hfinXY.toFinset, g w = 1 := h2.symm.trans honeE
  exact ⟨g, hfinXY, hsumV, hsgnY, honeG⟩

/-- HOL `LIST_OF_CC_UH` (leaf_cell.hl:2750-2764). -/
theorem LIST_OF_CC_UH {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) :
    ccUh V ul = [(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
      (ccUh V ul).getD 3 0] := by
  have hb := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  exact list4_eq _ hb.1.1

/-- HOL `SET_OF_LIST_CC_UH` (leaf_cell.hl:2765-2792). -/
theorem SET_OF_LIST_CC_UH {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) :
    setOfList (ccUh V ul) = {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, (ccUh V ul).getD 3 0} := by
  rw [LIST_OF_CC_UH hs hp hl']
  ext t
  simp [setOfList]
  all_goals tauto

/-- HOL `K4_CHI_MSB_EQVL` (leaf_cell.hl:1391-?): the fourth `cc_uh` point is
a positive-scaled image of `cc_pe1` under the row-`d` linearity of
`chi_msb` (via `XNHPWAB2` on the `cc_uh` list). -/
theorem K4_CHI_MSB_EQVL {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h4 : ccKe V ul = 4) :
    reEqvl (chiMsb ul ((ccUh V ul).getD 3 0)) (chiMsb ul (ccPe1 V ul)) := by
  have hbar := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  have hQ := Classical.choose_spec (Classical.choose_spec (cc_pe_exists V ul)) hp hs hl'
  obtain ⟨e0, e1, e2⟩ := EL_CC_UH hp hs hl'
  have hhl4 : hl (ccUh V ul) < Real.sqrt 2 := by
    unfold ccKe at h4
    by_contra hcon
    rw [if_neg hcon] at h4
    norm_num at h4
  have hb : barV V 3 (ccUh V ul) := hbar.1
  have hom : omegaList V (ccUh V ul) = ccPe1 V ul := hbar.2.2
  have hmem : omegaList V (ccUh V ul) ∈ convexHull ℝ (setOfList (ccUh V ul)) :=
    XNHPWAB2 V (ccUh V ul) 3 hp hb hhl4
  rw [SET_OF_LIST_CC_UH hs hp hl', hom] at hmem
  rw [CONVEX_HULL_4] at hmem
  simp only [Set.mem_setOf_eq] at hmem
  obtain ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, hsum, hccPe⟩ := hmem
  have hul3 : ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := list3_eq ul hl'.1.1
  have key : chiMsb ul (ccPe1 V ul) = t4 * chiMsb ul ((ccUh V ul).getD 3 0) := by
    have hstep : ∀ q : V3, chiMsb ul q
        = chiMsb [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] q := by
      intro q
      conv_lhs => rw [hul3]
    rw [hstep (ccPe1 V ul), hstep ((ccUh V ul).getD 3 0), ← e0, ← e1, ← e2, hccPe,
      chi_msb_additive_d _ _ _ _ _ _ _ _ hsum]
  have ht4ne : t4 ≠ 0 := by
    intro h0
    rw [h0] at key
    simp at key
    exact absurd key (ne_of_gt hQ.2.2)
  have ht4pos : 0 < t4 := lt_of_le_of_ne ht4 (Ne.symm ht4ne)
  refine ⟨t4⁻¹, inv_pos.2 ht4pos, ?_⟩
  rw [key]
  field_simp

/-- HOL `K4_CHI_MSB_POS` (leaf_cell.hl:1391-?): the fourth point has strictly
positive `chi_msb` because `cc_pe1` does (`cc_pe_exists`). -/
theorem K4_CHI_MSB_POS {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h4 : ccKe V ul = 4) :
    0 < chiMsb ul ((ccUh V ul).getD 3 0) := by
  have hQ := Classical.choose_spec (Classical.choose_spec (cc_pe_exists V ul)) hp hs hl'
  obtain ⟨t, ht0, heq⟩ := K4_CHI_MSB_EQVL hp hs hl' h4
  rw [heq]
  exact mul_pos ht0 hQ.2.2

/-- HOL `MXI_BETWEEN` (leaf_cell.hl:1391-1421): `MXI_EXPLICIT` on the
`cc_uh` list reads off both the betweenness and the `sqrt 2` distance. -/
theorem MXI_BETWEEN {V : Set V3} {ul vl : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h3 : ccKe V ul = 3)
    (hv : ccUh V ul = vl) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      mxi V vl = (1 - t) • omegaListN V vl 2 + t • omegaListN V vl 3) ∧
      dist (vl.getD 0 0) (mxi V vl) = Real.sqrt 2 := by
  subst hv
  have hbar := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  have hb : barV V 3 (ccUh V ul) := hbar.1
  have hle : Real.sqrt 2 ≤ hl (ccUh V ul) := by
    unfold ccKe at h3
    by_contra hcon
    rw [if_pos (lt_of_not_ge hcon)] at h3
    norm_num at h3
  have hul3 : ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := list3_eq ul hl'.1.1
  obtain ⟨e0, e1, e2⟩ := EL_CC_UH hp hs hl'
  have h2 : hl (truncateSimplex 2 (ccUh V ul)) < Real.sqrt 2 := by
    rw [BARV3_TRUNC2 hb, e0, e1, e2, ← hul3]
    exact hl'.2
  obtain ⟨s, hseg, hdist, hmxi⟩ :=
    MXI_EXPLICIT V (ccUh V ul) _ _ _ _ hs hp hb (LIST_OF_CC_UH hs hp hl') h2 hle
  obtain ⟨u, w, hu, hw, hsum, hpt⟩ := hseg
  have hw' : 1 - w = u := by linarith [hsum]
  refine ⟨⟨w, hw, by linarith [hsum], ?_⟩, ?_⟩
  · rw [hw', ← hmxi, ← hpt]
  · rw [← hmxi, show (ccUh V ul).getD 0 0 = hdV (ccUh V ul) from by
      cases ccUh V ul <;> simp [hdV]]
    exact hdist

set_option maxHeartbeats 12000000 in
/-- HOL `affine_invert` (leaf_cell.hl:1422-1528). -/
theorem affine_invert {u : ℝ} {p q : V3} {s : Set V3} (hu : u ≠ 0)
    (haff : affineSpan ℝ s = s)
    (hm : (1 - u) • p + u • q ∈ s) (hp : p ∈ s) : q ∈ s := by
  have hr : (1 - u) • p + u • q ∈ (affineSpan ℝ s : Set V3) := by
    rw [haff]; exact hm
  have hps : p ∈ (affineSpan ℝ s : Set V3) := by
    rw [haff]; exact hp
  have hdir : (((1 - u) • p + u • q) -ᵥ p : V3) ∈ (affineSpan ℝ s).direction :=
    AffineSubspace.vsub_mem_direction hr hps
  have hscale : (q -ᵥ p : V3) = (u⁻¹ : ℝ) • (((1 - u) • p + u • q) -ᵥ p) := by
    rw [vsub_eq_sub, vsub_eq_sub, smul_sub, smul_add, smul_smul, smul_smul,
      show u⁻¹ * (1 - u) = u⁻¹ - 1 from by
        rw [mul_sub, mul_one, inv_mul_cancel₀ hu], sub_smul, one_smul,
      inv_mul_cancel₀ hu, one_smul]
    abel
  have hq : (q -ᵥ p : V3) ∈ (affineSpan ℝ s).direction := by
    rw [hscale]
    exact Submodule.smul_mem _ _ hdir
  have hmem := AffineSubspace.vadd_mem_of_mem_direction hq hps
  rw [vsub_vadd] at hmem
  have hmem2 : q ∈ (affineSpan ℝ s : Set V3) := hmem
  rwa [haff] at hmem2

/-! ## leaf_cell.hl: the cc_cell block -/

/-- HOL `CELL3_NONDEG` (leaf_cell.hl:1529-1575): the `k = 3` apex `mxi` sits
on the `o2–o3` segment with `o2` the stem circumcenter (`chi_msb` zero
there) and `o3 = cc_pe1` (`chi_msb` positive), with a positive weight. -/
theorem CELL3_NONDEG {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    (mxi V (ccUh V ul)) ∉ affineSpan ℝ (setOfList ul) ∧
      0 < chiMsb ul (mxi V (ccUh V ul)) := by
  have hbar := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  have hQ := Classical.choose_spec (Classical.choose_spec (cc_pe_exists V ul)) hp hs hl'
  have hlen4 : (ccUh V ul).length = 4 := hbar.1.1
  have htr : truncateSimplex 2 (ccUh V ul) = ul := hbar.2.1
  have ho3 : omegaListN V (ccUh V ul) 3 = ccPe1 V ul := by
    have h1 : omegaList V (ccUh V ul) = omegaListN V (ccUh V ul) 3 := by
      simp only [omegaList, hlen4]
    rw [← h1]
    exact hbar.2.2
  have ho2 : omegaListN V (ccUh V ul) 2 = circumcenter (setOfList ul) := by
    have hstab : omegaListN V (ccUh V ul) 2
        = omegaListN V (truncateSimplex 2 (ccUh V ul)) 2 :=
      OMEGA_LIST_N_LEMMA V (ccUh V ul) 2 0 (by rw [hlen4]; omega)
    have hstab2 : omegaListN V ul 2 = omegaList V ul := by
      simp only [omegaList, hl'.1.1]
    rw [hstab, htr, hstab2, XNHPWAB1 V ul 2 hp hl'.1 hl'.2]
  obtain ⟨⟨t, ht0, ht1, hmxi⟩, hdist⟩ := MXI_BETWEEN hp hs hl' h3 rfl
  have hchi : chiMsb ul (mxi V (ccUh V ul))
      = t * chiMsb ul (ccPe1 V ul) := by
    rw [hmxi, CHI_MSB_ADDITIVE ul _ _ (1 - t) t (by ring), ho2, ho3,
      JDHAWAY_1 hp hs hl', mul_zero, zero_add]
  have htpos : 0 < t := by
    by_contra hcon
    push_neg at hcon
    have htz : t = 0 := le_antisymm hcon ht0
    have hmx0 : mxi V (ccUh V ul) = circumcenter (setOfList ul) := by
      simp [hmxi, htz, ho2, ho3, one_smul, zero_smul, add_zero]
    have hd : dist ((ccUh V ul).getD 0 0) (circumcenter (setOfList ul))
        = Real.sqrt 2 := by rw [← hmx0]; exact hdist
    obtain ⟨e0, e1, e2⟩ := EL_CC_UH hp hs hl'
    have hd0 : (ccUh V ul).getD 0 0 = hdV ul := by
      rw [e0]
      show ul.getD 0 0 = List.headD ul 0
      cases ul <;> rfl
    have hHL : hl ul = dist (circumcenter (setOfList ul)) (hdV ul) :=
      HL_EQ_DIST0 V 2 ul hp hl'.1
    rw [dist_comm] at hd
    rw [hd0, ← hHL] at hd
    linarith [hd, hl'.2]
  refine ⟨fun hmem => ?_, by rw [hchi]; exact mul_pos htpos hQ.2.2⟩
  exact absurd (AFFINE_IMP_CHI_MSB_0 ul _ hl'.1.1 hmem) (ne_of_gt
    (by rw [hchi]; exact mul_pos htpos hQ.2.2))

/-- HOL `CELL_NN` (leaf_cell.hl:1529-1575): `chi_msb` is convex, the stem
triple lies in its own affine span (value zero), and the apex is positive
(`CELL3_NONDEG` / `K4_CHI_MSB_POS`), so the whole `cc_cell` hull is in the
nonnegative half-space. -/
theorem CELL_NN {V : Set V3} {ul : List V3} {p : V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (hp' : p ∈ ccCell V ul) :
    0 ≤ chiMsb ul p := by
  have h34 := CC_CELL34 (V := V) (ul := ul)
    (pp := if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0)
    hp hs hl' rfl
  have hconv := CHI_MSB_CONVEX ul
  have h3l : ul.length = 3 := hl'.1.1
  have hul3 : ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := list3_eq ul h3l
  have hmem0 : ul.getD 0 0 ∈ setOfList ul := by rw [hul3]; simp [setOfList]
  have hmem1 : ul.getD 1 0 ∈ setOfList ul := by rw [hul3]; simp [setOfList]
  have hmem2 : ul.getD 2 0 ∈ setOfList ul := by rw [hul3]; simp [setOfList]
  have hmem0' : ul.getD 0 0 ∈ affineSpan ℝ (setOfList ul) := mem_affineSpan ℝ hmem0
  have hmem1' : ul.getD 1 0 ∈ affineSpan ℝ (setOfList ul) := mem_affineSpan ℝ hmem1
  have hmem2' : ul.getD 2 0 ∈ affineSpan ℝ (setOfList ul) := mem_affineSpan ℝ hmem2
  have hsub : ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
      (if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0)} : Set V3) ⊆
      {q | 0 ≤ chiMsb ul q} := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hq
    obtain ⟨f0, f1, f2⟩ := EL_CC_UH hp hs hl'
    rcases hq with rfl | rfl | rfl | rfl
    · rw [f0]
      show 0 ≤ chiMsb ul (ul.getD 0 0)
      rw [AFFINE_IMP_CHI_MSB_0 ul _ h3l hmem0']
    · rw [f1]
      show 0 ≤ chiMsb ul (ul.getD 1 0)
      rw [AFFINE_IMP_CHI_MSB_0 ul _ h3l hmem1']
    · rw [f2]
      show 0 ≤ chiMsb ul (ul.getD 2 0)
      rw [AFFINE_IMP_CHI_MSB_0 ul _ h3l hmem2']
    · by_cases h3 : ccKe V ul = 3
      · rw [if_pos h3]
        exact le_of_lt (CELL3_NONDEG hp hs hl' h3).2
      · have h4 : ccKe V ul = 4 := by
          rcases CC_KE_34 V ul with hh | hh
          · exact absurd hh h3
          · exact hh
        rw [if_neg h3]
        exact le_of_lt (K4_CHI_MSB_POS hp hs hl' h4)
  rw [h34] at hp'
  exact convexHull_min hsub hconv hp'

/-- HOL `delta_delta_x` (leaf_cell.hl:1576-1584): the two Cayley–Menger
encodings agree. -/
theorem delta_delta_x (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaP x1 x2 x3 x6 x5 x4 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaP, deltaX]
  ring

/-- HOL `ZWVCBMN` (leaf_cell.hl:1585-1629). -/
theorem ZWVCBMN (a b c d : V3) (h : ¬Coplanar ({a, b, c, d} : Set V3)) :
    0 < MeasureTheory.volume (convexHull ℝ ({a, b, c, d} : Set V3)) := by
-- NEEDS: positive volume of a non-coplanar tetrahedron hull. HOL route
-- (VOLUME_OF_CLOSED_TETRAHEDRON + POLFLZY + DELTA_POS_4POINTS) has no
-- repo/Mathlib counterpart; blocks CC_CELL_NOT_NULLSET/FUEIMOV_K.
  sorry

/-- `¬Collinear3` for a triple keeps the triple-set affinely independent
(the bridge `OAPVION2_concl` needs; direction finrank 2 on both sides). -/
private theorem pa18_ncol3_affDep {a b c : V3} (h : ¬Collinear3 a b c) :
    ¬affineDependent ({a, b, c} : Set V3) := by
  have hdim := NOT_COLLINEAR_AFF_DIM2 a b c h
  have hne : ({a, b, c} : Set V3) ≠ ∅ := by
    intro hc
    rw [affDim, hc] at hdim
    norm_num at hdim
  have hfin : Module.finrank ℝ (vectorSpan ℝ ({a, b, c} : Set V3)) = 2 := by
    rw [affDim, if_neg hne] at hdim
    exact_mod_cast hdim
  have hne12 : a ≠ b := ne₁₂_of_not_collinear h
  have hne13 : a ≠ c := ne₁₃_of_not_collinear h
  have hne23 : b ≠ c := ne₂₃_of_not_collinear h
  have hcard : Nat.card ({a, b, c} : Set V3) = 3 := by
    have h1 : ({a, b, c} : Set V3).ncard = ({b, c} : Set V3).ncard + 1 :=
      Set.ncard_insert_of_notMem (by simp [hne12, hne13])
    have h2 : ({b, c} : Set V3).ncard = ({c} : Set V3).ncard + 1 :=
      Set.ncard_insert_of_notMem (by simp [hne23])
    have h3 : ({c} : Set V3).ncard = 1 := Set.ncard_singleton c
    have he : Nat.card ({a, b, c} : Set V3) = ({a, b, c} : Set V3).ncard := rfl
    omega
  have hcardfi : Fintype.card ↥({a, b, c} : Set V3) = 3 := by
    rwa [Nat.card_eq_fintype_card] at hcard
  have hrange : Set.range (fun x : ↥({a, b, c} : Set V3) => (x : V3))
      = ({a, b, c} : Set V3) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  intro hdep
  rw [affineDependent] at hdep
  refine hdep ?_
  rw [affineIndependent_iff_le_finrank_vectorSpan ℝ
    (fun x : ↥({a, b, c} : Set V3) => (x : V3)) (n := 2) hcardfi, hrange]
  exact hfin.ge

/-- HOL `MXI_IN_VORONOI_LIST` (leaf_cell.hl:1630-1665): `mxi` sits on the
`omega_list_n` 2–3 segment, so it lands in the stem's Voronoi face at
distance `sqrt 2`. -/
theorem MXI_IN_VORONOI_LIST {V : Set V3} {vl : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 vl) (h1 : Real.sqrt 2 ≤ hl vl)
    (h2 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    mxi V vl ∈ voronoiList V (truncateSimplex 2 vl) ∧
      dist (vl.getD 0 0) (mxi V vl) = Real.sqrt 2 := by
  have ho2 : omegaListN V vl 2 ∈ voronoiList V (truncateSimplex 2 vl) :=
    OMEGA_LIST_N_IN_VORONOI_LIST_GEN V vl 3 2 2 hp hs hb (le_refl 2) (by omega)
  have ho3 : omegaListN V vl 3 ∈ voronoiList V (truncateSimplex 2 vl) :=
    OMEGA_LIST_N_IN_VORONOI_LIST_GEN V vl 3 2 3 hp hs hb (by omega) (by omega)
  have hconv := CONVEX_VORONOI_LIST V (truncateSimplex 2 vl)
  have hsub2 : convexHull ℝ ({omegaListN V vl 2, omegaListN V vl 3} : Set V3) ⊆
      voronoiList V (truncateSimplex 2 vl) := by
    refine convexHull_min ?_ hconv
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact ho2
    · exact ho3
  obtain ⟨s, hseg, hdist, hmxi⟩ :=
    MXI_EXPLICIT V vl (vl.getD 0 0) (vl.getD 1 0) (vl.getD 2 0) (vl.getD 3 0) hs hp hb
      (list4_eq vl hb.1) h2 h1
  have hseg' : mxi V vl ∈ segment ℝ (omegaListN V vl 2) (omegaListN V vl 3) := by
    rw [← hmxi]; exact hseg
  have hdist' : dist (vl.getD 0 0) (mxi V vl) = Real.sqrt 2 := by
    rw [show vl.getD 0 0 = hdV vl from by cases vl <;> simp [hdV], ← hmxi]
    exact hdist
  exact ⟨hsub2 (by rw [convexHull_pair]; exact hseg'), hdist'⟩

/-- HOL `VORONOI_LIST_EQ` (leaf_cell.hl:1666-1687): every point of a Voronoi
list cell is equidistant from the list points (the pairwise `voronoi_closed`
inequalities close up to equalities). -/
theorem VORONOI_LIST_EQ {V : Set V3} {ul : List V3} {p : V3} {k : ℕ}
    (hp : p ∈ voronoiList V ul) (hb : barV V k ul) :
    ∃ r : ℝ, ∀ q ∈ setOfList ul, dist p q = r := by
  rw [voronoiList, voronoiSet, Set.mem_sInter] at hp
  have hle : ∀ v ∈ setOfList ul, ∀ w ∈ V, dist p v ≤ dist p w := by
    intro v hv
    have hv2 : voronoiClosed V v ∈ {voronoiClosed V v | v ∈ setOfList ul} :=
      ⟨v, hv, rfl⟩
    exact (hp _ hv2)
  refine ⟨dist p (hdV ul), fun q hq => ?_⟩
  have hh : 1 ≤ ul.length := by
    have := hb.1
    omega
  have hsub : setOfList ul ⊆ V := BARV_SUBSET V k ul hb
  have h1 : dist p q ≤ dist p (hdV ul) := hle q hq (hdV ul) (hsub (HD_IN_SET_OF_LIST ul hh))
  have h2 : dist p (hdV ul) ≤ dist p q := hle (hdV ul) (HD_IN_SET_OF_LIST ul hh) q (hsub hq)
  exact le_antisymm h1 h2

/-- HOL `NOT_COL_IMP_RADV` (leaf_cell.hl:1688-1869): immediate from
`OAPVION2_concl` via the `pa18_ncol3_affDep` bridge. -/
theorem NOT_COL_IMP_RADV (va vb vc : V3) (h : ¬Collinear3 va vb vc) :
    ∀ w ∈ ({va, vb, vc} : Set V3),
      radV ({va, vb, vc} : Set V3) = dist (circumcenter ({va, vb, vc} : Set V3)) w :=
  OAPVION2_concl ({va, vb, vc} : Set V3) (pa18_ncol3_affDep h)

/-- HOL `MCELL3_NONPLANAR` (leaf_cell.hl:1698-1794): the `mcell3` hull
contains a non-collinear stem triple plus `mxi`, which provably stays off
the stem's affine span (else it would be the stem circumcenter at radius
`sqrt 2 > hl`); coplanarity would force `affDim` past 2. -/
theorem MCELL3_NONPLANAR {V : Set V3} {vl : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 vl) (h1 : Real.sqrt 2 ≤ hl vl)
    (h2 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    ¬Coplanar (mcell3 V vl) := by
  have e0 : truncateSimplex 2 vl = [vl.getD 0 0, vl.getD 1 0, vl.getD 2 0] :=
    BARV3_TRUNC2 hb
  have hb2 : barV V 2 (truncateSimplex 2 vl) := TRUNCATE_SIMPLEX_BARV V 2 3 vl hb (by omega)
  have hleaf : leaf V (truncateSimplex 2 vl) := ⟨hb2, h2⟩
  have hT : setOfList (truncateSimplex 2 vl)
      = ({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) := by
    rw [e0]
    ext t
    simp [setOfList]
  have hncol : ¬Collinear3 (vl.getD 0 0) (vl.getD 1 0) (vl.getD 2 0) := by
    rw [show vl.getD 0 0 = (truncateSimplex 2 vl)[0]! from by rw [e0]; simp,
      show vl.getD 1 0 = (truncateSimplex 2 vl)[1]! from by rw [e0]; simp,
      show vl.getD 2 0 = (truncateSimplex 2 vl)[2]! from by rw [e0]; simp]
    exact GBEWYFX hp hs hleaf
  have hmxi := MXI_IN_VORONOI_LIST hp hs hb h1 h2
  -- mxi is NOT in the stem's affine span (else it is the circumcenter at radius sqrt 2)
  have hnotin : mxi V vl ∉ (affineSpan ℝ (setOfList (truncateSimplex 2 vl)) : Set V3) := by
    intro hmem
    obtain ⟨r, hr⟩ := VORONOI_LIST_EQ hmxi.1 hb2
    have hd0 : dist (mxi V vl) (vl.getD 0 0) = Real.sqrt 2 := by
      rw [dist_comm]; exact hmxi.2
    have hr0 : dist (mxi V vl) (vl.getD 0 0) = r := hr _ (by rw [hT]; simp)
    have heqall : ∃ c : ℝ, ∀ w ∈ setOfList (truncateSimplex 2 vl), dist (mxi V vl) w = c :=
      ⟨Real.sqrt 2, fun w hw => by rw [hr w hw, ← hr0, hd0]⟩
    have hcirc : mxi V vl = circumcenter (setOfList (truncateSimplex 2 vl)) :=
      OAPVION3 (setOfList (truncateSimplex 2 vl)) (by rw [hT]; exact pa18_ncol3_affDep hncol)
        (mxi V vl) hmem heqall
    have hhlbad : hl (truncateSimplex 2 vl) = Real.sqrt 2 := by
      show radV (setOfList (truncateSimplex 2 vl)) = Real.sqrt 2
      rw [hT] at hcirc
      rw [hT, NOT_COL_IMP_RADV (vl.getD 0 0) (vl.getD 1 0) (vl.getD 2 0) hncol
        (vl.getD 0 0) (by simp), ← hcirc]
      exact hd0
    rw [hhlbad] at h2
    exact absurd h2 (by norm_num)
  -- coplanarity of the cell contradicts the dimension jump (HOL 1b/1c)
  intro hcFalse
  obtain ⟨u, v, w, hcsub⟩ := hcFalse
  have hm3 : mcell3 V vl = convexHull ℝ (setOfList (truncateSimplex 2 vl) ∪ {mxi V vl}) := by
    rw [mcell3, if_pos ⟨h2, h1⟩]
  have hnotin2 : mxi V vl ∉ (affineSpan ℝ ({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3)) := by
    rw [hT] at hnotin
    exact hnotin
  have hcopU : Coplanar (({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) ∪ {mxi V vl}) := by
    refine ⟨u, v, w, fun q hq => hcsub (by
      rw [hm3]; exact subset_convexHull ℝ _ (by rw [hT]; exact hq))⟩
  have hdimU : affDim (({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) ∪ {mxi V vl}) ≤ 2 :=
    COPLANAR_IMP_AFF_DIM hcopU
  have hUnion : (({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) ∪ {mxi V vl})
      = insert (mxi V vl) ({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) := by
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  have hdimT : affDim ({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) = 2 :=
    NOT_COLLINEAR_AFF_DIM2 (vl.getD 0 0) (vl.getD 1 0) (vl.getD 2 0) hncol
  rw [hUnion, pa18_affDim_insert ({vl.getD 0 0, vl.getD 1 0, vl.getD 2 0} : Set V3) (mxi V vl)
    ⟨vl.getD 0 0, by simp⟩ hnotin2, hdimT] at hdimU
  norm_num at hdimU

/-- HOL `MCELL2_SUBSET_AFF_GE` (leaf_cell.hl:1870-?). -/
theorem MCELL2_SUBSET_AFF_GE (V : Set V3) (ul : List V3) :
    mcell2 V ul ⊆ affGe {hdV ul, hdV ul.tail} {mxi V ul, omegaListN V ul 3} := by
  sorry

/-- HOL `CONDS_IN_CONV2` (leaf_cell.hl:1870-?). -/
theorem CONDS_IN_CONV2 {v w : V3} {t2 t3 : ℝ} (h2 : 0 ≤ t2) (h3 : 0 ≤ t3)
    (hne : ¬(t2 = 0 ∧ t3 = 0)) :
    (t2 / (t2 + t3)) • v + (t3 / (t2 + t3)) • w ∈ convexHull ℝ ({v, w} : Set V3) := by
  have hpos : 0 < t2 + t3 := by
    by_contra hcon
    push_neg at hcon
    exact hne ⟨by linarith, by linarith⟩
  have hsum1 : t2 / (t2 + t3) + t3 / (t2 + t3) = 1 := by field_simp
  rw [convexHull_pair]
  simp only [segment, Set.mem_setOf_eq]
  exact ⟨t2 / (t2 + t3), t3 / (t2 + t3), div_nonneg h2 hpos.le, div_nonneg h3 hpos.le,
    hsum1, rfl⟩

/-- HOL `AFFINE_DEPENDENT_EXPLICIT_4` (leaf_cell.hl:1870-?). -/
theorem AFFINE_DEPENDENT_EXPLICIT_4 (a b c d : V3) (ta tb tc td : ℝ)
    (hind : AffineIndependent ℝ (fun x : ({a, b, c, d} : Set V3) => (x : V3)))
    (hcard : Nat.card ({a, b, c, d} : Set V3) = 4)
    (hsum : ta + tb + tc + td = 0)
    (hlin : ta • a + tb • b + tc • c + td • d = 0) :
    ta = 0 ∧ tb = 0 ∧ tc = 0 ∧ td = 0 := by
  sorry

/-- HOL `CONVEX_PLANE_INTER` (leaf_cell.hl:1870-2053). -/
theorem CONVEX_PLANE_INTER (a b p q : V3) (hab : a ≠ b) (hd : a ≠ p ∧ b ≠ p)
    (hq : q ∈ affGt {a, b} {p}) :
    ∃ c, c ∈ affGt {a, b} {p} ∧
      c ∈ convexHull ℝ ({a, b, p} : Set V3) ∩ convexHull ℝ ({a, b, q} : Set V3) := by
  sorry

/-- HOL `CONVEX_R3_INTER` (leaf_cell.hl:1870-2053). -/
theorem CONVEX_R3_INTER (a b c p q : V3) (hnc : ¬Coplanar ({a, b, c, p} : Set V3))
    (hq : q ∈ affGt {a, b, c} {p}) :
    ∃ d : V3, ¬Coplanar ({a, b, c, d} : Set V3) ∧
      d ∈ convexHull ℝ ({a, b, c, p} : Set V3) ∩ convexHull ℝ ({a, b, c, q} : Set V3) := by
  sorry

/-- HOL `MCELL2_CONVEX` (leaf_cell.hl:2054-2131). -/
theorem MCELL2_CONVEX {V : Set V3} {vl : List V3} (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 vl) : Convex ℝ (mcell2 V vl) := by
  sorry

/-- HOL `MCELL_CONVEX` (leaf_cell.hl:2054-2131). -/
theorem MCELL_CONVEX {V : Set V3} {vl : List V3} {k : ℕ} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 vl) (hk : 2 ≤ k) : Convex ℝ (mcell k V vl) := by
  sorry

/-- HOL `CHI_MSB_AFF_GT_0` (leaf_cell.hl:2132-2177). -/
theorem CHI_MSB_AFF_GT_0 (a b c q q' : V3)
    (hnc : ¬Coplanar ({a, b, c, q} : Set V3))
    (hq : 0 < chiMsb [a, b, c] q) (hq' : 0 < chiMsb [a, b, c] q') :
    q' ∈ affGt {a, b, c} {q} := by
  sorry

/-- HOL `CHI_MSB_POS2` (leaf_cell.hl:2132-2177). -/
theorem CHI_MSB_POS2 (a b c d p : V3) (hd : a ≠ b ∧ b ≠ c)
    (hd' : d ∈ affGt {a, b} {c}) :
    reEqvl (chiMsb [a, b, d] p) (chiMsb [a, b, c] p) := by
  sorry

/-- HOL `MCELL_ARG_REDUCE` (leaf_cell.hl:2132-2177): every Marchal cell is
one of `mcell j`, `j ≤ 4`. -/
theorem MCELL_ARG_REDUCE (V : Set V3) (ul : List V3) (i : ℕ) :
    ∃ j, j ≤ 4 ∧ mcell i V ul = mcell j V ul := by
  match i with
  | 0 => exact ⟨0, by omega, rfl⟩
  | 1 => exact ⟨1, by omega, rfl⟩
  | 2 => exact ⟨2, by omega, rfl⟩
  | 3 => exact ⟨3, by omega, rfl⟩
  | n + 4 => exact ⟨4, by omega, by simp [mcell]⟩

/-- HOL `AJRIPQN_0` (leaf_cell.hl:2132-2177): `MCELL_ARG_REDUCE` brings both
dispatch values into `AJRIPQN`'s `≤ 4` range. -/
theorem AJRIPQN_0 {V : Set V3} {ul vl : List V3} {i j : ℕ} (hp : Packing V)
    (hs : saturated V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hvol : ¬nullSet (mcell i V ul ∩ mcell j V vl)) :
    mcell j V vl = mcell i V ul := by
  obtain ⟨i', hi', hi'e⟩ := MCELL_ARG_REDUCE V ul i
  obtain ⟨j', hj', hj'e⟩ := MCELL_ARG_REDUCE V vl j
  have hmem : ∀ n : ℕ, n ≤ 4 → n ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
    intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hkey := AJRIPQN V ul vl i' j' hs hp hb1 hb2 (hmem i' hi') (hmem j' hj')
    (by rw [← hi'e, ← hj'e]; exact hvol)
  rw [hi'e, hj'e]
  exact hkey.2.symm

/-- HOL `CFFONNL` (leaf_cell.hl:2178-2514). -/
theorem CFFONNL {V : Set V3} {ul : List V3} {X : Set V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (hX : X ∈ mcellSet V)
    (he : {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} ∈ edgeX V X)
    (hA : X ∩ ccA0 ul ≠ ∅) (hne : X ≠ ccCell V ul) :
    X = ccCell V [(ccUh V ul).getD 1 0, (ccUh V ul).getD 0 0, (ccUh V ul).getD 2 0] := by
-- NEEDS (GIANT): leaf_cell.hl:2178-2400ish, mcell dispatch +
-- CHI_MSB_COPLANAR + EDGEX_SUBSET_MCELL kit.
  sorry

/-- HOL `CC_CELL_IN_MCELL_SET` (leaf_cell.hl:2515-2584). -/
theorem CC_CELL_IN_MCELL_SET {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) : ccCell V ul ∈ mcellSet V := by
  rw [ccCell, mcellSet]
  exact ⟨ccKe V ul, ccUh V ul, rfl,
    ((Classical.choose_spec (cc_uh_exists V ul)) hp hs hl').1⟩

/-- HOL `CARD4_ALL_DISTINCT` (leaf_cell.hl:2585-?). -/
theorem CARD4_ALL_DISTINCT {a b c d : V3} (h4 : Nat.card ({a, b, c, d} : Set V3) = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have h3le : ∀ (q r s : V3), Nat.card ({q, r, s} : Set V3) ≤ 3 := by
    intro q r s
    have h1 : ({q, r, s} : Set V3).ncard ≤ ({r, s} : Set V3).ncard + 1 :=
      Set.ncard_insert_le q _
    have h2 : ({r, s} : Set V3).ncard ≤ ({s} : Set V3).ncard + 1 := Set.ncard_insert_le r _
    have h3 : ({s} : Set V3).ncard = 1 := Set.ncard_singleton s
    have he : Nat.card ({q, r, s} : Set V3) = ({q, r, s} : Set V3).ncard := rfl
    omega
  have hdupe : ∀ (p q : V3), p = q → ∀ (r s : V3),
      Nat.card ({p, q, r, s} : Set V3) ≤ 3 := by
    intro p q hpq r s
    have hset : ({p, q, r, s} : Set V3) = {q, r, s} := by
      rw [← hpq]; ext t; simp; all_goals tauto
    have hh := h3le q r s
    rw [← hset] at hh
    exact hh
  refine ⟨fun hcon => absurd (hdupe a b hcon c d) (by omega),
    fun hcon => by
      have hh := hdupe a c hcon b d
      have hperm : ({a, b, c, d} : Set V3) = {a, c, b, d} := by
        ext t; simp; all_goals tauto
      rw [← hperm] at hh
      exact absurd hh (by omega),
    fun hcon => by
      have hh := hdupe a d hcon b c
      have hperm : ({a, b, c, d} : Set V3) = {a, d, b, c} := by
        ext t; simp; all_goals tauto
      rw [← hperm] at hh
      exact absurd hh (by omega),
    fun hcon => by
      have hh := hdupe b c hcon a d
      have hperm : ({a, b, c, d} : Set V3) = {b, c, a, d} := by
        ext t; simp; all_goals tauto
      rw [← hperm] at hh
      exact absurd hh (by omega),
    fun hcon => by
      have hh := hdupe b d hcon a c
      have hperm : ({a, b, c, d} : Set V3) = {b, d, a, c} := by
        ext t; simp; all_goals tauto
      rw [← hperm] at hh
      exact absurd hh (by omega),
    fun hcon => by
      have hh := hdupe c d hcon a b
      have hperm : ({a, b, c, d} : Set V3) = {c, d, a, b} := by
        ext t; simp; all_goals tauto
      rw [← hperm] at hh
      exact absurd hh (by omega)⟩

/-- HOL `LENGTH4_SET2` (leaf_cell.hl:2585-?). -/
theorem LENGTH4_SET2 {a b c d e f : V3} (h4 : Nat.card ({a, b, c, d} : Set V3) = 4)
    (hset : setOfList [a, b, c, d] = setOfList [a, b, e, f]) :
    (e = c ∧ f = d) ∨ (e = d ∧ f = c) := by
  have hset4 : ({a, b, c, d} : Set V3) = setOfList [a, b, c, d] := by
    apply Set.ext (fun t => ?_)
    simp [setOfList]
  have h4abef : Nat.card ({a, b, e, f} : Set V3) = 4 := by
    have hR : ({a, b, e, f} : Set V3) = setOfList [a, b, e, f] := by
      apply Set.ext (fun t => ?_)
      simp [setOfList]
    have hL : Nat.card (setOfList [a, b, e, f])
        = Nat.card (setOfList [a, b, c, d]) := by
      rw [hset]
    rw [hR, hL, ← hset4]
    exact h4
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := CARD4_ALL_DISTINCT h4
  obtain ⟨hab', hae, haf, hbe, hbf, hef⟩ := CARD4_ALL_DISTINCT h4abef
  have hemem : e ∈ ({a, b, c, d} : Set V3) := by
    rw [hset4, hset]
    simp only [setOfList, List.mem_cons]
    exact Or.inr (Or.inr (Or.inl rfl))
  have hfcases : ∀ g : V3, g ∈ ({a, b, c, d} : Set V3) → g ≠ a → g ≠ b →
      g = c ∨ g = d := by
    intro g hg hga hgb
    rcases Set.mem_insert_iff.1 hg with hg1 | hg2
    · exact absurd hg1 hga
    · rcases Set.mem_insert_iff.1 hg2 with hg3 | hg4
      · exact absurd hg3 hgb
      · rcases Set.mem_insert_iff.1 hg4 with hg5 | hg6
        · exact Or.inl hg5
        · exact Or.inr (Set.mem_singleton_iff.1 hg6)
  have he : e = c ∨ e = d := hfcases e hemem hae.symm hbe.symm
  have hfmem : f ∈ ({a, b, c, d} : Set V3) := by
    rw [hset4, hset]
    simp only [setOfList, List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hf : f = c ∨ f = d := hfcases f hfmem haf.symm hbf.symm
  rcases he with hec | hed
  · refine Or.inl ⟨hec, ?_⟩
    rcases hf with hfc | hfd
    · exact absurd (hec.trans hfc.symm) hef
    · exact hfd
  · refine Or.inr ⟨hed, ?_⟩
    rcases hf with hfc | hfd
    · exact hfc
    · exact absurd (hed.trans hfd.symm) hef

/-- HOL `LENGTH4_SET2_SWAP01` (leaf_cell.hl:2585-?). -/
theorem LENGTH4_SET2_SWAP01 {a b c d e f : V3}
    (h4 : Nat.card ({a, b, c, d} : Set V3) = 4)
    (hset : setOfList [a, b, c, d] = setOfList [b, a, e, f]) :
    (e = c ∧ f = d) ∨ (e = d ∧ f = c) := by
  refine LENGTH4_SET2 h4 ?_
  rw [hset]
  apply Set.ext (fun t => ?_)
  simp [setOfList]
  all_goals tauto

/-- HOL `MCELL4_NONPLANAR` (leaf_cell.hl:1608-1629): the `k = 4` cell is the
Delaunay tetrahedron hull, whose vertex set has affine dimension 3
(`MHFTTZN1`), so it cannot be coplanar. -/
private theorem pa18_mcell4_nonplanar {V : Set V3} {vl : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 vl) (hhl : hl vl < Real.sqrt 2) :
    ¬Coplanar (mcell4 V vl) := by
  rw [mcell4, if_pos hhl]
  intro hcop
  obtain ⟨x, hplane, hsub⟩ := coplanar_eq_coplanar_alt.1 hcop
  have hc2 : Coplanar (setOfList vl) :=
    coplanar_eq_coplanar_alt.2 ⟨x, hplane, fun q hq => hsub (subset_convexHull ℝ _ hq)⟩
  have h1 : affDim (setOfList vl) ≤ 2 := COPLANAR_IMP_AFF_DIM hc2
  have h2 := MHFTTZN1 V vl 3 hp hb
  omega

/-- HOL `CC_CELL_NOT_COPLANAR` (leaf_cell.hl:2585-2621): dispatch on
`cc_ke` to `MCELL3_NONPLANAR` / `pa18_mcell4_nonplanar`. -/
theorem CC_CELL_NOT_COPLANAR {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) : ¬Coplanar (ccCell V ul) := by
  have hbar := (Classical.choose_spec (cc_uh_exists V ul)) hp hs hl'
  have hb : barV V 3 (ccUh V ul) := hbar.1
  obtain ⟨e0, e1, e2⟩ := EL_CC_UH hp hs hl'
  have hul3 : ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := list3_eq ul hl'.1.1
  rcases CC_KE_34 V ul with h3 | h4
  · rw [ccCell, h3, (MCELL_EXPLICIT 3 V (ccUh V ul)).2.2.2.1]
    refine MCELL3_NONPLANAR hp hs hb ?_ ?_
    · unfold ccKe at h3
      by_contra hcon
      rw [if_pos (lt_of_not_ge hcon)] at h3
      norm_num at h3
    · rw [BARV3_TRUNC2 hb, e0, e1, e2, ← hul3]
      exact hl'.2
  · rw [ccCell, h4, (MCELL_EXPLICIT 4 V (ccUh V ul)).2.2.2.2 (Nat.le_refl 4)]
    refine pa18_mcell4_nonplanar hp hs hb ?_
    unfold ccKe at h4
    by_contra hcon
    rw [if_neg hcon] at h4
    norm_num at h4

/-- HOL `CC_CELL_NOT_COPLANAR_EXTREME` (leaf_cell.hl:2622-2640). -/
theorem CC_CELL_NOT_COPLANAR_EXTREME {V : Set V3} {ul : List V3} {pp : V3}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    ¬Coplanar ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pp} : Set V3) := by
  intro hcop
  obtain ⟨u2, v2, w2, hcpsub⟩ := hcop
  refine CC_CELL_NOT_COPLANAR hp hs hl' ⟨u2, v2, w2, ?_⟩
  rw [CC_CELL34 (V := V) (ul := ul) (pp := pp) hp hs hl' hpp]
  refine convexHull_min ?_ (AffineSubspace.convex _)
  exact hcpsub

/-- HOL `CC_CELL_NOT_NULLSET` (leaf_cell.hl:2641-2661). -/
theorem CC_CELL_NOT_NULLSET {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) : ¬nullSet (ccCell V ul) := by
-- NEEDS: waits on ZWVCBMN; the rest is CC_CELL34 +
-- CC_CELL_NOT_COPLANAR_EXTREME (both proved).
  sorry

/-- Four pairwise-distinct points give a 4-element set. -/
private theorem pa18_card4_of_distinct {a b c d : V3} (h1 : a ≠ b) (h2 : a ≠ c)
    (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    Nat.card ({a, b, c, d} : Set V3) = 4 := by
  have e1 : ({a, b, c, d} : Set V3).ncard = ({b, c, d} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e2 : ({b, c, d} : Set V3).ncard = ({c, d} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e3 : ({c, d} : Set V3).ncard = ({d} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e4 : ({d} : Set V3).ncard = 1 := Set.ncard_singleton d
  have he : Nat.card ({a, b, c, d} : Set V3) = ({a, b, c, d} : Set V3).ncard := rfl
  omega

private theorem pa18_mem_affspan3 {q x y z : V3} (h : q ∈ ({x, y, z} : Set V3)) :
    q ∈ (affineSpan ℝ ({x, y, z} : Set V3) : Set V3) :=
  mem_affineSpan ℝ h

/-- A 4-point set with fewer than 4 elements is coplanar (any collision
drops it to a triple). -/
private theorem pa18_coplanar4_of_card_ne4 {a b c d : V3}
    (hcard : Nat.card ({a, b, c, d} : Set V3) ≠ 4) :
    Coplanar ({a, b, c, d} : Set V3) := by
  rcases eq_or_ne a b with heq | hab
  · subst heq
    exact ⟨a, c, d, fun q hq => pa18_mem_affspan3 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)⟩
  rcases eq_or_ne a c with heq | hac
  · subst heq
    exact ⟨a, b, d, fun q hq => pa18_mem_affspan3 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)⟩
  rcases eq_or_ne a d with heq | had
  · subst heq
    exact ⟨a, b, c, fun q hq => pa18_mem_affspan3 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)⟩
  rcases eq_or_ne b c with heq | hbc
  · subst heq
    exact ⟨a, b, d, fun q hq => pa18_mem_affspan3 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)⟩
  rcases eq_or_ne b d with heq | hbd
  · subst heq
    exact ⟨a, b, c, fun q hq => pa18_mem_affspan3 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)⟩
  rcases eq_or_ne c d with heq | hcd
  · subst heq
    exact ⟨a, b, c, fun q hq => pa18_mem_affspan3 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)⟩
  exact absurd (pa18_card4_of_distinct hab hac had hbc hbd hcd) hcard

/-- HOL `CC_CELL_EXTREME_CARD` (leaf_cell.hl:2662-2678): the four extreme
points are pairwise distinct because the tetrahedron is non-coplanar. -/
theorem CC_CELL_EXTREME_CARD {V : Set V3} {ul : List V3} {pp : V3}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    Nat.card ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pp} : Set V3)
      = 4 := by
  by_contra hcon
  exact CC_CELL_NOT_COPLANAR_EXTREME hp hs hl' hpp (pa18_coplanar4_of_card_ne4 hcon)

/-- HOL `CC_CELL_INDEPENDENT` (leaf_cell.hl:2679-2708). -/
theorem CC_CELL_INDEPENDENT {V : Set V3} {ul : List V3} {pp : V3}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    AffineIndependent ℝ (fun x : ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, pp} : Set V3) => (x : V3)) := by
  set S : Set V3 := {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pp} with hS
  have hcard := CC_CELL_EXTREME_CARD hp hs hl' hpp
  have hne : S ≠ ∅ := by
    intro hc
    have hmem : (ccUh V ul).getD 0 0 ∈ S := by rw [hS]; simp
    rw [hc] at hmem
    simp at hmem
  have hfin : S.Finite := by
    rw [hS]
    refine Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.finite_singleton pp)))
  haveI : Fintype ↥S := hfin.fintype
  have hcardfi : Fintype.card ↥S = 4 := by
    rwa [Nat.card_eq_fintype_card] at hcard
  have hrange : Set.range (fun x : ↥S => (x : V3)) = S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  rw [affineIndependent_iff_not_finrank_vectorSpan_le ℝ (fun x : ↥S => (x : V3)) (n := 2)
    hcardfi, hrange]
  intro hle
  have hdim : affDim S ≤ 2 := by
    rw [affDim, if_neg hne]
    exact_mod_cast hle
  exact CC_CELL_NOT_COPLANAR_EXTREME hp hs hl' hpp (AFF_DIM_LE_2_IMP_COPLANAR S hdim)

/-- HOL `CC_CELL_CONVEX_HULL_INJ` (leaf_cell.hl:2709-2731). -/
theorem CC_CELL_CONVEX_HULL_INJ {V : Set V3} {ul vl : List V3} {pu pv : V3}
    (hp : Packing V) (hs : saturated V) (hl1 : leaf V ul) (hl2 : leaf V vl)
    (hpu : pu = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0)
    (hpv : pv = if ccKe V vl = 3 then mxi V (ccUh V vl) else (ccUh V vl).getD 3 0)
    (heq : ccCell V ul = ccCell V vl) :
    ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pu} : Set V3)
      = {(ccUh V vl).getD 0 0, (ccUh V vl).getD 1 0, (ccUh V vl).getD 2 0, pv} := by
  have hdep1 := CC_CELL_INDEPENDENT hp hs hl1 hpu
  have hdep2 := CC_CELL_INDEPENDENT hp hs hl2 hpv
  have hul := CC_CELL34 (V := V) (ul := ul) (pp := pu) hp hs hl1 hpu
  have hvl := CC_CELL34 (V := V) (ul := vl) (pp := pv) hp hs hl2 hpv
  have hhull : convexHull ℝ ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, pu} : Set V3)
      = convexHull ℝ ({(ccUh V vl).getD 0 0, (ccUh V vl).getD 1 0,
      (ccUh V vl).getD 2 0, pv} : Set V3) := by
    rw [← hul, ← hvl]; exact heq
  exact (CONVEX_HULL_EQ_EQ_SET_EQ _ _
    (show ¬affineDependent ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, pu} : Set V3) from fun hdep => hdep hdep1)
    (show ¬affineDependent ({(ccUh V vl).getD 0 0, (ccUh V vl).getD 1 0,
      (ccUh V vl).getD 2 0, pv} : Set V3) from fun hdep => hdep hdep2)).1 hhull

/-- HOL `FUEIMOV_K` (leaf_cell.hl:2732-2749). -/
theorem FUEIMOV_K {V : Set V3} {ul vl : List V3} (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V ul) (hl2 : leaf V vl) (heq : ccCell V ul = ccCell V vl) :
    ccKe V ul = ccKe V vl := by
-- NEEDS: waits on CC_CELL_NOT_NULLSET; the other half is PA17.AJRIPQN
-- (still sorry in PackingAuto17, out of PA18 scope).
  sorry

/-- HOL `MCELL4_EXTREME_POINT` (leaf_cell.hl:2793-?). -/
theorem MCELL4_EXTREME_POINT {V : Set V3} {ul vl : List V3} (hs : saturated V)
    (hp : Packing V) (hl1 : leaf V ul) (hl2 : leaf V vl)
    (heq : ccCell V ul = ccCell V vl) (h4 : ccKe V ul = 4) :
    setOfList (ccUh V ul) = setOfList (ccUh V vl) := by
-- NEEDS: leaf_cell.hl:2779-2810; needs the EDGE_FIRST-style rigidity kit
-- plus CC_CELL_CONVEX_HULL_INJ (proved).
  sorry


/-- HOL `STEM_OF_LEAF` (leaf_cell.hl:2793-?). -/
theorem STEM_OF_LEAF {V : Set V3} {ul : List V3} (hl' : leaf V ul) :
    stem ul = {ul.getD 0 0, ul.getD 1 0} := by
  have h3 : ul.length = 3 := hl'.1.1
  rw [stem, list3_eq ul h3]
  have hinit : initialSublist [ul.getD 0 0, ul.getD 1 0]
      [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := ⟨[ul.getD 2 0], rfl⟩
  rw [((TRUNCATE_SIMPLEX_INITIAL_SUBLIST 1 _ _).2 ⟨hinit, by simp⟩).1]
  ext t
  simp [setOfList]
  all_goals tauto

/-- HOL `FUEIMOV_4` (leaf_cell.hl:2793-?). -/
theorem FUEIMOV_4 {V : Set V3} {ul vl : List V3} (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V ul) (hl2 : leaf V vl) (heq : ccCell V ul = ccCell V vl)
    (hst : stem ul = stem vl) (h4 : ccKe V ul = 4) (hne : ul ≠ vl) :
    ccUh V vl = [(ccUh V ul).getD 1 0, (ccUh V ul).getD 0 0, (ccUh V ul).getD 3 0,
      (ccUh V ul).getD 2 0] := by
-- NEEDS (GIANT): leaf_cell.hl:2810-2894 stem-swap rigidity.
  sorry

/-- HOL `MXI_NOT_IN_V` (leaf_cell.hl:2894-2948). -/
theorem MXI_NOT_IN_V {V : Set V3} {ul : List V3} (hs : saturated V) (hp : Packing V)
    (hl' : leaf V ul) (h3 : ccKe V ul = 3) : mxi V (ccUh V ul) ∉ V := by
-- NEEDS: leaf_cell.hl:2894-2948; needs the mxi sqrt-2 distance vs the
-- packing-ball separation kit.
  sorry

/-- HOL `MCELL_V_INTER_EXTREME` (leaf_cell.hl:2949-2976). -/
theorem MCELL_V_INTER_EXTREME {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    V ∩ {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
        mxi V (ccUh V ul)} = setOfList ul := by
-- NEEDS: leaf_cell.hl:2949-2976; waits on MXI_NOT_IN_V.
  sorry

/-- HOL `MCELL_EXTREME_DIFF_V` (leaf_cell.hl:2977-3337). -/
theorem MCELL_EXTREME_DIFF_V {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
        mxi V (ccUh V ul)} : Set V3) \ V = {mxi V (ccUh V ul)} := by
-- NEEDS: leaf_cell.hl:2977-3000; waits on MXI_NOT_IN_V.
  sorry

/-- HOL `FUEIMOV_3` (leaf_cell.hl:2977-3337). -/
theorem FUEIMOV_3 {V : Set V3} {ul vl : List V3} (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V ul) (hl2 : leaf V vl) (h3 : ccKe V ul = 3)
    (hst : ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} : Set V3)
        = {(ccUh V vl).getD 0 0, (ccUh V vl).getD 1 0})
    (heq : ccCell V ul = ccCell V vl) : ul = vl := by
-- NEEDS (GIANT): leaf_cell.hl:3000-3114.
  sorry

/-- HOL `MCELL2_EDGE_FIRST` (leaf_cell.hl:3338-3374). -/
theorem MCELL2_EDGE_FIRST {V : Set V3} {ul : List V3} {u v : V3} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell2 V ul)) :
    ∃ vl, barV V 3 vl ∧ u = vl.getD 0 0 ∧ v = vl.getD 1 0 ∧ mcell2 V ul = mcell2 V vl := by
-- NEEDS (GIANT): leaf_cell.hl:3114-3374 mcell edge-rigidity kit.
  sorry

/-- HOL `FINITE_CARD1_IMP_SINGLETON` (leaf_cell.hl:3338-3374). -/
theorem FINITE_CARD1_IMP_SINGLETON {α : Type*} {S : Set α}
    (h : Nat.card S = 1) : ∃ x, S = {x} := by
  have hfin : S.Finite := by
    by_contra hin
    push_neg at hin
    have hz : (Nat.card S : ℕ) = 0 := @Nat.card_eq_zero_of_infinite _ (infinite_coe_iff.2 hin)
    rw [hz] at h
    exact absurd h (by norm_num)
  exact Set.ncard_eq_one.1 h

/-- HOL `SET2_INSERT1` (leaf_cell.hl:3375-?). -/
theorem SET2_INSERT1 {a b x y z : V3} (hsub : ({a, b} : Set V3) ⊆ {x, y, z})
    (hne : a ≠ b) : ∃ c : V3, ({a, b, c} : Set V3) = {x, y, z} := by
  have hm : ∀ t : V3, t ∈ ({x, y, z} : Set V3) ↔ t = x ∨ t = y ∨ t = z := by
    intro t; simp
  have ha := (hm a).1 (hsub (Set.mem_insert_iff.2 (Or.inl rfl)))
  have hb := (hm b).1 (hsub (Set.mem_insert_iff.2 (Or.inr rfl)))
  rcases ha with rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ⟨z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨y, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
  · rcases hb with rfl | rfl | rfl
    · exact ⟨z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact absurd rfl hne
    · exact ⟨x, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
  · rcases hb with rfl | rfl | rfl
    · exact ⟨y, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨x, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact absurd rfl hne

/-- HOL `MCELL3_EDGE_FIRST` (leaf_cell.hl:3375-?). -/
theorem MCELL3_EDGE_FIRST {V : Set V3} {ul : List V3} {u v : V3} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell3 V ul)) :
    ∃ vl, barV V 3 vl ∧ u = vl.getD 0 0 ∧ v = vl.getD 1 0 ∧ mcell3 V ul = mcell3 V vl := by
-- NEEDS (GIANT): leaf_cell.hl:3197-3281 mcell edge-rigidity kit.
  sorry

/-- HOL `SET2_INSERT2` (leaf_cell.hl:3375-?). -/
theorem SET2_INSERT2 {a b w x y z : V3} (hsub : ({a, b} : Set V3) ⊆ {w, x, y, z})
    (hne : a ≠ b) (h4 : Nat.card ({w, x, y, z} : Set V3) = 4) :
    ∃ c d : V3, ({w, x, y, z} : Set V3) = {a, b, c, d} := by
  have hm : ∀ t : V3, t ∈ ({w, x, y, z} : Set V3) ↔ t = w ∨ t = x ∨ t = y ∨ t = z := by
    intro t; simp
  have ha := (hm a).1 (hsub (Set.mem_insert_iff.2 (Or.inl rfl)))
  have hb := (hm b).1 (hsub (Set.mem_insert_iff.2 (Or.inr rfl)))
  rcases ha with rfl | rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ⟨y, z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨x, z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨x, y, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
  · rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨y, z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact absurd rfl hne
    · exact ⟨w, z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨w, y, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
  · rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨x, z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨w, z, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact absurd rfl hne
    · exact ⟨w, x, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
  · rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨x, y, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨w, y, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact ⟨w, x, by ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; all_goals tauto⟩
    · exact absurd rfl hne

/-- HOL `MCELL4_EDGE_FIRST` (leaf_cell.hl:3375-?). -/
theorem MCELL4_EDGE_FIRST {V : Set V3} {ul : List V3} {u v : V3} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell4 V ul)) :
    ∃ vl, barV V 3 vl ∧ u = vl.getD 0 0 ∧ v = vl.getD 1 0 ∧ mcell4 V ul = mcell4 V vl := by
-- NEEDS (GIANT): leaf_cell.hl:3281-3374 mcell edge-rigidity kit.
  sorry

/-- HOL `STEM_EDGEX` (leaf_cell.hl:3375-?). -/
theorem STEM_EDGEX {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V ul) :
    {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} ∈ edgeX V (ccCell V ul) := by
-- NEEDS: leaf_cell.hl:3375-3432; stem edge in edgeX of cc_cell, waits on
-- the EDGE_FIRST kit.
  sorry

/-- HOL `FCHKUGT` (leaf_cell.hl:3432-3528). -/
theorem FCHKUGT {V : Set V3} {u0 u1 u2 u2' : V3} (hs : saturated V) (hp : Packing V)
    (hA : ccA0 [u0, u1, u2] = ccA0 [u0, u1, u2'])
    (hl1 : leaf V [u0, u1, u2]) (hl2 : leaf V [u0, u1, u2']) : u2 = u2' := by
-- NEEDS (GIANT): leaf_cell.hl:3432-3528 cc_A0 injectivity.
  sorry

/-- HOL `AZIM_BASE_SHIFT_LE` (leaf_cell.hl:3529-3547), via two applications of
fan.hl:1698 `sum4_azim_fan` (the three-point azimuth addition) and linear
arithmetic. -/
theorem AZIM_BASE_SHIFT_LE (x y b1 b2 w1 w2 : V3)
    (h1 : ¬Collinear3 x y b1) (h2 : ¬Collinear3 x y b2) (h3 : ¬Collinear3 x y w1)
    (h4 : ¬Collinear3 x y w2)
    (h5 : azim x y b1 b2 ≤ azim x y b1 w1) (h6 : azim x y b1 b2 ≤ azim x y b1 w2) :
    azim x y b1 w2 - azim x y b1 w1 = azim x y b2 w2 - azim x y b2 w1 := by
  have hyx : y ≠ x := fun he => h1 (collinear3_of_eq he)
  have e1 := sum4_azim_fan hyx h1 h2 h4 h6
  have e2 := sum4_azim_fan hyx h1 h2 h3 h5
  linarith

/-- HOL `WEDGE_GE_SPLIT` (leaf_cell.hl:3548-3611): inserting an interior ray
splits the closed wedge into two closed wedges (`AZIM_BASE_SHIFT_LE`). -/
theorem WEDGE_GE_SPLIT (u0 u1 u2 u3 w : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hw : w ∈ wedge u0 u1 u2 u3) :
    ¬Collinear3 u0 u1 w ∧
      wedgeGe u0 u1 u2 u3 = wedgeGe u0 u1 u2 w ∪ wedgeGe u0 u1 w u3 := by
  rw [wedge, Set.mem_setOf_eq] at hw
  refine ⟨hw.1, ?_⟩
  refine Set.ext (fun x => ?_)
  by_cases hcol : Collinear3 u0 u1 x
  · have hx0 : azim u0 u1 u2 x = 0 := by rw [azim, if_pos (Or.inr hcol)]
    constructor
    · intro hx
      refine Set.mem_union_left _ ?_
      rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
      refine ⟨azim_nonneg u0 u1 u2 x, ?_⟩
      rw [hx0]
      exact le_of_lt hw.2.1
    · intro hx
      rw [Set.mem_union] at hx
      rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
      rcases hx with hx | hx
      · rw [hx0]
        exact ⟨le_refl 0, azim_nonneg u0 u1 u2 u3⟩
      · rw [hx0]
        exact ⟨le_refl 0, azim_nonneg u0 u1 u2 u3⟩
  · rcases le_or_gt (azim u0 u1 u2 x) (azim u0 u1 u2 w) with hle | hgt
    · constructor
      · intro hx
        refine Set.mem_union_left _ ?_
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        exact ⟨azim_nonneg u0 u1 u2 x, hle⟩
      · intro hx
        rw [Set.mem_union] at hx
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨hx.1, le_trans hx.2 (le_of_lt hw.right.right)⟩
        · exact ⟨azim_nonneg u0 u1 u2 x, le_trans hle (le_of_lt hw.right.right)⟩
    · have hshift := AZIM_BASE_SHIFT_LE u0 u1 u2 w x u3 h2 hw.1 hcol h3 (le_of_lt hgt)
        (le_of_lt hw.2.2)
      -- azim u2 u3 - azim u2 x = azim w u3 - azim w x
      constructor
      · intro hx
        refine Set.mem_union_right _ ?_
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        refine ⟨azim_nonneg u0 u1 w x, ?_⟩
        linarith
      · intro hx
        rw [Set.mem_union] at hx
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨hx.1, le_trans hx.2 (le_of_lt hw.right.right)⟩
        · rcases le_or_gt (azim u0 u1 u2 x) (azim u0 u1 u2 w) with hle'' | hgt''
          · exact ⟨azim_nonneg u0 u1 u2 x, le_trans hle'' (le_of_lt hw.2.2)⟩
          · have hshift' := AZIM_BASE_SHIFT_LE u0 u1 u2 w x u3 h2 hw.1 hcol h3
              (le_of_lt hgt'') (le_of_lt hw.2.2)
            rw [wedgeGe, Set.mem_setOf_eq] at hx
            refine ⟨azim_nonneg u0 u1 u2 x, ?_⟩
            linarith


/-- HOL `AFF_GT_0_2` (leaf_cell.hl:3589-3602, proved unconditionally by
`AFF_TAC`).  The earlier "FALSE as ported" verdict in this file's STATUS was a
mistake: HOL `affsign` sums over the *set* `s ∪ t` (so it already dedups at
`v = w`), and the Lean `Affsign` sums over `h.toFinset` with the same set
semantics.  At `v = w` both sides are `{v}` — the LHS forces `f v = 1`, the
RHS collapses `t2 • v + t3 • w` to `(t2 + t3) • v = v` — so the statement is
literally true and is proved outright, faithful to the HOL statement (which
carries no `v ≠ w` hypothesis). -/
theorem AFF_GT_0_2 (v w : V3) :
    conv0 {v, w} = {y | ∃ t2 t3 : ℝ, 0 < t2 ∧ 0 < t3 ∧ t2 + t3 = 1 ∧
      y = t2 • v + t3 • w} := by
  refine Set.ext (fun y => ?_)
  rw [conv0, affGt, Set.mem_setOf_eq, Set.mem_setOf_eq, Affsign]
  constructor
  · rintro ⟨f, hfin, hvec, hpos, hone⟩
    by_cases hvw : v = w
    · subst hvw
      have h1 : hfin.toFinset = ({v} : Finset V3) := by
        ext z
        simp [hfin.mem_toFinset]
      rw [h1, Finset.sum_singleton] at hvec hone
      exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        rw [hvec, hone]; module⟩
    · have h1 : hfin.toFinset = ({v, w} : Finset V3) := by
        ext z
        simp [hfin.mem_toFinset]
      rw [h1, Finset.sum_insert (show v ∉ ({w} : Finset V3) from by simp [hvw]),
        Finset.sum_singleton] at hvec hone
      exact ⟨f v, f w, hpos v (Set.mem_insert v ({w} : Set V3)),
        hpos w (Set.mem_insert_of_mem v (Set.mem_singleton w)), hone, hvec⟩
  · rintro ⟨t2, t3, h2, h3, h4, h5⟩
    have hfin : (∅ ∪ {v, w} : Set V3).Finite :=
      Set.Finite.union Set.finite_empty (Set.Finite.insert v (Set.finite_singleton w))
    by_cases hvw : v = w
    · subst hvw
      have h1 : hfin.toFinset = ({v} : Finset V3) := by
        ext z
        simp [hfin.mem_toFinset]
      refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
      · rw [h1, Finset.sum_singleton, h5]
        show t2 • v + t3 • v = (1 : ℝ) • v
        rw [← add_smul, h4]
      · intro z _
        exact zero_lt_one
      · rw [h1, Finset.sum_singleton]
    · have h1 : hfin.toFinset = ({v, w} : Finset V3) := by
        ext z
        simp [hfin.mem_toFinset]
      refine ⟨fun z => if z = v then t2 else if z = w then t3 else 0, hfin, ?_, ?_, ?_⟩
      · rw [h1, Finset.sum_insert (show v ∉ ({w} : Finset V3) from by simp [hvw]),
          Finset.sum_singleton, h5]
        show t2 • v + t3 • w
            = (if v = v then t2 else if v = w then t3 else 0) • v
              + (if w = v then t2 else if w = w then t3 else 0) • w
        rw [if_pos rfl, if_neg (Ne.symm hvw), if_pos rfl]
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz1 | hz1
        · show 0 < (if z = v then t2 else if z = w then t3 else 0)
          rw [if_pos hz1]
          exact h2
        · show 0 < (if z = v then t2 else if z = w then t3 else 0)
          rw [if_neg (fun hc => hvw (hc.symm.trans hz1)), if_pos hz1]
          exact h3
      · rw [h1, Finset.sum_insert (show v ∉ ({w} : Finset V3) from by simp [hvw]),
          Finset.sum_singleton]
        show (if v = v then t2 else if v = w then t3 else 0)
            + (if w = v then t2 else if w = w then t3 else 0) = 1
        rw [if_pos rfl, if_neg (Ne.symm hvw), if_pos rfl]
        exact h4

/-- HOL `MIDPOINT_IN_CONV0` (leaf_cell.hl:3659-?).  When `p = q` the
`toFinset` in `Affsign` is a singleton, so the witness function is `1`. -/
theorem MIDPOINT_IN_CONV0 (p q : V3) :
    ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) ∈ conv0 {p, q} := by
  have hfin : (∅ ∪ {p, q} : Set V3).Finite :=
    Set.Finite.union Set.finite_empty (Set.Finite.insert p (Set.finite_singleton q))
  by_cases hpq : p = q
  · subst hpq
    rw [conv0, affGt, Set.mem_setOf_eq, Affsign]
    have h1 : hfin.toFinset = ({p} : Finset V3) := by
      ext w
      simp [hfin.mem_toFinset]
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [h1, ← add_smul]
      norm_num
    · intro w hw
      have hw2 : w ∈ (∅ ∪ {p, p} : Set V3) := Set.mem_union_right _ hw
      have hw' := hfin.mem_toFinset.2 hw2
      rw [h1] at hw'
      simp at hw'
      simp [hw']
    · rw [h1]
      simp
  · rw [conv0, affGt, Set.mem_setOf_eq, Affsign]
    have h1f : hfin.toFinset = ({p, q} : Finset V3) := by
      ext w
      simp [hfin.mem_toFinset]
    have h1m : ∀ w : V3, w ∈ hfin.toFinset ↔ (w = p ∨ w = q) := by
      intro w
      rw [hfin.mem_toFinset]
      simp
    refine ⟨fun _ => 1 / 2, hfin, ?_, ?_, ?_⟩
    · rw [h1f]
      simp [hpq, add_comm]
    · intro w hw
      have hw2 : w ∈ (∅ ∪ {p, q} : Set V3) := Set.mem_union_right _ hw
      have hw' := hfin.mem_toFinset.2 hw2
      rw [h1m] at hw'
      rcases hw' with rfl | hw'
      · norm_num
      · norm_num
    · rw [h1f, Finset.sum_insert (by simp [hpq]), Finset.sum_singleton]
      norm_num
/-- HOL `IN_CONV0_IMP_AZIM_PI_ALT` (leaf_cell.hl:3612-?).  NEEDS: x ∈ conv0 {a,b}
puts x strictly between a and b (x = t2•a + t3•b, t2,t3 > 0, t2+t3 = 1), so
b - x = -(t2/t3) • (a - x); read the azimuth frame via `azim_frame_spec`
(Geom/AzimLemmas) for the pair (a, b), compare the opposite projections
(zOf f1 f2 (b - x) = -(t2/t3) • zOf f1 f2 (a - x), norms give r2 = (t2/t3)*r1),
then `angle_eq_of_exp_eq` yields azim x e a b = π.  (A full frame proof was
drafted here but not finished this wave.) -/
theorem IN_CONV0_IMP_AZIM_PI_ALT (x e a b : V3) (h : ¬Collinear3 x e a)
    (hx : x ∈ conv0 {a, b}) : azim x e a b = Real.pi := by
  sorry

/-- HOL `AZIM_SPLIT_POINT` (leaf_cell.hl:3612-?).  NEEDS: take w := 2•u0 - u2
(the reflection of u2 through u0); then u0 ∈ conv0 {u2, w} (midpoint), so
IN_CONV0_IMP_AZIM_PI_ALT gives azim u0 u1 u2 w = π; wedge membership is
hw-free; and sum4_azim_fan + azim_lt_two_pi give azim u0 u1 w u3 < π.
(Blocks on IN_CONV0_IMP_AZIM_PI_ALT above.) -/
theorem AZIM_SPLIT_POINT (u0 u1 u2 u3 : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hpi : Real.pi < azim u0 u1 u2 u3) :
    ∃ w, w ∈ wedge u0 u1 u2 u3 ∧ azim u0 u1 u2 w = Real.pi ∧
      azim u0 u1 w u3 < Real.pi := by
  sorry

/-- HOL `CLOSED_WEDGE_LT_PI` (leaf_cell.hl:3659-?). -/
theorem CLOSED_WEDGE_LT_PI (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) (hpi : azim u0 u1 u2 u3 < Real.pi) :
    IsClosed (wedgeGe u0 u1 u2 u3) := by
  sorry

/-- HOL `CLOSED_WEDGE_EQ_PI` (leaf_cell.hl:3659-?). -/
theorem CLOSED_WEDGE_EQ_PI (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) (hpi : azim u0 u1 u2 u3 = Real.pi) :
    IsClosed (wedgeGe u0 u1 u2 u3) := by
  sorry

/-- HOL `CLOSED_WEDGE` (leaf_cell.hl:3659-?). -/
theorem CLOSED_WEDGE (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) : IsClosed (wedgeGe u0 u1 u2 u3) := by
  sorry

/-- HOL `WEDGE_INTER_AFF_GE` (leaf_cell.hl:3710-3743): the open wedge is
disjoint from both bounding half-planes of the axis. -/
theorem WEDGE_INTER_AFF_GE (u0 u1 v1 v2 : V3) :
    wedge u0 u1 v1 v2 ∩ affGe {u0, u1} {v1} = ∅ ∧
      wedge u0 u1 v1 v2 ∩ affGe {u0, u1} {v2} = ∅ := by
  constructor
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_inter_iff, wedge, Set.mem_setOf_eq] at hx
    by_cases h1 : Collinear3 u0 u1 v1
    · rw [azim, if_pos (Or.inl h1)] at hx
      norm_num at hx
    · have h0 := (pa18_azim_zero_affGe h1).2 hx.2
      rw [h0] at hx
      norm_num at hx
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_inter_iff, wedge, Set.mem_setOf_eq] at hx
    by_cases hcolx : Collinear3 u0 u1 x
    · rw [azim, if_pos (Or.inr hcolx)] at hx
      norm_num at hx
    · have hv2n : ¬Collinear3 u0 u1 v2 := by
        intro hc
        have h0 : azim u0 u1 v1 v2 = 0 := by
          rw [azim, if_pos (Or.inr hc)]
        linarith [hx.1.2.2, azim_nonneg u0 u1 v1 x]
      have hv1n : ¬Collinear3 u0 u1 v1 := by
        intro hc
        rw [azim, if_pos (Or.inl hc)] at hx
        norm_num at hx
      have hgt : x ∈ affGt ({u0, u1} : Set V3) ({v2} : Set V3) :=
        pa18_affGe_affGt_of_ncol hv2n hcolx hx.2
      have hiff := azim_eq_azim_iff hv1n hv2n hcolx
      rw [hiff.2 hgt] at hx
      norm_num at hx

/-- HOL `AFF_GE_SUBSET_WEDGE_GE` (leaf_cell.hl:3744-3766): each bounding
half-plane lies in the closed wedge. -/
theorem AFF_GE_SUBSET_WEDGE_GE (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) :
    affGe {u0, u1} {v1} ⊆ wedgeGe u0 u1 v1 v2 ∧ affGe {u0, u1} {v2} ⊆ wedgeGe u0 u1 v1 v2 := by
  constructor
  · intro x hx
    have h0 : azim u0 u1 v1 x = 0 := (pa18_azim_zero_affGe h1).2 hx
    rw [wedgeGe, Set.mem_setOf_eq]
    refine ⟨azim_nonneg u0 u1 v1 x, ?_⟩
    rw [h0]
    exact azim_nonneg u0 u1 v1 v2
  · intro x hx
    have h0 : azim u0 u1 v2 x = 0 := (pa18_azim_zero_affGe h2).2 hx
    rw [wedgeGe, Set.mem_setOf_eq]
    refine ⟨azim_nonneg u0 u1 v1 x, ?_⟩
    by_cases hcolx : Collinear3 u0 u1 x
    · rw [azim, if_pos (Or.inr hcolx)]
      exact azim_nonneg u0 u1 v1 v2
    · have hgt : x ∈ affGt ({u0, u1} : Set V3) ({v2} : Set V3) :=
        (azim_eq_zero_iff_alt h2 hcolx).1 h0
      have hiff := azim_eq_azim_iff h1 h2 hcolx
      rw [hiff.2 hgt]

/-- HOL `BDXKHTW_PREP_LEMMA` (leaf_cell.hl:3767-3903). -/
theorem BDXKHTW_PREP_LEMMA {V : Set V3} {X : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
    (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
    (haz : azim u0 u1 v1 v2 ≠ 0)
    (hy : ∃ y, y ∈ X ∩ wedge u0 u1 v1 v2)
    (hx : ∃ x, x ∈ X ∧ x ∉ wedgeGe u0 u1 v1 v2) :
    Convex ℝ X ∧ u0 ≠ u1 ∧ ¬Collinear3 u0 u1 v1 ∧ ¬Collinear3 u0 u1 v2 ∧
      ∃ p q, p ∈ X ∩ wedge u0 u1 v1 v2 ∧ q ∈ X \ wedgeGe u0 u1 v1 v2 ∧
        ¬Coplanar ({p, q, u0, u1} : Set V3) ∧
        p ∉ affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} ∧
        q ∉ affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} := by
  sorry

/-- HOL `WEDGE_SUBSET_WEDGE_GE` (leaf_cell.hl:3904-3912). -/
theorem WEDGE_SUBSET_WEDGE_GE (u0 u1 u2 u3 : V3) :
    wedge u0 u1 u2 u3 ⊆ wedgeGe u0 u1 u2 u3 := by
  intro y hy
  exact ⟨le_of_lt hy.2.1, le_of_lt hy.2.2⟩

/-- HOL `AFF_INTER_IMP_COPLANAR` (leaf_cell.hl:3913-3963). -/
theorem AFF_INTER_IMP_COPLANAR (a b c d : V3)
    (h : (affineSpan ℝ {a, b} : Set V3) ∩ (affineSpan ℝ {c, d} : Set V3) ≠ ∅) :
    Coplanar ({a, b, c, d} : Set V3) := by
  sorry

/-- HOL `NOT_COLLINEAR_AFF_DIM2` is proved above; `ADD_NN_ZERO` here. -/
theorem ADD_NN_ZERO (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : a * x + b * y = 0) : x = 0 ∧ y = 0 := by
  have h5 : 0 ≤ a * x := mul_nonneg ha.le hx
  have h6 : 0 ≤ b * y := mul_nonneg hb.le hy
  have hax : a * x = 0 := by linarith
  have hby : b * y = 0 := by linarith
  exact ⟨by
    rcases mul_eq_zero.1 hax with h7 | h7
    · exact absurd h7 ha.ne'
    · exact h7,
    by
      rcases mul_eq_zero.1 hby with h7 | h7
      · exact absurd h7 hb.ne'
      · exact h7⟩

/-- HOL `BDXKHTW` (leaf_cell.hl:3984-4166). -/
theorem BDXKHTW {V : Set V3} {X : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
    (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
    (haz : azim u0 u1 v1 v2 ≠ 0)
    (hy : ∃ y, y ∈ X ∩ wedge u0 u1 v1 v2) :
    X ⊆ wedgeGe u0 u1 v1 v2 := by
  sorry

/-- HOL `AZIM_POS_IMP_SUM_2PI_ALT` (leaf_cell.hl:4167-?), from the Geom
complement formula `azim_compl` (`azim z w w2 w1 = 2π - azim z w w1 w2` off
the degenerate zero). -/
theorem AZIM_POS_IMP_SUM_2PI_ALT (a b c d : V3) (h : 0 < azim a b c d) :
    azim a b c d + azim a b d c = 2 * Real.pi := by
  have hnc : ¬(Collinear3 a b c ∨ Collinear3 a b d) := by
    intro hc
    rw [azim, if_pos hc] at h
    norm_num at h
  have hnc1 : ¬ Collinear3 a b c := fun hc => hnc (Or.inl hc)
  have hnc2 : ¬ Collinear3 a b d := fun hc => hnc (Or.inr hc)
  rw [azim_compl hnc1 hnc2, if_neg (ne_of_gt h)]
  ring

/-- HOL `WEDGE_GE_COMPLEMENT` (leaf_cell.hl:4167-4201). -/
theorem WEDGE_GE_COMPLEMENT (u0 u1 v1 v2 : V3) (h : azim u0 u1 v1 v2 ≠ 0) :
    (Set.univ : Set V3) \ wedgeGe u0 u1 v1 v2 = wedge u0 u1 v2 v1 := by
  sorry

/-- HOL `WEDGE_COMPLEMENT` (leaf_cell.hl:4202-4215). -/
theorem WEDGE_COMPLEMENT (u0 u1 v1 v2 : V3) (h : azim u0 u1 v1 v2 ≠ 0) :
    (Set.univ : Set V3) \ wedge u0 u1 v1 v2 = wedgeGe u0 u1 v2 v1 := by
  sorry

/-- HOL `EWYBJUA` (leaf_cell.hl:4216-4306): two cells sharing a leaf stem lie
on azimuthal sides of the stem. -/
theorem EWYBJUA {V : Set V3} {X : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
    (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
    (haz : azim u0 u1 v1 v2 ≠ 0) :
    X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1 := by
  sorry


/-! ### setSum arithmetic kit (p16-shape copies; PA16's are private) -/

private theorem p18_setSum_union {α : Type*} {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (hdisj : Disjoint s t) (f : α → ℝ) : setSum (s ∪ t) f = setSum s f + setSum t f := by
  unfold setSum
  rw [dif_pos (hs.union ht), dif_pos hs, dif_pos ht, Set.Finite.toFinset_union hs ht]
  exact Finset.sum_union (Finset.disjoint_left.mpr fun a ha hb =>
    Set.disjoint_left.mp hdisj ((Set.Finite.mem_toFinset hs).mp ha)
      ((Set.Finite.mem_toFinset ht).mp hb))

private theorem p18_setSum_add {α : Type*} {s : Set α} (hs : s.Finite) (f g : α → ℝ) :
    setSum s f + setSum s g = setSum s (fun x => f x + g x) := by
  unfold setSum
  rw [dif_pos hs, dif_pos hs, dif_pos hs]
  rw [Finset.sum_add_distrib]

private theorem p18_setSum_lmul {α : Type*} {s : Set α} (hs : s.Finite) (a : ℝ) (f : α → ℝ) :
    setSum s (fun x => a * f x) = a * setSum s f := by
  unfold setSum
  rw [dif_pos hs, dif_pos hs]
  rw [Finset.mul_sum]

private theorem p18_setSum_eq_zero {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ)
    (h : ∀ a ∈ s, f a = 0) : setSum s f = 0 := by
  unfold setSum
  rw [dif_pos hs, Finset.sum_eq_zero fun a ha => h a ((Set.Finite.mem_toFinset hs).mp ha)]

private theorem p18_setSum_le_of_subset {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (hsub : s ⊆ t) (f : α → ℝ)
    (hnn : ∀ a ∈ t, 0 ≤ f a) : setSum s f ≤ setSum t f := by
  unfold setSum
  rw [dif_pos hs, dif_pos ht]
  have hss : hs.toFinset ⊆ ht.toFinset := fun a ha =>
    (Set.Finite.mem_toFinset ht).mpr (hsub ((Set.Finite.mem_toFinset hs).mp ha))
  have hsplit : ∑ x ∈ ht.toFinset \ hs.toFinset, f x + ∑ x ∈ hs.toFinset, f x
      = ∑ x ∈ ht.toFinset, f x := Finset.sum_sdiff hss
  have hdiffnn : 0 ≤ ∑ x ∈ ht.toFinset \ hs.toFinset, f x :=
    Finset.sum_nonneg fun x hx => hnn x
      ((Set.Finite.mem_toFinset ht).mp (Finset.mem_sdiff.mp hx).1)
  linarith [hsplit, hdiffnn]

private theorem p18_setSum_const {α : Type*} {s : Set α} (hs : s.Finite) (c : ℝ) :
    setSum s (fun _ => c) = (Nat.card s : ℝ) * c := by
  unfold setSum
  rw [dif_pos hs, Finset.sum_const, nsmul_eq_mul]
  simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

private theorem p18_setSum_fubini {α β : Type*} {B : Set α} {A : Set β}
    (hB : B.Finite) (hA : A.Finite) (f : α → β → ℝ) :
    setSum B (fun X => setSum A (fun u => f X u))
      = setSum A (fun u => setSum B (fun X => f X u)) := by
  simp only [setSum, dif_pos hB, dif_pos hA]
  exact Finset.sum_comm

private theorem p18_setSum_superset_eq {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (hsub : s ⊆ t) (f : α → ℝ)
    (hz : ∀ a ∈ t, a ∉ s → f a = 0) : setSum s f = setSum t f := by
  have hsd : ht.toFinset \ hs.toFinset ⊆ ht.toFinset := fun a ha =>
    (Finset.mem_sdiff.mp ha).1
  have hsplit : ∑ x ∈ ht.toFinset \ hs.toFinset, f x + ∑ x ∈ hs.toFinset, f x
      = ∑ x ∈ ht.toFinset, f x := Finset.sum_sdiff
      (fun a ha => (Set.Finite.mem_toFinset ht).mpr
        (hsub ((Set.Finite.mem_toFinset hs).mp ha)))
  have hzero : ∑ x ∈ ht.toFinset \ hs.toFinset, f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have h1 : x ∈ t := (Set.Finite.mem_toFinset ht).mp (Finset.mem_sdiff.mp hx).1
    have h2 : x ∉ s := by
      intro hcon
      exact (Finset.mem_sdiff.mp hx).2 ((Set.Finite.mem_toFinset hs).mpr hcon)
    rw [hz x h1 h2]
  unfold setSum
  rw [dif_pos hs, dif_pos ht, ← hsplit, hzero]
  linarith

private theorem p18_setSum_filter {α : Type*} {A : Set α} (hA : A.Finite)
    (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    setSum {u | u ∈ A ∧ P u} f = setSum A (fun u => if P u then f u else 0) := by
  have hfin : ({u | u ∈ A ∧ P u} : Set α).Finite := hA.subset fun u hu => hu.1
  unfold setSum
  rw [dif_pos hfin, dif_pos hA]
  have heq : hfin.toFinset = hA.toFinset.filter P := by
    ext u
    simp [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter,
      Set.Finite.mem_toFinset]
  rw [heq, Finset.sum_filter]

/-! ### ordered/unordered pair halving (marchal3 `SUM_PAIR_2_SET`, closed here) -/

private theorem p18_sum_pair_2_set (f : Set V3 → ℝ) (s : Set V3) (d : ℝ) (hs : s.Finite) :
    setSum {p : V3 × V3 | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ d}
        (fun p => f {p.1, p.2}) =
      2 * setSum {e : Set V3 | ∃ m ∈ s, ∃ n ∈ s, m ≠ n ∧ dist m n ≤ d ∧ e = {m, n}} f := by
  classical
  set O : Set (V3 × V3) := {p : V3 × V3 | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ d}
    with hOdef
  set E : Set (Set V3) := {e : Set V3 | ∃ m ∈ s, ∃ n ∈ s, m ≠ n ∧ dist m n ≤ d ∧ e = {m, n}}
    with hEdef
  have hOsub : O ⊆ s ×ˢ s := fun p hp => ⟨hp.1, hp.2.1⟩
  have hOfin : O.Finite := (hs.prod hs).subset hOsub
  have hEeq : E = (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' O := by
    ext e
    simp only [hEdef, hOdef, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨m, hm, n, hn, hne, hdle, rfl⟩
      exact ⟨(m, n), ⟨hm, hn, hne, hdle⟩, rfl⟩
    · rintro ⟨p, ⟨hm, hn, hne, hdle⟩, rfl⟩
      exact ⟨p.1, hm, p.2, hn, hne, hdle, rfl⟩
  have hEfin : E.Finite := by rw [hEeq]; exact hOfin.image _
  have hEtf : hEfin.toFinset = hOfin.toFinset.image (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) := by
    ext e
    rw [Set.Finite.mem_toFinset hEfin, hEeq, Set.mem_image, Finset.mem_image]
    simp only [← Set.Finite.mem_toFinset hOfin]
  have hfib : setSum O (fun p => f ({p.1, p.2} : Set V3))
      = ∑ e ∈ hEfin.toFinset,
        ∑ p ∈ hOfin.toFinset.filter
          (fun p => ({p.1, p.2} : Set V3) = e), f ({p.1, p.2} : Set V3) := by
    have himg : ∀ p ∈ O, ({p.1, p.2} : Set V3) ∈ E := fun p hp => by
      rw [hEeq]; exact ⟨p, hp, rfl⟩
    rw [setSum, dif_pos hOfin, hEtf]
    exact (Finset.sum_fiberwise_of_maps_to
      (t := hOfin.toFinset.image (fun p : V3 × V3 => ({p.1, p.2} : Set V3)))
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun p => f ({p.1, p.2} : Set V3))).symm
  have hinner : ∀ e ∈ E,
      ∑ p ∈ hOfin.toFinset.filter (fun p => ({p.1, p.2} : Set V3) = e),
        f ({p.1, p.2} : Set V3) = 2 * f e := by
    intro e he
    have him : e ∈ (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' O := by
      rw [← hEeq]; exact he
    rw [Set.mem_image] at him
    obtain ⟨p0, hp0, rfl⟩ := him
    obtain ⟨hm, hn, hne, hdle⟩ := hp0
    have hmO1 : (p0.1, p0.2) ∈ O := ⟨hm, hn, hne, hdle⟩
    have hmO2 : (p0.2, p0.1) ∈ O :=
      ⟨hn, hm, fun h => hne h.symm, by rw [dist_comm]; exact hdle⟩
    have hcomm : ({p0.2, p0.1} : Set V3) = ({p0.1, p0.2} : Set V3) := by
      ext x
      simp
      tauto
    have hsub : hOfin.toFinset.filter
        (fun p => ({p.1, p.2} : Set V3) = ({p0.1, p0.2} : Set V3)) ⊆
        insert (p0.1, p0.2) ({(p0.2, p0.1)} : Finset (V3 × V3)) := by
      intro p hp
      have hpm : p ∈ O :=
        (Set.Finite.mem_toFinset hOfin).mp (Finset.mem_filter.mp hp).1
      have hpe : ({p.1, p.2} : Set V3) = ({p0.1, p0.2} : Set V3) :=
        (Finset.mem_filter.mp hp).2
      have hmemb2 : p.2 ∈ ({p0.1, p0.2} : Set V3) := by rw [← hpe]; simp
      have hmemb1 : p.1 ∈ ({p0.1, p0.2} : Set V3) := by rw [← hpe]; simp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemb1 hmemb2
      rcases hmemb2 with h21 | h22
      · rcases hmemb1 with h11 | h12
        · exact absurd (h11.trans h21.symm) hpm.2.2.1
        · exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (Prod.ext h12 h21)))
      · exact Finset.mem_insert.mpr (Or.inl (Prod.ext (by
          rcases hmemb1 with h11 | h12
          · exact h11
          · exact absurd (h12.trans h22.symm) hpm.2.2.1) h22))
    have hsup : insert (p0.1, p0.2) ({(p0.2, p0.1)} : Finset (V3 × V3)) ⊆
        hOfin.toFinset.filter
          (fun p => ({p.1, p.2} : Set V3) = ({p0.1, p0.2} : Set V3)) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with hp1 | hp2
      · subst hp1
        exact Finset.mem_filter.mpr
          ⟨(Set.Finite.mem_toFinset hOfin).mpr hmO1, rfl⟩
      · rw [Finset.mem_singleton] at hp2
        subst hp2
        exact Finset.mem_filter.mpr
          ⟨(Set.Finite.mem_toFinset hOfin).mpr hmO2, hcomm⟩
    have hne' : ((p0.1, p0.2) : V3 × V3) ∉ ({(p0.2, p0.1)} : Finset (V3 × V3)) := by
      intro hcon
      exact hne ((Prod.mk.injEq _ _ _ _).mp (Finset.mem_singleton.mp hcon)).1
    have heqf : hOfin.toFinset.filter
        (fun p => ({p.1, p.2} : Set V3) = ({p0.1, p0.2} : Set V3)) =
        insert (p0.1, p0.2) ({(p0.2, p0.1)} : Finset (V3 × V3)) :=
      Finset.ext fun p => ⟨fun hp => hsub hp, fun hp => hsup hp⟩
    rw [heqf, Finset.sum_insert hne', Finset.sum_singleton, hcomm]
    ring
  rw [hfib]
  have hstep : ∀ e ∈ hEfin.toFinset,
      ∑ p ∈ hOfin.toFinset.filter (fun p => ({p.1, p.2} : Set V3) = e),
        f ({p.1, p.2} : Set V3) = 2 * f e := fun e he =>
    hinner e ((Set.Finite.mem_toFinset hEfin).mp he)
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  rw [setSum, dif_pos hEfin]

/-! ### betaBump transfer (PA4 `betaBump` = PA2 `betaBumpV1`, same body) -/

private theorem p18_betaBump_eq (V : Set V3) (e X : Set V3) :
    betaBumpV1 V e X = betaBump V e X := rfl


/-! ## sum_gamma.hl: the UPFZBZM support estimate

The supporting kit below closes `BOUND_GAMMA_X_lmfun` (PA15:2086 is still
`sorry` there; this lane may only write PA18, so the proof lives here as the
private `p18_BOUND_GAMMA_X_lmfun` with the PA15 statement shape). Route
(marchal3.hl:6671): split `gammaX` into the volume term (≤ `4/3·π·8³` by
`MCELL_SUBSET_BALL8_2` + `MEASURABLE_MCELL` + ball volume), the `total_solid`
term (`≥ 0`: `sol` is unconditionally nonnegative and `mm1 ≥ 0` via
`sol0 ∈ [π/6, π/5)` ⇒ `tau0 > 0`), and the edge term (the pattern-lambda
`p18_gammaE` bound `≤ π·(h0/(h0-1))` per edge — PA15's `gamma_y_lmfun_bound2`
with the `Classical.epsilon` pair inlined, avoiding the private `pairOf` —
times `CARD_EDGEX_LE_16`, closed here from `Nat.card (VX V X) ≤ 4` via the
`truncateSimplex` length `≤ 4`). The certified `sol0`/`tau0`/`mm2` numerics are
p16-shape copies (PA16's are private); `mm1 ≥ 0` needs only `0 ≤ sol0` and
`tau0 > 0`.

Also closed here (2026-09-30, SUM_GAMMAX wave 1): the marchal3
`SUM_PAIR_2_SET` halving lemma (PA15:1916 is `sorry` there) as the private
`p18_sum_pair_2_set` (fiber = the two orderings of the pair), plus the
setSum arithmetic kit, `betaBumpV1 = betaBump` (PA4) transfer, per-edge
critical-family counting (`p18_crit_family_card`, bound `c2n`) and the
translated-finiteness / endpoint bridges. Continuation map for the
`SUM_GAMMAX_LMFUN_ESTIMATE` assembly: /tmp/sum_gammax_handoff.md
(draft skeleton /tmp/chunk4.lean).

NEEDS (SUM_GAMMAX upstream, not closable from PA18 alone; consumed banked):
-- PA15 `CARD_MCELL_CONTAINS_POINT_klemma` (:2009), `BOUNDS_VGEN_klemma`
-- (:1997), `PACKING_BALL_BOUNDARY` (:495), `FINITE_MCELL_SET_LEMMA_2`
-- (:1148); PA10 `HDTFNFZ` (:246) and `MEASURABLE_MCELL` (:517, via
-- `measurableSet_affGe_wedge_p10` :509) — the two sorried leaves inside
-- `MCELL_SUBSET_BALL8_2`/`MEASURABLE_MCELL` consumed by cc1's kit. -/

private theorem p18_sol0_nonneg : 0 ≤ sol0 := by
  have h1 : (1 / 3 : ℝ) ≤ 1 / 2 := by norm_num
  have h2 : Real.arccos (1 / 2) ≤ Real.arccos (1 / 3) := Real.arccos_le_arccos h1
  have h3 : Real.arccos (1 / 2) = Real.pi / 3 :=
    Real.arccos_eq_of_eq_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      Real.cos_pi_div_three.symm
  unfold sol0
  linarith

private theorem p18_sol0_lt_pi_div_five : sol0 < Real.pi / 5 := by
  have hcos5 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have hcos2 : Real.cos (2 * Real.pi / 5) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
    have hshape : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
    rw [hshape]; exact Real.cos_two_mul _
  have hsqrt5 : (Real.sqrt 5 : ℝ) < 7 / 3 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hsq : ((1 + Real.sqrt 5) / 4) ^ 2 = (3 + Real.sqrt 5) / 8 := by
    have hs25 : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
      have h25 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      nlinarith [h25]
    rw [div_pow, hs25]
    ring
  have hval : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [hcos2, hcos5, hsq]
    ring
  have hlt : Real.cos (2 * Real.pi / 5) < 1 / 3 := by
    rw [hval]; linarith [hsqrt5]
  have hkey : Real.arccos (1 / 3) < 2 * Real.pi / 5 := by
    calc Real.arccos (1 / 3)
        < Real.arccos (Real.cos (2 * Real.pi / 5)) :=
          Real.arccos_lt_arccos (Real.neg_one_le_cos _) hlt (by norm_num)
      _ = 2 * Real.pi / 5 :=
          Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  unfold sol0
  linarith

private theorem p18_tau0_pos : 0 < tau0 := by
  have h := p18_sol0_lt_pi_div_five
  unfold tau0
  linarith [h, Real.pi_pos]

private theorem p18_mm1_nonneg : 0 ≤ mm1 := by
  unfold mm1
  exact div_nonneg (mul_nonneg p18_sol0_nonneg (Real.sqrt_nonneg 8))
    (le_of_lt p18_tau0_pos)

private theorem p18_mm2_nonneg : 0 ≤ mm2 := by
  have hpos : (0:ℝ) < Real.pi / 9 := by linarith [Real.pi_pos]
  have hlt : Real.pi / 9 < Real.pi := by linarith [Real.pi_pos]
  have hs0 : 0 ≤ Real.sin (Real.pi / 9) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  have htri : Real.sin (Real.pi / 3)
      = 3 * Real.sin (Real.pi / 9) - 4 * Real.sin (Real.pi / 9) ^ 3 := by
    have hshape : Real.pi / 3 = 3 * (Real.pi / 9) := by ring
    rw [hshape, Real.sin_three_mul]
  have hval : Real.sqrt 3 / 2
      = 3 * Real.sin (Real.pi / 9) - 4 * Real.sin (Real.pi / 9) ^ 3 := by
    rw [← Real.sin_pi_div_three]; exact htri
  have hsq3 : (23:ℝ) / 27 < Real.sqrt 3 / 2 := by
    have h46sq : ((46:ℝ) / 27) ^ 2 < 3 := by norm_num
    have h46 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ ((46:ℝ) / 27) ^ 2) h46sq
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (46:ℝ) / 27)] at h46
    linarith
  have hge : (1:ℝ) / 3 ≤ Real.sin (Real.pi / 9) := by
    by_contra hcon
    have hf1 : (0:ℝ) < 1 / 3 - Real.sin (Real.pi / 9) := by linarith
    have hsq : Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9) < 1 / 9 := by
      have h1 : Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          ≤ Real.sin (Real.pi / 9) * (1 / 3) :=
        mul_le_mul_of_nonneg_left (le_of_not_ge hcon) hs0
      have h2 : Real.sin (Real.pi / 9) * (1 / 3) < (1 / 3) * (1 / 3) :=
        mul_lt_mul_of_pos_right (lt_of_not_ge hcon) (by norm_num)
      linarith
    have hfac : 23 / 27 - (3 * Real.sin (Real.pi / 9)
          - 4 * Real.sin (Real.pi / 9) ^ 3)
        = (1 / 3 - Real.sin (Real.pi / 9)) *
            (3 - 4 * (Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
              + Real.sin (Real.pi / 9) / 3 + 1 / 9)) := by ring
    have hprod : (0:ℝ) < (1 / 3 - Real.sin (Real.pi / 9)) *
        (3 - 4 * (Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          + Real.sin (Real.pi / 9) / 3 + 1 / 9)) := by
      have h1 : (0:ℝ) < 1 / 3 - Real.sin (Real.pi / 9) := by linarith
      have hT : Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          + Real.sin (Real.pi / 9) / 3 + 1 / 9 < 1 / 3 := by linarith
      have h2 : (0:ℝ) < 3 - 4 * (Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          + Real.sin (Real.pi / 9) / 3 + 1 / 9) := by linarith [hT]
      exact mul_pos h1 h2
    have hlt23 : 3 * Real.sin (Real.pi / 9) - 4 * Real.sin (Real.pi / 9) ^ 3
        < 23 / 27 := by linarith
    linarith [hsq3, hval, hlt23]
  have hshape : 7 * Real.pi / 18 = Real.pi / 2 - Real.pi / 9 := by ring
  have hcos : (1:ℝ) / 3 ≤ Real.cos (7 * Real.pi / 18) := by
    rw [hshape, Real.cos_pi_div_two_sub]
    exact hge
  have hkey : 7 * Real.pi / 18 ≤ Real.arccos (1 / 3) := by
    have h1 := Real.arccos_le_arccos hcos
    rw [Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at h1
    exact h1
  have hkey' : (7:ℝ) * Real.pi / 6 ≤ 3 * Real.arccos (1 / 3) := by
    have h1 : (7:ℝ) * Real.pi / 18 * 3 ≤ Real.arccos (1 / 3) * 3 :=
      mul_le_mul_of_nonneg_right hkey (le_of_lt (by norm_num : (0:ℝ) < 3))
    linarith
  have hsol0 : Real.pi / 6 ≤ sol0 := by
    unfold sol0
    linarith
  have htau : (0:ℝ) < 6 * tau0 := by linarith [p18_tau0_pos]
  unfold mm2
  refine div_nonneg (mul_nonneg ?_ (Real.sqrt_nonneg 2)) (le_of_lt htau)
  linarith

/-! ### setSum micro kit -/

private theorem p18_setSum_nonneg {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ)
    (h : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ setSum s f := by
  unfold setSum
  rw [dif_pos hs]
  exact Finset.sum_nonneg fun a ha =>
    h a ((Set.Finite.mem_toFinset hs).mp ha)

private theorem p18_setSum_le_card_mul {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ)
    (d : ℝ) (h : ∀ a ∈ s, f a ≤ d) :
    setSum s f ≤ (Nat.card s : ℝ) * d := by
  unfold setSum
  rw [dif_pos hs]
  have h1 : ∀ a ∈ hs.toFinset, f a ≤ d := fun a ha =>
    h a ((Set.Finite.mem_toFinset hs).mp ha)
  have h2 := Finset.sum_le_card_nsmul hs.toFinset f d h1
  rw [nsmul_eq_mul] at h2
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]
  exact h2

private theorem p18_setSum_congr {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : setSum s f = setSum s g := by
  unfold setSum
  rw [dif_pos hs, dif_pos hs]
  exact Finset.sum_congr rfl fun a ha =>
    h a ((Set.Finite.mem_toFinset hs).mp ha)

/-! ### sol positivity -/

private theorem p18_sol_nonneg (x : V3) (C : Set V3) : 0 ≤ sol x C := by
  unfold sol
  split
  · rename_i h
    have h1 : 0 ≤ MeasureTheory.volume.real (C ∩ Metric.ball x (Classical.choose h)) :=
      MeasureTheory.measureReal_nonneg
    exact div_nonneg (mul_nonneg (by norm_num) h1)
      (pow_nonneg (le_of_lt (Classical.choose_spec h).1) 3)
  · exact le_refl 0

private theorem p18_totalSolid_nonneg (V X : Set V3) (hp : Packing V) (hs : saturated V)
    (hm : mcellSet V X) : 0 ≤ totalSolid V X := by
  refine p18_setSum_nonneg (FINITE_VX V X hp hs hm) _ fun x hx => ?_
  exact p18_sol_nonneg x X

/-! ### gammaE (pattern-lambda) bound -/

private noncomputable def p18_gammaE (V X : Set V3) (f : ℝ → ℝ) (e : Set V3) : ℝ :=
  if e ∈ edgeX V X then
    let q := Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}
    dihX V X (q.1, q.2) * f (hl [q.1, q.2])
  else 0

private theorem p18_gammaE_le (V X : Set V3) (e : Set V3) :
    p18_gammaE V X lmfun e ≤ Real.pi * (h0 / (h0 - 1)) := by
  unfold p18_gammaE
  split_ifs with he
  · have h1 : dihX V X
        ((Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}).1,
        (Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}).2) ≤ Real.pi :=
      DIHX_LE_PI V X _ _
    have h2 : lmfun
        (hl [(Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}).1,
        (Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}).2])
        ≤ h0 / (h0 - 1) := by
      refine lmfun_bounded ?_
      rw [HL_2]
      positivity
    exact mul_le_mul h1 h2 (lmfun_pos_le _) Real.pi_pos.le
  · exact mul_nonneg Real.pi_pos.le (by norm_num [h0])

/-! ### card edgeX ≤ 16 -/

private theorem p18_cellParams_spec (V : Set V3) (X : Set V3) (hm : mcellSet V X) :
    (cellParams V X).1 ≤ 4 ∧ barV V 3 (cellParams V X).2 ∧ X = mcell (cellParams V X).1 V
      (cellParams V X).2 := by
  obtain ⟨i, ul, rfl, hb⟩ := hm
  have hwit : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ mcell i V ul = mcell p.1 V p.2 := by
    rcases le_or_gt i 4 with h4 | h4
    · exact ⟨(i, ul), h4, hb, rfl⟩
    · exact ⟨(4, ul), le_refl 4, hb, (MCELL_EXPLICIT i V ul).2.2.2.2 (le_of_lt h4)⟩
  exact Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ mcell i V ul = mcell p.1 V p.2) hwit

private theorem p18_vx_card_le4 (V : Set V3) (X : Set V3) (hm : mcellSet V X) :
    Nat.card (VX V X) ≤ 4 := by
  classical
  by_cases hnull : nullSet X
  · rw [VX, if_pos hnull]
    simp
  · obtain ⟨hk, hbarq, hXq⟩ := p18_cellParams_spec V X hm
    by_cases hp0 : (cellParams V X).1 = 0
    · have hvx : VX V X = ∅ := by rw [VX, if_neg hnull, if_pos hp0]
      rw [hvx]
      simp
    · have hvx : VX V X = setOfList (truncateSimplex ((cellParams V X).1 - 1)
        (cellParams V X).2) := by
        rw [VX, if_neg hnull, if_neg hp0]
      rw [hvx]
      -- the truncation list has length k ≤ 4 (epsilon predicate satisfiable)
      have htsat : (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).length
          = (cellParams V X).1 - 1 + 1 := by
        have heps := @Classical.epsilon_spec _
          (fun vl : List V3 => vl.length = (cellParams V X).1 - 1 + 1 ∧
            initialSublist vl (cellParams V X).2)
          ⟨(cellParams V X).2.take ((cellParams V X).1 - 1 + 1),
            List.length_take_of_le (by rw [hbarq.1]; omega),
            ⟨(cellParams V X).2.drop ((cellParams V X).1 - 1 + 1),
              (List.take_append_drop _ _).symm⟩⟩
        exact heps.1
      have hL4 : (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).length ≤ 4 := by
        rw [htsat]; omega
      have hfinL : (setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2)).Finite :=
        Set.Finite.ofFinset
          (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).toFinset
          (fun x => by simp [setOfList])
      have heqf : hfinL.toFinset =
          (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).toFinset := by
        ext x
        simp [setOfList]
      have hc : Nat.card ↥(setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2)) = hfinL.toFinset.card := by
        rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfinL]
      rw [hc, heqf]
      exact (List.toFinset_card_le _).trans hL4

private theorem p18_card_edgex_le16 (V : Set V3) (X : Set V3) (hm : mcellSet V X) :
    Nat.card (edgeX V X) ≤ 16 := by
  classical
  have hfin : (VX V X).Finite := by
    by_cases hnull : nullSet X
    · rw [VX, if_pos hnull]
      exact Set.finite_empty
    · by_cases hp0 : (cellParams V X).1 = 0
      · have hvx : VX V X = ∅ := by rw [VX, if_neg hnull, if_pos hp0]
        rw [hvx]
        exact Set.finite_empty
      · have hvx : VX V X = setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2) := by
          rw [VX, if_neg hnull, if_neg hp0]
        rw [hvx]
        refine Set.Finite.ofFinset
          (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).toFinset ?_
        intro x
        simp [setOfList]
  have hn := p18_vx_card_le4 V X hm
  have hsub : (edgeX V X : Set (Set V3)) ⊆
      (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (VX V X ×ˢ VX V X) := by
    rintro e ⟨u, v, rfl, hu, hv, -⟩
    exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
  have himg : ((fun p : V3 × V3 => ({p.1, p.2} : Set V3)) ''
      (VX V X ×ˢ VX V X)).Finite := Set.Finite.image _ (hfin.prod hfin)
  have he : (edgeX V X).Finite := himg.subset hsub
  have h1 : Nat.card (edgeX V X) ≤
      Nat.card ((fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (VX V X ×ˢ VX V X)) :=
    by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsub himg
  have h2 : Nat.card ((fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (VX V X ×ˢ VX V X))
      ≤ Nat.card (VX V X ×ˢ VX V X) := Nat.card_image_le (hfin.prod hfin)
  have hprod : Nat.card (VX V X ×ˢ VX V X) = Nat.card (VX V X) * Nat.card (VX V X) := by
    rw [Nat.card_congr (Equiv.Set.prod (VX V X) (VX V X)), Nat.card_prod]
  calc Nat.card (edgeX V X)
      ≤ Nat.card (VX V X) * Nat.card (VX V X) := h1.trans (h2.trans hprod.le)
    _ ≤ 16 := by
        have := Nat.mul_le_mul hn hn
        simpa using this

/-! ### main bound -/

private theorem p18_edgex_finite (V : Set V3) (X : Set V3) : (edgeX V X).Finite := by
  classical
  have hfin : (VX V X).Finite := by
    by_cases hnull : nullSet X
    · rw [VX, if_pos hnull]
      exact Set.finite_empty
    · by_cases hp0 : (cellParams V X).1 = 0
      · have hvx : VX V X = ∅ := by rw [VX, if_neg hnull, if_pos hp0]
        rw [hvx]
        exact Set.finite_empty
      · have hvx : VX V X = setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2) := by
          rw [VX, if_neg hnull, if_neg hp0]
        rw [hvx]
        refine Set.Finite.ofFinset
          (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).toFinset ?_
        intro x
        simp [setOfList]
  have hsub : (edgeX V X : Set (Set V3)) ⊆
      (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (VX V X ×ˢ VX V X) := by
    rintro e ⟨u, v, rfl, hu, hv, -⟩
    exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
  have himg : ((fun p : V3 × V3 => ({p.1, p.2} : Set V3)) ''
      (VX V X ×ˢ VX V X)).Finite := Set.Finite.image _ (hfin.prod hfin)
  exact himg.subset hsub

private theorem p18_BOUND_GAMMA_X_lmfun :
    ∃ c : ℝ, ∀ (V : Set V3) (X : Set V3), Packing V → saturated V → mcellSet V X →
      gammaX V X lmfun ≤ c := by
  classical
  refine ⟨4 / 3 * Real.pi * 8 ^ 3 + (8 * mm2 / Real.pi) *
    (16 * (Real.pi * (h0 / (h0 - 1)))), ?_⟩
  intro V X hp hs hm
  rcases Set.eq_empty_or_nonempty X with hXe | hXne
  · have hnull : nullSet X := by rw [nullSet, hXe]; simp
    have hvx0 : VX V X = ∅ := by rw [VX, if_pos hnull]
    have hts : totalSolid V X = 0 := by
      rw [totalSolid, hvx0]
      simp [setSum]
    have hedg : edgeX V X = (∅ : Set (Set V3)) := by
      ext e
      simp [edgeX, hvx0]
    have hvol : MeasureTheory.volume.real X = 0 := by
      rw [MeasureTheory.Measure.real_def, hnull]
      simp
    have hzero : gammaX V X lmfun = 0 := by
      rw [gammaX, hvol, hts, hedg]
      simp [setSum]
    rw [hzero]
    have h1 : (0:ℝ) < h0 / (h0 - 1) := by norm_num [h0]
    have hc0 : (0:ℝ) ≤ 8 * mm2 / Real.pi :=
      div_nonneg (mul_nonneg (by norm_num) p18_mm2_nonneg) Real.pi_pos.le
    have hc1 : (0:ℝ) ≤ 16 * (Real.pi * (h0 / (h0 - 1))) :=
      mul_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le h1.le)
    exact add_nonneg (by positivity) (mul_nonneg hc0 hc1)
  · obtain ⟨p, hpX⟩ := hXne
    have h1 : (0:ℝ) < h0 / (h0 - 1) := by norm_num [h0]
    have hm' : X ∈ mcellSet V := hm
    simp only [mcellSet] at hm
    obtain ⟨i, ul, hXul, hb⟩ := hm
    have hmeas : MeasurableSet X := by rw [hXul]; exact MEASURABLE_MCELL V ul i hs hp hb
    have hsub8 : X ⊆ Metric.ball p 8 := MCELL_SUBSET_BALL8_2 V X p hp hs hm' hpX
    have hball : MeasureTheory.volume.real (Metric.ball p 8) = 4 / 3 * Real.pi * 8 ^ 3 := by
      rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      ring
    have hvol : MeasureTheory.volume.real X ≤ 4 / 3 * Real.pi * 8 ^ 3 := by
      have hmono : MeasureTheory.volume.real X ≤ MeasureTheory.volume.real (Metric.ball p 8) :=
        MeasureTheory.measureReal_mono hsub8 (by finiteness)
      rw [hball] at hmono
      exact hmono
    have hfin : (edgeX V X).Finite := p18_edgex_finite V X
    have hsum : setSum (edgeX V X) (p18_gammaE V X lmfun)
        ≤ 16 * (Real.pi * (h0 / (h0 - 1))) := by
      have hbound := p18_setSum_le_card_mul hfin (p18_gammaE V X lmfun)
        (Real.pi * (h0 / (h0 - 1))) (fun e _ => p18_gammaE_le V X e)
      have hcard := p18_card_edgex_le16 V X hm'
      have h16 : ((Nat.card (edgeX V X) : ℕ) : ℝ) ≤ 16 := by exact_mod_cast hcard
      have hd0 : (0:ℝ) ≤ Real.pi * (h0 / (h0 - 1)) :=
        mul_nonneg Real.pi_pos.le h1.le
      have hcd : ((Nat.card (edgeX V X) : ℕ) : ℝ) * (Real.pi * (h0 / (h0 - 1)))
          ≤ 16 * (Real.pi * (h0 / (h0 - 1))) :=
        mul_le_mul_of_nonneg_right h16 hd0
      linarith
    have hts : 0 ≤ totalSolid V X := p18_totalSolid_nonneg V X hp hs hm'
    have hcoef2 : (0:ℝ) ≤ 2 * mm1 / Real.pi :=
      div_nonneg (mul_nonneg (by norm_num) p18_mm1_nonneg) Real.pi_pos.le
    have hcoef8 : (0:ℝ) ≤ 8 * mm2 / Real.pi :=
      div_nonneg (mul_nonneg (by norm_num) p18_mm2_nonneg) Real.pi_pos.le
    have hexp : gammaX V X lmfun = MeasureTheory.volume.real X - (2 * mm1 / Real.pi) * totalSolid V X
        + (8 * mm2 / Real.pi) * setSum (edgeX V X) (p18_gammaE V X lmfun) := rfl
    rw [hexp]
    have hprod : (8 * mm2 / Real.pi) * setSum (edgeX V X) (p18_gammaE V X lmfun)
        ≤ (8 * mm2 / Real.pi) * (16 * (Real.pi * (h0 / (h0 - 1)))) :=
      mul_le_mul_of_nonneg_left hsum hcoef8
    have hts2 : (0:ℝ) ≤ (2 * mm1 / Real.pi) * totalSolid V X :=
      mul_nonneg hcoef2 hts
    linarith


/-! ### final kit pieces for the SUM_GAMMAX assembly -/

private theorem p18_setSum_le {α : Type*} {s : Set α} (hs : s.Finite) (f g : α → ℝ)
    (h : ∀ a ∈ s, f a ≤ g a) : setSum s f ≤ setSum s g := by
  unfold setSum
  rw [dif_pos hs, dif_pos hs]
  exact Finset.sum_le_sum fun a ha =>
    h a ((Set.Finite.mem_toFinset hs).mp ha)

private theorem p18_criticalEdgeX_finite (V X : Set V3) : (criticalEdgeX V X).Finite :=
  (p18_edgex_finite V X).subset fun e he => by
    simp only [criticalEdgeX, Set.mem_setOf_eq] at he ⊢
    obtain ⟨u, v, rfl, hex, -, -⟩ := he
    exact hex

/-- Banked on PA10 `HDTFNFZ` (still `sorry` there; PA15/PA16 already consume it). -/
private theorem p18_vx_sub_cell (V X : Set V3) (u : V3) (hs : saturated V) (hp : Packing V)
    (hm : mcellSet V X) (hu : u ∈ VX V X) : u ∈ X := by
  obtain ⟨i, ul, rfl, hb⟩ := hm
  by_cases hnull : nullSet (mcell i V ul)
  · rw [VX, if_pos hnull] at hu
    exact absurd hu (by simp)
  · rw [HDTFNFZ (v := u) hs hp hb rfl hnull] at hu
    exact hu.2

private theorem p18_crit_edge_mem_vx (V X : Set V3) (u v : V3) (hm : mcellSet V X)
    (he : criticalEdgeX V X ({u, v} : Set V3)) : u ∈ VX V X := by
  simp only [criticalEdgeX, Set.mem_setOf_eq] at he
  obtain ⟨u', v', hpe, hex, -, -⟩ := he
  rw [edgeX, Set.mem_setOf_eq] at hex
  obtain ⟨u0, v0, hpe2, hu0, hv0, -⟩ := hex
  have hu : u ∈ ({u, v} : Set V3) := by simp
  rw [hpe2] at hu
  rcases Set.mem_insert_iff.mp hu with h | h
  · exact h ▸ hu0
  · exact Set.mem_singleton_iff.mp h ▸ hv0

private theorem p18_crit_family_card (V : Set V3) (u v : V3) (hs : saturated V)
    (hp : Packing V) (hu : u ∈ V) (c2n : ℕ)
    (hc2 : ∀ (W : Set V3) (w : V3), saturated W → Packing W → w ∈ W →
      Nat.card {Y : Set V3 | mcellSet W Y ∧ w ∈ VX W Y} ≤ c2n) :
    Nat.card {X : Set V3 | mcellSet V X ∧ criticalEdgeX V X ({u, v} : Set V3)} ≤ c2n := by
  classical
  have hsub : {X : Set V3 | mcellSet V X ∧ criticalEdgeX V X ({u, v} : Set V3)} ⊆
      {X : Set V3 | mcellSet V X ∧ u ∈ VX V X} := fun X hX =>
    ⟨hX.1, p18_crit_edge_mem_vx V X u v hX.1 hX.2⟩
  have hfin2 : ({X : Set V3 | mcellSet V X ∧ u ∈ VX V X} : Set (Set V3)).Finite := by
    have hsub2 : {X : Set V3 | mcellSet V X ∧ u ∈ VX V X} ⊆
        {X : Set V3 | X ⊆ Metric.ball u 8 ∧ mcellSet V X} := by
      intro X hX
      have huX : u ∈ X := p18_vx_sub_cell V X u hs hp hX.1 hX.2
      exact ⟨MCELL_SUBSET_BALL8_2 V X u hp hs hX.1 huX, hX.1⟩
    exact (FINITE_MCELL_SET_LEMMA_2 V 8 u hp hs).subset hsub2
  have hmono : Nat.card {X : Set V3 | mcellSet V X ∧ criticalEdgeX V X ({u, v} : Set V3)} ≤
      Nat.card {X : Set V3 | mcellSet V X ∧ u ∈ VX V X} := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub hfin2
  exact hmono.trans (hc2 V u hs hp hu)

private theorem p18_vx_sub_V (V X : Set V3) (u : V3) (hm : mcellSet V X)
    (hu : u ∈ VX V X) : u ∈ V := by
  by_cases hnull : nullSet X
  · rw [VX, if_pos hnull] at hu
    exact absurd hu (by simp)
  · obtain ⟨hk, hbarq, -⟩ := p18_cellParams_spec V X hm
    by_cases hp0 : (cellParams V X).1 = 0
    · rw [VX, if_neg hnull, if_pos hp0] at hu
      exact absurd hu (by simp)
    · rw [VX, if_neg hnull, if_neg hp0] at hu
      have hsub : setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2) ⊆ setOfList (cellParams V X).2 :=
        SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET _ _ (by rw [hbarq.1]; omega)
      exact BARV_SUBSET V 3 (cellParams V X).2 hbarq (hsub hu)

private theorem p18_two_hplus_lt_three : (2:ℝ) * hplus < 3 := by norm_num [hplus]

/-! ### product-decomposition helper for the ordered-pair sums -/

private theorem p18_setSum_prod {α β : Type*} {A : Set α} {B : Set β} (ha : A.Finite)
    (hb : B.Finite) (f : α × β → ℝ) :
    setSum (A ×ˢ B) f = setSum A (fun a => setSum B (fun b => f (a, b))) := by
  have hprodfin : (A ×ˢ B).Finite := ha.prod hb
  have hprod : hprodfin.toFinset = ha.toFinset ×ˢ hb.toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_prod, Finset.mem_product]
  have hlhs : setSum (A ×ˢ B) f = hprodfin.toFinset.sum f := by
    unfold setSum
    exact dif_pos hprodfin
  have hrhs : setSum A (fun a => setSum B (fun b => f (a, b)))
      = ha.toFinset.sum (fun a => hb.toFinset.sum fun b => f (a, b)) := by
    unfold setSum
    refine Eq.trans (dif_pos ha) (Finset.sum_congr rfl fun a _ => ?_)
    exact dif_pos hb
  rw [hlhs, hrhs, hprod]
  exact Finset.sum_product ha.toFinset hb.toFinset f

/-! ### SUM_GAMMAX_LMFUN_ESTIMATE: the cluster-sum main assembly (sum_gamma.hl:62-1462) -/

private theorem p18_sum_gammax_main (V : Set V3) :
    saturated V → Packing V →
    ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V → 1 ≤ r → cellClusterInequality V →
      TSKAJXY_statement →
      c * r ^ 2 ≤ setSum {X | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
        (fun X => gammaX V X lmfun) := by
  intro hs hp
  classical
  by_cases hsp : saturated V ∧ Packing V
  · -- constants (independent of r)
    obtain ⟨c1, hc1⟩ := p18_BOUND_GAMMA_X_lmfun
    obtain ⟨c2n, hc2⟩ := CARD_MCELL_CONTAINS_POINT_klemma
    obtain ⟨c3, hc3⟩ := BumpP4.BOUND_BETA_BUMP
    obtain ⟨d1, hd1⟩ := PACKING_BALL_BOUNDARY V 0 0 8 hp
    obtain ⟨d3, hd3⟩ := PACKING_BALL_BOUNDARY V 0 0 16 hp
    simp only [add_zero] at hd1 hd3
    set c2 : ℝ := ((c2n : ℕ) : ℝ) with hc2def
    set cc1 : ℝ := max c1 1 with hcc1def
    set cc3 : ℝ := max c3 1 with hcc3def
    have hc2pos : 0 ≤ c2 := Nat.cast_nonneg _
    have hcc1pos : 0 ≤ cc1 := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right c1 1)
    have hcc3pos : 0 ≤ cc3 := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right c3 1)
    have hcc1ge : ∀ W : Set V3, Packing W → saturated W → ∀ Z ∈ mcellSet W,
        gammaX W Z lmfun ≤ cc1 := fun W hW hW2 Z hZ =>
      le_trans (hc1 W Z hW hW2 hZ) (le_max_left _ _)
    have hcc3ge : ∀ (Z e : Set V3), Z ∈ mcellSet V → e ∈ criticalEdgeX V Z →
        betaBumpV1 V e Z ≤ cc3 := by
      intro Z e hmZ he
      show betaBump V e Z ≤ cc3
      exact le_trans (hc3 V Z e hs hp hmZ he) (le_max_left _ _)
    have hXpos : (0:ℝ) ≤ c2 * cc1 := mul_nonneg hc2pos hcc1pos
    have hXpos3 : (0:ℝ) ≤ c2 * cc3 := mul_nonneg hc2pos hcc3pos
    refine ⟨-((32:ℝ) * (c2 * cc1 * d1) + (32:ℝ) * (c2 * cc3 * d3)), ?_⟩
    intro r hsat hpack hr1 hcc hts
    -- the point sets T1/T3/T3' and the boundary counts
    set T1 : Set V3 := V ∩ Metric.ball 0 r with hT1def
    set T3 : Set V3 := {u : V3 | u ∈ V ∧ u ∈ Metric.ball 0 r ∧ u ∉ Metric.ball 0 (r - 8)}
      with hT3def
    set T3' : Set V3 := {u : V3 | u ∈ V ∧ u ∈ Metric.ball 0 r ∧ u ∉ Metric.ball 0 (r - 16)}
      with hT3'def
    have hT1fin : T1.Finite := hp.finite_inter_ball r
    have hT3fin : T3.Finite := hT1fin.subset fun u hu => by
      simp only [hT3def, Set.mem_setOf_eq] at hu
      exact ⟨hu.1, hu.2.1⟩
    have hT3'fin : T3'.Finite := hT1fin.subset fun u hu => by
      simp only [hT3'def, Set.mem_setOf_eq] at hu
      exact ⟨hu.1, hu.2.1⟩
    have hT3seteq : T3 = (V ∩ Metric.ball 0 r) \ (V ∩ Metric.ball 0 (r - 8)) := by
      ext u
      simp only [hT3def, Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff]
      tauto
    have hT3'seteq : T3' = (V ∩ Metric.ball 0 r) \ (V ∩ Metric.ball 0 (r - 16)) := by
      ext u
      simp only [hT3'def, Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff]
      tauto
    have hT3card : Nat.card T3 = Nat.card ↥((V ∩ Metric.ball 0 r) \
        (V ∩ Metric.ball 0 (r - 8))) := by rw [hT3seteq]
    have hT3'card : Nat.card T3' = Nat.card ↥((V ∩ Metric.ball 0 r) \
        (V ∩ Metric.ball 0 (r - 16))) := by rw [hT3'seteq]
    have hd1r : ((Nat.card T3 : ℕ) : ℝ) ≤ d1 * r ^ 2 := by rw [hT3card]; exact hd1 r hr1
    have hd3r : ((Nat.card T3' : ℕ) : ℝ) ≤ d3 * r ^ 2 := by rw [hT3'card]; exact hd3 r hr1
    -- the cell families B/B0/B1
    set B : Set (Set V3) := {X | X ⊆ Metric.ball 0 r ∧ mcellSet V X} with hBdef
    set B0 : Set (Set V3) := {X | X ∈ B ∧ criticalEdgeX V X = ∅} with hB0def
    set B1 : Set (Set V3) := {X | X ∈ B ∧ criticalEdgeX V X ≠ ∅} with hB1def
    have hBfin : B.Finite := FINITE_MCELL_SET_LEMMA V r hp hs
    have hB0fin : B0.Finite := hBfin.subset fun X hX => hX.1
    have hB1fin : B1.Finite := hBfin.subset fun X hX => hX.1
    have hB0pos : 0 ≤ setSum B0 (fun X => gammaX V X lmfun) :=
      p18_setSum_nonneg hB0fin _ fun X hX => hts V X hsat hpack hX.1.2 hX.2
    have hBsplit : B = B0 ∪ B1 := by
      ext X
      simp only [hBdef, hB0def, hB1def, Set.mem_setOf_eq, Set.mem_union]
      tauto
    have hB0B1disj : Disjoint B0 B1 := by
      rw [Set.disjoint_left]
      intro X h1 h2
      simp only [hB0def, hB1def, Set.mem_setOf_eq] at h1 h2
      exact h2.2 h1.2
    -- the edge pair sets T2/T4/T4'
    set T2 : Set (Set V3) := {y | ∃ u, u ∈ T1 ∧ ∃ v, v ∈ T1 ∧ u ≠ v ∧
      y = ({u, v} : Set V3) ∧ hl [u, v] ≤ hplus} with hT2def
    set T4 : Set (Set V3) := {e | ∃ m ∈ T3, ∃ n ∈ T3, m ≠ n ∧
      dist m n ≤ 2 * hplus ∧ e = ({m, n} : Set V3)} with hT4def
    set T4' : Set (Set V3) := {e | ∃ m ∈ T3', ∃ n ∈ T3', m ≠ n ∧
      dist m n ≤ 2 * hplus ∧ e = ({m, n} : Set V3)} with hT4'def
    have hT2fin : T2.Finite := by
      refine ((hT1fin.prod hT1fin).image
        (fun p : V3 × V3 => ({p.1, p.2} : Set V3))).subset ?_
      intro e he
      simp only [hT2def, Set.mem_setOf_eq] at he
      obtain ⟨u, hu, v, hv, hne, rfl, hle⟩ := he
      exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
    have hT4fin : T4.Finite := by
      refine ((hT3fin.prod hT3fin).image
        (fun p : V3 × V3 => ({p.1, p.2} : Set V3))).subset ?_
      intro e he
      simp only [hT4def, Set.mem_setOf_eq] at he
      obtain ⟨m, hm, n, hn, hne, hdle, rfl⟩ := he
      exact ⟨(m, n), ⟨hm, hn⟩, rfl⟩
    have hT4'fin : T4'.Finite := by
      refine ((hT3'fin.prod hT3'fin).image
        (fun p : V3 × V3 => ({p.1, p.2} : Set V3))).subset ?_
      intro e he
      simp only [hT4'def, Set.mem_setOf_eq] at he
      obtain ⟨m, hm, n, hn, hne, hdle, rfl⟩ := he
      exact ⟨(m, n), ⟨hm, hn⟩, rfl⟩
    have hT4sub : T4 ⊆ T2 := by
      intro e he
      simp only [hT4def, Set.mem_setOf_eq] at he
      obtain ⟨m, hm, n, hn, hne, hdle, rfl⟩ := he
      simp only [hT3def, Set.mem_setOf_eq] at hm hn
      simp only [hT2def, Set.mem_setOf_eq]
      refine ⟨m, ⟨hm.1, hm.2.1⟩, n, ⟨hn.1, hn.2.1⟩, hne, rfl, ?_⟩
      rw [HL_2]
      linarith
    have hT4'sub : T4' ⊆ T2 := by
      intro e he
      simp only [hT4'def, Set.mem_setOf_eq] at he
      obtain ⟨m, hm, n, hn, hne, hdle, rfl⟩ := he
      simp only [hT3'def, Set.mem_setOf_eq] at hm hn
      simp only [hT2def, Set.mem_setOf_eq]
      refine ⟨m, ⟨hm.1, hm.2.1⟩, n, ⟨hn.1, hn.2.1⟩, hne, rfl, ?_⟩
      rw [HL_2]
      linarith
    -- critical edges of cells in B are T2 pairs
    have hcritT2 : ∀ X ∈ B, ∀ e ∈ criticalEdgeX V X, e ∈ T2 := by
      intro X hX e he
      rw [criticalEdgeX, Set.mem_setOf_eq] at he
      obtain ⟨u, v, rfl, hex, -, hhi⟩ := he
      rw [edgeX, Set.mem_setOf_eq] at hex
      obtain ⟨u0, v0, hpe, hu0, hv0, hne⟩ := hex
      have huVX : u ∈ VX V X ∨ u ∈ VX V X := by
        have h1 : u ∈ ({u, v} : Set V3) := by simp
        rw [hpe] at h1
        rcases Set.mem_insert_iff.mp h1 with h | h
        · exact Or.inl (h ▸ hu0)
        · exact Or.inr (Set.mem_singleton_iff.mp h ▸ hv0)
      have hvVX : v ∈ VX V X ∨ v ∈ VX V X := by
        have h1 : v ∈ ({u, v} : Set V3) := by simp
        rw [hpe] at h1
        rcases Set.mem_insert_iff.mp h1 with h | h
        · exact Or.inl (h ▸ hu0)
        · exact Or.inr (Set.mem_singleton_iff.mp h ▸ hv0)
      have huV : u ∈ V ∧ u ∈ X := by
        rcases huVX with h | h
        · exact ⟨p18_vx_sub_V V X u hX.2 h, p18_vx_sub_cell V X u hs hp hX.2 h⟩
        · exact ⟨p18_vx_sub_V V X u hX.2 h, p18_vx_sub_cell V X u hs hp hX.2 h⟩
      have hvV : v ∈ V ∧ v ∈ X := by
        rcases hvVX with h | h
        · exact ⟨p18_vx_sub_V V X v hX.2 h, p18_vx_sub_cell V X v hs hp hX.2 h⟩
        · exact ⟨p18_vx_sub_V V X v hX.2 h, p18_vx_sub_cell V X v hs hp hX.2 h⟩
      have huv : u ≠ v := by
        by_contra hcon
        have h1 : v0 ∈ ({u0, v0} : Set V3) := by simp
        have h2 : u0 ∈ ({u0, v0} : Set V3) := by simp
        rw [← hpe, ← hcon] at h1 h2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
        rcases h2 with h2 | h2 <;> rcases h1 with h1 | h1
        · exact hne (h2.trans h1.symm)
        · exact hne (h2.trans h1.symm)
        · exact hne (h2.trans h1.symm)
        · exact hne (h2.trans h1.symm)
      simp only [hT2def, Set.mem_setOf_eq, hT1def, Set.mem_inter_iff]
      exact ⟨u, ⟨huV.1, Metric.mem_ball.mpr (hX.1 huV.2)⟩, v,
        ⟨hvV.1, Metric.mem_ball.mpr (hX.1 hvV.2)⟩, huv, rfl, hhi⟩
    have hcritXset : ∀ X ∈ B,
        criticalEdgeX V X = {e : Set V3 | e ∈ T2 ∧ e ∈ criticalEdgeX V X} := by
      intro X hX
      ext e
      simp only [Set.mem_setOf_eq]
      constructor
      · intro he
        exact ⟨hcritT2 X hX e he, he⟩
      · intro he
        exact he.2
    -- criticalWeight bounds
    have hcritWle : ∀ X : Set V3, criticalWeight V X ≤ 1 := by
      intro X
      by_cases h0 : Nat.card (criticalEdgeX V X) = 0
      · unfold criticalWeight
        rw [h0]
        norm_num
      · have hposr : (0:ℝ) < ((Nat.card (criticalEdgeX V X) : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
        have h1le : (1:ℝ) ≤ ((Nat.card (criticalEdgeX V X) : ℕ) : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero h0
        unfold criticalWeight
        exact (div_le_one hposr).mpr h1le
    have hcritWnn : ∀ X : Set V3, 0 ≤ criticalWeight V X := by
      intro X
      unfold criticalWeight
      exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hcardpos : ∀ X : Set V3, criticalEdgeX V X ≠ ∅ →
        1 ≤ (Nat.card (criticalEdgeX V X) : ℕ) := by
      intro X hne
      have hfin := p18_criticalEdgeX_finite V X
      have hnp : (criticalEdgeX V X).Nonempty := (Set.nonempty_iff_ne_empty).mpr hne
      obtain ⟨e, he⟩ := hnp
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
      exact Finset.card_pos.mpr ⟨e, (Set.Finite.mem_toFinset hfin).mpr he⟩
    -- endpoint data and cluster-family finiteness/cardinality for T2 edges
    have hT2pts : ∀ e ∈ T2, ∃ u : V3, ∃ v : V3, e = ({u, v} : Set V3) ∧ u ≠ v ∧
        u ∈ V ∧ u ∈ Metric.ball 0 r ∧ v ∈ V ∧ v ∈ Metric.ball 0 r ∧
        hl [u, v] ≤ hplus ∧ dist u v ≤ 2 * hplus := by
      intro e he
      simp only [hT2def, Set.mem_setOf_eq] at he
      obtain ⟨u, hu, v, hv, hne, rfl, hle⟩ := he
      simp only [hT1def, Set.mem_inter_iff] at hu hv
      refine ⟨u, v, rfl, hne, hu.1, hu.2, hv.1, hv.2, hle, ?_⟩
      rw [HL_2] at hle
      linarith
    have hfamfin : ∀ e ∈ T2, (cellCluster V e).Finite := by
      intro e he
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      have huX : ∀ X ∈ cellCluster V ({u, v} : Set V3), u ∈ X := by
        intro X hX
        simp only [cellCluster, Set.mem_setOf_eq] at hX
        have hsub := CRITICAL_EDGEX_SUBSET_MCELL V X ({u, v} : Set V3) hp hs hX.2 hX.1
        exact hsub (by simp)
      exact (FINITE_MCELL_SET_LEMMA_2 V 8 u hp hs).subset fun X hX =>
        ⟨MCELL_SUBSET_BALL8_2 V X u hp hs hX.2 (huX X hX), hX.2⟩
    have hfameq : ∀ (u v : V3), cellCluster V ({u, v} : Set V3) =
        {X : Set V3 | mcellSet V X ∧ criticalEdgeX V X ({u, v} : Set V3)} := by
      intro u v
      ext X
      simp only [cellCluster, Set.mem_setOf_eq]
      tauto
    have hfamcard : ∀ e ∈ T2, ((Nat.card (cellCluster V e) : ℕ) : ℝ) ≤ c2 := by
      intro e he
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      rw [hfameq u v]
      exact Nat.cast_le.mpr (p18_crit_family_card V u v hs hp huV c2n hc2)
    -- inner/outer families of a cluster (w.r.t. ball 0 r and ball 0 (r-8))
    set innr : Set V3 → Set (Set V3) :=
      fun e => {X | X ∈ cellCluster V e ∧ X ⊆ Metric.ball 0 r} with hinnrdef
    set outr : Set V3 → Set (Set V3) :=
      fun e => {X | X ∈ cellCluster V e ∧ ¬(X ⊆ Metric.ball 0 r)} with houtrdef
    set inn8 : Set V3 → Set (Set V3) :=
      fun e => {X | X ∈ cellCluster V e ∧ X ⊆ Metric.ball 0 (r - 8)} with hinn8def
    set ann8 : Set V3 → Set (Set V3) :=
      fun e => {X | X ∈ cellCluster V e ∧ ¬(X ⊆ Metric.ball 0 (r - 8))} with hann8def
    have hinnrfin : ∀ e ∈ T2, (innr e).Finite := fun e he =>
      ((hfamfin e he).subset fun X hX => by obtain ⟨h1, -⟩ := hX; exact h1)
    have houtrfin : ∀ e ∈ T2, (outr e).Finite := fun e he =>
      ((hfamfin e he).subset fun X hX => by obtain ⟨h1, -⟩ := hX; exact h1)
    have hinn8fin : ∀ e ∈ T2, (inn8 e).Finite := fun e he =>
      ((hfamfin e he).subset fun X hX => by obtain ⟨h1, -⟩ := hX; exact h1)
    have hann8fin : ∀ e ∈ T2, (ann8 e).Finite := fun e he =>
      ((hfamfin e he).subset fun X hX => by obtain ⟨h1, -⟩ := hX; exact h1)
    have hfamunion : ∀ e : Set V3, cellCluster V e = innr e ∪ outr e := by
      intro e
      ext X
      show (e ∈ criticalEdgeX V X ∧ X ∈ mcellSet V) ↔
        (X ∈ {q : Set V3 | q ∈ cellCluster V e ∧ q ⊆ Metric.ball 0 r} ∨
         X ∈ {q : Set V3 | q ∈ cellCluster V e ∧ ¬(q ⊆ Metric.ball 0 r)})
      simp only [cellCluster, Set.mem_setOf_eq, Set.mem_union]
      tauto
    have hdisj : ∀ e : Set V3, Disjoint (innr e) (outr e) := by
      intro e
      rw [Set.disjoint_left]
      intro X h1 h2
      obtain ⟨-, h1'⟩ := h1
      obtain ⟨-, h2''⟩ := h2
      exact h2'' h1'
    have hfamunion8 : ∀ e : Set V3, cellCluster V e = inn8 e ∪ ann8 e := by
      intro e
      ext X
      show (e ∈ criticalEdgeX V X ∧ X ∈ mcellSet V) ↔
        (X ∈ {q : Set V3 | q ∈ cellCluster V e ∧ q ⊆ Metric.ball 0 (r - 8)} ∨
         X ∈ {q : Set V3 | q ∈ cellCluster V e ∧ ¬(q ⊆ Metric.ball 0 (r - 8))})
      simp only [cellCluster, Set.mem_setOf_eq, Set.mem_union]
      tauto
    have hdisj8 : ∀ e : Set V3, Disjoint (inn8 e) (ann8 e) := by
      intro e
      rw [Set.disjoint_left]
      intro X h1 h2
      obtain ⟨-, h1'⟩ := h1
      obtain ⟨-, h2''⟩ := h2
      exact h2'' h1'
    -- per-edge cluster inequality (from cellClusterInequality)
    have hcluster : ∀ e ∈ T2,
        setSum (innr e) (fun X => gammaX V X lmfun * criticalWeight V X)
          + setSum (outr e) (fun X => gammaX V X lmfun * criticalWeight V X)
          + setSum (cellCluster V e) (fun X => betaBumpV1 V e X) ≥ 0 := by
      intro e he
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      have h0 : 0 ≤ setSum (cellCluster V ({u, v} : Set V3))
          (fun X => gammaX V X lmfun * criticalWeight V X
            + betaBumpV1 V ({u, v} : Set V3) X) := by
        simpa only [clusterGamma] using hcc ({u, v} : Set V3)
      rw [hfamunion ({u, v} : Set V3), p18_setSum_union (hinnrfin _ he) (houtrfin _ he)
        (hdisj ({u, v} : Set V3)) (fun X => gammaX V X lmfun * criticalWeight V X
          + betaBumpV1 V ({u, v} : Set V3) X),
        ← p18_setSum_add (hinnrfin _ he) (fun X => gammaX V X lmfun * criticalWeight V X)
          (fun X => betaBumpV1 V ({u, v} : Set V3) X),
        ← p18_setSum_add (houtrfin _ he) (fun X => gammaX V X lmfun * criticalWeight V X)
          (fun X => betaBumpV1 V ({u, v} : Set V3) X)] at h0
      have hβ : setSum (cellCluster V ({u, v} : Set V3))
          (fun X => betaBumpV1 V ({u, v} : Set V3) X)
          = setSum (innr ({u, v} : Set V3)) (fun X => betaBumpV1 V ({u, v} : Set V3) X)
            + setSum (outr ({u, v} : Set V3)) (fun X => betaBumpV1 V ({u, v} : Set V3) X) := by
        rw [hfamunion ({u, v} : Set V3), p18_setSum_union (hinnrfin _ he) (houtrfin _ he)
          (hdisj ({u, v} : Set V3)) (fun X => betaBumpV1 V ({u, v} : Set V3) X)]
      linarith
    -- per-edge bounds for the two remainder sums
    have hQ2le : ∀ e ∈ T2,
        setSum (outr e) (fun X => gammaX V X lmfun * criticalWeight V X) ≤ c2 * cc1 := by
      intro e he
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      have hcardmono : ((Nat.card (outr ({u, v} : Set V3)) : ℕ) : ℝ)
          ≤ ((Nat.card (cellCluster V ({u, v} : Set V3)) : ℕ) : ℝ) := by
        refine Nat.cast_le.mpr ?_
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        refine Set.ncard_le_ncard (fun X hX => ?_) (hfamfin ({u, v} : Set V3) he)
        obtain ⟨h1, -⟩ := hX
        exact h1
      calc setSum (outr ({u, v} : Set V3)) (fun X => gammaX V X lmfun * criticalWeight V X)
          ≤ setSum (outr ({u, v} : Set V3)) (fun _ => cc1) := by
            refine p18_setSum_le (houtrfin ({u, v} : Set V3) he) _ _ fun X hX => ?_
            obtain ⟨hfam, -⟩ := hX
            simp only [cellCluster, Set.mem_setOf_eq] at hfam
            have hgm : gammaX V X lmfun ≤ cc1 := hcc1ge V hp hs X hfam.2
            calc gammaX V X lmfun * criticalWeight V X
                ≤ cc1 * criticalWeight V X := mul_le_mul_of_nonneg_right hgm (hcritWnn X)
              _ ≤ cc1 * 1 := mul_le_mul_of_nonneg_left (hcritWle X) hcc1pos
              _ = cc1 := by ring
        _ = ((Nat.card (outr ({u, v} : Set V3)) : ℕ) : ℝ) * cc1 :=
            p18_setSum_const (houtrfin ({u, v} : Set V3) he) cc1
        _ ≤ ((Nat.card (cellCluster V ({u, v} : Set V3)) : ℕ) : ℝ) * cc1 :=
            mul_le_mul_of_nonneg_right hcardmono hcc1pos
        _ ≤ c2 * cc1 := mul_le_mul_of_nonneg_right (hfamcard ({u, v} : Set V3) he) hcc1pos
    have hQ3outle : ∀ e ∈ T2,
        setSum (ann8 e) (fun X => betaBumpV1 V e X) ≤ c2 * cc3 := by
      intro e he
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      have hcardmono : ((Nat.card (ann8 ({u, v} : Set V3)) : ℕ) : ℝ)
          ≤ ((Nat.card (cellCluster V ({u, v} : Set V3)) : ℕ) : ℝ) := by
        refine Nat.cast_le.mpr ?_
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        refine Set.ncard_le_ncard (fun X hX => ?_) (hfamfin ({u, v} : Set V3) he)
        obtain ⟨h1, -⟩ := hX
        exact h1
      calc setSum (ann8 ({u, v} : Set V3)) (fun X => betaBumpV1 V ({u, v} : Set V3) X)
          ≤ setSum (ann8 ({u, v} : Set V3)) (fun _ => cc3) := by
            refine p18_setSum_le (hann8fin ({u, v} : Set V3) he) _ _ fun X hX => ?_
            obtain ⟨hfam, -⟩ := hX
            simp only [cellCluster, Set.mem_setOf_eq] at hfam
            exact hcc3ge X ({u, v} : Set V3) hfam.2 hfam.1
        _ = ((Nat.card (ann8 ({u, v} : Set V3)) : ℕ) : ℝ) * cc3 :=
            p18_setSum_const (hann8fin ({u, v} : Set V3) he) cc3
        _ ≤ ((Nat.card (cellCluster V ({u, v} : Set V3)) : ℕ) : ℝ) * cc3 :=
            mul_le_mul_of_nonneg_right hcardmono hcc3pos
        _ ≤ c2 * cc3 := mul_le_mul_of_nonneg_right (hfamcard ({u, v} : Set V3) he) hcc3pos
    have hbeta3le : ∀ e ∈ T2,
        setSum (cellCluster V e) (fun X => betaBumpV1 V e X) ≤ c2 * cc3 := by
      intro e he
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      calc setSum (cellCluster V ({u, v} : Set V3)) (fun X => betaBumpV1 V ({u, v} : Set V3) X)
          ≤ setSum (cellCluster V ({u, v} : Set V3)) (fun _ => cc3) := by
            refine p18_setSum_le (hfamfin ({u, v} : Set V3) he) _ _ fun X hX => ?_
            simp only [cellCluster, Set.mem_setOf_eq] at hX
            exact hcc3ge X ({u, v} : Set V3) hX.2 hX.1
        _ = ((Nat.card (cellCluster V ({u, v} : Set V3)) : ℕ) : ℝ) * cc3 :=
            p18_setSum_const (hfamfin ({u, v} : Set V3) he) cc3
        _ ≤ c2 * cc3 := mul_le_mul_of_nonneg_right (hfamcard ({u, v} : Set V3) he) hcc3pos
    -- outside families are empty off T4/T4'
    have houtempty : ∀ e ∈ T2, e ∉ T4 → outr e = (∅ : Set (Set V3)) := by
      intro e he hne4
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      refine Set.eq_empty_iff_forall_notMem.mpr fun X hX => ?_
      obtain ⟨hfam, hnotsub⟩ := hX
      simp only [cellCluster, Set.mem_setOf_eq] at hfam
      rw [Set.not_subset] at hnotsub
      obtain ⟨p, hpX, hpball⟩ := hnotsub
      have hmX : mcellSet V X := hfam.2
      have hsubX := CRITICAL_EDGEX_SUBSET_MCELL V X ({u, v} : Set V3) hp hs hmX hfam.1
      have huX2 : u ∈ X := hsubX (by simp)
      have hvX2 : v ∈ X := hsubX (by simp)
      have hpu : dist p u < 8 := MCELL_SUBSET_BALL8_2 V X u hp hs hmX huX2 hpX
      have hpv : dist p v < 8 := MCELL_SUBSET_BALL8_2 V X v hp hs hmX hvX2 hpX
      have hp0 : r ≤ dist p 0 := not_lt.mp (fun hc => hpball (Metric.mem_ball.mpr hc))
      have hu0 : r - 8 < dist u 0 := by
        have htri : dist p 0 ≤ dist p u + dist u 0 := dist_triangle p u 0
        linarith
      have hv0 : r - 8 < dist v 0 := by
        have htri : dist p 0 ≤ dist p v + dist v 0 := dist_triangle p v 0
        linarith
      exact hne4 ⟨u, ⟨huV, huB, fun hcon => by
        have := Metric.mem_ball.mp hcon; linarith⟩,
        v, ⟨hvV, hvB, fun hcon => by
        have := Metric.mem_ball.mp hcon; linarith⟩, hne,
        by rw [HL_2] at hle; linarith, rfl⟩
    have hann8empty : ∀ e ∈ T2, e ∉ T4' → ann8 e = (∅ : Set (Set V3)) := by
      intro e he hne4
      obtain ⟨u, v, rfl, hne, huV, huB, hvV, hvB, hle, hdle⟩ := hT2pts e he
      refine Set.eq_empty_iff_forall_notMem.mpr fun X hX => ?_
      obtain ⟨hfam, hnotsub⟩ := hX
      simp only [cellCluster, Set.mem_setOf_eq] at hfam
      rw [Set.not_subset] at hnotsub
      obtain ⟨p, hpX, hpball⟩ := hnotsub
      have hmX : mcellSet V X := hfam.2
      have hsubX := CRITICAL_EDGEX_SUBSET_MCELL V X ({u, v} : Set V3) hp hs hmX hfam.1
      have huX2 : u ∈ X := hsubX (by simp)
      have hvX2 : v ∈ X := hsubX (by simp)
      have hpu : dist p u < 8 := MCELL_SUBSET_BALL8_2 V X u hp hs hmX huX2 hpX
      have hpv : dist p v < 8 := MCELL_SUBSET_BALL8_2 V X v hp hs hmX hvX2 hpX
      have hp08 : r - 8 ≤ dist p 0 := not_lt.mp (fun hc => hpball (Metric.mem_ball.mpr hc))
      have hu0 : r - 16 < dist u 0 := by
        have htri : dist p 0 ≤ dist p u + dist u 0 := dist_triangle p u 0
        linarith
      have hv0 : r - 16 < dist v 0 := by
        have htri : dist p 0 ≤ dist p v + dist v 0 := dist_triangle p v 0
        linarith
      exact hne4 ⟨u, ⟨huV, huB, fun hcon => by
        have := Metric.mem_ball.mp hcon; linarith⟩,
        v, ⟨hvV, hvB, fun hcon => by
        have := Metric.mem_ball.mp hcon; linarith⟩, hne,
        by rw [HL_2] at hle; linarith, rfl⟩
    -- the reweighting on B1: gammaX = gammaX * (card * weight) = sum over critical edges
    have hreweight : setSum B1 (fun X => gammaX V X lmfun)
        = setSum T2 (fun e => setSum B1 (fun X => if e ∈ criticalEdgeX V X
            then gammaX V X lmfun * criticalWeight V X else 0)) := by
      have hstepA : ∀ X ∈ B1, gammaX V X lmfun
          = setSum (criticalEdgeX V X)
              (fun _ => gammaX V X lmfun * criticalWeight V X) := by
        intro X hX
        simp only [hB1def, Set.mem_setOf_eq] at hX
        obtain ⟨hXB, hne⟩ := hX
        have hposr : (0:ℝ) < ((Nat.card (criticalEdgeX V X) : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one (hcardpos X hne))
        have hcne : ((Nat.card (criticalEdgeX V X) : ℕ) : ℝ) ≠ 0 := ne_of_gt hposr
        have hcard1 : ((Nat.card (criticalEdgeX V X) : ℕ) : ℝ) * criticalWeight V X = 1 := by
          unfold criticalWeight
          rw [mul_comm]
          exact div_mul_cancel₀ (1:ℝ) hcne
        have h1 : setSum (criticalEdgeX V X)
            (fun _ => gammaX V X lmfun * criticalWeight V X)
            = gammaX V X lmfun
              * (((Nat.card (criticalEdgeX V X) : ℕ) : ℝ) * criticalWeight V X) := by
          rw [p18_setSum_lmul (p18_criticalEdgeX_finite V X) (gammaX V X lmfun)
            (fun _ => criticalWeight V X), p18_setSum_const
            (p18_criticalEdgeX_finite V X) (criticalWeight V X)]
        rw [h1, hcard1, mul_one]
      have hstepB : ∀ X ∈ B1, setSum (criticalEdgeX V X)
          (fun _ => gammaX V X lmfun * criticalWeight V X)
          = setSum T2 (fun e => if e ∈ criticalEdgeX V X
              then gammaX V X lmfun * criticalWeight V X else 0) := by
        intro X hX
        have hXB : X ∈ B := by
          simp only [hB1def, Set.mem_setOf_eq] at hX
          exact hX.1
        calc setSum (criticalEdgeX V X) (fun _ => gammaX V X lmfun * criticalWeight V X)
            = setSum {e : Set V3 | e ∈ T2 ∧ e ∈ criticalEdgeX V X}
                (fun _ => gammaX V X lmfun * criticalWeight V X) := by
              conv_lhs => rw [hcritXset X hXB]
          _ = setSum T2 (fun e => if e ∈ criticalEdgeX V X
                then gammaX V X lmfun * criticalWeight V X else 0) :=
              p18_setSum_filter hT2fin (fun e => e ∈ criticalEdgeX V X)
                (fun _ => gammaX V X lmfun * criticalWeight V X)
      rw [p18_setSum_congr hB1fin hstepA, p18_setSum_congr hB1fin hstepB,
        p18_setSum_fubini hB1fin hT2fin (fun (X e : Set V3) => if e ∈ criticalEdgeX V X
          then gammaX V X lmfun * criticalWeight V X else 0)]
    -- the B1 sum dominates the two remainder sums over T2
    have hQ1 : setSum T2 (fun e => setSum B1 (fun X => if e ∈ criticalEdgeX V X
          then gammaX V X lmfun * criticalWeight V X else 0))
        + setSum T2 (fun e => setSum (outr e)
            (fun X => gammaX V X lmfun * criticalWeight V X))
        + setSum T2 (fun e => setSum (cellCluster V e) (fun X => betaBumpV1 V e X)) ≥ 0 := by
      have hsplit : 0 ≤ setSum T2 (fun e => setSum B1 (fun X => if e ∈ criticalEdgeX V X
            then gammaX V X lmfun * criticalWeight V X else 0)
          + setSum (outr e) (fun X => gammaX V X lmfun * criticalWeight V X)
          + setSum (cellCluster V e) (fun X => betaBumpV1 V e X)) := by
        refine p18_setSum_nonneg hT2fin _ fun e he => ?_
        have hB1e : setSum B1 (fun X => if e ∈ criticalEdgeX V X
            then gammaX V X lmfun * criticalWeight V X else 0)
            = setSum (innr e) (fun X => gammaX V X lmfun * criticalWeight V X) := by
          have hkey : ∀ Y : Set V3, e ∈ criticalEdgeX V Y → criticalEdgeX V Y ≠ ∅ :=
            fun Y hh hcon => by rw [hcon] at hh; exact hh
          have hseteq3 : {X : Set V3 | X ∈ B1 ∧ e ∈ criticalEdgeX V X} = innr e := by
            ext Y
            show (((Y ⊆ Metric.ball 0 r ∧ mcellSet V Y) ∧ criticalEdgeX V Y ≠ ∅) ∧
                e ∈ criticalEdgeX V Y) ↔
              ((e ∈ criticalEdgeX V Y ∧ Y ∈ mcellSet V) ∧ Y ⊆ Metric.ball 0 r)
            refine ⟨fun h => ⟨⟨h.2, h.1.1.2⟩, h.1.1.1⟩,
              fun h => ⟨⟨⟨h.2, h.1.2⟩, hkey Y h.1.1⟩, h.1.1⟩⟩
          rw [← p18_setSum_filter hB1fin (fun X => e ∈ criticalEdgeX V X)
            (fun X => gammaX V X lmfun * criticalWeight V X), hseteq3]
        rw [hB1e]
        exact hcluster e he
      have h2a := p18_setSum_add hT2fin
        (fun e => setSum B1 (fun X => if e ∈ criticalEdgeX V X
          then gammaX V X lmfun * criticalWeight V X else 0))
        (fun e => setSum (outr e) (fun X => gammaX V X lmfun * criticalWeight V X))
      have h2 := p18_setSum_add hT2fin
        (fun e => setSum B1 (fun X => if e ∈ criticalEdgeX V X
          then gammaX V X lmfun * criticalWeight V X else 0)
          + setSum (outr e) (fun X => gammaX V X lmfun * criticalWeight V X))
        (fun e => setSum (cellCluster V e) (fun X => betaBumpV1 V e X))
      rw [h2a, h2]
      exact hsplit
    have hQ3split : setSum T2 (fun e => setSum (cellCluster V e)
          (fun X => betaBumpV1 V e X))
        = setSum T2 (fun e => setSum (inn8 e) (fun X => betaBumpV1 V e X))
          + setSum T2 (fun e => setSum (ann8 e) (fun X => betaBumpV1 V e X)) := by
      refine Eq.trans ?_ (p18_setSum_add hT2fin
        (fun e => setSum (inn8 e) (fun X => betaBumpV1 V e X))
        (fun e => setSum (ann8 e) (fun X => betaBumpV1 V e X))).symm
      refine p18_setSum_congr hT2fin (fun e he => ?_)
      rw [hfamunion8 e, p18_setSum_union (hinn8fin e he) (hann8fin e he) (hdisj8 e)
        (fun X => betaBumpV1 V e X)]
    -- the inner (ball r-8) beta-bump sum vanishes (BumpP4.SUM_BETA_BUMP_LEMMA)
    have hQ3in : setSum T2 (fun e => setSum (inn8 e) (fun X => betaBumpV1 V e X)) = 0 := by
      have htfin : ({X : Set V3 | X ⊆ Metric.ball 0 (r - 8) ∧ mcellSet V X} :
          Set (Set V3)).Finite := FINITE_MCELL_SET_LEMMA_2 V (r - 8) 0 hp hs
      have hstep : ∀ e : Set V3, setSum (inn8 e) (fun X => betaBumpV1 V e X)
          = setSum {X : Set V3 | X ⊆ Metric.ball 0 (r - 8) ∧ mcellSet V X}
              (fun X => if e ∈ criticalEdgeX V X then betaBumpV1 V e X else 0) := by
        intro e
        have hseteq2 : (inn8 e : Set (Set V3))
            = {X : Set V3 | X ∈ {X : Set V3 | X ⊆ Metric.ball 0 (r - 8) ∧ mcellSet V X}
                ∧ e ∈ criticalEdgeX V X} := by
          ext X
          show ((e ∈ criticalEdgeX V X ∧ X ∈ mcellSet V) ∧
              X ⊆ Metric.ball 0 (r - 8)) ↔
            ((X ⊆ Metric.ball 0 (r - 8) ∧ mcellSet V X) ∧ e ∈ criticalEdgeX V X)
          tauto
        rw [hseteq2, p18_setSum_filter htfin (fun X => e ∈ criticalEdgeX V X)
          (fun X => betaBumpV1 V e X)]
      have hzero : ∀ X ∈ {X : Set V3 | X ⊆ Metric.ball 0 (r - 8) ∧ mcellSet V X},
          setSum T2 (fun e => if e ∈ criticalEdgeX V X then betaBumpV1 V e X else 0) = 0 := by
        intro X hX
        obtain ⟨hsubt, hmX⟩ := hX
        have hXB : X ∈ B :=
          ⟨Set.Subset.trans hsubt (Metric.ball_subset_ball (by linarith)), hmX⟩
        calc setSum T2 (fun e => if e ∈ criticalEdgeX V X then betaBumpV1 V e X else 0)
            = setSum {e : Set V3 | e ∈ T2 ∧ e ∈ criticalEdgeX V X}
                (fun e => betaBumpV1 V e X) :=
              (p18_setSum_filter hT2fin (fun e => e ∈ criticalEdgeX V X)
                (fun e => betaBumpV1 V e X)).symm
          _ = setSum (criticalEdgeX V X) (fun e => betaBumpV1 V e X) := by
              conv_rhs => rw [hcritXset X hXB]
          _ = setSum (criticalEdgeX V X) (fun e => betaBump V e X) :=
              p18_setSum_congr (p18_criticalEdgeX_finite V X)
                (fun e _ => p18_betaBump_eq V e X)
          _ = 0 := BumpP4.SUM_BETA_BUMP_LEMMA V X hs hp hmX
      have hfub := p18_setSum_fubini hT2fin htfin (fun (e X : Set V3) =>
        if e ∈ criticalEdgeX V X then betaBumpV1 V e X else 0)
      simp only [hstep]
      exact hfub.trans (p18_setSum_eq_zero htfin _ hzero)
    -- ordered-pair halving bounds (p18_sum_pair_2_set + fiber count 4^3)
    have hpair' : setSum {p : V3 × V3 | p.1 ∈ T3 ∧ p.2 ∈ T3 ∧ p.1 ≠ p.2 ∧
        dist p.1 p.2 ≤ 2 * hplus} (fun _ => c2 * cc1)
        = 2 * setSum T4 (fun _ => c2 * cc1) := by
      have hp2 := p18_sum_pair_2_set (fun _ => c2 * cc1) T3 (2 * hplus) hT3fin
      simpa using hp2
    have hO4bound : setSum {p : V3 × V3 | p.1 ∈ T3 ∧ p.2 ∈ T3 ∧ p.1 ≠ p.2 ∧
        dist p.1 p.2 ≤ 2 * hplus} (fun _ => c2 * cc1)
        ≤ (64:ℝ) * (d1 * r ^ 2 * (c2 * cc1)) := by
      have hseteq : {p : V3 × V3 | p.1 ∈ T3 ∧ p.2 ∈ T3 ∧ p.1 ≠ p.2 ∧
          dist p.1 p.2 ≤ 2 * hplus}
          = {p : V3 × V3 | p ∈ T3 ×ˢ T3 ∧ (p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ 2 * hplus)} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_prod]
        tauto
      rw [hseteq, p18_setSum_filter (hT3fin.prod hT3fin)
        (fun p : V3 × V3 => p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ 2 * hplus) (fun _ => c2 * cc1),
        p18_setSum_prod hT3fin hT3fin (fun p : V3 × V3 =>
          if p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ 2 * hplus then (c2 * cc1 : ℝ) else 0)]
      have hinner : ∀ m ∈ T3,
          setSum T3 (fun n : V3 => if m ≠ n ∧ dist m n ≤ 2 * hplus
            then (c2 * cc1 : ℝ) else 0)
          ≤ (4:ℝ) ^ 3 * (c2 * cc1) := by
        intro m hm
        simp only [hT3def, Set.mem_setOf_eq] at hm
        have hfin3 : (V ∩ Metric.ball m 3).Finite :=
          (hp.finite_inter_ball (r + 3)).subset fun a ha => by
            refine ⟨ha.1, Metric.mem_ball.mpr ?_⟩
            have ha2 : dist a m < 3 := Metric.mem_ball.mp ha.2
            have hm2 : dist m 0 < r := Metric.mem_ball.mp hm.2.1
            have htri : dist a 0 ≤ dist a m + dist m 0 := dist_triangle a m 0
            linarith
        have hfin : ({n : V3 | n ∈ T3 ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : Set V3).Finite :=
          hT3fin.subset fun n hn => hn.1
        have hfil : setSum T3 (fun n : V3 => if m ≠ n ∧ dist m n ≤ 2 * hplus
            then (c2 * cc1 : ℝ) else 0)
            = setSum {n : V3 | n ∈ T3 ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)}
                (fun _ => c2 * cc1) :=
          (p18_setSum_filter hT3fin (fun n : V3 => m ≠ n ∧ dist m n ≤ 2 * hplus)
            (fun _ => c2 * cc1)).symm
        rw [hfil, p18_setSum_const hfin (c2 * cc1)]
        have hsub : ({n : V3 | n ∈ T3 ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : Set V3) ⊆
            V ∩ Metric.ball m 3 := by
          rintro n ⟨hn, -, hdle⟩
          exact ⟨hn.1, Metric.mem_ball.mpr
            (by rw [dist_comm]; exact lt_of_le_of_lt hdle p18_two_hplus_lt_three)⟩
        have hcardle : ((Nat.card {n : V3 | n ∈ T3 ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : ℕ) : ℝ)
            ≤ ((Nat.card ↥(V ∩ Metric.ball m 3) : ℕ) : ℝ) := by
          refine Nat.cast_le.mpr ?_
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_le_ncard hsub hfin3
        have h64 := BOUNDS_VGEN_klemma m V 3 (by norm_num) hp
        calc ((Nat.card {n : V3 | n ∈ T3 ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : ℕ) : ℝ)
              * (c2 * cc1)
            ≤ ((Nat.card ↥(V ∩ Metric.ball m 3) : ℕ) : ℝ) * (c2 * cc1) :=
              mul_le_mul_of_nonneg_right hcardle hXpos
          _ ≤ ((3:ℝ) + 1) ^ 3 * (c2 * cc1) := mul_le_mul_of_nonneg_right h64 hXpos
          _ ≤ (4:ℝ) ^ 3 * (c2 * cc1) := by norm_num
      have hXpos64 : (0:ℝ) ≤ (4:ℝ) ^ 3 * (c2 * cc1) := mul_nonneg (by norm_num) hXpos
      refine le_trans (p18_setSum_le hT3fin _ _ hinner) ?_
      rw [p18_setSum_const hT3fin ((4:ℝ) ^ 3 * (c2 * cc1))]
      refine le_trans (mul_le_mul_of_nonneg_right hd1r hXpos64) (le_of_eq ?_)
      ring
    have hpair'' : setSum {p : V3 × V3 | p.1 ∈ T3' ∧ p.2 ∈ T3' ∧ p.1 ≠ p.2 ∧
        dist p.1 p.2 ≤ 2 * hplus} (fun _ => c2 * cc3)
        = 2 * setSum T4' (fun _ => c2 * cc3) := by
      have hp2 := p18_sum_pair_2_set (fun _ => c2 * cc3) T3' (2 * hplus) hT3'fin
      simpa using hp2
    have hO4'bound : setSum {p : V3 × V3 | p.1 ∈ T3' ∧ p.2 ∈ T3' ∧ p.1 ≠ p.2 ∧
        dist p.1 p.2 ≤ 2 * hplus} (fun _ => c2 * cc3)
        ≤ (64:ℝ) * (d3 * r ^ 2 * (c2 * cc3)) := by
      have hseteq : {p : V3 × V3 | p.1 ∈ T3' ∧ p.2 ∈ T3' ∧ p.1 ≠ p.2 ∧
          dist p.1 p.2 ≤ 2 * hplus}
          = {p : V3 × V3 | p ∈ T3' ×ˢ T3' ∧ (p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ 2 * hplus)} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_prod]
        tauto
      rw [hseteq, p18_setSum_filter (hT3'fin.prod hT3'fin)
        (fun p : V3 × V3 => p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ 2 * hplus) (fun _ => c2 * cc3),
        p18_setSum_prod hT3'fin hT3'fin (fun p : V3 × V3 =>
          if p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ 2 * hplus then (c2 * cc3 : ℝ) else 0)]
      have hinner : ∀ m ∈ T3',
          setSum T3' (fun n : V3 => if m ≠ n ∧ dist m n ≤ 2 * hplus
            then (c2 * cc3 : ℝ) else 0)
          ≤ (4:ℝ) ^ 3 * (c2 * cc3) := by
        intro m hm
        simp only [hT3'def, Set.mem_setOf_eq] at hm
        have hfin3 : (V ∩ Metric.ball m 3).Finite :=
          (hp.finite_inter_ball (r + 3)).subset fun a ha => by
            refine ⟨ha.1, Metric.mem_ball.mpr ?_⟩
            have ha2 : dist a m < 3 := Metric.mem_ball.mp ha.2
            have hm2 : dist m 0 < r := Metric.mem_ball.mp hm.2.1
            have htri : dist a 0 ≤ dist a m + dist m 0 := dist_triangle a m 0
            linarith
        have hfin : ({n : V3 | n ∈ T3' ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : Set V3).Finite :=
          hT3'fin.subset fun n hn => hn.1
        have hfil : setSum T3' (fun n : V3 => if m ≠ n ∧ dist m n ≤ 2 * hplus
            then (c2 * cc3 : ℝ) else 0)
            = setSum {n : V3 | n ∈ T3' ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)}
                (fun _ => c2 * cc3) :=
          (p18_setSum_filter hT3'fin (fun n : V3 => m ≠ n ∧ dist m n ≤ 2 * hplus)
            (fun _ => c2 * cc3)).symm
        rw [hfil, p18_setSum_const hfin (c2 * cc3)]
        have hsub : ({n : V3 | n ∈ T3' ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : Set V3) ⊆
            V ∩ Metric.ball m 3 := by
          rintro n ⟨hn, -, hdle⟩
          exact ⟨hn.1, Metric.mem_ball.mpr
            (by rw [dist_comm]; exact lt_of_le_of_lt hdle p18_two_hplus_lt_three)⟩
        have hcardle : ((Nat.card {n : V3 | n ∈ T3' ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : ℕ) : ℝ)
            ≤ ((Nat.card ↥(V ∩ Metric.ball m 3) : ℕ) : ℝ) := by
          refine Nat.cast_le.mpr ?_
          rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_le_ncard hsub hfin3
        have h64 := BOUNDS_VGEN_klemma m V 3 (by norm_num) hp
        calc ((Nat.card {n : V3 | n ∈ T3' ∧ (m ≠ n ∧ dist m n ≤ 2 * hplus)} : ℕ) : ℝ)
              * (c2 * cc3)
            ≤ ((Nat.card ↥(V ∩ Metric.ball m 3) : ℕ) : ℝ) * (c2 * cc3) :=
              mul_le_mul_of_nonneg_right hcardle hXpos3
          _ ≤ ((3:ℝ) + 1) ^ 3 * (c2 * cc3) := mul_le_mul_of_nonneg_right h64 hXpos3
          _ ≤ (4:ℝ) ^ 3 * (c2 * cc3) := by norm_num
      have hXpos64 : (0:ℝ) ≤ (4:ℝ) ^ 3 * (c2 * cc3) := mul_nonneg (by norm_num) hXpos3
      refine le_trans (p18_setSum_le hT3'fin _ _ hinner) ?_
      rw [p18_setSum_const hT3'fin ((4:ℝ) ^ 3 * (c2 * cc3))]
      refine le_trans (mul_le_mul_of_nonneg_right hd3r hXpos64) (le_of_eq ?_)
      ring
    -- the two T2-level bounds
    have hT2Q2 : setSum T2 (fun e => setSum (outr e)
        (fun X => gammaX V X lmfun * criticalWeight V X))
        ≤ (32:ℝ) * (c2 * cc1 * d1) * r ^ 2 := by
      have hstep := p18_setSum_superset_eq hT4fin hT2fin hT4sub
        (fun e => setSum (outr e) (fun X => gammaX V X lmfun * criticalWeight V X))
        (fun e he hne4 => by
          rw [houtempty e he hne4]
          exact p18_setSum_eq_zero Set.finite_empty _
            (fun a ha => absurd ha (by simp)))
      rw [← hstep]
      refine le_trans (p18_setSum_le hT4fin _ _
        (fun e he => hQ2le e (hT4sub he))) ?_
      rw [p18_setSum_const hT4fin (c2 * cc1)]
      have hrw : (32:ℝ) * (c2 * cc1 * d1) * r ^ 2
          = 32 * (d1 * r ^ 2 * (c2 * cc1)) := by ring
      rw [hrw]
      have hA : ((Nat.card T4 : ℕ) : ℝ) * (c2 * cc1) = setSum T4 (fun _ => c2 * cc1) :=
        (p18_setSum_const hT4fin (c2 * cc1)).symm
      linarith [hA, hpair', hO4bound]
    have hT2Q3 : setSum T2 (fun e => setSum (cellCluster V e)
        (fun X => betaBumpV1 V e X)) ≤ (32:ℝ) * (c2 * cc3 * d3) * r ^ 2 := by
      rw [hQ3split, hQ3in, zero_add]
      have hstep := p18_setSum_superset_eq hT4'fin hT2fin hT4'sub
        (fun e => setSum (ann8 e) (fun X => betaBumpV1 V e X))
        (fun e he hne4 => by
          rw [hann8empty e he hne4]
          exact p18_setSum_eq_zero Set.finite_empty _
            (fun a ha => absurd ha (by simp)))
      rw [← hstep]
      refine le_trans (p18_setSum_le hT4'fin _ _
        (fun e he => hQ3outle e (hT4'sub he))) ?_
      rw [p18_setSum_const hT4'fin (c2 * cc3)]
      have hrw : (32:ℝ) * (c2 * cc3 * d3) * r ^ 2
          = 32 * (d3 * r ^ 2 * (c2 * cc3)) := by ring
      rw [hrw]
      have hA : ((Nat.card T4' : ℕ) : ℝ) * (c2 * cc3) = setSum T4' (fun _ => c2 * cc3) :=
        (p18_setSum_const hT4'fin (c2 * cc3)).symm
      linarith [hA, hpair'', hO4'bound]
    -- assembly
    have hring : ((32:ℝ) * (c2 * cc1 * d1) + (32:ℝ) * (c2 * cc3 * d3)) * r ^ 2
        = (32:ℝ) * (c2 * cc1 * d1) * r ^ 2 + (32:ℝ) * (c2 * cc3 * d3) * r ^ 2 := by ring
    rw [neg_mul, hring, hBsplit, p18_setSum_union hB0fin hB1fin hB0B1disj
      (fun X => gammaX V X lmfun)]
    have hsplit2 : setSum T2 (fun e => setSum B1 (fun X => if e ∈ criticalEdgeX V X
        then gammaX V X lmfun * criticalWeight V X else 0))
        ≥ -(32:ℝ) * (c2 * cc1 * d1) * r ^ 2
          - (32:ℝ) * (c2 * cc3 * d3) * r ^ 2 := by linarith
    linarith
  · exact absurd ⟨hs, hp⟩ hsp

/-- HOL `SUM_GAMMAX_LMFUN_ESTIMATE` (sum_gamma.hl:62-1465): proved via the
private `p18_sum_gammax_main` cluster-sum assembly. Note the DISCHARGE
convention vs PackingAuto2 concl theorems: this is only a *support lemma* for
UPFZBZM — it matches neither `UPFZBZM_concl`, `RDWKARC_concl`, `GOTCJAH_concl`
nor `TIWWFYQ_concl`, which therefore remain `sorry` in PackingAuto2.
`TSKAJXY_statement` itself is byte-identical to PackingAuto2's encoding and is
reused, not redefined. -/
theorem SUM_GAMMAX_LMFUN_ESTIMATE : SUM_GAMMAX_LMFUN_ESTIMATE_concl := by
  intro V
  have hkey : ∃ c : ℝ, saturated V → Packing V → ∀ r : ℝ, saturated V → Packing V →
      1 ≤ r → cellClusterInequality V → TSKAJXY_statement →
      c * r ^ 2 ≤ setSum {X | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
        (fun X => gammaX V X lmfun) := by
    by_cases hsp : saturated V ∧ Packing V
    · obtain ⟨c, hc⟩ := p18_sum_gammax_main V hsp.1 hsp.2
      exact ⟨c, fun _ _ r hsat' hpack' hr1 hcc hts =>
        hc r hsat' hpack' hr1 hcc hts⟩
    · exact ⟨0, fun hsat hpack _ _ hpack' _ _ _ => absurd ⟨hsat, hpack'⟩ hsp⟩
  obtain ⟨c, hc⟩ := hkey
  exact ⟨c, fun r hsat hpack hr1 hcc hts => hc hsat hpack r hsat hpack hr1 hcc hts⟩

end
end Kepler.Text
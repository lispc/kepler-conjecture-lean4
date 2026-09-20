/-
LocalAuto37 — port of `scripts/local/lunar_deform.hl` (5039 ln, module
`Lunar_deform`, Nguyen Quang Truong / T. Hales 2013; 0 defs + 48 theorems):
the MHAEYJN *deformation* bank of the Local Fan chapter.  The file proves
that a lunar (two-half) convex local fan survives a small deformation
`f : V3 → ℝ → V3` that moves only the apex `u` inside the plane
`aff {0, v, w, u}`:

  * geometry localisation kit: `aff_gt` subset/`azim` lemmas
    (`AFF_GT_SUBSET_AFFINE_HULL21`, `TOW_POINTS_IN_IMP_AFF_GT_SUBSET`,
    `COLL_IN_AFF_GT_INTER_EMPTY`, `AZIM_PI_LEMMA`, `IN_AFF_GT_IMP_AZIMEQ*`),
    the lunar two-half characterisation (`HKIRPEP_ALT`,
    `LUNAR_IMP_IN_TWO_HAFLS_PLANE`, `LOCAL_CONVEX_NOT_COLLINEAR`);
  * the `SUB_LUNAR_DEFORM_LEMMA` giant (528-1830: `Lunar` survives the
    deformation) and its `ConvexLocalFan` wrapper `MHAEYJN_CONVEX_LOCAL_FAN`;
  * the hypermap-iso kit (darts/`ff_of`/`nn_of`/`ee_of` transfer under a
    vertex bijection: `ORD_PAIRS_INJ_IMAGE`, `BIJ_AND_MAP_COMM`,
    `NODE_EDGE_COMM_LEMMA`, `HYP_ISO_LEMMAA`, `IMAGE_FACE_F`, `ITER_COMM*`,
    `HAS_THE_SAME_ORD_LEM`, `HYP_ISO_DIH2K_PRESERVED`);
  * continuity-at-`atreal` preservation kit (`CONS_IMP_CONTINUOUS_ATREAL`,
    `DISJTINCT_PROPERTY`, `CONT_ATREAL_INJ_PRESERVED`,
    `CONT_ATREAL_REAL_CONTS`, `CONTINUOUS_POS_PRES`);
  * the iterated `rho_node1` plane/cross kit (`IVS_RHO_NODE_V_IN_FF`,
    `CROSS_IN_SAME_DIRECTION`, `ITER_CROSS_SAME_DIRECTION`,
    `ITER_IN_AFF_GT_2_1`, `AZIM_PI_ITER_LOCAL_FAN`);
  * the registry conclusion `MHAEYJN`.

ALIGNMENT (twin policy): `LocalAuto34` carries `MHAEYJN_prop_p34` (the
`real_interval (a,b)` ↔ `Icc a b` rendering of appendix.hl:25), but the
LocalAuto34 olean is NOT built in this checkout (same-wave lanes are
mutually non-imported), so alignment is not reachable here.  We therefore
carry the verbatim `_p37` copy `MHAEYJN_prop_p37` with a NEEDS marker to
merge against `MHAEYJN_prop_p34` at the LocalAuto34 merge point.

Encoding (house conventions, cf. LocalAuto31/34):
- HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `(0 : V3)`; `&0` ↔ `(0:ℝ)`;
  `#` rationals ↔ exact literals; `real_interval (a,b)` ↔ `Set.Icc a b`;
  `--e` ↔ `-e`; `!`/`?` ↔ `∀`/`∃`; `x IN s` ↔ `x ∈ s`; `A SUBSET B` ↔ `A ⊆ B`;
  `IMAGE f s` ↔ `f '' s`; `~(a = b)` ↔ `a ≠ b`; `DISJOINT s t` ↔ `Disjoint s t`;
  `ITER i f x` ↔ `f^[i] x` (`Function.iterate`); `POWER n f x` likewise.
- `convex_local_fan`/`local_fan`/`lunar`/`deformation`/`interior_angle1`/
  `rho_node1`/`ivs_rho_node1` ↔ `ConvexLocalFan`/`LocalFan`/`Lunar`/
  `Deformation`/`interiorAngle1`/`rhoNode1`/`ivsRhoNode1` (LocalAuto1; the
  registry `LocalFan` is the stub `True` there, so `LocalFan`-conditioned
  statements keep the hypothesis for signature fidelity and theorems whose
  proof needs fan substance are `sorry` — see NEEDS markers).
- `aff_gt`/`aff_lt` ↔ `affGt`/`affLt` (Geom.Aff `Affsign` rendering);
  `aff {a,b}` ↔ `affineSpan ℝ ({a, b} : Set V3)`; `collinear {a,b,c}` ↔
  `Collinear ℝ ({a, b, c} : Set V3)`; `azim` ↔ `Kepler.Geom.azim`.
- `x cross y` ↔ `cross3_p37` (verbatim copy of the shared `cross3`; see the
  def comment for the PackingAuto18/PackingAuto20 `atn2PA18` conflict);
  `x dot y` ↔ `⬝ᵥ` after coercion to `Fin 3 → ℝ`; `norm` ↔ `‖·‖`.
- HOL `f continuous atreal r` ↔ `ContinuousAt f r` for point-`atreal`
  statements (LocalAuto6/14 convention).  EXCEPTION, documented: in
  `CONS_IMP_CONTINUOUS_ATREAL` the source unfolds `continuous_atreal`
  *against* the ambient `real_interval (a,b)` (its HOL proof rewrites both),
  i.e. the conclusion is continuity *within* the interval; we therefore
  render that single conclusion as `ContinuousWithinAt f t (Icc a b)`.
- `plane P` (Collect_geom) ↔ `PlaneP_p37 P` := `∃ a b c, ¬Collinear ℝ {a,b,c}
  ∧ P = affineSpan ℝ {a,b,c}`.  NEEDS: verify against the azure `plane`
  definition before merging.
- `hyp_iso f (H,HH)` (Hypermap_iso) ↔ `hypIso_p37 f H HH` := dart `BijOn` +
  commuting face/node/edge maps (shape follows the consumer lemmas of this
  file).  NEEDS: verbatim check against `hypermap_iso.hl`; the
  `hypermap (HYP (vec 0,V,E))` instances go through `hypermapOfFan`
  (Fan.lean), kept explicit as `FAN` hypotheses at the skeleton level.
- `{ITER l (rho_node1 FF) v | 0 < l /\ l < i}` ↔ `{z | ∃ l, 0 < l ∧ l < i ∧
  z = (rhoNode1 FF)^[l] v}`; `CARD V` ↔ `Set.ncard V`; `dih2k H k` ↔
  `dih2k_p2 H k` (LocalAuto2); `darts_of_hyp`/`ff_of_hyp`/`nn_of_hyp`/
  `ee_of_hyp`/`face`/`ord_pairs` ↔ the `*_p4` twins (LocalAuto4/5).
- TACTIC-HELPER NON-PORT.  The OCaml block `ATTACH`…`MAKE_FIRST_TAC`
  (source lines 33-89: `NHANH`/`PHA`/`DOWN_TAC`/`PAT_*_REWRITE_TAC`/…
  hypothesis-shuffling tactics) and the debug `els`/`bls` carry no
  mathematical content and are deliberately NOT ported; their effect is
  folded into the direct proofs below.  The mid-file `let tt = GEN_ALL …`
  bindings are HOL proof-script scoping (ISPECL instantiations inside
  tactic blocks), likewise folded.
- DISCHARGES: proved items are mechanical (real-arithmetic trivia, set/image
  bookkeeping, iterate commutation by induction, epsilon packing under a
  finite set, stub-reducing `LocalFan` conclusions).  The giants
  (`SUB_LUNAR_DEFORM_LEMMA`, `MHAEYJN_CONVEX_LOCAL_FAN`, `MHAEYJN`, the
  lunar characterisation chain and the `rho_node1` plane/cross kit) are
  `sorry` with NEEDS markers naming the blocking kit (the
  `Local_lemmas`/`Local_lemmas1` twins still carried as `sorry` in
  LocalAuto5/6, e.g. `CARD_V_TWO_HAFL_CIRCLE`, `COLL_IN_AFF_GT_TOO`,
  `LOCAL_FAN_CHARACTER_OF_RHO_NODE3`, `RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT`).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Local twin defs (`_p37` copies) -/

/-- HOL `u cross v` on `real^3` — verbatim copy of the shared
`PackingAuto18.cross3` / `TopologyFan.cross3` body.  WHY A COPY: this file
imports `LocalAuto1`, whose tree loads `PackingAuto18`; the same-wave
`LocalAuto2`/`LocalAuto9` trees load `PackingAuto20`, and the two declare
conflicting `Kepler.Text.atn2PA18` copies, so the trees cannot coexist.
NEEDS: switch to the shared `cross3` once the `atn2PA18` shadowing is merged. -/
noncomputable def cross3_p37 (a b : V3) : V3 :=
  WithLp.toLp 2 (crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ))

/-- HOL `has_orders h k` (localization.hl:24; `LocalAuto2.hasOrders_p2`
copy — LocalAuto2 is not importable here, see `cross3_p37`).
NEEDS: merge with `hasOrders_p2`. -/
def hasOrders_p37 {α : Type*} (f : α → α) (k : ℕ) : Prop :=
  (∀ i, 0 < i → i < k → ¬(f^[i] = id)) ∧ f^[k] = id

/-- HOL `dih2k H k` (localization.hl:30; `LocalAuto2.dih2k_p2` copy).
NEEDS: merge with `dih2k_p2`. -/
def dih2k_p37 {α : Type*} [DecidableEq α] (H : Hypermap α) (k : ℕ) : Prop :=
  H.darts.card = 2 * k ∧
    (∀ x ∈ (H.darts : Set α), (↑H.darts : Set α) = H.face x ∪ (H.nodeMap : α → α) '' H.face x) ∧
    hasOrders_p37 (H.faceMap : α → α) k ∧
    hasOrders_p37 (H.edgeMap : α → α) 2 ∧
    hasOrders_p37 (H.nodeMap : α → α) 2

/-! ## Geometric localisation kit (source 109-527) -/

/-- HOL `CONS_IMP_CONTINUOUS_ATREAL` (lunar_deform.hl:109).  The `atreal`
continuity is rendered *within* the ambient interval (see header): the
source proof unfolds `continuous_atreal` against `real_interval (a,b)`. -/
theorem CONS_IMP_CONTINUOUS_ATREAL_p37 {a b : ℝ} {f : ℝ → V3} {u : V3}
    (h : ∀ t ∈ Icc a b, f t = u) :
    ∀ t ∈ Icc a b, ContinuousWithinAt f (Icc a b) t := by
  intro t ht
  exact (continuous_const.continuousWithinAt).congr (fun y hy => h y hy) (h t ht)

/-- HOL `AFF_GT_SUBSET_AFFINE_HULL21` (lunar_deform.hl:127): the
`{u,v} ∪ {w}` instance of `AFF_GT_SUBSET_AFFINE_HULL`.
NEEDS: `Affsign` → affine-combination → `affineSpan` bridge (Mathlib
`mem_affineSpan_iff_eq_affineCombination` bookkeeping over the explicit
finite witness of `Affsign`). -/
theorem AFF_GT_SUBSET_AFFINE_HULL21_p37 (u v w : V3) :
    affGt {u, v} {w} ⊆ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) := by
  sorry

/-- HOL `DISJTINCT_PROPERTY` (lunar_deform.hl:131; source spelling kept):
a deformation pinning `V \\ {u}` while moving `u` continuously off them
separates `u` from `V \\ {u}` in a uniform time window. -/
theorem DISJTINCT_PROPERTY_p37 {V : Set V3} {f : V3 → ℝ → V3} {u : V3} {a b : ℝ}
    (hV : V.Finite) (hcu : ContinuousAt (f u) 0) (hu0 : f u 0 = u)
    (ha : a < 0) (hb : 0 < b)
    (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') :
    ∃ e : ℝ, 0 < e ∧ ∀ t u', -e < t ∧ t < e ∧ u' ∈ V ∧ u' ≠ u → f u t ≠ f u' t := by
  by_cases hempty : (V \ {u}).Nonempty
  · obtain ⟨s0, hs0⟩ := hempty
    haveI : Nonempty {z // z ∈ (V \ {u} : Set V3)} := ⟨⟨s0, hs0⟩⟩
    have hVd : (V \ {u} : Set V3).Finite := hV.sdiff
    obtain ⟨s, hmin⟩ := hVd.exists_min (fun z : {z // z ∈ (V \ {u} : Set V3)} => dist u z)
    have hsu : (s : V3) ≠ u := by
      intro heq
      exact s.2.2 (by rw [heq]; exact Set.mem_singleton u)
    have hsd : 0 < dist u (s : V3) := by
      have h0 : dist u (s : V3) ≠ 0 := fun hzero => hsu (dist_eq_zero.mp hzero).symm
      exact lt_of_le_of_ne (by norm_num : 0 ≤ dist u (s : V3)) (Ne.symm h0)
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ s' : ℝ, dist s' 0 < δ →
        dist (f u s') (f u 0) < dist u (s : V3) / 2 := by
      have h2 := Metric.continuousAt_iff.mp hcu (dist u (s : V3) / 2) (by linarith)
      obtain ⟨δ, hδ0, hδ⟩ := h2
      exact ⟨δ, hδ0, hδ⟩
    have hpos : 0 < min (min (-a) b) (min δ (dist u (s : V3) / 2)) :=
      lt_min (lt_min (by linarith) hb) (lt_min hδ0 (by linarith))
    refine ⟨min (min (-a) b) (min δ (dist u (s : V3) / 2)), hpos, ?_⟩
    intro t u' hcon
    obtain ⟨ht1, ht2, hmem, hne⟩ := hcon
    have hea : min (min (-a) b) (min δ (dist u (s : V3) / 2)) ≤ -a :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hebs : min (min (-a) b) (min δ (dist u (s : V3) / 2)) ≤ b :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hicc : t ∈ Icc a b := by
      have h1 : a ≤ t := by linarith
      have h2 : t ≤ b := by linarith
      exact ⟨h1, h2⟩
    have hpin' : f u' t = u' := hpin u' hmem (Ne.symm hne) t hicc
    have hpin0 : f u' 0 = u' := hpin u' hmem (Ne.symm hne) 0 ⟨by linarith, by linarith⟩
    have hts : dist t 0 < δ := by
      rw [Real.dist_0_eq_abs]
      have hab : |t| < min (min (-a) b) (min δ (dist u (s : V3) / 2)) := by
        rw [abs_lt]; exact ⟨ht1, ht2⟩
      exact lt_of_lt_of_le hab (le_trans (min_le_right _ _) (min_le_left _ _))
    have hcontr : dist (f u t) (f u 0) < dist u (s : V3) / 2 := hδ t hts
    rw [hu0] at hcontr
    intro heq
    rw [heq, hpin'] at hcontr
    rw [dist_comm u' u] at hcontr
    have h1 : dist u (s : V3) ≤ dist u u' := by
      have hsu' : u' ∈ (V \ {u} : Set V3) := ⟨hmem, hne⟩
      have := hmin ⟨u', hsu'⟩
      simpa using this
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro t u' hcon
    obtain ⟨_, _, hmem, hne⟩ := hcon
    exact absurd (⟨u', ⟨hmem, hne⟩⟩ : (V \ {u} : Set V3).Nonempty) hempty

/-- HOL `EDGE_FORM_IN_LOCAL_FAN` (lunar_deform.hl:175).  NEEDS: the fan
`E`-is-2-sets kit (`Local_lemmas1.HAS_SIZE_2_EXISTS2` path) — the registry
`LocalFan` stub carries no `E` substance. -/
theorem EDGE_FORM_IN_LOCAL_FAN_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {x : Set V3} (h : LocalFan V E FF) (hx : x ∈ E) :
    ∃ u v : V3, u ≠ v ∧ {u, v} = x := by
  sorry

/-- HOL `EDGE_IN_LOCAL_FAN_DET_RHO_NODE` (lunar_deform.hl:185).  NEEDS:
`Local_lemmas.LOFA_IN_E_IMP_IN_FF` + `Local_lemmas.DETER_RHO_NODE` twins
(still `sorry` in LocalAuto5). -/
theorem EDGE_IN_LOCAL_FAN_DET_RHO_NODE_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {x : Set V3} (h : LocalFan V E FF) (hx : x ∈ E) :
    ∃ v ∈ V, {v, rhoNode1 FF v} = x := by
  sorry

/-- HOL `TOW_POINTS_IN_IMP_AFF_GT_SUBSET` (lunar_deform.hl:209; source
spelling kept).  NEEDS: the `AFF_GT_2_1`/`AFF_GT_1_2` affine-coordinate
decomposition twins (positive-coefficient rewriting kit). -/
theorem TOW_POINTS_IN_IMP_AFF_GT_SUBSET_p37 {x u v a b : V3}
    (_h1 : Disjoint ({x, u} : Set V3) ({v} : Set V3))
    (_ha : a ∈ affGt {x, u} {v}) (_hb : b ∈ affGt {x, u} {v})
    (_h2 : Disjoint ({x} : Set V3) ({a, b} : Set V3)) :
    affGt {x} {a, b} ⊆ affGt {x, u} {v} := by
  sorry

/-- HOL `REAL_LT_MUL12` (lunar_deform.hl:251). -/
theorem REAL_LT_MUL12_p37 {a b : ℝ} (hb : 0 < b) (ha : a < 0) : a * b < 0 :=
  mul_neg_of_neg_of_pos ha hb

/-- HOL `COLL_IN_AFF_GT_INTER_EMPTY` (lunar_deform.hl:259).  NEEDS:
`Local_lemmas.COLL_IN_AFF_GT_TOO` + `Fan.th3a` + the affine-coordinate
decomposition kit. -/
theorem COLL_IN_AFF_GT_INTER_EMPTY_p37 {a b x u : V3}
    (hnc : ¬Collinear ℝ ({a, b, x} : Set V3)) (hu : u ∈ affGt {a, b} {x}) :
    affGt {a, b} {x} ∩ affLt {a} {u} = ∅ := by
  sorry

/-- HOL `HKIRPEP_ALT` (lunar_deform.hl:316): the lunar two-half circle
characterisation, `Local_lemmas.HKIRPEP` re-pruned for the deformation
file.  NEEDS: `Local_lemmas1.CARD_V_TWO_HAFL_CIRCLE` (still `sorry` in
LocalAuto6). -/
theorem HKIRPEP_ALT_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} (_h : ConvexLocalFan V E FF) (_hl : Lunar v w V E) :
    (∀ u ∈ V \ {v, w}, interiorAngle1 0 FF u = Real.pi) ∧
      0 < interiorAngle1 0 FF v ∧
      interiorAngle1 0 FF v ≤ Real.pi ∧
      interiorAngle1 0 FF v = interiorAngle1 0 FF w ∧
      ∃ i j : ℕ, i + j = Set.ncard V ∧ i < Set.ncard V ∧ i ≠ 0 ∧ i ≠ 1 ∧
        w = (rhoNode1 FF)^[i] v ∧
        {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} =
          affGt {0, v} {rhoNode1 FF v} ∩ V ∧
        j < Set.ncard V ∧ j ≠ 0 ∧ j ≠ 1 ∧
        v = (rhoNode1 FF)^[j] w ∧
        {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} =
          affGt {0, v} {ivsRhoNode1 FF v} ∩ V := by
  sorry

/-- HOL `LUNAR_IMP_IN_TWO_HAFLS_PLANE` (lunar_deform.hl:358).  NEEDS:
`HKIRPEP_ALT` + `Local_lemmas.CVX_LO_IMP_LO`. -/
theorem LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3} (_h : ConvexLocalFan V E FF)
    (_hl : Lunar v w V E) :
    ∀ u ∈ V, u ≠ v → u ≠ w →
      u ∈ affGt {0, v} {rhoNode1 FF v} ∨ u ∈ affGt {0, v} {ivsRhoNode1 FF v} := by
  sorry

/-- HOL `IN_CONV0_IMP_AFF_EQ1` (lunar_deform.hl:434).  The twin
`Local_lemmas.IN_CONV0_IMP_AFF_EQ` lives in the unbuilt LocalAuto5, so
`conv0 {x, y}` is rendered as Mathlib `openSegment ℝ x y` (open segment;
`conv0` in the azure tree is `open_segment` per Polytope.lean head note)
and the two-span equality is proved directly.
NEEDS: re-align with `conv0_p2`/`IN_CONV0_IMP_AFF_EQ` at the LocalAuto5
merge point. -/
theorem IN_CONV0_IMP_AFF_EQ1_p37 {x y a : V3} (ha : a ∈ openSegment ℝ x y) :
    (affineSpan ℝ ({a, x} : Set V3) : Set V3) = (affineSpan ℝ ({a, y} : Set V3) : Set V3) := by
  obtain ⟨p, q, hp, hq, hpq, hab⟩ := ha
  have hq1 : q = 1 - p := by linarith
  have hxmem : x ∈ (affineSpan ℝ ({a, y} : Set V3) : Set V3) := by
    have hx0 : x -ᵥ a = q • (x - y) := by
      rw [vsub_eq_sub, ← hab, hq1]
      module
    have hy0 : y -ᵥ a = p • (y - x) := by
      rw [vsub_eq_sub, ← hab, hq1]
      module
    have hp0 : p ≠ 0 := ne_of_gt hp
    have hcancel : (-q / p) * p = -q := by field_simp
    have hv : x -ᵥ a = (-q / p) • (y -ᵥ a) := by
      rw [hx0, hy0, smul_smul, hcancel]
      module
    have h1 : x = AffineMap.lineMap a y (-q / p) := by
      rw [AffineMap.lineMap_apply, ← hv, vsub_vadd]
    rw [h1]
    exact AffineMap.lineMap_mem_affineSpan_pair (-q / p) a y
  have hymem : y ∈ (affineSpan ℝ ({a, x} : Set V3) : Set V3) := by
    have hx2 : a -ᵥ x = q • (y - x) := by
      rw [vsub_eq_sub, ← hab, hq1]
      module
    have hcancel2 : 1 / q * q = 1 := by field_simp
    have hv2 : y -ᵥ x = (1 / q) • (a -ᵥ x) := by
      rw [hx2, smul_smul, hcancel2, vsub_eq_sub]
      module
    have h1 : y = AffineMap.lineMap x a (1 / q) := by
      rw [AffineMap.lineMap_apply, ← hv2, vsub_vadd]
    have h3 := AffineMap.lineMap_mem_affineSpan_pair (1 / q) x a
    rw [show ({x, a} : Set V3) = {a, x} by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h3
    rw [h1]
    exact h3
  have hsp : affineSpan ℝ ({a, x} : Set V3) ≤ affineSpan ℝ ({a, y} : Set V3) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan (k := ℝ) (Set.mem_insert _ _)) hxmem
  have hsp' : affineSpan ℝ ({a, y} : Set V3) ≤ affineSpan ℝ ({a, x} : Set V3) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan (k := ℝ) (Set.mem_insert _ _)) hymem
  exact le_antisymm hsp hsp'

/-- HOL `AFF_LT_SUBSET_AFF11` (lunar_deform.hl:444).  NEEDS: the
`AFF_LT_1_1` + `Collect_geom.AFF_2POINTS_INTERPRET` affine-coordinate
twins. -/
theorem AFF_LT_SUBSET_AFF11_p37 {a b : V3} (_h : Disjoint ({a} : Set V3) ({b} : Set V3)) :
    affLt {a} {b} ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := by
  sorry

/-- HOL `AZIM_PI_LEMMA` (lunar_deform.hl:459).  NEEDS:
`Local_lemmas.COLL_IN_AFF_GT_AFF_GT_EQ`/`COLL_IN_AFF_GT_TOO` +
`AFF_LT_MONO_LEFT` kit. -/
theorem AZIM_PI_LEMMA_p37 {u v x y a : V3} {s : Set V3}
    (_h1 : ¬(affGt {u} s ∩ affLt {u} {a} = ∅))
    (_h2 : affGt {u} s ⊆ affGt {u, v} {y})
    (_h3 : a ∈ affGt {u, v} {x})
    (_h4 : ¬Collinear ℝ ({u, v, x} : Set V3))
    (_h5 : ¬Collinear ℝ ({u, v, y} : Set V3)) :
    azim u v x y = Real.pi := by
  sorry

/-! ## The SUB_LUNAR_DEFORM_LEMMA giant (source 528-1830) -/

/-- HOL `SUB_LUNAR_DEFORM_LEMMA` (lunar_deform.hl:528): the lunar
`Lunar` conclusion survives the pinned deformation.  GIANT (sorry):
needs the `Local_lemmas.HKIRPEP` + azim/cross iteration kit below. -/
theorem SUB_LUNAR_DEFORM_LEMMA_p37 {a b : ℝ} {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → ℝ → V3} {u v w : V3}
    (_hV : V.Finite) (_hcf : ConvexLocalFan V E FF) (_hl : Lunar v w V E)
    (_hE : ∀ x ∈ E, x ⊆ V) (_hu0 : f u 0 = u) (_hcu : ContinuousAt (f u) 0)
    (_hang : interiorAngle1 0 FF v < Real.pi) (_ha : a < 0) (_hb : 0 < b)
    (_hu : u ∈ V) (_hv : u ≠ v) (_hw : u ≠ w)
    (_hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E) := by
  sorry

/-! ## The local-fan / hypermap-iso kit (source 1836-3160) -/

/-- HOL `LOCAL_FAN_SET_E` (lunar_deform.hl:1836).  NEEDS: fan substance
(`Local_lemmas1.LOCAL_RHO_NODE_PAIR_E` + `EDGE_IN_LOCAL_FAN_DET_RHO_NODE`);
the registry `LocalFan` stub carries no `E` data. -/
theorem LOCAL_FAN_SET_E_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_h : LocalFan V E FF) :
    {p : Set V3 | ∃ v ∈ V, p = {v, rhoNode1 FF v}} = E := by
  sorry

/-- HOL `LOCAL_FAN_FACE_FF` (lunar_deform.hl:1856).  NEEDS:
`Local_lemmas.LOCAL_FAN_RHO_NODE_PROS`/`PROS2` twins. -/
theorem LOCAL_FAN_FACE_FF_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_h : LocalFan V E FF) :
    {p : V3 × V3 | ∃ v ∈ V, p = (v, rhoNode1 FF v)} = FF := by
  sorry

/-- HOL `ORD_PAIRS_INJ_IMAGE` (lunar_deform.hl:1881): `ord_pairs` commutes
with a piecewise-injective vertex map. -/
theorem ORD_PAIRS_INJ_IMAGE_p37 {E : Set (Set V3)} {f : V3 → V3}
    (h : ∀ s ∈ E, Set.InjOn f s) :
    ordPairs_p4 ((fun s => f '' s) '' E) = (fun p => (f p.1, f p.2)) '' ordPairs_p4 E := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hsE, hseq⟩ := hp
    have hseq' : (f '' s : Set V3) = {p.1, p.2} := hseq
    have h1 : p.1 ∈ (f '' s : Set V3) := by rw [hseq']; simp
    have h2 : p.2 ∈ (f '' s : Set V3) := by rw [hseq']; simp
    obtain ⟨x, hxs, hx⟩ := h1
    obtain ⟨y, hys, hy⟩ := h2
    have hinj : Set.InjOn f s := h s hsE
    have hsset : s = {x, y} := by
      refine Set.Subset.antisymm ?_ ?_
      · intro z hz
        have hz0 : f z ∈ (f '' s : Set V3) := ⟨z, hz, rfl⟩
        have hz' : f z ∈ ({p.1, p.2} : Set V3) := by rwa [hseq'] at hz0
        rcases Set.mem_insert_iff.mp hz' with he | he
        · left; exact (hinj hxs hz (hx.trans he.symm)).symm
        · right; exact (hinj hys hz (hy.trans he.symm)).symm
      · intro z hz
        rcases Set.mem_insert_iff.mp hz with he | he
        · rw [he]; exact hxs
        · rw [he]; exact hys
    refine ⟨(x, y), ?_, ?_⟩
    · exact show {x, y} ∈ E from hsset ▸ hsE
    · rw [Prod.mk.injEq]; exact ⟨hx, hy⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨{d.1, d.2}, hd, ?_⟩
    show f '' {d.1, d.2} = {f d.1, f d.2}
    rw [Set.image_insert_eq, Set.image_singleton]

/-- HOL `SET2_DETER` (lunar_deform.hl:1920): a two-point set is determined
by any two distinct members. -/
theorem SET2_DETER_p37 {x y a b : V3} {s : Set V3} (hs : s = {x, y}) (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  subst hs
  ext z
  constructor <;> intro hz <;>
    rcases Set.mem_insert_iff.mp hz with rfl | rfl <;>
    rcases Set.mem_insert_iff.mp ha with rfl | rfl <;>
    rcases Set.mem_insert_iff.mp hb with rfl | rfl <;> simp_all

/-- HOL `INJ_IMP_BIJ_IMAGE` (lunar_deform.hl:1929). -/
theorem INJ_IMP_BIJ_IMAGE_p37 {f : V3 → V3} {S S' : Set V3}
    (h : Set.InjOn f S) : Set.BijOn f S (f '' S) :=
  ⟨Set.mapsTo_image f S, h, Set.surjOn_image f S⟩

/-- HOL `BIJ_AND_MAP_COMM` (lunar_deform.hl:1938): the dart/`ff_of` transfer
kit.  NEEDS: `Wrgcvdr_cizmrrh.ELMS_OF_HYPERMAP_HYP` + the local-fan
`hyp_iso` unfolding kit. -/
theorem BIJ_AND_MAP_COMM_p37 {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3} {ff : V3 × V3 → V3 × V3}
    (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
    (_hE : (fun s => f '' s) '' E = E') (_hfan' : Fan.FAN 0 V' E')
    (_hff : (fun p => (f p.1, f p.2)) = ff) :
    Set.BijOn ff (dartsOfHyp_p4 E V) (dartsOfHyp_p4 E' V') ∧
      (∀ x ∈ dartsOfHyp_p4 E V,
        ffOfHyp_p4 0 V' E' (ff x) = ff (ffOfHyp_p4 0 V E x)) := by
  sorry

/-- HOL `NODE_EDGE_COMM_LEMMA` (lunar_deform.hl:2308): `nn_of`/`ee_of`
commutation under the dart map.  NEEDS: same kit as `BIJ_AND_MAP_COMM_p37`. -/
theorem NODE_EDGE_COMM_LEMMA_p37 {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3} {ff : V3 × V3 → V3 × V3}
    (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
    (_hE : (fun s => f '' s) '' E = E') (_hfan' : Fan.FAN 0 V' E')
    (_hff : (fun p => (f p.1, f p.2)) = ff) :
    ∀ x ∈ dartsOfHyp_p4 E V,
      nnOfHyp_p4 0 V' E' (ff x) = ff (nnOfHyp_p4 0 V E x) ∧
      eeOfHyp_p4 0 V' E' (ff x) = ff (eeOfHyp_p4 0 V E x) := by
  sorry

/-- HOL `hyp_iso f (H,HH)` (Hypermap_iso): dart bijection commuting with the
face/node/edge maps.  Shape reconstructed from this file's consumer lemmas.
NEEDS: verbatim check against `hypermap_iso.hl`. -/
def hypIso_p37 {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (H : Hypermap α) (HH : Hypermap β) : Prop :=
  Set.BijOn f (H.darts : Set α) (HH.darts : Set β) ∧
    (∀ p ∈ (H.darts : Set α), (HH.faceMap : β → β) (f p) = f ((H.faceMap : α → α) p)) ∧
    (∀ p ∈ (H.darts : Set α), (HH.nodeMap : β → β) (f p) = f ((H.nodeMap : α → α) p)) ∧
    (∀ p ∈ (H.darts : Set α), (HH.edgeMap : β → β) (f p) = f ((H.edgeMap : α → α) p))

/-- HOL `HYP_ISO_LEMMAA` (lunar_deform.hl:2612): the `HYP`-hypermaps of a
vertex-bijective fan pair are `hyp_iso`.  NEEDS:
`ELMS_OF_HYPERMAP_HYP` kit + `dih2k` card transfer. -/
theorem HYP_ISO_LEMMAA_p37 {V V' : Set V3} {E E' : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → V3}
    (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
    (_hE : (fun s => f '' s) '' E = E') (_hfan : Fan.FAN 0 V E)
    (_hfan' : Fan.FAN 0 V' E') :
    hypIso_p37 (fun (p : V3 × V3) => (f p.1, f p.2)) (Fan.hypermapOfFan 0 V E _hfan)
      (Fan.hypermapOfFan 0 V' E' _hfan') := by
  sorry

/-- Iterate of the face map stays on the dart set (helper for
`POWER_COMM_p37`/`IMAGE_FACE_F_p37`). -/
private theorem faceMap_mem_iter_p37 {α : Type*} [DecidableEq α] (H : Hypermap α)
    (p : α) (hp : p ∈ (H.darts : Set α)) (n : ℕ) :
    ((H.faceMap : α → α))^[n] p ∈ (H.darts : Set α) := by
  have hstep : ∀ q ∈ (H.darts : Set α), ((H.faceMap : α → α)) q ∈ (H.darts : Set α) := by
    intro q hq
    by_contra hnot
    have h1 : ((H.faceMap : α → α)) ((H.faceMap : α → α) q) = ((H.faceMap : α → α)) q :=
      H.faceMap_permutes _ (Finset.mem_coe.not.mp hnot)
    have h2 : ((H.faceMap : α → α)) q = q := Equiv.injective _ h1
    exact hnot (by rw [h2]; exact hq)
  induction n with
  | zero => simpa using hp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih

/-- HOL `POWER_COMM` (lunar_deform.hl:2817; source is a spec'd instance of
`Hypermap_iso.power_comm`): face-map iterates commute with the dart map. -/
theorem POWER_COMM_p37 {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {H : Hypermap α} {HH : Hypermap β} (hiso : hypIso_p37 f H HH)
    (x : α) (hx : x ∈ (H.darts : Set α)) (n : ℕ) :
    (HH.faceMap : β → β)^[n] (f x) = f ((H.faceMap : α → α)^[n] x) := by
  have key : ∀ (m : ℕ) (q : α), q ∈ (H.darts : Set α) →
      (HH.faceMap : β → β)^[m] (f q) = f ((H.faceMap : α → α)^[m] q) := by
    intro m
    induction m with
    | zero => intro q _; simp
    | succ m ih =>
        intro q hq
        have hqm : ((H.faceMap : α → α)^[m]) q ∈ (H.darts : Set α) :=
          faceMap_mem_iter_p37 H q hq m
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih q hq,
          hiso.2.1 _ hqm]
  exact key n x hx

/-- HOL `ITER_COMM` (lunar_deform.hl:2820; the `POWER_TO_ITER` form of
`POWER_COMM`): function iterates commute with a conjugation. -/
theorem ITER_COMM_p37 {α β : Type*} {h : α → α} {k : β → β} {f : α → β}
    (hcomm : ∀ x, k (f x) = f (h x)) (x : α) (n : ℕ) :
    k^[n] (f x) = f (h^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hcomm]

/-- HOL `IMAGE_FACE_F` (lunar_deform.hl:2826): faces (`Hypermap.face`, the
face-map orbit) are carried to faces by a hypermap isomorphism. -/
theorem IMAGE_FACE_F_p37 {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {H : Hypermap α} {HH : Hypermap β} (hiso : hypIso_p37 f H HH)
    (p : α) (hp : p ∈ (H.darts : Set α)) :
    f '' (H.face p) = HH.face (f p) := by
  have key : ∀ (m : ℕ) (q : α), q ∈ (H.darts : Set α) →
      ((HH.faceMap : β → β))^[m] (f q) = f (((H.faceMap : α → α))^[m] q) :=
    fun m q hq => POWER_COMM_p37 hiso q hq m
  have hcoe : ∀ (m : ℕ) (q : α), ((H.faceMap ^ m) q) = ((H.faceMap : α → α))^[m] q :=
    fun m q => by rw [Equiv.Perm.coe_pow]
  have hcoe2 : ∀ (m : ℕ) (q : β), ((HH.faceMap ^ m) q) = ((HH.faceMap : β → β))^[m] q :=
    fun m q => by rw [Equiv.Perm.coe_pow]
  ext z
  constructor
  · rintro ⟨y, ymem, rfl⟩
    obtain ⟨m, hm⟩ := ymem
    have hz : ((HH.faceMap : β → β))^[m] (f p) = f y := by
      rw [key m p hp, ← hcoe, hm]
    exact ⟨m, hz⟩
  · intro hmem
    obtain ⟨m, hm⟩ := hmem
    refine ⟨(H.faceMap ^ m) p, ⟨⟨m, rfl⟩, ?_⟩⟩
    rw [hcoe, ← key m p hp, ← hcoe2]
    exact hm

/-- HOL `AUTOMAP_IMP_ALL_ITER_IN2` (lunar_deform.hl:2844): an invariant set
absorbs all iterates. -/
theorem AUTOMAP_IMP_ALL_ITER_IN2_p37 {α : Type*} {f : α → α} {W : Set α}
    {p : α} {N : ℕ} (hp : p ∈ W) (hf : ∀ x ∈ W, f x ∈ W) : f^[N] p ∈ W := by
  induction N with
  | zero => simpa using hp
  | succ n ih => simpa [Function.iterate_succ_apply'] using hf (f^[n] p) ih

/-- HOL `ITER_COMM_RESTRICTED` (lunar_deform.hl:2849): iterate commutation
with membership invariants on both sides. -/
theorem ITER_COMM_RESTRICTED_p37 {α β : Type*} {V : Set α} {V' : Set β}
    {f : α → β} {h : α → α} {g : β → β}
    (hf : ∀ x ∈ V, f x ∈ V') (hh : ∀ x, h x ∈ V ↔ x ∈ V)
    (_hg : ∀ y, g y ∈ V' ↔ y ∈ V')
    (hcomm : ∀ x ∈ V, f (h x) = g (f x)) (x : α) (hx : x ∈ V) (n : ℕ) :
    f (h^[n] x) = g^[n] (f x) := by
  have hinv : ∀ m, h^[m] x ∈ V := by
    intro m
    induction m with
    | zero =>
        simp only [Function.iterate_zero, id_eq]
        exact hx
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (hh _).mpr ih
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        hcomm (h^[m] x) (hinv m), ih]

/-- HOL `HAS_THE_SAME_ORD_LEM` (lunar_deform.hl:2871): the order of a
map is preserved under conjugation by a bijection.  NEEDS: iterate
conjugation + minimality transfer. -/
theorem HAS_THE_SAME_ORD_LEM_p37 {α β : Type*} {V : Set α} {V' : Set β}
    {h : α → α} {g : β → β} {f : α → β} {k : ℕ}
    (_h1 : ∀ x ∉ V, h x = x) (_h2 : ∀ y ∉ V', g y = y)
    (_hbij : Set.BijOn f V V') (_h3 : ∀ x, h x ∈ V ↔ x ∈ V)
    (_h4 : ∀ y, g y ∈ V' ↔ y ∈ V')
    (_h5 : ∀ x ∈ V, f (h x) = g (f x)) (_h6 : hasOrders_p37 h k) :
    hasOrders_p37 g k := by
  sorry

/-- HOL `COMM_THEN_IMAGE_IMAGE_EQ` (lunar_deform.hl:2926). -/
theorem COMM_THEN_IMAGE_IMAGE_EQ_p37 {S A : Set V3} {f g h : V3 → V3}
    (hcomm : ∀ x ∈ S, f (g x) = h (f x)) (hA : A ⊆ S) :
    f '' (g '' A) = h '' (f '' A) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun a ha => hcomm a (hA ha)

/-- HOL `IN_DART_PRESERVED` (lunar_deform.hl:2931): dart-closedness of the
three maps, stated over the proof-carrying `Hypermap` structure. -/
theorem IN_DART_PRESERVED_p37 {α : Type*} [DecidableEq α] (H : Hypermap α)
    (h1 : ∀ x, (H.faceMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α))
    (h2 : ∀ x, (H.nodeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α))
    (h3 : ∀ x, (H.edgeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) :
    (∀ x, (H.faceMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) ∧
      (∀ x, (H.nodeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) ∧
      (∀ x, (H.edgeMap : α → α) x ∈ (H.darts : Set α) ↔ x ∈ (H.darts : Set α)) :=
  ⟨h1, h2, h3⟩

/-- HOL `HYP_ISO_DIH2K_PRESERVED` (lunar_deform.hl:2937): `dih2k` transfers
along a hypermap isomorphism.  NEEDS: `iso_components` + card/face kit. -/
theorem HYP_ISO_DIH2K_PRESERVED_p37 {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {HH : Hypermap β} {f : α → β} {k : ℕ}
    (_hfin : (H.darts : Set α).Finite) (_hd : dih2k_p37 H k)
    (_hiso : hypIso_p37 f H HH) :
    dih2k_p37 HH k := by
  sorry

/-! ## Continuity preservation, the cross/plane kit, and MHAEYJN
(source 3073-5039) -/

/-- HOL `XRECQNS_UPDATE` (lunar_deform.hl:3073).  The `local_fan` conclusion
reduces to the registry stub `LocalFan = True` (LocalAuto1), so the
existence claim is witnessed by an arbitrary window; the substantive
content (the `Deformation.XRECQNS` fan transfer) is deferred with the real
fan kit. -/
theorem XRECQNS_UPDATE_p37 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {f : V3 → ℝ → V3} {a b : ℝ} (_hd : Deformation f V a b) (_hl : LocalFan V E FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      LocalFan ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E)
        ((fun p => (f p.1 t, f p.2 t)) '' FF) :=
  ⟨1, by norm_num, fun _ _ => trivial⟩

/-- HOL `NORM_CROSS_LE` (lunar_deform.hl:3200): `|u cross v| <= |u| |v|`
(via Mathlib's sin-of-angle form of the cross-product norm). -/
theorem NORM_CROSS_LE_p37 (u w : V3) : ‖cross3_p37 u w‖ ≤ ‖u‖ * ‖w‖ := by
  rw [cross3_p37, InnerProductGeometry.norm_toLp_symm_crossProduct]
  simp only [WithLp.toLp_ofLp]
  calc ‖u‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle u w)
      ≤ ‖u‖ * ‖w‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one (InnerProductGeometry.angle u w))
          (mul_nonneg (norm_nonneg u) (norm_nonneg w))
    _ = ‖u‖ * ‖w‖ := by rw [mul_one]

/-- HOL `CONT_ATREAL_INJ_PRESERVED` (lunar_deform.hl:3043).  NEEDS: the
`Local_lemmas1.CONTINUOUS_ATREAL_INJ_PRESERVED` twin (unbuilt LocalAuto6,
itself `sorry` there). -/
theorem CONT_ATREAL_INJ_PRESERVED_p37 {V : Set V3} {ff : V3 → ℝ → V3} {r : ℝ}
    (_hV : V.Finite) (_hc : ∀ v ∈ V, ContinuousAt (ff v) r)
    (_hinj : Set.InjOn (fun v => ff v r) V) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t - r| < e →
      Set.InjOn (fun v => ff v t) V := by
  sorry

/-- HOL `INJ_BIJ_IMAGE` (lunar_deform.hl:3066). -/
theorem INJ_BIJ_IMAGE_p37 {f : V3 → V3} {S S' A : Set V3}
    (h : Set.InjOn f S) (hA : A ⊆ S) : Set.BijOn f A (f '' A) :=
  ⟨Set.mapsTo_image f A, h.mono hA, Set.surjOn_image f A⟩

/-- HOL `CONT_ATREAL_REAL_CONTS` (lunar_deform.hl:3214): post-composing with
`cross _ y` and a fixed dot product keeps continuity. -/
theorem CONT_ATREAL_REAL_CONTS_p37 {f : ℝ → V3} {r : ℝ} {x y : V3}
    (h : ContinuousAt f r) :
    ContinuousAt
      (fun s => ((cross3_p37 (f s) y : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((cross3_p37 x y : V3) : Fin 3 → ℝ)) r := by
  have hcross : Continuous fun w : Fin 3 → ℝ => crossProduct w ((y : V3) : Fin 3 → ℝ) :=
    LinearMap.continuous_of_finiteDimensional (LinearMap.flip crossProduct ((y : V3) : Fin 3 → ℝ))
  have h2 : Continuous fun z : V3 => ((z : V3) : Fin 3 → ℝ) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)
  have h3 : Continuous fun w : Fin 3 → ℝ => WithLp.toLp 2 w :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  have hmidG : Continuous (fun z : V3 => cross3_p37 z y) :=
    Continuous.comp h3 (hcross.comp h2)
  have hstep : Continuous (fun z : V3 => ((cross3_p37 z y : V3) : Fin 3 → ℝ)) :=
    Continuous.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)) hmidG
  have h1 : ContinuousAt (fun s : ℝ => ((cross3_p37 (f s) y : V3) : Fin 3 → ℝ)) r :=
    (hstep.continuousAt).comp h
  have hfun : Continuous fun w : Fin 3 → ℝ =>
      w ⬝ᵥ ((cross3_p37 x y : V3) : Fin 3 → ℝ) := by
    unfold dotProduct
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).mul continuous_const)
  exact hfun.continuousAt.comp h1

/-- HOL `CONTINUOUS_POS_PRES` (lunar_deform.hl:3288).  NEEDS: the
coefficient-extraction kit (`CONT_ATREAL_REAL_CONTS` numeric margins +
`Collect_geom` affine representation). -/
theorem CONTINUOUS_POS_PRES_p37 {x y : V3} {a b r : ℝ} {f : ℝ → V3}
    (_hnc : ¬Collinear ℝ ({x, y, (0 : V3)} : Set V3)) (_hab : f r = a • x + b • y)
    (_h0 : 0 < a) (_hc : ContinuousAt f r) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → ∀ t1 t2 : ℝ,
      f (r + t) = t1 • x + t2 • y → 0 < t1 := by
  sorry

/-- HOL `IVS_RHO_NODE_V_IN_FF` (lunar_deform.hl:3334).  NEEDS:
`Local_lemmas.LOCAL_FAN_RHO_NODE_PROS2` + `Local_lemmas1.LOCAL_FAN_IVS_IN_V`
twins (fan substance beyond the registry stub). -/
theorem IVS_RHO_NODE_V_IN_FF_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (_h : LocalFan V E FF) (hv : v ∈ V) :
    (ivsRhoNode1 FF v, v) ∈ FF := by
  sorry

/-- HOL `IN_AFF_GT_IMP_AZIMEQ` (lunar_deform.hl:3348): `azim` is constant
along `aff_gt {u,v} {y}` rays.  NEEDS: `AZIM_DEGENERATE` + the
`aff_gt`-ray `azim` invariance kit. -/
theorem IN_AFF_GT_IMP_AZIMEQ_p37 {u v w x y : V3}
    (_hx : x ∈ affGt {u, v} {y}) : azim u v w x = azim u v w y := by
  sorry

/-- HOL `IN_AFF_GT_IMP_AZIMEQ2` (lunar_deform.hl:3384). -/
theorem IN_AFF_GT_IMP_AZIMEQ2_p37 {u v x y : V3} (hx : x ∈ affGt {u, v} {y})
    (w : V3) : azim u v w x = azim u v w y :=
  IN_AFF_GT_IMP_AZIMEQ_p37 hx

/-- HOL `plane P` (Collect_geom): `P` is the affine hull of three
non-collinear points.  NEEDS: verbatim check against the azure `plane`
definition before merging. -/
def PlaneP_p37 (P : Set V3) : Prop :=
  ∃ a b c : V3, ¬Collinear ℝ ({a, b, c} : Set V3) ∧ P = affineSpan ℝ ({a, b, c} : Set V3)

/-- HOL `CROSS_IN_SAME_DIRECTION` (lunar_deform.hl:3389): consecutive
`rho_node1` crosses point along the initial cross direction.
NEEDS: `Local_lemmas.RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT`. -/
theorem CROSS_IN_SAME_DIRECTION_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3} {e : V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P)
    (_he : cross3_p37 v (rhoNode1 FF v) = e) :
    ∀ i < l, ∃ k : ℝ, 0 < k ∧
      cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) = k • e := by
  sorry

/-- HOL `ITER_CROSS_SAME_DIRECTION` (lunar_deform.hl:3461): all consecutive
crosses are positive multiples of one another.  NEEDS:
`CROSS_IN_SAME_DIRECTION_p37` + division algebra. -/
theorem ITER_CROSS_SAME_DIRECTION_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P) :
    ∀ i j, i < l → j < l → ∃ k : ℝ, 0 < k ∧
      cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) =
        k • (cross3_p37 ((rhoNode1 FF)^[j] v) ((rhoNode1 FF)^[j + 1] v)) := by
  sorry

/-- HOL `ITER_IN_AFF_GT_2_1` (lunar_deform.hl:3486).  NEEDS:
`Local_lemmas.LOCAL_FAN_CHARACTER_OF_RHO_NODE3`. -/
theorem ITER_IN_AFF_GT_2_1_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P) :
    ∀ i < l - 1,
      (rhoNode1 FF)^[i + 2] v ∈
        affLt {0, (rhoNode1 FF)^[i + 1] v} {(rhoNode1 FF)^[i] v} := by
  sorry

/-- HOL `AZIM_PI_ITER_LOCAL_FAN` (lunar_deform.hl:3589).  NEEDS:
`ITER_IN_AFF_GT_2_1_p37` + `AZIM_PI_LEMMA_p37`. -/
theorem AZIM_PI_ITER_LOCAL_FAN_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (_hlf : LocalFan V E FF) (_hv : v ∈ V)
    (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
    (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P) :
    ∀ i < l - 1,
      azim 0 ((rhoNode1 FF)^[i + 1] v) ((rhoNode1 FF)^[i] v)
        ((rhoNode1 FF)^[i + 2] v) = Real.pi := by
  sorry

/-- HOL `LOCAL_CONVEX_NOT_COLLINEAR` (lunar_deform.hl:3616).  NEEDS:
`LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37` + `Local_lemmas.CVX_LO_IMP_LO`. -/
theorem LOCAL_CONVEX_NOT_COLLINEAR_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3}
    (_h : ConvexLocalFan V E FF) (_hl : Lunar v w V E) :
    ∀ u ∈ V, u ≠ v → u ≠ w → ¬Collinear ℝ ({0, v, u} : Set V3) := by
  sorry

/-- HOL `LOCAL_FAN_RHO_NODE_PROS2` (lunar_deform.hl:3633).  NEEDS:
`Local_lemmas.LOCAL_FAN_RHO_NODE_PROS` (fan substance). -/
theorem LOCAL_FAN_RHO_NODE_PROS2_p37 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (_h : LocalFan V E FF) :
    ∀ x ∈ V, (x, rhoNode1 FF x) ∈ FF := by
  sorry

/-- HOL `MHAEYJN_CONVEX_LOCAL_FAN` (lunar_deform.hl:3644): the
`ConvexLocalFan` conclusion of MHAEYJN without the lunar conjunct.
GIANT (sorry): combines `SUB_LUNAR_DEFORM_LEMMA_p37` with the
`XRECQNS_UPDATE` fan-transfer kit (`Wrgcvdr_cizmrrh.LOCAL_FAN_IMP_FAN`,
`UNIONS_SUBSET`, epsilon min). -/
theorem MHAEYJN_CONVEX_LOCAL_FAN_p37 {a b : ℝ} {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {f : V3 → ℝ → V3} {v w u : V3}
    (_hcf : ConvexLocalFan V E FF) (_hl : Lunar v w V E) (_hd : Deformation f V a b)
    (_hang : interiorAngle1 0 FF v < Real.pi) (_hu : u ∈ V) (_hv : u ≠ v)
    (_hw : u ≠ w)
    (_hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
    (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      ConvexLocalFan ((fun z => f z t) '' V)
        ((fun s => (fun z => f z t) '' s) '' E)
        ((fun p => (f p.1 t, f p.2 t)) '' FF) := by
  sorry

/-- The registry `MHAEYJN_concl` (appendix.hl:25) as a `Prop`: the
`real_interval (a,b)` ↔ `Icc a b` rendering, verbatim `_p37` copy.
NEEDS: merge with the NUXCOEA/IMJXPHR-lane twin `MHAEYJN_prop_p34`
(LocalAuto34; its olean is not built in this checkout). -/
def MHAEYJN_prop_p37 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (v w u : V3),
    ConvexLocalFan V E FF →
    Lunar v w V E →
    Deformation f V a b →
    interiorAngle1 0 FF v < Real.pi →
    u ∈ V → u ≠ v → u ≠ w →
    (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
    (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Lunar v w ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- HOL `MHAEYJN` (lunar_deform.hl:4985): the lunar deformation registry
conclusion.  GIANT (sorry): needs `MHAEYJN_CONVEX_LOCAL_FAN_p37` +
`SUB_LUNAR_DEFORM_LEMMA_p37` (the `if e < e' then e else e'` min of the two
windows; the Lunar conjunct comes from `SUB_LUNAR_DEFORM_LEMMA_p37`). -/
theorem MHAEYJN_p37 : MHAEYJN_prop_p37 := by
  sorry

end Kepler.Text

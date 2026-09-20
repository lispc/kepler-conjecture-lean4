/-
LocalAuto7: port of `scripts/local/polar_fan.hl` (Flyspeck "polar fan"
formalization, module `Polar_fan`; 3362 lines, 2 defs + 49 theorems).

FILE MAP
  The file is the POLAR-FAN DUALITY chapter of the local-fan development.
  (a) Geometric groundwork: azimuth/arc/dihedral kit (`DIHV_ARCV`,
      `AZIM_DIHV_SAME_STRONG`, `AZIM_ARCV`), plane/hull kit
      (`PLANE_AFFINE_HULL_3`, `AFFINE_HULL_3_GENERATED`), azimuth
      degeneracy (`COLLINEAR_AZIM_0_OR_PI`), angle additivity on cones
      (`ANGLES_ADD_AFF_GE`).
  (b) The aff_ge cone lemmas driving the polar construction:
      `AFF_GE_SCALE_LEMMA`, `AZIM_SAME_WITHIN_AFF_GE(_ALT)`,
      `COLLINEAR_WITHIN_AFF_GE_COLLINEAR`,
      `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE`, `UNION_AFF_GE_1_2`.
  (c) Cycle/iteration kit on the rho orbit (`AZIM_CYCLE_*`,
      `IVS_AZIM_CYCLE_*`, `RHO_NODE1_INJECTIVE`, the orbit-map lemmas,
      `ITER_(IVS_)RHO_IDD`, `LOFA_IMP_ITER_IVS_RHO_NODE_ID`), the
      hyp-function characterizations (`nnOfHyp3`/`ffOfHyp3`/`eeOfHyp3`),
      cyclicity sums (`ORDER_AZIM_SUM2Pi_0`), local-fan cardinal facts,
      sin/cross sign kit (`SIN_AZIM_MUTUAL_CROSS`,
      `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS(_ALT)`).
  (d) fan7/FAN economizations (`GMLWKPK`, `GMLWKPK_ALT`,
      `FAN_ECONOMIZED`, `FAN7_AFF_GT_CONDITION`, `FAN_AFF_GT_CONDITION`,
      `GMLWKPK_SIMPLE`, `FAN_ECONOMIZED_SIMPLE`).
  (e) The polar fan itself: `polarFan` (HOL `JNVXCRC`), its fundamental
      duality property `BGMIFTE` (the polar fan of a convex local fan is
      again a convex local fan; arc ↔ interior-angle duality), and the
      perimeter lane: `fanPerimeter` (HOL `IQCPCGW`), invariance
      (`FAN_PERIMETER_INVARIANT`, `FAN_PERIMETER_INVARIANT_CARD_V`,
      `FAN_PERIMETER`) and the 2*pi bound `WSEWPCH`.

ENCODING NOTES (polar fan ↔ local fan duality)
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `ITER n f x` ↔
    `f^[n] x` (`Function.iterate`); `@v. v IN V` ↔ `Classical.epsilon`;
    `CARD s` ↔ `Set.ncard` (junk 0 on infinite sets, as in HOL);
    `sum (0..n) g` ↔ `∑ i ∈ Finset.Ico 0 (n+1)`; the `CARD FF - 1`
    truncation in `fan_perimeter` is kept verbatim via natural
    subtraction: `Finset.range ((FF.ncard : ℕ) - 1 + 1)`.
  - HOL `cross` ↔ `cross3` (Mathlib `crossProduct` lifted over the
    `WithLp` type synonym; the TopologyFan copy is private there, so a
    module-local copy is made here).  HOL `orthogonal a b` is rendered
    pointwise as `a ⬝ᵥ b = 0`.
  - The Wrgcvdr_cizmrrh/Sphere vocabulary is ported here as the module's
    own `_p7` copies (bodies copied verbatim from the `_p2` lane in
    LocalAuto2): `azim_cycle` ↦ `azimCycle_p7`, `ivs_azim_cycle` ↦
    `ivsAzimCycle_p7`, `nn_of_hyp`/`ff_of_hyp`/`ee_of_hyp` ↦
    `nnOfHyp_p7`/`ffOfHyp_p7`/`eeOfHyp_p7`, `darts_of_hyp` ↦
    `dartsOfHyp_p7`, `EE` ↦ LocalAuto1's `ee`, `plane` ↦ `plane_p7`.
    Rationale: LocalAuto2 is NOT importable next to LocalAuto1 (the
    PackingAuto18/PackingAuto20 lanes both own `Kepler.Text.atn2PA18`, so the
    two import trees clash), and the unsuffixed names stay reserved for
    the LocalAuto1/LocalAnchors lanes per their merge notes.  Merge note:
    when the atn2PA18 clash is resolved, these `_p7` copies and their `rfl`
    lemmas should be re-pointed at the shared lane and deleted.
  - `local_fan`/`convex_local_fan` ↦ LocalAuto1's `LocalFan` /
    `ConvexLocalFan` (whose hypermap kit is still a registry stub), so
    every theorem whose HOL proof consumes local-fan content carries a
    faithful STATEMENT with `sorry` body — DISCHARGES convention: the
    Local-Fan chapter discharges them when the hypermap kit lands, with
    the statements unchanged.  `interior_angle1` ↦ `interiorAngle1`;
    `rho_node1`/`ivs_rho_node1` ↦ `rhoNode1`/`ivsRhoNode1`;
    `generic`/`circular`/`lunar` ↦ `Generic`/`Circular`/`Lunar`;
    `graph`/`fan1`/`fan2`/`fan6`/`fan7`/`FAN` ↦ `Kepler.Text.Fan`'s
    `Graph`/`fan1`/`fan2`/`fan6`/`fan7`/`FAN`; `aff_ge`/`aff_gt`/
    `aff_lt` ↦ `affGe`/`affGt`/`affLt` (Kepler.Geom.Aff); HOL
    `angle(v,u,x)` ↦ `EuclideanGeometry.angle v u x`; `sum V f` over a
    set ↦ `setSum` (PackingAuto2, junk 0 on infinite sets).
  - The 15 mechanical theorems are PROVED here: `DIHV_ARCV`,
    `AZIM_DIHV_SAME_STRONG`, `AZIM_ARCV`, `PLANE_AFFINE_HULL_3`,
    `AZIM_CYCLE_BASIC_PROPERTIES`, `AZIM_CYCLE_TWO_POINT_SET_ALT`,
    `IVS_AZIM_CYCLE_TWO_POINT_SET`, `IVS_AZIM_CYCLE_TWO_POINT_SET_ALT`,
    `AZIM_CYCLE_SING`, `IVS_AZIM_CYCLE_SING`, `nnOfHyp3`, `ffOfHyp3`,
    `eeOfHyp3`, `FAN_ECONOMIZED`, `FAN_ECONOMIZED_SIMPLE` (the latter
    two by propositional transport through `GMLWKPK`/`GMLWKPK_SIMPLE`).
    NO `native_decide` anywhere.

DISCHARGES: the sorry'd theorems are the polar-fan chapter contract
(`BGMIFTE`, `WSEWPCH`, the orbit/perimeter lemmas and the fan7/FAN
economizations); they are discharged from the Local-Fan foundation with
the statements below unchanged.
-/

import Kepler.Geom.Aff
import Kepler.Geom.LuneVolume
import Kepler.Text.Fan
import Kepler.Text.LocalAuto1
import Kepler.Text.PackingAuto5
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Cross product (HOL `cross`) -/

/-- HOL `cross` (`real^3` cross product) on `V3` — this is PackingAuto18's
`cross3` (imported; a module-local copy would clash).  Coercion kit for
the `WithLp` type synonym, mirroring `Kepler.Geom`: -/
private theorem coe_cross3P (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) = crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) :=
  rfl

/-- Canonical dot on `V3` (both arguments coerced whole to the
`Fin 3 → ℝ` identification); module-internal carrier keeping coercion
forms stable under `rw` (HOL `x dot y`). -/
@[reducible] private def dotV (x y : V3) : ℝ := ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ)

private theorem coe_smulP (t : ℝ) (a : V3) : ((t • a : V3) : Fin 3 → ℝ) = t • ((a : V3) : Fin 3 → ℝ) := rfl
private theorem coe_subP (a b : V3) : ((a - b : V3) : Fin 3 → ℝ) = ((a : V3) : Fin 3 → ℝ) - ((b : V3) : Fin 3 → ℝ) := rfl
private theorem coe_zeroV : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl
private theorem smul_dotP (t : ℝ) (a b : Fin 3 → ℝ) :
    (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := smul_dotProduct t a b
private theorem dot_smulP (a : Fin 3 → ℝ) (t : ℝ) (b : Fin 3 → ℝ) :
    a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) := dotProduct_smul t a b

/-! ## Wrgcvdr vocabulary, `_p7` copies (localization.hl:38-63) -/

/-- HOL `azim_cycle` (sphere.hl:414; minimal azimuth, distance tiebreak,
`W SUBSET {p}` degenerate case).  `_p7` module-local copy, see the
encoding notes; HOL `projection (w-v) (u-v)` ↔ repo
`projection (u - v) (w - v)`. -/
noncomputable def azimCycle_p7 (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-- HOL `ivs_azim_cycle W v0 v w` (localization.hl:55). -/
noncomputable def ivsAzimCycle_p7 (W : Set V3) (v0 v w : V3) : V3 :=
  if W = ∅ then w else Classical.epsilon fun x => x ∈ W ∧ azimCycle_p7 W v0 v x = w

/-- HOL `darts_of_hyp E V` (localization.hl:45) =
`ord_pairs E ∪ self_pairs E V`. -/
def dartsOfHyp_p7 {α : Type*} (E : Set (Set α)) (V : Set α) : Set (α × α) :=
  {p | {p.1, p.2} ∈ E} ∪ {p | p.1 = p.2 ∧ p.1 ∈ V}

/-- HOL `ee_of_hyp (x,V,E)` (localization.hl:48). -/
noncomputable def eeOfHyp_p7 (_x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p7 E V then (d.2, d.1) else d

/-- HOL `nn_of_hyp (x,V,E)` (localization.hl:51). -/
noncomputable def nnOfHyp_p7 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p7 E V then (d.1, azimCycle_p7 (ee d.1 E) x d.1 d.2) else d

/-- HOL `ff_of_hyp (x,V,E)` (localization.hl:59). -/
noncomputable def ffOfHyp_p7 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p7 E V then (d.2, ivsAzimCycle_p7 (ee d.2 E) x d.2 d.1) else d

/-- HOL `plane` (sphere.hl:345): spanned by three non-collinear points. -/
def plane_p7 (A : Set V3) : Prop :=
  ∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧ A = affineSpan ℝ ({u, v, w} : Set V3)

/-! ## Some natural lemmas (polar_fan.hl:11-100) -/

/-- HOL `DIHV_ARCV` (polar_fan.hl:11). -/
theorem DIHV_ARCV {e u v w : V3} (h1 : (e - u) ⬝ᵥ (v - u) = 0)
    (h2 : (e - u) ⬝ᵥ (w - u) = 0) (he : e ≠ u) : dihV u e v w = arcV u v w := by
  have hcn : 0 < ‖(e - u : V3)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hc : 0 < dotV (e - u) (e - u) := by
    rw [show dotV (e - u) (e - u)
          = ‖(e - u : V3)‖ ^ 2 from (norm_sq_eq_dot (e - u : V3)).symm]
    exact pow_pos hcn 2
  have h1' : dotV (v - u) (e - u) = 0 := by
    show ((v - u : V3) : Fin 3 → ℝ) ⬝ᵥ ((e - u : V3) : Fin 3 → ℝ) = 0
    rw [dotProduct_comm]
    exact h1
  have h2' : dotV (w - u) (e - u) = 0 := by
    show ((w - u : V3) : Fin 3 → ℝ) ⬝ᵥ ((e - u : V3) : Fin 3 → ℝ) = 0
    rw [dotProduct_comm]
    exact h2
  unfold dihV
  dsimp only
  show arcV 0 (dotV (e - u) (e - u) • (v - u) - dotV (v - u) (e - u) • (e - u))
           (dotV (e - u) (e - u) • (w - u) - dotV (w - u) (e - u) • (e - u))
      = arcV u v w
  rw [h1', h2', zero_smul, sub_zero]
  simp only [arcV, coe_zeroV, coe_smulP, coe_subP, sub_zero, dist_eq_norm, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, smul_dotP, dot_smulP]
  by_cases ha : v - u = 0
  · rw [ha]; simp
  by_cases hb : w - u = 0
  · rw [hb]; simp
  · have hna : ‖(v - u : V3)‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hnb : ‖(w - u : V3)‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    have hcne : dotV (e - u) (e - u) ≠ 0 := ne_of_gt hc
    refine congrArg Real.arccos ?_
    field_simp

/-- HOL `AZIM_DIHV_SAME_STRONG` (polar_fan.hl:23). -/
theorem AZIM_DIHV_SAME_STRONG {v w v1 v2 : V3} (h1 : ¬ Collinear3 v w v1)
    (h2 : ¬ Collinear3 v w v2) (hπ : azim v w v1 v2 ≤ Real.pi) :
    azim v w v1 v2 = dihV v w v1 v2 := by
  rcases lt_or_eq_of_le hπ with hlt | heq
  · exact azim_dihv_same h1 h2 hlt
  · have hcompl := azim_dihv_compl h1 h2 (le_of_eq heq.symm)
    rw [heq]; linarith

/-- HOL `AZIM_ARCV` (polar_fan.hl:31). -/
theorem AZIM_ARCV {e u v w : V3} (h1 : (e - u) ⬝ᵥ (v - u) = 0)
    (h2 : (e - u) ⬝ᵥ (w - u) = 0) (h3 : ¬ Collinear3 u e v) (h4 : ¬ Collinear3 u e w)
    (hπ : azim u e v w ≤ Real.pi) : azim u e v w = arcV u v w := by
  have hne : e ≠ u := fun h => h3 (collinear3_of_eq h)
  rw [← DIHV_ARCV h1 h2 hne]
  exact AZIM_DIHV_SAME_STRONG h3 h4 hπ

/-- HOL `PLANE_AFFINE_HULL_3` (polar_fan.hl:42). -/
theorem PLANE_AFFINE_HULL_3 (a b c : V3) :
    plane_p7 (affineSpan ℝ ({a, b, c} : Set V3)) ↔ ¬ Collinear ℝ ({a, b, c} : Set V3) := by
  constructor
  · rintro ⟨u, v, w, hnc, hA⟩ hC
    apply hnc
    have hdir : vectorSpan ℝ ({u, v, w} : Set V3) = vectorSpan ℝ ({a, b, c} : Set V3) := by
      rw [← direction_affineSpan ℝ ({u, v, w} : Set V3),
          ← direction_affineSpan ℝ ({a, b, c} : Set V3)]
      have hA' : affineSpan ℝ ({a, b, c} : Set V3) = affineSpan ℝ ({u, v, w} : Set V3) :=
        SetLike.coe_injective hA
      rw [hA']
    rw [collinear_iff_finrank_le_one, hdir]
    exact collinear_iff_finrank_le_one.mp hC
  · intro hnc
    exact ⟨a, b, c, hnc, rfl⟩

/-- HOL `AFFINE_HULL_3_GENERATED` (polar_fan.hl:46). -/
theorem AFFINE_HULL_3_GENERATED {s : Set V3} {u v w : V3}
    (hsub : s ⊆ affineSpan ℝ ({u, v, w} : Set V3)) (hnc : ¬ Collinear ℝ s) :
    affineSpan ℝ ({u, v, w} : Set V3) = affineSpan ℝ s := by
  sorry

/-- HOL `COLLINEAR_AZIM_0_OR_PI` (polar_fan.hl:63). -/
theorem COLLINEAR_AZIM_0_OR_PI (u e v w : V3) (hcol : Collinear ℝ ({u, v, w} : Set V3)) :
    azim u e v w = 0 ∨ azim u e v w = Real.pi := by
  sorry

/-- HOL `ANGLES_ADD_AFF_GE` (polar_fan.hl:74). -/
theorem ANGLES_ADD_AFF_GE {u v w x : V3} (hv : v ≠ u) (hw : w ≠ u) (hx : x ≠ u)
    (hmem : x ∈ affGt {u} {v, w}) :
    EuclideanGeometry.angle v u x + EuclideanGeometry.angle x u w
      = EuclideanGeometry.angle v u w := by
  sorry

/-! ## Borderline case and aff_ge cones (polar_fan.hl:102-273) -/

/-- HOL `AFF_GE_SCALE_LEMMA` (polar_fan.hl:102). -/
theorem AFF_GE_SCALE_LEMMA (a : ℝ) (u v : V3) (ha : 0 < a) (hv : v ≠ 0) :
    affGe ({0} : Set V3) {a • u, v} = affGe ({0} : Set V3) {u, v} := by
  sorry

/-- HOL `AZIM_SAME_WITHIN_AFF_GE` (polar_fan.hl:120). -/
theorem AZIM_SAME_WITHIN_AFF_GE (a u v w z : V3) (hmem : v ∈ affGe {a} {u, w})
    (h1 : ¬ Collinear3 a u v) (h2 : ¬ Collinear3 a u w) :
    azim a u v z = azim a u w z := by
  sorry

/-- HOL `AZIM_SAME_WITHIN_AFF_GE_ALT` (polar_fan.hl:148). -/
theorem AZIM_SAME_WITHIN_AFF_GE_ALT (a u v w z : V3) (hmem : v ∈ affGe {a} {u, w})
    (h1 : ¬ Collinear3 a u v) (h2 : ¬ Collinear3 a u w) :
    azim a u z v = azim a u z w := by
  sorry

/-- HOL `COLLINEAR_WITHIN_AFF_GE_COLLINEAR` (polar_fan.hl:161). -/
theorem COLLINEAR_WITHIN_AFF_GE_COLLINEAR (a u v w : V3) (hmem : v ∈ affGe {a} {u, w})
    (hcol : Collinear3 a u w) : Collinear3 a v w := by
  sorry

/-- HOL `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE` (polar_fan.hl:188). -/
theorem GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE (u v w : V3)
    (h1 : ¬ Collinear3 (0 : V3) v u) (h2 : ¬ Collinear3 (0 : V3) v w)
    (hπ : azim (0 : V3) v w u = Real.pi)
    (hdis : affGe ({0} : Set V3) {v, w} ∩ affLt ({0} : Set V3) {u} = ∅) :
    v ∈ affGe ({0} : Set V3) {u, w} := by
  sorry

/-- HOL `UNION_AFF_GE_1_2` (polar_fan.hl:226). -/
theorem UNION_AFF_GE_1_2 (a u v w : V3) (hmem : v ∈ affGe {a} {u, w})
    (hu : u ≠ a) (hv : v ≠ a) (hw : w ≠ a) :
    affGe {a} {u, v} ∪ affGe {a} {v, w} = affGe {a} {u, w} := by
  sorry

/-! ## Cycle and iteration kit (polar_fan.hl:279-406) -/

/-- HOL `AZIM_CYCLE_BASIC_PROPERTIES` (polar_fan.hl:279). -/
theorem AZIM_CYCLE_BASIC_PROPERTIES {W : Set V3} {v w p : V3} (hfin : W.Finite)
    (hp : p ∈ W) :
    azimCycle_p7 W v w p ∈ W ∧
      ∀ q ∈ W, q ≠ p → azim v w p (azimCycle_p7 W v w p) ≤ azim v w p q := by
  by_cases hsub : W ⊆ {p}
  · rw [azimCycle_p7, if_pos hsub]
    refine ⟨hp, fun q hq _ => ?_⟩
    rw [azim_self]
    exact azim_nonneg v w p q
  · have hne : ∃ u ∈ W, u ≠ p := by
      by_contra hc
      push_neg at hc
      exact hsub (fun x hx => by rw [hc x hx]; simp)
    -- lexicographic minimizer of (azim, ‖projection‖) on {u ∈ W | u ≠ p}
    have hf : {u : V3 | u ∈ W ∧ u ≠ p}.Finite := hfin.subset fun x hx => hx.1
    have hne2 : {u : V3 | u ∈ W ∧ u ≠ p}.Nonempty := by
      obtain ⟨u, hu1, hu2⟩ := hne
      exact ⟨u, hu1, hu2⟩
    obtain ⟨q, hqin, hqmin⟩ := Set.exists_min_image
      {u : V3 | u ∈ W ∧ u ≠ p}
      (fun x => toLex (azim v w p x, ‖projection (x - v) (w - v)‖)) hf hne2
    have hqP : q ≠ p ∧ q ∈ W ∧ ∀ r ∈ W, r ≠ p →
        azim v w p q < azim v w p r ∨
          azim v w p q = azim v w p r ∧
            ‖projection (q - v) (w - v)‖ ≤ ‖projection (r - v) (w - v)‖ := by
      refine ⟨hqin.2, hqin.1, fun r hr hpr => ?_⟩
      have h := hqmin r ⟨hr, hpr⟩
      rw [Prod.Lex.toLex_le_toLex] at h
      exact h
    rw [azimCycle_p7, if_neg hsub]
    obtain ⟨hεne, hεW, hεmin⟩ := Classical.epsilon_spec
      (p := fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
        azim v w p u < azim v w p q ∨
          azim v w p u = azim v w p q ∧
            ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖)
      ⟨q, hqP⟩
    exact ⟨hεW, fun r hr hpr => by
      rcases hεmin r hr hpr with h | h
      · exact le_of_lt h
      · exact le_of_eq h.1⟩

/-- HOL `AZIM_CYCLE_TWO_POINT_SET_ALT` (polar_fan.hl:292). -/
theorem AZIM_CYCLE_TWO_POINT_SET_ALT {W : Set V3} {x u v w : V3} (hW : W = {v, w}) :
    azimCycle_p7 W x u v = w := by
  subst hW
  by_cases hvw : v = w
  · subst hvw
    rw [azimCycle_p7, if_pos (c := (({v, v} : Set V3) ⊆ {v})) (by simp)]
  · rw [azimCycle_p7, if_neg (c := (({v, w} : Set V3) ⊆ {v}))
      (fun h => hvw (mem_singleton_iff.mp (h (by simp))).symm)]
    have hwP : w ≠ v ∧ w ∈ ({v, w} : Set V3) ∧ ∀ q ∈ ({v, w} : Set V3), q ≠ v →
        azim x u v w < azim x u v q ∨
          azim x u v w = azim x u v q ∧
            ‖projection (w - x) (u - x)‖ ≤ ‖projection (q - x) (u - x)‖ := by
      refine ⟨fun h => hvw h.symm, by simp, ?_⟩
      intro q hq hqv
      have hq2 : q ∈ ({v} ∪ {w} : Set V3) := hq
      rcases hq2 with h | h
      · exact absurd (Set.mem_singleton_iff.mp h) hqv
      · exact Or.inr ⟨by rw [Set.mem_singleton_iff.mp h], by rw [Set.mem_singleton_iff.mp h]⟩
    obtain ⟨h1, h2, h3⟩ := Classical.epsilon_spec
      (p := fun z : V3 => z ≠ v ∧ z ∈ ({v, w} : Set V3) ∧
        ∀ q ∈ ({v, w} : Set V3), q ≠ v → azim x u v z < azim x u v q ∨
          azim x u v z = azim x u v q ∧
            ‖projection (z - x) (u - x)‖ ≤ ‖projection (q - x) (u - x)‖)
      ⟨w, hwP⟩
    have h2' : ((Classical.epsilon (fun z : V3 => z ≠ v ∧ z ∈ ({v, w} : Set V3) ∧ ∀ q ∈ ({v, w} : Set V3), q ≠ v → azim x u v z < azim x u v q ∨ azim x u v z = azim x u v q ∧ ‖projection (z - x) (u - x)‖ ≤ ‖projection (q - x) (u - x)‖)) ∈ ({v} ∪ {w} : Set V3)) := h2
    rcases h2' with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) h1
    · exact Set.mem_singleton_iff.mp h

/-- The epsilon characterisation of `ivs_azim_cycle` on a singleton. -/
private theorem ivsAzimCycle_singleton {W : Set V3} {x u v : V3} (hW : W = {v})
    (hself : azimCycle_p7 W x u v = v) :
    ivsAzimCycle_p7 W x u v = v := by
  subst hW
  rw [ivsAzimCycle_p7, if_neg (c := (({v} : Set V3) = ∅)) (by
    intro h
    have h2 : (v : V3) ∈ ({v} : Set V3) := by simp
    rw [h] at h2
    exact absurd h2 (by simp))]
  have hspec := Classical.epsilon_spec
    (p := fun z : V3 => z ∈ ({v} : Set V3) ∧ azimCycle_p7 ({v} : Set V3) x u z = v)
    ⟨v, by simp, hself⟩
  have h1 : (Classical.epsilon (fun z : V3 => z ∈ ({v} : Set V3) ∧
      azimCycle_p7 ({v} : Set V3) x u z = v)) ∈ ({v} : Set V3) := hspec.1
  have h3 : (Classical.epsilon (fun z : V3 => z ∈ ({v} : Set V3) ∧
      azimCycle_p7 ({v} : Set V3) x u z = v)) = v := Set.mem_singleton_iff.mp h1
  rw [h3]

/-- HOL `AZIM_CYCLE_SING` (polar_fan.hl:309). -/
theorem AZIM_CYCLE_SING (x u v : V3) : azimCycle_p7 ({v} : Set V3) x u v = v := by
  rw [azimCycle_p7, if_pos (c := (({v} : Set V3) ⊆ {v})) (Set.Subset.refl _)]

/-- HOL `IVS_AZIM_CYCLE_SING` (polar_fan.hl:313). -/
theorem IVS_AZIM_CYCLE_SING (x u v : V3) : ivsAzimCycle_p7 ({v} : Set V3) x u v = v :=
  ivsAzimCycle_singleton rfl (AZIM_CYCLE_SING x u v)

/-- HOL `IVS_AZIM_CYCLE_TWO_POINT_SET` (polar_fan.hl:296). -/
theorem IVS_AZIM_CYCLE_TWO_POINT_SET (a b v w : V3) :
    ivsAzimCycle_p7 ({a, b} : Set V3) v w a = b := by
  by_cases hab : a = b
  · subst hab
    exact ivsAzimCycle_singleton (by simp)
      (AZIM_CYCLE_TWO_POINT_SET_ALT (x := v) (u := w) (v := a) (w := a) rfl)
  · rw [ivsAzimCycle_p7, if_neg (c := (({a, b} : Set V3) = ∅)) (by
      intro h
      have h2 : (a : V3) ∈ ({a, b} : Set V3) := by simp
      rw [h] at h2
      exact absurd h2 (by simp))]
    have hPb : b ∈ ({a, b} : Set V3) ∧ azimCycle_p7 ({a, b} : Set V3) v w b = a :=
      ⟨by simp, AZIM_CYCLE_TWO_POINT_SET_ALT (Set.pair_comm a b)⟩
    obtain ⟨h1, h2⟩ := Classical.epsilon_spec
      (p := fun z : V3 => z ∈ ({a, b} : Set V3) ∧
        azimCycle_p7 ({a, b} : Set V3) v w z = a) ⟨b, hPb⟩
    have h1' : ((Classical.epsilon (fun z : V3 => z ∈ ({a, b} : Set V3) ∧ azimCycle_p7 ({a, b} : Set V3) v w z = a)) ∈ ({a} ∪ {b} : Set V3)) := h1
    rcases h1' with h | h
    · exfalso
      rw [Set.mem_singleton_iff.mp h, AZIM_CYCLE_TWO_POINT_SET_ALT (W := ({a, b} : Set V3)) (x := v) (u := w) (v := a) (w := b) rfl] at h2
      exact hab h2.symm
    · exact Set.mem_singleton_iff.mp h

/-- HOL `IVS_AZIM_CYCLE_TWO_POINT_SET_ALT` (polar_fan.hl:305). -/
theorem IVS_AZIM_CYCLE_TWO_POINT_SET_ALT {W : Set V3} {x u v w : V3} (hW : W = {v, w}) :
    ivsAzimCycle_p7 W x u v = w := by
  subst hW
  exact IVS_AZIM_CYCLE_TWO_POINT_SET v w x u

/-! ## rho_node1 orbit (polar_fan.hl:318-469) -/

/-- HOL `RHO_NODE1_INJECTIVE` (polar_fan.hl:318). -/
theorem RHO_NODE1_INJECTIVE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) :
    ∀ v ∈ V, ∀ w ∈ V, (rhoNode1 FF v = rhoNode1 FF w ↔ v = w) := by
  sorry

/-- HOL `IVS_RHO_NODE1_IN_V` (polar_fan.hl:325). -/
theorem IVS_RHO_NODE1_IN_V {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : ∀ v ∈ V, ivsRhoNode1 FF v ∈ V := by
  sorry

/-- HOL `LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V` (polar_fan.hl:330). -/
theorem LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {v : V3} (hv : v ∈ V) (i : ℕ) :
    (ivsRhoNode1 FF)^[i] v ∈ V := by
  sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT` (polar_fan.hl:336). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i, i < V.ncard ∧ w = (rhoNode1 FF)^[i] v := by
  sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS` (polar_fan.hl:360). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i, i < V.ncard ∧ w = (ivsRhoNode1 FF)^[i] v := by
  sorry

/-- HOL `ITER_IVS_RHO_IDD` (polar_fan.hl:381). -/
theorem ITER_IVS_RHO_IDD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (v : V3) (hv : v ∈ V) (n : ℕ) :
    (ivsRhoNode1 FF)^[n] ((rhoNode1 FF)^[n] v) = v := by
  sorry

/-- HOL `ITER_RHO_IVS_IDD` (polar_fan.hl:392). -/
theorem ITER_RHO_IVS_IDD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (v : V3) (hv : v ∈ V) (n : ℕ) :
    (rhoNode1 FF)^[n] ((ivsRhoNode1 FF)^[n] v) = v := by
  sorry

/-- HOL `LOFA_IMP_ITER_IVS_RHO_NODE_ID` (polar_fan.hl:402). -/
theorem LOFA_IMP_ITER_IVS_RHO_NODE_ID {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (v : V3) (hv : v ∈ V) :
    (ivsRhoNode1 FF)^[V.ncard] v = v := by
  sorry

/-- HOL `GENERIC_LOCAL_FAN_AZIM_POS` (polar_fan.hl:408). -/
theorem GENERIC_LOCAL_FAN_AZIM_POS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : ConvexLocalFan V E FF) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    (v w : V3) (hv : v ∈ V) (hw : w ∈ V) (hwv : w ≠ v) (hwr : w ≠ rhoNode1 FF v) :
    0 < Real.sin (azim (0 : V3) v (rhoNode1 FF v) w) := by
  sorry

/-! ## Hyp-function characterizations and order sums (polar_fan.hl:471-530) -/

/-- HOL `nn_of_hyp3` (polar_fan.hl:471). -/
theorem nnOfHyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    nnOfHyp_p7 x V E = fun d =>
      if d ∈ dartsOfHyp_p7 E V then (d.1, azimCycle_p7 (ee d.1 E) x d.1 d.2) else d :=
  rfl

/-- HOL `ff_of_hyp3` (polar_fan.hl:477). -/
theorem ffOfHyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    ffOfHyp_p7 x V E = fun d =>
      if d ∈ dartsOfHyp_p7 E V then (d.2, ivsAzimCycle_p7 (ee d.2 E) x d.2 d.1) else d :=
  rfl

/-- HOL `ee_of_hyp3` (polar_fan.hl:483). -/
theorem eeOfHyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    eeOfHyp_p7 x V E = fun d => if d ∈ dartsOfHyp_p7 E V then (d.2, d.1) else d :=
  rfl

/-- HOL `ORDER_AZIM_SUM2Pi_0` (polar_fan.hl:488). -/
theorem ORDER_AZIM_SUM2Pi_0 {x y z : V3} {n : ℕ} {g : ℕ → V3}
    (h1 : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (h2 : ∀ i ∈ Finset.Ico 0 (n + 1), ¬ Collinear ℝ ({x, y, g i} : Set V3))
    (h3 : g (n + 1) = g 0) (h4 : 0 < n)
    (h5 : ∀ j ∈ Finset.Ico 0 (n + 1), ∀ k ∈ Finset.Ico 0 (n + 1), j < k →
      azim x y z (g j) < azim x y z (g k)) :
    (∑ i ∈ Finset.Ico 0 (n + 1), azim x y (g i) (g (i + 1))) = 2 * Real.pi := by
  sorry

/-- HOL `LOCAL_FAN_NOT_EMPTY_FF` (polar_fan.hl:511). -/
theorem LOCAL_FAN_NOT_EMPTY_FF {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : FF ≠ ∅ := by
  sorry

/-- HOL `LOCAL_FAN_NOT_CARD_FF_GE_2` (polar_fan.hl:521). -/
theorem LOCAL_FAN_NOT_CARD_FF_GE_2 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) : 2 ≤ FF.ncard := by
  sorry

/-! ## Sin/cross sign kit (polar_fan.hl:532-566) -/

/-- HOL `SIN_AZIM_MUTUAL_CROSS` (polar_fan.hl:532). -/
theorem SIN_AZIM_MUTUAL_CROSS (u v w : V3) :
    (Real.sin (azim (0 : V3) u v w) < 0 ↔ (cross3 u v) ⬝ᵥ w < 0) ∧
    (0 < Real.sin (azim (0 : V3) u v w) ↔ 0 < (cross3 u v) ⬝ᵥ w) ∧
    (Real.sin (azim (0 : V3) u v w) ≤ 0 ↔ (cross3 u v) ⬝ᵥ w ≤ 0) ∧
    (0 ≤ Real.sin (azim (0 : V3) u v w) ↔ 0 ≤ (cross3 u v) ⬝ᵥ w) ∧
    (Real.sin (azim (0 : V3) u v w) = 0 ↔ (cross3 u v) ⬝ᵥ w = 0) := by
  sorry

/-- HOL `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS` (polar_fan.hl:541). -/
theorem CROSS_POSITIVE_MULTIPLE_AZIM_AXIS {x y z : V3} (hx : x ≠ 0)
    (h1 : x ⬝ᵥ y = 0) (h2 : x ⬝ᵥ z = 0)
    (h3 : 0 < azim (0 : V3) x y z) (h4 : azim (0 : V3) x y z < Real.pi) :
    ∃ a : ℝ, 0 < a ∧ cross3 y z = a • x := by
  sorry

/-- HOL `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS_ALT` (polar_fan.hl:557). -/
theorem CROSS_POSITIVE_MULTIPLE_AZIM_AXIS_ALT {x y z : V3} (hx : x ≠ 0)
    (h1 : x ⬝ᵥ y = 0) (h2 : x ⬝ᵥ z = 0)
    (h3 : 0 < azim (0 : V3) x y z) (h4 : azim (0 : V3) x y z < Real.pi) :
    ∃ a : ℝ, 0 < a ∧ x = a • cross3 y z := by
  sorry

/-! ## fan7 / FAN equivalences (polar_fan.hl:572-1047) -/

/-- HOL `GMLWKPK` (polar_fan.hl:572). -/
theorem GMLWKPK (x : V3) (V : Set V3) (E : Set (Set V3)) (hg : Graph E) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
          (∀ v : V3, e1 ∩ e2 = {v} → affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v}) := by
  sorry

/-- HOL `GMLWKPK_ALT` (polar_fan.hl:608). -/
theorem GMLWKPK_ALT (x : V3) (V : Set V3) (E : Set (Set V3)) (hg : Graph E)
    (hx : ∀ e ∈ E, x ∉ e) :
    (fan7 x V E ↔
      (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
      (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
        affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v})) := by
  sorry

/-- HOL `FAN_ECONOMIZED` (polar_fan.hl:641). -/
theorem FAN_ECONOMIZED (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ↔
      (⋃₀ E) ⊆ V ∧ Graph E ∧ fan1 x V E ∧ fan2 x V E ∧ fan6 x V E ∧
        (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
          ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
            (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
            (∀ v : V3, e1 ∩ e2 = {v} →
              affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v})) := by
  constructor
  · rintro ⟨hun, hg, hf1, hf2, hf6, hf7⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK x V E hg).mp hf7⟩
  · rintro ⟨hun, hg, hf1, hf2, hf6, he⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK x V E hg).mpr he⟩

/-- HOL `FAN7_AFF_GT_CONDITION` (polar_fan.hl:661). -/
theorem FAN7_AFF_GT_CONDITION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hg : Graph E) (hx : x ∉ V)
    (hsub : ∀ e ∈ E, e ⊆ V ∧ x ∉ e)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅) :
    fan7 x V E := by
  sorry

/-- HOL `FAN_AFF_GT_CONDITION` (polar_fan.hl:812). -/
theorem FAN_AFF_GT_CONDITION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hun : (⋃₀ E) ⊆ V) (hg : Graph E) (hf1 : fan1 x V E) (hf2 : fan2 x V E)
    (hf6 : fan6 x V E)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅) :
    FAN x V E := by
  sorry

/-- HOL `GMLWKPK_SIMPLE` (polar_fan.hl:832). -/
theorem GMLWKPK_SIMPLE (x : V3) (V : Set V3) (E : Set (Set V3))
    (hun : (⋃₀ E) ⊆ V) (hg : Graph E) (hf6 : fan6 x V E)
    (hx : ∀ e ∈ E, x ∉ e) :
    (fan7 x V E ↔
      ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) := by
  sorry

/-- HOL `FAN_ECONOMIZED_SIMPLE` (polar_fan.hl:1023). -/
theorem FAN_ECONOMIZED_SIMPLE (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ↔
      (⋃₀ E) ⊆ V ∧ Graph E ∧ fan1 x V E ∧ fan2 x V E ∧ fan6 x V E ∧
        (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
          ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
            e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) := by
  constructor
  · rintro ⟨hun, hg, hf1, hf2, hf6, hf7⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK_SIMPLE x V E hun hg hf6
      (fun e he hxe => hf2 (hun (Set.mem_sUnion_of_mem hxe he)))).mp hf7⟩
  · rintro ⟨hun, hg, hf1, hf2, hf6, he⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK_SIMPLE x V E hun hg hf6
      (fun e he hxe => hf2 (hun (Set.mem_sUnion_of_mem hxe he)))).mpr he⟩

/-! ## Definition of the polar fan (polar_fan.hl:1053) -/

/-- HOL `JNVXCRC` (polar_fan.hl:1053): the polar fan of `(V,E,FF)` —
vertices are the cross products `v × rho_node1 FF v`, edges join
consecutive images, darts likewise.  `E` is not used by the body (kept
for the HOL signature). -/
noncomputable def polarFan (V : Set V3) (_E : Set (Set V3)) (FF : Set (V3 × V3)) :
    Set V3 × Set (Set V3) × Set (V3 × V3) :=
  let r := rhoNode1 FF
  let p := fun v : V3 => cross3 v (r v)
  (image p V, image (fun v : V3 => {p v, p (r v)}) V,
    image (fun v : V3 => (p v, p (r v))) V)

/-! ## Properties of the polar fan (polar_fan.hl:1065) -/

/-- HOL `BGMIFTE` (polar_fan.hl:1065): the polar fan of a convex local
fan is a convex local fan; the interior angles pass to the polar
vertices via `arcV = π - interior_angle1` in both directions. -/
theorem BGMIFTE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {V' : Set V3}
    {E' : Set (Set V3)}
    {FF' : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    (hp : polarFan V E FF = (V', E', FF')) :
    ConvexLocalFan V' E' FF' ∧ Generic V' E' ∧ V'.ncard = V.ncard ∧
      (∀ v ∈ V,
          arcV (0 : V3) (cross3 v (rhoNode1 FF v))
                (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)))
            = Real.pi - interiorAngle1 (0 : V3) FF (rhoNode1 FF v) ∧
          0 < arcV (0 : V3) (cross3 v (rhoNode1 FF v))
                (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))) ∧
          arcV (0 : V3) (cross3 v (rhoNode1 FF v))
                (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))) < Real.pi) ∧
      (∀ v ∈ V,
          arcV (0 : V3) v (rhoNode1 FF v)
            = Real.pi - interiorAngle1 (0 : V3) FF' (cross3 v (rhoNode1 FF v)) ∧
          0 < arcV (0 : V3) v (rhoNode1 FF v) ∧
          arcV (0 : V3) v (rhoNode1 FF v) < Real.pi) := by
  sorry

/-! ## Perimeter and its bound of 2 pi (polar_fan.hl:2115-3362) -/

/-- HOL `IQCPCGW` (polar_fan.hl:2115): `fan_perimeter`.  The
`@v. v IN V` choice is `Classical.epsilon`; the `CARD FF - 1`
truncation is kept verbatim. -/
noncomputable def fanPerimeter (V : Set V3) (_E : Set (Set V3)) (FF : Set (V3 × V3)) : ℝ :=
  let v := Classical.epsilon (fun v : V3 => v ∈ V)
  ∑ i ∈ Finset.range ((FF.ncard - 1 : ℕ) + 1),
    arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v)

/-- HOL `FAN_PERIMETER_INVARIANT` (polar_fan.hl:2122). -/
theorem FAN_PERIMETER_INVARIANT {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (v : V3) (hv : v ∈ V) :
    fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((FF.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := by
  sorry

/-- HOL `FAN_PERIMETER_INVARIANT_CARD_V` (polar_fan.hl:2171). -/
theorem FAN_PERIMETER_INVARIANT_CARD_V {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (v : V3) (hv : v ∈ V) :
    fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((V.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := by
  sorry

/-- HOL `FAN_PERIMETER` (polar_fan.hl:2184). -/
theorem FAN_PERIMETER {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) :
    fanPerimeter V E FF = setSum V (fun v : V3 => arcV (0 : V3) v (rhoNode1 FF v)) := by
  sorry

/-- HOL `WSEWPCH` (polar_fan.hl:2213): the fan perimeter of a convex
local fan is at most `2 * pi`. -/
theorem WSEWPCH {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : fanPerimeter V E FF ≤ 2 * Real.pi := by
  sorry

end Kepler.Text

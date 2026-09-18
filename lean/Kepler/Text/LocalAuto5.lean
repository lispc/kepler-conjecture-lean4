/-
LocalAuto5: port of `scripts/local/local_lemmas.hl` (Flyspeck "Local Fan"
chapter, Hoang Le Truong 2010; 7463 lines — the chapter's biggest lemma
bank: 3 definitions + 194 theorems over the `localization.hl` vocabulary).

FILE MAP (HL order preserved)
  - lines 34-1735: local-fan structure kit: `LOCAL_FAN_*` (face/vertex
    transport), `FAN_*` (plain-fan darts), rho_node1 orbit facts
    (`LOCAL_FAN_ORBIT_MAP*`, `*_IS_SUCCESEOR_AZIM`, `FIRST_AZIM_CYCLE_*`,
    `SEQUENCE_OF_RHO_NODE_IS_SUC`, `V_AZIM_SMALLEST_ELMS`,
    `AZIM_LAST_POINT_*`, `KOMWBWC`), cardinality of orbits.
  - lines 1736-2530: `interior_angle1` kit, wedge_ge / azim monotonicity,
    EE two-neighbor facts, `OZQVSFF`, `INTERSECTION_LEMMA`.
  - lines 2531-3497: conv0/aff line lemmas (`IN_CONV0*`, `AFF2_*`,
    `INTER_AFF_GT_LT_*`, `AFF_GT_AFF_LT_INTERPRET*`), orbit/card recursion
    (`CARD_RECUSIVE_EQ`, `LE_CARDV_IMP_CARD_DETERED`, `LOOP_SET_*`),
    `KCHMAMG` (circular fan), `AZIM_EQ_0_GE_ALT2`.
  - lines 3498-4430: wedge_ge ↔ aff_ge, azim = pi wedge, `wedge_in_fan_ge2`
    / `azim_in_fan2` unfoldings, `PGSQVBL`, `LUNAR_IMP_*` half-circle kit,
    `LOFA_IMP_*` card/bij facts.
  - lines 4431-6071: `HALF_CIRCULAR_IN_PLANE`, `RHO_NODE1_MONO_WITH_AZIM`,
    lunar geometry (`LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT*`,
    `HALP_CIRCLE_IS_INTERSECTION`, `HKIRPEP`), `MONO_AZIM_AS_BTA_I`
    predecessor.
  - lines 6072-7463: `vv`-sequence kit (`FIRST_EQ0_LAST_LT_PI`,
    `EGHNAVX`), successive rho-node plane lemmas
    (`SUCCESSIVE_RHO_NODE1_AFF_LT`, `TWO_SIDES_SUCESSIVE`,
    `CNVX_IMP_INTERIOR_ANGLE_PI`).

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `vec 0` <-> `(0 : V3)`;
    `FST`/`SND` <-> `.1`/`.2`; `ITER n f` <-> `f^[n]` (Function.iterate);
    `CARD` <-> `Set.ncard`; `IMAGE`/`INJ`/`BIJ`/`SURJ` <->
    `Set.image`/`Set.InjOn`/`Set.BijOn`/surjection.
  - Vocabulary is the importable LocalAuto2 localization kit (`_p2`):
    `local_fan` -> `localFan_p2`, `convex_local_fan` -> `convexLocalFan_p2`,
    `lunar` -> `lunar_p2`, `rho_node1` -> `rhoNode1_p2`,
    `ivs_rho_node1` -> `ivsRhoNode1_p2`, `interior_angle1` ->
    `interiorAngle1_p2`, `wedge_ge` -> `wedgeGe_p2`,
    `wedge_in_fan_ge` -> `wedgeInFanGe_p2`, `azim_in_fan` -> `azimInFan_p2`,
    `EE` -> `EE_p2`, `azim_cycle` -> `azimCycle_p2`, `conv0` -> `conv0_p2`,
    `plane` -> `plane_p2`, `orbit_map` -> `orbitF_p2`,
    `ord_pairs`/`self_pairs`/`darts_of_hyp`/`ee_of_hyp`/`nn_of_hyp`/
    `ff_of_hyp` -> the `_p2` copies, `graph` -> `Kepler.Text.Fan.Graph`,
    `FAN (vec 0,V,E)` -> `FAN 0 V E`.
  - The 3 `new_definition`s of the source (`rho_node1`, `ivs_rho_node1`,
    `interior_angle1`) are NOT re-ported: identical bodies already live in
    the kit (`rhoNode1_p2`/`ivsRhoNode1_p2`/`interiorAngle1_p2`; canonical
    `LocalAuto1.rhoNode1`/`ivsRhoNode1`/`interiorAngle1`). Merge note: this
    lane owns the LEMMAS only.
  - `cyclic_set` -> `cyclicSet_p3` (LocalAuto3, polyhedron.hl:126);
    `dihV`/`arcV` -> Kepler.Geom; `aff`/`affine hull` -> `affineSpan ℝ`;
    `conv` -> `convexHull ℝ`; `collinear` -> `Collinear ℝ`;
    `coplanar` -> `Kepler.Geom.Coplanar`; `cross` -> `crossProduct` via the
    `WithLp.toLp 2` idiom (cf. `polarFan_p2`).
  - HOL `x,y IN FF ==> x IN V /\ y IN V` (LOCAL_FAN_IMP_IN_V) is a dart
    statement: rendered as `d1 ∈ FF -> d2 ∈ FF -> d1.1 ∈ V ∧ d1.2 ∈ V ∧
    d2.1 ∈ V ∧ d2.2 ∈ V` (cf. LOCAL_FAN_IMP_IN_V2).
  - OCaml tactic/term bindings (SWITCH_TAC, AFF_SGN_TRULE, `full`,
    `term_length`, `sortlength_thml`, PAT_TAC, FIRST_PAT_ASSUM,
    FIRST_PAT_X_ASSUM, the two intermediate `t` lets) are not ported; the
    two `t` lets carry the statements of
    `FOR_AFF_GT_NOT_INTERSECTION2`/`X_IN_AFF_GT_X`, which ARE ported.
  - Name re-bindings in HL are carried once: the second
    `INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0` (a currying re-render) and
    `AFF_GT_AFF_LT_INTERPRET2` (a DISJOINT-union re-render, derived here).
  - Mechanical lemmas are PROVED; giants carry `sorry` (docstrings keep the
    HL proof hints). `Affsign`-encoding deviation: the repo `Affsign`
    requires a finite support-set, so the `CONV_SUBSET_AFF_GE` /
    `CONV0_SUBSET_AFF_GT` / `X_IN_AFF_GT_X` trio carries an explicit
    `S.Finite` hypothesis (flagged in the docstrings).
  - DISCHARGES: nothing yet — this file carries no `*_concl` items; the
    appendix registry (LocalAuto1) is untouched. Parallel lanes LocalAuto6-11
    may copy statements as `_pN` + NEEDS markers per lane convention.
-/

import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto3
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## Port support (not in HL) -/

/-- `Classical.epsilon` collapse when the predicate holds at one point only
(rendering HOL `(@w. P w)` under a uniqueness hypothesis). -/
theorem epsilonFixed {α : Type*} [Nonempty α] {p : α → Prop} {a : α} (hpa : p a)
    (huniq : ∀ y, p y → y = a) : Classical.epsilon p = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- Port support: the non-negative `Affsign` body-set is convex (the
implicit convexity of HOL `aff_ge` / `conv` cones). -/
theorem Affsign_convex {s t : Set V3} :
    Convex ℝ {v : V3 | Affsign (fun x : ℝ => 0 ≤ x) s t v} := by
  intro a ha b hb m n hm hn hmn
  obtain ⟨f1, h1, hv1, hs1, hsum1⟩ := ha
  obtain ⟨f2, h2, hv2, hs2, hsum2⟩ := hb
  have hEq : h1.toFinset = h2.toFinset := by
    ext w; simp [Set.Finite.mem_toFinset]
  have hv2' : b = ∑ w ∈ h1.toFinset, f2 w • w := by rw [hv2, hEq]
  have hsum2' : ∑ w ∈ h1.toFinset, f2 w = 1 := by rw [← hEq]; exact hsum2
  refine ⟨fun w => m * f1 w + n * f2 w, h1, ?_, ?_, ?_⟩
  · rw [hv1, hv2', Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_smul, smul_smul, ← add_smul]
  · intro w hw
    have h1w : 0 ≤ f1 w := hs1 w hw
    have h2w : 0 ≤ f2 w := hs2 w hw
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1, hsum2']
    simpa using hmn

/-- Port support: collinearity of a triple through the second point
(`u` on the line `xv`, or the degenerate first-two-points case). -/
theorem collinear_triple_iff {x v u : V3} :
    Collinear ℝ ({x, v, u} : Set V3) ↔ u ∈ affineSpan ℝ ({x, v} : Set V3) ∨ x = v := by
  constructor
  · intro hcol
    obtain ⟨p₀, r, hr⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
    obtain ⟨a, ha⟩ := hr x (by simp)
    obtain ⟨b, hb⟩ := hr v (by simp)
    obtain ⟨c, hc⟩ := hr u (by simp)
    simp only [vadd_eq_add] at ha hb hc
    rcases eq_or_ne x v with hx | hx
    · exact Or.inr hx
    · have hba : b - a ≠ 0 := by
        intro h0
        apply hx
        have h2 : x - v = 0 := by
          rw [ha, hb, sub_eq_zero.mp h0]
          abel
        exact sub_eq_zero.mp h2
      refine Or.inl (mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨(c - a) / (b - a), ?_⟩)
      have hsub : v - x = (b - a) • r := by rw [hb, ha]; module
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      rw [hsub, smul_smul, div_mul_cancel₀ _ hba, ha, hc]
      module
  · intro h
    rcases h with hmem | hx
    · refine ((collinear_insert_of_mem_affineSpan_pair (p₁ := u) (p₂ := x)
        (p₃ := v) hmem).subset ?_)
      intro z hz; simp at hz ⊢; tauto
    · rw [hx]
      simpa using collinear_pair ℝ v u


/-! ## HL lines 46-533: local-fan structure kit and FAN darts -/

/-- HOL `LOCAL_FAN_IMP_IN_V` (local_lemmas.hl:46). The HL conclusion
`x IN V /\ y IN V` is a dart statement (elements of `FF` are darts; the
HOL proof transports via `face H x SUBSET dart H` + `UNIONS E SUBSET V`;
cf. `LOCAL_FAN_IMP_IN_V2` below). -/
theorem LOCAL_FAN_IMP_IN_V (h : localFan_p2 V E FF) {d1 d2 : V3 × V3}
    (hd1 : d1 ∈ FF) (hd2 : d2 ∈ FF) :
    d1.1 ∈ V ∧ d1.2 ∈ V ∧ d2.1 ∈ V ∧ d2.2 ∈ V := sorry

/-- HOL `LOCAL_FAN_RHO_NODE_PROS` (local_lemmas.hl:69): the rho-node maps
`V` onto successor darts, and every dart is `(FST x, rho_node1 FF (FST x))`. -/
theorem LOCAL_FAN_RHO_NODE_PROS (h : localFan_p2 V E FF) :
    (∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF) ∧
      ∀ x ∈ FF, x = (x.1, rhoNode1_p2 FF x.1) := sorry

/-- HOL `ORTHONORMAL_CYCLIC` (local_lemmas.hl:106): a finite set lying in
the hyperplane through 0 perpendicular to `x - y`, disjoint from
`affine hull {x,y}`, is `cyclic_set U x y`. -/
theorem ORTHONORMAL_CYCLIC {x y : V3} {U : Set V3} (hxy : ¬(x = y))
    (hfin : U.Finite)
    (hdot : ∀ u1 ∈ U, ∀ u2 ∈ U, (u1 - u2) ⬝ᵥ (x - y) = 0)
    (hinter : U ∩ affineSpan ℝ ({x, y} : Set V3) = ∅) :
    cyclicSet_p3 U x y := by
  refine ⟨hxy, hfin, ?_, hinter⟩
  intro p hp q hq h hpq
  have hx' : ((x : V3) : Fin 3 → ℝ) - ((y : V3) : Fin 3 → ℝ) ≠ 0 := by
    intro h0
    exact hxy (sub_eq_zero.mp (WithLp.ofLp_injective 2 (by
      rw [WithLp.ofLp_sub 2, WithLp.ofLp_zero 2]
      exact h0)))
  have hnorm : (((x : V3) : Fin 3 → ℝ) - ((y : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (((x : V3) : Fin 3 → ℝ) - ((y : V3) : Fin 3 → ℝ)) ≠ 0 := by
    intro h0
    exact hx' (dotProduct_self_eq_zero.mp h0)
  have h1 : (p - q) ⬝ᵥ (x - y) = 0 := hdot p hp q hq
  rw [hpq, WithLp.ofLp_smul 2, WithLp.ofLp_sub 2, dotProduct_comm,
    dotProduct_smul, smul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h0 | h0
  · rw [h0, zero_smul, sub_eq_zero] at hpq
    exact hpq
  · exact absurd h0 hnorm

/-- HOL `FAN_SINGLETON_V_DARTS` (local_lemmas.hl:126). -/
theorem FAN_SINGLETON_V_DARTS {v : V3} (hfan : FAN 0 V E) (hV : V = {v}) :
    dartsOfHyp_p2 E V = ({(v, v)} : Set (V3 × V3)) := by
  have hEsub : (⋃₀ E) ⊆ V := hfan.1
  have hEE : EE_p2 v E = ∅ := by
    ext w
    simp only [EE_p2, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    constructor
    · intro hw
      exfalso
      have h2 : ({v, w} : Set V3) ⊆ V := (Set.subset_sUnion_of_mem hw).trans hEsub
      have hwV : w ∈ V := h2 (Set.mem_insert_of_mem v rfl)
      have hwv : w = v := by rw [hV] at hwV; exact hwV
      rw [hwv] at hw
      obtain ⟨hf, hc⟩ := hfan.2.1 _ hw
      have h3 : hf.toFinset = ({v} : Finset V3) := by
        ext z
        simp [Set.Finite.mem_toFinset]
      rw [h3] at hc
      simp at hc
    · intro h; exact absurd h (by simp)
  ext d
  constructor
  · intro hd
    rcases Set.mem_or_mem_of_mem_union
      (show d ∈ (ordPairs_p2 E ∪ selfPairs_p2 E V) from hd) with ho | hs
    · have h2 : ({d.1, d.2} : Set V3) ⊆ V := (Set.subset_sUnion_of_mem ho).trans hEsub
      have hde : d = (d.1, d.2) := Prod.mk.eta
      have hd1' : d.1 ∈ V := h2 (Set.mem_insert d.1 ({d.2} : Set V3))
      have hd2' : d.2 ∈ V := h2 (Set.mem_insert_of_mem d.1 rfl)
      have hd1 : d.1 = v := by rw [hV] at hd1'; exact hd1'
      have hd2 : d.2 = v := by rw [hV] at hd2'; exact hd2'
      rw [hde, hd1, hd2]
      simp
    · have hde : d = (d.1, d.2) := Prod.mk.eta
      have h3 : d.1 = d.2 ∧ d.1 ∈ V ∧ EE_p2 d.1 E = ∅ := hs
      have hdd1 : d.1 ∈ V := h3.2.1
      have hdv : d.1 = v := by rw [hV] at hdd1; exact hdd1
      rw [hde, ← h3.1, hdv]
      simp
  · intro hd
    rw [hd]
    exact Or.inr ⟨rfl, by rw [hV]; simp, hEE⟩

/-- HOL `FAN_IN_DARTS_FST_EQ_SND_SELF_PAIRS` (local_lemmas.hl:154). -/
theorem FAN_IN_DARTS_FST_EQ_SND_SELF_PAIRS (hfan : FAN 0 V E) {y : V3 × V3}
    (hy : y ∈ dartsOfHyp_p2 E V) : (y.1 = y.2 ↔ y ∈ selfPairs_p2 E V) := by
  constructor
  · intro h
    rcases Set.mem_or_mem_of_mem_union
      (show y ∈ (ordPairs_p2 E ∪ selfPairs_p2 E V) from hy) with ho | hs
    · exfalso
      obtain ⟨hf, hc⟩ := hfan.2.1 _ ho
      have h1 : ({y.1, y.2} : Set V3) = ({y.1} : Set V3) := by
        simp [← h]
      have h2 : hf.toFinset = ({y.1} : Finset V3) := by
        ext z
        simp [← h, Set.Finite.mem_toFinset]
      rw [h2] at hc
      simp at hc
    · exact hs
  · intro h
    exact h.1

/-- HOL `FAN_FST_EQ_SND_SUPPER_EQ` (local_lemmas.hl:171): a self-pair dart
is fixed by `ee_of_hyp`, `nn_of_hyp` and `ff_of_hyp`. -/
theorem FAN_FST_EQ_SND_SUPPER_EQ (hfan : FAN 0 V E) {y : V3 × V3}
    (hy : y.1 = y.2) :
    eeOfHyp_p2 0 V E y = y ∧ nnOfHyp_p2 0 V E y = y ∧ ffOfHyp_p2 0 V E y = y := by
  obtain ⟨y1, y2⟩ := y
  have hy' : y1 = y2 := hy
  have hEEself : (y1, y2) ∈ dartsOfHyp_p2 E V → EE_p2 y1 E = ∅ := fun hd =>
    ((FAN_IN_DARTS_FST_EQ_SND_SELF_PAIRS hfan hd).mp hy').2.2
  by_cases hd : (y1, y2) ∈ dartsOfHyp_p2 E V
  · have h1 : EE_p2 y1 E = ∅ := hEEself hd
    have h2 : EE_p2 y2 E = ∅ := by rw [← hy']; exact h1
    have h3 : azimCycle_p2 (EE_p2 y1 E) 0 y1 y2 = y2 := by
      rw [h1]
      exact if_pos (by simp)
    unfold eeOfHyp_p2 nnOfHyp_p2 ffOfHyp_p2
    refine ⟨?_, ?_, ?_⟩
    · rw [if_pos hd, hy']
    · rw [if_pos hd, h3, hy']
    · rw [if_pos hd, hy', h2]
      simp [ivsAzimCycle_p2]
  · unfold eeOfHyp_p2 nnOfHyp_p2 ffOfHyp_p2
    exact ⟨if_neg hd, if_neg hd, if_neg hd⟩

/-- HOL `COLLINEAR_CROSS_0` (local_lemmas.hl:190). Cross rendered via
`crossProduct` and the `WithLp.toLp` idiom. -/
theorem COLLINEAR_CROSS_0 {x y z : V3} :
    Collinear ℝ ({x, y, z} : Set V3) ↔
      (WithLp.toLp 2 (crossProduct ((y - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) : V3) = 0 := sorry

/-- HOL `DET_CROSS` (local_lemmas.hl:198). -/
theorem DET_CROSS (x y z : V3) :
    Matrix.det (Matrix.of fun i j => (![x, y, z] : Fin 3 → V3) i j) =
      (crossProduct ((x : V3) : Fin 3 → ℝ) ((y : V3) : Fin 3 → ℝ))
        ⬝ᵥ ((z : V3) : Fin 3 → ℝ) := sorry

/-- HOL `COPLANAR_IFF_CROSS_DOT` (local_lemmas.hl:203). -/
theorem COPLANAR_IFF_CROSS_DOT {x y z t : V3} :
    Coplanar ({x, y, z, t} : Set V3) ↔
      (WithLp.toLp 2 (crossProduct ((y - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (t - x) = 0 := sorry

/-- HOL `CROSS_DOT_COPLANAR` (local_lemmas.hl:211). -/
theorem CROSS_DOT_COPLANAR {x y z : V3} :
    (WithLp.toLp 2 (crossProduct ((x : V3) : Fin 3 → ℝ)
      ((y : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ z = 0 ↔
      Coplanar ({0, x, y, z} : Set V3) := sorry

/-- HOL `SUBSET_NOT_COLLINEAR_AFFINE_HULL_EQ` (local_lemmas.hl:219). -/
theorem SUBSET_NOT_COLLINEAR_AFFINE_HULL_EQ {a b c x y z : V3}
    (hsub : ({a, b, c} : Set V3) ⊆ affineSpan ℝ ({x, y, z} : Set V3))
    (hcol : ¬ Collinear ℝ ({a, b, c} : Set V3)) :
    affineSpan ℝ ({x, y, z} : Set V3) = affineSpan ℝ ({a, b, c} : Set V3) := sorry

/-- HOL `THREE_NOT_COLL_DETER_PLANE` (local_lemmas.hl:258). -/
theorem THREE_NOT_COLL_DETER_PLANE {P : Set V3} {a b c : V3} (hP : plane_p2 P)
    (hsub : ({a, b, c} : Set V3) ⊆ P)
    (hcol : ¬ Collinear ℝ ({a, b, c} : Set V3)) :
    affineSpan ℝ ({a, b, c} : Set V3) = P := sorry

/-- HOL `LOCAL_FAN_NOT_V_SING` (local_lemmas.hl:266). -/
theorem LOCAL_FAN_NOT_V_SING (h : localFan_p2 V E FF) : ¬ ∃ v : V3, V = {v} := sorry

/-- HOL `LOCAL_FAN_NOT_SING_FF` (local_lemmas.hl:288). -/
theorem LOCAL_FAN_NOT_SING_FF (h : localFan_p2 V E FF) :
    ¬ ∃ x : V3 × V3, FF = {x} := sorry

/-- HOL `LOCAL_FAN_IN_FF_DISTINCT` (local_lemmas.hl:309). -/
theorem LOCAL_FAN_IN_FF_DISTINCT (h : localFan_p2 V E FF) {d : V3 × V3}
    (hd : d ∈ FF) : d.1 ≠ d.2 := sorry


/-- HOL `LOCAL_FAN_IN_FF_IN_ORD_PAIRS` (local_lemmas.hl:338). -/
theorem LOCAL_FAN_IN_FF_IN_ORD_PAIRS (h : localFan_p2 V E FF) {d : V3 × V3}
    (hd : d ∈ FF) : d ∈ ordPairs_p2 E := sorry

/-- HOL `LOCAL_FAN_IN_FF_NOT_COLLINEAR` (local_lemmas.hl:364). -/
theorem LOCAL_FAN_IN_FF_NOT_COLLINEAR (h : localFan_p2 V E FF) {d : V3 × V3}
    (hd : d ∈ FF) : ¬ Collinear ℝ ({0, d.1, d.2} : Set V3) := sorry

/-- HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE` (local_lemmas.hl:377). -/
theorem LOCAL_FAN_CHARACTER_OF_RHO_NODE (h : localFan_p2 V E FF) {v : V3}
    (hv : v ∈ V) :
    rhoNode1_p2 FF v ≠ v ∧ (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 E ∧
      ¬ Collinear ℝ ({0, v, rhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `graph2` (local_lemmas.hl:393). -/
theorem graph2 (E : Set (Set V3)) :
    Graph E ↔ ∀ e ∈ E, e.Finite ∧ e.ncard = 2 := by
  constructor
  · intro h e he
    obtain ⟨hf, hc⟩ := h e he
    refine ⟨hf, ?_⟩
    rw [Set.ncard_eq_toFinset_card e hf]
    exact hc
  · intro h e he
    obtain ⟨hf, hc⟩ := h e he
    refine ⟨hf, ?_⟩
    rw [← Set.ncard_eq_toFinset_card e hf]
    exact hc

/-- HOL `GRAPH_WITH_SET2` (local_lemmas.hl:396). -/
theorem GRAPH_WITH_SET2 (h : Graph E) : ∀ a b : V3, ({a, b} : Set V3) ∈ E → a ≠ b := by
  intro a b he
  obtain ⟨hf, hc⟩ := ((graph2 E).mp h) _ he
  intro h0
  have hcard : ({a, b} : Set V3).ncard = 1 := by
    rw [h0]
    simp
  rw [hcard] at hc
  simp at hc

/-- HOL `FAN_V_TWO_ELMS_IN_E_DARTS2` (local_lemmas.hl:403). -/
theorem FAN_V_TWO_ELMS_IN_E_DARTS2 {v1 v2 : V3} (hfan : FAN 0 V E)
    (hV : V = {v1, v2}) (he : ({v1, v2} : Set V3) ∈ E) :
    dartsOfHyp_p2 E V = ({(v1, v2), (v2, v1)} : Set (V3 × V3)) := by
  obtain ⟨hsub0, hgraph, hfin, hapex, hfan6, hfan7⟩ := hfan
  have hVmem : ∀ z ∈ V, z = v1 ∨ z = v2 := by
    intro z hz
    rw [hV] at hz
    simpa using hz
  have hno1 : ∀ z : V3, ({z} : Set V3) ∉ E := by
    intro z hz
    obtain ⟨hf, hc⟩ := hgraph _ hz
    have h1 : hf.toFinset = ({z} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset]
    rw [h1] at hc
    simp at hc
  have hv2EE : v2 ∈ EE_p2 v1 E := by
    show ({v1, v2} : Set V3) ∈ E
    exact he
  have hv1EE : v1 ∈ EE_p2 v2 E := by
    show ({v2, v1} : Set V3) ∈ E
    rw [Set.pair_comm]
    exact he
  have hselfE : selfPairs_p2 E V = ∅ := by
    ext p
    constructor
    · intro h3
      simp only [selfPairs_p2, Set.mem_setOf_eq] at h3
      rcases hVmem p.1 h3.2.1 with z | z
      · rw [z] at h3
        rw [h3.2.2] at hv2EE
        exact absurd hv2EE (by simp)
      · rw [z] at h3
        rw [h3.2.2] at hv1EE
        exact absurd hv1EE (by simp)
    · intro h3
      exact absurd h3 (by simp)
  have hord : ordPairs_p2 E = ({(v1, v2), (v2, v1)} : Set (V3 × V3)) := by
    ext p
    simp only [ordPairs_p2, Set.mem_setOf_eq]
    constructor
    · intro ho
      have hsub : ({p.1, p.2} : Set V3) ⊆ {v1, v2} := by
        rw [← hV]
        exact (Set.subset_sUnion_of_mem ho).trans hsub0
      have hm1 : p.1 = v1 ∨ p.1 = v2 := by
        simpa using hsub (Set.mem_insert p.1 ({p.2} : Set V3))
      have hm2 : p.2 = v1 ∨ p.2 = v2 := by
        simpa using hsub (Set.mem_insert_of_mem p.1 rfl)
      rcases hm1 with z1 | z1
      · rcases hm2 with z2 | z2
        · exfalso
          refine hno1 v1 ?_
          have heq : ({p.1, p.2} : Set V3) = ({v1} : Set V3) := by
            simp [z1, z2]
          rw [← heq]
          exact ho
        · left
          exact (by
            have hpe : (p.1, p.2) = p := Prod.mk.eta
            rw [← hpe, z1, z2])
      · rcases hm2 with z2 | z2
        · right
          exact (by
            have hpe : (p.1, p.2) = p := Prod.mk.eta
            rw [← hpe, z1, z2]
            simp)
        · exfalso
          refine hno1 v2 ?_
          have heq : ({p.1, p.2} : Set V3) = ({v2} : Set V3) := by
            simp [z1, z2]
          rw [← heq]
          exact ho
    · intro ho
      rcases Set.mem_insert_iff.mp ho with h | h
      · rw [h]
        exact he
      · rw [h, Set.pair_comm]
        exact he
  ext d
  show d ∈ (ordPairs_p2 E ∪ selfPairs_p2 E V) ↔
    d ∈ ({(v1, v2), (v2, v1)} : Set (V3 × V3))
  rw [hselfE, hord]
  constructor
  · intro hd
    rcases Set.mem_or_mem_of_mem_union hd with h | h
    · exact h
    · exact absurd h (by simp)
  · intro hd
    exact Set.mem_union_left _ hd

/-- HOL `FAN_IN_E_DIFF` (local_lemmas.hl:434). -/
theorem FAN_IN_E_DIFF (hfan : FAN 0 V E) : ∀ x y : V3, ({x, y} : Set V3) ∈ E →
    (x, y) ≠ (y, x) := by
  intro x y he h0
  have h1 : x ≠ y := GRAPH_WITH_SET2 hfan.2.1 x y he
  exact absurd (by rw [Prod.mk.injEq] at h0; exact h0.1) h1

/-- HOL `LOCAL_FAN_NOT_TWO_V_IN_E` (local_lemmas.hl:441). -/
theorem LOCAL_FAN_NOT_TWO_V_IN_E (h : localFan_p2 V E FF) :
    ¬ ∃ v1 v2 : V3, V = {v1, v2} ∧ ({v1, v2} : Set V3) ∈ E := sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_V` (local_lemmas.hl:469). -/
theorem LOCAL_FAN_ORBIT_MAP_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    orbitF_p2 (rhoNode1_p2 FF) v = V := sorry

/-- HOL `LOCAL_FAN_RHO_NODE_PROS2` (local_lemmas.hl:486): the conjunction of
`LOCAL_FAN_RHO_NODE_PROS` in swapped order. -/
theorem LOCAL_FAN_RHO_NODE_PROS2 (h : localFan_p2 V E FF) :
    (∀ x ∈ FF, x = (x.1, rhoNode1_p2 FF x.1)) ∧
      ∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF :=
  ⟨(LOCAL_FAN_RHO_NODE_PROS h).2, (LOCAL_FAN_RHO_NODE_PROS h).1⟩

/-- HOL `FINTE_OF_N_FIRST_ELMS2` (local_lemmas.hl:490). -/
theorem FINTE_OF_N_FIRST_ELMS2 {α : Type*} (f : α → α) (x : α) (i : ℕ) :
    ({f^[n] x | n < i} : Set α).Finite :=
  Set.Finite.image (fun n => f^[n] x) (Set.finite_Iio i)

/-- HOL `PLANE_AFFINE_HUL_INTER_P` (local_lemmas.hl:497). -/
theorem PLANE_AFFINE_HUL_INTER_P {P : Set V3} {x y z : V3} (hP : plane_p2 P)
    (hsub : ({x, y, z} : Set V3) ⊆ P) :
    ((affineSpan ℝ ({x, (WithLp.toLp 2 (crossProduct ((y - x : V3) : Fin 3 → ℝ)
      ((z - x : V3) : Fin 3 → ℝ)) : V3) + x} : Set V3) : Set V3) ∩ P) = {x} := sorry

/-- HOL `FAN_IMP_V_DIFF` (local_lemmas.hl:526). -/
theorem FAN_IMP_V_DIFF {x : V3} (hfan : FAN x V E) : ∀ v ∈ V, v ≠ x := by
  intro v hv he
  exact hfan.2.2.2.1 (he ▸ hv)

/-- HOL `LOCAL_FAN_IMP_CYCLIC_SET` (local_lemmas.hl:534). -/
theorem LOCAL_FAN_IMP_CYCLIC_SET (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3}
    (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U) {P : Set V3} (hP : plane_p2 P)
    (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    cyclicSet_p3 U 0 e := sorry

/-- HOL `LOCAL_FAN_ITER_RHO_NODE_IN_V` (local_lemmas.hl:652). -/
theorem LOCAL_FAN_ITER_RHO_NODE_IN_V (h : localFan_p2 V E FF) {v : V3}
    (hv : v ∈ V) : ∀ i : ℕ, (rhoNode1_p2 FF)^[i] v ∈ V := sorry


/-- HOL `ORD2_ORBIT_MAP` (local_lemmas.hl:663). -/
theorem ORD2_ORBIT_MAP {α : Type*} {f : α → α} {x : α} (h : f (f x) = x) :
    orbitF_p2 f x = ({x, f x} : Set α) := by
  have hiter : ∀ n : ℕ, f^[n] x = x ∨ f^[n] x = f x := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ m ih =>
      rcases m with _ | k
      · exact Or.inr rfl
      · rcases ih with h1 | h1
        · rw [Function.iterate_succ_apply', h1]
          exact Or.inr rfl
        · rw [Function.iterate_succ_apply', h1, h]
          exact Or.inl rfl
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := hy
    rcases hiter n with h1 | h1
    · exact Or.inl (hn.symm.trans h1)
    · exact Or.inr (hn.symm.trans h1)
  · intro hy
    rcases hy with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

/-- HOL `LOCAL_FAN_IMP_NOT_SEMI_IDE` (local_lemmas.hl:671). -/
theorem LOCAL_FAN_IMP_NOT_SEMI_IDE (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    rhoNode1_p2 FF (rhoNode1_p2 FF v) ≠ v := sorry

/-- HOL `RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT` (local_lemmas.hl:689). -/
theorem RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT (h : localFan_p2 V E FF) {v : V3}
    (hv : v ∈ V) {l : ℕ} {U : Set V3}
    (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U) {P : Set V3} (hP : plane_p2 P)
    (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    ∀ i : ℕ, i < l →
      0 < ((WithLp.toLp 2 (crossProduct
          (((rhoNode1_p2 FF)^[i] v : V3) : Fin 3 → ℝ)
          (((rhoNode1_p2 FF)^[i + 1] v : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (e : V3)) := sorry

/-- HOL `AZIM_RANGE` (local_lemmas.hl:918). -/
theorem AZIM_RANGE (v w w1 w2 : V3) :
    0 ≤ azim v w w1 w2 ∧ azim v w w1 w2 < 2 * Real.pi :=
  ⟨azim_nonneg v w w1 w2, azim_lt_two_pi v w w1 w2⟩

/-- HOL `PI_TO_TWO_PI_NEG_SIN` (local_lemmas.hl:924). -/
theorem PI_TO_TWO_PI_NEG_SIN : ∀ x : ℝ, Real.pi < x → x < 2 * Real.pi →
    Real.sin x < 0 := by
  intro x h1 h2
  have h3 : Real.sin (x - Real.pi) > 0 :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [show Real.sin x = -Real.sin (x - Real.pi) from by
    rw [Real.sin_sub]; simp [Real.cos_pi, Real.sin_pi]]
  linarith

/-- HOL `MIXED_PROD_POS_IMP_RANGE_AZIM` (local_lemmas.hl:937). -/
theorem MIXED_PROD_POS_IMP_RANGE_AZIM {u v w : V3}
    (h1 : ¬ Collinear ℝ ({0, u, v} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u, w} : Set V3))
    (h3 : 0 < (WithLp.toLp 2 (crossProduct ((u : V3) : Fin 3 → ℝ)
      ((v : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (w : V3)) :
    0 < azim 0 u v w ∧ azim 0 u v w < Real.pi := sorry

/-- HOL `COLLINEAR_ONCE_VEC_0` (local_lemmas.hl:973). -/
theorem COLLINEAR_ONCE_VEC_0 {x : V3} (hx : x ≠ 0) (y : V3) :
    Collinear ℝ ({0, x, y} : Set V3) ↔ ∃ t : ℝ, y = t • x := by
  have hx' : (0:V3) ≠ x := fun h => hx h.symm
  constructor
  · intro hcol
    rcases (collinear_triple_iff (x := (0:V3)) (v := x) (u := y)).mp hcol with
      hmem | h0
    · obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
      refine ⟨r, ?_⟩
      have h2 := hr
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, sub_zero,
        smul_zero, add_zero] at h2
      exact h2.symm
    · exact absurd h0 hx'
  · intro ht
    obtain ⟨t, ht2⟩ := ht
    have hmem : y ∈ affineSpan ℝ ({0, x} : Set V3) :=
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, by
        rw [AffineMap.lineMap_apply, ht2]
        simp⟩
    exact (collinear_triple_iff (x := (0:V3)) (v := x) (u := y)).mpr
      (Or.inl hmem)

/-- HOL `AFF_GE11` (local_lemmas.hl:984). -/
theorem AFF_GE11 (x v : V3) (hxv : x ≠ v) :
    affGe ({x} : Set V3) ({v} : Set V3) =
      {y : V3 | ∃ t1 t2 : ℝ, 0 ≤ t2 ∧ t1 + t2 = 1 ∧ y = t1 • x + t2 • v} := by
  have hfin : (({x} ∪ {v} : Set V3) : Set V3).Finite := by simp
  have hEq : hfin.toFinset = ({x, v} : Finset V3) := by
    ext w
    simp [Set.Finite.mem_toFinset, hxv]
    tauto
  ext y
  constructor
  · intro hy
    obtain ⟨f, hf, hy2, hsgn, hsum⟩ := hy
    rw [hEq] at hy2 hsum
    have hy3 : y = f x • x + f v • v := by simpa [hxv] using hy2
    have hs3 : f x + f v = 1 := by simpa [hxv] using hsum
    exact ⟨f x, f v, hsgn v (by simp), hs3, hy3⟩
  · intro hy
    obtain ⟨t1, t2, ht2, hsum, hy2⟩ := hy
    refine ⟨fun w => if w = v then t2 else if w = x then t1 else 0, hfin, ?_, ?_, ?_⟩
    · rw [hy2, hEq]
      simp [hxv]
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw]
      simp
      exact ht2
    · rw [hEq]
      simp [hxv, hsum]

/-- HOL `X_IN_AFF_GE11` (local_lemmas.hl:990). -/
theorem X_IN_AFF_GE11 (x c : V3) (hcx : c ≠ x) : x ∈ affGe ({c} : Set V3) ({x} : Set V3) := by
  rw [AFF_GE11 c x hcx]
  refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
  simp

/-- HOL `FAN_IN_AFF_GE_IMP_EQ` (local_lemmas.hl:996). -/
theorem FAN_IN_AFF_GE_IMP_EQ {x a b v : V3} (hfan : FAN x V E) (hv : v ∈ V)
    (he : ({a, b} : Set V3) ∈ E) (hmem : v ∈ affGe ({x} : Set V3) ({a, b} : Set V3)) :
    v = a ∨ v = b := sorry

/-- HOL `AFF_GE22` (local_lemmas.hl:1030). -/
theorem AFF_GE22 (a b x y : V3) (hdis : Disjoint ({a, b} : Set V3) ({x, y} : Set V3)) :
    affGe ({a, b} : Set V3) ({x, y} : Set V3) =
      {z : V3 | ∃ aa bb xx yy : ℝ, 0 ≤ xx ∧ 0 ≤ yy ∧
        aa + bb + xx + yy = 1 ∧ z = aa • a + bb • b + xx • x + yy • y} := sorry

/-- HOL `RHO_NODE_IS_SUCCESEOR_AZIM` (local_lemmas.hl:1034). -/
theorem RHO_NODE_IS_SUCCESEOR_AZIM (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    ∀ x : V3, ∀ n : ℕ, x = (rhoNode1_p2 FF)^[n] v → n < l →
      ∀ y : V3, y ∈ U → y ≠ x → y ≠ rhoNode1_p2 FF x →
        azim 0 e x (rhoNode1_p2 FF x) < azim 0 e x y := sorry

/-- HOL `FIRST_AZIM_CYCLE_EQ_RHO_NODE` (local_lemmas.hl:1204). -/
theorem FIRST_AZIM_CYCLE_EQ_RHO_NODE (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    ∀ x : V3, ∀ n : ℕ, x = (rhoNode1_p2 FF)^[n] v → n < l →
      azimCycle_p2 U 0 e x = rhoNode1_p2 FF x := sorry

/-- HOL `SEQUENCE_OF_RHO_NODE_IS_SUC` (local_lemmas.hl:1270). -/
theorem SEQUENCE_OF_RHO_NODE_IS_SUC (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    ∀ x : V3, ∀ n : ℕ, x = (rhoNode1_p2 FF)^[n] v → n < l →
      ∀ y : V3, y ∈ U → y ≠ x → y ≠ rhoNode1_p2 FF x →
        azim 0 e y x < azim 0 e y (rhoNode1_p2 FF x) := sorry

/-- HOL `V_AZIM_SMALLEST_ELMS` (local_lemmas.hl:1469). -/
theorem V_AZIM_SMALLEST_ELMS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) {ls : V3}
    (hls : (rhoNode1_p2 FF)^[l] v = ls)
    (hlsne : ∀ i : ℕ, i < l → ls ≠ (rhoNode1_p2 FF)^[i] v) :
    ∀ y : V3, y ∈ U → y ≠ v → y ≠ ls → azim 0 e ls v < azim 0 e ls y := sorry


/-- HOL `AZIM_LAST_POINT_IN_RHO_SET` (local_lemmas.hl:1566). -/
theorem AZIM_LAST_POINT_IN_RHO_SET (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) {ls : V3}
    (hls : (rhoNode1_p2 FF)^[l] v = ls)
    (hlsne : ∀ i : ℕ, i < l → ls ≠ (rhoNode1_p2 FF)^[i] v) :
    azimCycle_p2 U 0 e ls = v := sorry

/-- HOL `LOOP_MAP_IMP_DIFF_FIRST_ELMS` (local_lemmas.hl:1625). -/
theorem LOOP_MAP_IMP_DIFF_FIRST_ELMS {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V) {k l : ℕ}
    (hk : k < V.ncard) (hl : l < k) : f^[k] v ≠ f^[l] v := sorry

/-- HOL `CARD_IMAGE_INJ2` (local_lemmas.hl:1656). -/
theorem CARD_IMAGE_INJ2 {α β : Type*} {f : α → β} {A : Set α} {B : Set β}
    (h : Set.InjOn f A) (hfin : A.Finite) : (Set.image f A).ncard = A.ncard :=
  Set.InjOn.ncard_image h

/-- HOL `BIJ_IMP_CARD_EQ` (local_lemmas.hl:1663). -/
theorem BIJ_IMP_CARD_EQ {α β : Type*} {f : α → β} {A : Set α} {B : Set β}
    (h : Set.BijOn f A B) (hfin : A.Finite) : A.ncard = B.ncard := by
  have h2 : Set.image f A = B := h.image_eq
  rw [← h2, Set.InjOn.ncard_image h.injOn]

/-- HOL `LOFA_IMP_DIS_ELMS` (local_lemmas.hl:1669). -/
theorem LOFA_IMP_DIS_ELMS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} (hl : l < FF.ncard) :
    ∀ i : ℕ, i < l → (rhoNode1_p2 FF)^[l] v ≠ (rhoNode1_p2 FF)^[i] v := sorry

/-- HOL `AZIM_LAST_POINT_IN_RHO_SET2` (local_lemmas.hl:1684). -/
theorem AZIM_LAST_POINT_IN_RHO_SET2 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) {ls : V3}
    (hls : (rhoNode1_p2 FF)^[l] v = ls) (hcard : l < FF.ncard) :
    azimCycle_p2 U 0 e ls = v := sorry

/-- HOL `KOMWBWC` (local_lemmas.hl:1703). -/
theorem KOMWBWC {E_ : Set (Set V3)} {V_ P U : Set V3} {l : ℕ} {FF_ : Set (V3 × V3)}
    {e ls v : V3}
    (h : localFan_p2 V_ E_ FF_) (hv : v ∈ V_)
    (hU : {(rhoNode1_p2 FF_)^[n] v | n ≤ l} = U)
    (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P)
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF_ v : V3) : Fin 3 → ℝ)) : V3) = e) :
    cyclicSet_p3 U 0 e ∧
      (∀ i : ℕ, i < l →
        0 < ((WithLp.toLp 2 (crossProduct
            (((rhoNode1_p2 FF_)^[i] v : V3) : Fin 3 → ℝ)
            (((rhoNode1_p2 FF_)^[i + 1] v : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (e : V3))) ∧
      (∀ x : V3, ∀ n : ℕ, x = (rhoNode1_p2 FF_)^[n] v → n < l →
        azimCycle_p2 U 0 e x = rhoNode1_p2 FF_ x) ∧
      ((rhoNode1_p2 FF_)^[l] v = ls → l < FF_.ncard → azimCycle_p2 U 0 e ls = v) := sorry

/-- HOL `WEDGE_GE_AZIM_LE` (local_lemmas.hl:1741). -/
theorem WEDGE_GE_AZIM_LE (x v0 v1 w1 w2 : V3) :
    x ∈ wedgeGe_p2 v0 v1 w1 w2 ↔ azim v0 v1 w1 x ≤ azim v0 v1 w1 w2 := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨azim_nonneg v0 v1 w1 x, h⟩

/-- HOL `IN_WEDGE_IMP_AZIM_LE` (local_lemmas.hl:1747). -/
theorem IN_WEDGE_IMP_AZIM_LE {v0 v1 w1 w2 x y : V3} (hy : y ∈ wedgeGe_p2 v0 v1 w1 w2)
    (hxy : azim v0 v1 w1 x ≤ azim v0 v1 w1 y)
    (hx : ¬ Collinear ℝ ({v0, v1, x} : Set V3))
    (hy2 : ¬ Collinear ℝ ({v0, v1, y} : Set V3))
    (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3)) :
    azim v0 v1 x y ≤ azim v0 v1 w1 w2 := sorry

/-- HOL `LOFA_IMAGE_RHO_NODE_IDE` (local_lemmas.hl:1762). -/
theorem LOFA_IMAGE_RHO_NODE_IDE (h : localFan_p2 V E FF) :
    Set.image (rhoNode1_p2 FF) V = V := sorry

/-- HOL `EXISTS_INVERSE_OF_V` (local_lemmas.hl:1769). -/
theorem EXISTS_INVERSE_OF_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∃ vv : V3, vv ∈ V ∧ rhoNode1_p2 FF vv = v := sorry

/-- HOL `LOFA_IN_V_SO_DO_RHO_NODE_V` (local_lemmas.hl:1776). -/
theorem LOFA_IN_V_SO_DO_RHO_NODE_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    rhoNode1_p2 FF v ∈ V := sorry

/-- HOL `HYP_MAPS_INVERSABLE` (local_lemmas.hl:1784): the hypermap maps are
invertible; in the Lean encoding the maps are `Equiv.Perm`s, so this is
mechanical. -/
theorem HYP_MAPS_INVERABLE {α : Type*} [DecidableEq α] (H : Hypermap α) :
    H.faceMap.symm.trans H.faceMap = Equiv.refl α ∧
      H.nodeMap.symm.trans H.nodeMap = Equiv.refl α ∧
      H.edgeMap.symm.trans H.edgeMap = Equiv.refl α ∧
      H.faceMap.trans H.faceMap.symm = Equiv.refl α ∧
      H.nodeMap.trans H.nodeMap.symm = Equiv.refl α ∧
      H.edgeMap.trans H.edgeMap.symm = Equiv.refl α := by
  refine ⟨Equiv.symm_trans_self _, Equiv.symm_trans_self _, Equiv.symm_trans_self _,
    ?_, ?_, ?_⟩
  · ext z
    simp
  · ext z
    simp
  · ext z
    simp

/-- HOL `LOFA_DARTS_FF_UNION_SWITCH_FF` (local_lemmas.hl:1795). -/
theorem LOFA_DARTS_FF_UNION_SWITCH_FF (h : localFan_p2 V E FF) :
    dartsOfHyp_p2 E V = FF ∪ {p : V3 × V3 | (p.2, p.1) ∈ FF} := sorry

/-- HOL `SELF_CYCLIC_IMP_FINITE` (local_lemmas.hl:1843): the orbit condition
forces finiteness (in HOL via the cyclic-orbit machinery; the plain-function
rendering keeps the statement, see the HL proof's `ITER_CYCLIC_ORBIT`). -/
theorem SELF_CYCLIC_IMP_FINITE {α : Type*} (f : α → α) (V : Set α)
    (h : ∀ x ∈ V, V = orbitF_p2 f x) : V.Finite := sorry


/-- HOL `SELF_CYCLIC_IMP_BIJ` (local_lemmas.hl:1879). -/
theorem SELF_CYCLIC_IMP_BIJ {α : Type*} (f : α → α) (S : Set α)
    (h : ∀ x ∈ S, S = orbitF_p2 f x) : Set.BijOn f S S := sorry

/-- HOL `LOFA_IN_E_IMP_IN_FF` (local_lemmas.hl:1887). -/
theorem LOFA_IN_E_IMP_IN_FF (h : localFan_p2 V E FF) {a b : V3}
    (he : ({a, b} : Set V3) ∈ E) : (a, b) ∈ FF ∨ (b, a) ∈ FF := sorry

/-- HOL `LOFA_IMP_EE_TWO_ELMS` (local_lemmas.hl:1899). -/
theorem LOFA_IMP_EE_TWO_ELMS (h : localFan_p2 V E FF) {vv v : V3} (hvv : vv ∈ V)
    (hr : rhoNode1_p2 FF vv = v) : EE_p2 v E = {rhoNode1_p2 FF v, vv} := sorry

/-- HOL `LOFA_CARD_EE_V_2` (local_lemmas.hl:1959). -/
theorem LOFA_CARD_EE_V_2 (h : localFan_p2 V E FF) {vv v : V3} (hvv : vv ∈ V)
    (hr : rhoNode1_p2 FF vv = v) : (EE_p2 v E).ncard = 2 := by
  have hne : rhoNode1_p2 FF v ≠ vv := by
    rw [← hr]
    exact LOCAL_FAN_IMP_NOT_SEMI_IDE h hvv
  rw [LOFA_IMP_EE_TWO_ELMS h hvv hr]
  have h2 : ({rhoNode1_p2 FF v, vv} : Set V3)
      = insert (rhoNode1_p2 FF v) ({vv} : Set V3) := rfl
  rw [h2, Set.ncard_insert_of_notMem (by simp [hne])]
  simp

/-- HOL `LOFA_CARD_EE_V_1` (local_lemmas.hl:1967). -/
theorem LOFA_CARD_EE_V_1 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    (EE_p2 v E).ncard = 2 := sorry

/-- HOL `RHO_NODE_INVERSE_POINT` (local_lemmas.hl:1976). -/
theorem RHO_NODE_INVERSE_POINT {w v : V3} (hw : (w, v) ∈ FF)
    (hun : ∀ ww : V3, (ww, v) ∈ FF → ww = w) : ivsRhoNode1_p2 FF v = w :=
  epsilonFixed hw hun

/-- HOL `AZIM_CYCLE_TWO_POINT_SET` (local_lemmas.hl:1982). -/
theorem AZIM_CYCLE_TWO_POINT_SET (a b v w : V3) :
    azimCycle_p2 ({a, b} : Set V3) v w a = b := by
  by_cases hab : a = b
  · subst hab
    rw [azimCycle_p2]
    exact if_pos (by simp)
  · have hcond : ¬(({a, b} : Set V3) ⊆ ({a} : Set V3)) := by
      intro hsub
      exact hab (hsub (Set.mem_insert_of_mem a rfl : b ∈ ({a, b} : Set V3))).symm
    rw [azimCycle_p2, if_neg hcond]
    refine epsilonFixed ?_ ?_
    · refine ⟨fun h => hab h.symm, by simp, ?_⟩
      intro q hq hqa
      rcases Set.mem_insert_iff.mp hq with h | h
      · exact absurd h hqa
      · rw [h]
        exact Or.inr ⟨rfl, le_rfl⟩
    · intro u hu
      rcases Set.mem_insert_iff.mp hu.2.1 with h | h
      · exact absurd h hu.1
      · exact h

/-- HOL `LOFA_IMP_BIJ_VV` (local_lemmas.hl:2016). -/
theorem LOFA_IMP_BIJ_VV (h : localFan_p2 V E FF) :
    Set.BijOn (rhoNode1_p2 FF) V V := sorry

/-- HOL `MOST_EXPAND_IN_WEDGE_GE` (local_lemmas.hl:2027). -/
theorem MOST_EXPAND_IN_WEDGE_GE {v0 v1 w1 w2 x y : V3}
    (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3))
    (hw2 : ¬ Collinear ℝ ({v0, v1, w2} : Set V3))
    (hx : ¬ Collinear ℝ ({v0, v1, x} : Set V3))
    (hy : ¬ Collinear ℝ ({v0, v1, y} : Set V3))
    (hyw : y ∈ wedgeGe_p2 v0 v1 w1 w2)
    (hxy : azim v0 v1 w1 x ≤ azim v0 v1 w1 y)
    (heq : azim v0 v1 x y = azim v0 v1 w1 w2) :
    azim v0 v1 w1 x = 0 ∧ azim v0 v1 y w2 = 0 := sorry

/-- HOL `OZQVSFF` (local_lemmas.hl:2056). -/
theorem OZQVSFF (h : convexLocalFan_p2 V E FF) {u v w : V3} {P : Set V3}
    (hsub : ({u, v, w} : Set V3) ⊆ V) (hP : plane_p2 P)
    (hsub2 : ({0, u, v, w} : Set V3) ⊆ P)
    (hdis : ({u, w} : Set V3) ∩ affineSpan ℝ ({0, v} : Set V3) = ∅)
    (hne : ¬ (((affineSpan ℝ ({v, 0} : Set V3) : Set V3) ∩
      conv0_p2 ({w, u} : Set V3)) = ∅)) :
    interiorAngle1_p2 0 FF v = Real.pi ∧
      rhoNode1_p2 FF v ∈ P ∧ ivsRhoNode1_p2 FF v ∈ P := sorry

/-- HOL `REAL_LT_DIV_NEG` (local_lemmas.hl:2230). -/
theorem REAL_LT_DIV_NEG {a b : ℝ} (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  div_pos_of_neg_of_neg ha hb

/-- HOL `IN_CONV0` (local_lemmas.hl:2235). -/
theorem IN_CONV0 {x y : V3} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((1 / (a + b)) • (a • x + b • y) : V3) ∈ conv0_p2 ({x, y} : Set V3) := by
  have habs : 0 < a + b := by linarith
  have hfin : ((∅ ∪ ({x, y} : Set V3) : Set V3)).Finite := by simp
  unfold conv0_p2
  by_cases hxy : x = y
  · subst hxy
    have hEq : hfin.toFinset = ({x} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset]
    refine ⟨fun w => if w = x then 1 else 0, hfin, ?_, ?_, ?_⟩
    · rw [hEq, Finset.sum_singleton]
      have hsc : 1 / (a + b) * a + 1 / (a + b) * b = 1 := by field_simp
      rw [smul_add, smul_smul, smul_smul, ← add_smul, hsc, one_smul]
      simp
    · intro w hw
      have hw2 : w = x := by simpa using hw
      rw [hw2]
      simp
    · rw [hEq, Finset.sum_singleton]
      simp
  · have hxN : y ≠ x := fun h => hxy h.symm
    have hEq : hfin.toFinset = ({x, y} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset]
    refine ⟨fun w => if w = x then a / (a + b) else if w = y then b / (a + b) else 0,
      hfin, ?_, ?_, ?_⟩
    · rw [hEq, Finset.sum_insert (by simp [hxy] : x ∉ ({y} : Finset V3)),
        Finset.sum_singleton]
      simp [hxy, hxN]
      rw [show a / (a + b) = (a + b)⁻¹ * a from by field_simp,
          show b / (a + b) = (a + b)⁻¹ * b from by field_simp]
      rw [smul_smul, smul_smul]
    · intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw
      · rw [hw]; simp [hxy, hxN]; exact div_pos ha habs
      · rw [hw]; simp [hxy, hxN]; exact div_pos hb habs
    · rw [hEq, Finset.sum_insert (by simp [hxy] : x ∉ ({y} : Finset V3)),
        Finset.sum_singleton]
      simp [hxy, hxN]
      field_simp

/-- HOL `INTERSECTION_LEMMA` (local_lemmas.hl:2261). -/
theorem INTERSECTION_LEMMA {x z u v w : V3} (hxz : z ≠ x)
    (hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3)) (hxu : x ≠ u)
    (hne : ¬ (affGt ({x} : Set V3) ({v, w} : Set V3) ∩
      affLt ({x} : Set V3) ({u} : Set V3) = ∅))
    (hz : z ∈ affineSpan ℝ ({x, v, w} : Set V3)) :
    ∃ a b t : V3, ({a, b} : Set V3) ⊆ ({u, v, w} : Set V3) ∧
      t ∈ ((affineSpan ℝ ({x, z} : Set V3) : Set V3) ∩
        conv0_p2 ({a, b} : Set V3)) := sorry

/-- HOL `CVX_LO_IMP_LO` (local_lemmas.hl:2531). -/
theorem CVX_LO_IMP_LO (h : convexLocalFan_p2 V E FF) : localFan_p2 V E FF := h.1

/-- HOL `S_SUBSET_IMP_AFF_S_TOO` (local_lemmas.hl:2536). -/
theorem S_SUBSET_IMP_AFF_S_TOO {S SS : Set V3} (h : S ⊆ (affineSpan ℝ SS : Set V3)) :
    (affineSpan ℝ S : Set V3) ⊆ (affineSpan ℝ SS : Set V3) := by
  intro z hmem
  have hz := affineSpan_mono ℝ h hmem
  rwa [AffineSubspace.affineSpan_coe] at hz


/-- HOL `AFF2_DET_BY_TWO_POINTS` (local_lemmas.hl:2542). -/
theorem AFF2_DET_BY_TWO_POINTS {a b x y : V3} (hsub : ({x, y} : Set V3) ⊆
    ((affineSpan ℝ ({a, b} : Set V3) : Set V3))) (hxy : x ≠ y) :
    (affineSpan ℝ ({a, b} : Set V3) : Set V3) = (affineSpan ℝ ({x, y} : Set V3) : Set V3) := sorry

/-- HOL `IN_CONV0_EQ_EQ` (local_lemmas.hl:2560). -/
theorem IN_CONV0_EQ_EQ {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    x = a ↔ a = b := sorry

/-- HOL `IN_CONV0_IMP_AFF_EQ` (local_lemmas.hl:2580). -/
theorem IN_CONV0_IMP_AFF_EQ {x y a : V3} (ha : a ∈ conv0_p2 ({x, y} : Set V3)) :
    (affineSpan ℝ ({x, y} : Set V3) : Set V3) = (affineSpan ℝ ({x, a} : Set V3) : Set V3) := sorry

/-- HOL `IN_CONV0_AFF_SUBSET` (local_lemmas.hl:2600). -/
theorem IN_CONV0_AFF_SUBSET {a b x y t : V3} (ht : t ∈ ((affineSpan ℝ ({a, b} : Set V3) :
    Set V3) ∩ conv0_p2 ({x, y} : Set V3))) (hx : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3)) :
    (affineSpan ℝ ({x, y} : Set V3) : Set V3) ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := sorry

/-- HOL `CONDS_FOR_INTER_AFF_CONV0` (local_lemmas.hl:2611). -/
theorem CONDS_FOR_INTER_AFF_CONV0 {x v w u t : V3} {t1 t2 t3 t1' t2' ss : ℝ}
    (ht2 : 0 < t2) (ht3 : 0 < t3) (h1 : t1 + t2 + t3 = ss)
    (h2 : t = t1 • x + t2 • v + t3 • w) (h3 : t1' + t2' = ss)
    (h4 : t = t1' • x + t2' • u) :
    ∃ tt : V3, tt ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) ∩ conv0_p2 ({v, w} : Set V3) := sorry

/-- HOL `INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0` (local_lemmas.hl:2644). -/
theorem INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0 {x v w u t : V3}
    (hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3)) (hxu : u ≠ x)
    (ht : t ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩ affLt ({x} : Set V3) ({u} : Set V3)) :
    ∃ tt : V3, tt ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) ∩ conv0_p2 ({v, w} : Set V3) := sorry

/-- HOL `SUBSET_AFF2_IMP_COLL` (local_lemmas.hl:2657). -/
theorem SUBSET_AFF2_IMP_COLL {S : Set V3} {a b : V3}
    (h : S ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3)) : Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, fun z hz => ?_⟩
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (h hz)
  refine ⟨t, ?_⟩
  rw [← ht]
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]

/-- HOL `CONDS_IN_HAFL_LINE` (local_lemmas.hl:2670). -/
theorem CONDS_IN_HAFL_LINE {x a b : V3} {t : ℝ} (ht : 0 ≤ t)
    (heq : a - x = t • (b - x)) : a ∈ affGe ({x} : Set V3) ({b} : Set V3) := by
  have hfin : (({x} ∪ {b} : Set V3) : Set V3).Finite := by simp
  have hsplit : x + t • (b - x) = (1 - t) • x + t • b := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  by_cases hxb : x = b
  · subst hxb
    have hEq : hfin.toFinset = ({x} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset]
    have ha : a = x := by
      have h2 : a - x = (0:V3) := by rw [heq]; simp
      exact sub_eq_zero.mp h2
    refine ⟨fun w => if w = x then 1 else 0, hfin, ?_, ?_, ?_⟩
    · rw [hEq, Finset.sum_singleton]
      simp
      exact ha
    · intro w hw
      have hw2 : w = x := by simpa using hw
      rw [hw2]
      simp
    · rw [hEq, Finset.sum_singleton]
      simp
  · have hEq : hfin.toFinset = ({x, b} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset, hxb]
      tauto
    have hx' : x ∉ ({b} : Finset V3) := by simp [hxb]
    have hav : a = (1 - t) • x + t • b := by
      rw [sub_eq_iff_eq_add] at heq
      rw [heq, add_comm (t • (b - x)) x]
      rw [← hsplit]
    refine ⟨fun w => if w = b then t else if w = x then 1 - t else 0, hfin, ?_, ?_, ?_⟩
    · rw [hEq, Finset.sum_insert hx', Finset.sum_singleton]
      simp [hxb]
      rw [hav]
    · intro w hw
      have hw2 : w = b := by simpa using hw
      rw [hw2]
      simp
      exact ht
    · rw [hEq, Finset.sum_insert hx', Finset.sum_singleton]
      simp [hxb]

/-- HOL `PRESERABLE_AFF_GE_SUBSET` (local_lemmas.hl:2676). -/
theorem PRESERABLE_AFF_GE_SUBSET {x a b : V3} (ha : a ∈ affGe ({x} : Set V3) ({b} : Set V3)) :
    affGe ({x} : Set V3) ({a} : Set V3) ⊆ affGe ({x} : Set V3) ({b} : Set V3) := sorry

/-- HOL `AFF_GE_EQ` (local_lemmas.hl:2686). -/
theorem AFF_GE_EQ {x a b : V3} {t : ℝ} (ht : 0 < t) (heq : a - x = t • (b - x)) :
    affGe ({x} : Set V3) ({a} : Set V3) = affGe ({x} : Set V3) ({b} : Set V3) := sorry

/-- HOL `AFF2_ITR_CONV0_IMP_SAME_ENDS` (local_lemmas.hl:2709). -/
theorem AFF2_ITR_CONV0_IMP_SAME_ENDS {x y a b t : V3}
    (ht : t ∈ ((affineSpan ℝ ({x, y} : Set V3) : Set V3) ∩
      conv0_p2 ({a, b} : Set V3))) :
    (a ∈ affineSpan ℝ ({x, y} : Set V3) ↔ b ∈ affineSpan ℝ ({x, y} : Set V3)) := sorry

/-- HOL `AFF_XX_CASES` (local_lemmas.hl:2725). -/
theorem AFF_XX_CASES (x : V3) :
    affLt ({x} : Set V3) ({x} : Set V3) = (∅ : Set V3) ∧
      affLe ({x} : Set V3) ({x} : Set V3) = ∅ ∧
      affGt ({x} : Set V3) ({x} : Set V3) = ({x} : Set V3) := by
  constructor
  · ext v
    simp only [affLt, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · intro h
      obtain ⟨f, hf, hv2, hsgn, hsum⟩ := h
      have hEq : hf.toFinset = ({x} : Finset V3) := by
        ext w
        simp [Set.Finite.mem_toFinset]
      rw [hEq] at hv2 hsum
      simp at hv2 hsum
      have h1 := hsgn x (by simp)
      linarith
    · intro h
      exact absurd h (by simp)
  · refine ⟨?_, ?_⟩
    · ext v
      simp only [affLe, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · intro h
        obtain ⟨f, hf, hv2, hsgn, hsum⟩ := h
        have hEq : hf.toFinset = ({x} : Finset V3) := by
          ext w
          simp [Set.Finite.mem_toFinset]
        rw [hEq] at hv2 hsum
        simp at hv2 hsum
        have h1 := hsgn x (by simp)
        linarith
      · intro h
        exact absurd h (by simp)
    · ext v
      simp only [affGt, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        obtain ⟨f, hf, hv2, hsgn, hsum⟩ := h
        have hEq : hf.toFinset = ({x} : Finset V3) := by
          ext w
          simp [Set.Finite.mem_toFinset]
        rw [hEq] at hv2 hsum
        simp at hv2 hsum
        rw [hv2, hsum, one_smul]
      · intro h
        have hfin : (({x} ∪ {x} : Set V3) : Set V3).Finite := by simp
        have hEq : hfin.toFinset = ({x} : Finset V3) := by
          ext w
          simp [Set.Finite.mem_toFinset]
        refine ⟨fun w => if w = x then 1 else 0, hfin, ?_, ?_, ?_⟩
        · rw [hEq, Finset.sum_singleton]
          simp
          exact h
        · intro w hw
          have hw2 : w = x := by simpa using hw
          rw [hw2]
          simp
        · rw [hEq]
          simp

/-- HOL `NOT_X_IN_AFF_X_A` (local_lemmas.hl:2750). -/
theorem NOT_X_IN_AFF_X_A (x a : V3) : x ∉ affLt ({x} : Set V3) ({a} : Set V3) := by
  by_cases hxa : a = x
  · intro hx
    rw [hxa, (AFF_XX_CASES x).1] at hx
    exact hx
  · intro hx
    obtain ⟨f, hf, hv2, hsgn, hsum⟩ := hx
    have hfa : f a < 0 := hsgn a (by simp)
    have hxa' : x ≠ a := Ne.symm hxa
    have hEq : hf.toFinset = ({x, a} : Finset V3) := by
      ext w
      simp [Set.Finite.mem_toFinset, hxa]
      tauto
    rw [hEq] at hv2 hsum
    have hv3 : x = f x • x + f a • a := by
      have h2 : x ∉ ({a} : Finset V3) := by simpa using hxa'
      rw [Finset.sum_insert h2, Finset.sum_singleton] at hv2
      simpa using hv2
    have hs3 : f x + f a = 1 := by
      have h2 : x ∉ ({a} : Finset V3) := by simpa using hxa'
      rw [Finset.sum_insert h2, Finset.sum_singleton] at hsum
      simpa using hsum
    have h5 : f a • x - f a • a = 0 := by
      have hfx : f x = 1 - f a := by linarith
      rw [hfx] at hv3
      rw [sub_smul, one_smul] at hv3
      have h8 : x - (x - f a • x + f a • a) = 0 := by
        rw [← hv3, sub_self]
      abel_nf at h8 ⊢
      exact h8
    rw [sub_eq_zero] at h5
    have h6 : f a • (x - a) = 0 := by
      rw [smul_sub, h5, sub_self]
    rw [smul_eq_zero] at h6
    rcases h6 with h6 | h6
    · exact absurd (by linarith) (by norm_num : ¬((0:ℝ) < 0))
    · exact hxa (sub_eq_zero.mp h6).symm

/-- HOL `INTER_EQ_EM_EXPAND` (local_lemmas.hl:2766). -/
theorem INTER_EQ_EM_EXPAND {α : Type*} (A B : Set α) :
    A ∩ B = ∅ ↔ ¬ ∃ x, x ∈ A ∧ x ∈ B := by
  constructor
  · intro h hex
    obtain ⟨x, hx1, hx2⟩ := hex
    have hmem : x ∈ A ∩ B := ⟨hx1, hx2⟩
    rw [h] at hmem
    exact hmem
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact h ⟨x, hx.1, hx.2⟩


/-- HOL `NOT_INTER_EQ_EM_IMP_AFF_SUBSET` (local_lemmas.hl:2772). -/
theorem NOT_INTER_EQ_EM_IMP_AFF_SUBSET {x u v w x' : V3}
    (hx' : x' ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩ affLt ({x} : Set V3) ({u} : Set V3)) :
    (affineSpan ℝ ({x, u} : Set V3) : Set V3) ⊆ affineSpan ℝ ({x, v, w} : Set V3) := sorry

/-- HOL `IN_AFF_HULL_3` (local_lemmas.hl:2796). -/
theorem IN_AFF_HULL_3 {x u v w x' : V3}
    (hx' : x' ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩ affLt ({x} : Set V3) ({u} : Set V3)) :
    u ∈ affineSpan ℝ ({x, v, w} : Set V3) := sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_VITER` (local_lemmas.hl:2806): all iterates of
the rho-node stay in `V`. -/
theorem LOCAL_FAN_ORBIT_MAP_VITER (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    (n : ℕ) : (rhoNode1_p2 FF)^[n] v ∈ V :=
  LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n

/-- HOL `AFF_GT_AFF_LT_INTERPRET` (local_lemmas.hl:2821). -/
theorem AFF_GT_AFF_LT_INTERPRET {x u v w : V3} (hdis1 : Disjoint ({x} : Set V3) ({v, w} : Set V3))
    (hdis2 : Disjoint ({x} : Set V3) ({u} : Set V3)) :
    (∃ aa bb c : ℝ, aa < 0 ∧ 0 < bb ∧ 0 < c ∧
      aa • (u - x) = bb • (v - x) + c • (w - x)) ↔
      ∃ tt : V3, tt ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩
        affLt ({x} : Set V3) ({u} : Set V3) := sorry

/-- HOL `AFF_GT_AFF_LT_INTERPRET2` (local_lemmas.hl:2872): the
DISJOINT-union re-render of `AFF_GT_AFF_LT_INTERPRET`. -/
theorem AFF_GT_AFF_LT_INTERPRET2 {x u v w : V3}
    (hdis : Disjoint ({x} : Set V3) ({u, v, w} : Set V3)) :
    (∃ aa bb c : ℝ, aa < 0 ∧ 0 < bb ∧ 0 < c ∧
      aa • (u - x) = bb • (v - x) + c • (w - x)) ↔
      ∃ tt : V3, tt ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩
        affLt ({x} : Set V3) ({u} : Set V3) := by
  have h1 : Disjoint ({x} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_left]
    intro t ht hmem
    exact (Set.disjoint_left.mp hdis) ht (Set.mem_insert_of_mem u hmem)
  have h2 : Disjoint ({x} : Set V3) ({u} : Set V3) := by
    rw [Set.disjoint_left]
    intro t ht hmem
    have htu : t = u := by simpa using hmem
    exact Set.disjoint_left.mp hdis ht (by rw [htu]; exact Set.mem_insert u ({v, w} : Set V3))
  exact AFF_GT_AFF_LT_INTERPRET h1 h2

/-- HOL `EXISTS_IN` (local_lemmas.hl:2874). -/
theorem EXISTS_IN {α : Type*} (a : Set α) : a ≠ ∅ ↔ ∃ x, x ∈ a :=
  Set.nonempty_iff_ne_empty.symm

/-- HOL `AFF_GT_LT_INTER_SYM` (local_lemmas.hl:2877). -/
theorem AFF_GT_LT_INTER_SYM {x u v w : V3}
    (hdis : Disjoint ({x} : Set V3) ({u, v, w} : Set V3))
    (hne : ¬ (affGt ({x} : Set V3) ({v, w} : Set V3) ∩
      affLt ({x} : Set V3) ({u} : Set V3) = ∅)) :
    ¬ (affGt ({x} : Set V3) ({u, v} : Set V3) ∩
      affLt ({x} : Set V3) ({w} : Set V3) = ∅) := sorry

/-- HOL `EXISTS_INTERSECTION_PROPERPLY` (local_lemmas.hl:2897). -/
theorem EXISTS_INTERSECTION_PROPERPLY {x z u v w : V3} (hxz : z ≠ x)
    (hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3)) (hxu : x ≠ u)
    (hne : ¬ (affGt ({x} : Set V3) ({v, w} : Set V3) ∩
      affLt ({x} : Set V3) ({u} : Set V3) = ∅))
    (hz : z ∈ affineSpan ℝ ({x, v, w} : Set V3))
    (hcol : ¬ Collinear ℝ ({x, v, w} : Set V3)) :
    ∃ a b t : V3, ({a, b} : Set V3) ⊆ ({u, v, w} : Set V3) ∧
      t ∈ ((affineSpan ℝ ({x, z} : Set V3) : Set V3) ∩ conv0_p2 ({a, b} : Set V3)) ∧
      ¬(a ∈ (affineSpan ℝ ({x, z} : Set V3) : Set V3)) := sorry

/-- HOL `LOFA_V_SUBSET_AFF_HULL` (local_lemmas.hl:2990). -/
theorem LOFA_V_SUBSET_AFF_HULL {v w u : V3} (hFF : (v, w) ∈ FF)
    (h : convexLocalFan_p2 V E FF) (hu : u ∈ V)
    (hne : ¬ (affGt ({0} : Set V3) ({v, w} : Set V3) ∩
      affLt ({0} : Set V3) ({u} : Set V3) = ∅)) :
    V ⊆ (affineSpan ℝ ({v, w, 0} : Set V3) : Set V3) ∧
      ¬ Collinear ℝ ({0, v, w} : Set V3) := sorry

/-- HOL `DETER_RHO_NODE` (local_lemmas.hl:3093): the rho-node is determined
by the dart. -/
theorem DETER_RHO_NODE (h : localFan_p2 V E FF) {v w : V3} (hw : (v, w) ∈ FF) :
    rhoNode1_p2 FF v = w := sorry

/-- HOL `CARD_RECUSIVE_EQ` (local_lemmas.hl:3101). -/
theorem CARD_RECUSIVE_EQ {α : Type*} (f : α → α) (x : α) {k : ℕ} (hk : 0 < k) :
    ({f^[n] x | n < k} : Set α).ncard = k ↔
      ({f^[n] x | n < k - 1} : Set α).ncard = k - 1 ∧
        ∀ i : ℕ, i < k - 1 → f^[i] x ≠ f^[k - 1] x := sorry

/-- HOL `LE_CARDV_IMP_CARD_DETERED` (local_lemmas.hl:3129). -/
theorem LE_CARDV_IMP_CARD_DETERED {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V) :
    ∀ l : ℕ, l ≤ V.ncard → ({f^[n] v | n < l} : Set α).ncard = l := sorry

/-- HOL `LEMMA_SUBSET_ORBIT_MAP` (local_lemmas.hl:3149). -/
theorem LEMMA_SUBSET_ORBIT_MAP {α : Type*} (p : α → α) (x : α) (n : ℕ) :
    {p^[i] x | i ≤ n} ⊆ orbitF_p2 p x := by
  intro y hy
  obtain ⟨i, hi⟩ := hy
  exact ⟨i, hi.2⟩

/-- HOL `LEMMA_SUBSET_ORBIT_MAP_LT` (local_lemmas.hl:3153). -/
theorem LEMMA_SUBSET_ORBIT_MAP_LT {α : Type*} (p : α → α) (x : α) (n : ℕ) :
    {p^[i] x | i < n} ⊆ orbitF_p2 p x := by
  intro y hy
  obtain ⟨i, hi⟩ := hy
  exact ⟨i, hi.2⟩

/-- HOL `LOOP_SET_DETER_FIRTS_ELMS` (local_lemmas.hl:3161). -/
theorem LOOP_SET_DETER_FIRTS_ELMS {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ v ∈ V, orbitF_p2 f v = V) (v : α) (hv : v ∈ V) :
    {f^[n] v | n < V.ncard} = V := sorry


/-- HOL `lemma_in_orbit_iter` (local_lemmas.hl:3186). -/
theorem lemma_in_orbit_iter {α : Type*} (p : α → α) (x : α) (i : ℕ) :
    p^[i] x ∈ orbitF_p2 p x :=
  ⟨i, rfl⟩

/-- HOL `SIN_SUB_PERIODIC` (local_lemmas.hl:3191). -/
theorem SIN_SUB_PERIODIC (x : ℝ) : Real.sin x = -Real.sin (x - Real.pi) := by
  rw [Real.sin_sub]
  simp [Real.cos_pi, Real.sin_pi]

/-- HOL `KCHMAMG` (local_lemmas.hl:3197): the circular-fan characterization. -/
theorem KCHMAMG (h : convexLocalFan_p2 V E FF) (hc : circular_p2 V E) :
    (∀ v ∈ V, interiorAngle1_p2 0 FF v = Real.pi) ∧
      (∃ A : Set V3, plane_p2 A ∧ (0:V3) ∈ A ∧ V ⊆ A ∧
        (∃ e : V3, (∀ x ∈ A, e ⬝ᵥ x = 0) ∧
          cyclicSet_p3 V 0 e ∧
          (∀ v ∈ V, azimCycle_p2 V 0 e v = rhoNode1_p2 FF v ∧
            azim 0 e v (rhoNode1_p2 FF v) = dihV 0 e v (rhoNode1_p2 FF v) ∧
            azim 0 e v (rhoNode1_p2 FF v) = arcV 0 v (rhoNode1_p2 FF v) ∧
            azim 0 e v (rhoNode1_p2 FF v) < Real.pi))) := sorry

/-- HOL `AZIM_EQ_0_GE_ALT2` (local_lemmas.hl:3477). -/
theorem AZIM_EQ_0_GE_ALT2 (v0 v1 w x : V3) (hw : ¬ Collinear ℝ ({v0, v1, w} : Set V3)) :
    azim v0 v1 w x = 0 ↔ x ∈ affGe ({v0, v1} : Set V3) ({w} : Set V3) := sorry

/-- HOL `WEDGE_GE_EQ_AFF_GE` (local_lemmas.hl:3498). -/
theorem WEDGE_GE_EQ_AFF_GE {v0 v1 w1 w2 : V3} (hlt : azim v0 v1 w1 w2 < Real.pi)
    (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3))
    (hw2 : ¬ Collinear ℝ ({v0, v1, w2} : Set V3)) :
    wedgeGe_p2 v0 v1 w1 w2 = affGe ({v0, v1} : Set V3) ({w1, w2} : Set V3) := sorry

/-- HOL `AZIM_PI_WEDGE_GE_SIN` (local_lemmas.hl:3672). -/
theorem AZIM_PI_WEDGE_GE_SIN {u v w ww : V3} (h : azim u v w ww = Real.pi) :
    wedgeGe_p2 u v w ww = {x : V3 | 0 ≤ Real.sin (azim u v w x)} := sorry

/-- HOL `AZIM_PI_WEDGE_GE_CROSS_DOT` (local_lemmas.hl:3702). -/
theorem AZIM_PI_WEDGE_GE_CROSS_DOT {u v w ww : V3} (h : azim u v w ww = Real.pi) :
    wedgeGe_p2 u v w ww = {x : V3 |
      0 ≤ ((WithLp.toLp 2 (crossProduct ((v - u : V3) : Fin 3 → ℝ)
        ((w - u : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (x - u))} := sorry

/-- HOL `AZIM_PI_CONVEX_WEDGE` (local_lemmas.hl:3717). -/
theorem AZIM_PI_CONVEX_WEDGE {u v w ww : V3} (h : azim u v w ww = Real.pi) :
    Convex ℝ (wedgeGe_p2 u v w ww) := sorry

/-- HOL `CONVEX_WEDGE_LE_PI` (local_lemmas.hl:3735). -/
theorem CONVEX_WEDGE_LE_PI {v0 v1 w1 w2 : V3} (h : azim v0 v1 w1 w2 ≤ Real.pi)
    (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3))
    (hw2 : ¬ Collinear ℝ ({v0, v1, w2} : Set V3)) :
    Convex ℝ (wedgeGe_p2 v0 v1 w1 w2) := sorry

/-- HOL `wedge_in_fan_ge2` (local_lemmas.hl:3749). -/
theorem wedge_in_fan_ge2 (x : V3 × V3) (E : Set (Set V3)) :
    wedgeInFanGe_p2 x E =
      if 1 < (EE_p2 x.1 E).ncard then
        wedgeGe_p2 0 x.1 x.2 (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2)
      else {y : V3 | True} := by
  by_cases h : 1 < (EE_p2 x.1 E).ncard
  · simp [wedgeInFanGe_p2, h]
  · simp [wedgeInFanGe_p2, h]

/-- HOL `azim_in_fan2` (local_lemmas.hl:3760). -/
theorem azim_in_fan2 (x : V3 × V3) (E : Set (Set V3)) :
    azimInFan_p2 x E =
      if 1 < (EE_p2 x.1 E).ncard then
        azim 0 x.1 x.2 (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2)
      else 2 * Real.pi := by
  by_cases h : 1 < (EE_p2 x.1 E).ncard
  · simp [azimInFan_p2, h]
  · simp [azimInFan_p2, h]

/-- HOL `LOFA_IMP_NOT_INCLUDE_VEC0` (local_lemmas.hl:3769). -/
theorem LOFA_IMP_NOT_INCLUDE_VEC0 (h : localFan_p2 V E FF) : ¬((0:V3) ∈ V) := sorry

/-- HOL `AZIM_SPEC_DEGENERATE` (local_lemmas.hl:3778). -/
theorem AZIM_SPEC_DEGENERATE (v0 v1 w1 : V3) :
    azim v0 v1 w1 v0 = 0 ∧ azim v0 v1 w1 v1 = 0 := by
  have h1 : Collinear3 v0 v1 w1 ∨ Collinear3 v0 v1 v0 :=
    Or.inr (collinear3_pair_left (rfl : v0 = v0))
  have h2 : Collinear3 v0 v1 w1 ∨ Collinear3 v0 v1 v1 :=
    Or.inr (collinear3_pair_right (rfl : v1 = v1))
  exact ⟨by rw [azim, if_pos h1], by rw [azim, if_pos h2]⟩

/-- HOL `CONDS_IN_CONV2` (local_lemmas.hl:3789). -/
theorem CONDS_IN_CONV2 {v w : V3} {t2 t3 : ℝ} (ht2 : 0 ≤ t2) (ht3 : 0 ≤ t3)
    (hne : ¬(t2 = 0 ∧ t3 = 0)) :
    (t2 / (t2 + t3)) • v + (t3 / (t2 + t3)) • w ∈ convexHull ℝ ({v, w} : Set V3) := by
  have hpos : 0 < t2 + t3 := by
    by_contra hcon
    push_neg at hcon
    exact hne ⟨by linarith, by linarith⟩
  have hsum1 : t2 / (t2 + t3) + t3 / (t2 + t3) = 1 := by field_simp
  rw [convexHull_pair]
  simp only [segment, Set.mem_setOf_eq]
  have hco : 0 ≤ t2 + t3 := le_of_lt hpos
  refine ⟨t2 / (t2 + t3), t3 / (t2 + t3),
    div_nonneg ht2 hco, div_nonneg ht3 hco, by rw [hsum1], rfl⟩

/-- HOL `PGSQVBL` (local_lemmas.hl:3815). -/
theorem PGSQVBL (h : convexLocalFan_p2 V E FF) {v w : V3} (hvw : {v, w} ⊆ V)
    (hx : x ∈ FF) :
    affGe ({0} : Set V3) ({v, w} : Set V3) ⊆ wedgeInFanGe_p2 x E := sorry


/-- HOL `FST_EQ_IF_SAME_SND` (local_lemmas.hl:3939). -/
theorem FST_EQ_IF_SAME_SND (h : localFan_p2 V E FF) {w1 w2 v : V3}
    (h1 : (w1, v) ∈ FF) (h2 : (w2, v) ∈ FF) : w1 = w2 := sorry

/-- HOL `PRE_IVS_RHO_NODE1_DETE` (local_lemmas.hl:3958). -/
theorem PRE_IVS_RHO_NODE1_DETE (h : localFan_p2 V E FF) {vv v : V3}
    (hv : (vv, v) ∈ FF) : ivsRhoNode1_p2 FF v = vv := sorry

/-- HOL `IVS_RHO_NODE1_DETE` (local_lemmas.hl:3966). -/
theorem IVS_RHO_NODE1_DETE (h : localFan_p2 V E FF) {vv v : V3}
    (hv : (vv, v) ∈ FF) : ivsRhoNode1_p2 FF v = vv := sorry

/-- HOL `AZIM_EQ_0_SYM2` (local_lemmas.hl:3973). -/
theorem AZIM_EQ_0_SYM2 (v0 v1 w1 w2 : V3) :
    azim v0 v1 w1 w2 = 0 ↔ azim v0 v1 w2 w1 = 0 := by
  have key0 : ∀ (a b : V3), Collinear3 v0 v1 a ∨ Collinear3 v0 v1 b →
      azim v0 v1 a b = 0 := by
    intro a b hc
    rw [azim, if_pos hc]
  by_cases h1 : Collinear3 v0 v1 w1
  · exact ⟨fun _ => key0 w2 w1 (Or.inr h1), fun _ => key0 w1 w2 (Or.inl h1)⟩
  · by_cases h2 : Collinear3 v0 v1 w2
    · exact ⟨fun _ => key0 w2 w1 (Or.inl h2), fun _ => key0 w1 w2 (Or.inr h2)⟩
    · exact azim_eq_zero_symm h1 h2

/-- HOL `LOCAL_FAN_IN_FF_IN_ORD_PAIRS2` (local_lemmas.hl:3979). -/
theorem LOCAL_FAN_IN_FF_IN_ORD_PAIRS2 (h : localFan_p2 V E FF) {x y : V3 × V3}
    (hx : x ∈ FF) (hy : y ∈ FF) :
    ({x.1, x.2} : Set V3) ∈ E ∧ ({y.1, y.2} : Set V3) ∈ E := sorry

/-- HOL `INTERIOR_ANGLE1_POS` (local_lemmas.hl:3989). -/
theorem INTERIOR_ANGLE1_POS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    0 < interiorAngle1_p2 0 FF v := sorry

/-- HOL `FAN_IMP_NOT_IN_AFF_GE` (local_lemmas.hl:4034). -/
theorem FAN_IMP_NOT_IN_AFF_GE {x v w : V3} (hfan : FAN x V E)
    (hvw : ({v, w} : Set V3) ⊆ V) (hvw2 : v ≠ w) : ¬(v ∈ affGe ({x} : Set V3) ({w} : Set V3)) := sorry

/-- HOL `IN_AFF_LT_IMP_IN_CONV` (local_lemmas.hl:4061). -/
theorem IN_AFF_LT_IMP_IN_CONV {x a b : V3} (hdis : Disjoint ({x} : Set V3) ({b} : Set V3))
    (ha : a ∈ affLt ({x} : Set V3) ({b} : Set V3)) : x ∈ conv0_p2 ({a, b} : Set V3) := sorry

/-- HOL `FAN_SUB_NOT_EQ_COLL_IN_CONV0` (local_lemmas.hl:4090). -/
theorem FAN_SUB_NOT_EQ_COLL_IN_CONV0 {x v w : V3} (hfan : FAN x V E)
    (hvw : ({v, w} : Set V3) ⊆ V) (hvw2 : v ≠ w)
    (hcol : Collinear ℝ ({x, v, w} : Set V3)) : x ∈ conv0_p2 ({v, w} : Set V3) := sorry

/-- HOL `IN_CONV_LINE_SEPERATABLE` (local_lemmas.hl:4119). -/
theorem IN_CONV_LINE_SEPERATABLE {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    (affineSpan ℝ ({a, b} : Set V3) : Set V3) =
      affGe ({x} : Set V3) ({a} : Set V3) ∪ affGe ({x} : Set V3) ({b} : Set V3) := sorry

/-- HOL `CVLF_LF_F` (local_lemmas.hl:4210). -/
theorem CVLF_LF_F (h : convexLocalFan_p2 V E FF) : localFan_p2 V E FF ∧ FAN 0 V E := by
  obtain ⟨HS, h1, h2, h3, h4, hFAN, h6⟩ := CVX_LO_IMP_LO h
  exact ⟨⟨HS, h1, h2, h3, h4, hFAN, h6⟩, hFAN⟩

/-- HOL `EMPTY_NOT_EXISTS_IN` (local_lemmas.hl:4217). -/
theorem EMPTY_NOT_EXISTS_IN {α : Type*} (a : Set α) : a = ∅ ↔ ¬ ∃ x, x ∈ a := by
  constructor
  · intro h hex
    obtain ⟨x, hx⟩ := hex
    rw [h] at hx
    exact hx
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact h ⟨x, hx⟩

/-- HOL `LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI` (local_lemmas.hl:4222). -/
theorem LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    (0:V3) ∈ conv0_p2 ({v, w} : Set V3) ∧
      (∀ u ∈ V \ {v, w}, interiorAngle1_p2 0 FF u = Real.pi ∧
        rhoNode1_p2 FF u ∈ affineSpan ℝ ({u, v, w} : Set V3) ∧
        ivsRhoNode1_p2 FF u ∈ affineSpan ℝ ({u, v, w} : Set V3)) := sorry

/-- HOL `AFF_GE_MONO_TRANS` (local_lemmas.hl:4336). -/
theorem AFF_GE_MONO_TRANS {S X Y : Set V3} (hsub : S ⊆ X) :
    affGe (X \ S) (Y ∪ S) ⊆ affGe X Y := sorry

theorem AFF_GT_MONO_TRANS {S X Y : Set V3} (hsub : S ⊆ X) :
    affGt (X \ S) (Y ∪ S) ⊆ affGt X Y := sorry


/-- HOL `LOFA_IMP_BIJ_FF_V` (local_lemmas.hl:4412). -/
theorem LOFA_IMP_BIJ_FF_V (h : localFan_p2 V E FF) : Set.BijOn Prod.fst FF V :=
  WRGCVDR_BIJ h

/-- HOL `LOFA_IMP_CARD_FF_V_EQ` (local_lemmas.hl:4415). -/
theorem LOFA_IMP_CARD_FF_V_EQ (h : localFan_p2 V E FF) : FF.ncard = V.ncard := sorry

/-- HOL `FIRST_IN_AFF` (local_lemmas.hl:4423). -/
theorem FIRST_IN_AFF (a : V3) (S : Set V3) :
    a ∈ (affineSpan ℝ (insert a S) : Set V3) :=
  subset_affineSpan ℝ (insert a S) (Set.mem_insert a S)

/-- HOL `HALF_CIRCULAR_IN_PLANE` (local_lemmas.hl:4431). -/
theorem HALF_CIRCULAR_IN_PLANE (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E)
    (hn : n < V.ncard) (hw : w = (rhoNode1_p2 FF)^[n] v) :
    {(rhoNode1_p2 FF)^[l] v | l ≤ n} ⊆ affineSpan ℝ ({0, v, rhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `LOFA_IMP_AZIM_RHO_NODE_ST` (local_lemmas.hl:4517). -/
theorem LOFA_IMP_AZIM_RHO_NODE_ST (h : localFan_p2 V E FF) {v e : V3} (hv : v ∈ V)
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    ¬(azim 0 e v (rhoNode1_p2 FF v) = 0 ∨ azim 0 e v (rhoNode1_p2 FF v) = Real.pi) := sorry

/-- HOL `LOFA_IMP_DIS_ELMS2` (local_lemmas.hl:4546). -/
theorem LOFA_IMP_DIS_ELMS2 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∀ i l : ℕ, i < l → l < FF.ncard →
      (rhoNode1_p2 FF)^[l] v ≠ (rhoNode1_p2 FF)^[i] v :=
  fun i l hi hl => LOFA_IMP_DIS_ELMS h hv hl i hi

/-- HOL `RHO_NODE1_MONO_WITH_AZIM` (local_lemmas.hl:4557). -/
theorem RHO_NODE1_MONO_WITH_AZIM (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} {U : Set V3} (hU : {(rhoNode1_p2 FF)^[n] v | n ≤ l} = U)
    {P : Set V3} (hP : plane_p2 P) (h0 : (0:V3) ∈ P) (hsub : U ⊆ P) {e : V3}
    (he : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((rhoNode1_p2 FF v : V3) : Fin 3 → ℝ)) : V3) = e) :
    ∀ n m : ℕ, n < m → m < V.ncard → m ≤ l →
      azim 0 e v ((rhoNode1_p2 FF)^[n] v) < azim 0 e v ((rhoNode1_p2 FF)^[m] v) := sorry

/-- HOL `DISJOINT_IMP_Z_IN_AFF_GT` (local_lemmas.hl:4682). -/
theorem DISJOINT_IMP_Z_IN_AFF_GT {x y z : V3}
    (h : Disjoint ({x, y} : Set V3) ({z} : Set V3)) :
    z ∈ affGt ({x, y} : Set V3) ({z} : Set V3) := by
  have hfin : ((({x, y} ∪ {z}) : Set V3) : Set V3).Finite := by simp
  have hEq : hfin.toFinset = ({x, y, z} : Finset V3) := by
    ext w
    simp [Set.Finite.mem_toFinset, Set.disjoint_left.mp h]
    tauto
  unfold affGt
  refine ⟨fun w => if w = z then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [hEq, Finset.sum_eq_single_of_mem z (by simp)]
    · simp
    · intro w _ hwz
      simp [hwz]
  · intro w hw
    simp only [Set.mem_singleton_iff] at hw
    rw [hw]
    simp
  · rw [hEq, Finset.sum_eq_single_of_mem z (by simp)]
    · simp
    · intro w _ hwz
      simp [hwz]

/-- HOL `LOFA_IMP_DIS_ELMS23` (local_lemmas.hl:4691). -/
theorem LOFA_IMP_DIS_ELMS23 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∀ i l : ℕ, i < l → l < V.ncard →
      (rhoNode1_p2 FF)^[l] v ≠ (rhoNode1_p2 FF)^[i] v := by
  intro i l hi hl
  exact LOFA_IMP_DIS_ELMS2 h hv i l hi ((LOFA_IMP_CARD_FF_V_EQ h) ▸ hl)

/-- HOL `NOT_COLL_IMP_COPL` (local_lemmas.hl:4701). -/
theorem NOT_COLL_IMP_COPL {v w : V3} (h : ¬ Collinear ℝ ({0, v, w} : Set V3)) :
    ¬ Coplanar ({0, v, w, (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((w : V3) : Fin 3 → ℝ)) : V3)} : Set V3) := sorry

/-- HOL `COLL_IFF_COLL_CROSS` (local_lemmas.hl:4707). -/
theorem COLL_IFF_COLL_CROSS {v w : V3} :
    Collinear ℝ ({0, v, w} : Set V3) ↔
      Collinear ℝ ({0, v, (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) : V3)} : Set V3) := sorry

/-- HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` (local_lemmas.hl:4719). -/
theorem LOCAL_FAN_CHARACTER_OF_RHO_NODE2 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ¬ Collinear ℝ ({0, v, rhoNode1_p2 FF v} : Set V3) :=
  (LOCAL_FAN_CHARACTER_OF_RHO_NODE h hv).2.2

/-- HOL `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` (local_lemmas.hl:4726). -/
theorem LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, i < V.ncard ∧ w = (rhoNode1_p2 FF)^[i] v ∧
      ((fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i}) ⊆
        affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `LOOP_SET_ITER_CARD_ID` (local_lemmas.hl:4930). -/
theorem LOOP_SET_ITER_CARD_ID {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V) : f^[V.ncard] v = v := sorry

/-- HOL `LOFA_IMP_ITER_RHO_NODE_ID` (local_lemmas.hl:4991). -/
theorem LOFA_IMP_ITER_RHO_NODE_ID (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard] v = v := sorry


/-- HOL `CONV_SUBSET_AFF_GE` (local_lemmas.hl:4999). Deviation note: the
Lean `Affsign` encoding needs a finite support-set, hence `hS`. -/
theorem CONV_SUBSET_AFF_GE {S SS : Set V3} (hS : S.Finite) (hSS : SS.Finite) :
    convexHull ℝ SS ⊆ (affGe S SS : Set V3) := by
  refine convexHull_min ?_ Affsign_convex
  intro w hw
  have hfin : (((S ∪ SS) : Set V3) : Set V3).Finite := by simp [hS, hSS]
  have hmem : w ∈ hfin.toFinset := by simp [Set.Finite.mem_toFinset, hw]
  refine ⟨fun z => if z = w then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single_of_mem w hmem (fun u _ hu => by simp [hu])]
    simp
  · intro z hz
    by_cases hz2 : z = w <;> simp [hz2]
  · rw [Finset.sum_eq_single_of_mem w hmem (fun u _ hu => by simp [hu])]
    simp

/-- HOL `CONV0_SUBSET_AFF_GT` (local_lemmas.hl:5003). Deviation note: `hS`
(finite support-set) is required by the Lean `Affsign` encoding. -/
theorem CONV0_SUBSET_AFF_GT {S SS : Set V3} (hS : S.Finite) :
    conv0_p2 SS ⊆ (affGt S SS : Set V3) := sorry

/-- HOL `collinear_fan22` (local_lemmas.hl:5011). -/
theorem collinear_fan22 (x v u : V3) :
    Collinear ℝ ({x, v, u} : Set V3) ↔
      u ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∨ x = v :=
  collinear_triple_iff

/-- HOL `IN_CONV0_IMP_COLL_IFF` (local_lemmas.hl:5014). -/
theorem IN_CONV0_IMP_COLL_IFF {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    Collinear ℝ ({a, x, v} : Set V3) ↔ Collinear ℝ ({a, b, v} : Set V3) := sorry

/-- HOL `IN_CONV0_IMP_COLL_ENDS_AFF` (local_lemmas.hl:5019). -/
theorem IN_CONV0_IMP_COLL_ENDS_AFF {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    Collinear ℝ ({a, x, v} : Set V3) ↔ Collinear ℝ ({b, x, v} : Set V3) := sorry

/-- HOL `IN_CONV0_IMP_AZIM_PI` (local_lemmas.hl:5031). -/
theorem IN_CONV0_IMP_AZIM_PI {x a b e : V3} (hcol : ¬ Collinear ℝ ({x, a, e} : Set V3))
    (hx : x ∈ conv0_p2 ({a, b} : Set V3)) : azim x e a b = Real.pi := sorry

/-- HOL `AFF_GT_MONO` (local_lemmas.hl:5064). -/
theorem AFF_GT_MONO {X Y S : Set V3} (hS : S ⊆ Y) :
    affGt X Y ⊆ affGt (X ∪ S) (Y \ S) := sorry

/-- HOL `AFF_GT_SUB_AFF_UNION` (local_lemmas.hl:5076). -/
theorem AFF_GT_SUB_AFF_UNION (X Y : Set V3) :
    affGt X Y ⊆ (affineSpan ℝ (X ∪ Y) : Set V3) := sorry

/-- HOL `SIN_AZIM_NEG_PI_LT` (local_lemmas.hl:5085). -/
theorem SIN_AZIM_NEG_PI_LT (x y u v : V3) :
    Real.sin (azim x y u v) < 0 ↔ Real.pi < azim x y u v := sorry

/-- HOL `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT` (local_lemmas.hl:5105). -/
theorem NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, w = (rhoNode1_p2 FF)^[i] v ∧ i + 1 < V.ncard ∧
      ¬((rhoNode1_p2 FF)^[i + 1] v ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3)) := sorry

/-- HOL `FOR_AFF_GT_NOT_INTERSECTION` (local_lemmas.hl:5226). -/
theorem FOR_AFF_GT_NOT_INTERSECTION {x y u v : V3} {a1 b1 a2 b2 t tt : ℝ}
    (h : a1 • x + b1 • y + t • u = a2 • x + b2 • y + tt • v)
    (ht : 0 < t) (htt : 0 < tt)
    (hs1 : a1 + b1 + t = 1) (hs2 : a2 + b2 + tt = 1) :
    u = ((a2 - a1) / t) • x + ((b2 - b1) / t) • y + (tt / t) • v ∧
      (a2 - a1) / t + (b2 - b1) / t + tt / t = 1 ∧ 0 < tt / t := by
  have h2 : t • u = (a2 - a1) • x + (b2 - b1) • y + tt • v := by
    linear_combination (norm := module) h
  refine ⟨?_, ?_, div_pos htt ht⟩
  · rw [← inv_smul_smul₀ ht.ne' u, h2, smul_add, smul_add, smul_smul, smul_smul,
      smul_smul, div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul]
  · field_simp
    linarith

/-- HOL `NOT_COLL_RHONODE_SND_POINT` (local_lemmas.hl:5265). -/
theorem NOT_COLL_RHONODE_SND_POINT (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) : ¬ Collinear ℝ ({0, v, rhoNode1_p2 FF w} : Set V3) := sorry

/-- HOL `NOT_INTERSECTION_BWT_AFF_GTS` (local_lemmas.hl:5295). -/
theorem NOT_INTERSECTION_BWT_AFF_GTS (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    affGt ({0, v} : Set V3) ({rhoNode1_p2 FF w} : Set V3) ∩
      affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) = ∅ := sorry

/-- HOL `LUNAR_COMM` (local_lemmas.hl:5322). -/
theorem LUNAR_COMM (v w : V3) (V : Set V3) (E : Set (Set V3)) :
    lunar_p2 v w V E ↔ lunar_p2 w v V E := by
  unfold lunar_p2
  constructor <;> intro h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have hset : ({w, v} : Set V3) = {v, w} := by ext z; simp; tauto
    have hc : ({0, w, v} : Set V3) = {0, v, w} := by ext z; simp; tauto
    exact ⟨h1, by rw [hset]; exact h2, h3.symm, by rw [hc]; exact h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have hset : ({v, w} : Set V3) = {w, v} := by ext z; simp; tauto
    have hc : ({0, v, w} : Set V3) = {0, w, v} := by ext z; simp; tauto
    exact ⟨h1, by rw [hset]; exact h2, h3.symm, by rw [hc]; exact h4⟩

/-- HOL `CONV0_AFF_GT_EQ` (local_lemmas.hl:5328). -/
theorem CONV0_AFF_GT_EQ {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3))
    (hcol : ¬ Collinear ℝ ({a, x, v} : Set V3)) :
    affGt ({x, a} : Set V3) ({v} : Set V3) =
      affGt ({x, a, b} : Set V3) ({v} : Set V3) := sorry


/-- HOL `AFF_GT_SAME_WITH_ENDS` (local_lemmas.hl:5375). -/
theorem AFF_GT_SAME_WITH_ENDS (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E) :
    affGt ({0, v} : Set V3) ({rhoNode1_p2 FF w} : Set V3) =
      affGt ({0, w} : Set V3) ({rhoNode1_p2 FF w} : Set V3) := sorry

/-- HOL `USEFULL_THHM` (local_lemmas.hl:5402). -/
theorem USEFULL_THHM {b c z w : V3} (h1 : z ∈ affineSpan ℝ ({b, c} : Set V3))
    (h2 : z ∈ affGt ({b, c} : Set V3) ({w} : Set V3)) :
    w ∈ affineSpan ℝ ({b, c} : Set V3) := sorry

/-- HOL `COLL_IN_AFF_GT_TOO` (local_lemmas.hl:5427). -/
theorem COLL_IN_AFF_GT_TOO {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    ¬ Collinear ℝ ({x, y, a} : Set V3) := sorry

/-- HOL `AFF_GT_IN_IMP_SUBSET` (local_lemmas.hl:5435). -/
theorem AFF_GT_IN_IMP_SUBSET {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    affGt ({x, y} : Set V3) ({a} : Set V3) ⊆ affGt ({x, y} : Set V3) ({z} : Set V3) := sorry

/-- HOL `FOR_AFF_GT_NOT_INTERSECTION2` (local_lemmas.hl:5459): the Specl
0/0/1 instance of `FOR_AFF_GT_NOT_INTERSECTION`. -/
theorem FOR_AFF_GT_NOT_INTERSECTION2 {x y u v : V3} {a1 b1 t : ℝ}
    (h : a1 • x + b1 • y + t • u = v) (ht : 0 < t) (hs : a1 + b1 + t = 1) :
    u = ((0 - a1) / t) • x + ((0 - b1) / t) • y + (1 / t) • v ∧
      (0 - a1) / t + (0 - b1) / t + 1 / t = 1 ∧ 0 < 1 / t := by
  exact FOR_AFF_GT_NOT_INTERSECTION (x := x) (y := y) (u := u)
    (a1 := a1) (b1 := b1) (a2 := 0) (b2 := 0) (t := t) (tt := 1)
    (by simpa [mul_zero, zero_add] using h) ht (by norm_num) hs (by norm_num)

/-- HOL `INVS_IN_AFF_GT` (local_lemmas.hl:5467). -/
theorem INVS_IN_AFF_GT {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    z ∈ affGt ({x, y} : Set V3) ({a} : Set V3) := sorry

/-- HOL `COLL_IN_AFF_GT_AFF_GT_EQ` (local_lemmas.hl:5488). -/
theorem COLL_IN_AFF_GT_AFF_GT_EQ {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    affGt ({x, y} : Set V3) ({z} : Set V3) = affGt ({x, y} : Set V3) ({a} : Set V3) := sorry

/-- HOL `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2` (local_lemmas.hl:5502). -/
theorem NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2 (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, w = (rhoNode1_p2 FF)^[i] v ∧ i + 1 < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧
      ¬((rhoNode1_p2 FF)^[i + 1] v ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3)) := sorry

/-- HOL `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT100` (local_lemmas.hl:5534). -/
theorem LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT100 (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, i < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧ w = (rhoNode1_p2 FF)^[i] v ∧
      ((fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i}) ⊆
        affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `IVS_RHO_IDD` (local_lemmas.hl:5568). -/
theorem IVS_RHO_IDD (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ivsRhoNode1_p2 FF (rhoNode1_p2 FF v) = v := sorry

/-- HOL `AFF_IVS_RHO_NODE_EQQ` (local_lemmas.hl:5578). -/
theorem AFF_IVS_RHO_NODE_EQQ (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E) :
    affGt ({0, w} : Set V3) ({rhoNode1_p2 FF w} : Set V3) =
      affGt ({0, v} : Set V3) ({ivsRhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `LOFA_IMP_LT_CARD_SET_V` (local_lemmas.hl:5627; cf. the
`LOFA_IMP_LT_CARD_SET_V_ALT` re-render in LocalAuto2). -/
theorem LOFA_IMP_LT_CARD_SET_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    {(rhoNode1_p2 FF)^[n] v | n < V.ncard} = V := sorry

/-- HOL `NOT_COLL_IMP_NOT_AFF_SUB` (local_lemmas.hl:5640). -/
theorem NOT_COLL_IMP_NOT_AFF_SUB {x y z v : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (hv : v ∈ affineSpan ℝ ({x, y} : Set V3)) :
    ¬(v ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) := sorry

/-- HOL `HALP_CIRCLE_IS_INTERSECTION` (local_lemmas.hl:5653). -/
theorem HALP_CIRCLE_IS_INTERSECTION (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, i < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧ w = (rhoNode1_p2 FF)^[i] v ∧
      ((fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i}) =
        affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) ∩ V := sorry

/-- HOL `CONVEX_LOFA_IMP_INANGLE_LE_PI` (local_lemmas.hl:5818). -/
theorem CONVEX_LOFA_IMP_INANGLE_LE_PI (h : convexLocalFan_p2 V E FF) {v : V3}
    (hv : v ∈ V) : interiorAngle1_p2 0 FF v ≤ Real.pi := sorry

/-- HOL `X_IN_AFF_GT_X` (local_lemmas.hl:5860). Deviation note: `hS` is
required by the Lean `Affsign` encoding. -/
theorem X_IN_AFF_GT_X {S : Set V3} (hS : S.Finite) (x : V3) :
    x ∈ affGt S ({x} : Set V3) := by
  have hfin : (((S ∪ {x}) : Set V3) : Set V3).Finite := by simp [hS]
  have hmem : x ∈ hfin.toFinset := by simp [Set.Finite.mem_toFinset]
  unfold affGt
  refine ⟨fun w => if w = x then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single_of_mem x hmem (fun u _ hu => by simp [hu])]
    simp
  · intro w hw
    have hw2 : w = x := by simpa using hw
    rw [hw2]
    simp
  · rw [Finset.sum_eq_single_of_mem x hmem (fun u _ hu => by simp [hu])]
    simp

/-- HOL `IVS_RNODE_IN_AFF_V` (local_lemmas.hl:5868). -/
theorem IVS_RNODE_IN_AFF_V (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E) :
    ivsRhoNode1_p2 FF w ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `AZIM_LE_PI_EQ_DIHV` (local_lemmas.hl:5880). -/
theorem AZIM_LE_PI_EQ_DIHV {a b x y : V3} (h1 : ¬ Collinear ℝ ({a, b, x} : Set V3))
    (h2 : ¬ Collinear ℝ ({a, b, y} : Set V3)) (h : azim a b x y ≤ Real.pi) :
    azim a b x y = dihV a b x y := sorry

/-- HOL `LOFA_IMP_NOT_COLL_IVS` (local_lemmas.hl:5890). -/
theorem LOFA_IMP_NOT_COLL_IVS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ¬ Collinear ℝ ({0, v, ivsRhoNode1_p2 FF v} : Set V3) := sorry

/-- HOL `DIHV_NOT_CHANGE` (local_lemmas.hl:5903). -/
theorem DIHV_NOT_CHANGE {x y v w : V3} {a b c : ℝ} (hc : 0 < c) (hsum : a + b + c = 1) :
    dihV x y (a • x + b • y + c • v) w = dihV x y v w := sorry

/-- HOL `LUNAR_IMP_INTERIOR_ANGLE_EQQ` (local_lemmas.hl:5915). -/
theorem LUNAR_IMP_INTERIOR_ANGLE_EQQ (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) : interiorAngle1_p2 0 FF v = interiorAngle1_p2 0 FF w := sorry

/-- HOL `HKIRPEP` (local_lemmas.hl:6027): the master lunar-fan inventory. -/
theorem HKIRPEP (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E) :
    (∀ u ∈ V \ {v, w}, interiorAngle1_p2 0 FF u = Real.pi) ∧
      0 < interiorAngle1_p2 0 FF v ∧
      interiorAngle1_p2 0 FF v ≤ Real.pi ∧
      interiorAngle1_p2 0 FF v = interiorAngle1_p2 0 FF w ∧
      (∃ i : ℕ, i < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧ w = (rhoNode1_p2 FF)^[i] v ∧
        ((fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i}) =
          affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) ∩ V) ∧
      (∃ j : ℕ, j < V.ncard ∧ ¬(j = 0) ∧ ¬(j = 1) ∧ v = (rhoNode1_p2 FF)^[j] w ∧
        ((fun l => (rhoNode1_p2 FF)^[l] w) '' {l : ℕ | 0 < l ∧ l < j}) =
          affGt ({0, v} : Set V3) ({ivsRhoNode1_p2 FF v} : Set V3) ∩ V) := sorry

/-- HOL `FINITE_CARD1_IMP_SINGLETON` (local_lemmas.hl:6072). -/
theorem FINITE_CARD1_IMP_SINGLETON {α : Type*} {S : Set α} (hS : S.Finite)
    (h1 : S.ncard = 1) : ∃ x, S = {x} := by
  rw [← Set.encard_eq_one]
  rw [Set.ncard_eq_toFinset_card S hS] at h1
  rw [hS.encard_eq_coe_toFinset_card]
  exact_mod_cast h1

/-- HOL `SURJ_IMP_FINITE` (local_lemmas.hl:6080). -/
theorem SURJ_IMP_FINITE {α β : Type*} (f : α → β) {A : Set α} {B : Set β}
    (hsurj : ∀ b ∈ B, ∃ a ∈ A, f a = b) (hA : A.Finite) : B.Finite := by
  refine Set.Finite.subset (hA.image f) ?_
  intro b hb
  obtain ⟨a, ha, hab⟩ := hsurj b hb
  exact ⟨a, ha, hab⟩

/-- HOL `LOFA_V_NOT_EMP` (local_lemmas.hl:6090). -/
theorem LOFA_V_NOT_EMP (h : localFan_p2 V E FF) : V ≠ ∅ := sorry

/-- HOL `LOCAL_FAN_FINITE_V` (local_lemmas.hl:6096). -/
theorem LOCAL_FAN_FINITE_V (h : localFan_p2 V E FF) : V.Finite := sorry

/-- HOL `ITER_CARD_MINUS1_EQ_IVS_RN1` (local_lemmas.hl:6106). -/
theorem ITER_CARD_MINUS1_EQ_IVS_RN1 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard - 1] v = ivsRhoNode1_p2 FF v := sorry

/-- HOL `FIRST_EQ0_LAST_LT_PI` (local_lemmas.hl:6145). -/
theorem FIRST_EQ0_LAST_LT_PI (h : convexLocalFan_p2 V E FF) {v0 : V3} (hv0 : v0 ∈ V)
    {k : ℕ} (hk : V.ncard = k) {vv : ℕ → V3} (hvv : ∀ i : ℕ, (rhoNode1_p2 FF)^[i] v0 = vv i)
    {bta : ℕ → ℝ} (hbta : ∀ i : ℕ, azim 0 v0 (vv 1) (vv i) = bta i) :
    bta 1 = 0 ∧ bta (k - 1) ≤ Real.pi := sorry

/-- HOL `DETERMINE_WEDGE_IN_FAN` (local_lemmas.hl:6173). -/
theorem DETERMINE_WEDGE_IN_FAN (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    wedgeInFanGe_p2 x E = wedgeGe_p2 0 x.1 x.2
      (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2) := sorry

/-- HOL `LOCAL_FAN_IMP_IN_V2` (local_lemmas.hl:6186). -/
theorem LOCAL_FAN_IMP_IN_V2 (h : localFan_p2 V E FF) {d : V3 × V3} (hd : d ∈ FF) :
    d.1 ∈ V ∧ d.2 ∈ V := sorry

/-- HOL `LOFA_DETERMINE_AZIM_IN_FA` (local_lemmas.hl:6199). -/
theorem LOFA_DETERMINE_AZIM_IN_FA (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    azimInFan_p2 x E = azim 0 x.1 x.2 (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2) := sorry

end Kepler.Text

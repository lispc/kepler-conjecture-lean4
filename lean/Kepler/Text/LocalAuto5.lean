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
import Kepler.Text.TopologyFan
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
    d1.1 ∈ V ∧ d1.2 ∈ V ∧ d2.1 ∈ V ∧ d2.2 ∈ V := by
  obtain ⟨HS, hd, -, -, -, hfan, ⟨x, hx, hFx⟩, -⟩ := h
  have hfaceSub := HS.face_subset_darts hx
  have hmem : ∀ z : V3 × V3, z ∈ FF → z ∈ dartsOfHyp_p2 E V := by
    intro z hz
    rw [hFx] at hz
    rw [← hd]
    exact hfaceSub hz
  have hV : ∀ z : V3 × V3, z ∈ dartsOfHyp_p2 E V → z.1 ∈ V ∧ z.2 ∈ V := by
    intro z hz
    have hEsub : (⋃₀ E) ⊆ V := hfan.1
    rcases Set.mem_or_mem_of_mem_union (show z ∈ (ordPairs_p2 E ∪ selfPairs_p2 E V) from hz) with
      ho | hs
    · exact ⟨(Set.subset_sUnion_of_mem ho).trans hEsub (Set.mem_insert z.1 ({z.2} : Set V3)),
        (Set.subset_sUnion_of_mem ho).trans hEsub (Set.mem_insert_of_mem z.1 rfl)⟩
    · exact ⟨hs.2.1, by rw [← hs.1]; exact hs.2.1⟩
  have e1 := hV d1 (hmem d1 hd1)
  have e2 := hV d2 (hmem d2 hd2)
  exact ⟨e1.1, e1.2, e2.1, e2.2⟩

/-- HOL `LOCAL_FAN_RHO_NODE_PROS` (local_lemmas.hl:69): the rho-node maps
`V` onto successor darts, and every dart is `(FST x, rho_node1 FF (FST x))`. -/
theorem LOCAL_FAN_RHO_NODE_PROS (h : localFan_p2 V E FF) :
    (∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF) ∧
      ∀ x ∈ FF, x = (x.1, rhoNode1_p2 FF x.1) := by
  -- B5 free-cascade wave (2026-10-10): WRGCVDR_BIJ (LocalAuto2) went real in
  -- the LA2 p2-mirror wave (`454b9479`); this 15-line derivation was queued in
  -- docs/la3-wrgcvdr-handoff.md ("LOCAL_FAN_RHO_NODE_PROS 仅 15 行可导").
  obtain ⟨hmap, hinj, hsurj⟩ := WRGCVDR_BIJ h
  have hleft : ∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF := by
    intro x hx
    obtain ⟨d, hd, hfd⟩ := hsurj hx
    have hdeq : (x, d.2) = d := Prod.ext hfd.symm rfl
    have hmemFF : (x, d.2) ∈ FF := by
      rw [hdeq]
      exact hd
    exact Classical.epsilon_spec (p := fun w => (x, w) ∈ FF) ⟨d.2, hmemFF⟩
  refine ⟨hleft, ?_⟩
  intro d hd
  have hsucc : (d.1, rhoNode1_p2 FF d.1) ∈ FF := hleft d.1 (hmap hd)
  exact (hinj hsucc hd rfl).symm

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

/-- Lane support (LA5): the `FAN 0 V E` component of a local fan. -/
private theorem la5_FAN_of_localFan (h : localFan_p2 V E FF) : FAN 0 V E := by
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := h
  exact hfan

/-- Lane support (LA5): a local-fan face is contained in the dart set. -/
private theorem la5_FF_subset_darts (h : localFan_p2 V E FF) :
    FF ⊆ dartsOfHyp_p2 E V := by
  obtain ⟨HS, hd, -, -, -, -, ⟨x, hx, hFx⟩, -⟩ := h
  have hsub := HS.face_subset_darts hx
  intro d hdF
  rw [hFx] at hdF
  rw [← hd]
  exact hsub hdF

/-- Lane support (LA5): both endpoints of a dart lie in `V`. -/
private theorem la5_dart_mem_V (hfan : FAN 0 V E) {d : V3 × V3}
    (hd : d ∈ dartsOfHyp_p2 E V) : d.1 ∈ V ∧ d.2 ∈ V := by
  have hEsub : (⋃₀ E) ⊆ V := hfan.1
  rcases Set.mem_or_mem_of_mem_union (show d ∈ (ordPairs_p2 E ∪ selfPairs_p2 E V) from hd) with
    ho | hs
  · exact ⟨(Set.subset_sUnion_of_mem ho).trans hEsub (Set.mem_insert d.1 ({d.2} : Set V3)),
      (Set.subset_sUnion_of_mem ho).trans hEsub (Set.mem_insert_of_mem d.1 rfl)⟩
  · exact ⟨hs.2.1, by rw [← hs.1]; exact hs.2.1⟩

/-- Lane support (LA5): a local-fan face is never a singleton (cardinality
engine: `dih2k` forces `CARD dart = 2 * CARD FF`). -/
private theorem la5_not_face_card_one (h : localFan_p2 V E FF) (h1 : FF.ncard = 1) :
    False := by
  have hsub0 := la5_FF_subset_darts h
  obtain ⟨HS, hd, h2, h3, h4, hfan, ⟨x, hx, hFx⟩, hdih⟩ := h
  have hsub : FF ⊆ (↑HS.darts : Set (V3 × V3)) := by
    intro z hz
    rw [hd]
    exact hsub0 hz
  have hfin : FF.Finite := (HS.darts.finite_toSet).subset hsub
  have hne0 : ∃ e, e ∈ FF := by
    by_contra h0
    push_neg at h0
    rw [Set.eq_empty_iff_forall_notMem.mpr h0, Set.ncard_empty] at h1
    norm_num at h1
  obtain ⟨e, heF⟩ := hne0
  have he : FF = {e} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨heF, ?_⟩
    intro z hz
    by_contra hne
    have hsub2 : ({e, z} : Set (V3 × V3)) ⊆ FF := by
      intro w hw
      rcases Set.mem_insert_iff.mp hw with h | h
      · exact h ▸ heF
      · exact h ▸ hz
    have h2c : ({e, z} : Set (V3 × V3)).ncard = 2 := Set.ncard_pair (fun h => hne h.symm)
    have hle := Set.ncard_le_ncard hsub2 hfin
    rw [h2c] at hle
    omega
  have hcard2 : HS.darts.card = 2 := by rw [hdih.1, h1]
  have heD : e ∈ (↑HS.darts : Set (V3 × V3)) := hsub (by rw [he]; simp)
  have hmem : e ∈ dartsOfHyp_p2 E V := by rw [← hd]; exact heD
  have hfx : e ∈ HS.face x := by rw [← hFx, he]; simp
  obtain ⟨m, hm⟩ := hfx
  rcases eq_or_ne e.1 e.2 with hself | hne2
  · have hfixF : (HS.faceMap : V3 × V3 → V3 × V3) e = e := by
      rw [h4]; exact (FAN_FST_EQ_SND_SUPPER_EQ hfan hself).2.2
    have hfixN : (HS.nodeMap : V3 × V3 → V3 × V3) e = e := by
      rw [h3]; exact (FAN_FST_EQ_SND_SUPPER_EQ hfan hself).2.1
    have hfaceE1 : HS.face e = {e} := orbitMap_eq_singleton hfixF
    have hunion := hdih.2.1 e heD
    rw [hfaceE1, Set.image_singleton, hfixN, Set.union_self] at hunion
    rw [← Set.ncard_coe_finset, hunion] at hcard2
    simp at hcard2
  · have hfe : (ffOfHyp_p2 0 V E e).1 = e.2 := by
      simp only [ffOfHyp_p2, if_pos hmem]
    have hfaceE : (HS.faceMap : V3 × V3 → V3 × V3) e ∈ HS.face x := by
      refine ⟨m + 1, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hm]
    rw [← hFx, he] at hfaceE
    have hfixed : (HS.faceMap : V3 × V3 → V3 × V3) e = e := by
      simpa using hfaceE
    rw [h4] at hfixed
    refine hne2 ?_
    have hff := congrArg Prod.fst hfixed
    rw [hfe] at hff
    exact hff.symm

/-- Lane support (LA5): a self-pair dart inside the face collapses the face
to a singleton. -/
private theorem la5_face_singleton_of_mem_self {d : V3 × V3} (h : localFan_p2 V E FF)
    (hdF : d ∈ FF) (hself : d.1 = d.2) : FF = {d} := by
  obtain ⟨HS, hd, -, -, h4, hfan, ⟨x, hx, hFx⟩, -⟩ := h
  have hsub := HS.face_subset_darts hx
  have hdD : d ∈ (↑HS.darts : Set (V3 × V3)) := by
    rw [hFx] at hdF
    exact hsub hdF
  have hmem : d ∈ dartsOfHyp_p2 E V := by rw [← hd]; exact hdD
  have hfixD : (HS.faceMap : V3 × V3 → V3 × V3) d = d := by
    rw [h4]; exact (FAN_FST_EQ_SND_SUPPER_EQ hfan hself).2.2
  have hpow : ∀ n : ℕ, ((HS.faceMap : Equiv.Perm (V3 × V3)) ^ n) d = d := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Equiv.Perm.mul_apply, hfixD, ih]
  obtain ⟨m, hm⟩ := by rw [hFx] at hdF; exact hdF
  have hxd : x = d := Equiv.injective (HS.faceMap ^ m) (hm.trans (hpow m).symm)
  rw [hFx, hxd]
  show orbitMap (HS.faceMap : Equiv.Perm (V3 × V3)) d = ({d} : Set (V3 × V3))
  exact orbitMap_eq_singleton hfixD

/-- Lane support (LA5): transport of vanishing through the `V3` /
`Fin 3 → ℝ` type synonym. -/
private theorem la5_toLp_eq_zero {f : Fin 3 → ℝ} : (WithLp.toLp 2 f : V3) = 0 ↔ f = 0 := by
  constructor
  · intro h
    simpa [WithLp.ofLp_toLp, WithLp.ofLp_zero] using
      congrArg (fun w : V3 => (w : Fin 3 → ℝ)) h
  · intro h
    subst h
    rfl

/-- Lane support (LA5): scalar multiplication transports through the type
synonym. -/
private theorem la5_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • ((a : V3) : Fin 3 → ℝ) := rfl

/-- Lane support (LA5): `Set.range ![p, q, r]` is the three-point set. -/
private theorem la5_range3 {p q r : V3} :
    (Set.range ![p, q, r] : Set V3) = ({p, q, r} : Set V3) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hw
    rcases Set.mem_insert_iff.mp hw with rfl | h
    · exact ⟨0, rfl⟩
    rcases Set.mem_insert_iff.mp h with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- HOL `COLLINEAR_CROSS_0` (local_lemmas.hl:190). Cross rendered via
`crossProduct` and the `WithLp.toLp` idiom. -/
theorem COLLINEAR_CROSS_0 {x y z : V3} :
    Collinear ℝ ({x, y, z} : Set V3) ↔
      (WithLp.toLp 2 (crossProduct ((y - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) : V3) = 0 := by
  constructor
  · intro hcol
    rcases collinear_triple_iff.mp hcol with hmem | hxy
    · obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
      have hz : (z - x : V3) = t • ((y - x : V3)) := by
        rw [← ht]
        simp [AffineMap.lineMap_apply]
      have hz' : ((z - x : V3) : Fin 3 → ℝ) = t • ((y - x : V3) : Fin 3 → ℝ) :=
        congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hz
      rw [hz', map_smul, cross_self, smul_zero]
      exact la5_toLp_eq_zero.mpr rfl
    · rw [hxy]
      simp
  · intro h0
    have h0' : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) = 0 := la5_toLp_eq_zero.mp h0
    rcases eq_or_ne x y with hxy | hxy
    · exact collinear_triple_iff.mpr (Or.inr hxy)
    · refine collinear_triple_iff.mpr (Or.inl ?_)
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      have hvy : ((y - x : V3) : Fin 3 → ℝ) ≠ 0 := by
        intro h
        rw [WithLp.ofLp_eq_zero] at h
        exact hxy (sub_eq_zero.mp h).symm
      have hnc : ¬((crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ≠ 0) := fun hne => hne h0'
      have hLI : ¬ LinearIndependent ℝ ![((y - x : V3) : Fin 3 → ℝ),
          ((z - x : V3) : Fin 3 → ℝ)] :=
        crossProduct_ne_zero_iff_linearIndependent.not.mp hnc
      have hdep : ∃ a : ℝ, ((z - x : V3) : Fin 3 → ℝ) = a • ((y - x : V3) : Fin 3 → ℝ) := by
        by_contra hdep
        push Not at hdep
        exact hLI ((LinearIndependent.pair_iff' hvy).mpr fun a hne => hdep a hne.symm)
      obtain ⟨a, ha⟩ := hdep
      have hz2 : (z : V3) - x = a • ((y : V3) - x) :=
        WithLp.ofLp_injective 2 (ha.trans (la5_coe_smul a ((y : V3) - x)).symm)
      refine ⟨a, ?_⟩
      have hz3 : (z : V3) = x + ((z : V3) - x) := by
        abel
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      rw [hz3, hz2]
      module

/-- HOL `DET_CROSS` (local_lemmas.hl:198). -/
theorem DET_CROSS (x y z : V3) :
    Matrix.det (Matrix.of fun i j => (![x, y, z] : Fin 3 → V3) i j) =
      (crossProduct ((x : V3) : Fin 3 → ℝ) ((y : V3) : Fin 3 → ℝ))
        ⬝ᵥ ((z : V3) : Fin 3 → ℝ) := by
  rw [dotProduct_comm, triple_product_permutation (z : Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (y : Fin 3 → ℝ)]
  exact (triple_product_eq_det (x : Fin 3 → ℝ) (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)).symm

/-- Lane support (LA5): evaluation of the three-element vector at the
indices 0, 1, 2 (rfl-transports for `simp only`). -/
private theorem la5_cons_val_zero' {α : Type*} (u v w : α) :
    (![u, v, w] : Fin 3 → α) 0 = u := rfl

private theorem la5_cons_val_one' {α : Type*} (u v w : α) :
    (![u, v, w] : Fin 3 → α) 1 = v := rfl

private theorem la5_cons_val_two {α : Type*} (u v w : α) :
    (![u, v, w] : Fin 3 → α) 2 = w := rfl

/-- Lane support (LA5): three linearly independent vectors span (in any
3-dimensional real module). -/
private theorem la5_span3 {M : Type*} [AddCommGroup M] [Module ℝ M]
    (h3 : Fintype.card (Fin 3) = Module.finrank ℝ M) {p q n u : M}
    (hLI : LinearIndependent ℝ ![p, q, n]) :
    ∃ a1 a2 a3 : ℝ, u = a1 • p + a2 • q + a3 • n := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ M := h3
  let b := basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hcoe : ⇑b = ![p, q, n] := coe_basisOfLinearIndependentOfCardEqFinrank _ hcard
  have hsum0 := b.sum_repr u
  rw [hcoe] at hsum0
  simp [Fin.sum_univ_three] at hsum0
  refine ⟨b.repr u 0, b.repr u 1, b.repr u 2, hsum0.symm⟩

/-- Lane support (LA5): non-collinearity of `{x, y, z}` gives linear
independence of the two difference vectors (Pi level). -/
private theorem la5_notcollinear_li {x y z : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3)) :
    LinearIndependent ℝ ![((y - x : V3) : Fin 3 → ℝ), ((z - x : V3) : Fin 3 → ℝ)] := by
  have hne : ¬((crossProduct ((y - x : V3) : Fin 3 → ℝ)
      ((z - x : V3) : Fin 3 → ℝ)) = 0) := fun h =>
    hcol ((COLLINEAR_CROSS_0 (x := x) (y := y) (z := z)).mpr
      (la5_toLp_eq_zero.mpr h))
  exact crossProduct_ne_zero_iff_linearIndependent.mp hne

/-- Lane support (LA5): a point in the affine hull of four coplanar points
whose first three are non-collinear lies on the difference span. -/
private theorem la5_coplanar_diff_span {x y z t : V3}
    (hcop : Coplanar ({x, y, z, t} : Set V3))
    (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3)) :
    (t - x : V3) ∈ Submodule.span ℝ ({y - x, z - x} : Set V3) := by
  have hLI := la5_notcollinear_li hcol
  obtain ⟨u, v, w, hsub⟩ := hcop
  have hxK : x ∈ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) := hsub (by simp)
  have hyK : y ∈ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) := hsub (by simp)
  have htK : t ∈ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) := hsub (by simp)
  have hp : (y - x : V3) ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction hyK hxK
  have hq : (z - x : V3) ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction (hsub (by simp)) hxK
  have hr : (t - x : V3) ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction htK hxK
  have hLIV3 : LinearIndependent ℝ ![(y - x : V3), (z - x : V3)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hPi : (∑ j, g j • ((![((y - x : V3) : Fin 3 → ℝ), ((z - x : V3) : Fin 3 → ℝ)] :
        Fin 2 → (Fin 3 → ℝ)) j)) = 0 := by
      simpa using congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hg
    exact Fintype.linearIndependent_iff.mp hLI g hPi i
  have hset : (Set.range ![y - x, z - x] : Set V3) = ({y - x, z - x} : Set V3) := by
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hs
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simpa using (Set.mem_singleton_iff.mp hs).symm⟩
  have hf2 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![y - x, z - x] : Set V3)) = 2 := by
    have := finrank_span_eq_card (R := ℝ) (M := V3) hLIV3
    simpa using this
  have hvs : vectorSpan ℝ ({u, v, w} : Set V3)
      = vectorSpan ℝ (Set.range ![u, v, w] : Set V3) := by
    rw [la5_range3]
  have hfrK : Module.finrank ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact finrank_vectorSpan_range_le ℝ ![u, v, w] (by norm_num)
  haveI hfdK : FiniteDimensional ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ (Set.toFinite _)
  have hle : Submodule.span ℝ (Set.range ![y - x, z - x] : Set V3)
      ≤ (affineSpan ℝ ({u, v, w} : Set V3)).direction := by
    rw [Submodule.span_le, hset]
    rintro s (rfl | rfl)
    · exact hp
    · exact hq
  have hEq : Submodule.span ℝ ({y - x, z - x} : Set V3)
      = (affineSpan ℝ ({u, v, w} : Set V3)).direction := by
    rw [← hset]
    exact Submodule.eq_of_le_of_finrank_eq hle
      (le_antisymm (Submodule.finrank_mono hle) (hfrK.trans hf2.ge))
  exact hEq ▸ hr

/-- HOL `COPLANAR_IFF_CROSS_DOT` (local_lemmas.hl:203). -/
theorem COPLANAR_IFF_CROSS_DOT {x y z t : V3} :
    Coplanar ({x, y, z, t} : Set V3) ↔
      (WithLp.toLp 2 (crossProduct ((y - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (t - x) = 0 := by
  constructor
  · intro hcop
    by_cases hcol : Collinear ℝ ({x, y, z} : Set V3)
    · have hz := (COLLINEAR_CROSS_0 (x := x) (y := y) (z := z)).mp hcol
      rw [hz]
      simp
    · have hmem := la5_coplanar_diff_span hcop hcol
      obtain ⟨a, b, hrab⟩ := Submodule.mem_span_pair.mp hmem
      have hrabPi : ((t : V3) : Fin 3 → ℝ) - ((x : V3) : Fin 3 → ℝ)
          = a • (((y - x : V3) : Fin 3 → ℝ)) + b • (((z - x : V3) : Fin 3 → ℝ)) :=
        (congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hrab).symm
      have hd1 : (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ))
          ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) = 0 :=
        (dotProduct_comm _ _).trans (dot_self_cross _ _)
      have hd2 : (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ))
          ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ) = 0 :=
        (dotProduct_comm _ _).trans (dot_cross_self _ _)
      rw [hrabPi, dotProduct_add, dotProduct_smul, dotProduct_smul, hd1, hd2]
      ring
  · intro h0
    have h0' : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((t - x : V3) : Fin 3 → ℝ) = 0 := h0
    by_cases hcol : Collinear ℝ ({x, y, z} : Set V3)
    · rcases eq_or_ne x y with hxy | hxy
      · -- x = y: use the triple {x, z, t}
        refine ⟨x, z, t, ?_⟩
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with hs | hs
        · rw [hs]; exact mem_affineSpan _ (by simp)
        rcases hs with hs | hs
        · rw [hs, ← hxy]; exact mem_affineSpan _ (by simp)
        rcases hs with hs | hs
        · rw [hs]; exact mem_affineSpan _ (by simp)
        · rw [hs]; exact mem_affineSpan _ (by simp)
      · -- x ≠ y: z lies on the line through x, y
        have hzmem : z ∈ affineSpan ℝ ({x, y} : Set V3) :=
          (collinear_triple_iff.mp hcol).resolve_right hxy
        refine ⟨x, y, t, ?_⟩
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with hs | hs
        · rw [hs]; exact mem_affineSpan _ (by simp)
        rcases hs with hs | hs
        · rw [hs]; exact mem_affineSpan _ (by simp)
        rcases hs with hs | hs
        · rw [hs]
          have hsub2 : ({x, y} : Set V3) ⊆ ({x, y, t} : Set V3) := by
            intro p hp
            simp at hp ⊢
            tauto
          exact (affineSpan_mono ℝ hsub2) hzmem
        · rw [hs]; exact mem_affineSpan _ (by simp)
    · -- main case: decompose and kill the cross component
      have hLI2 := la5_notcollinear_li hcol
      have hpne : ((y - x : V3) : Fin 3 → ℝ) ≠ 0 := by
        intro hhp
        have h1 : (y - x : V3) = 0 :=
          WithLp.ofLp_injective 2 (by simpa using hhp)
        exact hcol (collinear_triple_iff.mpr (Or.inr (sub_eq_zero.mp h1).symm))
      have hncross : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ≠ 0 := by
        intro hc
        exact hcol ((COLLINEAR_CROSS_0 (x := x) (y := y) (z := z)).mpr
          (la5_toLp_eq_zero.mpr hc))
      have hdotn : ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) = 0 := dot_self_cross _ _
      have hdotn2 : ((z - x : V3) : Fin 3 → ℝ) ⬝ᵥ (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) = 0 := dot_cross_self _ _
      have hnnpos : 0 < (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) := (dot_self_pos_iff _).mpr hncross
      have hLI3 : LinearIndependent ℝ ![((y - x : V3) : Fin 3 → ℝ),
          ((z - x : V3) : Fin 3 → ℝ), (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ))] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        simp only [Fin.sum_univ_three, la5_cons_val_zero', la5_cons_val_one',
          la5_cons_val_two] at hg
        have hd : (g 0 • (((y - x : V3) : Fin 3 → ℝ))
              + g 1 • (((z - x : V3) : Fin 3 → ℝ))
              + g 2 • (crossProduct ((y - x : V3) : Fin 3 → ℝ)
                ((z - x : V3) : Fin 3 → ℝ)))
            ⬝ᵥ (crossProduct ((y - x : V3) : Fin 3 → ℝ)
              ((z - x : V3) : Fin 3 → ℝ)) = 0 := by
          rw [hg, zero_dotProduct]
        rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          smul_dotProduct] at hd
        simp only [hdotn, hdotn2, smul_zero, add_zero, zero_add] at hd
        have hgn : g 2 = 0 := by
          rcases smul_eq_zero.mp hd with h' | h'
          · exact h'
          · exact absurd h' hnnpos.ne'
        rw [hgn, zero_smul, add_zero] at hg
        have hsum2 : (∑ j, (fun j => g (Fin.castSucc j)) j •
            ((![((y - x : V3) : Fin 3 → ℝ), ((z - x : V3) : Fin 3 → ℝ)] :
              Fin 2 → (Fin 3 → ℝ)) j)) = 0 := by
          simpa using hg
        fin_cases i
        · exact Fintype.linearIndependent_iff.mp hLI2 (fun j => g (Fin.castSucc j))
            hsum2 ⟨0, by norm_num⟩
        · exact Fintype.linearIndependent_iff.mp hLI2 (fun j => g (Fin.castSucc j))
            hsum2 ⟨1, by norm_num⟩
        · exact hgn
      obtain ⟨a, b, c, hdecomp⟩ := la5_span3 (M := (Fin 3 → ℝ)) (by simp) hLI3
        (u := ((t - x : V3) : Fin 3 → ℝ))
      have hkey : c * ((crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ))) = 0 := by
        have h1 : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
            ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((t - x : V3) : Fin 3 → ℝ) = 0 := h0'
        rw [hdecomp, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
          dotProduct_smul, dotProduct_comm, dot_self_cross, dotProduct_comm,
          dot_cross_self] at h1
        simpa using h1
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp hkey with h' | h'
        · exact h'
        · exact absurd h' hnnpos.ne'
      rw [hc0, zero_smul, add_zero] at hdecomp
      refine ⟨x, y, z, ?_⟩
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with hs | hs
      · rw [hs]; exact mem_affineSpan _ (by simp)
      rcases hs with hs | hs
      · rw [hs]; exact mem_affineSpan _ (by simp)
      rcases hs with hs | hs
      · rw [hs]; exact mem_affineSpan _ (by simp)
      · -- s = t
        rw [hs]
        have htx : (t : V3) - x = a • ((y : V3) - x) + b • ((z : V3) - x) := by
          refine WithLp.ofLp_injective 2 ?_
          rw [show (WithLp.ofLp (a • ((y : V3) - x) + b • ((z : V3) - x) : V3))
              = a • (((y : V3) - x : V3) : Fin 3 → ℝ)
                + b • (((z : V3) - x : V3) : Fin 3 → ℝ) from rfl]
          exact hdecomp
        have h1 : (t : V3) = x + (t - x) := by
          abel
        rw [h1, htx]
        have hyA : y -ᵥ x ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
          AffineSubspace.vsub_mem_direction (mem_affineSpan _ (by simp))
            (mem_affineSpan _ (by simp))
        have hzA : z -ᵥ x ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
          AffineSubspace.vsub_mem_direction (mem_affineSpan _ (by simp))
            (mem_affineSpan _ (by simp))
        have hxM : x ∈ (affineSpan ℝ ({x, y, z} : Set V3) : Set V3) := mem_affineSpan _ (by simp)
        rw [add_comm x (a • ((y : V3) - x) + b • ((z : V3) - x))]
        exact AffineSubspace.vadd_mem_of_mem_direction
          (((affineSpan ℝ ({x, y, z} : Set V3)).direction).add_mem
            (((affineSpan ℝ ({x, y, z} : Set V3)).direction).smul_mem a hyA)
            (((affineSpan ℝ ({x, y, z} : Set V3)).direction).smul_mem b hzA)) hxM

/-- HOL `CROSS_DOT_COPLANAR` (local_lemmas.hl:211). -/
theorem CROSS_DOT_COPLANAR {x y z : V3} :
    (WithLp.toLp 2 (crossProduct ((x : V3) : Fin 3 → ℝ)
      ((y : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ z = 0 ↔
      Coplanar ({0, x, y, z} : Set V3) := by
  have h := COPLANAR_IFF_CROSS_DOT (x := (0:V3)) (y := x) (z := y) (t := z)
  have hbridge : ((WithLp.toLp 2 (crossProduct ((x : V3) : Fin 3 → ℝ)
      ((y : V3) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ) ⬝ᵥ ((z : V3) : Fin 3 → ℝ) = 0 ↔
      ((WithLp.toLp 2 (crossProduct ((x - (0:V3) : V3) : Fin 3 → ℝ)
      ((y - (0:V3) : V3) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((z - (0:V3) : V3) : Fin 3 → ℝ) = 0 := by
    simp [sub_zero]
  exact hbridge.trans h.symm

/-- HOL `SUBSET_NOT_COLLINEAR_AFFINE_HULL_EQ` (local_lemmas.hl:219). -/
theorem SUBSET_NOT_COLLINEAR_AFFINE_HULL_EQ {a b c x y z : V3}
    (hsub : ({a, b, c} : Set V3) ⊆ affineSpan ℝ ({x, y, z} : Set V3))
    (hcol : ¬ Collinear ℝ ({a, b, c} : Set V3)) :
    affineSpan ℝ ({x, y, z} : Set V3) = affineSpan ℝ ({a, b, c} : Set V3) := by
  have hAI : AffineIndependent ℝ ![a, b, c] := affineIndependent_iff_not_collinear_set.mpr hcol
  have hA2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ![a, b, c] : Set V3)) = 2 :=
    hAI.finrank_vectorSpan (by norm_num)
  have hK2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ![x, y, z] : Set V3)) ≤ 2 :=
    finrank_vectorSpan_range_le ℝ ![x, y, z] (by norm_num)
  have hAK : affineSpan ℝ ({a, b, c} : Set V3) ≤ affineSpan ℝ ({x, y, z} : Set V3) :=
    affineSpan_le.mpr hsub
  have hdirA : (affineSpan ℝ ({a, b, c} : Set V3)).direction
      = vectorSpan ℝ (Set.range ![a, b, c] : Set V3) := by
    rw [direction_affineSpan, ← la5_range3]
  have hdirK : (affineSpan ℝ ({x, y, z} : Set V3)).direction
      = vectorSpan ℝ (Set.range ![x, y, z] : Set V3) := by
    rw [direction_affineSpan, ← la5_range3]
  haveI hfdA : FiniteDimensional ℝ (affineSpan ℝ ({a, b, c} : Set V3)).direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ (Set.toFinite _)
  haveI hfdK : FiniteDimensional ℝ (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ (Set.toFinite _)
  have hfdA2 : Module.finrank ℝ (affineSpan ℝ ({a, b, c} : Set V3)).direction = 2 := by
    rw [hdirA]
    exact hA2
  have hfdK2 : Module.finrank ℝ (affineSpan ℝ ({x, y, z} : Set V3)).direction ≤ 2 := by
    rw [hdirK]
    exact hK2
  have hdirEq : (affineSpan ℝ ({a, b, c} : Set V3)).direction
      = (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hAK)
      (le_antisymm (Submodule.finrank_mono (AffineSubspace.direction_le hAK))
        (hfdK2.trans hfdA2.ge))
  refine (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirEq ?_ hAK).symm
  rw [affineSpan_nonempty]
  exact ⟨a, by simp⟩

/-- HOL `THREE_NOT_COLL_DETER_PLANE` (local_lemmas.hl:258). -/
theorem THREE_NOT_COLL_DETER_PLANE {P : Set V3} {a b c : V3} (hP : plane_p2 P)
    (hsub : ({a, b, c} : Set V3) ⊆ P)
    (hcol : ¬ Collinear ℝ ({a, b, c} : Set V3)) :
    affineSpan ℝ ({a, b, c} : Set V3) = P := by
  obtain ⟨u, v, w, hnc, hPdef⟩ := hP
  have hsub2 : ({a, b, c} : Set V3) ⊆ affineSpan ℝ ({u, v, w} : Set V3) := by
    rw [← hPdef]
    exact hsub
  have h := SUBSET_NOT_COLLINEAR_AFFINE_HULL_EQ (a := a) (b := b) (c := c) (x := u) (y := v)
    (z := w) hsub2 hcol
  rw [hPdef, h]

/-- HOL `LOCAL_FAN_NOT_V_SING` (local_lemmas.hl:266). -/
theorem LOCAL_FAN_NOT_V_SING (h : localFan_p2 V E FF) : ¬ ∃ v : V3, V = {v} := by
  rintro ⟨v, rfl⟩
  obtain ⟨HS, hd, -, -, -, hfan, -, hdih⟩ := h
  have hcard : HS.darts.card = 1 := by
    rw [← Set.ncard_coe_finset, hd, FAN_SINGLETON_V_DARTS hfan rfl]
    simp
  rw [hdih.1] at hcard
  omega

/-- HOL `LOCAL_FAN_NOT_SING_FF` (local_lemmas.hl:288). -/
theorem LOCAL_FAN_NOT_SING_FF (h : localFan_p2 V E FF) :
    ¬ ∃ x : V3 × V3, FF = {x} := by
  rintro ⟨d, rfl⟩
  exact la5_not_face_card_one h (by simp)

/-- HOL `LOCAL_FAN_IN_FF_DISTINCT` (local_lemmas.hl:309). -/
theorem LOCAL_FAN_IN_FF_DISTINCT (h : localFan_p2 V E FF) {d : V3 × V3}
    (hd : d ∈ FF) : d.1 ≠ d.2 := by
  intro hself
  have h1 : FF = {d} := la5_face_singleton_of_mem_self h hd hself
  exact la5_not_face_card_one h (by rw [h1]; simp)


/-- HOL `LOCAL_FAN_IN_FF_IN_ORD_PAIRS` (local_lemmas.hl:338). -/
theorem LOCAL_FAN_IN_FF_IN_ORD_PAIRS (h : localFan_p2 V E FF) {d : V3 × V3}
    (hd : d ∈ FF) : d ∈ ordPairs_p2 E := by
  have hdD : d ∈ dartsOfHyp_p2 E V := la5_FF_subset_darts h hd
  have hne := LOCAL_FAN_IN_FF_DISTINCT h hd
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := h
  rcases Set.mem_or_mem_of_mem_union hdD with ho | hs
  · exact ho
  · exact absurd ((FAN_IN_DARTS_FST_EQ_SND_SELF_PAIRS hfan hdD).mpr hs) hne

/-- HOL `LOCAL_FAN_IN_FF_NOT_COLLINEAR` (local_lemmas.hl:364). -/
theorem LOCAL_FAN_IN_FF_NOT_COLLINEAR (h : localFan_p2 V E FF) {d : V3 × V3}
    (hd : d ∈ FF) : ¬ Collinear ℝ ({0, d.1, d.2} : Set V3) := by
  have hE := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hd
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := h
  exact hfan.2.2.2.2.1 _ hE

/-- HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE` (local_lemmas.hl:377). -/
theorem LOCAL_FAN_CHARACTER_OF_RHO_NODE (h : localFan_p2 V E FF) {v : V3}
    (hv : v ∈ V) :
    rhoNode1_p2 FF v ≠ v ∧ (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 E ∧
      ¬ Collinear ℝ ({0, v, rhoNode1_p2 FF v} : Set V3) := by
  -- B5 free-cascade wave: HOL route (local_lemmas.hl:377) — the dart
  -- `(v, rho v)` comes from LOCAL_FAN_RHO_NODE_PROS (now real, WRGCVDR_BIJ
  -- cascade), then the three proven IN_FF lemmas read off the conjuncts.
  -- (conjunct-by-conjunct `intro` avoids unifying projections against the
  -- epsilon-shaped goal type: 54cb5660's whnf-heartbeat mine.)
  have hdart : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h).1 v hv
  refine ⟨?_, ?_, ?_⟩
  · intro hcon
    exact LOCAL_FAN_IN_FF_DISTINCT h hdart hcon.symm
  · exact LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdart
  · -- t3b-form (probe r4): the direct `exact LOCAL_FAN_IN_FF_NOT_COLLINEAR h hdart`
    -- hangs in the postponed-unification isDefEq path (300k-cap whnf timeout);
    -- ascribing the projection-shaped type first, then exacting, is instant.
    have hnc : ¬ Collinear ℝ ({0, (v, rhoNode1_p2 FF v).1, (v, rhoNode1_p2 FF v).2} : Set V3) :=
      LOCAL_FAN_IN_FF_NOT_COLLINEAR h hdart
    exact hnc

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
    ¬ ∃ v1 v2 : V3, V = {v1, v2} ∧ ({v1, v2} : Set V3) ∈ E := by
  have hkeep := h
  rintro ⟨v1, v2, rfl, he⟩
  obtain ⟨HS, hd, -, -, -, hfan, -, hdih⟩ := h
  have hne : (v1:V3) ≠ v2 := GRAPH_WITH_SET2 hfan.2.1 v1 v2 he
  have hcard : HS.darts.card = 2 := by
    rw [← Set.ncard_coe_finset, hd, FAN_V_TWO_ELMS_IN_E_DARTS2 hfan rfl he]
    simp [hne]
  rw [hdih.1] at hcard
  exact la5_not_face_card_one hkeep (by omega)

/-- HOL `LOCAL_FAN_ORBIT_MAP_V` (local_lemmas.hl:469) — filled (orbit wave
2026-10-08) by the generic-WRGCVDR orbit half `WRGCVDR_ORBIT` (LocalAuto2,
localization.hl:365; HOL WRGCVDR.hl:2622 second conjunct, with
`hro := rho_node1 FF` from `LOCAL_FAN_RHO_NODE_PROS`). -/
theorem LOCAL_FAN_ORBIT_MAP_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    orbitF_p2 (rhoNode1_p2 FF) v = V :=
  WRGCVDR_ORBIT h v hv

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

/-- HOL `LOCAL_FAN_ITER_RHO_NODE_IN_V` (local_lemmas.hl:652) — filled (orbit
wave 2026-10-08): the orbit closure `LOCAL_FAN_ORBIT_MAP_V` contains every
iterate. -/
theorem LOCAL_FAN_ITER_RHO_NODE_IN_V (h : localFan_p2 V E FF) {v : V3}
    (hv : v ∈ V) : ∀ i : ℕ, (rhoNode1_p2 FF)^[i] v ∈ V := by
  intro i
  have h1 : (rhoNode1_p2 FF)^[i] v ∈ orbitF_p2 (rhoNode1_p2 FF) v := ⟨i, rfl⟩
  rwa [LOCAL_FAN_ORBIT_MAP_V h hv] at h1


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

/-- Lane support (LA5 r3): `q`-periodic points stay fixed under multiples
of the period. -/
private theorem la5_period_mul {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (k : ℕ) : f^[k * q] x = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, hqx, ih]

/-- Lane support (LA5 r3): index reduction modulo a period. -/
private theorem la5_period_mod {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (n : ℕ) : f^[n] x = f^[n % q] x := by
  have hsplit : n / q * q + n % q = n := Nat.div_add_mod' n q
  have hqx' : f^[q] (f^[n % q] x) = f^[n % q] x := by
    rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hqx]
  calc f^[n] x = f^[n / q * q + n % q] x := by rw [hsplit]
    _ = f^[n / q * q] (f^[n % q] x) := Function.iterate_add_apply f (n / q * q) (n % q) x
    _ = f^[n % q] x := la5_period_mul f hqx' (n / q)

/-- Lane support (LA5 r3): under the orbit condition, coinciding iterates
of a point force it to be periodic with the index difference (the second
point lies in the orbit of the first). -/
private theorem la5_orbit_key {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ x ∈ V, orbitF_p2 f x = V) {x : α} (hx : x ∈ V) {i j : ℕ}
    (hij2 : i ≤ j) (hij : f^[i] x = f^[j] x) : f^[j - i] x = x := by
  have hEq : j - i + i = j := by omega
  have hy : f^[j] x = f^[j - i] (f^[i] x) := by
    have h := Function.iterate_add_apply f (j - i) i x
    rwa [hEq] at h
  have hmem : ∀ n : ℕ, f^[n] x ∈ V := by
    intro n
    rw [← horb x hx]
    exact ⟨n, rfl⟩
  have hyV : f^[i] x ∈ V := hmem i
  have hxO : x ∈ orbitF_p2 f (f^[i] x) := by rw [horb (f^[i] x) hyV]; exact hx
  obtain ⟨t, hxt⟩ := hxO
  have hfix : f^[j - i] (f^[i] x) = f^[i] x := hy.symm.trans hij.symm
  calc f^[j - i] x = f^[j - i] (f^[t] (f^[i] x)) := by rw [hxt]
    _ = f^[(j - i) + t] (f^[i] x) := (Function.iterate_add_apply f (j - i) t (f^[i] x)).symm
    _ = f^[t + (j - i)] (f^[i] x) := by rw [Nat.add_comm]
    _ = f^[t] (f^[j - i] (f^[i] x)) := Function.iterate_add_apply f t (j - i) (f^[i] x)
    _ = f^[t] (f^[i] x) := by rw [hfix]
    _ = x := hxt

/-- Lane support (LA5 r3): the orbit condition makes `V` a finite cycle;
`p` is a common period with `0 < p`, the first `p` iterates are pairwise
distinct and exhaust `V`, and `V.ncard = p`. -/
private theorem la5_orbit_cycle {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ x ∈ V, orbitF_p2 f x = V) {x : α} (hx : x ∈ V) :
    ∃ p : ℕ, 0 < p ∧ f^[p] x = x ∧
      (∀ i j : ℕ, i < j → j < p → f^[i] x ≠ f^[j] x) ∧
      ({f^[n] x | n < p} : Set α) = V ∧ V.ncard = p := by
  have hmem : ∀ n : ℕ, f^[n] x ∈ V := by
    intro n
    rw [← horb x hx]
    exact ⟨n, rfl⟩
  have hper : ∃ p : ℕ, 0 < p ∧ f^[p] x = x := by
    have hfx : f x ∈ V := hmem 1
    have hxO : x ∈ orbitF_p2 f (f x) := by rw [horb (f x) hfx]; exact hx
    obtain ⟨n, hn⟩ := hxO
    exact ⟨n + 1, Nat.succ_pos n, by rw [Function.iterate_succ_apply f n x]; exact hn⟩
  have hex : ∃ n, 0 < n ∧ f^[n] x = x := hper
  have hp0 : 0 < Nat.find hex := (Nat.find_spec hex).1
  have hpx : f^[Nat.find hex] x = x := (Nat.find_spec hex).2
  have hmin : ∀ m : ℕ, 0 < m → m < Nat.find hex → f^[m] x ≠ x :=
    fun m hm0 hmlt hcon => Nat.find_min hex hmlt ⟨hm0, hcon⟩
  have hkey : ∀ i j : ℕ, i ≤ j → f^[i] x = f^[j] x → f^[j - i] x = x :=
    fun i j hle hij' => la5_orbit_key horb hx hle hij'
  have hdis : ∀ i j : ℕ, i < j → j < Nat.find hex → f^[i] x ≠ f^[j] x := by
    intro i j hij hjp hcon
    exact hmin (j - i) (by omega) (by omega) (hkey i j (Nat.le_of_lt hij) hcon)
  have hset : ({f^[n] x | n < Nat.find hex} : Set α) = V := by
    ext y
    constructor
    · rintro ⟨n, -, rfl⟩
      exact hmem n
    · intro hy
      have hYO : y ∈ orbitF_p2 f x := by rw [horb x hx]; exact hy
      obtain ⟨m, hm⟩ := hYO
      refine ⟨m % Nat.find hex, Nat.mod_lt _ hp0, ?_⟩
      rw [← la5_period_mod f hpx m]
      exact hm
  have hcard : V.ncard = Nat.find hex := by
    have himage : ({f^[n] x | n < Nat.find hex} : Set α) =
        (fun n : ℕ => f^[n] x) '' Set.Iio (Nat.find hex) := rfl
    rw [← hset, himage]
    have hInj : Set.InjOn (fun n : ℕ => f^[n] x) (Set.Iio (Nat.find hex)) := by
      intro i hi j hj hcon
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact absurd hcon (hdis i j h (Set.mem_Iio.mp hj))
      · exact h
      · exact absurd hcon.symm (hdis j i h (Set.mem_Iio.mp hi))
    rw [Set.InjOn.ncard_image hInj]
    exact Set.ncard_Iio_nat _
  exact ⟨Nat.find hex, hp0, hpx, hdis, hset, hcard⟩

/-- Lane support (LA5 r3): a positive normalized two-point combination is in
the open segment. -/
private theorem la5_seg_member {p v w : V3} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (a + b) • p = a • v + b • w) : p ∈ conv0_p2 ({v, w} : Set V3) := by
  have hab : a + b ≠ 0 := by linarith
  by_cases hvw : v = w
  · subst hvw
    have hpa : p = v := by
      rw [← add_smul a b v] at h
      exact smul_right_injective V3 hab h
    have hfin₀ : (((∅ : Set V3) ∪ ({v, v} : Set V3))).Finite := by simp
    have hEq : hfin₀.toFinset = ({v} : Finset V3) := by ext z; simp
    refine ⟨fun _ => 1, hfin₀, ?_, ?_, ?_⟩
    · rw [hpa, hEq, Finset.sum_singleton, one_smul]
    · intro z hz
      norm_num
    · rw [hEq, Finset.sum_singleton]
  · have hp' : p = (a / (a + b)) • v + (b / (a + b)) • w := by
      have e1 : p = (1 / (a + b)) • ((a + b) • p) := by
        rw [smul_smul, show (1:ℝ) / (a + b) * (a + b) = 1 from by field_simp, one_smul]
      rw [e1, h, smul_add, smul_smul, smul_smul,
        show (1:ℝ) / (a + b) * a = a / (a + b) from by ring,
        show (1:ℝ) / (a + b) * b = b / (a + b) from by ring]
    have hfin₀ : (((∅ : Set V3) ∪ ({v, w} : Set V3))).Finite := by simp
    have hEq : hfin₀.toFinset = ({v, w} : Finset V3) := by ext z; simp [hvw]
    have hv0 : (fun z : V3 => if z = v then a / (a + b) else b / (a + b)) v = a / (a + b) :=
      if_pos rfl
    have hw0 : (fun z : V3 => if z = v then a / (a + b) else b / (a + b)) w = b / (a + b) :=
      if_neg (Ne.symm hvw)
    refine ⟨fun z => if z = v then a / (a + b) else b / (a + b), hfin₀, ?_, ?_, ?_⟩
    · rw [hEq, Finset.sum_insert (show ¬((v:V3) ∈ ({w} : Finset V3)) from by simp [hvw]),
        Finset.sum_singleton, hv0, hw0, hp']
    · intro z hz
      have hz' : z = v ∨ z = w := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        tauto
      rcases hz' with hzv | hzw
      · rw [hzv, hv0]
        exact div_pos ha (by linarith)
      · rw [hzw, hw0]
        exact div_pos hb (by linarith)
    · rw [hEq, Finset.sum_insert (show ¬((v:V3) ∈ ({w} : Finset V3)) from by simp [hvw]),
        Finset.sum_singleton, if_pos rfl, if_neg (Ne.symm hvw)]
      field_simp

/-- Lane support (LA5 r3): the intersection point of the `x u` line with the
open segment, in coefficient form. -/
private theorem la5_lineMap_seg_eq {x u v w : V3} {b' b c : ℝ}
    (hcore : b' • (u - x) = b • (v - x) + c • (w - x)) (hbc : 0 < b + c) :
    (b + c) • (AffineMap.lineMap x u (b' / (b + c))) = b • v + c • w := by
  have hb0 : (b:ℝ) + c ≠ 0 := by linarith
  have hsc : ((b:ℝ) + c) * (b' / ((b:ℝ) + c)) = b' := by field_simp
  rw [AffineMap.lineMap_apply_module', smul_add, smul_smul, hsc, hcore]
  module

/-- Lane support (LA5 r3): an affine span is closed under `lineMap`. -/
private theorem la5_lineMap_mem_span {S : Set V3} {p q : V3} (s : ℝ)
    (hp : p ∈ (affineSpan ℝ S : Set V3)) (hq : q ∈ (affineSpan ℝ S : Set V3)) :
    AffineMap.lineMap p q s ∈ (affineSpan ℝ S : Set V3) := by
  have h1 : q -ᵥ p ∈ (affineSpan ℝ S).direction :=
    AffineSubspace.vsub_mem_direction hq hp
  have h2 : AffineMap.lineMap p q s -ᵥ p ∈ (affineSpan ℝ S).direction := by
    rw [AffineMap.lineMap_vsub_left]
    exact (affineSpan ℝ S).direction.smul_mem s h1
  have h3 := AffineSubspace.vadd_mem_of_mem_direction h2 hp
  rwa [vsub_vadd] at h3

/-- Lane support (LA5 r3): extraction of the ray form from `affGt {x} {v, w}`
(valid for all coincidence patterns of the three points). -/
private theorem la5_affGt_extract {x v w t : V3}
    (ht : t ∈ affGt ({x} : Set V3) ({v, w} : Set V3)) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ t - x = b • (v - x) + c • (w - x) := by
  obtain ⟨f, hfin, hvec, hpos, hsum⟩ := ht
  have hEqPair : ∀ {a b : V3} (h : ({a} ∪ {b, b} : Set V3).Finite),
      h.toFinset = ({a, b} : Finset V3) := by
    intro a b h
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hEq3 : ∀ {a b : V3} (h : ({a} ∪ {a, b} : Set V3).Finite),
      h.toFinset = ({a, b} : Finset V3) := by
    intro a b h
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  by_cases hvw : v = w
  · subst hvw
    by_cases hxv : x = v
    · subst hxv
      have hEq : hfin.toFinset = ({x} : Finset V3) := by ext z; simp
      rw [hEq] at hvec hsum
      simp only [Finset.sum_singleton] at hvec hsum
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, ?_⟩
      rw [hvec, hsum, one_smul]
      module
    · have hEq : hfin.toFinset = ({x, v} : Finset V3) := hEqPair hfin
      rw [hEq] at hvec hsum
      rw [Finset.sum_insert (Finset.mem_singleton.not.mpr hxv),
        Finset.sum_singleton] at hvec hsum
      have hfv : 0 < f v := hpos v (by simp)
      refine ⟨f v / 2, f v / 2, div_pos hfv (by linarith), div_pos hfv (by linarith), ?_⟩
      have hx1 : x = (f x + f v) • x := by rw [hsum, one_smul]
      rw [hvec]
      nth_rewrite 3 [hx1]
      module
  · by_cases hxv : x = v
    · subst hxv
      have hEq : hfin.toFinset = ({x, w} : Finset V3) := hEq3 hfin
      rw [hEq] at hvec hsum
      rw [Finset.sum_insert (Finset.mem_singleton.not.mpr hvw),
        Finset.sum_singleton] at hvec hsum
      refine ⟨f x, f w, hpos x (by simp), hpos w (by simp), ?_⟩
      have hx1 : x = (f x + f w) • x := by rw [hsum, one_smul]
      rw [hvec]
      nth_rewrite 3 [hx1]
      module
    · by_cases hxw : x = w
      · subst hxw
        have hEq : hfin.toFinset = ({x, v} : Finset V3) := by
          ext z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hEq] at hvec hsum
        rw [Finset.sum_insert (Finset.mem_singleton.not.mpr hxv),
          Finset.sum_singleton] at hvec hsum
        refine ⟨f v, f x, hpos v (by simp), hpos x (by simp), ?_⟩
        have hx1 : x = (f x + f v) • x := by rw [hsum, one_smul]
        rw [hvec]
        nth_rewrite 3 [hx1]
        module
      · have hEq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          ext z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        rw [hEq] at hvec hsum
        rw [Finset.sum_insert (show ¬((x:V3) ∈ ({v, w} : Finset V3)) from by simp [hxv, hxw]),
          Finset.sum_insert (Finset.mem_singleton.not.mpr hvw),
          Finset.sum_singleton] at hvec hsum
        refine ⟨f v, f w, hpos v (by simp), hpos w (by simp), ?_⟩
        have hx1 : x = (f x + (f v + f w)) • x := by rw [hsum, one_smul]
        rw [hvec]
        nth_rewrite 3 [hx1]
        module

/-- Lane support (LA5 r3): extraction of the ray form from `affLt {x} {u}`. -/
private theorem la5_affLt_extract {x u t : V3}
    (ht : t ∈ affLt ({x} : Set V3) ({u} : Set V3)) :
    ∃ b : ℝ, b < 0 ∧ t - x = b • (u - x) := by
  obtain ⟨f, hfin, hvec, hneg, hsum⟩ := ht
  by_cases hxu : x = u
  · subst hxu
    have hEq : hfin.toFinset = ({x} : Finset V3) := by ext z; simp
    rw [hEq] at hvec hsum
    simp only [Finset.sum_singleton] at hvec hsum
    have h1 : (f x : ℝ) = 1 := hsum
    have h2 : (f x : ℝ) < 0 := hneg x (Set.mem_singleton x)
    exfalso
    linarith
  · have hEq : hfin.toFinset = ({x, u} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    rw [hEq] at hvec hsum
    rw [Finset.sum_insert (Finset.mem_singleton.not.mpr hxu),
      Finset.sum_singleton] at hvec hsum
    refine ⟨f u, hneg u (Set.mem_singleton u), ?_⟩
    have hx1 : x = (f x + f u) • x := by rw [hsum, one_smul]
    rw [hvec]
    nth_rewrite 3 [hx1]
    module

/-- Lane support (LA5 r3): line re-parameterization through two fixed points. -/
private theorem la5_lineMap_reparam {a b x y : V3} {r s : ℝ} (hrs : s ≠ r)
    (hx : x = (1 - r) • a + r • b) (hy : y = (1 - s) • a + s • b) (c t : ℝ)
    (hct : r + c * (s - r) = t) :
    AffineMap.lineMap x y c = AffineMap.lineMap a b t := by
  have pfA : ((1:ℝ) - c) * (1 - r) + c * (1 - s) = 1 - t := by
    have h9 : ((1:ℝ) - c) * (1 - r) + c * (1 - s) = 1 - (((1:ℝ) - c) * r + c * s) := by ring
    rw [h9, show ((1:ℝ) - c) * r + c * s = r + c * (s - r) from by ring, hct]
  have pfB : ((1:ℝ) - c) * r + c * s = t := by
    rw [show ((1:ℝ) - c) * r + c * s = r + c * (s - r) from by ring, hct]
  rw [AffineMap.lineMap_apply_module, hx, hy, AffineMap.lineMap_apply_module, smul_add,
    smul_add, smul_smul, smul_smul, smul_smul, smul_smul, ← hct]
  module

/-- HOL `LOOP_MAP_IMP_DIFF_FIRST_ELMS` (local_lemmas.hl:1625). -/
theorem LOOP_MAP_IMP_DIFF_FIRST_ELMS {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V) {k l : ℕ}
    (hk : k < V.ncard) (hl : l < k) : f^[k] v ≠ f^[l] v := by
  obtain ⟨p, hp0, hpx, hdis, -, hcard⟩ := la5_orbit_cycle horb hv
  rw [hcard] at hk
  intro hcon
  have hd : f^[k - l] v = v := la5_orbit_key horb hv (Nat.le_of_lt hl) hcon.symm
  exact hdis 0 (k - l) (by omega) (by omega) hd.symm


/-- HOL `CARD_IMAGE_INJ2` (local_lemmas.hl:1656). -/
theorem CARD_IMAGE_INJ2 {α β : Type*} {f : α → β} {A : Set α} {B : Set β}
    (h : Set.InjOn f A) (hfin : A.Finite) : (Set.image f A).ncard = A.ncard :=
  Set.InjOn.ncard_image h

/-- HOL `BIJ_IMP_CARD_EQ` (local_lemmas.hl:1663). -/
theorem BIJ_IMP_CARD_EQ {α β : Type*} {f : α → β} {A : Set α} {B : Set β}
    (h : Set.BijOn f A B) (hfin : A.Finite) : A.ncard = B.ncard := by
  have h2 : Set.image f A = B := h.image_eq
  rw [← h2, Set.InjOn.ncard_image h.injOn]

/-- HOL `LOFA_IMP_DIS_ELMS` (local_lemmas.hl:1669) — filled (orbit wave
2026-10-08): `LOCAL_FAN_ORBIT_MAP_V` makes `V` the rho-cycle of minimal
period `p = V.ncard = FF.ncard` (`la5_orbit_cycle` + `BIJ_IMP_CARD_EQ`
through `WRGCVDR_BIJ`), and the first `p` iterates are pairwise distinct. -/
theorem LOFA_IMP_DIS_ELMS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {l : ℕ} (hl : l < FF.ncard) :
    ∀ i : ℕ, i < l → (rhoNode1_p2 FF)^[l] v ≠ (rhoNode1_p2 FF)^[i] v := by
  obtain ⟨p, hp0, hpx, hdis, -, hcard⟩ :=
    la5_orbit_cycle (fun x hx => LOCAL_FAN_ORBIT_MAP_V h hx) hv
  have hfinFF : FF.Finite := by
    obtain ⟨HS, -, -, -, -, -, ⟨x, hx, hFx⟩, -⟩ := h
    refine Set.Finite.subset HS.darts.finite_toSet ?_
    rw [hFx]
    exact HS.face_subset_darts hx
  have hFFV : FF.ncard = V.ncard := BIJ_IMP_CARD_EQ (WRGCVDR_BIJ h) hfinFF
  have hlp : l < p := by rw [hFFV, hcard] at hl; exact hl
  intro i hi
  exact (hdis i l hi hlp).symm

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
    azim v0 v1 x y ≤ azim v0 v1 w1 w2 := by
  have hv10 : (v1:V3) ≠ v0 := fun h => hw1 (collinear3_of_eq h)
  have e1 := sum4_azim_fan hv10 hw1 hx hy2 hxy
  have hn : 0 ≤ azim v0 v1 w1 x := azim_nonneg v0 v1 w1 x
  calc azim v0 v1 x y ≤ azim v0 v1 w1 y := by linarith
    _ ≤ azim v0 v1 w1 w2 := hy.2

/-- HOL `LOFA_IMAGE_RHO_NODE_IDE` (local_lemmas.hl:1762) — filled (LA5
downstream wave 2026-10-08): rho preserves `V` (orbit) and the cycle
predecessor `rho^[p-1] x` maps onto `x` (`la5_orbit_cycle` minimal period). -/
theorem LOFA_IMAGE_RHO_NODE_IDE (h : localFan_p2 V E FF) :
    Set.image (rhoNode1_p2 FF) V = V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : rhoNode1_p2 FF y ∈ orbitF_p2 (rhoNode1_p2 FF) y := ⟨1, rfl⟩
    rwa [LOCAL_FAN_ORBIT_MAP_V h hy] at h1
  · intro hx
    obtain ⟨p, hp0, hpx, -, -, -⟩ :=
      la5_orbit_cycle (fun _u hu => LOCAL_FAN_ORBIT_MAP_V h hu) hx
    have hmem : (rhoNode1_p2 FF)^[p - 1] x ∈ orbitF_p2 (rhoNode1_p2 FF) x := ⟨p - 1, rfl⟩
    rw [LOCAL_FAN_ORBIT_MAP_V h hx] at hmem
    refine ⟨(rhoNode1_p2 FF)^[p - 1] x, hmem, ?_⟩
    have h2 : (rhoNode1_p2 FF)^[p - 1 + 1] x
        = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[p - 1] x) :=
      Function.iterate_succ_apply' _ _ _
    rw [← h2, show p - 1 + 1 = p by omega]
    exact hpx

/-- HOL `EXISTS_INVERSE_OF_V` (local_lemmas.hl:1769) — filled (LA5
downstream wave 2026-10-08): same cycle-predecessor witness. -/
theorem EXISTS_INVERSE_OF_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ∃ vv : V3, vv ∈ V ∧ rhoNode1_p2 FF vv = v := by
  obtain ⟨p, hp0, hpx, -, -, -⟩ :=
    la5_orbit_cycle (fun _u hu => LOCAL_FAN_ORBIT_MAP_V h hu) hv
  have hmem : (rhoNode1_p2 FF)^[p - 1] v ∈ orbitF_p2 (rhoNode1_p2 FF) v := ⟨p - 1, rfl⟩
  rw [LOCAL_FAN_ORBIT_MAP_V h hv] at hmem
  refine ⟨(rhoNode1_p2 FF)^[p - 1] v, hmem, ?_⟩
  have h2 : (rhoNode1_p2 FF)^[p - 1 + 1] v
      = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[p - 1] v) :=
    Function.iterate_succ_apply' _ _ _
  rw [← h2, show p - 1 + 1 = p by omega]
  exact hpx

/-- HOL `LOFA_IN_V_SO_DO_RHO_NODE_V` (local_lemmas.hl:1776) — filled (LA5
downstream wave 2026-10-08): one-step orbit membership. -/
theorem LOFA_IN_V_SO_DO_RHO_NODE_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    rhoNode1_p2 FF v ∈ V := by
  have h1 : rhoNode1_p2 FF v ∈ orbitF_p2 (rhoNode1_p2 FF) v := ⟨1, rfl⟩
  rwa [LOCAL_FAN_ORBIT_MAP_V h hv] at h1

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

/-- Lane support (LA5 r2): every point of a self-cyclic set is periodic. -/
private theorem la5_orbit_period {α : Type*} (f : α → α) {S : Set α}
    (h : ∀ x ∈ S, S = orbitF_p2 f x) {x : α} (hx : x ∈ S) :
    ∃ p : ℕ, 0 < p ∧ f^[p] x = x := by
  have hfx : f x ∈ S := by
    rw [h x hx]
    exact ⟨1, rfl⟩
  have h2 := h (f x) hfx
  have hxmem : x ∈ orbitF_p2 f (f x) := by rw [← h2]; exact hx
  obtain ⟨n, hn⟩ := hxmem
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [Function.iterate_succ_apply f n x]
  exact hn

/-- Lane support (LA5 r2): the least period of a periodic point. -/
private theorem la5_min_period {α : Type*} (f : α → α) {x : α} {p : ℕ}
    (hp : 0 < p) (hpx : f^[p] x = x) :
    ∃ q : ℕ, 0 < q ∧ q ≤ p ∧ f^[q] x = x ∧ ∀ i : ℕ, 0 < i → i < q → f^[i] x ≠ x := by
  have hex : ∃ n, 0 < n ∧ f^[n] x = x := ⟨p, hp, hpx⟩
  have hspec : 0 < Nat.find hex ∧ f^[Nat.find hex] x = x := Nat.find_spec hex
  refine ⟨Nat.find hex, hspec.1, Nat.find_le ⟨hp, hpx⟩, hspec.2, ?_⟩
  intro i hi0 hilt hcon
  exact Nat.find_min hex hilt ⟨hi0, hcon⟩

/-- Lane support (LA5 r2): `q`-periodic points have `q`-multiple periods. -/
private theorem la5_iterate_mul {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (k : ℕ) : f^[k * q] x = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, hqx, ih]

/-- Lane support (LA5 r2): index reduction modulo a period. -/
private theorem la5_iterate_mod {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (n : ℕ) : f^[n] x = f^[n % q] x := by
  have hsplit : n / q * q + n % q = n := Nat.div_add_mod' n q
  have hqx' : f^[q] (f^[n % q] x) = f^[n % q] x := by
    rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hqx]
  calc f^[n] x = f^[n / q * q + n % q] x := by rw [hsplit]
    _ = f^[n / q * q] (f^[n % q] x) := Function.iterate_add_apply f (n / q * q) (n % q) x
    _ = f^[n % q] x := la5_iterate_mul f hqx' (n / q)


/-- Lane support (LA5 r2): a self-cyclic set is finite (placed before
`LOOP_MAP_IMP_DIFF_FIRST_ELMS`, which sits earlier in the file). -/
private theorem la5_self_cyclic_finite {α : Type*} (f : α → α) (V : Set α)
    (h : ∀ x ∈ V, V = orbitF_p2 f x) : V.Finite := by
  by_cases hV : V = ∅
  · rw [hV]
    exact Set.finite_empty
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hV
    obtain ⟨p, hp0, hper⟩ := la5_orbit_period f h hx₀
    have hsub : V ⊆ ({f^[i] x₀ | i < p} : Set α) := by
      rw [h x₀ hx₀]
      intro y hy
      obtain ⟨m, hm⟩ := hy
      have hr : m % p < p := Nat.mod_lt _ hp0
      refine ⟨m % p, hr, ?_⟩
      exact (la5_iterate_mod f hper m).symm.trans hm
    exact (FINTE_OF_N_FIRST_ELMS2 f x₀ p).subset hsub

/-- HOL `SELF_CYCLIC_IMP_FINITE` (local_lemmas.hl:1843): the orbit condition
forces finiteness (in HOL via the cyclic-orbit machinery; the plain-function
rendering keeps the statement, see the HL proof's `ITER_CYCLIC_ORBIT`). -/
theorem SELF_CYCLIC_IMP_FINITE {α : Type*} (f : α → α) (V : Set α)
    (h : ∀ x ∈ V, V = orbitF_p2 f x) : V.Finite :=
  la5_self_cyclic_finite f V h


/-- HOL `SELF_CYCLIC_IMP_BIJ` (local_lemmas.hl:1879). -/
theorem SELF_CYCLIC_IMP_BIJ {α : Type*} (f : α → α) (S : Set α)
    (h : ∀ x ∈ S, S = orbitF_p2 f x) : Set.BijOn f S S := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [h y hy]
    exact ⟨1, rfl⟩
  · -- InjOn: least-period argument; only iterate_add/succ identities, no
    -- stripping of `f` (f need not be injective off `S`)
    intro a ha b hb hab
    obtain ⟨q0, hq0, hqb⟩ := la5_orbit_period f h hb
    obtain ⟨q, hqpos, -, hqb', hmin⟩ := la5_min_period f hq0 hqb
    have hxmem : a ∈ orbitF_p2 f b := by rw [← h b hb]; exact ha
    obtain ⟨m, hm⟩ := hxmem
    have hage : a = f^[m % q] b := by rw [← hm, la5_iterate_mod f hqb' m]
    by_cases hr0 : m % q = 0
    · rw [hage, hr0, Function.iterate_zero_apply]
    · have hr1 : 0 < m % q := Nat.pos_of_ne_zero hr0
      have hrq : m % q < q := Nat.mod_lt _ hqpos
      have hstep : f (f^[m % q] b) = f b := by rw [← hage, hab]
      have hc : f^[m % q] (f b) = f b := by
        rw [← Function.iterate_succ_apply f (m % q) b,
          Function.iterate_succ_apply' f (m % q) b]
        exact hstep
      have hbq : b = f^[q - 1] (f b) := calc
        b = f^[q] b := hqb'.symm
        _ = f^[(q - 1) + 1] b := by rw [show (q - 1) + 1 = q from by omega]
        _ = f^[q - 1] (f b) := Function.iterate_add_apply f (q - 1) 1 b
      have hra : f^[m % q] b = b := by
        rw [hbq, ← Function.iterate_add_apply, Nat.add_comm,
          Function.iterate_add_apply, hc]
      rw [hage, hra]
  · intro z hz
    obtain ⟨q, hq0, hqz⟩ := la5_orbit_period f h hz
    refine ⟨f^[q - 1] z, ?_, ?_⟩
    · rw [h z hz]
      exact ⟨q - 1, rfl⟩
    · rw [← Function.iterate_succ_apply' f (q - 1) z,
        show (q - 1).succ = q from by omega, hqz]

/-- Lane support (LA5 r2): under the least period the first `p` iterates are
pairwise distinct (backward-orbit commutation, no stripping of `f`). -/
private theorem la5_min_period_inj {α : Type*} (f : α → α) {x : α} {p : ℕ}
    (hpx : f^[p] x = x) (hmin : ∀ i : ℕ, 0 < i → i < p → f^[i] x ≠ x) :
    Set.InjOn (fun n => f^[n] x) (Set.Iio p) := by
  have key : ∀ i j : ℕ, i < j → j < p → f^[i] x = f^[j] x → False := by
    intro i j hij hjp hcon
    have hd1 : 0 < j - i := by omega
    have hdp : j - i < p := by omega
    have hcd : f^[j - i] (f^[i] x) = f^[i] x := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hij),
        ← hcon]
    have hxback : x = f^[p - i] (f^[i] x) := by
      have e1 : f^[p - i] (f^[i] x) = f^[(p - i) + i] x :=
        (Function.iterate_add_apply f (p - i) i x).symm
      rw [e1, show (p - i) + i = p from by omega, hpx]
    have hdx : f^[j - i] x = x := by
      rw [hxback, ← Function.iterate_add_apply, Nat.add_comm,
        Function.iterate_add_apply, hcd, ← hxback]
    exact absurd hdx (hmin (j - i) hd1 hdp)
  intro i hi j hj hcon
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hcon (key i j h hj)
  · exact h
  · exact absurd hcon.symm (key j i h hi)

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

/-- HOL `LOFA_IMP_BIJ_VV` (local_lemmas.hl:2016) — filled (orbit wave
2026-10-08) from `LOCAL_FAN_ORBIT_MAP_V`: MapsTo is orbit closure, InjOn
reads `rho a = rho b` through the minimal cycle (`la5_orbit_cycle`,
`la5_period_mod`; the wrap case `ib + 1 = p` gives `rho^[1] a = a` and a
period-1 reduction), SurjOn takes the `p - 1`-th iterate via
`LOFA_IMP_ITER`-style periodicity `rho^[p] w = w`. -/
theorem LOFA_IMP_BIJ_VV (h : localFan_p2 V E FF) :
    Set.BijOn (rhoNode1_p2 FF) V V := by
  have horb : ∀ x ∈ V, orbitF_p2 (rhoNode1_p2 FF) x = V :=
    fun x hx => LOCAL_FAN_ORBIT_MAP_V h hx
  have hmaps : ∀ x ∈ V, rhoNode1_p2 FF x ∈ V := by
    intro x hx
    have h1 : rhoNode1_p2 FF x ∈ orbitF_p2 (rhoNode1_p2 FF) x := ⟨1, rfl⟩
    rwa [horb x hx] at h1
  refine ⟨hmaps, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨p, hp0, hpx, hdis, hcover, -⟩ := la5_orbit_cycle horb ha
    rw [← hcover] at hb
    obtain ⟨ib, hiblt, hib⟩ := hb
    by_cases hib0 : ib = 0
    · rw [hib0, Function.iterate_zero_apply] at hib
      exact hib
    · have hp1 : 1 ≤ ib := by omega
      have hap : (rhoNode1_p2 FF)^[ib + 1] a
          = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[ib] a) :=
        Function.iterate_succ_apply' _ _ _
      have hstep : rhoNode1_p2 FF a = (rhoNode1_p2 FF)^[ib + 1] a := by
        rw [hap]
        rw [← hib] at hab
        exact hab
      by_cases hlt : ib + 1 < p
      · exact absurd hstep (hdis 1 (ib + 1) (by omega) hlt)
      · have heqp : ib + 1 = p := by omega
        rw [heqp] at hstep
        rw [hpx] at hstep
        have hq1 : (rhoNode1_p2 FF)^[1] a = a := hstep
        have h9 : (rhoNode1_p2 FF)^[ib] a
            = (rhoNode1_p2 FF)^[ib % 1] a := la5_period_mod _ hq1 ib
        rw [← hib, h9, Nat.mod_one, Function.iterate_zero_apply]
  · intro w hw
    obtain ⟨p, hp0, hpx, -, -, -⟩ := la5_orbit_cycle horb hw
    have hp1 : p - 1 + 1 = p := by omega
    have hrun : (rhoNode1_p2 FF)^[p] w
        = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[p - 1] w) := by
      rw [← hp1]
      exact Function.iterate_succ_apply' _ _ _
    refine ⟨(rhoNode1_p2 FF)^[p - 1] w, LOCAL_FAN_ITER_RHO_NODE_IN_V h hw (p - 1), ?_⟩
    rw [← hrun, hpx]

/-- HOL `MOST_EXPAND_IN_WEDGE_GE` (local_lemmas.hl:2027). -/
theorem MOST_EXPAND_IN_WEDGE_GE {v0 v1 w1 w2 x y : V3}
    (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3))
    (hw2 : ¬ Collinear ℝ ({v0, v1, w2} : Set V3))
    (hx : ¬ Collinear ℝ ({v0, v1, x} : Set V3))
    (hy : ¬ Collinear ℝ ({v0, v1, y} : Set V3))
    (hyw : y ∈ wedgeGe_p2 v0 v1 w1 w2)
    (hxy : azim v0 v1 w1 x ≤ azim v0 v1 w1 y)
    (heq : azim v0 v1 x y = azim v0 v1 w1 w2) :
    azim v0 v1 w1 x = 0 ∧ azim v0 v1 y w2 = 0 := by
  have hv10 : (v1:V3) ≠ v0 := fun h => hw1 (collinear3_of_eq h)
  have e1 := sum4_azim_fan hv10 hw1 hx hy hxy
  have e2 := sum4_azim_fan hv10 hw1 hy hw2 hyw.2
  have hn1 : 0 ≤ azim v0 v1 w1 x := azim_nonneg v0 v1 w1 x
  have hn2 : 0 ≤ azim v0 v1 y w2 := azim_nonneg v0 v1 y w2
  exact ⟨by linarith, by linarith⟩

/-- Copy of LA5-private `la5_conv02_extract` (later in file, not importable
from the probe). -/
private theorem ozq_conv02_extract {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β = 1 ∧ x = α • a + β • b := by
  obtain ⟨f, hfin, hvec, hpos, hsum⟩ := hx
  by_cases hab : a = b
  · subst hab
    have hEq : hfin.toFinset = ({a} : Finset V3) := by ext w; simp
    rw [hEq] at hvec hsum
    simp only [Finset.sum_singleton] at hvec hsum
    have hfa : f a = 1 := hsum
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hvec, hfa]
    module
  · have hEq : hfin.toFinset = ({a, b} : Finset V3) := by ext w; simp [hab]
    rw [hEq] at hvec hsum
    simp only [Finset.sum_insert (by simp [hab] : ¬(a ∈ ({b} : Finset V3))),
      Finset.sum_singleton] at hvec hsum
    exact ⟨f a, f b, hpos a (by simp), hpos b (by simp), by linarith, hvec⟩

/-- Lane support (OZQVSFF wave): a positive combination of `w` and `u`
landing on the axis line `0v` forces the azimuth `w→u` around `0v` to be a
half turn (LDURDPN core, frame computation). -/
private theorem ozq_azim_pi_of_pos_combo {v w u : V3}
    (hw : ¬ Collinear ℝ ({0, v, w} : Set V3)) (hu : ¬ Collinear ℝ ({0, v, u} : Set V3))
    {α β t : ℝ} (hα : 0 < α) (hβ : 0 < β) (hcombo : α • w + β • u = t • v) :
    azim 0 v w u = Real.pi := by
  have hv0 : v ≠ 0 := by
    intro hcon
    exact hw ((collinear_triple_iff (x := 0) (v := v) (u := w)).mpr (Or.inr hcon.symm))
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (v - 0) (by simpa using hv0)
  have hax : (v - 0 : V3) = dist v 0 • e3 := by rw [dist_eq_norm]; exact halign
  have hvaxis : v = dist v 0 • e3 := by rw [← hax, sub_zero]
  obtain ⟨hd11, hd22, hd33, hd12, hd13, hd23, -⟩ := id hon
  have he21 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact hd12
  have hvz1 : v ⬝ᵥ e1 = 0 := by
    rw [hvaxis, WithLp.ofLp_smul 2, smul_dotProduct, dotProduct_comm]
    rw [hd13]; ring
  have hvz2 : v ⬝ᵥ e2 = 0 := by
    rw [hvaxis, WithLp.ofLp_smul 2, smul_dotProduct, dotProduct_comm]
    rw [hd23]; ring
  -- dots distribute over two-term combinations
  have lin1 : ∀ (r s : ℝ) (x y : V3), (r • x + s • y) ⬝ᵥ e1 = r * (x ⬝ᵥ e1) + s * (y ⬝ᵥ e1) := by
    intro r s x y
    rw [WithLp.ofLp_add 2, WithLp.ofLp_smul 2, WithLp.ofLp_smul 2, add_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have lin2 : ∀ (r s : ℝ) (x y : V3), (r • x + s • y) ⬝ᵥ e2 = r * (x ⬝ᵥ e2) + s * (y ⬝ᵥ e2) := by
    intro r s x y
    rw [WithLp.ofLp_add 2, WithLp.ofLp_smul 2, WithLp.ofLp_smul 2, add_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  -- dots of a frame representation
  have lin3 : ∀ (r s t : ℝ) (x y z : V3),
      (r • x + s • y + t • z) ⬝ᵥ e1 = r * (x ⬝ᵥ e1) + s * (y ⬝ᵥ e1) + t * (z ⬝ᵥ e1) := by
    intro r s t x y z
    rw [WithLp.ofLp_add 2, add_dotProduct, lin1 r s x y, WithLp.ofLp_smul 2, smul_dotProduct,
      smul_eq_mul]
  have lin3e2 : ∀ (r s t : ℝ) (x y z : V3),
      (r • x + s • y + t • z) ⬝ᵥ e2 = r * (x ⬝ᵥ e2) + s * (y ⬝ᵥ e2) + t * (z ⬝ᵥ e2) := by
    intro r s t x y z
    rw [WithLp.ofLp_add 2, add_dotProduct, lin2 r s x y, WithLp.ofLp_smul 2, smul_dotProduct,
      smul_eq_mul]
  have dotOf : ∀ (p : V3) (a b c : ℝ), p = a • e1 + b • e2 + c • v →
      p ⬝ᵥ e1 = a ∧ p ⬝ᵥ e2 = b := by
    intro p a b c hp
    constructor
    · rw [hp, lin3 a b c e1 e2 v, hd11, he21, hvz1]; ring
    · rw [hp, lin3e2 a b c e1 e2 v, hd22, hd12, hvz2]; ring
  obtain ⟨-, -, h1f, h2f, hframes⟩ := azim_master 0 v w u
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ :=
    hframes e1 e2 e3 hon hax (by simpa using hv0)
  have hr1' : 0 < r1 := hr1 hw
  have hr2' : 0 < r2 := hr2 hu
  have hw' : w = (r1 * Real.cos ψ) • e1 + (r1 * Real.sin ψ) • e2 + h1f • v := by
    have hw'' := hrep1
    simp only [sub_zero] at hw''
    exact hw''
  have hu' : u = (r2 * Real.cos (ψ + azim 0 v w u)) • e1 +
      (r2 * Real.sin (ψ + azim 0 v w u)) • e2 + h2f • v := by
    have hu'' := hrep2
    simp only [sub_zero] at hu''
    exact hu''
  obtain ⟨hw1, hw2⟩ := dotOf w _ _ _ hw'
  obtain ⟨hu1, hu2⟩ := dotOf u _ _ _ hu'
  set θ := azim 0 v w u with hθdef
  -- the combo dotted with the frame vectors kills the axis term
  have d1 : α * (w ⬝ᵥ e1) + β * (u ⬝ᵥ e1) = 0 := by
    have hd : (α • w + β • u) ⬝ᵥ e1 = (t • v) ⬝ᵥ e1 :=
      congrArg (fun x : V3 => x ⬝ᵥ e1) hcombo
    rw [lin1 α β w u, WithLp.ofLp_smul 2, smul_dotProduct, smul_eq_mul, hvz1, mul_zero] at hd
    linarith
  have d2 : α * (w ⬝ᵥ e2) + β * (u ⬝ᵥ e2) = 0 := by
    have hd : (α • w + β • u) ⬝ᵥ e2 = (t • v) ⬝ᵥ e2 :=
      congrArg (fun x : V3 => x ⬝ᵥ e2) hcombo
    rw [lin2 α β w u, WithLp.ofLp_smul 2, smul_dotProduct, smul_eq_mul, hvz2, mul_zero] at hd
    linarith
  rw [hw1, hu1] at d1
  rw [hw2, hu2] at d2
  -- Pythagoras on d1, d2 gives β * r2 = α * r1
  have hcsq : Real.cos ψ ^ 2 + Real.sin ψ ^ 2 = 1 := Real.cos_sq_add_sin_sq ψ
  have hc2 : Real.cos (ψ + θ) ^ 2 + Real.sin (ψ + θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have e1 : (β * r2) ^ 2
      = (β * r2 * Real.cos (ψ + θ)) ^ 2 + (β * r2 * Real.sin (ψ + θ)) ^ 2 := by
    calc (β * r2) ^ 2
        = (β * r2) ^ 2 * (Real.cos (ψ + θ) ^ 2 + Real.sin (ψ + θ) ^ 2) := by rw [hc2, mul_one]
      _ = (β * r2 * Real.cos (ψ + θ)) ^ 2 + (β * r2 * Real.sin (ψ + θ)) ^ 2 := by ring
  have e2 : (α * r1) ^ 2 = (α * r1 * Real.cos ψ) ^ 2 + (α * r1 * Real.sin ψ) ^ 2 := by
    calc (α * r1) ^ 2 = (α * r1) ^ 2 * (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) := by rw [hcsq, mul_one]
      _ = (α * r1 * Real.cos ψ) ^ 2 + (α * r1 * Real.sin ψ) ^ 2 := by ring
  have e3 : (β * r2 * Real.cos (ψ + θ)) ^ 2 + (β * r2 * Real.sin (ψ + θ)) ^ 2
      = (α * r1 * Real.cos ψ) ^ 2 + (α * r1 * Real.sin ψ) ^ 2 := by
    have h2 : β * r2 * Real.cos (ψ + θ) = -(α * r1 * Real.cos ψ) := by linarith
    have h3 : β * r2 * Real.sin (ψ + θ) = -(α * r1 * Real.sin ψ) := by linarith
    rw [h2, h3]; ring
  have hsqeq : (β * r2) ^ 2 = (α * r1) ^ 2 := by linarith [e1, e2, e3]
  have hβr2eq : β * r2 = α * r1 := by
    have hp : (0:ℝ) < β * r2 := mul_pos hβ hr2'
    have hq : (0:ℝ) < α * r1 := mul_pos hα hr1'
    rcases lt_trichotomy (β * r2) (α * r1) with h | h | h
    · exact absurd hsqeq (by nlinarith)
    · exact h
    · exact absurd hsqeq (by nlinarith)
  -- so cos(ψ+θ) = −cosψ and sin(ψ+θ) = −sinψ; expanding at ψ gives cosθ = −1
  have hαr1 : (α * r1 : ℝ) ≠ 0 := ne_of_gt (mul_pos hα hr1')
  have dd1 : Real.cos ψ + Real.cos (ψ + θ) = 0 := by
    have h2 := d1
    simp only [← mul_assoc] at h2
    rw [hβr2eq] at h2
    have hsum : (α * r1) * (Real.cos ψ + Real.cos (ψ + θ)) = 0 := by
      rw [mul_add]; linarith
    rw [mul_eq_zero] at hsum
    rcases hsum with h0 | h0
    · exact absurd h0 hαr1
    · exact h0
  have dd2 : Real.sin ψ + Real.sin (ψ + θ) = 0 := by
    have h2 := d2
    simp only [← mul_assoc] at h2
    rw [hβr2eq] at h2
    have hsum : (α * r1) * (Real.sin ψ + Real.sin (ψ + θ)) = 0 := by
      rw [mul_add]; linarith
    rw [mul_eq_zero] at hsum
    rcases hsum with h0 | h0
    · exact absurd h0 hαr1
    · exact h0
  have ex1 : Real.cos ψ * (Real.cos θ + 1) - Real.sin ψ * Real.sin θ = 0 := by
    rw [Real.cos_add] at dd1
    linarith
  have ex2 : Real.sin ψ * (Real.cos θ + 1) + Real.cos ψ * Real.sin θ = 0 := by
    rw [Real.sin_add] at dd2
    linarith
  have hcosm1 : Real.cos θ = -1 := by
    have h1 : (Real.cos ψ * (Real.cos θ + 1) - Real.sin ψ * Real.sin θ) * Real.cos ψ
        + (Real.sin ψ * (Real.cos θ + 1) + Real.cos ψ * Real.sin θ) * Real.sin ψ
        = (Real.cos θ + 1) * (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) := by ring
    rw [ex1, ex2, Real.cos_sq_add_sin_sq ψ] at h1
    linarith
  -- sin θ = 0, then θ ∈ [0, 2π) with cos θ = −1 forces θ = π
  have hsin0 : Real.sin θ = 0 := by
    have hsq : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    rw [hcosm1] at hsq
    norm_num at hsq
    exact hsq
  rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨k, hk⟩
  have hr0 : 0 ≤ (k:ℝ) * Real.pi := by rw [hk]; exact azim_nonneg 0 v w u
  have hr1lt : (k:ℝ) * Real.pi < 2 * Real.pi := by rw [hk]; exact azim_lt_two_pi 0 v w u
  have hk01 : k = 0 ∨ k = 1 := by
    have hpos : (0:ℝ) < Real.pi := Real.pi_pos
    have hk0 : 0 ≤ k := by
      by_contra hneg
      have hz : (k:ℤ) ≤ -1 := by omega
      have hle : ((k:ℤ) : ℝ) ≤ ((-1:ℤ) : ℝ) := by exact_mod_cast hz
      have hle' : (k:ℝ) ≤ -1 := by simpa using hle
      nlinarith [hr0, hle', hpos]
    have hk2 : k ≤ 1 := by
      by_contra hge
      have hz : (2:ℤ) ≤ k := by omega
      have hge2 : ((2:ℤ) : ℝ) ≤ ((k:ℤ) : ℝ) := by exact_mod_cast hz
      have hge' : (2:ℝ) ≤ k := by simpa using hge2
      nlinarith [hr1lt, hge', hpos]
    omega
  rcases hk01 with rfl | rfl
  · have hθ0 : θ = 0 := by rw [← hk]; ring
    rw [hθ0, Real.cos_zero] at hcosm1
    linarith
  · rw [← hk]; ring

/-- Lane support (OZQVSFF wave): an azimuth of `0` or `π` around the axis
`0v` pins the second point into the linear span of the axis and the first
point. -/
private theorem ozq_affCombo_of_azim_0_or_pi {v a b : V3}
    (ha : ¬ Collinear ℝ ({0, v, a} : Set V3)) (hb : ¬ Collinear ℝ ({0, v, b} : Set V3))
    (hz : azim 0 v a b = 0 ∨ azim 0 v a b = Real.pi) :
    ∃ c d : ℝ, b = c • a + d • v := by
  have hv0 : v ≠ 0 := by
    intro hcon
    exact ha ((collinear_triple_iff (x := 0) (v := v) (u := a)).mpr (Or.inr hcon.symm))
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (v - 0) (by simpa using hv0)
  have hax : (v - 0 : V3) = dist v 0 • e3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨-, -, h1f, h2f, hframes⟩ := azim_master 0 v a b
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ :=
    hframes e1 e2 e3 hon hax (by simpa using hv0)
  have hr1' : 0 < r1 := hr1 ha
  have hr2' : 0 < r2 := hr2 hb
  have ha' : a = (r1 * Real.cos ψ) • e1 + (r1 * Real.sin ψ) • e2 + h1f • v := by
    have ha'' := hrep1
    simp only [sub_zero] at ha''
    exact ha''
  rcases hz with hz0 | hzπ
  · refine ⟨r2 / r1, h2f - r2 / r1 * h1f, ?_⟩
    have hr1ne : r1 ≠ 0 := ne_of_gt hr1'
    have k1 : r1 * (r2 / r1) = r2 := by
      rw [mul_comm, div_mul_eq_mul_div]
      exact mul_div_cancel_right₀ r2 hr1ne
    have k2 : r1 * (r2 / r1 * h1f) = r2 * h1f := by rw [← mul_assoc, k1]
    have k3 : r1 * (h2f - r2 / r1 * h1f) = r1 * h2f - r2 * h1f := by rw [mul_sub, k2]
    have hmul : r1 • ((r2 / r1) • a + (h2f - r2 / r1 * h1f) • v) = r1 • b := by
      have hb'' := hrep2
      rw [hz0, add_zero] at hb''
      simp only [sub_zero] at hb''
      rw [ha', hb'', smul_add, smul_smul, k1, smul_smul, k3]
      module
    exact (smul_right_injective (M := V3) hr1ne) hmul.symm
  · refine ⟨-(r2 / r1), h2f + r2 / r1 * h1f, ?_⟩
    have hr1ne : r1 ≠ 0 := ne_of_gt hr1'
    have k1 : r1 * (r2 / r1) = r2 := by
      rw [mul_comm, div_mul_eq_mul_div]
      exact mul_div_cancel_right₀ r2 hr1ne
    have k2 : r1 * (r2 / r1 * h1f) = r2 * h1f := by rw [← mul_assoc, k1]
    have k3 : r1 * (h2f + r2 / r1 * h1f) = r1 * h2f + r2 * h1f := by rw [mul_add, k2]
    have hmul : r1 • (-(r2 / r1) • a + (h2f + r2 / r1 * h1f) • v) = r1 • b := by
      have hb'' := hrep2
      rw [hzπ, Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi] at hb''
      simp only [sub_zero] at hb''
      have k1n : r1 * -(r2 / r1) = -r2 := by rw [mul_neg, k1]
      rw [ha', hb'', smul_add, smul_smul, k1n, smul_smul, k3]
      module
    exact (smul_right_injective (M := V3) hr1ne) hmul.symm

theorem OZQVSFF (h : convexLocalFan_p2 V E FF) {u v w : V3} {P : Set V3}
    (hsub : ({u, v, w} : Set V3) ⊆ V) (hP : plane_p2 P)
    (hsub2 : ({0, u, v, w} : Set V3) ⊆ P)
    (hdis : ({u, w} : Set V3) ∩ affineSpan ℝ ({0, v} : Set V3) = ∅)
    (hne : ¬ (((affineSpan ℝ ({v, 0} : Set V3) : Set V3) ∩
      conv0_p2 ({w, u} : Set V3)) = ∅)) :
    interiorAngle1_p2 0 FF v = Real.pi ∧
      rhoNode1_p2 FF v ∈ P ∧ ivsRhoNode1_p2 FF v ∈ P := by
  obtain ⟨hlo, hcvx⟩ := h
  have hlo' : localFan_p2 V E FF := hlo
  obtain ⟨H, hdart, -, hnn, hff, hfan, ⟨z, hzd, hFF⟩, hdih⟩ := hlo
  have hvV : v ∈ V := hsub (by simp)
  have huV : u ∈ V := hsub (by simp)
  have hwV : w ∈ V := hsub (by simp)
  have hv0 : v ≠ 0 := by
    intro hcon
    exact hfan.2.2.2.1 (hcon ▸ hvV)
  -- the rho-dart `(v, ρ)`
  have hbij : Set.BijOn Prod.fst FF V := WRGCVDR_BIJ hlo'
  have hd0 : (v, rhoNode1_p2 FF v) ∈ FF := by
    obtain ⟨d, hdF, hdfst⟩ := hbij.2.2 hvV
    have hmem : (v, d.2) ∈ FF := by rw [← hdfst]; exact hdF
    simp only [rhoNode1_p2]
    exact Classical.epsilon_spec (p := fun w : V3 => (v, w) ∈ FF) ⟨d.2, hmem⟩
  set ρ : V3 := rhoNode1_p2 FF v with hrho
  have hfaceSub : H.face z ⊆ (↑H.darts : Set (V3 × V3)) := H.face_subset_darts hzd
  have hV : ∀ d ∈ FF, d ∈ (dartsOfHyp_p2 E V : Set (V3 × V3)) := by
    intro d hdF
    have hsub' : d ∈ (↑H.darts : Set (V3 × V3)) := hfaceSub (by rw [← hFF]; exact hdF)
    rw [hdart] at hsub'
    exact hsub'
  -- convexity facts for the dart `(v, ρ)`
  obtain ⟨hinfan, hwedge⟩ := hcvx (v, ρ) hd0
  set dstar : V3 := azimCycle_p2 (EE_p2 v E) 0 v ρ with hdstar
  have hAI : azimInFan_p2 (v, ρ) E
      = if 1 < (EE_p2 v E).ncard then azim 0 v ρ dstar else 2 * Real.pi := rfl
  have hWF : wedgeInFanGe_p2 (v, ρ) E
      = if 1 < (EE_p2 v E).ncard then wedgeGe_p2 0 v ρ dstar else Set.univ := rfl
  by_cases hcond : 1 < (EE_p2 v E).ncard
  · rw [hAI, if_pos hcond] at hinfan
    rw [hWF, if_pos hcond] at hwedge
    have hord : (v, ρ) ∈ ordPairs_p2 E := by
      rcases hV (v, ρ) hd0 with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨-, -, hEE⟩ := h2
        have hEE' : EE_p2 v E = ∅ := hEE
        rw [hEE'] at hcond
        simp at hcond
    have hρEE : ρ ∈ EE_p2 v E := hord
    have hcolρ : ¬ Collinear ℝ ({0, v, ρ} : Set V3) :=
      hfan.2.2.2.2.1 ({v, ρ} : Set V3) hord
    have hθu : azim 0 v ρ u ≤ azim 0 v ρ dstar := (hwedge huV).2
    have hθw : azim 0 v ρ w ≤ azim 0 v ρ dstar := (hwedge hwV).2
    have hcolU : ¬ Collinear ℝ ({0, v, u} : Set V3) := by
      intro hcol
      rcases (collinear_triple_iff (x := 0) (v := v) (u := u)).mp hcol with hmem | hzero
      · exact absurd
          (Set.mem_inter (by simp : u ∈ ({u, w} : Set V3)) hmem)
          (by rw [hdis]; simp)
      · exact hfan.2.2.2.1 (hzero ▸ hvV)
    have hcolW : ¬ Collinear ℝ ({0, v, w} : Set V3) := by
      intro hcol
      rcases (collinear_triple_iff (x := 0) (v := v) (u := w)).mp hcol with hmem | hzero
      · exact absurd
          (Set.mem_inter (by simp : w ∈ ({u, w} : Set V3)) hmem)
          (by rw [hdis]; simp)
      · exact hfan.2.2.2.1 (hzero ▸ hvV)
    -- the intersection point forces `azim 0 v w u = π`
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨α, β, hα, hβ, hsumαβ, hxcombo⟩ := ozq_conv02_extract hx.2
    have hxline : ∃ s : ℝ, x = s • v := by
      have hcol : Collinear ℝ ({v, 0, x} : Set V3) :=
        (collinear_triple_iff (x := v) (v := 0) (u := x)).mpr (Or.inl hx.1)
      obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := v) (w := 0) (w1 := x)
        (Ne.symm hv0)).mp hcol
      refine ⟨1 - c, ?_⟩
      have hx'' : x = c • (0 - v) + v := sub_eq_iff_eq_add.mp hc
      rw [hx'']
      module
    obtain ⟨s, hxs⟩ := hxline
    have hapi : azim 0 v w u = Real.pi :=
      ozq_azim_pi_of_pos_combo hcolW hcolU hα hβ (by rw [← hxs]; exact hxcombo.symm)
    -- the sector through `ρ` and `dstar` has full half-turn width
    obtain ⟨hθdπ, hsector⟩ :
        azim 0 v ρ dstar = Real.pi ∧
          (azim 0 v ρ u = Real.pi ∧ azim 0 v ρ w = 0 ∨
            azim 0 v ρ u = 0 ∧ azim 0 v ρ w = Real.pi) := by
      rcases le_total (azim 0 v ρ w) (azim 0 v ρ u) with hcase | hcase
      · have hsum := sum4_azim_fan (x := 0) (v := v) (u := ρ) (w1 := w) (w2 := u) hv0
          hcolρ hcolW hcolU hcase
        rw [hsum, hapi] at hθu
        have h1 : (0:ℝ) ≤ azim 0 v ρ w := azim_nonneg 0 v ρ w
        refine ⟨?_, Or.inl ⟨by linarith, by linarith⟩⟩
        linarith
      · have hcompl : azim 0 v u w = Real.pi := by
          have h2 := azim_compl hcolW hcolU
          rw [hapi, if_neg (by norm_num : ¬((Real.pi:ℝ) = 0))] at h2
          linarith
        have hsum := sum4_azim_fan (x := 0) (v := v) (u := ρ) (w1 := u) (w2 := w) hv0
          hcolρ hcolU hcolW hcase
        rw [hsum, hcompl] at hθw
        have h1 : (0:ℝ) ≤ azim 0 v ρ u := azim_nonneg 0 v ρ u
        refine ⟨?_, Or.inr ⟨by linarith, by linarith⟩⟩
        linarith
    have hρdstar : ρ ≠ dstar := by
      intro hcon
      rw [← hcon, azim_self] at hθdπ
      exact absurd hθdπ (by linarith [Real.pi_pos])
    have hneEE : ¬(EE_p2 v E = ∅) := by
      intro h
      rw [h] at hcond
      simp at hcond
    have hdstarEE : dstar ∈ EE_p2 v E := by
      have hd0dart : (v, ρ) ∈ (↑H.darts : Set (V3 × V3)) := by
        rw [hdart]; exact hV (v, ρ) hd0
      have h1 : (H.nodeMap : V3 × V3 → V3 × V3) (v, ρ) ∈ (dartsOfHyp_p2 E V : Set (V3 × V3)) := by
        rw [← hdart]
        exact H.nodeMap_apply_mem (Finset.mem_coe.mpr hd0dart)
      have h2 : (H.nodeMap : V3 × V3 → V3 × V3) (v, ρ) = (v, dstar) := by
        rw [hnn]
        simp only [nnOfHyp_p2, if_pos (hV (v, ρ) hd0)]
        rfl
      rw [h2] at h1
      rcases h1 with h3 | h3
      · exact h3
      · exfalso
        obtain ⟨-, -, hEE⟩ := h3
        have hEE' : EE_p2 v E = ∅ := hEE
        rw [hEE'] at hcond
        simp at hcond
    -- every E-neighbour of `v` is `ρ` or `dstar`
    have hdartsUnion : (dartsOfHyp_p2 E V : Set (V3 × V3))
        = FF ∪ (H.nodeMap : V3 × V3 → V3 × V3) '' FF := by
      have hzz := hdih.2.1 z hzd
      rw [← hFF] at hzz
      rw [← hdart]
      exact hzz
    have hEEsub : ∀ z' ∈ EE_p2 v E, z' = ρ ∨ z' = dstar := by
      intro z' hz'E
      have hz'E' : ((v, z') : V3 × V3) ∈ ordPairs_p2 E := hz'E
      have hdartmem : ((v, z') : V3 × V3) ∈ (dartsOfHyp_p2 E V : Set (V3 × V3)) :=
        Set.mem_union_left _ hz'E'
      rw [hdartsUnion] at hdartmem
      rcases hdartmem with h1 | ⟨d', hd'F, hd'eq⟩
      · have hpair : ((v, z') : V3 × V3) = (v, ρ) := hbij.2.1 h1 hd0 (by simp)
        exact Or.inl (congrArg Prod.snd hpair)
      · have hd'darts : d' ∈ (dartsOfHyp_p2 E V : Set (V3 × V3)) := hV d' hd'F
        have hd'eq' : ((v, z') : V3 × V3)
            = (d'.1, azimCycle_p2 (EE_p2 d'.1 E) 0 d'.1 d'.2) := by
          rw [← hd'eq, hnn]
          simp only [nnOfHyp_p2, if_pos hd'darts]
        have hd'1 : v = d'.1 := congrArg Prod.fst hd'eq'
        have hd'2 : z' = azimCycle_p2 (EE_p2 d'.1 E) 0 d'.1 d'.2 := congrArg Prod.snd hd'eq'
        have hd'is : d' = (v, ρ) := hbij.2.1 hd'F hd0 (by exact hd'1.symm)
        refine Or.inr ?_
        rw [hd'2, ← hd'1, hd'is]
    have hEEset : EE_p2 v E = {ρ, dstar} := by
      ext q
      constructor
      · intro hq
        rcases hEEsub q hq with hq' | hq'
        · simp [hq']
        · simp [hq']
      · rintro (rfl | rfl)
        · exact hρEE
        · exact hdstarEE
    -- exactly one dart of `FF` has second component `v`, namely `(dstar, v)`
    have hfinFF : FF.Finite :=
      (H.darts.finite_toSet).subset fun d hdF => by rw [hdart]; exact hV d hdF
    have hkpos : 0 < FF.ncard := Set.ncard_pos (hs := hfinFF).mpr ⟨(v, ρ), hd0⟩
    have hIter : ∀ x : V3 × V3, (H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard] x = x := by
      intro x
      rw [hdih.2.2.1.2]; rfl
    have hpreFace : (H.faceMap : V3 × V3 → V3 × V3)
        ((H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard - 1] (v, ρ)) = (v, ρ) := by
      have hsplit : (H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard] (v, ρ)
          = (H.faceMap : V3 × V3 → V3 × V3)
            ((H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard - 1] (v, ρ)) := by
        conv in (H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard] =>
          rw [show FF.ncard = FF.ncard - 1 + 1 from by omega]
        exact Function.iterate_succ_apply' _ _ _
      rw [← hsplit]; exact hIter (v, ρ)
    have hpreMemFace : (H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard - 1] (v, ρ) ∈ H.face z := by
      have hmem0 : (v, ρ) ∈ H.face z := by rw [← hFF]; exact hd0
      obtain ⟨n0, hn0⟩ := hmem0
      have hstep : (H.faceMap ^ (FF.ncard - 1)) (v, ρ)
          = (H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard - 1] (v, ρ) :=
        congrFun (Equiv.Perm.coe_pow H.faceMap (FF.ncard - 1)) (v, ρ)
      refine ⟨FF.ncard - 1 + n0, ?_⟩
      rw [← hstep, pow_add, Equiv.Perm.mul_apply, hn0]
    have hpreMem : (H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard - 1] (v, ρ) ∈ FF :=
      hFF.symm ▸ hpreMemFace
    obtain ⟨pre, hpreMem, hpreFace⟩ :
        ∃ p, p ∈ FF ∧ (H.faceMap : V3 × V3 → V3 × V3) p = (v, ρ) :=
      ⟨(H.faceMap : V3 × V3 → V3 × V3)^[FF.ncard - 1] (v, ρ), hpreMem, hpreFace⟩
    have hpre2v : pre.2 = v := by
      have h1 := hpreFace
      rw [hff] at h1
      simp only [ffOfHyp_p2, if_pos (hV pre hpreMem)] at h1
      exact congrArg Prod.fst h1
    have hpre1EE : pre.1 ∈ EE_p2 v E := by
      show ({v, pre.1} : Set V3) ∈ E
      rw [Set.pair_comm]
      have hpd := hV pre hpreMem
      rcases hpd with h3 | h3
      · simp only [ordPairs_p2, Set.mem_setOf_eq] at h3
        rw [hpre2v] at h3
        exact h3
      · exfalso
        obtain ⟨hp12, -, hEE⟩ := h3
        rw [hpre2v] at hp12
        have hEE' : EE_p2 v E = ∅ := by rw [← hp12]; exact hEE
        rw [hEE'] at hcond
        simp at hcond
    have hFstSnd : ∀ a : V3, (a, v) ∈ FF → a = dstar := by
      intro a ha
      have hfv : (H.faceMap : V3 × V3 → V3 × V3) (a, v) ∈ FF := by
        have hmem0 : (a, v) ∈ H.face z := by rw [← hFF]; exact ha
        obtain ⟨m, hm⟩ := hmem0
        have hm' : (H.faceMap : V3 × V3 → V3 × V3)^[m] z = (a, v) := by
          rw [← Equiv.Perm.coe_pow]
          exact hm
        have h2' : (H.faceMap : V3 × V3 → V3 × V3)^[m + 1] z
            = (H.faceMap : V3 × V3 → V3 × V3) (a, v) := by
          rw [Function.iterate_succ_apply', hm']
        exact hFF ▸ ⟨m + 1, h2'⟩
      have hdartsav := hV (a, v) ha
      have h2 : (H.faceMap : V3 × V3 → V3 × V3) (a, v)
          = (v, ivsAzimCycle_p2 (EE_p2 v E) 0 v a) := by
        rw [hff]
        simp only [ffOfHyp_p2, if_pos hdartsav]
      have hfvEq : (H.faceMap : V3 × V3 → V3 × V3) (a, v) = (v, ρ) :=
        hbij.2.1 hfv hd0 (by rw [h2])
      rw [h2, ivsAzimCycle_p2, if_neg hneEE] at hfvEq
      -- hfvEq : (v, ε (fun x => x ∈ EE ∧ azimCycle (EE) 0 v x = a)) = (v, ρ)
      have haEE : a ∈ EE_p2 v E := by
        show ({v, a} : Set V3) ∈ E
        rw [Set.pair_comm]
        have hpd := hV (a, v) ha
        rcases hpd with h3 | h3
        · exact h3
        · exfalso
          obtain ⟨hp12, -, hEE⟩ := h3
          have hav : a = v := hp12
          have hEE' : EE_p2 v E = ∅ := by rw [← hav]; exact hEE
          rw [hEE'] at hcond
          simp at hcond
      rcases hEEsub a haEE with hcase | hcase
      · -- a = ρ: then the ε must pick `dstar`, forcing dstar = ρ
        rw [hcase] at hfvEq
        have hnonempty : ∃ x, x ∈ EE_p2 v E ∧ azimCycle_p2 (EE_p2 v E) 0 v x = ρ := by
          refine ⟨dstar, hdstarEE, ?_⟩
          rw [hEEset, Set.pair_comm]
          exact AZIM_CYCLE_TWO_POINT_SET dstar ρ 0 v
        have hspec := Classical.epsilon_spec
          (p := fun x : V3 => x ∈ EE_p2 v E ∧ azimCycle_p2 (EE_p2 v E) 0 v x = ρ) hnonempty
        have heps : (Classical.epsilon fun x : V3 => x ∈ EE_p2 v E ∧
            azimCycle_p2 (EE_p2 v E) 0 v x = ρ) = ρ := congrArg Prod.snd hfvEq
        rw [heps] at hspec
        exact absurd hspec.2.symm hρdstar
      · exact hcase
    have hprePair : (pre.1, v) = pre := by rw [← hpre2v]
    have hvivs : ivsRhoNode1_p2 FF v = dstar := by
      have hspec := Classical.epsilon_spec (p := fun a : V3 => (a, v) ∈ FF)
        ⟨pre.1, by rw [hprePair]; exact hpreMem⟩
      simp only [ivsRhoNode1_p2]
      exact hFstSnd _ hspec
    -- plane memberships
    obtain ⟨p1, p2, p3, -, hPeq⟩ := hP
    have h0Q : (0:V3) ∈ (affineSpan ℝ ({p1, p2, p3} : Set V3) : Set V3) := by
      rw [← hPeq]; exact hsub2 (by simp)
    have hvQ : v ∈ (affineSpan ℝ ({p1, p2, p3} : Set V3) : Set V3) := by
      rw [← hPeq]; exact hsub2 (by simp)
    have huQ : u ∈ (affineSpan ℝ ({p1, p2, p3} : Set V3) : Set V3) := by
      rw [← hPeq]; exact hsub2 (by simp)
    -- ρ = c • u + d • v (same half-plane line as the axis)
    have huρ : azim 0 v u ρ = 0 ∨ azim 0 v u ρ = Real.pi := by
      have h2 := azim_compl hcolρ hcolU
      rcases hsector with h1 | h1
      · rw [h1.1, if_neg (by norm_num : ¬((Real.pi:ℝ) = 0)),
          show (2:ℝ) * Real.pi - Real.pi = Real.pi from by ring] at h2
        exact Or.inr h2
      · rw [h1.1, if_pos rfl] at h2
        exact Or.inl h2
    obtain ⟨c, d, hρcombo⟩ := ozq_affCombo_of_azim_0_or_pi hcolU hcolρ huρ
    have hpt : (d • (v -ᵥ (0:V3)) +ᵥ (c • (u -ᵥ (0:V3)) +ᵥ (0:V3)) : V3) = ρ := by
      rw [hρcombo]
      simp only [vadd_eq_add, vsub_eq_sub, sub_zero]
      module
    have hρQ : ρ ∈ (affineSpan ℝ ({p1, p2, p3} : Set V3) : Set V3) := by
      have hmem := AffineSubspace.smul_vsub_vadd_mem
        (affineSpan ℝ ({p1, p2, p3} : Set V3)) d hvQ h0Q
        (AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ ({p1, p2, p3} : Set V3)) c huQ h0Q h0Q)
      rw [hpt] at hmem
      exact hmem
    refine ⟨?_, ?_, ?_⟩
    · show azim 0 v ρ (ivsRhoNode1_p2 FF v) = Real.pi
      rw [hvivs]; exact hθdπ
    · rw [hPeq]
      exact SetLike.mem_coe.mpr hρQ
    · -- ivs = dstar lies in the span of `ρ` and `v`
      have hcolD : ¬ Collinear ℝ ({0, v, dstar} : Set V3) := by
        intro hcol
        have hz : azim 0 v ρ dstar = 0 := by
          simp only [azim]
          split
          · rfl
          · rename_i hnc
            exact (hnc (Or.inr hcol)).elim
        rw [hz] at hθdπ
        exact absurd hθdπ (by linarith [Real.pi_pos])
      obtain ⟨c2, d2, hdcombo⟩ := ozq_affCombo_of_azim_0_or_pi hcolρ hcolD (Or.inr hθdπ)
      have hpt2 : (d2 • (v -ᵥ (0:V3)) +ᵥ (c2 • (ρ -ᵥ (0:V3)) +ᵥ (0:V3)) : V3) = dstar := by
        rw [hdcombo]
        simp only [vadd_eq_add, vsub_eq_sub, sub_zero]
        module
      have hmem2 := AffineSubspace.smul_vsub_vadd_mem
        (affineSpan ℝ ({p1, p2, p3} : Set V3)) d2 hvQ h0Q
        (AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ ({p1, p2, p3} : Set V3)) c2 hρQ h0Q h0Q)
      rw [hpt2] at hmem2
      rw [hPeq, hvivs]
      exact SetLike.mem_coe.mpr hmem2
  · -- degenerate branch: azimInFan = 2π > π contradicts convexity
    rw [hAI, if_neg hcond] at hinfan
    nlinarith [Real.pi_pos]


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
    (affineSpan ℝ ({a, b} : Set V3) : Set V3) = (affineSpan ℝ ({x, y} : Set V3) : Set V3) := by
  have hx : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := hsub (Set.mem_insert x _)
  have hy : y ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3) :=
    hsub (Set.mem_insert_of_mem x (Set.mem_singleton y))
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
  have hrs : r ≠ s := by
    intro hcon
    rw [hcon] at hr
    exact hxy (hr.symm.trans hs)
  have hrs' : (r:ℝ) - s ≠ 0 := sub_ne_zero.mpr hrs
  have hrs2 : (s:ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  have hxn : x = (1 - r) • a + r • b := by rw [← hr, AffineMap.lineMap_apply_module]
  have hyn : y = (1 - s) • a + s • b := by rw [← hs, AffineMap.lineMap_apply_module]
  refine Set.eq_of_subset_of_subset ?_ ?_
  · have hax : a ∈ (affineSpan ℝ ({x, y} : Set V3) : Set V3) := by
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨r / (r - s), ?_⟩
      have hct : r + r / (r - s) * (s - r) = 0 := by
        rw [show (s:ℝ) - r = -(r - s) from by ring, mul_neg, div_mul_eq_mul_div,
          show (r:ℝ) + -(r * (r - s) / (r - s)) = r - r * (r - s) / (r - s) from by ring,
          show (r:ℝ) * (r - s) / (r - s) = r from by field_simp]
        ring
      rw [la5_lineMap_reparam (Ne.symm hrs) hxn hyn (r / (r - s)) 0 hct,
        AffineMap.lineMap_apply_module]
      simp
    have hbx : b ∈ (affineSpan ℝ ({x, y} : Set V3) : Set V3) := by
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨(1 - r) / (s - r), ?_⟩
      have hct : r + (1 - r) / (s - r) * (s - r) = 1 := by
        rw [div_mul_eq_mul_div]
        field_simp
        ring
      rw [la5_lineMap_reparam (Ne.symm hrs) hxn hyn ((1 - r) / (s - r)) 1 hct,
        AffineMap.lineMap_apply_module]
      simp
    exact affineSpan_le.mpr (by
      intro z hz
      have hz' : z = a ∨ z = b := Set.mem_insert_iff.mp hz
      rcases hz' with hz' | hz'
      · rw [hz']; exact hax
      · rw [hz']; exact hbx)
  · exact affineSpan_le.mpr (by
      intro z hz
      have hz' : z = x ∨ z = y := Set.mem_insert_iff.mp hz
      rcases hz' with hz' | hz'
      · rw [hz']; exact hx
      · rw [hz']; exact hy)


/-- Lane support (LA5 r2): extract positive affine coefficients from a
two-point `conv0_p2` membership. -/
private theorem la5_conv02_extract {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β = 1 ∧ x = α • a + β • b := by
  obtain ⟨f, hfin, hvec, hpos, hsum⟩ := hx
  by_cases hab : a = b
  · subst hab
    have hEq : hfin.toFinset = ({a} : Finset V3) := by ext w; simp
    rw [hEq] at hvec hsum
    simp only [Finset.sum_singleton] at hvec hsum
    have hfa : f a = 1 := hsum
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hvec, hfa]
    module
  · have hEq : hfin.toFinset = ({a, b} : Finset V3) := by ext w; simp [hab]
    rw [hEq] at hvec hsum
    simp only [Finset.sum_insert (by simp [hab] : ¬(a ∈ ({b} : Finset V3))),
      Finset.sum_singleton] at hvec hsum
    exact ⟨f a, f b, hpos a (by simp [hab]), hpos b (by simp [hab]), by linarith, hvec⟩

/-- Lane support (LA5 r2): an affine combination of two points lies in their
affine span. -/
private theorem la5_affComb_mem_affSpan {a b x : V3} {α β : ℝ} (hsum : α + β = 1)
    (hx : x = α • a + β • b) : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := by
  rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨β, ?_⟩
  rw [AffineMap.lineMap_apply_module, hx, show (1:ℝ) - β = α from by linarith]

/-- Lane support (LA5 r2): from `t = α•x + β•y` (`α+β=1`, `β≠0`) the partner
point `y` sits on the ray from `x` through `t` at parameter `1/β`. -/
private theorem la5_conv02_partner {x y t : V3} {α β : ℝ} (hsum : α + β = 1)
    (hβ : β ≠ 0) (htxy : t = α • x + β • y) :
    y = AffineMap.lineMap x t (1 / β) := by
  rw [AffineMap.lineMap_apply_module, htxy, smul_add, smul_smul, smul_smul,
    show (1:ℝ) / β * β = 1 from by field_simp, one_smul,
    show (1:ℝ) / β * α = α / β from by ring]
  rw [← add_assoc, ← add_smul, show (1:ℝ) - 1 / β + α / β = 0 by field_simp; linarith,
    zero_smul, zero_add]

/-- HOL `IN_CONV0_EQ_EQ` (local_lemmas.hl:2560). -/
theorem IN_CONV0_EQ_EQ {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    x = a ↔ a = b := by
  obtain ⟨α, β, hα, hβ, hsum, hxa⟩ := la5_conv02_extract hx
  constructor
  · intro hxa2
    rw [hxa2] at hxa
    -- hxa : a = α • a + β • b
    have h3 : a - α • a = β • b := by
      nth_rewrite 1 [hxa]
      rw [add_sub_cancel_left]
    have s1 : (1:ℝ) - α = β := by linarith
    have e4 : β • a = a - α • a := by
      rw [show β = (1:ℝ) - α from s1.symm, sub_smul, one_smul]
    have h3' : β • a = β • b := e4.trans h3
    have h5 : β • (a - b) = (0:V3) := by rw [smul_sub, h3', sub_self]
    rcases smul_eq_zero.mp h5 with h | h
    · linarith
    · exact sub_eq_zero.mp h
  · intro hab
    subst hab
    rw [hxa, ← add_smul, hsum, one_smul]

/-- HOL `IN_CONV0_IMP_AFF_EQ` (local_lemmas.hl:2580). -/
theorem IN_CONV0_IMP_AFF_EQ {x y a : V3} (ha : a ∈ conv0_p2 ({x, y} : Set V3)) :
    (affineSpan ℝ ({x, y} : Set V3) : Set V3) = (affineSpan ℝ ({x, a} : Set V3) : Set V3) := by
  obtain ⟨α, β, hα, hβ, hsum, hab⟩ := la5_conv02_extract ha
  have hβ0 : β ≠ 0 := hβ.ne'
  refine le_antisymm ?_ ?_
  · refine S_SUBSET_IMP_AFF_S_TOO ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact left_mem_affineSpan_pair _ _ _
    · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
      exact ⟨1 / β, (la5_conv02_partner hsum hβ0 hab).symm⟩
  · refine S_SUBSET_IMP_AFF_S_TOO ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact left_mem_affineSpan_pair _ _ _
    · exact la5_affComb_mem_affSpan hsum hab

/-- HOL `IN_CONV0_AFF_SUBSET` (local_lemmas.hl:2600). -/
theorem IN_CONV0_AFF_SUBSET {a b x y t : V3} (ht : t ∈ ((affineSpan ℝ ({a, b} : Set V3) :
    Set V3) ∩ conv0_p2 ({x, y} : Set V3))) (hx : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3)) :
    (affineSpan ℝ ({x, y} : Set V3) : Set V3) ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3) := by
  obtain ⟨α, β, hα, hβ, hsum, htxy⟩ := la5_conv02_extract ht.2
  have hβ0 : β ≠ 0 := hβ.ne'
  refine S_SUBSET_IMP_AFF_S_TOO ?_
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | rfl
  · exact hx
  · rw [SetLike.mem_coe, la5_conv02_partner hsum hβ0 htxy]
    have ht1 : t ∈ (affineSpan ℝ ({a, b} : Set V3)) := ht.1
    have hx1 : x ∈ (affineSpan ℝ ({a, b} : Set V3)) := hx
    exact AffineMap.lineMap_mem (1 / β) hx1 ht1

/-- HOL `CONDS_FOR_INTER_AFF_CONV0` (local_lemmas.hl:2611). -/
theorem CONDS_FOR_INTER_AFF_CONV0 {x v w u t : V3} {t1 t2 t3 t1' t2' ss : ℝ}
    (ht2 : 0 < t2) (ht3 : 0 < t3) (h1 : t1 + t2 + t3 = ss)
    (h2 : t = t1 • x + t2 • v + t3 • w) (h3 : t1' + t2' = ss)
    (h4 : t = t1' • x + t2' • u) :
    ∃ tt : V3, tt ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) ∩ conv0_p2 ({v, w} : Set V3) := by
  have hcore : t2' • (u - x) = t2 • (v - x) + t3 • (w - x) := by
    have e1 : t2' • (u - x) = t - ss • x := by
      rw [smul_sub, h4, ← h3]
      module
    rw [e1, h2, ← h1]
    module
  by_cases ht2' : t2' = 0
  · refine ⟨x, left_mem_affineSpan_pair _ _ _, ?_⟩
    rw [ht2', zero_smul] at hcore
    refine la5_seg_member ht2 ht3 ?_
    linear_combination (norm := module) hcore
  · refine ⟨AffineMap.lineMap x u (t2' / (t2 + t3)), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
      exact ⟨_, rfl⟩
    · exact la5_seg_member ht2 ht3 (la5_lineMap_seg_eq hcore (by linarith))


/-- HOL `INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0` (local_lemmas.hl:2644). -/
theorem INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0 {x v w u t : V3}
    (hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3)) (hxu : u ≠ x)
    (ht : t ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩ affLt ({x} : Set V3) ({u} : Set V3)) :
    ∃ tt : V3, tt ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) ∩ conv0_p2 ({v, w} : Set V3) := by
  obtain ⟨b, c, hb, hc, hgt⟩ := la5_affGt_extract ht.1
  obtain ⟨b', hb', hlt⟩ := la5_affLt_extract ht.2
  have hcore : b' • (u - x) = b • (v - x) + c • (w - x) := by rw [← hgt, hlt]
  refine ⟨AffineMap.lineMap x u (b' / (b + c)), ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
    exact ⟨_, rfl⟩
  · exact la5_seg_member hb hc (la5_lineMap_seg_eq hcore (by linarith))


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

/-- Lane support (LA5 r2): ray extraction from `affGe {x} {v}` membership
(valid also in the degenerate `x = v` case). -/
private theorem la5_affGe2_extract {x v y : V3}
    (hy : y ∈ affGe ({x} : Set V3) ({v} : Set V3)) :
    ∃ t : ℝ, 0 ≤ t ∧ y - x = t • (v - x) := by
  obtain ⟨f, hfin, hvec, hsgn, hsum⟩ := hy
  by_cases hxv : x = v
  · refine ⟨0, le_refl 0, ?_⟩
    subst hxv
    have hEq : hfin.toFinset = ({x} : Finset V3) := by ext w; simp
    rw [hEq] at hvec hsum
    simp only [Finset.sum_singleton] at hvec hsum
    rw [hvec, hsum, one_smul, sub_self, zero_smul]
  · refine ⟨f v, hsgn v (by simp), ?_⟩
    rw [sum_insert_single_v hfin hxv] at hvec
    rw [sum_insert_single_s hfin hxv] at hsum
    have hfx : f x = 1 - f v := by linarith
    rw [hvec, hfx]
    module

/-- HOL `PRESERABLE_AFF_GE_SUBSET` (local_lemmas.hl:2676). -/
theorem PRESERABLE_AFF_GE_SUBSET {x a b : V3} (ha : a ∈ affGe ({x} : Set V3) ({b} : Set V3)) :
    affGe ({x} : Set V3) ({a} : Set V3) ⊆ affGe ({x} : Set V3) ({b} : Set V3) := by
  obtain ⟨t, ht0, hta⟩ := la5_affGe2_extract ha
  intro z hz
  obtain ⟨s, hs0, hsz⟩ := la5_affGe2_extract hz
  exact CONDS_IN_HAFL_LINE (mul_nonneg hs0 ht0) (by rw [hsz, hta, smul_smul])

/-- HOL `AFF_GE_EQ` (local_lemmas.hl:2686). -/
theorem AFF_GE_EQ {x a b : V3} {t : ℝ} (ht : 0 < t) (heq : a - x = t • (b - x)) :
    affGe ({x} : Set V3) ({a} : Set V3) = affGe ({x} : Set V3) ({b} : Set V3) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro z hz
    obtain ⟨s, hs0, hsz⟩ := la5_affGe2_extract hz
    exact CONDS_IN_HAFL_LINE (mul_nonneg hs0 ht.le) (by rw [hsz, heq, smul_smul])
  · intro z hz
    obtain ⟨s, hs0, hsz⟩ := la5_affGe2_extract hz
    have hbx : b - x = t⁻¹ • (a - x) := by
      rw [heq, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    exact CONDS_IN_HAFL_LINE (mul_nonneg hs0 (inv_nonneg.2 ht.le)) (by rw [hsz, hbx, smul_smul])

/-- HOL `AFF2_ITR_CONV0_IMP_SAME_ENDS` (local_lemmas.hl:2709). -/
theorem AFF2_ITR_CONV0_IMP_SAME_ENDS {x y a b t : V3}
    (ht : t ∈ ((affineSpan ℝ ({x, y} : Set V3) : Set V3) ∩
      conv0_p2 ({a, b} : Set V3))) :
    (a ∈ affineSpan ℝ ({x, y} : Set V3) ↔ b ∈ affineSpan ℝ ({x, y} : Set V3)) := by
  have key : ∀ u v : V3, t ∈ conv0_p2 ({u, v} : Set V3) →
      v ∈ (affineSpan ℝ ({x, y} : Set V3) : Set V3) →
      u ∈ (affineSpan ℝ ({x, y} : Set V3) : Set V3) := by
    intro u v hconv hv
    obtain ⟨α, β, hα, hβ, hsum, htuv⟩ := la5_conv02_extract hconv
    have h1 : t = β • v + α • u := by rw [htuv, add_comm]
    rw [SetLike.mem_coe, la5_conv02_partner (by linarith) hα.ne' h1]
    have ht1 : t ∈ (affineSpan ℝ ({x, y} : Set V3)) := ht.1
    exact AffineMap.lineMap_mem (1 / α) hv ht1
  constructor
  · intro ha
    have hsym : t ∈ conv0_p2 ({b, a} : Set V3) := by
      have hca : conv0_p2 ({b, a} : Set V3) = conv0_p2 ({a, b} : Set V3) := by
        rw [Set.pair_comm (a := b) (b := a)]
      rw [hca]
      exact ht.2
    exact key b a hsym ha
  · intro hb
    exact key a b ht.2 hb

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
    (affineSpan ℝ ({x, u} : Set V3) : Set V3) ⊆ affineSpan ℝ ({x, v, w} : Set V3) := by
  obtain ⟨b, c, hb, hc, hgt⟩ := la5_affGt_extract hx'.1
  obtain ⟨b', hb', hlt⟩ := la5_affLt_extract hx'.2
  have hcore : b' • (u - x) = b • (v - x) + c • (w - x) := by rw [← hgt, hlt]
  have hb'0 : (b':ℝ) ≠ 0 := ne_of_lt hb'
  have hA : (b:ℝ) + c ≠ 0 := by linarith
  have key : ({x, u} : Set V3) ⊆ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) := by
    intro z hz
    have hz' : z = x ∨ z = u := Set.mem_insert_iff.mp hz
    rcases hz' with hz' | hz'
    · rw [hz']
      exact mem_affineSpan ℝ (Set.mem_insert x {v, w})
    · rw [hz']
      have hz1 : AffineMap.lineMap v w (c / (b + c)) - x =
          (1 / (b + c)) • (b • (v - x) + c • (w - x)) := by
        have e1 : (b + c) • (AffineMap.lineMap v w (c / (b + c)) - x) =
            b • (v - x) + c • (w - x) := by
          rw [AffineMap.lineMap_apply_module', smul_sub, smul_add, smul_smul,
            show ((b:ℝ) + c) * (c / ((b:ℝ) + c)) = c from by field_simp,
            smul_sub, smul_sub]
          module
        have e2 : AffineMap.lineMap v w (c / (b + c)) - x =
            (1 / (b + c)) • ((b + c) • (AffineMap.lineMap v w (c / (b + c)) - x)) := by
          rw [smul_smul, show ((1:ℝ) / (b + c) * (b + c)) = 1 from by field_simp, one_smul]
        rw [e2, e1]
      have hux : AffineMap.lineMap x (AffineMap.lineMap v w (c / (b + c))) ((b + c) / b') - x =
          (1 / b') • (b • (v - x) + c • (w - x)) := by
        rw [AffineMap.lineMap_apply_module', hz1, smul_smul,
          show ((b:ℝ) + c) / b' * (1 / (b + c)) = 1 / b' from by field_simp,
          add_sub_cancel_right]
      have hu0 : u - x = (1 / b') • (b • (v - x) + c • (w - x)) := by
        have h1 : b' • (u - x) = b' • ((1 / b') • (b • (v - x) + c • (w - x))) := by
          rw [smul_smul, show ((b':ℝ) * (1 / b')) = 1 from by field_simp, one_smul]
          exact hcore
        exact smul_right_injective V3 hb'0 h1
      have hzspan : AffineMap.lineMap v w (c / (b + c)) ∈
          (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) := by
        have hp : AffineMap.lineMap v w (c / (b + c)) ∈
            (affineSpan ℝ ({v, w} : Set V3) : Set V3) :=
          AffineMap.lineMap_mem_affineSpan_pair _ _ _
        exact affineSpan_mono ℝ (Set.subset_insert x {v, w}) (SetLike.mem_coe.mp hp)
      have hueq : u = AffineMap.lineMap x (AffineMap.lineMap v w (c / (b + c)))
          ((b + c) / b') := by
        rw [← sub_add_cancel (a := u) (b := x), hu0, ← hux, sub_add_cancel]
      rw [hueq]
      exact la5_lineMap_mem_span ((b + c) / b')
        (mem_affineSpan ℝ (Set.mem_insert x {v, w})) hzspan
  exact affineSpan_le.mpr key


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
    ∀ l : ℕ, l ≤ V.ncard → ({f^[n] v | n < l} : Set α).ncard = l := by
  obtain ⟨p, hp0, hpx, hdis, -, hcard⟩ := la5_orbit_cycle horb hv
  intro l hl
  rw [hcard] at hl
  have himage : ({f^[n] v | n < l} : Set α) = (fun n : ℕ => f^[n] v) '' Set.Iio l := rfl
  have hInj : Set.InjOn (fun n : ℕ => f^[n] v) (Set.Iio l) := by
    intro i hi j hj hcon
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd hcon (hdis i j h (by have := Set.mem_Iio.mp hj; omega))
    · exact h
    · exact absurd hcon.symm (hdis j i h (by have := Set.mem_Iio.mp hi; omega))
  rw [himage, Set.InjOn.ncard_image hInj]
  exact Set.ncard_Iio_nat l


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
    {f^[n] v | n < V.ncard} = V := by
  obtain ⟨p, hp0, hpx, hdis, hset, hcard⟩ := la5_orbit_cycle horb hv
  rw [hcard]
  exact hset



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
theorem LOFA_IMP_NOT_INCLUDE_VEC0 (h : localFan_p2 V E FF) : ¬((0:V3) ∈ V) :=
  fun h0 => (la5_FAN_of_localFan h).2.2.2.1 h0

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
    ({x.1, x.2} : Set V3) ∈ E ∧ ({y.1, y.2} : Set V3) ∈ E :=
  ⟨LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hx, LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hy⟩

/-- HOL `INTERIOR_ANGLE1_POS` (local_lemmas.hl:3989). -/
theorem INTERIOR_ANGLE1_POS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    0 < interiorAngle1_p2 0 FF v := sorry

/-- Lane support (LA5 r3): two-point `affLt` witness construction (pair
distinct). -/
private theorem la5_affLt2_intro {p q y : V3} {s t : ℝ} (hpq : p ≠ q) (hst : s + t = 1)
    (ht : t < 0) (hy : y = s • p + t • q) : y ∈ affLt ({p} : Set V3) ({q} : Set V3) := by
  have hfin : ((({p} : Set V3) ∪ {q}) : Set V3).Finite := by simp
  have hEq : hfin.toFinset = ({p, q} : Finset V3) := by ext w; simp; tauto
  refine ⟨fun w => if w = q then t else s, hfin, ?_, ?_, ?_⟩
  · rw [hEq, Finset.sum_insert (by simp [hpq] : ¬(p ∈ ({q} : Finset V3))),
      Finset.sum_singleton]
    simp only [hpq, reduceIte]
    exact hy
  · intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simp only [reduceIte]
    exact ht
  · rw [hEq, Finset.sum_insert (by simp [hpq] : ¬(p ∈ ({q} : Finset V3))),
      Finset.sum_singleton]
    simp only [hpq, reduceIte]
    exact hst

/-- HOL `FAN_IMP_NOT_IN_AFF_GE` (local_lemmas.hl:4034). -/
theorem FAN_IMP_NOT_IN_AFF_GE {x v w : V3} (hfan : FAN x V E)
    (hvw : ({v, w} : Set V3) ⊆ V) (hvw2 : v ≠ w) : ¬(v ∈ affGe ({x} : Set V3) ({w} : Set V3)) := by
  obtain ⟨-, -, -, h2, -, h7⟩ := hfan
  have hvV : v ∈ V := hvw (by simp)
  have hwV : w ∈ V := hvw (by simp)
  have hxv : x ≠ v := by
    intro h
    exact h2 (by rw [h]; exact hvV)
  by_contra hmem
  have hvin : v ∈ affGe ({x} : Set V3) ({v} : Set V3) :=
    CONDS_IN_HAFL_LINE (t := 1) (by norm_num) (by rw [one_smul])
  have hE1 : ({v} : Set V3) ∈ E ∪ {s | ∃ z ∈ V, s = {z}} := by
    refine Set.mem_union_right _ ?_
    exact ⟨v, hvV, rfl⟩
  have hE2 : ({w} : Set V3) ∈ E ∪ {s | ∃ z ∈ V, s = {z}} := by
    refine Set.mem_union_right _ ?_
    exact ⟨w, hwV, rfl⟩
  have hkey : (v:V3) ∈ affGe ({x} : Set V3) ({v} : Set V3) ∩
      affGe ({x} : Set V3) ({w} : Set V3) := ⟨hvin, hmem⟩
  rw [h7 {v} hE1 {w} hE2] at hkey
  have hinter : (({v} : Set V3) ∩ {w} : Set V3) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    exact ⟨fun hz => hvw2 (hz.1.symm.trans hz.2), fun hz => hz.elim⟩
  rw [hinter] at hkey
  obtain ⟨f, hfin, hvec, -, hsum⟩ := hkey
  have hEq : hfin.toFinset = ({x} : Finset V3) := by ext z; simp
  rw [hEq] at hvec hsum
  simp only [Finset.sum_singleton] at hvec hsum
  exact hxv (by rw [hvec, hsum, one_smul])

/-- HOL `IN_AFF_LT_IMP_IN_CONV` (local_lemmas.hl:4061). -/
theorem IN_AFF_LT_IMP_IN_CONV {x a b : V3} (hdis : Disjoint ({x} : Set V3) ({b} : Set V3))
    (ha : a ∈ affLt ({x} : Set V3) ({b} : Set V3)) : x ∈ conv0_p2 ({a, b} : Set V3) := by
  obtain ⟨b0, hb0, htab⟩ := la5_affLt_extract ha
  have ha' : a = (1 - b0) • x + b0 • b := by
    rw [sub_eq_iff_eq_add.mp htab]
    module
  have hc : (1:ℝ) - b0 ≠ 0 := by linarith
  have hp1 : (0:ℝ) < 1 / (1 - b0) := div_pos (by norm_num) (by linarith)
  have hp2 : (0:ℝ) < -b0 / (1 - b0) := div_pos (by linarith) (by linarith)
  have h12 : (1:ℝ)/(1 - b0) + -b0/(1 - b0) = 1 := by
    rw [← add_div, show ((1:ℝ) + -b0) = 1 - b0 from by ring, div_self hc]
  have hterm : x = ((1:ℝ)/(1 - b0)) • a + ((-b0:ℝ)/(1 - b0)) • b := by
    have key : ((1:ℝ)/(1 - b0)) • a = x + (b0 / (1 - b0)) • b := by
      rw [ha', smul_add, smul_smul, smul_smul]
      rw [show ((1:ℝ)/(1 - b0) * (1 - b0)) = 1 from by field_simp,
        one_smul,
        show ((1:ℝ)/(1 - b0) * b0) = b0 / (1 - b0) from by ring]
    rw [key, add_assoc, ← add_smul,
      show ((b0:ℝ)/(1 - b0) + -b0/(1 - b0)) = 0 from by ring, zero_smul, add_zero]
  have hmem := IN_CONV0 (x := a) (y := b) (a := (1:ℝ)/(1 - b0)) (b := (-b0:ℝ)/(1 - b0)) hp1 hp2
  rw [h12, one_div_one, one_smul] at hmem
  rw [hterm]
  exact hmem

/-- HOL `FAN_SUB_NOT_EQ_COLL_IN_CONV0` (local_lemmas.hl:4090). -/
theorem FAN_SUB_NOT_EQ_COLL_IN_CONV0 {x v w : V3} (hfan : FAN x V E)
    (hvw : ({v, w} : Set V3) ⊆ V) (hvw2 : v ≠ w)
    (hcol : Collinear ℝ ({x, v, w} : Set V3)) : x ∈ conv0_p2 ({v, w} : Set V3) := by
  have h2 := hfan.2.2.2.1
  have hwV : w ∈ V := hvw (by simp)
  have hxw : x ≠ w := by
    intro h
    exact h2 (by rw [h]; exact hwV)
  have hdis : Disjoint ({x} : Set V3) ({w} : Set V3) := by
    refine Set.disjoint_iff_inter_eq_empty.mpr ?_
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false]
    exact ⟨fun hz => hxw (hz.1.symm.trans hz.2), fun hz => hz.elim⟩
  have hcol2 : Collinear ℝ ({x, w, v} : Set V3) := by
    have heq : ({x, w, v} : Set V3) = ({x, v, w} : Set V3) := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [heq]
    exact hcol
  rcases (collinear_triple_iff (x := x) (v := w) (u := v)).mp hcol2 with hmem | hxw2
  · obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
    rw [AffineMap.lineMap_apply_module] at ht
    by_cases htc : 0 ≤ t
    · exact absurd (CONDS_IN_HAFL_LINE htc (by rw [← ht]; module))
        (FAN_IMP_NOT_IN_AFF_GE hfan hvw hvw2)
    · have ht0 : t < 0 := lt_of_not_ge htc
      have hvlt : v ∈ affLt ({x} : Set V3) ({w} : Set V3) :=
        la5_affLt2_intro hxw (by ring) ht0 ht.symm
      exact IN_AFF_LT_IMP_IN_CONV hdis hvlt
  · exact absurd hxw2 hxw

/-- Lane support (LA5): build an `affGe {p} {q}` membership from a two-point
affine decomposition with nonnegative second coefficient (pair distinct). -/
private theorem la5_affGe2_intro {p q y : V3} {s t : ℝ} (hpq : p ≠ q) (hst : s + t = 1)
    (ht : 0 ≤ t) (hy : y = s • p + t • q) : y ∈ affGe ({p} : Set V3) ({q} : Set V3) := by
  have hfin : ((({p} : Set V3) ∪ {q}) : Set V3).Finite := by simp
  have hEq : hfin.toFinset = ({p, q} : Finset V3) := by ext w; simp; tauto
  refine ⟨fun w => if w = q then t else s, hfin, ?_, ?_, ?_⟩
  · rw [hEq, Finset.sum_insert (by simp [hpq] : ¬(p ∈ ({q} : Finset V3))),
      Finset.sum_singleton]
    simp only [hpq, reduceIte]
    exact hy
  · intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simp only [reduceIte]
    exact ht
  · rw [hEq, Finset.sum_insert (by simp [hpq] : ¬(p ∈ ({q} : Finset V3))),
      Finset.sum_singleton]
    simp only [hpq, reduceIte]
    exact hst

/-- Lane support (LA5): `conv0_p2` ignores the order of its two points. -/
private theorem la5_conv02_comm {a b : V3} :
    conv0_p2 ({a, b} : Set V3) = conv0_p2 ({b, a} : Set V3) := by
  ext w
  constructor
  · intro h
    obtain ⟨f, hfin, hvec, hpos, hsum⟩ := h
    have hfin2 : ((∅ : Set V3) ∪ {b, a} : Set V3).Finite := by simp
    have hEq : hfin.toFinset = hfin2.toFinset := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    rw [hEq] at hvec hsum
    refine ⟨f, hfin2, hvec, ?_, hsum⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hpos z (by simp)
    · exact hpos z (by simp)
  · intro h
    obtain ⟨f, hfin, hvec, hpos, hsum⟩ := h
    have hfin2 : ((∅ : Set V3) ∪ {a, b} : Set V3).Finite := by simp
    have hEq : hfin.toFinset = hfin2.toFinset := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    rw [hEq] at hvec hsum
    refine ⟨f, hfin2, hvec, ?_, hsum⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hpos z (by simp)
    · exact hpos z (by simp)

/-- HOL `IN_CONV_LINE_SEPERATABLE` (local_lemmas.hl:4119). -/
theorem IN_CONV_LINE_SEPERATABLE {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    (affineSpan ℝ ({a, b} : Set V3) : Set V3) =
      affGe ({x} : Set V3) ({a} : Set V3) ∪ affGe ({x} : Set V3) ({b} : Set V3) := by
  by_cases hab : a = b
  · -- degenerate: a = b forces x = a and both sides collapse to {x}.
    have hxa : x = a := (IN_CONV0_EQ_EQ hx).mpr hab
    rw [← hab, ← hxa, Set.insert_eq_of_mem (Set.mem_singleton_iff.mpr rfl),
      AffineSubspace.coe_affineSpan_singleton, Set.union_self]
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hfin : ((({x} : Set V3) ∪ {x}) : Set V3).Finite := by simp
      have hEq : hfin.toFinset = ({x} : Finset V3) := by ext w; simp
      show ∃ f : V3 → ℝ, ∃ h : (({x} : Set V3) ∪ {x}).Finite,
        x = ∑ w ∈ h.toFinset, f w • w ∧
          (∀ w ∈ ({x} : Set V3), 0 ≤ f w) ∧
          ∑ w ∈ h.toFinset, f w = 1
      refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
      · rw [hEq, Finset.sum_singleton]
        simp
      · intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        simp
      · rw [hEq, Finset.sum_singleton]
    · intro hz
      obtain ⟨f, hfin, hvec, -, hsum⟩ := hz
      have hEq : hfin.toFinset = ({x} : Finset V3) := by ext w; simp
      rw [hEq] at hvec hsum
      simp only [Finset.sum_singleton] at hvec hsum
      rw [Set.mem_singleton_iff]
      rw [hvec, hsum, one_smul]
  · obtain ⟨α, β, hα, hβ, hsum, hxab⟩ := la5_conv02_extract hx
    have hα0 : α ≠ 0 := hα.ne'
    have hβ0 : β ≠ 0 := hβ.ne'
    have hxa : x ≠ a := fun h => hab ((IN_CONV0_EQ_EQ hx).mp h)
    have hx' : x ∈ conv0_p2 ({b, a} : Set V3) := by rw [la5_conv02_comm]; exact hx
    have hxb : x ≠ b := fun h => hab (((IN_CONV0_EQ_EQ hx').mp h).symm)
    have hsum' : (α + β) • a = (1:ℝ) • a := by rw [hsum, one_smul]
    have hsum'' : (α + β) • b = (1:ℝ) • b := by rw [hsum, one_smul]
    ext z
    constructor
    · intro hz
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hz
      obtain ⟨r, hr⟩ := hz
      rw [AffineMap.lineMap_apply_module] at hr
      -- hr : (1 - r) • a + r • b = z
      by_cases hca : 0 ≤ 1 - r / β
      · have hza : z = (r / β) • x + (1 - r / β) • a := by
          have h1 : (z - a : V3) = r • (b - a) := by
            rw [← hr]
            module
          have h2 : (x - a : V3) = β • (b - a) := by
            linear_combination (norm := module) hxab + hsum'
          have hzma : (z - a : V3) = (r / β) • (x - a) := by
            rw [h1, h2, smul_smul, div_mul_cancel₀ _ hβ0]
          rw [sub_eq_iff_eq_add.mp hzma, sub_smul]
          module
        exact Set.mem_union_left _ (la5_affGe2_intro hxa (by ring) hca hza)
      · have h1 : (1:ℝ) - r / β < 0 := not_le.mp hca
        have h2 : β ≤ r := by
          have hkey : (1:ℝ) < r / β := by linarith
          have h3 := mul_lt_mul_of_pos_right hkey hβ
          rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hβ0, one_mul] at h3
          linarith
        have hsign : 0 ≤ 1 - (1 - r) / α := by
          rw [sub_nonneg, div_le_one hα]
          linarith
        have hzb : z = ((1 - r) / α) • x + (1 - (1 - r) / α) • b := by
          have h1b : (z - b : V3) = (1 - r) • (a - b) := by
            rw [← hr]
            module
          have h2b : (x - b : V3) = α • (a - b) := by
            linear_combination (norm := module) hxab + hsum''
          have hzmb : (z - b : V3) = ((1 - r) / α) • (x - b) := by
            rw [h1b, h2b, smul_smul, div_mul_cancel₀ _ hα0]
          rw [sub_eq_iff_eq_add.mp hzmb, sub_smul]
          module
        exact Set.mem_union_right _ (la5_affGe2_intro hxb (by ring) hsign hzb)
    · intro hz
      simp only [Set.mem_union] at hz
      rcases hz with hz | hz
      · obtain ⟨t, ht⟩ := affGe_ray hxa hz
        refine la5_affComb_mem_affSpan (α := (1 - t) * α + t) (β := (1 - t) * β) ?_ ?_
        · have e : (1 - t) * α + t + (1 - t) * β = (1 - t) * (α + β) + t := by ring
          rw [e, hsum]
          ring
        · rw [sub_eq_iff_eq_add.mp ht, hxab]
          module
      · obtain ⟨t, ht⟩ := affGe_ray hxb hz
        refine la5_affComb_mem_affSpan (α := (1 - t) * α) (β := (1 - t) * β + t) ?_ ?_
        · have e : (1 - t) * α + ((1 - t) * β + t) = (1 - t) * (α + β) + t := by ring
          rw [e, hsum]
          ring
        · rw [sub_eq_iff_eq_add.mp ht, hxab]
          module

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

/-- HOL `LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI` (local_lemmas.hl:4222). Proof note:
part 1 is `FAN_SUB_NOT_EQ_COLL_IN_CONV0` on the lunar collinearity; part 2
instantiates `OZQVSFF` with (u' := v, v' := u, w' := w, P := affineSpan
{u,v,w}) after deriving the two OZQVSFF side conditions `{v,w} ∩ aff {0,u} =
∅` and `¬ collinear {u,v,w}` from `IN_CONV_LINE_SEPERATABLE` +
`FAN_IMP_NOT_IN_AFF_GE` + `AFF2_DET_BY_TWO_POINTS` +
`AFF2_ITR_CONV0_IMP_SAME_ENDS`. NOTE: `OZQVSFF` itself still carries its
placeholder body, so this proof inherits that placeholder-axiom dependency
(chain depth reduced by one; genuine closure lands together with
`OZQVSFF`). -/
theorem LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    (0:V3) ∈ conv0_p2 ({v, w} : Set V3) ∧
      (∀ u ∈ V \ {v, w}, interiorAngle1_p2 0 FF u = Real.pi ∧
        rhoNode1_p2 FF u ∈ affineSpan ℝ ({u, v, w} : Set V3) ∧
        ivsRhoNode1_p2 FF u ∈ affineSpan ℝ ({u, v, w} : Set V3)) := by
  obtain ⟨-, hvw, hvw2, hcol⟩ := hl
  obtain ⟨-, hFAN0⟩ := CVLF_LF_F h
  have h0c : (0:V3) ∈ conv0_p2 ({v, w} : Set V3) :=
    FAN_SUB_NOT_EQ_COLL_IN_CONV0 hFAN0 hvw hvw2 hcol
  refine ⟨h0c, ?_⟩
  intro u hu
  obtain ⟨huV, hnv⟩ := hu
  have huv : u ≠ v := by
    intro hcon
    exact hnv (by simp [hcon])
  have huw : u ≠ w := by
    intro hcon
    exact hnv (by simp [hcon])
  have h0V : (0:V3) ∉ V := hFAN0.2.2.2.1
  have hvV : v ∈ V := hvw (by simp)
  have hwV : w ∈ V := hvw (by simp)
  have h0v : (0:V3) ≠ v := by
    intro hcon
    exact h0V (by rw [hcon]; exact hvV)
  -- any member point sits in its own span
  have memIns : ∀ (z : V3) (S : Set V3), z ∈ S →
      z ∈ (affineSpan ℝ S : Set V3) := by
    intro z S hz
    have hz1 : ({z} : Set V3) ⊆ S := by
      intro a ha
      simp only [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hz
    exact (SetLike.le_def.mp (affineSpan_mono ℝ hz1))
      ((AffineSubspace.mem_affineSpan_singleton ℝ V3).mpr rfl)
  obtain ⟨α, β, hα, hβ, hsum, h0vw⟩ := la5_conv02_extract h0c
  have h0span : (0:V3) ∈ (affineSpan ℝ ({v, w} : Set V3) : Set V3) :=
    la5_affComb_mem_affSpan hsum h0vw
  have affSpan_vw : (affineSpan ℝ ({v, w} : Set V3) : Set V3) =
      affGe ({0} : Set V3) ({v} : Set V3) ∪ affGe ({0} : Set V3) ({w} : Set V3) :=
    IN_CONV_LINE_SEPERATABLE h0c
  have hUV : ({u, v} : Set V3) ⊆ V := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact huV
    · exact hvV
  have hUW : ({u, w} : Set V3) ⊆ V := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact huV
    · exact hwV
  have hFv : ¬ (u ∈ affGe ({0} : Set V3) ({v} : Set V3)) :=
    FAN_IMP_NOT_IN_AFF_GE hFAN0 hUV huv
  have hFw : ¬ (u ∈ affGe ({0} : Set V3) ({w} : Set V3)) :=
    FAN_IMP_NOT_IN_AFF_GE hFAN0 hUW huw
  have hncol : ¬ Collinear ℝ ({u, v, w} : Set V3) := by
    intro hcol3
    have hcol4 : Collinear ℝ ({v, w, u} : Set V3) := by
      have heq : ({v, w, u} : Set V3) = ({u, v, w} : Set V3) := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [heq]
      exact hcol3
    rcases (collinear_triple_iff (x := v) (v := w) (u := u)).mp hcol4 with hu2 | hvw3
    · rw [← SetLike.mem_coe, affSpan_vw] at hu2
      simp only [Set.mem_union] at hu2
      rcases hu2 with hu2 | hu2
      · exact hFv hu2
      · exact hFw hu2
    · exact hvw2 hvw3
  have hvn : ¬ ((v:V3) ∈ (affineSpan ℝ ({0, u} : Set V3) : Set V3)) := by
    intro hv
    have h0u' : (0:V3) ∈ (affineSpan ℝ ({0, u} : Set V3) : Set V3) :=
      memIns 0 ({0, u} : Set V3) (by simp)
    have huu' : (u:V3) ∈ (affineSpan ℝ ({0, u} : Set V3) : Set V3) :=
      memIns u ({0, u} : Set V3) (by simp)
    have hsub01 : (({0, v} : Set V3) ⊆ ((affineSpan ℝ ({0, u} : Set V3) : Set V3))) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz0 | hzv
      · rw [hz0]
        exact h0u'
      · rw [hzv]
        exact hv
    have h0u_eq : (affineSpan ℝ ({0, u} : Set V3) : Set V3) =
        (affineSpan ℝ ({0, v} : Set V3) : Set V3) :=
      AFF2_DET_BY_TWO_POINTS hsub01 h0v
    have hsub0v : (({0, v} : Set V3) ⊆ ((affineSpan ℝ ({v, w} : Set V3) : Set V3))) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz0 | hzv
      · rw [hz0]
        exact h0span
      · rw [hzv]
        exact memIns v ({v, w} : Set V3) (by simp)
    have hvw_eq : (affineSpan ℝ ({v, w} : Set V3) : Set V3) =
        (affineSpan ℝ ({0, v} : Set V3) : Set V3) :=
      AFF2_DET_BY_TWO_POINTS hsub0v h0v
    have hu_vw : (u:V3) ∈ (affineSpan ℝ ({v, w} : Set V3) : Set V3) := by
      rw [hvw_eq, ← h0u_eq]
      exact huu'
    rw [affSpan_vw] at hu_vw
    simp only [Set.mem_union] at hu_vw
    rcases hu_vw with hcu | hcu
    · exact hFv hcu
    · exact hFw hcu
  have hwn : ¬ ((w:V3) ∈ (affineSpan ℝ ({0, u} : Set V3) : Set V3)) := by
    have h0in : (0:V3) ∈ ((affineSpan ℝ ({0, u} : Set V3) : Set V3) ∩
        conv0_p2 ({v, w} : Set V3)) :=
      Set.mem_inter (memIns 0 ({0, u} : Set V3) (by simp)) h0c
    intro hw
    exact hvn ((AFF2_ITR_CONV0_IMP_SAME_ENDS h0in).mpr hw)
  have hne : ¬(((affineSpan ℝ ({u, 0} : Set V3) : Set V3) ∩
      conv0_p2 ({w, v} : Set V3)) = ∅) := by
    intro hcon
    have hmem0 : (0:V3) ∈ ((affineSpan ℝ ({u, 0} : Set V3) : Set V3) ∩
        conv0_p2 ({w, v} : Set V3)) :=
      Set.mem_inter (memIns 0 ({u, 0} : Set V3) (by simp))
        (by rw [Set.pair_comm (a := w) (b := v)]; exact h0c)
    rw [hcon] at hmem0
    exact absurd hmem0 (by simp)
  have hdisj : (({v, w} : Set V3) ∩ (affineSpan ℝ ({0, u} : Set V3) : Set V3)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz1
    rcases hz1 with rfl | rfl
    · exact hvn hz2
    · exact hwn hz2
  have hOZsub : (({v, u, w} : Set V3) ⊆ V) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hvV
    · exact huV
    · exact hwV
  have hOZP : plane_p2 (affineSpan ℝ ({u, v, w} : Set V3) : Set V3) :=
    ⟨u, v, w, hncol, rfl⟩
  have hOZsub2 : (({0, v, u, w} : Set V3) ⊆
      (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz0 | hzv | hzu | hzw
    · rw [hz0]
      have hsubvw : (({v, w} : Set V3) ⊆
        (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with hav | haw
        · rw [hav]
          exact memIns v ({u, v, w} : Set V3) (by simp)
        · rw [haw]
          exact memIns w ({u, v, w} : Set V3) (by simp)
      exact S_SUBSET_IMP_AFF_S_TOO hsubvw h0span
    · rw [hzv]
      exact memIns v ({u, v, w} : Set V3) (by simp)
    · rw [hzu]
      exact memIns u ({u, v, w} : Set V3) (by simp)
    · rw [hzw]
      exact memIns w ({u, v, w} : Set V3) (by simp)
  obtain ⟨hang, hrho, hivs⟩ :=
    OZQVSFF (V := V) (E := E) (FF := FF) (u := v) (v := u) (w := w)
      (P := (affineSpan ℝ ({u, v, w} : Set V3)))
      h hOZsub hOZP hOZsub2 hdisj hne
  exact ⟨hang, hrho, hivs⟩

/-- Lane support (LA5): re-coefficients a signed affine combination onto a
larger support pair. The sign condition survives verbatim because the new
target side `t2` is contained in `t1`, and the enlarged support only adds
zero coefficients. -/
private theorem la5_affsign_mono {sgn : ℝ → Prop} {s1 t1 s2 t2 : Set V3} {v : V3}
    (h1 : Affsign sgn s1 t1 v) (ht2 : t2 ⊆ t1)
    (hsub : s1 ∪ t1 ⊆ s2 ∪ t2) (hf2 : (s2 ∪ t2).Finite) :
    Affsign sgn s2 t2 v := by
  obtain ⟨f, hfin1, hvec, hcond, hone⟩ := h1
  have hle : hfin1.toFinset ⊆ hf2.toFinset := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw ⊢
    exact hsub hw
  let g : V3 → ℝ := fun w => if w ∈ s1 ∪ t1 then f w else 0
  have hgmem : ∀ w ∈ hfin1.toFinset, g w = f w := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    show (if w ∈ s1 ∪ t1 then f w else 0) = f w
    rw [if_pos hw]
  have hgzero : ∀ w ∈ hf2.toFinset, w ∉ hfin1.toFinset → g w • w = 0 := by
    intro w _ hwout
    rw [Set.Finite.mem_toFinset] at hwout
    show (if w ∈ s1 ∪ t1 then f w else 0) • w = 0
    rw [if_neg hwout, zero_smul]
  have hgzero' : ∀ w ∈ hf2.toFinset, w ∉ hfin1.toFinset → g w = 0 := by
    intro w _ hwout
    rw [Set.Finite.mem_toFinset] at hwout
    show (if w ∈ s1 ∪ t1 then f w else 0) = 0
    rw [if_neg hwout]
  refine ⟨g, hf2, ?_, ?_, ?_⟩
  · rw [hvec]
    calc ∑ w ∈ hfin1.toFinset, f w • w
        = ∑ w ∈ hfin1.toFinset, g w • w :=
          Finset.sum_congr rfl (fun w hw => by rw [hgmem w hw])
      _ = ∑ w ∈ hf2.toFinset, g w • w := Finset.sum_subset hle hgzero
  · intro w hw
    have hw1 : w ∈ t1 := ht2 hw
    have hw' : w ∈ s1 ∪ t1 := Set.mem_union_right s1 hw1
    show sgn (if w ∈ s1 ∪ t1 then f w else 0)
    rw [if_pos hw']
    exact hcond w hw1
  · calc ∑ w ∈ hf2.toFinset, g w
        = ∑ w ∈ hfin1.toFinset, g w := (Finset.sum_subset hle hgzero').symm
      _ = ∑ w ∈ hfin1.toFinset, f w :=
          Finset.sum_congr rfl (fun w hw => hgmem w hw)
      _ = 1 := hone

/-- HOL `AFF_GE_MONO_TRANS` (local_lemmas.hl:4336). -/
theorem AFF_GE_MONO_TRANS {S X Y : Set V3} (hsub : S ⊆ X) :
    affGe (X \ S) (Y ∪ S) ⊆ affGe X Y := by
  intro v hv
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := hv
  have hfXY : (X ∪ Y).Finite := by
    refine hfin.subset ?_
    intro w hw
    simp only [Set.mem_union] at hw
    rcases hw with hw | hw
    · by_cases hws : w ∈ S
      · exact Set.mem_union_right (X \ S) (Set.mem_union_right Y hws)
      · exact Set.mem_union_left (Y ∪ S) ⟨hw, hws⟩
    · exact Set.mem_union_right (X \ S) (Set.mem_union_left S hw)
  refine la5_affsign_mono ⟨f, hfin, hvec, hpos, hone⟩
    (fun w hw => Set.mem_union_left S hw) ?_ hfXY
  intro w hw
  rcases hw with hw | hw
  · exact Set.mem_union_left Y hw.1
  rcases hw with hw | hw
  · exact Set.mem_union_right X hw
  · exact Set.mem_union_left Y (hsub hw)

theorem AFF_GT_MONO_TRANS {S X Y : Set V3} (hsub : S ⊆ X) :
    affGt (X \ S) (Y ∪ S) ⊆ affGt X Y := by
  intro v hv
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := hv
  have hfXY : (X ∪ Y).Finite := by
    refine hfin.subset ?_
    intro w hw
    simp only [Set.mem_union] at hw
    rcases hw with hw | hw
    · by_cases hws : w ∈ S
      · exact Set.mem_union_right (X \ S) (Set.mem_union_right Y hws)
      · exact Set.mem_union_left (Y ∪ S) ⟨hw, hws⟩
    · exact Set.mem_union_right (X \ S) (Set.mem_union_left S hw)
  refine la5_affsign_mono ⟨f, hfin, hvec, hpos, hone⟩
    (fun w hw => Set.mem_union_left S hw) ?_ hfXY
  intro w hw
  rcases hw with hw | hw
  · exact Set.mem_union_left Y hw.1
  rcases hw with hw | hw
  · exact Set.mem_union_right X hw
  · exact Set.mem_union_left Y (hsub hw)


/-- HOL `LOFA_IMP_BIJ_FF_V` (local_lemmas.hl:4412). -/
theorem LOFA_IMP_BIJ_FF_V (h : localFan_p2 V E FF) : Set.BijOn Prod.fst FF V :=
  WRGCVDR_BIJ h

/-- HOL `LOFA_IMP_CARD_FF_V_EQ` (local_lemmas.hl:4415). -/
theorem LOFA_IMP_CARD_FF_V_EQ (h : localFan_p2 V E FF) : FF.ncard = V.ncard := by
  have hbij : Set.BijOn Prod.fst FF V := LOFA_IMP_BIJ_FF_V h
  have himg : Prod.fst '' FF = V := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hbij.1 hd
    · intro hx
      exact hbij.2.2 hx
  rw [← himg, Set.InjOn.ncard_image hbij.2.1]

/-- HOL `FIRST_IN_AFF` (local_lemmas.hl:4423). -/
theorem FIRST_IN_AFF (a : V3) (S : Set V3) :
    a ∈ (affineSpan ℝ (insert a S) : Set V3) :=
  subset_affineSpan ℝ (insert a S) (Set.mem_insert a S)

/-- HOL `HALF_CIRCULAR_IN_PLANE` (local_lemmas.hl:4431) — filled (LA5
downstream wave 2026-10-08): mirrors the HOL induction on `l ≤ n`. Step
case consumes the second component of `LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI`
(`rho u ∈ aff {u, v, w}`) at `u := rho^[m] v` — legal since the two
non-revisit side conditions come from `LOFA_IMP_DIS_ELMS` (i := 0 and
i := m against n) plus `LOCAL_FAN_ORBIT_MAP_VITER` (u ∈ V) — and
transports `aff {u, v, w} ⊆ aff {0, v, rho v}` via `affineSpan_le.mpr`
(the HOL `S_SUBSET_IMP_AFF_S_TOO` step), with `w` itself in the plane
from `0 ∈ conv0 {v, w}` (`IN_CONV0_IMP_AFF_EQ`). -/
theorem HALF_CIRCULAR_IN_PLANE (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E)
    (hn : n < V.ncard) (hw : w = (rhoNode1_p2 FF)^[n] v) :
    {(rhoNode1_p2 FF)^[l] v | l ≤ n} ⊆ affineSpan ℝ ({0, v, rhoNode1_p2 FF v} : Set V3) := by
  obtain ⟨hlo, -⟩ := CVLF_LF_F h
  obtain ⟨h0c, hsec⟩ := LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI h hl
  obtain ⟨-, hvw, -, -⟩ := hl
  have hvV : v ∈ V := hvw (by simp)
  have hsub01 : ({(0:V3), v} : Set V3) ⊆ ({(0:V3), v, rhoNode1_p2 FF v} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  -- w lies in the big span: 0 ∈ conv0 {v,w} → aff {v,w} = aff {v,0} ⊆ aff {0,v,ρ v}
  have hwaff : w ∈ (affineSpan ℝ ({(0:V3), v, rhoNode1_p2 FF v} : Set V3) : Set V3) := by
    have h1 : w ∈ (affineSpan ℝ ({v, w} : Set V3) : Set V3) := mem_affineSpan _ (by simp)
    rw [IN_CONV0_IMP_AFF_EQ h0c] at h1
    have hset : ({v, (0:V3)} : Set V3) = ({(0:V3), v} : Set V3) := by ext z; simp; tauto
    rw [hset] at h1
    exact affineSpan_mono ℝ hsub01 h1
  -- induction over the iterates
  have key : ∀ l : ℕ, l ≤ n →
      (rhoNode1_p2 FF)^[l] v ∈ (affineSpan ℝ ({(0:V3), v, rhoNode1_p2 FF v} : Set V3) : Set V3) := by
    intro l
    induction l with
    | zero =>
      intro _
      exact subset_affineSpan ℝ _ (by simp)
    | succ m ih =>
      intro hle
      rw [Function.iterate_succ_apply']
      by_cases hm0 : m = 0
      · rw [hm0, Function.iterate_zero_apply]
        exact subset_affineSpan ℝ _ (by simp)
      · have hcard : FF.ncard = V.ncard := LOFA_IMP_CARD_FF_V_EQ hlo
        have hmn : m < n := Nat.lt_of_succ_le hle
        have hltF : n < FF.ncard := by rw [hcard]; exact hn
        have hltm : m < FF.ncard := by rw [hcard]; omega
        have hmV : (rhoNode1_p2 FF)^[m] v ∈ V := LOCAL_FAN_ORBIT_MAP_VITER hlo hvV m
        -- non-revisit of v (DIS_ELMS instance i := 0) and of w (= rho^[n] v)
        have hne1 : (rhoNode1_p2 FF)^[m] v ≠ v := by
          intro hc
          exact (LOFA_IMP_DIS_ELMS hlo hvV hltm) 0 (by omega)
            (by rw [hc, Function.iterate_zero_apply])
        have hnew : (rhoNode1_p2 FF)^[m] v ≠ w := by
          intro hc
          have hcontra := LOFA_IMP_DIS_ELMS (h := hlo) (hv := hvV) (l := n) hltF m hmn
          exact hcontra (hc.trans hw).symm
        have hmnot : (rhoNode1_p2 FF)^[m] v ∉ ({v, w} : Set V3) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hne1, hnew⟩
        have hmemo := hsec ((rhoNode1_p2 FF)^[m] v) ⟨hmV, hmnot⟩
        refine (affineSpan_le.mpr ?_) hmemo.2.1
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact ih (by omega)
        · exact subset_affineSpan ℝ _ (by simp)
        · exact hwaff
  intro x hx
  obtain ⟨l, hlle, rfl⟩ := hx
  exact key l hlle

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
      azim 0 e v ((rhoNode1_p2 FF)^[n] v) < azim 0 e v ((rhoNode1_p2 FF)^[m] v) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): double induction needs
  -- `SEQUENCE_OF_RHO_NODE_IS_SUC` (the cyclic successor step, itself on the
  -- cyclicSet kit — see LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT's -- NEEDS) for
  -- both the m = n+1 rung and the transitivity rungs, plus
  -- `LOFA_IMP_AZIM_RHO_NODE_ST` (sin ≠ 0 at the cross-product axis) and the
  -- m/n = 0 boundary cases (AZIM_REFL / AZIM_RANGE, real).
  sorry

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
      ((w : V3) : Fin 3 → ℝ)) : V3)} : Set V3) := by
  have hncross : (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ)) ≠ 0 := by
    intro hc
    exact h (by
      simpa using (COLLINEAR_CROSS_0 (x := (0:V3)) (y := v) (z := w)).mpr
        (la5_toLp_eq_zero.mpr (by simpa using hc)))
  intro hcop
  have hmem := la5_coplanar_diff_span (x := (0:V3)) (y := v) (z := w)
    (t := (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((w : V3) : Fin 3 → ℝ)) : V3)) hcop h
  obtain ⟨a, b, hnab⟩ := Submodule.mem_span_pair.mp hmem
  have h2 : a • (((v : V3) : Fin 3 → ℝ)) + b • (((w : V3) : Fin 3 → ℝ))
      = (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ)) := by
    simpa using congrArg (fun a : V3 => (a : Fin 3 → ℝ)) hnab
  have hdotn : ((v : V3) : Fin 3 → ℝ) ⬝ᵥ (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((w : V3) : Fin 3 → ℝ)) = 0 := dot_self_cross _ _
  have hdotw : ((w : V3) : Fin 3 → ℝ) ⬝ᵥ (crossProduct ((v : V3) : Fin 3 → ℝ)
      ((w : V3) : Fin 3 → ℝ)) = 0 := dot_cross_self _ _
  have hpos : 0 < (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ))
      ⬝ᵥ (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ)) :=
    (dot_self_pos_iff _).mpr hncross
  have hnn : (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ))
      ⬝ᵥ (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ)) = 0 := by
    nth_rewrite 2 [← h2]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm,
      hdotn, dotProduct_comm, hdotw]
    simp
  rw [hnn] at hpos
  exact lt_irrefl _ hpos

/-- HOL `COLL_IFF_COLL_CROSS` (local_lemmas.hl:4707). -/
theorem COLL_IFF_COLL_CROSS {v w : V3} :
    Collinear ℝ ({0, v, w} : Set V3) ↔
      Collinear ℝ ({0, v, (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) : V3)} : Set V3) := by
  have hkey : Collinear ℝ ({0, v, w} : Set V3) →
      (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) : V3) = 0 := fun hcol => by
    simpa using (COLLINEAR_CROSS_0 (x := (0:V3)) (y := v) (z := w)).mp hcol
  constructor
  · intro hcol
    rw [hkey hcol]
    simpa using collinear_pair ℝ v 0
  · intro hcol
    by_contra hnc
    have hcross : (crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ)) ≠ 0 := by
      intro h0
      exact hnc (by
        simpa using (COLLINEAR_CROSS_0 (x := (0:V3)) (y := v) (z := w)).mpr
          (la5_toLp_eq_zero.mpr (by simpa using h0)))
    have hv0 : (v : V3) ≠ 0 := by
      intro h0
      refine hnc ?_
      simp only [h0, map_zero, LinearMap.zero_apply, WithLp.toLp_zero]
      exact collinear_triple_iff.mpr (Or.inr rfl)
    have hmem : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) : V3) ∈ affineSpan ℝ ({0, v} : Set V3) :=
      (collinear_triple_iff.mp hcol).resolve_right (fun hh => hv0 hh.symm)
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
    have hexp : (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) : V3) = t • v := by
      rw [← ht]
      simp [AffineMap.lineMap_apply]
    have hdot : ((WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ) ⬝ᵥ ((v : V3) : Fin 3 → ℝ) = 0 :=
      (dotProduct_comm (crossProduct ((v : V3) : Fin 3 → ℝ)
        ((w : V3) : Fin 3 → ℝ)) ((v : V3) : Fin 3 → ℝ)).trans (dot_self_cross v w)
    have h2 : t * (((v : V3) : Fin 3 → ℝ) ⬝ᵥ ((v : V3) : Fin 3 → ℝ)) = 0 := by
      have h3 : ((t • (v : V3) : V3) : Fin 3 → ℝ) ⬝ᵥ ((v : V3) : Fin 3 → ℝ)
          = t * (((v : V3) : Fin 3 → ℝ) ⬝ᵥ ((v : V3) : Fin 3 → ℝ)) := by
        rw [la5_coe_smul, smul_dotProduct]
        simp
      rw [← h3, ← hexp]
      exact hdot
    have hvv : (((v : V3) : Fin 3 → ℝ) ⬝ᵥ ((v : V3) : Fin 3 → ℝ)) ≠ 0 := by
      intro h0
      have hv1 : ((v : V3) : Fin 3 → ℝ) = 0 := dotProduct_self_eq_zero.mp h0
      have hv2 : (v : V3) = 0 := by
        apply WithLp.ofLp_injective 2
        simpa using hv1
      exact hv0 hv2
    rcases mul_eq_zero.mp h2 with h' | h'
    · rw [h'] at hexp
      exact hcross (la5_toLp_eq_zero.mp (by simpa using hexp))
    · exact absurd h' hvv

/-- HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` (local_lemmas.hl:4719). -/
theorem LOCAL_FAN_CHARACTER_OF_RHO_NODE2 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ¬ Collinear ℝ ({0, v, rhoNode1_p2 FF v} : Set V3) :=
  (LOCAL_FAN_CHARACTER_OF_RHO_NODE h hv).2.2

/-- HOL `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` (local_lemmas.hl:4726).
NEEDS (orbit wave 2026-10-08): `LOCAL_FAN_ORBIT_MAP_V` is now real
(`WRGCVDR_ORBIT`, LocalAuto2). Updated (LA5 downstream wave 2026-10-08):
`HALF_CIRCULAR_IN_PLANE` is now real; the residual blockers are exactly
`FIRST_AZIM_CYCLE_EQ_RHO_NODE` + `RHO_NODE1_MONO_WITH_AZIM` — see the
`-- NEEDS` line inside the body. Already real: the LUNAR premise
(`54cb5660`) and `LOCAL_FAN_CHARACTER_OF_RHO_NODE` (B5 wave). -/
theorem LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, i < V.ncard ∧ w = (rhoNode1_p2 FF)^[i] v ∧
      ((fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i}) ⊆
        affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): the cyclicSet/azimCycle kit.
  -- (1) `FIRST_AZIM_CYCLE_EQ_RHO_NODE` (HOL local_lemmas.hl:1204) needs
  --     `Wrgcvdr_cizmrrh.IDENTIFY_AZIM_CYCLE` (epsilon-characterization of
  --     azim_cycle — unported) plus still-sorried `LOCAL_FAN_IMP_CYCLIC_SET`,
  --     `RHO_NODE_IS_SUCCESEOR_AZIM`, `RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT`.
  -- (2) `RHO_NODE1_MONO_WITH_AZIM` (HOL 4557) needs the same kit through
  --     `SEQUENCE_OF_RHO_NODE_IS_SUC` + `LOFA_IMP_AZIM_RHO_NODE_ST`.
  -- With both: pick i via LOOP_SET_DETER_FIRTS_ELMS (real); HALF_CIRCULAR
  -- (real) puts the arc in P = aff {0,v,ρ v}; RHO_NODE1_MONO + e = v × ρ v
  -- give 0 < azim 0 e v (ρ^[l] v) < azim 0 e v w = π (IN_CONV0_IMP_AZIM_PI,
  -- real); affGt membership via SIN_AZIM_NEG_PI_LT + Fan.th3a kit (real).
  sorry

/-- HOL `LOOP_SET_ITER_CARD_ID` (local_lemmas.hl:4930). -/
theorem LOOP_SET_ITER_CARD_ID {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V) : f^[V.ncard] v = v := by
  obtain ⟨p, hp0, hpx, hdis, -, hcard⟩ := la5_orbit_cycle horb hv
  rw [hcard]
  exact hpx


/-- HOL `LOFA_IMP_ITER_RHO_NODE_ID` (local_lemmas.hl:4991) — filled (orbit
wave 2026-10-08) by `LOOP_SET_ITER_CARD_ID` on the orbit half. -/
theorem LOFA_IMP_ITER_RHO_NODE_ID (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard] v = v :=
  LOOP_SET_ITER_CARD_ID (fun _u hu => LOCAL_FAN_ORBIT_MAP_V h hu) hv


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
    conv0_p2 SS ⊆ (affGt S SS : Set V3) := by
  intro v hv
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := hv
  have hSSfin : SS.Finite := hfin.subset (by simp)
  refine la5_affsign_mono ⟨f, hfin, hvec, hpos, hone⟩ (fun w hw => hw) ?_ (hS.union hSSfin)
  intro w hw
  simp only [Set.mem_union] at hw ⊢
  rcases hw with hw | hw
  · exact absurd hw (Set.notMem_empty w)
  · exact Or.inr hw

/-- HOL `collinear_fan22` (local_lemmas.hl:5011). -/
theorem collinear_fan22 (x v u : V3) :
    Collinear ℝ ({x, v, u} : Set V3) ↔
      u ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∨ x = v :=
  collinear_triple_iff

/-- Lane support (LA5): two affine spans of point pairs generating the same
line coincide. -/
private theorem la5_span_pair_eq {a b x : V3}
    (hx : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3))
    (hb : b ∈ (affineSpan ℝ ({a, x} : Set V3) : Set V3)) :
    affineSpan ℝ ({a, b} : Set V3) = affineSpan ℝ ({a, x} : Set V3) := by
  refine le_antisymm (affineSpan_le.mpr ?_) (affineSpan_le.mpr ?_)
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan _ (by simp)
    · exact hb
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan _ (by simp)
    · exact hx

/-- Lane support (LA5): the affine span of a pair is insensitive to the
order of the pair. -/
private theorem la5_affSpan_pair_comm {a b : V3} :
    affineSpan ℝ ({a, b} : Set V3) = affineSpan ℝ ({b, a} : Set V3) := by
  refine le_antisymm (affineSpan_le.mpr ?_) (affineSpan_le.mpr ?_)
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan _ (by simp)
    · exact mem_affineSpan _ (by simp)
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan _ (by simp)
    · exact mem_affineSpan _ (by simp)

/-- HOL `IN_CONV0_IMP_COLL_IFF` (local_lemmas.hl:5014). -/
theorem IN_CONV0_IMP_COLL_IFF {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    Collinear ℝ ({a, x, v} : Set V3) ↔ Collinear ℝ ({a, b, v} : Set V3) := by
  rw [collinear_triple_iff, collinear_triple_iff]
  by_cases hab : a = b
  · have hxa : x = a := (IN_CONV0_EQ_EQ hx).mpr hab
    subst hab
    subst hxa
    exact Iff.rfl
  · obtain ⟨α, β, hα, hβ, hsum, hxab⟩ := la5_conv02_extract hx
    have hxa : x ≠ a := fun h => hab ((IN_CONV0_EQ_EQ hx).mp h)
    have hxAB : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3) :=
      la5_affComb_mem_affSpan hsum hxab
    have hbx : b ∈ (affineSpan ℝ ({a, x} : Set V3) : Set V3) :=
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
        ⟨1 / β, (la5_conv02_partner hsum hβ.ne' hxab).symm⟩
    have hspan : affineSpan ℝ ({a, b} : Set V3) = affineSpan ℝ ({a, x} : Set V3) :=
      la5_span_pair_eq hxAB hbx
    constructor
    · rintro (hmem | h)
      · refine Or.inl ?_
        rw [hspan]
        exact hmem
      · exact absurd h.symm hxa
    · rintro (hmem | h)
      · refine Or.inl ?_
        rw [← hspan]
        exact hmem
      · exact absurd h hab

/-- HOL `IN_CONV0_IMP_COLL_ENDS_AFF` (local_lemmas.hl:5019). -/
theorem IN_CONV0_IMP_COLL_ENDS_AFF {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    Collinear ℝ ({a, x, v} : Set V3) ↔ Collinear ℝ ({b, x, v} : Set V3) := by
  rw [collinear_triple_iff, collinear_triple_iff]
  by_cases hab : a = b
  · have hxa : x = a := (IN_CONV0_EQ_EQ hx).mpr hab
    subst hab
    subst hxa
    exact Iff.rfl
  · obtain ⟨α, β, hα, hβ, hsum, hxab⟩ := la5_conv02_extract hx
    have hx' : x ∈ conv0_p2 ({b, a} : Set V3) := by rw [la5_conv02_comm]; exact hx
    obtain ⟨γ, δ, hγ, hδ, hsum', hxab'⟩ := la5_conv02_extract hx'
    have hxa : x ≠ a := fun h => hab ((IN_CONV0_EQ_EQ hx).mp h)
    have hxb : x ≠ b := fun h => hab (((IN_CONV0_EQ_EQ hx').mp h).symm)
    have hxAB : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3) :=
      la5_affComb_mem_affSpan hsum hxab
    have hxBA : x ∈ (affineSpan ℝ ({b, a} : Set V3) : Set V3) :=
      la5_affComb_mem_affSpan hsum' hxab'
    have hbx : b ∈ (affineSpan ℝ ({a, x} : Set V3) : Set V3) :=
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
        ⟨1 / β, (la5_conv02_partner hsum hβ.ne' hxab).symm⟩
    have hax : a ∈ (affineSpan ℝ ({b, x} : Set V3) : Set V3) :=
      mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
        ⟨1 / δ, (la5_conv02_partner hsum' hδ.ne' hxab').symm⟩
    have hspanAB : affineSpan ℝ ({a, b} : Set V3) = affineSpan ℝ ({a, x} : Set V3) :=
      la5_span_pair_eq hxAB hbx
    have hspanBA : affineSpan ℝ ({b, a} : Set V3) = affineSpan ℝ ({b, x} : Set V3) :=
      la5_span_pair_eq hxBA hax
    constructor
    · rintro (hmem | h)
      · refine Or.inl ?_
        rw [← hspanBA, ← la5_affSpan_pair_comm, hspanAB]
        exact hmem
      · exact absurd h.symm hxa
    · rintro (hmem | h)
      · refine Or.inl ?_
        rw [← hspanAB, la5_affSpan_pair_comm, hspanBA]
        exact hmem
      · exact absurd h.symm hxb

/-- HOL `IN_CONV0_IMP_AZIM_PI` (local_lemmas.hl:5031). -/
theorem IN_CONV0_IMP_AZIM_PI {x a b e : V3} (hcol : ¬ Collinear ℝ ({x, a, e} : Set V3))
    (hx : x ∈ conv0_p2 ({a, b} : Set V3)) : azim x e a b = Real.pi := by
  obtain ⟨α, β, hα, hβ, hsum, hxab⟩ := la5_conv02_extract hx
  have hβ0 : β ≠ 0 := hβ.ne'
  have hsum'' : (α + β) • b = (1:ℝ) • b := by rw [hsum, one_smul]
  have hex : e ≠ x := by
    intro h
    apply hcol
    refine collinear_triple_iff.mpr (Or.inl ?_)
    rw [h]
    exact mem_affineSpan _ (by simp)
  have hset1 : ({x, e, a} : Set V3) = {x, a, e} := by ext w; simp; tauto
  have h1 : ¬ Collinear3 x e a := fun hc => hcol (by rw [← hset1]; exact hc)
  have hse : ({a, x, e} : Set V3) = {x, a, e} := by ext w; simp; tauto
  have hcol' : ¬ Collinear ℝ ({a, x, e} : Set V3) := fun hc => hcol (by rw [← hse]; exact hc)
  have hset2 : ({x, e, b} : Set V3) = {b, x, e} := by ext w; simp; tauto
  have h2 : ¬ Collinear ℝ ({x, e, b} : Set V3) := by
    intro hc
    rw [hset2] at hc
    exact hcol' ((IN_CONV0_IMP_COLL_ENDS_AFF hx).mpr hc)
  have e0 : (1:ℝ) - α = β := by linarith
  have hxa' : (x - a : V3) = β • (b - a) := by
    rw [hxab, ← e0]
    module
  have hbx : α • (b - a) = b - x := by
    linear_combination (norm := module) hxab + hsum''
  have hbx2 : b - x = (α / β) • (x - a) := by
    rw [← hbx, hxa', smul_smul, div_mul_cancel₀ _ hβ0]
  have hsub : (b - x) = -(α / β) • (a - x) := by
    rw [hbx2]
    module
  obtain ⟨θ, hspec⟩ := azimSpec_exists h1 h2
  have hazim : azim x e a b = θ := azim_eq_of_spec h1 h2 hspec
  have myspec : AzimSpec x e a b Real.pi := by
    refine ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos],
      ((a - x : V3) ⬝ᵥ (e - x)) / (dist e x) ^ 2,
      ((b - x : V3) ⬝ᵥ (e - x)) / (dist e x) ^ 2, ?_⟩
    intro e1 e2 e3 hon hax hex
    have hd : 0 < dist e x := dist_pos.mpr hex
    have hzA : zOf e1 e2 (a - x) ≠ 0 := (zOf_ne_zero_iff hon hax hex a).mpr h1
    set A := zOf e1 e2 (a - x) with hA
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hzA
    have hnA : A = ‖A‖ * Complex.exp (Complex.arg A * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I A).symm
    have hdecA := rep_of_zOf hon hax hex a (Complex.arg A) ‖A‖ hnA
    have hdecA2 : (α / β) • (a - x)
        = ((α / β) * (‖A‖ * Real.cos (Complex.arg A))) • e1
          + ((α / β) * (‖A‖ * Real.sin (Complex.arg A))) • e2
          + ((α / β) * (((a - x : V3) ⬝ᵥ e3) / dist e x)) • (e - x) := by
      nth_rewrite 1 [hdecA]
      rw [smul_add, smul_smul, smul_add, smul_smul, smul_smul]
    have hco3 : ∀ y : V3, ((y - x : V3) ⬝ᵥ (e - x)) = dist e x * ((y - x : V3) ⬝ᵥ e3) := by
      intro y
      have q1 : ((y - x : V3) ⬝ᵥ (e - x)) = inner ℝ (y - x) (e - x) :=
        (inner_eq_dot (y - x) (e - x)).symm
      have q2 : inner ℝ (e - x) (y - x) = dist e x * inner ℝ e3 (y - x) := by
        rw [hax, real_inner_smul_left]
      have q3 : inner ℝ e3 (y - x) = inner ℝ (y - x) e3 := by rw [real_inner_comm]
      have q4 : ((y - x : V3) ⬝ᵥ e3) = inner ℝ (y - x) e3 :=
        (inner_eq_dot (y - x) e3).symm
      rw [q1, real_inner_comm, q2, q3, ← q4]
    have hc3a : ((a - x : V3) ⬝ᵥ (e - x)) / (dist e x) ^ 2
        = ((a - x : V3) ⬝ᵥ e3) / dist e x := by
      rw [hco3 a]
      field_simp
    have hc3b : ((b - x : V3) ⬝ᵥ (e - x)) / (dist e x) ^ 2
        = ((b - x : V3) ⬝ᵥ e3) / dist e x := by
      rw [hco3 b]
      field_simp
    have hkab : ((b - x : V3) ⬝ᵥ e3) = -(α / β) * ((a - x : V3) ⬝ᵥ e3) := by
      rw [hsub, ← inner_eq_dot, real_inner_smul_left, ← inner_eq_dot]
    refine ⟨Complex.arg A, ‖A‖, (α / β) * ‖A‖, ?_, ?_, hApos,
      mul_pos (div_pos hα hβ) hApos⟩
    · rw [hc3a]
      exact rep_of_zOf hon hax hex a (Complex.arg A) ‖A‖ hnA
    · rw [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi, hc3b, hkab]
      linear_combination (norm := module) hbx2 - hdecA2
  rw [hazim]
  exact azimSpec_unique hex hspec myspec

/-- HOL `AFF_GT_MONO` (local_lemmas.hl:5064). -/
theorem AFF_GT_MONO {X Y S : Set V3} (hS : S ⊆ Y) :
    affGt X Y ⊆ affGt (X ∪ S) (Y \ S) := by
  intro v hv
  refine la5_affsign_mono hv (fun w hw => hw.1) ?_ ?_
  · intro w hw
    simp only [Set.mem_union] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (Or.inl hw)
    · by_cases hws : w ∈ S
      · exact Or.inl (Or.inr hws)
      · exact Or.inr ⟨hw, hws⟩
  · obtain ⟨f, hfin, hvec, hpos, hone⟩ := hv
    have hXfin : X.Finite := hfin.subset (fun w hw => Or.inl hw)
    have hYfin : Y.Finite := hfin.subset (fun w hw => Or.inr hw)
    have hSfin : S.Finite := hYfin.subset hS
    exact (hXfin.union hSfin).union (hYfin.subset (fun w hw => hw.1))

/-- HOL `AFF_GT_SUB_AFF_UNION` (local_lemmas.hl:5076). -/
theorem AFF_GT_SUB_AFF_UNION (X Y : Set V3) :
    affGt X Y ⊆ (affineSpan ℝ (X ∪ Y) : Set V3) := by
  intro v hv
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := hv
  have hsum1 : ∑ w ∈ hfin.toFinset.attach, f (w : V3) = 1 := by
    rw [Finset.sum_attach]; exact hone
  have hAC : (hfin.toFinset.attach).affineCombination ℝ
      (fun w : ↥(hfin.toFinset) => (w : V3)) (fun w => f (w : V3))
      = ∑ w ∈ hfin.toFinset, f w • w := by
    rw [hfin.toFinset.attach.affineCombination_eq_linear_combination
      (p := fun w : ↥(hfin.toFinset) => (w : V3)) (w := fun w => f (w : V3)) hsum1]
    exact Finset.sum_attach (s := hfin.toFinset) (f := fun w : V3 => f w • w)
  have hmem : (hfin.toFinset.attach).affineCombination ℝ
      (fun w : ↥(hfin.toFinset) => (w : V3)) (fun w => f (w : V3))
      ∈ affineSpan ℝ (Set.range (fun w : ↥(hfin.toFinset) => (w : V3))) :=
    affineCombination_mem_affineSpan hsum1 (fun w : ↥(hfin.toFinset) => (w : V3))
  rw [Subtype.range_coe_subtype] at hmem
  have hset : ({x | x ∈ hfin.toFinset} : Set V3) = (X ∪ Y : Set V3) := hfin.coe_toFinset
  rw [hset] at hmem
  rw [hvec, ← hAC]
  exact hmem

/-- HOL `SIN_AZIM_NEG_PI_LT` (local_lemmas.hl:5085). -/
theorem SIN_AZIM_NEG_PI_LT (x y u v : V3) :
    Real.sin (azim x y u v) < 0 ↔ Real.pi < azim x y u v := by
  have hrange := azim_nonneg x y u v
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have h0 : (0:ℝ) ≤ Real.sin (azim x y u v) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hrange hcon
    exact lt_irrefl _ (lt_of_lt_of_le h h0)
  · intro h
    have h2 := azim_lt_two_pi x y u v
    have h3 : Real.sin (azim x y u v - Real.pi) > 0 :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have h4 : Real.sin (azim x y u v) = -Real.sin (azim x y u v - Real.pi) := by
      rw [Real.sin_sub]
      simp [Real.cos_pi, Real.sin_pi]
    linarith

/-- HOL `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT` (local_lemmas.hl:5105).
NEEDS (orbit wave 2026-10-08): `LOFA_IMP_ITER_RHO_NODE_ID` is now real
(WRGCVDR orbit half). Remaining blocker =
`LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` (see its NEEDS);
`LOCAL_FAN_CHARACTER_OF_RHO_NODE2` was purified by the B5 wave. -/
theorem NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, w = (rhoNode1_p2 FF)^[i] v ∧ i + 1 < V.ncard ∧
      ¬((rhoNode1_p2 FF)^[i + 1] v ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3)) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): `LOFA_IMP_ITER_RHO_NODE_ID` is
  -- real, so the only blocker left is `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT`
  -- (i + 1 < CARD V from its i < CARD V plus i ≠ CARD V - 1: rho w = v would
  -- collapse ¬collinear {0,w,ρ w} onto ¬collinear {0,v,ρ v} — see HOL 5105;
  -- the final exclusion reuses the GT-side membership just proven).
  sorry

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
    (hl : lunar_p2 v w V E) : ¬ Collinear ℝ ({0, v, rhoNode1_p2 FF w} : Set V3) := by
  -- B5 free-cascade wave: the HOL route (local_lemmas.hl:5265, first tactic
  -- `NHANH LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI`) — blocked only by LUNAR's
  -- placeholder era; all inputs are real since `54cb5660` (LUNAR) and the
  -- B5 fill of LOCAL_FAN_CHARACTER_OF_RHO_NODE.
  have h0c : (0:V3) ∈ conv0_p2 ({v, w} : Set V3) := (LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI h hl).1
  obtain ⟨-, hvw, hvw2, -⟩ := hl
  obtain ⟨hlo, hFAN0⟩ := CVLF_LF_F h
  have h0V : (0:V3) ∉ V := hFAN0.2.2.2.1
  have hvV : v ∈ V := hvw (by simp)
  have hwV : w ∈ V := hvw (by simp)
  have h0cwv : (0:V3) ∈ conv0_p2 ({w, v} : Set V3) := by
    rw [show ({w, v} : Set V3) = {v, w} by ext z; simp; tauto]
    exact h0c
  have s1 : ({0, v} : Set V3) = {v, 0} := by ext z; simp; tauto
  have s3 : ({v, w} : Set V3) = {w, v} := by ext z; simp; tauto
  have s5 : ({w, 0} : Set V3) = {0, w} := by ext z; simp; tauto
  have e1 : (affineSpan ℝ ({0, v} : Set V3) : Set V3)
      = (affineSpan ℝ ({v, 0} : Set V3) : Set V3) := by rw [s1]
  have e2 : (affineSpan ℝ ({v, 0} : Set V3) : Set V3)
      = (affineSpan ℝ ({v, w} : Set V3) : Set V3) := (IN_CONV0_IMP_AFF_EQ h0c).symm
  have e3 : (affineSpan ℝ ({v, w} : Set V3) : Set V3)
      = (affineSpan ℝ ({w, v} : Set V3) : Set V3) := by rw [s3]
  have e4 : (affineSpan ℝ ({w, v} : Set V3) : Set V3)
      = (affineSpan ℝ ({w, 0} : Set V3) : Set V3) := IN_CONV0_IMP_AFF_EQ h0cwv
  have e5 : (affineSpan ℝ ({w, 0} : Set V3) : Set V3)
      = (affineSpan ℝ ({0, w} : Set V3) : Set V3) := by rw [s5]
  have hEq : (affineSpan ℝ ({0, v} : Set V3) : Set V3)
      = (affineSpan ℝ ({0, w} : Set V3) : Set V3) :=
    e1.trans (e2.trans (e3.trans (e4.trans e5)))
  rw [collinear_fan22]
  intro hcon
  rcases hcon with hrin | h0v
  · exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlo hwV
      ((collinear_fan22 0 w (rhoNode1_p2 FF w)).mpr
        (Or.inl (by rw [← hEq]; exact hrin)))
  · exact h0V (by rw [h0v]; exact hvV)

/-- HOL `NOT_INTERSECTION_BWT_AFF_GTS` (local_lemmas.hl:5295).  NEEDS
(B5 audit 2026-10-10): `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT` (orbit side);
`NOT_COLL_RHONODE_SND_POINT` (closed by the B5 wave),
`LOCAL_FAN_CHARACTER_OF_RHO_NODE2` (purified), HOL `Fan.th3a`
(≈ `sum4_azim_fan` kit, available). -/
theorem NOT_INTERSECTION_BWT_AFF_GTS (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    affGt ({0, v} : Set V3) ({rhoNode1_p2 FF w} : Set V3) ∩
      affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) = ∅ := by
  -- NEEDS (LA5 downstream wave 2026-10-08): only `NEXT_OPOSITE_POINT_IS_NOT_
  -- IN_AFF_GT` remains (itself blocked by the cyclicSet kit — see its
  -- -- NEEDS). Everything else on the HOL route (5295) is real:
  -- `NOT_COLL_RHONODE_SND_POINT`/`LOCAL_FAN_CHARACTER_OF_RHO_NODE2`
  -- (B5 wave) give the pair distinctness for la5_affGt212_extract/intro;
  -- `FOR_AFF_GT_NOT_INTERSECTION` (real) turns a common point x into
  -- ρ w = combo of {0, v, ρ v} with positive ρ v-coefficient, contradicting
  -- NEXT_OPOSITE at i + 1 (ρ w = ρ^[i+1] v via iterate_succ_apply').
  sorry

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

/-- Lane support (LA5): enlarging the free support of an `Affsign` witness by
one point carrying coefficient zero preserves the witness. -/
private theorem la5_affsign_insert {sgn : ℝ → Prop} {s t : Set V3} {p q : V3}
    (h : Affsign sgn s t p) : Affsign sgn (insert q s) t p := by
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := h
  have hfin2 : ((insert q s ∪ t : Set V3)).Finite := by
    rw [Set.insert_union]
    exact hfin.insert q
  have hT2 : hfin2.toFinset = insert q hfin.toFinset := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_union,
      Finset.mem_insert]
    tauto
  by_cases hq : q ∈ s ∪ t
  · refine ⟨f, hfin2, ?_, hpos, ?_⟩
    · rw [hT2, Finset.insert_eq_of_mem (hfin.mem_toFinset.mpr hq)]
      exact hvec
    · rw [hT2, Finset.insert_eq_of_mem (hfin.mem_toFinset.mpr hq)]
      exact hone
  · have hpoint : ∀ w ∈ hfin.toFinset, (if w = q then (0:ℝ) else f w) = f w := by
      intro w hw
      have hwq : w ≠ q := fun he => hq (by rw [← he]; exact hfin.mem_toFinset.mp hw)
      rw [if_neg hwq]
    have hqT : q ∉ hfin.toFinset := hfin.mem_toFinset.not.mpr hq
    refine ⟨fun w => if w = q then (0:ℝ) else f w, hfin2, ?_, ?_, ?_⟩
    · rw [hT2, Finset.sum_insert hqT]
      show p = (if q = q then (0:ℝ) else f q) • q
        + ∑ w ∈ hfin.toFinset, (if w = q then (0:ℝ) else f w) • w
      rw [if_pos (rfl : q = q), zero_smul, zero_add]
      have hcong : ∑ w ∈ hfin.toFinset, (if w = q then (0:ℝ) else f w) • w
          = ∑ w ∈ hfin.toFinset, f w • w :=
        Finset.sum_congr rfl (fun w hw => by
          show (if w = q then (0:ℝ) else f w) • w = f w • w
          rw [hpoint w hw])
      rw [hcong]
      exact hvec
    · intro w hw
      have hwq : w ≠ q := fun he => hq (Or.inr (by rw [← he]; exact hw))
      show sgn (if w = q then (0:ℝ) else f w)
      rw [if_neg hwq]
      exact hpos w hw
    · rw [hT2, Finset.sum_insert hqT]
      show (if q = q then (0:ℝ) else f q)
        + ∑ w ∈ hfin.toFinset, (if w = q then (0:ℝ) else f w) = 1
      rw [if_pos (rfl : q = q), zero_add]
      refine Eq.trans (Finset.sum_congr rfl (fun w hw => ?_)) hone
      show (if w = q then (0:ℝ) else f w) = f w
      rw [hpoint w hw]


/-- HOL `CONV0_AFF_GT_EQ` (local_lemmas.hl:5328). -/
theorem CONV0_AFF_GT_EQ {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3))
    (hcol : ¬ Collinear ℝ ({a, x, v} : Set V3)) :
    affGt ({x, a} : Set V3) ({v} : Set V3) =
      affGt ({x, a, b} : Set V3) ({v} : Set V3) := by
  have hset : ({x, a, b} : Set V3) = insert b ({x, a} : Set V3) := by
    ext w; simp; tauto
  rw [hset]
  ext u
  constructor
  · intro hu
    exact la5_affsign_insert hu
  · intro hu
    by_cases hbx : b = x
    · rw [hbx, Set.insert_eq_of_mem (by simp : x ∈ ({x, a} : Set V3))] at hu
      exact hu
    · by_cases hba : b = a
      · rw [hba, Set.insert_eq_of_mem (by simp : a ∈ ({x, a} : Set V3))] at hu
        exact hu
      · -- main case: b is distinct from x and a
        obtain ⟨α, β, hα, hβ, hsum, hxab⟩ := la5_conv02_extract hx
        have hβ0 : β ≠ 0 := hβ.ne'
        have hbdec : b = (1 / β) • x + (-(α / β)) • a := by
          have e1 : (1 / β) • (α • a) = (α / β) • a := by rw [smul_smul]; field_simp
          have e2 : (-(α / β)) • a = -((α / β) • a) := by rw [neg_smul]
          rw [hxab, smul_add, e1, e2, smul_smul, div_mul_cancel₀ _ hβ0, one_smul]
          abel
        have hxa : x ≠ a := fun h => hcol (collinear_triple_iff.mpr (Or.inr h.symm))
        have hxv : x ≠ v := fun h => hcol (collinear_triple_iff.mpr (Or.inl
          (by rw [← h]; exact mem_affineSpan _ (by simp))))
        have hav : a ≠ v := fun h => hcol (collinear_triple_iff.mpr (Or.inl
          (by rw [← h]; exact mem_affineSpan _ (by simp))))
        have hsum2 : -(α / β) + 1 / β = 1 := by
          have e : -(α / β) + 1 / β = (1 - α) / β := by ring
          rw [e]
          have h1f : 1 - α = β := by linarith
          rw [h1f, div_self hβ0]
        have hbv : b ≠ v := by
          intro h
          apply hcol
          refine collinear_triple_iff.mpr (Or.inl ?_)
          have hdec : v = (-(α / β)) • a + (1 / β) • x := by
            rw [← h, hbdec]; abel
          exact la5_affComb_mem_affSpan hsum2 hdec
        obtain ⟨f, hfin, hvec, hpos, hone⟩ := hu
        have hT1 : hfin.toFinset = ({x, a, b, v} : Finset V3) := by
          ext w
          simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_union,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hfin2 : ((({x, a} : Set V3) ∪ {v}) : Set V3).Finite := by simp
        have hT2 : hfin2.toFinset = ({x, a, v} : Finset V3) := by
          ext w
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hT1] at hvec hone
        simp only [Finset.sum_insert (by simp [hxa, Ne.symm hbx, hxv] : ¬(x ∈ ({a, b, v} : Finset V3))),
          Finset.sum_insert (by simp [Ne.symm hba, hav] : ¬(a ∈ ({b, v} : Finset V3))),
          Finset.sum_insert (by simp [hbv] : ¬(b ∈ ({v} : Finset V3))),
          Finset.sum_singleton] at hvec hone
        -- hvec : u = f x • x + f a • a + f b • b + f v • v
        -- hone : f x + f a + f b + f v = 1
        set g : V3 → ℝ := fun w => if w = x then f w + f b / β
          else if w = a then f w + -(f b * α / β) else f w with hgdef
        have gx : g x = f x + f b / β := by
          simp only [hgdef, reduceIte]
        have ga : g a = f a + -(f b * α / β) := by
          simp only [hgdef, if_neg (Ne.symm hxa), reduceIte]
        have gv : g v = f v := by
          simp only [hgdef, if_neg (Ne.symm hxv), if_neg (Ne.symm hav), reduceIte]
        have key : ∀ r : ℝ, r • b = (r / β) • x + (-(r * α / β)) • a := by
          intro r
          rw [hbdec, smul_add, smul_smul, smul_smul]
          have e1 : r * (1 / β) = r / β := by field_simp
          have e2 : r * (-(α / β)) = -(r * α / β) := by field_simp
          rw [e1, e2]
        refine ⟨g, hfin2, ?_, ?_, ?_⟩
        · rw [hT2, Finset.sum_insert (by simp [hxa, hxv] : ¬(x ∈ ({a, v} : Finset V3))),
            Finset.sum_insert (by simp [hav] : ¬(a ∈ ({v} : Finset V3))),
            Finset.sum_singleton, gx, ga, gv, hvec, key (f b)]
          module
        · intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst hz
          rw [gv]
          exact hpos z (by simp)
        · rw [hT2, Finset.sum_insert (by simp [hxa, hxv] : ¬(x ∈ ({a, v} : Finset V3))),
            Finset.sum_insert (by simp [hav] : ¬(a ∈ ({v} : Finset V3))),
            Finset.sum_singleton, gx, ga, gv]
          have hdiv : f b / β + -(f b * α / β) = f b := by
            have e : f b / β + -(f b * α / β) = f b * (1 - α) / β := by ring
            rw [e]
            have h1f : 1 - α = β := by linarith
            rw [h1f, mul_div_cancel_right₀ _ hβ0]
          linarith


/-- HOL `AFF_GT_SAME_WITH_ENDS` (local_lemmas.hl:5375). -/
theorem AFF_GT_SAME_WITH_ENDS (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E) :
    affGt ({0, v} : Set V3) ({rhoNode1_p2 FF w} : Set V3) =
      affGt ({0, w} : Set V3) ({rhoNode1_p2 FF w} : Set V3) := by
  -- B5 free-cascade wave: HOL route = LUNAR + NOT_COLL_RHONODE_SND_POINT
  -- (both sides of the 0 ∈ conv0 {v,w} coin, closed this wave) +
  -- LOCAL_FAN_CHARACTER_OF_RHO_NODE2 (purified this wave) + the proven
  -- CONV0_AFF_GT_EQ; only set-literal swaps remain.
  have h0c : (0:V3) ∈ conv0_p2 ({v, w} : Set V3) := (LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI h hl).1
  have h0cwv : (0:V3) ∈ conv0_p2 ({w, v} : Set V3) := by
    rw [show ({w, v} : Set V3) = {v, w} by ext z; simp; tauto]
    exact h0c
  obtain ⟨hlo, -⟩ := CVLF_LF_F h
  have hnc1 : ¬ Collinear ℝ ({v, (0:V3), rhoNode1_p2 FF w} : Set V3) := by
    rw [show ({v, (0:V3), rhoNode1_p2 FF w} : Set V3) = {0, v, rhoNode1_p2 FF w} by
      ext z; simp; tauto]
    exact NOT_COLL_RHONODE_SND_POINT h hl
  obtain ⟨-, hvw, -, -⟩ := hl
  have hwV : w ∈ V := hvw (by simp)
  have hnc2 : ¬ Collinear ℝ ({w, (0:V3), rhoNode1_p2 FF w} : Set V3) := by
    rw [show ({w, (0:V3), rhoNode1_p2 FF w} : Set V3) = {0, w, rhoNode1_p2 FF w} by
      ext z; simp; tauto]
    exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlo hwV
  have e_a : affGt ({(0:V3), v} : Set V3) ({rhoNode1_p2 FF w} : Set V3)
      = affGt ({(0:V3), v, w} : Set V3) ({rhoNode1_p2 FF w} : Set V3) :=
    CONV0_AFF_GT_EQ h0c hnc1
  have e_b : affGt ({(0:V3), w} : Set V3) ({rhoNode1_p2 FF w} : Set V3)
      = affGt ({(0:V3), w, v} : Set V3) ({rhoNode1_p2 FF w} : Set V3) :=
    CONV0_AFF_GT_EQ h0cwv hnc2
  have e_mid : affGt ({(0:V3), v, w} : Set V3) ({rhoNode1_p2 FF w} : Set V3)
      = affGt ({(0:V3), w, v} : Set V3) ({rhoNode1_p2 FF w} : Set V3) := by
    rw [show ({(0:V3), v, w} : Set V3) = ({0, w, v} : Set V3) by
      ext z; simp; tauto]
  exact e_a.trans (e_mid.trans e_b.symm)

/-- Lane support (LA5): an affine combination of three points of an affine
subspace stays in the subspace. -/
private theorem la5_affComb3_in_span {t a b c : V3} {α β γ : ℝ} (hsum : α + β + γ = 1)
    (ht : t = α • a + β • b + γ • c) {S : AffineSubspace ℝ V3}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : t ∈ S := by
  have hdir : (t -ᵥ c : V3) ∈ S.direction := by
    have h1 : (t -ᵥ c : V3) = α • (a -ᵥ c) + β • (b -ᵥ c) := by
      have hγ : γ = 1 - α - β := by linarith
      rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, ht, hγ, sub_smul, sub_smul, one_smul]
      module
    rw [vsub_eq_sub] at h1 ⊢
    have hac : (a - c : V3) ∈ S.direction := AffineSubspace.vsub_mem_direction ha hc
    have hbc : (b - c : V3) ∈ S.direction := AffineSubspace.vsub_mem_direction hb hc
    rw [h1]
    exact S.direction.add_mem (S.direction.smul_mem α hac) (S.direction.smul_mem β hbc)
  have h2 : (t -ᵥ c : V3) +ᵥ c ∈ S := AffineSubspace.vadd_mem_of_mem_direction hdir hc
  have h3 : (t -ᵥ c : V3) +ᵥ c = t := by rw [vadd_eq_add, vsub_eq_sub, sub_add_cancel]
  rw [← h3]
  exact h2

/-- Lane support (LA5): an affine combination of three points lies in their
affine span. -/
private theorem la5_affComb3_mem_affSpan {a b c t : V3} {α β γ : ℝ} (hsum : α + β + γ = 1)
    (ht : t = α • a + β • b + γ • c) :
    t ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) :=
  la5_affComb3_in_span hsum ht (mem_affineSpan _ (by simp)) (mem_affineSpan _ (by simp))
    (mem_affineSpan _ (by simp))

/-- Lane support (LA5): solve for the "carrier" point in a three-point
affine decomposition. -/
private theorem la5_smul_div_solve {b c w z : V3} {gx gy gw : ℝ} (hgw : gw ≠ 0)
    (hvec : z = gx • b + gy • c + gw • w) :
    w = (1 / gw) • z - (gx / gw) • b - (gy / gw) • c := by
  rw [hvec, smul_add, smul_add]
  have e1 : (1 / gw) • (gx • b) = (gx / gw) • b := by rw [smul_smul]; field_simp
  have e2 : (1 / gw) • (gy • c) = (gy / gw) • c := by rw [smul_smul]; field_simp
  rw [e1, e2, smul_smul, div_mul_cancel₀ _ hgw, one_smul]
  abel

/-- Lane support (LA5): extract explicit coefficients from a membership in
`affGt {x, y} {z}`. -/
private theorem la5_affGt212_extract {x y z u : V3}
    (hu : u ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    ∃ gx gy gz : ℝ, 0 < gz ∧ gx + gy + gz = 1 ∧ u = gx • x + gy • y + gz • z := by
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := hu
  have hposz : 0 < f z := hpos z (by simp)
  by_cases hxy : x = y
  · subst hxy
    by_cases hxz : x = z
    · subst hxz
      have hEq : hfin.toFinset = ({x} : Finset V3) := by
        ext w
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hEq] at hvec hone
      simp only [Finset.sum_singleton] at hvec hone
      exact ⟨0, 0, f x, hposz, by linarith,
        by rw [zero_smul, zero_add, zero_add]; exact hvec⟩
    · have hEq : hfin.toFinset = ({x, z} : Finset V3) := by
        ext w
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hEq] at hvec hone
      simp only [Finset.sum_insert (by simp [hxz] : ¬(x ∈ ({z} : Finset V3))),
        Finset.sum_singleton] at hvec hone
      refine ⟨f x, 0, f z, hposz, by linarith, ?_⟩
      rw [zero_smul, add_zero]
      exact hvec
  · by_cases hxz : x = z
    · subst hxz
      have hEq : hfin.toFinset = ({x, y} : Finset V3) := by
        ext w
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hEq] at hvec hone
      simp only [Finset.sum_insert (by simp [hxy] : ¬(x ∈ ({y} : Finset V3))),
        Finset.sum_singleton] at hvec hone
      refine ⟨0, f y, f x, hposz, by linarith, ?_⟩
      rw [hvec, zero_smul, zero_add]
      abel
    · by_cases hyz : y = z
      · subst hyz
        have hEq : hfin.toFinset = ({x, y} : Finset V3) := by
          ext w
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hEq] at hvec hone
        simp only [Finset.sum_insert (by simp [hxy] : ¬(x ∈ ({y} : Finset V3))),
          Finset.sum_singleton] at hvec hone
        refine ⟨f x, 0, f y, hposz, by linarith, ?_⟩
        rw [zero_smul, add_zero]
        exact hvec
      · have hfin2 : ((({x} ∪ {y, z} : Set V3)) : Set V3).Finite := by simp
        have hEq : hfin.toFinset = hfin2.toFinset := by
          ext w
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hEq] at hvec hone
        rw [sum_insert_pair_v hfin2 hxy hxz hyz] at hvec
        rw [sum_insert_pair_s hfin2 hxy hxz hyz] at hone
        exact ⟨f x, f y, f z, hposz, by linarith, hvec⟩

/-- Lane support (LA5): build a membership in `affGt {x, y} {z}` from
explicit coefficients (pair support assumed distinct). -/
private theorem la5_affGt212_intro {x y z u : V3} {gx gy gz : ℝ} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hgz : 0 < gz) (hsum : gx + gy + gz = 1)
    (hu : u = gx • x + gy • y + gz • z) :
    u ∈ affGt ({x, y} : Set V3) ({z} : Set V3) := by
  have hfin : ((({x, y} ∪ {z}) : Set V3) : Set V3).Finite := by simp
  have hEq : hfin.toFinset = ({x, y, z} : Finset V3) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨fun w => if w = x then gx else if w = y then gy else gz, hfin, ?_, ?_, ?_⟩
  · rw [hEq, Finset.sum_insert (by simp [hxy, hxz] : ¬(x ∈ ({y, z} : Finset V3))),
      Finset.sum_insert (by simp [hyz] : ¬(y ∈ ({z} : Finset V3))), Finset.sum_singleton]
    simp only [if_pos rfl, if_neg hxy, if_neg hxz, if_neg hyz,
      if_neg (Ne.symm hxy), if_neg (Ne.symm hxz), if_neg (Ne.symm hyz), if_true, if_false]
    rw [hu, add_assoc]
  · intro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simp only [if_pos rfl, if_neg (Ne.symm hxz), if_neg (Ne.symm hyz)]
    exact hgz
  · rw [hEq, Finset.sum_insert (by simp [hxy, hxz] : ¬(x ∈ ({y, z} : Finset V3))),
      Finset.sum_insert (by simp [hyz] : ¬(y ∈ ({z} : Finset V3))), Finset.sum_singleton]
    simp only [if_pos rfl, if_neg hxy, if_neg hxz, if_neg hyz,
      if_neg (Ne.symm hxy), if_neg (Ne.symm hxz), if_neg (Ne.symm hyz), if_true, if_false]
    rw [← hsum, add_assoc]

/-- HOL `USEFULL_THHM` (local_lemmas.hl:5402). -/
theorem USEFULL_THHM {b c z w : V3} (h1 : z ∈ affineSpan ℝ ({b, c} : Set V3))
    (h2 : z ∈ affGt ({b, c} : Set V3) ({w} : Set V3)) :
    w ∈ affineSpan ℝ ({b, c} : Set V3) := by
  by_cases hw : w = b
  · rw [hw]; exact mem_affineSpan _ (by simp)
  by_cases hw2 : w = c
  · rw [hw2]; exact mem_affineSpan _ (by simp)
  obtain ⟨gx, gy, gw, hgw, hsum, hvec⟩ := la5_affGt212_extract h2
  have hgw0 : gw ≠ 0 := hgw.ne'
  have hw'' : w = (1 / gw) • z + (-(gx / gw)) • b + (-(gy / gw)) • c := by
    have e1 : (1 / gw) • (gx • b) = (gx / gw) • b := by rw [smul_smul]; field_simp
    have e2 : (1 / gw) • (gy • c) = (gy / gw) • c := by rw [smul_smul]; field_simp
    have e3 : (-(gx / gw)) • b = -((gx / gw) • b) := by rw [neg_smul]
    have e4 : (-(gy / gw)) • c = -((gy / gw) • c) := by rw [neg_smul]
    rw [hvec, smul_add, smul_add, e1, e2, e3, e4, smul_smul, div_mul_cancel₀ _ hgw0,
      one_smul]
    abel
  refine la5_affComb3_in_span ?_ hw'' h1 (mem_affineSpan _ (by simp))
    (mem_affineSpan _ (by simp))
  field_simp
  linarith

/-- HOL `COLL_IN_AFF_GT_TOO` (local_lemmas.hl:5427). -/
theorem COLL_IN_AFF_GT_TOO {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    ¬ Collinear ℝ ({x, y, a} : Set V3) := by
  intro hcol2
  obtain ⟨fx, fy, fz, hfz, hf, hfa⟩ := la5_affGt212_extract ha
  rcases collinear_triple_iff.mp hcol2 with hmem | hxy
  · have hfz0 : fz ≠ 0 := hfz.ne'
    have hz'' : z = (1 / fz) • a + (-(fx / fz)) • x + (-(fy / fz)) • y := by
      have e1 : (1 / fz) • (fx • x) = (fx / fz) • x := by rw [smul_smul]; field_simp
      have e2 : (1 / fz) • (fy • y) = (fy / fz) • y := by rw [smul_smul]; field_simp
      have e3 : (-(fx / fz)) • x = -((fx / fz) • x) := by rw [neg_smul]
      have e4 : (-(fy / fz)) • y = -((fy / fz) • y) := by rw [neg_smul]
      rw [hfa, smul_add, smul_add, e1, e2, e3, e4, smul_smul, div_mul_cancel₀ _ hfz0,
        one_smul]
      abel
    have hzmem : z ∈ (affineSpan ℝ ({x, y} : Set V3) : Set V3) :=
      la5_affComb3_in_span (by field_simp; linarith) hz'' hmem
        (mem_affineSpan _ (by simp)) (mem_affineSpan _ (by simp))
    exact hcol (collinear_triple_iff.mpr (Or.inl hzmem))
  · exact hcol (collinear_triple_iff.mpr (Or.inr hxy))

/-- HOL `AFF_GT_IN_IMP_SUBSET` (local_lemmas.hl:5435). -/
theorem AFF_GT_IN_IMP_SUBSET {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    affGt ({x, y} : Set V3) ({a} : Set V3) ⊆ affGt ({x, y} : Set V3) ({z} : Set V3) := by
  have hxy : x ≠ y := fun h => hcol (collinear_triple_iff.mpr (Or.inr h))
  have hxz : x ≠ z := fun h => hcol (collinear_triple_iff.mpr (Or.inl
    (by rw [← h]; exact mem_affineSpan _ (by simp))))
  have hyz : y ≠ z := fun h => hcol (collinear_triple_iff.mpr (Or.inl
    (by rw [← h]; exact mem_affineSpan _ (by simp))))
  intro u hu
  obtain ⟨fx, fy, fz, hfz, hf, hfa⟩ := la5_affGt212_extract ha
  obtain ⟨gx, gy, ga, hga, hg, hua⟩ := la5_affGt212_extract hu
  have hd : ga * fx + (ga * fy + ga * fz) = ga := by
    rw [← mul_add, ← mul_add, ← add_assoc, hf, mul_one]
  have hsum' : gx + ga * fx + (gy + ga * fy) + ga * fz = 1 := by linarith
  have hu' : u = (gx + ga * fx) • x + (gy + ga * fy) • y + (ga * fz) • z := by
    rw [hua, hfa]
    module
  exact la5_affGt212_intro hxy hxz hyz (mul_pos hga hfz) hsum' hu'

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
    z ∈ affGt ({x, y} : Set V3) ({a} : Set V3) := by
  have hxy : x ≠ y := fun h => hcol (collinear_triple_iff.mpr (Or.inr h))
  have hxz : x ≠ z := fun h => hcol (collinear_triple_iff.mpr (Or.inl
    (by rw [← h]; exact mem_affineSpan _ (by simp))))
  have hyz : y ≠ z := fun h => hcol (collinear_triple_iff.mpr (Or.inl
    (by rw [← h]; exact mem_affineSpan _ (by simp))))
  obtain ⟨fx, fy, fz, hfz, hf, hfa⟩ := la5_affGt212_extract ha
  have hfz0 : fz ≠ 0 := hfz.ne'
  have hz'' : z = (1 / fz) • a + (-(fx / fz)) • x + (-(fy / fz)) • y := by
    have e1 : (1 / fz) • (fx • x) = (fx / fz) • x := by rw [smul_smul]; field_simp
    have e2 : (1 / fz) • (fy • y) = (fy / fz) • y := by rw [smul_smul]; field_simp
    have e3 : (-(fx / fz)) • x = -((fx / fz) • x) := by rw [neg_smul]
    have e4 : (-(fy / fz)) • y = -((fy / fz) • y) := by rw [neg_smul]
    rw [hfa, smul_add, smul_add, e1, e2, e3, e4, smul_smul, div_mul_cancel₀ _ hfz0,
      one_smul]
    abel
  have hcol2 : ¬ Collinear ℝ ({x, y, a} : Set V3) := COLL_IN_AFF_GT_TOO hcol ha
  have hxa : x ≠ a := fun h => hcol2 (collinear_triple_iff.mpr (Or.inl
    (by rw [← h]; exact mem_affineSpan _ (by simp))))
  have hya : y ≠ a := fun h => hcol2 (collinear_triple_iff.mpr (Or.inl
    (by rw [← h]; exact mem_affineSpan _ (by simp))))
  have hzr : z = -(fx / fz) • x + -(fy / fz) • y + (1 / fz) • a := by
    rw [hz'']; abel
  exact la5_affGt212_intro hxy hxa hya (gx := -(fx / fz)) (gy := -(fy / fz))
    (gz := 1 / fz) (by positivity)
    (by
      have h2 : (1:ℝ) - fx - fy = fz := by linarith
      have e0 : -(fx / fz) + -(fy / fz) + 1 / fz = (1 - fx - fy) / fz := by
        ring
      rw [e0, h2, div_self hfz0]) hzr

/-- HOL `COLL_IN_AFF_GT_AFF_GT_EQ` (local_lemmas.hl:5488). -/
theorem COLL_IN_AFF_GT_AFF_GT_EQ {x y z a : V3} (hcol : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (ha : a ∈ affGt ({x, y} : Set V3) ({z} : Set V3)) :
    affGt ({x, y} : Set V3) ({z} : Set V3) = affGt ({x, y} : Set V3) ({a} : Set V3) :=
  subset_antisymm
    (AFF_GT_IN_IMP_SUBSET (x := x) (y := y) (z := a) (a := z)
      (COLL_IN_AFF_GT_TOO hcol ha) (INVS_IN_AFF_GT hcol ha))
    (AFF_GT_IN_IMP_SUBSET hcol ha)

/-- HOL `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2` (local_lemmas.hl:5502).
NEEDS (orbit wave 2026-10-08): same orbit-side chain as
`NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT` (`LOFA_IMP_ITER_RHO_NODE_ID` now real;
`LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` still sorry) plus `i ≠ 1`
(ITER12-style). -/
theorem NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2 (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, w = (rhoNode1_p2 FF)^[i] v ∧ i + 1 < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧
      ¬((rhoNode1_p2 FF)^[i + 1] v ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3)) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): i ≠ 0 (else w = v against lunar
  -- v ≠ w) and i ≠ 1 (else w = ρ v makes {0,v,w} collinear — both mechanical
  -- once `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT` lands); that one is blocked by
  -- `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` (cyclicSet kit — see its -- NEEDS).
  sorry

/-- HOL `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT100` (local_lemmas.hl:5534).
NEEDS (B5 audit 2026-10-10): `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` (orbit
side) + the `i ≠ 1` refinement (HOL: ITER12 +
`LOCAL_FAN_CHARACTER_OF_RHO_NODE2`, purified by the B5 wave). -/
theorem LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT100 (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) :
    ∃ i : ℕ, i < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧ w = (rhoNode1_p2 FF)^[i] v ∧
      ((fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < i}) ⊆
        affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): `LUNAR_IMP_HALF_CIRCLE_SUBSET_
  -- AFF_GT` (cyclicSet kit — see its -- NEEDS) + the mechanical i ≠ 0 / i ≠ 1
  -- refinement (HOL: ITER12 + LOCAL_FAN_CHARACTER_OF_RHO_NODE2, real).
  sorry

/-- HOL `IVS_RHO_IDD` (local_lemmas.hl:5568) — filled (orbit wave
2026-10-08): `(v, rho v)` is the unique dart with second component
`rho v` (uniqueness via `LOFA_IMP_BIJ_VV` InjOn), so `RHO_NODE_INVERSE_POINT`
picks it. -/
theorem IVS_RHO_IDD (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ivsRhoNode1_p2 FF (rhoNode1_p2 FF v) = v := by
  have hw : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h).1 v hv
  have hbij := LOFA_IMP_BIJ_VV h
  have hun : ∀ ww : V3, (ww, rhoNode1_p2 FF v) ∈ FF → ww = v := by
    intro ww hww
    have hwv := LOCAL_FAN_IMP_IN_V h hww hww
    have hdet := (LOCAL_FAN_RHO_NODE_PROS h).2 (ww, rhoNode1_p2 FF v) hww
    have hsnd : (ww, rhoNode1_p2 FF v).2 = (ww, rhoNode1_p2 FF ww).2 :=
      congrArg Prod.snd hdet
    have hrho : rhoNode1_p2 FF ww = rhoNode1_p2 FF v := hsnd.symm
    exact hbij.2.1 hwv.1 hv hrho
  exact RHO_NODE_INVERSE_POINT hw hun

/-- HOL `AFF_IVS_RHO_NODE_EQQ` (local_lemmas.hl:5578). -/
theorem AFF_IVS_RHO_NODE_EQQ (h : convexLocalFan_p2 V E FF) (hl : lunar_p2 v w V E) :
    affGt ({0, w} : Set V3) ({rhoNode1_p2 FF w} : Set V3) =
      affGt ({0, v} : Set V3) ({ivsRhoNode1_p2 FF v} : Set V3) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): `LUNAR_IMP_HALF_CIRCLE_SUBSET_
  -- AFF_GT100` on lunar (w, v) (cyclicSet kit — see its -- NEEDS). Rest of
  -- the HOL route (5578) is real: v = ρ^[i] w with i ≥ 2 gives
  -- ivs v = ρ^[i-1] w (IVS_RHO_IDD shift) in the image set ⊆ affGt {0,w}{ρ w};
  -- COLL_IN_AFF_GT_AFF_GT_EQ (real) then swaps the GT point, and the {0,w}↦{0,v}
  -- ends swap is AFF_GT_SAME_WITH_ENDS (B5 wave).
  sorry

/-- HOL `LOFA_IMP_LT_CARD_SET_V` (local_lemmas.hl:5627; cf. the
`LOFA_IMP_LT_CARD_SET_V_ALT` re-render in LocalAuto2) — filled (LA5
downstream wave 2026-10-08): `LOOP_SET_DETER_FIRTS_ELMS` (real) on the
orbit half. -/
theorem LOFA_IMP_LT_CARD_SET_V (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    {(rhoNode1_p2 FF)^[n] v | n < V.ncard} = V :=
  LOOP_SET_DETER_FIRTS_ELMS (fun _u hu => LOCAL_FAN_ORBIT_MAP_V h hu) v hv

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
    (hv : v ∈ V) : interiorAngle1_p2 0 FF v ≤ Real.pi := by
  -- NEEDS (LA5 downstream wave 2026-10-08): the two-neighbor fact
  -- `(EE_p2 v E).ncard = 2`. Its chain is still sorried:
  -- LOFA_CARD_EE_V_1 ← LOFA_CARD_EE_V_2 ← LOFA_IMP_EE_TWO_ELMS (HOL 1899)
  -- ← LOFA_IN_E_IMP_IN_FF ← LOFA_DARTS_FF_UNION_SWITCH_FF (HOL 1786;
  -- dartsOfHyp_p2 E V = FF ∪ swapped — hypermap-side, still sorry) +
  -- LOCAL_FAN_IMP_NOT_SEMI_IDE (ρ²v ≠ v; needs |FF| ≥ 3, i.e. face-card ≥ 2
  -- content beyond la5_not_face_card_one). With it: azimInFan_p2 (v,ρ v) E ≤ π
  -- (the convex-fan hypothesis) forces the 1 < ncard branch (else 2π ≤ π),
  -- AZIM_CYCLE_TWO_POINT_SET (real) + epsilonFixed identify the cycle point
  -- as ivs v, and interiorAngle1_p2 (definitional) gives the claim.
  sorry

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
    ivsRhoNode1_p2 FF w ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) := by
  -- NEEDS (LA5 downstream wave 2026-10-08): `AFF_IVS_RHO_NODE_EQQ` (see its
  -- -- NEEDS; cyclicSet kit). HOL route (5868) is otherwise a one-liner:
  -- X_IN_AFF_GT_X gives ivs w ∈ affGt {0,w} {ivs w}, and the (real)
  -- LUNAR_COMM + AFF_IVS_RHO_NODE_EQQ instance identifies that set with
  -- affGt {0,v} {ρ v}.
  sorry

/-- HOL `AZIM_LE_PI_EQ_DIHV` (local_lemmas.hl:5880) — filled (LA5 downstream
wave 2026-10-08): `azim < π` case is LuneVolume `azim_dihv_same`; the
`azim = π` case rides `azim_dihv_compl` (public, Kepler.Geom) which gives
`azim = 2π - dihV`, hence `dihV = π` by linear arithmetic. -/
theorem AZIM_LE_PI_EQ_DIHV {a b x y : V3} (h1 : ¬ Collinear ℝ ({a, b, x} : Set V3))
    (h2 : ¬ Collinear ℝ ({a, b, y} : Set V3)) (h : azim a b x y ≤ Real.pi) :
    azim a b x y = dihV a b x y := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact azim_dihv_same h1 h2 hlt
  · have hcompl := azim_dihv_compl h1 h2 (by rw [heq])
    rw [heq]
    linarith

/-- HOL `LOFA_IMP_NOT_COLL_IVS` (local_lemmas.hl:5890) — filled (LA5
downstream wave 2026-10-08): the cycle predecessor `rho^[V.ncard - 1] v`
inverts `v` under `rho` (`LOFA_IMP_ITER_RHO_NODE_ID`, orbit wave), so
`ivs v` collapses to it via `IVS_RHO_IDD`, and the claim becomes the
B5-real `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` modulo a set permutation. -/
theorem LOFA_IMP_NOT_COLL_IVS (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    ¬ Collinear ℝ ({0, v, ivsRhoNode1_p2 FF v} : Set V3) := by
  have h1 : 0 < V.ncard := by
    by_contra hc
    have h0 : V.ncard = 0 := by omega
    have hV0 : V = ∅ :=
      (Set.ncard_eq_zero
        (hs := (la5_FAN_of_localFan h).2.2.1.1)).mp h0
    apply absurd hv
    rw [hV0]
    exact Set.notMem_empty v
  have hvv : (rhoNode1_p2 FF)^[V.ncard - 1] v ∈ V :=
    LOCAL_FAN_ORBIT_MAP_VITER h hv (V.ncard - 1)
  have hstep : (rhoNode1_p2 FF)^[V.ncard - 1 + 1] v = v := by
    have hID := LOFA_IMP_ITER_RHO_NODE_ID h hv
    have heq : V.ncard - 1 + 1 = V.ncard := by omega
    rw [heq]
    exact hID
  have h2 : (rhoNode1_p2 FF)^[V.ncard - 1 + 1] v
      = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] v) :=
    Function.iterate_succ_apply' _ _ _
  have hrv : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] v) = v := by
    rw [← h2]
    exact hstep
  have hivs : ivsRhoNode1_p2 FF v = (rhoNode1_p2 FF)^[V.ncard - 1] v := by
    have h3 := IVS_RHO_IDD h hvv
    rw [hrv] at h3
    exact h3
  intro hcol
  refine LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h hvv ?_
  rw [hrv]
  rw [hivs] at hcol
  have hperm : ({(0:V3), (rhoNode1_p2 FF)^[V.ncard - 1] v, v} : Set V3)
      = ({(0:V3), v, (rhoNode1_p2 FF)^[V.ncard - 1] v} : Set V3) := by
    ext z; simp; tauto
  rw [hperm]
  exact hcol

/-- HOL `DIHV_NOT_CHANGE` (local_lemmas.hl:5903). -/
theorem DIHV_NOT_CHANGE {x y v w : V3} {a b c : ℝ} (hc : 0 < c) (hsum : a + b + c = 1) :
    dihV x y (a • x + b • y + c • v) w = dihV x y v w := by
  have hsumv : (a + b + c) • x = (1:ℝ) • x := by rw [hsum, one_smul]
  -- Pi-level dot transport (LuneVolume idiom; V3-dot is Pi-dotProduct up to coe)
  have dot_smul_l : ∀ (t : ℝ) (u v : V3), (t • u) ⬝ᵥ v = t * (u ⬝ᵥ v) :=
    fun t u v => smul_dotProduct t (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  have dot_add_l : ∀ (u v w : V3), (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w :=
    fun u v w => add_dotProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)
  have dot_smul_r : ∀ (u : V3) (t : ℝ) (v : V3), (u ⬝ᵥ (t • v)) = t * (u ⬝ᵥ v) :=
    fun u t v => dotProduct_smul t (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  set w2 : V3 := (a • x + b • y + c • v : V3) with hw2def
  set VA : V3 := ((y - x : V3) ⬝ᵥ (y - x)) • (v - x)
      - ((v - x : V3) ⬝ᵥ (y - x)) • (y - x) with hVAdef
  set VBP : V3 := ((y - x : V3) ⬝ᵥ (y - x)) • (w - x)
      - ((w - x : V3) ⬝ᵥ (y - x)) • (y - x) with hVBPdef
  have hva : (w2 - x : V3) = b • (y - x) + c • (v - x) := by
    rw [hw2def]
    linear_combination (norm := module) hsumv
  -- the new projection vector is c • VA (the b-part lies along the axis and cancels)
  have hvap : ((y - x : V3) ⬝ᵥ (y - x)) • (w2 - x)
      - ((w2 - x : V3) ⬝ᵥ (y - x)) • (y - x) = c • VA := by
    rw [hva, hVAdef, smul_add, dot_add_l, dot_smul_l, dot_smul_l, smul_smul, smul_smul]
    module
  -- arcV is invariant under a common positive rescaling of both arguments
  have hscale : arcV 0 (c • VA) VBP = arcV 0 VA VBP := by
    rw [arcV, arcV]
    have coez : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl
    simp only [coez, sub_zero, dist_eq_norm, sub_zero, dot_smul_l, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    field_simp
  show arcV 0 (((y - x : V3) ⬝ᵥ (y - x)) • (w2 - x)
      - ((w2 - x : V3) ⬝ᵥ (y - x)) • (y - x)) VBP
    = arcV 0 VA VBP
  rw [hvap, hscale]

/-- HOL `LUNAR_IMP_INTERIOR_ANGLE_EQQ` (local_lemmas.hl:5915).  NEEDS
(updated LA5 downstream wave 2026-10-08): of the four gaps, two are now
real — `AZIM_LE_PI_EQ_DIHV` (LuneVolume azim_dihv_same/azim_dihv_compl)
and `LOFA_IMP_NOT_COLL_IVS` (cycle predecessor + IVS_RHO_IDD). Remaining:
`IVS_RNODE_IN_AFF_V` (← AFF_IVS_RHO_NODE_EQQ ← GT100, cyclicSet kit) and
`CONVEX_LOFA_IMP_INANGLE_LE_PI` (← EE-card chain) — see the `-- NEEDS`
lines at those items. Already real: `NOT_COLL_RHONODE_SND_POINT` (B5
wave), `LUNAR_COMM`, `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` (purified),
`DIHV_NOT_CHANGE`, `FOR_AFF_GT_NOT_INTERSECTION2`, `sum4_azim_fan`. -/
theorem LUNAR_IMP_INTERIOR_ANGLE_EQQ (h : convexLocalFan_p2 V E FF)
    (hl : lunar_p2 v w V E) : interiorAngle1_p2 0 FF v = interiorAngle1_p2 0 FF w := by
  -- NEEDS (LA5 downstream wave 2026-10-08): mirrors HOL 5915 once the two
  -- remaining gaps land. Skeleton: CONVEX_LOFA_IMP_INANGLE_LE_PI (v and w)
  -- + AZIM_LE_PI_EQ_DIHV (real) rewrite interiorAngle1_p2 0 FF v and
  -- interiorAngle1_p2 0 FF w as dihV values; IVS_RNODE_IN_AFF_V on both
  -- sides (via LUNAR_COMM) + Fan.th3a/AFF_GT_2_1 extraction
  -- (la5_affGt212_extract, real) + 0 ∈ conv0 {w,v} (LUNAR's coin, real)
  -- feed the DIHV_SPECIAL_SCALE / DIHV_NOT_CHANGE (real) transport.
  sorry

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
theorem LOFA_V_NOT_EMP (h : localFan_p2 V E FF) : V ≠ ∅ :=
  (la5_FAN_of_localFan h).2.2.1.2

/-- HOL `LOCAL_FAN_FINITE_V` (local_lemmas.hl:6096). -/
theorem LOCAL_FAN_FINITE_V (h : localFan_p2 V E FF) : V.Finite :=
  (la5_FAN_of_localFan h).2.2.1.1

/-- HOL `ITER_CARD_MINUS1_EQ_IVS_RN1` (local_lemmas.hl:6106) — filled (LA5
downstream wave 2026-10-08): the cycle predecessor inverts `v` (orbit
wave `LOFA_IMP_ITER_RHO_NODE_ID`), and `IVS_RHO_IDD` then identifies it
as the inverse-point. -/
theorem ITER_CARD_MINUS1_EQ_IVS_RN1 (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard - 1] v = ivsRhoNode1_p2 FF v := by
  have h1 : 0 < V.ncard := by
    by_contra hc
    have h0 : V.ncard = 0 := by omega
    have hV0 : V = ∅ :=
      (Set.ncard_eq_zero
        (hs := (la5_FAN_of_localFan h).2.2.1.1)).mp h0
    apply absurd hv
    rw [hV0]
    exact Set.notMem_empty v
  have hvv : (rhoNode1_p2 FF)^[V.ncard - 1] v ∈ V :=
    LOCAL_FAN_ORBIT_MAP_VITER h hv (V.ncard - 1)
  have hstep : (rhoNode1_p2 FF)^[V.ncard - 1 + 1] v = v := by
    have hID := LOFA_IMP_ITER_RHO_NODE_ID h hv
    have heq : V.ncard - 1 + 1 = V.ncard := by omega
    rw [heq]
    exact hID
  have h2 : (rhoNode1_p2 FF)^[V.ncard - 1 + 1] v
      = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] v) :=
    Function.iterate_succ_apply' _ _ _
  have hrv : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[V.ncard - 1] v) = v := by
    rw [← h2]
    exact hstep
  have h3 := IVS_RHO_IDD h hvv
  rw [hrv] at h3
  exact h3.symm

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
    d.1 ∈ V ∧ d.2 ∈ V := by
  have h1 := la5_FF_subset_darts h hd
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := h
  exact la5_dart_mem_V hfan h1

/-- HOL `LOFA_DETERMINE_AZIM_IN_FA` (local_lemmas.hl:6199). -/
theorem LOFA_DETERMINE_AZIM_IN_FA (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    azimInFan_p2 x E = azim 0 x.1 x.2 (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2) := sorry

end Kepler.Text

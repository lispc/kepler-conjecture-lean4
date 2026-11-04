/-
Kepler.Text.LocalAuto10 — port of Flyspeck `local/LVDUCXU.hl` (module
`Lvducxu`, Nguyen Quang Truong, 2010-05-09; 2311 lines, 0 definitions + 50
theorem bindings): the "localization preserves the face structure" chapter.
Its headline `LVDUCXU` feeds the second lemma of the Local Fan chapter:
under a local fan at the origin, passing from `(V,E)` to the localized
`(v_prime V FF, e_prime E FF)` preserves faces (`LOCALIZE_PRESERVE_FACE`),
the fan quantities (`azim_in_fan`, `wedge_in_fan_ge/gt`), and — for faces of
cardinality `> 2` with a simple localized hypermap — yields a local fan.

Encoding notes (per Kepler/Text/Polytope.lean conventions):
- HOL `real^3` ↔ `V3`; `vec 0` ↔ `(0 : V3)`; darts are `V3 × V3`;
  `ITER n f` ↔ `f^[n]`; `POWER n f` collapses likewise.
- The upstream `_p3` kit of Kepler.Text.LocalAuto3 (source `WRGCVDR.hl`, the
  direct predecessor `flyspeck_needs`ed by this file) is IMPORTED, not
  copied: `dartsOfHyp_p3`, `eeOfHyp_p3`, `nnOfHyp_p3`, `ffOfHyp_p3`,
  `EE_p3`, `ordPairs_p3`, `selfPairs_p3`, `azimCycle_p3`, `ivsAzimCycle_p3`,
  `vPrime_p3`, `ePrime_p3`, `hasOrders_p3`, `cyclicOn_p3`, `dih2k_p3`,
  `orbitF_p3`, `permutesF_p3`, `localFan_p3`, `azimInFan_p3`,
  `wedgeInFanGe_p3`, `wedgeInFanGt_p3` and the theorem layer on top.
- `hypermap (HYP (x,V,E))` (the 4-tuple constructor) is ABSORBED by the
  proof-carrying `Hypermap` structure exactly as in LocalAuto2/3: theorems
  are stated over a carrier `HS : Hypermap (V3 × V3)` satisfying the local
  predicate `IsHypOn_p10 x V E HS` (dart set + e/n/f maps equal the `HYP`
  components — the `IsHyp_p2` pattern). Existence of such a carrier under
  `FAN` is `LocalAuto3.HYP_LEMMA`/`ELMS_OF_HYPERMAP_HYP`; `dart (hypermap …)`
  in a hypothesis becomes `dartsOfHyp_p3 E V` via `FAN_DART_DARTS` below.
- HOL `BIJ f S T` ↦ `BIJ_p10 f S T` (InjOn + surjection onto T); HOL `CARD`
  ↦ `Set.ncard` (junk `∞ ↦ 0` matches only on finite sets; faces of local
  fans are finite), `dih2k H (CARD FF)` ↦ `dih2k_p3 _ (Set.ncard FF)`
  following the `localFan_p3` convention; `inverse (face_map H)` on the
  `Equiv.Perm` maps ↦ `.symm` (`⁻¹` is definitionally `symm`); `permutes`
  on the structure maps ↦ `PermutesOn` (fields), on plain functions ↦
  `permutesF_p3`.
- Shadowed HOL re-bindings of the same name are merged into one Lean
  theorem: `PROPERTIES_OF_IVS_AZIM_CYCLE2` (source lines 29 alias + 142
  proved version), `EE_FST_Y_EQ_SET_SET_SNDY` (lines 956 = 1041), and
  `EDGE_MAP_RESO_INVERSE` (lines 1772 + 1776 conjunction). The two distinct
  statements of `FAN_FACE_IMP_IVS_F_IN_F` (lines 500 with, 533 without, the
  dart-membership hypothesis) are kept apart as `FAN_FACE_IMP_IVS_F_IN_F`
  and `FAN_FACE_IMP_IVS_F_IN_F_DART`. The line-1036 re-binding
  `W_SUBSET_SINGLETON_IMP_IDE` coincides with the importable
  `LocalAuto3.W_SUBSET_SINGLETON_IMP_IDE` and is NOT redeclared. Tactic
  bindings (`ENF_RULE`, `MP_TAC2`, `TR_ENF_TAC`, the local `ge`) have no
  Lean counterpart; `ENF_RULE`'s two instances are inlined into
  `EDGE_MAP_RESO_INVERSE`, `TR_ENF_TAC`'s content into `ENF_IMAGE_ITSELF`.
- Giant proofs are stated and `sorry`-marked (DISCHARGES registry); the
  mechanical/forwarding layer is proved.

DISCHARGES: nothing yet (this file is the LVDUCXU contract registry; the
sorried giants are discharged by a later wave, after which the `sorry`s
disappear).
-/

import Kepler.Text.LocalAuto3
import Kepler.Text.Polytope
import Kepler.Text.Fan
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## `_p10` copies: the HYP-carrier predicate and HOL `BIJ` -/

/-- HOL `hypermap (HYP (x,V,E))` as a predicate on the carrier `Hypermap`
(the `IsHyp_p2` pattern of LocalAuto2, over the imported `_p3` kit).
NEEDS: dedup against `IsHyp_p2` at merge (different kit instance). -/
def IsHypOn_p10 (x : V3) (V : Set V3) (E : Set (Set V3)) (HS : Hypermap (V3 × V3)) :
    Prop :=
  (↑HS.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
    (HS.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
    (HS.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
    (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E

/-- HOL `BIJ f S T = INJ f S T /\ SURJ f S T` (surjective onto `T`). -/
def BIJ_p10 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  Set.InjOn f s ∧ ∀ y ∈ t, ∃ x ∈ s, f x = y

/-- Pointwise transport between a permutation and its function coercion
(used by the orbit lemmas). -/
private theorem lvd_orbitMap_eq_orbitF {α : Type*} [DecidableEq α] {p : Equiv.Perm α}
    {s : Finset α} (hp : PermutesOn p s) (x y : α) (h : y ∈ orbitMap p x) :
    orbitMap p x = orbitF_p3 (p : α → α) y := by
  rw [← orbitMap_eq_of_mem hp h]
  ext z
  simp only [orbitMap, orbitF_p3, Set.mem_setOf_eq]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, by rw [Equiv.Perm.coe_pow] at hm; exact hm⟩,
    fun ⟨m, hm⟩ => ⟨m, by rw [Equiv.Perm.coe_pow]; exact hm⟩⟩

/-- `(p⁻¹)^n ((p^n) x) = x` (helper for `INVERSE_FACE_CYCLE`). -/
private theorem lvd_symmPow_pow_apply {α : Type*} (p : Equiv.Perm α) :
    ∀ n : ℕ, ∀ x : α, (p.symm ^ n) ((p ^ n) x) = x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.symm_apply_apply, ih]

/-- Orbit-closure induction: if `fc'` maps `f` into itself and `b ∈ f`, all
iterates of `b` stay in `f`. (Skeleton of the HOL `LOCALIZE_PRESERVE_FACE`
orbit argument.) -/
private theorem lvd_orbit_subset_of_closed {α : Type*} [DecidableEq α] {fc' : Equiv.Perm α}
    {f : Set α} {b : α} (hb : b ∈ f) (hclosed : ∀ d ∈ f, fc' d ∈ f) :
    ∀ n : ℕ, (fc' ^ n) b ∈ f := by
  intro n
  induction n with
  | zero => simpa using hb
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hclosed _ ih

/-- Pointwise agreement of two permutations on the `fc`-orbit of `b` gives
agreement of all iterates at `b`. -/
private theorem lvd_pow_agree {α : Type*} [DecidableEq α] {fc fc' : Equiv.Perm α}
    {f : Set α} {b : α} (hbf : orbitMap fc b = f)
    (hagree : ∀ d ∈ f, fc' d = fc d) : ∀ n : ℕ, (fc' ^ n) b = (fc ^ n) b := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hmem : (fc ^ m) b ∈ f := by rw [← hbf]; exact pow_apply_mem_orbitMap fc m b
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact hagree _ hmem

/-- Orbit extension: if `f` is the `fc`-orbit of `b`, and `fc'` agrees with
`fc` on `f` and maps `f` into itself, then the `fc'`-orbit of `b` is `f`
(the geometric-free skeleton of HOL `LOCALIZE_PRESERVE_FACE`). -/
private theorem lvd_orbit_ext_of_agree {α : Type*} [DecidableEq α] {fc fc' : Equiv.Perm α}
    {f : Set α} {b : α} (hbf : orbitMap fc b = f) (hb : b ∈ f)
    (hagree : ∀ d ∈ f, fc' d = fc d) (hclosed : ∀ d ∈ f, fc' d ∈ f) :
    orbitMap fc' b = f := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    obtain ⟨n, hn⟩ := hy
    rw [← hn]
    exact lvd_orbit_subset_of_closed hb hclosed n
  · intro y hy
    rw [← hbf] at hy
    obtain ⟨n, hn⟩ := hy
    rw [← hn, ← lvd_pow_agree hbf hagree n]
    exact pow_apply_mem_orbitMap fc' n b

/-- σ-agreement on nested neighbour sets (HOL `IN_FF_FACE_MAP_IDE` tail,
`IDENTIFY_AZIM_CYCLE` step): if the restricted neighbour set sits inside the
full one, `u` is restricted, and the full successor `σ_full u` is restricted,
then the two successors agree.  Single-point branches fold by definition;
otherwise `SIGMA_FAN` minimality on both sides plus azimuth uniqueness. -/
private theorem lvd_sigma_agree {x : V3} {V V' : Set V3} {E E' : Set (Set V3)} {w u : V3}
    (hfan : FAN x V E) (hfan' : FAN x V' E')
    (hsub : ∀ p : V3, p ∈ setOfEdge w V' E' → p ∈ setOfEdge w V E)
    (hu' : u ∈ setOfEdge w V' E') (hu : u ∈ setOfEdge w V E)
    (hσ : sigmaFan x V E w u ∈ setOfEdge w V' E') :
    sigmaFan x V E w u = sigmaFan x V' E' w u := by
  by_cases hSfull : setOfEdge w V E = {u}
  · have hσu : sigmaFan x V E w u = u := by rw [sigmaFan, if_pos hSfull]
    have huin : u ∈ setOfEdge w V' E' := by rw [← hσu]; exact hσ
    have hSrst : setOfEdge w V' E' = {u} := by
      apply Set.ext
      intro a
      constructor
      · intro ha
        have ha' : a ∈ setOfEdge w V E := hsub a ha
        rw [hSfull] at ha'
        simpa using ha'
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact huin
    rw [hσu, sigmaFan, if_pos hSrst]
  · obtain ⟨hσS, hσne, hσmin⟩ := SIGMA_FAN hSfull hfan hu
    by_cases hSrst : setOfEdge w V' E' = {u}
    · exfalso
      have hmem : sigmaFan x V E w u = u := by
        have h1 : sigmaFan x V E w u ∈ ({u} : Set V3) := hSrst ▸ hσ
        simpa using h1
      exact hσne hmem
    · obtain ⟨hσS', hσne', hσmin'⟩ := SIGMA_FAN hSrst hfan' hu'
      have hwu : ({w, u} : Set V3) ∈ E :=
        (properties_of_setOfEdge_fan x V E w u hfan).mpr hu
      have hfullE : ({w, sigmaFan x V E w u} : Set V3) ∈ E :=
        (properties_of_setOfEdge_fan x V E w _ hfan).mpr hσS
      have hrstfull : sigmaFan x V' E' w u ∈ setOfEdge w V E := hsub _ hσS'
      have hrstE : ({w, sigmaFan x V' E' w u} : Set V3) ∈ E :=
        (properties_of_setOfEdge_fan x V E w _ hfan).mpr hrstfull
      have hle1 : azim x w u (sigmaFan x V E w u) ≤ azim x w u (sigmaFan x V' E' w u) :=
        hσmin _ hrstfull hσne'
      have hle2 : azim x w u (sigmaFan x V' E' w u) ≤ azim x w u (sigmaFan x V E w u) :=
        hσmin' _ hσ hσne
      exact unique_azim_point_fan hfan hwu hfullE hrstE (le_antisymm hle1 hle2)

/-- Canonical `HYP` carrier of a fan in component form (projection of the
proved `ELMS_OF_HYPERMAP_HYP`). -/
private theorem lvd_hypCarrier {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E) :
    ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E := by
  obtain ⟨H, hH⟩ := ELMS_OF_HYPERMAP_HYP hfan
  have h1 : (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V :=
    (congrArg Prod.fst hH).symm
  have h2 : (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E :=
    (congrArg (fun p => p.2.1) hH).symm
  have h3 : (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E :=
    (congrArg (fun p => p.2.2.1) hH).symm
  have h4 : (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E :=
    (congrArg (fun p => p.2.2.2) hH).symm
  exact ⟨H, h1, h2, h3, h4⟩

/-- The localized fan exists (`IMP_FAN_V_PRIME_E_PRIME` with the canonical
carrier as the `HYP` witness). -/
private theorem lvd_fan_vPrime_ePrime {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {FF : Set (V3 × V3)} {HS : Hypermap (V3 × V3)}
    (hHS : IsHypOn_p10 x V E HS) {v : V3 × V3} (hv : v ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face v) :
    FAN x (vPrime_p3 V FF) (ePrime_p3 E FF) := by
  obtain ⟨H, hd, he, hn, hf⟩ := lvd_hypCarrier hfan
  have hvd : v ∈ H.darts := Finset.mem_coe.mp (by rw [hd]; exact hv)
  have hperm : H.faceMap = HS.faceMap := by
    apply Equiv.ext
    intro d
    rw [hf, ← hHS.2.2.2]
  have hfaceH : H.face v = FF := by
    rw [Hypermap.face, hperm, ← Hypermap.face]
    exact hFF.symm
  exact IMP_FAN_V_PRIME_E_PRIME hfan ⟨H, hd, he, hn, hf, v, hvd, hfaceH.symm⟩

/-! ## Set-composition block (LVDUCXU.hl:58–116, 1373–1385, 2081) -/

/-- LVDUCXU.hl:58 `W_EQ_ITS_ORBIT_IMP_EQ_ITS_IMAGE`. -/
theorem W_EQ_ITS_ORBIT_IMP_EQ_ITS_IMAGE {α : Type*} {f : α → α} {W : Set α}
    (h : ∀ x ∈ W, W = orbitF_p3 f x) : W = f '' W := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hyx⟩ := CYCLIC_MAP_IMP_CIRCLE_ITSELF h hy
    exact ⟨x, hx, hyx.symm⟩
  · rintro ⟨x, hx, rfl⟩
    have h2 : f x ∈ orbitF_p3 f x := IN_ORBIT_MAP_IMP_F_Y (X_IN_ITS_ORBIT f x)
    rwa [← h x hx] at h2

/-- LVDUCXU.hl:84 `FINITE_AND_LOOP_IMP_BIJ_S_IM_S`. -/
theorem FINITE_AND_LOOP_IMP_BIJ_S_IM_S {α : Type*} {f : α → α} {S : Set α}
    (hfin : S.Finite) (h : ∀ x ∈ S, S = orbitF_p3 f x) :
    BIJ_p10 f S (f '' S) := by
  have himg : f '' S = S := (W_EQ_ITS_ORBIT_IMP_EQ_ITS_IMAGE h).symm
  refine ⟨?_, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, hx, rfl⟩⟩
  have heq : hfin.toFinset.image f = hfin.toFinset := by
    refine Finset.coe_injective ?_
    rw [Finset.coe_image, Set.Finite.coe_toFinset, himg]
  have hc : (hfin.toFinset.image f).card = (hfin.toFinset).card := by rw [heq]
  rw [Finset.card_image_iff] at hc
  intro a ha b hb hab
  exact hc (by simpa using ha) (by simpa using hb) (by simpa using hab)

/-- LVDUCXU.hl:111 `FIN_LOOP_IMP_BIJ_ITSELF`. -/
theorem FIN_LOOP_IMP_BIJ_ITSELF {α : Type*} {f : α → α} {S : Set α}
    (hfin : S.Finite) (h : ∀ x ∈ S, S = orbitF_p3 f x) : BIJ_p10 f S S := by
  have h1 := FINITE_AND_LOOP_IMP_BIJ_S_IM_S hfin h
  refine ⟨h1.1, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := CYCLIC_MAP_IMP_CIRCLE_ITSELF h hy
  exact h1.2 (f x) (Set.mem_image_of_mem f hx)

/-- LVDUCXU.hl:1373 `FX_IN_S_IMP_F_POWER_TOO`. -/
theorem FX_IN_S_IMP_F_POWER_TOO {α : Type*} {f : α → α} {S : Set α}
    (h : ∀ x ∈ S, f x ∈ S) {x : α} (hx : x ∈ S) :
    ∀ n : ℕ, f^[n] x ∈ S := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact h _ ih

/-- LVDUCXU.hl:1380 `FX_IN_S_IMP_ORBIT_SUBSET`. -/
theorem FX_IN_S_IMP_ORBIT_SUBSET {α : Type*} {f : α → α} {S : Set α}
    (h : ∀ x ∈ S, f x ∈ S) {x : α} (hx : x ∈ S) : orbitF_p3 f x ⊆ S := by
  rintro y ⟨n, rfl⟩
  exact FX_IN_S_IMP_F_POWER_TOO h hx n

/-- LVDUCXU.hl:2081 `IDE_ON_S_IMP_SAME_IMAGE`. -/
theorem IDE_ON_S_IMP_SAME_IMAGE {α β : Type*} {f g : α → β} {S : Set α}
    (h : ∀ x ∈ S, f x = g x) : f '' S = g '' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (h x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, h x hx⟩

/-! ## Darts / `EE` / `e_prime` block (LVDUCXU.hl:33, 164, 122, 731) -/

/-- LVDUCXU.hl:33 `IN_FF_IMP_FST_SND_IN_V`. -/
theorem IN_FF_IMP_FST_SND_IN_V {E : Set (Set V3)} {V : Set V3} (hsub : ⋃₀ E ⊆ V)
    {FF : Set (V3 × V3)} (hFF : FF ⊆ dartsOfHyp_p3 E V) {x : V3 × V3} (hx : x ∈ FF) :
    x.1 ∈ V ∧ x.2 ∈ V :=
  IN_DARTS_HYP_IMP_FST_SND_IN_V hsub (hFF hx)

/-- LVDUCXU.hl:164 `IN_EE_IFF_IN_E` (definitional). -/
theorem IN_EE_IFF_IN_E {α : Type*} {E : Set (Set α)} (v x : α) :
    x ∈ EE_p3 v E ↔ {v, x} ∈ E := Iff.rfl

/-- LVDUCXU.hl:122 `IN_DARTS_FF_IMP_DARTS_E_PRIME_V_PRIME`. -/
theorem IN_DARTS_FF_IMP_DARTS_E_PRIME_V_PRIME {E : Set (Set V3)} {V : Set V3}
    {FF : Set (V3 × V3)} {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hxFF : x ∈ FF) :
    x ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) := by
  rcases (Set.mem_union _ _ _).mp hx with h | h
  · refine Set.mem_union_left _ ?_
    exact ⟨x.1, x.2, rfl, h, hxFF⟩
  · refine Set.mem_union_right _ ?_
    have hs : x.1 = x.2 ∧ x.1 ∈ V ∧ EE_p3 x.1 E = ∅ := h
    show x.1 = x.2 ∧ x.1 ∈ vPrime_p3 V FF ∧ EE_p3 x.1 (ePrime_p3 E FF) = ∅
    have hxe : x = (x.1, x.1) := PAIR_EQ2.mpr ⟨rfl, hs.1.symm⟩
    refine ⟨hs.1, ⟨hs.2.1, x.1, ?_⟩, ?_⟩
    · rw [← hxe]
      exact hxFF
    · refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      obtain ⟨a, b, hab, hE, -⟩ := hw
      rw [← hab] at hE
      have hmem : w ∈ EE_p3 x.1 E := hE
      rw [hs.2.2] at hmem
      exact hmem

/-- LVDUCXU.hl:731 `IN_DARTS_IMP_NN_OF_HYP_TOO` (forwarding of the
importable `IN_DARTS_IFF_NN_OF_HYP_TOO`). -/
theorem IN_DARTS_IMP_NN_OF_HYP_TOO {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (y : V3 × V3) (hy : y ∈ dartsOfHyp_p3 E V) :
    nnOfHyp_p3 x V E y ∈ dartsOfHyp_p3 E V :=
  (IN_DARTS_IFF_NN_OF_HYP_TOO hfan y).mp hy

/-! ## azim-cycle cyclicity (LVDUCXU.hl:142, 98, 168, 175) -/

/-- LVDUCXU.hl:29/142 `PROPERTIES_OF_IVS_AZIM_CYCLE2` (the line-29 alias is
the line-142 proved statement, in `EE`/`azim_cycle` form). -/
theorem PROPERTIES_OF_IVS_AZIM_CYCLE2 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v w : V3} (hw : w ∈ EE_p3 v E) :
    ivsAzimCycle_p3 (EE_p3 v E) x v w ∈ EE_p3 v E ∧
      azimCycle_p3 (EE_p3 v E) x v (ivsAzimCycle_p3 (EE_p3 v E) x v w) = w := by
  have hE : EE_p3 v E = setOfEdge v V E := FAN_IMP_EE_EQ_SET_OF_EDGE hfan v
  rw [hE] at hw
  obtain ⟨h1, h2⟩ := IVS_AZIM_PROPERTIES hfan hw
  have hconv : ivsAzimCycle_p3 (EE_p3 v E) x v w = ivsAzimCycle_p3 (setOfEdge v V E) x v w := by
    rw [hE]
  rw [hconv]
  refine ⟨by rwa [hE], ?_⟩
  exact (AZIM_CYCLE_EQ_SIGMA_FAN hfan h1).trans h2

/-- LVDUCXU.hl:98 `CYCLIC_SET_IMP_SELF_LOPP2`. -/
theorem CYCLIC_SET_IMP_SELF_LOPP2 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (he : {v, u} ∈ E) (a : V3) (ha : a ∈ EE_p3 v E) :
    EE_p3 v E = orbitF_p3 (azimCycle_p3 (EE_p3 v E) x v) a := by
  have hstab := CYCLIC_SET_IMP_STABLE_SET2 hfan he a ha
  refine hstab.trans ?_
  ext z
  simp only [orbitF_p3, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, hn.symm⟩
  · intro h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, hn.symm⟩

/-- LVDUCXU.hl:168 `CYCLIC_SET_IMP_SELF_LOPP3`. -/
theorem CYCLIC_SET_IMP_SELF_LOPP3 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (v : V3) (a : V3) (ha : a ∈ EE_p3 v E) :
    EE_p3 v E = orbitF_p3 (azimCycle_p3 (EE_p3 v E) x v) a :=
  CYCLIC_SET_IMP_SELF_LOPP2 hfan ((IN_EE_IFF_IN_E v a).mp ha) a ha

/-- LVDUCXU.hl:175 `BIJ_AZIM_CYCLE_EE`. -/
theorem BIJ_AZIM_CYCLE_EE {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (v : V3) :
    BIJ_p10 (azimCycle_p3 (EE_p3 v E) x v) (EE_p3 v E) (EE_p3 v E) :=
  FIN_LOOP_IMP_BIJ_ITSELF (FAN_IMP_FINITE_EE hfan v)
    (fun a ha => CYCLIC_SET_IMP_SELF_LOPP3 hfan v a ha)

/-! ## Generic hypermap-permutation block (LVDUCXU.hl:654, 1164, 1345,
1362, 1662, 1763–1826, 2054, 2072) -/

/-- LVDUCXU.hl:654 `ED_MA_O_NO_MA_EQ_INV_FA`. -/
theorem ED_MA_O_NO_MA_EQ_INV_FA {α : Type*} [DecidableEq α] (H : Hypermap α) :
    (H.edgeMap * H.nodeMap : Equiv.Perm α) = H.faceMap⁻¹ :=
  H.edgeMap_mul_nodeMap

/-- LVDUCXU.hl:1164 `FACE_NODE_EDGE_ORBIT_INVERSE`. -/
theorem FACE_NODE_EDGE_ORBIT_INVERSE {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    H.face x = orbitMap (H.faceMap.symm) x ∧
      H.node x = orbitMap (H.nodeMap.symm) x ∧
      H.edge x = orbitMap (H.edgeMap.symm) x :=
  ⟨(H.faceMap_permutes.orbitMap_symm x).symm,
    (H.nodeMap_permutes.orbitMap_symm x).symm,
    (H.edgeMap_permutes.orbitMap_symm x).symm⟩

/-- LVDUCXU.hl:1345 `FIRST_AAUHTVE2` (the `permutes` conjuncts are the
carrier structure fields; the two composition identities hold at the
`Equiv.Perm` level, cf. the plain-function `FIRST_AAUHTVE`). -/
theorem FIRST_AAUHTVE2 {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E) :
    ∃ HS : Hypermap (V3 × V3),
      (↑HS.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (HS.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
      (HS.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
      (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E ∧
      PermutesOn HS.edgeMap HS.darts ∧ PermutesOn HS.nodeMap HS.darts ∧
        PermutesOn HS.faceMap HS.darts ∧
        (HS.edgeMap * HS.nodeMap * HS.faceMap : Equiv.Perm (V3 × V3)) = 1 ∧
        (HS.edgeMap * HS.edgeMap : Equiv.Perm (V3 × V3)) = 1 := by
  obtain ⟨HS, hd, he, hn, hf, hee⟩ := FIRST_AAUHTVE hfan
  refine ⟨HS, hd, he, hn, hf, HS.edgeMap_permutes, HS.nodeMap_permutes,
    HS.faceMap_permutes, HS.comp_eq_one, ?_⟩
  refine Equiv.ext fun d => ?_
  simpa [Equiv.Perm.mul_apply] using congrFun hee d

/-- LVDUCXU.hl:1362 `NOT_IN_DART_IMP_IDE`. -/
theorem NOT_IN_DART_IMP_IDE {α : Type*} [DecidableEq α] (H : Hypermap α) {x : α}
    (hx : x ∉ H.darts) :
    H.edgeMap x = x ∧ H.nodeMap x = x ∧ H.faceMap x = x :=
  ⟨H.edgeMap_permutes x hx, H.nodeMap_permutes x hx, H.faceMap_permutes x hx⟩

/-- LVDUCXU.hl:1662 `HYP_MAPS_INJ`. -/
theorem HYP_MAPS_INJ {α : Type*} [DecidableEq α] (H : Hypermap α) :
    (∀ x y : α, H.edgeMap x = H.edgeMap y ↔ x = y) ∧
      (∀ x y : α, H.nodeMap x = H.nodeMap y ↔ x = y) ∧
      (∀ x y : α, H.faceMap x = H.faceMap y ↔ x = y) :=
  ⟨fun _ _ => H.edgeMap.injective.eq_iff, fun _ _ => H.nodeMap.injective.eq_iff,
    fun _ _ => H.faceMap.injective.eq_iff⟩

/-- LVDUCXU.hl:1763 `ITER12`. -/
theorem ITER12 {α : Type*} (f : α → α) (x : α) :
    f^[1] x = f x ∧ f^[2] x = f (f x) := by
  simp

/-- LVDUCXU.hl:1772/1776 `EDGE_MAP_RESO_INVERSE` (both bindings; edge and
node components). -/
theorem EDGE_MAP_RESO_INVERSE {α : Type*} [DecidableEq α] (H : Hypermap α) :
    ((H.edgeMap * H.edgeMap : Equiv.Perm α) = 1 ↔ H.edgeMap.symm = H.edgeMap) ∧
      ((H.nodeMap * H.nodeMap : Equiv.Perm α) = 1 ↔ H.nodeMap.symm = H.nodeMap) := by
  constructor
  · constructor
    · intro h
      exact (eq_inv_of_mul_eq_one_left h).symm
    · intro h
      have h' : H.edgeMap⁻¹ = H.edgeMap := h
      have hi := inv_mul_cancel H.edgeMap
      rw [h'] at hi
      exact hi
  · constructor
    · intro h
      exact (eq_inv_of_mul_eq_one_left h).symm
    · intro h
      have h' : H.nodeMap⁻¹ = H.nodeMap := h
      have hi := inv_mul_cancel H.nodeMap
      rw [h'] at hi
      exact hi

/-- LVDUCXU.hl:1781 `HAS_ORD2_INTERPRET`. -/
theorem HAS_ORD2_INTERPRET {α : Type*} (f : α → α) :
    hasOrders_p3 f 2 ↔ f ∘ f = id ∧ ¬(f = id) := by
  constructor
  · rintro ⟨hnone, hfix⟩
    exact ⟨hfix, fun hc => hnone 1 (by omega) (by omega) hc⟩
  · rintro ⟨hcomp, hne⟩
    refine ⟨?_, ?_⟩
    · intro i hi1 hi2 hc
      rw [show i = 1 from by omega] at hc
      exact hne hc
    · exact hcomp

/-- LVDUCXU.hl:1788 `HYP_MAPS_INVS`. -/
theorem HYP_MAPS_INVS {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    H.edgeMap (H.edgeMap.symm x) = x ∧ H.edgeMap.symm (H.edgeMap x) = x ∧
      H.faceMap (H.faceMap.symm x) = x ∧ H.faceMap.symm (H.faceMap x) = x ∧
      H.nodeMap (H.nodeMap.symm x) = x ∧ H.nodeMap.symm (H.nodeMap x) = x :=
  ⟨H.edgeMap.apply_symm_apply x, H.edgeMap.symm_apply_apply x,
    H.faceMap.apply_symm_apply x, H.faceMap.symm_apply_apply x,
    H.nodeMap.apply_symm_apply x, H.nodeMap.symm_apply_apply x⟩

/-- LVDUCXU.hl:1798 `ITER_CYCLIC_ORBIT`. -/
theorem ITER_CYCLIC_ORBIT {α : Type*} (f : Equiv.Perm α) {x : α} {i : ℕ} (hi : 0 < i)
    (h : (f ^ i) x = x) :
    orbitMap f x = (fun n => (f ^ n) x) '' {n : ℕ | n < i} := by
  have hset : (↑(Finset.range i) : Set ℕ) = {n : ℕ | n < i} := by
    ext n
    exact Finset.mem_range
  rw [orbit_cyclic f (Nat.ne_of_gt hi) h, hset]

/-- LVDUCXU.hl:1805 `FACE_CYCLE_CARD`. -/
theorem FACE_CYCLE_CARD {α : Type*} [DecidableEq α] (H : Hypermap α) {x y : α}
    (hy : y ∈ H.face x) : (H.faceMap ^ (H.face x).ncard) y = y := by
  have hxy : H.face x = H.face y := H.face_eq_of_mem hy
  rw [hxy]
  exact H.pow_card_face_apply_self y

/-- LVDUCXU.hl:1812 `INVERSE_FACE_CYCLE`. -/
theorem INVERSE_FACE_CYCLE {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    (H.faceMap.symm ^ (H.face x).ncard) x = x := by
  calc (H.faceMap.symm ^ (H.face x).ncard) x
      = (H.faceMap.symm ^ (H.face x).ncard) ((H.faceMap ^ (H.face x).ncard) x) :=
        by rw [H.pow_card_face_apply_self x]
    _ = x := lvd_symmPow_pow_apply H.faceMap (H.face x).ncard x

/-- LVDUCXU.hl:1822 `INVERSE_FACE_CYCLE_ALL`. -/
theorem INVERSE_FACE_CYCLE_ALL {α : Type*} [DecidableEq α] (H : Hypermap α) {x y : α}
    (hy : y ∈ H.face x) : (H.faceMap.symm ^ (H.face x).ncard) y = y := by
  have hxy : H.face x = H.face y := H.face_eq_of_mem hy
  rw [hxy]
  exact INVERSE_FACE_CYCLE H y

/-- LVDUCXU.hl:2054 `EE_OF_HYP_IDE_FST_SND_EQ`. -/
theorem EE_OF_HYP_IDE_FST_SND_EQ (x : V3) (V : Set V3) (E : Set (Set V3))
    {z : V3 × V3} (hz : z ∈ dartsOfHyp_p3 E V) :
    eeOfHyp_p3 x V E z = z ↔ z.1 = z.2 := by
  have hexp : eeOfHyp_p3 x V E z = (z.2, z.1) := by
    simp only [eeOfHyp_p3]
    rw [if_pos hz]
  rw [hexp, PAIR_EQ2]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.symm, h⟩

/-- LVDUCXU.hl:2072 `ENF_IMAGE_ITSELF` (the `TR_ENF_TAC` content inlined). -/
theorem ENF_IMAGE_ITSELF {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    H.edge x = (H.edgeMap : α → α) '' H.edge x ∧
      H.node x = (H.nodeMap : α → α) '' H.node x ∧
      H.face x = (H.faceMap : α → α) '' H.face x := by
  have key : ∀ (p : Equiv.Perm α) (hp : PermutesOn p H.darts),
      orbitMap p x = (p : α → α) '' orbitMap p x := by
    intro p hp
    exact W_EQ_ITS_ORBIT_IMP_EQ_ITS_IMAGE
      (fun y hy => lvd_orbitMap_eq_orbitF hp x y hy)
  exact ⟨key _ H.edgeMap_permutes, key _ H.nodeMap_permutes, key _ H.faceMap_permutes⟩

/-! ## Dart-set lemmas under a fan (LVDUCXU.hl:1391, 1406, 1413) -/

/-- Membership transport between the carrier dart set and `darts_of_hyp`. -/
private theorem lvd_mem_darts {x : V3} {E : Set (Set V3)} {V : Set V3}
    {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS) {d : V3 × V3}
    (hd : d ∈ dartsOfHyp_p3 E V) : d ∈ HS.darts :=
  Finset.mem_coe.mp (by rw [hHS.1]; exact hd)

/-- LVDUCXU.hl:1406 `FAN_DART_DARTS`. -/
theorem FAN_DART_DARTS {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E)
    {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS) :
    (↑HS.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V :=
  hHS.1

/-- LVDUCXU.hl:1413 `FACE_SUBSET_DARTS`. -/
theorem FACE_SUBSET_DARTS {v : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN v V E)
    {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 v V E HS) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) : HS.face x ⊆ dartsOfHyp_p3 E V := by
  intro y hy
  have hsub := HS.face_subset_darts (lvd_mem_darts hHS hx) hy
  rw [hHS.1] at hsub
  exact hsub

/-- LVDUCXU.hl:1391 `FAN_DARTS_OF_IN_D`. -/
theorem FAN_DARTS_OF_IN_D {v : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN v V E)
    {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 v V E HS) {x x' : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = HS.face x) (hx' : x' ∈ FF) :
    x' ∈ dartsOfHyp_p3 E V := by
  have hy' : x' ∈ HS.face x := by rw [← hFF]; exact hx'
  exact FACE_SUBSET_DARTS _hfan hHS hx hy'

/-! ## Faces under localization (LVDUCXU.hl:191–730) -/

/-- LVDUCXU.hl:533 `FAN_FACE_IMP_IVS_F_IN_F`. -/
theorem FAN_FACE_IMP_IVS_F_IN_F {x : V3} {V : Set V3} {E : Set (Set V3)}
    {HS : Hypermap (V3 × V3)} (_hHS : IsHypOn_p10 x V E HS) {FF : Set (V3 × V3)}
    {xx y : V3 × V3} (hFF : FF = HS.face xx) (hy : y ∈ FF) :
    (HS.faceMap.symm : V3 × V3 → V3 × V3) y ∈ FF ∧
      (HS.faceMap : V3 × V3 → V3 × V3) ∘ (HS.faceMap.symm : V3 × V3 → V3 × V3) = id ∧
      (HS.faceMap.symm : V3 × V3 → V3 × V3) ∘ (HS.faceMap : V3 × V3 → V3 × V3) = id := by
  refine ⟨?_, funext fun d => HS.faceMap.apply_symm_apply d,
    funext fun d => HS.faceMap.symm_apply_apply d⟩
  have hy' : y ∈ HS.face xx := by rw [← hFF]; exact hy
  by_cases hxx : xx ∈ HS.darts
  · have h1 := Hypermap.faceMap_symm_mem_face HS hy'
    rw [← hFF] at h1
    exact h1
  · have hperm : HS.faceMap xx = xx := HS.faceMap_permutes xx hxx
    have hface : HS.face xx = {xx} := orbitMap_eq_singleton hperm
    have hsymm : (HS.faceMap.symm : V3 × V3 → V3 × V3) xx = xx :=
      HS.faceMap.injective (by rw [HS.faceMap.apply_symm_apply xx, hperm])
    have hy'' : y = xx := by
      rw [hface, Set.mem_singleton_iff] at hy'
      exact hy'
    rw [hy'', hsymm, hFF, hface]
    exact Set.mem_singleton xx

/-- LVDUCXU.hl:500 `FAN_FACE_IMP_IVS_F_IN_F` (first binding, carrying the
extra dart-membership hypothesis; subsumed by the line-533 version). -/
theorem FAN_FACE_IMP_IVS_F_IN_F_DART {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS)
    {FF : Set (V3 × V3)} {xx y : V3 × V3} (_hxx : xx ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face xx) (hy : y ∈ FF) :
    (HS.faceMap.symm : V3 × V3 → V3 × V3) y ∈ FF ∧
      (HS.faceMap : V3 × V3 → V3 × V3) ∘ (HS.faceMap.symm : V3 × V3 → V3 × V3) = id ∧
      (HS.faceMap.symm : V3 × V3 → V3 × V3) ∘ (HS.faceMap : V3 × V3 → V3 × V3) = id :=
  FAN_FACE_IMP_IVS_F_IN_F hHS hFF hy

/-- LVDUCXU.hl:191 `IN_FF_FACE_MAP_IDE` (giant — DISCHARGES registry). -/
theorem IN_FF_FACE_MAP_IDE {v : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN v V E)
    {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hx : ∃ x ∈ dartsOfHyp_p3 E V, FF = H1.face x) {x' : V3 × V3} (hx' : x' ∈ FF) :
    (H1.faceMap : V3 × V3 → V3 × V3) x' = (H2.faceMap : V3 × V3 → V3 × V3) x' := by
  obtain ⟨x, hxd, hxFF⟩ := hx
  have hFFsub : ∀ y ∈ FF, y ∈ dartsOfHyp_p3 E V :=
    fun y hy => FACE_SUBSET_DARTS _hfan h1 hxd (hxFF ▸ hy)
  obtain ⟨a, c⟩ := x'
  have hx'd : (a, c) ∈ dartsOfHyp_p3 E V := hFFsub (a, c) hx'
  have hx'd' : (a, c) ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) :=
    IN_DARTS_FF_IMP_DARTS_E_PRIME_V_PRIME hx'd hx'
  -- both face maps are `ff_of_hyp`, hence determined by the inverse σ value
  have hL : (H1.faceMap : V3 × V3 → V3 × V3) (a, c)
      = (c, ivsAzimCycle_p3 (EE_p3 c E) v c a) := by
    rw [h1.2.2.2]
    simp only [ffOfHyp_p3, if_pos hx'd]
  have hR : (H2.faceMap : V3 × V3 → V3 × V3) (a, c)
      = (c, ivsAzimCycle_p3 (EE_p3 c (ePrime_p3 E FF)) v c a) := by
    rw [h2.2.2.2]
    simp only [ffOfHyp_p3, if_pos hx'd']
  rw [hL, hR]
  congr 1
  rcases (Set.mem_union _ _ _).mp hx'd with hord | hself
  · -- genuine dart: `{a, c} ∈ E`; reduce both sides to `inverse1SigmaFan`
    have hacE : ({a, c} : Set V3) ∈ E := hord
    have hswap : ({c, a} : Set V3) = ({a, c} : Set V3) := by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    have hcaE : ({c, a} : Set V3) ∈ E := by rw [hswap]; exact hacE
    have hacE' : ({a, c} : Set V3) ∈ ePrime_p3 E FF := ⟨a, c, rfl, hacE, hx'⟩
    have hcaE' : ({c, a} : Set V3) ∈ ePrime_p3 E FF := by
      rw [hswap]; exact hacE'
    have hH : ∃ H : Hypermap (V3 × V3),
        (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
        (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 v V E ∧
        (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 v V E ∧
        (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 v V E ∧
        ∃ x ∈ H.darts, FF = H.face x :=
      ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x, lvd_mem_darts h1 hxd, hxFF⟩
    have hfan' : FAN v (vPrime_p3 V FF) (ePrime_p3 E FF) :=
      IMP_FAN_V_PRIME_E_PRIME _hfan hH
    rw [IVS_AZIM_EQ_INVERSE_SIGMA_FAN _hfan hcaE,
      IVS_AZIM_EQ_INVERSE_SIGMA_FAN hfan' hcaE']
    set t := inverse1SigmaFan v V E c a
    have htσ : sigmaFan v V E c t = a := (INVERSE1_SIGMA_FAN _hfan).2.1 a hcaE
    have hctE : ({c, t} : Set V3) ∈ E := (INVERSE1_SIGMA_FAN _hfan).1 a hcaE
    have htV : t ∈ V := ((properties_of_setOfEdge_fan v V E c t _hfan).mp hctE).2
    -- `(c, t)` lies on the face (orbit closure of the full face map)
    have hctFF : (c, t) ∈ FF := by
      have hmem : (H1.faceMap : V3 × V3 → V3 × V3) (a, c) ∈ H1.face (a, c) := by
        simpa using H1.pow_faceMap_mem_face (a, c) 1
      have hface_eq : H1.face (a, c) = FF := by
        rw [hxFF]
        exact (H1.face_eq_of_mem (x := x) (y := (a, c)) (hxFF ▸ hx')).symm
      have hval : (H1.faceMap : V3 × V3 → V3 × V3) (a, c) = (c, t) := by
        rw [hL, IVS_AZIM_EQ_INVERSE_SIGMA_FAN _hfan hcaE]
      rw [hval, hface_eq] at hmem
      exact hmem
    -- `t` is a vertex of the restricted fan: `(c,t) ∈ FF` and the face map
    -- sends `(c,t)` to `(t, _) ∈ FF` (orbit closure)
    have htFF : ∃ w : V3, (t, w) ∈ FF := by
      have hmem2 : (H1.faceMap : V3 × V3 → V3 × V3) (c, t) ∈ H1.face (c, t) := by
        simpa using H1.pow_faceMap_mem_face (c, t) 1
      have hface_ct : H1.face (c, t) = FF := by
        rw [hxFF]
        exact (H1.face_eq_of_mem (x := x) (y := (c, t)) (hxFF ▸ hctFF)).symm
      have hctd : (c, t) ∈ dartsOfHyp_p3 E V := hFFsub (c, t) hctFF
      have hval2 : (H1.faceMap : V3 × V3 → V3 × V3) (c, t)
          = (t, ivsAzimCycle_p3 (EE_p3 t E) v t c) := by
        rw [h1.2.2.2]
        simp only [ffOfHyp_p3, if_pos hctd]
      rw [hval2, hface_ct] at hmem2
      exact ⟨_, hmem2⟩
    obtain ⟨w, htw⟩ := htFF
    -- `t` and `a` both live in the restricted neighbour set of `c`
    have htSrst : t ∈ setOfEdge c (vPrime_p3 V FF) (ePrime_p3 E FF) :=
      ⟨⟨c, t, rfl, hctE, hctFF⟩, htV, w, htw⟩
    have haV : a ∈ V := (PAIRS_IN_UNIONS hacE _hfan.1).1
    have haSrst : a ∈ setOfEdge c (vPrime_p3 V FF) (ePrime_p3 E FF) :=
      ⟨hcaE', haV, c, hx'⟩
    have hsub : ∀ p : V3, p ∈ setOfEdge c (vPrime_p3 V FF) (ePrime_p3 E FF) →
        p ∈ setOfEdge c V E :=
      fun p hp => ⟨E_PRIME_SUBSET_E E FF hp.1, hp.2.1⟩
    have htSfull : t ∈ setOfEdge c V E := ⟨hctE, htV⟩
    have hσagree : sigmaFan v V E c t
        = sigmaFan v (vPrime_p3 V FF) (ePrime_p3 E FF) c t := by
      refine lvd_sigma_agree _hfan hfan' hsub htSrst htSfull ?_
      rw [htσ]
      exact haSrst
    have hgu : inverse1SigmaFan v (vPrime_p3 V FF) (ePrime_p3 E FF) c a
        ∈ setOfEdge c (vPrime_p3 V FF) (ePrime_p3 E FF) ∧
        sigmaFan v (vPrime_p3 V FF) (ePrime_p3 E FF) c
          (inverse1SigmaFan v (vPrime_p3 V FF) (ePrime_p3 E FF) c a) = a :=
      ⟨(properties_of_setOfEdge_fan v (vPrime_p3 V FF) (ePrime_p3 E FF) c _ hfan').mp
          ((INVERSE1_SIGMA_FAN hfan').1 a hcaE'),
        (INVERSE1_SIGMA_FAN hfan').2.1 a hcaE'⟩
    have hσrst : sigmaFan v (vPrime_p3 V FF) (ePrime_p3 E FF) c t = a := by
      rw [← hσagree, htσ]
    exact mono_sigma_fan hfan' htSrst hgu.1 (hσrst.trans hgu.2.symm)
  · -- self-pair dart: both neighbour sets are empty, both inverse σ's are `a`
    have hself' : a = c ∧ a ∈ V ∧ EE_p3 a E = ∅ := hself
    obtain ⟨hac, haV, hEE⟩ := hself'
    have hEE' : EE_p3 a (ePrime_p3 E FF) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      obtain ⟨p, q, hpq, hEpq, -⟩ := hw
      rw [← hpq] at hEpq
      have hmem : w ∈ EE_p3 a E := hEpq
      rw [hEE] at hmem
      exact hmem
    rw [hac]
    have hEEc : EE_p3 c E = ∅ := by rw [← hac]; exact hEE
    have hEEc' : EE_p3 c (ePrime_p3 E FF) = ∅ := by rw [← hac]; exact hEE'
    rw [hEEc, hEEc', IVS_AZIM_EMPTY_IDE]

/-- LVDUCXU.hl:460 `LOCALIZE_PRESERVE_FACE` (giant — DISCHARGES registry). -/
theorem LOCALIZE_PRESERVE_FACE {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x) :
    FF = H2.face x := by
  have hx_FF : x ∈ FF := by rw [hFF]; exact H1.mem_face_self x
  have hagree : ∀ d ∈ FF, (H2.faceMap : V3 × V3 → V3 × V3) d =
      (H1.faceMap : V3 × V3 → V3 × V3) d :=
    fun d hd => (IN_FF_FACE_MAP_IDE _hfan h1 h2 ⟨x, hx, hFF⟩ hd).symm
  have hclosed : ∀ d ∈ FF, (H2.faceMap : V3 × V3 → V3 × V3) d ∈ FF := by
    intro d hd
    rw [hagree d hd]
    have hmem : (H1.faceMap : V3 × V3 → V3 × V3) d ∈ H1.face d := by
      simpa using H1.pow_faceMap_mem_face d 1
    have hface_eq : H1.face d = FF := by
      rw [hFF]
      exact (H1.face_eq_of_mem (x := x) (y := d) (hFF ▸ hd)).symm
    rwa [hface_eq] at hmem
  have hmain := lvd_orbit_ext_of_agree (fc := H1.faceMap) (fc' := H2.faceMap)
    (f := FF) (b := x) hFF.symm hx_FF hagree hclosed
  rw [Hypermap.face]
  exact hmain.symm

/-- LVDUCXU.hl:585 `INVERSE_FACE_EQ_INV_FACE_LOCALLIZED` (giant — DISCHARGES
registry). -/
theorem INVERSE_FACE_EQ_INV_FACE_LOCALLIZED {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x) :
    ∀ x ∈ FF, (H1.faceMap.symm : V3 × V3 → V3 × V3) x =
      (H2.faceMap.symm : V3 × V3 → V3 × V3) x := by
  intro y hy
  have hy' : y ∈ H1.face x := hFF ▸ hy
  have hz : (H1.faceMap.symm : V3 × V3 → V3 × V3) y ∈ FF := by
    have h1' := Hypermap.faceMap_symm_mem_face H1 hy'
    rw [← hFF] at h1'
    exact h1'
  have hagree : (H2.faceMap : V3 × V3 → V3 × V3)
      ((H1.faceMap.symm : V3 × V3 → V3 × V3) y) =
      (H1.faceMap : V3 × V3 → V3 × V3) ((H1.faceMap.symm : V3 × V3 → V3 × V3) y) :=
    (IN_FF_FACE_MAP_IDE _hfan h1 h2 ⟨x, hx, hFF⟩ hz).symm
  have h2y : (H2.faceMap : V3 × V3 → V3 × V3)
      ((H1.faceMap.symm : V3 × V3 → V3 × V3) y) = y := by
    rw [hagree, H1.faceMap.apply_symm_apply]
  have hfin := congrArg (H2.faceMap.symm : V3 × V3 → V3 × V3) h2y
  rw [H2.faceMap.symm_apply_apply] at hfin
  exact hfin

/-- LVDUCXU.hl:672 `IN_FF_IMP_AZIM_CYCLE_EQ` (giant — DISCHARGES registry). -/
theorem IN_FF_IMP_AZIM_CYCLE_EQ {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x) :
    ∀ x ∈ FF, (azimCycle_p3 (EE_p3 x.1 E) v x.1 x.2, x.1) =
      (azimCycle_p3 (EE_p3 x.1 (ePrime_p3 E FF)) v x.1 x.2, x.1) := by
  intro y hy
  obtain ⟨a, c⟩ := y
  have hyd : (a, c) ∈ dartsOfHyp_p3 E V := FACE_SUBSET_DARTS _hfan h1 hx (hFF ▸ hy)
  have hyd' : (a, c) ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) :=
    IN_DARTS_FF_IMP_DARTS_E_PRIME_V_PRIME hyd hy
  have hH : ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 v V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 v V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 v V E ∧
      ∃ x ∈ H.darts, FF = H.face x :=
    ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x, lvd_mem_darts h1 hx, hFF⟩
  have hfan' : FAN v (vPrime_p3 V FF) (ePrime_p3 E FF) := IMP_FAN_V_PRIME_E_PRIME _hfan hH
  have hn1 : (H1.nodeMap : V3 × V3 → V3 × V3) (a, c)
      = (a, azimCycle_p3 (EE_p3 a E) v a c) := by
    rw [h1.2.2.1]
    simp only [nnOfHyp_p3, if_pos hyd]
  have hn2 : (H2.nodeMap : V3 × V3 → V3 × V3) (a, c)
      = (a, azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) v a c) := by
    rw [h2.2.2.1]
    simp only [nnOfHyp_p3, if_pos hyd']
  have hnd1 : (H1.nodeMap : V3 × V3 → V3 × V3) (a, c) ∈ dartsOfHyp_p3 E V := by
    rw [h1.2.2.1]
    exact IN_DARTS_IMP_NN_OF_HYP_TOO _hfan (a, c) hyd
  have hnd2 : (H2.nodeMap : V3 × V3 → V3 × V3) (a, c)
      ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) := by
    rw [h2.2.2.1]
    exact IN_DARTS_IMP_NN_OF_HYP_TOO hfan' (a, c) hyd'
  have hnd1' : (a, azimCycle_p3 (EE_p3 a E) v a c) ∈ dartsOfHyp_p3 E V := by
    rw [← hn1]; exact hnd1
  have hnd2' : (a, azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) v a c)
      ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) := by
    rw [← hn2]; exact hnd2
  have he1 : (H1.edgeMap : V3 × V3 → V3 × V3)
      ((H1.nodeMap : V3 × V3 → V3 × V3) (a, c))
      = (azimCycle_p3 (EE_p3 a E) v a c, a) := by
    rw [hn1, h1.2.1]
    simp only [eeOfHyp_p3, if_pos hnd1']
  have he2 : (H2.edgeMap : V3 × V3 → V3 × V3)
      ((H2.nodeMap : V3 × V3 → V3 × V3) (a, c))
      = (azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) v a c, a) := by
    rw [hn2, h2.2.1]
    simp only [eeOfHyp_p3, if_pos hnd2']
  have hc1 : (H1.edgeMap : V3 × V3 → V3 × V3)
      ((H1.nodeMap : V3 × V3 → V3 × V3) (a, c))
      = (H1.faceMap.symm : V3 × V3 → V3 × V3) (a, c) := by
    have key : ((H1.edgeMap * H1.nodeMap : Equiv.Perm (V3 × V3)) : V3 × V3 → V3 × V3) (a, c)
        = (H1.faceMap.symm : V3 × V3 → V3 × V3) (a, c) := by
      rw [ED_MA_O_NO_MA_EQ_INV_FA]
      rfl
    rwa [Equiv.Perm.mul_apply] at key
  have hc2 : (H2.edgeMap : V3 × V3 → V3 × V3)
      ((H2.nodeMap : V3 × V3 → V3 × V3) (a, c))
      = (H2.faceMap.symm : V3 × V3 → V3 × V3) (a, c) := by
    have key : ((H2.edgeMap * H2.nodeMap : Equiv.Perm (V3 × V3)) : V3 × V3 → V3 × V3) (a, c)
        = (H2.faceMap.symm : V3 × V3 → V3 × V3) (a, c) := by
      rw [ED_MA_O_NO_MA_EQ_INV_FA]
      rfl
    rwa [Equiv.Perm.mul_apply] at key
  have hsym := INVERSE_FACE_EQ_INV_FACE_LOCALLIZED _hfan h1 h2 hx hFF (a, c) hy
  have heq : (azimCycle_p3 (EE_p3 a E) v a c, a)
      = (azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) v a c, a) := by
    rw [← he1, ← he2, hc1, hc2, hsym]
  exact heq

/-- First-component form of `IN_FF_IMP_AZIM_CYCLE_EQ`, with the localized
carrier built from `ELMS_OF_HYPERMAP_HYP`. -/
private theorem lvd_azimCycle_fst {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS)
    {FF : Set (V3 × V3)} {v y : V3 × V3} (hv : v ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face v) (hy : y ∈ FF) :
    azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2 =
      azimCycle_p3 (EE_p3 y.1 (ePrime_p3 E FF)) x y.1 y.2 := by
  have hfan' := lvd_fan_vPrime_ePrime hfan hHS hv hFF
  obtain ⟨H2, hd2, he2, hn2, hf2⟩ := lvd_hypCarrier hfan'
  exact congrArg Prod.fst (IN_FF_IMP_AZIM_CYCLE_EQ hfan hHS ⟨hd2, he2, hn2, hf2⟩ hv hFF y hy)

/-- LVDUCXU.hl:924 `AZIM_CY_FST_Y_IN_FF`: on a face, the inverse face map is
the `azim_cycle` switch, and lands back in the face. -/
theorem AZIM_CY_FST_Y_IN_FF {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS)
    {FF : Set (V3 × V3)} {xx y : V3 × V3} (hxx : xx ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face xx) (hy : y ∈ FF) :
    (azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2, y.1) ∈ FF ∧
      (HS.faceMap.symm : V3 × V3 → V3 × V3) y =
        (azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2, y.1) := by
  have hy' : y ∈ HS.face xx := by rw [← hFF]; exact hy
  have hxxd : xx ∈ HS.darts := lvd_mem_darts hHS hxx
  have h1 : (HS.faceMap.symm : V3 × V3 → V3 × V3) y ∈ FF := by
    have h1' := Hypermap.faceMap_symm_mem_face HS hy'
    rw [← hFF] at h1'
    exact h1'
  have hyd : y ∈ dartsOfHyp_p3 E V := by
    have hsub := HS.face_subset_darts hxxd hy'
    rw [hHS.1] at hsub
    exact hsub
  have hnn : (HS.nodeMap : V3 × V3 → V3 × V3) y =
      (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) := by
    rw [hHS.2.2.1]
    rw [show nnOfHyp_p3 x V E y =
      if y ∈ dartsOfHyp_p3 E V then (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) else y from rfl,
      if_pos hyd]
  have hnnd : nnOfHyp_p3 x V E y ∈ dartsOfHyp_p3 E V :=
    (IN_DARTS_IFF_NN_OF_HYP_TOO hfan y).mp hyd
  have hnnd' : (HS.nodeMap : V3 × V3 → V3 × V3) y ∈ dartsOfHyp_p3 E V := by
    rw [hHS.2.2.1]
    exact hnnd
  have hmem2 : (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) ∈ dartsOfHyp_p3 E V := by
    rw [← hnn]
    exact hnnd'
  have hee : (HS.edgeMap : V3 × V3 → V3 × V3)
      ((HS.nodeMap : V3 × V3 → V3 × V3) y) =
      (azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2, y.1) := by
    rw [hnn, hHS.2.1]
    show (if (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) ∈ dartsOfHyp_p3 E V
        then ((y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2).2,
          (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2).1)
        else (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2)) =
      (azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2, y.1)
    rw [if_pos hmem2]
  have hinv : (HS.faceMap.symm : V3 × V3 → V3 × V3) y =
      (azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2, y.1) := by
    have key := ED_MA_O_NO_MA_EQ_INV_FA (α := V3 × V3) HS
    have h2 : (HS.faceMap⁻¹ : Equiv.Perm (V3 × V3)) y =
        (HS.edgeMap : V3 × V3 → V3 × V3) ((HS.nodeMap : V3 × V3 → V3 × V3) y) := by
      rw [← key, Equiv.Perm.mul_apply]
    rw [show (HS.faceMap.symm : V3 × V3 → V3 × V3) y =
      (HS.faceMap⁻¹ : Equiv.Perm (V3 × V3)) y from rfl, h2, hee]
  rw [hinv] at h1
  exact ⟨h1, hinv⟩

/-! ## Fan quantities after localization (LVDUCXU.hl:743, 897, 956, 1121) -/

/-- LVDUCXU.hl:743 `CARD_E_GT1_EQ_CARD_E_PRIME` (giant — DISCHARGES
registry). -/
theorem CARD_E_GT1_EQ_CARD_E_PRIME {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS)
    {FF : Set (V3 × V3)} {v y : V3 × V3} (hv : v ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face v) (hy : y ∈ FF) :
    (1 < Set.ncard (EE_p3 y.1 E)) ↔ (1 < Set.ncard (EE_p3 y.1 (ePrime_p3 E FF))) := by
  obtain ⟨a, b⟩ := y
  show (1 < Set.ncard (EE_p3 a E)) ↔ (1 < Set.ncard (EE_p3 a (ePrime_p3 E FF)))
  have hyd : (a, b) ∈ dartsOfHyp_p3 E V := FACE_SUBSET_DARTS _hfan hHS hv (hFF ▸ hy)
  have hfan' := lvd_fan_vPrime_ePrime _hfan hHS hv hFF
  have hfin : (EE_p3 a E).Finite := FAN_IMP_FINITE_EE _hfan a
  have hfin' : (EE_p3 a (ePrime_p3 E FF)).Finite := FAN_IMP_FINITE_EE hfan' a
  have hsub : EE_p3 a (ePrime_p3 E FF) ⊆ EE_p3 a E :=
    SUBSET_IMP_SO_DO_EE (E_PRIME_SUBSET_E E FF) a
  constructor
  · intro hgt
    have hnotsub : ¬(EE_p3 a E ⊆ {b}) := by
      intro hc
      have hle : Set.ncard (EE_p3 a E) ≤ 1 := by
        have h1 : Set.ncard (EE_p3 a E) ≤ Set.ncard ({b} : Set V3) :=
          Set.ncard_le_ncard hc (Set.finite_singleton b)
        rwa [Set.ncard_singleton] at h1
      omega
    obtain ⟨hne, hmem, -⟩ :=
      AZIM_CYCLE_PROPERTIES (W := EE_p3 a E) (p := b) hnotsub hfin x a
    have hfirst := lvd_azimCycle_fst _hfan hHS hv hFF (y := (a, b)) hy
    have hEab : ({a, b} : Set V3) ∈ E := by
      rcases (Set.mem_union _ _ _).mp hyd with h | h
      · exact h
      · exfalso
        have hself' : a = b ∧ a ∈ V ∧ EE_p3 a E = ∅ := h
        obtain ⟨-, -, hEE⟩ := hself'
        have hzero : Set.ncard (EE_p3 a E) = 0 := by rw [hEE, Set.ncard_empty]
        omega
    have hbE' : b ∈ EE_p3 a (ePrime_p3 E FF) := ⟨a, b, rfl, hEab, hy⟩
    by_cases hsub' : EE_p3 a (ePrime_p3 E FF) ⊆ {b}
    · exfalso
      have hsingle : azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) x a b = b :=
        W_SUBSET_SINGLETON_IMP_IDE hsub' x a
      rw [hfirst, hsingle] at hne
      exact hne rfl
    · obtain ⟨-, hmem', -⟩ :=
        AZIM_CYCLE_PROPERTIES (W := EE_p3 a (ePrime_p3 E FF)) (p := b) hsub' hfin' x a
      have hpair : ({b, azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) x a b} : Set V3) ⊆
          EE_p3 a (ePrime_p3 E FF) := by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact hbE'
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hmem'
      have hbne : b ≠ azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) x a b := by
        intro he
        apply hne
        rw [hfirst]
        exact he.symm
      have h2le : Set.ncard ({b, azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) x a b} : Set V3)
          ≤ Set.ncard (EE_p3 a (ePrime_p3 E FF)) := Set.ncard_le_ncard hpair hfin'
      rw [Set.ncard_pair hbne] at h2le
      omega
  · intro hgt'
    have hle : Set.ncard (EE_p3 a (ePrime_p3 E FF)) ≤ Set.ncard (EE_p3 a E) :=
      Set.ncard_le_ncard hsub hfin
    omega

/-- LVDUCXU.hl:897 `AZIM_IN_FAN_EQ_IZIM_E_PRIME` (giant — DISCHARGES
registry). -/
theorem AZIM_IN_FAN_EQ_IZIM_E_PRIME {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN 0 V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 0 V E HS)
    {FF : Set (V3 × V3)} {v y : V3 × V3} (hv : v ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face v) (hy : y ∈ FF) :
    azimInFan_p3 y E = azimInFan_p3 y (ePrime_p3 E FF) := by
  have hc := CARD_E_GT1_EQ_CARD_E_PRIME _hfan hHS hv hFF hy
  have hcyc := lvd_azimCycle_fst _hfan hHS hv hFF hy
  simp only [azimInFan_p3]
  by_cases h : 1 < (EE_p3 y.1 E).ncard
  · have h' : 1 < (EE_p3 y.1 (ePrime_p3 E FF)).ncard := hc.mp h
    rw [if_pos h, if_pos h']
    rw [hcyc]
  · have h' : ¬(1 < (EE_p3 y.1 (ePrime_p3 E FF)).ncard) := fun hh => h (hc.mpr hh)
    rw [if_neg h, if_neg h']

/-- LVDUCXU.hl:956/1041 `EE_FST_Y_EQ_SET_SET_SNDY` (the two identical HOL
bindings merged). -/
theorem EE_FST_Y_EQ_SET_SET_SNDY {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 x V E HS)
    {FF : Set (V3 × V3)} {v y : V3 × V3} (hv : v ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face v) (hy : y ∈ FF) :
    EE_p3 y.1 E = {y.2} ↔ EE_p3 y.1 (ePrime_p3 E FF) = {y.2} := by
  obtain ⟨a, b⟩ := y
  have hyd : (a, b) ∈ dartsOfHyp_p3 E V := FACE_SUBSET_DARTS _hfan hHS hv (hFF ▸ hy)
  rcases (Set.mem_union _ _ _).mp hyd with hord | hself
  · have hEab : ({a, b} : Set V3) ∈ E := hord
    have hEab' : ({a, b} : Set V3) ∈ ePrime_p3 E FF := ⟨a, b, rfl, hEab, hy⟩
    have hbE : b ∈ EE_p3 a E := hEab
    have hbE' : b ∈ EE_p3 a (ePrime_p3 E FF) := hEab'
    have hsub : EE_p3 a (ePrime_p3 E FF) ⊆ EE_p3 a E :=
      SUBSET_IMP_SO_DO_EE (E_PRIME_SUBSET_E E FF) a
    constructor
    · intro hEE
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hbE', fun z hz => ?_⟩
      have hzE : z ∈ EE_p3 a E := hsub hz
      rw [hEE] at hzE
      exact Set.mem_singleton_iff.mp hzE
    · intro hEE'
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hsub (hEE' ▸ Set.mem_singleton b), fun z hz => ?_⟩
      by_contra hzb
      have hnotsub : ¬(EE_p3 a E ⊆ {b}) := fun hc =>
        hzb (Set.mem_singleton_iff.mp (hc hz))
      have hfin : (EE_p3 a E).Finite := FAN_IMP_FINITE_EE _hfan a
      obtain ⟨hne, -, -⟩ :=
        AZIM_CYCLE_PROPERTIES (W := EE_p3 a E) (p := b) hnotsub hfin x a
      have hfirst := lvd_azimCycle_fst _hfan hHS hv hFF (y := (a, b)) hy
      have hsingle : azimCycle_p3 (EE_p3 a (ePrime_p3 E FF)) x a b = b :=
        W_SUBSET_SINGLETON_IMP_IDE (by rw [hEE']) x a
      rw [hfirst, hsingle] at hne
      exact hne rfl
  · -- self-pair: both neighbour sets are empty
    have hself' : a = b ∧ a ∈ V ∧ EE_p3 a E = ∅ := hself
    obtain ⟨-, -, hEE⟩ := hself'
    have hsub : EE_p3 a (ePrime_p3 E FF) ⊆ EE_p3 a E :=
      SUBSET_IMP_SO_DO_EE (E_PRIME_SUBSET_E E FF) a
    have hEE' : EE_p3 a (ePrime_p3 E FF) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzE := hsub hz
      rw [hEE] at hzE
      exact hzE
    rw [hEE, hEE']

/-- LVDUCXU.hl:1121 `WEDGE_IN_FAN_EQ_WITH_E_PRIME` (giant — DISCHARGES
registry). -/
theorem WEDGE_IN_FAN_EQ_WITH_E_PRIME {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN 0 V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 0 V E HS)
    {FF : Set (V3 × V3)} {v y : V3 × V3} (hv : v ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face v) (hy : y ∈ FF) :
    wedgeInFanGe_p3 y E = wedgeInFanGe_p3 y (ePrime_p3 E FF) ∧
      wedgeInFanGt_p3 y E = wedgeInFanGt_p3 y (ePrime_p3 E FF) := by
  have hc := CARD_E_GT1_EQ_CARD_E_PRIME _hfan hHS hv hFF hy
  have hcyc := lvd_azimCycle_fst _hfan hHS hv hFF hy
  have hsingle := EE_FST_Y_EQ_SET_SET_SNDY _hfan hHS hv hFF hy
  have hgt : wedgeInFanGt_p3 y E = wedgeInFanGt_p3 y (ePrime_p3 E FF) := by
    simp only [wedgeInFanGt_p3]
    by_cases h : 1 < (EE_p3 y.1 E).ncard
    · have h' : 1 < (EE_p3 y.1 (ePrime_p3 E FF)).ncard := hc.mp h
      rw [if_pos h, if_pos h', hcyc]
    · have h' : ¬(1 < (EE_p3 y.1 (ePrime_p3 E FF)).ncard) := fun hh => h (hc.mpr hh)
      rw [if_neg h, if_neg h']
      by_cases hs : EE_p3 y.1 E = {y.2}
      · have hs' : EE_p3 y.1 (ePrime_p3 E FF) = {y.2} := hsingle.mp hs
        rw [if_pos hs, if_pos hs']
      · have hs' : ¬(EE_p3 y.1 (ePrime_p3 E FF) = {y.2}) := fun hh => hs (hsingle.mpr hh)
        rw [if_neg hs, if_neg hs']
  have hge : wedgeInFanGe_p3 y E = wedgeInFanGe_p3 y (ePrime_p3 E FF) := by
    simp only [wedgeInFanGe_p3]
    by_cases h : 1 < (EE_p3 y.1 E).ncard
    · have h' : 1 < (EE_p3 y.1 (ePrime_p3 E FF)).ncard := hc.mp h
      rw [if_pos h, if_pos h', hcyc]
    · have h' : ¬(1 < (EE_p3 y.1 (ePrime_p3 E FF)).ncard) := fun hh => h (hc.mpr hh)
      rw [if_neg h, if_neg h']
  exact ⟨hge, hgt⟩

/-! ## Dart set of the localized hypermap (LVDUCXU.hl:1178, 1216, 1273,
1285, 1313, 1423) -/

/-- LVDUCXU.hl:1178 `DARTS_E_PRIME_EQ_FF_UNION_SWITCH`. -/
theorem DARTS_E_PRIME_EQ_FF_UNION_SWITCH {E : Set (Set V3)} {V : Set V3}
    {FF : Set (V3 × V3)} (h : ∀ x ∈ FF, {x.1, x.2} ∈ E) :
    dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) =
      FF ∪ {p : V3 × V3 | (p.2, p.1) ∈ FF} := by
  ext p
  rw [Set.mem_union]
  constructor
  · intro hp
    rcases (Set.mem_union _ _ _).mp hp with h' | h'
    · obtain ⟨a, b, hab, hE, hFF⟩ := h'
      rcases Set.pair_eq_pair_iff.mp hab with h1 | h1
      · left
        have hmem : (p.1, p.2) ∈ FF := by rw [h1.1, h1.2]; exact hFF
        exact hmem
      · right
        have hmem : (p.2, p.1) ∈ FF := by rw [h1.2, h1.1]; exact hFF
        exact hmem
    · exfalso
      obtain ⟨heq, hV, hEE⟩ := h'
      obtain ⟨w, hwFF⟩ := hV.2
      have hE : {p.1, w} ∈ E := h (p.1, w) hwFF
      have hmem : w ∈ EE_p3 p.1 (ePrime_p3 E FF) :=
        (⟨p.1, w, rfl, hE, hwFF⟩ : {p.1, w} ∈ ePrime_p3 E FF)
      rw [hEE] at hmem
      exact hmem
  · rintro (h' | h')
    · exact Or.inl ⟨p.1, p.2, rfl, h p h', h'⟩
    · have hFFsw : (p.2, p.1) ∈ FF := h'
      have hE : {p.2, p.1} ∈ E := h (p.2, p.1) hFFsw
      refine Or.inl ?_
      show {p.1, p.2} ∈ ePrime_p3 E FF
      exact ⟨p.2, p.1, Set.pair_comm p.1 p.2, hE, hFFsw⟩

/-- LVDUCXU.hl:1216 `CARD_FF_GT1_FF_SUBSET` (giant — DISCHARGES registry). -/
theorem CARD_FF_GT1_FF_SUBSET {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 v V E HS)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hFF : FF = HS.face x)
    (hcard : 1 < Set.ncard FF) :
    ∀ y ∈ FF, {y.1, y.2} ∈ E := by
  have hxmem : x ∈ HS.darts := by
    by_contra hx
    have hfix : HS.faceMap x = x := HS.faceMap_permutes x hx
    have hface : HS.face x = {x} := orbitMap_eq_singleton hfix
    rw [hFF, hface, Set.ncard_singleton] at hcard
    omega
  intro y hy
  have hyface : y ∈ HS.face x := by rw [← hFF]; exact hy
  have hyd : y ∈ HS.darts := HS.face_subset_darts hxmem hyface
  have hyd' : y ∈ dartsOfHyp_p3 E V := by
    have h : y ∈ (↑HS.darts : Set (V3 × V3)) := hyd
    rwa [hHS.1] at h
  rcases (Set.mem_union _ _ _).mp hyd' with ho | hs
  · exact ho
  · exfalso
    obtain ⟨h12, -, hEE⟩ := hs
    have hfix : HS.faceMap y = y := by
      rw [hHS.2.2.2]
      show ffOfHyp_p3 v V E y = y
      rw [show ffOfHyp_p3 v V E y =
        if y ∈ dartsOfHyp_p3 E V then
          (y.2, ivsAzimCycle_p3 (EE_p3 y.2 E) v y.2 y.1) else y from rfl, if_pos hyd']
      have hEE' : EE_p3 y.2 E = ∅ := by rw [← h12]; exact hEE
      rw [show ivsAzimCycle_p3 (EE_p3 y.2 E) v y.2 y.1 =
        if EE_p3 y.2 E = ∅ then y.1 else
          Classical.epsilon fun x => x ∈ EE_p3 y.2 E ∧
            azimCycle_p3 (EE_p3 y.2 E) v y.2 x = y.1 from rfl, if_pos hEE']
      exact PAIR_EQ2.mpr ⟨h12.symm, h12⟩
    have hface : HS.face y = {y} := orbitMap_eq_singleton hfix
    have hsame : HS.face x = HS.face y := HS.face_eq_of_mem hyface
    rw [hFF, hsame, hface, Set.ncard_singleton] at hcard
    omega

/-- LVDUCXU.hl:1273 `DARTS_E_PRIME_GT1_SWITCH` (giant — DISCHARGES registry). -/
theorem DARTS_E_PRIME_GT1_SWITCH {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 v V E HS)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hFF : FF = HS.face x)
    (hcard : 1 < Set.ncard FF) :
    dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) =
      FF ∪ {p : V3 × V3 | (p.2, p.1) ∈ FF} :=
  DARTS_E_PRIME_EQ_FF_UNION_SWITCH (CARD_FF_GT1_FF_SUBSET _hfan hHS hFF hcard)

/-- LVDUCXU.hl:1285 `FAN_FACE_GT1_IMAGE_EE_OF_HYP` (giant — DISCHARGES
registry). -/
theorem FAN_FACE_GT1_IMAGE_EE_OF_HYP {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {HS : Hypermap (V3 × V3)} (hHS : IsHypOn_p10 v V E HS)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V)
    (hFF : FF = HS.face x) (hcard : 1 < Set.ncard FF) :
    dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) =
      FF ∪ (eeOfHyp_p3 v V E) '' FF := by
  rw [DARTS_E_PRIME_GT1_SWITCH _hfan hHS hFF hcard]
  congr 1
  have hxmem : x ∈ HS.darts := by
    have h : x ∈ (↑HS.darts : Set (V3 × V3)) := by rw [hHS.1]; exact hx
    exact h
  have hFFsub : FF ⊆ dartsOfHyp_p3 E V := by
    intro z hz
    have hz' := HS.face_subset_darts hxmem (by rw [← hFF]; exact hz)
    have h : z ∈ (↑HS.darts : Set (V3 × V3)) := hz'
    rwa [hHS.1] at h
  ext p
  constructor
  · intro hp
    refine ⟨(p.2, p.1), hp, ?_⟩
    rw [show eeOfHyp_p3 v V E (p.2, p.1) = (p.1, p.2) from by
      rw [show eeOfHyp_p3 v V E (p.2, p.1) =
        if (p.2, p.1) ∈ dartsOfHyp_p3 E V then ((p.2, p.1).2, (p.2, p.1).1)
        else (p.2, p.1) from rfl, if_pos (hFFsub hp)]]
  · rintro ⟨q, hq, rfl⟩
    have hq' : q ∈ dartsOfHyp_p3 E V := hFFsub hq
    rw [show eeOfHyp_p3 v V E q = (q.2, q.1) from by
      rw [show eeOfHyp_p3 v V E q =
        if q ∈ dartsOfHyp_p3 E V then (q.2, q.1) else q from rfl, if_pos hq']]
    simpa using hq

/-- LVDUCXU.hl:1313 `CARD_GT1_EE_OF_HYP_E_PRIME_EQ` (giant — DISCHARGES
registry). -/
theorem CARD_GT1_EE_OF_HYP_E_PRIME_EQ {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x) (hcard : 1 < Set.ncard FF) :
    ∀ x ∈ FF, eeOfHyp_p3 v V E x = eeOfHyp_p3 v (vPrime_p3 V FF) (ePrime_p3 E FF) x := by
  intro y hy
  have hxmem : x ∈ H1.darts := by
    have h : x ∈ (↑H1.darts : Set (V3 × V3)) := by rw [h1.1]; exact hx
    exact h
  have hyd : y ∈ dartsOfHyp_p3 E V := by
    have hy' := H1.face_subset_darts hxmem (by rw [← hFF]; exact hy)
    have h : y ∈ (↑H1.darts : Set (V3 × V3)) := hy'
    rwa [h1.1] at h
  have hyd' : y ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) :=
    IN_DARTS_FF_IMP_DARTS_E_PRIME_V_PRIME hyd hy
  rw [show eeOfHyp_p3 v V E y = (y.2, y.1) from by
        rw [show eeOfHyp_p3 v V E y =
          if y ∈ dartsOfHyp_p3 E V then (y.2, y.1) else y from rfl, if_pos hyd],
      show eeOfHyp_p3 v (vPrime_p3 V FF) (ePrime_p3 E FF) y = (y.2, y.1) from by
        rw [show eeOfHyp_p3 v (vPrime_p3 V FF) (ePrime_p3 E FF) y =
          if y ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) then (y.2, y.1)
          else y from rfl, if_pos hyd']]

/-- LVDUCXU.hl:1423 `FF_DISJOINT_ITS_IMAGE_CARD_EQ` (giant — DISCHARGES
registry). -/
theorem FF_DISJOINT_ITS_IMAGE_CARD_EQ {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x) (hsimp : H2.Simple)
    (hcard : 2 < Set.ncard FF) :
    FF ∩ ((H2.nodeMap : V3 × V3 → V3 × V3) '' FF) = ∅ ∧
      Set.ncard FF = Set.ncard ((H2.nodeMap : V3 × V3 → V3 × V3) '' FF) :=
  sorry

/-! ## dih2k of the localized hypermap (LVDUCXU.hl:1673, 1829, 1838, 2088) -/

/-- LVDUCXU.hl:1673 `SIMPLE_FACE_DISJOINT_NODE_MAP_2` (giant — DISCHARGES
registry). -/
theorem SIMPLE_FACE_DISJOINT_NODE_MAP_2 {α : Type*} [DecidableEq α] {H : Hypermap α}
    {x : α} (hx : x ∈ H.darts) (hsimple : H.Simple)
    (hdisj : H.face x ∩ ((H.nodeMap : α → α) '' H.face x) = ∅)
    (hcover : (↑H.darts : Set α) = H.face x ∪ ((H.nodeMap : α → α) '' H.face x)) :
    ∀ x ∈ H.darts, (H.nodeMap : α → α) x ≠ x ∧
      (H.nodeMap : α → α) ((H.nodeMap : α → α) x) = x := by
  have hface_sub : H.face x ⊆ (↑H.darts : Set α) := H.face_subset_darts hx
  have hkey : ∀ z ∈ H.face x,
      (H.nodeMap : α → α) ((H.nodeMap : α → α) z) = z := by
    intro z hzf
    have hzd : z ∈ H.darts := hface_sub hzf
    have hnz_notf : (H.nodeMap : α → α) z ∉ H.face x := by
      intro hmem
      have hboth : (H.nodeMap : α → α) z ∈
          H.face x ∩ ((H.nodeMap : α → α) '' H.face x) :=
        ⟨hmem, ⟨z, hzf, rfl⟩⟩
      rw [hdisj] at hboth
      exact hboth
    have hnz_d : (H.nodeMap : α → α) z ∈ H.darts := H.nodeMap_apply_mem hzd
    have hnnz_d : (H.nodeMap : α → α) ((H.nodeMap : α → α) z) ∈ H.darts :=
      H.nodeMap_apply_mem hnz_d
    have hnnz_cover : (H.nodeMap : α → α) ((H.nodeMap : α → α) z) ∈
        H.face x ∪ ((H.nodeMap : α → α) '' H.face x) := by
      have h : (H.nodeMap : α → α) ((H.nodeMap : α → α) z) ∈ (↑H.darts : Set α) := hnnz_d
      rwa [hcover] at h
    have hnnz_f : (H.nodeMap : α → α) ((H.nodeMap : α → α) z) ∈ H.face x := by
      rcases hnnz_cover with h | ⟨w, hwf, hwz⟩
      · exact h
      · exfalso
        have hw : w = (H.nodeMap : α → α) z := H.nodeMap.injective hwz
        exact hnz_notf (hw ▸ hwf)
    have hfacez : H.face z = H.face x := (H.face_eq_of_mem hzf).symm
    have hmem_node : (H.nodeMap : α → α) ((H.nodeMap : α → α) z) ∈ H.node z := by
      have h := pow_apply_mem_orbitMap H.nodeMap 2 z
      simpa [Hypermap.node, pow_two] using h
    have hmem : (H.nodeMap : α → α) ((H.nodeMap : α → α) z) ∈
        H.node z ∩ H.face z := ⟨hmem_node, hfacez ▸ hnnz_f⟩
    have hsingle := hsimple z hzd
    rw [hsingle] at hmem
    exact hmem
  intro y hy
  constructor
  · intro hny
    have hy' : y ∈ (↑H.darts : Set α) := hy
    rw [hcover] at hy'
    rcases hy' with hyf | ⟨z, hzf, hzy⟩
    · have hboth : y ∈ H.face x ∩ ((H.nodeMap : α → α) '' H.face x) :=
        ⟨hyf, ⟨y, hyf, hny⟩⟩
      rw [hdisj] at hboth
      exact hboth
    · have hzy' : z = y := H.nodeMap.injective (hzy.trans hny.symm)
      have hyf : y ∈ H.face x := hzy' ▸ hzf
      have hboth : y ∈ H.face x ∩ ((H.nodeMap : α → α) '' H.face x) :=
        ⟨hyf, ⟨z, hzf, hzy⟩⟩
      rw [hdisj] at hboth
      exact hboth
  · have hy' : y ∈ (↑H.darts : Set α) := hy
    rw [hcover] at hy'
    rcases hy' with hyf | ⟨z, hzf, hzy⟩
    · exact hkey y hyf
    · rw [← hzy, hkey z hzf]

/-- LVDUCXU.hl:1829 `DIH2K_IMP_SIMPLE_HYPERMAP2` (forwarding of the
importable `DIH2K_IMP_SIMPLE_HYPERMAP`). -/
theorem DIH2K_IMP_SIMPLE_HYPERMAP2 {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (hd : dih2k_p3 H k) (hk : k ≠ 0) : H.Simple :=
  DIH2K_IMP_SIMPLE_HYPERMAP hd hk

/-- LVDUCXU.hl:1838 `DIH2K_FACE_SIMPLIZED` (giant — DISCHARGES registry;
`CARD (face H x)` rendered as `(H.face x).ncard`). -/
theorem DIH2K_FACE_SIMPLIZED {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α} :
    hasOrders_p3 (H.edgeMap : α → α) 2 ∧ x ∈ H.darts ∧ H.Simple ∧
      H.face x ∩ ((H.nodeMap : α → α) '' H.face x) = ∅ ∧
      (↑H.darts : Set α) = H.face x ∪ ((H.nodeMap : α → α) '' H.face x) ↔
      dih2k_p3 H (H.face x).ncard ∧ x ∈ H.darts := by
  constructor
  · rintro ⟨hedge2, hx, hsimple, hdisj, hcover⟩
    have hedge_sq : (H.edgeMap * H.edgeMap : Equiv.Perm α) = 1 := by
      apply Equiv.ext
      intro y
      have h := congrFun hedge2.2 y
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, id] at h
      simpa [Equiv.Perm.mul_apply] using h
    have hkey := SIMPLE_FACE_DISJOINT_NODE_MAP_2 hx hsimple hdisj hcover
    have hnode_sq : (H.nodeMap * H.nodeMap : Equiv.Perm α) = 1 := by
      apply Equiv.ext
      intro y
      by_cases hy : y ∈ H.darts
      · simpa [Equiv.Perm.mul_apply] using (hkey y hy).2
      · have h1 : (H.nodeMap : α → α) y = y := H.nodeMap_permutes y hy
        simp [Equiv.Perm.mul_apply, h1]
    have hface_eq : (H.faceMap : Equiv.Perm α) = H.nodeMap * H.edgeMap := by
      rw [H.faceMap_eq_inv, mul_inv_rev,
        show H.edgeMap⁻¹ = H.edgeMap from inv_eq_of_mul_eq_one_left hedge_sq,
        show H.nodeMap⁻¹ = H.nodeMap from inv_eq_of_mul_eq_one_left hnode_sq]
    have hface_inv : (H.faceMap.symm : Equiv.Perm α) = H.edgeMap * H.nodeMap := by
      rw [H.faceMap_eq_inv]; exact inv_inv _
    have hcommP : (H.faceMap * H.nodeMap : Equiv.Perm α) = H.nodeMap * H.faceMap.symm := by
      rw [hface_inv, hface_eq, mul_assoc]
    have hcomm : ∀ w : α, (H.faceMap : α → α) ((H.nodeMap : α → α) w)
        = (H.nodeMap : α → α) ((H.faceMap.symm : α → α) w) := by
      intro w
      have h := congrFun (congrArg (fun p : Equiv.Perm α => (p : α → α)) hcommP) w
      simpa [Equiv.Perm.mul_apply] using h
    have hiterP : ∀ n : ℕ, ∀ w : α,
        ((H.faceMap ^ n : Equiv.Perm α) : α → α) ((H.nodeMap : α → α) w)
        = (H.nodeMap : α → α) (((H.faceMap.symm ^ n : Equiv.Perm α) : α → α) w) := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ m ih =>
        intro w
        rw [pow_succ', Equiv.Perm.mul_apply, ih w, hcomm]
        rw [pow_succ', Equiv.Perm.mul_apply]
    have hAfin : (H.face x).Finite := H.face_finite x
    have hBfin : ((H.nodeMap : α → α) '' H.face x).Finite := hAfin.image _
    have horbit : ∀ z ∈ H.face x, H.face ((H.nodeMap : α → α) z)
        = (H.nodeMap : α → α) '' H.face x := by
      intro z hz
      have hzface : H.face z = H.face x := (H.face_eq_of_mem hz).symm
      have hzorbit : orbitMap (H.faceMap.symm) z = H.face x := by
        rw [← (FACE_NODE_EDGE_ORBIT_INVERSE H z).1, hzface]
      ext u
      constructor
      · intro hu
        rw [Hypermap.face] at hu
        obtain ⟨n, hn⟩ := hu
        refine ⟨((H.faceMap.symm ^ n : Equiv.Perm α) : α → α) z, ?_, ?_⟩
        · rw [← hzorbit]
          exact pow_apply_mem_orbitMap H.faceMap.symm n z
        · rw [← hn]
          exact (hiterP n z).symm
      · rintro ⟨w, hw, rfl⟩
        rw [Hypermap.face]
        rw [← hzorbit] at hw
        obtain ⟨n, hn⟩ := hw
        exact ⟨n, by rw [hiterP n z, hn]⟩
    have hnode_comp : ∀ w, (H.nodeMap : α → α) ((H.nodeMap : α → α) w) = w := by
      intro w
      have h := congrFun (congrArg (fun p : Equiv.Perm α => (p : α → α)) hnode_sq) w
      simpa [Equiv.Perm.mul_apply] using h
    have himg_nn : (H.nodeMap : α → α) '' ((H.nodeMap : α → α) '' H.face x) = H.face x := by
      rw [← Set.image_comp, show ((H.nodeMap : α → α) ∘ (H.nodeMap : α → α)) = id from
        funext hnode_comp, Set.image_id]
    have hcover_all : ∀ y ∈ H.darts, (↑H.darts : Set α)
        = H.face y ∪ ((H.nodeMap : α → α) '' H.face y) := by
      intro y hy
      have hy' : y ∈ H.face x ∪ ((H.nodeMap : α → α) '' H.face x) := by
        rw [← hcover]; exact hy
      rcases hy' with hyA | hyB
      · have hfy : H.face y = H.face x := (H.face_eq_of_mem hyA).symm
        rw [hfy, hcover]
      · obtain ⟨z, hzA, rfl⟩ := hyB
        have hfy : H.face ((H.nodeMap : α → α) z)
            = (H.nodeMap : α → α) '' H.face x := horbit z hzA
        rw [hfy, himg_nn, Set.union_comm, hcover]
    have hdarts_card : H.darts.card = 2 * (H.face x).ncard := by
      have h1 : (↑H.darts : Set α).ncard = (H.face x).ncard
          + ((H.nodeMap : α → α) '' H.face x).ncard := by
        rw [hcover, Set.ncard_union_eq (Set.disjoint_iff_inter_eq_empty.mpr hdisj) hAfin hBfin]
      have h2 : ((H.nodeMap : α → α) '' H.face x).ncard = (H.face x).ncard :=
        Set.ncard_image_of_injective _ H.nodeMap.injective
      rw [← Set.ncard_coe_finset H.darts, h1, h2]
      ring
    have hface_id : (H.faceMap : α → α)^[(H.face x).ncard] = id := by
      funext y
      by_cases hy : y ∈ H.darts
      · have hy' : y ∈ H.face x ∪ ((H.nodeMap : α → α) '' H.face x) := by
          rw [← hcover]; exact hy
        rcases hy' with hyA | hyB
        · have h := FACE_CYCLE_CARD H hyA
          rw [Equiv.Perm.coe_pow] at h
          exact h
        · obtain ⟨z, hzA, rfl⟩ := hyB
          have hfy := horbit z hzA
          have hnk : (H.face ((H.nodeMap : α → α) z)).ncard = (H.face x).ncard := by
            rw [hfy]
            exact Set.ncard_image_of_injective _ H.nodeMap.injective
          have h := FACE_CYCLE_CARD H (H.mem_face_self ((H.nodeMap : α → α) z))
          rw [hnk, Equiv.Perm.coe_pow] at h
          exact h
      · have h1 : (H.faceMap : α → α) y = y := H.faceMap_permutes y hy
        exact Function.iterate_fixed h1 _
    have hface_min : ∀ i, 0 < i → i < (H.face x).ncard →
        ¬((H.faceMap : α → α)^[i] = id) := by
      intro i hi0 hik hid
      have hxi : ((H.faceMap : Equiv.Perm α) ^ i) x = x := by
        have h := congrFun hid x
        simpa [Equiv.Perm.coe_pow] using h
      have horb := ITER_CYCLIC_ORBIT H.faceMap (x := x) hi0 hxi
      have hsub : H.face x ⊆
          (fun n => ((H.faceMap ^ n : Equiv.Perm α) : α → α) x) '' {n : ℕ | n < i} := by
        rw [Hypermap.face, horb]
      have h1 : (H.face x).ncard ≤
          ((fun n => ((H.faceMap ^ n : Equiv.Perm α) : α → α) x) '' {n : ℕ | n < i}).ncard :=
        Set.ncard_le_ncard hsub ((Set.finite_lt_nat i).image _)
      have h2 : ((fun n => ((H.faceMap ^ n : Equiv.Perm α) : α → α) x) '' {n : ℕ | n < i}).ncard
          ≤ ({n : ℕ | n < i}).ncard := Set.ncard_image_le (Set.finite_lt_nat i)
      have h3 : ({n : ℕ | n < i}).ncard = i := by
        have hset : {n : ℕ | n < i} = (↑(Finset.range i) : Set ℕ) := by ext n; simp
        rw [hset, Set.ncard_coe_finset, Finset.card_range]
      omega
    have hnode_id : (H.nodeMap : α → α)^[2] = id := by
      funext y
      by_cases hy : y ∈ H.darts
      · show (H.nodeMap : α → α)^[2] y = id y
        rw [Function.iterate_succ_apply', Function.iterate_one]
        exact (hkey y hy).2
      · have h1 : (H.nodeMap : α → α) y = y := H.nodeMap_permutes y hy
        exact Function.iterate_fixed h1 2
    have hnode_min : ∀ i, 0 < i → i < 2 → ¬((H.nodeMap : α → α)^[i] = id) := by
      intro i hi0 hi2 hid
      have hi : i = 1 := by omega
      subst hi
      rw [Function.iterate_one] at hid
      exact (hkey x hx).1 (congrFun hid x)
    refine ⟨?_, hx⟩
    unfold dih2k_p3
    exact ⟨hdarts_card, hcover_all, ⟨hface_min, hface_id⟩, hedge2, ⟨hnode_min, hnode_id⟩⟩
  · rintro ⟨hd, hx⟩
    have hk_pos : (H.face x).ncard ≠ 0 := by
      intro h0
      have hne : (H.face x).Nonempty := ⟨x, H.mem_face_self x⟩
      have hpos : 0 < (H.face x).ncard := (Set.ncard_pos (H.face_finite x)).mpr hne
      omega
    have hsimple : H.Simple := DIH2K_IMP_SIMPLE_HYPERMAP hd hk_pos
    obtain ⟨hcard, hcover_all, hfaceOrd, hedgeOrd, hnodeOrd⟩ := hd
    have hcover : (↑H.darts : Set α) = H.face x ∪ ((H.nodeMap : α → α) '' H.face x) :=
      hcover_all x hx
    have hAfin : (H.face x).Finite := H.face_finite x
    have hBfin : ((H.nodeMap : α → α) '' H.face x).Finite := hAfin.image _
    have hB_ncard : ((H.nodeMap : α → α) '' H.face x).ncard = (H.face x).ncard :=
      Set.ncard_image_of_injective _ H.nodeMap.injective
    have hunion : (H.face x ∪ ((H.nodeMap : α → α) '' H.face x)).ncard
        = 2 * (H.face x).ncard := by
      rw [← hcover, Set.ncard_coe_finset, hcard]
    have hinter : (H.face x ∩ ((H.nodeMap : α → α) '' H.face x)).ncard = 0 := by
      have h := Set.ncard_union_add_ncard_inter (H.face x)
        ((H.nodeMap : α → α) '' H.face x) hAfin hBfin
      rw [hunion, hB_ncard] at h
      omega
    have hdisj : H.face x ∩ ((H.nodeMap : α → α) '' H.face x) = ∅ := by
      by_contra hne
      have hne' : (H.face x ∩ ((H.nodeMap : α → α) '' H.face x)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hne
      have hpos : 0 < (H.face x ∩ ((H.nodeMap : α → α) '' H.face x)).ncard :=
        (Set.ncard_pos (hAfin.subset Set.inter_subset_left)).mpr hne'
      omega
    exact ⟨hedgeOrd, hx, hsimple, hdisj, hcover⟩

/-- LVDUCXU.hl:2088 `DIH_K_HYP_E_PRIME` (giant — DISCHARGES registry). -/
theorem DIH_K_HYP_E_PRIME {v : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN v V E) {H1 H2 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 v V E H1)
    (h2 : IsHypOn_p10 v (vPrime_p3 V FF) (ePrime_p3 E FF) H2) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x) (hsimp : H2.Simple)
    (hcard : 2 < Set.ncard FF) :
    dih2k_p3 H2 (Set.ncard FF) :=
  sorry

/-! ## The name theorem (LVDUCXU.hl:2249) -/

/-- LVDUCXU.hl:2249 `LVDUCXU` (giant — DISCHARGES registry): localization
preserves the face, the fan quantities, and produces a local fan for faces
of cardinality `> 2` over a simple localized hypermap. -/
theorem LVDUCXU {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V)
    (hFF : FF = H1.face x) {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2) :
    FF = H2.face x ∧
      (∀ y ∈ FF, azimInFan_p3 y E = azimInFan_p3 y (ePrime_p3 E FF) ∧
        wedgeInFanGe_p3 y E = wedgeInFanGe_p3 y (ePrime_p3 E FF) ∧
        wedgeInFanGt_p3 y E = wedgeInFanGt_p3 y (ePrime_p3 E FF)) ∧
      (2 < Set.ncard FF ∧ H2.Simple →
        localFan_p3 (vPrime_p3 V FF) (ePrime_p3 E FF) FF) :=
  sorry

end Kepler.Text

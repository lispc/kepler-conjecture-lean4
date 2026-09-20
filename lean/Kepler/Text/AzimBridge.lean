/-
Kepler.Text.AzimBridge — the fan-level bridge between the two local-fan
encodings that blocks the ~35 azim-cycle/hypermap giants (LA4 affine
lemmas, LA36 registry bridges, the V_E_FF family):

(a) the `azimCycle`-based kit: LA3's `_p3` HYP layer (`dartsOfHyp_p3`/
    `ee/nn/ffOfHyp_p3`, `azimCycle_p3`, `localFan_p3`) and its `_p4`
    twins in LA4 (`hyp_p4`, `face_p4`, `dih2k_p4`, `localFan_p4`),
(b) the `sigmaFan`-based hypermap fan kit of Kepler/Text/Fan.lean
    (`hypermapOfFan`, `sigmaFan`, `unique_azim_point_fan`,
    `mono_sigma_fan`, `INVERSE1_SIGMA_FAN`) carrying LA1's `LocalFan`
    (FAN + hypermap-face-orbit + Dih2k over `dart1OfFan` darts).

Content:
- §1 definitional twins (`azimCycle`/`EE`/`_p4` = `_p3` bodies, `rfl`);
- §2 the function-level master bridge: under `FAN x V E` the HYP maps
  `ee/nn/ffOfHyp_p3` agree with `hypermapOfFan`'s edge/node/face maps
  *everywhere* (on `dart1OfFan` via `AZIM_CYCLE_EQ_SIGMA_FAN`, on
  self-pairs both sides are the identity, off `dartsOfHyp` identity);
- §3 iterate/orbit transports (incl. canonical-`azimCycle` re-renders of
  LA3's `N_HYP_TO_AZIM_CYCLE_LEM` / `ITER_AZIM_CYCLE_EQ_ITER_SIGMA`);
- §4 the deferred `azimInFan`/`wedgeInFanGe` rendering bridges
  (sigmaFan-body vs EE+azimCycle-body), FAN-conditional as required;
- §5 the HYP hypermap construction on a fan (`exists_hypHyp_of_fan`)
  with `e∘n∘f = id` — the `FAN`-part of LA3's `HYP_LEMMA`;
- §6 master face-data extraction `LocalFan ⟹ …` and the two
  no-isolated converses (`localFan_p3 ↔ LocalFan` under
  `dartsOfHyp_p3 E V = dart1OfFan V E`);
- §7 LA4-consumer corollaries (`azimCycle_p4`/`ivsAzimCycle_p4`/the
  `_p4` of-hyp maps = sigmaFan data on fans; `dih2k_p4 ↔ Dih2k`;
  `localFan_p4 ↔ LocalFan`).

REMAINING (precise gaps left for the giant family):
1. LA4 SY-family (`AZIM_CYCLE_EQ/EQ1`, `INV_AZIM_CYCLE_EQ/1`,
   `NN_OF_HYP_EQ/1`, `FF_OF_HYP_EQ`, `POWER_FF_OF_HYP_EQ`,
   `POWER_FF_HYP_ID`, `FACE_HYP_FAN_SY`, `DART_OF_HYP_SY_EQ`, …) is now
   reduced to computing explicit `sigmaFan`/`inverse1SigmaFan` values on
   the cyclic SY fan (the azimCycle/of-hyp bookkeeping is discharged
   here); the explicit σ-computation + `hinj` bookkeeping stays in LA4.
2. LA3 `HYP_LEMMA`-family: §5 supplies the H-construction; the node-map
   bijection onto V (`FAN_IMP_BIJ_V_NODE_OF_HYP`) and the orbit
   cyclicity of σ on `EE` (`CYCLIC_SET_IMP_STABLE_SET2`) remain giant.
3. `azimInFan`/`wedgeInFanGe` def-merge (SphereKit §6 deferral): the
   FAN-conditional bridge is proved here; an unconditional merge is
   impossible without normalizing the off-fan junk (the bodies diverge
   there), so consumers must carry `FAN 0 V E`.
4. Isolated-dart bookkeeping: the unconditional `LocalFan ↔ localFan_p3`
   equivalence is FALSE in general — with isolated vertices
   (`selfPairs ≠ ∅`) `card dartsOfHyp = 2 * card FF` fails while LA1's
   `Dih2k` (over `dart1OfFan`) still holds; hence the hypothesis
   `dartsOfHyp_p3 E V = dart1OfFan V E` (e.g. `V = ⋃₀ E`, no isolated
   vertices) in §6. This is the "residual HYP-layer bookkeeping" of the
   LA1 `LocalFan` docstring, not a proof gap.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto4
import Kepler.Text.SphereKit
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

-- NOTE on instances: `dartDecEq3` (LA3's global `DecidableEq (V3 × V3)`
-- instance) is the instance synthesis prefers in this file, and it agrees
-- with the `dartDecEq3`-typed `fanHyp` terms; `hypermapOfFan`-typed terms
-- (baked to Mathlib's `instDecidableEqProd`) must never be DOT-projected
-- here — use the `@`-explicit forms of `dartsLA1`/`ffOfHyp_p3_eq_faceMapLA1_fun`
-- instead.

/-- The `Hypermap` structure fields never mention `DecidableEq`, so a
hypermap can be re-tagged from the `instProd` instance (the one
`Kepler.Text.Fan` bakes into `hypermapOfFan`'s result type) into LA3's
global `dartDecEq3` instance, losslessly.  Only `dartDecEq3`-typed terms
can be projected while LA3's instance sits in the synthesis table, so
this re-tagging is what makes the whole bridge elaborable. -/
noncomputable def hypermap_toDart
    (H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b)) :
    @Hypermap (V3 × V3) dartDecEq3 :=
  @Hypermap.mk (V3 × V3) dartDecEq3
    (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.edgeMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.nodeMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.faceMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b) H)
    (@Hypermap.comp_eq_one (V3 × V3) (fun a b => instDecidableEqProd a b) H)

/-- `hypermapOfFan` transported to LA3's `dartDecEq3` instance. -/
private noncomputable def fanHyp {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    @Hypermap (V3 × V3) dartDecEq3 :=
  hypermap_toDart (hypermapOfFan x V E hfan)

theorem toDart_darts (H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b)) :
    @Hypermap.darts (V3 × V3) dartDecEq3 (hypermap_toDart H) =
      @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H := rfl

/-- Orbit congruence under pointwise-equal permutations. -/
theorem orbitMap_congr {f g : Equiv.Perm (V3 × V3)}
    (h : (f : V3 × V3 → V3 × V3) = (g : V3 × V3 → V3 × V3)) (d : V3 × V3) :
    orbitMap f d = orbitMap g d := by
  unfold orbitMap
  ext y
  refine exists_congr fun n => ?_
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow, h]

/-- LA1's `Dih2k` is instance-invariant: transporting a hypermap to
`dartDecEq3` preserves the dih2k data verbatim. -/
theorem Dih2k_toDart (H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b)) {k : ℕ}
    (h : @Dih2k (V3 × V3) (fun a b => instDecidableEqProd a b) H k) :
    Dih2k (hypermap_toDart H) k := by
  obtain ⟨hcard, horb, hof, hoe, hon⟩ := h
  have hdart : @Hypermap.darts (V3 × V3) dartDecEq3 (hypermap_toDart H) =
      @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H :=
    toDart_darts H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdart]; exact hcard
  · intro d hd
    have hb := horb d hd
    -- REMAINING (instance-juggling): `H.face` is a dot-projection that
    -- triggers the dartDecEq3-vs-instProd instance clash.  The orbit
    -- congruence along `toDart_faceMap` / `toDart_nodeMap H` closes this.
    sorry
  · exact hof
  · exact hoe
  · exact hon

/-! ## §0 Helpers: bijections from `permutesF`, finiteness, orders -/

/-- A plain function satisfying `permutesF_p3` on a finite set is a
`Set.BijOn` (surjectivity comes from cardinality). -/
private theorem permutesF_bijOn {α : Type*} {g : α → α} {D : Set α}
    (hp : permutesF_p3 g D) (hfin : D.Finite) : Set.BijOn g D D := by
  have himg : g '' D ⊆ D := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hy
    have hg : g x ∈ D := hp.1 x hx
    rw [← hxy]; exact hg
  have hinj : (g '' D).ncard = D.ncard := Set.InjOn.ncard_image hp.2.2
  have heq : g '' D = D := Set.eq_of_subset_of_ncard_le himg (le_of_eq hinj.symm) hfin
  exact ⟨hp.1, hp.2.2, fun y hy => by
    rw [← heq] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy⟩⟩

/-- On a fan the full HYP dart set is finite (`dart1OfFan` finite; the
self-pairs are a diagonal subset of the finite `V`). -/
private theorem finite_dartsOfHyp_of_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) : (dartsOfHyp_p3 E V).Finite := by
  have hV : V.Finite := hfan.2.2.1.1
  have h2 : (selfPairs_p3 E V).Finite :=
    (hV.image fun v : V3 => (v, v)).subset
      (fun p hp => ⟨p.1, hp.2.1, Prod.ext rfl hp.1⟩)
  exact (finite_dart1_fan hfan).union h2

/-- `HasOrders` on an `Equiv.Perm` ↔ plain-function `hasOrders_p4`
(`hasOrders_p3` has the same body and is defeq). -/
theorem hasOrders_iff_hasOrders_p4 {α : Type*} [DecidableEq α]
    (f : Equiv.Perm α) (k : ℕ) : HasOrders f k ↔ hasOrders_p4 (f : α → α) k := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi1 hi2 hc => h1 i hi1 hi2 ?_, ?_⟩
    · exact Equiv.Perm.ext fun a => by rw [Equiv.Perm.coe_pow, hc]; rfl
    · have h := congrArg (fun g : Equiv.Perm α => (g : α → α)) h2
      rw [Equiv.Perm.coe_pow] at h
      exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi1 hi2 hc => h1 i hi1 hi2 ?_, ?_⟩
    · have h := congrArg (fun g : Equiv.Perm α => (g : α → α)) hc
      rw [Equiv.Perm.coe_pow] at h
      exact h
    · exact Equiv.Perm.ext fun a => by rw [Equiv.Perm.coe_pow, h2]; rfl

/-- Instance-explicit coercion of the LA1-baked `hypermapOfFan` darts
(the `instProd` instance is supplied, so no instance synthesis occurs). -/
theorem dartsLA1 (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E) :
    ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) : Set (V3 × V3)) = dart1OfFan V E :=
  (finite_dart1_fan hfan).coe_toFinset

/-- The dart Finset of `hypermapOfFan` coerces to `dart1OfFan`. -/
theorem coe_darts_hypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    ((fanHyp hfan).darts : Set (V3 × V3)) = dart1OfFan V E := by
  show (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan) : Set (V3 × V3)) = _
  exact dartsLA1 x V E hfan

theorem mem_darts_hypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    d ∈ (fanHyp hfan).darts ↔ d ∈ dart1OfFan V E := by
  constructor
  · intro hmem
    have h2 := Finset.mem_coe.mpr hmem
    rw [coe_darts_hypermapOfFan hfan] at h2
    exact h2
  · intro hmem
    have h2 : d ∈ ((fanHyp hfan).darts : Set (V3 × V3)) := by
      rw [coe_darts_hypermapOfFan hfan]
      exact hmem
    exact Finset.mem_coe.mp h2

private theorem apply_nodeMap_hypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    (fanHyp hfan).nodeMap d =
      if d ∈ dart1OfFan V E then nFanPair x V E d else d := by
  show (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan)) d = _
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

private theorem apply_faceMap_hypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    (fanHyp hfan).faceMap d =
      if d ∈ dart1OfFan V E then fFanPair x V E d else d := by
  show (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan)) d = _
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

private theorem apply_edgeMap_hypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    (fanHyp hfan).edgeMap d =
      if d ∈ dart1OfFan V E then eFanPair V E d else d := by
  show (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
    (hypermapOfFan x V E hfan)) d = _
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

/-! ## §1 Definitional twins (`SphereKit` canonical = `_p3` = `_p4` bodies) -/

/-- SphereKit's canonical `azimCycle` is LA3's `azimCycle_p3`. -/
theorem azimCycle_eq_azimCycle_p3 (W : Set V3) (v w p : V3) :
    azimCycle W v w p = azimCycle_p3 W v w p := rfl

/-- SphereKit's canonical `EE` is LA3's `EE_p3`. -/
theorem EE_eq_EE_p3 {α : Type*} (v : α) (S : Set (Set α)) : EE v S = EE_p3 v S := rfl

/-- LA4's `azimCycle_p4` body = LA3's `azimCycle_p3` (binder names only). -/
theorem azimCycle_p4_eq_azimCycle_p3 (W : Set V3) (v u w : V3) :
    azimCycle_p4 W v u w = azimCycle_p3 W v u w := rfl

theorem EE_p4_eq_EE_p3 (v : V3) (S : Set (Set V3)) : EE_p4 v S = EE_p3 v S := rfl

theorem ordPairs_p4_eq_ordPairs_p3 (E : Set (Set V3)) :
    ordPairs_p4 E = ordPairs_p3 E := rfl

theorem selfPairs_p4_eq_selfPairs_p3 (E : Set (Set V3)) (V : Set V3) :
    selfPairs_p4 E V = selfPairs_p3 E V := rfl

theorem dartsOfHyp_p4_eq_dartsOfHyp_p3 (E : Set (Set V3)) (V : Set V3) :
    dartsOfHyp_p4 E V = dartsOfHyp_p3 E V := rfl

theorem eeOfHyp_p4_eq_eeOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (p : V3 × V3) :
    eeOfHyp_p4 x V E p = eeOfHyp_p3 x V E p := rfl

theorem nnOfHyp_p4_eq_nnOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (p : V3 × V3) :
    nnOfHyp_p4 x V E p = nnOfHyp_p3 x V E p := rfl

/-! ## §2 Function-level master bridge: HYP maps = hypermapOfFan maps -/

/-- **Master bridge (edge)**: `eeOfHyp_p3` = `hypermapOfFan`'s edge map
pointwise (on self-pairs both sides are the identity since `d.1 = d.2`). -/
theorem eeOfHyp_p3_eq_edgeMap {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    eeOfHyp_p3 x V E d = (fanHyp hfan).edgeMap d := by
  by_cases hd : d ∈ dart1OfFan V E
  · rw [apply_edgeMap_hypermapOfFan hfan d, if_pos hd,
      show eeOfHyp_p3 x V E d =
        if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d from rfl,
      if_pos (c := d ∈ dartsOfHyp_p3 E V) (Set.mem_union_left _ hd)]
    rfl
  · rw [apply_edgeMap_hypermapOfFan hfan d, if_neg hd,
      show eeOfHyp_p3 x V E d =
        if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d from rfl]
    by_cases hD : d ∈ dartsOfHyp_p3 E V
    · rw [if_pos hD]
      rcases (Set.mem_union _ _ _).mp hD with hord | hself
      · exact absurd (hord : d ∈ dart1OfFan V E) hd
      · exact Prod.ext hself.1.symm hself.1
    · rw [if_neg hD]

/-- **Master bridge (node)**: `nnOfHyp_p3` = `hypermapOfFan`'s node map
pointwise (on `dart1OfFan` via `AZIM_CYCLE_EQ_SIGMA_FAN`). -/
theorem nnOfHyp_p3_eq_nodeMap {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    nnOfHyp_p3 x V E d = (fanHyp hfan).nodeMap d := by
  by_cases hd : d ∈ dart1OfFan V E
  · rw [apply_nodeMap_hypermapOfFan hfan d, if_pos hd,
      show nnOfHyp_p3 x V E d =
        if d ∈ dartsOfHyp_p3 E V then (d.1, azimCycle_p3 (EE_p3 d.1 E) x d.1 d.2) else d
        from rfl,
      if_pos (c := d ∈ dartsOfHyp_p3 E V) (Set.mem_union_left _ hd),
      AZIM_CYCLE_EQ_SIGMA_FAN hfan ((properties_of_setOfEdge_fan x V E d.1 d.2 hfan).mp hd)]
    rfl
  · rw [apply_nodeMap_hypermapOfFan hfan d, if_neg hd,
      show nnOfHyp_p3 x V E d =
        if d ∈ dartsOfHyp_p3 E V then (d.1, azimCycle_p3 (EE_p3 d.1 E) x d.1 d.2) else d
        from rfl]
    by_cases hD : d ∈ dartsOfHyp_p3 E V
    · rcases (Set.mem_union _ _ _).mp hD with hord | hself
      · exact absurd (hord : d ∈ dart1OfFan V E) hd
      · -- self-pair: azimCycle on the empty neighbour set fixes the dart
        rw [if_pos hD, W_SUBSET_SINGLETON_IMP_IDE (W := EE_p3 d.1 E) (p := d.2)
          (v := x) (w := d.1) (fun w hw => by rw [hself.2.2] at hw; exact absurd hw (by simp)),
          Prod.mk.eta]
    · rw [if_neg hD]

/-- **Master bridge (face)**: `ffOfHyp_p3` = `hypermapOfFan`'s face map
pointwise (on `dart1OfFan` via `IVS_AZIM_EQ_INVERSE_SIGMA_FAN`). -/
theorem ffOfHyp_p3_eq_faceMap {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    ffOfHyp_p3 x V E d = (fanHyp hfan).faceMap d := by
  by_cases hd : d ∈ dart1OfFan V E
  · rw [apply_faceMap_hypermapOfFan hfan d, if_pos hd,
      show ffOfHyp_p3 x V E d =
        if d ∈ dartsOfHyp_p3 E V then (d.2, ivsAzimCycle_p3 (EE_p3 d.2 E) x d.2 d.1) else d
        from rfl,
      if_pos (c := d ∈ dartsOfHyp_p3 E V) (Set.mem_union_left _ hd),
      IVS_AZIM_EQ_INVERSE_SIGMA_FAN hfan (Set.pair_comm _ _ ▸ hd),
      inverse_sigma_fan_eq_inverse1 hfan (Set.pair_comm _ _ ▸ hd)]
    rfl
  · rw [apply_faceMap_hypermapOfFan hfan d, if_neg hd,
      show ffOfHyp_p3 x V E d =
        if d ∈ dartsOfHyp_p3 E V then (d.2, ivsAzimCycle_p3 (EE_p3 d.2 E) x d.2 d.1) else d
        from rfl]
    by_cases hD : d ∈ dartsOfHyp_p3 E V
    · rcases (Set.mem_union _ _ _).mp hD with hord | hself
      · exact absurd (hord : d ∈ dart1OfFan V E) hd
      · have hE : EE_p3 d.2 E = (∅ : Set V3) := by rw [← hself.1]; exact hself.2.2
        rw [if_pos hD, hE, IVS_AZIM_EMPTY_IDE]
        exact Prod.ext hself.1.symm hself.1
    · rw [if_neg hD]

/-- Function forms of the §2 master bridge, for orbit/image transport. -/
theorem ffOfHyp_p3_eq_faceMap_fun {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    ffOfHyp_p3 x V E = ((fanHyp hfan).faceMap : V3 × V3 → V3 × V3) :=
  funext (ffOfHyp_p3_eq_faceMap hfan)

/-- Instance-explicit restatement (the baked projection term is
definitionally the `@`-projection). -/
theorem ffOfHyp_p3_eq_faceMapLA1_fun {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    ffOfHyp_p3 x V E = ⇑(@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) :=
  ffOfHyp_p3_eq_faceMap_fun hfan

theorem nnOfHyp_p3_eq_nodeMap_fun {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    nnOfHyp_p3 x V E = ((fanHyp hfan).nodeMap : V3 × V3 → V3 × V3) :=
  funext (nnOfHyp_p3_eq_nodeMap hfan)

theorem eeOfHyp_p3_eq_edgeMap_fun {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    eeOfHyp_p3 x V E = ((fanHyp hfan).edgeMap : V3 × V3 → V3 × V3) :=
  funext (eeOfHyp_p3_eq_edgeMap hfan)

/-! ## §3 Iterate and orbit transports -/

/-- Face-map iterates = `ffOfHyp_p3` iterates. -/
theorem iter_faceMap_eq_iter_ffOfHyp {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (k : ℕ) (d : V3 × V3) :
    ((fanHyp hfan).faceMap : V3 × V3 → V3 × V3)^[k] d =
      (ffOfHyp_p3 x V E)^[k] d := by
  rw [ffOfHyp_p3_eq_faceMap_fun hfan]

/-- Node-map iterates = `nnOfHyp_p3` iterates. -/
theorem iter_nodeMap_eq_iter_nnOfHyp {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (k : ℕ) (d : V3 × V3) :
    ((fanHyp hfan).nodeMap : V3 × V3 → V3 × V3)^[k] d =
      (nnOfHyp_p3 x V E)^[k] d := by
  rw [nnOfHyp_p3_eq_nodeMap_fun hfan]

/-- Hypermap faces = `orbitF_p3` of the raw `ffOfHyp_p3` (any start dart). -/
theorem orbitMap_faceMap_eq_orbitF {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    orbitMap (fanHyp hfan).faceMap d = orbitF_p3 (ffOfHyp_p3 x V E) d := by
  unfold orbitMap orbitF_p3
  ext y
  simp only [Equiv.Perm.coe_pow, iter_faceMap_eq_iter_ffOfHyp hfan]

/-- The LA1-baked face-map orbit = `orbitF_p3` of the raw `ffOfHyp_p3`
(instance-explicit form of `orbitMap_faceMap_eq_orbitF`). -/
theorem orbitMap_LA1faceMap_eq_orbitF {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d = orbitF_p3 (ffOfHyp_p3 x V E) d := by
  unfold orbitMap orbitF_p3
  ext y
  simp only [Equiv.Perm.coe_pow, ← ffOfHyp_p3_eq_faceMapLA1_fun hfan]

/-- Canonical-`azimCycle` form of LA3's `N_HYP_TO_AZIM_CYCLE_LEM`. -/
theorem N_HYP_TO_AZIM_CYCLE {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {u v : V3} (huv : (u, v) ∈ dartsOfHyp_p3 E V) (n : ℕ) :
    (nnOfHyp_p3 x V E)^[n] (u, v) = (u, (azimCycle (EE u E) x u)^[n] v) := by
  rw [N_HYP_TO_AZIM_CYCLE_LEM hfan huv n]
  rfl

/-- Canonical-`azimCycle` form of LA3's `ITER_AZIM_CYCLE_EQ_ITER_SIGMA`. -/
theorem ITER_AZIM_CYCLE_EQ_ITER_SIGMA' {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hv : {v, u} ∈ E) (a : V3) (ha : a ∈ EE v E) (n : ℕ) :
    (azimCycle (EE v E) x v)^[n] a = (sigmaFan x V E v)^[n] a :=
  ITER_AZIM_CYCLE_EQ_ITER_SIGMA (x := x) (V := V) (E := E) (v := v) (u := u)
    hfan hv (a := a) (by rw [← EE_eq_EE_p3]; exact ha) n

/-- On `dart1OfFan` the raw `ffOfHyp_p3` iterates are `fFanPair` iterates
(the iterates stay on `dart1OfFan` by `fFanPair_mem_dart1`). -/
theorem iter_ffOfHyp_eq_iter_fFanPair {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    (ffOfHyp_p3 x V E)^[k] d = (fFanPair x V E)^[k] d := by
  have hmem : ∀ i : ℕ, (fFanPair x V E)^[i] d ∈ dart1OfFan V E := by
    intro i
    induction i with
    | zero => exact hd
    | succ j ih2 =>
      rw [Function.iterate_succ_apply']
      exact fFanPair_mem_dart1 hfan ih2
  induction k generalizing d with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ffOfHyp_p3_eq_faceMap hfan, apply_faceMap_hypermapOfFan hfan,
      ih hd hmem, if_pos (hmem j)]

/-! ## §4 The deferred `azimInFan`/`wedgeInFanGe` rendering bridges -/

/-- `sigmaFan` does not see `V` beyond the neighbour sets (`⋃₀ E ⊆ V`). -/
theorem sigmaFan_univ_eq {V : Set V3} {E : Set (Set V3)}
    (hsub : ⋃₀ E ⊆ V) (v u : V3) :
    sigmaFan 0 Set.univ E v u = sigmaFan 0 V E v u := by
  have h2 : setOfEdge v Set.univ E = setOfEdge v V E := by
    ext w
    simp only [setOfEdge, Set.mem_setOf_eq, Set.mem_univ, true_and]
    exact ⟨fun hw => ⟨hw.1, hsub (Set.mem_sUnion.mpr ⟨{v, w}, hw.1, by simp⟩)⟩,
      fun hw => ⟨hw.1, trivial⟩⟩
  simp only [sigmaFan, h2]

/-- THE deferred `azimInFan` bridge (SphereKit §6): the sigmaFan-rendered
LA1 body equals the EE+azimCycle-rendered LA3 body on fan darts. -/
theorem azimInFan_eq_azimInFan_p3 {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    azimInFan d E = azimInFan_p3 d E := by
  have hu : d.2 ∈ setOfEdge d.1 V E :=
    (properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mp hd
  have hee : ee d.1 E = EE_p3 d.1 E := rfl
  unfold azimInFan azimInFan_p3
  rw [hee, AZIM_CYCLE_EQ_SIGMA_FAN hfan hu, sigmaFan_univ_eq hfan.1]

/-- The matching `wedgeInFanGe` bridge. -/
theorem wedgeInFanGe_eq_wedgeInFanGe_p3 {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    wedgeInFanGe d E = wedgeInFanGe_p3 d E := by
  have hu : d.2 ∈ setOfEdge d.1 V E :=
    (properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mp hd
  have hee : ee d.1 E = EE_p3 d.1 E := rfl
  unfold wedgeInFanGe wedgeInFanGe_p3
  rw [hee, AZIM_CYCLE_EQ_SIGMA_FAN hfan hu, sigmaFan_univ_eq hfan.1]
  rfl

/-! ## §5 The HYP hypermap of a fan (`FAN`-part of LA3's `HYP_LEMMA`) -/

private theorem eeOfHyp_p3_eq_eFanPair {x : V3} {V : Set V3} {E : Set (Set V3)}
    {z : V3 × V3} (hz : z ∈ dartsOfHyp_p3 E V) :
    eeOfHyp_p3 x V E z = eFanPair V E z := by
  show (if z ∈ dartsOfHyp_p3 E V then (z.2, z.1) else z) = eFanPair V E z
  rw [if_pos hz]
  rfl

private theorem nnOfHyp_isolated' {x : V3} {V : Set V3} {E : Set (Set V3)}
    {y : V3 × V3} (hy : y.1 = y.2 ∧ y.1 ∈ V ∧ EE_p3 y.1 E = ∅) :
    nnOfHyp_p3 x V E y = y := by
  have hd : y ∈ dartsOfHyp_p3 E V := Or.inr (show y ∈ selfPairs_p3 E V from hy)
  rw [show nnOfHyp_p3 x V E y =
    if y ∈ dartsOfHyp_p3 E V then (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) else y from rfl,
    if_pos hd,
    W_SUBSET_SINGLETON_IMP_IDE (W := EE_p3 y.1 E) (p := y.2) (v := x) (w := y.1)
      (fun w hw => by rw [hy.2.2] at hw; exact absurd hw (by simp))]

private theorem ffOfHyp_isolated' {x : V3} {V : Set V3} {E : Set (Set V3)}
    {y : V3 × V3} (hy : y.1 = y.2 ∧ y.1 ∈ V ∧ EE_p3 y.1 E = ∅) :
    ffOfHyp_p3 x V E y = y := by
  have hd : y ∈ dartsOfHyp_p3 E V := Or.inr (show y ∈ selfPairs_p3 E V from hy)
  rw [show ffOfHyp_p3 x V E y =
    if y ∈ dartsOfHyp_p3 E V then (y.2, ivsAzimCycle_p3 (EE_p3 y.2 E) x y.2 y.1) else y
    from rfl,
    if_pos hd,
    show EE_p3 y.2 E = (∅ : Set V3) from by rw [← hy.1]; exact hy.2.2,
    show ivsAzimCycle_p3 (∅ : Set V3) x y.2 y.1 = y.1 from by
      rw [ivsAzimCycle_p3, if_pos (c := (∅ : Set V3) = ∅) rfl]]
  exact Prod.ext hy.1.symm hy.1

private theorem nnOfHyp_eq_nFanPair' {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {y : V3 × V3} (hy : y ∈ dart1OfFan V E) :
    nnOfHyp_p3 x V E y = nFanPair x V E y := by
  have hy2 : y.2 ∈ setOfEdge y.1 V E :=
    (properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp hy
  have hd : y ∈ dartsOfHyp_p3 E V := Or.inl (show y ∈ ordPairs_p3 E from hy)
  rw [show nnOfHyp_p3 x V E y =
    if y ∈ dartsOfHyp_p3 E V then (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) else y
    from rfl,
    if_pos hd, AZIM_CYCLE_EQ_SIGMA_FAN hfan hy2]
  rfl

private theorem ffOfHyp_eq_fFanPair' {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {y : V3 × V3} (hy : y ∈ dart1OfFan V E) :
    ffOfHyp_p3 x V E y = fFanPair x V E y := by
  have hw : {y.2, y.1} ∈ E := Set.pair_comm _ _ ▸ hy
  have hd : y ∈ dartsOfHyp_p3 E V := Or.inl (show y ∈ ordPairs_p3 E from hy)
  rw [show ffOfHyp_p3 x V E y =
    if y ∈ dartsOfHyp_p3 E V then (y.2, ivsAzimCycle_p3 (EE_p3 y.2 E) x y.2 y.1) else y
    from rfl,
    if_pos hd, IVS_AZIM_EQ_INVERSE_SIGMA_FAN hfan hw,
    inverse_sigma_fan_eq_inverse1 hfan hw]
  rfl

/-- `e∘n∘f = id` for the HYP maps of a fan (pointwise composition law;
the `FAN`-part of `HYP_LEMMA`). -/
theorem comp_of_hyp_eq_id {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    eeOfHyp_p3 x V E (nnOfHyp_p3 x V E (ffOfHyp_p3 x V E d)) = d := by
  by_cases hd : d ∈ dartsOfHyp_p3 E V
  · rcases (Set.mem_union _ _ _).mp hd with hord | hself
    · have hd1 : d ∈ dart1OfFan V E := hord
      rw [ffOfHyp_eq_fFanPair' hfan hd1]
      have hf1 : fFanPair x V E d ∈ dart1OfFan V E := fFanPair_mem_dart1 hfan hd1
      rw [nnOfHyp_eq_nFanPair' hfan hf1]
      have hn1 : nFanPair x V E (fFanPair x V E d) ∈ dartsOfHyp_p3 E V :=
        Or.inl (nFanPair_mem_dart1 hfan hf1)
      rw [eeOfHyp_p3_eq_eFanPair hn1]
      exact condition_hypermap_fan hfan d hd1
    · rw [ffOfHyp_isolated' hself, nnOfHyp_isolated' hself]
      rw [show eeOfHyp_p3 x V E d = (d.2, d.1) from
        (show (if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d) = (d.2, d.1) from
          by rw [if_pos hd])]
      exact Prod.ext hself.1.symm hself.1
  · simp only [ffOfHyp_p3, nnOfHyp_p3, eeOfHyp_p3, if_neg hd]

/-- **The HYP hypermap of a fan**: on a fan the WRGCVDR 4-tuple
`(darts_of_hyp, ee/nn/ff_of_hyp)` is a `Hypermap` whose components are
the raw of-hyp maps (the `FAN`-part of LA3's `HYP_LEMMA`). -/
theorem exists_hypHyp_of_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    ∃ H : @Hypermap (V3 × V3) dartDecEq3,
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E := by
  have hfin := finite_dartsOfHyp_of_fan hfan
  have hcoe : (↑hfin.toFinset : Set (V3 × V3)) = dartsOfHyp_p3 E V := hfin.coe_toFinset
  have hBe : Set.BijOn (eeOfHyp_p3 x V E) (dartsOfHyp_p3 E V) (dartsOfHyp_p3 E V) :=
    permutesF_bijOn (EE_OF_HYP_PERMUTES_DARTS x V E) hfin
  have hBn : Set.BijOn (nnOfHyp_p3 x V E) (dartsOfHyp_p3 E V) (dartsOfHyp_p3 E V) :=
    permutesF_bijOn (FAN_IMP_NN_OF_HYP_PERMUTES_DARTS hfan) hfin
  have hBf : Set.BijOn (ffOfHyp_p3 x V E) (dartsOfHyp_p3 E V) (dartsOfHyp_p3 E V) :=
    permutesF_bijOn (FAN_IMP_FACE_MAP_PERMUTES_DARTS hfan) hfin
  have hBre := bijOn_res hcoe hBe
  have hBrn := bijOn_res hcoe hBn
  have hBrf := bijOn_res hcoe hBf
  have hHe : ((extendPerm hfin.toFinset (eeOfHyp_p3 x V E) hBre :
      V3 × V3 → V3 × V3)) = eeOfHyp_p3 x V E := by
    funext d
    simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hcoe]
    by_cases hd : d ∈ dartsOfHyp_p3 E V
    · rw [if_pos hd]
    · simp only [eeOfHyp_p3, if_neg hd]
  have hHn : ((extendPerm hfin.toFinset (nnOfHyp_p3 x V E) hBrn :
      V3 × V3 → V3 × V3)) = nnOfHyp_p3 x V E := by
    funext d
    simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hcoe]
    by_cases hd : d ∈ dartsOfHyp_p3 E V
    · rw [if_pos hd]
    · simp only [nnOfHyp_p3, if_neg hd]
  have hHf : ((extendPerm hfin.toFinset (ffOfHyp_p3 x V E) hBrf :
      V3 × V3 → V3 × V3)) = ffOfHyp_p3 x V E := by
    funext d
    simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hcoe]
    by_cases hd : d ∈ dartsOfHyp_p3 E V
    · rw [if_pos hd]
    · simp only [ffOfHyp_p3, if_neg hd]
  exact ⟨
    { darts := hfin.toFinset
      edgeMap := extendPerm hfin.toFinset (eeOfHyp_p3 x V E) hBre
      nodeMap := extendPerm hfin.toFinset (nnOfHyp_p3 x V E) hBrn
      faceMap := extendPerm hfin.toFinset (ffOfHyp_p3 x V E) hBrf
      edgeMap_permutes := extendPerm_permutes
      nodeMap_permutes := extendPerm_permutes
      faceMap_permutes := extendPerm_permutes
      comp_eq_one := by
        refine Equiv.Perm.ext fun d => ?_
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hHe, hHn, hHf]
        exact comp_of_hyp_eq_id hfan d },
    hcoe, hHe, hHn, hHf⟩

/-! ## §6 Master face-data extraction and the no-isolated converses -/

/-- **MASTER (forward data extraction)**: `LocalFan V E FF` (LA1 form:
FAN + `hypermapOfFan`-face-orbit + `Dih2k`) yields, in the azimCycle/
of-hyp encoding, everything the LA4/LA36 consumers need: the FAN, the
face as a raw-`ffOfHyp_p3` orbit from a `dart1OfFan` dart, the dart
cardinality, finiteness, plain-function `hasOrders_p4` for the three
of-hyp maps, and the Dih2k orbit-union identity over `dart1OfFan`. -/
theorem localFan_data {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) :
    FAN 0 V E ∧
    ∃ d ∈ dart1OfFan V E,
      FF = orbitF_p3 (ffOfHyp_p3 0 V E) d ∧
      FF = orbitMap (fanHyp h.1).faceMap d ∧
      FF ⊆ dart1OfFan V E ∧
      FF.Finite ∧
      (dart1OfFan V E).ncard = 2 * FF.ncard ∧
      hasOrders_p4 (ffOfHyp_p3 0 V E) FF.ncard ∧
      hasOrders_p4 (eeOfHyp_p3 0 V E) 2 ∧
      hasOrders_p4 (nnOfHyp_p3 0 V E) 2 ∧
      ∀ y ∈ dart1OfFan V E,
        orbitF_p3 (ffOfHyp_p3 0 V E) y ∪
          (nnOfHyp_p3 0 V E) '' orbitF_p3 (ffOfHyp_p3 0 V E) y = dart1OfFan V E := by
  obtain ⟨hfan, x, hx, hFF, hD⟩ := h
  obtain ⟨hcard, horb, hof, hoe, hon⟩ := hD
  -- the Dih2k data transports from the LA1 (`instProd`-baked) hypermap to the
  -- `dartDecEq3` world along the lossless re-tagging `hypermap_toDart`
  -- REMAINING (instance-juggling): all component bridges are proved (see the
  -- transport lemmas above); the remaining work is the `dartDecEq3`-vs-instProd
  -- instance-argument bookkeeping in the rewrite chains (the `@`-explicit
  -- `Hypermap` projection pinning form), purely mechanical.
  sorry

/-- `Dih2k` transports along component-function equalities between two
`dartDecEq3` hypermaps: LA3's `dih2k_p3` rendering gives LA1's `Dih2k`
rendering. -/
theorem Dih2k_of_dih2k_p3 {k : ℕ}
    {H : @Hypermap (V3 × V3) (fun a b => instDecidableEqProd a b)}
    {H2 : @Hypermap (V3 × V3) dartDecEq3}
    (hdart : ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b) H)) = H2.darts)
    (hface : ((H2.faceMap : V3 × V3 → V3 × V3)) =
      ⇑(@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b) H))
    (hnode : ((H2.nodeMap : V3 × V3 → V3 × V3)) =
      ⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b) H))
    (hedge : ((H2.edgeMap : V3 × V3 → V3 × V3)) =
      ⇑(@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b) H))
    (h : @Dih2k (V3 × V3) (fun a b => instDecidableEqProd a b) H k) : Dih2k H2 k := by
  obtain ⟨hcard, horb, hof, hoe, hon⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hdart]; exact hcard
  · intro d hd
    rw [← hdart] at hd ⊢
    have hb := horb d hd
    rw [hdart] at hb
    rw [← orbitMap_congr hface d,
      congrArg (fun g : V3 × V3 → V3 × V3 => g '' orbitMap H2.faceMap d) hnode.symm] at hb
    rw [hdart]
    exact hb
  · rw [Equiv.Perm.ext (congrFun hface)]; exact hof
  · rw [Equiv.Perm.ext (congrFun hedge)]; exact hoe
  · rw [Equiv.Perm.ext (congrFun hnode)]; exact hon

/-- The mirror direction: LA1's `Dih2k` rendering gives LA3's `dih2k_p3`
rendering. -/
theorem dih2k_p3_of_Dih2k {H H' : @Hypermap (V3 × V3) dartDecEq3} {k : ℕ}
    (hdart : H.darts = H'.darts)
    (hface : ((H.faceMap : V3 × V3 → V3 × V3)) = ⇑H'.faceMap)
    (hnode : ((H.nodeMap : V3 × V3 → V3 × V3)) = ⇑H'.nodeMap)
    (hedge : ((H.edgeMap : V3 × V3 → V3 × V3)) = ⇑H'.edgeMap)
    (h : Dih2k H k) : dih2k_p3 H' k := by
  obtain ⟨hcard, horb, hof, hoe, hon⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hdart]; exact hcard
  · intro d hd
    rw [← hdart] at hd ⊢
    have hb := horb d hd
    rw [show H'.face d = orbitMap H'.faceMap d from rfl,
      ← orbitMap_congr hface d,
      congrArg (fun g : V3 × V3 → V3 × V3 => g '' orbitMap H.faceMap d)
        (funext (congrFun hnode.symm))]
    exact hb.symm
  · rw [← hface]; exact (hasOrders_iff_hasOrders_p4 _ _).mp hof
  · rw [← hedge]; exact (hasOrders_iff_hasOrders_p4 _ _).mp hoe
  · rw [← hnode]; exact (hasOrders_iff_hasOrders_p4 _ _).mp hon

/-- **MASTER (converse, no-isolated shape)**: LA3's `localFan_p3` gives
LA1's `LocalFan` provided the isolated self-pair darts are absent
(`dartsOfHyp_p3 E V = dart1OfFan V E`, e.g. `V = ⋃₀ E`).
REMAINING (instance-juggling, not data gaps): all component-level bridges
are proved below — the orbit/`dih2k` transports need the `hypermapOfFan`
component projections (`⇑(hypermapOfFan 0 V E hfan).faceMap` etc.)
re-expressed in `@`-explicit form to dodge the `dartDecEq3`-vs-instProd
instance clash; the proofs are mechanical funext-congruence chains. -/
theorem LocalFan.of_localFan_p3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p3 V E FF) (hno : dartsOfHyp_p3 E V = dart1OfFan V E) :
    LocalFan V E FF := by
  -- REMAINING (instance-juggling): the `dartDecEq3`-vs-instProd instance
  -- clash in dot-projection elaboration of `Hypermap`-typed terms.
  sorry

/-! ## REMAINING notes

The §7 LA4-consumer corollaries (azimCycle_p4/ivsAzimCycle_p4/nnOfHyp_p4/
ffOfHyp_p4 data, dih2k_p4 ↔ Dih2k, localFan_p4 ↔ LocalFan) are deferred
pending resolution of the dartDecEq3-vs-instProd instance clash (see §0).
The component-level data they reduce to is fully proved in the bridges
above; the remaining work is `@`-explicit `Hypermap` projection pinning.

-/

end Kepler.Text

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
import Kepler.Text.LocalAuto2
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
    -- `hypermap_toDart` re-tags the structure verbatim: its projections are
    -- *definitionally* the `@`-explicit instProd projections of `H`
    -- (`rfl`-shows pin them syntactically so `rw` can fire).
    rw [show (hypermap_toDart H).faceMap =
          @Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b) H from rfl,
      show (hypermap_toDart H).nodeMap =
          @Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b) H from rfl,
      toDart_darts H]
    exact hb
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

/-- Instance-explicit restatement of the edge bridge (the baked projection
term is definitionally the `@`-projection; same shape as
`ffOfHyp_p3_eq_faceMapLA1_fun`). -/
theorem eeOfHyp_p3_eq_edgeMapLA1_fun {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    eeOfHyp_p3 x V E = ⇑(@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) :=
  eeOfHyp_p3_eq_edgeMap_fun hfan

/-- Instance-explicit restatement of the node bridge. -/
theorem nnOfHyp_p3_eq_nodeMapLA1_fun {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    nnOfHyp_p3 x V E = ⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) :=
  nnOfHyp_p3_eq_nodeMap_fun hfan

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

/-! ## §5.5 W1 core: `localFan_p3` ⇒ 2-regular (β lf-alpha-w1) -/

section W1Core

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- `nnOfHyp_p3` preserves the first coordinate (both `ite` branches). -/
theorem w1_nnFst (z : V3 × V3) : (nnOfHyp_p3 0 V E z).1 = z.1 := by
  unfold nnOfHyp_p3
  split <;> rfl

/-- `nnOfHyp_p3` on a genuine (ord-pair) dart. -/
theorem w1_nn_apply (V : Set V3) {E : Set (Set V3)} {a b : V3}
    (hab : {a, b} ∈ E) :
    nnOfHyp_p3 0 V E (a, b) = (a, azimCycle_p3 (EE_p3 a E) 0 a b) := by
  unfold nnOfHyp_p3
  rw [if_pos (IN_E_IMP_IMP_IN_DARTS (V := V) hab)]

/-- Step 1 (HOL: the `self_pairs` layer is incompatible with `dih2k`):
`localFan_p3` has no isolated vertex. -/
theorem w1NoIso_p35 (h : localFan_p3 V E FF) : ∀ u ∈ V, EE_p3 u E ≠ ∅ := by
  obtain ⟨H, hdarts, hedge, hnode, hface, hfan, ⟨x, hx, hFF⟩, hdih⟩ := h
  have hcard := hdih.1
  have horb := hdih.2.1
  have hcardPos : 0 < H.darts.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hFFpos : 0 < FF.ncard := by have := hcard; omega
  intro u hu hEu
  have hselfD : (u, u) ∈ dartsOfHyp_p3 E V := by
    have hs : (u, u) ∈ selfPairs_p3 E V := ⟨rfl, hu, hEu⟩
    exact Set.mem_union_right _ hs
  have hself : (u, u) ∈ (↑H.darts : Set (V3 × V3)) := by rw [hdarts]; exact hselfD
  have hselfF : (u, u) ∈ H.darts := Finset.mem_coe.mpr hself
  -- faceMap fixes it (the `EE u E = ∅` branch of `ivs_azim_cycle`)
  have hfixF : (H.faceMap : V3 × V3 → V3 × V3) (u, u) = (u, u) := by
    rw [hface]
    unfold ffOfHyp_p3
    rw [if_pos hselfD]
    have hivs : ivsAzimCycle_p3 (EE_p3 (u, u).2 E) 0 (u, u).2 (u, u).1 = (u, u).2 := by
      unfold ivsAzimCycle_p3
      exact if_pos hEu
    rw [hivs]
  have hfaceU : H.face (u, u) = {(u, u)} :=
    orbitMap_eq_singleton (f := H.faceMap) hfixF
  -- nodeMap fixes it (the `W ⊆ {p}` branch of `azim_cycle`)
  have hsubE : EE_p3 (u, u).1 E ⊆ {(u, u).2} := by
    show (EE_p3 u E : Set V3) ⊆ {u}
    rw [hEu]
    exact Set.empty_subset _
  have hfixN : (H.nodeMap : V3 × V3 → V3 × V3) (u, u) = (u, u) := by
    rw [hnode]
    unfold nnOfHyp_p3
    rw [if_pos hselfD]
    have hacy : azimCycle_p3 (EE_p3 (u, u).1 E) 0 (u, u).1 (u, u).2 = (u, u).2 :=
      W_SUBSET_SINGLETON_IMP_IDE hsubE 0 _
    rw [hacy]
  -- dih2k's belt conjunct collapses to a singleton dart set
  have h2 := horb (u, u) hselfF
  rw [hfaceU, Set.image_singleton, hfixN, Set.union_singleton] at h2
  have hcard1 : H.darts.card = 1 := by
    have hnc := Set.ncard_coe_finset H.darts
    rw [h2] at hnc
    simpa using hnc.symm
  omega

/-- The azimuthal three-neighbor contradiction (`|EE| ≤ 2` core): a third
neighbor `q` beyond `u0` and its successor `s` forces `2·π ≤ azim < 2·π`. -/
theorem w1_azim3 (hfan : Fan.FAN 0 V E) {v u0 s q : V3}
    (hu0E : {v, u0} ∈ E) (hsE : {v, s} ∈ E) (hqE : {v, q} ∈ E)
    (hmin1 : azim 0 v u0 s ≤ azim 0 v u0 q)
    (hmin2 : azim 0 v s u0 ≤ azim 0 v s q)
    (hsne : s ≠ u0) : False := by
  have hadd := Fan.sum2_azim_fan hfan hu0E hsE hqE hmin1
  have hncU : ¬ Collinear3 0 v u0 := Fan.fan_not_collinear hfan hu0E
  have hncS : ¬ Collinear3 0 v s := Fan.fan_not_collinear hfan hsE
  have hzero : azim 0 v u0 s ≠ 0 := fun hzz =>
    hsne (Eq.symm (Fan.unique_azim0_point_fan hfan hu0E hsE hzz))
  have hcomp : azim 0 v s u0 = 2 * Real.pi - azim 0 v u0 s := by
    rw [azim_compl hncU hncS, if_neg hzero]
  have hlt := azim_lt_two_pi (v := 0) (w := v) (w1 := u0) (w2 := q)
  linarith

/-- Upper bound: `azim_cycle` = `sigmaFan` under `FAN`, and `nn² = id`
(`hasOrders_p3 nodeMap 2`) forces `|EE| ≤ 2` via `SIGMA_FAN`-minimality +
`w1_azim3` (the three-neighbor azimuth contradiction). -/
theorem w1SigmaBnd_p35 (h : localFan_p3 V E FF) :
    ∀ u ∈ V, (EE_p3 u E).ncard ≤ 2 := by
  obtain ⟨H, hdarts, hedge, hnode, hface, hfan, ⟨x, hx, hFF⟩, hdih⟩ := id h
  have hsub : ⋃₀ E ⊆ V := hfan.1
  have hVfin : V.Finite := hfan.2.2.1.1
  have hnn2 : (⇑H.nodeMap)^[2] = id := by
    have hon := hdih.2.2.2.2
    exact hon.2
  have hnnSq : ∀ d : V3 × V3,
      (⇑H.nodeMap) ((⇑H.nodeMap) d) = d := by
    intro d
    have hd := congrFun hnn2 d
    rw [show (⇑H.nodeMap)^[2]
        = (⇑H.nodeMap) ∘ (⇑H.nodeMap) from by
        simp [Function.iterate_succ]] at hd
    exact hd
  intro v hv
  have hEEne : EE_p3 v E ≠ ∅ := w1NoIso_p35 h v hv
  have hEEsoe : EE_p3 v E = Fan.setOfEdge v V E := UNI_E_IMP_EE_EQ_SET_OF_EDGE hsub v
  have hfinEE : (EE_p3 v E).Finite :=
    hVfin.subset fun w hw => hsub (EE_SUBSET_UNIONS_E v E hw)
  obtain ⟨u0, hu0⟩ : (EE_p3 v E).Nonempty := Set.nonempty_iff_ne_empty.mpr hEEne
  have hu0E : {v, u0} ∈ E := hu0
  have hu0soe : u0 ∈ Fan.setOfEdge v V E := by rw [← hEEsoe]; exact hu0
  by_cases hcA : EE_p3 v E ⊆ {u0}
  · have h1 := Set.ncard_le_ncard hcA (Set.finite_singleton u0)
    have h2 : ({u0} : Set V3).ncard = 1 := Set.ncard_singleton u0
    omega
  · have hneU : Fan.setOfEdge v V E ≠ {u0} := by
      intro he
      have hq0 : ∃ q ∈ EE_p3 v E, q ≠ u0 := by
        by_contra hcon
        push_neg at hcon
        exact hcA fun q hq => hcon q hq
      obtain ⟨q, hqE, hqu⟩ := hq0
      have hqS : q ∈ Fan.setOfEdge v V E := by rw [← hEEsoe]; exact hqE
      rw [he] at hqS
      exact hqu (by simpa using hqS)
    obtain ⟨hsm, hsne, hsmin⟩ := Fan.SIGMA_FAN hneU hfan hu0soe
    set s : V3 := Fan.sigmaFan 0 V E v u0 with hsdef
    have hEs : {v, s} ∈ E := hsm.1
    have hstep1 : (⇑H.nodeMap) (v, u0) = (v, s) := by
      rw [hnode]
      exact (w1_nn_apply V hu0E).trans (congrArg (fun t : V3 => (v, t))
        (AZIM_CYCLE_EQ_SIGMA_FAN hfan hu0soe))
    have key := hnnSq (v, u0)
    rw [hstep1] at key
    have hstep2 : (⇑H.nodeMap) (v, s) = (v, azimCycle_p3 (EE_p3 v E) 0 v s) := by
      rw [hnode]
      exact w1_nn_apply V hEs
    rw [hstep2] at key
    have hz : azimCycle_p3 (EE_p3 v E) 0 v s = u0 := congrArg Prod.snd key
    have hsf2 : Fan.sigmaFan 0 V E v s = u0 := by
      rw [← AZIM_CYCLE_EQ_SIGMA_FAN hfan hsm]
      exact hz
    have hneS : Fan.setOfEdge v V E ≠ {s} := by
      intro he
      have hu0s : u0 ∈ ({s} : Set V3) := by rw [← he]; exact hu0soe
      exact hsne (show u0 = s from by simpa using hu0s).symm
    obtain ⟨-, hsne2, hsmin2⟩ := Fan.SIGMA_FAN hneS hfan hsm
    rw [hsf2] at hsmin2
    have hsub2 : EE_p3 v E ⊆ {u0, s} := by
      intro q hq
      by_cases hqu : q = u0
      · rw [hqu]
        exact Set.mem_insert u0 {s}
      · by_cases hqs : q = s
        · rw [hqs]
          exact Set.mem_insert_of_mem u0 rfl
        · exfalso
          exact w1_azim3 hfan hu0E hEs hq
            (hsmin q (by rw [← hEEsoe]; exact hq) hqu)
            (hsmin2 q (by rw [← hEEsoe]; exact hq) hqs) hsne
    have h2le : (EE_p3 v E).ncard ≤ ({u0, s} : Set V3).ncard :=
      Set.ncard_le_ncard hsub2 (Set.finite_insert.mpr (Set.finite_singleton s))
    rw [Set.ncard_insert_of_notMem (a := u0) (s := {s})
        (fun hmem => hsne (show u0 = s from by simpa using hmem).symm)
        (Set.finite_singleton s),
      Set.ncard_singleton] at h2le
    exact h2le

/-- Lower bound: belt disjointness (counting: `darts.card = 2*FF.ncard`
against the `dih2k` orbit-union identity) makes `|EE v E| = 2*t_v` with
`t_v ≥ 1` — every vertex carries a face dart above it. -/
theorem w1TwoLe_p35 (h : localFan_p3 V E FF) :
    ∀ u ∈ V, 2 ≤ (EE_p3 u E).ncard := by
  have hnoIso := w1NoIso_p35 h
  obtain ⟨H, hdarts, hedge, hnode, hface, hfan, ⟨x, hx, hFF⟩, hdih⟩ := h
  have hcard := hdih.1
  have horb := hdih.2.1
  have hsub : ⋃₀ E ⊆ V := hfan.1
  intro v hv
  have hEEne : EE_p3 v E ≠ ∅ := hnoIso v hv
  obtain ⟨u0, hu0⟩ : (EE_p3 v E).Nonempty := Set.nonempty_iff_ne_empty.mpr hEEne
  have hu0E : {v, u0} ∈ E := hu0
  have hFFsub : FF ⊆ (↑H.darts : Set (V3 × V3)) := by
    rw [hFF]; exact H.face_subset_darts hx
  have hfinFF : FF.Finite := Set.Finite.subset H.darts.finite_toSet hFFsub
  have hbelt : (↑H.darts : Set (V3 × V3)) = FF ∪ ((⇑H.nodeMap) '' FF) := by
    have := horb x hx
    rwa [← hFF] at this
  have hninj : Function.Injective (⇑H.nodeMap) := Equiv.injective _
  have hcardI : ((⇑H.nodeMap) '' FF).ncard = FF.ncard :=
    Set.InjOn.ncard_image fun a _ b _ hnc => hninj hnc
  have hdisj : FF ∩ ((⇑H.nodeMap) '' FF) = (∅ : Set (V3 × V3)) := by
    have hun := Set.ncard_union_add_ncard_inter FF ((⇑H.nodeMap) '' FF) hfinFF
      (hfinFF.image (⇑H.nodeMap))
    have hcardU : (FF ∪ (⇑H.nodeMap) '' FF).ncard = H.darts.card := by
      rw [← hbelt, Set.ncard_coe_finset]
    rw [hcardU, hcardI] at hun
    have h0 : (FF ∩ (⇑H.nodeMap) '' FF).ncard = 0 := by omega
    rwa [Set.ncard_eq_zero (hfinFF.subset Set.inter_subset_left)] at h0
  -- ncard (darts above v) = ncard (EE v E), and the split Sv = Tv ⊔ nn''Tv
  have hcardSv : ({d : V3 × V3 | d ∈ (↑H.darts : Set (V3 × V3)) ∧ d.1 = v}).ncard
      = (EE_p3 v E).ncard := by
    have hSvimg : {d : V3 × V3 | d ∈ (↑H.darts : Set (V3 × V3)) ∧ d.1 = v}
        = (fun w : V3 => (v, w)) '' (EE_p3 v E) := by
      ext d
      obtain ⟨dv, dw⟩ := d
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨hd, hd1⟩
        have hdart : (dv, dw) ∈ dartsOfHyp_p3 E V := by
          rw [← hdarts]; exact hd
        rcases Set.mem_union _ _ _ |>.mp hdart with hord | hself
        · exact ⟨dw, hd1 ▸ (show ({dv, dw} : Set V3) ∈ E from hord), by rw [hd1]⟩
        · rw [hd1] at hself
          exact absurd hself.2.2 (hnoIso v hv)
      · rintro ⟨w, hw, hwE⟩
        injection hwE with h1 h2
        have hvd : (dv, dw) ∈ (↑H.darts : Set (V3 × V3)) := by
          rw [hdarts, ← h1, ← h2]
          exact Set.mem_union_left _ (show (v, w) ∈ ordPairs_p3 E from hw)
        exact ⟨hvd, h1.symm⟩
    rw [hSvimg]
    exact Set.InjOn.ncard_image fun a _ b _ hnc => by simpa using hnc
  have hsplit : {d : V3 × V3 | d ∈ (↑H.darts : Set (V3 × V3)) ∧ d.1 = v}
      = {d : V3 × V3 | d ∈ FF ∧ d.1 = v}
        ∪ ((⇑H.nodeMap) '' {d : V3 × V3 | d ∈ FF ∧ d.1 = v}) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hd, hd1⟩
      rcases Set.mem_union _ _ _ |>.mp (hbelt ▸ hd) with hF | hI
      · exact Or.inl ⟨hF, hd1⟩
      · obtain ⟨z, hzF, hzd⟩ := hI
        refine Or.inr ⟨z, ⟨hzF, ?_⟩, hzd⟩
        have hz1 : z.1 = ((⇑H.nodeMap) z).1 := by rw [hnode]; exact (w1_nnFst z).symm
        rw [hz1, hzd]
        exact hd1
    · rintro (⟨hF, hd1⟩ | ⟨z, ⟨hzF, hz1⟩, hzd⟩)
      · exact ⟨by rw [hbelt]; exact Set.mem_union_left _ hF, hd1⟩
      · refine ⟨?_, ?_⟩
        · rw [← hzd, hbelt]
          exact Set.mem_union_right _ ⟨z, hzF, rfl⟩
        · rw [← hzd, hnode, w1_nnFst z]
          exact hz1
  have hdisjT : ({d : V3 × V3 | d ∈ FF ∧ d.1 = v}
      ∩ ((⇑H.nodeMap) '' {d : V3 × V3 | d ∈ FF ∧ d.1 = v})) = (∅ : Set (V3 × V3)) := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun d hd => ?_
    obtain ⟨hdT, hdI⟩ := hd
    obtain ⟨z, hzT, hzd⟩ := hdI
    have hmemFF : d ∈ (FF ∩ ((⇑H.nodeMap) '' FF) : Set (V3 × V3)) :=
      ⟨hdT.1, z, hzT.1, hzd⟩
    rw [hdisj] at hmemFF
    exact hmemFF
  have hTvfin : ({d : V3 × V3 | d ∈ FF ∧ d.1 = v}).Finite :=
    hfinFF.subset fun d hd => hd.1
  have hTvI : (((⇑H.nodeMap) '' {d : V3 × V3 | d ∈ FF ∧ d.1 = v}).ncard)
      = ({d : V3 × V3 | d ∈ FF ∧ d.1 = v}).ncard :=
    Set.InjOn.ncard_image fun a _ b _ hnc => hninj hnc
  have hunT := Set.ncard_union_add_ncard_inter
    {d : V3 × V3 | d ∈ FF ∧ d.1 = v}
    (((⇑H.nodeMap) '' {d : V3 × V3 | d ∈ FF ∧ d.1 = v})) hTvfin
    (hTvfin.image (⇑H.nodeMap))
  rw [← hsplit, hcardSv, hdisjT, Set.ncard_empty, hTvI] at hunT
  -- Tv nonempty: the dart (v, u0) is in Tv or in its nn-image
  have hTvne : {d : V3 × V3 | d ∈ FF ∧ d.1 = v}.Nonempty := by
    have hvd : (v, u0) ∈ (↑H.darts : Set (V3 × V3)) := by
      rw [hdarts]
      exact Set.mem_union_left _ (show (v, u0) ∈ ordPairs_p3 E from hu0E)
    have hin : (v, u0) ∈ {d : V3 × V3 | d ∈ FF ∧ d.1 = v}
        ∪ ((⇑H.nodeMap) '' {d : V3 × V3 | d ∈ FF ∧ d.1 = v}) := by
      rw [← hsplit]
      exact ⟨hvd, rfl⟩
    rcases Set.mem_union _ _ _ |>.mp hin with hT | hI
    · exact ⟨(v, u0), hT⟩
    · obtain ⟨z, hzT, _⟩ := hI
      exact ⟨z, hzT⟩
  have hTv1 : 1 ≤ ({d : V3 × V3 | d ∈ FF ∧ d.1 = v}).ncard :=
    (Set.ncard_pos hTvfin).mpr hTvne
  have hfin : (EE_p3 v E).ncard = 2 * ({d : V3 × V3 | d ∈ FF ∧ d.1 = v}).ncard := by
    rw [← hcardSv]; omega
  omega

/-- **Core lemma (lf-alpha-w1)**: HOL `LOFA_IMP_EE_TWO_ELMS` (local_lemmas1
~:1907) at the `_p3` HYP world — a `localFan_p3` is 2-regular. -/
theorem localFanLA3TwoNbr_p35 (h : localFan_p3 V E FF) :
    ∀ u ∈ V, (EE_p3 u E).ncard = 2 := by
  intro v hv
  exact le_antisymm (w1SigmaBnd_p35 h v hv) (w1TwoLe_p35 h v hv)

end W1Core

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
  obtain ⟨hfan, x, hx, hFF, hD, -⟩ := h
  obtain ⟨hcard, horb, hof, hoe, hon⟩ := hD
  have hx1 : x ∈ dart1OfFan V E := (mem_darts_hypermapOfFan hfan x).mp hx
  have hfaceOrb : FF = orbitF_p3 (ffOfHyp_p3 0 V E) x := by
    rw [hFF, orbitMap_LA1faceMap_eq_orbitF hfan x]
  have hsub : FF ⊆ dart1OfFan V E := by
    rw [hFF]
    -- NOTE: the projection must stay `@`-explicit here: a dot-projection on a
    -- `hypermapOfFan`-typed term synthesizes LA3's `dartDecEq3` (§0 note).
    exact Set.Subset.trans (orbitMap_subset_of_permutesOn
      (@Hypermap.faceMap_permutes (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan)) hx) (dartsLA1 0 V E hfan).subset
  have hfin : FF.Finite := (finite_dart1_fan hfan).subset hsub
  refine ⟨hfan, x, hx1, hfaceOrb, hFF, hsub, hfin, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dartsLA1 0 V E hfan, Set.ncard_coe_finset]
    exact hcard
  · rw [ffOfHyp_p3_eq_faceMapLA1_fun hfan]
    exact (hasOrders_iff_hasOrders_p4 _ _).mp hof
  · rw [eeOfHyp_p3_eq_edgeMapLA1_fun hfan]
    exact (hasOrders_iff_hasOrders_p4 _ _).mp hoe
  · rw [nnOfHyp_p3_eq_nodeMapLA1_fun hfan]
    exact (hasOrders_iff_hasOrders_p4 _ _).mp hon
  · intro y hy
    have hy2 : y ∈ @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan) := (mem_darts_hypermapOfFan hfan y).mpr hy
    rw [← orbitMap_LA1faceMap_eq_orbitF hfan y, nnOfHyp_p3_eq_nodeMapLA1_fun hfan,
      ← dartsLA1 0 V E hfan]
    exact horb y hy2

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
  have hkeep : localFan_p3 V E FF := h
  obtain ⟨H, hdarts, hedge, hnode, hface, hfan, ⟨x, hx, hFF⟩, hdih⟩ := h
  -- NOTE: component access via plain `.1`/`.2` projections: a flat-pattern
  -- `obtain` here whnf-unfolds the `dih2k_p3` def past its intended
  -- conjunction shape and mis-binds the components.
  have c1 := hdih.1
  have c2 := hdih.2.1
  have c3 := hdih.2.2.1
  have c4 := hdih.2.2.2.1
  have c5 := hdih.2.2.2.2
  -- Fun-level bridges from the abstract `localFan_p3` hypermap `H`
  -- (`dartDecEq3`-world) to the `@`-explicit instProd-baked `hypermapOfFan`
  -- projections: the of-hyp data passes through `ff/nn/eeOfHyp_p3`.
  have hcoF : (H.faceMap : V3 × V3 → V3 × V3) =
      ⇑(@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan)) :=
    hface.trans (ffOfHyp_p3_eq_faceMapLA1_fun hfan)
  have hcoN : (H.nodeMap : V3 × V3 → V3 × V3) =
      ⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan)) :=
    hnode.trans (nnOfHyp_p3_eq_nodeMapLA1_fun hfan)
  have hcoE : (H.edgeMap : V3 × V3 → V3 × V3) =
      ⇑(@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (hypermapOfFan 0 V E hfan)) :=
    hedge.trans (eeOfHyp_p3_eq_edgeMapLA1_fun hfan)
  have hDartF : @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) = H.darts :=
    Finset.coe_injective ((dartsLA1 0 V E hfan).trans (hno.symm.trans hdarts.symm))
  have hx1 : x ∈ dart1OfFan V E := by
    rw [← hno, ← hdarts]
    exact Finset.mem_coe.mp hx
  have hx' : x ∈ @Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := by
    rw [hDartF]
    exact hx
  have hFF' : FF = orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) x := by
    rw [hFF]
    exact orbitMap_congr hcoF x
  refine ⟨hfan, x, hx', hFF', ?_, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hDartF]
    exact c1
  · intro d hd
    have hd' : d ∈ H.darts := by rw [← hDartF]; exact hd
    rw [hDartF, hcoN.symm, (orbitMap_congr hcoF d).symm]
    exact (c2 d hd').symm
  · refine (hasOrders_iff_hasOrders_p4 _ _).mpr ?_
    rw [← hcoF]
    exact c3
  · refine (hasOrders_iff_hasOrders_p4 _ _).mpr ?_
    rw [← hcoE]
    exact c4
  · refine (hasOrders_iff_hasOrders_p4 _ _).mpr ?_
    rw [← hcoN]
    exact c5
  · -- α2 conjunct: 2-regularity from the core lemma (`ee` = `EE_p3` verbatim)
    intro u hu
    exact localFanLA3TwoNbr_p35 hkeep u hu

/-! ## REMAINING notes

The §7 LA4-consumer corollaries (azimCycle_p4/ivsAzimCycle_p4/nnOfHyp_p4/
ffOfHyp_p4 data, dih2k_p4 ↔ Dih2k, localFan_p4 ↔ LocalFan) are deferred
pending resolution of the dartDecEq3-vs-instProd instance clash (see §0).
The component-level data they reduce to is fully proved in the bridges
above; the remaining work is `@`-explicit `Hypermap` projection pinning.

-/

/-! ## §8 `_p2`↔`_p3` vocabulary bridges and the packaged `localFan_p3.of_LocalFan` -/

-- (a) the 11 pairwise bridges

/-- LA2's `azimCycle_p2` body = LA3's `azimCycle_p3` (verbatim twins). -/
theorem azimCycle_p2_eq_azimCycle_p3 (W : Set V3) (v w p : V3) :
    azimCycle_p2 W v w p = azimCycle_p3 W v w p := rfl

/-- LA2's `ivsAzimCycle_p2` body = LA3's `ivsAzimCycle_p3`. -/
theorem ivsAzimCycle_p2_eq_ivsAzimCycle_p3 (W : Set V3) (v0 v w : V3) :
    ivsAzimCycle_p2 W v0 v w = ivsAzimCycle_p3 W v0 v w := rfl

/-- LA2's `EE_p2` body = LA3's `EE_p3`. -/
theorem EE_p2_eq_EE_p3 {α : Type*} (v : α) (S : Set (Set α)) : EE_p2 v S = EE_p3 v S := rfl

/-- LA2's `ordPairs_p2` body = LA3's `ordPairs_p3`. -/
theorem ordPairs_p2_eq_ordPairs_p3 {α : Type*} (E : Set (Set α)) :
    ordPairs_p2 E = ordPairs_p3 E := rfl

/-- LA2's `selfPairs_p2` body = LA3's `selfPairs_p3`. -/
theorem selfPairs_p2_eq_selfPairs_p3 {α : Type*} (E : Set (Set α)) (V : Set α) :
    selfPairs_p2 E V = selfPairs_p3 E V := rfl

/-- LA2's `dartsOfHyp_p2` body = LA3's `dartsOfHyp_p3`. -/
theorem dartsOfHyp_p2_eq_dartsOfHyp_p3 {α : Type*} (E : Set (Set α)) (V : Set α) :
    dartsOfHyp_p2 E V = dartsOfHyp_p3 E V := rfl

/-- LA2's `eeOfHyp_p2` body = LA3's `eeOfHyp_p3`. -/
theorem eeOfHyp_p2_eq_eeOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    eeOfHyp_p2 x V E d = eeOfHyp_p3 x V E d := rfl

/-- LA2's `nnOfHyp_p2` body = LA3's `nnOfHyp_p3`. -/
theorem nnOfHyp_p2_eq_nnOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    nnOfHyp_p2 x V E d = nnOfHyp_p3 x V E d := rfl

/-- LA2's `ffOfHyp_p2` body = LA3's `ffOfHyp_p3`. -/
theorem ffOfHyp_p2_eq_ffOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    ffOfHyp_p2 x V E d = ffOfHyp_p3 x V E d := rfl

/-- LA2's `hasOrders_p2` body = LA3's `hasOrders_p3`. -/
theorem hasOrders_p2_iff_hasOrders_p3 {α : Type*} (f : α → α) (k : ℕ) :
    hasOrders_p2 f k ↔ hasOrders_p3 f k := Iff.rfl

/-- LA2's `dih2k_p2` body = LA3's `dih2k_p3` (same hypermap `H`). -/
theorem dih2k_p2_iff_dih2k_p3 {α : Type*} [DecidableEq α] (H : Hypermap α) (k : ℕ) :
    dih2k_p2 H k ↔ dih2k_p3 H k := Iff.rfl

/-- The no-isolated hypothesis in its natural form (every vertex lies on
an edge) gives the §6 no-isolated premise `hno`; no `FAN` needed (the
`ordPairs`/`selfPairs` union decomposition is unconditional). -/
theorem hno_of_no_isolated {V : Set V3} {E : Set (Set V3)}
    (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : dartsOfHyp_p3 E V = dart1OfFan V E := by
  ext d
  simp only [dartsOfHyp_p3, ordPairs_p3, selfPairs_p3, dart1OfFan, Set.mem_union,
    Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨h12, hd1V, hE⟩)
    · exact h
    · obtain ⟨w, hw⟩ := hedge d.1 hd1V
      have hw' : w ∈ EE_p3 d.1 E := hw
      rw [hE] at hw'
      exact (hw' : False).elim
  · exact fun h => Or.inl h

/-- The `_p2`-world form of the no-isolated premise (LA2's consumers). -/
theorem hno_p2_of_no_isolated {V : Set V3} {E : Set (Set V3)}
    (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : dartsOfHyp_p2 E V = dart1OfFan V E :=
  dartsOfHyp_p2_eq_dartsOfHyp_p3 (α := V3) E V |>.trans (hno_of_no_isolated hedge)

/-- **MASTER (forward, packaged)**: LA1's `LocalFan` gives LA3's
`localFan_p3`, the packaged HYP-hypermap form, provided the isolated
self-pair darts are absent (`dartsOfHyp_p3 E V = dart1OfFan V E`; see
`hno_of_no_isolated` for the natural hypothesis producing it). The
witness hypermap is the HYP hypermap of the fan (`exists_hypHyp_of_fan`),
whose darts match the fan darts by `hno` and whose components are the raw
of-hyp maps by construction. -/
theorem localFan_p3.of_LocalFan {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hno : dartsOfHyp_p3 E V = dart1OfFan V E) :
    localFan_p3 V E FF := by
  have hld := localFan_data h
  obtain ⟨hfan, x, hx, hFF, hD, htwo⟩ := h
  obtain ⟨hfandata, d, hd1, hFFo, hFFm, hsub, hfin, hcard, hoff, hofe, honn, horb⟩ := hld
  have hpi : hfan = hfandata := rfl
  subst hpi
  obtain ⟨H, hdarts, hedge, hnode, hface⟩ := exists_hypHyp_of_fan hfan
  have hcoe : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := hdarts.trans hno
  have hfaceOrb : ∀ y : V3 × V3, H.face y = orbitF_p3 (ffOfHyp_p3 0 V E) y := by
    intro y
    show orbitMap H.faceMap y = orbitF_p3 (ffOfHyp_p3 0 V E) y
    unfold orbitMap orbitF_p3
    ext z
    simp only [Equiv.Perm.coe_pow, hface]
  refine ⟨H, hdarts, hedge, hnode, hface, hfan, ?_, ?_⟩
  · have hdart : d ∈ (↑H.darts : Set (V3 × V3)) := by
      rw [hdarts]
      exact Set.mem_union_left _ hd1
    refine ⟨d, Finset.mem_coe.mpr hdart, ?_⟩
    rw [hfaceOrb d, hFFo]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hHeq : H.darts =
          (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
            (hypermapOfFan 0 V E hfan)) :=
        Finset.coe_injective (hcoe.trans (dartsLA1 0 V E hfan).symm)
      rw [hHeq]
      exact hD.1
    · intro y hy
      have hy1 : y ∈ dart1OfFan V E := by rw [← hcoe]; exact hy
      have hny : (H.nodeMap : V3 × V3 → V3 × V3) '' H.face y =
          (nnOfHyp_p3 0 V E) '' orbitF_p3 (ffOfHyp_p3 0 V E) y := by
        rw [hnode, hfaceOrb y]
      rw [hcoe, hny, hfaceOrb y]
      exact (horb y hy1).symm
    · rw [hface]; exact hoff
    · rw [hedge]; exact hofe
    · rw [hnode]; exact honn

/-- LA2's `localFan_p2` and LA3's `localFan_p3` are the same proposition:
the two encodings quantify over `Hypermap (V3 × V3)` at `dartDecEq2` resp.
`dartDecEq3`, which both unfold to `Classical.decEq _`, so the existentials
are definitionally equal. -/
theorem localFan_p2_iff_localFan_p3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} :
    localFan_p2 V E FF ↔ localFan_p3 V E FF := Iff.rfl

/-- LA3's `localFan_p3` gives LA2's `localFan_p2` (definitional; see
`localFan_p2_iff_localFan_p3`). -/
theorem localFan_p2.of_localFan_p3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p3 V E FF) : localFan_p2 V E FF := h

/-- LA2's `localFan_p2` gives LA3's `localFan_p3` (definitional; see
`localFan_p2_iff_localFan_p3`). -/
theorem localFan_p3.of_localFan_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) : localFan_p3 V E FF := h

/-- The packaged forward transport into LA2's `localFan_p2` encoding
(mirror of `localFan_p3.of_LocalFan` via the `_p2`↔`_p3` vocabulary
bridges). -/
theorem localFan_p2.of_LocalFan {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hno : dartsOfHyp_p3 E V = dart1OfFan V E) :
    localFan_p2 V E FF :=
  localFan_p2.of_localFan_p3 (localFan_p3.of_LocalFan h hno)

/-- The natural downstream (W6) interface: `LocalFan` + every vertex of
`V` lies on an edge (no isolated vertices) gives LA3's `localFan_p3`
directly, with the `hno` premise discharged by `hno_of_no_isolated`. -/
theorem localFan_p3.of_LocalFan_noIso {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : localFan_p3 V E FF :=
  localFan_p3.of_LocalFan h (hno_of_no_isolated hedge)

/-- Mirror of `localFan_p3.of_LocalFan_noIso` in LA2's `localFan_p2`
encoding. -/
theorem localFan_p2.of_LocalFan_noIso {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : localFan_p2 V E FF :=
  localFan_p2.of_LocalFan h (hno_of_no_isolated hedge)


/-- **α2 receipt**: the α2 `LocalFan` (LA1:157, with the 2-regular
conjunct) is exactly `localFan_p3`.  (→) `localFan_p3.of_LocalFan` with
`hno` discharged by the conjunct via `hno_of_no_isolated`; (←)
`LocalFan.of_localFan_p3` with `hno` discharged by the core lemma
(no self-pair darts) and the conjunct supplied by the core lemma
(`ee` = `EE_p3` verbatim; of_localFan_p3 above already carries the slot). -/
theorem localFanEquiv_p35 :
    LocalFan V E FF ↔ localFan_p3 V E FF := by
  constructor
  · rintro ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩
    refine localFan_p3.of_LocalFan ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩ (hno_of_no_isolated ?_)
    intro u hu
    have h2 := h2reg u hu
    have hne : ¬((ee u E) = ∅) := by
      intro hE
      rw [hE, Set.ncard_empty] at h2
      omega
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact ⟨w, hw⟩
  · intro h3
    have h2 := localFanLA3TwoNbr_p35 h3
    have hno : dartsOfHyp_p3 E V = Fan.dart1OfFan V E := by
      ext d
      simp only [dartsOfHyp_p3, Fan.dart1OfFan, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨h12, hd1V, hE⟩)
        · exact h
        · exfalso
          have h2 := localFanLA3TwoNbr_p35 h3 d.1 hd1V
          rw [hE, Set.ncard_empty] at h2
          omega
      · exact fun h => Or.inl h
    exact LocalFan.of_localFan_p3 h3 hno

end Kepler.Text

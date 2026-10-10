/-
Kepler.Text.LocalAuto2 — Local Fan chapter: the localization block.

HOL sources (persistent copies under `lean/scripts/local/`):
- `localization.hl` (1595 ln, 40 defs + 43 theorems): odds and ends from the
  first part of the Local Fan chapter — the `local_fan` family, the HYP
  hypermap kit (`darts/ee/nn/ff_of_hyp`), wedge/azim-in-fan vocabulary,
  `v_prime`/`e_prime`, the slice kit (`slicev/slicee/slicef`), `sol_local`/
  `tau_fun`/`tauVEF`, and the ear constants.
- `LDURDPN.hl` (126 ln): `SUBSET_P_HULL`, `IN_HULL_INSERT`,
  `VECTOR_SCALE_CHANGE`, `AFF_CONV0_IN_AFF_LT`, `LDURDPN` (azim = pi iff
  coplanar and the open cone meets the affine hull).
- `LFJCIXP.hl` (64 ln): the `delta`/ball-annulus diameter bound `LFJCIXP`.

Encoding notes.
- HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; darts are `V3 × V3`.
- HOL `ITER i f` ↔ `f^[i]` (`Function.iterate`); `orbit_map` on a plain
  function ↦ `orbitF_p2` (the `Equiv.Perm` version is `Kepler.Text.orbitMap`).
- **`local_fan` (localization.hl:66) is the chapter's central structure.**
  HOL builds `hypermap (HYP (vec 0, V, E))` by applying the 4-tuple
  constructor; our `Hypermap` is a proof-carrying structure (Finset of darts
  plus `Equiv.Perm`s), so the constructor application is rendered
  *existentially*: `localFan_p2` quantifies over the `Hypermap` whose dart
  set and e/n/f maps are *equal to the components of* `HYP_p2 0 V E`
  (predicate `IsHyp_p2`), then states `FAN 0 V E`, the face-generation
  clause, and `dih2k H (CARD FF)` verbatim. Same rendering as the reviewed
  `localFan_p3` encoding.
- `rho_node1` is defined TWICE in localization.hl (lines 72 and 115); the
  later definition overrides the former, so `rhoNode1_p2` ports the line-115
  version (`FF : real^3#real^3 -> bool`, `(v,w) IN FF`). `rho_fun` and
  `tau_fun` are likewise re-defined (identically) later in the file.
- HOL `CARD s` ↔ `Set.ncard` (the `CARD s > 1` finiteness side condition is
  absorbed by the `ncard`-of-infinite-set-is-0 convention).
- HOL `sum S f` over a set ↔ `Kepler.Text.setSum` (junk value 0 on infinite
  sets), the PackingAuto2 convention. Note `&(CARD f - 2)` in `tau_fun` is a
  cast of *truncated* natural subtraction, while `&2 - &(CARD f)` in
  `tauVEF` is genuine real subtraction — both ported verbatim.
- `hypermap (HYP (vec 0, V, E))` as a *hypothesis* of later theorems (e.g.
  `COMPATIBLE_BW_TWO_LEMMAS2_ALT`) ↦ `IsHyp_p2 0 V E HS`. HOL `graph` ↦ the
  importable `Kepler.Text.Fan.Graph`; `fan1/fan2/fan6` likewise imported.
- Parallel lanes own the unsuffixed versions of these declarations
  (`LocalFan`, `azimInFan`, `rhoFun`, `rho`, `cstab`, `azimCycle`, ... in
  LocalAuto1/LocalAnchors and the `_p3`/`_p4` copies in LocalAuto3/4);
  everything here is the `_p2` copy of this lane with `NEEDS` merge markers.
  Do NOT import the parallel lanes from here.
- LDURDPN/LFJCIXP-specific vocabulary: `conv0` ↦ `conv0_p2` (affsign sgn_gt
  at the empty base), `plane` ↦ `plane_p2`, `P hull` ↦ `convexHull ℝ`,
  `delta` (collect_geom) ↦ the importable `deltaX` (same Cayley–Menger
  determinant; the historic hub spelling `deltaXf` was renamed away in the
  atn2-merge wave 3), `packing` ↦ `Kepler.Packing`, `ball_annulus` ↦
  `Kepler.Text.ballAnnulus`, `sol_y` ↦ `Kepler.Text.solY`.
- DEDUP (atn2-merge wave 3): the sphere.hl numeric kit this file consumes
  (`atn2`, `deltaX`, `dihXf`, `dihY`, `solY`, `const1`, …) is single-sourced
  in `Kepler.Text.SphereKit` (reached transitively via `PackingAuto20`);
  the hub's `atn2` clash is gone and `LocalAuto1` + `LocalAuto2` are
  co-importable again (dual-import probe verified 2026-09-18). The
  localization/dih2k kit (`azimCycle_p2`, `EE_p2`, `rhoNode1_p2`, …,
  `dih2k_p2`) STAYS here: `SphereKit` defers it until a rendering bridge
  exists (plan §6).
- WRGCVDR_BIJ wave (2026-10-08): `WRGCVDR_BIJ` (localization.hl:356) is
  closed by direct construction — the proved `LocalAuto3` bij kit mirrored
  as the private `p2_*` block before the giants section (same-`fst` ⟹ same
  node orbit ⟹ same face orbit ⟹ `Simple`); this adds the acyclic import
  `Kepler.Text.TopologyFan` (`orbit_eq_setOfEdge`; depends only on `Fan`,
  downstream interfaces unchanged) and fills `AZIM_CYCLE_EQ_SIGMA_FAN_ALT`
  via `p2_AZIM_CYCLE_EQ_SIGMA_FAN` + `EE_elim`.
- WRGCVDR orbit wave (2026-10-08): `WRGCVDR_ORBIT` (localization.hl:365, the
  orbit half of HOL `WRGCVDR` WRGCVDR.hl:2622) is closed on top of
  `WRGCVDR_BIJ` — `lemma_face_identity` ↦ `orbitMap_eq_of_mem` gives the
  common face orbit, `ff_of_hyp` on darts + FST-determinacy gives the
  `face_map ↔ hro POWER n` correspondence, and both set inclusions read off
  darts (`p2_IN_DARTS_HYP_IMP_FST_SND_IN_V`); unlocks the LA5
  `LOCAL_FAN_ORBIT_MAP_V` blocking chain.
-/

import Kepler.Text.Polytope
import Kepler.Text.Fan
import Kepler.Text.TopologyFan
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto3
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto20
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## Support instances and plain-function iteration kit -/

/-- Darts are `V3 × V3`; classical decidability for `Hypermap (V3 × V3)`. -/
noncomputable instance dartDecEq2 : DecidableEq (V3 × V3) := Classical.decEq _

/-- HOL `orbit_map f x` (hypermap.hl:49) on a plain function. NEEDS: merge
with the hypermap layer's plain-function `orbit_map` (cf. `orbitF_p3`). -/
def orbitF_p2 {α : Type*} (f : α → α) (x : α) : Set α := {y | ∃ n : ℕ, f^[n] x = y}

/-- HOL `azim_cycle` (sphere.hl:414; minimal azimuth, distance tiebreak,
`W SUBSET {p}` degenerate case). NEEDS: upstream home in the sphere/fan_defs
layer; `_p2` copy of the `azimCycle_p3`/`azimCycle_p4` parallel copies.
HOL `projection (w-v) (u-v)` ↔ repo `projection (u - v) (w - v)`. -/
noncomputable def azimCycle_p2 (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-! ## Orders, cyclicity, dih2k (localization.hl:20–36) -/

/-- HOL `has_orders` (localization.hl:20). -/
def hasOrders_p2 {α : Type*} (f : α → α) (k : ℕ) : Prop :=
  (∀ i, 0 < i → i < k → ¬(f^[i] = id)) ∧ f^[k] = id

/-- HOL `order f x y` (localization.hl:24): least `n` with `f^[n] x = y`
(HOL choice; junk value when no such `n`). -/
noncomputable def order_p2 {α : Type*} (f : α → α) (x y : α) : ℕ :=
  Classical.epsilon fun n => f^[n] x = y ∧ ∀ i, 0 < i → i < n → ¬(f^[i] x = y)

/-- HOL `cyclic_on` (localization.hl:27). -/
def cyclicOn_p2 {α : Type*} (f : α → α) (S : Set α) : Prop :=
  ∀ x ∈ S, S = {z | ∃ n : ℕ, z = f^[n] x}

/-- HOL `dih2k H k` (localization.hl:30), over the proof-carrying `Hypermap`
structure (finiteness of darts built in). -/
def dih2k_p2 {α : Type*} [DecidableEq α] (H : Hypermap α) (k : ℕ) : Prop :=
  H.darts.card = 2 * k ∧
    (∀ x ∈ H.darts, (↑H.darts : Set α) = H.face x ∪ (H.nodeMap : α → α) '' H.face x) ∧
    hasOrders_p2 (H.faceMap : α → α) k ∧
    hasOrders_p2 (H.edgeMap : α → α) 2 ∧
    hasOrders_p2 (H.nodeMap : α → α) 2

/-! ## The HYP hypermap kit (localization.hl:38–70) -/

/-- HOL `EE v S` (localization.hl:38). -/
def EE_p2 {α : Type*} (v : α) (S : Set (Set α)) : Set α := {w | {v, w} ∈ S}

/-- HOL `ord_pairs E` (localization.hl:40). -/
def ordPairs_p2 {α : Type*} (E : Set (Set α)) : Set (α × α) := {p | {p.1, p.2} ∈ E}

/-- HOL `self_pairs E V` (localization.hl:42). -/
def selfPairs_p2 {α : Type*} (E : Set (Set α)) (V : Set α) : Set (α × α) :=
  {p | p.1 = p.2 ∧ p.1 ∈ V ∧ EE_p2 p.1 E = ∅}

/-- HOL `darts_of_hyp E V` (localization.hl:45). -/
def dartsOfHyp_p2 {α : Type*} (E : Set (Set α)) (V : Set α) : Set (α × α) :=
  ordPairs_p2 E ∪ selfPairs_p2 E V

/-- HOL `ee_of_hyp (x,V,E)` (localization.hl:48). -/
noncomputable def eeOfHyp_p2 (_x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p2 E V then (d.2, d.1) else d

/-- HOL `nn_of_hyp (x,V,E)` (localization.hl:51). -/
noncomputable def nnOfHyp_p2 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p2 E V then (d.1, azimCycle_p2 (EE_p2 d.1 E) x d.1 d.2) else d

/-- HOL `ivs_azim_cycle W v0 v w` (localization.hl:55). -/
noncomputable def ivsAzimCycle_p2 (W : Set V3) (v0 v w : V3) : V3 :=
  if W = ∅ then w else Classical.epsilon fun x => x ∈ W ∧ azimCycle_p2 W v0 v x = w

/-- HOL `ff_of_hyp (x,V,E)` (localization.hl:59). -/
noncomputable def ffOfHyp_p2 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p2 E V then (d.2, ivsAzimCycle_p2 (EE_p2 d.2 E) x d.2 d.1) else d

/-- HOL `HYP (x,V,E)` (localization.hl:63): the 4-tuple
`(darts_of_hyp, ee_of_hyp, nn_of_hyp, ff_of_hyp)`. -/
noncomputable def HYP_p2 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Set (V3 × V3) × ((V3 × V3 → V3 × V3) × ((V3 × V3 → V3 × V3) × (V3 × V3 → V3 × V3))) :=
  (dartsOfHyp_p2 E V, (eeOfHyp_p2 x V E, (nnOfHyp_p2 x V E, ffOfHyp_p2 x V E)))

/-- HOL `hypermap (HYP (x, V, E))` (constructor application) as a predicate:
`HS` is a `Hypermap` whose components are exactly the `HYP_p2 x V E` pieces.
Used to render the `HS = hypermap (HYP ...)` hypotheses of the slice
theorems; `localFan_p2` unfolds to the same condition inlined. -/
def IsHyp_p2 (x : V3) (V : Set V3) (E : Set (Set V3)) (HS : Hypermap (V3 × V3)) : Prop :=
  (↑HS.darts : Set (V3 × V3)) = dartsOfHyp_p2 E V ∧
    (HS.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p2 x V E ∧
    (HS.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p2 x V E ∧
    (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p2 x V E

/-- HOL `local_fan (V,E,FF)` (localization.hl:66) — **the chapter's central
structure**. HOL: `let H = hypermap (HYP (vec 0, V, E)) in FAN (vec 0, V, E)
/\ (?x. x IN dart H /\ FF = face H x) /\ dih2k H (CARD FF)`. Since the repo
`Hypermap` is proof-carrying (no 4-tuple constructor), the let-bound
`hypermap (HYP ...)` is rendered existentially over the `Hypermap` whose
components are the `HYP_p2 0 V E` pieces (cf. `IsHyp_p2`, `localFan_p3`). -/
def localFan_p2 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  ∃ HS : Hypermap (V3 × V3),
    (↑HS.darts : Set (V3 × V3)) = dartsOfHyp_p2 E V ∧
    (HS.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p2 0 V E ∧
    (HS.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p2 0 V E ∧
    (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p2 0 V E ∧
    FAN 0 V E ∧
    (∃ x ∈ HS.darts, FF = HS.face x) ∧
    dih2k_p2 HS FF.ncard

/-! ## rho_node1, wedges, azim_in_fan (localization.hl:74–153) -/

/-- HOL `rho_node1` (localization.hl:115 — the *second* definition in the
file, which overrides the line-72 version). NEEDS: merge with
`LocalAnchors.rhoNode1`. -/
noncomputable def rhoNode1_p2 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon fun w => (v, w) ∈ FF

/-- HOL `ivs_rho_node1` (localization.hl:117). NEEDS: merge with
`LocalAnchors.ivsRhoNode1`. -/
noncomputable def ivsRhoNode1_p2 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon fun a => (a, v) ∈ FF

/-- HOL `interior_angle1 x FF v` (localization.hl:119). NEEDS: merge with
`LocalAnchors.interiorAngle1`. -/
noncomputable def interiorAngle1_p2 (x : V3) (FF : Set (V3 × V3)) (v : V3) : ℝ :=
  azim x v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)

/-- HOL `azim_in_fan` (localization.hl:74). NEEDS: merge with
`LocalAnchors.azimInFan`. -/
noncomputable def azimInFan_p2 (d : V3 × V3) (E : Set (Set V3)) : ℝ :=
  if 1 < (EE_p2 d.1 E).ncard then azim 0 d.1 d.2 (azimCycle_p2 (EE_p2 d.1 E) 0 d.1 d.2)
  else 2 * Real.pi

/-- HOL `wedge_in_fan_gt` (localization.hl:79). NEEDS: merge with the
`wedgeInFanGt_p3` copy. -/
noncomputable def wedgeInFanGt_p2 (d : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (EE_p2 d.1 E).ncard then
    wedge 0 d.1 d.2 (azimCycle_p2 (EE_p2 d.1 E) 0 d.1 d.2)
  else if EE_p2 d.1 E = {d.2} then
    {x | x ∉ affGe ({0, d.1} : Set V3) {d.2}}
  else
    {x | x ∉ affineSpan ℝ ({0, d.1} : Set V3)}

/-- HOL `wedge_ge` (localization.hl:85). Identical body to the importable
`Kepler.Text.wedgeGe` (PackingAuto2); kept as a `_p2` copy per lane
convention. NEEDS: dedup at merge. -/
def wedgeGe_p2 (v0 v1 w1 w2 : V3) : Set V3 :=
  {z | 0 ≤ azim v0 v1 w1 z ∧ azim v0 v1 w1 z ≤ azim v0 v1 w1 w2}

/-- HOL `wedge_in_fan_ge` (localization.hl:88). NEEDS: merge with the
`wedgeInFanGe_p3` copy. -/
noncomputable def wedgeInFanGe_p2 (d : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (EE_p2 d.1 E).ncard then
    wedgeGe_p2 0 d.1 d.2 (azimCycle_p2 (EE_p2 d.1 E) 0 d.1 d.2)
  else Set.univ

/-- HOL `convex_local_fan` (localization.hl:92). NEEDS: merge with
`LocalAnchors.ConvexLocalFan`. -/
def convexLocalFan_p2 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  localFan_p2 V E FF ∧
    ∀ x ∈ FF, azimInFan_p2 x E ≤ Real.pi ∧ V ⊆ wedgeInFanGe_p2 x E

/-- HOL `v_prime` (localization.hl:97). -/
def vPrime_p2 (V : Set V3) (FF : Set (V3 × V3)) : Set V3 :=
  {v | v ∈ V ∧ ∃ w, (v, w) ∈ FF}

/-- HOL `e_prime` (localization.hl:100): `{{v,w} | {v,w} IN E /\ (v,w) IN FF}`. -/
def ePrime_p2 (E : Set (Set V3)) (FF : Set (V3 × V3)) : Set (Set V3) :=
  {e | ∃ v w, e = {v, w} ∧ {v, w} ∈ E ∧ (v, w) ∈ FF}

/-- HOL `generic` (localization.hl:103). NEEDS: merge with
`LocalAnchors.Generic`. -/
def generic_p2 (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v w u : V3, {v, w} ∈ E → u ∈ V → affGe ({0} : Set V3) {v, w} ∩ affLt ({0} : Set V3) {u} = ∅

/-- HOL `circular` (localization.hl:107). NEEDS: merge with
`LocalAnchors.Circular`. -/
def circular_p2 (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∃ v w u : V3, {v, w} ∈ E ∧ u ∈ V ∧ ¬(affGe ({0} : Set V3) {v, w} ∩ affLt ({0} : Set V3) {u} = ∅)

/-- HOL `lunar` (localization.hl:111). NEEDS: merge with
`LocalAnchors.Lunar`. -/
def lunar_p2 (v w : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ¬circular_p2 V E ∧ {v, w} ⊆ V ∧ v ≠ w ∧ Collinear ℝ ({0, v, w} : Set V3)

/-- HOL `sol_local` (localization.hl:122). NEEDS: merge with
`LocalAnchors.solLocal`. -/
noncomputable def solLocal_p2 (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  2 * Real.pi + setSum f (fun e => azimInFan_p2 e E - Real.pi)

/-- HOL `rho_fun` (localization.hl:124; re-defined verbatim at 1541).
NEEDS: merge with `LocalAnchors.rhoFun`. -/
noncomputable def rhoFun_p2 (y : ℝ) : ℝ :=
  1 + (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (y - 2)

/-- HOL `tau_fun` (localization.hl:126; re-defined verbatim at 1562).
NEEDS: merge with `LocalAnchors.tauFun`. -/
noncomputable def tauFun_p2 (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  setSum f (fun e => rhoFun_p2 ‖e.1‖ * azimInFan_p2 e E) -
    (Real.pi + sol0) * ((f.ncard - 2 : ℕ) : ℝ)

/-- HOL `deformation` (localization.hl:128); `real_interval (a,b)` ↦ the
closed interval `Set.Icc a b`, `continuous atreal` ↦ `ContinuousAt`. NEEDS:
merge with `LocalAnchors.Deformation`. -/
def deformation_p2 (ff : V3 → ℝ → V3) (V : Set V3) (a b : ℝ) : Prop :=
  (0 : ℝ) ∈ Set.Icc a b ∧
    (∀ v : V3, v ∈ V → ∀ r : ℝ, r ∈ Set.Icc a b → ContinuousAt (ff v) r) ∧
    ∀ v ∈ V, ff v 0 = v

/-- HOL `localization (V,E) FF` (localization.hl:133). -/
def localization_p2 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) :
    Set V3 × Set (Set V3) :=
  (vPrime_p2 V FF, ePrime_p2 E FF)

/-- HOL `cstab` (informal value 3.01; `Pack_defs.cstab`). NEEDS: merge with
`LocalAnchors.cstab`. -/
noncomputable def cstab_p2 : ℝ := 3.01

/-- HOL `a_ear0` (localization.hl:135); `J` is a set of residue-edges. -/
noncomputable def aEar0_p2 (J : Set (Set ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if ({i % 3, j % 3} : Set ℕ) ∈ J then Real.sqrt 8 else 2

/-- HOL `b_ear0` (localization.hl:138). -/
noncomputable def bEar0_p2 (J : Set (Set ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if ({i % 3, j % 3} : Set ℕ) ∈ J then cstab_p2 else 2 * h0

/-- HOL `JNVXCRC`, i.e. `polar_fan (V,E,FF)` (localization.hl:141): the
polar fan with `r = rho_node1 FF` and `prime v = v cross (r v)`. The cross
product uses the repo `WithLp.toLp 2 (crossProduct …)` idiom. -/
noncomputable def polarFan_p2 (V : Set V3) (FF : Set (V3 × V3)) :
    Set V3 × Set (Set V3) × Set (V3 × V3) :=
  let r := rhoNode1_p2 FF
  let prime : V3 → V3 := fun v =>
    WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ) ((r v : V3) : Fin 3 → ℝ))
  (prime '' V, (fun v => {prime v, prime (r v)}) '' V,
    (fun v => (prime v, prime (r v))) '' V)

/-- HOL `slicev` (localization.hl:149); the `0 <= n` clause is vacuous for
`ℕ`. -/
def slicev_p2 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) : Set V3 :=
  {u | ∃ n : ℕ, n ≤ order_p2 (rhoNode1_p2 FF) v w ∧ u = (rhoNode1_p2 FF)^[n] v}

/-- HOL `slicee` (localization.hl:151); `s DELETE w` ↦ `{u | u ∈ s ∧ u ≠ w}`. -/
def slicee_p2 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) : Set (Set V3) :=
  {e | ∃ u, u ∈ slicev_p2 E FF v w ∧ u ≠ w ∧ e = {u, rhoNode1_p2 FF u}} ∪ {{w, v}}

/-- HOL `slicef` (localization.hl:153). -/
def slicef_p2 (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3) : Set (V3 × V3) :=
  {f | ∃ u, u ∈ slicev_p2 E FF v w ∧ u ≠ w ∧ f = (u, rhoNode1_p2 FF u)} ∪ {(w, v)}

/-! ## h_dart, tauVEF and the rho/ly constants (localization.hl:1541–1560) -/

/-- HOL `interp` (sphere.hl:190). NEEDS: upstream sphere-layer home. -/
noncomputable def interp_p2 (x1 y1 x2 y2 x : ℝ) : ℝ :=
  y1 + (x - x1) * (y2 - y1) / (x2 - x1)

/-- HOL `ly` (sphere.hl:199). NEEDS: merge with the sphere layer's `ly`. -/
noncomputable def ly_p2 (y : ℝ) : ℝ := interp_p2 2 1 2.52 0 y

/- DEDUP (atn2-merge wave 3): the verbatim twin `const1_p2`
(`solY 2 2 2 2 2 2 / pi`) is deleted; `rho_p2` consumes the canonical
`Kepler.Text.const1` from `Kepler.Text.SphereKit` (via PackingAuto20),
whose body is verbatim-identical. `ly_p2`/`interp_p2` stay: not
syntactic twins of SphereKit `ly` (plan §6). -/

/-- HOL `rho` (sphere.hl:201). NEEDS: merge with `LocalAnchors.rho`. -/
noncomputable def rho_p2 (y : ℝ) : ℝ := 1 + const1 - const1 * ly_p2 y

/-- HOL `h_dart` (localization.hl:1557). -/
noncomputable def hDart_p2 (x : V3 × V3) : ℝ := ‖x.1‖ / 2

/-- HOL `tauVEF` (localization.hl:1559). Note the `&2 - &(CARD f)` here is
*real* subtraction (unlike `tau_fun`'s truncated-natural `CARD f - 2`). -/
noncomputable def tauVEF_p2 (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  setSum f (fun x => azimDart V E x * (1 + (sol0 / Real.pi) * (1 - lmfun (hDart_p2 x)))) +
    (Real.pi + sol0) * (2 - (f.ncard : ℝ))

/-! ## LDURDPN support defs -/

/-- HOL `conv0` (sphere.hl:294): `affsign sgn_gt {} S`, the open cone. -/
def conv0_p2 (S : Set V3) : Set V3 := {v | Affsign (fun x : ℝ => 0 < x) ∅ S v}

/-- HOL `plane` (sphere.hl:345): spanned by three non-collinear points. -/
def plane_p2 (A : Set V3) : Prop :=
  ∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧ A = affineSpan ℝ ({u, v, w} : Set V3)

/-! ## Mechanical theorems (proved) -/

/-- HOL `FAN_EDGE_SUBSET_V` (localization.hl:155). -/
theorem FAN_EDGE_SUBSET_V (hfan : FAN 0 V E) {e : Set V3} (he : e ∈ E) : e ⊆ V :=
  (Set.subset_sUnion_of_mem he).trans hfan.1

/-- HOL `FAN_EDGE_EL_V` (localization.hl:164). -/
theorem FAN_EDGE_EL_V (hfan : FAN 0 V E) {u v : V3} (he : {u, v} ∈ E) : v ∈ V :=
  FAN_EDGE_SUBSET_V hfan he (by simp)

/-- HOL `EE_elim` (localization.hl:177): under a fan, `EE v E` is the
neighbor set of `v`. -/
theorem EE_elim (hfan : FAN 0 V E) (v : V3) : EE_p2 v E = setOfEdge v V E := by
  ext w
  show w ∈ EE_p2 v E ↔ w ∈ setOfEdge v V E
  simp only [EE_p2, setOfEdge, Set.mem_setOf_eq]
  constructor
  · exact fun h => ⟨h, FAN_EDGE_EL_V hfan h⟩
  · exact fun h => h.1

/-- HOL `dart_of_fan_eq` (localization.hl:201). -/
theorem dart_of_fan_eq (V : Set V3) (E : Set (Set V3)) :
    dartOfFan V E =
      dart1OfFan V E ∪ {d | d.1 = d.2 ∧ d.1 ∈ V ∧ setOfEdge d.1 V E = ∅} := by
  rw [dartOfFan, Set.union_comm]

/-- HOL `darts_of_hyp_elim` (localization.hl:190). -/
theorem darts_of_hyp_elim (hfan : FAN 0 V E) : dartsOfHyp_p2 E V = dartOfFan V E := by
  have hEE := EE_elim hfan
  ext d
  simp only [dartsOfHyp_p2, ordPairs_p2, selfPairs_p2, dartOfFan, dart1OfFan,
    Set.mem_union, Set.mem_setOf_eq]
  rw [hEE]
  tauto

/-- HOL `ee_of_hyp_elim` (localization.hl:215). -/
theorem ee_of_hyp_elim (hfan : FAN 0 V E) :
    eeOfHyp_p2 0 V E = eFanPairExt V E := by
  have hkey : ∀ d : V3 × V3, d ∈ dartOfFan V E → (d.2, d.1) = d ∨ d ∈ dart1OfFan V E := by
    intro d hd
    rw [dartOfFan] at hd
    rcases Set.mem_or_mem_of_mem_union hd with h | h
    · refine Or.inl ?_
      obtain ⟨a, b⟩ := d
      have h12 : a = b := h.1
      rw [h12]
    · exact Or.inr h
  funext d
  simp only [eeOfHyp_p2, eFanPairExt]
  by_cases h1 : d ∈ dart1OfFan V E
  · have hm : d ∈ dartsOfHyp_p2 E V := by
      rw [darts_of_hyp_elim hfan]
      rw [dart_of_fan_eq]
      exact Set.mem_union_left _ h1
    rw [if_pos hm, if_pos h1]; rfl
  · by_cases h2 : d ∈ dartsOfHyp_p2 E V
    · rw [if_pos h2, if_neg h1]
      rcases hkey d ((darts_of_hyp_elim hfan) ▸ h2) with he | hc
      · rw [he]
      · exact absurd hc h1
    · rw [if_neg h2, if_neg h1]

/-- HOL `V_PRIME_SUBSET_V` (localization.hl:540). -/
theorem V_PRIME_SUBSET_V (V : Set V3) (f : Set (V3 × V3)) : vPrime_p2 V f ⊆ V := by
  intro v hv
  exact hv.1

/-- HOL `WEDGE_VV` (localization.hl:450): the apex-side vertex is never in
the open wedge. -/
theorem WEDGE_VV (a b c d : V3) : b ∉ wedge a b c d := by
  intro hb
  simp only [wedge, Set.mem_setOf_eq] at hb
  refine hb.1 ?_
  simpa [Collinear3] using collinear_pair ℝ a b

/-- HOL `SUBSET_P_HULL` (LDURDPN.hl:23); `P hull` ↦ `convexHull ℝ`.
NEEDS: merge with `PackingAuto22.SUBSET_P_HULL` (identical). -/
theorem SUBSET_P_HULL_p2 (S : Set V3) : S ⊆ convexHull ℝ S := subset_convexHull ℝ S

/-- HOL `IN_HULL_INSERT` (LDURDPN.hl:26). -/
theorem IN_HULL_INSERT_p2 (x : V3) (S : Set V3) : x ∈ convexHull ℝ (insert x S) :=
  subset_convexHull ℝ _ (Set.mem_insert _ _)

/-- HOL `VECTOR_SCALE_CHANGE` (LDURDPN.hl:33). -/
theorem VECTOR_SCALE_CHANGE {a : ℝ} {x y : V3} (ha : a ≠ 0) : a • x = y ↔ x = (1 / a) • y := by
  constructor
  · intro h
    rw [← h, smul_smul, one_div, inv_mul_cancel₀ ha, one_smul]
  · intro h
    rw [h, smul_smul, one_div, mul_inv_cancel₀ ha, one_smul]

/-- HOL `ly_EQ_lmfun` (localization.hl:1564): on the `≤ 2*h0` range the
piecewise-linear `lmfun` agrees with `ly` (a real-arithmetic identity). -/
theorem ly_EQ_lmfun (x : V3 × V3) (hx : ‖x.1‖ ≤ 2 * h0) :
    lmfun (hDart_p2 x) = ly_p2 ‖x.1‖ := by
  have h2 : ‖x.1‖ / 2 ≤ h0 := by linarith
  have h0v : h0 = 1.26 := rfl
  rw [hDart_p2, lmfun, if_pos h2, ly_p2, interp_p2, h0v]
  field_simp
  ring

/-- HOL `aff_ge_INTER_aff_lt` (localization.hl:1054). -/
theorem aff_ge_INTER_aff_lt {y : V3} (hy : y ≠ 0) :
    affGe ({0} : Set V3) {y} ∩ affLt ({0} : Set V3) {y} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have h1 : Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3) {y} z := hz.1
  have h2 : Affsign (fun x : ℝ => x < 0) ({0} : Set V3) {y} z := hz.2
  unfold Affsign at h1 h2
  obtain ⟨f, ffin, hfz, hfpos, _hfsum⟩ := h1
  obtain ⟨g, gfin, hgz, hgneg, _hgsum⟩ := h2
  have sumEq : ∀ hfin : ({0, y} : Set V3).Finite, ∀ c : V3 → ℝ,
      ∑ w ∈ hfin.toFinset, c w • w = c y • y := by
    intro hfin c
    rw [Finset.sum_eq_single_of_mem y (hfin.mem_toFinset.mpr (by simp))]
    intro b hb hbne
    have hbm : b = 0 ∨ b = y := hfin.mem_toFinset.mp hb
    have hzero : c b • b = 0 := by
      rcases hbm with h0 | hy2
      · rw [h0]; simp
      · exact absurd hy2 hbne
    exact hzero
  have hfz' : z = f y • y := by rw [hfz]; exact sumEq ffin f
  have hgz' : z = g y • y := by rw [hgz]; exact sumEq gfin g
  have hkey : f y • y = g y • y := by rw [← hfz', ← hgz']
  have hsub : (f y - g y) • y = (0 : V3) := by
    rw [sub_smul, ← hfz', ← hgz', sub_self]
  rcases smul_eq_zero.mp hsub with heq | hy0
  · exact absurd heq (by
      have h3 := hfpos y (by simp)
      have h4 := hgneg y (by simp)
      linarith)
  · exact absurd hy0 hy

/-! ## The `WRGCVDR_BIJ` kit (mirror of LocalAuto3's proved bij block,
`_p2` vocabulary; wave LA2-p2 2026-10). Hypermap-combinatorics core: same-fst
darts share the node orbit (`EE_p2` is a single azim cycle), the `dih2k_p2`
hypermap is `Simple`, and `fst` maps faces bijectively to `V`. The
single-cyclicity input is the importable `orbit_eq_setOfEdge`
(`Kepler.Text.TopologyFan`, new import this wave — depends only on `Fan`). -/

/-- Mirror of `LocalAuto3.EE_SUBSET_UNIONS_E` (WRGCVDR.hl:1264). -/
private theorem p2_EE_SUBSET_UNIONS_E {α : Type*} (v : α) (E : Set (Set α)) :
    EE_p2 v E ⊆ ⋃₀ E := fun w hw => Set.mem_sUnion.mpr ⟨{v, w}, hw, by simp⟩

/-- Mirror of `LocalAuto3.UNI_E_IMP_EE_EQ_SET_OF_EDGE` (WRGCVDR.hl:275). -/
private theorem p2_UNI_E_IMP_EE_EQ_SET_OF_EDGE {E : Set (Set V3)} {V : Set V3}
    (h : ⋃₀ E ⊆ V) (v : V3) : EE_p2 v E = setOfEdge v V E := by
  ext w
  constructor
  · intro hw
    have hwV : w ∈ ⋃₀ E := Set.mem_sUnion.mpr ⟨{v, w}, hw, by simp⟩
    exact ⟨hw, h hwV⟩
  · rintro ⟨hw, -⟩
    exact hw

/-- Mirror of `LocalAuto3.FAN_IMP_FINITE_EE` (WRGCVDR.hl:1276). -/
private theorem p2_FAN_IMP_FINITE_EE {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (v : V3) : (EE_p2 v E).Finite :=
  hfan.2.2.1.1.subset (Set.Subset.trans (p2_EE_SUBSET_UNIONS_E v E) hfan.1)

/-- Mirror of `LocalAuto3.IN_DARTS_HYP_IMP_FST_SND_IN_V` (WRGCVDR.hl:245;
HOL `PAIRS_IN_UNIONS` inlined). -/
private theorem p2_IN_DARTS_HYP_IMP_FST_SND_IN_V {E : Set (Set V3)} {V : Set V3}
    (hsub : ⋃₀ E ⊆ V) {y : V3 × V3} (hy : y ∈ dartsOfHyp_p2 E V) :
    y.1 ∈ V ∧ y.2 ∈ V := by
  rcases (Set.mem_union _ _ _).mp hy with h | h
  · exact ⟨hsub (show y.1 ∈ ⋃₀ E from ⟨{y.1, y.2}, h, Set.mem_insert y.1 {y.2}⟩),
      hsub (show y.2 ∈ ⋃₀ E from
        ⟨{y.1, y.2}, h, Set.mem_insert_of_mem y.1 (Set.mem_singleton y.2)⟩)⟩
  · exact ⟨h.2.1, by rw [← h.1]; exact h.2.1⟩

/-- Mirror of `LocalAuto3.IN_V_OF_FAN_EXISTS_DART` (WRGCVDR.hl:203). -/
private theorem p2_IN_V_OF_FAN_EXISTS_DART {E : Set (Set V3)} {V : Set V3}
    (hsub : ⋃₀ E ⊆ V) {u : V3} (hu : u ∈ V) : ∃ v ∈ V, (u, v) ∈ dartsOfHyp_p2 E V := by
  by_cases hex : ∃ w, {u, w} ∈ E
  · obtain ⟨w, hw⟩ := hex
    have hwV : w ∈ ⋃₀ E := Set.mem_sUnion.mpr ⟨{u, w}, hw, by simp⟩
    exact ⟨w, hsub hwV, Set.mem_union_left _ hw⟩
  · have hE : EE_p2 u E = ∅ := by
      rw [EE_p2]
      exact Set.eq_empty_iff_forall_notMem.mpr fun w hw => hex ⟨w, hw⟩
    exact ⟨u, hu, Set.mem_union_right _ ⟨rfl, hu, hE⟩⟩

/-- HOL `choose_nd_point` (WRGCVDR.hl:341, Skolemization; mirror of
`LocalAuto3.chooseNdPoint_p3`). -/
private noncomputable def chooseNdPoint_p2 (u : V3) (E : Set (Set V3)) (V : Set V3) : V3 :=
  if h : ⋃₀ E ⊆ V ∧ u ∈ V then Classical.choose (p2_IN_V_OF_FAN_EXISTS_DART h.1 h.2) else u

/-- HOL `choose_nd_point` specification (mirror of `LocalAuto3.choose_nd_point`). -/
private theorem p2_choose_nd_point (u : V3) (E : Set (Set V3)) (V : Set V3) (h1 : ⋃₀ E ⊆ V)
    (h2 : u ∈ V) :
    chooseNdPoint_p2 u E V ∈ V ∧ (u, chooseNdPoint_p2 u E V) ∈ dartsOfHyp_p2 E V := by
  have hexp : chooseNdPoint_p2 u E V = Classical.choose (p2_IN_V_OF_FAN_EXISTS_DART h1 h2) :=
    dif_pos ⟨h1, h2⟩
  rw [hexp]
  exact Classical.choose_spec (p2_IN_V_OF_FAN_EXISTS_DART h1 h2)

/-- Mirror of `LocalAuto3.HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW` (WRGCVDR.hl:357). -/
private theorem p2_HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW {α : Type*} {f : α → α} {k : ℕ}
    (hf : hasOrders_p2 f k) (hk : k ≠ 0) (x : α) :
    orbitF_p2 f x = {y | ∃ n < k, f^[n] x = y} := by
  have hid := hf.2
  have key : ∀ n : ℕ, f^[n] x = f^[n % k] x := by
    intro n
    have hnm : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    conv => lhs; rw [hnm]
    rw [Function.iterate_add, Function.iterate_mul, hid]
    simp
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n % k, Nat.mod_lt n (Nat.pos_of_ne_zero hk), (key n).symm⟩
  · rintro ⟨n, -, rfl⟩
    exact ⟨n, rfl⟩

/-- Mirror of `LocalAuto3.HAVING_ORDERS_K_IMP_CARD_ORBIT_LE_K` (WRGCVDR.hl:408). -/
private theorem p2_HAVING_ORDERS_K_IMP_CARD_ORBIT_LE_K {α : Type*} {f : α → α} {k : ℕ}
    (hf : hasOrders_p2 f k) (hk : k ≠ 0) (x : α) : (orbitF_p2 f x).ncard ≤ k := by
  have hEq : {y : α | ∃ n < k, f^[n] x = y} = (fun n => f^[n] x) '' (Finset.range k : Set ℕ) := by
    ext y
    simp [Finset.mem_range]
  rw [p2_HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW hf hk x, hEq]
  calc Set.ncard ((fun n => f^[n] x) '' (Finset.range k : Set ℕ))
      ≤ Set.ncard (Finset.range k : Set ℕ) := Set.ncard_image_le
    _ = k := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- Mirror of `LocalAuto3.CARD_UNION_NOT_DISTJ_LT` (WRGCVDR.hl:546). -/
private theorem p2_CARD_UNION_NOT_DISTJ_LT {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (h : s ∩ t ≠ ∅) : (s ∪ t).ncard < s.ncard + t.ncard :=
  Set.ncard_union_lt hs ht fun hd => h (by rwa [Set.disjoint_iff_inter_eq_empty] at hd)

/-- Mirror of `LocalAuto3.HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT` (WRGCVDR.hl:683). -/
private theorem p2_HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT {α : Type*} {f : α → α} {k : ℕ}
    (hf : hasOrders_p2 f k) (hk : k ≠ 0) {x y : α} (h : x ∈ orbitF_p2 f y) :
    orbitF_p2 f x = orbitF_p2 f y := by
  obtain ⟨n, rfl⟩ := h
  have key : ∀ m : ℕ, f^[m] y = f^[m % k] y := by
    intro m
    have hnm : m = k * (m / k) + m % k := (Nat.div_add_mod m k).symm
    conv => lhs; rw [hnm]
    rw [Function.iterate_add, Function.iterate_mul, hf.2]
    simp
  have main : ∀ q < k, orbitF_p2 f (f^[q] y) = orbitF_p2 f y := by
    intro q hq
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m + q, Function.iterate_add_apply f m q y⟩
    · rintro ⟨m, rfl⟩
      have hEq2 : k - q + q = k := by omega
      have hy : f^[k - q] (f^[q] y) = y := by
        rw [← Function.iterate_add_apply, hEq2, hf.2]
        simp
      exact ⟨m + (k - q), by rw [Function.iterate_add_apply, hy]⟩
  have hnx : orbitF_p2 f (f^[n] y) = orbitF_p2 f (f^[n % k] y) := by congr 1; exact key n
  rw [hnx, main (n % k) (Nat.mod_lt n (Nat.pos_of_ne_zero hk))]

/-- Mirror of `LocalAuto3.W_SUBSET_SINGLETON_IMP_IDE` (WRGCVDR.hl:1102). -/
private theorem p2_W_SUBSET_SINGLETON_IMP_IDE {W : Set V3} {p : V3} (h : W ⊆ {p}) (v w : V3) :
    azimCycle_p2 W v w p = p := by
  simp only [azimCycle_p2, if_pos h]

/-- Mirror of the proved `LocalAuto3.EXIS_SMALLEST_WITH_AZIM_ORD`
(WRGCVDR.hl:1009; lexicographic minimizer of (azim, ‖projection‖)). -/
private theorem p2_EXIS_SMALLEST_WITH_AZIM_ORD {W : Set V3} {v w p : V3}
    (h1 : ¬(W ⊆ {p})) (hfin : W.Finite) :
    ∃ u : V3, u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖ := by
  have hne : {u : V3 | u ∈ W ∧ u ≠ p}.Nonempty := by
    by_contra hc
    apply h1
    intro x hx
    by_contra hxp
    exact hc ⟨x, hx, hxp⟩
  have hf : {u : V3 | u ∈ W ∧ u ≠ p}.Finite := hfin.subset fun x hx => hx.1
  obtain ⟨q, hqin, hqmin⟩ := Set.exists_min_image
    {u : V3 | u ∈ W ∧ u ≠ p}
    (fun x => toLex (azim v w p x, ‖projection (x - v) (w - v)‖)) hf hne
  refine ⟨q, hqin.2, hqin.1, fun r hr hpr => ?_⟩
  have h := hqmin r ⟨hr, hpr⟩
  rw [Prod.Lex.toLex_le_toLex] at h
  exact h

/-- Mirror of `LocalAuto3.AZIM_CYCLE_PROPERTIES` (WRGCVDR.hl:1086). -/
private theorem p2_AZIM_CYCLE_PROPERTIES {W : Set V3} {p : V3} (hsub : ¬(W ⊆ {p}))
    (hfin : W.Finite) (v w : V3) :
    azimCycle_p2 W v w p ≠ p ∧ azimCycle_p2 W v w p ∈ W ∧
      ∀ q ∈ W, q ≠ p →
        azim v w p (azimCycle_p2 W v w p) < azim v w p q ∨
          azim v w p (azimCycle_p2 W v w p) = azim v w p q ∧
            ‖projection (azimCycle_p2 W v w p - v) (w - v)‖ ≤
              ‖projection (q - v) (w - v)‖ := by
  obtain ⟨u, hu1, hu2, hu3⟩ := p2_EXIS_SMALLEST_WITH_AZIM_ORD hsub hfin
  have hex : ∃ z : V3, z ≠ p ∧ z ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p z < azim v w p q ∨
        azim v w p z = azim v w p q ∧
          ‖projection (z - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖ :=
    ⟨u, hu1, hu2, hu3⟩
  rw [azimCycle_p2, if_neg hsub]
  exact Classical.epsilon_spec hex

/-- Mirror of the proved `LocalAuto3.AZIM_CYCLE_EQ_SIGMA_FAN`
(WRGCVDR.hl:1111): the chosen cyclic successor is the fan's `sigmaFan`. -/
private theorem p2_AZIM_CYCLE_EQ_SIGMA_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hu : u ∈ setOfEdge v V E) :
    azimCycle_p2 (EE_p2 v E) x v u = sigmaFan x V E v u := by
  have hEE : EE_p2 v E = setOfEdge v V E := p2_UNI_E_IMP_EE_EQ_SET_OF_EDGE hfan.1 v
  have hfinEE : (EE_p2 v E).Finite :=
    hfan.2.2.1.1.subset (Set.Subset.trans (p2_EE_SUBSET_UNIONS_E v E) hfan.1)
  by_cases hne : setOfEdge v V E = {u}
  · have hsub : EE_p2 v E ⊆ {u} := by rw [hEE]; exact hne.subset
    rw [p2_W_SUBSET_SINGLETON_IMP_IDE hsub x v, sigmaFan, if_pos hne]
  · have hneE : ¬(EE_p2 v E ⊆ {u}) := by
      intro hc
      refine hne (Set.eq_singleton_iff_unique_mem.mpr ⟨hu, fun w hw => ?_⟩)
      exact hc (by rw [← hEE] at hw; exact hw)
    obtain ⟨hz1, hz2, hz3⟩ :=
      p2_AZIM_CYCLE_PROPERTIES (W := EE_p2 v E) (p := u) hneE hfinEE x v
    obtain ⟨hs1, hs2, hs3⟩ := SIGMA_FAN hne hfan hu
    have hEu : {v, u} ∈ E := (properties_of_setOfEdge_fan x V E v u hfan).mpr hu
    have hEz : {v, azimCycle_p2 (EE_p2 v E) x v u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr (by rw [← hEE]; exact hz2)
    have hEs : {v, sigmaFan x V E v u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr hs1
    have hminz : azim x v u (azimCycle_p2 (EE_p2 v E) x v u)
        ≤ azim x v u (sigmaFan x V E v u) := by
      rcases hz3 (sigmaFan x V E v u) (by rw [hEE]; exact hs1) hs2 with h | h
      · exact le_of_lt h
      · exact le_of_eq h.1
    have hmins : azim x v u (sigmaFan x V E v u)
        ≤ azim x v u (azimCycle_p2 (EE_p2 v E) x v u) :=
      hs3 _ (by rw [← hEE]; exact hz2) hz1
    exact unique_azim_point_fan hfan hEu hEz hEs (le_antisymm hminz hmins)

/-- Mirror of `LocalAuto3.nnOfHyp_dart` (WRGCVDR.hl:1302). -/
private theorem p2_nnOfHyp_dart {x : V3} {V : Set V3} {E : Set (Set V3)} {u w : V3}
    (hw : (u, w) ∈ dartsOfHyp_p2 E V) :
    nnOfHyp_p2 x V E (u, w) = (u, azimCycle_p2 (EE_p2 u E) x u w) := by
  have hd : (u, w) ∈ dartsOfHyp_p2 E V := hw
  rw [show nnOfHyp_p2 x V E (u, w) =
    if (u, w) ∈ dartsOfHyp_p2 E V
    then ((u, w).1, azimCycle_p2 (EE_p2 (u, w).1 E) x (u, w).1 (u, w).2) else (u, w)
    from rfl, if_pos hd]

/-- Mirror of `LocalAuto3.FAN_darts_dichotomy`. -/
private theorem p2_FAN_darts_dichotomy {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {y : V3 × V3} (hy : y ∈ dartsOfHyp_p2 E V) :
    y ∈ dart1OfFan V E ∨ (y.1 = y.2 ∧ y.1 ∈ V ∧ EE_p2 y.1 E = ∅) := by
  rcases (Set.mem_union _ _ _).mp hy with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩

/-- Mirror of `LocalAuto3.nnOfHyp_isolated`. -/
private theorem p2_nnOfHyp_isolated {x : V3} {V : Set V3} {E : Set (Set V3)}
    {y : V3 × V3} (hy : y.1 = y.2 ∧ y.1 ∈ V ∧ EE_p2 y.1 E = ∅) :
    nnOfHyp_p2 x V E y = y := by
  have hd : y ∈ dartsOfHyp_p2 E V := Or.inr (show y ∈ selfPairs_p2 E V from hy)
  rw [show nnOfHyp_p2 x V E y =
    if y ∈ dartsOfHyp_p2 E V then (y.1, azimCycle_p2 (EE_p2 y.1 E) x y.1 y.2) else y from rfl,
    if_pos hd,
    p2_W_SUBSET_SINGLETON_IMP_IDE (W := EE_p2 y.1 E) (p := y.2) (v := x) (w := y.1)
      (fun w hw => by rw [hy.2.2] at hw; exact absurd hw (by simp))]

/-- Mirror of `LocalAuto3.nnOfHyp_eq_nFanPair`. -/
private theorem p2_nnOfHyp_eq_nFanPair {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {y : V3 × V3} (hy : y ∈ dart1OfFan V E) :
    nnOfHyp_p2 x V E y = nFanPair x V E y := by
  have hy2 : y.2 ∈ setOfEdge y.1 V E :=
    (properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp hy
  have hd : y ∈ dartsOfHyp_p2 E V := Or.inl (show y ∈ ordPairs_p2 E from hy)
  rw [show nnOfHyp_p2 x V E y =
    if y ∈ dartsOfHyp_p2 E V then (y.1, azimCycle_p2 (EE_p2 y.1 E) x y.1 y.2) else y
    from rfl,
    if_pos hd, p2_AZIM_CYCLE_EQ_SIGMA_FAN hfan hy2]
  rfl

/-- Mirror of `LocalAuto3.N_HYP_TO_AZIM_CYCLE_LEM` (WRGCVDR.hl:1995). -/
private theorem p2_N_HYP_TO_AZIM_CYCLE_LEM {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {u v : V3} (_huv : (u, v) ∈ dartsOfHyp_p2 E V) (n : ℕ) :
    (nnOfHyp_p2 x V E)^[n] (u, v) = (u, (azimCycle_p2 (EE_p2 u E) x u)^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih _huv]
    have hwD : (u, (azimCycle_p2 (EE_p2 u E) x u)^[k] v) ∈ dartsOfHyp_p2 E V := by
      rcases p2_FAN_darts_dichotomy _hfan _huv with h1 | h2
      · have hEE : EE_p2 u E = setOfEdge u V E :=
          p2_UNI_E_IMP_EE_EQ_SET_OF_EDGE _hfan.1 u
        have hvE : v ∈ EE_p2 u E := by
          rw [hEE]
          exact (properties_of_setOfEdge_fan x V E u v _hfan).mp h1
        have hstep : ∀ m : ℕ, ∀ z : V3, z ∈ EE_p2 u E →
            (azimCycle_p2 (EE_p2 u E) x u)^[m] z ∈ EE_p2 u E := by
          intro m
          induction m with
          | zero => intro z hz; exact hz
          | succ j jh =>
            intro z hz
            rw [Function.iterate_succ_apply']
            have hq : (azimCycle_p2 (EE_p2 u E) x u)^[j] z ∈ EE_p2 u E := jh z hz
            by_cases hsub : EE_p2 u E ⊆ {(azimCycle_p2 (EE_p2 u E) x u)^[j] z}
            · rw [p2_W_SUBSET_SINGLETON_IMP_IDE (W := EE_p2 u E)
                (p := (azimCycle_p2 (EE_p2 u E) x u)^[j] z) (v := x) (w := u) hsub]
              exact hq
            · exact (p2_AZIM_CYCLE_PROPERTIES (W := EE_p2 u E)
                (p := (azimCycle_p2 (EE_p2 u E) x u)^[j] z) hsub
                (p2_FAN_IMP_FINITE_EE _hfan u) x u).2.1
        have hwE : (azimCycle_p2 (EE_p2 u E) x u)^[k] v ∈ EE_p2 u E := hstep k v hvE
        have hE2 : {u, (azimCycle_p2 (EE_p2 u E) x u)^[k] v} ∈ E :=
          (properties_of_setOfEdge_fan x V E u _ _hfan).mpr
            (by rw [hEE] at hwE ⊢; exact hwE)
        exact Set.mem_union_left (b := selfPairs_p2 E V) hE2
      · have hE : EE_p2 u E = ∅ := h2.2.2
        have huv2 : u = v := h2.1
        rw [← huv2, hE]
        have hfix : ∀ m : ℕ, (azimCycle_p2 (∅ : Set V3) x u)^[m] u = u := by
          intro m
          induction m with
          | zero => rfl
          | succ j jh =>
            rw [Function.iterate_succ_apply',
              p2_W_SUBSET_SINGLETON_IMP_IDE (W := (∅ : Set V3))
                (p := (azimCycle_p2 (∅ : Set V3) x u)^[j] u) (v := x) (w := u)
                (by simp), jh]
        rw [hfix]
        exact Set.mem_union_right (a := ordPairs_p2 E)
          ⟨rfl, h2.2.1, h2.2.2⟩
    rw [p2_nnOfHyp_dart hwD]

/-- Mirror of `LocalAuto3.ITER_AZIM_CYCLE_EQ_ITER_SIGMA` (WRGCVDR.hl:2044). -/
private theorem p2_ITER_AZIM_CYCLE_EQ_ITER_SIGMA {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {v u : V3} (_hv : {v, u} ∈ E) (a : V3) (_ha : a ∈ EE_p2 v E)
    (n : ℕ) :
    (azimCycle_p2 (EE_p2 v E) x v)^[n] a = (sigmaFan x V E v)^[n] a := by
  have haE : a ∈ setOfEdge v V E := by
    rw [← p2_UNI_E_IMP_EE_EQ_SET_OF_EDGE _hfan.1 v]
    exact _ha
  have hmem : ∀ m : ℕ, (sigmaFan x V E v)^[m] a ∈ setOfEdge v V E := by
    intro m
    induction m with
    | zero => exact haE
    | succ j jh =>
      rw [Function.iterate_succ_apply']
      exact sigma_fan_in_setOfEdge _hfan jh
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact p2_AZIM_CYCLE_EQ_SIGMA_FAN _hfan (hmem k)

/-- Mirror of `LocalAuto3.CYCLIC_SET_IMP_STABLE_SET2` (WRGCVDR.hl:2080); the
single-cyclicity input is the importable `orbit_eq_setOfEdge`. -/
private theorem p2_CYCLIC_SET_IMP_STABLE_SET2 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {v u : V3} (_hv : {v, u} ∈ E) (a : V3) (_ha : a ∈ EE_p2 v E) :
    EE_p2 v E = {y | ∃ n : ℕ, y = (azimCycle_p2 (EE_p2 v E) x v)^[n] a} := by
  have hfan : FAN x V E := ‹FAN x V E›
  have hv : {v, u} ∈ E := ‹{v, u} ∈ E›
  have ha : a ∈ EE_p2 v E := ‹a ∈ EE_p2 v E›
  have hEE : EE_p2 v E = setOfEdge v V E := p2_UNI_E_IMP_EE_EQ_SET_OF_EDGE hfan.1 v
  have hae : {v, a} ∈ E :=
    (properties_of_setOfEdge_fan x V E v a hfan).mpr (by rw [← hEE]; exact ha)
  have hconv : ∀ n : ℕ, (azimCycle_p2 (EE_p2 v E) x v)^[n] a = (sigmaFan x V E v)^[n] a :=
    fun n => p2_ITER_AZIM_CYCLE_EQ_ITER_SIGMA hfan hv a ha n
  ext y
  constructor
  · intro hy
    have hyE : y ∈ setOfEdge v V E := hEE ▸ hy
    have hyn : y ∈ setOfOrbitsPointsFan x V E v a :=
      orbit_eq_setOfEdge hfan hae ▸ hyE
    simp only [setOfOrbitsPointsFan, Set.mem_setOf_eq] at hyn
    obtain ⟨n, hn⟩ := hyn
    exact ⟨n, hn.symm.trans (hconv n).symm⟩
  · rintro ⟨n, hn⟩
    have hyE : y ∈ setOfEdge v V E := by
      rw [← orbit_eq_setOfEdge hfan hae]
      simp only [setOfOrbitsPointsFan, Set.mem_setOf_eq]
      exact ⟨n, (hconv n).symm.trans hn.symm⟩
    rw [hEE]
    exact hyE

/-! ### Private aux kit for `WRGCVDR_BIJ` (mirror of LocalAuto3's `p3_*`
block; HOL source WRGCVDR.hl:589–744, 2519, 2548 with the
`hypermap (HYP …)` tuple absorbed by the proof-carrying `Hypermap`). -/

/-- Faces are orbits of the face map (mirror of `LocalAuto3.p3_faceEqOrbit`). -/
private theorem p2_faceEqOrbit {α : Type*} [DecidableEq α] (H : Hypermap α) (d : α) :
    H.face d = orbitF_p2 (H.faceMap : α → α) d := by
  rw [Hypermap.face, orbitMap]
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hnn⟩
    exact ⟨n, by rwa [Equiv.Perm.coe_pow] at hnn⟩
  · rintro ⟨n, hnn⟩
    exact ⟨n, by rw [Equiv.Perm.coe_pow]; exact hnn⟩

/-- Node orbits read through the `HYP` component `nn_of_hyp`
(mirror of `LocalAuto3.p3_nodeMem_iterate`). -/
private theorem p2_nodeMem_iterate {x : V3} {V : Set V3} {E : Set (Set V3)}
    {H : Hypermap (V3 × V3)}
    (hn : (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p2 x V E) (d w : V3 × V3) :
    w ∈ H.node d ↔ ∃ n : ℕ, (nnOfHyp_p2 x V E)^[n] d = w := by
  rw [Hypermap.node, orbitMap]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hnn⟩
    exact ⟨n, by rwa [Equiv.Perm.coe_pow, hn] at hnn⟩
  · rintro ⟨n, hnn⟩
    exact ⟨n, by rw [Equiv.Perm.coe_pow, hn]; exact hnn⟩

/-- `nn_of_hyp` preserves the first component, hence so do its iterates
(mirror of `LocalAuto3.p3_fst_iterate`). -/
private theorem p2_fst_iterate (x : V3) (V : Set V3) (E : Set (Set V3)) :
    ∀ (m : ℕ) (d : V3 × V3), ((nnOfHyp_p2 x V E)^[m] d).1 = d.1 := by
  have hFST : ∀ d : V3 × V3, (nnOfHyp_p2 x V E d).1 = d.1 := by
    intro d
    by_cases hdd : d ∈ dartsOfHyp_p2 E V
    · rw [show nnOfHyp_p2 x V E d =
        if d ∈ dartsOfHyp_p2 E V then (d.1, azimCycle_p2 (EE_p2 d.1 E) x d.1 d.2) else d
        from rfl, if_pos hdd]
    · rw [show nnOfHyp_p2 x V E d =
        if d ∈ dartsOfHyp_p2 E V then (d.1, azimCycle_p2 (EE_p2 d.1 E) x d.1 d.2) else d
        from rfl, if_neg hdd]
  intro m
  induction m with
  | zero => intro d; rfl
  | succ k ih =>
    intro d
    rw [Function.iterate_succ_apply', hFST]
    exact ih d

/-- HOL `DIH2K_IMP_PRE_SIMPLE_HYP` (WRGCVDR.hl:589; mirror of
`LocalAuto3.p3_preSimple`). -/
private theorem p2_preSimple {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (hd : dih2k_p2 H k) (hk : k ≠ 0) :
    ∀ z ∈ H.darts, (H.nodeMap : α → α) z ∉ H.face z := by
  intro z hz hmem
  have hxS : z ∈ H.face z := H.mem_face_self z
  have hsub : H.face z ⊆ (↑H.darts : Set α) := H.face_subset_darts hz
  have hfinS : (H.face z).Finite := (H.darts.finite_toSet).subset hsub
  have hfinImg : ((H.nodeMap : α → α) '' H.face z).Finite :=
    Set.Finite.image (H.nodeMap : α → α) hfinS
  have hSle : (H.face z).ncard ≤ k := by
    rw [p2_faceEqOrbit]
    exact p2_HAVING_ORDERS_K_IMP_CARD_ORBIT_LE_K (f := (H.faceMap : α → α)) hd.2.2.1 hk z
  have hmemI : (H.nodeMap : α → α) z ∈ H.face z ∩ ((H.nodeMap : α → α) '' H.face z) :=
    ⟨hmem, z, hxS, rfl⟩
  have hinter : (H.face z ∩ ((H.nodeMap : α → α) '' H.face z)) ≠ ∅ := by
    intro hc
    rw [hc] at hmemI
    simp at hmemI
  have hcard := p2_CARD_UNION_NOT_DISTJ_LT hfinS hfinImg hinter
  have himg : ((H.nodeMap : α → α) '' H.face z).ncard ≤ (H.face z).ncard :=
    Set.ncard_image_le (hs := hfinS)
  have hcover := hd.2.1 z hz
  have hstep1 : (↑H.darts : Set α).ncard <
      (H.face z).ncard + ((H.nodeMap : α → α) '' H.face z).ncard := by
    rw [hcover]; exact hcard
  have hstep2 : (H.face z).ncard + ((H.nodeMap : α → α) '' H.face z).ncard
      ≤ (H.face z).ncard + (H.face z).ncard := add_le_add (le_refl _) himg
  have h9 : (↑H.darts : Set α).ncard = 2 * k := by
    rw [Set.ncard_coe_finset, hd.1]
  omega

/-- HOL `DIH2K_IMP_SIMPLE_HYPERMAP` (WRGCVDR.hl:641; mirror of
`LocalAuto3.p3_simple`). -/
private theorem p2_simple {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (hd : dih2k_p2 H k) (hk : k ≠ 0) : H.Simple := by
  have hpre := p2_preSimple hd hk
  intro z hz
  have horders2 : hasOrders_p2 (H.nodeMap : α → α) 2 := hd.2.2.2.2
  have hnodeOrbit : H.node z = orbitF_p2 (H.nodeMap : α → α) z := by
    simp only [Hypermap.node, orbitMap, orbitF_p2, Equiv.Perm.coe_pow]
  have hnode : H.node z = {z, (H.nodeMap : α → α) z} := by
    rw [hnodeOrbit, p2_HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW horders2 two_ne_zero z]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hnlt, hn⟩
      have hn2 : n = 0 ∨ n = 1 := by omega
      rcases hn2 with rfl | rfl
      · subst hn; simp
      · subst hn; simp
    · rintro (hy | hy)
      · exact ⟨0, by norm_num, hy.symm⟩
      · refine ⟨1, by norm_num, ?_⟩
        rw [hy, Function.iterate_one]
  ext w
  constructor
  · rintro ⟨hn', hf'⟩
    rw [hnode] at hn'
    rcases Set.mem_insert_iff.mp hn' with hw | hw
    · exact hw
    · exact absurd (hw ▸ hf') (hpre z hz)
  · intro hw
    rw [hw]
    exact ⟨H.mem_node_self z, H.mem_face_self z⟩

/-- HOL `DIH_IMP_EVERY_NODE_INTER_FACE` (WRGCVDR.hl:717; mirror of
`LocalAuto3.p3_everyNode`). -/
private theorem p2_everyNode {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (hd : dih2k_p2 H k) {a b : α} (ha : a ∈ H.darts) (hb : b ∈ H.darts) :
    ∃ d, d ∈ H.node a ∧ d ∈ H.face b := by
  have horders2 : hasOrders_p2 (H.nodeMap : α → α) 2 := hd.2.2.2.2
  have hinv : ∀ z : α, (H.nodeMap : α → α) ((H.nodeMap : α → α) z) = z := by
    intro z
    have h2 : (H.nodeMap : α → α)^[2] z = z := by rw [horders2.2]; rfl
    simpa [Function.iterate_succ_apply', Function.iterate_one] using h2
  have hcover := hd.2.1 b hb
  have hamem : a ∈ ((H.face b : Set α) ∪ (H.nodeMap : α → α) '' H.face b) := hcover ▸ ha
  rcases Set.mem_or_mem_of_mem_union hamem with h1 | h2
  · exact ⟨a, H.mem_node_self a, h1⟩
  · obtain ⟨z, hzF, hza⟩ := h2
    refine ⟨z, ?_, hzF⟩
    rw [Hypermap.node, orbitMap]
    simp only [Set.mem_setOf_eq]
    refine ⟨1, ?_⟩
    rw [Equiv.Perm.coe_pow, Function.iterate_one]
    exact ((hinv z).symm.trans (congrArg (H.nodeMap : α → α) hza)).symm

/-- The combinatorial core of `WRGCVDR_BIJ`: two darts with the same first
component lie in the same node orbit (`EE_p2` is a single azim cycle:
`p2_CYCLIC_SET_IMP_STABLE_SET2` + `p2_N_HYP_TO_AZIM_CYCLE_LEM`; mirror of
`LocalAuto3.p3_same_fst_node`). -/
private theorem p2_same_fst_node {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d1 d2 : V3 × V3} (hd1 : d1 ∈ dartsOfHyp_p2 E V)
    (hd2 : d2 ∈ dartsOfHyp_p2 E V) (h12 : d1.1 = d2.1) :
    d2 ∈ orbitF_p2 (nnOfHyp_p2 x V E) d1 := by
  rcases Set.mem_or_mem_of_mem_union hd1 with ho1 | hs1
  · have hvE1 : d1.2 ∈ EE_p2 d1.1 E := ho1
    rcases Set.mem_or_mem_of_mem_union hd2 with ho2 | hs2
    · have hvE2 : d2.2 ∈ EE_p2 d1.1 E := by
        have h' : d2.2 ∈ EE_p2 d2.1 E := ho2
        rw [← h12] at h'
        exact h'
      have hE1 : {d1.1, d1.2} ∈ E := ho1
      obtain ⟨m, hm⟩ :=
        (p2_CYCLIC_SET_IMP_STABLE_SET2 (x := x) hfan (v := d1.1) (u := d1.2) hE1 d1.2 hvE1) ▸ hvE2
      exact ⟨m, by rw [p2_N_HYP_TO_AZIM_CYCLE_LEM hfan hd1 m]; exact Prod.ext h12 hm.symm⟩
    · exfalso
      have hz2 : EE_p2 d1.1 E = ∅ := by rw [h12]; exact hs2.2.2
      exact absurd hvE1 (by rw [hz2]; exact fun hc => hc)
  · rcases Set.mem_or_mem_of_mem_union hd2 with ho2 | hs2
    · exfalso
      have hz1 : EE_p2 d1.1 E = ∅ := hs1.2.2
      have hvE2 : d2.2 ∈ EE_p2 d1.1 E := by
        have h' : d2.2 ∈ EE_p2 d2.1 E := ho2
        rw [← h12] at h'
        exact h'
      exact absurd hvE2 (by rw [hz1]; exact fun hc => hc)
    · have he2 : d1.2 = d2.2 := hs1.1.symm.trans (h12.trans hs2.1)
      exact ⟨0, by rw [Function.iterate_zero_apply]; exact Prod.ext h12 he2⟩

/-! ## Remaining localization.hl theorems (giants; statements verbatim,
proofs deferred) -/

/-- HOL `AZIM_CYCLE_EQ_SIGMA_FAN_ALT` (localization.hl:234) — filled via the
kit's `p2_AZIM_CYCLE_EQ_SIGMA_FAN` and the proved `EE_elim`. -/
theorem AZIM_CYCLE_EQ_SIGMA_FAN_ALT (hfan : FAN 0 V E) {u v : V3}
    (hu : u ∈ setOfEdge v V E) :
    azimCycle_p2 (setOfEdge v V E) 0 v u = sigmaFan 0 V E v u := by
  rw [← EE_elim hfan v]
  exact p2_AZIM_CYCLE_EQ_SIGMA_FAN hfan hu

/-- HOL `nn_of_hyp_elim` (localization.hl:245). -/
theorem nn_of_hyp_elim (hfan : FAN 0 V E) :
    nnOfHyp_p2 0 V E = nFanPairExt 0 V E := sorry

/-- HOL `ivs_azim_cycle_elim` (localization.hl:281). -/
theorem ivs_azim_cycle_elim (hfan : FAN 0 V E) {p1 p2 : V3} (he : {p1, p2} ∈ E) :
    ivsAzimCycle_p2 (setOfEdge p1 V E) 0 p1 p2 = inverseSigmaFan 0 V E p1 p2 := sorry

/-- HOL `ff_of_hyp_elim` (localization.hl:295). -/
theorem ff_of_hyp_elim (hfan : FAN 0 V E) :
    ffOfHyp_p2 0 V E = fFanPairExt 0 V E := sorry

/-- HOL `HYP_elim` (localization.hl:320). -/
theorem HYP_elim (hfan : FAN 0 V E) :
    HYP_p2 0 V E =
      (dartOfFan V E, (eFanPairExt V E, (nFanPairExt 0 V E, fFanPairExt 0 V E))) := sorry

/-- HOL `hypermap_HYP_elim` (localization.hl:330): `hypermap (HYP (vec 0,V,E))`
equals `hypermap_of_fan (V,E)`. Rendered as: a fan hypermap exists with the
`dart_of_fan` dart set and the e/n/f pair-extension maps. -/
theorem hypermap_HYP_elim (hfan : FAN 0 V E) :
    ∃ HS : Hypermap (V3 × V3),
      (↑HS.darts : Set (V3 × V3)) = dartOfFan V E ∧
      (HS.edgeMap : V3 × V3 → V3 × V3) = eFanPairExt V E ∧
      (HS.nodeMap : V3 × V3 → V3 × V3) = nFanPairExt 0 V E ∧
      (HS.faceMap : V3 × V3 → V3 × V3) = fFanPairExt 0 V E := sorry

/-- HOL `local_fan2` (localization.hl:339): `local_fan` via `hypermap_of_fan`
and `face_set`; the let-bound hypermap is rendered via `IsHyp_p2`. -/
theorem local_fan2 (hV : V) (hE : E) (hFF : FF) :
    localFan_p2 V E FF ↔
      FAN 0 V E ∧ ∃ HS : Hypermap (V3 × V3), IsHyp_p2 0 V E HS ∧
        FF ∈ HS.faceSet ∧ dih2k_p2 HS FF.ncard := sorry

/-- HOL `WRGCVDR_BIJ` (localization.hl:356) — direct construction (mirror of
the proved `LocalAuto3.BIJ_BETWEEN_FF_AND_V`): MapsTo from `FF ⊆ darts`;
SurjOn from `p2_everyNode` + `p2_choose_nd_point`; InjOn because darts of one
face sharing `FST` share the node orbit (`p2_same_fst_node`), lie in the same
face orbit (`p2_HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT`), and the hypermap is
`Simple` (`p2_simple`). -/
theorem WRGCVDR_BIJ (h : localFan_p2 V E FF) : Set.BijOn Prod.fst FF V := by
  show Set.BijOn (fun d : V3 × V3 => d.1) FF V
  obtain ⟨H, hd, -, hn, -, hfan, ⟨z, hzd, hFF⟩, hdih⟩ := h
  have hzF : z ∈ FF := by rw [hFF]; exact H.mem_face_self z
  have hdartOf : ∀ d ∈ FF, d ∈ dartsOfHyp_p2 E V := by
    intro d hdF
    have hsub := H.face_subset_darts hzd (hFF ▸ hdF)
    rw [hd] at hsub
    exact hsub
  have hfinFF : FF.Finite :=
    (H.darts.finite_toSet).subset fun d hdF => hd ▸ hdartOf d hdF
  have hk : FF.ncard ≠ 0 := by
    intro h0
    have hFE : FF = ∅ := (Set.ncard_eq_zero hfinFF).mp h0
    rw [hFE] at hzF
    simp at hzF
  have hfaceOrbit : ∀ d ∈ FF, H.face d = FF := by
    intro d hdF
    have hbr : FF = orbitF_p2 (H.faceMap : V3 × V3 → V3 × V3) z := by
      rw [hFF, p2_faceEqOrbit]
    rw [hbr]
    exact p2_HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT
      (f := (H.faceMap : V3 × V3 → V3 × V3)) hdih.2.2.1 hk
      ((p2_faceEqOrbit H z) ▸ (hFF ▸ hdF))
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    intro d hdF
    exact (p2_IN_DARTS_HYP_IMP_FST_SND_IN_V hfan.1 (hdartOf d hdF)).1
  · -- InjOn
    intro d1 hd1 d2 hd2 h12
    have hsame : d2 ∈ orbitF_p2 (nnOfHyp_p2 0 V E) d1 :=
      p2_same_fst_node hfan (hdartOf d1 hd1) (hdartOf d2 hd2) h12
    have hnode2 : d2 ∈ H.node d1 := by
      rw [p2_nodeMem_iterate hn d1 d2]
      exact hsame
    have hsimple : H.node d1 ∩ H.face d1 = {d1} :=
      p2_simple hdih hk d1 (H.face_subset_darts hzd (hFF ▸ hd1))
    have hboth : d2 ∈ H.node d1 ∩ H.face d1 :=
      ⟨hnode2, by rw [hfaceOrbit d1 hd1]; exact hd2⟩
    rw [hsimple] at hboth
    exact hboth.symm
  · -- SurjOn
    intro v hv
    have hcp := p2_choose_nd_point v E V hfan.1 hv
    have hdart : ((v, chooseNdPoint_p2 v E V) : V3 × V3) ∈ (↑H.darts : Set (V3 × V3)) := by
      rw [hd]; exact hcp.2
    obtain ⟨d, hdN, hdF⟩ := p2_everyNode hdih hdart hzd
    refine ⟨d, ?_, ?_⟩
    · rw [hFF]; exact hdF
    rw [p2_nodeMem_iterate hn (v, chooseNdPoint_p2 v E V) d] at hdN
    obtain ⟨n, hnn⟩ := hdN
    rw [← hnn]
    exact p2_fst_iterate 0 V E n (v, chooseNdPoint_p2 v E V)

/-- HOL `WRGCVDR_ORBIT` (localization.hl:365) — the orbit half of HOL
`WRGCVDR` (WRGCVDR.hl:2622): `rho_node1` generates `V` off any vertex.
Proof (mirror of the HOL second conjunct): every dart of `FF` sees the same
face orbit (`orbitMap_eq_of_mem` = HOL `lemma_face_identity`), the face map
preserves `FF`, so `ff_of_hyp` on darts plus the `FST`-determinacy of darts
(`LOCAL_FAN_RHO_NODE_PROS` argument, re-derived here from `WRGCVDR_BIJ`)
give the `face_map ↔ hro POWER n` correspondence
`(faceMap^[n] (v, rho v)) = (rho^[n] v, rho^[n+1] v)`; both inclusions of
`orbitF_p2 (rhoNode1_p2 FF) v = V` then read off darts. -/
theorem WRGCVDR_ORBIT (h : localFan_p2 V E FF) :
    ∀ v ∈ V, orbitF_p2 (rhoNode1_p2 FF) v = V := by
  intro v hv
  obtain ⟨hmap, hinj, hsurj⟩ := WRGCVDR_BIJ h
  obtain ⟨H, hd, -, -, hface, hfan, ⟨z, hzd, hFF⟩, -⟩ := h
  have hdartOf : ∀ d ∈ FF, d ∈ dartsOfHyp_p2 E V := by
    intro d hdF
    have hsub := H.face_subset_darts hzd (hFF ▸ hdF)
    rw [hd] at hsub
    exact hsub
  have hleft : ∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF := by
    intro x hx
    obtain ⟨d, hdF, hfd⟩ := hsurj hx
    have hdeq : (x, d.2) = d := Prod.ext hfd.symm rfl
    have hmemFF : (x, d.2) ∈ FF := by
      rw [hdeq]
      exact hdF
    exact Classical.epsilon_spec (p := fun w => (x, w) ∈ FF) ⟨d.2, hmemFF⟩
  have hdet : ∀ d ∈ FF, d = (d.1, rhoNode1_p2 FF d.1) := by
    intro d hdF
    have hsucc : (d.1, rhoNode1_p2 FF d.1) ∈ FF := hleft d.1 (hmap hdF)
    exact (hinj hsucc hdF rfl).symm
  have hvFF : (v, rhoNode1_p2 FF v) ∈ FF := hleft v hv
  have hmemF : (v, rhoNode1_p2 FF v) ∈ H.face z := hFF ▸ hvFF
  have hfaceV : FF = H.face (v, rhoNode1_p2 FF v) :=
    hFF.trans (orbitMap_eq_of_mem H.faceMap_permutes hmemF).symm
  have hFF2 : ∀ d ∈ FF, (H.faceMap : V3 × V3 → V3 × V3) d ∈ FF := by
    intro d hdF
    have h1 : (H.faceMap : V3 × V3 → V3 × V3) d ∈ H.face d := by
      have hpow := pow_apply_mem_orbitMap H.faceMap 1 d
      rw [pow_one] at hpow
      exact hpow
    have hd' : d ∈ H.face (v, rhoNode1_p2 FF v) := by rw [← hfaceV]; exact hdF
    have h2 : H.face d = H.face (v, rhoNode1_p2 FF v) :=
      orbitMap_eq_of_mem H.faceMap_permutes hd'
    rwa [h2, ← hfaceV] at h1
  have hstep : ∀ a b : V3, (a, b) ∈ FF →
      (H.faceMap : V3 × V3 → V3 × V3) (a, b) = (b, rhoNode1_p2 FF b) := by
    intro a b hab
    have hres : (H.faceMap : V3 × V3 → V3 × V3) (a, b) ∈ FF := hFF2 (a, b) hab
    have hproj : ((H.faceMap : V3 × V3 → V3 × V3) (a, b)).1 = b := by
      have hco : (H.faceMap : V3 × V3 → V3 × V3) (a, b) = ffOfHyp_p2 0 V E (a, b) := by
        rw [hface]
      rw [hco, show ffOfHyp_p2 0 V E (a, b) =
        if (a, b) ∈ dartsOfHyp_p2 E V then
          ((a, b).2, ivsAzimCycle_p2 (EE_p2 (a, b).2 E) 0 (a, b).2 (a, b).1)
        else (a, b)
        from rfl, if_pos (hdartOf (a, b) hab)]
    have hpair : (H.faceMap : V3 × V3 → V3 × V3) (a, b)
        = (((H.faceMap : V3 × V3 → V3 × V3) (a, b)).1,
          rhoNode1_p2 FF ((H.faceMap : V3 × V3 → V3 × V3) (a, b)).1) :=
      hdet _ hres
    refine hpair.trans ?_
    rw [hproj]
  have hmemIter : ∀ n : ℕ,
      (H.faceMap : V3 × V3 → V3 × V3)^[n] (v, rhoNode1_p2 FF v) ∈ FF := by
    intro n
    have hit : (H.faceMap : V3 × V3 → V3 × V3)^[n] (v, rhoNode1_p2 FF v)
        ∈ H.face (v, rhoNode1_p2 FF v) := by
      rw [p2_faceEqOrbit H (v, rhoNode1_p2 FF v)]
      exact ⟨n, rfl⟩
    rw [← hfaceV] at hit
    exact hit
  have hkey : ∀ n : ℕ, (H.faceMap : V3 × V3 → V3 × V3)^[n] (v, rhoNode1_p2 FF v)
      = ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v) := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      have hmem : ((rhoNode1_p2 FF)^[k] v, (rhoNode1_p2 FF)^[k + 1] v) ∈ FF := by
        rw [← ih]
        exact hmemIter k
      have hp : (rhoNode1_p2 FF)^[k + 1 + 1] v
          = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[k + 1] v) :=
        Function.iterate_succ_apply' _ _ _
      rw [Function.iterate_succ_apply', ih,
        hstep ((rhoNode1_p2 FF)^[k] v) ((rhoNode1_p2 FF)^[k + 1] v) hmem, hp]
  rw [orbitF_p2]
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    have hdart : ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v) ∈ FF := by
      rw [← hkey n]
      exact hmemIter n
    have hV := p2_IN_DARTS_HYP_IMP_FST_SND_IN_V hfan.1 (hdartOf _ hdart)
    rw [← hn]
    exact hV.1
  · intro hw
    obtain ⟨d, hdF, hfd⟩ := hsurj hw
    have hd' : d ∈ H.face (v, rhoNode1_p2 FF v) := by rw [← hfaceV]; exact hdF
    rw [p2_faceEqOrbit H (v, rhoNode1_p2 FF v)] at hd'
    obtain ⟨m, hm⟩ := hd'
    rw [hkey m] at hm
    have hd1 : d.1 = (rhoNode1_p2 FF)^[m] v := by rw [← hm]
    refine ⟨m, ?_⟩
    rw [← hd1]
    exact hfd

/-- HOL `ALL_TO_THE_NONPARALLEL_PART_ALT` (localization.hl:374); HOL `graph`
↦ `Kepler.Text.Fan.Graph`. -/
theorem ALL_TO_THE_NONPARALLEL_PART_ALT {phii : V3 → ℝ → V3} {a b : ℝ}
    (hdef : deformation_p2 phii V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
      let Im : Set V3 → Set V3 := fun s => (fun v : V3 => phii v t) '' s
      (⋃₀ (Im '' E)) ⊆ (fun v : V3 => phii v t) '' V ∧
        Graph (Im '' E) ∧
        fan1 0 ((fun v : V3 => phii v t) '' V) (Im '' E) ∧
        fan2 0 ((fun v : V3 => phii v t) '' V) (Im '' E) ∧
        fan6 0 ((fun v : V3 => phii v t) '' V) (Im '' E) := sorry

/-- HOL `COMPATIBLE_BW_TWO_LEMMAS2_ALT` (localization.hl:401); the
`HS = hypermap (HYP (vec 0, V, E UNION {{v,w}}))` hypothesis ↦ `IsHyp_p2`. -/
theorem COMPATIBLE_BW_TWO_LEMMAS2_ALT (hV : V) (hE : E) (hFF : FF)
    (HS : Hypermap (V3 × V3)) (fv fw : Set (V3 × V3)) (v w : V3)
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    (vPrime_p2 V fv = slicev_p2 E FF v w ∧
        ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w ∧
        fv = slicef_p2 E FF v w) ∧
      vPrime_p2 V fw = slicev_p2 E FF w v ∧
      ePrime_p2 (E ∪ {{w, v}}) fw = slicee_p2 E FF w v ∧
      fw = slicef_p2 E FF w v := sorry

/-- HOL `EJRCFJD_ALT` (localization.hl:422). -/
theorem EJRCFJD_ALT (hV : V) (hE : E) (hFF : FF) (HS : Hypermap (V3 × V3))
    (fv fw : Set (V3 × V3)) (v w : V3)
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw ∧
      ∀ ff : ℕ → ℝ,
        setSum {i | i < V.ncard}
            (fun i => ff i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv}
              (fun i => ff i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) +
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw}
              (fun i => ff i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v)) := sorry

/-- HOL `ejr_distinct` (localization.hl:462). -/
theorem ejr_distinct (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V)
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) : w ≠ v := sorry

/-- HOL `WEDGE_EDGE_NOT_ADJ` (localization.hl:505). -/
theorem WEDGE_EDGE_NOT_ADJ (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ¬(affGt ({0} : Set V3) {v, rhoNode1_p2 FF v} ⊆
        wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E) := sorry

/-- HOL `PERIODIC_RHO_NODE1` (localization.hl:528). -/
theorem PERIODIC_RHO_NODE1 (h : localFan_p2 V E FF) (hv : v ∈ V) :
    periodic (fun i => (rhoNode1_p2 FF)^[i] v) V.ncard := sorry

/-- HOL `SLICEV_IMAGE` (localization.hl:549). -/
theorem SLICEV_IMAGE (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    (hi : i < V.ncard) (hwv : w = (rhoNode1_p2 FF)^[i] v) :
    slicev_p2 E FF v w = (fun j => (rhoNode1_p2 FF)^[j] v) '' {j | j < i + 1} := sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT` (localization.hl:618). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i : ℕ, i < V.ncard ∧ w = (rhoNode1_p2 FF)^[i] v := sorry

/-- HOL `SLICEW_IMAGE` (localization.hl:642). -/
theorem SLICEW_IMAGE (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    (hn : n < V.ncard) (hwv : w = (rhoNode1_p2 FF)^[n] v) :
    slicev_p2 E FF w v =
      (fun j => (rhoNode1_p2 FF)^[j] v) '' {j | j = 0 ∨ n ≤ j ∧ j < V.ncard} := sorry

/-- HOL `CARD_SLICEV_LT` (localization.hl:707). -/
theorem CARD_SLICEV_LT (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    (slicev_p2 E FF v w).ncard < V.ncard := sorry

/-- HOL `SLICEW_BIJ` (localization.hl:801). -/
theorem SLICEW_BIJ (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    (hn : n < V.ncard) (hwv : w = (rhoNode1_p2 FF)^[n] v) :
    Set.BijOn (fun j => (rhoNode1_p2 FF)^[j] v)
      {j | j = 0 ∨ n ≤ j ∧ j < V.ncard} (slicev_p2 E FF w v) := sorry

/-- HOL `SLICEV_BIJ` (localization.hl:844). -/
theorem SLICEV_BIJ (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    (hn : n < V.ncard) (hwv : w = (rhoNode1_p2 FF)^[n] v) :
    Set.BijOn (fun j => (rhoNode1_p2 FF)^[j] v) {j | j < n + 1} (slicev_p2 E FF v w) := sorry

/-- HOL `CARD_SLICEV` (localization.hl:887). -/
theorem CARD_SLICEV (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    (slicev_p2 E FF v w).ncard + (slicev_p2 E FF w v).ncard = V.ncard + 2 := sorry

/-- HOL `HAFL_CIRCLE_FORM_LOCAL_FAN_ALT` (localization.hl:964). -/
theorem HAFL_CIRCLE_FORM_LOCAL_FAN_ALT (hV : V) (hE : E) (hFF : FF)
    (HS : Hypermap (V3 × V3)) (fv : Set (V3 × V3)) (v w : V3)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
        ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv := sorry

/-- HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2_ALT` (localization.hl:984). -/
theorem HAFL_CIRCLE_FORM_LOCAL_FAN2_ALT (hV : V) (hE : E) (hFF : FF)
    (HS : Hypermap (V3 × V3)) (fv fw : Set (V3 × V3)) (v w : V3)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
        ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      localFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw := sorry

/-- HOL `CARD_SLICEF` (localization.hl:1006). -/
theorem CARD_SLICEF (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    (slicef_p2 E FF v w).ncard + (slicef_p2 E FF w v).ncard = FF.ncard + 2 := sorry

/-- HOL `ejr_generic` (localization.hl:1074). -/
theorem ejr_generic (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    (hg : generic_p2 V E) :
    generic_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) := sorry

/-- HOL `LOFA_IMP_LT_CARD_SET_V_ALT` (localization.hl:1171). -/
theorem LOFA_IMP_LT_CARD_SET_V_ALT (h : localFan_p2 V E FF) (hv : v ∈ V) :
    (fun n => (rhoNode1_p2 FF)^[n] v) '' {n | n < V.ncard} = V := sorry

/-- HOL `ejr_sum` (localization.hl:1180). -/
theorem ejr_sum (hV : V) (hE : E) (hFF : FF) (HS : Hypermap (V3 × V3)) (v w : V3)
    (f : V3 → ℝ) (fv fw : Set (V3 × V3))
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w))
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    setSum FF (fun e => f e.1 * azimInFan_p2 e E) =
      setSum fv (fun e => f e.1 * azimInFan_p2 e (ePrime_p2 (E ∪ {{v, w}}) fv)) +
      setSum fw (fun e => f e.1 * azimInFan_p2 e (ePrime_p2 (E ∪ {{w, v}}) fw)) := sorry

/-- HOL `EJRCFJD_ALT2` (localization.hl:1367). -/
theorem EJRCFJD_ALT2 (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    convexLocalFan_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) ∧
      convexLocalFan_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      tauFun_p2 V E FF ≥
        tauFun_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
          tauFun_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      solLocal_p2 E FF =
        solLocal_p2 (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
          solLocal_p2 (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      (slicev_p2 E FF v w).ncard < V.ncard ∧ (slicev_p2 E FF w v).ncard < V.ncard ∧
      (generic_p2 V E → generic_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) ∧
        generic_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v)) := sorry

/-- HOL `NKEZBFC` (localization.hl:1502). -/
theorem NKEZBFC (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E) :
    0 ≤ solLocal_p2 E FF := sorry

/-- HOL `azim_dart_azim_in_fan` (localization.hl:1515). -/
theorem azim_dart_azim_in_fan (hfan : FAN 0 V E) {x : V3 × V3}
    (he : {x.1, x.2} ∈ E) : azimDart V E x = azimInFan_p2 x E := sorry

/-- HOL `rho_rho_fun` (localization.hl:1543). NEEDS: merge with
`LocalAnchors.rho_rho_fun` (same name there). -/
theorem rho_rho_fun_p2 (y : ℝ) : rhoFun_p2 y = rho_p2 y := sorry

/-- HOL `tauVEF_tau_fun` (localization.hl:1568). -/
theorem tauVEF_tau_fun (hfan : FAN 0 V E) {f : Set (V3 × V3)} (hcard : 2 ≤ f.ncard)
    (hn : ∀ x ∈ f, ‖x.1‖ ≤ 2 * h0) (he : ∀ x ∈ f, {x.1, x.2} ∈ E) :
    tauFun_p2 V E f = tauVEF_p2 V E f := sorry

/-! ## LDURDPN.hl and LFJCIXP.hl -/

/-- HOL `AFF_CONV0_IN_AFF_LT` (LDURDPN.hl:44). -/
theorem AFF_CONV0_IN_AFF_LT {u v w : V3} (hcol : ¬ Collinear ℝ ({0, u, v} : Set V3))
    (hint : ((affineSpan ℝ ({0, u} : Set V3) ∩ conv0_p2 {v, w} : Set V3)) ≠ ∅) :
    w ∈ affLt ({0, u} : Set V3) ({v} : Set V3) := by
  classical
  have hfin3 : (({0, u, v} : Set V3) : Set V3).Finite := by simp
  have hne' : ¬ ∀ z : V3, z ∉ (affineSpan ℝ ({0, u} : Set V3) ∩ conv0_p2 {v, w} : Set V3) := by
    intro h
    refine hint ?_
    ext x
    exact ⟨fun hmem => h x hmem, fun hf => by simp at hf⟩
  push_neg at hne'
  obtain ⟨z, hz1, hz2⟩ := hne'
  have hsub : z ∈ affineSpan ℝ ({0, u} : Set V3) := hz1
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hsub
  have hr' : r • u = z := by simpa [AffineMap.lineMap_apply] using hr
  have hz2' : Affsign (fun x : ℝ => 0 < x) ∅ ({v, w} : Set V3) z := hz2
  unfold Affsign at hz2'
  obtain ⟨ff, ffin, hfz, hfpos, _hfsum⟩ := hz2'
  -- 0, u, v are pairwise distinct (else collinear)
  have hu0 : u ≠ 0 := fun he => hcol (by rw [he]; simpa [Collinear3] using collinear_pair ℝ (0:V3) v)
  have hv0 : v ≠ 0 := fun he => hcol (by rw [he]; simpa [Collinear3] using collinear_pair ℝ u 0)
  have huv : u ≠ v := fun he => hcol (by rw [he]; simpa [Collinear3] using collinear_pair ℝ (0:V3) v)
  -- sum over a two-point set splits
  rcases eq_or_ne v w with hvw | hvw
  · -- v = w: z = v, so v lies on the line through 0 and u: contradiction
    exfalso
    have h1 : ffin.toFinset = ({v} : Finset V3) := by
      ext x; simpa [hvw, Set.mem_singleton_iff] using ·
    rw [h1, Finset.sum_singleton] at hfz _hfsum
    have hzv : z = v := by rw [hfz, show ff v = 1 from _hfsum, one_smul]
    have hvin : v ∈ affineSpan ℝ ({0, u} : Set V3) := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨r, ?_⟩
      have hlm : AffineMap.lineMap (0:V3) u r = r • u := by
        rw [AffineMap.lineMap_apply]; simp
      rw [hlm, hr', hzv]
    exact hcol (by
      have hc := collinear_insert_of_mem_affineSpan_pair (p₁ := v) (p₂ := 0) (p₃ := u) hvin
      have hset : ({0, u, v} : Set V3) = {v, 0, u} := by ext x; simp; tauto
      rw [hset]; exact hc)
  · -- v ≠ w: the cone point writes w as a negative-coefficient combination
    have hapos : 0 < ff v := hfpos v (by simp)
    have hbpos0 : 0 < ff w := hfpos w (by simp)
    have hb : ff w ≠ 0 := ne_of_gt hbpos0
    have h1 : ffin.toFinset = ({v, w} : Finset V3) := by
      ext x; simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ·
    rw [h1, Finset.sum_insert (by simp [hvw] : v ∉ ({w} : Finset V3)),
      Finset.sum_singleton] at hfz
    have hbw : ff w • w = r • u - ff v • v := by rw [hr', hfz, add_sub_cancel_left]
    have hbinv : ff w ≠ 0 := hb
    have hwv' : w = ((ff w)⁻¹ * r) • u + (-((ff w)⁻¹ * ff v)) • v := by
      have h2 : (ff w)⁻¹ • (ff w • w) = (ff w)⁻¹ • (r • u - ff v • v) := by rw [hbw]
      rw [smul_smul, inv_mul_cancel₀ hb, one_smul, smul_sub, smul_smul, smul_smul] at h2
      exact h2.trans (by rw [sub_eq_add_neg, neg_smul])
    set g : V3 → ℝ :=
      fun x => if x = 0 then 1 - (ff w)⁻¹ * r + (ff w)⁻¹ * ff v
        else if x = u then (ff w)⁻¹ * r else -((ff w)⁻¹ * ff v) with hgdef
    have hsum3 : ∀ c : V3 → ℝ,
        ∑ x ∈ ({0, u, v} : Finset V3), c x = c 0 + (c u + c v) := by
      intro c
      rw [Finset.sum_insert (by simp [hu0.symm, hv0.symm] : (0:V3) ∉ ({u, v} : Finset V3)),
        Finset.sum_insert (by simp [huv] : (u:V3) ∉ ({v} : Finset V3)), Finset.sum_singleton]
    have hsum3v : ∀ c : V3 → ℝ,
        ∑ x ∈ ({0, u, v} : Finset V3), c x • x = c 0 • 0 + (c u • u + c v • v) := by
      intro c
      rw [Finset.sum_insert (by simp [hu0.symm, hv0.symm] : (0:V3) ∉ ({u, v} : Finset V3)),
        Finset.sum_insert (by simp [huv] : (u:V3) ∉ ({v} : Finset V3)), Finset.sum_singleton]
    have hg0 : g 0 = 1 - (ff w)⁻¹ * r + (ff w)⁻¹ * ff v := by simp [hgdef]
    have hgu : g u = (ff w)⁻¹ * r := by simp [hgdef, hu0]
    have hgv : g v = -((ff w)⁻¹ * ff v) := by simp [hgdef, huv.symm, hv0]
    have hfin' : (({0, u} ∪ {v} : Set V3)).Finite := by simp
    have hconv : hfin'.toFinset = ({0, u, v} : Finset V3) := by
      ext x
      simp only [hfin'.mem_toFinset, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    have hbipos : 0 < (ff w)⁻¹ := inv_pos.mpr hbpos0
    refine ⟨g, hfin', ?_, ?_, ?_⟩
    · rw [hconv, hsum3v g, hg0, hgu, hgv]
      simp only [smul_zero, zero_add]
      exact hwv'
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      rw [hgv]
      linarith [mul_pos hbipos hapos]
    · rw [hconv, hsum3 g, hg0, hgu, hgv]
      ring

/-- HOL `LDURDPN` (LDURDPN.hl:69): `azim = pi` iff coplanar and the open
cone meets the affine hull. -/
theorem LDURDPN {u v w : V3} (huv : ¬ Collinear ℝ ({0, u, v} : Set V3))
    (huw : ¬ Collinear ℝ ({0, u, w} : Set V3)) :
    (azim 0 u v w = Real.pi ↔
      (∃ A : Set V3, plane_p2 A ∧ ({0, u, v, w} : Set V3) ⊆ A) ∧
        ¬((affineSpan ℝ ({0, u} : Set V3) ∩ conv0_p2 {v, w} : Set V3) = ∅)) := sorry

/-- HOL `LFJCIXP` (LFJCIXP.hl:25): the delta bound and the resulting
ball-annulus diameter bound; `delta` ↦ `deltaX`, `packing` ↦ `Kepler.Packing`. -/
theorem LFJCIXP :
    (∀ y1 y2 y3 y4 y5 y6 : ℝ,
        2 ≤ y1 ∧ y1 ≤ 2.52 ∧ 2 ≤ y2 ∧ y2 ≤ 2.52 ∧ 2 ≤ y3 ∧ y3 ≤ 2.52 ∧
            2 ≤ y4 ∧ y4 ≤ 4.52 ∧ y5 = 2 ∧ y6 = 2 →
          y4 ≤ 3.915 ∨ deltaX (y1 ^ 2) (y2 ^ 2) (y3 ^ 2) (y4 ^ 2) (y5 ^ 2) (y6 ^ 2) < 0) ∧
      ∀ {v u w : V3}, {v, u, w} ⊆ ballAnnulus → Packing ({v, u, w} : Set V3) →
        u ≠ w → ‖v - u‖ = 2 → ‖v - w‖ = 2 → ‖u - w‖ ≤ 4.52 → ‖u - w‖ ≤ 3.915 := sorry

end Kepler.Text

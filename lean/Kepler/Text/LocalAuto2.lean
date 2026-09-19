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
-/

import Kepler.Text.Polytope
import Kepler.Text.Fan
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

/-! ## Remaining localization.hl theorems (giants; statements verbatim,
proofs deferred) -/

/-- HOL `AZIM_CYCLE_EQ_SIGMA_FAN_ALT` (localization.hl:234). NEEDS the
azim-cycle/sigma-fan compatibility theorem of the Wrgcvdr block. -/
theorem AZIM_CYCLE_EQ_SIGMA_FAN_ALT (hfan : FAN 0 V E) {u v : V3}
    (hu : u ∈ setOfEdge v V E) :
    azimCycle_p2 (setOfEdge v V E) 0 v u = sigmaFan 0 V E v u := sorry

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

/-- HOL `WRGCVDR_BIJ` (localization.hl:356). -/
theorem WRGCVDR_BIJ (h : localFan_p2 V E FF) : Set.BijOn Prod.fst FF V := sorry

/-- HOL `WRGCVDR_ORBIT` (localization.hl:365). -/
theorem WRGCVDR_ORBIT (h : localFan_p2 V E FF) :
    ∀ v ∈ V, orbitF_p2 (rhoNode1_p2 FF) v = V := sorry

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

/-
Kepler.Text.LocalAuto3 — port of Flyspeck `local/WRGCVDR.hl` (module
`Wrgcvdr_cizmrrh`, Truong Nguyen Quang, 2010-03-30; 3331 lines, 23
`new_definition` + 1 `new_specification` + 97 theorems): the local-fan
hypermap layer — `darts_of_hyp`/`ee/nn/ff_of_hyp` dart maps, the
`azim_cycle`/`ivs_azim_cycle` cyclic-order kit, `dih2k` hypermaps,
`local_fan`, and the MFMPCVM/PJRIMCV/localization entry defs
(`v_prime`, `e_prime`, `generic`, `circular`, `lunar`).

Encoding notes (per Kepler/Text/Polytope.lean conventions):
- HOL `real^3` ↔ `V3`; `vec 0` ↔ `(0 : V3)`; `ITER n f` ↔ `f^[n]`
  (`Nat.iterate`); HOL `POWER n f` collapses to `Nat.iterate` too, so
  `POWER_TO_ITER` is a definitional no-op (documented at the statement).
- HOL `hypermap` type ↔ `structure Hypermap` (Kepler.Text.Hypermap, imported
  transitively via Kepler.Text.Fan). The HOL tuple constructor
  `hypermap (D,e,n,f)` + `tuple_hypermap`/`hypermap_tybij` round-trip is
  ABSORBED by the structure: the permutation side-conditions are fields.
  Consequently `HYP_LEMMA`/`ELMS_OF_HYPERMAP_HYP`/`local_fan` are rendered
  with an existential `H : Hypermap (V3 × V3)` whose components equal the
  components of `HYP_p3 x V E` — the faithful reading of
  `let H = hypermap (HYP (vec 0,V,E)) in …`.
- HOL `e permutes D` on `Equiv.Perm` maps ↔ `PermutesOn` (repo); on plain
  functions `g : V3×V3 → V3×V3` it is rendered by the local 3-conjunct
  `permutesF_p3` below (injectivity on D, identity off D).
- HOL `CARD` on sets ↔ `Set.ncard` (ENat; infinity ↦ 0 junk matches HOL's
  junk-free `CARD` only on finite sets); `CARD (dart H)` ↔ `H.darts.card`.
  In `localFan_p3` the conjunct `dih2k H (CARD FF)` is rendered with
  `(Set.ncard FF).toNat` (faces of local fans are finite; see
  `LOCAL_FAN_FINITE_FF`).
- `azim_cycle` is NOT yet ported upstream (flyspeck sphere.hl:414, the
  minimal-azimuth choice with norm tiebreak, condition `W SUBSET {p}`);
  `azimCycle_p3` is a verbatim `_p3` copy — NEEDS: move to the fan_defs /
  sphere layer at merge and re-point.
- Names suffixed `_p3` overlap the localization lane (LocalAuto2 worker owns
  `localization.hl`, whose definitions share these HOL names) or upstream
  files; they are deliberate local copies for independent compilation —
  NEEDS: dedup against `PackingAuto2.wedgeGe` (identical body) and
  `PolyAuto1.cyclicSet` at merge. `chooseNdPoint_p3` is defined after
  `IN_V_OF_FAN_EXISTS_DART` (name-resolution order in Lean).
- DISCHARGE note: theorems here are stated and proved standalone; where a
  conclusion coincides in shape with an appendix (LocalAuto1) result, no
  dependence is taken — consumers may discharge such goals by shape-matching
  either file.
- Anonymous HOL `prove(...)` blocks (e.g. WRGCVDR.hl:238) are kept as named
  helpers (`PAIRS_IN_UNIONS`); tactic-only `let`s (`SET_TAC`,
  `TR_SET_RULE`, `types_in_th`, `SMOOTH_GEN_ALL`, `AFF_SGN_TRULE`, …) have
  no Lean counterpart; the two bare `REWRITE_RULE` statements at
  WRGCVDR.hl:2496/2500 are refoldings of `LOCAL_FAN_IMP_BIJ_FF_NODES`/
  `FAN_IMP_BIJ_V_NODE_OF_HYP` and are subsumed by their `∃`-renderings.
-/

import Kepler.Text.Polytope
import Kepler.Text.Fan
import Kepler.Text.PackingAuto5
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Local instances and plain-function orbit (`orbit_map`) -/

/-- Darts are `V3 × V3` (HOL `real^3#real^3`); classical decidability for
`Hypermap (V3 × V3)`. -/
noncomputable instance dartDecEq3 : DecidableEq (V3 × V3) := Classical.decEq _

/-- HOL `orbit_map f x` (hypermap.hl:49) on a plain function; the
`Equiv.Perm` version is `Kepler.Text.orbitMap`. NEEDS: merge with the
hypermap layer's plain-function `orbit_map` when ported. -/
def orbitF_p3 {α : Type*} (f : α → α) (x : α) : Set α := {y | ∃ n : ℕ, f^[n] x = y}

/-- HOL `azim_cycle` (sphere.hl:414; minimal azimuth, distance tiebreak,
`W SUBSET {p}` degenerate case). NEEDS: upstream home in the sphere/fan_defs
layer; `_p3` copy. Note the argument order of the repo `projection`:
HOL `projection (w-v) (u-v)` ↔ `projection (u - v) (w - v)`. -/
noncomputable def azimCycle_p3 (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-! ## Definitions (WRGCVDR.hl:78–172, 341, 2773–2914) -/

/-- HOL `has_orders` (WRGCVDR.hl:78; also localization.hl:20 — `_p3`). -/
def hasOrders_p3 {α : Type*} (f : α → α) (k : ℕ) : Prop :=
  (∀ i, 0 < i → i < k → ¬(f^[i] = id)) ∧ f^[k] = id

/-- HOL `cyclic_on` (WRGCVDR.hl:82; also localization.hl:27 — `_p3`). -/
def cyclicOn_p3 {α : Type*} (f : α → α) (S : Set α) : Prop :=
  ∀ x ∈ S, S = {z | ∃ n : ℕ, z = f^[n] x}

/-- HOL `dih2k` (WRGCVDR.hl:86; also localization.hl:30 — `_p3`), with the
`Hypermap` structure carrying `dart`/maps (finiteness built in). -/
def dih2k_p3 {α : Type*} [DecidableEq α] (H : Hypermap α) (k : ℕ) : Prop :=
  H.darts.card = 2 * k ∧
    (∀ x ∈ H.darts, (↑H.darts : Set α) = H.face x ∪ (H.nodeMap : α → α) '' H.face x) ∧
    hasOrders_p3 (H.faceMap : α → α) k ∧
    hasOrders_p3 (H.edgeMap : α → α) 2 ∧
    hasOrders_p3 (H.nodeMap : α → α) 2

/-- HOL `EE` (WRGCVDR.hl:95; also localization.hl:38 — `_p3`). -/
def EE_p3 {α : Type*} (v : α) (S : Set (Set α)) : Set α := {w | {v, w} ∈ S}

/-- HOL `ord_pairs` (WRGCVDR.hl:97; also localization.hl:40 — `_p3`). -/
def ordPairs_p3 {α : Type*} (E : Set (Set α)) : Set (α × α) := {p | {p.1, p.2} ∈ E}

/-- HOL `self_pairs` (WRGCVDR.hl:99; also localization.hl:42 — `_p3`). -/
def selfPairs_p3 {α : Type*} (E : Set (Set α)) (V : Set α) : Set (α × α) :=
  {p | p.1 = p.2 ∧ p.1 ∈ V ∧ EE_p3 p.1 E = ∅}

/-- HOL `darts_of_hyp` (WRGCVDR.hl:102; also localization.hl:45 — `_p3`). -/
def dartsOfHyp_p3 {α : Type*} (E : Set (Set α)) (V : Set α) : Set (α × α) :=
  ordPairs_p3 E ∪ selfPairs_p3 E V

/-- HOL `ee_of_hyp` (WRGCVDR.hl:105; also localization.hl:48 — `_p3`). -/
noncomputable def eeOfHyp_p3 (_x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d

/-- HOL `nn_of_hyp` (WRGCVDR.hl:113; also localization.hl:51 — `_p3`). -/
noncomputable def nnOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p3 E V then (d.1, azimCycle_p3 (EE_p3 d.1 E) x d.1 d.2) else d

/-- HOL `ivs_azim_cycle` (WRGCVDR.hl:126; also localization.hl:55, whose
owner is the LocalAuto2 lane — `_p3`). -/
noncomputable def ivsAzimCycle_p3 (W : Set V3) (v0 v w : V3) : V3 :=
  if W = ∅ then w else Classical.epsilon fun x => x ∈ W ∧ azimCycle_p3 W v0 v x = w

/-- HOL `ff_of_hyp` (WRGCVDR.hl:130; also localization.hl:59 — `_p3`). -/
noncomputable def ffOfHyp_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p3 E V then (d.2, ivsAzimCycle_p3 (EE_p3 d.2 E) x d.2 d.1) else d

/-- HOL `HYP` (WRGCVDR.hl:140; also localization.hl:63 — `_p3`): the 4-tuple
`(darts, e, n, f)`; the hypermap coercion is rendered by the `∃`-form in
`localFan_p3`/`HYP_LEMMA` (see encoding notes). -/
noncomputable def HYP_p3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Set (V3 × V3) × ((V3 × V3 → V3 × V3) × ((V3 × V3 → V3 × V3) × (V3 × V3 → V3 × V3))) :=
  (dartsOfHyp_p3 E V, (eeOfHyp_p3 x V E, (nnOfHyp_p3 x V E, ffOfHyp_p3 x V E)))

/-- HOL `local_fan` (WRGCVDR.hl:144; also localization.hl:66 — `_p3`),
rendered existentially over the `Hypermap` whose components are those of
`HYP_p3 0 V E` (encoding notes). -/
def localFan_p3 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  ∃ H : Hypermap (V3 × V3),
    (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
    (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 0 V E ∧
    (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 0 V E ∧
    (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 0 V E ∧
    FAN 0 V E ∧
    (∃ x ∈ H.darts, FF = H.face x) ∧
    dih2k_p3 H FF.ncard

/-- HOL `azim_in_fan` (WRGCVDR.hl:151; also localization.hl:74 — `_p3`;
compare `Kepler.Text.Fan.azimFan`). -/
noncomputable def azimInFan_p3 (d : V3 × V3) (E : Set (Set V3)) : ℝ :=
  let dd := azimCycle_p3 (EE_p3 d.1 E) 0 d.1 d.2
  if 1 < (EE_p3 d.1 E).ncard then azim 0 d.1 d.2 dd else 2 * Real.pi

/-- HOL `wedge_in_fan_gt` (WRGCVDR.hl:156; also localization.hl:79 — `_p3`). -/
noncomputable def wedgeInFanGt_p3 (d : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (EE_p3 d.1 E).ncard then
    Kepler.Geom.wedge 0 d.1 d.2 (azimCycle_p3 (EE_p3 d.1 E) 0 d.1 d.2)
  else if EE_p3 d.1 E = {d.2} then
    {x | x ∉ affGe ({0, d.1} : Set V3) {d.2}}
  else
    {x | x ∉ affineSpan ℝ ({0, d.1} : Set V3)}

/-- HOL `wedge_ge` (WRGCVDR.hl:162; also localization.hl:85 — `_p3`).
Identical body to `Kepler.Text.wedgeGe` (PackingAuto2); kept as a `_p3`
copy per the lane convention. NEEDS: dedup at merge. -/
def wedgeGe_p3 (v0 v1 w1 w2 : V3) : Set V3 :=
  {z | 0 ≤ azim v0 v1 w1 z ∧ azim v0 v1 w1 z ≤ azim v0 v1 w1 w2}

/-- HOL `wedge_in_fan_ge` (WRGCVDR.hl:165; also localization.hl:88 — `_p3`). -/
noncomputable def wedgeInFanGe_p3 (d : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (EE_p3 d.1 E).ncard then
    wedgeGe_p3 0 d.1 d.2 (azimCycle_p3 (EE_p3 d.1 E) 0 d.1 d.2)
  else univ

/-- HOL `convex_local_fan` (WRGCVDR.hl:169; also localization.hl:92 — `_p3`). -/
def convexLocalFan_p3 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  localFan_p3 V E FF ∧
    ∀ x ∈ FF, azimInFan_p3 x E ≤ Real.pi ∧ V ⊆ wedgeInFanGe_p3 x E

/-- HOL `cyclic_set` (polyhedron.hl:126; needed by IDENTIFY_AZIM_CYCLE and
CYCLIC_SET_IMP_NOT_COLLINEAR). Identical to `Kepler.Text.cyclicSet`
(PolyAuto1). NEEDS: dedup at merge — `_p3` copy. -/
def cyclicSet_p3 (W : Set V3) (v w : V3) : Prop :=
  v ≠ w ∧ W.Finite ∧
    (∀ p ∈ W, ∀ q ∈ W, ∀ h : ℝ, p - q = h • (v - w) → p = q) ∧
    W ∩ affineSpan ℝ ({v, w} : Set V3) = ∅

/-- HOL `permutes` for a plain function (hypermap.hl): maps D into D,
identity off D, injective on D. Used for `ee/nn/ff_of_hyp` permutes
statements (`PermutesOn` covers the `Equiv.Perm` case). -/
def permutesF_p3 {α : Type*} (g : α → α) (D : Set α) : Prop :=
  (∀ d ∈ D, g d ∈ D) ∧ (∀ d ∉ D, g d = d) ∧ ∀ a ∈ D, ∀ b ∈ D, g a = g b → a = b

-- HOL `choose_nd_point` (WRGCVDR.hl:341, `new_specification` from
-- `IN_V_OF_FAN_EXISTS_DART` via SKOLEM) is defined after that theorem below
-- (Lean name-resolution order).

/-- HOL `power_map_points` (fan_chemin.hl; upstream, not ported): the
`n`-fold iterate of `f x V E v` started at `w`. `_p3` copy. -/
def powerMapPoints_p3 (f : V3 → Set V3 → Set (Set V3) → V3 → V3 → V3) (x : V3)
    (V : Set V3) (E : Set (Set V3)) (v w : V3) (n : ℕ) : V3 :=
  (f x V E v)^[n] w

/-- HOL `v_prime` (WRGCVDR.hl:2773; also localization.hl — `_p3`). -/
def vPrime_p3 (V : Set V3) (FF : Set (V3 × V3)) : Set V3 := {v | v ∈ V ∧ ∃ w, (v, w) ∈ FF}

/-- HOL `e_prime` (WRGCVDR.hl:2776; also localization.hl — `_p3`). -/
def ePrime_p3 (E : Set (Set V3)) (FF : Set (V3 × V3)) : Set (Set V3) :=
  {e | ∃ v w, e = {v, w} ∧ {v, w} ∈ E ∧ (v, w) ∈ FF}

/-- HOL `generic` (WRGCVDR.hl:2902, Definition 7.8 RTPRRJS; also
localization.hl — `_p3`). -/
def generic_p3 (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v w u, {v, w} ∈ E → u ∈ V → affGe {0} {v, w} ∩ affLt {0} {u} = ∅

/-- HOL `circular` (WRGCVDR.hl:2907; also localization.hl — `_p3`). -/
def circular_p3 (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∃ v w u, {v, w} ∈ E ∧ u ∈ V ∧ ¬(affGt {0} {v, w} ∩ affLt {0} {u} = ∅)

/-- HOL `lunar` (WRGCVDR.hl:2912; also localization.hl — `_p3`). -/
def lunar_p3 (d : V3 × V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ¬circular_p3 V E ∧ {d.1, d.2} ⊆ V ∧ d.1 ≠ d.2 ∧ Collinear3 0 d.1 d.2

/-! ## Hypermap plumbing and iterate basics (WRGCVDR.hl:49–233, 261–271,
347–351, 778–784, 227–232) -/

/-- WRGCVDR.hl:174 `FST_SND_FORM_OF_4_TUPLE`: the 4-tuple is determined by
its iterated projections. -/
theorem FST_SND_FORM_OF_4_TUPLE {α β γ δ : Type*} {X : α × β × γ × δ}
    {D : α} {e : β} {n : γ} {f : δ} :
    (X.1 = D ∧ X.2.1 = e ∧ X.2.2.1 = n ∧ X.2.2.2 = f) ↔ X = (D, e, n, f) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have heta : X = (X.1, X.2.1, X.2.2.1, X.2.2.2) := rfl
    rw [heta, h1, h2, h3, h4]
  · intro h
    rw [h]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- WRGCVDR.hl:49 `SPEC_HY_ELEMS`: the component reading of the
hypermap-carrier tuple (structure encoding absorbs `tuple_hypermap`). -/
theorem SPEC_HY_ELEMS {α : Type*} [DecidableEq α]
    (X : Finset α × Equiv.Perm α × Equiv.Perm α × Equiv.Perm α)
    (D : Finset α) (e n f : Equiv.Perm α) :
    (X.1 = D ∧ X.2.1 = e ∧ X.2.2.1 = n ∧ X.2.2.2 = f) ↔ X = (D, e, n, f) :=
  FST_SND_FORM_OF_4_TUPLE

/-- WRGCVDR.hl:66 `hypermap`: the carrier of a hypermap permutes its darts
and `e∘n∘f = I` (structure fields; HOL derives it from `hypermap_lemma`). -/
theorem HYPERMAP {α : Type*} [DecidableEq α] (H : Hypermap α) :
    PermutesOn H.edgeMap H.darts ∧ PermutesOn H.nodeMap H.darts ∧
      PermutesOn H.faceMap H.darts ∧ H.edgeMap * H.nodeMap * H.faceMap = 1 :=
  H.hypermap_lemma

/-- WRGCVDR.hl:238 (anonymous prove): edges land in `V` under `⋃₀ E ⊆ V`. -/
theorem PAIRS_IN_UNIONS {E : Set (Set V3)} {V : Set V3} {a b : V3}
    (he : {a, b} ∈ E) (hsub : ⋃₀ E ⊆ V) : a ∈ V ∧ b ∈ V :=
  ⟨hsub (show a ∈ ⋃₀ E from ⟨{a, b}, he, Set.mem_insert a {b}⟩),
    hsub (show b ∈ ⋃₀ E from
      ⟨{a, b}, he, Set.mem_insert_of_mem a (Set.mem_singleton b)⟩)⟩

/-- WRGCVDR.hl:245 `IN_DARTS_HYP_IMP_FST_SND_IN_V`. -/
theorem IN_DARTS_HYP_IMP_FST_SND_IN_V {E : Set (Set V3)} {V : Set V3}
    (hsub : ⋃₀ E ⊆ V) {y : V3 × V3} (hy : y ∈ dartsOfHyp_p3 E V) :
    y.1 ∈ V ∧ y.2 ∈ V := by
  rcases (Set.mem_union _ _ _).mp hy with h | h
  · exact PAIRS_IN_UNIONS h hsub
  · exact ⟨h.2.1, by rw [← h.1]; exact h.2.1⟩

/-- WRGCVDR.hl:187 `V_IN_DARTS_IMP_SWICH_SO_DO`. -/
theorem V_IN_DARTS_IMP_SWICH_SO_DO {α : Type*} {E : Set (Set α)} {V : Set α}
    {v : α × α} (h : v ∈ dartsOfHyp_p3 E V) : (v.2, v.1) ∈ dartsOfHyp_p3 E V := by
  rcases (Set.mem_union _ _ _).mp h with h | h
  · refine Set.mem_union_left _ ?_
    have h' : {v.1, v.2} ∈ E := h
    rw [Set.pair_comm] at h'
    exact h'
  · have h' : v.1 = v.2 ∧ v.1 ∈ V ∧ EE_p3 v.1 E = ∅ := h
    refine Set.mem_union_right _ ?_
    show v.2 = v.1 ∧ v.2 ∈ V ∧ EE_p3 v.2 E = ∅
    exact ⟨h'.1.symm, by rw [← h'.1]; exact h'.2.1, by rw [← h'.1]; exact h'.2.2⟩

/-- WRGCVDR.hl:198 `V_IN_DARTS_IFF_SWICH_SO_DO` (HOL takes the implication
as the iff). -/
theorem V_IN_DARTS_IFF_SWICH_SO_DO {α : Type*} {E : Set (Set α)} {V : Set α}
    {v : α × α} : v ∈ dartsOfHyp_p3 E V ↔ (v.2, v.1) ∈ dartsOfHyp_p3 E V :=
  ⟨V_IN_DARTS_IMP_SWICH_SO_DO, V_IN_DARTS_IMP_SWICH_SO_DO⟩

/-- WRGCVDR.hl:261 `POWER_SND`; HOL `POWER`/`ITER` both collapse to
`Nat.iterate`. -/
theorem POWER_SND {α : Type*} (f : α → α) (n : ℕ) : f^[n + 1] = f ∘ f^[n] :=
  Function.iterate_succ' f n

/-- WRGCVDR.hl:268 `POWER_TO_ITER`: definitional in the Lean encoding. -/
theorem POWER_TO_ITER {α : Type*} (f : α → α) (n : ℕ) :
    (f^[n] : α → α) = fun x => f^[n] x := rfl

/-- WRGCVDR.hl:347 `ITER_N_I`. -/
theorem ITER_N_I {α : Type*} (n : ℕ) : (id : α → α)^[n] = id := Function.iterate_id n

/-- WRGCVDR.hl:633 `ITER1`. -/
theorem ITER1 {α : Type*} (f : α → α) : f^[1] = f := Function.iterate_one f

/-- WRGCVDR.hl:227 `X_IN_ITS_ORBIT`. -/
theorem X_IN_ITS_ORBIT {α : Type*} (f : α → α) (x : α) : x ∈ orbitF_p3 f x :=
  ⟨0, rfl⟩

/-- WRGCVDR.hl:231 `X_IN_HYP_ORBITS`. -/
theorem X_IN_HYP_ORBITS {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    x ∈ H.edge x ∧ x ∈ H.node x ∧ x ∈ H.face x :=
  ⟨H.mem_edge_self x, H.mem_node_self x, H.mem_face_self x⟩

/-- WRGCVDR.hl:778 `IN_ORBIT_MAP_IMP_F_Y`. -/
theorem IN_ORBIT_MAP_IMP_F_Y {α : Type*} {f : α → α} {x y : α}
    (h : y ∈ orbitF_p3 f x) : f y ∈ orbitF_p3 f x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩

/-! ## Darts-set basics (WRGCVDR.hl:275–342, 1294–1297, 1347–1588,
1802–1804, 2857–2863) -/

/-- WRGCVDR.hl:290 `IN_ORD_PAIRS_IMP_IMP_IN_TOO`. -/
theorem IN_ORD_PAIRS_IMP_IMP_IN_TOO {α : Type*} {E : Set (Set α)} {V : Set α}
    {y : α × α} {d : α} (hy : y ∈ ordPairs_p3 E)
    (hd : (y.1, d) ∈ dartsOfHyp_p3 E V) : (y.1, d) ∈ ordPairs_p3 E := by
  rcases (Set.mem_union _ _ _).mp hd with h | h
  · exact h
  · exfalso
    have hself : y.1 = d ∧ y.1 ∈ V ∧ EE_p3 y.1 E = ∅ := h
    have hyE : y.2 ∈ EE_p3 y.1 E := hy
    exact absurd hyE (by rw [hself.2.2]; exact fun hc => hc)

/-- WRGCVDR.hl:313 `IN_ORD_PAIRS_IMP_SND_IN_EE_FST`. -/
theorem IN_ORD_PAIRS_IMP_SND_IN_EE_FST {α : Type*} {E : Set (Set α)}
    {y : α × α} (hy : y ∈ ordPairs_p3 E) : y.2 ∈ EE_p3 y.1 E := hy

/-- WRGCVDR.hl:1294 `IN_SELF_PAIRS_IMP_EE_EMPTY`. -/
theorem IN_SELF_PAIRS_IMP_EE_EMPTY {α : Type*} {E : Set (Set α)} {V : Set α}
    {x : α × α} (h : x ∈ selfPairs_p3 E V) : EE_p3 x.1 E = ∅ := h.2.2

/-- WRGCVDR.hl:327 `IN_SELF_PAIRS_IMP_FST_EQ_SND_FORALL`. -/
theorem IN_SELF_PAIRS_IMP_FST_EQ_SND_FORALL {α : Type*} {E : Set (Set α)} {V : Set α}
    (v : α) {y : α × α} (hy : y ∈ selfPairs_p3 E V)
    (hd : (y.1, v) ∈ dartsOfHyp_p3 E V) : y.1 = v := by
  rcases (Set.mem_union _ _ _).mp hd with h | h
  · exfalso
    have hv : v ∈ EE_p3 y.1 E := h
    exact absurd hv (by rw [hy.2.2]; exact fun hc => hc)
  · exact h.1

/-- WRGCVDR.hl:1347 `IN_E_IMP_IMP_IN_DARTS`. -/
theorem IN_E_IMP_IMP_IN_DARTS {α : Type*} {E : Set (Set α)} {V : Set α} {a b : α}
    (h : {a, b} ∈ E) : (a, b) ∈ dartsOfHyp_p3 E V := Set.mem_union_left _ h

/-- WRGCVDR.hl:1358 `PAIR_EQ2`. -/
theorem PAIR_EQ2 {α β : Type*} {a b : α × β} : a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · intro h
    cases a with
    | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
        simp only at h
        rw [h.1, h.2]

/-- WRGCVDR.hl:1363 `IN_ORD_E_EQ_IN_E`. -/
theorem IN_ORD_E_EQ_IN_E {α : Type*} {E : Set (Set α)} (x : α × α) :
    x ∈ ordPairs_p3 E ↔ {x.1, x.2} ∈ E := Iff.rfl

/-- WRGCVDR.hl:1568 `IN_E_IFF_IN_ORD_E`. -/
theorem IN_E_IFF_IN_ORD_E {α : Type*} {E : Set (Set α)} (a b : α) :
    {a, b} ∈ E ↔ (a, b) ∈ ordPairs_p3 E := Iff.rfl

/-- WRGCVDR.hl:1576 `IN_ORD_E_IFF_SWITCH_TOO`. -/
theorem IN_ORD_E_IFF_SWITCH_TOO {α : Type*} {E : Set (Set α)} (x : α × α) :
    x ∈ ordPairs_p3 E ↔ (x.2, x.1) ∈ ordPairs_p3 E := by
  rw [IN_ORD_E_EQ_IN_E, IN_ORD_E_EQ_IN_E]
  exact ⟨fun h => Set.pair_comm x.1 x.2 ▸ h, fun h => Set.pair_comm x.2 x.1 ▸ h⟩

/-- WRGCVDR.hl:275 `UNI_E_IMP_EE_EQ_SET_OF_EDGE`. -/
theorem UNI_E_IMP_EE_EQ_SET_OF_EDGE {E : Set (Set V3)} {V : Set V3}
    (h : ⋃₀ E ⊆ V) (v : V3) : EE_p3 v E = setOfEdge v V E := by
  ext w
  constructor
  · intro hw
    have hwV : w ∈ ⋃₀ E := Set.mem_sUnion.mpr ⟨{v, w}, hw, by simp⟩
    exact ⟨hw, h hwV⟩
  · rintro ⟨hw, -⟩
    exact hw

/-- WRGCVDR.hl:1264 `EE_SUBSET_UNIONS_E`. -/
theorem EE_SUBSET_UNIONS_E {α : Type*} (v : α) (E : Set (Set α)) :
    EE_p3 v E ⊆ ⋃₀ E := fun w hw => Set.mem_sUnion.mpr ⟨{v, w}, hw, by simp⟩

/-- WRGCVDR.hl:2861 `SUBSET_IMP_SO_DO_EE`. -/
theorem SUBSET_IMP_SO_DO_EE {α : Type*} {W1 W2 : Set (Set α)} (h : W1 ⊆ W2) (v : α) :
    EE_p3 v W1 ⊆ EE_p3 v W2 := fun _ hw => h hw

/-- WRGCVDR.hl:203 `IN_V_OF_FAN_EXISTS_DART`. -/
theorem IN_V_OF_FAN_EXISTS_DART {E : Set (Set V3)} {V : Set V3} (hsub : ⋃₀ E ⊆ V)
    {u : V3} (hu : u ∈ V) : ∃ v ∈ V, (u, v) ∈ dartsOfHyp_p3 E V := by
  by_cases hex : ∃ w, {u, w} ∈ E
  · obtain ⟨w, hw⟩ := hex
    have hwV : w ∈ ⋃₀ E := Set.mem_sUnion.mpr ⟨{u, w}, hw, by simp⟩
    exact ⟨w, hsub hwV, Set.mem_union_left _ hw⟩
  · have hE : EE_p3 u E = ∅ := by
      rw [EE_p3]
      exact Set.eq_empty_iff_forall_notMem.mpr fun w hw => hex ⟨w, hw⟩
    exact ⟨u, hu, Set.mem_union_right _ ⟨rfl, hu, hE⟩⟩

-- HOL `choose_nd_point` (WRGCVDR.hl:341): Skolemization of the previous.

/-- HOL `choose_nd_point` (WRGCVDR.hl:341, `new_specification` from
`IN_V_OF_FAN_EXISTS_DART` via SKOLEM). -/
noncomputable def chooseNdPoint_p3 (u : V3) (E : Set (Set V3)) (V : Set V3) : V3 :=
  if h : ⋃₀ E ⊆ V ∧ u ∈ V then Classical.choose (IN_V_OF_FAN_EXISTS_DART h.1 h.2) else u

/-- WRGCVDR.hl:341 `choose_nd_point` (the specification). -/
theorem choose_nd_point (u : V3) (E : Set (Set V3)) (V : Set V3) (h1 : ⋃₀ E ⊆ V)
    (h2 : u ∈ V) :
    chooseNdPoint_p3 u E V ∈ V ∧ (u, chooseNdPoint_p3 u E V) ∈ dartsOfHyp_p3 E V := by
  have hexp : chooseNdPoint_p3 u E V = Classical.choose (IN_V_OF_FAN_EXISTS_DART h1 h2) :=
    dif_pos ⟨h1, h2⟩
  rw [hexp]
  exact Classical.choose_spec (IN_V_OF_FAN_EXISTS_DART h1 h2)

/-! ## Order/cardinality lemmas (WRGCVDR.hl:357–586, 744–791,
2503–2504, 2868–2888) -/

/-- WRGCVDR.hl:357 `HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW`. -/
theorem HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW {α : Type*} {f : α → α} {k : ℕ}
    (hf : hasOrders_p3 f k) (hk : k ≠ 0) (x : α) :
    orbitF_p3 f x = {y | ∃ n < k, f^[n] x = y} := by
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

/-- WRGCVDR.hl:469 `FINITENESS_OF_K_FIRST_ELMS` (stated early for reuse;
HOL places it at line 469). -/
theorem FINITENESS_OF_K_FIRST_ELMS {α : Type*} (f : ℕ → α) (k : ℕ) :
    (f '' {n : ℕ | n < k}).Finite :=
  (Set.finite_Iio k).image f

/-- WRGCVDR.hl:381 `FINITE_OF_N_FIRST_ELMS`. -/
theorem FINITE_OF_N_FIRST_ELMS {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    {y : α | ∃ n < k, f^[n] x = y}.Finite := by
  have hsub : {y : α | ∃ n < k, f^[n] x = y} ⊆ (fun n => f^[n] x) '' {n : ℕ | n < k} :=
    fun y hy => hy
  exact ((FINITENESS_OF_K_FIRST_ELMS (fun n => f^[n] x) k).subset hsub)

/-- WRGCVDR.hl:396 `CARD_INSERT_GE_AND_LE`. -/
theorem CARD_INSERT_GE_AND_LE {α : Type*} (s : Finset α) (x : α) :
    s.card ≤ (insert x s).card ∧ (insert x s).card ≤ s.card + 1 :=
  ⟨Finset.card_le_card (Finset.subset_insert _ _), Finset.card_insert_le x s⟩

/-- WRGCVDR.hl:408 `HAVING_ORDERS_K_IMP_CARD_ORBIT_LE_K`. -/
theorem HAVING_ORDERS_K_IMP_CARD_ORBIT_LE_K {α : Type*} {f : α → α} {k : ℕ}
    (hf : hasOrders_p3 f k) (hk : k ≠ 0) (x : α) : (orbitF_p3 f x).ncard ≤ k := by
  have hEq : {y : α | ∃ n < k, f^[n] x = y} = (fun n => f^[n] x) '' (Finset.range k : Set ℕ) := by
    ext y
    simp [Finset.mem_range]
  rw [HAS_ORDERS_IMP_ORBIT_MAP_FIRST_ROW hf hk x, hEq]
  calc Set.ncard ((fun n => f^[n] x) '' (Finset.range k : Set ℕ))
      ≤ Set.ncard (Finset.range k : Set ℕ) := Set.ncard_image_le
    _ = k := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- WRGCVDR.hl:479 `CARD_K_FIRST_ELMS_LE_K`. -/
theorem CARD_K_FIRST_ELMS_LE_K {α : Type*} (f : ℕ → α) (k : ℕ) :
    Set.ncard (f '' {n : ℕ | n < k}) ≤ k := by
  have hEq : (f '' {n : ℕ | n < k}) = f '' (Finset.range k : Set ℕ) := by
    ext y
    simp [Finset.mem_range]
  rw [hEq]
  calc Set.ncard (f '' (Finset.range k : Set ℕ))
      ≤ Set.ncard (Finset.range k : Set ℕ) := Set.ncard_image_le
    _ = k := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- WRGCVDR.hl:434 `CARD_LE_K_OF_SET_K_FIRST_ELMS` (HOL derives it from
`CARD_FINITE_SERIES_LE`; identical content to `CARD_K_FIRST_ELMS_LE_K`). -/
theorem CARD_LE_K_OF_SET_K_FIRST_ELMS {α : Type*} (f : ℕ → α) (k : ℕ) :
    Set.ncard (f '' {n : ℕ | n < k}) ≤ k :=
  CARD_K_FIRST_ELMS_LE_K f k

/-- WRGCVDR.hl:528 `CARD_K_ELMS_EQ_K_IMP_ALL_DISTINCT`. -/
theorem CARD_K_ELMS_EQ_K_IMP_ALL_DISTINCT {α : Type*} [DecidableEq α] (f : ℕ → α)
    (k : ℕ) (h : Set.ncard (f '' {n : ℕ | n < k}) = k) :
    ∀ i j, i < k → j < k → i ≠ j → f i ≠ f j := by
  have hEq : (f '' {n : ℕ | n < k}) = f '' (Finset.range k : Set ℕ) := by
    ext y; simp
  rw [hEq] at h
  have h2 : (Finset.image f (Finset.range k)).card = (Finset.range k).card := by
    rw [← Set.ncard_coe_finset (Finset.image f (Finset.range k)), Finset.coe_image, h,
      Finset.card_range]
  have hinj : Set.InjOn f ((Finset.range k : Finset ℕ) : Set ℕ) :=
    Finset.card_image_iff.mp h2
  intro i j hi hj hij hfe
  exact hij (hinj (by simpa using hi) (by simpa using hj) hfe)

/-- WRGCVDR.hl:575 `CARD_ITER_K_EK_IMP_DIST`. -/
theorem CARD_ITER_K_EK_IMP_DIST {α : Type*} [DecidableEq α] (f : α → α) (x : α) (k : ℕ)
    (h : Set.ncard ((fun n => f^[n] x) '' {n : ℕ | n < k}) = k) :
    ∀ i j, i < k → j < k → i ≠ j → f^[i] x ≠ f^[j] x :=
  CARD_K_ELMS_EQ_K_IMP_ALL_DISTINCT (fun n => f^[n] x) k h

/-- WRGCVDR.hl:546 `CARD_UNION_NOT_DISTJ_LT`. -/
theorem CARD_UNION_NOT_DISTJ_LT {α : Type*} {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (h : s ∩ t ≠ ∅) : (s ∪ t).ncard < s.ncard + t.ncard :=
  Set.ncard_union_lt hs ht fun hd => h (by rwa [Set.disjoint_iff_inter_eq_empty] at hd)

/-- WRGCVDR.hl:683 `HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT`. -/
theorem HAS_ORDK_IN_ORBIT_IMP_SAME_ORBIT {α : Type*} {f : α → α} {k : ℕ}
    (hf : hasOrders_p3 f k) (hk : k ≠ 0) {x y : α} (h : x ∈ orbitF_p3 f y) :
    orbitF_p3 f x = orbitF_p3 f y := by
  obtain ⟨n, rfl⟩ := h
  have key : ∀ m : ℕ, f^[m] y = f^[m % k] y := by
    intro m
    have hnm : m = k * (m / k) + m % k := (Nat.div_add_mod m k).symm
    conv => lhs; rw [hnm]
    rw [Function.iterate_add, Function.iterate_mul, hf.2]
    simp
  have main : ∀ q < k, orbitF_p3 f (f^[q] y) = orbitF_p3 f y := by
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
  have hnx : orbitF_p3 f (f^[n] y) = orbitF_p3 f (f^[n % k] y) := by congr 1; exact key n
  rw [hnx, main (n % k) (Nat.mod_lt n (Nat.pos_of_ne_zero hk))]

/-- WRGCVDR.hl:744 `TOW_BIJS_IMP_BIJ_BETWEEN_FIRST` (the HOL choice
`@a. a IN S2 /\ f x = g a` rendered by a `dite` on the existence, since
Lean's `Classical.epsilon` needs `Nonempty`). -/
theorem TOW_BIJS_IMP_BIJ_BETWEEN_FIRST {α β γ : Type*} {f : β → α} {g : γ → α}
    {S1 : Set β} {S2 : Set γ} {V : Set α}
    {aa : γ} (hf : Set.BijOn f S1 V) (hg : Set.BijOn g S2 V) (ff : β → γ)
    (hff : ∀ x, ff x = if h : ∃ a : γ, a ∈ S2 ∧ f x = g a then h.choose else aa) :
    Set.BijOn ff S1 S2 := by
  have hkey : ∀ x ∈ S1, ff x ∈ S2 ∧ f x = g (ff x) := by
    intro x hx
    obtain ⟨a, ha2, hga⟩ := hg.surjOn (hf.mapsTo hx)
    have hex : ∃ a : γ, a ∈ S2 ∧ f x = g a := ⟨a, ha2, hga.symm⟩
    rw [hff x, dif_pos hex]
    exact hex.choose_spec
  have hmaps : Set.MapsTo ff S1 S2 := fun x hx => (hkey x hx).1
  have hinj : Set.InjOn ff S1 := by
    intro a ha c hc hfe
    have h1 : f a = g (ff a) := (hkey a ha).2
    have h2 : f c = g (ff c) := (hkey c hc).2
    rw [hfe] at h1
    exact hf.injOn ha hc (by rw [h1, h2])
  have hsurj : Set.SurjOn ff S1 S2 := by
    intro y hy
    obtain ⟨x, hx1, hx2⟩ := hf.surjOn (hg.mapsTo hy)
    have hfe := hkey x hx1
    exact ⟨x, hx1, hg.injOn hfe.1 hy (hfe.2.symm.trans hx2)⟩
  exact ⟨hmaps, hinj, hsurj⟩

/-- WRGCVDR.hl:762 `INDENT_IN_S1_IMP_BIJ`. -/
theorem INDENT_IN_S1_IMP_BIJ {α β : Type*} {f g : α → β} {S1 : Set α} {S2 : Set β}
    (h : Set.BijOn f S1 S2) (h2 : ∀ x ∈ S1, f x = g x) : Set.BijOn g S1 S2 := by
  have hmaps : Set.MapsTo g S1 S2 := fun y hy => h2 y hy ▸ h.mapsTo hy
  have hinj : Set.InjOn g S1 := by
    intro a ha c hc hfe
    exact h.injOn ha hc (by rw [h2 a ha, h2 c hc]; exact hfe)
  have hsurj : Set.SurjOn g S1 S2 := by
    intro z hz
    obtain ⟨a, ha, hfa⟩ := h.surjOn hz
    exact ⟨a, ha, (h2 a ha).symm.trans hfa⟩
  exact ⟨hmaps, hinj, hsurj⟩

/-- WRGCVDR.hl:790 `SURJ_IMP_S2_EQ_IMAGE_S1` (HOL `SURJ` bundles
maps-to with surjectivity; rendered as the conjunction). -/
theorem SURJ_IMP_S2_EQ_IMAGE_S1 {α β : Type*} {f : α → β} {S1 : Set α} {S2 : Set β}
    (h : Set.MapsTo f S1 S2 ∧ Set.SurjOn f S1 S2) : f '' S1 = S2 := by
  refine Set.Subset.antisymm ?_ h.2
  rintro y ⟨x, hx, rfl⟩
  exact h.1 hx

/-- WRGCVDR.hl:2503 `ITER_FIXPOINT2`. -/
theorem ITER_FIXPOINT2 {α : Type*} {f : α → α} {x : α} (h : f x = x) (n : ℕ) :
    f^[n] x = x := Function.iterate_fixed h n

private theorem existsMinAux {α : Type*} [DecidableEq α] (ll : α → α → Prop) :
    ∀ n : ℕ, ∀ s : Finset α, s.card ≤ n → s.Nonempty →
      (∀ x y : α, ll x y ∨ ll y x) → (∀ x y z : α, ll x y → ll y z → ll x z) →
      ∃ v ∈ s, ∀ w ∈ s, ll v w := by
  intro n
  induction n with
  | zero =>
    intro s hcard hne _ _
    obtain ⟨x, hx⟩ := hne
    have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact absurd hx (by rw [hs0]; exact Finset.notMem_empty x)
  | succ k ih =>
    intro s hcard hne hconn htrans
    obtain ⟨x, hx⟩ := hne
    by_cases hall : ∀ w ∈ s, ll x w
    · exact ⟨x, hx, hall⟩
    · push_neg at hall
      obtain ⟨w, hw, hnx⟩ := hall
      have hwx : w ≠ x := by
        intro he
        apply hnx
        rw [he]
        exact (hconn x x).elim id id
      have hcard2 : (s.erase x).card ≤ k := by
        have h1 : (s.erase x).card < s.card := Finset.card_erase_lt_of_mem hx
        exact Nat.lt_succ_iff.mp (lt_of_lt_of_le h1 hcard)
      obtain ⟨v, hv, hvall⟩ :=
        ih (s.erase x) hcard2 ⟨w, Finset.mem_erase.mpr ⟨hwx, hw⟩⟩ hconn htrans
      by_cases hxv : ll x v
      · refine ⟨x, hx, ?_⟩
        intro y hy
        by_cases hyx : y = x
        · rw [hyx]; exact (hconn x x).elim id id
        · exact htrans x v y hxv (hvall y (Finset.mem_erase.mpr ⟨hyx, hy⟩))
      · refine ⟨v, Finset.mem_of_mem_erase hv, ?_⟩
        intro y hy
        by_cases hyx : y = x
        · rw [hyx]; exact (hconn x v).resolve_left hxv
        · exact hvall y (Finset.mem_erase.mpr ⟨hyx, hy⟩)

/-- WRGCVDR.hl:956 `EXISTS_SMALLEST_ELMS`: a nonempty finite set has an
`ll`-least element for any connex transitive relation. -/
theorem EXISTS_SMALLEST_ELMS {α : Type*} [DecidableEq α] (ll : α → α → Prop)
    (W : Set α) (hfin : W.Finite) (hne : W ≠ ∅)
    (hconn : ∀ x y : α, ll x y ∨ ll y x)
    (htrans : ∀ x y z : α, ll x y → ll y z → ll x z) :
    ∃ v ∈ W, ∀ w ∈ W, ll v w := by
  have hne2 : hfin.toFinset.Nonempty := by
    by_contra hc
    exact hne (Set.eq_empty_iff_forall_notMem.mpr fun x hx => hc ⟨x, by simpa using hx⟩)
  obtain ⟨v, hv, hvall⟩ :=
    existsMinAux ll hfin.toFinset.card hfin.toFinset (Nat.le_refl _) (by simpa using hne2)
      hconn htrans
  refine ⟨v, by simpa using hv, ?_⟩
  intro w hw
  exact hvall w (by simpa using hw)

/-! ## azim_cycle kit, ivs_azim_cycle, permutes of ee (WRGCVDR.hl:796–950,
1009–1281, 1594–1603) -/

/-- WRGCVDR.hl:1009 `EXIS_SMALLEST_WITH_AZIM_ORD` (minimal-azimuth element
with distance tiebreak; HOL proves it from `EXISTS_SMALLEST_ELMS` with
azim/projection connexity — genuine geometry, deferred). -/
theorem EXIS_SMALLEST_WITH_AZIM_ORD {W : Set V3} {v w p : V3}
    (h1 : ¬(W ⊆ {p})) (hfin : W.Finite) :
    ∃ u : V3, u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖ := sorry

/-- WRGCVDR.hl:1086 `AZIM_CYCLE_PROPERTIES`. -/
theorem AZIM_CYCLE_PROPERTIES {W : Set V3} {p : V3} (hsub : ¬(W ⊆ {p})) (hfin : W.Finite)
    (v w : V3) :
    azimCycle_p3 W v w p ≠ p ∧ azimCycle_p3 W v w p ∈ W ∧
      ∀ q ∈ W, q ≠ p →
        azim v w p (azimCycle_p3 W v w p) < azim v w p q ∨
          azim v w p (azimCycle_p3 W v w p) = azim v w p q ∧
            ‖projection (azimCycle_p3 W v w p - v) (w - v)‖ ≤
              ‖projection (q - v) (w - v)‖ := by
  obtain ⟨u, hu1, hu2, hu3⟩ := EXIS_SMALLEST_WITH_AZIM_ORD hsub hfin
  have hex : ∃ z : V3, z ≠ p ∧ z ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p z < azim v w p q ∨
        azim v w p z = azim v w p q ∧
          ‖projection (z - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖ :=
    ⟨u, hu1, hu2, hu3⟩
  rw [azimCycle_p3, if_neg hsub]
  exact Classical.epsilon_spec hex

/-- WRGCVDR.hl:1102 `W_SUBSET_SINGLETON_IMP_IDE`. -/
theorem W_SUBSET_SINGLETON_IMP_IDE {W : Set V3} {p : V3} (h : W ⊆ {p}) (v w : V3) :
    azimCycle_p3 W v w p = p := by
  simp only [azimCycle_p3, if_pos h]

/-- WRGCVDR.hl:832 `IDENTIFY_AZIM_CYCLE` (characterization of the chosen
cyclic successor; heavy geometry). -/
theorem IDENTIFY_AZIM_CYCLE {W : Set V3} {v w p u : V3}
    (h1 : ¬(W ⊆ {p})) (h2 : ¬Collinear3 v w p) (h3 : cyclicSet_p3 W v w)
    (h4 : u ≠ p ∧ u ∈ W)
    (h5 : ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖) :
    azimCycle_p3 W v w p = u := sorry

/-- WRGCVDR.hl:796 `CYCLIC_SET_IMP_NOT_COLLINEAR`. -/
theorem CYCLIC_SET_IMP_NOT_COLLINEAR {W : Set V3} {x y : V3} (h : cyclicSet_p3 W x y) :
    ∀ v ∈ W, ¬Collinear3 v x y := by
  obtain ⟨hxy, -, -, hdisj⟩ := h
  intro v hv hcol
  have hv2 : v ∈ affineSpan ℝ ({x, y} : Set V3) :=
    Collinear.mem_affineSpan_of_mem_of_ne hcol
      (by simp) (by simp) (by simp) hxy
  exact absurd (Set.mem_inter hv hv2) (by rw [hdisj]; exact Set.notMem_empty v)

/-- WRGCVDR.hl:1111 `AZIM_CYCLE_EQ_SIGMA_FAN`. -/
theorem AZIM_CYCLE_EQ_SIGMA_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hu : u ∈ setOfEdge v V E) :
    azimCycle_p3 (EE_p3 v E) x v u = sigmaFan x V E v u := sorry

/-- WRGCVDR.hl:1151 `IVS_AZIM_AS_SIGMA_FAN`. -/
theorem IVS_AZIM_AS_SIGMA_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hu : u ∈ setOfEdge v V E) :
    ivsAzimCycle_p3 (setOfEdge v V E) x v u =
      Classical.epsilon (fun xx : V3 => xx ∈ setOfEdge v V E ∧ sigmaFan x V E v xx = u) := sorry

/-- WRGCVDR.hl:1177 `IVS_AZIM_PROPERTIES`. -/
theorem IVS_AZIM_PROPERTIES {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hu : u ∈ setOfEdge v V E) :
    ivsAzimCycle_p3 (setOfEdge v V E) x v u ∈ setOfEdge v V E ∧
      sigmaFan x V E v (ivsAzimCycle_p3 (setOfEdge v V E) x v u) = u := sorry

/-- WRGCVDR.hl:1208 `IVS_AZIM_EQ_INVERSE_SIGMA_FAN`. -/
theorem IVS_AZIM_EQ_INVERSE_SIGMA_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hw : {v, u} ∈ E) :
    ivsAzimCycle_p3 (EE_p3 v E) x v u = inverse1SigmaFan x V E v u := sorry

/-- WRGCVDR.hl:1236 `EE_OF_HYP_PERMUTES_DARTS`. -/
theorem EE_OF_HYP_PERMUTES_DARTS (x : V3) (V : Set V3) (E : Set (Set V3)) :
    permutesF_p3 (eeOfHyp_p3 x V E) (dartsOfHyp_p3 E V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [show eeOfHyp_p3 x V E d = if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d from rfl,
      if_pos hd]
    exact V_IN_DARTS_IMP_SWICH_SO_DO hd
  · intro d hd
    rw [show eeOfHyp_p3 x V E d = if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d from rfl,
      if_neg hd]
  · intro a ha b hb hab
    have ha' : eeOfHyp_p3 x V E a = (a.2, a.1) := by rw [eeOfHyp_p3, if_pos ha]
    have hb' : eeOfHyp_p3 x V E b = (b.2, b.1) := by rw [eeOfHyp_p3, if_pos hb]
    rw [ha', hb'] at hab
    rw [Prod.mk.injEq] at hab
    exact Prod.ext hab.2 hab.1

/-- WRGCVDR.hl:1276 `FAN_IMP_FINITE_EE`. -/
theorem FAN_IMP_FINITE_EE {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E)
    (v : V3) : (EE_p3 v E).Finite :=
  hfan.2.2.1.1.subset (Set.Subset.trans (EE_SUBSET_UNIONS_E v E) hfan.1)

/-- WRGCVDR.hl:1594 `SIG_AND_INVERSE1_SIG`. -/
theorem SIG_AND_INVERSE1_SIG {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E)
    {u w v : V3} (hw : {u, w} ∈ E) (hv : sigmaFan x V E u w = v) :
    inverse1SigmaFan x V E u v = w := by
  have hmem : w ∈ setOfEdge u V E := (properties_of_setOfEdge_fan x V E u w hfan).mp hw
  have hvo : sigmaFan x V E u w ∈ setOfEdge u V E := sigma_fan_in_setOfEdge hfan hmem
  have hve : {u, v} ∈ E := by
    rw [← hv]
    exact (properties_of_setOfEdge_fan x V E u _ hfan).mpr hvo
  have hin := INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := u) hfan
  have hiv : inverse1SigmaFan x V E u v ∈ setOfEdge u V E :=
    (properties_of_setOfEdge_fan x V E u _ hfan).mp (hin.1 v hve)
  exact mono_sigma_fan (x := x) (V := V) (E := E) (v := u) hfan hiv hmem (by
    rw [hin.2.1 v hve, hv])

/-- WRGCVDR.hl:1600 `INVERSE1_SIG_AND_SIG`. -/
theorem INVERSE1_SIG_AND_SIG {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E)
    {u v w : V3} (hv : {u, v} ∈ E) (hw : inverse1SigmaFan x V E u v = w) :
    sigmaFan x V E u w = v := by
  have h2 := (INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := u) hfan).2.1
  rw [← hw]
  exact h2 v hv

/-! ## nn/ff machinery and the hypermap of a fan (WRGCVDR.hl:811–826,
1302–1962, 1995–2038) -/

/-- WRGCVDR.hl:811 `SLIDABLE_PROJECTION` (repo `projection` argument order:
HOL `projection e (t % e + x)` ↔ `projection (t • e + x) e`). -/
theorem SLIDABLE_PROJECTION (t : ℝ) {e x : V3} (he : e ≠ 0) :
    projection (t • e + x) e = projection x e := by
  have hne : (e ⬝ᵥ e) ≠ 0 := by
    intro h
    have hsum : ∑ i : Fin 3, e.ofLp i * e.ofLp i = 0 := by simpa [dotProduct] using h
    have hz : e.ofLp = 0 := by
      funext i
      exact mul_self_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (e.ofLp j)).mp hsum i
          (Finset.mem_univ i))
    exact he (by simpa using hz)
  unfold projection
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul]
  rw [add_dotProduct, smul_dotProduct, add_div, add_smul]
  have h1 : (t • (e ⬝ᵥ e)) / (e ⬝ᵥ e) = t := by rw [smul_eq_mul]; field_simp
  rw [h1, add_sub_add_left_eq_sub]

/-- WRGCVDR.hl:825 `LINEAR_PROJECTION`. -/
theorem LINEAR_PROJECTION (t : ℝ) (x e : V3) :
    projection (t • x) e = t • projection x e := by
  unfold projection
  simp only [WithLp.ofLp_smul]
  rw [smul_dotProduct, smul_sub, smul_smul, smul_eq_mul, ← mul_div_assoc']

/-- WRGCVDR.hl:1302 `IN_DARTS_IFF_NN_OF_HYP_TOO`. -/
theorem IN_DARTS_IFF_NN_OF_HYP_TOO {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) (y : V3 × V3) :
    y ∈ dartsOfHyp_p3 E V ↔ nnOfHyp_p3 x V E y ∈ dartsOfHyp_p3 E V := sorry

/-- WRGCVDR.hl:1372 `FAN_IMP_NN_OF_HYP_PERMUTES_DARTS`. -/
theorem FAN_IMP_NN_OF_HYP_PERMUTES_DARTS {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) : permutesF_p3 (nnOfHyp_p3 x V E) (dartsOfHyp_p3 E V) := sorry

/-- WRGCVDR.hl:1521 `IVS_AZIM_EMPTY_IDE`. -/
theorem IVS_AZIM_EMPTY_IDE (x y t : V3) : ivsAzimCycle_p3 ∅ x y t = t := by
  rw [ivsAzimCycle_p3, if_pos rfl]

/-- WRGCVDR.hl:1529 `FAN_IMP_IN_DARTS_IFF_FF_TOO`. -/
theorem FAN_IMP_IN_DARTS_IFF_FF_TOO {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) (y : V3 × V3) :
    y ∈ dartsOfHyp_p3 E V ↔ ffOfHyp_p3 x V E y ∈ dartsOfHyp_p3 E V := sorry

/-- WRGCVDR.hl:1748 `nn_of_hyp3_alt`. -/
theorem nn_of_hyp3_alt (x : V3) (V : Set V3) (E : Set (Set V3)) (y : V3 × V3) :
    nnOfHyp_p3 x V E y =
      if y ∉ dartsOfHyp_p3 E V ∨ y ∈ selfPairs_p3 E V then y
      else (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) := by
  by_cases h : y ∈ dartsOfHyp_p3 E V
  · rw [show nnOfHyp_p3 x V E y =
        if y ∈ dartsOfHyp_p3 E V then (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) else y
      from rfl, if_pos h]
    by_cases hs : y ∈ selfPairs_p3 E V
    · have he : y.1 = y.2 := hs.1
      have hE : EE_p3 y.1 E = ∅ := hs.2.2
      rw [if_pos (Or.inr hs),
        W_SUBSET_SINGLETON_IMP_IDE (v := x) (w := y.1) (p := y.2) (by simp [hE]),
        Prod.mk.eta]
    · have hneg : ¬(y ∉ dartsOfHyp_p3 E V ∨ y ∈ selfPairs_p3 E V) := by
        intro hc
        rcases hc with h' | h'
        · exact h' h
        · exact hs h'
      rw [if_neg hneg]
  · rw [show nnOfHyp_p3 x V E y =
        if y ∈ dartsOfHyp_p3 E V then (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) else y
      from rfl, if_neg h, if_pos (Or.inl h)]

/-- WRGCVDR.hl:1762 `ff_of_hyp3`. -/
theorem ff_of_hyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) (u : V3 × V3) :
    ffOfHyp_p3 x V E u =
      if u ∉ dartsOfHyp_p3 E V ∨ u ∈ selfPairs_p3 E V then u
      else (u.2, ivsAzimCycle_p3 (EE_p3 u.2 E) x u.2 u.1) := by
  by_cases h : u ∈ dartsOfHyp_p3 E V
  · rw [show ffOfHyp_p3 x V E u =
        if u ∈ dartsOfHyp_p3 E V then (u.2, ivsAzimCycle_p3 (EE_p3 u.2 E) x u.2 u.1) else u
      from rfl, if_pos h]
    by_cases hs : u ∈ selfPairs_p3 E V
    · have he : u.1 = u.2 := hs.1
      have hE : EE_p3 u.1 E = ∅ := hs.2.2
      have hz : ivsAzimCycle_p3 (EE_p3 u.2 E) x u.2 u.1 = u.1 := by
        rw [ivsAzimCycle_p3, if_pos (by rw [← he]; exact hE)]
      rw [if_pos (Or.inr hs), hz]
      have hu' : u = (u.2, u.2) := PAIR_EQ2.mpr ⟨he, rfl⟩
      rw [he, hu']
    · have hneg : ¬(u ∉ dartsOfHyp_p3 E V ∨ u ∈ selfPairs_p3 E V) := by
        intro hc
        rcases hc with h' | h'
        · exact h' h
        · exact hs h'
      rw [if_neg hneg]
  · rw [show ffOfHyp_p3 x V E u =
        if u ∈ dartsOfHyp_p3 E V then (u.2, ivsAzimCycle_p3 (EE_p3 u.2 E) x u.2 u.1) else u
      from rfl, if_neg h, if_pos (Or.inl h)]

/-- WRGCVDR.hl:1610 `FAN_IMP_FACE_MAP_PERMUTES_DARTS`. -/
theorem FAN_IMP_FACE_MAP_PERMUTES_DARTS {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) : permutesF_p3 (ffOfHyp_p3 x V E) (dartsOfHyp_p3 E V) := sorry

/-- WRGCVDR.hl:1779 `FAN_IMP_FIMITE_DARTS`. -/
theorem FAN_IMP_FIMITE_DARTS {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E) :
    (dartsOfHyp_p3 E V).Finite := by
  have hprod : (V ×ˢ V).Finite := hfan.2.2.1.1.prod hfan.2.2.1.1
  refine hprod.subset ?_
  intro p hp
  obtain ⟨h1, h2⟩ := IN_DARTS_HYP_IMP_FST_SND_IN_V hfan.1 hp
  exact ⟨h1, h2⟩

/-- WRGCVDR.hl:1802 `FAN_IMP_EE_EQ_SET_OF_EDGE`. -/
theorem FAN_IMP_EE_EQ_SET_OF_EDGE {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (v : V3) : EE_p3 v E = setOfEdge v V E :=
  UNI_E_IMP_EE_EQ_SET_OF_EDGE hfan.1 v

/-- WRGCVDR.hl:1809 `FAN_IMP_IN_SELF_PAIRS_IFF_FF_OF_HYP`. -/
theorem FAN_IMP_IN_SELF_PAIRS_IFF_FF_OF_HYP {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) (y : V3 × V3) :
    y ∈ selfPairs_p3 E V ↔ ffOfHyp_p3 x V E y ∈ selfPairs_p3 E V := sorry

/-- WRGCVDR.hl:1846 `FIRST_AAUHTVE`: under `FAN`, the components of `HYP`
carry a hypermap structure with `e² = I`. -/
theorem FIRST_AAUHTVE {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E) :
    ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E ∧
      (H.edgeMap : V3 × V3 → V3 × V3) ∘ (H.edgeMap : V3 × V3 → V3 × V3) = id := sorry

/-- WRGCVDR.hl:1966 `HYP_LEMMA` (structure encoding: the tuple is realized
by an honest `Hypermap`). -/
theorem HYP_LEMMA {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E) :
    ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E := sorry

/-- WRGCVDR.hl:1986 `ELMS_OF_HYPERMAP_HYP` (component reading of
`hypermap (HYP (x,V,E))`). -/
theorem ELMS_OF_HYPERMAP_HYP {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E) :
    ∃ H : Hypermap (V3 × V3),
      HYP_p3 x V E = ((↑H.darts : Set (V3 × V3)),
        ((H.edgeMap : V3 × V3 → V3 × V3),
          ((H.nodeMap : V3 × V3 → V3 × V3), (H.faceMap : V3 × V3 → V3 × V3)))) := sorry

/-- WRGCVDR.hl:2030 `iter_sigma_fan_in_set_of_edge`. -/
theorem iter_sigma_fan_in_set_of_edge {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {v u : V3} (hu : u ∈ setOfEdge v V E) (n : ℕ) :
    (sigmaFan x V E v)^[n] u ∈ setOfEdge v V E := by
  induction n with
  | zero => simpa using hu
  | succ k ih => rw [Function.iterate_succ_apply']; exact sigma_fan_in_setOfEdge hfan ih

/-! ## Orbits of the nn map; faces as orbits (WRGCVDR.hl:1995–2101,
2311–2360, 2503–2616) -/

/-- WRGCVDR.hl:1995 `N_HYP_TO_AZIM_CYCLE_LEM`. -/
theorem N_HYP_TO_AZIM_CYCLE_LEM {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {u v : V3} (_huv : (u, v) ∈ dartsOfHyp_p3 E V) (n : ℕ) :
    (nnOfHyp_p3 x V E)^[n] (u, v) = (u, (azimCycle_p3 (EE_p3 u E) x u)^[n] v) := sorry

/-- WRGCVDR.hl:2044 `ITER_AZIM_CYCLE_EQ_ITER_SIGMA`. -/
theorem ITER_AZIM_CYCLE_EQ_ITER_SIGMA {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {v u : V3} (_hv : {v, u} ∈ E) (a : V3) (_ha : a ∈ EE_p3 v E)
    (n : ℕ) :
    (azimCycle_p3 (EE_p3 v E) x v)^[n] a = (sigmaFan x V E v)^[n] a := sorry

/-- WRGCVDR.hl:2070 `pmp_to_iter`. -/
theorem pmp_to_iter (f : V3 → Set V3 → Set (Set V3) → V3 → V3 → V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) (v w : V3) (n : ℕ) :
    powerMapPoints_p3 f x V E v w n = (f x V E v)^[n] w := rfl

/-- WRGCVDR.hl:2080 `CYCLIC_SET_IMP_STABLE_SET2`. -/
theorem CYCLIC_SET_IMP_STABLE_SET2 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) {v u : V3} (_hv : {v, u} ∈ E) (a : V3) (_ha : a ∈ EE_p3 v E) :
    EE_p3 v E = {y | ∃ n : ℕ, y = (azimCycle_p3 (EE_p3 v E) x v)^[n] a} := sorry

/-- WRGCVDR.hl:2106 `FAN_IMP_BIJ_V_NODE_OF_HYP` (`∃`-rendering; the HOL
`f` is the stated pointwise function). -/
theorem FAN_IMP_BIJ_V_NODE_OF_HYP {x : V3} {V : Set V3} {E : Set (Set V3)}
    (_hfan : FAN x V E) :
    ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E ∧
      Set.BijOn
        (fun u : V3 =>
          if u ∈ V then H.node (u, chooseNdPoint_p3 u E V) else (∅ : Set (V3 × V3)))
        V ((fun y : V3 × V3 => H.node y) '' dartsOfHyp_p3 E V) := sorry

/-- WRGCVDR.hl:2311 `LOCAL_FAN_IMP_FF_SUBSET_DARTS`. -/
theorem LOCAL_FAN_IMP_FF_SUBSET_DARTS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : localFan_p3 V E FF) : FF ⊆ dartsOfHyp_p3 E V := by
  obtain ⟨H, hd, -, -, -, -, ⟨x, hx, hFx⟩, -⟩ := h
  have hsub := H.face_subset_darts hx
  intro d hdF
  rw [hFx] at hdF
  rw [← hd]
  exact hsub hdF

/-- WRGCVDR.hl:2333 `LOCAL_IMP_FINITE_DARTS`. -/
theorem LOCAL_IMP_FINITE_DARTS {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p3 V E FF) : (dartsOfHyp_p3 E V).Finite := by
  obtain ⟨H, hd, -, -, -, -, -, -⟩ := h
  rw [← hd]
  exact H.darts.finite_toSet

/-- WRGCVDR.hl:2345 `LOCAL_FAN_FINITE_FF`. -/
theorem LOCAL_FAN_FINITE_FF {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p3 V E FF) : FF.Finite := by
  obtain ⟨H, hd, -, -, -, -, ⟨x, hx, hFx⟩, -⟩ := h
  have hsub := H.face_subset_darts hx
  refine (H.darts.finite_toSet).subset ?_
  rw [hFx]
  exact hsub

/-- WRGCVDR.hl:2362 `LOCAL_FAN_IMP_BIJ_FF_NODES` (`∃`-rendering). -/
theorem LOCAL_FAN_IMP_BIJ_FF_NODES {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_h : localFan_p3 V E FF) :
    ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 0 V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 0 V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 0 V E ∧
      Set.BijOn (fun y : V3 × V3 => H.node y) FF
        ((fun y : V3 × V3 => H.node y) '' dartsOfHyp_p3 E V) := sorry

/-- WRGCVDR.hl:2508 `NOT_IN_DARTS_NN_OF_HYP_POWER_IDE`. -/
theorem NOT_IN_DARTS_NN_OF_HYP_POWER_IDE (x : V3) (V : Set V3) (E : Set (Set V3))
    {y : V3 × V3} (h : y ∉ dartsOfHyp_p3 E V) :
    ∀ n : ℕ, (nnOfHyp_p3 x V E)^[n] y = y := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [show nnOfHyp_p3 x V E y =
      if y ∈ dartsOfHyp_p3 E V then (y.1, azimCycle_p3 (EE_p3 y.1 E) x y.1 y.2) else y from rfl,
      if_neg h]

/-- WRGCVDR.hl:2519 `IN_NODE_IMP_FIRST_EQ` (given the fan hypermap). -/
theorem IN_NODE_IMP_FIRST_EQ {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E)
    {H : Hypermap (V3 × V3)}
    (_hd : (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V)
    (_he : (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E)
    (_hn : (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E)
    (_hf : (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E)
    {a b : V3 × V3} (_ha : a ∈ H.node b) : a.1 = b.1 := sorry

/-- WRGCVDR.hl:2548 `BIJ_BETWEEN_FF_AND_V` (fst maps faces bijectively to
vertices). -/
theorem BIJ_BETWEEN_FF_AND_V {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_h : localFan_p3 V E FF) : Set.BijOn (fun d : V3 × V3 => d.1) FF V := sorry

/-! ## WRGCVDR main theorem; localization defs; Definition 7.8 trichotomy
(WRGCVDR.hl:2622–2725, 2780–2863, 2868–2888, 2920–3328) -/

/-- WRGCVDR.hl:2622 `WRGCVDR` (the file's name theorem): on a local fan the
face-start map `hro` (with the two compatibility hypotheses) makes `V` an
`orbit_map` of itself. -/
theorem WRGCVDR {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_hlf : localFan_p3 V E FF) (hro : V3 → V3) :
    Set.BijOn (fun d : V3 × V3 => d.1) FF V ∧
      ((∀ x ∈ V, (x, hro x) ∈ FF) →
        (∀ x ∈ FF, x = (x.1, hro x.1)) →
        ∀ x ∈ V, V = orbitF_p3 hro x) := sorry

/-- WRGCVDR.hl:2780 `IMP_FAN_V_PRIME_E_PRIME`. -/
theorem IMP_FAN_V_PRIME_E_PRIME {v : V3} {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (_hfan : FAN v V E)
    (_hH : ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 v V E ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 v V E ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 v V E ∧
      ∃ x ∈ H.darts, FF = H.face x) :
    FAN v (vPrime_p3 V FF) (ePrime_p3 E FF) := sorry

/-- WRGCVDR.hl:2857 `E_PRIME_SUBSET_E`. -/
theorem E_PRIME_SUBSET_E (E : Set (Set V3)) (FF : Set (V3 × V3)) :
    ePrime_p3 E FF ⊆ E := by
  intro x he
  obtain ⟨v, w, rfl, hE, -⟩ := he
  exact hE

/-- WRGCVDR.hl:2868 `CYCLIC_MAP_IMP_CIRCLE_ITSELF`. -/
theorem CYCLIC_MAP_IMP_CIRCLE_ITSELF {α : Type*} {f : α → α} {W : Set α}
    (h : ∀ x ∈ W, W = orbitF_p3 f x) {y : α} (hy : y ∈ W) : ∃ x ∈ W, y = f x := by
  have h1 : f y ∈ W := by
    have hmem := IN_ORBIT_MAP_IMP_F_Y (f := f) (x := y) (y := y) (X_IN_ITS_ORBIT f y)
    rw [← h y hy] at hmem
    exact hmem
  have h2 : y ∈ orbitF_p3 f (f y) := by
    rw [← h (f y) h1]
    exact hy
  obtain ⟨n, hn⟩ := h2
  have hm : f^[n] y ∈ W := by
    rw [h y hy]
    exact ⟨n, rfl⟩
  refine ⟨f^[n] y, hm, ?_⟩
  symm
  rw [show f (f^[n] y) = f^[n + 1] y from (Function.iterate_succ_apply' f n y).symm,
    Function.iterate_succ_apply]
  exact hn

/-- WRGCVDR.hl:589 `DIH2K_IMP_PRE_SIMPLE_HYP`. -/
theorem DIH2K_IMP_PRE_SIMPLE_HYP {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (_hd : dih2k_p3 H k) (_hk : k ≠ 0) :
    ∀ x ∈ H.darts, (H.nodeMap : α → α) x ∉ H.face x := sorry

/-- WRGCVDR.hl:641 `DIH2K_IMP_SIMPLE_HYPERMAP`. -/
theorem DIH2K_IMP_SIMPLE_HYPERMAP {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (_hd : dih2k_p3 H k) (_hk : k ≠ 0) : H.Simple := sorry

/-- WRGCVDR.hl:717 `DIH_IMP_EVERY_NODE_INTER_FACE`. -/
theorem DIH_IMP_EVERY_NODE_INTER_FACE {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (_hd : dih2k_p3 H k) :
    ∀ x ∈ H.darts, ∀ y ∈ H.darts, ∃ d, d ∈ H.node x ∧ d ∈ H.face y := sorry

/-- WRGCVDR.hl:2920 `DIH2K_IMP_NODE_MAP_X_DIFF_X`. -/
theorem DIH2K_IMP_NODE_MAP_X_DIFF_X {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (_hd : dih2k_p3 H k) (_hk : k ≠ 0) :
    ∀ x ∈ H.darts, (H.nodeMap : α → α) x ≠ x := sorry

/-- WRGCVDR.hl:2938 `FAN7_SIMPLE`. -/
theorem FAN7_SIMPLE {V : Set V3} {E : Set (Set V3)} {x : V3} (h : fan7 x V E)
    (a b : V3) (ha : a ∈ V) (hb : b ∈ V) :
    affGe {x} ({a} : Set V3) ∩ affGe {x} ({b} : Set V3) =
      affGe {x} (({a} ∩ {b} : Set V3)) := by
  have h1 := h {a} (Set.mem_union_right _ ⟨a, ha, rfl⟩)
    {b} (Set.mem_union_right _ ⟨b, hb, rfl⟩)
  simpa using h1

/-- WRGCVDR.hl:2927 `FAN_IMP_NOT_EMPTY_DARTS`. -/
theorem FAN_IMP_NOT_EMPTY_DARTS {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) : dartsOfHyp_p3 E V ≠ ∅ := by
  have hvne : V ≠ ∅ := hfan.2.2.1.2
  obtain ⟨u, hu⟩ : V.Nonempty := by
    by_contra hnc
    exact hvne (Set.eq_empty_iff_forall_notMem.mpr fun w hw => hnc ⟨w, hw⟩)
  by_cases hE : EE_p3 u E = ∅
  · intro hEq
    have hm : (u, u) ∈ dartsOfHyp_p3 E V := Set.mem_union_right _ ⟨rfl, hu, hE⟩
    rw [hEq] at hm
    exact absurd hm (fun hc => hc)
  · obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hE
    have hwo : {u, w} ∈ E := hw
    intro hEq
    have hm : (u, w) ∈ dartsOfHyp_p3 E V := Set.mem_union_left _ hwo
    rw [hEq] at hm
    exact absurd hm (fun hc => hc)

/-- WRGCVDR.hl:2948 `FAN_IMP_DIFF`. -/
theorem FAN_IMP_DIFF {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E) :
    ∀ v ∈ (V ∪ ⋃₀ E), v ≠ x := by
  intro v hv
  rcases (Set.mem_union _ _ _).mp hv with h | h
  · intro he
    subst he
    exact hfan.2.2.2.1 h
  · intro he
    subst he
    exact hfan.2.2.2.1 (hfan.1 h)

/-! ## Affine-sign lemmas and the generic/circular/lunar trichotomy
(WRGCVDR.hl:2954–3328) -/

/-- WRGCVDR.hl:2954 `AFF_GE_TO_AFF_GT2_GE1`. -/
theorem AFF_GE_TO_AFF_GT2_GE1 {x u v : V3} (hu : u ≠ x) (hv : v ≠ x) :
    affGe {x} {u, v} = affGt {x} {u, v} ∪ affGe {x} {u} ∪ affGe {x} {v} := sorry

/-- WRGCVDR.hl:3011 `AFF_GE_INTER_AFF_LT_IMP_NOT_EQ_COL`. -/
theorem AFF_GE_INTER_AFF_LT_IMP_NOT_EQ_COL {u v : V3} (hv : v ≠ 0) (hu : u ≠ 0)
    (hne : affGe {0} {v} ∩ affLt {0} {u} ≠ ∅) :
    u ≠ v ∧ Collinear3 0 u v := sorry

/-- WRGCVDR.hl:3056 `CIZMRRH`: a local fan is generically placed, or
circular, or lunar — exclusively. -/
theorem CIZMRRH {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_hlf : localFan_p3 V E FF) :
    generic_p3 V E ∧ ¬(circular_p3 V E ∨ ∃ v w, lunar_p3 (v, w) V E) ∨
      circular_p3 V E ∧ ¬(generic_p3 V E ∨ ∃ v w, lunar_p3 (v, w) V E) ∨
      (∃ v w, lunar_p3 (v, w) V E) ∧ ¬(generic_p3 V E ∨ circular_p3 V E) := sorry

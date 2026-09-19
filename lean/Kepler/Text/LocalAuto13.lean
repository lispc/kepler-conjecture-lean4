/-
LocalAuto13: port of `scripts/local/YXIONXL2.hl` (Flyspeck "Local Fan"
appendix continuation, Hoang Le Truong, 2012-04-01; 3528 lines, 0 defs +
105 theorems — `SUM_AZIM_SYM_0` is stated twice, src:1361 and src:1371,
with a verbatim-identical body; ported once).

FILE MAP
  Section 0 (`_p13` copies, each with a NEEDS marker): the scs_v39 record
  lane (`ScsV39P13`, `isScsV39P13`, the BB*/MM* minimality tower,
  `scsOppV39P13`, `scsArrowV39P13`, `subdivV39P13`), the periodic kit
  (`PeriodicP13`, `Periodic2P13`, `peroppP13`, `peropp2P13`), the tau kit
  (`rhoFunP13`, `tau3P13`, `tauFunP13`), the local-fan skeleton
  (`localFanP13`, `ConvexLocalFanP13`), and the hypermap-of-HYP kit
  signatures (`eeP13`, `ordPairsP13`, `selfPairsP13`, `dartsOfHypP13`,
  `azimCycleP13`, `ivsAzimCycleP13`, `ffOfHypP13`, `nnOfHypP13`,
  `eeOfHypP13`, `hypFaceP13`).
  Sections 1-5: the 105 theorems in source order.  Mechanical image /
  pair / mod lemmas are PROVED; the scs / hypermap / azim giants keep
  `sorry` (DISCHARGES convention, like LocalAuto1's `*_concl` items).

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `vec 0` <-> `0`; `--x` <-> `-x`;
    `IMAGE` <-> `Set.image`/`''`; `CARD` <-> `Nat.card`; `POWER n` /
    `ITER n` <-> `Function.iterate` (`f^[n]`); `SUC n` <-> `n + 1`;
    `dist`/`norm` verbatim; NO `native_decide` anywhere.
  - HOL `linear f` (additivity + scalar compat) is rendered as the explicit
    conjunction in `LINAER_SYM_0_p13`; HOL `collinear` <-> `Collinear ℝ`;
    HOL `graph` <-> `Kepler.Text.Fan.Graph`; `FAN` <-> `Kepler.Text.Fan.FAN`;
    `ball_annulus` <-> `ballAnnulus` (PackingAuto2); `sum` <-> `setSum`.
  - Name plan: every declaration carries the `_p13` suffix because the
    canonical owners (LocalAuto1 scs record lane, LocalAuto2-12, and the
    hypermap-of-HYP foundation deferred with `hypermapOfFan`, Fan.lean head
    note) are parallel-in-flight and must NOT be imported yet.  Each
    `_p13` block names its future import; LocalAuto1-derived bodies are
    verbatim copies.  The `darts_of_hyp`-kit bodies (`ord_pairs`,
    `self_pairs`, `azim_cycle`, `ivs_azim_cycle`, `ff_of_hyp`, `nn_of_hyp`,
    `ee_of_hyp`) are summarized from the source proofs and marked
    NEEDS-VERIFY for the upstream lane: `ORD_PAIRS_E_VV` (no hypotheses)
    forces `ord_pairs` WITHOUT a `v ≠ w` guard, and `SELF_PAIR_EMPTY_VV`
    (no hypotheses, proof witnesses `vv (SUC x)` against `EE v E`) forces
    the `EE v E = ∅` (isolated-vertex) reading of `self_pairs`.
  - `cstab` is copied as `cstabP13` (NEEDS LocalAuto1); `h0`/`sol0`/
    `setSum`/`ballAnnulus`/`wedgeGe` come from PackingAuto2 (importable);
    `dihV` from Kepler.Geom.LuneVolume; `azim`/`Collinear` from Kepler.Geom.
  - The recurring SCS-block hypothesis
    `scs_k_v39 s = k /\ IMAGE vv (:num) = V /\ ... /\ is_scs_v39 s /\
    ~(k <= 3) /\ BBs_v39 s vv` is kept conjunct-by-conjunct, with the
    structure projection `s.k` for `scs_k_v39 s`.

DISCHARGES: nothing yet; the `sorry` bodies are the registry (same
convention as LocalAuto1's `*_concl` items).
FILL ROUND (2026-09-19): 47 -> 43 sorries.  Proved `EE_SYM_0_p13` and
`SUM_PAIR_SYM_0_p13` (negation transports two-point sets / the neg-pair
involution reindexes `setSum`), `COLLINEAR_SYM_0_p13` +
`COLLINEAR_POINT_SYM_0_p13` (`collinear_iff_of_mem` with negated anchors).
NOTE: `POINT_IN_AFF_LT_SYM_0_p13` is unprovable as stated (counterexample
`w2 = 0`, `v1 ≠ 0`: the weight conditions force `f w2 < 0` with `w2` in the
base set, making `∑ f = 1` and vector `0` incompatible); the HOL source
presumably assumes `w2 ≠ 0` — left `sorry` with this note.
-/

import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Geom.LuneVolume
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Section 0: `_p13` copies of the parallel-in-flight dependencies -/

-- NEEDS: LocalAuto1 `Periodic` (OXLZLEZ1.hl:59; universe-polymorphic).
def PeriodicP13 {α : Sort u} (f : ℕ → α) (n : ℕ) : Prop := ∀ i, f (i + n) = f i

-- NEEDS: LocalAuto1 `Periodic2` (appendix.hl:349).
def Periodic2P13 {α : Sort u} (f : ℕ → ℕ → α) (n : ℕ) : Prop :=
  ∀ i j, f (i + n) j = f i j ∧ f i (j + n) = f i j

-- NEEDS: LocalAuto1 `peropp` (appendix.hl:199).
def peroppP13 {α : Sort u} (f : ℕ → α) (k : ℕ) (i : ℕ) : α := f (k - (i % k + 1))

-- NEEDS: LocalAuto1 `peropp2` (appendix.hl:201).
def peropp2P13 {α : Sort u} (f : ℕ → ℕ → α) (k i j : ℕ) : α :=
  f (k - (i % k + 1)) (k - (j % k + 1))

-- NEEDS: LocalAuto1 `cstab` (appendix-lane shared constant).
def cstabP13 : ℝ := 3.01

/-- HOL `EE v E` (localization.hl:38): the neighbours of `v` along the
edge set `S`. -/
def eeP13 (v : V3) (S : Set (Set V3)) : Set V3 := {w | {v, w} ∈ S}

/-- NEEDS-VERIFY: HOL `ord_pairs` (Hypermap.hl); guard-free reading forced
by the unconditional source theorem `ORD_PAIRS_E_VV`. -/
def ordPairsP13 (E : Set (Set V3)) : Set (V3 × V3) := {p | {p.1, p.2} ∈ E}

/-- NEEDS-VERIFY: HOL `self_pairs` (Hypermap.hl); the proof of
`SELF_PAIR_EMPTY_VV` witnesses `vv (SUC x)` as a member of `EE v E`, which
forces the isolated-vertex (`EE v E = ∅`) reading. -/
def selfPairsP13 (E : Set (Set V3)) (V : Set V3) : Set (V3 × V3) :=
  {p | p.1 = p.2 ∧ p.1 ∈ V ∧ eeP13 p.1 E = ∅}

/-- HOL `darts_of_hyp` (Hypermap.hl). -/
def dartsOfHypP13 (E : Set (Set V3)) (V : Set V3) : Set (V3 × V3) :=
  ordPairsP13 E ∪ selfPairsP13 E V

/-- NEEDS-VERIFY: HOL `azim_cycle` (wrgcvdr_cizmrrh.hl): the fan-successor
choice with junk `u` when `u` is not a neighbour, and on a singleton
neighbourhood. -/
noncomputable def azimCycleP13 (Ev : Set V3) (x v u : V3) : V3 :=
  if u ∉ Ev then u
  else if Ev = {u} then u
  else
    Classical.epsilon fun w => w ∈ Ev ∧ w ≠ u ∧
      ∀ w1 ∈ Ev, w1 ≠ u → azim x v u w ≤ azim x v u w1

/-- NEEDS-VERIFY: HOL `ivs_azim_cycle` (wrgcvdr_cizmrrh.hl): the inverse
fan-successor choice. -/
noncomputable def ivsAzimCycleP13 (Ev : Set V3) (x v u : V3) : V3 :=
  Classical.epsilon fun w => azimCycleP13 Ev x v w = u

/-- NEEDS-VERIFY: HOL `ff_of_hyp` (Hypermap.hl): the face map
`(v,w) ↦ (v, azim_cycle (EE v E) x v w)` on darts, junk identity off the
dart set. -/
noncomputable def ffOfHypP13 (x : V3) (V : Set V3) (E : Set (Set V3))
    (d : V3 × V3) : V3 × V3 :=
  if d ∈ dartsOfHypP13 E V then (d.1, azimCycleP13 (eeP13 d.1 E) x d.1 d.2)
  else d

/-- NEEDS-VERIFY: HOL `nn_of_hyp` (Hypermap.hl): the node map
`(v,w) ↦ (ivs_azim_cycle (EE w E) x w v, w)` on darts. -/
noncomputable def nnOfHypP13 (x : V3) (V : Set V3) (E : Set (Set V3))
    (d : V3 × V3) : V3 × V3 :=
  if d ∈ dartsOfHypP13 E V then (ivsAzimCycleP13 (eeP13 d.2 E) x d.2 d.1, d.2)
  else d

/-- NEEDS-VERIFY: HOL `ee_of_hyp` (Hypermap.hl): the edge map
`(v,w) ↦ (w, azim_cycle (EE w E) x w v)` on darts. -/
noncomputable def eeOfHypP13 (x : V3) (V : Set V3) (E : Set (Set V3))
    (d : V3 × V3) : V3 × V3 :=
  if d ∈ dartsOfHypP13 E V then (d.2, azimCycleP13 (eeP13 d.2 E) x d.2 d.1)
  else d

/-- HOL `face (hypermap (HYP (x,V,E))) d`: the `ff` orbit
(Hypermap.lean `orbitMap` convention). -/
def hypFaceP13 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    Set (V3 × V3) := {y | ∃ n : ℕ, (ffOfHypP13 x V E)^[n] d = y}

-- NEEDS: LocalAuto1 `rho_fun` (appendix.hl:80).
noncomputable def rhoFunP13 (y : ℝ) : ℝ :=
  1 + (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (y - 2)

-- NEEDS: LocalAuto1 `rho` (sphere.hl local copy).
noncomputable def rhoP13 (y : ℝ) : ℝ :=
  1 + (y - 2) * (sol0 / Real.pi) / (2 * h0 - 2)

-- NEEDS: LocalAuto1 `azim_in_fan` (localization.hl:74).
noncomputable def azimInFanP13 (e : V3 × V3) (E : Set (Set V3)) : ℝ :=
  if 1 < (eeP13 e.1 E).ncard then azim 0 e.1 e.2 (sigmaFan 0 Set.univ E e.1 e.2)
  else 2 * Real.pi

-- NEEDS: LocalAuto1 `wedge_in_fan_ge` (localization.hl:88).
noncomputable def wedgeInFanGeP13 (e : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (eeP13 e.1 E).ncard then wedgeGe 0 e.1 e.2 (sigmaFan 0 Set.univ E e.1 e.2)
  else Set.univ

-- NEEDS: LocalAuto1 `local_fan` skeleton (WRGCVDR.hl:144).
def localFanP13 (_V : Set V3) (_E : Set (Set V3)) (_FF : Set (V3 × V3)) : Prop :=
  True

-- NEEDS: LocalAuto1 `convex_local_fan` (localization.hl:92).
def ConvexLocalFanP13 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  localFanP13 V E FF ∧ ∀ x ∈ FF, azimInFanP13 x E ≤ Real.pi ∧ V ⊆ wedgeInFanGeP13 x E

-- NEEDS: LocalAuto1 `tau_fun` (appendix.hl:96).
noncomputable def tauFunP13 (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) :
    ℝ :=
  setSum f (fun e => rhoFunP13 (norm e.1) * azimInFanP13 e E) -
    (Real.pi + sol0) * ((f.ncard - 2 : ℕ) : ℝ)

-- NEEDS: LocalAuto1 `tau3` (appendix.hl:98).
noncomputable def tau3P13 (v1 v2 v3 : V3) : ℝ :=
  rhoP13 (norm v1) * dihV 0 v1 v2 v3 + rhoP13 (norm v2) * dihV 0 v2 v3 v1 +
    rhoP13 (norm v3) * dihV 0 v3 v1 v2 - (Real.pi + sol0)

-- NEEDS: LocalAuto1 `ScsV39` record (appendix.hl:216-228, the 10-tuple
-- `(k,d,a,alpha,beta,b,J,lo,hi,str)` under `new_type_definition`).
structure ScsV39P13 where
  k : ℕ
  d : ℝ
  a : ℕ → ℕ → ℝ
  am : ℕ → ℕ → ℝ
  bm : ℕ → ℕ → ℝ
  b : ℕ → ℕ → ℝ
  J : ℕ → ℕ → Prop
  lo : ℕ → Prop
  hi : ℕ → Prop
  str : ℕ → Prop
  deriving Inhabited

-- NEEDS: LocalAuto1 `is_scs_v39` (appendix.hl:354; duplicated `periodic
-- ... str` conjunct verbatim).
def isScsV39P13 (s : ScsV39P13) : Prop :=
  s.d < 0.9 ∧
  3 ≤ s.k ∧
  s.k ≤ 6 ∧
  PeriodicP13 s.lo s.k ∧
  PeriodicP13 s.hi s.k ∧
  PeriodicP13 s.str s.k ∧
  PeriodicP13 s.str s.k ∧
  Periodic2P13 s.a s.k ∧
  Periodic2P13 s.am s.k ∧
  Periodic2P13 s.bm s.k ∧
  Periodic2P13 s.b s.k ∧
  Periodic2P13 s.J s.k ∧
  (∀ i j, s.a i j = s.a j i ∧ s.am i j = s.am j i ∧
    s.bm i j = s.bm j i ∧ s.b i j = s.b j i ∧ s.J i j = s.J j i) ∧
  (∀ i j, s.a i j ≤ s.am i j ∧ s.am i j ≤ s.bm i j ∧ s.bm i j ≤ s.b i j) ∧
  (∀ i, s.a i i = 0) ∧
  (∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j) ∧
  (∀ i, s.k = 3 → s.b i (i + 1) < 4) ∧
  (∀ i, 3 < s.k → s.b i (i + 1) ≤ cstabP13) ∧
  (∀ i j, s.J i j → j % s.k = (i + 1) % s.k ∨ i % s.k = (j + 1) % s.k) ∧
  (∀ i j, s.J i j → s.a i j = Real.sqrt 8 ∧ s.b i j = cstabP13) ∧
  {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.ncard + s.k ≤ 6

-- NEEDS: LocalAuto1 `unadorned_v39` (appendix.hl:384).
def unadornedV39P13 (s : ScsV39P13) : Prop :=
  s.lo = (fun _ => False : ℕ → Prop) ∧ s.hi = (fun _ => False : ℕ → Prop) ∧
    s.str = (fun _ => False : ℕ → Prop) ∧ s.a = s.am ∧ s.b = s.bm

-- NEEDS: LocalAuto1 `mk_unadorned_v39` (appendix.hl:448).
def mkUnadornedV39P13 (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ) : ScsV39P13 :=
  ScsV39P13.mk k d a a b b (fun _ _ => False) (fun _ => False : ℕ → Prop)
    (fun _ => False : ℕ → Prop) (fun _ => False : ℕ → Prop)

-- NEEDS: LocalAuto1 `is_ear_v39` (appendix.hl:408).
def isEarV39P13 (s : ScsV39P13) : Prop :=
  isScsV39P13 s ∧ unadornedV39P13 s ∧ s.k = 3 ∧ s.d = 0.11 ∧
  (∀ i, s.b i i = 0) ∧
  ∃ i, {j | j < 3 ∧ s.J j (j + 1)} = {i} ∧
    s.a i (i + 1) = Real.sqrt 8 ∧ s.b i (i + 1) = cstabP13 ∧
    (∀ j, j < 3 ∧ j ≠ i → s.a j (j + 1) = 2 ∧ s.b j (j + 1) = 2 * h0)

-- NEEDS: LocalAuto1 `BBs_v39` (appendix.hl:418).
def BBsV39P13 (s : ScsV39P13) (vv : ℕ → V3) : Prop :=
  Set.range vv ⊆ ballAnnulus ∧
  PeriodicP13 vv s.k ∧
  (∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j) ∧
  (s.k ≤ 3 ∨ ConvexLocalFanP13 (Set.range vv)
    (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))

-- NEEDS: LocalAuto1 `dsv_v39` (appendix.hl:427).
noncomputable def dsvV39P13 (s : ScsV39P13) (vv : ℕ → V3) : ℝ :=
  s.d + 0.1 * (if isEarV39P13 s then 1 else -1) *
    setSum {i | i < s.k ∧ s.J i (i + 1)}
      (fun i => cstabP13 - dist (vv i) (vv (i + 1)))

-- NEEDS: LocalAuto1 `taustar_v39` (appendix.hl:441).
noncomputable def taustarV39P13 (s : ScsV39P13) (vv : ℕ → V3) : ℝ :=
  if s.k ≤ 3 then tau3P13 (vv 0) (vv 1) (vv 2) - dsvV39P13 s vv
  else
    tauFunP13 (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) - dsvV39P13 s vv

-- NEEDS: LocalAuto1 `min_num` (LEAST via choice; junk on `∅`).
noncomputable def minNumP13 (S : Set ℕ) : ℕ :=
  Classical.epsilon fun n => n ∈ S ∧ ∀ m ∈ S, n ≤ m

-- NEEDS: LocalAuto1 `BBprime_v39` (appendix.hl:656).
def BBprimeV39P13 (s : ScsV39P13) : Set (ℕ → V3) :=
  {vv | BBsV39P13 s vv ∧
    (∀ ww, BBsV39P13 s ww → taustarV39P13 s vv ≤ taustarV39P13 s ww) ∧
    taustarV39P13 s vv < 0}

-- NEEDS: LocalAuto1 `BBindex_v39` (appendix.hl:659).
noncomputable def BBindexV39P13 (s : ScsV39P13) (vv : ℕ → V3) : ℕ :=
  {i | i < s.k ∧ s.a i (i + 1) = dist (vv i) (vv (i + 1))}.ncard

-- NEEDS: LocalAuto1 `BBindex_min_v39` (appendix.hl:662).
noncomputable def BBindexMinV39P13 (s : ScsV39P13) : ℕ :=
  minNumP13 (BBindexV39P13 s '' BBprimeV39P13 s)

-- NEEDS: LocalAuto1 `BBprime2_v39` (appendix.hl:665).
def BBprime2V39P13 (s : ScsV39P13) : Set (ℕ → V3) :=
  {vv | vv ∈ BBprimeV39P13 s ∧ BBindexV39P13 s vv = BBindexMinV39P13 s}

-- NEEDS: LocalAuto1 `MMs_v39` (appendix.hl:668).
def MMsV39P13 (s : ScsV39P13) : Set (ℕ → V3) :=
  {vv | vv ∈ BBprime2V39P13 s ∧
    (∀ i, s.str i → azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) = Real.pi) ∧
    (∀ i, s.lo i → norm (vv i) = 2) ∧
    (∀ i, s.hi i → norm (vv i) = 2 * h0) ∧
    (∀ i j, s.am i j ≤ dist (vv i) (vv j)) ∧
    (∀ i j, dist (vv i) (vv j) ≤ s.bm i j)}

-- NEEDS: LocalAuto1 `scs_arrow_v39` (appendix.hl:804).
def scsArrowV39P13 (S1 S2 : Set ScsV39P13) : Prop :=
  (∀ s ∈ S2, isScsV39P13 s) ∧
    ((∀ s ∈ S1, MMsV39P13 s = ∅) ∨ ∃ s ∈ S2, MMsV39P13 s ≠ ∅)

-- NEEDS: LocalAuto1 `psort` (appendix.hl:455).
noncomputable def psortP13 (k : ℕ) (u : ℕ × ℕ) : ℕ × ℕ :=
  if u.1 % k ≤ u.2 % k then (u.1 % k, u.2 % k) else (u.2 % k, u.1 % k)

-- NEEDS: LocalAuto1 `override` (appendix.hl:479).
noncomputable def overrideP13 (a : ℕ → ℕ → ℝ) (k : ℕ) (u : ℕ × ℕ) (d : ℝ)
    (i j : ℕ) : ℝ :=
  if psortP13 k u = psortP13 k (i, j) then d else a i j

-- NEEDS: LocalAuto1 `restriction_cs1_v39` (appendix.hl:723).
noncomputable def restrictionCs1V39P13 (s : ScsV39P13) (p q : ℕ) (c : ℝ) : ScsV39P13 :=
  let b1 := overrideP13 s.b s.k (p, q) c
  let bm := if c < s.bm p q then overrideP13 s.bm s.k (p, q) c else s.bm
  ScsV39P13.mk s.k s.d s.a s.am bm b1 s.J s.lo s.hi s.str

-- NEEDS: LocalAuto1 `restriction_cs2_v39` (appendix.hl:730).
noncomputable def restrictionCs2V39P13 (s : ScsV39P13) (p q : ℕ) (c : ℝ) : ScsV39P13 :=
  let a1 := overrideP13 s.a s.k (p, q) c
  let am := if s.am p q < c then overrideP13 s.am s.k (p, q) c else s.am
  ScsV39P13.mk s.k s.d a1 am s.bm s.b s.J s.lo s.hi s.str

-- NEEDS: LocalAuto1 `subdiv_v39` (appendix.hl:737).
noncomputable def subdivV39P13 (s : ScsV39P13) (p q : ℕ) (c : ℝ) : List ScsV39P13 :=
  if c ≤ s.a p q then [s]
  else if c ≤ s.am p q then [restrictionCs2V39P13 s p q c]
  else if c < s.bm p q then [restrictionCs1V39P13 s p q c, restrictionCs2V39P13 s p q c]
  else if c < s.b p q then [restrictionCs1V39P13 s p q c] else [s]

-- NEEDS: LocalAuto1 `scs_opp_v39` (appendix.hl:763).
def scsOppV39P13 (s : ScsV39P13) : ScsV39P13 :=
  ScsV39P13.mk s.k s.d (peropp2P13 s.a s.k) (peropp2P13 s.am s.k)
    (peropp2P13 s.bm s.k) (peropp2P13 s.b s.k) (peropp2P13 s.J s.k)
    (peroppP13 s.lo s.k) (peroppP13 s.hi s.k) (peroppP13 s.str s.k)

/-! ## Section 1: point/symmetry lemmas (src YXIONXL2.hl:83-333) -/

private theorem negInjP13 : Function.Injective (fun x : V3 => -x) :=
  fun _ _ h => by simpa using h

/-- pointwise-equal functions have equal images over `univ`. -/
private theorem imageUnivCongrP13 {α β} {f g : α → β} (h : ∀ i, f i = g i) :
    Set.image f Set.univ = Set.image g Set.univ :=
  congrArg (Set.image · Set.univ) (funext h)

/-- HOL `PERIODIC_PROPERTY`: periodicity transfers to residues. -/
private theorem periodicAddP13 {α : Sort u} {f : ℕ → α} {k : ℕ}
    (hper : PeriodicP13 f k) : ∀ q j, f (j + q * k) = f j := by
  intro q
  induction q with
  | zero => intro j; simp
  | succ n ih =>
      intro j
      have hsplit : j + Nat.succ n * k = j + n * k + k := by
        rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (n * k) k]
      rw [hsplit, hper, ih j]

private theorem periodicModP13 {α : Sort u} {f : ℕ → α} {k : ℕ}
    (hper : PeriodicP13 f k) (_hk : k ≠ 0) (j : ℕ) : f (j % k) = f j := by
  have h := periodicAddP13 hper (j / k) (j % k)
  rw [Nat.mul_comm] at h
  rw [Nat.mod_add_div j k] at h
  exact h.symm

/-- HOL `IN_SYM_0` (src:83). -/
theorem IN_SYM_0_p13 {a : V3} {A : Set V3} (h : a ∈ A) :
    -a ∈ Set.image (fun x : V3 => -x) A :=
  ⟨a, h, rfl⟩

/-- HOL `SUBSET_SYM_0` (src:89). -/
theorem SUBSET_SYM_0_p13 {A B : Set V3} (h : A ⊆ B) :
    Set.image (fun x : V3 => -x) A ⊆ Set.image (fun x : V3 => -x) B :=
  fun x hx => let ⟨y, hy, hyx⟩ := hx; ⟨y, h hy, hyx⟩

/-- HOL `SET_EQ_SYM_0` (src:96). -/
theorem SET_EQ_SYM_0_p13 {A B : Set V3} (h : A = B) :
    Set.image (fun x : V3 => -x) A = Set.image (fun x : V3 => -x) B := by rw [h]

/-- HOL `IMAGE_V_SYM_0` (src:105). -/
theorem IMAGE_V_SYM_0_p13 (vv : ℕ → V3) :
    Set.image (fun i : ℕ => -(vv i)) Set.univ
      = Set.image (fun x : V3 => -x) (Set.image vv Set.univ) := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨vv i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- HOL `UNIONS_IMAGE_FAN_SYM_0` (src:120). -/
theorem UNIONS_IMAGE_FAN_SYM_0_p13 (vv : ℕ → V3) :
    ⋃₀ (Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ)
      = Set.image (fun x : V3 => -x)
          (⋃₀ (Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ)) := by
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨i, -, rfl⟩ := ht
    rcases Set.mem_insert_iff.mp hx with rfl | rfl
    · exact ⟨vv i, ⟨{vv i, vv (i + 1)}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert _ _⟩, rfl⟩
    · exact ⟨vv (i + 1), ⟨{vv i, vv (i + 1)}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨t', ht', hy'⟩ := hy
    obtain ⟨i, -, rfl⟩ := ht'
    subst hyx
    rcases Set.mem_insert_iff.mp hy' with rfl | rfl
    · exact ⟨{-(vv i), -(vv (i + 1))}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert _ _⟩
    · exact ⟨{-(vv i), -(vv (i + 1))}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩

/-- HOL `FINITE_SYM_0` (src:159). -/
theorem FINITE_SYM_0_p13 {A : Set V3} (h : A.Finite) :
    (Set.image (fun x : V3 => -x) A).Finite := h.image _

/-- HOL `CARD_SYM_0` (src:162). -/
theorem CARD_SYM_0_p13 {A : Set V3} (h : A.Finite) :
    Nat.card (Set.image (fun x : V3 => -x) A) = Nat.card A :=
  Nat.card_image_of_injective negInjP13 A

/-- HOL `ELEMENT2_SYM_0` (src:169). -/
theorem ELEMENT2_SYM_0_p13 (a b : V3) :
    ({-a, -b} : Set V3) = Set.image (fun x : V3 => -x) ({a, b} : Set V3) := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, rfl⟩
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- HOL `GRAPH_SYM_0` (src:178); HOL `graph` <-> `Kepler.Text.Fan.Graph`
(every edge finite of card 2). -/
theorem GRAPH_SYM_0_p13 (vv : ℕ → V3)
    (h : Graph (Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ)) :
    Graph (Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ) := by
  intro e he
  obtain ⟨x, -, rfl⟩ := he
  obtain ⟨hf, hc⟩ := h {vv x, vv (x + 1)} ⟨x, Set.mem_univ _, rfl⟩
  have hne : vv x ≠ vv (x + 1) := by
    intro hcon
    have h1 : hf.toFinset.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      have ha' : a ∈ ({vv x, vv (x + 1)} : Set V3) := by simpa using ha
      have hb' : b ∈ ({vv x, vv (x + 1)} : Set V3) := by simpa using hb
      rw [hcon] at ha' hb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp
    omega
  have hne' : -(vv x) ≠ -(vv (x + 1)) := fun hcc => hne (by simpa using hcc)
  have hset : ({-(vv x), -(vv (x + 1))} : Set V3)
      = Set.image (fun y : V3 => -y) ({vv x, vv (x + 1)} : Set V3) := by
    rw [← ELEMENT2_SYM_0_p13]
  have hf2 : (Set.image (fun y : V3 => -y) ({vv x, vv (x + 1)} : Set V3)).Finite :=
    hf.image _
  have hfin : ({-(vv x), -(vv (x + 1))} : Set V3).Finite := by
    rw [hset]
    exact hf2
  have hcard : hfin.toFinset.card = 2 := by
    have h2 : ({vv x, vv (x + 1)} : Set V3).ncard = 2 :=
      (Set.ncard_eq_toFinset_card _ hf).trans hc
    have h3 : ({-(vv x), -(vv (x + 1))} : Set V3).ncard = 2 := by
      rw [hset, Set.ncard_image_of_injective _ negInjP13]
      exact h2
    exact (Set.ncard_eq_toFinset_card _ hfin).symm.trans h3
  exact ⟨hfin, hcard⟩

/-- HOL `NOT_SUBSET_EMPTY_SYM_0` (src:197). -/
theorem NOT_SUBSET_EMPTY_SYM_0_p13 {A : Set V3} (h : ¬(A ⊆ ∅)) :
    ¬(Set.image (fun x : V3 => -x) A ⊆ ∅) := by
  rw [Set.not_subset] at h ⊢
  obtain ⟨a, ha, -⟩ := h
  exact ⟨-a, IN_SYM_0_p13 ha, by simp⟩

/-- HOL `REFL_SYM_0` (src:204). -/
theorem REFL_SYM_0_p13 (A : Set V3) :
    Set.image (fun x : V3 => -x) (Set.image (fun x : V3 => -x) A) = A := by
  simp

/-- HOL `IMAGE_E_SYM_0` (src:216). -/
theorem IMAGE_E_SYM_0_p13 (vv : ℕ → V3) {e : Set V3}
    (h : e ∈ Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ) :
    Set.image (fun x : V3 => -x) e
      ∈ Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ := by
  obtain ⟨x, -, rfl⟩ := h
  have himg : Set.image (fun x : V3 => -x) {-(vv x), -(vv (x + 1))}
      = {vv x, vv (x + 1)} := by
    rw [← ELEMENT2_SYM_0_p13 (-(vv x)) (-(vv (x + 1)))]
    simp
  rw [himg]
  exact ⟨x, Set.mem_univ _, rfl⟩

/-- HOL `COLLINEAR_SYM_0` (src:233).
DISCHARGED: `collinear_iff_of_mem` at the negated anchor — the same
direction vector `v` works with negated coefficients (`-r • v +ᵥ -p₀`). -/
theorem COLLINEAR_SYM_0_p13 {e : Set V3} (h : Collinear ℝ e) :
    Collinear ℝ (Set.image (fun x : V3 => -x) e) := by
  by_cases he : e = ∅
  · rw [he, Set.image_empty]
    exact @collinear_empty ℝ V3 V3 _ _ _ _
  · obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr he
    rw [collinear_iff_of_mem (Set.mem_image_of_mem _ hp₀)]
    obtain ⟨v, hv⟩ := (collinear_iff_of_mem hp₀).mp h
    refine ⟨v, ?_⟩
    rintro p ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := hv x hx
    refine ⟨-r, ?_⟩
    have hx2 : (-x : V3) = -(r • v +ᵥ p₀) := by rw [hr]
    show (-x : V3) = (-r) • v +ᵥ (-p₀)
    rw [hx2, vadd_eq_add, vadd_eq_add]
    module
  -- NEEDS: Mathlib collinear-image transfer for the negation map.

/-- HOL `UNION_SYM_0` (src:248). -/
theorem UNION_SYM_0_p13 (s e : Set V3) :
    Set.image (fun x : V3 => -x) (s ∪ e)
      = Set.image (fun x : V3 => -x) s ∪ Set.image (fun x : V3 => -x) e :=
  Set.image_union _ _ _

/-- HOL `VEC0_SYM_0` (src:252). -/
theorem VEC0_SYM_0_p13 :
    Set.image (fun x : V3 => -x) ({0} : Set V3) = ({0} : Set V3) := by
  ext x
  simp

/-- HOL `VEC0_UNION_SYM_0` (src:262). -/
theorem VEC0_UNION_SYM_0_p13 (e : Set V3) :
    Set.image (fun x : V3 => -x) (({0} : Set V3) ∪ e)
      = ({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e := by
  rw [UNION_SYM_0_p13, VEC0_SYM_0_p13]

/-- HOL `NOT_COLLINEAR_SYM_0` (src:266). -/
theorem NOT_COLLINEAR_SYM_0_p13 {e : Set V3} (h : ¬Collinear ℝ e) :
    ¬Collinear ℝ (Set.image (fun x : V3 => -x) e) := fun hc =>
  h (by rw [← REFL_SYM_0_p13 e]; exact COLLINEAR_SYM_0_p13 hc)

/-- HOL `VEC0_NOT_COLLINEAR_SYM_0` (src:273). -/
theorem VEC0_NOT_COLLINEAR_SYM_0_p13 {e : Set V3}
    (h : ¬Collinear ℝ (({0} : Set V3) ∪ e)) :
    ¬Collinear ℝ (({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e) := fun hc =>
  h (by
    have h1 := COLLINEAR_SYM_0_p13 hc
    rw [UNION_SYM_0_p13, VEC0_SYM_0_p13, REFL_SYM_0_p13 e] at h1
    exact h1)

/-- HOL `IMAGE_E_UNION_V_SYM_0` (src:279); the singleton-set families are
rendered as images of the point map. -/
theorem IMAGE_E_UNION_V_SYM_0_p13 (vv : ℕ → V3) {e : Set V3}
    (h : e ∈ Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ
      ∪ Set.image (fun v : V3 => {v}) (Set.range fun i => -(vv i))) :
    Set.image (fun x : V3 => -x) e
      ∈ Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ
        ∪ Set.image (fun v : V3 => {v}) (Set.range vv) := by
  rcases h with h | h
  · exact Or.inl (IMAGE_E_SYM_0_p13 vv h)
  · obtain ⟨y, ⟨i, rfl⟩, rfl⟩ := h
    refine Or.inr ⟨vv i, ⟨i, rfl⟩, ?_⟩
    rw [Set.image_singleton]
    simp

/-- HOL `LINAER_SYM_0` (src:304; HOL `linear f` rendered as the explicit
additivity + scalar-compat conjunction). -/
theorem LINAER_SYM_0_p13 :
    (∀ x y : V3, -(x + y) = -x + -y) ∧ ∀ (c : ℝ) (x : V3), -(c • x) = c • -x :=
  ⟨fun _ _ => by rw [neg_add], fun _ _ => by simp⟩

/-- HOL `INTER_SYM_0` (src:330). -/
theorem INTER_SYM_0_p13 (e1 e2 : Set V3) :
    Set.image (fun x : V3 => -x) (e1 ∩ e2)
      = Set.image (fun x : V3 => -x) e1 ∩ Set.image (fun x : V3 => -x) e2 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨⟨y, hy1, rfl⟩, ⟨y, hy2, rfl⟩⟩
  · rintro ⟨⟨y1, hy1, rfl⟩, ⟨y2, hy2, hy12⟩⟩
    have hyy : y1 = y2 := neg_inj.mp hy12.symm
    exact ⟨y1, ⟨hy1, hyy ▸ hy2⟩, rfl⟩

/-! ## Section 2: arithmetic of the opposite index (src:381-433, 570-594) -/

/-- HOL `OPP_SUC_MOD` (src:381). -/
theorem OPP_SUC_MOD_p13 {k x : ℕ} (hk : k ≠ 0) :
    k - ((k - (x % k + 1)) % k + 1) = x % k := by
  have h1 : x % k < k := Nat.mod_lt x (Nat.pos_of_ne_zero hk)
  have h2 : (k - (x % k + 1)) % k = k - (x % k + 1) := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  omega

/-- HOL `periodic` residue transfer used by the OPP_IMAGE lemmas. -/
theorem PERIODIC_PROPERTY_p13 {α : Sort u} {f : ℕ → α} {k : ℕ}
    (hper : PeriodicP13 f k) (hk : k ≠ 0) (j : ℕ) : f (j % k) = f j :=
  periodicModP13 hper hk j

/-- HOL `OPP_IMAGE_V_EQ` (src:396). -/
theorem OPP_IMAGE_V_EQ_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : k ≠ 0) :
    Set.image (fun i : ℕ => vv (k - (i % k + 1))) Set.univ
      = Set.image vv Set.univ := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨k - (i % k + 1), rfl⟩
  · rintro ⟨j, rfl⟩
    have hjk : j % k < k := Nat.mod_lt j (Nat.pos_of_ne_zero hk)
    have h1 : (k - (j % k + 1)) % k = k - (j % k + 1) := Nat.mod_eq_of_lt (by omega)
    have h2 : k - ((k - (j % k + 1)) % k + 1) = j % k := OPP_SUC_MOD_p13 hk
    rw [h1] at h2
    exact ⟨k - (j % k + 1), by rw [h1, h2, PERIODIC_PROPERTY_p13 hper hk j]⟩

/-- HOL `MOD_SUC_MOD` (src:412). -/
theorem MOD_SUC_MOD_p13 {k x : ℕ} (hk : 1 < k) :
    (x % k + 1) % k = (x + 1) % k := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [show (x + 1) % k = (x % k + 1 % k) % k from Nat.add_mod x 1 k, h1]

/-- HOL `SUC_MOD_EQ_MOD_SUC` (src:420; `k - SUC x MOD k` parses as
`k - ((x+1) % k)` in the source). -/
theorem SUC_MOD_EQ_MOD_SUC_p13 {k x : ℕ} (hk : 1 < k) :
    (k - (x % k + 1)) % k = (k - ((x + 1) % k)) % k := by
  have h1 : x % k < k := Nat.mod_lt x (by omega)
  by_cases hlt : x % k + 1 < k
  · rw [(MOD_SUC_MOD_p13 (x := x) hk).symm, Nat.mod_eq_of_lt hlt]
  · have heq : x % k + 1 = k := by omega
    have h0 : (x + 1) % k = 0 := by
      rw [(MOD_SUC_MOD_p13 (x := x) hk).symm, heq, Nat.mod_self]
    rw [heq, Nat.sub_self, Nat.zero_mod, h0, Nat.sub_zero, Nat.mod_self]

/-- 2-element sets commute. -/
private theorem pairEqSwapP13 {a b : V3} : ({a, b} : Set V3) = {b, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- 2-element sets are equal iff their entries match up (either way). -/
private theorem pairSetEqP13 {a b c d : V3} :
    ({a, b} : Set V3) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h1 : a ∈ ({c, d} : Set V3) := by rw [← h]; simp
    have h2 : b ∈ ({c, d} : Set V3) := by rw [← h]; simp
    have h3 : d ∈ ({a, b} : Set V3) := by rw [h]; simp
    have h4 : c ∈ ({a, b} : Set V3) := by rw [h]; simp
    rcases Set.mem_insert_iff.mp h1 with hac | had
    · rcases Set.mem_insert_iff.mp h2 with hbc | hbd
      · rcases Set.mem_insert_iff.mp h3 with hda | hdb
        · exact Or.inr ⟨hda.symm, hbc⟩
        · exact Or.inl ⟨hac, hdb.symm⟩
      · exact Or.inl ⟨hac, hbd⟩
    · rcases Set.mem_insert_iff.mp h2 with hbc | hbd
      · exact Or.inr ⟨had, hbc⟩
      · rcases Set.mem_insert_iff.mp h4 with hca | hcb
        · exact Or.inl ⟨hca.symm, hbd⟩
        · exact Or.inr ⟨had, hcb.symm⟩
  · rintro (h | h)
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- HOL `OPP_IMAGE_E_EQ` (src:439); `SUC (SUC i MOD k)` renders as
`(i + 1) % k` and the unordered edge pairs are `Set V3` doubletons. -/
theorem OPP_IMAGE_E_EQ_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ => ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
        Set.univ
      = Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ := by
  have hk0 : (0:ℕ) < k := by omega
  have hv0 : vv k = vv 0 := by
    have h := hper 0
    rwa [Nat.zero_add] at h
  have key : ∀ j, j < k → ({vv j, vv (j + 1)} : Set V3)
      ∈ Set.image
          (fun i : ℕ => ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
          Set.univ := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) k with hlt | heq
    · refine ⟨k - (j + 2), Set.mem_univ _, ?_⟩
      show ({vv (k - ((k - (j + 2)) % k + 1)),
             vv (k - ((k - (j + 2) + 1) % k + 1))} : Set V3)
          = {vv j, vv (j + 1)}
      rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) < k),
          Nat.mod_eq_of_lt (by omega : k - (j + 2) + 1 < k),
          show k - (k - (j + 2) + 1 + 1) = j from by omega,
          show k - (k - (j + 2) + 1) = j + 1 from by omega,
          pairEqSwapP13]
    · have heq' : j + 1 = k := by omega
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      show ({vv (k - ((k - 1) % k + 1)),
             vv (k - ((k - 1 + 1) % k + 1))} : Set V3)
          = {vv j, vv (j + 1)}
      rw [Nat.mod_eq_of_lt (by omega : k - 1 < k),
        show k - 1 + 1 = k from by omega, Nat.mod_self, heq', hv0,
        show j = k - 1 from by omega,
        show k - (0 + 1) = k - 1 from by omega, Nat.sub_self, pairEqSwapP13]
  ext e
  constructor
  · intro he
    obtain ⟨i, -, hFe⟩ := he
    subst hFe
    have hu : (i + 1) % k = (i % k + 1) % k := (Nat.mod_add_mod i k 1).symm
    have hk1 : i % k < k := Nat.mod_lt i hk0
    by_cases hlt : i % k + 1 < k
    · rw [Set.mem_image]
      show ∃ x ∈ Set.univ, ({vv x, vv (x + 1)} : Set V3)
          = {vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))}
      rw [hu, Nat.mod_eq_of_lt hlt]
      refine ⟨k - (i % k + 2), Set.mem_univ _, ?_⟩
      rw [pairEqSwapP13,
        show k - (i % k + 2) + 1 = k - (i % k + 1) from by omega,
        show k - (i % k + 2) = k - (i % k + 1 + 1) from by omega]
    · rw [Set.mem_image]
      show ∃ x ∈ Set.univ, ({vv x, vv (x + 1)} : Set V3)
          = {vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))}
      have heq : i % k + 1 = k := by omega
      rw [hu, heq, Nat.mod_self, Nat.sub_self]
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      rw [show k - 1 + 1 = k from by omega, hv0,
        show k - (0 + 1) = k - 1 from by omega, pairEqSwapP13]
  · intro he
    obtain ⟨j, -, hjF⟩ := he
    subst hjF
    rw [Set.mem_image]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact key j hjk
    · show ({vv j, vv (j + 1)} : Set V3)
          ∈ Set.image
              (fun i : ℕ =>
                ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
              Set.univ
      have h1 : vv (j % k + 1) = vv (j + 1) := by
        rw [← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) (j % k + 1),
          Nat.mod_add_mod j k 1,
          ← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) (j + 1)]
      have heqset : (({vv j, vv (j + 1)} : Set V3) =
          {vv (j % k), vv (j % k + 1)}) := by
        rw [← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) j, ← h1]
      rw [heqset]
      exact key (j % k) (Nat.mod_lt j hk0)

/-- dart equality componentwise. -/
private theorem dartEqP13 {a b c d : V3} (h1 : a = c) (h2 : b = d) :
    ((a, b) : V3 × V3) = (c, d) := by rw [h1, h2]

/-- HOL `OPP_IMAGE_F_EQ` (src:482): ordered darts. -/
theorem OPP_IMAGE_F_EQ_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : 1 < k) :
    Set.image
        (fun i : ℕ => (vv (k - ((i + 1) % k + 1)), vv (k - (i % k + 1)))) Set.univ
      = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ := by
  have hk0 : (0:ℕ) < k := by omega
  have hv0 : vv k = vv 0 := by
    have h := hper 0
    rwa [Nat.zero_add] at h
  have key : ∀ j, j < k → (vv j, vv (j + 1))
      ∈ Set.image
          (fun i : ℕ => (vv (k - ((i + 1) % k + 1)), vv (k - (i % k + 1))))
          Set.univ := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) k with hlt | heq
    · refine ⟨k - (j + 2), Set.mem_univ _, ?_⟩
      have hA : k - ((k - (j + 2) + 1) % k + 1) = j := by
        rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) + 1 < k)]
        omega
      have hB : k - ((k - (j + 2)) % k + 1) = j + 1 := by
        rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) < k)]
        omega
      exact dartEqP13 (congrArg vv hA) (congrArg vv hB)
    · have heq' : j + 1 = k := by omega
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      show ((vv (k - ((k - 1 + 1) % k + 1)), vv (k - ((k - 1) % k + 1))) : V3 × V3)
          = (vv j, vv (j + 1))
      rw [Nat.mod_eq_of_lt (by omega : k - 1 < k), show k - 1 + 1 = k from by omega,
        Nat.mod_self, heq', hv0, show j = k - 1 from by omega,
        show k - (0 + 1) = k - 1 from by omega, Nat.sub_self]
  ext d
  constructor
  · intro hd
    obtain ⟨i, -, hdi⟩ := hd
    subst hdi
    rw [Set.mem_image]
    have hu : (i + 1) % k = (i % k + 1) % k := (Nat.mod_add_mod i k 1).symm
    have hk1 : i % k < k := Nat.mod_lt i hk0
    by_cases hlt : i % k + 1 < k
    · show ∃ x ∈ Set.univ, (vv x, vv (x + 1))
          = (vv (k - ((i + 1) % k + 1)), vv (k - (i % k + 1)))
      rw [hu, Nat.mod_eq_of_lt hlt]
      refine ⟨k - (i % k + 2), Set.mem_univ _, ?_⟩
      exact dartEqP13 (congrArg vv (by omega)) (congrArg vv (by omega))
    · show ∃ x ∈ Set.univ, (vv x, vv (x + 1))
          = (vv (k - ((i + 1) % k + 1)), vv (k - (i % k + 1)))
      have heq : i % k + 1 = k := by omega
      rw [hu, heq, Nat.mod_self, Nat.sub_self]
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      exact dartEqP13 rfl (by rw [show k - 1 + 1 = k from by omega, hv0])
  · intro hd
    obtain ⟨j, -, hjd⟩ := hd
    subst hjd
    rw [Set.mem_image]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact key j hjk
    · show ∃ x ∈ Set.univ, (vv (k - ((x + 1) % k + 1)), vv (k - (x % k + 1)))
          = (vv j, vv (j + 1))
      have h1 : vv (j % k + 1) = vv (j + 1) := by
        rw [← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) (j % k + 1),
          Nat.mod_add_mod j k 1,
          ← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) (j + 1)]
      have h0 : ((vv j, vv (j + 1)) : V3 × V3) = (vv (j % k), vv (j % k + 1)) :=
        dartEqP13 (PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) j).symm h1.symm
      rw [h0]
      exact key (j % k) (Nat.mod_lt j hk0)

/-- HOL `OPP_IMAGE_F_EQ2` (src:526): ordered darts, reversed RHS. -/
theorem OPP_IMAGE_F_EQ2_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : 1 < k) :
    Set.image
        (fun i : ℕ => (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))) Set.univ
      = Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  have hk0 : (0:ℕ) < k := by omega
  have hv0 : vv k = vv 0 := by
    have h := hper 0
    rwa [Nat.zero_add] at h
  have key : ∀ j, j < k → (vv (j + 1), vv j)
      ∈ Set.image
          (fun i : ℕ => (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))))
          Set.univ := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) k with hlt | heq
    · refine ⟨k - (j + 2), Set.mem_univ _, ?_⟩
      have hA : k - ((k - (j + 2)) % k + 1) = j + 1 := by
        rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) < k)]
        omega
      have hB : k - ((k - (j + 2) + 1) % k + 1) = j := by
        rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) + 1 < k)]
        omega
      exact dartEqP13 (congrArg vv hA) (congrArg vv hB)
    · have heq' : j + 1 = k := by omega
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      show ((vv (k - ((k - 1) % k + 1)), vv (k - ((k - 1 + 1) % k + 1))) : V3 × V3)
          = (vv (j + 1), vv j)
      rw [Nat.mod_eq_of_lt (by omega : k - 1 < k), show k - 1 + 1 = k from by omega,
        Nat.mod_self, Nat.sub_self, heq', hv0, show j = k - 1 from by omega]
  ext d
  constructor
  · intro hd
    obtain ⟨i, -, hdi⟩ := hd
    subst hdi
    rw [Set.mem_image]
    have hu : (i + 1) % k = (i % k + 1) % k := (Nat.mod_add_mod i k 1).symm
    have hk1 : i % k < k := Nat.mod_lt i hk0
    by_cases hlt : i % k + 1 < k
    · show ∃ x ∈ Set.univ, (vv (x + 1), vv x)
          = (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))
      rw [hu, Nat.mod_eq_of_lt hlt]
      refine ⟨k - (i % k + 2), Set.mem_univ _, ?_⟩
      exact dartEqP13 (congrArg vv (by omega)) (congrArg vv (by omega))
    · show ∃ x ∈ Set.univ, (vv (x + 1), vv x)
          = (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))
      have heq : i % k + 1 = k := by omega
      rw [hu, heq, Nat.mod_self]
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      exact dartEqP13
        (by rw [show k - 1 + 1 = k from by omega, hv0, Nat.sub_self])
        (by rw [show k - (0 + 1) = k - 1 from by omega])
  · intro hd
    obtain ⟨j, -, hjd⟩ := hd
    subst hjd
    rw [Set.mem_image]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact key j hjk
    · show ∃ x ∈ Set.univ, (vv (k - (x % k + 1)), vv (k - ((x + 1) % k + 1)))
          = (vv (j + 1), vv j)
      have h1 : vv (j % k + 1) = vv (j + 1) := by
        rw [← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) (j % k + 1),
          Nat.mod_add_mod j k 1,
          ← PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) (j + 1)]
      have h0 : ((vv (j + 1), vv j) : V3 × V3) = (vv (j % k + 1), vv (j % k)) :=
        dartEqP13 h1.symm (PERIODIC_PROPERTY_p13 hper (by omega : (k:ℕ) ≠ 0) j).symm
      rw [h0]
      exact key (j % k) (Nat.mod_lt j hk0)

/-- negation commutes with univ-images (point form). -/
private theorem imageNegCompUnivP13 {f : ℕ → V3} :
    Set.image (fun i : ℕ => -(f i)) Set.univ
      = Set.image (fun x : V3 => -x) (Set.image f Set.univ) := by
  rw [Set.image_image, imageUnivCongrP13 (fun _ => rfl)]

/-- negation commutes with univ-images (pair-of-points form). -/
private theorem imageNegDartCompUnivP13 {f g : ℕ → V3} :
    Set.image (fun i : ℕ => (-(f i), -(g i))) Set.univ
      = Set.image (fun p : V3 × V3 => (-p.1, -p.2))
          (Set.image (fun i : ℕ => (f i, g i)) Set.univ) := by
  rw [Set.image_image, imageUnivCongrP13 (fun _ => rfl)]

/-- negation commutes with univ-images (2-element-set form). -/
private theorem imageNegPairCompUnivP13 {f g : ℕ → V3} :
    Set.image (fun i : ℕ => ({-(f i), -(g i)} : Set V3)) Set.univ
      = Set.image (fun S : Set V3 => Set.image (fun x : V3 => -x) S)
          (Set.image (fun i : ℕ => ({f i, g i} : Set V3)) Set.univ) := by
  ext S
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨{f i, g i}, ⟨i, rfl⟩, by rw [← ELEMENT2_SYM_0_p13 (f i) (g i)]⟩
  · rintro ⟨T, ⟨i, rfl⟩, hT⟩
    have h2 : Set.image (fun x : V3 => -x) ({f i, g i} : Set V3)
        = {-(f i), -(g i)} := by
      rw [← ELEMENT2_SYM_0_p13 (f i) (g i)]
    rw [h2] at hT
    exact ⟨i, hT⟩

/-- HOL `OPP_IMAGE_V_EQ_NEG` (src:885). -/
theorem OPP_IMAGE_V_EQ_NEG_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : k ≠ 0) :
    Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ
      = Set.image (fun i : ℕ => -(vv i)) Set.univ := by
  rw [imageNegCompUnivP13 (f := fun i => vv (k - (i % k + 1))),
    OPP_IMAGE_V_EQ_p13 vv hper hk, imageNegCompUnivP13 (f := vv)]

/-- HOL `OPP_IMAGE_E_EQ_NEG` (src:902). -/
theorem OPP_IMAGE_E_EQ_NEG_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3))
        Set.univ
      = Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ := by
  rw [imageNegPairCompUnivP13
      (f := fun i => vv (k - (i % k + 1)))
      (g := fun i => vv (k - ((i + 1) % k + 1))),
    OPP_IMAGE_E_EQ_p13 vv hper hk, imageNegPairCompUnivP13]

/-- HOL `OPP_IMAGE_F_EQ_NEG` (src:946). -/
theorem OPP_IMAGE_F_EQ_NEG_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ =>
        (-(vv (k - ((i + 1) % k + 1))), -(vv (k - (i % k + 1))))) Set.univ
      = Set.image (fun i : ℕ => (-(vv i), -(vv (i + 1)))) Set.univ := by
  rw [imageNegDartCompUnivP13
      (f := fun i => vv (k - ((i + 1) % k + 1)))
      (g := fun i => vv (k - (i % k + 1))),
    OPP_IMAGE_F_EQ_p13 vv hper hk, imageNegDartCompUnivP13]

/-- HOL `OPP_IMAGE_F_EQ2_NEG` (src:991). -/
theorem OPP_IMAGE_F_EQ2_NEG_p13 (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ =>
        (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ
      = Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) Set.univ := by
  rw [imageNegDartCompUnivP13
      (f := fun i => vv (k - (i % k + 1)))
      (g := fun i => vv (k - ((i + 1) % k + 1))),
    OPP_IMAGE_F_EQ2_p13 vv hper hk, imageNegDartCompUnivP13]

/-- HOL `BALL_ANNULUS_SYM_0` (src:570); `ball_annulus` <->
`ballAnnulus` (PackingAuto2). -/
theorem BALL_ANNULUS_SYM_0_p13 (v : V3) : -v ∈ ballAnnulus ↔ v ∈ ballAnnulus := by
  simp only [ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
    dist_eq_norm, sub_zero, norm_neg]

/-- HOL `DIST_SYM_0` (src:574). -/
theorem DIST_SYM_0_p13 (a b : V3) : dist (-a) (-b) = dist a b := by
  have h : (-a) - (-b) = -(a - b) := by abel
  rw [dist_eq_norm, dist_eq_norm, h, norm_neg]

/-! ## Section 3: fan/hypermap-side lemmas (src:578-627) -/

/-- HOL `OPP_FAN_SYM_0` (src:578). Proof pending (needs the `FAN`
conjunct-by-conjunct transfer; DISCHARGES convention). -/
theorem OPP_FAN_SYM_0_p13 {k : ℕ} (vv : ℕ → V3) (h3 : 3 ≤ k)
    (hper : PeriodicP13 vv k)
    (hf : FAN 0 (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)) :
    FAN 0
      (Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ)
      (Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3))
        Set.univ) := by
  sorry

/-- HOL `ORD_PAIRS_E_VV` (src:598). -/
theorem ORD_PAIRS_E_VV_p13 (vv : ℕ → V3) :
    ordPairsP13 (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
        ∪ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  ext p
  constructor
  · intro hp
    have hp' : ({p.1, p.2} : Set V3)
        ∈ Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ := hp
    obtain ⟨i, -, he⟩ := hp'
    rw [pairSetEqP13] at he
    rcases he with (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨i, Set.mem_univ _, by show (vv i, vv (i + 1)) = p; rw [h1, h2]⟩
    · exact Or.inr ⟨i, Set.mem_univ _, by show (vv (i + 1), vv i) = p; rw [h1, h2]⟩
  · rintro (⟨i, -, he⟩ | ⟨i, -, he⟩)
    · rw [← he]
      exact Set.mem_setOf_eq.mpr (by
        show {vv i, vv (i + 1)} ∈ Set.image
          (fun j : ℕ => ({vv j, vv (j + 1)} : Set V3)) Set.univ
        exact ⟨i, Set.mem_univ _, rfl⟩)
    · rw [← he]
      exact Set.mem_setOf_eq.mpr (by
        show {vv (i + 1), vv i} ∈ Set.image
          (fun j : ℕ => ({vv j, vv (j + 1)} : Set V3)) Set.univ
        rw [pairEqSwapP13]
        exact ⟨i, Set.mem_univ _, rfl⟩)

/-- HOL `SELF_PAIR_EMPTY_VV` (src:609). -/
theorem SELF_PAIR_EMPTY_VV_p13 (vv : ℕ → V3) :
    selfPairsP13 (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
        (Set.image vv Set.univ)
      = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨h12, hv, hev⟩ := hp
  obtain ⟨i, -, hi⟩ := hv
  have hmemb : vv (i + 1) ∈ eeP13 p.1
      (Set.image (fun j : ℕ => ({vv j, vv (j + 1)} : Set V3)) Set.univ) :=
    Set.mem_setOf_eq.mpr ⟨i, Set.mem_univ _, by rw [← hi]⟩
  rw [hev] at hmemb
  exact Set.notMem_empty _ hmemb

/-- HOL `DART_OF_HYP_VV` (src:622). -/
theorem DART_OF_HYP_VV_p13 (vv : ℕ → V3) :
    dartsOfHypP13 (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
        (Set.image vv Set.univ)
      = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
        ∪ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  rw [dartsOfHypP13, SELF_PAIR_EMPTY_VV_p13, ORD_PAIRS_E_VV_p13, Set.union_empty]

/-! ## Section 4: pair-of-points lemmas (src:628-712, 1037, 1096, 1233,
1379-1414, 2359, 814) -/

/-- HOL `PAIR_FUN_SYM_0` (src:628). -/
theorem PAIR_FUN_SYM_0_p13 (vv1 vv2 : ℕ → V3) :
    Set.image (fun i : ℕ => (-(vv1 i), -(vv2 i))) Set.univ
      = Set.image (fun p : V3 × V3 => (-p.1, -p.2))
          (Set.image (fun i : ℕ => (vv1 i, vv2 i)) Set.univ) := by
  rw [Set.image_image, imageUnivCongrP13 (fun _ => rfl)]

/-- HOL `IN_PAIR_SYM_0` (src:643). -/
theorem IN_PAIR_SYM_0_p13 {a : V3 × V3} {A : Set (V3 × V3)} (h : a ∈ A) :
    (fun p : V3 × V3 => (-p.1, -p.2)) a
      ∈ Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A :=
  Set.mem_image_of_mem _ h

/-- HOL `ID_SYM_0` (src:646). -/
theorem ID_SYM_0_p13 (x : V3 × V3) :
    (fun p : V3 × V3 => (-p.1, -p.2)) ((fun p : V3 × V3 => (-p.1, -p.2)) x) = x := by
  simp

/-- HOL `ID_PAIR_SYM_0` (src:654). -/
theorem ID_PAIR_SYM_0_p13 (A : Set (V3 × V3)) :
    Set.image (fun p : V3 × V3 => (-p.1, -p.2))
        (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A)
      = A := by
  rw [Set.image_image]
  simpa using Set.image_id A

/-- HOL `IN_EQ_PAIR_SYM_0` (src:667). -/
theorem IN_EQ_PAIR_SYM_0_p13 {a : V3 × V3} {A : Set (V3 × V3)} :
    (fun p : V3 × V3 => (-p.1, -p.2)) a
        ∈ Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A
      ↔ a ∈ A := by
  constructor
  · intro h
    rw [Set.mem_image] at h
    obtain ⟨y, hy, hfya⟩ := h
    rw [Prod.mk.injEq] at hfya
    have hay : a = y :=
      (Prod.ext (neg_inj.mp hfya.1) (neg_inj.mp hfya.2)).symm
    rw [hay]
    exact hy
  · intro h
    rw [Set.mem_image]
    exact ⟨a, h, rfl⟩

/-- HOL `FST_SND_PAIR_SYM_0` (src:676). -/
theorem FST_SND_PAIR_SYM_0_p13 (x : V3 × V3) :
    ((fun p : V3 × V3 => (-p.1, -p.2)) x).1 = -x.1
      ∧ ((fun p : V3 × V3 => (-p.1, -p.2)) x).2 = -x.2 :=
  ⟨rfl, rfl⟩

/-- HOL `EQ_SET_PAIR_SYM_0` (src:684). -/
theorem EQ_SET_PAIR_SYM_0_p13 {A B : Set (V3 × V3)} :
    Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A
        = Set.image (fun p : V3 × V3 => (-p.1, -p.2)) B
      ↔ A = B := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  ext x
  have h1 : (fun p : V3 × V3 => (-p.1, -p.2)) x
      ∈ Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A ↔ x ∈ A :=
    IN_EQ_PAIR_SYM_0_p13
  have h2 : (fun p : V3 × V3 => (-p.1, -p.2)) x
      ∈ Set.image (fun p : V3 × V3 => (-p.1, -p.2)) B ↔ x ∈ B :=
    IN_EQ_PAIR_SYM_0_p13
  constructor
  · intro hx
    exact h2.mp (h ▸ h1.mpr hx)
  · intro hx
    exact h1.mp (h.symm ▸ h2.mpr hx)

/-- HOL `COMMUTATIVE_POINT_PAIR_0` (src:1233). -/
theorem COMMUTATIVE_POINT_PAIR_0_p13 {a b : V3 × V3} :
    (fun p : V3 × V3 => (-p.1, -p.2)) a = b ↔ a = (fun p : V3 × V3 => (-p.1, -p.2)) b := by
  constructor
  · intro h
    have := ID_SYM_0_p13 a
    rw [h] at this
    exact this.symm
  · intro h
    rw [h]
    exact ID_SYM_0_p13 b

/-- HOL `FST_SND_EQ_PAIR_SYM_0` (src:1096). -/
theorem FST_SND_EQ_PAIR_SYM_0_p13 (x : V3 × V3) :
    (fun p : V3 × V3 => (-p.1, -p.2)) x = (-x.1, -x.2) :=
  rfl

/-- HOL `EQUI_FF_SYM_0` (src:1379). -/
theorem EQUI_FF_SYM_0_p13 (vv : ℕ → V3) (x : V3 × V3) :
    (x.2, x.1) ∈ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
      ↔ x ∈ Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ := by
  cases x with
  | mk x1 x2 =>
    simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨i, h2⟩
      rw [Prod.mk.injEq] at h2
      exact ⟨i, by rw [h2.2, h2.1]⟩
    · rintro ⟨i, h2⟩
      rw [Prod.mk.injEq] at h2
      exact ⟨i, by rw [h2.1, h2.2]⟩

/-- HOL `CARD_EQUI_FF_SYM_0` (src:1403). -/
theorem CARD_EQUI_FF_SYM_0_p13 (vv : ℕ → V3)
    (h : (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).Finite) :
    Nat.card (Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ)
      = Nat.card (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
  have hswap : Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
      = Prod.swap '' (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rw [Set.image_image]
    exact (imageUnivCongrP13 (fun _ => rfl)).symm
  rw [hswap, Nat.card_image_of_injective
    (f := Prod.swap)
    (fun a b hab => by
      have h2 : (a.2, a.1) = (b.2, b.1) := hab
      rw [Prod.mk.injEq] at h2
      exact Prod.ext h2.2 h2.1)
    _]

/-- HOL `FUN_COMMUTATIVE` (src:814); `POWER n`/`ITER n` <-> `f^[n]`. -/
theorem FUN_COMMUTATIVE_p13 {f g f1 : V3 × V3 → V3 × V3}
    (h : ∀ x, f (g x) = g (f1 x)) : ∀ n x, f^[n] (g x) = g (f1^[n] x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h]

/-- Negation transports two-point sets (`EE_SYM_0_p13` bridge). -/
private theorem image_neg_pair_p13 (x y : V3) :
    (Set.image (fun z : V3 => -z) ({x, y} : Set V3)) = ({-x, -y} : Set V3) := by
  ext u
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, (rfl | rfl), rfl⟩ <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> simp

/-- HOL `EE_SYM_0` (src:693).
DISCHARGED: elementwise — `{-a, w} = {-(vv i), -(vv (i+1))}` transports
under negation to `{a, -w} = {vv i, vv (i+1)}` (`image_neg_pair_p13`), so
`-w ∈ eeP13 a E` exactly when `w ∈ eeP13 (-a) E'`. -/
theorem EE_SYM_0_p13 (vv : ℕ → V3) (a : V3) :
    eeP13 (-a) (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      = Set.image (fun x : V3 => -x)
          (eeP13 a (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)) := by
  ext w
  constructor
  · intro hw
    rw [eeP13, Set.mem_setOf_eq] at hw
    obtain ⟨i, -, hS⟩ := (Set.mem_image _ _ _).mp hw
    have hS' : ({-(vv i), -(vv (i + 1))} : Set V3) = {-a, w} := hS
    refine ⟨-w, ?_, by simp⟩
    show {a, -w} ∈ Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ
    refine ⟨i, Set.mem_univ _, ?_⟩
    have h1' : (Set.image (fun z : V3 => -z) ({-a, w} : Set V3))
        = (Set.image (fun z : V3 => -z) ({-(vv i), -(vv (i + 1))} : Set V3)) := by
      rw [hS']
    show ({vv i, vv (i + 1)} : Set V3) = {a, -w}
    calc ({vv i, vv (i + 1)} : Set V3)
        = (fun z : V3 => -z) '' ({-(vv i), -(vv (i + 1))} : Set V3) := by
          rw [image_neg_pair_p13 (-(vv i)) (-(vv (i + 1)))]
          simp
      _ = (fun z : V3 => -z) '' ({-a, w} : Set V3) := by rw [hS']
      _ = {a, -w} := by
          rw [image_neg_pair_p13 (-a) w]
          simp
  · intro hw
    obtain ⟨w', hmem, hw'eq⟩ := (Set.mem_image _ _ _).mp hw
    rw [eeP13, Set.mem_setOf_eq] at hmem
    obtain ⟨i, -, hEq⟩ := (Set.mem_image _ _ _).mp hmem
    have hEq' : ({a, w'} : Set V3) = ({vv i, vv (i + 1)} : Set V3) := hEq.symm
    refine ⟨i, Set.mem_univ _, ?_⟩
    rw [← hw'eq]
    simp only
    rw [← image_neg_pair_p13 a w', ← image_neg_pair_p13 (vv i) (vv (i + 1)), hEq']

/-- HOL `SUM_PAIR_SYM_0` (src:2359).
DISCHARGED: the neg-pair map is an involution, so finiteness transports and
`Finset.sum_image` reindexes the finite branch; both branches give `0` in
the infinite case. -/
theorem SUM_PAIR_SYM_0_p13 {s : Set (V3 × V3)} (f : V3 × V3 → ℝ) :
    setSum (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) s) f
      = setSum s (f ∘ (fun p : V3 × V3 => (-p.1, -p.2))) := by
  set m : V3 × V3 → V3 × V3 := fun p => (-p.1, -p.2) with hm
  have hms : ∀ x : V3 × V3, m (m x) = x := by
    intro x
    simp only [hm]
    simp
  have hinj : Function.Injective m := by
    intro a b hab
    have h1 : m (m a) = m (m b) := by rw [hab]
    rwa [hms, hms] at h1
  by_cases hs : s.Finite
  · have hf : (Set.image m s).Finite := hs.image _
    have himg := Set.Finite.toFinset_image m hs hf
    unfold setSum
    rw [dif_pos hf, dif_pos hs, himg, Finset.sum_image (g := m) (by
      intro x _ y _ hxy
      exact hinj hxy)]
    rfl
  · have hf : ¬ (Set.image m s).Finite := by
      intro hfi
      have hEq : Set.image m (Set.image m s) = s := by
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          rw [hms]
          exact hz
        · intro hx
          exact (Set.mem_image _ _ _).mpr ⟨m x, (Set.mem_image _ _ _).mpr ⟨x, hx, rfl⟩, hms x⟩
      have hfin2 : (Set.image m (Set.image m s)).Finite := hfi.image m
      rw [hEq] at hfin2
      exact hs hfin2
    unfold setSum
    rw [dif_neg hf, dif_neg hs]

/-- HOL `DUAL_EXISTS_MOD0` (src:1453). -/
theorem DUAL_EXISTS_MOD0_p13 {k b : ℕ} (hk : k ≠ 0) :
    ∃ n : ℕ, (n * (k - 1)) % k = b % k := by
  have hbk : b % k < k := Nat.mod_lt b (Nat.pos_of_ne_zero hk)
  obtain ⟨t, ht⟩ : ∃ t, t = b % k := ⟨b % k, rfl⟩
  refine ⟨k - t, ?_⟩
  rw [← ht]
  obtain ⟨m, hmdef⟩ : ∃ m, m = k - t := ⟨k - t, rfl⟩
  rw [← hmdef]
  have hm1 : 1 ≤ m := by omega
  have h3 : k - m = t := by omega
  have hkm : k ≤ k * m := Nat.le_mul_of_pos_right k hm1
  have hkey : m * (k - 1) = k * (m - 1) + (k - m) := by
    have h1 : m * (k - 1) = m * k - m := by rw [Nat.mul_sub, Nat.mul_one]
    have h2 : k * (m - 1) = k * m - k := by rw [Nat.mul_sub, Nat.mul_one]
    have h4 : k * m = m * k := Nat.mul_comm k m
    rw [h1, h2, h4]
    omega
  rw [hkey, Nat.add_comm (k * (m - 1)) (k - m), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega : k - m < k), h3]

/-- HOL `DUAL_EXISTS_MOD_LE` (src:1470). -/
theorem DUAL_EXISTS_MOD_LE_p13 {k a b : ℕ} (hk : k ≠ 0) (hle : a % k ≤ b % k) :
    ∃ n : ℕ, (n * (k - 1) + a) % k = b % k := by
  have hak : a % k < k := Nat.mod_lt a (Nat.pos_of_ne_zero hk)
  have hbk : b % k < k := Nat.mod_lt b (Nat.pos_of_ne_zero hk)
  obtain ⟨n0, hn0⟩ := DUAL_EXISTS_MOD0_p13 hk (b := b % k - a % k)
  refine ⟨n0, ?_⟩
  have h1 : (b % k - a % k) % k = b % k - a % k := Nat.mod_eq_of_lt (by omega)
  rw [Nat.add_mod, hn0, h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- HOL `DUAL_EXISTS_MOD_GE` (src:1482). -/
theorem DUAL_EXISTS_MOD_GE_p13 {k a b : ℕ} (hk : k ≠ 0) (hge : b % k ≤ a % k) :
    ∃ n : ℕ, (n * (k - 1) + a) % k = b % k := by
  have hak : a % k < k := Nat.mod_lt a (Nat.pos_of_ne_zero hk)
  have hbk : b % k < k := Nat.mod_lt b (Nat.pos_of_ne_zero hk)
  obtain ⟨n0, hn0⟩ := DUAL_EXISTS_MOD0_p13 hk (b := b % k + k - a % k)
  refine ⟨n0, ?_⟩
  rw [Nat.add_mod, hn0, Nat.mod_add_mod (b % k + k - a % k) k (a % k)]
  have h2 : b % k + k - a % k + a % k = b % k + k := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hbk]

/-- HOL `DUAL_EXISTS_MOD` (src:1497). -/
theorem DUAL_EXISTS_MOD_p13 {k a b : ℕ} (hk : k ≠ 0) :
    ∃ n : ℕ, (n * (k - 1) + a) % k = b % k := by
  rcases le_total (a % k) (b % k) with h | h
  · exact DUAL_EXISTS_MOD_LE_p13 hk h
  · exact DUAL_EXISTS_MOD_GE_p13 hk h

/-- HOL `NO_IS_EAR` (src:2226). -/
theorem NO_IS_EAR_p13 (s : ScsV39P13) (hk : ¬(s.k ≤ 3)) : ¬(isEarV39P13 s) := by
  intro h
  obtain ⟨-, -, h3, -, -, -⟩ := h
  omega

/-- HOL `NO_IS_EAR_SCS_OPP` (src:2230). -/
theorem NO_IS_EAR_SCS_OPP_p13 (s : ScsV39P13) (hk : ¬(s.k ≤ 3)) :
    ¬(isEarV39P13 (scsOppV39P13 s)) := by
  intro h
  obtain ⟨-, -, h3, -, -, -⟩ := h
  have hk2 : (scsOppV39P13 s).k = s.k := rfl
  omega

/-- HOL `K_SCS_OPP` (src:3127). -/
theorem K_SCS_OPP_p13 (s : ScsV39P13) : (scsOppV39P13 s).k = s.k := rfl

/-- HOL `DUAL_PEROPP` (src:3084). -/
theorem DUAL_PEROPP_p13 {α : Sort u} {a : ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hper : PeriodicP13 a k) : peroppP13 (peroppP13 a k) k = a := by
  funext i
  show a (k - ((k - (i % k + 1)) % k + 1)) = a i
  rw [OPP_SUC_MOD_p13 hk, PERIODIC_PROPERTY_p13 hper hk i]

/-- 2-argument periodicity transfers to multiples. -/
private theorem periodicAdd2P13 {α : Sort u} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2P13 a k) : ∀ q i j, a (i + q * k) j = a i j ∧ a i (j + q * k) = a i j := by
  intro q
  induction q with
  | zero => intro i j; simp
  | succ n ih =>
      intro i j
      have hsplit : i + Nat.succ n * k = i + n * k + k := by
        rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (n * k) k]
      have hsplitJ : j + Nat.succ n * k = j + n * k + k := by
        rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (n * k) k]
      rw [hsplit, hsplitJ]
      exact ⟨(hper (i + n * k) j).1.trans (ih i j).1,
        (hper i (j + n * k)).2.trans (ih i j).2⟩

/-- HOL `DUAL_PEROPP2` (src:3089). -/
theorem DUAL_PEROPP2_p13 {α : Sort u} {a : ℕ → ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hper : Periodic2P13 a k) : peropp2P13 (peropp2P13 a k) k = a := by
  funext i j
  show a (k - ((k - (i % k + 1)) % k + 1)) (k - ((k - (j % k + 1)) % k + 1)) = a i j
  rw [OPP_SUC_MOD_p13 hk, OPP_SUC_MOD_p13 hk]
  have hA : a (i % k) (j % k) = a i (j % k) := by
    have h := (periodicAdd2P13 hper (i / k) (i % k) (j % k)).1.symm
    rw [Nat.mul_comm, Nat.mod_add_div i k] at h
    exact h
  have hB : a i (j % k) = a i j := by
    have h := (periodicAdd2P13 hper (j / k) i (j % k)).2.symm
    rw [Nat.mul_comm, Nat.mod_add_div j k] at h
    exact h
  rw [hA, hB]

/-- HOL `DUAL_NEG_PEROPP` (src:3132). -/
theorem DUAL_NEG_PEROPP_p13 {k : ℕ} (ww : ℕ → V3) (hk : k ≠ 0)
    (hper : PeriodicP13 ww k) :
    (fun i => -(peroppP13 (fun i => -(peroppP13 ww k i)) k i)) = ww := by
  funext i
  show -(-ww (k - ((k - (i % k + 1)) % k + 1))) = ww i
  rw [neg_neg]
  exact (congrArg ww (OPP_SUC_MOD_p13 hk)).trans (PERIODIC_PROPERTY_p13 hper hk i)

/-- HOL `DUALNEG_PEROPP_BB` (src:3141). -/
theorem DUALNEG_PEROPP_BB_p13 {s : ScsV39P13} {k : ℕ} (ww : ℕ → V3)
    (hk : s.k = k) (hbb : BBsV39P13 (scsOppV39P13 s) ww) (hk3 : ¬(k ≤ 3)) :
    (fun i => -(peroppP13 (fun i => -(peroppP13 ww k i)) k i)) = ww := by
  refine DUAL_NEG_PEROPP_p13 ww (by omega) ?_
  have hk0 : k ≠ 0 := by omega
  have := hbb.2.1
  rwa [K_SCS_OPP_p13 s, hk] at this

/-- HOL `FAN_SYM_0` (src:336). Proof pending (fan6/fan7 conjunct transfer;
DISCHARGES convention). -/
theorem FAN_SYM_0_p13 (vv : ℕ → V3)
    (hf : FAN 0 (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)) :
    FAN 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
      (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ) := by
  sorry

/-- HOL `AFF_GE_COMMUTATIVE_SYM_0` (src:309). Proof pending. -/
theorem AFF_GE_COMMUTATIVE_SYM_0_p13 (e1 e : Set V3) :
    affGe (Set.image (fun x : V3 => -x) e1) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affGe e1 e) := by
  sorry

/-- HOL `AFF_GE_VEC0_SYM_0` (src:315). Proof pending. -/
theorem AFF_GE_VEC0_SYM_0_p13 (e : Set V3) :
    affGe ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affGe ({0} : Set V3) e) := by
  sorry

/-- HOL `AFF_LT_COMMUTATIVE_SYM_0` (src:319). Proof pending. -/
theorem AFF_LT_COMMUTATIVE_SYM_0_p13 (e1 e : Set V3) :
    affLt (Set.image (fun x : V3 => -x) e1) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affLt e1 e) := by
  sorry

/-- HOL `AFF_LT_VEC0_SYM_0` (src:325). Proof pending. -/
theorem AFF_LT_VEC0_SYM_0_p13 (e : Set V3) :
    affLt ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affLt ({0} : Set V3) e) := by
  sorry

/-- HOL `POINT_IN_AFF_LT_SYM_0` (src:1324). Proof pending. -/
theorem POINT_IN_AFF_LT_SYM_0_p13 {v1 w2 : V3} (hd : Disjoint ({v1} : Set V3) {w2}) :
    -w2 ∈ affLt ({0, v1} : Set V3) {w2} := by
  sorry

/-- HOL `COLLINEAR_POINT_SYM_0` (src:1336).
DISCHARGED: `collinear_iff_of_mem` at `0` — if `v1` and `-w1` are both
`v`-multiples then so are `v1` and `w1` (`-w1 = r • v` gives
`w1 = -r • v`). -/
theorem COLLINEAR_POINT_SYM_0_p13 {v1 w1 : V3} (h : ¬Collinear ℝ ({0, v1, w1} : Set V3)) :
    ¬Collinear ℝ ({0, v1, -w1} : Set V3) := by
  intro hc
  have h0 : (0 : V3) ∈ ({0, v1, -w1} : Set V3) := by simp
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem h0).mp hc
  have h0p : (0 : V3) ∈ ({0, v1, w1} : Set V3) := by simp
  refine h ((collinear_iff_of_mem h0p).mpr ⟨v, ?_⟩)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h0 | h1c | h2c
  · rw [h0]; exact ⟨0, by simp⟩
  · rw [h1c]; exact hv v1 (by simp)
  · rw [h2c]
    obtain ⟨r, hr⟩ := hv (-w1) (by simp)
    exact ⟨-r, by
      have h1 : -w1 = r • v := by rw [hr, vadd_eq_add]; simp
      have h2 : w1 = -(-w1) := by rw [neg_neg]
      rw [h2, h1, neg_smul, vadd_eq_add]
      simp⟩

/-- HOL `AZIM_EQ_PI_POINT_SYM_0` (src:1350). Proof pending. -/
theorem AZIM_EQ_PI_POINT_SYM_0_p13 {v1 w1 : V3}
    (h : ¬Collinear ℝ ({0, v1, w1} : Set V3)) :
    azim 0 v1 w1 (-w1) = Real.pi := by
  sorry

/-- HOL `SUM_AZIM_SYM_0` (src:1361 and src:1371, verbatim duplicate). Proof
pending. -/
theorem SUM_AZIM_SYM_0_p13 {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3))
    (h3 : azim 0 v1 w1 w2 ≤ Real.pi) :
    azim 0 v1 w1 w2 + azim 0 v1 w2 (-w1) = Real.pi := by
  sorry

/-- HOL `AZIM_NEG_FIRST_PI` (src:1883). Proof pending. -/
theorem AZIM_NEG_FIRST_PI_p13 {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3))
    (h3 : 0 < azim 0 v1 w1 w2) :
    azim 0 (-v1) w1 w2 = 2 * Real.pi - azim 0 v1 w1 w2 := by
  sorry

/-- HOL `AZIM_COMPL_NEG` (src:1932). Proof pending. -/
theorem AZIM_COMPL_NEG_p13 {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3)) :
    azim 0 (-v1) w1 w2 = azim 0 v1 w2 w1 := by
  sorry

/-- HOL `REMOVE_NEG_AZIM1_SYM_0` (src:1961). Proof pending. -/
theorem REMOVE_NEG_AZIM1_SYM_0_p13 {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3)) :
    azim 0 v1 (-w1) (-w2) = azim 0 v1 w1 w2 := by
  sorry

/-- HOL `AZIM_NEG` (src:2014). Proof pending. -/
theorem AZIM_NEG_p13 {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3)) :
    azim 0 (-v1) (-w1) (-w2) = azim 0 v1 w2 w1 := by
  sorry

/-! ## Section 6: the scs-block conclusions (src:714-2527; the terminal
SCS/polar-symmetry registry).  The recurring hypothesis block
`scs_k_v39 s = k /\ IMAGE vv (:num) = V /\ IMAGE edges = E /\
IMAGE darts = FF /\ is_scs_v39 s /\ ~(k <= 3) /\ BBs_v39 s vv` is carried
conjunct-by-conjunct.  All proofs pending (DISCHARGES convention): they
compose the mechanical Section-1/2 lemmas through the hypermap-of-HYP
foundation deferred with `hypermapOfFan` (Fan.lean head note). -/

/-- HOL `EE_EXPAND_BB_VV` (src:714). -/
theorem EE_EXPAND_BB_VV_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (i : ℕ)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    eeP13 (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3) := by
  sorry

/-- HOL `IVS_AZIM_CYCLE_SYM_0` (src:749). -/
theorem IVS_AZIM_CYCLE_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv)
    (hx : x ∈ dartsOfHypP13 E V) :
    ivsAzimCycleP13 (eeP13 (-(x.2)) E) 0 (-(x.2)) (-(x.1))
      = -(ivsAzimCycleP13 (eeP13 (x.2) E) 0 (x.2) (x.1)) := by
  sorry

/-- HOL `ff_FUN_COMMUTATIVE_SYM_0` (src:787). -/
theorem ff_FUN_COMMUTATIVE_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ x : V3 × V3,
      ffOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) (ffOfHypP13 0 V E x) := by
  sorry

/-- HOL `ff_POWER_COMMUTATIVE_SYM_0` (src:823). -/
theorem ff_POWER_COMMUTATIVE_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ (n : ℕ) (x : V3 × V3),
      (ffOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))^[n]
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2))
            ((ffOfHypP13 0 V E)^[n] x) := by
  sorry

/-- HOL `FACE_SYM_0` (src:846). -/
theorem FACE_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    hypFaceP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        ((fun p : V3 × V3 => (-p.1, -p.2)) x)
      = Set.image (fun p : V3 × V3 => (-p.1, -p.2)) (hypFaceP13 0 V E x) := by
  sorry

/-- HOL `FACE_ALL_SYM_0` (src:1056). -/
theorem FACE_ALL_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ x : V3 × V3,
      hypFaceP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = Set.image (fun p : V3 × V3 => (-p.1, -p.2)) (hypFaceP13 0 V E x) := by
  sorry

/-- HOL `SYM_AZIM_CYCLE_SYM_0` (src:1104). -/
theorem SYM_AZIM_CYCLE_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv)
    (hx : x ∈ dartsOfHypP13 E V) :
    azim 0 (-(x.1)) (-(x.2)) =
        -(azim 0 (x.1) (x.2)) := by
  sorry

/-- HOL `NODE_MAP_SYM_0` (src:1143). -/
theorem NODE_MAP_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ x : V3 × V3,
      nnOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) (nnOfHypP13 0 V E x) := by
  sorry

/-- HOL `IMAGE_NODE_SYM_0` (src:1188). -/
theorem IMAGE_NODE_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ A : Set (V3 × V3),
      Set.image (nnOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
          (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A)
        = Set.image (fun p : V3 × V3 => (-p.1, -p.2))
            (Set.image (nnOfHypP13 0 V E) A) := by
  sorry

/-- HOL `EDGE_MAP_SYM_0` (src:1242). -/
theorem EDGE_MAP_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ x : V3 × V3,
      eeOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) (eeOfHypP13 0 V E x) := by
  sorry

/-- HOL `EDGE_POWER_MAP_SYM_0` (src:1285). -/
theorem EDGE_POWER_MAP_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ (n : ℕ) (x : V3 × V3),
      (eeOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))^[n]
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) ((eeOfHypP13 0 V E)^[n] x) := by
  sorry

/-- HOL `NODE_POWER_MAP_SYM_0` (src:1303). -/
theorem NODE_POWER_MAP_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ (n : ℕ) (x : V3 × V3),
      (nnOfHypP13 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))^[n]
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) ((nnOfHypP13 0 V E)^[n] x) := by
  sorry

/-- HOL `FF_OF_HYP_ITER_VV` (src:1417). -/
theorem FF_OF_HYP_ITER_VV_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (i : ℕ)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ∀ n : ℕ,
      (ffOfHypP13 0 V E)^[n] (vv (i + 1), vv i)
        = (vv (n * (k - 1) + i + 1), vv (n * (k - 1) + i)) := by
  sorry

/-- HOL `FACE_DUAL_SYM_0` (src:1505). -/
theorem FACE_DUAL_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv)
    (hxFF : x ∈ FF) :
    Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ = hypFaceP13 0 V E x := by
  sorry

/-- HOL `LOCAL_FAN_DUAL_SYM_0` (src:1558). -/
theorem LOCAL_FAN_DUAL_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    localFanP13 (Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ)
      (Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ =>
        (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ) := by
  sorry

/-- HOL `CONVEX_LOCAL_FAN_SYM_0` (src:2029). -/
theorem CONVEX_LOCAL_FAN_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    ConvexLocalFanP13
      (Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ)
      (Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ =>
        (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ) := by
  sorry

/-- HOL `PEROPP_IN_BB_SYM_0` (src:2183). -/
theorem PEROPP_IN_BB_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    BBsV39P13 (scsOppV39P13 s) (fun i => -(peroppP13 vv k i)) := by
  sorry

/-- HOL `DSV_EQ_SYM_0` (src:2236). -/
theorem DSV_EQ_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    dsvV39P13 (scsOppV39P13 s) (fun i => -(peroppP13 vv k i)) = dsvV39P13 s vv := by
  sorry

/-- HOL `TAUSTAR_EQ_SYM_0` (src:2374). -/
theorem TAUSTAR_EQ_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39P13 s vv) :
    taustarV39P13 (scsOppV39P13 s) (fun i => -(peroppP13 vv k i))
      = taustarV39P13 s vv := by
  sorry

/-- HOL `OPP_IS_SCS` (src:2536). -/
theorem OPP_IS_SCS_p13 (s : ScsV39P13) (hiscs : isScsV39P13 s) :
    isScsV39P13 (scsOppV39P13 s) := by
  sorry

/-- HOL `SCS_OPP_REFL` (src:3095). -/
theorem SCS_OPP_REFL_p13 (s : ScsV39P13) (hiscs : isScsV39P13 s) :
    scsOppV39P13 (scsOppV39P13 s) = s := by
  sorry

/-- HOL `BBPRIME_EQ_OPP_SYM_0` (src:3154). -/
theorem BBPRIME_EQ_OPP_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3))
    (hbp : vv ∈ BBprimeV39P13 s) :
    (fun i => -(peroppP13 vv k i)) ∈ BBprimeV39P13 (scsOppV39P13 s) := by
  sorry

/-- HOL `BBINDEX_EQ_SYM_0` (src:3182). -/
theorem BBINDEX_EQ_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3))
    (hbp : vv ∈ BBprimeV39P13 s) :
    BBindexV39P13 (scsOppV39P13 s) (fun i => -(peroppP13 vv k i))
      = BBindexV39P13 s vv := by
  sorry

/-- HOL `IMAGE_BBINDEX_SYM_0` (src:3316). -/
theorem IMAGE_BBINDEX_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3))
    (hbp : vv ∈ BBprimeV39P13 s) :
    Set.image (BBindexV39P13 (scsOppV39P13 s)) (BBprimeV39P13 (scsOppV39P13 s))
      = Set.image (BBindexV39P13 s) (BBprimeV39P13 s) := by
  sorry

/-- HOL `BBINDEX_MIN_SYM_0` (src:3343). -/
theorem BBINDEX_MIN_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3))
    (hbp : vv ∈ BBprimeV39P13 s) :
    BBindexMinV39P13 (scsOppV39P13 s) = BBindexMinV39P13 s := by
  sorry

/-- HOL `BBPRIME2_SYM_0` (src:3355). -/
theorem BBPRIME2_SYM_0_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3))
    (hbp2 : vv ∈ BBprime2V39P13 s) :
    (fun i => -(peroppP13 vv k i)) ∈ BBprime2V39P13 (scsOppV39P13 s) := by
  sorry

/-- HOL `MM_SCS_OPP` (src:3370). -/
theorem MM_SCS_OPP_p13 (s : ScsV39P13) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39P13 s) (hk3 : ¬(k ≤ 3))
    (hmm : vv ∈ MMsV39P13 s) :
    (fun i => -(peroppP13 vv k i)) ∈ MMsV39P13 (scsOppV39P13 s) := by
  sorry

/-- HOL `YXIONXL2` (src:3501): the terminal SCS arrow to the opposite
system. -/
theorem YXIONXL2_p13 (s : ScsV39P13) (k : ℕ)
    (hiscs : isScsV39P13 s) (hk : s.k = k) (hk3 : ¬(k ≤ 3)) :
    scsArrowV39P13 {s} {scsOppV39P13 s} := by
  sorry

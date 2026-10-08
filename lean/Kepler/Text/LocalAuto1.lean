/-
LocalAuto1: port of `scripts/local/appendix.hl` (Flyspeck "Local Fan /
Conclusions" appendix, T. Hales, 2013; 1571 lines, 89 defs + 21 theorems).

FILE MAP
  This appendix is the STATEMENT-REGISTRY of the Local Fan chapter's terminal
  SCS (semi-conic-system) case analysis: `svn 3270 contains deprecated
  terminal SCS cases`, so only the surviving conclusions are carried.  The
  file holds three payloads.
  (a) Local-fan-side primitives quoted by the conclusions but owned by the
      chapter proper (WRGCVDR/localization lanes): `azim_in_fan`,
      `interior_angle1`, `sol_local`, `circular`, `generic`, `lunar`,
      `deformation`, `convex_local_fan` (ported here; `local_fan` carries
      its full FAN / hypermap-face / `dih2k` content over `hypermapOfFan`).
  (b) Shared constants/kit feeding the tau inequalities: `cstab`, `rho_fun`,
      `rho_rho_fun` (rho_fun = Sphere.rho), `tau_fun`, `tau3`, `d_tame`,
      `tgt`, `arc1553_v39`, the torsor kit.
  (c) The scs_v39 record lane: the 10-component system type, `is_scs_v39` /
      `unadorned_v39` / `is_ear_v39`, the BB* / MM* minimality tower
      (`BBs_v39`, `dsv_v39`, `taustar_v39`, `BBprime_v39`, `BBindex_v39`,
      `BBprime2_v39`, `MMs_v39`), the initial list `s_init_list_v39`, the
      8 + 14 + 10 concrete systems (`scs_6I1`..`scs_3M1`), the arrow/slice/
      restriction toolkit, and every `*_concl` contract statement.

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `vec 0` <-> `0`; `packing` <->
    `Kepler.Statement.Packing`; `ball_annulus` <-> `ballAnnulus`;
    `sqrt8`/`#3.62`/`#15.53` etc. are exact decimal literals
    (`Real.sqrt 8`, `3.62`, `15.53`); NO `native_decide` anywhere.
  - The `scs_v39` type (appendix.hl:216-228, `new_type_definition` over the
    10-tuple `(k,d,a,alpha,beta,b,J,lo,hi,str)`) is ported as the structure
    `ScsV39`; the accessors `scs_k_v39`..`scs_str_v39` are the projections
    (`scs_str_v39 = SND(drop3(drop3 ...))` collapses to a field), so the ten
    `scs_*_v39_explicit` lemmas and `scs_components` are `rfl`.  `BBs_v39` /
    `MMs_v39` are the registry predicates over those tuple accessors.
  - `scs_J_v39`, `scs_lo_v39`, `scs_hi_v39`, `scs_str_v39` are predicates
    (`num->bool`); `periodic` is carried universe-polymorphically (`Periodic`)
    so it also applies to predicates, as in HOL.
  - The 21 mechanical theorems (`rho_rho_fun`, `peropp_periodic`,
    `periodic_empty`, `scs_components`, the ten `scs_*_v39_explicit`,
    `scs_v39_explicit`, `scs_unadorned`, `dsv_J_empty`,
    `LENGTH_s_init_list`, `FZIOTEF_REFL`, `FZIOTEF_TRANS`, `scs_inj`,
    `scs_3T1`) are PROVED here.  Every `*_concl` item keeps a `sorry` body:
    they are the chapter's contract registry (DISCHARGES convention — a later
    wave proves them and the `sorry` disappears).
  - The six JEJTVGB items and `JEJTVGB_concl`/`JEJTVGB_assume_v39` are term
    bindings in HOL (`let X_concl = `stmt``, resp. `new_definition` of the
    conjunction), and are referenced as PROPOSITIONS by `ZITHLQN_concl` /
    `EAPGLE_concl`; they are therefore carried as Prop-valued defs (statement
    registry, no proof claimed).  All other `*_concl` items are sorry'd
    theorems.
  - HOL term-level lets that are re-declared later (`scs_6T1`..`scs_3T7` at
    appendix.hl:511-603, `ear_cs`, `terminal_tri_5405130650`, the tuple
    pattern `scs_data`) are skipped; only the `new_definition` versions are
    ported.  `scs_3T6'`/`scs_4M3'`..`scs_4M6'` keep their primed names.
  - Source typos kept or fixed: `is_scs_v39` carries `periodic ... str` twice
    (verbatim); VPWSHTO's duplicated `u1 IN ...` conjunct kept; AURSIPD's free
    `vv` is bound as `v` (fixed).  `mk_planar` is identified with this file's
    `mk_planar2` (same argument shape at the EYYPQDW2/3 call sites); function
    level `re_eqvl` in TBRMXRZ1 is rendered pointwise via `reEqvl`
    (PackingAuto18).
  - `Kepler.Text.LocalAnchors` (bridge lane) deliberately does NOT import this
    file; the canonical `cstab`/`scsBasicV39`/`scsDiag` live here per the
    anchor notes there.

DISCHARGES: nothing yet (this file IS the contract registry).
-/

import Kepler.Geom.Aff
import Kepler.Geom.Coplanar
import Kepler.Geom.LuneVolume
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto18
import Kepler.Text.SphereKit
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Local-fan primitives quoted by the appendix conclusions
(localization.hl:66-131; `local_fan`'s FAN/face/`dih2k` content over
`hypermapOfFan`, with `has_orders`/`dih2k` ported below) -/

/-- HOL `EE` (localization.hl:38): the neighbours of `v` along `S`. -/
def ee (v : V3) (S : Set (Set V3)) : Set V3 := {w | {v, w} ∈ S}

/-- HOL `azim_in_fan (v,w) E` (localization.hl:74): the fan azimuth at the
dart, `2*pi` when the vertex is 1-valent; `azim_cycle (EE v E) (vec 0) v w`
is the fan successor `sigmaFan 0 univ E v w`. -/
noncomputable def azimInFan (e : V3 × V3) (E : Set (Set V3)) : ℝ :=
  if 1 < (ee e.1 E).ncard then azim 0 e.1 e.2 (sigmaFan 0 Set.univ E e.1 e.2)
  else 2 * Real.pi

/-- HOL `rho_node1 FF v = (@w. (v,w) IN FF)` (localization.hl:115). -/
noncomputable def rhoNode1 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon (fun w => (v, w) ∈ FF)

/-- HOL `ivs_rho_node1 FF v = (@a. (a,v) IN FF)` (localization.hl:117). -/
noncomputable def ivsRhoNode1 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon (fun a => (a, v) ∈ FF)

/-- HOL `interior_angle1 x FF v` (localization.hl:119). -/
noncomputable def interiorAngle1 (x : V3) (FF : Set (V3 × V3)) (v : V3) : ℝ :=
  azim x v (rhoNode1 FF v) (ivsRhoNode1 FF v)

/-- HOL `sol_local E f` (localization.hl:122); `sum` <-> `setSum`
(PackingAuto2:124, `0` on infinite sets, as in HOL Light). -/
noncomputable def solLocal (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  2 * Real.pi + setSum f (fun e => azimInFan e E - Real.pi)

/-- HOL `circular V E` (localization.hl:107). -/
def Circular (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∃ v w u : V3, {v, w} ∈ E ∧ u ∈ V ∧ ¬(affGt {0} {v, w} ∩ affLt {0} {u} = ∅)

/-- HOL `generic V E` (localization.hl:103). -/
def Generic (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v w u : V3, {v, w} ∈ E → u ∈ V → affGt {0} {v, w} ∩ affLt {0} {u} = ∅

/-- HOL `lunar (v,w) V E` (localization.hl:111). -/
def Lunar (v w : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ¬Circular V E ∧ {v, w} ⊆ V ∧ v ≠ w ∧ Collinear ℝ ({0, v, w} : Set V3)

/-- HOL `deformation ff V (a,b)` (localization.hl:128). -/
def Deformation (f : V3 → ℝ → V3) (V : Set V3) (a b : ℝ) : Prop :=
  (0 : ℝ) ∈ Icc a b ∧ (∀ v ∈ V, ∀ r ∈ Icc a b, ContinuousAt (f v) r) ∧
    ∀ v ∈ V, f v 0 = v

/-- HOL `has_orders f k` (localization.hl:20): the iterates below `k` are
nontrivial and the `k`-th is the identity.  `ITER i f = I` on functions ↦
`(f ^ i : Equiv.Perm α) = 1` (Hypermap.lean encoding note). -/
def HasOrders {α : Type*} (f : Equiv.Perm α) (k : ℕ) : Prop :=
  (∀ i, 0 < i → i < k → f ^ i ≠ 1) ∧ f ^ k = 1

/-- HOL `dih2k H k` (localization.hl:30): `CARD (dart H) = 2*k`, every dart's
face `S = face H x` satisfies `dart H = S UNION IMAGE (node_map H) S`, and
face/edge/node maps have orders `k`/`2`/`2`.  `face H x = orbit_map
(face_map H) x` ↦ `orbitMap H.faceMap x`; `dart H` ↦ `H.darts`. -/
def Dih2k {α : Type*} [DecidableEq α] (H : Hypermap α) (k : ℕ) : Prop :=
  H.darts.card = 2 * k ∧
    (∀ d ∈ H.darts, orbitMap H.faceMap d ∪ H.nodeMap '' orbitMap H.faceMap d =
      (H.darts : Set α)) ∧
    HasOrders H.faceMap k ∧ HasOrders H.edgeMap 2 ∧ HasOrders H.nodeMap 2

/-- HOL `local_fan (V,E,FF)` (WRGCVDR.hl:144 = localization.hl:66): `FAN
(vec 0,V,E)`, `FF` a hypermap face (`?x. x IN dart H /\ FF = face H x`) and
`dih2k H (CARD FF)` at `H = hypermap (HYP (vec 0,V,E))`.  Ported over the
fan chapter's dart-layer hypermap `hypermapOfFan 0 V E` (Fan.lean), whose
darts are `dart1OfFan V E`: on a fan the `HYP` kit's isolated-vertex
`self_pairs` are absent and its `azim_cycle` maps coincide with the
`sigmaFan` maps, so the face/`dih2k` content lands verbatim; the residual
`HYP`-layer bookkeeping is tracked by downstream obligations. -/
def LocalFan (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  ∃ hfan : FAN 0 V E,
    ∃ x ∈ (hypermapOfFan 0 V E hfan).darts,
      FF = orbitMap (hypermapOfFan 0 V E hfan).faceMap x ∧
        Dih2k (hypermapOfFan 0 V E hfan) FF.ncard

/-- HOL `wedge_in_fan_ge (v,w) E` (localization.hl:88). -/
noncomputable def wedgeInFanGe (e : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (ee e.1 E).ncard then wedgeGe 0 e.1 e.2 (sigmaFan 0 Set.univ E e.1 e.2)
  else Set.univ

/-- HOL `convex_local_fan (V,E,FF)` (localization.hl:92). -/
def ConvexLocalFan (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  LocalFan V E FF ∧ ∀ x ∈ FF, azimInFan x E ≤ Real.pi ∧ V ⊆ wedgeInFanGe x E

/-! ## Shared constants and tau kit (appendix.hl:75-140) -/

/-- HOL `rho_fun` (appendix.hl:80). -/
noncomputable def rhoFun (y : ℝ) : ℝ :=
  1 + (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (y - 2)

/-- HOL `Sphere.rho` (sphere.hl; used by `rho_rho_fun`). Local copy for import
hygiene — merge note: prefer a shared Sphere lane copy if one lands. -/
noncomputable def rho (y : ℝ) : ℝ := 1 + (y - 2) * (sol0 / Real.pi) / (2 * h0 - 2)

/-- HOL `rho_rho_fun` (appendix.hl:82): `rho_fun` is `Sphere.rho`. -/
theorem rho_rho_fun (y : ℝ) : rhoFun y = rho y := by
  have h20 : (2:ℝ) * h0 - 2 ≠ 0 := by norm_num [h0]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold rhoFun rho
  field_simp [h20, hpi]

/-- HOL `arc1553_v39` (appendix.hl:75); `#15.53` is the exact literal
`1553/100` and `arclength` is `arcLength` (PackingAuto18:161). -/
noncomputable def arc1553V39 : ℝ := arcLength 2 2 (Real.sqrt 15.53)

/-- HOL `cstab` (appendix.hl:78) — canonical copy (LocalAnchors carries the
bridge alias `cstabAnchor`). -/
def cstab : ℝ := 3.01

/-- HOL `tgt` (appendix.hl:106). -/
def tgt : ℝ := 1.541

/-- HOL `d_tame` (appendix.hl:108). -/
def dTame (n : ℕ) : ℝ :=
  if n = 3 then 0 else
    if n = 4 then 0.206 else
      if n = 5 then 0.4819 else
        if n = 6 then 0.712 else tgt

set_option linter.unusedVariables false in
/-- HOL `tau_fun` (appendix.hl:96); the `V` argument is unused in the body
(verbatim arity kept). -/
noncomputable def tauFun (V : Set V3) (E : Set (Set V3)) (f : Set (V3 × V3)) : ℝ :=
  setSum f (fun e => rhoFun (norm e.1) * azimInFan e E) -
    (Real.pi + sol0) * ((f.ncard - 2 : ℕ) : ℝ)

/-- HOL `tau3` (appendix.hl:98). -/
noncomputable def tau3 (v1 v2 v3 : V3) : ℝ :=
  rho (norm v1) * dihV 0 v1 v2 v3 + rho (norm v2) * dihV 0 v2 v3 v1 +
    rho (norm v3) * dihV 0 v3 v1 v2 - (Real.pi + sol0)

/-- HOL `torsor` (appendix.hl:102). -/
def Torsor {α : Type u} (s : Set α) (k : ℕ) (f : α → α) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x1 x2, x1 ∈ s → x2 ∈ s → f x1 = f x2 → x1 = x2) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧ (∀ x, x ∈ s → f^[k] x = x) ∧
    s.Finite ∧ Nat.card s = k

/-! ## The scs_v39 record lane (appendix.hl:199-260) -/

/-- HOL `periodic` (OXLZLEZ1.hl:59), universe-polymorphic so it also applies
to the predicate components `num->bool` of the scs record (Kepler.Text.periodic
covers only data types). -/
def Periodic {α : Sort u} (f : ℕ → α) (n : ℕ) : Prop := ∀ i, f (i + n) = f i

/-- HOL `periodic2` (appendix.hl:349), universe-polymorphic. -/
def Periodic2 {α : Sort u} (f : ℕ → ℕ → α) (n : ℕ) : Prop :=
  ∀ i j, f (i + n) j = f i j ∧ f i (j + n) = f i j

/-- HOL `peropp` (appendix.hl:199). -/
def peropp {α : Sort u} (f : ℕ → α) (k : ℕ) (i : ℕ) : α := f (k - (i % k + 1))

/-- HOL `peropp2` (appendix.hl:201). -/
def peropp2 {α : Sort u} (f : ℕ → ℕ → α) (k i j : ℕ) : α :=
  f (k - (i % k + 1)) (k - (j % k + 1))

/-- HOL `peropp_periodic` (appendix.hl:203). -/
theorem peropp_periodic {α : Sort u} (f : ℕ → α) (k : ℕ) :
    Periodic (peropp f k) k := fun i => by
  simp [peropp, Nat.add_mod_right]

/-- HOL `scs_v39`: the 10-component system type (`new_type_definition` over
`(k,d,a,alpha,beta,b,J,lo,hi,str)`, appendix.hl:216-228) ported as a
structure; the accessors `scs_k_v39`..`scs_str_v39` are the projections
(`part*`/`drop*` collapse), so `scs_str_v39 = SND(drop3(drop3 ...))` is just
the last field. -/
structure ScsV39 where
  /-- `scs_k_v39` -/
  k : ℕ
  /-- `scs_d_v39` -/
  d : ℝ
  /-- `scs_a_v39` -/
  a : ℕ → ℕ → ℝ
  /-- `scs_am_v39` -/
  am : ℕ → ℕ → ℝ
  /-- `scs_bm_v39` -/
  bm : ℕ → ℕ → ℝ
  /-- `scs_b_v39` -/
  b : ℕ → ℕ → ℝ
  /-- `scs_J_v39` -/
  J : ℕ → ℕ → Prop
  /-- `scs_lo_v39` -/
  lo : ℕ → Prop
  /-- `scs_hi_v39` -/
  hi : ℕ → Prop
  /-- `scs_str_v39` -/
  str : ℕ → Prop
  deriving Inhabited

/-- HOL `scs_exists` (appendix.hl:216): carrier nonemptiness feeding
`new_type_definition`; manifest for a structure. -/
theorem scs_exists : Nonempty ScsV39 := ⟨default⟩

/-- HOL `scs_components` (appendix.hl:246). -/
theorem scs_components (s : ScsV39) :
    ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str = s := rfl

/-- HOL `scs_k_v39_explicit` (appendix.hl:261). -/
theorem scs_k_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).k = k := rfl

/-- HOL `scs_d_v39_explicit` (appendix.hl:269). -/
theorem scs_d_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).d = d := rfl

/-- HOL `scs_a_v39_explicit` (appendix.hl:277). -/
theorem scs_a_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).a = a := rfl

/-- HOL `scs_am_v39_explicit` (appendix.hl:285). -/
theorem scs_am_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).am = am := rfl

/-- HOL `scs_bm_v39_explicit` (appendix.hl:293). -/
theorem scs_bm_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).bm = bm := rfl

/-- HOL `scs_b_v39_explicit` (appendix.hl:301). -/
theorem scs_b_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).b = b := rfl

/-- HOL `scs_J_v39_explicit` (appendix.hl:309). -/
theorem scs_J_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).J = J := rfl

/-- HOL `scs_lo_v39_explicit` (appendix.hl:317). -/
theorem scs_lo_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).lo = lo := rfl

/-- HOL `scs_hi_v39_explicit` (appendix.hl:325). -/
theorem scs_hi_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).hi = hi := rfl

/-- HOL `scs_str_v39_explicit` (appendix.hl:333). -/
theorem scs_str_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).str = str := rfl

/-- HOL `scs_v39_explicit` (appendix.hl:341): the ten explicit lemmas,
conjoined (`end_itlist CONJ`). -/
theorem scs_v39_explicit (k : ℕ) (d : ℝ) (a am bm b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop) (lo hi str : ℕ → Prop) :
    (ScsV39.mk k d a am bm b J lo hi str).k = k ∧
    (ScsV39.mk k d a am bm b J lo hi str).d = d ∧
    (ScsV39.mk k d a am bm b J lo hi str).a = a ∧
    (ScsV39.mk k d a am bm b J lo hi str).am = am ∧
    (ScsV39.mk k d a am bm b J lo hi str).bm = bm ∧
    (ScsV39.mk k d a am bm b J lo hi str).b = b ∧
    (ScsV39.mk k d a am bm b J lo hi str).J = J ∧
    (ScsV39.mk k d a am bm b J lo hi str).lo = lo ∧
    (ScsV39.mk k d a am bm b J lo hi str).hi = hi ∧
    (ScsV39.mk k d a am bm b J lo hi str).str = str :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `periodic_empty` (appendix.hl:387). -/
theorem periodic_empty (n : ℕ) : Periodic (fun _ => False : ℕ → Prop) n := fun _ => rfl

/-- HOL `is_scs_v39` (appendix.hl:354; the duplicated `periodic ... str`
conjunct is verbatim from the source). -/
def isScsV39 (s : ScsV39) : Prop :=
  s.d < 0.9 ∧
  3 ≤ s.k ∧
  s.k ≤ 6 ∧
  Periodic s.lo s.k ∧
  Periodic s.hi s.k ∧
  Periodic s.str s.k ∧
  Periodic s.str s.k ∧
  Periodic2 s.a s.k ∧
  Periodic2 s.am s.k ∧
  Periodic2 s.bm s.k ∧
  Periodic2 s.b s.k ∧
  Periodic2 s.J s.k ∧
  (∀ i j, s.a i j = s.a j i ∧ s.am i j = s.am j i ∧
    s.bm i j = s.bm j i ∧ s.b i j = s.b j i ∧ s.J i j = s.J j i) ∧
  (∀ i j, s.a i j ≤ s.am i j ∧ s.am i j ≤ s.bm i j ∧ s.bm i j ≤ s.b i j) ∧
  (∀ i, s.a i i = 0) ∧
  (∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j) ∧
  (∀ i, s.k = 3 → s.b i (i + 1) < 4) ∧
  (∀ i, 3 < s.k → s.b i (i + 1) ≤ cstab) ∧
  (∀ i j, s.J i j → j % s.k = (i + 1) % s.k ∨ i % s.k = (j + 1) % s.k) ∧
  (∀ i j, s.J i j → s.a i j = Real.sqrt 8 ∧ s.b i j = cstab) ∧
  {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.ncard + s.k ≤ 6

/-- HOL `unadorned_v39` (appendix.hl:384). -/
def unadornedV39 (s : ScsV39) : Prop :=
  s.lo = (fun _ => False : ℕ → Prop) ∧ s.hi = (fun _ => False : ℕ → Prop) ∧ s.str = (fun _ => False : ℕ → Prop) ∧
    s.a = s.am ∧ s.b = s.bm

/-- HOL `mk_unadorned_v39` (appendix.hl:448). -/
def mkUnadornedV39 (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ) : ScsV39 :=
  ScsV39.mk k d a a b b (fun _ _ => False) (fun _ => False : ℕ → Prop) (fun _ => False : ℕ → Prop)
    (fun _ => False : ℕ → Prop)

/-- HOL `scs_unadorned` (appendix.hl:396). -/
theorem scs_unadorned (s : ScsV39) (h : isScsV39 s) :
    isScsV39 (mkUnadornedV39 s.k s.d s.a s.b) := by
  unfold isScsV39 at h
  obtain ⟨hd, hk1, hk2, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, hdiag0, hdiag,
    hb3, hbc, -, -, hcard⟩ := h
  refine ⟨hd, hk1, hk2, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, hpa, hpa,
    hpb, hpb, fun _ _ => ⟨rfl, rfl⟩,
    fun i j => ⟨(hsym i j).1, (hsym i j).1, (hsym i j).2.2.2.1, (hsym i j).2.2.2.1, rfl⟩,
    fun i j => ⟨le_refl _, (hch i j).1.trans ((hch i j).2.1.trans (hch i j).2.2),
      le_refl _⟩,
    hdiag0, hdiag, hb3, hbc, fun _ _ hj => hj.elim, fun _ _ hj => hj.elim, hcard⟩

/-- HOL `is_ear_v39` (appendix.hl:408). -/
def isEarV39 (s : ScsV39) : Prop :=
  isScsV39 s ∧ unadornedV39 s ∧ s.k = 3 ∧ s.d = 0.11 ∧ (∀ i, s.b i i = 0) ∧
  ∃ i, {j | j < 3 ∧ s.J j (j + 1)} = {i} ∧
    s.a i (i + 1) = Real.sqrt 8 ∧ s.b i (i + 1) = cstab ∧
    (∀ j, j < 3 ∧ j ≠ i → s.a j (j + 1) = 2 ∧ s.b j (j + 1) = 2 * h0)

/-- HOL `BBs_v39 s vv` (appendix.hl:418): the scs realisation predicate over
the tuple accessors (`IMAGE vv (:num)` <-> `Set.range vv`). -/
def BBsV39 (s : ScsV39) (vv : ℕ → V3) : Prop :=
  Set.range vv ⊆ ballAnnulus ∧
  Periodic vv s.k ∧
  (∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j) ∧
  (s.k ≤ 3 ∨ ConvexLocalFan (Set.range vv)
    (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))

/-- HOL `dsv_v39` (appendix.hl:427). -/
noncomputable def dsvV39 (s : ScsV39) (vv : ℕ → V3) : ℝ :=
  s.d + 0.1 * (if isEarV39 s then 1 else -1) *
    setSum {i | i < s.k ∧ s.J i (i + 1)}
      (fun i => cstab - dist (vv i) (vv (i + 1)))

/-- HOL `dsv_J_empty` (appendix.hl:431). -/
theorem dsv_J_empty (s : ScsV39) (vv : ℕ → V3) (hJ : s.J = fun _ _ => False) :
    dsvV39 s vv = s.d := by
  unfold dsvV39
  rw [hJ]
  simp [setSum]

/-- HOL `taustar_v39` (appendix.hl:441). -/
noncomputable def taustarV39 (s : ScsV39) (vv : ℕ → V3) : ℝ :=
  if s.k ≤ 3 then tau3 (vv 0) (vv 1) (vv 2) - dsvV39 s vv
  else
    tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) - dsvV39 s vv

/-- HOL `cs_adj` (appendix.hl:451). -/
def csAdj (k : ℕ) (a1 a2 : ℝ) (i j : ℕ) : ℝ :=
  if i % k = j % k then 0
  else if j % k = (i + 1) % k ∨ (j + 1) % k = i % k then a1 else a2

/-- HOL `psort` (appendix.hl:455). -/
def psort (k : ℕ) (u : ℕ × ℕ) : ℕ × ℕ :=
  let i := u.1 % k
  let j := u.2 % k
  if i ≤ j then (i, j) else (j, i)

/- Private psort/Periodic2 toolkit for this file's `*_concl` discharges
(scsStabDiagV39/restriction bookkeeping). -/
private theorem la1psort_cases {k i j x y : ℕ} (heq : psort k (i, j) = psort k (x, y)) :
    (i % k = x % k ∧ j % k = y % k) ∨ (i % k = y % k ∧ j % k = x % k) := by
  simp only [psort] at heq
  split at heq <;> split at heq <;>
    simp only [Prod.mk.injEq] at heq
  · exact Or.inl heq
  · exact Or.inr heq
  · exact Or.inr ⟨heq.2, heq.1⟩
  · exact Or.inl ⟨heq.2, heq.1⟩

private theorem la1psort_symm (k i j : ℕ) : psort k (i, j) = psort k (j, i) := by
  simp only [psort]
  by_cases h : i % k ≤ j % k
  · by_cases h2 : j % k ≤ i % k
    · rw [Nat.le_antisymm h h2]
    · simp [h, h2]
  · have h2 : j % k ≤ i % k := Nat.le_of_lt (by omega)
    simp [h, h2]

private theorem la1psort_add_left (k : ℕ) (i j : ℕ) :
    psort k (i + k, j) = psort k (i, j) := by
  have h : (i + k) % k = i % k := by
    rw [Nat.add_comm]
    exact Nat.add_mod_left k i
  simp only [psort, h]

private theorem la1periodic2_mod {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ}
    (h : Periodic2 f k) (i j : ℕ) : f i j = f (i % k) (j % k) := by
  have step1 : ∀ (n : ℕ) (x : ℕ), f (x + n * k) j = f x j := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        have he : x + (m + 1) * k = (x + m * k) + k := by rw [Nat.succ_mul, Nat.add_assoc]
        rw [he, (h (x + m * k) j).1]
        exact ih x
  have step2 : ∀ (n : ℕ) (x y : ℕ), f x (y + n * k) = f x y := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ m ih =>
        intro x y
        have he : y + (m + 1) * k = (y + m * k) + k := by rw [Nat.succ_mul, Nat.add_assoc]
        rw [he, (h x (y + m * k)).2]
        exact ih x y
  have main1 : ∀ x : ℕ, f x j = f (x % k) j := by
    intro x
    have hx := step1 (x / k) (x % k)
    rw [Nat.mul_comm, Nat.mod_add_div] at hx
    exact hx
  have main2 : ∀ (x y : ℕ), f x y = f x (y % k) := by
    intro x y
    have hy := step2 (y / k) x (y % k)
    rw [Nat.mul_comm, Nat.mod_add_div] at hy
    exact hy
  rw [main1 i, main2]

private theorem la1periodic_mul {α : Sort u} {f : ℕ → α} {k : ℕ} (h : Periodic f k) :
    ∀ n x, f (x + n * k) = f x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      have he : x + (m + 1) * k = (x + m * k) + k := by rw [Nat.succ_mul, Nat.add_assoc]
      rw [he, h]
      exact ih x

private theorem la1periodic_mod {α : Sort u} {f : ℕ → α} {k : ℕ} (h : Periodic f k)
    (x : ℕ) : f x = f (x % k) := by
  have hx := la1periodic_mul h (x / k) (x % k)
  have he : x % k + x / k * k = x := by rw [Nat.mul_comm]; exact Nat.mod_add_div x k
  rw [he] at hx
  exact hx

/-- HOL `ASSOCD_v39` (appendix.hl:465; list recursion). Data-typed (`Type`):
the Prop-valued `J` list uses (appendix.hl:641/650 term-lets) are skipped. -/
noncomputable def assocdV39 {β : Type u} (a : ℕ × ℕ) : List ((ℕ × ℕ) × β) → β → β
  | [], d => d
  | h :: t, d => if a = h.1 then h.2 else assocdV39 a t d

/-- HOL `funlist_v39` (appendix.hl:469; `&0` diagonal). -/
noncomputable def funlistV39 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i j : ℕ) : ℝ :=
  if i % k = j % k then 0
  else assocdV39 (psort k (i, j)) (data.map (fun p => (psort k p.1, p.2))) d

/-- HOL `funlistA_v39` (appendix.hl:474; diagonal carried). Data-typed:
the `bool`-valued `J` list uses are skipped term-lets. -/
noncomputable def funlistAV39 {A : Type u} (data : List ((ℕ × ℕ) × A)) (diag : A) (dflt : A)
    (k i j : ℕ) : A :=
  if i % k = j % k then diag
  else assocdV39 (psort k (i, j)) (data.map (fun p => (psort k p.1, p.2))) dflt

/-- HOL `override` (appendix.hl:479). -/
noncomputable def override (a : ℕ → ℕ → ℝ) (k : ℕ) (u : ℕ × ℕ) (d : ℝ) (i j : ℕ) : ℝ :=
  if psort k u = psort k (i, j) then d else a i j

/-- HOL `s_init_list_v39` (appendix.hl:484): the eight initial systems
(`upperbd = &6`, `a_pro` inlined as `aPro`). -/
noncomputable def sInitListV39 : List ScsV39 :=
  let upperbd : ℝ := 6
  let aPro : ℕ → ℝ → ℝ → ℝ → ℕ → ℕ → ℝ := fun k p a1 a2 i j =>
    if i % k = j % k then 0
    else if ({i % k, j % k} : Set ℕ) = {0, 1} then p
    else if j % k = (i + 1) % k ∨ (j + 1) % k = i % k then a1 else a2
  [ mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) upperbd),
    mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) upperbd),
    mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) upperbd),
    mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) upperbd),
    mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) upperbd),
    mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) upperbd),
    mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
      (aPro 5 (Real.sqrt 8) (2 * h0) upperbd),
    mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro 4 (Real.sqrt 8) (2 * h0) upperbd)]

/-- HOL `LENGTH_s_init_list` (appendix.hl:500). -/
theorem LENGTH_s_init_list : sInitListV39.length = 8 := rfl

/-! ## JEJTVGB registry (appendix.hl:116-195)

The six statements and their `list_mk_conj` are TERM bindings in HOL
(`let X_concl = `stmt``) and `JEJTVGB_assume_v39` is the `new_definition` of
the conjunction; `ZITHLQN_concl`/`EAPGLE_concl` reference it as a PROPOSITION.
They are therefore carried as Prop-valued defs; the discharging theorems of a
later wave will take these names. -/

/-- HOL `JEJTVGB_std_concl` (appendix.hl:116). -/
def JEJTVGB_std_concl : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
    ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus →
    4 ≤ V.ncard → V.ncard ≤ 6 →
    (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w) →
    (∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0) →
    dTame V.ncard ≤ tauFun V E FF

/-- HOL `JEJTVGB_std3_concl` (appendix.hl:126). -/
def JEJTVGB_std3_concl : Prop :=
  ∀ v1 v2 v3 : V3, 2 ≤ norm v1 → 2 ≤ norm v2 → 2 ≤ norm v3 →
    norm v1 ≤ 2 * h0 → norm v2 ≤ 2 * h0 → norm v3 ≤ 2 * h0 →
    2 ≤ dist v1 v2 → 2 ≤ dist v1 v3 → 2 ≤ dist v2 v3 →
    dist v1 v2 ≤ 2 * h0 → dist v1 v3 ≤ 2 * h0 → dist v2 v3 ≤ 2 * h0 →
    0 ≤ tau3 v1 v2 v3

/-- HOL `JEJTVGB_pent_diag_concl` (appendix.hl:142). -/
def JEJTVGB_pent_diag_concl : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
    ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus →
    V.ncard = 5 →
    (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E →
      Real.sqrt 8 ≤ dist v w) →
    (∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0) →
    0.616 ≤ tauFun V E FF

/-- HOL `JEJTVGB_pent_pro_concl` (appendix.hl:152). -/
def JEJTVGB_pent_pro_concl : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
    ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus →
    V.ncard = 5 →
    (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w) →
    (∃ v0 w0 : V3, (∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({v0, w0} : Set V3) →
        2 ≤ dist v w ∧ dist v w ≤ 2 * h0) ∧ {v0, w0} ∈ E ∧
      2 * h0 ≤ dist v0 w0 ∧ dist v0 w0 ≤ Real.sqrt 8) →
    0.616 ≤ tauFun V E FF

/-- HOL `JEJTVGB_quad_pro_concl` (appendix.hl:166). -/
def JEJTVGB_quad_pro_concl : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
    ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus →
    V.ncard = 4 →
    (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E →
      Real.sqrt 8 ≤ dist v w) →
    (∃ v0 w0 : V3, (∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({v0, w0} : Set V3) →
        2 ≤ dist v w ∧ dist v w ≤ 2 * h0) ∧ {v0, w0} ∈ E ∧
      2 * h0 ≤ dist v0 w0 ∧ dist v0 w0 ≤ Real.sqrt 8) →
    0.477 ≤ tauFun V E FF

/-- HOL `JEJTVGB_quad_diag_concl` (appendix.hl:180; `0.467` is the 2013-06-03
correction). -/
def JEJTVGB_quad_diag_concl : Prop :=
  ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
    ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus →
    V.ncard = 4 →
    (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 3 ≤ dist v w) →
    (∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0) →
    0.467 ≤ tauFun V E FF

/-- HOL `JEJTVGB_concl` (appendix.hl:190): `list_mk_conj` of the six items
above, in source order. -/
def JEJTVGB_concl : Prop :=
  JEJTVGB_std_concl ∧ JEJTVGB_std3_concl ∧ JEJTVGB_pent_diag_concl ∧
    JEJTVGB_pent_pro_concl ∧ JEJTVGB_quad_pro_concl ∧ JEJTVGB_quad_diag_concl

/-- HOL `JEJTVGB_assume_v39` (appendix.hl:195): `new_definition` of the
JEJTVGB conjunction. -/
def JEJTVGB_assume_v39 : Prop := JEJTVGB_concl

/-- HOL `ZITHLQN_concl` (appendix.hl:652). Proof pending (later wave). -/
theorem ZITHLQN_concl :
    (∀ s ∈ sInitListV39, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv) →
    JEJTVGB_assume_v39 := by
  sorry

/-- HOL `min_num`: the least element of a set of naturals (`LEAST`; junk on
`∅`, rendered via choice). -/
noncomputable def minNum (S : Set ℕ) : ℕ :=
  Classical.epsilon (fun n => n ∈ S ∧ ∀ m ∈ S, n ≤ m)

/-- `minNum` spec: on a nonempty set the choice lands on an attained minimum
(well-ordering). -/
private theorem la1minNum_spec (S : Set ℕ) (hne : S.Nonempty) :
    minNum S ∈ S ∧ ∀ m ∈ S, minNum S ≤ m := by
  have hex : ∃ n : ℕ, n ∈ S ∧ ∀ m ∈ S, n ≤ m :=
    ⟨sInf S, Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩
  exact Classical.epsilon_spec hex

/-- HOL `BBprime_v39` (appendix.hl:656). -/
def BBprimeV39 (s : ScsV39) : Set (ℕ → V3) :=
  {vv | BBsV39 s vv ∧ (∀ ww, BBsV39 s ww → taustarV39 s vv ≤ taustarV39 s ww) ∧
    taustarV39 s vv < 0}

/-- HOL `BBindex_v39` (appendix.hl:659). -/
noncomputable def BBindexV39 (s : ScsV39) (vv : ℕ → V3) : ℕ :=
  {i | i < s.k ∧ s.a i (i + 1) = dist (vv i) (vv (i + 1))}.ncard

/-- HOL `BBindex_min_v39` (appendix.hl:662). -/
noncomputable def BBindexMinV39 (s : ScsV39) : ℕ :=
  minNum (BBindexV39 s '' BBprimeV39 s)

/-- HOL `BBprime2_v39` (appendix.hl:665). -/
def BBprime2V39 (s : ScsV39) : Set (ℕ → V3) :=
  {vv | vv ∈ BBprimeV39 s ∧ BBindexV39 s vv = BBindexMinV39 s}

/-- HOL `MMs_v39` (appendix.hl:668). -/
def MMsV39 (s : ScsV39) : Set (ℕ → V3) :=
  {vv | vv ∈ BBprime2V39 s ∧
    (∀ i, s.str i → azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) = Real.pi) ∧
    (∀ i, s.lo i → norm (vv i) = 2) ∧
    (∀ i, s.hi i → norm (vv i) = 2 * h0) ∧
    (∀ i j, s.am i j ≤ dist (vv i) (vv j)) ∧
    (∀ i j, dist (vv i) (vv j) ≤ s.bm i j)}

/-- `BBindex_min` is dominated by every `BBprime` index. -/
private theorem la1bbindexMin_le (s : ScsV39) {v : ℕ → V3} (hv : v ∈ BBprimeV39 s) :
    BBindexMinV39 s ≤ BBindexV39 s v := by
  have himg : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨BBindexV39 s v, v, hv, rfl⟩
  exact (la1minNum_spec _ himg).2 _ ⟨v, hv, rfl⟩

/-- `BBindex_min` is attained (at a `BBprime` member). -/
private theorem la1bbindexMin_attained (s : ScsV39) (z : ℕ → V3)
    (hz : z ∈ BBprimeV39 s) : ∃ w, w ∈ BBprimeV39 s ∧ BBindexV39 s w = BBindexMinV39 s := by
  have himg : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨BBindexV39 s z, z, hz, rfl⟩
  obtain ⟨hmin, -⟩ := la1minNum_spec _ himg
  obtain ⟨w, hw, hwval⟩ := hmin
  exact ⟨w, hw, hwval⟩

/-- Two `BBprime` members have equal `taustar` (mutual domination). -/
private theorem la1bbprime_taustar_eq {s : ScsV39} {v w : ℕ → V3}
    (hv : v ∈ BBprimeV39 s) (hw : w ∈ BBprimeV39 s) : taustarV39 s v = taustarV39 s w :=
  le_antisymm (hv.2.1 w hw.1) (hw.2.1 v hv.1)

/-- HOL `unadorned_MMs_concl` (appendix.hl:676). Discharged 2026-09-30
(LocalAuto1 lane): unadorned kills the str/lo/hi clauses and identifies the
am/bm clauses with the BBs bounds. -/
theorem unadorned_MMs_concl :
    ∀ s : ScsV39, unadornedV39 s → MMsV39 s = BBprime2V39 s := by
  intro s ⟨hlo, hhi, hstr, ham, hbm⟩
  ext vv
  simp only [MMsV39, BBprime2V39, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hb2, -, -, -, -, -⟩
    exact hb2
  · rintro ⟨⟨hBB, hmin, hneg⟩, hidx⟩
    refine ⟨⟨⟨hBB, hmin, hneg⟩, hidx⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hstr] at hi
      exact hi.elim
    · intro i hi
      rw [hlo] at hi
      exact hi.elim
    · intro i hi
      rw [hhi] at hi
      exact hi.elim
    · intro i j
      exact ham ▸ (hBB.2.2.1 i j).1
    · intro i j
      exact hbm ▸ (hBB.2.2.1 i j).2

/-- HOL `XWITCCN_concl` (appendix.hl:679). Proof pending. -/
theorem XWITCCN_concl : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅ := by
  sorry

/-- HOL `XWITCCN2_concl` (appendix.hl:682). Proof pending. -/
theorem XWITCCN2_concl : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ := by
  sorry

/-- HOL `AYQJTMD_concl` (appendix.hl:685). Proof pending. -/
theorem AYQJTMD_concl : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ := by
  sorry

/-- HOL `EAPGLE_concl` (appendix.hl:688). Proof pending. -/
theorem EAPGLE_concl :
    (∀ s ∈ sInitListV39, MMsV39 s = ∅) → JEJTVGB_assume_v39 := by
  sorry

/-- HOL `scs_M` (appendix.hl:875). -/
def scsM (s : ScsV39) : Set ℕ :=
  {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}

/-- HOL `scs_basic_v39` (appendix.hl:834; the `scs_basic` new_definition). -/
def scsBasicV39 (s : ScsV39) : Prop :=
  unadornedV39 s ∧ ∀ i j, s.J i j = False

/-- HOL `scs_inj` (appendix.hl:837). -/
theorem scs_inj (s s' : ScsV39) (h1 : scsBasicV39 s) (h1' : scsBasicV39 s')
    (hd : s.d = s'.d) (hk : s.k = s'.k) (ha : s.a = s'.a) (hb : s.b = s'.b) :
    s = s' := by
  obtain ⟨hu, hJ⟩ := h1
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  obtain ⟨hu', hJ'⟩ := h1'
  obtain ⟨hlo', hhi', hstr', ham', hbm'⟩ := hu'
  have hJeq : ∀ i j, s.J i j = False := hJ
  have hJeq' : ∀ i j, s'.J i j = False := hJ'
  have e : s = ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str := rfl
  have e' : s' = ScsV39.mk s'.k s'.d s'.a s'.am s'.bm s'.b s'.J s'.lo s'.hi s'.str := rfl
  rw [e, e', ScsV39.mk.injEq]
  refine ⟨hk, hd, ha, ?_, ?_, hb, ?_, ?_, ?_, ?_⟩
  · exact ham.symm.trans (ha.trans ham')
  · exact hbm.symm.trans (hb.trans hbm')
  · exact funext fun i => funext fun j => (hJeq i j).trans (hJeq' i j).symm
  · exact hlo.trans hlo'.symm
  · exact hhi.trans hhi'.symm
  · exact hstr.trans hstr'.symm

/-! ## Arrow / slice / restriction toolkit (appendix.hl:704-833) -/

/-- HOL `scs_generic` (appendix.hl:821). -/
def scsGeneric (v : ℕ → V3) : Prop :=
  Generic (Set.range v) (Set.range fun i => {v i, v (i + 1)})

/-- HOL `scs_is_str` (appendix.hl:825). -/
def scsIsStr (s : ScsV39) (vv : ℕ → V3) (i : ℕ) : Prop :=
  azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) = Real.pi

/-- HOL `scs_arrow_v39` (appendix.hl:804). -/
def scsArrowV39 (S1 S2 : Set ScsV39) : Prop :=
  (∀ s ∈ S2, isScsV39 s) ∧
    ((∀ s ∈ S1, MMsV39 s = ∅) ∨ ∃ s ∈ S2, MMsV39 s ≠ ∅)

/-- HOL `scs_diag` (appendix.hl:769). -/
def scsDiag (k i j : ℕ) : Prop :=
  ¬(i % k = j % k) ∧ ¬((i + 1) % k = j % k) ∧ ¬(i % k = (j + 1) % k)

/-- A diagonal pair never lands in the psort-class of an adjacent pair
(`x, x+1`); key step for the neighbour-preservation of `scsStabDiagV39`. -/
private theorem la1psort_diag (k : ℕ) {i j x : ℕ} (hd : scsDiag k i j)
    (heq : psort k (i, j) = psort k (x, x + 1)) : False := by
  obtain hc | hc := la1psort_cases heq
  · refine hd.2.1 ?_
    rw [← Nat.mod_add_mod i k 1, hc.1, hc.2]
    exact Nat.mod_add_mod x k 1
  · refine hd.2.2 ?_
    rw [← Nat.mod_add_mod j k 1, hc.1, hc.2]
    exact (Nat.mod_add_mod x k 1).symm

/-- `csAdj 6 a1 a2` is constant on a `psort`-class of a diagonal pair
(`scsDiag`): the class never lands on the 0/adjacent slots, so the value is
the far constant `a2` throughout the class. -/
private theorem la1csAdj_diag6 {a1 a2 : ℝ} {i j x y : ℕ}
    (hxy : (x % 6 = i % 6 ∧ y % 6 = j % 6) ∨ (x % 6 = j % 6 ∧ y % 6 = i % 6))
    (hd : scsDiag 6 i j) : csAdj 6 a1 a2 x y = a2 := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [csAdj, h1, h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl
  · simp only [csAdj, h1, h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl

/-- HOL `scs_stab_diag_v39` (appendix.hl:828). -/
noncomputable def scsStabDiagV39 (s : ScsV39) (i j : ℕ) : ScsV39 :=
  let k := s.k
  let b' : ℕ → ℕ → ℝ := fun i' j' =>
    if psort k (i, j) = psort k (i', j') then cstab else s.b i' j'
  mkUnadornedV39 k s.d s.a b'

/-- HOL `scs_half_slice_v39` (appendix.hl:776). -/
noncomputable def scsHalfSliceV39 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop) :
    ScsV39 :=
  let p' := p % s.k
  let k' := (q + 1 + (s.k - p')) % s.k
  let mod2 : (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ := fun f j j' => f (j % k' + p') (j' % k' + p')
  let mod2b : (ℕ → ℕ → Prop) → ℕ → ℕ → Prop := fun f j j' =>
    f (j % k' + p') (j' % k' + p')
  let a1 : ℕ → ℕ → ℝ := fun i'' j'' =>
    if ({i'' % k', j'' % k'} : Set ℕ) = {0, k' - 1} then s.am p q
    else mod2 s.a i'' j''
  let b1 : ℕ → ℕ → ℝ := fun i'' j'' =>
    if ({i'' % k', j'' % k'} : Set ℕ) = {0, k' - 1} then s.bm p q
    else mod2 s.b i'' j''
  let J : ℕ → ℕ → Prop := fun i'' j'' =>
    if ({i'' % k', j'' % k'} : Set ℕ) = {0, k' - 1} then mkj
    else mod2b s.J i'' j''
  ScsV39.mk k' d' a1 a1 b1 b1 J (fun _ => False) (fun _ => False)
    (fun _ => False)

/-- HOL `scs_slice_v39` (appendix.hl:788). -/
noncomputable def scsSliceV39 (s : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop) :
    ScsV39 × ScsV39 :=
  (scsHalfSliceV39 s p q d' mkj, scsHalfSliceV39 s q p d'' mkj)

/-- HOL `is_scs_slice_v39` (appendix.hl:792). -/
noncomputable def isScsSliceV39 (s s' s'' : ScsV39) (p q : ℕ) : Prop :=
  let d' := s'.d
  let d'' := s''.d
  let mkj := s'.J 0 (s'.k - 1)
  (s', s'') = scsSliceV39 s p q d' d'' mkj ∧ d' < 0.9 ∧ d'' < 0.9 ∧
    s.d ≤ d' + d'' ∧ s.bm p q < 4 ∧ (s.k = 4 ∨ s.bm p q ≤ cstab) ∧
    (mkj → (isEarV39 s' ∨ isEarV39 s''))

/-- HOL `scs_prop_equ_v39` (appendix.hl:755). -/
def scsPropEquV39 (s : ScsV39) (i : ℕ) : ScsV39 :=
  ScsV39.mk s.k s.d (fun j j' => s.a (i + j) (i + j'))
    (fun j j' => s.am (i + j) (i + j')) (fun j j' => s.bm (i + j) (i + j'))
    (fun j j' => s.b (i + j) (i + j')) (fun j j' => s.J (i + j) (i + j'))
    (fun j => s.lo (i + j)) (fun j => s.hi (i + j)) (fun j => s.str (i + j))

/-- HOL `scs_opp_v39` (appendix.hl:763). -/
def scsOppV39 (s : ScsV39) : ScsV39 :=
  let k := s.k
  ScsV39.mk s.k s.d (peropp2 s.a k) (peropp2 s.am k) (peropp2 s.bm k) (peropp2 s.b k)
    (peropp2 s.J k) (peropp s.lo k) (peropp s.hi k) (peropp s.str k)

/-- HOL `transfer_v39` (appendix.hl:744). -/
def transferV39 (s t : ScsV39) : Prop :=
  (isEarV39 s → s = t) ∧ isScsV39 t ∧ unadornedV39 t ∧ s.d ≤ t.d ∧ t.k = s.k ∧
    (∀ i j, t.a i j ≤ s.a i j) ∧ (∀ i j, s.b i j ≤ t.b i j) ∧
    (∀ i j, t.J i j → s.J i j)

/-- HOL `restriction_typ1_v39` (appendix.hl:716). -/
def restrictionTyp1V39 (s : ScsV39) : ScsV39 :=
  ScsV39.mk s.k s.d s.a s.am s.bm s.bm s.J s.lo s.hi s.str

/-- HOL `restriction_typ2_v39` (appendix.hl:719). -/
def restrictionTyp2V39 (s : ScsV39) : ScsV39 :=
  ScsV39.mk s.k s.d s.am s.am s.am s.am s.J s.lo s.hi s.str

/-- HOL `restriction_cs1_v39` (appendix.hl:723). -/
noncomputable def restrictionCs1V39 (s : ScsV39) (p q : ℕ) (c : ℝ) : ScsV39 :=
  let b1 := override s.b s.k (p, q) c
  let bm := if c < s.bm p q then override s.bm s.k (p, q) c else s.bm
  ScsV39.mk s.k s.d s.a s.am bm b1 s.J s.lo s.hi s.str

/-- HOL `restriction_cs2_v39` (appendix.hl:730). -/
noncomputable def restrictionCs2V39 (s : ScsV39) (p q : ℕ) (c : ℝ) : ScsV39 :=
  let a1 := override s.a s.k (p, q) c
  let am := if s.am p q < c then override s.am s.k (p, q) c else s.am
  ScsV39.mk s.k s.d a1 am s.bm s.b s.J s.lo s.hi s.str

/-- HOL `subdiv_v39` (appendix.hl:737). -/
noncomputable def subdivV39 (s : ScsV39) (p q : ℕ) (c : ℝ) : List ScsV39 :=
  if c ≤ s.a p q then [s]
  else if c ≤ s.am p q then [restrictionCs2V39 s p q c]
  else if c < s.bm p q then [restrictionCs1V39 s p q c, restrictionCs2V39 s p q c]
  else if c < s.b p q then [restrictionCs1V39 s p q c] else [s]

/-- HOL `xrr` (appendix.hl:809). -/
noncomputable def xrr (y1 y2 y6 : ℝ) : ℝ :=
  8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))

/-- HOL `scs_basic3` (appendix.hl:811). -/
noncomputable def scsBasic3 (d a01 b01 a02 b02 a12 b12 : ℝ) : ScsV39 :=
  let a := funlistV39 [((0, 1), a01), ((0, 2), a02), ((1, 2), a12)] 0 3
  let b := funlistV39 [((0, 1), b01), ((0, 2), b02), ((1, 2), b12)] 0 3
  mkUnadornedV39 3 d a b

/-- HOL `scs_basic4` (appendix.hl:816). -/
noncomputable def scsBasic4 (d a01 b01 a02 b02 a03 b03 a12 b12 a13 b13 a23 b23 : ℝ) :
    ScsV39 :=
  let a := funlistV39 [((0, 1), a01), ((0, 2), a02), ((0, 3), a03), ((1, 2), a12),
      ((1, 3), a13), ((2, 3), a23)] 0 4
  let b := funlistV39 [((0, 1), b01), ((0, 2), b02), ((0, 3), b03), ((1, 2), b12),
      ((1, 3), b13), ((2, 3), b23)] 0 4
  mkUnadornedV39 4 d a b

/- `deltaX4`/`deltaX5` (HOL `delta_x4`/`delta_x5`, sphere.hl:110 / Nonlin_def.hl:435)
are canonical in `Kepler.Text.SphereKit` (imported above; `deltaX5` there is the
corrected 6-term body — DEDUP 2026-09-17, local copies removed to fix the
co-import clash). `mkSimplex1` below resolves against the canonical defs. -/

/-- HOL `mk_simplex1` (appendix.hl:862); `cross` <-> `cross3`
(PackingAuto18:86), `%` <-> `•`. BODY-FIX 2026-09-17: the `d5` coefficient
now picks up the corrected `deltaX5` (was the 4-term mis-port), so this
def's value has changed; the body is unchanged. -/
noncomputable def mkSimplex1 (v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ) : V3 :=
  let uinv := 1 / upsX x1 x2 x6
  let d := deltaX x1 x2 x3 x4 x5 x6
  let d5 := deltaX5 x1 x2 x3 x4 x5 x6
  let d4 := deltaX4 x1 x2 x3 x4 x5 x6
  let vcross := cross3 (v1 - v0) (v2 - v0)
  v0 + uinv • ((2 * Real.sqrt d) • vcross + d5 • (v1 - v0) + d4 • (v2 - v0))

/-- HOL `mk_planar2` (appendix.hl:870); flyspeck `mk_planar` is identified
with this def at the EYYPQDW2/EYYPQDW3 call sites (same argument shape). -/
noncomputable def mkPlanar2 (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ) : V3 :=
  let vcross := cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0))
  v0 + ((x1 + x3 - x5) / (2 * x1)) • (v1 - v0) +
    ((s / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) • vcross

/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:24-44): the closed
conjunction of `Main_estimate` inequalities built from the nonlinear
chapter's Ineq database (see `LocalAnchors.MainNonlinearTerminalV11` for the
visible box shape). Registry: `sorry`-typed Prop until that lane lands. -/
def main_nonlinear_terminal_v11 : Prop := sorry

/-! ## Conclusions, part 1 (appendix.hl:25-59, 679-714, 1089-1108) -/

/-- HOL `FZIOTEF_REFL` (appendix.hl:1089). -/
theorem FZIOTEF_REFL (S : Set ScsV39) (h : ∀ s ∈ S, isScsV39 s) :
    scsArrowV39 S S := by
  refine ⟨h, ?_⟩
  by_cases hex : ∃ s ∈ S, MMsV39 s ≠ ∅
  · exact Or.inr hex
  · exact Or.inl fun s hs => by
      by_contra hne
      exact hex ⟨s, hs, hne⟩

/-- HOL `FZIOTEF_TRANS` (appendix.hl:1098). -/
theorem FZIOTEF_TRANS (S1 S2 S3 : Set ScsV39) (h12 : scsArrowV39 S1 S2)
    (h23 : scsArrowV39 S2 S3) : scsArrowV39 S1 S3 := by
  refine ⟨h23.1, ?_⟩
  by_cases hex1 : ∃ s ∈ S1, MMsV39 s ≠ ∅
  · obtain ⟨s, hs1, hsne⟩ := hex1
    rcases h12.2 with hempty12 | ⟨t, ht2, htne⟩
    · exact absurd (hempty12 s hs1) hsne
    rcases h23.2 with hempty23 | ⟨u, hu3, hune⟩
    · exact absurd (hempty23 t ht2) htne
    · exact Or.inr ⟨u, hu3, hune⟩
  · exact Or.inl fun s hs1 => by
      by_contra hne
      exact hex1 ⟨s, hs1, hne⟩

/-- HOL `JKQEWGV1_concl` (appendix.hl:690). Proof pending. -/
theorem JKQEWGV1_concl : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s → BBsV39 s vv →
    taustarV39 s vv < 0 → 3 < s.k →
    solLocal (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) < Real.pi := by
  sorry

/-- HOL `JKQEWGV2_concl` (appendix.hl:695). Proof pending. -/
theorem JKQEWGV2_concl : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s → BBsV39 s vv →
    taustarV39 s vv < 0 → 3 < s.k →
    ¬Circular (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)}) := by
  sorry

/-- HOL `JKQEWGV3_concl` (appendix.hl:702). Proof pending. -/
theorem JKQEWGV3_concl : ∀ (s : ScsV39) (vv : ℕ → V3) (v w : V3),
    isScsV39 s → BBsV39 s vv → taustarV39 s vv < 0 → Lunar v w (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) → 3 < s.k →
    interiorAngle1 0 (Set.range fun i => (vv i, vv (i + 1))) v < Real.pi / 2 := by
  sorry

/-- HOL `HFNXPZA_concl` (appendix.hl:710). Proof pending. -/
theorem HFNXPZA_concl : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s → BBsV39 s vv →
    taustarV39 s vv < 0 → s.k = 3 →
    dihV 0 (vv 0) (vv 1) (vv 2) + dihV 0 (vv 1) (vv 2) (vv 3) +
      dihV 0 (vv 2) (vv 3) (vv 1) < 2 * Real.pi := by
  sorry

/-! ## Conclusions, part 2 (appendix.hl:25-59, 1110-1207) -/

/-- HOL `derived_form t f f' x s` (Calc_derivative kit): the side-condition
`t` carried as antecedent; `f'` is the slope value at `x` (DRNDRDV passes a
number; cf. `derivedFormP22`, PackingAuto22:137, for the function-valued
rendering). -/
def derivedForm (T : Prop) (f : ℝ → ℝ) (f' x : ℝ) (s : Set ℝ) : Prop :=
  T → HasDerivWithinAt f f' s x

/-- HOL `MHAEYJN_concl` (appendix.hl:25). Proof pending (Lunar_deform lane). -/
theorem MHAEYJN_concl :
    ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (f : V3 → ℝ → V3) (v w u : V3),
      ConvexLocalFan V E FF →
      Lunar v w V E →
      Deformation f V a b →
      interiorAngle1 0 FF v < Real.pi →
      u ∈ V → u ≠ v → u ≠ w →
      (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
      (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
        ConvexLocalFan ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
        Lunar v w ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E) := by
  sorry

/-- HOL `ZLZTHIC_concl` (appendix.hl:45). Proof pending. -/
theorem ZLZTHIC_concl :
    ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (f : V3 → ℝ → V3),
      ConvexLocalFan V E FF →
      Generic V E →
      Deformation f V a b →
      (∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
        interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
        ConvexLocalFan ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
        Generic ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E) := by
  sorry

/-- HOL `VPWSHTO_concl` (appendix.hl:62; the duplicated `u1 IN ...` conjunct
is verbatim from the source). Proof pending. -/
theorem VPWSHTO_concl : ∀ v x u w w1 : V3,
    ({v, x, u, w, w1} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({v, x, u, w, w1} : Set V3) →
    v ≠ x → v ≠ u → v ≠ w → v ≠ w1 → x ≠ u → x ≠ w → x ≠ w1 → u ≠ w → u ≠ w1 →
    w ≠ w1 →
    norm (v - x) = 2 → norm (x - u) = 2 → norm (u - w) = 2 →
    norm (w - w1) = 2 → norm (w1 - v) = 2 →
    ∃ v1 u1 w2 : V3,
      u1 ∈ ({v, x, u, w, w1} : Set V3) ∧ u1 ∈ ({v, x, u, w, w1} : Set V3) ∧
      w2 ∈ ({v, x, u, w, w1} : Set V3) ∧ v1 ≠ u1 ∧ u1 ≠ w2 ∧ v1 ≠ w2 ∧
      2 < dist v1 u1 ∧ 2 < dist v1 w2 ∧
      dist v1 u1 ≤ 1 + Real.sqrt 5 ∧ dist v1 w2 ≤ 1 + Real.sqrt 5 := by
  sorry

/-- HOL `EQTTNZI1_concl` (appendix.hl:1110). Discharged 2026-09-30
(LocalAuto1 lane): the b:=bm restriction preserves `is_scs_v39` (monotone card
sub-count) and every `MMs_v39` realization transports (`is_ear` fails on both
sides since J-values force the 3-face to be empty-or-full). -/
theorem EQTTNZI1_concl : ∀ s : ScsV39, isScsV39 s →
    (∀ i j, s.J i j → s.b i j = s.bm i j) →
    (s.J = fun _ _ => False ∨ 3 < s.k) →
    scsArrowV39 {s} {restrictionTyp1V39 s} := by
  intro s his hJe hJcase
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := his
  -- as written (statement frozen), the hypothesis says s.J i j = (3 < s.k)
  have hJval : ∀ i j, s.J i j = (3 < s.k) := by
    intro i j
    rw [hJcase]
    simp
  -- is_scs for the restriction (b-slot := bm)
  have hisT : isScsV39 (restrictionTyp1V39 s) := by
    refine ⟨h1, h2, h3, h4, h5, h7, h7, h8, h9, h10, h10, h12,
      fun i j => ⟨(h13 i j).1, (h13 i j).2.1, (h13 i j).2.2.1, (h13 i j).2.2.1,
        (h13 i j).2.2.2.2⟩,
      fun i j => ⟨(h14 i j).1, (h14 i j).2.1, le_refl _⟩,
      h15, h16,
      fun i hk3 => ((h14 i (i + 1)).2.2).trans_lt (h17 i hk3),
      fun i hk3 => ((h14 i (i + 1)).2.2).trans (h18 i hk3),
      fun i j hj => h19 i j hj,
      fun i j hj => ⟨(h20 i j hj).1, (hJe i j hj).symm.trans (h20 i j hj).2⟩,
      ?_⟩
    have hsub : {i : ℕ | i < s.k ∧ (2 * h0 < s.bm i (i + 1) ∨ 2 < s.a i (i + 1))} ⊆
        {i : ℕ | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} := by
      rintro i ⟨hlt, hval⟩
      rcases hval with hv | hv
      · exact ⟨hlt, Or.inl (lt_of_lt_of_le hv ((h14 i (i + 1)).2.2))⟩
      · exact ⟨hlt, Or.inr hv⟩
    have hfin : {i : ℕ | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.Finite :=
      Set.Finite.subset (Set.finite_Iio s.k) (fun i hi => hi.1)
    have hle := Set.ncard_le_ncard hsub hfin
    exact (Nat.add_le_add_right hle s.k).trans h21
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hisT
  · by_cases hMMe : MMsV39 s = ∅
    · refine Or.inl ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hMMe
    · refine Or.inr ⟨restrictionTyp1V39 s, Set.mem_singleton _, ?_⟩
      obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hMMe
      simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
      obtain ⟨⟨⟨hBBs, hmin, hneg⟩, hidx⟩, hstrc, hloc, hhic, hamc, hbmc⟩ := hv
      -- neither system is an ear: J-values forbid the singleton-3 face
      have hJTval : ∀ i j, (restrictionTyp1V39 s).J i j = (3 < s.k) := hJval
      have hnoearS : ¬isEarV39 s := by
        intro hex
        obtain ⟨i, hi, -, -, -⟩ := hex.2.2.2.2.2
        have h0 : (0:ℕ) ∈ {j | j < 3 ∧ s.J j (j + 1)} ↔ (3 < s.k) := by
          constructor
          · intro hm; exact Eq.mp (hJval 0 1) (Set.mem_setOf.mp hm).right
          · intro h3lt; exact Set.mem_setOf.mpr ⟨by omega, Eq.mp (hJval 0 1).symm h3lt⟩
        have h1 : (1:ℕ) ∈ {j | j < 3 ∧ s.J j (j + 1)} ↔ (3 < s.k) := by
          constructor
          · intro hm; exact Eq.mp (hJval 1 2) (Set.mem_setOf.mp hm).right
          · intro h3lt; exact Set.mem_setOf.mpr ⟨by omega, Eq.mp (hJval 1 2).symm h3lt⟩
        by_cases hk3lt : 3 < s.k
        · have m0 := h0.2 hk3lt
          rw [hi] at m0
          simp at m0
          have m1 := h1.2 hk3lt
          rw [hi] at m1
          simp at m1
          omega
        · have hne : {j | j < 3 ∧ s.J j (j + 1)} = ∅ := by
            ext j
            simp [hJval j (j + 1), hk3lt]
          exact absurd (Set.mem_singleton i) (by rw [← hi]; rw [hne]; simp)
      have hJTval : ∀ i j, (restrictionTyp1V39 s).J i j = (3 < s.k) := hJval
      have hnoearT : ¬isEarV39 (restrictionTyp1V39 s) := by
        intro hex
        obtain ⟨i, hi, -, -, -⟩ := hex.2.2.2.2.2
        have h0 : (0:ℕ) ∈ {j | j < 3 ∧ (restrictionTyp1V39 s).J j (j + 1)} ↔ (3 < s.k) := by
          constructor
          · intro hm; exact Eq.mp (hJTval 0 1) (Set.mem_setOf.mp hm).right
          · intro h3lt; exact Set.mem_setOf.mpr ⟨by omega, Eq.mp (hJTval 0 1).symm h3lt⟩
        have h1 : (1:ℕ) ∈ {j | j < 3 ∧ (restrictionTyp1V39 s).J j (j + 1)} ↔ (3 < s.k) := by
          constructor
          · intro hm; exact Eq.mp (hJTval 1 2) (Set.mem_setOf.mp hm).right
          · intro h3lt; exact Set.mem_setOf.mpr ⟨by omega, Eq.mp (hJTval 1 2).symm h3lt⟩
        by_cases hk3lt : 3 < s.k
        · have m0 := h0.2 hk3lt
          rw [hi] at m0
          simp at m0
          have m1 := h1.2 hk3lt
          rw [hi] at m1
          simp at m1
          omega
        · have hne : {j | j < 3 ∧ (restrictionTyp1V39 s).J j (j + 1)} = ∅ := by
            ext j
            simp [hJTval j (j + 1), hk3lt]
          exact absurd (Set.mem_singleton i) (by rw [← hi]; rw [hne]; simp)
      -- taustar transport
      -- taustar transport
      -- taustar transport (dsv is literally shared)
      have hdsvT : ∀ x : ℕ → V3, dsvV39 (restrictionTyp1V39 s) x = dsvV39 s x := by
        intro x
        unfold dsvV39
        rw [if_neg hnoearT, if_neg hnoearS]
        rfl
      have htauT : ∀ x : ℕ → V3, taustarV39 (restrictionTyp1V39 s) x = taustarV39 s x := by
        intro x
        unfold taustarV39
        rw [hdsvT x]
        rfl
      have hBBsub : ∀ x, BBsV39 (restrictionTyp1V39 s) x → BBsV39 s x := by
        intro x hx
        refine ⟨hx.1, hx.2.1, ?_, hx.2.2.2⟩
        intro i j
        exact ⟨(hx.2.2.1 i j).1, (hx.2.2.1 i j).2.trans (h14 i j).2.2⟩
      have hBBsT : BBsV39 (restrictionTyp1V39 s) v := by
        refine ⟨hBBs.1, hBBs.2.1, ?_, hBBs.2.2.2⟩
        intro i j
        exact ⟨(hBBs.2.2.1 i j).1, hbmc i j⟩
      have hminT : ∀ y, BBsV39 (restrictionTyp1V39 s) y →
          taustarV39 (restrictionTyp1V39 s) v ≤ taustarV39 (restrictionTyp1V39 s) y := by
        intro y hy
        rw [htauT v, htauT y]
        exact hmin y (hBBsub y hy)
      have hnegT : taustarV39 (restrictionTyp1V39 s) v < 0 := by
        rw [htauT v]
        exact hneg
      have hv'T : v ∈ BBprimeV39 (restrictionTyp1V39 s) := ⟨hBBsT, hminT, hnegT⟩
      -- the BBindex minimum is attained and shared
      have himgT : (BBindexV39 (restrictionTyp1V39 s) ''
          BBprimeV39 (restrictionTyp1V39 s)).Nonempty :=
        ⟨BBindexV39 (restrictionTyp1V39 s) v, v, hv'T, rfl⟩
      obtain ⟨hmin0, hminle⟩ := la1minNum_spec _ himgT
      obtain ⟨w, hw, hwval⟩ := hmin0
      obtain ⟨hBBw, hminw, hnegw⟩ := hw
      have htw : taustarV39 s w = taustarV39 s v := by
        have q1 : taustarV39 (restrictionTyp1V39 s) w ≤
            taustarV39 (restrictionTyp1V39 s) v := hminw v hBBsT
        have q2 : taustarV39 s v ≤ taustarV39 s w := hmin w (hBBsub w hBBw)
        rw [htauT w, htauT v] at q1
        linarith [q1, q2]
      have hwS : w ∈ BBprimeV39 s := by
        refine ⟨hBBsub w hBBw, ?_, ?_⟩
        · intro y hy
          rw [htw]
          exact hmin y hy
        · rw [htw]
          exact hneg
      have himgS : (BBindexV39 s '' BBprimeV39 s).Nonempty :=
        ⟨BBindexV39 s v, v, ⟨hBBs, hmin, hneg⟩, rfl⟩
      have hspecS := la1minNum_spec _ himgS
      have hle : BBindexMinV39 (restrictionTyp1V39 s) ≤
          BBindexV39 (restrictionTyp1V39 s) v := hminle _ ⟨v, hv'T, rfl⟩
      have hBBI : ∀ x, BBindexV39 (restrictionTyp1V39 s) x = BBindexV39 s x := fun _ => rfl
      have h5 : BBindexMinV39 s ≤ BBindexV39 s w := hspecS.2 _ ⟨w, hwS, rfl⟩
      have h3 : BBindexV39 (restrictionTyp1V39 s) v ≤
          BBindexMinV39 (restrictionTyp1V39 s) := by
        rw [hBBI v, hidx]
        show BBindexMinV39 s ≤
          minNum (BBindexV39 (restrictionTyp1V39 s) '' BBprimeV39 (restrictionTyp1V39 s))
        exact h5.trans (le_of_eq ((hBBI w).symm.trans hwval))
      have hidxT : BBindexV39 (restrictionTyp1V39 s) v =
          BBindexMinV39 (restrictionTyp1V39 s) := le_antisymm h3 hle
      exact Set.nonempty_iff_ne_empty.mp
        ⟨v, ⟨⟨⟨hBBsT, hminT, hnegT⟩, hidxT⟩, fun i hi => hstrc i hi,
          fun i hi => hloc i hi, fun i hi => hhic i hi, fun i j => hamc i j,
          fun i j => hbmc i j⟩⟩

/-- HOL `EQTTNZI2_concl` (appendix.hl:1115). Discharged 2026-10-08
(LocalAuto1 lane): `¬J` empties both `dsv` sums (equal `taustar` on `s` and
the typ2 restriction), and the `MMs` am/bm-clauses plus `am = bm` force every
`MMs s` realization to realize `s.am` exactly, which is precisely the `BBs`
bound pair of the typ2 restriction (all four bound functions are `s.am`). -/
theorem EQTTNZI2_concl : ∀ (s t : ScsV39), isScsV39 s → s.am = s.bm →
    t = restrictionTyp2V39 s → (∀ i j, ¬s.J i j) → (∀ i, s.am i i = 0) →
    {i | i < t.k ∧ (2 * h0 < t.b i (i + 1) ∨ 2 < t.a i (i + 1))}.ncard + t.k ≤ 6 →
    scsArrowV39 {s} {t} := by
  intro s t his hambm ht hnoJ ham0 hcard
  subst ht
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21⟩ := his
  have hisT : isScsV39 (restrictionTyp2V39 s) :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h9, h9, h9, h9, h12,
      fun i j => ⟨(h13 i j).2.1, (h13 i j).2.1, (h13 i j).2.1, (h13 i j).2.1,
        (h13 i j).2.2.2.2⟩,
      fun i j => ⟨le_refl _, le_refl _, le_refl _⟩, ham0,
      fun i j hij => (h16 i j hij).trans (h14 i j).1,
      fun i hk3 => ((h14 i (i + 1)).2.1.trans ((h14 i (i + 1)).2.2)).trans_lt (h17 i hk3),
      fun i hk3 => (h14 i (i + 1)).2.1.trans ((h14 i (i + 1)).2.2.trans (h18 i hk3)),
      fun i j hj => absurd hj (hnoJ i j), fun i j hj => absurd hj (hnoJ i j), hcard⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hisT
  · by_cases hMMe : MMsV39 s = ∅
    · refine Or.inl ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hMMe
    · obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hMMe
      simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
      have hBBs := hv.1.1.1
      have hmin := hv.1.1.2.1
      have hneg := hv.1.1.2.2
      have hidx := hv.1.2
      have hstrc := hv.2.1
      have hloc := hv.2.2.1
      have hhic := hv.2.2.2.1
      have hamc := hv.2.2.2.2.1
      have hbmc := hv.2.2.2.2.2
      obtain ⟨hBBr, hBBp, hBBb, hBBf⟩ := hBBs
      -- both J-sums of `dsv` are empty, so taustar agrees on s and its typ2 restriction
      have hJset : {i : ℕ | i < s.k ∧ s.J i (i + 1)} = ∅ := by
        ext i
        simp [hnoJ]
      have htauT : ∀ w : ℕ → V3,
          taustarV39 (restrictionTyp2V39 s) w = taustarV39 s w := by
        intro w
        have hdT : dsvV39 (restrictionTyp2V39 s) w = s.d := by
          simp only [dsvV39, restrictionTyp2V39, hJset]
          simp [setSum]
        have hdS : dsvV39 s w = s.d := by
          simp only [dsvV39, hJset]
          simp [setSum]
        unfold taustarV39
        rw [hdT, hdS]
        rfl
      have hBBsT : BBsV39 (restrictionTyp2V39 s) v :=
        ⟨hBBr, hBBp, fun i j => ⟨hamc i j, by
          show dist (v i) (v j) ≤ s.am i j
          rw [hambm]
          exact hbmc i j⟩, hBBf⟩
      have hBBw : ∀ w, BBsV39 (restrictionTyp2V39 s) w → BBsV39 s w := by
        intro w hw
        refine ⟨hw.1, hw.2.1, ?_, hw.2.2.2⟩
        intro i j
        obtain ⟨hlo1, hhi1⟩ := hw.2.2.1 i j
        exact ⟨(h14 i j).1.trans hlo1,
          hhi1.trans ((h14 i j).2.1.trans (h14 i j).2.2)⟩
      have hvBT : v ∈ BBprimeV39 (restrictionTyp2V39 s) :=
        ⟨hBBsT, by
          intro w hw
          rw [htauT v, htauT w]
          exact hmin w (hBBw w hw),
          by rw [htauT v]; exact hneg⟩
      -- every BBs-realization of the restriction has full index s.k
      have hidxfull : ∀ w, BBsV39 (restrictionTyp2V39 s) w →
          BBindexV39 (restrictionTyp2V39 s) w = s.k := by
        intro w hw
        have seteq : {i : ℕ | i < (restrictionTyp2V39 s).k ∧
            (restrictionTyp2V39 s).a i (i + 1) = dist (w i) (w (i + 1))}
            = Set.Iio s.k := by
          ext i
          simp only [Set.mem_setOf_eq, Set.mem_Iio, restrictionTyp2V39]
          refine ⟨fun h => h.1, fun hlt => ⟨hlt, le_antisymm ?_ ?_⟩⟩
          · exact (hw.2.2.1 i (i + 1)).1
          · exact (hw.2.2.1 i (i + 1)).2
        rw [BBindexV39, seteq, Set.ncard_Iio_nat]
      obtain ⟨z, hzBB, hzval⟩ := la1bbindexMin_attained _ v hvBT
      have hidxT : BBindexV39 (restrictionTyp2V39 s) v = BBindexMinV39 (restrictionTyp2V39 s) := by
        rw [hidxfull v hBBsT, ← hzval, hidxfull z hzBB.1]
      have hvT : v ∈ MMsV39 (restrictionTyp2V39 s) := by
        have hvB2 : v ∈ BBprime2V39 (restrictionTyp2V39 s) := ⟨hvBT, hidxT⟩
        simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq]
        exact ⟨hvB2, hstrc, hloc, hhic, hamc,
          fun i j => by
            show dist (v i) (v j) ≤ s.am i j
            rw [hambm]
            exact hbmc i j⟩
      exact Or.inr ⟨restrictionTyp2V39 s, Set.mem_singleton _,
        Set.nonempty_iff_ne_empty.mp ⟨v, hvT⟩⟩

/-- HOL `UAGHHBM_concl` (appendix.hl:1122). Proof pending. -/
theorem UAGHHBM_concl : ∀ (s : ScsV39) (i j : ℕ) (c : ℝ),
    isScsV39 s → s.a i j ≤ c → c ≤ s.b i j → 3 < s.k →
    ¬(i % s.k = j % s.k) → ¬s.J i j →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k → ¬(c = s.am i j)) →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k →
      2 < s.a i j ∨ 2 * h0 < s.b i j) →
    scsArrowV39 {s} (setOfList (subdivV39 s i j c)) := by
  sorry

/-- HOL `YXIONXL1_concl` (appendix.hl:1134). Proof pending. -/
theorem YXIONXL1_concl : ∀ s t : ScsV39, isScsV39 s → transferV39 s t →
    scsArrowV39 {s} {t} := by
  sorry

/-- HOL `YXIONXL2_concl` (appendix.hl:1138). Proof pending. -/
theorem YXIONXL2_concl : ∀ s : ScsV39, isScsV39 s →
    scsArrowV39 {s} {scsOppV39 s} := by
  sorry

/-! ### Residue-shift toolkit for `YXIONXL3` (`scs_prop_equ_v39`)

The shift `j ↦ (i + j) % k` is a bijection of `{j | j < k}` with inverse
`m ↦ (m + k - i % k) % k`; every `scs` component of `scsPropEquV39 s i`
transports along it. -/

private theorem la1shift_inj {k i : ℕ} :
    Set.InjOn (fun j => (i + j) % k) {j | j < k} := by
  intro j₁ hj₁ j₂ hj₂ heq
  have hme : Nat.ModEq k (i + j₁) (i + j₂) := heq
  have hcan : j₁ % k = j₂ % k := Nat.ModEq.add_left_cancel' i hme
  rw [Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at hcan
  exact hcan

private theorem la1shift_rho {k i : ℕ} (hk : 0 < k) (m : ℕ) :
    (i + (m + k - i % k) % k) % k = m % k := by
  have hip : i % k < k := Nat.mod_lt i hk
  have h0 : Nat.ModEq k i (i % k) := (Nat.mod_mod i k).symm
  have h1 : Nat.ModEq k (i + (m + k - i % k) % k) (i % k + (m + k - i % k) % k) :=
    Nat.ModEq.add_right _ h0
  have h2 : Nat.ModEq k (i % k + (m + k - i % k) % k) (i % k + (m + k - i % k)) :=
    Nat.ModEq.add_left _ (Nat.mod_mod (m + k - i % k) k)
  have h3 : Nat.ModEq k (i % k + (m + k - i % k)) m := by
    have he : i % k + (m + k - i % k) = m + k := by omega
    show (i % k + (m + k - i % k)) % k = m % k
    rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact (h1.trans h2).trans h3

private theorem la1shift_surj {k i : ℕ} (hk : 0 < k) (m : ℕ) (hm : m < k) :
    ∃ j, j < k ∧ (i + j) % k = m := by
  refine ⟨(m + k - i % k) % k, Nat.mod_lt _ hk, ?_⟩
  rw [la1shift_rho hk, Nat.mod_eq_of_lt hm]

private theorem la1shift_back {k i : ℕ} (hk : 0 < k) (j : ℕ) :
    ((i + j) % k + (k - i % k)) % k = j % k := by
  have hip : i % k ≤ k := Nat.le_of_lt (Nat.mod_lt i hk)
  have h1 : Nat.ModEq k ((i + j) % k) (i + j) := Nat.mod_mod (i + j) k
  have h2 : Nat.ModEq k ((i + j) % k + (k - i % k)) (i + j + (k - i % k)) :=
    Nat.ModEq.add_right (k - i % k) h1
  have h0 : Nat.ModEq k i (i % k) := (Nat.mod_mod i k).symm
  have h3 : Nat.ModEq k (i + j + (k - i % k)) (i % k + j + (k - i % k)) :=
    Nat.ModEq.add_right _ (Nat.ModEq.add_right j h0)
  have h4 : Nat.ModEq k (i % k + j + (k - i % k)) (j + k) := by
    have he : i % k + j + (k - i % k) = j + k := by omega
    rw [he]
  have h5 : ((i + j) % k + (k - i % k)) % k = (j + k) % k := h2.trans (h3.trans h4)
  rw [h5, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

private theorem la1setSum_image {α : Type} {B : Set α} (hB : B.Finite)
    {f : α → α} (hinj : Set.InjOn f B) (g : α → ℝ) :
    setSum (f '' B) g = setSum B (fun x => g (f x)) := by
  have hfin : (f '' B).Finite := Set.Finite.image f hB
  haveI := Classical.decEq α
  unfold setSum
  rw [dif_pos hfin, dif_pos hB, Set.Finite.toFinset_image f hB hfin]
  exact Finset.sum_image fun a ha b hb hab =>
    hinj (Set.Finite.mem_toFinset hB |>.mp ha) (Set.Finite.mem_toFinset hB |>.mp hb) hab

private theorem la1setSum_congr {α : Type} {S : Set α} (hS : S.Finite) {f g : α → ℝ}
    (h : ∀ x ∈ S, f x = g x) : setSum S f = setSum S g := by
  unfold setSum
  rw [dif_pos hS, dif_pos hS]
  exact Finset.sum_congr rfl fun x hx => h x (Set.Finite.mem_toFinset hS |>.mp hx)

private theorem la1setSum_shift {Q P : ℕ → Prop} {k i : ℕ} (hk : 0 < k) (f g : ℕ → ℝ)
    (hiff : ∀ j, j < k → (Q j ↔ P ((i + j) % k)))
    (hfg : ∀ j, j < k → f j = g ((i + j) % k)) :
    setSum {j | j < k ∧ Q j} f = setSum {m | m < k ∧ P m} g := by
  have hB : {j | j < k ∧ Q j}.Finite :=
    Set.Finite.subset (Set.finite_Iio k) fun j hj => hj.1
  have himg : {m | m < k ∧ P m} = (fun j => (i + j) % k) '' {j | j < k ∧ Q j} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hm, hP⟩
      obtain ⟨j, hj, hjm⟩ := la1shift_surj hk m hm
      have hQj : Q j := (hiff j hj).mpr (by rw [hjm]; exact hP)
      exact ⟨j, ⟨hj, hQj⟩, hjm⟩
    · rintro ⟨j, ⟨hj, hQ⟩, hjm⟩
      have hm' : m < k := by rw [← hjm]; exact Nat.mod_lt _ hk
      have hPm : P m := by rw [← hjm]; exact (hiff j hj).mp hQ
      exact ⟨hm', hPm⟩
  rw [himg, la1setSum_image hB
    ((la1shift_inj (k := k) (i := i)).mono fun j hj => hj.1) g]
  exact la1setSum_congr hB fun x hx => hfg x hx.1

private theorem la1tau3_cyc (a b c : V3) : tau3 a b c = tau3 b c a := by
  unfold tau3
  ring

private theorem la1tau3_cyc2 (a b c : V3) : tau3 a b c = tau3 c a b := by
  unfold tau3
  ring

private theorem la1periodic2_mul {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (h : Periodic2 f k) :
    ∀ n x y, f (x + n * k) (y + n * k) = f x y := by
  intro n x y
  calc f (x + n * k) (y + n * k)
      = f (x + n * k) y :=
        la1periodic_mul (f := fun m => f (x + n * k) m) (k := k)
          (fun m => (h (x + n * k) m).2) n y
    _ = f x y :=
        la1periodic_mul (f := fun m => f m y) (k := k) (fun m => (h m y).1) n x

private theorem la1range_shift {x : ℕ → V3} {k i : ℕ} (hk : 0 < k)
    (hxper : Periodic x k) :
    Set.range (fun m => x (i + m)) = Set.range x := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨i + m, rfl⟩
  · rintro ⟨m, rfl⟩
    refine ⟨(m + k - i % k) % k, ?_⟩
    show x (i + ((m + k - i % k) % k)) = x m
    have hrho : (i + ((m + k - i % k) % k)) % k = m % k := la1shift_rho hk m
    have h1 : x (i + ((m + k - i % k) % k)) = x ((i + ((m + k - i % k) % k)) % k) :=
      la1periodic_mod hxper _
    rw [h1, hrho, la1periodic_mod hxper m]

private theorem la1shift_ncard {Q P : ℕ → Prop} {k i : ℕ} (hk : 0 < k)
    (hiff : ∀ j, j < k → (Q j ↔ P ((i + j) % k))) :
    {j | j < k ∧ Q j}.ncard = {m | m < k ∧ P m}.ncard := by
  have himg : {m | m < k ∧ P m} = (fun j => (i + j) % k) '' {j | j < k ∧ Q j} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hm, hP⟩
      obtain ⟨j, hj, hjm⟩ := la1shift_surj hk m hm
      have hQj : Q j := (hiff j hj).mpr (by rw [hjm]; exact hP)
      exact ⟨j, ⟨hj, hQj⟩, hjm⟩
    · rintro ⟨j, ⟨hj, hQ⟩, hjm⟩
      have hm' : m < k := by rw [← hjm]; exact Nat.mod_lt _ hk
      have hPm : P m := by rw [← hjm]; exact (hiff j hj).mp hQ
      exact ⟨hm', hPm⟩
  rw [himg, Set.InjOn.ncard_image ((la1shift_inj (k := k) (i := i)).mono fun j hj => hj.1)]

private theorem la1isScs_propEqu (s : ScsV39) (i : ℕ) (his : isScsV39 s) :
    isScsV39 (scsPropEquV39 s i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := his
  have hk : 0 < s.k := by omega
  refine ⟨h1, h2, h3,
    fun m => by
      show s.lo (i + (m + s.k)) = s.lo (i + m)
      rw [← Nat.add_assoc]
      exact h4 (i + m),
    fun m => by
      show s.hi (i + (m + s.k)) = s.hi (i + m)
      rw [← Nat.add_assoc]
      exact h5 (i + m),
    fun m => by
      show s.str (i + (m + s.k)) = s.str (i + m)
      rw [← Nat.add_assoc]
      exact h6 (i + m),
    fun m => by
      show s.str (i + (m + s.k)) = s.str (i + m)
      rw [← Nat.add_assoc]
      exact h7 (i + m),
    fun m m' => by
      show s.a (i + (m + s.k)) (i + m') = s.a (i + m) (i + m') ∧
        s.a (i + m) (i + (m' + s.k)) = s.a (i + m) (i + m')
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact h8 (i + m) (i + m'),
    fun m m' => by
      show s.am (i + (m + s.k)) (i + m') = s.am (i + m) (i + m') ∧
        s.am (i + m) (i + (m' + s.k)) = s.am (i + m) (i + m')
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact h9 (i + m) (i + m'),
    fun m m' => by
      show s.bm (i + (m + s.k)) (i + m') = s.bm (i + m) (i + m') ∧
        s.bm (i + m) (i + (m' + s.k)) = s.bm (i + m) (i + m')
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact h10 (i + m) (i + m'),
    fun m m' => by
      show s.b (i + (m + s.k)) (i + m') = s.b (i + m) (i + m') ∧
        s.b (i + m) (i + (m' + s.k)) = s.b (i + m) (i + m')
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact h11 (i + m) (i + m'),
    fun m m' => by
      show s.J (i + (m + s.k)) (i + m') = s.J (i + m) (i + m') ∧
        s.J (i + m) (i + (m' + s.k)) = s.J (i + m) (i + m')
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact h12 (i + m) (i + m'),
    fun j j' => ⟨(h13 (i + j) (i + j')).1, (h13 (i + j) (i + j')).2.1,
      (h13 (i + j) (i + j')).2.2.1, (h13 (i + j) (i + j')).2.2.2.1,
      (h13 (i + j) (i + j')).2.2.2.2⟩,
    fun j j' => ⟨(h14 (i + j) (i + j')).1, (h14 (i + j) (i + j')).2.1,
      (h14 (i + j) (i + j')).2.2⟩,
    fun j => h15 (i + j),
    ?_, fun j hj => h17 (i + j) hj, fun j hj => h18 (i + j) hj,
    fun j j' hj => by
      rcases h19 (i + j) (i + j') hj with h | h
      · refine Or.inl ?_
        have hme : Nat.ModEq s.k (i + j') (i + (j + 1)) := by
          rw [← Nat.add_assoc]
          exact h
        exact Nat.ModEq.add_left_cancel' i hme
      · refine Or.inr ?_
        have hme : Nat.ModEq s.k (i + j) (i + (j' + 1)) := by
          rw [← Nat.add_assoc]
          exact h
        exact Nat.ModEq.add_left_cancel' i hme,
    fun j j' hj => by
      rw [show (scsPropEquV39 s i).a j j' = s.a (i + j) (i + j') from rfl,
        show (scsPropEquV39 s i).b j j' = s.b (i + j) (i + j') from rfl]
      exact h20 (i + j) (i + j') hj,
    ?_⟩
  · -- 2 ≤ a for distinct slots
    intro j j' hj
    rw [show (scsPropEquV39 s i).a j j' = s.a (i + j) (i + j') from rfl,
      la1periodic2_mod h8 (i + j) (i + j')]
    exact h16 ((i + j) % s.k) ((i + j') % s.k)
      ⟨Nat.mod_lt _ hk, Nat.mod_lt _ hk, fun heq => hj.2.2 (by
        have hj1 : j < s.k := hj.1
        have hj2 : j' < s.k := hj.2.1
        have hme : j % s.k = j' % s.k := Nat.ModEq.add_left_cancel' i heq
        rw [Nat.mod_eq_of_lt hj1, Nat.mod_eq_of_lt hj2] at hme
        exact hme)⟩
  · -- card bound: the M-set transports along the shift bijection
    have hsplit : ∀ j : ℕ, i + j = (i + j) % s.k + (i + j) / s.k * s.k := by
      intro j
      rw [Nat.mul_comm ((i + j) / s.k) s.k,
        Nat.add_comm ((i + j) % s.k) (s.k * ((i + j) / s.k))]
      exact (Nat.div_add_mod (i + j) s.k).symm
    have hsplit2 : ∀ j : ℕ, i + j + 1 = ((i + j) % s.k + 1) + (i + j) / s.k * s.k := by
      intro j
      linarith [hsplit j]
    have hsb : ∀ j : ℕ, s.b (i + j) (i + j + 1) =
        s.b ((i + j) % s.k) (((i + j) % s.k) + 1) := by
      intro j
      have hA : s.b (i + j) (i + j + 1)
          = s.b ((i + j) % s.k + (i + j) / s.k * s.k) (i + j + 1) := by
        nth_rewrite 1 [hsplit j]
        rfl
      have hB : s.b ((i + j) % s.k + (i + j) / s.k * s.k) (i + j + 1)
          = s.b ((i + j) % s.k) (i + j + 1) :=
        la1periodic_mul (f := fun m => s.b m (i + j + 1)) (k := s.k)
          (fun m => (h11 m (i + j + 1)).1) ((i + j) / s.k) ((i + j) % s.k)
      have hC : s.b ((i + j) % s.k) (i + j + 1)
          = s.b ((i + j) % s.k) (((i + j) % s.k + 1) + (i + j) / s.k * s.k) := by
        nth_rewrite 1 [hsplit2 j]
        rfl
      have hD : s.b ((i + j) % s.k) (((i + j) % s.k + 1) + (i + j) / s.k * s.k)
          = s.b ((i + j) % s.k) (((i + j) % s.k) + 1) :=
        la1periodic_mul (f := fun m => s.b ((i + j) % s.k) m) (k := s.k)
          (fun m => (h11 ((i + j) % s.k) m).2) ((i + j) / s.k) (((i + j) % s.k) + 1)
      rw [hA, hB, hC, hD]
    have hsa : ∀ j : ℕ, s.a (i + j) (i + j + 1) =
        s.a ((i + j) % s.k) (((i + j) % s.k) + 1) := by
      intro j
      have hA : s.a (i + j) (i + j + 1)
          = s.a ((i + j) % s.k + (i + j) / s.k * s.k) (i + j + 1) := by
        nth_rewrite 1 [hsplit j]
        rfl
      have hB : s.a ((i + j) % s.k + (i + j) / s.k * s.k) (i + j + 1)
          = s.a ((i + j) % s.k) (i + j + 1) :=
        la1periodic_mul (f := fun m => s.a m (i + j + 1)) (k := s.k)
          (fun m => (h8 m (i + j + 1)).1) ((i + j) / s.k) ((i + j) % s.k)
      have hC : s.a ((i + j) % s.k) (i + j + 1)
          = s.a ((i + j) % s.k) (((i + j) % s.k + 1) + (i + j) / s.k * s.k) := by
        nth_rewrite 1 [hsplit2 j]
        rfl
      have hD : s.a ((i + j) % s.k) (((i + j) % s.k + 1) + (i + j) / s.k * s.k)
          = s.a ((i + j) % s.k) (((i + j) % s.k) + 1) :=
        la1periodic_mul (f := fun m => s.a ((i + j) % s.k) m) (k := s.k)
          (fun m => (h8 ((i + j) % s.k) m).2) ((i + j) / s.k) (((i + j) % s.k) + 1)
      rw [hA, hB, hC, hD]
    show {j : ℕ | j < (scsPropEquV39 s i).k ∧
        (2 * h0 < (scsPropEquV39 s i).b j (j + 1) ∨ 2 < (scsPropEquV39 s i).a j (j + 1))}.ncard
          + s.k ≤ 6
    have hset2 : {j : ℕ | j < (scsPropEquV39 s i).k ∧
        (2 * h0 < (scsPropEquV39 s i).b j (j + 1) ∨ 2 < (scsPropEquV39 s i).a j (j + 1))}
        = {j : ℕ | j < s.k ∧ (2 * h0 < s.b (i + j) (i + j + 1) ∨
          2 < s.a (i + j) (i + j + 1))} := by
      ext j
      have hbb : (scsPropEquV39 s i).b j (j + 1) = s.b (i + j) (i + j + 1) := by
        show s.b (i + j) (i + (j + 1)) = s.b (i + j) (i + j + 1)
        rw [Nat.add_assoc]
      have haa : (scsPropEquV39 s i).a j (j + 1) = s.a (i + j) (i + j + 1) := by
        show s.a (i + j) (i + (j + 1)) = s.a (i + j) (i + j + 1)
        rw [Nat.add_assoc]
      simp only [Set.mem_setOf_eq, hbb, haa,
        show (scsPropEquV39 s i).k = s.k from rfl]
    have hiff : ∀ j : ℕ, j < s.k →
        ((2 * h0 < s.b (i + j) (i + j + 1) ∨ 2 < s.a (i + j) (i + j + 1)) ↔
          (2 * h0 < s.b ((i + j) % s.k) (((i + j) % s.k) + 1) ∨
            2 < s.a ((i + j) % s.k) (((i + j) % s.k) + 1))) := by
      intro j _
      rw [hsb j, hsa j]
    rw [hset2, la1shift_ncard (k := s.k) (i := i)
      (P := fun m => 2 * h0 < s.b m (m + 1) ∨ 2 < s.a m (m + 1)) hk hiff]
    exact h21

/-- HOL `YXIONXL3_concl` (appendix.hl:1141). Proof pending. -/
theorem YXIONXL3_concl : ∀ (s : ScsV39) (i : ℕ), isScsV39 s →
    scsArrowV39 {s} {scsPropEquV39 s i} := by
  sorry

/-- HOL `LKGRQUI_concl` (appendix.hl:1144). Proof pending. -/
theorem LKGRQUI_concl : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
    isScsV39 s → (s', s'') = scsSliceV39 s p q d' d'' mkj →
    scsArrowV39 {s} {s', s''} := by
  sorry

/-- HOL `HXHYTIJ_concl` (appendix.hl:1147). Discharged 2026-09-30
(LocalAuto1 lane): pure bookkeeping — equal-taustar membership in `BBprime`
plus attainment of the `BBindex` minimum. -/
theorem HXHYTIJ_concl : ∀ (s : ScsV39) (vv ww : ℕ → V3), isScsV39 s →
    vv ∈ BBprime2V39 s → BBsV39 s ww →
    taustarV39 s vv < taustarV39 s ww ∨ BBindexV39 s vv ≤ BBindexV39 s ww := by
  intro s vv ww _ hv _
  simp only [BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
  obtain ⟨⟨hBBv, hminv, hnegv⟩, hidxv⟩ := hv
  by_cases hlt : taustarV39 s vv < taustarV39 s ww
  · exact Or.inl hlt
  · right
    have h1 : taustarV39 s vv ≤ taustarV39 s ww := hminv ww ‹BBsV39 s ww›
    have heq : taustarV39 s ww = taustarV39 s vv := by linarith
    have hwprime : ww ∈ BBprimeV39 s := by
      refine ⟨‹BBsV39 s ww›, ?_, ?_⟩
      · intro w hw
        rw [heq]
        exact hminv w hw
      · rw [heq]
        exact hnegv
    have himg : BBindexV39 s ww ∈ BBindexV39 s '' BBprimeV39 s :=
      ⟨ww, hwprime, rfl⟩
    have hspec := la1minNum_spec _ ⟨_, himg⟩
    rw [hidxv]
    exact hspec.2 _ himg

/-- HOL `ODXLSTCv2_concl` (appendix.hl:1154). Proof pending. -/
theorem ODXLSTCv2_concl : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    isScsV39 s → w ∈ MMsV39 s → k = s.k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → norm (w l) ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    False := by
  sorry

/-- HOL `IMJXPHRv2_concl` (appendix.hl:1168). Proof pending. -/
theorem IMJXPHRv2_concl : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    k = s.k → 3 < k →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → norm (w l) ≠ 2 →
    (∀ i, scsDiag k l i → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) := by
  sorry

/-- HOL `NUXCOEAv2_concl` (appendix.hl:1188). Proof pending. -/
theorem NUXCOEAv2_concl : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ),
    isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    k = s.k → 3 < k →
    (j % k = (l + 1) % k ∨ (j + 1) % k = l % k) →
    s.a j l = dist (w j) (w l) → s.a j l < s.b j l →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    (∀ i, scsDiag k l i → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) := by
  sorry

/-! ## Conclusions, part 3 (appendix.hl:1212-1319) -/

/-- HOL `DRNDRDV_concl` (appendix.hl:1212); header note updated: `f'` is the
slope value `8*y6/(y1*y2)` at `y6`. Discharged 2026-09-30 (LocalAuto1 lane):
direct differentiation of `xrr` in the third argument. -/
theorem DRNDRDV_concl : ∀ y1 y2 y6 : ℝ,
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      (Set.univ : Set ℝ) := by
  intro y1 y2 y6 hy
  have h1 : HasDerivAt (fun q : ℝ => q * q) (2 * y6) y6 := by
    have h := (hasDerivAt_id y6).mul (hasDerivAt_id y6)
    rwa [show (id y6 = y6) from rfl,
      show ((1 * y6 + y6 * 1 : ℝ) = 2 * y6) from by ring,
      show ((id * id : ℝ → ℝ) = fun q : ℝ => q * q) from rfl] at h
  have h2 : HasDerivAt (fun q : ℝ => (y1 * y1 + y2 * y2 - q * q) / (2 * y1 * y2))
      (-(2 * y6) / (2 * y1 * y2)) y6 := by
    simpa using (h1.const_sub (y1 * y1 + y2 * y2)).div_const (2 * y1 * y2)
  have h3 : HasDerivAt (fun q : ℝ => 1 - (y1 * y1 + y2 * y2 - q * q) / (2 * y1 * y2))
      (2 * y6 / (2 * y1 * y2)) y6 := by
    have h := h2.const_sub 1
    rwa [show ((-(-(2 * y6) / (2 * y1 * y2)) : ℝ) = 2 * y6 / (2 * y1 * y2)) from by ring] at h
  have h4 : HasDerivAt (fun q : ℝ => 8 * (1 - (y1 * y1 + y2 * y2 - q * q) / (2 * y1 * y2)))
      (8 * y6 / (y1 * y2)) y6 := by
    have h := h3.const_mul 8
    rwa [show ((8:ℝ) * (2 * y6 / (2 * y1 * y2)) = 8 * y6 / (y1 * y2)) from by ring] at h
  exact h4.hasDerivWithinAt

-- NEEDS (LocalAuto1 lane, 2026-09-30): TBRMXRZ1_concl is FALSE as stated
-- (statement frozen; left as `sorry` for the statement-fix lane).  Explicit
-- counterexample: f = id, f' = 1, g = fun z => -z, h' = -1, x = y = 0.  Both
-- derivedForm True hypotheses hold (HasDerivWithinAt id 1 univ 0 resp.
-- HasDerivWithinAt (fun z => -z) (-1) univ 0) and g x = y holds, but
-- reEqvl 1 (-1) = ∃ t > 0, 1 = t * (-1) is false (no positive t).  The HOL
-- source statement (appendix.hl:1216 over calc_derivative.hl:402,
-- `derived_form p f f' x s = (p ==> (f has_real_derivative f') atreal x
-- within s)`) admits the same counterexample, so the flyspeck item itself
-- needs an extra slope-proportionality hypothesis (e.g. 0 < g' x) before it
-- can be discharged.
/-- HOL `TBRMXRZ1_concl` (appendix.hl:1216); `re_eqvl` at the slope values
via `reEqvl` (PackingAuto18:79). Proof pending. -/
theorem TBRMXRZ1_concl : ∀ (f : ℝ → ℝ) (f' : ℝ) (g : ℝ → ℝ) (h' x y : ℝ),
    derivedForm True f f' y (Set.univ : Set ℝ) →
    derivedForm True (fun z => f (g z)) h' x (Set.univ : Set ℝ) →
    g x = y → reEqvl f' h' := by
  sorry

/-- HOL `PQCSXWG1_concl` (appendix.hl:1221). Proof pending. -/
theorem PQCSXWG1_concl : ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
      0 < ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ
        (crossProduct ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ)) := by
  sorry

/-- HOL `PQCSXWG2_concl` (appendix.hl:1234). Proof pending. -/
theorem PQCSXWG2_concl : ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    ContinuousAt (fun q => mkSimplex1 v0 v1 v2 x1 x2 x3 x4 q x6) x5 := by
  sorry

/-- HOL `EYYPQDW_concl` (appendix.hl:1244). Proof pending. -/
theorem EYYPQDW_concl : ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < upsX x1 x3 x5 → s = 1 ∨ s = -1 →
    v3 = mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 s →
    Coplanar ({v0, v1, v2, v3} : Set V3) ∧
    x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧
    ∃ t : ℝ, 0 < t ∧ t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0) := by
  sorry

/-- HOL `EYYPQDW2_concl` (appendix.hl:1259; `mk_planar` <-> `mkPlanar2`).
Proof pending. -/
theorem EYYPQDW2_concl : ∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < upsX x1 x3 x5 →
    ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3 := by
  sorry

/-- HOL `EYYPQDW3_concl` (appendix.hl:1268; `mk_planar` <-> `mkPlanar2`).
Proof pending. -/
theorem EYYPQDW3_concl : ∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < upsX x1 x3 x5 →
    ContinuousAt (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) v2 := by
  sorry

/-- HOL `FEKTYIY_concl` (appendix.hl:1277). Proof pending. -/
theorem FEKTYIY_concl : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → 3 < s.k →
    ¬Coplanar (({0} ∪ Set.range v : Set V3)) := by
  sorry

/-- HOL `AURSIPD_concl` (appendix.hl:1281; the free `vv` of the source is
bound as `v`). Proof pending. -/
theorem AURSIPD_concl : ∀ (s : ScsV39) (v : ℕ → V3), 3 < s.k → isScsV39 s →
    scsGeneric v → v ∈ MMsV39 s →
    3 + {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ s.k := by
  sorry

/-- HOL `PPBTYDQ_concl` (appendix.hl:1285). Proof pending. -/
theorem PPBTYDQ_concl : ∀ (u v p : V3), ¬Collinear ℝ ({0, v, p} : Set V3) →
    ¬Collinear ℝ ({0, u, p} : Set V3) →
    arcV 0 u p + arcV 0 p v < Real.pi →
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3)) := by
  sorry

/-- HOL `MXQTIED_concl` (appendix.hl:1288). Proof pending. -/
theorem MXQTIED_concl : ∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s → isScsV39 s' →
    scsBasicV39 s → scsBasicV39 s' → scsM s = scsM s' → s.k = s'.k →
    v ∈ MMsV39 s → BBsV39 s' v → s.d = s'.d →
    (∀ i, s'.a i (i + 1) = s.a i (i + 1)) →
    (∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) → v ∈ MMsV39 s' := by
  intro s s' v _ _ hb hb' _ hkk hv hvs' hdd hnb hmono
  obtain hu' := hb'.1
  rw [unadorned_MMs_concl s' hu']
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
  obtain ⟨⟨⟨hBBs, hmin, hneg⟩, hidx⟩, -, -, -, -, -⟩ := hv
  -- dsv and taustar agree pointwise on s vs s' (J-side sums are empty)
  have hJs : ∀ i j, s.J i j = False := hb.2
  have hJs' : ∀ i j, s'.J i j = False := hb'.2
  have hsetS : {i : ℕ | i < s.k ∧ s.J i (i + 1)} = ∅ := by
    ext i; simp [hJs]
  have hsetS' : {i : ℕ | i < s'.k ∧ s'.J i (i + 1)} = ∅ := by
    ext i; simp [hJs']
  have hdsv : ∀ x, dsvV39 s x = dsvV39 s' x := by
    intro x
    simp only [dsvV39, hsetS, hsetS']
    simp [hdd, setSum]
  have htau : ∀ x, taustarV39 s x = taustarV39 s' x := by
    intro x
    simp only [taustarV39]
    rw [hkk, hdsv x]
  -- BBs s' ⊆ BBs s (monotone bounds)
  have hBBsub : ∀ x, BBsV39 s' x → BBsV39 s x := by
    intro x hx
    refine ⟨hx.1, ?_, ?_, ?_⟩
    · rw [hkk]
      exact hx.2.1
    · intro i j
      exact ⟨(hmono i j).1.trans (hx.2.2.1 i j).1, (hx.2.2.1 i j).2.trans (hmono i j).2⟩
    · rw [hkk]
      exact hx.2.2.2
  -- v is taustar-minimal for s' as well
  have hv' : v ∈ BBprimeV39 s' := by
    refine ⟨hvs', ?_, ?_⟩
    · intro y hy
      rw [← htau v, ← htau y]
      exact hmin y (hBBsub y hy)
    · rw [← htau]
      exact hneg
  -- BBindex transport (neighbour values agree)
  have hBI : ∀ x, BBindexV39 s' x = BBindexV39 s x := by
    intro x
    have seteq : {i : ℕ | i < s'.k ∧ s'.a i (i + 1) = dist (x i) (x (i + 1))} =
        {i : ℕ | i < s.k ∧ s.a i (i + 1) = dist (x i) (x (i + 1))} := by
      ext i
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hlt, hval⟩
        exact ⟨by rw [hkk]; exact hlt, by rw [← hnb i]; exact hval⟩
      · rintro ⟨hlt, hval⟩
        exact ⟨by rw [← hkk]; exact hlt, by rw [hnb i]; exact hval⟩
    simp only [BBindexV39]
    rw [seteq]
  refine And.intro hv' ?_
  -- index bookkeeping: the min of s' is attained at some w, which is then
  -- taustar-equal to v, hence also index-minimal for s
  have himg : (BBindexV39 s' '' BBprimeV39 s').Nonempty := ⟨BBindexV39 s' v, v, hv', rfl⟩
  obtain ⟨hmin0, hminle⟩ := la1minNum_spec _ himg
  obtain ⟨w, ⟨hw, hwval⟩⟩ := hmin0
  obtain ⟨hBBw, hminw, hnegw⟩ := hw
  have htw : taustarV39 s w = taustarV39 s v := by
    have h1 : taustarV39 s' w ≤ taustarV39 s' v := hminw v hvs'
    have h2 : taustarV39 s v ≤ taustarV39 s w := hmin w (hBBsub w hBBw)
    rw [← htau w, ← htau v] at h1
    linarith [h1, h2]
  have hw'S : v ∈ BBprimeV39 s := ⟨hBBs, hmin, hneg⟩
  have hwS : w ∈ BBprimeV39 s := by
    refine ⟨hBBsub w hBBw, ?_, ?_⟩
    · intro y hy
      rw [htw]
      exact hmin y hy
    · rw [htw]
      exact hneg
  have himgS : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨BBindexV39 s v, v, hw'S, rfl⟩
  have hspecS := la1minNum_spec _ himgS
  rw [hBI]
  have hle : BBindexMinV39 s' ≤ BBindexV39 s v := by
    rw [← hBI]
    exact hminle _ ⟨v, hv', rfl⟩
  have h3 : BBindexV39 s v ≤ BBindexMinV39 s' := by
    rw [hidx]
    have h5 : BBindexMinV39 s ≤ BBindexV39 s w := hspecS.2 _ ⟨w, hwS, rfl⟩
    unfold BBindexMinV39
    rw [← hwval, hBI]
    exact h5
  exact Nat.le_antisymm h3 hle

/-- HOL `SYNQIWN_concl` (appendix.hl:1296). Proof pending. -/
theorem SYNQIWN_concl : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    BBsV39 s v →
    (norm (v i) = 2 ∨ dist (v i) (v (i + 1)) = 2) →
    (norm (v (i + 2)) = 2 ∨ dist (v (i + 1)) (v (i + 2)) = 2) →
    cstab ≤ dist (v i) (v (i + 2)) →
    Real.pi / 2 < azim 0 (v (i + 1)) (v (i + 2)) (v i) := by
  sorry

/-- HOL `XWNHLMD_concl` (appendix.hl:1303). Proof pending. -/
theorem XWNHLMD_concl : ∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s → isScsV39 s' →
    scsBasicV39 s → scsBasicV39 s' → s.k = s'.k → v ∈ MMsV39 s → BBsV39 s' v →
    scsArrowV39 {s} {s'} := by
  sorry

/-- HOL `OIQKKEP_concl` (appendix.hl:1309). Proof pending. -/
theorem OIQKKEP_concl : ∀ (u v : V3) (c : ℝ), u ∈ ballAnnulus → v ∈ ballAnnulus →
    c < 4 → 2 ≤ dist u v → dist u v ≤ c → arcV 0 u v ≤ arcLength 2 2 c := by
  sorry

/-- HOL `AXJRPNC_concl` (appendix.hl:1313). Proof pending. -/
theorem AXJRPNC_concl : ∀ (s : ScsV39) (v : ℕ → V3) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → v ∈ MMsV39 s → (∀ i, s.b i (i + 1) ≤ cstab) →
    Lunar (v i) (v j) (Set.range v) (Set.range fun i => {v i, v (i + 1)}) →
    s.k = 6 ∧ v j = v (i + 3) := by
  sorry

/-! ## Concrete systems: I / T rows (appendix.hl:878-938) -/

/-- HOL `scs_6I1` (appendix.hl:878). -/
noncomputable def scs6I1 : ScsV39 :=
  mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6)

/-- HOL `scs_5I1` (appendix.hl:881). -/
noncomputable def scs5I1 : ScsV39 :=
  mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6)

/-- HOL `scs_4I1` (appendix.hl:884). -/
noncomputable def scs4I1 : ScsV39 :=
  mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6)

/-- HOL `scs_3I1` (appendix.hl:888). -/
noncomputable def scs3I1 : ScsV39 :=
  mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6)

/-- HOL `scs_5I2` (appendix.hl:892). -/
noncomputable def scs5I2 : ScsV39 :=
  mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6)

/-- HOL `scs_4I2` (appendix.hl:896). -/
noncomputable def scs4I2 : ScsV39 :=
  mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)

/-- HOL `scs_5I3` (appendix.hl:900). -/
noncomputable def scs5I3 : ScsV39 :=
  mkUnadornedV39 5 0.616
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5)
    (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)

/-- HOL `scs_4I3` (appendix.hl:905). -/
noncomputable def scs4I3 : ScsV39 :=
  mkUnadornedV39 4 0.477
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)] 2 4)
    (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_6T1` (appendix.hl:912). -/
noncomputable def scs6T1 : ScsV39 :=
  mkUnadornedV39 6 (dTame 6) (csAdj 6 2 cstab) (csAdj 6 2 6)

/-- HOL `scs_5T1` (appendix.hl:915). -/
noncomputable def scs5T1 : ScsV39 :=
  mkUnadornedV39 5 0.616 (csAdj 5 2 cstab) (csAdj 5 2 6)

/-- HOL `scs_4T1` (appendix.hl:918). -/
noncomputable def scs4T1 : ScsV39 :=
  mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 2 6)

/-- HOL `scs_4T2` (appendix.hl:922). -/
noncomputable def scs4T2 : ScsV39 :=
  mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 3)

/-- HOL `scs_4T3` (appendix.hl:925). -/
noncomputable def scs4T3 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] 2 4)

/-- HOL `scs_4T4` (appendix.hl:930). -/
noncomputable def scs4T4 : ScsV39 :=
  mkUnadornedV39 4 0.477
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)] 2 4)
    (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), cstab)] (2 * h0) 4)

/-- HOL `scs_4T5` (appendix.hl:935). -/
noncomputable def scs4T5 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), cstab)] (2 * h0) 4)

/-! ## Concrete systems: 3T row and M rows (appendix.hl:940-1050) -/

/-- HOL `scs_3T1` (appendix.hl:940, `scs_3T1_PRELIM`). -/
noncomputable def scs3T1 : ScsV39 :=
  ScsV39.mk 3 0.11 (funlistV39 [((0, 1), Real.sqrt 8)] 2 3)
    (funlistV39 [((0, 1), Real.sqrt 8)] 2 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
    (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => False)

/-- HOL `scs_3T1` equation (appendix.hl:948). -/
theorem scs_3T1 : scs3T1 = mkUnadornedV39 3 0.11
    (funlistV39 [((0, 1), Real.sqrt 8)] 2 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3) := rfl

/-- HOL `scs_3T2` (appendix.hl:958). -/
noncomputable def scs3T2 : ScsV39 :=
  mkUnadornedV39 3 0 (funlistV39 [] 2 3) (funlistV39 [] 2 3)

/-- HOL `scs_3T3` (appendix.hl:965). -/
noncomputable def scs3T3 : ScsV39 :=
  mkUnadornedV39 3 0.476 (funlistV39 [] (2 * h0) 3) (funlistV39 [] cstab 3)

/-- HOL `scs_3T4` (appendix.hl:971). -/
noncomputable def scs3T4 : ScsV39 :=
  mkUnadornedV39 3 0.2759 (funlistV39 [((0, 1), 2)] (2 * h0) 3)
    (funlistV39 [((0, 1), 2 * h0)] cstab 3)

/-- HOL `scs_3T5` (appendix.hl:977). -/
noncomputable def scs3T5 : ScsV39 :=
  mkUnadornedV39 3 0.103 (funlistV39 [((0, 1), 2 * h0)] 2 3)
    (funlistV39 [((0, 1), Real.sqrt 8)] (2 * h0) 3)

/-- HOL `scs_3T6'` (appendix.hl:983). -/
noncomputable def scs3T6' : ScsV39 :=
  mkUnadornedV39 3 0.4348
    (funlistV39 [((0, 1), Real.sqrt 8), ((1, 2), Real.sqrt 8)] 2 3)
    (funlistV39 [((0, 1), cstab), ((1, 2), cstab)] (2 * h0) 3)

/-- HOL `scs_3T7` (appendix.hl:989). -/
noncomputable def scs3T7 : ScsV39 :=
  mkUnadornedV39 3 0.2565
    (funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 2), 2)] 2 3)
    (funlistV39 [((0, 1), 3.62), ((0, 2), cstab), ((1, 2), 2)] 2 3)

/-- HOL `scs_6M1` (appendix.hl:994). -/
noncomputable def scs6M1 : ScsV39 :=
  mkUnadornedV39 6 (dTame 6) (csAdj 6 2 cstab) (csAdj 6 (2 * h0) 6)

/-- HOL `scs_5M1` (appendix.hl:997). -/
noncomputable def scs5M1 : ScsV39 :=
  mkUnadornedV39 5 0.616
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)

/-- HOL `scs_5M2` (appendix.hl:1002). -/
noncomputable def scs5M2 : ScsV39 :=
  mkUnadornedV39 5 0.616
    (funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
      ((1, 4), cstab), ((2, 4), cstab)] 2 5)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)

/-- HOL `scs_4M1` (appendix.hl:1007). -/
noncomputable def scs4M1 : ScsV39 :=
  mkUnadornedV39 4 0.3401
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M2` (appendix.hl:1012). -/
noncomputable def scs4M2 : ScsV39 :=
  mkUnadornedV39 4 0.3789
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M3'` (appendix.hl:1017). -/
noncomputable def scs4M3' : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), Real.sqrt 8),
      ((1, 3), Real.sqrt 8)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M4'` (appendix.hl:1022). -/
noncomputable def scs4M4' : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), 2 * h0),
      ((1, 3), 2 * h0)] 2 4)
    (funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M5'` (appendix.hl:1027). -/
noncomputable def scs4M5' : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), 2 * h0),
      ((1, 3), 2 * h0)] 2 4)
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M6'` (appendix.hl:1032). -/
noncomputable def scs4M6' : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M7` (appendix.hl:1037). -/
noncomputable def scs4M7 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6),
      ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M8` (appendix.hl:1042). -/
noncomputable def scs4M8 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6),
      ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_3M1` (appendix.hl:1047). -/
noncomputable def scs3M1 : ScsV39 :=
  mkUnadornedV39 3 0.103 (funlistV39 [((0, 1), 2 * h0)] 2 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)

/-! ## Conclusions, part 4 (appendix.hl:1321-1408) -/

/-- HOL `RRCWNSJ_concl` (appendix.hl:1321). Proof pending. -/
theorem RRCWNSJ_concl : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → scsBasicV39 s →
    3 < s.k → v ∈ MMsV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v := by
  sorry

/-- HOL `JCYFMRP_concl` (appendix.hl:1329). Proof pending. -/
theorem JCYFMRP_concl : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → v ∈ MMsV39 s →
    scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 → 3 < s.k →
    (∀ i, s.a i (i + 1) = 2) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    ∃ i, dist (v i) (v (i + 1)) = 2 := by
  sorry

/-- HOL `TFITSKC_concl` (appendix.hl:1337). Proof pending. -/
theorem TFITSKC_concl : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    3 < s.k → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → (s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    dist (v (i + 1)) (v (i + 2)) = 2 := by
  sorry

/-- HOL `CQAOQLR_concl` (appendix.hl:1349). Proof pending. -/
theorem CQAOQLR_concl : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    s.a i (i + 1) = 2 → s.b i (i + 1) = 2 * h0 →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    (dist (v i) (v (i + 1)) = 2 ↔ dist (v (i + 1)) (v (i + 2)) = 2) := by
  sorry

/-- HOL `JLXFDMJ_concl` (appendix.hl:1357). Proof pending. -/
theorem JLXFDMJ_concl : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s → dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
    s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
    ∀ j, j ∉ scsM s → dist (v j) (v (j + 1)) = 2 := by
  sorry

/-- HOL `WKEIDFT_concl` (appendix.hl:1368). Proof pending. -/
theorem WKEIDFT_concl : ∀ (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ),
    isScsV39 s → scsBasicV39 s →
    (∀ i, s.a i (i + 1) = a) → (∀ i, s.b i (i + 1) = b) → p' + q = p + q' →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab) →
    (∀ i j, scsDiag s.k i j → s.a i j = a') →
    (∀ i j, scsDiag s.k i j → s.b i j = b') →
    scsArrowV39 {scsStabDiagV39 s p q} {scsStabDiagV39 s p' q'} := by
  sorry

/-- HOL `PEDSLGV1_concl` (appendix.hl:1379). Discharged 2026-10-08
(LocalAuto1 lane): the `cstab` diagonal override only shrinks the `b`-bound
on the class of `(i, j)` (far constant `6` there), so every `BBs`-realization
of the stab is one of `scs_6I1`, the `J`-empty `dsv`s agree (`taustar`
pointwise equal), and the diagonal class transports the required
`dist (v i) (v j) ≤ cstab`. -/
theorem PEDSLGV1_concl : ∀ (v : ℕ → V3) (i j : ℕ), v ∈ MMsV39 scs6I1 →
    scsDiag 6 i j → dist (v i) (v j) ≤ cstab →
    v ∈ MMsV39 (scsStabDiagV39 scs6I1 i j) := by
  intro v i j hv hdg hcl
  have hunad : unadornedV39 scs6I1 := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [unadorned_MMs_concl scs6I1 hunad] at hv
  simp only [BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
  obtain ⟨⟨hBBs, hmin, hneg⟩, hidx⟩ := hv
  obtain ⟨hBBr, hBBp, hBBb, hBBf⟩ := hBBs
  have hper : Periodic v 6 := hBBp
  set b' : ℕ → ℕ → ℝ := fun x y =>
    if psort 6 (i, j) = psort 6 (x, y) then cstab else csAdj 6 (2 * h0) 6 x y with hb'def
  have hS : scsStabDiagV39 scs6I1 i j =
      mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b' := by
    simp only [scsStabDiagV39, scs6I1, mkUnadornedV39, hb'def]
  have hunadS : unadornedV39 (scsStabDiagV39 scs6I1 i j) := by rw [hS]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [unadorned_MMs_concl _ hunadS, hS]
  -- class transport of the required diagonal bound
  have hclsdist : ∀ x y, psort 6 (i, j) = psort 6 (x, y) →
      dist (v x) (v y) ≤ cstab := by
    intro x y hcls
    obtain hc | hc := la1psort_cases hcls
    · rw [la1periodic_mod hper x, la1periodic_mod hper y, ← hc.1, ← hc.2,
        ← la1periodic_mod hper i, ← la1periodic_mod hper j]
      exact hcl
    · rw [la1periodic_mod hper x, la1periodic_mod hper y, ← hc.2, ← hc.1,
        ← la1periodic_mod hper j, ← la1periodic_mod hper i, dist_comm]
      exact hcl
  have hdistle : ∀ x y, dist (v x) (v y) ≤ b' x y := by
    intro x y
    by_cases hcls : psort 6 (i, j) = psort 6 (x, y)
    · simp only [hb'def, if_pos hcls]
      exact hclsdist x y hcls
    · simp only [hb'def, if_neg hcls]
      exact (hBBb x y).2
  have hup : ∀ x y, b' x y ≤ csAdj 6 (2 * h0) 6 x y := by
    intro x y
    by_cases hcls : psort 6 (i, j) = psort 6 (x, y)
    · simp only [hb'def, if_pos hcls]
      obtain hc | hc := la1psort_cases hcls
      · rw [la1csAdj_diag6 (Or.inl ⟨hc.1.symm, hc.2.symm⟩) hdg]
        norm_num [cstab]
      · rw [la1csAdj_diag6 (Or.inr ⟨hc.2.symm, hc.1.symm⟩) hdg]
        norm_num [cstab]
    · simp only [hb'def, if_neg hcls]
      exact le_refl _
  -- taustar pointwise equality (J-free dsv on both sides)
  have htau : ∀ w : ℕ → V3,
      taustarV39 (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b') w
        = taustarV39 scs6I1 w := by
    intro w
    simp only [taustarV39]
    rw [dsv_J_empty _ _ rfl, dsv_J_empty _ _ rfl]
    rfl
  have hBBsS : BBsV39 (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b') v :=
    ⟨hBBr, hper, fun x y => ⟨(hBBb x y).1, hdistle x y⟩, hBBf⟩
  have hBBw : ∀ w, BBsV39 (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b') w →
      BBsV39 scs6I1 w := by
    intro w hw
    refine ⟨hw.1, hw.2.1, fun x y => ⟨(hw.2.2.1 x y).1, le_trans (hw.2.2.1 x y).2 (hup x y)⟩,
      hw.2.2.2⟩
  have hvBS : v ∈ BBprimeV39 (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b') :=
    ⟨hBBsS, by
      intro w hw
      rw [htau v, htau w]
      exact hmin w (hBBw w hw),
      by rw [htau v]; exact hneg⟩
  have hle1 := la1bbindexMin_le _ hvBS
  obtain ⟨z, hz, hzval⟩ := la1bbindexMin_attained _ v hvBS
  have hzS : BBsV39 scs6I1 z := hBBw z hz.1
  have htaueq : taustarV39 scs6I1 z = taustarV39 scs6I1 v := by
    have h1 : taustarV39 scs6I1 v ≤ taustarV39 scs6I1 z := hmin z hzS
    have h2 : taustarV39 scs6I1 z ≤ taustarV39 scs6I1 v := by
      rw [← htau z, ← htau v]
      exact hz.2.1 v hBBsS
    exact le_antisymm h2 h1
  have hzprime : z ∈ BBprimeV39 scs6I1 := by
    refine ⟨hzS, ?_, ?_⟩
    · intro w hw
      rw [htaueq]
      exact hmin w hw
    · rw [htaueq]
      exact hneg
  have hidxT : BBindexV39 (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b') v
      = BBindexMinV39 (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) b') := by
    refine le_antisymm ?_ hle1
    have h1 : BBindexMinV39 scs6I1 ≤ BBindexV39 scs6I1 z :=
      la1bbindexMin_le scs6I1 hzprime
    rw [← hzval]
    show BBindexV39 scs6I1 v ≤ BBindexV39 scs6I1 z
    rw [hidx]
    exact h1
  exact ⟨hvBS, hidxT⟩

/-- HOL `PEDSLGV2_concl` (appendix.hl:1385). Discharged 2026-10-08
(LocalAuto1 lane): `scs_6M1` differs from `scs_6I1` only by raising the
non-adjacent lower bounds `2*h0` to `cstab` — exactly the `scsDiag` slots of
the hypothesis — while `d`, `b` and the adjacent slots are unchanged; `dsv` is
`J`-free on both sides, so `taustar` agrees pointwise and the whole `MMs`
membership transports. -/
theorem PEDSLGV2_concl : ∀ v : ℕ → V3, v ∈ MMsV39 scs6I1 →
    (∀ i j, scsDiag 6 i j → cstab ≤ dist (v i) (v j)) → v ∈ MMsV39 scs6M1 := by
  intro v hv hd
  have hunad : unadornedV39 scs6I1 := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [unadorned_MMs_concl scs6I1 hunad] at hv
  simp only [BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at hv
  obtain ⟨⟨hBBs, hmin, hneg⟩, hidx⟩ := hv
  obtain ⟨hBBr, hBBp, hBBb, hBBf⟩ := hBBs
  have hlowerM : ∀ x y, csAdj 6 2 cstab x y ≤ dist (v x) (v y) := by
    intro x y
    by_cases hd0 : x % 6 = y % 6
    · have hb := (hBBb x y).1
      simp only [scs6I1, mkUnadornedV39, csAdj, if_pos hd0] at hb ⊢
      exact hb
    · by_cases ha : y % 6 = (x + 1) % 6 ∨ (y + 1) % 6 = x % 6
      · have hb := (hBBb x y).1
        simp only [scs6I1, mkUnadornedV39, csAdj, if_neg hd0, if_pos ha] at hb ⊢
        exact hb
      · have hdiag : scsDiag 6 x y :=
          ⟨hd0, fun hc => ha (Or.inl hc.symm), fun hc => ha (Or.inr hc.symm)⟩
        simp only [csAdj, if_neg hd0, if_neg ha]
        exact hd x y hdiag
  have htau : ∀ w : ℕ → V3, taustarV39 scs6M1 w = taustarV39 scs6I1 w := by
    intro w
    simp only [taustarV39]
    rw [dsv_J_empty _ _ rfl, dsv_J_empty _ _ rfl]
    rfl
  have hBBw : ∀ w, BBsV39 scs6M1 w → BBsV39 scs6I1 w := by
    intro w hw
    refine ⟨hw.1, hw.2.1, ?_, hw.2.2.2⟩
    intro x y
    have h1 := (hw.2.2.1 x y).1
    have h2 := (hw.2.2.1 x y).2
    simp only [scs6M1, scs6I1, mkUnadornedV39, csAdj] at h1 h2 ⊢
    by_cases hd0 : x % 6 = y % 6
    · simp only [if_pos hd0] at h1 h2 ⊢
      exact ⟨h1, h2⟩
    · by_cases ha : y % 6 = (x + 1) % 6 ∨ (y + 1) % 6 = x % 6
      · simp only [if_neg hd0, if_pos ha] at h1 h2 ⊢
        exact ⟨h1, h2⟩
      · simp only [if_neg hd0, if_neg ha] at h1 h2 ⊢
        exact ⟨le_trans (by norm_num [h0, cstab]) h1, h2⟩
  have hBIeq : ∀ w : ℕ → V3, BBindexV39 scs6M1 w = BBindexV39 scs6I1 w := by
    intro w
    have hval : ∀ i : ℕ, csAdj 6 2 cstab i (i + 1) = csAdj 6 2 (2 * h0) i (i + 1) := by
      intro i
      have hnd : ¬ (i % 6 = (i + 1) % 6) := by omega
      show (if i % 6 = (i + 1) % 6 then (0:ℝ)
            else if (i + 1) % 6 = (i + 1) % 6 ∨ (i + 2) % 6 = i % 6 then 2 else cstab) =
          (if i % 6 = (i + 1) % 6 then (0:ℝ)
            else if (i + 1) % 6 = (i + 1) % 6 ∨ (i + 2) % 6 = i % 6 then 2 else 2 * h0)
      rw [if_neg hnd, if_neg hnd]
      simp
    have seteq : {i : ℕ | i < scs6M1.k ∧ scs6M1.a i (i + 1) = dist (w i) (w (i + 1))} =
        {i : ℕ | i < scs6I1.k ∧ scs6I1.a i (i + 1) = dist (w i) (w (i + 1))} := by
      ext i
      show (i < scs6M1.k ∧ csAdj 6 2 cstab i (i + 1) = dist (w i) (w (i + 1))) ↔
          (i < scs6I1.k ∧ csAdj 6 2 (2 * h0) i (i + 1) = dist (w i) (w (i + 1)))
      rw [hval i]
      exact Iff.rfl
    simp only [BBindexV39]
    rw [seteq]
  have hBBsM : BBsV39 scs6M1 v :=
    ⟨hBBr, hBBp, fun x y => ⟨hlowerM x y, (hBBb x y).2⟩, hBBf⟩
  have hvBM : v ∈ BBprimeV39 scs6M1 :=
    ⟨hBBsM, by
      intro w hw
      rw [htau v, htau w]
      exact hmin w (hBBw w hw),
      by rw [htau v]; exact hneg⟩
  have hle1 := la1bbindexMin_le scs6M1 hvBM
  obtain ⟨z, hz, hzval⟩ := la1bbindexMin_attained scs6M1 v hvBM
  have hzI : BBsV39 scs6I1 z := hBBw z hz.1
  have htaueq : taustarV39 scs6I1 z = taustarV39 scs6I1 v := by
    have h2 : taustarV39 scs6M1 z ≤ taustarV39 scs6M1 v := hz.2.1 v hBBsM
    have h1 : taustarV39 scs6M1 v ≤ taustarV39 scs6M1 z := by
      rw [htau v, htau z]
      exact hmin z (hBBw z hz.1)
    rw [← htau z, ← htau v]
    exact le_antisymm h2 h1
  have hzprime : z ∈ BBprimeV39 scs6I1 := by
    refine ⟨hzI, ?_, ?_⟩
    · intro w hw
      rw [htaueq]
      exact hmin w hw
    · rw [htaueq]
      exact hneg
  have hidxT : BBindexV39 scs6M1 v = BBindexMinV39 scs6M1 := by
    refine le_antisymm ?_ hle1
    have h1 : BBindexMinV39 scs6I1 ≤ BBindexV39 scs6I1 z :=
      la1bbindexMin_le scs6I1 hzprime
    rw [← hzval, hBIeq v, hBIeq z, hidx]
    exact h1
  have hunadM : unadornedV39 scs6M1 := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [unadorned_MMs_concl scs6M1 hunadM]
  exact ⟨hvBM, hidxT⟩

/-- HOL `AQICLXA_concl` (appendix.hl:1390). Proof pending. -/
theorem AQICLXA_concl :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs5M1, scs3M1} := by
  sorry

/-- HOL `FUNOUYH_concl` (appendix.hl:1392). Proof pending. -/
theorem FUNOUYH_concl :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2} := by
  sorry

/-- HOL `OEHDBEN_concl` (appendix.hl:1394). Proof pending. -/
theorem OEHDBEN_concl :
    scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3T1} := by
  sorry

/-- HOL `OTMTOTJ1_concl` (appendix.hl:1396). Proof pending. -/
theorem OTMTOTJ1_concl :
    scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2} := by
  sorry

/-- HOL `OTMTOTJ2_concl` (appendix.hl:1398). Proof pending. -/
theorem OTMTOTJ2_concl :
    scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2} := by
  sorry

/-- HOL `OTMTOTJ3_concl` (appendix.hl:1400). Proof pending. -/
theorem OTMTOTJ3_concl :
    scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  sorry

/-- HOL `OTMTOTJ4_concl` (appendix.hl:1403). Proof pending. -/
theorem OTMTOTJ4_concl :
    scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  sorry

/-- HOL `HIJQAHA_concl` (appendix.hl:1406). Proof pending. -/
theorem HIJQAHA_concl :
    scsArrowV39 {scs5M2} {scs3T1, scs3T4, scs4M6', scs4M7, scs4M8, scs5T1,
      scsStabDiagV39 scs5I2 0 2, scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4} := by
  sorry

/-- HOL `CNICGSF1_concl` (appendix.hl:1410). Proof pending. -/
theorem CNICGSF1_concl :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs4M2, scs3M1} := by
  sorry

/-- HOL `CNICGSF2_concl` (appendix.hl:1413). Proof pending. -/
theorem CNICGSF2_concl :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs4M3', scs3T1} := by
  sorry

/-- HOL `CNICGSF3_concl` (appendix.hl:1416). Proof pending. -/
theorem CNICGSF3_concl :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs4M2, scs3T4} := by
  sorry

/-- HOL `CNICGSF4_concl` (appendix.hl:1419). Proof pending. -/
theorem CNICGSF4_concl :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1} := by
  sorry

/-- HOL `CNICGSF5_concl` (appendix.hl:1422). Proof pending. -/
theorem CNICGSF5_concl :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs4M5', scs3M1} := by
  sorry

/-- HOL `ARDBZYE_concl` (appendix.hl:1425). Proof pending. -/
theorem ARDBZYE_concl : scsArrowV39 {scs4I2} {scs4T1, scs4T2} := by
  sorry

/-- HOL `FYSSVEV_concl` (appendix.hl:1427). Proof pending. -/
theorem FYSSVEV_concl :
    scsArrowV39 {scs4I1} {scs4I2, scsStabDiagV39 scs4I1 0 2} := by
  sorry

/-- HOL `AUEAHEH_concl` (appendix.hl:1429). Proof pending. -/
theorem AUEAHEH_concl :
    scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1} := by
  sorry

/-- HOL `ZNLLLDL_concl` (appendix.hl:1431). Proof pending. -/
theorem ZNLLLDL_concl :
    scsArrowV39 {scsStabDiagV39 scs4I3 0 2} {scs4T4} := by
  sorry

/-- HOL `VQFYMZY_concl` (appendix.hl:1433). Proof pending. -/
theorem VQFYMZY_concl : scsArrowV39 {scs4I3} {scs4T4, scs4M6'} := by
  sorry

/-- HOL `BNAWVNH_concl` (appendix.hl:1437). Proof pending. -/
theorem BNAWVNH_concl :
    scsArrowV39 {scs4M2} {scs3M1, scs3T4, scs4M6'} := by
  sorry

/-- HOL `RAWZDIB_concl` (appendix.hl:1439). Proof pending. -/
theorem RAWZDIB_concl :
    scsArrowV39 {scs4M3'} {scs3T1, scs3T6', scs4M6'} := by
  sorry

/-- HOL `MFKLVDK_concl` (appendix.hl:1441). Proof pending. -/
theorem MFKLVDK_concl :
    scsArrowV39 {scs4M4'} {scs3M1, scs3T4, scs3T3, scs4M7} := by
  sorry

/-- HOL `RYPDIXT_concl` (appendix.hl:1443). Proof pending. -/
theorem RYPDIXT_concl : scsArrowV39 {scs4M5'} {scs3T4, scs4M8} := by
  sorry

/-- HOL `GSXRFWM_concl` (appendix.hl:1445). Proof pending. -/
theorem GSXRFWM_concl : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → s.k = 4 →
    v ∈ MMsV39 s → scsGeneric v := by
  sorry

/-- HOL `WGDHPPI_concl` (appendix.hl:1448). Proof pending. -/
theorem WGDHPPI_concl : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → s.k = 4 →
    v ∈ MMsV39 s → {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ 1 := by
  sorry

/-- HOL `ASSWPOW_concl` (appendix.hl:1452). Proof pending. -/
theorem ASSWPOW_concl : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → s.k = 4 → scsBasicV39 s →
    s.b i (i + 1) ≤ 2 * h0 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
    xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53 := by
  sorry

/-- HOL `YEBWJNG_concl` (appendix.hl:1457). Proof pending. -/
theorem YEBWJNG_concl : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) → s.a p (p + 1) = 2 →
    dist (v p) (v (p + 1)) = 2 := by
  sorry

/-- HOL `TUAPYYU_concl` (appendix.hl:1465). Proof pending. -/
theorem TUAPYYU_concl : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) →
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  sorry

/-- HOL `WKZZEEH_concl` (appendix.hl:1473). Proof pending. -/
theorem WKZZEEH_concl : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) → ¬scsIsStr s v (p + 3) →
    ¬(dist (v p) (v (p + 3)) = cstab ∧ dist (v p) (v (p + 1)) = cstab) := by
  sorry

/-- HOL `PWEIWBZ_concl` (appendix.hl:1481). Proof pending. -/
theorem PWEIWBZ_concl : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    s.a p (p + 1) = 2 → dist (v p) (v (p + 1)) = 2 := by
  sorry

/-- HOL `VASYYAU_concl` (appendix.hl:1489). Proof pending. -/
theorem VASYYAU_concl : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    scsIsStr s v p →
    (dist (v p) (v (p + 1)) = s.a p (p + 1) ∧
      dist (v p) (v (p + 3)) = s.a p (p + 3)) := by
  sorry

/-- HOL `NWDGKXH_concl` (appendix.hl:1498). Proof pending. -/
theorem NWDGKXH_concl : scsArrowV39 {scs4M6'} {scs4T3, scs4T5} := by
  sorry

/-- HOL `EFLYGAU_concl` (appendix.hl:1500). Proof pending. -/
theorem EFLYGAU_concl :
    (∃ v : ℕ → V3, v ∈ MMsV39 scs4M7 ∧ cstab < dist (v 0) (v 2) ∧
      cstab < dist (v 1) (v 3)) → scsArrowV39 {scs4M7} {scs4M6'} := by
  sorry

/-- HOL `YOBIMPP_concl` (appendix.hl:1504). Proof pending. -/
theorem YOBIMPP_concl :
    scsArrowV39 {scs4M7} {scs3M1, scs3T3, scs3T4, scs4M6'} := by
  sorry

/-- HOL `BJTDWPS_concl` (appendix.hl:1506). Proof pending. -/
theorem BJTDWPS_concl :
    (∃ v : ℕ → V3, v ∈ MMsV39 scs4M8 ∧ cstab < dist (v 0) (v 2) ∧
      cstab < dist (v 1) (v 3)) → scsArrowV39 {scs4M8} {scs4M6', scs3T7} := by
  sorry

/-- HOL `MIQMCSN_concl` (appendix.hl:1510). Proof pending. -/
theorem MIQMCSN_concl :
    scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4} := by
  sorry

/-- HOL `LFLACKU_concl` (appendix.hl:1512). Proof pending. -/
theorem LFLACKU_concl : scsArrowV39 {scs3T1} {scs3T2, scs3T5} := by
  sorry

/-- HOL `CUXVZOZ_concl` (appendix.hl:1514). Proof pending. -/
theorem CUXVZOZ_concl : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (FF : Set (V3 × V3)) (k p1 : ℕ) (v : ℕ → V3),
      FF = Set.range (fun i => (v i, v (i + 1))) →
      isScsV39 s → k = s.k → 3 < k → v ∈ MMsV39 s → scsBasicV39 s → scsGeneric v →
      3 ≤ dist (v (p1 + k - 1)) (v (p1 + 1)) →
      (∀ i j, scsDiag k i j ∧ psort k (i, j) ≠ psort k (p1 + k - 1, p1 + 1) →
        s.a i j < dist (v i) (v j)) →
      (∀ i j, scsDiag k i j → 4 * h0 < s.b i j) →
      interiorAngle1 0 FF (v p1) < Real.pi →
      (Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
        interiorAngle1 0 FF (v (p1 + 1)) < Real.pi) →
      s.a p1 (p1 + 1) = 2 → s.b p1 (p1 + 1) ≤ 2 * h0 →
      2 ≤ dist (v (p1 + k - 1)) (v p1) →
      dist (v (p1 + k - 1)) (v p1) ≤ cstab →
      dist (v p1) (v (p1 + 1)) = 2 := by
  sorry

/-- HOL `CJBDXXN_concl` (appendix.hl:1534). Proof pending. -/
theorem CJBDXXN_concl : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (FF : Set (V3 × V3)) (k p1 : ℕ) (v : ℕ → V3),
      FF = Set.range (fun i => (v i, v (i + 1))) →
      isScsV39 s → k = s.k → 3 < k → v ∈ MMsV39 s → scsBasicV39 s → scsGeneric v →
      3 ≤ dist (v (p1 + 1)) (v (p1 + k - 1)) →
      (∀ i j, scsDiag k i j ∧ psort k (i, j) ≠ psort k (p1 + 1, p1 + k - 1) →
        s.a i j < dist (v i) (v j)) →
      (∀ i j, scsDiag k i j → 4 * h0 < s.b i j) →
      interiorAngle1 0 FF (v p1) < Real.pi →
      (Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
        interiorAngle1 0 FF (v (p1 + k - 1)) < Real.pi) →
      s.a p1 (p1 + k - 1) = 2 → s.b p1 (p1 + k - 1) ≤ 2 * h0 →
      2 ≤ dist (v (p1 + 1)) (v p1) →
      dist (v (p1 + 1)) (v p1) ≤ cstab →
      dist (v p1) (v (p1 + k - 1)) = 2 := by
  sorry

/-- HOL `YRTAFYH_concl` (appendix.hl:1554). Discharged 2026-09-30 (LocalAuto1
lane): pure override bookkeeping over `psort` — the diagonal slot of `b` is
replaced by `cstab`, all is_scs constraints transport through the psort toolkit
above. -/
theorem YRTAFYH_concl : ∀ (s : ScsV39) (i j : ℕ), isScsV39 s → scsBasicV39 s →
    3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j) := by
  intro s i j his hbasic hk hdg hac
  obtain ⟨h1, h2, h3, -, -, -, -, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -, -,
    h21⟩ := his
  set b' : ℕ → ℕ → ℝ :=
    fun x y => if psort s.k (i, j) = psort s.k (x, y) then cstab else s.b x y with hb'def
  have hts : scsStabDiagV39 s i j = mkUnadornedV39 s.k s.d s.a b' := by
    simp only [scsStabDiagV39, hb'def]
  have hb'periodic : Periodic2 b' s.k := by
    intro x y
    constructor
    · show b' (x + s.k) y = b' x y
      simp only [hb'def, la1psort_add_left, (h11 x y).1]
    · have hps : psort s.k (x, y + s.k) = psort s.k (x, y) := by
        rw [la1psort_symm, la1psort_add_left, la1psort_symm]
      show b' x (y + s.k) = b' x y
      simp only [hb'def, hps, (h11 x y).2]
  have hb'symm : ∀ x y, b' x y = b' y x := by
    intro x y
    by_cases hpxy : psort s.k (i, j) = psort s.k (x, y)
    · have hpyx : psort s.k (i, j) = psort s.k (y, x) := by rw [hpxy, la1psort_symm]
      simp only [hb'def, if_pos hpxy, if_pos hpyx]
    · have hyx : psort s.k (i, j) ≠ psort s.k (y, x) := by
        intro h
        exact hpxy (by rw [h, la1psort_symm])
      simp only [hb'def, if_neg hpxy, if_neg hyx]
      exact (h13 x y).2.2.2.1
  have hb'ge : ∀ x y, s.a x y ≤ b' x y := by
    intro x y
    by_cases hpxy : psort s.k (i, j) = psort s.k (x, y)
    · have hxy : s.a x y = s.a i j := by
        obtain hc | hc := la1psort_cases hpxy
        · rw [la1periodic2_mod h8 x y, hc.1.symm, hc.2.symm, ← la1periodic2_mod h8 i j]
        · rw [la1periodic2_mod h8 x y, hc.2.symm, hc.1.symm, ← la1periodic2_mod h8 j i,
            (h13 i j).1]
      have hbxy : b' x y = cstab := by simp only [hb'def, if_pos hpxy]
      rw [hbxy, hxy]
      exact hac
    · have hbxy : b' x y = s.b x y := by simp only [hb'def, if_neg hpxy]
      rw [hbxy]
      exact (h14 x y).1.trans ((h14 x y).2.1.trans (h14 x y).2.2)
  have hb'adj : ∀ x, psort s.k (i, j) ≠ psort s.k (x, x + 1) :=
    fun x heq => la1psort_diag s.k hdg heq
  have hb'nb : ∀ x, b' x (x + 1) = s.b x (x + 1) := fun x => if_neg (hb'adj x)
  rw [hts]
  refine ⟨⟨h1, h2, h3, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, h8, h8,
    hb'periodic, hb'periodic, fun _ _ => ⟨rfl, rfl⟩,
    fun x y => ⟨(h13 x y).1, (h13 x y).1, hb'symm x y, hb'symm x y, rfl⟩,
    fun x y => ⟨le_refl _, hb'ge x y, le_refl _⟩,
    h15, h16, fun x h3' => absurd h3'.symm hk.ne,
    fun x _ => by show b' x (x + 1) ≤ cstab; rw [hb'nb x]; exact h18 x hk,
    fun x y hj => hj.elim, fun x y hj => hj.elim, ?_⟩,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩⟩
  show {x : ℕ | x < s.k ∧ (2 * h0 < b' x (x + 1) ∨ 2 < s.a x (x + 1))}.ncard + s.k ≤ 6
  have seteq : {x : ℕ | x < s.k ∧ (2 * h0 < b' x (x + 1) ∨ 2 < s.a x (x + 1))} =
      {x : ℕ | x < s.k ∧ (2 * h0 < s.b x (x + 1) ∨ 2 < s.a x (x + 1))} := by
    ext x
    simp only [Set.mem_setOf_eq, hb'nb x]
  rw [seteq]
  exact h21


/-- HOL `BKOSSGE_concl` (appendix.hl:1564). Proof pending. -/
theorem BKOSSGE_concl : scsArrowV39 {scs3M1} {scs3T1, scs3T5} := by
  sorry

/-! ## Conclusions, part 5: the QKNVMLB slicing trio (appendix.hl:1055-1084) -/

/-- HOL `QKNVMLB1_concl` (appendix.hl:1055). Proof pending. -/
theorem QKNVMLB1_concl : ∀ (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    MMsV39 s vv → s.bm p q < 4 → (s.k = 4 ∨ s.bm p q ≤ cstab) → isScsV39 s →
    d' < 0.9 → scsDiag s.k p q →
    BBsV39 (scsHalfSliceV39 s p q d' mkj)
      (fun i => vv ((i + p) % (scsHalfSliceV39 s p q d' mkj).k)) := by
  sorry

/-- HOL `QKNVMLB2_concl` (appendix.hl:1064). Proof pending. -/
theorem QKNVMLB2_concl : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    (s', s'') = scsSliceV39 s p q d' d'' mkj →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    dsvV39 s vv ≤ dsvV39 s' (fun i => vv ((i + p) % s'.k)) +
      dsvV39 s'' (fun i => vv ((i + q) % s''.k)) := by
  sorry

/-- HOL `QKNVMLB3_concl` (appendix.hl:1075). Proof pending. -/
theorem QKNVMLB3_concl : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    (s', s'') = scsSliceV39 s p q d' d'' mkj →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    taustarV39 s' (fun i => vv ((i + p) % s'.k)) +
      taustarV39 s'' (fun i => vv ((i + q) % s''.k)) ≤ taustarV39 s vv := by
  sorry

/-! Coverage note: every appendix.hl item is carried above except the pure
term-level lets that the source itself re-declares or only feeds to other
chapters (the tuple pattern `scs_data` at appendix.hl:214, the terminal-case
quotations at appendix.hl:511-603, `ear_cs` and `terminal_tri_5405130650` at
appendix.hl:635-650).  The 21 mechanical theorems are proved; every other
`*_concl` keeps its `sorry` body pending the later discharge waves. -/

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
      `deformation`, `convex_local_fan` (ported here; the hypermap content of
      `local_fan` is deferred with `hypermapOfFan`, see Fan.lean head note).
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
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Local-fan primitives quoted by the appendix conclusions
(localization.hl:66-131; `local_fan`'s hypermap kit deferred with
`hypermapOfFan`, Fan.lean head note) -/

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

/-- HOL `local_fan (V,E,FF)` (WRGCVDR.hl:144 = localization.hl:66): `FAN
(vec 0,V,E)` at the hypermap `hypermap (HYP (vec 0,V,E))` with `FF` a
hypermap face and `dih2k H (CARD FF)`.  Skeleton: the `HYP`-hypermap kit
(`darts_of_hyp`/`ee_of_hyp`/`nn_of_hyp`/`ff_of_hyp` over `azim_cycle`) is the
Local-Fan chapter foundation and is deferred together with `hypermapOfFan`
(Fan.lean head note); the registry statements only need the signature. -/
def LocalFan (_V : Set V3) (_E : Set (Set V3)) (_FF : Set (V3 × V3)) : Prop := True

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

/-- HOL `unadorned_MMs_concl` (appendix.hl:676). Proof pending. -/
theorem unadorned_MMs_concl :
    ∀ s : ScsV39, unadornedV39 s → MMsV39 s = BBprime2V39 s := by
  sorry

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

/-- HOL `delta_x4` (sphere.hl:110); local copy for import hygiene
(`deltaX4f`, PackingAuto20). -/
noncomputable def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `delta_x5` (sphere.hl; Nonlin_def.hl:435): partial derivative of
`delta_x` at `x5`. BODY-FIX 2026-09-17: was a mis-port dropping the
`- x1 * x3 + x1 * x4` summands; this is the corrected 6-term body, verbatim
twin of LocalAuto11:165 `deltaX5f_p11` / LocalAuto21:113 `deltaX5_p21` /
LocalAuto22:120 `deltaX5_p22` (checked as `∂deltaXPA18/∂x5`), now canonical in
`Kepler.Text.SphereKit`. -/
noncomputable def deltaX5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x3 + x1 * x4 - x2 * x5 + x3 * x6 - x4 * x6 +
    x2 * (x1 - x2 + x3 + x4 - x5 + x6)

/-- HOL `mk_simplex1` (appendix.hl:862); `cross` <-> `cross3`
(PackingAuto18:86), `%` <-> `•`. BODY-FIX 2026-09-17: the `d5` coefficient
now picks up the corrected `deltaX5` (was the 4-term mis-port), so this
def's value has changed; the body is unchanged. -/
noncomputable def mkSimplex1 (v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ) : V3 :=
  let uinv := 1 / upsXPA18 x1 x2 x6
  let d := deltaXPA18 x1 x2 x3 x4 x5 x6
  let d5 := deltaX5 x1 x2 x3 x4 x5 x6
  let d4 := deltaX4 x1 x2 x3 x4 x5 x6
  let vcross := cross3 (v1 - v0) (v2 - v0)
  v0 + uinv • ((2 * Real.sqrt d) • vcross + d5 • (v1 - v0) + d4 • (v2 - v0))

/-- HOL `mk_planar2` (appendix.hl:870); flyspeck `mk_planar` is identified
with this def at the EYYPQDW2/EYYPQDW3 call sites (same argument shape). -/
noncomputable def mkPlanar2 (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ) : V3 :=
  let vcross := cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0))
  v0 + ((x1 + x3 - x5) / (2 * x1)) • (v1 - v0) +
    ((s / x1) * Real.sqrt (upsXPA18 x1 x3 x5 / upsXPA18 x1 x2 x6)) • vcross

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

/-- HOL `EQTTNZI1_concl` (appendix.hl:1110). Proof pending. -/
theorem EQTTNZI1_concl : ∀ s : ScsV39, isScsV39 s →
    (∀ i j, s.J i j → s.b i j = s.bm i j) →
    (s.J = fun _ _ => False ∨ 3 < s.k) →
    scsArrowV39 {s} {restrictionTyp1V39 s} := by
  sorry

/-- HOL `EQTTNZI2_concl` (appendix.hl:1115). Proof pending. -/
theorem EQTTNZI2_concl : ∀ (s t : ScsV39), isScsV39 s → s.am = s.bm →
    t = restrictionTyp2V39 s → (∀ i j, ¬s.J i j) → (∀ i, s.am i i = 0) →
    {i | i < t.k ∧ (2 * h0 < t.b i (i + 1) ∨ 2 < t.a i (i + 1))}.ncard + t.k ≤ 6 →
    scsArrowV39 {s} {t} := by
  sorry

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

/-- HOL `YXIONXL3_concl` (appendix.hl:1141). Proof pending. -/
theorem YXIONXL3_concl : ∀ (s : ScsV39) (i : ℕ), isScsV39 s →
    scsArrowV39 {s} {scsPropEquV39 s i} := by
  sorry

/-- HOL `LKGRQUI_concl` (appendix.hl:1144). Proof pending. -/
theorem LKGRQUI_concl : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
    isScsV39 s → (s', s'') = scsSliceV39 s p q d' d'' mkj →
    scsArrowV39 {s} {s', s''} := by
  sorry

/-- HOL `HXHYTIJ_concl` (appendix.hl:1147). Proof pending. -/
theorem HXHYTIJ_concl : ∀ (s : ScsV39) (vv ww : ℕ → V3), isScsV39 s →
    vv ∈ BBprime2V39 s → BBsV39 s ww →
    taustarV39 s vv < taustarV39 s ww ∨ BBindexV39 s vv ≤ BBindexV39 s ww := by
  sorry

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
slope value `8*y6/(y1*y2)` at `y6`. Proof pending. -/
theorem DRNDRDV_concl : ∀ y1 y2 y6 : ℝ,
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      (Set.univ : Set ℝ) := by
  sorry

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
    0 < deltaXPA18 x1 x2 x3 x4 x5 x6 →
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
    0 < deltaXPA18 x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    ContinuousAt (fun q => mkSimplex1 v0 v1 v2 x1 x2 x3 x4 q x6) x5 := by
  sorry

/-- HOL `EYYPQDW_concl` (appendix.hl:1244). Proof pending. -/
theorem EYYPQDW_concl : ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < upsXPA18 x1 x3 x5 → s = 1 ∨ s = -1 →
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
    0 < upsXPA18 x1 x3 x5 →
    ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3 := by
  sorry

/-- HOL `EYYPQDW3_concl` (appendix.hl:1268; `mk_planar` <-> `mkPlanar2`).
Proof pending. -/
theorem EYYPQDW3_concl : ∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < upsXPA18 x1 x3 x5 →
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
  sorry

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

/-- HOL `PEDSLGV1_concl` (appendix.hl:1379). Proof pending. -/
theorem PEDSLGV1_concl : ∀ (v : ℕ → V3) (i j : ℕ), v ∈ MMsV39 scs6I1 →
    scsDiag 6 i j → dist (v i) (v j) ≤ cstab →
    v ∈ MMsV39 (scsStabDiagV39 scs6I1 i j) := by
  sorry

/-- HOL `PEDSLGV2_concl` (appendix.hl:1385). Proof pending. -/
theorem PEDSLGV2_concl : ∀ v : ℕ → V3, v ∈ MMsV39 scs6I1 →
    (∀ i j, scsDiag 6 i j → cstab ≤ dist (v i) (v j)) → v ∈ MMsV39 scs6M1 := by
  sorry

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

/-- HOL `YRTAFYH_concl` (appendix.hl:1554). Proof pending. -/
theorem YRTAFYH_concl : ∀ (s : ScsV39) (i j : ℕ), isScsV39 s → scsBasicV39 s →
    3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j) := by
  sorry

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

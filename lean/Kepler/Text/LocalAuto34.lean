/-
LocalAuto34 — port of `scripts/local/IMJXPHR.hl` (11028 ln; 1 def + 117
theorems — the `v3_defor_v4` deformation/azim-continuity bank closing the
appendix-to-Local-Fan chapter).  The file mirrors the source layout: the
`v3_defor_v4` base deformation and its eta/composition kit, the
`ups_x`-positivity and continuity starters, the a/b-bound deformation kit
around the pair `(w l, w (SUC l))`, the `FF`-relabel/rho-node tower, the
azim-continuity family (`DEFORMATION_AZIM_*`, at `v2`, `v1`, `w (l+k-1)`,
any `v`, all `V`), the lunar affine-hull pair, the composite
`ZLZTHIC ==> MHAEYJN ==> _concl` registry arrows, and the `TWO_CASES` twins
of the whole tower ( neighbour `w (l+k-1)` instead of `w (SUC l)`), ending
in the master arrow `IMJXPHR`.

Encoding:
- HOL `real^3` <-> `V3`; `norm v pow 2` <-> `norm v ^ 2`; `dist(x,y)` <->
  `dist x y`; `SUC n` <-> `n + 1`; `w (l + k - 1)` kept verbatim; `--e < t` <->
  `-e < t`; `x MOD k` <-> `x % k`.
- `collinear {vec 0, a, b}` <-> `Collinear ℝ ({0, a, b} : Set V3)`;
  `aff_gt {vec 0} {u, v}` <-> `affGt {0} {u, v}`; `azim (vec 0) u v w` <->
  `azim 0 u v w`; `aff {a,b,c}` <-> `affineSpan ℝ {a,b,c}`.
- scs accessors: `scs_k_v39 s` <-> `s.k`, `scs_a_v39`/`scs_b_v39` <-> `s.a`/
  `s.b`, `scs_J_v39 s l i` <-> `s.J l i`, `scs_diag k l i` <-> `scsDiag k l i`;
  `is_scs_v39`/`MMs_v39`/`BBs_v39`/`taustar_v39`/`dsv_v39` <-> `isScsV39`/
  `MMsV39`/`BBsV39`/`taustarV39`/`dsvV39` (LocalAuto1); `h0`/`ball_annulus` <->
  `h0`/`ballAnnulus` (PackingAuto2).
- `v3_defor_v1 a v1 v2 x1 x2 x5 x6 x3` <-> `v3DeforV1_p17` (LocalAuto17);
  `ups_x` <-> `upsX`, `x cross y` <-> `cross3` (PackingAuto18); `rho_node1` <->
  `rhoNode1`, `interior_angle1` <-> `interiorAngle1`, `deformation` <->
  `Deformation`, `lunar` <-> `Lunar`, `generic` <-> `Generic`,
  `convex_local_fan` <-> `ConvexLocalFan`, `rho_fun` <-> `rhoFun`,
  `xrr` <-> `xrr` (LocalAuto1); `real_interval (a,b)` <-> `Icc a b`;
  `ITER i f x` <-> `f^[i] x`.
- `v3_defor_v4` (IMJXPHR.hl:87) is ported here as `v3DeforV4_p34` — NEEDS:
  merge with the NUXCOEA-lane copy (`v3DeforV4_p28`); that lane's olean was
  not built at port time, so this file carries its own twins (`epPair_p34` ~
  `epPair_p28`, `deformedFF4_p34` ~ `deformedFF_p28` for the v4 map).
- The pointwise relabel `IMAGE (\uv. (if FST uv = v2 then f else FST uv),
  (if SND uv = v2 then f else SND uv)) FF` is abbreviated `relabelFF_p34`;
  the deformed face `IMAGE (\uv. (v4 (FST uv) t, v4 (SND uv) t)) FF` is
  `deformedFF4_p34`; `@a. a,x IN FF` is `epPair_p34` (`Classical.epsilon`).
- `e3_fan`/`e2_fan`/`e1_fan` (fan.hl:1133/1138/1140) are twinned as
  `e3Fan_p34`/`e2Fan_p34`/`e1Fan_p34` (TopologyFan is not on this lane's
  import list; its `cross3` twin is private anyway) — NEEDS: merge with
  TopologyFan's public copies at the lane merge point.
- The `_concl` term templates are Props: `MHAEYJNv1_concl_p34`/
  `ZLZTHICv1_concl_p34` (the `&0<t /\ t<b` variants of the registry
  antecedents; the registry `Icc`-shaped `ZLZTHIC_concl`/`MHAEYJN_concl`
  themselves are LocalAuto1 theorems, used verbatim as hypothesis arguments
  of the composite arrows), `V3_DEFOR_CONVEX_LOCAL_FAN_concl_p34` (+ its
  `TWO_CASES` twin), `TAUSTAR_V3_DEFOR_concl_p34` (+ twin), `IMJXPHR_concl_p34`
  (aligned with LocalAuto1 `IMJXPHRv2_concl`).  The tautological conjuncts
  `(&10 = &10)`/`(&1 = &1)` of the source conclusions are dropped.
- Shadowed source names: `CROSS_LAGRANGE1` is stated twice identically
  (ported once); `DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM` and its
  `_TWO_CASES` twin have two DIFFERENT statements each (the surviving later
  one is the skolemised `?e. !t i.` form, ported as `..._COM_b_p34`).
- `check_completeness_claimA_concl` is a template-table item, not a theorem,
  and is not ported (same treatment as NUXCOEA lane).
- DISCHARGES: `IMJXPHR_p34` discharges the `IMJXPHRv2_concl` registry sorry
  (LocalAuto1:976); `V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_p34` and its
  `_TWO_CASES` twin carry the `ZLZTHIC_concl`/`MHAEYJN_concl` antecedents.
- No `native_decide`; proved items are mechanical (eta/funext, mod
  arithmetic, norm positivity from collinearity, the continuity lift,
  deformation interval shrinking, set-image identities, the
  finite-minimum skolemisation of per-index existence, rho-node transport,
  `BBs` periodicity).
- FILL LOG (2026-09-19, 92 -> 60 sorries, zero errors): filled
  `BBS_IMP_CONVEX_LOCAL_FAN`, `V3_DEFOR_ID`, the `UPS_X_POS_SEG(_C)`
  continuity window, `EXISTS_SMALL_{LE,LT}_CONST(_V1)` (continuity of
  `t |-> dist (v3_defor_v1 (x2 - t)) w` at `t = 0`), the `xrr`
  monotonicity pair (Cauchy-Schwarz + `h0 = 1.26` arithmetic), the WHOLE
  `V3_DEFOR_EQ_IN_FF_*` relabel tower (22 goals; residue-arithmetic
  neighbour bookkeeping + pointwise-relabel master), and the epsilon twins
  via the singleton-selection lemma.  STILL `sorry` (honest NEEDS): the
  azim-continuity family (LA14's own azim kit is sorried), lunar /
  interior-angle / taustar / convex-local-fan composite giants,
  `HYPER_MM_COLLINEAR` (+ the per-index `DEFORMATION_DIST_LE_*` that need
  its non-collinearity), `V3_DEFOR_DEFORMATION` (needs the
  `ups_x`-window deformation), `NOT_IN_V` family (needs the deformed-norm
  Cayley algebra, cf. sorried `EYYPQDW_NORMV3_p17`), the `e2Fan`/`aff_gt`
  dot-characterisation quartet, `OPEN_RELA_AFF_GT`, `DSV_V3_DEFOR_EQ`,
  `CARD_FF`, `RHO_FUN_DEFORMATION`, `IMJXPHR`.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto17
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Definitions -/

/-- HOL `v3_defor_v4 a x1 x2 x6 v1 w v t` (IMJXPHR.hl:87); the base
deformation fixing every point except `w`.  NEEDS: merge with NUXCOEA-lane
`v3DeforV4_p28`. -/
noncomputable def v3DeforV4_p34 (a x1 x2 x6 : ℝ) (v1 w v : V3) (t : ℝ) : V3 :=
  if v = w then v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - t) else v

/-- HOL `@a. a, x IN FF` (epsilon witness of an edge ending at `x`). -/
noncomputable def epPair_p34 (FF : Set (V3 × V3)) (x : V3) : V3 :=
  Classical.epsilon fun a => (a, x) ∈ FF

/-- The deformed face `IMAGE (\uv. (v3_defor_v4 (-1) x1 x2 x6 v1 v2 (FST uv) t,
v3_defor_v4 (-1) x1 x2 x6 v1 v2 (SND uv) t)) FF` used by every azim /
interior-angle statement. -/
noncomputable def deformedFF4_p34 (x1 x2 x6 : ℝ) (v1 v2 : V3) (t : ℝ)
    (FF : Set (V3 × V3)) : Set (V3 × V3) :=
  (fun d : V3 × V3 => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.1 t,
    v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.2 t)) '' FF

/-- The pointwise relabel of `FF` sending every `v2`-coordinate to the
deformed point `f` (IMJXPHR.hl:2158 et al.). -/
noncomputable def relabelFF_p34 (f v2 : V3) (FF : Set (V3 × V3)) : Set (V3 × V3) :=
  (fun d : V3 × V3 => (if d.1 = v2 then f else d.1, if d.2 = v2 then f else d.2)) '' FF

/-- HOL fan.hl:1133 `e3_fan` (unit vector along `v - x`).  NEEDS: merge with
TopologyFan `e3Fan`. -/
noncomputable def e3Fan_p34 (x v _u : V3) : V3 := ‖v - x‖⁻¹ • (v - x)

/-- HOL fan.hl:1138 `e2_fan`.  NEEDS: merge with TopologyFan `e2Fan`. -/
noncomputable def e2Fan_p34 (x v u : V3) : V3 :=
  ‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ • cross3 (e3Fan_p34 x v u) (u - x)

/-- HOL fan.hl:1140 `e1_fan`.  NEEDS: merge with TopologyFan `e1Fan`. -/
noncomputable def e1Fan_p34 (x v u : V3) : V3 := cross3 (e2Fan_p34 x v u) (e3Fan_p34 x v u)

/-- HOL `MHAEYJNv1_concl` (IMJXPHR.hl:5464): the `&0 < t /\ t < b` variant of
the registry `MHAEYJN_concl` (LocalAuto1) used by this file's composites. -/
def MHAEYJNv1_concl_p34 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (v w u : V3),
    ConvexLocalFan V E FF →
    Lunar v w V E →
    Deformation f V a b →
    interiorAngle1 0 FF v < Real.pi →
    u ∈ V → u ≠ v → u ≠ w →
    (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
    (∀ t : ℝ, 0 < t → t < b → f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Lunar v w ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- HOL `ZLZTHICv1_concl` (IMJXPHR.hl:5483): the `&0 < t /\ t < b` variant of
the registry `ZLZTHIC_concl` (LocalAuto1). -/
def ZLZTHICv1_concl_p34 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3),
    ConvexLocalFan V E FF →
    Generic V E →
    Deformation f V a b →
    (∀ v ∈ V, ∀ t : ℝ, 0 < t → t < b → interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Generic ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- The registry `MHAEYJN_concl` (appendix.hl:25; LocalAuto1 statement) as a
`Prop` (LocalAuto1 carries it as a theorem/proof, which cannot sit in a
hypothesis position).  NEEDS: merge with NUXCOEA-lane `MHAEYJN_prop_p28`. -/
def MHAEYJN_prop_p34 : Prop :=
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
        ((fun e => (fun v => f v t) '' e) '' E)

/-- The registry `ZLZTHIC_concl` (appendix.hl:45; LocalAuto1 statement) as a
`Prop`.  NEEDS: merge with NUXCOEA-lane `ZLZTHIC_prop_p28`. -/
def ZLZTHIC_prop_p34 : Prop :=
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
        ((fun e => (fun v => f v t) '' e) '' E)

/-- HOL `V3_DEFOR_CONVEX_LOCAL_FAN_concl` (IMJXPHR.hl:5500).  The free
`x1 x2 x6 v1 v2 a` of the source template are quantified here; the
tautologies `&10 = &10` / `&1 = &1` are dropped. -/
def V3_DEFOR_CONVEX_LOCAL_FAN_concl_p34 : Prop :=
  ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 : ℝ) (v1 v2 : V3) (a : ℝ),
    s.k = k → isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    3 < k →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    ¬(2 = ‖v2‖) →
    (∀ i, ¬s.J l i) →
    w l = v2 → w (l + 1) = v1 →
    ‖v1‖ ^ 2 = x1 → ‖v2‖ ^ 2 = x2 → ‖v1 - v2‖ ^ 2 = x6 → a = -1 →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      ConvexLocalFan (Set.range fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)
        (Set.range fun i => {v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t})
        (Set.range fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t))

/-- HOL `V3_DEFOR_CONVEX_LOCAL_FAN_TWO_CASES_concl` (IMJXPHR.hl:9135): same
conclusion with the fixed neighbour `w (l + k - 1)`. -/
def V3_DEFOR_CONVEX_LOCAL_FAN_TWO_CASES_concl_p34 : Prop :=
  ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 : ℝ) (v1 v2 : V3) (a : ℝ),
    s.k = k → isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    3 < k →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    ¬(2 = ‖v2‖) →
    (∀ i, ¬s.J l i) →
    w l = v2 → w (l + k - 1) = v1 →
    ‖v1‖ ^ 2 = x1 → ‖v2‖ ^ 2 = x2 → ‖v1 - v2‖ ^ 2 = x6 → a = -1 →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      ConvexLocalFan (Set.range fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)
        (Set.range fun i => {v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t})
        (Set.range fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t))

/-- HOL `TAUSTAR_V3_DEFOR_concl` (IMJXPHR.hl:6119). -/
def TAUSTAR_V3_DEFOR_concl_p34 : Prop :=
  ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 a e1 : ℝ) (v1 v2 : V3),
    3 < k → s.k = k → isScsV39 s → w ∈ MMsV39 s →
    w l = v2 → w (l + 1) = v1 →
    0 < x1 → 0 < x2 → 0 < x6 →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    ¬Collinear ℝ ({0, v1, v2} : Set V3) →
    ‖v1‖ ^ 2 = x1 → ‖v2‖ ^ 2 = x2 → ‖v1 - v2‖ ^ 2 = x6 → a = -1 →
    ¬(2 = ‖w l‖) →
    (∀ i, ¬s.J l i) →
    (∀ t : ℝ, 0 < t → t < e1 →
      BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)) →
    0 < e1 →
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      taustarV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t) < taustarV39 s w

/-- HOL `TAUSTAR_V3_DEFOR_TWO_CASES_concl` (IMJXPHR.hl:9504). -/
def TAUSTAR_V3_DEFOR_TWO_CASES_concl_p34 : Prop :=
  ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 a e1 : ℝ) (v1 v2 : V3),
    3 < k → s.k = k → isScsV39 s → w ∈ MMsV39 s →
    w l = v2 → w (l + k - 1) = v1 →
    0 < x1 → 0 < x2 → 0 < x6 →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    ¬Collinear ℝ ({0, v1, v2} : Set V3) →
    ‖v1‖ ^ 2 = x1 → ‖v2‖ ^ 2 = x2 → ‖v1 - v2‖ ^ 2 = x6 → a = -1 →
    ¬(2 = ‖w l‖) →
    (∀ i, ¬s.J l i) →
    (∀ t : ℝ, 0 < t → t < e1 →
      BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)) →
    0 < e1 →
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      taustarV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t) < taustarV39 s w

/-- HOL `IMJXPHR_concl` (IMJXPHR.hl:9682), aligned with LocalAuto1
`IMJXPHRv2_concl`. -/
def IMJXPHR_concl_p34 : Prop :=
  ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    s.k = k → isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    3 < k →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    ¬(2 = ‖w l‖) →
    (∀ i, scsDiag k l i → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1)))

/-! ## Section 0: shared kit -/

/-! ### Shared helper kit (filled 2026-09: continuity-at-`t=0` family).

The `v3_defor_v1`-deformation is continuous in the time argument around
`x3 = x2` (`EYYPQDW_CONTINUOUS_AT_X_p17`, LocalAuto17), fixes `v2` there
(`v3DeforV1_at_x2_p34` below), and `ups_x x1 x2 x6 > 0` off the
non-collinearity (`upsX_pos_nc_p34`, via the public
`TRI_UPS_X_STRICT_POS`-free Cauchy-Schwarz route).  These three facts power
every `EXISTS_SMALL_*` / `DEFORMATION_DIST_LE_*` / `_NOT_IN_V`-shape lemma
below. -/

/-- Non-collinearity of `{0, v1, v2}` gives nonzero norms. -/
private theorem nc_norm_pos_p34 {v1 v2 : V3} (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3)) :
    0 < ‖v1‖ ∧ 0 < ‖v2‖ := by
  have twopt : ∀ u : V3, Collinear ℝ ({0, u} : Set V3) := by
    intro u
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨(0 : V3), u, fun p hp => ?_⟩
    have hpu : p = 0 ∨ p = u := by simpa using hp
    rcases hpu with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  refine ⟨norm_pos_iff.mpr ?_, norm_pos_iff.mpr ?_⟩
  · intro h
    apply hnc
    rw [h, Set.insert_idem]
    exact twopt v2
  · intro h
    apply hnc
    rw [h, collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨(0 : V3), v1, fun p hp => ?_⟩
    rcases Set.mem_insert_iff.mp hp with hp | hp
    · subst hp
      exact ⟨0, by simp⟩
    · rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst hp
        exact ⟨1, by simp⟩
      · rcases Set.mem_singleton_iff.mp hp with hp
        subst hp
        exact ⟨0, by simp⟩

/-- Non-collinearity of `{0, v1, v2}` forbids `v2` being a multiple of
`v1` (via `collinear3_iff_smul`). -/
private theorem nc_not_smul_p34 {v1 v2 : V3} (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3)) :
    ∀ r : ℝ, v2 ≠ r • v1 := by
  obtain ⟨h1, -⟩ := nc_norm_pos_p34 hnc
  intro r hr
  apply hnc
  rw [show Collinear ℝ ({0, v1, v2} : Set V3) = Collinear3 0 v1 v2 from rfl,
    collinear3_iff_smul (by simpa using h1)]
  exact ⟨r, by simpa using hr⟩

/-- `ups_x x1 x2 x6 > 0` off the non-collinearity: `upsX` is
`4 (x1 x2 - (v1·v2)^2)`, and Cauchy-Schwarz is strict for independent
vectors. -/
private theorem upsX_pos_nc_p34 {v1 v2 : V3} {x1 x2 x6 : ℝ}
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    0 < upsX x1 x2 x6 := by
  obtain ⟨h1, h2⟩ := nc_norm_pos_p34 hnc
  have hd1 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have hd2 : v2 ⬝ᵥ v2 = x2 := (norm_sq_eq_dot v2).symm.trans hx2
  have hexp : (x1 + x2 - x6) / 2 = v1 ⬝ᵥ v2 := by
    have hnn : inner ℝ (v1 - v2) (v1 - v2) = ‖v1 - v2‖ ^ 2 :=
      real_inner_self_eq_norm_sq (v1 - v2)
    have hdc : v2 ⬝ᵥ v1 = v1 ⬝ᵥ v2 := dotProduct_comm _ _
    have key : x6 = x1 + x2 - 2 * (v1 ⬝ᵥ v2) := by
      rw [← hx6, ← hnn]
      simp only [inner_sub_right, inner_sub_left]
      rw [inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot, hd1, hd2, hdc]
      ring
    rw [key]
    ring
  have hcs : |v1 ⬝ᵥ v2| < ‖v1‖ * ‖v2‖ := by
    rw [← inner_eq_dot]
    rcases lt_or_eq_of_le (abs_real_inner_le_norm v1 v2) with h | h
    · exact h
    · exfalso
      rw [← Real.norm_eq_abs] at h
      obtain ⟨r, -, hr⟩ :=
        (norm_inner_eq_norm_iff (𝕜 := ℝ) (norm_pos_iff.mp h1) (norm_pos_iff.mp h2)).mp h
      exact absurd hr (nc_not_smul_p34 hnc r)
  have hprod : (0 : ℝ) < ‖v1‖ * ‖v2‖ := mul_pos h1 h2
  have hsq : (v1 ⬝ᵥ v2) ^ 2 < x1 * x2 := by
    have h2v : (‖v1‖ * ‖v2‖) ^ 2 = x1 * x2 := by
      have e1 : (‖v1‖ * ‖v2‖) ^ 2 = ‖v1‖ ^ 2 * ‖v2‖ ^ 2 := by rw [sq]; ring
      rw [e1, hx1, hx2]
    have hd2' : (v1 ⬝ᵥ v2) ^ 2 = |v1 ⬝ᵥ v2| ^ 2 := (sq_abs _).symm
    have hneg : -(‖v1‖ * ‖v2‖) < |v1 ⬝ᵥ v2| := by
      linarith [hcs, abs_nonneg (v1 ⬝ᵥ v2)]
    rw [hd2', ← h2v]
    exact sq_lt_sq' hneg hcs
  have hu : upsX x1 x2 x6 = 4 * (x1 * x2 - (v1 ⬝ᵥ v2) ^ 2) := by
    unfold upsX
    rw [← hexp]
    field_simp
    ring
  rw [hu]
  linarith

/-- The deformation fixes `v2` at time `x3 = x2` (`v3_defor_v1` evaluates
to `v2`); algebra on the explicit completion formula. -/
private theorem v3DeforV1_at_x2_p34 (a : ℝ) (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 x2 = v2 := by
  obtain ⟨h1, h2⟩ := nc_norm_pos_p34 hnc
  have hd1 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have hd2 : v2 ⬝ᵥ v2 = x2 := (norm_sq_eq_dot v2).symm.trans hx2
  have hx1n : (0 : ℝ) < x1 := by rw [← hx1]; exact pow_pos h1 2
  have hexp : (x1 + x2 - x6) / 2 = v1 ⬝ᵥ v2 := by
    have hnn : inner ℝ (v1 - v2) (v1 - v2) = ‖v1 - v2‖ ^ 2 :=
      real_inner_self_eq_norm_sq (v1 - v2)
    have hdc : v2 ⬝ᵥ v1 = v1 ⬝ᵥ v2 := dotProduct_comm _ _
    have key : x6 = x1 + x2 - 2 * (v1 ⬝ᵥ v2) := by
      rw [← hx6, ← hnn]
      simp only [inner_sub_right, inner_sub_left]
      rw [inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot, hd1, hd2, hdc]
      ring
    rw [key]
    ring
  have hups : 0 < upsX x1 x2 x6 := upsX_pos_nc_p34 hnc hx1 hx2 hx6
  have hsqr : Real.sqrt (upsX x1 x2 x6 / upsX x1 x2 x6) = 1 := by
    rw [div_self (ne_of_gt hups)]
    exact Real.sqrt_one
  have hcross : cross3 v1 (cross3 v1 v2) = (v1 ⬝ᵥ v2) • v1 - x1 • v2 := by
    rw [cross3, cross3, cross_cross_eq_smul_sub_smul', hd1]
    simp
  have h1s : (-1 : ℝ) / x1 * (v1 ⬝ᵥ v2) = -(v1 ⬝ᵥ v2 / x1) := by field_simp
  have h2s : (-1 : ℝ) / x1 * x1 = -1 := by field_simp
  simp only [v3DeforV1_p17, hsqr, mul_one, ha]
  rw [hcross]
  have hc1 : (x1 + x2 - x6) / (2 * x1) = (v1 ⬝ᵥ v2) / x1 := by
    rw [← hexp]
    field_simp
  rw [hc1, smul_sub, smul_smul, smul_smul, h1s, h2s, neg_one_smul, sub_neg_eq_add,
    ← add_assoc, ← add_smul, add_neg_cancel, zero_smul, zero_add]

/-- The `t ↦ dist (v3_defor_v1 (x2 - t)) y` profile is continuous at `t = 0`
(`EYYPQDW_CONTINUOUS_AT_X_p17` composed with `t ↦ x2 - t`). -/
private theorem deforV1_dist_cont_p34 (a : ℝ) (v1 v2 y : V3) (x1 x2 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ContinuousAt (fun t : ℝ => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) y) 0 := by
  obtain ⟨hn1, hn2⟩ := nc_norm_pos_p34 hnc
  have hups : 0 < upsX x1 x2 x6 := upsX_pos_nc_p34 hnc hx1 hx2 hx6
  have hbase := EYYPQDW_CONTINUOUS_AT_X_p17 a v1 v2 x1 x2 x2 1 x6 x6 h1 h2 h2 one_pos h6 h6
    hnc hx1 hx2 hx6 (by simp [ha]) hups
  have hdist : ContinuousAt
      (fun u : ℝ => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 u) y) (x2 - 0) := by
    rw [sub_zero]
    exact hbase.dist continuousAt_const
  have hshift : ContinuousAt (fun t : ℝ => (x2 - t : ℝ)) 0 :=
    (continuousAt_const.sub continuousAt_id)
  exact hdist.comp hshift

/-- HOL `FUN_V3_DEFOR` (IMJXPHR.hl:91). -/
theorem FUN_V3_DEFOR_p34 (a x1 x2 x6 : ℝ) (v1 w v : V3) :
    v3DeforV4_p34 a x1 x2 x6 v1 w v = fun t => v3DeforV4_p34 a x1 x2 x6 v1 w v t := rfl

/-- HOL `MOD_ADD_SUB_1` (IMJXPHR.hl:106). -/
theorem MOD_ADD_SUB_1_p34 {k l : ℕ} (hk : 1 < k) :
    ¬((l + k - 1) % k = l % k) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · intro hcon
    rw [Nat.zero_add, Nat.zero_mod] at hcon
    rw [Nat.mod_eq_of_lt (by omega : k - 1 < k)] at hcon
    omega
  · intro hcon
    have h1 : (l + k - 1) % k = (l - 1) % k := by
      rw [show l + k - 1 = (l - 1) + k by omega, Nat.add_mod_right]
    rw [h1] at hcon
    set r := (l - 1) % k with _hr
    have hrk : r < k := Nat.mod_lt _ (by omega)
    have h2 : l % k = (r + 1) % k := by
      conv_lhs => rw [show l = l - 1 + 1 by omega]
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
    rw [h2] at hcon
    rcases Nat.lt_or_ge (r + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hcon
      omega
    · have heq : r + 1 = k := by omega
      rw [heq, Nat.mod_self] at hcon
      omega

/-- HOL `BBS_IMP_CONVEX_LOCAL_FAN` (IMJXPHR.hl:97). -/
theorem BBS_IMP_CONVEX_LOCAL_FAN_p34 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (hk : 3 < k) (hkk : s.k = k) (hBB : BBsV39 s w) :
    ConvexLocalFan (Set.range w)
      (Set.range fun i => {w i, w (i + 1)})
      (Set.range fun i => (w i, w (i + 1))) := by
  rcases hBB.2.2.2 with h3 | hcf
  · exact absurd h3 (by omega)
  · exact hcf

/-- HOL `UPS_X_POS_SEG` (IMJXPHR.hl:118). -/
theorem UPS_X_POS_SEG_p34 (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (h2 : 0 < x2) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → 0 < upsX x1 (x2 - t) x6 ∧ 0 < x2 - t := by
  obtain ⟨e1, he1, hmem⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      ((LIFT_UPS_CONTINUOUS_p17 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6).preimage_mem_nhds
        (Ioi_mem_nhds (upsX_pos_nc_p34 hnc hx1 hx2 hx6)))
  refine ⟨min e1 (x2 / 2), lt_min he1 (half_pos h2), fun t ht => ?_⟩
  have habs : |t| < min e1 (x2 / 2) := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  have hball : x2 - t ∈ Metric.ball x2 e1 := by
    have hx : (x2 - t) - x2 = -t := by ring
    rw [Metric.mem_ball, Real.dist_eq, hx, abs_neg]
    exact lt_of_lt_of_le habs (min_le_left e1 (x2 / 2))
  have hup := Set.mem_Ioi.mp (hmem (x2 - t) hball)
  refine ⟨hup, ?_⟩
  have hpos : t < x2 := by
    have h3' := lt_of_lt_of_le habs (min_le_right e1 (x2 / 2))
    rw [abs_lt] at h3'
    linarith
  linarith

/-- HOL `UPS_X_POS_SEG_C` (IMJXPHR.hl:152). -/
theorem UPS_X_POS_SEG_C_p34 (v1 v2 : V3) (x1 x2 x6 c : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (h2 : 0 < x2) (hc : 0 < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → 0 < upsX x1 (x2 - t) x6 ∧ 0 < x2 - t ∧ t < c := by
  obtain ⟨e1, he1, hmem⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      ((LIFT_UPS_CONTINUOUS_p17 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6).preimage_mem_nhds
        (Ioi_mem_nhds (upsX_pos_nc_p34 hnc hx1 hx2 hx6)))
  refine ⟨min (min e1 (x2 / 2)) c, lt_min (lt_min he1 (half_pos h2)) hc, fun t ht => ?_⟩
  have habs : |t| < min (min e1 (x2 / 2)) c := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  have hball : x2 - t ∈ Metric.ball x2 e1 := by
    have hx : (x2 - t) - x2 = -t := by ring
    rw [Metric.mem_ball, Real.dist_eq, hx, abs_neg]
    exact lt_of_lt_of_le habs ((min_le_left (min e1 (x2 / 2)) c).trans (min_le_left e1 (x2 / 2)))
  have hup := Set.mem_Ioi.mp (hmem (x2 - t) hball)
  refine ⟨hup, ?_, ?_⟩
  · have h1' := lt_of_lt_of_le (lt_of_lt_of_le habs (min_le_left (min e1 (x2 / 2)) c)) (min_le_right e1 (x2 / 2))
    rw [abs_lt] at h1'
    linarith
  · exact lt_of_abs_lt (lt_of_lt_of_le habs (min_le_right (min e1 (x2 / 2)) c))

/-- HOL `V3_DEFOR_V1_O_DEF` (IMJXPHR.hl:190). -/
theorem V3_DEFOR_V1_O_DEF_p34 (a : ℝ) (v1 w : V3) (x1 x2 x6 : ℝ) :
    (fun t => v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - t)) =
      (fun x3 => v3DeforV1_p17 a v1 w x1 x2 x6 x6 x3) ∘ (fun t => x2 - t) := rfl

/-- HOL `V3_DEFOR_ID` (IMJXPHR.hl:194). -/
theorem V3_DEFOR_ID_p34 (v1 w : V3) (x1 x2 x6 a : ℝ)
    (h1 : 0 < x1) (hnc : ¬Collinear ℝ ({0, v1, w} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖w‖ ^ 2 = x2) (hx6 : ‖v1 - w‖ ^ 2 = x6)
    (ha : a = -1) :
    v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - 0) = w := by
  rw [sub_zero]
  exact v3DeforV1_at_x2_p34 a v1 w x1 x2 x6 hnc hx1 hx2 hx6 ha

/-- HOL `V3_DEFOR_DEFORMATION` (IMJXPHR.hl:228). -/
theorem V3_DEFOR_DEFORMATION_p34 (v1 w : V3) (V : Set V3) (x1 x2 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h4 : 0 < x4) (h5 : 0 < x5) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, w} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖w‖ ^ 2 = x2) (hx6 : ‖v1 - w‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ Deformation (v3DeforV4_p34 a x1 x2 x6 v1 w) V (-e) e := by
  sorry

/-- HOL `V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION` (IMJXPHR.hl:279). -/
theorem V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION_p34 (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hball : v2 ∈ ballAnnulus) (hn : ‖v2‖ ≠ 2) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      v3DeforV4_p34 a x1 x2 x6 v1 v2 v2 t ∈ ballAnnulus := by
  sorry

/-- HOL `NORM_POS_COLLINEAR` (IMJXPHR.hl:321). -/
theorem NORM_POS_COLLINEAR_p34 (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    0 < x1 ∧ 0 < x2 ∧ 0 < x6 := by
  have twopt : ∀ u : V3, Collinear ℝ ({0, u} : Set V3) := by
    intro u
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨(0 : V3), u, fun p hp => ?_⟩
    have hpu : p = 0 ∨ p = u := by simpa using hp
    rcases hpu with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  have hv1 : v1 ≠ 0 := by
    intro h
    apply hnc
    rw [h, Set.insert_idem]
    exact twopt v2
  have hv2 : v2 ≠ 0 := by
    intro h
    apply hnc
    rw [h, collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨(0 : V3), v1, fun p hp => ?_⟩
    rcases Set.mem_insert_iff.mp hp with hp | hp
    · subst hp
      exact ⟨0, by simp⟩
    · rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst hp
        exact ⟨1, by simp⟩
      · rcases Set.mem_singleton_iff.mp hp with hp
        subst hp
        exact ⟨0, by simp⟩
  have hv12 : v1 - v2 ≠ 0 := by
    intro h
    apply hnc
    rw [show v1 = v2 from sub_eq_zero.mp h, collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨(0 : V3), v2, fun p hp => ?_⟩
    rcases Set.mem_insert_iff.mp hp with hp | hp
    · subst hp
      exact ⟨0, by simp⟩
    · rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst hp
        exact ⟨1, by simp⟩
      · rcases Set.mem_singleton_iff.mp hp with hp
        subst hp
        exact ⟨1, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hx1]; exact pow_pos (norm_pos_iff.mpr hv1) 2
  · rw [← hx2]; exact pow_pos (norm_pos_iff.mpr hv2) 2
  · rw [← hx6]; exact pow_pos (norm_pos_iff.mpr hv12) 2

/-- HOL `HYPER_MM_COLLINEAR` (IMJXPHR.hl:363). -/
theorem HYPER_MM_COLLINEAR_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hk : 3 < k)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    0 < x1 ∧ 0 < x2 ∧ 0 < x6 ∧ ¬Collinear ℝ ({0, v1, v2} : Set V3) := by
  sorry

/-- HOL `EYYPQDW_CONTINUOUS_LIFT_DIST` (IMJXPHR.hl:404); the HOL `lift`
wrapper is dropped (`ℝ`-valued `dist`). -/
theorem EYYPQDW_CONTINUOUS_LIFT_DIST_p34 (v1 v2 v : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5) :
    ContinuousAt (fun y => dist (v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 y) v) x3 := by
  exact (EYYPQDW_CONTINUOUS_AT_X_p17 a v1 v2 x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
    hnc hx1 hx2 hx6 ha hups).dist continuousAt_const

/-- HOL `EXISTS_SMALL_LE_CONST` (IMJXPHR.hl:427). -/
theorem EXISTS_SMALL_LE_CONST_p34 (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hclt : c < dist v2 w) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w := by
  have hclt' : c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - 0)) w := by
    rwa [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha]
  obtain ⟨e1, he1, hmem⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      ((deforV1_dist_cont_p34 a v1 v2 w x1 x2 x6 h1 h2 h6 hnc hx1 hx2 hx6 ha).preimage_mem_nhds
        (Ioi_mem_nhds hclt'))
  refine ⟨e1, he1, fun t ht => ?_⟩
  have hb : t ∈ Metric.ball 0 e1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht.1]
    exact ht.2
  exact Set.mem_Ioi.mp (hmem t hb)

/-- HOL `EXISTS_SMALL_LE_CONST_V1` (IMJXPHR.hl:456). -/
theorem EXISTS_SMALL_LE_CONST_V1_p34 (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hclt : c < dist v2 w) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w := by
  have hclt' : c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - 0)) w := by
    rwa [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha]
  obtain ⟨e1, he1, hmem⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      ((deforV1_dist_cont_p34 a v1 v2 w x1 x2 x6 h1 h2 h6 hnc hx1 hx2 hx6 ha).preimage_mem_nhds
        (Ioi_mem_nhds hclt'))
  refine ⟨e1, he1, fun t ht => ?_⟩
  have hb : t ∈ Metric.ball 0 e1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact abs_lt.mpr ht
  exact Set.mem_Ioi.mp (hmem t hb)

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A` (IMJXPHR.hl:482). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_p34 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hbound : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) → s.a l j < dist v2 (w j)) :
    ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
  -- NEEDS: the `MMs`-collinearity kit (HYPER_MM_COLLINEAR, still sorried):
  -- the profile is continuous and strict at `t = 0`, but the strictness
  -- `s.a l j < dist v2 (w j)` only feeds `v3DeforV1` machinery after
  -- `¬Collinear {0, v1, v2}` is available, which this per-index lemma's
  -- hypotheses do not (yet) provide.
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_SUC` (IMJXPHR.hl:501). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hbound : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) → s.a l j < dist v2 (w j)) :
    ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
  sorry

/-- The finite-minimum skolemisation used by every `_COM` lemma: from
per-index existence and downward closure of the predicate in the radius. -/
theorem minWitness_p34 {R : ℕ → ℝ → Prop} {T : Finset ℕ}
    (hmono : ∀ (i : ℕ) (e : ℝ), R i e → ∀ e' : ℝ, 0 < e' → e' ≤ e → R i e')
    (hne : T.Nonempty)
    (h : ∀ i ∈ T, ∃ e : ℝ, 0 < e ∧ R i e) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ i ∈ T, R i e0 := by
  choose! f hf hR using h
  obtain ⟨m, hm, hle⟩ := Finset.exists_min_image T f hne
  exact ⟨f m, hf m hm, fun i hi => hmono i (f i) (hR i hi) (f m) (hf m hm) (hle i hi)⟩

/-- Periodicity fold (NUXCOEA-lane `modPeriodic` kit): a `k`-periodic
function only depends on the residue. -/
theorem modFold_p34 {α : Sort u} {f : ℕ → α} {k : ℕ} (hk : 0 < k)
    (hper : ∀ i, f (i + k) = f i) (j : ℕ) : f j = f (j % k) := by
  have key : ∀ q j : ℕ, f (j + q * k) = f j := by
    intro q
    induction q with
    | zero => intro j; simp
    | succ q ih =>
      intro j
      have heq : j + (q + 1) * k = (j + q * k) + k := by rw [Nat.succ_mul]; omega
      rw [heq, hper, ih]
  have hj : j = j % k + (j / k) * k := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div j k).symm
  conv_lhs => rw [hj]
  rw [key]

/-- `MMs` realisations are `s.k`-periodic (via `MMs -> BBprime2 -> BBprime ->
BBs`). -/
theorem MMs_periodic_p34 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (hkk : s.k = k)
    (hmw : w ∈ MMsV39 s) : ∀ i, w (i + k) = w i := by
  have hBB : BBsV39 s w := by
    have h := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h
    have h2 := h.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.1
  intro i
  rw [← hkk]
  exact hBB.2.1 i

/-- The `a`-table of an scs system is periodic in the second index. -/
theorem scsA_periodic_p34 (s : ScsV39) (k : ℕ) (hs : isScsV39 s) (hkk : s.k = k)
    (l : ℕ) : ∀ i, s.a l (i + k) = s.a l i := by
  intro i
  rw [← hkk]
  have hpa : Periodic2 s.a s.k := hs.2.2.2.2.2.2.2.1
  exact (hpa l i).2

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC` (IMJXPHR.hl:522).  Sits on
the (sorried) per-index `A_SUC` parent via the finite-minimum argument over
the residues `< k`, folding arbitrary indices back by periodicity. -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hbound : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) → s.a l j < dist v2 (w j)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ j : ℕ,
      ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
      s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_p34 s k l w v1 v2 x1 x2 x6 a hs hmw
    hkk hk hl hl1 hx1 hx2 hx6 ha hbound
  have hper_a := scsA_periodic_p34 s k hs hkk l
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  set T : Finset ℕ := (Finset.range k).filter
    (fun i => l % k ≠ i % k ∧ (l + 1) % k ≠ i % k) with hT
  have hmono : ∀ (i : ℕ) (e : ℝ),
      (∀ τ : ℝ, 0 < τ ∧ τ < e → s.a l i < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i)) →
      ∀ e' : ℝ, 0 < e' → e' ≤ e →
      ∀ τ : ℝ, 0 < τ ∧ τ < e' → s.a l i < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨hτ.1, hτ.2.trans_le hle⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun τ hτ j hj1 hj2 => ?_⟩
    have hjm : j % k ∈ T :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hj1 (by rw [Nat.mod_eq_of_lt (Nat.mod_lt j hk0)] at hc; exact hc),
          fun hc => hj2 (by rw [Nat.mod_eq_of_lt (Nat.mod_lt j hk0)] at hc; exact hc)⟩
    rw [hempty] at hjm
    simp at hjm
  · obtain ⟨e0, he0, hall⟩ := minWitness_p34 hmono hne
      (fun i hi => hparent i (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2)
    refine ⟨e0, he0, fun τ hτ j hj1 hj2 => ?_⟩
    have haj : s.a l j = s.a l (j % k) := modFold_p34 hk0 hper_a j
    have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w j) =
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (j % k)) :=
      congrArg _ (modFold_p34 hk0 hper_w j)
    rw [haj, hwj]
    exact hall (j % k)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hj1 (by rw [Nat.mod_eq_of_lt (Nat.mod_lt j hk0)] at hc; exact hc),
          fun hc => hj2 (by rw [Nat.mod_eq_of_lt (Nat.mod_lt j hk0)] at hc; exact hc)⟩)
      τ hτ

/-- HOL `EXISTS_SMALL_LT_CONST` (IMJXPHR.hl:650). -/
theorem EXISTS_SMALL_LT_CONST_p34 (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hclt : dist v2 w < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w < c := by
  have hclt' : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - 0)) w < c := by
    rwa [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha]
  obtain ⟨e1, he1, hmem⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      ((deforV1_dist_cont_p34 a v1 v2 w x1 x2 x6 h1 h2 h6 hnc hx1 hx2 hx6 ha).preimage_mem_nhds
        (Iio_mem_nhds hclt'))
  refine ⟨e1, he1, fun t ht => ?_⟩
  have hb : t ∈ Metric.ball 0 e1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht.1]
    exact ht.2
  exact Set.mem_Iio.mp (hmem t hb)

/-- HOL `EXISTS_SMALL_LT_CONST_V1` (IMJXPHR.hl:677). -/
theorem EXISTS_SMALL_LT_CONST_V1_p34 (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hclt : dist v2 w < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w < c := by
  have hclt' : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - 0)) w < c := by
    rwa [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha]
  obtain ⟨e1, he1, hmem⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      ((deforV1_dist_cont_p34 a v1 v2 w x1 x2 x6 h1 h2 h6 hnc hx1 hx2 hx6 ha).preimage_mem_nhds
        (Iio_mem_nhds hclt'))
  refine ⟨e1, he1, fun t ht => ?_⟩
  have hb : t ∈ Metric.ball 0 e1 := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact abs_lt.mpr ht
  exact Set.mem_Iio.mp (hmem t hb)

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_SUC` (IMJXPHR.hl:703). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hkk : s.k = k) (hk : 3 < k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, scsDiag k l i →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < s.b l i := by
  sorry

/-- HOL `xrr_decreasing_lt` (IMJXPHR.hl:758). -/
theorem xrr_decreasing_lt_p34 (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
    (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2h : y2 ≤ 2 * h0) (hlt : y1 < y1') :
    xrr y1' y2 y6 < xrr y1 y2 y6 := by
  sorry

/-- HOL `exp_aff_gt_by_dot` (IMJXPHR.hl:801). -/
theorem exp_aff_gt_by_dot_p34 (x v u : V3) (hnc : ¬Collinear ℝ {x, v, u}) :
    affGt {x, v} {u} = {w : V3 | (w - x) ⬝ᵥ e2Fan_p34 x v u = 0 ∧ 0 < (w - x) ⬝ᵥ e1Fan_p34 x v u} := by
  sorry

/-- HOL `CROSS_LAGRANGE1` (IMJXPHR.hl:804; restated verbatim at :876). -/
theorem CROSS_LAGRANGE1_p34 (x y z : V3) :
    cross3 (cross3 x y) z = (x ⬝ᵥ z) • y - (y ⬝ᵥ z) • x := by
  rw [cross3, cross3, cross_cross_eq_smul_sub_smul]
  simp

/-- HOL `exp_aff_by_dot` (IMJXPHR.hl:872). -/
theorem exp_aff_by_dot_p34 (x v u : V3) (hnc : ¬Collinear ℝ {x, v, u}) :
    affineSpan ℝ ({x, v, u} : Set V3) = {w : V3 | (w - x) ⬝ᵥ e2Fan_p34 x v u = 0} := by
  sorry

/-- HOL `IN_AFF_EQ_DOT_E2_FAN` (IMJXPHR.hl:940). -/
theorem IN_AFF_EQ_DOT_E2_FAN_p34 (x y z : V3) (hnc : ¬Collinear ℝ ({0, x, y} : Set V3)) :
    e2Fan_p34 0 x y ⬝ᵥ z = 0 ↔ z ∈ affineSpan ℝ ({0, x, y} : Set V3) := by
  sorry

/-- HOL `OPEN_RELA_AFF_GT` (IMJXPHR.hl:951). -/
theorem OPEN_RELA_AFF_GT_p34 (z x y : V3)
    (h1 : ¬Collinear ℝ ({0, z, x} : Set V3))
    (h2 : ¬Collinear ℝ ({0, x, y} : Set V3))
    (hz : z ∈ affGt {0} {x, y}) :
    ∃ e : ℝ, 0 < e ∧ Metric.ball z e ∩ affineSpan ℝ ({0, x, z} : Set V3) ⊆ affGt {0} {x, y} := by
  sorry

/-- HOL `V3_DEFOR_IN_AFF_GT` (IMJXPHR.hl:1026). -/
theorem V3_DEFOR_IN_AFF_GT_p34 (v1 v2 w : V3) (x1 x2 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hnc2 : ¬Collinear ℝ ({0, v1, w} : Set V3))
    (hv2 : v2 ∈ affGt {0} {v1, w}) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ∈ affGt {0} {v1, w} := by
  sorry

/-- HOL `V3_DEFOR_IN_AFF_GT_V1` (IMJXPHR.hl:1075). -/
theorem V3_DEFOR_IN_AFF_GT_V1_p34 (v1 v2 w : V3) (x1 x2 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hnc2 : ¬Collinear ℝ ({0, v1, w} : Set V3))
    (hv2 : v2 ∈ affGt {0} {v1, w}) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ∈ affGt {0} {v1, w} := by
  sorry

/-- HOL `xrr_increasing_le` (IMJXPHR.hl:1130). -/
theorem xrr_increasing_le_p34 (y1 y2 y6 y6' : ℝ) (h1 : 0 < y1) (h2 : 0 < y2)
    (h6 : 0 ≤ y6) (h6' : y6 ≤ y6') :
    xrr y1 y2 y6 ≤ xrr y1 y2 y6' := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_2` (IMJXPHR.hl:1143). -/
theorem DEFORMATION_DIST_LE_2_p34 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l i < dist v2 (w i))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hmod : l % k = (i + 1) % k) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      2 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_EDGE` (IMJXPHR.hl:1190). -/
theorem DEFORMATION_V3_DEFOR_EDGE_p34 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l i < dist v2 (w i))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hmod : l % k = (i + 1) % k) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < dist v2 (w i) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM` (IMJXPHR.hl:1598; the first
`let` of the shadowed pair — the per-index `?e. !t.` form). -/
theorem DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l (l + k - 1) < dist v2 (w (l + k - 1)))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, ¬(i % k = l % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM` (IMJXPHR.hl:1696; the
surviving second `let` of the shadowed pair — the skolemised
`?e. !t i.` form, named `_b`). -/
theorem DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_b_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l (l + k - 1) < dist v2 (w (l + k - 1)))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_p34 s k l w v1 v2 x1 x2 x6 a hk hkk
    hs hmw haz hnc haff hl hl1 hn ha_lt hx1 hx2 hx6 ha hdiag
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  have hper_b : ∀ i, s.b l (i + k) = s.b l i := by
    intro i
    rw [← hkk]
    exact ((hs.2.2.2.2.2.2.2.2.2.2.1) l i).2
  set T : Finset ℕ := (Finset.range k).filter (fun i => i % k ≠ l % k) with hT
  have hmono : ∀ (i : ℕ) (e : ℝ),
      (∀ τ : ℝ, 0 < τ ∧ τ < e → dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) ≤ s.b l i) →
      ∀ e' : ℝ, 0 < e' → e' ≤ e →
      ∀ τ : ℝ, 0 < τ ∧ τ < e' → dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) ≤ s.b l i := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨hτ.1, hτ.2.trans_le hle⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun τ hτ i hi => ?_⟩
    have hjm : i % k ∈ T :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hi (by rw [Nat.mod_eq_of_lt (Nat.mod_lt i hk0)] at hc; exact hc)⟩
    rw [hempty] at hjm
    simp at hjm
  · obtain ⟨e0, he0, hall⟩ := minWitness_p34 hmono hne
      (fun i hi => hparent i (Finset.mem_filter.mp hi).2)
    refine ⟨e0, he0, fun τ hτ i hi => ?_⟩
    have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) =
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (i % k)) :=
      congrArg _ (modFold_p34 hk0 hper_w i)
    have hbj : s.b l i = s.b l (i % k) := modFold_p34 hk0 hper_b i
    rw [hwj, hbj]
    exact hall (i % k)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hi (by rw [Nat.mod_eq_of_lt (Nat.mod_lt i hk0)] at hc; exact hc)⟩)
      τ hτ

/-- HOL `DEFORMATION_SMALL_INTERVAL` (IMJXPHR.hl:1821). -/
theorem DEFORMATION_SMALL_INTERVAL_p34 {f : V3 → ℝ → V3} {V : Set V3} {a b c d : ℝ}
    (h : Deformation f V a b) (hac : a ≤ c) (hc : c < 0) (hd : 0 < d) (hdb : d ≤ b) :
    Deformation f V c d := by
  obtain ⟨h0, hcont, hfix⟩ := h
  refine ⟨⟨le_of_lt hc, le_of_lt hd⟩, ?_, hfix⟩
  intro v hv r hr
  exact hcont v hv r ⟨le_trans hac hr.1, le_trans hr.2 hdb⟩

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V` (IMJXPHR.hl:1837). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_V1` (IMJXPHR.hl:1911). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∀ i : ℕ, ¬(i % k = l % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
        0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM` (IMJXPHR.hl:1946).  Sits on the
per-index parent via the finite-minimum argument plus `MMs` periodicity. -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ,
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_V3_DEFOR_NOT_IN_V_p34 s k l w v1 v2 x1 x2 x6 a hk hkk hs hmw
    hl hl1 hx1 hx2 hx6 ha
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  obtain ⟨e0, he0, hall⟩ := minWitness_p34
    (R := fun i e => ∀ τ : ℝ, 0 < τ ∧ τ < e →
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i))
    (fun i e hR e' he' hle τ hτ => hR τ ⟨hτ.1, hτ.2.trans_le hle⟩)
    ⟨0, Finset.mem_range.mpr hk0⟩ (fun i _ => hparent i)
  refine ⟨e0, he0, fun τ hτ i => ?_⟩
  have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) =
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (i % k)) :=
    congrArg (fun x => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) x)
      (modFold_p34 hk0 hper_w i)
  rw [hwj]
  exact hall (i % k) (Finset.mem_range.mpr (Nat.mod_lt _ hk0)) τ hτ

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1` (IMJXPHR.hl:2020). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_V3_DEFOR_NOT_IN_V_V1_p34 s k l w v1 v2 x1 x2 x6 a hk hkk hs hmw
    hl hl1 hx1 hx2 hx6 ha
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  set T : Finset ℕ := (Finset.range k).filter (fun i => i % k ≠ l % k) with hT
  have hmem : ∀ i : ℕ, ¬(i % k = l % k) → i % k ∈ T := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0), ?_⟩
    rw [Nat.mod_eq_of_lt (Nat.mod_lt i hk0)]
    exact hi
  have hmono : ∀ (i : ℕ) (e : ℝ),
      (∀ τ : ℝ, -e < τ ∧ τ < e → 0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i)) →
      ∀ e' : ℝ, 0 < e' → e' ≤ e →
      ∀ τ : ℝ, -e' < τ ∧ τ < e' → 0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨lt_of_le_of_lt (neg_le_neg hle) hτ.1, hτ.2.trans_le hle⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun τ hτ i hi => ?_⟩
    exact absurd (hmem i hi) (by rw [hempty]; simp)
  · obtain ⟨e0, he0, hall⟩ := minWitness_p34 hmono hne
      (fun i hi => hparent i (Finset.mem_filter.mp hi).2)
    refine ⟨e0, he0, fun τ hτ i hi => ?_⟩
    have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) =
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (i % k)) :=
      congrArg (fun x => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) x)
        (modFold_p34 hk0 hper_w i)
    rw [hwj]
    exact hall (i % k) (hmem i hi) τ hτ

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ` (IMJXPHR.hl:2115). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ,
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := by
  obtain ⟨e, he, hall⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_p34 s k l w v1 v2 x1 x2 x6 a
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 ha
  refine ⟨e, he, fun t i ht hcon => ?_⟩
  have hpos := hall t i ht
  rw [hcon, dist_self] at hpos
  exact lt_irrefl (0 : ℝ) hpos

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1` (IMJXPHR.hl:2136). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := by
  obtain ⟨e, he, hall⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_p34 s k l w v1 v2 x1 x2 x6 a
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 ha
  refine ⟨e, he, fun t i ht hi hcon => ?_⟩
  have hpos := hall t i ht hi
  rw [hcon, dist_self] at hpos
  exact lt_irrefl (0 : ℝ) hpos

/-! ### FF-relabel kit (filled 2026-09: the `V3_DEFOR_EQ_IN_FF_*` tower).

The pointwise relabel `r(p,q) = (g p, g q)`, `g z = if z = v2 then f else z`,
is injective on the `w`-edge set once `f` is off the `w`-range; membership in
`relabelFF f v2 FF` collapses to the four-case master below, and every
`V3_DEFOR_EQ_IN_FF_*` goal is an instance with concrete in/out-neighbour
bookkeeping (scs-residue arithmetic). -/

/-- Residue successor injectivity modulo `k > 1`. -/
private theorem res_succ_inj_p34 {k i j : ℕ} (hk : 1 < k) (h : (i + 1) % k = (j + 1) % k) :
    i % k = j % k := by
  have hk0 : 0 < k := by omega
  have hi : i % k < k := Nat.mod_lt _ hk0
  have hj : j % k < k := Nat.mod_lt _ hk0
  have h1 : (i + 1) % k = (i % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  have h2 : (j + 1) % k = (j % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  rw [h1, h2] at h
  rcases lt_or_ge (i % k + 1) k with ha | hb
  · rw [Nat.mod_eq_of_lt ha] at h
    rcases lt_or_ge (j % k + 1) k with hc | hd
    · rw [Nat.mod_eq_of_lt hc] at h; omega
    · have hz : j % k + 1 = k := by omega
      rw [hz, Nat.mod_self] at h; omega
  · have hbi : i % k + 1 = k := by omega
    rw [hbi, Nat.mod_self] at h
    rcases lt_or_ge (j % k + 1) k with hc | hd
    · rw [Nat.mod_eq_of_lt hc] at h; omega
    · have hz : j % k + 1 = k := by omega
      rw [hz, Nat.mod_self] at h; omega

/-- Residue successor congruence. -/
private theorem res_succ_congr_p34 {k i j : ℕ} (hk : 1 < k) (h : i % k = j % k) :
    (i + 1) % k = (j + 1) % k := by
  have hk0 : 0 < k := by omega
  have hi : i % k < k := Nat.mod_lt _ hk0
  have hj : j % k < k := Nat.mod_lt _ hk0
  have e1 : (i + 1) % k = (i % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  have e2 : (j + 1) % k = (j % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  rw [e1, e2, h]

/-- The predecessor residue: `(i+1) ≡ j` gives `i ≡ j-1` (rendered `j+k-1`). -/
private theorem res_succ_shift_p34 {k i j : ℕ} (hk : 1 < k) (h : (i + 1) % k = j % k) :
    i % k = (j + k - 1) % k := by
  refine res_succ_inj_p34 hk ?_
  have hje : ((j + k - 1) + 1) % k = j % k := by
    have h2 : (j + k - 1) + 1 = j + k := by omega
    rw [h2, Nat.add_mod_right]
  rwa [hje]

/-- Consecutive residues differ for `k ≥ 2`. -/
private theorem mod_ne_succ_p34 {k l : ℕ} (hk : 2 ≤ k) : l % k ≠ (l + 1) % k := by
  intro hcon
  have hk0 : 0 < k := by omega
  have hm : l % k < k := Nat.mod_lt _ hk0
  have h2 : (l + 1) % k = (l % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  rw [h2] at hcon
  rcases lt_or_ge (l % k + 1) k with ha | hb
  · rw [Nat.mod_eq_of_lt ha] at hcon; omega
  · have hz : l % k + 1 = k := by omega
    rw [hz, Nat.mod_self] at hcon; omega

/-- `l+1` and `l+k-1` are different residues for `4 ≤ k`. -/
private theorem mod_ne_shift_p34 {k l : ℕ} (hk : 4 ≤ k) : (l + 1) % k ≠ (l + k - 1) % k := by
  intro hcon
  have hk0 : 0 < k := by omega
  have hp : l % k < k := Nat.mod_lt _ hk0
  have hr : (l + k - 1) % k < k := Nat.mod_lt _ hk0
  have h1 : ((l + k - 1) + 1) % k = l % k := by
    have h2 : (l + k - 1) + 1 = l + k := by omega
    rw [h2, Nat.add_mod_right]
  have h3 : (l + 1) % k = (l % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  have h4 : ((l + k - 1) % k + 1) % k = l % k := by
    have h1' : ((l + k - 1) % k + 1) % k = ((l + k - 1) + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq (l + k - 1) k)
    rw [h1', h1]
  rw [hcon] at h3
  rcases lt_or_ge ((l + k - 1) % k + 1) k with ha | hb
  · rw [Nat.mod_eq_of_lt ha] at h4
    rcases lt_or_ge (l % k + 1) k with hc | hd
    · rw [Nat.mod_eq_of_lt hc] at h3; omega
    · have hz : l % k + 1 = k := by omega
      rw [hz, Nat.mod_self] at h3; omega
  · have hz : (l + k - 1) % k + 1 = k := by omega
    rw [hz, Nat.mod_self] at h4
    rcases lt_or_ge (l % k + 1) k with hc | hd
    · rw [Nat.mod_eq_of_lt hc] at h3; omega
    · have hz2 : l % k + 1 = k := by omega
      rw [hz2, Nat.mod_self] at h3; omega

/-- `MMs` realisations are `BBs`. -/
private theorem mms_bbs_p34 {s : ScsV39} {w : ℕ → V3} (hmw : w ∈ MMsV39 s) : BBsV39 s w := by
  have h := hmw
  simp only [MMsV39, Set.mem_setOf_eq] at h
  have h2 := h.1
  simp only [BBprime2V39, Set.mem_setOf_eq] at h2
  have h3 := h2.1
  simp only [BBprimeV39, Set.mem_setOf_eq] at h3
  exact h3.1

/-- Distinct residues give distinct vertices on an `MMs` realisation. -/
private theorem w_inj_p34 {s : ScsV39} {k : ℕ} {w : ℕ → V3} (hk : 3 < k) (hkk : s.k = k)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) : ∀ i j : ℕ, i % k ≠ j % k → w i ≠ w j := by
  have hk0 : 0 < k := by omega
  have hBB := mms_bbs_p34 hmw
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  intro i j hij hcon
  have hik : i % k < k := Nat.mod_lt _ hk0
  have hjk : j % k < k := Nat.mod_lt _ hk0
  have h2le : 2 ≤ s.a (i % k) (j % k) :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % k) (j % k)
      ⟨by rw [hkk]; exact Nat.mod_lt _ hk0, by rw [hkk]; exact Nat.mod_lt _ hk0,
        fun hc => hij hc⟩
  have hperW : ∀ q, w (q + k) = w q := MMs_periodic_p34 s k w hkk hmw
  have hw1 : w i = w (i % k) := modFold_p34 hk0 hperW i
  have hw2 : w j = w (j % k) := modFold_p34 hk0 hperW j
  have e1 : s.a i j = s.a (i % k) j :=
    modFold_p34 (f := fun q => s.a q j) hk0 (fun q => (hpa q j).1) i
  have e2 : s.a (i % k) j = s.a (i % k) (j % k) :=
    modFold_p34 (f := fun q => s.a (i % k) q) hk0 (fun q => (hpa (i % k) q).2) j
  have hle : s.a (i % k) (j % k) ≤ dist (w i) (w j) := by
    rw [hw1, hw2]
    exact (hBB.2.2.1 (i % k) (j % k)).1
  rw [hcon, dist_self] at hle
  exact absurd hle (by linarith)

/-- Edge membership is witnessed by an index. -/
private theorem ff_edge_index_p34 {w : ℕ → V3} {FF : Set (V3 × V3)}
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    {a b : V3} (hmem : (a, b) ∈ FF) :
    ∃ i : ℕ, w i = a ∧ w (i + 1) = b := by
  have h := hmem
  rw [← hFF] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa using hi⟩

/-- Linear independence of `{v1, v2}` off the collinearity. -/
private theorem lindep_p34 {v1 v2 : V3} (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    {α β : ℝ} (h : α • v1 + β • v2 = 0) : α = 0 ∧ β = 0 := by
  obtain ⟨hn1, hn2⟩ := nc_norm_pos_p34 hnc
  by_cases hb : β = 0
  · rw [hb, zero_smul, add_zero] at h
    exact ⟨smul_eq_zero.mp h |>.resolve_right (norm_pos_iff.mp hn1), hb⟩
  · have h2 : β • v2 = -(α • v1) := by
      linear_combination (norm := module) h
    have h3 : v2 = (β⁻¹ * (-α)) • v1 := by
      rw [← smul_smul, eq_inv_smul_iff₀ hb, neg_smul]
      exact h2
    exact absurd h3 (nc_not_smul_p34 hnc _)

/-- The deformed point never coincides with `v2` (any `t ≠ 0`). -/
private theorem deforV1_ne_self_p34 (a : ℝ) (v1 v2 : V3) (x1 x2 x6 t : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (ht : t ≠ 0) :
    v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 := by
  obtain ⟨h1, h2⟩ := nc_norm_pos_p34 hnc
  have hx1n : (0 : ℝ) < x1 := by rw [← hx1]; exact pow_pos h1 2
  have hd1 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have hexp : (x1 + x2 - x6) / 2 = v1 ⬝ᵥ v2 := by
    have hnn : inner ℝ (v1 - v2) (v1 - v2) = ‖v1 - v2‖ ^ 2 :=
      real_inner_self_eq_norm_sq (v1 - v2)
    have hdc : v2 ⬝ᵥ v1 = v1 ⬝ᵥ v2 := dotProduct_comm _ _
    have key : x6 = x1 + x2 - 2 * (v1 ⬝ᵥ v2) := by
      rw [← hx6, ← hnn]
      simp only [inner_sub_right, inner_sub_left]
      rw [inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot, hd1, (norm_sq_eq_dot v2).symm.trans hx2, hdc]
      ring
    rw [key]
    ring
  have hcross : cross3 v1 (cross3 v1 v2) = (v1 ⬝ᵥ v2) • v1 - x1 • v2 := by
    rw [cross3, cross3, cross_cross_eq_smul_sub_smul', hd1]
    simp
  intro hcon
  set c2 : ℝ := (-1 / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6) with hc2def
  simp only [v3DeforV1_p17, ha] at hcon
  rw [← hc2def] at hcon
  rw [hcross, smul_sub, smul_smul, smul_smul] at hcon
  -- hcon : c1 • v1 + ((c2 * d) • v1 - (c2 * x1) • v2) = v2
  have hz : ((x1 + (x2 - t) - x6) / (2 * x1) + c2 * (v1 ⬝ᵥ v2)) • v1 +
      (-(c2 * x1) - 1) • v2 = 0 := by
    linear_combination (norm := module) hcon
  obtain ⟨hA, hB⟩ := lindep_p34 hnc hz
  have hB' : c2 * x1 = -1 := by linarith
  have hC : c2 = -1 / x1 := by
    apply mul_right_cancel₀ hx1n.ne'
    rw [hB', neg_div]
    field_simp
  rw [hC] at hA
  rw [← hexp] at hA
  field_simp at hA
  apply ht
  linarith

/-- Master membership characterization of the pointwise relabel. -/
private theorem relabelFF_master_p34 {f v2 : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (x y : V3) :
    (x, y) ∈ relabelFF_p34 f v2 FF ↔
      ((x, y) ∈ FF ∧ x ≠ v2 ∧ y ≠ v2) ∨ (x = f ∧ (v2, y) ∈ FF ∧ y ≠ v2) ∨
        ((x, v2) ∈ FF ∧ y = f ∧ x ≠ v2) ∨ (x = f ∧ y = f ∧ (v2, v2) ∈ FF) := by
  unfold relabelFF_p34
  constructor
  · rintro ⟨d, hd, hde⟩
    rw [Prod.mk.injEq] at hde
    obtain ⟨hde1, hde2⟩ := hde
    by_cases h1 : d.1 = v2
    · by_cases h2 : d.2 = v2
      · rw [if_pos h1] at hde1
        rw [if_pos h2] at hde2
        have hdd : (d.1, d.2) ∈ FF := hd
        rw [h1, h2] at hdd
        exact Or.inr (Or.inr (Or.inr ⟨hde1.symm, hde2.symm, hdd⟩))
      · rw [if_pos h1] at hde1
        rw [if_neg h2] at hde2
        have hd' : (d.1, d.2) ∈ FF := hd
        rw [h1, hde2] at hd'
        exact Or.inr (Or.inl ⟨hde1.symm, hd', fun hyy => h2 (hde2.trans hyy)⟩)
    · by_cases h2 : d.2 = v2
      · rw [if_neg h1] at hde1
        rw [if_pos h2] at hde2
        have hd' : (d.1, d.2) ∈ FF := hd
        rw [hde1, h2] at hd'
        exact Or.inr (Or.inr (Or.inl ⟨hd', hde2.symm, fun hxx => h1 (hde1.trans hxx)⟩))
      · rw [if_neg h1] at hde1
        rw [if_neg h2] at hde2
        have hd' : (d.1, d.2) ∈ FF := hd
        rw [hde1, hde2] at hd'
        exact Or.inl ⟨hd', fun hxx => h1 (hde1.trans hxx),
          fun hyy => h2 (hde2.trans hyy)⟩
  · rintro (⟨hmem, hxv, hyv⟩ | ⟨hxf, hmem, hyv⟩ | ⟨hmem, hyf, hxv⟩ | ⟨hxf, hyf, hmem⟩)
    · refine ⟨(x, y), hmem, ?_⟩
      simp only [if_neg hxv, if_neg hyv, reduceIte]
    · refine ⟨(v2, y), hmem, ?_⟩
      rw [hxf]
      simp only [if_neg hyv, reduceIte]
    · refine ⟨(x, v2), hmem, ?_⟩
      rw [hyf]
      simp only [if_neg hxv, reduceIte]
    · refine ⟨(v2, v2), hmem, ?_⟩
      simp only [if_pos rfl, reduceIte]
      rw [hxf, hyf]

/-- Abstract shape `f`-column: the relabel moves the in-edge of `y` from
`v2` to `f`. -/
private theorem relabelFF_shapeA_p34 {f v2 : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (hK3 : (v2, v2) ∉ FF) (hfn1 : ∀ z, (f, z) ∉ FF)
    (y : V3) : (f, y) ∈ relabelFF_p34 f v2 FF ↔ (v2, y) ∈ FF := by
  rw [relabelFF_master_p34 hfv]
  constructor
  · rintro (⟨hF, hx, hy⟩ | ⟨hx, hF, hy⟩ | ⟨hF, hy, hx⟩ | ⟨hx, hy, hF⟩)
    · exact absurd hF (hfn1 y)
    · exact hF
    · exact absurd hF (hfn1 v2)
    · exact absurd hF hK3
  · intro h
    exact Or.inr (Or.inl ⟨rfl, h, fun hyy => hK3 (by rw [hyy] at h; exact h)⟩)

/-- Abstract shape `f`-row. -/
private theorem relabelFF_shapeB_p34 {f v2 : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (hK3 : (v2, v2) ∉ FF) (hfn2 : ∀ z, (z, f) ∉ FF)
    (x : V3) : (x, f) ∈ relabelFF_p34 f v2 FF ↔ (x, v2) ∈ FF := by
  rw [relabelFF_master_p34 hfv]
  constructor
  · rintro (⟨hF, hx, hy⟩ | ⟨hx, hF, hy⟩ | ⟨hF, hy, hx⟩ | ⟨hx, hy, hF⟩)
    · exact absurd hF (hfn2 x)
    · exact absurd hF (hfn2 v2)
    · exact hF
    · exact absurd hF hK3
  · intro h
    have hxv : x ≠ v2 := fun hxv => hK3 (by rw [hxv] at h; exact h)
    exact Or.inr (Or.inr (Or.inl ⟨h, rfl, hxv⟩))

/-- Abstract shape: a column away from `f`/`v2` is untouched. -/
private theorem relabelFF_shapeC_p34 {f v2 a : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (haf : a ≠ f) (hav : a ≠ v2) (hnav : (a, v2) ∉ FF)
    (y : V3) : (a, y) ∈ relabelFF_p34 f v2 FF ↔ (a, y) ∈ FF := by
  rw [relabelFF_master_p34 hfv]
  constructor
  · rintro (⟨hF, hx, hy⟩ | ⟨hx, hF, hy⟩ | ⟨hF, hy, hx⟩ | ⟨hx, hy, hF⟩)
    · exact hF
    · exact absurd hx haf
    · exact absurd hF hnav
    · exact absurd hx haf
  · intro h
    exact Or.inl ⟨h, hav, fun hyc => hnav (by rw [hyc] at h; exact h)⟩

/-- Abstract shape: a row away from `f`/`v2` is untouched. -/
private theorem relabelFF_shapeD_p34 {f v2 b : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (hK3 : (v2, v2) ∉ FF) (hbf : b ≠ f) (hbv : b ≠ v2) (hnbv : (v2, b) ∉ FF)
    (x : V3) : (x, b) ∈ relabelFF_p34 f v2 FF ↔ (x, b) ∈ FF := by
  rw [relabelFF_master_p34 hfv]
  constructor
  · rintro (⟨hF, hx, hy⟩ | ⟨hx, hF, hy⟩ | ⟨hF, hy, hx⟩ | ⟨hx, hy, hF⟩)
    · exact hF
    · exact absurd hF hnbv
    · exact absurd hy hbf
    · exact absurd hF hK3
  · intro h
    exact Or.inl ⟨h, fun hxc => hnbv (by rw [hxc] at h; exact h), hbv⟩

/-- Abstract shape: the relabelled in-edge set at `c` is `{f}`. -/
private theorem relabelFF_shapeS_p34 {f v2 c : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (hcf : c ≠ f) (hcv : c ≠ v2) (hvc : (v2, c) ∈ FF)
    (hinc : ∀ z, (z, c) ∈ FF → z = v2)
    (z : V3) : (z, c) ∈ relabelFF_p34 f v2 FF ↔ z = f := by
  rw [relabelFF_master_p34 hfv]
  constructor
  · rintro (⟨hF, hx, hy⟩ | ⟨hx, hF, hy⟩ | ⟨hF, hy, hx⟩ | ⟨hx, hy, hF⟩)
    · exact absurd (hinc z hF) hx
    · exact hx
    · exact absurd hy hcf
    · exact absurd hy hcf
  · intro h
    exact Or.inr (Or.inl ⟨h, hvc, hcv⟩)

/-- Abstract shape: the relabelled out-edge set at `b` is `{f}`. -/
private theorem relabelFF_shapeS2_p34 {f v2 b : V3} {FF : Set (V3 × V3)} (hfv : f ≠ v2)
    (hbf : b ≠ f) (hbv : b ≠ v2) (hbv2 : (b, v2) ∈ FF)
    (hout : ∀ z, (b, z) ∈ FF → z = v2)
    (z : V3) : (b, z) ∈ relabelFF_p34 f v2 FF ↔ z = f := by
  rw [relabelFF_master_p34 hfv]
  constructor
  · rintro (⟨hF, hx, hy⟩ | ⟨hx, hF, hy⟩ | ⟨hF, hy, hx⟩ | ⟨hx, hy, hF⟩)
    · exact absurd (hout z hF) hy
    · exact absurd hx hbf
    · exact hy
    · exact absurd hx hbf
  · intro h
    exact Or.inr (Or.inr (Or.inl ⟨hbv2, h, hbv⟩))

/-- All the edge bookkeeping the `V3_DEFOR_EQ_IN_FF_*` instances need, for a
deformed point `f` off the `w`-range (index facts via scs residues). -/
private theorem ff_ctx_p34 {s : ScsV39} {k l : ℕ} {w : ℕ → V3} {v2 f : V3}
    {FF : Set (V3 × V3)}
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hf : ∀ i : ℕ, f ≠ w i)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (v2, v2) ∉ FF ∧
      (∀ z, (f, z) ∉ FF) ∧
      (∀ z, (z, f) ∉ FF) ∧
      v2 ≠ w (l + 1) ∧
      (∀ z, (z, v2) ∈ FF → z = w (l + k - 1)) ∧
      (∀ z, (v2, z) ∈ FF → z = w (l + 1)) ∧
      (∀ z, (z, w (l + 1)) ∈ FF → z = v2) ∧
      (w (l + 1), v2) ∉ FF ∧
      (v2, w (l + k - 1)) ∉ FF ∧
      (∀ z, (w (l + k - 1), z) ∈ FF → z = v2) ∧
      (v2, w (l + 1)) ∈ FF ∧
      (w (l + k - 1), v2) ∈ FF ∧
      w (l + k - 1) ≠ v2 := by
  have hk0 : 0 < k := by omega
  have hk4 : 4 ≤ k := by omega
  have hinj := w_inj_p34 hk hkk hs hmw
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have heq : ∀ i j : ℕ, i % k = j % k → w i = w j := fun i j h =>
    by rw [modFold_p34 hk0 hper i, modFold_p34 hk0 hper j, h]
  have hmem : ∀ a b : V3, (a, b) ∈ FF → ∃ i : ℕ, w i = a ∧ w (i + 1) = b :=
    fun a b => ff_edge_index_p34 hFF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    obtain ⟨i, hi1, hi2⟩ := hmem v2 v2 hc
    exact hinj i (i + 1) (mod_ne_succ_p34 (by omega)) (hi1.trans hi2.symm)
  · intro z hc
    obtain ⟨i, hi1, -⟩ := hmem f z hc
    exact hf i hi1.symm
  · intro z hc
    obtain ⟨i, -, hi2⟩ := hmem z f hc
    exact hf (i + 1) hi2.symm
  · intro hc
    exact hinj l (l + 1) (mod_ne_succ_p34 (by omega)) (by rwa [hl])
  · intro z hc
    obtain ⟨i, hi1, hi2⟩ := hmem z v2 hc
    have hres : (i + 1) % k = l % k := by
      by_contra hne
      exact hinj (i + 1) l hne (hi2.trans hl.symm)
    rw [← hi1, modFold_p34 hk0 hper i, res_succ_shift_p34 (by omega) hres,
      ← modFold_p34 hk0 hper (l + k - 1)]
  · intro z hc
    obtain ⟨i, hi1, hi2⟩ := hmem v2 z hc
    have hres : i % k = l % k := by
      by_contra hne
      exact hinj i l hne (hi1.trans hl.symm)
    rw [← hi2, modFold_p34 hk0 hper (i + 1),
      res_succ_congr_p34 (by omega) hres, ← modFold_p34 hk0 hper (l + 1)]
  · intro z hc
    obtain ⟨i, hi1, hi2⟩ := hmem z (w (l + 1)) hc
    have hres : (i + 1) % k = (l + 1) % k := by
      by_contra hne
      exact hinj (i + 1) (l + 1) hne hi2
    rw [← hi1, modFold_p34 hk0 hper i, res_succ_inj_p34 (by omega) hres,
      ← modFold_p34 hk0 hper l, hl]
  · intro hc
    obtain ⟨i, hi1, hi2⟩ := hmem (w (l + 1)) v2 hc
    have ha : i % k = (l + 1) % k := by
      by_contra hne
      exact hinj i (l + 1) hne hi1
    have hb : i % k = (l + k - 1) % k := res_succ_shift_p34 (by omega) (by
      by_contra hne
      exact hinj (i + 1) l hne (hi2.trans hl.symm))
    exact mod_ne_shift_p34 hk4 (ha.symm.trans hb)
  · intro hc
    obtain ⟨i, hi1, hi2⟩ := hmem v2 (w (l + k - 1)) hc
    have ha : i % k = l % k := by
      by_contra hne
      exact hinj i l hne (hi1.trans hl.symm)
    have hb : (i + 1) % k = (l + 1) % k := res_succ_congr_p34 (by omega) ha
    have hc2 : (i + 1) % k = (l + k - 1) % k := by
      by_contra hne
      exact hinj (i + 1) (l + k - 1) hne hi2
    exact mod_ne_shift_p34 hk4 (hb.symm.trans hc2)
  · intro z hc
    obtain ⟨i, hi1, hi2⟩ := hmem (w (l + k - 1)) z hc
    have hres : i % k = (l + k - 1) % k := by
      by_contra hne
      exact hinj i (l + k - 1) hne hi1
    have hstep : (i + 1) % k = l % k := by
      have h1 : (i + 1) % k = ((l + k - 1) + 1) % k := res_succ_congr_p34 (by omega) hres
      rwa [show (l + k - 1) + 1 = l + k by omega, Nat.add_mod_right] at h1
    rw [← hi2, modFold_p34 hk0 hper (i + 1), hstep, ← modFold_p34 hk0 hper l, hl]
  · have h : (w l, w (l + 1)) ∈ Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l, rfl⟩
    rw [hFF] at h
    rwa [hl] at h
  · have h : (w (l + k - 1), w ((l + k - 1) + 1)) ∈
      Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l + k - 1, rfl⟩
    rw [hFF] at h
    rw [show (l + k - 1) + 1 = l + k by omega, hper l, hl] at h
    exact h
  · intro hc
    refine hinj (l + k - 1) l ?_ ?_
    · intro hres
      have h1 : ((l + k - 1) + 1) % k = l % k := by
        have h2 : (l + k - 1) + 1 = l + k := by omega
        rw [h2, Nat.add_mod_right]
      have h2' : ((l + k - 1) + 1) % k = (l + 1) % k := res_succ_congr_p34 (by omega) hres
      rw [h1] at h2'
      exact Ne.symm (mod_ne_succ_p34 (by omega)) h2'.symm
    · rwa [hl]

/-- The `f`-facts for the one-sided (`0 < t`) lane: `f` differs from every
`w`-vertex, in particular from `v2`. -/
private theorem hf_plain_p34 {v1 v2 : V3} {x1 x2 x6 a e t : ℝ} {w : ℕ → V3}
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (ht : 0 < t) (hte : t < e) (hl : w l = v2) :
    v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 ∧
      ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := by
  refine ⟨fun hc => hne t l ⟨ht, hte⟩ (hc.trans hl.symm), fun i => hne t i ⟨ht, hte⟩⟩

/-- The `f`-facts for the two-sided (`-e < t`) lane: either `t = 0` (the
deformation is the identity at `t = 0`) or `f` differs from every
`w`-vertex. -/
private theorem hf_mod_p34 {a : ℝ} {v1 v2 : V3} {x1 x2 x6 e t : ℝ} {w : ℕ → V3} {k l : ℕ}
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hk0 : 0 < k) (hper : ∀ i, w (i + k) = w i)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (ht : -e < t ∧ t < e) (hl : w l = v2) :
    (t = 0 ∨ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2) ∧
      (t ≠ 0 → ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i) := by
  refine ⟨?_, fun ht0 i => ?_⟩
  · by_cases ht0 : t = 0
    · exact Or.inl ht0
    · exact Or.inr (deforV1_ne_self_p34 a v1 v2 x1 x2 x6 t hnc hx1 hx2 hx6 ha ht0)
  · by_cases him : i % k = l % k
    · rw [modFold_p34 hk0 hper i, him, ← modFold_p34 hk0 hper l, hl]
      exact deforV1_ne_self_p34 a v1 v2 x1 x2 x6 t hnc hx1 hx2 hx6 ha ht0
    · exact hne t i ht him

/-- Identity case for `t = 0`: the relabel at `f = v2` is the identity. -/
private theorem relabelFF_id_p34 {v2 : V3} {FF : Set (V3 × V3)} :
    relabelFF_p34 v2 v2 FF = FF := by
  have hpt : ∀ z : V3 × V3,
      (if z.1 = v2 then v2 else z.1, if z.2 = v2 then v2 else z.2) = z := by
    rintro ⟨z1, z2⟩
    by_cases h1 : z1 = v2 <;> by_cases h2 : z2 = v2 <;> simp [h1, h2]
  unfold relabelFF_p34
  conv_rhs => rw [← Set.image_id FF]
  exact Set.image_congr fun z _ => hpt z

/-! ## Section 2: the FF-relabel and rho-node tower -/

/-- Epsilon selection from a singleton characterization. -/
private theorem epsilon_eq_of_p34 {α : Type*} [Nonempty α] {p : α → Prop} {a : α}
    (hdir : ∀ y, p y → y = a) (hb : p a) : Classical.epsilon p = a := by
  exact hdir _ (Classical.epsilon_spec (p := p) ⟨a, hb⟩)

/-- HOL `V3_DEFOR_EQ_IN_FF` (IMJXPHR.hl:2158): the relabelled face contains
exactly the edges of `FF` out of the deformed point. -/
theorem V3_DEFOR_EQ_IN_FF_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t), w') ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v2, w') ∈ FF := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  intro w'
  exact relabelFF_shapeA_p34 hfv hK3 hfn1 w'

/-- HOL `V3_DEFOR_EQ_IN_FF_V1` (IMJXPHR.hl:2232). -/
theorem V3_DEFOR_EQ_IN_FF_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t), w') ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v2, w') ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    intro w'
    exact relabelFF_shapeA_p34 hfv hK3 hfn1 w'

/-- HOL `V3_DEFOR_RHO_NODE` (IMJXPHR.hl:2320).  Mechanical transport of the
rho node through the face relabel, via `V3_DEFOR_EQ_IN_FF_p34`. -/
theorem V3_DEFOR_RHO_NODE_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
      (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 := by
  have hEQ := V3_DEFOR_EQ_IN_FF_p34 s k l w v1 v2 x1 x2 x6 a e t FF hk hkk hs hmw
    hl hl1 hx1p hx2p hx6p hnc hx1 hx2 hx6 ha he ht hne hte hFF
  simp only [rhoNode1]
  rw [funext fun w' => propext (hEQ w')]

/-- HOL `V3_DEFOR_RHO_NODE_V1` (IMJXPHR.hl:2345). -/
theorem V3_DEFOR_RHO_NODE_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
      (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 := by
  have hEQ := V3_DEFOR_EQ_IN_FF_V1_p34 s k l w v1 v2 x1 x2 x6 a e t FF hk hkk hs hmw
    hl hl1 hx1p hx2p hx6p hnc hx1 hx2 hx6 ha he ht hne hte hFF
  simp only [rhoNode1]
  rw [funext fun w' => propext (hEQ w')]

/-- HOL `V3_DEFOR_EQ_IN_FF_SYM` (IMJXPHR.hl:2373). -/
theorem V3_DEFOR_EQ_IN_FF_SYM_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (w', v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v2) ∈ FF := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  intro w'
  exact relabelFF_shapeB_p34 hfv hK3 hfn2 w'

/-- HOL `V3_DEFOR_EQ_IN_FF_SYM_V1` (IMJXPHR.hl:2449). -/
theorem V3_DEFOR_EQ_IN_FF_SYM_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (w', v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v2) ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    intro w'
    exact relabelFF_shapeB_p34 hfv hK3 hfn2 w'

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V1` (IMJXPHR.hl:2736). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (v1, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v1, w') ∈ FF := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  have haf : v1 ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
    fun hc => hf (l + 1) (by rw [hl1]; exact hc.symm)
  have hav : v1 ≠ v2 := fun hc => hadj (by rw [hl1]; exact hc.symm)
  have hnav : (v1, v2) ∉ FF := fun hF => hK7 (by rw [← hl1] at hF; exact hF)
  intro y
  exact relabelFF_shapeC_p34 hfv haf hav hnav y

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V1_V1` (IMJXPHR.hl:2868). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V1_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (v1, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v1, w') ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have haf : v1 ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + 1) (by rw [hl1]; exact hc.symm)
    have hav : v1 ≠ v2 := fun hc => hadj (by rw [hl1]; exact hc.symm)
    have hnav : (v1, v2) ∉ FF := fun hF => hK7 (by rw [← hl1] at hF; exact hF)
    intro y
    exact relabelFF_shapeC_p34 hfv haf hav hnav y

/-- HOL `V3_DEFOR_RHO_NODE_AT_V1` (IMJXPHR.hl:2999). -/
theorem V3_DEFOR_RHO_NODE_AT_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1 =
      rhoNode1 FF v1 := by
  have hEQ := V3_DEFOR_EQ_IN_FF_AT_V1_p34 s k l w v1 v2 x1 x2 x6 a e t FF hk hkk hs hmw
    hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 ha he ht hne hte hFF
  simp only [rhoNode1]
  rw [funext fun w' => propext (hEQ w')]

/-- HOL `V3_DEFOR_RHO_NODE_AT_V1_V1` (IMJXPHR.hl:3028). -/
theorem V3_DEFOR_RHO_NODE_AT_V1_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1 =
      rhoNode1 FF v1 := by
  have hEQ := V3_DEFOR_EQ_IN_FF_AT_V1_V1_p34 s k l w v1 v2 x1 x2 x6 a e t FF hk hkk hs hmw
    hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 ha he ht hne hte hFF
  simp only [rhoNode1]
  rw [funext fun w' => propext (hEQ w')]

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V1_SYM` (IMJXPHR.hl:3061). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V1_SYM_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (Classical.epsilon fun w' : V3 =>
        (w', v1) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  have hcf : v1 ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
    fun hc => hf (l + 1) (by rw [hl1]; exact hc.symm)
  have hcv : v1 ≠ v2 := fun hc => hadj (by rw [hl1]; exact hc.symm)
  have hinc : ∀ z, (z, v1) ∈ FF → z = v2 := fun z hF => hU3 z (by rw [← hl1] at hF; exact hF)
  have hvc : (v2, v1) ∈ FF := by rw [← hl1]; exact hE1
  apply epsilon_eq_of_p34
  · intro y hy
    exact (relabelFF_shapeS_p34 hfv hcf hcv hvc hinc y).mp hy
  · exact (relabelFF_shapeS_p34 hfv hcf hcv hvc hinc _).mpr rfl

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1` (IMJXPHR.hl:3173). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (Classical.epsilon fun w' : V3 =>
        (w', v1) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    have hinj := w_inj_p34 hk hkk hs hmw
    have hk0 : 0 < k := by omega
    have hperW : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
    have hU3 : ∀ z, (z, w (l + 1)) ∈ FF → z = v2 := by
      intro z hF
      obtain ⟨i, hi1, hi2⟩ := ff_edge_index_p34 hFF hF
      have hres : (i + 1) % k = (l + 1) % k := by
        by_contra hne
        exact hinj (i + 1) (l + 1) hne hi2
      rw [← hi1, modFold_p34 hk0 hperW i, res_succ_inj_p34 (by omega) hres,
        ← modFold_p34 hk0 hperW l, hl]
    have hE1 : (v2, w (l + 1)) ∈ FF := by
      have h : (w l, w (l + 1)) ∈ Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l, rfl⟩
      rw [hFF] at h
      rwa [hl] at h
    apply epsilon_eq_of_p34
    · intro y hy
      exact hU3 y (by rw [← hl1] at hy; exact hy)
    · exact (by rw [← hl1]; exact hE1)
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have hcf : v1 ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + 1) (by rw [hl1]; exact hc.symm)
    have hcv : v1 ≠ v2 := fun hc => hadj (by rw [hl1]; exact hc.symm)
    have hinc : ∀ z, (z, v1) ∈ FF → z = v2 := fun z hF => hU3 z (by rw [← hl1] at hF; exact hF)
    have hvc : (v2, v1) ∈ FF := by rw [← hl1]; exact hE1
    apply epsilon_eq_of_p34
    · intro y hy
      exact (relabelFF_shapeS_p34 hfv hcf hcv hvc hinc y).mp hy
    · exact (relabelFF_shapeS_p34 hfv hcf hcv hvc hinc _).mpr rfl

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1` (IMJXPHR.hl:2535): the azimuth at the
deformed point stays `pi` under the `v3_defor_v4` deformation of the face. -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_V1` (IMJXPHR.hl:2633): the two-sided
interval twin of `DEFORMATION_AZIM_V3_DEFOR_V1_p34`. -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1` (IMJXPHR.hl:3291). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1` (IMJXPHR.hl:3402). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)) = Real.pi := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_W` (IMJXPHR.hl:3519). -/
theorem V3_DEFOR_EQ_IN_FF_AT_W_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ v' : V3, (v', w (l + (s.k - 1))) ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v', w (l + (s.k - 1))) ∈ FF := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  have hbf : w (l + k - 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
    fun hc => hf (l + k - 1) hc.symm
  intro x
  rw [show l + (s.k - 1) = l + k - 1 from by rw [hkk]; omega]
  exact relabelFF_shapeD_p34 hfv hK3 hbf hbne hK8 x

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_W_V1` (IMJXPHR.hl:3646). -/
theorem V3_DEFOR_EQ_IN_FF_AT_W_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ v' : V3, (v', w (l + (s.k - 1))) ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v', w (l + (s.k - 1))) ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have hbf : w (l + k - 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + k - 1) hc.symm
    intro x
    rw [show l + (s.k - 1) = l + k - 1 from by rw [hkk]; omega]
    exact relabelFF_shapeD_p34 hfv hK3 hbf hbne hK8 x

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_W_SYM` (IMJXPHR.hl:3777). -/
theorem V3_DEFOR_EQ_IN_FF_AT_W_SYM_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (Classical.epsilon fun v' : V3 =>
        (w (l + k - 1), v') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  have hbf : w (l + k - 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
    fun hc => hf (l + k - 1) hc.symm
  apply epsilon_eq_of_p34
  · intro y hy
    exact (relabelFF_shapeS2_p34 hfv hbf hbne hE2 hU5 y).mp hy
  · exact (relabelFF_shapeS2_p34 hfv hbf hbne hE2 hU5 _).mpr rfl

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1` (IMJXPHR.hl:3891). -/
theorem V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (Classical.epsilon fun v' : V3 =>
        (w (l + k - 1), v') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    have hinj := w_inj_p34 hk hkk hs hmw
    have hk0 : 0 < k := by omega
    have hperW : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
    have hU5 : ∀ z, (w (l + k - 1), z) ∈ FF → z = v2 := by
      intro z hF
      obtain ⟨i, hi1, hi2⟩ := ff_edge_index_p34 hFF hF
      have hres : i % k = (l + k - 1) % k := by
        by_contra hne
        exact hinj i (l + k - 1) hne hi1
      have hstep : (i + 1) % k = l % k := by
        have hx : (i + 1) % k = ((l + k - 1) + 1) % k := res_succ_congr_p34 (by omega) hres
        rwa [show (l + k - 1) + 1 = l + k by omega, Nat.add_mod_right] at hx
      rw [← hi2, modFold_p34 hk0 hperW (i + 1), hstep, ← modFold_p34 hk0 hperW l, hl]
    have hE2 : (w (l + k - 1), v2) ∈ FF := by
      have h : (w (l + k - 1), w ((l + k - 1) + 1)) ∈
        Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l + k - 1, rfl⟩
      rw [hFF] at h
      rw [show (l + k - 1) + 1 = l + k by omega, hperW l, hl] at h
      exact h
    apply epsilon_eq_of_p34
    · intro y hy
      exact hU5 y hy
    · exact hE2
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have hbf : w (l + k - 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + k - 1) hc.symm
    apply epsilon_eq_of_p34
    · intro y hy
      exact (relabelFF_shapeS2_p34 hfv hbf hbne hE2 hU5 y).mp hy
    · exact (relabelFF_shapeS2_p34 hfv hbf hbne hE2 hU5 _).mpr rfl

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_W` (IMJXPHR.hl:4014). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1` (IMJXPHR.hl:4154). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = Real.pi := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY` (IMJXPHR.hl:4296). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V_ANY_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
    (hvV : v ∈ Set.range w) :
    ∀ w' : V3, (v, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v, w') ∈ FF := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  obtain ⟨i, hi⟩ := hvV
  have haf : v ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
    fun hc => hf i (by rw [hc] at hi; exact hi.symm)
  have hnav : (v, v2) ∉ FF := fun hF => absurd (hU1 v hF) hvw
  intro w'
  exact relabelFF_shapeC_p34 hfv haf hvv2 hnav w'

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1` (IMJXPHR.hl:4413). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
    (hvV : v ∈ Set.range w) :
    ∀ w' : V3, (v, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v, w') ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    obtain ⟨i, hi⟩ := hvV
    have haf : v ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf i (by rw [hc] at hi; exact hi.symm)
    have hnav : (v, v2) ∉ FF := fun hF => absurd (hU1 v hF) hvw
    intro w'
    exact relabelFF_shapeC_p34 hfv haf hvv2 hnav w'

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM` (IMJXPHR.hl:4557). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : 0 < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
    (hvV : v ∈ Set.range w) :
    ∀ w' : V3, (w', v) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v) ∈ FF := by
  obtain ⟨hfv, hf⟩ := hf_plain_p34 hne ht hte hl
  obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
    ff_ctx_p34 hk hkk hs hmw hl hf hFF
  obtain ⟨i, hi⟩ := hvV
  have hbf : v ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
    fun hc => hf i (by rw [hc] at hi; exact hi.symm)
  have hnbv : (v2, v) ∉ FF := fun hF => hvv1 (by rw [← hl1]; exact hU2 v hF)
  intro w'
  exact relabelFF_shapeD_p34 hfv hK3 hbf hvv2 hnbv w'

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1` (IMJXPHR.hl:4684). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
    (hvV : v ∈ Set.range w) :
    ∀ w' : V3, (w', v) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v) ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    obtain ⟨i, hi⟩ := hvV
    have hbf : v ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf i (by rw [hc] at hi; exact hi.symm)
    have hnbv : (v2, v) ∉ FF := fun hF => hvv1 (by rw [← hl1]; exact hU2 v hF)
    intro w'
    exact relabelFF_shapeD_p34 hfv hK3 hbf hvv2 hnbv w'

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY` (IMJXPHR.hl:4829). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, 0 < t ∧ t < e → v ≠ v1 → v ≠ v2 →
      v ≠ w (l + k - 1) → v ∈ Set.range w →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1` (IMJXPHR.hl:4887). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ≠ v1 → v ≠ v2 →
      v ≠ w (l + k - 1) → v ∈ Set.range w →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL` (IMJXPHR.hl:4947). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, 0 < t ∧ t < e → v ∈ Set.range w →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1` (IMJXPHR.hl:5022). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ∈ Set.range w →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR` (IMJXPHR.hl:5106). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → 0 < t → t < e →
      interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1` (IMJXPHR.hl:5141). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
      interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi := by
  sorry

/-- HOL `V_DEFORMATION_V3_DEFOR` (IMJXPHR.hl:5175). -/
theorem V_DEFORMATION_V3_DEFOR_p34 (w : ℕ → V3) (x1 x2 x6 t : ℝ) (v1 v2 : V3) :
    Set.range (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t) =
      (fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) '' Set.range w :=
  Set.range_comp (fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) w

/-- HOL `E_DEFORMATION_V3_DEFOR` (IMJXPHR.hl:5181). -/
theorem E_DEFORMATION_V3_DEFOR_p34 (w : ℕ → V3) (x1 x2 x6 t : ℝ) (v1 v2 : V3) :
    Set.range (fun i => {v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + 1)) t}) =
      (fun e => (fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) '' e) ''
        Set.range (fun i => {w i, w (i + 1)}) := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨{w i, w (i + 1)}, Set.mem_range_self i, ?_⟩
    simp [Set.image_insert_eq, Set.image_singleton]
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, rfl⟩ := he
    exact ⟨i, by simp [Set.image_insert_eq, Set.image_singleton]⟩

/-- HOL `F_DEFORMATION_V3_DEFOR` (IMJXPHR.hl:5211). -/
theorem F_DEFORMATION_V3_DEFOR_p34 (w : ℕ → V3) (x1 x2 x6 t : ℝ) (v1 v2 : V3) :
    Set.range (fun i => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + 1)) t)) =
      (fun d : V3 × V3 => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.1 t,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.2 t)) ''
        Set.range (fun i => (w i, w (i + 1))) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(w i, w (i + 1)), Set.mem_range_self i, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨i, rfl⟩ := hp
    exact ⟨i, by simp⟩

/-- HOL `DEFORMATION_LUNAR_AFFINE_HULL` (IMJXPHR.hl:5233). -/
theorem DEFORMATION_LUNAR_AFFINE_HULL_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 v w1 : V3) (x1 x2 x6 a : ℝ) (V : Set V3) (E : Set (Set V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF'')
    (hV : Set.range w = V)
    (hE : Set.range (fun i : ℕ => {w i, w (i + 1)}) = E)
    (hlun : Lunar v w1 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t < e →
      v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3) := by
  sorry

/-- HOL `DEFORMATION_LUNAR_AFFINE_HULL_V1` (IMJXPHR.hl:5343). -/
theorem DEFORMATION_LUNAR_AFFINE_HULL_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 v w1 : V3) (x1 x2 x6 a : ℝ) (V : Set V3) (E : Set (Set V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = Set.range (fun i : ℕ => (w i, w (i + 1))))
    (hV : Set.range w = V)
    (hE : Set.range (fun i : ℕ => {w i, w (i + 1)}) = E)
    (hlun : Lunar v w1 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, t ∈ Icc (-e) e →
      v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3) := by
  sorry

/-! ## Section 3: the composite registry arrows -/

/-- HOL `V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1` (IMJXPHR.hl:5535; shape
`mk_imp (ZLZTHIC_concl, mk_imp (MHAEYJN_concl, V3_DEFOR_CONVEX_LOCAL_FAN_concl))`).
DISCHARGES: proving this closes the `ZLZTHIC`/`MHAEYJN` antecedents for the
`v3_defor_v4` convex-local-fan conclusion. -/
theorem V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_p34 (hz : ZLZTHIC_prop_p34)
    (hm : MHAEYJN_prop_p34) (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 : ℝ)
    (v1 v2 : V3) (a : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hk : 3 < k)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hn2 : ¬(2 = ‖v2‖))
    (hJ : ∀ i, ¬s.J l i)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      ConvexLocalFan (Set.range fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)
        (Set.range fun i => {v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t})
        (Set.range fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t)) := by
  sorry

/-- HOL `CARD_FF_EQ_V3_DEFOR_DEFORMATION` (IMJXPHR.hl:5808). -/
theorem CARD_FF_EQ_V3_DEFOR_DEFORMATION_p34 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (V : Set V3)
    (v1 v2 : V3) (x1 x2 x6 a e1 : ℝ)
    (hkk : s.k = k) (hV : Set.range w = V) (hs : isScsV39 s) (hk : 3 < k)
    (hBB : BBsV39 s w)
    (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
      BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)) :
    ∀ t : ℝ, 0 < t → t < e1 →
      (Set.range (fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t))).ncard =
        (Set.range fun i => (w i, w (i + 1))).ncard := by
  sorry

/-- HOL `DSV_V3_DEFOR_EQ` (IMJXPHR.hl:5842). -/
theorem DSV_V3_DEFOR_EQ_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 : V3) (t a x1 x2 x6 : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hBB : BBsV39 s w)
    (hJ : ∀ i, ¬s.J l i) :
    dsvV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 (w l) (w i) t) = dsvV39 s w := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1` (IMJXPHR.hl:5975). -/
theorem DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v := by
  sorry

/-- HOL `RHO_FUN_DEFORMATION_V3_DEFOR` (IMJXPHR.hl:6009). -/
theorem RHO_FUN_DEFORMATION_V3_DEFOR_p34 (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      rhoFun ‖(v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) : V3)‖ < rhoFun ‖v2‖ := by
  sorry

/-- HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1` (IMJXPHR.hl:6051). -/
theorem INTERIOR_ANGLE_SAME_V3_DEFOR1_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e1 : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
      BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t))
    (he1 : 0 < e1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < e →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF))^[i]
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k))) := by
  sorry

/-- HOL `TAUSTAR_V3_DEFOR` (IMJXPHR.hl:6140; statement `TAUSTAR_V3_DEFOR_concl`,
IMJXPHR.hl:6119). -/
theorem TAUSTAR_V3_DEFOR_p34 : TAUSTAR_V3_DEFOR_concl_p34 := by
  sorry

/-- HOL `EQ_W_L_IN_BBS` (IMJXPHR.hl:6299). -/
theorem EQ_W_L_IN_BBS_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (hk : 3 < k) (hkk : s.k = k) (hBB : BBsV39 s w) :
    w ((l + k - 1) + 1) = w l := by
  rw [show (l + k - 1) + 1 = l + k by omega, ← hkk]
  exact hBB.2.1 l

/-! ## Section 4: the TWO_CASES twins (fixed neighbour `w (l + k - 1)`) -/

/-- HOL `HYPER_MM_COLLINEAR_TWO_CASES` (IMJXPHR.hl:6316). -/
theorem HYPER_MM_COLLINEAR_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hk : 3 < k)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    0 < x1 ∧ 0 < x2 ∧ 0 < x6 ∧ ¬Collinear ℝ ({0, v1, v2} : Set V3) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_TWO_CASES` (IMJXPHR.hl:6354). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hbound : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) → s.a l j < dist v2 (w j)) :
    ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_TWO_CASES` (IMJXPHR.hl:6374). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hbound : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) → s.a l j < dist v2 (w j)) :
    ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
  -- NEEDS: the `MMs`-collinearity kit (HYPER_MM_COLLINEAR, still sorried):
  -- the profile is continuous and strict at `t = 0`, but the strictness
  -- `s.a l j < dist v2 (w j)` only feeds `v3DeforV1` machinery after
  -- `¬Collinear {0, v1, v2}` is available, which this per-index lemma's
  -- hypotheses do not (yet) provide.
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_TWO_CASES` (IMJXPHR.hl:6394).
Sits on the (sorried) per-index `A_SUC_TWO_CASES` parent via the finite-minimum
argument plus `MMs`/`a`-table periodicity. -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hbound : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) → s.a l j < dist v2 (w j)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ j : ℕ,
      ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
      s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 a
    hs hmw hkk hk hl hlk hx1 hx2 hx6 ha hbound
  have hper_a := scsA_periodic_p34 s k hs hkk l
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  set T : Finset ℕ := (Finset.range k).filter
    (fun i => l % k ≠ i % k ∧ l % k ≠ (i + 1) % k) with hT
  have hmono : ∀ (i : ℕ) (e : ℝ),
      (∀ τ : ℝ, 0 < τ ∧ τ < e → s.a l i < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i)) →
      ∀ e' : ℝ, 0 < e' → e' ≤ e →
      ∀ τ : ℝ, 0 < τ ∧ τ < e' → s.a l i < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨hτ.1, hτ.2.trans_le hle⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun τ hτ j hj1 hj2 => ?_⟩
    have hmeq : ((j % k) + 1) % k = (j + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq j k)
    have hjm : j % k ∈ T :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hj1 (by rw [Nat.mod_eq_of_lt (Nat.mod_lt j hk0)] at hc; exact hc),
          fun hc => hj2 (by rw [hmeq] at hc; exact hc)⟩
    rw [hempty] at hjm
    simp at hjm
  · obtain ⟨e0, he0, hall⟩ := minWitness_p34 hmono hne
      (fun i hi => hparent i (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2)
    refine ⟨e0, he0, fun τ hτ j hj1 hj2 => ?_⟩
    have hmeq : ((j % k) + 1) % k = (j + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq j k)
    have haj : s.a l j = s.a l (j % k) := modFold_p34 hk0 hper_a j
    have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w j) =
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (j % k)) :=
      congrArg (fun x => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) x)
        (modFold_p34 hk0 hper_w j)
    rw [haj, hwj]
    exact hall (j % k)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hj1 (by rw [Nat.mod_eq_of_lt (Nat.mod_lt j hk0)] at hc; exact hc),
          fun hc => hj2 (by rw [hmeq] at hc; exact hc)⟩)
      τ hτ

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_TWO_CASES` (IMJXPHR.hl:6512). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hkk : s.k = k) (hk : 3 < k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, scsDiag k l i →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < s.b l i := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_2_TWO_CASES` (IMJXPHR.hl:6563). -/
theorem DEFORMATION_DIST_LE_2_TWO_CASES_p34 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l i < dist v2 (w i))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hmod : (l + 1) % k = i % k) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      2 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_EDGE_TWO_CASES` (IMJXPHR.hl:6613). -/
theorem DEFORMATION_V3_DEFOR_EDGE_TWO_CASES_p34 (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l i < dist v2 (w i))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hmod : (l + 1) % k = i % k) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < dist v2 (w i) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES` (IMJXPHR.hl:7042;
the first `let` of the shadowed pair). -/
theorem DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l (l + 1) < dist v2 (w (l + 1)))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, ¬(i % k = l % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES` (IMJXPHR.hl:7146;
the surviving second `let` of the shadowed pair, named `_b`). -/
theorem DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_b_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
    (ha_lt : s.a l (l + 1) < dist v2 (w (l + 1)))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 a
    hk hkk hs hmw haz hncW haff hl hlk hn ha_lt hx1 hx2 hx6 ha hdiag
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  have hper_b : ∀ i, s.b l (i + k) = s.b l i := by
    intro i
    rw [← hkk]
    exact ((hs.2.2.2.2.2.2.2.2.2.2.1) l i).2
  set T : Finset ℕ := (Finset.range k).filter (fun i => i % k ≠ l % k) with hT
  have hmono : ∀ (i : ℕ) (e : ℝ),
      (∀ τ : ℝ, 0 < τ ∧ τ < e → dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) ≤ s.b l i) →
      ∀ e' : ℝ, 0 < e' → e' ≤ e →
      ∀ τ : ℝ, 0 < τ ∧ τ < e' → dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) ≤ s.b l i := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨hτ.1, hτ.2.trans_le hle⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun τ hτ i hi => ?_⟩
    have hjm : i % k ∈ T :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hi (by rw [Nat.mod_eq_of_lt (Nat.mod_lt i hk0)] at hc; exact hc)⟩
    rw [hempty] at hjm
    simp at hjm
  · obtain ⟨e0, he0, hall⟩ := minWitness_p34 hmono hne
      (fun i hi => hparent i (Finset.mem_filter.mp hi).2)
    refine ⟨e0, he0, fun τ hτ i hi => ?_⟩
    have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) =
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (i % k)) :=
      congrArg (fun x => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) x)
        (modFold_p34 hk0 hper_w i)
    have hbj : s.b l i = s.b l (i % k) := modFold_p34 hk0 hper_b i
    rw [hwj, hbj]
    exact hall (i % k)
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0),
          fun hc => hi (by rw [Nat.mod_eq_of_lt (Nat.mod_lt i hk0)] at hc; exact hc)⟩)
      τ hτ

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES` (IMJXPHR.hl:7265). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∀ i : ℕ, ¬(i % k = l % k) →
      ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
        0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_TWO_CASES` (IMJXPHR.hl:7299). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  have hk0 : 0 < k := by omega
  have hparent := DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 a
    hk hkk hs hmw hl hlk hx1 hx2 hx6 ha
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  set T : Finset ℕ := (Finset.range k).filter (fun i => i % k ≠ l % k) with hT
  have hmem : ∀ i : ℕ, ¬(i % k = l % k) → i % k ∈ T := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk0), ?_⟩
    rw [Nat.mod_eq_of_lt (Nat.mod_lt i hk0)]
    exact hi
  have hmono : ∀ (i : ℕ) (e : ℝ),
      (∀ τ : ℝ, -e < τ ∧ τ < e → 0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i)) →
      ∀ e' : ℝ, 0 < e' → e' ≤ e →
      ∀ τ : ℝ, -e' < τ ∧ τ < e' → 0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨lt_of_le_of_lt (neg_le_neg hle) hτ.1, hτ.2.trans_le hle⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun τ hτ i hi => ?_⟩
    exact absurd (hmem i hi) (by rw [hempty]; simp)
  · obtain ⟨e0, he0, hall⟩ := minWitness_p34 hmono hne
      (fun i hi => hparent i (Finset.mem_filter.mp hi).2)
    refine ⟨e0, he0, fun τ hτ i hi => ?_⟩
    have hwj : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) =
        dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w (i % k)) :=
      congrArg (fun x => dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) x)
        (modFold_p34 hk0 hper_w i)
    rw [hwj]
    exact hall (i % k) (hmem i hi) τ hτ

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_TWO_CASES` (IMJXPHR.hl:7394). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := by
  obtain ⟨e, he, hall⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_TWO_CASES_p34 s k l w v1 v2
    x1 x2 x6 a hk hkk hs hmw hl hlk hx1 hx2 hx6 ha
  refine ⟨e, he, fun t i ht hi hcon => ?_⟩
  have hpos := hall t i ht hi
  rw [hcon, dist_self] at hpos
  exact lt_irrefl (0 : ℝ) hpos

/-- HOL `V3_DEFOR_EQ_IN_FF_V1_TWO_CASES` (IMJXPHR.hl:7417). -/
theorem V3_DEFOR_EQ_IN_FF_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t), w') ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v2, w') ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    intro w'
    exact relabelFF_shapeA_p34 hfv hK3 hfn1 w'

/-- HOL `V3_DEFOR_RHO_NODE_V1_TWO_CASES` (IMJXPHR.hl:7499). -/
theorem V3_DEFOR_RHO_NODE_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
      (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 := by
  have hEQ := V3_DEFOR_EQ_IN_FF_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 a e t FF hk hkk hs hmw
    hl hlk hx1p hx2p hx6p hnc hx1 hx2 hx6 ha he ht hne hte hFF
  simp only [rhoNode1]
  rw [funext fun w' => propext (hEQ w')]

/-- HOL `V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES` (IMJXPHR.hl:7526). -/
theorem V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
    (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ w' : V3, (w', v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v2) ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    intro w'
    exact relabelFF_shapeB_p34 hfv hK3 hfn2 w'

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_V1_TWO_CASES` (IMJXPHR.hl:7609). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)) = Real.pi := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V1_V1_TWO_CASES` (IMJXPHR.hl:7713). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V1_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ a' : V3, (w (l + 1), a') ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w (l + 1), a') ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have haf : w (l + 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + 1) hc.symm
    have hav : w (l + 1) ≠ v2 := fun hc => hadj hc.symm
    intro y
    exact relabelFF_shapeC_p34 hfv haf hav hK7 y

/-- HOL `V3_DEFOR_RHO_NODE_AT_V1_V1_TWO_CASES` (IMJXPHR.hl:7865). -/
theorem V3_DEFOR_RHO_NODE_AT_V1_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
      (w (l + 1)) = rhoNode1 FF (w (l + 1)) := by
  have hEQ := V3_DEFOR_EQ_IN_FF_AT_V1_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 a e t FF
    hk hkk hs hmw hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 ha he ht hne hte hFF
  simp only [rhoNode1]
  rw [funext fun a' => propext (hEQ a')]

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_TWO_CASES` (IMJXPHR.hl:7895). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (Classical.epsilon fun a' : V3 =>
        (a', w (l + 1)) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    have hinj := w_inj_p34 hk hkk hs hmw
    have hk0 : 0 < k := by omega
    have hperW : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
    have hU3 : ∀ z, (z, w (l + 1)) ∈ FF → z = v2 := by
      intro z hF
      obtain ⟨i, hi1, hi2⟩ := ff_edge_index_p34 hFF hF
      have hres : (i + 1) % k = (l + 1) % k := by
        by_contra hne
        exact hinj (i + 1) (l + 1) hne hi2
      rw [← hi1, modFold_p34 hk0 hperW i, res_succ_inj_p34 (by omega) hres,
        ← modFold_p34 hk0 hperW l, hl]
    have hE1 : (v2, w (l + 1)) ∈ FF := by
      have h : (w l, w (l + 1)) ∈ Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l, rfl⟩
      rw [hFF] at h
      rwa [hl] at h
    apply epsilon_eq_of_p34
    · intro y hy
      exact hU3 y hy
    · exact hE1
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have hcf : w (l + 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + 1) hc.symm
    have hcv : w (l + 1) ≠ v2 := fun hc => hadj hc.symm
    refine epsilon_eq_of_p34 (fun y hy => ?_) ?_
    · exact (relabelFF_shapeS_p34 hfv hcf hcv hE1 hU3 y).mp hy
    · exact (relabelFF_shapeS_p34 hfv hcf hcv hE1 hU3 _).mpr rfl

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_TWO_CASES` (IMJXPHR.hl:8017). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t)) = Real.pi := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_W_V1_TWO_CASES` (IMJXPHR.hl:8152). -/
theorem V3_DEFOR_EQ_IN_FF_AT_W_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∀ v' : V3, (v', w (l + (s.k - 1))) ∈
        relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v', w (l + (s.k - 1))) ∈ FF := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have hbf : w (l + k - 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + k - 1) hc.symm
    intro x
    rw [show l + (s.k - 1) = l + k - 1 from by rw [hkk]; omega]
    exact relabelFF_shapeD_p34 hfv hK3 hbf hbne hK8 x

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_TWO_CASES` (IMJXPHR.hl:8286). -/
theorem V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    (Classical.epsilon fun v' : V3 =>
        (w (l + k - 1), v') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    have hinj := w_inj_p34 hk hkk hs hmw
    have hk0 : 0 < k := by omega
    have hperW : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
    have hU5 : ∀ z, (w (l + k - 1), z) ∈ FF → z = v2 := by
      intro z hF
      obtain ⟨i, hi1, hi2⟩ := ff_edge_index_p34 hFF hF
      have hres : i % k = (l + k - 1) % k := by
        by_contra hne
        exact hinj i (l + k - 1) hne hi1
      have hstep : (i + 1) % k = l % k := by
        have hx : (i + 1) % k = ((l + k - 1) + 1) % k := res_succ_congr_p34 (by omega) hres
        rwa [show (l + k - 1) + 1 = l + k by omega, Nat.add_mod_right] at hx
      rw [← hi2, modFold_p34 hk0 hperW (i + 1), hstep, ← modFold_p34 hk0 hperW l, hl]
    have hE2 : (w (l + k - 1), v2) ∈ FF := by
      have h : (w (l + k - 1), w ((l + k - 1) + 1)) ∈
        Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l + k - 1, rfl⟩
      rw [hFF] at h
      rw [show (l + k - 1) + 1 = l + k by omega, hperW l, hl] at h
      exact h
    apply epsilon_eq_of_p34
    · intro y hy
      exact hU5 y hy
    · exact hE2
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    have hbf : w (l + k - 1) ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf (l + k - 1) hc.symm
    apply epsilon_eq_of_p34
    · intro y hy
      exact (relabelFF_shapeS2_p34 hfv hbf hbne hE2 hU5 y).mp hy
    · exact (relabelFF_shapeS2_p34 hfv hbf hbne hE2 hU5 _).mpr rfl

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_TWO_CASES` (IMJXPHR.hl:8406). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = Real.pi := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_TWO_CASES` (IMJXPHR.hl:8551). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 v : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + 1))
    (hvV : v ∈ Set.range w) :
    ∀ w' : V3, (v, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (v, w') ∈ FF := by

  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    obtain ⟨i, hi⟩ := hvV
    have haf : v ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf i (by rw [hc] at hi; exact hi.symm)
    have hnav : (v, v2) ∉ FF := fun hF => hvv1 (by rw [← hlk]; exact hU1 v hF)
    intro w'
    exact relabelFF_shapeC_p34 hfv haf hvv2 hnav w'

/-- HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_TWO_CASES` (IMJXPHR.hl:8695). -/
theorem V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 v : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (he : 0 < e) (ht : -e < t)
    (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
    (hte : t < e)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
    (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + 1))
    (hvV : v ∈ Set.range w) :
    ∀ w' : V3, (w', v) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v) ∈ FF := by

  by_cases ht0 : t = 0
  · subst ht0
    rw [sub_zero, v3DeforV1_at_x2_p34 a v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 ha,
      relabelFF_id_p34]
    intro w'
    exact Iff.rfl
  · obtain ⟨hdisj, hf⟩ := hf_mod_p34 hnc hx1 hx2 hx6 ha (by omega)
      (MMs_periodic_p34 s k w hkk hmw) hne ⟨ht, hte⟩ hl
    have hfv : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ v2 :=
      hdisj.resolve_left ht0
    have hf : ∀ i : ℕ, v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := hf ht0
    obtain ⟨hK3, hfn1, hfn2, hadj, hU1, hU2, hU3, hK7, hK8, hU5, hE1, hE2, hbne⟩ :=
      ff_ctx_p34 hk hkk hs hmw hl hf hFF
    obtain ⟨i, hi⟩ := hvV
    have hbf : v ≠ v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) :=
      fun hc => hf i (by rw [hc] at hi; exact hi.symm)
    have hnbv : (v2, v) ∉ FF := fun hF => absurd (hU2 v hF) hvw
    intro w'
    exact relabelFF_shapeD_p34 hfv hK3 hbf hvv2 hnbv w'

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_TWO_CASES` (IMJXPHR.hl:8838). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ≠ v1 → v ≠ v2 →
      v ≠ w (l + 1) → v ∈ Set.range w →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES` (IMJXPHR.hl:8900). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ∈ Set.range w →
      azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
        (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
        (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = Real.pi := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_TWO_CASES` (IMJXPHR.hl:8977). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
      interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi := by
  sorry

/-- HOL `DEFORMATION_LUNAR_AFFINE_HULL_V1_TWO_CASES` (IMJXPHR.hl:9013). -/
theorem DEFORMATION_LUNAR_AFFINE_HULL_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 v w1 : V3) (x1 x2 x6 a : ℝ) (V : Set V3) (E : Set (Set V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
    (hV : Set.range w = V)
    (hE : Set.range (fun i : ℕ => {w i, w (i + 1)}) = E)
    (hlun : Lunar v w1 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, t ∈ Icc (-e) e →
      v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3) := by
  sorry

/-- HOL `V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_TWO_CASES` (IMJXPHR.hl:9171;
shape `mk_imp (ZLZTHIC_concl, mk_imp (MHAEYJN_concl,
V3_DEFOR_CONVEX_LOCAL_FAN_TWO_CASES_concl))`). -/
theorem V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_TWO_CASES_p34 (hz : ZLZTHIC_prop_p34)
    (hm : MHAEYJN_prop_p34) (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 : ℝ)
    (v1 v2 : V3) (a : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hk : 3 < k)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hn2 : ¬(2 = ‖v2‖))
    (hJ : ∀ i, ¬s.J l i)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      ConvexLocalFan (Set.range fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)
        (Set.range fun i => {v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t})
        (Set.range fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
          v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t)) := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_TWO_CASES`
(IMJXPHR.hl:9397). -/
theorem DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ)
    (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v := by
  sorry

/-- HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES` (IMJXPHR.hl:9431). -/
theorem INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a e1 : ℝ) (FF : Set (V3 × V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1)
    (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
      BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t))
    (he1 : 0 < e1)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < e →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
        ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF))^[i]
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k))) := by
  sorry

/-- HOL `TAUSTAR_V3_DEFOR_TWO_CASES` (IMJXPHR.hl:9527; statement
`TAUSTAR_V3_DEFOR_TWO_CASES_concl`, IMJXPHR.hl:9504). -/
theorem TAUSTAR_V3_DEFOR_TWO_CASES_p34 : TAUSTAR_V3_DEFOR_TWO_CASES_concl_p34 := by
  sorry

/-- HOL `IMJXPHR` (IMJXPHR.hl:9703; shape `mk_imp (ZLZTHIC_concl,
mk_imp (MHAEYJN_concl, IMJXPHR_concl))`, conclusion IMJXPHR_concl_p34 =
`IMJXPHR_concl` verbatim, IMJXPHR.hl:9682, aligned with LocalAuto1
`IMJXPHRv2_concl`).  DISCHARGES: proving this closes the `IMJXPHRv2_concl`
registry sorry (LocalAuto1). -/
theorem IMJXPHR_p34 (hz : ZLZTHIC_prop_p34) (hm : MHAEYJN_prop_p34) :
    IMJXPHR_concl_p34 := by
  sorry

end Kepler.Text

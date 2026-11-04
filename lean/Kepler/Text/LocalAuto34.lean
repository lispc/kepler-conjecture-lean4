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
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto7
import Kepler.Text.CircularSolKit
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto35
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

/-! ### Private coe/dot/cross3 kit (ported from the TopologyFan private
block; `cross3` here is the public `PackingAuto18` one, same body). -/

private theorem coe_smul_p34 (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem coe_zero_p34 : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem coe_sub_p34 (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem toLp_smul_p34 (t : ℝ) (p : Fin 3 → ℝ) :
    (WithLp.toLp 2 (t • p) : V3) = t • (WithLp.toLp 2 p : V3) := by
  rw [show t • (WithLp.toLp 2 p : V3) =
      WithLp.toLp 2 ((t • (WithLp.toLp 2 p : V3) : Fin 3 → ℝ)) from
    (WithLp.toLp_ofLp 2 _).symm]

private theorem crossProduct_smul_left_p34 (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

private theorem cross3_smul_left_p34 (t : ℝ) (a b : V3) :
    cross3 (t • a) b = t • cross3 a b := by
  rw [cross3, cross3, coe_smul_p34, crossProduct_smul_left_p34, toLp_smul_p34]

private theorem dot_coe_p34 (a b : V3) :
    (a : Fin 3 → ℝ) ⬝ᵥ (b : Fin 3 → ℝ) = a ⬝ᵥ b := rfl

private theorem dot_comm_p34 (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem zero_dot_p34 (a : V3) : (0 : V3) ⬝ᵥ a = 0 :=
  zero_dotProduct (a : Fin 3 → ℝ)

private theorem smul_dot_p34 (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem add_dot_p34 (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem sub_dot_p34 (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_sub_p34 (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_smul_p34 (a b : V3) (t : ℝ) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem cross3_eq_p34 (a b : V3) :
    cross3 a b = WithLp.toLp 2 (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) := rfl

private theorem cross3_dot_left_p34 (a b : V3) : a ⬝ᵥ cross3 a b = 0 := by
  rw [cross3, dotProduct_comm, dot_toLp, dotProduct_comm, triple_product_permutation]
  exact dot_cross_self _ _

private theorem cross3_dot_right_p34 (a b : V3) : b ⬝ᵥ cross3 a b = 0 := by
  rw [cross3, dotProduct_comm, dot_toLp, dotProduct_comm]
  exact dot_cross_self _ _

private theorem cross3_cross3_p34 (a b c : V3) :
    cross3 (cross3 a b) c = ((a : Fin 3 → ℝ) ⬝ᵥ (c : Fin 3 → ℝ)) • b -
      ((b : Fin 3 → ℝ) ⬝ᵥ (c : Fin 3 → ℝ)) • a := by
  rw [cross3_eq_p34, cross3_eq_p34, cross_cross_eq_smul_sub_smul]
  simp

private theorem cross3_dot_self_p34 (a b : V3) :
    cross3 a b ⬝ᵥ cross3 a b = (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) * (b ⬝ᵥ a) := by
  rw [cross3_eq_p34, dot_toLp, coe_toLp, cross_dot_cross, dot_coe_p34, dot_coe_p34,
    dot_coe_p34, dot_coe_p34]

/-! ### Distinctness helpers (from `¬ Collinear ℝ {x, v, u}`). -/

private theorem ncol_vx_p34 {x v u : V3} (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) : v ≠ x :=
  fun he => hnc (collinear3_of_eq he)

private theorem ncol_ux_p34 {x v u : V3} (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) : u ≠ x := by
  intro he
  apply hnc
  rw [he]
  simpa using collinear_pair ℝ v x

private theorem ncol_uv_p34 {x v u : V3} (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) : u ≠ v := by
  intro he
  apply hnc
  rw [he]
  simpa using collinear_pair ℝ x v

/-- Shifted collinearity: `{0, v-x, u-x}` vs `{x, v, u}`. -/
private theorem ncol_shift_p34 {x v u : V3} (hvx : v ≠ x) :
    Collinear ℝ ({0, v - x, u - x} : Set V3) ↔ Collinear ℝ ({x, v, u} : Set V3) := by
  have h1 : Collinear ℝ ({0, v - x, u - x} : Set V3) ↔ ∃ c : ℝ, u - x = c • (v - x) := by
    show Collinear3 (0:V3) (v - x) (u - x) ↔ _
    rw [collinear3_iff_smul (sub_ne_zero.mpr hvx)]
    simp only [sub_zero]
  have h2 : Collinear ℝ ({x, v, u} : Set V3) ↔ ∃ c : ℝ, u - x = c • (v - x) := by
    show Collinear3 x v u ↔ _
    exact collinear3_iff_smul hvx
  exact h1.trans h2.symm

/-! ### eFan facts (ports of the TopologyFan kit). -/

private theorem e3Fan_dot_self_p34 (hvx : v ≠ x) (u : V3) :
    e3Fan_p34 x v u ⬝ᵥ e3Fan_p34 x v u = 1 := by
  have h1 : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  rw [e3Fan_p34, coe_smul_p34, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← norm_sq_eq_dot, smul_eq_mul]
  have h2 : ‖v - x‖⁻¹ * (‖v - x‖⁻¹ * ‖v - x‖ ^ 2) = 1 := by field_simp [h1]
  exact h2

private theorem e3Fan_cross_ux_ne_zero_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    cross3 (e3Fan_p34 x v u) (u - x) ≠ 0 := by
  intro hzero
  have hvx : v ≠ x := ncol_vx_p34 hnc
  -- |cross|² = |ux|² - (ux·e3)² = 0 ⟹ ux = t•e3 ⟹ 共线
  have hsq : (u - x) ⬝ᵥ (u - x) =
      ((u - x) ⬝ᵥ e3Fan_p34 x v u) * ((u - x) ⬝ᵥ e3Fan_p34 x v u) := by
    have h1 : cross3 (e3Fan_p34 x v u) (u - x) ⬝ᵥ cross3 (e3Fan_p34 x v u) (u - x) = 0 := by
      rw [hzero, coe_zero_p34, zero_dotProduct]
    rw [cross3_eq_p34, dot_toLp, coe_toLp, cross_dot_cross, dot_coe_p34, dot_coe_p34,
      dot_coe_p34, dot_coe_p34, e3Fan_dot_self_p34 hvx u,
      dotProduct_comm ((u - x : V3) : Fin 3 → ℝ) ((e3Fan_p34 x v u : V3) : Fin 3 → ℝ)] at h1
    rw [← coe_sub_p34]
    rw [dotProduct_comm ((u - x : V3) : Fin 3 → ℝ) ((e3Fan_p34 x v u : V3) : Fin 3 → ℝ)]
    linarith [h1]
  have hp : ((u - x) - ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u) ⬝ᵥ
      ((u - x) - ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u) = 0 := by
    have he3 : e3Fan_p34 x v u ⬝ᵥ e3Fan_p34 x v u = 1 := e3Fan_dot_self_p34 hvx u
    rw [← coe_sub_p34] at hsq
    -- 变量化：(u-x)、e3Fan 变为原子变量，绕开复合 coercion 的混合形态
    set ux : V3 := u - x with hux
    set e3 : V3 := e3Fan_p34 x v u with he3s
    have hcomm : e3 ⬝ᵥ ux = ux ⬝ᵥ e3 := dotProduct_comm _ _
    have hp' : (ux - (ux ⬝ᵥ e3) • e3) ⬝ᵥ (ux - (ux ⬝ᵥ e3) • e3) = 0 := by
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, dotProduct_sub,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, he3, hcomm] at hsq ⊢
      nlinarith [hsq]
    exact hp'
  have hp0 : (u - x) - ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u = 0 := by
    have h3 : ‖(u - x) - ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u‖ ^ 2 = 0 := by
      rw [norm_sq_eq_dot]; exact hp
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h3)
  have hux : u - x = ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u := sub_eq_zero.mp hp0
  have h2 : ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u =
      (((u - x) ⬝ᵥ e3Fan_p34 x v u) * ‖v - x‖⁻¹) • (v - x) := by
    rw [e3Fan_p34, smul_smul]
  exact hnc ((collinear3_iff_smul hvx).mpr
    ⟨((u - x) ⬝ᵥ e3Fan_p34 x v u) * ‖v - x‖⁻¹, by rw [← h2]; exact hux⟩)

private theorem e2Fan_dot_self_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e2Fan_p34 x v u ⬝ᵥ e2Fan_p34 x v u = 1 := by
  have hn : ‖cross3 (e3Fan_p34 x v u) (u - x)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (e3Fan_cross_ux_ne_zero_p34 hnc)
  rw [e2Fan_p34, coe_smul_p34, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← norm_sq_eq_dot, smul_eq_mul]
  have h2 : ‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ *
      (‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ * ‖cross3 (e3Fan_p34 x v u) (u - x)‖ ^ 2) = 1 := by
    field_simp [hn]
  exact h2

private theorem e2Fan_dot_e3_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e2Fan_p34 x v u ⬝ᵥ e3Fan_p34 x v u = 0 := by
  rw [e2Fan_p34, coe_smul_p34, smul_dotProduct,
    dotProduct_comm ((cross3 (e3Fan_p34 x v u) (u - x) : V3) : Fin 3 → ℝ)
      ((e3Fan_p34 x v u : V3) : Fin 3 → ℝ),
    cross3_dot_left_p34, smul_zero]

private theorem e1Fan_dot_self_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e1Fan_p34 x v u ⬝ᵥ e1Fan_p34 x v u = 1 := by
  have hvx : v ≠ x := ncol_vx_p34 hnc
  rw [e1Fan_p34, cross3_eq_p34, dot_toLp, coe_toLp, cross_dot_cross, dot_coe_p34,
    dot_coe_p34, dot_coe_p34, dot_coe_p34, e2Fan_dot_self_p34 hnc,
    e3Fan_dot_self_p34 hvx u,
    dotProduct_comm ((e3Fan_p34 x v u : V3) : Fin 3 → ℝ) ((e2Fan_p34 x v u : V3) : Fin 3 → ℝ),
    e2Fan_dot_e3_p34 hnc]
  ring

private theorem e1Fan_dot_e2_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e1Fan_p34 x v u ⬝ᵥ e2Fan_p34 x v u = 0 := by
  rw [e1Fan_p34,
    dotProduct_comm ((cross3 (e2Fan_p34 x v u) (e3Fan_p34 x v u) : V3) : Fin 3 → ℝ)
      ((e2Fan_p34 x v u : V3) : Fin 3 → ℝ)]
  exact cross3_dot_left_p34 _ _

private theorem e1Fan_dot_e3_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e1Fan_p34 x v u ⬝ᵥ e3Fan_p34 x v u = 0 := by
  rw [e1Fan_p34,
    dotProduct_comm ((cross3 (e2Fan_p34 x v u) (e3Fan_p34 x v u) : V3) : Fin 3 → ℝ)
      ((e3Fan_p34 x v u : V3) : Fin 3 → ℝ)]
  exact cross3_dot_right_p34 _ _

private theorem dot_e2Fan_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    (u - x) ⬝ᵥ e2Fan_p34 x v u = 0 := by
  rw [e2Fan_p34, coe_smul_p34, dotProduct_smul, cross3_dot_right_p34, smul_zero]

private theorem vdot_e2Fan_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    (v - x) ⬝ᵥ e2Fan_p34 x v u = 0 := by
  rw [e2Fan_p34, coe_smul_p34, dotProduct_smul, e3Fan_p34, cross3_smul_left_p34, coe_smul_p34,
    dotProduct_smul, cross3_dot_left_p34, smul_zero, smul_zero]

private theorem e1Fan_eq_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e1Fan_p34 x v u = ‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ •
      ((u - x) - ((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u) := by
  have hvx : v ≠ x := ncol_vx_p34 hnc
  rw [e1Fan_p34, e2Fan_p34, cross3_smul_left_p34, cross3, cross3, dot_toLp, coe_toLp,
    cross_cross_eq_smul_sub_smul, dot_coe_p34, dot_coe_p34,
    e3Fan_dot_self_p34 hvx u, one_smul]
  try simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_neg, WithLp.ofLp_zero, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_neg, WithLp.toLp_zero,
    WithLp.toLp_smul, WithLp.toLp_ofLp, sub_zero, add_zero, zero_add, inner_eq_dot, norm_sq_eq_dot]

private theorem udot_e1Fan_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    0 < (u - x) ⬝ᵥ e1Fan_p34 x v u := by
  have hvx : v ≠ x := ncol_vx_p34 hnc
  have hn : 0 < ‖cross3 (e3Fan_p34 x v u) (u - x)‖ :=
    norm_pos_iff.mpr (e3Fan_cross_ux_ne_zero_p34 hnc)
  have h1 : (u - x) ⬝ᵥ e1Fan_p34 x v u = ‖cross3 (e3Fan_p34 x v u) (u - x)‖ := by
    rw [e1Fan_eq_p34 hnc, coe_smul_p34, dotProduct_smul,
      coe_sub_p34 (u - x) (((u - x) ⬝ᵥ e3Fan_p34 x v u) • e3Fan_p34 x v u), coe_smul_p34,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hsq : (u - x) ⬝ᵥ (u - x) - ((u - x) ⬝ᵥ e3Fan_p34 x v u) *
        ((u - x) ⬝ᵥ e3Fan_p34 x v u) =
        cross3 (e3Fan_p34 x v u) (u - x) ⬝ᵥ cross3 (e3Fan_p34 x v u) (u - x) := by
      rw [cross3_eq_p34, dot_toLp, coe_toLp, cross_dot_cross, dot_coe_p34, dot_coe_p34,
        dot_coe_p34, dot_coe_p34, e3Fan_dot_self_p34 hvx u,
        dotProduct_comm ((u - x : V3) : Fin 3 → ℝ) ((e3Fan_p34 x v u : V3) : Fin 3 → ℝ)]
      simp only [coe_sub_p34]
      ring
    simp only [coe_sub_p34, smul_eq_mul] at hsq ⊢
    rw [hsq, ← norm_sq_eq_dot]
    have h2 : ‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ * ‖cross3 (e3Fan_p34 x v u) (u - x)‖ ^ 2 =
        ‖cross3 (e3Fan_p34 x v u) (u - x)‖ := by
      field_simp [ne_of_gt hn]
    exact h2
  rw [h1]
  exact hn

private theorem vdot_e1Fan_p34 (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    (v - x) ⬝ᵥ e1Fan_p34 x v u = 0 := by
  rw [e1Fan_p34, cross3_eq_p34, dotProduct_comm, dot_toLp, dotProduct_comm,
    triple_product_permutation, e3Fan_p34, coe_smul_p34, crossProduct_smul_left_p34,
    cross_self, smul_zero, dotProduct_zero]

/-! ### Strict Gram positivity and the spanning helper. -/

private theorem gram_pos_p34 {A B : V3} (hncAB : ¬ Collinear ℝ ({0, A, B} : Set V3)) :
    (0:ℝ) < (A ⬝ᵥ A) * (B ⬝ᵥ B) - (A ⬝ᵥ B) * (B ⬝ᵥ A) := by
  obtain ⟨h1, h2⟩ := nc_norm_pos_p34 hncAB
  have hdc : B ⬝ᵥ A = A ⬝ᵥ B := dotProduct_comm _ _
  have hcs : |A ⬝ᵥ B| < ‖A‖ * ‖B‖ := by
    rw [← inner_eq_dot]
    rcases lt_or_eq_of_le (abs_real_inner_le_norm A B) with h | h
    · exact h
    · exfalso
      rw [← Real.norm_eq_abs] at h
      obtain ⟨r, -, hr⟩ :=
        (norm_inner_eq_norm_iff (𝕜 := ℝ) (norm_pos_iff.mp h1) (norm_pos_iff.mp h2)).mp h
      exact absurd hr (nc_not_smul_p34 hncAB r)
  have hsq : (A ⬝ᵥ B) ^ 2 < (A ⬝ᵥ A) * (B ⬝ᵥ B) := by
    have h2v : (‖A‖ * ‖B‖) ^ 2 = (A ⬝ᵥ A) * (B ⬝ᵥ B) := by
      have e1 : (‖A‖ * ‖B‖) ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 := by rw [sq]; ring
      rw [e1, ← norm_sq_eq_dot, ← norm_sq_eq_dot]
    have hd2' : (A ⬝ᵥ B) ^ 2 = |A ⬝ᵥ B| ^ 2 := (sq_abs _).symm
    have hneg : -(‖A‖ * ‖B‖) < |A ⬝ᵥ B| := by
      linarith [hcs, abs_nonneg (A ⬝ᵥ B)]
    rw [hd2', ← h2v]
    exact sq_lt_sq' hneg hcs
  rw [hdc]
  linarith

private theorem cross3_ne_zero_p34 {a b : V3} (hncAB : ¬ Collinear ℝ ({0, a, b} : Set V3)) :
    cross3 a b ≠ 0 := by
  intro h
  have hgram := gram_pos_p34 hncAB
  have hdot : cross3 a b ⬝ᵥ cross3 a b = (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) * (b ⬝ᵥ a) :=
    cross3_dot_self_p34 a b
  rw [h, coe_zero_p34, zero_dotProduct] at hdot
  linarith [hdot, hgram]

/-- Spanning: a vector orthogonal to `cross3 A B` lies in `span {A, B}`
(non-collinear case). -/
private theorem mem_span_AB_of_dot_cross_p34 {A B p : V3}
    (hncAB : ¬ Collinear ℝ ({0, A, B} : Set V3))
    (hp : p ⬝ᵥ cross3 A B = 0) :
    p ∈ Submodule.span ℝ ({A, B} : Set V3) := by
  obtain ⟨h1, h2⟩ := nc_norm_pos_p34 hncAB
  have hba : B ⬝ᵥ A = A ⬝ᵥ B := dotProduct_comm _ _
  have hgram := gram_pos_p34 hncAB
  rw [hba] at hgram
  have hBB : (0:ℝ) < B ⬝ᵥ B := by
    have h := pow_pos h2 2
    rwa [norm_sq_eq_dot] at h
  have hN := cross3_dot_self_p34 A B
  rw [hba] at hN
  have hli : LinearIndependent ℝ ![A, B, cross3 A B] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    have hd : ∀ e : V3, (g 0 • A + g 1 • B + g 2 • cross3 A B) ⬝ᵥ e = 0 := by
      intro e
      rw [hg]
      exact zero_dotProduct (e : Fin 3 → ℝ)
    -- the N-coefficient dies against the Gram determinant
    have hNdot := hd (cross3 A B)
    rw [add_dot_p34, add_dot_p34, smul_dot_p34, smul_dot_p34, smul_dot_p34,
      cross3_dot_left_p34, cross3_dot_right_p34, hN] at hNdot
    simp only [mul_zero, zero_add, add_zero] at hNdot
    have hg2 : g 2 = 0 := by
      rcases mul_eq_zero.mp hNdot with h | h
      · exact h
      · rw [h] at hgram; norm_num at hgram
    have hd0 := hd
    rw [hg2, zero_smul, add_zero] at hd0
    have hA : g 0 * (A ⬝ᵥ A) + g 1 * (A ⬝ᵥ B) = 0 := by
      have hA0 := hd0 A
      rw [add_dot_p34, smul_dot_p34, smul_dot_p34, hba] at hA0
      exact hA0
    have hB : g 0 * (A ⬝ᵥ B) + g 1 * (B ⬝ᵥ B) = 0 := by
      have hB0 := hd0 B
      rw [add_dot_p34, smul_dot_p34, smul_dot_p34] at hB0
      exact hB0
    have hcomb : (g 0 * (A ⬝ᵥ A) + g 1 * (A ⬝ᵥ B)) * (B ⬝ᵥ B)
        - (g 0 * (A ⬝ᵥ B) + g 1 * (B ⬝ᵥ B)) * (A ⬝ᵥ B)
        = g 0 * ((A ⬝ᵥ A) * (B ⬝ᵥ B) - (A ⬝ᵥ B) * (A ⬝ᵥ B)) := by
      ring
    have hg0 : g 0 = 0 := by
      have h2c := hcomb
      rw [hA, hB, zero_mul, zero_mul, sub_self] at h2c
      rcases mul_eq_zero.mp h2c.symm with h | h
      · exact h
      · rw [h] at hgram; norm_num at hgram
    have hg1 : g 1 = 0 := by
      rw [hg0, zero_mul, zero_add] at hB
      rcases mul_eq_zero.mp hB with h | h
      · exact h
      · rw [h] at hBB; norm_num at hBB
    fin_cases j
    · exact hg0
    · exact hg1
    · exact hg2
  have hspan : Submodule.span ℝ (Set.range ![A, B, cross3 A B]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace])
  have hmem : p ∈ Submodule.span ℝ (Set.range ![A, B, cross3 A B]) :=
    hspan.symm ▸ Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hp' : p = c 0 • A + c 1 • B + c 2 • cross3 A B := by
    rw [← hc, Finsupp.sum,
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_smul])]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  -- the expansion dotted with N kills the A- and B-coefficients
  rw [hp'] at hp
  rw [add_dot_p34, add_dot_p34, smul_dot_p34, smul_dot_p34, smul_dot_p34,
    cross3_dot_left_p34, cross3_dot_right_p34, hN] at hp
  simp only [mul_zero, zero_add, add_zero] at hp
  rcases mul_eq_zero.mp hp with h | h
  · rw [hp', h, zero_smul, add_zero]
    exact Submodule.mem_span_pair.mpr ⟨c 0, c 1, rfl⟩
  · rw [h] at hgram; norm_num at hgram

/-! ### affineSpan triple characterisation. -/

private theorem mem_affSpan3_iff_p34 {x v u z : V3} :
    z ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) ↔
      z - x ∈ Submodule.span ℝ ({v - x, u - x} : Set V3) := by
  have hx : x ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) :=
    mem_affineSpan _ (Set.mem_insert _ _)
  have hv : v ∈ ({x, v, u} : Set V3) := by simp
  have hdir : (affineSpan ℝ ({x, v, u} : Set V3)).direction =
      Submodule.span ℝ ({v - x, u - x} : Set V3) := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_left (k := ℝ) hv]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro d ⟨w, hw, he⟩
      subst he
      simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_neg, WithLp.ofLp_zero, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_neg, WithLp.toLp_zero,
    WithLp.toLp_smul, WithLp.toLp_ofLp, sub_zero, add_zero, zero_add, inner_eq_dot, norm_sq_eq_dot] at *
      rcases Set.mem_insert_iff.mp hw with he1 | hw'
      · rw [he1, vsub_eq_sub]
        exact Submodule.subset_span (by simp)
      · rcases Set.mem_insert_iff.mp hw' with he2 | hw''
        · rw [he2, vsub_self]
          exact Submodule.zero_mem _
        · rcases Set.mem_singleton_iff.mp hw'' with he3
          rw [he3, vsub_eq_sub, show (v : V3) - u = (v - x) - (u - x) from by module]
          exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro d hd
      rcases Set.mem_insert_iff.mp hd with he | hd'
      · rw [he]
        exact Submodule.subset_span (by simp)
      · rw [Set.mem_singleton_iff] at hd'
        rw [hd']
        rw [show (u : V3) - x = (v - x) - (v - u) from by module]
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
  constructor
  · intro hz
    have hd : z - x ∈ (affineSpan ℝ ({x, v, u} : Set V3)).direction :=
      AffineSubspace.vsub_mem_direction hz hx
    rwa [hdir] at hd
  · intro hspan
    have hd : z - x ∈ (affineSpan ℝ ({x, v, u} : Set V3)).direction := by
      rw [hdir]; exact hspan
    have hm := (AffineSubspace.vadd_mem_iff_mem_direction (v := z - x) hx).mpr hd
    simpa using hm

/-! ### affGt {0} {x, y} pair characterisation. -/

private theorem affGt_zero_pair_char_p34 {x y w : V3}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    w ∈ affGt {0} {x, y} ↔ ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ β • x + γ • y = w := by
  have hx0 : (0:V3) ≠ x := Ne.symm hx
  have hy0 : (0:V3) ≠ y := Ne.symm hy
  have hfin : (({0} : Set V3) ∪ {x, y} : Set V3).Finite := by simp
  have hset : ({0} ∪ {x, y} : Set V3) = ({0, x, y} : Set V3) := by
    ext q; simp; tauto
  have h4 : hfin.toFinset = ({0, x, y} : Finset V3) := by
    ext q
    rw [Set.Finite.mem_toFinset, hset]
    simp
  have hsum3 : ∀ (F : V3 → ℝ), (∑ q ∈ ({0, x, y} : Finset V3), F q) = F 0 + (F x + F y) := by
    intro F
    rw [Finset.sum_insert (by simp [hx0, hy0]), Finset.sum_insert (by simp [hxy]),
      Finset.sum_singleton]
  have hsum3v : ∀ (F : V3 → ℝ), (∑ q ∈ ({0, x, y} : Finset V3), F q • q)
      = F 0 • 0 + (F x • x + F y • y) := by
    intro F
    rw [Finset.sum_insert (by simp [hx0, hy0]), Finset.sum_insert (by simp [hxy]),
      Finset.sum_singleton]
  constructor
  · rintro ⟨f, g, hsum, hpos, hone⟩
    rw [h4, hsum3v] at hsum
    simp only [smul_zero, zero_add] at hsum
    exact ⟨f x, f y, hpos x (by simp), hpos y (by simp), hsum.symm⟩
  · rintro ⟨β, γ, hβ, hγ, hw⟩
    have hF0 : ((if (0:V3) = x then β else if (0:V3) = y then γ else 1 - β - γ):ℝ)
        = 1 - β - γ := by simp [hx0, hy0]
    have hFx : ((if (x:V3) = x then β else if (x:V3) = y then γ else 1 - β - γ):ℝ) = β := by
      simp
    have hFy : ((if (y:V3) = x then β else if (y:V3) = y then γ else 1 - β - γ):ℝ) = γ := by
      simp [hxy.symm]

    refine ⟨fun p => if p = x then β else if p = y then γ else 1 - β - γ, hfin, ?_, ?_, ?_⟩
    · rw [h4, hsum3v, hF0, hFx, hFy]
      simp only [smul_zero, zero_add]
      rw [hw]
    · intro q hq
      rcases Set.mem_insert_iff.mp hq with he | he
      · rw [he]
        simpa using hβ
      · rw [he]
        simpa [hxy.symm] using hγ
    · rw [h4, hsum3, hF0, hFx, hFy]
      ring

private theorem norm_lt_of_sq_lt_p34 {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : c ^ 2 < a ^ 2) : c < a := by
  by_contra hle
  push_neg at hle
  exact absurd (sq_le_sq' (show -(c:ℝ) ≤ a from by linarith [ha, hc]) hle) (by linarith)

private theorem norm_le_of_sq_le_p34 {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : c ^ 2 ≤ a ^ 2) : c ≤ a := by
  by_contra hgt
  push_neg at hgt
  nlinarith [hgt, ha, hc, h]

/-- A point `w` within `z ⬝ vv / (2‖vv‖)` of `z` keeps the `vv`-dot positive
(radius form of continuity of `· ⬝ᵥ vv` at `z`). -/
private theorem dot_close_pos_p34 {w z vv : V3} (hvv : ‖vv‖ ≠ 0)
    (hz : (0:ℝ) < z ⬝ᵥ vv) (hwz : ‖w - z‖ < z ⬝ᵥ vv / (2 * ‖vv‖)) :
    (0:ℝ) < w ⬝ᵥ vv := by
  have hcs : |(w - z) ⬝ᵥ vv| ≤ ‖w - z‖ * ‖vv‖ := by
    rw [← inner_eq_dot]
    exact abs_real_inner_le_norm (w - z) vv
  have hkey : z ⬝ᵥ vv / (2 * ‖vv‖) * ‖vv‖ = z ⬝ᵥ vv / 2 := by
    field_simp [hvv]
  have hposvv : (0:ℝ) < ‖vv‖ := lt_of_le_of_ne (norm_nonneg vv) (Ne.symm hvv)
  have hlt : ‖w - z‖ * ‖vv‖ < z ⬝ᵥ vv / 2 := by
    have h2 := mul_lt_mul_of_pos_right hwz hposvv
    rwa [hkey] at h2
  have hwz' : (w - z) ⬝ᵥ vv = w ⬝ᵥ vv - z ⬝ᵥ vv :=
    sub_dotProduct (w : Fin 3 → ℝ) (z : Fin 3 → ℝ) (vv : Fin 3 → ℝ)
  have hlow : -(w ⬝ᵥ vv - z ⬝ᵥ vv) < z ⬝ᵥ vv / 2 := by
    have h1 : -(w ⬝ᵥ vv - z ⬝ᵥ vv) ≤ |(w - z) ⬝ᵥ vv| := by
      rw [hwz']
      have h0 := le_abs_self (-(w ⬝ᵥ vv - z ⬝ᵥ vv))
      rwa [abs_neg] at h0
    linarith [h1, hlt]
  have hnn := norm_nonneg vv
  linarith

/-! ### e2Fan as a smul of the cross product; orthogonality transfer. -/

private theorem e2Fan_eq_smul_cross_p34 {x v u : V3} (hvx : v ≠ x)
    (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) :
    e2Fan_p34 x v u = (‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ * ‖v - x‖⁻¹) •
      cross3 (v - x) (u - x) := by
  rw [e2Fan_p34, e3Fan_p34, cross3_smul_left_p34, smul_smul]

private theorem dot_cross_of_dot_e2_p34 {x v u p : V3} (hvx : v ≠ x)
    (hnc : ¬ Collinear ℝ ({x, v, u} : Set V3)) (hp : p ⬝ᵥ e2Fan_p34 x v u = 0) :
    p ⬝ᵥ cross3 (v - x) (u - x) = 0 := by
  rw [e2Fan_eq_smul_cross_p34 hvx hnc] at hp
  have ht : (‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ * ‖v - x‖⁻¹) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (e3Fan_cross_ux_ne_zero_p34 hnc)))
      (inv_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)))
  have hp' : (‖cross3 (e3Fan_p34 x v u) (u - x)‖⁻¹ * ‖v - x‖⁻¹) *
      (p ⬝ᵥ cross3 (v - x) (u - x)) = 0 := by
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_neg, WithLp.ofLp_zero, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_neg, WithLp.toLp_zero,
    WithLp.toLp_smul, WithLp.toLp_ofLp, sub_zero, add_zero, zero_add, inner_eq_dot, norm_sq_eq_dot] at *
    simpa only [dotProduct_smul, smul_eq_mul] using hp
  rcases mul_eq_zero.mp hp' with h | h
  · exact absurd h ht
  · exact h


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

  obtain ⟨e0, he0, hup⟩ := UPS_X_POS_SEG_p34 v1 w x1 x2 x6 hnc hx1 hx2 hx6 h2
  refine ⟨e0 / 2, by linarith [he0], ⟨by constructor <;> linarith [he0], ?_, ?_⟩⟩
  · intro v hv r hr
    by_cases hvw : v = w
    · show ContinuousAt (fun t => v3DeforV4_p34 a x1 x2 x6 v1 w v t) r
      simp only [v3DeforV4_p34, if_pos hvw]
      have hshift : ContinuousAt (fun t : ℝ => x2 - t) r :=
        continuousAt_const.sub continuousAt_id
      have hmem := hup r ⟨by linarith [hr.1, he0], by linarith [hr.2, he0]⟩
      have hmain : ContinuousAt (fun x3 => v3DeforV1_p17 a v1 w x1 x2 x6 x6 x3) (x2 - r) :=
        EYYPQDW_CONTINUOUS_AT_X_p17 a v1 w x1 x2 (x2 - r) x6 x6 x6 h1 h2
          (by linarith [hmem.2]) h6 h6 h6 hnc hx1 hx2 hx6 (by simp [ha]) hmem.1
      exact hmain.comp hshift
    · show ContinuousAt (fun t => v3DeforV4_p34 a x1 x2 x6 v1 w v t) r
      simp only [v3DeforV4_p34, if_neg hvw]
      exact continuousAt_const
  · intro v hv
    by_cases hvw : v = w
    · show v3DeforV4_p34 a x1 x2 x6 v1 w v 0 = v
      simp only [v3DeforV4_p34, if_pos hvw]
      rw [hvw]
      exact V3_DEFOR_ID_p34 v1 w x1 x2 x6 a h1 hnc hx1 hx2 hx6 ha
    · show v3DeforV4_p34 a x1 x2 x6 v1 w v 0 = v
      simp only [v3DeforV4_p34, if_neg hvw]

/-- HOL `V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION` (IMJXPHR.hl:279). -/
theorem V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION_p34 (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hball : v2 ∈ ballAnnulus) (hn : ‖v2‖ ≠ 2) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      v3DeforV4_p34 a x1 x2 x6 v1 v2 v2 t ∈ ballAnnulus := by

  unfold ballAnnulus at hball ⊢
  obtain ⟨hcl, hnb⟩ := hball
  have hd2 : dist v2 0 ≤ 2 * h0 := Metric.mem_closedBall.mp hcl
  have hnorm2 : ‖v2‖ ≤ 2 * h0 := by
    rwa [dist_eq_norm, sub_zero] at hd2
  have hge2 : ¬ (dist v2 0 < 2) := fun hmem => hnb hmem
  have hgt2 : (2:ℝ) < ‖v2‖ := by
    have h3 : (2:ℝ) ≤ ‖v2‖ := by
      have h3' : (2:ℝ) ≤ dist v2 0 := le_of_not_gt hge2
      rwa [dist_eq_norm, sub_zero] at h3'
    exact lt_of_le_of_ne h3 (Ne.symm hn)
  have hx4 : (4:ℝ) < x2 := by
    rw [← hx2]
    nlinarith [hgt2]
  obtain ⟨c0, hc0, hup⟩ := UPS_X_POS_SEG_C_p34 v1 v2 x1 x2 x6 ((x2 - 4) / 2)
    hnc hx1 hx2 hx6 h2 (by linarith [hx4])
  refine ⟨c0, hc0, fun t ht => ?_⟩
  obtain ⟨hups, hx2t, htlt⟩ :=
    hup t ⟨by linarith [ht.1, hc0], ht.2⟩
  have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
  have hnorm := EYYPQDW_NORMV3_p17 v1 v2 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t))
    x1 x2 (x2 - t) x6 x6 x6 a h1 h2 hx2t h6 h6 h6 hnc hx1 hx2 hx6 (by simp [ha]) hups hv3
  rw [v3DeforV4_p34, if_pos rfl]
  constructor
  · -- in the closed ball of radius 2 * h0
    refine Metric.mem_closedBall.mpr ?_
    rw [dist_eq_norm, sub_zero]
    apply norm_le_of_sq_le_p34 (by norm_num [h0]) (norm_nonneg _)
    have hx2le : ‖v2‖ ^ 2 ≤ (2 * h0) ^ 2 := by
      exact sq_le_sq' (by linarith [norm_nonneg v2]) hnorm2
    rw [hnorm]
    linarith
  · -- not in the open ball of radius 2
    intro hm
    rw [Metric.mem_ball] at hm
    rw [dist_eq_norm, sub_zero] at hm
    have h2t : (2:ℝ) * t < x2 - 4 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)] at htlt
      linarith [htlt, hc0]
    have hnorm4 : (2:ℝ) < ‖v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)‖ := by
      apply norm_lt_of_sq_lt_p34 (norm_nonneg _) (by norm_num)
      rw [hnorm]
      linarith
    linarith

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

  have hBB : BBsV39 s w := by
    have h := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h
    have h2 := h.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.1
  have hclf := BBS_IMP_CONVEX_LOCAL_FAN_p34 s k w hk hkk hBB
  obtain ⟨hlf, -⟩ := hclf
  obtain ⟨hfan, -, -, -, -, -⟩ := hlf
  obtain ⟨-, -, -, -, hfan6, -⟩ := hfan
  have hed : ({v2, v1} : Set V3) ∈
      Set.range (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) := by
    refine ⟨l, ?_⟩
    show ({w l, w (l + 1)} : Set V3) = ({v2, v1} : Set V3)
    rw [hl, hl1]
  have hncins := hfan6 ({v2, v1} : Set V3) hed
  have hnc' : ¬ Collinear ℝ ({0, v1, v2} : Set V3) := by
    intro hc
    apply hncins
    have hset : ({0, v2, v1} : Set V3) = ({0, v1, v2} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset]
  exact (NORM_POS_COLLINEAR_p34 v1 v2 x1 x2 x6 hnc' hx1 hx2 hx6).imp id
    (fun h => ⟨h.1, h.2, hnc'⟩)

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
  intro j hj1 hj2
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w j) x1 x2 x6 a (s.a l j) h1 h2 h6 hnc
    hx1 hx2 hx6 ha (hbound j hj1 hj2)

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
  intro j hj1 hj2
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w j) x1 x2 x6 a (s.a l j) h1 h2 h6 hnc
    hx1 hx2 hx6 ha (hbound j hj1 hj2)

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

/-- Early copy of the `MMs` -> `BBs` extraction (the later `mms_bbs_p34`
lives below the `EDGE`/`BLL` block; this `w5cC3_` twin serves the W2/W3
distance proofs). -/
private theorem w5cC3_mms_bbs_p34 {s : ScsV39} {w : ℕ → V3} (hmw : w ∈ MMsV39 s) :
    BBsV39 s w := by
  have h := hmw
  simp only [MMsV39, Set.mem_setOf_eq] at h
  have h2 := h.1
  simp only [BBprime2V39, Set.mem_setOf_eq] at h2
  have h3 := h2.1
  simp only [BBprimeV39, Set.mem_setOf_eq] at h3
  exact h3.1

/-- Early copy of `mod_ne_succ_p34` (declared below the `EDGE`/`BLL` block). -/
private theorem w5cC3_mod_ne_succ_p34 {k l : ℕ} (hk : 2 ≤ k) : l % k ≠ (l + 1) % k := by
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
  intro i hdiag_i
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hBB := w5cC3_mms_bbs_p34 hmw
  have hv2 : v2 ∈ ballAnnulus := by
    have := hBB.1 (Set.mem_range.mpr ⟨l, rfl⟩)
    rwa [hl] at this
  have hwi : w i ∈ ballAnnulus := hBB.1 (Set.mem_range.mpr ⟨i, rfl⟩)
  have hdv : dist v2 0 ≤ 2 * h0 :=
    Metric.mem_closedBall.mp hv2.1
  have hdw : dist (w i) 0 ≤ 2 * h0 :=
    Metric.mem_closedBall.mp hwi.1
  have htri : dist v2 (w i) ≤ dist v2 0 + dist 0 (w i) := dist_triangle v2 0 (w i)
  have h4 : dist v2 (w i) ≤ 4 * h0 := by
    rw [dist_comm 0 (w i)] at htri
    linarith
  exact EXISTS_SMALL_LT_CONST_p34 v1 v2 (w i) x1 x2 x6 a (s.b l i)
    h1 h2 h6 hnc hx1 hx2 hx6 ha (lt_of_le_of_lt h4 (hdiag i hdiag_i))

/-- HOL `xrr_decreasing_lt` (IMJXPHR.hl:758). -/
theorem xrr_decreasing_lt_p34 (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
    (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2h : y2 ≤ 2 * h0) (hlt : y1 < y1') :
    xrr y1' y2 y6 < xrr y1 y2 y6 := by

  have hh0 : (0:ℝ) < 2 - h0 * h0 := by norm_num [h0]
  have h4 : (4:ℝ) ≤ y1 * y1' := by
    have hy1' : (2:ℝ) < y1' := lt_of_le_of_lt h1 hlt
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith [hy1']), sub_nonneg.mpr h1,
      sub_nonneg.mpr (le_of_lt hy1')]
  have hc : y2 * y2 - y6 * y6 < y1 * y1' := by
    have h2sq : y2 * y2 ≤ 4 * (h0 * h0) := by
      nlinarith [sq_nonneg (2 * h0 - y2), sq_nonneg (2 * h0 + y2)]
    have h6sq : (2:ℝ) * 2 ≤ y6 * y6 := by
      nlinarith [sq_nonneg (y6 - 2)]
    linarith
  have hkey : (0:ℝ) < (y1' * y1' + y2 * y2 - y6 * y6) / y1'
      - (y1 * y1 + y2 * y2 - y6 * y6) / y1 := by
    have hEq : (y1' * y1' + y2 * y2 - y6 * y6) / y1'
        - (y1 * y1 + y2 * y2 - y6 * y6) / y1
        = (y1' - y1) * ((y1 * y1' - (y2 * y2 - y6 * y6)) / (y1 * y1')) := by
      field_simp
      ring
    rw [hEq]
    exact mul_pos (by linarith [hlt]) (div_pos (by linarith [hc]) (by nlinarith))
  have hd : (0:ℝ) < (y1' * y1' + y2 * y2 - y6 * y6) / (2 * y1' * y2)
      - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2) := by
    have hEq : (y1' * y1' + y2 * y2 - y6 * y6) / (2 * y1' * y2)
        - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2)
        = ((y1' * y1' + y2 * y2 - y6 * y6) / y1'
            - (y1 * y1 + y2 * y2 - y6 * y6) / y1) / (2 * y2) := by
      field_simp
    rw [hEq]
    exact div_pos hkey (by linarith)
  simp only [xrr]
  linarith

/-- HOL `exp_aff_gt_by_dot` (IMJXPHR.hl:801). -/
theorem exp_aff_gt_by_dot_p34 (x v u : V3) (hnc : ¬Collinear ℝ {x, v, u}) :
    affGt {x, v} {u} = {w : V3 | (w - x) ⬝ᵥ e2Fan_p34 x v u = 0 ∧ 0 < (w - x) ⬝ᵥ e1Fan_p34 x v u} := by

  have hvx : v ≠ x := ncol_vx_p34 hnc
  have hux : u ≠ x := ncol_ux_p34 hnc
  have huv : u ≠ v := ncol_uv_p34 hnc
  ext w
  have hchar := affGt_pair_iff (v0 := x) (v1 := v) (x := u) (y := w) (Ne.symm hvx) hux huv
  rw [hchar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, h, hw⟩
    refine ⟨?_, ?_⟩
    · rw [hw]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, dot_e2Fan_p34 hnc, vdot_e2Fan_p34 hnc]
      ring
    · rw [hw]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, vdot_e1Fan_p34 hnc, zero_mul, mul_zero,
        add_zero]
      exact mul_pos hc (udot_e1Fan_p34 hnc)
  · rintro ⟨he2, he1p⟩
    have hNdot : (w - x) ⬝ᵥ cross3 (v - x) (u - x) = 0 :=
      dot_cross_of_dot_e2_p34 hvx hnc he2
    have hsp : (w - x) ∈ Submodule.span ℝ ({v - x, u - x} : Set V3) :=
      mem_span_AB_of_dot_cross_p34 (A := v - x) (B := u - x) (p := w - x)
        (fun hc => hnc ((ncol_shift_p34 hvx).mp hc)) hNdot
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hsp
    have hdot1 : (w - x) ⬝ᵥ e1Fan_p34 x v u = b * ((u - x) ⬝ᵥ e1Fan_p34 x v u) := by
      rw [← hab]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, vdot_e1Fan_p34 hnc, zero_mul, mul_zero,
        add_zero, zero_add]
    rw [hdot1] at he1p
    have hbpos : (0:ℝ) < b := by
      by_contra hbn
      push_neg at hbn
      nlinarith [mul_nonneg (le_of_lt (udot_e1Fan_p34 hnc)) (by linarith : (0:ℝ) ≤ -b)]
    exact ⟨b, hbpos, a, by rw [add_comm]; exact hab.symm⟩

/-- HOL `CROSS_LAGRANGE1` (IMJXPHR.hl:804; restated verbatim at :876). -/
theorem CROSS_LAGRANGE1_p34 (x y z : V3) :
    cross3 (cross3 x y) z = (x ⬝ᵥ z) • y - (y ⬝ᵥ z) • x := by
  rw [cross3, cross3, cross_cross_eq_smul_sub_smul]
  simp

/-- HOL `exp_aff_by_dot` (IMJXPHR.hl:872). -/
theorem exp_aff_by_dot_p34 (x v u : V3) (hnc : ¬Collinear ℝ {x, v, u}) :
    affineSpan ℝ ({x, v, u} : Set V3) = {w : V3 | (w - x) ⬝ᵥ e2Fan_p34 x v u = 0} := by

  have hvx : v ≠ x := ncol_vx_p34 hnc
  ext z
  rw [mem_affSpan3_iff_p34, Set.mem_setOf_eq]
  constructor
  · rw [Submodule.mem_span_pair]
    rintro ⟨a, b, hab⟩
    rw [← hab]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, dot_e2Fan_p34 hnc, vdot_e2Fan_p34 hnc]
    ring
  · intro hz
    exact mem_span_AB_of_dot_cross_p34 (fun hc => hnc ((ncol_shift_p34 hvx).mp hc))
      (dot_cross_of_dot_e2_p34 hvx hnc hz)

/-- HOL `IN_AFF_EQ_DOT_E2_FAN` (IMJXPHR.hl:940). -/
theorem IN_AFF_EQ_DOT_E2_FAN_p34 (x y z : V3) (hnc : ¬Collinear ℝ ({0, x, y} : Set V3)) :
    e2Fan_p34 0 x y ⬝ᵥ z = 0 ↔ z ∈ affineSpan ℝ ({0, x, y} : Set V3) := by

  have h1 := exp_aff_by_dot_p34 0 x y hnc
  have h2 : z ∈ (affineSpan ℝ ({0, x, y} : Set V3) : Set V3) ↔
      (z - (0 : V3)) ⬝ᵥ e2Fan_p34 0 x y = 0 := by
    rw [h1]
    simp only [Set.mem_setOf_eq]
  have h3 : (e2Fan_p34 0 x y ⬝ᵥ z = 0) ↔
      ((z - (0 : V3)) ⬝ᵥ e2Fan_p34 0 x y = 0) := by
    rw [sub_zero]
    constructor
    · intro hz; rwa [dot_comm_p34] at hz
    · intro hz; rwa [dot_comm_p34]
  exact h3.trans h2.symm

/-- HOL `OPEN_RELA_AFF_GT` (IMJXPHR.hl:951). -/
theorem OPEN_RELA_AFF_GT_p34 (z x y : V3)
    (h1 : ¬Collinear ℝ ({0, z, x} : Set V3))
    (h2 : ¬Collinear ℝ ({0, x, y} : Set V3))
    (hz : z ∈ affGt {0} {x, y}) :
    ∃ e : ℝ, 0 < e ∧ Metric.ball z e ∩ affineSpan ℝ ({0, x, z} : Set V3) ⊆ affGt {0} {x, y} := by

  have hx0 : x ≠ 0 := ncol_vx_p34 (x := 0) (v := x) (u := y) h2
  have hy0 : y ≠ 0 := ncol_ux_p34 (x := 0) (v := x) (u := y) h2
  have hxy : x ≠ y := Ne.symm (ncol_uv_p34 (x := 0) (v := x) (u := y) h2)
  obtain ⟨β, γ, hβ, hγ, hzcoef⟩ :=
    (affGt_zero_pair_char_p34 hx0 hy0 hxy).mp hz
  have h2p : ({0, y, x} : Set V3) = ({0, x, y} : Set V3) := by ext q; simp; tauto
  have h2' : ¬ Collinear ℝ ({0, y, x} : Set V3) := fun hc => h2 (by rwa [h2p] at hc)
  have hxz1 : x ⬝ᵥ e1Fan_p34 0 x y = 0 := by
    have hh := vdot_e1Fan_p34 (x := (0:V3)) (v := x) (u := y) h2
    rwa [sub_zero] at hh
  have hyp : (0:ℝ) < y ⬝ᵥ e1Fan_p34 0 x y := by
    have hh := udot_e1Fan_p34 (x := (0:V3)) (v := x) (u := y) h2
    rwa [sub_zero] at hh
  have hyx1 : y ⬝ᵥ e1Fan_p34 0 y x = 0 := by
    have hh := vdot_e1Fan_p34 (x := (0:V3)) (v := y) (u := x) h2'
    rwa [sub_zero] at hh
  have hxp : (0:ℝ) < x ⬝ᵥ e1Fan_p34 0 y x := by
    have hh := udot_e1Fan_p34 (x := (0:V3)) (v := y) (u := x) h2'
    rwa [sub_zero] at hh
  have hz1 : z ⬝ᵥ e1Fan_p34 0 x y = γ * (y ⬝ᵥ e1Fan_p34 0 x y) := by
    rw [← hzcoef]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hxz1]
    ring
  have hz1p : (0:ℝ) < z ⬝ᵥ e1Fan_p34 0 x y := by rw [hz1]; exact mul_pos hγ hyp
  have hz1' : z ⬝ᵥ e1Fan_p34 0 y x = β * (x ⬝ᵥ e1Fan_p34 0 y x) := by
    rw [← hzcoef]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hyx1]
    ring
  have hz1'p : (0:ℝ) < z ⬝ᵥ e1Fan_p34 0 y x := by rw [hz1']; exact mul_pos hβ hxp
  have hne1 : ‖e1Fan_p34 0 x y‖ ≠ 0 := by
    intro h0
    have hzero : e1Fan_p34 0 x y = 0 := norm_eq_zero.mp h0
    simpa [hzero] using hz1p
  have hne1' : ‖e1Fan_p34 0 y x‖ ≠ 0 := by
    intro h0
    have hzero : e1Fan_p34 0 y x = 0 := norm_eq_zero.mp h0
    simpa [hzero] using hz1'p
  have hn2e1 : (0:ℝ) < 2 * ‖e1Fan_p34 0 x y‖ := by
    have hnn := norm_nonneg (e1Fan_p34 0 x y)
    have hpos : (0:ℝ) < ‖e1Fan_p34 0 x y‖ := lt_of_le_of_ne hnn (Ne.symm hne1)
    linarith
  have hn2e1' : (0:ℝ) < 2 * ‖e1Fan_p34 0 y x‖ := by
    have hnn := norm_nonneg (e1Fan_p34 0 y x)
    have hpos : (0:ℝ) < ‖e1Fan_p34 0 y x‖ := lt_of_le_of_ne hnn (Ne.symm hne1')
    linarith
  refine ⟨min (z ⬝ᵥ e1Fan_p34 0 x y / (2 * ‖e1Fan_p34 0 x y‖))
      (z ⬝ᵥ e1Fan_p34 0 y x / (2 * ‖e1Fan_p34 0 y x‖)),
    lt_min (div_pos hz1p hn2e1) (div_pos hz1'p hn2e1'), ?_⟩
  intro q hq
  obtain ⟨hball, haff⟩ := hq
  have hspan := (mem_affSpan3_iff_p34 (x := (0:V3)) (v := x) (u := z)).mp haff
  simp only [sub_zero] at hspan
  obtain ⟨b, c, hbc⟩ := Submodule.mem_span_pair.mp hspan
  have hcz : c • z = (c * β) • x + (c * γ) • y := by rw [← hzcoef]; module
  have hd : ‖q - z‖ < min (z ⬝ᵥ e1Fan_p34 0 x y / (2 * ‖e1Fan_p34 0 x y‖))
      (z ⬝ᵥ e1Fan_p34 0 y x / (2 * ‖e1Fan_p34 0 y x‖)) := by
    rw [Metric.mem_ball] at hball
    rwa [dist_eq_norm] at hball
  have hd1 : ‖q - z‖ < z ⬝ᵥ e1Fan_p34 0 x y / (2 * ‖e1Fan_p34 0 x y‖) :=
    lt_of_lt_of_le hd (min_le_left _ _)
  have hd1' : ‖q - z‖ < z ⬝ᵥ e1Fan_p34 0 y x / (2 * ‖e1Fan_p34 0 y x‖) :=
    lt_of_lt_of_le hd (min_le_right _ _)
  have hq1p : (0:ℝ) < q ⬝ᵥ e1Fan_p34 0 x y :=
    dot_close_pos_p34 hne1 hz1p hd1
  have hq1'p : (0:ℝ) < q ⬝ᵥ e1Fan_p34 0 y x :=
    dot_close_pos_p34 hne1' hz1'p hd1'
  have hq1 : q ⬝ᵥ e1Fan_p34 0 x y = c * (z ⬝ᵥ e1Fan_p34 0 x y) := by
    rw [← hbc, hcz]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hxz1, hz1]
    ring
  have hq1' : q ⬝ᵥ e1Fan_p34 0 y x = (b + c * β) * (x ⬝ᵥ e1Fan_p34 0 y x) := by
    rw [← hbc, hcz]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hyx1, hz1']
    ring
  have hcpos : (0:ℝ) < c := by
    by_contra hcn
    push_neg at hcn
    have hprod : c * (z ⬝ᵥ e1Fan_p34 0 x y) ≤ 0 := by
      nlinarith [mul_nonneg (le_of_lt hz1p) (by linarith : (0:ℝ) ≤ -c)]
    linarith [hq1, hprod, hq1p]
  have hbcpos : (0:ℝ) < b + c * β := by
    by_contra hcn
    push_neg at hcn
    have hprod : (b + c * β) * (x ⬝ᵥ e1Fan_p34 0 y x) ≤ 0 := by
      nlinarith [mul_nonneg (le_of_lt hxp) (by linarith : (0:ℝ) ≤ -(b + c * β))]
    linarith [hq1', hprod, hq1'p]
  have hqcoef : (b + c * β) • x + (c * γ) • y = q := by
    rw [← hbc, hcz]; module
  exact ((affGt_zero_pair_char_p34 hx0 hy0 hxy).mpr
    ⟨b + c * β, c * γ, hbcpos, mul_pos hcpos hγ, hqcoef⟩)

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

  have hncperm : ¬ Collinear ℝ ({0, v2, v1} : Set V3) := by
    intro hc
    have hset : ({0, v2, v1} : Set V3) = ({0, v1, v2} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset] at hc
    exact hnc hc
  obtain ⟨e', he', hsub⟩ := OPEN_RELA_AFF_GT_p34 v2 v1 w hncperm hnc2 hv2
  obtain ⟨e'', he'', hdist⟩ := EXISTS_SMALL_LT_CONST_p34 v1 v2 v2 x1 x2 x6 a e' h1 h2 h6
    hnc hx1 hx2 hx6 ha (by rw [dist_self]; linarith)
  refine ⟨min e' e'', lt_min he' he'', fun t ht => ?_⟩
  have ht2 : t < e'' := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have hdist'' : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 < e' :=
    hdist t ⟨ht.1, ht2⟩
  have hballmem : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ∈ Metric.ball v2 e' :=
    Metric.mem_ball.mpr hdist''
  have hd1 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have hcross : cross3 v1 (cross3 v1 v2) = (v1 ⬝ᵥ v2) • v1 - x1 • v2 := by
    rw [cross3, cross3, cross_cross_eq_smul_sub_smul', hd1]
    simp
  have hcombo : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
      = ((x1 + (x2 - t) - x6) / (2 * x1)) • v1
        + ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
          ((v1 ⬝ᵥ v2) • v1 - x1 • v2) := by
    simp only [v3DeforV1_p17]
    rw [hcross]
  have haffmem : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
      ∈ (affineSpan ℝ ({0, v1, v2} : Set V3) : Set V3) := by
    rw [mem_affSpan3_iff_p34, sub_zero]
    rw [Submodule.mem_span_pair]
    refine ⟨((x1 + (x2 - t) - x6) / (2 * x1)) +
        ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) * (v1 ⬝ᵥ v2),
      -(((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) * x1), ?_⟩
    rw [hcombo]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_neg, WithLp.ofLp_zero, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_neg, WithLp.toLp_zero,
    WithLp.toLp_smul, WithLp.toLp_ofLp, sub_zero, add_zero, zero_add, inner_eq_dot, norm_sq_eq_dot] at *
    module
  exact hsub ⟨hballmem, haffmem⟩

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

  have hncperm : ¬ Collinear ℝ ({0, v2, v1} : Set V3) := by
    intro hc
    have hset : ({0, v2, v1} : Set V3) = ({0, v1, v2} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset] at hc
    exact hnc hc
  obtain ⟨e', he', hsub⟩ := OPEN_RELA_AFF_GT_p34 v2 v1 w hncperm hnc2 hv2
  obtain ⟨e'', he'', hdist⟩ := EXISTS_SMALL_LT_CONST_V1_p34 v1 v2 v2 x1 x2 x6 a e' h1 h2 h6
    hnc hx1 hx2 hx6 ha (by rw [dist_self]; linarith)
  refine ⟨min e' e'' / 2, div_pos (lt_min he' he'') (by norm_num), fun t ht => ?_⟩
  have ht1 : -e'' < t := by linarith [ht.1, min_le_right e' e'', he'']
  have ht2 : t < e'' := by linarith [ht.2, min_le_right e' e'', he'']
  have hdist'' : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 < e' :=
    hdist t ⟨ht1, ht2⟩
  have hballmem : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ∈ Metric.ball v2 e' :=
    Metric.mem_ball.mpr hdist''
  have hd1 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have hcross : cross3 v1 (cross3 v1 v2) = (v1 ⬝ᵥ v2) • v1 - x1 • v2 := by
    rw [cross3, cross3, cross_cross_eq_smul_sub_smul', hd1]
    simp
  have hcombo : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
      = ((x1 + (x2 - t) - x6) / (2 * x1)) • v1
        + ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
          ((v1 ⬝ᵥ v2) • v1 - x1 • v2) := by
    simp only [v3DeforV1_p17]
    rw [hcross]
  have haffmem : v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
      ∈ (affineSpan ℝ ({0, v1, v2} : Set V3) : Set V3) := by
    rw [mem_affSpan3_iff_p34, sub_zero]
    rw [Submodule.mem_span_pair]
    refine ⟨((x1 + (x2 - t) - x6) / (2 * x1)) +
        ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) * (v1 ⬝ᵥ v2),
      -(((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) * x1), ?_⟩
    rw [hcombo]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_neg, WithLp.ofLp_zero, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_neg, WithLp.toLp_zero,
    WithLp.toLp_smul, WithLp.toLp_ofLp, sub_zero, add_zero, zero_add, inner_eq_dot, norm_sq_eq_dot] at *
    module
  exact hsub ⟨hballmem, haffmem⟩

/-- HOL `xrr_increasing_le` (IMJXPHR.hl:1130). -/
theorem xrr_increasing_le_p34 (y1 y2 y6 y6' : ℝ) (h1 : 0 < y1) (h2 : 0 < y2)
    (h6 : 0 ≤ y6) (h6' : y6 ≤ y6') :
    xrr y1 y2 y6 ≤ xrr y1 y2 y6' := by

  have hpos : (0:ℝ) < 2 * y1 * y2 := by nlinarith
  have hsq : y6 * y6 ≤ y6' * y6' := by
    nlinarith [sq_nonneg (y6' - y6), h6, h6']
  have hd : y1 * y1 + y2 * y2 - y6' * y6' ≤ y1 * y1 + y2 * y2 - y6 * y6 := by linarith
  have key : (y1 * y1 + y2 * y2 - y6' * y6') / (2 * y1 * y2)
      ≤ (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2) := by
    exact div_le_div_of_nonneg_right hd (by linarith)
  simp only [xrr]
  linarith

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
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hk0 : 0 < k := by omega
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  have hik : i % k < k := Nat.mod_lt _ hk0
  have hlk : l % k < k := Nat.mod_lt _ hk0
  have hne : i % k ≠ l % k := by
    intro h
    have hsucc : i % k ≠ (i + 1) % k := w5cC3_mod_ne_succ_p34 (by omega)
    exact hsucc (h.trans hmod)
  have h2res : 2 ≤ s.a (i % k) (l % k) :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % k) (l % k)
      ⟨by rw [hkk]; exact hik, by rw [hkk]; exact hlk, hne⟩
  have e1 : s.a l i = s.a l (i % k) := modFold_p34 hk0 (fun q => (hpa l q).2) i
  have e2 : s.a l (i % k) = s.a (i % k) l :=
    (hs.2.2.2.2.2.2.2.2.2.2.2.2.1 l (i % k)).1
  have e3 : s.a (i % k) l = s.a (i % k) (l % k) :=
    modFold_p34 hk0 (fun q => (hpa (i % k) q).2) l
  have h2le : 2 ≤ s.a l i := by rw [e1, e2, e3]; exact h2res
  exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w i) x1 x2 x6 a 2
    h1 h2 h6 hnc hx1 hx2 hx6 ha (by linarith)

private theorem w5cC4_suc_k_sub_p34 {k l i : ℕ} (h : l % k = (i + 1) % k) (hk : 1 < k) :
    (l + k - 1) % k = i % k := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h0k : 0 < k := by omega
    have hm : i % k < k := Nat.mod_lt _ h0k
    have h2 : i % k + 1 = k := by
      have h1 : (i + 1) % k = 0 := by simpa using h.symm
      rw [Nat.add_mod, Nat.mod_eq_of_lt hk] at h1
      rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h1; omega
      · have hsub : i % k + 1 - k < k := by omega
        have e : i % k + 1 = i % k + 1 - k + k := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hsub] at h1
        omega
    rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
    omega
  · have h' : ((l - 1) + 1) % k = (i + 1) % k := by rwa [Nat.sub_add_cancel hl]
    have h'' : (l - 1) % k = i % k :=
      Nat.ModEq.add_right_cancel' 1 h'
    have e1 : l + k - 1 = (l - 1) + k := by omega
    rw [e1, Nat.add_mod_right]
    exact h''

private theorem w5cC4_coe_cross3_p34 (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) = crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) :=
  coe_toLp _

private theorem w5cC4_dot_coe_p34 (a b : V3) :
    (a : Fin 3 → ℝ) ⬝ᵥ (b : Fin 3 → ℝ) = a ⬝ᵥ b := by
  rw [← dot_toLp, WithLp.toLp_ofLp]

private theorem w5cC4_cross3_lagrange_p34 (a b : V3) :
    cross3 a (cross3 a b) = (a ⬝ᵥ b) • a - (a ⬝ᵥ a) • b := by
  rw [cross3, w5cC4_coe_cross3_p34,
    cross_cross_eq_smul_sub_smul' (a : Fin 3 → ℝ) (a : Fin 3 → ℝ) (b : Fin 3 → ℝ),
    WithLp.toLp_sub, WithLp.toLp_smul, WithLp.toLp_smul, w5cC4_dot_coe_p34,
    w5cC4_dot_coe_p34, WithLp.toLp_ofLp, WithLp.toLp_ofLp]

private theorem w5cC4_normsq_smul_p34 (t : ℝ) (v : V3) : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem w5cC4_normsq_add_orth_p34 (t s : ℝ) (u w : V3) (hd : u ⬝ᵥ w = 0) :
    ‖t • u + s • w‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, inner_eq_dot, hd,
    w5cC4_normsq_smul_p34, w5cC4_normsq_smul_p34]
  ring

private theorem w5cC4_dot_add_left_p34 (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c := by
  simp only [WithLp.ofLp_add, add_dotProduct]

private theorem w5cC4_dot_add_right_p34 (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c := by
  simp only [WithLp.ofLp_add, dotProduct_add]

private theorem w5cC4_dot_sub_left_p34 (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c := by
  simp only [WithLp.ofLp_sub, sub_dotProduct]

private theorem w5cC4_dot_sub_right_p34 (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c := by
  simp only [WithLp.ofLp_sub, dotProduct_sub]

private theorem w5cC4_dot_smul_left_p34 (a b : V3) (r : ℝ) : (r • a) ⬝ᵥ b = r * (a ⬝ᵥ b) := by
  simp only [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]

private theorem w5cC4_dot_smul_right_p34 (a b : V3) (r : ℝ) : a ⬝ᵥ (r • b) = r * (a ⬝ᵥ b) := by
  simp only [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]

private theorem w5cC4_dot_comm_p34 (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem w5cC4_normsq_double_cross_p34 (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    ‖cross3 v1 (cross3 v1 v2)‖ ^ 2 = x1 * upsX x1 x2 x6 / 4 := by
  have h11 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have h22 : v2 ⬝ᵥ v2 = x2 := (norm_sq_eq_dot v2).symm.trans hx2
  have hups4 : upsX x1 x2 x6 = 4 * (x1 * x2 - (v1 ⬝ᵥ v2) ^ 2) := by
    have hd6 : x6 = x1 + x2 - 2 * (v1 ⬝ᵥ v2) := by
      have h6e : ‖v1 - v2‖ ^ 2 = ‖v1‖ ^ 2 - 2 * (v1 ⬝ᵥ v2) + ‖v2‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_eq_dot]
      rw [← hx6, h6e, hx1, hx2]; ring
    unfold upsX
    rw [hd6]
    ring
  have hC : cross3 v1 (cross3 v1 v2) = (v1 ⬝ᵥ v2) • v1 - x1 • v2 := by
    rw [w5cC4_cross3_lagrange_p34, h11]
  have hinner : inner ℝ ((v1 ⬝ᵥ v2) • v1) (x1 • v2) = (v1 ⬝ᵥ v2) * x1 * (v1 ⬝ᵥ v2) := by
    rw [real_inner_smul_left, real_inner_smul_right, inner_eq_dot]
    ring
  rw [hC, norm_sub_sq_real, w5cC4_normsq_smul_p34, w5cC4_normsq_smul_p34, hinner, hx1, hx2,
    hups4]
  ring

private theorem w5cC4_scsA_ge_two_p34 {s : ScsV39} {k : ℕ} (hk0 : 0 < k)
    (hkk : s.k = k) (hs : isScsV39 s) {i j : ℕ} (hij : i % k ≠ j % k) :
    2 ≤ s.a i j := by
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  have hsym : ∀ i j, s.a i j = s.a j i := fun i j =>
    (hs.2.2.2.2.2.2.2.2.2.2.2.2.1 i j).1
  have hper1 : ∀ i j, s.a (i + k) j = s.a i j := by
    intro i j
    rw [hsym (i + k) j, hsym i j]
    exact (hpa j i).2
  have e1 : s.a i j = s.a (i % k) j :=
    modFold_p34 hk0 (f := fun q => s.a q j) (fun q => hper1 q j) i
  have e2 : s.a (i % k) j = s.a (i % k) (j % k) :=
    modFold_p34 hk0 (f := fun q => s.a (i % k) q) (fun q => (hpa (i % k) q).2) j
  rw [e1, e2]
  exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % k) (j % k)
    ⟨by rw [hkk]; exact Nat.mod_lt _ hk0, by rw [hkk]; exact Nat.mod_lt _ hk0, hij⟩

private theorem w5cC4_sqrt_ratio_p34 (U U0 : ℝ) (hU : 0 ≤ U) (hU0 : 0 < U0) :
    (1 - Real.sqrt (U / U0)) ^ 2 * U0 ≤ (U0 - U) ^ 2 / U0 := by
  set r := Real.sqrt (U / U0) with hrdef
  have hr : r ^ 2 = U / U0 := Real.sq_sqrt (div_nonneg hU hU0.le)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hpos : (0:ℝ) < 1 + r := by linarith
  have hsq : (1 - r) * (1 + r) = (U0 - U) / U0 := by
    have h1 : (1 - r) * (1 + r) = 1 - r ^ 2 := by ring
    rw [h1, hr]
    field_simp
  have h2 : (U0 - U) = (1 - r) * (1 + r) * U0 := by
    rw [hsq]; field_simp
  have hkey : (1 - r) ^ 2 * U0 = (U0 - U) ^ 2 / (U0 * (1 + r) ^ 2) := by
    rw [h2]
    field_simp
  rw [hkey]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hU0 (by nlinarith [sq_nonneg r, hr0])

private theorem w5cC4_cone_cert_p34 {al be P Q X D1 D2 R2 : ℝ}
    (ha : 0 < al) (hb : 0 < be) (hs : al + be ≤ 1)
    (hP : P ≤ R2) (hQ : Q ≤ R2) (hX : 4 ≤ X) (hD1 : 4 ≤ D1) (hD2 : 4 < D2)
    (hR2 : R2 < 8)
    (hid : al * D1 + be * D2 = al * P + be * Q - (2 - (al + be)) * X) : False := by
  nlinarith [mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hP),
    mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hQ),
    mul_le_mul_of_nonneg_left hD1 (le_of_lt ha),
    mul_le_mul_of_nonneg_left (le_of_lt hD2) (le_of_lt hb),
    mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hX)]

private theorem w5cC4_norm_and_dot_p34 (v1 v2 : V3) (x1 x2 x6 t : ℝ)
    (h1 : 0 < x1) (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2)
    (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    ‖v2 - v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)‖ ^ 2
        = t ^ 2 / (4 * x1) + (1 - Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) ^ 2
            * upsX x1 x2 x6 / (4 * x1) ∧
      (v2 - v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) ⬝ᵥ v1 = t / 2 := by
  set C : V3 := cross3 v1 (cross3 v1 v2) with hC
  have hd1 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  have hlag : C = (v1 ⬝ᵥ v2) • v1 - x1 • v2 := by
    rw [hC, w5cC4_cross3_lagrange_p34, hd1]
  have horth : v1 ⬝ᵥ C = 0 := by
    rw [hlag]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hd1]
    ring
  have hcn2 : ‖C‖ ^ 2 = x1 * upsX x1 x2 x6 / 4 := by
    rw [hC]; exact w5cC4_normsq_double_cross_p34 v1 v2 x1 x2 x6 hx1 hx2 hx6
  have hm : x1 + x2 - x6 = 2 * (v1 ⬝ᵥ v2) := by
    have h6e : ‖v1 - v2‖ ^ 2 = ‖v1‖ ^ 2 - 2 * (v1 ⬝ᵥ v2) + ‖v2‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_eq_dot]
    rw [← hx6, h6e, hx1, hx2]; ring
  have hCsplit : (1 / x1) • C = ((v1 ⬝ᵥ v2) / x1) • v1 - v2 := by
    rw [hlag, smul_sub, smul_smul, smul_smul]
    have e1 : (1 / x1) * (v1 ⬝ᵥ v2) = (v1 ⬝ᵥ v2) / x1 := by ring
    have e2 : (1 / x1) * x1 = 1 := by field_simp
    rw [e1, e2, one_smul]
  have hdec : v2 = ((x1 + x2 - x6) / (2 * x1)) • v1 - (1 / x1) • C := by
    rw [hCsplit, hm]
    have e : (2 * (v1 ⬝ᵥ v2)) / (2 * x1) = (v1 ⬝ᵥ v2) / x1 := by
      field_simp
    rw [e]
    module
  have hv3def : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)
      = ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
        ((-1 / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) • C := by
    rw [hC]
    simp only [v3DeforV1_p17]
  have hvs : v2 - v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)
      = (t / (2 * x1)) • v1 +
        (-((1 - Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) / x1)) • C := by
    rw [hv3def, hdec]
    have ea : (x1 + x2 - x6) / (2 * x1) - (x1 + (x2 - t) - x6) / (2 * x1)
        = t / (2 * x1) := by
      field_simp; ring
    have eb : -(1 / x1) - (-1 / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)
        = -((1 - Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) / x1) := by
      field_simp; ring
    have hL : ((x1 + x2 - x6) / (2 * x1)) • v1 - (1 / x1) • C
        - (((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
            ((-1 / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) • C)
        = (((x1 + x2 - x6) / (2 * x1)) - ((x1 + (x2 - t) - x6) / (2 * x1))) • v1
          + (-(1 / x1) - ((-1 / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6))) • C := by
      module
    rw [hL, ea, eb]
  constructor
  · rw [hvs,
      w5cC4_normsq_add_orth_p34 (t / (2 * x1))
        (-((1 - Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) / x1)) v1 C horth,
      hx1, hcn2]
    field_simp [h1.ne']
    ring
  · rw [hvs, w5cC4_dot_add_left_p34, w5cC4_dot_smul_left_p34, w5cC4_dot_smul_left_p34,
      hd1, w5cC4_dot_comm_p34 C v1, horth]
    field_simp [h1.ne']
    ring

/-- The `(v2 - v3)·v2 = (t + ‖v2 - v3‖²)/2` identity, via the norm of `v3`. -/
private theorem w5cC4_u_dot_v2_p34 (v1 v2 v3 : V3) (x1 x2 x6 t : ℝ)
    (hx2 : ‖v2‖ ^ 2 = x2) (h3 : ‖v3‖ ^ 2 = x2 - t) :
    (v2 - v3) ⬝ᵥ v2 = (t + ‖v2 - v3‖ ^ 2) / 2 := by
  have hns : ‖v2 - v3‖ ^ 2 = ‖v2‖ ^ 2 - 2 * (v2 ⬝ᵥ v3) + ‖v3‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_eq_dot]
  have hdot : (v2 - v3) ⬝ᵥ v2 = ‖v2‖ ^ 2 - (v2 ⬝ᵥ v3) := by
    simp only [WithLp.ofLp_sub, sub_dotProduct,
      dotProduct_comm (v3 : Fin 3 → ℝ) (v2 : Fin 3 → ℝ)]
    rw [← norm_sq_eq_dot v2]
  rw [hdot]
  nlinarith [hns, hx2, h3]


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

  obtain ⟨h1, h2, h6, hnc0⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hk0 : 0 < k := by omega
  have hBB := w5cC3_mms_bbs_p34 hmw
  have hperw := MMs_periodic_p34 s k w hkk hmw
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  -- normalise the `l + (s.k - 1)` index
  have hnW : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hnc' : ¬Collinear ℝ ({0, v1, w (l + k - 1)} : Set V3) := by
    rw [← hl1, ← hnW]; exact hnc
  have haff' : w l ∈ affGt {0} ({v1, w (l + k - 1)} : Set V3) := by
    rw [← hl1, ← hnW]; exact haff
  -- distinctness from non-collinearity
  have hv1ne : v1 ≠ 0 := by
    intro hv
    apply hnc'
    rw [hv]
    simpa using collinear_pair ℝ (0 : V3) (w (l + k - 1))
  have hWne : w (l + k - 1) ≠ 0 := by
    intro hW
    apply hnc'
    rw [hW]
    have hpair : Collinear ℝ ({0, v1} : Set V3) := collinear_pair ℝ (0 : V3) v1
    convert hpair using 1
    ext x; simp [or_comm]
  have hv1W : v1 ≠ w (l + k - 1) := by
    intro hW
    apply hnc'
    rw [hW]
    simpa using collinear_pair ℝ (0 : V3) (w (l + k - 1))
  obtain ⟨α, β, hα, hβ, hcoef0⟩ :=
    (affGt_zero_pair_char_p34 hv1ne hWne hv1W).mp haff'
  have hcoef : α • v1 + β • w (l + k - 1) = v2 := by
    rw [← hl]; exact hcoef0
  -- i and l+k-1 agree
  have hWi : w i = w (l + k - 1) := by
    rw [modFold_p34 hk0 hperw i, ← w5cC4_suc_k_sub_p34 hmod (by omega),
      ← modFold_p34 hk0 hperw (l + k - 1)]
  have ha_lt' : s.a l (l + k - 1) < dist v2 (w (l + k - 1)) := by
    have e_a : s.a l i = s.a l (l + k - 1) := by
      rw [modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) i,
        ← w5cC4_suc_k_sub_p34 hmod (by omega),
        modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) (l + k - 1)]
    rw [← hWi, ← e_a]
    exact ha_lt
  -- cone certificate inputs
  have hPle : ‖v1‖ ^ 2 ≤ (2 * h0) ^ 2 := by
    have hv1mem : v1 ∈ ballAnnulus := by
      rw [← hl1]
      exact hBB.1 (Set.mem_range.mpr ⟨l + 1, rfl⟩)
    have hle : ‖v1‖ ≤ 2 * h0 := by
      have h' := Metric.mem_closedBall.mp hv1mem.1
      rwa [dist_zero_right] at h'
    have h0pos : (0:ℝ) < h0 := by unfold h0; norm_num
    nlinarith [norm_nonneg v1, hle, h0pos]
  have hQle : ‖w (l + k - 1)‖ ^ 2 ≤ (2 * h0) ^ 2 := by
    have hWmem : w (l + k - 1) ∈ ballAnnulus :=
      hBB.1 (Set.mem_range.mpr ⟨l + k - 1, rfl⟩)
    have hle : ‖w (l + k - 1)‖ ≤ 2 * h0 := by
      have h' := Metric.mem_closedBall.mp hWmem.1
      rwa [dist_zero_right] at h'
    have h0pos : (0:ℝ) < h0 := by unfold h0; norm_num
    nlinarith [norm_nonneg (w (l + k - 1)), hle, h0pos]
  have hXge : 4 ≤ ‖v2‖ ^ 2 := by
    have hv2mem : v2 ∈ ballAnnulus := by
      rw [← hl]
      exact hBB.1 (Set.mem_range.mpr ⟨l, rfl⟩)
    have h2le : 2 ≤ ‖v2‖ := by
      by_contra hlt
      push_neg at hlt
      exact hv2mem.2 (Metric.mem_ball.mpr (by rwa [dist_zero_right]))
    nlinarith
  have hD1ge : 4 ≤ ‖v2 - v1‖ ^ 2 := by
    have hdist : s.a l (l + 1) ≤ dist (w l) (w (l + 1)) := (hBB.2.2.1 l (l + 1)).1
    rw [hl, hl1] at hdist
    have h2a : 2 ≤ s.a l (l + 1) :=
      w5cC4_scsA_ge_two_p34 hk0 hkk hs (w5cC3_mod_ne_succ_p34 (by omega))
    have h2d : 2 ≤ dist v2 v1 := le_trans h2a hdist
    rw [dist_eq_norm] at h2d
    nlinarith
  have hD2gt : 4 < ‖v2 - w (l + k - 1)‖ ^ 2 := by
    have h2a : 2 ≤ s.a l (l + k - 1) := by
      have hne : l % k ≠ (l + k - 1) % k :=
        fun h => MOD_ADD_SUB_1_p34 (k := k) (l := l) (by omega) h.symm
      exact w5cC4_scsA_ge_two_p34 hk0 hkk hs hne
    have h2d : 2 < dist v2 (w (l + k - 1)) := lt_of_le_of_lt h2a ha_lt'
    rw [dist_eq_norm] at h2d
    nlinarith
  have hR2 : (2 * h0) ^ 2 < 8 := by unfold h0; norm_num
  have hs1 : 1 < α + β := by
    by_contra hle
    push_neg at hle
    have hP : ‖v1‖ ^ 2 ≤ (2 * h0) ^ 2 := hPle
    have hQ : ‖w (l + k - 1)‖ ^ 2 ≤ (2 * h0) ^ 2 := hQle
    have hX : 4 ≤ ‖v2‖ ^ 2 := hXge
    have hD1 : 4 ≤ ‖v2 - v1‖ ^ 2 := hD1ge
    have hD2 : 4 < ‖v2 - w (l + k - 1)‖ ^ 2 := hD2gt
    have hid : α * ‖v2 - v1‖ ^ 2 + β * ‖v2 - w (l + k - 1)‖ ^ 2
        = α * ‖v1‖ ^ 2 + β * ‖w (l + k - 1)‖ ^ 2 - (2 - (α + β)) * ‖v2‖ ^ 2 := by
      have hv2e : v2 = α • v1 + β • w (l + k - 1) := hcoef.symm
      have e1 : ‖v2 - v1‖ ^ 2 = ‖v2‖ ^ 2 - 2 * (v2 ⬝ᵥ v1) + ‖v1‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_eq_dot]
      have e2 : ‖v2 - w (l + k - 1)‖ ^ 2
          = ‖v2‖ ^ 2 - 2 * (v2 ⬝ᵥ w (l + k - 1)) + ‖w (l + k - 1)‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_eq_dot]
      have hXeq : ‖v2‖ ^ 2 = α * (v2 ⬝ᵥ v1) + β * (v2 ⬝ᵥ w (l + k - 1)) := by
        rw [norm_sq_eq_dot v2]
        nth_rewrite 1 [hv2e]
        rw [w5cC4_dot_add_left_p34, w5cC4_dot_smul_left_p34, w5cC4_dot_smul_left_p34,
          w5cC4_dot_comm_p34 v1 v2, w5cC4_dot_comm_p34 (w (l + k - 1)) v2]
      nlinarith [e1, e2, hXeq]
    exact w5cC4_cone_cert_p34 hα hβ hle hP hQ hX hD1 hD2 hR2 hid
  -- small-t construction
  obtain ⟨eU, heU, hU⟩ := UPS_X_POS_SEG_C_p34 v1 v2 x1 x2 x6 1 hnc0 hx1 hx2 hx6 h2 one_pos
  have hU0pos : 0 < upsX x1 x2 x6 := upsX_pos_nc_p34 hnc0 hx1 hx2 hx6
  set M : ℝ := x1 - (x1 + x2 - x6) / 2 with hM
  have hupsdiff : ∀ t : ℝ,
      upsX x1 x2 x6 - upsX x1 (x2 - t) x6 = 4 * M * t + t ^ 2 := by
    intro t
    rw [hM]
    unfold upsX
    ring
  set K : ℝ := 1 / (4 * x1) + (4 * |M| + 1) ^ 2 / (4 * x1 * upsX x1 x2 x6) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h4x1 : 0 < 4 * x1 := by linarith
    have hfirst : 0 < 1 / (4 * x1) := one_div_pos.mpr h4x1
    have hsecond : 0 ≤ (4 * |M| + 1) ^ 2 / (4 * x1 * upsX x1 x2 x6) := by positivity
    linarith
  have hs1pos : 0 < α + β - 1 := by linarith
  refine ⟨min eU (min 1 ((α + β - 1) / (2 * K))),
    lt_min heU (lt_min one_pos (div_pos hs1pos (by linarith))), ?_⟩
  intro t ht
  have htU : t < eU := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htinner : t < min 1 ((α + β - 1) / (2 * K)) :=
    lt_of_lt_of_le ht.2 (min_le_right _ _)
  have ht1 : t < 1 := lt_of_lt_of_le htinner (min_le_left _ _)
  have htE : t < (α + β - 1) / (2 * K) := lt_of_lt_of_le htinner (min_le_right _ _)
  obtain ⟨hupU, hx2t, -⟩ := hU t ⟨by linarith [ht.1], htU⟩
  set U : ℝ := upsX x1 (x2 - t) x6 with hUdef
  set U0 : ℝ := upsX x1 x2 x6 with hU0def
  set r : ℝ := Real.sqrt (U / U0) with hr
  have hU0pos' : 0 < U0 := hU0pos
  have hUpos : 0 < U := hupU
  have hsqrtle : (1 - r) ^ 2 * U0 ≤ (U0 - U) ^ 2 / U0 :=
    w5cC4_sqrt_ratio_p34 U U0 hUpos.le hU0pos'
  have hdiff : U0 - U = 4 * M * t + t ^ 2 := by
    simpa [hU0def, hUdef] using hupsdiff t
  have hdiffle : |U0 - U| ≤ (4 * |M| + 1) * t := by
    rw [hdiff]
    have ht0 : 0 ≤ t := ht.1.le
    have h1 : |4 * M * t + t ^ 2| ≤ 4 * |M| * t + t ^ 2 := by
      have e3 : |4 * M * t| = 4 * |M| * t := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0,
          abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num)]
      calc |4 * M * t + t ^ 2| ≤ |4 * M * t| + |t ^ 2| := abs_add_le _ _
        _ = 4 * |M| * t + t ^ 2 := by rw [e3, abs_of_nonneg (sq_nonneg t)]
    have h2 : 4 * |M| * t + t ^ 2 ≤ (4 * |M| + 1) * t := by nlinarith [ht0]
    linarith
  have hnormu : ‖v2 - v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)‖ ^ 2
      = t ^ 2 / (4 * x1) + (1 - r) ^ 2 * U0 / (4 * x1) := by
    have hmain := (w5cC4_norm_and_dot_p34 v1 v2 x1 x2 x6 t h1 hx1 hx2 hx6).1
    rw [← hUdef, ← hU0def, ← hr] at hmain
    rw [ha]
    exact hmain
  have hKbound : ‖v2 - v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)‖ ^ 2 ≤ t ^ 2 * K := by
    rw [hnormu]
    have h4x : (0:ℝ) ≤ 4 * x1 := by linarith
    have hstep1 : (1 - r) ^ 2 * U0 / (4 * x1) ≤ (U0 - U) ^ 2 / U0 / (4 * x1) :=
      div_le_div_of_nonneg_right hsqrtle h4x
    have hsq : (U0 - U) ^ 2 ≤ ((4 * |M| + 1) * t) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (U0 - U)) hdiffle 2
      rwa [sq_abs] at h
    have hstep2 : (U0 - U) ^ 2 / U0 / (4 * x1)
        ≤ ((4 * |M| + 1) * t) ^ 2 / U0 / (4 * x1) := by
      apply div_le_div_of_nonneg_right _ h4x
      exact div_le_div_of_nonneg_right hsq hU0pos'.le
    have hcollapse : ((4 * |M| + 1) * t) ^ 2 / U0 / (4 * x1)
        = t ^ 2 * ((4 * |M| + 1) ^ 2 / (4 * x1 * U0)) := by
      field_simp [h1.ne', hU0pos'.ne']
    calc t ^ 2 / (4 * x1) + (1 - r) ^ 2 * U0 / (4 * x1)
        ≤ t ^ 2 / (4 * x1) + (U0 - U) ^ 2 / U0 / (4 * x1) := by linarith
      _ ≤ t ^ 2 / (4 * x1) + ((4 * |M| + 1) * t) ^ 2 / U0 / (4 * x1) := by linarith
      _ = t ^ 2 * K := by rw [hK, hcollapse]; ring
  have htK : t ^ 2 * K < t * (α + β - 1) / 2 := by
    have htK' : t * K < (α + β - 1) / 2 := by
      calc t * K < ((α + β - 1) / (2 * K)) * K := mul_lt_mul_of_pos_right htE hKpos
        _ = (α + β - 1) / 2 := by field_simp [hKpos.ne']
    nlinarith [htK', ht.1]
  -- final comparison
  set v3 : V3 := v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) with hv3def
  have hnorm3 : ‖v3‖ ^ 2 = x2 - t := by
    rw [hv3def]
    have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
        ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
          cross3 v1 (cross3 v1 v2) = v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
    exact EYYPQDW_NORMV3_p17 v1 v2 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t))
      x1 x2 (x2 - t) x6 x6 x6 a h1 h2 hx2t h6 h6 h6 hnc0 hx1 hx2 hx6
      (by rw [ha]; norm_num) hupU hv3
  have hu_dot_v1 : (v2 - v3) ⬝ᵥ v1 = t / 2 := by
    rw [hv3def, ha]
    exact (w5cC4_norm_and_dot_p34 v1 v2 x1 x2 x6 t h1 hx1 hx2 hx6).2
  have hu_dot_v2 : (v2 - v3) ⬝ᵥ v2 = (t + ‖v2 - v3‖ ^ 2) / 2 :=
    w5cC4_u_dot_v2_p34 v1 v2 v3 x1 x2 x6 t hx2 hnorm3
  have hdotcoef : (v2 - v3) ⬝ᵥ v2
      = α * ((v2 - v3) ⬝ᵥ v1) + β * ((v2 - v3) ⬝ᵥ w (l + k - 1)) := by
    have hcoef_pi : ((α • v1 + β • w (l + k - 1) : V3) : Fin 3 → ℝ) = (v2 : Fin 3 → ℝ) := by
      rw [hcoef]
    have h1' : (v2 - v3) ⬝ᵥ (α • v1 + β • w (l + k - 1)) = (v2 - v3) ⬝ᵥ v2 :=
      congrArg (fun z : Fin 3 → ℝ => (v2 - v3 : V3) ⬝ᵥ z) hcoef_pi
    have h2' : (v2 - v3) ⬝ᵥ (α • v1 + β • w (l + k - 1))
        = α * ((v2 - v3) ⬝ᵥ v1) + β * ((v2 - v3) ⬝ᵥ w (l + k - 1)) := by
      rw [w5cC4_dot_add_right_p34, w5cC4_dot_smul_right_p34, w5cC4_dot_smul_right_p34]
    exact h1'.symm.trans h2'
  have huW : (v2 - v3) ⬝ᵥ w (l + k - 1)
      = ((v2 - v3) ⬝ᵥ v2 - α * ((v2 - v3) ⬝ᵥ v1)) / β := by
    rw [eq_div_iff hβ.ne']
    linarith [hdotcoef]
  have hkey : β * (‖v3 - w (l + k - 1)‖ ^ 2 - ‖v2 - w (l + k - 1)‖ ^ 2)
      = t * (1 - α - β) + ‖v2 - v3‖ ^ 2 := by
    have hnormexp : ‖v3 - w (l + k - 1)‖ ^ 2 - ‖v2 - w (l + k - 1)‖ ^ 2
        = -2 * ((v2 - v3) ⬝ᵥ (v2 - w (l + k - 1))) + ‖v2 - v3‖ ^ 2 := by
      have e1 : ‖v3 - w (l + k - 1)‖ ^ 2
          = ‖(v2 - w (l + k - 1)) - (v2 - v3)‖ ^ 2 := by
        rw [show v3 - w (l + k - 1) = (v2 - w (l + k - 1)) - (v2 - v3) by abel]
      have e2 : ‖(v2 - w (l + k - 1)) - (v2 - v3)‖ ^ 2
          = ‖v2 - w (l + k - 1)‖ ^ 2
            - 2 * ((v2 - v3) ⬝ᵥ (v2 - w (l + k - 1))) + ‖v2 - v3‖ ^ 2 := by
        rw [norm_sub_sq_real, real_inner_comm (v2 - v3) (v2 - w (l + k - 1)), inner_eq_dot]
        simp only [WithLp.ofLp_sub]
      rw [e1, e2]
      ring
    rw [hnormexp]
    have hdotW : (v2 - v3) ⬝ᵥ (v2 - w (l + k - 1))
        = (v2 - v3) ⬝ᵥ v2 - (v2 - v3) ⬝ᵥ w (l + k - 1) := by
      rw [w5cC4_dot_sub_right_p34]
    rw [hdotW, huW, hu_dot_v1, hu_dot_v2]
    field_simp [hβ.ne']
    ring
  have hsqlt : ‖v3 - w (l + k - 1)‖ ^ 2 < ‖v2 - w (l + k - 1)‖ ^ 2 := by
    have hneg : β * (‖v3 - w (l + k - 1)‖ ^ 2 - ‖v2 - w (l + k - 1)‖ ^ 2) < 0 := by
      rw [hkey]
      have hinner : t * (1 - α - β) + ‖v2 - v3‖ ^ 2 < 0 := by
        nlinarith [htK, hKbound, ht.1]
      exact hinner
    by_contra hge
    push_neg at hge
    have hnn : 0 ≤ ‖v3 - w (l + k - 1)‖ ^ 2 - ‖v2 - w (l + k - 1)‖ ^ 2 := by linarith
    exact absurd (mul_nonneg hβ.le hnn) (not_le.mpr hneg)
  have hlt_norm : ‖v3 - w (l + k - 1)‖ < ‖v2 - w (l + k - 1)‖ :=
    norm_lt_of_sq_lt_p34 (norm_nonneg _) (norm_nonneg _) hsqlt
  rw [hWi, dist_eq_norm, dist_eq_norm]
  exact hlt_norm

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

  obtain ⟨h1, h2, h6, hnc0⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hk0 : 0 < k := by omega
  have hBB := w5cC3_mms_bbs_p34 hmw
  have hperw := MMs_periodic_p34 s k w hkk hmw
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  have hpb : Periodic2 s.b k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.2.2.2.1
  intro i hi
  by_cases hA : l % k = (i + 1) % k
  · have e_w : w i = w (l + k - 1) := by
      rw [modFold_p34 hk0 hperw i, ← w5cC4_suc_k_sub_p34 hA (by omega),
        ← modFold_p34 hk0 hperw (l + k - 1)]
    have e_a : s.a l i = s.a l (l + k - 1) := by
      rw [modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) i,
        ← w5cC4_suc_k_sub_p34 hA (by omega),
        modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) (l + k - 1)]
    have ha_lt_i : s.a l i < dist v2 (w i) := by
      rw [e_a, e_w]; exact ha_lt
    obtain ⟨e, he, hedge⟩ := DEFORMATION_V3_DEFOR_EDGE_p34 s k l i w v1 v2 x1 x2 x6 a
      hk hkk hs hmw haz hnc haff hl hl1 hn ha_lt_i hx1 hx2 hx6 ha hA
    refine ⟨e, he, fun t ht => ?_⟩
    have hb : dist v2 (w i) ≤ s.b l i := by
      have h' := (hBB.2.2.1 l i).2
      rwa [hl] at h'
    exact le_of_lt (lt_of_lt_of_le (hedge t ht) hb)
  · by_cases hB : (l + 1) % k = i % k
    · have e_w : w i = v1 := by
        rw [modFold_p34 hk0 hperw i, ← hB, ← modFold_p34 hk0 hperw (l + 1), hl1]
      have e_b : s.b l i = s.b l (l + 1) := by
        rw [modFold_p34 hk0 (f := fun q => s.b l q) (fun q => (hpb l q).2) i, ← hB,
          modFold_p34 hk0 (f := fun q => s.b l q) (fun q => (hpb l q).2) (l + 1)]
      obtain ⟨eU, heU, hU⟩ := UPS_X_POS_SEG_p34 v1 v2 x1 x2 x6 hnc0 hx1 hx2 hx6 h2
      refine ⟨eU, heU, fun t ht => ?_⟩
      obtain ⟨hup, hx2t⟩ := hU t ⟨by linarith [ht.1], ht.2⟩
      have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
          ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
            cross3 v1 (cross3 v1 v2) = v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
      have hsq3 : ‖v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ ^ 2 = x6 :=
        EYYPQDW_NORM_V3_V1_p17 v1 v2 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t))
          x1 x2 (x2 - t) x6 x6 x6 a h1 h2 hx2t h6 h6 h6 hnc0 hx1 hx2 hx6
          (by rw [ha]; norm_num) hup hv3
      have heqn : ‖v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ = ‖v2 - v1‖ := by
        rw [← Real.sqrt_sq
            (norm_nonneg (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) - v1)),
          hsq3, ← hx6, Real.sqrt_sq (norm_nonneg (v1 - v2)), norm_sub_rev]
      have hdist : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) =
          dist v2 (w i) := by
        rw [e_w, dist_eq_norm, dist_eq_norm, heqn]
      rw [hdist, e_w, e_b]
      have h' := (hBB.2.2.1 l (l + 1)).2
      rwa [hl, hl1] at h'
    · have hd : scsDiag k l i := ⟨Ne.symm hi, hB, hA⟩
      obtain ⟨e, he, hlt⟩ := DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_p34 s k l w v1 v2 x1 x2 x6 a
        hkk hk hs hmw hl hl1 hx1 hx2 hx6 ha hdiag i hd
      exact ⟨e, he, fun t ht => le_of_lt (hlt t ht)⟩

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
  refine ⟨⟨hc, hd⟩, ?_, hfix⟩
  intro v hv r hr
  exact hcont v hv r ⟨lt_of_le_of_lt hac hr.1, lt_of_lt_of_le hr.2 hdb⟩

/-- Early copy of the `MMs` residue injectivity (the later `w_inj_p34`
lives below the `NOT_IN_V` block; this `w5cC2_` twin serves the W2 dist-le
proofs). -/
private theorem w5cC2_w_inj_p34 {s : ScsV39} {k : ℕ} {w : ℕ → V3} (hk : 3 < k)
    (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) :
    ∀ i j : ℕ, i % k ≠ j % k → w i ≠ w j := by
  have hk0 : 0 < k := by omega
  have hBB : BBsV39 s w := by
    have h := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h
    have h2 := h.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.1
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  intro i j hij hcon
  have h2le : 2 ≤ s.a (i % k) (j % k) :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % k) (j % k)
      ⟨by rw [hkk]; exact Nat.mod_lt _ hk0, by rw [hkk]; exact Nat.mod_lt _ hk0,
        fun hc => hij hc⟩
  have hperW : ∀ q, w (q + k) = w q := MMs_periodic_p34 s k w hkk hmw
  have hw1 : w i = w (i % k) := modFold_p34 hk0 hperW i
  have hw2 : w j = w (j % k) := modFold_p34 hk0 hperW j
  have hle : s.a (i % k) (j % k) ≤ dist (w i) (w j) := by
    rw [hw1, hw2]
    exact (hBB.2.2.1 (i % k) (j % k)).1
  rw [hcon, dist_self] at hle
  exact absurd hle (by linarith)

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V` (IMJXPHR.hl:1837). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
  intro i
  have hk0 : 0 < k := by omega
  have hper_w := MMs_periodic_p34 s k w hkk hmw
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  rcases eq_or_ne (i % k) (l % k) with hmod | hmod
  · have hi : w i = v2 := by
      rw [modFold_p34 hk0 hper_w i, hmod, ← modFold_p34 hk0 hper_w l, hl]
    obtain ⟨e0, he0, hup⟩ := UPS_X_POS_SEG_C_p34 v1 v2 x1 x2 x6 1 hnc hx1 hx2 hx6 h2 one_pos
    refine ⟨e0, he0, fun t ht => ?_⟩
    obtain ⟨hups, hx2t, -⟩ := hup t ⟨by linarith [ht.1, he0], ht.2⟩
    rw [hi]
    apply dist_pos.mpr
    intro hcon
    have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
        ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
          cross3 v1 (cross3 v1 v2) =
        v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
    have hnorm := EYYPQDW_NORMV3_p17 v1 v2 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t))
      x1 x2 (x2 - t) x6 x6 x6 a h1 h2 hx2t h6 h6 h6 hnc hx1 hx2 hx6 (by simp [ha]) hups hv3
    have heqx : x2 - t = x2 := by rw [← hnorm, hcon, hx2]
    linarith
  · have hwi : w i ≠ v2 := by
      intro h
      exact w5cC2_w_inj_p34 hk hkk hs hmw i l hmod (by rw [hl]; exact h)
    have hdist : 0 < dist v2 (w i) := dist_pos.mpr (Ne.symm hwi)
    exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w i) x1 x2 x6 a 0 h1 h2 h6 hnc
      hx1 hx2 hx6 ha hdist

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
  intro i hmod
  have hwi : w i ≠ v2 := by
    intro h
    exact w5cC2_w_inj_p34 hk hkk hs hmw i l hmod (by rw [hl]; exact h)
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hdist : 0 < dist v2 (w i) := dist_pos.mpr (Ne.symm hwi)
  exact EXISTS_SMALL_LE_CONST_V1_p34 v1 v2 (w i) x1 x2 x6 a 0 h1 h2 h6 hnc
    hx1 hx2 hx6 ha hdist

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


/-! ### W4: ivs / rho-node identities on the `range` face -/

/-- `rhoNode1` on the range face at `w l` is the successor vertex `w (l+1)`
(LA34-vocabulary rendering of the HOL `CARD_V_EQ_SCS_K1`/`CVLF_LF_F` ivs
step; no `localFan_p2` transport needed). -/
private theorem w5cC4_rhoNode1_range_p34 {s : ScsV39} {k l : ℕ} {w : ℕ → V3}
    {FF : Set (V3 × V3)} (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s)
    (hmw : w ∈ MMsV39 s)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    rhoNode1 FF (w l) = w (l + 1) := by
  have hk0 : 0 < k := by omega
  have hinj := w_inj_p34 hk hkk hs hmw
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hmem : ∀ a b : V3, (a, b) ∈ FF → ∃ i : ℕ, w i = a ∧ w (i + 1) = b :=
    fun a b => ff_edge_index_p34 hFF
  rw [rhoNode1]
  refine epsilon_eq_of_p34 ?_ ?_
  · intro y hy
    obtain ⟨i, hi1, hi2⟩ := hmem (w l) y hy
    have hres : i % k = l % k := by
      by_contra hne
      exact hinj i l hne hi1
    rw [← hi2, modFold_p34 hk0 hper (i + 1), res_succ_congr_p34 (by omega) hres,
      ← modFold_p34 hk0 hper (l + 1)]
  · have h : (w l, w (l + 1)) ∈ Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l, rfl⟩
    rwa [hFF] at h

/-- `ivsRhoNode1` on the range face at `w l` is the predecessor vertex
`w (l+k-1)` (HOL `ITER_CARD_MINUS1_EQ_IVS_RN1` content, direct residue
route). -/
private theorem w5cC4_ivsRhoNode1_range_p34 {s : ScsV39} {k l : ℕ} {w : ℕ → V3}
    {FF : Set (V3 × V3)} (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s)
    (hmw : w ∈ MMsV39 s)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    ivsRhoNode1 FF (w l) = w (l + k - 1) := by
  have hk0 : 0 < k := by omega
  have hinj := w_inj_p34 hk hkk hs hmw
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hmem : ∀ a b : V3, (a, b) ∈ FF → ∃ i : ℕ, w i = a ∧ w (i + 1) = b :=
    fun a b => ff_edge_index_p34 hFF
  rw [ivsRhoNode1]
  refine epsilon_eq_of_p34 ?_ ?_
  · intro y hy
    obtain ⟨i, hi1, hi2⟩ := hmem y (w l) hy
    have hres : (i + 1) % k = l % k := by
      by_contra hne
      exact hinj (i + 1) l hne hi2
    rw [← hi1, modFold_p34 hk0 hper i, res_succ_shift_p34 (by omega) hres,
      ← modFold_p34 hk0 hper (l + k - 1)]
  · have h : (w (l + k - 1), w (l + k - 1 + 1)) ∈
        Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l + k - 1, rfl⟩
    rw [hFF] at h
    simpa [show l + k - 1 + 1 = l + k by omega, hper] using h

/-- `epPair` on the range face at `w l` is the predecessor vertex
`w (l+k-1)` (HOL `ITER_CARD_MINUS1_EQ_IVS_RN1` in the `epPair` rendering). -/
private theorem w5cC4_epPair_range_p34 {s : ScsV39} {k l : ℕ} {w : ℕ → V3}
    {FF : Set (V3 × V3)} (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s)
    (hmw : w ∈ MMsV39 s)
    (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    epPair_p34 FF (w l) = w (l + k - 1) :=
  w5cC4_ivsRhoNode1_range_p34 hk hkk hs hmw hFF

/-! ### W5: azim-base kit (Planarity extraction) -/

/-- Pair swap for the affine cone: `affGt {x} {v,u} = affGt {x} {u,v}`. -/
private theorem w5cC5_affGt_pair_swap_p34 {x v u : V3} :
    affGt {x} ({v, u} : Set V3) = affGt {x} ({u, v} : Set V3) := by
  have h : ({v, u} : Set V3) = {u, v} := Set.pair_comm v u
  unfold affGt Affsign
  rw [h]

/-- `¬ Collinear3 0 a b` is symmetric in the last two slots. -/
private theorem w5cC5_collinear3_zero_swap {a b : V3} (h : ¬ Collinear3 0 a b) :
    ¬ Collinear3 0 b a := by
  intro hc
  apply h
  show Collinear ℝ ({0, a, b} : Set V3)
  have hset : ({0, a, b} : Set V3) = ({0, b, a} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact hc

/-- `¬ Collinear3 0 a b` gives `0 ∉ {a,b}` in `Disjoint` form. -/
private theorem w5cC5_disjoint_zero_pair_p34 {a b : V3} (h : ¬ Collinear3 0 a b) :
    Disjoint ({0} : Set V3) ({a, b} : Set V3) := by
  rw [Set.disjoint_singleton_left]
  intro h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
  rcases h0 with h0 | h0
  · have hcol : Collinear3 0 a b := by
      show Collinear ℝ ({0, a, b} : Set V3)
      rw [← h0]
      have hset : ({0, 0, b} : Set V3) = ({0, b} : Set V3) := by
        ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]
      exact collinear_pair ℝ (0 : V3) b
    exact h hcol
  · have hcol : Collinear3 0 a b := by
      show Collinear ℝ ({0, a, b} : Set V3)
      rw [← h0]
      have hset : ({0, a, 0} : Set V3) = ({0, a} : Set V3) := by
        ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]
      exact collinear_pair ℝ (0 : V3) a
    exact h hcol

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
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3 : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by
    rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_p34 (w (l + 1)) (w l) (w (l + k - 1))
    x1 x2 x6 (-1) hx1p hx2p hx6p hnc3 hx1' hx2' hx6' rfl hncW3 haffW
  have hemin : 0 < min e e' := lt_min he he'
  have he1 : 0 < min e e' / 2 := by linarith
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  refine ⟨min e e' / 2, he1, fun t ht => ?_⟩
  have htpos : 0 < t := ht.1
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hDv2 : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t
      = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    rw [v3DeforV4_p34, if_pos rfl]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 :=
    V3_DEFOR_RHO_NODE_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl he htpos
      (fun τ i hτ => hne τ hτ i) ht_e hFF
  have hSYM : ∀ w' : V3, (w', v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
        relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v2) ∈ FF :=
    V3_DEFOR_EQ_IN_FF_SYM_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl he htpos
      (fun τ i hτ => hne τ hτ i) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = epPair_p34 FF v2 := by
    simp only [epPair_p34]
    congr 1
    funext a
    exact propext (hSYM a)
  have hrFF : rhoNode1 FF v2 = w (l + 1) := by
    rw [← hl]; exact w5cC4_rhoNode1_range_p34 hk hkk hs hmw hFF
  have hepFF : epPair_p34 FF v2 = w (l + k - 1) := by
    rw [← hl]; exact w5cC4_epPair_range_p34 hk hkk hs hmw hFF
  rw [hDv2, hDFF, hRho, hEP, hrFF, hepFF]
  have hgt' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    have h := hgt t ⟨htpos, ht_e'⟩
    simpa only [hl1, hl] using h
  have hncv : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + 1)) :=
    properties_of_collinear4_points_fan hncW3 hgt'
  have hswap : affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3)
      = affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := w5cC5_affGt_pair_swap_p34
  have hmemW : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3) := by
    rw [hswap]; exact hgt'
  have hncu : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 1)) :=
    properties_of_collinear4_points_fan (w5cC5_collinear3_zero_swap hncW3) hmemW
  have hdis : Disjoint ({0} : Set V3) ({w (l + 1), w (l + k - 1)} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncW3
  exact aff_gt2_subset_aff_ge hdis hncu hncv hgt'

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
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3 : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by
    rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 (w (l + 1)) (w l) (w (l + k - 1))
    x1 x2 x6 (-1) hx1p hx2p hx6p hnc3 hx1' hx2' hx6' rfl hncW3 haffW
  have hemin : 0 < min e e' := lt_min he he'
  have he1 : 0 < min e e' / 2 := by linarith
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  refine ⟨min e e' / 2, he1, fun t ht => ?_⟩
  have ht_neg : -e < t := by linarith [ht.1, he1e]
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_neg' : -e' < t := by linarith [ht.1, he1e']
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hDv2 : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t
      = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    rw [v3DeforV4_p34, if_pos rfl]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 :=
    V3_DEFOR_RHO_NODE_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  have hSYM : ∀ w' : V3, (w', v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
        relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v2) ∈ FF :=
    V3_DEFOR_EQ_IN_FF_SYM_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = epPair_p34 FF v2 := by
    simp only [epPair_p34]
    congr 1
    funext a
    exact propext (hSYM a)
  have hrFF : rhoNode1 FF v2 = w (l + 1) := by
    rw [← hl]; exact w5cC4_rhoNode1_range_p34 hk hkk hs hmw hFF
  have hepFF : epPair_p34 FF v2 = w (l + k - 1) := by
    rw [← hl]; exact w5cC4_epPair_range_p34 hk hkk hs hmw hFF
  rw [hDv2, hDFF, hRho, hEP, hrFF, hepFF]
  have hgt' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    have h := hgt t ⟨ht_neg', ht_e'⟩
    simpa only [hl1, hl] using h
  have hncv : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + 1)) :=
    properties_of_collinear4_points_fan hncW3 hgt'
  have hswap : affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3)
      = affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := w5cC5_affGt_pair_swap_p34
  have hmemW : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3) := by
    rw [hswap]; exact hgt'
  have hncu : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 1)) :=
    properties_of_collinear4_points_fan (w5cC5_collinear3_zero_swap hncW3) hmemW
  have hdis : Disjoint ({0} : Set V3) ({w (l + 1), w (l + k - 1)} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncW3
  exact aff_gt2_subset_aff_ge hdis hncu hncv hgt'

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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)) = azim 0 v1 (rhoNode1 FF v1) (epPair_p34 FF v1) := by
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3 : ¬ Collinear3 0 v1 v2 := hnc
  have hnc3W : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_p34 (w (l + 1)) (w l) (w (l + k - 1))
    x1 x2 x6 (-1) hx1p hx2p hx6p hnc3W hx1' hx2' hx6' rfl hncW3 haffW
  refine ⟨min e e' / 2, by positivity, fun t ht => ?_⟩
  have htpos : 0 < t := ht.1
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hv12 : v1 ≠ v2 := fun hc => hnc3 (by rw [hc]; exact collinear3_pair_right rfl)
  have hDv1 : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t = v1 := by
    rw [v3DeforV4_p34, if_neg hv12]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1
      = rhoNode1 FF v1 :=
    V3_DEFOR_RHO_NODE_AT_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he htpos (fun τ i hτ => hne τ hτ i) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1
      = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) :=
    V3_DEFOR_EQ_IN_FF_AT_V1_SYM_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he htpos (fun τ i hτ => hne τ hτ i) ht_e hFF
  rw [hDv1, hDFF, hRho, hEP]
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hepFF : epPair_p34 FF v1 = v2 := by
    rw [← hl1]
    have h := w5cC4_epPair_range_p34 (l := l + 1) hk hkk hs hmw hFF
    rw [h, show l + 1 + k - 1 = l + k by omega, hper l, hl]
  rw [hepFF]
  have hgt' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({v1, w (l + k - 1)} : Set V3) := by
    have h := hgt t ⟨htpos, ht_e'⟩
    rw [hl1, hl] at h
    exact h
  have hncW3' : ¬ Collinear3 0 v1 (w (l + k - 1)) := by rwa [hl1] at hncW3
  have hncvf : ¬ Collinear3 0 v1 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) := by
    have h : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v1 :=
      properties_of_collinear4_points_fan hncW3' hgt'
    exact w5cC5_collinear3_zero_swap h
  have hdis : Disjoint ({0} : Set V3) ({v1, w (l + k - 1)} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncW3'
  have hmemf : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGe ({0} : Set V3) ({v1, w (l + k - 1)} : Set V3) :=
    aff_gt_subset_aff_ge hdis hgt'
  have hmemv2 : v2 ∈ affGe ({0} : Set V3) ({v1, w (l + k - 1)} : Set V3) := by
    have hh := haffW
    rw [hl1, hl] at hh
    exact aff_gt_subset_aff_ge hdis hh
  have hstep1 : azim 0 v1 (rhoNode1 FF v1) (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
      = azim 0 v1 (rhoNode1 FF v1) (w (l + k - 1)) :=
    AZIM_SAME_WITHIN_AFF_GE_ALT 0 v1 _ (w (l + k - 1)) (rhoNode1 FF v1) hmemf hncvf hncW3'
  have hstep2 : azim 0 v1 (rhoNode1 FF v1) v2
      = azim 0 v1 (rhoNode1 FF v1) (w (l + k - 1)) :=
    AZIM_SAME_WITHIN_AFF_GE_ALT 0 v1 v2 (w (l + k - 1)) (rhoNode1 FF v1) hmemv2 hnc3 hncW3'
  rw [hstep1, hstep2]


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)) = azim 0 v1 (rhoNode1 FF v1) (epPair_p34 FF v1) := by
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3 : ¬ Collinear3 0 v1 v2 := hnc
  have hnc3W : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 (w (l + 1)) (w l) (w (l + k - 1))
    x1 x2 x6 (-1) hx1p hx2p hx6p hnc3W hx1' hx2' hx6' rfl hncW3 haffW
  refine ⟨min e e' / 2, by positivity, fun t ht => ?_⟩
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  have ht_neg : -e < t := by linarith [ht.1, he1e]
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_neg' : -e' < t := by linarith [ht.1, he1e']
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hv12 : v1 ≠ v2 := fun hc => hnc3 (by rw [hc]; exact collinear3_pair_right rfl)
  have hDv1 : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t = v1 := by
    rw [v3DeforV4_p34, if_neg hv12]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1
      = rhoNode1 FF v1 :=
    V3_DEFOR_RHO_NODE_AT_V1_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1
      = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) :=
    V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
      hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  rw [hDv1, hDFF, hRho, hEP]
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hepFF : epPair_p34 FF v1 = v2 := by
    rw [← hl1]
    have h := w5cC4_epPair_range_p34 (l := l + 1) hk hkk hs hmw hFF
    rw [h, show l + 1 + k - 1 = l + k by omega, hper l, hl]
  rw [hepFF]
  have hgt' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({v1, w (l + k - 1)} : Set V3) := by
    have h := hgt t ⟨ht_neg', ht_e'⟩
    rw [hl1, hl] at h
    exact h
  have hncW3' : ¬ Collinear3 0 v1 (w (l + k - 1)) := by rwa [hl1] at hncW3
  have hncvf : ¬ Collinear3 0 v1 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) := by
    have h : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v1 :=
      properties_of_collinear4_points_fan hncW3' hgt'
    exact w5cC5_collinear3_zero_swap h
  have hdis : Disjoint ({0} : Set V3) ({v1, w (l + k - 1)} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncW3'
  have hmemf : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGe ({0} : Set V3) ({v1, w (l + k - 1)} : Set V3) :=
    aff_gt_subset_aff_ge hdis hgt'
  have hmemv2 : v2 ∈ affGe ({0} : Set V3) ({v1, w (l + k - 1)} : Set V3) := by
    have hh := haffW
    rw [hl1, hl] at hh
    exact aff_gt_subset_aff_ge hdis hh
  have hstep1 : azim 0 v1 (rhoNode1 FF v1) (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
      = azim 0 v1 (rhoNode1 FF v1) (w (l + k - 1)) :=
    AZIM_SAME_WITHIN_AFF_GE_ALT 0 v1 _ (w (l + k - 1)) (rhoNode1 FF v1) hmemf hncvf hncW3'
  have hstep2 : azim 0 v1 (rhoNode1 FF v1) v2
      = azim 0 v1 (rhoNode1 FF v1) (w (l + k - 1)) :=
    AZIM_SAME_WITHIN_AFF_GE_ALT 0 v1 v2 (w (l + k - 1)) (rhoNode1 FF v1) hmemv2 hnc3 hncW3'
  rw [hstep1, hstep2]


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1))) (epPair_p34 FF (w (l + k - 1))) := by
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3W : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_p34 (w (l + 1)) (w l) (w (l + k - 1))
    x1 x2 x6 (-1) hx1p hx2p hx6p hnc3W hx1' hx2' hx6' rfl hncW3 haffW
  refine ⟨min e e' / 2, by positivity, fun t ht => ?_⟩
  have htpos : 0 < t := ht.1
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hu_ne_v2 : w (l + k - 1) ≠ v2 := by
    intro hc
    have hres : (l + k - 1) % k ≠ l % k := by
      have h := mod_ne_succ_p34 (k := k) (l := l + k - 1) (by omega)
      rwa [show l + k - 1 + 1 = l + k by omega, Nat.add_mod_right] at h
    exact (w_inj_p34 hk hkk hs hmw (l + k - 1) l hres) (by rw [hc, hl])
  have hDv : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t = w (l + k - 1) := by
    rw [v3DeforV4_p34, if_neg hu_ne_v2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + k - 1)) = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    simpa only [rhoNode1] using
      V3_DEFOR_EQ_IN_FF_AT_W_SYM_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
        hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he htpos
        (fun τ i hτ => hne τ hτ i) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + k - 1)) = epPair_p34 FF (w (l + k - 1)) := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (by
      have h := V3_DEFOR_EQ_IN_FF_AT_W_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw
        hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he htpos
        (fun τ i hτ => hne τ hτ i) ht_e hFF y
      have hidx : l + (k - 1) = l + k - 1 := by omega
      simpa only [hkk, hidx] using h)
  rw [hDv, hDFF, hRho, hEP]
  have hrhoFF : rhoNode1 FF (w (l + k - 1)) = v2 := by
    have h := w5cC4_rhoNode1_range_p34 (l := l + k - 1) hk hkk hs hmw hFF
    rw [h, show l + k - 1 + 1 = l + k by omega, hper l, hl]
  have hepFF : epPair_p34 FF (w (l + k - 1)) = w (l + k - 2) := by
    have h := w5cC4_epPair_range_p34 (l := l + k - 1) hk hkk hs hmw hFF
    rw [h, show l + k - 1 + k - 1 = l + k - 2 + k by omega, hper (l + k - 2)]
  rw [hrhoFF, hepFF]
  have hgt' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({v1, w (l + k - 1)} : Set V3) := by
    have h := hgt t ⟨htpos, ht_e'⟩
    rw [hl1, hl] at h
    exact h
  have hncUV : ¬ Collinear3 0 (w (l + k - 1)) v1 := by
    simpa only [hl1] using w5cC5_collinear3_zero_swap hncW3
  have hswap : affGt {0} ({v1, w (l + k - 1)} : Set V3)
      = affGt {0} ({w (l + k - 1), v1} : Set V3) := w5cC5_affGt_pair_swap_p34
  have hgtU : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + k - 1), v1} : Set V3) := by
    rw [← hswap]; exact hgt'
  have hncvU : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 1)) :=
    properties_of_collinear4_points_fan hncUV hgtU
  have hncUf : ¬ Collinear3 0 (w (l + k - 1)) (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) :=
    w5cC5_collinear3_zero_swap hncvU
  have hdisU : Disjoint ({0} : Set V3) ({w (l + k - 1), v1} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncUV
  have hmemf : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGe ({0} : Set V3) ({w (l + k - 1), v1} : Set V3) :=
    aff_gt_subset_aff_ge hdisU hgtU
  have hgtv2U : v2 ∈ affGt {0} ({w (l + k - 1), v1} : Set V3) := by
    rw [← hswap]
    have hh := haffW
    rw [hl1, hl] at hh
    exact hh
  have hmemv2 : v2 ∈ affGe ({0} : Set V3) ({w (l + k - 1), v1} : Set V3) :=
    aff_gt_subset_aff_ge hdisU hgtv2U
  have hncv2U : ¬ Collinear3 0 v2 (w (l + k - 1)) :=
    properties_of_collinear4_points_fan hncUV hgtv2U
  have hncUv2 : ¬ Collinear3 0 (w (l + k - 1)) v2 :=
    w5cC5_collinear3_zero_swap hncv2U
  have hstep1 : azim 0 (w (l + k - 1))
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 2))
      = azim 0 (w (l + k - 1)) v1 (w (l + k - 2)) :=
    AZIM_SAME_WITHIN_AFF_GE 0 (w (l + k - 1)) _ v1 (w (l + k - 2))
      hmemf hncUf hncUV
  have hstep2 : azim 0 (w (l + k - 1)) v2 (w (l + k - 2))
      = azim 0 (w (l + k - 1)) v1 (w (l + k - 2)) :=
    AZIM_SAME_WITHIN_AFF_GE 0 (w (l + k - 1)) v2 v1 (w (l + k - 2))
      hmemv2 hncUv2 hncUV
  rw [hstep1, hstep2]


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1))) (epPair_p34 FF (w (l + k - 1))) := by
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3W : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 (w (l + 1)) (w l) (w (l + k - 1))
    x1 x2 x6 (-1) hx1p hx2p hx6p hnc3W hx1' hx2' hx6' rfl hncW3 haffW
  refine ⟨min e e' / 2, by positivity, fun t ht => ?_⟩
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  have ht_neg : -e < t := by linarith [ht.1, he1e]
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_neg' : -e' < t := by linarith [ht.1, he1e']
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hu_ne_v2 : w (l + k - 1) ≠ v2 := by
    intro hc
    have hres : (l + k - 1) % k ≠ l % k := by
      have h := mod_ne_succ_p34 (k := k) (l := l + k - 1) (by omega)
      rwa [show l + k - 1 + 1 = l + k by omega, Nat.add_mod_right] at h
    exact (w_inj_p34 hk hkk hs hmw (l + k - 1) l hres) (by rw [hc, hl])
  have hDv : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t = w (l + k - 1) := by
    rw [v3DeforV4_p34, if_neg hu_ne_v2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + k - 1)) = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    simpa only [rhoNode1] using
      V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hl1
        hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
        (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + k - 1)) = epPair_p34 FF (w (l + k - 1)) := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (by
      have h := V3_DEFOR_EQ_IN_FF_AT_W_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw
        hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
        (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF y
      have hidx : l + (k - 1) = l + k - 1 := by omega
      simpa only [hkk, hidx] using h)
  rw [hDv, hDFF, hRho, hEP]
  have hrhoFF : rhoNode1 FF (w (l + k - 1)) = v2 := by
    have h := w5cC4_rhoNode1_range_p34 (l := l + k - 1) hk hkk hs hmw hFF
    rw [h, show l + k - 1 + 1 = l + k by omega, hper l, hl]
  have hepFF : epPair_p34 FF (w (l + k - 1)) = w (l + k - 2) := by
    have h := w5cC4_epPair_range_p34 (l := l + k - 1) hk hkk hs hmw hFF
    rw [h, show l + k - 1 + k - 1 = l + k - 2 + k by omega, hper (l + k - 2)]
  rw [hrhoFF, hepFF]
  have hgt' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({v1, w (l + k - 1)} : Set V3) := by
    have h := hgt t ⟨ht_neg', ht_e'⟩
    rw [hl1, hl] at h
    exact h
  have hncUV : ¬ Collinear3 0 (w (l + k - 1)) v1 := by
    simpa only [hl1] using w5cC5_collinear3_zero_swap hncW3
  have hswap : affGt {0} ({v1, w (l + k - 1)} : Set V3)
      = affGt {0} ({w (l + k - 1), v1} : Set V3) := w5cC5_affGt_pair_swap_p34
  have hgtU : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + k - 1), v1} : Set V3) := by
    rw [← hswap]; exact hgt'
  have hncvU : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 1)) :=
    properties_of_collinear4_points_fan hncUV hgtU
  have hncUf : ¬ Collinear3 0 (w (l + k - 1)) (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) :=
    w5cC5_collinear3_zero_swap hncvU
  have hdisU : Disjoint ({0} : Set V3) ({w (l + k - 1), v1} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncUV
  have hmemf : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGe ({0} : Set V3) ({w (l + k - 1), v1} : Set V3) :=
    aff_gt_subset_aff_ge hdisU hgtU
  have hgtv2U : v2 ∈ affGt {0} ({w (l + k - 1), v1} : Set V3) := by
    rw [← hswap]
    have hh := haffW
    rw [hl1, hl] at hh
    exact hh
  have hmemv2 : v2 ∈ affGe ({0} : Set V3) ({w (l + k - 1), v1} : Set V3) :=
    aff_gt_subset_aff_ge hdisU hgtv2U
  have hncv2U : ¬ Collinear3 0 v2 (w (l + k - 1)) :=
    properties_of_collinear4_points_fan hncUV hgtv2U
  have hncUv2 : ¬ Collinear3 0 (w (l + k - 1)) v2 :=
    w5cC5_collinear3_zero_swap hncv2U
  have hstep1 : azim 0 (w (l + k - 1))
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 2))
      = azim 0 (w (l + k - 1)) v1 (w (l + k - 2)) :=
    AZIM_SAME_WITHIN_AFF_GE 0 (w (l + k - 1)) _ v1 (w (l + k - 2))
      hmemf hncUf hncUV
  have hstep2 : azim 0 (w (l + k - 1)) v2 (w (l + k - 2))
      = azim 0 (w (l + k - 1)) v1 (w (l + k - 2)) :=
    AZIM_SAME_WITHIN_AFF_GE 0 (w (l + k - 1)) v2 v1 (w (l + k - 2))
      hmemv2 hncUv2 hncUV
  rw [hstep1, hstep2]


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v) := by
  subst ha
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  refine ⟨e, he, fun t v ht hv1 hv2 hvw hvV => ?_⟩
  have htpos : 0 < t := ht.1
  have ht_e : t < e := ht.2
  have hDv : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t = v := by
    rw [v3DeforV4_p34, if_neg hv2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v
      = rhoNode1 FF v := by
    simp only [rhoNode1]
    rw [funext fun y => propext (V3_DEFOR_EQ_IN_FF_AT_V_ANY_p34 s k l w v1 v2 v x1 x2 x6 (-1) e t FF
      hk hkk hs hmw hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he htpos
      (fun τ i hτ => hne τ hτ i) ht_e hFF hv1 hv2 hvw hvV y)]
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v
      = epPair_p34 FF v := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_p34 s k l w v1 v2 v x1 x2 x6 (-1) e t FF
      hk hkk hs hmw hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he htpos
      (fun τ i hτ => hne τ hτ i) ht_e hFF hv1 hv2 hvw hvV y)
  rw [hDv, hDFF, hRho, hEP]


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v) := by
  subst ha
  obtain ⟨e, he, hne⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hl1 hx1 hx2 hx6 rfl
  refine ⟨e, he, fun t v ht hv1 hv2 hvw hvV => ?_⟩
  have ht_neg : -e < t := ht.1
  have ht_e : t < e := ht.2
  have hDv : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t = v := by
    rw [v3DeforV4_p34, if_neg hv2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v
      = rhoNode1 FF v := by
    simp only [rhoNode1]
    rw [funext fun y => propext (V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_p34 s k l w v1 v2 v x1 x2 x6 (-1)
      e t FF hk hkk hs hmw hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF hv1 hv2 hvw hvV y)]
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v
      = epPair_p34 FF v := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_p34 s k l w v1 v2 v x1 x2 x6 (-1) e t FF
      hk hkk hs hmw hl hl1 hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF hv1 hv2 hvw hvV y)
  rw [hDv, hDFF, hRho, hEP]


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v) := by
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3W : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨eA, heA, hA⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eB, heB, hB⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eC, heC, hC⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eD, heD, hD⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨min (min (min eA eB) eC) eD / 2, by positivity, fun t v ht => ?_⟩
  intro hvV
  have htpos : 0 < t := ht.1
  have hleA : min (min (min eA eB) eC) eD / 2 < eA := by
    have h := le_trans (min_le_left (min (min eA eB) eC) eD)
      (le_trans (min_le_left (min eA eB) eC) (min_le_left eA eB))
    linarith
  have hleB : min (min (min eA eB) eC) eD / 2 < eB := by
    have h := le_trans (min_le_left (min (min eA eB) eC) eD)
      (le_trans (min_le_left (min eA eB) eC) (min_le_right eA eB))
    linarith
  have hleC : min (min (min eA eB) eC) eD / 2 < eC := by
    have h := le_trans (min_le_left (min (min eA eB) eC) eD) (min_le_right (min eA eB) eC)
    linarith
  have hleD : min (min (min eA eB) eC) eD / 2 < eD := by
    have h := min_le_right (min (min eA eB) eC) eD
    linarith
  have htA : 0 < t ∧ t < eA := ⟨htpos, by linarith [ht.2, hleA]⟩
  have htB : 0 < t ∧ t < eB := ⟨htpos, by linarith [ht.2, hleB]⟩
  have htC : 0 < t ∧ t < eC := ⟨htpos, by linarith [ht.2, hleC]⟩
  have htD : 0 < t ∧ t < eD := ⟨htpos, by linarith [ht.2, hleD]⟩
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hk0 : 0 < k := by omega
  obtain ⟨j, hj⟩ := hvV
  by_cases h2 : j % k = l % k
  · have hv2 : v = v2 := by
      rw [← hj, modFold_p34 hk0 hper j, h2, ← modFold_p34 hk0 hper l, hl]
    rw [hv2]
    rw [hC t htC]
    have hrho : rhoNode1 FF v2 = v1 := by
      have h := w5cC4_rhoNode1_range_p34 (l := l) hk hkk hs hmw hFF
      rwa [hl, hl1] at h
    have hep : epPair_p34 FF v2 = w (l + k - 1) := by
      have h := w5cC4_epPair_range_p34 (l := l) hk hkk hs hmw hFF
      rwa [hl] at h
    rw [hrho, hep]
    have haz' : azim 0 v2 v1 (w (l + k - 1)) = Real.pi := by
      rw [← hl, ← hl1, ← hlk]
      exact haz
    exact haz'.symm
  · by_cases h1c : j % k = (l + 1) % k
    · have hv1 : v = v1 := by
        rw [← hj, modFold_p34 hk0 hper j, h1c, ← modFold_p34 hk0 hper (l + 1), hl1]
      rw [hv1]
      exact hB t htB
    · by_cases hEc : j % k = (l + k - 1) % k
      · have hvW : v = w (l + k - 1) := by
          rw [← hj, modFold_p34 hk0 hper j, hEc, ← modFold_p34 hk0 hper (l + k - 1)]
        rw [hvW]
        exact hA t htA
      · have hvne2 : v ≠ v2 := by
          intro hcon
          exact h2 (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j l hne) (by rw [hj, hcon, hl]))
        have hvne1 : v ≠ v1 := by
          intro hcon
          exact h1c (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j (l + 1) hne) (by rw [hj, hcon, hl1]))
        have hvneW : v ≠ w (l + k - 1) := by
          intro hcon
          exact hEc (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j (l + k - 1) hne) (by rw [hj, hcon]))
        exact hD t v htD hvne1 hvne2 hvneW ⟨j, hj⟩


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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v) := by
  subst ha
  have hlk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk]; exact hncW
  have hnc3W : ¬ Collinear ℝ ({0, w (l + 1), w l} : Set V3) := by rw [hl1, hl]; exact hnc
  have hx1' : ‖w (l + 1)‖ ^ 2 = x1 := by rw [hl1]; exact hx1
  have hx2' : ‖w l‖ ^ 2 = x2 := by rw [hl]; exact hx2
  have hx6' : ‖w (l + 1) - w l‖ ^ 2 = x6 := by rw [hl1, hl]; exact hx6
  obtain ⟨eA, heA, hA⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eB, heB, hB⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eC, heC, hC⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eD, heD, hD⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨min (min (min eA eB) eC) eD / 2, by positivity, fun t v ht => ?_⟩
  intro hvV
  have hleA : min (min (min eA eB) eC) eD / 2 < eA := by
    have h := le_trans (min_le_left (min (min eA eB) eC) eD)
      (le_trans (min_le_left (min eA eB) eC) (min_le_left eA eB))
    linarith
  have hleB : min (min (min eA eB) eC) eD / 2 < eB := by
    have h := le_trans (min_le_left (min (min eA eB) eC) eD)
      (le_trans (min_le_left (min eA eB) eC) (min_le_right eA eB))
    linarith
  have hleC : min (min (min eA eB) eC) eD / 2 < eC := by
    have h := le_trans (min_le_left (min (min eA eB) eC) eD) (min_le_right (min eA eB) eC)
    linarith
  have hleD : min (min (min eA eB) eC) eD / 2 < eD := by
    have h := min_le_right (min (min eA eB) eC) eD
    linarith
  have htA : -eA < t ∧ t < eA := ⟨by linarith [ht.1, hleA], by linarith [ht.2, hleA]⟩
  have htB : -eB < t ∧ t < eB := ⟨by linarith [ht.1, hleB], by linarith [ht.2, hleB]⟩
  have htC : -eC < t ∧ t < eC := ⟨by linarith [ht.1, hleC], by linarith [ht.2, hleC]⟩
  have htD : -eD < t ∧ t < eD := ⟨by linarith [ht.1, hleD], by linarith [ht.2, hleD]⟩
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hk0 : 0 < k := by omega
  obtain ⟨j, hj⟩ := hvV
  by_cases h2 : j % k = l % k
  · have hv2 : v = v2 := by
      rw [← hj, modFold_p34 hk0 hper j, h2, ← modFold_p34 hk0 hper l, hl]
    rw [hv2]
    rw [hC t htC]
    have hrho : rhoNode1 FF v2 = v1 := by
      have h := w5cC4_rhoNode1_range_p34 (l := l) hk hkk hs hmw hFF
      rwa [hl, hl1] at h
    have hep : epPair_p34 FF v2 = w (l + k - 1) := by
      have h := w5cC4_epPair_range_p34 (l := l) hk hkk hs hmw hFF
      rwa [hl] at h
    rw [hrho, hep]
    have haz' : azim 0 v2 v1 (w (l + k - 1)) = Real.pi := by
      rw [← hl, ← hl1, ← hlk]
      exact haz
    exact haz'.symm
  · by_cases h1c : j % k = (l + 1) % k
    · have hv1 : v = v1 := by
        rw [← hj, modFold_p34 hk0 hper j, h1c, ← modFold_p34 hk0 hper (l + 1), hl1]
      rw [hv1]
      exact hB t htB
    · by_cases hEc : j % k = (l + k - 1) % k
      · have hvW : v = w (l + k - 1) := by
          rw [← hj, modFold_p34 hk0 hper j, hEc, ← modFold_p34 hk0 hper (l + k - 1)]
        rw [hvW]
        exact hA t htA
      · have hvne2 : v ≠ v2 := by
          intro hcon
          exact h2 (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j l hne) (by rw [hj, hcon, hl]))
        have hvne1 : v ≠ v1 := by
          intro hcon
          exact h1c (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j (l + 1) hne) (by rw [hj, hcon, hl1]))
        have hvneW : v ≠ w (l + k - 1) := by
          intro hcon
          exact hEc (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j (l + k - 1) hne) (by rw [hj, hcon]))
        exact hD t v htD hvne1 hvne2 hvneW ⟨j, hj⟩


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
  obtain ⟨e, he, h⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨e, he, fun v t hv ht0 hte hπ => ?_⟩
  have hEq : interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
      (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v := by
    simpa only [interiorAngle1, ivsRhoNode1, epPair_p34] using h t v ⟨by linarith, hte⟩ hv
  rw [hEq, hπ]

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
  obtain ⟨e, he, h⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨e, he, fun v t hv ht1 ht2 hπ => ?_⟩
  have hEq : interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
      (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v := by
    simpa only [interiorAngle1, ivsRhoNode1, epPair_p34] using h t v ⟨ht1, ht2⟩ hv
  rw [hEq, hπ]

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

/-! ### W10: LA5 bridge for the lunar affine-hull items

`LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI` (LocalAuto5:6766) is consumed through
`import Kepler.Text.CircularSolKit`; its axiom face is exactly
`[propext, Classical.choice, Quot.sound]` (kernel `#print axioms`, see
`logs/probe_ax.log`).  The LA1→LA2 convex-local-fan transport below is a
verbatim copy of `CircularSolKit.kcs_clf2` together with its two private
prerequisites (they are `private` in that module, hence not importable). -/

/-- 2-regularity ⇒ every vertex lies on some edge. -/
private theorem w10_hedge {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E) ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

/-- `localFan_p2 ⇒ FF ⊆ dart1OfFan` (pattern of LocalAuto9:1422-1428). -/
private theorem w10_ffSubDart {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : localFan_p2 V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    FF ⊆ Fan.dart1OfFan V E := by
  obtain ⟨H, hd, -, -, -, -, hface, -⟩ := hlf
  obtain ⟨z, hzd, hFF⟩ := hface
  intro d hdF
  have hsub := H.face_subset_darts hzd (hFF ▸ hdF)
  rw [hd] at hsub
  exact (hno_p2_of_no_isolated hedge) ▸ hsub

/-- Transport the LA1 `ConvexLocalFan` hypothesis to the LA2
`convexLocalFan_p2` encoding (verbatim copy of `CircularSolKit.kcs_clf2`,
`private` there). -/
private theorem w10_clf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf (w10_hedge h2reg)
  have hsub := w10_ffSubDart hlf2 (w10_hedge h2reg)
  refine ⟨hlf2, ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · have hb : azimInFan d E = azimInFan_p3 d E :=
      azimInFan_eq_azimInFan_p3 hfan (hsub hd)
    show azimInFan_p2 d E ≤ Real.pi
    rw [show azimInFan_p2 d E = azimInFan_p3 d E from rfl, ← hb]
    exact (hcvx d hd).1
  · show V ⊆ wedgeInFanGe_p2 d E
    rw [show wedgeInFanGe_p2 d E = wedgeInFanGe_p3 d E from rfl,
      ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfan (hsub hd)]
    exact (hcvx d hd).2

/-- Common core of the three `DEFORMATION_LUNAR_AFFINE_HULL*` items: the
`v3_defor_v4` image stays in the strict cone `affGt {0} {v1, u}`, which sits
in `aff {0, v1, u}`; the LUNAR statement of LocalAuto5 places both
neighbour slots of `v2` (`rhoNode1 FF v2 = w (l+1)` and
`ivsRhoNode1 FF v2 = w (l+k-1)`, the `w5cC4` special values) in
`aff {v2, v, w1}`, so `{0, v1, u} ⊆ aff {v2, v, w1} ⊆ aff {0, v, w1, v2}`.
`hpair` is the only variant-dependent slot: the non-twin items have
`v1 = w (l+1)` and `u = w (l+k-1)`, the `TWO_CASES` twin has `v1 = w (l+k-1)`
and `u = w (l+1)`.  The conclusion uses the closed `Icc (-e) e` shape; the
strict-cone input is consumed at `e/2`. -/
private theorem w10_lunar_hull_core_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 v w1 u : V3) (x1 x2 x6 : ℝ) (V : Set V3) (E : Set (Set V3))
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3))
    (haffW : v2 ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3))
    (hpair : ({v1, u} : Set V3) = ({w (l + 1), w (l + k - 1)} : Set V3))
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc3 : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
    (hV : Set.range w = V)
    (hE : Set.range (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) = E)
    (hlun : Lunar v w1 V E) (hl : w l = v2)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, t ∈ Icc (-e) e →
      v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈
        affineSpan ℝ ({0, v, w1, v2} : Set V3) := by
  -- the `v3DeforV1` image stays in the strict cone at `{v1, u}`
  obtain ⟨e₀, he₀, hgt⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 v1 v2 u x1 x2 x6 (-1)
    hx1p hx2p hx6p hnc3 hx1 hx2 hx6 rfl (by rw [hpair]; exact hncW)
    (by rw [hpair]; exact haffW)
  -- the cone sits in `aff {0, v1, u} = aff {0, w (l+1), w (l+k-1)}`
  have hset0 : ({0, v1, u} : Set V3) = ({0, w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [hpair]
  have hcone : affGt {0} ({v1, u} : Set V3) ⊆
      (affineSpan ℝ ({0, v1, u} : Set V3) : Set V3) := by
    refine subset_trans (AFF_GT_SUB_AFF_UNION {0} ({v1, u} : Set V3)) ?_
    intro z hz
    refine affineSpan_mono ℝ ?_ hz
    intro q hq
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  -- LUNAR: both neighbour slots of `v2` lie in `aff {v2, v, w1}`
  have hBB : BBsV39 s w := by
    have h := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h
    have h2 := h.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.1
  have hclf : ConvexLocalFan (Set.range w)
      (Set.range fun i => ({w i, w (i + 1)} : Set V3))
      (Set.range fun i => (w i, w (i + 1))) :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s k w hk hkk hBB
  have hclf2 := w10_clf2 hclf
  have hlun' : lunar_p2 v w1 (Set.range w)
      (Set.range fun i => ({w i, w (i + 1)} : Set V3)) := by
    rw [← hV, ← hE] at hlun
    exact hlun
  have hL := LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI (V := Set.range w)
    (E := Set.range fun i => ({w i, w (i + 1)} : Set V3))
    (FF := Set.range fun i => (w i, w (i + 1))) (v := v) (w := w1) hclf2 hlun'
  obtain ⟨h0c, hspec⟩ := hL
  have hv2mem : v2 ∈ Set.range w \ ({v, w1} : Set V3) := by
    refine ⟨⟨l, ?_⟩, ?_⟩
    · rw [hl]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hvv2 h.symm, fun h => hw1v2 h.symm⟩
  obtain ⟨-, hrho_mem, hivs_mem⟩ := hspec v2 hv2mem
  have hrho : rhoNode1_p2 (Set.range fun i : ℕ => (w i, w (i + 1))) v2 = w (l + 1) := by
    calc rhoNode1_p2 (Set.range fun i : ℕ => (w i, w (i + 1))) v2
        = rhoNode1 (Set.range fun i : ℕ => (w i, w (i + 1))) v2 := rfl
      _ = w (l + 1) := by
        have h := w5cC4_rhoNode1_range_p34 (FF := Set.range fun i : ℕ => (w i, w (i + 1)))
          (k := k) (l := l) (w := w) (s := s) hk hkk hs hmw rfl
        rwa [hl] at h
  have hivs : ivsRhoNode1_p2 (Set.range fun i : ℕ => (w i, w (i + 1))) v2 = w (l + k - 1) := by
    calc ivsRhoNode1_p2 (Set.range fun i : ℕ => (w i, w (i + 1))) v2
        = ivsRhoNode1 (Set.range fun i : ℕ => (w i, w (i + 1))) v2 := rfl
      _ = w (l + k - 1) := by
        have h := w5cC4_ivsRhoNode1_range_p34 (FF := Set.range fun i : ℕ => (w i, w (i + 1)))
          (k := k) (l := l) (w := w) (s := s) hk hkk hs hmw rfl
        rwa [hl] at h
  rw [hrho] at hrho_mem
  rw [hivs] at hivs_mem
  -- `0 ∈ aff {v2, v, w1}` from `0 ∈ conv0 {v, w1}`
  have h0span : (0:V3) ∈ (affineSpan ℝ ({v2, v, w1} : Set V3) : Set V3) := by
    have hEq : (affineSpan ℝ ({v, w1} : Set V3) : Set V3) = affineSpan ℝ ({v, 0} : Set V3) :=
      IN_CONV0_IMP_AFF_EQ (x := v) (y := w1) (a := 0) h0c
    have h0v0 : (0:V3) ∈ (affineSpan ℝ ({v, 0} : Set V3) : Set V3) :=
      right_mem_affineSpan_pair _ _ _
    have h0vw : (0:V3) ∈ (affineSpan ℝ ({v, w1} : Set V3) : Set V3) := by
      rw [hEq]
      exact h0v0
    refine affineSpan_mono ℝ ?_ h0vw
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hsub3 : ({0, w (l + 1), w (l + k - 1)} : Set V3) ⊆
      (affineSpan ℝ ({v2, v, w1} : Set V3) : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact h0span
    · exact hrho_mem
    · exact hivs_mem
  have hspan3 : (affineSpan ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3) : Set V3) ⊆
      affineSpan ℝ ({v2, v, w1} : Set V3) :=
    S_SUBSET_IMP_AFF_S_TOO hsub3
  refine ⟨e₀ / 2, by linarith, fun t ht => ?_⟩
  rw [Set.mem_Icc] at ht
  have ht1 : -e₀ < t := by linarith [ht.1]
  have ht2 : t < e₀ := by linarith [ht.2]
  have hdef : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t
      = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    rw [v3DeforV4_p34, if_pos rfl]
  rw [hdef]
  have hmemgt : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({v1, u} : Set V3) :=
    hgt t ⟨ht1, ht2⟩
  have hmem1 : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      (affineSpan ℝ ({0, v1, u} : Set V3) : Set V3) := hcone hmemgt
  have hmem2 : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      (affineSpan ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3) : Set V3) := by
    rw [← hset0]
    exact hmem1
  have hmem3 := hspan3 hmem2
  refine affineSpan_mono ℝ ?_ hmem3
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  tauto

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
  subst ha
  have hlkk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hncW3 : ¬Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlkk]
    exact hncW
  have haffW : v2 ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlkk, ← hl]
    exact haff
  obtain ⟨hx1p, hx2p, hx6p, hnc3⟩ :=
    HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6 hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hpair : ({v1, w (l + k - 1)} : Set V3) =
      ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hl1]
  obtain ⟨e, he, hmem⟩ := w10_lunar_hull_core_p34 s k l w v1 v2 v w1 (w (l + k - 1))
    x1 x2 x6 V E hk hkk hs hmw hncW3 haffW hpair hx1p hx2p hx6p hnc3 hvv2 hw1v2
    hV hE hlun hl hx1 hx2 hx6
  refine ⟨e, he, fun t ht hte => hmem t ?_⟩
  rw [Set.mem_Icc]
  constructor <;> linarith

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
  subst ha
  have hlkk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hncW3 : ¬Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlkk]
    exact hncW
  have haffW : v2 ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlkk, ← hl]
    exact haff
  obtain ⟨hx1p, hx2p, hx6p, hnc3⟩ :=
    HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6 hkk hs hmw hk hl hl1 hx1 hx2 hx6
  have hpair : ({v1, w (l + k - 1)} : Set V3) =
      ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hl1]
  obtain ⟨e, he, hmem⟩ := w10_lunar_hull_core_p34 s k l w v1 v2 v w1 (w (l + k - 1))
    x1 x2 x6 V E hk hkk hs hmw hncW3 haffW hpair hx1p hx2p hx6p hnc3 hvv2 hw1v2
    hV hE hlun hl hx1 hx2 hx6
  exact ⟨e, he, hmem⟩

/-! ## Section 3: the composite registry arrows -/

/-- `Lunar v w` is symmetric (`LUNAR_COMM` in the LA1 vocabulary). -/
private theorem w11_lunar_comm (v w : V3) (V : Set V3) (E : Set (Set V3)) :
    Lunar v w V E ↔ Lunar w v V E := by
  have hp : ({v, w} : Set V3) = {w, v} := Set.pair_comm v w
  have hc : ({0, v, w} : Set V3) = {0, w, v} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  simp only [Lunar, hp, hc, ne_comm]

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
  subst ha
  set V : Set V3 := Set.range w with hV
  set E : Set (Set V3) := Set.range (fun i => {w i, w (i + 1)}) with hE
  set FF : Set (V3 × V3) := Set.range (fun i => (w i, w (i + 1))) with hFF
  have hBB : BBsV39 s w := mms_bbs_p34 hmw
  have hta : taustarV39 s w < 0 := by
    have h1 := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h1
    have h2 := h1.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.2.2
  have hcirc : ¬ Circular V E := by
    have h := JKQEWGV2_p23 s w hs (by omega) hBB hta
    simpa [V, E, Set.image_univ] using h
  have hclf : ConvexLocalFan V E FF := by
    have h := BBS_IMP_CONVEX_LOCAL_FAN_p34 s k w hk hkk hBB
    simpa [V, E, FF] using h
  obtain ⟨hx1p, hx2p, hx6p, hnc⟩ :=
    HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6 hkk hs hmw hk hl hl1 hx1 hx2 hx6
  -- the generic/circular/lunar trichotomy of a local fan
  have hlf : LocalFan V E FF := hclf.1
  obtain ⟨hfan, x, hxD, hFFeq, hDih, hreg⟩ := hlf
  have hlf' : LocalFan V E FF := ⟨hfan, x, hxD, hFFeq, hDih, hreg⟩
  have hno : dartsOfHyp_p3 E V = Fan.dart1OfFan V E := hno_of_no_isolated (w10_hedge hreg)
  have hlf3 : localFan_p3 V E FF := localFan_p3.of_LocalFan hlf' hno
  have htri := CIZMRRH hlf3
  -- deformation and interior-angle witnesses
  obtain ⟨e3, he3, hdef3⟩ :=
    V3_DEFOR_DEFORMATION_p34 v1 v2 V x1 x2 x2 x2 x6 (-1) hx1p hx2p hx2p hx2p hx6p
      hnc hx1 hx2 hx6 rfl
  obtain ⟨e4, he4, hang4⟩ :=
    DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
      hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF.symm
  rcases htri with hgen | hcirc3 | hlun3
  · -- (1) generic: the ZLZTHIC arrow applies
    have hgen0 : Generic V E := by
      simpa only [generic_p3, Generic] using hgen.1
    set e1 : ℝ := min e3 e4 / 2 with he1def
    have he1pos : 0 < e1 := by
      have h : 0 < min e3 e4 := lt_min he3 he4
      rw [he1def]; linarith
    have he1lt3 : e1 < e3 := by
      have h2 : min e3 e4 ≤ e3 := min_le_left _ _
      rw [he1def]; nlinarith
    have he1lt4 : e1 < e4 := by
      have h2 : min e3 e4 ≤ e4 := min_le_right _ _
      rw [he1def]; nlinarith
    have hdef1 : Deformation (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) V (-e1) e1 :=
      DEFORMATION_SMALL_INTERVAL_p34 hdef3 (by linarith) (by linarith) he1pos
        (le_of_lt he1lt3)
    have hang1 : ∀ v ∈ V, ∀ t ∈ Icc (-e1) e1,
        interiorAngle1 0 FF v = Real.pi →
        interiorAngle1 0 ((fun d : V3 × V3 => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.1 t,
          v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.2 t)) '' FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi := by
      intro v hv t ht hpi
      exact hang4 v t (hV ▸ hv) (by linarith [ht.1]) (by linarith [ht.2]) hpi
    obtain ⟨eps, heps, hconcl⟩ := hz (-e1) e1 V E FF
      (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) hclf hgen0 hdef1 hang1
    refine ⟨eps, heps, fun t ht => ?_⟩
    have h := (hconcl t ht).1
    rw [V_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        E_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        F_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2, ← hV, ← hE, ← hFF]
    exact h
  · -- (2) circular: excluded by JKQEWGV2
    exact absurd (by simpa only [circular_p3, Circular] using hcirc3.1) hcirc
  · -- (3) lunar: the MHAEYJN arrow applies
    obtain ⟨vv, w1, hlun3'⟩ := hlun3.1
    have hlun : Lunar vv w1 V E := by
      simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hlun3'
    have hang_lt : interiorAngle1 0 FF vv < Real.pi / 2 := by
      have h := JKQEWGV3_p23 s w vv w1 hs hBB (by omega) hta (by
        simpa [V, E, Set.image_univ] using hlun)
      simpa [FF, Set.image_univ] using h
    have hv2V : v2 ∈ V := by
      rw [hV]; exact ⟨l, hl⟩
    have hv2ne_v : v2 ≠ vv := by
      intro h
      have hwl : w l = vv := hl.trans h
      have hneg : ¬ Lunar w1 vv V E := by
        have h' := hlunar V E w1 rfl rfl
        rwa [hwl] at h'
      exact hneg ((w11_lunar_comm vv w1 V E).mp hlun)
    have hv2ne_w1 : v2 ≠ w1 := by
      intro h
      have hneg : ¬ Lunar vv v2 V E := by
        have h' := hlunar V E vv rfl rfl
        rwa [hl] at h'
      exact hneg (h.symm ▸ hlun)
    obtain ⟨e5, he5, haff5⟩ :=
      DEFORMATION_LUNAR_AFFINE_HULL_V1_p34 s k l w v1 v2 vv w1 x1 x2 x6 (-1) V E
        hk hkk hs hmw haz hncW haff hl hl1 (fun h => hn2 h.symm) hx1 hx2 hx6 rfl
        (Ne.symm hv2ne_v) (Ne.symm hv2ne_w1) rfl hV.symm hE.symm hlun
    set e1 : ℝ := min (min e3 e4) e5 / 2 with he1def
    have he1pos : 0 < e1 := by
      have h : 0 < min (min e3 e4) e5 := lt_min (lt_min he3 he4) he5
      rw [he1def]; linarith
    have he1lt3 : e1 < e3 := by
      have h2 : min (min e3 e4) e5 ≤ e3 := (min_le_left _ _).trans (min_le_left _ _)
      rw [he1def]; nlinarith
    have he1lt4 : e1 < e4 := by
      have h2 : min (min e3 e4) e5 ≤ e4 := (min_le_left _ _).trans (min_le_right _ _)
      rw [he1def]; nlinarith
    have he1lt5 : e1 < e5 := by
      have h2 : min (min e3 e4) e5 ≤ e5 := min_le_right _ _
      rw [he1def]; nlinarith
    have hdef1 : Deformation (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) V (-e1) e1 :=
      DEFORMATION_SMALL_INTERVAL_p34 hdef3 (by linarith) (by linarith) he1pos
        (le_of_lt he1lt3)
    have hfix : ∀ u' ∈ V, v2 ≠ u' → ∀ t ∈ Icc (-e1) e1,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 u' t = u' := by
      intro u' _ hu' t _ht
      simp only [v3DeforV4_p34, if_neg (Ne.symm hu')]
    have haffine : ∀ t ∈ Icc (-e1) e1,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈
          affineSpan ℝ ({0, vv, w1, v2} : Set V3) := by
      intro t ht
      exact haff5 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨eps, heps, hconcl⟩ := hm (-e1) e1 V E FF
      (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) vv w1 v2
      hclf hlun hdef1 (by linarith [Real.pi_pos]) hv2V hv2ne_v hv2ne_w1 hfix haffine
    refine ⟨eps, heps, fun t ht => ?_⟩
    have h := (hconcl t ht).1
    rw [V_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        E_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        F_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2, ← hV, ← hE, ← hFF]
    exact h

/-- `_p28`-style quasi-injectivity of an `BBs` realisation, in-file (LA34):
`w x = w y → x % s.k = y % s.k`. Needed by the `ncard` computation below;
`W_IN_BB_FUN_EQ_p28` lives in `LocalAuto28`, which imports this file. -/
private theorem w8_w_in_bb_fun_eq_p34 (s : ScsV39) (w : ℕ → V3) (x y : ℕ)
    (hs : isScsV39 s) (hbb : BBsV39 s w) (h : w x = w y) : x % s.k = y % s.k := by
  have hk0 : 0 < s.k := by have := hs.2.1; omega
  have hper : ∀ i, w (i + s.k) = w i := hbb.2.1
  have hwx : w (x % s.k) = w x := (modFold_p34 hk0 hper x).symm
  have hwy : w (y % s.k) = w y := (modFold_p34 hk0 hper y).symm
  by_contra hne
  have hdist : dist (w (x % s.k)) (w (y % s.k)) = 0 := by
    rw [hwx, hwy, h, dist_self]
  have hle := (hbb.2.2.1 (x % s.k) (y % s.k)).1
  rw [hdist] at hle
  have h2le : 2 ≤ s.a (x % s.k) (y % s.k) :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (x % s.k) (y % s.k)
      ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, hne⟩
  linarith

/-- The edge range of a `BBs` realisation has exactly `k` distinct darts. -/
private theorem w8_card_ff_p34 (s : ScsV39) (w : ℕ → V3) (k : ℕ) (hkk : s.k = k)
    (hk : 3 < k) (hs : isScsV39 s) (hbb : BBsV39 s w) :
    (Set.range fun i : ℕ => (w i, w (i + 1))).ncard = k := by
  have hk0 : 0 < s.k := by have := hs.2.1; omega
  have hper : ∀ i, w (i + s.k) = w i := hbb.2.1
  set g : ℕ → V3 × V3 := fun i => (w i, w (i + 1)) with hg
  have hmods : ∀ i : ℕ, g (i % s.k) = g i := by
    intro i
    have h1 : w (i % s.k) = w i := (modFold_p34 hk0 hper i).symm
    have h2 : w (i % s.k + 1) = w (i + 1) := by
      rw [modFold_p34 hk0 hper (i % s.k + 1), modFold_p34 hk0 hper (i + 1)]
      congr 1
      rw [Nat.add_mod i 1 (s.k), Nat.mod_eq_of_lt (by omega : 1 < s.k)]
    simp only [hg, h1, h2]
  have hrange : Set.range g = g '' {i : ℕ | i < k} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i % s.k, ?_, hmods i⟩
      have hlt := Nat.mod_lt i hk0
      simpa [hkk] using hlt
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  have hinj : Set.InjOn g {i : ℕ | i < k} := by
    intro i hi j hj he
    simp only [hg, Prod.mk.injEq] at he
    by_contra hne
    have hne' : i % s.k ≠ j % s.k := by
      intro hc
      have hc' : i % k = j % k := by rwa [hkk] at hc
      exact hne (by rw [← Nat.mod_eq_of_lt hi, ← Nat.mod_eq_of_lt hj, hc'])
    have hle : s.a (i % s.k) (j % s.k) ≤ dist (w i) (w j) := by
      rw [modFold_p34 hk0 hper i, modFold_p34 hk0 hper j]
      exact (hbb.2.2.1 (i % s.k) (j % s.k)).1
    rw [he.1, dist_self] at hle
    have h2le : 2 ≤ s.a (i % s.k) (j % s.k) :=
      hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % s.k) (j % s.k)
        ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, hne'⟩
    linarith
  rw [hrange, Set.ncard_image_of_injOn hinj]
  exact Set.ncard_Iio_nat k

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
  intro t ht0 hte
  have h1 := w8_card_ff_p34 s w k hkk hk hs hBB
  have h2 := w8_card_ff_p34 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t) k hkk hk hs
    (hBBd t ht0 hte)
  rw [h2, h1]

private theorem w8_periodic2_mod_r {α : Sort*} {f : ℕ → ℕ → α} {k : ℕ}
    (hp : Periodic2 f k) (i m : ℕ) : f i m = f i (m % k) := by
  have h1 : f i m = f i (m % k + m / k * k) := by
    conv_lhs => rw [(Nat.mod_add_div m k).symm, Nat.mul_comm k (m / k)]
  rw [h1]
  induction m / k with
  | zero => simp
  | succ n ih =>
      have hrw : m % k + (n + 1) * k = (m % k + n * k) + k := by ring
      rw [hrw, (hp i (m % k + n * k)).2, ih]

/-- HOL `EQ_SUC_K_SUB` (NUXCOEA.hl:156), local copy (LA28 imports this file). -/
private theorem w8_eq_suc_k_sub {k l i : ℕ} (h : l % k = (i + 1) % k) (hk : 1 < k) :
    (l + k - 1) % k = i % k := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h0k : 0 < k := by omega
    have hm : i % k < k := Nat.mod_lt _ h0k
    have h2 : i % k + 1 = k := by
      have h1 : (i + 1) % k = 0 := by simpa using h.symm
      rw [Nat.add_mod, Nat.mod_eq_of_lt hk] at h1
      rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h1; omega
      · have hsub : i % k + 1 - k < k := by omega
        have e : i % k + 1 = i % k + 1 - k + k := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hsub] at h1
        omega
    rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
    omega
  · have h' : ((l - 1) + 1) % k = (i + 1) % k := by rwa [Nat.sub_add_cancel hl]
    have h'' : (l - 1) % k = i % k := Nat.ModEq.add_right_cancel' 1 h'
    have e1 : l + k - 1 = (l - 1) + k := by omega
    rw [e1, Nat.add_mod_right]
    exact h''

private theorem w8_setSum_congr {S : Set ℕ} (hS : S.Finite) {f g : ℕ → ℝ}
    (h : ∀ i ∈ S, f i = g i) : setSum S f = setSum S g := by
  unfold setSum
  rw [dif_pos hS, dif_pos hS]
  exact Finset.sum_congr rfl fun i hi => h i (hS.mem_toFinset.mp hi)

/-- HOL `DSV_V3_DEFOR_EQ` (IMJXPHR.hl:5842). -/
theorem DSV_V3_DEFOR_EQ_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 : V3) (t a x1 x2 x6 : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hBB : BBsV39 s w)
    (hJ : ∀ i, ¬s.J l i) :
    dsvV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 (w l) (w i) t) = dsvV39 s w := by
  have hk0 : 0 < s.k := by have := hs.2.1; omega
  have hJper : Periodic2 s.J s.k := hs.2.2.2.2.2.2.2.2.2.2.2.1
  have hJsym : ∀ i j, s.J i j = s.J j i :=
    fun i j => (hs.2.2.2.2.2.2.2.2.2.2.2.2.1 i j).2.2.2.2
  have hjmod : ∀ i j : ℕ, s.J (i % s.k) (j % s.k) = s.J i j := by
    intro i j
    calc s.J (i % s.k) (j % s.k) = s.J (j % s.k) (i % s.k) := hJsym _ _
      _ = s.J (j % s.k) i := (w8_periodic2_mod_r hJper (j % s.k) i).symm
      _ = s.J i (j % s.k) := hJsym _ _
      _ = s.J i j := (w8_periodic2_mod_r hJper i j).symm
  have hne_l : ∀ i : ℕ, s.J i (i + 1) → w i ≠ w l := by
    intro i hi heq
    have hres : i % s.k = l % s.k := w8_w_in_bb_fun_eq_p34 s w i l hs hBB heq
    have hres1 : (i + 1) % s.k = (l + 1) % s.k := Nat.ModEq.add_right 1 hres
    have hJli : s.J l (l + 1) := by
      have h1 : s.J l (l + 1) = s.J (l % s.k) ((l + 1) % s.k) := (hjmod l (l + 1)).symm
      have h2 : s.J (l % s.k) ((l + 1) % s.k) = s.J (i % s.k) ((i + 1) % s.k) := by
        rw [← hres, ← hres1]
      have h3 : s.J (i % s.k) ((i + 1) % s.k) = s.J i (i + 1) := hjmod i (i + 1)
      rw [h1, h2, h3]
      exact hi
    exact hJ (l + 1) hJli
  have hne_succ : ∀ i : ℕ, s.J i (i + 1) → w (i + 1) ≠ w l := by
    intro i hi heq
    have hres : (i + 1) % s.k = l % s.k := w8_w_in_bb_fun_eq_p34 s w (i + 1) l hs hBB heq
    have hpred : (l + s.k - 1) % s.k = i % s.k :=
      w8_eq_suc_k_sub hres.symm (by have := hs.2.1; omega)
    have hJli : s.J l (l + s.k - 1) := by
      have h1 : s.J l (l + s.k - 1) = s.J (l % s.k) ((l + s.k - 1) % s.k) :=
        (hjmod l (l + s.k - 1)).symm
      have h2 : s.J (l % s.k) ((l + s.k - 1) % s.k) = s.J (i % s.k) ((i + 1) % s.k) := by
        rw [hpred, hres, hJsym (l % s.k) (i % s.k)]
      have h3 : s.J (i % s.k) ((i + 1) % s.k) = s.J i (i + 1) := hjmod i (i + 1)
      rw [h1, h2, h3]
      exact hi
    exact hJ (l + s.k - 1) hJli
  have hfin : {i : ℕ | i < s.k ∧ s.J i (i + 1)}.Finite :=
    (Set.finite_Iio s.k).subset (fun i hi => hi.1)
  have hsum : setSum {i : ℕ | i < s.k ∧ s.J i (i + 1)}
      (fun i => cstab - dist (v3DeforV4_p34 a x1 x2 x6 v1 (w l) (w i) t)
        (v3DeforV4_p34 a x1 x2 x6 v1 (w l) (w (i + 1)) t))
      = setSum {i : ℕ | i < s.k ∧ s.J i (i + 1)}
          (fun i => cstab - dist (w i) (w (i + 1))) := by
    refine w8_setSum_congr hfin ?_
    intro i hi
    have hwi : w i ≠ w l := hne_l i hi.2
    have hwi1 : w (i + 1) ≠ w l := hne_succ i hi.2
    rw [v3DeforV4_p34, if_neg hwi, v3DeforV4_p34, if_neg hwi1]
  simp only [dsvV39]
  rw [hsum]

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
  obtain ⟨e, he, h⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨e, he, fun v t hv ht1 ht2 => ?_⟩
  simpa only [interiorAngle1, ivsRhoNode1, epPair_p34] using h t v ⟨ht1, ht2⟩ hv

/-- `sol0 > 0` (appendix constant; `sol0 = 3·arccos(1/3) − π`). -/
private theorem w5cC5_sol0_pos : 0 < sol0 := by
  have harc : Real.pi / 3 < Real.arccos (1 / 3) := by
    have h := Real.arccos_lt_arccos (x := (1 : ℝ) / 3) (y := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    rw [show Real.arccos (1 / 2) = Real.pi / 3 from ?_] at h
    · exact h
    · rw [← Real.cos_pi_div_three]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  unfold sol0
  linarith

/-- `rhoFun` is strictly increasing (`(1/(2h0−2))·(1/π)·sol0 > 0`). -/
private theorem w5cC5_rhoFun_lt {y z : ℝ} (h : y < z) : rhoFun y < rhoFun z := by
  have hcoef : 0 < (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 := by
    have h0' : 0 < 2 * h0 - 2 := by unfold h0; norm_num
    have hp : 0 < Real.pi := Real.pi_pos
    have hs : 0 < sol0 := w5cC5_sol0_pos
    positivity
  unfold rhoFun
  nlinarith [h, hcoef]

/-- HOL `RHO_FUN_DEFORMATION_V3_DEFOR` (IMJXPHR.hl:6009). -/
theorem RHO_FUN_DEFORMATION_V3_DEFOR_p34 (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      rhoFun ‖(v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) : V3)‖ < rhoFun ‖v2‖ := by
  subst ha
  obtain ⟨eU, heU, hU⟩ := UPS_X_POS_SEG_p34 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6 hx2p
  refine ⟨min eU 1, lt_min heU one_pos, fun t ht => ?_⟩
  have htU : t < eU := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_right _ _)
  obtain ⟨hup, hx2t⟩ := hU t ⟨by linarith [ht.1], htU⟩
  set v3 : V3 := v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) with hv3def
  have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
      ((-1 / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3 := by
    rw [hv3def]
    rfl
  have hnorm3 : ‖v3‖ ^ 2 = x2 - t := by
    rw [hv3def]
    exact EYYPQDW_NORMV3_p17 v1 v2 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
      x1 x2 (x2 - t) x6 x6 x6 (-1) hx1p hx2p hx2t hx6p hx6p hx6p hnc hx1 hx2 hx6
      (by norm_num) hup hv3
  have hn3 : ‖v3‖ = Real.sqrt (x2 - t) := by
    rw [← hnorm3]
    exact (Real.sqrt_sq (norm_nonneg v3)).symm
  have hn2 : ‖v2‖ = Real.sqrt x2 := by
    rw [← hx2]
    exact (Real.sqrt_sq (norm_nonneg v2)).symm
  have hlt : ‖v3‖ < ‖v2‖ := by
    rw [hn3, hn2]
    exact Real.sqrt_lt_sqrt hx2t.le (by linarith)
  exact w5cC5_rhoFun_lt hlt

/-! ### W9: rho-orbit iteration kit (local twin of LA35 `VV_SUC_EQ_RHO_NODE_PRIME`) -/

/-- `rhoNode1` on a range face at `vv j` is the successor `vv (j+1)`, for an
abstract periodic/injective cyclic sequence (generalises
`w5cC4_rhoNode1_range_p34` from `MMs` membership to any such `vv`; the
deformed sequence is only known to be a `BBs` realisation). -/
private theorem w9_rhoNode1_range_p34 {vv : ℕ → V3} {k j : ℕ} {FF : Set (V3 × V3)}
    (hk0 : 0 < k) (hk1 : 1 < k) (hper : ∀ i, vv (i + k) = vv i)
    (hinj : ∀ i j : ℕ, i % k ≠ j % k → vv i ≠ vv j)
    (hFF : Set.range (fun i : ℕ => (vv i, vv (i + 1))) = FF) :
    rhoNode1 FF (vv j) = vv (j + 1) := by
  have hmem : ∀ a b : V3, (a, b) ∈ FF → ∃ i : ℕ, vv i = a ∧ vv (i + 1) = b :=
    fun a b => ff_edge_index_p34 hFF
  rw [rhoNode1]
  refine epsilon_eq_of_p34 ?_ ?_
  · intro y hy
    obtain ⟨i, hi1, hi2⟩ := hmem (vv j) y hy
    have hres : i % k = j % k := by
      by_contra hne
      exact hinj i j hne hi1
    rw [← hi2, modFold_p34 hk0 hper (i + 1), res_succ_congr_p34 hk1 hres,
      ← modFold_p34 hk0 hper (j + 1)]
  · have h : (vv j, vv (j + 1)) ∈ Set.range (fun i : ℕ => (vv i, vv (i + 1))) := ⟨j, rfl⟩
    rwa [hFF] at h

/-- The `rhoNode1` orbit follows the cyclic ordering (HOL
`VV_SUC_EQ_RHO_NODE_PRIME`, iterated; QKNVMLB.hl:4024). -/
private theorem w9_rhoOrbit_p34 {vv : ℕ → V3} {k : ℕ} {FF : Set (V3 × V3)}
    (hk0 : 0 < k) (hk1 : 1 < k) (hper : ∀ i, vv (i + k) = vv i)
    (hinj : ∀ i j : ℕ, i % k ≠ j % k → vv i ≠ vv j)
    (hFF : Set.range (fun i : ℕ => (vv i, vv (i + 1))) = FF) (p1 : ℕ) :
    ∀ m : ℕ, (rhoNode1 FF)^[m] (vv p1) = vv (m + p1) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [w9_rhoNode1_range_p34 hk0 hk1 hper hinj hFF]
    congr 1
    omega

/-- Distinct residues give distinct vertices on a `BBs` realisation (the
`w_inj_p34` argument with `MMs` membership replaced by `BBs`; needed for the
deformed sequence). -/
private theorem w9_bbs_inj_p34 {s : ScsV39} {k : ℕ} {vv : ℕ → V3}
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hBB : BBsV39 s vv) :
    ∀ i j : ℕ, i % k ≠ j % k → vv i ≠ vv j := by
  have hk0 : 0 < k := by omega
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  intro i j hij hcon
  have h2le : 2 ≤ s.a (i % k) (j % k) :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % k) (j % k)
      ⟨by rw [hkk]; exact Nat.mod_lt _ hk0, by rw [hkk]; exact Nat.mod_lt _ hk0, hij⟩
  have hper : ∀ q, vv (q + k) = vv q := by
    intro q
    rw [← hkk]
    exact hBB.2.1 q
  have hw1 : vv i = vv (i % k) := modFold_p34 hk0 hper i
  have hw2 : vv j = vv (j % k) := modFold_p34 hk0 hper j
  have hle : s.a (i % k) (j % k) ≤ dist (vv i) (vv j) := by
    rw [hw1, hw2]
    exact (hBB.2.2.1 (i % k) (j % k)).1
  rw [hcon, dist_self] at hle
  exact absurd hle (by linarith)

/-- The face of a pointwise-deformed cyclic sequence is the image face
(unfolds `deformedFF4_p34`). -/
private theorem w9_deformedFF_range_p34 {w : ℕ → V3} {FF : Set (V3 × V3)}
    (f : V3 → V3) (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF) :
    Set.range (fun i : ℕ => (f (w i), f (w (i + 1))))
      = (fun d : V3 × V3 => (f d.1, f d.2)) '' FF := by
  rw [← hFF]
  exact Set.range_comp (fun d : V3 × V3 => (f d.1, f d.2))
    (fun i : ℕ => (w i, w (i + 1)))

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
  subst ha
  obtain ⟨e, he, hEq⟩ := DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_p34 s k l w v1 v2
    x1 x2 x6 (-1) FF hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc
    hx1 hx2 hx6 rfl hFF
  refine ⟨min e e1, lt_min he he1, fun t i ht0 hte => ?_⟩
  have hte' : t < e := lt_of_lt_of_le hte (min_le_left _ _)
  have hte1 : t < e1 := lt_of_lt_of_le hte (min_le_right _ _)
  have hper : ∀ q, w (q + k) = w q := MMs_periodic_p34 s k w hkk hmw
  have hinj : ∀ i j : ℕ, i % k ≠ j % k → w i ≠ w j :=
    fun i j h => w_inj_p34 hk hkk hs hmw i j h
  have horb := w9_rhoOrbit_p34 (vv := w) (k := k) (FF := FF) (by omega) (by omega) hper
    hinj hFF (l % k) i
  have hBB := hBBd t ht0 hte1
  have hperd : ∀ q, v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (q + k)) t
      = v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w q) t := by
    intro q
    rw [← hkk]
    exact hBB.2.1 q
  have hFFd : Set.range (fun q : ℕ => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w q) t,
      v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (q + 1)) t))
      = deformedFF4_p34 x1 x2 x6 v1 v2 t FF :=
    w9_deformedFF_range_p34 (f := fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) hFF
  have horbd := w9_rhoOrbit_p34
    (vv := fun q => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w q) t)
    (k := k) (FF := deformedFF4_p34 x1 x2 x6 v1 v2 t FF) (by omega) (by omega) hperd
    (w9_bbs_inj_p34 hk hkk hs hBB) hFFd (l % k) i
  rw [horbd, horb]
  exact hEq (w (i + l % k)) t ⟨i + l % k, rfl⟩ (by linarith) hte'

/-- Common core of the two `TAUSTAR_V3_DEFOR` twins: one `v3_defor_v4` step
at `v2` strictly decreases `taustar_v39`, given the pointwise interior-angle
constancy `hang` (supplied by the corresponding `INTERIOR_ANGLE_SAME_*`
lemma) and the `BBs` deformation hypothesis.  The `tau_fun` comparison is
termwise: the `i = 0` summand contracts because `rho_fun ∘ norm` contracts at
the moving point `v2` and the undirected interior angle is positive, while
every later summand is unchanged (the deformation fixes the vertices
`w (i + l % k) ≠ w l`). -/
private theorem w12_taustar_core_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (x1 x2 x6 e1 : ℝ) (v1 v2 : V3)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2)
    (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (hJ : ∀ i, ¬s.J l i)
    (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
      BBsV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t))
    (he1 : 0 < e1)
    (hang : ∃ eA : ℝ, 0 < eA ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < eA →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t
          (Set.range fun i : ℕ => (w i, w (i + 1))))
        ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t
          (Set.range fun i : ℕ => (w i, w (i + 1)))))^[i]
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 (Set.range fun i : ℕ => (w i, w (i + 1)))
        ((rhoNode1 (Set.range fun i : ℕ => (w i, w (i + 1))))^[i] (w (l % k)))) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
      taustarV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t) <
        taustarV39 s w := by
  obtain ⟨eA, heA, hAng⟩ := hang
  have hsk0 : 0 < s.k := by have := hs.2.1; omega
  have hsk3 : ¬ s.k ≤ 3 := by omega
  have hBB : BBsV39 s w := mms_bbs_p34 hmw
  have hwl : w (l % s.k) = v2 := by
    rw [(modFold_p34 hsk0 hBB.2.1 l).symm, hl]
  have hlmod : l % s.k = l % k := by rw [hkk]
  have hwlk : w (l % k) = v2 := by rw [← hlmod]; exact hwl
  set V : Set V3 := Set.range w with hVdef
  set E : Set (Set V3) := Set.range fun i => ({w i, w (i + 1)} : Set V3) with hEdef
  set FF : Set (V3 × V3) := Set.range fun i => (w i, w (i + 1)) with hFFdef
  obtain ⟨eR, heR, hRho⟩ :=
    RHO_FUN_DEFORMATION_V3_DEFOR_p34 v1 v2 x1 x2 x6 (-1)
      hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl
  have hcard : ∀ t : ℝ, 0 < t → t < e1 →
      (Set.range (fun i : ℕ => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + 1)) t))).ncard =
      (Set.range fun i : ℕ => (w i, w (i + 1))).ncard :=
    CARD_FF_EQ_V3_DEFOR_DEFORMATION_p34 s k w V v1 v2 x1 x2 x6 (-1) e1
      hkk rfl hs hk hBB hBBd
  have hpos : 0 < interiorAngle1 0 FF (w (l % s.k)) := by
    have hclf : ConvexLocalFan V E FF := by
      have h := BBS_IMP_CONVEX_LOCAL_FAN_p34 s k w hk hkk hBB
      simpa only [V, E, FF] using h
    obtain ⟨-, -, -, -, -, h2reg⟩ := hclf.1
    have hno : dartsOfHyp_p3 E V = Fan.dart1OfFan V E := hno_of_no_isolated (w10_hedge h2reg)
    have hlf2 : localFan_p2 V E FF :=
      localFan_p2.of_localFan_p3 (localFan_p3.of_LocalFan hclf.1 hno)
    exact INTERIOR_ANGLE1_POS hlf2 (v := w (l % s.k)) ⟨l % s.k, rfl⟩
  set e : ℝ := min (min eA eR) e1 / 2 with hedef
  refine ⟨e, ?_, ?_⟩
  · have h3 : 0 < min (min eA eR) e1 := lt_min (lt_min heA heR) he1
    rw [hedef]; linarith
  · intro t ht
    obtain ⟨ht0, hte⟩ := ht
    have hA : t < eA := by
      have hle : min (min eA eR) e1 ≤ eA := (min_le_left _ _).trans (min_le_left _ _)
      rw [hedef] at hte; linarith
    have hR : t < eR := by
      have hle : min (min eA eR) e1 ≤ eR := (min_le_left _ _).trans (min_le_right _ _)
      rw [hedef] at hte; linarith
    have h1e : t < e1 := by
      have hle : min (min eA eR) e1 ≤ e1 := min_le_right _ _
      rw [hedef] at hte; linarith
    set w' : ℕ → V3 := fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t with hw'def
    have hBB' : BBsV39 s w' := by
      rw [hw'def]
      exact hBBd t ht0 h1e
    set E' : Set (Set V3) := Set.range fun i => ({w' i, w' (i + 1)} : Set V3) with hE'def
    set FF' : Set (V3 × V3) := Set.range fun i => (w' i, w' (i + 1)) with hFF'def
    have hFF'eq : FF' = deformedFF4_p34 x1 x2 x6 v1 v2 t FF := by
      rw [hFF'def, hw'def, hFFdef]
      exact F_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2
    set g' : ℕ → ℝ := fun i => rhoFun ‖w' (i + l % s.k)‖ *
      interiorAngle1 0 FF' ((rhoNode1 FF')^[i] (w' (l % s.k))) with hg'def
    set g : ℕ → ℝ := fun i => rhoFun ‖w (i + l % s.k)‖ *
      interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % s.k))) with hgdef
    have hSz' : setSum {i | i < s.k} g' = setSum FF' (fun e => rhoFun ‖e.1‖ * azimInFan e E') :=
      SUM_AZIM_EQ_ANGLE_LE4_p35 s l 0 (w' (l % s.k)) (Set.range w') E' FF' w'
        hsk3 hBB' hs rfl rfl rfl rfl
    have hSz : setSum {i | i < s.k} g = setSum FF (fun e => rhoFun ‖e.1‖ * azimInFan e E) :=
      SUM_AZIM_EQ_ANGLE_LE4_p35 s l 0 (w (l % s.k)) V E FF w
        hsk3 hBB hs rfl rfl rfl rfl
    have hsetSum : ∀ (f : ℕ → ℝ) (K : ℕ),
        setSum {i | i < K} f = ∑ i ∈ Finset.range K, f i := by
      intro f K
      rw [setSum]
      have hfin : {i | i < K}.Finite := Set.finite_Iio K
      rw [dif_pos hfin]
      have hEq : hfin.toFinset = Finset.range K := by
        ext i
        simp [Set.mem_toFinset, Finset.mem_range]
      rw [hEq]
    have hterm0 : g' 0 < g 0 := by
      have hg'0 : g' 0 = rhoFun ‖v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % s.k)) t‖ *
          interiorAngle1 0 FF' (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % s.k)) t) := by
        rw [hg'def]
        simp only [hw'def, Nat.zero_add, Function.iterate_zero_apply]
      have hg0 : g 0 = rhoFun ‖w (l % s.k)‖ * interiorAngle1 0 FF (w (l % s.k)) := by
        rw [hgdef]
        simp only [Nat.zero_add, Function.iterate_zero_apply]
      rw [hg'0, hg0, hlmod]
      have hAng0 : interiorAngle1 0 FF'
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t) =
          interiorAngle1 0 FF (w (l % k)) := by
        have h := hAng t 0 ht0 hA
        rw [← hFF'eq] at h
        simpa only [Function.iterate_zero_apply] using h
      rw [hAng0]
      have hrho0 : rhoFun ‖v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t‖ <
          rhoFun ‖w (l % k)‖ := by
        have hwv : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t =
            v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
          rw [hwlk]
          exact if_pos rfl
        rw [hwv, hwlk]
        exact hRho t ⟨ht0, hR⟩
      have hposk : 0 < interiorAngle1 0 FF (w (l % k)) := by
        rw [← hlmod]
        exact hpos
      exact mul_lt_mul_of_pos_right hrho0 hposk
    have htail : ∀ i ∈ Finset.range (s.k - 1), g' (i + 1) = g (i + 1) := by
      intro i hi
      have hiK : i + 1 < s.k := by
        have := Finset.mem_range.mp hi
        omega
      have hres : (i + 1 + l % s.k) % s.k ≠ (l % s.k) % s.k := by
        have hm : l % s.k < s.k := Nat.mod_lt _ hsk0
        intro h
        rcases Nat.lt_or_ge (i + 1 + l % s.k) s.k with h2 | h2
        · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hm] at h
          omega
        · have h3 : i + 1 + l % s.k - s.k < s.k := by omega
          rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hm] at h
          have h4 : i + 1 + l % s.k = (i + 1 + l % s.k - s.k) + s.k := by omega
          rw [h] at h4
          omega
      have hfix : w' (i + 1 + l % s.k) = w (i + 1 + l % s.k) := by
        have hres' : (i + 1 + l % s.k) % k ≠ (l % s.k) % k := by
          rw [← hkk]
          exact hres
        have hne : w (i + 1 + l % s.k) ≠ v2 := by
          intro he
          exact w_inj_p34 hk hkk hs hmw (i + 1 + l % s.k) (l % s.k) hres' (by rw [he, hwl])
        show v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + 1 + l % s.k)) t =
          w (i + 1 + l % s.k)
        simp only [v3DeforV4_p34, if_neg hne]
      have hAngj : interiorAngle1 0 FF' ((rhoNode1 FF')^[i + 1] (w' (l % s.k))) =
          interiorAngle1 0 FF ((rhoNode1 FF)^[i + 1] (w (l % s.k))) := by
        have h := hAng t (i + 1) ht0 hA
        rw [← hFF'eq] at h
        simpa only [hw'def, hlmod] using h
      have hg'j : g' (i + 1) = rhoFun ‖w' (i + 1 + l % s.k)‖ *
          interiorAngle1 0 FF' ((rhoNode1 FF')^[i + 1] (w' (l % s.k))) := by
        rw [hg'def]
      have hgj : g (i + 1) = rhoFun ‖w (i + 1 + l % s.k)‖ *
          interiorAngle1 0 FF ((rhoNode1 FF)^[i + 1] (w (l % s.k))) := by
        rw [hgdef]
      rw [hg'j, hgj, hfix, hAngj]
    have hsum_lt : setSum {i | i < s.k} g' < setSum {i | i < s.k} g := by
      rw [hsetSum g' s.k, hsetSum g s.k]
      rw [show s.k = s.k - 1 + 1 from (Nat.sub_add_cancel (by omega)).symm]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      exact add_lt_add_of_le_of_lt (le_of_eq (Finset.sum_congr rfl htail)) hterm0
    have hcard' : FF'.ncard = FF.ncard := by
      rw [hFF'def, hw'def, hFFdef]
      exact hcard t ht0 h1e
    have htau : tauFun (Set.range w') E' FF' < tauFun V E FF := by
      simp only [tauFun]
      rw [← hSz', ← hSz, hcard']
      exact sub_lt_sub_right hsum_lt _
    have hdsv : dsvV39 s w' = dsvV39 s w := by
      rw [hw'def, ← hl]
      exact DSV_V3_DEFOR_EQ_p34 s k l w v1 t (-1) x1 x2 x6 hkk hs hBB hJ
    have hL : taustarV39 s w' = tauFun (Set.range w') E' FF' - dsvV39 s w' := by
      rw [taustarV39, if_neg hsk3]
    have hR : taustarV39 s w = tauFun V E FF - dsvV39 s w := by
      rw [taustarV39, if_neg hsk3]
    rw [hL, hR, hdsv]
    exact sub_lt_sub_right htau _

/-- HOL `TAUSTAR_V3_DEFOR` (IMJXPHR.hl:6140; statement `TAUSTAR_V3_DEFOR_concl`,
IMJXPHR.hl:6119). -/
theorem TAUSTAR_V3_DEFOR_p34 : TAUSTAR_V3_DEFOR_concl_p34 := by
  intro s k w l x1 x2 x6 a e1 v1 v2 hk hkk hs hmw hl hl1 hx1p hx2p hx6p
    haz hncW haff hnc hx1 hx2 hx6 ha hn2 hJ hBBd he1
  subst ha
  have hang : ∃ eA : ℝ, 0 < eA ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < eA →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t
          (Set.range fun i : ℕ => (w i, w (i + 1))))
        ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t
          (Set.range fun i : ℕ => (w i, w (i + 1)))))^[i]
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 (Set.range fun i : ℕ => (w i, w (i + 1)))
        ((rhoNode1 (Set.range fun i : ℕ => (w i, w (i + 1))))^[i] (w (l % k))) :=
    INTERIOR_ANGLE_SAME_V3_DEFOR1_p34 s k l w v1 v2 x1 x2 x6 (-1) e1
      (Set.range fun i : ℕ => (w i, w (i + 1)))
      hk hkk hs hmw hl hl1 hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hBBd he1 rfl
  exact w12_taustar_core_p34 s k l w x1 x2 x6 e1 v1 v2 hk hkk hs hmw hl
    hx1p hx2p hx6p hnc hx1 hx2 hx6 hJ hBBd he1 hang

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
  have hper : w ((l + k - 1) + 1) = w l := by
    have e : (l + k - 1) + 1 = l + k := by omega
    rw [e]
    exact MMs_periodic_p34 s k w hkk hmw l
  have h := HYPER_MM_COLLINEAR_p34 s k (l + k - 1) w v2 v1 x2 x1 x6 hkk hs hmw hk
    hlk (by rw [hper, hl]) hx2 hx1 (by rw [norm_sub_rev]; exact hx6)
  obtain ⟨h2, h1, h6, hnc⟩ := h
  refine ⟨h1, h2, h6, ?_⟩
  intro hc
  apply hnc
  have e : ({0, v1, v2} : Set V3) = ({0, v2, v1} : Set V3) := by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rwa [e] at hc

/-- `_TWO_CASES` twin of `HYPER_MM_COLLINEAR_p34`: the non-collinear
neighbour is `w (l+k-1)` (the predecessor edge) instead of `w (l+1)`. -/
private theorem w5cC5_hyper_mm_collinear_tc_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hk : 3 < k)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    0 < x1 ∧ 0 < x2 ∧ 0 < x6 ∧ ¬Collinear ℝ ({0, v1, v2} : Set V3) := by
  have hBB : BBsV39 s w := by
    have h := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h
    have h2 := h.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.1
  have hclf := BBS_IMP_CONVEX_LOCAL_FAN_p34 s k w hk hkk hBB
  obtain ⟨hlf, -⟩ := hclf
  obtain ⟨hfan, -, -, -, -, -⟩ := hlf
  obtain ⟨-, -, -, -, hfan6, -⟩ := hfan
  have hperw : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have hed : ({v2, v1} : Set V3) ∈
      Set.range (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) := by
    refine ⟨l + k - 1, ?_⟩
    show ({w (l + k - 1), w (l + k - 1 + 1)} : Set V3) = ({v2, v1} : Set V3)
    rw [show l + k - 1 + 1 = l + k by omega, hperw l, hlk, hl]
    exact (Set.pair_comm v2 v1).symm
  have hncins := hfan6 ({v2, v1} : Set V3) hed
  have hnc' : ¬ Collinear ℝ ({0, v1, v2} : Set V3) := by
    intro hc
    apply hncins
    have hset : ({0, v2, v1} : Set V3) = ({0, v1, v2} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset]
  exact (NORM_POS_COLLINEAR_p34 v1 v2 x1 x2 x6 hnc' hx1 hx2 hx6).imp id
    (fun h => ⟨h.1, h.2, hnc'⟩)

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
  intro j hj1 hj2
  obtain ⟨h1, h2, h6, hnc⟩ := w5cC5_hyper_mm_collinear_tc_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w j) x1 x2 x6 a (s.a l j) h1 h2 h6 hnc
    hx1 hx2 hx6 ha (hbound j hj1 hj2)

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
  intro j hj1 hj2
  obtain ⟨h1, h2, h6, hnc⟩ := w5cC5_hyper_mm_collinear_tc_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w j) x1 x2 x6 a (s.a l j) h1 h2 h6 hnc
    hx1 hx2 hx6 ha (hbound j hj1 hj2)

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
  intro i hdiag_i
  obtain ⟨h1, h2, h6, hnc⟩ := w5cC5_hyper_mm_collinear_tc_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hBB := w5cC3_mms_bbs_p34 hmw
  have hv2 : v2 ∈ ballAnnulus := by
    have := hBB.1 (Set.mem_range.mpr ⟨l, rfl⟩)
    rwa [hl] at this
  have hwi : w i ∈ ballAnnulus := hBB.1 (Set.mem_range.mpr ⟨i, rfl⟩)
  have hdv : dist v2 0 ≤ 2 * h0 :=
    Metric.mem_closedBall.mp hv2.1
  have hdw : dist (w i) 0 ≤ 2 * h0 :=
    Metric.mem_closedBall.mp hwi.1
  have htri : dist v2 (w i) ≤ dist v2 0 + dist 0 (w i) := dist_triangle v2 0 (w i)
  have h4 : dist v2 (w i) ≤ 4 * h0 := by
    rw [dist_comm 0 (w i)] at htri
    linarith
  exact EXISTS_SMALL_LT_CONST_p34 v1 v2 (w i) x1 x2 x6 a (s.b l i)
    h1 h2 h6 hnc hx1 hx2 hx6 ha (lt_of_le_of_lt h4 (hdiag i hdiag_i))

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
  obtain ⟨h1, h2, h6, hnc⟩ := w5cC5_hyper_mm_collinear_tc_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hk0 : 0 < k := by omega
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  have hik : i % k < k := Nat.mod_lt _ hk0
  have hlkm : l % k < k := Nat.mod_lt _ hk0
  have hne : i % k ≠ l % k := by
    intro h
    exact w5cC3_mod_ne_succ_p34 (by omega) (hmod.trans h).symm
  have h2res : 2 ≤ s.a (i % k) (l % k) :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (i % k) (l % k)
      ⟨by rw [hkk]; exact hik, by rw [hkk]; exact hlkm, hne⟩
  have e1 : s.a l i = s.a l (i % k) := modFold_p34 hk0 (fun q => (hpa l q).2) i
  have e2 : s.a l (i % k) = s.a (i % k) l :=
    (hs.2.2.2.2.2.2.2.2.2.2.2.2.1 l (i % k)).1
  have e3 : s.a (i % k) l = s.a (i % k) (l % k) :=
    modFold_p34 hk0 (fun q => (hpa (i % k) q).2) l
  have h2le : 2 ≤ s.a l i := by rw [e1, e2, e3]; exact h2res
  exact EXISTS_SMALL_LE_CONST_p34 v1 v2 (w i) x1 x2 x6 a 2
    h1 h2 h6 hnc hx1 hx2 hx6 ha (by linarith)

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
  obtain ⟨h1, h2, h6, hnc0⟩ := w5cC5_hyper_mm_collinear_tc_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hk0 : 0 < k := by omega
  have hBB := w5cC3_mms_bbs_p34 hmw
  have hperw := MMs_periodic_p34 s k w hkk hmw
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  -- normalise the `l + (s.k - 1)` index
  have hnW : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hncW' : ¬Collinear ℝ ({0, v1, w (l + 1)} : Set V3) := by
    have hperm : ({0, v1, w (l + 1)} : Set V3)
        = ({0, w (l + 1), w (l + k - 1)} : Set V3) := by
      rw [← hlk]
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hperm, ← hnW]
    exact hncW
  have haff' : w l ∈ affGt {0} ({v1, w (l + 1)} : Set V3) := by
    have hswap : affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3)
        = affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := w5cC5_affGt_pair_swap_p34
    rw [← hlk, hswap, ← hnW]
    exact haff
  -- distinctness from non-collinearity
  have hv1ne : v1 ≠ 0 := by
    intro hv
    apply hncW'
    rw [hv]
    simpa using collinear_pair ℝ (0 : V3) (w (l + 1))
  have hWne : w (l + 1) ≠ 0 := by
    intro hW
    apply hncW'
    rw [hW]
    have hpair : Collinear ℝ ({0, v1} : Set V3) := collinear_pair ℝ (0 : V3) v1
    convert hpair using 1
    ext x; simp [or_comm]
  have hv1W : v1 ≠ w (l + 1) := by
    intro hW
    apply hncW'
    rw [hW]
    simpa using collinear_pair ℝ (0 : V3) (w (l + 1))
  obtain ⟨α, β, hα, hβ, hcoef0⟩ :=
    (affGt_zero_pair_char_p34 hv1ne hWne hv1W).mp haff'
  have hcoef : α • v1 + β • w (l + 1) = v2 := by
    rw [← hl]; exact hcoef0
  -- i and l+k-1 agree
  have hWi : w i = w (l + 1) := by
    rw [modFold_p34 hk0 hperw i, ← hmod, ← modFold_p34 hk0 hperw (l + 1)]
  have ha_lt' : s.a l (l + 1) < dist v2 (w (l + 1)) := by
    have e_a : s.a l i = s.a l (l + 1) := by
      rw [modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) i,
        ← hmod,
        modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) (l + 1)]
    rw [← hWi, ← e_a]
    exact ha_lt
  -- cone certificate inputs
  have hPle : ‖v1‖ ^ 2 ≤ (2 * h0) ^ 2 := by
    have hv1mem : v1 ∈ ballAnnulus := by
      rw [← hlk]
      exact hBB.1 (Set.mem_range.mpr ⟨l + k - 1, rfl⟩)
    have hle : ‖v1‖ ≤ 2 * h0 := by
      have h' := Metric.mem_closedBall.mp hv1mem.1
      rwa [dist_zero_right] at h'
    have h0pos : (0:ℝ) < h0 := by unfold h0; norm_num
    nlinarith [norm_nonneg v1, hle, h0pos]
  have hQle : ‖w (l + 1)‖ ^ 2 ≤ (2 * h0) ^ 2 := by
    have hWmem : w (l + 1) ∈ ballAnnulus :=
      hBB.1 (Set.mem_range.mpr ⟨l + 1, rfl⟩)
    have hle : ‖w (l + 1)‖ ≤ 2 * h0 := by
      have h' := Metric.mem_closedBall.mp hWmem.1
      rwa [dist_zero_right] at h'
    have h0pos : (0:ℝ) < h0 := by unfold h0; norm_num
    nlinarith [norm_nonneg (w (l + 1)), hle, h0pos]
  have hXge : 4 ≤ ‖v2‖ ^ 2 := by
    have hv2mem : v2 ∈ ballAnnulus := by
      rw [← hl]
      exact hBB.1 (Set.mem_range.mpr ⟨l, rfl⟩)
    have h2le : 2 ≤ ‖v2‖ := by
      by_contra hlt
      push_neg at hlt
      exact hv2mem.2 (Metric.mem_ball.mpr (by rwa [dist_zero_right]))
    nlinarith
  have hD1ge : 4 ≤ ‖v2 - v1‖ ^ 2 := by
    have hdist : s.a l (l + k - 1) ≤ dist (w l) (w (l + k - 1)) := (hBB.2.2.1 l (l + k - 1)).1
    rw [hl, hlk] at hdist
    have h2a : 2 ≤ s.a l (l + k - 1) := by
      have hne : l % k ≠ (l + k - 1) % k :=
        fun h => MOD_ADD_SUB_1_p34 (k := k) (l := l) (by omega) h.symm
      exact w5cC4_scsA_ge_two_p34 hk0 hkk hs hne
    have h2d : 2 ≤ dist v2 v1 := le_trans h2a hdist
    rw [dist_eq_norm] at h2d
    nlinarith
  have hD2gt : 4 < ‖v2 - w (l + 1)‖ ^ 2 := by
    have h2a : 2 ≤ s.a l (l + 1) :=
      w5cC4_scsA_ge_two_p34 hk0 hkk hs (w5cC3_mod_ne_succ_p34 (by omega))
    have h2d : 2 < dist v2 (w (l + 1)) := lt_of_le_of_lt h2a ha_lt'
    rw [dist_eq_norm] at h2d
    nlinarith
  have hR2 : (2 * h0) ^ 2 < 8 := by unfold h0; norm_num
  have hs1 : 1 < α + β := by
    by_contra hle
    push_neg at hle
    have hP : ‖v1‖ ^ 2 ≤ (2 * h0) ^ 2 := hPle
    have hQ : ‖w (l + 1)‖ ^ 2 ≤ (2 * h0) ^ 2 := hQle
    have hX : 4 ≤ ‖v2‖ ^ 2 := hXge
    have hD1 : 4 ≤ ‖v2 - v1‖ ^ 2 := hD1ge
    have hD2 : 4 < ‖v2 - w (l + 1)‖ ^ 2 := hD2gt
    have hid : α * ‖v2 - v1‖ ^ 2 + β * ‖v2 - w (l + 1)‖ ^ 2
        = α * ‖v1‖ ^ 2 + β * ‖w (l + 1)‖ ^ 2 - (2 - (α + β)) * ‖v2‖ ^ 2 := by
      have hv2e : v2 = α • v1 + β • w (l + 1) := hcoef.symm
      have e1 : ‖v2 - v1‖ ^ 2 = ‖v2‖ ^ 2 - 2 * (v2 ⬝ᵥ v1) + ‖v1‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_eq_dot]
      have e2 : ‖v2 - w (l + 1)‖ ^ 2
          = ‖v2‖ ^ 2 - 2 * (v2 ⬝ᵥ w (l + 1)) + ‖w (l + 1)‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_eq_dot]
      have hXeq : ‖v2‖ ^ 2 = α * (v2 ⬝ᵥ v1) + β * (v2 ⬝ᵥ w (l + 1)) := by
        rw [norm_sq_eq_dot v2]
        nth_rewrite 1 [hv2e]
        rw [w5cC4_dot_add_left_p34, w5cC4_dot_smul_left_p34, w5cC4_dot_smul_left_p34,
          w5cC4_dot_comm_p34 v1 v2, w5cC4_dot_comm_p34 (w (l + 1)) v2]
      nlinarith [e1, e2, hXeq]
    exact w5cC4_cone_cert_p34 hα hβ hle hP hQ hX hD1 hD2 hR2 hid
  -- small-t construction
  obtain ⟨eU, heU, hU⟩ := UPS_X_POS_SEG_C_p34 v1 v2 x1 x2 x6 1 hnc0 hx1 hx2 hx6 h2 one_pos
  have hU0pos : 0 < upsX x1 x2 x6 := upsX_pos_nc_p34 hnc0 hx1 hx2 hx6
  set M : ℝ := x1 - (x1 + x2 - x6) / 2 with hM
  have hupsdiff : ∀ t : ℝ,
      upsX x1 x2 x6 - upsX x1 (x2 - t) x6 = 4 * M * t + t ^ 2 := by
    intro t
    rw [hM]
    unfold upsX
    ring
  set K : ℝ := 1 / (4 * x1) + (4 * |M| + 1) ^ 2 / (4 * x1 * upsX x1 x2 x6) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h4x1 : 0 < 4 * x1 := by linarith
    have hfirst : 0 < 1 / (4 * x1) := one_div_pos.mpr h4x1
    have hsecond : 0 ≤ (4 * |M| + 1) ^ 2 / (4 * x1 * upsX x1 x2 x6) := by positivity
    linarith
  have hs1pos : 0 < α + β - 1 := by linarith
  refine ⟨min eU (min 1 ((α + β - 1) / (2 * K))),
    lt_min heU (lt_min one_pos (div_pos hs1pos (by linarith))), ?_⟩
  intro t ht
  have htU : t < eU := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htinner : t < min 1 ((α + β - 1) / (2 * K)) :=
    lt_of_lt_of_le ht.2 (min_le_right _ _)
  have ht1 : t < 1 := lt_of_lt_of_le htinner (min_le_left _ _)
  have htE : t < (α + β - 1) / (2 * K) := lt_of_lt_of_le htinner (min_le_right _ _)
  obtain ⟨hupU, hx2t, -⟩ := hU t ⟨by linarith [ht.1], htU⟩
  set U : ℝ := upsX x1 (x2 - t) x6 with hUdef
  set U0 : ℝ := upsX x1 x2 x6 with hU0def
  set r : ℝ := Real.sqrt (U / U0) with hr
  have hU0pos' : 0 < U0 := hU0pos
  have hUpos : 0 < U := hupU
  have hsqrtle : (1 - r) ^ 2 * U0 ≤ (U0 - U) ^ 2 / U0 :=
    w5cC4_sqrt_ratio_p34 U U0 hUpos.le hU0pos'
  have hdiff : U0 - U = 4 * M * t + t ^ 2 := by
    simpa [hU0def, hUdef] using hupsdiff t
  have hdiffle : |U0 - U| ≤ (4 * |M| + 1) * t := by
    rw [hdiff]
    have ht0 : 0 ≤ t := ht.1.le
    have h1 : |4 * M * t + t ^ 2| ≤ 4 * |M| * t + t ^ 2 := by
      have e3 : |4 * M * t| = 4 * |M| * t := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0,
          abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num)]
      calc |4 * M * t + t ^ 2| ≤ |4 * M * t| + |t ^ 2| := abs_add_le _ _
        _ = 4 * |M| * t + t ^ 2 := by rw [e3, abs_of_nonneg (sq_nonneg t)]
    have h2 : 4 * |M| * t + t ^ 2 ≤ (4 * |M| + 1) * t := by nlinarith [ht0]
    linarith
  have hnormu : ‖v2 - v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)‖ ^ 2
      = t ^ 2 / (4 * x1) + (1 - r) ^ 2 * U0 / (4 * x1) := by
    have hmain := (w5cC4_norm_and_dot_p34 v1 v2 x1 x2 x6 t h1 hx1 hx2 hx6).1
    rw [← hUdef, ← hU0def, ← hr] at hmain
    rw [ha]
    exact hmain
  have hKbound : ‖v2 - v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)‖ ^ 2 ≤ t ^ 2 * K := by
    rw [hnormu]
    have h4x : (0:ℝ) ≤ 4 * x1 := by linarith
    have hstep1 : (1 - r) ^ 2 * U0 / (4 * x1) ≤ (U0 - U) ^ 2 / U0 / (4 * x1) :=
      div_le_div_of_nonneg_right hsqrtle h4x
    have hsq : (U0 - U) ^ 2 ≤ ((4 * |M| + 1) * t) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (U0 - U)) hdiffle 2
      rwa [sq_abs] at h
    have hstep2 : (U0 - U) ^ 2 / U0 / (4 * x1)
        ≤ ((4 * |M| + 1) * t) ^ 2 / U0 / (4 * x1) := by
      apply div_le_div_of_nonneg_right _ h4x
      exact div_le_div_of_nonneg_right hsq hU0pos'.le
    have hcollapse : ((4 * |M| + 1) * t) ^ 2 / U0 / (4 * x1)
        = t ^ 2 * ((4 * |M| + 1) ^ 2 / (4 * x1 * U0)) := by
      field_simp [h1.ne', hU0pos'.ne']
    calc t ^ 2 / (4 * x1) + (1 - r) ^ 2 * U0 / (4 * x1)
        ≤ t ^ 2 / (4 * x1) + (U0 - U) ^ 2 / U0 / (4 * x1) := by linarith
      _ ≤ t ^ 2 / (4 * x1) + ((4 * |M| + 1) * t) ^ 2 / U0 / (4 * x1) := by linarith
      _ = t ^ 2 * K := by rw [hK, hcollapse]; ring
  have htK : t ^ 2 * K < t * (α + β - 1) / 2 := by
    have htK' : t * K < (α + β - 1) / 2 := by
      calc t * K < ((α + β - 1) / (2 * K)) * K := mul_lt_mul_of_pos_right htE hKpos
        _ = (α + β - 1) / 2 := by field_simp [hKpos.ne']
    nlinarith [htK', ht.1]
  -- final comparison
  set v3 : V3 := v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) with hv3def
  have hnorm3 : ‖v3‖ ^ 2 = x2 - t := by
    rw [hv3def]
    have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
        ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
          cross3 v1 (cross3 v1 v2) = v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
    exact EYYPQDW_NORMV3_p17 v1 v2 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t))
      x1 x2 (x2 - t) x6 x6 x6 a h1 h2 hx2t h6 h6 h6 hnc0 hx1 hx2 hx6
      (by rw [ha]; norm_num) hupU hv3
  have hu_dot_v1 : (v2 - v3) ⬝ᵥ v1 = t / 2 := by
    rw [hv3def, ha]
    exact (w5cC4_norm_and_dot_p34 v1 v2 x1 x2 x6 t h1 hx1 hx2 hx6).2
  have hu_dot_v2 : (v2 - v3) ⬝ᵥ v2 = (t + ‖v2 - v3‖ ^ 2) / 2 :=
    w5cC4_u_dot_v2_p34 v1 v2 v3 x1 x2 x6 t hx2 hnorm3
  have hdotcoef : (v2 - v3) ⬝ᵥ v2
      = α * ((v2 - v3) ⬝ᵥ v1) + β * ((v2 - v3) ⬝ᵥ w (l + 1)) := by
    have hcoef_pi : ((α • v1 + β • w (l + 1) : V3) : Fin 3 → ℝ) = (v2 : Fin 3 → ℝ) := by
      rw [hcoef]
    have h1' : (v2 - v3) ⬝ᵥ (α • v1 + β • w (l + 1)) = (v2 - v3) ⬝ᵥ v2 :=
      congrArg (fun z : Fin 3 → ℝ => (v2 - v3 : V3) ⬝ᵥ z) hcoef_pi
    have h2' : (v2 - v3) ⬝ᵥ (α • v1 + β • w (l + 1))
        = α * ((v2 - v3) ⬝ᵥ v1) + β * ((v2 - v3) ⬝ᵥ w (l + 1)) := by
      rw [w5cC4_dot_add_right_p34, w5cC4_dot_smul_right_p34, w5cC4_dot_smul_right_p34]
    exact h1'.symm.trans h2'
  have huW : (v2 - v3) ⬝ᵥ w (l + 1)
      = ((v2 - v3) ⬝ᵥ v2 - α * ((v2 - v3) ⬝ᵥ v1)) / β := by
    rw [eq_div_iff hβ.ne']
    linarith [hdotcoef]
  have hkey : β * (‖v3 - w (l + 1)‖ ^ 2 - ‖v2 - w (l + 1)‖ ^ 2)
      = t * (1 - α - β) + ‖v2 - v3‖ ^ 2 := by
    have hnormexp : ‖v3 - w (l + 1)‖ ^ 2 - ‖v2 - w (l + 1)‖ ^ 2
        = -2 * ((v2 - v3) ⬝ᵥ (v2 - w (l + 1))) + ‖v2 - v3‖ ^ 2 := by
      have e1 : ‖v3 - w (l + 1)‖ ^ 2
          = ‖(v2 - w (l + 1)) - (v2 - v3)‖ ^ 2 := by
        rw [show v3 - w (l + 1) = (v2 - w (l + 1)) - (v2 - v3) by abel]
      have e2 : ‖(v2 - w (l + 1)) - (v2 - v3)‖ ^ 2
          = ‖v2 - w (l + 1)‖ ^ 2
            - 2 * ((v2 - v3) ⬝ᵥ (v2 - w (l + 1))) + ‖v2 - v3‖ ^ 2 := by
        rw [norm_sub_sq_real, real_inner_comm (v2 - v3) (v2 - w (l + 1)), inner_eq_dot]
        simp only [WithLp.ofLp_sub]
      rw [e1, e2]
      ring
    rw [hnormexp]
    have hdotW : (v2 - v3) ⬝ᵥ (v2 - w (l + 1))
        = (v2 - v3) ⬝ᵥ v2 - (v2 - v3) ⬝ᵥ w (l + 1) := by
      rw [w5cC4_dot_sub_right_p34]
    rw [hdotW, huW, hu_dot_v1, hu_dot_v2]
    field_simp [hβ.ne']
    ring
  have hsqlt : ‖v3 - w (l + 1)‖ ^ 2 < ‖v2 - w (l + 1)‖ ^ 2 := by
    have hneg : β * (‖v3 - w (l + 1)‖ ^ 2 - ‖v2 - w (l + 1)‖ ^ 2) < 0 := by
      rw [hkey]
      have hinner : t * (1 - α - β) + ‖v2 - v3‖ ^ 2 < 0 := by
        nlinarith [htK, hKbound, ht.1]
      exact hinner
    by_contra hge
    push_neg at hge
    have hnn : 0 ≤ ‖v3 - w (l + 1)‖ ^ 2 - ‖v2 - w (l + 1)‖ ^ 2 := by linarith
    exact absurd (mul_nonneg hβ.le hnn) (not_le.mpr hneg)
  have hlt_norm : ‖v3 - w (l + 1)‖ < ‖v2 - w (l + 1)‖ :=
    norm_lt_of_sq_lt_p34 (norm_nonneg _) (norm_nonneg _) hsqlt
  rw [hWi, dist_eq_norm, dist_eq_norm]
  exact hlt_norm

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
  obtain ⟨h1, h2, h6, hnc0⟩ := w5cC5_hyper_mm_collinear_tc_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hk0 : 0 < k := by omega
  have hBB := w5cC3_mms_bbs_p34 hmw
  have hperw := MMs_periodic_p34 s k w hkk hmw
  have hpa : Periodic2 s.a k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.1
  have hpb : Periodic2 s.b k := by rw [← hkk]; exact hs.2.2.2.2.2.2.2.2.2.2.1
  intro i hi
  by_cases hA : (l + 1) % k = i % k
  · have e_w : w i = w (l + 1) := by
      rw [modFold_p34 hk0 hperw i, ← hA, ← modFold_p34 hk0 hperw (l + 1)]
    have e_a : s.a l i = s.a l (l + 1) := by
      rw [modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) i, ← hA,
        modFold_p34 hk0 (f := fun q => s.a l q) (fun q => (hpa l q).2) (l + 1)]
    have ha_lt_i : s.a l i < dist v2 (w i) := by
      rw [e_a, e_w]; exact ha_lt
    obtain ⟨e, he, hedge⟩ := DEFORMATION_V3_DEFOR_EDGE_TWO_CASES_p34 s k l i w v1 v2 x1 x2 x6 a
      hk hkk hs hmw haz hncW haff hl hlk hn ha_lt_i hx1 hx2 hx6 ha hA
    refine ⟨e, he, fun t ht => ?_⟩
    have hb : dist v2 (w i) ≤ s.b l i := by
      have h' := (hBB.2.2.1 l i).2
      rwa [hl] at h'
    exact le_of_lt (lt_of_lt_of_le (hedge t ht) hb)
  · by_cases hB : (l + k - 1) % k = i % k
    · have e_w : w i = v1 := by
        rw [modFold_p34 hk0 hperw i, ← hB, ← modFold_p34 hk0 hperw (l + k - 1), hlk]
      have e_b : s.b l i = s.b l (l + k - 1) := by
        rw [modFold_p34 hk0 (f := fun q => s.b l q) (fun q => (hpb l q).2) i, ← hB,
          modFold_p34 hk0 (f := fun q => s.b l q) (fun q => (hpb l q).2) (l + k - 1)]
      obtain ⟨eU, heU, hU⟩ := UPS_X_POS_SEG_p34 v1 v2 x1 x2 x6 hnc0 hx1 hx2 hx6 h2
      refine ⟨eU, heU, fun t ht => ?_⟩
      obtain ⟨hup, hx2t⟩ := hU t ⟨by linarith [ht.1], ht.2⟩
      have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
          ((a / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
            cross3 v1 (cross3 v1 v2) = v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
      have hsq3 : ‖v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ ^ 2 = x6 :=
        EYYPQDW_NORM_V3_V1_p17 v1 v2 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t))
          x1 x2 (x2 - t) x6 x6 x6 a h1 h2 hx2t h6 h6 h6 hnc0 hx1 hx2 hx6
          (by rw [ha]; norm_num) hup hv3
      have heqn : ‖v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ = ‖v2 - v1‖ := by
        rw [← Real.sqrt_sq
            (norm_nonneg (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) - v1)),
          hsq3, ← hx6, Real.sqrt_sq (norm_nonneg (v1 - v2)), norm_sub_rev]
      have hdist : dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) =
          dist v2 (w i) := by
        rw [e_w, dist_eq_norm, dist_eq_norm, heqn]
      rw [hdist, e_w, e_b]
      have h' := (hBB.2.2.1 l (l + k - 1)).2
      rwa [hl, hlk] at h'
    · have hC : ¬(l % k = (i + 1) % k) :=
        fun h => hB (w5cC4_suc_k_sub_p34 h (by omega))
      have hd : scsDiag k l i := ⟨Ne.symm hi, hA, hC⟩
      obtain ⟨e, he, hlt⟩ := DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 a
        hkk hk hs hmw hl hlk hx1 hx2 hx6 ha hdiag i hd
      exact ⟨e, he, fun t ht => le_of_lt (hlt t ht)⟩

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
  intro i hmod
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hwi : w i ≠ v2 := by
    intro h
    exact w5cC2_w_inj_p34 hk hkk hs hmw i l hmod (by rw [hl]; exact h)
  have hdist : 0 < dist v2 (w i) := dist_pos.mpr (Ne.symm hwi)
  exact EXISTS_SMALL_LE_CONST_V1_p34 v1 v2 (w i) x1 x2 x6 a 0 h1 h2 h6 hnc
    hx1 hx2 hx6 ha hdist

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
  subst ha
  have hlk' : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk']; exact hncW
  have hncB1 : ¬ Collinear3 0 (w (l + 1)) v1 := by
    rw [← hlk]; exact hncW3
  have hnc1B : ¬ Collinear3 0 v1 (w (l + 1)) := w5cC5_collinear3_zero_swap hncB1
  have hv2gt : v2 ∈ affGt {0} ({v1, w (l + 1)} : Set V3) := by
    have h : w l ∈ affGt {0} ({w (l + 1), v1} : Set V3) := by
      simpa only [hlk', hlk] using haff
    rw [w5cC5_affGt_pair_swap_p34] at h
    rw [hl] at h
    exact h
  obtain ⟨eC, heC, hneC⟩ := DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_TWO_CASES_p34
    s k l w v1 v2 x1 x2 x6 (-1) hk hkk hs hmw hl hlk hx1 hx2 hx6 rfl
  obtain ⟨eC', heC', hgtC⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 v1 v2 (w (l + 1)) x1 x2 x6 (-1)
    hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl hnc1B hv2gt
  refine ⟨min eC eC' / 2, by positivity, fun t ht => ?_⟩
  have hleC : min eC eC' / 2 < eC := by
    have h := min_le_left eC eC'; linarith
  have hleC' : min eC eC' / 2 < eC' := by
    have h := min_le_right eC eC'; linarith
  have htC : -eC < t ∧ t < eC := ⟨by linarith [ht.1, hleC], by linarith [ht.2, hleC]⟩
  have htC' : -eC' < t ∧ t < eC' := ⟨by linarith [ht.1, hleC'], by linarith [ht.2, hleC']⟩
  have hDv2 : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t
      = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    rw [v3DeforV4_p34, if_pos rfl]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 :=
    V3_DEFOR_RHO_NODE_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) eC t FF hk hkk hs hmw
      hl hlk hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl heC htC.1
      (fun τ i hτ hmod => hneC τ hτ i hmod) htC.2 hFF
  have hSYM : ∀ w' : V3, (w', v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
        relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
      (w', v2) ∈ FF :=
    V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) eC t FF hk hkk hs hmw
      hl hlk hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl heC htC.1
      (fun τ i hτ hmod => hneC τ hτ i hmod) htC.2 hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = epPair_p34 FF v2 := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (hSYM y)
  have hrFF : rhoNode1 FF v2 = w (l + 1) := by
    rw [← hl]; exact w5cC4_rhoNode1_range_p34 hk hkk hs hmw hFF
  have hepFF : epPair_p34 FF v2 = w (l + k - 1) := by
    rw [← hl]; exact w5cC4_epPair_range_p34 hk hkk hs hmw hFF
  rw [hDv2, hDFF, hRho, hEP, hrFF, hepFF, hlk]
  have hgtC' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + 1), v1} : Set V3) := by
    rw [w5cC5_affGt_pair_swap_p34]
    exact hgtC t htC'
  have hdisC : Disjoint ({0} : Set V3) ({w (l + 1), v1} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncB1
  have hncfv1 : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v1 :=
    properties_of_collinear4_points_fan hnc1B (hgtC t htC')
  have hncfb : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + 1)) :=
    properties_of_collinear4_points_fan hncB1 hgtC'
  have hLHS : azim 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + 1)) v1
      = Real.pi :=
    aff_gt2_subset_aff_ge hdisC hncfv1 hncfb hgtC'
  rw [hLHS]

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

/-- `_TWO_CASES` clean epsilon kit: on a neighbourhood of `0` the deformation
avoids every `w i` with `i % k ≠ l % k`.  Same finite-minimum route as
`DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_TWO_CASES_p34`, rebuilt locally because
that theorem consumes the still-sorried per-index parent
`DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES_p34`. -/
private theorem w7_two_cases_avoid_p34 (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
    (v1 v2 : V3) (x1 x2 x6 a : ℝ)
    (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (hl : w l = v2) (hlk : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i := by
  have hk0 : 0 < k := by omega
  obtain ⟨h1, h2, h6, hnc⟩ := HYPER_MM_COLLINEAR_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6
    hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hparent : ∀ i : ℕ, ¬(i % k = l % k) → ∃ e : ℝ, 0 < e ∧
      ∀ t : ℝ, -e < t ∧ t < e →
        0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
    intro i hmod
    have hwi : w i ≠ v2 := by
      intro h
      exact w5cC2_w_inj_p34 hk hkk hs hmw i l hmod (by rw [hl]; exact h)
    have hdist : 0 < dist v2 (w i) := dist_pos.mpr (Ne.symm hwi)
    exact EXISTS_SMALL_LE_CONST_V1_p34 v1 v2 (w i) x1 x2 x6 a 0 h1 h2 h6 hnc
      hx1 hx2 hx6 ha hdist
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
      ∀ τ : ℝ, -e' < τ ∧ τ < e' →
        0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ)) (w i) := by
    intro i e hR e' he' hle τ hτ
    exact hR τ ⟨lt_of_le_of_lt (neg_le_neg hle) hτ.1, hτ.2.trans_le hle⟩
  have hres : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
      0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
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
  obtain ⟨e, he, hall⟩ := hres
  refine ⟨e, he, fun t i ht hi hcon => ?_⟩
  have hpos := hall t i ht hi
  rw [hcon, dist_self] at hpos
  exact lt_irrefl (0 : ℝ) hpos
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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t)) = azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) (epPair_p34 FF (w (l + 1))) := by
  subst ha
  have hlk' : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk']; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk']; exact hncW
  have hncBv2 : ¬ Collinear3 0 (w (l + 1)) (w l) :=
    w5cC5_collinear3_zero_swap (properties_of_collinear4_points_fan hncW3 haffW)
  have hncB1 : ¬ Collinear3 0 (w (l + 1)) v1 := by
    rw [← hlk]; exact hncW3
  have hnc1B : ¬ Collinear3 0 v1 (w (l + 1)) := w5cC5_collinear3_zero_swap hncB1
  have hv2gt : v2 ∈ affGt {0} ({v1, w (l + 1)} : Set V3) := by
    have h : w l ∈ affGt {0} ({w (l + 1), v1} : Set V3) := by
      rw [← hlk]; exact haffW
    rw [w5cC5_affGt_pair_swap_p34] at h
    rw [hl] at h
    exact h
  obtain ⟨e, he, hne⟩ := w7_two_cases_avoid_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hlk hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 v1 v2 (w (l + 1)) x1 x2 x6 (-1)
    hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl hnc1B hv2gt
  refine ⟨min e e' / 2, by positivity, fun t ht => ?_⟩
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  have ht_neg : -e < t := by linarith [ht.1, he1e]
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_neg' : -e' < t := by linarith [ht.1, he1e']
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hwv2 : w (l + 1) ≠ v2 := by
    intro hc
    exact hncBv2 (by rw [hc, hl]; exact collinear3_pair_right rfl)
  have hDw : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t = w (l + 1) := by
    rw [v3DeforV4_p34, if_neg hwv2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + 1)) = rhoNode1 FF (w (l + 1)) :=
    V3_DEFOR_RHO_NODE_AT_V1_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw
      hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + 1)) = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) :=
    V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF hk hkk hs hmw
      hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  rw [hDw, hDFF, hRho, hEP]
  have hepFF : epPair_p34 FF (w (l + 1)) = v2 := by
    have h := w5cC4_epPair_range_p34 (l := l + 1) hk hkk hs hmw hFF
    rw [h, show l + 1 + k - 1 = l + k by omega, hper l, hl]
  rw [hepFF]
  have hgtS : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + 1), v1} : Set V3) := by
    rw [w5cC5_affGt_pair_swap_p34]
    exact hgt t ⟨ht_neg', ht_e'⟩
  have hv2S : v2 ∈ affGt {0} ({w (l + 1), v1} : Set V3) := by
    rw [w5cC5_affGt_pair_swap_p34]
    exact hv2gt
  have hdis : Disjoint ({0} : Set V3) ({w (l + 1), v1} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncB1
  have hmemf : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGe ({0} : Set V3) ({w (l + 1), v1} : Set V3) :=
    aff_gt_subset_aff_ge hdis hgtS
  have hmemv2 : v2 ∈ affGe ({0} : Set V3) ({w (l + 1), v1} : Set V3) :=
    aff_gt_subset_aff_ge hdis hv2S
  have hncbf : ¬ Collinear3 0 (w (l + 1))
      (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) :=
    w5cC5_collinear3_zero_swap (properties_of_collinear4_points_fan hncB1 hgtS)
  have hncv2b : ¬ Collinear3 0 (w (l + 1)) v2 :=
    w5cC5_collinear3_zero_swap (properties_of_collinear4_points_fan hncB1 hv2S)
  have hstep1 : azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1)))
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
      = azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) v1 :=
    AZIM_SAME_WITHIN_AFF_GE_ALT 0 (w (l + 1)) _ v1 (rhoNode1 FF (w (l + 1)))
      hmemf hncbf hncB1
  have hstep2 : azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) v2
      = azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) v1 :=
    AZIM_SAME_WITHIN_AFF_GE_ALT 0 (w (l + 1)) v2 v1 (rhoNode1 FF (w (l + 1)))
      hmemv2 hncv2b hncB1
  rw [hstep1, hstep2]

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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1))) (epPair_p34 FF (w (l + k - 1))) := by
  subst ha
  have hlk' : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk']; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk']; exact hncW
  have hncU : ¬ Collinear3 0 (w (l + k - 1)) (w (l + 1)) :=
    w5cC5_collinear3_zero_swap hncW3
  have hnc1U : ¬ Collinear3 0 v1 (w (l + 1)) := by
    rw [← hlk]; exact hncU
  have hv12 : v1 ≠ v2 := fun hc => hnc (by rw [hc]; exact collinear3_pair_right rfl)
  have hv2gt : v2 ∈ affGt {0} ({v1, w (l + 1)} : Set V3) := by
    have h : w l ∈ affGt {0} ({w (l + 1), v1} : Set V3) := by
      rw [← hlk]; exact haffW
    rw [w5cC5_affGt_pair_swap_p34] at h
    rw [hl] at h
    exact h
  obtain ⟨e, he, hne⟩ := w7_two_cases_avoid_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hlk hx1 hx2 hx6 rfl
  obtain ⟨e', he', hgt⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 v1 v2 (w (l + 1)) x1 x2 x6 (-1)
    hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl hnc1U hv2gt
  refine ⟨min e e' / 2, by positivity, fun t ht => ?_⟩
  have he1e : min e e' / 2 < e := by have h := min_le_left e e'; linarith
  have he1e' : min e e' / 2 < e' := by have h := min_le_right e e'; linarith
  have ht_neg : -e < t := by linarith [ht.1, he1e]
  have ht_e : t < e := lt_trans ht.2 he1e
  have ht_neg' : -e' < t := by linarith [ht.1, he1e']
  have ht_e' : t < e' := lt_trans ht.2 he1e'
  have hu_ne_v2 : w (l + k - 1) ≠ v2 := by
    rw [hlk]; exact hv12
  have hDw : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t = w (l + k - 1) := by
    rw [v3DeforV4_p34, if_neg hu_ne_v2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + k - 1)) = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
    simpa only [rhoNode1] using
      V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF
        hk hkk hs hmw hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
        (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
        (w (l + k - 1)) = epPair_p34 FF (w (l + k - 1)) := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (by
      have h := V3_DEFOR_EQ_IN_FF_AT_W_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) e t FF
        hk hkk hs hmw hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
        (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF y
      have hidx : l + (k - 1) = l + k - 1 := by omega
      simpa only [hkk, hidx] using h)
  rw [hDw, hDFF, hRho, hEP]
  have hrhoFF : rhoNode1 FF (w (l + k - 1)) = v2 := by
    have h := w5cC4_rhoNode1_range_p34 (l := l + k - 1) hk hkk hs hmw hFF
    rw [h, show l + k - 1 + 1 = l + k by omega, hper l, hl]
  have hepFF : epPair_p34 FF (w (l + k - 1)) = w (l + k - 2) := by
    have h := w5cC4_epPair_range_p34 (l := l + k - 1) hk hkk hs hmw hFF
    rw [h, show l + k - 1 + k - 1 = l + k - 2 + k by omega, hper (l + k - 2)]
  rw [hrhoFF, hepFF]
  have hgtU : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3) := by
    have hset : ({v1, w (l + 1)} : Set V3) = {w (l + k - 1), w (l + 1)} := by
      rw [← hlk]
    have h := hgt t ⟨ht_neg', ht_e'⟩
    rwa [hset] at h
  have hncvU : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
      (w (l + k - 1)) :=
    properties_of_collinear4_points_fan hncU hgtU
  have hncUf : ¬ Collinear3 0 (w (l + k - 1))
      (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) :=
    w5cC5_collinear3_zero_swap hncvU
  have hdisU : Disjoint ({0} : Set V3) ({w (l + k - 1), w (l + 1)} : Set V3) :=
    w5cC5_disjoint_zero_pair_p34 hncU
  have hmemf : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
      affGe ({0} : Set V3) ({w (l + k - 1), w (l + 1)} : Set V3) :=
    aff_gt_subset_aff_ge hdisU hgtU
  have hgtv2U : v2 ∈ affGt {0} ({w (l + k - 1), w (l + 1)} : Set V3) := by
    rw [w5cC5_affGt_pair_swap_p34]
    rw [← hl]
    exact haffW
  have hmemv2 : v2 ∈ affGe ({0} : Set V3) ({w (l + k - 1), w (l + 1)} : Set V3) :=
    aff_gt_subset_aff_ge hdisU hgtv2U
  have hncv2U : ¬ Collinear3 0 v2 (w (l + k - 1)) :=
    properties_of_collinear4_points_fan hncU hgtv2U
  have hncUv2 : ¬ Collinear3 0 (w (l + k - 1)) v2 :=
    w5cC5_collinear3_zero_swap hncv2U
  have hstep1 : azim 0 (w (l + k - 1))
        (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + k - 2))
      = azim 0 (w (l + k - 1)) (w (l + 1)) (w (l + k - 2)) :=
    AZIM_SAME_WITHIN_AFF_GE 0 (w (l + k - 1)) _ (w (l + 1)) (w (l + k - 2))
      hmemf hncUf hncU
  have hstep2 : azim 0 (w (l + k - 1)) v2 (w (l + k - 2))
      = azim 0 (w (l + k - 1)) (w (l + 1)) (w (l + k - 2)) :=
    AZIM_SAME_WITHIN_AFF_GE 0 (w (l + k - 1)) v2 (w (l + 1)) (w (l + k - 2))
      hmemv2 hncUv2 hncU
  rw [hstep1, hstep2]

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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v) := by
  subst ha
  obtain ⟨e, he, hne⟩ := w7_two_cases_avoid_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hlk hx1 hx2 hx6 rfl
  refine ⟨e, he, fun t v ht hv1 hv2 hvw hvV => ?_⟩
  have ht_neg : -e < t := ht.1
  have ht_e : t < e := ht.2
  have hDv : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t = v := by
    rw [v3DeforV4_p34, if_neg hv2]
  have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
      = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
  have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v
      = rhoNode1 FF v := by
    simp only [rhoNode1]
    rw [funext fun y => propext (V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_TWO_CASES_p34 s k l w v1 v2 v
      x1 x2 x6 (-1) e t FF hk hkk hs hmw hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl
      he ht_neg (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF hv1 hv2 hvw hvV y)]
  have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v
      = epPair_p34 FF v := by
    simp only [epPair_p34]
    congr 1
    funext y
    exact propext (V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_TWO_CASES_p34 s k l w v1 v2 v x1 x2 x6
      (-1) e t FF hk hkk hs hmw hl hlk hx1p hx2p hx6p hncW hnc hx1 hx2 hx6 rfl he ht_neg
      (fun τ i hτ hmod => hne τ hτ i hmod) ht_e hFF hv1 hv2 hvw hvV y)
  rw [hDv, hDFF, hRho, hEP]

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
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v) := by
  subst ha
  have hlk' : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hper : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hkk hmw
  have haffW : w l ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk']; exact haff
  have hncW3 : ¬ Collinear3 0 (w (l + 1)) (w (l + k - 1)) := by
    show ¬ Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3)
    rw [← hlk']; exact hncW
  have hncB1 : ¬ Collinear3 0 (w (l + 1)) v1 := by
    rw [← hlk]; exact hncW3
  have hnc1B : ¬ Collinear3 0 v1 (w (l + 1)) := w5cC5_collinear3_zero_swap hncB1
  have hv2gt : v2 ∈ affGt {0} ({v1, w (l + 1)} : Set V3) := by
    have h : w l ∈ affGt {0} ({w (l + 1), v1} : Set V3) := by
      rw [← hlk]; exact haffW
    rw [w5cC5_affGt_pair_swap_p34] at h
    rw [hl] at h
    exact h
  obtain ⟨eA, heA, hA⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eB, heB, hB⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eD, heD, hD⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  obtain ⟨eC, heC, hneC⟩ := w7_two_cases_avoid_p34 s k l w v1 v2 x1 x2 x6 (-1)
    hk hkk hs hmw hl hlk hx1 hx2 hx6 rfl
  obtain ⟨eC', heC', hgtC⟩ := V3_DEFOR_IN_AFF_GT_V1_p34 v1 v2 (w (l + 1)) x1 x2 x6 (-1)
    hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl hnc1B hv2gt
  refine ⟨min (min (min eA eB) (min eC eC')) eD / 2, by positivity, fun t v ht => ?_⟩
  intro hvV
  have hleA : min (min (min eA eB) (min eC eC')) eD / 2 < eA := by
    have h := le_trans (min_le_left (min (min eA eB) (min eC eC')) eD)
      (le_trans (min_le_left (min eA eB) (min eC eC')) (min_le_left eA eB))
    linarith
  have hleB : min (min (min eA eB) (min eC eC')) eD / 2 < eB := by
    have h := le_trans (min_le_left (min (min eA eB) (min eC eC')) eD)
      (le_trans (min_le_left (min eA eB) (min eC eC')) (min_le_right eA eB))
    linarith
  have hleC : min (min (min eA eB) (min eC eC')) eD / 2 < eC := by
    have h := le_trans (min_le_left (min (min eA eB) (min eC eC')) eD)
      (le_trans (min_le_right (min eA eB) (min eC eC')) (min_le_left eC eC'))
    linarith
  have hleC' : min (min (min eA eB) (min eC eC')) eD / 2 < eC' := by
    have h := le_trans (min_le_left (min (min eA eB) (min eC eC')) eD)
      (le_trans (min_le_right (min eA eB) (min eC eC')) (min_le_right eC eC'))
    linarith
  have hleD : min (min (min eA eB) (min eC eC')) eD / 2 < eD := by
    have h := min_le_right (min (min eA eB) (min eC eC')) eD
    linarith
  have htA : -eA < t ∧ t < eA := ⟨by linarith [ht.1, hleA], by linarith [ht.2, hleA]⟩
  have htB : -eB < t ∧ t < eB := ⟨by linarith [ht.1, hleB], by linarith [ht.2, hleB]⟩
  have htC : -eC < t ∧ t < eC := ⟨by linarith [ht.1, hleC], by linarith [ht.2, hleC]⟩
  have htC' : -eC' < t ∧ t < eC' := ⟨by linarith [ht.1, hleC'], by linarith [ht.2, hleC']⟩
  have htD : -eD < t ∧ t < eD := ⟨by linarith [ht.1, hleD], by linarith [ht.2, hleD]⟩
  have hk0 : 0 < k := by omega
  obtain ⟨j, hj⟩ := hvV
  by_cases h2 : j % k = l % k
  · have hv2 : v = v2 := by
      rw [← hj, modFold_p34 hk0 hper j, h2, ← modFold_p34 hk0 hper l, hl]
    rw [hv2]
    have hDv2 : v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t
        = v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
      rw [v3DeforV4_p34, if_pos rfl]
    have hDFF : deformedFF4_p34 x1 x2 x6 v1 v2 t FF
        = relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF := rfl
    have hRho : rhoNode1 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
          (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2 :=
      V3_DEFOR_RHO_NODE_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) eC t FF hk hkk hs hmw
        hl hlk hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl heC htC.1
        (fun τ i hτ hmod => hneC τ hτ i hmod) htC.2 hFF
    have hSYM : ∀ w' : V3, (w', v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
          relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
        (w', v2) ∈ FF :=
      V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) eC t FF hk hkk hs hmw
        hl hlk hx1p hx2p hx6p hnc hx1 hx2 hx6 rfl heC htC.1
        (fun τ i hτ hmod => hneC τ hτ i hmod) htC.2 hFF
    have hEP : epPair_p34 (relabelFF_p34 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
          (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) = epPair_p34 FF v2 := by
      simp only [epPair_p34]
      congr 1
      funext y
      exact propext (hSYM y)
    have hrFF : rhoNode1 FF v2 = w (l + 1) := by
      rw [← hl]; exact w5cC4_rhoNode1_range_p34 hk hkk hs hmw hFF
    have hepFF : epPair_p34 FF v2 = w (l + k - 1) := by
      rw [← hl]; exact w5cC4_epPair_range_p34 hk hkk hs hmw hFF
    rw [hDv2, hDFF, hRho, hEP, hrFF, hepFF, hlk]
    have hgtC' : v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) ∈
        affGt {0} ({w (l + 1), v1} : Set V3) := by
      rw [w5cC5_affGt_pair_swap_p34]
      exact hgtC t htC'
    have hdisC : Disjoint ({0} : Set V3) ({w (l + 1), v1} : Set V3) :=
      w5cC5_disjoint_zero_pair_p34 hncB1
    have hncfv1 : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v1 :=
      properties_of_collinear4_points_fan hnc1B (hgtC t htC')
    have hncfb : ¬ Collinear3 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + 1)) :=
      properties_of_collinear4_points_fan hncB1 hgtC'
    have hLHS : azim 0 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w (l + 1)) v1
        = Real.pi :=
      aff_gt2_subset_aff_ge hdisC hncfv1 hncfb hgtC'
    have hRHS : azim 0 v2 (w (l + 1)) v1 = Real.pi := by
      rw [← hl, ← hlk, ← hlk']
      exact haz
    rw [hLHS, hRHS]
  · by_cases h1c : j % k = (l + 1) % k
    · have hvw1 : v = w (l + 1) := by
        rw [← hj, modFold_p34 hk0 hper j, h1c, ← modFold_p34 hk0 hper (l + 1)]
      rw [hvw1]
      exact hB t htB
    · by_cases hEc : j % k = (l + k - 1) % k
      · have hv1 : v = v1 := by
          rw [← hj, modFold_p34 hk0 hper j, hEc, ← modFold_p34 hk0 hper (l + k - 1), hlk]
        rw [hv1]
        simpa only [hlk] using hA t htA
      · have hvne2 : v ≠ v2 := by
          intro hcon
          exact h2 (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j l hne) (by rw [hj, hcon, hl]))
        have hvneW1 : v ≠ w (l + 1) := by
          intro hcon
          exact h1c (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j (l + 1) hne) (by rw [hj, hcon]))
        have hvne1 : v ≠ v1 := by
          intro hcon
          exact hEc (by
            by_contra hne
            exact (w_inj_p34 hk hkk hs hmw j (l + k - 1) hne) (by rw [hj, hcon, hlk]))
        exact hD t v htD hvne1 hvne2 hvneW1 ⟨j, hj⟩

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
  obtain ⟨e, he, h⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨e, he, fun v t hv ht1 ht2 hπ => ?_⟩
  have hEq : interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
      (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v := by
    simpa only [interiorAngle1, ivsRhoNode1, epPair_p34] using h t v ⟨ht1, ht2⟩ hv
  rw [hEq, hπ]

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
  subst ha
  have hlkk : l + (s.k - 1) = l + k - 1 := by rw [hkk]; omega
  have hncW3 : ¬Collinear ℝ ({0, w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlkk]
    exact hncW
  have haffW : v2 ∈ affGt {0} ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlkk, ← hl]
    exact haff
  obtain ⟨hx1p, hx2p, hx6p, hnc3⟩ :=
    HYPER_MM_COLLINEAR_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 hkk hs hmw hk hl hlk hx1 hx2 hx6
  have hpair : ({v1, w (l + 1)} : Set V3) =
      ({w (l + 1), w (l + k - 1)} : Set V3) := by
    rw [← hlk]
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨e, he, hmem⟩ := w10_lunar_hull_core_p34 s k l w v1 v2 v w1 (w (l + 1))
    x1 x2 x6 V E hk hkk hs hmw hncW3 haffW hpair hx1p hx2p hx6p hnc3 hvv2 hw1v2
    hV hE hlun hl hx1 hx2 hx6
  exact ⟨e, he, hmem⟩

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
  subst ha
  set V : Set V3 := Set.range w with hV
  set E : Set (Set V3) := Set.range (fun i => {w i, w (i + 1)}) with hE
  set FF : Set (V3 × V3) := Set.range (fun i => (w i, w (i + 1))) with hFF
  have hBB : BBsV39 s w := mms_bbs_p34 hmw
  have hta : taustarV39 s w < 0 := by
    have h1 := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h1
    have h2 := h1.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.2.2
  have hcirc : ¬ Circular V E := by
    have h := JKQEWGV2_p23 s w hs (by omega) hBB hta
    simpa [V, E, Set.image_univ] using h
  have hclf : ConvexLocalFan V E FF := by
    have h := BBS_IMP_CONVEX_LOCAL_FAN_p34 s k w hk hkk hBB
    simpa [V, E, FF] using h
  obtain ⟨hx1p, hx2p, hx6p, hnc⟩ :=
    HYPER_MM_COLLINEAR_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 hkk hs hmw hk hl hlk hx1 hx2 hx6
  -- the generic/circular/lunar trichotomy of a local fan
  have hlf : LocalFan V E FF := hclf.1
  obtain ⟨hfan, x, hxD, hFFeq, hDih, hreg⟩ := hlf
  have hlf' : LocalFan V E FF := ⟨hfan, x, hxD, hFFeq, hDih, hreg⟩
  have hno : dartsOfHyp_p3 E V = Fan.dart1OfFan V E := hno_of_no_isolated (w10_hedge hreg)
  have hlf3 : localFan_p3 V E FF := localFan_p3.of_LocalFan hlf' hno
  have htri := CIZMRRH hlf3
  -- deformation and interior-angle witnesses
  obtain ⟨e3, he3, hdef3⟩ :=
    V3_DEFOR_DEFORMATION_p34 v1 v2 V x1 x2 x2 x2 x6 (-1) hx1p hx2p hx2p hx2p hx6p
      hnc hx1 hx2 hx6 rfl
  obtain ⟨e4, he4, hang4⟩ :=
    DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
      hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF.symm
  rcases htri with hgen | hcirc3 | hlun3
  · -- (1) generic: the ZLZTHIC arrow applies
    have hgen0 : Generic V E := by
      simpa only [generic_p3, Generic] using hgen.1
    set e1 : ℝ := min e3 e4 / 2 with he1def
    have he1pos : 0 < e1 := by
      have h : 0 < min e3 e4 := lt_min he3 he4
      rw [he1def]; linarith
    have he1lt3 : e1 < e3 := by
      have h2 : min e3 e4 ≤ e3 := min_le_left _ _
      rw [he1def]; nlinarith
    have he1lt4 : e1 < e4 := by
      have h2 : min e3 e4 ≤ e4 := min_le_right _ _
      rw [he1def]; nlinarith
    have hdef1 : Deformation (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) V (-e1) e1 :=
      DEFORMATION_SMALL_INTERVAL_p34 hdef3 (by linarith) (by linarith) he1pos
        (le_of_lt he1lt3)
    have hang1 : ∀ v ∈ V, ∀ t ∈ Icc (-e1) e1,
        interiorAngle1 0 FF v = Real.pi →
        interiorAngle1 0 ((fun d : V3 × V3 => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.1 t,
          v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.2 t)) '' FF)
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi := by
      intro v hv t ht hpi
      exact hang4 v t (hV ▸ hv) (by linarith [ht.1]) (by linarith [ht.2]) hpi
    obtain ⟨eps, heps, hconcl⟩ := hz (-e1) e1 V E FF
      (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) hclf hgen0 hdef1 hang1
    refine ⟨eps, heps, fun t ht => ?_⟩
    have h := (hconcl t ht).1
    rw [V_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        E_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        F_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2, ← hV, ← hE, ← hFF]
    exact h
  · -- (2) circular: excluded by JKQEWGV2
    exact absurd (by simpa only [circular_p3, Circular] using hcirc3.1) hcirc
  · -- (3) lunar: the MHAEYJN arrow applies
    obtain ⟨vv, w1, hlun3'⟩ := hlun3.1
    have hlun : Lunar vv w1 V E := by
      simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hlun3'
    have hang_lt : interiorAngle1 0 FF vv < Real.pi / 2 := by
      have h := JKQEWGV3_p23 s w vv w1 hs hBB (by omega) hta (by
        simpa [V, E, Set.image_univ] using hlun)
      simpa [FF, Set.image_univ] using h
    have hv2V : v2 ∈ V := by
      rw [hV]; exact ⟨l, hl⟩
    have hv2ne_v : v2 ≠ vv := by
      intro h
      have hwl : w l = vv := hl.trans h
      have hneg : ¬ Lunar w1 vv V E := by
        have h' := hlunar V E w1 rfl rfl
        rwa [hwl] at h'
      exact hneg ((w11_lunar_comm vv w1 V E).mp hlun)
    have hv2ne_w1 : v2 ≠ w1 := by
      intro h
      have hneg : ¬ Lunar vv v2 V E := by
        have h' := hlunar V E vv rfl rfl
        rwa [hl] at h'
      exact hneg (h.symm ▸ hlun)
    obtain ⟨e5, he5, haff5⟩ :=
      DEFORMATION_LUNAR_AFFINE_HULL_V1_TWO_CASES_p34 s k l w v1 v2 vv w1 x1 x2 x6 (-1) V E
        hk hkk hs hmw haz hncW haff hl hlk (fun h => hn2 h.symm) hx1 hx2 hx6 rfl
        (Ne.symm hv2ne_v) (Ne.symm hv2ne_w1) hV.symm hE.symm hlun
    set e1 : ℝ := min (min e3 e4) e5 / 2 with he1def
    have he1pos : 0 < e1 := by
      have h : 0 < min (min e3 e4) e5 := lt_min (lt_min he3 he4) he5
      rw [he1def]; linarith
    have he1lt3 : e1 < e3 := by
      have h2 : min (min e3 e4) e5 ≤ e3 := (min_le_left _ _).trans (min_le_left _ _)
      rw [he1def]; nlinarith
    have he1lt4 : e1 < e4 := by
      have h2 : min (min e3 e4) e5 ≤ e4 := (min_le_left _ _).trans (min_le_right _ _)
      rw [he1def]; nlinarith
    have he1lt5 : e1 < e5 := by
      have h2 : min (min e3 e4) e5 ≤ e5 := min_le_right _ _
      rw [he1def]; nlinarith
    have hdef1 : Deformation (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) V (-e1) e1 :=
      DEFORMATION_SMALL_INTERVAL_p34 hdef3 (by linarith) (by linarith) he1pos
        (le_of_lt he1lt3)
    have hfix : ∀ u' ∈ V, v2 ≠ u' → ∀ t ∈ Icc (-e1) e1,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 u' t = u' := by
      intro u' _ hu' t _ht
      simp only [v3DeforV4_p34, if_neg (Ne.symm hu')]
    have haffine : ∀ t ∈ Icc (-e1) e1,
        v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈
          affineSpan ℝ ({0, vv, w1, v2} : Set V3) := by
      intro t ht
      exact haff5 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨eps, heps, hconcl⟩ := hm (-e1) e1 V E FF
      (fun v t => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) vv w1 v2
      hclf hlun hdef1 (by linarith [Real.pi_pos]) hv2V hv2ne_v hv2ne_w1 hfix haffine
    refine ⟨eps, heps, fun t ht => ?_⟩
    have h := (hconcl t ht).1
    rw [V_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        E_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2,
        F_DEFORMATION_V3_DEFOR_p34 w x1 x2 x6 t v1 v2, ← hV, ← hE, ← hFF]
    exact h

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
  obtain ⟨e, he, h⟩ := DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) FF
    hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hFF
  refine ⟨e, he, fun v t hv ht1 ht2 => ?_⟩
  simpa only [interiorAngle1, ivsRhoNode1, epPair_p34] using h t v ⟨ht1, ht2⟩ hv

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
  subst ha
  obtain ⟨e, he, hEq⟩ := DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_TWO_CASES_p34 s k l w
    v1 v2 x1 x2 x6 (-1) FF hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc
    hx1 hx2 hx6 rfl hFF
  refine ⟨min e e1, lt_min he he1, fun t i ht0 hte => ?_⟩
  have hte' : t < e := lt_of_lt_of_le hte (min_le_left _ _)
  have hte1 : t < e1 := lt_of_lt_of_le hte (min_le_right _ _)
  have hper : ∀ q, w (q + k) = w q := MMs_periodic_p34 s k w hkk hmw
  have hinj : ∀ i j : ℕ, i % k ≠ j % k → w i ≠ w j :=
    fun i j h => w_inj_p34 hk hkk hs hmw i j h
  have horb := w9_rhoOrbit_p34 (vv := w) (k := k) (FF := FF) (by omega) (by omega) hper
    hinj hFF (l % k) i
  have hBB := hBBd t ht0 hte1
  have hperd : ∀ q, v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (q + k)) t
      = v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w q) t := by
    intro q
    rw [← hkk]
    exact hBB.2.1 q
  have hFFd : Set.range (fun q : ℕ => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w q) t,
      v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (q + 1)) t))
      = deformedFF4_p34 x1 x2 x6 v1 v2 t FF :=
    w9_deformedFF_range_p34 (f := fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) hFF
  have horbd := w9_rhoOrbit_p34
    (vv := fun q => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w q) t)
    (k := k) (FF := deformedFF4_p34 x1 x2 x6 v1 v2 t FF) (by omega) (by omega) hperd
    (w9_bbs_inj_p34 hk hkk hs hBB) hFFd (l % k) i
  rw [horbd, horb]
  exact hEq (w (i + l % k)) t ⟨i + l % k, rfl⟩ (by linarith) hte'

/-- HOL `TAUSTAR_V3_DEFOR_TWO_CASES` (IMJXPHR.hl:9527; statement
`TAUSTAR_V3_DEFOR_TWO_CASES_concl`, IMJXPHR.hl:9504). -/
theorem TAUSTAR_V3_DEFOR_TWO_CASES_p34 : TAUSTAR_V3_DEFOR_TWO_CASES_concl_p34 := by
  intro s k w l x1 x2 x6 a e1 v1 v2 hk hkk hs hmw hl hlk hx1p hx2p hx6p
    haz hncW haff hnc hx1 hx2 hx6 ha hn2 hJ hBBd he1
  subst ha
  have hang : ∃ eA : ℝ, 0 < eA ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < eA →
      interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t
          (Set.range fun i : ℕ => (w i, w (i + 1))))
        ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t
          (Set.range fun i : ℕ => (w i, w (i + 1)))))^[i]
          (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 (Set.range fun i : ℕ => (w i, w (i + 1)))
        ((rhoNode1 (Set.range fun i : ℕ => (w i, w (i + 1))))^[i] (w (l % k))) :=
    INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1) e1
      (Set.range fun i : ℕ => (w i, w (i + 1)))
      hk hkk hs hmw hl hlk hx1p hx2p hx6p haz hncW haff hnc hx1 hx2 hx6 rfl hBBd he1 rfl
  exact w12_taustar_core_p34 s k l w x1 x2 x6 e1 v1 v2 hk hkk hs hmw hl
    hx1p hx2p hx6p hnc hx1 hx2 hx6 hJ hBBd he1 hang

/-- HOL `IMJXPHR` (IMJXPHR.hl:9703; shape `mk_imp (ZLZTHIC_concl,
mk_imp (MHAEYJN_concl, IMJXPHR_concl))`, conclusion IMJXPHR_concl_p34 =
`IMJXPHR_concl` verbatim, IMJXPHR.hl:9682, aligned with LocalAuto1
`IMJXPHRv2_concl`).  Proved 2026-11-05 (la34-imjxphr-w14).  NOTE: this is the
parametric version (`hz`/`hm`); it does NOT by itself discharge the
premise-free LA1 registry `IMJXPHRv2_concl` (that still needs the
`ZLZTHIC`/`MHAEYJN` props) — see the lane DELIVERY. -/
theorem IMJXPHR_p34 (hz : ZLZTHIC_prop_p34) (hm : MHAEYJN_prop_p34) :
    IMJXPHR_concl_p34 := by
  -- DISCHARGES (la34-imjxphr-w14 2026-11-05): source IMJXPHR.hl:9703-11013.
  -- Route: the two symmetric branches of the HOL proof are independent in this
  -- port.  Branch 1 moves `w l` with the fixed neighbour `v1 = w (l+1)` and
  -- proves the second edge equality (`l + k - 1`); branch 2 moves `w l` with
  -- the fixed neighbour `v1 = w (l + k - 1)` and proves the first (`l + 1`).
  -- Each branch, under the negation of its target equality, builds the
  -- `v3_defor_v4` family, checks `BBsV39` on a shrunken window, gets the
  -- strict `taustar` decrease from `TAUSTAR_V3_DEFOR(_TWO_CASES)` and
  -- contradicts the `taustar` minimality carried by `MMsV39 s w`.
  -- The distance to the *fixed* neighbour is preserved by `v3_defor_v1`
  -- (`EYYPQDW_NORM_V3_V1`), so only the *other* neighbour needs its strict
  -- a-bound, which is exactly the negation of the target equality.
  intro s k w l hsk his hmw haz hk3 hnc haff hdiag hnorm hlt hJ hlunar
  have hk1 : 1 ≤ k := by omega
  have hsub : l + (k - 1) = l + k - 1 := by omega
  have hbb : BBsV39 s w := mms_bbs_p34 hmw
  have hmin : ∀ ww, BBsV39 s ww → taustarV39 s w ≤ taustarV39 s ww := by
    have h1 := hmw
    simp only [MMsV39, Set.mem_setOf_eq] at h1
    have h2 := h1.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.2.1
  have hkpos : 0 < k := by omega
  have hperw : ∀ i, w (i + k) = w i := MMs_periodic_p34 s k w hsk hmw
  have hfoldw : ∀ q, w q = w (q % k) := fun q => modFold_p34 hkpos hperw q
  have hpl : l % k < k := Nat.mod_lt _ hkpos
  have hfinj : ∀ a b : ℕ, a < k → b < k → a ≠ b → w a ≠ w b := by
    intro a b ha hb hne hcon
    exact w_inj_p34 hk3 hsk his hmw a b
      (by rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; exact hne) hcon
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsym, hchain, hdiag0, _, _, _, _, _, _⟩ :=
    id his
  have hpa : Periodic2 s.a s.k := his.2.2.2.2.2.2.2.1
  have hpb : Periodic2 s.b s.k := his.2.2.2.2.2.2.2.2.2.2.1
  have hpa' : Periodic2 s.a k := by rw [← hsk]; exact hpa
  have hpb' : Periodic2 s.b k := by rw [← hsk]; exact hpb
  have ham : ∀ i j, s.a i j = s.a (i % k) (j % k) := by
    intro i j
    have h := (periodic2_mod_p18 hpa i j).symm
    rwa [hsk] at h
  have hbm : ∀ i j, s.b i j = s.b (i % k) (j % k) := by
    intro i j
    have h := (periodic2_mod_p18 hpb i j).symm
    rwa [hsk] at h
  have hfolda : ∀ q, s.a l q = s.a l (q % k) :=
    fun q => modFold_p34 hkpos (fun i => (hpa' l i).2) q
  have hfoldb : ∀ q, s.b l q = s.b l (q % k) :=
    fun q => modFold_p34 hkpos (fun i => (hpb' l i).2) q
  have hwlann : w l ∈ ballAnnulus := hbb.1 (Set.mem_range_self l)
  -- ## Branch 1: prove the second edge equality by moving `w l` with
  -- fixed neighbour `v1 = w (l + 1)`.
  have hP2 : s.a l (l + k - 1) = dist (w l) (w (l + k - 1)) := by
    by_contra hne2
    have hlt2 : s.a l (l + k - 1) < dist (w l) (w (l + k - 1)) :=
      lt_of_le_of_ne (hbb.2.2.1 l (l + k - 1)).1 hne2
    set v2 : V3 := w l with hv2
    set v1 : V3 := w (l + 1) with hv1
    set x1 : ℝ := ‖v1‖ ^ 2 with hx1def
    set x2 : ℝ := ‖v2‖ ^ 2 with hx2def
    set x6 : ℝ := ‖v1 - v2‖ ^ 2 with hx6def
    have hlt2' : s.a l (l + k - 1) < dist v2 (w (l + k - 1)) := by
      simpa [hv2] using hlt2
    have hnorm2 : ¬(2 = ‖v2‖) := by simpa [hv2] using hnorm
    have hwlann' : v2 ∈ ballAnnulus := by simpa [hv2] using hwlann
    have hwliff : ∀ i : ℕ, w i = v2 ↔ i % k = l % k := by
      intro i
      constructor
      · intro h
        have h1 : w (i % k) = w (l % k) := by rw [← hfoldw i, ← hfoldw l, h, hv2]
        by_contra hne
        exact hfinj (i % k) (l % k) (Nat.mod_lt _ hkpos) hpl hne h1
      · intro h
        rw [hfoldw i, hv2, hfoldw l, h]
    obtain ⟨hx1p, hx2p, hx6p, hncv⟩ :=
      HYPER_MM_COLLINEAR_p34 s k l w v1 v2 x1 x2 x6 hsk his hmw hk3
        hv2.symm hv1.symm hx1def.symm hx2def.symm hx6def.symm
    obtain ⟨eA, heA, hannA⟩ :=
      V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION_p34 v1 v2 x1 x2 x6 (-1) hx1p hx2p hx6p hncv
        hx1def.symm hx2def.symm hx6def.symm rfl hwlann' (Ne.symm hnorm2)
    have hboundA : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
        s.a l j < dist v2 (w j) := by
      intro j hj1 hj2
      by_cases hjq : j % k = (l + k - 1) % k
      · have e_a : s.a l j = s.a l (l + k - 1) := by
          rw [hfolda j, hjq, ← hfolda (l + k - 1)]
        have e_w : w j = w (l + k - 1) := by
          rw [hfoldw j, hjq, ← hfoldw (l + k - 1)]
        simpa [e_a, e_w, hv2] using hlt2
      · have hd : scsDiag k l j :=
          ⟨hj1, hj2, fun h => hjq (w5cC4_suc_k_sub_p34 h (by omega)).symm⟩
        simpa [hv2] using hlt j hd
    obtain ⟨eAc, heAc, hAw⟩ :=
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_p34 s k l w v1 v2 x1 x2 x6 (-1)
        his hmw hsk hk3 hv2.symm hv1.symm hx1def.symm hx2def.symm hx6def.symm rfl hboundA
    obtain ⟨eB, heB, hBw⟩ :=
      DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_b_p34 s k l w v1 v2 x1 x2 x6 (-1)
        hk3 hsk his hmw haz hnc haff hv2.symm hv1.symm (Ne.symm hnorm2) hlt2'
        hx1def.symm hx2def.symm hx6def.symm rfl hdiag
    obtain ⟨eD, heD, hDw⟩ :=
      V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_p34 hz hm s k w l x1 x2 x6 v1 v2 (-1)
        hsk his hmw haz hk3 hnc haff hnorm2 hJ hv2.symm hv1.symm
        hx1def.symm hx2def.symm hx6def.symm rfl hlunar
    obtain ⟨eU, heU, hUw⟩ :=
      UPS_X_POS_SEG_p34 v1 v2 x1 x2 x6 hncv hx1def.symm hx2def.symm hx6def.symm hx2p
    have hpres : ∀ t : ℝ, 0 < t → t < eU →
        dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v1 = dist v2 v1 := by
      intro t ht0 htU
      obtain ⟨hup, hx2t⟩ := hUw t ⟨by linarith, htU⟩
      have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
          (((-1 : ℝ) / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
            cross3 v1 (cross3 v1 v2) =
          v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
      have hsq3 : ‖v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ ^ 2 = x6 :=
        EYYPQDW_NORM_V3_V1_p17 v1 v2 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
          x1 x2 (x2 - t) x6 x6 x6 (-1) hx1p hx2p hx2t hx6p hx6p hx6p hncv
          hx1def.symm hx2def.symm hx6def.symm (by norm_num) hup hv3
      have heqn : ‖v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ = ‖v2 - v1‖ := by
        rw [← Real.sqrt_sq
            (norm_nonneg (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) - v1)),
          hsq3, hx6def, Real.sqrt_sq (norm_nonneg (v1 - v2)), norm_sub_rev]
      rw [dist_eq_norm, dist_eq_norm, heqn]
    set e1 : ℝ := min (min (min (min eAc eB) eD) eU) eA / 2 with he1def
    have he1pos : 0 < e1 := by
      have h2 : 0 < min (min (min (min eAc eB) eD) eU) eA :=
        lt_min (lt_min (lt_min (lt_min heAc heB) heD) heU) heA
      rw [he1def]; linarith
    have he1A : e1 < eAc := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eAc :=
        (min_le_left _ _).trans
          ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
      rw [he1def]; nlinarith
    have he1B : e1 < eB := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eB :=
        (min_le_left _ _).trans
          ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
      rw [he1def]; nlinarith
    have he1D : e1 < eD := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eD :=
        (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
      rw [he1def]; nlinarith
    have he1U : e1 < eU := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eU :=
        (min_le_left _ _).trans (min_le_right _ _)
      rw [he1def]; nlinarith
    have he1Ann : e1 < eA := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eA := min_le_right _ _
      rw [he1def]; nlinarith
    have hbbs : ∀ t : ℝ, 0 < t → t < e1 →
        BBsV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t) := by
      intro t ht0 ht1
      have htAnn : t < eA := lt_trans ht1 he1Ann
      have htAc : t < eAc := lt_trans ht1 he1A
      have htB : t < eB := lt_trans ht1 he1B
      have htD : t < eD := lt_trans ht1 he1D
      have htU : t < eU := lt_trans ht1 he1U
      have hmove : ∀ i, w i = v2 → v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t =
          v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
        intro i hi; rw [v3DeforV4_p34, if_pos hi]
      have hkeep : ∀ i, w i ≠ v2 → v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t = w i := by
        intro i hi; rw [v3DeforV4_p34, if_neg hi]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨i, rfl⟩ := hx
        change v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t ∈ ballAnnulus
        by_cases hi : w i = v2
        · rw [hmove i hi]
          simpa [v3DeforV4_p34] using hannA t ⟨ht0, htAnn⟩
        · rw [hkeep i hi]
          exact hbb.1 (Set.mem_range_self i)
      · intro i
        show v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + s.k)) t
            = v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t
        rw [hbb.2.1 i]
      · intro i j
        by_cases hi : i % k = l % k
        · by_cases hj : j % k = l % k
          · have hwi : w i = v2 := (hwliff i).mpr hi
            have hwj : w j = v2 := (hwliff j).mpr hj
            have hdist0 : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t) = 0 := by
              rw [hmove i hwi, hmove j hwj, dist_self]
            have haij : s.a i j = 0 := by
              rw [ham i j, hi, hj]; exact hdiag0 (l % k)
            have hab : s.a i j ≤ s.b i j :=
              le_trans (hchain i j).1 (le_trans (hchain i j).2.1 (hchain i j).2.2)
            constructor
            · rw [hdist0, haij]
            · rw [hdist0]; exact le_trans (le_of_eq haij.symm) hab
          · have hwi : w i = v2 := (hwliff i).mpr hi
            have hwj : w j ≠ v2 := fun h => hj ((hwliff j).mp h)
            have haij : s.a i j = s.a l j := by rw [ham i j, ham l j, hi]
            have hbij : s.b i j = s.b l j := by rw [hbm i j, hbm l j, hi]
            have hdist : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t)
                = dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
              rw [hmove i hwi, hkeep j hwj]
            constructor
            · rw [haij, hdist]
              by_cases hjq : j % k = (l + 1) % k
              · have hwjv1 : w j = v1 := by
                  rw [hfoldw j, hjq, ← hfoldw (l + 1), ← hv1]
                have hpj : dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
                    = dist v2 (w j) := by rw [hwjv1]; exact hpres t ht0 htU
                rw [hpj]
                simpa [hv2] using (hbb.2.2.1 l j).1
              · have hguard2 : ¬((l + 1) % k = j % k) := fun h => hjq h.symm
                exact le_of_lt (hAw t ⟨ht0, htAc⟩ j (fun h => hj h.symm) hguard2)
            · rw [hbij, hdist]
              exact hBw t ⟨ht0, htB⟩ j hj
        · by_cases hj : j % k = l % k
          · have hwj : w j = v2 := (hwliff j).mpr hj
            have hwi : w i ≠ v2 := fun h => hi ((hwliff i).mp h)
            have haij : s.a i j = s.a l i := by
              rw [ham i j, ham l i, hj]; exact (hsym (i % k) (l % k)).1
            have hbij : s.b i j = s.b l i := by
              rw [hbm i j, hbm l i, hj]; exact (hsym (i % k) (l % k)).2.2.2.1
            have hdist : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t)
                = dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
              rw [hkeep i hwi, hmove j hwj, dist_comm]
            constructor
            · rw [haij, hdist]
              by_cases hiq : i % k = (l + 1) % k
              · have hwiv1 : w i = v1 := by
                  rw [hfoldw i, hiq, ← hfoldw (l + 1), ← hv1]
                have hpi : dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
                    = dist v2 (w i) := by rw [hwiv1]; exact hpres t ht0 htU
                rw [hpi]
                simpa [hv2] using (hbb.2.2.1 l i).1
              · have hguard2 : ¬((l + 1) % k = i % k) := fun h => hiq h.symm
                exact le_of_lt (hAw t ⟨ht0, htAc⟩ i (fun h => hi h.symm) hguard2)
            · rw [hbij, hdist]
              exact hBw t ⟨ht0, htB⟩ i hi
          · have hwi : w i ≠ v2 := fun h => hi ((hwliff i).mp h)
            have hwj : w j ≠ v2 := fun h => hj ((hwliff j).mp h)
            have hdist : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t) = dist (w i) (w j) := by
              rw [hkeep i hwi, hkeep j hwj]
            rw [hdist]
            exact hbb.2.2.1 i j
      · refine Or.inr ?_
        exact hDw t ⟨by linarith, htD⟩
    obtain ⟨eT, heT, htau⟩ :=
      TAUSTAR_V3_DEFOR_p34 s k w l x1 x2 x6 (-1) e1 v1 v2 hk3 hsk his hmw
        hv2.symm hv1.symm hx1p hx2p hx6p haz hnc haff hncv
        hx1def.symm hx2def.symm hx6def.symm rfl hnorm hJ hbbs he1pos
    set t0 : ℝ := min e1 eT / 2 with ht0def
    have ht0pos : 0 < t0 := by
      have h2 : 0 < min e1 eT := lt_min he1pos heT
      rw [ht0def]; linarith
    have ht0e1 : t0 < e1 := by
      have h2 : min e1 eT ≤ e1 := min_le_left _ _
      rw [ht0def]; nlinarith
    have ht0eT : t0 < eT := by
      have h2 : min e1 eT ≤ eT := min_le_right _ _
      rw [ht0def]; nlinarith
    have hlt_tau : taustarV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t0)
        < taustarV39 s w := htau t0 ⟨ht0pos, ht0eT⟩
    have hge : taustarV39 s w ≤
        taustarV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t0) :=
      hmin _ (hbbs t0 ht0pos ht0e1)
    linarith
  -- ## Branch 2: prove the first edge equality by moving `w l` with
  -- fixed neighbour `v1 = w (l + k - 1)`.
  have hP1 : s.a l (l + 1) = dist (w l) (w (l + 1)) := by
    by_contra hne1
    have hlt1 : s.a l (l + 1) < dist (w l) (w (l + 1)) :=
      lt_of_le_of_ne (hbb.2.2.1 l (l + 1)).1 hne1
    set v2 : V3 := w l with hv2
    set v1 : V3 := w (l + k - 1) with hv1
    set x1 : ℝ := ‖v1‖ ^ 2 with hx1def
    set x2 : ℝ := ‖v2‖ ^ 2 with hx2def
    set x6 : ℝ := ‖v1 - v2‖ ^ 2 with hx6def
    have hlt1' : s.a l (l + 1) < dist v2 (w (l + 1)) := by
      simpa [hv2] using hlt1
    have hnorm2 : ¬(2 = ‖v2‖) := by simpa [hv2] using hnorm
    have hwlann' : v2 ∈ ballAnnulus := by simpa [hv2] using hwlann
    have hwliff : ∀ i : ℕ, w i = v2 ↔ i % k = l % k := by
      intro i
      constructor
      · intro h
        have h1 : w (i % k) = w (l % k) := by rw [← hfoldw i, ← hfoldw l, h, hv2]
        by_contra hne
        exact hfinj (i % k) (l % k) (Nat.mod_lt _ hkpos) hpl hne h1
      · intro h
        rw [hfoldw i, hv2, hfoldw l, h]
    obtain ⟨hx1p, hx2p, hx6p, hncv⟩ :=
      HYPER_MM_COLLINEAR_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 hsk his hmw hk3
        hv2.symm hv1.symm hx1def.symm hx2def.symm hx6def.symm
    obtain ⟨eA, heA, hannA⟩ :=
      V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION_p34 v1 v2 x1 x2 x6 (-1) hx1p hx2p hx6p hncv
        hx1def.symm hx2def.symm hx6def.symm rfl hwlann' (Ne.symm hnorm2)
    have hboundA : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
        s.a l j < dist v2 (w j) := by
      intro j hj1 hj2
      by_cases hjq : j % k = (l + 1) % k
      · have e_a : s.a l j = s.a l (l + 1) := by
          rw [hfolda j, hjq, ← hfolda (l + 1)]
        have e_w : w j = w (l + 1) := by
          rw [hfoldw j, hjq, ← hfoldw (l + 1)]
        simpa [e_a, e_w, hv2] using hlt1
      · have hd : scsDiag k l j :=
          ⟨hj1, fun h => hjq h.symm, hj2⟩
        simpa [hv2] using hlt j hd
    obtain ⟨eAc, heAc, hAw⟩ :=
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_TWO_CASES_p34 s k l w v1 v2 x1 x2 x6 (-1)
        his hmw hsk hk3 hv2.symm hv1.symm hx1def.symm hx2def.symm hx6def.symm rfl hboundA
    obtain ⟨eB, heB, hBw⟩ :=
      DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_b_p34 s k l w v1 v2 x1 x2 x6 (-1)
        hk3 hsk his hmw haz hnc haff hv2.symm hv1.symm (Ne.symm hnorm2) hlt1'
        hx1def.symm hx2def.symm hx6def.symm rfl hdiag
    obtain ⟨eD, heD, hDw⟩ :=
      V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_TWO_CASES_p34 hz hm s k w l x1 x2 x6 v1 v2 (-1)
        hsk his hmw haz hk3 hnc haff hnorm2 hJ hv2.symm hv1.symm
        hx1def.symm hx2def.symm hx6def.symm rfl hlunar
    obtain ⟨eU, heU, hUw⟩ :=
      UPS_X_POS_SEG_p34 v1 v2 x1 x2 x6 hncv hx1def.symm hx2def.symm hx6def.symm hx2p
    have hpres : ∀ t : ℝ, 0 < t → t < eU →
        dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) v1 = dist v2 v1 := by
      intro t ht0 htU
      obtain ⟨hup, hx2t⟩ := hUw t ⟨by linarith, htU⟩
      have hv3 : ((x1 + (x2 - t) - x6) / (2 * x1)) • v1 +
          (((-1 : ℝ) / x1) * Real.sqrt (upsX x1 (x2 - t) x6 / upsX x1 x2 x6)) •
            cross3 v1 (cross3 v1 v2) =
          v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := rfl
      have hsq3 : ‖v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ ^ 2 = x6 :=
        EYYPQDW_NORM_V3_V1_p17 v1 v2 (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t))
          x1 x2 (x2 - t) x6 x6 x6 (-1) hx1p hx2p hx2t hx6p hx6p hx6p hncv
          hx1def.symm hx2def.symm hx6def.symm (by norm_num) hup hv3
      have heqn : ‖v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) - v1‖ = ‖v2 - v1‖ := by
        rw [← Real.sqrt_sq
            (norm_nonneg (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) - v1)),
          hsq3, hx6def, Real.sqrt_sq (norm_nonneg (v1 - v2)), norm_sub_rev]
      rw [dist_eq_norm, dist_eq_norm, heqn]
    set e1 : ℝ := min (min (min (min eAc eB) eD) eU) eA / 2 with he1def
    have he1pos : 0 < e1 := by
      have h2 : 0 < min (min (min (min eAc eB) eD) eU) eA :=
        lt_min (lt_min (lt_min (lt_min heAc heB) heD) heU) heA
      rw [he1def]; linarith
    have he1A : e1 < eAc := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eAc :=
        (min_le_left _ _).trans
          ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
      rw [he1def]; nlinarith
    have he1B : e1 < eB := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eB :=
        (min_le_left _ _).trans
          ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
      rw [he1def]; nlinarith
    have he1D : e1 < eD := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eD :=
        (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
      rw [he1def]; nlinarith
    have he1U : e1 < eU := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eU :=
        (min_le_left _ _).trans (min_le_right _ _)
      rw [he1def]; nlinarith
    have he1Ann : e1 < eA := by
      have h2 : min (min (min (min eAc eB) eD) eU) eA ≤ eA := min_le_right _ _
      rw [he1def]; nlinarith
    have hbbs : ∀ t : ℝ, 0 < t → t < e1 →
        BBsV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t) := by
      intro t ht0 ht1
      have htAnn : t < eA := lt_trans ht1 he1Ann
      have htAc : t < eAc := lt_trans ht1 he1A
      have htB : t < eB := lt_trans ht1 he1B
      have htD : t < eD := lt_trans ht1 he1D
      have htU : t < eU := lt_trans ht1 he1U
      have hmove : ∀ i, w i = v2 → v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t =
          v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t) := by
        intro i hi; rw [v3DeforV4_p34, if_pos hi]
      have hkeep : ∀ i, w i ≠ v2 → v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t = w i := by
        intro i hi; rw [v3DeforV4_p34, if_neg hi]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨i, rfl⟩ := hx
        change v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t ∈ ballAnnulus
        by_cases hi : w i = v2
        · rw [hmove i hi]
          simpa [v3DeforV4_p34] using hannA t ⟨ht0, htAnn⟩
        · rw [hkeep i hi]
          exact hbb.1 (Set.mem_range_self i)
      · intro i
        show v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + s.k)) t
            = v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t
        rw [hbb.2.1 i]
      · intro i j
        by_cases hi : i % k = l % k
        · by_cases hj : j % k = l % k
          · have hwi : w i = v2 := (hwliff i).mpr hi
            have hwj : w j = v2 := (hwliff j).mpr hj
            have hdist0 : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t) = 0 := by
              rw [hmove i hwi, hmove j hwj, dist_self]
            have haij : s.a i j = 0 := by
              rw [ham i j, hi, hj]; exact hdiag0 (l % k)
            have hab : s.a i j ≤ s.b i j :=
              le_trans (hchain i j).1 (le_trans (hchain i j).2.1 (hchain i j).2.2)
            constructor
            · rw [hdist0, haij]
            · rw [hdist0]; exact le_trans (le_of_eq haij.symm) hab
          · have hwi : w i = v2 := (hwliff i).mpr hi
            have hwj : w j ≠ v2 := fun h => hj ((hwliff j).mp h)
            have haij : s.a i j = s.a l j := by rw [ham i j, ham l j, hi]
            have hbij : s.b i j = s.b l j := by rw [hbm i j, hbm l j, hi]
            have hdist : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t)
                = dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w j) := by
              rw [hmove i hwi, hkeep j hwj]
            constructor
            · rw [haij, hdist]
              by_cases hjq : j % k = (l + k - 1) % k
              · have hwjv1 : w j = v1 := by
                  rw [hfoldw j, hjq, ← hfoldw (l + k - 1), ← hv1]
                have hpj : dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
                    = dist v2 (w j) := by rw [hwjv1]; exact hpres t ht0 htU
                rw [hpj]
                simpa [hv2] using (hbb.2.2.1 l j).1
              · have hguard2 : ¬(l % k = (j + 1) % k) := by
                  intro h
                  exact hjq (w5cC4_suc_k_sub_p34 h (by omega)).symm
                exact le_of_lt (hAw t ⟨ht0, htAc⟩ j (fun h => hj h.symm) hguard2)
            · rw [hbij, hdist]
              exact hBw t ⟨ht0, htB⟩ j hj
        · by_cases hj : j % k = l % k
          · have hwj : w j = v2 := (hwliff j).mpr hj
            have hwi : w i ≠ v2 := fun h => hi ((hwliff i).mp h)
            have haij : s.a i j = s.a l i := by
              rw [ham i j, ham l i, hj]; exact (hsym (i % k) (l % k)).1
            have hbij : s.b i j = s.b l i := by
              rw [hbm i j, hbm l i, hj]; exact (hsym (i % k) (l % k)).2.2.2.1
            have hdist : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t)
                = dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) := by
              rw [hkeep i hwi, hmove j hwj, dist_comm]
            constructor
            · rw [haij, hdist]
              by_cases hiq : i % k = (l + k - 1) % k
              · have hwiv1 : w i = v1 := by
                  rw [hfoldw i, hiq, ← hfoldw (l + k - 1), ← hv1]
                have hpi : dist (v3DeforV1_p17 (-1) v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
                    = dist v2 (w i) := by rw [hwiv1]; exact hpres t ht0 htU
                rw [hpi]
                simpa [hv2] using (hbb.2.2.1 l i).1
              · have hguard2 : ¬(l % k = (i + 1) % k) := by
                  intro h
                  exact hiq (w5cC4_suc_k_sub_p34 h (by omega)).symm
                exact le_of_lt (hAw t ⟨ht0, htAc⟩ i (fun h => hi h.symm) hguard2)
            · rw [hbij, hdist]
              exact hBw t ⟨ht0, htB⟩ i hi
          · have hwi : w i ≠ v2 := fun h => hi ((hwliff i).mp h)
            have hwj : w j ≠ v2 := fun h => hj ((hwliff j).mp h)
            have hdist : dist (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t)
                (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w j) t) = dist (w i) (w j) := by
              rw [hkeep i hwi, hkeep j hwj]
            rw [hdist]
            exact hbb.2.2.1 i j
      · refine Or.inr ?_
        exact hDw t ⟨by linarith, htD⟩
    obtain ⟨eT, heT, htau⟩ :=
      TAUSTAR_V3_DEFOR_TWO_CASES_p34 s k w l x1 x2 x6 (-1) e1 v1 v2 hk3 hsk his hmw
        hv2.symm hv1.symm hx1p hx2p hx6p haz hnc haff hncv
        hx1def.symm hx2def.symm hx6def.symm rfl hnorm hJ hbbs he1pos
    set t0 : ℝ := min e1 eT / 2 with ht0def
    have ht0pos : 0 < t0 := by
      have h2 : 0 < min e1 eT := lt_min he1pos heT
      rw [ht0def]; linarith
    have ht0e1 : t0 < e1 := by
      have h2 : min e1 eT ≤ e1 := min_le_left _ _
      rw [ht0def]; nlinarith
    have ht0eT : t0 < eT := by
      have h2 : min e1 eT ≤ eT := min_le_right _ _
      rw [ht0def]; nlinarith
    have hlt_tau : taustarV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t0)
        < taustarV39 s w := htau t0 ⟨ht0pos, ht0eT⟩
    have hge : taustarV39 s w ≤
        taustarV39 s (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t0) :=
      hmin _ (hbbs t0 ht0pos ht0e1)
    linarith
  exact ⟨hP1, by simpa [hsub] using hP2⟩

end Kepler.Text

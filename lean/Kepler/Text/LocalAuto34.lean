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
  import list) — NEEDS: delete and import TopologyFan's public copies.
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
  `BBs` periodicity).  All azim/taustar/interior-angle/lunar/fan giants are
  `sorry` (skeleton-first).
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
  sorry

/-- HOL `UPS_X_POS_SEG` (IMJXPHR.hl:118). -/
theorem UPS_X_POS_SEG_p34 (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (h2 : 0 < x2) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → 0 < upsX x1 (x2 - t) x6 ∧ 0 < x2 - t := by
  sorry

/-- HOL `UPS_X_POS_SEG_C` (IMJXPHR.hl:152). -/
theorem UPS_X_POS_SEG_C_p34 (v1 v2 : V3) (x1 x2 x6 c : ℝ)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (h2 : 0 < x2) (hc : 0 < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → 0 < upsX x1 (x2 - t) x6 ∧ 0 < x2 - t ∧ t < c := by
  sorry

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
  sorry

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
  sorry

/-- HOL `EXISTS_SMALL_LE_CONST_V1` (IMJXPHR.hl:456). -/
theorem EXISTS_SMALL_LE_CONST_V1_p34 (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hclt : c < dist v2 w) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w := by
  sorry

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
  sorry

/-- HOL `EXISTS_SMALL_LT_CONST_V1` (IMJXPHR.hl:677). -/
theorem EXISTS_SMALL_LT_CONST_V1_p34 (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
    (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a = -1) (hclt : dist v2 w < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w < c := by
  sorry

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

/-! ## Section 2: the FF-relabel and rho-node tower -/

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

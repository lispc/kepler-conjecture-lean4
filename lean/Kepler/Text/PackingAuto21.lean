/-
PackingAuto21: port of `scripts/packing/TSKAJXY2.hl` (731 lines, Vu Khac Ky
2013: the 0/3/4-cell special cases of TSKAJXY) and `scripts/packing/TSKAJXY3.hl`
(2288 lines, Thomas C. Hales 2012: the remaining 1/2-cell cases + capstone).
Together with the hub PackingAuto20 (TSKAJXY1.hl) this COMPLETES the TSKAJXY
chain: `TSKAJXY` below is the capstone consuming `TSKAJXY_034` (0/3/4 cells)
and `TSKAJXY_1`/`TSKAJXY_2` (1/2 cells).

FILE MAP (TSKAJXY2.hl: 1 def + 1 thm)
  `cell3_from_ineq`, `GRKIBMP_concl` (statement `let`s), `tsk_hyp_new`
  (the hypothesis bundle `GRKIBMP_concl /\ cell3_from_ineq /\ tsk_hyp`),
  `TSKAJXY_statement_special_case` (`new_definition`), `TSKAJXY_034` (giant).

FILE MAP (TSKAJXY3.hl: 1 def + 66 thms; HJKDESR1a_1cell dedup)
  Measure/split kit for `mcell1` (GAMMAX_NULLSET ... TSKAJXY_1), the
  `cell_params_d` kit for `mcell2` (MCELL_CELL_PARAMETERS_D_EXIST ...),
  bisector algebra (BIS_*), symmetric-difference algebra (SDIFF_*),
  `frustt`/wedge negligibility (FRUSTT_*), the `mcell2` volume/solid-angle
  reduction (MCELL2_VOL_SPLIT ... MCELL2_SOL), the analytic def
  `gamma2_x_div_azim_v2` and `GAMMAX_GAMMA2_X`, capstones `TSKAJXY_2`,
  `TSKAJXY`.  `HJKDESR1a_1cell` (TSKAJXY3.hl:766) is byte-identical to the
  hub's copy (TSKAJXY1.hl:5652, PackingAuto20.lean:241); it was deduped at
  the atn2-merge (plan §5.3): PA21 now imports PackingAuto20 and uses the
  hub's declaration.  `MCELL2_SUBSET_AFF_GE` below is suffixed `_p21`
  because PackingAuto18 hosts a same-named theorem with a DIFFERENT
  statement (plan §6).
  `tsk_required_ineq` (TSKAJXY3.hl:2240) is a list of Merge_ineq string
  keys with no mathematical content; ported as a `List String` def.
  - MERGE NOTE (atn2-merge, executed 2026-09: docs/atn2-merge-plan.md §5.3):
    the verbatim hub-lane kit copy below (`atn2`/`deltaXf`/`deltaX4f`/
    `dihXf`/`dihY`/`solY`/`volXf`/`volY`/`vol3r`/`vol3f`/`gamma3f` and the
    numeric seed `HJKDESR1a_1cell`) is DELETED; the file imports
    PackingAuto20     (the vol/gamma family + `HJKDESR1a_1cell` + the
    `deltaXf`/`deltaX4f` compatibility aliases) and Kepler.Text.SphereKit
    (the canonical `atn2`/`deltaX`/`deltaX4`/`dihXf`/`dihY`/`solY`,
    declared in the shared `Kepler.Text` namespace).
    `gamma2_x_div_azim_v2` stays: it is TSKAJXY3's own
    single definition, not a PA20 twin.

ENCODING NOTES
  - HOL `real^3` <-> `V3`; `dist(u,v)` <-> `dist u v`; `EL i ul` <->
    `elV ul i`; `HD ul` <-> `hdV ul`; `NULLSET X` <-> `nullSet X`; `vol` <->
    `volume.real`; `atn` <-> `Real.arctan`; `pi` <-> `Real.pi`; `sqrt2`/
    `sqrt8` <-> `Real.sqrt 2`/`Real.sqrt 8` (inlined, per PackingAuto2);
    `conv`/`coplanar`/`collinear` <-> `Convex ℝ`/`Coplanar`/`Collinear3`;
    `aff_ge` <-> `affGe`; `bis`/`bis_le` <-> `bis`/`bisLe`; `omega_list_n` <->
    `omegaListN`; `cell_params_d` <-> `cellParamsD`; `left_action_list` <->
    `leftActionList`; `mcell_set` <-> `mcellSet`; `SDIFF` (symmetric
    difference) <-> `SymmDiff` (Mathlib `s ∆ t`); `radial`/`radial_norm` <->
    `radialNorm` (Kepler.Geom); `eventually_radial` <-> `EventuallyRadial`.
  - UPSTREAM DEFS ABSENT LOCALLY: `h0cut`, `eta_y`, `tsk_hyp`,
    `pack_nonlinear_non_ox3q1h` (Merge_ineq.hl / sphere.hl), `frustum`/
    `frustt` (vol1.hl).  `h0cut` is reconstructed as
    `x <= 2 * h0 -> 1 else 0`, the unique body making the upstream
    `lmfun x = h0cut (2*x) * lfun x` hold (used by GAMMAX_GAMMA2_X's
    `lmfun_h0cut` step); `frustum`/`frustt` are reconstructed from use
    sites (slab `0 <= (x-u).dot(v-u) <= h*norm(v-u)`, resp. its
    intersection with `rcone_gt u v a`).  MERGE-INEQ wave 0
    (docs/merge-ineq-channel.md §2.1/§2.2): `eta_y` is re-pointed to the
    faithful `IneqClosureDefs.etaY` (sphere.hl:131-135), and `tsk_hyp`/
    `pack_nonlinear_non_ox3q1h` are structured as the 19 TSKAJXY
    consumption slices (`bank_*` entries + `cell3_bank`/`tsk_bank`/
    `grk_bank`) plus the 62-entry rest leaf `pack_nonlinear_rest`
    (G4 placeholder).
  - `l ~/ y` in ATN2_Y_NEG etc. uses `Real.arctan`; `atn2` is
    Kepler.Text.SphereKit.atn2 (verbatim sphere.hl:48).

DISCHARGES
  - NONE of the concl interfaces match verbatim: the capstone `TSKAJXY`
    carries the extra antecedent `pack_nonlinear_non_ox3q1h` (the
    Merge_ineq certified-inequality bank; structured in wave 0 as
    19 slices + rest leaf, still assumption-fed at the capstones), so it
    implies but
    does not discharge `Kepler.Text.TSKAJXY_statement`
    (PackingAuto2.lean:845); `TSKAJXY_034` additionally needs
    `tsk_hyp_new`.  No `pack_concl` lemma is re-proved here.

NEEDS (wave-B3 state, 2026-09-30): closed in-file — GAMMAX_MCELL1,
  MCELL2_VX_PROPS, MCELL1_SOL_RESTRICT, MCELL1_RADIAL, MCELL1_VOL,
  MCELL_CELL_PARAMETERS_D_EXIST, MCELL2_CELL_PARAMETERS_EXIST,
  MCELL_PARAM_D_UL, MCELL2_PARAM_D_UL, MCELL2_DIHX,
  MCELL2_INTER_BIS_LE_MEASURABLE, MCELL2_VOL_SPLIT, RCONE_PAIR,
  MCELL2_SPLIT, FRUSTT_RCONE_GE, FRUSTT_WEDGE_RCONE_GE,
  NOT_COPLANAR_EXTREME_MCELL2, MCELL2_DIHV_LT_PI, MCELL2_DIHV_AZIM,
  TSKAJXY_1, TSKAJXY (capstone, assumption-fed), NOT_COPLANAR_OMEGA_LIST_N,
  NOT_COPLANAR_R3, BARV_DISTINCT, OMEGA_LIST_BISECTOR,
  CONVEX_HULL_4_AFF_GE, CONVEX_HULL_SCALE; B3-wave assemblies: GAMMAX_MCELL2,
  MCELL2_VOL, TSKAJXY_2.
CLOSED (2026-09-30 wedge GIANT lane; 措辞降级 2026-10-14 #print axioms
  核查): `MCELL2_VOL_SPLIT_EXPLICIT` PROVED（axiom 面标准三，真零债）;
  `MCELL2_SOL` 证法落地但 **axiom 面含 sorryAx**（消费上游债, 非零债 PROVED）——
  二者同以 wedge closed forms 件装配（slicing closed form `VOLUME_FRUSTT_WEDGE`
  port + `WEDGE_GE_EQ_AFF_GE` port + radial kit）。
REMAINING sorry (2 sites; A11 lane 2026-10-08: `pack_nonlinear_rest` def
  body honestly narrowed from unknown-Prop stub to the explicit 62-entry
  `bank_*` conjunction — see "bank rest" section, `#print axioms` = standard
  three): `mi_gamma3f_gamma3f_x_div_sqrtdelta` (merge_ineq WEAK/WEAK2),
  `TSKAJXY_034` (0/3/4-cell giant).
DEDUP/CLOSED (2026-09-30, LA38 wrapper lane): `GAMMAX_GAMMA2_X` PROVED —
  the sole structural gap (the dihV<->dih_y bridge) is consumed via the new
  `Kepler.Text.LocalAuto38Bridge` public wrappers (`DIHV_EQ_DIH_Y_4PT_B`/
  `DIHV_NN_4PT_B`, clash-free re-hosts of the LocalAuto38 `DIHV_EQ_DIH_Y_4PT`
  wave; direct `import Kepler.Text.LocalAuto38` is impossible because
  LocalAuto1's `rho` collides with IneqClosureDefs' `rho`).  The local
  sorry'd copies of `LEFT_ACTION_LIST_1_PROPERTIES_ALT` and
  `MCELL2_PERMUTE_01` are DELETED: PackingAuto14 (:785/:822) now hosts
  proved identical statements on this file's transitive import closure, and
  `MCELL2_VOL`/`GAMMAX_GAMMA2_X` consume them unchanged.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto4
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto17
import Kepler.Text.PackingAuto18
import Kepler.Text.PackingAuto20
import Kepler.Text.LocalAuto38Bridge  -- GAMMAX_GAMMA2_X (2026-09-30): consumes
  -- the public 4-point dihV<->dih_y bridge `DIHV_EQ_DIH_Y_4PT_B` hosted there.
  -- (Direct `import Kepler.Text.LocalAuto38` is impossible: LA38's closure
  -- brings LocalAuto1's `rho`, which collides with IneqClosureDefs' `rho`.)
import Kepler.Text.SphereKit
import Kepler.Text.IneqClosureDefs
import Kepler.Text.Polytope
import Kepler.Text.ConicCapVolume
import Kepler.Geom.WedgeVolume
import Kepler.Geom.LuneVolume
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory
open scoped Matrix

/-! ## Sphere.hl toolkit (atn2-merge, docs/atn2-merge-plan.md §5.3)

The verbatim hub-lane kit copy (`atn2`/`deltaXf`/`deltaX4f`/`dihXf`/`dihY`/
`solY`/`volXf`/`volY`/`vol3r`/`vol3f`/`gamma3f` and the duplicate
`HJKDESR1a_1cell`) is gone: the canonical numeric kit is
`Kepler.Text.SphereKit` — which declares it in this same `Kepler.Text`
namespace, so the plain names keep resolving — and the vol/gamma family plus
`HJKDESR1a_1cell` come from the hub PackingAuto20, imported above. -/

/-- HOL `gamma2_x_div_azim_v2` (TSKAJXY3.hl:2065-2068, the file's single
`new_definition`; placed here because `GRKIBMP_concl` below mentions it). -/
noncomputable def gamma2_x_div_azim_v2 (m x : ℝ) : ℝ :=
  (8 - x) * Real.sqrt x / 24 -
    (2 * (2 * mm1 / Real.pi) * (1 - Real.sqrt x / Real.sqrt 8) -
      (8 * mm2 / Real.pi) * m * lfun (Real.sqrt x / 2))

/-! ## Upstream definitional payload (bodies absent from local sources) -/

-- HOL `bis` (sphere.hl:360): already public in Kepler.Text.PackingAuto5.lean:65.

/-- HOL `eta_y` (sphere.hl:131-135): `eta_x` at squared lengths, i.e.
`sqrt(x1*x2*x3/ups_x …)`（忠实体 = `IneqClosureDefs.etaY`，单一来源）. -/
noncomputable def eta_y (y4 y5 y6 : ℝ) : ℝ := etaY y4 y5 y6

/-- HOL `h0cut` (Merge_ineq.hl).  Reconstruction: the unique `if`-body
with `lmfun x = h0cut (2 * x) * lfun x` (the upstream `lmfun_h0cut` used
inside GAMMAX_GAMMA2_X): for `x <= 2 * h0` the factor is `1`, else `0`. -/
noncomputable def h0cut (x : ℝ) : ℝ := if x ≤ 2 * h0 then 1 else 0

/-! ## Merge_ineq bank: the 19 TSKAJXY consumption slices (MERGE-INEQ
wave 0, docs/merge-ineq-channel.md §2.2)

HOL `pack_nonlinear_non_ox3q1h` (merge_ineq.hl:118-122) is the
conjunction of the 81-entry `packing_ineq_data` filter over the Ineq
database (`IdLists.lean:43-126 packNonlinearNonOx3q1hIds`).  Per charter
§2.0 route A' the bank is re-bodied here as: the 19 entries consumed by
TSKAJXY (`tsk_required_ineq`, TSKAJXY3.hl:2240-2249 = `cell3_hyp`
(merge_ineq.hl:3490-3495) @ `tsk_hyp` (:1370-1377) @ GRKIBMP (:3795)),
materialized verbatim in arrow form (HOL `Sphere.ineq` boxes unfolded;
charter §6.2), plus one honest 62-entry rest leaf.  Entry naming:
`bank_` + the idv string whitespace-squeezed; each docstring carries the
HOL idv and its ineq.hl registration line.  Conjunction order = the
consumer groups, not the HOL prepend order — registered reconciliation
(charter §4.3 item 8). -/

/-- HOL `eulerA_x` (sphere.hl:830-833): verbatim the let-bound `a` of
`sol_euler_x_div_sqrtdelta` (IneqClosureDefs.solEulerXDivSqrtdelta,
with `sqrt(x1*x2*x3)` split into the three-factor product of eulerA_x). -/
noncomputable def eulerAX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt x1 * Real.sqrt x2 * Real.sqrt x3 +
    Real.sqrt x1 * (x2 + x3 - x4) / 2 +
    Real.sqrt x2 * (x1 + x3 - x5) / 2 +
    Real.sqrt x3 * (x1 + x2 - x6) / 2

/-- HOL `gamma2_x1_div_a_v2` (nonlin_def.hl:346-347):
`promote1_to_6 (gamma2_x_div_azim_v2 m)`, the six-variable lift. -/
noncomputable def gamma2x1DivAV2 (m : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 _x2 _x3 _x4 _x5 _x6 => gamma2_x_div_azim_v2 m x1

/-- HOL ineq entry `QZECFIC wt0` (ineq.hl:1372).  Box
[1,1]³×[2.01,2hmin]×[2,2hmin]². -/
def bank_QZECFICwt0 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2.01 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    0 < yOfX (gamma3fXDivSqrtdelta 1 1 1) y1 y2 y3 y4 y5 y6

/-- HOL ineq entry `QZECFIC wt0 corner` (ineq.hl:1389).  Box
[1,1]³×[2,2.01]³. -/
def bank_QZECFICwt0corner : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2 ≤ y4 → y4 ≤ 2.01 → 2 ≤ y5 → y5 ≤ 2.01 → 2 ≤ y6 → y6 ≤ 2.01 →
    0 ≤ yOfX (gamma3fXDivSqrtdelta 1 1 1) y1 y2 y3 y4 y5 y6

/-- HOL ineq entry `QZECFIC wt0 sqrt8` (ineq.hl:1406).  Box
[1,1]³×[2hplus,√8]×[2,2hmin]×[2,2hmin]. -/
def bank_QZECFICwt0sqrt8 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2 * hplus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    0 < yOfX (gamma3fXDivSqrtdelta 0 1 1) y1 y2 y3 y4 y5 y6 ∨
      eta_y y4 y5 y6 ^ 2 > 2

/-- HOL ineq entry `QZECFIC wt1` (ineq.hl:1425).  Box
[√2,√2]³×[2hmin,2hplus]×[2,2hmin]×[2,2hmin]. -/
def bank_QZECFICwt1 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, Real.sqrt 2 ≤ y1 → y1 ≤ Real.sqrt 2 →
    Real.sqrt 2 ≤ y2 → y2 ≤ Real.sqrt 2 → Real.sqrt 2 ≤ y3 → y3 ≤ Real.sqrt 2 →
    2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    yOfX (gamma3fXDivSqrtdelta (h0cut y4) 1 1) y1 y2 y3 y4 y5 y6 >
        0.008 * yOfX dih4XDivSqrtdeltaPosbranch y1 y2 y3 y4 y5 y6 ∨
      eta_y y4 y5 y6 ^ 2 > 2

/-- HOL ineq entry `QZECFIC wt2 A` (ineq.hl:1443).  Box
[√2,√2]³×[2hmin,√8]×[2hmin,√8]×[2,2hmin]. -/
def bank_QZECFICwt2A : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, Real.sqrt 2 ≤ y1 → y1 ≤ Real.sqrt 2 →
    Real.sqrt 2 ≤ y2 → y2 ≤ Real.sqrt 2 → Real.sqrt 2 ≤ y3 → y3 ≤ Real.sqrt 2 →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 * hminus ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    yOfX (gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) 1) y1 y2 y3 y4 y5 y6 / 2 >
        0.008 * yOfX dih4XDivSqrtdeltaPosbranch y1 y2 y3 y4 y5 y6 ∨
      eta_y y4 y5 y6 ^ 2 > 2

/-- HOL ineq entry `CIHTIUM` (ineq.hl:1462).  Box [1,1]³×[2hmin,√8]³. -/
def bank_CIHTIUM : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 * hminus ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 * hminus ≤ y6 → y6 ≤ Real.sqrt 8 →
    eta_y y4 y5 y6 ^ 2 > 2

/-- HOL ineq entry `CJFZZDW` (ineq.hl:1479).  Box
[1,1]³×[2hplus,√8]×[2hplus,√8]×[2,√8]. -/
def bank_CJFZZDW : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2 * hplus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 * hplus ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    eta_y y4 y5 y6 ^ 2 > 2

/-- HOL ineq entry `TSKAJXY-GXSABWC DIV` (ineq.hl:359).  x-space entry
(variables are squared lengths).  Box
[2.8²,8]×[4,2.01²]×[4,2.01²]×[2.8²,8]×[4,2.01²]×[4,2.01²]. -/
def bank_TSKAJXYGXSA : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, (2.8 : ℝ) ^ 2 ≤ x1 → x1 ≤ 8 →
    4 ≤ x2 → x2 ≤ 2.01 ^ 2 → 4 ≤ x3 → x3 ≤ 2.01 ^ 2 →
    (2.8 : ℝ) ^ 2 ≤ x4 → x4 ≤ 8 → 4 ≤ x5 → x5 ≤ 2.01 ^ 2 →
    4 ≤ x6 → x6 ≤ 2.01 ^ 2 →
    1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 +
          solEuler345XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
          solEuler156XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
          solEuler246XDivSqrtdelta x1 x2 x3 x4 x5 x6) -
      (8 * mm2 / Real.pi) *
        (ldih2XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
          ldih3XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
          ldih5XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
          ldih6XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6) ≥ 0 ∨
      deltaX x1 x2 x3 x4 x5 x6 < 0

/-- HOL ineq entry `TSKAJXY-delta_x4` (ineq.hl:341).  x-space entry.  Box
[4,2.01²]×[4,2.01²]×[2.8²,8]×[4,2.01²]×[4,2.01²]×[2.8²,8]. -/
def bank_TSKAJXYdx4 : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, 4 ≤ x1 → x1 ≤ 2.01 ^ 2 → 4 ≤ x2 → x2 ≤ 2.01 ^ 2 →
    (2.8 : ℝ) ^ 2 ≤ x3 → x3 ≤ 8 → 4 ≤ x4 → x4 ≤ 2.01 ^ 2 →
    4 ≤ x5 → x5 ≤ 2.01 ^ 2 → (2.8 : ℝ) ^ 2 ≤ x6 → x6 ≤ 8 →
    0 < deltaX4 x1 x2 x3 x4 x5 x6

/-- HOL ineq entry `TSKAJXY-eulerA` (ineq.hl:324).  x-space entry.  Box
[2.8²,8]×[4,2.01²]×[4,2.01²]×[2.8²,8]×[4,2.01²]×[4,2.01²]. -/
def bank_TSKAJXYeulerA : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, (2.8 : ℝ) ^ 2 ≤ x1 → x1 ≤ 8 →
    4 ≤ x2 → x2 ≤ 2.01 ^ 2 → 4 ≤ x3 → x3 ≤ 2.01 ^ 2 →
    (2.8 : ℝ) ^ 2 ≤ x4 → x4 ≤ 8 → 4 ≤ x5 → x5 ≤ 2.01 ^ 2 →
    4 ≤ x6 → x6 ≤ 2.01 ^ 2 →
    0 < eulerAX x1 x2 x3 x4 x5 x6

/-- HOL ineq entry `TSKAJXY-XLLIPLS` (ineq.hl:304).  Box
[2hplus,√8]×[2,2.01]×[2,2.01]×[2hplus,2.8]×[2,2.01]×[2,2.01]. -/
def bank_TSKAJXYXLLIPLS : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
    2 ≤ y2 → y2 ≤ 2.01 → 2 ≤ y3 → y3 ≤ 2.01 →
    2 * hplus ≤ y4 → y4 ≤ 2.8 → 2 ≤ y5 → y5 ≤ 2.01 → 2 ≤ y6 → y6 ≤ 2.01 →
    0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun

/-- HOL ineq entry `TSKAJXY-WKGUESB sym` (ineq.hl:281).  Box
[2hplus,√8]×[2.01,2hmin]×[2,2hmin]×[2hplus,√8]×[2,2hmin]×[2,2hmin]. -/
def bank_TSKAJXYWKGUESBsym : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
    2.01 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hplus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ∨
      y2 < y3 ∨ y2 < y5 ∨ y2 < y6 ∨ y1 < y4

/-- HOL ineq entry `TSKAJXY-IYOUOBF sharp v2` (ineq.hl:242).  Box
[2hplus,√8]×[2,2.001]×[2,2.001]×[2,2hmin]×[2,2.001]×[2,2.001]. -/
def bank_TSKAJXYIYOUOBFsharpv2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
    2 ≤ y2 → y2 ≤ 2.001 → 2 ≤ y3 → y3 ≤ 2.001 → 2 ≤ y4 → y4 ≤ 2 * hminus →
    2 ≤ y5 → y5 ≤ 2.001 → 2 ≤ y6 → y6 ≤ 2.001 →
    0 ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun

/-- HOL ineq entry `TSKAJXY-IYOUOBF sym` (ineq.hl:223).  Box
[2hplus,√8]×[2.001,2hmin]×[2,2hmin]×[2,2hmin]×[2,2hmin]×[2,2hmin]. -/
def bank_TSKAJXYIYOUOBFsym : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
    2.001 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    0 ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ∨ y2 < y3 ∨ y2 < y5 ∨ y2 < y6

/-- HOL ineq entry `TSKAJXY-RIBCYXU sym` (ineq.hl:183).  Box
[2.001,2hmin]×[2,2hmin]⁵. -/
def bank_TSKAJXYRIBCYXUsym : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2.001 ≤ y1 → y1 ≤ 2 * hminus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ∨
      y1 < y2 ∨ y1 < y3 ∨ y1 < y4 ∨ y1 < y5 ∨ y1 < y6 ∨
      y2 < y3 ∨ y2 < y5 ∨ y2 < y6

/-- HOL ineq entry `TSKAJXY-RIBCYXU sharp` (ineq.hl:165).  Box
[2,2.001]⁶. -/
def bank_TSKAJXYRIBCYXUsharp : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 ≤ y1 → y1 ≤ 2.001 → 2 ≤ y2 → y2 ≤ 2.001 →
    2 ≤ y3 → y3 ≤ 2.001 → 2 ≤ y4 → y4 ≤ 2.001 → 2 ≤ y5 → y5 ≤ 2.001 →
    2 ≤ y6 → y6 ≤ 2.001 →
    0 ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun

/-- HOL ineq entry `TSKAJXY-TADIAMB` (ineq.hl:127).  Box
[2hplus,√8]×[2hplus,√8]×[2,√8]⁴. -/
def bank_TSKAJXYTADIAMB : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
    2 * hplus ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    2 < yOfX rad2X y1 y2 y3 y4 y5 y6

/-- HOL ineq entry `GRKIBMP A V2` (ineq.hl:1520).  Box
[2,2hplus]×[1,1]⁵. -/
def bank_GRKIBMPAV2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 ≤ y1 → y1 ≤ 2 * hplus → 1 ≤ y2 → y2 ≤ 1 →
    1 ≤ y3 → y3 ≤ 1 → 1 ≤ y4 → y4 ≤ 1 → 1 ≤ y5 → y5 ≤ 1 → 1 ≤ y6 → y6 ≤ 1 →
    0.008 < yOfX (gamma2x1DivAV2 (h0cut y1)) y1 y2 y3 y4 y5 y6

-- RESOLVED (GRKIBMP A V2 hand-proof lane, 2026-10-12): the entry is proved
-- analytically below as `bank_GRKIBMPAV2_proof` — no certificate data needed.
-- Route (scout §2.2): h0cut split at 2*h0; m=1 arm linear-lfun with the
-- sharpened seed `arccos(1/3) ≤ 1231/1000` (two-sided `mm1` enclosure); m=0
-- arm reuses the B V2 factored kernel (`p21_av2_grk_factor`).  Assembly:
-- `nliGrkBank := ⟨bank_GRKIBMPAV2_proof, bank_GRKIBMPBV2_proof⟩` closes the
-- grk slice (the old "needs ε-margin/weak encoding" note is obsolete).

/-- HOL ineq entry `GRKIBMP B V2` (ineq.hl:1537).  Box
[2hplus,√8]×[1,1]⁵. -/
def bank_GRKIBMPBV2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
    1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 → 1 ≤ y4 → y4 ≤ 1 →
    1 ≤ y5 → y5 ≤ 1 → 1 ≤ y6 → y6 ≤ 1 →
    0 ≤ yOfX (gamma2x1DivAV2 0) y1 y2 y3 y4 y5 y6

/-- HOL `cell3_hyp` (merge_ineq.hl:3490-3495). -/
def cell3_bank : Prop :=
  bank_QZECFICwt0 ∧ bank_QZECFICwt0corner ∧ bank_QZECFICwt0sqrt8 ∧
    bank_QZECFICwt1 ∧ bank_QZECFICwt2A ∧ bank_CIHTIUM ∧ bank_CJFZZDW

/-- HOL `tsk_hyp` (merge_ineq.hl:1370-1377, string order). -/
def tsk_bank : Prop :=
  bank_TSKAJXYGXSA ∧ bank_TSKAJXYIYOUOBFsharpv2 ∧ bank_TSKAJXYIYOUOBFsym ∧
    bank_TSKAJXYRIBCYXUsharp ∧ bank_TSKAJXYRIBCYXUsym ∧ bank_TSKAJXYTADIAMB ∧
    bank_TSKAJXYWKGUESBsym ∧ bank_TSKAJXYXLLIPLS ∧ bank_TSKAJXYdx4 ∧
    bank_TSKAJXYeulerA

/-- HOL bank entries `GRKIBMP A V2` ∧ `GRKIBMP B V2`
(`add_hyp` order, merge_ineq.hl:3795). -/
def grk_bank : Prop := bank_GRKIBMPAV2 ∧ bank_GRKIBMPBV2

/-! ## bank rest: the other 62 entries of the 81-entry registry
`packNonlinearNonOx3q1hIds` (IdLists.lean:43-126) — A11 车道 2026-10-08
GIANT 诚实收窄（MERGE-INEQ wave 0 后继）。

原形是单叶 `def pack_nonlinear_rest : Prop := sorry`——语句本身未定形的
unknown-Prop（比 sorried 定理更不诚实：消费方免费获得 62 条未知不等式）。
本波按 19 条消费切片同款 arrow 形逐条显式定形（HOL `Sphere.ineq` 盒子
展开，章程 §6.2）：字面 40 条直录 ineq.hl（行号经 ineqs.json g4e 独立
解析交叉验证），生成 22 条（ZTGIJCF4 ×16、QITNPEA1 ×6）按 make_F4 /
add_QITNPEA1 循环的模板参数化转录。命名 `bank_` + idv 挤压；合取顺序 =
IdLists 注册序（去 19 条消费切片；章程 §4.3 item 8 的既有重排注记继续
有效）。**证明债逐条落在各 `bank_*` 陈述上**：证书不在库（deferred-
compute，G4 主案章程 §2.2/附则1；在库两案 `QITNPEA 3725403817`（内核
闭合 2026-09-18）与 `1965189142 34`（Cases.C1965189142x34）的粘合入
§2a 查表 = 量产接线波，本波不动）。 -/

/-- HOL ineq entry `6096597438 b` (ineq.hl:1661).  Box [3,64]×[1,1]⁵. -/
def bank_6096597438b : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, 3 ≤ x1 → x1 ≤ 64 → 1 ≤ x2 → x2 ≤ 1 → 1 ≤ x3 → x3 ≤ 1 →
    1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
    2 * Real.pi - 2 * asn797k x1 x2 x3 x4 x5 x6 >
      0.591 - 0.0331 * x1 + 0.506 * lfun 1 + 1

/-- HOL ineq entry `6096597438 a` (ineq.hl:1650).  Box [1,1]（单变量 `h`）. -/
def bank_6096597438a : Prop :=
  ∀ h : ℝ, 1 ≤ h → h ≤ 1 → 0.591 - 0.0331 * 64 + 0.506 * lfun 1 + 1 < 0

/-- HOL ineq entry `1965189142 a` (ineq.hl:1598).  Box
[1.0,1.26]×[3,34]×[1,1]⁴. -/
def bank_1965189142a : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, 1 ≤ x1 → x1 ≤ 1.26 → 3 ≤ x2 → x2 ≤ 34 →
    1 ≤ x3 → x3 ≤ 1 → 1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
    2 * Real.pi - 2 * asnFnhk x1 x2 x3 x4 x5 x6 >
      0.591 - 0.0331 * x2 + 0.506 * lfunY1 x1 x2 x3 x4 x5 x6

/-- HOL ineq entry `1965189142 34` (ineq.hl:1587).  Box [1.0,1.26]×[1,1]⁵.
G4 证书在库（`Kepler.Interval.Cases.C1965189142x34`），粘合待量产接线波. -/
def bank_1965189142x34 : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ, 1 ≤ x1 → x1 ≤ 1.26 → 1 ≤ x2 → x2 ≤ 1 →
    1 ≤ x3 → x3 ≤ 1 → 1 ≤ x4 → x4 ≤ 1 → 1 ≤ x5 → x5 ≤ 1 → 1 ≤ x6 → x6 ≤ 1 →
    0.591 - 0.0331 * 34 + 0.506 * lfunY1 x1 x2 x3 x4 x5 x6 < 0

/-- HOL ineq entry `JSPEVYT` (ineq.hl:1495).  Box
[1,1]³×[2hmin,√8]²×[2,√8]. -/
def bank_JSPEVYT : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 1 ≤ y1 → y1 ≤ 1 → 1 ≤ y2 → y2 ≤ 1 → 1 ≤ y3 → y3 ≤ 1 →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 * hminus ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    eta_y y4 y5 y6 ^ 2 > 1.34 ^ 2

/-- HOL ineq entry `QITNPEA 4003532128 a` (ineq.hl:1290).  Box
[2hmin,2hplus]×[2,√8]×[√2,√2]³×[2,√8]. -/
def bank_QITNPEA4003532128a : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → Real.sqrt 2 ≤ y3 → y3 ≤ Real.sqrt 2 →
    Real.sqrt 2 ≤ y4 → y4 ≤ Real.sqrt 2 → Real.sqrt 2 ≤ y5 → y5 ≤ Real.sqrt 2 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    delta4Y y1 y2 y3 y4 y5 y6 > 25 ∨
      deltaY y1 y2 y3 y4 y5 y6 > 0.14 ∨ deltaY y1 y2 y3 y4 y5 y6 < 0

/-- HOL ineq entry `IXPOTPA` (ineq.hl:1265).  Box
[2hmin,2hplus]×[2,2hmin]²×[√8,4hmin]×[2,2hmin]². -/
def bank_IXPOTPA : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    Real.sqrt 8 ≤ y4 → y4 ≤ 4 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    deltaY y1 y2 y3 y4 y5 y6 < 0 ∨ delta4Y y1 y2 y3 y4 y5 y6 > 0 ∨
      4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 <
        3.07 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6 ∨
      4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 >
        6.45 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6 ∨
      eta_y y1 y2 y6 ^ 2 > 1.34 ^ 2 ∨ eta_y y1 y3 y5 ^ 2 > 1.34 ^ 2 ∨
      yOfX (gamma23Full8X (h0cut y1)) y1 y2 y3 y4 y5 y6 > 3 * 0.0057

/-- HOL ineq entry `TXQTPVC` (ineq.hl:1241).  Box
[2hmin,2hplus]×[2,2hmin]²×[2,√8]×[2,2hmin]². -/
def bank_TXQTPVC : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    yOfX (gamma23Full8X (h0cut y1)) y1 y2 y3 y4 y5 y6 > 3 * 0.0057 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 < 2 ∨ dihY y1 y2 y3 y4 y5 y6 > 2.089 ∨
      dihY y1 y2 y3 y4 y5 y6 < 1.946 ∨
      eta_y y1 y2 y6 ^ 2 > 1.34 ^ 2 ∨ eta_y y1 y3 y5 ^ 2 > 1.34 ^ 2

/-- HOL ineq entry `QITNPEA 3725403817` (ineq.hl:1221).  Box
[2hmin,2hplus]×[2,2hmin]³×[2,2.1]×[2,2hmin]².
G4 证书内核闭合（964,984 叶，2026-09-18，公理标准三），粘合待量产接线波. -/
def bank_QITNPEA3725403817 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2.1 → 2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
    dihY y1 y2 y3 y4 y5 y6 < 1.56

/-- HOL ineq entry `QITNPEAv2 4003532128` (ineq.hl:1193).  Box
[2hmin,2hplus]×[2,2hmin]³×[2,√8]×[2,2hmin]². -/
def bank_QITNPEAv24003532128 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    eta_y y1 y2 y6 ^ 2 > 1.34 ^ 2 ∨ eta_y y1 y3 y5 ^ 2 > 1.34 ^ 2 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 < 2 ∨ y2 < y3 ∨ y2 < y5 ∨ y2 < y6 ∨
      yOfX (gamma23Full8X (h0cut y1)) y1 y2 y3 y4 y5 y6 -
          0.00457511 - 0.00609451 * dihY y1 y2 y3 y4 y5 y6 > 0

/-- HOL ineq entry `PEMKWKU` (ineq.hl:1169).  Box
[2hmin,2hplus]×[2,√8]×[2,2hmin]×[2,√8]×[2,2hmin]×[2,√8]. -/
def bank_PEMKWU : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    yOfX (gamma23Keep135X (h0cut y1)) y1 y2 y3 y4 y5 y6 >
        aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 < 2 ∨ dihY y1 y2 y3 y4 y5 y6 > 1.074 ∨
      eta_y y1 y2 y6 ^ 2 > 2 ∨ eta_y y1 y2 y6 ^ 2 < 1.34 ^ 2 ∨
      eta_y y1 y3 y5 ^ 2 > 1.34 ^ 2

/-- HOL ineq entry `TEWNSCJ` (ineq.hl:1146).  Box
[2hmin,2hplus]×[2,2hmin]³×[2,√8]×[2,2hmin]². -/
def bank_TEWNSCJ : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    yOfX (gamma23Full8X (h0cut y1)) y1 y2 y3 y4 y5 y6 >
        aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 < 2 ∨
      eta_y y1 y2 y6 ^ 2 > 1.34 ^ 2 ∨ eta_y y1 y3 y5 ^ 2 > 1.34 ^ 2

/-- HOL ineq entry `QITNPEA  5400790175 b` (ineq.hl:1121).  Box
[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]². -/
def bank_QITNPEA5400790175b : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + betaBumpLb +
        gamma3f y1 y2 y6 (Real.sqrt 2) lmfun > 0.0057 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2 ∨ eta_y y1 y2 y6 ^ 2 > 1.34 ^ 2

/-- HOL ineq entry `QITNPEA  5400790175 a` (ineq.hl:1103).  Box 同上. -/
def bank_QITNPEA5400790175a : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + betaBumpLb > 0.0057 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2 ∨ eta_y y1 y2 y6 ^ 2 < 1.34 ^ 2

/-- HOL ineq entry `QITNPEA 3848804089` (ineq.hl:1059).  Box
[2hmin,2hplus]×[2,2hmin]⁵（y4 限 [2,2hmin]）. -/
def bank_QITNPEA3848804089 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun - 0.161517 +
      0.119482 * dihY y1 y2 y3 y4 y5 y6 > 0

/-- HOL ineq entry `QITNPEA 5814748276` (ineq.hl:1041).  Box 同上. -/
def bank_QITNPEA5814748276 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun - 0.00127562 +
      0.00522841 * dihY y1 y2 y3 y4 y5 y6 > 0

/-- HOL ineq entry `QITNPEA 6206775865` (ineq.hl:1023).  Box 同上. -/
def bank_QITNPEA6206775865 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.0142852 -
      0.00609451 * dihY y1 y2 y3 y4 y5 y6 > 0

/-- HOL ineq entry `QITNPEA 5653753305` (ineq.hl:1004).  Box
[2hmin,2hplus]×[2,2hmin]⁵. -/
def bank_QITNPEA5653753305 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.0659 -
      0.042 * dihY y1 y2 y3 y4 y5 y6 > 0

/-- HOL ineq entry `BIXPCGW 9455898160` (ineq.hl:985).  Box
[2hmin,2hplus]×[2,2hmin]⁵.  HOL 字面 `-- #0.00569`（双重负号 = 0.00569）. -/
def bank_BIXPCGW9455898160 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > 0.00569

/-- HOL ineq entry `FWGKMBZ` (ineq.hl:967).  Box
[2hmin,2hplus]×[2,√8]⁵. -/
def bank_FWGKMBZ : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    yOfX deltaX y1 y2 y3 y4 y5 y6 > 0

/-- HOL ineq entry `FHBVYXZ b` (ineq.hl:942).  Box
[2hmin,2hplus]×[2,2hmin]⁵. -/
def bank_FHBVYXZb : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun +
        gamma3f y1 y2 y6 (Real.sqrt 2) lmfun > 0 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2 ∨ eta_y y1 y2 y6 ^ 2 > 1.34 ^ 2

/-- HOL ineq entry `FHBVYXZ a` (ineq.hl:914).  Box 同上. -/
def bank_FHBVYXZa : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > 0 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2 ∨ eta_y y1 y2 y6 ^ 2 < 1.34 ^ 2

/-- HOL ineq entry `FHBVYXZv2 a` (ineq.hl:888).  Box 同上. -/
def bank_FHBVYXZv2a : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > 0.0057 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2 ∨ eta_y y1 y3 y5 ^ 2 < 1.34 ^ 2

/-- HOL ineq entry `QITNPEA 2134082733` (ineq.hl:864).  Box
[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]². -/
def bank_QITNPEA2134082733 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + betaBumpLb - 0.213849 +
        0.119482 * dihY y1 y2 y3 y4 y5 y6 > 0 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-! ### QITNPEA1 生成族（6 条；ineq.hl:827-845 `mk_QITNPEA1` 模板 +
:845-862 `add_QITNPEA1` 循环 i3∈{1,2}, i4∈{0,1,2}）

边界 x i = nth [2; 2*hmin; 2*hplus; √8] i，X i = x (i+1)：
(x 0, X 0) = (2, 2*hmin)，(x 1, X 1) = (2*hmin, 2*hplus)，
(x 2, X 2) = (2*hplus, √8)；w = 1 + 子临界计数（i=1 记 1）。
转录注记（registered reconciliation, 章程 §4.3）：源文模板体 ineq.hl:835
在 `lmfun / &w` 后有残段 `// + &m *beta_bump_lb`（其中 `m` 的 let 绑定在该
模板内被注释；2012-12-01 doc 注记「Removed beta_bump_lb」），本形按删除
断言转录（γ/w 项）；beta 项的衔接见 merge_ineq.hl:2037-2056
`ineq_approxA_ztg4`（`&m * beta_bump_lb ≤ beta_bumpA_y` 桥）。 -/

/-- QITNPEA1 模板下界：i=0 ↦ 2，i=1 ↦ 2*hmin，i=2 ↦ 2*hplus. -/
noncomputable def bank_QITNPEA1lo : ℕ → ℝ :=
  fun i => if i = 0 then 2 else if i = 1 then 2 * hminus else 2 * hplus

/-- QITNPEA1 模板上界：i=0 ↦ 2*hmin，i=1 ↦ 2*hplus，i=2 ↦ √8. -/
noncomputable def bank_QITNPEA1hi : ℕ → ℝ :=
  fun i => if i = 0 then 2 * hminus else if i = 1 then 2 * hplus else Real.sqrt 8

/-- 子临界指示（i=1 ↦ 1，其余 ↦ 0；两生成族共用）. -/
def bankGenMid : ℕ → ℝ := fun i => if i = 1 then 1 else 0

/-- QITNPEA1 参数化模板（ineq.hl:829-838 引文逐句）. -/
def bank_QITNPEA1tmpl (i3 i4 : ℕ) : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ,
    2 * hminus ≤ y1 → y1 ≤ 2 * hplus → 2 ≤ y2 → y2 ≤ 2 * hminus →
    bank_QITNPEA1lo i3 ≤ y3 → y3 ≤ bank_QITNPEA1hi i3 →
    bank_QITNPEA1lo i4 ≤ y4 → y4 ≤ bank_QITNPEA1hi i4 →
    2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun /
        (1 + bankGenMid i3 + bankGenMid i4) > 0.0057 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL idv `QITNPEA1 2 2 9063653052 A` (ineq.hl:845-862 循环). -/
def bank_QITNPEA1_2_2 : Prop := bank_QITNPEA1tmpl 2 2
/-- HOL idv `QITNPEA1 2 1 9063653052 A`. -/
def bank_QITNPEA1_2_1 : Prop := bank_QITNPEA1tmpl 2 1
/-- HOL idv `QITNPEA1 2 0 9063653052 A`. -/
def bank_QITNPEA1_2_0 : Prop := bank_QITNPEA1tmpl 2 0
/-- HOL idv `QITNPEA1 1 2 9063653052 A`. -/
def bank_QITNPEA1_1_2 : Prop := bank_QITNPEA1tmpl 1 2
/-- HOL idv `QITNPEA1 1 1 9063653052 A`. -/
def bank_QITNPEA1_1_1 : Prop := bank_QITNPEA1tmpl 1 1
/-- HOL idv `QITNPEA1 1 0 9063653052 A`. -/
def bank_QITNPEA1_1_0 : Prop := bank_QITNPEA1tmpl 1 0

/-- 模板实例化抽查：i3=2 ↦ (2*hplus, √8)；实例 (2,1) 的 w 项 = 1+0+1 = 2. -/
example : bank_QITNPEA1lo 2 = 2 * hplus ∧ bank_QITNPEA1hi 2 = Real.sqrt 8 ∧
    1 + bankGenMid 2 + bankGenMid 1 = 2 := by
  norm_num [bank_QITNPEA1lo, bank_QITNPEA1hi, bankGenMid]

/-- HOL ineq entry `QITNPEA 9939613598` (ineq.hl:798).  Box
[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]². -/
def bank_QITNPEA9939613598 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hplus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun - 0.00457511 -
        0.00609451 * dihY y1 y2 y3 y4 y5 y6 > 0 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `BIXPCGW 7274157868 a` (ineq.hl:776).  Box
[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]². -/
def bank_BIXPCGW7274157868a : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hplus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > 0.0057 ∨
      dihY y1 y2 y3 y4 y5 y6 < 2.3

/-- HOL ineq entry `BIXPCGW b` (ineq.hl:758).  Box
[2hmin,2hplus]×[2,√8]²×[2,2hplus]×[2,√8]². -/
def bank_BIXPCGWb : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ 2 * hplus → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    delta4Y y1 y2 y3 y4 y5 y6 > 0 ∨
      deltaY y1 y2 y3 y4 y5 y6 > 60 ∨ deltaY y1 y2 y3 y4 y5 y6 < 0

/-- HOL ineq entry `BIXPCGW 1738910218 a2` (ineq.hl:739).  Box 同 `BIXPCGW b`. -/
def bank_BIXPCGW1738910218a2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ 2 * hplus → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    dihY y1 y2 y3 y4 y5 y6 < 2.3

/-- HOL ineq entry `BIXPCGW 7080972881 a2` (ineq.hl:721).  Box
[2hmin,2hplus]×[2hmin,√8]×[2,√8]⁴. -/
def bank_BIXPCGW7080972881a2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 * hminus ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    dihY y1 y2 y3 y4 y5 y6 < 2.3

/-- HOL ineq entry `BIXPCGW 6652007036 a2` (ineq.hl:701).  Box
[2hmin,2hplus]×[2,√8]⁵. -/
def bank_BIXPCGW6652007036a2 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    dihY y1 y2 y3 y4 y5 y6 < 2.8

/-- HOL ineq entry `GLFVCVK4 2477216213 y4subcrit` (ineq.hl:675).  Box
[2hmin,2hplus]×[2hmin,√8]×[2,2hmin]⁴. -/
def bank_GLFVCVK4y4subcrit : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 * hminus ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 ≤ y4 → y4 ≤ 2 * hminus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 > 0.0057 ∨
      eta_y y1 y2 y6 ^ 2 < 1.34 ^ 2 ∨ yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `GLFVCVK4 2477216213 y4supercrit` (ineq.hl:649).  Box
[2hmin,2hplus]×[2,2h0]×[2,2hmin]×[2hplus,√8]×[2,2hmin]². -/
def bank_GLFVCVK4y4supercrit : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hplus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 > 0.0057 ∨
      eta_y y1 y2 y6 ^ 2 < 1.34 ^ 2 ∨ yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `GLFVCVK4 2477216213 y4crit` (ineq.hl:623).  Box
[2hmin,2hplus]×[2hmin,2hplus]×[2,2hmin]×[2hmin,2hplus]×[2,2hmin]². -/
def bank_GLFVCVK4y4crit : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 * hminus ≤ y2 → y2 ≤ 2 * hplus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 3 > 0.0057 ∨
      eta_y y1 y2 y6 ^ 2 < 1.34 ^ 2 ∨ yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `GLFVCVK4a 8328676778` (ineq.hl:586).  Box
[2hmin,2hplus]×[2,2hmin]²×[2hmin,2hplus]×[2,2hmin]². -/
def bank_GLFVCVK4a8328676778 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ 2 * hminus → 2 ≤ y3 → y3 ≤ 2 * hminus →
    2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 2 ≤ y5 → y5 ≤ 2 * hminus →
    2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + betaBumpForceY y1 y2 y3 y4 y5 y6 >
      0 ∨ yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `GLFVCVK4 2477216213` (ineq.hl:559).  Box
[2hmin,2hplus]×[2,√8]⁵. -/
def bank_GLFVCVK4 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > 0 ∨
      norm2hh y1 y2 y3 y4 y5 y6 < (hplus - hminus) ^ 2 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `MKFKQWU halfwt` (ineq.hl:523).  Box
[2hmin,2hplus]×[2hplus,√8]×[2,√8]×[2hmin,√8]×[2,√8]². -/
def bank_MKFKQWUhalfwt : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 * hplus ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL ineq entry `MKFKQWU` (ineq.hl:502).  Box
[2hmin,2hplus]×[2hmin,√8]²×[2,√8]×[2hmin,√8]². -/
def bank_MKFKQWU : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 * hminus ≤ y2 → y2 ≤ Real.sqrt 8 → 2 * hminus ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 * hminus ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 * hminus ≤ y6 → y6 ≤ Real.sqrt 8 →
    yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-! ### ZTGIJCF4 生成族（16 条；ineq.hl:456-466 `template_F4` 模板 +
:468-476 `mk_ineq_F4` + :486-499 `make_F4` 循环 i3,i4,i5,i6∈{0,1}）

边界 x i = nth [2; 2*hmin; √8] i（i∈{0,1}），X i = x (i+1)：
(x 0, X 0) = (2, 2*hmin)，(x 1, X 1) = (2*hmin, √8)；
w = 1 + 子临界计数；m = 1 当且仅当恰一子临界且其在 y4（HOL
`if (w = 2) && (i4 = 1) then 1 else 0`）. -/

/-- ZTGIJCF4 模板下界：i=0 ↦ 2，i=1 ↦ 2*hmin. -/
noncomputable def bank_ZTGIJCF4lo : ℕ → ℝ := fun i => if i = 0 then 2 else 2 * hminus

/-- ZTGIJCF4 模板上界：i=0 ↦ 2*hmin，i=1 ↦ √8. -/
noncomputable def bank_ZTGIJCF4hi : ℕ → ℝ := fun i => if i = 0 then 2 * hminus else Real.sqrt 8

/-- ZTGIJCF4 参数化模板（template_F4 引文逐句；w/m 按 `mk_ineq_F4` 展开）. -/
def bank_ZTGIJCF4tmpl (i3 i4 i5 i6 : ℕ) : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ,
    2 * hminus ≤ y1 → y1 ≤ 2 * hplus → 2 ≤ y2 → y2 ≤ 2 * hminus →
    bank_ZTGIJCF4lo i3 ≤ y3 → y3 ≤ bank_ZTGIJCF4hi i3 →
    bank_ZTGIJCF4lo i4 ≤ y4 → y4 ≤ bank_ZTGIJCF4hi i4 →
    bank_ZTGIJCF4lo i5 ≤ y5 → y5 ≤ bank_ZTGIJCF4hi i5 →
    bank_ZTGIJCF4lo i6 ≤ y6 → y6 ≤ bank_ZTGIJCF4hi i6 →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun /
        (1 + bankGenMid i3 + bankGenMid i4 + bankGenMid i5 + bankGenMid i6) +
      (if 1 + bankGenMid i3 + bankGenMid i4 + bankGenMid i5 + bankGenMid i6 = 2 ∧
          i4 = 1 then 1 else 0 : ℝ) * betaBumpLb >
      aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6 ∨
    yOfX rad2X y1 y2 y3 y4 y5 y6 > 2

/-- HOL idv `ZTGIJCF4 1 1 1 1 1821661595` (ineq.hl:486-499 循环). -/
def bank_ZTGIJCF4_1_1_1_1 : Prop := bank_ZTGIJCF4tmpl 1 1 1 1
/-- HOL idv `ZTGIJCF4 1 1 1 0 1821661595`. -/
def bank_ZTGIJCF4_1_1_1_0 : Prop := bank_ZTGIJCF4tmpl 1 1 1 0
/-- HOL idv `ZTGIJCF4 1 1 0 1 1821661595`. -/
def bank_ZTGIJCF4_1_1_0_1 : Prop := bank_ZTGIJCF4tmpl 1 1 0 1
/-- HOL idv `ZTGIJCF4 1 1 0 0 1821661595`. -/
def bank_ZTGIJCF4_1_1_0_0 : Prop := bank_ZTGIJCF4tmpl 1 1 0 0
/-- HOL idv `ZTGIJCF4 1 0 1 1 1821661595`. -/
def bank_ZTGIJCF4_1_0_1_1 : Prop := bank_ZTGIJCF4tmpl 1 0 1 1
/-- HOL idv `ZTGIJCF4 1 0 1 0 1821661595`. -/
def bank_ZTGIJCF4_1_0_1_0 : Prop := bank_ZTGIJCF4tmpl 1 0 1 0
/-- HOL idv `ZTGIJCF4 1 0 0 1 1821661595`. -/
def bank_ZTGIJCF4_1_0_0_1 : Prop := bank_ZTGIJCF4tmpl 1 0 0 1
/-- HOL idv `ZTGIJCF4 1 0 0 0 1821661595`. -/
def bank_ZTGIJCF4_1_0_0_0 : Prop := bank_ZTGIJCF4tmpl 1 0 0 0
/-- HOL idv `ZTGIJCF4 0 1 1 1 1821661595`. -/
def bank_ZTGIJCF4_0_1_1_1 : Prop := bank_ZTGIJCF4tmpl 0 1 1 1
/-- HOL idv `ZTGIJCF4 0 1 1 0 1821661595`. -/
def bank_ZTGIJCF4_0_1_1_0 : Prop := bank_ZTGIJCF4tmpl 0 1 1 0
/-- HOL idv `ZTGIJCF4 0 1 0 1 1821661595`. -/
def bank_ZTGIJCF4_0_1_0_1 : Prop := bank_ZTGIJCF4tmpl 0 1 0 1
/-- HOL idv `ZTGIJCF4 0 1 0 0 1821661595`. -/
def bank_ZTGIJCF4_0_1_0_0 : Prop := bank_ZTGIJCF4tmpl 0 1 0 0
/-- HOL idv `ZTGIJCF4 0 0 1 1 1821661595`. -/
def bank_ZTGIJCF4_0_0_1_1 : Prop := bank_ZTGIJCF4tmpl 0 0 1 1
/-- HOL idv `ZTGIJCF4 0 0 1 0 1821661595`. -/
def bank_ZTGIJCF4_0_0_1_0 : Prop := bank_ZTGIJCF4tmpl 0 0 1 0
/-- HOL idv `ZTGIJCF4 0 0 0 1 1821661595`. -/
def bank_ZTGIJCF4_0_0_0_1 : Prop := bank_ZTGIJCF4tmpl 0 0 0 1
/-- HOL idv `ZTGIJCF4 0 0 0 0 1821661595`. -/
def bank_ZTGIJCF4_0_0_0_0 : Prop := bank_ZTGIJCF4tmpl 0 0 0 0

/-- 模板实例化抽查：边界 x/X 归约；(0,1,0,0) 恰 y4 critical ↦ w=2, m=1；
(1,1,1,1) 全 critical ↦ w=5, m=0. -/
example : bank_ZTGIJCF4lo 0 = 2 ∧ bank_ZTGIJCF4hi 0 = 2 * hminus ∧
    bank_ZTGIJCF4lo 1 = 2 * hminus ∧ bank_ZTGIJCF4hi 1 = Real.sqrt 8 ∧
    1 + bankGenMid 0 + bankGenMid 0 + bankGenMid 0 + bankGenMid 0 = 1 ∧
    (if 1 + bankGenMid 0 + bankGenMid 1 + bankGenMid 0 + bankGenMid 0 = 2 ∧
        (1 : ℕ) = 1 then 1 else 0 : ℝ) = 1 ∧
    (if 1 + bankGenMid 1 + bankGenMid 1 + bankGenMid 1 + bankGenMid 1 = 2 ∧
        (1 : ℕ) = 1 then 1 else 0 : ℝ) = 0 := by
  norm_num [bank_ZTGIJCF4lo, bank_ZTGIJCF4hi, bankGenMid]

/-- 生成族实例为纯模板应用（语句级忠实性机器锚：16+6 实例逐一 `rfl`
化简到显式盒式）. -/
example : bank_ZTGIJCF4_0_1_0_0 = bank_ZTGIJCF4tmpl 0 1 0 0 := rfl
example : bank_QITNPEA1_2_0 = bank_QITNPEA1tmpl 2 0 := rfl

/-- HOL ineq entry `ZTGIJCF0` (ineq.hl:446).  Box [1,1]（单变量 `dummy`）：
5-叶以上聚簇常数核算 `5a + b·2π > 0`. -/
def bank_ZTGIJCF0 : Prop :=
  ∀ _dummy : ℝ, 1 ≤ _dummy → _dummy ≤ 1 →
    5 * aSpine5 + bSpine5 * 2 * Real.pi > 0

/-- HOL ineq entry `GCKBQEA` (ineq.hl:1352).  Box [2hmin,2hplus]×[2,√8]⁵. -/
def bank_GCKBQEA : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    dihY y1 y2 y3 y4 y5 y6 > 0.606

/-- HOL ineq entry `RQWUDDU` (ineq.hl:1332).  Box 同上. -/
def bank_RQWUDDU : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 * hminus ≤ y1 → y1 ≤ 2 * hplus →
    2 ≤ y2 → y2 ≤ Real.sqrt 8 → 2 ≤ y3 → y3 ≤ Real.sqrt 8 →
    2 ≤ y4 → y4 ≤ Real.sqrt 8 → 2 ≤ y5 → y5 ≤ Real.sqrt 8 →
    2 ≤ y6 → y6 ≤ Real.sqrt 8 →
    dihY y1 y2 y3 y4 y5 y6 > 0.76 ∨ eta_y y1 y2 y6 ^ 2 > 2 ∨
      eta_y y1 y3 y5 ^ 2 > 2

/-- HOL bank remainder `pack_nonlinear_rest`（merge_ineq.hl:118-134 过滤的
81 条中除 19 条消费切片外的 62 条）：显式盒式逐条合取，顺序 =
IdLists.lean `packNonlinearNonOx3q1hIds` 注册序.  证明债逐条落在各
`bank_*` 陈述上（deferred-compute；在库两案的粘合注记见各 docstring）。 -/
def pack_nonlinear_rest : Prop :=
  bank_6096597438b ∧ bank_6096597438a ∧ bank_1965189142a ∧ bank_1965189142x34 ∧
    bank_JSPEVYT ∧ bank_QITNPEA4003532128a ∧ bank_IXPOTPA ∧ bank_TXQTPVC ∧
    bank_QITNPEA3725403817 ∧ bank_QITNPEAv24003532128 ∧ bank_PEMKWU ∧
    bank_TEWNSCJ ∧ bank_QITNPEA5400790175b ∧ bank_QITNPEA5400790175a ∧
    bank_QITNPEA3848804089 ∧ bank_QITNPEA5814748276 ∧ bank_QITNPEA6206775865 ∧
    bank_QITNPEA5653753305 ∧ bank_BIXPCGW9455898160 ∧ bank_FWGKMBZ ∧
    bank_FHBVYXZb ∧ bank_FHBVYXZa ∧ bank_FHBVYXZv2a ∧ bank_QITNPEA2134082733 ∧
    bank_QITNPEA1_2_2 ∧ bank_QITNPEA1_2_1 ∧ bank_QITNPEA1_2_0 ∧
    bank_QITNPEA1_1_2 ∧ bank_QITNPEA1_1_1 ∧ bank_QITNPEA1_1_0 ∧
    bank_QITNPEA9939613598 ∧ bank_BIXPCGW7274157868a ∧ bank_BIXPCGWb ∧
    bank_BIXPCGW1738910218a2 ∧ bank_BIXPCGW7080972881a2 ∧
    bank_BIXPCGW6652007036a2 ∧ bank_GLFVCVK4y4subcrit ∧
    bank_GLFVCVK4y4supercrit ∧ bank_GLFVCVK4y4crit ∧
    bank_GLFVCVK4a8328676778 ∧ bank_GLFVCVK4 ∧ bank_MKFKQWUhalfwt ∧
    bank_MKFKQWU ∧ bank_ZTGIJCF4_1_1_1_1 ∧ bank_ZTGIJCF4_1_1_1_0 ∧
    bank_ZTGIJCF4_1_1_0_1 ∧ bank_ZTGIJCF4_1_1_0_0 ∧ bank_ZTGIJCF4_1_0_1_1 ∧
    bank_ZTGIJCF4_1_0_1_0 ∧ bank_ZTGIJCF4_1_0_0_1 ∧ bank_ZTGIJCF4_1_0_0_0 ∧
    bank_ZTGIJCF4_0_1_1_1 ∧ bank_ZTGIJCF4_0_1_1_0 ∧ bank_ZTGIJCF4_0_1_0_1 ∧
    bank_ZTGIJCF4_0_1_0_0 ∧ bank_ZTGIJCF4_0_0_1_1 ∧ bank_ZTGIJCF4_0_0_1_0 ∧
    bank_ZTGIJCF4_0_0_0_1 ∧ bank_ZTGIJCF4_0_0_0_0 ∧ bank_ZTGIJCF0 ∧
    bank_GCKBQEA ∧ bank_RQWUDDU

/-- HOL `pack_nonlinear_non_ox3q1h` (merge_ineq.hl:118-122).  Structured
form (MERGE-INEQ wave 0, route A'): the 19 TSKAJXY consumption slices
(§1.2 table) + the 62-entry rest leaf.  Against the 81-entry HOL bank
this differs by conjunction reordering + rest folding — registered
reconciliation (charter §4.3 item 8). -/
def pack_nonlinear_non_ox3q1h : Prop :=
  cell3_bank ∧ tsk_bank ∧ grk_bank ∧ pack_nonlinear_rest

/-- HOL `tsk_hyp` (body was `sorry`; now the tsk slice bank). -/
def tsk_hyp : Prop := tsk_bank

/-- Named projection of the cell3 slice group (no bare `.1` chains;
charter §6.5). -/
theorem proj_cell3_bank (h : pack_nonlinear_non_ox3q1h) : cell3_bank := h.1

/-- Named projection of the tsk slice group. -/
theorem proj_tsk_bank (h : pack_nonlinear_non_ox3q1h) : tsk_bank := h.2.1

/-- Named projection of the GRKIBMP slice group. -/
theorem proj_grk_bank (h : pack_nonlinear_non_ox3q1h) : grk_bank := h.2.2.1

/-- HOL `frustum u v h a` (vol1.hl; 4th argument inert, kept for arity):
the slab `0 <= (x-u).dot(v-u) <= h * norm(v-u)`.  Reconstructed from use
sites (FRUSTT_RCONE_GE, MCELL2_VOL_SPLIT_EXPLICIT). -/
def frustum (u v : V3) (h _a : ℝ) : Set V3 :=
  {x : V3 | 0 ≤ (x - u) ⬝ᵥ (v - u) ∧ (x - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖}

/-- HOL `frustt u v h a` (vol1.hl): `frustum u v h a ∩ rcone_gt u v a`.
Reconstructed from use sites. -/
def frustt (u v : V3) (h a : ℝ) : Set V3 :=
  frustum u v h a ∩ rconeGt u v a

/-! ## TSKAJXY2.hl: the 0/3/4-cell special case -/

/-- HOL `cell3_from_ineq` (TSKAJXY2.hl:61-70). -/
def cell3_from_ineq : Prop :=
  ∀ y4 y5 y6 : ℝ, 2 ≤ y4 → 2 ≤ y5 → 2 ≤ y6 →
    y4 ≤ 2 * Real.sqrt 2 → y5 ≤ 2 * Real.sqrt 2 → y6 ≤ 2 * Real.sqrt 2 →
    eta_y y4 y5 y6 < Real.sqrt 2 → 0 ≤ gamma3f y4 y5 y6 (Real.sqrt 2) lmfun

/-- HOL `GRKIBMP_concl` (TSKAJXY2.hl:73-75). -/
def GRKIBMP_concl : Prop :=
  ∀ y : ℝ, 2 ≤ y → y ≤ Real.sqrt 8 → 0 ≤ gamma2_x_div_azim_v2 (h0cut y) (y * y)

/-- HOL `tsk_hyp_new` (TSKAJXY2.hl:77-78). -/
def tsk_hyp_new : Prop := GRKIBMP_concl ∧ cell3_from_ineq ∧ tsk_hyp

/- HOL `cell3_from_ineq_thm` — its declaration block was moved verbatim
(pure block move; statement and docstring byte-identical) to the end of the
wave-2a kit below, after `mi_REAL_WLOG_SIMPLEX_3d`, so the wave-2b proof can
consume the `mi_*` kit (Lean has no forward references; the HOL source makes
the same move: the theorem sits at merge_ineq.hl:3507, after its kit at
:2873-3425).  See `cell3_from_ineq_thm` below. -/

/-! ## MERGE-INEQ wave 1: GRKIBMP dispatcher helpers

Mirror pieces of the HOL proof body (merge_ineq.hl:3794-3816), kept
private: the two `if`-expansions of `h0cut` (optimize.hl:138/146), the
numeric `h0 < hplus` (Nonlinear_lemma.hl:957-961), and the
`funext`-shape projection `nonf_gamma2_x1_div_a_v2
(functional_equation.hl:1237-1244)`. -/

/-- HOL `Optimize.h0cutA` (optimize.hl:138-144): at or below the cut
`2 * h0` the weight is `1`. -/
private theorem p21_h0cutA (y : ℝ) (hy : y ≤ 2 * h0) : h0cut y = 1 := by
  simp only [h0cut, if_pos hy]

/-- HOL `Optimize.h0cutB` (optimize.hl:146-152): above the cut the
weight is `0`. -/
private theorem p21_h0cutB (y : ℝ) (hy : 2 * h0 < y) : h0cut y = 0 := by
  simp only [h0cut, if_neg (show ¬(y ≤ 2 * h0) from fun hc => absurd hy (by linarith))]

/-- HOL `Nonlinear_lemma.h0_lt_hplus` (Nonlinear_lemma.hl:957-961):
numeric (`1.26 < 1.3254`). -/
private theorem p21_h0_lt_hplus : h0 < hplus := by norm_num [h0, hplus]

/-- HOL `Functional_equation.nonf_gamma2_x1_div_a_v2`
(functional_equation.hl:1237-1244): the six-variable lift of
`gamma2_x_div_azim_v2` ignores its last five arguments. -/
private theorem p21_nonf_gamma2x1DivAV2 (m x1 x2 x3 x4 x5 x6 : ℝ) :
    gamma2x1DivAV2 m x1 x2 x3 x4 x5 x6 = gamma2_x_div_azim_v2 m x1 := rfl

/-- The same projection in the `y_of_x`-packaged form the bank entries
are stated in (`yOfX` rescales to squared lengths, and the lift projects
back to `y1` alone, exactly the `(y * y)` x-argument of `GRKIBMP_concl`). -/
private theorem p21_nonf_gamma2x1DivAV2_yOfX (m y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX (gamma2x1DivAV2 m) y1 y2 y3 y4 y5 y6 = gamma2_x_div_azim_v2 m (y1 * y1) :=
  rfl

/-- HOL `GRKIBMP` (merge_ineq.hl:3794-3816, `add_hyp ["GRKIBMP A V2";
"GRKIBMP B V2"] GRKIBMP_concl`; ~20-line proof: entries ineq.hl:1520-1535 /
1537-1552 instantiated at y2..y6 := 1).  MERGE-INEQ wave 0 skeleton. -/
theorem GRKIBMP : grk_bank → GRKIBMP_concl := by
  -- :3799-3800 strip the two bank entries and instantiate them at
  -- y2..y6 := 1 (the [1,1] singleton boxes close by `le_rfl`).
  rintro ⟨hA, hB⟩ y hy2 hy8
  rcases lt_or_ge y (2 * hplus) with hlt | hge
  · -- :3815 short-edge side: entry A keeps `h0cut y` symbolic and gives
    -- the strict bound `> 0.008`; final REAL_ARITH lifts it to `≥ 0`.
    have hA1 := hA y 1 1 1 1 1 hy2 (le_of_lt hlt) le_rfl le_rfl le_rfl le_rfl
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    rw [p21_nonf_gamma2x1DivAV2_yOfX] at hA1
    linarith
  · -- :3805-3810 long-edge side: `2 * h0 < 2 * hplus ≤ y` forces
    -- `h0cut y = 0` (h0cutB via h0_lt_hplus); entry B then supplies the
    -- nonnegativity with x-argument `y * y` unchanged (via the nonf
    -- defeq `p21_nonf_gamma2x1DivAV2_yOfX`).
    rw [p21_h0cutB y (by linarith [p21_h0_lt_hplus, hge])]
    exact hB y 1 1 1 1 1 hge hy8 le_rfl le_rfl le_rfl le_rfl le_rfl
      le_rfl le_rfl le_rfl le_rfl le_rfl

/-! ## MERGE-INEQ wave 1+: the GRKIBMP B V2 bank entry, proved by hand
(grkibmb scout lane W1, 2026-10-12; docs/scouts/grkibmb-scout.md §2.1)

`bank_GRKIBMPBV2` is the sharp-edge entry: its kernel vanishes exactly at
the box corner y1 = √8 (both the `8 - x` and the `1 - √x/√8` factors die
there), so no interval subdivision can separate 0 — the hand proof walks
the factorization instead.  Structure (scout §2.1): for `y = y1 ∈
[2hplus, √8]`, `gamma2_x_div_azim_v2 0 (y*y) = (√8-y) * [(√8+y)y/24 -
4·mm1/(π·√8)]`; the first factor is ≥ 0 by the box, and the bracket is
minimized at y = 2hplus where the numeric seed `p21_mm1_lt_four_thirds`
(mm1 ≈ 1.0121 < 4/3) leaves a comfortable slack after cross-multiplication.

The seed upgrades the PA20 `HJKDESR1a_1cell` bound (mm1 < π√2/3): the
crude `arccos(1/3) ≤ π/2 - 1/3` is not enough for `mm1 < 4/3`, so we take
the sin-Taylor one step further via Mathlib's cubic lower bound
`Real.sin_ge_sub_cube` at the half angle — `cos(2u) = 1 - 2·sin²u ≤
1 - 2(u - u³/6)² < 1/3` for `u = 247/400` — giving `arccos(1/3) ≤ 247/200`
and hence `sol0 ≤ 3·247/200 - π`. -/

/-- Stepping stone for `p21_mm1_lt_four_thirds`: `arccos(1/3) ≤ 247/200`.
From `Real.sin_ge_sub_cube` at `u = 247/400` (`sin u ≥ u - u³/6 > 0`),
`cos(247/200) = 1 - 2·sin²u ≤ 1 - 2(u - u³/6)² < 1/3` (rational check),
then antitonicity of `arccos`. -/
private theorem p21_arccos_one_third_le : Real.arccos (1 / 3 : ℝ) ≤ 247 / 200 := by
  have hpi : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  have hcos : Real.cos (247 / 200) ≤ 1 / 3 := by
    have hsb := Real.sin_ge_sub_cube (by norm_num : (0:ℝ) ≤ 247 / 400)
    have hpos : (0:ℝ) < 247 / 400 - (247 / 400) ^ 3 / 6 := by norm_num
    have hsq : (247 / 400 - (247 / 400) ^ 3 / 6) ^ 2 ≤ (Real.sin (247 / 400)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hsb 2
    have hhalf := Real.sin_sq_eq_half_sub (x := 247 / 400)
    have h2 : (2:ℝ) * (247 / 400) = 247 / 200 := by norm_num
    have hE : Real.cos (247 / 200) = 1 - 2 * (Real.sin (247 / 400)) ^ 2 := by
      rw [← h2, hhalf]; ring
    rw [hE]
    have hkey : (1:ℝ) / 3 < (247 / 400 - (247 / 400) ^ 3 / 6) ^ 2 := by norm_num
    linarith
  have hstep : Real.arccos (1 / 3) ≤ Real.arccos (Real.cos (247 / 200)) :=
    Real.arccos_le_arccos hcos
  rw [Real.arccos_cos (by linarith) (by linarith)] at hstep
  exact hstep

/-- Numeric seed for the GRKIBMP slice: `mm1 < 4/3` (mm1 ≈ 1.0121).
Strengthens PA20's `HJKDESR1a_1cell` (`mm1 < π·√2/3`), which is insufficient
here.  Chain: `sol0 = 3·arccos(1/3) - π ≤ 3·247/200 - π` (stepping stone
above), then `mm1 < 4/3 ⟺ sol0·(3√8+80) < 16π` via `tau0 = 4π - 20·sol0`,
closed by the everywhere-positive split `π(3√8+96) - 3·(247/200)(3√8+80)
= (3√8+96)(π - 3.14) + (5.04 - 1.695·√8)` with `3.14 < π` and `√8 ≤ 2.829`
(positive remainder ≈ 0.245). -/
private theorem p21_mm1_lt_four_thirds : mm1 < 4 / 3 := by
  have hpi : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  have hs8le : Real.sqrt 8 ≤ (2.829:ℝ) :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have har := p21_arccos_one_third_le
  have hsol : sol0 ≤ 3 * (247 / 200) - Real.pi := by
    have h0 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
    linarith
  have htaupos : (0:ℝ) < tau0 := by
    have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
    linarith
  have hs8nn : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
  have hkey : sol0 * (3 * Real.sqrt 8 + 80) < 16 * Real.pi := by
    have hmul : sol0 * (3 * Real.sqrt 8 + 80)
        ≤ (3 * (247 / 200) - Real.pi) * (3 * Real.sqrt 8 + 80) :=
      mul_le_mul_of_nonneg_right hsol (by linarith)
    have hE1 : (3 * (247 / 200) - Real.pi) * (3 * Real.sqrt 8 + 80)
        = 3 * (247 / 200) * (3 * Real.sqrt 8 + 80)
          - Real.pi * (3 * Real.sqrt 8 + 80) := by ring
    have hE2 : Real.pi * (3 * Real.sqrt 8 + 96)
        = Real.pi * (3 * Real.sqrt 8 + 80) + 16 * Real.pi := by ring
    have hE3 : Real.pi * (3 * Real.sqrt 8 + 96)
        - 3 * (247 / 200) * (3 * Real.sqrt 8 + 80)
        = (3 * Real.sqrt 8 + 96) * (Real.pi - 3.14)
          + (5.04 - 1.695 * Real.sqrt 8) := by ring
    have h1 : (0:ℝ) ≤ (3 * Real.sqrt 8 + 96) * (Real.pi - 3.14) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : (0:ℝ) < 5.04 - 1.695 * Real.sqrt 8 := by linarith
    have hpos1 : (0:ℝ) < Real.pi * (3 * Real.sqrt 8 + 96)
        - 3 * (247 / 200) * (3 * Real.sqrt 8 + 80) := by
      rw [hE3]; linarith
    rw [hE1] at hmul
    linarith
  have hmm1 : mm1 = sol0 * Real.sqrt 8 / tau0 := rfl
  have h3 : (0:ℝ) < 3 := by norm_num
  have hstep : sol0 * Real.sqrt 8 < (4 / 3) * tau0 := by
    rw [show (4/3:ℝ) * tau0 = 4 * tau0 / 3 from by ring, lt_div_iff₀ h3]
    have hsplit : 4 * tau0 = 16 * Real.pi - 80 * sol0 := by
      have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
      rw [h0]; ring
    have hprod : sol0 * Real.sqrt 8 * 3 = sol0 * (3 * Real.sqrt 8 + 80)
        - 80 * sol0 := by ring
    linarith
  rw [hmm1]
  exact (div_lt_iff₀ htaupos).mpr hstep

/-- The sharp-edge GRKIBMP B V2 bank entry (HOL `GRKIBMP B V2`,
ineq.hl:1537-1552; sharp.hl:246 proves the corner equality), PROVED by hand
— no certificate needed.  Proof: the `y2..y6 ∈ [1,1]` box closes by
`le_rfl` inside `gamma2x1DivAV2` (projection to `y1`, via the rfl bridge
`p21_nonf_gamma2x1DivAV2_yOfX`); with `m = 0` the mm2/lfun term dies and
`√(y1²) = y1`; the kernel factors as `(√8-y1)·[(√8+y1)y1/24 -
4mm1/(π√8)]`; the first factor is nonnegative by the box, the bracket is
bounded below at `y1 = 2hplus` by monotone growth of `(√8+y)y`, and
`96·mm1 < 128 ≤ (√8+2hplus)·2hplus·π·√8` (numeric seed
`p21_mm1_lt_four_thirds` + `π > 3.14`, `√8 > 2.828`, `(√8)² = 8`)
cross-multiplies to the bracket's nonnegativity. -/
theorem bank_GRKIBMPBV2_proof : bank_GRKIBMPBV2 := by
  intro y1 y2 y3 y4 y5 y6 hy1 hy8 _ _ _ _ _ _ _ _ _ _
  have hppos : (0:ℝ) < hplus := by norm_num [hplus]
  have hpi : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  have hs8nn : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
  have h0y1 : 0 ≤ y1 := by linarith
  have hsqrt1 : Real.sqrt (y1 * y1) = y1 := Real.sqrt_mul_self h0y1
  have hrw : (8 - y1 * y1) * y1 / 24
        - 2 * (2 * mm1 / Real.pi) * (1 - y1 / Real.sqrt 8)
      = (Real.sqrt 8 - y1)
        * ((Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)) := by
    have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    have hquad : (Real.sqrt 8 - y1) * (Real.sqrt 8 + y1) = 8 - y1 * y1 := by
      calc (Real.sqrt 8 - y1) * (Real.sqrt 8 + y1)
          = Real.sqrt 8 * Real.sqrt 8 - y1 * y1 := by ring
        _ = 8 - y1 * y1 := by rw [hsq8]
    have hden : (24:ℝ) * (Real.pi * Real.sqrt 8) ≠ 0 := by positivity
    refine mul_right_cancel₀ hden ?_
    have e1 : ((8 - y1 * y1) * y1 / 24
          - 2 * (2 * mm1 / Real.pi) * (1 - y1 / Real.sqrt 8))
        * ((24:ℝ) * (Real.pi * Real.sqrt 8))
        = (8 - y1 * y1) * y1 * (Real.pi * Real.sqrt 8)
          - 96 * mm1 * (Real.sqrt 8 - y1) := by
      field_simp
      ring
    have e2 : ((Real.sqrt 8 - y1)
          * ((Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)))
        * ((24:ℝ) * (Real.pi * Real.sqrt 8))
        = (Real.sqrt 8 - y1) * (Real.sqrt 8 + y1) * y1 * (Real.pi * Real.sqrt 8)
          - 96 * mm1 * (Real.sqrt 8 - y1) := by
      field_simp
      ring
    rw [hquad] at e2
    rw [e1, e2]
  have hbr : 0 ≤ (Real.sqrt 8 + y1) * y1 / 24
      - 4 * mm1 / (Real.pi * Real.sqrt 8) := by
    have hden : 0 < (24:ℝ) * (Real.pi * Real.sqrt 8) := by positivity
    have h43 : mm1 < 4 / 3 := p21_mm1_lt_four_thirds
    have hseed : (96:ℝ) * mm1 < 128 :=
      (mul_lt_mul_of_pos_left h43 (by norm_num : (0:ℝ) < 96)).trans_le (by norm_num)
    have hnum : (128:ℝ) ≤ (Real.sqrt 8 + 2 * hplus) * (2 * hplus)
        * (Real.pi * Real.sqrt 8) := by
      rw [show (2:ℝ) * hplus = 2.6508 from by norm_num [hplus]]
      have hs8ge : (2.828:ℝ) < Real.sqrt 8 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have hE : (Real.sqrt 8 + 2.6508) * 2.6508 * (Real.pi * Real.sqrt 8)
          = (2.6508:ℝ) * (Real.sqrt 8 * Real.sqrt 8) * Real.pi
            + (2.6508 * 2.6508) * (Real.pi * Real.sqrt 8) := by ring
      rw [Real.mul_self_sqrt (by norm_num)] at hE
      have hC : (3.14 * 2.828:ℝ) ≤ Real.pi * Real.sqrt 8 :=
        mul_le_mul hpi.le hs8ge.le (by norm_num) (by positivity)
      linarith
    have hmono : (Real.sqrt 8 + 2 * hplus) * (2 * hplus)
        ≤ (Real.sqrt 8 + y1) * y1 :=
      mul_le_mul (by linarith) hy1 (by linarith) (by linarith)
    have hchain : (96:ℝ) * mm1 < (Real.sqrt 8 + y1) * y1
        * (Real.pi * Real.sqrt 8) := by
      calc (96:ℝ) * mm1 < 128 := hseed
        _ ≤ (Real.sqrt 8 + 2 * hplus) * (2 * hplus) * (Real.pi * Real.sqrt 8) := hnum
        _ ≤ (Real.sqrt 8 + y1) * y1 * (Real.pi * Real.sqrt 8) :=
              mul_le_mul_of_nonneg_right hmono (by positivity)
    have hcross : 0 ≤ (Real.sqrt 8 + y1) * y1 * (Real.pi * Real.sqrt 8)
        - 96 * mm1 := by linarith
    have hX0 : (Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)
        = ((Real.sqrt 8 + y1) * y1 * (Real.pi * Real.sqrt 8) - 96 * mm1)
          / ((24:ℝ) * (Real.pi * Real.sqrt 8)) := by
      field_simp
      ring
    rw [hX0]
    exact div_nonneg hcross hden.le
  rw [show yOfX (gamma2x1DivAV2 0) y1 y2 y3 y4 y5 y6
      = gamma2_x_div_azim_v2 0 (y1 * y1) from rfl]
  rw [show gamma2_x_div_azim_v2 0 (y1 * y1)
      = (8 - y1 * y1) * Real.sqrt (y1 * y1) / 24
        - (2 * (2 * mm1 / Real.pi) * (1 - Real.sqrt (y1 * y1) / Real.sqrt 8)
          - (8 * mm2 / Real.pi) * 0 * lfun (Real.sqrt (y1 * y1) / 2)) from rfl,
    hsqrt1, mul_zero, zero_mul, sub_zero, hrw]
  exact mul_nonneg (by linarith) hbr


/-! ## MERGE-INEQ wave 2: the GRKIBMP A V2 bank entry, hand-proved
analytically (grkibmb scout lane W2, 2026-10-12; docs/scouts/grkibmb-scout.md
§2.2)

`bank_GRKIBMPAV2` needs `0.008 < gamma2_x_div_azim_v2 (h0cut y1) (y1*y1)` on
`y1 ∈ [2, 2hplus]`, `y2..y6 ∈ [1,1]` (the lift ignores the last five
coordinates).  Fully elementary route, no certificates: split at the
`h0cut` breakpoint `2·h0 = 2.52` —
* m = 1 arm (`y1 ≤ 2·h0`): the weight is 1, `lfun` is linear
  (`lfun(y1/2) = (2h0−y1)/(2(h0−1))`, PA2:466), and after collecting terms
  the bound is affine in `y1` with positive slope and value `≈ 0.0091` at
  `y1 = 2` — one chord bound for the cubic `(8−y²)y/24` (exact identity
  `g(y) = 1/3 − (y−2)(y²+2y−4)/24` with `y²+2y−4 ≤ 7.3904` on the box) plus
  rational two-sided enclosures of `mm1`/`mm2`.
* m = 0 arm (`2·h0 < y1 ≤ 2·hplus`): the weight dies and the kernel is
  exactly the B V2 factorization `(√8−y1)·[(√8+y1)y1/24 − 4mm1/(π√8)]`
  (lemmatized below as `p21_av2_grk_factor`, the `hrw` of
  `bank_GRKIBMPBV2_proof`); both factors are bounded at their interval ends,
  product `≥ 0.1776·0.105 ≈ 0.0186 > 0.008`.

The numeric seed both arms consume is a sharpening of wave W1's
`p21_arccos_one_third_le` (247/200): the triple-angle identity
`cos 3w = 4cos³w − 3cos w` at `w = 1231/3000` (increasing on `[1/2,∞)`,
fed by the same sin-cubic half-angle bound) gives `arccos(1/3) ≤ 1.231`,
which through `sol0`/`tau0` yields the two-sided enclosure
`5023/5000 ≤ mm1 ≤ 507/500` (true value ≈ 1.0121) needed because the m = 1
arm cancels to within 2% of the target.  All numeric margins are exact
rational checks (`norm_num`), π bounds are Mathlib's `pi_gt_d6`/`pi_lt_d4`. -/

/-- Stepping stone for the A V2 slice: `arccos(1/3) ≤ 1231/1000` (true value
1.23096).  From `Real.sin_ge_sub_cube` at `w/2` with `w = 1231/3000`:
`cos w = 1 − 2sin²(w/2) ≤ 1 − 2(w/2 − w³/48)² =: c`, `cos w ≥ 1 − w²/2 ≥ 1/2`,
and `4x³ − 3x` is increasing on `[1/2, ∞)`, so by `Real.cos_three_mul`
`cos(3w) = 4cos³w − 3cos w ≤ 4c³ − 3c ≤ 1/3` (rational check); antitonicity
of `arccos` on `0 < 3w = 1231/1000 < π` finishes. -/
private theorem p21_arccos_one_third_le_1231 : Real.arccos (1 / 3 : ℝ) ≤ 1231 / 1000 := by
  have hw0 : (0 : ℝ) ≤ 1231 / 3000 / 2 := by norm_num
  have hsb := Real.sin_ge_sub_cube hw0
  have hpos : (0 : ℝ) < 1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6 := by norm_num
  have hsq : (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2
      ≤ (Real.sin (1231 / 3000 / 2)) ^ 2 := pow_le_pow_left₀ (by norm_num) hsb 2
  have hhalf := Real.sin_sq_eq_half_sub (x := 1231 / 3000 / 2)
  have hcw : Real.cos (1231 / 3000)
      = 1 - 2 * (Real.sin (1231 / 3000 / 2)) ^ 2 := by
    conv_lhs => rw [← show (2 : ℝ) * (1231 / 3000 / 2) = 1231 / 3000 from by norm_num]
    rw [hhalf]
    ring
  have hcwUB : Real.cos (1231 / 3000)
      ≤ 1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2 := by
    rw [hcw]
    linarith
  have hsinle : Real.sin (1231 / 3000 / 2) ≤ 1231 / 3000 / 2 := by
    have := Real.sin_lt (by norm_num : (0 : ℝ) < 1231 / 3000 / 2)
    linarith
  have hsinpos : (0 : ℝ) ≤ Real.sin (1231 / 3000 / 2) := by linarith
  have hsin2 : (Real.sin (1231 / 3000 / 2)) ^ 2 ≤ (1231 / 3000 / 2) ^ 2 :=
    pow_le_pow_left₀ hsinpos hsinle 2
  have hcwLB : (1 : ℝ) / 2 ≤ Real.cos (1231 / 3000) := by
    rw [hcw]
    have h2 : (1231 / 3000 / 2) ^ 2 ≤ (41 : ℝ) / 100 := by norm_num
    linarith
  have hf : ∀ x y : ℝ, (1 : ℝ) / 2 ≤ x → x ≤ y → 4 * x ^ 3 - 3 * x ≤ 4 * y ^ 3 - 3 * y := by
    intro x y hx hxy
    have hd : 4 * y ^ 3 - 3 * y - (4 * x ^ 3 - 3 * x)
        = (y - x) * (4 * (x * x + y * x + y * y) - 3) := by ring
    have hp1 : (0 : ℝ) ≤ y - x := by linarith
    have hp2 : (0 : ℝ) ≤ 4 * (x * x + y * x + y * y) - 3 := by
      nlinarith [hx, hx, hxy]
    have hprod : (0 : ℝ) ≤ (y - x) * (4 * (x * x + y * x + y * y) - 3) :=
      mul_nonneg hp1 hp2
    linarith [hd, hprod]
  have hmono : 4 * (Real.cos (1231 / 3000)) ^ 3 - 3 * Real.cos (1231 / 3000)
      ≤ 4 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) ^ 3
        - 3 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) :=
    hf _ _ hcwLB hcwUB
  have hfin : 4 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) ^ 3
      - 3 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) ≤ (1 : ℝ) / 3 := by
    norm_num
  have hcos3 : Real.cos (3 * (1231 / 3000))
      = 4 * (Real.cos (1231 / 3000)) ^ 3 - 3 * Real.cos (1231 / 3000) :=
    Real.cos_three_mul _
  have hcosT : Real.cos (1231 / 1000) ≤ (1 : ℝ) / 3 := by
    rw [show (1231 : ℝ) / 1000 = 3 * (1231 / 3000) from by norm_num, hcos3]
    exact le_trans hmono hfin
  have hstep : Real.arccos (1 / 3) ≤ Real.arccos (Real.cos (1231 / 1000)) :=
    Real.arccos_le_arccos hcosT
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_d2])] at hstep
  exact hstep

/-- Second stepping stone: `arcsin(1/3) ≤ 17/50`.  From `Real.sin_ge_sub_cube`
at `17/50` (`sin(0.34) ≥ 0.34 − 0.34³/6 ≥ 1/3`, exact rational check) and
monotonicity of `arcsin` (`Real.arcsin_le_iff_le_sin`). -/
private theorem p21_av2_arcsin_le_17_50 : Real.arcsin (1 / 3 : ℝ) ≤ 17 / 50 := by
  have hmem : (1 : ℝ) / 3 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem2 : (17 / 50 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_d2]⟩
  have hsb := Real.sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 17 / 50)
  have hval : (1 : ℝ) / 3 ≤ 17 / 50 - (17 / 50) ^ 3 / 6 := by norm_num
  have hsin : (1 : ℝ) / 3 ≤ Real.sin (17 / 50) := by linarith
  exact (Real.arcsin_le_iff_le_sin hmem hmem2).mpr hsin

/-! ### sol0 / tau0 enclosures (both arms' numeric seed)

`sol0 = 3·arccos(1/3) − π ∈ [0.550796, 0.551408]`,
`tau0 = 4π − 20·sol0 ∈ [1.538208, 1.55048]` (true values 0.5507963 / 1.540658);
lower bound via `arccos_eq_pi_div_two_sub_arcsin` + `arcsin ≤ 17/50`,
upper via `arccos ≤ 1231/1000`, with `π ∈ (3.141592, 3.1416)`
(`Real.pi_gt_d6` / `Real.pi_lt_d4`). -/

private theorem p21_av2_sol0_le : sol0 ≤ 551408 / 1000000 := by
  have h0 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  linarith [h0, p21_arccos_one_third_le_1231, Real.pi_gt_d6]

private theorem p21_av2_sol0_ge : 550796 / 1000000 ≤ sol0 := by
  have h0 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  rw [h0, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [p21_av2_arcsin_le_17_50, Real.pi_gt_d6]

private theorem p21_av2_tau0_pos : (0 : ℝ) < tau0 := by
  have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
  linarith [h0, p21_av2_sol0_le, Real.pi_gt_d6]

private theorem p21_av2_tau0_ge : 1538208 / 1000000 ≤ tau0 := by
  have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
  linarith [h0, p21_av2_sol0_le, Real.pi_gt_d6]

private theorem p21_av2_tau0_le : tau0 ≤ 155048 / 100000 := by
  have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
  linarith [h0, p21_av2_sol0_ge, Real.pi_lt_d4]

/-! ### the mm1 two-sided enclosure

`mm1 = sol0·√8/tau0 ∈ [5023/5000, 507/500]` (true value ≈ 1.01203): the m = 1
arm's near-cancellation (kernel ≈ 0.0207 against target 0.008 at `y1 = 2`)
needs mm1 to ~0.2% accuracy, unattainable from wave W1's `mm1 < 4/3`.
Cross-multiplications `sol0·√8 ≤ (507/500)·tau0` resp.
`(5023/5000)·tau0 ≤ sol0·√8` close with margins ≈ 1.2e-4 / 2.6e-4. -/

private theorem p21_av2_mm1_le : mm1 ≤ 507 / 500 := by
  have hs8u : Real.sqrt 8 ≤ 282843 / 100000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hn1 : sol0 * Real.sqrt 8
      ≤ (551408 : ℝ) / 1000000 * (282843 / 100000) :=
    mul_le_mul p21_av2_sol0_le hs8u (by norm_num) (by positivity)
  have hmm1 : mm1 = sol0 * Real.sqrt 8 / tau0 := rfl
  rw [hmm1]
  exact (div_le_iff₀ p21_av2_tau0_pos).mpr (by linarith [p21_av2_tau0_ge])

private theorem p21_av2_mm1_ge : 5023 / 5000 ≤ mm1 := by
  have hs8lo : (7071 : ℝ) / 2500 < Real.sqrt 8 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hn1 : (550796 : ℝ) / 1000000 * (7071 / 2500) ≤ sol0 * Real.sqrt 8 :=
    mul_le_mul p21_av2_sol0_ge hs8lo.le (by norm_num) (by linarith [p21_av2_sol0_ge])
  have hmm1 : mm1 = sol0 * Real.sqrt 8 / tau0 := rfl
  rw [hmm1]
  exact (le_div_iff₀ p21_av2_tau0_pos).mpr (by linarith [p21_av2_tau0_le])

/-- The B V2 kernel identity, lemmatized (the `hrw` step inside
`bank_GRKIBMPBV2_proof`, proved the same way: multiply by the positive
`24·π·√8`, `ring`). -/
private theorem p21_av2_grk_factor (y1 : ℝ) : (8 - y1 * y1) * y1 / 24
      - 2 * (2 * mm1 / Real.pi) * (1 - y1 / Real.sqrt 8)
    = (Real.sqrt 8 - y1)
      * ((Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)) := by
  have hsq8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hquad : (Real.sqrt 8 - y1) * (Real.sqrt 8 + y1) = 8 - y1 * y1 := by
    calc (Real.sqrt 8 - y1) * (Real.sqrt 8 + y1)
        = Real.sqrt 8 * Real.sqrt 8 - y1 * y1 := by ring
      _ = 8 - y1 * y1 := by rw [hsq8]
  have hden : (24 : ℝ) * (Real.pi * Real.sqrt 8) ≠ 0 := by positivity
  refine mul_right_cancel₀ hden ?_
  have e1 : ((8 - y1 * y1) * y1 / 24
        - 2 * (2 * mm1 / Real.pi) * (1 - y1 / Real.sqrt 8))
      * ((24 : ℝ) * (Real.pi * Real.sqrt 8))
      = (8 - y1 * y1) * y1 * (Real.pi * Real.sqrt 8)
        - 96 * mm1 * (Real.sqrt 8 - y1) := by
    field_simp
    ring
  have e2 : ((Real.sqrt 8 - y1)
        * ((Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)))
      * ((24 : ℝ) * (Real.pi * Real.sqrt 8))
      = (Real.sqrt 8 - y1) * (Real.sqrt 8 + y1) * y1 * (Real.pi * Real.sqrt 8)
        - 96 * mm1 * (Real.sqrt 8 - y1) := by
    field_simp
    ring
  rw [hquad] at e2
  rw [e1, e2]

/-- The m = 1 arm of `bank_GRKIBMPAV2` (`h0cut y1 = 1`, `y1 ∈ [2, 2·h0]`).
The `lfun` weight is the exact linear function `lfun(y1/2) = (2h0−y1)/(2(h0−1))`
(PA2:466), so after the `hexp` collection the goal is a cubic plus three
linear pieces in `y1`.  Bounds (all exact-rational, π ∈ (3.141592, 3.1416),
√8 ∈ (2.8284, 2.8285)): the cubic chord `g(y1) ≥ 1/3 − (y1−2)·(7.3904/24)`;
`−4mm1/π ≥ −1.2917` and `4mm1/(π√8)·y1 ≥ 0.45215·y1` (two-sided mm1);
`8mm2/(π·2(h0−1)) ≥ 0.1214` (mm2 = (6sol0−π)√2/(6tau0) ≥ 0.0248).  The
resulting affine under-estimate has positive slope 0.0228 and value
`≈ 0.0091 > 0.008` at `y1 = 2` — `linarith` closes. -/
private theorem p21_av2_arm1 (y1 : ℝ) (hy2 : 2 ≤ y1) (hle : y1 ≤ 2 * h0)
    (hM : mm1 ≤ 507 / 500) (hmlow : 5023 / 5000 ≤ mm1) :
    (0.008 : ℝ) < gamma2_x_div_azim_v2 1 (y1 * y1) := by
  have hpi1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi2 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hy0 : (0 : ℝ) ≤ y1 := by linarith
  have hsqrt1 : Real.sqrt (y1 * y1) = y1 := Real.sqrt_mul_self hy0
  have h252 : (2 : ℝ) * h0 = 2.52 := by norm_num [h0]
  have h26 : (2 : ℝ) * (h0 - 1) = 0.52 := by norm_num [h0]
  have h252le : y1 ≤ 2.52 := by linarith
  have hlf2 : lfun (y1 / 2) = (2 * h0 - y1) / (2 * (h0 - 1)) := by
    show (h0 - y1 / 2) / (h0 - 1) = (2 * h0 - y1) / (2 * (h0 - 1))
    have hd : (h0 : ℝ) - 1 ≠ 0 := by norm_num [h0]
    refine div_eq_div_iff hd (by positivity) |>.mpr ?_
    ring
  have hexp : gamma2_x_div_azim_v2 1 (y1 * y1)
      = (8 - y1 * y1) * y1 / 24 - 4 * mm1 / Real.pi
        + 4 * mm1 / (Real.pi * Real.sqrt 8) * y1
        + 8 * mm2 / (Real.pi * (2 * (h0 - 1))) * (2 * h0 - y1) := by
    have h1 : gamma2_x_div_azim_v2 1 (y1 * y1)
        = (8 - y1 * y1) * Real.sqrt (y1 * y1) / 24
          - (2 * (2 * mm1 / Real.pi) * (1 - Real.sqrt (y1 * y1) / Real.sqrt 8)
            - (8 * mm2 / Real.pi) * 1 * lfun (Real.sqrt (y1 * y1) / 2)) := rfl
    rw [h1, hsqrt1, mul_one, hlf2]
    field_simp
    ring
  rw [hexp]
  -- g-chord: (8 − y²)y/24 is exactly 1/3 − (y−2)(y²+2y−4)/24, and y²+2y−4 ≤ 7.3904
  have h1 : y1 * y1 ≤ 2.52 * y1 := by nlinarith [h252le, hy0]
  have h2 : y1 * y1 + 2 * y1 - 4 ≤ 73904 / 10000 := by linarith
  have hg : (8 - y1 * y1) * y1 / 24
      ≥ (1 : ℝ) / 3 - (y1 - 2) * ((73904 : ℝ) / 10000 / 24) := by
    have hid : (8 - y1 * y1) * y1 / 24
        = (1 : ℝ) / 3 - (y1 - 2) * ((y1 * y1 + 2 * y1 - 4) / 24) := by ring
    have h3 : (y1 * y1 + 2 * y1 - 4) / 24 ≤ (73904 : ℝ) / 10000 / 24 := by
      have he : (y1 * y1 + 2 * y1 - 4) / 24 = (y1 * y1 + 2 * y1 - 4) * (1 / 24) := by ring
      have he2 : ((73904 : ℝ) / 10000) / 24 = (73904 : ℝ) / 10000 * (1 / 24) := by ring
      rw [he, he2]
      exact mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 24)
    have hpos : (0 : ℝ) ≤ y1 - 2 := by linarith
    have h3' : (y1 - 2) * ((y1 * y1 + 2 * y1 - 4) / 24)
        ≤ (y1 - 2) * ((73904 : ℝ) / 10000 / 24) :=
      mul_le_mul_of_nonneg_left h3 hpos
    rw [hid]
    linarith
  -- mm1 upper: 4·mm1/π ≤ 1.2917
  have hpN : 4 * mm1 / Real.pi ≤ 12917 / 10000 := by
    have h5 : (4 : ℝ) * (507 / 500) ≤ (12917 : ℝ) / 10000 * Real.pi := by
      linarith
    exact (div_le_iff₀ (by positivity)).mpr (by linarith [hM, h5])
  -- mm1 lower: 4·mm1/(π·√8) ≥ 0.45215
  have hpP : (45215 : ℝ) / 100000 ≤ 4 * mm1 / (Real.pi * Real.sqrt 8) := by
    have hs8u : Real.sqrt 8 ≤ 28285 / 10000 :=
      (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    have hU : Real.pi * Real.sqrt 8 ≤ 3.1416 * (28285 / 10000) :=
      mul_le_mul hpi2.le hs8u (by norm_num) (by positivity)
    have hq1 : (45215 : ℝ) / 100000 * (3.1416 * (28285 / 10000))
        ≤ (4 : ℝ) * (5023 / 5000) := by norm_num
    exact (le_div_iff₀ (by positivity)).mpr (by linarith [hU, hq1, hmlow])
  -- mm2 lower: 8·mm2/(π·2(h0−1)) ≥ 0.1214
  have hq2 : (1214 : ℝ) / 10000 ≤ 8 * mm2 / (Real.pi * (2 * (h0 - 1))) := by
    have hsq2 : (1.4142 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    have hsol6 : (163176 : ℝ) / 1000000 ≤ 6 * sol0 - Real.pi := by
      linarith [p21_av2_sol0_ge, hpi2]
    have hprod : (163176 : ℝ) / 1000000 * 1.4142
        ≤ (6 * sol0 - Real.pi) * Real.sqrt 2 :=
      mul_le_mul hsol6 hsq2.le (by norm_num) (by linarith)
    have h0 : mm2 = (6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0) := rfl
    rw [h26]
    have hA : (1214 : ℝ) / 10000 * (Real.pi * 0.52) ≤ 1984 / 10000 := by
      linarith
    have hB : (1984 : ℝ) / 10000 ≤ 8 * mm2 := by
      have hden : (0 : ℝ) < 6 * tau0 := by linarith [p21_av2_tau0_pos]
      have hcore : (31 : ℝ) / 1250 * (6 * tau0)
          ≤ (6 * sol0 - Real.pi) * Real.sqrt 2 := by
        linarith [hprod, p21_av2_tau0_le]
      have h1 : (31 : ℝ) / 1250
          ≤ (6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0) :=
        (le_div_iff₀ hden).mpr hcore
      linarith [h1]
    have hden2 : (0 : ℝ) < Real.pi * 0.52 := by positivity
    have hT : (1214 : ℝ) / 10000 * (Real.pi * 0.52) ≤ 8 * mm2 := by
      linarith [hB, hpi2]
    exact (le_div_iff₀ hden2).mpr hT
  -- assemble: the bound is affine in y1 with value > 0.008 at y1 = 2
  have hpN' : -(4 * mm1 / Real.pi) ≥ -(12917 : ℝ) / 10000 := by linarith
  have hpP' : (45215 : ℝ) / 100000 * y1 ≤ 4 * mm1 / (Real.pi * Real.sqrt 8) * y1 :=
    mul_le_mul_of_nonneg_right hpP hy0
  have hqpos : (0 : ℝ) ≤ 2 * h0 - y1 := by linarith
  have hq' : (1214 : ℝ) / 10000 * (2 * h0 - y1)
      ≤ 8 * mm2 / (Real.pi * (2 * (h0 - 1))) * (2 * h0 - y1) :=
    mul_le_mul_of_nonneg_right hq2 hqpos
  linarith [hg, hpN', hpP', hq', hy2, h252, h252le]

/-- The m = 0 arm of `bank_GRKIBMPAV2` (`h0cut y1 = 0`, `2·h0 < y1 ≤ 2·hplus`):
the weight dies, and the kernel is the B V2 factorization
`(√8−y1)·[(√8+y1)y1/24 − 4mm1/(π√8)]` (via `p21_av2_grk_factor`).  On the
interval: `√8−y1 ≥ 2.8284−2.6508 = 0.1776`, the bracket `≥ 0.561582−0.4565 =
0.105082 ≥ 0.105` (bracket numerator minimized at `y1 = 2h0`, `4mm1/(π√8) ≤
0.4565` from `mm1 ≤ 507/500`), so the product `≥ 0.0186 > 0.008`. -/
private theorem p21_av2_arm0 (y1 : ℝ) (hgt : 2 * h0 < y1) (hhp : y1 ≤ 2 * hplus)
    (hM : mm1 ≤ 507 / 500) :
    (0.008 : ℝ) < gamma2_x_div_azim_v2 0 (y1 * y1) := by
  have hpi1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h26508 : (2 : ℝ) * hplus = 2.6508 := by norm_num [hplus]
  have h252 : (2 : ℝ) * h0 = 2.52 := by norm_num [h0]
  have hy0 : (0 : ℝ) ≤ y1 := by linarith
  have hsqrt1 : Real.sqrt (y1 * y1) = y1 := Real.sqrt_mul_self hy0
  have hgt2 : (2.52 : ℝ) < y1 := by linarith
  have hle : y1 ≤ 2.6508 := by linarith
  have hs8lo : (2.8284 : ℝ) < Real.sqrt 8 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hexp0 : gamma2_x_div_azim_v2 0 (y1 * y1)
      = (Real.sqrt 8 - y1)
        * ((Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)) := by
    have h1 : gamma2_x_div_azim_v2 0 (y1 * y1)
        = (8 - y1 * y1) * Real.sqrt (y1 * y1) / 24
          - (2 * (2 * mm1 / Real.pi) * (1 - Real.sqrt (y1 * y1) / Real.sqrt 8)
            - (8 * mm2 / Real.pi) * 0 * lfun (Real.sqrt (y1 * y1) / 2)) := rfl
    rw [h1, hsqrt1, mul_zero, zero_mul, sub_zero]
    exact p21_av2_grk_factor y1
  rw [hexp0]
  have e2 : (0.1776 : ℝ) ≤ Real.sqrt 8 - y1 := by linarith
  have hA : (2.8284 : ℝ) + 2.52 ≤ Real.sqrt 8 + y1 := by linarith
  have hB1 : ((2.8284 : ℝ) + 2.52) * 2.52 ≤ (Real.sqrt 8 + y1) * y1 :=
    mul_le_mul hA hgt2.le (by norm_num) (by linarith)
  have hB2 : 4 * mm1 / (Real.pi * Real.sqrt 8) ≤ 4565 / 10000 := by
    refine (div_le_iff₀ (by positivity)).mpr ?_
    have hpL : (4 : ℝ) * (507 / 500)
        ≤ (4565 : ℝ) / 10000 * (3.141592 * 2.8284) := by norm_num
    have hpU : 3.141592 * 2.8284 ≤ Real.pi * Real.sqrt 8 :=
      mul_le_mul hpi1.le hs8lo.le (by norm_num) (by positivity)
    linarith [hpL, hpU, hM]
  have e4 : (0.105 : ℝ)
      ≤ (Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8) := by
    linarith [hB1, hB2]
  have hmul : (0.1776 : ℝ) * 0.105
      ≤ (Real.sqrt 8 - y1)
        * ((Real.sqrt 8 + y1) * y1 / 24 - 4 * mm1 / (Real.pi * Real.sqrt 8)) :=
    mul_le_mul e2 e4 (by linarith) (by linarith [e2])
  linarith

/-- The sharp-edge group's A V2 bank entry (HOL `GRKIBMP A V2`,
ineq.hl:1520-1535, doc "gamma2 at least 0.008 per azim along critical edge"),
PROVED by hand — fully analytic, no certificate data.  Proof: the `y2..y6 ∈
[1,1]` box closes inside `gamma2x1DivAV2` via the rfl bridge
`p21_nonf_gamma2x1DivAV2_yOfX`; then `lt_trichotomy` on `y1` against the
`h0cut` breakpoint `2·h0`: at or below it the weight is `1` and the linear
`lfun` term carries the left part of the box (`p21_av2_arm1`, affine bound
`≈ 0.0091` at `y1 = 2`); above it the weight dies and the B V2 factored
kernel gives `≥ 0.0186` (`p21_av2_arm0`).  Numeric seed: the triple-angle
`arccos(1/3) ≤ 1231/1000` and the two-sided `mm1 ∈ [1.0046, 1.014]` (doc of
`p21_av2_mm1_le`).  Assembles with `bank_GRKIBMPBV2_proof` into
`grk_bank` (Assembly `nliGrkBank := ⟨bank_GRKIBMPAV2_proof,
bank_GRKIBMPBV2_proof⟩`). -/
theorem bank_GRKIBMPAV2_proof : bank_GRKIBMPAV2 := by
  intro y1 y2 y3 y4 y5 y6 hy2 hhp _ _ _ _ _ _ _ _ _ _
  have hM := p21_av2_mm1_le
  have hmlow := p21_av2_mm1_ge
  rw [show yOfX (gamma2x1DivAV2 (h0cut y1)) y1 y2 y3 y4 y5 y6
      = gamma2_x_div_azim_v2 (h0cut y1) (y1 * y1) from rfl]
  rcases lt_trichotomy y1 (2 * h0) with hlt | heq | hgt
  · rw [p21_h0cutA y1 (le_of_lt hlt)]
    exact p21_av2_arm1 y1 hy2 (le_of_lt hlt) hM hmlow
  · rw [p21_h0cutA y1 (le_of_eq heq)]
    exact p21_av2_arm1 y1 hy2 (le_of_eq heq) hM hmlow
  · rw [p21_h0cutB y1 hgt]
    exact p21_av2_arm0 y1 hgt hhp hM
/-! ## MERGE-INEQ wave 2a: the cell3 kit (docs/merge-ineq-channel.md §4.2-3)

The thirteen 2a kit items for `cell3_from_ineq_thm` (wave 2b), each with its
HOL anchor (all in `text_formalization/nonlinear/merge_ineq.hl` or its
dependencies).  Per charter §6.2 the HOL `ineq` box wrapper is not ported:
statements are the arrow/implication form throughout.  Registration of the
two def-level items:

- **Item 1** `gamma3f_x_div_sqrtdelta`: already carried by the tree at
  `IneqClosureDefs.lean:441` (`gamma3fXDivSqrtdelta`, verbatim operator
  composition against the batch-2 kit) — reused, no local def.
- **Item 2** `eulerA_x`: already materialized above (:162 `eulerAX`) —
  skipped.

The `mi_` prefix (Merge_ineq kit) is collision-free tree-wide.  -/

/-! ### Item 13: the Flyspeck-constants numeric seeds (norm_num-affine) -/

/-- Numeric seed: `1.414213 < sqrt 2` (Flyspeck_constants.bounds slice;
the PA19:357 pattern). -/
private theorem mi_sqrt2_lb : (1.414213 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- Numeric seed: `sqrt 2 < 1.414214`. -/
private theorem mi_sqrt2_ub : Real.sqrt 2 < 1.414214 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- `sqrt 8 = 2 * sqrt 2` (HOL `Nonlinear_lemma.sqrt8_sqrt2`,
nonlinear_lemma.hl:182). -/
theorem mi_sqrt8_eq : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 from by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- Numeric seed: `2.8 < sqrt 8`. -/
private theorem mi_sqrt8_lb : (2.8 : ℝ) < Real.sqrt 8 := by
  rw [mi_sqrt8_eq]; linarith [mi_sqrt2_lb]

/-! ### Item 3: eta_y_nn -/

/-- HOL `eta_y_nn` (merge_ineq.hl:3452-3462): nonnegativity of `eta_y`
(`sqrt` is nonnegative; the hypothesis keeps the HOL shape). -/
theorem mi_eta_y_nn (y4 y5 y6 : ℝ) (_h : 0 ≤ upsX (y4 * y4) (y5 * y5) (y6 * y6)) :
    0 ≤ eta_y y4 y5 y6 := Real.sqrt_nonneg _

/-- eta_y swap symmetries (the `Collect_geom.ETA_Y_SYYM` slice used by
`ETA_Y_LE_IMP_LT_ALL`/`gamma3f_sym`; `ups_x` is a symmetric polynomial). -/
theorem mi_eta_y_sym (y1 y2 y3 : ℝ) :
    eta_y y1 y2 y3 = eta_y y2 y1 y3 ∧ eta_y y1 y2 y3 = eta_y y1 y3 y2 := by
  constructor
  · show etaX (y1 * y1) (y2 * y2) (y3 * y3) = etaX (y2 * y2) (y1 * y1) (y3 * y3)
    simp only [etaX, upsX]; congr 1; ring
  · show etaX (y1 * y1) (y2 * y2) (y3 * y3) = etaX (y1 * y1) (y3 * y3) (y2 * y2)
    simp only [etaX, upsX]; congr 1; ring

/-! ### Item 4: UPS_X_POS -/

/-- HOL `TRI_UPS_X_STRICT_POS` (YSSKQOY.hl:340-346).  PackingAuto18 hosts
the chapter copy but sits outside this file's import closure, so the short
Heron-factorization proof is mirrored here (PackingAuto18.lean:478-505). -/
private theorem mi_sqUpsX (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c)
      = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  simp only [upsX]; ring

/-- HOL `TRI_UPS_X_STRICT_POS` (YSSKQOY.hl:340-346). -/
private theorem mi_TRI_UPS_X_STRICT_POS (a b c : ℝ) (ha : 0 < a) (_hb : 0 < b) (_hc : 0 ≤ c)
    (h1 : c < a + b) (h2 : a < b + c) (h3 : b < c + a) :
    0 < upsX (a * a) (b * b) (c * c) := by
  rw [mi_sqUpsX]
  refine mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)

/-- HOL `UPS_X_POS` (merge_ineq.hl:2917-2928). -/
theorem mi_UPS_X_POS (y1 y2 y3 : ℝ) (h1 : 2 ≤ y1) (h1' : y1 < 4) (h2 : 2 ≤ y2)
    (h2' : y2 < 4) (h3 : 2 ≤ y3) (h3' : y3 < 4) :
    0 < upsX (y1 * y1) (y2 * y2) (y3 * y3) :=
  mi_TRI_UPS_X_STRICT_POS y1 y2 y3 (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

/-! ### Item 5: cell_3_delta_x_eta_x -/

/-- `sqrt t < sqrt 2 ↔ t < 2` for `0 ≤ t` (workhorse for items 5/6/7). -/
private theorem mi_sqrt_lt_sqrt2 {t : ℝ} (_ht : 0 ≤ t) :
    Real.sqrt t < Real.sqrt 2 ↔ t < 2 := by
  rw [Real.sqrt_lt' (Real.sqrt_pos.mpr (by norm_num)),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- HOL `cell_3_delta_x_eta_x` (merge_ineq.hl:2873-2886): at the
`(2,2,2)`-pinned Cayley determinant, positivity is equivalent to
`eta_x < sqrt 2` (via `delta_x 2 2 2 x4 x5 x6 = 2*ups_x - x4*x5*x6`). -/
theorem mi_cell_3_delta_x_eta_x (x4 x5 x6 : ℝ) (h4 : 0 < x4) (h5 : 0 < x5) (h6 : 0 < x6)
    (hu : 0 < upsX x4 x5 x6) :
    (0 < deltaX 2 2 2 x4 x5 x6 ↔ etaX x4 x5 x6 < Real.sqrt 2) := by
  have hD : deltaX 2 2 2 x4 x5 x6 = 2 * upsX x4 x5 x6 - x4 * x5 * x6 := by
    simp only [deltaX, upsX]; ring
  have hprod : 0 < x4 * x5 * x6 := by positivity
  have ht : 0 ≤ x4 * x5 * x6 / upsX x4 x5 x6 := div_nonneg (le_of_lt hprod) (le_of_lt hu)
  constructor
  · intro hd
    rw [hD] at hd
    show Real.sqrt (x4 * x5 * x6 / upsX x4 x5 x6) < Real.sqrt 2
    rw [mi_sqrt_lt_sqrt2 ht, div_lt_iff₀ hu]
    linarith
  · intro he
    rw [hD]
    have he' : Real.sqrt (x4 * x5 * x6 / upsX x4 x5 x6) < Real.sqrt 2 := he
    have ht2 : x4 * x5 * x6 / upsX x4 x5 x6 < 2 := (mi_sqrt_lt_sqrt2 ht).mp he'
    rw [div_lt_iff₀ hu] at ht2
    linarith

/-- Core of `ETA_Y_BOUNDS`/`ETA_Y_LE_IMP_LT` (merge_ineq.hl:3179-3253):
under the `2 ≤ y < 4` box, `eta_y < sqrt 2` forces the `(2,2,2)`-pinned
Cayley determinant positive (UPS_X_POS + cell_3_delta_x_eta_x). -/
theorem mi_etaY_lt_sqrt2_delta (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h4' : y4 < 4)
    (h5 : 2 ≤ y5) (h5' : y5 < 4) (h6 : 2 ≤ y6) (h6' : y6 < 4)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    0 < deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
  have hcu := mi_UPS_X_POS y4 y5 y6 h4 h4' h5 h5' h6 h6'
  have key := mi_cell_3_delta_x_eta_x (y4 * y4) (y5 * y5) (y6 * y6)
    (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
    (mul_pos (by linarith) (by linarith)) hcu
  exact key.mpr het

/-! ### Item 6: ETA_Y_BOUNDS -/

/-- HOL `ETA_Y_BOUNDS` (merge_ineq.hl:3223-3253). -/
theorem mi_ETA_Y_BOUNDS (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ Real.sqrt 8) (h6 : 2 ≤ y6) (h6' : y6 ≤ Real.sqrt 8)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    0 < upsX (y4 * y4) (y5 * y5) (y6 * y6) ∧
      0 < deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
  have h84 : Real.sqrt 8 < 4 := by rw [mi_sqrt8_eq]; linarith [mi_sqrt2_ub]
  have hlt4 : y4 < 4 := by linarith
  have hlt5 : y5 < 4 := by linarith
  have hlt6 : y6 < 4 := by linarith
  exact ⟨mi_UPS_X_POS y4 y5 y6 h4 hlt4 h5 hlt5 h6 hlt6,
    mi_etaY_lt_sqrt2_delta y4 y5 y6 h4 hlt4 h5 hlt5 h6 hlt6 het⟩

/-! ### Item 7: ETA_Y_LE_IMP_LT_ALL -/

/-- HOL `ETA_Y_LE_IMP_LT` (merge_ineq.hl:3179-3200), the single-slot base:
a maximizer at `sqrt 8` would make the `(2,2,2)`-determinant equal
`-2*(y5²+y6²-8)² ≤ 0`. -/
private theorem mi_ETA_Y_LE_IMP_LT (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ Real.sqrt 8) (h6 : 2 ≤ y6) (h6' : y6 ≤ Real.sqrt 8)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) : y4 < Real.sqrt 8 := by
  have h84 : Real.sqrt 8 < 4 := by rw [mi_sqrt8_eq]; linarith [mi_sqrt2_ub]
  have hlt4 : y4 < 4 := by linarith
  have hlt5 : y5 < 4 := by linarith
  have hlt6 : y6 < 4 := by linarith
  by_contra hcon
  have h8 : y4 = Real.sqrt 8 := le_antisymm h4' (le_of_not_gt hcon)
  have hsq : y4 * y4 = 8 := by rw [h8]; exact Real.mul_self_sqrt (by norm_num)
  have hd := mi_etaY_lt_sqrt2_delta y4 y5 y6 h4 hlt4 h5 hlt5 h6 hlt6 het
  rw [hsq] at hd
  have hid : deltaX 2 2 2 8 (y5 * y5) (y6 * y6) = -2 * (y5 * y5 + y6 * y6 - 8) ^ 2 := by
    simp only [deltaX]; ring
  rw [hid] at hd
  linarith [sq_nonneg (y5 * y5 + y6 * y6 - 8)]

/-- HOL `ETA_Y_LE_IMP_LT_ALL` (merge_ineq.hl:3214-3222): all three slots,
via `eta_y` swap symmetry. -/
theorem mi_ETA_Y_LE_IMP_LT_ALL (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ Real.sqrt 8) (h6 : 2 ≤ y6) (h6' : y6 ≤ Real.sqrt 8)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    y4 < Real.sqrt 8 ∧ y5 < Real.sqrt 8 ∧ y6 < Real.sqrt 8 := by
  have h54 : eta_y y5 y4 y6 < Real.sqrt 2 := by
    have he : eta_y y4 y5 y6 = eta_y y5 y4 y6 := (mi_eta_y_sym y4 y5 y6).1
    rw [← he]; exact het
  have h64 : eta_y y6 y5 y4 < Real.sqrt 2 := by
    have he : eta_y y4 y5 y6 = eta_y y6 y5 y4 := by
      rw [(mi_eta_y_sym y4 y5 y6).2, (mi_eta_y_sym y4 y6 y5).1,
        (mi_eta_y_sym y6 y4 y5).2]
    rw [← he]; exact het
  exact ⟨mi_ETA_Y_LE_IMP_LT y4 y5 y6 h4 h4' h5 h5' h6 h6' het,
    mi_ETA_Y_LE_IMP_LT y5 y4 y6 h5 h5' h4 h4' h6 h6' h54,
    mi_ETA_Y_LE_IMP_LT y6 y5 y4 h6 h6' h5 h5' h4 h4' h64⟩

/-! ### Item 12a: lmfun_h0cut -/

/-- HOL `lmfun_h0cut` (merge_ineq.hl:2889-2896): `lmfun` is `lfun` cut off
by the `h0cut` weight. -/
theorem mi_lmfun_h0cut (y : ℝ) : lmfun (y / 2) = lfun (y / 2) * h0cut y := by
  unfold lmfun lfun h0cut
  by_cases hy : y ≤ 2 * h0
  · rw [if_pos hy, if_pos (by linarith : y / 2 ≤ h0)]; ring
  · rw [if_neg hy, if_neg (by linarith : ¬ (y / 2 ≤ h0))]; ring

/-! ### Item 13 (cont.): the hminus cluster

`mi_hminus_exists` is the one non-mechanical 2a point (charter §6.1): the
IVT sign change of `marchal_quartic - lfun` over `[1.2, 1.26]` (HOL
`hminus_exists`, nonlinear_lemma.hl:846-880, `REAL_IVT_INCREASING`), then
epsilon spec (:882-890) and the `marchal_quartic > 0` on `[1, hplus)`
argument (:902-935) give `hminus < h0` (:937-951). -/

private theorem mi_marchalQuartic_sub_lfun_cont :
    ContinuousOn (fun h : ℝ => marchalQuartic h - lfun h) (Set.Icc 1.2 1.26) := by
  have hC : (Real.sqrt 2 - 1) * 5 * (hplus - 1) ≠ 0 := by
    rw [show hplus = 1.3254 from rfl]
    exact ne_of_gt (mul_pos (mul_pos (by linarith [mi_sqrt2_lb]) (by norm_num))
      (by norm_num))
  have hc1 : Continuous marchalQuartic := by
    unfold marchalQuartic
    refine Continuous.div ?_ continuous_const (fun _ => hC)
    refine Continuous.mul ?_ ?_
    · exact Continuous.mul (continuous_const.sub continuous_id)
        (continuous_id.sub continuous_const)
    · exact (by fun_prop :
        Continuous fun h : ℝ => (9 : ℝ) * h ^ 2 - 17 * h + 3)

  have hc2 : Continuous lfun := by
    unfold lfun
    exact Continuous.div (continuous_const.sub continuous_id) continuous_const
      (fun _ => by show (1.26 : ℝ) - 1 ≠ 0; norm_num)
  exact hc1.sub hc2 |>.continuousOn

private theorem mi_ivt_neg : marchalQuartic 1.2 - lfun 1.2 < 0 := by
  have hs1 : (1.414213 : ℝ) < Real.sqrt 2 := mi_sqrt2_lb
  have hs2 : Real.sqrt 2 < 1.414214 := mi_sqrt2_ub
  rw [sub_lt_zero]
  have hl : lfun 1.2 = 3 / 13 := by unfold lfun h0; norm_num
  rw [hl]
  show (Real.sqrt 2 - 1.2) * (1.2 - hplus) * (9 * 1.2 ^ 2 - 17 * 1.2 + 3)
      / ((Real.sqrt 2 - 1) * 5 * (hplus - 1)) < 3 / 13
  rw [show hplus = 1.3254 from rfl]
  rw [div_lt_iff₀ (mul_pos (mul_pos (by linarith [mi_sqrt2_lb]) (by norm_num))
    (by norm_num))]
  ring_nf
  linarith

private theorem mi_ivt_pos : 0 < marchalQuartic 1.26 - lfun 1.26 := by
  have hl : lfun 1.26 = 0 := by unfold lfun h0; norm_num
  rw [hl, sub_zero]
  show (0 : ℝ) < (Real.sqrt 2 - 1.26) * (1.26 - hplus) * (9 * 1.26 ^ 2 - 17 * 1.26 + 3)
      / ((Real.sqrt 2 - 1) * 5 * (hplus - 1))
  rw [show hplus = 1.3254 from rfl]
  have hB : (0 : ℝ) < (Real.sqrt 2 - 1) * 5 * (1.3254 - 1) :=
    mul_pos (mul_pos (by linarith [mi_sqrt2_lb]) (by norm_num)) (by norm_num)
  refine div_pos ?_ hB
  have e1 : (0 : ℝ) < Real.sqrt 2 - 1.26 := by linarith [mi_sqrt2_lb]
  have hbc : (0 : ℝ) < (1.26 - 1.3254) * (9 * 1.26 ^ 2 - 17 * 1.26 + 3) :=
    mul_pos_of_neg_of_neg (by norm_num) (by norm_num)
  rw [mul_assoc]
  exact mul_pos e1 hbc

/-- HOL `Nonlinear_lemma.hminus_exists` (nonlinear_lemma.hl:846-880):
the `marchal_quartic = lfun` crossing inside `[1.2, 1.26]`. -/
private theorem mi_hminus_exists :
    ∃ x, 1.2 ≤ x ∧ x < 1.3 ∧ marchalQuartic x = lmfun x := by
  have hcu : ContinuousOn (fun h : ℝ => marchalQuartic h - lfun h) (uIcc (1.2 : ℝ) 1.26) := by
    rw [Set.uIcc_of_le (by norm_num : (1.2 : ℝ) ≤ 1.26)]
    exact mi_marchalQuartic_sub_lfun_cont
  obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc hcu
    (Set.mem_uIcc_of_le (le_of_lt mi_ivt_neg) (le_of_lt mi_ivt_pos))
  have hxI : x ∈ Set.Icc (1.2 : ℝ) 1.26 := by
    rwa [Set.uIcc_of_le (by norm_num : (1.2 : ℝ) ≤ 1.26)] at hx
  have h12 : (1.2 : ℝ) ≤ x := hxI.1
  have h126 : x ≤ 1.26 := hxI.2
  have hx0 : x ≤ h0 := by show x ≤ 1.26; exact h126
  have hml : marchalQuartic x = lfun x := by
    have hfx' : marchalQuartic x - lfun x = 0 := hfx
    linarith [hfx']
  refine ⟨x, h12, by linarith, ?_⟩
  unfold lmfun
  rw [if_pos hx0]
  exact hml

/-- HOL `Nonlinear_lemma.hminus_prop` (nonlinear_lemma.hl:882-890):
the epsilon-selected `hminus` satisfies its defining predicate. -/
theorem mi_hminus_prop :
    1.2 ≤ hminus ∧ hminus < 1.3 ∧ marchalQuartic hminus = lmfun hminus :=
  Classical.epsilon_spec mi_hminus_exists

/-- HOL `Nonlinear_lemma.hminus_lt_h0` step (nonlinear_lemma.hl:902-935):
`marchal_quartic` is positive on `[1, hplus)`. -/
private theorem mi_marchalQuartic_pos (h : ℝ) (h1 : 1 ≤ h) (h2 : h < hplus) :
    0 < marchalQuartic h := by
  have h2' : h < 1.3254 := h2
  unfold marchalQuartic
  rw [show hplus = 1.3254 from rfl]
  refine div_pos ?_ (mul_pos (mul_pos (by linarith [mi_sqrt2_lb]) (by norm_num))
    (by norm_num))
  have hsh : (0 : ℝ) < Real.sqrt 2 - h := by linarith [mi_sqrt2_lb]
  have hq : (9 : ℝ) * h ^ 2 - 17 * h + 3 < 0 := by
    have hpos : (0 : ℝ) < h := by linarith
    have hsq : 9 * h ^ 2 < 9 * 1.3254 * h := by nlinarith [h2', hpos]
    linarith
  have hbc : (0 : ℝ) < (h - 1.3254) * (9 * h ^ 2 - 17 * h + 3) := by
    have e2 : (0 : ℝ) < -(h - 1.3254) := by linarith
    have e3 : (0 : ℝ) < -(9 * h ^ 2 - 17 * h + 3) := by linarith
    nlinarith
  rw [mul_assoc]
  exact mul_pos hsh hbc

/-- HOL `Nonlinear_lemma.hminus_lt_h0` (nonlinear_lemma.hl:937-951). -/
theorem mi_hminus_lt_h0 : hminus < h0 := by
  by_contra hcon
  obtain ⟨hm1, hm2, hm3⟩ := mi_hminus_prop
  have hge : h0 ≤ hminus := le_of_not_gt hcon
  have hl0 : lmfun hminus = 0 := by
    unfold lmfun
    split
    · have heq : hminus = h0 := le_antisymm ‹hminus ≤ h0› hge
      rw [heq, sub_self, zero_div]
    · rfl
  have hlt : hminus < hplus := by
    rw [show hplus = 1.3254 from rfl]; linarith [hm2]
  have hmq := mi_marchalQuartic_pos hminus (by linarith [hm1]) hlt
  rw [hl0] at hm3
  rw [hm3] at hmq
  exact lt_irrefl (0 : ℝ) hmq

/-- Numeric corollaries used by the cell3 tracks and `y_bounds`
(HOL: Flyspeck_constants.bounds + Nonlinear_lemma + REAL_ARITH). -/
theorem mi_two_hminus_le_two_h0 : 2 * hminus ≤ 2 * h0 := by
  linarith [mi_hminus_lt_h0]

theorem mi_two_le_two_hminus : 2 ≤ 2 * hminus := by
  linarith [mi_hminus_prop.1]

theorem mi_two_hminus_le_sqrt8 : 2 * hminus ≤ Real.sqrt 8 := by
  linarith [mi_hminus_prop.2.1, mi_sqrt8_lb]

theorem mi_two_hminus_le_two_sqrt2 : 2 * hminus ≤ 2 * Real.sqrt 2 := by
  rw [← mi_sqrt8_eq]; exact mi_two_hminus_le_sqrt8

theorem mi_two_hplus_le_two_sqrt2 : 2 * hplus ≤ 2 * Real.sqrt 2 := by
  have hhp : hplus = 1.3254 := rfl
  linarith [mi_sqrt8_eq, mi_sqrt8_lb, hhp]

theorem mi_201_le_two_h0 : (2.01 : ℝ) ≤ 2 * h0 := by norm_num [h0]

theorem mi_201_le_sqrt8 : (2.01 : ℝ) ≤ Real.sqrt 8 := by
  rw [mi_sqrt8_eq]; linarith [mi_sqrt2_lb]

/-! ### Item 12b: y_bounds -/

/-- HOL `y_bounds` (merge_ineq.hl:3809-3846): the eleven box-bridging
arithmetic implications. -/
theorem mi_y_bounds (y : ℝ) :
    (y ≤ 2 * hminus → y ≤ Real.sqrt 8) ∧
      (y ≤ Real.sqrt 8 → y ≤ 2 * Real.sqrt 2) ∧
      (y ≤ 2 * Real.sqrt 2 → y < 4) ∧
      (y < 2 * hminus → y ≤ 2 * hminus) ∧
      (y < 2 * hminus → y ≤ 2 * Real.sqrt 2) ∧
      (2 ≤ y → 0 < y) ∧
      (2 * hminus ≤ y → 2 ≤ y) ∧
      (2 ≤ y → 0 ≤ y) ∧
      (2 * hminus ≤ y → 0 ≤ y) ∧
      (y ≤ 2 * hminus → y ≤ 2 * h0) ∧
      (y ≤ 2 * hplus → y ≤ 2 * Real.sqrt 2) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => le_of_lt h, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => by linarith, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · linarith [mi_two_hminus_le_sqrt8]
  · rw [← mi_sqrt8_eq]; exact h
  · linarith [mi_sqrt2_ub]
  · linarith [mi_two_hminus_le_two_sqrt2]
  · linarith
  · linarith [mi_two_le_two_hminus]
  · linarith [mi_two_le_two_hminus]
  · linarith [mi_two_hminus_le_two_h0]
  · linarith [mi_two_hplus_le_two_sqrt2, mi_sqrt2_ub]

/-! ### Item 8: dih_y_div_sqrtdelta_pos -/

/-- Positivity of the posbranch body (service lemma for item 8; the HOL
route `dih_x_dih_x_div_sqrtdelta_posbranch` merge_ineq.hl:920 +
`dih_x_div_sqrtdelta_pos` :3158 is taken directly at the body here). -/
theorem mi_dihXDivSqrtdeltaPosbranch_nn (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hd4 : 0 < deltaX4 x1 x2 x3 x4 x5 x6) :
    0 ≤ dihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
  have ht : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 / deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 :=
    div_pos (by positivity) (by positivity)
  show 0 ≤ (Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6) *
    matan (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 / deltaX4 x1 x2 x3 x4 x5 x6 ^ 2)
  refine mul_nonneg (div_nonneg (Real.sqrt_nonneg (4 * x1)) (le_of_lt hd4)) ?_
  rw [matan, if_neg (ne_of_gt ht), if_pos ht]
  exact le_of_lt (div_pos (Real.arctan_pos.mpr (Real.sqrt_pos.mpr ht))
    (Real.sqrt_pos.mpr ht))

/-- HOL `delta_x4_pos` (merge_ineq.hl:2996-3009, via `delta_x4_2` :2991). -/
theorem mi_delta_x4_pos (x4 x5 x6 : ℝ) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 0 < x6)
    (h8 : x6 < 8) : 0 < deltaX4 x6 2 x5 2 x4 2 := by
  have hid : deltaX4 x6 2 x5 2 x4 2 = x6 * (x4 + x5 - x6) := by
    simp only [deltaX4]; ring
  rw [hid]
  exact mul_pos h6 (by linarith)

/-- HOL `dih_y_div_sqrtdelta_pos` (merge_ineq.hl:3264-3290). -/
theorem mi_dih_y_div_sqrtdelta_pos (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h5 : 2 ≤ y5)
    (h6 : 2 ≤ y6) (h4' : y4 ≤ 2 * Real.sqrt 2) (h5' : y5 ≤ 2 * Real.sqrt 2)
    (h6' : y6 ≤ 2 * Real.sqrt 2) (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    0 ≤ yOfX dih4XDivSqrtdeltaPosbranch (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2)
      y4 y5 y6 := by
  have h8a : y4 ≤ Real.sqrt 8 := by rw [mi_sqrt8_eq]; exact h4'
  have h8b : y5 ≤ Real.sqrt 8 := by rw [mi_sqrt8_eq]; exact h5'
  have h8c : y6 ≤ Real.sqrt 8 := by rw [mi_sqrt8_eq]; exact h6'
  obtain ⟨hlt4, hlt5, hlt6⟩ :=
    mi_ETA_Y_LE_IMP_LT_ALL y4 y5 y6 h4 h8a h5 h8b h6 h8c het
  obtain ⟨hu, hd⟩ := mi_ETA_Y_BOUNDS y4 y5 y6 h4 h8a h5 h8b h6 h8c het
  have hs4 : 0 ≤ y4 := by linarith
  have hs5 : 0 ≤ y5 := by linarith
  have hs6 : 0 ≤ y6 := by linarith
  have hp4 : 0 < y4 * y4 := by positivity
  have hsq4 : y4 * y4 < 8 := by
    have h1 : y4 * y4 < Real.sqrt 8 * Real.sqrt 8 := by
      nlinarith [hlt4, hs4, Real.sqrt_nonneg 8]
    rwa [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)] at h1
  have hyOfX : yOfX dih4XDivSqrtdeltaPosbranch (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2)
      y4 y5 y6 = dih4XDivSqrtdeltaPosbranch 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
    unfold yOfX
    rw [show Real.sqrt 2 * Real.sqrt 2 = 2 from Real.mul_self_sqrt (by norm_num)]
  rw [hyOfX, show dih4XDivSqrtdeltaPosbranch 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6)
      = dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 from rfl]
  refine mi_dihXDivSqrtdeltaPosbranch_nn _ _ _ _ _ _ hp4 ?_ ?_
  · have hid : deltaX (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2
        = deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
      simp only [deltaX]; ring
    rw [hid]; exact hd
  · have hid : deltaX4 (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2
        = y4 * y4 * (y5 * y5 + y6 * y6 - y4 * y4) := by
      simp only [deltaX4]; ring
    rw [hid]
    have h8 : y5 * y5 + y6 * y6 - y4 * y4 > 0 := by
      have h5p : 4 ≤ y5 * y5 := by nlinarith
      have h6p : 4 ≤ y6 * y6 := by nlinarith
      linarith
    exact mul_pos hp4 h8

/-! ### Item 9: gamma3f_gamma3f_x_div_sqrtdelta -/

/-- HOL `gamma3f_x_div_sqrtdelta_arg3` (merge_ineq.hl:3331-3336): the
operator body ignores its first three slots. -/
theorem mi_gamma3fXDivSqrtdelta_arg3 (m4 m5 m6 x1 x2 x3 x4 x5 x6 : ℝ) :
    gamma3fXDivSqrtdelta m4 m5 m6 x1 x2 x3 x4 x5 x6
      = gamma3fXDivSqrtdelta m4 m5 m6 1 1 1 x4 x5 x6 := rfl

/-- HOL `gamma3f_y_div_sqrtdelta_arg3` (merge_ineq.hl:3343-3348): the same
invariance in the `y_of_x` packaging used by the bank entries. -/
theorem mi_gamma3fYDivSqrtdelta_arg3 (m4 m5 m6 : ℝ → ℝ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX (gamma3fXDivSqrtdelta (m4 y4) (m5 y5) (m6 y6)) y1 y2 y3 y4 y5 y6
      = yOfX (gamma3fXDivSqrtdelta (m4 y4) (m5 y5) (m6 y6)) 1 1 1 y4 y5 y6 := rfl

section P21Euler4Kit

set_option maxHeartbeats 50000000
set_option maxRecDepth 20000

/-- The `R[J]/(J^2+1)` element `a + b*J`, realized as a complex number. -/
private def mi_p21eJ (a b : ℝ) : ℂ := a + b * Complex.I

private theorem mi_p21eJ_mul (a b c d : ℝ) :
    mi_p21eJ a b * mi_p21eJ c d = mi_p21eJ (a * c - b * d) (a * d + b * c) := by
  simp only [mi_p21eJ, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  constructor <;> ring

private theorem mi_p21eJ_inj {a b c d : ℝ} (h : mi_p21eJ a b = mi_p21eJ c d) : a = c ∧ b = d := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [mi_p21eJ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  norm_num at h1 h2
  exact ⟨h1, h2⟩

private theorem mi_p21eJ_injEq {a b c d : ℝ} :
    mi_p21eJ a b = mi_p21eJ c d ↔ a = c ∧ b = d := ⟨mi_p21eJ_inj, fun h => by obtain ⟨e1, e2⟩ := h; simp only [e1, e2]⟩

private theorem mi_p21e_atn2 (a b : ℝ) (ha : 0 < a) : atn2 a b = Real.arctan (b / a) := by
  rw [atn2]
  split_ifs with h1 h2 h3
  · rfl
  · have hba : 0 < b / a := div_pos h2 ha
    rw [show a / b = (b / a)⁻¹ from by field_simp, Real.arctan_inv_of_pos hba]
    ring
  · have hz : 0 < -(b / a) := by
      rw [neg_pos]
      exact div_neg_of_neg_of_pos h3 ha
    have h1' : a / b = -(-(b / a))⁻¹ := by field_simp
    have h2' : b / a = -(-(b / a)) := by ring
    rw [h1', Real.arctan_neg, Real.arctan_inv_of_pos hz, h2', Real.arctan_neg]
    ring
  · have hb0 : b = 0 := by linarith
    rw [hb0] at h1
    simp at h1
    linarith

private theorem mi_p21e_matan (z : ℝ) (hz : 0 < z) :
    matan z = Real.arctan (Real.sqrt z) / Real.sqrt z := by
  rw [matan, if_neg (ne_of_gt hz), if_pos hz]

private theorem mi_p21e_dihsym (a b c : ℝ) : dihXf a b 2 2 2 c = dihXf a 2 c 2 b 2 := by
  have hd : deltaX a b 2 2 2 c = deltaX a 2 c 2 b 2 := by simp only [deltaX]; ring
  have hd4 : deltaX4 a b 2 2 2 c = deltaX4 a 2 c 2 b 2 := by simp only [deltaX4]; ring
  unfold dihXf
  rw [hd, hd4]

/-! ### complex-exp helpers -/

private theorem mi_p21e_expI (x : ℝ) :
    Complex.exp (Complex.I * x) = Complex.cos x + Complex.sin x * Complex.I := by
  apply Complex.ext
  · rw [show Complex.I * x = x * Complex.I from by ring, Complex.exp_ofReal_mul_I_re]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.cos_ofReal_re,
      Complex.ofReal_im]
  · rw [show Complex.I * x = x * Complex.I from by ring, Complex.exp_ofReal_mul_I_im]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im]

private theorem mi_p21e_expI' (x : ℝ) :
    Complex.exp (x * Complex.I) = Complex.cos x + Complex.sin x * Complex.I := by
  rw [show x * Complex.I = Complex.I * x from by ring, mi_p21e_expI]

private theorem mi_p21e_expIpi : Complex.exp (Complex.I * Real.pi) = -1 := by
  rw [mi_p21e_expI, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
  norm_num

private theorem mi_p21e_expIc (z : ℂ) :
    Complex.exp (Complex.I * z) = Complex.cos z + Complex.sin z * Complex.I := by
  rw [← mul_comm z Complex.I, Complex.exp_mul_I]

private theorem mi_p21e_T (e q : ℝ) (hq : 0 < q) :
    Complex.exp (Complex.I * (Real.pi / 2 - Real.arctan (e / q)))
      = mi_p21eJ e q / Real.sqrt (e ^ 2 + q ^ 2) := by
  have hc : Complex.cos (↑Real.pi / 2 - ↑(Real.arctan (e / q)))
      = ↑(Real.sin (Real.arctan (e / q))) := by
    have harg : (↑Real.pi / 2 - ↑(Real.arctan (e / q)) : ℂ)
        = ((Real.pi / 2 - Real.arctan (e / q) : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_cos, Real.cos_pi_div_two_sub]
  have hs : Complex.sin (↑Real.pi / 2 - ↑(Real.arctan (e / q)))
      = ↑(Real.cos (Real.arctan (e / q))) := by
    have harg : (↑Real.pi / 2 - ↑(Real.arctan (e / q)) : ℂ)
        = ((Real.pi / 2 - Real.arctan (e / q) : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_sin, Real.sin_pi_div_two_sub]
  rw [mi_p21e_expIc, hc, hs, Real.sin_arctan, Real.cos_arctan, mi_p21eJ]
  have h1 : Real.sqrt (1 + (e / q) ^ 2) = Real.sqrt (e ^ 2 + q ^ 2) / q := by
    rw [show 1 + (e / q) ^ 2 = (e ^ 2 + q ^ 2) / q ^ 2 from by field_simp; ring,
      Real.sqrt_div (by positivity) (q ^ 2), Real.sqrt_sq (le_of_lt hq)]
  rw [h1]
  field_simp
  push_cast
  ring

private theorem mi_p21e_dih_atn (x1 x2 x3 x4 x5 x6 : ℝ) (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6
      = Real.pi / 2 - Real.arctan (deltaX4 x1 x2 x3 x4 x5 x6
          / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) := by
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold dihXf
  rw [mi_p21e_atn2 _ _ hA]
  rw [show (-deltaX4 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      = -(deltaX4 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) from
    by ring, Real.arctan_neg]
  ring

/-! ### The W-product chain (fixed branch order; d-form statements) -/

private theorem mi_p21e_g2 (u v w t d E1 E2 : ℝ) (htd : t ^ 2 = d)
    (hE1 : E1 = u ^ 2 * (v ^ 2 + w ^ 2 - u ^ 2))
    (hE2 : E2 = v ^ 2 * (u ^ 2 + w ^ 2 - v ^ 2)) :
    mi_p21eJ E1 (2 * t * u) * mi_p21eJ E2 (2 * t * v)
      = mi_p21eJ (E1 * E2 - 4 * d * u * v) (2 * t * (v * E1 + u * E2)) := by
  rw [mi_p21eJ_mul, mi_p21eJ_injEq, hE1, hE2]
  constructor
  · ring_nf; rw [htd]; try ring
  · ring

private theorem mi_p21e_g3 (u v w t d s E1 E2 E3 : ℝ) (htd : t ^ 2 = d) :
    mi_p21eJ (E1 * E2 - 4 * d * u * v) (2 * t * (v * E1 + u * E2)) * mi_p21eJ E3 (2 * s * t)
      = mi_p21eJ ((E1 * E2 - 4 * d * u * v) * E3 - 4 * s * d * (v * E1 + u * E2))
          (2 * t * (s * (E1 * E2 - 4 * d * u * v) + (v * E1 + u * E2) * E3)) := by
  rw [mi_p21eJ_mul, mi_p21eJ_injEq]
  constructor
  · ring_nf; rw [htd]; try ring
  · ring






/-- Euler's solid-angle formula at the `(u^2, v^2, 2, 2, 2, w^2)`-pinned
tetrahedron: the spherical-excess form equals the closed form
`pi - 2*arctan(X/t)` (the `EULER_TRIANGLE` specialization consumed by
`sol_x_sol_euler_x`, merge_ineq.hl:841; W-product method: the product
`Z1*Z2*Z3*(t+X*I)^2` over `R[J]/(J^2+1)` elements equals the positive
real `M`, so `e^{i(S-R)} = 1`, and the pinning `S in (-pi, 2*pi)`,
`R in (0, pi)` forces `S = R`). -/
private theorem mi_p21e_euler (u v w t s X E1 E2 E3 : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hu8 : u ^ 2 < 8) (hv8 : v ^ 2 < 8)
    (h1 : u < v + w) (h2 : v < u + w) (h3 : w < u + v)
    (ht0 : 0 < t) (htd : t ^ 2 = (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))
    (hΔ : 0 < (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))
    (hs2 : s ^ 2 = 2) (hs0 : 0 < s)
    (hE1 : E1 = u ^ 2 * (v ^ 2 + w ^ 2 - u ^ 2))
    (hE2 : E2 = v ^ 2 * (u ^ 2 + w ^ 2 - v ^ 2))
    (hE3 : E3 = 4 * (u ^ 2 + v ^ 2 - w ^ 2) - u ^ 2 * v ^ 2)
    (hX : X = (2 * s * u * v + u * v ^ 2 + u ^ 2 * v + s * (u ^ 2 + v ^ 2 - w ^ 2)))
    (hXp : 0 < X) :
    (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + (Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
      + (Real.pi / 2 - Real.arctan (E3 / (2 * s * t)))
      - Real.pi
      = Real.pi - 2 * Real.arctan (X / t) := by
  -- the W-product coefficient M is positive on the cell-3 domain
  -- (four sign-carrying factors: `-u^3*v^3`, `u^2-8`, `v^2-8`, `u-v-w`)
  have hM : (0:ℝ) < ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) := by
    have hu3 : 0 < u ^ 3 := pow_pos hu 3
    have hv3 : 0 < v ^ 3 := pow_pos hv 3
    have hP : (0:ℝ) < u ^ 3 * v ^ 3 := mul_pos hu3 hv3
    have hN1 : (u ^ 2 - 8 : ℝ) < 0 := by linarith
    have hN2 : (v ^ 2 - 8 : ℝ) < 0 := by linarith
    have hN3 : (u - v - w : ℝ) < 0 := by linarith
    have hP4 : (0:ℝ) < u - v + w := by linarith
    have hK8 : (0:ℝ) < 2 * s * (u + v) + u * v + 8 := by
      have hsu : (0:ℝ) < 2 * s * u := by nlinarith
      have hsv : (0:ℝ) < 2 * s * v := by nlinarith
      have hvu : (0:ℝ) < u * v := by nlinarith
      linarith
    have A : (0:ℝ) < -u ^ 3 * v ^ 3 * (u ^ 2 - 8) := by
      have h := mul_neg_of_pos_of_neg hP hN1
      rw [show (-u ^ 3 * v ^ 3 * (u ^ 2 - 8)) = -(u ^ 3 * v ^ 3 * (u ^ 2 - 8)) from by ring]
      exact neg_pos.mpr h
    have B : (-u ^ 3 * v ^ 3 * (u ^ 2 - 8)) * (v ^ 2 - 8) < 0 :=
      mul_neg_of_pos_of_neg A hN2
    have C : (0:ℝ) < (-u ^ 3 * v ^ 3 * (u ^ 2 - 8)) * (v ^ 2 - 8) * (u - v - w) := by
      have h := mul_pos (neg_pos.mpr B) (neg_pos.mpr hN3)
      rwa [show (-((-u ^ 3 * v ^ 3 * (u ^ 2 - 8)) * (v ^ 2 - 8))) * (-(u - v - w))
          = (-u ^ 3 * v ^ 3 * (u ^ 2 - 8)) * (v ^ 2 - 8) * (u - v - w) from by ring] at h
    refine mul_pos (mul_pos (mul_pos (mul_pos C hP4)
      (sq_pos_iff.mpr (by linarith : u + v - w ≠ 0)))
      (sq_pos_iff.mpr (by positivity : u + v + w ≠ 0))) hK8
  -- nonnegativity of the modulus factors (from `hΔ : 0 < DEXP`)
  have hnn1 : (0:ℝ) ≤ E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2 := by
    have h1 : (0:ℝ) ≤ E1 ^ 2 := sq_nonneg E1
    have h2 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
    have h3 : (0:ℝ) ≤ 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2 := by nlinarith
    linarith
  have hnn2 : (0:ℝ) ≤ E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2 := by
    have h1 : (0:ℝ) ≤ E2 ^ 2 := sq_nonneg E2
    have h2 : (0:ℝ) ≤ v ^ 2 := sq_nonneg v
    have h3 : (0:ℝ) ≤ 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2 := by nlinarith
    linarith
  have hnn3 : (0:ℝ) ≤ E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) := by
    have h1 : (0:ℝ) ≤ E3 ^ 2 := sq_nonneg E3
    have h2 : (0:ℝ) ≤ s ^ 2 := sq_nonneg s
    have h3 : (0:ℝ) ≤ 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) := by nlinarith
    linarith
  have hnn12 : (0:ℝ) ≤ (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2) :=
    mul_nonneg hnn1 hnn2
  -- the W-product chain over `R[J]/(J^2+1)` elements, `t^2` reduced to `DEXP`
  set W := v * E1 + u * E2 with hW
  set a := E1 * E2 - 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u * v with ha
  set A := a * E3 - 4 * s * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * W with hA
  set B := 2 * t * (s * a + W * E3) with hB
  have hz12 : mi_p21eJ E1 (2 * t * u) * mi_p21eJ E2 (2 * t * v) = mi_p21eJ a (2 * t * W) := by
    rw [mi_p21e_g2 u v w t (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) E1 E2 htd hE1 hE2, ← hW, ← ha]
  have hz123 : mi_p21eJ a (2 * t * W) * mi_p21eJ E3 (2 * s * t) = mi_p21eJ A B := by
    rw [mi_p21e_g3 u v w t (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) s E1 E2 E3 htd, ← hW, ← ha]
  have hf4 : (t + X * Complex.I) ^ 2 = mi_p21eJ ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) (2 * t * X) := by
    have h1 : mi_p21eJ t X * mi_p21eJ t X = mi_p21eJ (t ^ 2 - X ^ 2) (2 * t * X) := by
      rw [mi_p21eJ_mul t X t X, mi_p21eJ_injEq]
      constructor <;> ring
    rw [sq]
    calc (t + X * Complex.I) * (t + X * Complex.I)
        = mi_p21eJ t X * mi_p21eJ t X := by rw [mi_p21eJ]
      _ = mi_p21eJ (t ^ 2 - X ^ 2) (2 * t * X) := h1
      _ = mi_p21eJ ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) (2 * t * X) := by rw [htd]
  have hprod : mi_p21eJ A B * mi_p21eJ ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) (2 * t * X)
      = mi_p21eJ (A * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) - B * (2 * t * X))
          (A * (2 * t * X) + B * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2)) :=
    mi_p21eJ_mul A B ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) (2 * t * X)
  -- the two sympy identities (W-product = M modulo `t ^ 2 = DEXP`, `s ^ 2 = 2`)
  have hre : A * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) - B * (2 * t * X)
      = ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) + (t ^ 2 - (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4)) * ((-16*u^4*v^6 - 16*u^6*v^4 - 4*u^4*v^8 - 4*u^8*v^4 + 8*u^6*v^6 + 16*u^2*v^8 + 16*u^8*v^2 - 64*s^2*u^2*v^6 - 64*s^2*u^6*v^2 - 48*s*u^3*v^6 - 48*s*u^6*v^3 - 32*u*s^2*v^7 - 32*v*s^2*u^7 - 32*u^2*v^6*w^2 - 32*u^3*v^5*w^2 - 32*u^5*v^3*w^2 - 32*u^6*v^2*w^2 - 16*s*u^2*v^7 - 16*s*u^7*v^2 - 16*s^2*u^5*v^5 - 4*s^2*u^4*v^6 - 4*s^2*u^6*v^4 + 4*s^2*u^2*v^8 + 4*s^2*u^8*v^2 + 4*u^4*v^6*w^2 + 4*u^6*v^4*w^2 + 8*s^2*u^3*v^7 + 8*s^2*u^7*v^3 + 8*u^5*v^5*w^2 + 16*s*u*v^8 + 16*s*v*u^8 + 16*u^2*v^4*w^4 + 16*u^4*v^2*w^4 + 32*s^2*u^3*v^5 + 32*s^2*u^5*v^3 + 32*u^3*v^3*w^4 + 48*s*u^4*v^5 + 48*s*u^5*v^4 + 128*s^2*u^4*v^4 - 96*u*s^2*v^3*w^4 - 96*v*s^2*u^3*w^4 - 64*s^2*u^2*v^2*w^4 - 48*s*u*v^6*w^2 - 48*s*v*u^6*w^2 - 24*s^2*u^4*v^4*w^2 - 16*s*u*v^2*w^6 - 16*s*v*u^2*w^6 - 16*s^2*u^3*v^5*w^2 - 16*s^2*u^5*v^3*w^2 - 8*s*u^3*v^4*w^4 - 8*s*u^4*v^3*w^4 - 8*s*u^4*v^5*w^2 - 8*s*u^5*v^4*w^2 - 4*s^2*u^2*v^4*w^4 - 4*s^2*u^2*v^6*w^2 - 4*s^2*u^4*v^2*w^4 - 4*s^2*u^6*v^2*w^2 + 4*s^2*u^2*v^2*w^6 + 8*s*u^3*v^6*w^2 + 8*s*u^6*v^3*w^2 + 8*s^2*u^3*v^3*w^4 + 16*s*u^2*v^3*w^4 + 16*s*u^2*v^5*w^2 + 16*s*u^3*v^2*w^4 + 16*s*u^5*v^2*w^2 + 32*s*u^3*v^4*w^2 + 32*s*u^4*v^3*w^2 + 32*u*v*s^2*w^6 + 48*s*u*v^4*w^4 + 48*s*v*u^4*w^4 + 64*s^2*u^3*v^3*w^2 + 96*u*s^2*v^5*w^2 + 96*v*s^2*u^5*w^2 + 128*s^2*u^2*v^4*w^2 + 128*s^2*u^4*v^2*w^2)) + (s ^ 2 - 2) * ((-u^4*v^12 - u^12*v^4 - 512*u^4*v^8 - 512*u^8*v^4 - 352*u^3*v^9 - 352*u^9*v^3 - 40*u^6*v^8 - 40*u^8*v^6 - 32*u^5*v^9 - 32*u^9*v^5 - 16*u^7*v^7 - 4*u^5*v^11 - 4*u^6*v^10 - 4*u^10*v^6 - 4*u^11*v^5 + 4*u^7*v^9 + 4*u^9*v^7 + 10*u^8*v^8 + 12*u^2*v^12 + 12*u^12*v^2 + 28*u^4*v^10 + 28*u^10*v^4 + 32*u*v^11 + 32*v*u^11 + 40*u^3*v^11 + 40*u^11*v^3 + 320*u^5*v^7 + 320*u^7*v^5 + 1024*u^6*v^6 - 576*u^3*v^5*w^4 - 576*u^5*v^3*w^4 - 512*u^4*v^4*w^4 - 320*u*v^5*w^6 - 320*v*u^5*w^6 - 248*u^6*v^6*w^2 - 160*u*v^9*w^2 - 160*v*u^9*w^2 - 144*u^5*v^7*w^2 - 144*u^7*v^5*w^2 - 128*u^3*v^3*w^6 - 112*u^3*v^9*w^2 - 112*u^9*v^3*w^2 - 88*s*u^4*v^9 - 88*s*u^9*v^4 - 80*u^4*v^4*w^6 - 80*u^4*v^8*w^2 - 80*u^8*v^4*w^2 - 72*u^2*v^6*w^6 - 72*u^6*v^2*w^6 - 52*u^2*v^10*w^2 - 52*u^10*v^2*w^2 - 48*s*u^5*v^8 - 48*s*u^8*v^5 - 32*u*v*w^10 - 20*u^5*v^7*w^4 - 20*u^7*v^5*w^4 - 16*u^3*v^5*w^6 - 16*u^5*v^3*w^6 - 16*u^6*v^6*w^4 - 12*u^4*v^8*w^4 - 12*u^8*v^4*w^4 - 8*s*u^3*v^10 - 8*s*u^10*v^3 - 8*u^3*v^3*w^8 - 4*u^2*v^2*w^10 - 3*u^4*v^4*w^8 + 6*u^4*v^10*w^2 + 6*u^10*v^4*w^2 + 8*s*u*v^12 + 8*s*v*u^12 + 8*u^5*v^5*w^6 + 10*u^4*v^6*w^6 + 10*u^6*v^4*w^6 + 10*u^6*v^8*w^2 + 10*u^8*v^6*w^2 + 16*u^5*v^9*w^2 + 16*u^9*v^5*w^2 + 24*s*u^2*v^11 + 24*s*u^11*v^2 + 28*u^2*v^4*w^8 + 28*u^4*v^2*w^8 + 88*u^2*v^8*w^4 + 88*u^8*v^2*w^4 + 96*u^3*v^7*w^4 + 96*u^7*v^3*w^4 + 104*u^4*v^6*w^4 + 104*u^6*v^4*w^4 + 112*s*u^6*v^7 + 112*s*u^7*v^6 + 160*u*v^3*w^8 + 160*v*u^3*w^8 + 192*u^5*v^5*w^4 + 320*u*v^7*w^4 + 320*v*u^7*w^4 + 576*u^5*v^5*w^2 + 896*u^3*v^7*w^2 + 896*u^7*v^3*w^2 + 1024*u^4*v^6*w^2 + 1024*u^6*v^4*w^2 - 160*s*u^3*v^4*w^6 - 160*s*u^4*v^3*w^6 - 144*s*u^2*v^5*w^6 - 144*s*u^5*v^2*w^6 - 104*s*u^2*v^9*w^2 - 104*s*u^9*v^2*w^2 - 80*s*u*v^6*w^6 - 80*s*v*u^6*w^6 - 40*s*u*v^10*w^2 - 40*s*v*u^10*w^2 - 32*s*u^3*v^8*w^2 - 32*s*u^8*v^3*w^2 - 28*s*u^4*v^7*w^4 - 28*s*u^7*v^4*w^4 - 24*s*u^5*v^6*w^4 - 24*s*u^6*v^5*w^4 - 20*s*u^6*v^7*w^2 - 20*s*u^7*v^6*w^2 - 12*s*u^3*v^8*w^4 - 12*s*u^8*v^3*w^4 - 8*s*u*v^2*w^10 - 8*s*v*u^2*w^10 - 4*s*u^3*v^4*w^8 - 4*s*u^4*v^3*w^8 + 4*s*u^3*v^10*w^2 + 4*s*u^5*v^8*w^2 + 4*s*u^8*v^5*w^2 + 4*s*u^10*v^3*w^2 + 12*s*u^3*v^6*w^6 + 12*s*u^4*v^9*w^2 + 12*s*u^6*v^3*w^6 + 12*s*u^9*v^4*w^2 + 20*s*u^4*v^5*w^6 + 20*s*u^5*v^4*w^6 + 40*s*u*v^4*w^8 + 40*s*v*u^4*w^8 + 56*s*u^2*v^3*w^8 + 56*s*u^3*v^2*w^8 + 80*s*u*v^8*w^4 + 80*s*v*u^8*w^4 + 80*s*u^5*v^6*w^2 + 80*s*u^6*v^5*w^2 + 96*s*u^4*v^7*w^2 + 96*s*u^7*v^4*w^2 + 112*s*u^4*v^5*w^4 + 112*s*u^5*v^4*w^4 + 144*s*u^3*v^6*w^4 + 144*s*u^6*v^3*w^4 + 176*s*u^2*v^7*w^4 + 176*s*u^7*v^2*w^4)) := by
    rw [hA, hB, ha, hW, hE1, hE2, hE3, hX]
    ring
  have him : A * (2 * t * X) + B * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2)
      = (s ^ 2 - 2) * ((-24*t*u^2*v^9 - 24*t*u^9*v^2 - 16*t*u^3*v^8 - 16*t*u^8*v^3 - 10*t*u^6*v^7 - 10*t*u^7*v^6 - 8*t*u*v^10 - 8*t*v*u^10 + 2*t*u^3*v^10 + 2*t*u^5*v^8 + 2*t*u^8*v^5 + 2*t*u^10*v^3 + 6*t*u^4*v^9 + 6*t*u^9*v^4 + 16*t*u^4*v^7 + 16*t*u^7*v^4 + 32*t*u^5*v^6 + 32*t*u^6*v^5 - 112*t*u^3*v^4*w^4 - 112*t*u^4*v^3*w^4 - 96*t*u^2*v^5*w^4 - 96*t*u^5*v^2*w^4 - 64*s*t*u^2*v^8 - 64*s*t*u^3*v^7 - 64*s*t*u^7*v^3 - 64*s*t*u^8*v^2 - 48*t*u*v^6*w^4 - 48*t*v*u^6*w^4 - 20*s*t*u^6*v^6 - 16*s*t*u*v^9 - 16*s*t*v*u^9 - 14*t*u^4*v^7*w^2 - 14*t*u^7*v^4*w^2 - 12*t*u^5*v^6*w^2 - 12*t*u^6*v^5*w^2 - 8*s*t*u^5*v^7 - 8*s*t*u^7*v^5 - 8*t*u*v^2*w^8 - 8*t*v*u^2*w^8 - 6*t*u^3*v^8*w^2 - 6*t*u^8*v^3*w^2 - 2*t*u^3*v^4*w^6 - 2*t*u^4*v^3*w^6 + 2*s*t*u^2*v^10 + 2*s*t*u^10*v^2 + 6*t*u^3*v^6*w^4 + 6*t*u^6*v^3*w^4 + 8*s*t*u^3*v^9 + 8*s*t*u^4*v^8 + 8*s*t*u^8*v^4 + 8*s*t*u^9*v^3 + 10*t*u^4*v^5*w^4 + 10*t*u^5*v^4*w^4 + 32*t*u*v^4*w^6 + 32*t*u*v^8*w^2 + 32*t*v*u^4*w^6 + 32*t*v*u^8*w^2 + 48*t*u^2*v^3*w^6 + 48*t*u^3*v^2*w^6 + 64*s*t*u^4*v^6 + 64*s*t*u^6*v^4 + 64*t*u^4*v^5*w^2 + 64*t*u^5*v^4*w^2 + 80*t*u^2*v^7*w^2 + 80*t*u^3*v^6*w^2 + 80*t*u^6*v^3*w^2 + 80*t*u^7*v^2*w^2 + 160*s*t*u^5*v^5 - 192*s*t*u^2*v^4*w^4 - 192*s*t*u^3*v^3*w^4 - 192*s*t*u^4*v^2*w^4 - 96*s*t*u*v^5*w^4 - 96*s*t*v*u^5*w^4 - 32*s*t*u^5*v^5*w^2 - 28*s*t*u^4*v^6*w^2 - 28*s*t*u^6*v^4*w^2 - 16*s*t*u*v*w^8 - 16*s*t*u^3*v^7*w^2 - 16*s*t*u^7*v^3*w^2 - 4*s*t*u^2*v^8*w^2 - 4*s*t*u^8*v^2*w^2 - 2*s*t*u^2*v^2*w^8 + 4*s*t*u^2*v^4*w^6 + 4*s*t*u^4*v^2*w^6 + 8*s*t*u^3*v^5*w^4 + 8*s*t*u^5*v^3*w^4 + 16*s*t*u^4*v^4*w^4 + 64*s*t*u*v^3*w^6 + 64*s*t*u*v^7*w^2 + 64*s*t*v*u^3*w^6 + 64*s*t*v*u^7*w^2 + 64*s*t*u^2*v^2*w^6 + 128*s*t*u^4*v^4*w^2 + 192*s*t*u^2*v^6*w^2 + 192*s*t*u^3*v^5*w^2 + 192*s*t*u^5*v^3*w^2 + 192*s*t*u^6*v^2*w^2)) := by
    rw [hA, hB, ha, hW, hE1, hE2, hE3, hX]
    ring
  -- the squared-modulus bookkeeping (all real, pure ring)
  have hsqid : (A ^ 2 + B ^ 2) * (((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) ^ 2 + (2 * t * X) ^ 2)
      = (A * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) - B * (2 * t * X)) ^ 2
        + (A * (2 * t * X) + B * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2)) ^ 2 := by ring
  -- kill the correction terms in `hre`/`him` *before* they ever touch `hsqid`:
  -- rewriting the giant correction polynomials into `hsqid` builds an enormous
  -- motive; instead keep them opaque and kill each zero factor separately.
  have htd' : t ^ 2 - (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) = 0 := by
    rw [htd]; ring
  have hs2' : s ^ 2 - 2 = 0 := by rw [hs2]; ring
  have hre0 : A * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) - B * (2 * t * X) = ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) := by
    rw [hre, htd', hs2']
    ring
  have him0 : A * (2 * t * X) + B * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) = 0 := by
    rw [him, hs2']
    ring
  have hsqid' : (A ^ 2 + B ^ 2) * (((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) ^ 2 + (2 * t * X) ^ 2)
      = ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) ^ 2 := by
    have h1 := hsqid
    rw [hre0, him0] at h1
    simpa using h1
  have hpow2 : (2 * t * X) ^ 2 = 4 * t ^ 2 * X ^ 2 := by ring
  have hgh2 : (((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) - X ^ 2) ^ 2 + 4 * t ^ 2 * X ^ 2) = (((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) + X ^ 2) ^ 2) := by
    rw [htd]; ring
  -- nonnegativity of the three squared modulus factors (from `hΔ`)
  have hf1 : (0:ℝ) ≤ E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2 := by
    positivity
  have hf2 : (0:ℝ) ≤ E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2 := by
    positivity
  have hf3 : (0:ℝ) ≤ E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) := by
    positivity
  -- `(2*t*u)^2`-shapes into the D-form used by the sqrt factors
  have hsqr1 : Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) = Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) := by
    congr 1
    rw [show (2 * t * u) ^ 2 = 4 * t ^ 2 * u ^ 2 from by ring, htd]
  have hsqr2 : Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2) = Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2) := by
    congr 1
    rw [show (2 * t * v) ^ 2 = 4 * t ^ 2 * v ^ 2 from by ring, htd]
  have hsqr3 : Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2) = Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4)) := by
    congr 1
    rw [show (2 * s * t) ^ 2 = 4 * s ^ 2 * t ^ 2 from by ring, htd]
  -- squares of the sqrt factors
  have hd1 : Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) ^ 2 = E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2 :=
    Real.sq_sqrt hf1
  have hd2 : Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2) ^ 2 = E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2 :=
    Real.sq_sqrt hf2
  have hd3 : Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4)) ^ 2 = E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) :=
    Real.sq_sqrt hf3
  have hrad : (Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2)
      * Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))) ^ 2
      = (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2) * (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4)) := by
    rw [mul_pow, mul_pow, hd1, hd2, hd3]
  -- factor identities for the modulus (small rings: `a, W` stay abstract)
  have hsq1 : A ^ 2 + B ^ 2
      = (a ^ 2 + 4 * t ^ 2 * W ^ 2) * (E3 ^ 2 + 4 * s ^ 2 * t ^ 2) := by
    have hA2 : A ^ 2 = (a * E3 - 4 * s * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * W) ^ 2 := by rw [hA]
    have hB2 : B ^ 2 = 4 * t ^ 2 * (s * a + W * E3) ^ 2 := by rw [hB]; ring
    rw [hA2, hB2, htd]
    ring
  have hsq2 : a ^ 2 + 4 * t ^ 2 * W ^ 2
      = (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2) := by
    rw [ha, hW, htd]; ring
  have hmod : A ^ 2 + B ^ 2
      = (Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2)
        * Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))) ^ 2 := by
    rw [hsq1, hsq2, htd]
    exact hrad.symm
  -- hsqid : (A^2 + B^2) * (DEXP + X^2)^2 = M^2
  have hcomb : ((Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2)
        * Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))) * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) + X ^ 2)) ^ 2 = ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) ^ 2 := by
    have h1 := hsqid'
    rw [hpow2, hgh2] at h1
    rw [hmod, ← mul_pow] at h1
    exact h1
  have hkey : (Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2)
      * Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))) * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) + X ^ 2) = ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) := by
    have hpos : (0:ℝ) ≤ (Real.sqrt (E1 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * u ^ 2) * Real.sqrt (E2 ^ 2 + 4 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) * v ^ 2) * Real.sqrt (E3 ^ 2 + 4 * s ^ 2 * (-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4))) * ((-2*u^4 - u^2*v^2*w^2 + 4*u^2*v^2 + 4*u^2*w^2 - 2*v^4 + 4*v^2*w^2 - 2*w^4) + X ^ 2) := by
      refine mul_nonneg ?_ ?_
      · positivity
      · positivity
    exact (sq_eq_sq₀ hpos (le_of_lt hM)).mp hcomb
  have hM0 : mi_p21eJ ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) 0 = (((((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) : ℝ) : ℂ)) := by
    simp [mi_p21eJ]
  -- the main identity: `Z1 * Z2 * Z3 * (t + X*I)^2 = M`
  have h14 : mi_p21eJ E1 (2 * t * u) * mi_p21eJ E2 (2 * t * v) * mi_p21eJ E3 (2 * s * t)
      * (t + X * Complex.I) ^ 2 = (((((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) : ℝ) : ℂ)) := by
    rw [hf4, hz12, hz123, hprod, hre0, him0, hM0]
  have hZP : mi_p21eJ E1 (2 * t * u) * mi_p21eJ E2 (2 * t * v) * mi_p21eJ E3 (2 * s * t)
      = ((((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) : ℝ) : ℂ) / (t + X * Complex.I) ^ 2 := by
    rw [eq_div_iff ?_]
    · exact h14
    · have hnz : (t + X * Complex.I) ≠ 0 := by
        intro hc
        have h := congrArg Complex.re hc
        simp at h
        linarith only [ht0, h]
      exact pow_ne_zero 2 hnz
  -- the exponential assembly
  have hexpS : Complex.exp (Complex.I * ((Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + ((Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
        + ((Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi))))
      = -(mi_p21eJ E1 (2 * t * u) * mi_p21eJ E2 (2 * t * v) * mi_p21eJ E3 (2 * s * t))
        / (Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) * Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2)
          * Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2)) := by
    rw [show Complex.I * ((Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
        + ((Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
          + ((Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi)))
      = Complex.I * (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
        + (Complex.I * (Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
          + (Complex.I * (Real.pi / 2 - Real.arctan (E3 / (2 * s * t)))
            + Complex.I * (-Real.pi))) from by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_add,
      mi_p21e_T _ _ (by positivity), mi_p21e_T _ _ (by positivity), mi_p21e_T _ _ (by positivity),
      show Complex.I * (-Real.pi) = -(Complex.I * Real.pi) from by ring,
      Complex.exp_neg, mi_p21e_expIpi]
    ring
  have hexpR : Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (X / t)))
      = (X + t * Complex.I) ^ 2 / (((t ^ 2 + X ^ 2 : ℝ) : ℂ)) := by
    have h2 : Complex.I * (Real.pi - 2 * Real.arctan (X / t))
        = ((2:ℕ):ℂ) * (Complex.I * (↑Real.pi / 2 - ↑(Real.arctan (X / t)))) := by
      push_cast
      ring
    rw [h2, Complex.exp_nat_mul, mi_p21e_T X t ht0, div_pow]
    congr 1
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ X ^ 2 + t ^ 2)]
    congr 1
    ring
  have hXt : (X + t * Complex.I) ^ 2 = -((t - X * Complex.I) ^ 2) := by
    apply Complex.ext
    · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  have hIform : ((t + X * Complex.I) * (t - X * Complex.I) : ℂ) = ((t ^ 2 + X ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
  have hkr : (Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) * Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2)
      * Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2)) * (t ^ 2 + X ^ 2) = ((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) := by
    rw [hsqr1, hsqr2, hsqr3, htd]
    exact hkey
  have hkeyT : ((Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) : ℂ) * (Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2) : ℂ)
      * (Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2) : ℂ)) * (((t ^ 2 + X ^ 2) : ℝ) : ℂ)
      = ((((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) : ℝ) : ℂ) := by
    have h := congrArg Complex.ofReal hkr
    push_cast at h ⊢
    exact h
  have hTpos : (0:ℝ) < t ^ 2 + X ^ 2 := by positivity
  have hTne : (((t ^ 2 + X ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hTpos
  have hKne : (↑t + ↑X * Complex.I : ℂ) ≠ 0 := by
    intro hc
    have h := hIform
    rw [hc, zero_mul] at h
    exact hTne h.symm
  have hKbarne : (↑t - ↑X * Complex.I : ℂ) ≠ 0 := by
    intro hc
    have h := hIform
    rw [hc, mul_zero] at h
    exact hTne h.symm
  have hq1 : (0:ℝ) < 2 * t * u := by positivity
  have hq2 : (0:ℝ) < 2 * t * v := by positivity
  have hq3 : (0:ℝ) < 2 * s * t := by positivity
  have h1pos : (0:ℝ) < Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have h2pos : (0:ℝ) < Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have h3pos : (0:ℝ) < Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have h1ne : ((Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h1pos
  have h2ne : ((Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h2pos
  have h3ne : ((Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h3pos
  have hRne : ((Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) : ℂ) * (Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2) : ℂ)
      * (Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero h1ne h2ne) h3ne
  -- atomize the giant modulus/key expressions so that `field_simp`/`ring`
  -- never expand them
  set MM : ℂ := ((((-u ^ 3 * v ^ 3 * (u ^ 2 - 8) * (v ^ 2 - 8) * (u - v - w) * (u - v + w) * (u + v - w) ^ 2 * (u + v + w) ^ 2 * (2 * s * (u + v) + u * v + 8))) : ℝ) : ℂ) with hMM
  set RR : ℂ := ((Real.sqrt (E1 ^ 2 + (2 * t * u) ^ 2) : ℂ) * (Real.sqrt (E2 ^ 2 + (2 * t * v) ^ 2) : ℂ)
    * (Real.sqrt (E3 ^ 2 + (2 * s * t) ^ 2) : ℂ)) with hRR
  set KK : ℂ := ((t : ℂ) + (X : ℂ) * Complex.I) with hKK
  set KB : ℂ := ((t : ℂ) - (X : ℂ) * Complex.I) with hKB
  set TT : ℂ := (((t ^ 2 + X ^ 2 : ℝ)) : ℂ) with hTT
  have hZP' : mi_p21eJ E1 (2 * t * u) * mi_p21eJ E2 (2 * t * v) * mi_p21eJ E3 (2 * s * t) = MM / KK ^ 2 := by
    rw [hMM, hKK]
    exact hZP
  have hXt' : ((X : ℂ) + (t : ℂ) * Complex.I) ^ 2 = -(KB ^ 2) := by
    rw [hKB]
    exact hXt
  have hexpR' : Complex.exp (Complex.I * (Real.pi - 2 * Real.arctan (X / t))) = -(KB ^ 2) / TT := by
    rw [hTT, ← hXt']
    exact hexpR
  have hkeyT' : RR * TT = MM := by
    rw [hRR, hTT, hMM]
    exact hkeyT
  have hIform' : KK * KB = TT := by
    rw [hKK, hKB, hTT]
    exact hIform
  have hKKne : KK ≠ 0 := by rw [hKK]; exact hKne
  have hKBne : KB ≠ 0 := by rw [hKB]; exact hKbarne
  have hTTne : TT ≠ 0 := by rw [hTT]; exact hTne
  have hRRne : RR ≠ 0 := by rw [hRR]; exact hRne
  have hexpSR : Complex.exp (Complex.I * (((Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + ((Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
        + ((Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi)))
      - (Real.pi - 2 * Real.arctan (X / t)))) = 1 := by
    rw [mul_sub, Complex.exp_sub, hexpS, hexpR', hZP']
    field_simp [hKKne, hKBne, hTTne, hRRne]
    rw [← hkeyT']
    rw [show KK ^ 2 * RR * KB ^ 2 = RR * (KK ^ 2 * KB ^ 2) from by ring]
    rw [show KK ^ 2 * KB ^ 2 = TT ^ 2 from by rw [← mul_pow, hIform']]
    ring
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp hexpSR
  have hSR : ((Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + ((Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
        + ((Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi)))
      - (Real.pi - 2 * Real.arctan (X / t)) = (n:ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    have hpi : ((n:ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = (((n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hpi] at h
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_re, Complex.add_im, zero_mul, one_mul, mul_one, mul_zero,
      add_zero, zero_add, sub_zero] at h
    rw [Complex.div_re] at h
    norm_num [Complex.normSq] at h
    linarith only [h]
  -- pinning: the S-side lies in `(-pi, 2*pi)`, the R-side in `(0, pi)`
  have hb1 : (0:ℝ) < Real.pi / 2 - Real.arctan (E1 / (2 * t * u)) :=
    by linarith only [Real.arctan_lt_pi_div_two (E1 / (2 * t * u))]
  have hb2 : (0:ℝ) < Real.pi / 2 - Real.arctan (E2 / (2 * t * v)) :=
    by linarith only [Real.arctan_lt_pi_div_two (E2 / (2 * t * v))]
  have hb3 : (0:ℝ) < Real.pi / 2 - Real.arctan (E3 / (2 * s * t)) :=
    by linarith only [Real.arctan_lt_pi_div_two (E3 / (2 * s * t))]
  have hb1' : Real.pi / 2 - Real.arctan (E1 / (2 * t * u)) < Real.pi :=
    by linarith only [Real.neg_pi_div_two_lt_arctan (E1 / (2 * t * u))]
  have hb2' : Real.pi / 2 - Real.arctan (E2 / (2 * t * v)) < Real.pi :=
    by linarith only [Real.neg_pi_div_two_lt_arctan (E2 / (2 * t * v))]
  have hb3' : Real.pi / 2 - Real.arctan (E3 / (2 * s * t)) < Real.pi :=
    by linarith only [Real.neg_pi_div_two_lt_arctan (E3 / (2 * s * t))]
  have hq : (0:ℝ) < X / t := div_pos hXp ht0
  have hbR : (0:ℝ) < Real.pi - 2 * Real.arctan (X / t) :=
    by linarith only [Real.arctan_pos.mpr hq, Real.arctan_lt_pi_div_two (X / t)]
  have hbR' : Real.pi - 2 * Real.arctan (X / t) < Real.pi :=
    by linarith only [Real.arctan_pos.mpr hq]
  have hS0 : -(Real.pi) < (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + ((Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
        + ((Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi)) := by
    linarith only [hb1, hb2, hb3]
  have hS1 : (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + ((Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
        + ((Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi)) < 2 * Real.pi := by
    linarith only [hb1', hb2', hb3']
  have hSR' : (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + (Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
      + (Real.pi / 2 - Real.arctan (E3 / (2 * s * t)))
      - Real.pi - (Real.pi - 2 * Real.arctan (X / t)) = (n:ℝ) * (2 * Real.pi) := by
    linarith only [hSR]
  have hS0' : -(Real.pi) < (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + (Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
      + (Real.pi / 2 - Real.arctan (E3 / (2 * s * t)))
      - Real.pi := by
    linarith only [hS0]
  have hS1' : (Real.pi / 2 - Real.arctan (E1 / (2 * t * u)))
      + (Real.pi / 2 - Real.arctan (E2 / (2 * t * v)))
      + (Real.pi / 2 - Real.arctan (E3 / (2 * s * t)))
      - Real.pi < 2 * Real.pi := by
    linarith only [hS1]
  -- local copy of the two-pin lemma: the green finisher was developed in a
  -- file where `mi_p21e_pin_zero` was a file-level lemma; this master has no such
  -- lemma, so keep the identical statement local to this proof segment.
  have mi_p21e_pin_zero : ∀ (S R : ℝ) (n : ℤ),
      S - R = (n:ℝ) * (2*Real.pi) → -(Real.pi) < S → S < 2*Real.pi →
      0 < R → R < Real.pi → S = R := by
    intro S R n hSR hS0 hS1 hR0 hR1
    have hn : n = 0 := by
      rcases lt_trichotomy n 0 with h | h | h
      · have hle : (n:ℝ) ≤ -1 := by
          have hz : n ≤ -1 := by omega
          exact_mod_cast hz
        have hb : S - R ≤ -(2*Real.pi) := by
          calc S - R = (n:ℝ) * (2*Real.pi) := hSR
            _ ≤ (-1:ℝ) * (2*Real.pi) := mul_le_mul_of_nonneg_right hle (by positivity)
            _ = -(2*Real.pi) := by ring
        linarith only [hb, hS0, hS1, hR0, hR1]
      · exact h
      · have hle : (1:ℝ) ≤ (n:ℝ) := by
          have hz : (1:ℤ) ≤ n := by omega
          exact_mod_cast hz
        have hb : 2*Real.pi ≤ S - R := by
          calc (2*Real.pi : ℝ) = 1 * (2*Real.pi) := by ring
            _ ≤ (n:ℝ) * (2*Real.pi) := mul_le_mul_of_nonneg_right hle (by positivity)
            _ = S - R := hSR.symm
        linarith only [hb, hS1, hR0]
    rw [hn] at hSR
    push_cast at hSR
    linarith only [hSR]
  exact mi_p21e_pin_zero _ _ n hSR' hS0' hS1' hbR hbR'

/-! ### the sol/dih bridges at the `(2,2,2)` pattern -/

/-- Positivity of the `(2,2,2)`-pinned Cayley determinant on the cell-3
domain (from the eta bound: `y_j < sqrt 8` forces `deltaX 2 2 2 > 0`). -/
private theorem mi_p21e_delta222_pos (y1 y2 y3 : ℝ) (h1 : 2 ≤ y1) (h1' : y1 ≤ Real.sqrt 8)
    (h2 : 2 ≤ y2) (h2' : y2 ≤ Real.sqrt 8) (h3 : 2 ≤ y3) (h3' : y3 ≤ Real.sqrt 8)
    (het : eta_y y1 y2 y3 < Real.sqrt 2) :
    0 < deltaX 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) := by
  exact mi_ETA_Y_BOUNDS y1 y2 y3 h1 h1' h2 h2' h3 h3' het |>.2

/-- The base-triangle inequality `y4^2 < y5^2 + y6^2` on the cell domain. -/
private theorem mi_p21e_tri (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ Real.sqrt 8) (h6 : 2 ≤ y6) (h6' : y6 ≤ Real.sqrt 8)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) : y4 * y4 < y5 * y5 + y6 * y6 := by
  obtain ⟨hlt4, hlt5, hlt6⟩ := mi_ETA_Y_LE_IMP_LT_ALL y4 y5 y6 h4 h4' h5 h5' h6 h6' het
  have h8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have h4sq : y4 * y4 < 8 := by rw [← h8]; nlinarith
  have h5sq : (4:ℝ) ≤ y5 * y5 := by nlinarith
  have h6sq : (4:ℝ) ≤ y6 * y6 := by nlinarith
  linarith

/-- Unfolding `sol_euler_x_div_sqrtdelta` at the `(y1^2,y2^2,2,2,2,y3^2)`
pattern: the let-bound `a` is `X/2` (with `X` the `mi_p21e_euler` variable),
and `delta_x` is `D`. -/
private theorem mi_p21e_solE (y1 y2 y3 s X D : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hX : X = 2 * s * y1 * y2 + y1 * y2 ^ 2 + y1 ^ 2 * y2
      + s * (y1 ^ 2 + y2 ^ 2 - y3 ^ 2))
    (hs : s = Real.sqrt 2) (hs2 : s ^ 2 = 2)
    (hDa : deltaX (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3) = D) :
    solEulerXDivSqrtdelta (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3)
      = matan (D / (4 * (X / 2) ^ 2)) / (X / 2) := by
  unfold solEulerXDivSqrtdelta
  dsimp only
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsa : Real.sqrt (y1 * y1) = y1 := by
    rw [show y1 * y1 = y1 ^ 2 by ring, Real.sqrt_sq (le_of_lt hy1)]
  have hsb : Real.sqrt (y2 * y2) = y2 := by
    rw [show y2 * y2 = y2 ^ 2 by ring, Real.sqrt_sq (le_of_lt hy2)]
  have hsabc : Real.sqrt ((y1 * y1) * (y2 * y2) * 2) = y1 * y2 * s := by
    have hsq : (y1 * y2 * s) ^ 2 = (y1 * y1) * (y2 * y2) * 2 := by
      calc (y1 * y2 * s) ^ 2 = y1 ^ 2 * y2 ^ 2 * s ^ 2 := by ring
        _ = y1 ^ 2 * y2 ^ 2 * 2 := by rw [hs2]
        _ = (y1 * y1) * (y2 * y2) * 2 := by ring
    rw [← hsq, Real.sqrt_sq (le_of_lt (by positivity : 0 < y1 * y2 * s))]
  rw [hsabc, hsa, hsb, ← hs, hDa]
  have hA : y1 * y2 * s + y1 * (y2 * y2 + 2 - 2) / 2
      + y2 * (y1 * y1 + 2 - 2) / 2
      + s * (y1 * y1 + y2 * y2 - y3 * y3) / 2 = X / 2 := by
    rw [hX]; ring
  rw [hA]

/-- The `matan`/`arctan` half of the sol bridge: after the `mi_p21e_euler`
reduction the right-hand side is `t * matan(D/(4*(X/2)^2))/(X/2)`, i.e.
`2*arctan(t/X)`, which is the complement of `pi - 2*arctan(X/t)`. -/
private theorem mi_p21e_soltrig (t X D : ℝ) (ht : 0 < t) (hX : 0 < X)
    (hD : D = t ^ 2) :
    Real.pi - 2 * Real.arctan (X / t)
      = t * (matan (D / (4 * (X / 2) ^ 2)) / (X / 2)) := by
  have harg : D / (4 * (X / 2) ^ 2) = (t / X) ^ 2 := by
    rw [hD]; field_simp; ring
  have hz : 0 < (t / X) ^ 2 := by positivity
  have hmat : matan ((t / X) ^ 2) = (X / t) * Real.arctan (t / X) := by
    rw [mi_p21e_matan _ hz]
    have hs : Real.sqrt ((t / X) ^ 2) = t / X :=
      Real.sqrt_sq (le_of_lt (div_pos ht hX))
    rw [hs]
    field_simp [ne_of_gt ht, ne_of_gt hX]
  have hcomp : Real.pi - 2 * Real.arctan (X / t) = 2 * Real.arctan (t / X) := by
    have h : Real.arctan ((X / t)⁻¹) = Real.pi / 2 - Real.arctan (X / t) :=
      Real.arctan_inv_of_pos (div_pos hX ht)
    have hinv : (X / t)⁻¹ = t / X := by field_simp
    rw [hinv] at h
    linarith
  rw [harg, hmat, hcomp]
  field_simp [ne_of_gt ht, ne_of_gt hX]

/-- The `matan`/`arctan` half of the dihedral bridge: `dih_x` written as
`pi/2 - arctan(d4/sqrt(4ad))` equals `sqrt(D)` times the posbranch formula
(valid on the `d4 > 0` branch). -/
private theorem mi_p21e_dihalg (a d d4 D : ℝ) (ha : 0 < a) (hd : 0 < d) (hd4 : 0 < d4)
    (hD : D = d) :
    Real.pi / 2 - Real.arctan (d4 / Real.sqrt (4 * a * d))
      = Real.sqrt D * (Real.sqrt (4 * a) / d4 * matan (4 * a * d / d4 ^ 2)) := by
  set z : ℝ := Real.sqrt (4 * a * d) / d4 with hzdef
  have harg : 0 < 4 * a * d / d4 ^ 2 := by positivity
  have hsqd : Real.sqrt (4 * a * d / d4 ^ 2) = z := by
    rw [hzdef, show 4 * a * d / d4 ^ 2 = (Real.sqrt (4 * a * d) / d4) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by positivity)]]
    exact Real.sqrt_sq (le_of_lt (by positivity : 0 < Real.sqrt (4 * a * d) / d4))
  have hmat : matan (4 * a * d / d4 ^ 2) = Real.arctan z / z := by
    rw [mi_p21e_matan _ harg, hsqd]
  have hcomp : Real.arctan z = Real.pi / 2 - Real.arctan (d4 / Real.sqrt (4 * a * d)) := by
    have h : Real.arctan ((d4 / Real.sqrt (4 * a * d))⁻¹)
        = Real.pi / 2 - Real.arctan (d4 / Real.sqrt (4 * a * d)) :=
      Real.arctan_inv_of_pos (div_pos hd4 (Real.sqrt_pos.mpr (by positivity)))
    have hinv : (d4 / Real.sqrt (4 * a * d))⁻¹ = z := by
      rw [hzdef]; field_simp
    rw [← h, hinv]
  rw [← hcomp, hmat, hD, hzdef]
  have hsq : Real.sqrt d * Real.sqrt (4 * a) = Real.sqrt (4 * a * d) := by
    rw [mul_comm]
    exact (Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * a) d).symm
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hd), ne_of_gt hd4]
  exact hsq.symm

/-- **The sol bridge** (EULER_TRIANGLE at the `(2,2,2)` pattern): the
spherical-excess form equals `sqrt(delta_x) * sol_euler_x_div_sqrtdelta`. -/
private theorem mi_p21e_sol_bridge (y1 y2 y3 : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ Real.sqrt 8)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ Real.sqrt 8) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ Real.sqrt 8)
    (het : eta_y y1 y2 y3 < Real.sqrt 2) :
    solY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y3
      = Real.sqrt (deltaX 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3))
        * solEulerXDivSqrtdelta (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3) := by
  set D : ℝ := -2 * y1 ^ 4 - y1 ^ 2 * y2 ^ 2 * y3 ^ 2 + 4 * y1 ^ 2 * y2 ^ 2
      + 4 * y1 ^ 2 * y3 ^ 2 - 2 * y2 ^ 4 + 4 * y2 ^ 2 * y3 ^ 2 - 2 * y3 ^ 4 with hD
  set t : ℝ := Real.sqrt D with ht
  set s : ℝ := Real.sqrt 2 with hs
  set X : ℝ := 2 * s * y1 * y2 + y1 * y2 ^ 2 + y1 ^ 2 * y2
      + s * (y1 ^ 2 + y2 ^ 2 - y3 ^ 2) with hX
  set E1 : ℝ := y1 ^ 2 * (y2 ^ 2 + y3 ^ 2 - y1 ^ 2) with hE1
  set E2 : ℝ := y2 ^ 2 * (y1 ^ 2 + y3 ^ 2 - y2 ^ 2) with hE2
  set E3 : ℝ := 4 * (y1 ^ 2 + y2 ^ 2 - y3 ^ 2) - y1 ^ 2 * y2 ^ 2 with hE3
  have hy1pos : 0 < y1 := by linarith
  have hy2pos : 0 < y2 := by linarith
  have hy3pos : 0 < y3 := by linarith
  have hDdelta : deltaX 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) = D := by
    rw [hD]; simp only [deltaX]; ring
  have hDpos : 0 < D := by
    rw [← hDdelta]
    exact mi_p21e_delta222_pos y1 y2 y3 hy1 hy1' hy2 hy2' hy3 hy3' het
  have htpos : 0 < t := by rw [ht]; exact Real.sqrt_pos.mpr hDpos
  have htd : t ^ 2 = D := by rw [ht]; exact Real.sq_sqrt (le_of_lt hDpos)
  have hs2 : s ^ 2 = 2 := by rw [hs]; exact Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨hlt1, hlt2, _⟩ :=
    mi_ETA_Y_LE_IMP_LT_ALL y1 y2 y3 hy1 hy1' hy2 hy2' hy3 hy3' het
  have h8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hu8 : y1 ^ 2 < 8 := by nlinarith [hlt1, hy1pos, h8]
  have hv8 : y2 ^ 2 < 8 := by nlinarith [hlt2, hy2pos, h8]
  have heta231 : eta_y y2 y3 y1 < Real.sqrt 2 := by
    have he : eta_y y1 y2 y3 = eta_y y2 y3 y1 := by
      rw [(mi_eta_y_sym y1 y2 y3).1, (mi_eta_y_sym y2 y1 y3).2]
    rwa [← he]
  have heta312 : eta_y y3 y1 y2 < Real.sqrt 2 := by
    have he : eta_y y1 y2 y3 = eta_y y3 y1 y2 := by
      rw [(mi_eta_y_sym y1 y2 y3).2, (mi_eta_y_sym y1 y3 y2).1]
    rwa [← he]
  have htri1 : y1 * y1 < y2 * y2 + y3 * y3 :=
    mi_p21e_tri y1 y2 y3 hy1 hy1' hy2 hy2' hy3 hy3' het
  have htri2 : y2 * y2 < y3 * y3 + y1 * y1 :=
    mi_p21e_tri y2 y3 y1 hy2 hy2' hy3 hy3' hy1 hy1' heta231
  have htri3 : y3 * y3 < y1 * y1 + y2 * y2 :=
    mi_p21e_tri y3 y1 y2 hy3 hy3' hy1 hy1' hy2 hy2' heta312
  have htri1' : y1 < y2 + y3 := by
    nlinarith [htri1, hy1pos, hy2pos, hy3pos, sq_nonneg (y1 - (y2 + y3))]
  have htri2' : y2 < y1 + y3 := by
    nlinarith [htri2, hy1pos, hy2pos, hy3pos, sq_nonneg (y2 - (y1 + y3))]
  have htri3' : y3 < y1 + y2 := by
    nlinarith [htri3, hy1pos, hy2pos, hy3pos, sq_nonneg (y3 - (y1 + y2))]
  have hbr : 0 < y1 ^ 2 + y2 ^ 2 - y3 ^ 2 := by linarith
  have hXpos : 0 < X := by
    rw [hX]
    have h1 : 0 < 2 * s * y1 * y2 := by positivity
    have h2 : 0 < y1 * y2 ^ 2 := by positivity
    have h3 : 0 < y1 ^ 2 * y2 := by positivity
    have h4 : 0 < s * (y1 ^ 2 + y2 ^ 2 - y3 ^ 2) := mul_pos hs0 hbr
    linarith
  have heuler := mi_p21e_euler y1 y2 y3 t s X E1 E2 E3 hy1pos hy2pos hy3pos
    hu8 hv8 htri1' htri2' htri3' htpos (htd.trans hD)
    (by rw [← hD]; exact hDpos) hs2 hs0 hE1 hE2 hE3 hX hXpos
  have hDa : deltaX (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3) = D := by
    rw [hD]; simp only [deltaX]; ring
  have hDb : deltaX (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2 = D := by
    rw [hD]; simp only [deltaX]; ring
  have hDc : deltaX 2 (y1 * y1) (y2 * y2) (y3 * y3) 2 2 = D := by
    rw [hD]; simp only [deltaX]; ring
  have hE1d : deltaX4 (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3) = E1 := by
    rw [hE1]; simp only [deltaX4]; ring
  have hE2d : deltaX4 (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2 = E2 := by
    rw [hE2]; simp only [deltaX4]; ring
  have hE3d : deltaX4 2 (y1 * y1) (y2 * y2) (y3 * y3) 2 2 = E3 := by
    rw [hE3]; simp only [deltaX4]; ring
  have hT1 : dihXf (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3)
      = Real.pi / 2 - Real.arctan (E1 / (2 * t * y1)) := by
    rw [mi_p21e_dih_atn (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3) (by positivity)
      (by rw [hDa]; exact hDpos)]
    rw [hE1d, hDa]
    have hsq : (4:ℝ) * (y1 * y1) * D = (2 * t * y1) ^ 2 := by
      rw [← htd]; ring
    rw [hsq, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * t * y1)]
  have hT2 : dihXf (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2
      = Real.pi / 2 - Real.arctan (E2 / (2 * t * y2)) := by
    rw [mi_p21e_dih_atn (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2 (by positivity)
      (by rw [hDb]; exact hDpos)]
    rw [hE2d, hDb]
    have hsq : (4:ℝ) * (y2 * y2) * D = (2 * t * y2) ^ 2 := by
      rw [← htd]; ring
    rw [hsq, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * t * y2)]
  have hT3 : dihXf 2 (y1 * y1) (y2 * y2) (y3 * y3) 2 2
      = Real.pi / 2 - Real.arctan (E3 / (2 * s * t)) := by
    rw [mi_p21e_dih_atn 2 (y1 * y1) (y2 * y2) (y3 * y3) 2 2 (by norm_num)
      (by rw [hDc]; exact hDpos)]
    rw [hE3d, hDc]
    have hs8 : (2 * s * t) ^ 2 = 8 * t ^ 2 := by
      calc (2 * s * t) ^ 2 = 4 * s ^ 2 * t ^ 2 := by ring
        _ = 8 * t ^ 2 := by rw [hs2]; ring
    have hsq : (4:ℝ) * 2 * D = (2 * s * t) ^ 2 := by
      rw [← htd, hs8]; ring
    rw [hsq, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * s * t)]
  have hsum : dihXf (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3)
      + dihXf (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2
      + dihXf 2 (y1 * y1) (y2 * y2) (y3 * y3) 2 2 - Real.pi
      = (Real.pi / 2 - Real.arctan (E1 / (2 * t * y1)))
        + (Real.pi / 2 - Real.arctan (E2 / (2 * t * y2)))
        + (Real.pi / 2 - Real.arctan (E3 / (2 * s * t))) - Real.pi := by
    rw [hT1, hT2, hT3]
  have hs2m : s * s = 2 := by rw [show s * s = s ^ 2 by ring, hs2]
  have hsol : solY y1 y2 s s s y3 = Real.pi - 2 * Real.arctan (X / t) := by
    simp only [solY, dihY]
    rw [hs2m, hsum, heuler]
  have hsE := mi_p21e_solE y1 y2 y3 s X D hy1pos hy2pos hX hs hs2 hDa
  rw [hsol, hDdelta, ← ht, hsE]
  exact mi_p21e_soltrig t X D htpos hXpos htd.symm

/-- **The dihedral bridge** at the `(2,2,2)` pattern: `dih_y` equals
`sqrt(delta_x) * dih_x_div_sqrtdelta_posbranch` at the slot-normalized
pattern. -/
private theorem mi_p21e_dih_bridge (y4 y5 y6 : ℝ) (hy4 : 2 ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ Real.sqrt 8) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ Real.sqrt 8)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    dihY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
  set a : ℝ := y4 * y4 with hA
  set b : ℝ := y5 * y5 with hB
  set c : ℝ := y6 * y6 with hC
  set s : ℝ := Real.sqrt 2 with hs
  have hy4pos : 0 < y4 := by linarith
  have hy5pos : 0 < y5 := by linarith
  have hy6pos : 0 < y6 := by linarith
  have hapos : 0 < a := by rw [hA]; positivity
  have hbpos : 0 < b := by rw [hB]; positivity
  have hcpos : 0 < c := by rw [hC]; positivity
  have hDpos : 0 < deltaX 2 2 2 a b c := by
    have h := mi_p21e_delta222_pos y4 y5 y6 hy4 hy4' hy5 hy5' hy6 hy6' het
    rwa [← hA, ← hB, ← hC] at h
  have htrib : a < b + c := by
    have h := mi_p21e_tri y4 y5 y6 hy4 hy4' hy5 hy5' hy6 hy6' het
    rwa [← hA, ← hB, ← hC] at h
  have hd : deltaX a 2 c 2 b 2 = deltaX 2 2 2 a b c := by
    simp only [deltaX]; ring
  have hdpos : 0 < deltaX a 2 c 2 b 2 := by rw [hd]; exact hDpos
  have hd4pos : 0 < deltaX4 a 2 c 2 b 2 := by
    rw [show deltaX4 a 2 c 2 b 2 = a * (b + c - a) by simp only [deltaX4]; ring]
    exact mul_pos hapos (by linarith)
  have hs2 : s * s = 2 := by rw [hs]; exact Real.mul_self_sqrt (by norm_num)
  have hL : dihY y4 y5 s s s y6 = dihXf a 2 c 2 b 2 := by
    rw [dihY, hs2, ← hA, ← hB, ← hC]
    exact mi_p21e_dihsym a b c
  have hT : dihXf a 2 c 2 b 2
      = Real.pi / 2 - Real.arctan
          (deltaX4 a 2 c 2 b 2 / Real.sqrt (4 * a * deltaX a 2 c 2 b 2)) :=
    mi_p21e_dih_atn a 2 c 2 b 2 hapos hdpos
  rw [hL, hT]
  unfold dihXDivSqrtdeltaPosbranch
  dsimp only
  exact mi_p21e_dihalg a (deltaX a 2 c 2 b 2) (deltaX4 a 2 c 2 b 2)
    (deltaX 2 2 2 a b c) hapos hdpos hd4pos hd.symm


/-- Pattern-swap for `sol_euler_x_div_sqrtdelta` at the two `(2,2,2)`
encodings of the same tetrahedron (`(y1²,y2²,2,2,2,y3²)` vs
`(y2²,2,y1²,2,y3²,2)`): both `delta_x` and the let-bound `a` coincide. -/
private theorem mi_solE_swap (y1 y2 y3 : ℝ) (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    solEulerXDivSqrtdelta (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3)
      = solEulerXDivSqrtdelta (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2 := by
  have hs1 : Real.sqrt (y1 * y1) = y1 := by
    rw [show y1 * y1 = y1 ^ 2 by ring, Real.sqrt_sq h1]
  have hs2 : Real.sqrt (y2 * y2) = y2 := by
    rw [show y2 * y2 = y2 ^ 2 by ring, Real.sqrt_sq h2]
  have hs12 : Real.sqrt ((y1 * y1) * (y2 * y2) * 2) = y1 * y2 * Real.sqrt 2 := by
    rw [show (y1 * y1) * (y2 * y2) * 2 = (y1 * y2) ^ 2 * 2 by ring,
      Real.sqrt_mul (sq_nonneg (y1 * y2)) 2, Real.sqrt_sq (mul_nonneg h1 h2)]
  have h21 : Real.sqrt ((y2 * y2) * 2 * (y1 * y1)) = y1 * y2 * Real.sqrt 2 := by
    rw [show (y2 * y2) * 2 * (y1 * y1) = (y1 * y2) ^ 2 * 2 by ring,
      Real.sqrt_mul (sq_nonneg (y1 * y2)) 2, Real.sqrt_sq (mul_nonneg h1 h2)]
  have hD : deltaX (y1 * y1) (y2 * y2) 2 2 2 (y3 * y3)
      = deltaX (y2 * y2) 2 (y1 * y1) 2 (y3 * y3) 2 := by
    simp only [deltaX]; ring
  have hA : y1 * y2 * Real.sqrt 2 + y1 * (y2 * y2 + 2 - 2) / 2
        + y2 * (y1 * y1 + 2 - 2) / 2 + Real.sqrt 2 * (y1 * y1 + y2 * y2 - y3 * y3) / 2
      = y1 * y2 * Real.sqrt 2 + y2 * (2 + y1 * y1 - 2) / 2
        + Real.sqrt 2 * (y2 * y2 + y1 * y1 - y3 * y3) / 2 + y1 * (y2 * y2 + 2 - 2) / 2 := by
    ring
  unfold solEulerXDivSqrtdelta
  dsimp only
  rw [hs1, hs2, hs12, h21]
  rw [hD, hA]

/-- Explicit unfolding of `gamma3fXDivSqrtdelta` at an arbitrary point
(the `mk456`/`rotate*`/`uni`/`scalar6` glue of nonlin_def.hl:349-363). -/
private theorem mi_gamma3fXDivSqrtdelta_unfold (m4 m5 m6 x1 x2 x3 x4 x5 x6 : ℝ) :
    gamma3fXDivSqrtdelta m4 m5 m6 x1 x2 x3 x4 x5 x6
      = 1 / 12
        - (2 * mm1 / Real.pi) * (solEulerXDivSqrtdelta x5 2 x4 2 x6 2
            + solEulerXDivSqrtdelta x6 2 x5 2 x4 2
            + solEulerXDivSqrtdelta x4 2 x6 2 x5 2)
        + (8 * mm2 / Real.pi) * (lfun (Real.sqrt x4 * 0.5) * m4
              * dihXDivSqrtdeltaPosbranch x4 2 x6 2 x5 2
            + lfun (Real.sqrt x5 * 0.5) * m5
              * dihXDivSqrtdeltaPosbranch x5 2 x4 2 x6 2
            + lfun (Real.sqrt x6 * 0.5) * m6
              * dihXDivSqrtdeltaPosbranch x6 2 x5 2 x4 2) := by
  simp only [gamma3fXDivSqrtdelta, scalar6, uni, mk456, compose6, projX4, projX5, projX6,
    projY4, projY5, projY6, constant6, two6, rotate4, rotate5, rotate6,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- Local copy of the `(2 3)(5 6)`-type `dihXf` slot symmetry (identical
statement to the file's later `mi_dihXf_sym2`; kept local to this section so
the item-9 assembly does not depend on declaration order). -/
private theorem mi_euler4_dihXf_sym2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    dihXf x1 x2 x3 x4 x5 x6 = dihXf x1 x5 x6 x4 x2 x3 := by
  have hd : deltaX x1 x5 x6 x4 x2 x3 = deltaX x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX]; ring
  have hd4 : deltaX4 x1 x5 x6 x4 x2 x3 = deltaX4 x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX4]; ring
  simp only [dihXf, hd, hd4]

/-- Local copy of the `solX` 3-cycle (identical statement to the file's later
`mi_solX_cycle`; the three `dihXf` summands just permute). -/
private theorem mi_euler4_solX_cycle (x1 x2 x3 x4 x5 x6 : ℝ) :
    solX x1 x2 x3 x4 x5 x6 = solX x2 x3 x1 x5 x6 x4 := by
  simp only [solX]
  ring

/-- HOL `gamma3f_gamma3f_x_div_sqrtdelta` (merge_ineq.hl:3292-3310).
Statement frozen for the wave 2b track-7 consumer.  PROVED (EULER lane 4)
by direct assembly instead of the absent `..._WEAK2`/`..._WEAK` route:
`gamma3f` unfolds over `vol3r`/`vol3f`; the three `solY` summands become
`solX` at the `mk456`-rotated `(y5²,2,y4²,2,y6²,2)`-type patterns
(`mi_euler4_solX_cycle`) and the three `dihY` summands become `dihXf`
(`mi_euler4_dihXf_sym2`).  The private bridge kit `mi_p21e_sol_bridge`/
`mi_p21e_dih_bridge` (copied verbatim from the green `P21EulerScratch`
lane, `mi_`-renamed per the §0' bridge-copy convention — the scratch module
imports this file, so no import edge is possible) supplies
`sol_x = sqrt(delta_x) * sol_euler_x_div_sqrtdelta` and
`dih_x = sqrt(delta_x) * dih_x_div_sqrtdelta_posbranch` at the `(2,2,2)`
pattern; the residual `solEulerXDivSqrtdelta` pattern mismatch is closed by
the pure-algebra `mi_solE_swap`, `lmfun` by `mi_lmfun_h0cut`, and the whole
by `mi_gamma3fXDivSqrtdelta_unfold` + `ring`. -/
theorem mi_gamma3f_gamma3f_x_div_sqrtdelta (a b c y4 y5 y6 : ℝ)
    (h4 : 2 ≤ y4) (h5 : 2 ≤ y5) (h6 : 2 ≤ y6) (h4' : y4 ≤ 2 * Real.sqrt 2)
    (h5' : y5 ≤ 2 * Real.sqrt 2) (h6' : y6 ≤ 2 * Real.sqrt 2)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    gamma3f y4 y5 y6 (Real.sqrt 2) lmfun
      = gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) (h0cut y6) a b c
          (y4 * y4) (y5 * y5) (y6 * y6)
        * Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6)) := by
  have hs2 : (Real.sqrt 2 * Real.sqrt 2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
  have h8a : y4 ≤ Real.sqrt 8 := by rw [mi_sqrt8_eq]; exact h4'
  have h8b : y5 ≤ Real.sqrt 8 := by rw [mi_sqrt8_eq]; exact h5'
  have h8c : y6 ≤ Real.sqrt 8 := by rw [mi_sqrt8_eq]; exact h6'
  have heta234 : eta_y y5 y6 y4 < Real.sqrt 2 := by
    have he : eta_y y4 y5 y6 = eta_y y5 y6 y4 := by
      rw [(mi_eta_y_sym y4 y5 y6).1, (mi_eta_y_sym y5 y4 y6).2]
    rwa [← he]
  have heta342 : eta_y y6 y4 y5 < Real.sqrt 2 := by
    have he : eta_y y4 y5 y6 = eta_y y6 y4 y5 := by
      rw [(mi_eta_y_sym y4 y5 y6).2, (mi_eta_y_sym y4 y6 y5).1]
    rwa [← he]
  have hS1 := mi_p21e_sol_bridge y4 y5 y6 h4 h8a h5 h8b h6 h8c het
  have hS2 := mi_p21e_sol_bridge y5 y6 y4 h5 h8b h6 h8c h4 h8a heta234
  have hS3 := mi_p21e_sol_bridge y6 y4 y5 h6 h8c h4 h8a h5 h8b heta342
  have hT1 := mi_p21e_dih_bridge y4 y5 y6 h4 h8a h5 h8b h6 h8c het
  have hT2 := mi_p21e_dih_bridge y5 y6 y4 h5 h8b h6 h8c h4 h8a heta234
  have hT3 := mi_p21e_dih_bridge y6 y4 y5 h6 h8c h4 h8a h5 h8b heta342
  have hp1 := mi_solE_swap y4 y5 y6 (by linarith) (by linarith)
  have hp2 := mi_solE_swap y5 y6 y4 (by linarith) (by linarith)
  have hp3 := mi_solE_swap y6 y4 y5 (by linarith) (by linarith)
  have hDc2 : deltaX 2 2 2 (y5 * y5) (y6 * y6) (y4 * y4)
      = deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [deltaX]; ring
  have hDc3 : deltaX 2 2 2 (y6 * y6) (y4 * y4) (y5 * y5)
      = deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [deltaX]; ring
  have hs4 : Real.sqrt (y4 * y4) = y4 := by
    rw [show y4 * y4 = y4 ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hs5 : Real.sqrt (y5 * y5) = y5 := by
    rw [show y5 * y5 = y5 ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hs6 : Real.sqrt (y6 * y6) = y6 := by
    rw [show y6 * y6 = y6 ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have e1 : solY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
      = solX (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    have h0 : solY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
        = solX (y4 * y4) (y5 * y5) (Real.sqrt 2 * Real.sqrt 2)
            (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y6 * y6) := rfl
    rw [h0, hs2]
    exact mi_euler4_solX_cycle (y4 * y4) (y5 * y5) 2 2 2 (y6 * y6)
  have e2 : solY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4
      = solX (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    have h0 : solY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4
        = solX (y5 * y5) (y6 * y6) (Real.sqrt 2 * Real.sqrt 2)
            (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y4 * y4) := rfl
    rw [h0, hs2]
    exact mi_euler4_solX_cycle (y5 * y5) (y6 * y6) 2 2 2 (y4 * y4)
  have e3 : solY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5
      = solX (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
    have h0 : solY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5
        = solX (y6 * y6) (y4 * y4) (Real.sqrt 2 * Real.sqrt 2)
            (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y5 * y5) := rfl
    rw [h0, hs2]
    exact mi_euler4_solX_cycle (y6 * y6) (y4 * y4) 2 2 2 (y5 * y5)
  have e4 : dihY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
      = dihXf (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
    show dihXf (y4 * y4) (y5 * y5) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y6 * y6) = _
    rw [hs2]
    exact mi_euler4_dihXf_sym2 (y4 * y4) (y5 * y5) 2 2 2 (y6 * y6)
  have e5 : dihY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4
      = dihXf (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    show dihXf (y5 * y5) (y6 * y6) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y4 * y4) = _
    rw [hs2]
    exact mi_euler4_dihXf_sym2 (y5 * y5) (y6 * y6) 2 2 2 (y4 * y4)
  have e6 : dihY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5
      = dihXf (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    show dihXf (y6 * y6) (y4 * y4) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y5 * y5) = _
    rw [hs2]
    exact mi_euler4_dihXf_sym2 (y6 * y6) (y4 * y4) 2 2 2 (y5 * y5)
  have hQ2 : solX (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    rw [← e1, hS1, hp1]
  have hQ3 : solX (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    rw [← e2, hS2, hDc2, hp2]
  have hQ1 : solX (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
    rw [← e3, hS3, hDc3, hp3]
  have hR1 : dihXf (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
    rw [← e4, hT1]
  have hR2 : dihXf (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    rw [← e5, hT2, hDc2]
  have hR3 : dihXf (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    rw [← e6, hT3, hDc3]
  have hvol : vol3r y4 y5 y6 (Real.sqrt 2)
      = volXf 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
    show volY (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 = _
    unfold volY
    rw [hs2]
  have hmain : gamma3f y4 y5 y6 (Real.sqrt 2) lmfun
      = Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6))
        * (1 / 12
          - (2 * mm1 / Real.pi) * (solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2
              + solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2
              + solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2)
          + (8 * mm2 / Real.pi) * (lfun (y4 / 2) * h0cut y4
                * dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2
              + lfun (y5 / 2) * h0cut y5
                * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2
              + lfun (y6 / 2) * h0cut y6
                * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2)) := by
    unfold gamma3f vol3f
    rw [e1, e2, e3, e4, e5, e6]
    rw [hvol]
    unfold volXf
    rw [mi_lmfun_h0cut y4, mi_lmfun_h0cut y5, mi_lmfun_h0cut y6]
    rw [hQ2, hQ3, hQ1, hR1, hR2, hR3]
    ring
  calc gamma3f y4 y5 y6 (Real.sqrt 2) lmfun
      = _ := hmain
    _ = gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) (h0cut y6) a b c
          (y4 * y4) (y5 * y5) (y6 * y6)
        * Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6)) := by
        rw [mi_gamma3fXDivSqrtdelta_unfold]
        rw [hs4, hs5, hs6]
        ring

end P21Euler4Kit

/-! ### Item 10: gamma3f_sym -/

/-- Klein-group symmetry of `dihXf` under `(2 3)(5 6)` (HOL `dih_x_sym`,
nonlinear_lemma.hl:481; polynomial identity level). -/
private theorem mi_dihXf_g1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    dihXf x1 x2 x3 x4 x5 x6 = dihXf x1 x3 x2 x4 x6 x5 := by
  have hd : deltaX x1 x3 x2 x4 x6 x5 = deltaX x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX]; ring
  have hd4 : deltaX4 x1 x3 x2 x4 x6 x5 = deltaX4 x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX4]; ring
  simp only [dihXf, hd, hd4]

/-- Klein-group symmetry of `dihXf` under `(2 6)(3 5)` (the composite
`g1∘g2` of the HOL `dih_x_sym`/`dih_x_sym2` maps, nonlinear_lemma.hl:481/
:493; polynomial identity level). -/
private theorem mi_dihXf_2635 (x1 x2 x3 x4 x5 x6 : ℝ) :
    dihXf x1 x2 x3 x4 x5 x6 = dihXf x1 x6 x5 x4 x3 x2 := by
  have hd : deltaX x1 x6 x5 x4 x3 x2 = deltaX x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX]; ring
  have hd4 : deltaX4 x1 x6 x5 x4 x3 x2 = deltaX4 x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX4]; ring
  simp only [dihXf, hd, hd4]

/-- The `(1 2)(4 5)`-slot symmetry of `solX` (HOL `sol_x_sym`/`sol_x_sym2`
composition, merge_ineq.hl:1111/:1122): each of the three `dihXf` terms of
the swapped sum is a `mi_dihXf_g1` image of an original term. -/
private theorem mi_solX_sym12 (x1 x2 x3 x4 x5 x6 : ℝ) :
    solX x1 x2 x3 x4 x5 x6 = solX x2 x1 x3 x5 x4 x6 := by
  have h1 : dihXf x2 x1 x3 x5 x4 x6 = dihXf x2 x3 x1 x5 x6 x4 :=
    mi_dihXf_g1 x2 x1 x3 x5 x4 x6
  have h2 : dihXf x1 x3 x2 x4 x6 x5 = dihXf x1 x2 x3 x4 x5 x6 :=
    mi_dihXf_g1 x1 x3 x2 x4 x6 x5
  have h3 : dihXf x3 x2 x1 x6 x5 x4 = dihXf x3 x1 x2 x6 x4 x5 :=
    mi_dihXf_g1 x3 x2 x1 x6 x5 x4
  show dihXf x1 x2 x3 x4 x5 x6 + dihXf x2 x3 x1 x5 x6 x4 + dihXf x3 x1 x2 x6 x4 x5 - Real.pi
      = dihXf x2 x1 x3 x5 x4 x6 + dihXf x1 x3 x2 x4 x6 x5 + dihXf x3 x2 x1 x6 x5 x4 - Real.pi
  rw [h1, h2, h3]
  ring

/-- HOL `gamma3f_sym` (merge_ineq.hl:3354-3388): `gamma3f` at the fixed
`sqrt 2` radius is symmetric under swapping its last two length arguments
and under the 3-cycle.  The vol/sol/dihedral summands match term-wise via
the polynomial slot symmetries (`mi_dihXf_g1`, `mi_dihXf_2635`,
`mi_solX_sym12`) plus commutativity. -/
theorem mi_gamma3f_sym (y4 y5 y6 : ℝ) :
    gamma3f y4 y5 y6 (Real.sqrt 2) lmfun = gamma3f y4 y6 y5 (Real.sqrt 2) lmfun ∧
      gamma3f y4 y5 y6 (Real.sqrt 2) lmfun = gamma3f y5 y6 y4 (Real.sqrt 2) lmfun := by
  have hV : vol3r y4 y5 y6 (Real.sqrt 2) = vol3r y4 y6 y5 (Real.sqrt 2) := by
    unfold vol3r volY volXf
    congr 1
    simp only [deltaX]; ring
  have hV2 : vol3r y4 y5 y6 (Real.sqrt 2) = vol3r y5 y6 y4 (Real.sqrt 2) := by
    unfold vol3r volY volXf
    congr 1
    simp only [deltaX]; ring
  have hS : ∀ a b c : ℝ,
      solY a b (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) c
        + solY b c (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) a
        + solY c a (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) b
      = solY a c (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) b
        + solY c b (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) a
        + solY b a (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) c := by
    intro a b c
    have e1 : ∀ u v w : ℝ, solY u v (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) w
        = solY v u (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) w := fun u v w =>
      mi_solX_sym12 (u * u) (v * v) (Real.sqrt 2 * Real.sqrt 2)
        (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (w * w)
    rw [e1 a c b, e1 c b a, e1 b a c]
    ring
  have hD : ∀ a b c : ℝ,
      lmfun (a / 2) * dihY a b (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) c
        + lmfun (b / 2) * dihY b c (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) a
        + lmfun (c / 2) * dihY c a (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) b
      = lmfun (a / 2) * dihY a c (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) b
        + lmfun (c / 2) * dihY c b (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) a
        + lmfun (b / 2) * dihY b a (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) c := by
    intro a b c
    have e1 : ∀ u v w : ℝ, dihY u v (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) w
        = dihY u w (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) v := fun u v w =>
      mi_dihXf_2635 (u * u) (v * v) (Real.sqrt 2 * Real.sqrt 2)
        (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (w * w)
    rw [e1 a b c, e1 c b a, e1 b a c]
    ring
  constructor
  · show vol3r y4 y5 y6 (Real.sqrt 2) - vol3f y4 y5 y6 (Real.sqrt 2) lmfun
        = vol3r y4 y6 y5 (Real.sqrt 2) - vol3f y4 y6 y5 (Real.sqrt 2) lmfun
    unfold vol3f
    rw [hV, hS y4 y5 y6, hD y4 y5 y6]
  · show vol3r y4 y5 y6 (Real.sqrt 2) - vol3f y4 y5 y6 (Real.sqrt 2) lmfun
        = vol3r y5 y6 y4 (Real.sqrt 2) - vol3f y5 y6 y4 (Real.sqrt 2) lmfun
    unfold vol3f
    rw [hV2]
    ring

/-! ### Item 11: REAL_WLOG_SIMPLEX_3d -/

/-- HOL `REAL_WLOG_SIMPLEX_3d` (merge_ineq.hl:3412-3425): the symmetry
reduction for 3-argument predicates.  The HOL boolean-equality hypotheses
are rendered as `Iff` (standard HOL→Lean encoding); the six linear orders
are discharged by hand (charter §6.8; no wlog plumbing needed at this
size). -/
theorem mi_REAL_WLOG_SIMPLEX_3d {P : ℝ → ℝ → ℝ → Prop}
    (h1 : ∀ y4 y5 y6 : ℝ, P y4 y5 y6 ↔ P y4 y6 y5)
    (h2 : ∀ y4 y5 y6 : ℝ, P y4 y5 y6 ↔ P y5 y6 y4)
    (h3 : ∀ y4 y5 y6 : ℝ, y6 ≤ y5 → y5 ≤ y4 → P y4 y5 y6)
    (y4 y5 y6 : ℝ) : P y4 y5 y6 := by
  rcases le_total y5 y4 with h54 | h45
  · rcases le_total y6 y5 with h65 | h56
    · exact h3 y4 y5 y6 h65 h54
    · rcases le_total y6 y4 with h64 | h46
      · rw [h1]; exact h3 y4 y6 y5 h56 h64
      · rw [h2, h2]; exact h3 y6 y4 y5 h54 h46
  · rcases le_total y6 y5 with h65 | h56
    · rcases le_total y6 y4 with h64 | h46
      · rw [h2, h1]; exact h3 y5 y4 y6 h64 h45
      · rw [h2]; exact h3 y5 y6 y4 h46 h65
    · rw [h2, h2, h1]; exact h3 y6 y5 y4 h45 h56

/-! ## MERGE-INEQ wave 2c: the lindihpi / gamma3_x channel

The merge_ineq.hl items consumed by PackingAuto25's
`IXPOTPA_MERGED`/`TXQTPVC_MERGED`/`TEWNSCJ_MERGED` (OXLZLEZ3.hl:8484/8572/8623):
`lindihpi_lt` (:2709-2734) / `lindihpi_gt` (:2735-2760) x-space cores,
`dih_gt_pi2` (:2761-2782), the y-space variants `lindihpi_lt_y` (:2783-2824) /
`lindihpi_gt_y` (:2825-2866) stated in the `bank_IXPOTPA` `yOfX` spelling, and
`gamma3_x_gamma3f` (:4101-4126).  The atn2 quadrant analysis follows
`Trigonometry1.ATN2_BREAKDOWN` (trig1.hl:341-353); the tan/arctan monotone
bridge is Mathlib `strictMonoOn_tan` + `tan_arctan`.  The same-root
`lp_details` variants on the LocalAuto11 lane (`lindihpi_lt_small_p11`, the
`delta_x4 > 0` quadrant) stay on that lane's own debt registry. -/

/-- HOL `Trigonometry1.ATN2_BREAKDOWN` first clause (trig1.hl:341-353): on
the positive-argument half-plane `atn2` is the plain arctangent of the
slope. -/
private theorem mi_atn2_pos_x {x y : ℝ} (hx : 0 < x) :
    atn2 x y = Real.arctan (y / x) := by
  rw [atn2]
  by_cases h1 : |y| < x
  · rw [if_pos h1]
  · rw [if_neg h1]
    rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [if_neg (show ¬(0 : ℝ) < y from by linarith), if_pos hy]
      have hxy : x / y < 0 := by
        have h2 : x / y = -(x / (-y)) := by field_simp
        rw [h2, neg_lt_zero]
        exact div_pos hx (neg_pos.mpr hy)
      have hinv := Real.arctan_inv_of_neg hxy
      rw [inv_div] at hinv
      exact hinv.symm
    · exact absurd (show |y| < x by rw [hy]; simpa using hx) h1
    · rw [if_pos hy]
      have hinv := Real.arctan_inv_of_pos (div_pos hy hx)
      rw [inv_div] at hinv
      linarith

/-- HOL `Trigonometry1.ATN2_BREAKDOWN` second clause (trig1.hl:341-353). -/
private theorem mi_atn2_pos_y {x y : ℝ} (hy : 0 < y) :
    atn2 x y = Real.pi / 2 - Real.arctan (x / y) := by
  rw [atn2]
  by_cases h1 : |y| < x
  · rw [if_pos h1]
    have hx : 0 < x := by linarith [le_abs_self y]
    have hinv := Real.arctan_inv_of_pos (div_pos hy hx)
    rw [inv_div] at hinv
    linarith
  · rw [if_neg h1, if_pos hy]

/-- HOL `dih_gt_pi2` (merge_ineq.hl:2761-2782). -/
theorem mi_dih_gt_pi2 {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hdih : Real.pi / 2 < dihXf x1 x2 x3 x4 x5 x6) :
    deltaX4 x1 x2 x3 x4 x5 x6 < 0 := by
  have hsqrt : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  have h0 : 0 < atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6)) := by
    have hdih' : Real.pi / 2 < Real.pi / 2 + atn2
        (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        (-(deltaX4 x1 x2 x3 x4 x5 x6)) := hdih
    linarith
  rw [mi_atn2_pos_x hsqrt] at h0
  rcases div_pos_iff.mp (Real.arctan_pos.mp h0) with ⟨hpos, -⟩ | ⟨-, hneg⟩
  · linarith
  · linarith [hsqrt]

/-- The slot symmetry of `dihXf` used by the `lindihpi` line (HOL
`Nonlinear_lemma.dih_x_sym2`, nonlinear_lemma.hl:493-505; polynomial
identity level). -/
private theorem mi_dihXf_sym2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    dihXf x1 x2 x3 x4 x5 x6 = dihXf x1 x5 x6 x4 x2 x3 := by
  have hd : deltaX x1 x5 x6 x4 x2 x3 = deltaX x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX]; ring
  have hd4 : deltaX4 x1 x5 x6 x4 x2 x3 = deltaX4 x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX4]; ring
  simp only [dihXf, hd, hd4]

/-- The 3-cycle slot symmetry of `solX` (HOL `sol_x_sym2`,
merge_ineq.hl:1122-1131; the three `dihXf` summands permute, so this is
plain commutativity). -/
private theorem mi_solX_cycle (x1 x2 x3 x4 x5 x6 : ℝ) :
    solX x1 x2 x3 x4 x5 x6 = solX x2 x3 x1 x5 x6 x4 := by
  simp only [solX]
  ring

/-- HOL `lindihpi_lt` (merge_ineq.hl:2709-2734). -/
theorem mi_lindihpi_lt {u x1 x2 x3 x4 x5 x6 : ℝ} (hu : |u| < Real.pi / 2)
    (h1 : 0 < x1) (hd4 : deltaX4 x1 x2 x3 x4 x5 x6 < 0) :
    (dihXf x1 x2 x3 x4 x5 x6 < Real.pi - u ↔
      -(Real.tan u) * deltaX4 x1 x2 x3 x4 x5 x6
        < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) := by
  have htpos : 0 < -(deltaX4 x1 x2 x3 x4 x5 x6) := by linarith
  have hbreak : dihXf x1 x2 x3 x4 x5 x6
      = Real.pi - Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6)) := by
    show Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6))
      = Real.pi - Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6))
    rw [mi_atn2_pos_y htpos]
    ring
  have hu_mem : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [abs_lt.mp hu], by linarith [abs_lt.mp hu]⟩
  have hmono : Real.tan u
      < Real.tan (Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6))) ↔
      u < Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6)) :=
    Real.strictMonoOn_tan.lt_iff_lt hu_mem (Real.arctan_mem_Ioo _)
  rw [Real.tan_arctan] at hmono
  have hbridge : Real.tan u * -(deltaX4 x1 x2 x3 x4 x5 x6)
      = -(Real.tan u) * deltaX4 x1 x2 x3 x4 x5 x6 := by ring
  constructor
  · intro hlt
    rw [hbreak] at hlt
    have h2 := hmono.mpr (by linarith)
    have h3 := (lt_div_iff₀ htpos).mp h2
    rw [← hbridge]
    exact h3
  · intro hR
    have h3 : Real.tan u * -(deltaX4 x1 x2 x3 x4 x5 x6)
        < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
      rw [hbridge]
      exact hR
    have h2 := (lt_div_iff₀ htpos).mpr h3
    rw [hbreak]
    linarith [hmono.mp h2]

/-- HOL `lindihpi_gt` (merge_ineq.hl:2735-2760). -/
theorem mi_lindihpi_gt {u x1 x2 x3 x4 x5 x6 : ℝ} (hu : |u| < Real.pi / 2)
    (h1 : 0 < x1) (hd4 : deltaX4 x1 x2 x3 x4 x5 x6 < 0) :
    (Real.pi - u < dihXf x1 x2 x3 x4 x5 x6 ↔
      Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        < -(Real.tan u) * deltaX4 x1 x2 x3 x4 x5 x6) := by
  have htpos : 0 < -(deltaX4 x1 x2 x3 x4 x5 x6) := by linarith
  have hbreak : dihXf x1 x2 x3 x4 x5 x6
      = Real.pi - Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6)) := by
    show Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6))
      = Real.pi - Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6))
    rw [mi_atn2_pos_y htpos]
    ring
  have hu_mem : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [abs_lt.mp hu], by linarith [abs_lt.mp hu]⟩
  have hmono : Real.tan u
      < Real.tan (Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6))) ↔
      u < Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6)) :=
    Real.strictMonoOn_tan.lt_iff_lt hu_mem (Real.arctan_mem_Ioo _)
  rw [Real.tan_arctan] at hmono
  have hmono2 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        / -(deltaX4 x1 x2 x3 x4 x5 x6) < Real.tan u ↔
      Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6)) < u := by
    have h := Real.strictMonoOn_tan.lt_iff_lt
      (Real.arctan_mem_Ioo (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          / -(deltaX4 x1 x2 x3 x4 x5 x6))) hu_mem
    rw [Real.tan_arctan] at h
    exact h
  have hbridge : Real.tan u * -(deltaX4 x1 x2 x3 x4 x5 x6)
      = -(Real.tan u) * deltaX4 x1 x2 x3 x4 x5 x6 := by ring
  constructor
  · intro hlt
    rw [hbreak] at hlt
    have h2 := hmono2.mpr (by linarith)
    have h3 := (div_lt_iff₀ htpos).mp h2
    rw [← hbridge]
    exact h3
  · intro hR
    have h3 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        < Real.tan u * -(deltaX4 x1 x2 x3 x4 x5 x6) := by
      rw [hbridge]
      exact hR
    have h2 := (div_lt_iff₀ htpos).mpr h3
    rw [hbreak]
    linarith [hmono2.mp h2]

/-- The squared-form bridge of the `lindihpi_y` line: `-(a)·delta4_y <
sqrt(4·y1²·delta_y)` (both sides nonnegative) iff `a²·delta4_y² <
4·y1²·delta_y` — the squaring step of HOL `lindihpi_lt_y`
(merge_ineq.hl:2783-2824, via `SQRT_POW_2` + `LT_POW2_EQ_LT`). -/
private theorem mi_lindihpi_y_bridge {a y1 y2 y3 y4 y5 y6 : ℝ} (ha : 0 < a)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hd4 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    (-(a) * delta4Y y1 y2 y3 y4 y5 y6
        < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)) ↔
    a ^ 2 * delta4Y y1 y2 y3 y4 y5 y6 ^ 2
      < 4 * (y1 * y1 * deltaY y1 y2 y3 y4 y5 y6) := by
  have hprod : (-(a) * delta4Y y1 y2 y3 y4 y5 y6) ^ 2
      = a ^ 2 * delta4Y y1 y2 y3 y4 y5 y6 ^ 2 := by ring
  have hA : 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6
      = 4 * (y1 * y1 * deltaY y1 y2 y3 y4 y5 y6) := by ring
  have hA0 : 0 ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
    nlinarith [hd]
  have hpos : 0 < -(a) * delta4Y y1 y2 y3 y4 y5 y6 := by nlinarith
  constructor
  · intro h0
    have hsq : (-(a) * delta4Y y1 y2 y3 y4 y5 y6) ^ 2
        < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) ^ 2 :=
      sq_lt_sq'
        (by linarith [Real.sqrt_nonneg (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)])
        h0
    rw [Real.sq_sqrt hA0, hA, hprod] at hsq
    exact hsq
  · intro h
    have h2 : (-(a) * delta4Y y1 y2 y3 y4 y5 y6) ^ 2
        < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) ^ 2 := by
      rw [hprod, Real.sq_sqrt hA0, hA]
      exact h
    exact (abs_lt_of_sq_lt_sq' h2 (Real.sqrt_nonneg _)).2

/-- HOL `lindihpi_lt_y` (merge_ineq.hl:2783-2824), stated in the
`bank_IXPOTPA` `yOfX` spelling. -/
theorem mi_lindihpi_lt_y {a y1 y2 y3 y4 y5 y6 : ℝ} (hy1 : 0 < y1) (ha : 0 < a)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hd4 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    (dihY y1 y2 y3 y4 y5 y6 < Real.pi - Real.arctan a ↔
      a ^ 2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6
        < 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6) := by
  have hx1 : 0 < y1 * y1 := by positivity
  have hcore := mi_lindihpi_lt (u := Real.arctan a)
    (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan a, Real.arctan_lt_pi_div_two a⟩)
    hx1 hd4
  rw [Real.tan_arctan] at hcore
  have hcore' : (dihY y1 y2 y3 y4 y5 y6 < Real.pi - Real.arctan a ↔
      -(a) * delta4Y y1 y2 y3 y4 y5 y6
        < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)) := hcore
  constructor
  · intro h
    exact (mi_lindihpi_y_bridge ha hy1 hd hd4).mp (hcore'.mp h)
  · intro h
    exact hcore'.mpr ((mi_lindihpi_y_bridge ha hy1 hd hd4).mpr h)

/-- The mirrored squared-form bridge for the `lindihpi_gt_y` line. -/
private theorem mi_lindihpi_y_bridge_gt {a y1 y2 y3 y4 y5 y6 : ℝ} (ha : 0 < a)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hd4 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)
        < -(a) * delta4Y y1 y2 y3 y4 y5 y6) ↔
    4 * (y1 * y1 * deltaY y1 y2 y3 y4 y5 y6)
      < a ^ 2 * delta4Y y1 y2 y3 y4 y5 y6 ^ 2 := by
  have hprod : (-(a) * delta4Y y1 y2 y3 y4 y5 y6) ^ 2
      = a ^ 2 * delta4Y y1 y2 y3 y4 y5 y6 ^ 2 := by ring
  have hA : 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6
      = 4 * (y1 * y1 * deltaY y1 y2 y3 y4 y5 y6) := by ring
  have hA0 : 0 ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
    nlinarith [hd]
  have hpos : 0 < -(a) * delta4Y y1 y2 y3 y4 y5 y6 := by nlinarith
  constructor
  · intro h0
    have hsq : Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) ^ 2
        < (-(a) * delta4Y y1 y2 y3 y4 y5 y6) ^ 2 :=
      sq_lt_sq'
        (by linarith [Real.sqrt_nonneg (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)])
        h0
    rw [Real.sq_sqrt hA0, hprod, hA] at hsq
    exact hsq
  · intro h
    have h2 : Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) ^ 2
        < (-(a) * delta4Y y1 y2 y3 y4 y5 y6) ^ 2 := by
      rw [Real.sq_sqrt hA0, hprod, hA]
      exact h
    exact (abs_lt_of_sq_lt_sq' h2 hpos.le).2

/-- HOL `lindihpi_gt_y` (merge_ineq.hl:2825-2866), stated in the
`bank_IXPOTPA` `yOfX` spelling. -/
theorem mi_lindihpi_gt_y {a y1 y2 y3 y4 y5 y6 : ℝ} (hy1 : 0 < y1) (ha : 0 < a)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hd4 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    (Real.pi - Real.arctan a < dihY y1 y2 y3 y4 y5 y6 ↔
      4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6
        < a ^ 2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6) := by
  have hx1 : 0 < y1 * y1 := by positivity
  have hcore := mi_lindihpi_gt (u := Real.arctan a)
    (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan a, Real.arctan_lt_pi_div_two a⟩)
    hx1 hd4
  rw [Real.tan_arctan] at hcore
  have hcore' : (Real.pi - Real.arctan a < dihY y1 y2 y3 y4 y5 y6 ↔
      Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)
        < -(a) * delta4Y y1 y2 y3 y4 y5 y6) := hcore
  constructor
  · intro h
    exact (mi_lindihpi_y_bridge_gt ha hd hd4).mp (hcore'.mp h)
  · intro h
    exact hcore'.mpr ((mi_lindihpi_y_bridge_gt ha hd hd4).mpr h)

/-- Named projection of rest entry 7 `bank_IXPOTPA`
(PackingAuto25 `IXPOTPA_MERGED` consumer). -/
theorem proj_bank_IXPOTPA (h : pack_nonlinear_non_ox3q1h) : bank_IXPOTPA :=
  h.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 8 `bank_TXQTPVC`
(PackingAuto25 `TXQTPVC_MERGED` consumer). -/
theorem proj_bank_TXQTPVC (h : pack_nonlinear_non_ox3q1h) : bank_TXQTPVC :=
  h.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 12 `bank_TEWNSCJ`
(PackingAuto25 `TEWNSCJ_MERGED` consumer). -/
theorem proj_bank_TEWNSCJ (h : pack_nonlinear_non_ox3q1h) : bank_TEWNSCJ :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 1 `bank_6096597438b`
(HOL ineq entry `6096597438 b` (ineq.hl:1661)). -/
theorem proj_bank_6096597438b (h : pack_nonlinear_non_ox3q1h) : bank_6096597438b :=
  h.2.2.2.1

/-- Named projection of rest entry 2 `bank_6096597438a`
(HOL ineq entry `6096597438 a` (ineq.hl:1650)). -/
theorem proj_bank_6096597438a (h : pack_nonlinear_non_ox3q1h) : bank_6096597438a :=
  h.2.2.2.2.1

/-- Named projection of rest entry 3 `bank_1965189142a`
(HOL ineq entry `1965189142 a` (ineq.hl:1598)). -/
theorem proj_bank_1965189142a (h : pack_nonlinear_non_ox3q1h) : bank_1965189142a :=
  h.2.2.2.2.2.1

/-- Named projection of rest entry 4 `bank_1965189142x34`
(HOL ineq entry `1965189142 34` (ineq.hl:1587)). -/
theorem proj_bank_1965189142x34 (h : pack_nonlinear_non_ox3q1h) : bank_1965189142x34 :=
  h.2.2.2.2.2.2.1

/-- Named projection of rest entry 5 `bank_JSPEVYT`
(HOL ineq entry `JSPEVYT` (ineq.hl:1495)). -/
theorem proj_bank_JSPEVYT (h : pack_nonlinear_non_ox3q1h) : bank_JSPEVYT :=
  h.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 6 `bank_QITNPEA4003532128a`
(HOL ineq entry `QITNPEA 4003532128 a` (ineq.hl:1290)). -/
theorem proj_bank_QITNPEA4003532128a (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA4003532128a :=
  h.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 9 `bank_QITNPEA3725403817`
(HOL ineq entry `QITNPEA 3725403817` (ineq.hl:1221)). -/
theorem proj_bank_QITNPEA3725403817 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA3725403817 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 10 `bank_QITNPEAv24003532128`
(HOL ineq entry `QITNPEAv2 4003532128` (ineq.hl:1193)). -/
theorem proj_bank_QITNPEAv24003532128 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEAv24003532128 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 11 `bank_PEMKWU`
(HOL ineq entry `PEMKWKU` (ineq.hl:1169)). -/
theorem proj_bank_PEMKWU (h : pack_nonlinear_non_ox3q1h) : bank_PEMKWU :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 13 `bank_QITNPEA5400790175b`
(HOL ineq entry `QITNPEA 5400790175 b` (ineq.hl:1121)). -/
theorem proj_bank_QITNPEA5400790175b (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA5400790175b :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 14 `bank_QITNPEA5400790175a`
(HOL ineq entry `QITNPEA 5400790175 a` (ineq.hl:1103)). -/
theorem proj_bank_QITNPEA5400790175a (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA5400790175a :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 15 `bank_QITNPEA3848804089`
(HOL ineq entry `QITNPEA 3848804089` (ineq.hl:1059)). -/
theorem proj_bank_QITNPEA3848804089 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA3848804089 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 16 `bank_QITNPEA5814748276`
(HOL ineq entry `QITNPEA 5814748276` (ineq.hl:1041)). -/
theorem proj_bank_QITNPEA5814748276 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA5814748276 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 17 `bank_QITNPEA6206775865`
(HOL ineq entry `QITNPEA 6206775865` (ineq.hl:1023)). -/
theorem proj_bank_QITNPEA6206775865 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA6206775865 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 18 `bank_QITNPEA5653753305`
(HOL ineq entry `QITNPEA 5653753305` (ineq.hl:1004)). -/
theorem proj_bank_QITNPEA5653753305 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA5653753305 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 19 `bank_BIXPCGW9455898160`
(HOL ineq entry `BIXPCGW 9455898160` (ineq.hl:985)). -/
theorem proj_bank_BIXPCGW9455898160 (h : pack_nonlinear_non_ox3q1h) : bank_BIXPCGW9455898160 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 20 `bank_FWGKMBZ`
(HOL ineq entry `FWGKMBZ` (ineq.hl:967)). -/
theorem proj_bank_FWGKMBZ (h : pack_nonlinear_non_ox3q1h) : bank_FWGKMBZ :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 21 `bank_FHBVYXZb`
(HOL ineq entry `FHBVYXZ b` (ineq.hl:942)). -/
theorem proj_bank_FHBVYXZb (h : pack_nonlinear_non_ox3q1h) : bank_FHBVYXZb :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 22 `bank_FHBVYXZa`
(HOL ineq entry `FHBVYXZ a` (ineq.hl:914)). -/
theorem proj_bank_FHBVYXZa (h : pack_nonlinear_non_ox3q1h) : bank_FHBVYXZa :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 23 `bank_FHBVYXZv2a`
(HOL ineq entry `FHBVYXZv2 a` (ineq.hl:888)). -/
theorem proj_bank_FHBVYXZv2a (h : pack_nonlinear_non_ox3q1h) : bank_FHBVYXZv2a :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 24 `bank_QITNPEA2134082733`
(HOL ineq entry `QITNPEA 2134082733` (ineq.hl:864)). -/
theorem proj_bank_QITNPEA2134082733 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA2134082733 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 25 `bank_QITNPEA1_2_2`
(HOL idv `QITNPEA1 2 2 9063653052 A` (ineq.hl:845-862 loop)). -/
theorem proj_bank_QITNPEA1_2_2 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA1_2_2 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 26 `bank_QITNPEA1_2_1`
(HOL idv `QITNPEA1 2 1 9063653052 A` (ineq.hl:845-862 loop)). -/
theorem proj_bank_QITNPEA1_2_1 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA1_2_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 27 `bank_QITNPEA1_2_0`
(HOL idv `QITNPEA1 2 0 9063653052 A` (ineq.hl:845-862 loop)). -/
theorem proj_bank_QITNPEA1_2_0 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA1_2_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 28 `bank_QITNPEA1_1_2`
(HOL idv `QITNPEA1 1 2 9063653052 A` (ineq.hl:845-862 loop)). -/
theorem proj_bank_QITNPEA1_1_2 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA1_1_2 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 29 `bank_QITNPEA1_1_1`
(HOL idv `QITNPEA1 1 1 9063653052 A` (ineq.hl:845-862 loop)). -/
theorem proj_bank_QITNPEA1_1_1 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA1_1_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 30 `bank_QITNPEA1_1_0`
(HOL idv `QITNPEA1 1 0 9063653052 A` (ineq.hl:845-862 loop)). -/
theorem proj_bank_QITNPEA1_1_0 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA1_1_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 31 `bank_QITNPEA9939613598`
(HOL ineq entry `QITNPEA 9939613598` (ineq.hl:798)). -/
theorem proj_bank_QITNPEA9939613598 (h : pack_nonlinear_non_ox3q1h) : bank_QITNPEA9939613598 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 32 `bank_BIXPCGW7274157868a`
(HOL ineq entry `BIXPCGW 7274157868 a` (ineq.hl:776)). -/
theorem proj_bank_BIXPCGW7274157868a (h : pack_nonlinear_non_ox3q1h) : bank_BIXPCGW7274157868a :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 33 `bank_BIXPCGWb`
(HOL ineq entry `BIXPCGW b` (ineq.hl:758)). -/
theorem proj_bank_BIXPCGWb (h : pack_nonlinear_non_ox3q1h) : bank_BIXPCGWb :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 34 `bank_BIXPCGW1738910218a2`
(HOL ineq entry `BIXPCGW 1738910218 a2` (ineq.hl:739)). -/
theorem proj_bank_BIXPCGW1738910218a2 (h : pack_nonlinear_non_ox3q1h) : bank_BIXPCGW1738910218a2 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 35 `bank_BIXPCGW7080972881a2`
(HOL ineq entry `BIXPCGW 7080972881 a2` (ineq.hl:721)). -/
theorem proj_bank_BIXPCGW7080972881a2 (h : pack_nonlinear_non_ox3q1h) : bank_BIXPCGW7080972881a2 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 36 `bank_BIXPCGW6652007036a2`
(HOL ineq entry `BIXPCGW 6652007036 a2` (ineq.hl:701)). -/
theorem proj_bank_BIXPCGW6652007036a2 (h : pack_nonlinear_non_ox3q1h) : bank_BIXPCGW6652007036a2 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 37 `bank_GLFVCVK4y4subcrit`
(HOL ineq entry `GLFVCVK4 2477216213 y4subcrit` (ineq.hl:675)). -/
theorem proj_bank_GLFVCVK4y4subcrit (h : pack_nonlinear_non_ox3q1h) : bank_GLFVCVK4y4subcrit :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 38 `bank_GLFVCVK4y4supercrit`
(HOL ineq entry `GLFVCVK4 2477216213 y4supercrit` (ineq.hl:649)). -/
theorem proj_bank_GLFVCVK4y4supercrit (h : pack_nonlinear_non_ox3q1h) : bank_GLFVCVK4y4supercrit :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 39 `bank_GLFVCVK4y4crit`
(HOL ineq entry `GLFVCVK4 2477216213 y4crit` (ineq.hl:623)). -/
theorem proj_bank_GLFVCVK4y4crit (h : pack_nonlinear_non_ox3q1h) : bank_GLFVCVK4y4crit :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 40 `bank_GLFVCVK4a8328676778`
(HOL ineq entry `GLFVCVK4a 8328676778` (ineq.hl:586)). -/
theorem proj_bank_GLFVCVK4a8328676778 (h : pack_nonlinear_non_ox3q1h) : bank_GLFVCVK4a8328676778 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 41 `bank_GLFVCVK4`
(HOL ineq entry `GLFVCVK4 2477216213` (ineq.hl:559)). -/
theorem proj_bank_GLFVCVK4 (h : pack_nonlinear_non_ox3q1h) : bank_GLFVCVK4 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 42 `bank_MKFKQWUhalfwt`
(HOL ineq entry `MKFKQWU halfwt` (ineq.hl:523)). -/
theorem proj_bank_MKFKQWUhalfwt (h : pack_nonlinear_non_ox3q1h) : bank_MKFKQWUhalfwt :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 43 `bank_MKFKQWU`
(HOL ineq entry `MKFKQWU` (ineq.hl:502)). -/
theorem proj_bank_MKFKQWU (h : pack_nonlinear_non_ox3q1h) : bank_MKFKQWU :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 44 `bank_ZTGIJCF4_1_1_1_1`
(HOL idv `ZTGIJCF4 1 1 1 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_1_1_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_1_1_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 45 `bank_ZTGIJCF4_1_1_1_0`
(HOL idv `ZTGIJCF4 1 1 1 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_1_1_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_1_1_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 46 `bank_ZTGIJCF4_1_1_0_1`
(HOL idv `ZTGIJCF4 1 1 0 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_1_0_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_1_0_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 47 `bank_ZTGIJCF4_1_1_0_0`
(HOL idv `ZTGIJCF4 1 1 0 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_1_0_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_1_0_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 48 `bank_ZTGIJCF4_1_0_1_1`
(HOL idv `ZTGIJCF4 1 0 1 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_0_1_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_0_1_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 49 `bank_ZTGIJCF4_1_0_1_0`
(HOL idv `ZTGIJCF4 1 0 1 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_0_1_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_0_1_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 50 `bank_ZTGIJCF4_1_0_0_1`
(HOL idv `ZTGIJCF4 1 0 0 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_0_0_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_0_0_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 51 `bank_ZTGIJCF4_1_0_0_0`
(HOL idv `ZTGIJCF4 1 0 0 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_1_0_0_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_1_0_0_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 52 `bank_ZTGIJCF4_0_1_1_1`
(HOL idv `ZTGIJCF4 0 1 1 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_1_1_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_1_1_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 53 `bank_ZTGIJCF4_0_1_1_0`
(HOL idv `ZTGIJCF4 0 1 1 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_1_1_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_1_1_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 54 `bank_ZTGIJCF4_0_1_0_1`
(HOL idv `ZTGIJCF4 0 1 0 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_1_0_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_1_0_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 55 `bank_ZTGIJCF4_0_1_0_0`
(HOL idv `ZTGIJCF4 0 1 0 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_1_0_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_1_0_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 56 `bank_ZTGIJCF4_0_0_1_1`
(HOL idv `ZTGIJCF4 0 0 1 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_0_1_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_0_1_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 57 `bank_ZTGIJCF4_0_0_1_0`
(HOL idv `ZTGIJCF4 0 0 1 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_0_1_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_0_1_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 58 `bank_ZTGIJCF4_0_0_0_1`
(HOL idv `ZTGIJCF4 0 0 0 1 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_0_0_1 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_0_0_1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 59 `bank_ZTGIJCF4_0_0_0_0`
(HOL idv `ZTGIJCF4 0 0 0 0 1821661595` (ineq.hl:486-499 loop)). -/
theorem proj_bank_ZTGIJCF4_0_0_0_0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF4_0_0_0_0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 60 `bank_ZTGIJCF0`
(HOL ineq entry `ZTGIJCF0` (ineq.hl:446)). -/
theorem proj_bank_ZTGIJCF0 (h : pack_nonlinear_non_ox3q1h) : bank_ZTGIJCF0 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 61 `bank_GCKBQEA`
(HOL ineq entry `GCKBQEA` (ineq.hl:1352)). -/
theorem proj_bank_GCKBQEA (h : pack_nonlinear_non_ox3q1h) : bank_GCKBQEA :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Named projection of rest entry 62 `bank_RQWUDDU`
(HOL ineq entry `RQWUDDU` (ineq.hl:1332)). -/
theorem proj_bank_RQWUDDU (h : pack_nonlinear_non_ox3q1h) : bank_RQWUDDU :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Explicit form of `vol3f456` (operator unfolding; matches the body of
HOL `Functional_equation.nonf_gamma3_x`, functional_equation.hl:1327-1340). -/
private theorem mi_vol3f456_eq (m x1 x2 x3 x4 x5 x6 : ℝ) :
    vol3f456 m x1 x2 x3 x4 x5 x6
      = (2 * mm1 / Real.pi) * (solX x5 2 x4 2 x6 2 + solX x6 2 x5 2 x4 2
            + solX x4 2 x6 2 x5 2)
        - (8 * mm2 / Real.pi) * (lfun (Real.sqrt x4 * 0.5) * m
              * dihXf x4 2 x6 2 x5 2
            + lfun (Real.sqrt x5 * 0.5) * dihXf x5 2 x4 2 x6 2
            + lfun (Real.sqrt x6 * 0.5) * dihXf x6 2 x5 2 x4 2) := by
  simp only [vol3f456, scalar6, uni, mk456, compose6, projX4, projX5, projX6,
    projY4, projY5, projY6, constant6, two6, rotate4, rotate5, rotate6,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- HOL `gamma3_x_gamma3f` (merge_ineq.hl:4101-4126). -/
theorem mi_gamma3_x_gamma3f (a b c y4 y5 y6 : ℝ)
    (h4 : 2 * hminus ≤ y4) (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hminus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hminus) :
    gamma3f y4 y5 y6 (Real.sqrt 2) lmfun
      = gamma3X (h0cut y4) a b c (y4 * y4) (y5 * y5) (y6 * y6) := by
  have hsq2 : (Real.sqrt 2 * Real.sqrt 2 : ℝ) = 2 := Real.mul_self_sqrt (by norm_num)
  have h2le4 : (2 : ℝ) ≤ y4 := le_trans mi_two_le_two_hminus h4
  have hs4 : Real.sqrt (y4 * y4) = y4 := by
    rw [show y4 * y4 = y4 ^ 2 from by ring]
    exact Real.sqrt_sq (by linarith)
  have hs5 : Real.sqrt (y5 * y5) = y5 := by
    rw [show y5 * y5 = y5 ^ 2 from by ring]
    exact Real.sqrt_sq (by linarith)
  have hs6 : Real.sqrt (y6 * y6) = y6 := by
    rw [show y6 * y6 = y6 ^ 2 from by ring]
    exact Real.sqrt_sq (by linarith)
  have h05 : ∀ z : ℝ, z * 0.5 = z / 2 := by
    intro z
    rw [div_eq_mul_inv]
    norm_num
  have hc5 : h0cut y5 = 1 := p21_h0cutA y5 (le_trans h5' mi_two_hminus_le_two_h0)
  have hc6 : h0cut y6 = 1 := p21_h0cutA y6 (le_trans h6' mi_two_hminus_le_two_h0)
  have hb4 : lfun (Real.sqrt (y4 * y4) * 0.5) * h0cut y4 = lmfun (y4 / 2) := by
    rw [hs4, h05]
    exact (mi_lmfun_h0cut y4).symm
  have hb5 : lfun (Real.sqrt (y5 * y5) * 0.5) = lmfun (y5 / 2) := by
    rw [hs5, h05, mi_lmfun_h0cut y5, hc5, mul_one]
  have hb6 : lfun (Real.sqrt (y6 * y6) * 0.5) = lmfun (y6 / 2) := by
    rw [hs6, h05, mi_lmfun_h0cut y6, hc6, mul_one]
  have hvol : vol3r y4 y5 y6 (Real.sqrt 2)
      = volXf 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6) := by
    show volY (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 = _
    unfold volY
    rw [hsq2]
  have e1 : solY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
      = solX (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    have h0 : solY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
        = solX (y4 * y4) (y5 * y5) (Real.sqrt 2 * Real.sqrt 2)
            (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y6 * y6) := rfl
    rw [h0, hsq2]
    exact mi_solX_cycle (y4 * y4) (y5 * y5) 2 2 2 (y6 * y6)
  have e2 : solY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4
      = solX (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    have h0 : solY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4
        = solX (y5 * y5) (y6 * y6) (Real.sqrt 2 * Real.sqrt 2)
            (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y4 * y4) := rfl
    rw [h0, hsq2]
    exact mi_solX_cycle (y5 * y5) (y6 * y6) 2 2 2 (y4 * y4)
  have e3 : solY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5
      = solX (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
    have h0 : solY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5
        = solX (y6 * y6) (y4 * y4) (Real.sqrt 2 * Real.sqrt 2)
            (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y5 * y5) := rfl
    rw [h0, hsq2]
    exact mi_solX_cycle (y6 * y6) (y4 * y4) 2 2 2 (y5 * y5)
  have e4 : dihY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6
      = dihXf (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
    show dihXf (y4 * y4) (y5 * y5) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y6 * y6) = _
    rw [hsq2]
    exact mi_dihXf_sym2 (y4 * y4) (y5 * y5) 2 2 2 (y6 * y6)
  have e5 : dihY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4
      = dihXf (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 := by
    show dihXf (y5 * y5) (y6 * y6) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y4 * y4) = _
    rw [hsq2]
    exact mi_dihXf_sym2 (y5 * y5) (y6 * y6) 2 2 2 (y4 * y4)
  have e6 : dihY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5
      = dihXf (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 := by
    show dihXf (y6 * y6) (y4 * y4) (Real.sqrt 2 * Real.sqrt 2)
      (Real.sqrt 2 * Real.sqrt 2) (Real.sqrt 2 * Real.sqrt 2) (y5 * y5) = _
    rw [hsq2]
    exact mi_dihXf_sym2 (y6 * y6) (y4 * y4) 2 2 2 (y5 * y5)
  show vol3r y4 y5 y6 (Real.sqrt 2) - vol3f y4 y5 y6 (Real.sqrt 2) lmfun
      = gamma3X (h0cut y4) a b c (y4 * y4) (y5 * y5) (y6 * y6)
  rw [show gamma3X (h0cut y4) a b c (y4 * y4) (y5 * y5) (y6 * y6)
      = volXf 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6)
        - vol3f456 (h0cut y4) a b c (y4 * y4) (y5 * y5) (y6 * y6) from rfl,
    hvol, mi_vol3f456_eq]
  unfold vol3f
  rw [e1, e2, e3, e4, e5, e6, ← hb4, ← hb5, ← hb6]


/-! ## MERGE-INEQ wave 2b: `cell3_from_ineq_thm` (the cell3 dispatcher)

The GIANT refinement (merge_ineq.hl:3507-3745) over the nine COMMENT tracks
of charter §1.3.  Track map (kit consumers in parentheses):
1. remove excess variables — the `bank_*` entries are instantiated at their
   pinned `y1 y2 y3` values and projected onto the shared `(1,1,1)`-pinned
   `x`-form (`p21_bank_proj`, via `mi_gamma3fXDivSqrtdelta_arg3`);
2. insert Q — pure logic (the hypothesis bundle of `p21_cell3_core`);
3. remove eta_y — every `eta_y^2 > 2` disjunct dies against `Q`'s
   `eta_y < sqrt 2` (`mi_eta_y_nn` + `mi_ETA_Y_BOUNDS` +
   `mi_sqrt_lt_sqrt2`); CIHTIUM/CJFZZDW collapse into empty-box
   contrapositives;
4. remove dih_4 — `0.008 * dih_y >= 0` under `Q`
   (`mi_dih_y_div_sqrtdelta_pos`);
5. make strict + h0cut y4/y5/y6 branches — `p21_h0cutA`/`p21_h0cutB` +
   `mi_two_hminus_le_two_h0`/`p21_h0_lt_hplus` (the wt2-A `/2` step is plain
   arithmetic against track 4);
7. gamma3f — `p21_track7` consumes `mi_gamma3f_gamma3f_x_div_sqrtdelta`
   (the one inherited wave-2a debt) and closes with the nonnegative
   `sqrt(delta_x 2 2 2 …)` factor; the `mi_lmfun_h0cut` consumer lives
   inside that key equation (HOL :3049 `GSYM lmfun_h0cut`);
8. symmetry reduction — `mi_REAL_WLOG_SIMPLEX_3d` + `mi_gamma3f_sym` +
   `mi_eta_y_sym` (the two symmetry `Iff`s below);
9. `2*hminus < y4` closeout — the case tree of `p21_cell3_core`, boxes
   ranked `2.01 / 2*hminus / 2*hplus / sqrt8` over the
   `2*h0`-calibrated `h0cut` weights (`bank_QZECFICwt0corner`/`wt0`/`wt1`/
   `wt2A`/`CIHTIUM`/`CJFZZDW` instances).

(The theorem block itself was moved here verbatim from its wave-0 skeleton
position — pure block move, statement/docstring frozen — mirroring the HOL
layout, where `cell3_from_ineq_thm` :3507 sits after its kit :2873-3425.)  -/

/-- Track 1/7 bridge: the `y_of_x` packaging of the bank entries projects
onto the `(1,1,1)`-pinned `x`-form (`yOfX` squares its arguments;
`mi_gamma3fXDivSqrtdelta_arg3`: the operator body ignores its first three
slots, so the pinned values `1`/`sqrt 2` of the boxes are irrelevant). -/
private theorem p21_bank_proj (m4 m5 m6 v1 v2 v3 y4 y5 y6 : ℝ) :
    yOfX (gamma3fXDivSqrtdelta m4 m5 m6) v1 v2 v3 y4 y5 y6
      = gamma3fXDivSqrtdelta m4 m5 m6 1 1 1 (y4 * y4) (y5 * y5) (y6 * y6) := by
  unfold yOfX
  exact mi_gamma3fXDivSqrtdelta_arg3 m4 m5 m6 _ _ _ _ _ _

/-- Track 7: from the `h0cut`-weighted `gamma3f_x_div_sqrtdelta` bound to
the goal.  The `sqrt(delta_x 2 2 2 …)` factor is nonnegative, so
`mul_nonneg` closes. -/
private theorem p21_track7 (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h5 : 2 ≤ y5) (h6 : 2 ≤ y6)
    (h4' : y4 ≤ 2 * Real.sqrt 2) (h5' : y5 ≤ 2 * Real.sqrt 2) (h6' : y6 ≤ 2 * Real.sqrt 2)
    (het : eta_y y4 y5 y6 < Real.sqrt 2)
    (hX : 0 ≤ gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) (h0cut y6) 1 1 1
      (y4 * y4) (y5 * y5) (y6 * y6)) :
    0 ≤ gamma3f y4 y5 y6 (Real.sqrt 2) lmfun := by
  rw [mi_gamma3f_gamma3f_x_div_sqrtdelta 1 1 1 y4 y5 y6 h4 h5 h6 h4' h5' h6' het]
  exact mul_nonneg hX (Real.sqrt_nonneg _)

/-- Tracks 1-5 and 9: the sorted-order core.  Under `y6 <= y5 <= y4` and the
`Q` box, the seven cell3 entries cover every region of `[2, 2*sqrt2]^3` on
which `Q` is satisfiable: CIHTIUM/CJFZZDW empty the `> 2*hminus` corner
(their boxes force `eta_y^2 > 2`), and the five `QZECFIC` entries (ranked
`2.01 / 2*hminus / 2*hplus / sqrt8`) cover the rest, each firing exactly on
its own box. -/
private theorem p21_cell3_core (h_wt0 : bank_QZECFICwt0)
    (h_corner : bank_QZECFICwt0corner) (h_sqrt8 : bank_QZECFICwt0sqrt8)
    (h_wt1 : bank_QZECFICwt1) (h_wt2 : bank_QZECFICwt2A)
    (h_ciht : bank_CIHTIUM) (h_cjfzz : bank_CJFZZDW)
    (y4 y5 y6 : ℝ) (h4 : 2 ≤ y4) (h5 : 2 ≤ y5) (h6 : 2 ≤ y6)
    (h4' : y4 ≤ 2 * Real.sqrt 2) (h5' : y5 ≤ 2 * Real.sqrt 2) (h6' : y6 ≤ 2 * Real.sqrt 2)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) (h65 : y6 ≤ y5) (h54 : y5 ≤ y4) :
    0 ≤ gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) (h0cut y6) 1 1 1
      (y4 * y4) (y5 * y5) (y6 * y6) := by
  have h8eq : Real.sqrt 8 = 2 * Real.sqrt 2 := mi_sqrt8_eq
  have b4 : y4 ≤ Real.sqrt 8 := by rw [h8eq]; exact h4'
  have b5 : y5 ≤ Real.sqrt 8 := by rw [h8eq]; exact h5'
  have b6 : y6 ≤ Real.sqrt 8 := by rw [h8eq]; exact h6'
  obtain ⟨hups, _hdelta⟩ := mi_ETA_Y_BOUNDS y4 y5 y6 h4 b4 h5 b5 h6 b6 het
  -- track 3: `Q` kills every `eta_y^2 > 2` disjunct (`eta_y` is a `sqrt`,
  -- so its square is the quotient inside)
  have hq0 : 0 ≤ (y4 * y4) * (y5 * y5) * (y6 * y6) /
      upsX (y4 * y4) (y5 * y5) (y6 * y6) :=
    div_nonneg (by positivity) (le_of_lt hups)
  have het2 : eta_y y4 y5 y6 ^ 2 < 2 := by
    have hsq : eta_y y4 y5 y6 ^ 2
        = (y4 * y4) * (y5 * y5) * (y6 * y6) / upsX (y4 * y4) (y5 * y5) (y6 * y6) :=
      Real.sq_sqrt hq0
    have hlt := (mi_sqrt_lt_sqrt2 hq0).1
      (show Real.sqrt ((y4 * y4) * (y5 * y5) * (y6 * y6) /
          upsX (y4 * y4) (y5 * y5) (y6 * y6)) < Real.sqrt 2 from het)
    rw [hsq]; exact hlt
  -- track 9: the eta_y-killed CIHTIUM / CJFZZDW entries are empty-box
  -- contrapositives under `Q`
  have hciht : ¬(2 * hminus ≤ y4 ∧ 2 * hminus ≤ y5 ∧ 2 * hminus ≤ y6) := by
    rintro ⟨k4, k5, k6⟩
    have hbig := h_ciht 1 1 1 y4 y5 y6 le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      k4 b4 k5 b5 k6 b6
    exact absurd hbig (not_lt.mpr (le_of_lt het2))
  have hcjfzz : ¬(2 * hplus ≤ y4 ∧ 2 * hplus ≤ y5) := by
    rintro ⟨k4, k5⟩
    have hbig := h_cjfzz 1 1 1 y4 y5 y6 le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      k4 b4 k5 b5 h6 b6
    exact absurd hbig (not_lt.mpr (le_of_lt het2))
  -- track 4: the dihedral term is nonnegative under `Q`
  have hdih := mi_dih_y_div_sqrtdelta_pos y4 y5 y6 h4 h5 h6 h4' h5' h6' het
  rcases le_or_gt y4 (2 * hminus) with hk4 | hk4
  · -- track 8, first chop: `y4 <= 2*hminus` (then all three are, by
    -- sorting); the wt0/corner pair covers `[2, 2*hminus]` split at `2.01`
    have h5k : y5 ≤ 2 * hminus := by linarith
    have h6k : y6 ≤ 2 * hminus := by linarith
    have hc4 : h0cut y4 = 1 := p21_h0cutA y4 (by linarith [mi_two_hminus_le_two_h0, hk4])
    have hc5 : h0cut y5 = 1 := p21_h0cutA y5 (by linarith [mi_two_hminus_le_two_h0, h5k])
    have hc6 : h0cut y6 = 1 := p21_h0cutA y6 (by linarith [mi_two_hminus_le_two_h0, h6k])
    rcases le_or_gt (2.01 : ℝ) y4 with h201 | h201
    · -- `QZECFIC wt0` fires on [2.01, 2hminus] × [2, 2hminus]²
      have hcon := h_wt0 1 1 1 y4 y5 y6 le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
        h201 hk4 h5 h5k h6 h6k
      rw [hc4, hc5, hc6, ← p21_bank_proj 1 1 1 1 1 1 y4 y5 y6]
      exact le_of_lt hcon
    · -- `QZECFIC wt0 corner` fires on [2, 2.01]³ (all three, by sorting)
      have hcon := h_corner 1 1 1 y4 y5 y6 le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
        h4 (le_of_lt h201) h5 (show y5 ≤ (2.01 : ℝ) from by linarith)
          h6 (show y6 ≤ (2.01 : ℝ) from by linarith)
      rw [hc4, hc5, hc6, ← p21_bank_proj 1 1 1 1 1 1 y4 y5 y6]
      exact hcon
  · -- track 9, main run: `2*hminus <= y4`; CIHTIUM forces `y6 < 2*hminus`
    have h6k : y6 < 2 * hminus := by
      rcases le_or_gt (2 * hminus) y6 with hh | hh
      · exact absurd ⟨le_of_lt hk4, le_trans hh h65, hh⟩ hciht
      · exact hh
    have hc6 : h0cut y6 = 1 := p21_h0cutA y6 (by linarith [mi_two_hminus_le_two_h0, h6k])
    rcases le_or_gt (2 * hminus) y5 with h5k | h5k
    · -- track 9, third disjunct: `QZECFIC wt2 A` fires (its `/2` handled by
      -- plain arithmetic against `hdih`)
      obtain hcon | hcon := h_wt2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (le_of_lt hk4) b4 h5k b5 h6
          (le_of_lt h6k)
      · have h008 : (0 : ℝ) ≤ 0.008 * yOfX dih4XDivSqrtdeltaPosbranch (Real.sqrt 2)
            (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 := mul_nonneg (by norm_num) hdih
        have hX1 : 0 < yOfX (gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) 1)
            (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 := by linarith
        rw [hc6, ← p21_bank_proj (h0cut y4) (h0cut y5) 1 (Real.sqrt 2) (Real.sqrt 2)
          (Real.sqrt 2) y4 y5 y6]
        exact le_of_lt hX1
      · exact absurd hcon (not_lt.mpr (le_of_lt het2))
    · -- `y5 < 2*hminus`; split `y4` at `2*hplus`
      have hc5 : h0cut y5 = 1 := p21_h0cutA y5 (by linarith [mi_two_hminus_le_two_h0, h5k])
      rcases le_or_gt (2 * hplus) y4 with h4p | h4p
      · -- track 9, fourth disjunct: `QZECFIC wt0 sqrt8` fires
        obtain hcon | hcon := h_sqrt8 1 1 1 y4 y5 y6 le_rfl le_rfl le_rfl le_rfl
          le_rfl le_rfl h4p b4 h5 (le_of_lt h5k) h6 (le_of_lt h6k)
        · have hc4 : h0cut y4 = 0 :=
            p21_h0cutB y4 (by linarith [p21_h0_lt_hplus, h4p])
          rw [hc4, hc5, hc6, ← p21_bank_proj 0 1 1 1 1 1 y4 y5 y6]
          exact le_of_lt hcon
        · exact absurd hcon (not_lt.mpr (le_of_lt het2))
      · -- track 9, final branch: `QZECFIC wt1` fires
        obtain hcon | hcon := h_wt1 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6
          le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (le_of_lt hk4) (le_of_lt h4p) h5
            (le_of_lt h5k) h6 (le_of_lt h6k)
        · have h008 : (0 : ℝ) ≤ 0.008 * yOfX dih4XDivSqrtdeltaPosbranch (Real.sqrt 2)
              (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 := mul_nonneg (by norm_num) hdih
          have hX1 : 0 < yOfX (gamma3fXDivSqrtdelta (h0cut y4) 1 1) (Real.sqrt 2)
              (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 := by linarith
          rw [hc5, hc6, ← p21_bank_proj (h0cut y4) 1 1 (Real.sqrt 2) (Real.sqrt 2)
            (Real.sqrt 2) y4 y5 y6]
          exact le_of_lt hX1
        · exact absurd hcon (not_lt.mpr (le_of_lt het2))

/-- HOL `cell3_from_ineq_thm` (merge_ineq.hl:3507, statement
`mk_imp(cell3_hyp, cell3_from_ineq)`; refinement proof to :3745 over the
nine COMMENT tracks of charter §1.3).  MERGE-INEQ wave 2b closure (2026-09-29):
tracks 1-5/7/8/9 all discharged; the sole inherited debt is track 7's
`mi_gamma3f_gamma3f_x_div_sqrtdelta` (wave-2a NEEDS, sol_x_sol_euler_x chain). -/
theorem cell3_from_ineq_thm : cell3_bank → cell3_from_ineq := by
  -- tracks 1-5/7/9 are packaged as `p21_cell3_core` + `p21_track7`; track 8
  -- is the `mi_REAL_WLOG_SIMPLEX_3d` reduction below (hol :3690-3710).
  intro hb
  obtain ⟨h_wt0, h_corner, h_sqrt8, h_wt1, h_wt2, h_ciht, h_cjfzz⟩ := hb
  intro y4 y5 y6 h4 h5 h6 h4' h5' h6' het
  have hsorted : ∀ a b c : ℝ, c ≤ b → b ≤ a → 2 ≤ a → 2 ≤ b → 2 ≤ c →
      a ≤ 2 * Real.sqrt 2 → b ≤ 2 * Real.sqrt 2 → c ≤ 2 * Real.sqrt 2 →
      eta_y a b c < Real.sqrt 2 → 0 ≤ gamma3f a b c (Real.sqrt 2) lmfun := by
    intro a b c hcb hba ha hb hc ha' hb' hc' heta
    exact p21_track7 a b c ha hb hc ha' hb' hc' heta
      (p21_cell3_core h_wt0 h_corner h_sqrt8 h_wt1 h_wt2 h_ciht h_cjfzz a b c ha hb hc
        ha' hb' hc' heta hcb hba)
  -- the swap symmetry `P a b c <-> P a c b` (gamma3f_sym + eta_y sym)
  have hs1 : ∀ a b c : ℝ,
      (2 ≤ a → 2 ≤ b → 2 ≤ c → a ≤ 2 * Real.sqrt 2 → b ≤ 2 * Real.sqrt 2 →
        c ≤ 2 * Real.sqrt 2 → eta_y a b c < Real.sqrt 2 →
        0 ≤ gamma3f a b c (Real.sqrt 2) lmfun) ↔
      (2 ≤ a → 2 ≤ c → 2 ≤ b → a ≤ 2 * Real.sqrt 2 → c ≤ 2 * Real.sqrt 2 →
        b ≤ 2 * Real.sqrt 2 → eta_y a c b < Real.sqrt 2 →
        0 ≤ gamma3f a c b (Real.sqrt 2) lmfun) := by
    intro a b c
    constructor
    · intro h ha hc hb ha' hc' hb' heta
      have het' : eta_y a b c < Real.sqrt 2 := by
        rw [← (mi_eta_y_sym a b c).2] at heta
        exact heta
      rw [← (mi_gamma3f_sym a b c).1]
      exact h ha hb hc ha' hb' hc' het'
    · intro h ha hb hc ha' hb' hc' heta
      have het' : eta_y a c b < Real.sqrt 2 := by
        rw [(mi_eta_y_sym a b c).2] at heta
        exact heta
      rw [← (mi_gamma3f_sym a c b).1]
      exact h ha hc hb ha' hc' hb' het'
  -- the 3-cycle symmetry `P a b c <-> P b c a`
  have hs2 : ∀ a b c : ℝ,
      (2 ≤ a → 2 ≤ b → 2 ≤ c → a ≤ 2 * Real.sqrt 2 → b ≤ 2 * Real.sqrt 2 →
        c ≤ 2 * Real.sqrt 2 → eta_y a b c < Real.sqrt 2 →
        0 ≤ gamma3f a b c (Real.sqrt 2) lmfun) ↔
      (2 ≤ b → 2 ≤ c → 2 ≤ a → b ≤ 2 * Real.sqrt 2 → c ≤ 2 * Real.sqrt 2 →
        a ≤ 2 * Real.sqrt 2 → eta_y b c a < Real.sqrt 2 →
        0 ≤ gamma3f b c a (Real.sqrt 2) lmfun) := by
    intro a b c
    constructor
    · intro h hb hc ha hb' hc' ha' heta
      have het' : eta_y a b c < Real.sqrt 2 := by
        rw [(mi_eta_y_sym b c a).2, (mi_eta_y_sym b a c).1] at heta
        exact heta
      rw [← (mi_gamma3f_sym a b c).2]
      exact h ha hb hc ha' hb' hc' het'
    · intro h ha hb hc ha' hb' hc' heta
      have het' : eta_y b c a < Real.sqrt 2 := by
        rw [← (mi_eta_y_sym b a c).1, ← (mi_eta_y_sym b c a).2] at heta
        exact heta
      rw [(mi_gamma3f_sym a b c).2]
      exact h hb hc ha hb' hc' ha' het'
  exact mi_REAL_WLOG_SIMPLEX_3d
    (P := fun a b c : ℝ => 2 ≤ a → 2 ≤ b → 2 ≤ c → a ≤ 2 * Real.sqrt 2 →
      b ≤ 2 * Real.sqrt 2 → c ≤ 2 * Real.sqrt 2 → eta_y a b c < Real.sqrt 2 →
      0 ≤ gamma3f a b c (Real.sqrt 2) lmfun)
    hs1 hs2 hsorted y4 y5 y6 h4 h5 h6 h4' h5' h6' het

/-- HOL `TSKAJXY_statement_special_case` (TSKAJXY2.hl:80-88, a
`new_definition`). -/
def TSKAJXY_statement_special_case : Prop :=
  ∀ (V X : Set V3), saturated V → Packing V → mcellSet V X →
    ¬(∃ i ul, barV V 3 ul ∧ (i = 1 ∨ i = 2) ∧ X = mcell i V ul) →
    criticalEdgeX V X = ∅ → gammaX V X lmfun ≥ 0

/-- HOL `TSKAJXY_034` (TSKAJXY2.hl:92-722; giant: 0-cell, 4-cell and
3-cell cases, ~600 refinement steps). -/
theorem TSKAJXY_034 : tsk_hyp_new → TSKAJXY_statement_special_case := by
  -- NEEDS: TSKAJXY2.hl:92-722（0/3/4 胞巨案，~600 步 refinement）；路线：G 轨 cell3_bank/tsk_bank 切片 + cell3_from_ineq 链，capstone 仍假设叶喂入
  sorry

/-! ## Dot-algebra bridges (V3 = WithLp 2 (Fin 3 → ℝ)) -/

private theorem p21_smul_dot (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem p21_dot_smul (a b : V3) (t : ℝ) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem p21_dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

/-- `‖w‖^2 = w ⬝ᵥ w` on `V3`. -/
private theorem p21_norm_sq (w : V3) : ‖w‖ ^ 2 = w ⬝ᵥ w := by
  rw [EuclideanSpace.real_norm_sq_eq, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Coordinate expansion of the dot product on `V3`. -/
private theorem p21_dot_apply (a b : V3) :
    a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [dotProduct, Fin.sum_univ_three]

private theorem p21_apply_sub (v w : V3) (i : Fin 3) : (v - w) i = v i - w i := rfl

private theorem p21_dotPi_sub_l (a b c : Fin 3 → ℝ) :
    dotProduct (a - b) c = dotProduct a c - dotProduct b c := sub_dotProduct a b c

private theorem p21_dotPi_sub_r (a b c : Fin 3 → ℝ) :
    dotProduct a (b - c) = dotProduct a b - dotProduct a c := dotProduct_sub a b c

private theorem p21_dotPi_comm (a b : Fin 3 → ℝ) :
    dotProduct a b = dotProduct b a := dotProduct_comm a b

/-- The two-argument subtraction split, in the mixed coercion form the
`\u2b1d\u1d65`-notation produces for `(x - y) \u2b1dᵥ (z - w)`. -/
private theorem p21_split_pushed (x y z w : V3) :
    (x - y) ⬝ᵥ (z - w) = (x - y) ⬝ᵥ z - (x - y) ⬝ᵥ w := by
  show dotProduct (WithLp.ofLp (x - y)) (WithLp.ofLp z - WithLp.ofLp w)
      = dotProduct (WithLp.ofLp (x - y)) (WithLp.ofLp z)
        - dotProduct (WithLp.ofLp (x - y)) (WithLp.ofLp w)
  rw [WithLp.ofLp_sub]
  exact p21_dotPi_sub_r _ _ _

private theorem p21_split_r_atom (x y z : V3) :
    x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z := by
  show dotProduct (WithLp.ofLp x) (WithLp.ofLp y - WithLp.ofLp z)
      = dotProduct (WithLp.ofLp x) (WithLp.ofLp y)
        - dotProduct (WithLp.ofLp x) (WithLp.ofLp z)
  exact p21_dotPi_sub_r _ _ _

private theorem p21_add_dot_whole (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem p21_dot_add_whole (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem p21_dot_sub_whole (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem p21_sub_dot_whole (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

/-! ## TSKAJXY3.hl: the remaining cases (in source order) -/

private theorem p21_dot_add (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem p21_add_dot (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

/-- `‖x - a‖^2 = x⬝x - 2 x⬝a + a⬝a`. -/
private theorem p21_sq_sub (x a : V3) : ‖x - a‖ ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ a) + a ⬝ᵥ a := by
  rw [p21_norm_sq]
  simp only [p21_dot_apply, p21_apply_sub]
  ring

/-- The half-plane characterization of the (closed) bisector sector,
in the form used by BALL_DIFF_RCONE_GT_BISECTOR (HOL
`Leaf_cell.DIST_LE_HALF_PLANE`). -/
private theorem p21_dist_le_half2 (x a b : V3) :
    dist x a ≤ dist x b ↔ (x - a) ⬝ᵥ (b - a) ≤ ‖b - a‖ ^ 2 / 2 := by
  have key : ‖x - b‖ ^ 2 - ‖x - a‖ ^ 2 =
      -2 * ((x - a) ⬝ᵥ (b - a)) + ‖b - a‖ ^ 2 := by
    have h1 : ‖x - b‖ ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ b) + b ⬝ᵥ b := p21_sq_sub x b
    have h2 : ‖x - a‖ ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ a) + a ⬝ᵥ a := p21_sq_sub x a
    have h3 : ‖b - a‖ ^ 2 = (b - a) ⬝ᵥ (b - a) := p21_norm_sq _
    have h4 : (b - a) ⬝ᵥ (b - a) =
        (b - a) 0 * (b - a) 0 + (b - a) 1 * (b - a) 1 + (b - a) 2 * (b - a) 2 :=
      p21_dot_apply _ _
    have h5 : (x - a) ⬝ᵥ (b - a) =
        (x - a) 0 * (b - a) 0 + (x - a) 1 * (b - a) 1 + (x - a) 2 * (b - a) 2 :=
      p21_dot_apply _ _
    have h6 : ∀ i : Fin 3, (b - a) i = b i - a i := p21_apply_sub b a
    have h7 : ∀ i : Fin 3, (x - a) i = x i - a i := p21_apply_sub x a
    rw [h1, h2, h3, h4, h5]
    simp only [p21_dot_apply, h6, h7]
    ring
  constructor
  · intro h
    rw [dist_eq_norm, dist_eq_norm] at h
    have hsq : ‖x - a‖ ^ 2 ≤ ‖x - b‖ ^ 2 := by
      nlinarith [h, norm_nonneg (x - a : V3), norm_nonneg (x - b : V3)]
    have hnn : 0 ≤ ‖b - a‖ ^ 2 := sq_nonneg _
    linarith
  · intro h
    rw [dist_eq_norm, dist_eq_norm]
    have hnn : 0 ≤ -2 * ((x - a) ⬝ᵥ (b - a)) + ‖b - a‖ ^ 2 := by linarith
    have hd : 0 ≤ ‖x - b‖ ^ 2 - ‖x - a‖ ^ 2 := by rw [key]; linarith
    have habs : ‖x - a‖ ≤ ‖x - b‖ := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hd, hcon, norm_nonneg (x - a : V3), norm_nonneg (x - b : V3)]
    exact habs

/-- HOL `GAMMAX_NULLSET` (TSKAJXY3.hl:23). -/
theorem GAMMAX_NULLSET (V : Set V3) (f : ℝ → ℝ) (X : Set V3) (ul : List V3) (k : ℕ)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell k V ul)
    (hnull : nullSet X) : gammaX V X f = 0 := by
  have hVX : VX V X = ∅ := by rw [VX, if_pos hnull]
  have hEdge : edgeX V X = ∅ := by
    ext e
    simp only [edgeX, hVX]
    simp
  have hTS : totalSolid V X = 0 := by
    rw [totalSolid, hVX]
    simp [setSum]
  have hvol : volume.real X = 0 := by
    rw [Measure.real_def, hnull]
    simp
  rw [gammaX, hvol, hTS, hEdge]
  simp [setSum]

/-- HOL `GAMMAX_MCELL1` (TSKAJXY3.hl:48; proved 2026-09-29 wave A2: non-null
forces `sqrt 2 ≤ hl ul`, `EDGE_IMP_K2` kills the edge term, and
`HDTFNFZ_ALT`+`V_CELL1_SINGLE`+`HD_IN_MCELL` pin `VX V X = {EL 0 ul}` so the
total solid collapses to the single vertex term). -/
theorem GAMMAX_MCELL1 (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell1 V ul)
    (_hn : ¬nullSet X) :
    gammaX V X lmfun =
      volume.real X - (2 * mm1 / Real.pi) * sol (elV ul 0) X := by
  have hs : saturated V := _hs
  have hp : Packing V := _hp
  have hb : barV V 3 ul := _hb
  have hX : X = mcell1 V ul := _hX
  have hn : ¬nullSet X := _hn
  have hneX : X ≠ ∅ := fun he => hn (by rw [he]; exact measure_empty)
  -- non-nullness forces the `sqrt 2` branch of `mcell1`
  have hcond : Real.sqrt 2 ≤ hl ul := by
    by_contra hle
    refine hn ?_
    rw [hX]
    unfold mcell1
    rw [if_neg (by omega)]
    exact measure_empty
  -- no edges for a 1-cell
  have hedge : edgeX V X = ∅ := by
    rw [hX, BumpP4.MCELL1]
    exact BumpP4.EDGE_IMP_K2 V ul 1 hs hp hb (by omega)
  -- the vertex set is the singleton of the head
  have hvx : VX V X = {elV ul 0} := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [BumpP4.HDTFNFZ_ALT V ul 1 X hs hp hb (by rw [hX, BumpP4.MCELL1]) hn, hX]
      refine Set.Subset.trans (BumpP4.V_CELL1_SINGLE V ul hs hp hb) ?_
      rw [show hdV ul = elV ul 0 from by
        cases ul with
        | nil => rfl
        | cons a t => rfl]
    · rw [BumpP4.HDTFNFZ_ALT V ul 1 X hs hp hb (by rw [hX, BumpP4.MCELL1]) hn]
      intro hz hmem0
      have hz0 : hz = elV ul 0 := Set.mem_singleton_iff.mp hmem0
      subst hz0
      refine Set.mem_inter ?_ ?_
      · have hnv := hb.2 ul
          (And.intro (⟨[], (List.append_nil ul).symm⟩ :
            ∃ yl : List V3, ul = ul ++ yl)
            (by rw [hb.1]; omega))
        have h0 : elV ul 0 ∈ setOfList ul := by
          cases ul with
          | nil => exact absurd _hb.1 (by simp)
          | cons a t => simp [setOfList, elV]
        exact hnv.2.1 h0
      · have hdin := HD_IN_MCELL V ul 1 X hp hs hb (by rw [hX, BumpP4.MCELL1]) hneX
          (by omega)
        rwa [show hdV ul = elV ul 0 from by
          cases ul with
          | nil => rfl
          | cons a t => rfl] at hdin
  -- the total solid collapses to the single vertex term
  have hTS : totalSolid V X = sol (elV ul 0) X := by
    rw [totalSolid, hvx, setSum]
    have hfin : ({elV ul 0} : Set V3).Finite := by simp
    rw [dif_pos hfin]
    have hts : hfin.toFinset = ({elV ul 0} : Finset V3) := by
      ext z
      simp
    rw [hts, Finset.sum_singleton]
  rw [gammaX, hedge, hTS]
  simp [setSum]

/-- The degenerate `mcell2` null lemma (the "u = v" backstop): if the edge
endpoints coincide, the cell sits in `u + span {mxi - u, omega3 - u}`, a
translate of a ≤2-dimensional subspace, hence null. -/
private theorem p21_mcell2_uv_null (V : Set V3) (ul : List V3)
    (huv : elV ul 0 = elV ul 1) : nullSet (mcell2 V ul) := by
  by_cases hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
  · have hcent : hdV ul = elV ul 0 ∧ hdV ul.tail = elV ul 1 := by
      cases ul with
      | nil => exact ⟨rfl, rfl⟩
      | cons a t =>
        cases t with
        | nil => exact ⟨rfl, rfl⟩
        | cons b t => exact ⟨rfl, rfl⟩
    have hWne : (Submodule.span ℝ
        ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3)) ≠ ⊤ := by
      intro htop
      have h3 : Module.finrank ℝ
          (Submodule.span ℝ ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3)) = 3 := by
        rw [htop]; simp
      have hfr : Module.finrank ℝ
          (Submodule.span ℝ ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3)) ≤ 2 := by
        refine le_trans (finrank_span_le_card (R := ℝ) (M := V3)
          (s := ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3))) ?_
        have h4 : ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3).toFinset.card ≤ 2 := by
          have h5 := Set.ncard_insert_le (mxi V ul - elV ul 0)
            ({omegaListN V ul 3 - elV ul 0} : Set V3)
          have h6 : ({omegaListN V ul 3 - elV ul 0} : Set V3).ncard = 1 :=
            Set.ncard_singleton _
          have h7 : ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3).ncard
              = ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3).toFinset.card :=
            Set.ncard_eq_toFinset_card' _
          omega
        exact h4
      omega
    have hAffNe : ((AffineSubspace.mk' (elV ul 0)
          (Submodule.span ℝ ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3))
          : AffineSubspace ℝ V3)) ≠ ⊤ := by
      intro htop
      refine hWne ?_
      have h5 : ((AffineSubspace.mk' (elV ul 0)
          (Submodule.span ℝ ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3))
          : AffineSubspace ℝ V3)).direction
        = Submodule.span ℝ ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3) :=
        AffineSubspace.direction_mk' _ _
      rw [htop, AffineSubspace.direction_top] at h5
      exact h5.symm
    have hsub : mcell2 V ul ⊆
        ((AffineSubspace.mk' (elV ul 0)
            (Submodule.span ℝ ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3))
            : AffineSubspace ℝ V3) : Set V3) := by
      intro x hx
      rw [mcell2, if_pos hcond] at hx
      obtain ⟨_, hx2⟩ := hx
      simp only [affGe, Affsign, Set.mem_setOf_eq] at hx2
      obtain ⟨f, hfin, hxv, _, hsum⟩ := hx2
      have hmem : ∀ w ∈ hfin.toFinset, w = elV ul 0 ∨ w = mxi V ul ∨ w = omegaListN V ul 3 := by
        intro w hw
        have hw' : w ∈ (({hdV ul, hdV ul.tail} : Set V3) ∪ {mxi V ul, omegaListN V ul 3} : Set V3) := by
          simpa [Set.Finite.mem_toFinset] using hw
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
          hcent.1, hcent.2.trans huv.symm] at hw'
        tauto
      have hkey : x - elV ul 0 = ∑ w ∈ hfin.toFinset, f w • (w - elV ul 0) := by
        have h1 : ∑ w ∈ hfin.toFinset, f w • (w - elV ul 0)
            = (∑ w ∈ hfin.toFinset, f w • w)
              - (∑ w ∈ hfin.toFinset, f w) • elV ul 0 := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun w _ => by rw [smul_sub]
        rw [h1, hxv, hsum]
        simp
      have hin : x - elV ul 0 ∈ Submodule.span ℝ
          ({mxi V ul - elV ul 0, omegaListN V ul 3 - elV ul 0} : Set V3) := by
        rw [hkey]
        refine Submodule.sum_mem _ fun w hw => ?_
        rcases hmem w hw with rfl | rfl | rfl
        · rw [sub_self, smul_zero]
          exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            (Set.mem_insert (mxi V ul - elV ul 0)
              ({omegaListN V ul 3 - elV ul 0} : Set V3)))
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            (Set.mem_insert_of_mem _ (Set.mem_singleton (omegaListN V ul 3 - elV ul 0))))
      rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
      exact hin
    refine measure_mono_null hsub (MeasureTheory.Measure.addHaar_affineSubspace volume _ hAffNe)
  · rw [mcell2, if_neg hcond]
    exact measure_empty

/-- HOL `MCELL2_VX_PROPS` (TSKAJXY3.hl:89; proved 2026-09-29 wave B1:
`HDTFNFZ_ALT` + `LEPJBDJ` (k = 2) + `SET_OF_LIST_TRUNCATE_1` for the vertex
set, the u = v null backstop for distinctness, and direct `edgeX` algebra). -/
theorem MCELL2_VX_PROPS (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell2 V ul)
    (_hn : ¬nullSet X) :
    VX V X = {elV ul 0, elV ul 1} ∧ elV ul 0 ≠ elV ul 1 ∧
      edgeX V X = {{elV ul 0, elV ul 1}} := by
  have hs : saturated V := _hs
  have hp : Packing V := _hp
  have hb : barV V 3 ul := _hb
  have hX : X = mcell2 V ul := _hX
  have hn : ¬nullSet X := _hn
  have huv : elV ul 0 ≠ elV ul 1 := fun heq =>
    hn (by rw [hX]; exact p21_mcell2_uv_null V ul heq)
  have hne : mcell2 V ul ≠ ∅ := fun he => hn (by
    rw [hX, he]; exact measure_empty)
  have hvx : VX V X = {elV ul 0, elV ul 1} := by
    rw [BumpP4.HDTFNFZ_ALT V ul 2 X hs hp hb hX hn, hX, BumpP4.MCELL2,
      LEPJBDJ V ul 2 hs hp hb (by norm_num) (by norm_num) hne,
      BumpP4.SET_OF_LIST_TRUNCATE_1 ul (by have := hb.1; omega)]
  have hmem : ∀ z : V3, z ∈ VX V X ↔ z = elV ul 0 ∨ z = elV ul 1 := by
    intro z
    rw [hvx]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hedg : edgeX V X = {{elV ul 0, elV ul 1}} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro e he
      simp only [edgeX, Set.mem_setOf_eq] at he
      obtain ⟨a, b, rfl, ha, hb', hab⟩ := he
      have ha' : a = elV ul 0 ∨ a = elV ul 1 := (hmem a).mp ha
      have hb'' : b = elV ul 0 ∨ b = elV ul 1 := (hmem b).mp hb'
      rcases ha' with rfl | rfl
      · rcases hb'' with rfl | rfl
        · exact absurd rfl hab
        · rfl
      · rcases hb'' with rfl | rfl
        · rw [Set.pair_comm]
          rfl
        · exact absurd rfl hab
    · intro e he
      simp only [Set.mem_singleton_iff] at he
      subst he
      exact ⟨elV ul 0, elV ul 1, rfl, (hmem _).mpr (Or.inl rfl),
        (hmem _).mpr (Or.inr rfl), huv⟩
  exact ⟨hvx, huv, hedg⟩

/-- HOL `GAMMAX_MCELL2` (TSKAJXY3.hl:138; proved 2026-09-30 wave B3:
`MCELL2_VX_PROPS` pins the two vertices and the single edge, `totalSolid`
collapses to the two vertex sols, and the edge sum is the epsilon-beta pair
evaluation closed by `DIHX_SYM`/`HL_2` on the swapped branch). -/
theorem GAMMAX_MCELL2 (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell2 V ul)
    (_hn : ¬nullSet X) :
    gammaX V X lmfun =
      volume.real X - (2 * mm1 / Real.pi) * (sol (elV ul 0) X + sol (elV ul 1) X) +
        (8 * mm2 / Real.pi) * lmfun (hl [elV ul 0, elV ul 1]) *
          dihX V X (elV ul 0, elV ul 1) := by
  have hs : saturated V := _hs
  have hp : Packing V := _hp
  have hb : barV V 3 ul := _hb
  have hX : X = mcell2 V ul := _hX
  have hn : ¬nullSet X := _hn
  obtain ⟨hvx, huv, hedg⟩ := MCELL2_VX_PROPS V X ul hs hp hb hX hn
  -- the total solid over the two-vertex set
  have hTS : totalSolid V X = sol (elV ul 0) X + sol (elV ul 1) X := by
    rw [totalSolid, hvx, setSum]
    have hfin : ({elV ul 0, elV ul 1} : Set V3).Finite := by simp
    rw [dif_pos hfin]
    have hts : hfin.toFinset = ({elV ul 0, elV ul 1} : Finset V3) := by
      ext z
      simp
    rw [hts, Finset.sum_insert
      (show elV ul 0 ∉ ({elV ul 1} : Finset V3) from
        fun hc => huv (Finset.mem_singleton.mp hc)),
      Finset.sum_singleton]
  -- the single-edge sum: the epsilon picks the pair up to swap; the swapped
  -- branch closes by DIHX_SYM (edge membership) and HL_2/dist_comm
  have hms : mcellSet V X := ⟨2, ul, by rw [hX]; exact BumpP4.MCELL2 V ul, hb⟩
  have hedg_in : ({elV ul 0, elV ul 1} : Set V3) ∈ edgeX V X := by rw [hedg]; simp
  have heps := Classical.epsilon_spec
    (p := fun r : V3 × V3 => ({elV ul 0, elV ul 1} : Set V3) = {r.1, r.2})
    (⟨(elV ul 0, elV ul 1), rfl⟩ : ∃ y, ({elV ul 0, elV ul 1} : Set V3) = {y.1, y.2})
  have hEdge : (setSum (edgeX V X) fun e =>
      if e ∈ edgeX V X then
        let q := Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}
        dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
      else 0)
      = dihX V X (elV ul 0, elV ul 1) * lmfun (hl [elV ul 0, elV ul 1]) := by
    rw [setSum]
    have hfin : (edgeX V X : Set (Set V3)).Finite := by rw [hedg]; simp
    rw [dif_pos hfin]
    have hts : hfin.toFinset = {{elV ul 0, elV ul 1}} := by
      ext e
      simp [hedg]
    rw [hts]
    simp only [Finset.sum_singleton]
    split
    · next hmem =>
      rcases Set.pair_eq_pair_iff.mp heps with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
      · rw [← h1, ← h2, ← DIHX_SYM V X (elV ul 0) (elV ul 1) hp hs hms hedg_in,
          HL_2, HL_2, dist_comm]
    · next hnot => exact absurd hedg_in hnot
  rw [gammaX, hTS, hEdge]
  ring

/-- HOL `BALL_DIFF_RCONE_GT` (TSKAJXY3.hl:176; proved: pure inner-product
algebra on the definitions of `ball`/`rcone_gt`). -/
theorem BALL_DIFF_RCONE_GT (u0 u1 p : V3) (a r : ℝ)
    (hp : p ∈ Metric.ball u0 r \ rconeGt u0 u1 a) (ha : 0 ≤ a) :
    p ⬝ᵥ (u1 - u0) ≤ u0 ⬝ᵥ (u1 - u0) + r * a * dist u1 u0 := by
  obtain ⟨hball, hcone⟩ := hp
  have hd : dist p u0 < r := hball
  have hle : (p - u0) ⬝ᵥ (u1 - u0) ≤ dist p u0 * dist u1 u0 * a := by
    have hnot : ¬((p - u0) ⬝ᵥ (u1 - u0) > dist p u0 * dist u1 u0 * a) := by
      intro hgt
      exact hcone (by
        unfold rconeGt
        simpa [Set.mem_setOf_eq] using hgt)
    have := le_of_not_gt hnot
    simpa [rconeGt, Set.mem_setOf_eq] using this
  have hsplit : p ⬝ᵥ (u1 - u0) = (p - u0) ⬝ᵥ (u1 - u0) + u0 ⬝ᵥ (u1 - u0) := by
    show dotProduct (WithLp.ofLp p) (WithLp.ofLp u1 - WithLp.ofLp u0)
        = dotProduct (WithLp.ofLp (p - u0)) (WithLp.ofLp u1 - WithLp.ofLp u0)
          + dotProduct (WithLp.ofLp u0) (WithLp.ofLp u1 - WithLp.ofLp u0)
    rw [WithLp.ofLp_sub 2 p u0, p21_dotPi_sub_r, p21_dotPi_sub_l, p21_dotPi_sub_r]
    ring
  have hprod : dist p u0 * dist u1 u0 * a ≤ r * a * dist u1 u0 := by
    have h1 : dist p u0 * (dist u1 u0 * a) ≤ r * (dist u1 u0 * a) :=
      mul_le_mul_of_nonneg_right (le_of_lt hd) (mul_nonneg dist_nonneg ha)
    nlinarith [h1]
  rw [hsplit]
  linarith

/-- HOL `BALL_DIFF_RCONE_GT_BISECTOR` (TSKAJXY3.hl:201; proved from
BALL_DIFF_RCONE_GT + the half-plane form of the closed bisector). -/
theorem BALL_DIFF_RCONE_GT_BISECTOR (u0 u1 p : V3) (r h : ℝ)
    (hp : p ∈ Metric.ball u0 r \ rconeGt u0 u1 (h / r))
    (hdist : 2 * h = dist u1 u0) (hr : 0 < r) :
    dist p u0 ≤ dist p u1 := by
  have h0 : 0 ≤ dist u1 u0 := dist_nonneg
  have hh : 0 ≤ h := by linarith
  have hkey := BALL_DIFF_RCONE_GT u0 u1 p (h / r) r hp (by
    have : 0 ≤ h / r := div_nonneg hh (le_of_lt hr)
    linarith)
  have hmul : r * (h / r) * dist u1 u0 = 2 * h * h := by
    have hdiv : r * (h / r) = h := by field_simp
    rw [hdiv, hdist, mul_comm]
  have hsplit : (p - u0) ⬝ᵥ (u1 - u0) = p ⬝ᵥ (u1 - u0) - u0 ⬝ᵥ (u1 - u0) := by
    show dotProduct (WithLp.ofLp (p - u0)) (WithLp.ofLp u1 - WithLp.ofLp u0)
        = dotProduct (WithLp.ofLp p) (WithLp.ofLp u1 - WithLp.ofLp u0)
          - dotProduct (WithLp.ofLp u0) (WithLp.ofLp u1 - WithLp.ofLp u0)
    rw [WithLp.ofLp_sub 2 p u0, p21_dotPi_sub_l, p21_dotPi_sub_r]
  have hkey' : p ⬝ᵥ (u1 - u0) ≤ u0 ⬝ᵥ (u1 - u0) + 2 * h * h := by
    rw [hmul] at hkey
    linarith
  have hnorm : ‖u1 - u0‖ ^ 2 / 2 = 2 * h * h := by
    have hd2 : ‖u1 - u0‖ = 2 * h := by
      have hdn : ‖u1 - u0‖ = dist u1 u0 := dist_eq_norm u1 u0
      rw [hdn]
      exact hdist.symm
    rw [hd2]
    ring
  exact (p21_dist_le_half2 p u0 u1).2 (by linarith)

/-- HOL `MCELL1_EXPLICIT` (TSKAJXY3.hl:226; proved from the `mcell1`/`MCELL1`
definitions plus non-nullness forcing the `if`-condition). -/
theorem MCELL1_EXPLICIT (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (hX : X = mcell1 V ul)
    (hn : ¬nullSet X) :
    X = (rogers V ul ∩ Metric.closedBall (hdV ul) (Real.sqrt 2)) \
      rconeGt (hdV ul) (hdV ul.tail) (hl (truncateSimplex 1 ul) / Real.sqrt 2) := by
  by_cases hcond : Real.sqrt 2 ≤ hl ul
  · rw [hX]
    unfold mcell1
    rw [if_pos hcond]
  · exfalso
    apply hn
    rw [hX]
    unfold mcell1
    rw [if_neg hcond]
    unfold nullSet
    simp

/-- HOL `NULLSET_MCELL1` (TSKAJXY3.hl:405; proved from MCELL1_EXPLICIT +
monotonicity of measure). -/
theorem NULLSET_MCELL1 (V : Set V3) (ul : List V3) (_hp : Packing V)
    (_hs : saturated V) (_hb : barV V 3 ul) (h1 : ¬nullSet (mcell1 V ul)) :
    ¬nullSet (rogers V ul) := by
  intro hnull
  apply h1
  have hsub : mcell1 V ul ⊆ rogers V ul := by
    rw [MCELL1_EXPLICIT V (mcell1 V ul) ul _hs _hp _hb rfl h1]
    intro x hx
    exact hx.1.1
  have hle : volume (mcell1 V ul) ≤ volume (rogers V ul) := measure_mono hsub
  rw [hnull] at hle
  exact le_antisymm hle (by simp)

/-- HOL `MCELL1_VOL_RESTRICT` (TSKAJXY3.hl:244; proved: the `sqrt 2`-sphere
sliver of `mcell1` is null, so the ball-restriction preserves volume). -/
theorem MCELL1_VOL_RESTRICT (V X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell1 V ul)
    (hn : ¬nullSet X) :
    volume.real X = volume.real (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
  have hmeas : MeasurableSet X := by
    rw [hX]; exact MEASURABLE_MCELL V ul 1 hs hp hb
  have hmeas2 : MeasurableSet (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) :=
    hmeas.inter Metric.isOpen_ball.measurableSet
  have hcent : hdV ul = elV ul 0 := by
    cases ul with
    | nil => rfl
    | cons a t => rfl
  have hsub : X \ (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) ⊆
      Metric.sphere (elV ul 0) (Real.sqrt 2) := by
    intro x hx
    have hxX : x ∈ X := hx.1
    have hxnb : x ∉ Metric.ball (elV ul 0) (Real.sqrt 2) := fun h => hx.2 ⟨hxX, h⟩
    rw [MCELL1_EXPLICIT V X ul hs hp hb hX hn] at hxX
    have hcb : x ∈ Metric.closedBall (hdV ul) (Real.sqrt 2) := hxX.1.2
    rw [hcent] at hcb
    rw [Metric.mem_ball] at hxnb
    rw [Metric.mem_closedBall] at hcb
    exact Metric.mem_sphere.2 (le_antisymm hcb (not_lt.mp hxnb))
  have hsphere : volume (Metric.sphere (elV ul 0) (Real.sqrt 2)) = 0 :=
    Measure.addHaar_sphere volume (elV ul 0) (Real.sqrt 2)
  have hvol0 : volume (X \ (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2))) = 0 :=
    measure_mono_null hsub hsphere
  have h1 : volume X ≤ volume (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
    have hU : (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) ∪
        (X \ (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2))) = X := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      tauto
    have hsplit : volume ((X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) ∪
        (X \ (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)))) ≤
        volume (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) +
        volume (X \ (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2))) :=
      measure_union_le _ _
    rw [hU, hvol0, add_zero] at hsplit
    exact hsplit
  have h2 : volume (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) ≤ volume X :=
    measure_mono Set.inter_subset_left
  have hEQ : volume X = volume (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) :=
    le_antisymm h1 h2
  rw [Measure.real_def, Measure.real_def, hEQ]

/-! ## Wave-A1 private kit: 4-point convex hull vs `affGe` (2026-09-29)

The HOL proofs of CONVEX_HULL_4_AFF_GE / CONVEX_HULL_SCALE go through the
explicit weight characterisations `Cfyxfty.AFF_GE_3_1` / `Planarity.AFF_GE_1_3`
plus the coefficient-uniqueness of a non-coplanar quadruple.  Ported here as
private kit (`p21_*`); copies of the PA12 vertex/convexity helpers, which are
private there. -/

/-- A finite set's `toFinset` is determined by its elements (copy of
PackingAuto12 `p12_finite_toFinset_eq`, private there). -/
private theorem p21_finite_toFinset_eq {S : Set V3} {hS : S.Finite} {T : Finset V3}
    (h : S = (T : Set V3)) : hS.toFinset = T :=
  Finset.coe_inj.1 (by rw [hS.coe_toFinset, h])

/-- A vertex of `s` lies in `affGe s t` (finite `s ∪ t`; copy of PA12
`p12_mem_affGe_vertex`). -/
private theorem p21_mem_affGe_vertex {s t : Set V3} (hfin : (s ∪ t).Finite) {v : V3}
    (hv : v ∈ s) : v ∈ affGe s t := by
  have hvF : v ∈ hfin.toFinset := by
    simpa [Set.Finite.mem_toFinset] using Set.mem_union_left _ hv
  refine ⟨fun p => if p = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · show v = ∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0) • p
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) • p = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp
  · intro p hp
    by_cases hpv : p = v <;> simp [hpv]
  · show (∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0)) = 1
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp

/-- A vertex of `t` lies in `affGe s t` (finite `s ∪ t`; copy of PA12
`p12_mem_affGe_vertex_t`). -/
private theorem p21_mem_affGe_vertex_t {s t : Set V3} (hfin : (s ∪ t).Finite) {v : V3}
    (hv : v ∈ t) : v ∈ affGe s t := by
  have hvF : v ∈ hfin.toFinset := by
    simpa [Set.Finite.mem_toFinset] using Set.mem_union_right _ hv
  refine ⟨fun p => if p = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · show v = ∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0) • p
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) • p = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp
  · intro p hp
    by_cases hpv : p = v <;> simp [hpv]
  · show (∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0)) = 1
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp

/-- `affGe s t` is convex for finite `s ∪ t` (copy of PA12
`p12_convex_affGe`). -/
private theorem p21_convex_affGe {s t : Set V3} (hfin : (s ∪ t).Finite) :
    Convex ℝ (affGe s t) := by
  intro x hx y hy a b ha hb hab
  simp only [affGe, Affsign, Set.mem_setOf_eq] at hx hy
  obtain ⟨f1, _, hx1, hx2, hx3⟩ := hx
  obtain ⟨f2, _, hy1, hy2, hy3⟩ := hy
  refine ⟨fun p => a * f1 p + b * f2 p, hfin, ?_, ?_, ?_⟩
  · have key : ∀ (g : V3 → ℝ) (c : ℝ), ∑ q ∈ hfin.toFinset, (c * g q) • q
        = c • ∑ q ∈ hfin.toFinset, g q • q := by
      intro g c
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [smul_smul]
    have hsum1 : ∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q) • q
        = ∑ q ∈ hfin.toFinset, ((a * f1 q) • q + (b * f2 q) • q) := by
      exact Finset.sum_congr rfl fun q _ => by rw [add_smul]
    rw [hsum1, Finset.sum_add_distrib, key, key, hx1, hy1]
  · intro p hp
    have h1 : 0 ≤ f1 p := hx2 p hp
    have h2 : 0 ≤ f2 p := hy2 p hp
    show 0 ≤ a * f1 p + b * f2 p
    exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · show (∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q)) = 1
    have h3' : ∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q)
        = a * ∑ q ∈ hfin.toFinset, f1 q + b * ∑ q ∈ hfin.toFinset, f2 q := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h3', hx3, hy3]
    simp only [mul_one]
    exact hab

/-- A set that collapses to three points is coplanar (it sits in the
affine span of those three). -/
private theorem p21_coplanar_of_pair_eq (S : Set V3) {x y p q : V3} (hxy : x = y)
    (hS : S ⊆ ({x, y, p, q} : Set V3)) : Coplanar S := by
  subst hxy
  refine ⟨x, p, q, fun z hz => ?_⟩
  rcases hS hz with he | he | he | he <;> rw [he] <;>
    exact SetLike.mem_coe.2 (mem_affineSpan ℝ (by simp))

/-- A non-coplanar quadruple is pairwise distinct. -/
private theorem p21_ne_of_notCoplanar {w0 w1 w2 w3 : V3}
    (hcp : ¬Coplanar ({w0, w1, w2, w3} : Set V3)) :
    w0 ≠ w1 ∧ w0 ≠ w2 ∧ w0 ≠ w3 ∧ w1 ≠ w2 ∧ w1 ≠ w3 ∧ w2 ≠ w3 := by
  refine ⟨fun h => hcp (p21_coplanar_of_pair_eq _ h (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)),
    fun h => hcp (p21_coplanar_of_pair_eq _ h (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)),
    fun h => hcp (p21_coplanar_of_pair_eq _ h (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)),
    fun h => hcp (p21_coplanar_of_pair_eq _ h (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)),
    fun h => hcp (p21_coplanar_of_pair_eq _ h (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)),
    fun h => hcp (p21_coplanar_of_pair_eq _ h (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))⟩

/-- An affine combination with weights summing to 1 of three points lies in
their affine span (via the `vectorSpan` characterisation
`mem_affineSpan_iff_exists`). -/
private theorem p21_mem_affineSpan_of_sum {p0 p1 p2 x : V3} {c0 c1 c2 : ℝ}
    (hsum : c0 + c1 + c2 = 1) (hx : x = c0 • p0 + c1 • p1 + c2 • p2) :
    x ∈ (affineSpan ℝ ({p0, p1, p2} : Set V3) : Set V3) := by
  refine (mem_affineSpan_iff_exists (k := ℝ)).mpr
    ⟨p2, Set.mem_insert_of_mem p0 (Set.mem_insert_of_mem p1 (Set.mem_singleton p2)),
      x - p2, ?_, by simp⟩
  rw [vectorSpan_def]
  have hexp : x - p2 = c0 • (p0 - p2) + c1 • (p1 - p2) := by
    rw [hx]
    have h1 : (c0 + c1 + c2) • p2 = p2 := by rw [hsum]; simp
    calc (c0 • p0 + c1 • p1 + c2 • p2) - p2
        = (c0 • p0 + c1 • p1 + c2 • p2) - (c0 + c1 + c2) • p2 := by rw [h1]
      _ = c0 • (p0 - p2) + c1 • (p1 - p2) := by module
  rw [hexp]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨p0, Set.mem_insert p0 {p1, p2}, p2,
        Set.mem_insert_of_mem p0 (Set.mem_insert_of_mem p1 (Set.mem_singleton p2)), rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨p1, Set.mem_insert_of_mem p0 (Set.mem_insert p1 {p2}), p2,
        Set.mem_insert_of_mem p0 (Set.mem_insert_of_mem p1 (Set.mem_singleton p2)), rfl⟩)

/-- Coefficient uniqueness for a non-coplanar quadruple: two affine
representations with weights summing to 1 coincide. -/
private theorem p21_coeff_unique {w0 w1 w2 w3 : V3}
    (hcp : ¬Coplanar ({w0, w1, w2, w3} : Set V3)) {t0 t1 t2 t3 s0 s1 s2 s3 : ℝ}
    (htsum : t0 + t1 + t2 + t3 = 1) (hssum : s0 + s1 + s2 + s3 = 1)
    (hy : t0 • w0 + t1 • w1 + t2 • w2 + t3 • w3 = s0 • w0 + s1 • w1 + s2 • w2 + s3 • w3) :
    t0 = s0 ∧ t1 = s1 ∧ t2 = s2 ∧ t3 = s3 := by
  have hsum : t0 - s0 + (t1 - s1) + (t2 - s2) + (t3 - s3) = 0 := by linarith
  have hvec : (t0 - s0) • w0 + (t1 - s1) • w1 + (t2 - s2) • w2 + (t3 - s3) • w3 = 0 := by
    have hsub : (t0 • w0 + t1 • w1 + t2 • w2 + t3 • w3)
        - (s0 • w0 + s1 • w1 + s2 • w2 + s3 • w3) = 0 := by
      rw [sub_eq_zero]
      exact hy
    calc (t0 - s0) • w0 + (t1 - s1) • w1 + (t2 - s2) • w2 + (t3 - s3) • w3
        = (t0 • w0 + t1 • w1 + t2 • w2 + t3 • w3)
          - (s0 • w0 + s1 • w1 + s2 • w2 + s3 • w3) := by module
      _ = 0 := hsub
  -- the key: a nonzero coefficient puts the corresponding point in the span
  -- of the other three, which makes any superset coplanar
  have key : ∀ (S : Set V3) (e a b c : V3) (de da db dc : ℝ), de ≠ 0 →
      da + db + dc + de = 0 → da • a + db • b + dc • c + de • e = 0 →
      S ⊆ ({e, a, b, c} : Set V3) → Coplanar S := by
    intro S e a b c de da db dc hde hsum hvec hS
    refine ⟨a, b, c, fun z hz => ?_⟩
    have hzin : z = e ∨ z = a ∨ z = b ∨ z = c := by
      have := hS hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      tauto
    have hcop : e ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := by
      refine p21_mem_affineSpan_of_sum (c0 := -da / de) (c1 := -db / de)
        (c2 := -dc / de) ?_ ?_
      · show (-da / de) + (-db / de) + (-dc / de) = 1
        field_simp
        linarith
      · show e = (-da / de) • a + (-db / de) • b + (-dc / de) • c
        have h1 : (da • a + db • b + dc • c) + de • e = 0 := hvec
        have hscal : de • e = (-da) • a + (-db) • b + (-dc) • c := by
          have h2 : de • e + (da • a + db • b + dc • c) = 0 := by
            rw [add_comm]
            exact h1
          first
            | linear_combination (norm := module) h2
            | linear_combination (norm := module) -h2
        calc e = (de⁻¹) • (de • e) := by
              rw [smul_smul, inv_mul_cancel₀ hde, one_smul]
          _ = (de⁻¹) • ((-da) • a + (-db) • b + (-dc) • c) := by rw [hscal]
          _ = (-da / de) • a + (-db / de) • b + (-dc / de) • c := by module
    rcases hzin with he | he | he | he
    · rw [he]
      exact hcop
    · rw [he]
      exact SetLike.mem_coe.2 (mem_affineSpan ℝ (by simp))
    · rw [he]
      exact SetLike.mem_coe.2 (mem_affineSpan ℝ (by simp))
    · rw [he]
      exact SetLike.mem_coe.2 (mem_affineSpan ℝ (by simp))
  have hsub4 : ({w0, w1, w2, w3} : Set V3) ⊆ ({w3, w0, w1, w2} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hsub2 : ({w0, w1, w2, w3} : Set V3) ⊆ ({w2, w0, w1, w3} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hsub1 : ({w0, w1, w2, w3} : Set V3) ⊆ ({w1, w0, w2, w3} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  rcases eq_or_ne (t0 - s0) 0 with h0 | h0
  · rcases eq_or_ne (t1 - s1) 0 with h1 | h1
    · rcases eq_or_ne (t2 - s2) 0 with h2 | h2
      · rcases eq_or_ne (t3 - s3) 0 with h3 | h3
        · exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩
        · exact absurd (key ({w0, w1, w2, w3} : Set V3) w3 w0 w1 w2 (t3 - s3) (t0 - s0)
            (t1 - s1) (t2 - s2) h3 (by linarith) hvec hsub4) hcp
      · exact absurd (key ({w0, w1, w2, w3} : Set V3) w2 w0 w1 w3 (t2 - s2) (t0 - s0)
          (t1 - s1) (t3 - s3) h2 (by linarith)
          (by first
            | linear_combination (norm := module) hvec
            | linear_combination (norm := module) -hvec) hsub2) hcp
    · exact absurd (key ({w0, w1, w2, w3} : Set V3) w1 w0 w2 w3 (t1 - s1) (t0 - s0)
        (t2 - s2) (t3 - s3) h1 (by linarith)
        (by first
          | linear_combination (norm := module) hvec
          | linear_combination (norm := module) -hvec) hsub1) hcp
  · exact absurd (key ({w0, w1, w2, w3} : Set V3) w0 w1 w2 w3 (t0 - s0) (t1 - s1)
      (t2 - s2) (t3 - s3) h0 (by linarith)
      (by first
        | linear_combination (norm := module) hvec
        | linear_combination (norm := module) -hvec) (Subset.refl _)) hcp

/-- Explicit weight characterisation of `affGe {p} {q1, q2, q3}` for a
pairwise-distinct quadruple (the 4-distinct branch of HOL `AFF_GE_1_3`,
Cfyxfty.hl). -/
private theorem p21_affGe_1_3_char {p q1 q2 q3 : V3}
    (hd : p ≠ q1 ∧ p ≠ q2 ∧ p ≠ q3 ∧ q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3) (y : V3) :
    y ∈ affGe ({p} : Set V3) ({q1, q2, q3} : Set V3) ↔
      ∃ t0 t1 t2 t3 : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3 ∧
        t0 + t1 + t2 + t3 = 1 ∧ y = t0 • p + t1 • q1 + t2 • q2 + t3 • q3 := by
  have hfin : ((({p} : Set V3) ∪ {q1, q2, q3}) : Set V3).Finite := by simp
  have hF : hfin.toFinset = insert p (insert q1 (insert q2 {q3})) := by
    refine p21_finite_toFinset_eq ?_
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton]
    all_goals tauto
  have hp' : p ∉ (insert q1 (insert q2 {q3}) : Finset V3) := by
    simp [hd.1, hd.2.1, hd.2.2.1]
  have hq' : q1 ∉ (insert q2 {q3} : Finset V3) := by
    simp [hd.2.2.2.1, hd.2.2.2.2.1]
  have hr' : q2 ∉ ({q3} : Finset V3) := by simp [hd.2.2.2.2.2]
  constructor
  · rintro ⟨f, _, hy, hpos, hsum⟩
    have hy' : y = f p • p + f q1 • q1 + f q2 • q2 + f q3 • q3 := by
      have h2 := hy
      rw [hF, Finset.sum_insert hp', Finset.sum_insert hq', Finset.sum_insert hr',
        Finset.sum_singleton] at h2
      have h3 : f p • p + (f q1 • q1 + (f q2 • q2 + f q3 • q3))
          = f p • p + f q1 • q1 + f q2 • q2 + f q3 • q3 := by module
      rw [← h3]
      exact h2
    have hsum' : f p + f q1 + f q2 + f q3 = 1 := by
      have h2 := hsum
      rw [hF, Finset.sum_insert hp', Finset.sum_insert hq', Finset.sum_insert hr',
        Finset.sum_singleton] at h2
      linarith
    refine ⟨f p, f q1, f q2, f q3,
      hpos q1 (by simp), hpos q2 (by simp), hpos q3 (by simp), hsum', hy'⟩
  · rintro ⟨t0, t1, t2, t3, ht1, ht2, ht3, htsum, hty⟩
    refine ⟨fun w => if w = p then t0 else if w = q1 then t1 else if w = q2 then t2 else t3,
      hfin, ?_, ?_, ?_⟩
    · rw [hF, Finset.sum_insert hp', Finset.sum_insert hq', Finset.sum_insert hr',
        Finset.sum_singleton]
      simp [Ne.symm hd.1, Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1,
        Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2]
      rw [hty]
      module
    · intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · simp [hd.1, Ne.symm hd.1, ht1]
      · simp [hd.2.1, Ne.symm hd.2.1, hd.2.2.2.1, Ne.symm hd.2.2.2.1, ht2]
      · simp [hd.2.2.1, Ne.symm hd.2.2.1, hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.1,
          hd.2.2.2.2.2, Ne.symm hd.2.2.2.2.2, ht3]
    · rw [hF, Finset.sum_insert hp', Finset.sum_insert hq', Finset.sum_insert hr',
        Finset.sum_singleton]
      simp [Ne.symm hd.1, Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1,
        Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2]
      linarith

/-- Explicit weight characterisation of `affGe {q1, q2, q3} {p}` for a
pairwise-distinct quadruple (the 4-distinct branch of HOL `AFF_GE_3_1`,
Cfyxfty.hl). -/
private theorem p21_affGe_3_1_char {p q1 q2 q3 : V3}
    (hd : p ≠ q1 ∧ p ≠ q2 ∧ p ≠ q3 ∧ q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3) (y : V3) :
    y ∈ affGe ({q1, q2, q3} : Set V3) ({p} : Set V3) ↔
      ∃ s0 s1 s2 s3 : ℝ, 0 ≤ s0 ∧ s0 + s1 + s2 + s3 = 1 ∧
        y = s0 • p + s1 • q1 + s2 • q2 + s3 • q3 := by
  have hfin : ((({q1, q2, q3} : Set V3) ∪ {p}) : Set V3).Finite := by simp
  have hF : hfin.toFinset = insert q1 (insert q2 (insert q3 {p})) := by
    refine p21_finite_toFinset_eq ?_
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton]
    all_goals tauto
  have hq1' : q1 ∉ (insert q2 (insert q3 {p}) : Finset V3) := by
    simp [hd.1, Ne.symm hd.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2]
  have hq2' : q2 ∉ (insert q3 {p} : Finset V3) := by
    simp [hd.2.1, Ne.symm hd.2.1, hd.2.2.2.2.2, Ne.symm hd.2.2.2.1]
  have hq3' : q3 ∉ ({p} : Finset V3) := by simp [hd.2.2.1, Ne.symm hd.2.2.1]
  constructor
  · rintro ⟨f, _, hy, hpos, hsum⟩
    have hy' : y = f p • p + f q1 • q1 + f q2 • q2 + f q3 • q3 := by
      have h2 := hy
      rw [hF, Finset.sum_insert hq1', Finset.sum_insert hq2', Finset.sum_insert hq3',
        Finset.sum_singleton] at h2
      have h3 : f q1 • q1 + (f q2 • q2 + (f q3 • q3 + f p • p))
          = f p • p + f q1 • q1 + f q2 • q2 + f q3 • q3 := by module
      rw [← h3]
      exact h2
    have hsum' : f p + f q1 + f q2 + f q3 = 1 := by
      have h2 := hsum
      rw [hF, Finset.sum_insert hq1', Finset.sum_insert hq2', Finset.sum_insert hq3',
        Finset.sum_singleton] at h2
      linarith
    exact ⟨f p, f q1, f q2, f q3, hpos p (Set.mem_singleton p), hsum', hy'⟩
  · rintro ⟨s0, s1, s2, s3, hs0, hssum, hsy⟩
    refine ⟨fun w => if w = p then s0 else if w = q1 then s1 else if w = q2 then s2 else s3,
      hfin, ?_, ?_, ?_⟩
    · rw [hF, Finset.sum_insert hq1', Finset.sum_insert hq2', Finset.sum_insert hq3',
        Finset.sum_singleton]
      simp [Ne.symm hd.1, Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1,
        Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2]
      rw [hsy]
      module
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simp [hd.1, hd.2.1, hd.2.2.1, hs0]
    · rw [hF, Finset.sum_insert hq1', Finset.sum_insert hq2', Finset.sum_insert hq3',
        Finset.sum_singleton]
      simp [Ne.symm hd.1, Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1,
        Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2]
      linarith

/-- Membership in the hull of four points from nonnegative weights summing
to 1 (via `mem_convexHull_of_exists_fintype` at `ι = Fin 4`). -/
private theorem p21_mem_hull4 {w0 w1 w2 w3 y : V3} {c0 c1 c2 c3 : ℝ}
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hcsum : c0 + c1 + c2 + c3 = 1)
    (hy : y = c0 • w0 + c1 • w1 + c2 • w2 + c3 • w3) :
    y ∈ convexHull ℝ ({w0, w1, w2, w3} : Set V3) := by
  refine mem_convexHull_of_exists_fintype ![c0, c1, c2, c3] ![w0, w1, w2, w3] ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [hc0, hc1, hc2, hc3]
  · rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact hcsum
  · intro i
    fin_cases i <;> simp
  · rw [Fin.sum_univ_four, hy]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    simp

/-- HOL `CONVEX_HULL_4_AFF_GE` (TSKAJXY3.hl:336; proved 2026-09-29 wave A1:
both containments from the explicit weight characterisations of the two
`affGe`s, the coefficient uniqueness closing the reverse one). -/
theorem CONVEX_HULL_4_AFF_GE (w0 w1 w2 w3 : V3) (hcp : ¬Coplanar ({w0, w1, w2, w3} : Set V3)) :
    convexHull ℝ ({w0, w1, w2, w3} : Set V3) =
      affGe ({w0} : Set V3) {w1, w2, w3} ∩
        affGe ({w1, w2, w3} : Set V3) ({w0} : Set V3) := by
  have hd := p21_ne_of_notCoplanar hcp
  have hfin1 : ((({w0} : Set V3) ∪ {w1, w2, w3}) : Set V3).Finite := by simp
  have hfin2 : ((({w1, w2, w3} : Set V3) ∪ {w0}) : Set V3).Finite := by simp
  have hconv : Convex ℝ (affGe ({w0} : Set V3) {w1, w2, w3} ∩
      affGe ({w1, w2, w3} : Set V3) ({w0} : Set V3)) :=
    (p21_convex_affGe hfin1).inter (p21_convex_affGe hfin2)
  have hsub : ({w0, w1, w2, w3} : Set V3) ⊆ affGe ({w0} : Set V3) {w1, w2, w3} ∩
      affGe ({w1, w2, w3} : Set V3) ({w0} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with he | he | he | he
    · rw [he]
      exact ⟨p21_mem_affGe_vertex hfin1 (Set.mem_singleton w0),
        p21_mem_affGe_vertex_t hfin2 (Set.mem_singleton w0)⟩
    · rw [he]
      exact ⟨p21_mem_affGe_vertex_t hfin1 (Set.mem_insert w1 {w2, w3}),
        p21_mem_affGe_vertex hfin2 (Set.mem_insert w1 {w2, w3})⟩
    · rw [he]
      exact ⟨p21_mem_affGe_vertex_t hfin1 (Set.mem_insert_of_mem _ (Set.mem_insert w2 {w3})),
        p21_mem_affGe_vertex hfin2 (Set.mem_insert_of_mem _ (Set.mem_insert w2 {w3}))⟩
    · rw [he]
      exact ⟨p21_mem_affGe_vertex_t hfin1
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton w3))),
        p21_mem_affGe_vertex hfin2
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton w3)))⟩
  refine Set.Subset.antisymm (convexHull_min hsub hconv) ?_
  intro y hy
  obtain ⟨t0, t1, t2, t3, ht1, ht2, ht3, htsum, hty⟩ :=
    (p21_affGe_1_3_char hd y).mp hy.1
  obtain ⟨s0, s1, s2, s3, hs0, hssum, hsy⟩ :=
    (p21_affGe_3_1_char hd y).mp hy.2
  have heq : t0 • w0 + t1 • w1 + t2 • w2 + t3 • w3 = s0 • w0 + s1 • w1 + s2 • w2 + s3 • w3 :=
    hty.symm.trans hsy
  obtain ⟨rfl, rfl, rfl, rfl⟩ := p21_coeff_unique hcp htsum hssum heq
  exact p21_mem_hull4 hs0 ht1 ht2 ht3 htsum hty

/-- HOL `CONVEX_HULL_SCALE` (TSKAJXY3.hl:363; proved 2026-09-29 wave A1:
coefficient comparison against the `affGe {w1,w2,w3} {w0}` witness via the
non-coplanar coefficient uniqueness). -/
theorem CONVEX_HULL_SCALE (w0 w1 w2 w3 w : V3) (t : ℝ)
    (hcp : ¬Coplanar ({w0, w1, w2, w3} : Set V3)) (hw : w ∈ convexHull ℝ ({w0, w1, w2, w3} : Set V3))
    (ht : 0 ≤ t)
    (hmem : w0 + t • (w - w0) ∈ affGe ({w1, w2, w3} : Set V3) ({w0} : Set V3)) :
    w0 + t • (w - w0) ∈ convexHull ℝ ({w0, w1, w2, w3} : Set V3) := by
  have hd := p21_ne_of_notCoplanar hcp
  rw [CONVEX_HULL_4_AFF_GE w0 w1 w2 w3 hcp] at hw
  obtain ⟨u0, u1, u2, u3, hu1, hu2, hu3, husum, huw⟩ :=
    (p21_affGe_1_3_char hd w).mp hw.1
  obtain ⟨s0, s1, s2, s3, hs0, hssum, hsy⟩ :=
    (p21_affGe_3_1_char hd (w0 + t • (w - w0))).mp hmem
  have hc0 : 1 - t + t * u0 + t * u1 + t * u2 + t * u3 = 1 := by
    have hkey : 1 - t + t * u0 + t * u1 + t * u2 + t * u3
        = 1 + t * (u0 + u1 + u2 + u3 - 1) := by ring
    rw [hkey, husum]
    ring
  have hvec : w0 + t • (w - w0)
      = (1 - t + t * u0) • w0 + (t * u1) • w1 + (t * u2) • w2 + (t * u3) • w3 := by
    rw [huw]
    module
  have hEq : (1 - t + t * u0) • w0 + (t * u1) • w1 + (t * u2) • w2 + (t * u3) • w3
      = s0 • w0 + s1 • w1 + s2 • w2 + s3 • w3 := by
    rw [← hvec, ← hsy]
  obtain ⟨hc0eq, hc1eq, hc2eq, hc3eq⟩ := p21_coeff_unique hcp hc0 hssum hEq
  refine p21_mem_hull4 ?_ ?_ ?_ ?_ hc0 hvec
  · linarith
  · exact mul_nonneg ht hu1
  · exact mul_nonneg ht hu2
  · exact mul_nonneg ht hu3

/-- HOL `IMAGE_4_EXPLICIT` (TSKAJXY3.hl:394). -/
theorem IMAGE_4_EXPLICIT {B : Type*} (f : ℕ → B) :
    {f i | i ≤ 3} = {f 0, f 1, f 2, f 3} := by
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, by norm_num, rfl⟩

/-- HOL `NULLSET_MCELL1` applied form `NOT_COPLANAR_OMEGA_LIST_N`
(TSKAJXY3.hl:422; proved 2026-09-29 wave A1: the Rogers simplex is the hull
of the four omega points, a coplanar hull dies inside the null span of a
three-point affine hull, and `mcell1 ⊆ rogers`). -/
theorem NOT_COPLANAR_OMEGA_LIST_N (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (h1 : ¬nullSet (mcell1 V ul)) :
    ¬Coplanar {omegaListN V ul i | i ≤ 3} := by
  intro hcp
  obtain ⟨p, q, r, hsub⟩ := hcp
  have hlen : ul.length = 4 := hb.1
  have himg : ∀ j : ℕ, j < ul.length →
      omegaListN V ul j ∈ {omegaListN V ul i | i ≤ 3} := by
    intro j hj
    exact ⟨j, by omega, rfl⟩
  have hspan : rogers V ul ⊆ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := by
    have hstep1 : rogers V ul ⊆
        (affineSpan ℝ (omegaListN V ul '' {j : ℕ | j < ul.length}) : Set V3) := by
      rw [rogers]
      exact convexHull_subset_affineSpan _
    have hstep2 : affineSpan ℝ (omegaListN V ul '' {j : ℕ | j < ul.length})
        ≤ affineSpan ℝ ({p, q, r} : Set V3) := by
      refine affineSpan_le.2 ?_
      rintro x ⟨j, hj, rfl⟩
      simp only [Set.mem_image, Set.mem_setOf_eq] at hj
      exact hsub (himg j hj)
    intro x hx
    exact SetLike.mem_coe.2 (hstep2 (hstep1 hx))
  have hsub1 : mcell1 V ul ⊆ rogers V ul := by
    rw [mcell1]
    by_cases hcond : Real.sqrt 2 ≤ hl ul
    · rw [if_pos hcond]
      exact Set.diff_subset.trans Set.inter_subset_left
    · rw [if_neg hcond]
      exact Set.empty_subset _
  have hne : (affineSpan ℝ ({p, q, r} : Set V3) : AffineSubspace ℝ V3) ≠ ⊤ := by
    have hle2 : Module.finrank ℝ (vectorSpan ℝ ({p, q, r} : Set V3)) ≤ 2 := by
      have hvs : vectorSpan ℝ ({p, q, r} : Set V3)
          ≤ Submodule.span ℝ ({q - p, r - p} : Set V3) := by
        rw [vectorSpan_eq_span_vsub_set_left (k := ℝ)
          (Set.mem_insert p ({q, r} : Set V3)), Submodule.span_le]
        rintro z ⟨x, hx, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with he | he | he
        · rw [he]; simp
        · rw [he]
          simp only [vsub_eq_sub]
          have hneg : (p - q : V3) = -(q - p) := by rw [neg_sub]
          rw [hneg]
          exact Submodule.neg_mem _ (Submodule.subset_span
            (Set.mem_insert (q - p) ({r - p} : Set V3)))
        · rw [he]
          simp only [vsub_eq_sub]
          have hneg : (p - r : V3) = -(r - p) := by rw [neg_sub]
          rw [hneg]
          exact Submodule.neg_mem _ (Submodule.subset_span
            (Set.mem_insert_of_mem (q - p) (Set.mem_singleton (r - p))))
      refine le_trans (Submodule.finrank_mono hvs) ?_
      refine le_trans (finrank_span_le_card (R := ℝ) (M := V3)
        (s := ({q - p, r - p} : Set V3))) ?_
      have hncard : ({q - p, r - p} : Set V3).toFinset.card ≤ 2 := by
        have h1 : ({q - p, r - p} : Set V3).ncard
            ≤ ({r - p} : Set V3).ncard + 1 := Set.ncard_insert_le _ _
        have h2 : ({r - p} : Set V3).ncard = 1 := Set.ncard_singleton _
        have h3 : ({q - p, r - p} : Set V3).ncard
            = ({q - p, r - p} : Set V3).toFinset.card := Set.ncard_eq_toFinset_card' _
        omega
      exact hncard
    intro htop
    have hvec : vectorSpan ℝ ({p, q, r} : Set V3) = ⊤ := by
      rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
    have hfr : Module.finrank ℝ (vectorSpan ℝ ({p, q, r} : Set V3)) = 3 := by
      rw [hvec]
      simp
    omega
  have hnull : volume ((affineSpan ℝ ({p, q, r} : Set V3) : Set V3)) = 0 :=
    MeasureTheory.Measure.addHaar_affineSubspace volume _ hne
  have h0 : volume (mcell1 V ul) = 0 :=
    measure_mono_null hsub1 (measure_mono_null hspan hnull)
  exact h1 h0

/-- HOL `NOT_COPLANAR_R3` (TSKAJXY3.hl:452; proved 2026-09-29 wave A1:
`affDim s = 3` via the contrapositive of `AFF_DIM_LE_2_IMP_COPLANAR`
(PA6) and the `finrank`-characterisation of `affineSpan = ⊤`. -/
theorem NOT_COPLANAR_R3 (s : Set V3) (h : ¬Coplanar s) :
    (affineSpan ℝ s : Set V3) = Set.univ := by
  have hne : s ≠ ∅ := fun he => h (by rw [he]; exact coplanar_empty)
  have h3 : 3 ≤ affDim s := by
    by_contra hle
    exact h (AFF_DIM_LE_2_IMP_COPLANAR s (by
      simpa using show (affDim s : ℤ) ≤ 2 from by omega))
  have hle3 : affDim s ≤ 3 := by
    simp only [affDim, if_neg (nonempty_iff_ne_empty.1 (Set.nonempty_iff_ne_empty.2 hne))]
    have h1 : Module.finrank ℝ (vectorSpan ℝ s) ≤ 3 := by
      have h2 : Module.finrank ℝ (vectorSpan ℝ s)
          ≤ Module.finrank ℝ (⊤ : Submodule ℝ V3) := Submodule.finrank_mono le_top
      have h3 : Module.finrank ℝ (⊤ : Submodule ℝ V3) = Module.finrank ℝ V3 :=
        finrank_top ℝ V3
      have h4 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
      omega
    exact Nat.cast_le.2 h1
  have hfin3 : affDim s = 3 := le_antisymm hle3 h3
  have hdir : (affineSpan ℝ s : AffineSubspace ℝ V3).direction = ⊤ := by
    rw [direction_affineSpan]
    refine Submodule.eq_top_of_finrank_eq ?_
    have hfr : Module.finrank ℝ (vectorSpan ℝ s) = 3 := by
      have h4 := hfin3
      simp only [affDim, if_neg (nonempty_iff_ne_empty.1 (Set.nonempty_iff_ne_empty.2 hne))] at h4
      omega
    rw [hfr]
    exact (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)).symm
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have htop : (affineSpan ℝ s : AffineSubspace ℝ V3) = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty
      (⟨x, SetLike.mem_coe.2 (mem_affineSpan ℝ hx)⟩ :
        ((affineSpan ℝ s : AffineSubspace ℝ V3) : Set V3).Nonempty)).mp hdir
  rw [htop]
  rfl

/-- BARV-level distinctness of the first two entries (the
`voronoi_nondg` length bookkeeping: `[u0, u1]` and `[u0]` would force
`affDim (voronoiList V ·)` to be both `2` and `3`). -/
private theorem p21_el01_ne_of_barV {k : ℕ} (V : Set V3) (ul : List V3) (hb : barV V k ul)
    (hlen : ul.length = 2) : elV ul 0 ≠ elV ul 1 := by
  rcases ul with _ | ⟨a, t⟩
  · simp at hlen
  rcases t with _ | ⟨b, t⟩
  · simp at hlen
  have ht : t = [] := by
    simpa [List.length_cons] using hlen
  subst ht
  have hv1 : voronoiNondg V [a, b] := hb.2 [a, b] ⟨⟨[], rfl⟩, by simp⟩
  have hv0 : voronoiNondg V [a] := hb.2 [a] ⟨⟨[b], rfl⟩, by simp⟩
  have h1 : affDim (voronoiList V [a, b]) + (2 : ℤ) = 4 := by simpa using hv1.2.2
  have h2 : affDim (voronoiList V [a]) + (1 : ℤ) = 4 := by simpa using hv0.2.2
  intro heq
  have hset : setOfList [a, b] = setOfList [a] := by
    ext x
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨fun h => h.elim (fun h1 => h1) (fun h' => by rw [h']; exact heq.symm),
      fun h => Or.inl h⟩
  have hveq : voronoiList V [a, b] = voronoiList V [a] := by
    rw [voronoiList, voronoiList, hset]
  rw [hveq] at h1
  omega

/-- HOL `BARV_DISTINCT` (TSKAJXY3.hl:464; proved 2026-09-29 wave A1). -/
theorem BARV_DISTINCT (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 1 ul) : elV ul 0 ≠ elV ul 1 :=
  p21_el01_ne_of_barV V ul hb (by simpa using hb.1)

/-! ## Wave-A2 private kit: the omega tower in the pair Voronoi cell
(2026-09-29)

`OMEGA_LIST_BISECTOR` needs the three distance equalities
`dist (omegaListN V ul i) (EL 0 ul) = dist (omegaListN V ul i) (EL 1 ul)` for
`i = 1,2,3`.  HOL gets them from `Rogers.OMEGA_LIST_N_IN_VORONOI_LIST_GEN`
(the omega-tower projection kit, sorry-tainted at PA5/PA6).  We route around
it: each truncated `barV` list carries its own `voronoi_nondg` (hence a
NONEMPTY cell), so `closest_point` lands in the truncated cell by the epsilon
specification, and `VORONOI_SET_SUBSET` shrinks the larger truncated cells
down to the pair cell. -/

private theorem p21_vndg_trunc (V : Set V3) (ul : List V3) (hb : barV V 3 ul)
    (j : ℕ) (hj : j ≤ 3) : voronoiNondg V (truncateSimplex j ul) := by
  have hbar := TRUNCATE_SIMPLEX_BARV V j 3 ul hb hj
  exact hbar.2 (truncateSimplex j ul)
    (And.intro
      (⟨[], (List.append_nil (truncateSimplex j ul)).symm⟩ :
        ∃ yl : List V3, truncateSimplex j ul = truncateSimplex j ul ++ yl)
      (by rw [hbar.1]; omega))

private theorem p21_omega_in_voronoi_pair (V : Set V3) (ul : List V3)
    (hb : barV V 3 ul) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    omegaListN V ul j ∈ voronoiList V (truncateSimplex 1 ul) := by
  have hnd := p21_vndg_trunc V ul hb j hj3
  have hlen : (truncateSimplex j ul : List V3).length = j + 1 :=
    LENGTH_TRUNCATE_SIMPLEX j ul (by have := hb.1; omega)
  have hne : voronoiList V (truncateSimplex j ul) ≠ ∅ := by
    intro he
    rw [voronoiNondg, he, hlen] at hnd
    have hneg : (affDim (∅ : Set V3) : ℤ) = -1 := by simp [affDim]
    rw [hneg] at hnd
    omega
  -- the cell is complete and convex, so the distance to it attains its infimum
  have hconv : Convex ℝ (voronoiList V (truncateSimplex j ul)) := by
    simp only [voronoiList, voronoiSet]
    refine convex_sInter ?_
    rintro S ⟨v, _, rfl⟩
    exact CONVEX_VORONOI_CLOSED V v
  have hcomp : IsComplete (voronoiList V (truncateSimplex j ul)) :=
    (CLOSED_VORONOI_LIST V (truncateSimplex j ul)).isComplete
  have hneS : (voronoiList V (truncateSimplex j ul) : Set V3).Nonempty :=
    Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨y, hyK, hymin⟩ := exists_norm_eq_iInf_of_complete_convex hneS hcomp hconv
    (omegaListN V ul (j - 1))
  have hex : ∃ y : V3, y ∈ voronoiList V (truncateSimplex j ul) ∧
      ∀ z ∈ voronoiList V (truncateSimplex j ul),
        dist (omegaListN V ul (j - 1)) y ≤ dist (omegaListN V ul (j - 1)) z := by
    refine ⟨y, hyK, ?_⟩
    intro z hz
    have hbb : BddBelow (Set.range fun w : ({y | y ∈ voronoiList V (truncateSimplex j ul)} : Set V3) =>
        ‖omegaListN V ul (j - 1) - (w : V3)‖) :=
      ⟨0, by rintro w ⟨v, rfl⟩; exact norm_nonneg _⟩
    have hle := ciInf_le hbb
      (⟨z, hz⟩ : ({y | y ∈ voronoiList V (truncateSimplex j ul)} : Set V3))
    rw [dist_eq_norm, dist_eq_norm, hymin]
    exact hle
  have hrw : omegaListN V ul j
      = closestPoint (voronoiList V (truncateSimplex j ul))
          (omegaListN V ul (j - 1)) := by
    have hj : j = (j - 1) + 1 := by omega
    rw [hj]
    rfl
  have hmem : omegaListN V ul j ∈ voronoiList V (truncateSimplex j ul) := by
    rw [hrw]
    exact (Classical.epsilon_spec hex).1
  exact VORONOI_SET_SUBSET V (setOfList (truncateSimplex 1 ul))
    (setOfList (truncateSimplex j ul))
    (TRUNCATE_SIMPLEX_SUBSET ul j 1 hj1 (by have := hb.1; omega)) hmem

/-- The four omega points, as an explicit quadruple with the head first, are
not coplanar (repackaging of `NOT_COPLANAR_OMEGA_LIST_N`). -/
private theorem p21_omega4_ncp (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (h1 : ¬nullSet (mcell1 V ul)) :
    ¬Coplanar ({hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} : Set V3) := by
  have h := NOT_COPLANAR_OMEGA_LIST_N V ul hp hs hb h1
  refine fun hc => h ?_
  rw [IMAGE_4_EXPLICIT]
  exact hc

/-- A non-coplanar quadruple `p, q1, q2, q3` has its vertex differences
spanning the whole space (the affine hull is everything, and the direction of
the affine hull is dominated by the three differences). -/
private theorem p21_span3_top {p q1 q2 q3 : V3}
    (hcp : ¬Coplanar ({p, q1, q2, q3} : Set V3)) :
    Submodule.span ℝ ({q1 - p, q2 - p, q3 - p} : Set V3) = ⊤ := by
  have huniv : (affineSpan ℝ ({p, q1, q2, q3} : Set V3) : Set V3) = Set.univ :=
    NOT_COPLANAR_R3 _ hcp
  have htopA : (affineSpan ℝ ({p, q1, q2, q3} : Set V3) : AffineSubspace ℝ V3) = ⊤ := by
    rw [AffineSubspace.ext_iff, AffineSubspace.top_coe]
    exact huniv
  have hdir : (affineSpan ℝ ({p, q1, q2, q3} : Set V3) : AffineSubspace ℝ V3).direction = ⊤ := by
    rw [htopA, AffineSubspace.direction_top]
  have hle : vectorSpan ℝ ({p, q1, q2, q3} : Set V3)
      ≤ Submodule.span ℝ ({q1 - p, q2 - p, q3 - p} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_left (k := ℝ)
      (Set.mem_insert p ({q1, q2, q3} : Set V3)), Submodule.span_le]
    have himg : ∀ x ∈ ({p, q1, q2, q3} : Set V3),
        (p - x : V3) ∈ Submodule.span ℝ ({q1 - p, q2 - p, q3 - p} : Set V3) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx1 | hx1 | hx1 | hx1
      · rw [hx1]
        simp
      · rw [hx1]
        have hneg : p - q1 = -(q1 - p) := by abel
        rw [hneg]
        exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_insert _ _))
      · rw [hx1]
        have hneg : p - q2 = -(q2 - p) := by abel
        rw [hneg]
        exact Submodule.neg_mem _ (Submodule.subset_span
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      · rw [hx1]
        have hmem : (q3 - p : V3) ∈ Submodule.span ℝ ({q1 - p, q2 - p, q3 - p} : Set V3) :=
          Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
            (Set.mem_singleton _)))
        have hneg : p - q3 = -(q3 - p) := by abel
        rw [hneg]
        exact Submodule.neg_mem _ hmem
    rintro z ⟨x, hx, rfl⟩
    exact himg x hx
  have htop : (⊤ : Submodule ℝ V3)
      ≤ Submodule.span ℝ ({q1 - p, q2 - p, q3 - p} : Set V3) := by
    rw [← hdir, direction_affineSpan]
    exact hle
  exact le_antisymm le_top htop

/-- The double-subtraction dot split (ofLp-robust form used by the wave-A2
dot bookkeeping; `show` normalizes the `⬝ᵥ`-elaboration first). -/
private theorem p21e_split_both (a b c d : V3) :
    (a - b) ⬝ᵥ (c - d) = a ⬝ᵥ c - a ⬝ᵥ d - (b ⬝ᵥ c - b ⬝ᵥ d) := by
  show dotProduct (WithLp.ofLp (a - b)) (WithLp.ofLp (c - d))
      = dotProduct (WithLp.ofLp a) (WithLp.ofLp c)
        - dotProduct (WithLp.ofLp a) (WithLp.ofLp d)
        - (dotProduct (WithLp.ofLp b) (WithLp.ofLp c)
          - dotProduct (WithLp.ofLp b) (WithLp.ofLp d))
  rw [WithLp.ofLp_sub, WithLp.ofLp_sub, p21_dotPi_sub_l, p21_dotPi_sub_r,
    p21_dotPi_sub_r]

/-- Squares agree iff values agree, for nonneg reals (early copy of the
private `p21_sq_eq`, which sits later in this file). -/
private theorem p21e_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b ↔ a ^ 2 = b ^ 2 := by
  constructor
  · intro h; rw [h]
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · nlinarith [h, hlt, ha]
    · nlinarith [h, hgt, hb]

/-- The tower points `ω1, ω2, ω3` are equidistant from the first two list
entries (pair-Voronoi membership from `p21_omega_in_voronoi_pair`). -/
private theorem p21_omega_dist_eq (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    dist (omegaListN V ul j) (elV ul 0) = dist (omegaListN V ul j) (elV ul 1) := by
  have htr1 : truncateSimplex 1 ul = [elV ul 0, elV ul 1] := by
    obtain ⟨a, b, c, d, rfl⟩ := BARV_3_EXPLICIT V ul hb
    exact (TRUNCATE_SIMPLEX_EXPLICIT_1 a b c d).2.2
  have hmem := p21_omega_in_voronoi_pair V ul hb j hj1 hj3
  rw [htr1] at hmem
  have hset : setOfList [elV ul 0, elV ul 1] = ({elV ul 0, elV ul 1} : Set V3) := by
    ext z
    simp [setOfList]
  simp only [voronoiList, voronoiSet, Set.mem_sInter] at hmem
  rw [hset] at hmem
  have hsub : ({elV ul 0, elV ul 1} : Set V3) ⊆ V := by
    have hnd := p21_vndg_trunc V ul hb 1 (by omega)
    rw [htr1] at hnd
    rw [voronoiNondg, hset] at hnd
    exact hnd.2.1
  have h0 := hmem (voronoiClosed V (elV ul 0)) ⟨elV ul 0, by simp, rfl⟩
  have h1 := hmem (voronoiClosed V (elV ul 1)) ⟨elV ul 1, by simp, rfl⟩
  simp only [voronoiClosed, Set.mem_setOf_eq] at h0 h1
  exact le_antisymm (h0 (elV ul 1) (hsub (by simp))) (h1 (elV ul 0) (hsub (by simp)))

/-- HOL `OMEGA_LIST_BISECTOR` (TSKAJXY3.hl:495; proved 2026-09-29 wave A2:
the face `{ω1,ω2,ω3}` spans the bisector half-space — distance equalities
from the pair-Voronoi kit `p21_omega_dist_eq`, the half-space pivoting on
`p21_dist_le_half2`, and the affine decomposition of an arbitrary point from
the span lemma `p21_span3_top`). -/
theorem OMEGA_LIST_BISECTOR (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (h1 : ¬nullSet (mcell1 V ul)) :
    affGe {omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} ({elV ul 0} : Set V3)
      = bisLe (elV ul 0) (elV ul 1) := by
  classical
  obtain ⟨u0, u1, u2, u3, rflu⟩ := BARV_3_EXPLICIT V ul hb
  subst rflu
  have hdV0 : hdV ([u0, u1, u2, u3] : List V3) = u0 := rfl
  have hncp := p21_omega4_ncp V [u0, u1, u2, u3] hp hs hb h1
  rw [hdV0] at hncp
  have hd := p21_ne_of_notCoplanar hncp
  have hbar1 : barV V 1 [u0, u1] := by
    rw [← (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
    exact TRUNCATE_SIMPLEX_BARV V 1 3 [u0, u1, u2, u3] hb (by omega)
  have hd01 : u0 ≠ u1 := BARV_DISTINCT V [u0, u1] hp hs hbar1
  have hdeq := p21_omega_dist_eq V [u0, u1, u2, u3] hp hs hb
  -- each tower point sits at half the axis-squared distance from `u0`
  have hdot : ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      (omegaListN V [u0, u1, u2, u3] i - u0) ⬝ᵥ (u1 - u0) = ‖u1 - u0‖ ^ 2 / 2 := by
    intro i hi1 hi3
    have hdi := hdeq i hi1 hi3
    have hsq : ‖omegaListN V [u0, u1, u2, u3] i - u1‖ ^ 2
        = ‖omegaListN V [u0, u1, u2, u3] i - u0‖ ^ 2 := by
      rw [← p21e_sq_eq (norm_nonneg _) (norm_nonneg _), ← dist_eq_norm, ← dist_eq_norm]
      exact hdi.symm
    have e0 := p21_sq_sub (omegaListN V [u0, u1, u2, u3] i) u0
    have e1 := p21_sq_sub (omegaListN V [u0, u1, u2, u3] i) u1
    have h2 : 2 * (omegaListN V [u0, u1, u2, u3] i ⬝ᵥ u1
        - omegaListN V [u0, u1, u2, u3] i ⬝ᵥ u0) = u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0 := by
      rw [e0, e1] at hsq
      linarith
    have dn0 := p21_sq_sub u1 u0
    have dnc : u1 ⬝ᵥ u0 = u0 ⬝ᵥ u1 := p21_dot_comm u1 u0
    rw [dnc] at dn0
    have hexp : (omegaListN V [u0, u1, u2, u3] i - u0) ⬝ᵥ (u1 - u0)
        = omegaListN V [u0, u1, u2, u3] i ⬝ᵥ u1 - omegaListN V [u0, u1, u2, u3] i ⬝ᵥ u0
          - (u0 ⬝ᵥ u1 - u0 ⬝ᵥ u0) := by
      rw [p21e_split_both]
    rw [hexp]
    linarith
  -- the half-plane pivoting: the `u0`-weight is nonnegative iff the point is
  -- on the `u0` side of the bisector
  have hhalf : ∀ (x : V3) (t1 t2 t3 t4 : ℝ), t1 + t2 + t3 + t4 = 1 →
      x = t4 • u0 + t1 • omegaListN V [u0, u1, u2, u3] 1
        + t2 • omegaListN V [u0, u1, u2, u3] 2
        + t3 • omegaListN V [u0, u1, u2, u3] 3 →
      (0 ≤ t4 ↔ dist x u0 ≤ dist x u1) := by
    intro x t1 t2 t3 t4 hsum hxy
    have h1' : t1 + t2 + t3 = 1 - t4 := by linarith
    have hk : (0:ℝ) < ‖u1 - u0‖ ^ 2 / 2 := by
      have h1 : (0:ℝ) < ‖u1 - u0‖ := by
        rw [← dist_eq_norm]
        exact dist_pos.2 (Ne.symm hd01)
      exact div_pos (sq_pos_of_ne_zero (ne_of_gt h1)) (by norm_num)
    have hxd : x - u0
        = t1 • (omegaListN V [u0, u1, u2, u3] 1 - u0)
          + t2 • (omegaListN V [u0, u1, u2, u3] 2 - u0)
          + t3 • (omegaListN V [u0, u1, u2, u3] 3 - u0) := by
      rw [hxy, show t4 = 1 - t1 - t2 - t3 from by linarith]
      module
    have hdotx : (x - u0) ⬝ᵥ (u1 - u0) = (1 - t4) * (‖u1 - u0‖ ^ 2 / 2) := by
      rw [hxd, p21_add_dot_whole, p21_add_dot_whole, p21_smul_dot, p21_smul_dot,
        p21_smul_dot, hdot 1 (by omega) (by omega), hdot 2 (by omega) (by omega),
        hdot 3 (by omega) (by omega)]
      have hswap : (t1 + t2 + t3) * (‖u1 - u0‖ ^ 2 / 2)
          = t1 * (‖u1 - u0‖ ^ 2 / 2) + t2 * (‖u1 - u0‖ ^ 2 / 2)
            + t3 * (‖u1 - u0‖ ^ 2 / 2) := by
        ring
      rw [← hswap, h1']
    constructor
    · -- `0 ≤ t4` forces the half-plane side, hence the bisector inequality
      intro hle
      refine (p21_dist_le_half2 x u0 u1).2 ?_
      rw [hdotx, show (1 - t4) * (‖u1 - u0‖ ^ 2 / 2)
          = ‖u1 - u0‖ ^ 2 / 2 - t4 * (‖u1 - u0‖ ^ 2 / 2) from by ring]
      have hprod : 0 ≤ t4 * (‖u1 - u0‖ ^ 2 / 2) := by nlinarith
      linarith
    · -- the bisector inequality forces `0 ≤ t4`
      intro h4
      have h2 := (p21_dist_le_half2 x u0 u1).1 h4
      rw [hdotx, show (1 - t4) * (‖u1 - u0‖ ^ 2 / 2)
          = ‖u1 - u0‖ ^ 2 / 2 - t4 * (‖u1 - u0‖ ^ 2 / 2) from by ring] at h2
      have hprod : 0 ≤ t4 * (‖u1 - u0‖ ^ 2 / 2) := by linarith
      by_cases h : 0 ≤ t4
      · exact h
      · exact absurd (by nlinarith : t4 * (‖u1 - u0‖ ^ 2 / 2) < 0) (by linarith)
  ext x
  constructor
  · intro hx
    obtain ⟨s0, s1, s2, s3, hs0, hssum, hsy⟩ := (p21_affGe_3_1_char hd x).mp hx
    have hssum' : s1 + s2 + s3 + s0 = 1 := by linarith
    exact (hhalf x s1 s2 s3 s0 hssum' hsy).1 hs0
  · intro hx
    have hrange : Set.range (![omegaListN V [u0, u1, u2, u3] 1 - u0,
        omegaListN V [u0, u1, u2, u3] 2 - u0, omegaListN V [u0, u1, u2, u3] 3 - u0] : Fin 3 → V3)
        = ({omegaListN V [u0, u1, u2, u3] 1 - u0, omegaListN V [u0, u1, u2, u3] 2 - u0,
          omegaListN V [u0, u1, u2, u3] 3 - u0} : Set V3) := by
      ext y
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    have hx' : x - u0
        ∈ Submodule.span ℝ ({omegaListN V [u0, u1, u2, u3] 1 - u0,
          omegaListN V [u0, u1, u2, u3] 2 - u0, omegaListN V [u0, u1, u2, u3] 3 - u0} : Set V3) := by
      rw [p21_span3_top hncp]
      exact Submodule.mem_top
    rw [← hrange] at hx'
    obtain ⟨t, ht⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (x := x - u0)).1 hx'
    have ht' : x - u0 = t 0 • (omegaListN V [u0, u1, u2, u3] 1 - u0)
        + t 1 • (omegaListN V [u0, u1, u2, u3] 2 - u0)
        + t 2 • (omegaListN V [u0, u1, u2, u3] 3 - u0) := by
      simpa [Fin.sum_univ_three] using ht.symm
    have hxy2 : x = (1 - (t 0 + t 1 + t 2)) • u0
        + t 0 • omegaListN V [u0, u1, u2, u3] 1
        + t 1 • omegaListN V [u0, u1, u2, u3] 2
        + t 2 • omegaListN V [u0, u1, u2, u3] 3 := by
      calc x = u0 + (x - u0) := by abel
        _ = u0 + (t 0 • (omegaListN V [u0, u1, u2, u3] 1 - u0)
            + t 1 • (omegaListN V [u0, u1, u2, u3] 2 - u0)
            + t 2 • (omegaListN V [u0, u1, u2, u3] 3 - u0)) := by rw [ht']
        _ = (1 - (t 0 + t 1 + t 2)) • u0 + t 0 • omegaListN V [u0, u1, u2, u3] 1
            + t 1 • omegaListN V [u0, u1, u2, u3] 2
            + t 2 • omegaListN V [u0, u1, u2, u3] 3 := by
            module
    have hsum2 : t 0 + t 1 + t 2 + (1 - (t 0 + t 1 + t 2)) = 1 := by ring
    have hsum3 : (1 - (t 0 + t 1 + t 2)) + t 0 + t 1 + t 2 = 1 := by ring
    have h4 := (hhalf x (t 0) (t 1) (t 2) (1 - (t 0 + t 1 + t 2)) hsum2 hxy2).2 hx
    exact (p21_affGe_3_1_char hd x).mpr
      ⟨1 - (t 0 + t 1 + t 2), t 0, t 1, t 2, h4, hsum3, hxy2⟩

/-- HOL `DIFF_INTER` (TSKAJXY3.hl:589). -/
theorem DIFF_INTER (X Y Z : Set V3) : (X \ Y) ∩ Z = (X ∩ Z) \ Y := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff]
  tauto

/-- HOL `BARV3_TRUNC1` (TSKAJXY3.hl:612). -/
theorem BARV3_TRUNC1 (V : Set V3) (ul : List V3) (hb : barV V 3 ul) :
    truncateSimplex 1 ul = [elV ul 0, elV ul 1] := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  exact (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2


/-- Pushed-coercion smul-dot identity (copy of the private
`p21_smul_dotP`, which is defined later in this file). -/
private theorem p21e_smul_dotP (t : ℝ) (a b c : V3) :
    (t • a).ofLp ⬝ᵥ (b.ofLp - c.ofLp)
      = t * ((a.ofLp ⬝ᵥ b.ofLp) - (a.ofLp ⬝ᵥ c.ofLp)) := by
  rw [show WithLp.ofLp b - WithLp.ofLp c = WithLp.ofLp (b - c) from
    (WithLp.ofLp_sub 2 b c).symm, p21_smul_dot t a (b - c), WithLp.ofLp_sub 2 b c,
    p21_dot_sub_whole a b c]

/-- Copy of `RCONE_GT_SCALE` (which sits later in this file): strict-cone
membership is positively homogeneous along rays from the apex. -/
private theorem p21e_rcone_gt_scale (u0 u1 u : V3) (a t : ℝ) (ht : 0 < t)
    (h : u0 + u ∈ rconeGt u0 u1 a) : u0 + t • u ∈ rconeGt u0 u1 a := by
  have hmem := h
  unfold rconeGt at hmem
  rw [Set.mem_setOf_eq] at hmem
  rw [show u0 + u - u0 = u from by abel, dist_eq_norm,
    show u0 + u - u0 = u from by abel] at hmem
  unfold rconeGt
  rw [Set.mem_setOf_eq]
  rw [show u0 + t • u - u0 = t • u from by abel, p21e_smul_dotP t u u1 u0,
    dist_eq_norm, show u0 + t • u - u0 = t • u from by abel, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht]
  have hdot := p21_dot_sub_whole u u1 u0
  rw [← hdot, gt_iff_lt]
  have h2 : t * ‖u‖ * dist u1 u0 * a < t * (u.ofLp ⬝ᵥ (u1.ofLp - u0.ofLp)) := by
    have hh := mul_lt_mul_of_pos_left hmem ht
    have hEq : t * (‖u‖ * dist u1 u0 * a) = t * ‖u‖ * dist u1 u0 * a := by ring
    linarith
  exact h2

/-- HOL `MCELL1_RADIAL` (TSKAJXY3.hl:624; proved 2026-09-29 wave A2: the
radial ray from `u0` through a point of `mcell1` stays in `rogers` by
`CONVEX_HULL_SCALE`, whose `affGe` side-condition is `OMEGA_LIST_BISECTOR`
plus `BALL_DIFF_RCONE_GT_BISECTOR`; the cone part dies by the contrapositive
of `RCONE_GT_SCALE`). -/
theorem MCELL1_RADIAL (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell1 V ul) (hn : ¬nullSet X) :
    radialNorm (Real.sqrt 2) (elV ul 0) (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
  classical
  obtain ⟨u0, u1, u2, u3, rflu⟩ := BARV_3_EXPLICIT V ul hb
  subst rflu
  have h1 : ¬nullSet (mcell1 V [u0, u1, u2, u3]) := by rw [← hX]; exact hn
  have hncp := p21_omega4_ncp V [u0, u1, u2, u3] hp hs hb h1
  refine ⟨Set.inter_subset_right, ?_⟩
  intro u hu t ht htn
  obtain ⟨hx, _⟩ := hu
  have hballmem : u0 + t • u ∈ Metric.ball u0 (Real.sqrt 2) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    exact htn
  rw [hX, MCELL1_EXPLICIT V (mcell1 V [u0, u1, u2, u3]) [u0, u1, u2, u3] hs hp hb rfl
    (by rw [← hX]; exact hn)] at hx
  rw [show hdV ([u0, u1, u2, u3] : List V3) = u0 from rfl,
    show hdV ([u0, u1, u2, u3].tail : List V3) = u1 from rfl,
    show elV [u0, u1, u2, u3] 0 = u0 from rfl] at hx
  obtain ⟨⟨hR, hcb⟩, hcon⟩ := hx
  -- the ray-homogeneity contrapositive: a scaled ray point in the cone pulls
  -- the original point back into the cone
  have hconeBack : u0 + t • u
      ∈ rconeGt u0 u1 (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) →
      u0 + u ∈ rconeGt u0 u1 (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) := by
    intro hmem
    have hsc := p21e_rcone_gt_scale u0 u1 (t • u)
      (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) (1 / t)
      (div_pos (by norm_num : (0:ℝ) < 1) ht) hmem
    rwa [smul_smul, show (1:ℝ) / t * t = 1 from by field_simp, one_smul] at hsc
  rw [hX, MCELL1_EXPLICIT V (mcell1 V [u0, u1, u2, u3]) [u0, u1, u2, u3] hs hp hb rfl
    (by rw [← hX]; exact hn)]
  rw [show hdV ([u0, u1, u2, u3] : List V3) = u0 from rfl,
    show hdV ([u0, u1, u2, u3].tail : List V3) = u1 from rfl,
    show elV [u0, u1, u2, u3] 0 = u0 from rfl]
  -- the Rogers simplex is the hull of the four omega points
  have h4 : ([u0, u1, u2, u3] : List V3).length = 4 := rfl
  have himg4 : omegaListN V [u0, u1, u2, u3] '' {j : ℕ | j < ([u0, u1, u2, u3] : List V3).length}
      ⊆ ({u0, omegaListN V [u0, u1, u2, u3] 1, omegaListN V [u0, u1, u2, u3] 2,
        omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
    rintro y ⟨j, hj, rfl⟩
    have hj4 : j < 4 := by simpa [h4] using hj
    interval_cases j
    · exact Or.inl rfl
    · exact Set.mem_insert_of_mem _ (Or.inl rfl)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Or.inl rfl))
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hsub4 : ({u0, omegaListN V [u0, u1, u2, u3] 1, omegaListN V [u0, u1, u2, u3] 2,
      omegaListN V [u0, u1, u2, u3] 3} : Set V3)
      ⊆ omegaListN V [u0, u1, u2, u3] '' {j : ℕ | j < ([u0, u1, u2, u3] : List V3).length} := by
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩
  have hreq : rogers V [u0, u1, u2, u3]
      = convexHull ℝ ({u0, omegaListN V [u0, u1, u2, u3] 1,
        omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
    rw [rogers]
    exact congrArg (convexHull ℝ) (Set.Subset.antisymm himg4 hsub4)
  rw [hreq, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_inter_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the Rogers-simplex part, via CONVEX_HULL_SCALE + OMEGA_LIST_BISECTOR
    rw [show u = u0 + u - u0 from (by abel : u0 + u - u0 = u).symm]
    rw [hreq] at hR
    refine CONVEX_HULL_SCALE u0 (omegaListN V [u0, u1, u2, u3] 1)
      (omegaListN V [u0, u1, u2, u3] 2) (omegaListN V [u0, u1, u2, u3] 3) (u0 + u) t hncp hR
      (le_of_lt ht) ?_
    rw [show u0 + u - u0 = u from by abel]
    have hvel : elV [u0, u1, u2, u3] 0 = u0 := rfl
    have homega := OMEGA_LIST_BISECTOR V [u0, u1, u2, u3] hp hs hb h1
    rw [hvel] at homega
    rw [homega]
    show dist (u0 + t • u) u0 ≤ dist (u0 + t • u) u1
    refine BALL_DIFF_RCONE_GT_BISECTOR u0 u1 (u0 + t • u) (Real.sqrt 2)
      (hl (truncateSimplex 1 [u0, u1, u2, u3])) ⟨hballmem, ?_⟩ ?_
      (Real.sqrt_pos.2 (by norm_num))
    · intro hmem
      exact hcon (hconeBack hmem)
    · rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2, HL_2 u0 u1, dist_comm u0 u1]
      ring
  · -- the closed-ball part
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htn.le
  · -- the strict-cone part dies by ray homogeneity
    intro hmem
    exact hcon (hconeBack hmem)
  · -- the open-ball part of the intersection
    exact hballmem

/-- HOL `MCELL1_SOL_RESTRICT` (TSKAJXY3.hl:285; proved 2026-09-30: both `sol`
values are evaluated at the common radius `sqrt 2` via `sol_spec` — the
`MCELL1_RADIAL` kit (whose file-order blockage is closed by hoisting the
wave-A1/A2 kit ahead of this theorem) makes both instances of `sol_spec`
evaluate on the very same restricted set). -/
theorem MCELL1_SOL_RESTRICT (V X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell1 V ul)
    (hn : ¬nullSet X) :
    sol (elV ul 0) X =
      sol (elV ul 0) (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
  have hmeas : MeasurableSet X := by
    rw [hX]; exact MEASURABLE_MCELL V ul 1 hs hp hb
  have hmeas2 : MeasurableSet (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) :=
    hmeas.inter Metric.isOpen_ball.measurableSet
  have hrad := MCELL1_RADIAL V X ul hs hp hb hX hn
  -- the restricted set is radial in its own right (double ball collapses)
  have hbb : (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) ∩
      Metric.ball (elV ul 0) (Real.sqrt 2)
      = X ∩ Metric.ball (elV ul 0) (Real.sqrt 2) := by
    rw [Set.inter_assoc, Set.inter_self]
  have h1 := sol_spec (x := elV ul 0) (C := X) (r := Real.sqrt 2)
    (Real.sqrt_pos.2 (by norm_num)) hmeas2 hrad
  have h2 := sol_spec (x := elV ul 0)
    (C := X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) (r := Real.sqrt 2)
    (Real.sqrt_pos.2 (by norm_num)) (by rw [hbb]; exact hmeas2)
    (by rw [hbb]; exact hrad)
  rw [h1, h2, hbb]

/-- HOL `CONV_CONVEX_HULL` (TSKAJXY3.hl:328). -/
theorem CONV_CONVEX_HULL (s : Set V3) : Convex ℝ s ↔ (convexHull ℝ s : Set V3) = s := by
  constructor
  · intro h
    exact Subset.antisymm (convexHull_min le_rfl h) (subset_convexHull ℝ s)
  · intro h
    rw [← h]
    exact convex_convexHull ℝ s

/-- HOL `MCELL1_VOL` (TSKAJXY3.hl:731; proved 2026-09-29 wave A2: both `sol`
values are evaluated at the common radius `sqrt 2` via `sol_spec`, using
`MCELL1_VOL_RESTRICT` and `MCELL1_RADIAL`). -/
theorem MCELL1_VOL (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell1 V ul) (hn : ¬nullSet X) :
    volume.real X = Real.sqrt 2 ^ 3 / 3 * sol (elV ul 0) X := by
  have hres := MCELL1_VOL_RESTRICT V X ul hs hp hb hX hn
  have hrad := MCELL1_RADIAL V X ul hs hp hb hX hn
  have hmeas : MeasurableSet (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
    rw [hX]
    exact (MEASURABLE_MCELL V ul 1 hs hp hb).inter Metric.isOpen_ball.measurableSet
  have hsol := sol_spec (x := elV ul 0) (C := X) (r := Real.sqrt 2)
    (Real.sqrt_pos.2 (by norm_num)) hmeas hrad
  rw [hres, hsol]
  have h2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

-- atn2-merge: `HJKDESR1a_1cell` (TSKAJXY3.hl:766 = TSKAJXY1.hl:5652) is
-- byte-identical to PackingAuto20.lean's declaration; with the hub now
-- imported above, its copy serves both files (plan §5.3).

/-- HOL `TSKAJXY_1` (TSKAJXY3.hl:780; proved 2026-09-29 wave A2: `GAMMAX_MCELL1`
+ `MCELL1_VOL` factor `gammaX = sol · (sqrt2^3/3 - 2·mm1/π)`, the bracket
positive by the PA20 numeric seed `HJKDESR1a_1cell`). -/
theorem TSKAJXY_1 (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) : gammaX V (mcell1 V ul) lmfun ≥ 0 := by
  by_cases hnull : nullSet (mcell1 V ul)
  · rw [GAMMAX_NULLSET V lmfun (mcell1 V ul) ul 1 hs hp hb (BumpP4.MCELL1 V ul) hnull]
  · have hv := GAMMAX_MCELL1 V (mcell1 V ul) ul hs hp hb rfl hnull
    have hv1 := MCELL1_VOL V (mcell1 V ul) ul hs hp hb rfl hnull
    -- the solid angle is nonnegative (three times a volume over a positive cube)
    have hsolnn : 0 ≤ sol (elV ul 0) (mcell1 V ul) := by
      have hvolnn : 0 ≤ volume.real (mcell1 V ul) := by
        rw [Measure.real_def]
        exact ENNReal.toReal_nonneg
      have hpos : (0:ℝ) < Real.sqrt 2 ^ 3 / 3 := by positivity
      have h2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
      have hform : sol (elV ul 0) (mcell1 V ul)
          = volume.real (mcell1 V ul) / (Real.sqrt 2 ^ 3 / 3) := by
        rw [hv1]
        field_simp
      rw [hform]
      exact div_nonneg hvolnn (le_of_lt hpos)
    have h8 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
        Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      rw [show (3:ℕ) = 2 + 1 from rfl, pow_add, pow_two, pow_one, h2sq]
    have hmm : mm1 < Real.pi * Real.sqrt 2 / 3 := by
      have hH := HJKDESR1a_1cell
      linarith
    have hdiff : 0 < Real.sqrt 2 ^ 3 / 3 - 2 * mm1 / Real.pi := by
      rw [h8]
      have h2' : (3:ℝ) * mm1 < Real.pi * Real.sqrt 2 := by linarith
      have hdiv : 2 * mm1 / Real.pi < 2 * Real.sqrt 2 / 3 := by
        refine div_lt_iff₀ Real.pi_pos |>.2 ?_
        nlinarith [Real.sqrt_pos.2 (show (0:ℝ) < 2 by norm_num)]
      linarith
    have hkey : sol (elV ul 0) (mcell1 V ul)
        * (Real.sqrt 2 ^ 3 / 3 - 2 * mm1 / Real.pi)
        = Real.sqrt 2 ^ 3 / 3 * sol (elV ul 0) (mcell1 V ul)
          - 2 * mm1 / Real.pi * sol (elV ul 0) (mcell1 V ul) := by ring
    rw [ge_iff_le, hv, hv1, ← hkey]
    exact mul_nonneg hsolnn hdiff.le

/-! ## cell_params_d uniqueness kit → moved to PackingAuto20 (suite-move A′, 2026-10-09) -/

/-- HOL `INITIAL_SUBLIST_2` (TSKAJXY3.hl:868). -/
theorem INITIAL_SUBLIST_2 (ul : List V3) (h : ul.length = 4) :
    initialSublist [elV ul 0, elV ul 1] ul := by
  rcases ul with _ | ⟨a, t⟩
  · simp at h
  rcases t with _ | ⟨b, t⟩
  · simp at h
  rcases t with _ | ⟨c, t⟩
  · simp at h
  rcases t with _ | ⟨d, t⟩
  · simp at h
  · simp [initialSublist, elV]

/-- HOL `MCELL2_CELL_PARAMETERS_EXIST` (TSKAJXY3.hl:884; proved 2026-09-29
wave B1: `MCELL_CELL_PARAMETERS_D_EXIST` at `k = 2` with the pair as the
initial sublist, via `INITIAL_SUBLIST_2`). -/
theorem MCELL2_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hX : X = mcell2 V ul) (hb : barV V 3 ul)
    (hn : ¬nullSet X) : (cellParamsD V X [elV ul 0, elV ul 1]).1 = 2 := by
  refine MCELL_CELL_PARAMETERS_D_EXIST V ul [elV ul 0, elV ul 1] 2 X (by norm_num) hp hs
    ?_ hb (INITIAL_SUBLIST_2 ul (by simpa using hb.1)) hn
  rw [hX, BumpP4.MCELL2]

/-- HOL `MCELL2_PARAM_D_UL` (TSKAJXY3.hl:923; proved 2026-09-29 wave B1:
`MCELL_PARAM_D_UL` at `k = 2`). -/
theorem MCELL2_PARAM_D_UL (V : Set V3) (ul ul' vl : List V3) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hX : X = mcell2 V ul) (hb : barV V 3 ul)
    (hn : ¬nullSet X) (his : initialSublist ul' ul)
    (hvl : vl = (cellParamsD V X ul').2) :
    X = mcell2 V vl ∧ barV V 3 vl ∧ initialSublist ul' vl := by
  have hres := MCELL_PARAM_D_UL V ul ul' vl X 2 (by norm_num) hp hs hX hb hn his hvl
  rw [BumpP4.MCELL2]
  exact hres

/-- HOL `MCELL2_DIHX` (TSKAJXY3.hl:936; proved 2026-09-29 wave B1: the
`cellParamsD` witness at `k = 2` has the same first two entries and, by the
cell-rigidity kit (`MCELL_ID_MXI_2` / `MCELL_ID_OMEGA_LIST_N`, PA15), the
same `mxi` and `omega_list_n 3`, so `dihX` folds back to `dihu2 V ul`). -/
theorem MCELL2_DIHX (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    dihX V X (elV ul 0, elV ul 1) =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) := by
  have hq1 : (cellParamsD V X [elV ul 0, elV ul 1]).1 = 2 :=
    MCELL2_CELL_PARAMETERS_EXIST V ul X hp hs hX hb hn
  have hex : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧
      initialSublist [elV ul 0, elV ul 1] p.2 := ⟨(2, ul), by norm_num, hb,
    by rw [hX, BumpP4.MCELL2], INITIAL_SUBLIST_2 ul (by simpa using hb.1)⟩
  have heps := Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧
      initialSublist [elV ul 0, elV ul 1] p.2) hex
  have hb1 : barV V 3 (cellParamsD V X [elV ul 0, elV ul 1]).2 := heps.2.1
  have heq1 : (cellParamsD V X [elV ul 0, elV ul 1]).1 = 2 := hq1
  have hinit : initialSublist [elV ul 0, elV ul 1]
      (cellParamsD V X [elV ul 0, elV ul 1]).2 := heps.2.2.2
  -- the witness list starts with the same two points
  have hpre : elV (cellParamsD V X [elV ul 0, elV ul 1]).2 0 = elV ul 0 ∧
      elV (cellParamsD V X [elV ul 0, elV ul 1]).2 1 = elV ul 1 := by
    obtain ⟨yl, hy⟩ := hinit
    rw [hy]
    exact ⟨by simp [elV, List.getD_append], by simp [elV, List.getD_append]⟩
  have hXw : X = mcell (cellParamsD V X [elV ul 0, elV ul 1]).1
      V (cellParamsD V X [elV ul 0, elV ul 1]).2 := heps.2.2.1
  have hXe : mcell 2 V (cellParamsD V X [elV ul 0, elV ul 1]).2 = mcell 2 V ul := by
    have h5 : mcell (cellParamsD V X [elV ul 0, elV ul 1]).1
        V (cellParamsD V X [elV ul 0, elV ul 1]).2
        = mcell 2 V (cellParamsD V X [elV ul 0, elV ul 1]).2 :=
      congrArg (fun i : ℕ => mcell i V (cellParamsD V X [elV ul 0, elV ul 1]).2) heq1
    exact Eq.trans h5.symm (Eq.trans hXw.symm (Eq.trans hX (BumpP4.MCELL2 V ul)))
  have hd : ¬nullSet (mcell 2 V (cellParamsD V X [elV ul 0, elV ul 1]).2) := by
    rw [hXe]
    intro hc
    exact hn (by rw [hX]; exact hc)
  have hI := (MCELL_ID_OMEGA_LIST_N V 2 2 (cellParamsD V X [elV ul 0, elV ul 1]).2 ul hp hs
    hb1 hb hXe hd (by simp) (by simp)).2 3 (by omega)
  have hM := MCELL_ID_MXI_2 V 2 2 (cellParamsD V X [elV ul 0, elV ul 1]).2 ul hp hs
    hb1 hb hXe hd (by simp) (by simp)
  rw [dihX, if_neg hn]
  simp only [hq1, if_true, dihu2]
  have final : dihV (elV (cellParamsD V X [elV ul 0, elV ul 1]).2 0)
        (elV (cellParamsD V X [elV ul 0, elV ul 1]).2 1)
        (mxi V (cellParamsD V X [elV ul 0, elV ul 1]).2)
        (omegaListN V (cellParamsD V X [elV ul 0, elV ul 1]).2 3)
      = dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) := by
    rw [hpre.1, hpre.2, hM, hI]
  exact final

/-- HOL `BIS_LE_INTER` (TSKAJXY3.hl:978). -/
theorem BIS_LE_INTER (u0 u1 : V3) : bisLe u0 u1 ∩ bisLe u1 u0 = bis u0 u1 := by
  ext x
  simp only [Set.mem_inter_iff, bisLe, bis, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 h2
  · intro h
    exact ⟨le_of_eq h, le_of_eq h.symm⟩

/-- HOL `BIS_LE_UNION` (TSKAJXY3.hl:987). -/
theorem BIS_LE_UNION (u0 u1 : V3) : bisLe u0 u1 ∪ bisLe u1 u0 = Set.univ := by
  ext x
  cases le_total (dist x u0) (dist x u1) with
  | inl h => simp [bisLe, h]
  | inr h => simp [bisLe, h]

/-- squares agree iff values agree, for nonneg reals. -/
private theorem p21_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b ↔ a ^ 2 = b ^ 2 := by
  constructor
  · intro h; rw [h]
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · nlinarith [h, hlt, ha]
    · nlinarith [h, hgt, hb]

/-- HOL `BIS_HYPERPLANE` (TSKAJXY3.hl:996; proved: the bisector is the
level set of the doubled axis functional — pure inner-product algebra,
PA5's `bis_mem_eq` pivoted into the hyperplane form). -/
theorem BIS_HYPERPLANE (u0 u1 : V3) :
    bis u0 u1 = {p : V3 | ((2:ℝ) • (u0 - u1)) ⬝ᵥ p = (u0 - u1) ⬝ᵥ (u0 + u1)} := by
  have hnorm : ∀ w : V3, ‖w‖ ^ 2 = w ⬝ᵥ w := by
    intro w; rw [← inner_eq_dot w w, real_inner_self_eq_norm_sq]
  have key : ∀ p : V3, ‖p - u0‖ ^ 2 = ‖p - u1‖ ^ 2 ↔
      2 * ((u0 - u1) ⬝ᵥ p) = u0 ⬝ᵥ u0 - u1 ⬝ᵥ u1 := by
    intro p
    have hA := norm_sub_sq_real (x := p) (y := u0)
    have hB := norm_sub_sq_real (x := p) (y := u1)
    rw [← real_inner_comm p u0, inner_eq_dot u0 p, hnorm u0] at hA
    rw [← real_inner_comm p u1, inner_eq_dot u1 p, hnorm u1] at hB
    rw [p21_sub_dot_whole u0 u1 p]
    constructor <;> intro h <;> linarith
  have hsplit : (u0 - u1) ⬝ᵥ (u0 + u1) = u0 ⬝ᵥ u0 - u1 ⬝ᵥ u1 := by
    rw [p21_dot_add_whole, p21_sub_dot_whole, p21_sub_dot_whole,
      p21_dot_comm u1 u0, p21_dot_comm u0 u1]
    ring
  ext p
  show dist p u0 = dist p u1 ↔ ((2:ℝ) • (u0 - u1)) ⬝ᵥ p = (u0 - u1) ⬝ᵥ (u0 + u1)
  rw [p21_smul_dot 2 (u0 - u1) p, hsplit, dist_eq_norm, dist_eq_norm,
    p21_sq_eq (norm_nonneg (p - u0)) (norm_nonneg (p - u1))]
  exact key p

/-- HOL `MCELL2_INTER_BIS_LE_MEASURABLE` (TSKAJXY3.hl:1007; proved: an
`mcell` is measurable (MEASURABLE_MCELL) and `bis_le` is a closed
half-space, hence Borel). -/
theorem MCELL2_INTER_BIS_LE_MEASURABLE (u0 u1 : V3) (V : Set V3) (X : Set V3)
    (ul : List V3) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hX : X = mcell2 V ul) : MeasurableSet (X ∩ bisLe u0 u1) := by
  have hXm : MeasurableSet X := by
    rw [hX]
    exact MEASURABLE_MCELL V ul 2 hs hp hb
  refine hXm.inter ?_
  show MeasurableSet {x : V3 | dist x u0 ≤ dist x u1}
  exact (isClosed_le (continuous_id.dist continuous_const)
    (continuous_id.dist continuous_const)).measurableSet

/-- pushed-coercion form of `p21_smul_dot` against a subtracted right
argument (elaborated `⬝ᵥ` on `V3` reduces `ofLp` through `-`). -/
private theorem p21_smul_dotP (t : ℝ) (a b c : V3) :
    (t • a).ofLp ⬝ᵥ (b.ofLp - c.ofLp)
      = t * ((a.ofLp ⬝ᵥ b.ofLp) - (a.ofLp ⬝ᵥ c.ofLp)) := by
  rw [show WithLp.ofLp b - WithLp.ofLp c = WithLp.ofLp (b - c) from
    (WithLp.ofLp_sub 2 b c).symm, p21_smul_dot t a (b - c), WithLp.ofLp_sub 2 b c,
    p21_dot_sub_whole a b c]

/-- HOL `RCONE_GT_SCALE` (TSKAJXY3.hl:597; proved: strict-cone membership is
positively homogeneous along rays from the apex). -/
theorem RCONE_GT_SCALE (u0 u1 u : V3) (a t : ℝ) (ht : 0 < t)
    (h : u0 + u ∈ rconeGt u0 u1 a) : u0 + t • u ∈ rconeGt u0 u1 a := by
  have hmem := h
  unfold rconeGt at hmem
  rw [Set.mem_setOf_eq] at hmem
  rw [show u0 + u - u0 = u from by abel, dist_eq_norm,
    show u0 + u - u0 = u from by abel] at hmem
  unfold rconeGt
  rw [Set.mem_setOf_eq]
  rw [show u0 + t • u - u0 = t • u from by abel, p21_smul_dotP t u u1 u0,
    dist_eq_norm, show u0 + t • u - u0 = t • u from by abel, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht]
  have hdot := p21_dot_sub_whole u u1 u0
  rw [← hdot, gt_iff_lt]
  have h2 : t * ‖u‖ * dist u1 u0 * a < t * (u.ofLp ⬝ᵥ (u1.ofLp - u0.ofLp)) := by
    have h := mul_lt_mul_of_pos_left hmem ht
    have hEq : t * (‖u‖ * dist u1 u0 * a) = t * ‖u‖ * dist u1 u0 * a := by ring
    linarith
  exact h2

/-- `cos ∘ arcV` as the normalized dot product (Cauchy-Schwarz via
`abs_real_inner_le_norm` + `inner_eq_dot`).  The degenerate denominator is
harmless: both dot and fraction vanish there. -/
private theorem p21_cos_arcV (u v x : V3) :
    Real.cos (arcV u v x) = ((v - u) ⬝ᵥ (x - u)) / (dist v u * dist x u) := by
  have hcs : |((v - u) ⬝ᵥ (x - u) : ℝ)| ≤ dist v u * dist x u := by
    have h1 := abs_real_inner_le_norm (x := v - u) (y := x - u)
    rw [inner_eq_dot, ← dist_eq_norm, ← dist_eq_norm] at h1
    exact h1
  have hnum0 : dist v u * dist x u = 0 → ((v - u) ⬝ᵥ (x - u) : ℝ) = 0 := by
    intro h0
    rw [← inner_eq_dot]
    rcases mul_eq_zero.1 h0 with h | h
    · simp [show v = u from dist_eq_zero.1 h]
    · simp [show x = u from dist_eq_zero.1 h]
  unfold arcV
  rcases eq_or_ne (dist v u * dist x u) 0 with h0 | h0
  · rw [h0, hnum0 h0, div_zero]
    exact Real.cos_arccos (by norm_num) (by norm_num)
  · have hpos : 0 < dist v u * dist x u :=
      lt_of_le_of_ne (mul_nonneg dist_nonneg dist_nonneg) (Ne.symm h0)
    have hbound : |(v - u) ⬝ᵥ (x - u) / (dist v u * dist x u)| ≤ 1 := by
      rw [abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).2 hcs
    exact Real.cos_arccos (abs_le.1 hbound).1 (abs_le.1 hbound).2

/-- HOL `RCONE_GE_COS` (TSKAJXY3.hl:1067; proved: the closed cone is the apex
plus the `cos ≥ a` region of `arcV` — `p21_cos_arcV` + sign bookkeeping on
the positive denominator). -/
theorem RCONE_GE_COS (u v : V3) (a : ℝ) (huv : u ≠ v) :
    rconeGe u v a = {u} ∪ {x : V3 | a ≤ Real.cos (arcV u v x)} := by
  have hduv : 0 < dist u v := dist_pos.2 huv
  ext x
  by_cases hx : x = u
  · rw [hx]
    refine ⟨fun _ => Set.mem_union_left _ rfl, fun _ => ?_⟩
    show (u - u) ⬝ᵥ (v - u) ≥ dist u u * dist v u * a
    rw [sub_self, dist_self, ← inner_eq_dot, inner_zero_left, zero_mul, zero_mul]
  · have hden : 0 < dist u v * dist x u :=
      mul_pos hduv (dist_pos.2 (fun hh => hx hh))
    have hden2 : 0 < dist v u * dist x u := by
      rw [dist_comm]
      exact hden
    constructor
    · intro hmem
      unfold rconeGe at hmem
      rw [Set.mem_setOf_eq] at hmem
      try rw [← WithLp.ofLp_sub 2 v u] at hmem
      rw [p21_dot_comm (x - u) (v - u), WithLp.ofLp_sub 2 x u, dist_comm v u] at hmem
      refine Set.mem_union_right _ ?_
      rw [Set.mem_setOf_eq, p21_cos_arcV u v x, le_div_iff₀ hden2]
      have hEq : a * (dist v u * dist x u) = dist x u * dist u v * a := by
        rw [dist_comm v u]; ring
      linarith [hEq, hmem]
    · intro hmem
      rcases (Set.mem_union _ _ _).1 hmem with heq | hle
      · exact absurd heq hx
      · unfold rconeGe
        rw [Set.mem_setOf_eq]
        try rw [← WithLp.ofLp_sub 2 v u]
        rw [p21_dot_comm (x - u) (v - u), WithLp.ofLp_sub 2 x u, dist_comm v u]
        rw [Set.mem_setOf_eq] at hle
        rw [p21_cos_arcV u v x, le_div_iff₀ hden2] at hle
        have hEq : a * (dist v u * dist x u) = dist x u * dist u v * a := by
          rw [dist_comm v u]; ring
        linarith [hEq, hle]

/-- Multiplied form of `p21_cos_arcV` (denominator-safe). -/
private theorem p21_cos_arcV_mul (u v x : V3) :
    dist v u * dist x u * Real.cos (arcV u v x) = ((v - u) ⬝ᵥ (x - u) : ℝ) := by
  rcases eq_or_ne (dist v u * dist x u) 0 with h0 | h0
  · rw [h0, zero_mul, ← inner_eq_dot]
    rcases mul_eq_zero.1 h0 with h | h
    · simp [show v = u from dist_eq_zero.1 h]
    · simp [show x = u from dist_eq_zero.1 h]
  · rw [p21_cos_arcV u v x, mul_comm]
    exact div_mul_cancel₀ _ h0

/-- Inner-product form of `p21_cos_arcV_mul`. -/
private theorem p21_cos_arcV_inner (u v x : V3) :
    dist v u * dist x u * Real.cos (arcV u v x) = inner ℝ (v - u) (x - u) := by
  rw [inner_eq_dot]
  exact p21_cos_arcV_mul u v x

/-- HOL `DIST_LAW_OF_COS_ALT` (TSKAJXY3.hl:1093; proved: `norm_sub_sq_real`
+ `p21_cos_arcV_inner` — holds verbatim including the degenerate junk cases,
since `cos (arcV)` vanishes there together with the dot). -/
theorem DIST_LAW_OF_COS_ALT (u v w : V3) :
    dist v w ^ 2 =
      dist u v ^ 2 + dist u w ^ 2 - 2 * dist u v * dist u w * Real.cos (arcV u v w) := by
  have hsplit : ‖v - w‖ ^ 2 = ‖v - u‖ ^ 2 + ‖w - u‖ ^ 2 - 2 * inner ℝ (v - u) (w - u) := by
    have h1 := norm_sub_sq_real (x := v - u) (y := w - u)
    rw [show (v - u) - (w - u) = v - w from by abel] at h1
    linarith
  have hkey : (2:ℝ) * dist u v * dist u w * Real.cos (arcV u v w) =
      2 * inner ℝ (v - u) (w - u) := by
    rw [dist_comm u v, dist_comm u w, ← p21_cos_arcV_inner]
    ring
  have e1 : ‖v - w‖ = dist v w := dist_eq_norm v w
  have e2 : ‖u - v‖ = dist u v := dist_eq_norm u v
  have e3 : ‖u - w‖ = dist u w := dist_eq_norm u w
  rw [hkey, ← e1, ← e2, ← e3, norm_sub_rev u v, norm_sub_rev u w]
  linarith [hsplit]

/-- HOL `ATN_DIV` (TSKAJXY3.hl:1103). -/
theorem ATN_DIV (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.arctan (x / y) = Real.pi / 2 - Real.arctan (y / x) := by
  have hyx : 0 < y / x := div_pos hy hx
  have h := Real.arctan_inv_of_pos hyx
  rw [← h]
  congr 1
  field_simp

/-- HOL `REAL_DIV_NEG` (TSKAJXY3.hl:1119). -/
theorem REAL_DIV_NEG (x y : ℝ) : x / -y = -(x / y) := by
  field_simp

/-- HOL `ATN2_Y_NEG` (TSKAJXY3.hl:1128), for the `atn2` of
PackingAuto20.lean:66. -/
theorem ATN2_Y_NEG (x y : ℝ) (hy : y < 0) :
    atn2 x y = -(Real.pi / 2) - Real.arctan (x / y) := by
  have hynonneg : 0 ≤ |y| := abs_nonneg y
  by_cases habs : |y| < x
  · rw [atn2, if_pos habs]
    have hx : 0 < x := by linarith
    have hyn : y / x < 0 := div_neg_of_neg_of_pos hy hx
    have hinv := Real.arctan_inv_of_neg hyn
    have hinv' : (y / x)⁻¹ = x / y := by
      field_simp
    rw [hinv'] at hinv
    linarith
  · rw [atn2, if_neg habs, if_neg (by linarith), if_pos hy]

/-- A hyperplane `{p | c ⬝ᵥ p = d}` with `c ≠ 0` is Lebesgue-null: it is the
strict affine subspace `p₀ + ker(p ↦ c ⬝ᵥ p)` (Measure.addHaar_affineSubspace). -/
private theorem p21_hyperplane_null (c : V3) (hc : c ≠ 0) (d : ℝ) :
    volume {p : V3 | c ⬝ᵥ p = d} = 0 := by
  have hcc : (0:ℝ) < c ⬝ᵥ c := by
    rw [← inner_eq_dot c c, real_inner_self_eq_norm_sq]
    nlinarith [norm_pos_iff.2 hc]
  have hK : (c ⬝ᵥ c : ℝ) ≠ 0 := ne_of_gt hcc
  have hp0 : c ⬝ᵥ ((d / (c ⬝ᵥ c)) • c) = d := by
    rw [p21_dot_smul]
    exact div_mul_cancel₀ _ hK
  set K : Submodule ℝ V3 :=
    { carrier := {p : V3 | c ⬝ᵥ p = 0}
      add_mem' := by
        intro a b ha hb
        have ha' : (c ⬝ᵥ a : ℝ) = 0 := ha
        have hb' : (c ⬝ᵥ b : ℝ) = 0 := hb
        show (c ⬝ᵥ (a + b) : ℝ) = 0
        rw [p21_dot_add_whole]
        linarith
      zero_mem' := by
        show (c ⬝ᵥ (0 : V3) : ℝ) = 0
        rw [← inner_eq_dot, inner_zero_right]
      smul_mem' := by
        intro t a ha
        have ha' : (c ⬝ᵥ a : ℝ) = 0 := ha
        show (c ⬝ᵥ (t • a) : ℝ) = 0
        rw [p21_dot_smul, ha', mul_zero] } with hKdef
  have hKne : K ≠ ⊤ := by
    intro hKtop
    apply hcc.ne'
    have hcin : c ∈ K := by rw [hKtop]; exact Submodule.mem_top
    exact hcin
  have hAffNe : (AffineSubspace.mk' ((d / (c ⬝ᵥ c)) • c) K) ≠ ⊤ := by
    intro h
    exact hKne (by rw [← AffineSubspace.direction_mk' ((d / (c ⬝ᵥ c)) • c) K, h,
      AffineSubspace.direction_top])
  have hset : {p : V3 | c ⬝ᵥ p = d} =
      ((AffineSubspace.mk' ((d / (c ⬝ᵥ c)) • c) K : AffineSubspace ℝ V3) : Set V3) := by
    ext p
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
    constructor
    · intro hmem
      show (p - (d / (c ⬝ᵥ c)) • c : V3) ∈ K
      have h2 : (c ⬝ᵥ (p - (d / (c ⬝ᵥ c)) • c) : ℝ) = 0 := by
        rw [p21_dot_sub_whole, p21_dot_smul, div_mul_cancel₀ _ hK]
        have h1 : (c ⬝ᵥ p : ℝ) = d := hmem
        linarith
      exact h2
    · intro h2
      have h3 : (c ⬝ᵥ (p - (d / (c ⬝ᵥ c)) • c) : ℝ) = 0 := h2
      rw [p21_dot_sub_whole, p21_dot_smul, div_mul_cancel₀ _ hK] at h3
      have h1 : (c ⬝ᵥ p : ℝ) = d := by linarith
      exact h1
  rw [hset]
  exact MeasureTheory.Measure.addHaar_affineSubspace volume _ hAffNe

/-- HOL `RCONE_PAIR` (TSKAJXY3.hl:1153; proved: coordinate-free quadratic
algebra — the bisector half gives `2A ≤ ‖v-u‖²`, the cone half
`A ≥ t·‖v-u‖·‖x-u‖`, and `t ≤ 1` closes the squared comparison). -/
theorem RCONE_PAIR (u v : V3) (t : ℝ) (huv : u ≠ v) (ht : 0 < t) (ht1 : t ≤ 1) :
    rconeGe u v t ∩ bisLe u v ⊆ rconeGe v u t := by
  intro x hx
  obtain ⟨hcone, hbis⟩ := hx
  have hcone0 := hcone
  unfold rconeGe at hcone0
  rw [Set.mem_setOf_eq, dist_comm v u] at hcone0
  have hbis' : dist x u ≤ dist x v := hbis
  have hdpos : 0 < dist u v := dist_pos.2 huv
  -- atoms: A := (x-u)·(v-u), B := (x-v)·(u-v), D := ‖v-u‖²
  set A := (x - u) ⬝ᵥ (v - u) with hAdef
  set B := (x - v) ⬝ᵥ (u - v) with hBdef
  set D := (v - u) ⬝ᵥ (v - u) with hDdef
  have hconeA : dist x u * dist u v * t ≤ A := by
    rw [hAdef]
    exact hcone0
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ dist x u * dist u v * t :=
      mul_nonneg (mul_nonneg dist_nonneg (le_of_lt hdpos)) (le_of_lt ht)
    linarith [hconeA, h1]
  have hBexp : B = v ⬝ᵥ v - (u ⬝ᵥ v) - (x ⬝ᵥ v) + (x ⬝ᵥ u) := by
    rw [hBdef, p21_sub_dot_whole, p21_dot_sub_whole, p21_dot_sub_whole, p21_dot_comm v u]
    ring
  have hAexp : A = u ⬝ᵥ u - (u ⬝ᵥ v) - (x ⬝ᵥ u) + (x ⬝ᵥ v) := by
    rw [hAdef, p21_sub_dot_whole, p21_dot_sub_whole, p21_dot_sub_whole]
    ring
  have hDexp : D = v ⬝ᵥ v - 2 * (u ⬝ᵥ v) + u ⬝ᵥ u := by
    rw [hDdef, p21_sub_dot_whole, p21_dot_sub_whole, p21_dot_sub_whole, p21_dot_comm v u]
    ring
  have hBD : B = D - A := by
    rw [hBexp, hAexp, hDexp]
    ring
  -- norm-squared dictionary
  have hd2 : dist u v * dist u v = D := by
    have h1 : dist u v = ‖u - v‖ := dist_eq_norm u v
    have h2 := norm_sub_sq_real u v
    have h3 : ‖u‖ ^ 2 = u ⬝ᵥ u := by rw [← inner_eq_dot u u, real_inner_self_eq_norm_sq]
    have h4 : ‖v‖ ^ 2 = v ⬝ᵥ v := by rw [← inner_eq_dot v v, real_inner_self_eq_norm_sq]
    have h5 : inner ℝ u v = (u ⬝ᵥ v : ℝ) := inner_eq_dot u v
    rw [← sq, h1, h2, h3, h4, h5, hDexp]
    ring
  have hL2 : dist x u * dist x u = x ⬝ᵥ x - 2 * (x ⬝ᵥ u) + u ⬝ᵥ u := by
    have h1 : dist x u = ‖x - u‖ := dist_eq_norm x u
    have h2 := norm_sub_sq_real x u
    have h3 : ‖x‖ ^ 2 = x ⬝ᵥ x := by rw [← inner_eq_dot x x, real_inner_self_eq_norm_sq]
    have h4 : ‖u‖ ^ 2 = u ⬝ᵥ u := by rw [← inner_eq_dot u u, real_inner_self_eq_norm_sq]
    have h5 : inner ℝ x u = (x ⬝ᵥ u : ℝ) := inner_eq_dot x u
    rw [← sq, h1, h2, h3, h4, h5]
  have hM2 : dist x v * dist x v = x ⬝ᵥ x - 2 * (x ⬝ᵥ v) + v ⬝ᵥ v := by
    have h1 : dist x v = ‖x - v‖ := dist_eq_norm x v
    have h2 := norm_sub_sq_real x v
    have h3 : ‖x‖ ^ 2 = x ⬝ᵥ x := by rw [← inner_eq_dot x x, real_inner_self_eq_norm_sq]
    have h4 : ‖v‖ ^ 2 = v ⬝ᵥ v := by rw [← inner_eq_dot v v, real_inner_self_eq_norm_sq]
    have h5 : inner ℝ x v = (x ⬝ᵥ v : ℝ) := inner_eq_dot x v
    rw [← sq, h1, h2, h3, h4, h5]
  -- bisector half: 2A ≤ D
  have h2lin : 2 * A ≤ D := by
    rw [hAexp, hDexp]
    have hLL : dist x u * dist x u ≤ dist x v * dist x v :=
      mul_self_le_mul_self dist_nonneg hbis'
    linarith [hM2, hL2, hLL]
  have hDAA : 0 ≤ D - A := by linarith
  have hBDA : D - A ≤ B := by rw [hBD]
  have hB0 : 0 ≤ B := by linarith
  have hBDsq : (D - A) * (D - A) ≤ B * B := mul_self_le_mul_self hDAA hBDA
  -- quadratic close
  have ht2 : t * t ≤ 1 := by
    have h : t * t ≤ t * 1 := mul_le_mul_of_nonneg_left ht1 (le_of_lt ht)
    linarith
  have htuv : (t * dist u v) * (t * dist u v) ≤ D := by
    have h1 : (t * dist u v) * (t * dist u v) = (t * t) * (dist u v * dist u v) := by
      ring
    have h2 : (t * t) * (dist u v * dist u v) ≤ dist u v * dist u v := by
      have h3 : 0 ≤ dist u v * dist u v := by positivity
      have h4 := mul_le_mul_of_nonneg_right ht2 h3
      rwa [one_mul] at h4
    rw [h1]
    linarith [h2, hd2]
  have hM2le : dist x v * dist x v ≤ dist x u * dist x u + (D - 2 * A) := by
    have hdiff : dist x v * dist x v - dist x u * dist x u = D - 2 * A := by
      rw [hM2, hL2, hDexp, hAexp]
      ring
    linarith
  have hLscale : dist x u * dist x u * ((t * dist u v) * (t * dist u v)) ≤ A * A := by
    have hmono : dist x u * (t * dist u v) = dist x u * dist u v * t := by ring
    have hnn : 0 ≤ dist x u * (t * dist u v) :=
      mul_nonneg dist_nonneg (mul_nonneg (le_of_lt ht) (le_of_lt hdpos))
    have h1 : dist x u * (t * dist u v) * (dist x u * (t * dist u v)) ≤ A * A := by
      have h2 : dist x u * (t * dist u v) ≤ A := by rw [hmono]; exact hconeA
      exact mul_le_mul h2 h2 hnn hA0
    have h2eq : dist x u * dist x u * ((t * dist u v) * (t * dist u v)) =
        dist x u * (t * dist u v) * (dist x u * (t * dist u v)) := by ring
    rw [h2eq]
    exact h1
  have hP2 : (D - 2 * A) * ((t * dist u v) * (t * dist u v)) ≤
      (D - A) * (D - A) - A * A := by
    have hD2A0 : 0 ≤ D - 2 * A := by linarith
    have e1 : (D - 2 * A) * ((t * dist u v) * (t * dist u v)) ≤ (D - 2 * A) * D :=
      mul_le_mul_of_nonneg_left htuv hD2A0
    have e2 : (D - 2 * A) * D ≤ (D - A) * (D - A) - A * A := by
      have h4 : (D - A) * (D - A) = D * D - 2 * A * D + A * A := by ring
      have h5 : (D - 2 * A) * D = D * D - 2 * A * D := by ring
      rw [h4, h5]
      linarith
    exact le_trans e1 e2
  have hM2scale : dist x v * dist x v * ((t * dist u v) * (t * dist u v)) ≤
      dist x u * dist x u * ((t * dist u v) * (t * dist u v)) +
        (D - 2 * A) * ((t * dist u v) * (t * dist u v)) := by
    have him := mul_le_mul_of_nonneg_right hM2le
      (mul_nonneg (mul_nonneg (le_of_lt ht) (le_of_lt hdpos))
        (mul_nonneg (le_of_lt ht) (le_of_lt hdpos)))
    rw [add_mul] at him
    exact him
  have hchain : (dist x v * dist u v * t) * (dist x v * dist u v * t) ≤ B * B := by
    have hsqeq : (dist x v * dist u v * t) * (dist x v * dist u v * t) =
        dist x v * dist x v * ((t * dist u v) * (t * dist u v)) := by ring
    rw [hsqeq]
    linarith [hM2scale, hLscale, hP2, hBDsq]
  have hnonneg : 0 ≤ dist x v * dist u v * t :=
    mul_nonneg (mul_nonneg dist_nonneg (le_of_lt hdpos)) (le_of_lt ht)
  have hfinal : dist x v * dist u v * t ≤ B :=
    (mul_self_le_mul_self_iff hnonneg hB0).2 hchain
  unfold rconeGe
  rw [Set.mem_setOf_eq]
  exact hfinal

/-- HOL `MCELL2_HL_LT_SQRT2` (TSKAJXY3.hl:1678; ported 2026-09-29 wave B1 —
was missing from the skeleton AND the NEEDS list (scout §5.1); one-line
by-contradiction from the `mcell2` definition: a failed side condition makes
the cell empty, hence null). -/
theorem MCELL2_HL_LT_SQRT2 (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    hl (truncateSimplex 1 ul) < Real.sqrt 2 := by
  by_contra hge
  refine hn (by rw [mcell2, if_neg (fun hc => hge hc.1)]; exact measure_empty)

theorem MCELL2_SPLIT (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    X ∩ bisLe (elV ul 0) (elV ul 1) =
      rconeGe (elV ul 0) (elV ul 1) (hl (truncateSimplex 1 ul) / Real.sqrt 2) ∩
        affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} ∩
          bisLe (elV ul 0) (elV ul 1) := by
  have huv : elV ul 0 ≠ elV ul 1 := fun heq =>
    hn (by rw [hX]; exact p21_mcell2_uv_null V ul heq)
  have hlt := MCELL2_HL_LT_SQRT2 V ul hs hp hb (by rw [← hX]; exact hn)
  have hpos := BARV_IMP_HL_1_POS_LT V ul hs hp hb
  have hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul := by
    refine ⟨hlt, ?_⟩
    by_contra hge
    refine hn ?_
    rw [hX, mcell2, if_neg (fun hc => hge hc.2)]
    exact measure_empty
  have h1 : 0 < hl (truncateSimplex 1 ul) / Real.sqrt 2 :=
    div_pos hpos (Real.sqrt_pos.mpr (by norm_num))
  have h2 : hl (truncateSimplex 1 ul) / Real.sqrt 2 ≤ 1 :=
    (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr
      (le_trans (le_of_lt hlt) (Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 2)))
  have hcent : hdV ul = elV ul 0 ∧ hdV ul.tail = elV ul 1 := by
    cases ul with
    | nil => exact absurd hb.1 (by simp)
    | cons a t =>
      cases t with
      | nil => exact absurd hb.1 (by simp)
      | cons b t => exact ⟨rfl, rfl⟩
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxX, hxb⟩ := hx
    rw [hX, mcell2, if_pos hcond, hcent.1, hcent.2, Set.mem_inter_iff,
      Set.mem_inter_iff] at hxX
    obtain ⟨hcc, f2, hfin2, hxw, hxb'⟩ := hxX
    obtain ⟨hc1, hc2⟩ := hcc
    refine And.intro (And.intro hc1 ⟨f2, hfin2, hxw, hxb'⟩) hxb
  · intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxAB, hxb⟩ := hx
    rw [Set.mem_inter_iff] at hxAB
    obtain ⟨hc1, hxw⟩ := hxAB
    rw [hX, mcell2, if_pos hcond, hcent.1, hcent.2]
    refine And.intro (And.intro (And.intro hc1 ?_) hxw) hxb
    exact RCONE_PAIR (elV ul 0) (elV ul 1) (hl (truncateSimplex 1 ul) / Real.sqrt 2)
      huv h1 h2 ⟨hc1, hxb⟩

theorem MCELL2_VOL_SPLIT (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    volume.real X = volume.real (X ∩ bisLe (elV ul 0) (elV ul 1)) +
      volume.real (X ∩ bisLe (elV ul 1) (elV ul 0)) := by
  have huv : elV ul 0 ≠ elV ul 1 := fun heq =>
    hn (by rw [hX]; exact p21_mcell2_uv_null V ul heq)
  have hXm : MeasurableSet X := by rw [hX]; exact MEASURABLE_MCELL V ul 2 hs hp hb
  have hA : MeasurableSet (X ∩ bisLe (elV ul 0) (elV ul 1)) :=
    MCELL2_INTER_BIS_LE_MEASURABLE (elV ul 0) (elV ul 1) V X ul hp hs hb hX
  have hB : MeasurableSet (X ∩ bisLe (elV ul 1) (elV ul 0)) :=
    MCELL2_INTER_BIS_LE_MEASURABLE (elV ul 1) (elV ul 0) V X ul hp hs hb hX
  have hc : (2:ℝ) • ((elV ul 0 : V3) - elV ul 1) ≠ 0 := by
    intro hz
    apply huv
    apply sub_eq_zero.mp
    have h5 : ‖(2:ℝ) • ((elV ul 0 : V3) - elV ul 1)‖ = 2 * ‖(elV ul 0 : V3) - elV ul 1‖ := by
      rw [norm_smul]; simp
    rw [hz, norm_zero] at h5
    exact norm_eq_zero.mp (by linarith)
  have hnullbis : volume (bis (elV ul 0) (elV ul 1)) = 0 := by
    rw [BIS_HYPERPLANE]
    exact p21_hyperplane_null ((2:ℝ) • ((elV ul 0 : V3) - elV ul 1)) hc _
  have hDm : MeasurableSet (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) :=
    hXm.inter (isOpen_lt (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)).measurableSet
  have hdis : Disjoint (X ∩ bisLe (elV ul 0) (elV ul 1))
      (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) := by
    refine Set.disjoint_left.mpr fun x hx => ?_
    rw [Set.mem_inter_iff] at hx
    obtain ⟨haX, hble⟩ := hx
    intro hx2
    rw [Set.mem_inter_iff] at hx2
    obtain ⟨_, hdst⟩ := hx2
    simp only [bisLe, Set.mem_setOf_eq] at hble
    simp only [Set.mem_setOf_eq] at hdst
    exfalso
    linarith
  have hcover : X ⊆ (X ∩ bisLe (elV ul 0) (elV ul 1)) ∪
      (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) := by
    intro x hx
    by_cases hlt : dist x (elV ul 1) < dist x (elV ul 0)
    · exact Or.inr
        ((Set.mem_inter_iff (x := x) (a := X)
            (b := {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)})).mpr ⟨hx, hlt⟩)
    · exact Or.inl
        ((Set.mem_inter_iff (x := x) (a := X) (b := bisLe (elV ul 0) (elV ul 1))).mpr
          ⟨hx, le_of_not_gt hlt⟩)
  have hDsubB : X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}
      ⊆ X ∩ bisLe (elV ul 1) (elV ul 0) := by
    intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxX, hxd⟩ := hx
    have hle : dist x (elV ul 1) ≤ dist x (elV ul 0) := le_of_lt hxd
    exact (Set.mem_inter_iff (x := x) (a := X) (b := bisLe (elV ul 1) (elV ul 0))).mpr
      ⟨hxX, hle⟩
  have hBsplit : X ∩ bisLe (elV ul 1) (elV ul 0) ⊆
      (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) ∪ (X ∩ bis (elV ul 0) (elV ul 1)) := by
    intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxX, hxd⟩ := hx
    by_cases heq : dist x (elV ul 1) = dist x (elV ul 0)
    · refine Or.inr ⟨hxX, ?_⟩
      simp only [bis, Set.mem_setOf_eq]
      exact heq.symm
    · refine Or.inl ⟨hxX, lt_of_le_of_ne hxd heq⟩
  have hbnd : Bornology.IsBounded X := by rw [hX]; exact BOUNDED_MCELL V ul 2 hs hp hb
  have hXlt : volume X < ⊤ := hbnd.measure_lt_top
  have hXne : volume X ≠ ⊤ := ne_of_lt hXlt
  have hAne : volume (X ∩ bisLe (elV ul 0) (elV ul 1)) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hXlt)
  have hBne : volume (X ∩ bisLe (elV ul 1) (elV ul 0)) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hXlt)
  have hE1 : volume X = volume (X ∩ bisLe (elV ul 0) (elV ul 1)) +
      volume (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_mono hcover) ?_
      rw [measure_union hdis hDm]
    · refine le_trans (le_of_eq (Eq.symm (measure_union hdis hDm))) ?_
      refine measure_mono ?_
      exact Set.union_subset
        (Set.inter_subset_left : X ∩ bisLe (elV ul 0) (elV ul 1) ⊆ X)
        (Set.inter_subset_left : X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)} ⊆ X)
  have hDB : volume (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)})
      = volume (X ∩ bisLe (elV ul 1) (elV ul 0)) := by
    refine le_antisymm (measure_mono hDsubB) ?_
    calc volume (X ∩ bisLe (elV ul 1) (elV ul 0))
        ≤ volume ((X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) ∪
            (X ∩ bis (elV ul 0) (elV ul 1))) := measure_mono hBsplit
      _ ≤ volume (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) +
            volume (X ∩ bis (elV ul 0) (elV ul 1)) :=
          measure_union_le (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)})
            (X ∩ bis (elV ul 0) (elV ul 1))
      _ = volume (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) + 0 := by
          rw [measure_mono_null
            (Set.inter_subset_right : (X ∩ bis (elV ul 0) (elV ul 1)) ⊆ bis (elV ul 0) (elV ul 1))
            hnullbis]
      _ = volume (X ∩ {y : V3 | dist y (elV ul 1) < dist y (elV ul 0)}) := add_zero _
  rw [Measure.real_def, Measure.real_def, Measure.real_def, hE1, hDB]
  exact ENNReal.toReal_add hAne hBne

/-- A single point is Lebesgue-null in `V3` (it is the affine subspace
`u + ⊥`). -/
private theorem p21_point_null (u : V3) : volume ({u} : Set V3) = 0 := by
  have h0 : volume ((AffineSubspace.mk' u (⊥ : Submodule ℝ V3) : AffineSubspace ℝ V3) : Set V3) = 0 :=
    MeasureTheory.Measure.addHaar_affineSubspace volume _ (by
      intro h
      have h4 : ((AffineSubspace.mk' u (⊥ : Submodule ℝ V3) : AffineSubspace ℝ V3)).direction
          = (⊥ : Submodule ℝ V3) := AffineSubspace.direction_mk' _ _
      rw [h, AffineSubspace.direction_top] at h4
      exact bot_ne_top h4.symm)
  refine measure_mono_null (Set.singleton_subset_iff.2 ?_) h0
  exact SetLike.mem_coe.2 (AffineSubspace.mem_mk'.mpr (by simp))

/-- A translate of the line `u + ℝ • w` is Lebesgue-null in `V3`. -/
private theorem p21_ray_null (u w : V3) (hw : w ≠ 0) :
    volume {x : V3 | x - u ∈ Submodule.span ℝ ({w} : Set V3)} = 0 := by
  have h0 : volume ((AffineSubspace.mk' u (Submodule.span ℝ ({w} : Set V3)) :
      AffineSubspace ℝ V3) : Set V3) = 0 :=
    MeasureTheory.Measure.addHaar_affineSubspace volume _ (by
      intro h
      have h4 : ((AffineSubspace.mk' u (Submodule.span ℝ ({w} : Set V3)) :
          AffineSubspace ℝ V3)).direction = Submodule.span ℝ ({w} : Set V3) :=
        AffineSubspace.direction_mk' _ _
      rw [h, AffineSubspace.direction_top] at h4
      have h5 : Module.finrank ℝ (Submodule.span ℝ ({w} : Set V3)) = 1 :=
        finrank_span_singleton hw
      have h6 : Module.finrank ℝ (⊤ : Submodule ℝ V3) = 3 := by simp
      rw [← h4] at h5
      omega)
  refine measure_mono_null ?_ h0
  intro x hx
  exact SetLike.mem_coe.2 (AffineSubspace.mem_mk'.mpr hx)

/-- HOL `SDIFF_SUBSET` (TSKAJXY3.hl:1339). -/
theorem SDIFF_SUBSET (X Y Z : Set V3) :
    symmDiff (X ∩ Z) (Y ∩ Z) ⊆ symmDiff X Y := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
  tauto

/-- HOL `SDIFF_TRANS` (TSKAJXY3.hl:1348). -/
theorem SDIFF_TRANS (X Y Z : Set V3) : symmDiff X Z ⊆ symmDiff X Y ∪ symmDiff Y Z := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_union] at hx ⊢
  tauto

/-- HOL `NULL_SDIFF_TRANS` (TSKAJXY3.hl:1357). -/
theorem NULL_SDIFF_TRANS (X Y Z : Set V3) (h1 : nullSet (symmDiff X Y))
    (h2 : nullSet (symmDiff Y Z)) : nullSet (symmDiff X Z) := by
  have hsub : symmDiff X Z ⊆ symmDiff X Y ∪ symmDiff Y Z := SDIFF_TRANS X Y Z
  have hle : volume (symmDiff X Z) ≤ volume (symmDiff X Y) + volume (symmDiff Y Z) := by
    calc volume (symmDiff X Z) ≤ volume (symmDiff X Y ∪ symmDiff Y Z) := measure_mono hsub
      _ ≤ volume (symmDiff X Y) + volume (symmDiff Y Z) := measure_union_le _ _
  unfold nullSet at h1 h2 ⊢
  rw [h1, h2, add_zero] at hle
  exact le_antisymm hle (by simp)

/-! ## FRUSTT_RCONE_GE: the circular-cone-surface null engine (TSKAJXY3.hl:1275)

The HOL proof reduces `FRUSTT_RCONE_GE` to the null-ness of the
`circular_cone` surface (its `NULLSET_RULES` step).  In Lean that surface is
handled by slicing with the `Kepler.Geom.WedgeVolume` frame projection
(`measurePreserving_proj`): the `t`-sections of the surface are circles in
`ℂ`, so `measure_prod_null_of_ae_null` closes it.  WedgeVolume was not in the
import closure (scout §3.4 flagged PA4/PA18; this wave adds the acyclic
`Kepler.Geom.WedgeVolume` import — it imports only Mathlib + Kepler.Geom
modules).  The two frame identities below are copies of the PRIVATE
`Kepler.Geom.WedgeVolume` helpers `zOf_norm_sq`/`on3_norm_sq`. -/

/-- Frame identity: `‖zOf e1 e2 x‖² = (x⬝e1)² + (x⬝e2)²` (copy of the private
`Kepler.Geom.WedgeVolume.zOf_norm_sq`). -/
private theorem p21_zOf_norm_sq (e1 e2 : V3) (x : V3) :
    ‖zOf e1 e2 x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [zOf, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    add_zero, zero_add, mul_one, sub_self]
  ring

/-- Frame identity: `‖x‖² = (x⬝e1)² + (x⬝e2)² + (x⬝e3)²` for an ON frame (copy
of the private `Kepler.Geom.WedgeVolume.on3_norm_sq`). -/
private theorem p21_on3_norm_sq (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (x : V3) :
    ‖x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 + (x ⬝ᵥ e3) ^ 2 := by
  have h12 : e1 ⬝ᵥ e2 = 0 := he.2.2.2.1
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [p21_dot_comm]; exact he.2.2.2.1
  have h13 : e1 ⬝ᵥ e3 = 0 := he.2.2.2.2.1
  have h31 : e3 ⬝ᵥ e1 = 0 := by rw [p21_dot_comm]; exact he.2.2.2.2.1
  have h23 : e2 ⬝ᵥ e3 = 0 := he.2.2.2.2.2.1
  have h32 : e3 ⬝ᵥ e2 = 0 := by rw [p21_dot_comm]; exact he.2.2.2.2.2.1
  rw [norm_sq_eq_dot, on3_expand he x]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [he.1, he.2.1, he.2.2.1, h12, h21, h13, h31, h23, h32]
  ring

/-- The surface of the circular cone `{x | x ⬝ᵥ w = ‖x‖ * ‖w‖ * a}` about the
`w`-axis is Lebesgue-null (`w ≠ 0`, `0 < a`).  In a right-hand ON frame with
axis `e3 ∥ w` the measure-preserving projection `x ↦ (x ⬝ᵥ e3, zOf e1 e2 x)`
carries it into a set whose `t`-sections are the circles
`{ζ | ‖ζ‖ = t·√(1−a²)/a}` (degenerate to `{0}` when `a ≥ 1`), so Fubini
(`measure_prod_null_of_ae_null`) applies.  This is the `circular_cone` step
of HOL `FRUSTT_RCONE_GE` (TSKAJXY3.hl:1275). -/
private theorem p21_cone_surf_null (w : V3) (hw : w ≠ 0) (a : ℝ) (ha : 0 < a) :
    volume {x : V3 | x ⬝ᵥ w = ‖x‖ * ‖w‖ * a} = 0 := by
  obtain ⟨e1, e2, e3, he, hax⟩ := exists_on3_eq_smul w hw
  have hw0 : (0:ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hzOf := p21_zOf_norm_sq e1 e2
  have hNx := p21_on3_norm_sq e1 e2 e3 he
  -- the surface is carried into T' by the measure-preserving frame projection
  have hsub : {x : V3 | x ⬝ᵥ w = ‖x‖ * ‖w‖ * a}
      ⊆ (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹'
          {p : ℝ × ℂ | p.1 * ‖w‖ = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
    have h1 : x ⬝ᵥ w = ‖w‖ * (x ⬝ᵥ e3) := by
      have h0 : x ⬝ᵥ w = x ⬝ᵥ (‖w‖ • e3) :=
        congrArg (fun z : V3 => x ⬝ᵥ z) hax
      rw [h0, p21_dot_smul]
    have hsq : Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) = ‖x‖ := by
      have h5 : (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [hzOf x, hNx x]; ring
      rw [h5, Real.sqrt_sq (norm_nonneg x)]
    show (x ⬝ᵥ e3) * ‖w‖
        = Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) * ‖w‖ * a
    rw [h1] at hx
    rw [hsq, mul_comm (x ⬝ᵥ e3) ‖w‖]
    exact hx
  have hmeas : MeasurableSet {p : ℝ × ℂ | p.1 * ‖w‖
      = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a} := by
    have hf : Measurable (fun p : ℝ × ℂ => p.1 * ‖w‖) :=
      measurable_fst.mul measurable_const
    have hsq2 : Measurable (fun p : ℝ × ℂ => p.1 ^ 2 + ‖p.2‖ ^ 2) :=
      (measurable_fst.pow_const 2).add (measurable_snd.norm.pow_const 2)
    have hg : Measurable (fun p : ℝ × ℂ =>
        Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a) :=
      (((Real.continuous_sqrt.measurable).comp hsq2).mul
        measurable_const).mul measurable_const
    have hsub0 : {p : ℝ × ℂ | p.1 * ‖w‖ = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a}
        = (fun p : ℝ × ℂ => p.1 * ‖w‖
            - Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a) ⁻¹' ({0} : Set ℝ) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
        sub_eq_zero]
    rw [hsub0]
    exact (hf.sub hg) (measurableSet_singleton 0)
  -- the per-section claim: the ζ-slice is the circle of radius `t·√(1−a²)/a`
  have hchar : ∀ (t : ℝ) (ζ : ℂ),
      t * ‖w‖ = Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) * ‖w‖ * a →
      ‖ζ‖ = t * Real.sqrt (1 - a ^ 2) / a := by
    intro t ζ hζ
    obtain ⟨s, hs, hts⟩ : ∃ s : ℝ, s = Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) ∧ t = a * s :=
      ⟨_, rfl, mul_right_cancel₀ hw0.ne' (by rw [hζ]; ring)⟩
    have htnn : (0:ℝ) ≤ t := by
      rw [hts]; exact mul_nonneg ha.le (by rw [hs]; exact Real.sqrt_nonneg _)
    have hsqeq : t ^ 2 = a ^ 2 * s ^ 2 := by rw [hts]; ring
    have hs2 : s ^ 2 = t ^ 2 + ‖ζ‖ ^ 2 := by
      rw [hs]; exact Real.sq_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg ‖ζ‖))
    have hzsq' : a ^ 2 * ‖ζ‖ ^ 2 = t ^ 2 * (1 - a ^ 2) := by
      rw [hs2] at hsqeq
      nlinarith [hsqeq]
    by_cases ha1 : a < 1
    · have hpos1 : (0:ℝ) < 1 - a ^ 2 := by nlinarith [ha1, ha]
      have hrhs : (t * Real.sqrt (1 - a ^ 2) / a) ^ 2
          = t ^ 2 * (1 - a ^ 2) / a ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hpos1.le]
      have ha2 : (0:ℝ) < a ^ 2 := by positivity
      have h4 : ‖ζ‖ ^ 2 = (t * Real.sqrt (1 - a ^ 2) / a) ^ 2 := by
        rw [hrhs, eq_div_iff ha2.ne', mul_comm]
        exact hzsq'
      have hrnn : (0:ℝ) ≤ t * Real.sqrt (1 - a ^ 2) / a :=
        div_nonneg (mul_nonneg htnn (Real.sqrt_nonneg _)) ha.le
      have h6 := congrArg Real.sqrt h4
      rw [Real.sqrt_sq (norm_nonneg ζ), Real.sqrt_sq_eq_abs, abs_of_nonneg hrnn] at h6
      exact h6
    · have ha1 : (1:ℝ) ≤ a := le_of_not_gt ha1
      have h2 : (1:ℝ) ≤ a ^ 2 := by nlinarith [sq_nonneg a, ha1]
      have h3 : t ^ 2 ≤ t ^ 2 * a ^ 2 := le_mul_of_one_le_right (sq_nonneg t) h2
      have hzle : a ^ 2 * ‖ζ‖ ^ 2 ≤ 0 := by
        rw [hs2] at hsqeq
        nlinarith [sq_nonneg t]
      have hz0 : ‖ζ‖ = 0 := by
        have hzero : a ^ 2 * ‖ζ‖ ^ 2 = 0 := le_antisymm hzle (by positivity)
        rcases mul_eq_zero.1 hzero with h | h
        · exact absurd h (by positivity)
        · exact sq_eq_zero_iff.1 h
      rw [hz0, Real.sqrt_eq_zero_of_nonpos (by linarith)]
      ring
  have hsec : ∀ t : ℝ, volume (Prod.mk t ⁻¹'
      {p : ℝ × ℂ | p.1 * ‖w‖ = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a}) = 0 := by
    intro t
    refine measure_mono_null ?_ (Measure.addHaar_sphere volume (0:ℂ)
      (t * Real.sqrt (1 - a ^ 2) / a))
    intro ζ hζ
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hζ
    rw [Metric.mem_sphere, dist_zero_right]
    exact hchar t ζ hζ
  have hv2 : (volume.prod volume) {p : ℝ × ℂ | p.1 * ‖w‖
      = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a} = 0 := by
    refine Measure.measure_prod_null_of_ae_null hmeas ?_
    filter_upwards with t
    exact hsec t
  have hle : volume {x : V3 | x ⬝ᵥ w = ‖x‖ * ‖w‖ * a}
      ≤ (volume.prod volume) {p : ℝ × ℂ | p.1 * ‖w‖
          = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a} := by
    calc volume {x : V3 | x ⬝ᵥ w = ‖x‖ * ‖w‖ * a}
        ≤ volume ((fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹'
            {p : ℝ × ℂ | p.1 * ‖w‖ = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a}) :=
          measure_mono hsub
      _ = (volume.prod volume) {p : ℝ × ℂ | p.1 * ‖w‖
            = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) * ‖w‖ * a} :=
          (measurePreserving_proj e1 e2 e3 he).measure_preimage hmeas.nullMeasurableSet
  exact le_antisymm (le_trans hle hv2.le) zero_le

/-- HOL `FRUSTT_RCONE_GE` (TSKAJXY3.hl:1275; proved 2026-09-29 wave B1:
the symmetric difference dies because `frustt ⊆ rconeGe ∩ H` makes one side
empty, and the other side lands in the circular-cone surface
`{x | (x-u)·(v-u) = dist x u * dist v u * a}`, which is null by
`p21_cone_surf_null`). -/
theorem FRUSTT_RCONE_GE (u v : V3) (h a : ℝ) (ha : 0 < a) (huv : u ≠ v) :
    nullSet (symmDiff (frustt u v h a)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})) := by
  -- the circular-cone surface is null (translate the apex to 0)
  have hB : volume {x : V3 | (x - u) ⬝ᵥ (v - u) = dist x u * dist v u * a} = 0 := by
    have hT : volume {y : V3 | y ⬝ᵥ (v - u) = ‖y‖ * ‖v - u‖ * a} = 0 :=
      p21_cone_surf_null (v - u) (sub_ne_zero.2 (Ne.symm huv)) a ha
    have hsub : {x : V3 | (x - u) ⬝ᵥ (v - u) = dist x u * dist v u * a}
        ⊆ (fun y : V3 => u + y) '' {y : V3 | y ⬝ᵥ (v - u) = ‖y‖ * ‖v - u‖ * a} := by
      rintro x hx
      refine ⟨x - u, ?_, by abel⟩
      simp only [Set.mem_setOf_eq, dist_eq_norm] at hx ⊢
      exact hx
    have hle : volume {x : V3 | (x - u) ⬝ᵥ (v - u) = dist x u * dist v u * a}
        ≤ volume ((fun y : V3 => u + y) '' {y : V3 | y ⬝ᵥ (v - u) = ‖y‖ * ‖v - u‖ * a}) :=
      measure_mono hsub
    rw [volume_image_add_left, hT] at hle
    exact le_antisymm hle zero_le
  -- the symmetric difference lands inside the surface
  have hsub : symmDiff (frustt u v h a)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})
      ⊆ {x : V3 | (x - u) ⬝ᵥ (v - u) = dist x u * dist v u * a} := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with ⟨hxA, hxB⟩ | ⟨hxA, hxB⟩
    · exfalso
      simp only [frustt, frustum, rconeGt, Set.mem_inter_iff, Set.mem_setOf_eq] at hxA
      obtain ⟨⟨hf1, hf2⟩, hgt⟩ := hxA
      have hge : (x - u) ⬝ᵥ (v - u) ≥ dist x u * dist v u * a := le_of_lt hgt
      exact hxB ⟨hge, hf2⟩
    · obtain ⟨hge, hH⟩ := hxA
      simp only [frustt, frustum, rconeGt, Set.mem_inter_iff, Set.mem_setOf_eq] at hxB
      show (x - u) ⬝ᵥ (v - u) = dist x u * dist v u * a
      by_cases hgt : (x - u) ⬝ᵥ (v - u) > dist x u * dist v u * a
      · exfalso
        refine hxB ⟨⟨?_, hH⟩, hgt⟩
        have hnn : (0:ℝ) ≤ dist x u * dist v u * a :=
          mul_nonneg (mul_nonneg dist_nonneg dist_nonneg) ha.le
        exact le_of_lt (lt_of_le_of_lt hnn hgt)
      · exact le_antisymm (not_lt.1 hgt) hge
  show volume (symmDiff (frustt u v h a)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})) = 0
  exact le_antisymm (le_trans (measure_mono hsub) hB.le) zero_le

/-! ## B2-wave private kit: null planes & the `dihV = π` antiparallel engine (2026-09-30)

Consumed by `FRUSTT_WEDGE_RCONE_GE` / `NOT_COPLANAR_EXTREME_MCELL2` /
`MCELL2_DIHV_LT_PI`: any three points span a proper affine subspace of `V3`
(hence null — the ConformingAuto2 `affineSpan_three_ne_top` mechanism, copied
here as private kit), affine combinations of points of an affine subspace stay
in it, and `dihV = π` forces the first projected difference to be antiparallel
to the second (the equality case of Cauchy–Schwarz), putting the four points
into one plane. -/

/-- A 2-vector span has rank at most 2 (copy of the private ConformingAuto2
`finrank_span_pair_le_two_auto2`). -/
private theorem p21_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h
  have h2 : ({a, b} : Finset V3).card ≤ 2 := by
    calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
      _ = 2 := by simp
  omega

/-- The affine span of three points of `V3` is a proper affine subspace. -/
private theorem p21_affSpan3_ne_top (a b c : V3) :
    (affineSpan ℝ ({a, b, c} : Set V3)) ≠ ⊤ := by
  intro htop
  have hdir : (affineSpan ℝ ({a, b, c} : Set V3)).direction = ⊤ := by
    rw [htop]; exact AffineSubspace.direction_top ℝ V3 V3
  have hvs : vectorSpan ℝ ({a, b, c} : Set V3)
      = Submodule.span ℝ ({b - a, c - a} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show a ∈ ({a, b, c} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl)
      · exact Submodule.subset_span ⟨b, by simp, rfl⟩
      · exact Submodule.subset_span ⟨c, by simp, rfl⟩
  have hle : Module.finrank ℝ (affineSpan ℝ ({a, b, c} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact p21_finrank_span_pair_le_two (b - a) (c - a)
  rw [hdir, finrank_top] at hle
  have h3 : Module.finrank ℝ V3 = 3 := by simp [V3]
  omega

/-- The affine span of three points of `V3` is Lebesgue-null. -/
private theorem p21_affSpan3_null (a b c : V3) :
    volume ((affineSpan ℝ ({a, b, c} : Set V3) : Set V3)) = 0 :=
  Measure.addHaar_affineSubspace volume _ (p21_affSpan3_ne_top a b c)

/-- An affine combination (weights summing to 1) of points of an affine
subspace stays in the subspace. -/
private theorem p21_affineCombo_mem_of_mem {S : AffineSubspace ℝ V3} {F : Finset V3}
    {f : V3 → ℝ} {b : V3} (hS : ∀ z ∈ F, (z : V3) ∈ (S : Set V3)) (hb : b ∈ S)
    (hsum : ∑ z ∈ F, f z = 1) {x : V3} (hx : x = ∑ z ∈ F, f z • z) :
    x ∈ (S : Set V3) := by
  have hdir : ∑ z ∈ F, f z • (z - b) ∈ S.direction := by
    refine Submodule.sum_mem _ (fun z hz => ?_)
    exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction (hS z hz) hb)
  have hsplit : ∑ z ∈ F, f z • z
      = ∑ z ∈ F, f z • (z - b) + (∑ z ∈ F, f z) • b := by
    rw [Finset.sum_smul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ => by rw [← smul_add, sub_add_cancel])
  have hx' : x = ∑ z ∈ F, f z • (z - b) + b := by
    rw [hx, hsplit, hsum, one_smul]
  rw [hx']
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hb

/-- The half-plane `affGe {u,v} {w}` is null (it lives in the plane spanned by
`u, v, w`, a proper affine subspace of `V3`). -/
private theorem p21_affGe_null (u v w : V3) :
    volume (affGe ({u, v} : Set V3) ({w} : Set V3)) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (p21_affSpan3_null u v w)
  obtain ⟨f, hfin, hx, -, hsum⟩ := hx
  refine p21_affineCombo_mem_of_mem (S := affineSpan ℝ ({u, v, w} : Set V3))
    (F := hfin.toFinset) (f := f) (b := w) (x := x) ?_ ?_ hsum hx
  · intro z hz
    have hz' : z ∈ ({u, v} : Set V3) ∪ ({w} : Set V3) := by
      simpa [Set.Finite.mem_toFinset] using hz
    rcases hz' with hz' | hz'
    · rcases hz' with rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
    · rw [hz']
      exact subset_affineSpan ℝ _ (by simp)
  · exact subset_affineSpan ℝ _ (by simp)

/-- Membership of a four-point set, in a deterministic disjunction order. -/
private theorem p21_mem_quad {α : Type*} {z a b c d : α}
    (hz : z ∈ ({a, b, c, d} : Set α)) : z = a ∨ z = b ∨ z = c ∨ z = d := by
  rcases Set.mem_insert_iff.1 hz with rfl | h2
  · exact Or.inl rfl
  · rcases Set.mem_insert_iff.1 h2 with rfl | h3
    · exact Or.inr (Or.inl rfl)
    · rcases Set.mem_insert_iff.1 h3 with rfl | h4
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.1 h4)))

/-- A coplanar quadruple forces the `affGe` slab spanned by one diagonal pair
against the other to be null (both diagonal pairs sit in one plane). -/
private theorem p21_coplanar_affGe_null {a b c d : V3}
    (hcp : Coplanar ({a, b, c, d} : Set V3)) :
    volume (affGe ({a, b} : Set V3) ({c, d} : Set V3)) = 0 := by
  obtain ⟨p, q, r, hsub⟩ := hcp
  refine measure_mono_null (fun x hx => ?_) (p21_affSpan3_null p q r)
  obtain ⟨f, hfin, hx, -, hsum⟩ := hx
  refine p21_affineCombo_mem_of_mem (S := affineSpan ℝ ({p, q, r} : Set V3))
    (F := hfin.toFinset) (f := f) (b := r) (x := x) ?_ ?_ hsum hx
  · intro z hz
    rcases (Set.Finite.mem_toFinset hfin).mp hz with ((rfl | rfl) | (rfl | rfl))
    · exact hsub (by simp)
    · exact hsub (by simp)
    · exact hsub (by simp)
    · exact hsub (by simp)
  · exact subset_affineSpan ℝ _ (by simp)

/-- Three collinear points plus any fourth are coplanar. -/
private theorem p21_collinear3_coplanar4 (a b c d : V3) (h : Collinear3 a b c) :
    Coplanar ({a, b, c, d} : Set V3) := by
  by_cases hab : a = b
  · refine ⟨a, c, d, fun z hz => ?_⟩
    rcases p21_mem_quad hz with h1 | h2 | h3 | h4
    · rw [h1]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h2, ← hab]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h3]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h4]; exact subset_affineSpan ℝ _ (by simp)
  · refine ⟨a, b, d, fun z hz => ?_⟩
    have hsub2 : ({a, b} : Set V3) ⊆ ({a, b, d} : Set V3) := by
      intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hx2
      · exact Set.mem_insert_iff.2 (Or.inl rfl)
      · rcases Set.mem_singleton_iff.1 hx2 with rfl
        exact Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl)))
    rcases p21_mem_quad hz with h1 | h2 | h3 | h4
    · rw [h1]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h2]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h3]; exact affineSpan_mono ℝ hsub2
        (Collinear.mem_affineSpan_of_mem_of_ne (p₁ := a) (p₂ := b) (p₃ := c)
          h (by simp) (by simp) (by simp) hab)
    · rw [h4]; exact subset_affineSpan ℝ _ (by simp)

/-- Variant of `p21_collinear3_coplanar4` with the collinear point in the last
slot. -/
private theorem p21_collinear3_coplanar4_last (a b c d : V3) (h : Collinear3 a b d) :
    Coplanar ({a, b, c, d} : Set V3) := by
  by_cases hab : a = b
  · refine ⟨a, c, d, fun z hz => ?_⟩
    rcases p21_mem_quad hz with h1 | h2 | h3 | h4
    · rw [h1]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h2, ← hab]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h3]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h4]; exact subset_affineSpan ℝ _ (by simp)
  · refine ⟨a, b, c, fun z hz => ?_⟩
    have hsub2 : ({a, b} : Set V3) ⊆ ({a, b, c} : Set V3) := by
      intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hx2
      · exact Set.mem_insert_iff.2 (Or.inl rfl)
      · rcases Set.mem_singleton_iff.1 hx2 with rfl
        exact Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl)))
    rcases p21_mem_quad hz with h1 | h2 | h3 | h4
    · rw [h1]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h2]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h3]; exact subset_affineSpan ℝ _ (by simp)
    · rw [h4]; exact affineSpan_mono ℝ hsub2
        (Collinear.mem_affineSpan_of_mem_of_ne (p₁ := a) (p₂ := b) (p₃ := d)
          h (by simp) (by simp) (by simp) hab)

/-- `dihV = π` forces the first projected difference to be antiparallel to the
second: `w2 - w0` lands in the span of `w3 - w0` and `w1 - w0` (Gram
antiparallelism — the equality case of Cauchy–Schwarz on the projected
vectors `vap`, `vbp`). -/
private theorem p21_dihV_eq_pi_span {w0 w1 w2 w3 : V3} (hvc : w1 - w0 ≠ 0)
    (hpi : dihV w0 w1 w2 w3 = Real.pi) :
    ∃ s t : ℝ, (w2 - w0 : V3) = s • (w3 - w0) + t • (w1 - w0) := by
  have hA : (0:ℝ) < (w1 - w0) ⬝ᵥ (w1 - w0) := by
    have hp : (0:ℝ) < ‖(w1 - w0 : V3)‖ ^ 2 := by
      have h := norm_pos_iff.2 hvc; nlinarith
    rwa [p21_norm_sq] at hp
  -- unpack `dihV` as the arccos of the normalized projected dot
  have hdih : dihV w0 w1 w2 w3
      = Real.arccos ((((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)
            - ((w2 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0)) ⬝ᵥ
          (((w1 - w0) ⬝ᵥ (w1 - w0)) • (w3 - w0)
            - ((w3 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0))
        / (‖(((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)
            - ((w2 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0) : V3)‖
          * ‖(((w1 - w0) ⬝ᵥ (w1 - w0)) • (w3 - w0)
            - ((w3 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0) : V3)‖)) := by
    show arcV 0 ((((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)
          - ((w2 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0) : V3))
      ((((w1 - w0) ⬝ᵥ (w1 - w0)) • (w3 - w0)
          - ((w3 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0) : V3)) = _
    rw [arcV]
    simp [sub_zero, dist_zero_right]
  set vap := ((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)
    - ((w2 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0) with hvap
  set vbp := ((w1 - w0) ⬝ᵥ (w1 - w0)) • (w3 - w0)
    - ((w3 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0) with hvbp
  rw [hdih, ← Real.arccos_neg_one] at hpi
  -- the normalized projected dot lies in [-1, 1] (Cauchy–Schwarz)
  have hrange : |(vap ⬝ᵥ vbp : ℝ)| ≤ ‖vap‖ * ‖vbp‖ := by
    have h1 := abs_real_inner_le_norm (x := vap) (y := vbp)
    rwa [inner_eq_dot] at h1
  have hRabs : |(vap ⬝ᵥ vbp : ℝ) / (‖vap‖ * ‖vbp‖)| ≤ 1 := by
    rcases eq_or_ne (‖vap‖ * ‖vbp‖) 0 with h0 | h0
    · rw [h0, div_zero]; norm_num
    · rw [abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact (div_le_one
        (lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm h0))).2 hrange
  have hrat : ((vap ⬝ᵥ vbp : ℝ) / (‖vap‖ * ‖vbp‖)) = -1 :=
    (Real.arccos_inj (abs_le.1 hRabs).1 (abs_le.1 hRabs).2
      (by norm_num) (by norm_num)).1 hpi
  have hden : ‖vap‖ * ‖vbp‖ ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrat
    norm_num at hrat
  have hbpne : ‖vbp‖ ≠ 0 := fun hh => hden (by rw [hh, mul_zero])
  have hbppos : 0 < ‖vbp‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hbpne)
  -- the equality case of Cauchy–Schwarz: `vap` is antiparallel to `vbp`
  have hdot : inner ℝ vap vbp = -‖vap‖ * ‖vbp‖ := by
    have h := congrArg (fun r : ℝ => r * (‖vap‖ * ‖vbp‖)) hrat
    rw [← inner_eq_dot, div_mul_cancel₀ _ hden] at h
    linarith
  have hzero : vap + (‖vap‖ / ‖vbp‖) • vbp = 0 := by
    have hsq : ‖vap + (‖vap‖ / ‖vbp‖) • vbp‖ ^ 2 = 0 := by
      have hform := norm_add_sq_real (x := vap) (y := (‖vap‖ / ‖vbp‖) • vbp)
      rw [real_inner_smul_right, hdot, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖vap‖ / ‖vbp‖)] at hform
      have hR0 : ‖vap‖ ^ 2 + 2 * (‖vap‖ / ‖vbp‖ * (-‖vap‖ * ‖vbp‖))
          + (‖vap‖ / ‖vbp‖ * ‖vbp‖) ^ 2 = 0 := by
        have e1 : (‖vap‖ : ℝ) / ‖vbp‖ * ‖vbp‖ = ‖vap‖ := div_mul_cancel₀ _ hbpne
        have e2 : (‖vap‖ : ℝ) / ‖vbp‖ * (‖vap‖ * ‖vbp‖) = ‖vap‖ ^ 2 := by
          rw [mul_comm ‖vap‖ ‖vbp‖, ← mul_assoc, div_mul_cancel₀ _ hbpne, sq]
        calc ‖vap‖ ^ 2 + 2 * (‖vap‖ / ‖vbp‖ * (-‖vap‖ * ‖vbp‖))
            + (‖vap‖ / ‖vbp‖ * ‖vbp‖) ^ 2
          = ‖vap‖ ^ 2 - 2 * ((‖vap‖ / ‖vbp‖) * (‖vap‖ * ‖vbp‖))
            + ((‖vap‖ / ‖vbp‖) * ‖vbp‖) ^ 2 := by ring
        _ = ‖vap‖ ^ 2 - 2 * ‖vap‖ ^ 2 + ‖vap‖ ^ 2 := by rw [e2, e1]
        _ = 0 := by ring
      rw [hform, hR0]
    have h0 : ‖vap + (‖vap‖ / ‖vbp‖) • vbp‖ = 0 := sq_eq_zero_iff.1 hsq
    exact norm_eq_zero.1 h0
  rw [hvap, hvbp] at hzero
  have hvapneg : ((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)
      - ((w2 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0)
      = -((‖vap‖ / ‖vbp‖) • (((w1 - w0) ⬝ᵥ (w1 - w0)) • (w3 - w0)
          - ((w3 - w0) ⬝ᵥ (w1 - w0)) • (w1 - w0))) :=
    eq_neg_of_add_eq_zero_left hzero
  -- solve for `w2 - w0`
  refine ⟨-(‖vap‖ / ‖vbp‖),
    (((w2 - w0) ⬝ᵥ (w1 - w0)) + (‖vap‖ / ‖vbp‖) * ((w3 - w0) ⬝ᵥ (w1 - w0)))
      / ((w1 - w0) ⬝ᵥ (w1 - w0)), ?_⟩
  have hAne : ((w1 - w0) ⬝ᵥ (w1 - w0) : ℝ) ≠ 0 := ne_of_gt hA
  have hstep : ((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)
      = (((w2 - w0) ⬝ᵥ (w1 - w0)) + (‖vap‖ / ‖vbp‖) * ((w3 - w0) ⬝ᵥ (w1 - w0))) • (w1 - w0)
        + (-(‖vap‖ / ‖vbp‖) * ((w1 - w0) ⬝ᵥ (w1 - w0))) • (w3 - w0) := by
    linear_combination (norm := module) hvapneg
  calc w2 - w0
      = (1 / ((w1 - w0) ⬝ᵥ (w1 - w0))) •
          (((w1 - w0) ⬝ᵥ (w1 - w0)) • (w2 - w0)) := by
        rw [one_div, inv_smul_smul₀ hAne]
    _ = (1 / ((w1 - w0) ⬝ᵥ (w1 - w0))) •
          ((((w2 - w0) ⬝ᵥ (w1 - w0)) + (‖vap‖ / ‖vbp‖) * ((w3 - w0) ⬝ᵥ (w1 - w0))) • (w1 - w0)
        + (-(‖vap‖ / ‖vbp‖) * ((w1 - w0) ⬝ᵥ (w1 - w0))) • (w3 - w0)) := by rw [hstep]
    _ = (-(‖vap‖ / ‖vbp‖)) • (w3 - w0)
        + ((((w2 - w0) ⬝ᵥ (w1 - w0)) + (‖vap‖ / ‖vbp‖) * ((w3 - w0) ⬝ᵥ (w1 - w0)))
          / ((w1 - w0) ⬝ᵥ (w1 - w0))) • (w1 - w0) := by
        rw [smul_add, smul_smul, smul_smul]
        have h1 : ((1 / ((w1 - w0) ⬝ᵥ (w1 - w0)) : ℝ) *
              (((w2 - w0) ⬝ᵥ (w1 - w0)) + (‖vap‖ / ‖vbp‖) * ((w3 - w0) ⬝ᵥ (w1 - w0))))
            = (((w2 - w0) ⬝ᵥ (w1 - w0)) + (‖vap‖ / ‖vbp‖) * ((w3 - w0) ⬝ᵥ (w1 - w0)))
              / ((w1 - w0) ⬝ᵥ (w1 - w0)) := by ring
        have h2 : ((1 / ((w1 - w0) ⬝ᵥ (w1 - w0)) : ℝ) *
              (-(‖vap‖ / ‖vbp‖) * ((w1 - w0) ⬝ᵥ (w1 - w0))))
            = -(‖vap‖ / ‖vbp‖) := by field_simp
        rw [h1, h2, add_comm]

/-- HOL `FRUSTT_WEDGE_RCONE_GE` (TSKAJXY3.hl:1368; proved 2026-09-30 wave B2:
the symmetric difference dies inside `symmDiff (frustt) (rconeGe ∩ H)` — null
by `FRUSTT_RCONE_GE` — together with the two bounding half-planes of the
closed wedge, which stick out of the open wedge by `WEDGE_WEDGE_GE`
(PA18:873) and are null planes by `p21_affGe_null`; `WEDGE_SUBSET_WEDGE_GE`
(PA18:2457) kills the first branch outright). -/
theorem FRUSTT_WEDGE_RCONE_GE (u v w1 w2 : V3) (h a : ℝ) (ha : 0 < a) (huv : u ≠ v)
    (ha1 : a ≤ 1) (hnn : 0 ≤ h)
    (hc1 : ¬Collinear3 u v w1) (hc2 : ¬Collinear3 u v w2) :
    nullSet (symmDiff (frustt u v h a ∩ wedge u v w1 w2)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖} ∩
        wedgeGe u v w1 w2)) := by
  classical
  have hsub : symmDiff (frustt u v h a ∩ wedge u v w1 w2)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖} ∩
        wedgeGe u v w1 w2)
      ⊆ symmDiff (frustt u v h a)
          (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})
        ∪ affGe ({u, v} : Set V3) ({w1} : Set V3)
        ∪ affGe ({u, v} : Set V3) ({w2} : Set V3) := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with ⟨⟨hxA, hxW⟩, hxN⟩ | ⟨⟨⟨hxB, hxH⟩, hxWg⟩, hxN⟩
    · by_cases hxB2 : x ∈ rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖}
      · exact (hxN ⟨hxB2, WEDGE_SUBSET_WEDGE_GE u v w1 w2 hxW⟩).elim
      · exact Or.inl (Or.inl (Set.mem_symmDiff.2 (Or.inl ⟨hxA, hxB2⟩)))
    · by_cases hxA : x ∈ frustt u v h a
      · have hxW : x ∉ wedge u v w1 w2 := fun hw =>
          hxN ⟨hxA, hw⟩
        rcases WEDGE_WEDGE_GE u v w1 w2 hc1 hc2 hxWg with (hy | hy) | hy
        · exact absurd hy hxW
        · exact Or.inl (Or.inr hy)
        · exact Or.inr hy
      · exact Or.inl (Or.inl (Set.mem_symmDiff.2 (Or.inr ⟨⟨hxB, hxH⟩, hxA⟩)))
  have hA := FRUSTT_RCONE_GE u v h a ha huv
  have hB := p21_affGe_null u v w1
  have hC := p21_affGe_null u v w2
  unfold nullSet at hA ⊢
  refine le_antisymm ?_ (by simp)
  calc volume (symmDiff (frustt u v h a ∩ wedge u v w1 w2)
        (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖} ∩
          wedgeGe u v w1 w2))
      ≤ volume (symmDiff (frustt u v h a)
          (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})
        ∪ affGe ({u, v} : Set V3) ({w1} : Set V3)
        ∪ affGe ({u, v} : Set V3) ({w2} : Set V3)) := measure_mono hsub
    _ ≤ volume (symmDiff (frustt u v h a)
          (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖}))
        + volume (affGe ({u, v} : Set V3) ({w1} : Set V3))
        + volume (affGe ({u, v} : Set V3) ({w2} : Set V3)) := by
        have hstep2 : volume ((symmDiff (frustt u v h a)
              (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})) ∪
            affGe ({u, v} : Set V3) ({w1} : Set V3))
            ≤ volume (symmDiff (frustt u v h a)
                (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖}))
              + volume (affGe ({u, v} : Set V3) ({w1} : Set V3)) := measure_union_le _ _
        exact le_trans (measure_union_le _ _) (add_le_add_left hstep2 _)
    _ = 0 := by rw [hA, hB, hC]; ring

/-- HOL `MCELL2_SUBSET_AFF_GE` (TSKAJXY3.hl:1419).  Suffixed `_p21` at the
atn2-merge: PackingAuto18.lean hosts a same-named `MCELL2_SUBSET_AFF_GE`
with a DIFFERENT statement (hypothesis-free, `hdV`/`tail` form) — the two
are NOT twins and must not be deduped (plan §6). -/
theorem MCELL2_SUBSET_AFF_GE_p21 (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) :
    mcell2 V ul ⊆
      affGe {elV ul 0, elV ul 1} ({mxi V ul, omegaListN V ul 3} : Set V3) := by
  intro x hx
  rw [mcell2] at hx
  have hcent : hdV ul = elV ul 0 ∧ hdV ul.tail = elV ul 1 := by
    cases ul with
    | nil => exact absurd hb.1 (by simp)
    | cons a t =>
      cases t with
      | nil => exact absurd hb.1 (by simp)
      | cons b t => exact ⟨rfl, rfl⟩
  by_cases hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
  · rw [if_pos hcond, hcent.1, hcent.2] at hx
    exact hx.2
  · rw [if_neg hcond] at hx
    exact absurd hx (by simp)

/-- HOL `NOT_COPLANAR_EXTREME_MCELL2` (TSKAJXY3.hl:1434; proved 2026-09-30
wave B2: `mcell2` lives in the half-plane `affGe {e0,e1} {mxi, ω3}` (its
defining slab), which is a null plane once the four extreme points are
coplanar — so coplanarity would force `mcell2` null, against `hn`). -/
theorem NOT_COPLANAR_EXTREME_MCELL2 (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    ¬Coplanar ({elV ul 0, elV ul 1, mxi V ul, omegaListN V ul 3} : Set V3) := by
  intro hcp
  refine hn (measure_mono_null (MCELL2_SUBSET_AFF_GE_p21 V ul hp hs hb) ?_)
  exact p21_coplanar_affGe_null hcp

/-- HOL `MCELL2_DIHV_LT_PI` (TSKAJXY3.hl:1456; proved 2026-09-30 wave B2:
`dihV = π` forces the Gram antiparallelism of the projected differences
(`p21_dihV_eq_pi_span`, the Cauchy–Schwarz equality case), which puts the
four extreme points into the plane `affineSpan {e0, e1, ω3}` — contradicting
`NOT_COPLANAR_EXTREME_MCELL2`). -/
theorem MCELL2_DIHV_LT_PI (V X : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hn : ¬nullSet X) :
    dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) < Real.pi := by
  by_cases hlt : dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) < Real.pi
  · exact hlt
  · exfalso
    have hn2 : ¬nullSet (mcell2 V ul) := by rw [← hX]; exact hn
    have hncp := NOT_COPLANAR_EXTREME_MCELL2 V ul hp hs hb hn2
    have h1 : ¬Collinear3 (elV ul 0) (elV ul 1) (mxi V ul) := fun hc =>
      hncp (p21_collinear3_coplanar4 _ _ _ _ hc)
    have he1 : (elV ul 1 - elV ul 0 : V3) ≠ 0 := by
      intro h0
      exact h1 (collinear3_of_eq (sub_eq_zero.1 h0))
    have hpi : dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) = Real.pi :=
      le_antisymm (Real.arccos_le_pi _) (not_lt.1 hlt)
    obtain ⟨s, t, hspan⟩ := p21_dihV_eq_pi_span he1 hpi
    refine hncp ⟨elV ul 0, elV ul 1, omegaListN V ul 3, fun z hz => ?_⟩
    rcases p21_mem_quad hz with rfl | rfl | rfl | rfl
    · exact subset_affineSpan ℝ _ (by simp)
    · exact subset_affineSpan ℝ _ (by simp)
    · have hmx : mxi V ul
          = (1 - s - t) • elV ul 0 + t • elV ul 1 + s • omegaListN V ul 3 := by
        linear_combination (norm := module) hspan
      exact p21_mem_affineSpan_of_sum (by ring) hmx
    · exact subset_affineSpan ℝ _ (by simp)

/-- HOL `MCELL2_DIHV_AZIM` (TSKAJXY3.hl:1477; proved 2026-09-30 wave B2: the
two extreme points are individually non-collinear with the axis (three
collinear of the four would be coplanar), so `azim_dihv_same` below `π` and
`azim_dihv_compl` + `azim_compl` above `π` give `dihV = azim` with the pair
taken in the matching order). -/
theorem MCELL2_DIHV_AZIM (V X : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hn : ¬nullSet X) :
    ∃ w1 w2 : V3, {w1, w2} = ({mxi V ul, omegaListN V ul 3} : Set V3) ∧
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) =
        azim (elV ul 0) (elV ul 1) w1 w2 := by
  have hn2 : ¬nullSet (mcell2 V ul) := by rw [← hX]; exact hn
  have hncp := NOT_COPLANAR_EXTREME_MCELL2 V ul hp hs hb hn2
  have h1 : ¬Collinear3 (elV ul 0) (elV ul 1) (mxi V ul) := fun hc =>
    hncp (p21_collinear3_coplanar4 _ _ _ _ hc)
  have h2 : ¬Collinear3 (elV ul 0) (elV ul 1) (omegaListN V ul 3) := fun hc =>
    hncp (p21_collinear3_coplanar4_last (elV ul 0) (elV ul 1) (mxi V ul)
      (omegaListN V ul 3) hc)
  by_cases hlt : azim (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) < Real.pi
  · refine ⟨mxi V ul, omegaListN V ul 3, rfl, (azim_dihv_same h1 h2 hlt).symm⟩
  · have hge : Real.pi ≤ azim (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) :=
      not_lt.1 hlt
    have hne0 : azim (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) ≠ 0 := by
      intro hh
      rw [hh] at hge
      linarith [Real.pi_pos]
    have hdihv : dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3)
        = 2 * Real.pi - azim (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) := by
      linarith [azim_dihv_compl h1 h2 hge]
    have hswap : azim (elV ul 0) (elV ul 1) (omegaListN V ul 3) (mxi V ul)
        = 2 * Real.pi - azim (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) := by
      rw [azim_compl h1 h2, if_neg hne0]
    refine ⟨omegaListN V ul 3, mxi V ul, Set.pair_comm _ _, ?_⟩
    rw [hswap]; linarith

/-- HOL `BIS_LE_NORM` (TSKAJXY3.hl:1510; proved by coordinate expansion of
the half-space form `BIS_LE_EQ_HALFSPACE`). -/
theorem BIS_LE_NORM (u v : V3) :
    bisLe u v = {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ ‖v - u‖ ^ 2 / 2} := by
  have hbase := BIS_LE_EQ_HALFSPACE u v
  have eL : ∀ y : V3, ((y - u) ⬝ᵥ (v - u) : ℝ) =
      (y - u) 0 * (v - u) 0 + (y - u) 1 * (v - u) 1 + (y - u) 2 * (v - u) 2 := by
    intro y
    show dotProduct (WithLp.ofLp (y - u)) (WithLp.ofLp v - WithLp.ofLp u)
        = (y - u) 0 * (v - u) 0 + (y - u) 1 * (v - u) 1 + (y - u) 2 * (v - u) 2
    rw [WithLp.ofLp_sub 2 y u, WithLp.ofLp_sub 2 v u,
      p21_dotPi_sub_l, p21_dotPi_sub_r, p21_dotPi_sub_r]
    simp only [p21_dot_apply, Pi.sub_apply]
    ring
  have eR : ∀ y : V3, ((v - u) ⬝ᵥ y : ℝ) =
      (v - u) 0 * y 0 + (v - u) 1 * y 1 + (v - u) 2 * y 2 := by
    intro y
    show dotProduct (WithLp.ofLp (v - u)) (WithLp.ofLp y)
        = (v - u) 0 * y 0 + (v - u) 1 * y 1 + (v - u) 2 * y 2
    rw [p21_dotPi_comm (WithLp.ofLp (v - u)) (WithLp.ofLp y),
      WithLp.ofLp_sub 2 v u, p21_dotPi_sub_r]
    simp only [p21_dot_apply, Pi.sub_apply]
    ring
  have eN : ‖v - u‖ ^ 2 =
      (v - u) 0 * (v - u) 0 + (v - u) 1 * (v - u) 1 + (v - u) 2 * (v - u) 2 := by
    rw [p21_norm_sq]
    show dotProduct (WithLp.ofLp v - WithLp.ofLp u) (WithLp.ofLp v - WithLp.ofLp u) = _
    rw [WithLp.ofLp_sub 2 v u, p21_dotPi_sub_l, p21_dotPi_sub_r, p21_dotPi_sub_r]
    simp only [p21_dot_apply, Pi.sub_apply]
    ring
  have eV2 : ((v ⬝ᵥ v : ℝ)) = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    show dotProduct (WithLp.ofLp v) (WithLp.ofLp v) = _
    rw [dotProduct, Fin.sum_univ_three]
    ring
  have eU2 : ((u ⬝ᵥ u : ℝ)) = (u 0)^2 + (u 1)^2 + (u 2)^2 := by
    show dotProduct (WithLp.ofLp u) (WithLp.ofLp u) = _
    rw [dotProduct, Fin.sum_univ_three]
    ring
  have hpivot : ∀ y : V3, ((y - u) ⬝ᵥ (v - u) : ℝ) ≤ ‖v - u‖ ^ 2 / 2 ↔
      2 * ((v - u) ⬝ᵥ y) ≤ v ⬝ᵥ v - u ⬝ᵥ u := by
    intro y
    rw [eL y, eR y, eN, eV2, eU2]
    have hs1 : ∀ i : Fin 3, (y - u) i = y i - u i := p21_apply_sub y u
    have hs2 : ∀ i : Fin 3, (v - u) i = v i - u i := p21_apply_sub v u
    simp only [hs1, hs2]
    constructor <;> intro h <;>
      simp only [mul_sub, sub_mul] at h ⊢ <;>
      ring_nf at h ⊢ <;> linarith
  ext y
  rw [hbase, Set.mem_setOf_eq, Set.mem_setOf_eq]
  exact (hpivot y).symm

/-- helper: `¬(A ≤ N/2) ↔ B < N/2` given `A + B = N`. -/
private theorem p21_pivot_lt_aux (x u v : V3) (hsum : ((x - v) ⬝ᵥ (u - v) : ℝ) +
    ((x - u) ⬝ᵥ (v - u) : ℝ) = ‖v - u‖ ^ 2) :
    ¬((x - v) ⬝ᵥ (u - v) ≤ ‖v - u‖ ^ 2 / 2) ↔
      (x - u) ⬝ᵥ (v - u) < ‖v - u‖ ^ 2 / 2 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    linarith
  · intro h hcon
    linarith

/-- HOL `BIS_LT_NORM` (TSKAJXY3.hl:1528; proved from the closed half-plane
form via the identity `(x-v)·(u-v) + (x-u)·(v-u) = ‖v-u‖²`). -/
theorem BIS_LT_NORM (u v x : V3) :
    dist x u < dist x v ↔ (x - u) ⬝ᵥ (v - u) < ‖v - u‖ ^ 2 / 2 := by
  have hA : ((x - v) ⬝ᵥ (u - v) : ℝ) + ((x - u) ⬝ᵥ (v - u) : ℝ) = ‖v - u‖ ^ 2 := by
    have eA : ((x - v) ⬝ᵥ (u - v) : ℝ) =
        (x - v) 0 * (u - v) 0 + (x - v) 1 * (u - v) 1 + (x - v) 2 * (u - v) 2 := by
      show dotProduct (WithLp.ofLp (x - v)) (WithLp.ofLp u - WithLp.ofLp v)
          = (x - v) 0 * (u - v) 0 + (x - v) 1 * (u - v) 1 + (x - v) 2 * (u - v) 2
      rw [WithLp.ofLp_sub 2 x v, WithLp.ofLp_sub 2 u v,
        p21_dotPi_sub_l, p21_dotPi_sub_r, p21_dotPi_sub_r]
      simp only [p21_dot_apply, Pi.sub_apply]
      ring
    have eB : ((x - u) ⬝ᵥ (v - u) : ℝ) =
        (x - u) 0 * (v - u) 0 + (x - u) 1 * (v - u) 1 + (x - u) 2 * (v - u) 2 := by
      show dotProduct (WithLp.ofLp (x - u)) (WithLp.ofLp v - WithLp.ofLp u)
          = (x - u) 0 * (v - u) 0 + (x - u) 1 * (v - u) 1 + (x - u) 2 * (v - u) 2
      rw [WithLp.ofLp_sub 2 x u, WithLp.ofLp_sub 2 v u,
        p21_dotPi_sub_l, p21_dotPi_sub_r, p21_dotPi_sub_r]
      simp only [p21_dot_apply, Pi.sub_apply]
      ring
    have eN : ‖v - u‖ ^ 2 =
        (v - u) 0 * (v - u) 0 + (v - u) 1 * (v - u) 1 + (v - u) 2 * (v - u) 2 := by
      rw [p21_norm_sq]
      show dotProduct (WithLp.ofLp v - WithLp.ofLp u) (WithLp.ofLp v - WithLp.ofLp u)
          = (v - u) 0 * (v - u) 0 + (v - u) 1 * (v - u) 1 + (v - u) 2 * (v - u) 2
      rw [WithLp.ofLp_sub 2 v u,
        p21_dotPi_sub_l, p21_dotPi_sub_r, p21_dotPi_sub_r]
      simp only [p21_dot_apply, Pi.sub_apply]
      ring
    rw [eA, eB, eN]
    simp only [p21_apply_sub x v, p21_apply_sub x u, p21_apply_sub v u,
      p21_apply_sub u v]
    ring
  rw [lt_iff_not_ge, p21_dist_le_half2 x v u, norm_sub_rev u v]
  exact p21_pivot_lt_aux x u v hA

/-- HOL `SDIFF_SYM` (TSKAJXY3.hl:1546). -/
theorem SDIFF_SYM (X Y : Set V3) : symmDiff X Y = symmDiff Y X := by
  ext x
  simp only [Set.mem_symmDiff]
  tauto


/-! ## Wave-B4 wedge closed forms (2026-09-30 wedge GIANT lane): the
`MCELL2_VOL_SPLIT_EXPLICIT`/`MCELL2_SOL` pair.  Kit: the closed-sector area
(`p21w_closedSector`, via the null angular rays `p21w_ray_null`), the
frustum-slab-wedge closed form `p21w_volume_rcone_slab_wedgeGe` (the
`VOLUME_FRUSTT_WEDGE` port, `azim · (1 - a ^ 2) / a ^ 2 * h ^ 3 / 6`, by the
ConicCapVolume slicing template: frame projection `measurePreserving_proj`,
cone-to-`‖ζ‖ ≤ √((1 - a ^ 2) / a ^ 2) * t ^ 2` slice reduction
(`p21w_cone_slice_sq`), closed-sector slices, and the single-piece
`∫ C * t ^ 2` core), the `wedgeGe = affGe` bridge `p21w_wedgeGe_eq_affGe`
(the `WEDGE_GE_EQ_AFF_GE` port, via the 2D sector-cone equivalence
`p21w_cone_to_band`/`p21w_band_to_cone`), and the radial kit
(`CONVEX_RCONE_GE` (PackingAuto12) for cone convexity, `pA_radial_of_mcell2`
— the `URRPHBZ2` port: mcell2 is
an apex-containing convex intersection, radially closed at the apex through
`RCONE_PAIR` and the wedge weight characterisation). -/

section WedgeClosedForms
open Complex
open scoped Pointwise


private theorem p21w_mcell2_hl_ul_ge (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    Real.sqrt 2 ≤ hl ul := by
  by_contra hge
  refine hn ?_
  rw [mcell2, if_neg (fun hc => hge hc.2)]
  exact measure_empty


private theorem p21w_span_singleton_ne_top (b : ℂ) (hb : b ≠ 0) :
    (Submodule.span ℝ {b} : Submodule ℝ ℂ) ≠ ⊤ := by
  intro htop
  have h1 : (1 : ℂ) ∈ (Submodule.span ℝ {b} : Submodule ℝ ℂ) := htop ▸ Submodule.mem_top
  have hI : (I : ℂ) ∈ (Submodule.span ℝ {b} : Submodule ℝ ℂ) := htop ▸ Submodule.mem_top
  obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨c2, hc2⟩ := Submodule.mem_span_singleton.mp hI
  have e1 : (↑c1 : ℂ) * b = 1 := by simpa using hc1
  have e2 : (↑c2 : ℂ) * b = I := by simpa using hc2
  have hre : (b.re : ℝ) ≠ 0 := by
    intro h0
    have h1r : ((↑c1 : ℂ) * b).re = (1 : ℂ).re := congrArg Complex.re e1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      h0, mul_zero, Complex.one_re] at h1r
    exact absurd h1r (by norm_num)
  have hzero : (c2 : ℝ) = 0 := by
    have h2r : ((↑c2 : ℂ) * b).re = (I : ℂ).re := congrArg Complex.re e2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      Complex.I_re] at h2r
    simp only [sub_zero] at h2r
    exact (mul_eq_zero.mp h2r).resolve_right hre
  have him : (1 : ℝ) = 0 := by
    have h2i : ((↑c2 : ℂ) * b).im = (I : ℂ).im := congrArg Complex.im e2
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hzero,
      zero_mul, Complex.I_im] at h2i
    exact absurd h2i (by norm_num)
  exact absurd him (by norm_num)

private theorem p21w_ray_null (a : ℂ) (ha : a ≠ 0) (θ : ℝ) :
    volume {z : ℂ | ang (a⁻¹ * z) = θ} = 0 := by
  classical
  have hb : a * Complex.exp (θ * I) ≠ 0 := mul_ne_zero ha (Complex.exp_ne_zero _)
  have hsub : {z : ℂ | ang (a⁻¹ * z) = θ}
      ⊆ ((Submodule.span ℝ {a * Complex.exp (θ * I)} : Submodule ℝ ℂ) : Set ℂ) := by
    intro z hz
    have hw : (a⁻¹ * z : ℂ) = (‖a⁻¹ * z‖ : ℂ) * Complex.exp (θ * I) := by
      rw [← hz]
      exact ang_mul_exp _
    refine Submodule.mem_span_singleton.mpr ⟨(‖a⁻¹ * z‖ : ℝ), ?_⟩
    show ((‖a⁻¹ * z‖ : ℝ) : ℂ) * (a * Complex.exp (θ * I)) = z
    have hstep : ((‖a⁻¹ * z‖ : ℝ) : ℂ) * (a * Complex.exp (θ * I))
        = (a : ℂ) * ((‖a⁻¹ * z‖ : ℂ) * Complex.exp (θ * I)) :=
      mul_left_comm _ _ _
    rw [hstep, ← hw, mul_inv_cancel_left₀ ha z]
  have hspan : volume ((Submodule.span ℝ {a * Complex.exp (θ * I)} : Submodule ℝ ℂ) : Set ℂ) = 0 :=
    Measure.addHaar_submodule (E := ℂ) volume _ (p21w_span_singleton_ne_top _ hb)
  have hle : volume {z : ℂ | ang (a⁻¹ * z) = θ}
      ≤ volume ((Submodule.span ℝ {a * Complex.exp (θ * I)} : Submodule ℝ ℂ) : Set ℂ) :=
    measure_mono hsub
  rw [hspan] at hle
  exact le_antisymm hle (by simp)

/-- closed disc sector: `‖ζ‖ ≤ R`, angle in the closed band `[0, θ]`. -/
private theorem p21w_closedSector (a : ℂ) (ha : a ≠ 0) (R θ : ℝ) (hR : 0 ≤ R)
    (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) :
    volume {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
      = ENNReal.ofReal (R ^ 2 * θ / 2) := by
  classical
  have hA : volume {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ}
      = ENNReal.ofReal (R ^ 2 * θ / 2) := volume_sector_rot ha hR hθ0 hθ2π
  have hray := p21w_ray_null a ha 0
  have hrayθ := p21w_ray_null a ha θ
  have hAD : {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ}
      ⊆ {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ} := by
    intro z hz
    exact ⟨hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2⟩
  have hDC : {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
      ⊆ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ} := by
    intro z hz
    exact ⟨le_of_lt hz.1, hz.2.1, hz.2.2⟩
  have hsubDA : {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ} \
      {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ}
      ⊆ {z : ℂ | ang (a⁻¹ * z) = 0} ∪ {z : ℂ | ang (a⁻¹ * z) = θ} := by
    intro z hz
    have hDz : ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ := hz.1
    have hAz : ¬ (‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ) := hz.2
    by_cases hpos : 0 < ang (a⁻¹ * z)
    · rcases lt_or_eq_of_le hDz.2.2 with hlt | heq
      · exact absurd ⟨hDz.1, hpos, hlt⟩ hAz
      · exact Or.inr heq
    · exact Or.inl (le_antisymm (le_of_not_gt hpos) hDz.2.1)
  have hrayunion : volume ({z : ℂ | ang (a⁻¹ * z) = 0} ∪ {z : ℂ | ang (a⁻¹ * z) = θ}) = 0 := by
    have h : volume ({z : ℂ | ang (a⁻¹ * z) = 0} ∪ {z : ℂ | ang (a⁻¹ * z) = θ})
        ≤ volume {z : ℂ | ang (a⁻¹ * z) = 0} + volume {z : ℂ | ang (a⁻¹ * z) = θ} :=
      measure_union_le (F := Measure ℂ) (μ := volume) _ _
    rw [hray, hrayθ] at h
    simpa using h
  have hDle : volume {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
      ≤ volume {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ} := by
    have hstep : volume {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
        ≤ volume {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ}
          + volume ({z : ℂ | ang (a⁻¹ * z) = 0} ∪ {z : ℂ | ang (a⁻¹ * z) = θ}) := by
      have hsub : {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
          ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ}
            ∪ ({z : ℂ | ang (a⁻¹ * z) = 0} ∪ {z : ℂ | ang (a⁻¹ * z) = θ}) := by
        intro z hz
        by_cases hm : z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ}
        · exact Or.inl hm
        · exact Or.inr (hsubDA ⟨hz, hm⟩)
      exact (measure_mono hsub).trans
        (measure_union_le (F := Measure ℂ) (μ := volume) _ _)
    rw [hrayunion] at hstep
    simpa using hstep
  have hD : volume {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
      = volume {z : ℂ | ‖z‖ < R ∧ 0 < ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) < θ} :=
    le_antisymm hDle (measure_mono hAD)
  have hCDle : volume {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
      ≤ volume {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ} := by
    have hstep : volume {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
        ≤ volume {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
          + volume (Metric.sphere (0 : ℂ) R) := by
      have hsub : {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
          ⊆ {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
            ∪ Metric.sphere (0 : ℂ) R := by
        intro z hz
        by_cases hm : z ∈ {z : ℂ | ‖z‖ < R ∧ 0 ≤ ang (a⁻¹ * z) ∧ ang (a⁻¹ * z) ≤ θ}
        · exact Or.inl hm
        · refine Or.inr ?_
          rw [Metric.mem_sphere, dist_zero_right]
          have hnotlt : ¬ (‖z‖ < R) := fun hlt => hm ⟨hlt, hz.2.1, hz.2.2⟩
          exact le_antisymm hz.1 (not_lt.mp hnotlt)
      exact (measure_mono hsub).trans
        (measure_union_le (F := Measure ℂ) (μ := volume) _ _)
    have hsphere : volume (Metric.sphere (0 : ℂ) R) = 0 :=
      Measure.addHaar_sphere volume 0 R
    rw [hsphere] at hstep
    simpa using hstep
  rw [← hA]
  exact le_antisymm (hCDle.trans hDle) (hD ▸ measure_mono hDC)


/-! ## translation kit (copies of WedgeVolume privates) -/

private theorem p21w_collinear3_zero_sub {x a b : V3} :
    Collinear3 x a b ↔ Collinear3 0 (a - x) (b - x) := by
  by_cases h : a = x
  · rw [h]
    simp only [sub_self]
    constructor <;> intro _ <;> exact collinear3_of_eq rfl
  · have h' : a - x ≠ 0 := sub_ne_zero.mpr h
    rw [collinear3_iff_smul h, collinear3_iff_smul h']
    simp only [sub_zero]

private theorem p21w_azimSpec_zero_sub {x a b c : V3} {θ : ℝ} :
    AzimSpec x a b c θ ↔ AzimSpec 0 (a - x) (b - x) (c - x) θ := by
  unfold AzimSpec
  simp only [sub_zero, sub_ne_zero]
  have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
  rw [hd]

private theorem p21w_azim_sub_self (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  unfold azim
  rw [p21w_collinear3_zero_sub (x := x) (a := a) (b := b),
    p21w_collinear3_zero_sub (x := x) (a := a) (b := c)]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => propext p21w_azimSpec_zero_sub
  rw [hpred]

private theorem p21w_on3_norm_sq (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (x : V3) :
    ‖x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 + (x ⬝ᵥ e3) ^ 2 := by
  have h12 : e1 ⬝ᵥ e2 = 0 := he.2.2.2.1
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.1
  have h13 : e1 ⬝ᵥ e3 = 0 := he.2.2.2.2.1
  have h31 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.1
  have h23 : e2 ⬝ᵥ e3 = 0 := he.2.2.2.2.2.1
  have h32 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.2.1
  rw [norm_sq_eq_dot, on3_expand he x]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [he.1, he.2.1, he.2.2.1, h12, h21, h13, h31, h23, h32]
  ring

private theorem p21w_zOf_norm_sq (e1 e2 : V3) (x : V3) :
    ‖zOf e1 e2 x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [zOf, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    add_zero, zero_add, mul_one, sub_self]
  ring

private theorem p21w_axis_zOf (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (b : ℝ) :
    zOf e1 e2 (b • (e3 : V3)) = 0 := by
  have e31 : (e3 : V3) ⬝ᵥ e1 = 0 := by
    rw [dotProduct_comm]
    exact he.2.2.2.2.1
  have e32 : (e3 : V3) ⬝ᵥ e2 = 0 := by
    rw [dotProduct_comm]
    exact he.2.2.2.2.2.1
  unfold zOf
  rw [WithLp.ofLp_smul, smul_dotProduct, smul_dotProduct, e31, e32]
  simp

/-! ## the frustum-slab-wedge model in frame coordinates -/

private def p21w_frustProj (a h θ : ℝ) (u : ℂ) : Set (ℝ × ℂ) :=
  {p : ℝ × ℂ | a * Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) ≤ p.1 ∧ p.1 ≤ h ∧
    0 ≤ ang (u⁻¹ * p.2) ∧ ang (u⁻¹ * p.2) ≤ θ}

private theorem p21w_frustProj_measurable (a h θ : ℝ) (u : ℂ) :
    MeasurableSet (p21w_frustProj a h θ u) := by
  have hnorm : Measurable fun p : ℝ × ℂ => ‖p.2‖ :=
    (measurable_snd : Measurable fun p : ℝ × ℂ => p.2).norm
  have hfc : Continuous fun p : ℝ × ℂ => a * Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) := by
    fun_prop
  have hf : Measurable fun p : ℝ × ℂ => a * Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) := hfc.measurable
  have hm : Measurable fun p : ℝ × ℂ => ang (u⁻¹ * p.2) :=
    measurable_ang.comp (measurable_const.mul measurable_snd)
  unfold p21w_frustProj
  exact (measurableSet_le hf measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const hm).inter
        (measurableSet_le hm measurable_const)))

private theorem p21w_cone_slice_sq {a t ρ : ℝ} (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    a * Real.sqrt (t ^ 2 + ρ ^ 2) ≤ t ↔ ρ ^ 2 ≤ (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hsa : 0 ≤ (1 - a ^ 2) / a ^ 2 := by
    refine div_nonneg ?_ (by positivity)
    nlinarith [sq_nonneg a, ha.le, ha1]
  have hconv : ∀ q : ℝ, a ^ 2 * ((1 - a ^ 2) / a ^ 2 * t ^ 2) = (1 - a ^ 2) * t ^ 2 := by
    intro q
    field_simp
  constructor
  · intro hle
    have hnn : 0 ≤ a * Real.sqrt (t ^ 2 + ρ ^ 2) :=
      mul_nonneg ha.le (Real.sqrt_nonneg _)
    have hsq : (a * Real.sqrt (t ^ 2 + ρ ^ 2)) ^ 2 ≤ t ^ 2 :=
      (sq_le_sq₀ hnn ht.le).mpr hle
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    have hkey : ρ ^ 2 * a ^ 2 ≤ (1 - a ^ 2) * t ^ 2 := by
      have h2 : a ^ 2 * t ^ 2 + a ^ 2 * ρ ^ 2 ≤ t ^ 2 := by
        have : a ^ 2 * (t ^ 2 + ρ ^ 2) = a ^ 2 * t ^ 2 + a ^ 2 * ρ ^ 2 := by ring
        rwa [this] at hsq
      linarith
    have h4 : ρ ^ 2 * a ^ 2 ≤ ((1 - a ^ 2) * t ^ 2 / a ^ 2) * a ^ 2 := by
      have h5 : ((1 - a ^ 2) * t ^ 2 / a ^ 2) * a ^ 2 = (1 - a ^ 2) * t ^ 2 := by
        field_simp
      rw [h5]
      exact hkey
    have h6 := (mul_le_mul_iff_of_pos_right ha2).mp h4
    have h7 : (1 - a ^ 2) * t ^ 2 / a ^ 2 = (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
      field_simp
    rw [h7] at h6
    exact h6
  · intro hle
    have m1 : a ^ 2 * ρ ^ 2 ≤ (1 - a ^ 2) * t ^ 2 := by
      have h0 : a ^ 2 * ρ ^ 2 ≤ a ^ 2 * ((1 - a ^ 2) / a ^ 2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left hle ha2.le
      have hc := hconv ρ
      linarith
    have h1 : a ^ 2 * (t ^ 2 + ρ ^ 2) ≤ t ^ 2 := by
      have h2 : a ^ 2 * (t ^ 2 + ρ ^ 2) = a ^ 2 * t ^ 2 + a ^ 2 * ρ ^ 2 := by ring
      have h3 : a ^ 2 * t ^ 2 + (1 - a ^ 2) * t ^ 2 = t ^ 2 := by ring
      rw [h2]
      linarith
    have hsq : (a * Real.sqrt (t ^ 2 + ρ ^ 2)) ^ 2 ≤ t ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      exact h1
    exact (sq_le_sq₀ (mul_nonneg ha.le (Real.sqrt_nonneg _)) ht.le).mp hsq


private theorem p21w_slice_vol (a h θ t : ℝ) (u : ℂ) (hu : u ≠ 0) (ha : 0 < a) (ha1 : a < 1)
    (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) :
    volume (Prod.mk t ⁻¹' p21w_frustProj a h θ u)
      = if 0 < t ∧ t ≤ h then ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * t ^ 2 * θ / 2) else 0 := by
  classical
  have hpre : Prod.mk t ⁻¹' p21w_frustProj a h θ u
      = {ζ : ℂ | a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) ≤ t ∧ t ≤ h ∧
          0 ≤ ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) ≤ θ} := by
    ext ζ
    simp only [Set.mem_preimage, p21w_frustProj, Set.mem_setOf_eq]
  by_cases ht0 : 0 < t
  · by_cases hth : t ≤ h
    · rw [if_pos ⟨ht0, hth⟩]
      have hsa : 0 ≤ (1 - a ^ 2) / a ^ 2 := by
        refine div_nonneg ?_ (by positivity)
        nlinarith [sq_nonneg a, ha.le, ha1]
      have hsq : (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2
          = (1 - a ^ 2) / a ^ 2 * t ^ 2 := Real.sq_sqrt (by positivity)
      have hkey : Prod.mk t ⁻¹' p21w_frustProj a h θ u
          = {ζ : ℂ | ‖ζ‖ ≤ Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2) ∧
              0 ≤ ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) ≤ θ} := by
        ext ζ
        simp only [Set.mem_preimage, p21w_frustProj, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, -, h3, h4⟩
          refine ⟨?_, h3, h4⟩
          have h2 : ‖ζ‖ ^ 2 ≤ (1 - a ^ 2) / a ^ 2 * t ^ 2 :=
            (p21w_cone_slice_sq ha ha1 ht0).mp h1
          have h5 : ‖ζ‖ ^ 2 ≤ (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 :=
            h2.trans hsq.symm.le
          exact (sq_le_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mp h5
        · rintro ⟨h1, h3, h4⟩
          refine ⟨(p21w_cone_slice_sq ha ha1 ht0).mpr ?_, hth, h3, h4⟩
          rw [← hsq]
          exact (sq_le_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mpr h1
      rw [hkey]
      have hsec := p21w_closedSector u hu (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) θ
        (Real.sqrt_nonneg _) hθ0 hθ2π
      rwa [hsq] at hsec
    · rw [if_neg (fun hc => hth hc.2)]
      have hempty : Prod.mk t ⁻¹' p21w_frustProj a h θ u = ∅ := by
        ext ζ
        simp only [Set.mem_preimage, p21w_frustProj, Set.mem_setOf_eq,
          Set.mem_empty_iff_false]
        exact ⟨fun hmem => hth hmem.2.1, fun h => absurd h (by simp)⟩
      rw [hempty, measure_empty]
  · rw [if_neg (fun hc => absurd hc.1 ht0)]
    have hsub : Prod.mk t ⁻¹' p21w_frustProj a h θ u ⊆ ({(0 : ℂ)} : Set ℂ) := by
      intro ζ hζ
      simp only [Set.mem_preimage, p21w_frustProj, Set.mem_setOf_eq] at hζ
      have h1 := hζ.1
      have h2 : a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) ≤ 0 := by linarith
      have hz : Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) = 0 := by
        have hnn : 0 ≤ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) :=
          mul_nonneg ha.le (Real.sqrt_nonneg _)
        have h0 : a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) = 0 := le_antisymm h2 hnn
        have h3 : Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) = 0 := by
          apply mul_left_cancel₀ ha.ne'
          rw [h0]
          simp
        exact h3
      have h3 : t ^ 2 + ‖ζ‖ ^ 2 = 0 := by
        have hsq3 : (Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2)) ^ 2 = 0 := by rw [hz]; norm_num
        calc t ^ 2 + ‖ζ‖ ^ 2
            = (Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ = 0 := hsq3
      have h5 : ‖ζ‖ = 0 := by
        have h4 : ‖ζ‖ ^ 2 = 0 := by
          have ht2 : 0 ≤ t ^ 2 := by positivity
          nlinarith
        exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h4
      exact norm_eq_zero.mp h5
    have hnull : volume (({(0 : ℂ)} : Set ℂ)) = 0 := by
      have hb : ({(0 : ℂ)} : Set ℂ) = ((⊥ : Submodule ℝ ℂ) : Set ℂ) := by
        ext z
        simp [Submodule.mem_bot]
      rw [hb]
      exact Measure.addHaar_submodule volume _ (by
        intro htop
        have h1 : (1 : ℂ) ∈ (⊥ : Submodule ℝ ℂ) := htop ▸ Submodule.mem_top
        have h2 : (1 : ℂ) = 0 := by simpa using h1
        norm_num at h2)
    have hle : volume (Prod.mk t ⁻¹' p21w_frustProj a h θ u)
        ≤ volume (({(0 : ℂ)} : Set ℂ)) := measure_mono hsub
    rw [hnull] at hle
    exact le_antisymm hle (by simp)


private theorem p21w_lintegral_frust (a h θ : ℝ) (u : ℂ) (hu : u ≠ 0) (ha : 0 < a)
    (ha1 : a < 1) (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) (hh : 0 ≤ h) :
    ∫⁻ t : ℝ, volume (Prod.mk t ⁻¹' p21w_frustProj a h θ u)
      = ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * h ^ 3 * θ / 6) := by
  have hfun : ∀ t : ℝ, volume (Prod.mk t ⁻¹' p21w_frustProj a h θ u)
      = if 0 < t ∧ t ≤ h then ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * t ^ 2 * θ / 2) else 0 :=
    fun t => p21w_slice_vol a h θ t u hu ha ha1 hθ0 hθ2π
  simp_rw [hfun]
  have hC0 : 0 ≤ (1 - a ^ 2) / a ^ 2 * θ / 2 := by
    have h1 : 0 ≤ (1 - a ^ 2) / a ^ 2 := by
      refine div_nonneg ?_ (by positivity)
      nlinarith [sq_nonneg a, ha.le, ha1]
    exact div_nonneg (mul_nonneg h1 hθ0) (by norm_num)
  have hmul : ∀ t : ℝ, ((1 - a ^ 2) / a ^ 2 * t ^ 2 * θ / 2 : ℝ)
      = (1 - a ^ 2) / a ^ 2 * θ / 2 * t ^ 2 := fun t => by ring
  have hcompl : ∫⁻ t : ℝ in (Set.Ioc 0 h)ᶜ,
      (if 0 < t ∧ t ≤ h then ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * t ^ 2 * θ / 2) else 0) = 0 := by
    refine setLIntegral_eq_zero (measurableSet_Ioc (a := 0) (b := h)).compl ?_
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_and] at ht
    rcases ht with (ht0 | hth)
    · exact if_neg (fun hc => absurd hc.1 (not_lt.mpr ht0))
    · exact if_neg (fun hc => hth hc.2)
  have hsplit := lintegral_add_compl
    (f := fun t : ℝ => if 0 < t ∧ t ≤ h then ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * t ^ 2 * θ / 2) else 0)
    (μ := volume) (A := Set.Ioc 0 h) measurableSet_Ioc
  rw [hcompl] at hsplit
  rw [add_zero] at hsplit
  rw [← hsplit]
  have hcongr : ∫⁻ t : ℝ in Set.Ioc 0 h,
      (if 0 < t ∧ t ≤ h then ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * t ^ 2 * θ / 2) else 0)
      = ∫⁻ t : ℝ in Set.Ioc 0 h, ENNReal.ofReal ((1 - a ^ 2) / a ^ 2 * θ / 2 * t ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht
    simp only []
    have ht0 : 0 < t := ht.1
    have hth : t ≤ h := ht.2
    rw [if_pos ⟨ht0, hth⟩, hmul t]
  rw [hcongr]
  have hcont : Continuous fun t : ℝ => (1 - a ^ 2) / a ^ 2 * θ / 2 * t ^ 2 := by
    fun_prop
  have hint : IntegrableOn (fun t : ℝ => (1 - a ^ 2) / a ^ 2 * θ / 2 * t ^ 2) (Set.Ioc 0 h) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp
      (hcont.intervalIntegrable 0 h)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 h)]
      (fun t : ℝ => (1 - a ^ 2) / a ^ 2 * θ / 2 * t ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t _
    exact mul_nonneg hC0 (sq_nonneg t)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hh, intervalIntegral.integral_const_mul,
    integral_pow]
  congr 1
  field_simp
  ring


private theorem p21w_norm_split (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (x : V3) :
    ‖x‖ ^ 2 = (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 := by
  rw [p21w_on3_norm_sq e1 e2 e3 he x, p21w_zOf_norm_sq e1 e2 x]
  ring

set_option maxHeartbeats 20000000 in
/-- closed wedge membership = closed angular band in the frame coordinates. -/
private theorem p21w_wedge_band (u v w1 w2 y : V3) (e1 e2 e3 : V3)
    (he : Orthonormal3 e1 e2 e3) (hax : (v - u : V3) = dist v u • e3)
    (hw : v ≠ u) (hc1 : ¬ Collinear3 u v w1) (hθ0 : 0 ≤ azim u v w1 w2) :
    (y ∈ wedgeGe u v w1 w2 ↔
      0 ≤ ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (y - u)) ∧
        ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (y - u)) ≤ azim u v w1 w2) := by
  classical
  have hne : (v - u : V3) ≠ 0 := sub_ne_zero.mpr hw
  have hDpos : 0 < dist v u := dist_pos.mpr hw
  have hax' : (v - u : V3) = dist (v - u) 0 • e3 := by
    have hd : dist v u = dist (v - u) 0 := by
      rw [dist_eq_norm, dist_zero_right]
    rw [← hd]
    exact hax
  have hnc1 : ¬ Collinear3 0 (v - u) (w1 - u) := fun h =>
    hc1 (p21w_collinear3_zero_sub.mpr h)
  have hzero : Collinear3 0 (v - u) (y - u) → zOf e1 e2 (y - u) = 0 := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hne).mp hcol
    simp only [sub_zero] at hc
    rw [hc, hax, smul_smul]
    exact p21w_axis_zOf e1 e2 e3 he (c * dist v u)
  have hang0 : Collinear3 0 (v - u) (y - u) →
      ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (y - u)) = 0 := by
    intro hcol
    rw [hzero hcol, mul_zero]
    simp [ang, angArg]
  have hazim0 : Collinear3 0 (v - u) (y - u) →
      azim 0 (v - u) (w1 - u) (y - u) = 0 := by
    intro hcol
    rw [azim, if_pos (Or.inr hcol)]
  have hEq : ∀ z : V3, ¬ Collinear3 0 (v - u) (z - u) →
      azim 0 (v - u) (w1 - u) (z - u)
        = ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (z - u)) :=
    fun z hz => azim_eq_ang_of_frame e1 e2 e3 he hax' hne hnc1 hz
  have hkey : azim u v w1 y = ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (y - u)) := by
    rw [p21w_azim_sub_self]
    by_cases hcol : Collinear3 0 (v - u) (y - u)
    · rw [hazim0 hcol, hang0 hcol]
    · exact hEq y hcol
  -- expose the azim conjunction via the equation lemma; raw `rintro` on the
  -- `wedgeGe` membership would whnf-unfold `azim`/`Collinear3` and grind.
  simp only [wedgeGe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← hkey]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    by_cases hcol : Collinear3 0 (v - u) (y - u)
    · rw [hkey, hang0 hcol]
      rw [hang0 hcol] at h1 h2
      exact ⟨h1, h2⟩
    · rw [hkey]
      exact ⟨h1, h2⟩


private theorem p21w_dot_smul (x : V3) (c : ℝ) (w : V3) :
    (x ⬝ᵥ (c • w) : ℝ) = c * (x ⬝ᵥ w) := by
  rw [dotProduct_smul]
  simp

set_option maxHeartbeats 20000000 in
private theorem p21w_volume_rcone_slab_wedgeGe (u v w1 w2 : V3) (h a : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (huv : u ≠ v) (hc1 : ¬ Collinear3 u v w1)
    (hc2 : ¬ Collinear3 u v w2) (hθ0 : 0 < azim u v w1 w2)
    (hθπ : azim u v w1 w2 < Real.pi) (hh : 0 ≤ h) :
    volume.real (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖}
        ∩ wedgeGe u v w1 w2)
      = azim u v w1 w2 * (1 - a ^ 2) / a ^ 2 * h ^ 3 / 6 := by
  classical
  have hvu : v ≠ u := Ne.symm huv
  obtain ⟨e1, e2, e3, he, hax⟩ := exists_on3_eq_smul (v - u) (sub_ne_zero.mpr hvu)
  have hDpos : 0 < dist v u := dist_pos.mpr hvu
  have hne : (v - u : V3) ≠ 0 := sub_ne_zero.mpr hvu
  have hax' : (v - u : V3) = dist (v - u) 0 • e3 := by
    have hd : dist v u = dist (v - u) 0 := by
      rw [dist_eq_norm, dist_zero_right]
    rw [← hd]
    exact hax
  have hnc1 : ¬ Collinear3 0 (v - u) (w1 - u) := fun hc =>
    hc1 (p21w_collinear3_zero_sub.mpr hc)
  have hθnonneg : 0 ≤ azim u v w1 w2 := azim_nonneg u v w1 w2
  have hζ₁0 : zOf e1 e2 (w1 - u) ≠ 0 :=
    (zOf_ne_zero_iff he hax hvu w1).mpr hc1
  have hlam : ∀ p : V3, p ⬝ᵥ (v - u) = dist v u * (p ⬝ᵥ e3) := by
    intro p
    have hvu2 : v.ofLp - u.ofLp = dist v u • (e3.ofLp : Fin 3 → ℝ) := by
      rw [← WithLp.ofLp_smul, ← WithLp.ofLp_sub]
      exact congrArg WithLp.ofLp (by rw [dist_eq_norm]; exact hax)
    rw [hvu2, dotProduct_smul, smul_eq_mul]
  have hlam2 : ∀ p : V3, p.ofLp ⬝ᵥ (v.ofLp - u.ofLp) = dist v u * (p.ofLp ⬝ᵥ e3.ofLp) := by
    intro p
    have hvu2 : v.ofLp - u.ofLp = dist v u • (e3.ofLp : Fin 3 → ℝ) := by
      rw [← WithLp.ofLp_smul, ← WithLp.ofLp_sub]
      exact congrArg WithLp.ofLp (by rw [dist_eq_norm]; exact hax)
    rw [hvu2, dotProduct_smul, smul_eq_mul]
  set S : Set V3 := rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖}
      ∩ wedgeGe u v w1 w2 with hSdef
  have htrans : volume.real ((fun y : V3 => y - u) '' S) = volume.real S := by
    have himg : (fun y : V3 => y - u) '' S = (fun y : V3 => -u + y) '' S := by
      ext z
      simp only [Set.mem_image]
      refine ⟨fun ⟨y, hy, hx⟩ => ⟨y, hy, by abel_nf at hx ⊢; exact hx⟩,
        fun ⟨y, hy, hx⟩ => ⟨y, hy, by abel_nf at hx ⊢; exact hx⟩⟩
    rw [himg, volume_real_add_left]
  -- the model-set equality
  have hset : (fun y : V3 => y - u) '' S
      = (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹'
          p21w_frustProj a h (azim u v w1 w2) (zOf e1 e2 (w1 - u)) := by
    ext x
    rw [Set.mem_image, Set.mem_preimage, p21w_frustProj, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨⟨hconeM, hslabM⟩, hwedge⟩, hx⟩
      have hyx : y = u + x := by rw [← hx]; abel
      subst hyx
      have hcone := Set.mem_setOf_eq.mp hconeM
      rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left, hlam x] at hcone
      have h1 : a * ‖x‖ ≤ x ⬝ᵥ e3 := by
        nlinarith [hcone, hDpos]
      -- hcone (whnf): (e3.ofLp ⬝ᵥ x.ofLp) * dist v u ≤ (‖x‖ * a) * dist v u
      have hslab := Set.mem_setOf_eq.mp hslabM
      rw [WithLp.ofLp_sub, WithLp.ofLp_add, add_sub_cancel_left, hlam2 x,
        mul_comm (dist v u) (x.ofLp ⬝ᵥ e3.ofLp), ← dist_eq_norm v u] at hslab
      -- hslab : dist v u * (x.ofLp ⬝ᵥ e3.ofLp) ≤ h * dist v u
      have h2 : x.ofLp ⬝ᵥ e3.ofLp ≤ h := le_of_mul_le_mul_right hslab hDpos
      have hwb :=
        (p21w_wedge_band u v w1 w2 (u + x) e1 e2 e3 he hax hvu hc1
          hθnonneg).mp hwedge
      simp only [add_sub_cancel_left] at hwb
      obtain ⟨hb1, hb2⟩ := hwb
      have hnorm2 : Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) = ‖x‖ := by
        have hns := p21w_norm_split e1 e2 e3 he x
        rw [← hns, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
      refine ⟨?_, h2, hb1, hb2⟩
      rw [hnorm2]
      exact h1
    · intro hx
      obtain ⟨hc1c, h2, hb1, hb2⟩ := hx
      have hnorm2 : Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) = ‖x‖ := by
        have hns := p21w_norm_split e1 e2 e3 he x
        rw [← hns, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
      rw [hnorm2] at hc1c
      have hge : a * ‖x‖ ≤ x ⬝ᵥ e3 := hc1c
      have hxeq : (u + x - u : V3) = x := add_sub_cancel_left u x
      rw [← hxeq] at hb1 hb2
      have hxdot : (x ⬝ᵥ ((v - u : V3)) : ℝ) = dist v u * (x ⬝ᵥ e3) := hlam x
      have hkey : ‖x‖ * dist v u * a ≤ x.ofLp ⬝ᵥ (v.ofLp - u.ofLp) := by
        rw [hlam x]
        calc ‖x‖ * dist v u * a = dist v u * (a * ‖x‖) := by ring
          _ ≤ dist v u * (x.ofLp ⬝ᵥ e3.ofLp) :=
                mul_le_mul_of_nonneg_left hge (le_of_lt hDpos)
      refine ⟨u + x, ⟨⟨Set.mem_setOf_eq.mpr ?_, Set.mem_setOf_eq.mpr ?_⟩,
        p21w_wedge_band u v w1 w2 (u + x) e1 e2 e3 he hax hvu hc1 hθnonneg
          |>.mpr ⟨hb1, hb2⟩⟩, ?_⟩
      · rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left]
        exact hkey
      · rw [add_sub_cancel_left, hlam x, mul_comm (dist v u) (x.ofLp ⬝ᵥ e3.ofLp),
          ← dist_eq_norm v u]
        exact mul_le_mul_of_nonneg_right h2 hDpos.le
      · show (u + x - u : V3) = x
        rw [add_sub_cancel_left]
  -- volume transfer
  have hproj := measurePreserving_proj e1 e2 e3 he
  have h1 : volume ((fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹'
      p21w_frustProj a h (azim u v w1 w2) (zOf e1 e2 (w1 - u)))
      = (volume.prod volume) (p21w_frustProj a h (azim u v w1 w2) (zOf e1 e2 (w1 - u))) :=
    hproj.measure_preimage (p21w_frustProj_measurable a h (azim u v w1 w2)
      (zOf e1 e2 (w1 - u))).nullMeasurableSet
  have hvoleq : volume.real S
      = ENNReal.toReal ((volume.prod volume)
          (p21w_frustProj a h (azim u v w1 w2) (zOf e1 e2 (w1 - u)))) := by
    rw [← htrans, Measure.real_def, hset, h1]
  have hsliceeq : (volume.prod volume)
      (p21w_frustProj a h (azim u v w1 w2) (zOf e1 e2 (w1 - u)))
      = ∫⁻ t : ℝ, volume (Prod.mk t ⁻¹'
          p21w_frustProj a h (azim u v w1 w2) (zOf e1 e2 (w1 - u))) :=
    Measure.prod_apply (p21w_frustProj_measurable a h (azim u v w1 w2)
      (zOf e1 e2 (w1 - u)))
  have hval0 : 0 ≤ (1 - a ^ 2) / a ^ 2 * h ^ 3 * (azim u v w1 w2) / 6 := by
    have hP : 0 ≤ (1 - a ^ 2) / a ^ 2 := by
      refine div_nonneg ?_ (by positivity)
      nlinarith [sq_nonneg a, ha.le, ha1]
    exact div_nonneg (mul_nonneg (mul_nonneg hP (pow_nonneg hh 3))
      hθnonneg) (by norm_num)
  rw [hvoleq, hsliceeq,
    p21w_lintegral_frust a h (azim u v w1 w2) (zOf e1 e2 (w1 - u)) hζ₁0 ha ha1
      hθ0.le (by linarith [hθπ, Real.pi_pos]) hh, ENNReal.toReal_ofReal hval0]
  ring


/-! ## the 2D sector-cone equivalence (W1 core) -/

private theorem p21w_ang_re (z : ℂ) (hz : z ≠ 0) : z.re = ‖z‖ * Real.cos (ang z) := by
  have hexp := ang_mul_exp z
  have hre : (Complex.exp (ang z * I)).re = Real.cos (ang z) := by
    simp [Complex.exp_re]
  have h1 : z.re = (↑‖z‖ * Complex.exp (ang z * I)).re := congrArg Complex.re hexp
  rw [h1, Complex.mul_re]
  simp [hre]

private theorem p21w_ang_im (z : ℂ) (hz : z ≠ 0) : z.im = ‖z‖ * Real.sin (ang z) := by
  have hexp := ang_mul_exp z
  have him : (Complex.exp (ang z * I)).im = Real.sin (ang z) := by
    simp [Complex.exp_im]
  have h1 : z.im = (↑‖z‖ * Complex.exp (ang z * I)).im := congrArg Complex.im hexp
  rw [h1, Complex.mul_im]
  simp [him]

private theorem p21w_ang_lt_pi_of_im_pos {g : ℂ} (hg : g ≠ 0) (hIM : 0 < g.im) :
    0 < ang g ∧ ang g < Real.pi := by
  have hsin : 0 < Real.sin (ang g) := by
    have h2 := p21w_ang_im g hg
    nlinarith [norm_pos_iff.mpr hg]
  have h0 : 0 ≤ ang g := ang_nonneg g
  have h2pi : ang g < 2 * Real.pi := ang_lt_two_pi g
  refine ⟨lt_of_le_of_ne h0 fun hzz => ?_, ?_⟩
  · rw [← hzz] at hsin
    simp at hsin
  · by_contra hgt
    push_neg at hgt
    have hne : ang g ≠ Real.pi := by
      intro he
      rw [he] at hsin
      simp at hsin
    have hx : ang g - 2 * Real.pi < 0 := by linarith
    have hx2 : -Real.pi < ang g - 2 * Real.pi := by
      rcases eq_or_lt_of_le hgt with heq | hlt
      · exact absurd heq.symm hne
      · linarith
    have hper : Real.sin (ang g) = Real.sin (ang g - 2 * Real.pi) := by
      have hp := Real.sin_periodic (ang g - 2 * Real.pi)
      rwa [show ang g - 2 * Real.pi + 2 * Real.pi = ang g from by ring] at hp
    rw [hper] at hsin
    have hneg := Real.sin_neg_of_neg_of_neg_pi_lt hx hx2
    linarith

private theorem p21w_cross_lin {f1 f2 : ℝ} {g w : ℂ} (hg : g = f1 + f2 * w) :
    g.re * w.im - g.im * w.re = f1 * w.im := by
  have h1 := congrArg Complex.re hg
  have h2 := congrArg Complex.im hg
  simp at h1 h2
  simp [h1, h2]
  ring

private theorem p21w_cross_sin {g w : ℂ} (hg : g ≠ 0) (hw : w ≠ 0) :
    g.re * w.im - g.im * w.re = ‖g‖ * ‖w‖ * Real.sin (ang w - ang g) := by
  rw [p21w_ang_re g hg, p21w_ang_im g hg, p21w_ang_re w hw, p21w_ang_im w hw]
  rw [Real.sin_sub]
  field_simp

/-- cone ⊆ band: nonnegative combinations stay in the closed angular band `[0, θ]`. -/
private theorem p21w_cone_to_band {ζ1 ζ2 : ℂ} (h1 : ζ1 ≠ 0) (h2z : ζ2 ≠ 0)
    (hθ0 : 0 < ang (ζ1⁻¹ * ζ2)) (hθπ : ang (ζ1⁻¹ * ζ2) < Real.pi)
    (f1 f2 : ℝ) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) :
    0 ≤ ang (ζ1⁻¹ * (ζ1 * f1 + ζ2 * f2)) ∧
      ang (ζ1⁻¹ * (ζ1 * f1 + ζ2 * f2)) ≤ ang (ζ1⁻¹ * ζ2) := by
  classical
  have hw0 : (ζ1⁻¹ * ζ2 : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero h1) h2z
  have hwim : 0 < (ζ1⁻¹ * ζ2 : ℂ).im := by
    have h2 := p21w_ang_im _ hw0
    have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    have hnormpos : (0:ℝ) < ‖(ζ1⁻¹ * ζ2 : ℂ)‖ := norm_pos_iff.mpr hw0
    nlinarith
  by_cases hg0 : f1 + f2 * (ζ1⁻¹ * ζ2) = 0
  · have hz : (ζ1⁻¹ * (ζ1 * f1 + ζ2 * f2) : ℂ) = 0 := by
      have heq : (ζ1⁻¹ * (ζ1 * f1 + ζ2 * f2) : ℂ) = f1 + f2 * (ζ1⁻¹ * ζ2) := by
        field_simp
      rw [heq, hg0]
    rw [hz]
    refine ⟨ang_nonneg 0, ?_⟩
    simpa [ang, angArg] using hθ0.le
  · set g : ℂ := ζ1⁻¹ * (ζ1 * f1 + ζ2 * f2) with hgdef
    have hgeq : g = f1 + f2 * (ζ1⁻¹ * ζ2) := by
      rw [hgdef]
      field_simp
    have hgne : g ≠ 0 := by
      rw [hgeq]
      exact hg0
    have hgim : g.im = f2 * (ζ1⁻¹ * ζ2).im := by
      rw [hgeq]
      simp [Complex.mul_im]
    by_cases hf2z : f2 = 0
    · have hgre : g.re = f1 := by
        have h1 := congrArg Complex.re hgeq
        simp [hf2z] at h1
        linarith
      have hgz : g.im = 0 := by rw [hgim, hf2z, zero_mul]
      have hzero : g.arg = 0 :=
        Complex.arg_eq_zero_iff.mpr ⟨by rw [hgre]; exact hf1, hgz⟩
      have harg : ang g = 0 := by
        by_cases hh : g.arg < 0
        · exfalso
          have hcon := ang_eq_arg_add_of_neg hh
          rw [hzero] at hcon
          simp at hcon
          linarith
        · exact (ang_eq_arg_of_nonneg (not_lt.mp hh)).trans hzero
      rw [harg]
      exact ⟨le_refl 0, le_of_lt hθ0⟩
    · have hf2p : 0 < f2 := lt_of_le_of_ne hf2 (Ne.symm hf2z)
      have hpsi := p21w_ang_lt_pi_of_im_pos hgne (by rw [hgim]; exact mul_pos hf2p hwim)
      have hcw := p21w_cross_lin hgeq
      have hcs := p21w_cross_sin hgne hw0
      have hwnormpos : (0:ℝ) < ‖(ζ1⁻¹ * ζ2 : ℂ)‖ := norm_pos_iff.mpr hw0
      have hgnormpos : (0:ℝ) < ‖g‖ := norm_pos_iff.mpr hgne
      have hsin0 : 0 ≤ Real.sin (ang (ζ1⁻¹ * ζ2) - ang g) := by
        have h1 : 0 ≤ f1 * (ζ1⁻¹ * ζ2).im := mul_nonneg hf1 hwim.le
        rw [← hcw, hcs] at h1
        nlinarith [mul_pos hgnormpos hwnormpos]
      by_cases hpos : 0 ≤ (ang (ζ1⁻¹ * ζ2)) - ang g
      · exact ⟨ang_nonneg g, le_of_sub_nonneg hpos⟩
      · exfalso
        have hpsub : 0 < ang g - (ang (ζ1⁻¹ * ζ2)) := by linarith
        have hlt : ang g - (ang (ζ1⁻¹ * ζ2)) < Real.pi := by linarith [hpsi.2]
        have hs1 := Real.sin_pos_of_pos_of_lt_pi hpsub hlt
        have hsneg : Real.sin ((ang (ζ1⁻¹ * ζ2)) - ang g)
            = -(Real.sin (ang g - (ang (ζ1⁻¹ * ζ2)))) := by
          rw [show (ang (ζ1⁻¹ * ζ2)) - ang g = -(ang g - (ang (ζ1⁻¹ * ζ2))) from by ring,
            Real.sin_neg]
        rw [hsneg] at hsin0
        linarith

/-- band ⊆ cone: points in the closed angular band `[0, θ]` are nonnegative
combinations. -/
private theorem p21w_band_to_cone {ζ1 ζ2 : ℂ} (h1 : ζ1 ≠ 0) (h2z : ζ2 ≠ 0)
    (hθ0 : 0 < ang (ζ1⁻¹ * ζ2)) (hθπ : ang (ζ1⁻¹ * ζ2) < Real.pi)
    {g : ℂ} (hg1 : 0 ≤ ang g) (hg2 : ang g ≤ ang (ζ1⁻¹ * ζ2)) :
    ∃ f1 f2 : ℝ, 0 ≤ f1 ∧ 0 ≤ f2 ∧ ζ1 * f1 + ζ2 * f2 = ζ1 * g := by
  classical
  have hw0 : (ζ1⁻¹ * ζ2 : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero h1) h2z
  have hwim : 0 < (ζ1⁻¹ * ζ2 : ℂ).im := by
    have h2 := p21w_ang_im _ hw0
    have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    have hnormpos : (0:ℝ) < ‖(ζ1⁻¹ * ζ2 : ℂ)‖ := norm_pos_iff.mpr hw0
    nlinarith
  by_cases hg0 : g = 0
  · refine ⟨0, 0, le_refl 0, le_refl 0, ?_⟩
    simp [hg0]
  · have harg : ang g = g.arg := by
      by_cases hh : g.arg < 0
      · exfalso
        have hcon := ang_eq_arg_add_of_neg hh
        linarith [Complex.neg_pi_lt_arg g, hθπ, hg2, hcon]
      · exact ang_eq_arg_of_nonneg (not_lt.mp hh)
    have hgre := p21w_ang_re g hg0
    have hgim := p21w_ang_im g hg0
    have hwre := p21w_ang_re _ hw0
    have hwim2 := p21w_ang_im _ hw0
    have hsinψ : 0 ≤ Real.sin (ang g) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hg1 (hg2.trans (le_of_lt hθπ))
    have hf1 : 0 ≤ (g.re * (ζ1⁻¹ * ζ2).im - g.im * (ζ1⁻¹ * ζ2).re)
        / (ζ1⁻¹ * ζ2).im := by
      refine div_nonneg ?_ hwim.le
      have hcs := p21w_cross_sin hg0 hw0
      have hsin0 : 0 ≤ Real.sin (ang (ζ1⁻¹ * ζ2) - ang g) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hg2) (by linarith)
      have hwnormpos : (0:ℝ) < ‖(ζ1⁻¹ * ζ2 : ℂ)‖ := norm_pos_iff.mpr hw0
      have hgnormpos : (0:ℝ) < ‖g‖ := norm_pos_iff.mpr hg0
      rw [hcs]
      exact mul_nonneg (mul_nonneg hgnormpos.le hwnormpos.le) hsin0
    have hf2 : 0 ≤ g.im / (ζ1⁻¹ * ζ2).im := by
      refine div_nonneg ?_ hwim.le
      have hnormpos : (0:ℝ) < ‖g‖ := norm_pos_iff.mpr hg0
      rw [hgim]
      exact mul_nonneg hnormpos.le hsinψ
    refine ⟨(g.re * (ζ1⁻¹ * ζ2).im - g.im * (ζ1⁻¹ * ζ2).re) / (ζ1⁻¹ * ζ2).im,
      g.im / (ζ1⁻¹ * ζ2).im, hf1, hf2, ?_⟩
    have hw0' : (ζ1⁻¹ * ζ2 : ℂ).im ≠ 0 := ne_of_gt hwim
    have hsplit : g = (↑((g.re * (ζ1⁻¹ * ζ2).im - g.im * (ζ1⁻¹ * ζ2).re)
          / (ζ1⁻¹ * ζ2).im) : ℂ)
        + (↑(g.im / (ζ1⁻¹ * ζ2).im) : ℂ) * (ζ1⁻¹ * ζ2) := by
      set w : ℂ := ζ1⁻¹ * ζ2 with hwdef
      have hwi : w.im ≠ 0 := hw0'
      rw [Complex.ext_iff]
      constructor
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
        field_simp
        ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
          Complex.ofReal_re, mul_zero, zero_mul, add_zero, sub_zero]
        field_simp
        ring
    conv_rhs => rw [hsplit]
    field_simp


private theorem p21w_zOf_add (e1 e2 x y : V3) :
    zOf e1 e2 (x + y) = zOf e1 e2 x + zOf e1 e2 y := by
  unfold zOf
  simp only [WithLp.ofLp_add, add_dotProduct, Complex.ofReal_add]
  ring

private theorem p21w_zOf_smul (e1 e2 : V3) (c : ℝ) (x : V3) :
    zOf e1 e2 (c • x) = c * zOf e1 e2 x := by
  unfold zOf
  simp only [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, Complex.ofReal_mul]
  ring

private theorem p21w_zOf_sub (e1 e2 x y : V3) :
    zOf e1 e2 (x - y) = zOf e1 e2 x - zOf e1 e2 y := by
  have h := p21w_zOf_add e1 e2 (x - y) y
  simp only [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private theorem p21w_mem_axis_of_zOf {e1 e2 e3 : V3} (he : Orthonormal3 e1 e2 e3)
    {x : V3} (h : zOf e1 e2 x = 0) : x = (x ⬝ᵥ e3) • e3 := by
  have hz : (x ⬝ᵥ e1) = 0 ∧ (x ⬝ᵥ e2) = 0 := by
    have h2 := Complex.ext_iff.mp h
    constructor
    · have h3 := h2.1
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
        mul_zero, zero_mul, sub_zero, add_zero] at h3
      exact h3
    · have h3 := h2.2
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.zero_im,
        mul_one, zero_mul, mul_zero, add_zero, zero_add] at h3
      exact h3
  have he31 : (e3 ⬝ᵥ e1) = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.1
  have he32 : (e3 ⬝ᵥ e2) = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.2.1
  have hd1 : ((x - (x ⬝ᵥ e3) • e3 : V3) ⬝ᵥ e1) = 0 := by
    rw [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct]
    rw [hz.1, he31]
    simp
  have hd2 : ((x - (x ⬝ᵥ e3) • e3 : V3) ⬝ᵥ e2) = 0 := by
    rw [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct]
    rw [hz.2, he32]
    simp
  have hd3 : ((x - (x ⬝ᵥ e3) • e3 : V3) ⬝ᵥ e3) = 0 := by
    rw [WithLp.ofLp_sub, WithLp.ofLp_smul, sub_dotProduct, smul_dotProduct]
    rw [show e3 ⬝ᵥ e3 = (1:ℝ) from he.2.2.1]
    simp
  have hsq : ‖x - (x ⬝ᵥ e3) • e3‖ ^ 2 = 0 := by
    have hns := p21w_on3_norm_sq e1 e2 e3 he (x - (x ⬝ᵥ e3) • e3)
    rw [hns, hd1, hd2, hd3]
    norm_num
  have hzero : ‖x - (x ⬝ᵥ e3) • e3‖ = 0 := sq_eq_zero_iff.mp hsq
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

private theorem p21w_affGe_2_2_char {u v w1 w2 : V3}
    (hd : u ≠ v ∧ u ≠ w1 ∧ u ≠ w2 ∧ v ≠ w1 ∧ v ≠ w2 ∧ w1 ≠ w2) (y : V3) :
    y ∈ affGe ({u, v} : Set V3) ({w1, w2} : Set V3) ↔
      ∃ c d e : ℝ, 0 ≤ c ∧ 0 ≤ d ∧
        y = c • w1 + d • w2 + e • v + (1 - c - d - e) • u := by
  have hfin : ((({u, v} : Set V3) ∪ {w1, w2}) : Set V3).Finite := by simp
  have hF : hfin.toFinset = insert u (insert v (insert w1 {w2})) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hp' : u ∉ (insert v (insert w1 {w2}) : Finset V3) := by
    simp [hd.1, hd.2.1, hd.2.2.1]
  have hv' : v ∉ (insert w1 {w2} : Finset V3) := by
    simp [hd.2.2.2.1, hd.2.2.2.2.1]
  have hw' : w1 ∉ ({w2} : Finset V3) := by simp [hd.2.2.2.2.2]
  constructor
  · rintro ⟨f, _, hy, hpos, hsum⟩
    have hy' : y = f u • u + f v • v + f w1 • w1 + f w2 • w2 := by
      have h2 := hy
      rw [hF, Finset.sum_insert hp', Finset.sum_insert hv', Finset.sum_insert hw',
        Finset.sum_singleton] at h2
      have h3 : f u • u + (f v • v + (f w1 • w1 + f w2 • w2))
          = f u • u + f v • v + f w1 • w1 + f w2 • w2 := by module
      rw [← h3]
      exact h2
    have hsum' : f u + f v + f w1 + f w2 = 1 := by
      have h2 := hsum
      rw [hF, Finset.sum_insert hp', Finset.sum_insert hv', Finset.sum_insert hw',
        Finset.sum_singleton] at h2
      linarith
    refine ⟨f w1, f w2, f v, hpos w1 (by simp), hpos w2 (by simp), ?_⟩
    have hx : y = f w1 • w1 + f w2 • w2 + f v • v + (1 - f w1 - f w2 - f v) • u := by
      rw [hy']
      rw [show (1 - f w1 - f w2 - f v) • u = f u • u from
        by rw [show 1 - f w1 - f w2 - f v = f u from by linarith]]
      abel
    exact hx
  · rintro ⟨c, d, e, hc, hd2, hty⟩
    refine ⟨fun w => if w = u then 1 - c - d - e else if w = v then e else if w = w1 then c
      else d, hfin, ?_, ?_, ?_⟩
    · rw [hF, Finset.sum_insert hp', Finset.sum_insert hv', Finset.sum_insert hw',
        Finset.sum_singleton]
      simp only [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, Ne.symm hd.1,
        Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1,
        Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2, if_true, eq_self_iff_true,
        if_false]
      rw [hty]
      abel
    · intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · simp [Ne.symm hd.2.1, Ne.symm hd.2.2.2.1, hc]
      · simp [Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2, hd2]
    · rw [hF, Finset.sum_insert hp', Finset.sum_insert hv', Finset.sum_insert hw',
        Finset.sum_singleton]
      simp only [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, Ne.symm hd.1,
        Ne.symm hd.2.1, Ne.symm hd.2.2.1, Ne.symm hd.2.2.2.1,
        Ne.symm hd.2.2.2.2.1, Ne.symm hd.2.2.2.2.2, if_true, eq_self_iff_true,
        if_false]
      ring

set_option maxHeartbeats 20000000 in
private theorem p21w_wedgeGe_eq_affGe {u v w1 w2 : V3}
    (hd : u ≠ v ∧ u ≠ w1 ∧ u ≠ w2 ∧ v ≠ w1 ∧ v ≠ w2 ∧ w1 ≠ w2)
    (hθ0 : 0 < azim u v w1 w2) (hθπ : azim u v w1 w2 < Real.pi) :
    wedgeGe u v w1 w2 = affGe ({u, v} : Set V3) ({w1, w2} : Set V3) := by
  classical
  obtain ⟨e1, e2, e3, he, hax⟩ :=
    exists_on3_eq_smul (v - u) (sub_ne_zero.mpr (Ne.symm hd.1))
  have hvu : v ≠ u := Ne.symm hd.1
  have hDpos : 0 < dist v u := dist_pos.mpr (Ne.symm hd.1)
  have hne : (v - u : V3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hd.1)
  have hax' : (v - u : V3) = dist (v - u) 0 • e3 := by
    have hd2 : dist v u = dist (v - u) 0 := by
      rw [dist_eq_norm, dist_zero_right]
    rw [← hd2]
    exact hax
  -- `0 < azim` rules out degeneracy: `azim` collapses to 0 on collinear fans.
  have hnc : ¬(Collinear3 u v w1 ∨ Collinear3 u v w2) := by
    intro hcol
    rw [azim, if_pos hcol] at hθ0
    norm_num at hθ0
  have hc1 : ¬ Collinear3 u v w1 := fun hc => hnc (Or.inl hc)
  have hc2 : ¬ Collinear3 u v w2 := fun hc => hnc (Or.inr hc)
  have hnc1 : ¬ Collinear3 0 (v - u) (w1 - u) := fun hc =>
    hc1 (p21w_collinear3_zero_sub.mpr hc)
  have hnc2 : ¬ Collinear3 0 (v - u) (w2 - u) := fun hc =>
    hc2 (p21w_collinear3_zero_sub.mpr hc)
  have hζ1 : zOf e1 e2 (w1 - u) ≠ 0 :=
    (zOf_ne_zero_iff he hax hvu w1).mpr hc1
  have hζ2 : zOf e1 e2 (w2 - u) ≠ 0 :=
    (zOf_ne_zero_iff he hax hvu w2).mpr hc2
  have hθnonneg : 0 ≤ azim u v w1 w2 := azim_nonneg u v w1 w2
  have hθeq : ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (w2 - u)) = azim u v w1 w2 := by
    have h1 := azim_eq_ang_of_frame e1 e2 e3 he hax' hne hnc1 hnc2
    rw [p21w_azim_sub_self, h1]
  have hband : ∀ y : V3,
      (y ∈ wedgeGe u v w1 w2 ↔
        0 ≤ ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (y - u)) ∧
          ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (y - u)) ≤ azim u v w1 w2) :=
    fun y => p21w_wedge_band u v w1 w2 y e1 e2 e3 he hax hvu hc1 hθnonneg
  ext y
  have hθang : 0 < ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (w2 - u)) := by
    rw [hθeq]
    exact hθ0
  have hθπang : ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (w2 - u)) < Real.pi := by
    rw [hθeq]
    exact hθπ
  constructor
  · rintro hy
    rw [p21w_affGe_2_2_char hd y]
    obtain ⟨hb1, hb2⟩ := (hband y).mp hy
    set g : ℂ := zOf e1 e2 (y - u) with hgdef
    -- the angular band of the relative coordinate `ζ1⁻¹ * g` is a cone in
    -- quotient coordinates; `band_to_cone` turns it into the direct linear
    -- combination `ζ1 * f1 + ζ2 * f2 = g`.
    have hb2' : ang ((zOf e1 e2 (w1 - u))⁻¹ * g)
        ≤ ang ((zOf e1 e2 (w1 - u))⁻¹ * zOf e1 e2 (w2 - u)) := by
      rw [hθeq]
      exact hb2
    obtain ⟨f1, f2, hf1, hf2, hvec⟩ :=
      p21w_band_to_cone hζ1 hζ2 hθang hθπang hb1 hb2'
    rw [mul_inv_cancel_left₀ hζ1] at hvec
    have hxzero : zOf e1 e2 (y - u - f1 • (w1 - u) - f2 • (w2 - u)) = 0 := by
      have h1 : zOf e1 e2 (y - u - f1 • (w1 - u) - f2 • (w2 - u))
          = zOf e1 e2 (y - u) - ↑f1 * zOf e1 e2 (w1 - u)
              - ↑f2 * zOf e1 e2 (w2 - u) := by
        rw [p21w_zOf_sub, p21w_zOf_sub, p21w_zOf_sub, p21w_zOf_smul, p21w_zOf_smul]
      rw [h1, ← hgdef, ← hvec]
      ring
    have haxis := p21w_mem_axis_of_zOf he hxzero
    set s : ℝ := (y - u - f1 • (w1 - u) - f2 • (w2 - u)) ⬝ᵥ e3 / dist v u with hsdef
    have hxeq' : (y - u) - f1 • (w1 - u) - f2 • (w2 - u) = s • (v - u) := by
      rw [haxis, hax, smul_smul]
      congr 1
      rw [hsdef, dist_eq_norm v u]
      have hd0 : ‖(v - u : V3)‖ ≠ 0 := by simpa using hne
      exact (div_mul_cancel₀ _ hd0).symm
    refine ⟨f1, f2, s, hf1, hf2, ?_⟩
    have hrhs : y = f1 • w1 + f2 • w2 + s • v + (1 - f1 - f2 - s) • u := by
      have h2 : f1 • w1 + f2 • w2 + s • v + (1 - f1 - f2 - s) • u
          = u + (f1 • (w1 - u) + f2 • (w2 - u) + s • (v - u)) := by
        simp only [smul_sub, sub_smul, one_smul]
        abel
      have hkey : y - u = f1 • (w1 - u) + f2 • (w2 - u) + s • (v - u) := by
        rw [sub_eq_iff_eq_add] at hxeq'
        rw [sub_eq_iff_eq_add] at hxeq'
        rw [hxeq']
        abel
      have hyu : y = u + (y - u) := by abel
      rw [hyu, hkey]
      exact h2.symm
    rw [hrhs]
  · rintro hy
    obtain ⟨c, d, e, hc, hd2, hty⟩ := (p21w_affGe_2_2_char hd y).mp hy
    have hvec : y - u = c • (w1 - u) + d • (w2 - u) + e • (v - u) := by
      rw [hty]
      module
    have hzof : zOf e1 e2 (y - u)
        = c * zOf e1 e2 (w1 - u) + d * zOf e1 e2 (w2 - u) := by
      rw [hvec, p21w_zOf_add, p21w_zOf_add, p21w_zOf_smul, p21w_zOf_smul,
        p21w_zOf_smul, hax]
      rw [p21w_axis_zOf e1 e2 e3 he]
      simp
    obtain ⟨hb1, hb2⟩ := p21w_cone_to_band hζ1 hζ2 hθang hθπang c d hc hd2
    rw [mul_comm (zOf e1 e2 (w1 - u)) c, mul_comm (zOf e1 e2 (w2 - u)) d] at hb1 hb2
    rw [← hzof] at hb1 hb2
    rw [hθeq] at hb2
    exact (hband y).mpr ⟨hb1, hb2⟩


theorem pA_coll_of_ne {a b : V3} (h : a = b) : Collinear3 a b b :=
  h ▸ collinear3_of_eq rfl

theorem pA_uv_ne (V : Set V3) (ul : List V3) (hX : X = mcell2 V ul)
    (hn : ¬nullSet X) : elV ul 0 ≠ elV ul 1 := fun heq =>
  hn (by rw [hX]; exact p21_mcell2_uv_null V ul heq)

theorem pA_sdiff_inter {X Y Z : Set V3} (h : nullSet (symmDiff X Y)) :
    nullSet (symmDiff (X ∩ Z) (Y ∩ Z)) := by
  have hsub : symmDiff (X ∩ Z) (Y ∩ Z) ⊆ symmDiff X Y := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
    tauto
  exact le_antisymm (le_trans (measure_mono hsub) h.le) zero_le

theorem pA_vol_sdiff {X Y : Set V3} (h : nullSet (symmDiff X Y)) :
    volume.real X = volume.real Y := by
  have hsub : X ⊆ Y ∪ symmDiff X Y := fun z hz => by
    by_cases hzY : z ∈ Y
    · exact Or.inl hzY
    · exact Or.inr (Or.inl ⟨hz, hzY⟩)
  have hsub2 : Y ⊆ X ∪ symmDiff X Y := fun z hz => by
    by_cases hzX : z ∈ X
    · exact Or.inl hzX
    · exact Or.inr (Or.inr ⟨hz, hzX⟩)
  have h1 : volume X ≤ volume Y := by
    calc volume X ≤ volume (Y ∪ symmDiff X Y) := measure_mono hsub
      _ ≤ volume Y + volume (symmDiff X Y) := measure_union_le _ _
      _ = volume Y := by rw [h]; simp
  have h2 : volume Y ≤ volume X := by
    calc volume Y ≤ volume (X ∪ symmDiff X Y) := measure_mono hsub2
      _ ≤ volume X + volume (symmDiff X Y) := measure_union_le _ _
      _ = volume X := by rw [h]; simp
  exact congrArg ENNReal.toReal (le_antisymm h1 h2)

theorem pA_ball_subset_bis_le (u v : V3) (r : ℝ) (hr : 2 * r ≤ dist u v) :
    Metric.ball u r ⊆ bisLe u v := by
  intro x hx
  have hxu : dist x u < r := hx
  have hduv : dist u v ≤ dist x u + dist x v := by
    have ht := dist_triangle u x v
    rwa [dist_comm u x] at ht
  have h1 : dist x u ≤ dist x v := by linarith
  exact h1

theorem pA_ball_subset_bis_lt (u v : V3) (r : ℝ) (hr : 2 * r ≤ dist u v) :
    Metric.ball u r ⊆ {y : V3 | dist y u < dist y v} := by
  intro x hx
  have hxu : dist x u < r := hx
  have hduv : dist u v ≤ dist x u + dist x v := by
    have ht := dist_triangle u x v
    rwa [dist_comm u x] at ht
  simp only [Set.mem_setOf_eq]
  linarith

theorem pA_sphere_null (x : V3) (r : ℝ) : volume (Metric.sphere x r) = 0 :=
  Measure.addHaar_sphere volume x r

theorem pA_convex_affGe {s t : Set V3} (hfin : (s ∪ t).Finite) :
    Convex ℝ (affGe s t) := by
  intro x hx y hy a b ha hb hab
  simp only [affGe, Affsign, Set.mem_setOf_eq] at hx hy
  obtain ⟨f1, _, hx1, hx2, hx3⟩ := hx
  obtain ⟨f2, _, hy1, hy2, hy3⟩ := hy
  refine ⟨fun p => a * f1 p + b * f2 p, hfin, ?_, ?_, ?_⟩
  · have key : ∀ (g : V3 → ℝ) (c : ℝ), ∑ q ∈ hfin.toFinset, (c * g q) • q
        = c • ∑ q ∈ hfin.toFinset, g q • q := by
      intro g c
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [smul_smul]
    have hsum1 : ∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q) • q
        = ∑ q ∈ hfin.toFinset, ((a * f1 q) • q + (b * f2 q) • q) := by
      exact Finset.sum_congr rfl fun q _ => by rw [add_smul]
    rw [hsum1, Finset.sum_add_distrib, key, key, hx1, hy1]
  · intro p hp
    have h1 : 0 ≤ f1 p := hx2 p hp
    have h2 : 0 ≤ f2 p := hy2 p hp
    show 0 ≤ a * f1 p + b * f2 p
    exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · show (∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q)) = 1
    have h3' : ∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q)
        = a * ∑ q ∈ hfin.toFinset, f1 q + b * ∑ q ∈ hfin.toFinset, f2 q := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h3', hx3, hy3]
    simp only [mul_one]
    exact hab

theorem pA_mem_affGe_vertex {s t : Set V3} (hfin : (s ∪ t).Finite) {v : V3}
    (hv : v ∈ s) : v ∈ affGe s t := by
  refine ⟨fun w => if w = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hbb
      simp [hbb]
    · intro h
      exact absurd (hfin.mem_toFinset.mpr (Set.mem_union_left _ hv)) h
  · intro p hp
    by_cases hpv : p = v
    · simp [hpv]
    · simp [hpv]
  · rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hbb
      simp [hbb]
    · intro h
      exact absurd (hfin.mem_toFinset.mpr (Set.mem_union_left _ hv)) h

set_option maxHeartbeats 20000000 in
theorem pA_radial_of_mcell2 (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    radialNorm (hl (truncateSimplex 1 ul)) (elV ul 0)
      (mcell2 V ul ∩ Metric.ball (elV ul 0) (hl (truncateSimplex 1 ul))) := by
  classical
  have huv : elV ul 0 ≠ elV ul 1 := pA_uv_ne V ul hX hn
  have hlt := MCELL2_HL_LT_SQRT2 V ul hs hp hb (by rw [hX] at hn; exact hn)
  have hpos : 0 < hl (truncateSimplex 1 ul) := BARV_IMP_HL_1_POS_LT V ul hs hp hb
  have hsq2 : Real.sqrt 2 ≤ hl ul :=
    p21w_mcell2_hl_ul_ge V ul hs hp hb (by rw [hX] at hn; exact hn)
  have hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul := ⟨hlt, hsq2⟩
  have hcent : hdV ul = elV ul 0 ∧ hdV ul.tail = elV ul 1 := by
    cases ul with
    | nil => exact absurd hb.1 (by simp)
    | cons a t =>
      cases t with
      | nil => exact absurd hb.1 (by simp)
      | cons b t => exact ⟨rfl, rfl⟩
  set h : ℝ := hl (truncateSimplex 1 ul) with hh
  have hapos : 0 < h / Real.sqrt 2 := div_pos hpos (Real.sqrt_pos.mpr (by norm_num))
  have hale : h / Real.sqrt 2 ≤ 1 := by
    refine (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr ?_
    linarith
  have hXm : mcell2 V ul
      = (rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
          ∩ rconeGe (elV ul 1) (elV ul 0) (h / Real.sqrt 2))
        ∩ affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} := by
    rw [mcell2, if_pos hcond, hcent.1, hcent.2]
  have hcone1 : Convex ℝ (rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)) :=
    CONVEX_RCONE_GE _ _ _ hapos.le
  have hwedge : Convex ℝ (affGe {elV ul 0, elV ul 1}
      {mxi V ul, omegaListN V ul 3}) := pA_convex_affGe (by simp)
  have huin : elV ul 0 ∈ mcell2 V ul := by
    rw [hXm]
    refine ⟨⟨?_, ?_⟩, pA_mem_affGe_vertex (by simp) (Set.mem_insert _ _)⟩
    · unfold rconeGe
      simp
    · show ((elV ul 0 - elV ul 1 : V3) ⬝ᵥ (elV ul 0 - elV ul 1 : V3) : ℝ)
        ≥ dist (elV ul 0) (elV ul 1) * dist (elV ul 0) (elV ul 1) * (h / Real.sqrt 2)
      rw [← norm_sq_eq_dot (elV ul 0 - elV ul 1), dist_eq_norm (elV ul 0) (elV ul 1)]
      nlinarith [sq_nonneg (‖(elV ul 0 - elV ul 1 : V3)‖), hale]
  have hncp := NOT_COPLANAR_EXTREME_MCELL2 V ul hp hs hb (by rw [hX] at hn; exact hn)
  have hw1 : ¬ Collinear3 (elV ul 0) (elV ul 1) (mxi V ul) := fun hc =>
    hncp (p21_collinear3_coplanar4 _ _ _ _ hc)
  have hw2 : ¬ Collinear3 (elV ul 0) (elV ul 1) (omegaListN V ul 3) := fun hc =>
    hncp (p21_collinear3_coplanar4_last _ _ _ _ hc)
  have hd4 : elV ul 0 ≠ elV ul 1 ∧ elV ul 0 ≠ mxi V ul ∧ elV ul 0 ≠ omegaListN V ul 3 ∧
      elV ul 1 ≠ mxi V ul ∧ elV ul 1 ≠ omegaListN V ul 3 ∧
      mxi V ul ≠ omegaListN V ul 3 := by
    refine ⟨huv, fun hcc => hw1 ?_, fun hcc => hw2 ?_, fun hcc => hw1 ?_,
      fun hcc => hw2 ?_, fun hcc => hncp ⟨elV ul 0, elV ul 1, mxi V ul, fun z hz => ?_⟩⟩
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨0, ?_⟩
      rw [hcc, sub_self, zero_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨0, ?_⟩
      rw [hcc, sub_self, zero_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨1, ?_⟩
      rw [hcc, one_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨1, ?_⟩
      rw [hcc, one_smul]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · rw [← hcc]
        exact subset_affineSpan ℝ _ (by simp)
  refine ⟨fun z hz => hz.2, ?_⟩
  intro p hp t ht htn
  have hupC : elV ul 0 + p ∈ mcell2 V ul := hp.1
  have hup' : elV ul 0 + p ∈ (rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
      ∩ rconeGe (elV ul 1) (elV ul 0) (h / Real.sqrt 2))
    ∩ affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} := hXm ▸ hupC
  obtain ⟨⟨hup1, hup2⟩, hup3⟩ := hup'
  -- cone at the apex is homogeneous
  have hc1 : elV ul 0 + t • p ∈ rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2) := by
    unfold rconeGe at hup1 ⊢
    simp only [Set.mem_setOf_eq] at hup1 ⊢
    have hsub : elV ul 0 + t • p - elV ul 0 = t • p := by abel
    have hsub2 : elV ul 0 + p - elV ul 0 = p := by abel
    have hdn : dist (elV ul 0 + t • p) (elV ul 0) = t * ‖p‖ := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le]
    have hdp : dist (elV ul 0 + p) (elV ul 0) = ‖p‖ := by
      rw [dist_eq_norm, hsub2]
    rw [hsub2, hdp] at hup1
    rw [hsub, hdn, WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
    have hassoc : (t * ‖p‖) * dist (elV ul 1) (elV ul 0) * (h / Real.sqrt 2)
        = t * (‖p‖ * dist (elV ul 1) (elV ul 0) * (h / Real.sqrt 2)) := by ring
    rw [hassoc]
    exact mul_le_mul_of_nonneg_left hup1 ht.le
  -- the second cone via the bisector bridge
  have hball : elV ul 0 + t • p ∈ Metric.ball (elV ul 0) h := by
    rw [Metric.mem_ball]
    have hsub : elV ul 0 + t • p - elV ul 0 = t • p := by abel
    have hdp : dist (elV ul 0 + t • p) (elV ul 0) = t * ‖p‖ := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le]
    rw [hdp]
    exact htn
  have hbis : elV ul 0 + t • p ∈ bisLe (elV ul 0) (elV ul 1) := by
    have hhl2 : hl [elV ul 0, elV ul 1] = h := by
      rw [← BARV3_TRUNC1 V ul hb, ← hh]
    have h4 : h = dist (elV ul 0) (elV ul 1) / 2 := by
      rw [← hhl2]
      exact HL_2 (elV ul 0) (elV ul 1)
    refine pA_ball_subset_bis_le (elV ul 0) (elV ul 1) h ?_ hball
    linarith
  have hc2 : elV ul 0 + t • p ∈ rconeGe (elV ul 1) (elV ul 0) (h / Real.sqrt 2) :=
    RCONE_PAIR (elV ul 0) (elV ul 1) (h / Real.sqrt 2) huv hapos hale ⟨hc1, hbis⟩
  -- the wedge is radially closed from the apex by the weight characterisation
  have hc3 : elV ul 0 + t • p ∈ affGe {elV ul 0, elV ul 1}
      {mxi V ul, omegaListN V ul 3} := by
    obtain ⟨c, d, e, hcc, hdd, hty⟩ := (p21w_affGe_2_2_char hd4 _).mp hup3
    have hpvec : p = c • (mxi V ul - elV ul 0) + d • (omegaListN V ul 3 - elV ul 0)
        + e • (elV ul 1 - elV ul 0) := by
      have h2 : elV ul 0 + p = elV ul 0 + (c • (mxi V ul - elV ul 0)
          + d • (omegaListN V ul 3 - elV ul 0) + e • (elV ul 1 - elV ul 0)) := by
        rw [hty]
        simp only [sub_smul, one_smul, smul_sub]
        abel
      have h3 := congrArg (fun z : V3 => -elV ul 0 + z) h2
      simpa using h3
    have hty2 : elV ul 0 + t • p = (t * c) • (mxi V ul) + (t * d) • (omegaListN V ul 3)
        + (t * e) • (elV ul 1) + (1 - t * c - t * d - t * e) • (elV ul 0) := by
      rw [hpvec]
      simp only [smul_add, smul_smul, smul_sub, sub_smul, one_smul]
      abel
    exact (p21w_affGe_2_2_char hd4 _).mpr ⟨t * c, t * d, t * e,
      mul_nonneg ht.le hcc, mul_nonneg ht.le hdd, hty2⟩
  have hmem : elV ul 0 + t • p ∈ mcell2 V ul := by
    rw [hXm]
    exact Set.mem_inter (Set.mem_inter hc1 hc2) hc3
  exact Set.mem_inter hmem hball

/-! ## W3: MCELL2_VOL_SPLIT_EXPLICIT -/

theorem pA_wedge_pair_rw {V : Set V3} {ul : List V3} {P : Set V3 → Prop}
    {w1 w2 : V3} (hpair : {w1, w2} = ({mxi V ul, omegaListN V ul 3} : Set V3))
    (hP : P ({elV ul 0, elV ul 1, w1, w2} : Set V3)) :
    P ({elV ul 0, elV ul 1, mxi V ul, omegaListN V ul 3} : Set V3) := by
  rw [show ({elV ul 0, elV ul 1, mxi V ul, omegaListN V ul 3} : Set V3)
      = {elV ul 0, elV ul 1, w1, w2} from by rw [hpair]]
  exact hP



set_option maxHeartbeats 20000000 in
/-- HOL `MCELL2_VOL_SPLIT_EXPLICIT` (TSKAJXY3.hl:1555; giant; closed
2026-09-30 wedge lane: `MCELL2_SPLIT` regionalises the bisector half, the
`p21w_wedgeGe_eq_affGe` bridge (wedgeGe = affGe, the WEDGE_GE_EQ_AFF_GE
port) and the slicing closed form `p21w_volume_rcone_slab_wedgeGe`
(the `VOLUME_FRUSTT_WEDGE` port: cone-truncated wedge sector,
`azim · (1 - a ^ 2) / a ^ 2 * h ^ 3 / 6`) close it; `BIS_LE_NORM` +
`BARV3_TRUNC1`/`HL_2` identify `bisLe` with the slab at `h = ‖v - u‖ / 2`).
Residual: none. -/
theorem MCELL2_VOL_SPLIT_EXPLICIT (V X : Set V3) (ul : List V3) (h : ℝ)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hhl : h = hl (truncateSimplex 1 ul)) (hht : h < Real.sqrt 2) (hn : ¬nullSet X) :
    volume.real (X ∩ bisLe (elV ul 0) (elV ul 1)) =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) *
        (2 - h ^ 2) * h / 6 := by
  classical
  have huv : elV ul 0 ≠ elV ul 1 := pA_uv_ne V ul hX hn
  have hpos : 0 < h := by rw [hhl]; exact BARV_IMP_HL_1_POS_LT V ul hs hp hb
  have hncp := NOT_COPLANAR_EXTREME_MCELL2 V ul hp hs hb (by rw [hX] at hn; exact hn)
  have hw1 : ¬ Collinear3 (elV ul 0) (elV ul 1) (mxi V ul) := fun hc =>
    hncp (p21_collinear3_coplanar4 _ _ _ _ hc)
  have hw2 : ¬ Collinear3 (elV ul 0) (elV ul 1) (omegaListN V ul 3) := fun hc =>
    hncp (p21_collinear3_coplanar4_last _ _ _ _ hc)
  obtain ⟨w1, w2, hpair, hdihv⟩ := MCELL2_DIHV_AZIM V X ul hp hs hb hX hn
  have hw1' : ¬ Collinear3 (elV ul 0) (elV ul 1) w1 := by
    intro hcc
    have hmem : w1 ∈ ({mxi V ul, omegaListN V ul 3} : Set V3) := by
      have hz : w1 ∈ ({w1, w2} : Set V3) := Set.mem_insert _ _
      rw [hpair] at hz
      exact hz
    rcases Set.mem_insert_iff.mp hmem with hz | hz
    · exact hw1 (hz ▸ hcc)
    · exact hw2 (hz ▸ hcc)
  have hw2' : ¬ Collinear3 (elV ul 0) (elV ul 1) w2 := by
    intro hcc
    have hmem : w2 ∈ ({mxi V ul, omegaListN V ul 3} : Set V3) := by
      have hz : w2 ∈ ({w1, w2} : Set V3) := Set.mem_insert_of_mem _ (Set.mem_singleton w2)
      rw [hpair] at hz
      exact hz
    rcases Set.mem_insert_iff.mp hmem with hz | hz
    · exact hw1 (hz ▸ hcc)
    · exact hw2 (hz ▸ hcc)
  have hθ0 : 0 < azim (elV ul 0) (elV ul 1) w1 w2 := by
    by_contra hz
    push_neg at hz
    have hz0 : azim (elV ul 0) (elV ul 1) w1 w2 = 0 :=
      le_antisymm hz (azim_nonneg _ _ _ _)
    exact hncp (pA_wedge_pair_rw hpair
      (AZIM_EQ_0_PI_IMP_COPLANAR (elV ul 0) (elV ul 1) w1 w2 (Or.inl hz0)))
  have hθπ : azim (elV ul 0) (elV ul 1) w1 w2 < Real.pi := by
    have h1 := MCELL2_DIHV_LT_PI V X ul hp hs hb hX hn
    rw [← hdihv]
    exact h1
  have hd4 : elV ul 0 ≠ elV ul 1 ∧ elV ul 0 ≠ w1 ∧ elV ul 0 ≠ w2 ∧
      elV ul 1 ≠ w1 ∧ elV ul 1 ≠ w2 ∧ w1 ≠ w2 := by
    refine ⟨huv, fun hcc => hw1' ?_, fun hcc => hw2' ?_, fun hcc => hw1' ?_,
      fun hcc => hw2' ?_, fun hcc => hncp (pA_wedge_pair_rw hpair ?_)⟩
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨0, ?_⟩
      rw [hcc, sub_self, zero_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨0, ?_⟩
      rw [hcc, sub_self, zero_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨1, ?_⟩
      rw [hcc, one_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨1, ?_⟩
      rw [hcc, one_smul]
    · refine ⟨elV ul 0, elV ul 1, w1, fun z hz => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · rw [← hcc]
        exact subset_affineSpan ℝ _ (by simp)
  have hhl2 : hl [elV ul 0, elV ul 1] = h := by
    rw [← BARV3_TRUNC1 V ul hb, ← hhl]
  have hdist0 : ‖elV ul 1 - elV ul 0‖ = 2 * h := by
    have h3 := HL_2 (elV ul 0) (elV ul 1)
    rw [hhl2] at h3
    rw [← dist_eq_norm (elV ul 1) (elV ul 0), dist_comm (elV ul 1) (elV ul 0)]
    linarith
  have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hapos : 0 < h / Real.sqrt 2 := div_pos hpos hsqrt2
  have hale : h / Real.sqrt 2 ≤ 1 :=
    (div_le_one hsqrt2).mpr (le_of_lt hht)
  have ha1 : h / Real.sqrt 2 < 1 := (div_lt_one hsqrt2).mpr hht
  rw [MCELL2_SPLIT V X ul hs hp hb hX hn, ← hhl]
  have hslab : {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
        ≤ ‖elV ul 1 - elV ul 0‖ ^ 2 / 2}
      = {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0) ≤ h * ‖elV ul 1 - elV ul 0‖} := by
    rw [hdist0]
    ext y
    simp only [Set.mem_setOf_eq]
    ring
  have hwedge : wedgeGe (elV ul 0) (elV ul 1) w1 w2
      = affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} := by
    rw [p21w_wedgeGe_eq_affGe hd4 hθ0 hθπ, hpair]
  have hset : rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
        ∩ affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3}
        ∩ bisLe (elV ul 0) (elV ul 1)
      = rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
        ∩ {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
            ≤ h * ‖elV ul 1 - elV ul 0‖}
        ∩ wedgeGe (elV ul 0) (elV ul 1) w1 w2 := by
    rw [BIS_LE_NORM, hslab, ← hwedge, Set.inter_assoc, Set.inter_comm (wedgeGe (elV ul 0) (elV ul 1) w1 w2)
        {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
            ≤ h * ‖elV ul 1 - elV ul 0‖}, Set.inter_assoc]
  rw [hset]
  rw [p21w_volume_rcone_slab_wedgeGe (elV ul 0) (elV ul 1) w1 w2 h (h / Real.sqrt 2)
    hapos ha1 huv hw1' hw2' hθ0 hθπ (by linarith)]
  rw [← hdihv]
  have hne0 : (h / Real.sqrt 2) ^ 2 ≠ 0 := by
    have h1 : h / Real.sqrt 2 ≠ 0 := div_ne_zero hpos.ne'
      (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    exact pow_ne_zero 2 h1
  field_simp [hdist0, hne0]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]


theorem MCELL2_SOL (V X : Set V3) (ul : List V3) (h : ℝ) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hhl : h = hl (truncateSimplex 1 ul)) (hht : h < Real.sqrt 2)
    (hn : ¬nullSet X) :
    sol (elV ul 0) X =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) *
        (1 - h / Real.sqrt 2) := by
  classical
  have huv : elV ul 0 ≠ elV ul 1 := pA_uv_ne V ul hX hn
  have hpos : 0 < h := by rw [hhl]; exact BARV_IMP_HL_1_POS_LT V ul hs hp hb
  have hncp := NOT_COPLANAR_EXTREME_MCELL2 V ul hp hs hb (by rw [hX] at hn; exact hn)
  have hw1 : ¬ Collinear3 (elV ul 0) (elV ul 1) (mxi V ul) := fun hc =>
    hncp (p21_collinear3_coplanar4 _ _ _ _ hc)
  have hw2 : ¬ Collinear3 (elV ul 0) (elV ul 1) (omegaListN V ul 3) := fun hc =>
    hncp (p21_collinear3_coplanar4_last _ _ _ _ hc)
  obtain ⟨w1, w2, hpair, hdihv⟩ := MCELL2_DIHV_AZIM V X ul hp hs hb hX hn
  have hw1' : ¬ Collinear3 (elV ul 0) (elV ul 1) w1 := by
    intro hcc
    have hmem : w1 ∈ ({mxi V ul, omegaListN V ul 3} : Set V3) := by
      have hz : w1 ∈ ({w1, w2} : Set V3) := Set.mem_insert _ _
      rw [hpair] at hz
      exact hz
    rcases Set.mem_insert_iff.mp hmem with hz | hz
    · exact hw1 (hz ▸ hcc)
    · exact hw2 (hz ▸ hcc)
  have hw2' : ¬ Collinear3 (elV ul 0) (elV ul 1) w2 := by
    intro hcc
    have hmem : w2 ∈ ({mxi V ul, omegaListN V ul 3} : Set V3) := by
      have hz : w2 ∈ ({w1, w2} : Set V3) := Set.mem_insert_of_mem _ (Set.mem_singleton w2)
      rw [hpair] at hz
      exact hz
    rcases Set.mem_insert_iff.mp hmem with hz | hz
    · exact hw1 (hz ▸ hcc)
    · exact hw2 (hz ▸ hcc)
  have hθ0 : 0 < azim (elV ul 0) (elV ul 1) w1 w2 := by
    by_contra hz
    push_neg at hz
    have hz0 : azim (elV ul 0) (elV ul 1) w1 w2 = 0 :=
      le_antisymm hz (azim_nonneg _ _ _ _)
    exact hncp (pA_wedge_pair_rw hpair
      (AZIM_EQ_0_PI_IMP_COPLANAR (elV ul 0) (elV ul 1) w1 w2 (Or.inl hz0)))
  have hθπ : azim (elV ul 0) (elV ul 1) w1 w2 < Real.pi := by
    have h1 := MCELL2_DIHV_LT_PI V X ul hp hs hb hX hn
    rw [← hdihv]
    exact h1
  have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hapos : 0 < h / Real.sqrt 2 := div_pos hpos hsqrt2
  have hale : h / Real.sqrt 2 ≤ 1 :=
    (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr (le_of_lt hht)
  have hhl2 : hl [elV ul 0, elV ul 1] = h := by
    rw [← BARV3_TRUNC1 V ul hb, ← hhl]
  have hdist0 : dist (elV ul 0) (elV ul 1) = 2 * h := by
    have h3 := HL_2 (elV ul 0) (elV ul 1)
    rw [hhl2] at h3
    linarith
  have hmeas : MeasurableSet (X ∩ Metric.ball (elV ul 0) h) := by
    rw [hX]
    exact (MEASURABLE_MCELL V ul 2 hs hp hb).inter Metric.isOpen_ball.measurableSet
  have hrad := pA_radial_of_mcell2 V ul hs hp hb hX hn
  rw [sol_spec (x := elV ul 0) (C := X) (r := h) hpos hmeas
    (by rw [hhl, hX]; exact hrad)]
  have hbisub : Metric.ball (elV ul 0) h ⊆ bisLe (elV ul 0) (elV ul 1) :=
    pA_ball_subset_bis_le (elV ul 0) (elV ul 1) h (by rw [hdist0])
  have eA : X ∩ Metric.ball (elV ul 0) h
      = (X ∩ bisLe (elV ul 0) (elV ul 1)) ∩ Metric.ball (elV ul 0) h := by
    ext z
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, hbisub h2⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [eA, MCELL2_SPLIT V X ul hs hp hb hX hn, ← hhl]
  have hslab : {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
        ≤ ‖elV ul 1 - elV ul 0‖ ^ 2 / 2}
      = {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0) ≤ h * ‖elV ul 1 - elV ul 0‖} := by
    rw [show ‖elV ul 1 - elV ul 0‖ = dist (elV ul 0) (elV ul 1) from
      (dist_eq_norm (elV ul 1) (elV ul 0)).symm.trans (dist_comm _ _), hdist0]
    ext y
    simp only [Set.mem_setOf_eq]
    ring
  have hd4 : elV ul 0 ≠ elV ul 1 ∧ elV ul 0 ≠ w1 ∧ elV ul 0 ≠ w2 ∧
      elV ul 1 ≠ w1 ∧ elV ul 1 ≠ w2 ∧ w1 ≠ w2 := by
    refine ⟨huv, fun hcc => hw1' ?_, fun hcc => hw2' ?_, fun hcc => hw1' ?_,
      fun hcc => hw2' ?_, fun hcc => hncp (pA_wedge_pair_rw hpair ?_)⟩
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨0, ?_⟩
      rw [hcc, sub_self, zero_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨0, ?_⟩
      rw [hcc, sub_self, zero_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨1, ?_⟩
      rw [hcc, one_smul]
    · rw [collinear3_iff_smul (Ne.symm huv)]
      refine ⟨1, ?_⟩
      rw [hcc, one_smul]
    · refine ⟨elV ul 0, elV ul 1, w1, fun z hz => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · rw [← hcc]
        exact subset_affineSpan ℝ _ (by simp)
  have hwedge : wedgeGe (elV ul 0) (elV ul 1) w1 w2
      = affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} := by
    rw [p21w_wedgeGe_eq_affGe hd4 hθ0 hθπ, hpair]
  have hset : rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
        ∩ affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3}
        ∩ bisLe (elV ul 0) (elV ul 1)
      = rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
        ∩ {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
            ≤ h * ‖elV ul 1 - elV ul 0‖}
        ∩ wedgeGe (elV ul 0) (elV ul 1) w1 w2 := by
    rw [BIS_LE_NORM, hslab, ← hwedge, Set.inter_assoc, Set.inter_comm (wedgeGe (elV ul 0) (elV ul 1) w1 w2)
        {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
            ≤ h * ‖elV ul 1 - elV ul 0‖}, Set.inter_assoc]
  rw [hset]
  have hsd := FRUSTT_WEDGE_RCONE_GE (elV ul 0) (elV ul 1) w1 w2 h (h / Real.sqrt 2)
    hapos huv hale (by linarith) hw1' hw2'
  have hvol1 : volume.real
      (((frustt (elV ul 0) (elV ul 1) h (h / Real.sqrt 2)
          ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2)
        ∩ Metric.ball (elV ul 0) h))
      = volume.real
      (((rconeGe (elV ul 0) (elV ul 1) (h / Real.sqrt 2)
        ∩ {y : V3 | (y - elV ul 0) ⬝ᵥ (elV ul 1 - elV ul 0)
            ≤ h * ‖elV ul 1 - elV ul 0‖}
        ∩ wedgeGe (elV ul 0) (elV ul 1) w1 w2)
      ∩ Metric.ball (elV ul 0) h)) := by
    exact pA_vol_sdiff (pA_sdiff_inter (Z := Metric.ball (elV ul 0) h) hsd)
  rw [← hvol1]
  have hset2 : (frustt (elV ul 0) (elV ul 1) h (h / Real.sqrt 2)
        ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2)
      ∩ Metric.ball (elV ul 0) h
      = (Metric.ball (elV ul 0) h
          ∩ rconeGt (elV ul 0) (elV ul 1) (h / Real.sqrt 2))
        ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2 := by
    ext z
    simp only [frustt, frustum, Set.mem_inter_iff, Set.mem_setOf_eq, rconeGt]
    constructor
    · rintro ⟨⟨⟨⟨hd1, hd2⟩, hgt⟩, hw⟩, hball⟩
      exact ⟨⟨hball, hgt⟩, hw⟩
    · rintro ⟨⟨hball, hgt⟩, hw⟩
      have hnormlt : ‖z - elV ul 0‖ < h := Metric.mem_ball.mp hball
      have habs : |((z - elV ul 0 : V3) ⬝ᵥ (elV ul 1 - elV ul 0))|
          ≤ ‖z - elV ul 0‖ * ‖elV ul 1 - elV ul 0‖ := by
        rw [← inner_eq_dot]
        exact abs_real_inner_le_norm (z - elV ul 0) (elV ul 1 - elV ul 0)
      have h1 : ((z - elV ul 0 : V3) ⬝ᵥ (elV ul 1 - elV ul 0))
          ≤ |((z - elV ul 0 : V3) ⬝ᵥ (elV ul 1 - elV ul 0))| := le_abs_self _
      have hle : ‖z - elV ul 0‖ * ‖elV ul 1 - elV ul 0‖ ≤ h * ‖elV ul 1 - elV ul 0‖ :=
        mul_le_mul_of_nonneg_right hnormlt.le (norm_nonneg _)
      have hge : (0:ℝ) ≤ dist z (elV ul 0) * dist (elV ul 1) (elV ul 0)
          * (h / Real.sqrt 2) :=
        mul_nonneg (mul_nonneg dist_nonneg dist_nonneg) (div_nonneg hpos.le hsqrt2.le)
      refine ⟨⟨⟨⟨?_, ?_⟩, hgt⟩, hw⟩, hball⟩
      · linarith
      · linarith
  rw [hset2]
  have hsd3 : symmDiff ((Metric.ball (elV ul 0) h
          ∩ rconeGt (elV ul 0) (elV ul 1) (h / Real.sqrt 2))
        ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2)
      (ccvConicCap (elV ul 0) (elV ul 1) h (h / Real.sqrt 2)
        ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2)
      ⊆ Metric.sphere (elV ul 0) h := by
    intro z hz
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, ccvConicCap, Metric.mem_closedBall,
      Metric.mem_ball, Set.mem_setOf_eq] at hz
    rcases hz with ⟨⟨⟨hball, hcone⟩, hw⟩, hnot⟩ | ⟨⟨⟨hball2, hcone⟩, hw⟩, hnot⟩
    · exact (hnot ⟨⟨le_of_lt hball, hcone⟩, hw⟩).elim
    · refine Metric.mem_sphere.mpr ?_
      refine le_antisymm hball2 (le_of_not_gt ?_)
      intro hlt
      exact hnot ⟨⟨hlt, hcone⟩, hw⟩
  have hvol2 : volume.real ((Metric.ball (elV ul 0) h
          ∩ rconeGt (elV ul 0) (elV ul 1) (h / Real.sqrt 2))
        ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2)
      = volume.real (ccvConicCap (elV ul 0) (elV ul 1) h (h / Real.sqrt 2)
        ∩ Kepler.Geom.wedge (elV ul 0) (elV ul 1) w1 w2) :=
    pA_vol_sdiff (by
      have hs := (measure_mono hsd3).trans_eq (Measure.addHaar_sphere volume (elV ul 0) h)
      exact le_antisymm hs (zero_le))
  rw [hvol2]
  have hcc := volumeConicCapWedge (elV ul 0) (elV ul 1) w1 w2 h (h / Real.sqrt 2) hapos
    hw1' hw2'
  have hcc2 := volumeConicCap (elV ul 0) (elV ul 1) h (h / Real.sqrt 2) hapos
  have ha1 : h / Real.sqrt 2 < 1 := (div_lt_one hsqrt2).mpr hht
  have hcond : ¬ (elV ul 1 = elV ul 0 ∨ 1 ≤ h / Real.sqrt 2 ∨ h < 0) := by
    rintro (h | h | h)
    · exact huv h.symm
    · exact absurd h (by linarith)
    · linarith
  rw [hcc, hcc2.2, if_neg hcond]
  rw [← hdihv]
  field_simp

/- HOL `MCELL2_VOL_SPLIT_EXPLICIT` (TSKAJXY3.hl:1555; giant): CLOSED above
(wedge closed forms section). -/

/- DEDUP (2026-09-30, LA38 wrapper lane): the local sorry'd copies of
`LEFT_ACTION_LIST_1_PROPERTIES_ALT` and `MCELL2_PERMUTE_01` are DELETED —
PackingAuto14 (:785/:822) now hosts PROVED versions with the identical
statements (incl. the item-19 `hfix` tail-fixedness hypothesis) and is on
this file's transitive import closure (via PackingAuto15), so the names
resolve upstream; the planned chain-copy migration is superseded. -/

/-- HOL `MCELL2_VOL` (TSKAJXY3.hl:1774; assembly 2026-09-30 wave B3:
`MCELL2_VOL_SPLIT` halves the cell across the bisector, each half is the
`MCELL2_VOL_SPLIT_EXPLICIT` wedge volume, the second transported along the
`MCELL2_PERMUTE_01` witness (`DIHV_SYM` closes the axis swap).  Both
consumed upstream giants are CLOSED (wedge closed forms section above). -/
theorem MCELL2_VOL (V X : Set V3) (ul : List V3) (h : ℝ) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hhl : h = hl (truncateSimplex 1 ul)) (hn : ¬nullSet X) :
    volume.real X =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) *
        (2 - h ^ 2) * h / 3 := by
  have hlt : h < Real.sqrt 2 := by rw [hhl]; exact MCELL2_HL_LT_SQRT2 V ul hs hp hb (by rw [← hX]; exact hn)
  rw [MCELL2_VOL_SPLIT V X ul hs hp hb hX hn,
    MCELL2_VOL_SPLIT_EXPLICIT V X ul h hs hp hb hX hhl hlt hn]
  -- second half: transport the explicit assembly along the 01-permutation
  obtain ⟨vl, hv0, hv1, hmxi, hom, hhlv, hcell, hbl⟩ :=
    MCELL2_PERMUTE_01 V ul hs hp hb (by rw [← hX]; exact hn)
  have hhl' : h = hl (truncateSimplex 1 vl) := by rw [hhl, hhlv]
  have h2 := MCELL2_VOL_SPLIT_EXPLICIT V X vl h hs hp hbl
    (by rw [hX]; exact hcell) hhl' hlt hn
  have e0 : bisLe (elV ul 1) (elV ul 0) = bisLe (elV vl 0) (elV vl 1) := by
    rw [hv1, hv0]
  have e1 : dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3)
      = dihV (elV vl 0) (elV vl 1) (mxi V vl) (omegaListN V vl 3) := by
    rw [hv0, hv1, hmxi, hom, DIHV_SYM (elV vl 1) (elV vl 0) (mxi V vl)
      (omegaListN V vl 3)]
  rw [e0, h2, ← e1]
  ring

/-- HOL `BALL_SUBSET_BIS_LE` (TSKAJXY3.hl:1817). -/
theorem BALL_SUBSET_BIS_LE (u v : V3) (r : ℝ) (hr : 2 * r ≤ dist u v) :
    Metric.ball u r ⊆ bisLe u v := by
  intro x hx
  have hxu : dist x u < r := hx
  have hduv : dist u v ≤ dist x u + dist x v := by
    have ht := dist_triangle u x v
    rwa [dist_comm u x] at ht
  have h1 : dist x u ≤ dist x v := by
    linarith [hduv, hr, hxu]
  simp only [bisLe, Set.mem_setOf_eq]
  exact h1

/-- HOL `BALL_SUBSET_BIS_LT` (TSKAJXY3.hl:1833). -/
theorem BALL_SUBSET_BIS_LT (u v : V3) (r : ℝ) (hr : 2 * r ≤ dist u v) :
    Metric.ball u r ⊆ {y : V3 | dist y u < dist y v} := by
  intro x hx
  have hxu : dist x u < r := hx
  have hduv : dist u v ≤ dist x u + dist x v := by
    have ht := dist_triangle u x v
    rwa [dist_comm u x] at ht
  simp only [Set.mem_setOf_eq]
  linarith

/-- HOL `RADIAL_LE` (TSKAJXY3.hl:1849; proved directly from the
`radialNorm` definition in Kepler/Geom/Volume.lean). -/
theorem RADIAL_LE (r r' : ℝ) (x : V3) (C : Set V3) (hr : r' ≤ r) (hpos : 0 < r')
    (h : radialNorm r x (C ∩ Metric.ball x r)) :
    radialNorm r' x (C ∩ Metric.ball x r') := by
  obtain ⟨_, hrad⟩ := h
  refine ⟨Set.inter_subset_right, fun u hu t ht htn => ?_⟩
  have hin := hrad u ⟨hu.1, lt_of_lt_of_le hu.2 hr⟩ t ht (lt_of_lt_of_le htn hr)
  refine ⟨hin.1, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht]
  exact htn

/- HOL `MCELL2_SOL` (TSKAJXY3.hl:1859; giant): CLOSED above (wedge closed
forms section). -/

/-- HOL `GAMMAX_GAMMA2_X` (TSKAJXY3.hl:2070; giant: reduces `gammaX` of a
2-cell to the analytic `gamma2_x_div_azim_v2` per unit azimuth). -/
theorem GAMMAX_GAMMA2_X (V X : Set V3) (ul : List V3) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hn : ¬nullSet X)
    (hy1 : y1 = dist (elV ul 0) (elV ul 1)) (hy2 : y2 = dist (elV ul 0) (mxi V ul))
    (hy3 : y3 = dist (elV ul 0) (omegaListN V ul 3))
    (hy4 : y4 = dist (mxi V ul) (omegaListN V ul 3))
    (hy5 : y5 = dist (elV ul 1) (omegaListN V ul 3))
    (hy6 : y6 = dist (elV ul 1) (mxi V ul)) :
    0 ≤ dihY y1 y2 y3 y4 y5 y6 ∧
      gammaX V X lmfun =
        gamma2_x_div_azim_v2 (h0cut y1) (y1 * y1) * dihY y1 y2 y3 y4 y5 y6 := by
  -- assembly 2026-09-30 (LA38 lane): the blocked gap was the dihV <-> dih_y
  -- bridge, now consumed as the LA38 public 4-point wrapper
  -- `DIHV_EQ_DIH_Y_4PT` (non-collinearity from NOT_COPLANAR_EXTREME_MCELL2,
  -- the MCELL2_DIHV_LT_PI route); the volume/sol/dihX faces rewrite via
  -- GAMMAX_MCELL2/MCELL2_VOL/MCELL2_SOL (second axis vertex through the
  -- MCELL2_PERMUTE_01 witness + DIHV_SYM) and `mi_lmfun_h0cut` closes the
  -- lmfun step; the rest is real-number accounting against the
  -- gamma2_x_div_azim_v2 body.
  have hn2 : ¬nullSet (mcell2 V ul) := by rw [← hX]; exact hn
  have hncp := NOT_COPLANAR_EXTREME_MCELL2 V ul hp hs hb hn2
  have hc2 : ¬ Collinear ℝ ({elV ul 0, elV ul 1, mxi V ul} : Set V3) := fun hc =>
    hncp (p21_collinear3_coplanar4 _ _ _ _ hc)
  have hc3 : ¬ Collinear ℝ ({elV ul 0, elV ul 1, omegaListN V ul 3} : Set V3) :=
    fun hc => hncp (p21_collinear3_coplanar4_last (elV ul 0) (elV ul 1)
      (mxi V ul) (omegaListN V ul 3) hc)
  -- the bridge in y-form
  have hby : dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3)
      = dihY y1 y2 y3 y4 y5 y6 := by
    rw [DIHV_EQ_DIH_Y_4PT_B (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3)
      hc2 hc3, hy1, hy2, hy3, hy4, hy5, hy6]
  -- y1 ≥ 2 (packing edge), for the DIH_Y_NN branch
  obtain ⟨_, huv, _⟩ := MCELL2_VX_PROPS V X ul hs hp hb hX hn
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  have hbsub : barV V 3 [u0, u1, u2, u3] := by rw [← hul]; exact hb
  have hsub : setOfList [u0, u1, u2, u3] ⊆ V := BARV_SUBSET V 3 [u0, u1, u2, u3] hbsub
  have hu0 : elV ul 0 ∈ V := by
    rw [hul]; exact hsub (by simp [setOfList, elV])
  have hu1 : elV ul 1 ∈ V := by
    rw [hul]; exact hsub (by simp [setOfList, elV])
  have hy1ge : (2:ℝ) ≤ dist (elV ul 0) (elV ul 1) := hp.dist_ge_two hu0 hu1 huv
  refine ⟨DIH_Y_NN_B y1 y2 y3 y4 y5 y6 (by rw [hy1]; linarith)
    (by rw [hy1, hy2, hy3, hy4, hy5, hy6];
        exact DELTA_Y_POS_4POINTS_B (elV ul 0) (elV ul 1) (mxi V ul)
          (omegaListN V ul 3)), ?_⟩
  -- the gammaX assembly
  have hht : hl (truncateSimplex 1 ul) < Real.sqrt 2 :=
    MCELL2_HL_LT_SQRT2 V ul hs hp hb (by rw [← hX]; exact hn)
  have hhh : hl (truncateSimplex 1 ul) = y1 / 2 := by
    rw [BARV3_TRUNC1 V ul hb, HL_2, ← hy1]
  -- the second axis-vertex sol rides the 01-permutation witness
  obtain ⟨vl, hv0, hv1, hmxi, hom, hhlv, hcell, hbl⟩ :=
    MCELL2_PERMUTE_01 V ul hs hp hb hn2
  have hsolv := MCELL2_SOL V (mcell2 V vl) vl (hl (truncateSimplex 1 ul)) hs hp hbl
    rfl hhlv hht (by rw [← hcell]; exact hn2)
  have hsol1 : sol (elV ul 1) X
      = dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3)
        * (1 - hl (truncateSimplex 1 ul) / Real.sqrt 2) := by
    have e0 : sol (elV ul 1) X = sol (elV vl 0) (mcell2 V vl) := by
      rw [hv1, hX, hcell]
    rw [e0, hsolv, show elV vl 0 = elV ul 1 from hv1.symm,
      show elV vl 1 = elV ul 0 from hv0.symm,
      show mxi V vl = mxi V ul from hmxi.symm,
      show omegaListN V vl 3 = omegaListN V ul 3 from hom.symm,
      DIHV_SYM (elV ul 1) (elV ul 0) (mxi V ul) (omegaListN V ul 3)]
  rw [GAMMAX_MCELL2 V X ul hs hp hb hX hn,
    MCELL2_VOL V X ul (hl (truncateSimplex 1 ul)) hs hp hb hX rfl hn,
    MCELL2_SOL V X ul (hl (truncateSimplex 1 ul)) hs hp hb hX rfl hht hn,
    hsol1, MCELL2_DIHX V X ul hs hp hb hX hn,
    HL_2, ← hy1, mi_lmfun_h0cut, ← hby, hhh]
  simp only [gamma2_x_div_azim_v2]
  rw [show Real.sqrt (y1 * y1) = y1 from by
        rw [← pow_two]
        exact Real.sqrt_sq (le_of_lt (show (0:ℝ) < y1 by rw [hy1]; linarith)),
    show (y1 / 2) / Real.sqrt 2 = y1 / (2 * Real.sqrt 2) from by ring,
    mi_sqrt8_eq]
  ring

/-- HOL `TSKAJXY_2` (TSKAJXY3.hl:2181; assembly 2026-09-30 wave B3: the
null branch is `GAMMAX_NULLSET`, the non-null branch is `GAMMAX_GAMMA2_X`
with the analytic factor nonnegative on `2 ≤ y1 ≤ √8` (`GRKIBMP` on the
`proj_grk_bank` slice, bounds from `Packing.dist_ge_two`/`MCELL2_HL_LT_SQRT2`
via `BARV3_TRUNC1`+`HL_2`, `mi_sqrt8_eq` for the cap).  Residual: the
consumed `GAMMAX_GAMMA2_X` giant upstream. -/
theorem TSKAJXY_2 (V X : Set V3) (ul : List V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hX : X = mcell2 V ul) : gammaX V X lmfun ≥ 0 := by
  by_cases hn : nullSet X
  · rw [GAMMAX_NULLSET V lmfun X ul 2 hs hp hb (by rw [hX]; exact BumpP4.MCELL2 V ul) hn]
  · -- non-null: the analytic per-azimuth factor is ≥ 0 on the y1-box
    obtain ⟨hy1n, hprod⟩ := GAMMAX_GAMMA2_X V X ul (dist (elV ul 0) (elV ul 1))
      (dist (elV ul 0) (mxi V ul)) (dist (elV ul 0) (omegaListN V ul 3))
      (dist (mxi V ul) (omegaListN V ul 3)) (dist (elV ul 1) (omegaListN V ul 3))
      (dist (elV ul 1) (mxi V ul)) hs hp hb hX hn rfl rfl rfl rfl rfl rfl
    obtain ⟨_, huv, _⟩ := MCELL2_VX_PROPS V X ul hs hp hb hX hn
    obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
    have hbsub : barV V 3 [u0, u1, u2, u3] := by rw [← hul]; exact hb
    have hsub : setOfList [u0, u1, u2, u3] ⊆ V := BARV_SUBSET V 3 [u0, u1, u2, u3] hbsub
    have hu0 : elV ul 0 ∈ V := by
      rw [hul]; exact hsub (by simp [setOfList, elV])
    have hu1 : elV ul 1 ∈ V := by
      rw [hul]; exact hsub (by simp [setOfList, elV])
    have hy2 : (2:ℝ) ≤ dist (elV ul 0) (elV ul 1) := hp.dist_ge_two hu0 hu1 huv
    have hlt : hl (truncateSimplex 1 ul) < Real.sqrt 2 :=
      MCELL2_HL_LT_SQRT2 V ul hs hp hb (by rw [← hX]; exact hn)
    have hy8 : dist (elV ul 0) (elV ul 1) ≤ Real.sqrt 8 := by
      have hlen : dist (elV ul 0) (elV ul 1) = 2 * hl (truncateSimplex 1 ul) := by
        rw [BARV3_TRUNC1 V ul hb, HL_2]
        ring
      rw [hlen, mi_sqrt8_eq]
      exact le_of_lt (mul_lt_mul_of_pos_left hlt (by norm_num : (0:ℝ) < 2))
    have hfac := GRKIBMP (proj_grk_bank hnl) (dist (elV ul 0) (elV ul 1)) hy2 hy8
    rw [hprod]
    exact mul_nonneg hfac hy1n

/-- HOL `tsk_required_ineq` (TSKAJXY3.hl:2240): the string keys of the
Merge_ineq certified inequalities consumed by `TSKAJXY` (no mathematical
content; documentation of the hypothesis bank). -/
def tsk_required_ineq : List String :=
  let cell3Hyp := ["QZECFIC wt0", "QZECFIC wt0 corner", "QZECFIC wt0 sqrt8",
    "QZECFIC wt1", "QZECFIC wt2 A", "CIHTIUM", "CJFZZDW"]
  let tsk := ["TSKAJXY-GXSABWC DIV", "TSKAJXY-IYOUOBF sharp v2",
    "TSKAJXY-IYOUOBF sym",
    "TSKAJXY-RIBCYXU sharp", "TSKAJXY-RIBCYXU sym", "TSKAJXY-TADIAMB",
    "TSKAJXY-WKGUESB sym", "TSKAJXY-XLLIPLS", "TSKAJXY-delta_x4",
    "TSKAJXY-eulerA"]
  let grk := ["GRKIBMP A V2", "GRKIBMP B V2"]
  cell3Hyp ++ tsk ++ grk

/-- HOL `TSKAJXY` (TSKAJXY3.hl:2251): CAPSTONE of the chain. Combines
`TSKAJXY_034` (0/3/4 cells) with `TSKAJXY_1`/`TSKAJXY_2` (1/2 cells).
DISCHARGES: the `pack_nonlinear_non_ox3q1h` antecedent is the Merge_ineq
bank, so the conclusion implies but does not verbatim-match
`Kepler.Text.TSKAJXY_statement` (PackingAuto2.lean:845); no `pack_concl`
interface is discharged here. -/
theorem TSKAJXY (V X : Set V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hs : saturated V) (hp : Packing V) (hm : mcellSet V X)
    (hcrit : criticalEdgeX V X = ∅) : gammaX V X lmfun ≥ 0 := by
  by_cases hcase : ∃ i ul, barV V 3 ul ∧ (i = 1 ∨ i = 2) ∧ X = mcell i V ul
  · obtain ⟨i, ul, hb, hi12, hX⟩ := hcase
    rcases hi12 with hi | hi
    · cases hi
      have hX' : X = mcell1 V ul := by
        rw [hX]
        unfold mcell
        simp
      rw [hX']
      exact TSKAJXY_1 V ul hs hp hb
    · cases hi
      have hX' : X = mcell2 V ul := by
        rw [hX]
        unfold mcell
        simp
      exact TSKAJXY_2 V X ul hnl hs hp hb hX'
  · -- the 0/3/4-cell arm: the Merge_ineq bank slices (grk/cell3/tsk) feed
    -- TSKAJXY_034 via GRKIBMP (wave 1) and cell3_from_ineq_thm (wave 2b).
    have hgrk : GRKIBMP_concl := GRKIBMP (proj_grk_bank hnl)
    have hc3 : cell3_from_ineq := cell3_from_ineq_thm (proj_cell3_bank hnl)
    exact TSKAJXY_034 ⟨hgrk, hc3, proj_tsk_bank hnl⟩ V X hs hp hm hcase hcrit

end WedgeClosedForms

end Kepler.Text

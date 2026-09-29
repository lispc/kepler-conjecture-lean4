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

NEEDS (giant fill-in markers): GAMMAX_MCELL1, MCELL2_VX_PROPS,
  GAMMAX_MCELL2, MCELL1_SOL_RESTRICT, MCELL1_RADIAL, MCELL1_VOL,
  MCELL_CELL_PARAMETERS_D_EXIST, MCELL2_CELL_PARAMETERS_EXIST,
  MCELL_PARAM_D_UL, MCELL2_PARAM_D_UL, MCELL2_DIHX,
  MCELL2_INTER_BIS_LE_MEASURABLE, MCELL2_VOL_SPLIT, RCONE_PAIR,
  MCELL2_SPLIT, FRUSTT_RCONE_GE, FRUSTT_WEDGE_RCONE_GE,
  NOT_COPLANAR_EXTREME_MCELL2, MCELL2_DIHV_LT_PI, MCELL2_DIHV_AZIM,
  MCELL2_VOL_SPLIT_EXPLICIT, MCELL2_PERMUTE_01, MCELL2_VOL, MCELL2_SOL,
  GAMMAX_GAMMA2_X, TSKAJXY_1, TSKAJXY_2, TSKAJXY_034, TSKAJXY,
  NOT_COPLANAR_OMEGA_LIST_N, NOT_COPLANAR_R3, BARV_DISTINCT,
  OMEGA_LIST_BISECTOR, CONVEX_HULL_4_AFF_GE, CONVEX_HULL_SCALE,
  LEFT_ACTION_LIST_1_PROPERTIES_ALT.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto20
import Kepler.Text.SphereKit
import Kepler.Text.IneqClosureDefs
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

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

/-- HOL bank remainder: the other 62 entries of the 81-entry registry
`packNonlinearNonOx3q1hIds` (IdLists.lean:43-126) — JSPEVYT, IXPOTPA,
TXQTPVC, TEWNSCJ, the QITNPEA family, the ZTGIJCF0/4 generated families,
GCKBQEA, RQWUDDU, 6096597438, 1965189142, ....  PLACEHOLDER(G4): to be
split into single-entry leaves when `CertifiedIneqHolds` lands. -/
def pack_nonlinear_rest : Prop := sorry
  -- MERGE-INEQ: 62-entry remainder leaf — NEEDS: G4 主案（Merge_ineq 章程 §2.2/附则1）

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

/-- HOL `gamma3f_gamma3f_x_div_sqrtdelta` (merge_ineq.hl:3292-3310).
Statement frozen for the wave 2b track-7 consumer.  NEEDS: the proof body
runs `gamma3f_gamma3f_x_div_sqrtdelta_WEAK2` (merge_ineq.hl:3079) →
`..._WEAK` (:3024), which needs the solid-angle conversions
`sol_x_sol_euler_x` (:841 — via `simplex_exists` +
`Euler_main_theorem.EULER_TRIANGLE`, both absent from the tree), plus the
matan-level `sol_euler_x = sqrt(delta_x) * sol_euler_x_div_sqrtdelta`
(:1060) and `dih_x = sqrt(delta_x) * dih_x_div_sqrtdelta_posbranch`
(:920) conversions. -/
theorem mi_gamma3f_gamma3f_x_div_sqrtdelta (a b c y4 y5 y6 : ℝ)
    (h4 : 2 ≤ y4) (h5 : 2 ≤ y5) (h6 : 2 ≤ y6) (h4' : y4 ≤ 2 * Real.sqrt 2)
    (h5' : y5 ≤ 2 * Real.sqrt 2) (h6' : y6 ≤ 2 * Real.sqrt 2)
    (het : eta_y y4 y5 y6 < Real.sqrt 2) :
    gamma3f y4 y5 y6 (Real.sqrt 2) lmfun
      = gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) (h0cut y6) a b c
          (y4 * y4) (y5 * y5) (y6 * y6)
        * Real.sqrt (deltaX 2 2 2 (y4 * y4) (y5 * y5) (y6 * y6)) := by
  -- NEEDS: merge_ineq.hl:3024/3079 WEAK/WEAK2 (+ :841/:920/:1060 conversions; EULER_TRIANGLE absent) — see docstring
  sorry

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

/-- HOL `GAMMAX_MCELL1` (TSKAJXY3.hl:48; giant). -/
theorem GAMMAX_MCELL1 (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell1 V ul)
    (_hn : ¬nullSet X) :
    gammaX V X lmfun =
      volume.real X - (2 * mm1 / Real.pi) * sol (elV ul 0) X := by
  sorry

/-- HOL `MCELL2_VX_PROPS` (TSKAJXY3.hl:89; giant). -/
theorem MCELL2_VX_PROPS (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell2 V ul)
    (_hn : ¬nullSet X) :
    VX V X = {elV ul 0, elV ul 1} ∧ elV ul 0 ≠ elV ul 1 ∧
      edgeX V X = {{elV ul 0, elV ul 1}} := by
  sorry

/-- HOL `GAMMAX_MCELL2` (TSKAJXY3.hl:138; giant). -/
theorem GAMMAX_MCELL2 (V X : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell2 V ul)
    (_hn : ¬nullSet X) :
    gammaX V X lmfun =
      volume.real X - (2 * mm1 / Real.pi) * (sol (elV ul 0) X + sol (elV ul 1) X) +
        (8 * mm2 / Real.pi) * lmfun (hl [elV ul 0, elV ul 1]) *
          dihX V X (elV ul 0, elV ul 1) := by
  sorry

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

/-- HOL `MCELL1_SOL_RESTRICT` (TSKAJXY3.hl:285; giant: solid-angle
invariance of `mcell1` under the `sqrt 2`-ball restriction, via
URRPHBZ2 + the `sol` density specification). -/
theorem MCELL1_SOL_RESTRICT (V X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell1 V ul)
    (hn : ¬nullSet X) :
    sol (elV ul 0) X =
      sol (elV ul 0) (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
  sorry

/-- HOL `CONV_CONVEX_HULL` (TSKAJXY3.hl:328). -/
theorem CONV_CONVEX_HULL (s : Set V3) : Convex ℝ s ↔ (convexHull ℝ s : Set V3) = s := by
  constructor
  · intro h
    exact Subset.antisymm (convexHull_min le_rfl h) (subset_convexHull ℝ s)
  · intro h
    rw [← h]
    exact convex_convexHull ℝ s

/-- HOL `CONVEX_HULL_4_AFF_GE` (TSKAJXY3.hl:336; giant). -/
theorem CONVEX_HULL_4_AFF_GE (w0 w1 w2 w3 : V3) (hcp : ¬Coplanar ({w0, w1, w2, w3} : Set V3)) :
    convexHull ℝ ({w0, w1, w2, w3} : Set V3) =
      affGe ({w0} : Set V3) {w1, w2, w3} ∩
        affGe ({w1, w2, w3} : Set V3) ({w0} : Set V3) := by
  sorry

/-- HOL `CONVEX_HULL_SCALE` (TSKAJXY3.hl:363; giant). -/
theorem CONVEX_HULL_SCALE (w0 w1 w2 w3 w : V3) (t : ℝ)
    (hcp : ¬Coplanar ({w0, w1, w2, w3} : Set V3)) (hw : w ∈ convexHull ℝ ({w0, w1, w2, w3} : Set V3))
    (ht : 0 ≤ t)
    (hmem : w0 + t • (w - w0) ∈ affGe ({w1, w2, w3} : Set V3) ({w0} : Set V3)) :
    w0 + t • (w - w0) ∈ convexHull ℝ ({w0, w1, w2, w3} : Set V3) := by
  sorry

/-- HOL `IMAGE_4_EXPLICIT` (TSKAJXY3.hl:394). -/
theorem IMAGE_4_EXPLICIT {B : Type*} (f : ℕ → B) :
    {f i | i ≤ 3} = {f 0, f 1, f 2, f 3} := by
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, by norm_num, rfl⟩

/-- HOL `NULLSET_MCELL1` applied form `NOT_COPLANAR_OMEGA_LIST_N`
(TSKAJXY3.hl:422; giant). -/
theorem NOT_COPLANAR_OMEGA_LIST_N (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (h1 : ¬nullSet (mcell1 V ul)) :
    ¬Coplanar {omegaListN V ul i | i ≤ 3} := by
  sorry

/-- HOL `NOT_COPLANAR_R3` (TSKAJXY3.hl:452; giant: needs the aff_dim
characterisation of `Coplanar`). -/
theorem NOT_COPLANAR_R3 (s : Set V3) (h : ¬Coplanar s) :
    (affineSpan ℝ s : Set V3) = Set.univ := by
  sorry

/-- HOL `BARV_DISTINCT` (TSKAJXY3.hl:464; giant). -/
theorem BARV_DISTINCT (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 1 ul) : elV ul 0 ≠ elV ul 1 := by
  sorry

/-- HOL `OMEGA_LIST_BISECTOR` (TSKAJXY3.hl:495; giant). -/
theorem OMEGA_LIST_BISECTOR (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (h1 : ¬nullSet (mcell1 V ul)) :
    affGe {omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} ({elV ul 0} : Set V3)
      = bisLe (elV ul 0) (elV ul 1) := by
  sorry

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

/-- HOL `MCELL1_RADIAL` (TSKAJXY3.hl:624; giant). -/
theorem MCELL1_RADIAL (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell1 V ul) (hn : ¬nullSet X) :
    radialNorm (Real.sqrt 2) (elV ul 0) (X ∩ Metric.ball (elV ul 0) (Real.sqrt 2)) := by
  sorry

/-- HOL `MCELL1_VOL` (TSKAJXY3.hl:731; giant: needs the `sol` density
specification at the `sqrt 2`-ball). -/
theorem MCELL1_VOL (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell1 V ul) (hn : ¬nullSet X) :
    volume.real X = Real.sqrt 2 ^ 3 / 3 * sol (elV ul 0) X := by
  sorry

-- atn2-merge: `HJKDESR1a_1cell` (TSKAJXY3.hl:766 = TSKAJXY1.hl:5652) is
-- byte-identical to PackingAuto20.lean's declaration; with the hub now
-- imported above, its copy serves both files (plan §5.3).

/-- HOL `TSKAJXY_1` (TSKAJXY3.hl:780; giant: the 1-cell case of TSKAJXY). -/
theorem TSKAJXY_1 (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) : gammaX V (mcell1 V ul) lmfun ≥ 0 := by
  sorry

/-- HOL `MCELL_CELL_PARAMETERS_D_EXIST` (TSKAJXY3.hl:841; giant). -/
theorem MCELL_CELL_PARAMETERS_D_EXIST (V : Set V3) (ul vl : List V3) (k : ℕ) (X : Set V3)
    (hk : k ≤ 4) (hp : Packing V) (hs : saturated V) (hX : X = mcell k V ul)
    (hb : barV V 3 ul) (his : initialSublist vl ul) (hn : ¬nullSet X) :
    (cellParamsD V X vl).1 = k := by
  sorry

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

/-- HOL `MCELL2_CELL_PARAMETERS_EXIST` (TSKAJXY3.hl:884; giant). -/
theorem MCELL2_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hX : X = mcell2 V ul) (hb : barV V 3 ul)
    (hn : ¬nullSet X) : (cellParamsD V X [elV ul 0, elV ul 1]).1 = 2 := by
  sorry

/-- HOL `MCELL_PARAM_D_UL` (TSKAJXY3.hl:897; giant). -/
theorem MCELL_PARAM_D_UL (V : Set V3) (ul ul' vl : List V3) (X : Set V3) (k : ℕ)
    (hk : k ≤ 4) (hp : Packing V) (hs : saturated V) (hX : X = mcell k V ul)
    (hb : barV V 3 ul) (hn : ¬nullSet X) (his : initialSublist ul' ul)
    (hvl : vl = (cellParamsD V X ul').2) :
    X = mcell k V vl ∧ barV V 3 vl ∧ initialSublist ul' vl := by
  sorry

/-- HOL `MCELL2_PARAM_D_UL` (TSKAJXY3.hl:923; giant). -/
theorem MCELL2_PARAM_D_UL (V : Set V3) (ul ul' vl : List V3) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hX : X = mcell2 V ul) (hb : barV V 3 ul)
    (hn : ¬nullSet X) (his : initialSublist ul' ul)
    (hvl : vl = (cellParamsD V X ul').2) :
    X = mcell2 V vl ∧ barV V 3 vl ∧ initialSublist ul' vl := by
  sorry

/-- HOL `MCELL2_DIHX` (TSKAJXY3.hl:936; giant). -/
theorem MCELL2_DIHX (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    dihX V X (elV ul 0, elV ul 1) =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) := by
  sorry

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

/-- NEEDS (NOT discharged this wave): the degenerate-`mcell2` null lemma and
its consumers. Filling `MCELL2_SPLIT`/`MCELL2_VOL_SPLIT` needs, for
`u := elV ul 0`, `v := elV ul 1`:
  1. `u ≠ v` from `¬nullSet (mcell2 V ul)`:
     `u = v` forces `mcell2 V ul = ((rc∩rc) ∩ affGe {u,u} {mxi,omega})` with
     `rc = ⊤`, so the cell sits in `u + span {mxi - u, omega - u}`, a
     translate of a ≤2-dim subspace (`finrank_span_finset_le_card`),
     null by `Measure.addHaar_submodule`. (Drafted; abandoned: the
     `Finset.sum`-membership bookkeeping under the `ofLp`-coercions made the
     `conv_lhs/rw`-chains too brittle for this wave.)
  2. `RCONE_PAIR` (this file, proved below) for the `rconeGe v u a` half of
     `MCELL2_SPLIT`, plus `MCELL2_HL_LT_SQRT2` + the `√2 ≤ hl ul` half.
  3. `MCELL2_VOL_SPLIT` additionally needs the null bisector hyperplane
     (`BIS_HYPERPLANE` + `p21_hyperplane_null`-style: strict affine subspace
     `p₀ + ker(p ↦ c ⬝ᵥ p)`, null by `Measure.addHaar_affineSubspace`), the
     `volume.real`-level union-inter additivity, and `BIS_LE_INTER`/`BIS_LE_UNION`.
-/
theorem MCELL2_SPLIT (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    X ∩ bisLe (elV ul 0) (elV ul 1) =
      rconeGe (elV ul 0) (elV ul 1) (hl (truncateSimplex 1 ul) / Real.sqrt 2) ∩
        affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} ∩
          bisLe (elV ul 0) (elV ul 1) := by
  sorry

theorem MCELL2_VOL_SPLIT (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    volume.real X = volume.real (X ∩ bisLe (elV ul 0) (elV ul 1)) +
      volume.real (X ∩ bisLe (elV ul 1) (elV ul 0)) := by
  sorry

/-- HOL `FRUSTT_RCONE_GE` (TSKAJXY3.hl:1275; giant). -/
theorem FRUSTT_RCONE_GE (u v : V3) (h a : ℝ) (ha : 0 < a) (huv : u ≠ v) :
    nullSet (symmDiff (frustt u v h a)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖})) := by
  sorry

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

/-- HOL `FRUSTT_WEDGE_RCONE_GE` (TSKAJXY3.hl:1368; giant). -/
theorem FRUSTT_WEDGE_RCONE_GE (u v w1 w2 : V3) (h a : ℝ) (ha : 0 < a) (huv : u ≠ v)
    (ha1 : a ≤ 1) (hnn : 0 ≤ h)
    (hc1 : ¬Collinear3 u v w1) (hc2 : ¬Collinear3 u v w2) :
    nullSet (symmDiff (frustt u v h a ∩ wedge u v w1 w2)
      (rconeGe u v a ∩ {y : V3 | (y - u) ⬝ᵥ (v - u) ≤ h * ‖v - u‖} ∩
        wedgeGe u v w1 w2)) := by
  sorry

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

/-- HOL `NOT_COPLANAR_EXTREME_MCELL2` (TSKAJXY3.hl:1434; giant). -/
theorem NOT_COPLANAR_EXTREME_MCELL2 (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    ¬Coplanar ({elV ul 0, elV ul 1, mxi V ul, omegaListN V ul 3} : Set V3) := by
  sorry

/-- HOL `MCELL2_DIHV_LT_PI` (TSKAJXY3.hl:1456; giant). -/
theorem MCELL2_DIHV_LT_PI (V X : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hn : ¬nullSet X) :
    dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) < Real.pi := by
  sorry

/-- HOL `MCELL2_DIHV_AZIM` (TSKAJXY3.hl:1477; giant). -/
theorem MCELL2_DIHV_AZIM (V X : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hn : ¬nullSet X) :
    ∃ w1 w2 : V3, {w1, w2} = ({mxi V ul, omegaListN V ul 3} : Set V3) ∧
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) =
        azim (elV ul 0) (elV ul 1) w1 w2 := by
  sorry

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

/-- HOL `MCELL2_VOL_SPLIT_EXPLICIT` (TSKAJXY3.hl:1555; giant). -/
theorem MCELL2_VOL_SPLIT_EXPLICIT (V X : Set V3) (ul : List V3) (h : ℝ)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hhl : h = hl (truncateSimplex 1 ul)) (hht : h < Real.sqrt 2) (hn : ¬nullSet X) :
    volume.real (X ∩ bisLe (elV ul 0) (elV ul 1)) =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) *
        (2 - h ^ 2) * h / 6 := by
  sorry

/-- HOL `LEFT_ACTION_LIST_1_PROPERTIES_ALT` (TSKAJXY3.hl:1694; giant: a
re-statement of Marchal_cells_2_new.LEFT_ACTION_LIST_1_PROPERTIES, not
ported in this checkout). -/
theorem LEFT_ACTION_LIST_1_PROPERTIES_ALT (V : Set V3) (ul : List V3) (xl : List V3)
    (p : Equiv.Perm ℕ) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hperm : permutes p {0, 1}) (hhl : hl (truncateSimplex 1 ul) < Real.sqrt 2)
    (hsq : Real.sqrt 2 ≤ hl ul) (hxl : xl = leftActionList p ul) :
    barV V 3 xl ∧
      omegaListN V xl 1 = omegaListN V ul 1 ∧
      omegaListN V xl 2 = omegaListN V ul 2 ∧
      omegaListN V xl 3 = omegaListN V ul 3 ∧
      mxi V xl = mxi V ul := by
  sorry

/-- HOL `MCELL2_PERMUTE_01` (TSKAJXY3.hl:1714; giant). -/
theorem MCELL2_PERMUTE_01 (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    ∃ vl : List V3, elV ul 0 = elV vl 1 ∧ elV ul 1 = elV vl 0 ∧
      mxi V ul = mxi V vl ∧ omegaListN V ul 3 = omegaListN V vl 3 ∧
      hl (truncateSimplex 1 ul) = hl (truncateSimplex 1 vl) ∧
      mcell2 V ul = mcell2 V vl ∧ barV V 3 vl := by
  sorry

/-- HOL `MCELL2_VOL` (TSKAJXY3.hl:1774; giant). -/
theorem MCELL2_VOL (V X : Set V3) (ul : List V3) (h : ℝ) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hhl : h = hl (truncateSimplex 1 ul)) (hn : ¬nullSet X) :
    volume.real X =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) *
        (2 - h ^ 2) * h / 3 := by
  sorry

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

/-- HOL `MCELL2_SOL` (TSKAJXY3.hl:1859; giant). -/
theorem MCELL2_SOL (V X : Set V3) (ul : List V3) (h : ℝ) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (hhl : h = hl (truncateSimplex 1 ul)) (hht : h < Real.sqrt 2)
    (hn : ¬nullSet X) :
    sol (elV ul 0) X =
      dihV (elV ul 0) (elV ul 1) (mxi V ul) (omegaListN V ul 3) *
        (1 - h / Real.sqrt 2) := by
  sorry

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
  sorry

/-- HOL `TSKAJXY_2` (TSKAJXY3.hl:2181; giant: the 2-cell case, consuming
GAMMAX_GAMMA2_X + the GRKIBMP bank). -/
theorem TSKAJXY_2 (V X : Set V3) (ul : List V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hX : X = mcell2 V ul) : gammaX V X lmfun ≥ 0 := by
  sorry

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

end Kepler.Text

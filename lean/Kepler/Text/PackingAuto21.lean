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
    intersection with `rcone_gt u v a`); `eta_y`/`tsk_hyp`/
    `pack_nonlinear_non_ox3q1h` are opaque (`sorry`-bodied constants) —
    they enter only sorried capstone statements/proofs.
  - `l ~/ y` in ATN2_Y_NEG etc. uses `Real.arctan`; `atn2` is
    Kepler.Text.SphereKit.atn2 (verbatim sphere.hl:48).

DISCHARGES
  - NONE of the concl interfaces match verbatim: the capstone `TSKAJXY`
    carries the extra antecedent `pack_nonlinear_non_ox3q1h` (the
    Merge_ineq certified-inequality bank, not ported), so it implies but
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
import Kepler.Text.PackingAuto20
import Kepler.Text.SphereKit
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

/-- HOL `eta_y` (sphere.hl): the 3-leg auxiliary entering
`cell3_from_ineq`.  The upstream body is not among local sources (use
sites pin it only through that statement, whose consumers are sorried);
opaque constant of the right type. -/
noncomputable def eta_y (y4 y5 y6 : ℝ) : ℝ := sorry

/-- HOL `h0cut` (Merge_ineq.hl).  Reconstruction: the unique `if`-body
with `lmfun x = h0cut (2 * x) * lfun x` (the upstream `lmfun_h0cut` used
inside GAMMAX_GAMMA2_X): for `x <= 2 * h0` the factor is `1`, else `0`. -/
noncomputable def h0cut (x : ℝ) : ℝ := if x ≤ 2 * h0 then 1 else 0

/-- HOL `tsk_hyp` (Merge_ineq bank, consumed via `tsk_hyp_new`): the
conjunction of the ten certified TSKAJXY inequalities keyed
`TSKAJXY-GXSABWC DIV`, ..., `TSKAJXY-eulerA` (see `tsk_required_ineq`
below).  Opaque: the bank is not among local sources. -/
def tsk_hyp : Prop := sorry

/-- HOL `pack_nonlinear_non_ox3q1h` (Merge_ineq.hl): the certified
nonlinear inequality bank.  Opaque; enters as an antecedent of the
capstones `TSKAJXY_2`/`TSKAJXY` (and the OXLZLEZ3 lane). -/
def pack_nonlinear_non_ox3q1h : Prop := sorry

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

/-- HOL `BIS_HYPERPLANE` (TSKAJXY3.hl:996). -/
theorem BIS_HYPERPLANE (u0 u1 : V3) :
    bis u0 u1 = {p : V3 | ((2:ℝ) • (u0 - u1)) ⬝ᵥ p = (u0 - u1) ⬝ᵥ (u0 + u1)} := by
  sorry

/-- HOL `MCELL2_INTER_BIS_LE_MEASURABLE` (TSKAJXY3.hl:1007; giant). -/
theorem MCELL2_INTER_BIS_LE_MEASURABLE (u0 u1 : V3) (V : Set V3) (X : Set V3)
    (ul : List V3) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hX : X = mcell2 V ul) : MeasurableSet (X ∩ bisLe u0 u1) := by
  sorry

/-- HOL `MCELL2_VOL_SPLIT` (TSKAJXY3.hl:1031; giant). -/
theorem MCELL2_VOL_SPLIT (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    volume.real X = volume.real (X ∩ bisLe (elV ul 0) (elV ul 1)) +
      volume.real (X ∩ bisLe (elV ul 1) (elV ul 0)) := by
  sorry

/-- HOL `RCONE_GT_SCALE` (TSKAJXY3.hl:597; giant). -/
theorem RCONE_GT_SCALE (u0 u1 u : V3) (a t : ℝ) (ht : 0 < t)
    (h : u0 + u ∈ rconeGt u0 u1 a) : u0 + t • u ∈ rconeGt u0 u1 a := by
  sorry

/-- HOL `RCONE_GE_COS` (TSKAJXY3.hl:1067; giant: the Cauchy-Schwarz bound
feeding `cos ∘ arccos` reduction). -/
theorem RCONE_GE_COS (u v : V3) (a : ℝ) (huv : u ≠ v) :
    rconeGe u v a = {u} ∪ {x : V3 | a ≤ Real.cos (arcV u v x)} := by
  sorry

/-- HOL `DIST_LAW_OF_COS_ALT` (TSKAJXY3.hl:1093). -/
theorem DIST_LAW_OF_COS_ALT (u v w : V3) :
    dist v w ^ 2 =
      dist u v ^ 2 + dist u w ^ 2 - 2 * dist u v * dist u w * Real.cos (arcV u v w) := by
  sorry

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

/-- HOL `RCONE_PAIR` (TSKAJXY3.hl:1153; giant: azimuth/`ups_x`/`atn2`
calculus). -/
theorem RCONE_PAIR (u v : V3) (t : ℝ) (huv : u ≠ v) (ht : 0 < t) (ht1 : t ≤ 1) :
    rconeGe u v t ∩ bisLe u v ⊆ rconeGe v u t := by
  sorry

/-- HOL `MCELL2_SPLIT` (TSKAJXY3.hl:1231; giant). -/
theorem MCELL2_SPLIT (V X : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell2 V ul) (hn : ¬nullSet X) :
    X ∩ bisLe (elV ul 0) (elV ul 1) =
      rconeGe (elV ul 0) (elV ul 1) (hl (truncateSimplex 1 ul) / Real.sqrt 2) ∩
        affGe {elV ul 0, elV ul 1} {mxi V ul, omegaListN V ul 3} ∩
          bisLe (elV ul 0) (elV ul 1) := by
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

/-- HOL `MCELL2_HL_LT_SQRT2` (TSKAJXY3.hl:1678; proved by contraposition
against the degenerate branch of the `mcell2` definition). -/
theorem MCELL2_HL_LT_SQRT2 (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hn : ¬nullSet (mcell2 V ul)) :
    hl (truncateSimplex 1 ul) < Real.sqrt 2 := by
  by_contra h
  apply hn
  have hE : mcell2 V ul = (∅ : Set V3) := by
    unfold mcell2
    exact if_neg (by simp [h])
  unfold nullSet
  rw [hE]
  exact measure_empty

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
  · -- the 0/3/4-cell arm: TSKAJXY_034 needs the GRKIBMP/cell3_from_ineq
    -- components of the (opaque) Merge_ineq bank; fill in at merge time.
    sorry

end Kepler.Text

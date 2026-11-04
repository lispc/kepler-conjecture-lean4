/-
LocalAuto17: port of three Flyspeck "remaining conclusions" modules feeding
the Local Fan appendix and the deformation lane:

  - `scripts/local/EYYPQDW.hl` (517 lines, 2 defs + 19 theorems,
    Hoang Le Truong 2012): `mk_planar2` completion `v3` of a planar-face
    triple — coplanarity, the two squared-length realisations
    (`EYYPQDW_NORMV3`, `EYYPQDW_NORM_V3_V1`), the cross-product scalar
    positivity, the `v3_defor_v1`/`v3_defor_v2` defs, the continuity of the
    completion in `x3` (`EYYPQDW_CONTINUOUS_AT_X` feeding `EYYPQDW2`) and in
    `v2` (`EYYPQDW_CONTINUOUS_AT_V` feeding `EYYPQDW3`), and the master
    statement `EYYPQDW` itself.
  - `scripts/local/YRTAFYH.hl` (520 lines, 14 theorems): the ℤ/k arithmetic
    under the diagonal-stabilisation `scs_stab_diag_v39` — `SUR_MOD_FUN`,
    `TRANS_DIAG` (two same-named versions in the source; the second is kept
    as `TRANS_DIAG_SCS_p17`), `scs_components`/`scs_inj` (already proved in
    LocalAuto1; re-stated `_p17` as one-line re-exports), the `DIAG_PSORT`
    psort-shift trio, `A_EQ_PSORT`/`B_EQ_PSORT`, `PROPERTY_OF_K_SCS`,
    `PSORT_PERIODIC`, `DIAG_NOT_PSORT`, `YRTAFYH` (stabilising a diagonal
    with `a <= cstab` preserves `is_scs_v39` + `scs_basic_v39`) and
    `STAB_IS_SCS`.
  - `scripts/local/deformation.hl` (1040 lines, 1 def + 16 theorems,
    John Harrison 2012): the deformation-path machinery — cone separation
    (`SEPARATE_CLOSED_CONES`), the `aff_ge`-cone characterisations
    (`AFF_GE_1_2_0`, `AFF_GE_1_1_0`, `CONIC_AFF_GE_0`), the `fan7`
    re-characterisations (`GMLWKPK`, `GMLWKPK_ALT`, `GMLWKPK_SIMPLE`), the
    perturbation estimates `lemma_1`/`lemma_2`, the minima kit
    (`MINIMIZE_OVER_MEMBERS`, `MINIMIZE_OVER_2`, `MINIMIZE_OVER_STRONGER`),
    the def `deformation` and the capstones `FAN7_SMALL_DEFORMATION` and
    `XRECQNS`.

FILE MAP
  Section A (support kit, `_p17`): the V3 cross-product bridges
    (`coe_cross3_p17`, `dot_coe_p17`, `cross3_lagrange_p17`, cross
    continuity), `cross3_ne_zero_p17`/`upsX_pos_of_noncollinear_p17`
    (the HOL `th3`/`DIST_UPS_X_POS`/`FHFMKIY` triangle), the translation
    invariance `collinear_transable_p17` (HOL `COLLINEAR_TRANSABLE`), and
    the ℤ/k arithmetic kit (`MOD_EQ_MOD_SHIFT_p17`, `mod_congr_add_p17`,
    `mod_add_cancel_p17`, `periodic2_mod_p17`, `psort_pair_eq_p17`).
  Section B (EYYPQDW): defs `v3DeforV1_p17`/`v3DeforV2_p17`, then the
    theorems in source order.
  Section C (YRTAFYH): the arithmetic theorems, then `YRTAFYH_p17` and
    `STAB_IS_SCS_p17`.
  Section D (deformation): `conicP17`, then the items in source order.

ENCODING NOTES (deformation kit and friends)
  - HOL `real^3` <-> `V3` (Kepler.Geom); `vec 0` <-> `0`; `dist(v,w) pow 2`
    <-> `dist v w ^ 2`; `a % v` <-> `a • v`; `sqrt` <-> `Real.sqrt`; NO
    `native_decide` anywhere.
  - `inv(&2*x1)*(x1+x3-x5)` and `inv x1 * a * sqrt(inv u * v)` are rendered
    with the division form `(x1 + x3 - x5) / (2 * x1)` and
    `(a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)` — the verbatim
    renderings already used by `mkPlanar2` (LocalAuto1.lean:787); `inv` is
    total on both sides so this is a pure re-association (HOL `MK_PLANAR_REP`
    exists exactly to move between the two shapes).
  - HOL `lift` / `drop` / `continuous atreal` collapse: `lift o f
    continuous atreal x` renders as `ContinuousAt f x` (LocalAuto11
    convention, head note there); `LIFT_CONTINUOUS_ATREAL` becomes
    `ContinuousAt id x`.
  - HOL `conic s` has no corpus port: `conicP17` is defined here verbatim
    (`!c x. &0 <= c /\ x IN s ==> c % x IN s`).
  - HOL `deformation ff V (a,b)` is ALREADY ported verbatim as `Deformation`
    (LocalAuto1.lean:128, `(0 : ℝ) ∈ Icc a b` = `(0) IN real_interval
    (a,b)`); no body copy is made — `deformationP17` is a one-line alias for
    the record (merge note: delete when the def moves upstream).
  - HOL `graph`/`fan6`/`fan7`/`FAN` are `Kepler.Text.Fan.Graph`/`fan6`/
    `fan7`/`FAN` (Fan.lean); `aff_ge` is `affGe` (Kepler.Geom.Aff).
  - `sgin`: `a IN {--&1, &1}` <-> `a ∈ ({-1, 1} : Set ℝ)`.
  - The HOL helper stack `th3`/`Trigonometry1.DIST_UPS_X_POS`/
    `Collect_geom.FHFMKIY` (positivity of `ups_x x1 x2 x6` from the
    non-collinearity + Cayley data) is re-proved here from the Lagrange
    identity `cross_dot_cross` as `upsX_pos_of_noncollinear_p17`.
  - Name plan: every NEW declaration carries the `_p17` suffix. Importable
    items are used unqualified from LocalAuto1 (`ScsV39`, `isScsV39`,
    `scsBasicV39`, `scsDiag`, `psort`, `scsStabDiagV39`, `cstab`, `Periodic`,
    `Periodic2`, `mkPlanar2`, `Deformation`), PackingAuto18 (`upsX`,
    `cross3`) and Kepler.Text.Fan (`FAN`, `fan6`, `fan7`, `Graph`).
    Same-wave lanes own LocalAuto12-16/18 — nothing is imported from them;
    no `_p17` copies of their material are needed here.

DISCHARGES convention (LocalAuto1.lean:44): the registry items of the
appendix lane are stated (sorry'd) there; matching statements here carry a
DISCHARGES marker and the LocalAuto1 `sorry` disappears when this file's
body is proved:
  - `EYYPQDW_p17`   DISCHARGES: LocalAuto1.EYYPQDW_concl  (appendix.hl:1244)
  - `EYYPQDW2_p17`  DISCHARGES: LocalAuto1.EYYPQDW2_concl (appendix.hl:1259)
  - `EYYPQDW3_p17`  DISCHARGES: LocalAuto1.EYYPQDW3_concl (appendix.hl:1268)
  - `YRTAFYH_p17`   DISCHARGES: LocalAuto1.YRTAFYH_concl  (appendix.hl:1554)
All four are stated faithfully here; `EYYPQDW2_p17`/`EYYPQDW3_p17` are
PROVED; `EYYPQDW_p17` PROVED (fill wave 2026-09-19, via the discharged
`EYYPQDW_NORMV3_p17`/`EYYPQDW_NORM_V3_V1_p17` Cayley identities);
`YRTAFYH_p17` remains sorry'd (giant case tree — see NEEDS marker).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.Fan
import Kepler.Text.TopologyFan
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Section A: support kit -/

/-- Pi-side coe of `cross3` (TopologyFan's private `coe_cross3`). -/
private theorem coe_cross3_p17 (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) = crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) :=
  coe_toLp _

/-- Pi-side dot equals the V3 dot (TopologyFan's private `dot_coe`). -/
private theorem dot_coe_p17 (a b : V3) :
    (a : Fin 3 → ℝ) ⬝ᵥ (b : Fin 3 → ℝ) = a ⬝ᵥ b := by
  rw [← dot_toLp, WithLp.toLp_ofLp]

/-- HOL `CROSS_LAGRANGE` shape needed at EYYPQDW (`v1 cross (v1 cross v2) =
(v1 dot v2) % v1 - (v1 dot v1) % v2`), via Mathlib
`cross_cross_eq_smul_sub_smul'` on the `Fin 3 → ℝ` identification. -/
private theorem cross3_lagrange_p17 (a b : V3) :
    cross3 a (cross3 a b) = (a ⬝ᵥ b) • a - (a ⬝ᵥ a) • b := by
  rw [cross3, coe_cross3_p17,
    cross_cross_eq_smul_sub_smul' (a : Fin 3 → ℝ) (a : Fin 3 → ℝ) (b : Fin 3 → ℝ),
    WithLp.toLp_sub, WithLp.toLp_smul, WithLp.toLp_smul, dot_coe_p17, dot_coe_p17,
    WithLp.toLp_ofLp, WithLp.toLp_ofLp]

private theorem crossProduct_apply_p17 (a b : Fin 3 → ℝ) (i : Fin 3) :
    crossProduct a b i = a (i + 1) * b (i + 2) - a (i + 2) * b (i + 1) := by
  rw [cross_apply]
  fin_cases i <;> simp

private theorem continuousAt_cross3_right_p17 (u v : V3) :
    ContinuousAt (fun w : V3 => cross3 u w) v := by
  refine Continuous.continuousAt ?_
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp ?_
  refine continuous_pi (fun i => ?_)
  simp only [crossProduct_apply_p17]
  exact (continuous_const.mul
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) (i + 2))).sub
    (continuous_const.mul
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) (i + 1)))

/-- `cross3 v1 v2 ≠ 0` for a non-collinear pair at the origin (the squared
Lagrange identity plus the Cauchy–Schwarz equality case). -/
private theorem cross3_ne_zero_p17 {v1 v2 : V3}
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) : cross3 v1 v2 ≠ 0 := by
  intro hzero
  refine hnc ?_
  by_cases hv1 : v1 = 0
  · subst hv1; simpa using collinear_pair ℝ (0:V3) v2
  have hsq : ‖cross3 v1 v2‖ ^ 2 =
      (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) - (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) := by
    rw [show ‖cross3 v1 v2‖ ^ 2 = inner ℝ (cross3 v1 v2) (cross3 v1 v2) from
      (real_inner_self_eq_norm_sq _).symm, inner_eq_dot, coe_cross3_p17,
      cross_dot_cross]
  have hzero' : (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) - (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) = 0 := by
    rw [← hsq, hzero]; simp
  have hD : (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2) = (‖v1‖ * ‖v2‖) * (‖v1‖ * ‖v2‖) := by
    have h11 : v1 ⬝ᵥ v1 = ‖v1‖ ^ 2 := (norm_sq_eq_dot v1).symm
    have h22 : v2 ⬝ᵥ v2 = ‖v2‖ ^ 2 := (norm_sq_eq_dot v2).symm
    have hcomm : (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) = (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2) := by
      rw [dotProduct_comm (v2 : Fin 3 → ℝ) (v1 : Fin 3 → ℝ)]
    have hA : (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) = (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) := by
      linarith [hzero']
    calc (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2) = (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) := hcomm.symm
      _ = (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) := hA.symm
      _ = (‖v1‖ * ‖v2‖) * (‖v1‖ * ‖v2‖) := by rw [h11, h22]; ring
  have habs : |v1 ⬝ᵥ v2| = ‖v1‖ * ‖v2‖ :=
    (mul_self_inj_of_nonneg (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
      (by rw [abs_mul_abs_self]; exact hD)
  have hinner : ‖inner ℝ v1 v2‖ = ‖v1‖ * ‖v2‖ := by
    rw [inner_eq_dot, Real.norm_eq_abs]; exact habs
  rcases ((norm_inner_eq_norm_tfae ℝ v1 v2).out 0 2).mp hinner with h0 | ⟨c, hc⟩
  · exact absurd h0 hv1
  · exact collinear3_iff_smul (v := (0:V3)) (w := v1) (w1 := v2) hv1 |>.mpr
      ⟨c, by simpa using hc⟩

/-- HOL `th3`/`Trigonometry1.DIST_UPS_X_POS`/`Collect_geom.FHFMKIY` triangle:
the Gram determinant `ups_x x1 x2 x6` is positive for a non-collinear pair
with the given Cayley data. -/
private theorem upsX_pos_of_noncollinear_p17 (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    0 < upsX x1 x2 x6 := by
  have hcross : cross3 v1 v2 ≠ 0 := cross3_ne_zero_p17 hnc
  have hsq : ‖cross3 v1 v2‖ ^ 2 =
      (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) - (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) := by
    rw [show ‖cross3 v1 v2‖ ^ 2 = inner ℝ (cross3 v1 v2) (cross3 v1 v2) from
      (real_inner_self_eq_norm_sq _).symm, inner_eq_dot, coe_cross3_p17,
      cross_dot_cross]
  have h6 : ‖v1 - v2‖ ^ 2 = ‖v1‖ ^ 2 - 2 * (v1 ⬝ᵥ v2) + ‖v2‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_eq_dot]
  have hd6 : x6 = x1 + x2 - 2 * (v1 ⬝ᵥ v2) := by
    rw [← hx6, h6, hx1, hx2]; ring
  have hups : upsX x1 x2 x6 =
      4 * ((v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) - (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1)) := by
    rw [hd6]
    have h11 : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
    have h22 : v2 ⬝ᵥ v2 = x2 := (norm_sq_eq_dot v2).symm.trans hx2
    unfold upsX
    rw [h11, h22, dotProduct_comm (v2 : Fin 3 → ℝ) (v1 : Fin 3 → ℝ)]
    ring
  have hpos : 0 < (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) - (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) := by
    have h3 : 0 < ‖cross3 v1 v2‖ ^ 2 := pow_pos (norm_pos_iff.mpr hcross) 2
    rw [hsq] at h3
    exact h3
  rw [hups]; linarith

/-! ### `_p17` cross3-linearity and dot bridges (fill kit) -/

private theorem coe_add_p17 (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

private theorem coe_smul_p17 (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem crossProduct_smul_left_p17 (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

private theorem crossProduct_add_left_p17 (p q r : Fin 3 → ℝ) :
    crossProduct (p + q) r = crossProduct p r + crossProduct q r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.add_apply]

private theorem toLp_smul_p17 (t : ℝ) (x : Fin 3 → ℝ) :
    (WithLp.toLp 2 (t • x) : V3) = t • WithLp.toLp 2 x := rfl

private theorem toLp_add_p17 (x y : Fin 3 → ℝ) :
    (WithLp.toLp 2 (x + y) : V3) = WithLp.toLp 2 x + WithLp.toLp 2 y := rfl

private theorem cross3_smul_left_p17 (t : ℝ) (a b : V3) :
    cross3 (t • a) b = t • cross3 a b := by
  rw [cross3, cross3, coe_smul_p17, crossProduct_smul_left_p17, toLp_smul_p17]

private theorem cross3_add_left_p17 (a b c : V3) :
    cross3 (a + b) c = cross3 a c + cross3 b c := by
  rw [cross3, cross3, cross3, coe_add_p17, crossProduct_add_left_p17, toLp_add_p17]

private theorem cross3_self_p17 (a : V3) : cross3 a a = 0 := by
  rw [cross3, cross_self]
  rfl

private theorem coe_neg_p17 (a : V3) :
    ((-a : V3) : Fin 3 → ℝ) = -(a : Fin 3 → ℝ) := rfl

private theorem toLp_neg_p17 (x : Fin 3 → ℝ) :
    (WithLp.toLp 2 (-x) : V3) = -WithLp.toLp 2 x := rfl

private theorem cross3_neg_left_p17 (a c : V3) : cross3 (-a) c = -cross3 a c := by
  rw [cross3, cross3, coe_neg_p17, map_neg, LinearMap.neg_apply, toLp_neg_p17]

private theorem cross3_sub_left_p17 (a b c : V3) :
    cross3 (a - b) c = cross3 a c - cross3 b c := by
  rw [sub_eq_add_neg, cross3_add_left_p17, cross3_neg_left_p17]
  abel




private theorem cross3_anticomm_p17 (a b : V3) : cross3 a b = -cross3 b a := by
  rw [cross3, cross3, ← cross_anticomm, toLp_neg_p17]

private theorem dot_smul_left_p17 (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_smul_right_p17 (t : ℝ) (a b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_add_left_p17 (a b c : V3) :
    (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_add_right_p17 (a b c : V3) :
    a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_comm_p17 (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_cross3_self_left_p17 (a b : V3) : a ⬝ᵥ cross3 a b = 0 :=
  dot_self_cross (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_cross3_v1_X_p17 (v1 v2 : V3) :
    v1 ⬝ᵥ cross3 v1 (cross3 v1 v2) = 0 :=
  dot_cross3_self_left_p17 v1 (cross3 v1 v2)

private theorem cross3_X_smul_p17 (v1 v2 : V3) :
    cross3 (cross3 v1 (cross3 v1 v2)) v1 = (v1 ⬝ᵥ v1) • cross3 v1 v2 := by
  rw [cross3_lagrange_p17, cross3_sub_left_p17, cross3_smul_left_p17,
    cross3_smul_left_p17, cross3_self_p17, smul_zero, zero_sub,
    cross3_anticomm_p17 v2 v1, smul_neg, neg_neg]


/-- HOL `Trigonometry2.COLLINEAR_TRANSABLE`: collinearity is translation
invariant. -/
private theorem collinear3_iff_smul_p17 (v w w1 : V3) (hw : w ≠ v) :
    Collinear ℝ ({v, w, w1} : Set V3) ↔ ∃ c : ℝ, w1 - v = c • (w - v) :=
  collinear3_iff_smul hw

private theorem collinear_transable_p17 (v0 v1 v2 : V3) :
    Collinear ℝ ({v0, v1, v2} : Set V3) ↔
      Collinear ℝ ({0, v1 - v0, v2 - v0} : Set V3) := by
  by_cases hv : v1 = v0
  · constructor
    · intro _; rw [hv]; simpa using collinear_pair ℝ (0:V3) (v2 - v0)
    · intro _; rw [hv]; simpa using collinear_pair ℝ v0 v2
  · have hv' : v1 - v0 ≠ 0 := sub_ne_zero.mpr hv
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (collinear3_iff_smul_p17 v0 v1 v2 hv).mp h
      exact (collinear3_iff_smul_p17 0 (v1 - v0) (v2 - v0) hv').mpr ⟨c, by simp [hc]⟩
    · intro h
      obtain ⟨c, hc⟩ :=
        (collinear3_iff_smul_p17 0 (v1 - v0) (v2 - v0) hv').mp h
      exact (collinear3_iff_smul_p17 v0 v1 v2 hv).mpr ⟨c, by simpa using hc⟩

/-! ### ℤ/k arithmetic kit -/

private theorem mod_congr_add_p17 (k i a b : ℕ) (h : a % k = b % k) :
    (i + a) % k = (i + b) % k := by
  rw [Nat.add_mod i a k, Nat.add_mod i b k, h]

private theorem mod_add_cancel_p17 (k i a b : ℕ) (hk : k ≠ 0)
    (h : (i + a) % k = (i + b) % k) : a % k = b % k := by
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  have hik := Nat.mod_lt i hk'
  have ha := Nat.mod_lt a hk'
  have hb := Nat.mod_lt b hk'
  rw [Nat.add_mod i a k, Nat.add_mod i b k] at h
  rcases Nat.lt_or_ge (i % k + a % k) k with h2 | h2 <;>
    rcases Nat.lt_or_ge (i % k + b % k) k with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h; omega
  · have h4 : i % k + b % k - k < k := by omega
    rw [show i % k + b % k = (i % k + b % k - k) + k from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h2] at h
    omega
  · have h4 : i % k + a % k - k < k := by omega
    rw [show i % k + a % k = (i % k + a % k - k) + k from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h3] at h
    omega
  · have h4 : i % k + a % k - k < k := by omega
    have h5 : i % k + b % k - k < k := by omega
    rw [show i % k + a % k = (i % k + a % k - k) + k from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h4,
      show i % k + b % k = (i % k + b % k - k) + k from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h5] at h
    omega

/-- HOL `Ocbicby.MOD_EQ_MOD_SHIFT`. -/
theorem MOD_EQ_MOD_SHIFT_p17 (k i' p p' i : ℕ) (hk : k ≠ 0)
    (h : (i + p) % k = p' % k) : (i' + i + p) % k = (i' + p') % k := by
  rw [Nat.add_assoc]
  exact mod_congr_add_p17 k i' (i + p) p' h

/-- HOL `psort` equality in terms of the unordered mod pairs. -/
private theorem psort_pair_eq_p17 (k a b c d : ℕ) :
    psort k (a, b) = psort k (c, d) ↔
      (a % k = c % k ∧ b % k = d % k) ∨ (a % k = d % k ∧ b % k = c % k) := by
  simp only [psort]
  by_cases h1 : a % k ≤ b % k
  · rw [if_pos h1]
    by_cases h2 : c % k ≤ d % k
    · rw [if_pos h2, Prod.mk.injEq]; omega
    · rw [if_neg h2, Prod.mk.injEq]; omega
  · rw [if_neg h1]
    by_cases h2 : c % k ≤ d % k
    · rw [if_pos h2, Prod.mk.injEq]; omega
    · rw [if_neg h2, Prod.mk.injEq]; omega

/-- One-sided coordinate reduction under `Periodic2`. -/
private theorem periodic2_mod_p17 {α : Sort u} {k : ℕ} {f : ℕ → ℕ → α}
    (hper : Periodic2 f k) (i j : ℕ) : f (i % k) (j % k) = f i j := by
  have hper1 : ∀ i j : ℕ, f (i + k) j = f i j := fun i j => (hper i j).1
  have hper2 : ∀ i j : ℕ, f i (j + k) = f i j := fun i j => (hper i j).2
  have auxL : ∀ u d r : ℕ, f (r + d * k) u = f r u := by
    intro u d
    induction d with
    | zero => intro r; simp
    | succ d ih =>
        intro r
        have he : r + (d + 1) * k = (r + d * k) + k := by ring
        rw [he, hper1]
        exact ih r
  have auxR : ∀ u d r : ℕ, f u (r + d * k) = f u r := by
    intro u d
    induction d with
    | zero => intro r; simp
    | succ d ih =>
        intro r
        have he : r + (d + 1) * k = (r + d * k) + k := by ring
        rw [he, hper2]
        exact ih r
  calc f (i % k) (j % k) = f (i % k) j := by
        rw [← auxR (i % k) (j / k) (j % k), Nat.mod_add_div' j k]
    _ = f i j := by
        rw [← auxL j (i / k) (i % k), Nat.mod_add_div' i k]

/-! ## Section B: EYYPQDW — the `mk_planar2` completion of a planar face -/

/-- HOL `SGIN_POW_EQ`. -/
theorem SGIN_POW_EQ_p17 (a : ℝ) (h : a ∈ ({-1, 1} : Set ℝ)) : a ^ 2 = 1 := by
  rcases h with rfl | rfl <;> norm_num

/-- HOL `EYYPQDW_COPLANAR`: the completion `v3` lies in the plane of
`{vec 0, v1, v2}` (via the Lagrange identity, `cross3 v1 (cross3 v1 v2)` is a
`v1, v2`-combination). -/
theorem EYYPQDW_COPLANAR_p17 (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
    (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3) :
    Coplanar ({0, v1, v2, v3} : Set V3) := by
  have hlag := cross3_lagrange_p17 v1 v2
  set c1 := (x1 + x3 - x5) / (2 * x1) with hc1
  set c2 := (a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6) with hc2
  have hv3' : v3 = (c1 + c2 * (v1 ⬝ᵥ v2)) • v1 - (c2 * (v1 ⬝ᵥ v1)) • v2 := by
    rw [← hv3, hlag]; module
  have hv1 : (v1 : V3) ∈ vectorSpan ℝ ({0, v1, v2} : Set V3) := by
    have h : (v1 - (0:V3)) ∈ vectorSpan ℝ ({0, v1, v2} : Set V3) :=
      vsub_mem_vectorSpan (k := ℝ) (p₁ := (v1:V3)) (p₂ := (0:V3)) (by simp) (by simp)
    simpa using h
  have hv2 : (v2 : V3) ∈ vectorSpan ℝ ({0, v1, v2} : Set V3) := by
    have h : (v2 - (0:V3)) ∈ vectorSpan ℝ ({0, v1, v2} : Set V3) :=
      vsub_mem_vectorSpan (k := ℝ) (p₁ := (v2:V3)) (p₂ := (0:V3)) (by simp) (by simp)
    simpa using h
  have hmem : (v3 : V3) ∈ vectorSpan ℝ ({0, v1, v2} : Set V3) := by
    rw [hv3']
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hv1) (Submodule.smul_mem _ _ hv2)
  have h0mem : (0 : V3) ∈ (affineSpan ℝ ({0, v1, v2} : Set V3) : Set V3) :=
    mem_affineSpan ℝ (by simp)
  have hv3mem := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan h0mem hmem
  refine ⟨0, v1, v2, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · simpa using hv3mem

/-- The `‖t • v‖² = t²‖v‖²` bridge (the cross3 fill-kit's norm twin). -/
private theorem normsq_smul_p17 (t : ℝ) (v : V3) : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Orthogonal pieces split a squared norm (`norm_add_sq_real` + the
`v1 ⬝ᵥ cross3 v1 (cross3 v1 v2) = 0` dot bridge). -/
private theorem normsq_add_orth_p17 (t s : ℝ) (u w : V3) (hd : u ⬝ᵥ w = 0) :
    ‖t • u + s • w‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, inner_eq_dot, hd,
    normsq_smul_p17, normsq_smul_p17]
  ring

/-- The squared norm of the double cross term: the Cayley identity
`‖cross3 v1 (cross3 v1 v2)‖² = x1 * upsX x1 x2 x6 / 4` (Lagrange /
`cross_dot_cross` twice + the Gram expansion of `upsX`). -/
private theorem normsq_double_cross_p17 (v1 v2 : V3) (x1 x2 x6 : ℝ)
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
  have hzero : ((v1 : V3) : Fin 3 → ℝ) ⬝ᵥ
      (crossProduct ((v1 : V3) : Fin 3 → ℝ) ((v2 : V3) : Fin 3 → ℝ)) = 0 :=
    dot_self_cross _ _
  have hw'raw : ((cross3 v1 v2 : V3) : Fin 3 → ℝ) ⬝ᵥ ((cross3 v1 v2 : V3) : Fin 3 → ℝ)
      = (v1 ⬝ᵥ v1) * (v2 ⬝ᵥ v2) - (v1 ⬝ᵥ v2) * (v2 ⬝ᵥ v1) :=
    cross_dot_cross ((v1 : V3) : Fin 3 → ℝ) ((v2 : V3) : Fin 3 → ℝ)
      ((v1 : V3) : Fin 3 → ℝ) ((v2 : V3) : Fin 3 → ℝ)
  have hwnraw : ((cross3 v1 (cross3 v1 v2) : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((cross3 v1 (cross3 v1 v2) : V3) : Fin 3 → ℝ)
      = (v1 ⬝ᵥ v1) * (((cross3 v1 v2 : V3) : Fin 3 → ℝ) ⬝ᵥ
          ((cross3 v1 v2 : V3) : Fin 3 → ℝ)) := by
    rw [coe_cross3_p17, coe_cross3_p17, cross_dot_cross, hzero, zero_mul, sub_zero]
  rw [show ‖cross3 v1 (cross3 v1 v2)‖ ^ 2 = inner ℝ (cross3 v1 (cross3 v1 v2))
      (cross3 v1 (cross3 v1 v2)) from (real_inner_self_eq_norm_sq _).symm,
    inner_eq_dot, hwnraw, hw'raw,
    dotProduct_comm ((v2 : V3) : Fin 3 → ℝ) ((v1 : V3) : Fin 3 → ℝ), h11, h22, hups4]
  field_simp

/-- HOL `EYYPQDW_NORMV3`: the realisation `‖v3‖^2 = x3`.
DISCHARGED: the Cayley algebra of the HOL proof (EYYPQDW.hl:85-157) —
the cross term `cross3 v1 (cross3 v1 v2)` is orthogonal to `v1`
(`dot_cross3_v1_X_p17`), has norm² `x1 * upsX x1 x2 x6 / 4`
(`normsq_double_cross_p17`), and the sign scalar squares to
`upsX x1 x3 x5 / (upsX x1 x2 x6 * x1 ^ 2)`; the two pieces then telescope
against `upsX x1 x3 x5 = 4 * x1 * x3 - (x1 + x3 - x5) ^ 2`. -/
theorem EYYPQDW_NORMV3_p17 (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
    (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3) :
    ‖v3‖ ^ 2 = x3 := by
  have hups126 : 0 < upsX x1 x2 x6 :=
    upsX_pos_of_noncollinear_p17 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6
  have hwnorm := normsq_double_cross_p17 v1 v2 x1 x2 x6 hx1 hx2 hx6
  have hbeta : ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) ^ 2
      = upsX x1 x3 x5 / (upsX x1 x2 x6 * x1 ^ 2) := by
    have hq : 0 ≤ upsX x1 x3 x5 / upsX x1 x2 x6 :=
      div_nonneg hups.le hups126.le
    rw [mul_pow, div_pow, SGIN_POW_EQ_p17 a ha, Real.sq_sqrt hq]
    field_simp
  have hnormv3 : ‖v3‖ ^ 2
      = ((x1 + x3 - x5) / (2 * x1)) ^ 2 * ‖v1‖ ^ 2
        + ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) ^ 2 *
          ‖cross3 v1 (cross3 v1 v2)‖ ^ 2 := by
    rw [← hv3]; exact normsq_add_orth_p17 _ _ _ _ (dot_cross3_v1_X_p17 v1 v2)
  have hups135 : upsX x1 x3 x5 = 4 * x1 * x3 - (x1 + x3 - x5) ^ 2 := by
    unfold upsX; ring
  rw [hnormv3, hx1, hwnorm, hbeta, hups135]
  field_simp [h1.ne']
  ring

/-- HOL `EYYPQDW_NORM_V3_V1`: the realisation `‖v3 - v1‖^2 = x5`.
DISCHARGED: the same Cayley algebra as `EYYPQDW_NORMV3_p17`, with the
affine coefficient shifted by one (`(x1+x3-x5)/(2*x1) - 1`); the pieces
telescope against `upsX x1 x3 x5 = 4 * x1 * x3 - (x1 + x3 - x5) ^ 2` to
`x5`. -/
theorem EYYPQDW_NORM_V3_V1_p17 (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
    (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3) :
    ‖v3 - v1‖ ^ 2 = x5 := by
  have hups126 : 0 < upsX x1 x2 x6 :=
    upsX_pos_of_noncollinear_p17 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6
  have hwnorm := normsq_double_cross_p17 v1 v2 x1 x2 x6 hx1 hx2 hx6
  have hbeta : ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) ^ 2
      = upsX x1 x3 x5 / (upsX x1 x2 x6 * x1 ^ 2) := by
    have hq : 0 ≤ upsX x1 x3 x5 / upsX x1 x2 x6 :=
      div_nonneg hups.le hups126.le
    rw [mul_pow, div_pow, SGIN_POW_EQ_p17 a ha, Real.sq_sqrt hq]
    field_simp
  have hshift : v3 - v1 = ((x1 + x3 - x5) / (2 * x1) - 1) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) := by
    rw [← hv3]
    module
  have hnormv5 : ‖v3 - v1‖ ^ 2
      = ((x1 + x3 - x5) / (2 * x1) - 1) ^ 2 * ‖v1‖ ^ 2
        + ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) ^ 2 *
          ‖cross3 v1 (cross3 v1 v2)‖ ^ 2 := by
    rw [hshift]; exact normsq_add_orth_p17 _ _ _ _ (dot_cross3_v1_X_p17 v1 v2)
  have hups135 : upsX x1 x3 x5 = 4 * x1 * x3 - (x1 + x3 - x5) ^ 2 := by
    unfold upsX; ring
  rw [hnormv5, hx1, hwnorm, hbeta, hups135]
  field_simp [h1.ne']
  ring

/-- HOL `EYYPQDW_SCALAR_POS`: the completion flips the cross product by a
positive scalar `a * t` (via the `cross3` linearity kit and the Lagrange
identity; EYYPQDW.hl:188-214). -/
theorem EYYPQDW_SCALAR_POS_p17 (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
    (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3) :
    ∃ t : ℝ, 0 < t ∧ cross3 v3 v1 = (a * t) • cross3 v1 v2 := by
  have hup126 : 0 < upsX x1 x2 x6 :=
    upsX_pos_of_noncollinear_p17 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6
  have hpos : 0 < Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6) :=
    Real.sqrt_pos.mpr (div_pos hups hup126)
  have hx1d : v1 ⬝ᵥ v1 = x1 := (norm_sq_eq_dot v1).symm.trans hx1
  refine ⟨Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6), hpos, ?_⟩
  rw [← hv3, cross3_add_left_p17, cross3_smul_left_p17, cross3_smul_left_p17,
    cross3_self_p17, smul_zero, zero_add, cross3_X_smul_p17, smul_smul, hx1d]
  field_simp [h1.ne']

/-- HOL `v3_defor_v1 a v1 v2 x1 x2 x5 x6 x3` (EYYPQDW.hl:220); the scalar
factors are re-associated into the division rendering of `mkPlanar2`
(LocalAuto1.lean:787), see the head note. -/
noncomputable def v3DeforV1_p17 (a : ℝ) (v1 v2 : V3) (x1 x2 x5 x6 x3 : ℝ) : V3 :=
  ((x1 + x3 - x5) / (2 * x1)) • v1 +
    ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
      cross3 v1 (cross3 v1 v2)

/-- HOL `v3_defor_v2 a x1 x2 x3 x5 x6 v1 v2` (EYYPQDW.hl:222). -/
noncomputable def v3DeforV2_p17 (a x1 x2 x3 x5 x6 : ℝ) (v1 v2 : V3) : V3 :=
  ((x1 + x3 - x5) / (2 * x1)) • v1 +
    ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
      cross3 v1 (cross3 v1 v2)

/-- HOL `LIFT_CONTINUOUS_ATREAL`; `lift` collapses to the identity
(LocalAuto11 convention). -/
theorem LIFT_CONTINUOUS_ATREAL_p17 (x : ℝ) : ContinuousAt (fun x : ℝ => x) x :=
  continuousAt_id

/-- HOL `LIFT_CONTINUOUS_ATREAL_I`. -/
theorem LIFT_CONTINUOUS_ATREAL_I_p17 (x : ℝ) :
    ContinuousAt (fun x : ℝ => (id ∘ id) x) x :=
  continuousAt_id

/-- HOL `EYYPQDW_CONTINUOUS_AT_X`: the completion is continuous in `x3`. -/
theorem EYYPQDW_CONTINUOUS_AT_X_p17 (a : ℝ) (v1 v2 : V3)
    (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5) :
    ContinuousAt (fun x3 => v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 x3) x3 := by
  have hup126 : 0 < upsX x1 x2 x6 :=
    upsX_pos_of_noncollinear_p17 v1 v2 x1 x2 x6 hnc hx1 hx2 hx6
  have hden : (2:ℝ) * x1 ≠ 0 := by linarith
  simp only [v3DeforV1_p17]
  refine ContinuousAt.add ?_ ?_
  · have hnum : ContinuousAt (fun x : ℝ => (x1 + x - x5 : ℝ)) x3 :=
      (continuousAt_const.add continuousAt_id).sub continuousAt_const
    have hden' : ContinuousAt (fun _ : ℝ => ((2:ℝ) * x1)) x3 := continuousAt_const
    exact (hnum.div hden' hden).smul continuousAt_const
  · have hvec : ContinuousAt (fun _ : ℝ => (cross3 v1 (cross3 v1 v2) : V3)) x3 :=
      continuousAt_const
    have hf : ContinuousAt (fun q : ℝ => upsX x1 q x5 / upsX x1 x2 x6) x3 := by
      have hnum2 : ContinuousAt (fun q : ℝ => upsX x1 q x5) x3 := by
        refine Continuous.continuousAt ?_; unfold upsX; fun_prop
      have hden2 : ContinuousAt (fun _ : ℝ => upsX x1 x2 x6) x3 := continuousAt_const
      exact hnum2.div hden2 (ne_of_gt hup126)
    have hsqrt : ContinuousAt
        (fun q : ℝ => Real.sqrt (upsX x1 q x5 / upsX x1 x2 x6)) x3 :=
      (Real.continuous_sqrt.continuousAt).comp hf
    have hscal : ContinuousAt
        (fun q : ℝ => (a / x1) * Real.sqrt (upsX x1 q x5 / upsX x1 x2 x6)) x3 :=
      ContinuousAt.mul continuousAt_const hsqrt
    exact ContinuousAt.smul hscal hvec

/-- HOL `EYYPQDW_CONTINUOUS_AT_V`: the completion is continuous in `v2`. -/
theorem EYYPQDW_CONTINUOUS_AT_V_p17 (a : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) (v1 v2 : V3)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5) :
    ContinuousAt (fun w => v3DeforV2_p17 a x1 x2 x3 x5 x6 v1 w) v2 := by
  simp only [v3DeforV2_p17]
  have hcross : ContinuousAt (fun w : V3 => cross3 v1 (cross3 v1 w)) v2 :=
    (continuousAt_cross3_right_p17 v1 (cross3 v1 v2)).comp
      (continuousAt_cross3_right_p17 v1 v2)
  have hc : ContinuousAt (fun w : V3 => ((x1 + x3 - x5) / (2 * x1)) • v1) v2 :=
    continuousAt_const
  exact ContinuousAt.add hc
    (ContinuousAt.smul
      (f := fun _ : V3 => (a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6))
      continuousAt_const hcross)

/-- HOL `V3_DEFOR_V1_EQV3_DEFOR_V2`. -/
theorem V3_DEFOR_V1_EQV3_DEFOR_V2_p17 (a : ℝ) (v1 v2 : V3) (x1 x2 x5 x6 x3 : ℝ) :
    v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 x3 =
      v3DeforV2_p17 a x1 x2 x3 x5 x6 v1 v2 :=
  rfl

/-- HOL `LIFT_UPS_CONTINUOUS`: `ups_x x1 x2 x6` is continuous in `x2`. -/
theorem LIFT_UPS_CONTINUOUS_p17 (v1 v2 : V3) (x1 x2 x6 : ℝ)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6) :
    ContinuousAt (fun x2 => upsX x1 x2 x6) x2 := by
  refine Continuous.continuousAt ?_
  unfold upsX
  fun_prop

/-- HOL `MK_PLANAR_REP`: `mk_planar2 ... - v0` is exactly the shifted
`v3_defor` shape. -/
theorem MK_PLANAR_REP_p17 (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 a : ℝ) :
    mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 a - v0 =
      ((x1 + x3 - x5) / (2 * x1)) • (v1 - v0) +
        ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
          cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0)) := by
  simp only [mkPlanar2]
  abel

/-- HOL `EYYPQDW` — the master statement.
DISCHARGES: LocalAuto1.EYYPQDW_concl (appendix.hl:1244).
DISCHARGED: the two Cayley norms via `EYYPQDW_NORMV3_p17` /
`EYYPQDW_NORM_V3_V1_p17` at the translated pair `(v1 - v0, v2 - v0)`;
coplanarity because the Lagrange identity makes `cross3 u1 (cross3 u1 u2)`
a `u1, u2`-combination (so `v3` lies in `affineSpan {v0, v1, v2}`); the
`t > 0` witness is the inverse of the square root, the scalar of
`cross3 (v3 - v0) (v1 - v0)` off `cross3 u1 u2` (`cross3_X_smul_p17`).
NEEDS: nothing. -/
theorem EYYPQDW_p17 (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h5 : 0 < x5) (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
    (hx6 : x6 = dist v1 v2 ^ 2)
    (hups : 0 < upsX x1 x3 x5) (hs : s = 1 ∨ s = -1)
    (hv3 : v3 = mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 s) :
    Coplanar ({v0, v1, v2, v3} : Set V3) ∧
      x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧
      ∃ t : ℝ, 0 < t ∧
        t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0) := by
  have hnc0 : ¬ Collinear ℝ ({0, v1 - v0, v2 - v0} : Set V3) := fun hc =>
    hnc ((collinear_transable_p17 v0 v1 v2).mpr hc)
  have hx1' : ‖v1 - v0‖ ^ 2 = x1 := by rw [hx1, dist_eq_norm]
  have hx2' : ‖v2 - v0‖ ^ 2 = x2 := by rw [hx2, dist_eq_norm]
  have hx6' : ‖v1 - v0 - (v2 - v0)‖ ^ 2 = x6 := by
    have hsimp : (v1 - v0 : V3) - (v2 - v0) = v1 - v2 := by abel
    rw [hsimp, ← dist_eq_norm]; exact hx6.symm
  have hsM : s ∈ ({-1, 1} : Set ℝ) := by
    rcases hs with rfl | rfl <;> simp
  have hrep := MK_PLANAR_REP_p17 v0 v1 v2 x1 x2 x3 x5 x6 s
  rw [← hv3] at hrep
  have hn3 : ‖v3 - v0‖ ^ 2 = x3 :=
    EYYPQDW_NORMV3_p17 (v1 - v0) (v2 - v0) (v3 - v0) x1 x2 x3 1 x5 x6 s
      h1 h2 h3 one_pos h5 h6 hnc0 hx1' hx2' hx6' hsM hups hrep.symm
  have hn5 : ‖v3 - v0 - (v1 - v0)‖ ^ 2 = x5 :=
    EYYPQDW_NORM_V3_V1_p17 (v1 - v0) (v2 - v0) (v3 - v0) x1 x2 x3 1 x5 x6 s
      h1 h2 h3 one_pos h5 h6 hnc0 hx1' hx2' hx6' hsM hups hrep.symm
  have hden126 : 0 < upsX x1 x2 x6 :=
    upsX_pos_of_noncollinear_p17 (v1 - v0) (v2 - v0) x1 x2 x6 hnc0 hx1' hx2' hx6'
  have hK : 0 < Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6) :=
    Real.sqrt_pos.mpr (div_pos hups hden126)
  -- coplanarity: v3 lies in the plane of {v0, v1, v2}
  have hcop : Coplanar ({v0, v1, v2, v3} : Set V3) := by
    have h1m : (v1 : V3) ∈ ({v0, v1, v2} : Set V3) := by simp
    have h0m : (v0 : V3) ∈ ({v0, v1, v2} : Set V3) := by simp
    have h2m : (v2 : V3) ∈ ({v0, v1, v2} : Set V3) := by simp
    have hu1 : ((v1 - v0 : V3)) ∈ vectorSpan ℝ ({v0, v1, v2} : Set V3) := by
      have h := vsub_mem_vectorSpan (k := ℝ) (p₁ := (v1 : V3)) (p₂ := (v0 : V3)) h1m h0m
      simpa using h
    have hu2 : ((v2 - v0 : V3)) ∈ vectorSpan ℝ ({v0, v1, v2} : Set V3) := by
      have h := vsub_mem_vectorSpan (k := ℝ) (p₁ := (v2 : V3)) (p₂ := (v0 : V3)) h2m h0m
      simpa using h
    have hw : (cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0)) : V3)
        ∈ vectorSpan ℝ ({v0, v1, v2} : Set V3) := by
      rw [cross3_lagrange_p17]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu1) (Submodule.smul_mem _ _ hu2)
    have hv3m : ((v3 - v0 : V3)) ∈ vectorSpan ℝ ({v0, v1, v2} : Set V3) := by
      rw [hrep]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu1) (Submodule.smul_mem _ _ hw)
    have h0mem : (v0 : V3) ∈ (affineSpan ℝ ({v0, v1, v2} : Set V3) : Set V3) :=
      mem_affineSpan ℝ (by simp)
    have hv3mem := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan h0mem hv3m
    refine ⟨v0, v1, v2, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · simpa using hv3mem
  refine ⟨hcop, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]; exact hn3.symm
  · have hacom : (v3 - v0 : V3) - (v1 - v0) = v3 - v1 := by abel
    have hsub : ‖v3 - v1‖ = ‖v3 - v0 - (v1 - v0)‖ := by rw [← hacom]
    rw [dist_eq_norm, hsub]; exact hn5.symm
  · -- the scalar off the cross product: t = (square root)⁻¹
    have h11 : WithLp.ofLp (v1 - v0) ⬝ᵥ WithLp.ofLp (v1 - v0) = x1 := by
      rw [← norm_sq_eq_dot (v1 - v0)]; exact hx1'
    have hcross : cross3 (v3 - v0) (v1 - v0)
        = (s * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
          cross3 (v1 - v0) (v2 - v0) := by
      rw [hrep, cross3_add_left_p17, cross3_smul_left_p17, cross3_smul_left_p17,
        cross3_self_p17, smul_zero, zero_add, cross3_X_smul_p17, h11, smul_smul]
      field_simp
    refine ⟨(Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6))⁻¹, inv_pos.mpr hK, ?_⟩
    rw [hcross, smul_smul]
    field_simp

/-- HOL `MK_PLANAR_V3_DEFOR_V1`. -/
theorem MK_PLANAR_V3_DEFOR_V1_p17 (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 a : ℝ) :
    mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 a - v0 =
      v3DeforV1_p17 a (v1 - v0) (v2 - v0) x1 x2 x5 x6 x3 :=
  MK_PLANAR_REP_p17 v0 v1 v2 x1 x2 x3 x5 x6 a

/-- HOL `MK_PLANAR_V3_DEFOR_V1_FUN`. -/
theorem MK_PLANAR_V3_DEFOR_V1_FUN_p17 (v0 v1 v2 : V3) (x1 x2 x5 x6 s : ℝ) :
    (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) =
      (fun x3 => v3DeforV1_p17 s (v1 - v0) (v2 - v0) x1 x2 x5 x6 x3 + v0) := by
  funext q
  exact sub_eq_iff_eq_add.mp (MK_PLANAR_V3_DEFOR_V1_p17 v0 v1 v2 x1 x2 q x5 x6 s)

/-- HOL `EYYPQDW2`: continuity in `x3` of the `mk_planar2` slice.
DISCHARGES: LocalAuto1.EYYPQDW2_concl (appendix.hl:1259). -/
theorem EYYPQDW2_p17 (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h5 : 0 < x5) (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
    (hx6 : x6 = dist v1 v2 ^ 2)
    (hups : 0 < upsX x1 x3 x5) (hs : s = 1 ∨ s = -1) :
    ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3 := by
  have hfun := MK_PLANAR_V3_DEFOR_V1_FUN_p17 v0 v1 v2 x1 x2 x5 x6 s
  rw [hfun]
  have hnc0 : ¬ Collinear ℝ ({0, v1 - v0, v2 - v0} : Set V3) := fun hc =>
    hnc ((collinear_transable_p17 v0 v1 v2).mpr hc)
  have hx1' : ‖v1 - v0‖ ^ 2 = x1 := by rw [hx1, dist_eq_norm]
  have hx2' : ‖v2 - v0‖ ^ 2 = x2 := by rw [hx2, dist_eq_norm]
  have hx6' : ‖(v1 - v0) - (v2 - v0)‖ ^ 2 = x6 := by
    rw [sub_sub_sub_cancel_right, hx6, dist_eq_norm]
  have hsgn : s ∈ ({-1, 1} : Set ℝ) := by
    rcases hs with h | h
    · exact Or.inr h
    · exact Or.inl h
  exact ContinuousAt.add
    (EYYPQDW_CONTINUOUS_AT_X_p17 s (v1 - v0) (v2 - v0) x1 x2 x3 1 x5 x6
      h1 h2 h3 one_pos h5 h6 hnc0 hx1' hx2' hx6' hsgn hups) continuousAt_const

/-- HOL `MK_PLANAR_V3_DEFOR_V2_FUN`. -/
theorem MK_PLANAR_V3_DEFOR_V2_FUN_p17 (v0 v1 : V3) (x1 x2 x3 x5 x6 s : ℝ) :
    (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) =
      (fun v2 => v3DeforV2_p17 s x1 x2 x3 x5 x6 (v1 - v0) (v2 - v0) + v0) := by
  funext q
  have h := MK_PLANAR_V3_DEFOR_V1_p17 v0 v1 q x1 x2 x3 x5 x6 s
  rw [v3DeforV1_p17] at h
  rw [v3DeforV2_p17]
  exact sub_eq_iff_eq_add.mp h

/-- HOL `lemma30000`: the `v2 ↦ v2 - v0` precomposition shape. -/
theorem lemma30000_p17 (s x3 x5 : ℝ) (v0 v1 v2 : V3) :
    (fun v2' => v3DeforV2_p17 s (‖v1 - v0‖ ^ 2) (‖v2 - v0‖ ^ 2) x3 x5
        (‖v1 - v2‖ ^ 2) (v1 - v0) (v2' - v0)) =
      (fun v2' => v3DeforV2_p17 s (‖v1 - v0‖ ^ 2) (‖v2 - v0‖ ^ 2) x3 x5
        (‖v1 - v2‖ ^ 2) (v1 - v0) v2') ∘ fun v2 : V3 => v2 - v0 :=
  rfl

/-- HOL `EYYPQDW3`: continuity in `v2` of the `mk_planar2` slice.
DISCHARGES: LocalAuto1.EYYPQDW3_concl (appendix.hl:1268). -/
theorem EYYPQDW3_p17 (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h5 : 0 < x5) (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
    (hx6 : x6 = dist v1 v2 ^ 2)
    (hups : 0 < upsX x1 x3 x5) (hs : s = 1 ∨ s = -1) :
    ContinuousAt (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) v2 := by
  have hfun := MK_PLANAR_V3_DEFOR_V2_FUN_p17 v0 v1 x1 x2 x3 x5 x6 s
  rw [hfun]
  have hnc0 : ¬ Collinear ℝ ({0, v1 - v0, v2 - v0} : Set V3) := fun hc =>
    hnc ((collinear_transable_p17 v0 v1 v2).mpr hc)
  have hx1' : ‖v1 - v0‖ ^ 2 = x1 := by rw [hx1, dist_eq_norm]
  have hx2' : ‖v2 - v0‖ ^ 2 = x2 := by rw [hx2, dist_eq_norm]
  have hx6' : ‖(v1 - v0) - (v2 - v0)‖ ^ 2 = x6 := by
    rw [sub_sub_sub_cancel_right, hx6, dist_eq_norm]
  have hsub : ContinuousAt (fun w : V3 => w - v0) v2 :=
    ContinuousAt.sub continuousAt_id continuousAt_const
  have hsgn : s ∈ ({-1, 1} : Set ℝ) := by
    rcases hs with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcomp : ContinuousAt
      (fun w : V3 => v3DeforV2_p17 s x1 x2 x3 x5 x6 (v1 - v0) (w - v0)) v2 :=
    ContinuousAt.comp
      (g := fun u : V3 => v3DeforV2_p17 s x1 x2 x3 x5 x6 (v1 - v0) u)
      (f := fun w : V3 => w - v0)
      (EYYPQDW_CONTINUOUS_AT_V_p17 s x1 x2 x3 1 x5 x6 (v1 - v0) (v2 - v0)
        h1 h2 h3 one_pos h5 h6 hnc0 hx1' hx2' hx6' hsgn hups) hsub
  exact ContinuousAt.add hcomp continuousAt_const

/-! ## Section C: YRTAFYH — diagonal stabilisation arithmetic -/

/-- HOL `SUR_MOD_FUN`: the shift `i` sending `p` to `p'` mod `k`. -/
theorem SUR_MOD_FUN_p17 (k p p' : ℕ) (hk : k ≠ 0) :
    ∃ i : ℕ, (i + p) % k = p' % k := by
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  have hp := Nat.mod_lt p hk'
  have hp' := Nat.mod_lt p' hk'
  refine ⟨p' % k + k - p % k, ?_⟩
  have h1 : p % k + k * (p / k) = p := Nat.mod_add_div p k
  have e : p' % k + k - p % k + p = p' % k + (k + k * (p / k)) := by omega
  have e2 : k + k * (p / k) = k * (1 + p / k) := by rw [mul_add, mul_one]
  rw [e, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp']

/-- HOL `TRANS_DIAG` (first version, EYYPQDW-side arithmetic). -/
theorem TRANS_DIAG_p17 (k i p p' q q' : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q') :
    (i + q) % k = q' % k := by
  have h4 : (p + (i + q)) % k = (p + q') % k := by
    rw [← Nat.add_assoc, Nat.add_comm p i, Nat.add_mod (i + p) q k, h1,
      ← Nat.add_mod p' q k, h2]
  exact mod_add_cancel_p17 k p (i + q) q' hk h4

/-- HOL `scs_components` (already PROVED in LocalAuto1.lean:258 as `rfl`;
re-stated `_p17` for the module inventory). -/
theorem scs_components_p17 (s : ScsV39) :
    ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str = s :=
  scs_components s

/-- HOL `scs_inj` (already PROVED in LocalAuto1.lean:619; re-stated `_p17`
for the module inventory). -/
theorem scs_inj_p17 (s s' : ScsV39) (h1 : scsBasicV39 s) (h1' : scsBasicV39 s')
    (hd : s.d = s'.d) (hk : s.k = s'.k) (ha : s.a = s'.a) (hb : s.b = s'.b) :
    s = s' :=
  scs_inj s s' h1 h1' hd hk ha hb

/-- HOL `DIAG_PSORT1`. -/
theorem DIAG_PSORT1_p17 (k i p i' j q' q : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q')
    (h3 : psort k (i', j) = psort k (p, q)) :
    psort k (i + i', i + j) = psort k (p', q') := by
  rw [psort_pair_eq_p17] at h3
  rcases h3 with hc | hc
  · have e1 : (i + i') % k = p' % k := (mod_congr_add_p17 k i i' p hc.1).trans h1
    have e2 : (i + j) % k = q' % k :=
      (mod_congr_add_p17 k i j q hc.2).trans (TRANS_DIAG_p17 k i p p' q q' hk h1 h2)
    rw [psort_pair_eq_p17]
    exact Or.inl ⟨e1, e2⟩
  · have e1 : (i + i') % k = q' % k :=
      (mod_congr_add_p17 k i i' q hc.1).trans
        (TRANS_DIAG_p17 k i p p' q q' hk h1 h2)
    have e2 : (i + j) % k = p' % k := (mod_congr_add_p17 k i j p hc.2).trans h1
    rw [psort_pair_eq_p17]
    exact Or.inr ⟨e1, e2⟩

/-- HOL `DIAG_PSORT2`. -/
theorem DIAG_PSORT2_p17 (k i p i' j q' q : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q')
    (h3 : psort k (i + i', i + j) = psort k (p', q')) :
    psort k (i', j) = psort k (p, q) := by
  rw [psort_pair_eq_p17] at h3
  rcases h3 with hc | hc
  · have e1 : i' % k = p % k :=
      mod_add_cancel_p17 k i i' p hk (hc.1.trans h1.symm)
    have e2 : j % k = q % k :=
      mod_add_cancel_p17 k i j q hk
        (hc.2.trans (TRANS_DIAG_p17 k i p p' q q' hk h1 h2).symm)
    rw [psort_pair_eq_p17]
    exact Or.inl ⟨e1, e2⟩
  · have e1 : i' % k = q % k :=
      mod_add_cancel_p17 k i i' q hk
        (hc.1.trans (TRANS_DIAG_p17 k i p p' q q' hk h1 h2).symm)
    have e2 : j % k = p % k := mod_add_cancel_p17 k i j p hk (hc.2.trans h1.symm)
    rw [psort_pair_eq_p17]
    exact Or.inr ⟨e1, e2⟩

/-- HOL `DIAG_PSORT`. -/
theorem DIAG_PSORT_p17 (k i p i' j q' q : ℕ) (hk : k ≠ 0)
    (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q') :
    (psort k (i + i', i + j) = psort k (p', q')) ↔
      (psort k (i', j) = psort k (p, q)) :=
  ⟨fun h => DIAG_PSORT2_p17 k i p i' j q' q hk h1 h2 h,
    fun h => DIAG_PSORT1_p17 k i p i' j q' q hk h1 h2 h⟩

/-- HOL `TRANS_DIAG` (second version of the same-named source theorem,
YRTAFYH.hl:311): `scs_diag` is invariant under the cyclic shift. -/
theorem TRANS_DIAG_SCS_p17 (k i' i j : ℕ) (hk : k ≠ 0) :
    scsDiag k i' j ↔ scsDiag k (i + i') (i + j) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun hc => h1 (mod_add_cancel_p17 k i i' j hk hc),
      fun hc => h2 (mod_add_cancel_p17 k i (i' + 1) j hk hc),
      fun hc => h3 (mod_add_cancel_p17 k i i' (j + 1) hk hc)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun hc => h1 (mod_congr_add_p17 k i i' j hc),
      fun hc => h2 (mod_congr_add_p17 k i (i' + 1) j hc),
      fun hc => h3 (mod_congr_add_p17 k i i' (j + 1) hc)⟩

/-- HOL `A_EQ_PSORT`: `scs_a_v39` only sees the `psort`-sorted mod pair. -/
theorem A_EQ_PSORT_p17 (s : ScsV39) (i j p q : ℕ) (his : isScsV39 s)
    (h : psort s.k (i, j) = psort s.k (p, q)) : s.a i j = s.a p q := by
  obtain ⟨hd, hk1, hk2, -, -, -, -, hperA, -, -, hperB, -, hsym, -, hdiag0, -, -, -, -, -⟩ :=
    his
  have hred := periodic2_mod_p17 hperA
  rw [psort_pair_eq_p17] at h
  rcases h with hc | hc
  · rw [(hred i j).symm, hc.1, hc.2, hred p q]
  · rw [(hred i j).symm, hc.1, hc.2, (hsym (q % s.k) (p % s.k)).1, hred p q]

/-- HOL `B_EQ_PSORT`. -/
theorem B_EQ_PSORT_p17 (s : ScsV39) (i j p q : ℕ) (his : isScsV39 s)
    (h : psort s.k (i, j) = psort s.k (p, q)) : s.b i j = s.b p q := by
  obtain ⟨hd, hk1, hk2, -, -, -, -, hperA, -, -, hperB, -, hsym, -, hdiag0, -, -, -, -, -⟩ :=
    his
  have hred := periodic2_mod_p17 hperB
  have hsymB : ∀ i j : ℕ, s.b i j = s.b j i := fun i j => (hsym i j).2.2.2.1
  rw [psort_pair_eq_p17] at h
  rcases h with hc | hc
  · rw [(hred i j).symm, hc.1, hc.2, hred p q]
  · rw [(hred i j).symm, hc.1, hc.2, hsymB (q % s.k) (p % s.k), hred p q]

/-- HOL `PROPERTY_OF_K_SCS`. -/
theorem PROPERTY_OF_K_SCS_p17 (s : ScsV39) (his : isScsV39 s) :
    s.k ≠ 0 ∧ 0 < s.k ∧ 1 < s.k ∧ 2 < s.k := by
  have hk := his.2.1
  omega

/-- HOL `PSORT_PERIODIC`. -/
theorem PSORT_PERIODIC_p17 (k i j : ℕ) (hk : k ≠ 0) :
    psort k (i + k, j) = psort k (i, j) ∧ psort k (i, j + k) = psort k (i, j) := by
  have h1 : (i + k) % k = i % k := Nat.add_mod_right i k
  have h2 : (j + k) % k = j % k := Nat.add_mod_right j k
  simp only [psort, h1, h2]
  trivial

/-- HOL `DIAG_NOT_PSORT`: a diagonal pair is never the `psort` of a vertex
and its successor. -/
theorem DIAG_NOT_PSORT_p17 (k i j : ℕ) (hk : k ≠ 0) (hd : scsDiag k i j)
    (i' : ℕ) : ¬ (psort k (i, j) = psort k (i', i' + 1)) := by
  intro heq
  obtain ⟨h1, h2, h3⟩ := hd
  rcases Nat.lt_or_ge k 2 with hk1 | hk1
  · have hk1' : k = 1 := by omega
    subst hk1'
    exact absurd (show i % 1 = j % 1 from
      (Nat.mod_one i).trans (Nat.mod_one j).symm) h1
  have hone : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hstep : (i' + 1) % k = (i' % k + 1) % k := by
    rw [Nat.add_mod, hone]
  rw [psort_pair_eq_p17] at heq
  rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hj : j % k = (i % k + 1) % k := by rw [e2, hstep, ← e1]
    exact h2 (by rw [Nat.add_mod, hone, hj])
  · have hi : i % k = (j % k + 1) % k := by rw [e1, hstep, e2]
    exact h3 (by rw [Nat.add_mod, hone, hi])

/-! ## SWEEP-A17 private kit for `YRTAFYH_p17` (all `private`, `swa`-prefixed)

Slot-level bookkeeping for the diagonal-stabilised record `scsStabDiagV39 s i j`
= `mkUnadornedV39 s.k s.d s.a b'` with `b' i' j' = if psort s.k (i, j) =
psort s.k (i', j') then cstab else s.b i' j'`: the record only re-points the
`b`/`bm` fields at the diagonal `psort`-class, so every `is_scs_v39` conjunct
transfers from `s`, with the diagonal class patched to `cstab`. -/

/-- `cstab` is below 4 (decimal crutch; `cstab = 3.01` by rfl). -/
private theorem swa_cstab_lt_four_p17 : cstab < 4 := by
  have h : cstab = 3.01 := rfl
  rw [h]; norm_num

/-- Slot evaluator for the staged `b'` of `scsStabDiagV39`: membership in the
diagonal `psort`-class of `(i, j)` decides `cstab` vs. the untouched `s.b`. -/
private theorem swa_bprime_app_p17 (s : ScsV39) (i j i' j' : ℕ) :
    (scsStabDiagV39 s i j).b i' j' =
      if psort s.k (i, j) = psort s.k (i', j') then cstab else s.b i' j' :=
  rfl

/-- `psort` discards `+ k` shifts of either coordinate. -/
private theorem swa_psort_add_right_p17 (k x y : ℕ) :
    psort k (x + k, y) = psort k (x, y) ∧ psort k (x, y + k) = psort k (x, y) := by
  constructor
  · exact psort_pair_eq_p17 k (x + k) y x y |>.mpr
      (Or.inl ⟨Nat.add_mod_right x k, rfl⟩)
  · exact psort_pair_eq_p17 k x (y + k) x y |>.mpr
      (Or.inl ⟨rfl, Nat.add_mod_right y k⟩)

/-- The staged `b'` is `k`-periodic in both coordinates. -/
private theorem swa_bprime_periodic_p17 (s : ScsV39) (i j : ℕ)
    (hpb : Periodic2 s.b s.k) (x y : ℕ) :
    (scsStabDiagV39 s i j).b (x + s.k) y = (scsStabDiagV39 s i j).b x y ∧
      (scsStabDiagV39 s i j).b x (y + s.k) = (scsStabDiagV39 s i j).b x y := by
  obtain ⟨hps1, hps2⟩ := swa_psort_add_right_p17 s.k x y
  refine ⟨?_, ?_⟩
  · rw [swa_bprime_app_p17 s i j (x + s.k) y, swa_bprime_app_p17 s i j x y]
    by_cases hc : psort s.k (i, j) = psort s.k (x, y)
    · rw [if_pos (hc.trans hps1.symm), if_pos hc]
    · rw [if_neg (fun hcon => hc (hcon.trans hps1)), if_neg hc, (hpb x y).1]
  · rw [swa_bprime_app_p17 s i j x (y + s.k), swa_bprime_app_p17 s i j x y]
    by_cases hc : psort s.k (i, j) = psort s.k (x, y)
    · rw [if_pos (hc.trans hps2.symm), if_pos hc]
    · rw [if_neg (fun hcon => hc (hcon.trans hps2)), if_neg hc, (hpb x y).2]

/-- The staged `b'` is symmetric. -/
private theorem swa_bprime_sym_p17 (s : ScsV39) (i j x y : ℕ)
    (hsb : ∀ u v : ℕ, s.b u v = s.b v u) :
    (scsStabDiagV39 s i j).b x y = (scsStabDiagV39 s i j).b y x := by
  have hswap : psort s.k (x, y) = psort s.k (y, x) :=
    psort_pair_eq_p17 s.k x y y x |>.mpr (Or.inr ⟨rfl, rfl⟩)
  rw [swa_bprime_app_p17 s i j x y, swa_bprime_app_p17 s i j y x]
  by_cases hc : psort s.k (i, j) = psort s.k (x, y)
  · rw [if_pos hc, if_pos (hc.trans hswap)]
  · rw [if_neg hc, if_neg (fun hcon => hc (hcon.trans hswap.symm)), hsb]

/-- The `a <= b'` chain slot: on the diagonal class it is exactly the hypothesis
`s.a i j <= cstab` transported through `A_EQ_PSORT_p17`; off the class it is
the untouched chain of `s`. -/
private theorem swa_chain_p17 (s : ScsV39) (i j x y : ℕ) (his : isScsV39 s)
    (hch : ∀ u v : ℕ, s.a u v ≤ s.am u v ∧ s.am u v ≤ s.bm u v ∧ s.bm u v ≤ s.b u v)
    (hac : s.a i j ≤ cstab) :
    s.a x y ≤ (scsStabDiagV39 s i j).b x y := by
  rw [swa_bprime_app_p17]
  by_cases hc : psort s.k (i, j) = psort s.k (x, y)
  · rw [if_pos hc, A_EQ_PSORT_p17 s x y i j his hc.symm]
    exact hac
  · rw [if_neg hc]
    exact (hch x y).1.trans ((hch x y).2.1.trans (hch x y).2.2)

/-- Adjacent slots of the staged `b'` carry either `cstab` or the untouched
`s.b` value. -/
private theorem swa_adj_b_p17 (s : ScsV39) (i j x : ℕ) :
    (scsStabDiagV39 s i j).b x (x + 1) = cstab ∨
      (scsStabDiagV39 s i j).b x (x + 1) = s.b x (x + 1) := by
  rw [swa_bprime_app_p17]
  by_cases hc : psort s.k (i, j) = psort s.k (x, x + 1)
  · rw [if_pos hc]; exact Or.inl rfl
  · rw [if_neg hc]; exact Or.inr rfl

/-- The card set of the stabilised record coincides with that of `s`: a
diagonal `psort`-class never meets an adjacent slot (`DIAG_NOT_PSORT_p17`), so
every adjacent value is the untouched `s.b`. -/
private theorem swa_card_p17 (s : ScsV39) (i j : ℕ) (hk0 : s.k ≠ 0)
    (hdiag : scsDiag s.k i j) :
    {x | x < (scsStabDiagV39 s i j).k ∧ (2 * h0 < (scsStabDiagV39 s i j).b x (x + 1) ∨
        2 < (scsStabDiagV39 s i j).a x (x + 1))} =
      {x | x < s.k ∧ (2 * h0 < s.b x (x + 1) ∨ 2 < s.a x (x + 1))} := by
  refine Set.ext (fun x => ?_)
  simp only [Set.mem_setOf_eq]
  rw [swa_bprime_app_p17, if_neg (DIAG_NOT_PSORT_p17 s.k i j hk0 hdiag x)]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- HOL `YRTAFYH`: stabilising a diagonal with `a i j <= cstab` preserves
`is_scs_v39` and `scs_basic_v39`.
DISCHARGES: LocalAuto1.YRTAFYH_concl (appendix.hl:1554).
DISCHARGED (sweep-a17-22): the 20-conjunct case tree of YRTAFYH.hl:430-496 is
assembled below via the private `swa_*` kit (the `A_EQ_PSORT` /
`DIAG_NOT_PSORT` splits included); standalone audit:
`#print axioms Kepler.Text.YRTAFYH_p17` = [propext, choice, Quot.sound]. -/
theorem YRTAFYH_p17 : ∀ (s : ScsV39) (i j : ℕ), isScsV39 s → scsBasicV39 s →
    3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j) := by
  intro s i j his hbas hk hdiag hac
  have hcopy := his
  obtain ⟨hd, hk1, hk2, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, hdiag0, h2a,
    hb3, hbc, -, -, hcard⟩ := hcopy
  have hk0 : s.k ≠ 0 := by omega
  have hsb : ∀ u v : ℕ, s.b u v = s.b v u := fun u v => (hsym u v).2.2.2.1
  refine ⟨⟨hd, hk1, hk2, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    hpa, hpa, fun x y => swa_bprime_periodic_p17 s i j hpb x y,
    fun x y => swa_bprime_periodic_p17 s i j hpb x y, fun x y => ⟨rfl, rfl⟩,
    fun x y => ⟨(hsym x y).1, (hsym x y).1, swa_bprime_sym_p17 s i j x y hsb,
      swa_bprime_sym_p17 s i j x y hsb, rfl⟩,
    fun x y => ⟨le_refl _, swa_chain_p17 s i j x y his hch hac, le_refl _⟩,
    hdiag0, h2a, ?_, ?_, fun x y hj => hj.elim, fun x y hj => hj.elim, ?_⟩,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun x y => rfl⟩⟩
  · intro x h3
    rcases swa_adj_b_p17 s i j x with he | he
    · rw [he]; exact swa_cstab_lt_four_p17
    · rw [he]; exact hb3 x h3
  · intro x h3k
    rcases swa_adj_b_p17 s i j x with he | he
    · rw [he]
    · rw [he]; exact hbc x h3k
  · rw [swa_card_p17 s i j hk0 hdiag]
    exact hcard

/-- HOL `STAB_IS_SCS` (YRTAFYH.hl:500): the `is_scs_v39` half of `YRTAFYH`,
derived from it exactly as `SIMP_TAC [YRTAFYH]` does. -/
theorem STAB_IS_SCS_p17 (s : ScsV39) (i j : ℕ) (his : isScsV39 s)
    (hbas : scsBasicV39 s) (hk : 3 < s.k) (hdiag : scsDiag s.k i j)
    (ha : s.a i j ≤ cstab) : isScsV39 (scsStabDiagV39 s i j) :=
  (YRTAFYH_p17 s i j his hbas hk hdiag ha).1

/-! ## Section D: deformation — the fan-deformation path machinery -/

/-- HOL `conic s` (no corpus port; verbatim: `!c x. &0 <= c /\ x IN s ==>
c % x IN s`). -/
def conicP17 (s : Set V3) : Prop := ∀ t : ℝ, ∀ x ∈ s, 0 ≤ t → t • x ∈ s

/-- HOL `COMPACT_SPHERE_0`. -/
theorem COMPACT_SPHERE_0_p17 (a : ℝ) : IsCompact {x : V3 | ‖x‖ = a} := by
  have h : {x : V3 | ‖x‖ = a} = Metric.sphere (0 : V3) a := by
    ext x
    simp [Metric.mem_sphere, dist_zero_right]
  rw [h]
  exact isCompact_sphere _ _


private theorem w_xrq17_one_sided_separation (c d : Set V3) (hc : conicP17 c)
    (hcc : IsClosed c) (hd : conicP17 d) (hdc : IsClosed d)
    (hint : c ∩ d ⊆ ({0} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ c, ∀ y ∈ d, e * ‖x‖ ≤ dist x y := by
  classical
  by_cases hdne : d = ∅
  · exact ⟨1, one_pos, fun x hx y hy => absurd hy (by rw [hdne]; exact Set.notMem_empty y)⟩
  have hdne' : d.Nonempty := Set.nonempty_iff_ne_empty.mpr hdne
  by_cases hKne : c ∩ Metric.sphere (0:V3) 1 = ∅
  · refine ⟨1, one_pos, fun x hx y hy => ?_⟩
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, mul_zero]; exact dist_nonneg
    · exfalso
      have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have hmem : (‖x‖⁻¹) • x ∈ c ∩ Metric.sphere (0:V3) 1 := by
        constructor
        · exact hc (‖x‖⁻¹) x hx (inv_nonneg.mpr (norm_nonneg x))
        · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hxn]
      rw [hKne] at hmem
      exact Set.notMem_empty _ hmem
  · obtain ⟨x0, hx0K⟩ := Set.nonempty_iff_ne_empty.mpr hKne
    have hK : IsCompact (c ∩ Metric.sphere (0:V3) 1) :=
      IsCompact.of_isClosed_subset (isCompact_sphere (0:V3) 1)
        (hcc.inter Metric.isClosed_sphere) Set.inter_subset_right
    have hcont : Continuous fun x : V3 => Metric.infDist x d := Metric.continuous_infDist_pt d
    obtain ⟨xm, hxmK, hmin⟩ :=
      hK.exists_isMinOn ⟨x0, hx0K⟩ hcont.continuousOn
    have hxm_notd : xm ∉ d := by
      intro hxmd
      have hxd0 : xm = 0 := by
        have hmem : xm ∈ c ∩ d := ⟨hxmK.1, hxmd⟩
        have h0 := hint hmem
        simpa using h0
      have hsp := hxmK.2
      rw [Metric.mem_sphere, hxd0, dist_self] at hsp
      norm_num at hsp
    have hpos : 0 < Metric.infDist xm d :=
      (Metric.infDist_pos_iff_notMem_closure hdne').mp (by
        rw [hdc.closure_eq]; exact hxm_notd)
    refine ⟨Metric.infDist xm d, hpos, fun x hx y hy => ?_⟩
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, mul_zero]; exact dist_nonneg
    · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have hxs : (‖x‖⁻¹) • x ∈ c ∩ Metric.sphere (0:V3) 1 := by
        constructor
        · exact hc (‖x‖⁻¹) x hx (inv_nonneg.mpr (norm_nonneg x))
        · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hxn]
      have hy'd : (‖x‖⁻¹) • y ∈ d :=
        hd (‖x‖⁻¹) y hy (inv_nonneg.mpr (norm_nonneg x))
      have h1 : Metric.infDist ((‖x‖⁻¹) • x) d
          ≤ dist ((‖x‖⁻¹) • x) ((‖x‖⁻¹) • y) :=
        Metric.infDist_le_dist_of_mem hy'd
      have h2 : Metric.infDist xm d ≤ Metric.infDist ((‖x‖⁻¹) • x) d := hmin hxs
      have h3 : dist ((‖x‖⁻¹) • x) ((‖x‖⁻¹) • y) = ‖x‖⁻¹ * dist x y := by
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
      have h4 : Metric.infDist xm d ≤ ‖x‖⁻¹ * dist x y := h2.trans (h1.trans_eq h3)
      calc Metric.infDist xm d * ‖x‖ ≤ (‖x‖⁻¹ * dist x y) * ‖x‖ :=
            mul_le_mul_of_nonneg_right h4 (norm_nonneg x)
        _ = dist x y := by
            field_simp

/-- HOL `SEPARATE_CLOSED_CONES`: two closed cones meeting only at the origin
are linearly separated. NEEDS: the compact-sphere separation argument of
deformation.hl:26-76 (SEPARATE_COMPACT_CLOSED + conic rescaling). -/
theorem SEPARATE_CLOSED_CONES_p17 (c d : Set V3) (hc : conicP17 c)
    (hcc : IsClosed c) (hd : conicP17 d) (hdc : IsClosed d)
    (hint : c ∩ d ⊆ ({0} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ c, ∀ y ∈ d, dist x y ≥ e * max ‖x‖ ‖y‖ := by
  obtain ⟨e1, he1, h1⟩ := w_xrq17_one_sided_separation c d hc hcc hd hdc hint
  obtain ⟨e2, he2, h2⟩ := w_xrq17_one_sided_separation d c hd hdc hc hcc
    (by
      intro z hz
      exact hint (by rwa [Set.inter_comm] at hz))
  refine ⟨min e1 e2, lt_min he1 he2, fun x hx y hy => ?_⟩
  have hx1 : min e1 e2 * ‖x‖ ≤ dist x y :=
    le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg x)) (h1 x hx y hy)
  have hy1 : min e1 e2 * ‖y‖ ≤ dist y x :=
    le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg y)) (h2 y hy x hx)
  have hy2 : min e1 e2 * ‖y‖ ≤ dist x y := by rwa [dist_comm] at hy1
  calc min e1 e2 * max ‖x‖ ‖y‖
      = max (min e1 e2 * ‖x‖) (min e1 e2 * ‖y‖) :=
        mul_max_of_nonneg _ _ (le_of_lt (lt_min he1 he2))
    _ ≤ dist x y := max_le hx1 hy2

/-- HOL `AFF_GE_1_1_0`: the half-line cone on one point. -/
theorem AFF_GE_1_1_0_p17 (v : V3) (hv : v ≠ (0:V3)) :
    affGe ({0} : Set V3) {v} = {y : V3 | ∃ t : ℝ, 0 ≤ t ∧ y = t • v} := by
  ext y
  have hnotv : (0:V3) ∉ ({v} : Finset V3) := by simp [Ne.symm hv]
  have hset : ∀ h : ((({0} : Set V3) ∪ {v} : Set V3)).Finite,
      h.toFinset = ({0, v} : Finset V3) := by
    intro h
    ext u
    simp [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  unfold affGe Affsign
  constructor
  · rintro ⟨f, hfin, hy, hsgn, hsum⟩
    rw [hset hfin] at hy hsum
    rw [Finset.sum_insert hnotv, Finset.sum_singleton] at hsum
    rw [Finset.sum_insert hnotv, Finset.sum_singleton, smul_zero, zero_add] at hy
    exact ⟨f v, hsgn v (by simp), hy⟩
  · rintro ⟨t, ht, hy⟩
    have hfin0 : (({0} : Set V3) ∪ {v} : Set V3).Finite :=
      Set.Finite.union (by simp) (by simp)
    refine ⟨fun u => if u = v then t else 1 - t, hfin0, ?_, ?_, ?_⟩
    · rw [hset hfin0, Finset.sum_insert hnotv, Finset.sum_singleton]
      show y = (if (0:V3) = v then t else 1 - t) • 0 +
        (if v = v then t else 1 - t) • v
      rw [if_neg (show ¬((0:V3) = v) from Ne.symm hv), if_pos rfl, smul_zero,
        zero_add]
      exact hy
    · intro u hu
      simp only [Set.mem_singleton_iff] at hu
      subst hu
      simp only [if_pos rfl]
      exact ht
    · rw [hset hfin0, Finset.sum_insert hnotv, Finset.sum_singleton]
      show (if (0:V3) = v then t else 1 - t) + (if v = v then t else 1 - t) = 1
      rw [if_neg (show ¬((0:V3) = v) from Ne.symm hv), if_pos rfl]
      ring

/-- HOL `AFF_GE_1_2_0`: the two-point `aff_ge` cone. -/
theorem AFF_GE_1_2_0_p17 (v w : V3) (hv : v ≠ (0:V3)) (hw : w ≠ (0:V3)) :
    affGe ({0} : Set V3) {v, w} =
      {y : V3 | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ y = a • v + b • w} := by
  ext y
  by_cases hvw : v = w
  · have hset : ({v, w} : Set V3) = {v} := by rw [hvw]; simp
    have hray : affGe ({0} : Set V3) {v, w} =
        {y : V3 | ∃ t : ℝ, 0 ≤ t ∧ y = t • v} := by
      rw [hset]; exact AFF_GE_1_1_0_p17 v hv
    rw [hray]
    constructor
    · rintro ⟨t, ht, hy⟩
      exact ⟨t, 0, ht, le_refl _, by rw [hy, zero_smul, add_zero]⟩
    · rintro ⟨a, b, ha, hb, hy⟩
      exact ⟨a + b, by linarith, by rw [hy, hvw]; module⟩
  · have hnot0 : (0:V3) ∉ insert v ({w} : Finset V3) := by
      simp [Ne.symm hv, Ne.symm hw]
    have hnotv : v ∉ ({w} : Finset V3) := by simp [hvw]
    have hset : ∀ h : ((({0} : Set V3) ∪ {v, w} : Set V3)).Finite,
        h.toFinset = ({0, v, w} : Finset V3) := by
      intro h
      ext u
      simp [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    unfold affGe Affsign
    constructor
    · rintro ⟨f, hfin, hy, hsgn, hsum⟩
      rw [hset hfin] at hy hsum
      rw [Finset.sum_insert hnot0, Finset.sum_insert hnotv,
        Finset.sum_singleton] at hsum
      rw [Finset.sum_insert hnot0, Finset.sum_insert hnotv, Finset.sum_singleton,
        smul_zero, zero_add] at hy
      exact ⟨f v, f w, hsgn v (by simp), hsgn w (by simp), hy⟩
    · rintro ⟨a, b, ha, hb, hy⟩
      have hfin0 : (({0} : Set V3) ∪ {v, w} : Set V3).Finite :=
        Set.Finite.union (by simp) (by simp)
      refine ⟨fun u => if u = v then a else if u = w then b else 1 - a - b,
        hfin0, ?_, ?_, ?_⟩
      · rw [hset hfin0, Finset.sum_insert hnot0, Finset.sum_insert hnotv,
          Finset.sum_singleton]
        simp only []
        rw [if_neg (show ¬((0:V3) = v) from Ne.symm hv),
          if_neg (show ¬((0:V3) = w) from Ne.symm hw),
          if_pos (trivial : True),
          if_neg (show ¬(w = v) from fun he => hvw he.symm),
          if_pos (trivial : True), smul_zero, zero_add]
        exact hy
      · intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with huv | huv
        · simp only []
          rw [if_pos huv]
          exact ha
        · simp only []
          rw [if_neg (show ¬(u = v) from fun he => hvw (he.symm.trans huv)),
            if_pos huv]
          exact hb
      · rw [hset hfin0, Finset.sum_insert hnot0, Finset.sum_insert hnotv,
          Finset.sum_singleton]
        simp only []
        rw [if_neg (show ¬((0:V3) = v) from Ne.symm hv),
          if_neg (show ¬((0:V3) = w) from Ne.symm hw),
          if_pos (trivial : True),
          if_neg (show ¬(w = v) from fun he => hvw he.symm),
          if_pos (trivial : True)]
        ring
/-- HOL `CONIC_AFF_GE_0`: `aff_ge {vec 0} s` is a cone for finite `s` away
from the origin. -/
theorem CONIC_AFF_GE_0_p17 (s : Set V3) (hfin : s.Finite) (h0 : (0:V3) ∉ s) :
    conicP17 (affGe ({0} : Set V3) s) := by
  intro c x hx hc0
  classical
  obtain ⟨f, hfin2, hxv, hsgn, hsum⟩ := hx
  set E := hfin.toFinset with hEdef
  set F := hfin2.toFinset with hFdef
  have hEs : ∀ u ∈ E, u ∈ s := by
    intro u hu
    have hu' : u ∈ s := by simpa [hEdef] using hu
    exact hu'
  have hEg : ∀ u ∈ E, (if u ∈ s then c * f u else 1 - c * ∑ w ∈ E, f w) = c * f u := by
    intro u hu
    rw [if_pos (hEs u hu)]
  have hFE : F.erase 0 = E := by
    ext u
    simp only [Finset.mem_erase, hFdef, Set.Finite.mem_toFinset, Set.mem_union,
      Set.mem_singleton_iff, hEdef, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hne, hmem⟩
      rcases hmem with hmem | hmem
      · exact absurd hmem hne
      · exact hmem
    · intro hmem
      refine ⟨fun he => ?_, Or.inr hmem⟩
      rw [he] at hmem
      exact h0 hmem
  have h0mem : (0:V3) ∈ F := by simp [hFdef]
  have hF0 : F = insert 0 (F.erase 0) := (Finset.insert_erase h0mem).symm
  have hnotE : (0:V3) ∉ E := by simp [hEdef, h0]
  have hxvE : x = ∑ w ∈ E, f w • w := by
    rw [hF0, hFE] at hxv
    rw [Finset.sum_insert hnotE, smul_zero, zero_add] at hxv
    exact hxv
  refine ⟨fun u => if u ∈ s then c * f u else 1 - c * ∑ w ∈ E, f w, hfin2, ?_, ?_, ?_⟩
  · rw [← hFdef] at ⊢
    rw [hF0, hFE] at hxv ⊢
    rw [Finset.sum_insert hnotE]
    simp only []
    rw [if_neg h0, smul_zero, zero_add]
    have hgg : ∑ w ∈ E,
        (fun u => if u ∈ s then c * f u else 1 - c * ∑ w' ∈ E, f w') w • w =
        c • ∑ w ∈ E, f w • w := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun w hw => by
        simp only [hEg w hw, smul_smul]
    rw [hgg, ← hxvE]
  · intro u hu
    simp only []
    rw [if_pos hu]
    exact mul_nonneg hc0 (hsgn u hu)
  · have hEsum : ∑ w ∈ E,
        (fun u => if u ∈ s then c * f u else 1 - c * ∑ w' ∈ E, f w') w
        = ∑ w ∈ E, c * f w :=
      Finset.sum_congr rfl fun w hw => by
        show (if w ∈ s then c * f w else 1 - c * ∑ w' ∈ E, f w') = c * f w
        rw [hEg w hw]
    rw [← hFdef] at ⊢
    rw [hF0, hFE]
    rw [Finset.sum_insert hnotE, if_neg h0, hEsum, Finset.mul_sum]
    ring

/-! ### W1 (xrecqns-w1 lane): private kit for the deformation tower. -/

private theorem w_xrq17_affGe_empty (x : V3) : affGe {x} (∅ : Set V3) = {x} := by
  ext y
  simp only [affGe, Set.mem_setOf_eq, Affsign, Set.mem_singleton_iff]
  constructor
  · rintro ⟨f, hfin, hsum, -, hone⟩
    have hTeq : hfin.toFinset = ({x} : Finset V3) := by ext z; simp
    rw [hTeq, Finset.sum_singleton] at hsum hone
    rw [hsum, hone, one_smul]
  · intro heq
    rw [heq]
    have hfin : ({x} ∪ (∅ : Set V3)).Finite :=
      (Set.finite_singleton x).union Set.finite_empty
    have hTeq : hfin.toFinset = ({x} : Finset V3) := by ext z; simp
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [hTeq]; simp
    · intro z hz; simp at hz
    · rw [hTeq]; simp

private theorem w_xrq17_affGe_mono_right {x : V3} {S T : Set V3} (hST : S ⊆ T)
    (hfin : ({x} ∪ T : Set V3).Finite) (hxT : x ∉ T) :
    affGe {x} S ⊆ affGe {x} T := by
  intro y hy
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hy ⊢
  obtain ⟨f, hS, hyv, hpos, hsum⟩ := hy
  have hsub : ({x} ∪ S : Set V3) ⊆ {x} ∪ T := by
    intro z hz
    simp only [Set.mem_union] at hz ⊢
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (hST h)
  have hsubfin : hS.toFinset ⊆ hfin.toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact hsub hz
  have hgv0 : ∀ z ∈ hfin.toFinset, z ∉ hS.toFinset →
      (if z ∈ ({x} ∪ S : Set V3) then f z else 0) = 0 := by
    intro z hz hzs
    exact if_neg (fun hcon => hzs (by
      simp only [Set.Finite.mem_toFinset]; exact hcon))
  have hgvv : ∀ z ∈ hfin.toFinset, z ∉ hS.toFinset →
      (if z ∈ ({x} ∪ S : Set V3) then f z else 0) • z = 0 := by
    intro z hz hzs
    rw [hgv0 z hz hzs, zero_smul]
  refine ⟨fun z => if z ∈ ({x} ∪ S : Set V3) then f z else 0, hfin, ?_, ?_, ?_⟩
  · show y = ∑ z ∈ hfin.toFinset,
      (if z ∈ ({x} ∪ S : Set V3) then f z else 0) • z
    rw [hyv, ← Finset.sum_subset hsubfin hgvv]
    exact Finset.sum_congr rfl (fun z hz => by
      simp only [Set.Finite.mem_toFinset] at hz
      rw [if_pos hz])
  · intro z hzT
    show 0 ≤ (if z ∈ ({x} ∪ S : Set V3) then f z else 0)
    by_cases hzS : z ∈ ({x} ∪ S : Set V3)
    · rw [if_pos hzS]
      simp only [Set.mem_union] at hzS
      rcases hzS with h | h
      · exact (hxT ((Set.mem_singleton_iff.mp h) ▸ hzT)).elim
      · exact hpos z h
    · rw [if_neg hzS]
  · show ∑ z ∈ hfin.toFinset, (if z ∈ ({x} ∪ S : Set V3) then f z else 0) = 1
    rw [← hsum, ← Finset.sum_subset hsubfin hgv0]
    exact Finset.sum_congr rfl (fun z hz => by
      simp only [Set.Finite.mem_toFinset] at hz
      rw [if_pos hz])

private theorem w_xrq17_ncard_le_two {V : Set V3} {E : Set (Set V3)} (hE : Graph E)
    {e : Set V3} (he : e ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) :
    e.Finite ∧ e.ncard ≤ 2 := by
  rw [Set.mem_union] at he
  rcases he with h | ⟨v, -, rfl⟩
  · obtain ⟨hf, hc⟩ := hE e h
    refine ⟨hf, ?_⟩
    rw [Set.ncard_eq_toFinset_card e hf, hc]
  · exact ⟨Set.finite_singleton v, by simp⟩

private theorem w_xrq17_eq_pair_of_subset {s : Set V3} {a b : V3}
    (hfin : s.Finite) (hcard : s.ncard ≤ 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    s = {a, b} := by
  have h2 : 2 ≤ s.ncard := by
    have hsub : ({a, b} : Set V3) ⊆ s := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ha
      · rw [Set.mem_singleton_iff] at hx
        subst hx; exact hb
    have hfin2 : ({a, b} : Set V3).Finite := (Set.finite_singleton b).insert a
    have h := Set.ncard_le_ncard hsub hfin
    rwa [Set.ncard_pair hab] at h
  have hsub : s ⊆ {a, b} := by
    intro x hx
    by_contra hx'
    have hx'2 : ¬(x = a ∨ x = b) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx'
    have hxne : x ≠ a := fun h => hx'2 (Or.inl h)
    have hxne' : x ≠ b := fun h => hx'2 (Or.inr h)
    have h3 : 3 ≤ s.ncard := by
      have hsub3 : ({a, b, x} : Set V3) ⊆ s := by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact ha
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact hb
        · rw [Set.mem_singleton_iff] at hy
          subst hy; exact hx
      have hfin3 : ({a, b, x} : Set V3).Finite :=
        ((Set.finite_singleton x).insert b).insert a
      have hc3 : ({a, b, x} : Set V3).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨a, b, x, hab, hxne.symm, hxne'.symm, rfl⟩
      have h := Set.ncard_le_ncard hsub3 hfin
      rw [hc3] at h
      omega
    omega
  exact Set.Subset.antisymm hsub (by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx; exact hb)

private theorem w_xrq17_inter_class {V : Set V3} {E : Set (Set V3)} (hE : Graph E)
    {e1 e2 : Set V3} (he1 : e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}})
    (he2 : e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) (hne : e1 ≠ e2) :
    e1 ∩ e2 = ∅ ∨ ∃ v, e1 ∩ e2 = {v} := by
  have h1 := w_xrq17_ncard_le_two hE he1
  have h2 := w_xrq17_ncard_le_two hE he2
  have hfinI : (e1 ∩ e2).Finite := h1.1.subset Set.inter_subset_left
  have hle1 : (e1 ∩ e2).ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff hfinI]
    intro a b ha hb
    by_contra hab
    have hp1 : e1 = {a, b} :=
      w_xrq17_eq_pair_of_subset h1.1 h1.2 (Set.mem_of_mem_inter_left ha)
        (Set.mem_of_mem_inter_left hb) hab
    have hp2 : e2 = {a, b} :=
      w_xrq17_eq_pair_of_subset h2.1 h2.2 (Set.mem_of_mem_inter_right ha)
        (Set.mem_of_mem_inter_right hb) hab
    exact hne (hp1.trans hp2.symm)
  rcases eq_or_ne (e1 ∩ e2) ∅ with hem | hne'
  · exact Or.inl hem
  · right
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    refine ⟨v, ?_⟩
    apply Set.Subset.antisymm
    · intro y hy
      have hyv : y = v := by
        rw [Set.ncard_le_one_iff hfinI] at hle1
        exact hle1 hy hv
      simp [hyv]
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy; exact hv

private theorem w_xrq17_edge_pair {E : Set (Set V3)} (hE : Graph E)
    {e : Set V3} (he : e ∈ E) : ∃ a b : V3, a ≠ b ∧ e = {a, b} := by
  obtain ⟨hf, hc⟩ := hE e he
  have h2 : e.ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card e hf, hc]
  obtain ⟨a, b, hab, heq⟩ := Set.ncard_eq_two.mp h2
  exact ⟨a, b, hab, heq⟩

private theorem w_xrq17_edge_pair_of_mem {E : Set (Set V3)} (hE : Graph E)
    {e : Set V3} (he : e ∈ E) {v : V3} (hv : v ∈ e) :
    ∃ u : V3, u ≠ v ∧ e = {u, v} := by
  obtain ⟨a, b, hab, heq⟩ := w_xrq17_edge_pair hE he
  subst heq
  rcases Set.mem_insert_iff.mp hv with h | h
  · refine ⟨b, ?_, ?_⟩
    · rw [h]; exact hab.symm
    · rw [h, Set.pair_comm]
  · rw [Set.mem_singleton_iff] at h
    refine ⟨a, ?_, ?_⟩
    · rw [h]; exact hab
    · rw [h]


-- main trio

private theorem w_xrq17_GMLWKPK (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
        (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
          (∀ v : V3, e1 ∩ e2 = {v} →
            affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3)) := by
  constructor
  · intro hf7 e1 he1 e2 he2
    have h := hf7 e1 he1 e2 he2
    constructor
    · intro hem
      rw [h, hem, w_xrq17_affGe_empty]
    · intro v hsing
      rw [h, hsing]
  · intro h e1 he1 e2 he2
    by_cases hEq : e1 = e2
    · subst hEq
      rw [Set.inter_self, Set.inter_self]
    · rcases w_xrq17_inter_class hE he1 he2 hEq with hem | ⟨v, hsing⟩
      · rw [(h e1 he1 e2 he2).1 hem, hem, w_xrq17_affGe_empty]
      · rw [(h e1 he1 e2 he2).2 v hsing, hsing]

private theorem w_xrq17_col3_swap {a b c : V3} (h : Collinear3 a b c) : Collinear3 a c b := by
  have hset : ({a, c, b} : Set V3) = {a, b, c} := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  show Collinear ℝ ({a, c, b} : Set V3)
  rw [hset]; exact h

private theorem w_xrq17_mem_affGe_pair_trans {x u v y : V3}
    (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v) :
    y ∈ affGe {x} {u, v} ↔
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ y - x = a • (u - x) + b • (v - x) := by
  have hdisj : Disjoint ({x} : Set V3) {u, v} := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rcases Set.mem_insert_iff.mp hz' with h | h
    · exact hxu h
    · rw [Set.mem_singleton_iff] at h
      exact hxv h
  constructor
  · intro hy
    obtain ⟨t1, t2, t3, ht2, ht3, hsum, hy'⟩ :=
      (mem_affGe_singleton_pair (x := x) (v := u) (w := v) hdisj huv).mp hy
    have ht1 : t1 = 1 - t2 - t3 := by linarith
    refine ⟨t2, t3, ht2, ht3, ?_⟩
    rw [hy', ht1]; module
  · rintro ⟨a, b, ha, hb, hy⟩
    refine (mem_affGe_singleton_pair (x := x) (v := u) (w := v) hdisj huv).mpr
      ⟨1 - a - b, a, b, ha, hb, by ring, ?_⟩
    have h1 : y = (y - x) + x := by abel
    rw [h1, hy]; module

private theorem w_xrq17_mem_affGe_single_trans {x v y : V3} (hxv : x ≠ v) :
    y ∈ affGe {x} {v} ↔ ∃ a : ℝ, 0 ≤ a ∧ y - x = a • (v - x) := by
  constructor
  · intro hy
    obtain ⟨t1, t2, ht2, hsum, hy'⟩ :=
      (mem_affGe_singleton (x := x) (v := v) hxv).mp hy
    refine ⟨t2, ht2, ?_⟩
    have ht1 : t1 = 1 - t2 := by linarith
    rw [hy', ht1]; module
  · rintro ⟨a, ha, hy⟩
    refine (mem_affGe_singleton (x := x) (v := v) hxv).mpr ⟨1 - a, a, ha, by ring, ?_⟩
    have h1 : y = (y - x) + x := by abel
    rw [h1, hy]; module

private theorem w_xrq17_inter_pair_proper_iff {x u v w : V3}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w)
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hnc1 : ¬ Collinear3 x u v) (hnc2 : ¬ Collinear3 x v w) :
    (affGe {x} {u, v} ∩ affGe {x} {v, w} ≠ affGe {x} {v}) ↔
      u ∈ affGe {x} {v, w} ∨ w ∈ affGe {x} {u, v} := by
  constructor
  · intro hne
    have hsub : affGe {x} {v} ⊆ affGe {x} {u, v} ∩ affGe {x} {v, w} := by
      intro y hy
      refine ⟨?_, ?_⟩
      · exact w_xrq17_affGe_mono_right (S := ({v} : Set V3)) (T := ({u, v} : Set V3))
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp)
          ((Set.finite_singleton x).union ((Set.finite_singleton v).insert u))
          (by simp [hxu, hxv]) hy
      · exact w_xrq17_affGe_mono_right (S := ({v} : Set V3)) (T := ({v, w} : Set V3))
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; simp)
          ((Set.finite_singleton x).union ((Set.finite_singleton w).insert v))
          (by simp [hxv, hxw]) hy
    have hnotsub : ¬ (affGe {x} {u, v} ∩ affGe {x} {v, w} ⊆ affGe {x} {v}) := by
      intro hs
      exact hne (Set.Subset.antisymm hs hsub)
    obtain ⟨y, hy, hyv⟩ := Set.not_subset.mp hnotsub
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨a, b, ha, hb, hya⟩ :=
      (w_xrq17_mem_affGe_pair_trans hxu hxv huv).mp hy1
    obtain ⟨c, d, hc, hd, hyb⟩ :=
      (w_xrq17_mem_affGe_pair_trans hxv hxw hvw).mp hy2
    have hane : a ≠ 0 := by
      intro h0
      apply hyv
      rw [h0, zero_smul, zero_add] at hya
      exact (w_xrq17_mem_affGe_single_trans hxv).mpr ⟨b, hb, hya⟩
    have hdne : d ≠ 0 := by
      intro h0
      apply hyv
      rw [h0, zero_smul, add_zero] at hyb
      exact (w_xrq17_mem_affGe_single_trans hxv).mpr ⟨c, hc, hyb⟩
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hane)
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdne)
    have hkey : a • (u - x) = (c - b) • (v - x) + d • (w - x) := by
      have h := hya.symm.trans hyb
      calc a • (u - x) = (a • (u - x) + b • (v - x)) - b • (v - x) := by abel
        _ = (c • (v - x) + d • (w - x)) - b • (v - x) := by rw [h]
        _ = (c - b) • (v - x) + d • (w - x) := by module
    rcases le_total b c with hbc | hcb
    · left
      refine (w_xrq17_mem_affGe_pair_trans hxv hxw hvw).mpr
        ⟨a⁻¹ * (c - b), a⁻¹ * d,
          mul_nonneg (le_of_lt (inv_pos.mpr hapos)) (by linarith),
          mul_nonneg (le_of_lt (inv_pos.mpr hapos)) hd, ?_⟩
      have h := congrArg (fun z => a⁻¹ • z) hkey
      rw [smul_add, smul_smul, smul_smul, smul_smul,
        inv_mul_cancel₀ hane, one_smul] at h
      exact h
    · right
      refine (w_xrq17_mem_affGe_pair_trans hxu hxv huv).mpr
        ⟨d⁻¹ * a, d⁻¹ * (b - c),
          mul_nonneg (le_of_lt (inv_pos.mpr hdpos)) ha,
          mul_nonneg (le_of_lt (inv_pos.mpr hdpos)) (by linarith), ?_⟩
      have h := congrArg (fun z => d⁻¹ • z) hkey
      rw [smul_add, smul_smul, smul_smul, smul_smul,
        inv_mul_cancel₀ hdne, one_smul] at h
      have h' : w - x = (d⁻¹ * a) • (u - x) - (d⁻¹ * (c - b)) • (v - x) := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact h.symm
      have hcoef : (d⁻¹ * (b - c)) • (v - x) = -((d⁻¹ * (c - b)) • (v - x)) := by
        rw [← neg_smul]
        congr 1
        ring
      rw [hcoef, ← sub_eq_add_neg]
      exact h'
  · rintro (hu | hw)
    · intro heq
      have hu1 : u ∈ affGe {x} {u, v} := by
        have hdisj : Disjoint ({x} : Set V3) {u, v} := by
          rw [Set.disjoint_left]
          intro z hz hz'
          rw [Set.mem_singleton_iff] at hz
          subst hz
          rcases Set.mem_insert_iff.mp hz' with h | h
          · exact hxu h
          · rw [Set.mem_singleton_iff] at h
            exact hxv h
        exact (mem_affGe_singleton_pair (x := x) (v := u) (w := v) hdisj huv).mpr
          ⟨0, 1, 0, by norm_num, by norm_num, by ring, by simp⟩
      have hmem : u ∈ affGe {x} {u, v} ∩ affGe {x} {v, w} := ⟨hu1, hu⟩
      rw [heq] at hmem
      have huray : u ∈ affGe {x} {v} := hmem
      obtain ⟨t, ht, htu⟩ := (w_xrq17_mem_affGe_single_trans hxv).mp huray
      have hcol : Collinear3 x v u :=
        (collinear3_iff_smul (v := x) (w := v) (w1 := u) hxv.symm).mpr ⟨t, htu⟩
      exact hnc1 (w_xrq17_col3_swap hcol)
    · intro heq
      have hw1 : w ∈ affGe {x} {v, w} := by
        have hdisj : Disjoint ({x} : Set V3) {v, w} := by
          rw [Set.disjoint_left]
          intro z hz hz'
          rw [Set.mem_singleton_iff] at hz
          subst hz
          rcases Set.mem_insert_iff.mp hz' with h | h
          · exact hxv h
          · rw [Set.mem_singleton_iff] at h
            exact hxw h
        exact (mem_affGe_singleton_pair (x := x) (v := v) (w := w) hdisj hvw).mpr
          ⟨0, 0, 1, by norm_num, by norm_num, by ring, by simp⟩
      have hmem : w ∈ affGe {x} {u, v} ∩ affGe {x} {v, w} := ⟨hw, hw1⟩
      rw [heq] at hmem
      have hwray : w ∈ affGe {x} {v} := hmem
      obtain ⟨t, ht, htw⟩ := (w_xrq17_mem_affGe_single_trans hxv).mp hwray
      have hcol : Collinear3 x v w :=
        (collinear3_iff_smul (v := x) (w := v) (w1 := w) hxv.symm).mpr ⟨t, htw⟩
      exact hnc2 hcol

end Kepler.Text

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical


private theorem w_xrq17_GMLWKPK_ALT (x : V3) (V : Set V3) (E : Set (Set V3))
    (hE : Graph E) (hx : ∀ e ∈ E, x ∉ e) :
    fan7 x V E ↔
      ((∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
        (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
          affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3))) := by
  rw [w_xrq17_GMLWKPK x V E hE]
  constructor
  · intro h
    exact ⟨fun e1 he1 e2 he2 => (h e1 he1 e2 he2).1,
      fun e1 he1 e2 he2 v hv => (h e1 (Set.mem_union_left _ he1) e2
        (Set.mem_union_left _ he2)).2 v hv⟩
  · rintro ⟨h0, h1⟩ e1 he1 e2 he2
    constructor
    · exact h0 e1 he1 e2 he2
    · intro v hsing
      rw [Set.mem_union] at he1 he2
      rcases he1 with hE1 | ⟨a, ha, rfl⟩
      · rcases he2 with hE2 | ⟨b, hb, rfl⟩
        · exact h1 e1 hE1 e2 hE2 v hsing
        · -- e2 = {b}
          have hvb : v = b := by
            have hmem : v ∈ e1 ∩ ({b} : Set V3) := by
              rw [hsing]; exact Set.mem_singleton v
            exact hmem.2
          have hb1 : b ∈ e1 := by
            have hmem : b ∈ e1 ∩ ({b} : Set V3) := by
              rw [hsing]
              rw [← hvb]
              exact Set.mem_singleton v
            exact hmem.1
          rw [hvb]
          apply Set.Subset.antisymm
          · exact Set.inter_subset_right
          · intro y hy
            have hfin1 : ({x} ∪ e1 : Set V3).Finite := by
              obtain ⟨hf, -⟩ := hE e1 hE1
              exact (Set.finite_singleton x).union hf
            exact ⟨w_xrq17_affGe_mono_right (S := ({b} : Set V3)) (T := e1)
              (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hb1)
              hfin1 (hx e1 hE1) hy, hy⟩
      · -- e1 = {a}
        rcases he2 with hE2 | ⟨b, hb, rfl⟩
        · have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ e2 := by
              rw [hsing]; exact Set.mem_singleton v
            exact hmem.1
          have ha2 : a ∈ e2 := by
            have hmem : a ∈ ({a} : Set V3) ∩ e2 := by
              rw [hsing]
              rw [← hva]
              exact Set.mem_singleton v
            exact hmem.2
          rw [hva]
          apply Set.Subset.antisymm
          · exact Set.inter_subset_left
          · intro y hy
            have hfin2 : ({x} ∪ e2 : Set V3).Finite := by
              obtain ⟨hf, -⟩ := hE e2 hE2
              exact (Set.finite_singleton x).union hf
            exact ⟨hy, w_xrq17_affGe_mono_right (S := ({a} : Set V3)) (T := e2)
              (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact ha2)
              hfin2 (hx e2 hE2) hy⟩
        · -- both singletons
          have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ ({b} : Set V3) := by
              rw [hsing]; exact Set.mem_singleton v
            exact hmem.1
          have hvb : v = b := by
            have hmem : v ∈ ({a} : Set V3) ∩ ({b} : Set V3) := by
              rw [hsing]; exact Set.mem_singleton v
            exact hmem.2
          rw [← hva, ← hvb, Set.inter_self]

private theorem w_xrq17_GMLWKPK_SIMPLE (V : Set V3) (E : Set (Set V3)) (x : V3)
    (hsup : ⋃₀ E ⊆ V) (hE : Graph E) (h6 : fan6 x V E)
    (hx : ∀ e ∈ E, x ∉ e) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
        e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3) := by
  rw [w_xrq17_GMLWKPK x V E hE]
  constructor
  · intro h e1 he1 e2 he2
    exact (h e1 he1 e2 he2).1
  · intro h0 e1 he1 e2 he2
    constructor
    · exact h0 e1 he1 e2 he2
    · intro v hsing
      rw [Set.mem_union] at he1 he2
      rcases he1 with hE1 | ⟨a, ha, rfl⟩
      · rcases he2 with hE2 | ⟨b, hb, rfl⟩
        · -- both edges
          have hv1 : v ∈ e1 := by
            have hmem : v ∈ e1 ∩ e2 := by rw [hsing]; exact Set.mem_singleton v
            exact hmem.1
          have hv2 : v ∈ e2 := by
            have hmem : v ∈ e1 ∩ e2 := by rw [hsing]; exact Set.mem_singleton v
            exact hmem.2
          obtain ⟨u, huv, he1u⟩ := w_xrq17_edge_pair_of_mem hE hE1 hv1
          obtain ⟨w, hvw, he2w⟩ := w_xrq17_edge_pair_of_mem hE hE2 hv2
          have hne : e1 ≠ e2 := by
            intro heq
            have h2 : e1.ncard = 2 := by
              obtain ⟨hf, hc⟩ := hE e1 hE1
              rw [Set.ncard_eq_toFinset_card e1 hf, hc]
            have hsingle : e1 = ({v} : Set V3) := by
              rw [← heq, Set.inter_self] at hsing
              exact hsing
            rw [hsingle] at h2
            simp at h2
          have huw : u ≠ w := by
            intro huw
            apply hne
            rw [he1u, he2w, huw]
          have hxue : x ∉ e1 := hx e1 hE1
          have hxwe : x ∉ e2 := hx e2 hE2
          have hxu : x ≠ u := by
            intro h
            apply hxue
            rw [he1u, h]
            simp
          have hxv : x ≠ v := by
            intro h
            apply hxue
            rw [he1u, h]
            simp
          have hxw : x ≠ w := by
            intro h
            apply hxwe
            rw [he2w, h]
            simp
          have hnc1 : ¬ Collinear3 x u v := by
            intro hc
            apply h6 e1 hE1
            have hset : (insert x ({u, v} : Set V3)) = ({x, u, v} : Set V3) := by
              ext z
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            rw [he1u, hset]
            exact hc
          have hnc2 : ¬ Collinear3 x v w := by
            intro hc
            apply h6 e2 hE2
            have hset : (insert x ({w, v} : Set V3)) = ({x, v, w} : Set V3) := by
              ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
            rw [he2w, hset]
            have hc' : Collinear ℝ ({x, v, w} : Set V3) := hc
            exact hc'
          have huV : u ∈ V :=
            hsup (Set.subset_sUnion_of_mem hE1 (by rw [he1u]; simp))
          have hwV : w ∈ V :=
            hsup (Set.subset_sUnion_of_mem hE2 (by rw [he2w]; simp))
          have hdisj_uw : ({u} : Set V3) ∩ {v, w} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            obtain ⟨hz1, hz2⟩ := hz
            rw [Set.mem_singleton_iff] at hz1
            rw [hz1] at hz2
            rcases Set.mem_insert_iff.mp hz2 with h | h
            · exact huv h
            · rw [Set.mem_singleton_iff] at h
              exact huw h
          have hdisj_wu : ({w} : Set V3) ∩ {u, v} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            obtain ⟨hz1, hz2⟩ := hz
            rw [Set.mem_singleton_iff] at hz1
            rw [hz1] at hz2
            rcases Set.mem_insert_iff.mp hz2 with h | h
            · exact huw h.symm
            · rw [Set.mem_singleton_iff] at h
              exact hvw h
          have hdisj_uw2 : ({u} : Set V3) ∩ e2 = ∅ := by
            rw [he2w, Set.pair_comm w v]
            exact hdisj_uw
          have hdisj_wu2 : ({w} : Set V3) ∩ e1 = ∅ := by
            rw [he1u]
            exact hdisj_wu
          have hu_in : u ∈ affGe {x} {u} := by
            refine (mem_affGe_singleton (x := x) (v := u) hxu).mpr
              ⟨0, 1, by norm_num, by norm_num, by simp⟩
          have hw_in : w ∈ affGe {x} {w} := by
            refine (mem_affGe_singleton (x := x) (v := w) hxw).mpr
              ⟨0, 1, by norm_num, by norm_num, by simp⟩
          have hnu : u ∉ affGe {x} {v, w} := by
            intro hu
            have hempty := h0 {u} (Set.mem_union_right _ ⟨u, huV, rfl⟩) e2
              (Set.mem_union_left _ hE2) hdisj_uw2
            have hmem : u ∈ affGe {x} {u} ∩ affGe {x} e2 := by
              refine ⟨hu_in, ?_⟩
              rw [he2w, Set.pair_comm w v]
              exact hu
            rw [hempty] at hmem
            exact hxu hmem.symm
          have hnw : w ∉ affGe {x} {u, v} := by
            intro hw
            have hempty := h0 {w} (Set.mem_union_right _ ⟨w, hwV, rfl⟩) e1
              (Set.mem_union_left _ hE1) hdisj_wu2
            have hmem : w ∈ affGe {x} {w} ∩ affGe {x} e1 := by
              refine ⟨hw_in, ?_⟩
              rw [he1u]
              exact hw
            rw [hempty] at hmem
            exact hxw hmem.symm
          have hproper := w_xrq17_inter_pair_proper_iff hxu hxv hxw huv hvw.symm huw hnc1 hnc2
          have hres : affGe {x} {u, v} ∩ affGe {x} {v, w} = affGe {x} {v} := by
            by_contra hne'
            rcases hproper.mp hne' with h | h
            · exact hnu h
            · exact hnw h
          rw [he1u, he2w, Set.pair_comm w v]
          exact hres
        · -- e2 singleton
          have hvb : v = b := by
            have hmem : v ∈ e1 ∩ ({b} : Set V3) := by rw [hsing]; exact Set.mem_singleton v
            exact hmem.2
          have hb1 : b ∈ e1 := by
            have hmem : b ∈ e1 ∩ ({b} : Set V3) := by
              rw [hsing]; rw [← hvb]; exact Set.mem_singleton v
            exact hmem.1
          rw [hvb]
          apply Set.Subset.antisymm
          · exact Set.inter_subset_right
          · intro y hy
            have hfin1 : ({x} ∪ e1 : Set V3).Finite := by
              obtain ⟨hf, -⟩ := hE e1 hE1
              exact (Set.finite_singleton x).union hf
            exact ⟨w_xrq17_affGe_mono_right (S := ({b} : Set V3)) (T := e1)
              (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hb1)
              hfin1 (hx e1 hE1) hy, hy⟩
      · -- e1 singleton
        rcases he2 with hE2 | ⟨b, hb, rfl⟩
        · have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ e2 := by rw [hsing]; exact Set.mem_singleton v
            exact hmem.1
          have ha2 : a ∈ e2 := by
            have hmem : a ∈ ({a} : Set V3) ∩ e2 := by
              rw [hsing]; rw [← hva]; exact Set.mem_singleton v
            exact hmem.2
          rw [hva]
          apply Set.Subset.antisymm
          · exact Set.inter_subset_left
          · intro y hy
            have hfin2 : ({x} ∪ e2 : Set V3).Finite := by
              obtain ⟨hf, -⟩ := hE e2 hE2
              exact (Set.finite_singleton x).union hf
            exact ⟨hy, w_xrq17_affGe_mono_right (S := ({a} : Set V3)) (T := e2)
              (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact ha2)
              hfin2 (hx e2 hE2) hy⟩
        · have hva : v = a := by
            have hmem : v ∈ ({a} : Set V3) ∩ ({b} : Set V3) := by
              rw [hsing]; exact Set.mem_singleton v
            exact hmem.1
          have hvb : v = b := by
            have hmem : v ∈ ({a} : Set V3) ∩ ({b} : Set V3) := by
              rw [hsing]; exact Set.mem_singleton v
            exact hmem.2
          rw [← hva, ← hvb, Set.inter_self]

/-- HOL `GMLWKPK`: `fan7` re-characterised pairwise over edges and singleton
vertices. NEEDS: the `AFF_GE_EQ_AFFINE_HULL` singleton case-kit
(deformation.hl:118-152). -/
theorem GMLWKPK_p17 (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
        (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
          (∀ v : V3, e1 ∩ e2 = {v} →
            affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3)) := w_xrq17_GMLWKPK x V E hE

/-- HOL `GMLWKPK_ALT`: with `x` off every edge the singleton-pair case is
needed only for edges. NEEDS: deformation.hl:154-185. -/
theorem GMLWKPK_ALT_p17 (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E)
    (hx : ∀ e ∈ E, x ∉ e) :
    fan7 x V E ↔
      ((∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
        (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
          affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3))) := w_xrq17_GMLWKPK_ALT x V E hE hx

/-- HOL `GMLWKPK_SIMPLE`: under `fan6` + covering, `fan7` reduces to the
empty-intersection case. NEEDS: the 4-point collinearity lemma at
deformation.hl:196-271 plus the case bash to deformation.hl:376. -/
theorem GMLWKPK_SIMPLE_p17 (V : Set V3) (E : Set (Set V3)) (x : V3)
    (hsup : ⋃₀ E ⊆ V) (hE : Graph E) (h6 : fan6 x V E)
    (hx : ∀ e ∈ E, x ∉ e) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
        e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3) := w_xrq17_GMLWKPK_SIMPLE V E x hsup hE h6 hx

/-- HOL `lemma_1`: the one-ray perturbation estimate (the scale-invariance
argument of deformation.hl:382-401). -/
theorem lemma_1_p17 (x : V3) (e : ℝ) (hx : x ≠ (0:V3)) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ x' : V3, dist x x' < d →
      ∀ z' ∈ affGe ({0} : Set V3) {x'}, ∃ z ∈ affGe ({0} : Set V3) {x},
        ‖z' - z‖ ≤ e * ‖z‖ := by
  refine ⟨e * ‖x‖, mul_pos he (norm_pos_iff.mpr hx), fun x' hx' z' hz' => ?_⟩
  have hxAEx : ∀ u : V3, u ≠ 0 → ∀ w ∈ affGe ({0} : Set V3) ({u} : Set V3),
      ∃ t : ℝ, 0 ≤ t ∧ w = t • u := fun u hu w hw => by
    have h := AFF_GE_1_1_0_p17 u hu
    rw [h] at hw
    exact hw
  by_cases hx'0 : x' = 0
  · -- `x' = 0`: the cone is `{0}`; `z' = 0`, take `z = 0`
    have hz0 : z' = 0 := by
      obtain ⟨f, hfin, hzv, -, hz1⟩ := hz'
      have hset : hfin.toFinset = {0} := by
        ext w
        by_cases w = 0 <;>
          simp [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
            hx'0, hz1]
      rw [hset] at hzv
      simpa using hzv
    refine ⟨0, ?_, by simp [hz0]⟩
    rw [AFF_GE_1_1_0_p17 x hx]
    exact ⟨0, le_refl 0, by simp⟩
  · obtain ⟨t, ht, rfl⟩ := hxAEx x' hx'0 z' hz'
    refine ⟨t • x, ?_, ?_⟩
    rw [AFF_GE_1_1_0_p17 x hx]
    exact ⟨t, ht, rfl⟩
    have hrev : ‖t • x' - t • x‖ = t * ‖x - x'‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, norm_sub_rev]
    rw [hrev, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    refine mul_le_mul_of_nonneg_left (le_of_lt hx') ht |>.trans (le_of_eq ?_)
    ring


private theorem w_xrq17_norm_cross_le (u v : V3) : ‖cross3 u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h := InnerProductGeometry.norm_toLp_symm_crossProduct
    (a := ((u : V3) : Fin 3 → ℝ)) (b := ((v : V3) : Fin 3 → ℝ))
  have hL : cross3 u v =
      (WithLp.toLp 2 (crossProduct ((u : V3) : Fin 3 → ℝ) ((v : V3) : Fin 3 → ℝ)) : V3) := rfl
  rw [hL, h]
  simp only [WithLp.toLp_ofLp]
  calc ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v)
      ≤ ‖u‖ * ‖v‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one _) (mul_nonneg (norm_nonneg u) (norm_nonneg v))
    _ = ‖u‖ * ‖v‖ := by rw [mul_one]

private theorem w_xrq17_cross3_add_right (a b c : V3) :
    cross3 a (b + c) = cross3 a b + cross3 a c := by
  have h := cross3_anticomm_p17 a (b + c)
  rw [cross3_add_left_p17, cross3_anticomm_p17 b a, cross3_anticomm_p17 c a] at h
  rw [h]; abel

private theorem w_xrq17_cross3_smul_right (t : ℝ) (a b : V3) :
    cross3 a (t • b) = t • cross3 a b := by
  have h := cross3_anticomm_p17 a (t • b)
  rw [cross3_smul_left_p17, cross3_anticomm_p17 b a] at h
  rw [h, smul_neg, neg_neg]

private theorem w_xrq17_lower_bound {x y : V3} (hx : x ≠ 0) (hy : y ≠ 0)
    (hnc : ¬ Collinear ℝ ({0, x, y} : Set V3)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖cross3 x y‖ / max ‖x‖ ‖y‖ * max a b ≤ ‖a • x + b • y‖ := by
  have hmaxpos : 0 < max ‖x‖ ‖y‖ := lt_max_of_lt_left (norm_pos_iff.mpr hx)
  have hcrosspos : 0 < ‖cross3 x y‖ := by
    rw [norm_pos_iff]
    exact cross3_ne_zero_p17 hnc
  have h1 : cross3 x (a • x + b • y) = b • cross3 x y := by
    rw [w_xrq17_cross3_add_right, w_xrq17_cross3_smul_right, w_xrq17_cross3_smul_right,
      cross3_self_p17, smul_zero, zero_add]
  have h2 : cross3 (a • x + b • y) y = a • cross3 x y := by
    rw [cross3_anticomm_p17, w_xrq17_cross3_add_right, w_xrq17_cross3_smul_right,
      w_xrq17_cross3_smul_right, cross3_self_p17, smul_zero, add_zero,
      cross3_anticomm_p17, smul_neg, neg_neg]
  have hb1 : b * ‖cross3 x y‖ ≤ ‖x‖ * ‖a • x + b • y‖ := by
    calc b * ‖cross3 x y‖ = ‖b • cross3 x y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      _ = ‖cross3 x (a • x + b • y)‖ := by rw [h1]
      _ ≤ ‖x‖ * ‖a • x + b • y‖ := w_xrq17_norm_cross_le x _
  have ha1 : a * ‖cross3 x y‖ ≤ ‖a • x + b • y‖ * ‖y‖ := by
    calc a * ‖cross3 x y‖ = ‖a • cross3 x y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      _ = ‖cross3 (a • x + b • y) y‖ := by rw [h2]
      _ ≤ ‖a • x + b • y‖ * ‖y‖ := w_xrq17_norm_cross_le _ y
  rcases le_total a b with hle | hle
  · have hm : max a b = b := max_eq_right hle
    rw [hm, div_mul_eq_mul_div, div_le_iff₀ hmaxpos]
    calc ‖cross3 x y‖ * b = b * ‖cross3 x y‖ := by ring
      _ ≤ ‖x‖ * ‖a • x + b • y‖ := hb1
      _ ≤ max ‖x‖ ‖y‖ * ‖a • x + b • y‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ = ‖a • x + b • y‖ * max ‖x‖ ‖y‖ := by ring
  · have hm : max a b = a := max_eq_left hle
    rw [hm, div_mul_eq_mul_div, div_le_iff₀ hmaxpos]
    calc ‖cross3 x y‖ * a = a * ‖cross3 x y‖ := by ring
      _ ≤ ‖a • x + b • y‖ * ‖y‖ := ha1
      _ ≤ ‖a • x + b • y‖ * max ‖x‖ ‖y‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
      _ = ‖a • x + b • y‖ * max ‖x‖ ‖y‖ := rfl

/-- HOL `lemma_2`: the two-ray perturbation estimate.
NEEDS: deformation.hl:403-466 (LINEAR_INJECTIVE_BOUNDED_BELOW_POS). -/
theorem lemma_2_p17 (x y : V3) (e : ℝ)
    (hnc : ¬ Collinear ℝ ({0, x, y} : Set V3)) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ x' y' : V3, dist x x' < d → dist y y' < d →
      ∀ z' ∈ affGe ({0} : Set V3) {x', y'}, ∃ z ∈ affGe ({0} : Set V3) {x, y},
        ‖z' - z‖ ≤ e * ‖z‖ := by
  have hx0 : x ≠ 0 := by
    intro h
    exact hnc (by rw [h]; simpa using collinear_pair ℝ (0:V3) y)
  have hy0 : y ≠ 0 := by
    intro h
    exact hnc (by rw [h]; simpa [Set.pair_comm] using collinear_pair ℝ (0:V3) x)
  have hmaxpos : 0 < max ‖x‖ ‖y‖ := lt_max_of_lt_left (norm_pos_iff.mpr hx0)
  have hcrosspos : 0 < ‖cross3 x y‖ := by
    rw [norm_pos_iff]
    exact cross3_ne_zero_p17 hnc
  set C : ℝ := ‖cross3 x y‖ / max ‖x‖ ‖y‖ with hCdef
  have hCpos : 0 < C := div_pos hcrosspos hmaxpos
  set d : ℝ := min (e * C / 4) (min ‖x‖ ‖y‖ / 2) with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    refine lt_min ?_ (by linarith [lt_min hxpos hypos])
    exact div_pos (mul_pos he hCpos) (by norm_num)
  have hd_le_e : d ≤ e * C / 4 := by rw [hddef]; exact min_le_left _ _
  have hd_le_x : d ≤ ‖x‖ / 2 := by
    rw [hddef]
    have h1 : min (e * C / 4) (min ‖x‖ ‖y‖ / 2) ≤ min ‖x‖ ‖y‖ / 2 := min_le_right _ _
    have h2 : min ‖x‖ ‖y‖ / 2 ≤ ‖x‖ / 2 := by linarith [min_le_left ‖x‖ ‖y‖]
    exact le_trans h1 h2
  have hd_le_y : d ≤ ‖y‖ / 2 := by
    rw [hddef]
    have h1 : min (e * C / 4) (min ‖x‖ ‖y‖ / 2) ≤ min ‖x‖ ‖y‖ / 2 := min_le_right _ _
    have h2 : min ‖x‖ ‖y‖ / 2 ≤ ‖y‖ / 2 := by linarith [min_le_right ‖x‖ ‖y‖]
    exact le_trans h1 h2
  refine ⟨d, hdpos, fun x' y' hdx hdy z' hz' => ?_⟩
  have hdx' : ‖x' - x‖ < d := by
    rw [dist_comm] at hdx
    rwa [dist_eq_norm] at hdx
  have hdy' : ‖y' - y‖ < d := by
    rw [dist_comm] at hdy
    rwa [dist_eq_norm] at hdy
  have hx'0 : x' ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hdx'
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    linarith
  have hy'0 : y' ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hdy'
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    linarith
  obtain ⟨a, b, ha, hb, hz'rep⟩ := by
    have h := hz'
    rw [AFF_GE_1_2_0_p17 x' y' hx'0 hy'0] at h
    exact h
  refine ⟨a • x + b • y, ?_, ?_⟩
  · rw [AFF_GE_1_2_0_p17 x y hx0 hy0]
    exact ⟨a, b, ha, hb, rfl⟩
  · have hzm : z' - (a • x + b • y) = a • (x' - x) + b • (y' - y) := by
      rw [hz'rep]; module
    have hnorm : ‖z' - (a • x + b • y)‖ ≤ a * d + b * d := by
      rw [hzm]
      calc ‖a • (x' - x) + b • (y' - y)‖
          ≤ ‖a • (x' - x)‖ + ‖b • (y' - y)‖ := norm_add_le _ _
        _ = a * ‖x' - x‖ + b * ‖y' - y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * d + b * d :=
            add_le_add (mul_le_mul_of_nonneg_left (le_of_lt hdx') ha)
              (mul_le_mul_of_nonneg_left (le_of_lt hdy') hb)
    have hm : max a b ≤ ‖a • x + b • y‖ / C := by
      rw [le_div_iff₀ hCpos, hCdef, mul_comm]
      exact w_xrq17_lower_bound hx0 hy0 hnc a b ha hb
    have h2d : a * d + b * d ≤ e * ‖a • x + b • y‖ := by
      have hsum : a + b ≤ 2 * max a b := by
        have h1 := le_max_left a b
        have h2 := le_max_right a b
        linarith
      have hposd : 0 ≤ d := le_of_lt hdpos
      have hstep1 : a * d + b * d = d * (a + b) := by ring
      rw [hstep1]
      calc d * (a + b) ≤ d * (2 * max a b) := mul_le_mul_of_nonneg_left hsum hposd
        _ = 2 * d * max a b := by ring
        _ ≤ 2 * d * (‖a • x + b • y‖ / C) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
        _ = (2 * d / C) * ‖a • x + b • y‖ := by field_simp
        _ ≤ e * ‖a • x + b • y‖ := by
            have hle : 2 * d / C ≤ e := by
              rw [div_le_iff₀ hCpos]
              nlinarith [hd_le_e, mul_pos he hCpos]
            exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    exact hnorm.trans h2d

/-- HOL `MINIMIZE_OVER_MEMBERS`: finitely many positive radii have a common
positive infimum. -/
theorem MINIMIZE_OVER_MEMBERS_p17 {α : Type*} {P : α → ℝ → Prop} {s : Set α}
    (hfin : s.Finite) (h : ∀ x ∈ s, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P x t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → ∀ x ∈ s, P x t := by
  by_cases hem : s = ∅
  · subst hem
    refine ⟨1, one_pos, fun t _ x hx => absurd hx (by simp)⟩
  classical
  have hne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hem
  have h' : ∀ x : α, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → x ∈ s → P x t := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨e, he, hpe⟩ := h x hx
      exact ⟨e, he, fun t ht _ => hpe t ht⟩
    · exact ⟨1, one_pos, fun _ _ hxs => absurd hxs hx⟩
  choose f hf0 hf1 using h'
  set T := hfin.toFinset.image f with hT
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨f x, Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩⟩
  refine ⟨T.min' hTne, ?_, ?_⟩
  · obtain ⟨x, hxT, hfx⟩ := Finset.mem_image.mp (T.min'_mem hTne)
    rw [← hfx]
    exact hf0 x
  · intro t ht x hx
    have hxT : x ∈ hfin.toFinset := by simpa using hx
    have hle : T.min' hTne ≤ f x :=
      T.min'_le _ (Finset.mem_image.mpr ⟨x, hxT, rfl⟩)
    exact hf1 x t (lt_of_lt_of_le ht hle) hx

/-- HOL `MINIMIZE_OVER_2`. -/
theorem MINIMIZE_OVER_2_p17 {P Q : ℝ → Prop}
    (h1 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P t)
    (h2 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → Q t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P t ∧ Q t := by
  obtain ⟨d, hd, hP⟩ := h1
  obtain ⟨e, he, hQ⟩ := h2
  exact ⟨min d e, lt_min hd he, fun t ht =>
    ⟨hP t (lt_of_lt_of_le ht (min_le_left _ _)),
      hQ t (lt_of_lt_of_le ht (min_le_right _ _))⟩⟩

/-- HOL `MINIMIZE_OVER_STRONGER`. -/
theorem MINIMIZE_OVER_STRONGER_p17 {P Q : ℝ → Prop} (hPQ : ∀ t : ℝ, P t → Q t)
    (h1 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → Q t := by
  obtain ⟨e, he, hP⟩ := h1
  exact ⟨e, he, fun t ht => hPQ t (hP t ht)⟩

/-- HOL `deformation ff V (a,b)` (deformation.hl:506) — already ported
verbatim as `Kepler.Text.Deformation` (LocalAuto1.lean:128; `(0 : ℝ) ∈
Icc a b` = `(0) IN real_interval (a,b)`). This alias records the identity
(merge note: delete when the def moves upstream). -/
def deformationP17 (ff : V3 → ℝ → V3) (V : Set V3) (a b : ℝ) : Prop :=
  Deformation ff V a b


/-! ### W1: FAN7_SMALL_DEFORMATION kit -/

private theorem w_xrq17_uniform_close (φ : V3 → ℝ → V3) (V : Set V3)
    (hV : V.Finite) (hφ0 : ∀ v ∈ V, φ v 0 = v)
    (hcont : ∀ v ∈ V, ContinuousAt (φ v) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t| < d →
      ∀ v ∈ V, ‖φ v t - v‖ < ε := by
  intro ε hε
  have h : ∀ v ∈ V, ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t| < d → ‖φ v t - v‖ < ε := by
    intro v hv
    obtain ⟨d, hd, hd'⟩ := Metric.continuousAt_iff.mp (hcont v hv) ε hε
    refine ⟨d, hd, fun t ht => ?_⟩
    have h1 : dist (φ v t) (φ v 0) < ε := hd' (by simpa [Real.dist_eq] using ht)
    rwa [hφ0 v hv, dist_eq_norm] at h1
  obtain ⟨d, hd, hd'⟩ := MINIMIZE_OVER_MEMBERS_p17 hV h
  exact ⟨d, hd, fun t ht v hv => hd' t ht v hv⟩

private theorem w_xrq17_exists_not_collinear3 {v : V3} (hv : v ≠ 0) :
    ∃ u : V3, ¬ Collinear3 0 v u := by
  classical
  have hne : ∃ i : Fin 3, ((v : V3) : Fin 3 → ℝ) i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (by ext i; exact h i)
  obtain ⟨i, hi⟩ := hne
  have hji : ∃ j : Fin 3, j ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  obtain ⟨j, hj⟩ := hji
  refine ⟨(WithLp.toLp 2 ((Pi.single j (1:ℝ) : Fin 3 → ℝ)) : V3), ?_⟩
  intro hc
  obtain ⟨c, hcu⟩ :=
    (collinear3_iff_smul (v := (0:V3)) (w := v)
      (w1 := (WithLp.toLp 2 ((Pi.single j (1:ℝ) : Fin 3 → ℝ)) : V3)) hv).mp hc
  have hcu' : (WithLp.toLp 2 ((Pi.single j (1:ℝ) : Fin 3 → ℝ)) : V3) = c • v := by simpa using hcu
  have hcoord : ((c • v : V3) : Fin 3 → ℝ) i = c * ((v : V3) : Fin 3 → ℝ) i := rfl
  have hleft : ((WithLp.toLp 2 ((Pi.single j (1:ℝ) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ) i = 0 := by
    show (Pi.single j (1:ℝ) : Fin 3 → ℝ) i = 0
    exact Pi.single_eq_of_ne (Ne.symm hj) 1
  have hzero : c * ((v : V3) : Fin 3 → ℝ) i = 0 := by
    have hcf := congrFun (congrArg (fun x : V3 => ((x : V3) : Fin 3 → ℝ)) hcu') i
    rw [hleft, hcoord] at hcf
    exact hcf.symm
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hi
  have hu0 : ((WithLp.toLp 2 ((Pi.single j (1:ℝ) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ) = 0 := by
    have hcf := congrArg (fun x : V3 => ((x : V3) : Fin 3 → ℝ)) hcu'
    rw [hcf, hc0, zero_smul]
    rfl
  have h1 : ((WithLp.toLp 2 ((Pi.single j (1:ℝ) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ) j = 1 := by
    show (Pi.single j (1:ℝ) : Fin 3 → ℝ) j = 1
    exact Pi.single_eq_same j 1
  have h2 := congrFun hu0 j
  rw [h1] at h2
  norm_num at h2

private theorem w_xrq17_isClosed_cone {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {s : Set V3} (hs : s ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) :
    IsClosed (affGe ({0} : Set V3) s) := by
  rw [Set.mem_union] at hs
  rcases hs with hsE | ⟨v, hvV, rfl⟩
  · obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 hsE
    have hnc : ¬ Collinear3 0 v w := by
      have h := hfan.2.2.2.2.1 {v, w} hsE
      have hset : (insert (0:V3) ({v, w} : Set V3)) = ({0, v, w} : Set V3) := by
        ext z; simp
      rw [hset] at h; exact h
    exact closed_aff_ge_1_2 hnc
  · have hv0 : v ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hvV)
    obtain ⟨u, hnc⟩ := w_xrq17_exists_not_collinear3 hv0
    exact closed_halfline_fan hnc

private theorem w_xrq17_cone_finite {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {s : Set V3} (hs : s ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) : s.Finite :=
  (w_xrq17_ncard_le_two hfan.2.1 hs).1

private theorem w_xrq17_cone_zero {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {s : Set V3} (hs : s ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) : (0:V3) ∉ s := by
  rw [Set.mem_union] at hs
  rcases hs with hsE | ⟨v, hvV, rfl⟩
  · obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 hsE
    have hvV : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem hsE (by simp))
    have hwV : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem hsE (by simp))
    intro h0
    rcases Set.mem_insert_iff.mp h0 with h | h
    · exact hfan.2.2.2.1 (h ▸ hvV)
    · rw [Set.mem_singleton_iff] at h
      exact hfan.2.2.2.1 (h ▸ hwV)
  · intro h0
    rw [Set.mem_singleton_iff] at h0
    exact hfan.2.2.2.1 (h0 ▸ hvV)

private theorem w_xrq17_zero_mem_affGe {s : Set V3} (hfin : s.Finite) :
    (0:V3) ∈ affGe ({0} : Set V3) s := by
  have hfin' : ({0} ∪ s : Set V3).Finite := (Set.finite_singleton 0).union hfin
  refine ⟨fun z => if z = 0 then 1 else 0, hfin', ?_, ?_, ?_⟩
  · show (0:V3) = ∑ z ∈ hfin'.toFinset, (if z = 0 then (1:ℝ) else 0) • z
    exact (Finset.sum_eq_zero (s := hfin'.toFinset)
      (f := fun z : V3 => (if z = 0 then (1:ℝ) else 0) • z) (by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0; simp
        · simp [hz0])).symm
  · intro z hz
    by_cases hz0 : z = 0
    · subst hz0; norm_num
    · simp [hz0]
  · show (∑ z ∈ hfin'.toFinset, (if z = 0 then (1:ℝ) else 0)) = 1
    have hmem : (0:V3) ∈ hfin'.toFinset := by simp [Set.Finite.mem_toFinset]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro z hz hz0; simp [hz0]
    · intro hnot; exact absurd hmem hnot

private theorem w_xrq17_cone_approx (φ : V3 → ℝ → V3) (V : Set V3) (E : Set (Set V3))
    (hV : V.Finite) (hfan : FAN 0 V E) (hφ0 : ∀ v ∈ V, φ v 0 = v)
    (hcont : ∀ v ∈ V, ContinuousAt (φ v) 0)
    (s : Set V3) (hs : s ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) :
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
      ∀ z' ∈ affGe ({0} : Set V3) ((fun v : V3 => φ v t) '' s),
        ∃ z ∈ affGe ({0} : Set V3) s, ‖z' - z‖ ≤ δ * ‖z‖ := by
  rintro δ hδ
  rw [Set.mem_union] at hs
  rcases hs with hsE | ⟨v, hvV, rfl⟩
  · obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 hsE
    have hvV : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem hsE (by simp))
    have hwV : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem hsE (by simp))
    have hv0 : v ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hvV)
    have hw0 : w ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hwV)
    have hnc : ¬ Collinear ℝ ({0, v, w} : Set V3) := by
      have h := hfan.2.2.2.2.1 {v, w} hsE
      have hset : (insert (0:V3) ({v, w} : Set V3)) = ({0, v, w} : Set V3) := by
        ext z; simp
      rw [hset] at h; exact h
    obtain ⟨d, hd, hd'⟩ := lemma_2_p17 v w δ hnc hδ
    obtain ⟨r, hr, hr'⟩ := w_xrq17_uniform_close φ V hV hφ0 hcont d hd
    refine ⟨r, hr, fun t ht z' hz' => ?_⟩
    have himg : ((fun x : V3 => φ x t) '' ({v, w} : Set V3)) = {φ v t, φ w t} := by
      rw [Set.image_insert_eq, Set.image_singleton]
    rw [himg] at hz'
    have hdistv : dist v (φ v t) < d := by
      have h := hr' t ht v hvV
      simpa [dist_eq_norm, norm_sub_rev] using h
    have hdistw : dist w (φ w t) < d := by
      have h := hr' t ht w hwV
      simpa [dist_eq_norm, norm_sub_rev] using h
    obtain ⟨z, hz, hbound⟩ := hd' (φ v t) (φ w t) hdistv hdistw z' hz'
    exact ⟨z, hz, hbound⟩
  · have hv0 : v ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hvV)
    obtain ⟨d, hd, hd'⟩ := lemma_1_p17 v δ hv0 hδ
    obtain ⟨r, hr, hr'⟩ := w_xrq17_uniform_close φ V hV hφ0 hcont d hd
    refine ⟨r, hr, fun t ht z' hz' => ?_⟩
    have himg : ((fun x : V3 => φ x t) '' ({v} : Set V3)) = {φ v t} := by
      rw [Set.image_singleton]
    rw [himg] at hz'
    have hdistv : dist v (φ v t) < d := by
      have h := hr' t ht v hvV
      simpa [dist_eq_norm, norm_sub_rev] using h
    obtain ⟨z, hz, hbound⟩ := hd' (φ v t) hdistv z' hz'
    exact ⟨z, hz, hbound⟩

private theorem w_xrq17_pair_empty (φ : V3 → ℝ → V3) (V : Set V3) (E : Set (Set V3))
    (hV : V.Finite) (hfan : FAN 0 V E) (hφ0 : ∀ v ∈ V, φ v 0 = v)
    (hcont : ∀ v ∈ V, ContinuousAt (φ v) 0)
    {s1 s2 : Set V3} (hs1 : s1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}})
    (hs2 : s2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}) (hdisj : s1 ∩ s2 = ∅) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
      affGe ({0} : Set V3) ((fun v : V3 => φ v t) '' s1) ∩
        affGe ({0} : Set V3) ((fun v : V3 => φ v t) '' s2) = ({0} : Set V3) := by
  have hcone : affGe ({0} : Set V3) s1 ∩ affGe ({0} : Set V3) s2 = ({0} : Set V3) := by
    have h7 := hfan.2.2.2.2.2 s1 hs1 s2 hs2
    rw [h7, hdisj, w_xrq17_affGe_empty]
  have hcl1 := w_xrq17_isClosed_cone hfan hs1
  have hcl2 := w_xrq17_isClosed_cone hfan hs2
  have hcon1 : conicP17 (affGe ({0} : Set V3) s1) :=
    CONIC_AFF_GE_0_p17 s1 (w_xrq17_cone_finite hfan hs1) (w_xrq17_cone_zero hfan hs1)
  have hcon2 : conicP17 (affGe ({0} : Set V3) s2) :=
    CONIC_AFF_GE_0_p17 s2 (w_xrq17_cone_finite hfan hs2) (w_xrq17_cone_zero hfan hs2)
  obtain ⟨δ, hδ, hsep⟩ := SEPARATE_CLOSED_CONES_p17 (affGe ({0} : Set V3) s1)
    (affGe ({0} : Set V3) s2) hcon1 hcl1 hcon2 hcl2 (by rw [hcone])
  obtain ⟨r1, hr1, happ1⟩ := w_xrq17_cone_approx φ V E hV hfan hφ0 hcont s1 hs1 (δ/3) (by linarith)
  obtain ⟨r2, hr2, happ2⟩ := w_xrq17_cone_approx φ V E hV hfan hφ0 hcont s2 hs2 (δ/3) (by linarith)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun t ht => ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨hzt1, hzt2⟩ := hz
    obtain ⟨z1, hz1, hb1⟩ := happ1 t (lt_of_lt_of_le ht (min_le_left _ _)) z hzt1
    obtain ⟨z2, hz2, hb2⟩ := happ2 t (lt_of_lt_of_le ht (min_le_right _ _)) z hzt2
    by_contra hz0
    have hz1ne : z1 ≠ 0 := by
      intro h0
      apply hz0
      rw [h0, sub_zero] at hb1
      have hzero : ‖z‖ = 0 := le_antisymm (by simpa using hb1) (norm_nonneg _)
      simpa using hzero
    have hz2ne : z2 ≠ 0 := by
      intro h0
      apply hz0
      rw [h0, sub_zero] at hb2
      have hzero : ‖z‖ = 0 := le_antisymm (by simpa using hb2) (norm_nonneg _)
      simpa using hzero
    have hdist : δ * max ‖z1‖ ‖z2‖ ≤ dist z1 z2 := hsep z1 hz1 z2 hz2
    have hb1' : ‖z1 - z‖ ≤ δ/3 * ‖z1‖ := by rwa [norm_sub_rev] at hb1
    have hb2' : ‖z - z2‖ ≤ δ/3 * ‖z2‖ := hb2
    have htri : dist z1 z2 ≤ ‖z1 - z‖ + ‖z - z2‖ := by
      rw [dist_eq_norm]
      calc ‖z1 - z2‖ = ‖(z1 - z) + (z - z2)‖ := by
            rw [show z1 - z2 = (z1 - z) + (z - z2) by abel]
        _ ≤ ‖z1 - z‖ + ‖z - z2‖ := norm_add_le _ _
    have hmain : δ * max ‖z1‖ ‖z2‖ ≤ δ * ((‖z1‖ + ‖z2‖) / 3) := by
      calc δ * max ‖z1‖ ‖z2‖ ≤ dist z1 z2 := hdist
        _ ≤ ‖z1 - z‖ + ‖z - z2‖ := htri
        _ ≤ δ/3 * ‖z1‖ + δ/3 * ‖z2‖ := add_le_add hb1' hb2'
        _ = δ * ((‖z1‖ + ‖z2‖) / 3) := by ring
    have hle : max ‖z1‖ ‖z2‖ ≤ (‖z1‖ + ‖z2‖) / 3 := (mul_le_mul_iff_of_pos_left hδ).mp hmain
    have hle2 : ‖z1‖ + ‖z2‖ ≤ 2 * max ‖z1‖ ‖z2‖ := by
      have h1 := le_max_left ‖z1‖ ‖z2‖
      have h2 := le_max_right ‖z1‖ ‖z2‖
      linarith
    have hmpos : 0 < max ‖z1‖ ‖z2‖ := lt_max_of_lt_left (norm_pos_iff.mpr hz1ne)
    nlinarith
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨w_xrq17_zero_mem_affGe ((w_xrq17_cone_finite hfan hs1).image _),
      w_xrq17_zero_mem_affGe ((w_xrq17_cone_finite hfan hs2).image _)⟩

private theorem w_xrq17_cross_norm_sq_eq (u v : V3) :
    ‖cross3 u v‖ ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) * (v ⬝ᵥ u) := by
  rw [show ‖cross3 u v‖ ^ 2 = inner ℝ (cross3 u v) (cross3 u v) from
      (real_inner_self_eq_norm_sq _).symm, inner_eq_dot, coe_cross3_p17,
    cross_dot_cross]

private theorem w_xrq17_dot_continuousAt (f g : ℝ → V3) (r : ℝ)
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) :
    ContinuousAt (fun t => (f t) ⬝ᵥ (g t)) r := by
  have h := (ContinuousAt.inner (𝕜 := ℝ) hf hg)
  simpa [inner_eq_dot] using h

private theorem w_xrq17_cross_norm_sq_continuousAt (f g : ℝ → V3) (r : ℝ)
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) :
    ContinuousAt (fun t => ‖cross3 (f t) (g t)‖ ^ 2) r := by
  have hff := w_xrq17_dot_continuousAt f f r hf hf
  have hgg := w_xrq17_dot_continuousAt g g r hg hg
  have hfg := w_xrq17_dot_continuousAt f g r hf hg
  have hgf := w_xrq17_dot_continuousAt g f r hg hf
  have hval : (fun t => ‖cross3 (f t) (g t)‖ ^ 2)
      = fun t => (f t) ⬝ᵥ (f t) * ((g t) ⬝ᵥ (g t))
          - ((f t) ⬝ᵥ (g t)) * ((g t) ⬝ᵥ (f t)) := by
    funext t
    exact w_xrq17_cross_norm_sq_eq (f t) (g t)
  rw [hval]
  exact ((hff.mul hgg).sub (hfg.mul hgf))

private theorem w_xrq17_cross3_zero_right (u : V3) : cross3 u (0:V3) = 0 := by
  conv_lhs => rw [show (0:V3) = (0:ℝ) • u by simp]
  rw [w_xrq17_cross3_smul_right, cross3_self_p17, smul_zero]

private theorem w_xrq17_cross3_zero_left (v : V3) : cross3 (0:V3) v = 0 := by
  rw [cross3_anticomm_p17, w_xrq17_cross3_zero_right, neg_zero]

private theorem w_xrq17_not_collinear_of_cross_ne_zero {u v : V3} (h : cross3 u v ≠ 0) :
    ¬ Collinear ℝ ({0, u, v} : Set V3) := by
  intro hc
  apply h
  by_cases hu : u = 0
  · rw [hu]; exact w_xrq17_cross3_zero_left v
  · by_cases hv : v = 0
    · rw [hv]; exact w_xrq17_cross3_zero_right u
    · obtain ⟨c, hc'⟩ :=
        (collinear3_iff_smul (v := (0:V3)) (w := u) (w1 := v) hu).mp hc
      have hc'' : v = c • u := by simpa using hc'
      rw [hc'', w_xrq17_cross3_smul_right, cross3_self_p17, smul_zero]

/-- HOL `FAN7_SMALL_DEFORMATION`. NEEDS: `GMLWKPK_SIMPLE_p17`,
`SEPARATE_CLOSED_CONES_p17`, `lemma_1_p17`, `lemma_2_p17` and the
MINIMIZE kit (deformation.hl:511-1009) — the fan7 small-deformation
theorem. -/
theorem FAN7_SMALL_DEFORMATION_p17 (V : Set V3) (E : Set (Set V3)) (a b : ℝ)
    (phii : V3 → ℝ → V3) (hdef : Deformation phii V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
      fan7 (0:V3) ((fun v : V3 => phii v t) '' V)
        ((fun e' => (fun v : V3 => phii v t) '' e') '' E) := by
  classical
  obtain ⟨h0Icc, hcontIcc, hφ0⟩ := hdef
  have hcont : ∀ v ∈ V, ContinuousAt (phii v) 0 := fun v hv => hcontIcc v hv 0 h0Icc
  have hV : V.Finite := hfan.2.2.1.1
  have huniform := w_xrq17_uniform_close phii V hV hφ0 hcont
  have hEfin : E.Finite := by
    have hsub : E ⊆ (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (V ×ˢ V) := by
      intro e he
      obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 he
      have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
      have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
      exact ⟨(v, w), ⟨hv, hw⟩, by simp⟩
    exact Set.Finite.subset ((hV.prod hV).image _) hsub
  obtain ⟨eI, heIpos, heI⟩ : ∃ eI : ℝ, 0 < eI ∧ ∀ t : ℝ, |t| < eI →
      Set.InjOn (fun v : V3 => phii v t) V := by
    have hper : ∀ p ∈ V ×ˢ V, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
        (p.1 ≠ p.2 → phii p.1 t ≠ phii p.2 t) := by
      intro p hp
      by_cases hne : p.1 ≠ p.2
      · have hp1 : p.1 ∈ V := hp.1
        have hp2 : p.2 ∈ V := hp.2
        have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        obtain ⟨d, hd, hd'⟩ := huniform (‖p.1 - p.2‖ / 2) (by linarith)
        refine ⟨d, hd, fun t ht _ heq => ?_⟩
        have h1 : ‖phii p.1 t - p.1‖ < ‖p.1 - p.2‖ / 2 := hd' t ht p.1 hp1
        have h2 : ‖phii p.2 t - p.2‖ < ‖p.1 - p.2‖ / 2 := hd' t ht p.2 hp2
        have hb1 : ‖p.1 - phii p.1 t‖ < ‖p.1 - p.2‖ / 2 := by rwa [norm_sub_rev] at h1
        have htri : ‖p.1 - p.2‖ ≤
            ‖p.1 - phii p.1 t‖ + ‖phii p.1 t - phii p.2 t‖ + ‖phii p.2 t - p.2‖ := by
          calc ‖p.1 - p.2‖ = ‖(p.1 - phii p.1 t) + (phii p.1 t - phii p.2 t) + (phii p.2 t - p.2)‖ := by
                rw [show p.1 - p.2 =
                  (p.1 - phii p.1 t) + (phii p.1 t - phii p.2 t) + (phii p.2 t - p.2) by abel]
            _ ≤ ‖(p.1 - phii p.1 t) + (phii p.1 t - phii p.2 t)‖ + ‖phii p.2 t - p.2‖ :=
                norm_add_le _ _
            _ ≤ ‖p.1 - phii p.1 t‖ + ‖phii p.1 t - phii p.2 t‖ + ‖phii p.2 t - p.2‖ := by
                linarith [norm_add_le (p.1 - phii p.1 t) (phii p.1 t - phii p.2 t)]
        have hlt : ‖p.1 - p.2‖ < ‖p.1 - p.2‖ := by
          calc ‖p.1 - p.2‖ ≤ ‖p.1 - phii p.1 t‖ + ‖phii p.1 t - phii p.2 t‖ + ‖phii p.2 t - p.2‖ := htri
            _ = ‖p.1 - phii p.1 t‖ + ‖phii p.2 t - p.2‖ := by
                rw [heq, sub_self, norm_zero, add_zero]
            _ < ‖p.1 - p.2‖ / 2 + ‖p.1 - p.2‖ / 2 := add_lt_add hb1 h2
            _ = ‖p.1 - p.2‖ := by ring
        exact lt_irrefl _ hlt
      · exact ⟨1, one_pos, fun t ht h => absurd h hne⟩
    obtain ⟨eI, heI, hI⟩ := MINIMIZE_OVER_MEMBERS_p17 (hV.prod hV) hper
    refine ⟨eI, heI, fun t ht v hv w hw heq => ?_⟩
    by_contra hne
    exact (hI t ht (v, w) ⟨hv, hw⟩ hne) heq
  have hgraphI : ∀ t : ℝ, |t| < eI →
      Graph ((fun e' : Set V3 => (fun v : V3 => phii v t) '' e') '' E) := by
    intro t ht
    have hinj := heI t ht
    intro e' he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 he
    have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
    have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
    have hne : phii v t ≠ phii w t := fun h => hvw (hinj hv hw h)
    change ∃ h : ((fun v : V3 => phii v t) '' ({v, w} : Set V3)).Finite, h.toFinset.card = 2
    rw [Set.image_insert_eq, Set.image_singleton]
    refine ⟨(Set.finite_singleton (phii w t)).insert (phii v t), ?_⟩
    rw [← Set.ncard_eq_toFinset_card _
      ((Set.finite_singleton (phii w t)).insert (phii v t))]
    exact Set.ncard_pair hne
  obtain ⟨eZ, heZpos, heZ⟩ : ∃ eZ : ℝ, 0 < eZ ∧ ∀ t : ℝ, |t| < eZ →
      ∀ e' ∈ (fun e' : Set V3 => (fun v : V3 => phii v t) '' e') '' E, (0:V3) ∉ e' := by
    have hper : ∀ p ∈ E, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
        ∀ z ∈ (fun v : V3 => phii v t) '' p, z ≠ 0 := by
      intro p hp
      obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 hp
      have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem hp (by simp))
      have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem hp (by simp))
      have hv0 : v ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hv)
      have hw0 : w ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hw)
      have hminpos : 0 < min ‖v‖ ‖w‖ := lt_min (norm_pos_iff.mpr hv0) (norm_pos_iff.mpr hw0)
      obtain ⟨d, hd, hd'⟩ := huniform (min ‖v‖ ‖w‖) hminpos
      refine ⟨d, hd, fun t ht z hz => ?_⟩
      have hvc : ‖phii v t - v‖ < min ‖v‖ ‖w‖ := hd' t ht v hv
      have hwc : ‖phii w t - w‖ < min ‖v‖ ‖w‖ := hd' t ht w hw
      rw [Set.image_insert_eq, Set.image_singleton] at hz
      rcases Set.mem_insert_iff.mp hz with h | h
      · rw [h]
        intro h0
        rw [h0] at hvc
        have : ‖v‖ < min ‖v‖ ‖w‖ := by simpa [zero_sub, norm_neg] using hvc
        linarith [min_le_left ‖v‖ ‖w‖]
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        intro h0
        rw [h0] at hwc
        have : ‖w‖ < min ‖v‖ ‖w‖ := by simpa [zero_sub, norm_neg] using hwc
        linarith [min_le_right ‖v‖ ‖w‖]
    obtain ⟨eZ, heZ, hZ⟩ := MINIMIZE_OVER_MEMBERS_p17 hEfin hper
    refine ⟨eZ, heZ, fun t ht e' he' => ?_⟩
    obtain ⟨e, he, rfl⟩ := he'
    change (0:V3) ∉ (fun v : V3 => phii v t) '' e
    intro hmem
    exact hZ t ht e he 0 hmem rfl
  obtain ⟨eF, heFpos, heF⟩ : ∃ eF : ℝ, 0 < eF ∧ ∀ t : ℝ, |t| < eF →
      fan6 0 ((fun v : V3 => phii v t) '' V)
        ((fun e' : Set V3 => (fun v : V3 => phii v t) '' e') '' E) := by
    have hper : ∀ p ∈ E, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
        ¬ Collinear ℝ (insert (0:V3) ((fun v : V3 => phii v t) '' p)) := by
      intro p hp
      obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 hp
      have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem hp (by simp))
      have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem hp (by simp))
      have hnc : ¬ Collinear ℝ ({0, v, w} : Set V3) := by
        have h := hfan.2.2.2.2.1 {v, w} hp
        have hset : (insert (0:V3) ({v, w} : Set V3)) = ({0, v, w} : Set V3) := rfl
        rwa [hset] at h
      have hcross : cross3 v w ≠ 0 := cross3_ne_zero_p17 hnc
      have hnormpos : 0 < ‖cross3 v w‖ ^ 2 := by
        have hp' : 0 < ‖cross3 v w‖ := norm_pos_iff.mpr hcross
        positivity
      have hHcont : ContinuousAt (fun t => ‖cross3 (phii v t) (phii w t)‖ ^ 2) 0 :=
        w_xrq17_cross_norm_sq_continuousAt (phii v) (phii w) 0 (hcont v hv) (hcont w hw)
      have hH0 : ‖cross3 (phii v 0) (phii w 0)‖ ^ 2 = ‖cross3 v w‖ ^ 2 := by
        rw [hφ0 v hv, hφ0 w hw]
      obtain ⟨d, hd, hd'⟩ := Metric.continuousAt_iff.mp hHcont (‖cross3 v w‖ ^ 2) hnormpos
      refine ⟨d, hd, fun t ht hcol => ?_⟩
      have hclose : dist (‖cross3 (phii v t) (phii w t)‖ ^ 2) (‖cross3 v w‖ ^ 2)
          < ‖cross3 v w‖ ^ 2 := by
        have := hd' (by simpa [Real.dist_eq] using ht)
        simpa [hH0] using this
      have hHpos : 0 < ‖cross3 (phii v t) (phii w t)‖ ^ 2 := by
        rw [Real.dist_eq, abs_lt] at hclose
        linarith [hclose.1]
      have hcross' : cross3 (phii v t) (phii w t) ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hHpos
        norm_num at hHpos
      have hnc' : ¬ Collinear ℝ ({0, phii v t, phii w t} : Set V3) :=
        w_xrq17_not_collinear_of_cross_ne_zero hcross'
      have himg : (insert (0:V3) ((fun v : V3 => phii v t) '' ({v, w} : Set V3)))
          = ({0, phii v t, phii w t} : Set V3) := by
        rw [Set.image_insert_eq, Set.image_singleton]
      exact hnc' (himg ▸ hcol)
    obtain ⟨eF, heF, hF⟩ := MINIMIZE_OVER_MEMBERS_p17 hEfin hper
    refine ⟨eF, heF, fun t ht e' he' => ?_⟩
    obtain ⟨e, he, rfl⟩ := he'
    exact hF t ht e he
  have hSfin : ({s : Set V3 | ∃ v ∈ V, s = {v}}).Finite := by
    have heq : ({s : Set V3 | ∃ v ∈ V, s = {v}}) = (fun v : V3 => ({v} : Set V3)) '' V := by
      ext s
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
    rw [heq]
    exact hV.image _
  have hFfin : (E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}}).Finite := hEfin.union hSfin
  obtain ⟨eE, heEpos, heE⟩ : ∃ eE : ℝ, 0 < eE ∧ ∀ t : ℝ, |t| < eE →
      ∀ p ∈ (E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}}) ×ˢ
        (E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}}),
        (((fun v : V3 => phii v t) '' p.1) ∩ ((fun v : V3 => phii v t) '' p.2) = ∅ →
          affGe ({0} : Set V3) ((fun v : V3 => phii v t) '' p.1) ∩
            affGe ({0} : Set V3) ((fun v : V3 => phii v t) '' p.2) = ({0} : Set V3)) := by
    have hper : ∀ p ∈ (E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}}) ×ˢ
        (E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}}), ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
        (((fun v : V3 => phii v t) '' p.1) ∩ ((fun v : V3 => phii v t) '' p.2) = ∅ →
          affGe ({0} : Set V3) ((fun v : V3 => phii v t) '' p.1) ∩
            affGe ({0} : Set V3) ((fun v : V3 => phii v t) '' p.2) = ({0} : Set V3)) := by
      intro p hp
      have hs1 : p.1 ∈ E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}} := hp.1
      have hs2 : p.2 ∈ E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}} := hp.2
      by_cases hdisj : p.1 ∩ p.2 = ∅
      · obtain ⟨r, hr, hr'⟩ := w_xrq17_pair_empty phii V E hV hfan hφ0 hcont hs1 hs2 hdisj
        exact ⟨r, hr, fun t ht _ => hr' t ht⟩
      · refine ⟨1, one_pos, fun t ht himgdisj => ?_⟩
        exfalso
        obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hdisj
        have hmem : phii z t ∈ ((fun v : V3 => phii v t) '' p.1) ∩
            ((fun v : V3 => phii v t) '' p.2) :=
          ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2, rfl⟩⟩
        rw [himgdisj] at hmem
        exact hmem
    obtain ⟨eE, heE, hE⟩ := MINIMIZE_OVER_MEMBERS_p17 (hFfin.prod hFfin) hper
    exact ⟨eE, heE, fun t ht p hp => hE t ht p hp⟩
  refine ⟨min eI (min eZ (min eF eE)), lt_min heIpos (lt_min heZpos (lt_min heFpos heEpos)), ?_⟩
  intro t hneg hpos
  have htabs : |t| < min eI (min eZ (min eF eE)) := abs_lt.mpr ⟨hneg, hpos⟩
  have htI : |t| < eI := lt_of_lt_of_le htabs (min_le_left _ _)
  have htZ : |t| < eZ := lt_of_lt_of_le htabs (le_trans (min_le_right _ _) (min_le_left _ _))
  have htF : |t| < eF := lt_of_lt_of_le htabs
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htE : |t| < eE := lt_of_lt_of_le htabs
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  set V' : Set V3 := (fun v : V3 => phii v t) '' V with hV'def
  set E' : Set (Set V3) := (fun e' : Set V3 => (fun v : V3 => phii v t) '' e') '' E with hE'def
  have hsup' : ⋃₀ E' ⊆ V' := by
    intro x hx
    rw [Set.mem_sUnion] at hx
    obtain ⟨e', he', hxe'⟩ := hx
    rw [hE'def, Set.mem_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    rw [Set.mem_image] at hxe'
    obtain ⟨v, hv, rfl⟩ := hxe'
    exact ⟨v, hfan.1 (Set.subset_sUnion_of_mem he hv), rfl⟩
  have hgraph' : Graph E' := by
    rw [hE'def]
    exact hgraphI t htI
  have hzero' : ∀ e' ∈ E', (0:V3) ∉ e' := by
    rw [hE'def]
    exact heZ t htZ
  have hfan6' : fan6 0 V' E' := by
    rw [hV'def, hE'def]
    exact heF t htF
  have hempty' : ∀ e1' ∈ E' ∪ {s : Set V3 | ∃ v ∈ V', s = {v}},
      ∀ e2' ∈ E' ∪ {s : Set V3 | ∃ v ∈ V', s = {v}},
        e1' ∩ e2' = ∅ → affGe ({0} : Set V3) e1' ∩ affGe ({0} : Set V3) e2' = ({0} : Set V3) := by
    intro e1' he1' e2' he2' hdj
    have hcover : E' ∪ {s : Set V3 | ∃ v ∈ V', s = {v}} ⊆
        (fun s : Set V3 => (fun v : V3 => phii v t) '' s) ''
          (E ∪ {s : Set V3 | ∃ v ∈ V, s = {v}}) := by
      intro s' hs'
      rw [Set.mem_union] at hs'
      rcases hs' with hEin | ⟨v', hv', rfl⟩
      · rw [hE'def, Set.mem_image] at hEin
        obtain ⟨e, he, rfl⟩ := hEin
        exact ⟨e, Set.mem_union_left _ he, rfl⟩
      · rw [Set.mem_image] at hv'
        obtain ⟨v, hv, rfl⟩ := hv'
        refine ⟨{v}, Set.mem_union_right _ ⟨v, hv, rfl⟩, ?_⟩
        show ((fun v : V3 => phii v t) '' ({v} : Set V3)) = {phii v t}
        rw [Set.image_singleton]
    obtain ⟨s1, hs1, hrepr1⟩ := hcover he1'
    obtain ⟨s2, hs2, hrepr2⟩ := hcover he2'
    have hrepr1' : ((fun v : V3 => phii v t) '' s1) = e1' := hrepr1
    have hrepr2' : ((fun v : V3 => phii v t) '' s2) = e2' := hrepr2
    have hpre : ((fun v : V3 => phii v t) '' s1) ∩ ((fun v : V3 => phii v t) '' s2) = ∅ := by
      rw [hrepr1', hrepr2']
      exact hdj
    have hres := heE t htE (s1, s2) ⟨hs1, hs2⟩ hpre
    change affGe ({0} : Set V3) ((fun v : V3 => phii v t) '' s1) ∩
      affGe ({0} : Set V3) ((fun v : V3 => phii v t) '' s2) = ({0} : Set V3) at hres
    rw [hrepr1', hrepr2'] at hres
    exact hres
  exact (GMLWKPK_SIMPLE_p17 V' E' 0 hsup' hgraph' hfan6' hzero').mpr hempty'



private theorem w_xrq17_image_fan_data (V : Set V3) (E : Set (Set V3)) (a b : ℝ)
    (φ : V3 → ℝ → V3) (hdef : Deformation φ V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      (⋃₀ ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E)) ⊆
        ((fun v : V3 => φ v t) '' V) ∧
      Graph ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) ∧
      fan1 0 ((fun v : V3 => φ v t) '' V)
        ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) ∧
      fan2 0 ((fun v : V3 => φ v t) '' V)
        ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) ∧
      fan6 0 ((fun v : V3 => φ v t) '' V)
        ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) := by
  classical
  obtain ⟨h0Icc, hcontIcc, hφ0⟩ := hdef
  have hcont : ∀ v ∈ V, ContinuousAt (φ v) 0 := fun v hv => hcontIcc v hv 0 h0Icc
  have hV : V.Finite := hfan.2.2.1.1
  have huniform := w_xrq17_uniform_close φ V hV hφ0 hcont
  have hEfin : E.Finite := by
    have hsub : E ⊆ (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (V ×ˢ V) := by
      intro e he
      obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 he
      have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
      have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
      exact ⟨(v, w), ⟨hv, hw⟩, by simp⟩
    exact Set.Finite.subset ((hV.prod hV).image _) hsub
  obtain ⟨eV, heVpos, heV⟩ : ∃ eV : ℝ, 0 < eV ∧ ∀ t : ℝ, |t| < eV →
      ∀ v ∈ V, φ v t ≠ 0 := by
    have hper : ∀ p ∈ V, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → φ p t ≠ 0 := by
      intro p hp
      have hp0 : p ≠ 0 := fun h => hfan.2.2.2.1 (h ▸ hp)
      have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      obtain ⟨d, hd, hd'⟩ := huniform (‖p‖ / 2) (by linarith)
      refine ⟨d, hd, fun t ht h0 => ?_⟩
      have h1 : ‖φ p t - p‖ < ‖p‖ / 2 := hd' t ht p hp
      rw [h0] at h1
      have h2 : ‖p‖ < ‖p‖ / 2 := by simpa [zero_sub, norm_neg] using h1
      linarith
    obtain ⟨eV, heV, hVall⟩ := MINIMIZE_OVER_MEMBERS_p17 hV hper
    exact ⟨eV, heV, fun t ht p hp => hVall t ht p hp⟩
  obtain ⟨eI, heIpos, heI⟩ : ∃ eI : ℝ, 0 < eI ∧ ∀ t : ℝ, |t| < eI →
      Set.InjOn (fun v : V3 => φ v t) V := by
    have hper : ∀ p ∈ V ×ˢ V, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
        (p.1 ≠ p.2 → φ p.1 t ≠ φ p.2 t) := by
      intro p hp
      by_cases hne : p.1 ≠ p.2
      · have hp1 : p.1 ∈ V := hp.1
        have hp2 : p.2 ∈ V := hp.2
        have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        obtain ⟨d, hd, hd'⟩ := huniform (‖p.1 - p.2‖ / 2) (by linarith)
        refine ⟨d, hd, fun t ht _ heq => ?_⟩
        have h1 : ‖φ p.1 t - p.1‖ < ‖p.1 - p.2‖ / 2 := hd' t ht p.1 hp1
        have h2 : ‖φ p.2 t - p.2‖ < ‖p.1 - p.2‖ / 2 := hd' t ht p.2 hp2
        have hb1 : ‖p.1 - φ p.1 t‖ < ‖p.1 - p.2‖ / 2 := by rwa [norm_sub_rev] at h1
        have htri : ‖p.1 - p.2‖ ≤
            ‖p.1 - φ p.1 t‖ + ‖φ p.1 t - φ p.2 t‖ + ‖φ p.2 t - p.2‖ := by
          calc ‖p.1 - p.2‖ = ‖(p.1 - φ p.1 t) + (φ p.1 t - φ p.2 t) + (φ p.2 t - p.2)‖ := by
                rw [show p.1 - p.2 =
                  (p.1 - φ p.1 t) + (φ p.1 t - φ p.2 t) + (φ p.2 t - p.2) by abel]
            _ ≤ ‖(p.1 - φ p.1 t) + (φ p.1 t - φ p.2 t)‖ + ‖φ p.2 t - p.2‖ :=
                norm_add_le _ _
            _ ≤ ‖p.1 - φ p.1 t‖ + ‖φ p.1 t - φ p.2 t‖ + ‖φ p.2 t - p.2‖ := by
                linarith [norm_add_le (p.1 - φ p.1 t) (φ p.1 t - φ p.2 t)]
        have hlt : ‖p.1 - p.2‖ < ‖p.1 - p.2‖ := by
          calc ‖p.1 - p.2‖ ≤ ‖p.1 - φ p.1 t‖ + ‖φ p.1 t - φ p.2 t‖ + ‖φ p.2 t - p.2‖ := htri
            _ = ‖p.1 - φ p.1 t‖ + ‖φ p.2 t - p.2‖ := by
                rw [heq, sub_self, norm_zero, add_zero]
            _ < ‖p.1 - p.2‖ / 2 + ‖p.1 - p.2‖ / 2 := add_lt_add hb1 h2
            _ = ‖p.1 - p.2‖ := by ring
        exact lt_irrefl _ hlt
      · exact ⟨1, one_pos, fun t ht h => absurd h hne⟩
    obtain ⟨eI, heI, hI⟩ := MINIMIZE_OVER_MEMBERS_p17 (hV.prod hV) hper
    refine ⟨eI, heI, fun t ht v hv w hw heq => ?_⟩
    by_contra hne
    exact (hI t ht (v, w) ⟨hv, hw⟩ hne) heq
  obtain ⟨eF, heFpos, heF⟩ : ∃ eF : ℝ, 0 < eF ∧ ∀ t : ℝ, |t| < eF →
      fan6 0 ((fun v : V3 => φ v t) '' V)
        ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) := by
    have hper : ∀ p ∈ E, ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
        ¬ Collinear ℝ (insert (0:V3) ((fun v : V3 => φ v t) '' p)) := by
      intro p hp
      obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 hp
      have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem hp (by simp))
      have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem hp (by simp))
      have hnc : ¬ Collinear ℝ ({0, v, w} : Set V3) := by
        have h := hfan.2.2.2.2.1 {v, w} hp
        rwa [show (insert (0:V3) ({v, w} : Set V3)) = ({0, v, w} : Set V3) from rfl] at h
      have hcross : cross3 v w ≠ 0 := cross3_ne_zero_p17 hnc
      have hnormpos : 0 < ‖cross3 v w‖ ^ 2 := by
        have hp' : 0 < ‖cross3 v w‖ := norm_pos_iff.mpr hcross
        positivity
      have hHcont : ContinuousAt (fun t => ‖cross3 (φ v t) (φ w t)‖ ^ 2) 0 :=
        w_xrq17_cross_norm_sq_continuousAt (φ v) (φ w) 0 (hcont v hv) (hcont w hw)
      have hH0 : ‖cross3 (φ v 0) (φ w 0)‖ ^ 2 = ‖cross3 v w‖ ^ 2 := by
        rw [hφ0 v hv, hφ0 w hw]
      obtain ⟨d, hd, hd'⟩ := Metric.continuousAt_iff.mp hHcont (‖cross3 v w‖ ^ 2) hnormpos
      refine ⟨d, hd, fun t ht hcol => ?_⟩
      have hclose : dist (‖cross3 (φ v t) (φ w t)‖ ^ 2) (‖cross3 v w‖ ^ 2)
          < ‖cross3 v w‖ ^ 2 := by
        have := hd' (by simpa [Real.dist_eq] using ht)
        simpa [hH0] using this
      have hHpos : 0 < ‖cross3 (φ v t) (φ w t)‖ ^ 2 := by
        rw [Real.dist_eq, abs_lt] at hclose
        linarith [hclose.1]
      have hcross' : cross3 (φ v t) (φ w t) ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hHpos
        norm_num at hHpos
      have hnc' : ¬ Collinear ℝ ({0, φ v t, φ w t} : Set V3) :=
        w_xrq17_not_collinear_of_cross_ne_zero hcross'
      have himg : (insert (0:V3) ((fun v : V3 => φ v t) '' ({v, w} : Set V3)))
          = ({0, φ v t, φ w t} : Set V3) := by
        rw [Set.image_insert_eq, Set.image_singleton]
      exact hnc' (himg ▸ hcol)
    obtain ⟨eF, heF, hF⟩ := MINIMIZE_OVER_MEMBERS_p17 hEfin hper
    refine ⟨eF, heF, fun t ht e' he' => ?_⟩
    obtain ⟨e, he, rfl⟩ := he'
    change ¬ Collinear ℝ (insert (0:V3) ((fun v : V3 => φ v t) '' e))
    exact hF t ht e he
  refine ⟨min eI (min eV eF), lt_min heIpos (lt_min heVpos heFpos), fun t ht => ?_⟩
  have htI : |t| < eI := lt_of_lt_of_le ht (min_le_left _ _)
  have htV : |t| < eV := lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have htF : |t| < eF := lt_of_lt_of_le ht
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hinj := heI t htI
  have hcover : (⋃₀ ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E)) ⊆
      ((fun v : V3 => φ v t) '' V) := by
    intro x hx
    rw [Set.mem_sUnion] at hx
    obtain ⟨e', he', hxe'⟩ := hx
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨v, hv, rfl⟩ := hxe'
    exact ⟨v, hfan.1 (Set.subset_sUnion_of_mem he hv), rfl⟩
  have hgraph : Graph ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨v, w, hvw, rfl⟩ := w_xrq17_edge_pair hfan.2.1 he
    have hv : v ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
    have hw : w ∈ V := hfan.1 (Set.subset_sUnion_of_mem he (by simp))
    have hne : φ v t ≠ φ w t := fun h => hvw (hinj hv hw h)
    change ∃ h : ((fun v : V3 => φ v t) '' ({v, w} : Set V3)).Finite, h.toFinset.card = 2
    rw [Set.image_insert_eq, Set.image_singleton]
    refine ⟨(Set.finite_singleton (φ w t)).insert (φ v t), ?_⟩
    rw [← Set.ncard_eq_toFinset_card _
      ((Set.finite_singleton (φ w t)).insert (φ v t))]
    exact Set.ncard_pair hne
  have hf1 : fan1 0 ((fun v : V3 => φ v t) '' V)
      ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) := by
    refine ⟨(hV.image _), ?_⟩
    obtain ⟨v, hv⟩ : V.Nonempty := by
      by_contra hne
      exact hfan.2.2.1.2 (Set.eq_empty_iff_forall_notMem.mpr fun z hz => hne ⟨z, hz⟩)
    intro hempty
    have hmem : φ v t ∈ (fun v : V3 => φ v t) '' V := ⟨v, hv, rfl⟩
    rw [hempty] at hmem
    exact hmem
  have hf2 : fan2 0 ((fun v : V3 => φ v t) '' V)
      ((fun e' : Set V3 => (fun v : V3 => φ v t) '' e') '' E) := by
    intro hv'
    obtain ⟨v, hv, hv0⟩ := hv'
    exact heV t htV v hv hv0
  exact ⟨hcover, hgraph, hf1, hf2, heF t htF⟩

/-- HOL `XRECQNS`: a small deformation of a fan is again a fan.
DISCHARGES: the deformation-path interface consumed by the localization
lane (LocalAuto2.ALL_TO_THE_NONPARALLEL_PART_ALT shape).
NEEDS: `FAN7_SMALL_DEFORMATION_p17` + the fan1/fan2/image-set bookkeeping
(deformation.hl:1011-1036). -/
theorem XRECQNS_p17 (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (f : V3 → ℝ → V3)
    (hdef : Deformation f V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
      FAN (0:V3) ((fun v : V3 => f v t) '' V)
        ((fun e' => (fun v : V3 => f v t) '' e') '' E) := by
  obtain ⟨e7, he7, h7⟩ := FAN7_SMALL_DEFORMATION_p17 V E a b f hdef hfan
  obtain ⟨e0, he0, h0⟩ := w_xrq17_image_fan_data V E a b f hdef hfan
  refine ⟨min e7 e0, lt_min he7 he0, fun t ht1 ht2 => ?_⟩
  have ht : |t| < min e7 e0 := abs_lt.mpr ⟨ht1, ht2⟩
  have hneg : -min e7 e0 < t := (abs_lt.mp ht).1
  have hpos : t < min e7 e0 := (abs_lt.mp ht).2
  have hmine : min e7 e0 ≤ e7 := min_le_left _ _
  have hmin0 : min e7 e0 ≤ e0 := min_le_right _ _
  have ha := h0 t (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hb := h7 t (by linarith) (by linarith)
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2, hb⟩

/-! Coverage note: every EYYPQDW.hl / YRTAFYH.hl / deformation.hl
definition and theorem is carried above (the deformation.hl def
`deformation` via the importable LocalAuto1 `Deformation` + the
`deformationP17` alias).  The mechanical arithmetic/continuity layer is
PROVED; the giant Cayley algebra (`EYYPQDW_NORMV3_p17`,
`EYYPQDW_NORM_V3_V1_p17`, `EYYPQDW_SCALAR_POS_p17`,
`EYYPQDW_p17`) and `lemma_1_p17` — `EYYPQDW_SCALAR_POS_p17`,
`lemma_1_p17`, `EYYPQDW_NORMV3_p17`, `EYYPQDW_NORM_V3_V1_p17` and
`EYYPQDW_p17` PROVED this wave; the NORM pair via the Lagrange /
`cross_dot_cross` identity `normsq_double_cross_p17` + the orthogonal
split `normsq_add_orth_p17`) — fill-wave note: the
`_p17` cross3-linearity/dot-bridge fill kit (`cross3_smul_left_p17`,
`cross3_add_left_p17`, `cross3_sub_left_p17`, `cross3_self_p17`,
`cross3_anticomm_p17`, `cross3_X_smul_p17`, the `dot_*` bridges) is in
place. -/

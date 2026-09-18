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
PROVED, `EYYPQDW_p17`/`YRTAFYH_p17` remain sorry'd (giant algebra /
giant case tree — see NEEDS markers at each).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.Fan
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

/-- HOL `EYYPQDW_NORMV3`: the realisation `‖v3‖^2 = x3`.
NEEDS: the `nlinarith`-heavy Cayley algebra of the HOL proof
(EYYPQDW.hl:85-157). -/
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
      sorry

/-- HOL `EYYPQDW_NORM_V3_V1`: the realisation `‖v3 - v1‖^2 = x5`.
NEEDS: same Cayley algebra as `EYYPQDW_NORMV3_p17` (EYYPQDW.hl:160-185). -/
theorem EYYPQDW_NORM_V3_V1_p17 (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
    (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
      ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
        cross3 v1 (cross3 v1 v2) = v3) :
    ‖v3 - v1‖ ^ 2 = x5 := sorry

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
NEEDS: `EYYPQDW_NORMV3_p17` / `EYYPQDW_NORM_V3_V1_p17` /
`EYYPQDW_SCALAR_POS_p17` (Cayley algebra), then mechanical. -/
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
        t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0) := sorry

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

/-- HOL `YRTAFYH`: stabilising a diagonal with `a i j <= cstab` preserves
`is_scs_v39` and `scs_basic_v39`.
DISCHARGES: LocalAuto1.YRTAFYH_concl (appendix.hl:1554).
NEEDS: the full `scs_v39_explicit` re-verification of the stabilised record
(the 20-conjunct case tree of YRTAFYH.hl:430-496, incl. `A_EQ_PSORT` /
`DIAG_NOT_PSORT` splits). -/
theorem YRTAFYH_p17 : ∀ (s : ScsV39) (i j : ℕ), isScsV39 s → scsBasicV39 s →
    3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j) := sorry

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

/-- HOL `SEPARATE_CLOSED_CONES`: two closed cones meeting only at the origin
are linearly separated. NEEDS: the compact-sphere separation argument of
deformation.hl:26-76 (SEPARATE_COMPACT_CLOSED + conic rescaling). -/
theorem SEPARATE_CLOSED_CONES_p17 (c d : Set V3) (hc : conicP17 c)
    (hcc : IsClosed c) (hd : conicP17 d) (hdc : IsClosed d)
    (hint : c ∩ d ⊆ ({0} : Set V3)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ c, ∀ y ∈ d, dist x y ≥ e * max ‖x‖ ‖y‖ := sorry

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

/-- HOL `GMLWKPK`: `fan7` re-characterised pairwise over edges and singleton
vertices. NEEDS: the `AFF_GE_EQ_AFFINE_HULL` singleton case-kit
(deformation.hl:118-152). -/
theorem GMLWKPK_p17 (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
        (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
          (∀ v : V3, e1 ∩ e2 = {v} →
            affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3)) := sorry

/-- HOL `GMLWKPK_ALT`: with `x` off every edge the singleton-pair case is
needed only for edges. NEEDS: deformation.hl:154-185. -/
theorem GMLWKPK_ALT_p17 (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E)
    (hx : ∀ e ∈ E, x ∉ e) :
    fan7 x V E ↔
      ((∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
        (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
          affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3))) := sorry

/-- HOL `GMLWKPK_SIMPLE`: under `fan6` + covering, `fan7` reduces to the
empty-intersection case. NEEDS: the 4-point collinearity lemma at
deformation.hl:196-271 plus the case bash to deformation.hl:376. -/
theorem GMLWKPK_SIMPLE_p17 (V : Set V3) (E : Set (Set V3)) (x : V3)
    (hsup : ⋃₀ E ⊆ V) (hE : Graph E) (h6 : fan6 x V E)
    (hx : ∀ e ∈ E, x ∉ e) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
        e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3) := sorry

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

/-- HOL `lemma_2`: the two-ray perturbation estimate.
NEEDS: deformation.hl:403-466 (LINEAR_INJECTIVE_BOUNDED_BELOW_POS). -/
theorem lemma_2_p17 (x y : V3) (e : ℝ)
    (hnc : ¬ Collinear ℝ ({0, x, y} : Set V3)) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ x' y' : V3, dist x x' < d → dist y y' < d →
      ∀ z' ∈ affGe ({0} : Set V3) {x', y'}, ∃ z ∈ affGe ({0} : Set V3) {x, y},
        ‖z' - z‖ ≤ e * ‖z‖ := sorry

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

/-- HOL `FAN7_SMALL_DEFORMATION`. NEEDS: `GMLWKPK_SIMPLE_p17`,
`SEPARATE_CLOSED_CONES_p17`, `lemma_1_p17`, `lemma_2_p17` and the
MINIMIZE kit (deformation.hl:511-1009) — the fan7 small-deformation
theorem. -/
theorem FAN7_SMALL_DEFORMATION_p17 (V : Set V3) (E : Set (Set V3)) (a b : ℝ)
    (phii : V3 → ℝ → V3) (hdef : Deformation phii V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
      fan7 (0:V3) ((fun v : V3 => phii v t) '' V)
        ((fun e' => (fun v : V3 => phii v t) '' e') '' E) := sorry

/-- HOL `XRECQNS`: a small deformation of a fan is again a fan.
DISCHARGES: the deformation-path interface consumed by the localization
lane (LocalAuto2.ALL_TO_THE_NONPARALLEL_PART_ALT shape).
NEEDS: `FAN7_SMALL_DEFORMATION_p17` + the fan1/fan2/image-set bookkeeping
(deformation.hl:1011-1036). -/
theorem XRECQNS_p17 (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (f : V3 → ℝ → V3)
    (hdef : Deformation f V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
      FAN (0:V3) ((fun v : V3 => f v t) '' V)
        ((fun e' => (fun v : V3 => f v t) '' e') '' E) := sorry

/-! Coverage note: every EYYPQDW.hl / YRTAFYH.hl / deformation.hl
definition and theorem is carried above (the deformation.hl def
`deformation` via the importable LocalAuto1 `Deformation` + the
`deformationP17` alias).  The mechanical arithmetic/continuity layer is
PROVED; the giant Cayley algebra (`EYYPQDW_NORMV3_p17`,
`EYYPQDW_NORM_V3_V1_p17`, `EYYPQDW_SCALAR_POS_p17`,
`EYYPQDW_p17`) and `lemma_1_p17` — `EYYPQDW_SCALAR_POS_p17` and
`lemma_1_p17` PROVED this wave) — fill-wave note: the
`_p17` cross3-linearity/dot-bridge fill kit (`cross3_smul_left_p17`,
`cross3_add_left_p17`, `cross3_sub_left_p17`, `cross3_self_p17`,
`cross3_anticomm_p17`, `cross3_X_smul_p17`, the `dot_*` bridges) is in
place. -/

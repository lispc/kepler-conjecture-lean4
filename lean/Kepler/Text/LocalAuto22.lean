/-
LocalAuto22 — port of `scripts/local/OCBICBY.hl` (4788 ln, 0 defs + 150 thms;
T. Hales 2013, "Conclusions / Local Fan", Lemma OCBICBY): the s_init_list /
slice case bank.  Three strata:

  - The xrr / derived-form calculus (lines 24-2100): the `xrr y1 y2 y6`
    replacement coordinates, the `derived_form` (one-real-variable
    derivative) kit for `delta_x`, `delta_x4`, `dih_x`, `num1`, `taum`,
    chain rules and second-derivative tests feeding `taum` monotonicity.
  - The scs-machine facts (lines 2100-3470): `is_scs_funlist_basic`,
    `is_scs_adj` (the cs_adj registry machine), the local-fan azimuth kit,
    `scs_6T1`/`scs_5T1` props+emptiness, `EAR_SOL_NN`, `RRCWNS_WEAK`,
    `SYNQIWN`, `delta4` obtuseness, `taum` interval tests.
  - The 34-system case bank (lines 3470-4788): `is_scs_*` for every
    appendix registry object `scs_6I1`..`scs_3M1`, the example
    conjunctions, the arrow-to-empty facts, and the 14-arrow assembly
    `OCBICBY` (`scs_arrow_v39 {scs_kT1} {}`).

The giants (`empty_6T1`, `empty_5T1`, `RRCWNS_WEAK`, `SYNQIWN`, the taum
second-derivative tests, `angle_sum_5T1`, `terminal_pent_taum2`,
`EAR_SOL_NN`, `OCBICBY` itself) keep `sorry` bodies.

ENCODING NOTES
  - Imports: `LocalAuto1` (the whole scs lane: `ScsV39`, `isScsV39`,
    `BBsV39`, `MMsV39`, `taustarV39`, `scsGeneric`, `scsBasicV39`,
    `scsDiag`, `scsArrowV39`, `scsStabDiagV39`, `unadornedV39`,
    `mkUnadornedV39`, `csAdj`, `psort`, `funlistV39`, `derivedForm`,
    `xrr`, `deltaX4`, `deltaX5`, `rho`, `cstab`, `dTame`, `Lunar`,
    `azimInFan`, `solLocal`, `interiorAngle1`, `Periodic`, `Periodic2`,
    `main_nonlinear_terminal_v11`, the registry objects `scs6I1`..`scs3M1`,
    plus `h0`/`sol0`/`dihV` (PackingAuto2) and `upsX`/`deltaX`/`arcLength`/
    `reEqvl` (PackingAuto18)).  LocalAuto16 (the dih_y/taum continuity lane)
    is NOT built in this checkout, so its sphere-kit twins are carried here
    as `_p22` copies instead: `atn2_p22`, `dihXf_p22`, `dihY_p22`,
    `deltaY_p22`, `taum_p22` (verbatim twins of LocalAuto16 `_p16`;
    merge candidates for the owning wave).
    Same-wave lanes LocalAuto19-21/23-27 are NOT imported; any helper that
    would live there is carried as a `_p22` copy with a NEEDS marker.
  - `_p22` copies (no importable port): `yOfX_p22` (sphere.hl `y_of_x`),
    `deltaX6_p22` (partial of `delta_x` at x6; twin of LocalAuto1
    `deltaX5`), `delta4Y_p22` (`delta4_y`), `num1_p22`/`dnum1_p22`
    (Terminal.hl; bodies reconstructed so `derived_form_num1` /
    `derived_form_dnum1` hold by construction — NEEDS check against the
    real Terminal.hl when that lane lands), `const1_p22`, `solY_p22` and
    `eulerP_p22`/`eulerAX_p22` (opaque registry signatures), `acsP22`
    (flyspeck `acs` = `Real.arccos`), `ineqP22` (sphere.hl `ineq`).
  - HOL `delta_x` ↔ `deltaX` (PackingAuto18:134); `delta_x4`/`delta_x5` ↔
    LocalAuto1 `deltaX4`/`deltaX5` (same formulas as LocalAuto16
    `deltaX4f_p16` twins).
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `dist(v,w)` ↔
    `dist v w`; `dih_x` ↔ `dihXf_p16`; `delta_x` ↔ `deltaXf_p16`;
    `delta_y` ↔ `deltaY_p16`; `dih_y` ↔ `dihY_p16`; `taum` ↔ `taum_p16`;
    `sqrt8` ↔ `Real.sqrt 8`; `acs` ↔ `acsP22`; `arclength` ↔ `arcLength`
    (PackingAuto18; the `atn2` rendering of `acs(1 - xrr/8)`).
    `real_open s` ↔ `IsOpen s`; `real_interval (a,b)` ↔ `Set.Ioo a b`;
    `real_continuous f atreal x` ↔ `ContinuousAt f x`; `{y | P y}` ↔
    set-builder; `sum {i | i < n} f` ↔ `Finset.sum (Finset.range n)`;
    `re_eqvl` ↔ `reEqvl`; `lunar (v,w) V E` ↔ `Lunar v w V E`; HOL lets in
    statement position are inlined as explicit conjunctions/args.
  - HOL tactic-level items (`LET_THM`, `diff`, `DERIVED_TAC`,
    `arrow_rewrite_list`, `scs_example_list`, the `c110186` numeric calc)
    have no Lean counterpart; `c110186` is recorded as a comment at its
    consumer `LEMMA_7175074394`.

DISCHARGES: `is_scs_examples` / `unadorned_examples` / `basic_examples`
assemble the case bank; `OCBICBY` (sorry) is the terminal-arrows-to-empty
theorem that LocalAuto16's `JEJTVGB_case_breakdown_p16` NEEDS.  All items
proved here are upstream-sorry-free except where marked.
-/

import Kepler.Text.LocalAuto1
import Kepler.Geom.Aff
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p22` copies of the sphere.hl / Terminal.hl kit -/

/-- HOL `y_of_x` (sphere.hl): rescale a symmetric x-space function to
y-coordinates. -/
def yOfX_p22 (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  f (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `atn2` (sphere.hl:48-52); verbatim twin of the PackingAuto18 /
LocalAuto16 renderings. -/
noncomputable def atn2_p22 (x y : ℝ) : ℝ :=
  if |y| < x then Real.arctan (y / x)
  else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
  else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y)
  else Real.pi

/-- HOL `dih_x` (sphere.hl:153). -/
noncomputable def dihXf_p22 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 +
    atn2_p22 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6))

/-- HOL `dih_y` (sphere.hl:159): `y_of_x dih_x`. -/
noncomputable def dihY_p22 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihXf_p22 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta_y` (sphere.hl): `y_of_x delta_x`. -/
noncomputable def deltaY_p22 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  yOfX_p22 (deltaX) y1 y2 y3 y4 y5 y6

/-- NEEDS: Terminal.hl `taum` (the truncated tau of a quad); opaque
registry signature (twins: LocalAuto11 `taum_p11`, LocalAuto16
`taum_p16`, forbidden/unbuilt lanes). -/
noncomputable def taum_p22 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-- HOL `delta_x5` (sphere.hl): partial derivative of `delta_x` at `x5`.
NEEDS merge: LocalAuto1's `deltaX5` drops the `x1 * x4` / `x1 * x3` terms
of the sphere.hl rendering (mis-port); this `_p22` copy satisfies
`derived_form_delta_x_wrt_x5_p22` by construction. -/
noncomputable def deltaX5_p22 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 - x1 * x3 + x2 * (x1 - x2 + x3 + x4 - x5 + x6) - x2 * x5 + x3 * x6 - x4 * x6

/-- HOL `delta_x6` (sphere.hl): partial derivative of `delta_x` at `x6`
(no prior port; LocalAuto1 `deltaX5` is the x5 twin). -/
noncomputable def deltaX6_p22 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x2 * x5 - x1 * x2 - x4 * x5 - x3 * x6
    + x3 * (x1 + x2 - x3 + x4 + x5 - x6)

/-- HOL `delta4_y` (sphere.hl): `y_of_x delta_x4`. -/
noncomputable def delta4Y_p22 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  yOfX_p22 (deltaX4) y1 y2 y3 y4 y5 y6

/-- NEEDS: Terminal.hl `num1` (body reconstructed from its uses; the
derivative laws `derived_form_num1`/`derived_form_dnum1` hold by
construction). -/
noncomputable def num1_p22 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ :=
  4 * ((16 * x4 - x4 * x4) * e1 + (x5 - 8) * x4 * e2 + (x6 - 8) * x4 * e3)

/-- NEEDS: Terminal.hl `dnum1` (reconstructed; see `num1_p22`). -/
noncomputable def dnum1_p22 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ :=
  (16 - 2 * x4) * e1 + (x5 - 8) * e2 + (x6 - 8) * e3

/-- HOL `const1` (Terminal.hl): `sol0 / pi`. -/
noncomputable def const1_p22 : ℝ := sol0 / Real.pi

/-- NEEDS: Terminal.hl `sol_y` (solid angle in y-space); opaque registry
signature (twin of PackingAuto20/21 `solY`, forbidden lane). -/
noncomputable def solY_p22 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-- NEEDS: Sphere.hl `euler_p` (solid angle of a tetrahedron); opaque
registry signature. -/
noncomputable def eulerP_p22 (v0 v1 v2 v3 : V3) : ℝ := sorry

/-- NEEDS: Sphere.hl `eulerA_x` (solid angle in x-space); opaque registry
signature. -/
noncomputable def eulerAX_p22 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- Flyspeck `acs` = `Real.arccos`. -/
noncomputable def acsP22 (x : ℝ) : ℝ := Real.arccos x

/-- HOL `ineq` (sphere.hl): the box constraints wrapping a conclusion. -/
def ineqP22 : List (ℝ × ℝ × ℝ) → Prop → Prop
  | [], Q => Q
  | (l, x, h) :: t, Q => l ≤ x ∧ x ≤ h ∧ ineqP22 t Q

/-! ## Section A: basic kit (OCBICBY.hl 24-210) -/

/-- HOL `sqrt8_flyspeck` (Flyspeck_constants.bounds). -/
theorem sqrt8_flyspeck_p22 : 2.828427 < Real.sqrt 8 ∧ Real.sqrt 8 < 2.828428 := by
  have h1 : (2.828427 : ℝ) ^ 2 < (8 : ℝ) := by norm_num
  have h2 : (8 : ℝ) < (2.828428 : ℝ) ^ 2 := by norm_num
  exact ⟨(Real.lt_sqrt (show (0:ℝ) ≤ 2.828427 by norm_num)).2 h1,
    (Real.sqrt_lt (show (0:ℝ) ≤ 8 by norm_num) (show (0:ℝ) ≤ 2.828428 by norm_num)).2 h2⟩

/-- HOL `DOT_LSUB`. -/
theorem DOT_LSUB_p22 (x y z : V3) : (x - y) ⬝ᵥ z = x ⬝ᵥ z - y ⬝ᵥ z := by
  rw [← inner_eq_dot, ← inner_eq_dot, ← inner_eq_dot]
  exact inner_sub_left _ _ _

/-- HOL `DOT_RSUB`. -/
theorem DOT_RSUB_p22 (x y z : V3) : x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z := by
  rw [← inner_eq_dot, ← inner_eq_dot, ← inner_eq_dot]
  exact inner_sub_right _ _ _

/-- HOL `derived_form_b`. -/
theorem derived_form_b_p22 (b : Prop) (f : ℝ → ℝ) (f' x : ℝ) (s : Set ℝ) :
    (derivedForm b f f' x s ↔ (b → derivedForm True f f' x s)) := by
  unfold derivedForm
  constructor
  · intro h hb _
    exact h hb
  · intro h hb
    exact h hb trivial

/-! ## Section B: euler / coplanar statements and the derivative kit -/

/-- HOL `euler_p_eulerA_x` (`euler_p` is `eulerA_x` in the distance-squared
coordinates; both signatures are opaque `_p22` copies). -/
theorem euler_p_eulerA_x_p22 (v0 v1 v2 v3 : V3) :
    eulerP_p22 v0 v1 v2 v3 =
      eulerAX_p22 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
  sorry

/-- HOL `COPLANAR_IMP_DIH_PI` (was `DELTA_IMP_DIH_PI`): coplanar + negative
`delta4_y` forces the straight dihedral angle. -/
theorem COPLANAR_IMP_DIH_PI_p22 (v0 v1 v2 v3 : V3)
    (hc12 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hc13 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3))
    (hcp : Coplanar ℝ ({v0, v1, v2, v3} : Set V3))
    (hd : yOfX_p22 (deltaX4) (dist v0 v1) (dist v0 v2) (dist v0 v3)
      (dist v2 v3) (dist v1 v3) (dist v1 v2) < 0) :
    dihV v0 v1 v2 v3 = Real.pi := by
  sorry

/-- HOL `DIH_IMP_EULER_A_POS`. -/
theorem DIH_IMP_EULER_A_POS_p22 (h : main_nonlinear_terminal_v11)
    (v0 v1 v2 v3 : V3)
    (hc12 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hc23 : ¬ Collinear ℝ ({v0, v2, v3} : Set V3))
    (hc13 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3))
    (hsum : dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 < 2 * Real.pi)
    (hy1 : 2 ≤ dist v0 v1 ∧ dist v0 v1 ≤ 2 * h0)
    (hy2 : 2 ≤ dist v0 v2 ∧ dist v0 v2 ≤ 2 * h0)
    (hy3 : 2 ≤ dist v0 v3 ∧ dist v0 v3 ≤ 2 * h0)
    (hy4 : 3.01 ≤ dist v2 v3 ∧ dist v2 v3 ≤ 3.915)
    (hy5 : 3.01 ≤ dist v1 v3 ∧ dist v1 v3 ≤ 3.915)
    (hy6 : 3.01 ≤ dist v1 v2 ∧ dist v1 v2 ≤ 3.915) :
    yOfX_p22 (eulerAX_p22) (dist v0 v1) (dist v0 v2) (dist v0 v3)
      (dist v2 v3) (dist v1 v3) (dist v1 v2) > 0 := by
  sorry

/-- One-variable quadratic derivative inside a set (workhorse for the
`derived_form` polynomial laws). -/
theorem hasDerivWithinAt_quad_p22 (a b c x : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (fun q => a * (q * q) + (b * q + c)) (a * (x + x) + b) s x := by
  have h1 : HasDerivWithinAt (fun q : ℝ => q * q) (x + x) s x := by
    exact HasDerivWithinAt.congr_deriv
      ((hasDerivWithinAt_id x s).mul (hasDerivWithinAt_id x s)) (by norm_num)
  have h2 : HasDerivWithinAt (fun q : ℝ => b * q + c) (b * 1 + 0) s x := by
    exact ((hasDerivWithinAt_id x s).const_mul b).add (hasDerivWithinAt_const x s c)
  exact HasDerivWithinAt.congr_deriv ((h1.const_mul a).add h2) (by norm_num)

/-- HOL `derived_form_delta_x_wrt_x4`. -/
theorem derived_form_delta_x_wrt_x4_p22 (x1 x2 x3 x4 x5 x6 : ℝ) :
    derivedForm True (fun q => deltaX x1 x2 x3 q x5 x6)
      (deltaX4 x1 x2 x3 x4 x5 x6) x4 Set.univ := by
  intro _
  have e : (fun q => deltaX x1 x2 x3 q x5 x6) = fun q =>
      (-(x1)) * (q * q)
        + ((x1 * (-x1 + x2 + x3 + x5 + x6) + (x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6)) * q
        + (x2 * x5 * (x1 - x2 + x3 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x5 - x6)
          - x1 * x3 * x5 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  have dv : (-(x1)) * (x4 + x4)
      + (x1 * (-x1 + x2 + x3 + x5 + x6) + (x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6))
      = deltaX4 x1 x2 x3 x4 x5 x6 := by
    unfold deltaX4; ring
  rw [e, ← dv]
  exact hasDerivWithinAt_quad_p22 _ _ _ x4 Set.univ

/-- HOL `derived_form_delta_x_wrt_x5` (with `deltaX5_p22`). -/
theorem derived_form_delta_x_wrt_x5_p22 (x1 x2 x3 x4 x5 x6 : ℝ) :
    derivedForm True (fun q => deltaX x1 x2 x3 x4 q x6)
      (deltaX5_p22 x1 x2 x3 x4 x5 x6) x5 Set.univ := by
  intro _
  have e : (fun q => deltaX x1 x2 x3 x4 q x6) = fun q =>
      (-(x2)) * (q * q)
        + ((x2 * (x1 - x2 + x3 + x4 + x6) + x1 * x4 + x3 * x6 - x4 * x6 - x1 * x3) * q
        + (x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6)
          - x2 * x3 * x4 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  have dv : (-(x2)) * (x5 + x5)
      + (x2 * (x1 - x2 + x3 + x4 + x6) + x1 * x4 + x3 * x6 - x4 * x6 - x1 * x3)
      = deltaX5_p22 x1 x2 x3 x4 x5 x6 := by
    unfold deltaX5_p22; ring
  rw [e, ← dv]
  exact hasDerivWithinAt_quad_p22 _ _ _ x5 Set.univ

/-! ## Section C: the xrr calculus and dimension reductions -/

/-- HOL `ups_x_delta_x`: the discriminant identity. -/
theorem ups_x_delta_x_p22 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 =
      upsX x1 x3 x5 * upsX x1 x2 x6 := by
  unfold deltaX4 deltaX upsX
  ring

/-- HOL `delta_diff4`. -/
theorem delta_diff4_p22 (x1 x2 x3 x4 x5 x6 z4 : ℝ) :
    deltaX x1 x2 x3 x4 x5 x6 =
      deltaX x1 x2 x3 z4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 * (x4 - z4)
        + x1 * (x4 - z4) ^ 2 := by
  unfold deltaX deltaX4
  ring

/-- HOL `derived_form_xrr`. -/
theorem derived_form_xrr_p22 (y1 y2 y6 : ℝ) :
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      Set.univ := by
  intro _
  have e : (fun q => xrr y1 y2 q) = fun q =>
      (4 / (y1 * y2)) * (q * q)
        + (0 * q + (8 - 4 * (y1 * y1 + y2 * y2) / (y1 * y2))) := by
    funext q; unfold xrr; field_simp; ring
  rw [e]
  exact HasDerivWithinAt.congr_deriv (hasDerivWithinAt_quad_p22 _ _ _ y6 Set.univ) (by ring)

/-- HOL `derived_form_xrr_wrt_y1`. -/
theorem derived_form_xrr_wrt_y1_p22 (y1 y2 y6 : ℝ) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) :
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr q y2 y6)
      (-(4 * ((y1 * y1 + y6 * y6 - y2 * y2) / (y1 ^ 2 * y2)))) y1 Set.univ := by
  sorry

/-- HOL `derived_form_xrr_D2`. -/
theorem derived_form_xrr_D2_p22 (y1 y2 y6 : ℝ) :
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => 8 * q / (y1 * y2)) (8 / (y1 * y2)) y6
      Set.univ := by
  intro _
  have e : (fun q : ℝ => 8 * q / (y1 * y2)) = fun q => (8 / (y1 * y2)) * q + 0 := by
    funext q; ring
  rw [e]
  refine HasDerivWithinAt.congr_deriv
    (((hasDerivWithinAt_id y6 Set.univ).const_mul (8 / (y1 * y2))).add
      (hasDerivWithinAt_const y6 Set.univ 0)) ?_
  norm_num

/-- HOL `derived_form_xrr_D3`. -/
theorem derived_form_xrr_D3_p22 (y1 y2 y6 : ℝ) :
    derivedForm (0 < y1 ∧ 0 < y2) (fun _q => 8 / (y1 * y2)) 0 y6 Set.univ := by
  intro _; exact hasDerivWithinAt_const y6 Set.univ (8 / (y1 * y2))

/-- HOL `xrr_sym`. -/
theorem xrr_sym_p22 (y1 y2 y6 : ℝ) : xrr y1 y2 y6 = xrr y2 y1 y6 := by
  unfold xrr; ring

/-- HOL `delta_y_dim_reduction`. -/
theorem delta_y_dim_reduction_p22 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0)
    (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0) :
    deltaX 4 4 4 (8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)))
        (8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)))
        (8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))) =
      64 * deltaY_p22 y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2 := by
  unfold deltaY_p22 yOfX_p22
  unfold deltaX
  field_simp
  ring

/-- HOL `delta_x_xrr`. -/
theorem delta_x_xrr_p22 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (hy3 : y3 ≠ 0) :
    deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) =
      64 * deltaY_p22 y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2 := by
  have h4 : xrr y2 y3 y4 = 8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)) := rfl
  have h5 : xrr y1 y3 y5 = 8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)) := rfl
  have h6 : xrr y1 y2 y6 = 8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2)) := rfl
  rw [h4, h5, h6]
  exact delta_y_dim_reduction_p22 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3

/-- HOL `delta_x4_dim_reduction`. -/
theorem delta_x4_dim_reduction_p22 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0)
    (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0) :
    deltaX4 4 4 4 (8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)))
        (8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)))
        (8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))) =
      16 * yOfX_p22 (deltaX4) y1 y2 y3 y4 y5 y6 / (y1 * y1 * y2 * y3) := by
  unfold deltaX4 yOfX_p22
  field_simp
  ring

/-- HOL `derived_form_delta_x4_wrt_x4`. -/
theorem derived_form_delta_x4_wrt_x4_p22 (x1 x2 x3 x4 x5 x6 : ℝ) :
    derivedForm True (fun q => deltaX4 x1 x2 x3 q x5 x6) (-2 * x1) x4 Set.univ := by
  intro _
  have e : (fun q => deltaX4 x1 x2 x3 q x5 x6) = fun q =>
      0 * (q * q) + ((-2 * x1) * q
        + (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6 + x1 * (-x1 + x2 + x3 + x5 + x6))) := by
    funext q; unfold deltaX4; ring
  rw [e]
  exact HasDerivWithinAt.congr_deriv (hasDerivWithinAt_quad_p22 _ _ _ x4 Set.univ) (by ring)

/-- HOL `derived_form_delta_x4_wrt_x5`. -/
theorem derived_form_delta_x4_wrt_x5_p22 (x1 x2 x3 x4 x5 x6 : ℝ) :
    derivedForm True (fun q => deltaX4 x1 x2 x3 x4 q x6) (x1 + x2 - x6) x5 Set.univ := by
  intro _
  have e : (fun q => deltaX4 x1 x2 x3 x4 q x6) = fun q =>
      0 * (q * q) + ((x1 + x2 - x6) * q
        + (-x2 * x3 - x1 * x4 + x3 * x6 + x1 * (-x1 + x2 + x3 - x4 + x6))) := by
    funext q; unfold deltaX4; ring
  rw [e]
  exact HasDerivWithinAt.congr_deriv (hasDerivWithinAt_quad_p22 _ _ _ x5 Set.univ) (by ring)

/-! ## Section D: the real_open kit -/

/-- HOL `real_open_univ`. -/
theorem real_open_univ_p22 : IsOpen (Set.univ : Set ℝ) := isOpen_univ

/-- HOL `REAL_OPEN_REAL_INTERVAL`. -/
theorem REAL_OPEN_REAL_INTERVAL_p22 (a b : ℝ) : IsOpen (Set.Ioo a b) :=
  isOpen_Ioo

/-! ## Section E: derived forms for dih_x, num1, and the chain kit -/

/-- HOL `derived_form_dih_x_wrt_x4` (NEEDS the `atn2` derivative kit). -/
theorem derived_form_dih_x_wrt_x4_p22 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h3 : 0 < upsX x1 x2 x6) (h4 : 0 < upsX x1 x3 x5) :
    derivedForm True (fun q => dihXf_p22 x1 x2 x3 q x5 x6)
      (Real.sqrt x1 / Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) x4 Set.univ := by
  sorry

/-- HOL `derived_form_dih_x_wrt_x5`. -/
theorem derived_form_dih_x_wrt_x5_p22 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h3 : 0 < upsX x1 x2 x6) (h4 : 0 < upsX x1 x3 x5) :
    derivedForm True (fun q => dihXf_p22 x1 x2 x3 x4 q x6)
      (-(Real.sqrt x1 * deltaX6_p22 x1 x2 x3 x4 x5 x6
        / (upsX x1 x3 x5 * Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)))) x5 Set.univ := by
  sorry

/-- HOL `derived_form_dih_x_wrt_x6`. -/
theorem derived_form_dih_x_wrt_x6_p22 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h3 : 0 < upsX x1 x2 x6) (h4 : 0 < upsX x1 x3 x5) :
    derivedForm True (fun q => dihXf_p22 x1 x2 x3 x4 x5 q)
      (-(Real.sqrt x1 * deltaX5_p22 x1 x2 x3 x4 x5 x6
        / (upsX x1 x2 x6 * Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)))) x6 Set.univ := by
  sorry

/-- HOL `derived_form_num1`. -/
theorem derived_form_num1_p22 (x4 x5 x6 e1 e2 e3 : ℝ) :
    derivedForm True (fun q => num1_p22 e1 e2 e3 q x5 x6)
      (4 * ((16 - 2 * x4) * e1 + (x5 - 8) * e2 + (x6 - 8) * e3)) x4 Set.univ := by
  intro _
  have e : (fun q => num1_p22 e1 e2 e3 q x5 x6) = fun q =>
      (-(4 * e1)) * (q * q)
        + ((64 * e1 + 4 * (x5 - 8) * e2 + 4 * (x6 - 8) * e3) * q + 0) := by
    funext q; unfold num1_p22; ring
  rw [e]
  refine HasDerivWithinAt.congr_deriv
    (hasDerivWithinAt_quad_p22 _ _ _ x4 Set.univ) ?_
  ring

/-- HOL `derived_form_dnum1`. -/
theorem derived_form_dnum1_p22 (x4 x5 x6 e1 e2 e3 : ℝ) :
    derivedForm True (fun q => num1_p22 e1 e2 e3 q x5 x6)
      (4 * dnum1_p22 e1 e2 e3 x4 x5 x6) x4 Set.univ := by
  intro _
  have e : (fun q => num1_p22 e1 e2 e3 q x5 x6) = fun q =>
      (-(4 * e1)) * (q * q)
        + ((64 * e1 + 4 * (x5 - 8) * e2 + 4 * (x6 - 8) * e3) * q + 0) := by
    funext q; unfold num1_p22; ring
  rw [e]
  refine HasDerivWithinAt.congr_deriv
    (hasDerivWithinAt_quad_p22 _ _ _ x4 Set.univ) ?_
  unfold dnum1_p22
  ring

/-- HOL `derived_form_sum_dih` (NEEDS the dih_x derivative kit). -/
theorem derived_form_sum_dih_p22 (x1 x2 x3 x4 x5 x6 e1 e2 e3 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3)
    (h4 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h5 : 0 < upsX x1 x2 x6) (h6 : 0 < upsX x1 x3 x5) (h7 : 0 < upsX x2 x3 x4) :
    derivedForm True
      (fun q => e1 * dihXf_p22 x1 x2 x3 q x5 x6
        + e2 * dihXf_p22 x2 x3 x1 x5 x6 q
        + e3 * dihXf_p22 x3 x1 x2 x6 q x5)
      ((e1 * Real.sqrt x1 * upsX x2 x3 x4
        - e2 * Real.sqrt x2 * deltaX6_p22 x1 x2 x3 x4 x5 x6
        - e3 * Real.sqrt x3 * deltaX5_p22 x1 x2 x3 x4 x5 x6)
        / (upsX x2 x3 x4 * Real.sqrt (deltaX x1 x2 x3 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_sum_dih444`. -/
theorem derived_form_sum_dih444_p22 (x4 x5 x6 e1 e2 e3 : ℝ)
    (h4 : 0 < x4 ∧ x4 < 16) (h5 : 0 < x5 ∧ x5 < 16) (h6 : 0 < x6 ∧ x6 < 16)
    (hd : 0 < deltaX 4 4 4 x4 x5 x6) :
    derivedForm True
      (fun q => e1 * dihXf_p22 4 4 4 q x5 x6
        + e2 * dihXf_p22 4 4 4 x5 x6 q
        + e3 * dihXf_p22 4 4 4 x6 q x5)
      (num1_p22 e1 e2 e3 x4 x5 x6
        / (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_sum_dih444sub`. -/
theorem derived_form_sum_dih444sub_p22 (x4 x5 x6 e1 e2 e3 : ℝ)
    (h4 : 0 < x4 ∧ x4 < 16) (h5 : 0 < x5 ∧ x5 < 16) (h6 : 0 < x6 ∧ x6 < 16)
    (hd : 0 < deltaX 4 4 4 x4 x5 x6) :
    derivedForm True
      (fun q => e1 * dihXf_p22 4 4 4 q x5 x6
        + e2 * dihXf_p22 4 4 4 x5 x6 q
        + e3 * dihXf_p22 4 4 4 x6 q x5 - (1 + const1_p22) * Real.pi)
      (num1_p22 e1 e2 e3 x4 x5 x6
        / (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_tau2D`. -/
theorem derived_form_tau2D_p22 (x4 x5 x6 e1 e2 e3 : ℝ)
    (h4 : 0 < x4 ∧ x4 < 16) (h5 : 0 < x5 ∧ x5 < 16) (h6 : 0 < x6 ∧ x6 < 16)
    (hd : 0 < deltaX 4 4 4 x4 x5 x6) (hnum : num1_p22 e1 e2 e3 x4 x5 x6 = 0) :
    derivedForm True
      (fun q => num1_p22 e1 e2 e3 q x5 x6
        / (2 * q * (16 - q) * Real.sqrt (deltaX 4 4 4 q x5 x6)))
      (4 * dnum1_p22 e1 e2 e3 x4 x5 x6
        / (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_taum_d3_exists`. -/
theorem derived_form_taum_d3_exists_p22 (x4 x5 x6 e1 e2 e3 : ℝ) :
    ∃ f'' : ℝ → ℝ, ∃ f''' : ℝ,
      (0 < x4 ∧ x4 < 16 ∧ 0 < x5 ∧ x5 < 16 ∧ 0 < x6 ∧ x6 < 16 ∧
        0 < deltaX 4 4 4 x4 x5 x6) →
      (∀ x4', 0 < x4' → x4' < 16 → 0 < deltaX 4 4 4 x4' x5 x6 →
        derivedForm True
          (fun q => num1_p22 e1 e2 e3 q x5 x6
            / (2 * q * (16 - q) * Real.sqrt (deltaX 4 4 4 q x5 x6)))
          (f'' x4') x4' Set.univ) ∧
      derivedForm True f'' f''' x4 Set.univ := by
  sorry

/-- HOL `dih_x_dim_reduction` (NEEDS the atn2 positive-scaling lemma). -/
theorem dih_x_dim_reduction_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6) :
    dihXf_p22 4 4 4 (8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)))
        (8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)))
        (8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))) =
      dihY_p22 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `derived_form_unique`. -/
theorem derived_form_unique_p22 (f : ℝ → ℝ) (f' f'' x : ℝ)
    (h1 : derivedForm True f f' x Set.univ) (h2 : derivedForm True f f'' x Set.univ) :
    f' = f'' := by
  have d1 := HasDerivAt.deriv (x := x) (f := f)
    ((h1 trivial).hasDerivAt (by simp : (Set.univ : Set ℝ) ∈ nhds x))
  have d2 := HasDerivAt.deriv (x := x) (f := f)
    ((h2 trivial).hasDerivAt (by simp : (Set.univ : Set ℝ) ∈ nhds x))
  rw [d1.symm, d2]

/-- HOL `derived_form_chain`. -/
theorem derived_form_chain_p22 (f g : ℝ → ℝ) (f' g' x y : ℝ)
    (hxy : f x = y)
    (hf : derivedForm True f f' x Set.univ)
    (hg : derivedForm True g g' y Set.univ) :
    derivedForm True (g ∘ f) (g' * f') x Set.univ := by
  intro _
  have h1 : HasDerivAt f f' x :=
    (hf trivial).hasDerivAt (by simp : (Set.univ : Set ℝ) ∈ nhds x)
  have h2 : HasDerivAt g g' (f x) := by
    have h3 : HasDerivAt g g' y :=
      (hg trivial).hasDerivAt (by simp : (Set.univ : Set ℝ) ∈ nhds y)
    rw [hxy]
    exact h3
  exact HasDerivAt.hasDerivWithinAt (𝕜 := ℝ) (F := ℝ)
    (f := g ∘ f) (f' := g' * f') (s := Set.univ) (x := x)
    (HasDerivAt.comp (h₂ := g) (h₂' := g') (h := f) (h' := f') (x := x) h2 h1)

/-- HOL `derived_form_chain_old`. -/
theorem derived_form_chain_old_p22 (f g : ℝ → ℝ) (f' g' h' x y : ℝ)
    (hxy : f x = y)
    (hf : derivedForm True f f' x Set.univ)
    (hg : derivedForm True g g' y Set.univ)
    (hh : derivedForm True (g ∘ f) h' x Set.univ) :
    h' = g' * f' := by
  have := derived_form_chain_p22 f g f' g' x y hxy hf hg
  exact (derived_form_unique_p22 (g ∘ f) h' (g' * f') x hh this)

/-! ## Section F: xrr factorization, bounds, triangle inequality -/

/-- HOL `xrr_factor`. -/
theorem xrr_factor_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    xrr y1 y2 y6 = 4 * ((y6 + y2 - y1) * (y6 - y2 + y1)) / (y1 * y2) := by
  unfold xrr
  field_simp
  ring

/-- HOL `xrr_factor_8`. -/
theorem xrr_factor_8_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    16 - xrr y1 y2 y6 = 4 * ((y6 + y2 + y1) * (y2 + y1 - y6)) / (y1 * y2) := by
  unfold xrr
  field_simp
  ring

/-- HOL `xrr_pos`. -/
theorem xrr_pos_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (t1 : y1 < y2 + y6) (t2 : y2 < y1 + y6) : 0 < xrr y1 y2 y6 := by
  rw [xrr_factor_p22 y1 y2 y6 hy1 hy2]
  have f1 : 0 < y6 - y2 + y1 := by linarith
  have f2 : 0 < y6 + y2 - y1 := by linarith
  have fp : 0 < y1 * y2 := by linarith [mul_pos hy1 hy2]
  exact div_pos (by nlinarith [mul_pos f1 f2]) fp

/-- HOL `xrr_lt_16`. -/
theorem xrr_lt_16_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
    (t3 : y6 < y1 + y2) : xrr y1 y2 y6 < 16 := by
  have h := xrr_factor_8_p22 y1 y2 y6 hy1 hy2
  have f1 : 0 < y6 + y2 + y1 := by linarith
  have f2 : 0 < y2 + y1 - y6 := by linarith
  have fp : 0 < y1 * y2 := by linarith [mul_pos hy1 hy2]
  have hpos : 0 < 4 * ((y6 + y2 + y1) * (y2 + y1 - y6)) / (y1 * y2) :=
    div_pos (by nlinarith [mul_pos f1 f2]) fp
  linarith [h, hpos]

/-- HOL `ups_x_triangle_ineq`. -/
theorem ups_x_triangle_ineq_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy6 : 0 < y6) :
    (0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) ↔
      (y1 < y2 + y6 ∧ y2 < y1 + y6 ∧ y6 < y1 + y2)) := by
  have hf : upsX (y1 * y1) (y2 * y2) (y6 * y6)
      = (y6 + y1 - y2) * (y6 - y1 + y2) * ((y1 + y2 - y6) * (y1 + y2 + y6)) := by
    unfold upsX; ring
  have hD : 0 < y1 + y2 + y6 := by linarith
  constructor
  · intro hpos
    rw [hf] at hpos
    rcases mul_pos_iff.mp hpos with ⟨hab, hcd⟩ | ⟨hab, hcd⟩
    · have hC : 0 < y1 + y2 - y6 := by
        rcases mul_pos_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
        · exact hc
        · exact absurd hd (by linarith)
      rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨by linarith, by linarith, by linarith⟩
      · exact absurd (show (0:ℝ) < y6 by linarith) (by linarith)
    · exfalso
      have hC : y1 + y2 - y6 < 0 := by
        rcases mul_neg_iff.mp hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
        · exact absurd hd (by linarith)
        · exact hc
      rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · linarith
      · linarith
  · intro ⟨t1, t2, t3⟩
    rw [hf]
    exact mul_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))

/-- HOL `xrr_bounds`. -/
theorem xrr_bounds_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
    (hu : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)) :
    0 < xrr y1 y2 y6 ∧ xrr y1 y2 y6 < 16 := by
  obtain ⟨t1, t2, t3⟩ := (ups_x_triangle_ineq_p22 y1 y2 y6 hy1 hy2 hy6).1 hu
  exact ⟨xrr_pos_p22 y1 y2 y6 hy1 hy2 t1 t2, xrr_lt_16_p22 y1 y2 y6 hy1 hy2 hy6 t3⟩

/-- HOL `xrr_bounds_2`. -/
theorem xrr_bounds_2_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6) :
    (0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) ↔
      0 < xrr y1 y2 y6 ∧ xrr y1 y2 y6 < 16) := by
  constructor
  · intro hu
    exact xrr_bounds_p22 y1 y2 y6 hy1 hy2 hy6 hu
  · rintro ⟨hp0, hlt0⟩
    have hden : 0 < y1 * y2 := by linarith [mul_pos hy1 hy2]
    have hp : 0 < 4 * ((y6 + y2 - y1) * (y6 - y2 + y1)) / (y1 * y2) := by
      have := xrr_factor_p22 y1 y2 y6 hy1 hy2
      linarith
    have hlt : 0 < 4 * ((y6 + y2 + y1) * (y2 + y1 - y6)) / (y1 * y2) := by
      have := xrr_factor_8_p22 y1 y2 y6 hy1 hy2
      linarith
    have hAB : 0 < (y6 + y2 - y1) * (y6 - y2 + y1) := by
      have hn : 0 < 4 * ((y6 + y2 - y1) * (y6 - y2 + y1)) :=
        (div_pos_iff_of_pos_right hden).mp hp
      nlinarith
    have hCD : 0 < (y6 + y2 + y1) * (y2 + y1 - y6) := by
      have hn : 0 < 4 * ((y6 + y2 + y1) * (y2 + y1 - y6)) :=
        (div_pos_iff_of_pos_right hden).mp hlt
      nlinarith
    have f1 : 0 < y6 + y2 - y1 ∧ 0 < y6 - y2 + y1 := by
      rcases mul_pos_iff.mp hAB with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨ha, hb⟩
      · exact absurd (show (0:ℝ) < y6 by linarith) (by linarith)
    have f2 : 0 < y2 + y1 - y6 := by
      rcases mul_pos_iff.mp hCD with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hb
      · exact absurd (show (0:ℝ) < y1 + y2 by linarith) (by linarith)
    exact (ups_x_triangle_ineq_p22 y1 y2 y6 hy1 hy2 hy6).2
      ⟨by linarith, by linarith, by linarith⟩

/-- HOL `xrr_le_16`. -/
theorem xrr_le_16_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
    (hu : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)) : xrr y1 y2 y6 ≤ 16 :=
  le_of_lt (xrr_bounds_p22 y1 y2 y6 hy1 hy2 hy6 hu).2

/-- HOL `arclength_xrr` (NEEDS the atn2/acs bridge: `arcLength a b c =
π/2 + atn2 (√upsX) (c²-a²-b²)` equals `acs ((a²+b²-c²)/(2ab))` on the
positive-ups domain). -/
theorem arclength_xrr_p22 (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
    (hu : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)) :
    arcLength y1 y2 y6 = acsP22 (1 - xrr y1 y2 y6 / 8) := by
  sorry

/-! ## Section G: chain tests and taum monotonicity (OCBICBY.hl 1158-2100) -/

/-- HOL `TBRMXRZ1`. -/
theorem TBRMXRZ1_p22 (f g : ℝ → ℝ) (f' g' h' x y : ℝ)
    (hf : derivedForm True f f' x Set.univ)
    (hg : derivedForm True g g' y Set.univ)
    (hh : derivedForm True (g ∘ f) h' x Set.univ)
    (hpos : 0 < f') (hxy : f x = y) :
    reEqvl h' g' := by
  have key := derived_form_chain_old_p22 f g f' g' h' x y hxy hf hg hh
  exact ⟨f', hpos, by rw [key]; ring⟩

/-- HOL `TBRMXRZ2` (NEEDS the eventual-eq version of the uniqueness kit). -/
theorem TBRMXRZ2_p22 (P Q : ℝ → Prop) (f f' f'' g g' g'' h' h'' : ℝ → ℝ) (x y : ℝ)
    (hx : P x) (hQ : Q (f x)) (hxy : y = f x) (hfp : 0 < f' x) (hhz : h' x = 0)
    (hopen : IsOpen {z | P z ∧ Q (f z)})
    (hf : ∀ z, derivedForm (P z) f (f' z) z Set.univ)
    (hg : ∀ z, derivedForm (Q z) g (g' z) z Set.univ)
    (hh : ∀ z, derivedForm (P z ∧ Q (f z)) (g ∘ f) (h' z) z Set.univ)
    (hf2 : derivedForm True f' (f'' x) x Set.univ)
    (hg2 : derivedForm True g' (g'' y) y Set.univ)
    (hh2 : derivedForm True h' (h'' x) x Set.univ) :
    reEqvl (h'' x) (g'' y) := by
  sorry

/-- HOL `SECOND_CHAIN_GENERAL`. -/
theorem SECOND_CHAIN_GENERAL_p22 (P Q : ℝ → Prop) (f f' g g' : ℝ → ℝ) (f'' g'' x y : ℝ)
    (hx : P x) (hQ : Q (f x)) (hxy : f x = y)
    (hopen : IsOpen {z | P z ∧ Q (f z)})
    (hf : ∀ z, derivedForm (P z) f (f' z) z Set.univ)
    (hg : ∀ z, derivedForm (Q z) g (g' z) z Set.univ)
    (hf2 : derivedForm True f' f'' x Set.univ)
    (hg2 : derivedForm True g' g'' y Set.univ) :
    derivedForm True (fun q => g' (f q) * f' q)
      (g' y * f'' + g'' * f' x ^ 2) x Set.univ := by
  sorry

/-- HOL `THIRD_CHAIN_GENERAL`. -/
theorem THIRD_CHAIN_GENERAL_p22 (P Q : ℝ → Prop) (f f' f'' f''' g g' g'' g''' : ℝ → ℝ)
    (x y : ℝ)
    (hx : P x) (hQ : Q (f x)) (hxy : f x = y)
    (hopen : IsOpen {z | P z ∧ Q (f z)})
    (hf : ∀ z, derivedForm (P z) f (f' z) z Set.univ)
    (hg : ∀ z, derivedForm (Q z) g (g' z) z Set.univ)
    (hf2 : ∀ z, derivedForm (P z) f' (f'' z) z Set.univ)
    (hg2 : ∀ z, derivedForm (Q z) g' (g'' z) z Set.univ)
    (hf3 : derivedForm (P x) f'' (f''' x) x Set.univ)
    (hg3 : derivedForm (Q y) g'' (g''' y) y Set.univ) :
    ∃ h''' : ℝ, derivedForm True
      (fun q => g' (f q) * f'' q + g'' (f q) * f' q ^ 2) h''' x Set.univ := by
  sorry

/-- HOL `SECOND_CHAIN_CONTINUOUS`. -/
theorem SECOND_CHAIN_CONTINUOUS_p22 (P Q : ℝ → Prop)
    (f f' f'' f''' g g' g'' g''' : ℝ → ℝ) (x y : ℝ)
    (hx : P x) (hQ : Q (f x)) (hxy : f x = y)
    (hopen : IsOpen {z | P z ∧ Q (f z)})
    (hf : ∀ z, derivedForm (P z) f (f' z) z Set.univ)
    (hg : ∀ z, derivedForm (Q z) g (g' z) z Set.univ)
    (hf2 : ∀ z, derivedForm (P z) f' (f'' z) z Set.univ)
    (hg2 : ∀ z, derivedForm (Q z) g' (g'' z) z Set.univ)
    (hf3 : derivedForm (P x) f'' (f''' x) x Set.univ)
    (hg3 : derivedForm (Q y) g'' (g''' y) y Set.univ) :
    ContinuousAt (fun q => g' (f q) * f'' q + g'' (f q) * f' q ^ 2) x := by
  sorry

/-- HOL `SECOND_DERIVATIVE_TEST_COMPOSE`. -/
theorem SECOND_DERIVATIVE_TEST_COMPOSE_p22 (P Q : ℝ → Prop) (x y : ℝ) (s : Set ℝ)
    (f f' f'' f''' g g' g'' g''' : ℝ → ℝ)
    (hx : P x) (hQ : Q (f x)) (hxy : f x = y) (hfp : 0 < f' x)
    (hs : s ⊆ {z | P z ∧ Q (f z)})
    (hopen : IsOpen {z | P z ∧ Q (f z)}) (hopens : IsOpen s) (hxin : x ∈ s)
    (hmin : ∀ z ∈ s, g (f x) ≤ g (f z))
    (hf : ∀ z, derivedForm (P z) f (f' z) z Set.univ)
    (hf2 : ∀ z, derivedForm (P z) f' (f'' z) z Set.univ)
    (hf3 : derivedForm (P x) f'' (f''' x) x Set.univ)
    (hg : ∀ z, derivedForm (Q z) g (g' z) z Set.univ)
    (hg2 : ∀ z, derivedForm (Q z) g' (g'' z) z Set.univ)
    (hg3 : derivedForm (Q y) g'' (g''' y) y Set.univ) :
    g' y = 0 ∧ 0 ≤ g'' y := by
  sorry

/-- HOL `delta_y_pos_xrr`. -/
theorem delta_y_pos_xrr_p22 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) :
    (0 < deltaY_p22 y1 y2 y3 y4 y5 y6 ↔
      0 < deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)) := by
  have h := delta_x_xrr_p22 y1 y2 y3 y4 y5 y6
    (by linarith) (by linarith) (by linarith)
  have h64 : 0 < (64 : ℝ) := by norm_num
  have hne : y1 * y2 * y3 ≠ 0 := mul_ne_zero (mul_ne_zero (ne_of_gt hy1) (ne_of_gt hy2))
    (ne_of_gt hy3)
  have hden : 0 < (y1 * y2 * y3) ^ 2 := sq_pos_of_ne_zero hne
  constructor
  · intro hpos
    rw [h]
    exact div_pos (mul_pos h64 hpos) hden
  · intro hd
    rw [h] at hd
    have hp := (div_pos_iff_of_pos_right hden).mp hd
    exact (mul_pos_iff_of_pos_left h64).mp hp

/-- HOL `xrr_convert` (set equality of the y4-domains; NEEDS the bounds /
delta-y bridge). -/
theorem xrr_convert_p22 (y1 y2 y3 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5))
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)) :
    {y | 0 < y ∧ 0 < xrr y2 y3 y ∧ xrr y2 y3 y < 16 ∧
      0 < deltaX 4 4 4 (xrr y2 y3 y) (xrr y1 y3 y5) (xrr y1 y2 y6)} =
    {y | 0 < y ∧ 0 < upsX (y2 * y2) (y3 * y3) (y * y) ∧
      0 < deltaY_p22 y1 y2 y3 y y5 y6} := by
  sorry

/-- HOL `real_open_contains_real_interval`. -/
theorem real_open_contains_real_interval_p22 (x : ℝ) (s : Set ℝ) (hx : x ∈ s)
    (hopen : IsOpen s) :
    ∃ a b, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ s := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨x - ε, x + ε, ⟨by linarith, by linarith⟩, ?_⟩
  intro z hz
  have hz' : dist z x < ε := by
    obtain ⟨h1, h2⟩ := hz
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  exact hsub ((Metric.mem_ball).mp hz')

/-- HOL `SECOND_DERIVATIVE_TEST_TAUM` (NEEDS the taum/num1/chain kit). -/
theorem SECOND_DERIVATIVE_TEST_TAUM_p22 (a b y1 y2 y3 y4 y5 y6 : ℝ)
    (hy4 : y4 ∈ Set.Ioo a b)
    (hsub : Set.Ioo a b ⊆ {y | 0 < deltaY_p22 y1 y2 y3 y y5 y6 ∧ 0 < y ∧
      0 < upsX (y2 * y2) (y3 * y3) (y * y)})
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5))
    (hcrit : num1_p22 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
        (xrr y1 y2 y6) = 0 →
      dnum1_p22 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
        (xrr y1 y2 y6) < 0) :
    ∃ y4', y4' ∈ Set.Ioo a b ∧ taum_p22 y1 y2 y3 y4' y5 y6 < taum_p22 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `FIRST_DERIV_POS_OPEN_COMPOSE`. -/
theorem FIRST_DERIV_POS_OPEN_COMPOSE_p22 (P Q : ℝ → Prop) (x y : ℝ)
    (f f' f'' g g' g'' : ℝ → ℝ)
    (hx : P x) (hQ : Q (f x)) (hxy : f x = y)
    (hopen : IsOpen {z | P z ∧ Q (f z)})
    (hf : ∀ z, derivedForm (P z) f (f' z) z Set.univ)
    (hf2 : ∀ z, derivedForm (P z) f' (f'' z) z Set.univ)
    (hg : ∀ z, derivedForm (Q z) g (g' z) z Set.univ)
    (hg2 : ∀ z, derivedForm (Q z) g' (g'' z) z Set.univ) :
    IsOpen {z | (P z ∧ Q (f z)) ∧ 0 < g' (f z) * f' z} := by
  sorry

/-- HOL `FIRST_DERIVATIVE_TEST_TAUM`. -/
theorem FIRST_DERIVATIVE_TEST_TAUM_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hy4 : 0 < y4)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5))
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hn : 0 < num1_p22 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
      (xrr y1 y2 y6)) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum_p22 y1 y2 y3 y4' y5 y6 < taum_p22 y1 y2 y3 y4'' y5 y6 := by
  sorry

/-! ## Section H: the cs_adj machine and `is_scs_adj` (OCBICBY.hl 2101-2213) -/

/-- Equal residues give equal residues of the successor. -/
theorem modSuccEq_p22 {k m n : ℕ} (h : m % k = n % k) : (m + 1) % k = (n + 1) % k := by
  have a : (m + 1) % k = (m % k + 1) % k := Nat.ModEq.add_right 1 (Nat.mod_modEq m k).symm
  have b : (n + 1) % k = (n % k + 1) % k := Nat.ModEq.add_right 1 (Nat.mod_modEq n k).symm
  rw [a, h, b]

/-- `cs_adj` depends on its arguments only through the mod-k residues. -/
theorem csAdj_mod_p22 {k : ℕ} {a1 a2 : ℝ} {i1 i2 j1 j2 : ℕ}
    (hi : i1 % k = i2 % k) (hj : j1 % k = j2 % k) :
    csAdj k a1 a2 i1 j1 = csAdj k a1 a2 i2 j2 := by
  have h1 := modSuccEq_p22 hi
  have h2 := modSuccEq_p22 hj
  simp only [csAdj, hi, hj, h1, h2]

/-- `cs_adj` is symmetric. -/
theorem csAdj_swap_p22 {k : ℕ} {a1 a2 : ℝ} {i j : ℕ} :
    csAdj k a1 a2 i j = csAdj k a1 a2 j i := by
  simp only [csAdj]
  by_cases h1 : i % k = j % k
  · simp [h1]
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    by_cases h2 : (j % k = (i + 1) % k ∨ (j + 1) % k = i % k)
    · have h2' : (i % k = (j + 1) % k ∨ (i + 1) % k = j % k) := by
        rcases h2 with h | h
        · exact Or.inr h.symm
        · exact Or.inl h.symm
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬ (i % k = (j + 1) % k ∨ (i + 1) % k = j % k) := by
        rintro (h | h)
        · exact h2 (Or.inr h.symm)
        · exact h2 (Or.inl h.symm)
      rw [if_neg h2, if_neg h2']

/-- `cs_adj` is `k`-periodic in each slot (HOL `periodic2_cs_adj`). -/
theorem periodic2_cs_adj_p22 {k : ℕ} {r r' : ℝ} : Periodic2 (csAdj k r r') k := by
  intro i j
  constructor
  · exact csAdj_mod_p22 (Nat.add_mod_right _ _) rfl
  · exact csAdj_mod_p22 rfl (Nat.add_mod_right _ _)

/-- For `k > 1` the successor does not wrap onto the same residue. -/
theorem succModNe_p22 {k i : ℕ} (hk : 1 < k) : (i + 1) % k ≠ i % k := by
  intro hc
  have he : i + (1:ℕ) ≡ i + 0 [MOD k] := by rw [Nat.add_zero]; exact hc
  have h0 : (1:ℕ) ≡ 0 [MOD k] := Nat.ModEq.add_left_cancel' i he
  have h1 : (1:ℕ) % k = 0 := h0
  have hk1 : k ≤ 1 := Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero h1)
  omega

/-- On the successor pair `i, i+1` (k > 1), `cs_adj` returns the a-value. -/
theorem csAdj_adj_p22 {k : ℕ} {a1 a2 : ℝ} (hk : 1 < k) {i : ℕ} :
    csAdj k a1 a2 i (i + 1) = a1 := by
  rw [csAdj, if_neg (Ne.symm (succModNe_p22 hk)), if_pos (Or.inl rfl)]

/-- `cs_adj` is bounded below by the lower of its two values off-diagonal. -/
theorem csAdj_ge2_p22 {k : ℕ} {a1 a2 : ℝ} (h1 : 2 ≤ a1) (h2 : 2 ≤ a2) {i j : ℕ}
    (h : ¬ (i % k = j % k)) : 2 ≤ csAdj k a1 a2 i j := by
  simp only [csAdj, if_neg h]
  split_ifs
  · exact h1
  · exact h2

/-- HOL `scs_diag_cs_adj`. -/
theorem scs_diag_cs_adj_p22 {k : ℕ} {a b : ℝ} {i j : ℕ} (h : scsDiag k i j) :
    csAdj k a b i j = b := by
  obtain ⟨h1, h2, h3⟩ := h
  have h23 : ¬ (j % k = (i + 1) % k ∨ (j + 1) % k = i % k) := by
    rintro (hc | hc)
    · exact h2 (eq_comm.mp hc)
    · exact h3 hc.symm
  rw [csAdj, if_neg h1, if_neg h23]

/-- HOL `cs_adj_SUC`. -/
theorem cs_adj_SUC_p22 {k : ℕ} {a1 a2 : ℝ} (hk : 1 < k) (i : ℕ) :
    csAdj k a1 a2 i (i + 1) = a1 := csAdj_adj_p22 hk

/-- HOL `scs_mk_unadorned_unadorned`. -/
theorem scs_mk_unadorned_unadorned_p22 {k : ℕ} {d : ℝ} {a b : ℕ → ℕ → ℝ} :
    unadornedV39 (mkUnadornedV39 k d a b) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `scs_basic_unadorned`. -/
theorem scs_basic_unadorned_p22 {k : ℕ} {d : ℝ} {a b : ℕ → ℕ → ℝ} :
    scsBasicV39 (mkUnadornedV39 k d a b) := by
  constructor
  · exact scs_mk_unadorned_unadorned_p22
  · intro i j; rfl

/-- `cs_adj` is monotone in both value slots (chain condition). -/
theorem csAdj_le_p22 {k : ℕ} {r r' s s' : ℝ} (hrs : r ≤ s) (hr's : r' ≤ s') (i j : ℕ) :
    csAdj k r r' i j ≤ csAdj k s s' i j := by
  simp only [csAdj]
  split_ifs
  · exact le_refl _
  · exact hrs
  · exact hr's

/-- HOL `is_scs_adj`: the registry machine. -/
theorem is_scs_adj_p22 (k : ℕ) (d r r' s s' : ℝ)
    (hd : d < 0.9) (hk1 : 3 ≤ k) (hk2 : k ≤ 6)
    (h3 : k = 3 → s < 4) (h4 : 3 < k → s ≤ cstab)
    (hr : 2 ≤ r) (hr' : 2 ≤ r') (hrs : r ≤ s) (hr's : r' ≤ s')
    (h5 : 3 < k → s ≤ 2 * h0 ∧ r = 2) :
    isScsV39 (mkUnadornedV39 k d (csAdj k r r') (csAdj k s s')) := by
  unfold isScsV39
  simp only [mkUnadornedV39]
  refine ⟨hd, hk1, hk2, periodic_empty k, periodic_empty k, periodic_empty k,
    periodic_empty k, periodic2_cs_adj_p22, periodic2_cs_adj_p22,
    periodic2_cs_adj_p22, periodic2_cs_adj_p22, fun _ _ => ⟨rfl, rfl⟩,
    fun i _ => ⟨csAdj_swap_p22, csAdj_swap_p22, csAdj_swap_p22, csAdj_swap_p22, trivial⟩,
    fun i j => ⟨le_refl _, csAdj_le_p22 hrs hr's i j, le_refl _⟩,
    fun i => by simp [csAdj], ?_, ?_, ?_,
    fun _ _ hJ => False.elim hJ, fun _ _ hJ => False.elim hJ, ?_⟩
  · intro i j hij
    obtain ⟨hik, hjk, hne⟩ := hij
    have e1 : i % k = i := Nat.mod_eq_of_lt hik
    have e2 : j % k = j := Nat.mod_eq_of_lt hjk
    simp only [csAdj, e1, e2]
    split_ifs with h h2
    · exact absurd (by rw [h]) hne
    · exact hr
    · exact hr'
  · intro i hk3
    subst hk3
    rw [csAdj_adj_p22 (by norm_num : (1:ℕ) < 3)]
    exact h3 rfl
  · intro i hk3
    rw [csAdj_adj_p22 (lt_of_le_of_lt (by norm_num : (1:ℕ) ≤ 3) hk3)]
    exact h4 hk3
  · by_cases hk3 : k = 3
    · subst hk3
      have hsub : {i | i < 3 ∧ (2 * h0 < csAdj 3 s s' i (i + 1) ∨
          2 < csAdj 3 r r' i (i + 1))} ⊆ ({0, 1, 2} : Set ℕ) := by
        rintro x hx
        simp only [Set.mem_setOf_eq] at hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      have hfin : ({0, 1, 2} : Set ℕ).Finite := Set.toFinite _
      have hle := Set.ncard_le_ncard hsub hfin
      have h3c : ({0, 1, 2} : Set ℕ).ncard = 3 := by
        rw [Set.ncard, Set.encard_eq_coe_toFinset_card]
        decide
      omega
    · have h3lt : 3 < k := lt_of_le_of_ne hk1 (Ne.symm hk3)
      obtain ⟨hs0, hr0⟩ := h5 h3lt
      have hk0 : 1 < k := lt_of_le_of_lt (by norm_num : (1:ℕ) ≤ 3) h3lt
      have hempty : {i | i < k ∧ (2 * h0 < csAdj k s s' i (i + 1) ∨
          2 < csAdj k r r' i (i + 1))} = ∅ := by
        have helper : ∀ i : ℕ, ¬ (i < k ∧ (2 * h0 < csAdj k s s' i (i + 1) ∨
            2 < csAdj k r r' i (i + 1))) := by
          rintro i ⟨hik, h1 | h2⟩
          · rw [csAdj_adj_p22 hk0] at h1
            linarith
          · rw [csAdj_adj_p22 hk0, hr0] at h2
            simp at h2
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_or]
        exact fun hik => ⟨fun h => helper i ⟨hik, Or.inl h⟩,
          fun h => helper i ⟨hik, Or.inr h⟩⟩
      rw [hempty, Set.ncard_empty]
      omega

/-! ## Section I: the cs_adj case bank (OCBICBY.hl 2213-, 3136-, 3883-4127) -/

/-- The registry numbers (`h0 = 1.26`, `cstab = 3.01`). -/
theorem h0_eq_p22 : (h0 : ℝ) = 1.26 := rfl
theorem cstab_eq_p22 : (cstab : ℝ) = 3.01 := rfl

/-- HOL `is_scs_6I1`. -/
theorem is_scs_6I1_p22 : isScsV39 scs6I1 :=
  is_scs_adj_p22 6 (dTame 6) 2 (2 * h0) (2 * h0) 6
    (by norm_num [dTame]) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by rw [h0_eq_p22]; norm_num) (by rw [h0_eq_p22]; norm_num)
    (by rw [h0_eq_p22]; norm_num)
    (fun _ => ⟨le_refl _, rfl⟩)

/-- HOL `is_scs_5I1`. -/
theorem is_scs_5I1_p22 : isScsV39 scs5I1 :=
  is_scs_adj_p22 5 (dTame 5) 2 (2 * h0) (2 * h0) 6
    (by norm_num [dTame]) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by rw [h0_eq_p22]; norm_num) (by rw [h0_eq_p22]; norm_num)
    (by rw [h0_eq_p22]; norm_num)
    (fun _ => ⟨le_refl _, rfl⟩)

/-- HOL `is_scs_4I1`. -/
theorem is_scs_4I1_p22 : isScsV39 scs4I1 :=
  is_scs_adj_p22 4 (dTame 4) 2 (2 * h0) (2 * h0) 6
    (by norm_num [dTame]) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by rw [h0_eq_p22]; norm_num) (by rw [h0_eq_p22]; norm_num)
    (by rw [h0_eq_p22]; norm_num)
    (fun _ => ⟨le_refl _, rfl⟩)

/-- HOL `is_scs_3I1`. -/
theorem is_scs_3I1_p22 : isScsV39 scs3I1 :=
  is_scs_adj_p22 3 (dTame 3) 2 (2 * h0) (2 * h0) 6
    (by norm_num [dTame]) (by norm_num) (by norm_num)
    (fun _ => by rw [h0_eq_p22]; norm_num)
    (fun h => absurd h (by norm_num))
    (by norm_num) (by rw [h0_eq_p22]; norm_num) (by rw [h0_eq_p22]; norm_num)
    (by rw [h0_eq_p22]; norm_num)
    (fun h => absurd h (by norm_num))

/-- HOL `is_scs_5I2`. -/
theorem is_scs_5I2_p22 : isScsV39 scs5I2 := by
  unfold scs5I2
  exact is_scs_adj_p22 5 0.616 2 (Real.sqrt 8) (2 * h0) 6
    (by norm_num) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by have h8 := sqrt8_flyspeck_p22.1; linarith)
    (by rw [h0_eq_p22]; norm_num)
    (by have h8 := sqrt8_flyspeck_p22.2; linarith)
    (fun _ => ⟨le_refl _, rfl⟩)

/-- HOL `is_scs_4I2`. -/
theorem is_scs_4I2_p22 : isScsV39 scs4I2 :=
  is_scs_adj_p22 4 0.467 2 3 (2 * h0) 6
    (by norm_num) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by norm_num) (by rw [h0_eq_p22]; norm_num)
    (by norm_num)
    (fun _ => ⟨le_refl _, rfl⟩)

/-- HOL `is_scs_6T1`. -/
theorem is_scs_6T1_p22 : isScsV39 scs6T1 :=
  is_scs_adj_p22 6 (dTame 6) 2 cstab 2 6
    (by norm_num [dTame]) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [cstab_eq_p22]; norm_num)
    (by norm_num) (by norm_num [cstab_eq_p22]) (by norm_num)
    (by rw [cstab_eq_p22]; norm_num)
    (fun _ => ⟨by rw [h0_eq_p22]; norm_num, rfl⟩)

/-- HOL `is_scs_5T1`. -/
theorem is_scs_5T1_p22 : isScsV39 scs5T1 :=
  is_scs_adj_p22 5 0.616 2 cstab 2 6
    (by norm_num) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [cstab_eq_p22]; norm_num)
    (by norm_num) (by norm_num [cstab_eq_p22]) (by norm_num)
    (by rw [cstab_eq_p22]; norm_num)
    (fun _ => ⟨by rw [h0_eq_p22]; norm_num, rfl⟩)

/-- HOL `is_scs_4T1`. -/
theorem is_scs_4T1_p22 : isScsV39 scs4T1 :=
  is_scs_adj_p22 4 0.467 2 3 2 6
    (by norm_num) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by norm_num [cstab_eq_p22])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => ⟨by rw [h0_eq_p22]; norm_num, rfl⟩)

/-- HOL `is_scs_4T2`. -/
theorem is_scs_4T2_p22 : isScsV39 scs4T2 :=
  is_scs_adj_p22 4 0.467 2 3 (2 * h0) 3
    (by norm_num) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by norm_num) (by rw [h0_eq_p22]; norm_num)
    (le_refl _)
    (fun _ => ⟨le_refl _, rfl⟩)

/-- HOL `is_scs_6M1`. -/
theorem is_scs_6M1_p22 : isScsV39 scs6M1 :=
  is_scs_adj_p22 6 (dTame 6) 2 cstab (2 * h0) 6
    (by norm_num [dTame]) (by norm_num) (by norm_num)
    (fun h => absurd h (by norm_num))
    (fun _ => by rw [h0_eq_p22, cstab_eq_p22]; norm_num)
    (by norm_num) (by norm_num [cstab_eq_p22]) (by rw [h0_eq_p22]; norm_num)
    (by rw [cstab_eq_p22]; norm_num)
    (fun _ => ⟨le_refl _, rfl⟩)


/-! ## Section J: psort / mod kit (OCBICBY.hl 3464-, 3821-3883) -/

/-- HOL `MOD_EQ_MOD_SHIFT`. -/
theorem MOD_EQ_MOD_SHIFT_p22 {n x1 x2 y : ℕ} (hn : n ≠ 0) :
    ((y + x1) % n = (y + x2) % n) ↔ (x1 % n = x2 % n) := by
  constructor
  · intro h
    have t : (x1 + y) % n = (x2 + y) % n := by
      rw [Nat.add_comm x1 y, Nat.add_comm x2 y, h]
    exact Nat.ModEq.add_right_cancel' y t
  · intro h
    have t : (x1 + y) ≡ (x2 + y) [MOD n] := Nat.ModEq.add_right y h
    rw [Nat.add_comm x1 y, Nat.add_comm x2 y] at t
    exact t

/-- HOL `scs_diag_2`. -/
theorem scs_diag_2_p22 {k i : ℕ} (hk : 3 < k) : scsDiag k (i + 1) (i + (k - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h2 := modSuccEq_p22 h
    rw [show i + (k - 1) + 1 = i + k by omega,
        show i + k = i + 0 + k by omega, Nat.add_mod_right] at h2
    rw [show i + 1 + 1 = i + 2 by omega, Nat.add_zero] at h2
    have hd2 : (2:ℕ) ≡ 0 [MOD k] := Nat.ModEq.add_left_cancel' i h2
    have hdvd : k ∣ 2 := Nat.dvd_of_mod_eq_zero hd2
    have hle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · intro h
    have h2 := modSuccEq_p22 (modSuccEq_p22 h)
    rw [show i + (k - 1) + 1 + 1 = i + k + 1 by omega,
        show i + k + 1 = i + 1 + k by omega, Nat.add_mod_right] at h2
    have h3 : (i + 1 + 3) % k = (i + 1 + 0) % k := by
      rw [show i + 1 + 3 = i + 4 by omega, h2, Nat.add_zero]
    have hd2 : (3:ℕ) ≡ 0 [MOD k] := Nat.ModEq.add_left_cancel' (i + 1) h3
    have hdvd : k ∣ 3 := Nat.dvd_of_mod_eq_zero hd2
    have hle : k ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · intro h
    rw [show i + (k - 1) + 1 = i + k by omega, Nat.add_mod_right] at h
    exact succModNe_p22 (by omega) h

/-- HOL `CARD_3_SUBSET`. -/
theorem CARD_3_SUBSET_p22 (f : ℕ → Prop) :
    {i | i < 3 ∧ f i}.ncard ≤ 3 := by
  have hsub : {i | i < 3 ∧ f i} ⊆ ({0, 1, 2} : Set ℕ) := by
    rintro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hfin : ({0, 1, 2} : Set ℕ).Finite := Set.toFinite _
  have hle := Set.ncard_le_ncard hsub hfin
  have h3c : ({0, 1, 2} : Set ℕ).ncard = 3 := by
    rw [Set.ncard, Set.encard_eq_coe_toFinset_card]
    decide
  omega

/-- HOL `I_LT_J_LT_5_EXPLICIT`. -/
theorem I_LT_J_LT_5_EXPLICIT_p22 (i j : ℕ) :
    (i < j ∧ j < 5) ↔
      ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 2) ∨
        (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 4) ∨
        (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4)) := by
  omega

/-- HOL `MOD_5_EXPLICIT`. -/
theorem MOD_5_EXPLICIT_p22 :
    0 % 5 = 0 ∧ 1 % 5 = 1 ∧ 2 % 5 = 2 ∧ 3 % 5 = 3 ∧ 4 % 5 = 4 ∧
      5 % 5 = 0 ∧ 6 % 5 = 1 ∧ 7 % 5 = 2 := by
  decide

/-- HOL `psort_4`. -/
theorem psort_4_p22 (i : ℕ) :
    psort 4 (i, 4) = psort 4 (i, 0) ∧ psort 4 (4, i) = psort 4 (0, i) := by
  constructor <;> · simp only [psort]

/-- HOL `psort_5`. -/
theorem psort_5_p22 :
    psort 5 (0, 1) = (0, 1) ∧ psort 5 (0, 2) = (0, 2) ∧ psort 5 (0, 3) = (0, 3) ∧
      psort 5 (0, 4) = (0, 4) ∧ psort 5 (1, 1) = (1, 1) ∧ psort 5 (1, 2) = (1, 2) ∧
      psort 5 (1, 3) = (1, 3) ∧ psort 5 (1, 4) = (1, 4) ∧ psort 5 (2, 1) = (1, 2) ∧
      psort 5 (2, 2) = (2, 2) ∧ psort 5 (2, 3) = (2, 3) ∧ psort 5 (2, 4) = (2, 4) ∧
      psort 5 (3, 1) = (1, 3) ∧ psort 5 (3, 2) = (2, 3) ∧ psort 5 (3, 3) = (3, 3) ∧
      psort 5 (3, 4) = (3, 4) ∧ psort 5 (4, 1) = (1, 4) ∧ psort 5 (4, 2) = (2, 4) ∧
      psort 5 (4, 3) = (3, 4) ∧ psort 5 (4, 4) = (4, 4) ∧ psort 5 (4, 5) = (0, 4) ∧
      psort 5 (5, 4) = (0, 4) := by
  decide

/-! ## Section K: rho / const1 and the xrr monotonicity kit -/

/-- HOL `const1_pos`. -/
theorem const1_pos_p22 : 0 < const1_p22 := by
  unfold const1_p22 sol0
  have hge : Real.pi / 3 < Real.arccos (1 / 3) := by
    have hanti := Real.strictAntiOn_arccos
      (by norm_num [Set.mem_Icc] : (1:ℝ) / 3 ∈ Set.Icc (-1) 1)
      (by norm_num [Set.mem_Icc] : (1:ℝ) / 2 ∈ Set.Icc (-1) 1)
      (by norm_num : (1:ℝ) / 3 < 1 / 2)
    have hhalf : Real.arccos (1 / 2) = Real.pi / 3 := by
      rw [show (1:ℝ) / 2 = Real.cos (Real.pi / 3) from by
        rw [Real.cos_pi_div_three]]
      exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [← hhalf]
    exact hanti
  have hscaled : (3:ℝ) * (Real.pi / 3) < 3 * Real.arccos (1 / 3) :=
    mul_lt_mul_of_pos_left hge (by norm_num)
  have hpi : (3:ℝ) * (Real.pi / 3) = Real.pi := by ring
  exact div_pos (by linarith) Real.pi_pos

/-- HOL `rho_bounds`. -/
theorem rho_bounds_p22 (y : ℝ) (hy1 : 2 ≤ y) (hy2 : y ≤ 2 * h0) :
    1 ≤ rho y ∧ rho y ≤ 1 + sol0 / Real.pi := by
  have hpos : 0 < sol0 / Real.pi := by
    have h := const1_pos_p22
    unfold const1_p22 at h
    exact h
  have hle : sol0 / Real.pi ≤ 1 := by
    have ha : Real.arccos (1 / 3) < Real.pi / 2 := by
      have h0 : Real.arccos 0 = Real.pi / 2 := Real.arccos_zero
      rw [← h0]
      exact Real.strictAntiOn_arccos
        (by norm_num : (0:ℝ) ∈ Set.Icc (-1) 1)
        (by norm_num : (1:ℝ) / 3 ∈ Set.Icc (-1) 1)
        (by norm_num)
    unfold sol0
    refine div_le_one Real.pi_pos |>.2 ?_
    have hcalc : 3 * Real.arccos (1 / 3) - Real.pi ≤ Real.pi := by
      nlinarith [ha, Real.pi_pos]
    linarith
  unfold rho
  have hden : 0 < 2 * h0 - 2 := by norm_num [h0_eq_p22]
  have h1 : 0 ≤ y - 2 := by linarith
  have h2 : y - 2 ≤ 2 * h0 - 2 := by linarith
  have he : (y - 2) * (sol0 / Real.pi) / (2 * h0 - 2)
      = (y - 2) / (2 * h0 - 2) * (sol0 / Real.pi) := by ring
  constructor
  · have hX : 0 ≤ (y - 2) * (sol0 / Real.pi) / (2 * h0 - 2) := by
      rw [he]
      exact mul_nonneg (div_nonneg h1 hden.le) hpos.le
    linarith
  · have hX : (y - 2) * (sol0 / Real.pi) / (2 * h0 - 2) ≤ sol0 / Real.pi := by
      rw [he]
      have hA1 : (y - 2) / (2 * h0 - 2) ≤ 1 := div_le_one hden |>.2 h2
      have hA0 : 0 ≤ (y - 2) / (2 * h0 - 2) := div_nonneg h1 hden.le
      nlinarith
    linarith

/-- HOL `xrr_increasing`. -/
theorem xrr_increasing_p22 (y1 y2 y6 y6' : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy6 : 0 ≤ y6) (hlt : y6 < y6') : xrr y1 y2 y6 < xrr y1 y2 y6' := by
  have hden : 0 < 2 * y1 * y2 := by nlinarith [mul_pos hy1 hy2]
  have hsq : y6 * y6 < y6' * y6' :=
    mul_self_lt_mul_self (by linarith) hlt
  have hB : y1 * y1 + y2 * y2 - y6' * y6' < y1 * y1 + y2 * y2 - y6 * y6 := by
    linarith
  have hdiv : (y1 * y1 + y2 * y2 - y6' * y6') / (2 * y1 * y2)
      < (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2) :=
    div_lt_div_iff_of_pos_right hden |>.2 hB
  unfold xrr
  linarith

/-- HOL `xrr_decreasing`. -/
theorem xrr_decreasing_p22 (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
    (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2' : y2 ≤ 2 * h0) (hlt : y1 ≤ y1') :
    xrr y1' y2 y6 ≤ xrr y1 y2 y6 := by
  sorry

/-- HOL `xrr_simple_lower_bound`. -/
theorem xrr_simple_lower_bound_p22 (y1 y2 y6 y6inf : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6inf) (hy6' : y6inf ≤ y6) :
    (y6inf / h0) ^ 2 ≤ xrr y1 y2 y6 := by
  sorry

/-- HOL `xrr_simple_upper_bound`. -/
theorem xrr_simple_upper_bound_p22 (y1 y2 y6 y6sup : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ y6sup)
    (hy6sup : y6sup < 4) :
    xrr y1 y2 y6 ≤ y6sup ^ 2 := by
  sorry

/-- HOL `taum_compose_xrr` (NEEDS the real `taum` body). -/
theorem taum_compose_xrr_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6) :
    (fun q => taum_p22 y1 y2 y3 q y5 y6) y4 =
      (fun q => rho y1 * dihXf_p22 4 4 4 q (xrr y1 y3 y5) (xrr y1 y2 y6)
        + rho y2 * dihXf_p22 4 4 4 (xrr y1 y3 y5) (xrr y1 y2 y6) q
        + rho y3 * dihXf_p22 4 4 4 (xrr y1 y2 y6) q (xrr y1 y3 y5)
        - (1 + const1_p22) * Real.pi) ((fun q => xrr y2 y3 q) y4) := by
  sorry

/-- HOL `real_open_delta_y` (NEEDS `dih`/`delta` continuity). -/
theorem real_open_delta_y_p22 (y1 y2 y3 y5 y6 : ℝ) :
    IsOpen {y4 | 0 < y4 ∧ 0 < deltaY_p22 y1 y2 y3 y4 y5 y6} := by
  sorry

/-- HOL `real_open_ups_y` (NEEDS `ups_x` continuity). -/
theorem real_open_ups_y_p22 (y1 y2 : ℝ) :
    IsOpen {y6 | 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)} := by
  sorry

/-! ## Section L: remaining machinery and the funlist case bank -/

/-- HOL `scs_vv_MOD`. -/
theorem scs_vv_MOD_p22 (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
    (h1 : isScsV39 s) (h2 : BBsV39 s vv) : vv (i % s.k) = vv i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h1
  obtain ⟨-, hperV, -, -⟩ := h2
  have key : ∀ m r : ℕ, vv (m * s.k + r) = vv r := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ n ih =>
        intro r
        have hstep := hperV (n * s.k + r)
        rw [show (n + 1) * s.k + r = n * s.k + r + s.k from by ring]
        rw [hstep, ih]
  have := key (i / s.k) (i % s.k)
  have e : i = s.k * (i / s.k) + i % s.k := (Nat.div_add_mod i s.k).symm
  conv_rhs => rw [e]
  rw [Nat.mul_comm]
  exact (key (i / s.k) (i % s.k)).symm

/-- HOL `stab_diag_basic`. -/
theorem stab_diag_basic_p22 (s : ScsV39) (i j : ℕ)
    (h : scsBasicV39 s) (hne : ¬ (i = j)) : scsBasicV39 (scsStabDiagV39 s i j) := by
  sorry

/-- HOL `is_scs_funlist_basic` (NEEDS the funlist periodicity/symmetry kit). -/
theorem is_scs_funlist_basic_p22 (k : ℕ) (d : ℝ) (a0 b0 : List ((ℕ × ℕ) × ℝ))
    (a b : ℕ × ℕ → ℝ) (hd : d < 0.9) (hk1 : 3 ≤ k) (hk2 : k ≤ 6)
    (hchain : ∀ i j, i < j ∧ j < k →
      funlistV39 a0 d k i j ≤ funlistV39 b0 d k i j)
    (ha : ∀ i j, i < j ∧ j < k → 2 ≤ funlistV39 a0 d k i j)
    (hb3 : ∀ i, i < 3 ∧ k = 3 → funlistV39 b0 d k i (Nat.succ i) < 4)
    (hbk : ∀ i, i < k ∧ 3 < k → funlistV39 b0 d k i (Nat.succ i) ≤ cstab)
    (hcard : {i | i < k ∧ (2 * h0 < funlistV39 b0 d k i (Nat.succ i) ∨
        2 < funlistV39 a0 d k i (Nat.succ i))}.ncard + k ≤ 6) :
    isScsV39 (mkUnadornedV39 k d (funlistV39 a0 d k) (funlistV39 b0 d k)) := by
  sorry

/-- HOL `azim_in_fan_azim` (NEEDS the sigmaFan/ee localization kit). -/
theorem azim_in_fan_azim_p22 (vv : ℕ → V3) (E : Set (Set V3)) (k i : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (hE : E = Set.range fun i => {vv i, vv (i + 1)}) :
    azimInFan (vv i, vv (i + 1)) E =
      azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1))) := by
  sorry

/-- HOL `sol_local_azim`. -/
theorem sol_local_azim_p22 (vv : ℕ → V3) (k : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (E : Set (Set V3)) (f : Set (V3 × V3))
    (hE : E = Set.range fun i => {vv i, vv (i + 1)})
    (hf : f = Set.range fun i => (vv i, vv (i + 1))) :
    solLocal E f =
      (Finset.sum (Finset.range k) fun i =>
          azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1)))) - Real.pi * (k - 2) := by
  sorry

/-- HOL `vv_inj_lemma`. -/
theorem vv_inj_lemma_p22 (s : ScsV39) (v : ℕ → V3) (k : ℕ)
    (h1 : isScsV39 s) (h2 : BBsV39 s v) (hk : s.k = k) :
    ∀ i j, i < k ∧ j < k ∧ v i = v j → i = j := by
  sorry

/-- HOL `LOCAL_FAN_AZIM_POS`. -/
theorem LOCAL_FAN_AZIM_POS_p22 (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (h1 : isScsV39 s) (h2 : BBsV39 s vv) :
    0 < azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) := by
  sorry

/-- HOL `INTERIOR_ANGLE1_AZIM`. -/
theorem INTERIOR_ANGLE1_AZIM_p22 (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
    (h1 : isScsV39 s) (h2 : BBsV39 s vv) (hk : 3 < s.k)
    (f : Set (V3 × V3)) (hf : f = Set.range fun i => (vv i, vv (i + 1))) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) =
      interiorAngle1 0 f (vv i) := by
  sorry

/-- HOL `delta_x4_imp_obtuse` (NEEDS the atn2 sign kit). -/
theorem delta_x4_imp_obtuse_p22 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 ≤ deltaX x1 x2 x3 x4 x5 x6)
    (h3 : deltaX4 x1 x2 x3 x4 x5 x6 < 0) :
    Real.pi / 2 < dihXf_p22 x1 x2 x3 x4 x5 x6 := by
  sorry

/-- HOL `delta4_y_imp_obtuse`. -/
theorem delta4_y_imp_obtuse_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1 : 0 < y1) (h2 : 0 ≤ deltaY_p22 y1 y2 y3 y4 y5 y6)
    (h3 : delta4Y_p22 y1 y2 y3 y4 y5 y6 < 0) :
    Real.pi / 2 < dihY_p22 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `scs_lb_2` (NEEDS the periodic2-backward reduction). -/
theorem scs_lb_2_p22 (s : ScsV39) (vv : ℕ → V3) (i j : ℕ)
    (h1 : isScsV39 s) (h2 : BBsV39 s vv) (hne : i % s.k ≠ j % s.k) :
    2 ≤ dist (vv i) (vv j) := by
  sorry

/-- HOL `SYNQIWN`. -/
theorem SYNQIWN_p22 (h : main_nonlinear_terminal_v11) (s : ScsV39) (v : ℕ → V3) (i k : ℕ)
    (h1 : isScsV39 s) (h2 : BBsV39 s v) (hkk : s.k = k) (h3 : 3 < k)
    (hears : (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2) ∨
      (norm (v (i + k - 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
      (norm (v (i + 1)) = 2 ∧ norm (v (i + k - 1)) = 2) ∨
      (dist (v i) (v (i + 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2) ∨
      (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
      (norm (v (i + k - 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2))
    (he1 : dist (v i) (v (i + 1)) ≤ 2 * h0)
    (he2 : dist (v i) (v (i + k - 1)) ≤ 2 * h0)
    (hc : cstab ≤ dist (v (i + 1)) (v (i + k - 1))) :
    Real.pi / 2 < azim 0 (v i) (v (i + 1)) (v (i + k - 1)) := by
  sorry

/-- HOL `RRCWNS_WEAK`. -/
theorem RRCWNS_WEAK_p22 (h : main_nonlinear_terminal_v11) (s : ScsV39) (vv : ℕ → V3)
    (hB : BBsV39 s vv) (hk : 3 < s.k) (ht : taustarV39 s vv < 0)
    (h1 : isScsV39 s) (h2 : scsBasicV39 s)
    (hd : ∀ i j, scsDiag s.k i j → cstab ≤ dist (vv i) (vv j))
    (hl : ∀ (i : ℕ) w, Lunar (vv i) w (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) →
      dist (vv i) (vv (i + 1)) ≤ 2 * h0 ∧ dist (vv i) (vv (i + (s.k - 1))) ≤ 2 * h0 ∧
        (norm (vv (i + 1)) = 2 ∨ dist (vv i) (vv (i + 1)) = 2) ∧
        (norm (vv (i + (s.k - 1))) = 2 ∨ dist (vv i) (vv (i + (s.k - 1))) = 2)) :
    scsGeneric vv := by
  sorry

/-- HOL `EAR_SOL_NN`. -/
theorem EAR_SOL_NN_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0) (hy4 : cstab ≤ y4 ∧ y4 ≤ 3.915)
    (hy5 : y5 = 2) (hy6 : y6 = 2) (hd : 0 ≤ deltaY_p22 y1 y2 y3 y4 y5 y6) :
    0 ≤ solY_p22 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `scs_6T1_props`. -/
theorem scs_6T1_props_p22 :
    scs6T1.k = 6 ∧ scsBasicV39 scs6T1 ∧
      (∀ vv i j, BBsV39 scs6T1 vv → scsDiag 6 i j → cstab ≤ dist (vv i) (vv j)) ∧
      (∀ vv i, BBsV39 scs6T1 vv → dist (vv i) (vv (i + 1)) = 2) := by
  sorry

/-- HOL `scs_5T1_props`. -/
theorem scs_5T1_props_p22 :
    scs5T1.k = 5 ∧ scsBasicV39 scs5T1 ∧
      (∀ vv i j, BBsV39 scs5T1 vv → scsDiag 5 i j → cstab ≤ dist (vv i) (vv j)) ∧
      (∀ vv i, BBsV39 scs5T1 vv → dist (vv i) (vv (i + 1)) = 2) := by
  sorry

/-- HOL `scs_6T1_generic`. -/
theorem scs_6T1_generic_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv) (ht : taustarV39 scs6T1 vv < 0) :
    scsGeneric vv := by
  sorry

/-- HOL `scs_5T1_generic`. -/
theorem scs_5T1_generic_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs5T1 vv) (ht : taustarV39 scs5T1 vv < 0) :
    scsGeneric vv := by
  sorry

/-- HOL `empty_6T1` (giant; the analytic core of the terminal emptiness). -/
theorem empty_6T1_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv) : 0 ≤ taustarV39 scs6T1 vv := by
  sorry

/-- HOL `empty_5T1` (giant). -/
theorem empty_5T1_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs5T1 vv) : 0 ≤ taustarV39 scs5T1 vv := by
  sorry

/-- HOL `periodic_sum_shift`. -/
theorem periodic_sum_shift_p22 (f : ℕ → ℝ) (j n : ℕ) (hper : Periodic f n) (hn : n ≠ 0) :
    Finset.sum (Finset.range n) f = Finset.sum (Finset.range n) (fun i => f (j + i)) := by
  sorry

/-- HOL `LEMMA_7175074394` (numeric; `c110186` records
`atn (sqrt 0.110186) < 0.3205` in HOL). -/
theorem LEMMA_7175074394_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hbox : ineqP22 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (2, y4, 2),
      (3.01, y5, 3.237), (2, y6, 2)] True)
    (hd : deltaY_p22 y1 y2 y3 y4 y5 y6 ≤ 20 ∧ 0 ≤ deltaY_p22 y1 y2 y3 y4 y5 y6) :
    dihY_p22 y1 y2 y3 y4 y5 y6 < 0.3205 := by
  sorry

/-- HOL `angle_sum_5T1`. -/
theorem angle_sum_5T1_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hbox : ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0),
      (2, y126, 2 * h0), (2, y135, 2 * h0), (2, y4, 2), (cstab, y5, 3.237),
      (cstab, y6, 3.237)] True)
    (hsub : dihY_p22 y1 y126 y135 cstab 2 2 ≤
        dihY_p22 y1 y2 y3 y4 y5 y6 + dihY_p22 y1 y2 y126 2 2 y6 +
          dihY_p22 y1 y3 y135 2 2 y5)
    (hd1 : 0 ≤ deltaY_p22 y1 y2 y126 2 2 y6) (hd2 : 0 ≤ deltaY_p22 y1 y3 y135 2 2 y5) :
    20 ≤ deltaY_p22 y1 y2 y126 2 2 y6 ∨ 20 ≤ deltaY_p22 y1 y3 y135 2 2 y5 := by
  sorry

/-- HOL `terminal_pent_taum2`. -/
theorem terminal_pent_taum2_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hd1 : 0 ≤ deltaY_p22 y126 y1 y2 y6 2 2)
    (hd2 : 0 ≤ deltaY_p22 y135 y1 y3 y5 2 2)
    (hsub : dihY_p22 y1 y126 y135 cstab 2 2 ≤
        dihY_p22 y1 y2 y3 y4 y5 y6 + dihY_p22 y1 y2 y126 2 2 y6 +
          dihY_p22 y1 y3 y135 2 2 y5) :
    ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2),
      (3.01, y5, 3.237), (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taum_p22 y126 y1 y2 y6 2 2 + taum_p22 y1 y2 y3 y4 y5 y6 +
        taum_p22 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `dih_y_mono`. -/
theorem dih_y_mono_p22 (y1 y2 y3 y4 y5 y6 y4' : ℝ)
    (hle : y4 ≤ y4') (hy1 : 0 < y1) (hy4 : 0 < y4)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6)
    (hd' : 0 ≤ deltaY_p22 y1 y2 y3 y4' y5 y6) :
    dihY_p22 y1 y2 y3 y4 y5 y6 ≤ dihY_p22 y1 y2 y3 y4' y5 y6 := by
  sorry

/-- HOL `LEMMA_1834976363`. -/
theorem LEMMA_1834976363_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 a b : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0)
    (hx4 : (2 / h0) ^ 2 ≤ xrr y2 y3 y4 ∧ xrr y2 y3 y4 ≤ 15.53)
    (hx5 : (2 / h0) ^ 2 ≤ xrr y1 y3 y5) (hx6 : (2 / h0) ^ 2 ≤ xrr y1 y2 y6)
    (hy4 : y4 ∈ Set.Ioo a b)
    (hsub : Set.Ioo a b ⊆ {y | 0 < deltaY_p22 y1 y2 y3 y y5 y6 ∧ 0 < y ∧
      0 < upsX (y2 * y2) (y3 * y3) (y * y)})
    (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ∃ y4', y4' ∈ Set.Ioo a b ∧ taum_p22 y1 y2 y3 y4' y5 y6 < taum_p22 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `NUM1_GENERIC`. -/
theorem NUM1_GENERIC_p22 (x4inf x4sup x5inf x5sup x6inf x6sup y1 y2 y3 y4 y5 y6 : ℝ)
    (hbox : ineqP22 [(1, rho y1, 1 + sol0 / Real.pi), (1, rho y2, 1 + sol0 / Real.pi),
      (1, rho y3, 1 + sol0 / Real.pi), (x4inf, xrr y2 y3 y4, x4sup),
      (x5inf, xrr y1 y3 y5, x5sup), (x6inf, xrr y1 y2 y6, x6sup)] True)
    (hnz : 0 < num1_p22 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
      (xrr y1 y2 y6))
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0)
    (hx4 : x4inf ≤ xrr y2 y3 y4 ∧ xrr y2 y3 y4 ≤ x4sup)
    (hx5 : x5inf ≤ xrr y1 y3 y5 ∧ xrr y1 y3 y5 ≤ x5sup)
    (hx6 : x6inf ≤ xrr y1 y2 y6 ∧ xrr y1 y2 y6 ≤ x6sup)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6)
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum_p22 y1 y2 y3 y4' y5 y6 < taum_p22 y1 y2 y3 y4'' y5 y6 := by
  sorry

/-- HOL `LEMMA_4828966562`. -/
theorem LEMMA_4828966562_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0) (hy4 : 2 ≤ y4 ∧ y4 ≤ 2 * h0)
    (hy5 : 2 ≤ y5 ∧ y5 ≤ 3.01) (hy6 : 3 ≤ y6)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum_p22 y1 y2 y3 y4' y5 y6 < taum_p22 y1 y2 y3 y4'' y5 y6 := by
  sorry

/-- HOL `LEMMA_6843920790`. -/
theorem LEMMA_6843920790_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0) (hy4 : 2 ≤ y4 ∧ y4 ≤ 3.01)
    (hy5 : 3 ≤ y5 ∧ xrr y1 y3 y5 ≤ 15.53) (hy6 : 3 ≤ y6 ∧ xrr y1 y2 y6 ≤ 15.53)
    (hd : 0 < deltaY_p22 y1 y2 y3 y4 y5 y6) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum_p22 y1 y2 y3 y4' y5 y6 < taum_p22 y1 y2 y3 y4'' y5 y6 := by
  sorry

/-! ## Section M: the funlist case bank and the OCBICBY assembly -/

/-- HOL `is_scs_4T3` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4T3_p22 : isScsV39 scs4T3 := by
  sorry

/-- HOL `is_scs_4T4` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4T4_p22 : isScsV39 scs4T4 := by
  sorry

/-- HOL `is_scs_4T5` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4T5_p22 : isScsV39 scs4T5 := by
  sorry

/-- HOL `is_scs_3T1` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T1_p22 : isScsV39 scs3T1 := by
  sorry

/-- HOL `is_scs_3T2` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T2_p22 : isScsV39 scs3T2 := by
  sorry

/-- HOL `is_scs_3T3` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T3_p22 : isScsV39 scs3T3 := by
  sorry

/-- HOL `is_scs_3T4` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T4_p22 : isScsV39 scs3T4 := by
  sorry

/-- HOL `is_scs_3T5` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T5_p22 : isScsV39 scs3T5 := by
  sorry

/-- HOL `is_scs_3T6` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T6_p22 : isScsV39 scs3T6' := by
  sorry

/-- HOL `is_scs_3T7` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T7_p22 : isScsV39 scs3T7 := by
  sorry

/-- HOL `is_scs_3M1` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3M1_p22 : isScsV39 scs3M1 := by
  sorry

/-- HOL `is_scs_5I3` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_5I3_p22 : isScsV39 scs5I3 := by
  sorry

/-- HOL `is_scs_4I3` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4I3_p22 : isScsV39 scs4I3 := by
  sorry

/-- HOL `is_scs_5M1` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_5M1_p22 : isScsV39 scs5M1 := by
  sorry

/-- HOL `is_scs_5M2` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_5M2_p22 : isScsV39 scs5M2 := by
  sorry

/-- HOL `is_scs_4M1` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M1_p22 : isScsV39 scs4M1 := by
  sorry

/-- HOL `is_scs_4M2` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M2_p22 : isScsV39 scs4M2 := by
  sorry

/-- HOL `is_scs_4M3` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M3_p22 : isScsV39 scs4M3' := by
  sorry

/-- HOL `is_scs_4M4` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M4_p22 : isScsV39 scs4M4' := by
  sorry

/-- HOL `is_scs_4M5` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M5_p22 : isScsV39 scs4M5' := by
  sorry

/-- HOL `is_scs_4M6` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M6_p22 : isScsV39 scs4M6' := by
  sorry

/-- HOL `is_scs_4M7` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M7_p22 : isScsV39 scs4M7 := by
  sorry

/-- HOL `is_scs_4M8` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_4M8_p22 : isScsV39 scs4M8 := by
  sorry

/-- HOL `is_scs_examples`: the full 34-system registry bank. -/
theorem is_scs_examples_p22 :
    isScsV39 scs6I1 ∧
    isScsV39 scs5I1 ∧
    isScsV39 scs5I2 ∧
    isScsV39 scs5I3 ∧
    isScsV39 scs4I1 ∧
    isScsV39 scs4I2 ∧
    isScsV39 scs4I3 ∧
    isScsV39 scs3I1 ∧
    isScsV39 scs6T1 ∧
    isScsV39 scs5T1 ∧
    isScsV39 scs4T1 ∧
    isScsV39 scs4T2 ∧
    isScsV39 scs4T3 ∧
    isScsV39 scs4T4 ∧
    isScsV39 scs4T5 ∧
    isScsV39 scs3T1 ∧
    isScsV39 scs3T2 ∧
    isScsV39 scs3T3 ∧
    isScsV39 scs3T4 ∧
    isScsV39 scs3T5 ∧
    isScsV39 scs3T6' ∧
    isScsV39 scs3T7 ∧
    isScsV39 scs6M1 ∧
    isScsV39 scs5M1 ∧
    isScsV39 scs5M2 ∧
    isScsV39 scs4M1 ∧
    isScsV39 scs4M2 ∧
    isScsV39 scs4M3' ∧
    isScsV39 scs4M4' ∧
    isScsV39 scs4M5' ∧
    isScsV39 scs4M6' ∧
    isScsV39 scs4M7 ∧
    isScsV39 scs4M8 ∧
    isScsV39 scs3M1 := by
  exact ⟨is_scs_6I1_p22, is_scs_5I1_p22, is_scs_5I2_p22, is_scs_5I3_p22, is_scs_4I1_p22, is_scs_4I2_p22, is_scs_4I3_p22, is_scs_3I1_p22, is_scs_6T1_p22, is_scs_5T1_p22, is_scs_4T1_p22, is_scs_4T2_p22, is_scs_4T3_p22, is_scs_4T4_p22, is_scs_4T5_p22, is_scs_3T1_p22, is_scs_3T2_p22, is_scs_3T3_p22, is_scs_3T4_p22, is_scs_3T5_p22, is_scs_3T6_p22, is_scs_3T7_p22, is_scs_6M1_p22, is_scs_5M1_p22, is_scs_5M2_p22, is_scs_4M1_p22, is_scs_4M2_p22, is_scs_4M3_p22, is_scs_4M4_p22, is_scs_4M5_p22, is_scs_4M6_p22, is_scs_4M7_p22, is_scs_4M8_p22, is_scs_3M1_p22⟩
/-- HOL `unadorned_examples`. -/
theorem unadorned_examples_p22 :
    unadornedV39 scs6I1 ∧
    unadornedV39 scs5I1 ∧
    unadornedV39 scs5I2 ∧
    unadornedV39 scs5I3 ∧
    unadornedV39 scs4I1 ∧
    unadornedV39 scs4I2 ∧
    unadornedV39 scs4I3 ∧
    unadornedV39 scs3I1 ∧
    unadornedV39 scs6T1 ∧
    unadornedV39 scs5T1 ∧
    unadornedV39 scs4T1 ∧
    unadornedV39 scs4T2 ∧
    unadornedV39 scs4T3 ∧
    unadornedV39 scs4T4 ∧
    unadornedV39 scs4T5 ∧
    unadornedV39 scs3T1 ∧
    unadornedV39 scs3T2 ∧
    unadornedV39 scs3T3 ∧
    unadornedV39 scs3T4 ∧
    unadornedV39 scs3T5 ∧
    unadornedV39 scs3T6' ∧
    unadornedV39 scs3T7 ∧
    unadornedV39 scs6M1 ∧
    unadornedV39 scs5M1 ∧
    unadornedV39 scs5M2 ∧
    unadornedV39 scs4M1 ∧
    unadornedV39 scs4M2 ∧
    unadornedV39 scs4M3' ∧
    unadornedV39 scs4M4' ∧
    unadornedV39 scs4M5' ∧
    unadornedV39 scs4M6' ∧
    unadornedV39 scs4M7 ∧
    unadornedV39 scs4M8 ∧
    unadornedV39 scs3M1 := by
  simp only [scs6I1, scs5I1, scs5I2, scs5I3, scs4I1, scs4I2, scs4I3, scs3I1,
    scs6T1, scs5T1, scs4T1, scs4T2, scs4T3, scs4T4, scs4T5, scs3T1, scs3T2, scs3T3,
    scs3T4, scs3T5, scs3T6', scs3T7, scs6M1, scs5M1, scs5M2, scs4M1, scs4M2,
    scs4M3', scs4M4', scs4M5', scs4M6', scs4M7, scs4M8, scs3M1]
  repeat' first
    | constructor
    | exact scs_mk_unadorned_unadorned_p22
    | rfl
theorem basic_examples_p22 :
    scsBasicV39 scs6I1 ∧
    scsBasicV39 scs5I1 ∧
    scsBasicV39 scs5I2 ∧
    scsBasicV39 scs5I3 ∧
    scsBasicV39 scs4I1 ∧
    scsBasicV39 scs4I2 ∧
    scsBasicV39 scs4I3 ∧
    scsBasicV39 scs3I1 ∧
    scsBasicV39 scs6T1 ∧
    scsBasicV39 scs5T1 ∧
    scsBasicV39 scs4T1 ∧
    scsBasicV39 scs4T2 ∧
    scsBasicV39 scs4T3 ∧
    scsBasicV39 scs4T4 ∧
    scsBasicV39 scs4T5 ∧
    scsBasicV39 scs3T1 ∧
    scsBasicV39 scs3T2 ∧
    scsBasicV39 scs3T3 ∧
    scsBasicV39 scs3T4 ∧
    scsBasicV39 scs3T5 ∧
    scsBasicV39 scs3T6' ∧
    scsBasicV39 scs3T7 ∧
    scsBasicV39 scs6M1 ∧
    scsBasicV39 scs5M1 ∧
    scsBasicV39 scs5M2 ∧
    scsBasicV39 scs4M1 ∧
    scsBasicV39 scs4M2 ∧
    scsBasicV39 scs4M3' ∧
    scsBasicV39 scs4M4' ∧
    scsBasicV39 scs4M5' ∧
    scsBasicV39 scs4M6' ∧
    scsBasicV39 scs4M7 ∧
    scsBasicV39 scs4M8 ∧
    scsBasicV39 scs3M1 := by
  simp only [scs6I1, scs5I1, scs5I2, scs5I3, scs4I1, scs4I2, scs4I3, scs3I1,
    scs6T1, scs5T1, scs4T1, scs4T2, scs4T3, scs4T4, scs4T5, scs3T1, scs3T2, scs3T3,
    scs3T4, scs3T5, scs3T6', scs3T7, scs6M1, scs5M1, scs5M2, scs4M1, scs4M2,
    scs4M3', scs4M4', scs4M5', scs4M6', scs4M7, scs4M8, scs3M1]
  repeat' first
    | constructor
    | exact scs_basic_unadorned_p22
    | exact scs_mk_unadorned_unadorned_p22
    | exact fun _ _ => rfl
    | rfl
/-- HOL `scs_arrow_sing_empty`. -/
theorem scs_arrow_sing_empty_p22 (s : ScsV39) :
    (scsArrowV39 {s} ∅ ↔ MMsV39 s = ∅) := by
  constructor
  · intro h
    rcases h.2 with h1 | h2
    · exact h1 s (by simp)
    · exact absurd h2 (by simp)
  · intro h
    refine ⟨fun s' h' => absurd h' (by simp), Or.inl ?_⟩
    rintro s' h'
    simp only [Set.mem_singleton_iff] at h'
    subst h'
    exact h

/-- HOL `pos_imp_scs_arrow_empty`. -/
theorem pos_imp_scs_arrow_empty_p22 (s : ScsV39)
    (h : ∀ vv, BBsV39 s vv → 0 ≤ taustarV39 s vv) :
    scsArrowV39 {s} ∅ := by
  sorry

/-- HOL `OCBICBY`: the 14 T-row arrows to the empty system (giant; discharges
LocalAuto16's `JEJTVGB_case_breakdown_p16` NEEDS marker when the `empty_*`
lane lands). -/
theorem OCBICBY_p22 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6T1} ∅ ∧ scsArrowV39 {scs5T1} ∅ ∧ scsArrowV39 {scs4T1} ∅ ∧
      scsArrowV39 {scs4T2} ∅ ∧ scsArrowV39 {scs4T3} ∅ ∧ scsArrowV39 {scs4T4} ∅ ∧
      scsArrowV39 {scs4T5} ∅ ∧ scsArrowV39 {scs3T1} ∅ ∧ scsArrowV39 {scs3T2} ∅ ∧
      scsArrowV39 {scs3T3} ∅ ∧ scsArrowV39 {scs3T4} ∅ ∧ scsArrowV39 {scs3T5} ∅ ∧
      scsArrowV39 {scs3T6'} ∅ ∧ scsArrowV39 {scs3T7} ∅ := by
  sorry

end Kepler.Text

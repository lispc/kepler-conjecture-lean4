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
    `reEqvl` (PackingAuto18)).  DEDUP 2026-09-17: the sphere-kit `_p22`
    copies (atn2/dih_x/dih_y/delta_y/delta_x5/delta4_y/num1/dnum1 and the
    `taum`/`sol_y` stubs — verbatim twins of the LocalAuto16 `_p16` lane)
    are deleted against `Kepler.Text.SphereKit` (bodies verified
    identical; `taum`/`sol_y` upgrade from sorry stubs to the real
    bodies).
    Same-wave lanes LocalAuto19-21/23-27 are NOT imported; any helper that
    would live there is carried as a `_p22` copy with a NEEDS marker.
  - `_p22` copies still here: `deltaX6_p22` (partial of `delta_x` at x6;
    SphereKit defers `delta_x6`), `const1_p22` (`sol0 / π` rendering —
    SphereKit's `const1` uses the `sol_y 2..2` rendering; not verbatim
    twins, both kept this pass), `eulerP_p22`/`eulerAX_p22` (opaque
    registry signatures), `acsP22` (flyspeck `acs` = `Real.arccos`),
    `ineqP22` (sphere.hl `ineq`).  The reconstructed Terminal.hl bodies
    (`num1`/`dnum1`) moved verbatim into SphereKit (DEDUP 2026-09-17).
  - HOL `delta_x`/`delta_x4`/`delta_x5` ↔ canonical `deltaX`/`deltaX4`/
    `deltaX5` (`Kepler.Text.SphereKit` since DEDUP 2026-09-17; `deltaX5`
    is the corrected 6-term body — LocalAuto1's mis-port was fixed
    2026-09-17, so `derived_form_delta_x_wrt_x5_p22` still holds by
    construction).
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `dist(v,w)` ↔
    `dist v w`; `dih_x` ↔ `dihXf`; `delta_x` ↔ `deltaX`;
    `delta_y` ↔ `deltaY`; `dih_y` ↔ `dihY`; `taum` ↔ `taum` (all canonical
    `Kepler.Text.SphereKit` names since DEDUP 2026-09-17);
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
-- LANE rrcw-weak-p26 (2026-11-06): `RRCWNS_WEAK_p22` is the HOL assembly
-- `CIZMRRH` + `JKQEWGV2` + `JKQEWGV3` + `INTERIOR_ANGLE1_AZIM` + `SYNQIWN`.
-- The trichotomy (`CIZMRRH`, LA3), the not-circular theorem (`JKQEWGV2_p23`,
-- LA23) and the lunar interior-angle bound (`JKQEWGV3_p23`, LA23) have no
-- `_p22` twins and no other producers anywhere in the tree, so the file
-- imports the LA23 lane module (acyclic: LA23's closure is LA1/2/3/4/5/9 +
-- `AzimBridge`/`CircularSolKit`/`ClosedSyKit`/`SphereKit`, which does not
-- contain LA22).  See DELIVERY.md `rrcw-weak-p26` for the sign-off note:
-- this supersedes the "same-wave lanes 19-21/23-27 are NOT imported" note
-- in the file header for this one item.
import Kepler.Text.LocalAuto23
import Kepler.Text.SphereKit
import Kepler.Geom.Aff
import Kepler.Geom.Azim
-- LA22MONO (2026-11-12, lane `la22mono-w1`): the x4/x5/x6 `dihXf`
-- partials consumed by the new taum-monotonicity kit below are the proved
-- `Gamma4Deriv2` values (HOL `OCBICBY.derived_form_dih_x_wrt_x4/5/6`).
-- The local `derived_form_dih_x_wrt_x*_p22` twins remain unproved for
-- their own (untouched) consumers.
import Kepler.Text.Gamma4Deriv2
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p22` copies of the sphere.hl / Terminal.hl kit

-- DEDUP 2026-09-17: the verbatim sphere-kit `_p22` copies that used to sit
-- here (y_of_x, atn2, dih_x, dih_y, delta_y, delta_x5, delta4_y, num1,
-- dnum1, and the `taum`/`sol_y` sorry stubs) are deleted against the
-- canonical `Kepler.Text.SphereKit` definitions — every body was verified
-- identical before deletion (the corrected 6-term `delta_x5` body
-- included, so `derived_form_delta_x_wrt_x5_p22` is unchanged in content).
-- The `taum`/`solY` stubs upgrade to SphereKit's real bodies: statements
-- keep their signatures, and no non-`sorry` proof exploited their opacity
-- (all consumers are `sorry`-proved here).  Remaining uses resolve through
-- the SphereKit import.  KEPT below: `deltaX6_p22` (SphereKit defers
-- `delta_x6`) and `const1_p22` (different rendering from SphereKit's
-- `const1`; not a verbatim twin). -/

/-- HOL `delta_x6` (sphere.hl): partial derivative of `delta_x` at `x6`
(no prior port; the canonical `deltaX5` is the x5 twin). KEEP: SphereKit
defers `delta_x6`. -/
noncomputable def deltaX6_p22 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x2 * x5 - x1 * x2 - x4 * x5 - x3 * x6
    + x3 * (x1 + x2 - x3 + x4 + x5 - x6)

/-- HOL `const1` (Terminal.hl): `sol0 / pi`. KEPT: different rendering
from SphereKit's `const1` (`solY 2 2 2 2 2 2 / π`); not a verbatim twin. -/
noncomputable def const1_p22 : ℝ := sol0 / Real.pi

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
    (hd : yOfX (deltaX4) (dist v0 v1) (dist v0 v2) (dist v0 v3)
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
    yOfX (eulerAX_p22) (dist v0 v1) (dist v0 v2) (dist v0 v3)
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

/-- HOL `derived_form_delta_x_wrt_x5` (with `deltaX5`). -/
theorem derived_form_delta_x_wrt_x5_p22 (x1 x2 x3 x4 x5 x6 : ℝ) :
    derivedForm True (fun q => deltaX x1 x2 x3 x4 q x6)
      (deltaX5 x1 x2 x3 x4 x5 x6) x5 Set.univ := by
  intro _
  have e : (fun q => deltaX x1 x2 x3 x4 q x6) = fun q =>
      (-(x2)) * (q * q)
        + ((x2 * (x1 - x2 + x3 + x4 + x6) + x1 * x4 + x3 * x6 - x4 * x6 - x1 * x3) * q
        + (x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6)
          - x2 * x3 * x4 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  have dv : (-(x2)) * (x5 + x5)
      + (x2 * (x1 - x2 + x3 + x4 + x6) + x1 * x4 + x3 * x6 - x4 * x6 - x1 * x3)
      = deltaX5 x1 x2 x3 x4 x5 x6 := by
    unfold deltaX5; ring
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
      64 * deltaY y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2 := by
  unfold deltaY
  unfold deltaX
  field_simp
  ring

/-- HOL `delta_x_xrr`. -/
theorem delta_x_xrr_p22 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (hy3 : y3 ≠ 0) :
    deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) =
      64 * deltaY y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2 := by
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
      16 * yOfX (deltaX4) y1 y2 y3 y4 y5 y6 / (y1 * y1 * y2 * y3) := by
  unfold deltaX4 yOfX
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
    derivedForm True (fun q => dihXf x1 x2 x3 q x5 x6)
      (Real.sqrt x1 / Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) x4 Set.univ := by
  sorry

/-- HOL `derived_form_dih_x_wrt_x5`. -/
theorem derived_form_dih_x_wrt_x5_p22 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h3 : 0 < upsX x1 x2 x6) (h4 : 0 < upsX x1 x3 x5) :
    derivedForm True (fun q => dihXf x1 x2 x3 x4 q x6)
      (-(Real.sqrt x1 * deltaX6_p22 x1 x2 x3 x4 x5 x6
        / (upsX x1 x3 x5 * Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)))) x5 Set.univ := by
  sorry

/-- HOL `derived_form_dih_x_wrt_x6`. -/
theorem derived_form_dih_x_wrt_x6_p22 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h3 : 0 < upsX x1 x2 x6) (h4 : 0 < upsX x1 x3 x5) :
    derivedForm True (fun q => dihXf x1 x2 x3 x4 x5 q)
      (-(Real.sqrt x1 * deltaX5 x1 x2 x3 x4 x5 x6
        / (upsX x1 x2 x6 * Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)))) x6 Set.univ := by
  sorry

/-- HOL `derived_form_num1`. -/
theorem derived_form_num1_p22 (x4 x5 x6 e1 e2 e3 : ℝ) :
    derivedForm True (fun q => num1 e1 e2 e3 q x5 x6)
      (4 * ((16 - 2 * x4) * e1 + (x5 - 8) * e2 + (x6 - 8) * e3)) x4 Set.univ := by
  intro _
  have e : (fun q => num1 e1 e2 e3 q x5 x6) = fun q =>
      (-(4 * e1)) * (q * q)
        + ((64 * e1 + 4 * (x5 - 8) * e2 + 4 * (x6 - 8) * e3) * q
          - 32 * (x5 - x6) * (e2 - e3)) := by
    funext q; unfold num1; ring
  rw [e]
  refine HasDerivWithinAt.congr_deriv
    (hasDerivWithinAt_quad_p22 _ _ _ x4 Set.univ) ?_
  ring

/-- HOL `derived_form_dnum1`. -/
theorem derived_form_dnum1_p22 (x4 x5 x6 e1 e2 e3 : ℝ) :
    derivedForm True (fun q => num1 e1 e2 e3 q x5 x6)
      (4 * dnum1 e1 e2 e3 x4 x5 x6) x4 Set.univ := by
  intro _
  have e : (fun q => num1 e1 e2 e3 q x5 x6) = fun q =>
      (-(4 * e1)) * (q * q)
        + ((64 * e1 + 4 * (x5 - 8) * e2 + 4 * (x6 - 8) * e3) * q
          - 32 * (x5 - x6) * (e2 - e3)) := by
    funext q; unfold num1; ring
  rw [e]
  refine HasDerivWithinAt.congr_deriv
    (hasDerivWithinAt_quad_p22 _ _ _ x4 Set.univ) ?_
  unfold dnum1
  ring

/-- HOL `derived_form_sum_dih` (NEEDS the dih_x derivative kit). -/
theorem derived_form_sum_dih_p22 (x1 x2 x3 x4 x5 x6 e1 e2 e3 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3)
    (h4 : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h5 : 0 < upsX x1 x2 x6) (h6 : 0 < upsX x1 x3 x5) (h7 : 0 < upsX x2 x3 x4) :
    derivedForm True
      (fun q => e1 * dihXf x1 x2 x3 q x5 x6
        + e2 * dihXf x2 x3 x1 x5 x6 q
        + e3 * dihXf x3 x1 x2 x6 q x5)
      ((e1 * Real.sqrt x1 * upsX x2 x3 x4
        - e2 * Real.sqrt x2 * deltaX6_p22 x1 x2 x3 x4 x5 x6
        - e3 * Real.sqrt x3 * deltaX5 x1 x2 x3 x4 x5 x6)
        / (upsX x2 x3 x4 * Real.sqrt (deltaX x1 x2 x3 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_sum_dih444`. -/
theorem derived_form_sum_dih444_p22 (x4 x5 x6 e1 e2 e3 : ℝ)
    (h4 : 0 < x4 ∧ x4 < 16) (h5 : 0 < x5 ∧ x5 < 16) (h6 : 0 < x6 ∧ x6 < 16)
    (hd : 0 < deltaX 4 4 4 x4 x5 x6) :
    derivedForm True
      (fun q => e1 * dihXf 4 4 4 q x5 x6
        + e2 * dihXf 4 4 4 x5 x6 q
        + e3 * dihXf 4 4 4 x6 q x5)
      (num1 e1 e2 e3 x4 x5 x6
        / (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_sum_dih444sub`. -/
theorem derived_form_sum_dih444sub_p22 (x4 x5 x6 e1 e2 e3 : ℝ)
    (h4 : 0 < x4 ∧ x4 < 16) (h5 : 0 < x5 ∧ x5 < 16) (h6 : 0 < x6 ∧ x6 < 16)
    (hd : 0 < deltaX 4 4 4 x4 x5 x6) :
    derivedForm True
      (fun q => e1 * dihXf 4 4 4 q x5 x6
        + e2 * dihXf 4 4 4 x5 x6 q
        + e3 * dihXf 4 4 4 x6 q x5 - (1 + const1_p22) * Real.pi)
      (num1 e1 e2 e3 x4 x5 x6
        / (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_tau2D`. -/
theorem derived_form_tau2D_p22 (x4 x5 x6 e1 e2 e3 : ℝ)
    (h4 : 0 < x4 ∧ x4 < 16) (h5 : 0 < x5 ∧ x5 < 16) (h6 : 0 < x6 ∧ x6 < 16)
    (hd : 0 < deltaX 4 4 4 x4 x5 x6) (hnum : num1 e1 e2 e3 x4 x5 x6 = 0) :
    derivedForm True
      (fun q => num1 e1 e2 e3 q x5 x6
        / (2 * q * (16 - q) * Real.sqrt (deltaX 4 4 4 q x5 x6)))
      (4 * dnum1 e1 e2 e3 x4 x5 x6
        / (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 Set.univ := by
  sorry

/-- HOL `derived_form_taum_d3_exists`. -/
theorem derived_form_taum_d3_exists_p22 (x4 x5 x6 e1 e2 e3 : ℝ) :
    ∃ f'' : ℝ → ℝ, ∃ f''' : ℝ,
      (0 < x4 ∧ x4 < 16 ∧ 0 < x5 ∧ x5 < 16 ∧ 0 < x6 ∧ x6 < 16 ∧
        0 < deltaX 4 4 4 x4 x5 x6) →
      (∀ x4', 0 < x4' → x4' < 16 → 0 < deltaX 4 4 4 x4' x5 x6 →
        derivedForm True
          (fun q => num1 e1 e2 e3 q x5 x6
            / (2 * q * (16 - q) * Real.sqrt (deltaX 4 4 4 q x5 x6)))
          (f'' x4') x4' Set.univ) ∧
      derivedForm True f'' f''' x4 Set.univ := by
  sorry

/-- HOL `dih_x_dim_reduction` (NEEDS the atn2 positive-scaling lemma). -/
theorem dih_x_dim_reduction_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    dihXf 4 4 4 (8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)))
        (8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)))
        (8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))) =
      dihY y1 y2 y3 y4 y5 y6 := by
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
    (0 < deltaY y1 y2 y3 y4 y5 y6 ↔
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
      0 < deltaY y1 y2 y3 y y5 y6} := by
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
    (hsub : Set.Ioo a b ⊆ {y | 0 < deltaY y1 y2 y3 y y5 y6 ∧ 0 < y ∧
      0 < upsX (y2 * y2) (y3 * y3) (y * y)})
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5))
    (hcrit : num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
        (xrr y1 y2 y6) = 0 →
      dnum1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
        (xrr y1 y2 y6) < 0) :
    ∃ y4', y4' ∈ Set.Ioo a b ∧ taum y1 y2 y3 y4' y5 y6 < taum y1 y2 y3 y4 y5 y6 := by
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
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hy4 : 0 < y4)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5))
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hn : 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
      (xrr y1 y2 y6)) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum y1 y2 y3 y4' y5 y6 < taum y1 y2 y3 y4'' y5 y6 := by
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

/-! ## `xrr` simple-bounds kit (early copies)

Private helper block added 2026-11-12 (lane `la22aux-w1`): early copies of
HOL `xrr_decreasing` + `xrr_simple_lower_bound` + `xrr_simple_upper_bound`
placed ahead of `xrr_simple_lower_bound_p22` / `xrr_simple_upper_bound_p22`
so the public proved theorems can consume them (Lean declaration order).
The `La22TaumMonoKit` block below keeps the original `la22_xrr_*` copies
(consumed by `LEMMA_4828966562_p22`); bodies are identical. -/
section La22XrrSimpleKit

private theorem la22aux_xrr_decreasing (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
    (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2' : y2 ≤ 2 * h0) (hlt : y1 ≤ y1') :
    xrr y1' y2 y6 ≤ xrr y1 y2 y6 := by
  have hp1 : (0:ℝ) < y1 := by linarith
  have hp1' : (0:ℝ) < y1' := by linarith
  have hp2 : (0:ℝ) < y2 := by linarith
  have hdiff : xrr y1 y2 y6 - xrr y1' y2 y6
      = 4 * (y1' - y1) * (y1 * y1' + y6 * y6 - y2 * y2) / (y1 * y1' * y2) := by
    unfold xrr
    field_simp
    ring
  have h0v : (2 * h0) * (2 * h0) = 6.3504 := by norm_num [h0_eq_p22]
  have hnn : 0 ≤ y1 * y1' + y6 * y6 - y2 * y2 := by
    have h22 : y2 * y2 ≤ (2 * h0) * (2 * h0) := by nlinarith
    nlinarith
  have hle : 0 ≤ 4 * (y1' - y1) * (y1 * y1' + y6 * y6 - y2 * y2) / (y1 * y1' * y2) := by
    positivity
  linarith

private theorem la22aux_xrr_simple_lower (y1 y2 y6 y6inf : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6inf) (hy6' : y6inf ≤ y6) :
    (y6inf / h0) ^ 2 ≤ xrr y1 y2 y6 := by
  have h1 : xrr (2 * h0) y2 y6 ≤ xrr y1 y2 y6 :=
    la22aux_xrr_decreasing y1 (2 * h0) y2 y6 hy1 (by linarith) hy2 (by linarith) hy2' hy1'
  have h2 : xrr (2 * h0) (2 * h0) y6 ≤ xrr (2 * h0) y2 y6 := by
    have h := la22aux_xrr_decreasing y2 (2 * h0) (2 * h0) y6 hy2 (by linarith)
      (by linarith) (by linarith) le_rfl hy2'
    rwa [xrr_sym_p22 y2 (2 * h0) y6] at h
  have h3 : xrr (2 * h0) (2 * h0) y6inf ≤ xrr (2 * h0) (2 * h0) y6 := by
    rcases lt_or_eq_of_le hy6' with hlt | heq
    · exact le_of_lt (xrr_increasing_p22 _ _ _ _ (by linarith) (by linarith) (by linarith) hlt)
    · rw [heq]
  have h4 : xrr (2 * h0) (2 * h0) y6inf = (y6inf / h0) ^ 2 := by
    have h0ne : (h0 : ℝ) ≠ 0 := by norm_num [h0_eq_p22]
    unfold xrr
    field_simp
    ring
  linarith

private theorem la22aux_xrr_simple_upper (y1 y2 y6 y6sup : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ y6sup)
    (_hy6sup : y6sup < 4) :
    xrr y1 y2 y6 ≤ y6sup ^ 2 := by
  have h1 : xrr y1 y2 y6 ≤ xrr 2 y2 y6 :=
    la22aux_xrr_decreasing 2 y1 y2 y6 (by norm_num) hy1 hy2 hy6 hy2' hy1
  have h2 : xrr 2 y2 y6 ≤ xrr 2 2 y6 := by
    have h := la22aux_xrr_decreasing 2 y2 2 y6 (by norm_num) hy2 (by norm_num) hy6
      (by linarith) hy2
    rw [xrr_sym_p22 2 y2 y6]
    exact h
  have h3 : xrr 2 2 y6 ≤ xrr 2 2 y6sup := by
    rcases lt_or_eq_of_le hy6' with hlt | heq
    · exact le_of_lt (xrr_increasing_p22 2 2 y6 y6sup (by norm_num) (by norm_num) (by linarith) hlt)
    · rw [heq]
  have h4 : xrr 2 2 y6sup = y6sup ^ 2 := by
    unfold xrr
    field_simp
    ring
  linarith

end La22XrrSimpleKit

/-- HOL `xrr_decreasing`. -/
theorem xrr_decreasing_p22 (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
    (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2' : y2 ≤ 2 * h0) (hlt : y1 ≤ y1') :
    xrr y1' y2 y6 ≤ xrr y1 y2 y6 := by
  sorry

/-- HOL `xrr_simple_lower_bound`. -/
-- PROVED 2026-11-12 (lane `la22aux-w1`): from the early `La22XrrSimpleKit`
-- copy `la22aux_xrr_simple_lower` (HOL route:
-- `xrr (&2*h0) y2 y6` / `xrr (&2*h0) (&2*h0) y6` intermediates, two
-- `xrr_decreasing` + one `xrr_increasing`, endpoint evaluation).
theorem xrr_simple_lower_bound_p22 (y1 y2 y6 y6inf : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6inf) (hy6' : y6inf ≤ y6) :
    (y6inf / h0) ^ 2 ≤ xrr y1 y2 y6 := by
  exact la22aux_xrr_simple_lower y1 y2 y6 y6inf hy1 hy1' hy2 hy2' hy6 hy6'

/-- HOL `xrr_simple_upper_bound`. -/
-- PROVED 2026-11-12 (lane `la22aux-w1`): from the early `La22XrrSimpleKit`
-- copy `la22aux_xrr_simple_upper` (HOL route:
-- `xrr &2 y2 y6` / `xrr &2 &2 y6` intermediates, two `xrr_decreasing` +
-- one `xrr_increasing`, endpoint evaluation).
theorem xrr_simple_upper_bound_p22 (y1 y2 y6 y6sup : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ y6sup)
    (hy6sup : y6sup < 4) :
    xrr y1 y2 y6 ≤ y6sup ^ 2 := by
  exact la22aux_xrr_simple_upper y1 y2 y6 y6sup hy1 hy1' hy2 hy2' hy6 hy6' hy6sup

/-- HOL `taum_compose_xrr` (NEEDS the real `taum` body). -/
theorem taum_compose_xrr_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    (fun q => taum y1 y2 y3 q y5 y6) y4 =
      (fun q => rho y1 * dihXf 4 4 4 q (xrr y1 y3 y5) (xrr y1 y2 y6)
        + rho y2 * dihXf 4 4 4 (xrr y1 y3 y5) (xrr y1 y2 y6) q
        + rho y3 * dihXf 4 4 4 (xrr y1 y2 y6) q (xrr y1 y3 y5)
        - (1 + const1_p22) * Real.pi) ((fun q => xrr y2 y3 q) y4) := by
  sorry

/-- HOL `real_open_delta_y` (NEEDS `dih`/`delta` continuity). -/
theorem real_open_delta_y_p22 (y1 y2 y3 y5 y6 : ℝ) :
    IsOpen {y4 | 0 < y4 ∧ 0 < deltaY y1 y2 y3 y4 y5 y6} := by
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

/-- `psort` reads unordered residue pairs: `psort k (j, i) = psort k (i, j)`
(hexagons.hl `PSORT` symmetry; port of LocalAuto20's `periodic2_funlist_p20`
support kit, which LA22 cannot import — LA20 imports LA22). -/
private theorem la22psort_swap (k : ℕ) (i j : ℕ) : psort k (j, i) = psort k (i, j) := by
  simp only [psort]
  rcases Nat.lt_trichotomy (i % k) (j % k) with h | h | h
  · rw [if_neg (Nat.not_le.mpr h), if_pos (Nat.le_of_lt h)]
  · have h1 : i % k ≤ j % k := Nat.le_of_eq h
    have h2 : j % k ≤ i % k := Nat.le_of_eq h.symm
    rw [if_pos h2, if_pos h1, h]
  · rw [if_pos (Nat.le_of_lt h), if_neg (Nat.not_le.mpr h)]

/-- `Periodic2` backward in both coordinates (residue reduction); funlist-case
edition of `la22periodic2_mod` below, hoisted ahead of the generator. -/
private theorem la22p2mod_fun {α : Sort u} {f : ℕ → ℕ → α} {n : ℕ}
    (hf : Periodic2 f n) (i j : ℕ) : f (i % n) (j % n) = f i j := by
  have hfirst : ∀ q r j, f (q * n + r) j = f r j := by
    intro q
    induction q with
    | zero => intro r j; simp
    | succ q ih =>
      intro r j
      have h1 : f (q * n + r + n) j = f (q * n + r) j := (hf _ j).1
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r j]
  have hsecond : ∀ q r i, f i (q * n + r) = f i r := by
    intro q
    induction q with
    | zero => intro r i; simp
    | succ q ih =>
      intro r i
      have h1 : f i (q * n + r + n) = f i (q * n + r) := (hf _ _).2
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r i]
  conv_rhs => rw [show i = i / n * n + i % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod i n).symm]
  rw [hfirst]
  conv_rhs => rw [show j = j / n * n + j % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod j n).symm]
  rw [hsecond]

/-- `funlist_v39` tables are `k`-periodic (hexagons.hl `PSORT_3456_PERIODIC`). -/
private theorem la22funlist_periodic2 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k : ℕ) :
    Periodic2 (funlistV39 data d k) k := by
  intro i j
  simp [funlistV39, psort, Nat.add_mod_right]

/-- `funlist_v39` reads unordered residue pairs. -/
private theorem la22funlist_sym (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i j : ℕ) :
    funlistV39 data d k i j = funlistV39 data d k j i := by
  unfold funlistV39
  rw [la22psort_swap k j i]
  by_cases h : i % k = j % k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `funlist_v39` edge entries read residues: the `(i, i + 1)` entry equals the
`(i % k, i % k + 1)` entry (JOTSWIX.hl:241-257 mod reduction). -/
private theorem la22funlist_edge_mod (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i : ℕ)
    (hk : 0 < k) :
    funlistV39 data d k i (i + 1) = funlistV39 data d k (i % k) (i % k + 1) := by
  have hper : Periodic2 (funlistV39 data d k) k := la22funlist_periodic2 data d k
  have hz : i % k < k := Nat.mod_lt i hk
  rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
  · have he : (i + 1) % k = i % k + 1 := by
      rw [← Nat.mod_add_mod i k 1]
      exact Nat.mod_eq_of_lt hlt
    rw [← la22p2mod_fun hper i (i + 1), he]
  · have heq : i % k + 1 = k := by omega
    have he : (i + 1) % k = 0 := by
      rw [← Nat.mod_add_mod i k 1, heq]
      exact Nat.mod_self k
    have hback : funlistV39 data d k (i % k) (i % k + 1) = funlistV39 data d k (i % k) 0 := by
      rw [heq]
      have h1 : funlistV39 data d k (i % k) (0 + k) = funlistV39 data d k (i % k) 0 :=
        (hper (i % k) 0).2
      rw [Nat.zero_add] at h1
      exact h1
    rw [← la22p2mod_fun hper i (i + 1), he, ← hback]

/-- HOL `is_scs_funlist_basic`: the funlist case-bank generator. An unadorned
system with `funlist_v39` tables is `is_scs` exactly when the slot hypotheses
hold (periodicity/symmetry/diag-zero come from the `psort`/`assocd` machine,
proved via the private kit above; the `a ≤ b` chain slot of HOL is vacuous in
the Lean `isScsV39` encoding). -/
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
  have hpa : Periodic2 (funlistV39 a0 d k) k := la22funlist_periodic2 a0 d k
  have hpb : Periodic2 (funlistV39 b0 d k) k := la22funlist_periodic2 b0 d k
  -- the `a ≤ bm` chain slot: `hchain` transported off the `i < j < k` window by
  -- residue reduction and table symmetry (the two `le_refl` slots are `a = am`,
  -- `bm = b` for unadorned systems)
  have hmid : ∀ i j, funlistV39 a0 d k i j ≤ funlistV39 b0 d k i j := by
    intro i j
    rw [← la22p2mod_fun hpa i j, ← la22p2mod_fun hpb i j]
    have hik : i % k < k := Nat.mod_lt i (by omega)
    have hjk : j % k < k := Nat.mod_lt j (by omega)
    rcases Nat.lt_trichotomy (i % k) (j % k) with h | h | h
    · exact hchain (i % k) (j % k) ⟨h, hjk⟩
    · rw [h]
      exact le_of_eq (by simp [funlistV39])
    · rw [la22funlist_sym a0 d k (i % k) (j % k), la22funlist_sym b0 d k (i % k) (j % k)]
      exact hchain (j % k) (i % k) ⟨h, hik⟩
  unfold isScsV39
  dsimp only [mkUnadornedV39]
  refine ⟨hd, hk1, hk2, periodic_empty k, periodic_empty k, periodic_empty k,
    periodic_empty k, hpa, hpa, hpb, hpb, fun _ _ => ⟨rfl, rfl⟩,
    fun i j => ⟨la22funlist_sym a0 d k i j, la22funlist_sym a0 d k i j,
      la22funlist_sym b0 d k i j, la22funlist_sym b0 d k i j, rfl⟩,
    fun i j => ⟨le_refl _, hmid i j, le_refl _⟩,
    fun i => by simp [funlistV39], ?_, ?_, ?_,
    fun _ _ hJ => False.elim hJ, fun _ _ hJ => False.elim hJ, hcard⟩
  · intro i j ⟨hik, hjk, hne⟩
    by_cases hij : i < j
    · exact ha i j ⟨hij, hjk⟩
    · have hji : j < i := lt_of_le_of_ne (Nat.le_of_not_lt hij) (fun he => hne he.symm)
      rw [la22funlist_sym a0 d k i j]
      exact ha j i ⟨hji, hik⟩
  · intro i hk3
    subst hk3
    rw [la22funlist_edge_mod b0 d 3 i (by omega)]
    exact hb3 (i % 3) ⟨Nat.mod_lt i (by omega), rfl⟩
  · intro i hk3
    rw [la22funlist_edge_mod b0 d k i (by omega)]
    exact hbk (i % k) ⟨Nat.mod_lt i (by omega), hk3⟩

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
-- PROVED 2026-11-12 (lane `la22aux-w1`): HOL chain
-- `azim_in_fan_azim` + `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM` +
-- `vv_rho_node1` + `vv_inj_lemma` + `INTERIOR_ANGLE1_POS`, reproduced on the
-- definitional `rhoNode1`/`ivsRhoNode1` route (same as `RRCWNS_WEAK_p22`):
-- `interiorAngle1 0 FF (vv i) = azim 0 (vv i) (vv (i+1)) (vv (i+(k-1)))`
-- by `DETER_RHO_NODE` + `PRE_IVS_RHO_NODE1_DETE`, then fan positivity.
theorem LOCAL_FAN_AZIM_POS_p22 (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (h1 : isScsV39 s) (h2 : BBsV39 s vv) :
    0 < azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) := by
  -- the fan is a `localFan_p2` (`LocalFan` ↦ `localFan_p3` ↦ `localFan_p2`)
  have hlf : LocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) := hcf.1
  have hlf2 : localFan_p2 (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) :=
    localFan_p2.of_localFan_p3 (localFanEquiv_p35.mp hlf)
  have hk3 : 3 ≤ s.k := h1.2.1
  -- rho-node is the successor, inverse-rho-node is the predecessor
  have hrn : rhoNode1 (Set.range fun i => (vv i, vv (i + 1))) (vv i) = vv (i + 1) := by
    have hrp : rhoNode1_p2 (Set.range fun i => (vv i, vv (i + 1))) (vv i) = vv (i + 1) :=
      DETER_RHO_NODE hlf2 (v := vv i) (w := vv (i + 1))
        (show (vv i, vv (i + 1)) ∈ (Set.range fun i => (vv i, vv (i + 1)))
          from Set.mem_range.mpr ⟨i, rfl⟩)
    simpa only [rhoNode1, rhoNode1_p2] using hrp
  have hivs : ivsRhoNode1 (Set.range fun i => (vv i, vv (i + 1))) (vv i)
      = vv (i + (s.k - 1)) := by
    have hmem : (vv (i + (s.k - 1)), vv i) ∈ (Set.range fun i => (vv i, vv (i + 1))) := by
      refine Set.mem_range.mpr ⟨i + (s.k - 1), ?_⟩
      have hper : vv (i + (s.k - 1) + 1) = vv i := by
        rw [show i + (s.k - 1) + 1 = i + s.k by omega]
        exact h2.2.1 i
      rw [hper]
    have hip : ivsRhoNode1_p2 (Set.range fun i => (vv i, vv (i + 1))) (vv i)
        = vv (i + (s.k - 1)) :=
      PRE_IVS_RHO_NODE1_DETE hlf2 hmem
    simpa only [ivsRhoNode1, ivsRhoNode1_p2] using hip
  have hid : interiorAngle1 0 (Set.range fun i => (vv i, vv (i + 1))) (vv i)
      = azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) := by
    simp only [interiorAngle1, hrn, hivs]
  rw [← hid]
  exact INTERIOR_ANGLE1_POS hlf2 (Set.mem_range_self i)

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
    Real.pi / 2 < dihXf x1 x2 x3 x4 x5 x6 := by
  sorry

/-- HOL `delta4_y_imp_obtuse`. -/
theorem delta4_y_imp_obtuse_p22 (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1 : 0 < y1) (h2 : 0 ≤ deltaY y1 y2 y3 y4 y5 y6)
    (h3 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    Real.pi / 2 < dihY y1 y2 y3 y4 y5 y6 := by
  sorry

/-- `Periodic` backward: the value at an index agrees with the value at its
residue (iterate `Periodic` along the quotient). -/
private theorem la22periodic_mod {α : Sort u} {f : ℕ → α} {n : ℕ} (hper : Periodic f n) :
    ∀ m, f (m % n) = f m := by
  have hstep : ∀ q r, f (q * n + r) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have h1 : f (q * n + r + n) = f (q * n + r) := hper _
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r]
  intro m
  conv_rhs => rw [show m = m / n * n + m % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod m n).symm]
  rw [hstep]

/-- `Periodic2` backward in both coordinates (residue reduction). -/
private theorem la22periodic2_mod {α : Sort u} {f : ℕ → ℕ → α} {n : ℕ}
    (hf : Periodic2 f n) (i j : ℕ) : f (i % n) (j % n) = f i j := by
  have hfirst : ∀ q r j, f (q * n + r) j = f r j := by
    intro q
    induction q with
    | zero => intro r j; simp
    | succ q ih =>
      intro r j
      have h1 : f (q * n + r + n) j = f (q * n + r) j := (hf _ j).1
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r j]
  have hsecond : ∀ q r i, f i (q * n + r) = f i r := by
    intro q
    induction q with
    | zero => intro r i; simp
    | succ q ih =>
      intro r i
      have h1 : f i (q * n + r + n) = f i (q * n + r) := (hf _ _).2
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r i]
  conv_rhs => rw [show i = i / n * n + i % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod i n).symm]
  rw [hfirst]
  conv_rhs => rw [show j = j / n * n + j % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod j n).symm]
  rw [hsecond]

/-- HOL `scs_lb_2`: the `is_scs` off-diagonal bound `2 ≤ a i j`, transported
to arbitrary indices by the `a`-table periodicity (`scs_lb_2` NEEDS marker:
the periodic2-backward reduction, discharged by `la22periodic2_mod`). -/
theorem scs_lb_2_p22 (s : ScsV39) (vv : ℕ → V3) (i j : ℕ)
    (h1 : isScsV39 s) (h2 : BBsV39 s vv) (hne : i % s.k ≠ j % s.k) :
    2 ≤ dist (vv i) (vv j) := by
  obtain ⟨-, hk3, -, -, -, -, -, hpa, -, -, -, -, -, -, hdiag0, hdiag, -, -, -, -, -⟩ := h1
  obtain ⟨-, -, hdist, -⟩ := h2
  obtain ⟨hle, -⟩ := hdist i j
  have hk0 : 0 < s.k := by omega
  have hred : s.a (i % s.k) (j % s.k) = s.a i j := la22periodic2_mod hpa i j
  have hne' : i % s.k ≠ j % s.k := hne
  have h2le : 2 ≤ s.a (i % s.k) (j % s.k) :=
    hdiag _ _ ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, hne'⟩
  rw [hred] at h2le
  exact h2le.trans hle

/-! ## w5sg2_* private block (lane scsgeneric-w5b2): the `SYNQIWN_p22` kit.
HOL `SYNQIWN` (OCBICBY.hl:2506) was proved via the terminal inequality
certificates "1117202051"/"4559601669"/"4559601669b" plus the
azim -> dihV -> dih_y -> delta4_y chain (all outside this module's closure);
this port replaces that route by a direct `azim_master` coordinate computation:
`cos (azim 0 A B C) < 0` from the projection dot product
`B*C - (B.proj)(C.proj) = deltaX4(six squared lengths) / (4*|A|^2)`, whose
negativity is the six-way case box arithmetic of `w5sg2_delta4_cases`
(the same three certificate boxes, discharged by direct real arithmetic).
-/

/-- `Periodic` backward (LA22 twin of `la22periodic_mod`; local copy so the
block is self-contained). -/
private theorem w5sg2_periodic_mod {α : Sort u} {f : ℕ → α} {n : ℕ}
    (hper : Periodic f n) : ∀ m, f (m % n) = f m := by
  have hstep : ∀ q r, f (q * n + r) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have h1 : f (q * n + r + n) = f (q * n + r) := hper _
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r]
  intro m
  conv_rhs => rw [show m = m / n * n + m % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod m n).symm]
  rw [hstep]


/-- Annulus norm bounds (LA4 twin). -/
private theorem w5sg2_norm_bounds {v : V3} (hv : v ∈ ballAnnulus) :
    2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := by
  obtain ⟨hin, hnot⟩ := hv
  have h1 : ‖v‖ ≤ 2 * h0 := by
    simpa [dist_zero_right] using Metric.mem_closedBall.mp hin
  have h2 : 2 ≤ ‖v‖ := by
    have h3 : ¬ (dist v (0:V3) < 2) := hnot
    simpa [dist_zero_right] using h3
  exact ⟨h2, h1⟩

/-- HOL `SUC_MOD_NOT_EQ` (QKNVMLB.hl:3431). -/
private theorem w5sg2_suc_mod_not_eq {k : ℕ} (hk : 1 < k) (i : ℕ) :
    i % k ≠ (i + 1) % k := by
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have hik : i % k < k := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge (i % k + 1) k with h | h
  · rw [e1, Nat.mod_eq_of_lt (by omega : i % k + 1 < k)]
    omega
  · have hk1 : i % k + 1 = k := by omega
    rw [e1, hk1, Nat.mod_self]
    omega

/-- HOL `NONPARALLEL_BALL_ANNULUS` core (dih2k.hl:635 / LA4 aux, `cstab = 3.01`). -/
private theorem w5sg2_nonparallel_annulus {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (h2 : 2 ≤ ‖v - w‖) (hup : ‖v - w‖ ≤ cstab) :
    ¬ Collinear3 (0:V3) v w := by
  obtain ⟨hv2, hvu⟩ := w5sg2_norm_bounds hv
  obtain ⟨hw2, hwu⟩ := w5sg2_norm_bounds hw
  have hvne : v ≠ 0 := by
    intro hzz; rw [hzz] at hv2; norm_num at hv2
  have h0126 : h0 = 1.26 := rfl
  have hcs : (cstab:ℝ) = 3.01 := rfl
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul hvne).mp hcol
  have hwv : w = c • v := by simpa using hc
  have e2 : ‖w‖ = |c| * ‖v‖ := by rw [hwv, norm_smul, Real.norm_eq_abs]
  by_cases hc0 : 0 ≤ c
  · have e3 : ‖w‖ = c * ‖v‖ := by rw [e2, abs_of_nonneg hc0]
    have e1 : ‖v - w‖ = |(1 - c) * ‖v‖| := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖v‖)]
    have habs : (1 - c) * ‖v‖ = ‖v‖ - c * ‖v‖ := by ring
    have e4 : ‖v - w‖ = |‖v‖ - ‖w‖| := by
      rw [e1, habs, e3]
    have hb : |‖v‖ - ‖w‖| ≤ 2 * h0 - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h02 : h0 < 2 := by norm_num [h0126]
    rw [e4] at h2
    linarith
  · have e1 : ‖v - w‖ = ‖v‖ + ‖w‖ := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 - c)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : c < 0)]
      ring
    rw [e1, hcs] at hup
    linarith

/-- HOL `IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3` (QKNVMLB.hl:3447). -/
private theorem w5sg2_not_collinear (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
    (hk : 3 < s.k) (hscs : isScsV39 s) (hBB : BBsV39 s vv) :
    ¬ Collinear ℝ {(0:V3), vv (i % s.k), vv ((i + 1) % s.k)} := by
  have hk0 : 0 < s.k := by omega
  have hP : i % s.k < s.k := Nat.mod_lt _ hk0
  have hQ : (i + 1) % s.k < s.k := Nat.mod_lt _ hk0
  have hne : i % s.k ≠ (i + 1) % s.k := w5sg2_suc_mod_not_eq (by omega) i
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpb, -, -, -, -, hd2, -, hbc, -, -, -⟩ := hscs
  have hp1 : Periodic (fun z => s.b (i % s.k) z) s.k := fun t => (hpb (i % s.k) t).2
  have h2' : (i % s.k + 1) % s.k = (i + 1) % s.k := Nat.mod_add_mod i s.k 1
  have hbb : s.b (i % s.k) ((i + 1) % s.k) ≤ cstab := by
    have h1 := w5sg2_periodic_mod hp1 (i % s.k + 1)
    conv_lhs => rw [← h2']
    rw [h1]
    exact hbc (i % s.k) hk
  have hv1 : vv (i % s.k) ∈ ballAnnulus := hBB.1 ⟨i % s.k, rfl⟩
  have hv2 : vv ((i + 1) % s.k) ∈ ballAnnulus := hBB.1 ⟨(i + 1) % s.k, rfl⟩
  have h2le : (2:ℝ) ≤ s.a (i % s.k) ((i + 1) % s.k) := hd2 _ _ ⟨hP, hQ, hne⟩
  have hge2 : (2 : ℝ) ≤ ‖vv (i % s.k) - vv ((i + 1) % s.k)‖ := by
    have h3 := (hBB.2.2.1 (i % s.k) ((i + 1) % s.k)).1
    rw [dist_eq_norm] at h3
    linarith
  have hup : ‖vv (i % s.k) - vv ((i + 1) % s.k)‖ ≤ cstab := by
    have h3 := (hBB.2.2.1 (i % s.k) ((i + 1) % s.k)).2
    rw [dist_eq_norm] at h3
    linarith
  exact w5sg2_nonparallel_annulus hv1 hv2 hge2 hup

/-! ## The delta_x4 six-case box arithmetic -/

/-- τ-symmetry: simultaneous swap `(x2,x3)` and `(x5,x6)`. -/
private theorem w5sg2_delta4_sym2 (a b c d e f : ℝ) :
    deltaX4 a b c d e f = deltaX4 a c b d f e := by
  simp only [deltaX4]; ring

/-- σ-symmetry: swap the pairs `(x2,x3) ↔ (x5,x6)`. -/
private theorem w5sg2_delta4_sym3 (a b c d e f : ℝ) :
    deltaX4 a b c d e f = deltaX4 a e f d b c := by
  simp only [deltaX4]; ring

/-- Shape 1: slots `x2 = x5 = 4`. -/
private theorem w5sg2_delta4_s1 (x1 x3 x4 x6 : ℝ) (h1 : 4 ≤ x1) (h4 : 9.0601 ≤ x4)
    (hn3 : 0 ≤ x3) (h3 : x3 ≤ 6.3504) (h6 : x6 ≤ 6.3504) :
    deltaX4 x1 4 x3 x4 4 x6 < 0 := by
  have hp : x3 * x6 ≤ 6.3504 * 6.3504 := by nlinarith [h3, h6, hn3]
  have he : deltaX4 x1 4 x3 x4 4 x6
      = (32 - 8 * x4 + x3 * x6) + (x1 - 4) * (4 - x1 - 2 * x4 + x3 + x6) := by
    simp only [deltaX4]; ring
  have hpn : (0:ℝ) ≤ (x1 - 4) * (x1 + 2 * x4 - x3 - x6 - 4) :=
    mul_nonneg (by linarith) (by linarith)
  have hprod : (x1 - 4) * (4 - x1 - 2 * x4 + x3 + x6) ≤ 0 := by nlinarith [hpn]
  rw [he]
  linarith

/-- Shape 3: slots `x2 = x3 = 4`. -/
private theorem w5sg2_delta4_s3 (x1 x4 x5 x6 : ℝ) (h1 : 4 ≤ x1) (h4 : 9.0601 ≤ x4)
    (h5 : x5 ≤ 6.3504) (h6 : x6 ≤ 6.3504) :
    deltaX4 x1 4 4 x4 x5 x6 < 0 := by
  have he : deltaX4 x1 4 4 x4 x5 x6
      = (61.27881984 - 8 * x4)
        - (x1 - 4) * (x1 + 2 * x4 - 16.7008)
        - (6.3504 - x5) * (x1 + 4 - x6)
        - (6.3504 - x6) * (x1 + 4 - 6.3504) := by
    simp only [deltaX4]; ring
  have hn1 : (0:ℝ) ≤ (x1 - 4) * (x1 + 2 * x4 - 16.7008) :=
    mul_nonneg (by linarith) (by linarith)
  have hn2 : (0:ℝ) ≤ (6.3504 - x5) * (x1 + 4 - x6) :=
    mul_nonneg (by linarith) (by linarith)
  have hn3 : (0:ℝ) ≤ (6.3504 - x6) * (x1 + 4 - 6.3504) :=
    mul_nonneg (by linarith) (by linarith)
  rw [he]
  linarith

/-- Shape 5: slots `x2 = x6 = 4`. -/
private theorem w5sg2_delta4_s5 (x1 x3 x4 x5 : ℝ) (h1 : 4 ≤ x1) (h4 : 9.0601 ≤ x4)
    (h3 : x3 ≤ 6.3504) (h5 : x5 ≤ 6.3504) :
    deltaX4 x1 4 x3 x4 x5 4 < 0 := by
  have he : deltaX4 x1 4 x3 x4 x5 4 = x1 * (-x1 + 8 - 2 * x4 + x3 + x5) := by
    simp only [deltaX4]; ring
  have hpn : (0:ℝ) ≤ x1 * (x1 + 2 * x4 - x3 - x5 - 8) :=
    mul_nonneg (by linarith) (by linarith)
  have hpr : (0:ℝ) ≤ (x1 - 4) * (-1.4194 - (-x1 + 8 - 2 * x4 + x3 + x5)) :=
    mul_nonneg (by linarith) (by linarith)
  rw [he]
  nlinarith [hpn, hpr]

/-- The six-way case analysis behind `SYNQIWN_p22` (HOL
`Terminal.get_main_nonlinear "1117202051"/"4559601669"/"4559601669b"`,
discharged by direct box arithmetic; `delta_x4` is affine of slope `-2*x1`
in `x4`, so the true diagonal slot only helps). -/
private theorem w5sg2_delta4_cases (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 4 ≤ x1) (h4 : 9.0601 ≤ x4)
    (hn2 : 0 ≤ x2) (hn3 : 0 ≤ x3)
    (hb2 : x2 ≤ 6.3504) (hb3 : x3 ≤ 6.3504) (hb5 : x5 ≤ 6.3504) (hb6 : x6 ≤ 6.3504)
    (hdisj : (x2 = 4 ∧ x5 = 4) ∨ (x3 = 4 ∧ x6 = 4) ∨ (x2 = 4 ∧ x3 = 4) ∨
      (x5 = 4 ∧ x6 = 4) ∨ (x2 = 4 ∧ x6 = 4) ∨ (x3 = 4 ∧ x5 = 4)) :
    deltaX4 x1 x2 x3 x4 x5 x6 < 0 := by
  rcases hdisj with h | h | h | h | h | h
  · obtain ⟨e2, e5⟩ := h
    subst e2; subst e5
    exact w5sg2_delta4_s1 x1 x3 x4 x6 h1 h4 hn3 hb3 hb6
  · obtain ⟨e3, e6⟩ := h
    subst e3; subst e6
    rw [w5sg2_delta4_sym2]
    exact w5sg2_delta4_s1 x1 x2 x4 x5 h1 h4 hn2 hb2 hb5
  · obtain ⟨e2, e3⟩ := h
    subst e2; subst e3
    exact w5sg2_delta4_s3 x1 x4 x5 x6 h1 h4 hb5 hb6
  · obtain ⟨e5, e6⟩ := h
    subst e5; subst e6
    rw [w5sg2_delta4_sym3]
    exact w5sg2_delta4_s3 x1 x4 x2 x3 h1 h4 hb2 hb3
  · obtain ⟨e2, e6⟩ := h
    subst e2; subst e6
    exact w5sg2_delta4_s5 x1 x3 x4 x5 h1 h4 hb3 hb5
  · obtain ⟨e3, e5⟩ := h
    subst e3; subst e5
    rw [w5sg2_delta4_sym3]
    exact w5sg2_delta4_s5 x1 x6 x4 x2 h1 h4 hb6 hb2

private theorem w5sg2_ofLp_sub (a b : V3) : (a - b).ofLp = a.ofLp - b.ofLp := rfl

private theorem w5sg2_dot_self (a : V3) :
    a.ofLp ⬝ᵥ a.ofLp = ‖a‖ * ‖a‖ := by
  have hd : a.ofLp ⬝ᵥ a.ofLp = ∑ i : Fin 3, a.ofLp i * a.ofLp i := rfl
  have hnp : 0 ≤ ∑ i : Fin 3, ‖a.ofLp i‖ ^ 2 := by positivity
  rw [hd, ← pow_two ‖a‖, EuclideanSpace.norm_eq, Real.sq_sqrt hnp]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.norm_eq_abs, sq_abs]; ring

private theorem w5sg2_cos_law (u v : V3) :
    u.ofLp ⬝ᵥ v.ofLp = (‖u‖ * ‖u‖ + ‖v‖ * ‖v‖ - ‖u - v‖ * ‖u - v‖) / 2 := by
  have h1 : (u - v).ofLp ⬝ᵥ (u - v).ofLp = ‖u - v‖ * ‖u - v‖ := w5sg2_dot_self _
  rw [w5sg2_ofLp_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h1
  rw [dotProduct_comm v.ofLp u.ofLp] at h1
  linarith [h1, w5sg2_dot_self u, w5sg2_dot_self v]

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

  have _h := h
  have hk0 : 0 < s.k := by have h32 := h1.2.1; omega
  have hk' : 3 < s.k := by rw [hkk]; exact h3
  have hper : Periodic v s.k := h2.2.1
  have hvper := w5sg2_periodic_mod hper
  have hnb : ∀ j : ℕ, 2 ≤ ‖v j‖ ∧ ‖v j‖ ≤ 2 * h0 := fun j =>
    w5sg2_norm_bounds (h2.1 ⟨j, rfl⟩)
  have hA0 : (v i) ≠ 0 := by
    have hge := (hnb i).1
    intro hzz; rw [hzz] at hge; norm_num at hge
  have hnc1 : ¬ Collinear3 (0:V3) (v i) (v (i + 1)) := by
    have hc0 := w5sg2_not_collinear s v i hk' h1 h2
    rw [hvper i, hvper (i + 1)] at hc0
    exact hc0
  have hnc2 : ¬ Collinear3 (0:V3) (v i) (v (i + k - 1)) := by
    have hc0 := w5sg2_not_collinear s v (i + k - 1) hk' h1 h2
    rw [hvper (i + k - 1), hvper (i + k - 1 + 1)] at hc0
    rw [show i + k - 1 + 1 = i + k from by omega] at hc0
    have hvi : v (i + s.k) = v i := hper i
    rw [hkk] at hvi
    rw [hvi] at hc0
    have hset : ({(0:V3), v (i + k - 1), v i} : Set V3) = {0, v i, v (i + k - 1)} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset] at hc0
    exact hc0
  obtain ⟨hn0, hn2pi, hspec⟩ := azim_master 0 (v i) (v (i + 1)) (v (i + k - 1))
  obtain ⟨e1, e2, e3, hon, hax⟩ := exists_on3_eq_smul (v i) hA0
  have haxis : ((v i - 0 : V3)) = dist (v i) 0 • e3 := by
    rw [sub_zero, dist_zero_right]
    exact hax
  obtain ⟨hh1, hh2, H⟩ := hspec
  obtain ⟨psi, r1, r2, hco1, hco2, hr1, hr2⟩ := H e1 e2 e3 hon haxis hA0
  have hr1' : 0 < r1 := hr1 hnc1
  have hr2' : 0 < r2 := hr2 hnc2
  simp only [sub_zero] at hco1 hco2
  obtain ⟨he11, he22, he33, he12, he13, he23, -⟩ := hon
  have hAv : ∀ (t : ℝ) (X : V3), ((t • e3 : V3) ⬝ᵥ X) = t * (X ⬝ᵥ e3) := by
    intro t X
    rw [← inner_eq_dot (t • e3) X, ← inner_eq_dot X e3, real_inner_smul_left,
      real_inner_comm]
  have hAA : ((v i : V3) ⬝ᵥ (v i : V3)) = ‖v i‖ * ‖v i‖ := by
    rw [← norm_sq_eq_dot (v i : V3), pow_two]
  have hA3 : ((v i : V3) ⬝ᵥ e3) = ‖v i‖ := by
    have h1 := hAv ‖v i‖ e3
    rw [← hax] at h1
    rw [h1, he33, mul_one]
  have hA1 : ((v i : V3) ⬝ᵥ e1) = 0 := by
    have h1 := hAv ‖v i‖ e1
    rw [← hax] at h1
    rw [h1, he13, mul_zero]
  have hA2e : ((v i : V3) ⬝ᵥ e2) = 0 := by
    have h1 := hAv ‖v i‖ e2
    rw [← hax] at h1
    rw [h1, he23, mul_zero]
  have hA1c : ((e1 : V3) ⬝ᵥ (v i : V3)) = 0 := by
    rw [dotProduct_comm]; exact hA1
  have hA2c : ((e2 : V3) ⬝ᵥ (v i : V3)) = 0 := by
    rw [dotProduct_comm]; exact hA2e
  have he12c : ((e2 : V3) ⬝ᵥ (e1 : V3)) = 0 := by
    rw [dotProduct_comm]; exact he12
  have hB3 : ((v (i + 1) : V3) ⬝ᵥ e3) = hh1 * ‖v i‖ := by
    conv_lhs => rw [hco1]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, smul_dotProduct,
      smul_eq_mul, he13, he23, hA3, mul_zero, zero_add, add_zero]
  have hC3 : ((v (i + k - 1) : V3) ⬝ᵥ e3) = hh2 * ‖v i‖ := by
    conv_lhs => rw [hco2]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, smul_dotProduct,
      smul_eq_mul, he13, he23, hA3, mul_zero, zero_add, add_zero]
  have hAB : ((v i : V3) ⬝ᵥ (v (i + 1))) = hh1 * (‖v i‖ * ‖v i‖) := by
    have h1 := hAv ‖v i‖ (v (i + 1))
    rw [← hax] at h1
    rw [h1, hB3]; ring
  have hAC : ((v i : V3) ⬝ᵥ (v (i + k - 1))) = hh2 * (‖v i‖ * ‖v i‖) := by
    have h1 := hAv ‖v i‖ (v (i + k - 1))
    rw [← hax] at h1
    rw [h1, hC3]; ring
  have htrig : Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1)))
      = Real.cos psi * Real.cos (psi + azim 0 (v i) (v (i + 1)) (v (i + k - 1)))
        + Real.sin psi * Real.sin (psi + azim 0 (v i) (v (i + 1)) (v (i + k - 1))) := by
    have hcs := Real.cos_sub psi
      (psi + azim 0 (v i) (v (i + 1)) (v (i + k - 1)))
    rw [show psi - (psi + azim 0 (v i) (v (i + 1)) (v (i + k - 1))) =
      -(azim 0 (v i) (v (i + 1)) (v (i + k - 1)) : ℝ) from by ring, Real.cos_neg] at hcs
    exact hcs
  have hBC : ((v (i + 1) : V3) ⬝ᵥ (v (i + k - 1)))
      = r1 * r2 * Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1)))
        + hh1 * hh2 * (‖v i‖ * ‖v i‖) := by
    conv_lhs => rw [hco1, hco2]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, he11, he22, he12, hA1, hA2e, hAA,
      hA1c, hA2c, he12c, mul_zero, mul_one, zero_add, add_zero]
    rw [htrig]
    ring
  have hP : ((v (i + 1) : V3) ⬝ᵥ (v (i + k - 1)))
      - ((v (i + 1) : V3) ⬝ᵥ e3) * ((v (i + k - 1) : V3) ⬝ᵥ e3)
      = r1 * r2 * Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1))) := by
    rw [hBC, hB3, hC3]; ring
  -- distance bridges
  have hdBC : ((v (i + 1) : V3) ⬝ᵥ (v (i + k - 1))) * 2
      = ‖v (i + 1)‖ * ‖v (i + 1)‖ + ‖v (i + k - 1)‖ * ‖v (i + k - 1)‖
        - dist (v (i + 1)) (v (i + k - 1)) * dist (v (i + 1)) (v (i + k - 1)) := by
    have h1 : ((v (i + 1) : V3) - v (i + k - 1)).ofLp
        ⬝ᵥ ((v (i + 1) : V3) - v (i + k - 1)).ofLp
        = ‖v (i + 1) - v (i + k - 1)‖ * ‖v (i + 1) - v (i + k - 1)‖ := w5sg2_dot_self _
    have h3 : ‖v (i + 1) - v (i + k - 1)‖ = dist (v (i + 1)) (v (i + k - 1)) :=
      (dist_eq_norm _ _).symm
    rw [← h3, ← h1, w5sg2_ofLp_sub, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, dotProduct_comm ((v (i + k - 1) : V3).ofLp) ((v (i + 1) : V3).ofLp),
      ← w5sg2_dot_self (v (i + 1)), ← w5sg2_dot_self (v (i + k - 1))]
    ring
  have hdAB : ((v i : V3) ⬝ᵥ (v (i + 1))) * 2
      = ‖v i‖ * ‖v i‖ + ‖v (i + 1)‖ * ‖v (i + 1)‖
        - dist (v i) (v (i + 1)) * dist (v i) (v (i + 1)) := by
    have h1 : ((v i : V3) - v (i + 1)).ofLp ⬝ᵥ ((v i : V3) - v (i + 1)).ofLp
        = ‖v i - v (i + 1)‖ * ‖v i - v (i + 1)‖ := w5sg2_dot_self _
    have h3 : ‖v i - v (i + 1)‖ = dist (v i) (v (i + 1)) := (dist_eq_norm _ _).symm
    rw [← h3, ← h1, w5sg2_ofLp_sub, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, dotProduct_comm ((v (i + 1) : V3).ofLp) ((v i : V3).ofLp),
      ← w5sg2_dot_self (v i), ← w5sg2_dot_self (v (i + 1))]
    ring
  have hdAC : ((v i : V3) ⬝ᵥ (v (i + k - 1))) * 2
      = ‖v i‖ * ‖v i‖ + ‖v (i + k - 1)‖ * ‖v (i + k - 1)‖
        - dist (v i) (v (i + k - 1)) * dist (v i) (v (i + k - 1)) := by
    have h1 : ((v i : V3) - v (i + k - 1)).ofLp ⬝ᵥ ((v i : V3) - v (i + k - 1)).ofLp
        = ‖v i - v (i + k - 1)‖ * ‖v i - v (i + k - 1)‖ := w5sg2_dot_self _
    have h3 : ‖v i - v (i + k - 1)‖ = dist (v i) (v (i + k - 1)) := (dist_eq_norm _ _).symm
    rw [← h3, ← h1, w5sg2_ofLp_sub, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, dotProduct_comm ((v (i + k - 1) : V3).ofLp) ((v i : V3).ofLp),
      ← w5sg2_dot_self (v i), ← w5sg2_dot_self (v (i + k - 1))]
    ring
  have hkey : deltaX4 (‖v i‖ ^ 2) (‖v (i + 1)‖ ^ 2) (‖v (i + k - 1)‖ ^ 2)
      (dist (v (i + 1)) (v (i + k - 1)) ^ 2) (dist (v i) (v (i + k - 1)) ^ 2)
      (dist (v i) (v (i + 1)) ^ 2)
      = (4 * ‖v i‖ ^ 2) * (((v (i + 1) : V3) ⬝ᵥ (v (i + k - 1)))
        - ((v (i + 1) : V3) ⬝ᵥ e3) * ((v (i + k - 1) : V3) ⬝ᵥ e3)) := by
    have hkey1 : deltaX4 (‖v i‖ ^ 2) (‖v (i + 1)‖ ^ 2) (‖v (i + k - 1)‖ ^ 2)
      (dist (v (i + 1)) (v (i + k - 1)) ^ 2) (dist (v i) (v (i + k - 1)) ^ 2)
      (dist (v i) (v (i + 1)) ^ 2)
      = (2 * ‖v i‖ ^ 2) * (‖v (i + 1)‖ * ‖v (i + 1)‖ + ‖v (i + k - 1)‖ * ‖v (i + k - 1)‖
          - dist (v (i + 1)) (v (i + k - 1)) * dist (v (i + 1)) (v (i + k - 1)))
        - (‖v i‖ * ‖v i‖ + ‖v (i + 1)‖ * ‖v (i + 1)‖
            - dist (v i) (v (i + 1)) * dist (v i) (v (i + 1)))
          * (‖v i‖ * ‖v i‖ + ‖v (i + k - 1)‖ * ‖v (i + k - 1)‖
            - dist (v i) (v (i + k - 1)) * dist (v i) (v (i + k - 1))) := by
      unfold deltaX4; ring
    rw [hkey1, ← hdBC, ← hdAB, ← hdAC, hAB, hAC, hB3, hC3]
    field_simp
    ring
  -- numeric bounds
  have h2h0 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  have hcst : (cstab:ℝ) = 3.01 := rfl
  have hx1 : (4:ℝ) ≤ ‖v i‖ ^ 2 := by nlinarith [(hnb i).1]
  have hx4 : (9.0601:ℝ) ≤ dist (v (i + 1)) (v (i + k - 1)) ^ 2 := by
    have hd1 : (3.01:ℝ) ≤ dist (v (i + 1)) (v (i + k - 1)) := by rw [← hcst]; exact hc
    have hdn : (0:ℝ) ≤ dist (v (i + 1)) (v (i + k - 1)) := dist_nonneg
    nlinarith [hd1, hdn]
  have hsqb : ∀ j : ℕ, ‖v j‖ ^ 2 ≤ 6.3504 := by
    intro j
    have hb := (hnb j).2
    rw [h2h0] at hb
    have hnn : (0:ℝ) ≤ ‖v j‖ := norm_nonneg _
    nlinarith [hb, hnn]
  have hd6 : dist (v i) (v (i + 1)) ^ 2 ≤ 6.3504 := by
    have hb := he1
    rw [h2h0] at hb
    have hnn : (0:ℝ) ≤ dist (v i) (v (i + 1)) := dist_nonneg
    nlinarith [hb, hnn]
  have hd5 : dist (v i) (v (i + k - 1)) ^ 2 ≤ 6.3504 := by
    have hb := he2
    rw [h2h0] at hb
    have hnn : (0:ℝ) ≤ dist (v i) (v (i + k - 1)) := dist_nonneg
    nlinarith [hb, hnn]
  have hdelta_neg : deltaX4 (‖v i‖ ^ 2) (‖v (i + 1)‖ ^ 2)
      (‖v (i + k - 1)‖ ^ 2) (dist (v (i + 1)) (v (i + k - 1)) ^ 2)
      (dist (v i) (v (i + k - 1)) ^ 2) (dist (v i) (v (i + 1)) ^ 2) < 0 := by
    apply w5sg2_delta4_cases (h1 := hx1) (h4 := hx4)
    · exact sq_nonneg _
    · exact sq_nonneg _
    · exact hsqb (i + 1)
    · exact hsqb (i + k - 1)
    · exact hd5
    · exact hd6
    · rcases hears with h | h | h | h | h | h
      · exact Or.inl (And.intro (by rw [h.1]; norm_num) (by rw [h.2]; norm_num))
      · exact Or.inr (Or.inl (And.intro (by rw [h.1]; norm_num) (by rw [h.2]; norm_num)))
      · exact Or.inr (Or.inr (Or.inl (And.intro (by rw [h.1]; norm_num)
          (by rw [h.2]; norm_num))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (And.intro (by rw [h.2]; norm_num)
          (by rw [h.1]; norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (And.intro (by rw [h.1]; norm_num)
          (by rw [h.2]; norm_num))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (And.intro (by rw [h.1]; norm_num)
          (by rw [h.2]; norm_num))))))
  have hA2pos : (0:ℝ) < ‖v i‖ ^ 2 := by nlinarith [(hnb i).1]
  have hPpos : (0:ℝ) < 4 * ‖v i‖ ^ 2 := by nlinarith [hA2pos]
  have hPlt : ((v (i + 1) : V3) ⬝ᵥ (v (i + k - 1)))
      - ((v (i + 1) : V3) ⬝ᵥ e3) * ((v (i + k - 1) : V3) ⬝ᵥ e3) < 0 := by
    have h0 : (4 * ‖v i‖ ^ 2) * (((v (i + 1) : V3) ⬝ᵥ (v (i + k - 1)))
        - ((v (i + 1) : V3) ⬝ᵥ e3) * ((v (i + k - 1) : V3) ⬝ᵥ e3)) < 0 := by
      rw [← hkey]; exact hdelta_neg
    nlinarith [h0, hPpos]
  have hcos : Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1))) < 0 := by
    have h0 : r1 * r2 * Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1))) < 0 := by
      rw [← hP]; exact hPlt
    have hrr : (0:ℝ) < r1 * r2 := mul_pos hr1' hr2'
    nlinarith [h0, hrr]
  by_cases hcmp : (3:ℝ) * Real.pi / 2 ≤ azim 0 (v i) (v (i + 1)) (v (i + k - 1))
  · exfalso
    have hhigh := hcmp
    have hper' := Real.cos_periodic
      (azim 0 (v i) (v (i + 1)) (v (i + k - 1)) - 2 * Real.pi)
    rw [show (azim 0 (v i) (v (i + 1)) (v (i + k - 1)) - 2 * Real.pi) + 2 * Real.pi =
      azim 0 (v i) (v (i + 1)) (v (i + k - 1)) from by ring] at hper'
    rw [hper'] at hcos
    have hcn : (0:ℝ) ≤ Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1)) - 2 * Real.pi) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    linarith
  · by_contra hcon
    have hcon2 : (azim 0 (v i) (v (i + 1)) (v (i + k - 1))) ≤ Real.pi / 2 :=
      not_lt.mp hcon
    have hcn : (0:ℝ) ≤ Real.cos (azim 0 (v i) (v (i + 1)) (v (i + k - 1))) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    linarith

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
  classical
  -- HOL OCBICBY.hl:2675-2696 — `V`, `E`, `FF` and the local-fan facts.
  set V : Set V3 := Set.range vv with hV
  set E : Set (Set V3) := Set.range (fun i => {vv i, vv (i + 1)}) with hE
  set FF : Set (V3 × V3) := Set.range (fun i => (vv i, vv (i + 1))) with hFF
  -- HOL :2678 `convex_local_fan(V,E,f)` from `BBs_v39` + `3 < k`
  -- (`BBs_v39` carries the `k <= 3 \/ convex_local_fan` disjunct).
  have hk3 : ¬ s.k ≤ 3 := by omega
  have hclf : ConvexLocalFan V E FF := by
    rcases hB.2.2.2 with h3 | hcf
    · exact absurd h3 hk3
    · simpa only [hV, hE, hFF] using hcf
  have hlf : LocalFan V E FF := hclf.1
  -- `AzimBridge` vocabulary bridges: LA1 `LocalFan` ↦ LA3 `localFan_p3` ↦
  -- LA2 `localFan_p2` (the `_p2` kit supplies `DETER_RHO_NODE`/`PRE_IVS`).
  have hlf3 : localFan_p3 V E FF := localFanEquiv_p35.mp hlf
  have hlf2 : localFan_p2 V E FF := localFan_p2.of_localFan_p3 hlf3
  -- HOL :2681 `JKQEWGV2`: the realisation graph is not circular.
  have hcirc : ¬ Circular V E := by
    have hq := JKQEWGV2_p23 s vv h1 hk hB ht
    simpa only [hV, hE, Set.image_univ] using hq
  -- HOL :2682-2683 `CIZMRRH` (via `CVX_LO_IMP_LO`): generic or circular or
  -- lunar, exclusively.
  have htri := CIZMRRH hlf3
  -- HOL :2680 the no-lunar subgoal: `JKQEWGV3` gives `< pi/2` at a lunar
  -- vertex, `INTERIOR_ANGLE1_AZIM` + `SYNQIWN` give `> pi/2` at the same
  -- angle (`hl` supplies the four lunar-local facts).
  have hnoLunar : ¬ ∃ v w : V3, Lunar v w V E := by
    rintro ⟨v, w, hlun⟩
    have hvV : v ∈ V := hlun.2.1 (by simp)
    obtain ⟨i, hi⟩ := hvV
    subst hi
    have hlun' : Lunar (vv i) w (Set.range vv)
        (Set.range fun i => {vv i, vv (i + 1)}) := by
      simpa only [hV, hE] using hlun
    -- HOL `INTERIOR_ANGLE1_AZIM`: `interiorAngle1 0 FF (vv i)` is the fan azim
    -- `azim 0 (vv i) (vv (i+1)) (vv (i+k-1))` (the rho-node is the successor,
    -- the inverse-rho-node is the predecessor).
    have hrn : rhoNode1 FF (vv i) = vv (i + 1) := by
      have hrp : rhoNode1_p2 FF (vv i) = vv (i + 1) :=
        DETER_RHO_NODE hlf2 (v := vv i) (w := vv (i + 1))
          (show (vv i, vv (i + 1)) ∈ FF from Set.mem_range.mpr ⟨i, rfl⟩)
      simpa only [rhoNode1, rhoNode1_p2] using hrp
    have hivs : ivsRhoNode1 FF (vv i) = vv (i + (s.k - 1)) := by
      have hmem : (vv (i + (s.k - 1)), vv i) ∈ FF := by
        refine Set.mem_range.mpr ⟨i + (s.k - 1), ?_⟩
        have hper : vv (i + (s.k - 1) + 1) = vv i := by
          rw [show i + (s.k - 1) + 1 = i + s.k by omega]
          exact hB.2.1 i
        rw [hper]
      have hip : ivsRhoNode1_p2 FF (vv i) = vv (i + (s.k - 1)) :=
        PRE_IVS_RHO_NODE1_DETE hlf2 hmem
      simpa only [ivsRhoNode1, ivsRhoNode1_p2] using hip
    have hid : interiorAngle1 0 FF (vv i)
        = azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) := by
      simp only [interiorAngle1, hrn, hivs]
    -- HOL :2686 `JKQEWGV3`: the interior angle at a lunar vertex is `< pi/2`.
    have hlt : interiorAngle1 0 FF (vv i) < Real.pi / 2 := by
      have hq := JKQEWGV3_p23 s vv (vv i) w h1 hB hk ht (by
        simpa only [Set.image_univ] using hlun')
      simpa only [hFF, Set.image_univ] using hq
    -- HOL :2699-2715 `SYNQIWN`: the same azim is `> pi/2`; contradiction.
    have hgt : Real.pi / 2 < azim 0 (vv i) (vv (i + 1)) (vv (i + (s.k - 1))) := by
      have hk1 : i + s.k - 1 = i + (s.k - 1) := by omega
      have hmain : Real.pi / 2 < azim 0 (vv i) (vv (i + 1)) (vv (i + s.k - 1)) := by
        refine SYNQIWN_p22 h s vv i s.k h1 hB rfl hk ?_ ?_ ?_ ?_
        · obtain ⟨-, -, he3, he4⟩ := hl i w hlun'
          rcases he3 with he3 | he3 <;> rcases he4 with he4 | he4
          · exact Or.inr (Or.inr (Or.inl (by simpa only [hk1] using ⟨he3, he4⟩)))
          · exact Or.inl (by simpa only [hk1] using ⟨he3, he4⟩)
          · exact Or.inr (Or.inl (by simpa only [hk1] using ⟨he4, he3⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hk1] using ⟨he3, he4⟩))))
        · exact (hl i w hlun').1
        · simpa only [hk1] using (hl i w hlun').2.1
        · simpa only [hk1] using hd (i + 1) (i + (s.k - 1)) (scs_diag_2_p22 hk)
      simpa only [hk1] using hmain
    rw [hid] at hlt
    linarith
  -- HOL :2723 final kill (`MESON_TAC`): the trichotomy's first branch, with
  -- `circular` killed by `JKQEWGV2` and `lunar` by the subgoal above.
  rcases htri with ⟨hgen, -⟩ | ⟨hcir, -⟩ | ⟨⟨v, w, hlun3⟩, -⟩
  · simpa only [scsGeneric, generic_p3, Generic, hV, hE] using hgen
  · exact absurd (by simpa only [circular_p3, Circular] using hcir) hcirc
  · exact absurd ⟨v, w, by
      simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hlun3⟩ hnoLunar

/-- HOL `EAR_SOL_NN`. -/
theorem EAR_SOL_NN_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0) (hy4 : cstab ≤ y4 ∧ y4 ≤ 3.915)
    (hy5 : y5 = 2) (hy6 : y6 = 2) (hd : 0 ≤ deltaY y1 y2 y3 y4 y5 y6) :
    0 ≤ solY y1 y2 y3 y4 y5 y6 := by
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

/-- HOL `periodic_sum_shift`. NEEDS: `sum_nbij` 旋转双弹幕——注意本 Mathlib
`Finset.sum_nbij` 的 h₀ 方向是 `f a = f' (g a)`(a ∈ LHS 集, g : LHS→RHS),
故 g 须取逆向旋转 `fun x => (x + n - j % n) % n`(则 h₀ 化为 `j + g a ≡ a
[MOD n]`, 经 hmod 链闭合);hb 证入 a := `(b + j % n) % n`;单射证走
`Nat.ModEq.add_right (j % n)` 后 omega(须先有 `j % n < n` 在场)。
μ-bug 备忘: omega 对变元模数 `% n` 无 `< n` 先验, 须显式 `Nat.mod_lt`。 -/
theorem periodic_sum_shift_p22 (f : ℕ → ℝ) (j n : ℕ) (hper : Periodic f n) (hn : n ≠ 0) :
    Finset.sum (Finset.range n) f = Finset.sum (Finset.range n) (fun i => f (j + i)) := by
  sorry

/-- HOL `LEMMA_7175074394` (numeric; `c110186` records
`atn (sqrt 0.110186) < 0.3205` in HOL). -/
theorem LEMMA_7175074394_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hbox : ineqP22 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (2, y4, 2),
      (3.01, y5, 3.237), (2, y6, 2)] True)
    (hd : deltaY y1 y2 y3 y4 y5 y6 ≤ 20 ∧ 0 ≤ deltaY y1 y2 y3 y4 y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 < 0.3205 := by
  sorry

/-- HOL `angle_sum_5T1`. -/
theorem angle_sum_5T1_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hbox : ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0),
      (2, y126, 2 * h0), (2, y135, 2 * h0), (2, y4, 2), (cstab, y5, 3.237),
      (cstab, y6, 3.237)] True)
    (hsub : dihY y1 y126 y135 cstab 2 2 ≤
        dihY y1 y2 y3 y4 y5 y6 + dihY y1 y2 y126 2 2 y6 +
          dihY y1 y3 y135 2 2 y5)
    (hd1 : 0 ≤ deltaY y1 y2 y126 2 2 y6) (hd2 : 0 ≤ deltaY y1 y3 y135 2 2 y5) :
    20 ≤ deltaY y1 y2 y126 2 2 y6 ∨ 20 ≤ deltaY y1 y3 y135 2 2 y5 := by
  sorry

/-- HOL `terminal_pent_taum2`. -/
theorem terminal_pent_taum2_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hd1 : 0 ≤ deltaY y126 y1 y2 y6 2 2)
    (hd2 : 0 ≤ deltaY y135 y1 y3 y5 2 2)
    (hsub : dihY y1 y126 y135 cstab 2 2 ≤
        dihY y1 y2 y3 y4 y5 y6 + dihY y1 y2 y126 2 2 y6 +
          dihY y1 y3 y135 2 2 y5) :
    ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2),
      (3.01, y5, 3.237), (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6 +
        taum y135 y1 y3 y5 2 2) := by
  sorry

/-! ## `dih_y_mono` kit: `dihY` monotone in its 4th slot

Private helper block added 2026-11-12 (lane `la22aux-w1`) for
`dih_y_mono_p22`.  Analytic proof of HOL
`Tame_inequalities.DIH_X_MONO_LT_4` + `dih_y_mono` (OCBICBY.hl:3406):
resolve the right-half-plane `atn2` branch to `π/2 + arctan(-P/√(4·x1·Δ))`,
compare the ratios via the discriminant invariant `P² + 4·x1·Δ = const`
and the midpoint identity `2(Δ'−Δ) = (P+P')(x4'−x4)`; pure algebra, no
calculus. -/
section La22DihYMonokit

private theorem la22dy_atn2_eq_arctan {A B : ℝ} (hA : 0 < A) :
    atn2 A B = Real.arctan (B / A) := by
  unfold atn2
  split_ifs with hb hb2 hb3
  · rfl
  · have hBA : 0 < B / A := div_pos hb2 hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp
    rw [hrec, Real.arctan_inv_of_pos hBA]
    ring
  · have hBA : B / A < 0 := div_neg_of_neg_of_pos hb3 hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp
    rw [hrec, Real.arctan_inv_of_neg hBA]
    ring
  · have hB : B = 0 := le_antisymm (not_lt.mp hb2) (not_lt.mp hb3)
    have hle : A ≤ |B| := le_of_not_gt hb
    rw [hB, abs_zero] at hle
    linarith

/-- 楔形 kit：`delta_x` 的两点判别式不变量（`P^2 + 4*x1*Δ` 与第 4 槽无关）。 -/
private theorem la22dy_delta_inv (x1 x2 x3 x4 x4' x5 x6 : ℝ) :
    (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
      = (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 := by
  simp only [deltaX, deltaX4]
  ring

/-- 楔形 kit：`delta_x4` 沿第 4 槽的仿射差（斜率 `-2*x1`）。 -/
private theorem la22dy_dX4_sub (x1 x2 x3 x4 x4' x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4' x5 x6
      = deltaX4 x1 x2 x3 x4 x5 x6 - 2 * x1 * (x4' - x4) := by
  simp only [deltaX4]
  ring

/-- 楔形 kit：`delta_x` 的两点中点恒等式。 -/
private theorem la22dy_dX_mid (x1 x2 x3 x4 x4' x5 x6 : ℝ) :
    2 * (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
      = (deltaX4 x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4' x5 x6) * (x4' - x4) := by
  simp only [deltaX, deltaX4]
  ring

/-- 楔形 kit：`-delta_x4 / sqrt(4*x1*delta_x)` 沿第 4 槽的比值比较
（判别式不变量消平方，正分子支 `abs_le_of_sq_le_sq'` 收口）。 -/
private theorem la22dy_ratio_le {x1 x2 x3 x4 x4' x5 x6 : ℝ} (hx1 : 0 < x1)
    (h44 : x4 ≤ x4') (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hd' : 0 < deltaX x1 x2 x3 x4' x5 x6) :
    -(deltaX4 x1 x2 x3 x4 x5 x6) / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
      ≤ -(deltaX4 x1 x2 x3 x4' x5 x6)
          / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have hdec : deltaX4 x1 x2 x3 x4' x5 x6 ≤ deltaX4 x1 x2 x3 x4 x5 x6 := by
    have h2 := la22dy_dX4_sub x1 x2 x3 x4 x4' x5 x6
    have hprod : 0 ≤ 2 * x1 * (x4' - x4) :=
      mul_nonneg (mul_nonneg zero_le_two hx1.le) (sub_nonneg.mpr h44)
    linarith
  have hmid := la22dy_dX_mid x1 x2 x3 x4 x4' x5 x6
  have hs0p : 0 ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 :=
    le_of_lt (mul_pos (mul_pos h4 hx1) hd)
  have hs1p : 0 ≤ 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 :=
    le_of_lt (mul_pos (mul_pos h4 hx1) hd')
  have hs0lt : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos h4 hx1) hd
  have hs1lt : 0 < 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 :=
    mul_pos (mul_pos h4 hx1) hd'
  have hs0 : 0 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) := Real.sqrt_nonneg _
  rcases le_or_gt 0 (deltaX4 x1 x2 x3 x4' x5 x6) with hP1 | hP1
  · -- both P ≥ 0: delta increases along the slot, negative numerators compare
    have hP0 : 0 ≤ deltaX4 x1 x2 x3 x4 x5 x6 := hP1.trans hdec
    have hDle : deltaX x1 x2 x3 x4 x5 x6 ≤ deltaX x1 x2 x3 x4' x5 x6 := by
      nlinarith [hmid, hP0, hP1, h44]
    have hsq : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) :=
      Real.sqrt_le_sqrt (by nlinarith [hDle, hx1.le])
    have hnp0 : -(deltaX4 x1 x2 x3 x4 x5 x6) ≤ -(deltaX4 x1 x2 x3 x4' x5 x6) := by linarith
    have hnp1 : -(deltaX4 x1 x2 x3 x4' x5 x6) ≤ 0 := by linarith
    refine le_trans ((div_le_div_iff₀ (Real.sqrt_pos.mpr hs0lt)
      (Real.sqrt_pos.mpr hs0lt)).mpr
      (mul_le_mul_of_nonneg_right hnp0 (Real.sqrt_nonneg _)))
      ((div_le_div_iff₀ (Real.sqrt_pos.mpr hs0lt) (Real.sqrt_pos.mpr hs1lt)).mpr
        (mul_le_mul_of_nonpos_left hsq hnp1))
  · rcases le_or_gt 0 (deltaX4 x1 x2 x3 x4 x5 x6) with hP0 | hP0
    · -- P1 < 0 ≤ P0: left side nonpositive, right side positive
      have hL : -(deltaX4 x1 x2 x3 x4 x5 x6)
            / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 0 :=
        (div_nonpos_iff).mpr (Or.inr ⟨by linarith, hs0⟩)
      have hR : 0 ≤ -(deltaX4 x1 x2 x3 x4' x5 x6)
            / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) :=
        (div_nonneg_iff).mpr (Or.inl ⟨by linarith, hs1⟩)
      linarith
    · -- both numerators positive: compare squares via the discriminant invariant
      have hnp0 : 0 < -(deltaX4 x1 x2 x3 x4 x5 x6) := by linarith
      have hnp1 : 0 < -(deltaX4 x1 x2 x3 x4' x5 x6) := by linarith
      have hDle : deltaX x1 x2 x3 x4' x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
        nlinarith [hmid, hdec, hP0, h44]
      have hcert : (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
          * ((deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
              + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6) * (4 * x1) ≤ 0 := by
        have hbase : 0 ≤ 4 * x1 := by linarith
        have hdiff : deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6 ≤ 0 := by
          nlinarith [hmid, hdec, hP0, h44]
        have hpos : 0 ≤ (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
            + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 := by nlinarith
        have hp1 : (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
            * ((deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
                + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hdiff hpos
        exact mul_nonpos_of_nonpos_of_nonneg hp1 hbase
      have heq : (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
            * (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)
          = (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
              * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            + (deltaX x1 x2 x3 x4' x5 x6 - deltaX x1 x2 x3 x4 x5 x6)
              * ((deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
                  + 4 * x1 * deltaX x1 x2 x3 x4' x5 x6) * (4 * x1) := by
        linear_combination (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) *
          la22dy_delta_inv x1 x2 x3 x4 x4' x5 x6
      have hsqnum : (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
            * (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)
          ≤ (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
              * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by linarith
      have hsq0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2
          = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := Real.sq_sqrt hs0p
      have hsq1 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) ^ 2
          = 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 := Real.sq_sqrt hs1p
      have hA2 : (-(deltaX4 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ^ 2
          ≤ (-(deltaX4 x1 x2 x3 x4' x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)) ^ 2 := by
        have h1 : (-(deltaX4 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ^ 2
            = (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
                / (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
          rw [div_pow, neg_sq, hsq0]
        have h2 : (-(deltaX4 x1 x2 x3 x4' x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6)) ^ 2
            = (deltaX4 x1 x2 x3 x4' x5 x6) ^ 2
                / (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) := by
          rw [div_pow, neg_sq, hsq1]
        rw [h1, h2]
        exact (div_le_div_iff₀ hs0lt hs1lt).mpr hsqnum
      exact (abs_le_of_sq_le_sq' hA2
        (le_of_lt (div_pos hnp1 (Real.sqrt_pos.mpr hs1lt)))).2

/-- 楔形 kit 主件：`dih_x` 沿第 4 槽单调（起点 `delta_x > 0`，终点 `≥ 0`；
终点退化时右侧值只增不减，`delta_x4 > 0` 支由中点恒等式排除）。 -/
private theorem la22dy_dihXf_mono_x4 {x1 x2 x3 x4 x4' x5 x6 : ℝ} (hx1 : 0 < x1)
    (h44 : x4 ≤ x4') (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (_hd' : 0 ≤ deltaX x1 x2 x3 x4' x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 ≤ dihXf x1 x2 x3 x4' x5 x6 := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have hs0 : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos h4 hx1) hd
  unfold dihXf
  rcases lt_or_ge 0 (deltaX x1 x2 x3 x4' x5 x6) with hD1 | hD1
  · have hs1 : 0 < 4 * x1 * deltaX x1 x2 x3 x4' x5 x6 :=
      mul_pos (mul_pos h4 hx1) hD1
    rw [la22dy_atn2_eq_arctan (A := Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        (B := -(deltaX4 x1 x2 x3 x4 x5 x6)) (Real.sqrt_pos.mpr hs0),
      la22dy_atn2_eq_arctan (A := Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6))
        (B := -(deltaX4 x1 x2 x3 x4' x5 x6)) (Real.sqrt_pos.mpr hs1)]
    linarith [Real.arctan_le_arctan_iff.mpr (la22dy_ratio_le hx1 h44 hd hD1)]
  · -- degenerate right endpoint: sqrt = 0, atn2 value only grows
    have hP1le : deltaX4 x1 x2 x3 x4' x5 x6 ≤ 0 := by
      by_contra hcon
      have hcon' : 0 < deltaX4 x1 x2 x3 x4' x5 x6 := lt_of_not_ge hcon
      have h2 := la22dy_dX4_sub x1 x2 x3 x4 x4' x5 x6
      have hprod : 0 ≤ 2 * x1 * (x4' - x4) :=
        mul_nonneg (mul_nonneg zero_le_two hx1.le) (sub_nonneg.mpr h44)
      have hP0pos : 0 < deltaX4 x1 x2 x3 x4 x5 x6 := by linarith
      have hsum : 0 < deltaX4 x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4' x5 x6 := by
        linarith
      have hprod2 : 0 ≤ (deltaX4 x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4' x5 x6) * (x4' - x4) :=
        mul_nonneg (le_of_lt hsum) (sub_nonneg.mpr h44)
      have hm := la22dy_dX_mid x1 x2 x3 x4 x4' x5 x6
      linarith [hm, hprod2, hd]
    have hz : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4' x5 x6) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by nlinarith [hD1, hx1.le])
    rw [hz, la22dy_atn2_eq_arctan (A := Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        (B := -(deltaX4 x1 x2 x3 x4 x5 x6)) (Real.sqrt_pos.mpr hs0)]
    have hArcL : Real.arctan (-(deltaX4 x1 x2 x3 x4 x5 x6)
        / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ≤ Real.pi / 2 :=
      (Real.arctan_lt_pi_div_two _).le
    unfold atn2
    split_ifs with hb1 hb2 hb3
    · linarith [abs_nonneg (-(deltaX4 x1 x2 x3 x4' x5 x6)), hArcL]
    · simp only [zero_div, Real.arctan_zero]
      linarith [hArcL]
    · linarith
    · linarith [Real.pi_pos, hArcL]

/-- 楔形 kit：`dih_y` 沿第 4 槽单调（y 空间版，即 HOL `dih_y_mono`）。 -/
private theorem la22dy_dihY_mono_y4 {y1 y2 y3 y4 y4' y5 y6 : ℝ} (hy1 : 0 < y1)
    (hy4 : 0 ≤ y4) (h44 : y4 ≤ y4') (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hd' : 0 ≤ deltaY y1 y2 y3 y4' y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 ≤ dihY y1 y2 y3 y4' y5 y6 := by
  show dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≤
    dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4' * y4') (y5 * y5) (y6 * y6)
  refine la22dy_dihXf_mono_x4 (mul_pos hy1 hy1) ?_ hd hd'
  have hstep1 : y4 * y4 ≤ y4' * y4 := mul_le_mul_of_nonneg_right h44 hy4
  have hstep2 : y4' * y4 ≤ y4' * y4' := by
    refine mul_le_mul_of_nonneg_left h44 ?_
    linarith
  linarith

end La22DihYMonokit

/-- HOL `dih_y_mono`. -/
-- PROVED 2026-11-12 (lane `la22aux-w1`): from the `La22DihYMonokit` block
-- above (HOL `Tame_inequalities.DIH_X_MONO_LT_4` at squared lengths);
-- `#print axioms` = standard three.
theorem dih_y_mono_p22 (y1 y2 y3 y4 y5 y6 y4' : ℝ)
    (hle : y4 ≤ y4') (hy1 : 0 < y1) (hy4 : 0 < y4)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hd' : 0 ≤ deltaY y1 y2 y3 y4' y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 ≤ dihY y1 y2 y3 y4' y5 y6 := by
  exact la22dy_dihY_mono_y4 hy1 hy4.le hle hd hd'

/-! ## LA22MONO kit: taum monotonicity in `y4`

Private helper block added 2026-11-12 (lane `la22mono-w1`) to prove
`LEMMA_1834976363_p22` and `LEMMA_4828966562_p22` without consuming the
unproved `SECOND_DERIVATIVE_TEST_TAUM_p22` / `FIRST_DERIVATIVE_TEST_TAUM_p22`
/ `NUM1_GENERIC_p22` / `xrr_simple_*` tape.  Contents: `taum = Σ rho·dihY −
(π+sol0)`, the `xrr` scaling identity for `dihY`, the `dihXf`-sum derivative
`num1/(2 x4 (16−x4) √Δx)` (from `Gamma4Deriv2`), the registry boxes, and the
MVT/monotonicity glue.  HOL sources: `OCBICBY.hl` `taum_compose_xrr`,
`derived_form_sum_dih444`, `xrr_simple_lower/upper_bound`, `xrr_le_16`,
`dih_y_mono`-adjacent kit. -/
section La22TaumMonoKit
open Filter
open scoped Topology

private theorem la22_atn2_smul {c a b : ℝ} (hc : 0 < c) :
    atn2 (c * a) (c * b) = atn2 a b := by
  have hcb : |c * b| = c * |b| := by rw [abs_mul, abs_of_pos hc]
  have hcond : |c * b| < c * a ↔ |b| < a := by
    rw [hcb]
    constructor
    · intro hh; exact lt_of_mul_lt_mul_left hh hc.le
    · intro hh; exact mul_lt_mul_of_pos_left hh hc
  have hcbne : b ≠ 0 → (c * b : ℝ) ≠ 0 := fun hh => mul_ne_zero (ne_of_gt hc) hh
  unfold atn2
  rcases lt_or_ge (abs b) a with h1 | h1
  · rw [if_pos (hcond.mpr h1), if_pos h1,
      show (c * b) / (c * a) = b / a from by field_simp]
  · rw [if_neg (not_lt.mpr (by rw [hcb]; exact mul_le_mul_of_nonneg_left h1 hc.le)),
      if_neg (not_lt.mpr h1)]
    rcases lt_trichotomy b 0 with h2 | h2 | h2
    · have hcbneg : c * b < 0 := by
        have ht := mul_lt_mul_of_pos_left h2 hc
        rwa [mul_zero] at ht
      rw [if_neg (by linarith : ¬ (0:ℝ) < c * b), if_neg (by linarith : ¬ (0:ℝ) < b),
        if_pos hcbneg, if_pos (by linarith : b < 0),
        show (c * a) / (c * b) = a / b from by field_simp [hcbne (ne_of_lt h2)]]
    · subst h2
      norm_num
    · rw [if_pos (mul_pos hc h2), if_pos h2,
        show (c * a) / (c * b) = a / b from by field_simp [hcbne (ne_of_gt h2)]]

private theorem la22_dihY222222 : dihY 2 2 2 2 2 2 = Real.arccos (1 / 3) := by
  have hdx : (deltaX 4 4 4 4 4 4 : ℝ) = 128 := by norm_num [deltaX]
  have hdx4 : (deltaX4 4 4 4 4 4 4 : ℝ) = 16 := by norm_num [deltaX4]
  have hd : dihY 2 2 2 2 2 2 = Real.pi / 2 + atn2 (Real.sqrt 2048) (-16) := by
    simp only [dihY, dihXf]
    norm_num [hdx, hdx4]
  have hsqrt2 : Real.sqrt (2048 : ℝ) = 32 * Real.sqrt 2 := by
    rw [show (2048 : ℝ) = 1024 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Real.sin (Real.arctan (1 / (2 * Real.sqrt 2))) = 1 / 3 := by
    rw [Real.sin_arctan]
    have hden : (1 : ℝ) + (1 / (2 * Real.sqrt 2)) ^ 2 = 9 / 8 := by
      have e1 : (1 / (2 * Real.sqrt 2)) ^ 2 = 1 / (2 * Real.sqrt 2) ^ 2 := by
        rw [one_div_pow]
      have e2 : (2 * Real.sqrt 2) ^ 2 = 8 := by rw [mul_pow, hsq2]; norm_num
      rw [e1, e2]
      norm_num
    have hr8 : Real.sqrt (9 / 8) = 3 / (2 * Real.sqrt 2) := by
      have hval : (9 / 8 : ℝ) = (3 / (2 * Real.sqrt 2)) ^ 2 := by
        rw [div_pow, mul_pow, hsq2]
        norm_num
      rw [hval, Real.sqrt_sq (by positivity)]
    rw [hden, hr8]
    field_simp
  have hθ : Real.arcsin (1 / 3) = Real.arctan (1 / (2 * Real.sqrt 2)) := by
    rw [← hs]
    obtain ⟨hm1, hm2⟩ := Real.arctan_mem_Ioo (1 / (2 * Real.sqrt 2))
    exact Real.arcsin_sin' ⟨le_of_lt hm1, le_of_lt hm2⟩
  have hv : atn2 (32 * Real.sqrt 2) (-16) = -(Real.arcsin (1 / 3)) := by
    have h1s : (1 : ℝ) < Real.sqrt 2 :=
      (Real.lt_sqrt (x := (1 : ℝ)) (by norm_num)).mpr (by norm_num)
    have hbr : |(-16 : ℝ)| < 32 * Real.sqrt 2 := by
      rw [abs_of_neg (by norm_num : (-16 : ℝ) < 0), neg_neg]
      calc (16 : ℝ) = 16 * 1 := by ring
        _ < 16 * (2 * Real.sqrt 2) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
        _ = 32 * Real.sqrt 2 := by ring
    have hconv : (-16 : ℝ) / (32 * Real.sqrt 2) = -(1 / (2 * Real.sqrt 2)) := by
      field_simp
      ring
    simp only [atn2, hbr, if_true, hconv, Real.arctan_neg, ← hθ]
  rw [hd, hsqrt2, hv, Real.arccos_eq_pi_div_two_sub_arcsin (1 / 3)]
  ring

private theorem la22_const1_eq : const1 = sol0 / Real.pi := by
  have hs0 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  have hsol : solY 2 2 2 2 2 2 = 3 * Real.arccos (1 / 3) - Real.pi := by
    show dihY 2 2 2 2 2 2 + dihY 2 2 2 2 2 2 + dihY 2 2 2 2 2 2 - Real.pi = _
    rw [la22_dihY222222]
    ring
  show solY 2 2 2 2 2 2 / Real.pi = sol0 / Real.pi
  rw [hs0, hsol]

private theorem la22_taum_eq (y1 y2 y3 y4 y5 y6 : ℝ) :
    taum y1 y2 y3 y4 y5 y6 =
      rho y1 * dihY y1 y2 y3 y4 y5 y6 +
        rho y2 * dihY y2 y3 y1 y5 y6 y4 +
        rho y3 * dihY y3 y1 y2 y6 y4 y5 - (Real.pi + sol0) := by
  have hc : const1 = sol0 / Real.pi := la22_const1_eq
  have ht : (2 : ℝ) * h0 - 2 ≠ 0 := by norm_num [h0]
  have hly : ∀ y : ℝ, ly y = 1 - (y - 2) / (2 * h0 - 2) := by
    intro y
    have h252 : (2.52 - 2 : ℝ) = 2 * h0 - 2 := by norm_num [h0]
    show 1 + (y - 2) * (0 - 1) / (2.52 - 2) = 1 - (y - 2) / (2 * h0 - 2)
    rw [h252]
    ring
  show solY y1 y2 y3 y4 y5 y6 * (1 + const1) -
    const1 * (lnazim y1 y2 y3 y4 y5 y6 +
      lnazim y2 y3 y1 y5 y6 y4 + lnazim y3 y1 y2 y6 y4 y5) = _
  simp only [solY, lnazim, hc, hly, rho]
  field_simp [ht, Real.pi_ne_zero]
  ring

private theorem la22_deltaY_rot231564 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y2 y3 y1 y5 y6 y4 = deltaY y1 y2 y3 y4 y5 y6 := by
  unfold deltaY deltaX
  ring

private theorem la22_deltaY_rot312645 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y3 y1 y2 y6 y4 y5 = deltaY y1 y2 y3 y4 y5 y6 := by
  unfold deltaY deltaX
  ring

private theorem la22_dihY_xrr (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 =
      dihXf 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) := by
  have hy1' : y1 ≠ 0 := ne_of_gt hy1
  have hy2' : y2 ≠ 0 := ne_of_gt hy2
  have hy3' : y3 ≠ 0 := ne_of_gt hy3
  have hD := delta_x_xrr_p22 y1 y2 y3 y4 y5 y6 hy1' hy2' hy3'
  have hD4raw := delta_x4_dim_reduction_p22 y1 y2 y3 y4 y5 y6 hy1' hy2' hy3'
  have hD4 : deltaX4 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)
      = 16 * yOfX deltaX4 y1 y2 y3 y4 y5 y6 / (y1 * y1 * y2 * y3) := hD4raw
  unfold dihXf
  change Real.pi / 2 + atn2
      (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
      (-(yOfX deltaX4 y1 y2 y3 y4 y5 y6)) =
    Real.pi / 2 + atn2
      (Real.sqrt (4 * 4 * deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)))
      (-(deltaX4 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)))
  rw [hD, hD4]
  congr 1
  have hk : (0 : ℝ) < 16 / (y1 * y1 * y2 * y3) := by positivity
  have hA : Real.sqrt (4 * 4 * (64 * deltaY y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2))
      = (16 / (y1 * y1 * y2 * y3)) *
        Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    have hsq : 4 * 4 * (64 * deltaY y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2)
        = (16 / (y1 * y1 * y2 * y3)) ^ 2 *
          (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
      field_simp
      ring
    rw [hsq,
      Real.sqrt_mul (x := (16 / (y1 * y1 * y2 * y3)) ^ 2) (by positivity)
        (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6),
      Real.sqrt_sq hk.le]
  have hB : -(16 * yOfX deltaX4 y1 y2 y3 y4 y5 y6 / (y1 * y1 * y2 * y3))
      = (16 / (y1 * y1 * y2 * y3)) * (-(yOfX deltaX4 y1 y2 y3 y4 y5 y6)) := by
    ring
  rw [hA, hB, la22_atn2_smul hk]

private theorem la22_taum_compose (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    taum y1 y2 y3 y4 y5 y6 =
      rho y1 * dihXf 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) +
      rho y2 * dihXf 4 4 4 (xrr y1 y3 y5) (xrr y1 y2 y6) (xrr y2 y3 y4) +
      rho y3 * dihXf 4 4 4 (xrr y1 y2 y6) (xrr y2 y3 y4) (xrr y1 y3 y5) -
        (Real.pi + sol0) := by
  have h1 := la22_dihY_xrr y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have hd2 : 0 < deltaY y2 y3 y1 y5 y6 y4 := by
    rw [la22_deltaY_rot231564]; exact hd
  have h2 := la22_dihY_xrr y2 y3 y1 y5 y6 y4 hy2 hy3 hy1 hd2
  have hd3 : 0 < deltaY y3 y1 y2 y6 y4 y5 := by
    rw [la22_deltaY_rot312645]; exact hd
  have h3 := la22_dihY_xrr y3 y1 y2 y6 y4 y5 hy3 hy1 hy2 hd3
  rw [la22_taum_eq, h1, h2, h3, xrr_sym_p22 y3 y1 y5, xrr_sym_p22 y2 y1 y6,
    xrr_sym_p22 y3 y2 y4]

private theorem la22_G_hasDerivAt (e1 e2 e3 x4 x5 x6 : ℝ)
    (h4 : 0 < x4) (h4' : x4 < 16) (hΔ : 0 < deltaX 4 4 4 x4 x5 x6) :
    HasDerivAt (fun q => e1 * dihXf 4 4 4 q x5 x6 + e2 * dihXf 4 4 4 x5 x6 q
        + e3 * dihXf 4 4 4 x6 q x5 - (1 + const1) * Real.pi)
      (num1 e1 e2 e3 x4 x5 x6 /
        (2 * x4 * (16 - x4) * Real.sqrt (deltaX 4 4 4 x4 x5 x6))) x4 := by
  have hcyc2 : deltaX 4 4 4 x5 x6 x4 = deltaX 4 4 4 x4 x5 x6 := by unfold deltaX; ring
  have hcyc3 : deltaX 4 4 4 x6 x4 x5 = deltaX 4 4 4 x4 x5 x6 := by unfold deltaX; ring
  have hΔ2 : 0 < deltaX 4 4 4 x5 x6 x4 := by rw [hcyc2]; exact hΔ
  have hΔ3 : 0 < deltaX 4 4 4 x6 x4 x5 := by rw [hcyc3]; exact hΔ
  have h1 := dihXf_hasDerivAt_x4 4 4 4 x4 x5 x6 (by norm_num) hΔ
  have h2 := dihXf_hasDerivAt_x6 4 4 4 x5 x6 x4 (by norm_num) hΔ2
  have h3 := dihXf_hasDerivAt_x5 4 4 4 x6 x4 x5 (by norm_num) hΔ3
  have h := (((h1.const_mul e1).add (h2.const_mul e2)).add (h3.const_mul e3)).sub
    (hasDerivAt_const (x := x4) ((1 + const1) * Real.pi))
  refine h.congr_deriv ?_
  rw [hcyc2, hcyc3]
  have hsq : ∀ D : ℝ, Real.sqrt (4 * 4 * D) = 4 * Real.sqrt D := by
    intro D
    rw [show (4:ℝ) * 4 * D = 4^2 * D by ring,
        Real.sqrt_mul (x := (4:ℝ)^2) (by norm_num) D, Real.sqrt_sq (by norm_num)]
  rw [hsq]
  have hu4 : upsX 4 4 x4 = x4 * (16 - x4) := by unfold upsX; ring
  rw [hu4]
  have hU4 : (0:ℝ) < x4 * (16 - x4) := by nlinarith
  have h16 : (16:ℝ) - x4 ≠ 0 := by nlinarith
  have hpoly : 4 * (e1 * (x4 * (16 - x4))
      - e2 * deltaX5 4 4 4 x5 x6 x4
      - e3 * g4dDX6 4 4 4 x6 x4 x5) = num1 e1 e2 e3 x4 x5 x6 := by
    unfold num1 deltaX5 g4dDX6
    ring
  field_simp [hU4.ne', h16, (Real.sqrt_pos.mpr hΔ).ne']
  linear_combination hpoly



private theorem la22_xrr_strictMonoOn (y2 y3 : ℝ) (hy2 : 0 < y2) (hy3 : 0 < y3)
    {q1 q2 : ℝ} (h1 : 0 < q1) (hlt : q1 < q2) : xrr y2 y3 q1 < xrr y2 y3 q2 := by
  have h2 : 0 < q2 := by linarith
  have h : xrr y2 y3 q2 - xrr y2 y3 q1 = 4 * (q2 - q1) * (q2 + q1) / (y2 * y3) := by
    unfold xrr
    field_simp
    ring
  have hpos : 0 < 4 * (q2 - q1) * (q2 + q1) / (y2 * y3) := by positivity
  linarith

private theorem la22_xrr_continuousAt (y2 y3 q : ℝ) :
    ContinuousAt (fun q => xrr y2 y3 q) q := by
  have hq : Continuous fun q : ℝ => y2 * y2 + y3 * y3 - q * q := by
    exact continuous_const.sub (continuous_id.mul continuous_id)
  have h : Continuous fun q : ℝ => 8 * (1 - (y2 * y2 + y3 * y3 - q * q) / (2 * y2 * y3)) :=
    continuous_const.mul (continuous_const.sub (hq.div_const _))
  unfold xrr
  exact h.continuousAt

private theorem la22_xrr_decreasing (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
    (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2' : y2 ≤ 2 * h0) (hlt : y1 ≤ y1') :
    xrr y1' y2 y6 ≤ xrr y1 y2 y6 := by
  have hp1 : (0:ℝ) < y1 := by linarith
  have hp1' : (0:ℝ) < y1' := by linarith
  have hp2 : (0:ℝ) < y2 := by linarith
  have hdiff : xrr y1 y2 y6 - xrr y1' y2 y6
      = 4 * (y1' - y1) * (y1 * y1' + y6 * y6 - y2 * y2) / (y1 * y1' * y2) := by
    unfold xrr
    field_simp
    ring
  have h0v : (2 * h0) * (2 * h0) = 6.3504 := by norm_num [h0_eq_p22]
  have hnn : 0 ≤ y1 * y1' + y6 * y6 - y2 * y2 := by
    have h22 : y2 * y2 ≤ (2 * h0) * (2 * h0) := by nlinarith
    nlinarith
  have hle : 0 ≤ 4 * (y1' - y1) * (y1 * y1' + y6 * y6 - y2 * y2) / (y1 * y1' * y2) := by
    positivity
  linarith

private theorem la22_xrr_simple_lower (y1 y2 y6 y6inf : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6inf) (hy6' : y6inf ≤ y6) :
    (y6inf / h0) ^ 2 ≤ xrr y1 y2 y6 := by
  have h1 : xrr (2 * h0) y2 y6 ≤ xrr y1 y2 y6 :=
    la22_xrr_decreasing y1 (2 * h0) y2 y6 hy1 (by linarith) hy2 (by linarith) hy2' hy1'
  have h2 : xrr (2 * h0) (2 * h0) y6 ≤ xrr (2 * h0) y2 y6 := by
    have h := la22_xrr_decreasing y2 (2 * h0) (2 * h0) y6 hy2 (by linarith)
      (by linarith) (by linarith) le_rfl hy2'
    rwa [xrr_sym_p22 y2 (2 * h0) y6] at h
  have h3 : xrr (2 * h0) (2 * h0) y6inf ≤ xrr (2 * h0) (2 * h0) y6 := by
    rcases lt_or_eq_of_le hy6' with hlt | heq
    · exact le_of_lt (xrr_increasing_p22 _ _ _ _ (by linarith) (by linarith) (by linarith) hlt)
    · rw [heq]
  have h4 : xrr (2 * h0) (2 * h0) y6inf = (y6inf / h0) ^ 2 := by
    have h0ne : (h0 : ℝ) ≠ 0 := by norm_num [h0_eq_p22]
    unfold xrr
    field_simp
    ring
  linarith

private theorem la22_xrr_simple_upper (y1 y2 y6 y6sup : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ y6sup)
    (_hy6sup : y6sup < 4) :
    xrr y1 y2 y6 ≤ y6sup ^ 2 := by
  have h1 : xrr y1 y2 y6 ≤ xrr 2 y2 y6 :=
    la22_xrr_decreasing 2 y1 y2 y6 (by norm_num) hy1 hy2 hy6 hy2' hy1
  have h2 : xrr 2 y2 y6 ≤ xrr 2 2 y6 := by
    have h := la22_xrr_decreasing 2 y2 2 y6 (by norm_num) hy2 (by norm_num) hy6
      (by linarith) hy2
    rw [xrr_sym_p22 2 y2 y6]
    exact h
  have h3 : xrr 2 2 y6 ≤ xrr 2 2 y6sup := by
    rcases lt_or_eq_of_le hy6' with hlt | heq
    · exact le_of_lt (xrr_increasing_p22 2 2 y6 y6sup (by norm_num) (by norm_num) (by linarith) hlt)
    · rw [heq]
  have h4 : xrr 2 2 y6sup = y6sup ^ 2 := by
    unfold xrr
    field_simp
    ring
  linarith

private theorem la22_upsX_box (a b c : ℝ) (ha : 2 ≤ a) (ha' : a ≤ 2 * h0)
    (hb : 2 ≤ b) (hb' : b ≤ 2 * h0) (hc : 2 ≤ c) (hc' : c ≤ 2 * h0) :
    0 < upsX (a * a) (b * b) (c * c) := by
  have h2h0 : (2:ℝ) * h0 = 2.52 := by norm_num [h0_eq_p22]
  refine TRI_UPS_X_STRICT_POS a b c (by linarith) (by linarith) (by linarith)
    ?_ ?_ ?_
  · nlinarith
  · nlinarith
  · nlinarith



private theorem la22_deltaY_continuous (y1 y2 y3 y5 y6 : ℝ) :
    Continuous (fun q => deltaY y1 y2 y3 q y5 y6) := by
  unfold deltaY deltaX
  continuity

private theorem la22_taum_hasDerivAt (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (_hy5 : 0 < y5) (_hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4)) :
    HasDerivAt (fun q => taum y1 y2 y3 q y5 y6)
      ((num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)
        / (2 * xrr y2 y3 y4 * (16 - xrr y2 y3 y4)
           * Real.sqrt (deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6))))
        * (8 * y4 / (y2 * y3))) y4 := by
  have hx4 := (xrr_bounds_2_p22 y2 y3 y4 hy2 hy3 hy4).mp hu4
  have hΔ : 0 < deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) := by
    rw [delta_x_xrr_p22 y1 y2 y3 y4 y5 y6 (ne_of_gt hy1) (ne_of_gt hy2) (ne_of_gt hy3)]
    positivity
  have hG := la22_G_hasDerivAt (rho y1) (rho y2) (rho y3)
    (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) hx4.1 hx4.2 hΔ
  have hxrr : HasDerivAt (fun q => xrr y2 y3 q) (8 * y4 / (y2 * y3)) y4 :=
    ((derived_form_xrr_p22 y2 y3 y4) ⟨hy2, hy3⟩).hasDerivAt (by simp)
  have hcomp := hG.comp y4 hxrr
  refine hcomp.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ q in 𝓝 y4, 0 < deltaY y1 y2 y3 q y5 y6 :=
    (la22_deltaY_continuous y1 y2 y3 y5 y6).continuousAt.eventually_mem
      (isOpen_Ioi.mem_nhds hd)
  filter_upwards [hev] with q hq
  have hc1 : Real.pi + sol0 = (1 + const1) * Real.pi := by
    rw [la22_const1_eq]
    field_simp
  rw [Function.comp_apply, ← hc1]
  exact la22_taum_compose y1 y2 y3 q y5 y6 hy1 hy2 hy3 hq

private theorem la22_taum_deriv_eq (y1 y2 y3 c y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hc : 0 < c)
    (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 c y5 y6)
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (c * c)) :
    deriv (fun q => taum y1 y2 y3 q y5 y6) c
      = (num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6)
        / (2 * xrr y2 y3 c * (16 - xrr y2 y3 c)
           * Real.sqrt (deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6))))
        * (8 * c / (y2 * y3)) :=
  (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1 hy2 hy3 hc hy5 hy6 hd hu4).deriv

private theorem la22_taum_deriv_pos (y1 y2 y3 c y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hc : 0 < c)
    (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 c y5 y6)
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (c * c))
    (hnum : 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 c) (xrr y1 y3 y5)
      (xrr y1 y2 y6)) :
    0 < deriv (fun q => taum y1 y2 y3 q y5 y6) c := by
  rw [la22_taum_deriv_eq y1 y2 y3 c y5 y6 hy1 hy2 hy3 hc hy5 hy6 hd hu4]
  have hx4 := (xrr_bounds_2_p22 y2 y3 c hy2 hy3 hc).mp hu4
  have hΔ : 0 < deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6) := by
    rw [delta_x_xrr_p22 y1 y2 y3 c y5 y6 (ne_of_gt hy1) (ne_of_gt hy2) (ne_of_gt hy3)]
    positivity
  have h16 : 0 < (16:ℝ) - xrr y2 y3 c := by linarith [hx4.2]
  have hsqrt : 0 < Real.sqrt (deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6)) :=
    Real.sqrt_pos.mpr hΔ
  have hden : 0 < 2 * xrr y2 y3 c * (16 - xrr y2 y3 c)
      * Real.sqrt (deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6)) := by
    have hA : 0 < 2 * xrr y2 y3 c := by
      have := hx4.1; linarith
    exact mul_pos (mul_pos hA h16) hsqrt
  exact mul_pos (div_pos hnum hden)
    (div_pos (by nlinarith [hc]) (mul_pos hy2 hy3))

private theorem la22_taum_deriv_neg (y1 y2 y3 c y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hc : 0 < c)
    (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 c y5 y6)
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (c * c))
    (hnum : num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 c) (xrr y1 y3 y5)
      (xrr y1 y2 y6) < 0) :
    deriv (fun q => taum y1 y2 y3 q y5 y6) c < 0 := by
  rw [la22_taum_deriv_eq y1 y2 y3 c y5 y6 hy1 hy2 hy3 hc hy5 hy6 hd hu4]
  have hx4 := (xrr_bounds_2_p22 y2 y3 c hy2 hy3 hc).mp hu4
  have hΔ : 0 < deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6) := by
    rw [delta_x_xrr_p22 y1 y2 y3 c y5 y6 (ne_of_gt hy1) (ne_of_gt hy2) (ne_of_gt hy3)]
    positivity
  have hsqrt : 0 < Real.sqrt (deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6)) :=
    Real.sqrt_pos.mpr hΔ
  have hden : 0 < 2 * xrr y2 y3 c * (16 - xrr y2 y3 c)
      * Real.sqrt (deltaX 4 4 4 (xrr y2 y3 c) (xrr y1 y3 y5) (xrr y1 y2 y6)) := by
    have := hx4.1; have := hx4.2
    positivity
  have hfac : 0 < 8 * c / (y2 * y3) := by positivity
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hnum hden) hfac

private theorem la22_mvt_lt {F : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hcont : ContinuousOn F (Set.Icc p q))
    (hdiff : DifferentiableOn ℝ F (Set.Ioo p q))
    (hpos : ∀ c ∈ Set.Ioo p q, 0 < deriv F c) :
    F p < F q := by
  obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope F hpq hcont hdiff
  have hp := hpos c hc
  rw [hcder] at hp
  have hq : 0 < q - p := by linarith
  have hpos' : 0 < F q - F p := (div_pos_iff_of_pos_right hq).mp hp
  linarith

private theorem la22_mvt_lt_of_neg {F : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hcont : ContinuousOn F (Set.Icc p q))
    (hdiff : DifferentiableOn ℝ F (Set.Ioo p q))
    (hneg : ∀ c ∈ Set.Ioo p q, deriv F c < 0) :
    F q < F p := by
  obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope F hpq hcont hdiff
  have hp := hneg c hc
  rw [hcder] at hp
  have hq : 0 < q - p := by linarith
  have hneg' : F q - F p < 0 := by
    rcases (div_neg_iff.mp hp) with ⟨_, hneg⟩ | ⟨hlt, _⟩
    · linarith
    · exact hlt
  linarith

private theorem la22_upsX_pos3 (a b c : ℝ) (ha : 2 ≤ a) (ha' : a ≤ 2 * h0)
    (hb : 2 ≤ b) (hb' : b ≤ 2 * h0) (hc : 2 ≤ c) (hc' : c ≤ 3.01) :
    0 < upsX (a * a) (b * b) (c * c) := by
  have h2h0 : (2:ℝ) * h0 = 2.52 := by norm_num [h0_eq_p22]
  refine TRI_UPS_X_STRICT_POS a b c (by linarith) (by linarith) (by linarith) ?_ ?_ ?_
  · nlinarith
  · nlinarith
  · nlinarith

end La22TaumMonoKit

/-- HOL `LEMMA_1834976363`. -/
-- PROVED 2026-11-12 (lane `la22mono-w1`): from the `La22TaumMonoKit` block
-- above (registry `1834976363` + MVT); `#print axioms` = standard three.
theorem LEMMA_1834976363_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 a b : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0)
    (hx4 : (2 / h0) ^ 2 ≤ xrr y2 y3 y4 ∧ xrr y2 y3 y4 ≤ 15.53)
    (hx5 : (2 / h0) ^ 2 ≤ xrr y1 y3 y5) (hx6 : (2 / h0) ^ 2 ≤ xrr y1 y2 y6)
    (hy4 : y4 ∈ Set.Ioo a b)
    (hsub : Set.Ioo a b ⊆ {y | 0 < deltaY y1 y2 y3 y y5 y6 ∧ 0 < y ∧
      0 < upsX (y2 * y2) (y3 * y3) (y * y)})
    (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ∃ y4', y4' ∈ Set.Ioo a b ∧ taum y1 y2 y3 y4' y5 y6 < taum y1 y2 y3 y4 y5 y6 := by
  have hy1p : 0 < y1 := by linarith [hy1.1]
  have hy2p : 0 < y2 := by linarith [hy2.1]
  have hy3p : 0 < y3 := by linarith [hy3.1]
  have hy4p : 0 < y4 := (hsub hy4).2.1
  have hx5lt : xrr y1 y3 y5 < 16 :=
    ((xrr_bounds_2_p22 y1 y3 y5 hy1p hy3p hy5).mp hu5).2
  have hx6lt : xrr y1 y2 y6 < 16 :=
    ((xrr_bounds_2_p22 y1 y2 y6 hy1p hy2p hy6).mp hu6).2
  have hx5le : xrr y1 y3 y5 ≤ 4 ^ 2 := by norm_num; linarith
  have hx6le : xrr y1 y2 y6 ≤ 4 ^ 2 := by norm_num; linarith
  have hnum := (h "1834976363" (by simp [mainNonlinearTerminalV11Ids_t11]))
    (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)
    (rho_bounds_p22 y1 hy1.1 hy1.2).1 (rho_bounds_p22 y1 hy1.1 hy1.2).2
    (rho_bounds_p22 y2 hy2.1 hy2.2).1 (rho_bounds_p22 y2 hy2.1 hy2.2).2
    (rho_bounds_p22 y3 hy3.1 hy3.2).1 (rho_bounds_p22 y3 hy3.1 hy3.2).2
    hx4.1 hx4.2 hx5 hx5le hx6 hx6le
  -- case split on the sign of num1 at y4
  by_cases hpos : 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4)
      (xrr y1 y3 y5) (xrr y1 y2 y6)
  · -- (A) strictly increasing on a neighbourhood
    let S : Set ℝ := Set.Ioo a b ∩
      {q | 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 q) (xrr y1 y3 y5)
        (xrr y1 y2 y6)}
    have hSopen : IsOpen S := by
      refine isOpen_Ioo.inter ?_
      have hcont : Continuous (fun q => num1 (rho y1) (rho y2) (rho y3)
          (xrr y2 y3 q) (xrr y1 y3 y5) (xrr y1 y2 y6)) := by
        unfold num1 xrr
        continuity
      exact isOpen_lt continuous_const hcont
    have hy4S : y4 ∈ S := ⟨hy4, hpos⟩
    obtain ⟨α, β, hy4αβ, hαβS⟩ :=
      real_open_contains_real_interval_p22 y4 S hy4S hSopen
    have hα4 : α < y4 := hy4αβ.1
    have h4β : y4 < β := hy4αβ.2
    let p : ℝ := (α + y4) / 2
    have hαp : α < p := by simp only [p]; linarith
    have hpy4 : p < y4 := by simp only [p]; linarith
    have hpS : p ∈ S := hαβS ⟨hαp, by linarith⟩
    -- differentiability and derivative positivity on [p, y4]
    have hdiff : DifferentiableOn ℝ (fun q => taum y1 y2 y3 q y5 y6) (Set.Ioo p y4) := by
      intro c hc
      have hcS : c ∈ S := hαβS ⟨by linarith [hc.1], by linarith [hc.2]⟩
      have hcab : c ∈ Set.Ioo a b := hcS.1
      have hc4 := hsub hcab
      exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
        hc4.1 hc4.2.2).differentiableAt.differentiableWithinAt
    have hcont : ContinuousOn (fun q => taum y1 y2 y3 q y5 y6) (Set.Icc p y4) := by
      intro c hc
      have hcp : p ≤ c := hc.1
      have hcy : c ≤ y4 := hc.2
      have hcab : c ∈ Set.Ioo a b := by
        have : c ∈ S := hαβS ⟨by linarith, by linarith⟩
        exact this.1
      have hc4 := hsub hcab
      exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
        hc4.1 hc4.2.2).continuousAt.continuousWithinAt
    have hderivpos : ∀ c ∈ Set.Ioo p y4, 0 < deriv (fun q => taum y1 y2 y3 q y5 y6) c := by
      intro c hc
      have hcS : c ∈ S := hαβS ⟨by linarith [hc.1], by linarith [hc.2]⟩
      have hcab : c ∈ Set.Ioo a b := hcS.1
      have hc4 := hsub hcab
      exact la22_taum_deriv_pos y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
        hc4.1 hc4.2.2 hcS.2
    exact ⟨p, hpS.1, la22_mvt_lt (F := fun q => taum y1 y2 y3 q y5 y6) hpy4 hcont hdiff hderivpos⟩
  · by_cases hneg : num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4)
        (xrr y1 y3 y5) (xrr y1 y2 y6) < 0
    · -- (B) strictly decreasing on a neighbourhood
      let S : Set ℝ := Set.Ioo a b ∩
        {q | num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 q) (xrr y1 y3 y5)
          (xrr y1 y2 y6) < 0}
      have hSopen : IsOpen S := by
        refine isOpen_Ioo.inter ?_
        have hcont : Continuous (fun q => num1 (rho y1) (rho y2) (rho y3)
            (xrr y2 y3 q) (xrr y1 y3 y5) (xrr y1 y2 y6)) := by
          unfold num1 xrr
          continuity
        exact isOpen_lt hcont continuous_const
      have hy4S : y4 ∈ S := ⟨hy4, hneg⟩
      obtain ⟨α, β, hy4αβ, hαβS⟩ :=
        real_open_contains_real_interval_p22 y4 S hy4S hSopen
      let q : ℝ := (y4 + β) / 2
      have h4q : y4 < q := by simp only [q]; linarith [hy4αβ.2]
      have hqβ : q < β := by simp only [q]; linarith [hy4αβ.2]
      have hqS : q ∈ S := hαβS ⟨by linarith [hy4αβ.1], hqβ⟩
      have hdiff : DifferentiableOn ℝ (fun q => taum y1 y2 y3 q y5 y6) (Set.Ioo y4 q) := by
        intro c hc
        have hcS : c ∈ S := hαβS ⟨by linarith [hc.1, hy4αβ.1], by linarith [hc.2]⟩
        have hcab : c ∈ Set.Ioo a b := hcS.1
        have hc4 := hsub hcab
        exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
          hc4.1 hc4.2.2).differentiableAt.differentiableWithinAt
      have hcont : ContinuousOn (fun q => taum y1 y2 y3 q y5 y6) (Set.Icc y4 q) := by
        intro c hc
        have hcab : c ∈ Set.Ioo a b := by
          have : c ∈ S := hαβS ⟨by linarith [hc.1, hy4αβ.1], by linarith [hc.2, hqβ]⟩
          exact this.1
        have hc4 := hsub hcab
        exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
          hc4.1 hc4.2.2).continuousAt.continuousWithinAt
      have hderivneg : ∀ c ∈ Set.Ioo y4 q, deriv (fun q => taum y1 y2 y3 q y5 y6) c < 0 := by
        intro c hc
        have hcS : c ∈ S := hαβS ⟨by linarith [hc.1, hy4αβ.1], by linarith [hc.2, hqβ]⟩
        have hcab : c ∈ Set.Ioo a b := hcS.1
        have hc4 := hsub hcab
        exact la22_taum_deriv_neg y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
          hc4.1 hc4.2.2 hcS.2
      exact ⟨q, hqS.1, la22_mvt_lt_of_neg (F := fun q => taum y1 y2 y3 q y5 y6) h4q hcont hdiff hderivneg⟩
    · -- (C) critical point: num1 = 0 and dnum1 < 0
      have hzero : num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4)
          (xrr y1 y3 y5) (xrr y1 y2 y6) = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hcrit : dnum1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4)
          (xrr y1 y3 y5) (xrr y1 y2 y6) < 0 := by
        rcases hnum with hh | hh | hh
        · exact absurd hh hpos
        · exact absurd hh hneg
        · exact hh
      have he1 : 0 < rho y1 := by linarith [(rho_bounds_p22 y1 hy1.1 hy1.2).1]
      let d := dnum1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4)
        (xrr y1 y3 y5) (xrr y1 y2 y6)
      let e1 := rho y1
      have hdneg : d < 0 := hcrit
      have hε : 0 < -d / (4 * e1) := by
        have : 0 < 4 * e1 := by simp only [e1]; linarith
        exact div_pos (by linarith) this
      -- the quadratic expansion of num1 around x4 = xrr y2 y3 y4
      have hquad : ∀ x : ℝ, num1 e1 (rho y2) (rho y3) x (xrr y1 y3 y5) (xrr y1 y2 y6)
          = -4 * e1 * (x - xrr y2 y3 y4) ^ 2 + 4 * d * (x - xrr y2 y3 y4) := by
        intro x
        have h0 : num1 e1 (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
            (xrr y1 y2 y6) = 0 := hzero
        calc num1 e1 (rho y2) (rho y3) x (xrr y1 y3 y5) (xrr y1 y2 y6)
            = num1 e1 (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
                (xrr y1 y2 y6)
              + 4 * d * (x - xrr y2 y3 y4)
              - 4 * e1 * (x - xrr y2 y3 y4) ^ 2 := by
              simp only [d, e1]
              unfold num1 dnum1
              ring
          _ = -4 * e1 * (x - xrr y2 y3 y4) ^ 2 + 4 * d * (x - xrr y2 y3 y4) := by
              rw [h0]; ring
      -- the left neighbourhood of x4 where num1 > 0
      have hleftpos : ∀ x : ℝ, xrr y2 y3 y4 - (-d / (4 * e1)) < x → x < xrr y2 y3 y4 →
          0 < num1 e1 (rho y2) (rho y3) x (xrr y1 y3 y5) (xrr y1 y2 y6) := by
        intro x hx1 hx2
        rw [hquad x]
        set t := x - xrr y2 y3 y4 with ht
        have htneg : t < 0 := by rw [ht]; linarith
        have hb1 : -t < -d / (4 * e1) := by rw [ht]; linarith
        have he : 0 < 4 * e1 := by simp only [e1]; linarith
        have hb : d - e1 * t < 0 := by
          have h2 : e1 * (-t) < e1 * (-d / (4 * e1)) :=
            mul_lt_mul_of_pos_left hb1 he1
          have h3 : e1 * (-d / (4 * e1)) = -d / 4 := by
            simp only [e1]
            field_simp
          rw [h3] at h2
          nlinarith
        have hfac : -4 * e1 * t ^ 2 + 4 * d * t = 4 * t * (d - e1 * t) := by ring
        rw [hfac]
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      -- pull back to a one-sided y-interval
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp
        (la22_xrr_continuousAt y2 y3 y4) (-d / (4 * e1)) hε
      let ρ := min (δ / 2) ((y4 - a) / 2)
      have hρpos : 0 < ρ := by
        have h1 : 0 < δ / 2 := by linarith
        have h2 : 0 < (y4 - a) / 2 := by linarith [hy4.1]
        exact lt_min h1 h2
      have hρδ : ρ < δ := by
        have h1 : ρ ≤ δ / 2 := min_le_left _ _
        linarith
      have hρa : ρ < y4 - a := by
        have h1 : ρ ≤ (y4 - a) / 2 := min_le_right _ _
        linarith [hy4.1]
      let q : ℝ := y4 - ρ
      have hq4 : q < y4 := by simp only [q]; linarith
      have hqa : a < q := by simp only [q]; linarith
      have hqpos : 0 < q := (hsub ⟨hqa, by linarith [hy4.2]⟩).2.1
      have hqδ : dist q y4 < δ := by
        rw [Real.dist_eq]
        have : |q - y4| = ρ := by
          rw [show q - y4 = -ρ by simp only [q]; ring, abs_neg, abs_of_pos hρpos]
        rw [this]
        exact hρδ
      have hxq : xrr y2 y3 y4 - (-d / (4 * e1)) < xrr y2 y3 q ∧
          xrr y2 y3 q < xrr y2 y3 y4 := by
        have hdist := hδ hqδ
        rw [Real.dist_eq] at hdist
        have habs : |xrr y2 y3 q - xrr y2 y3 y4| < -d / (4 * e1) := hdist
        have hlt1 := (abs_lt.mp habs).1
        have hsmono : xrr y2 y3 q < xrr y2 y3 y4 :=
          la22_xrr_strictMonoOn y2 y3 hy2p hy3p hqpos hq4
        exact ⟨by linarith, hsmono⟩
      have hqnum : 0 < num1 e1 (rho y2) (rho y3) (xrr y2 y3 q) (xrr y1 y3 y5)
          (xrr y1 y2 y6) := hleftpos _ hxq.1 hxq.2
      -- derivative positivity on (q, y4)
      have hdiff : DifferentiableOn ℝ (fun q => taum y1 y2 y3 q y5 y6) (Set.Ioo q y4) := by
        intro c hc
        have hcab : c ∈ Set.Ioo a b := ⟨by linarith [hc.1], by linarith [hc.2, hy4.2]⟩
        have hc4 := hsub hcab
        exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
          hc4.1 hc4.2.2).differentiableAt.differentiableWithinAt
      have hcont : ContinuousOn (fun q => taum y1 y2 y3 q y5 y6) (Set.Icc q y4) := by
        intro c hc
        have hcab : c ∈ Set.Ioo a b := ⟨by linarith [hc.1], by linarith [hc.2, hy4.2]⟩
        have hc4 := hsub hcab
        exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
          hc4.1 hc4.2.2).continuousAt.continuousWithinAt
      have hderivpos : ∀ c ∈ Set.Ioo q y4, 0 < deriv (fun q => taum y1 y2 y3 q y5 y6) c := by
        intro c hc
        have hcab : c ∈ Set.Ioo a b := ⟨by linarith [hc.1], by linarith [hc.2, hy4.2]⟩
        have hc4 := hsub hcab
        have hxc : xrr y2 y3 y4 - (-d / (4 * e1)) < xrr y2 y3 c ∧
            xrr y2 y3 c < xrr y2 y3 y4 := by
          have hlt1 : xrr y2 y3 q < xrr y2 y3 c :=
            la22_xrr_strictMonoOn y2 y3 hy2p hy3p hqpos hc.1
          have hlt2 : xrr y2 y3 c < xrr y2 y3 y4 :=
            la22_xrr_strictMonoOn y2 y3 hy2p hy3p (by linarith [hqpos, hc.1]) hc.2
          exact ⟨by linarith [hxq.1, hlt1], by linarith [hlt2]⟩
        have hnumc : 0 < num1 e1 (rho y2) (rho y3) (xrr y2 y3 c) (xrr y1 y3 y5)
            (xrr y1 y2 y6) := hleftpos _ hxc.1 hxc.2
        have := la22_taum_deriv_pos y1 y2 y3 c y5 y6 hy1p hy2p hy3p hc4.2.1 hy5 hy6
          hc4.1 hc4.2.2 ?_
        · exact this
        · simpa only [e1] using hnumc
      exact ⟨q, ⟨hqa, by linarith [hy4.2]⟩, la22_mvt_lt (F := fun q => taum y1 y2 y3 q y5 y6) hq4 hcont hdiff hderivpos⟩

/-- HOL `NUM1_GENERIC`. -/
theorem NUM1_GENERIC_p22 (x4inf x4sup x5inf x5sup x6inf x6sup y1 y2 y3 y4 y5 y6 : ℝ)
    (hbox : ineqP22 [(1, rho y1, 1 + sol0 / Real.pi), (1, rho y2, 1 + sol0 / Real.pi),
      (1, rho y3, 1 + sol0 / Real.pi), (x4inf, xrr y2 y3 y4, x4sup),
      (x5inf, xrr y1 y3 y5, x5sup), (x6inf, xrr y1 y2 y6, x6sup)] True)
    (hnz : 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5)
      (xrr y1 y2 y6))
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0)
    (hx4 : x4inf ≤ xrr y2 y3 y4 ∧ xrr y2 y3 y4 ≤ x4sup)
    (hx5 : x5inf ≤ xrr y1 y3 y5 ∧ xrr y1 y3 y5 ≤ x5sup)
    (hx6 : x6inf ≤ xrr y1 y2 y6 ∧ xrr y1 y2 y6 ≤ x6sup)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hu4 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum y1 y2 y3 y4' y5 y6 < taum y1 y2 y3 y4'' y5 y6 := by
  sorry

/-- HOL `LEMMA_4828966562`. -/
-- PROVED 2026-11-12 (lane `la22mono-w1`): from the `La22TaumMonoKit` block
-- above (registry `4828966562` + `strictMonoOn_of_deriv_pos`); `#print axioms`
-- = standard three.
theorem LEMMA_4828966562_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0) (hy4 : 2 ≤ y4 ∧ y4 ≤ 2 * h0)
    (hy5 : 2 ≤ y5 ∧ y5 ≤ 3.01) (hy6 : 3 ≤ y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hu6 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum y1 y2 y3 y4' y5 y6 < taum y1 y2 y3 y4'' y5 y6 := by
  have hy1p : 0 < y1 := by linarith [hy1.1]
  have hy2p : 0 < y2 := by linarith [hy2.1]
  have hy3p : 0 < y3 := by linarith [hy3.1]
  have hy4p : 0 < y4 := by linarith [hy4.1]
  have hy5p : 0 < y5 := by linarith [hy5.1]
  have hy6p : 0 < y6 := by linarith
  have hu4 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4) :=
    la22_upsX_box y2 y3 y4 hy2.1 hy2.2 hy3.1 hy3.2 hy4.1 hy4.2
  have hu5 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5) :=
    la22_upsX_pos3 y1 y3 y5 hy1.1 hy1.2 hy3.1 hy3.2 hy5.1 hy5.2
  have h4lo : (2 / h0) ^ 2 ≤ xrr y2 y3 y4 :=
    la22_xrr_simple_lower y2 y3 y4 2 hy2.1 hy2.2 hy3.1 hy3.2 (by norm_num) hy4.1
  have h4hi : xrr y2 y3 y4 ≤ (2 * h0) ^ 2 :=
    la22_xrr_simple_upper y2 y3 y4 (2 * h0) hy2.1 hy2.2 hy3.1 hy3.2 hy4.1 hy4.2
      (by norm_num [h0_eq_p22])
  have h5lo : (2 / h0) ^ 2 ≤ xrr y1 y3 y5 :=
    la22_xrr_simple_lower y1 y3 y5 2 hy1.1 hy1.2 hy3.1 hy3.2 (by norm_num) hy5.1
  have h5hi : xrr y1 y3 y5 ≤ 3.01 ^ 2 :=
    la22_xrr_simple_upper y1 y3 y5 3.01 hy1.1 hy1.2 hy3.1 hy3.2 hy5.1 hy5.2
      (by norm_num)
  have h6lo' : ((3 : ℝ) / h0) ^ 2 ≤ xrr y1 y2 y6 :=
    la22_xrr_simple_lower y1 y2 y6 3 hy1.1 hy1.2 hy2.1 hy2.2 (by norm_num) hy6
  have h6lo : ((2.38 : ℝ)) ^ 2 ≤ xrr y1 y2 y6 := by
    have hc : ((2.38 : ℝ)) ^ 2 ≤ ((3 : ℝ) / h0) ^ 2 := by
      rw [h0_eq_p22]
      norm_num
    linarith
  have h6hi : xrr y1 y2 y6 ≤ (16.0 : ℝ) := by
    have := xrr_le_16_p22 y1 y2 y6 hy1p hy2p hy6p hu6
    rw [show (16.0 : ℝ) = 16 by norm_num]
    exact this
  have hnum := (h "4828966562" (by simp [mainNonlinearTerminalV11Ids_t11]))
    (rho y1) (rho y2) (rho y3) (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6)
    (rho_bounds_p22 y1 hy1.1 hy1.2).1 (rho_bounds_p22 y1 hy1.1 hy1.2).2
    (rho_bounds_p22 y2 hy2.1 hy2.2).1 (rho_bounds_p22 y2 hy2.1 hy2.2).2
    (rho_bounds_p22 y3 hy3.1 hy3.2).1 (rho_bounds_p22 y3 hy3.1 hy3.2).2
    h4lo h4hi h5lo h5hi h6lo h6hi
  let S : Set ℝ := {q | 0 < deltaY y1 y2 y3 q y5 y6} ∩ {q | 0 < q} ∩
    {q | 0 < upsX (y2 * y2) (y3 * y3) (q * q)} ∩
    {q | 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 q) (xrr y1 y3 y5)
      (xrr y1 y2 y6)}
  have hSopen : IsOpen S := by
    have h1 : IsOpen {q : ℝ | 0 < deltaY y1 y2 y3 q y5 y6} :=
      isOpen_lt continuous_const (la22_deltaY_continuous y1 y2 y3 y5 y6)
    have h2 : IsOpen {q : ℝ | 0 < q} := isOpen_Ioi
    have h3 : IsOpen {q : ℝ | 0 < upsX (y2 * y2) (y3 * y3) (q * q)} := by
      apply isOpen_lt continuous_const
      unfold upsX
      continuity
    have h4 : IsOpen {q : ℝ | 0 < num1 (rho y1) (rho y2) (rho y3) (xrr y2 y3 q)
        (xrr y1 y3 y5) (xrr y1 y2 y6)} := by
      apply isOpen_lt continuous_const
      unfold num1 xrr
      continuity
    exact ((h1.inter h2).inter h3).inter h4
  have hy4S : y4 ∈ S := ⟨⟨⟨hd, hy4p⟩, hu4⟩, hnum⟩
  obtain ⟨α, β, hy4αβ, hαβS⟩ :=
    real_open_contains_real_interval_p22 y4 S hy4S hSopen
  have hcont : ContinuousOn (fun q => taum y1 y2 y3 q y5 y6) (Set.Ioo α β) := by
    intro c hc
    obtain ⟨⟨⟨hdc, hcpos⟩, huc⟩, _⟩ := hαβS hc
    exact (la22_taum_hasDerivAt y1 y2 y3 c y5 y6 hy1p hy2p hy3p hcpos hy5p hy6p
      hdc huc).continuousAt.continuousWithinAt
  have hderiv : ∀ c ∈ interior (Set.Ioo α β),
      0 < deriv (fun q => taum y1 y2 y3 q y5 y6) c := by
    intro c hc
    rw [interior_Ioo] at hc
    obtain ⟨⟨⟨hdc, hcpos⟩, huc⟩, hnumc⟩ := hαβS hc
    exact la22_taum_deriv_pos y1 y2 y3 c y5 y6 hy1p hy2p hy3p hcpos hy5p hy6p
      hdc huc hnumc
  have hmono := strictMonoOn_of_deriv_pos (D := Set.Ioo α β)
    (f := fun q => taum y1 y2 y3 q y5 y6) (convex_Ioo α β) hcont hderiv
  exact ⟨α, β, hy4αβ, fun y4' y4'' h1 h2 hlt => hmono h1 h2 hlt⟩

/-- HOL `LEMMA_6843920790`. -/
theorem LEMMA_6843920790_p22 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1 ∧ y1 ≤ 2 * h0) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3 ∧ y3 ≤ 2 * h0) (hy4 : 2 ≤ y4 ∧ y4 ≤ 3.01)
    (hy5 : 3 ≤ y5 ∧ xrr y1 y3 y5 ≤ 15.53) (hy6 : 3 ≤ y6 ∧ xrr y1 y2 y6 ≤ 15.53)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ∃ a b, y4 ∈ Set.Ioo a b ∧ ∀ y4' y4'', y4' ∈ Set.Ioo a b → y4'' ∈ Set.Ioo a b →
      y4' < y4'' → taum y1 y2 y3 y4' y5 y6 < taum y1 y2 y3 y4'' y5 y6 := by
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

/-- Numeric facts for the funlist case bank (decimal crutch via
`sqrt8_flyspeck_p22`; this Mathlib's `norm_num` cannot order `√8` against
decimals directly). -/
private theorem la22two_le_sqrt8 : (2:ℝ) ≤ Real.sqrt 8 :=
  le_trans (by norm_num) (le_of_lt sqrt8_flyspeck_p22.1)
private theorem la22two_h0_le_sqrt8 : 2 * h0 ≤ Real.sqrt 8 := by
  rw [h0_eq_p22]; exact le_trans (by norm_num) (le_of_lt sqrt8_flyspeck_p22.1)
private theorem la22two_h0_lt_sqrt8 : 2 * h0 < Real.sqrt 8 := by
  rw [h0_eq_p22]; exact lt_of_le_of_lt (by norm_num) sqrt8_flyspeck_p22.1
private theorem la22sqrt8_le_cstab : Real.sqrt 8 ≤ cstab := by
  exact le_trans (le_of_lt sqrt8_flyspeck_p22.2) (by norm_num [cstab_eq_p22])
private theorem la22sqrt8_lt_four : Real.sqrt 8 < 4 :=
  lt_trans sqrt8_flyspeck_p22.2 (by norm_num)
private theorem la22cstab_lt_four : cstab < 4 := by rw [cstab_eq_p22]; norm_num
private theorem la22two_h0_lt_four : 2 * h0 < 4 := by rw [h0_eq_p22]; norm_num
private theorem la22two_h0_lt_cstab : 2 * h0 < cstab := by
  rw [h0_eq_p22, cstab_eq_p22]; norm_num
private theorem la22two_h0_le_cstab : 2 * h0 ≤ cstab := by
  rw [h0_eq_p22, cstab_eq_p22]; norm_num
private theorem la22two_le_two_h0 : (2:ℝ) ≤ 2 * h0 := by rw [h0_eq_p22]; norm_num

/-- HOL `is_scs_3T1`: direct `is_scs` verification of the `scs_3T1` funlist
tables (`k = 3, d = 0.11`; slot `(0,1)` carries `√8`, card set `{0}`). The
generator `is_scs_funlist_basic_p22` cannot be literally applied here — its
conclusion type-fits `mkUnadornedV39 k d (funlist a0 d k)` with table default
`= d`, while the registry T/M rows carry defaults `2`/`2 * h0`; the private
funlist kit above is the evaluation + card kit it contributes. -/
theorem is_scs_3T1_p22 : isScsV39 scs3T1 := by
  unfold isScsV39 scs3T1
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), Real.sqrt 8)] 2 3) 3 :=
    la22funlist_periodic2 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), cstab)] (2 * h0) 3) 3 :=
    la22funlist_periodic2 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 3, periodic_empty 3,
    periodic_empty 3, periodic_empty 3, pa, pa, pb, pb, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_,
    fun i => by simp [funlistV39], ?_, ?_, ?_,
    fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    exact ⟨la22funlist_sym _ _ _ i j, la22funlist_sym _ _ _ i j,
      la22funlist_sym _ _ _ i j, la22funlist_sym _ _ _ i j, rfl⟩
  · intro i j
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hz2 : j % 3 < 3 := Nat.mod_lt j (by omega)
    rw [← la22p2mod_fun pa i j, ← la22p2mod_fun pb i j]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [funlistV39, psort, assocdV39, la22sqrt8_le_cstab, la22two_le_two_h0] <;>
      norm_num [h0_eq_p22]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39, la22two_le_sqrt8] <;> norm_num
  · intro i hk3
    have hz : i % 3 < 3 := Nat.mod_lt i (by omega)
    rw [la22funlist_edge_mod _ _ 3 i (by omega)]
    interval_cases i % 3 <;>
      simp [funlistV39, psort, assocdV39, la22cstab_lt_four, la22two_h0_lt_four]
  · intro i hk3
    exact absurd hk3 (by norm_num)
  · have key : ∀ r : ℕ, r < 3 →
        ((2 * h0 < funlistV39 [((0, 1), cstab)] (2 * h0) 3 r ((r + 1) % 3) ∨
          2 < funlistV39 [((0, 1), Real.sqrt 8)] 2 3 r ((r + 1) % 3)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, la22two_h0_lt_cstab, la22two_le_sqrt8,
          lt_irrefl] <;> norm_num [h0_eq_p22, cstab_eq_p22]
    have hS : {i | i < 3 ∧ (2 * h0 < funlistV39 [((0, 1), cstab)] (2 * h0) 3 i (i + 1) ∨
        2 < funlistV39 [((0, 1), Real.sqrt 8)] 2 3 i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← la22p2mod_fun pb i (i + 1), ← la22p2mod_fun pa i (i + 1),
        ← Nat.mod_add_mod i 3 1]
      rw [key (i % 3) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    norm_num [Set.ncard_singleton]

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

/-- HOL `is_scs_3T5`: direct `is_scs` verification of the `scs_3T5` funlist
tables (`k = 3, d = 0.103`; slot `(0,1)` carries `2 * h0`, card set `{0}`;
same generator-type caveat as `is_scs_3T1_p22`). -/
theorem is_scs_3T5_p22 : isScsV39 scs3T5 := by
  unfold isScsV39 scs3T5 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0)] 2 3) 3 :=
    la22funlist_periodic2 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), Real.sqrt 8)] (2 * h0) 3) 3 :=
    la22funlist_periodic2 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 3, periodic_empty 3,
    periodic_empty 3, periodic_empty 3, pa, pa, pb, pb, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_,
    fun i => by simp [funlistV39], ?_, ?_, ?_,
    fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    exact ⟨la22funlist_sym _ _ _ i j, la22funlist_sym _ _ _ i j,
      la22funlist_sym _ _ _ i j, la22funlist_sym _ _ _ i j, rfl⟩
  · intro i j
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hz2 : j % 3 < 3 := Nat.mod_lt j (by omega)
    rw [← la22p2mod_fun pa i j, ← la22p2mod_fun pb i j]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [funlistV39, psort, assocdV39, la22two_h0_le_sqrt8, la22two_le_two_h0] <;>
      norm_num [h0_eq_p22]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39, la22two_le_two_h0] <;> norm_num [h0_eq_p22]
  · intro i hk3
    have hz : i % 3 < 3 := Nat.mod_lt i (by omega)
    rw [la22funlist_edge_mod _ _ 3 i (by omega)]
    interval_cases i % 3 <;>
      simp [funlistV39, psort, assocdV39, la22sqrt8_lt_four, la22two_h0_lt_four]
  · intro i hk3
    exact absurd hk3 (by norm_num)
  · have key : ∀ r : ℕ, r < 3 →
        ((2 * h0 < funlistV39 [((0, 1), Real.sqrt 8)] (2 * h0) 3 r ((r + 1) % 3) ∨
          2 < funlistV39 [((0, 1), 2 * h0)] 2 3 r ((r + 1) % 3)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, la22two_h0_lt_sqrt8, la22two_le_two_h0,
          lt_irrefl] <;> norm_num [h0_eq_p22]
    have hS : {i | i < 3 ∧ (2 * h0 < funlistV39 [((0, 1), Real.sqrt 8)] (2 * h0) 3 i
            (i + 1) ∨
        2 < funlistV39 [((0, 1), 2 * h0)] 2 3 i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← la22p2mod_fun pb i (i + 1), ← la22p2mod_fun pa i (i + 1),
        ← Nat.mod_add_mod i 3 1]
      rw [key (i % 3) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    norm_num [Set.ncard_singleton]

/-- HOL `is_scs_3T6` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T6_p22 : isScsV39 scs3T6' := by
  sorry

/-- HOL `is_scs_3T7` (NEEDS the funlist evaluation + card kit of
`is_scs_funlist_basic_p22`). -/
theorem is_scs_3T7_p22 : isScsV39 scs3T7 := by
  sorry

/-- HOL `is_scs_3M1`: direct `is_scs` verification of the `scs_3M1` funlist
tables (`k = 3, d = 0.103`; slot `(0,1)` carries `2 * h0`, card set `{0}`).
Port of the planned LocalAuto20:209 `SCS_3M1_IS_SCS` twin via the private
funlist kit (LA20 imports LA22, so the twin cannot be cited directly). -/
theorem is_scs_3M1_p22 : isScsV39 scs3M1 := by
  unfold isScsV39 scs3M1 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0)] 2 3) 3 :=
    la22funlist_periodic2 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), cstab)] (2 * h0) 3) 3 :=
    la22funlist_periodic2 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 3, periodic_empty 3,
    periodic_empty 3, periodic_empty 3, pa, pa, pb, pb, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_,
    fun i => by simp [funlistV39], ?_, ?_, ?_,
    fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    exact ⟨la22funlist_sym _ _ _ i j, la22funlist_sym _ _ _ i j,
      la22funlist_sym _ _ _ i j, la22funlist_sym _ _ _ i j, rfl⟩
  · intro i j
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hz2 : j % 3 < 3 := Nat.mod_lt j (by omega)
    rw [← la22p2mod_fun pa i j, ← la22p2mod_fun pb i j]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [funlistV39, psort, assocdV39, la22two_h0_le_cstab, la22two_le_two_h0] <;>
      norm_num [h0_eq_p22]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39, la22two_le_two_h0] <;> norm_num [h0_eq_p22]
  · intro i hk3
    have hz : i % 3 < 3 := Nat.mod_lt i (by omega)
    rw [la22funlist_edge_mod _ _ 3 i (by omega)]
    interval_cases i % 3 <;>
      simp [funlistV39, psort, assocdV39, la22cstab_lt_four, la22two_h0_lt_four]
  · intro i hk3
    exact absurd hk3 (by norm_num)
  · have key : ∀ r : ℕ, r < 3 →
        ((2 * h0 < funlistV39 [((0, 1), cstab)] (2 * h0) 3 r ((r + 1) % 3) ∨
          2 < funlistV39 [((0, 1), 2 * h0)] 2 3 r ((r + 1) % 3)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, la22two_h0_lt_cstab, la22two_le_two_h0,
          lt_irrefl] <;> norm_num [h0_eq_p22, cstab_eq_p22]
    have hS : {i | i < 3 ∧ (2 * h0 < funlistV39 [((0, 1), cstab)] (2 * h0) 3 i (i + 1) ∨
        2 < funlistV39 [((0, 1), 2 * h0)] 2 3 i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← la22p2mod_fun pb i (i + 1), ← la22p2mod_fun pa i (i + 1),
        ← Nat.mod_add_mod i 3 1]
      rw [key (i % 3) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    norm_num [Set.ncard_singleton]

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
  refine ⟨fun x hx => absurd hx (by simp), ?_⟩
  refine Or.inl fun s' hs' => ?_
  rw [Set.mem_singleton_iff] at hs'
  subst hs'
  by_contra hne
  obtain ⟨vv, hvv⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- keep `BBindexV39 = BBindexMinV39` opaque: unfolding it to
  -- `encard-match = choice-projection` breaks dependent case analysis;
  -- projections instead of rcases so the contaminated equation is never cleared
  simp only [MMsV39, Set.mem_setOf_eq] at hvv
  have hp2 := hvv.1
  simp only [BBprime2V39, Set.mem_setOf_eq] at hp2
  have hbp := hp2.1
  simp only [BBprimeV39, Set.mem_setOf_eq] at hbp
  linarith [h vv hbp.1, hbp.2.2]

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

/-
LocalAuto19 — port of `scripts/local/pent_hex.hl` (Flyspeck "Terminal Pent
and Hex cases", T. Hales 2013; 3187 lines, 0 defs + 81 theorems), skeleton-
first pass.

The chapter closes the terminal pentagon/hexagon case split of the Local Fan
chapter: every conclusion consumes the nonlinear anchor
`main_nonlinear_terminal_v11` (carried here by `mainNonlinearTerminalV11_p18`,
the LocalAuto18 twin of LocalAnchors' anchor — LocalAnchors itself is not
importable on this side, see ENCODING), and most of the heavy theorems
additionally consume single inequalities of the nonlinear database
(`Terminal.get_main_nonlinear "..."`); those are marked NEEDS-DB and `sorry`.

FILE MAP
  Section 0 (`_p19` definitional payload, verbatim twins with NEEDS markers):
    `yOfX_p19`, `deltaX1_p19`, `muY_p19`, `mu6X_p19`, `flatTerm_p19`,
    `flatTermX_p19`, `taudP19`, the taum kit `solY_p19`/`lyP19`/`const1P19`/
    `lnazimP19`/`taumP19`, the anchors `taumX_p19`/`tauResidualX_p19`
    (EXTERNAL-ANCHOR stubs; bodies live in the unported tau_x kit of
    nonlin_def.hl), the slot-deltas `delta126x_p19`/`delta234x_p19`/
    `delta135x_p19`, the quadratic kit `abcOfQuadratic_p19`/
    `quadraticRootPlus_p19`/`edge2FlatDX1_p19`, the x-level composites
    `mud126xV1_p19`/`mud135xV1_p19`/`mud234xV1_p19`, `mudLs126x_p19`/
    `mudLs135x_p19`/`mudLs234x_p19`, `flatTerm2_126x_p19`/`flatTerm2_135x_p19`/
    `flatTerm2_234x_p19`, `eulerAx_p19`, the derivative numerators
    `taudD1numX_p19`/`taudD2numX_p19`, the inequality shell `ineqP19`
    (HOL `Sphere.ineq`), and the r755 database shell `r755D234_p19`/
    `r755D126_p19`/`r755D135_p19`/`r755C234_p19`/`r755C126_p19`/`r755C135_p19`/
    `r755Body_p19`/`r755Ineq_p19` (`mk_ineq_hex`/`g755_`; the database itself
    is EXTERNAL-ANCHOR on the nonlinear chapter).
  Sections A-F: the 81 theorems in source order —
    A  algebra/numerics: `sqrt_secant_approx` .. `taud_minimizer_terminal_hex_cases`
    B  derivatives: `derived_form_F` .. `derived_form_taud_D3`,
       `SECOND_DERIVATIVE_TEST`, continuity/topology kit
    C  minimizer case splits and db lemmas
    D  quadratic/edge kit: `quadratic_root_*`, `edge2_flatD_*`, `delta_*`
    E  terminal pentagon conclusions `terminal_pent_*`, `taud_sqrt20`
    F  symmetry kit, `nonfunctional_*` transfer lemmas, `ineq_sym_*`,
       wlog lemmas `REAL_WLOG_*`, the r755 transfer lemmas `r755_ikj`/
       `r755_jik`, and the hex reductions `terminal_hex_*`.

ENCODING NOTES
  - Import discipline: this file sits on the LocalAuto1/`PackingAuto18` side
    of the fatal `atn2PA18` duplication (LocalAuto2/`PackingAuto20`, and
    LocalAuto9/11/16 which import LocalAuto2, must NOT be imported next to
    LocalAuto1). Everything needed from those lanes is carried as a verbatim
    `_p19` twin with a NEEDS merge marker. `deltaY_p18`/`dihY_p18`/
    `mainNonlinearTerminalV11_p18` are imported from LocalAuto18 (they are
    already canonical on this side); `h0`/`sol0` from PackingAuto2; `deltaXPA18`,
    `derivedForm`, `cstab` from PackingAuto18/LocalAuto1.
  - HOL `real^3`-free file: everything is real-arithmetic over the six
    variables `y1..y6` (the pent/hex terminal box).
  - HOL `ineq [lo,v,hi; ...] c` = `ineqP19 [(lo,v,hi),...] c` (recursive box
    implication, `Sphere.ineq`); `real_interval [a,b]` = `Set.Icc a b`,
    `real_interval (a,b)` = `Set.Ioo a b`; `real_open`/`real_closed` =
    `IsOpen`/`IsClosed`; `f real_continuous_on s` = `ContinuousOn f s`;
    `f real_continuous atreal z` = `ContinuousAt f z`; `derived_form` =
    `derivedForm` (LocalAuto1: `T → HasDerivWithinAt f f' s x`).
  - The 6-ary operator calculus of nonlin_def.hl (`uni`/`mul6`/`compose6`/
    `constant6`/`proj_*`/`dummy6`) is collapsed: composites are stated at the
    x-level directly, so `y_of_x (mud_126_x_v1 a b c)` becomes
    `yOfX_p19 (mud126xV1_p19 a b c)` with an identical body.
  - `quadratic_root_plus (a,b,c)` = `quadraticRootPlus_p19 a b c`;
    `abc_of_quadratic f` = `abcOfQuadratic_p19 f`.
  - `taum_sym_cases2_p19` needs the dihedral-angle symmetry kit of sphere.hl
    (`dih_y` symmetries via `atn2PA18`), which is not yet ported on this side:
    sorry + NEEDS. The r755 transfers `r755_ikj_p19`/`r755_jik_p19` consume
    it (their proofs are otherwise mechanical slot transports).
  - Theorems marked NEEDS-DB consume single conjuncts of the opaque
    `main_nonlinear_terminal_v11` conjunction (`Terminal.get_main_nonlinear`
    entries "3078028960", "5546286427", "7550003505 ..." etc.); they are
    stated faithfully and `sorry`'d.
-/

import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto4
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: definitional payload (`_p19` twins) -/

/-- HOL `y_of_x` (sphere.hl:538): evaluate an x-level function at squared
lengths. Verbatim twin of LocalAuto11's `yOfX_p11` (wrong atn2PA18 side). NEEDS:
merge. -/
def yOfX_p19 (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  f (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta_x1` (nonlin_def.hl:418): `∂delta_x/∂x1`. Verbatim twin of
PackingAuto20's `deltaX1f`. NEEDS: merge. -/
def deltaX1_p19 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x4 + x2 * x5 - x3 * x5 - x2 * x6 + x3 * x6 +
    x4 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `mu_y` (nonlin_def.hl:401, sphere.hl). No Lean twin on this side. -/
def muY_p19 (y1 y2 y3 : ℝ) : ℝ :=
  0.012 + 0.07 * (2.52 - y1) + 0.01 * (2.52 * 2 - y2 - y3)

/-- HOL `mu6_x` (nonlin_def.hl:403): the 6-ary `mu_y ∘ proj_y1..3`; the
`dummy6` slots are irrelevant. -/
noncomputable def mu6X_p19 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := muY_p19 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)

/-- HOL `flat_term` (sphere.hl:527, nonlin_def.hl:399). -/
noncomputable def flatTerm_p19 (y : ℝ) : ℝ := sol0 * (y - 2 * h0) / (2 * h0 - 2)

/-- HOL `flat_term_x` (sphere.hl:825). -/
noncomputable def flatTermX_p19 (x : ℝ) : ℝ := flatTerm_p19 (Real.sqrt x)

/-- HOL `taud` (nonlin_def.hl:406). -/
noncomputable def taudP19 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  flatTerm_p19 y1 + Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) * muY_p19 y1 y2 y3

/-- HOL `sol_y` (sphere.hl:185): spherical excess. Verbatim twin of
PackingAuto20/21's `solY` via `dihY_p18`. NEEDS: merge. -/
noncomputable def solY_p19 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihY_p18 y1 y2 y3 y4 y5 y6 + dihY_p18 y2 y3 y1 y5 y6 y4 +
    dihY_p18 y3 y1 y2 y6 y4 y5 - Real.pi

/-- HOL `ly` (sphere.hl:199): `interp 2 1 2.52 0 y`. -/
noncomputable def lyP19 (y : ℝ) : ℝ := 1 + (y - 2) * (0 - 1) / (2.52 - 2)

/-- HOL `const1` (sphere.hl:197). Twin of LocalAuto2's `const1_p2` (wrong
atn2PA18 side). NEEDS: merge. -/
noncomputable def const1P19 : ℝ := solY_p19 2 2 2 2 2 2 / Real.pi

/-- HOL `lnazim` (sphere.hl:214). -/
noncomputable def lnazimP19 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  lyP19 y1 * dihY_p18 y1 y2 y3 y4 y5 y6

/-- HOL `taum` (sphere.hl:215). -/
noncomputable def taumP19 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  solY_p19 y1 y2 y3 y4 y5 y6 * (1 + const1P19) -
    const1P19 * (lnazimP19 y1 y2 y3 y4 y5 y6 +
      lnazimP19 y2 y3 y1 y5 y6 y4 + lnazimP19 y3 y1 y2 y6 y4 y5)

/-- EXTERNAL-ANCHOR: HOL `taum_x` (sphere.hl:827) = `rhazim_x`-sum minus
`(1+const1)*pi`. The `rhazim_x_div_sqrtdelta_posbranch` kit of nonlin_def.hl
is unported; carried as a stub with the honest signature. NEEDS: tau_x kit. -/
noncomputable def taumX_p19 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ _ _ _ => (0 : ℝ)

/-- EXTERNAL-ANCHOR: HOL `tau_residual_x` (nonlin_def.hl:181), the sum of the
three rotated `rhazim_x_div_sqrtdelta_posbranch`. Stub. NEEDS: tau_x kit. -/
noncomputable def tauResidualX_p19 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun _ _ _ _ _ _ => (0 : ℝ)

/-- HOL `delta_126_x` (sphere.hl:844). -/
def delta126x_p19 (s3 s4 s5 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := deltaXPA18 x1 x2 s3 s4 s5 x6

/-- HOL `delta_234_x` (sphere.hl:848). -/
def delta234x_p19 (s1 s5 s6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := deltaXPA18 s1 x2 x3 x4 s5 s6

/-- HOL `delta_135_x` (sphere.hl:852). -/
def delta135x_p19 (s2 s4 s6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := deltaXPA18 x1 s2 x3 s4 x5 s6

/-- HOL `abc_of_quadratic` (sphere.hl:59): coefficients of the quadratic
interpolant through `f` at `0, ±1`. -/
noncomputable def abcOfQuadratic_p19 (f : ℝ → ℝ) : ℝ × ℝ × ℝ :=
  ((f 1 + f (-1)) / 2 - f 0, (f 1 - f (-1)) / 2, f 0)

/-- HOL `quadratic_root_plus` (sphere.hl:67): the `+sqrt` root. -/
noncomputable def quadraticRootPlus_p19 (a b c : ℝ) : ℝ :=
  (-b + Real.sqrt (b * b - 4 * a * c)) / (2 * a)

/-- HOL `edge2_flatD_x1` (nonlin_def.hl:473). -/
noncomputable def edge2FlatDX1_p19 (d x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let abc := abcOfQuadratic_p19 fun x1 => d - deltaXPA18 x1 x2 x3 x4 x5 x6
  quadraticRootPlus_p19 abc.1 abc.2.1 abc.2.2

/-- HOL `mud_126_x_v1` (nonlin_def.hl:496), x-level composite. -/
noncomputable def mud126xV1_p19 (a b c : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    muY_p19 a (Real.sqrt x1) (Real.sqrt x2) *
      Real.sqrt (delta126x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6)

/-- HOL `mud_135_x_v1` (nonlin_def.hl:491), x-level composite. -/
noncomputable def mud135xV1_p19 (a b c : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    muY_p19 a (Real.sqrt x1) (Real.sqrt x3) *
      Real.sqrt (delta135x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6)

/-- HOL `mud_234_x_v1` (nonlin_def.hl:501), x-level composite. -/
noncomputable def mud234xV1_p19 (a b c : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    muY_p19 a (Real.sqrt x2) (Real.sqrt x3) *
      Real.sqrt (delta234x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6)

/-- HOL `mudLs_126_x` (nonlin_def.hl:511), x-level composite. -/
noncomputable def mudLs126x_p19 (d1s d2s a b c : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    mu6X_p19 (a * a) x1 x2 0 0 0 *
      ((1 / (d1s + d2s)) *
          (delta126x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)

/-- HOL `mudLs_135_x` (nonlin_def.hl:516), x-level composite. -/
noncomputable def mudLs135x_p19 (d1s d2s a b c : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    mu6X_p19 (a * a) x1 x3 0 0 0 *
      ((1 / (d1s + d2s)) *
          (delta135x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)

/-- HOL `mudLs_234_x` (nonlin_def.hl:506), x-level composite. -/
noncomputable def mudLs234x_p19 (d1s d2s a b c : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    mu6X_p19 (a * a) x2 x3 0 0 0 *
      ((1 / (d1s + d2s)) *
          (delta234x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)

/-- HOL `flat_term2_126_x` (nonlin_def.hl:486), x-level composite. -/
noncomputable def flatTerm2_126x_p19 (d a b : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x1 x2 x6 a b))

/-- HOL `flat_term2_135_x` (nonlin_def.hl:489), x-level composite. -/
noncomputable def flatTerm2_135x_p19 (d a b : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x1 x3 x5 a b))

/-- HOL `flat_term2_234_x` (nonlin_def.hl:492), x-level composite. -/
noncomputable def flatTerm2_234x_p19 (d a b : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun x1 x2 x3 x4 x5 x6 =>
    flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x2 x3 x4 a b))

/-- HOL `eulerA_x` (sphere.hl:831). -/
noncomputable def eulerAx_p19 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt x1 * Real.sqrt x2 * Real.sqrt x3 +
    Real.sqrt x1 * (x2 + x3 - x4) / 2 +
    Real.sqrt x2 * (x1 + x3 - x5) / 2 +
    Real.sqrt x3 * (x1 + x2 - x6) / 2

/-- HOL `taud_D1_num_x` (nonlin_def.hl:457), x-level
(`delta' = delta_x1·2·proj_y1`, `ft' = sol0/(2*h0-2)`). -/
noncomputable def taudD1numX_p19 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -0.07 * deltaXPA18 x1 x2 x3 x4 x5 x6 +
    (1 / 2) * mu6X_p19 x1 x2 x3 x4 x5 x6 *
      (deltaX1_p19 x1 x2 x3 x4 x5 x6 * 2 * Real.sqrt x1) +
    (sol0 / (2 * h0 - 2)) * Real.sqrt (deltaXPA18 x1 x2 x3 x4 x5 x6)

/-- HOL `taud_D2_num_x` (nonlin_def.hl:465), x-level
(`delta'' = -8·proj_x1·proj_x4 + 2·delta_x1`). -/
noncomputable def taudD2numX_p19 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let d : ℝ := deltaXPA18 x1 x2 x3 x4 x5 x6
  let delta' : ℝ := deltaX1_p19 x1 x2 x3 x4 x5 x6 * 2 * Real.sqrt x1
  let delta'' : ℝ := -8 * x1 * x4 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * 2
  let mu : ℝ := mu6X_p19 x1 x2 x3 x4 x5 x6
  (-0.07 * d * delta' - (1 / 4) * mu * (delta' * delta') +
    (1 / 2) * mu * d * delta'')

/-- HOL `ineq` (sphere.hl:27): the box-implication shell. -/
def ineqP19 : List (ℝ × ℝ × ℝ) → Prop → Prop
  | [], c => c
  | (lo, v, hi) :: rest, c => lo ≤ v ∧ v ≤ hi → ineqP19 rest c

/-- The r755 d-slot selector (`mk_ineq_hex`'s first `nth` list, 234 copy). -/
noncomputable def r755D234_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  match i with
  | 0 => yOfX_p19 (flatTerm2_234x_p19 0 4 4) y1 y2 y3 y4 y5 y6
  | 1 => 0
  | 2 => yOfX_p19 (mud234xV1_p19 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
  | 3 => yOfX_p19 (mudLs234x_p19 4 10 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
  | _ => 0 - sol0

/-- The r755 d-slot selector, 126 copy. -/
noncomputable def r755D126_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  match i with
  | 0 => yOfX_p19 (flatTerm2_126x_p19 0 4 4) y1 y2 y3 y4 y5 y6
  | 1 => 0
  | 2 => yOfX_p19 (mud126xV1_p19 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
  | 3 => yOfX_p19 (mudLs126x_p19 4 10 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
  | _ => 0 - sol0

/-- The r755 d-slot selector, 135 copy. -/
noncomputable def r755D135_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  match i with
  | 0 => yOfX_p19 (flatTerm2_135x_p19 0 4 4) y1 y2 y3 y4 y5 y6
  | 1 => 0
  | 2 => yOfX_p19 (mud135xV1_p19 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
  | 3 => yOfX_p19 (mudLs135x_p19 4 10 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
  | _ => 0 - sol0

/-- The r755 c-slot (range guard) selector, 234 copy (clean form:
`y_of_x (delta_234_x ...)` unfolds to `delta_y 2 y2 y3 y4 2 2`). -/
noncomputable def r755C234_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  match i with
  | 0 => deltaY_p18 2 y2 y3 y4 2 2 < 0 ∨ deltaY_p18 2.52 y2 y3 y4 2 2 > 0
  | 1 => False
  | 2 => deltaY_p18 2 y2 y3 y4 2 2 < 100
  | 3 => deltaY_p18 2 y2 y3 y4 2 2 < 16 ∨ deltaY_p18 2 y2 y3 y4 2 2 > 100
  | _ => deltaY_p18 2 y2 y3 y4 2 2 < 0 ∨ deltaY_p18 2 y2 y3 y4 2 2 > 16

/-- The r755 c-slot selector, 126 copy. -/
noncomputable def r755C126_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  match i with
  | 0 => deltaY_p18 2 y1 y2 y6 2 2 < 0 ∨ deltaY_p18 2.52 y1 y2 y6 2 2 > 0
  | 1 => False
  | 2 => deltaY_p18 2 y1 y2 y6 2 2 < 100
  | 3 => deltaY_p18 2 y1 y2 y6 2 2 < 16 ∨ deltaY_p18 2 y1 y2 y6 2 2 > 100
  | _ => deltaY_p18 2 y1 y2 y6 2 2 < 0 ∨ deltaY_p18 2 y1 y2 y6 2 2 > 16

/-- The r755 c-slot selector, 135 copy. -/
noncomputable def r755C135_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  match i with
  | 0 => deltaY_p18 2 y1 y3 y5 2 2 < 0 ∨ deltaY_p18 2.52 y1 y3 y5 2 2 > 0
  | 1 => False
  | 2 => deltaY_p18 2 y1 y3 y5 2 2 < 100
  | 3 => deltaY_p18 2 y1 y3 y5 2 2 < 16 ∨ deltaY_p18 2 y1 y3 y5 2 2 > 100
  | _ => deltaY_p18 2 y1 y3 y5 2 2 < 0 ∨ deltaY_p18 2 y1 y3 y5 2 2 > 16

/-- The `template_hex` body of `mk_ineq_hex` with the `s45`/`s56` flag
disjuncts rendered as explicit props (the flags `i234 = i126`, `i126 = i135`
are resolved by the database instantiator; `g755_` sets them to `False`). -/
noncomputable def r755Body_p19 (i234 i126 i135 : ℕ) (f1 f2 : ℝ) (b1 b2 s45 s56 : Prop)
    (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  f1 + (taumP19 y1 y2 y3 y4 y5 y6 + r755D234_p19 i234 y1 y2 y3 y4 y5 y6 +
        r755D126_p19 i126 y1 y2 y3 y4 y5 y6 + r755D135_p19 i135 y1 y2 y3 y4 y5 y6) + f2 >
      0.712 ∨
    yOfX_p19 eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0 ∨
    r755C234_p19 i234 y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 i126 y1 y2 y3 y4 y5 y6 ∨
    r755C135_p19 i135 y1 y2 y3 y4 y5 y6 ∨ s45 ∨ s56 ∨ b2

/-- One entry of the r755 database (`get_ineq' (i,j,k)` = `clean_ineq` of
`Terminal.get_main_nonlinear "7550003505 i j k"`). EXTERNAL-ANCHOR: the
entries are conjuncts of the nonlinear chapter's database. -/
noncomputable def r755Ineq_p19 (i234 i126 i135 : ℕ) (f1 f2 : ℝ) (b1 b2 s45 s56 : Prop) :
    Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ,
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915)]
      (r755Body_p19 i234 i126 i135 f1 f2 b1 b2 s45 s56 y1 y2 y3 y4 y5 y6)

/-! ## Numeric anchors -/

/-- HOL `Flyspeck_constants.bounds` component: `0 < sol0` (sol0 = the
regular-tetrahedron solid angle `3·arccos(1/3) − π`). -/
theorem sol0Pos_p19 : 0 < sol0 := by
  have h2 : (1 / 2 : ℝ) = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
  have h3 : Real.arccos (1 / 2) = Real.pi / 3 := by
    rw [h2]; exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h4 : Real.arccos (1 / 2) < Real.arccos (1 / 3) :=
    Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have h5 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  linarith

/-- HOL `Flyspeck_constants.bounds` components `#0.551285 < sol0 < #0.551286`
(used via `mu_y_ft_combine2`). NEEDS: rational `arccos(1/3)` bounds
(`π`-interval arithmetic); Flyspeck proves this inside `Flyspeck_constants`. -/
theorem sol0Bounds_p19 : 0.551285 < sol0 ∧ sol0 < 0.551286 := by
  constructor
  · sorry
  · sorry

/-- Helper: `h0 = 1.26` (sphere.hl:203) and consequences used throughout. -/
theorem h0_num_p19 : h0 = 1.26 ∧ 2 * h0 = 2.52 ∧ 2 * h0 - 2 = 0.52 :=
  ⟨rfl, by norm_num [h0], by norm_num [h0]⟩


/-! ## Section A: algebra, numerics, and the first case analysis -/

/-- HOL `sqrt_secant_approx` (pent_hex.hl:21). -/
theorem sqrt_secant_approx_p19 {x1 x2 x : ℝ} (ha : 0 ≤ x1) (hb : x1 ≤ x) (hc : x ≤ x2) :
    (1 / (Real.sqrt x1 + Real.sqrt x2)) * (x - x1) + Real.sqrt x1 ≤ Real.sqrt x := by
  have hx0 : 0 ≤ x := le_trans ha hb
  have hx20 : 0 ≤ x2 := le_trans hx0 hc
  rcases lt_or_eq_of_le hx20 with hp2 | hz
  · have hmono1 : Real.sqrt x1 ≤ Real.sqrt x := Real.sqrt_le_sqrt hb
    have hmono2 : Real.sqrt x ≤ Real.sqrt x2 := Real.sqrt_le_sqrt hc
    have hab : 0 < Real.sqrt x1 + Real.sqrt x2 :=
      add_pos_of_nonneg_of_pos (Real.sqrt_nonneg x1) (Real.sqrt_pos.mpr hp2)
    have hkey : x - x1 ≤ (Real.sqrt x - Real.sqrt x1) * (Real.sqrt x1 + Real.sqrt x2) := by
      have e1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
      have e2 : Real.sqrt x1 * Real.sqrt x1 = x1 := Real.mul_self_sqrt ha
      have h1 : 0 ≤ Real.sqrt x - Real.sqrt x1 := sub_nonneg.mpr hmono1
      have hdiff : x - x1 = Real.sqrt x * Real.sqrt x - Real.sqrt x1 * Real.sqrt x1 := by
        rw [e1, e2]
      calc x - x1 = (Real.sqrt x - Real.sqrt x1) * (Real.sqrt x + Real.sqrt x1) := by
            rw [hdiff]; ring
        _ ≤ (Real.sqrt x - Real.sqrt x1) * (Real.sqrt x1 + Real.sqrt x2) :=
            mul_le_mul_of_nonneg_left (by linarith) h1
    have hstep : (1 / (Real.sqrt x1 + Real.sqrt x2)) * (x - x1)
        ≤ Real.sqrt x - Real.sqrt x1 := by
      calc (1 / (Real.sqrt x1 + Real.sqrt x2)) * (x - x1)
          ≤ (1 / (Real.sqrt x1 + Real.sqrt x2)) *
              ((Real.sqrt x - Real.sqrt x1) * (Real.sqrt x1 + Real.sqrt x2)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = Real.sqrt x - Real.sqrt x1 := by
            field_simp
    linarith
  · subst hz
    have hxz : x = 0 := le_antisymm hc hx0
    have hx1z : x1 = 0 := by
      have : x1 ≤ x := hb
      rw [hxz] at this
      exact le_antisymm this ha
    subst hxz
    subst hx1z
    simp

/-- HOL `flat_term_neg` (pent_hex.hl:63). -/
theorem flat_term_neg_p19 (y : ℝ) (hy : y ≤ 2 * h0) : flatTerm_p19 y ≤ 0 := by
  have hp := sol0Pos_p19
  rw [flatTerm_p19, div_le_iff₀ (by linarith [h0_num_p19.2.2])]
  nlinarith [hp, hy]

/-- HOL `mu_y_ft_combine` (pent_hex.hl:79). -/
theorem mu_y_ft_combine_p19 (y y2 y3 sd : ℝ) :
    muY_p19 y y2 y3 * sd + flatTerm_p19 y
      = muY_p19 (2 * h0) y2 y3 * sd +
        (1 - (2 * h0 - 2) * 0.07 * sd / sol0) * flatTerm_p19 y := by
  have hb := h0_num_p19
  have hp : sol0 ≠ 0 := ne_of_gt sol0Pos_p19
  have hd : (2 * h0 - 2 : ℝ) ≠ 0 := by linarith
  have h52 : (2 * h0 - 2 : ℝ) = 0.52 := h0_num_p19.2.2
  rw [muY_p19, muY_p19, flatTerm_p19, h52]
  field_simp
  ring

/-- HOL `mu_y_ft_combine2` (pent_hex.hl:95). -/
theorem mu_y_ft_combine2_p19 (y y2 y3 : ℝ) (hy : y ≤ 2 * h0) :
    muY_p19 (2 * h0) y2 y3 * Real.sqrt 20 + 0.705 * flatTerm_p19 y ≤
      muY_p19 y y2 y3 * Real.sqrt 20 + flatTerm_p19 y := by
  obtain ⟨hslo, hshi⟩ := sol0Bounds_p19
  have hsqrt : (4.47 : ℝ) ≤ Real.sqrt 20 := by
    have h2 : (4.47 : ℝ) ^ 2 ≤ 20 := by norm_num
    have h3 : Real.sqrt (4.47 ^ 2) ≤ Real.sqrt 20 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (by norm_num)] at h3
  have hftle := flat_term_neg_p19 y hy
  rw [mu_y_ft_combine_p19]
  have hc : 0.295 ≤ (2 * h0 - 2) * 0.07 * Real.sqrt 20 / sol0 := by
    have h52 : (2 * h0 - 2 : ℝ) = 0.52 := h0_num_p19.2.2
    rw [h52, le_div_iff₀ sol0Pos_p19]
    have e1 : (0.52 : ℝ) * 0.07 * 4.47 ≥ 0.295 * 0.551286 := by norm_num
    calc (0.52 : ℝ) * 0.07 * Real.sqrt 20
        ≥ 0.0364 * 4.47 := by nlinarith [hsqrt]
      _ = 0.52 * 0.07 * 4.47 := by norm_num
      _ ≥ 0.295 * 0.551286 := e1
      _ ≥ 0.295 * sol0 := by nlinarith [hshi]
  have hrest : 0.705 * flatTerm_p19 y
      ≤ (1 - (2 * h0 - 2) * 0.07 * Real.sqrt 20 / sol0) * flatTerm_p19 y := by
    have h0le : 0 ≤ sol0 := le_of_lt sol0Pos_p19
    nlinarith [hc, hftle, sol0Pos_p19]
  linarith

/-- HOL `nonfunctional_mu6_x_y` (pent_hex.hl:126). -/
theorem nonfunctional_mu6_x_y_p19 (x1 x2 x3 a b c : ℝ) :
    mu6X_p19 x1 x2 x3 a b c = muY_p19 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3) := rfl

/-- HOL `tau_x_tau_residual_x_general` (pent_hex.hl:136). NEEDS: the tau_x
kit `rhazim_x_div_sqrtdelta_posbranch` (unported); carried via the
`taumX_p19`/`tauResidualX_p19` anchors. -/
theorem tau_x_tau_residual_x_general_p19 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 4 ≤ x1) (h2 : Real.sqrt x1 ≤ 2 * h0) (h3 : 0 < x1) (h4 : 0 < x2)
    (h5 : 0 < x3) (h6 : 0 < x4) (h7 : 0 < x5) (h8 : 0 < x6)
    (h9 : deltaX4_p18 x1 x2 x3 x4 x5 x6 < 0)
    (h10 : 0 < deltaX4_p18 x2 x3 x1 x5 x6 x4)
    (h11 : 0 < deltaX4_p18 x3 x1 x2 x6 x4 x5)
    (h12 : 0 ≤ deltaXPA18 x1 x2 x3 x4 x5 x6) :
    taumX_p19 x1 x2 x3 x4 x5 x6
      = Real.sqrt (deltaXPA18 x1 x2 x3 x4 x5 x6) * tauResidualX_p19 x1 x2 x3 x4 x5 x6
        + flatTermX_p19 x1 := by
  sorry

/-- HOL `OWZLKVY4` (pent_hex.hl:216). NEEDS-DB: consumes a nonlinear-database
conjunct (terminal `taud ≤ taum` estimate) beyond the anchor. -/
theorem OWZLKVY4_p19 (h : mainNonlinearTerminalV11_p18) (y1 y2 y3 y4 y5 y6 : ℝ)
    (b1 : 2 ≤ y1) (b2 : y1 ≤ 2 * h0) (b3 : 2 ≤ y2) (b4 : y2 ≤ 2 * h0)
    (b5 : 2 ≤ y3) (b6 : y3 ≤ 2 * h0) (b7 : cstab ≤ y4) (b8 : y4 ≤ 3.915)
    (b9 : y5 = 2) (b10 : y6 = 2) (hd : 0 ≤ deltaY_p18 y1 y2 y3 y4 y5 y6) :
    taudP19 y1 y2 y3 y4 y5 y6 ≤ taumP19 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `OPEN_REAL_INTERVAL_SING` (pent_hex.hl:290). -/
theorem OPEN_REAL_INTERVAL_SING_p19 (a b c : ℝ) : Set.Ioo a b ≠ {c} := by
  intro h
  by_cases hab : a < b
  · have p1 : (a + (a + b) / 2) / 2 ∈ (Set.Ioo a b : Set ℝ) := ⟨by linarith, by linarith⟩
    have p2 : ((a + b) / 2 + b) / 2 ∈ (Set.Ioo a b : Set ℝ) := ⟨by linarith, by linarith⟩
    have e1 : (a + (a + b) / 2) / 2 = c := by
      rw [h] at p1; exact Set.mem_singleton_iff.mp p1
    have e2 : ((a + b) / 2 + b) / 2 = c := by
      rw [h] at p2; exact Set.mem_singleton_iff.mp p2
    linarith
  · have hc : c ∈ (Set.Ioo a b : Set ℝ) := by rw [h]; exact rfl
    have hba : b ≤ a := le_of_not_gt hab
    exact absurd (lt_trans hc.1 (lt_of_lt_of_le hc.2 hba)) (lt_irrefl a)

/-- HOL `derived_form_F` (pent_hex.hl:318): the antecedent `False` is vacuous. -/
theorem derived_form_F_p19 (f : ℝ → ℝ) (f' x : ℝ) (s : Set ℝ) :
    derivedForm False f f' x s := fun hn => absurd hn (by simp)

/-- Derivative of `q ↦ delta_y q y2 y3 y4 y5 y6`: the `delta_x1` chain rule. -/
theorem deltaY_hasDerivAt_p19 (t y2 y3 y4 y5 y6 : ℝ) :
    HasDerivAt (fun q => deltaY_p18 q y2 y3 y4 y5 y6)
      (2 * t * deltaX1_p19 (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) t := by
  set K0 : ℝ := (y4 * y4) * (y2 * y2 + y3 * y3 - y4 * y4 + y5 * y5 + y6 * y6)
      + (y2 * y2) * (y5 * y5) + (y3 * y3) * (y6 * y6)
      - (y3 * y3) * (y5 * y5) - (y2 * y2) * (y6 * y6) with hK0def
  set C0 : ℝ := (y2 * y2) * (y5 * y5) * (-(y2 * y2) + y3 * y3 + y4 * y4 - y5 * y5 + y6 * y6)
      + (y3 * y3) * (y6 * y6) * ((y2 * y2) - y3 * y3 + y4 * y4 + y5 * y5 - y6 * y6)
      - (y2 * y2) * (y3 * y3) * (y4 * y4) - (y4 * y4) * (y5 * y5) * (y6 * y6) with hC0def
  have hg : HasDerivAt (fun w : ℝ => w * w) (2 * t) t :=
    HasDerivAt.congr_deriv ((hasDerivAt_id t).mul (hasDerivAt_id t))
      (by simp [two_mul])
  have hsq : HasDerivAt (fun w : ℝ => (w * w) * (w * w)) (4 * t * t * t) t :=
    HasDerivAt.congr_deriv (hg.mul hg) (by ring)
  have hlin : HasDerivAt (fun w : ℝ => K0 * (w * w)) (K0 * (2 * t)) t := hg.const_mul K0
  have hres : HasDerivAt
      (fun w : ℝ => -(y4 * y4) * ((w * w) * (w * w)) + K0 * (w * w) + C0)
      (-(y4 * y4) * (4 * t * t * t) + K0 * (2 * t) + 0) t :=
    ((hsq.const_mul (-(y4 * y4))).add hlin).add (hasDerivAt_const (c := C0) t)
  have hcongr : (fun w => deltaY_p18 w y2 y3 y4 y5 y6)
      = fun w => -(y4 * y4) * ((w * w) * (w * w)) + K0 * (w * w) + C0 := by
    funext w
    show deltaXPA18 (w * w) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) = _
    unfold deltaXPA18
    ring
  have hd1 : deltaX1_p19 (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
      = -2 * (y4 * y4) * (t * t) + K0 := by
    unfold deltaX1_p19
    rw [hK0def]
    ring
  rw [hcongr, hd1]
  exact HasDerivAt.congr_deriv hres (by ring)

/-- HOL `derived_form_delta_y` (pent_hex.hl:326). -/
theorem derived_form_delta_y_p19 (y1 y2 y3 y4 y5 y6 : ℝ) :
    derivedForm True (fun q => deltaY_p18 q y2 y3 y4 y5 y6)
      (yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6 * 2 * y1) y1 Set.univ := by
  intro _
  exact HasDerivAt.hasDerivWithinAt
    (HasDerivAt.congr_deriv (deltaY_hasDerivAt_p19 y1 y2 y3 y4 y5 y6)
      (by simp only [yOfX_p19]; ring))

/-- HOL `deriv_form_taud` (pent_hex.hl:341). -/
theorem deriv_form_taud_p19 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY_p18 y1 y2 y3 y4 y5 y6) :
    derivedForm (0 < deltaY_p18 y1 y2 y3 y4 y5 y6)
      (fun q => taudP19 q y2 y3 y4 y5 y6)
      ((-0.07 * deltaY_p18 y1 y2 y3 y4 y5 y6 +
          muY_p19 y1 y2 y3 * (yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6 * y1) +
          (sol0 / (2 * h0 - 2)) * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)) /
        Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6))
      y1 Set.univ := by
  have hD : deltaY_p18 y1 y2 y3 y4 y5 y6 ≠ 0 := ne_of_gt hd
  have hdelta := deltaY_hasDerivAt_p19 y1 y2 y3 y4 y5 y6
  have hsqrt : HasDerivAt (fun q => Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6))
      (1 / (2 * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)) *
        (2 * y1 * yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6)) y1 :=
    HasDerivAt.comp y1 (Real.hasDerivAt_sqrt hD) hdelta
  have hmu : HasDerivAt (fun q => muY_p19 q y2 y3) (-0.07) y1 := by
    have he : (fun q => muY_p19 q y2 y3)
        = fun q => 0.012 + 0.07 * 2.52 + 0.01 * (2.52 * 2 - y2 - y3) + -0.07 * q := by
      funext q; unfold muY_p19; ring
    rw [he]
    exact HasDerivAt.congr_deriv
      ((hasDerivAt_const y1 (0.012 + 0.07 * 2.52 + 0.01 * (2.52 * 2 - y2 - y3))).add
        ((hasDerivAt_id y1).const_mul (-0.07))) (by ring)
  have hft : HasDerivAt (fun q => flatTerm_p19 q) (sol0 / (2 * h0 - 2)) y1 := by
    have he : (fun q => flatTerm_p19 q)
        = fun q => sol0 / (2 * h0 - 2) * q + (-(sol0 * (2 * h0)) / (2 * h0 - 2)) := by
      funext q; unfold flatTerm_p19; ring
    rw [he]
    exact HasDerivAt.congr_deriv
      (((hasDerivAt_id y1).const_mul (sol0 / (2 * h0 - 2))).add
        (hasDerivAt_const (x := y1)
          (c := -(sol0 * (2 * h0)) / (2 * h0 - 2)))) (by ring)
  intro _
  refine HasDerivAt.hasDerivWithinAt ?_
  have hsum := hft.add (hsqrt.mul hmu)
  have hsum2 : HasDerivAt (fun q => flatTerm_p19 q +
      Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6) * muY_p19 q y2 y3)
      (sol0 / (2 * h0 - 2) +
        (1 / (2 * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)) *
              (2 * y1 * yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6) * muY_p19 y1 y2 y3 +
            Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) * -0.07)) y1 := hsum
  exact HasDerivAt.congr_deriv hsum2 (by
    have hsq : Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)
        = deltaY_p18 y1 y2 y3 y4 y5 y6 := Real.mul_self_sqrt hd.le
    have hsD : Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hd)
    have hs2 : Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) ^ 2
        = deltaY_p18 y1 y2 y3 y4 y5 y6 := Real.sq_sqrt hd.le
    field_simp [hsq, hsD]
    rw [hs2]
    ring)

/-- HOL `derived_form_taud_ALT` (pent_hex.hl:389). -/
theorem derived_form_taud_ALT_p19 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY_p18 y1 y2 y3 y4 y5 y6) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3) :
    derivedForm (0 < deltaY_p18 y1 y2 y3 y4 y5 y6 ∧ 0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3)
      (fun q => taudP19 q y2 y3 y4 y5 y6)
      (yOfX_p19 taudD1numX_p19 y1 y2 y3 y4 y5 y6 /
        Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6))
      y1 Set.univ := by
  rintro ⟨hd, -, -, -⟩
  have hbase : (0 < deltaY_p18 y1 y2 y3 y4 y5 y6 ∧ 0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3) →
      HasDerivWithinAt (fun q => taudP19 q y2 y3 y4 y5 y6)
      ((-0.07 * deltaY_p18 y1 y2 y3 y4 y5 y6 +
          muY_p19 y1 y2 y3 * (yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6 * y1) +
          (sol0 / (2 * h0 - 2)) * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)) /
        Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6))
      Set.univ y1 := fun hcon =>
    (deriv_form_taud_p19 y1 y2 y3 y4 y5 y6 hcon.1) hcon.1
  exact HasDerivWithinAt.congr_deriv (hbase ⟨hd, hy1, hy2, hy3⟩) (by
    show ((-0.07 * deltaY_p18 y1 y2 y3 y4 y5 y6 +
        muY_p19 y1 y2 y3 * (yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6 * y1) +
        sol0 / (2 * h0 - 2) * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)) /
      Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6))
      = (yOfX_p19 taudD1numX_p19 y1 y2 y3 y4 y5 y6 /
          Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6))
    have hdy : deltaY_p18 y1 y2 y3 y4 y5 y6
      = deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := rfl
    have hs1 : Real.sqrt (y1 * y1) = y1 := Real.sqrt_mul_self hy1
    have hs2 : Real.sqrt (y2 * y2) = y2 := Real.sqrt_mul_self hy2
    have hs3 : Real.sqrt (y3 * y3) = y3 := Real.sqrt_mul_self hy3
    show ((-0.07 * deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) +
        muY_p19 y1 y2 y3 * (deltaX1_p19 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
            (y5 * y5) (y6 * y6) * y1) +
        sol0 / (2 * h0 - 2) *
          Real.sqrt (deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))) /
      Real.sqrt (deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
      = ((-0.07 * deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) +
        (1 / 2) * (muY_p19 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))) *
            (deltaX1_p19 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2 *
              Real.sqrt (y1 * y1)) +
        sol0 / (2 * h0 - 2) *
          Real.sqrt (deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))) /
      Real.sqrt (deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
    rw [hs1, hs2, hs3]
    field_simp
    try ring)

/-- HOL `deriv_form_taud_D2` (pent_hex.hl:424). NEEDS: second-order chain
computation for `taud_D1_num / sqrt(delta)` (large but mechanical). -/
theorem deriv_form_taud_D2_p19 (y1 y2 y3 y4 y5 y6 : ℝ) :
    derivedForm (0 < deltaY_p18 y1 y2 y3 y4 y5 y6 ∧ 0 < y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3)
      (fun q => yOfX_p19 taudD1numX_p19 q y2 y3 y4 y5 y6 /
        Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6))
      (yOfX_p19 taudD2numX_p19 y1 y2 y3 y4 y5 y6 /
        Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) ^ 3)
      y1 Set.univ := by
  sorry

/-- Existence of the D2-derivative (HOL `derived_form_taud_D3`, computed in
HOL via the `thD3` differentiation script): the D2-slope function is
differentiable wherever `delta_y > 0`, so some derivative exists. -/
theorem derived_form_taud_D3_p19 (y1 y2 y3 y4 y5 y6 : ℝ) :
    ∃ f' : ℝ, derivedForm (0 < deltaY_p18 y1 y2 y3 y4 y5 y6 ∧ 0 < y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3)
      (fun q => yOfX_p19 taudD2numX_p19 q y2 y3 y4 y5 y6 /
        Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6) ^ 3)
      f' y1 Set.univ := by
  refine ⟨deriv
    (fun q => yOfX_p19 taudD2numX_p19 q y2 y3 y4 y5 y6 /
      Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6) ^ 3) y1, ?_⟩
  rintro ⟨hd, ht, -, -⟩
  have hne : deltaY_p18 y1 y2 y3 y4 y5 y6 ≠ 0 := ne_of_gt hd
  have hne1 : y1 * y1 ≠ 0 := ne_of_gt (mul_pos ht ht)
  have hg : HasDerivAt (fun w : ℝ => w * w) (2 * y1) y1 :=
    HasDerivAt.congr_deriv ((hasDerivAt_id y1).mul (hasDerivAt_id y1)) (by simp [two_mul])
  have hB : HasDerivAt
      (fun q => deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      (-2 * (y4 * y4) * (2 * y1)) y1 := by
    have he : (fun q => deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
        = fun q => -2 * (y4 * y4) * (q * q)
          + deltaX1_p19 0 (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
      funext q; unfold deltaX1_p19; ring
    rw [he]
    exact HasDerivAt.congr_deriv
      ((hg.const_mul (-2 * (y4 * y4))).add
        (hasDerivAt_const (x := y1)
          (c := deltaX1_p19 0 (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))) (by ring)
  have hS : HasDerivAt (fun q => Real.sqrt (q * q))
      (1 / (2 * Real.sqrt (y1 * y1)) * (2 * y1)) y1 :=
    HasDerivAt.comp y1 (Real.hasDerivAt_sqrt hne1) hg
  have hmu3 : HasDerivAt
      (fun q => muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)))
      ((-0.07) * (1 / (2 * Real.sqrt (y1 * y1)) * (2 * y1))) y1 := by
    have he : (fun q => muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)))
        = fun q => 0.012 + 0.07 * 2.52
            + 0.01 * (2.52 * 2 - Real.sqrt (y2 * y2) - Real.sqrt (y3 * y3))
          + -0.07 * Real.sqrt (q * q) := by
      funext q; unfold muY_p19; ring
    rw [he]
    exact HasDerivAt.congr_deriv
      ((hasDerivAt_const (x := y1)
          (c := 0.012 + 0.07 * 2.52
            + 0.01 * (2.52 * 2 - Real.sqrt (y2 * y2) - Real.sqrt (y3 * y3)))).add
        (hS.const_mul (-0.07))) (by ring)
  have hB2S := (hB.mul (hasDerivAt_const (x := y1) (c := (2 : ℝ)))).mul hS
  have hB2S2 := hB2S.mul hB2S
  have hmuB2S2 := hmu3.mul hB2S2
  have hD2 := (hg.const_mul (-(8 * y4 * y4))).add
    (hB.mul (hasDerivAt_const (x := y1) (c := (2 : ℝ))))
  have hmuD := hmu3.mul ((deltaY_hasDerivAt_p19 y1 y2 y3 y4 y5 y6).mul hD2)
  have dN : DifferentiableAt ℝ
      (fun q => yOfX_p19 taudD2numX_p19 q y2 y3 y4 y5 y6) y1 := by
    have hb : (fun q => yOfX_p19 taudD2numX_p19 q y2 y3 y4 y5 y6)
        = fun q => (-0.07) * (deltaY_p18 q y2 y3 y4 y5 y6 *
              (deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2 *
                Real.sqrt (q * q))) +
            (-1 / 4) * (muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) *
              ((deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2 *
                      Real.sqrt (q * q)) *
                (deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2 *
                  Real.sqrt (q * q)))) +
            (1 / 2) * (muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) *
              (deltaY_p18 q y2 y3 y4 y5 y6 *
                (-8 * (q * q) * (y4 * y4) +
                  deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2))) := by
      funext q
      unfold yOfX_p19 taudD2numX_p19 mu6X_p19 deltaY_p18
      ring
    rw [hb]
    have hshape : (fun q => (-0.07) * (deltaY_p18 q y2 y3 y4 y5 y6 *
            ((deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 : ℝ)) *
              Real.sqrt (q * q))) +
          (-1 / 4) * (muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) *
            (((deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 : ℝ)) *
                    Real.sqrt (q * q)) *
              ((deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 : ℝ)) *
                Real.sqrt (q * q)))) +
          (1 / 2) * (muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) *
            (deltaY_p18 q y2 y3 y4 y5 y6 *
              (-8 * (q * q) * (y4 * y4) +
                deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2))))
      = ((fun y => (-0.07) *
            (((fun q => deltaY_p18 q y2 y3 y4 y5 y6) *
                ((fun q => deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 : ℝ)) *
                  fun q => Real.sqrt (q * q))) y)) +
        (fun y => (-1 / 4) * (((fun q => muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))) *
            (((fun q => deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 : ℝ)) *
                  fun q => Real.sqrt (q * q)) *
              ((fun q => deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 : ℝ)) *
                fun q => Real.sqrt (q * q)))) y)) +
        (fun y => (1 / 2) * (((fun q => muY_p19 (Real.sqrt (q * q)) (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))) *
            ((fun q => deltaY_p18 q y2 y3 y4 y5 y6) *
              ((fun y => -(8 * y4 * y4) * (y * y)) +
                (fun q => deltaX1_p19 (q * q) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 2)))) y))) := by
      funext q
      simp only [Pi.mul_apply, Pi.add_apply]
      ring
    rw [hshape]
    exact ((((deltaY_hasDerivAt_p19 y1 y2 y3 y4 y5 y6).mul hB2S).const_mul (-0.07)).add
      (hmuB2S2.const_mul (-1 / 4))).add (hmuD.const_mul (1 / 2)) |>.differentiableAt
  have hsqrt3 : HasDerivAt (fun q => Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6))
      (1 / (2 * Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6)) *
        (2 * y1 * yOfX_p19 deltaX1_p19 y1 y2 y3 y4 y5 y6)) y1 :=
    HasDerivAt.comp y1 (Real.hasDerivAt_sqrt hne) (deltaY_hasDerivAt_p19 y1 y2 y3 y4 y5 y6)
  have dD : DifferentiableAt ℝ (fun q => Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6) ^ 3) y1 :=
    hsqrt3.differentiableAt.pow 3
  have dDne : (fun q => Real.sqrt (deltaY_p18 q y2 y3 y4 y5 y6) ^ 3) y1 ≠ 0 := by
    have : Real.sqrt (deltaY_p18 y1 y2 y3 y4 y5 y6) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
    simpa using pow_ne_zero 3 this
  exact dN.div dD dDne |>.hasDerivAt.hasDerivWithinAt

/-- HOL `SECOND_DERIVATIVE_TEST` (pent_hex.hl:620). The `f' z = 0` half is
Fermat; the `0 ≤ f'' z` half needs a one-sided Taylor/MVT argument not yet
in this lane. NEEDS: 1D second-derivative test. -/
theorem SECOND_DERIVATIVE_TEST_p19 (f f' f'' : ℝ → ℝ) (z : ℝ) (s : Set ℝ)
    (hz : z ∈ s) (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ s, HasDerivAt f' (f'' x) x)
    (hfc : ContinuousAt f'' z)
    (hmin : ∀ x ∈ s, f z ≤ f x) :
    f' z = 0 ∧ 0 ≤ f'' z := by
  sorry

/-- HOL `delta_y_continuous` (pent_hex.hl:838). -/
theorem delta_y_continuous_p19 (y2 y3 y4 y5 y6 : ℝ) :
    ContinuousOn (fun q => deltaY_p18 q y2 y3 y4 y5 y6) Set.univ := fun x _ =>
  (deltaY_hasDerivAt_p19 x y2 y3 y4 y5 y6).continuousAt.continuousWithinAt

/-- HOL `taud_continuous` (pent_hex.hl:853). -/
theorem taud_continuous_p19 (y2 y3 y4 y5 y6 : ℝ) :
    ContinuousOn (fun q => taudP19 q y2 y3 y4 y5 y6)
      {q | 0 ≤ deltaY_p18 q y2 y3 y4 y5 y6} := by
  have hft : Continuous (fun q => flatTerm_p19 q) := by
    have he : (fun q => flatTerm_p19 q)
        = fun q => sol0 / (2 * h0 - 2) * q + (-(sol0 * (2 * h0)) / (2 * h0 - 2)) := by
      funext q; unfold flatTerm_p19; ring
    rw [he]
    exact ((continuous_const.mul continuous_id)).add continuous_const
  intro q _
  have hmuC : Continuous fun r => muY_p19 r y2 y3 :=
    (continuous_const.add
      (continuous_const.mul (continuous_const.sub continuous_id))).add continuous_const
  have hk : ContinuousAt (fun r => flatTerm_p19 r +
      Real.sqrt (deltaY_p18 r y2 y3 y4 y5 y6) * muY_p19 r y2 y3) q :=
    ContinuousAt.add hft.continuousAt
      (ContinuousAt.mul
        ((deltaY_hasDerivAt_p19 q y2 y3 y4 y5 y6).continuousAt.sqrt) hmuC.continuousAt)
  exact hk.continuousWithinAt

/-- HOL `continuous_preimage_closed` (pent_hex.hl:769). -/
theorem continuous_preimage_closed_p19 {f : ℝ → ℝ} {s t : Set ℝ}
    (hs : IsClosed s) (ht : IsClosed t) (hc : ContinuousOn f s) :
    IsClosed {x | x ∈ s ∧ f x ∈ t} := by
  have he : {x | x ∈ s ∧ f x ∈ t} = s ∩ f ⁻¹' t := by
    ext x; constructor
    · rintro ⟨hx, hfx⟩; exact ⟨hx, hfx⟩
    · rintro ⟨hx, hfx⟩; exact ⟨hx, hfx⟩
  rw [he]
  exact hc.preimage_isClosed_of_isClosed hs ht

/-- HOL `continuous_preimage_open` (pent_hex.hl:802). -/
theorem continuous_preimage_open_p19 {f : ℝ → ℝ} {s t : Set ℝ}
    (hs : IsOpen s) (ht : IsOpen t) (hc : ContinuousOn f s) :
    IsOpen {x | x ∈ s ∧ f x ∈ t} := by
  have he : {x | x ∈ s ∧ f x ∈ t} = s ∩ f ⁻¹' t := rfl
  rw [he]
  exact (continuousOn_open_iff hs).mp hc t ht

/-- HOL `taud_minimizer` (pent_hex.hl:898): `taud` attains its minimum on the
compact set `real_interval [a,b] INTER {d ≤ delta_y}`. -/
theorem taud_minimizer_p19 (a b d y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 ≤ d)
    (hne : (Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6}) ≠ ∅) :
    ∃ z1 ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6},
      ∀ y1 ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6},
        taudP19 z1 y2 y3 y4 y5 y6 ≤ taudP19 y1 y2 y3 y4 y5 y6 := by
  have hdc : Continuous fun q : ℝ => deltaY_p18 q y2 y3 y4 y5 y6 :=
    continuous_iff_continuousAt.mpr fun x =>
      (deltaY_hasDerivAt_p19 x y2 y3 y4 y5 y6).continuousAt
  have hclosed : IsClosed {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6} := by
    have he : {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6}
        = (fun q : ℝ => deltaY_p18 q y2 y3 y4 y5 y6) ⁻¹' Set.Ici d := rfl
    rw [he]
    exact isClosed_Ici.preimage hdc
  have hcomp : IsCompact (Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6}) :=
    isCompact_Icc.inter_right hclosed
  have hsub : ∀ q ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6},
      0 ≤ deltaY_p18 q y2 y3 y4 y5 y6 := fun q hq => le_trans hd hq.2
  have hcont := ContinuousOn.mono (taud_continuous_p19 y2 y3 y4 y5 y6) hsub
  obtain ⟨z1, hz1, hmin⟩ :=
    hcomp.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hne) hcont
  exact ⟨z1, hz1, fun y1 hy1 => (isMinOn_iff.mp hmin) y1 hy1⟩

/-- HOL `taud_minimizer_cases` (pent_hex.hl:937). NEEDS: the derivative-sign
case analysis at interior minimizers (`taud_D1`/`taud_D2` numerology). -/
theorem taud_minimizer_cases_p19 (a b d z1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3)
    (hz1 : z1 ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6})
    (hmin : ∀ y1 ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6},
      taudP19 z1 y2 y3 y4 y5 y6 ≤ taudP19 y1 y2 y3 y4 y5 y6) :
    z1 = a ∨ z1 = b ∨ d = deltaY_p18 z1 y2 y3 y4 y5 y6 ∨
      (yOfX_p19 taudD1numX_p19 z1 y2 y3 y4 y5 y6 = 0 ∧
        0 ≤ yOfX_p19 taudD2numX_p19 z1 y2 y3 y4 y5 y6) := by
  sorry

/-- HOL `taud_minimizer_terminal_pent_cases` (pent_hex.hl:1053).
NEEDS-DB: consumes database inequality 5546286427 plus
`taud_minimizer_cases`. -/
theorem taud_minimizer_terminal_pent_cases_p19 (h : mainNonlinearTerminalV11_p18)
    (d y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : y1 ∈ Set.Icc 2 (2 * h0) ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6})
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy4 : 3.01 ≤ y4) (hy4' : y4 ≤ 3.237) (hy5 : y5 = 2) (hy6 : y6 = 2)
    (hd : 0 ≤ d) :
    ∃ z1 ∈ Set.Icc 2 (2 * h0) ∩ {q : ℝ | d ≤ deltaY_p18 q y2 y3 y4 y5 y6},
      taudP19 z1 y2 y3 y4 y5 y6 ≤ taudP19 y1 y2 y3 y4 y5 y6 ∧
        (z1 = 2 ∨ z1 = 2 * h0 ∨ d = deltaY_p18 z1 y2 y3 y4 y5 y6 ∨
          0.12 ≤ taudP19 z1 y2 y3 y4 y5 y6) := by
  sorry

/-- HOL `taud_mud_126_x` (pent_hex.hl:1111). -/
theorem taud_mud_126_x_p19 (y3 y4 y5 y1 y2 y3' y4' y5' y6 : ℝ) (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    yOfX_p19 (mud126xV1_p19 y3 y4 y5) y1 y2 y3' y4' y5' y6
      = taudP19 y3 y1 y2 y6 y4 y5 - flatTerm_p19 y3 := by
  have hs1 : Real.sqrt (y1 * y1) = y1 := Real.sqrt_mul_self h1
  have hs2 : Real.sqrt (y2 * y2) = y2 := Real.sqrt_mul_self h2
  have hdp : deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
      = deltaXPA18 (y3 * y3) (y1 * y1) (y2 * y2) (y6 * y6) (y4 * y4) (y5 * y5) := by
    unfold deltaXPA18; ring
  rw [yOfX_p19, mud126xV1_p19, delta126x_p19, hs1, hs2, hdp]
  show muY_p19 y3 y1 y2 * Real.sqrt (deltaY_p18 y3 y1 y2 y6 y4 y5)
      = taudP19 y3 y1 y2 y6 y4 y5 - flatTerm_p19 y3
  rw [taudP19, flatTerm_p19]
  ring

/-- HOL `taud_mud_135_x` (pent_hex.hl:1131). -/
theorem taud_mud_135_x_p19 (y2 y4 y6 y1 y2' y3 y4' y5 y6' : ℝ) (h1 : 0 ≤ y1) (h3 : 0 ≤ y3) :
    yOfX_p19 (mud135xV1_p19 y2 y4 y6) y1 y2' y3 y4' y5 y6'
      = taudP19 y2 y1 y3 y5 y4 y6 - flatTerm_p19 y2 := by
  have hs1 : Real.sqrt (y1 * y1) = y1 := Real.sqrt_mul_self h1
  have hs3 : Real.sqrt (y3 * y3) = y3 := Real.sqrt_mul_self h3
  have hdp : deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
      = deltaXPA18 (y2 * y2) (y1 * y1) (y3 * y3) (y5 * y5) (y4 * y4) (y6 * y6) := by
    unfold deltaXPA18; ring
  rw [yOfX_p19, mud135xV1_p19, delta135x_p19, hs1, hs3, hdp]
  show muY_p19 y2 y1 y3 * Real.sqrt (deltaY_p18 y2 y1 y3 y5 y4 y6)
      = taudP19 y2 y1 y3 y5 y4 y6 - flatTerm_p19 y2
  rw [taudP19, flatTerm_p19]
  ring

/-- HOL `mud_126_135` (pent_hex.hl:1151): the 126/135 x-level composites
agree under the slot rotation. -/
theorem mud_126_135_p19 (y1 y2 y3 y4 y5 y6 y3' y4' y5' : ℝ) :
    mud126xV1_p19 y3' y4' y5' y1 y2 y3 y4 y5 y6
      = mud135xV1_p19 y3' y4' y5' y1 y3 y2 y4 y6 y5 := by
  have hdp : deltaXPA18 y1 y2 (y3' * y3') (y4' * y4') (y5' * y5') y6
      = deltaXPA18 y1 (y3' * y3') y2 (y4' * y4') y6 (y5' * y5') := by
    unfold deltaXPA18; ring
  unfold mud126xV1_p19 mud135xV1_p19 delta126x_p19 delta135x_p19
  rw [hdp]

/-- HOL `flat_term_2` (pent_hex.hl:1163). -/
theorem flat_term_2_p19 : flatTerm_p19 2 = -sol0 := by
  rw [flatTerm_p19]
  have hb := h0_num_p19
  have hz : (h0 - 1 : ℝ) ≠ 0 := by linarith
  field_simp
  linarith

/-- HOL `flat_term_2h0` (pent_hex.hl:1173). -/
theorem flat_term_2h0_p19 : flatTerm_p19 (2 * h0) = 0 := by
  rw [flatTerm_p19]
  simp only [sub_self]
  ring

/-- HOL `flat_term_sol0` (pent_hex.hl:1182). -/
theorem flat_term_sol0_p19 (y : ℝ) (hy : 2 ≤ y) : -sol0 ≤ flatTerm_p19 y := by
  have hb := h0_num_p19
  have hp := sol0Pos_p19
  rw [flatTerm_p19]
  have hsplit : sol0 * (y - 2 * h0) / (2 * h0 - 2)
      = -sol0 + sol0 * (y - 2) / (2 * h0 - 2) := by
    have h52 : (2 * h0 - 2 : ℝ) = 0.52 := hb.2.2
    have h20 : (2 * h0 : ℝ) = 2.52 := hb.2.1
    have hz : (0.52 : ℝ) ≠ 0 := by norm_num
    rw [h52, h20]
    field_simp
    ring
  rw [hsplit]
  have h1 : 0 ≤ sol0 * (y - 2) / (2 * h0 - 2) := by
    refine div_nonneg ?_ (by linarith [hb.2.2])
    exact mul_nonneg hp.le (sub_nonneg.mpr hy)
  linarith [h1]

/-- HOL `taud_2h0` (pent_hex.hl:1200). -/
theorem taud_2h0_p19 (y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 ≤ deltaY_p18 (2 * h0) y2 y3 y4 y5 y6)
    (hy2 : y2 ≤ 2 * h0) (hy3 : y3 ≤ 2 * h0) :
    0 ≤ taudP19 (2 * h0) y2 y3 y4 y5 y6 := by
  rw [taudP19, flatTerm_p19]
  have h52 : (2 * h0 - 2 : ℝ) = 0.52 := h0_num_p19.2.2
  rw [h52]
  simp only [sub_self, mul_zero, zero_mul, zero_div, zero_add]
  have hmu : 0 ≤ muY_p19 (2 * h0) y2 y3 := by
    unfold muY_p19
    have h252 : (2 * h0 : ℝ) = 2.52 := h0_num_p19.2.1
    linarith [h252, hy2, hy3]
  exact mul_nonneg (Real.sqrt_nonneg _) hmu

/-- HOL `taud_053` (pent_hex.hl:1754). -/
theorem taud_053_p19 (y2 y3 y4 y5 y6 : ℝ)
    (hy2 : y2 ≤ 2 * h0) (hy3 : y3 ≤ 2 * h0)
    (hd : 20 ≤ deltaY_p18 (2 * h0) y2 y3 y4 y5 y6) :
    0.053 ≤ taudP19 (2 * h0) y2 y3 y4 y5 y6 := by
  rw [taudP19, flat_term_2h0_p19, zero_add]
  have h252 : (2 * h0 : ℝ) = 2.52 := h0_num_p19.2.1
  have hmu : 0.012 ≤ muY_p19 (2 * h0) y2 y3 := by
    unfold muY_p19
    linarith [h252, hy2, hy3]
  have hsqrt : (4.47 : ℝ) ≤ Real.sqrt (deltaY_p18 (2 * h0) y2 y3 y4 y5 y6) := by
    have h1 : (4.47 : ℝ) ≤ Real.sqrt 20 := by
      have h2 : (4.47 : ℝ) ^ 2 ≤ 20 := by norm_num
      have h3 : Real.sqrt (4.47 ^ 2) ≤ Real.sqrt 20 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq (by norm_num)] at h3
    exact le_trans h1 (Real.sqrt_le_sqrt hd)
  have hprod : 4.47 * 0.012 ≤ Real.sqrt (deltaY_p18 (2 * h0) y2 y3 y4 y5 y6)
      * muY_p19 (2 * h0) y2 y3 :=
    mul_le_mul hsqrt (le_trans (by norm_num) hmu) (by norm_num) (by linarith [hmu])
  linarith [hprod]

/-- HOL `quadratic_root_minus_works` (pent_hex.hl:1217). -/
theorem quadratic_root_minus_works_p19 (a b c : ℝ) (ha : a ≠ 0)
    (hd : 0 ≤ b * b - 4 * a * c) :
    a * (-(b + Real.sqrt (b * b - 4 * a * c)) / (2 * a)) ^ 2
        + b * (-(b + Real.sqrt (b * b - 4 * a * c)) / (2 * a)) + c = 0 := by
  set S := Real.sqrt (b * b - 4 * a * c) with hS
  have hsq : S * S = b * b - 4 * a * c := Real.mul_self_sqrt hd
  have hden : (2 * a : ℝ) ≠ 0 := mul_ne_zero two_ne_zero ha
  have hnum : (b + S) * (b + S) + 4 * a * c - 2 * b * (b + S) = 0 := by
    linear_combination hsq
  have heq : a * (-(b + S) / (2 * a)) ^ 2 + b * (-(b + S) / (2 * a)) + c
      = ((b + S) * (b + S) + 4 * a * c - 2 * b * (b + S)) / (4 * a) := by
    field_simp
    ring
  rw [heq, hnum, zero_div]

/-- HOL `quadratic_root_imp_discr_nn` (pent_hex.hl:1238). -/
theorem quadratic_root_imp_discr_nn_p19 (a b c x : ℝ)
    (h : a * x ^ 2 + b * x + c = 0) : 0 ≤ b * b - 4 * a * c := by
  have h1 : b * b - 4 * a * c
      = (b + 2 * a * x) ^ 2 - 4 * a * (a * x ^ 2 + b * x + c) := by ring
  rw [h1, h, mul_zero, sub_zero]
  exact sq_nonneg (b + 2 * a * x)

/-- HOL `quadratic_root_plus_eq` (pent_hex.hl:1251). -/
theorem quadratic_root_plus_eq_p19 (a b c m x : ℝ) (ha : 0 < a) (hm : m ≤ x)
    (h : a * x ^ 2 + b * x + c = 0)
    (hdisj : 0 < 2 * m * a + b ∨ (2 * m * a + b) ^ 2 < b * b - 4 * a * c) :
    quadraticRootPlus_p19 a b c = x := by
  have hD : b * b - 4 * a * c = (b + 2 * a * x) ^ 2 := by
    linear_combination (norm := ring_nf) (-4 * a) * h
  have hpos : 0 ≤ b + 2 * a * x := by
    rcases hdisj with h1 | h2
    · have hle : 2 * m * a ≤ 2 * x * a := by nlinarith [ha.le, hm]
      linarith
    · by_contra hneg
      have h2' : (2 * m * a + b) ^ 2 < b * b - 4 * a * c := h2
      rw [hD] at h2'
      have hle : 2 * m * a + b ≤ b + 2 * a * x := by nlinarith
      nlinarith [h2', hle, hneg, sub_nonneg.mpr (le_of_lt ha)]
  have hsqr : Real.sqrt (b * b - 4 * a * c) = b + 2 * a * x := by
    rw [hD, Real.sqrt_sq_eq_abs, abs_of_nonneg hpos]
  unfold quadraticRootPlus_p19
  rw [hsqr]
  field_simp
  ring

/-- HOL `delta_diff` (pent_hex.hl:1378). -/
theorem delta_diff_p19 (x1 z1 x2 x3 x4 x5 x6 : ℝ) :
    deltaXPA18 x1 x2 x3 x4 x5 x6
      = deltaXPA18 z1 x2 x3 x4 x5 x6 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * (x1 - z1)
        + x4 * (x1 - z1) ^ 2 := by
  unfold deltaXPA18 deltaX1_p19
  ring

/-- Coefficients of the quadratic through `f` at `0, ±1`. -/
theorem abcOfQuadratic_p19_quad (A B C : ℝ) :
    abcOfQuadratic_p19 (fun t => A * t * t + B * t + C) = (A, B, C) := by
  show ((A * 1 * 1 + B * 1 + C + (A * -1 * -1 + B * -1 + C)) / 2
        - (A * 0 * 0 + B * 0 + C),
      (A * 1 * 1 + B * 1 + C - (A * -1 * -1 + B * -1 + C)) / 2,
      A * 0 * 0 + B * 0 + C) = (A, B, C)
  rw [Prod.mk.injEq]
  refine And.intro (by ring) ?_
  rw [Prod.mk.injEq]
  exact And.intro (by ring) (by ring)

/-- HOL `edge2_flatD_x1_delta_lemma2` (pent_hex.hl:1306): when `d` is the
Cayley value at `x1` and `delta_x1 < 0`, the positive flat-edge root is
`x1` itself. -/
theorem edge2_flatD_x1_delta_lemma2_p19 (d x1 x2 x3 x4 x5 x6 : ℝ)
    (hd : deltaXPA18 x1 x2 x3 x4 x5 x6 = d) (hx4 : 0 < x4)
    (hΔ : deltaX1_p19 x1 x2 x3 x4 x5 x6 < 0) :
    edge2FlatDX1_p19 d x2 x3 x4 x5 x6 = x1 := by
  have habc : ∀ t : ℝ, d - deltaXPA18 t x2 x3 x4 x5 x6
      = x4 * t * t + (-(2 * x1 * x4 + deltaX1_p19 x1 x2 x3 x4 x5 x6)) * t
        + (x4 * x1 * x1 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * x1) := by
    intro t
    have hdd := delta_diff_p19 x1 t x2 x3 x4 x5 x6
    rw [hd] at hdd
    linarith
  have habcq : abcOfQuadratic_p19 (fun t => d - deltaXPA18 t x2 x3 x4 x5 x6)
      = (x4, -(2 * x1 * x4 + deltaX1_p19 x1 x2 x3 x4 x5 x6),
          x4 * x1 * x1 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * x1) := by
    rw [Prod.mk.injEq]
    refine And.intro ?_ ?_
    · show (d - deltaXPA18 1 x2 x3 x4 x5 x6 + (d - deltaXPA18 (-1) x2 x3 x4 x5 x6)) / 2
          - (d - deltaXPA18 0 x2 x3 x4 x5 x6) = x4
      linarith [habc 1, habc (-1), habc 0]
    · rw [Prod.mk.injEq]
      refine And.intro ?_ ?_
      · show (d - deltaXPA18 1 x2 x3 x4 x5 x6 - (d - deltaXPA18 (-1) x2 x3 x4 x5 x6)) / 2
            = -(2 * x1 * x4 + deltaX1_p19 x1 x2 x3 x4 x5 x6)
        linarith [habc 1, habc (-1)]
      · show d - deltaXPA18 0 x2 x3 x4 x5 x6
            = x4 * x1 * x1 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * x1
        linarith [habc 0]
  have hsqrtval : Real.sqrt (deltaX1_p19 x1 x2 x3 x4 x5 x6 * deltaX1_p19 x1 x2 x3 x4 x5 x6)
      = -deltaX1_p19 x1 x2 x3 x4 x5 x6 := by
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonpos hΔ.le]
  show quadraticRootPlus_p19
      (abcOfQuadratic_p19 (fun t => d - deltaXPA18 t x2 x3 x4 x5 x6)).1
      (abcOfQuadratic_p19 (fun t => d - deltaXPA18 t x2 x3 x4 x5 x6)).2.1
      (abcOfQuadratic_p19 (fun t => d - deltaXPA18 t x2 x3 x4 x5 x6)).2.2 = x1
  rw [habcq]
  simp only
  unfold quadraticRootPlus_p19
  have hdisc : (-(2 * x1 * x4 + deltaX1_p19 x1 x2 x3 x4 x5 x6)) *
        (-(2 * x1 * x4 + deltaX1_p19 x1 x2 x3 x4 x5 x6))
      - 4 * x4 * (x4 * x1 * x1 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * x1)
      = deltaX1_p19 x1 x2 x3 x4 x5 x6 * deltaX1_p19 x1 x2 x3 x4 x5 x6 := by ring
  rw [hdisc, hsqrtval]
  field_simp
  ring

/-- HOL `edge2_flatD_x1_delta_lemma3` (pent_hex.hl:1346). NEEDS-DB: the
`delta_x1 < 0` side condition comes from the nonlinear database under the
terminal box. -/
theorem edge2_flatD_x1_delta_lemma3_p19 (h : mainNonlinearTerminalV11_p18)
    (d y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : deltaY_p18 y1 y2 y3 y4 y5 y6 = d) (hd0 : 0 ≤ d) (hd20 : d ≤ 20)
    (b1 : 2 ≤ y1) (b1' : y1 ≤ 2.52) (b2 : 2 ≤ y2) (b2' : y2 ≤ 2.52)
    (b3 : 2 ≤ y3) (b3' : y3 ≤ 2.52) (b4 : 3.01 ≤ y4) (b4' : y4 ≤ 3.915)
    (b5 : y5 = 2) (b6 : y6 = 2) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915), (2, y5, 2),
        (2, y6, 2)]
      (edge2FlatDX1_p19 d (y2 * y2) (y3 * y3) (y4 * y4) (2 * 2) (2 * 2) = y1 * y1) := by
  sorry

/-- HOL `delta_2_nn` (pent_hex.hl:1388). NEEDS-DB: database conjunct
"3078028960". -/
theorem delta_2_nn_p19 (h : mainNonlinearTerminalV11_p18) (z1 y2 y3 y4 : ℝ)
    (b1 : 2 ≤ z1) (b1' : z1 ≤ 2 * h0) (b2 : 2 ≤ y2) (b2' : y2 ≤ 2 * h0)
    (b3 : 2 ≤ y3) (b3' : y3 ≤ 2 * h0) (b4 : 3.01 ≤ y4) (b4' : y4 ≤ 3.915)
    (hz : deltaY_p18 z1 y2 y3 y4 2 2 = 0) :
    0 ≤ deltaY_p18 2 y2 y3 y4 2 2 := by
  sorry

/-- HOL `delta_mono` (pent_hex.hl:1429). NEEDS-DB: database conjunct
"3078028960". -/
theorem delta_mono_p19 (h : mainNonlinearTerminalV11_p18) (z1 y1 y2 y3 y4 y5 y6 : ℝ)
    (b1 : 2 ≤ y1) (b1' : y1 ≤ z1) (b1'' : z1 ≤ 2 * h0) (b2 : 2 ≤ y2) (b2' : y2 ≤ 2 * h0)
    (b3 : 2 ≤ y3) (b3' : y3 ≤ 2 * h0) (b4 : 3.01 ≤ y4) (b4' : y4 ≤ 3.915)
    (b5 : 2 ≤ y5) (b5' : y5 ≤ 2) (b6 : 2 ≤ y6) (b6' : y6 ≤ 2)
    (hd0 : 0 ≤ deltaY_p18 y1 y2 y3 y4 y5 y6)
    (hd20 : deltaY_p18 y1 y2 y3 y4 y5 y6 ≤ 20) :
    deltaY_p18 z1 y2 y3 y4 y5 y6 ≤ deltaY_p18 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `flat_term2_126_x_eval` (pent_hex.hl:1469). NEEDS-DB. -/
theorem flat_term2_126_x_eval_p19 (h : mainNonlinearTerminalV11_p18)
    (d z y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : deltaY_p18 z y1 y2 y6 2 2 = d) (hd0 : 0 ≤ d) (hd20 : d ≤ 20)
    (bz : 2 ≤ z) (bz' : z ≤ 2 * h0) (b1 : 2 ≤ y1) (b1' : y1 ≤ 2 * h0)
    (b2 : 2 ≤ y2) (b2' : y2 ≤ 2 * h0) (b6 : 3.01 ≤ y6) (b6' : y6 ≤ 3.915) :
    yOfX_p19 (flatTerm2_126x_p19 d 4 4) y1 y2 y3 y4 y5 y6 = flatTerm_p19 z := by
  sorry

/-- HOL `flat_term2_135_x_eval` (pent_hex.hl:1493). NEEDS-DB. -/
theorem flat_term2_135_x_eval_p19 (h : mainNonlinearTerminalV11_p18)
    (d z y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : deltaY_p18 z y1 y3 y5 2 2 = d) (hd0 : 0 ≤ d) (hd20 : d ≤ 20)
    (bz : 2 ≤ z) (bz' : z ≤ 2 * h0) (b1 : 2 ≤ y1) (b1' : y1 ≤ 2 * h0)
    (b3 : 2 ≤ y3) (b3' : y3 ≤ 2 * h0) (b5 : 3.01 ≤ y5) (b5' : y5 ≤ 3.915) :
    yOfX_p19 (flatTerm2_135x_p19 d 4 4) y1 y2 y3 y4 y5 y6 = flatTerm_p19 z := by
  sorry

/-- HOL `delta_126_x_2h0_le_d` (pent_hex.hl:1517). NEEDS-DB. -/
theorem delta_126_x_2h0_le_d_p19 (h : mainNonlinearTerminalV11_p18)
    (d z1 y1 y2 y3 y4 y5 y6 : ℝ)
    (bz : 2 ≤ z1) (bz' : z1 ≤ 2 * h0) (b1 : 2 ≤ y1) (b1' : y1 ≤ 2 * h0)
    (b2 : 2 ≤ y2) (b2' : y2 ≤ 2 * h0) (b6 : 3.01 ≤ y6) (b6' : y6 ≤ 3.915)
    (hd0 : 0 ≤ d) (hd20 : d ≤ 20)
    (hd : deltaY_p18 z1 y1 y2 y6 2 2 = d) :
    yOfX_p19 (delta126x_p19 (4 * h0 * h0) 4 4) y1 y2 y3 y4 y5 y6 ≤ d := by
  sorry

/-- HOL `delta_135_x_2h0_le_d` (pent_hex.hl:1546). NEEDS-DB. -/
theorem delta_135_x_2h0_le_d_p19 (h : mainNonlinearTerminalV11_p18)
    (d z1 y1 y2 y3 y4 y5 y6 : ℝ)
    (bz : 2 ≤ z1) (bz' : z1 ≤ 2 * h0) (b1 : 2 ≤ y1) (b1' : y1 ≤ 2 * h0)
    (b3 : 2 ≤ y3) (b3' : y3 ≤ 2 * h0) (b5 : 3.01 ≤ y5) (b5' : y5 ≤ 3.915)
    (hd0 : 0 ≤ d) (hd20 : d ≤ 20)
    (hd : deltaY_p18 z1 y1 y3 y5 2 2 = d) :
    yOfX_p19 (delta135x_p19 (4 * h0 * h0) 4 4) y1 y2 y3 y4 y5 y6 ≤ d := by
  sorry

/-- HOL `lemma_5546286427` (pent_hex.hl:1575). NEEDS-DB: database inequality
"5546286427". -/
theorem lemma_5546286427_p19 (h : mainNonlinearTerminalV11_p18)
    (z1 y1 y2 y3 y4 y5 y6 : ℝ) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, z1, 2.52)]
      (0 = deltaY_p18 z1 y1 y2 y6 2 2 →
        taumP19 y1 y2 y3 y4 y5 y6 + flatTerm_p19 z1 + 0.12 > 0.616) := by
  sorry

/-- HOL `taud_ge_flat_term` (pent_hex.hl:1610). -/
theorem taud_ge_flat_term_p19 (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1 : y1 ≤ 2 * h0) (h2 : y2 ≤ 2 * h0) (h3 : y3 ≤ 2 * h0)
    (hd : 0 ≤ deltaY_p18 y1 y2 y3 y4 y5 y6) :
    flatTerm_p19 y1 ≤ taudP19 y1 y2 y3 y4 y5 y6 := by
  rw [taudP19]
  have h252 : (2 * h0 : ℝ) = 2.52 := h0_num_p19.2.1
  have hmu : 0 ≤ muY_p19 y1 y2 y3 := by
    unfold muY_p19
    nlinarith [h1, h2, h3, h252]
  exact le_trans (le_refl _) (by nlinarith [Real.sqrt_nonneg (deltaY_p18 y1 y2 y3 y4 y5 y6), hmu])

/-- HOL `sqrt20` (pent_hex.hl:1745). -/
theorem sqrt20_p19 : 4.47 ≤ Real.sqrt 20 := by
  have h2 : (4.47 : ℝ) ^ 2 ≤ 20 := by norm_num
  have h3 : Real.sqrt (4.47 ^ 2) ≤ Real.sqrt 20 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (by norm_num)] at h3

/-- HOL `terminal_pent_taum126_012` (pent_hex.hl:1626). NEEDS-DB. -/
theorem terminal_pent_taum126_012_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h126 : 0.12 ≤ taudP19 y126 y1 y2 y6 2 2)
    (h135 : 0 ≤ deltaY_p18 y135 y1 y3 y5 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taudP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taudP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `terminal_pent_tau135_012` (pent_hex.hl:1717). NEEDS-DB. -/
theorem terminal_pent_tau135_012_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h135 : 0.12 ≤ taudP19 y135 y1 y3 y5 2 2)
    (h126 : 0 ≤ deltaY_p18 y126 y1 y2 y6 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taudP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taudP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `terminal_pent_tau126_2` (pent_hex.hl:1784). NEEDS-DB. -/
theorem terminal_pent_tau126_2_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h126 : y126 = 2) (h126' : 0 ≤ deltaY_p18 y126 y1 y2 y6 2 2)
    (h135 : 0 ≤ deltaY_p18 y135 y1 y3 y5 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taudP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taudP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `terminal_pent_tau135_2` (pent_hex.hl:1903). NEEDS-DB. -/
theorem terminal_pent_tau135_2_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h135 : y135 = 2) (h126 : 0 ≤ deltaY_p18 y126 y1 y2 y6 2 2)
    (h135' : 0 ≤ deltaY_p18 y135 y1 y3 y5 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taudP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taudP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `terminal_pent_tau126_2h0` (pent_hex.hl:1932). NEEDS-DB. -/
theorem terminal_pent_tau126_2h0_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h126 : y126 = 2 * h0) (h126' : 20 ≤ deltaY_p18 y126 y1 y2 y6 2 2)
    (h135 : 0 ≤ deltaY_p18 y135 y1 y3 y5 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taudP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taudP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `taud_sqrt20` (pent_hex.hl:2047). NEEDS-DB. -/
theorem taud_sqrt20_p19 (h : mainNonlinearTerminalV11_p18) (z1 y1 y2 y3 y4 y5 y6 : ℝ)
    (bz : 2 ≤ z1) (bz' : z1 ≤ 2 * h0) (b1 : 2 ≤ y1) (b1' : y1 ≤ 2 * h0)
    (b3 : 2 ≤ y3) (b3' : y3 ≤ 2 * h0) (b5 : 3.01 ≤ y5) (b5' : y5 ≤ 3.915)
    (hd : deltaY_p18 z1 y1 y3 y5 2 2 = 20) :
    yOfX_p19 (flatTerm2_135x_p19 20 4 4) y1 y2 y3 y4 y5 y6
        + (0.012 + 0.01 * (2.52 * 2 - y1 - y3)) * 4.47
      ≤ taudP19 z1 y1 y3 y5 2 2 := by
  sorry

/-- HOL `terminal_pent_tau126_delta20` (pent_hex.hl:2078). NEEDS-DB. -/
theorem terminal_pent_tau126_delta20_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h126 : deltaY_p18 y126 y1 y2 y6 2 2 = 20)
    (h135 : 0 ≤ deltaY_p18 y135 y1 y3 y5 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taudP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taudP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `terminal_pent_taum` (pent_hex.hl:2223). NEEDS-DB. -/
theorem terminal_pent_taum_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (h126 : 20 ≤ deltaY_p18 y126 y1 y2 y6 2 2)
    (h135 : 0 ≤ deltaY_p18 y135 y1 y3 y5 2 2) :
    ineqP19 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2), (3.01, y5, 3.237),
        (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taumP19 y126 y1 y2 y6 2 2 + taumP19 y1 y2 y3 y4 y5 y6
        + taumP19 y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `taud_minimizer_terminal_hex_cases` (pent_hex.hl:2288). NEEDS-DB. -/
theorem taud_minimizer_terminal_hex_cases_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 : ℝ)
    (hd : 0 ≤ deltaY_p18 y1 y2 y3 y4 2 2) (b1 : 2 ≤ y1) (b1' : y1 ≤ 2 * h0)
    (b2 : 2 ≤ y2) (b2' : y2 ≤ 2 * h0) (b3 : 2 ≤ y3) (b3' : y3 ≤ 2 * h0)
    (b4 : 3.01 ≤ y4) (b4' : y4 ≤ 3.915) (hmt : taumP19 y1 y2 y3 y4 2 2 < 0) :
    ∃ z1, 0 ≤ deltaY_p18 z1 y2 y3 y4 2 2 ∧ 2 ≤ z1 ∧ z1 ≤ 2 * h0 ∧
      taudP19 z1 y2 y3 y4 2 2 ≤ taudP19 y1 y2 y3 y4 2 2 ∧
      (z1 = 2 ∨ deltaY_p18 z1 y2 y3 y4 2 2 = 0) := by
  sorry

/-! ## Section F: symmetry kit, wlog, and the r755 / hex reductions -/

/-- HOL `delta_y_sym_cases2` (pent_hex.hl:2404): the three 2-variable
symmetries of `delta_y` with `y5 = y6 = 2` slots. -/
theorem delta_y_sym_cases2_p19 (y1 y2 y3 y4 y5 y6 a : ℝ) :
    deltaY_p18 a y3 y1 y5 2 2 = deltaY_p18 a y1 y3 y5 2 2 ∧
      deltaY_p18 a y3 y2 y4 2 2 = deltaY_p18 a y2 y3 y4 2 2 ∧
      deltaY_p18 a y2 y1 y6 2 2 = deltaY_p18 a y1 y2 y6 2 2 := by
  unfold deltaY_p18 deltaXPA18 <;> ring <;> trivial

/-- HOL `taum_sym_cases2` (pent_hex.hl:2414): the four S3 symmetries of
`taum`. NEEDS: the dihedral-angle symmetry kit of sphere.hl (`dih_y`
symmetries through `atn2PA18`), unported on this side. -/
theorem taum_sym_cases2_p19 (y1 y2 y3 y4 y5 y6 : ℝ) :
    taumP19 y2 y1 y3 y5 y4 y6 = taumP19 y1 y2 y3 y4 y5 y6 ∧
      taumP19 y1 y3 y2 y4 y6 y5 = taumP19 y1 y2 y3 y4 y5 y6 ∧
      taumP19 y3 y1 y2 y6 y4 y5 = taumP19 y1 y2 y3 y4 y5 y6 ∧
      taumP19 y3 y2 y1 y6 y5 y4 = taumP19 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `edge2_flatD_sym` (pent_hex.hl:2425; via `Merge_ineq.delta_x_sym`). -/
theorem edge2_flatD_sym_p19 (d y1 y2 y3 a : ℝ) :
    edge2FlatDX1_p19 d y1 y2 y3 a a = edge2FlatDX1_p19 d y2 y1 y3 a a := by
  have hring : ∀ (t u v : ℝ), deltaXPA18 t u v y3 a a = deltaXPA18 t v u y3 a a := by
    intro t u v; unfold deltaXPA18; ring
  have hfe : (fun t : ℝ => d - deltaXPA18 t y1 y2 y3 a a)
      = (fun t : ℝ => d - deltaXPA18 t y2 y1 y3 a a) := by
    funext t; rw [hring t y1 y2]
  unfold edge2FlatDX1_p19
  simp only
  rw [congrArg abcOfQuadratic_p19 hfe]

/-- HOL `edge2_flatD_x1_sym_cases` (pent_hex.hl:2433). -/
theorem edge2_flatD_x1_sym_cases_p19 (y1 y2 y3 y4 y5 y6 : ℝ) :
    edge2FlatDX1_p19 0 (y3 * y3) (y2 * y2) (y4 * y4) (2 * 2) (2 * 2)
        = edge2FlatDX1_p19 0 (y2 * y2) (y3 * y3) (y4 * y4) (2 * 2) (2 * 2) ∧
      edge2FlatDX1_p19 0 (y3 * y3) (y1 * y1) (y5 * y5) (2 * 2) (2 * 2)
        = edge2FlatDX1_p19 0 (y1 * y1) (y3 * y3) (y5 * y5) (2 * 2) (2 * 2) ∧
      edge2FlatDX1_p19 0 (y2 * y2) (y1 * y1) (y6 * y6) (2 * 2) (2 * 2)
        = edge2FlatDX1_p19 0 (y1 * y1) (y2 * y2) (y6 * y6) (2 * 2) (2 * 2) := by
  have hring : ∀ (t u v w : ℝ), deltaXPA18 t u v w (2 * 2) (2 * 2)
      = deltaXPA18 t v u w (2 * 2) (2 * 2) := by
    intro t u v w; unfold deltaXPA18; ring
  have hfe : ∀ (u v w : ℝ), (fun t : ℝ => (0 : ℝ) - deltaXPA18 t u v w (2 * 2) (2 * 2))
      = (fun t : ℝ => (0 : ℝ) - deltaXPA18 t v u w (2 * 2) (2 * 2)) := by
    intro u v w; funext t; rw [hring t u v w]
  unfold edge2FlatDX1_p19
  simp only
  rw [congrArg abcOfQuadratic_p19 (hfe (y3 * y3) (y2 * y2) (y4 * y4)),
    congrArg abcOfQuadratic_p19 (hfe (y3 * y3) (y1 * y1) (y5 * y5)),
    congrArg abcOfQuadratic_p19 (hfe (y2 * y2) (y1 * y1) (y6 * y6))]
  exact And.intro rfl (And.intro rfl rfl)

/-- HOL `eulerA_x_sym_cases` (pent_hex.hl:2448). -/
theorem eulerA_x_sym_cases_p19 (y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX_p19 eulerAx_p19 y2 y1 y3 y5 y4 y6 = yOfX_p19 eulerAx_p19 y1 y2 y3 y4 y5 y6 ∧
      yOfX_p19 eulerAx_p19 y3 y1 y2 y6 y4 y5 = yOfX_p19 eulerAx_p19 y1 y2 y3 y4 y5 y6 ∧
      yOfX_p19 eulerAx_p19 y3 y2 y1 y6 y5 y4 = yOfX_p19 eulerAx_p19 y1 y2 y3 y4 y5 y6 ∧
      yOfX_p19 eulerAx_p19 y1 y3 y2 y4 y6 y5 = yOfX_p19 eulerAx_p19 y1 y2 y3 y4 y5 y6 := by
  all_goals
    unfold yOfX_p19 eulerAx_p19
    ring <;> trivial

/-- HOL `mu_y_sym` (pent_hex.hl:2465). -/
theorem mu_y_sym_p19 (y1 y2 y3 : ℝ) : muY_p19 y1 y2 y3 = muY_p19 y1 y3 y2 := by
  unfold muY_p19; ring

/-- HOL `mu_y_sym_cases` (pent_hex.hl:2474). -/
theorem mu_y_sym_cases_p19 (y1 y2 y3 : ℝ) :
    muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y1 * y1))
        = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2)) ∧
      muY_p19 2 (Real.sqrt (y3 * y3)) (Real.sqrt (y2 * y2))
        = muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) ∧
      muY_p19 2 (Real.sqrt (y3 * y3)) (Real.sqrt (y1 * y1))
        = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mu_y_sym_p19]

/-- Ring symmetry of the Cayley determinant (vertex relabeling used by the
126/135/234 transfers). -/
theorem deltaX_perm_p19 (a b c d e f : ℝ) : deltaXPA18 a b c d e f = deltaXPA18 c a b f d e := by
  unfold deltaXPA18; ring

/-- HOL `nonfunctional_mud_126` (pent_hex.hl:2488). -/
theorem nonfunctional_mud_126_p19 (a b c y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX_p19 (mud126xV1_p19 a b c) y1 y2 y3 y4 y5 y6
      = muY_p19 a (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
          * Real.sqrt (deltaY_p18 a y1 y2 y6 b c) := by
  rw [yOfX_p19, mud126xV1_p19, delta126x_p19, deltaY_p18, deltaX_perm_p19]

/-- HOL `nonfunctional_mud_234` (pent_hex.hl:2500). -/
theorem nonfunctional_mud_234_p19 (a b c y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX_p19 (mud234xV1_p19 a b c) y1 y2 y3 y4 y5 y6
      = muY_p19 a (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
          * Real.sqrt (deltaY_p18 a y2 y3 y4 b c) := by
  rw [yOfX_p19, mud234xV1_p19, delta234x_p19, deltaY_p18]

/-- Ring symmetry of the Cayley determinant (vertex swap 1↔ 2). -/
theorem deltaX_vert12_p19 (a b c d e f : ℝ) : deltaXPA18 a b c d e f = deltaXPA18 b a c e d f := by
  unfold deltaXPA18; ring

/-- HOL `nonfunctional_mud_135` (pent_hex.hl:2511). -/
theorem nonfunctional_mud_135_p19 (a b c y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX_p19 (mud135xV1_p19 a b c) y1 y2 y3 y4 y5 y6
      = muY_p19 a (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
          * Real.sqrt (deltaY_p18 a y1 y3 y5 b c) := by
  rw [yOfX_p19, mud135xV1_p19, delta135x_p19, deltaY_p18, deltaX_vert12_p19]

/-- HOL `nonfunctional_flat_term2_126` (pent_hex.hl:2524). -/
theorem nonfunctional_flat_term2_126_p19 (d a b x1 x2 x3 x4 x5 x6 : ℝ) :
    flatTerm2_126x_p19 d a b x1 x2 x3 x4 x5 x6
      = flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x1 x2 x6 a b)) := rfl

/-- HOL `nonfunctional_flat_term2_234` (pent_hex.hl:2534). -/
theorem nonfunctional_flat_term2_234_p19 (d a b x1 x2 x3 x4 x5 x6 : ℝ) :
    flatTerm2_234x_p19 d a b x1 x2 x3 x4 x5 x6
      = flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x2 x3 x4 a b)) := rfl

/-- HOL `nonfunctional_flat_term2_135` (pent_hex.hl:2544). -/
theorem nonfunctional_flat_term2_135_p19 (d a b x1 x2 x3 x4 x5 x6 : ℝ) :
    flatTerm2_135x_p19 d a b x1 x2 x3 x4 x5 x6
      = flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x1 x3 x5 a b)) := rfl

/-- HOL `nonfunctional_mudLs_126` (pent_hex.hl:2554). -/
theorem nonfunctional_mudLs_126_p19 (y1 y2 x3 x4 x5 y6 : ℝ) :
    mudLs126x_p19 4 10 2 2 2 (y1 * y1) (y2 * y2) x3 x4 x5 (y6 * y6)
      = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
          * (1 / 14 * (deltaY_p18 2 y1 y2 y6 2 2 - 16) + 4) := by
  have hsq : Real.sqrt (2 * 2) = 2 := by norm_num
  have hdp : deltaXPA18 (y1 * y1) (y2 * y2) (2 * 2) (2 * 2) (2 * 2) (y6 * y6)
      = deltaXPA18 (2 * 2) (y1 * y1) (y2 * y2) (y6 * y6) (2 * 2) (2 * 2) := by
    rw [deltaX_perm_p19]
  unfold mudLs126x_p19 mu6X_p19 delta126x_p19
  rw [hsq, hdp, deltaY_p18,
    show (1 / (4 + 10) : ℝ) = 1 / 14 from by norm_num,
    show (4 * 4 : ℝ) = 16 from by norm_num]

/-- HOL `nonfunctional_mudLs_234` (pent_hex.hl:2571). -/
theorem nonfunctional_mudLs_234_p19 (x1 y2 y3 y4 x5 x6 : ℝ) :
    mudLs234x_p19 4 10 2 2 2 x1 (y2 * y2) (y3 * y3) (y4 * y4) x5 x6
      = muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
          * (1 / 14 * (deltaY_p18 2 y2 y3 y4 2 2 - 16) + 4) := by
  have hsq : Real.sqrt (2 * 2) = 2 := by norm_num
  unfold mudLs234x_p19 mu6X_p19 delta234x_p19
  rw [hsq, deltaY_p18,
    show (1 / (4 + 10) : ℝ) = 1 / 14 from by norm_num,
    show (4 * 4 : ℝ) = 16 from by norm_num]

/-- HOL `nonfunctional_mudLs_135` (pent_hex.hl:2588). -/
theorem nonfunctional_mudLs_135_p19 (y1 x2 y3 x4 y5 x6 : ℝ) :
    mudLs135x_p19 4 10 2 2 2 (y1 * y1) x2 (y3 * y3) x4 (y5 * y5) x6
      = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
          * (1 / 14 * (deltaY_p18 2 y1 y3 y5 2 2 - 16) + 4) := by
  have hsq : Real.sqrt (2 * 2) = 2 := by norm_num
  have hdp : deltaXPA18 (y1 * y1) (2 * 2) (y3 * y3) (2 * 2) (y5 * y5) (2 * 2)
      = deltaXPA18 (2 * 2) (y1 * y1) (y3 * y3) (y5 * y5) (2 * 2) (2 * 2) := by
    rw [deltaX_vert12_p19]
  unfold mudLs135x_p19 mu6X_p19 delta135x_p19
  rw [hsq, hdp, deltaY_p18,
    show (1 / (4 + 10) : ℝ) = 1 / 14 from by norm_num,
    show (4 * 4 : ℝ) = 16 from by norm_num]

/-- HOL `ineq_sym_s3` (pent_hex.hl:2605). -/
theorem ineq_sym_s3_p19 {y4 y5 y6 : ℝ} {p : List (ℝ × ℝ × ℝ)} {r : Prop}
    (hp : ineqP19 p (r ∨ y6 < y4 ∨ y5 < y6)) (hord : y4 ≤ y6 ∧ y6 ≤ y5) :
    ineqP19 p r := by
  revert hp
  induction p with
  | nil =>
    intro hp
    rcases hp with hb | hb | hb
    · exact hb
    · exact absurd hb (by linarith)
    · exact absurd hb (by linarith)
  | cons h t ih =>
    intro hp h2
    exact ih (hp h2)

/-- HOL `ineq_sym_s2_aab` (pent_hex.hl:2617). -/
theorem ineq_sym_s2_aab_p19 {y4 y6 : ℝ} {p : List (ℝ × ℝ × ℝ)} {r : Prop}
    (hp : ineqP19 p (r ∨ y6 < y4)) (hord : y4 ≤ y6) : ineqP19 p r := by
  revert hp
  induction p with
  | nil =>
    intro hp
    rcases hp with hb | hb
    · exact hb
    · exact absurd hb (by linarith)
  | cons h t ih =>
    intro hp h2
    exact ih (hp h2)

/-- HOL `ineq_sym_s2_abb` (pent_hex.hl:2628). -/
theorem ineq_sym_s2_abb_p19 {y5 y6 : ℝ} {p : List (ℝ × ℝ × ℝ)} {r : Prop}
    (hp : ineqP19 p (r ∨ y5 < y6)) (hord : y6 ≤ y5) : ineqP19 p r := by
  revert hp
  induction p with
  | nil =>
    intro hp
    rcases hp with hb | hb
    · exact hb
    · exact absurd hb (by linarith)
  | cons h t ih =>
    intro hp h2
    exact ih (hp h2)

/-- Ring symmetry of the Cayley determinant (the `delta_x_sym` swap). -/
theorem deltaX_swap_p19 (a b c d e f : ℝ) : deltaXPA18 a b c d e f = deltaXPA18 a c b d f e := by
  unfold deltaXPA18; ring

/-! Slot transports for the r755 transfers. -/

theorem r755D234_shuffle_ikj_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    r755D234_p19 i y1 y3 y2 y4 y6 y5 = r755D234_p19 i y1 y2 y3 y4 y5 y6 := by
  rcases i with _ | _ | _ | _ | _ | n <;>
    simp only [r755D234_p19, yOfX_p19, flatTerm2_234x_p19, mud234xV1_p19, mudLs234x_p19,
      mu6X_p19, delta234x_p19]
  · rw [edge2_flatD_sym_p19]
  · rw [mu_y_sym_p19, deltaX_swap_p19]
  · rw [show Real.sqrt (2 * 2) = 2 from by norm_num, mu_y_sym_p19, deltaX_swap_p19]

theorem r755D126_shuffle_ikj_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    r755D126_p19 i y1 y3 y2 y4 y6 y5 = r755D135_p19 i y1 y2 y3 y4 y5 y6 := by
  rcases i with _ | _ | _ | _ | _ | n <;>
    simp only [r755D126_p19, r755D135_p19, yOfX_p19, flatTerm2_126x_p19, flatTerm2_135x_p19,
      mud126xV1_p19, mud135xV1_p19, mudLs126x_p19, mudLs135x_p19, mu6X_p19, delta126x_p19,
      delta135x_p19]
  · rw [mu_y_sym_p19, deltaX_swap_p19]
  · rw [show Real.sqrt (2 * 2) = 2 from by norm_num, mu_y_sym_p19, deltaX_swap_p19]

theorem r755D135_shuffle_ikj_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    r755D135_p19 i y1 y3 y2 y4 y6 y5 = r755D126_p19 i y1 y2 y3 y4 y5 y6 := by
  rcases i with _ | _ | _ | _ | _ | n <;>
    simp only [r755D126_p19, r755D135_p19, yOfX_p19, flatTerm2_126x_p19, flatTerm2_135x_p19,
      mud126xV1_p19, mud135xV1_p19, mudLs126x_p19, mudLs135x_p19, mu6X_p19, delta126x_p19,
      delta135x_p19]
  · rw [mu_y_sym_p19, deltaX_swap_p19]
  · rw [show Real.sqrt (2 * 2) = 2 from by norm_num, mu_y_sym_p19, deltaX_swap_p19]

theorem r755C234_shuffle_ikj_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    r755C234_p19 i y1 y3 y2 y4 y6 y5 = r755C234_p19 i y1 y2 y3 y4 y5 y6 := by
  cases i <;> simp only [r755C234_p19] <;> first
    | rw [(delta_y_sym_cases2_p19 y1 y2 y3 y4 y5 y6 2).2.1,
        (delta_y_sym_cases2_p19 y1 y2 y3 y4 y5 y6 2.52).2.1]
    | rw [(delta_y_sym_cases2_p19 y1 y2 y3 y4 y5 y6 2).2.1]

theorem r755C126_shuffle_ikj_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    r755C126_p19 i y1 y3 y2 y4 y6 y5 = r755C135_p19 i y1 y2 y3 y4 y5 y6 := by
  cases i <;> simp only [r755C126_p19, r755C135_p19]

theorem r755C135_shuffle_ikj_p19 (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) :
    r755C135_p19 i y1 y3 y2 y4 y6 y5 = r755C126_p19 i y1 y2 y3 y4 y5 y6 := by
  cases i <;> simp only [r755C126_p19, r755C135_p19]

/-- HOL `r755_ikj` (pent_hex.hl:2840): a database entry transfers along the
`ikj` slot rotation, modulo the S3 symmetry kit. NEEDS: the `taum`
symmetry kit (`taum_sym_cases2_p19`, sorry'd above) closes the transport;
the D/C-slot transports are available as proved helpers above. -/
theorem r755_ikj_p19 (i j k : ℕ) (f1 f2 : ℝ) (b1 b2 s45 s56 : Prop)
    (hsrc : r755Ineq_p19 i k j f1 f2 b1 b2 s45 s56) :
    r755Ineq_p19 i j k f1 f2 b1 b2 s45 s56 := by
  sorry

/-- HOL `r755_jik` (pent_hex.hl:2878): the `jik` slot-rotation transfer.
NEEDS: as `r755_ikj_p19` (the `taum` symmetry kit). -/
theorem r755_jik_p19 (i j k : ℕ) (f1 f2 : ℝ) (b1 b2 s45 s56 : Prop)
    (hsrc : r755Ineq_p19 j i k f1 f2 b1 b2 s45 s56) :
    r755Ineq_p19 i j k f1 f2 b1 b2 s45 s56 := by
  sorry

/-! ## Wlog lemmas -/

/-- HOL `REAL_WLOG_S3_SIMPLEX` (pent_hex.hl:2355). -/
theorem REAL_WLOG_S3_SIMPLEX_p19 {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (hcyc : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y3 y1 y2 y6 y4 y5)
    (hswap : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y2 y1 y3 y5 y4 y6)
    (hord : ∀ y1 y2 y3 y4 y5 y6, y4 ≤ y6 → y6 ≤ y5 → P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6
  rcases le_total y4 y5 with h45 | h54
  · rcases le_total y5 y6 with h56 | h65
    · -- y4 ≤ y5 ≤ y6
      rw [hcyc y1 y2 y3 y4 y5 y6, hswap y3 y1 y2 y6 y4 y5]
      exact hord y1 y3 y2 y4 y6 y5 h45 h56
    · rcases le_total y4 y6 with h46 | h64
      · -- y4 ≤ y6 ≤ y5
        exact hord y1 y2 y3 y4 y5 y6 h46 h65
      · -- y6 ≤ y4 ≤ y5
        rw [hcyc y1 y2 y3 y4 y5 y6, hcyc y3 y1 y2 y6 y4 y5, hswap y2 y3 y1 y5 y6 y4]
        exact hord y3 y2 y1 y6 y5 y4 h64 h45
  · rcases le_total y4 y6 with h46 | h64
    · -- y5 ≤ y4 ≤ y6
      rw [hcyc y1 y2 y3 y4 y5 y6, hcyc y3 y1 y2 y6 y4 y5]
      exact hord y2 y3 y1 y5 y6 y4 h54 h46
    · rcases le_total y5 y6 with h56 | h65
      · -- y5 ≤ y6 ≤ y4
        rw [hswap y1 y2 y3 y4 y5 y6]
        exact hord y2 y1 y3 y5 y4 y6 h56 h64
      · -- y6 ≤ y5 ≤ y4
        rw [hcyc y1 y2 y3 y4 y5 y6]
        exact hord y3 y1 y2 y6 y4 y5 h65 h54

/-- HOL `REAL_WLOG_AAB_SIMPLEX` (pent_hex.hl:2369). -/
theorem REAL_WLOG_AAB_SIMPLEX_p19 {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (hswap : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y3 y2 y1 y6 y5 y4)
    (hord : ∀ y1 y2 y3 y4 y5 y6, y4 ≤ y6 → P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6
  rcases le_total y4 y6 with h | h'
  · exact hord y1 y2 y3 y4 y5 y6 h
  · rw [hswap y1 y2 y3 y4 y5 y6]
    exact hord y3 y2 y1 y6 y5 y4 h'

/-- HOL `REAL_WLOG_ABB_SIMPLEX` (pent_hex.hl:2382). -/
theorem REAL_WLOG_ABB_SIMPLEX_p19 {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (hswap : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y1 y3 y2 y4 y6 y5)
    (hord : ∀ y1 y2 y3 y4 y5 y6, y6 ≤ y5 → P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6
  rcases le_total y6 y5 with h | h'
  · exact hord y1 y2 y3 y4 y5 y6 h
  · rw [hswap y1 y2 y3 y4 y5 y6]
    exact hord y1 y3 y2 y4 y6 y5 h'

/-! ## The r755 / hex terminal reductions -/

/-- HOL `taud_mu_clauses` (pent_hex.hl:2924). NEEDS-DB: the r755 database
entries for the diag/aab/abb triples. -/
theorem taud_mu_clauses_p19 (h : mainNonlinearTerminalV11_p18) (y2 y3 y4 : ℝ)
    (hb : 2 ≤ y2 ∧ y2 ≤ 2.52 ∧ 2 ≤ y3 ∧ y3 ≤ 2.52 ∧ 3.01 ≤ y4 ∧ y4 ≤ 3.915) :
    (0 ≤ deltaY_p18 2 y2 y3 y4 2 2 ∧ deltaY_p18 2 y2 y3 y4 2 2 ≤ 16 →
        -sol0 ≤ taudP19 2 y2 y3 y4 2 2) ∧
      (16 ≤ deltaY_p18 2 y2 y3 y4 2 2 ∧ deltaY_p18 2 y2 y3 y4 2 2 ≤ 100 →
        muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
              * (1 / 14 * (deltaY_p18 2 y2 y3 y4 2 2 - 16) + 2 * 2) - sol0
          ≤ taudP19 2 y2 y3 y4 2 2) ∧
      (100 ≤ deltaY_p18 2 y2 y3 y4 2 2 →
        muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
              * Real.sqrt (deltaY_p18 2 y2 y3 y4 2 2) - sol0
          ≤ taudP19 2 y2 y3 y4 2 2) := by
  sorry

/-! ## The hex terminal reductions -/

/-- HOL `terminal_hex_234_reduction` (pent_hex.hl:2981): the r755 database
bundle (five slot-instantiations of `taud_mu_clauses`) reduces the 234-cell
`taum` bound. NEEDS-DB. -/
theorem terminal_hex_234_reduction_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y234 : ℝ) (f1 f2 : ℝ) (b1 b2 : Prop)
    (h0c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + yOfX_p19 (flatTerm2_234x_p19 0 4 4) y1 y2 y3 y4 y5 y6 + f2 > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y2 y3 y4 2 2 < 0 ∨ deltaY_p18 2.52 y2 y3 y4 2 2 > 0) ∨ b2))
    (h1c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + 0 + f2 > 0.712 ∨ b1 ∨ False ∨ b2))
    (h2c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + (muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) *
            Real.sqrt (deltaY_p18 2 y2 y3 y4 2 2) - sol0) + f2 > 0.712 ∨
        b1 ∨ deltaY_p18 2 y2 y3 y4 2 2 < 100 ∨ b2))
    (h3c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + (muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) *
            (1 / 14 * (deltaY_p18 2 y2 y3 y4 2 2 - 16) + 2 * 2) - sol0) + f2 > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y2 y3 y4 2 2 < 16 ∨ deltaY_p18 2 y2 y3 y4 2 2 > 100) ∨ b2))
    (h4c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + (0 - sol0) + f2 > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y2 y3 y4 2 2 < 0 ∨ deltaY_p18 2 y2 y3 y4 2 2 > 16) ∨ b2)) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915), (3.01, y5, 3.915),
        (3.01, y6, 3.915), (2, y234, 2.52)]
      ((f1 + taumP19 y234 y2 y3 y4 2 2) + f2 > 0.712 ∨
        (deltaY_p18 y234 y2 y3 y4 2 2 < 0 ∨ b1) ∨ b2) := by
  sorry

/-- HOL `terminal_hex_126_reduction` (pent_hex.hl:3079): the 126-reduction is
the 234-reduction at the rotated slot tuple. -/
theorem terminal_hex_126_reduction_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y234 y126 : ℝ) (f1 f2 : ℝ) (b1 b2 : Prop)
    (h0c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 0 (y1 * y1) (y2 * y2) (y6 * y6) 4 4))
            + f2 > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y1 y2 y6 2 2 < 0 ∨ deltaY_p18 2.52 y1 y2 y6 2 2 > 0) ∨ b2))
    (h1c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + 0 + f2 > 0.712 ∨ b1 ∨ False ∨ b2))
    (h2c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2)) *
            Real.sqrt (deltaY_p18 2 y1 y2 y6 2 2) - sol0) + f2 > 0.712 ∨
        b1 ∨ deltaY_p18 2 y1 y2 y6 2 2 < 100 ∨ b2))
    (h3c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2)) *
            (1 / 14 * (deltaY_p18 2 y1 y2 y6 2 2 - 16) + 2 * 2) - sol0) + f2 > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y1 y2 y6 2 2 < 16 ∨ deltaY_p18 2 y1 y2 y6 2 2 > 100) ∨ b2))
    (h4c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (f1 + (0 - sol0) + f2 > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y1 y2 y6 2 2 < 0 ∨ deltaY_p18 2 y1 y2 y6 2 2 > 16) ∨ b2)) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915), (3.01, y5, 3.915),
        (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      ((f1 + taumP19 y126 y1 y2 y6 2 2) + f2 > 0.712 ∨
        (deltaY_p18 y126 y1 y2 y6 2 2 < 0 ∨ b1) ∨ b2) := by
  intro c1 c2 c3 c4 c5 c6 c7 c8
  have h := terminal_hex_234_reduction_p19 h y3 y1 y2 y6 y4 y5 y126 f1 f2 b1 b2
    (fun _ _ _ _ _ _ _ => by
      simp only [yOfX_p19, flatTerm2_234x_p19, deltaY_p18]
      exact h0c c1 c2 c3 c4 c5 c6 c7)
    (fun _ _ _ _ _ _ _ => h1c c1 c2 c3 c4 c5 c6 c7)
    (fun _ _ _ _ _ _ _ => h2c c1 c2 c3 c4 c5 c6 c7)
    (fun _ _ _ _ _ _ _ => h3c c1 c2 c3 c4 c5 c6 c7)
    (fun _ _ _ _ _ _ _ => h4c c1 c2 c3 c4 c5 c6 c7)
  exact h c3 c1 c2 c6 c4 c5 c8

/-- HOL `terminal_hex_135_reduction` (pent_hex.hl:3132): the 135-reduction is
the 234-reduction at the rotated slot tuple. -/
theorem terminal_hex_135_reduction_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y234 y126 y135 : ℝ) (f1 : ℝ) (b1 b2 : Prop)
    (h0c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (f1 + flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 0 (y1 * y1) (y3 * y3) (y5 * y5) 4 4))
            > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y1 y3 y5 2 2 < 0 ∨ deltaY_p18 2.52 y1 y3 y5 2 2 > 0) ∨ b2))
    (h1c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (f1 + 0 > 0.712 ∨ b1 ∨ False ∨ b2))
    (h2c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (f1 + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3)) *
            Real.sqrt (deltaY_p18 2 y1 y3 y5 2 2) - sol0) > 0.712 ∨
        b1 ∨ deltaY_p18 2 y1 y3 y5 2 2 < 100 ∨ b2))
    (h3c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (f1 + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3)) *
            (1 / 14 * (deltaY_p18 2 y1 y3 y5 2 2 - 16) + 2 * 2) - sol0) > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y1 y3 y5 2 2 < 16 ∨ deltaY_p18 2 y1 y3 y5 2 2 > 100) ∨ b2))
    (h4c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (f1 + (0 - sol0) > 0.712 ∨
        b1 ∨ (deltaY_p18 2 y1 y3 y5 2 2 < 0 ∨ deltaY_p18 2 y1 y3 y5 2 2 > 16) ∨ b2)) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915), (3.01, y5, 3.915),
        (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52), (2, y135, 2.52)]
      ((f1 + taumP19 y135 y1 y3 y5 2 2) > 0.712 ∨
        (deltaY_p18 y135 y1 y3 y5 2 2 < 0 ∨ b1) ∨ b2) := by
  intro c1 c2 c3 c4 c5 c6 c7 c8 c9
  have h := terminal_hex_234_reduction_p19 h y2 y1 y3 y5 y4 y6 y135 f1 0 b1 b2
    (fun _ _ _ _ _ _ _ => by
      simp only [yOfX_p19, flatTerm2_234x_p19]
      simpa [deltaY_p18] using h0c c1 c2 c3 c4 c5 c6 c7 c8)
    (fun _ _ _ _ _ _ _ => by simpa using h1c c1 c2 c3 c4 c5 c6 c7 c8)
    (fun _ _ _ _ _ _ _ => by simpa using h2c c1 c2 c3 c4 c5 c6 c7 c8)
    (fun _ _ _ _ _ _ _ => by simpa using h3c c1 c2 c3 c4 c5 c6 c7 c8)
    (fun _ _ _ _ _ _ _ => by simpa using h4c c1 c2 c3 c4 c5 c6 c7 c8)
  refine Or.imp_left (by simp) (h c2 c1 c3 c5 c4 c6 c9)

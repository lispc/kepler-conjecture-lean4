/-
LocalAuto11: port of three Flyspeck chapters feeding the LP / fan layer,

  - `scripts/local/lp_details.hl` (1768 lines, 1 def + 40 theorems) —
    "Treatment of special inequalities for the linear programs"
    (T. C. Hales, 2013): the quadratic-root kit behind the quad
    inequalities, the IVT/monotonicity machinery for `delta_x` /
    `delta_y`, the two LP lemmas `LEMMA_8673686234` /
    `LEMMA_5691615370`, the `lindihpi` line, the `atn (sqrt _)` numeric
    bounds, and the quad registry statements `quad_4240815464_a` /
    `quad_3862621143_revised` (consumers of `quad_nonlinear_v10`).
  - `scripts/local/PQCSXWG.hl` (320 lines, 1 def + 14 theorems) —
    sqrt-continuity suite (J. Harrison) and `mk_simplex1`: the
    unit-circumradius simplex completion `v3` of a triangle with the
    first three Cayley–Menger coordinates prescribed, its translation
    invariance, continuity, and the distance-realization statement
    `PQCSXWG1`.
  - `scripts/local/TECOXBM.hl` (1742 lines, 0 defs + 8 theorems) —
    (H. M. Le Truong) `B_SY1`-fan properties: `CROSS_DOT_POS_SY`,
    the `ivs_rho_node1` edge/inverse lemmas, row separation,
    `AFF_GT_INTER_AFF_SY`, and the TECOXBM1/2/TECOXBM wedge-coverage
    conclusions for short non-edge vertex pairs.

FILE MAP
  Section A (lp_details): quadratic-root kit (`quadraticRootPlus`,
    `deltaX1f_p11`, `edge2FlatD_x1f_p11`), the `ineq_p11` renderer of
    HOL `Sphere.ineq`, the `y_of_x` functional, the registry types
    (`quadNonlinearV10`, `getQuadNonlinear_p11`), then the 40 lp
    theorems in source order.
  Section B (PQCSXWG): `mkSimplex1_p11` (+ `deltaX5`), the eight
    sqrt-continuity lemmas, `MK_SIMPLEX_TRANSLATION`, the two
    `*_concl` registry props, `PQCSXWG1` and the continuity chain.
  Section C (TECOXBM): `wedgeInFanGt_p11` (localization.hl:79), the
    ℕ-indexed lift `liftAB_p11` of the `Fin`-indexed coefficient
    tables, and the 8 TECOXBM theorems.

ENCODING NOTES
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `real^N` (sqrt suite) ↔ an
    arbitrary topological space; `dist(v,w) pow 2` ↔ `dist v w ^ 2`;
    `vec 0` ↔ `0`; `sqrt8` ↔ `Real.sqrt 8`; `h0`/`cstab` are the
    PackingAuto2/LocalAuto4 constants (1.26 / 3.01); NO
    `native_decide` anywhere.
  - Name plan: historically every declaration carried the `_p11`
    suffix.  The
    sphere.hl kit `atn2`/`delta_x`/`delta_x4`/`dih_x`/`dih_y`/`sol_y`
    USED TO exist TWICE in the corpus (`PackingAuto20` via LocalAuto2,
    `PackingAuto21` via PackingAuto25, verbatim-identical bodies),
    making a dual import fatal.  DEDUP (atn2-merge wave 3, plan
    §5.15): the kit is now single-sourced in `Kepler.Text.SphereKit`
    (via LocalAuto2 → PackingAuto20); the Section-A `_p11`
    aliases/pins (`atn2_p11`, `deltaXf_p11`, `deltaX4f_p11`,
    `dihXf_p11`, `dihY_p11`) and the verbatim copies SphereKit hosts
    (`upsX_p11`, `deltaY_p11`, `quadraticRootPlus_p11`, `deltaX5f_p11`,
    `yOfX_p11`, `delta4Y_p11`, `taum_p11`) are deleted, and every use
    is renamed to the canonical name (plan §4).  `deltaX1f_p11` STAYS
    (SphereKit does not host `delta_x1`), as do the lane-own ports
    `edge2_flatD_x1`, `delta_234_x`, `ineq`, `dart_std4`, `tauq`,
    `x1_delta_y`, `delta4_squared_y`, `mk_simplex1`,
    `wedge_in_fan_gt` (`_p11` copies here).  With the clash resolved,
    `LocalAuto1` + `LocalAuto2` are co-importable again (dual-import
    probe verified 2026-09-18).
  - `delta_x1` (Nonlin_def.hl, not in the corpus) is recovered as the
    x1-partial of `delta_x`, the sibling recovery of `deltaX4`
    (ex-`deltaX4f`, PackingAuto20.lean:80): it satisfies both consumers
    checked here — `delta_x1 x1.. - delta_x1 x1'.. = 2*x4*(x1'-x1)`
    (lp_details.hl:390) and the quadratic normal form in
    `edge2_flatD_x1_quadratic_root_plus` (lp_details.hl:233).
    Same recovery for `delta_x5` (used by `mk_simplex1`), now
    canonical `deltaX5` in SphereKit.
  - `edge2_flatD_x1` is rendered through `quadratic_root_plus`
    (lp_details.hl:221-227 identifies the two forms; Nonlin_def.hl's
    own expanded body is not in the corpus).
  - HOL `Sphere.ineq [(lo,x,hi); ...] u` ("bounds imply u") is the
    recursive `ineq_p11`.  `dart_std4`/`tauq` (Ineq.hl / sphere.hl,
    not in the corpus) are carried as opaque constants — only their
    signatures are consumed by the quad registry statements.  `taum`
    (Terminal.hl) is now the REAL body in `Kepler.Text.SphereKit`
    (the old opaque `taum` stub is deleted); the registry
    statements consume it by signature only, so the stub→real-body
    upgrade is meaning-preserving for this file (plan §6.3).
  - HOL `quad_nonlinear` (lp_details.hl:71) defines `quad_nonlinear_v10`
    as the 17-fold conjunction of registry inequalities selected by
    `quad_idv`; the registry itself lives in
    main_nonlinear_terminal_v11 (another wave), so the conjunction is
    parameterised over the 17 statements in `quad_idv` order:
    6184614449, 6078657299, 8384429938, 9893763499, 5429228381,
    3508342905, 2327525027, 1611600345x, 2608321088x, JNTEFVP 1,
    8425800388, 3253650737, 6723997360, 1968758929, 6404645741,
    2513405547, 8293089898.
  - The HOL `real_continuous` / `continuous atreal` / `continuous`
    trichotomy on reals collapses to Mathlib's `ContinuousWithinAt` /
    `ContinuousAt`; the 8 sqrt-suite lemmas are kept as separate
    statements for 1:1 traceability (several share one Lean body).
    HOL `lift`/`drop` disappear in the rendering.
  - TECOXBM: `stable_system`, `B_SY1`, `V_SY`, `E_SY`, `F_SY`,
    `vecmats`, `local_fan`, `ivs_rho_node1`, `rho_node1` are the
    LocalAuto4 (`*_p4`) / LocalAuto2 (`*_p2`) ports; `dimindex(:M)=k`
    becomes the `Fin k` row indexing, `row (SUC (i MOD dimindex(:M)))`
    becomes `finNext i`; the HOL 1-based rows `1<=i<=dimindex` are
    0-based `Fin k` indices.  The ℕ-indexed `stable_system` consumes
    the `Fin k`-indexed `a b` through `liftAB_p11`.  HOL
    `collinear ({vec 0} ∪ {u,w})` ↔ `Collinear3 0 u w`; HOL
    `aff {vec 0, y}` ↔ `affineSpan ℝ {0, y}`; `wedge (vec 0) v w d` is
    Kepler.Geom.wedge (Azim.lean:63); `aff`-kit from Kepler.Geom.Aff.
  - `atn (sqrt _)` numeric facts (`atn_sqrt_*`) were discharged in HOL
    by `Flyspeck_constants.calc` (rigorous interval arithmetic); they
    are sorry'd here pending an interval tactic (DISCHARGES).
  - The 8 TECOXBM statements and the giants `LEMMA_8673686234`,
    `LEMMA_5691615370`, `PQCSXWG1`, the `lindihpi` pair, the IVT
    family and `quad_*` registry theorems are the chapter's contract
    registry (sorry'd; DISCHARGES convention — later waves prove them
    and the `sorry` disappears).

DISCHARGES: nothing yet (registry items keep `sorry`).
-/

import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto4
import Kepler.Geom.Aff
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section A: lp_details.hl — quadratic-root and delta_x kit -/

/- DEDUP (atn2-merge wave 3, plan §5.15): the Section-A ambiguity
aliases `atn2_p11`/`deltaXf_p11`/`deltaX4f_p11`/`dihXf_p11`/`dihY_p11`
(the kit pinned to the PackingAuto20 copies while the PackingAuto21 side
was unimportable) and the verbatim twins SphereKit hosts — `upsX_p11`,
`deltaY_p11`, `quadraticRootPlus_p11`, `deltaX5f_p11`, `yOfX_p11`,
`delta4Y_p11`, `taum_p11` — are deleted; every use now resolves to the
canonical `Kepler.Text.SphereKit` names (`atn2`, `deltaX`, `deltaX4`,
`dihXf`, `dihY`, `upsX`, `deltaY`, `quadraticRootPlus`, `deltaX5`,
`yOfX`, `delta4Y`, `taum`).  `deltaX1f_p11` and the lane-own ports
below stay (`delta_x1` has no canonical home yet). -/

/-- HOL `delta_x1` (Nonlin_def.hl; partial of `delta_x` at `x1`; see the
encoding notes — sibling recovery of `deltaX4`; no canonical home yet). -/
noncomputable def deltaX1f_p11 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x4 * (-x1 + x2 + x3 - x4 + x5 + x6) - x1 * x4 +
    x2 * x5 + x3 * x6 - x2 * x6 - x3 * x5

/- DEDUP (atn2-merge wave 3): `deltaX5f_p11` deleted — canonical
`Kepler.Text.deltaX5` (SphereKit) carries the same corrected 6-term
body (term order differs only up to `ring`), so `mkSimplex1_p11` and
its theorems are value-identical under the rename. -/

/-- HOL `edge2_flatD_x1` (Nonlin_def.hl), rendered through
`quadratic_root_plus` (lp_details.hl:221-227). -/
noncomputable def edge2FlatD_x1f_p11 (d x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  quadraticRootPlus x4 (-(deltaX1f_p11 0 x2 x3 x4 x5 x6))
    (d - deltaX 0 x2 x3 x4 x5 x6)

/-- HOL `delta_234_x` (sphere.hl): `delta_x` with the x1/x5/x6 slots
frozen (curried first); argument shape recovered from the two lp_details
call sites (lp_details.hl:1535). -/
noncomputable def delta234X_p11 (x1 x5 x6 x2 x3 x4 : ℝ) : ℝ :=
  deltaX x1 x2 x3 x4 x5 x6

/-- HOL `x1_delta_y` (sphere.hl): `y_of_x x1_delta_x` with
`x1_delta_x = x1 * delta_x1`. -/
noncomputable def x1DeltaY_p11 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y1 * y1 * deltaX1f_p11 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
    (y6 * y6)

/-- HOL `delta4_squared_y` (sphere.hl): `y_of_x (delta_x4 ^ 2)`. -/
noncomputable def delta4SquaredY_p11 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ^ 2

/-- HOL `ineq` (sphere.hl): `ineq [(lo,x,hi); ...] u` = "the bounds imply
`u`", read disjunctively. -/
def ineq_p11 : List (ℝ × ℝ × ℝ) → Prop → Prop
  | [], u => u
  | (p, x, q) :: t, u => x < p ∨ q < x ∨ ineq_p11 t u

/-- NEEDS: HOL `dart_std4` (Ineq.hl, not in the corpus): the standard
9-slot dart bounds list `(lo,x,hi)` consumed by `quad_4240815464_a`;
only the signature is needed for the registry statement, so the value
is carried opaquely until the Ineq wave lands. -/
noncomputable def dartStd4_p11 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    List (ℝ × ℝ × ℝ) := sorry

/-- NEEDS: HOL `tauq` (sphere.hl): the tau functional of a quad
(9 y-slots); opaque registry signature. -/
noncomputable def tauq_p11 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ := sorry

/- DEDUP (atn2-merge wave 3): the opaque `sorry` stub `taum_p11` is
deleted; the canonical `Kepler.Text.taum` (SphereKit) now carries the
real body (taumP19 rendering).  This file's registry statements consume
`taum` by signature only, so the stub→real-body upgrade preserves every
statement (plan §6.3). -/

/-- HOL `quad_nonlinear` (lp_details.hl:71-77): `quad_nonlinear_v10` is
the 17-fold conjunction of the `quad_idv` registry inequalities; the
registry entries (main_nonlinear_terminal_v11) are parameters here, in
`quad_idv` order (see the header). -/
def quadNonlinearV10 (Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ, ∀ i : Fin 17, Q i y1 y2 y3 y4 y5 y6

/-- HOL `get_quad_nonlinear` (lp_details.hl:79-86): the conjunct
selector at index `i`. -/
theorem getQuadNonlinear_p11 {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : quadNonlinearV10 Q) (i : Fin 17) (y1 y2 y3 y4 y5 y6 : ℝ) :
    Q i y1 y2 y3 y4 y5 y6 := h y1 y2 y3 y4 y5 y6 i

/-! ### The quadratic-root kit -/

/-- Helper (Tame_lemmas.quadratic_root_plus_works): `quadraticRootPlus`
is a root of the quadratic whenever the discriminant is nonnegative
(`a ≠ 0` suffices; HOL states `0 < a`). -/
theorem quadRootPlus_works_p11 {a b c : ℝ} (ha : a ≠ 0)
    (hD : 0 ≤ b ^ 2 - 4 * a * c) :
    a * quadraticRootPlus a b c ^ 2 + b * quadraticRootPlus a b c + c = 0 := by
  have hsq : Real.sqrt (b ^ 2 - 4 * a * c) ^ 2 = b ^ 2 - 4 * a * c := by
    rw [pow_two]; exact Real.mul_self_sqrt hD
  have hden : ((2:ℝ) * a) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero ha)
  have key : ((2:ℝ) * a) ^ 2 * (a * ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) /
      ((2:ℝ) * a)) ^ 2 + b * ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) /
      ((2:ℝ) * a)) + c)
      = a * Real.sqrt (b ^ 2 - 4 * a * c) ^ 2 - a * b ^ 2 + 4 * a ^ 2 * c := by
    field_simp
    ring
  rw [hsq] at key
  have key2 : ((2:ℝ) * a) ^ 2 * (a * ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) /
      ((2:ℝ) * a)) ^ 2 + b * ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) /
      ((2:ℝ) * a)) + c) = 0 := by rw [key]; ring
  rcases mul_eq_zero.mp key2 with h0 | h0
  · exact absurd h0 hden
  · exact h0

/-- lp_details.hl:89 `quadratic_root_plus_disc`. -/
theorem quadratic_root_plus_disc_p11 {a b c x : ℝ} (ha : 0 < a)
    (h : a * x ^ 2 + b * x + c ≤ 0) : 0 ≤ b ^ 2 - 4 * a * c := by
  have h1 : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ -4 * a * (a * x ^ 2 + b * x + c) := by nlinarith
  nlinarith [h1, h2]

/-- lp_details.hl:114 `quadratic_root_exists`. -/
theorem quadratic_root_exists_p11 {a b c x : ℝ} (ha : 0 < a)
    (h : a * x ^ 2 + b * x + c ≤ 0) :
    ∃ y, x ≤ y ∧ a * y ^ 2 + b * y + c = 0 := by
  have key : (b + 2 * a * x) ^ 2 - 4 * a * (a * x ^ 2 + b * x + c)
      = b ^ 2 - 4 * a * c := by ring
  have hD : 0 ≤ b ^ 2 - 4 * a * c := quadratic_root_plus_disc_p11 ha h
  have hX : 0 ≤ -(4 * a * (a * x ^ 2 + b * x + c)) := by nlinarith
  have hnum : 0 ≤ -(b + 2 * a * x) + Real.sqrt ((b + 2 * a * x) ^ 2
      - 4 * a * (a * x ^ 2 + b * x + c)) := by
    have hmono : Real.sqrt ((b + 2 * a * x) ^ 2)
        ≤ Real.sqrt ((b + 2 * a * x) ^ 2 - 4 * a * (a * x ^ 2 + b * x + c)) :=
      Real.sqrt_le_sqrt (by linarith [sq_nonneg (b + 2 * a * x), hX])
    have habs : b + 2 * a * x ≤ Real.sqrt ((b + 2 * a * x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]; exact le_abs_self (a := b + 2 * a * x)
    linarith
  have ha2 : 0 ≤ (2:ℝ) * a := by linarith
  refine ⟨x + quadraticRootPlus a (b + 2 * a * x) (a * x ^ 2 + b * x + c),
    ?_, ?_⟩
  · unfold quadraticRootPlus
    exact le_add_of_nonneg_right (div_nonneg hnum ha2)
  · have hw := quadRootPlus_works_p11 (a := a) (b := b + 2 * a * x)
      (c := a * x ^ 2 + b * x + c) (by linarith) (by rw [key]; exact hD)
    set q := quadraticRootPlus a (b + 2 * a * x) (a * x ^ 2 + b * x + c) with hq
    calc a * (x + q) ^ 2 + b * (x + q) + c
        = a * q ^ 2 + (b + 2 * a * x) * q + (a * x ^ 2 + b * x + c) := by ring
      _ = 0 := hw

/-- lp_details.hl:149 `quadratic_root_pos_exists`. -/
theorem quadratic_root_pos_exists_p11 {a b c x : ℝ} (ha : a < 0)
    (h : 0 ≤ a * x ^ 2 + b * x + c) :
    ∃ y, x ≤ y ∧ a * y ^ 2 + b * y + c = 0 := by
  obtain ⟨y, hy1, hy2⟩ := quadratic_root_exists_p11
    (a := -a) (b := -b) (c := -c) (x := x) (by linarith) (by nlinarith)
  exact ⟨y, hy1, by linarith [hy2]⟩

/-- lp_details.hl:164 `delta_x_root_exists`. -/
theorem delta_x_root_exists_p11 {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : 0 ≤ deltaX x1 x2 x3 x4 x5 x6) (hx1 : 0 < x1) :
    ∃ x4', x4 ≤ x4' ∧ deltaX x1 x2 x3 x4' x5 x6 = 0 := by
  have hquad : ∀ z : ℝ, deltaX x1 x2 x3 z x5 x6
      = (-x1) * z ^ 2 + deltaX4 x1 x2 x3 0 x5 x6 * z
        + deltaX x1 x2 x3 0 x5 x6 := by
    intro z; simp only [deltaX, deltaX, deltaX4, deltaX4]; ring
  obtain ⟨y, hy1, hy2⟩ := quadratic_root_pos_exists_p11
    (a := -x1) (b := deltaX4 x1 x2 x3 0 x5 x6)
    (c := deltaX x1 x2 x3 0 x5 x6) (x := x4) (by linarith)
    (by have := hquad x4; linarith)
  exact ⟨y, hy1, by rw [hquad y]; exact hy2⟩

/-- lp_details.hl:186 `delta_y_root_exists`. -/
theorem delta_y_root_exists_p11 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h : 0 ≤ deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1) (hy4 : 0 < y4) :
    ∃ y4', y4 ≤ y4' ∧ deltaY y1 y2 y3 y4' y5 y6 = 0 := by
  have hy4nn : 0 ≤ y4 := le_of_lt hy4
  have hx1p : 0 < y1 * y1 := by nlinarith
  obtain ⟨x4', hx4'1, hx4'2⟩ := delta_x_root_exists_p11
    (x1 := y1 * y1) (x2 := y2 * y2) (x3 := y3 * y3) (x4 := y4 * y4)
    (x5 := y5 * y5) (x6 := y6 * y6) h hx1p
  have hx4'0 : 0 ≤ x4' := by nlinarith [sq_nonneg y4, hx4'1]
  refine ⟨Real.sqrt x4', ?_, ?_⟩
  · have h1 : Real.sqrt (y4 * y4) ≤ Real.sqrt x4' := Real.sqrt_le_sqrt hx4'1
    rwa [Real.sqrt_mul_self hy4nn] at h1
  · have hsq : Real.sqrt x4' * Real.sqrt x4' = x4' := Real.mul_self_sqrt hx4'0
    show deltaX (y1 * y1) (y2 * y2) (y3 * y3) (Real.sqrt x4' * Real.sqrt x4')
      (y5 * y5) (y6 * y6) = 0
    rwa [hsq]

/-- lp_details.hl:221 `edge2_flatD_x1_quadratic_root_plus` (a defining
identity under the `quadraticRootPlus` rendering of
`edge2_flatD_x1`). -/
theorem edge2_flatD_x1_quadratic_root_plus_p11 (d x2 x3 x4 x5 x6 : ℝ) :
    edge2FlatD_x1f_p11 d x2 x3 x4 x5 x6 =
      quadraticRootPlus x4 (-(deltaX1f_p11 0 x2 x3 x4 x5 x6))
        (d - deltaX 0 x2 x3 x4 x5 x6) := rfl

/-- lp_details.hl:242 `edge2_flatD_x1_expanded`. -/
theorem edge2_flatD_x1_expanded_p11 (d x2 x3 x4 x5 x6 : ℝ) :
    edge2FlatD_x1f_p11 d x2 x3 x4 x5 x6 =
      (deltaX1f_p11 0 x2 x3 x4 x5 x6 +
        Real.sqrt (upsX x2 x3 x4 * upsX x4 x5 x6 - 4 * x4 * d)) /
        (2 * x4) := by
  rw [edge2_flatD_x1_quadratic_root_plus_p11]
  have hid : (-(deltaX1f_p11 0 x2 x3 x4 x5 x6)) ^ 2
      - 4 * x4 * (d - deltaX 0 x2 x3 x4 x5 x6)
      = upsX x2 x3 x4 * upsX x4 x5 x6 - 4 * x4 * d := by
    simp only [deltaX1f_p11, deltaX, deltaX, upsX]; ring
  show (-(-(deltaX1f_p11 0 x2 x3 x4 x5 x6)) +
      Real.sqrt ((-(deltaX1f_p11 0 x2 x3 x4 x5 x6)) ^ 2 -
        4 * x4 * (d - deltaX 0 x2 x3 x4 x5 x6))) / (2 * x4)
    = (deltaX1f_p11 0 x2 x3 x4 x5 x6 +
        Real.sqrt (upsX x2 x3 x4 * upsX x4 x5 x6 - 4 * x4 * d)) / (2 * x4)
  rw [hid, neg_neg]

/-- HOL `derived_form` (Calc_derivative.hl) at the `T`/univ guard, the
only form consumed in this corpus: `f` has derivative `f'` at `x` (the
continuity conjunct follows from `HasDerivAt`). -/
def DerivedForm_p11 (f : ℝ → ℝ) (f' : ℝ → ℝ) (x : ℝ) : Prop :=
  HasDerivAt f (f' x) x

/-- lp_details.hl:265 `derived_form_edge2_flatD_x1` (giant: needs the
explicit derivative formula of `edge2_flatD_x1`; DISCHARGES). -/
theorem derived_form_edge2_flatD_x1_p11 {x2 x3 x4 x5 x6 : ℝ}
    (h1 : 0 < upsX x2 x3 x4) (h2 : 0 < upsX x4 x5 x6) (hx4 : 0 < x4) :
    ∃ f' : ℝ → ℝ,
      DerivedForm_p11 (fun q => edge2FlatD_x1f_p11 0 q x3 x4 x5 x6) f' x2 := by
  sorry

/-- lp_details.hl:288 `edge2_flatD_x1_continuous`. -/
theorem edge2_flatD_x1_continuous_p11 {x2 x3 x4 x5 x6 : ℝ}
    (_h1 : 0 < upsX x2 x3 x4) (_h2 : 0 < upsX x4 x5 x6) (hx4 : 0 < x4) :
    ContinuousAt (fun q => edge2FlatD_x1f_p11 0 q x3 x4 x5 x6) x2 := by
  have hfun : (fun q => edge2FlatD_x1f_p11 0 q x3 x4 x5 x6)
      = (fun q => (deltaX1f_p11 0 q x3 x4 x5 x6 +
          Real.sqrt (upsX q x3 x4 * upsX x4 x5 x6)) / (2 * x4)) := by
    funext q
    have hrw := edge2_flatD_x1_expanded_p11 0 q x3 x4 x5 x6
    simp only [mul_zero, sub_zero] at hrw
    exact hrw
  rw [hfun]
  have hpoly : ContinuousAt (fun q => deltaX1f_p11 0 q x3 x4 x5 x6) x2 := by
    simp only [deltaX1f_p11]
    fun_prop
  have hups : ContinuousAt (fun q => upsX q x3 x4) x2 := by
    simp only [upsX]
    fun_prop
  have hprod : ContinuousAt (fun q => upsX q x3 x4 * upsX x4 x5 x6) x2 :=
    hups.mul continuousAt_const
  have hsum : ContinuousAt (fun q => deltaX1f_p11 0 q x3 x4 x5 x6 +
      Real.sqrt (upsX q x3 x4 * upsX x4 x5 x6)) x2 :=
    hpoly.add hprod.sqrt
  exact hsum.div continuousAt_const (mul_ne_zero two_ne_zero (ne_of_gt hx4))

/-- lp_details.hl:301 `IVT_edge2_flatD_x1`; NEEDS the Pent_hex
`edge2_flatD_x1_delta_lemma2` (not in this corpus; DISCHARGES). -/
theorem IVT_edge2_flatD_x1_p11 {x1m x1M x2m x2M x3 x4 x5 x6 : ℝ}
    (hups1 : ∀ x2 : ℝ, x2m ≤ x2 ∧ x2 ≤ x2M → 0 < upsX x2 x3 x4)
    (hups2 : 0 < upsX x4 x5 x6) (hx4 : 0 < x4) (h1mM : x1m ≤ x1M)
    (h2mM : x2m ≤ x2M) (hroot : deltaX x1M x2M x3 x4 x5 x6 = 0)
    (hdec : ∀ x1 x2 : ℝ, x1m ≤ x1 ∧ x1 ≤ x1M ∧ x2m ≤ x2 ∧ x2 ≤ x2M →
      deltaX1f_p11 x1 x2 x3 x4 x5 x6 < 0) :
    (∃ x2, x2m ≤ x2 ∧ x2 ≤ x2M ∧
        edge2FlatD_x1f_p11 0 x2 x3 x4 x5 x6 = x1m) ∨
      (x1m < edge2FlatD_x1f_p11 0 x2m x3 x4 x5 x6) := by
  sorry

/-- lp_details.hl:354 `edge2_flatD_x1_works`. -/
theorem edge2_flatD_x1_works_p11 {x2 x3 x4 x5 x6 : ℝ}
    (h1 : 0 ≤ upsX x2 x3 x4) (h2 : 0 ≤ upsX x4 x5 x6) (hx4 : x4 ≠ 0) :
    deltaX (edge2FlatD_x1f_p11 0 x2 x3 x4 x5 x6) x2 x3 x4 x5 x6 = 0 := by
  have hquad : ∀ z : ℝ, 0 - deltaX z x2 x3 x4 x5 x6
      = x4 * z ^ 2 + (-(deltaX1f_p11 0 x2 x3 x4 x5 x6)) * z
        + (0 - deltaX 0 x2 x3 x4 x5 x6) := by
    intro z; simp only [deltaX1f_p11, deltaX, deltaX]; ring
  have hid : (-(deltaX1f_p11 0 x2 x3 x4 x5 x6)) ^ 2
      - 4 * x4 * (0 - deltaX 0 x2 x3 x4 x5 x6)
      = upsX x2 x3 x4 * upsX x4 x5 x6 := by
    simp only [deltaX1f_p11, deltaX, deltaX, upsX]; ring
  have hD : 0 ≤ (-(deltaX1f_p11 0 x2 x3 x4 x5 x6)) ^ 2
      - 4 * x4 * (0 - deltaX 0 x2 x3 x4 x5 x6) := by
    rw [hid]; nlinarith
  show deltaX (edge2FlatD_x1f_p11 0 x2 x3 x4 x5 x6) x2 x3 x4 x5 x6 = 0
  have hz : (0:ℝ) - deltaX (edge2FlatD_x1f_p11 0 x2 x3 x4 x5 x6) x2 x3 x4 x5 x6 = 0 := by
    rw [hquad (edge2FlatD_x1f_p11 0 x2 x3 x4 x5 x6)]
    exact quadRootPlus_works_p11 hx4 hD
  linarith

/-- lp_details.hl:383 `delta_x1_decreasing`. -/
theorem delta_x1_decreasing_p11 {x1 x2 x3 x4 x5 x6 x1' : ℝ} (hle : x1 ≤ x1')
    (hx4 : 0 ≤ x4) :
    deltaX1f_p11 x1' x2 x3 x4 x5 x6 ≤ deltaX1f_p11 x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX1f_p11 x1 x2 x3 x4 x5 x6 - deltaX1f_p11 x1' x2 x3 x4 x5 x6
      = 2 * x4 * (x1' - x1) := by simp only [deltaX1f_p11]; ring
  have hpos : 0 ≤ deltaX1f_p11 x1 x2 x3 x4 x5 x6 - deltaX1f_p11 x1' x2 x3 x4 x5 x6 := by
    rw [hid]; nlinarith
  linarith

/-- lp_details.hl:447 `delta_x1_sym`. -/
theorem delta_x1_sym_p11 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX1f_p11 x1 x3 x2 x4 x6 x5 = deltaX1f_p11 x1 x2 x3 x4 x5 x6 ∧
    deltaX1f_p11 x1 x5 x6 x4 x2 x3 = deltaX1f_p11 x1 x2 x3 x4 x5 x6 := by
  constructor <;> simp only [deltaX1f_p11] <;> ring

/-! ### The IVT family and the square bijection -/

/-- lp_details.hl:403 `IVT_delta_x` (giant through
`IVT_edge2_flatD_x1`; DISCHARGES). -/
theorem IVT_delta_x_p11 {x1m x1M x2m x2M x3 x4 x5 x6 : ℝ}
    (hups1 : ∀ x2 : ℝ, x2m ≤ x2 ∧ x2 ≤ x2M → 0 < upsX x2 x3 x4)
    (hups2 : 0 < upsX x4 x5 x6) (hx4 : 0 < x4) (h1mM : x1m ≤ x1M)
    (h2mM : x2m ≤ x2M) (hroot : deltaX x1M x2M x3 x4 x5 x6 = 0)
    (hdec : ∀ x2 : ℝ, x2m ≤ x2 ∧ x2 ≤ x2M →
      deltaX1f_p11 x1m x2 x3 x4 x5 x6 < 0) :
    (∃ x2, x2m ≤ x2 ∧ x2 ≤ x2M ∧ deltaX x1m x2 x3 x4 x5 x6 = 0) ∨
    (∃ x1, x1m < x1 ∧ deltaX x1 x2m x3 x4 x5 x6 = 0) := by
  sorry

/-- lp_details.hl:458 `IVT_delta_x_3` (giant; DISCHARGES). -/
theorem IVT_delta_x_3_p11 {x1m x1M x2 x3m x3M x4 x5 x6 : ℝ}
    (hups1 : ∀ x3 : ℝ, x3m ≤ x3 ∧ x3 ≤ x3M → 0 < upsX x2 x3 x4)
    (hups2 : 0 < upsX x4 x5 x6) (hx4 : 0 < x4) (h1mM : x1m ≤ x1M)
    (h3mM : x3m ≤ x3M) (hroot : deltaX x1M x2 x3M x4 x5 x6 = 0)
    (hdec : ∀ x3 : ℝ, x3m ≤ x3 ∧ x3 ≤ x3M →
      deltaX1f_p11 x1m x2 x3 x4 x5 x6 < 0) :
    (∃ x3, x3m ≤ x3 ∧ x3 ≤ x3M ∧ deltaX x1m x2 x3 x4 x5 x6 = 0) ∨
    (∃ x1, x1m < x1 ∧ deltaX x1 x2 x3m x4 x5 x6 = 0) := by
  sorry

/-- lp_details.hl:492 `IVT_delta_x_5` (giant; DISCHARGES). -/
theorem IVT_delta_x_5_p11 {x1m x1M x2 x3 x4 x5m x5M x6 : ℝ}
    (hups1 : ∀ x5 : ℝ, x5m ≤ x5 ∧ x5 ≤ x5M → 0 < upsX x4 x5 x6)
    (hups2 : 0 < upsX x2 x3 x4) (hx4 : 0 < x4) (h1mM : x1m ≤ x1M)
    (h5mM : x5m ≤ x5M) (hroot : deltaX x1M x2 x3 x4 x5M x6 = 0)
    (hdec : ∀ x5 : ℝ, x5m ≤ x5 ∧ x5 ≤ x5M →
      deltaX1f_p11 x1m x2 x3 x4 x5 x6 < 0) :
    (∃ x5, x5m ≤ x5 ∧ x5 ≤ x5M ∧ deltaX x1m x2 x3 x4 x5 x6 = 0) ∨
    (∃ x1, x1m < x1 ∧ deltaX x1 x2 x3 x4 x5m x6 = 0) := by
  sorry

/-- lp_details.hl:523 `IVT_delta_x_6` (giant; DISCHARGES). -/
theorem IVT_delta_x_6_p11 {x1m x1M x2 x3 x4 x5 x6m x6M : ℝ}
    (hups1 : ∀ x6 : ℝ, x6m ≤ x6 ∧ x6 ≤ x6M → 0 < upsX x4 x5 x6)
    (hups2 : 0 < upsX x2 x3 x4) (hx4 : 0 < x4) (h1mM : x1m ≤ x1M)
    (h6mM : x6m ≤ x6M) (hroot : deltaX x1M x2 x3 x4 x5 x6M = 0)
    (hdec : ∀ x6 : ℝ, x6m ≤ x6 ∧ x6 ≤ x6M →
      deltaX1f_p11 x1m x2 x3 x4 x5 x6 < 0) :
    (∃ x6, x6m ≤ x6 ∧ x6 ≤ x6M ∧ deltaX x1m x2 x3 x4 x5 x6 = 0) ∨
    (∃ x1, x1m < x1 ∧ deltaX x1 x2 x3 x4 x5 x6m = 0) := by
  sorry

/-- lp_details.hl:554 `IVT_delta_x_full` (giant; DISCHARGES). -/
theorem IVT_delta_x_full_p11 {x1m x1M x2m x2M x3m x3M x4 x5m x5M x6m x6M : ℝ}
    (hx4 : 0 < x4)
    (hups1 : ∀ x2 x3 : ℝ, x2m ≤ x2 ∧ x2 ≤ x2M ∧ x3m ≤ x3 ∧ x3 ≤ x3M →
      0 < upsX x2 x3 x4)
    (hups2 : ∀ x5 x6 : ℝ, x5m ≤ x5 ∧ x5 ≤ x5M ∧ x6m ≤ x6 ∧ x6 ≤ x6M →
      0 < upsX x4 x5 x6)
    (h1 : x1m ≤ x1M) (h2 : x2m ≤ x2M) (h3 : x3m ≤ x3M) (h5 : x5m ≤ x5M)
    (h6 : x6m ≤ x6M)
    (hroot : deltaX x1M x2M x3M x4 x5M x6M = 0)
    (hdec : ∀ x2 x3 x5 x6 : ℝ, x2m ≤ x2 ∧ x2 ≤ x2M ∧ x3m ≤ x3 ∧ x3 ≤ x3M ∧
      x5m ≤ x5 ∧ x5 ≤ x5M ∧ x6m ≤ x6 ∧ x6 ≤ x6M →
      deltaX1f_p11 x1m x2 x3 x4 x5 x6 < 0) :
    (∃ x2 x3 x5 x6, x2m ≤ x2 ∧ x2 ≤ x2M ∧ x3m ≤ x3 ∧ x3 ≤ x3M ∧
        x5m ≤ x5 ∧ x5 ≤ x5M ∧ x6m ≤ x6 ∧ x6 ≤ x6M ∧
        deltaX x1m x2 x3 x4 x5 x6 = 0) ∨
    (∃ x1, x1m < x1 ∧ deltaX x1 x2m x3m x4 x5m x6m = 0) := by
  sorry

/-- lp_details.hl:662 `FORALL_BIJ_SQUARE`. -/
theorem FORALL_BIJ_SQUARE_p11 {P : ℝ → Prop} {ym yM : ℝ} (h1 : 0 ≤ ym)
    (h2 : 0 ≤ yM) :
    ((∀ x, ym * ym ≤ x ∧ x ≤ yM * yM → P x) ↔
      ∀ y, ym ≤ y ∧ y ≤ yM → P (y * y)) := by
  constructor
  · intro hP y hy
    obtain ⟨hy1, hy2⟩ := hy
    exact hP (y * y) ⟨by nlinarith, by nlinarith⟩
  · intro hP x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 ≤ x := by nlinarith [sq_nonneg ym, hx1]
    have hy4 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have e1 : ym ≤ Real.sqrt x := by
      have hle : Real.sqrt (ym * ym) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1
      rwa [Real.sqrt_mul_self h1] at hle
    have e2 : Real.sqrt x ≤ yM := by
      have hle : Real.sqrt x ≤ Real.sqrt (yM * yM) := Real.sqrt_le_sqrt hx2
      rwa [Real.sqrt_mul_self h2] at hle
    have hv := hP (Real.sqrt x) ⟨e1, e2⟩
    have hx' : x = Real.sqrt x * Real.sqrt x := hy4.symm
    rw [hx']
    exact hv

/-- lp_details.hl:698 `EXISTS_BIJ_SQUARE`. -/
theorem EXISTS_BIJ_SQUARE_p11 {P : ℝ → Prop} {ym yM : ℝ} (h1 : 0 ≤ ym)
    (h2 : 0 ≤ yM) :
    ((∃ x, ym * ym ≤ x ∧ x ≤ yM * yM ∧ P x) ↔
      ∃ y, ym ≤ y ∧ y ≤ yM ∧ P (y * y)) := by
  constructor
  · rintro ⟨x, hx1, hx2, hxP⟩
    have hx0 : 0 ≤ x := by nlinarith [sq_nonneg ym, hx1]
    have hy4 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    refine ⟨Real.sqrt x, ?_, ?_, ?_⟩
    · have hle : Real.sqrt (ym * ym) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1
      rwa [Real.sqrt_mul_self h1] at hle
    · have hle : Real.sqrt x ≤ Real.sqrt (yM * yM) := Real.sqrt_le_sqrt hx2
      rwa [Real.sqrt_mul_self h2] at hle
    · rw [hy4]
      exact hxP
  · rintro ⟨y, hy1, hy2, hyP⟩
    exact ⟨y * y, by nlinarith, by nlinarith, hyP⟩

/-- lp_details.hl:713 `IVT_delta_y_full` (giant through
`IVT_delta_x_full`; DISCHARGES). -/
theorem IVT_delta_y_full_p11 {y1m y1M y2m y2M y3m y3M y4 y5m y5M y6m y6M : ℝ}
    (hy4 : 0 < y4) (hy1m : 0 ≤ y1m) (hy2m : 0 ≤ y2m) (hy3m : 0 ≤ y3m)
    (hy5m : 0 ≤ y5m) (hy6m : 0 ≤ y6m)
    (hups1 : ∀ y2 y3 : ℝ, y2m ≤ y2 ∧ y2 ≤ y2M ∧ y3m ≤ y3 ∧ y3 ≤ y3M →
      0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hups2 : ∀ y5 y6 : ℝ, y5m ≤ y5 ∧ y5 ≤ y5M ∧ y6m ≤ y6 ∧ y6 ≤ y6M →
      0 < upsX (y4 * y4) (y5 * y5) (y6 * y6))
    (h1 : y1m ≤ y1M) (h2 : y2m ≤ y2M) (h3 : y3m ≤ y3M) (h5 : y5m ≤ y5M)
    (h6 : y6m ≤ y6M)
    (hroot : deltaY y1M y2M y3M y4 y5M y6M = 0)
    (hdec : ∀ y2 y3 y5 y6 : ℝ, y2m ≤ y2 ∧ y2 ≤ y2M ∧ y3m ≤ y3 ∧ y3 ≤ y3M ∧
      y5m ≤ y5 ∧ y5 ≤ y5M ∧ y6m ≤ y6 ∧ y6 ≤ y6M →
      yOfX (fun x1 x2 x3 x4 x5 x6 => deltaX1f_p11 x1 x2 x3 x4 x5 x6)
        y1m y2 y3 y4 y5 y6 < 0) :
    (∃ y2 y3 y5 y6, y2m ≤ y2 ∧ y2 ≤ y2M ∧ y3m ≤ y3 ∧ y3 ≤ y3M ∧
        y5m ≤ y5 ∧ y5 ≤ y5M ∧ y6m ≤ y6 ∧ y6 ≤ y6M ∧
        deltaY y1m y2 y3 y4 y5 y6 = 0) ∨
    (∃ y1, y1m < y1 ∧ deltaY y1 y2m y3m y4 y5m y6m = 0) := by
  sorry

/-! ### The WLOG lemmas and the two LP lemmas -/

/-- lp_details.hl:797 `REAL_WLOG_DS_LEMMA`. -/
theorem REAL_WLOG_DS_LEMMA_p11 {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h23 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6 ↔ P y1 y3 y2 y4 y6 y5)
    (h56 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6 ↔ P y1 y5 y6 y4 y2 y3)
    (hmax : ∀ y1 y2 y3 y4 y5 y6 : ℝ, y3 ≤ y2 → y5 ≤ y2 → y6 ≤ y2 →
      P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6
  have hne : ({y2, y3, y5, y6} : Finset ℝ).Nonempty := ⟨y2, by simp⟩
  have ha1 : ({y2, y3, y5, y6} : Finset ℝ).max' hne ∈ {y2, y3, y5, y6} :=
    Finset.max'_mem _ hne
  have ha2 : ∀ x ∈ ({y2, y3, y5, y6} : Finset ℝ),
      x ≤ ({y2, y3, y5, y6} : Finset ℝ).max' hne := fun x hx => Finset.le_max' _ x hx
  rcases Finset.mem_insert.mp ha1 with heq | ha1
  · have b3 := ha2 y3 (by simp); rw [heq] at b3
    have b5 := ha2 y5 (by simp); rw [heq] at b5
    have b6 := ha2 y6 (by simp); rw [heq] at b6
    exact hmax y1 y2 y3 y4 y5 y6 b3 b5 b6
  rcases Finset.mem_insert.mp ha1 with heq | ha1
  · have b2 := ha2 y2 (by simp); rw [heq] at b2
    have b5 := ha2 y5 (by simp); rw [heq] at b5
    have b6 := ha2 y6 (by simp); rw [heq] at b6
    rw [← h23 y1 y3 y2 y4 y6 y5]
    exact hmax y1 y3 y2 y4 y6 y5 b2 b6 b5
  rcases Finset.mem_insert.mp ha1 with heq | ha1
  · have b2 := ha2 y2 (by simp); rw [heq] at b2
    have b3 := ha2 y3 (by simp); rw [heq] at b3
    have b6 := ha2 y6 (by simp); rw [heq] at b6
    rw [← h56 y1 y5 y6 y4 y2 y3]
    exact hmax y1 y5 y6 y4 y2 y3 b6 b2 b3
  · rcases Finset.mem_singleton.mp ha1 with heq
    have b2 := ha2 y2 (by simp); rw [heq] at b2
    have b3 := ha2 y3 (by simp); rw [heq] at b3
    have b5 := ha2 y5 (by simp); rw [heq] at b5
    rw [← h56 y1 y5 y6 y4 y2 y3, ← h23 y1 y6 y5 y4 y3 y2]
    exact hmax y1 y6 y5 y4 y3 y2 b5 b3 b2


/-- lp_details.hl:818 `WLOG_8673686234`: as stated in HOL the hypothesis
and conclusion coincide (the WLOG content is `REAL_WLOG_DS_LEMMA_p11`
consumption). -/
theorem WLOG_8673686234_p11 :
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(Real.sqrt 8, y1, 3.0), (2, y2, 2 * h0), (2, y3, 2 * h0),
         (Real.sqrt 8, y4, 4 * h0), (2, y5, 2 * h0), (2, y6, 2 * h0)]
        (y2 + y3 + y5 + y6 - 7.99 > 2.75 * (y1 - Real.sqrt 8) ∨
          deltaY y1 y2 y3 y4 y5 y6 < 0 ∨ y4 < y1)) →
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(Real.sqrt 8, y1, 3.0), (2, y2, 2 * h0), (2, y3, 2 * h0),
         (Real.sqrt 8, y4, 4 * h0), (2, y5, 2 * h0), (2, y6, 2 * h0)]
        (y2 + y3 + y5 + y6 - 7.99 > 2.75 * (y1 - Real.sqrt 8) ∨
          deltaY y1 y2 y3 y4 y5 y6 < 0 ∨ y4 < y1) := fun h => h

/-- lp_details.hl:864 `LEMMA_8673686234` (giant; uses "6170936724",
"8673686234 a/b/c" through the WLOG + IVT kit; DISCHARGES). -/
theorem LEMMA_8673686234_p11 :
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3, y1, 3), (2, y2, 2.52), (2, y3, 2.52), (Real.sqrt 8, y4, 4 * h0),
         (2, y5, 2.52), (2, y6, 2.52)]
        (yOfX (fun x1 x2 x3 x4 x5 x6 => deltaX1f_p11 x1 x2 x3 x4 x5 x6)
          y1 y2 y3 y4 y5 y6 < 0)) ∧
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(Real.sqrt 8, y1, 3.0), (2, y2, 2.07), (2, y3, 2.07),
         (Real.sqrt 8, y4, 4 * h0), (2, y5, 2.07), (2, y6, 2.07)]
        (y2 + y3 + y5 + y6 - 7.99 - 0.00385 * deltaY y1 y2 y3 y4 y5 y6 >
          2.75 * ((y1 + y4) / 2 - Real.sqrt 8))) ∧
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(Real.sqrt 8, y1, 3.0), (2.07, y2, 2 * h0), (2, y3, 2 * h0),
         (3.0, y4, 3.0), (2, y5, 2 * h0), (2, y6, 2 * h0)]
        (y2 + y3 + y5 + y6 - 7.99 > 2.75 * (y1 - Real.sqrt 8) ∨
          deltaY y1 y2 y3 y4 y5 y6 < 0)) ∧
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(Real.sqrt 8, y1, 3.0), (2.07, y2, 2 * h0), (2, y3, 2 * h0),
         (Real.sqrt 8, y4, 3.0), (2, y5, 2 * h0), (2, y6, 2 * h0)]
        (y2 + y3 + y5 + y6 - 7.99 > 2.75 * ((y1 + y4) / 2 - Real.sqrt 8) ∨
          y2 + y3 + y5 + y6 - 7.99 - 0.00385 * deltaY y1 y2 y3 y4 y5 y6 >
            2.75 * ((y1 + y4) / 2 - Real.sqrt 8) ∨
          deltaY y1 y2 y3 y4 y5 y6 < 0)) →
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(Real.sqrt 8, y1, 3.0), (2, y2, 2 * h0), (2, y3, 2 * h0),
         (Real.sqrt 8, y4, 4 * h0), (2, y5, 2 * h0), (2, y6, 2 * h0)]
        (y2 + y3 + y5 + y6 - 7.99 > 2.75 * (y1 - Real.sqrt 8) ∨
          deltaY y1 y2 y3 y4 y5 y6 < 0 ∨ y4 < y1) := by
  sorry

/-- lp_details.hl:1052 `WLOG_5691615370` (giant: needs Terminal's
`REAL_WLOG_SQUARE2_LEMMA`, not in this corpus; DISCHARGES). -/
theorem WLOG_5691615370_p11 :
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3.0, y1, 3.0), (2, y2, 2.52), (2, y3, 2.52), (3.0, y4, 3.0),
         (2, y5, 2.52), (2, y6, 2.52)]
        (deltaY y1 y2 y3 y4 y5 y6 < 0 ∨
          y2 + y3 + y5 + y6 > 8.472 ∨ y2 < y3 ∨ y2 < y5 ∨ y2 < y6 ∨
            y3 < y6)) →
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3.0, y1, 3.0), (2, y2, 2.52), (2, y3, 2.52), (3.0, y4, 3.0),
         (2, y5, 2.52), (2, y6, 2.52)]
        (deltaY y1 y2 y3 y4 y5 y6 < 0 ∨ y2 + y3 + y5 + y6 > 8.472) := by
  sorry

/-- lp_details.hl:1096 `LEMMA_5691615370` (giant; uses "5584033259",
"6170936724", "5691615370"; DISCHARGES). -/
theorem LEMMA_5691615370_p11 :
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3, y1, 4 * h0), (2, y2, 2.472), (2, y3, 2.472), (3, y4, 4 * h0),
         (2, y5, 2.472), (2, y6, 2.472)]
        (y1 < 4 ∨ deltaY y1 y2 y3 y4 y5 y6 < 0)) ∧
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3, y1, 3), (2, y2, 2.52), (2, y3, 2.52), (Real.sqrt 8, y4, 4 * h0),
         (2, y5, 2.52), (2, y6, 2.52)]
        (yOfX (fun x1 x2 x3 x4 x5 x6 => deltaX1f_p11 x1 x2 x3 x4 x5 x6)
          y1 y2 y3 y4 y5 y6 < 0)) ∧
    (∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3.0, y1, 3.0), (2, y2, 2.52), (2, y3, 2.52), (3.0, y4, 3.0),
         (2, y5, 2.52), (2, y6, 2.52)]
        (deltaY y1 y2 y3 y4 y5 y6 < 0 ∨
          y2 + y3 + y5 + y6 > 8.472 ∨ y2 < y3 ∨ y2 < y5 ∨ y2 < y6 ∨
            y3 < y6)) →
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, ineq_p11
        [(3.0, y1, 4 * h0), (2, y2, 2.52), (2, y3, 2.52), (3.0, y4, 4 * h0),
         (2, y5, 2.52), (2, y6, 2.52)]
        (deltaY y1 y2 y3 y4 y5 y6 < 0 ∨ y2 + y3 + y5 + y6 > 8.472) := by
  sorry

/-! ### The `lindihpi` line and the numeric `atn (sqrt _)` bounds -/

/-- lp_details.hl:1272 `lindihpi_lt_small` (quadrant analysis of `atn2`;
DISCHARGES). -/
theorem lindihpi_lt_small_p11 {u x1 x2 x3 x4 x5 x6 : ℝ}
    (habs : |u| < Real.pi / 2) (hx1 : 0 < x1)
    (hd4 : 0 < deltaX4 x1 x2 x3 x4 x5 x6) :
    (dihXf x1 x2 x3 x4 x5 x6 < u ↔
      Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        < Real.tan u * deltaX4 x1 x2 x3 x4 x5 x6) := by
  sorry

/-- lp_details.hl:1296 `lindihpi_lt_y_small` (through
`lindihpi_lt_small_p11`; DISCHARGES). -/
theorem lindihpi_lt_y_small_p11 {b y1 y2 y3 y4 y5 y6 : ℝ} (hy1 : 0 < y1)
    (hb : 0 < b) (hd : 0 ≤ deltaY y1 y2 y3 y4 y5 y6)
    (hd4 : 0 < delta4Y y1 y2 y3 y4 y5 y6) :
    (4 * x1DeltaY_p11 y1 y2 y3 y4 y5 y6
        < b * delta4SquaredY_p11 y1 y2 y3 y4 y5 y6 ↔
      dihY y1 y2 y3 y4 y5 y6 < Real.arctan (Real.sqrt b)) := by
  sorry

/-- lp_details.hl:1348 `dih_y_imp_delta_y_nz`. -/
theorem dih_y_imp_delta_y_nz_p11 {y1 y2 y3 y4 y5 y6 : ℝ} (hy1 : 0 < y1)
    (hpi : dihY y1 y2 y3 y4 y5 y6 < Real.pi)
    (hd4 : delta4Y y1 y2 y3 y4 y5 y6 < 0) :
    deltaY y1 y2 y3 y4 y5 y6 ≠ 0 := by
  intro h0
  -- BODY-FIX (atn2-merge wave 3): the old set `[deltaY_p11, deltaXf_p11,
  -- delta4Y_p11, deltaX4f_p11]` unfolded the y-space twins and stopped at
  -- the plain kit names, keeping `h0`/`hd4` in `deltaXf`/`deltaX4f`
  -- spelling.  With the aliases deleted we stop at the canonical
  -- `deltaX`/`deltaX4` spellings instead (NOT unfolded) — same rewrite
  -- shape, now matching the canonical `dihXf` body below; `yOfX` is
  -- included because canonical `delta4Y` routes through `yOfX`
  -- (`yOfX deltaX4 …` → `deltaX4 (y1*y1) …`), which the old inline body
  -- did not.
  simp only [deltaY, delta4Y, yOfX] at h0 hd4
  simp only [dihY, dihXf] at hpi
  have hsqrt : Real.sqrt
      ((4:ℝ) * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6)) = 0 := by
    simp only [h0, mul_zero, Real.sqrt_zero]
  have harg : atn2 (Real.sqrt
      ((4:ℝ) * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6)))
      (-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
        (y6 * y6))) = Real.pi / 2 := by
    simp only [atn2, hsqrt]
    simp [hd4]
  rw [harg] at hpi
  linarith

/-- lp_details.hl:1367 `atn_sqrt_39609` (HOL: `Flyspeck_constants.calc`
interval evaluation; needs an interval tactic; DISCHARGES). -/
theorem atn_sqrt_39609_p11 :
    (1.621:ℝ) < Real.pi - Real.arctan (Real.sqrt 396.09) := by
  sorry

/-- lp_details.hl:1375 `atn_sqrt_3418` (DISCHARGES). -/
theorem atn_sqrt_3418_p11 :
    Real.arctan (Real.sqrt 3.418) < (2.15:ℝ) / 2 := by
  sorry

/-- lp_details.hl:1383 `atn_sqrt_38` (DISCHARGES). -/
theorem atn_sqrt_38_p11 : Real.arctan (Real.sqrt 38.0) < (1.41:ℝ) := by
  sorry

/-- lp_details.hl:1391 `atn_sqrt_405` (DISCHARGES). -/
theorem atn_sqrt_405_p11 : Real.arctan (Real.sqrt 4.05) < (1.11:ℝ) := by
  sorry

/-- lp_details.hl:1399 `atn_sqrt_29` (DISCHARGES). -/
theorem atn_sqrt_29_p11 : Real.arctan (Real.sqrt 2.9) < (1.04:ℝ) := by
  sorry

/-- lp_details.hl:1407 `atn_sqrt_1914` (DISCHARGES). -/
theorem atn_sqrt_1914_p11 : Real.arctan (Real.sqrt 1.914) < (0.945:ℝ) := by
  sorry

/-- lp_details.hl:1415 `atn_sqrt_68158` (DISCHARGES). -/
theorem atn_sqrt_68158_p11 : Real.arctan (Real.sqrt 6.8158) < (1.205:ℝ) := by
  sorry

/-- lp_details.hl:1423 `atn_sqrt_833` (DISCHARGES). -/
theorem atn_sqrt_833_p11 : Real.arctan (Real.sqrt 0.833) < (0.74:ℝ) := by
  sorry

/-! ### The quad registry statements -/

/-- lp_details.hl:1431 `quad_4240815464_a` (registry giant through
`quad_nonlinear_v10` conjuncts "6184614449".."2608321088x"; DISCHARGES). -/
theorem quad_4240815464_a_p11 {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (hQ : quadNonlinearV10 Q) :
    ∀ y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ,
      ineq_p11 (dartStd4_p11 y1 y2 y3 y4 y5 y6 y7 y8 y9)
        (tauq_p11 y1 y2 y3 y4 y5 y6 y7 y8 y9 < 0.206 ∨
          y2 + y3 < y4 ∨
          tauq_p11 y1 y2 y3 y4 y5 y6 y7 y8 y9
              + 0.7573 * dihY y1 y2 y3 y4 y5 y6 - 1.433 > 0.0 ∨
          deltaY y1 y2 y3 y4 y5 y6 < 0) := by
  sorry

/-- lp_details.hl:1548 `quad_3862621143_revised_wlog` (registry giant;
DISCHARGES). -/
theorem quad_3862621143_revised_wlog_p11
    {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hQ : quadNonlinearV10 Q) :
    ∀ y0 y1 y2 y3 y5 y6 y7 y8 y9 : ℝ,
      ineq_p11
        [(3.01, y0, 4 * h0), (2.0, y1, 2 * h0), (2.0, y2, 2 * h0),
         (2.0, y3, 2 * h0), (2.0, y5, 2 * h0), (2.0, y6, 2 * h0),
         (2.0, y7, 2 * h0), (2.0, y8, 2 * h0), (2.0, y9, 2 * h0)]
        (taum y1 y2 y7 y9 y0 y6 + taum y1 y3 y7 y8 y0 y5 < 0.206 ∨
          taum y1 y2 y7 y9 y0 y6 + taum y1 y3 y7 y8 y0 y5
              - 0.453 * (dihY y1 y2 y7 y9 y0 y6 +
                dihY y1 y3 y7 y8 y0 y5) + 0.777 > 0.0 ∨
          deltaY y1 y2 y7 y9 y0 y6 < 0 ∨
          deltaY y1 y3 y7 y8 y0 y5 < 0 ∨
          dihY y1 y3 y7 y8 y0 y5 < dihY y1 y2 y7 y9 y0 y6) := by
  sorry

/-- lp_details.hl:1732 `quad_3862621143_revised` (registry giant through
the wlog + `taum_sym2`/`dih_y_sym`; DISCHARGES). -/
theorem quad_3862621143_revised_p11
    {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hQ : quadNonlinearV10 Q) :
    ∀ y0 y1 y2 y3 y5 y6 y7 y8 y9 : ℝ,
      ineq_p11
        [(3.01, y0, 4 * h0), (2.0, y1, 2 * h0), (2.0, y2, 2 * h0),
         (2.0, y3, 2 * h0), (2.0, y5, 2 * h0), (2.0, y6, 2 * h0),
         (2.0, y7, 2 * h0), (2.0, y8, 2 * h0), (2.0, y9, 2 * h0)]
        (taum y1 y2 y7 y9 y0 y6 + taum y1 y3 y7 y8 y0 y5 < 0.206 ∨
          taum y1 y2 y7 y9 y0 y6 + taum y1 y3 y7 y8 y0 y5
              - 0.453 * (dihY y1 y2 y7 y9 y0 y6 +
                dihY y1 y3 y7 y8 y0 y5) + 0.777 > 0.0 ∨
          deltaY y1 y2 y7 y9 y0 y6 < 0 ∨
          deltaY y1 y3 y7 y8 y0 y5 < 0) := by
  sorry

/-! ## Section B: PQCSXWG.hl — sqrt continuity and `mk_simplex1` -/

/-- HOL `mk_simplex1` (PQCSXWG.hl:94, corrected Flyspeck definition): the
unit-sphere simplex completion of a triangle `v0 v1 v2` with prescribed
squared coordinates `x1 = |v1-v0|²`, `x2 = |v2-v0|²`, `x6 = |v1-v2|²` and
Cayley–Menger data `x3 x4 x5`.  `uinv % v` renders as `uinv • v`. -/
noncomputable def mkSimplex1_p11 (v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ) : V3 :=
  let uinv := 1 / upsX x1 x2 x6
  let d := deltaX x1 x2 x3 x4 x5 x6
  let d5 := deltaX5 x1 x2 x3 x4 x5 x6
  let d4 := deltaX4 x1 x2 x3 x4 x5 x6
  let vcross : V3 :=
    (WithLp.toLp 2 (crossProduct (WithLp.ofLp (v1 - v0))
      (WithLp.ofLp (v2 - v0))) : V3)
  v0 + uinv • ((2 * Real.sqrt d) • vcross + d5 • (v1 - v0) + d4 • (v2 - v0))

/-! ### The sqrt-continuity suite (PQCSXWG.hl:16-88)

HOL states these for `real^N` with `lift`/`drop` round-trips and the
`real_continuous`/`atreal` refinements; the Lean rendering is uniform in
`ContinuousWithinAt`/`ContinuousAt` (Mathlib's `Real.sqrt` is continuous
everywhere, so the sign disjunction is carried in the statement only). -/

/-- PQCSXWG.hl:16 `CONTINUOUS_WITHIN_SQRT_COMPOSE`. -/
theorem CONTINUOUS_WITHIN_SQRT_COMPOSE_p11 {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} {s : Set α} {a : α}
    (hf : ContinuousWithinAt f s a) (_h : 0 < f a ∨ ∀ x ∈ s, 0 ≤ f x) :
    ContinuousWithinAt (fun x => Real.sqrt (f x)) s a :=
  hf.sqrt

/-- PQCSXWG.hl:34 `CONTINUOUS_AT_SQRT_COMPOSE`. -/
theorem CONTINUOUS_AT_SQRT_COMPOSE_p11 {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} {a : α}
    (hf : ContinuousAt f a) (_h : 0 < f a ∨ ∀ x, 0 ≤ f x) :
    ContinuousAt (fun x => Real.sqrt (f x)) a :=
  hf.sqrt

/-- PQCSXWG.hl:43 `REAL_CONTINUOUS_WITHIN_SQRT_COMPOSE` (same Lean body
as `CONTINUOUS_WITHIN_SQRT_COMPOSE_p11` after the `lift`-collapse). -/
theorem REAL_CONTINUOUS_WITHIN_SQRT_COMPOSE_p11 {α : Type*}
    [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}
    (hf : ContinuousWithinAt f s a) (_h : 0 < f a ∨ ∀ x ∈ s, 0 ≤ f x) :
    ContinuousWithinAt (fun x => Real.sqrt (f x)) s a :=
  hf.sqrt

/-- PQCSXWG.hl:51 `REAL_CONTINUOUS_AT_SQRT_COMPOSE`. -/
theorem REAL_CONTINUOUS_AT_SQRT_COMPOSE_p11 {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} {a : α}
    (hf : ContinuousAt f a) (_h : 0 < f a ∨ ∀ x, 0 ≤ f x) :
    ContinuousAt (fun x => Real.sqrt (f x)) a :=
  hf.sqrt

/-- PQCSXWG.hl:59 `CONTINUOUS_WITHINREAL_SQRT_COMPOSE`. -/
theorem CONTINUOUS_WITHINREAL_SQRT_COMPOSE_p11 {f : ℝ → ℝ} {s : Set ℝ}
    {a : ℝ}
    (hf : ContinuousWithinAt f s a) (_h : 0 < f a ∨ ∀ x ∈ s, 0 ≤ f x) :
    ContinuousWithinAt (fun x => Real.sqrt (f x)) s a :=
  hf.sqrt

/-- PQCSXWG.hl:68 `CONTINUOUS_ATREAL_SQRT_COMPOSE`. -/
theorem CONTINUOUS_ATREAL_SQRT_COMPOSE_p11 {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (_h : 0 < f a ∨ ∀ x, 0 ≤ f x) :
    ContinuousAt (fun x => Real.sqrt (f x)) a :=
  hf.sqrt

/-- PQCSXWG.hl:76 `REAL_CONTINUOUS_WITHINREAL_SQRT_COMPOSE`. -/
theorem REAL_CONTINUOUS_WITHINREAL_SQRT_COMPOSE_p11 {f : ℝ → ℝ} {s : Set ℝ}
    {a : ℝ}
    (hf : ContinuousWithinAt f s a) (_h : 0 < f a ∨ ∀ x ∈ s, 0 ≤ f x) :
    ContinuousWithinAt (fun x => Real.sqrt (f x)) s a :=
  hf.sqrt

/-- PQCSXWG.hl:83 `REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE`. -/
theorem REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE_p11 {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (_h : 0 < f a ∨ ∀ x, 0 ≤ f x) :
    ContinuousAt (fun x => Real.sqrt (f x)) a :=
  hf.sqrt

/-- PQCSXWG.hl:102 `MK_SIMPLEX_TRANSLATION` (the HOL
`add_translation_invariants` registration is implicit: Lean has no
invariant database, consumers apply the lemma directly). -/
theorem MK_SIMPLEX_TRANSLATION_p11 (a v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ) :
    mkSimplex1_p11 (a + v0) (a + v1) (a + v2) x1 x2 x3 x4 x5 x6
      = a + mkSimplex1_p11 v0 v1 v2 x1 x2 x3 x4 x5 x6 := by
  simp only [mkSimplex1_p11, add_sub_add_left_eq_sub]
  rw [add_assoc]

/-- PQCSXWG.hl:117 `PQCSXWG1_concl` (statement-registry term; carried as
a Prop def, cf. the LocalAuto1 `*_concl` convention). -/
def PQCSXWG1_concl_p11 : Prop :=
  ∀ v0 v1 v2 v3 : V3, ∀ x1 x2 x3 x4 x5 x6 : ℝ,
    0 < x1 ∧ 0 < x2 ∧ 0 < x3 ∧ 0 < x4 ∧ 0 < x5 ∧ 0 < x6 ∧
      ¬Collinear3 v0 v1 v2 ∧
      x1 = dist v1 v0 ^ 2 ∧ x2 = dist v2 v0 ^ 2 ∧ x6 = dist v1 v2 ^ 2 ∧
      0 < deltaX x1 x2 x3 x4 x5 x6 ∧
      v3 = mkSimplex1_p11 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
      x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
        0 < (v1 - v0) ⬝ᵥ (WithLp.toLp 2
          (crossProduct (WithLp.ofLp (v2 - v0)) (WithLp.ofLp (v3 - v0))) : V3)

/-- PQCSXWG.hl:130 `PQCSXWG1` (giant: the distance-realization identity
for `mk_simplex1`; DISCHARGES). -/
theorem PQCSXWG1_p11 : PQCSXWG1_concl_p11 := by
  sorry

/-- PQCSXWG.hl:214 `CONTINUOUS_MK_SIMPLEX_WITHINREAL` (long continuity
choreography; DISCHARGES). -/
theorem CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11
    {v0 v1 v2 : ℝ → V3} {x1 x2 x3 x4 x5 x6 : ℝ → ℝ} {s : Set ℝ} {a : ℝ}
    (hups : upsX (x1 a) (x2 a) (x6 a) ≠ 0)
    (hd : 0 < deltaX (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a))
    (hv0 : ContinuousWithinAt v0 s a) (hv1 : ContinuousWithinAt v1 s a)
    (hv2 : ContinuousWithinAt v2 s a)
    (hx1 : ContinuousWithinAt x1 s a) (hx2 : ContinuousWithinAt x2 s a)
    (hx3 : ContinuousWithinAt x3 s a) (hx4 : ContinuousWithinAt x4 s a)
    (hx5 : ContinuousWithinAt x5 s a) (hx6 : ContinuousWithinAt x6 s a) :
    ContinuousWithinAt
      (fun t => mkSimplex1_p11 (v0 t) (v1 t) (v2 t) (x1 t) (x2 t) (x3 t)
        (x4 t) (x5 t) (x6 t)) s a := by
  sorry

/-- PQCSXWG.hl:256 `PQCSXWG2_WITHINREAL` (giant through
`CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11` and
`Collect_geom2.NOT_COL_EQ_UPS_X_POS`; DISCHARGES). -/
theorem PQCSXWG2_WITHINREAL_p11
    {v0 v1 v2 : ℝ → V3} {x1 x2 x3 x4 x5 x6 : ℝ → ℝ} {s : Set ℝ} {a : ℝ}
    (hnc : ¬Collinear3 (v0 a) (v1 a) (v2 a))
    (hx1 : x1 a = dist (v1 a) (v0 a) ^ 2)
    (hx2 : x2 a = dist (v2 a) (v0 a) ^ 2)
    (hx6 : x6 a = dist (v1 a) (v2 a) ^ 2)
    (hd : 0 < deltaX (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a))
    (hv0 : ContinuousWithinAt v0 s a) (hv1 : ContinuousWithinAt v1 s a)
    (hv2 : ContinuousWithinAt v2 s a)
    (hx1c : ContinuousWithinAt x1 s a) (hx2c : ContinuousWithinAt x2 s a)
    (hx3c : ContinuousWithinAt x3 s a) (hx4c : ContinuousWithinAt x4 s a)
    (hx5c : ContinuousWithinAt x5 s a) (hx6c : ContinuousWithinAt x6 s a) :
    ContinuousWithinAt
      (fun t => mkSimplex1_p11 (v0 t) (v1 t) (v2 t) (x1 t) (x2 t) (x3 t)
        (x4 t) (x5 t) (x6 t)) s a := by
  sorry

/-- PQCSXWG.hl:282 `PQCSXWG2_ATREAL`. -/
theorem PQCSXWG2_ATREAL_p11
    {v0 v1 v2 : ℝ → V3} {x1 x2 x3 x4 x5 x6 : ℝ → ℝ} {a : ℝ}
    (hnc : ¬Collinear3 (v0 a) (v1 a) (v2 a))
    (hx1 : x1 a = dist (v1 a) (v0 a) ^ 2)
    (hx2 : x2 a = dist (v2 a) (v0 a) ^ 2)
    (hx6 : x6 a = dist (v1 a) (v2 a) ^ 2)
    (hd : 0 < deltaX (x1 a) (x2 a) (x3 a) (x4 a) (x5 a) (x6 a))
    (hv0 : ContinuousAt v0 a) (hv1 : ContinuousAt v1 a)
    (hv2 : ContinuousAt v2 a)
    (hx1c : ContinuousAt x1 a) (hx2c : ContinuousAt x2 a)
    (hx3c : ContinuousAt x3 a) (hx4c : ContinuousAt x4 a)
    (hx5c : ContinuousAt x5 a) (hx6c : ContinuousAt x6 a) :
    ContinuousAt
      (fun t => mkSimplex1_p11 (v0 t) (v1 t) (v2 t) (x1 t) (x2 t) (x3 t)
        (x4 t) (x5 t) (x6 t)) a := by
  have h := PQCSXWG2_WITHINREAL_p11 (s := Set.univ) hnc hx1 hx2 hx6 hd
    hv0.continuousWithinAt hv1.continuousWithinAt hv2.continuousWithinAt
    hx1c.continuousWithinAt hx2c.continuousWithinAt hx3c.continuousWithinAt
    hx4c.continuousWithinAt hx5c.continuousWithinAt hx6c.continuousWithinAt
  rwa [continuousWithinAt_univ] at h

/-- PQCSXWG.hl:304 `PQCSXWG2_concl` (statement-registry term). -/
def PQCSXWG2_concl_p11 : Prop :=
  ∀ (v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 ∧ 0 < x2 ∧ 0 < x3 ∧ 0 < x4 ∧ 0 < x5 ∧ 0 < x6 ∧
      ¬Collinear3 v0 v1 v2 ∧
      x1 = dist v1 v0 ^ 2 ∧ x2 = dist v2 v0 ^ 2 ∧ x6 = dist v1 v2 ^ 2 ∧
      0 < deltaX x1 x2 x3 x4 x5 x6 →
      ContinuousAt (fun q => mkSimplex1_p11 v0 v1 v2 x1 x2 x3 x4 q x6) x5

/-- PQCSXWG.hl:314 `PQCSXWG2`. -/
theorem PQCSXWG2_p11 : PQCSXWG2_concl_p11 := by
  intro v0 v1 v2 x1 x2 x3 x4 x5 x6 ⟨h1, h2, h3, h4, h5, h6, hnc, hx1, hx2,
    hx6, hd⟩
  exact PQCSXWG2_ATREAL_p11 hnc hx1 hx2 hx6 hd continuousAt_const
    continuousAt_const continuousAt_const continuousAt_const
    continuousAt_const continuousAt_const continuousAt_const
    continuousAt_id continuousAt_const

/-! ## Section C: TECOXBM.hl — `B_SY1` fan properties -/

/-- NEEDS: HOL `wedge_in_fan_gt` (localization.hl:79): the open wedge of
the dart `e = (v, w)` against `E`, with the two degenerate branches
(`EE v E = {w}`: outside `aff_ge {0,v} {w}`; smaller: outside
`aff {0,v}`).  `wedge (vec 0) v w d` is Kepler.Geom.wedge. -/
noncomputable def wedgeInFanGt_p11 (e : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (EE_p4 e.1 E).ncard then
    Kepler.Geom.wedge 0 e.1 e.2 (azimCycle_p4 (EE_p4 e.1 E) 0 e.1 e.2)
  else if EE_p4 e.1 E = {e.2} then
    {x | x ∉ affGe {0, e.1} {e.2}}
  else
    {x | x ∉ affineSpan ℝ ({0, e.1} : Set V3)}

/-- The ℕ-indexed lift of a `Fin k` coefficient table: TECOXBM's
`stable_system` consumes `a b : num#num->real` while LocalAuto4's
`B_SY1_p4` is `Fin k`-indexed; entries outside `k × k` read 0. -/
def liftAB_p11 {k : ℕ} (a : Fin k → Fin k → ℝ) : ℕ → ℕ → ℝ :=
  fun i j => if h : i < k ∧ j < k then a ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- TECOXBM.hl:39 `CROSS_DOT_POS_SY` (giant through the Local_lemmas
`DETERMINE_WEDGE_IN_FAN`/`PGSQVBL`/`AZIM_PI_WEDGE_GE_CROSS_DOT` chain;
DISCHARGES).  `y`/`z` are rows `i`/`finNext i` of `vecmats l`; the HOL
`(y cross z) dot u` renders via the `Fin 3 → ℝ` crossProduct. -/
theorem CROSS_DOT_POS_SY_p11 {k : ℕ} {a b : Fin k → Fin k → ℝ}
    {J : Finset (Finset ℕ)} {d : ℕ} (hk : 2 < k) (l : FinVec k 3) (u : V3)
    (i : Fin k)
    (hss : stableSystem_p4 k d (Finset.Ico 0 k) (liftAB_p11 a) (liftAB_p11 b) J
      (fun n => (n + 1) % k))
    (hu : u ∈ V_SY_p4 (vecmatsV3_p4 l)) (hl : l ∈ B_SY1_p4 a b) :
    0 ≤ (WithLp.toLp 2
        (crossProduct (WithLp.ofLp (vecmatsV3_p4 l i))
          (WithLp.ofLp (vecmatsV3_p4 l (finNext i)))) : V3) ⬝ᵥ u := by
  sorry

/-- TECOXBM.hl:183 `IVS_RHO_NODE_IN_EDGE` (giant through Local_lemmas
`IVS_RHO_IDD`/`LOFA_IMP_EE_TWO_ELMS`; DISCHARGES). -/
theorem IVS_RHO_NODE_IN_EDGE_p11 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (v : V3) (hf : localFan_p4 V E FF) (hv : v ∈ V) :
    {v, ivsRhoNode1_p2 FF v} ∈ E := by
  sorry

/-- TECOXBM.hl:197 `RHO_IVS_IDD` (giant through Local_lemmas
`IVS_RHO_IDD`; DISCHARGES). -/
theorem RHO_IVS_IDD_p11 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (v : V3) (hf : localFan_p4 V E FF) (hv : v ∈ V) :
    rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := by
  sorry

/-- TECOXBM.hl:207 `PROPERTIES_OF_FAN_IN_B_SY` (giant: row separation
inside `B_SY1`; DISCHARGES). -/
theorem PROPERTIES_OF_FAN_IN_B_SY_p11 {k : ℕ} {a b : Fin k → Fin k → ℝ}
    {J : Finset (Finset ℕ)} {d : ℕ} (hk : 2 < k) (l : FinVec k 3)
    (i j : Fin k) (hij : i ≠ j)
    (hss : stableSystem_p4 k d (Finset.Ico 0 k) (liftAB_p11 a) (liftAB_p11 b) J
      (fun n => (n + 1) % k))
    (hl : l ∈ B_SY1_p4 a b) :
    (2:ℝ) ≤ ‖vecmatsV3_p4 l i - vecmatsV3_p4 l j‖ := by
  sorry

/-- TECOXBM.hl:311 `AFF_GT_INTER_AFF_SY` (giant; DISCHARGES).  HOL
`aff {vec 0, y, z}` renders as `affineSpan ℝ {0, y, z}`. -/
theorem AFF_GT_INTER_AFF_SY_p11 {k : ℕ} {a b : Fin k → Fin k → ℝ}
    {J : Finset (Finset ℕ)} {d : ℕ} (hk : 2 < k) (l : FinVec k 3) (u w : V3)
    (i : Fin k)
    (hss : stableSystem_p4 k d (Finset.Ico 0 k) (liftAB_p11 a) (liftAB_p11 b) J
      (fun n => (n + 1) % k))
    (hsub : {u, w} ⊆ V_SY_p4 (vecmatsV3_p4 l)) (hn1 : ‖u - w‖ ≤ cstab_p4)
    (hn2 : (2:ℝ) ≤ ‖u - w‖)
    (hE : {u, w} ∉ E_SY_p4 (vecmatsV3_p4 l)) (hl : l ∈ B_SY1_p4 a b) :
    affGt {0} {u, w} ∩
        (affineSpan ℝ
          ({0, vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)} : Set V3)) = ∅ := by
  sorry

/-- TECOXBM.hl:1456 `TECOXBM1` (giant through `convex_local_fan` +
`DETERMINE_WEDGE_IN_FAN`; DISCHARGES). -/
theorem TECOXBM1_p11 {k : ℕ} {a b : Fin k → Fin k → ℝ}
    {J : Finset (Finset ℕ)} {d : ℕ} (hk : 2 < k) (l : FinVec k 3) (u w : V3)
    (hss : stableSystem_p4 k d (Finset.Ico 0 k) (liftAB_p11 a) (liftAB_p11 b) J
      (fun n => (n + 1) % k))
    (hsub : {u, w} ⊆ V_SY_p4 (vecmatsV3_p4 l)) (hn1 : ‖u - w‖ ≤ cstab_p4)
    (hn2 : (2:ℝ) ≤ ‖u - w‖)
    (hE : {u, w} ∉ E_SY_p4 (vecmatsV3_p4 l)) (hl : l ∈ B_SY1_p4 a b) :
    ∀ x ∈ F_SY_p4 (vecmatsV3_p4 l),
      affGt {0} {u, w} ⊆ wedgeInFanGt_p11 x (E_SY_p4 (vecmatsV3_p4 l)) := by
  sorry

/-- TECOXBM.hl:1682 `TECOXBM2` (giant through
`NONPARALLEL_BALL_ANNULUS`; DISCHARGES).  HOL
`~(collinear ({vec 0} ∪ {u, w}))` ↔ `¬Collinear3 0 u w`. -/
theorem TECOXBM2_p11 {k : ℕ} {a b : Fin k → Fin k → ℝ}
    {J : Finset (Finset ℕ)} {d : ℕ} (hk : 2 < k) (l : FinVec k 3) (u w : V3)
    (hss : stableSystem_p4 k d (Finset.Ico 0 k) (liftAB_p11 a) (liftAB_p11 b) J
      (fun n => (n + 1) % k))
    (hsub : {u, w} ⊆ V_SY_p4 (vecmatsV3_p4 l)) (hn1 : ‖u - w‖ ≤ cstab_p4)
    (hn2 : (2:ℝ) ≤ ‖u - w‖)
    (hE : {u, w} ∉ E_SY_p4 (vecmatsV3_p4 l)) (hl : l ∈ B_SY1_p4 a b) :
    ¬Collinear3 0 u w := by
  sorry

/-- TECOXBM.hl:1726 `TECOXBM` — the conjunction of TECOXBM1/TECOXBM2
(the HOL proof pairs the two). -/
theorem TECOXBM_p11 {k : ℕ} {a b : Fin k → Fin k → ℝ}
    {J : Finset (Finset ℕ)} {d : ℕ} (hk : 2 < k) (l : FinVec k 3) (u w : V3)
    (hss : stableSystem_p4 k d (Finset.Ico 0 k) (liftAB_p11 a) (liftAB_p11 b) J
      (fun n => (n + 1) % k))
    (hsub : {u, w} ⊆ V_SY_p4 (vecmatsV3_p4 l)) (hn1 : ‖u - w‖ ≤ cstab_p4)
    (hn2 : (2:ℝ) ≤ ‖u - w‖)
    (hE : {u, w} ∉ E_SY_p4 (vecmatsV3_p4 l)) (hl : l ∈ B_SY1_p4 a b) :
    ¬Collinear3 0 u w ∧
      ∀ x ∈ F_SY_p4 (vecmatsV3_p4 l),
        affGt {0} {u, w} ⊆ wedgeInFanGt_p11 x (E_SY_p4 (vecmatsV3_p4 l)) :=
  ⟨TECOXBM2_p11 hk l u w hss hsub hn1 hn2 hE hl,
   TECOXBM1_p11 hk l u w hss hsub hn1 hn2 hE hl⟩

end Kepler.Text

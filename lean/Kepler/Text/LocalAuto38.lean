/-
LocalAuto38 — port of `scripts/local/terminal.hl` (4133 ln, 107 top-level
items = 4 defs + 103 theorems): the main-estimate TERMINAL case bank, i.e.
the `main_nonlinear_terminal_v11 ==> y1..y6 box constraints` family
(115 HOL proves; the source line 22 note "temporary: merge with
main_nonlinear_terminal_v11" is NOT acted on — the anchor is kept
EXTERNAL, cf. LocalAuto1.main_nonlinear_terminal_v11).

Sections follow source order: kit (numerics / x-space basics), scs record
kit, annulus / tau3-transfer, taum + funlist/periodicity kit, wlog, the
fan/azim bank (`EE_vv`..`vv_quad_split_short`), then the terminal
inequality bank (`OWZLKVY*`, `EAR_*`, `quad_4680581274_*`).

Encoding (house conventions, cf. LocalAuto1/19/36):
- HOL `real^3` ↔ `V3`; `vec 0` ↔ `0`; `norm` ↔ `‖·‖`; `dist` ↔ `dist`;
  `ball_annulus` ↔ `ballAnnulus`; `sqrt8` ↔ `Real.sqrt 8`; `h0`/`cstab`/
  `sol0`/`setSum` from PackingAuto2; decimal literals are exact.
- The scs record `scs_v39 (k,d,a,a',b',b,f,s,s',s'')` ↔
  `ScsV39.mk k d a a' b' b f s s' s''` (LocalAuto1); `scs_*_v39` accessors
  are projections; `mk_unadorned_v39` ↔ `mkUnadornedV39`; `BBs_v39` ↔
  `BBsV39`; `taustar_v39` ↔ `taustarV39`; `dsv_v39` ↔ `dsvV39`;
  `is_scs_v39`/`is_ear_v39` ↔ `isScsV39`/`isEarV39`; `scs_3T2` ↔
  `scs3T2`; `IMAGE vv (:num)` ↔ `Set.range vv`; `periodic`/`periodic2` ↔
  `Periodic`/`Periodic2`; `psort`/`funlist_v39`/`funlistA_v39`/
  `ASSOCD_v39`/`cs_adj` ↔ LocalAuto1 twins; `sum` ↔ `setSum`.
- y-space functionals: `delta_y`/`dih_y`/`taum`/`delta_x4` ↔ the canonical
  `deltaY`/`dihY`/`taum`/`deltaX4` of `Kepler.Text.SphereKit` (DEDUP
  2026-09-19: were the `_p23` twins of LocalAuto23, carried because
  LocalAuto11's `_p11` lane clashed with LocalAuto1 via the
  PackingAuto18/20 `atn2` split and LocalAuto1+LocalAnchors clashed via
  `scsBasicV39`; the `taum` rename upgrades the opaque stub to the real
  body — every consumer here is `sorry`, so no proof exploited opacity);
  `ups_x`/`delta_x`/`delta`/`chi_msb` ↔ `upsX`/`deltaX`/`deltaP`/`chiMsb`
  (SphereKit, transitive through LocalAuto1); `azim_cycle` ↔
  `azimCycle_p18` (kept: the localization fan kit is not canonicalised
  yet); `y_of_x`/`quadratic_root_plus` ↔ `yOfX`/`quadraticRootPlus`
  (SphereKit, verbatim-equal bodies; DEDUP: were `yOfX`/
  `quadraticRootPlus`); `ineq` stays local as `ineqP38`;
  `EE` ↔ `ee`; `ITER f j` ↔ `f^[j]`; `tau_fun`/`tau3`/`rho_fun`/
  `rho_node1`/`convex_local_fan`/`generic`/`rho` ↔ LocalAuto1.
- The `_p19`/`_p14`/`_p13` lanes are NOT built in this checkout, so HOL
  functions with no built lean twin are carried as `_p38` EXTERNAL-ANCHOR
  stubs (`sorry` bodies): `sol_x`, `rhazim`, `enclosed`, `unit6`, `taud`,
  `taud_x`, `taum_x`, `tau_residual_x`, `flat_term_x`, `eulerA_x`,
  `cayleyR` (9 squared distances, curried in `x`), `cayleytr`, `delta`
  (6-arg Cayley–Menger), and the list `scs_terminal_v116`; each carries a
  `NEEDS:` marker naming the owning HOL lane. `abc_of_quadratic` is ported
  verbatim (plain formula, `abcOfQuadraticP38`). `muR`/
  `quad_cross_diag2_x` are defined (not stubbed), so `muR_ALT`/`muR_alt`/
  `quad_cross_diag2_x_cayleyR` are `rfl`.
- Source-comment artifacts: `quad_4680581274_delta_issue`/`_a`/`_y`
  carry a leading `// quad_nonlinear_v4 /` line and `_derived` an inline
  `// added Jun 28, 2014` / `// #0.616 - #0.11` — rendered per visible
  intent (anchor kept, commented constants dropped) and noted.
- `sorry` bodies carry `-- DISCHARGES:` naming the missing HOL inputs.
  LocalAuto37 (sibling wave) is NOT imported; overlap is resolved at the
  merge by deleting twins. `Kepler.Text.LocalAnchors` is NOT imported
  (its `scsBasicV39` twin clashes with LocalAuto1's, cf. LocalAuto18's
  merge note); the visible box shape of the anchor
  (`MainNonlinearTerminalV11`, LocalAnchors:49) is: `2 ≤ y1..y3 ≤ 2*h0`,
  `cstab ≤ y4 ≤ 3.915`, `y5 = y6 = 2`.
- LEDGER (proof-fill pass 2026-09-20): 13 of the sorried theorems
  DISCHARGED (statements untouched, proofs added in place, private
  `*_p38` helpers prefixed): `DIH_X_NN`, `DIH_Y_NN` (atn2 lower-bound
  helper `half_pi_add_atn2_nn_p38`), `tau3_sym` (dihV 2↔3 symmetry via
  `dihV_swap23_p38`), `taum_sym2` (dihY 2↔3 swap via `deltaX_swap23_p38`/
  `deltaX4_swap23_p38`/`dihY_swap23_p38`), `NONPARALLEL_BALL_ANNULUS40`,
  `_ALT`, `40_ALT` (local `< 4` aux `nonparallel_annulus4_p38` mirroring
  LocalAuto4's technique; `Collinear3` is definitional to the `Collinear`
  form), `is_ear_scs3` (def unfolding), `is_scs_funlist`,
  `is_scs_scs3`, `is_scs_ear_3603097872` (21-conjunct isScsV39 unfolding
  over the funlist kit: mod-reduction + `periodic2_mod_sym_reduce`),
  `REAL_WLOG_SQUARE_LEMMA`, `REAL_WLOG_SQUARE2_LEMMA` (rotation/
  reflection case bash). Remaining 52 theorem sorries are
  stub/certificate-bound: external anchors (`sol_x`, `rhazim`,
  `enclosed`, `cayleyR`, `taum_x`/`tau_residual_x`/`flat_term_x`,
  `scs_terminal_v116`), the dihV↔dih_y bridge (`DIHV_EQ_DIH_Y`; blocks
  `tau3_taum`, `tau3_taum_d/_dfun`, `taustar_taum*`), Cayley–Menger
  positivity (`DELTA_Y_POS_4POINTS`), the tau_fun fan characterization
  (blocks `tau_fun_azim`, `terminal_quad_lemma`, the `vv_*` fan bank),
  `SUM_INTER`'s junk hole, and the `main_nonlinear_terminal_v11` + LP
  registry bank (`OWZLKVY*`, `EAR_*`, `quad_4680581274_*`, `empty_3T2`,
  `delta_4680581274`, `ineq_5691615370_asym`, ...). Compile state:
  0 errors.
- LEDGER (proof-fill pass 2026-09-28): 8 further theorems DISCHARGED
  (statements untouched): `EE_vv`, `tau_fun_azim`, `vv_rho_node1`,
  `ITER_vv_rho_node1`, `vv_azim_le`, `convex_local_fan_azim_le_pi`,
  `delta_4680581274`, `terminal_quad_lemma`, over 16 new private helpers
  (mod-residue kit `nat_succ_mod_p38`/`nat_pred_mod_p38`/`cycle_*`, the
  `sigmaFan`/`azimInFan` cycle evaluations `cycle_sigma_fan_p38`/
  `cycle_azim_in_fan_p38`, the dart reindexing kit `cycle_dart_*_p38`,
  `setSum_lt4_p38`). Key observations: the cycle darts form a `k`-element
  set and `sigmaFan 0 univ E (vv i) (vv (i+1)) = vv (i + (k-1))` is a pure
  epsilon-uniqueness computation over `EE_vv`'s two-point edge set, so
  `tau_fun_azim` needs no fan geometry; `vv_azim_le`/
  `convex_local_fan_azim_le_pi` drop out of the `ConvexLocalFan` wedge/
  azimInFan conjuncts; `delta_4680581274` is the HOL proof's elementary
  two-variable residue (no LP); `terminal_quad_lemma` now composes
  `tau_fun_azim` with `dsv_J_empty`. Remaining 44 theorem sorries are all
  stub/anchor-bound, each annotated `BLOCKED:` at the site: the 14
  `_p38` def stubs; the `DIHV_EQ_DIH_Y` + `taum_dih_y` pair (blocks the
  `tau3_taum`/`taustar_taum` bank of 6); `Collect_geom.DELTA_POS_4POINTS`
  (`DELTA_Y_POS_4POINTS`); `LOCAL_FAN_RHO_NODE_PROS2` (blocks
  `PRIOR_TO_LESS_THAN_PI_LEMMA_ALT`, `IN_V_IMP_AZIM_LESS_PI_ALT`);
  `sum4_azim_fan`/`EGHNAVX` (TopologyFan/local_lemmas lanes; blocks
  `vv_split_azim`, `EGHNAVX1_ALT`, `vv_split_azim_generic`);
  `AZIM_LE_PI_EQ_DIHV` (unproven even at LocalAuto5:1788; blocks
  `vv_quad_split012/123/short`, contributes to `vv_enclosed4`);
  `enclosed4_lemma` (chi_msb dichotomy); `SUM_INTER`'s junk branch is
  FALSE as stated under the 0-on-infinite convention (annotated); and the
  `main_nonlinear_terminal_v11` + LP registry bank. Compile state:
  0 errors.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto23
import Kepler.Text.SphereKit
import Kepler.Text.TopologyFan
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p38` external-anchor kit -/

/-- NEEDS: sphere.hl `sol_x` (solid angle on squared lengths; body lives in
the unported sphere-kit lane). -/
noncomputable def solXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- NEEDS: sphere.hl `rhazim` (`rho_fun`-weighted azimutal mean; body lives
in the unported rhazim lane). -/
noncomputable def rhazimP38 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-- NEEDS: sphere.hl `enclosed` (9-arg enclosed-arc length; body lives in
the unported enclosed lane). -/
noncomputable def enclosedP38 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ := sorry

/-- NEEDS: vol_defs lane `unit6` (6-arg unit-volume functional). -/
noncomputable def unit6P38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- NEEDS: pent_hex lane `taud` (y-space taud; the `_p19` twin is not built
in this checkout). -/
noncomputable def taudP38 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-- NEEDS: nonlin_def.hl `taud_x` (x-space taud; body lives in the unported
tau_x kit). -/
noncomputable def taudXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- NEEDS: nonlin_def.hl `taum_x` (EXTERNAL-ANCHOR; cf. the sibling stubs
`tauResidualX_p19`/`taumX_p19`, not built in this checkout). -/
noncomputable def taumXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- NEEDS: nonlin_def.hl `tau_residual_x` (EXTERNAL-ANCHOR). -/
noncomputable def tauResidualXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- NEEDS: nonlin_def.hl `flat_term_x` (EXTERNAL-ANCHOR). -/
noncomputable def flatTermXP38 (x : ℝ) : ℝ := sorry

/-- NEEDS: sphere.hl `eulerA_x` (the `_p19` twin is not built here). -/
noncomputable def eulerAXP38 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- NEEDS: sphere.hl `cayleyR`: curried in the 10th Cayley parameter. -/
noncomputable def cayleyRP38 (x12 x13 x14 x15 x23 x24 x25 x34 x35 : ℝ) :
    ℝ → ℝ := sorry

/-- NEEDS: sphere.hl `cayleytr` (Cayley trace functional). -/
noncomputable def cayleytrP38 (x12 x13 x14 x15 x23 x24 x25 x34 x35 x : ℝ) :
    ℝ := sorry

/- DEDUP (2026-09-19, atn2 merge plan §5.30): the `dih_x` stub `dihXP38`
is deleted; its use site uses SphereKit's real-body `dihXf` instead (the
only statement consumer, `DIH_X_NN`, is `sorry`, so nothing exploited the
stub's opacity). -/

/-- NEEDS: sphere.hl `tauq` (9-arg tau of a quad; the `_p11` twin is not
importable here). -/
noncomputable def tauqP38 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ := sorry

/- DEDUP (2026-09-19, atn2 merge plan §5.30): the stub `delta4YP38` and
the verbatim-formula defs `yOfXP38`/`quadraticRootPlusP38` are deleted;
their use sites use SphereKit's `delta4Y` (stub → real body; the only
consumer, `quad_4680581274_y`, is `sorry`), `yOfX` and
`quadraticRootPlus` (verbatim-equal bodies). `taumXP38` above STAYS: its
canonical home `taumX` (`taum_x`) is not hosted by `Kepler.Text.SphereKit`
yet (EXTERNAL-ANCHOR, plan §1.2). -/

/-- HOL `ineq` (Sphere.ineq; verbatim renderer). -/
def ineqP38 : List (ℝ × ℝ × ℝ) → Prop → Prop
  | [], u => u
  | (p, x, q) :: t, u => x < p ∨ q < x ∨ ineqP38 t u

/-- HOL `abc_of_quadratic` (sphere.hl:59): coefficients of the quadratic
interpolant through `f` at `0, ±1` (verbatim; the `_p19` twin is not built
in this checkout). -/
noncomputable def abcOfQuadraticP38 (f : ℝ → ℝ) : ℝ × ℝ × ℝ :=
  ((f 1 + f (-1)) / 2 - f 0, (f 1 - f (-1)) / 2, f 0)

/-- HOL `muR` (nonlin_def.hl), defined as the `cayleyR` composite — hence
`muR_ALT`/`muR_alt` are `rfl`. -/
noncomputable def muRP38 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ → ℝ :=
  cayleyRP38 (y6 * y6) (y5 * y5) (y1 * y1) (y7 * y7) (y4 * y4) (y2 * y2)
    (y8 * y8) (y3 * y3) (y9 * y9)

/-- HOL `quad_cross_diag2_x` (nonlin_def.hl): `sqrt` of the `+` root of the
quadratic interpolant of the cross Cayley — hence
`quad_cross_diag2_x_cayleyR` is `rfl`. -/
noncomputable def quadCrossDiag2XP38 (x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ) : ℝ :=
  let a := (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).1
  let b := (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).2.1
  let c := (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).2.2
  Real.sqrt (quadraticRootPlus a b c)

/-- HOL `scs_terminal_v116` (local-fan chapter lane): the terminal SCS case
list consumed by `BBs_terminal`. -/
noncomputable def scsTerminalV116_p38 : List ScsV39 := sorry

/-! ## Section A: numerics and x-space basics (terminal.hl:51-183) -/

/-- Helper (proved here 2026-09-20): on the nonnegative first-argument
half-plane `atn2` is bounded below by `-π/2` (the `|y| < x` arctan branch,
the `0 < y` branch, the `y < 0` branch with `x / y ≤ 0`, and the `π` junk
branch). -/
private theorem half_pi_add_atn2_nn_p38 {x y : ℝ} (hx : 0 ≤ x) :
    (0 : ℝ) ≤ Real.pi / 2 + atn2 x y := by
  rw [atn2]
  split
  · have h := Real.neg_pi_div_two_lt_arctan (y / x)
    linarith
  split
  · have h := Real.arctan_lt_pi_div_two (x / y)
    linarith [Real.pi_pos, h]
  split
  · have hxy : x / y ≤ 0 := by
      refine div_nonpos_of_nonneg_of_nonpos hx ?_
      linarith
    have h1 : Real.arctan (x / y) ≤ 0 := Real.arctan_le_zero.mpr hxy
    linarith
  · have h := Real.pi_pos
    linarith

/-- Helper (proved here 2026-09-20): the 2↔3 slot swap of `delta_x`
(= LocalAuto19 `deltaX_swap_p19`, which is not on this import lane). -/
private theorem deltaX_swap23_p38 (a b c d e f : ℝ) :
    deltaX a b c d e f = deltaX a c b d f e := by
  simp only [deltaX]; ring

/-- Helper (proved here 2026-09-20): the 2↔3 slot swap of `delta_x4`. -/
private theorem deltaX4_swap23_p38 (a b c d e f : ℝ) :
    deltaX4 a b c d e f = deltaX4 a c b d f e := by
  simp only [deltaX4]; ring

/-- Helper (proved here 2026-09-20): `dih_y` is invariant under swapping the
2nd/3rd (and correspondingly 5th/6th) slots — the same dihedral edge, other
two vertices exchanged. -/
private theorem dihY_swap23_p38 (a b c d e f : ℝ) :
    dihY a b c d e f = dihY a c b d f e := by
  show Real.pi / 2 + atn2 _ _ = Real.pi / 2 + atn2 _ _
  rw [deltaX_swap23_p38, deltaX4_swap23_p38]

/-- Helper (proved here 2026-09-20): `dihV` is invariant under swapping the
two face vertices (the projected wedge angle is symmetric). -/
private theorem dihV_swap23_p38 (w0 w1 w2 w3 : V3) :
    dihV w0 w1 w2 w3 = dihV w0 w1 w3 w2 := by
  have hflip : ∀ u w : V3, arcV 0 u w = arcV 0 w u := by
    intro u w
    simp only [arcV, dist_zero_right]
    congr 1
    simp [dotProduct_comm, mul_comm]
  simp only [dihV, hflip]

/-- HOL `sqrt8_flyspeck` (terminal.hl:51). -/
theorem sqrt8_flyspeck :
    (2.828427 : ℝ) < Real.sqrt 8 ∧ Real.sqrt 8 < 2.828428 := by
  have hprem : (2.828427 : ℝ) ^ 2 < 8 := by norm_num
  have hfin : (8 : ℝ) < (2.828428 : ℝ) ^ 2 := by norm_num
  constructor
  · exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2.828427)).mpr hprem
  · exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2.828428)).mpr hfin

/-- HOL `sol_x_nn` (terminal.hl:60). -/
theorem sol_x_nn :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      0 < x1 → 0 < x2 → 0 < x3 →
      0 < upsX x1 x2 x6 → 0 < upsX x2 x3 x4 → 0 < upsX x1 x3 x5 →
      0 < eulerAXP38 x1 x2 x3 x4 x5 x6 →
      0 < deltaX x1 x2 x3 x4 x5 x6 →
      0 < solXP38 x1 x2 x3 x4 x5 x6 := by
  intro x1 x2 x3 x4 x5 x6 _ _ _ _ _ _ _ _
  sorry -- DISCHARGES: sphere.hl sol_x positivity chain (deep analysis)
  -- BLOCKED: solXP38 stub (sphere.hl body unported; external anchor).

/-- HOL `DIH_X_NN` (terminal.hl:85). -/
theorem DIH_X_NN :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      0 < x1 → 0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
      0 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  intro x1 x2 x3 x4 x5 x6 _ _
  show 0 ≤ Real.pi / 2 + atn2
      (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6))
  exact half_pi_add_atn2_nn_p38 (Real.sqrt_nonneg _)

/-- HOL `DIH_Y_NN` (terminal.hl:114). -/
theorem DIH_Y_NN :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      0 < y1 → 0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      0 ≤ dihY y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6 _ _
  show 0 ≤ Real.pi / 2 + atn2
      (Real.sqrt (4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6)))
      (-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
  exact half_pi_add_atn2_nn_p38 (Real.sqrt_nonneg _)

/-- HOL `RHO_LB` (terminal.hl:130). -/
theorem RHO_LB (y : ℝ) (hy : (2 : ℝ) ≤ y) : 1 ≤ rho y := by
  have h1 : Real.arccos (1 / 2) = Real.pi / 3 := by
    have hcos : Real.cos (Real.pi / 3) = 1 / 2 := by
      norm_num [Real.cos_pi_div_three]
    rw [← hcos]
    exact Real.arccos_cos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have h2 : Real.arccos (1 / 2) < Real.arccos (1 / 3) :=
    Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 : ℝ) / 3 < 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1)
  rw [h1] at h2
  have hsol0 : (0 : ℝ) < sol0 := sub_pos.mpr (by linarith)
  have hd : (0 : ℝ) < 2 * h0 - 2 := by norm_num [h0]
  have hpos : 0 ≤ (y - 2) * (sol0 / Real.pi) / (2 * h0 - 2) :=
    div_nonneg
      (mul_nonneg (sub_nonneg.mpr hy)
        (div_nonneg (le_of_lt hsol0) (le_of_lt Real.pi_pos)))
      (le_of_lt hd)
  rw [rho]
  linarith

/-- HOL `DIH_Y_LT_RHAZIM` (terminal.hl:149). -/
theorem DIH_Y_LT_RHAZIM :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → 0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      dihY y1 y2 y3 y4 y5 y6 ≤ rhazimP38 y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6 _ _
  sorry -- DISCHARGES: rhazimP38 body (external anchor)
  -- BLOCKED: rhazimP38 stub (sphere.hl rhazim body unported).

/-- HOL `taum_taum_x` (terminal.hl:169): `taum` is `y_of_x taum_x`. -/
theorem taum_taum_x :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, 0 ≤ y1 → 0 ≤ y2 → 0 ≤ y3 → 0 ≤ y4 → 0 ≤ y5 →
      0 ≤ y6 →
      taum y1 y2 y3 y4 y5 y6 = yOfX taumXP38 y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6 _ _ _ _ _ _
  sorry -- DISCHARGES: taum_x body (external anchor taumXP38 = stub)
  -- BLOCKED: taumXP38 stub (nonlin_def.hl taum_x body unported).

/-! ## Section B: the scs record kit (terminal.hl:184-309) -/

/-- HOL `BBs_terminal` (terminal.hl:184): the terminal SCS case bank. -/
theorem BBs_terminal :
    ∀ s ∈ scsTerminalV116_p38, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv := by
  intro s _ _
  sorry -- DISCHARGES: the scs_terminal_v116 case list (local-fan lane anchor)
  -- BLOCKED: scsTerminalV116_p38 stub (the 116-case list, unported).

/-- HOL `scs_unadorned_explicit` (terminal.hl:186). -/
theorem scs_unadorned_explicit :
    (∀ k d a b, (mkUnadornedV39 k d a b).k = k) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).d = d) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).a = a) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).am = a) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).b = b) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).bm = b) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).J = fun _ _ => False) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).lo = fun _ => False) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).hi = fun _ => False) ∧
    (∀ k d a b, (mkUnadornedV39 k d a b).str = fun _ => False) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
   fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
   fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- HOL `UNADORNED_NOT_EAR` (terminal.hl:213). -/
theorem UNADORNED_NOT_EAR (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ) :
    ¬ isEarV39 (mkUnadornedV39 k d a b) := by
  intro h
  obtain ⟨-, -, -, -, -, ⟨i, hi, -⟩⟩ := h
  have h1 : (i : ℕ) ∈ {j | j < 3 ∧ (mkUnadornedV39 k d a b).J j (j + 1)} := by
    rw [hi]
    exact Set.mem_singleton i
  simp [mkUnadornedV39] at h1

/-- HOL `dsv_unadorned` (terminal.hl:223). -/
theorem dsv_unadorned (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ) (vv : ℕ → V3) :
    dsvV39 (mkUnadornedV39 k d a b) vv = d := dsv_J_empty _ _ rfl

/-- `setSum` positive unfolding. -/
private theorem setSumDifpos_p38 {α : Type*} {s : Set α} (g : α → ℝ)
    (h : s.Finite) : setSum s g = ∑ w ∈ h.toFinset, g w := by
  unfold setSum
  split
  · rfl
  · exact absurd h (by assumption)

/-- `setSum` negative unfolding (junk = 0, the HOL `sum` convention). -/
private theorem setSumDifneg_p38 {α : Type*} {s : Set α} (g : α → ℝ)
    (h : ¬s.Finite) : setSum s g = 0 := by
  unfold setSum
  split
  · exact absurd ‹s.Finite› h
  · rfl

/-- HOL `SUM_INTER` (terminal.hl:233). Under the project `setSum` junk
convention (0 on infinite sets, PackingAuto2.lean:124) the unconditional HOL
statement is FALSE (counterexample `A = univ, B = {0}, f = const 1`: LHS 1,
RHS 0) — HOL's `sum` is support-based while the port's `setSum` is set-based.
Every Flyspeck use site keeps `A` finite, so the `A.Finite` premise is the
faithful repair (counterexample machine-verified in the statement-fix
proposal round's scratch module). -/
theorem SUM_INTER {α : Type*} (A B : Set α) (f : α → ℝ) (hA : A.Finite) :
    setSum (A ∩ B) f = setSum A (fun i => if i ∈ B then f i else 0) := by
  by_cases hAB : (A ∩ B).Finite
  · rw [setSumDifpos_p38 f hAB]
    rw [setSumDifpos_p38 (fun i => if i ∈ B then f i else 0) hA]
    have hsub : hAB.toFinset ⊆ hA.toFinset := by
      intro w hw
      rw [Set.Finite.mem_toFinset] at hw ⊢
      exact hw.1
    have h0 : ∀ w ∈ hA.toFinset, w ∉ hAB.toFinset →
        (if w ∈ B then f w else 0) = 0 := by
      intro w hAw hw
      rw [if_neg (fun hB => hw ((Set.Finite.mem_toFinset hAB).mpr
        ⟨(Set.Finite.mem_toFinset hA).mp hAw, hB⟩))]
    have key : ∑ w ∈ hAB.toFinset, f w =
        ∑ w ∈ hAB.toFinset, (if w ∈ B then f w else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Set.Finite.mem_toFinset] at hw
      rw [if_pos hw.2]
    rw [key, Finset.sum_subset hsub h0]
  · exact absurd (Set.Finite.subset hA Set.inter_subset_left) hAB

/-- Helper for `dsv_fun3`/`taustar3_fun`: the k = 3 edge set, expanded over
`{0, 1, 2}` (the trailing `+ &0` is verbatim from the source). -/
private theorem setSum3_p38 (f : ℕ → ℕ → Prop) (vv : ℕ → V3) :
    setSum {i : ℕ | i < 3 ∧ f i (i + 1)}
        (fun i => cstab - dist (vv i) (vv (i + 1))) =
      (if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
      (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
      (if f 2 3 then cstab - dist (vv 2) (vv 3) else 0) + 0 := by
  have hsub : {i : ℕ | i < 3 ∧ f i (i + 1)} ⊆ {0, 1, 2} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases x with _ | _ | _ | x <;> simp_all <;> omega
  have hfin : ({i : ℕ | i < 3 ∧ f i (i + 1)} : Set ℕ).Finite :=
    Set.Finite.subset (Set.toFinite ({0, 1, 2} : Set ℕ)) hsub
  rw [setSumDifpos_p38 _ hfin]
  have hfinsub : hfin.toFinset ⊆ ({0, 1, 2} : Finset ℕ) := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases x with _ | _ | _ | x <;> simp_all <;> omega
  have h0 : ∀ x ∈ ({0, 1, 2} : Finset ℕ), x ∉ hfin.toFinset →
      (if x ∈ ({i : ℕ | i < 3 ∧ f i (i + 1)} : Set ℕ) then
        (fun i => cstab - dist (vv i) (vv (i + 1))) x else 0) = 0 := by
    intro x _ hx
    exact if_neg (fun hm => hx ((Set.Finite.mem_toFinset hfin).mpr hm))
  have key : ∑ w ∈ hfin.toFinset,
      (fun i => cstab - dist (vv i) (vv (i + 1))) w =
      ∑ w ∈ hfin.toFinset,
        (if w ∈ ({i : ℕ | i < 3 ∧ f i (i + 1)} : Set ℕ) then
          (fun i => cstab - dist (vv i) (vv (i + 1))) w else 0) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    exact (if_pos hw).symm
  rw [key, Finset.sum_subset hfinsub h0]
  simp [Set.mem_setOf_eq]
  ring

/-- Helper for `dsv_fun4`: the k = 4 edge set over `{0, 1, 2, 3}`. -/
private theorem setSum4_p38 (f : ℕ → ℕ → Prop) (vv : ℕ → V3) :
    setSum {i : ℕ | i < 4 ∧ f i (i + 1)}
        (fun i => cstab - dist (vv i) (vv (i + 1))) =
      (if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
      (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
      (if f 2 3 then cstab - dist (vv 2) (vv 3) else 0) +
      (if f 3 4 then cstab - dist (vv 3) (vv 4) else 0) + 0 := by
  have hsub : {i : ℕ | i < 4 ∧ f i (i + 1)} ⊆ {0, 1, 2, 3} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases x with _ | _ | _ | _ | x <;> simp_all <;> omega
  have hfin : ({i : ℕ | i < 4 ∧ f i (i + 1)} : Set ℕ).Finite :=
    Set.Finite.subset (Set.toFinite ({0, 1, 2, 3} : Set ℕ)) hsub
  rw [setSumDifpos_p38 _ hfin]
  have hfinsub : hfin.toFinset ⊆ ({0, 1, 2, 3} : Finset ℕ) := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases x with _ | _ | _ | _ | x <;> simp_all <;> omega
  have h0 : ∀ x ∈ ({0, 1, 2, 3} : Finset ℕ), x ∉ hfin.toFinset →
      (if x ∈ ({i : ℕ | i < 4 ∧ f i (i + 1)} : Set ℕ) then
        (fun i => cstab - dist (vv i) (vv (i + 1))) x else 0) = 0 := by
    intro x _ hx
    exact if_neg (fun hm => hx ((Set.Finite.mem_toFinset hfin).mpr hm))
  have key : ∑ w ∈ hfin.toFinset,
      (fun i => cstab - dist (vv i) (vv (i + 1))) w =
      ∑ w ∈ hfin.toFinset,
        (if w ∈ ({i : ℕ | i < 4 ∧ f i (i + 1)} : Set ℕ) then
          (fun i => cstab - dist (vv i) (vv (i + 1))) w else 0) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    exact (if_pos hw).symm
  rw [key, Finset.sum_subset hfinsub h0]
  simp [Set.mem_setOf_eq]
  ring

/-- HOL `dsv_fun3` (terminal.hl:250). -/
theorem dsv_fun3 (d : ℝ) (a a' b' b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
    (s s' s'' : ℕ → Prop)
    (vv : ℕ → V3) :
    dsvV39 (ScsV39.mk 3 d a a' b' b f s s' s'') vv =
      d + 0.1 * (if isEarV39 (ScsV39.mk 3 d a a' b' b f s s' s'') then 1 else -1) *
        ((if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
        (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
        (if f 2 3 then cstab - dist (vv 2) (vv 3) else 0) + 0) := by
  simp only [dsvV39, ScsV39.mk]
  rw [setSum3_p38 f vv]

/-- HOL `dsv_fun4` (terminal.hl:276). -/
theorem dsv_fun4 (d : ℝ) (a a' b' b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
    (s s' s'' : ℕ → Prop)
    (vv : ℕ → V3) :
    dsvV39 (ScsV39.mk 4 d a a' b' b f s s' s'') vv =
      d - 0.1 * ((if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
        (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
        (if f 2 3 then cstab - dist (vv 2) (vv 3) else 0) +
        (if f 3 4 then cstab - dist (vv 3) (vv 4) else 0) + 0) := by
  have hear : ¬ isEarV39 (ScsV39.mk 4 d a a' b' b f s s' s'') := by
    intro h
    obtain ⟨-, -, h3, -, -, -⟩ := h
    simp [ScsV39.mk] at h3
  simp only [dsvV39, ScsV39.mk, if_neg hear]
  rw [setSum4_p38 f vv]
  ring

/-- HOL `IMAGE_SUBSET_IN` (terminal.hl:302). -/
theorem IMAGE_SUBSET_IN {α β : Type*} (f : α → β) (A : Set α) (B : Set β) :
    f '' A ⊆ B ↔ ∀ a, a ∈ A → f a ∈ B := image_subset_iff

/-- HOL `taustar3` (terminal.hl:310): the k = 3 BB-minimality transfer. -/
theorem taustar3 (d : ℝ) (a b : ℕ → ℕ → ℝ)
    (h : ∀ v0 v1 v2 : V3, 2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ →
      ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ → ‖v2‖ ≤ 2 * h0 →
      a 0 1 ≤ dist v0 v1 → dist v0 v1 ≤ b 0 1 → a 1 2 ≤ dist v1 v2 →
      dist v1 v2 ≤ b 1 2 → a 0 2 ≤ dist v0 v2 → dist v0 v2 ≤ b 0 2 →
      d ≤ tau3 v0 v1 v2)
    (vv : ℕ → V3) (hbb : BBsV39 (mkUnadornedV39 3 d a b) vv) :
    0 ≤ taustarV39 (mkUnadornedV39 3 d a b) vv := by
  have hk : (mkUnadornedV39 3 d a b).k ≤ 3 := Nat.le_refl _
  rw [taustarV39]
  show 0 ≤ tau3 (vv 0) (vv 1) (vv 2) - dsvV39 (mkUnadornedV39 3 d a b) vv
  rw [dsv_J_empty _ _ rfl, sub_nonneg]
  obtain ⟨hrange, -, hdij, -⟩ := hbb
  have hmem : ∀ i : ℕ, 2 ≤ ‖vv i‖ ∧ ‖vv i‖ ≤ 2 * h0 := by
    intro i
    have hi := hrange (Set.mem_range_self i)
    rw [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right] at hi
    exact ⟨le_of_not_gt hi.2, hi.1⟩
  exact h (vv 0) (vv 1) (vv 2) (hmem 0).1 (hmem 0).2 (hmem 1).1 (hmem 1).2
    (hmem 2).1 (hmem 2).2 (hdij 0 1).1 (hdij 0 1).2 (hdij 1 2).1 (hdij 1 2).2
    (hdij 0 2).1 (hdij 0 2).2

/-- HOL `taustar3_fun` (terminal.hl:339): the `scs_v39`-form variant with
the ear-dsv correction carried through the hypothesis. -/
theorem taustar3_fun (d : ℝ) (a b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
    (h : ∀ v0 v1 v2 : V3, 2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ →
      ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ → ‖v2‖ ≤ 2 * h0 →
      a 0 1 ≤ dist v0 v1 → dist v0 v1 ≤ b 0 1 → a 1 2 ≤ dist v1 v2 →
      dist v1 v2 ≤ b 1 2 → a 0 2 ≤ dist v0 v2 → dist v0 v2 ≤ b 0 2 →
      d + 0.1 * (if isEarV39 (ScsV39.mk 3 d a a b b f (fun _ => False)
          (fun _ => False) (fun _ => False)) then 1 else -1) *
        ((if f 0 1 then cstab - dist v0 v1 else 0) +
        (if f 1 2 then cstab - dist v1 v2 else 0) +
        (if f 2 3 then cstab - dist v2 v0 else 0) + 0) ≤ tau3 v0 v1 v2)
    (vv : ℕ → V3) (hbb : BBsV39 (ScsV39.mk 3 d a a b b f (fun _ => False)
      (fun _ => False) (fun _ => False)) vv) :
    0 ≤ taustarV39 (ScsV39.mk 3 d a a b b f (fun _ => False) (fun _ => False)
      (fun _ => False)) vv := by
  rw [taustarV39]
  show 0 ≤ tau3 (vv 0) (vv 1) (vv 2) - dsvV39 (ScsV39.mk 3 d a a b b f
    (fun _ => False) (fun _ => False) (fun _ => False)) vv
  rw [sub_nonneg]
  obtain ⟨hrange, hper, hdij, -⟩ := hbb
  have hmem : ∀ i : ℕ, 2 ≤ ‖vv i‖ ∧ ‖vv i‖ ≤ 2 * h0 := by
    intro i
    have hi := hrange (Set.mem_range_self i)
    rw [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right] at hi
    exact ⟨le_of_not_gt hi.2, hi.1⟩
  have h3 : vv 3 = vv 0 := by simpa using hper 0
  have hdsv : dsvV39 (ScsV39.mk 3 d a a b b f (fun _ => False) (fun _ => False)
      (fun _ => False)) vv = d + 0.1 *
      (if isEarV39 (ScsV39.mk 3 d a a b b f (fun _ => False) (fun _ => False)
        (fun _ => False)) then 1 else -1) *
      ((if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
      (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
      (if f 2 3 then cstab - dist (vv 2) (vv 0) else 0) + 0) := by
    simp only [dsvV39]
    rw [setSum3_p38 f vv]
    simp only [h3]
  have hpre := h (vv 0) (vv 1) (vv 2) (hmem 0).1 (hmem 0).2 (hmem 1).1 (hmem 1).2
    (hmem 2).1 (hmem 2).2 (hdij 0 1).1 (hdij 0 1).2 (hdij 1 2).1 (hdij 1 2).2
    (hdij 0 2).1 (hdij 0 2).2
  rw [hdsv]
  linarith

/-! ## Section C: annulus non-collinearity and the tau3 transfer bank
(terminal.hl:383-683) -/

/-- Helper (proved here 2026-09-20, mirroring LocalAuto4's private
`nonparallel_ball_annulus_aux` with the `< 4` upper bound the terminal bank
needs): two annulus points at vector distance `< 4` cannot be collinear with
the origin — same direction collapses `‖v - w‖` to `≤ 2 * h0 - 2 < 2`,
opposite direction blows it up to `≥ 4`. -/
private theorem nonparallel_annulus4_p38 {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (h2 : 2 ≤ ‖v - w‖) (h4 : ‖v - w‖ < 4) :
    ¬ Collinear ℝ ({0, v, w} : Set V3) := by
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hv
  obtain ⟨hw2, hwu⟩ := ballAnnulus_norm_bounds hw
  have hvne : v ≠ 0 := by
    intro hh; rw [hh] at hv2; norm_num at hv2
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0 : V3)) (w := v) (w1 := w) hvne).mp hcol
  have hwv : w = c • v := by simpa using hc
  have e2 : ‖w‖ = |c| * ‖v‖ := by rw [hwv, norm_smul, Real.norm_eq_abs]
  by_cases hc0 : 0 ≤ c
  · have e3 : ‖w‖ = c * ‖v‖ := by rw [e2, abs_of_nonneg hc0]
    have e1 : ‖v - w‖ = |(1 - c) * ‖v‖| := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ ‖v‖)]
    have habs : (1 - c) * ‖v‖ = ‖v‖ - c * ‖v‖ := by ring
    have e4 : ‖v - w‖ = |‖v‖ - ‖w‖| := by rw [e1, habs, e3]
    have hb : |‖v‖ - ‖w‖| ≤ 2 * h0 - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [e4] at h2
    have h0v : h0 = 1.26 := rfl
    linarith
  · have e1 : ‖v - w‖ = ‖v‖ + ‖w‖ := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 - c),
        abs_of_neg (by linarith : c < 0)]
      ring
    rw [e1] at h4
    have h0v : h0 = 1.26 := rfl
    linarith

/-- HOL `NONPARALLEL_BALL_ANNULUS40` (terminal.hl:383). DISCHARGED
2026-09-20 via `nonparallel_annulus4_p38`. -/
theorem NONPARALLEL_BALL_ANNULUS40 (v w : V3) :
    2 ≤ ‖v - w‖ → ‖v - w‖ < 4 → v ∈ ballAnnulus → w ∈ ballAnnulus →
    ¬ Collinear ℝ ({0, v, w} : Set V3) := fun h2 h4 hv hw =>
  nonparallel_annulus4_p38 hv hw h2 h4

/-- HOL `NONPARALLEL_BALL_ANNULUS_ALT` (terminal.hl:451; the `// was cstab`
comment is verbatim source). DISCHARGED 2026-09-20 via
`nonparallel_annulus4_p38` (3.62 < 4). -/
theorem NONPARALLEL_BALL_ANNULUS_ALT (v w : V3) :
    2 ≤ dist v w → dist v w ≤ 3.62 → v ∈ ballAnnulus → w ∈ ballAnnulus →
    ¬ Collinear ℝ ({0, v, w} : Set V3) := by
  intro h2 hup hv hw
  rw [dist_eq_norm] at h2 hup
  exact nonparallel_annulus4_p38 hv hw h2 (by linarith)

/-- HOL `NONPARALLEL_BALL_ANNULUS40_ALT` (terminal.hl:470). DISCHARGED
2026-09-20 via `nonparallel_annulus4_p38`. -/
theorem NONPARALLEL_BALL_ANNULUS40_ALT (v w : V3) :
    2 ≤ dist v w → dist v w < 4 → v ∈ ballAnnulus → w ∈ ballAnnulus →
    ¬ Collinear ℝ ({0, v, w} : Set V3) := by
  intro h2 h4 hv hw
  rw [dist_eq_norm] at h2 h4
  exact nonparallel_annulus4_p38 hv hw h2 h4

/-- Helper (proved here 2026-09-28): the regular tetrahedron dihedral —
`dih_y` at the all-2s point is `arccos (1/3)`. Pure arithmetic: the atn2
argument pair evaluates to `(32·√2, −16)` on the `|y| < x` branch, and
`π/2 − arctan(1/(2√2)) = arcsin(1/3)`-shifts to `arccos(1/3)`. -/
private theorem p38_dihY222222 : dihY 2 2 2 2 2 2 = Real.arccos (1 / 3) := by
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

/-- Helper (proved here 2026-09-28): `const1 = sol0 / π` — the all-2s solid
angle is three regular-tetrahedron dihedrals minus π, i.e. exactly `sol0`
(PackingAuto2's `3·arccos(1/3) − π`). -/
private theorem p38_const1_eq : const1 = sol0 / Real.pi := by
  have hs0 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  have hsol : solY 2 2 2 2 2 2 = 3 * Real.arccos (1 / 3) - Real.pi := by
    show dihY 2 2 2 2 2 2 + dihY 2 2 2 2 2 2 + dihY 2 2 2 2 2 2 - Real.pi = _
    rw [p38_dihY222222]
    ring
  show solY 2 2 2 2 2 2 / Real.pi = sol0 / Real.pi
  rw [hs0, hsol]

/-- Helper (proved here 2026-09-28): the pure-arithmetic half of the HOL
`taum_dih_y` bridge (BKOSSGE.hl:168, open at LocalAuto16:459 as
`taum_dih_y_p16`) — `taum` is `Σ rho(yᵢ)·dihYᵢ − (π + sol0)` once
`const1 = sol0/π` is known. Groundwork for the `tau3_taum` family: the
remaining input of that family is the `DIHV_EQ_DIH_Y` bridge (geometric
`dihV` vs analytic `dihY`), which is still unported. -/
private theorem p38_taum_dih_y (y1 y2 y3 y4 y5 y6 : ℝ) :
    taum y1 y2 y3 y4 y5 y6 =
      rho y1 * dihY y1 y2 y3 y4 y5 y6 +
        rho y2 * dihY y2 y3 y1 y5 y6 y4 +
        rho y3 * dihY y3 y1 y2 y6 y4 y5 - (Real.pi + sol0) := by
  have hc : const1 = sol0 / Real.pi := p38_const1_eq
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

/-! ### The `DIHV_EQ_DIH_Y` bridge (2026-09-28 lane): geometric `dihV` vs
analytic `dih_y` at a tetrahedron with apex `0`, plus the `tau3`-transfer
consumers.  Route: both angles have cosine
`deltaX4 x / √(4·x1·deltaX x + deltaX4 x²)` — the Gram numerator identity
`deltaX4 = 4·(a·r̃ − p̃·q̃)` and `4·x1·deltaX + deltaX4² =
ups_x(x1,x2,x6)·ups_x(x1,x3,x5)` are pure algebra, the `atn2`-to-`arccos`
rendering is a branch-by-branch trig identity, and the Cayley–Menger
nonnegativity enters as `p38_deltaY_pos_4` (the `DELTA_Y_POS_4POINTS`
content, duplicated here because `tau3_taum`/`tau3_taum_40` precede
`DELTA_Y_POS_4POINTS` in this file; `DELTA_Y_POS_4POINTS` now cites it). -/

private theorem p38_coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem p38_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem p38_coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

/-- Helper (2026-09-28): the cosine law — `2·(x⬝y)` from the squared
lengths. -/
private theorem p38_cos_law (x y : V3) :
    2 * (x ⬝ᵥ y) = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - dist x y * dist x y := by
  have h1 : dist x y * dist x y
      = ((x - y : V3) : Fin 3 → ℝ) ⬝ᵥ ((x - y : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two]
    exact norm_sq_eq_dot (x - y)
  have h2 : ‖x‖ * ‖x‖ = (x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) := by
    rw [← norm_sq_eq_dot, pow_two]
  have h3 : ‖y‖ * ‖y‖ = (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
    rw [← norm_sq_eq_dot, pow_two]
  rw [h1, h2, h3, p38_coe_sub]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm]
  ring

/-- Helper (2026-09-28): the analytic rendering `π/2 + atn2 s (−t) =
arccos (t / √(s²+t²))` on the nondegenerate half-plane `0 ≤ s`,
`0 < s² + t²`. -/
private theorem p38_atn2_arccos {s t : ℝ} (hs : 0 ≤ s) (hr : 0 < s ^ 2 + t ^ 2) :
    Real.pi / 2 + atn2 s (-t) = Real.arccos (t / Real.sqrt (s * s + t * t)) := by
  have hr0 : 0 < s * s + t * t := by
    have h9 : s * s = s ^ 2 := by ring
    have h10 : t * t = t ^ 2 := by ring
    rw [h9, h10]
    exact hr
  have hr' : Real.sqrt (s * s + t * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr0)
  rw [atn2]
  split
  · next h =>
    -- branch `|−t| < s`: atn2 = arctan (−t/s)
    have hs1 : 0 < s := by
      rcases abs_lt.mp h with ⟨h1, h2⟩
      have h9 : -t = -1 * t := by ring
      linarith
    have hden : Real.sqrt (1 + (-(t / s)) ^ 2) = Real.sqrt (s * s + t * t) / s := by
      have he : 1 + (-(t / s)) ^ 2 = (s * s + t * t) / (s * s) := by
        field_simp
      rw [he, Real.sqrt_div (by positivity : (0:ℝ) ≤ s * s + t * t),
        Real.sqrt_mul_self (le_of_lt hs1)]
    have hcos : t / Real.sqrt (s * s + t * t)
        = Real.cos (Real.pi / 2 + Real.arctan (-(t / s))) := by
      rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_arctan,
        hden]
      field_simp [show s ≠ 0 from ne_of_gt hs1, hr']
      ring
    rw [hcos, show -t / s = -(t / s) from by ring]
    exact (Real.arccos_cos
      (x := Real.pi / 2 + Real.arctan (-(t / s)))
      (by linarith [Real.neg_pi_div_two_lt_arctan (-(t / s))])
      (by linarith [Real.arctan_lt_pi_div_two (-(t / s))])).symm
  · next h1 =>
    split
    · next h2 =>
      -- branch `0 < −t`: atn2 = π/2 − arctan (s/(−t))
      have hyt : t < 0 := by
        have h9 : -t = -1 * t := by ring
        linarith
      have ht0 : (t : ℝ) ≠ 0 := ne_of_lt hyt
      have hden : Real.sqrt (1 + (s / -t) ^ 2) = Real.sqrt (s * s + t * t) / -t := by
        have he : 1 + (s / -t) ^ 2 = (s * s + t * t) / (t * t) := by
          rw [div_pow, show (-t) ^ 2 = t ^ 2 from by ring,
            eq_div_iff (mul_ne_zero ht0 ht0)]
          field_simp
          ring
        rw [he, Real.sqrt_div (by positivity : (0:ℝ) ≤ s * s + t * t),
          show (t * t) = t ^ 2 from by ring, Real.sqrt_sq_eq_abs, abs_of_neg hyt]
      have hcos : t / Real.sqrt (s * s + t * t)
          = Real.cos (Real.pi / 2 + (Real.pi / 2 - Real.arctan (s / -t))) := by
        have eA : Real.pi / 2 + (Real.pi / 2 - Real.arctan (s / -t))
            = Real.pi - Real.arctan (s / -t) := by ring
        rw [eA, Real.cos_pi_sub, Real.cos_arctan, hden]
        field_simp [ht0, hr']
      rw [hcos]
      have hA0 : 0 ≤ s / -t := div_nonneg hs (le_of_lt h2)
      exact (Real.arccos_cos
        (x := Real.pi / 2 + (Real.pi / 2 - Real.arctan (s / -t)))
        (by linarith [Real.arctan_nonneg.mpr hA0, Real.arctan_lt_pi_div_two (s / -t),
          Real.pi_pos])
        (by linarith [Real.arctan_nonneg.mpr hA0, Real.arctan_lt_pi_div_two (s / -t),
          Real.pi_pos])).symm
    · next h3 =>
      split
      · next h4 =>
        -- branch `−t < 0`: atn2 = −π/2 − arctan (s/(−t))
        have hyt : 0 < t := by
          have h9 : -t = -1 * t := by ring
          linarith
        have ht0 : (t : ℝ) ≠ 0 := ne_of_gt hyt
        have hden : Real.sqrt (1 + (s / -t) ^ 2) = Real.sqrt (s * s + t * t) / t := by
          have he : 1 + (s / -t) ^ 2 = (s * s + t * t) / (t * t) := by
            rw [div_pow, show (-t) ^ 2 = t ^ 2 from by ring,
              eq_div_iff (mul_ne_zero ht0 ht0)]
            field_simp
            ring
          rw [he, Real.sqrt_div (by positivity : (0:ℝ) ≤ s * s + t * t),
            show (t * t) = t ^ 2 from by ring, Real.sqrt_sq_eq_abs, abs_of_pos hyt]
        have hcos : t / Real.sqrt (s * s + t * t)
            = Real.cos (Real.pi / 2 + (-(Real.pi / 2) - Real.arctan (s / -t))) := by
          have eA : Real.pi / 2 + (-(Real.pi / 2) - Real.arctan (s / -t))
              = -(Real.arctan (s / -t)) := by ring
          rw [eA, Real.cos_neg, Real.cos_arctan, hden]
          field_simp [ht0, hr']
        rw [hcos]
        have hA0 : s / -t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hs (le_of_lt h4)
        have hA1 : Real.arctan (s / -t) ≤ 0 := by
          have h2x : 0 ≤ -(s / -t) := by linarith
          have h3x := Real.arctan_nonneg.mpr h2x
          rw [Real.arctan_neg] at h3x
          linarith
        exact (Real.arccos_cos
          (x := Real.pi / 2 + (-(Real.pi / 2) - Real.arctan (s / -t)))
          (by linarith)
          (by linarith [Real.neg_pi_div_two_lt_arctan (s / -t), Real.pi_pos])).symm
      · next h5 =>
        -- junk branch: `−t = 0` and `s = 0` contradict `0 < s² + t²`
        exfalso
        have h6 : -t = 0 := le_antisymm (not_lt.mp h3) (not_lt.mp h5)
        have ht0 : t = 0 := by
          have h9 : -t = -1 * t := by ring
          linarith
        have h7 : s = 0 := by
          have h8 : ¬ (0 < s) := fun hc => h1 (by simpa [h6] using hc)
          linarith
        rw [h7, ht0] at hr0
        norm_num at hr0

/-- Helper (2026-09-28): `ups_x` in Gram form from `2p = a + b − f`. -/
private theorem p38_upsX_gram (a b f p : ℝ) (h : 2 * p = a + b - f) :
    upsX a b f = 4 * (a * b - p * p) := by
  simp only [upsX]
  linear_combination (2 * p + a + b - f) * h

/-- Helper (2026-09-28): `delta_x4` is `4·(a·r̃ − p̃·q̃)` in Gram form. -/
private theorem p38_deltaX4_gram (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    deltaX4 a b c d e f = 4 * (a * r - p * q) := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX4]
  ring

/-- Helper (2026-09-28): `4·x1·delta_x + delta_x4² =
ups_x(x1,x2,x6)·ups_x(x1,x3,x5)`. -/
private theorem p38_ups_delta (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    4 * a * deltaX a b c d e f + deltaX4 a b c d e f ^ 2 =
      upsX a b f * upsX a c e := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX, deltaX4, upsX]
  ring

/-- Helper (2026-09-28): `ups_x` is positive on the annulus box — the Heron
factorization `ups = ((‖x‖+‖y‖)² − d²)(d² − (‖x‖−‖y‖)²)` with both factors
forced by `2 ≤ ‖v‖`, `‖v‖ ≤ 2·h0`, `2 ≤ dist < 4`. -/
private theorem p38_upsX_pos_box {x y : V3} (x2 : 2 ≤ ‖x‖) (xu : ‖x‖ ≤ 2 * h0)
    (y2 : 2 ≤ ‖y‖) (yu : ‖y‖ ≤ 2 * h0) (hd : 2 ≤ dist x y) (h4 : dist x y < 4) :
    0 < upsX (‖x‖ * ‖x‖) (‖y‖ * ‖y‖) (dist x y * dist x y) := by
  have h0v : h0 = 1.26 := rfl
  have he : upsX (‖x‖ * ‖x‖) (‖y‖ * ‖y‖) (dist x y * dist x y)
      = ((‖x‖ + ‖y‖) ^ 2 - dist x y * dist x y)
        * (dist x y * dist x y - (‖x‖ - ‖y‖) ^ 2) := by
    simp only [upsX]
    ring
  rw [he, show dist x y * dist x y = dist x y ^ 2 from by ring]
  have hs4 : (4 : ℝ) ≤ ‖x‖ + ‖y‖ := by linarith
  have hsum : (4 : ℝ) ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := sq_le_sq' (by linarith) hs4
  have hdb : dist x y ^ 2 < (4 : ℝ) ^ 2 := sq_lt_sq' (by linarith) h4
  have hdd : (2 : ℝ) ^ 2 ≤ dist x y ^ 2 := sq_le_sq' (by linarith) hd
  have habs : |‖x‖ - ‖y‖| ≤ 2 * h0 - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsub : (‖x‖ - ‖y‖) ^ 2 ≤ (2 * h0 - 2) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hf1 : (0:ℝ) < (‖x‖ + ‖y‖) ^ 2 - dist x y ^ 2 := by linarith
  have hf2 : (0:ℝ) < dist x y ^ 2 - (‖x‖ - ‖y‖) ^ 2 := by
    have h52 : (2 * h0 - 2) ^ 2 < 4 := by norm_num [h0v]
    linarith
  exact mul_pos hf1 hf2

/-- Helper (proved here 2026-09-28): the Gram-form of `delta_x` with the
Gram entries given directly (`2p = a+b−f`, `2q = a+c−e`, `2r = b+c−d`). -/
private theorem p38_deltaX_gram_aux (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    deltaX a b c d e f =
      4 * (a * (b * c - r ^ 2) - p * (p * c - q * r) + q * (p * r - b * q)) := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX]
  ring

/-- Helper (proved here 2026-09-28): `delta_x` is 4× the Gram determinant
of three edge vectors — `det [[a,p,q],[p,b,r],[q,r,c]]` with
`p = (a+b−f)/2`, `q = (a+c−e)/2`, `r = (b+c−d)/2`. Pure algebra. -/
private theorem p38_deltaX_gram (a b c d e f : ℝ) :
    deltaX a b c d e f =
      4 * (a * (b * c - ((b + c - d) / 2) ^ 2)
        - ((a + b - f) / 2) * (((a + b - f) / 2) * c
          - ((a + c - e) / 2) * ((b + c - d) / 2))
        + ((a + c - e) / 2) * (((a + b - f) / 2) * ((b + c - d) / 2)
          - b * ((a + c - e) / 2))) := by
  have hp : 2 * ((a + b - f) / 2) = a + b - f := by ring
  have hq : 2 * ((a + c - e) / 2) = a + c - e := by ring
  have hr : 2 * ((b + c - d) / 2) = b + c - d := by ring
  rw [p38_deltaX_gram_aux a b c d e f ((a + b - f) / 2) ((a + c - e) / 2)
    ((b + c - d) / 2) hp hq hr]

/-- Helper (proved here 2026-09-28): the Gram determinant of three vectors
equals the determinant of the matrix with those rows, squared — hence
nonnegative. -/
private theorem p38_det_gram_eq (u v w : Fin 3 → ℝ) :
    u ⬝ᵥ u * (v ⬝ᵥ v * w ⬝ᵥ w - (v ⬝ᵥ w) ^ 2)
      - (u ⬝ᵥ v) * ((u ⬝ᵥ v) * w ⬝ᵥ w - (u ⬝ᵥ w) * (v ⬝ᵥ w))
      + (u ⬝ᵥ w) * ((u ⬝ᵥ v) * (v ⬝ᵥ w) - v ⬝ᵥ v * (u ⬝ᵥ w))
      = Matrix.det
          (Matrix.of fun i j =>
            (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i ⬝ᵥ
              (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j) := by
  rw [Matrix.det_fin_three]
  simp [dotProduct, Matrix.of_apply, mul_comm]
  ring

private theorem p38_det_gram_nn (u v w : Fin 3 → ℝ) :
    0 ≤ u ⬝ᵥ u * (v ⬝ᵥ v * w ⬝ᵥ w - (v ⬝ᵥ w) ^ 2)
      - (u ⬝ᵥ v) * ((u ⬝ᵥ v) * w ⬝ᵥ w - (u ⬝ᵥ w) * (v ⬝ᵥ w))
      + (u ⬝ᵥ w) * ((u ⬝ᵥ v) * (v ⬝ᵥ w) - v ⬝ᵥ v * (u ⬝ᵥ w)) := by
  have hdet := p38_det_gram_eq u v w
  have hGM : (Matrix.of fun i j =>
      (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i ⬝ᵥ
        (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j)
      = (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) *
        (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i) := by
    ext i j
    simp [Matrix.mul_apply, dotProduct, Matrix.of_apply]
  have hdMt : Matrix.det (Matrix.of fun i j =>
      (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i)
      = Matrix.det (Matrix.of fun i j =>
        (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) := by
    rw [← show Matrix.transpose (Matrix.of fun i j =>
          (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i)
        = (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) from rfl,
      Matrix.det_transpose]
  rw [hdet, hGM, Matrix.det_mul, hdMt]
  linarith [sq_nonneg (Matrix.det (Matrix.of fun i j =>
    (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j)), pow_two (Matrix.det (Matrix.of
    fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j))]

/-- Helper (2026-09-28): Cayley–Menger nonnegativity for a tetrahedron with
apex `0` — the `DELTA_Y_POS_4POINTS` content (that theorem now cites this
lemma; the copy here is needed because `tau3_taum` precedes it). -/

private theorem p38_deltaY_pos_4 (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) := by
  have hA : dist v0 v1 * dist v0 v1
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v1 - v0)
  have hB : dist v0 v2 * dist v0 v2
      = ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v2 - v0)
  have hC : dist v0 v3 * dist v0 v3
      = ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v3 - v0)
  have hP : 2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ)
        + ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ)
        - dist v1 v2 * dist v1 v2 := by
    have hc := p38_cos_law (v1 - v0) (v2 - v0)
    rw [show ‖(v1 - v0 : V3)‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v2 - v0 : V3)‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hA, hB] at hc
    rw [show dist v1 v2 = dist (v1 - v0) (v2 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  have hQ : 2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ)
        + ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
        - dist v1 v3 * dist v1 v3 := by
    have hc := p38_cos_law (v1 - v0) (v3 - v0)
    rw [show ‖(v1 - v0 : V3)‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v3 - v0 : V3)‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hA, hC] at hc
    rw [show dist v1 v3 = dist (v1 - v0) (v3 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  have hR : 2 * (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ)
        + ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
        - dist v2 v3 * dist v2 v3 := by
    have hc := p38_cos_law (v2 - v0) (v3 - v0)
    rw [show ‖(v2 - v0 : V3)‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v3 - v0 : V3)‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hB, hC] at hc
    rw [show dist v2 v3 = dist (v2 - v0) (v3 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  rw [deltaY, hA, hB, hC,
    p38_deltaX_gram_aux
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ))
      (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      (((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      (dist v2 v3 * dist v2 v3) (dist v1 v3 * dist v1 v3)
      (dist v1 v2 * dist v1 v2)
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      hP hQ hR]
  linarith [p38_det_gram_nn ((v1 - v0 : V3) : Fin 3 → ℝ)
    ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ)]

/-- The `DIHV_EQ_DIH_Y` bridge (2026-09-28): at a tetrahedron with apex `0`,
the geometric dihedral `dihV 0 w1 w2 w3` equals the analytic `dih_y` of the
squared-length box — both angles have cosine
`deltaX4 x / √(4·x1·deltaX x + deltaX4 x²)`.  `hΔy` is the Cayley–Menger
nonnegativity (`p38_deltaY_pos_4`). -/
private theorem p38_dihV_eq_dihY (w1 w2 w3 : V3)
    (hw1 : 0 < ‖w1‖)
    (hΔy : 0 ≤ deltaY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2))
    (hu2 : 0 < upsX (‖w1‖ * ‖w1‖) (‖w2‖ * ‖w2‖) (dist w1 w2 * dist w1 w2))
    (hu3 : 0 < upsX (‖w1‖ * ‖w1‖) (‖w3‖ * ‖w3‖) (dist w1 w3 * dist w1 w3)) :
    dihV 0 w1 w2 w3 =
      dihY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2) := by
  set a : ℝ := ‖w1‖ * ‖w1‖ with ha
  set b : ℝ := ‖w2‖ * ‖w2‖ with hb
  set c : ℝ := ‖w3‖ * ‖w3‖ with hc
  set d : ℝ := dist w2 w3 * dist w2 w3 with hd
  set e : ℝ := dist w1 w3 * dist w1 w3 with he
  set f : ℝ := dist w1 w2 * dist w1 w2 with hf
  set p : ℝ := w1 ⬝ᵥ w2 with hp
  set q : ℝ := w1 ⬝ᵥ w3 with hq
  set r : ℝ := w2 ⬝ᵥ w3 with hr
  have gA : a = w1 ⬝ᵥ w1 := by rw [ha, ← norm_sq_eq_dot, pow_two]
  have gB : b = w2 ⬝ᵥ w2 := by rw [hb, ← norm_sq_eq_dot, pow_two]
  have gC : c = w3 ⬝ᵥ w3 := by rw [hc, ← norm_sq_eq_dot, pow_two]
  have hP' : 2 * p = a + b - f := p38_cos_law w1 w2
  have hQ' : 2 * q = a + c - e := p38_cos_law w1 w3
  have hR' : 2 * r = b + c - d := p38_cos_law w2 w3
  have hU2 : upsX a b f = 4 * (a * b - p * p) := p38_upsX_gram a b f p hP'
  have hU3 : upsX a c e = 4 * (a * c - q * q) := p38_upsX_gram a c e q hQ'
  have hD4 : deltaX4 a b c d e f = 4 * (a * r - p * q) :=
    p38_deltaX4_gram a b c d e f p q r hP' hQ' hR'
  have hUD : 4 * a * deltaX a b c d e f + deltaX4 a b c d e f ^ 2
      = upsX a b f * upsX a c e := p38_ups_delta a b c d e f p q r hP' hQ' hR'
  have hap : (0:ℝ) < a := by positivity
  have hΔx : deltaX a b c d e f
      = deltaY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2) := by
    rw [deltaY, ← ha, ← hb, ← hc, ← hd, ← he, ← hf]
  have hΔ0 : 0 ≤ 4 * a * deltaX a b c d e f := by
    have h1x : 0 ≤ deltaX a b c d e f := by rw [hΔx]; exact hΔy
    exact mul_nonneg (by positivity) h1x
  have hden : 0 < 4 * a * deltaX a b c d e f + deltaX4 a b c d e f ^ 2 := by
    rw [hUD]; exact mul_pos hu2 hu3
  have hdihY : dihY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2)
      = Real.pi / 2 + atn2 (Real.sqrt (4 * a * deltaX a b c d e f))
          (-(deltaX4 a b c d e f)) := by
    rw [dihY, show ‖w1‖ * ‖w1‖ = a from ha.symm, show ‖w2‖ * ‖w2‖ = b from hb.symm,
      show ‖w3‖ * ‖w3‖ = c from hc.symm,
      show dist w2 w3 * dist w2 w3 = d from hd.symm,
      show dist w1 w3 * dist w1 w3 = e from he.symm,
      show dist w1 w2 * dist w1 w2 = f from hf.symm, dihXf]
  have hdihv0 : dihV 0 w1 w2 w3
      = arcV 0 (a • w2 - p • w1) (a • w3 - q • w1) := by
    unfold dihV
    dsimp only
    simp only [sub_zero]
    rw [dotProduct_comm w2 w1, dotProduct_comm w3 w1, ← gA, ← hp, ← hq]
  have harc : arcV 0 (a • w2 - p • w1) (a • w3 - q • w1)
      = Real.arccos (((a • w2 - p • w1 : V3) ⬝ᵥ (a • w3 - q • w1))
        / (dist (a • w2 - p • w1) (0:V3) * dist (a • w3 - q • w1) (0:V3))) := by
    rw [arcV]
    simp only [p38_coe_zero, p38_coe_sub, p38_coe_smul, sub_zero, dist_zero_right]
  have hnum : ((a • w2 - p • w1 : V3) ⬝ᵥ (a • w3 - q • w1)) = a * (a * r - p * q) := by
    simp only [p38_coe_sub, p38_coe_smul]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_comm w2 w1, ← gA, ← hp, ← hq, ← hr]
    ring
  have hab1 : 0 < a * b - p * p := by linarith
  have hab2 : 0 < a * c - q * q := by linarith
  have hnn2 : ((a • w2 - p • w1 : V3) ⬝ᵥ (a • w2 - p • w1)) = a * (a * b - p * p) := by
    simp only [p38_coe_sub, p38_coe_smul]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_comm w2 w1, ← gA, ← hp, ← gB]
    ring
  have hnn3 : ((a • w3 - q • w1 : V3) ⬝ᵥ (a • w3 - q • w1)) = a * (a * c - q * q) := by
    simp only [p38_coe_sub, p38_coe_smul]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_comm w3 w1, ← gA, ← hq, ← gC]
    ring
  have hdist2 : dist (a • w2 - p • w1) (0:V3) = Real.sqrt (a * (a * b - p * p)) := by
    rw [dist_zero_right, ← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_dot]
    exact congrArg Real.sqrt hnn2
  have hdist3 : dist (a • w3 - q • w1) (0:V3) = Real.sqrt (a * (a * c - q * q)) := by
    rw [dist_zero_right, ← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_dot]
    exact congrArg Real.sqrt hnn3
  have hden' : dist (a • w2 - p • w1) (0:V3) * dist (a • w3 - q • w1) (0:V3)
      = a * Real.sqrt ((a * b - p * p) * (a * c - q * q)) := by
    rw [hdist2, hdist3]
    calc Real.sqrt (a * (a * b - p * p)) * Real.sqrt (a * (a * c - q * q))
        = Real.sqrt ((a * (a * b - p * p)) * (a * (a * c - q * q))) :=
          (Real.sqrt_mul (by positivity : (0:ℝ) ≤ a * (a * b - p * p)) _).symm
      _ = Real.sqrt ((a * a) * ((a * b - p * p) * (a * c - q * q))) := by
          rw [show (a * (a * b - p * p)) * (a * (a * c - q * q))
            = (a * a) * ((a * b - p * p) * (a * c - q * q)) from by ring]
      _ = a * Real.sqrt ((a * b - p * p) * (a * c - q * q)) := by
          rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ a * a),
            Real.sqrt_mul_self (le_of_lt hap)]
  have harg : (a * (a * r - p * q)) / (a * Real.sqrt ((a * b - p * p) * (a * c - q * q)))
      = deltaX4 a b c d e f / Real.sqrt (4 * a * deltaX a b c d e f
        + deltaX4 a b c d e f ^ 2) := by
    rw [hUD, hD4, hU2, hU3]
    have hsq16 : Real.sqrt ((4:ℝ) * (a * b - p * p) * (4 * (a * c - q * q)))
        = 4 * Real.sqrt ((a * b - p * p) * (a * c - q * q)) := by
      rw [show (4:ℝ) * (a * b - p * p) * (4 * (a * c - q * q))
            = 16 * ((a * b - p * p) * (a * c - q * q)) from by ring,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ 16)]
      have h16 : Real.sqrt 16 = 4 := by norm_num
      rw [h16]
    rw [hsq16]
    have hane : a ≠ 0 := ne_of_gt hap
    have hzne : Real.sqrt ((a * b - p * p) * (a * c - q * q)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (mul_pos hab1 hab2))
    field_simp [hane, hzne]
  rw [hdihv0, harc, hnum, hden', harg, hdihY]
  have hdens : 0 < (Real.sqrt (4 * a * deltaX a b c d e f)) ^ 2
      + deltaX4 a b c d e f ^ 2 := by
    rw [Real.sq_sqrt hΔ0]
    exact hden
  have hz := p38_atn2_arccos (s := Real.sqrt (4 * a * deltaX a b c d e f))
    (t := deltaX4 a b c d e f) (Real.sqrt_nonneg _) hdens
  rw [show Real.sqrt (4 * a * deltaX a b c d e f)
        * Real.sqrt (4 * a * deltaX a b c d e f)
      = (Real.sqrt (4 * a * deltaX a b c d e f)) ^ 2 from by ring,
    show deltaX4 a b c d e f * deltaX4 a b c d e f
      = deltaX4 a b c d e f ^ 2 from by ring,
    Real.sq_sqrt hΔ0] at hz
  exact hz.symm

/-- The `tau3` = `taum` transfer on the annulus box (2026-09-28): the
composed `DIHV_EQ_DIH_Y` + `taum_dih_y` route.  `hΔ` is the Cayley–Menger
nonnegativity in norm form (`p38_deltaY_pos_4 0 v w u` + `dist_zero_left`). -/
private theorem p38_tau3_eq_taum {v0 v1 v2 : V3}
    (hΔ : ∀ v w u : V3, 0 ≤ deltaY ‖v‖ ‖w‖ ‖u‖ (dist w u) (dist v u) (dist v w))
    (m0 : 2 ≤ ‖v0‖) (m0u : ‖v0‖ ≤ 2 * h0) (m1 : 2 ≤ ‖v1‖) (m1u : ‖v1‖ ≤ 2 * h0)
    (m2 : 2 ≤ ‖v2‖) (m2u : ‖v2‖ ≤ 2 * h0)
    (d01 : 2 ≤ dist v0 v1) (d01u : dist v0 v1 < 4) (d02 : 2 ≤ dist v0 v2)
    (d02u : dist v0 v2 < 4) (d12 : 2 ≤ dist v1 v2) (d12u : dist v1 v2 < 4) :
    tau3 v0 v1 v2 =
      taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  have dc01 : 2 ≤ dist v1 v0 := by rw [dist_comm]; exact d01
  have dc02 : 2 ≤ dist v2 v0 := by rw [dist_comm]; exact d02
  have dc12 : 2 ≤ dist v2 v1 := by rw [dist_comm]; exact d12
  have dc01u : dist v1 v0 < 4 := by rw [dist_comm]; exact d01u
  have dc02u : dist v2 v0 < 4 := by rw [dist_comm]; exact d02u
  have dc12u : dist v2 v1 < 4 := by rw [dist_comm]; exact d12u
  have u01 := p38_upsX_pos_box m0 m0u m1 m1u d01 d01u
  have u02 := p38_upsX_pos_box m0 m0u m2 m2u d02 d02u
  have u12 := p38_upsX_pos_box m1 m1u m2 m2u d12 d12u
  have u10 := p38_upsX_pos_box m1 m1u m0 m0u dc01 dc01u
  have u20 := p38_upsX_pos_box m2 m2u m0 m0u dc02 dc02u
  have u21 := p38_upsX_pos_box m2 m2u m1 m1u dc12 dc12u
  have p0 : 0 < ‖v0‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) m0
  have p1 : 0 < ‖v1‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) m1
  have p2 : 0 < ‖v2‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) m2
  simp only [tau3]
  rw [p38_dihV_eq_dihY v0 v1 v2 p0 (hΔ v0 v1 v2) u01 u02,
      p38_dihV_eq_dihY v1 v2 v0 p1 (hΔ v1 v2 v0) u12 u10,
      p38_dihV_eq_dihY v2 v0 v1 p2 (hΔ v2 v0 v1) u20 u21]
  rw [dist_comm v2 v0, dist_comm v1 v0, dist_comm v2 v1]
  exact (p38_taum_dih_y ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1)).symm

/-- HOL `tau3_taum` (terminal.hl:489). -/
theorem tau3_taum (v0 v1 v2 : V3) :
    v0 ∈ ballAnnulus → v1 ∈ ballAnnulus → v2 ∈ ballAnnulus →
    2 ≤ dist v0 v1 → 2 ≤ dist v0 v2 → 2 ≤ dist v1 v2 →
    dist v0 v1 ≤ 3.62 → dist v0 v2 ≤ 3.62 → dist v1 v2 ≤ 3.62 →
    tau3 v0 v1 v2 =
      taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  intro _ _ _ _ _ _ _ _ _
  have hA : v0 ∈ ballAnnulus := by assumption
  have hB : v1 ∈ ballAnnulus := by assumption
  have hC : v2 ∈ ballAnnulus := by assumption
  have h01 : 2 ≤ dist v0 v1 := by assumption
  have h02 : 2 ≤ dist v0 v2 := by assumption
  have h12 : 2 ≤ dist v1 v2 := by assumption
  have h01u : dist v0 v1 ≤ 3.62 := by assumption
  have h02u : dist v0 v2 ≤ 3.62 := by assumption
  have h12u : dist v1 v2 ≤ 3.62 := by assumption
  obtain ⟨n0, n0u⟩ := ballAnnulus_norm_bounds hA
  obtain ⟨n1, n1u⟩ := ballAnnulus_norm_bounds hB
  obtain ⟨n2, n2u⟩ := ballAnnulus_norm_bounds hC
  exact p38_tau3_eq_taum (fun v w u => by
      have h := p38_deltaY_pos_4 0 v w u
      rwa [dist_zero_left, dist_zero_left, dist_zero_left] at h)
    n0 n0u n1 n1u n2 n2u
    h01 (lt_of_le_of_lt h01u (by norm_num : (3.62:ℝ) < 4))
    h02 (lt_of_le_of_lt h02u (by norm_num : (3.62:ℝ) < 4))
    h12 (lt_of_le_of_lt h12u (by norm_num : (3.62:ℝ) < 4))

/-- HOL `tau3_taum_40` (terminal.hl:513): the `< &4` variant. -/
theorem tau3_taum_40 (v0 v1 v2 : V3) :
    v0 ∈ ballAnnulus → v1 ∈ ballAnnulus → v2 ∈ ballAnnulus →
    2 ≤ dist v0 v1 → 2 ≤ dist v0 v2 → 2 ≤ dist v1 v2 →
    dist v0 v1 < 4 → dist v0 v2 < 4 → dist v1 v2 < 4 →
    tau3 v0 v1 v2 =
      taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  intro _ _ _ _ _ _ _ _ _
  have hA : v0 ∈ ballAnnulus := by assumption
  have hB : v1 ∈ ballAnnulus := by assumption
  have hC : v2 ∈ ballAnnulus := by assumption
  have h01 : 2 ≤ dist v0 v1 := by assumption
  have h02 : 2 ≤ dist v0 v2 := by assumption
  have h12 : 2 ≤ dist v1 v2 := by assumption
  have h01u : dist v0 v1 < 4 := by assumption
  have h02u : dist v0 v2 < 4 := by assumption
  have h12u : dist v1 v2 < 4 := by assumption
  obtain ⟨n0, n0u⟩ := ballAnnulus_norm_bounds hA
  obtain ⟨n1, n1u⟩ := ballAnnulus_norm_bounds hB
  obtain ⟨n2, n2u⟩ := ballAnnulus_norm_bounds hC
  exact p38_tau3_eq_taum (fun v w u => by
      have h := p38_deltaY_pos_4 0 v w u
      rwa [dist_zero_left, dist_zero_left, dist_zero_left] at h)
    n0 n0u n1 n1u n2 n2u h01 h01u h02 h02u h12 h12u

/-- HOL `DELTA_Y_POS_4POINTS` (terminal.hl:537). DISCHARGED 2026-09-28:
`delta_y` is 4× the Gram determinant of the three edge vectors `v1 − v0`,
`v2 − v0`, `v3 − v0` (via `p38_deltaX_gram`), the cross terms come from
`‖x − y‖²` dot expansions, and the Gram determinant equals
`det M · det Mᵀ = det M² ≥ 0` (`p38_det_gram_nn`). -/
theorem DELTA_Y_POS_4POINTS (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) :=
  p38_deltaY_pos_4 v0 v1 v2 v3

/-- HOL `tau3_taum_d` (terminal.hl:548). -/
theorem tau3_taum_d (d a01 a12 a02 b01 b12 b02 : ℝ)
    (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      a01 ≤ y6 → y6 ≤ b01 → a12 ≤ y4 → y4 ≤ b12 → a02 ≤ y5 → y5 ≤ b02 →
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      d ≤ taum y1 y2 y3 y4 y5 y6)
    (v0 v1 v2 : V3) :
    2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ → ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ →
    ‖v2‖ ≤ 2 * h0 → a01 ≤ dist v0 v1 → dist v0 v1 ≤ b01 →
    a12 ≤ dist v1 v2 → dist v1 v2 ≤ b12 → a02 ≤ dist v0 v2 →
    dist v0 v2 ≤ b02 → d ≤ tau3 v0 v1 v2 := by
  intro _ _ _ _ _ _ _ _ _ _ _ _
  sorry -- NEEDS: the DIHV_EQ_DIH_Y bridge is DONE (p38_dihV_eq_dihY above),
  -- but this statement's hypotheses do NOT force `2 ≤ dist v_i v_j`, so the
  -- ups_x-factors of the bridge can vanish on parallel wedges (where
  -- dihV = π/2-junk ≠ dihY ∈ {0,π,3π/2}).  Remaining work: a degenerate-case
  -- analysis showing d ≤ tau3 from h's box-bound (statement-level question).

/-- HOL `tau3_taum_dfun` (terminal.hl:583): tau3_taum_d with the
edge-correction functional `f`. -/
theorem tau3_taum_dfun (d : ℝ) (a01 a12 a02 b01 b12 b02 : ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      a01 ≤ y6 → y6 ≤ b01 → a12 ≤ y4 → y4 ≤ b12 → a02 ≤ y5 → y5 ≤ b02 →
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      d + f y4 y5 y6 ≤ taum y1 y2 y3 y4 y5 y6)
    (v0 v1 v2 : V3) :
    2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ → ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ →
    ‖v2‖ ≤ 2 * h0 → a01 ≤ dist v0 v1 → dist v0 v1 ≤ b01 →
    a12 ≤ dist v1 v2 → dist v1 v2 ≤ b12 → a02 ≤ dist v0 v2 →
    dist v0 v2 ≤ b02 → d + f (dist v1 v2) (dist v0 v2) (dist v0 v1) ≤ tau3 v0 v1 v2 := by
  intro _ _ _ _ _ _ _ _ _ _ _ _
  sorry -- NEEDS: as tau3_taum_d above (bridge done; degenerate parallel-wedge
  -- case blocks the ups_x-positivity — statement-level question).

/-- HOL `taustar_taum` (terminal.hl:618). -/
theorem taustar_taum (d : ℝ) (a b : ℕ → ℕ → ℝ) (h1 : 2 ≤ a 0 1) (h2 : 2 ≤ a 1 2)
    (h3 : 2 ≤ a 0 2) (h4 : b 0 1 ≤ 3.62) (h5 : b 1 2 ≤ 3.62) (h6 : b 0 2 ≤ 3.62)
    (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      a 0 1 ≤ y6 → y6 ≤ b 0 1 → a 1 2 ≤ y4 → y4 ≤ b 1 2 →
      a 0 2 ≤ y5 → y5 ≤ b 0 2 →
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      d ≤ taum y1 y2 y3 y4 y5 y6)
    (vv : ℕ → V3) (hbb : BBsV39 (mkUnadornedV39 3 d a b) vv) :
    0 ≤ taustarV39 (mkUnadornedV39 3 d a b) vv := by
  sorry -- DISCHARGES: tau3_taum (box-to-vector transfer)
  -- BLOCKED: as tau3_taum (DIHV_EQ_DIH_Y + taum_dih_y).

/-- Helper (2026-09-28): `setSum` over the `{i | i < 3 ∧ f i (i+1)}` index
set evaluates to the three-way `if`. -/
private theorem p38_setSum3 (f : ℕ → ℕ → Prop) (g : ℕ → ℝ) :
    setSum {i | i < 3 ∧ f i (i + 1)} g
      = (if f 0 1 then g 0 else 0) + (if f 1 2 then g 1 else 0)
        + (if f 2 3 then g 2 else 0) := by
  rw [setSum]
  have hfin : Set.Finite {i | i < 3 ∧ f i (i + 1)} :=
    Set.Finite.subset (Set.finite_Iio 3) (fun _ hx => hx.1)
  rw [dif_pos hfin]
  have hF : hfin.toFinset = Finset.filter (fun i => f i (i + 1)) (Finset.range 3) := by
    ext i
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_range]
  rw [hF, Finset.sum_filter,
    Finset.sum_range_succ (fun i => (if f i (i + 1) then g i else 0)) 2,
    Finset.sum_range_succ (fun i => (if f i (i + 1) then g i else 0)) 1,
    Finset.sum_range_succ (fun i => (if f i (i + 1) then g i else 0)) 0]
  simp only [Finset.sum_empty, Nat.reduceAdd, zero_add]
  ring

/-- HOL `taustar_taum_dfun` (terminal.hl:642). -/
theorem taustar_taum_dfun (d : ℝ) (a b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
    (h1 : 2 ≤ a 0 1) (h2 : 2 ≤ a 1 2) (h3 : 2 ≤ a 0 2) (h4 : b 0 1 ≤ 3.62)
    (h5 : b 1 2 ≤ 3.62) (h6 : b 0 2 ≤ 3.62)
    (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      a 0 1 ≤ y6 → y6 ≤ b 0 1 → a 1 2 ≤ y4 → y4 ≤ b 1 2 →
      a 0 2 ≤ y5 → y5 ≤ b 0 2 →
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      d + 0.1 * (if isEarV39 (ScsV39.mk 3 d a a b b f (fun _ => False)
          (fun _ => False) (fun _ => False)) then 1 else -1) *
        ((if f 0 1 then cstab - y6 else 0) + (if f 1 2 then cstab - y4 else 0) +
        (if f 2 3 then cstab - y5 else 0) + 0) ≤ taum y1 y2 y3 y4 y5 y6)
    (vv : ℕ → V3) (hbb : BBsV39 (ScsV39.mk 3 d a a b b f (fun _ => False)
      (fun _ => False) (fun _ => False)) vv) :
    0 ≤ taustarV39 (ScsV39.mk 3 d a a b b f (fun _ => False) (fun _ => False)
      (fun _ => False)) vv := by
  sorry -- DISCHARGES: tau3_taum (box-to-vector transfer)
  -- BLOCKED: as tau3_taum (DIHV_EQ_DIH_Y + taum_dih_y).

/-! ## Section D: taum symmetry and the funlist/periodicity kit
(terminal.hl:684-1211) -/

/-- HOL `taum_sym2` (terminal.hl:684). DISCHARGED 2026-09-20: `taum` sums
`ly`-weighted `dihY` terms over the three edges from the origin; the vertex
transpositions permute those three terms, and each permuted `dihY` is related
to the original by `dihY_swap23_p38`. -/
theorem taum_sym2 (y1 y2 y3 y4 y5 y6 : ℝ) :
    taum y1 y2 y3 y4 y5 y6 = taum y2 y1 y3 y5 y4 y6 ∧
    taum y1 y2 y3 y4 y5 y6 = taum y1 y3 y2 y4 y6 y5 := by
  have e1 : dihY y2 y1 y3 y5 y4 y6 = dihY y2 y3 y1 y5 y6 y4 :=
    dihY_swap23_p38 _ _ _ _ _ _
  have e2 : dihY y1 y3 y2 y4 y6 y5 = dihY y1 y2 y3 y4 y5 y6 :=
    dihY_swap23_p38 _ _ _ _ _ _
  have e3 : dihY y3 y2 y1 y6 y5 y4 = dihY y3 y1 y2 y6 y4 y5 :=
    dihY_swap23_p38 _ _ _ _ _ _
  constructor
  · simp only [taum, solY, lnazim, e1, e2, e3]
    ring
  · simp only [taum, solY, lnazim, e1, e2, e3]
    ring

/-- HOL `MOD_4_EXPLICIT` (terminal.hl:697). -/
theorem MOD_4_EXPLICIT :
    0 % 4 = 0 ∧ 1 % 4 = 1 ∧ 2 % 4 = 2 ∧ 3 % 4 = 3 ∧ 4 % 4 = 0 ∧ 5 % 4 = 1 ∧
    6 % 4 = 2 := by
  norm_num

/-- HOL `FUNLIST_EXPLICIT` (terminal.hl:707). -/
theorem FUNLIST_EXPLICIT :
    (∀ data d k i j, funlistV39 data d k i j =
      if i % k = j % k then 0
      else assocdV39 (psort k (i, j)) (data.map fun p => (psort k p.1, p.2)) d) ∧
    (∀ (A : Type u) (data : List ((ℕ × ℕ) × A)) (u u' : A) (k i j : ℕ),
      funlistAV39 data u u' k i j =
      if i % k = j % k then u
      else assocdV39 (psort k (i, j)) (data.map fun p => (psort k p.1, p.2)) u') ∧
    0 % 3 = 0 ∧ 1 % 3 = 1 ∧ 2 % 3 = 2 ∧ 3 % 3 = 0 ∧
    (∀ x : ℝ, x = x) ∧ (0 : ℕ) ≠ 1 ∧ (0 : ℕ) ≠ 2 ∧ (1 : ℕ) ≠ 2 ∧
    (0 : ℕ) ≠ 3 ∧ (1 : ℕ) ≠ 3 ∧ (2 : ℕ) ≠ 3 ∧
    psort 3 (0, 1) = (0, 1) ∧ psort 3 (0, 2) = (0, 2) ∧ psort 3 (1, 2) = (1, 2) ∧
    psort 3 (2, 3) = (0, 2) ∧ psort 4 (0, 1) = (0, 1) ∧ psort 4 (0, 2) = (0, 2) ∧
    psort 4 (0, 3) = (0, 3) ∧ psort 4 (1, 2) = (1, 2) ∧ psort 4 (1, 3) = (1, 3) ∧
    psort 4 (2, 3) = (2, 3) ∧ psort 4 (1, 0) = (0, 1) ∧ psort 4 (2, 0) = (0, 2) ∧
    psort 4 (3, 0) = (0, 3) ∧ psort 4 (2, 1) = (1, 2) ∧ psort 4 (3, 1) = (1, 3) ∧
    psort 4 (3, 2) = (2, 3) := by
  repeat' first
    | constructor
    | (intros; rfl)
    | norm_num
    | exact fun _ => rfl
    | simp [psort]

/-- HOL `periodic2_funlist` (terminal.hl:772). -/
theorem periodic2_funlist (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ) (k : ℕ) :
    Periodic2 (funlistV39 a a0 k) k := by
  intro i j
  constructor <;> simp [funlistV39, psort, Nat.add_mod_left]

/-- HOL `periodic2_funlistA` (terminal.hl:789). -/
theorem periodic2_funlistA {A : Type u} (j1 : List ((ℕ × ℕ) × A)) (j' j'' : A)
    (k : ℕ) : Periodic2 (funlistAV39 j1 j' j'' k) k := by
  intro i j
  constructor <;> simp [funlistAV39, psort, Nat.add_mod_left]

/-- HOL `psort_sym` (terminal.hl:806). -/
theorem psort_sym (k i j : ℕ) : psort k (i, j) = psort k (j, i) := by
  simp only [psort]
  split <;> rename_i h1 <;> split <;> rename_i h2 <;>
    first | rfl | (simp at h1 h2; omega) |
      (have := Nat.le_antisymm h1 h2; simp [this])

/-- HOL `funlist_sym` (terminal.hl:817). -/
theorem funlist_sym (k : ℕ) (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ) (i j : ℕ) :
    funlistV39 a a0 k i j = funlistV39 a a0 k j i := by
  simp only [funlistV39, psort_sym, eq_comm (a := i % k) (b := j % k)]

/-- HOL `funlistA_sym` (terminal.hl:830). -/
theorem funlistA_sym {A : Type u} (k : ℕ) (a : List ((ℕ × ℕ) × A)) (a0 a1 : A)
    (i j : ℕ) : funlistAV39 a a0 a1 k i j = funlistAV39 a a0 a1 k j i := by
  simp only [funlistAV39, psort_sym, eq_comm (a := i % k) (b := j % k)]

/-- HOL `funlist_diag` (terminal.hl:843). -/
theorem funlist_diag (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ) (k i : ℕ) :
    funlistV39 a a0 k i i = 0 := by
  simp [funlistV39]

/-- HOL `funlistA_diag` (terminal.hl:851). -/
theorem funlistA_diag {A : Type u} (j1 : List ((ℕ × ℕ) × A)) (j2 j3 : A) (k i : ℕ) :
    funlistAV39 j1 j2 j3 k i i = j2 := by
  simp [funlistAV39]

/-- HOL `funlistA_empty` (terminal.hl:859; the HOL `F` diagonal at the
`Prop` instance). -/
theorem funlistA_empty (k : ℕ) :
    funlistAV39 [] False False (A := Prop) k = fun _ _ => False := by
  funext i j
  simp [funlistAV39, assocdV39]

/-- HOL `is_scs_funlist` (terminal.hl:1002). -/
theorem is_scs_funlist (k : ℕ) (d a0 b0 : ℝ) (j0 : Prop)
    (a : List ((ℕ × ℕ) × ℝ)) (b : List ((ℕ × ℕ) × ℝ))
    (j1 : List ((ℕ × ℕ) × Prop)) (u u' u'' : ℕ → Prop)
    (h1 : d < 0.9) (h2 : 3 ≤ k) (h3 : k ≤ 6)
    (h4 : Periodic u k) (h5 : Periodic u' k) (h6 : Periodic u'' k)
    (h7 : ∀ i j : ℕ, i < j ∧ j < k →
      funlistV39 a a0 k i j ≤ funlistV39 b b0 k i j)
    (h8 : ∀ i j : ℕ, i < j ∧ j < k → 2 ≤ funlistV39 a a0 k i j)
    (h9 : ∀ i : ℕ, i < 3 ∧ k = 3 → funlistV39 b b0 k i (i + 1) < 4)
    (h10 : ∀ i : ℕ, i < k ∧ 3 < k → funlistV39 b b0 k i (i + 1) ≤ cstab)
    (h11 : ∀ i j : ℕ, i < j ∧ j < k ∧ funlistAV39 j1 False j0 k i j →
      funlistV39 a a0 k i j = Real.sqrt 8 ∧ funlistV39 b b0 k i j = cstab)
    (h12 : ∀ i j : ℕ, i < j ∧ j < k ∧ funlistAV39 j1 False j0 k i j →
      j = i + 1 ∨ (i = 0 ∧ j + 1 = k))
    (h13 : {i : ℕ | i < k ∧ (2 * h0 < funlistV39 b b0 k i (i + 1) ∨
        2 < funlistV39 a a0 k i (i + 1))}.ncard + k ≤ 6) :
    isScsV39 (ScsV39.mk k d (funlistV39 a a0 k) (funlistV39 a a0 k)
      (funlistV39 b b0 k) (funlistV39 b b0 k) (funlistAV39 j1 False j0 k)
      u u' u'') := by
  have hk0 : k ≠ 0 := fun hc => by rw [hc] at h2; norm_num at h2
  have hFred : ∀ i j : ℕ, funlistV39 a a0 k i j =
      funlistV39 a a0 k (i % k) (j % k) :=
    fun i j => by simp only [funlistV39, psort, Nat.mod_mod]
  have hGred : ∀ i j : ℕ, funlistV39 b b0 k i j =
      funlistV39 b b0 k (i % k) (j % k) :=
    fun i j => by simp only [funlistV39, psort, Nat.mod_mod]
  have hJred : ∀ i j : ℕ, funlistAV39 j1 False j0 k i j ↔
      funlistAV39 j1 False j0 k (i % k) (j % k) :=
    fun i j => by simp only [funlistAV39, psort, Nat.mod_mod]
  refine ⟨h1, h2, h3, h4, h5, h6, h6, periodic2_funlist a a0 k,
    periodic2_funlist a a0 k, periodic2_funlist b b0 k,
    periodic2_funlist b b0 k, periodic2_funlistA j1 False j0 k,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [ScsV39.mk]
  · intro i j
    exact ⟨funlist_sym k a a0 i j, funlist_sym k a a0 i j,
      funlist_sym k b b0 i j, funlist_sym k b b0 i j,
      funlistA_sym k j1 False j0 i j⟩
  · intro i j
    rw [hFred i j, hGred i j]
    rcases Nat.lt_trichotomy (i % k) (j % k) with hlt | heq | hgt
    · exact ⟨le_refl _, h7 _ _ ⟨hlt, Nat.mod_lt _ (Nat.pos_of_ne_zero hk0)⟩,
        le_refl _⟩
    · rw [heq, funlist_diag, funlist_diag]
      exact ⟨le_refl _, le_refl _, le_refl _⟩
    · rw [funlist_sym k a a0, funlist_sym k b b0]
      exact ⟨le_refl _, h7 _ _ ⟨hgt, Nat.mod_lt _ (Nat.pos_of_ne_zero hk0)⟩,
        le_refl _⟩
  · intro i
    exact funlist_diag a a0 k i
  · intro i j hijk
    obtain ⟨hik, hjk, hne⟩ := hijk
    rw [hFred i j, Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk]
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact h8 i j ⟨hlt, hjk⟩
    · exact absurd heq hne
    · rw [funlist_sym k a a0]
      exact h8 j i ⟨hgt, hik⟩
  · intro i hk3
    subst hk3
    have hb : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rw [hGred i (i + 1)]
    rcases hb with h0 | h1 | h2'
    · rw [h0, show (i + 1) % 3 = 1 by omega]
      exact h9 0 ⟨by norm_num, rfl⟩
    · rw [h1, show (i + 1) % 3 = 2 by omega]
      exact h9 1 ⟨by norm_num, rfl⟩
    · rw [h2', show (i + 1) % 3 = 0 by omega]
      have hx : funlistV39 b b0 3 2 0 = funlistV39 b b0 3 2 (2 + 1) := by
        simp [funlistV39, psort]
      rw [hx]
      exact h9 2 ⟨by norm_num, rfl⟩
  · intro i hik
    have hred : funlistV39 b b0 k i (i + 1) =
        funlistV39 b b0 k (i % k) (i % k + 1) := by
      simp only [funlistV39, psort, Nat.add_mod, Nat.mod_mod]
    rw [hred]
    exact h10 _ ⟨Nat.mod_lt i (Nat.pos_of_ne_zero hk0), hik⟩
  · intro i j hjJ
    rw [hJred i j] at hjJ
    have key : ∀ p q : ℕ, p < k → q < k →
        funlistAV39 j1 False j0 k p q →
        q % k = (p + 1) % k ∨ p % k = (q + 1) % k := by
      intro p q hpk hqk hJ
      rw [Nat.mod_eq_of_lt hpk, Nat.mod_eq_of_lt hqk]
      simp only [funlistAV39, Nat.mod_mod] at hJ
      by_cases he : p = q
      · subst he
        simp at hJ
      · rcases Nat.lt_trichotomy p q with hlt | heq | hgt
        · rcases h12 p q ⟨hlt, hqk, hJ⟩ with heq' | hwrap
          · left
            rw [heq', Nat.mod_eq_of_lt (by omega : p + 1 < k)]
          · obtain ⟨hp0, hq1⟩ := hwrap
            subst hp0
            subst hq1
            right
            simp
        · exact absurd heq he
        · have hJqp : funlistAV39 j1 False j0 k q p := by
            rw [funlistA_sym k j1 False j0]
            exact hJ
          rcases h12 q p ⟨hgt, hpk, hJqp⟩ with heq'' | hwrap
          · right
            rw [heq'', Nat.mod_eq_of_lt (by omega : q + 1 < k)]
          · obtain ⟨hq0, hp1⟩ := hwrap
            subst hq0
            subst hp1
            left
            simp
    have hred := key (i % k) (j % k) (Nat.mod_lt i (Nat.pos_of_ne_zero hk0))
      (Nat.mod_lt j (Nat.pos_of_ne_zero hk0)) hjJ
    rwa [Nat.mod_mod, Nat.mod_mod, Nat.mod_add_mod, Nat.mod_add_mod] at hred
  · intro i j hjJ
    rw [hJred i j] at hjJ
    rw [hFred i j, hGred i j]
    have hik := Nat.mod_lt i (Nat.pos_of_ne_zero hk0)
    have hjk := Nat.mod_lt j (Nat.pos_of_ne_zero hk0)
    rcases Nat.lt_trichotomy (i % k) (j % k) with hlt | heq | hgt
    · exact h11 _ _ ⟨hlt, hjk, hjJ⟩
    · rw [heq] at hjJ
      simp only [funlistAV39, Nat.mod_mod, reduceIte] at hjJ
    · have hJqp : funlistAV39 j1 False j0 k (j % k) (i % k) := by
        rw [funlistA_sym k j1 False j0]
        exact hjJ
      obtain ⟨e1, e2⟩ := h11 (j % k) (i % k) ⟨hgt, hik, hJqp⟩
      rw [funlist_sym k a a0, funlist_sym k b b0]
      exact ⟨e1, e2⟩
  · exact h13

/-- HOL `is_ear_scs3` (terminal.hl:1103). DISCHARGED 2026-09-20: the
`is_ear_v39` unfolding — `unadorned_v39`/`k = 3`/`d = 0.11` are `rfl` for the
`scs_v39 (3, #0.11, a, a, b, b, jf, {}, {}, {})` record. -/
theorem is_ear_scs3 (a b : ℕ → ℕ → ℝ) (jf : ℕ → ℕ → Prop) :
    isEarV39 (ScsV39.mk 3 0.11 a a b b jf (fun _ => False) (fun _ => False)
      (fun _ => False)) ↔
    isScsV39 (ScsV39.mk 3 0.11 a a b b jf (fun _ => False) (fun _ => False)
      (fun _ => False)) ∧ (∀ i, b i i = 0) ∧
    (∃ i, {j | j < 3 ∧ jf j (j + 1)} = {i} ∧ a i (i + 1) = Real.sqrt 8 ∧
      b i (i + 1) = cstab ∧
      (∀ j, j < 3 ∧ j ≠ i → a j (j + 1) = 2 ∧ b j (j + 1) = 2 * h0)) := by
  constructor
  · intro h
    unfold isEarV39 at h
    obtain ⟨hscs, -, -, -, hdiag, hex⟩ := h
    exact ⟨hscs, hdiag, hex⟩
  · rintro ⟨hscs, hdiag, hex⟩
    refine ⟨hscs, ?_, rfl, rfl, hdiag, hex⟩
    unfold unadornedV39
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `is_scs_scs3` (terminal.hl:1126). -/
theorem is_scs_scs3 (d : ℝ) (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ)
    (b : List ((ℕ × ℕ) × ℝ)) (b0 : ℝ) (jf : List ((ℕ × ℕ) × Prop)) (j0 : Prop)
    (h1 : d < 0.9)
    (h2 : funlistV39 a a0 3 0 1 ≤ funlistV39 b b0 3 0 1)
    (h3 : funlistV39 a a0 3 0 2 ≤ funlistV39 b b0 3 0 2)
    (h4 : funlistV39 a a0 3 1 2 ≤ funlistV39 b b0 3 1 2)
    (h5 : 2 ≤ funlistV39 a a0 3 0 1)
    (h6 : 2 ≤ funlistV39 a a0 3 1 2)
    (h7 : 2 ≤ funlistV39 a a0 3 0 2)
    (h8 : funlistV39 b b0 3 0 1 < 4)
    (h9 : funlistV39 b b0 3 0 2 < 4)
    (h10 : funlistV39 b b0 3 1 2 < 4)
    (h11 : ∀ i j : ℕ, i < j ∧ j < 3 ∧ funlistAV39 jf False j0 3 i j →
      funlistV39 a a0 3 i j = Real.sqrt 8 ∧ funlistV39 b b0 3 i j = cstab) :
    isScsV39 (ScsV39.mk 3 d (funlistV39 a a0 3) (funlistV39 a a0 3)
      (funlistV39 b b0 3) (funlistV39 b b0 3)       (funlistAV39 jf False j0 3)
      (fun _ => False) (fun _ => False) (fun _ => False)) := by
  refine is_scs_funlist 3 d a0 b0 j0 a b jf (fun _ => False) (fun _ => False)
    (fun _ => False) h1 (by norm_num) (by norm_num)
    (periodic_empty _) (periodic_empty _) (periodic_empty _) ?_ ?_ ?_ ?_ h11 ?_ ?_
  · rintro i j ⟨hij, hj3⟩
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      h01 | h02 | h12'
    · obtain ⟨rfl, rfl⟩ := h01
      exact h2
    · obtain ⟨rfl, rfl⟩ := h02
      exact h3
    · obtain ⟨rfl, rfl⟩ := h12'
      exact h4
  · rintro i j ⟨hij, hj3⟩
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      h01 | h02 | h12'
    · obtain ⟨rfl, rfl⟩ := h01
      exact h5
    · obtain ⟨rfl, rfl⟩ := h02
      exact h7
    · obtain ⟨rfl, rfl⟩ := h12'
      exact h6
  · rintro i ⟨hi, -⟩
    have hb : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hb with h0 | h1' | h2'
    · subst h0; exact h8
    · subst h1'; exact h10
    · subst h2'
      have hx : funlistV39 b b0 3 2 (2 + 1) = funlistV39 b b0 3 0 2 := by
        simp [funlistV39, psort]
      rw [hx]
      exact h9
  · rintro i ⟨-, h3lt⟩
    exact absurd h3lt (by norm_num)
  · rintro i j ⟨hij, hj3⟩
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      h01 | h02 | h12'
    · obtain ⟨rfl, rfl⟩ := h01
      exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := h02
      exact Or.inr ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := h12'
      exact Or.inl rfl
  · have hnc : {i | i < 3 ∧ (2 * h0 < funlistV39 b b0 3 i (i + 1) ∨
        2 < funlistV39 a a0 3 i (i + 1))}.ncard ≤ ({0, 1, 2} : Set ℕ).ncard := by
      refine Set.ncard_le_ncard ?_ ?_
      · intro x hx
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        obtain ⟨hx1, -⟩ := hx
        omega
      · exact Set.toFinite _
    have h3 : ({0, 1, 2} : Set ℕ).ncard = 3 := by simp
    omega

/-- HOL `is_scs_ear_3603097872` (terminal.hl:1186). -/
theorem is_scs_ear_3603097872 :
    isScsV39 (ScsV39.mk 3 0.11
      (funlistV39 [((0, 1), Real.sqrt 8)] 2 3) (funlistV39 [((0, 1), Real.sqrt 8)] 2 3)
      (funlistV39 [((0, 1), cstab)] (2 * h0) 3) (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
      (funlistAV39 [((0, 1), True)] False False 3)
      (fun _ => False) (fun _ => False) (fun _ => False)) := by
  have hF01 : funlistV39 [((0, 1), Real.sqrt 8)] 2 3 0 1 = Real.sqrt 8 := by
    simp [funlistV39, psort, assocdV39]
  have hG01 : funlistV39 [((0, 1), cstab)] (2 * h0) 3 0 1 = cstab := by
    simp [funlistV39, psort, assocdV39]
  have hF12 : funlistV39 [((0, 1), Real.sqrt 8)] 2 3 1 2 = 2 := by
    simp [funlistV39, psort, assocdV39]
  have hG12 : funlistV39 [((0, 1), cstab)] (2 * h0) 3 1 2 = 2 * h0 := by
    simp [funlistV39, psort, assocdV39]
  refine is_scs_scs3 0.11 [((0, 1), Real.sqrt 8)] 2 [((0, 1), cstab)] (2 * h0)
    [((0, 1), True)] False (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hF01, hG01]
    exact (Real.sqrt_le_left (by norm_num [cstab])).mpr
      (by norm_num : (8:ℝ) ≤ (3.01:ℝ) ^ 2)
  · show (2:ℝ) ≤ 2 * h0
    norm_num [h0]
  · show (2:ℝ) ≤ 2 * h0
    norm_num [h0]
  · rw [hF01]
    have h8sq : (2.828427:ℝ) ^ 2 < 8 := by norm_num
    exact le_trans (by norm_num : (2:ℝ) ≤ 2.828427)
      (le_of_lt ((Real.lt_sqrt (by norm_num)).mpr h8sq))
  · show (2:ℝ) ≤ 2
    norm_num
  · show (2:ℝ) ≤ 2
    norm_num
  · show (cstab:ℝ) < 4
    norm_num [cstab]
  · show (2 * h0:ℝ) < 4
    norm_num [h0]
  · show (2 * h0:ℝ) < 4
    norm_num [h0]
  · rintro i j ⟨hij, hJ⟩
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      h01 | h02 | h12'
    · obtain ⟨rfl, rfl⟩ := h01
      exact ⟨hF01, hG01⟩
    · obtain ⟨rfl, rfl⟩ := h02
      simp [funlistAV39, psort, assocdV39] at hJ
    · obtain ⟨rfl, rfl⟩ := h12'
      simp [funlistAV39, psort, assocdV39] at hJ

/-- HOL `REAL_FINITE_MIN_EXISTS` (terminal.hl:1213); the name is taken by an
imported twin, so the `_p38` suffix is used. -/
theorem REAL_FINITE_MIN_EXISTS_p38 (S : Set ℝ) (hfin : S.Finite)
    (hne : S.Nonempty) :
    ∃ m, m ∈ S ∧ ∀ x ∈ S, m ≤ x := by
  exact ⟨sInf S, hne.csInf_mem hfin, fun x hx => csInf_le hfin.bddBelow hx⟩

/-- HOL `REAL_WLOG_SQUARE_LEMMA` (terminal.hl:1217). -/
theorem REAL_WLOG_SQUARE_LEMMA (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hrot : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5)
    (hmax : ∀ y1 y2 y3 y4 y5 y6 : ℝ, y2 ≤ y1 → y3 ≤ y1 → y4 ≤ y1 →
      P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6
  have r1 : P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5 := hrot _ _ _ _ _ _
  have r2 : P y2 y3 y4 y1 y6 y5 = P y3 y4 y1 y2 y5 y6 := hrot _ _ _ _ _ _
  have r3 : P y3 y4 y1 y2 y5 y6 = P y4 y1 y2 y3 y6 y5 := hrot _ _ _ _ _ _
  rcases le_total y2 y1 with h21 | h12
  · rcases le_total y3 y1 with h31 | h13
    · rcases le_total y4 y1 with h41 | h14
      · exact hmax _ _ _ _ _ _ h21 h31 h41
      · rw [r1, r2, r3]
        exact hmax _ _ _ _ _ _ h14 (le_trans h21 h14)
          (le_trans h31 h14)
    · rcases le_total y4 y3 with h43 | h34
      · rw [r1, r2]
        exact hmax _ _ _ _ _ _ h43 h13 (le_trans h21 h13)
      · rw [r1, r2, r3]
        exact hmax _ _ _ _ _ _ (h13.trans h34)
          (h21.trans (h13.trans h34)) h34
  · rcases le_total y3 y2 with h32 | h23
    · rcases le_total y4 y2 with h42 | h24
      · rw [r1]
        exact hmax _ _ _ _ _ _ h32 h42 h12
      · rw [r1, r2, r3]
        exact hmax _ _ _ _ _ _ (h12.trans h24) h24 (h32.trans h24)
    · rcases le_total y4 y3 with h43 | h34
      · rw [r1, r2]
        exact hmax _ _ _ _ _ _ h43 (h12.trans h23) h23
      · rw [r1, r2, r3]
        exact hmax _ _ _ _ _ _ (h12.trans (h23.trans h34))
          (h23.trans h34) h34

/-- HOL `REAL_WLOG_SQUARE2_LEMMA` (terminal.hl:1237). -/
theorem REAL_WLOG_SQUARE2_LEMMA (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hrot : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5 ∧
      P y1 y2 y3 y4 y5 y6 = P y1 y4 y3 y2 y6 y5)
    (hmax : ∀ y1 y2 y3 y4 y5 y6 : ℝ, y2 ≤ y1 → y3 ≤ y1 → y4 ≤ y1 → y4 ≤ y2 →
      P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6
  have rot1 : P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5 := hrot _ _ _ _ _ _ |>.1
  have rot2 : P y2 y3 y4 y1 y6 y5 = P y3 y4 y1 y2 y5 y6 := hrot _ _ _ _ _ _ |>.1
  have rot3 : P y3 y4 y1 y2 y5 y6 = P y4 y1 y2 y3 y6 y5 := hrot _ _ _ _ _ _ |>.1
  have ref1 : P y1 y2 y3 y4 y5 y6 = P y1 y4 y3 y2 y6 y5 := hrot _ _ _ _ _ _ |>.2
  have ref2 : P y2 y3 y4 y1 y6 y5 = P y2 y1 y4 y3 y5 y6 := hrot _ _ _ _ _ _ |>.2
  have ref3 : P y3 y4 y1 y2 y5 y6 = P y3 y2 y1 y4 y6 y5 := hrot _ _ _ _ _ _ |>.2
  have ref4 : P y4 y1 y2 y3 y6 y5 = P y4 y3 y2 y1 y5 y6 := hrot _ _ _ _ _ _ |>.2
  rcases le_total y2 y1 with h21 | h12
  · rcases le_total y3 y1 with h31 | h13
    · rcases le_total y4 y1 with h41 | h14
      · rcases le_total y4 y2 with h42 | h24
        · -- head y1, direct
          exact hmax _ _ _ _ _ _ h21 h31 h41 h42
        · -- head y1, reflected (2nd = y4, 4th = y2)
          rw [ref1]
          exact hmax _ _ _ _ _ _ h41 h31 h21 h24
      · -- y1 ≤ y4: head y4 (three rotations); middle pair (y1, y3)
        rcases le_total y3 y1 with h31' | h13'
        · rw [rot1, rot2, rot3]
          exact hmax _ _ _ _ _ _ h14 (h21.trans h14) (h31.trans h14) h31'
        · rw [rot1, rot2, rot3, ref4]
          exact hmax _ _ _ _ _ _ (h31.trans h14) (h21.trans h14) h14 h13'
    · -- y1 ≤ y3
      rcases le_total y4 y1 with h41 | h14
      · -- head y3 (two rotations); middle pair (y4, y2)
        rcases le_total y2 y4 with h42' | h24'
        · rw [rot1, rot2]
          exact hmax _ _ _ _ _ _ (h41.trans h13) h13 (h21.trans h13) h42'
        · rw [rot1, rot2, ref3]
          exact hmax _ _ _ _ _ _ (h21.trans h13) h13 (h41.trans h13) h24'
      · -- y1 ≤ y4: compare y3, y4
        rcases le_total y4 y3 with h43 | h34
        · -- head y3; middle pair (y4, y2)
          rcases le_total y2 y4 with h42' | h24'
          · rw [rot1, rot2]
            exact hmax _ _ _ _ _ _ h43 h13 (h21.trans h13) h42'
          · rw [rot1, rot2, ref3]
            exact hmax _ _ _ _ _ _ (h21.trans h13) h13 h43 h24'
        · -- head y4; middle pair (y1, y3)
          rcases le_total y3 y1 with h31' | h13'
          · rw [rot1, rot2, rot3]
            exact hmax _ _ _ _ _ _ h14 (h21.trans h14) h34 h31'
          · rw [rot1, rot2, rot3, ref4]
            exact hmax _ _ _ _ _ _ h34 (h21.trans h14) h14 h13'
  · -- y2 ≤ y1
    rcases le_total y3 y2 with h32 | h23
    · rcases le_total y4 y2 with h42 | h24
      · -- head y2 (one rotation); middle pair (y3, y1)
        rcases le_total y1 y3 with h13' | h31'
        · rw [rot1]
          exact hmax _ _ _ _ _ _ h32 h42 h12 h13'
        · rw [rot1, ref2]
          exact hmax _ _ _ _ _ _ h12 h42 h32 h31'
      · -- y2 ≤ y4: head y4; middle pair (y1, y3)
        rcases le_total y3 y1 with h31' | h13'
        · rw [rot1, rot2, rot3]
          exact hmax _ _ _ _ _ _ (h12.trans h24) h24 (h32.trans h24) h31'
        · rw [rot1, rot2, rot3, ref4]
          exact hmax _ _ _ _ _ _ (h32.trans h24) h24 (h12.trans h24) h13'
    · -- y2 ≤ y3
      rcases le_total y4 y3 with h43 | h34
      · -- head y3 (two rotations); middle pair (y4, y2)
        rcases le_total y2 y4 with h42' | h24'
        · rw [rot1, rot2]
          exact hmax _ _ _ _ _ _ h43 (h12.trans h23) h23 h42'
        · rw [rot1, rot2, ref3]
          exact hmax _ _ _ _ _ _ h23 (h12.trans h23) h43 h24'
      · -- y3 ≤ y4: head y4; middle pair (y1, y3)
        rcases le_total y3 y1 with h31' | h13'
        · rw [rot1, rot2, rot3]
          exact hmax _ _ _ _ _ _ (h12.trans (h23.trans h34))
            (h23.trans h34) h34 h31'
        · rw [rot1, rot2, rot3, ref4]
          exact hmax _ _ _ _ _ _ h34 (h23.trans h34)
            (h12.trans (h23.trans h34)) h13'

/-! ## Section E: the fan / azim bank (terminal.hl:1254-2230) -/

/-! ### Proof-fill kit (2026-09-28): periodic-cycle helpers shared by the
`EE_vv`/`tau_fun_azim`/`vv_rho_node1`/`ITER_vv_rho_node1`/`vv_azim_le`/
`convex_local_fan_azim_le_pi` discharges. -/

/-- Helper (proved here 2026-09-28): transfer of a successor-residue
equality back to the indices. -/
private theorem nat_succ_mod_p38 {k : ℕ} (hk : 0 < k) {a b : ℕ}
    (h : (a + 1) % k = (b + 1) % k) : a % k = b % k := by
  have e1 : a % k = (a + k) % k := (Nat.add_mod_right a k).symm
  have e2 : a + k = a + 1 + (k - 1) := by omega
  have e3 : b + k = b + 1 + (k - 1) := by omega
  rw [e1, e2, Nat.add_mod, h, ← Nat.add_mod, ← e3, Nat.add_mod_right]

/-- Helper (proved here 2026-09-28): transfer of a successor-residue
equality with a plain residue target to the shifted index. -/
private theorem nat_pred_mod_p38 {k : ℕ} (hk : 0 < k) {a b : ℕ}
    (h : (a + 1) % k = b % k) : a % k = (b + (k - 1)) % k := by
  have e1 : a % k = (a + k) % k := (Nat.add_mod_right a k).symm
  have e2 : a + k = a + 1 + (k - 1) := by omega
  rw [e1, e2, Nat.add_mod, h]
  exact (Nat.add_mod b (k - 1) k).symm

/-- Helper (proved here 2026-09-28): `vv` only sees the residue along one
period (the `Oxl_def.periodic_mod` down-pass; kept local because
`periodic_vv_inj` sits later in the file). -/
private theorem cycle_vv_mod_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk0 : 0 < k) (a : ℕ) : vv a = vv (a % k) := by
  have hdown : ∀ a : ℕ, vv a = vv (a % k) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      rcases Nat.lt_or_ge a k with hak | hak
      · rw [Nat.mod_eq_of_lt hak]
      · rw [show a = (a - k) + k by omega, hper (a - k), ih (a - k) (by omega),
          Nat.add_mod_right]
  exact hdown a

/-- Helper (proved here 2026-09-28): equal vertices give equal residues. -/
private theorem cycle_mod_inj_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk0 : 0 < k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    {a b : ℕ} (h : vv a = vv b) : a % k = b % k := by
  rw [cycle_vv_mod_p38 hper hk0 a, cycle_vv_mod_p38 hper hk0 b] at h
  exact hinj (a % k) (b % k) ⟨Nat.mod_lt a (by omega), Nat.mod_lt b (by omega), h⟩

/-- Helper (proved here 2026-09-28): equal residues give equal vertices. -/
private theorem cycle_mod_congr_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk0 : 0 < k) {a b : ℕ} (h : a % k = b % k) : vv a = vv b := by
  rw [cycle_vv_mod_p38 hper hk0 a, h, cycle_vv_mod_p38 hper hk0 b]

/-- Helper (proved here 2026-09-28): the cycle successor is never the same
vertex once `3 ≤ k`. -/
private theorem cycle_succ_ne_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (j : ℕ) : vv (j + 1) ≠ vv j := by
  have hk0 : 0 < k := by omega
  intro he
  have h4 : (j % k + 1) % k = j % k := by
    rw [Nat.mod_add_mod j k 1, cycle_mod_inj_p38 hper hk0 hinj he]
  have hr : j % k < k := Nat.mod_lt j hk0
  rcases Nat.lt_or_ge (j % k + 1) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h4; omega
  · rw [Nat.mod_eq_sub_mod hge] at h4
    rw [Nat.mod_eq_of_lt (by omega : j % k + 1 - k < k)] at h4
    omega

/-- Helper (proved here 2026-09-28): the two cycle neighbours of `vv i` are
distinct once `3 ≤ k`. -/
private theorem cycle_edge_ne_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (i : ℕ) : vv (i + 1) ≠ vv (i + (k - 1)) := by
  have hk0 : 0 < k := by omega
  intro he
  have hres := cycle_mod_inj_p38 hper hk0 hinj he
  have h2 : (i + 2) % k = i % k := by
    have t1 : (i + 2) % k = ((i + 1) % k + 1) % k :=
      (Nat.mod_add_mod (i + 1) k 1).symm
    rw [t1, hres, Nat.mod_add_mod (i + (k - 1)) k 1,
      show i + (k - 1) + 1 = i + k by omega, Nat.add_mod_right]
  have hr : i % k < k := Nat.mod_lt i hk0
  have h3 : (i % k + 2) % k = i % k := by
    rw [Nat.mod_add_mod i k 2]; exact h2
  rcases Nat.lt_or_ge (i % k + 2) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h3; omega
  · rw [Nat.mod_eq_sub_mod hge] at h3
    rw [Nat.mod_eq_of_lt (by omega : i % k + 2 - k < k)] at h3
    omega

/-- HOL `EE_vv` (terminal.hl:1254). DISCHARGED 2026-09-28: both inclusions
reduce, over the dart-pair equality `{vv j, vv (j + 1)} = {vv i, ww}`, to
`periodic_vv_inj` residue transfers (the degenerate singletons force
`vv (j + 1) = vv j`, excluded by `cycle_succ_ne_p38`). -/
theorem EE_vv (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    ee (vv i) (Set.range fun i => {vv i, vv (i + 1)}) =
      {vv (i + 1), vv (i + (k - 1))} := by
  have hk0 : 0 < k := by omega
  have hsucc := cycle_succ_ne_p38 hper hk hinj
  ext ww
  simp only [ee, Set.mem_setOf_eq, Set.mem_range, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj⟩
    -- hj : {vv j, vv (j + 1)} = {vv i, ww}
    have hvj : vv j = vv i ∨ vv j = ww := by
      have hm : vv j ∈ ({vv i, ww} : Set V3) := by rw [← hj]; simp
      simpa using hm
    have hvj1 : vv (j + 1) = vv i ∨ vv (j + 1) = ww := by
      have hm : vv (j + 1) ∈ ({vv i, ww} : Set V3) := by rw [← hj]; simp
      simpa using hm
    have hww : ww = vv j ∨ ww = vv (j + 1) := by
      have hm : ww ∈ ({vv j, vv (j + 1)} : Set V3) := by rw [hj]; simp
      simpa using hm
    rcases hvj with hAv | hAv
    · rcases hww with hBw | hBw
      · -- ww = vv j: the dart pair collapses to a singleton
        exfalso
        rw [← hAv] at hvj1
        rcases hvj1 with h | h
        · exact absurd h (hsucc j)
        · exact absurd (h.trans hBw) (hsucc j)
      · -- ww = vv (j + 1): residue transfer to the cycle successor
        refine Or.inl ?_
        have e1 : j % k = i % k := cycle_mod_inj_p38 hper hk0 hinj hAv
        have e2 : (j + 1) % k = (i + 1) % k := by
          rw [← Nat.mod_add_mod j k 1, e1, Nat.mod_add_mod i k 1]
        exact hBw.trans (cycle_mod_congr_p38 hper hk0 e2)
    · -- vv j = ww
      rcases hvj1 with hAv1 | hAv1
      · -- vv (j + 1) = vv i: residue transfer to the cycle predecessor
        refine Or.inr ?_
        have e1 : (j + 1) % k = i % k := cycle_mod_inj_p38 hper hk0 hinj hAv1
        have e2 : j % k = (i + (k - 1)) % k := nat_pred_mod_p38 hk0 e1
        exact hAv.symm.trans (cycle_mod_congr_p38 hper hk0 e2)
      · -- vv (j + 1) = ww = vv j: singleton clash again
        exfalso
        exact absurd (hAv1.trans hAv.symm) (hsucc j)
  · rintro (rfl | hw)
    · exact ⟨i, rfl⟩
    · refine ⟨i + (k - 1), ?_⟩
      have hlast : vv ((i + (k - 1)) + 1) = vv i := by
        rw [show (i + (k - 1)) + 1 = i + k by omega, hper i]
      rw [hlast, hw, Set.pair_comm]

/-- Helper (proved here 2026-09-28): the cycle edge set has exactly two
elements. -/
private theorem cycle_ee_ncard_p38 (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    (ee (vv i) (Set.range fun i => {vv i, vv (i + 1)})).ncard = 2 := by
  rw [EE_vv vv k i hper hk hinj]
  exact Set.ncard_pair (cycle_edge_ne_p38 hper hk hinj i)

/-- Helper (proved here 2026-09-28): `set_of_edge` over `Set.univ` is `ee`. -/
private theorem setOfEdge_univ_p38 (v : V3) (E : Set (Set V3)) :
    Kepler.Text.Fan.setOfEdge v Set.univ E = ee v E := by
  ext w
  simp [Kepler.Text.Fan.setOfEdge, ee]

/-- Helper (proved here 2026-09-28): the fan successor `sigmaFan` at a cycle
dart is the predecessor vertex `vv (i + (k - 1))` (the azim-minimal neighbour
is unique on the two-point edge set). -/
private theorem cycle_sigma_fan_p38 (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    Kepler.Text.Fan.sigmaFan 0 Set.univ (Set.range fun i => {vv i, vv (i + 1)}) (vv i)
      (vv (i + 1)) = vv (i + (k - 1)) := by
  set E : Set (Set V3) := Set.range fun i => {vv i, vv (i + 1)} with hEd
  have hE := EE_vv vv k i hper hk hinj
  have hne := cycle_edge_ne_p38 hper hk hinj i
  have hsoe : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E = ee (vv i) E :=
    setOfEdge_univ_p38 (vv i) E
  have hcond : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E ≠ {vv (i + 1)} := by
    intro hc
    rw [hsoe, hE] at hc
    have hmem : vv (i + (k - 1)) ∈ ({vv (i + 1)} : Set V3) := by rw [← hc]; simp
    rw [Set.mem_singleton_iff] at hmem
    exact hne hmem.symm
  have key : ∀ w, w ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E ∧ w ≠ vv (i + 1) ∧
      (∀ w1 ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E, w1 ≠ vv (i + 1) →
        azim 0 (vv i) (vv (i + 1)) w ≤ azim 0 (vv i) (vv (i + 1)) w1) →
      w = vv (i + (k - 1)) := by
    rw [hsoe, hE]
    rintro w ⟨hmem, hne2, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact absurd h hne2
    · exact h
  have hex : ∃ y, y ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E ∧ y ≠ vv (i + 1) ∧
      (∀ w1 ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E, w1 ≠ vv (i + 1) →
        azim 0 (vv i) (vv (i + 1)) y ≤ azim 0 (vv i) (vv (i + 1)) w1) := by
    refine ⟨vv (i + (k - 1)), ?_, hne.symm, ?_⟩
    · rw [hsoe, hE]; simp
    · rintro w1 hmem hne1
      rw [hsoe, hE] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact absurd h hne1
      · rw [h]
  simp only [Kepler.Text.Fan.sigmaFan]
  split
  · next hc => exact absurd hc hcond
  · next =>
    have heps := Classical.epsilon_spec_aux inferInstance _ hex
    exact key _ heps

/-- Helper (proved here 2026-09-28): `azim_in_fan` at a cycle dart is the
azimuth onto the cycle predecessor. -/
private theorem cycle_azim_in_fan_p38 (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    azimInFan (vv i, vv (i + 1)) (Set.range fun i => {vv i, vv (i + 1)})
      = azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1))) := by
  have hnc := cycle_ee_ncard_p38 vv k i hper hk hinj
  have hs := cycle_sigma_fan_p38 vv k i hper hk hinj
  rw [azimInFan, if_pos (show 1 < (ee (vv i) (Set.range fun i => {vv i, vv (i + 1)})).ncard
    from by rw [hnc]; norm_num), hs]

/-- Helper (proved here 2026-09-28): the cycle dart at index `i` is the dart
of the reduced index. -/
private theorem cycle_dart_mod_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk0 : 0 < k) (i : ℕ) :
    (vv i, vv (i + 1)) = (vv (i % k), vv (i % k + 1)) := by
  have h1 : vv i = vv (i % k) := cycle_vv_mod_p38 hper hk0 i
  have h2 : vv (i + 1) = vv (i % k + 1) := by
    have e1 : vv (i + 1) = vv ((i + 1) % k) := cycle_vv_mod_p38 hper hk0 (i + 1)
    have e2 : (i + 1) % k = (i % k + 1) % k := (Nat.mod_add_mod i k 1).symm
    rw [e1, e2, ← cycle_vv_mod_p38 hper hk0]
  rw [h1, h2]

/-- Helper (proved here 2026-09-28): the dart range is the image of one
period. -/
private theorem cycle_dart_image_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk0 : 0 < k) :
    Set.range (fun i => (vv i, vv (i + 1))) =
      (fun i => (vv i, vv (i + 1))) '' {i | i < k} := by
  ext p
  simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i % k, Nat.mod_lt i hk0, (cycle_dart_mod_p38 hper hk0 i).symm⟩
  · rintro ⟨i, -, rfl⟩
    exact Set.mem_range_self i

/-- Helper (proved here 2026-09-28): the dart map is injective on one
period. -/
private theorem cycle_dart_inj_p38 {vv : ℕ → V3} {k : ℕ} (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    Set.InjOn (fun i => (vv i, vv (i + 1))) (↑(Finset.range k) : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_range] at ha hb
  rw [Prod.mk.injEq] at hab
  exact hinj a b ⟨ha, hb, hab.1⟩

/-- Helper (proved here 2026-09-28): the dart range has `k` elements. -/
private theorem cycle_dart_ncard_p38 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    (Set.range fun i => (vv i, vv (i + 1))).ncard = k := by
  have hk0 : 0 < k := by omega
  rw [cycle_dart_image_p38 hper hk0,
    show (({i | i < k} : Set ℕ) : Set ℕ) = (↑(Finset.range k) : Set ℕ) from by
      rw [Finset.coe_range]; rfl,
    Set.InjOn.ncard_image (cycle_dart_inj_p38 hk hinj), Set.ncard_coe_finset,
    Finset.card_range]

/-- Helper (proved here 2026-09-28): `setSum` over the cycle dart range
reindexes to a sum over `Finset.range k`. -/
private theorem cycle_dart_sum_p38 {g : V3 × V3 → ℝ} {vv : ℕ → V3} {k : ℕ}
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    setSum (Set.range fun i => (vv i, vv (i + 1))) g
      = ∑ i ∈ Finset.range k, g (vv i, vv (i + 1)) := by
  have hk0 : 0 < k := by omega
  have hfin : (Set.range fun i => (vv i, vv (i + 1))).Finite := by
    rw [cycle_dart_image_p38 hper hk0]
    exact Set.Finite.image _ (Set.toFinite _)
  rw [setSumDifpos_p38 g hfin]
  have hto : hfin.toFinset =
      Finset.image (fun i => (vv i, vv (i + 1))) (Finset.range k) := by
    ext p
    rw [Set.Finite.mem_toFinset hfin, Set.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨i % k, Finset.mem_range.mpr (Nat.mod_lt i hk0),
        (cycle_dart_mod_p38 hper hk0 i).symm⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  rw [hto, Finset.sum_image (cycle_dart_inj_p38 hk hinj)]

/-- HOL `tau_fun_azim` (terminal.hl:1316). DISCHARGED 2026-09-28: the dart
range has `k` elements and the `setSum` reindexes over one period
(`cycle_dart_sum_p38`, `cycle_dart_ncard_p38`); each `azim_in_fan` value is
the azimuth onto `vv (i + (k - 1))` via `EE_vv` + `cycle_sigma_fan_p38`
(`cycle_azim_in_fan_p38`). -/
theorem tau_fun_azim (vv : ℕ → V3) (k : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) =
      setSum {i | i < k}
          (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1)))) -
        (Real.pi + sol0) * (k - 2) := by
  have hnc := cycle_dart_ncard_p38 hper hk hinj
  have hrhs : setSum {i | i < k}
      (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1))))
      = ∑ i ∈ Finset.range k,
        (rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1)))) := by
    have hfin : ({i | i < k} : Set ℕ).Finite := Set.toFinite _
    rw [setSumDifpos_p38 _ hfin]
    have hto : hfin.toFinset = Finset.range k := by
      ext j
      rw [Set.Finite.mem_toFinset hfin, Set.mem_setOf_eq, Finset.mem_range]
    rw [hto]
  show setSum (Set.range fun i => (vv i, vv (i + 1)))
      (fun e => rhoFun ‖e.1‖ * azimInFan e (Set.range fun i => {vv i, vv (i + 1)})) -
    (Real.pi + sol0) *
      (((Set.range fun i => (vv i, vv (i + 1))).ncard - 2 : ℕ) : ℝ) = _
  have hkcast : ((k : ℝ) - 2) = ((k - 2 : ℕ) : ℝ) :=
    (Nat.cast_sub (show 2 ≤ k by omega)).symm
  have hsum : (∑ i ∈ Finset.range k,
      (fun e => rhoFun ‖e.1‖ * azimInFan e (Set.range fun i => {vv i, vv (i + 1)}))
        (vv i, vv (i + 1)))
      = ∑ i ∈ Finset.range k,
        (rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only []
    rw [cycle_azim_in_fan_p38 vv k j hper hk hinj]
  rw [cycle_dart_sum_p38 hper hk hinj, hnc, hrhs, hkcast, hsum]

/-- HOL `vv_rho_node1` (terminal.hl:1382). DISCHARGED 2026-09-28: the dart
`(vv i, vv (i + 1))` is the unique `FF`-dart out of `vv i` (residue transfer
via `periodic_vv_inj`), so the defining `Classical.epsilon` picks it. -/
theorem vv_rho_node1 (vv : ℕ → V3) (k : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (i : ℕ) :
    rhoNode1 (Set.range fun i => (vv i, vv (i + 1))) (vv i) = vv (i + 1) := by
  have hk0 : 0 < k := by omega
  have hspec : ∀ w, (vv i, w) ∈ Set.range (fun i => (vv i, vv (i + 1))) →
      w = vv (i + 1) := by
    rintro w ⟨j, hj⟩
    rw [Prod.mk.injEq] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have e1 : j % k = i % k := cycle_mod_inj_p38 hper hk0 hinj hj1
    have e2 : (j + 1) % k = (i + 1) % k := by
      rw [← Nat.mod_add_mod j k 1, e1, Nat.mod_add_mod i k 1]
    exact hj2.symm.trans (cycle_mod_congr_p38 hper hk0 e2)
  show Classical.epsilon
      (fun w => (vv i, w) ∈ Set.range (fun i => (vv i, vv (i + 1)))) = vv (i + 1)
  have heps := Classical.epsilon_spec_aux inferInstance
    (fun w => (vv i, w) ∈ Set.range (fun i => (vv i, vv (i + 1))))
    ⟨vv (i + 1), Set.mem_range_self i⟩
  exact hspec _ heps

/-- HOL `ITER_vv_rho_node1` (terminal.hl:1418). DISCHARGED 2026-09-28 by
induction on `j` over `vv_rho_node1` (`vv (i + j + 1) = vv (i + (j + 1))` is
`omega` on the index). -/
theorem ITER_vv_rho_node1 (vv : ℕ → V3) (k j : ℕ) (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (i : ℕ) :
    (rhoNode1 (Set.range fun i => (vv i, vv (i + 1))))^[j] (vv i) = vv (i + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, vv_rho_node1 vv k hper hk hinj (i + j)]
    congr 1

/-- HOL `PRIOR_TO_LESS_THAN_PI_LEMMA_ALT` (terminal.hl:1440). -/
theorem PRIOR_TO_LESS_THAN_PI_LEMMA_ALT (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (hcf : ConvexLocalFan V E FF) (hv : v ∈ V)
    (w : V3) (hw : w ∈ V) :
    azim 0 v (rhoNode1 FF v) w ≤
      azim 0 v (rhoNode1 FF v)
        (azimCycle_p18 (ee v E) 0 v (rhoNode1 FF v)) := by
  sorry -- DISCHARGES: prior-to-less-than-pi fan lemma
  -- BLOCKED: needs LOCAL_FAN_RHO_NODE_PROS2 ((v, rhoNode1 FF v) in FF;
    -- hypermap-orbit content, unported).
    -- LocalFan; hypermap-orbit content, unported)

/-- HOL `vv_azim_le` (terminal.hl:1452). DISCHARGED 2026-09-28: the convex
local fan wedge condition at the dart `(vv i, vv (i + 1))` (whose edge set
has two elements, so `wedge_in_fan_ge` is the `wedgeGe` sector) reads off as
the claim once `sigmaFan` is computed (`cycle_sigma_fan_p38`). -/
theorem vv_azim_le (vv : ℕ → V3) (k i j : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hsub : Set.range vv ⊆ ballAnnulus)
    (hd1 : dist (vv i) (vv (i + 1)) < 4)
    (hd2 : dist (vv i) (vv (i + (k - 1))) < 4)
    (hd3 : dist (vv i) (vv j) < 4)
    (hmod : ¬(i % k = j % k))
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    azim 0 (vv i) (vv (i + 1)) (vv j) ≤
      azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  have hnc := cycle_ee_ncard_p38 vv k i hper hk hinj
  have hin : vv j ∈ wedgeInFanGe (vv i, vv (i + 1))
      (Set.range fun i => {vv i, vv (i + 1)}) :=
    (hcf.2 _ (Set.mem_range_self i)).2 (Set.mem_range_self j)
  rw [wedgeInFanGe, if_pos (show 1 < (ee (vv i, vv (i + 1)).1
      (Set.range fun i => {vv i, vv (i + 1)})).ncard from by
        rw [cycle_ee_ncard_p38 vv k i hper hk hinj]; norm_num)] at hin
  simp only [wedgeGe, Set.mem_setOf_eq] at hin
  rw [cycle_sigma_fan_p38 vv k i hper hk hinj] at hin
  rw [show i + k - 1 = i + (k - 1) by omega]
  exact hin.2

/-- Helper (proved here 2026-09-28): `(i + c) % k ≠ i % k` whenever `2 ≤ k`
and `c` is not a multiple of `k`. -/
private theorem p38_mod_add_ne {k c i : ℕ} (hk : 2 ≤ k) (hc : ¬(c % k = 0)) :
    (i + c) % k ≠ i % k := by
  have h1 : (i + c) % k = (i % k + c % k) % k := Nat.add_mod i c k
  have hilt : i % k < k := Nat.mod_lt i (by omega)
  have hclt : c % k < k := Nat.mod_lt c (by omega)
  rw [h1]
  rcases Nat.lt_or_ge (i % k + c % k) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    intro hcon
    exact hc (by omega)
  · have h2 : (i % k + c % k) % k = i % k + c % k - k := by
      have h3 : i % k + c % k - k < k := by omega
      have hx : i % k + c % k = (i % k + c % k - k) + k := by omega
      conv_lhs => rw [hx]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt h3]
    rw [h2]
    intro hcon
    exact hc (by omega)

set_option maxHeartbeats 10000000 in
/-- HOL `vv_split_azim` (terminal.hl:1492). DISCHARGED 2026-09-28: this is
`sum4_azim_fan` (TopologyFan, now on the import lane) applied over the
in-file `vv_azim_le` ordering, with the three non-collinearity side
conditions read off `NONPARALLEL_BALL_ANNULUS40_ALT` from the annulus box. -/
theorem vv_split_azim (vv : ℕ → V3) (k i j : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hsub : Set.range vv ⊆ ballAnnulus)
    (hd1 : dist (vv i) (vv (i + 1)) < 4)
    (hd2 : dist (vv i) (vv (i + (k - 1))) < 4)
    (hd3 : dist (vv i) (vv j) < 4)
    (hmod : ¬(i % k = j % k))
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) =
      azim 0 (vv i) (vv (i + 1)) (vv j) +
        azim 0 (vv i) (vv j) (vv (i + k - 1)) := by
  have hk0 : ¬(k = 0) := by omega
  have hk2 : 2 ≤ k := by omega
  have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hkm1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  have hdown : ∀ a : ℕ, vv a = vv (a % k) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      rcases Nat.lt_or_ge a k with hak | hak
      · rw [Nat.mod_eq_of_lt hak]
      · rw [show a = (a - k) + k by omega, hper (a - k), ih (a - k) (by omega),
          Nat.add_mod_right]
  have hcoll : ∀ m n : ℕ, 2 ≤ dist (vv m) (vv n) → dist (vv m) (vv n) < 4 →
      ¬ Collinear3 0 (vv m) (vv n) :=
    fun m n hge hlt => NONPARALLEL_BALL_ANNULUS40_ALT (vv m) (vv n) hge hlt
      (hsub (Set.mem_range_self m)) (hsub (Set.mem_range_self n))
  have hne0 : vv i ≠ 0 := by
    obtain ⟨hb, _⟩ := ballAnnulus_norm_bounds (hsub (Set.mem_range_self i))
    intro he
    rw [he] at hb
    rw [norm_zero] at hb
    linarith
  have hpv : ∀ m n : ℕ, vv m = vv n ↔ m % k = n % k := by
    intro m n
    constructor
    · intro he
      refine hinj (m % k) (n % k) ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), ?_⟩
      rw [← hdown m, ← hdown n, he]
    · intro h
      rw [hdown m, hdown n, h]
  have hsucc : ¬(vv i = vv (i + 1)) := fun he =>
    p38_mod_add_ne (k := k) (c := 1) (i := i) hk2
      (by rw [h1mod]; omega) (hpv _ _ |>.mp he).symm
  have hik : (i + (k - 1) : ℕ) = i + k - 1 := by omega
  have hge1 : 2 ≤ dist (vv i) (vv (i + 1)) := hsep i (i + 1) hsucc
  have hgej : 2 ≤ dist (vv i) (vv j) := hsep i j
    (fun he => hmod (hpv i j |>.mp he))
  have hgeik : 2 ≤ dist (vv i) (vv (i + k - 1)) := by
    have h := hsep i (i + (k - 1)) (fun he =>
      p38_mod_add_ne (k := k) (c := k - 1) (i := i) hk2
        (by rw [hkm1]; omega) (hpv _ _ |>.mp he).symm)
    rwa [hik] at h
  have hd2k : dist (vv i) (vv (i + k - 1)) < 4 := by
    rw [← hik]
    exact hd2
  exact sum4_azim_fan (x := 0) (v := vv i) (u := vv (i + 1)) (w1 := vv j)
    (w2 := vv (i + k - 1)) hne0 (hcoll i (i + 1) hge1 hd1) (hcoll i j hgej hd3)
    (hcoll i (i + k - 1) hgeik hd2k)
    (vv_azim_le vv k i j hper hk hsub hd1 hd2 hd3 hmod hsep hcf hinj)

/-- HOL `EGHNAVX1_ALT` (terminal.hl:1536). -/
theorem EGHNAVX1_ALT (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (bta : ℕ → ℝ) (v0 : V3) (ww : ℕ → V3) (k : ℕ)
    (hcf : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hcard : Nat.card V = k)
    (hnc : ∀ v, v ∈ V ∧ v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
    (hiter : ∀ i : ℕ, (rhoNode1 FF)^[i] v0 = ww i)
    (hbta : ∀ i : ℕ, azim 0 v0 (ww 1) (ww i) = bta i)
    (i j : ℕ) (hij : i < j ∧ j < k) :
    bta i ≤ bta j := by
  sorry -- DISCHARGES: monotone azim sequence around a fan vertex
  -- BLOCKED: needs Local_lemmas.EGHNAVX (deep monotonicity, unported).

/-- HOL `vv_split_azim_generic` (terminal.hl:1552). -/
theorem vv_split_azim_generic (vv : ℕ → V3) (k i j j' : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k) (hj : 0 < j) (hjj : j < j') (hj'k : j' < k)
    (hgen : Generic (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)}))
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ a b : ℕ, a < k ∧ b < k ∧ vv a = vv b → a = b) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + j')) =
      azim 0 (vv i) (vv (i + 1)) (vv (i + j)) +
        azim 0 (vv i) (vv (i + j)) (vv (i + j')) := by
  sorry -- DISCHARGES: generic azim splitting
  -- BLOCKED: needs EGHNAVX1_ALT + sum4_azim_fan (TopologyFan lane).
    -- sum4_azim_fan (TopologyFan lane)

/-- HOL `muR_ALT` (terminal.hl:1610): `rfl` by the `muRP38` definition. -/
theorem muR_ALT (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    muRP38 y1 y2 y3 y4 y5 y6 y7 y8 y9 =
      cayleyRP38 (y6 * y6) (y5 * y5) (y1 * y1) (y7 * y7) (y4 * y4) (y2 * y2)
        (y8 * y8) (y3 * y3) (y9 * y9) :=
  rfl

/-- HOL `enclosed4_lemma` (terminal.hl:1623). -/
theorem enclosed4_lemma (v0 v1 v2 v3 : V3) :
    0 < upsX (‖v0‖ * ‖v0‖) (‖v2‖ * ‖v2‖) (dist v0 v2 * dist v0 v2) →
      chiMsb [0, v0, v2] v1 * chiMsb [0, v0, v2] v3 ≤ 0 →
      dist v1 v3 =
        enclosedP38 ‖v1‖ (dist v0 v1) (dist v1 v2) (dist v0 v2) ‖v2‖ ‖v0‖
          ‖v3‖ (dist v0 v3) (dist v2 v3) := by
  intro _ _
  sorry -- DISCHARGES: chi_msb sign dichotomy (the enclosing-arc dichotomy)
  -- BLOCKED: enclosedP38 stub + the chi_msb branch identity (unported).

/-- HOL `IN_V_IMP_AZIM_LESS_PI_ALT` (terminal.hl:1768). -/
theorem IN_V_IMP_AZIM_LESS_PI_ALT (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (hcf : ConvexLocalFan V E FF) (hv : v ∈ V)
    (w : V3) (hw : w ∈ V) :
    azim 0 v (rhoNode1 FF v) w ≤ Real.pi := by
  sorry -- DISCHARGES: fan azim < pi
  -- BLOCKED: PRIOR_TO chain (LOCAL_FAN_RHO_NODE_PROS2 hole).
    -- hole)

/-- HOL `vv_enclosed4` (terminal.hl:1777). -/
theorem vv_enclosed4 (vv : ℕ → V3) (i : ℕ)
    (hper : Periodic vv 4)
    (hd1 : dist (vv i) (vv (i + 1)) < 4)
    (hd2 : dist (vv i) (vv (i + 3)) < 4)
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hsub : Set.range vv ⊆ ballAnnulus)
    (hd3 : dist (vv i) (vv (i + 2)) < 4)
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j) :
    dist (vv (i + 1)) (vv (i + 3)) =
      enclosedP38 ‖vv (i + 1)‖ (dist (vv i) (vv (i + 1)))
        (dist (vv (i + 1)) (vv (i + 2))) (dist (vv i) (vv (i + 2))) ‖vv (i + 2)‖
        ‖vv i‖ ‖vv (i + 3)‖ (dist (vv i) (vv (i + 3)))
        (dist (vv (i + 2)) (vv (i + 3))) := by
  sorry -- DISCHARGES: the k = 4 enclosed-arc identity (via vv_split_azim)
  -- BLOCKED: enclosedP38 stub + AZIM_LE_PI_EQ_DIHV (open at LocalAuto5).
    -- LocalAuto5:1788)

/-- HOL `enclosed_sym` (terminal.hl:1930). -/
theorem enclosed_sym (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 =
      enclosedP38 y1 y6 y5 y4 y3 y2 y7 y9 y8 := by
  sorry -- DISCHARGES: enclosedP38 body (external anchor)
  -- BLOCKED: enclosedP38 stub (body unported).

/-- HOL `enclosed_sym2` (terminal.hl:1946). -/
theorem enclosed_sym2 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 =
      enclosedP38 y7 y8 y9 y4 y2 y3 y1 y5 y6 := by
  sorry -- DISCHARGES: enclosedP38 body (external anchor)
  -- BLOCKED: enclosedP38 stub (body unported).

/-- HOL `convex_local_fan_azim_le_pi` (terminal.hl:1962). DISCHARGED
2026-09-28: the second `convex_local_fan` conjunct gives
`azim_in_fan (vv i, vv (i + 1)) ≤ pi`, and `cycle_azim_in_fan_p38` computes
that value as the claim. -/
theorem convex_local_fan_azim_le_pi (vv : ℕ → V3) (k i : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hsub : Set.range vv ⊆ ballAnnulus) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≤ Real.pi := by
  have hle := (hcf.2 _ (Set.mem_range_self i)).1
  rw [cycle_azim_in_fan_p38 vv k i hper hk hinj] at hle
  rw [show i + k - 1 = i + (k - 1) by omega]
  exact hle

/-- Helper (proved here 2026-09-28): the `AZIM_LE_PI_EQ_DIHV` bridge rendered
locally from LuneVolume's public `azim_dihv_same` / `azim_dihv_compl` —
on `azim ≤ π` the azimuth equals the geometric dihedral. -/
private theorem p38_azim_eq_dihV {v w v1 v2 : V3} (h1 : ¬ Collinear3 v w v1)
    (h2 : ¬ Collinear3 v w v2) (hp : azim v w v1 v2 ≤ Real.pi) :
    azim v w v1 v2 = dihV v w v1 v2 := by
  rcases lt_or_eq_of_le hp with hlt | heq
  · exact azim_dihv_same h1 h2 hlt
  · have hle : Real.pi ≤ azim v w v1 v2 := by rw [heq]
    have hc := azim_dihv_compl h1 h2 hle
    rw [heq]
    linarith

/-- Helper (proved here 2026-09-28): quad non-collinearity from the k = 4
separation kit — the annulus box plus `NONPARALLEL_BALL_ANNULUS40_ALT`. -/
private theorem p38_quad_ncoll {vv : ℕ → V3} (hsub : Set.range vv ⊆ ballAnnulus)
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j)
    {m n : ℕ} (hm : m < 4) (hn : n < 4) (hne : ¬(m = n))
    (hlt : dist (vv m) (vv n) < 4) : ¬ Collinear3 0 (vv m) (vv n) := by
  refine NONPARALLEL_BALL_ANNULUS40_ALT (vv m) (vv n) ?_ hlt
    (hsub (Set.mem_range_self m)) (hsub (Set.mem_range_self n))
  exact hsep m n (fun he => hne (hinj m n ⟨hm, hn, he⟩))

set_option maxHeartbeats 10000000 in
/-- HOL `vv_quad_split012` (terminal.hl:1996). DISCHARGED 2026-09-28: corners
0 and 2 split along the short diagonal by `vv_split_azim`, corners 1 and 3
convert wholesale via `p38_azim_eq_dihV`; after `rhoFun = rho` the four
`dihV`-corner terms rearrange into `tau3 (vv 0) (vv 1) (vv 2)` +
`tau3 (vv 2) (vv 3) (vv 0)` by `ring`. -/
theorem vv_quad_split012 (vv : ℕ → V3)
    (hper : Periodic vv 4) (hsub : Set.range vv ⊆ ballAnnulus)
    (hd1 : dist (vv 0) (vv 1) < 4) (hd2 : dist (vv 0) (vv 2) < 4)
    (hd3 : dist (vv 0) (vv 3) < 4) (hd4 : dist (vv 1) (vv 2) < 4)
    (hd5 : dist (vv 2) (vv 3) < 4)
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j) :
    (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
        rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) +
        rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) +
        rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 0) (vv 2)) -
      (Real.pi + sol0) * 2 =
      tau3 (vv 0) (vv 1) (vv 2) + tau3 (vv 2) (vv 3) (vv 0) := by
  have h40 : vv 4 = vv 0 := by rw [show (4 : ℕ) = 0 + 4 by norm_num]; exact hper 0
  have h50 : vv 5 = vv 1 := by rw [show (5 : ℕ) = 1 + 4 by norm_num]; exact hper 1
  have h62 : vv 6 = vv 2 := by rw [show (6 : ℕ) = 2 + 4 by norm_num]; exact hper 2
  have hS0 : azim 0 (vv 0) (vv 1) (vv 3)
      = azim 0 (vv 0) (vv 1) (vv 2) + azim 0 (vv 0) (vv 2) (vv 3) :=
    vv_split_azim vv 4 0 2 hper (by norm_num) hsub hd1 hd3 hd2 (by norm_num) hsep
      hcf hinj
  have hd52 : dist (vv 2) (vv (2 + (4 - 1))) < 4 := by
    rw [show (2 + (4 - 1) : ℕ) = 5 by norm_num, h50, dist_comm]
    exact hd4
  have hd20 : dist (vv 2) (vv 0) < 4 := by
    rw [dist_comm]
    exact hd2
  have hS2 : azim 0 (vv 2) (vv 3) (vv 1)
      = azim 0 (vv 2) (vv 3) (vv 0) + azim 0 (vv 2) (vv 0) (vv 1) := by
    have hs := vv_split_azim vv 4 2 0 hper (by norm_num) hsub hd5 hd52 hd20
      (by norm_num) hsep hcf hinj
    rwa [show (2 + 4 - 1 : ℕ) = 5 by norm_num, h50] at hs
  have hpi0 : azim 0 (vv 0) (vv 1) (vv 3) ≤ Real.pi :=
    convex_local_fan_azim_le_pi vv 4 0 hper (by norm_num) hinj hcf hsub
  have hpi1 : azim 0 (vv 1) (vv 2) (vv 0) ≤ Real.pi := by
    have h := convex_local_fan_azim_le_pi vv 4 1 hper (by norm_num) hinj hcf hsub
    rwa [show (1 + 4 - 1 : ℕ) = 4 by norm_num, h40] at h
  have hpi2 : azim 0 (vv 2) (vv 3) (vv 1) ≤ Real.pi := by
    have h := convex_local_fan_azim_le_pi vv 4 2 hper (by norm_num) hinj hcf hsub
    rwa [show (2 + 4 - 1 : ℕ) = 5 by norm_num, h50] at h
  have hpi3 : azim 0 (vv 3) (vv 0) (vv 2) ≤ Real.pi := by
    have h := convex_local_fan_azim_le_pi vv 4 3 hper (by norm_num) hinj hcf hsub
    rwa [show (3 + 4 - 1 : ℕ) = 6 by norm_num, h62, h40] at h
  have hnc01 := p38_quad_ncoll (m := 0) (n := 1) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd1
  have hnc02 := p38_quad_ncoll (m := 0) (n := 2) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd2
  have hnc03 := p38_quad_ncoll (m := 0) (n := 3) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd3
  have hnc12 := p38_quad_ncoll (m := 1) (n := 2) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd4
  have hnc23 := p38_quad_ncoll (m := 2) (n := 3) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd5
  have hnc10 := p38_quad_ncoll (m := 1) (n := 0) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd1)
  have hnc20 := p38_quad_ncoll (m := 2) (n := 0) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd2)
  have hnc21 := p38_quad_ncoll (m := 2) (n := 1) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd4)
  have hnc30 := p38_quad_ncoll (m := 3) (n := 0) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd3)
  have hnc32 := p38_quad_ncoll (m := 3) (n := 2) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd5)
  have ha012 : 0 ≤ azim 0 (vv 0) (vv 1) (vv 2) := azim_nonneg _ _ _ _
  have ha023 : 0 ≤ azim 0 (vv 0) (vv 2) (vv 3) := azim_nonneg _ _ _ _
  have hp012 : azim 0 (vv 0) (vv 1) (vv 2) ≤ Real.pi := by linarith
  have hp023 : azim 0 (vv 0) (vv 2) (vv 3) ≤ Real.pi := by linarith
  have ha230 : 0 ≤ azim 0 (vv 2) (vv 3) (vv 0) := azim_nonneg _ _ _ _
  have ha201 : 0 ≤ azim 0 (vv 2) (vv 0) (vv 1) := azim_nonneg _ _ _ _
  have hp230 : azim 0 (vv 2) (vv 3) (vv 0) ≤ Real.pi := by linarith
  have hp201 : azim 0 (vv 2) (vv 0) (vv 1) ≤ Real.pi := by linarith
  rw [rho_rho_fun, rho_rho_fun, rho_rho_fun, rho_rho_fun]
  simp only [tau3]
  rw [hS0, hS2, p38_azim_eq_dihV hnc01 hnc02 hp012,
    p38_azim_eq_dihV hnc02 hnc03 hp023, p38_azim_eq_dihV hnc12 hnc10 hpi1,
    p38_azim_eq_dihV hnc23 hnc20 hp230, p38_azim_eq_dihV hnc20 hnc21 hp201,
    p38_azim_eq_dihV hnc30 hnc32 hpi3]
  ring

set_option maxHeartbeats 10000000 in
/-- HOL `vv_quad_split123` (terminal.hl:2049). DISCHARGED 2026-09-28: mirror
of `vv_quad_split012` — corners 1 and 3 split, corners 0 and 2 convert
wholesale; the four `dihV` terms rearrange into `tau3 (vv 1) (vv 2) (vv 3)` +
`tau3 (vv 3) (vv 0) (vv 1)`. -/
theorem vv_quad_split123 (vv : ℕ → V3)
    (hper : Periodic vv 4) (hsub : Set.range vv ⊆ ballAnnulus)
    (hd1 : dist (vv 0) (vv 1) < 4) (hd2 : dist (vv 0) (vv 3) < 4)
    (hd3 : dist (vv 1) (vv 2) < 4) (hd4 : dist (vv 1) (vv 3) < 4)
    (hd5 : dist (vv 2) (vv 3) < 4)
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j) :
    (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
        rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) +
        rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) +
        rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 0) (vv 2)) -
      (Real.pi + sol0) * 2 =
      tau3 (vv 1) (vv 2) (vv 3) + tau3 (vv 3) (vv 0) (vv 1) := by
  have h40 : vv 4 = vv 0 := by rw [show (4 : ℕ) = 0 + 4 by norm_num]; exact hper 0
  have h50 : vv 5 = vv 1 := by rw [show (5 : ℕ) = 1 + 4 by norm_num]; exact hper 1
  have h62 : vv 6 = vv 2 := by rw [show (6 : ℕ) = 2 + 4 by norm_num]; exact hper 2
  have hd14 : dist (vv 1) (vv (1 + (4 - 1))) < 4 := by
    rw [show (1 + (4 - 1) : ℕ) = 4 by norm_num, h40, dist_comm]
    exact hd1
  have hd31 : dist (vv 3) (vv 1) < 4 := by
    rw [dist_comm]
    exact hd4
  have hS1 : azim 0 (vv 1) (vv 2) (vv 0)
      = azim 0 (vv 1) (vv 2) (vv 3) + azim 0 (vv 1) (vv 3) (vv 0) := by
    have hs := vv_split_azim vv 4 1 3 hper (by norm_num) hsub hd3 hd14 hd4
      (by norm_num) hsep hcf hinj
    rwa [show (1 + 4 - 1 : ℕ) = 4 by norm_num, h40] at hs
  have hd34 : dist (vv 3) (vv (3 + (4 - 1))) < 4 := by
    rw [show (3 + (4 - 1) : ℕ) = 6 by norm_num, h62, dist_comm]
    exact hd5
  have hd30 : dist (vv 3) (vv 0) < 4 := by
    rw [dist_comm]
    exact hd2
  have hS3 : azim 0 (vv 3) (vv 0) (vv 2)
      = azim 0 (vv 3) (vv 0) (vv 1) + azim 0 (vv 3) (vv 1) (vv 2) := by
    have hs := vv_split_azim vv 4 3 1 hper (by norm_num) hsub
      (by rw [show (3 + 1 : ℕ) = 4 by norm_num, h40]; exact hd30) hd34 hd31
      (by norm_num) hsep hcf hinj
    rwa [show (3 + 4 - 1 : ℕ) = 6 by norm_num, h62, h40] at hs
  have hpi0 : azim 0 (vv 0) (vv 1) (vv 3) ≤ Real.pi :=
    convex_local_fan_azim_le_pi vv 4 0 hper (by norm_num) hinj hcf hsub
  have hpi1 : azim 0 (vv 1) (vv 2) (vv 0) ≤ Real.pi := by
    have h := convex_local_fan_azim_le_pi vv 4 1 hper (by norm_num) hinj hcf hsub
    rwa [show (1 + 4 - 1 : ℕ) = 4 by norm_num, h40] at h
  have hpi2 : azim 0 (vv 2) (vv 3) (vv 1) ≤ Real.pi := by
    have h := convex_local_fan_azim_le_pi vv 4 2 hper (by norm_num) hinj hcf hsub
    rwa [show (2 + 4 - 1 : ℕ) = 5 by norm_num, h50] at h
  have hpi3 : azim 0 (vv 3) (vv 0) (vv 2) ≤ Real.pi := by
    have h := convex_local_fan_azim_le_pi vv 4 3 hper (by norm_num) hinj hcf hsub
    rwa [show (3 + 4 - 1 : ℕ) = 6 by norm_num, h62, h40] at h
  have hnc01 := p38_quad_ncoll (m := 0) (n := 1) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd1
  have hnc03 := p38_quad_ncoll (m := 0) (n := 3) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd2
  have hnc12 := p38_quad_ncoll (m := 1) (n := 2) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd3
  have hnc13 := p38_quad_ncoll (m := 1) (n := 3) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd4
  have hnc23 := p38_quad_ncoll (m := 2) (n := 3) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) hd5
  have hnc10 := p38_quad_ncoll (m := 1) (n := 0) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd1)
  have hnc21 := p38_quad_ncoll (m := 2) (n := 1) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd3)
  have hnc30 := p38_quad_ncoll (m := 3) (n := 0) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd2)
  have hnc31 := p38_quad_ncoll (m := 3) (n := 1) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd4)
  have hnc32 := p38_quad_ncoll (m := 3) (n := 2) hsub hsep hinj (by norm_num) (by norm_num)
    (by norm_num) (by rw [dist_comm]; exact hd5)
  have ha123 : 0 ≤ azim 0 (vv 1) (vv 2) (vv 3) := azim_nonneg _ _ _ _
  have ha130 : 0 ≤ azim 0 (vv 1) (vv 3) (vv 0) := azim_nonneg _ _ _ _
  have hp123 : azim 0 (vv 1) (vv 2) (vv 3) ≤ Real.pi := by linarith
  have hp130 : azim 0 (vv 1) (vv 3) (vv 0) ≤ Real.pi := by linarith
  have ha301 : 0 ≤ azim 0 (vv 3) (vv 0) (vv 1) := azim_nonneg _ _ _ _
  have ha312 : 0 ≤ azim 0 (vv 3) (vv 1) (vv 2) := azim_nonneg _ _ _ _
  have hp301 : azim 0 (vv 3) (vv 0) (vv 1) ≤ Real.pi := by linarith
  have hp312 : azim 0 (vv 3) (vv 1) (vv 2) ≤ Real.pi := by linarith
  rw [rho_rho_fun, rho_rho_fun, rho_rho_fun, rho_rho_fun]
  simp only [tau3]
  rw [hS1, hS3, p38_azim_eq_dihV hnc01 hnc03 hpi0,
    p38_azim_eq_dihV hnc12 hnc13 hp123, p38_azim_eq_dihV hnc13 hnc10 hp130,
    p38_azim_eq_dihV hnc23 hnc21 hpi2, p38_azim_eq_dihV hnc30 hnc31 hp301,
    p38_azim_eq_dihV hnc31 hnc32 hp312]
  ring

set_option maxHeartbeats 10000000 in
/-- HOL `vv_quad_split_short` (terminal.hl:2103). DISCHARGED 2026-09-28:
compare the two diagonals and invoke `vv_quad_split012` (resp.
`vv_quad_split123`) at `i = 0` (resp. `i = 1`); the `i + 2` / `i + 3`
index arithmetic is discharged by periodicity at `k = 4`. -/
theorem vv_quad_split_short (vv : ℕ → V3)
    (hper : Periodic vv 4) (hsub : Set.range vv ⊆ ballAnnulus)
    (hd1 : dist (vv 0) (vv 1) < 4) (hd2 : dist (vv 0) (vv 3) < 4)
    (hd3 : dist (vv 0) (vv 2) < 4) (hd4 : dist (vv 1) (vv 2) < 4)
    (hd5 : dist (vv 1) (vv 3) < 4) (hd6 : dist (vv 2) (vv 3) < 4)
    (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j) :
    ∃ i, i < 2 ∧ dist (vv i) (vv (i + 2)) ≤ dist (vv (i + 1)) (vv (i + 3)) ∧
      (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
          rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) +
          rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) +
          rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 0) (vv 2)) -
        (Real.pi + sol0) * 2 =
        tau3 (vv i) (vv (i + 1)) (vv (i + 2)) +
          tau3 (vv (i + 2)) (vv (i + 3)) (vv i) := by
  rcases le_or_gt (dist (vv 0) (vv 2)) (dist (vv 1) (vv 3)) with hdiag | hdiag
  · refine ⟨0, by norm_num, hdiag, ?_⟩
    exact vv_quad_split012 vv hper hsub hd1 hd3 hd2 hd4 hd6 hsep hcf hinj
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [show (1 + 2 : ℕ) = 3 by norm_num]
      have h24 : dist (vv 2) (vv (1 + 3)) = dist (vv 0) (vv 2) := by
        rw [show (1 + 3 : ℕ) = 0 + 4 by norm_num, hper 0, dist_comm]
      rw [h24]
      linarith
    · rw [show (1 + 3 : ℕ) = 0 + 4 by norm_num, hper 0]
      exact vv_quad_split123 vv hper hsub hd1 hd2 hd4 hd5 hd6 hsep hcf hinj

/-! ## Section F: terminal inequalities, k ≤ 3 bank (terminal.hl:2145-3100) -/

/-- HOL `SUC_EXPLICIT` (terminal.hl:2145). -/
theorem SUC_EXPLICIT :
    Nat.succ 0 = 1 ∧ Nat.succ 1 = 2 ∧ Nat.succ 2 = 3 ∧ Nat.succ 3 = 4 ∧
    Nat.succ 4 = 5 ∧ Nat.succ 5 = 6 ∧ Nat.succ 6 = 7 ∧ Nat.succ 7 = 8 ∧
    Nat.succ 8 = 9 := by
  norm_num

/-- HOL `cs_adj4_EXPLICIT` (terminal.hl:2153). -/
theorem cs_adj4_EXPLICIT (a b : ℝ) :
    csAdj 4 a b 0 0 = 0 ∧ csAdj 4 a b 0 1 = a ∧ csAdj 4 a b 0 2 = b ∧
    csAdj 4 a b 0 3 = a ∧ csAdj 4 a b 1 0 = a ∧ csAdj 4 a b 1 1 = 0 ∧
    csAdj 4 a b 1 2 = a ∧ csAdj 4 a b 1 3 = b ∧ csAdj 4 a b 2 0 = b ∧
    csAdj 4 a b 2 1 = a ∧ csAdj 4 a b 2 2 = 0 ∧ csAdj 4 a b 2 3 = a ∧
    csAdj 4 a b 3 0 = a ∧ csAdj 4 a b 3 1 = b ∧ csAdj 4 a b 3 2 = a ∧
    csAdj 4 a b 3 3 = 0 := by
  norm_num [csAdj]

/-- HOL `delta_4680581274` (terminal.hl:2179). DISCHARGED 2026-09-28 (the
HOL proof's arithmetic, no LP needed): with `y = y1^2`, `z = y4^2`,
`c = cstab^2`, the delta value is `(-64 + 32c - 4c^2) - y*z*(y + z - 12 - c)`;
the first summand is negative (as `c = 9.0601`), and the second is positive
since `y ≥ c > 0`, `z ≥ 16` and `y + z > 12 + c`. -/
theorem delta_4680581274 (y1 y4 : ℝ) (hy1 : cstab ≤ y1) (hy4 : 4 ≤ y4) :
    deltaY y1 2 2 y4 2 cstab < 0 := by
  have hy1p : 0 < y1 := lt_of_lt_of_le (by norm_num [cstab] : (0:ℝ) < cstab) hy1
  have hy4p : 0 < y4 := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) hy4
  have hcpos : (0 : ℝ) < cstab := by norm_num [cstab]
  have hy1c : 0 ≤ y1 - cstab := sub_nonneg.mpr hy1
  have hy4c : 0 ≤ y4 - 4 := sub_nonneg.mpr hy4
  have hyy : cstab * cstab ≤ y1 * y1 := by
    nlinarith [hy1c, hcpos]
  have hzz : 16 ≤ y4 * y4 := by
    nlinarith [hy4c, hy4p]
  have hsum : 12 + cstab * cstab < y1 * y1 + y4 * y4 := by linarith
  have key : deltaY y1 2 2 y4 2 cstab =
      (-64 : ℝ) + 32 * (cstab * cstab) - 4 * (cstab * cstab) ^ 2 -
        y1 * y1 * (y4 * y4) * (y1 * y1 + y4 * y4 - (12 + cstab * cstab)) := by
    show deltaX (y1 * y1) ((2 : ℝ) * 2) ((2 : ℝ) * 2) (y4 * y4) ((2 : ℝ) * 2)
      (cstab * cstab) = _
    simp only [deltaX]
    ring
  have hterm1 : (-64 : ℝ) + 32 * (cstab * cstab) - 4 * (cstab * cstab) ^ 2 < 0 := by
    norm_num [cstab]
  have hterm2 : 0 < y1 * y1 * (y4 * y4) * (y1 * y1 + y4 * y4 - (12 + cstab * cstab)) :=
    mul_pos (mul_pos (mul_pos hy1p hy1p) (mul_pos hy4p hy4p))
      (by nlinarith [hsum])
  rw [key]
  linarith

/-- HOL `tau3_sym` (terminal.hl:2218). DISCHARGED 2026-09-20: both
symmetries follow from `dihV_swap23_p38` — each `dihV` term rewrites to the
corresponding term of the permuted sum. -/
theorem tau3_sym (v0 v1 v2 : V3) :
    tau3 v0 v1 v2 = tau3 v0 v2 v1 ∧ tau3 v0 v1 v2 = tau3 v1 v0 v2 := by
  have h0 : ∀ a b c : V3, tau3 a b c = rho (norm a) * dihV 0 a b c +
      rho (norm b) * dihV 0 b c a + rho (norm c) * dihV 0 c a b -
      (Real.pi + sol0) := fun a b c => rfl
  constructor
  · rw [h0, h0, dihV_swap23_p38 0 v0 v1 v2, dihV_swap23_p38 0 v1 v2 v0,
      dihV_swap23_p38 0 v2 v0 v1]
    ring
  · rw [h0, h0, dihV_swap23_p38 0 v0 v1 v2, dihV_swap23_p38 0 v1 v2 v0,
      dihV_swap23_p38 0 v2 v0 v1]
    ring

/-- HOL `INSERT_SUBSET` (terminal.hl:2229). -/
theorem INSERT_SUBSET {α : Type*} (a : α) (A S : Set α) :
    insert a A ⊆ S ↔ a ∈ S ∧ A ⊆ S :=
  insert_subset_iff

/-- HOL `OWZLKVY0` (terminal.hl:2239). -/
theorem OWZLKVY0 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2 * h0 ∧ 2 ≤ y1 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧
      2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧ cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      200 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      0 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 (external anchor) + LP

/-- HOL `EAR_DELTA_X4` (terminal.hl:2264). -/
theorem EAR_DELTA_X4 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧
      cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      deltaY y1 y2 y3 y4 y5 y6 ≤ 200 →
      deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < 0 ∧
      0 < deltaX4 (y2 * y2) (y3 * y3) (y1 * y1) (y5 * y5) (y6 * y6) (y4 * y4) ∧
      0 < deltaX4 (y3 * y3) (y1 * y1) (y2 * y2) (y6 * y6) (y4 * y4) (y5 * y5) := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `EAR_DIH1_DELTA_0` (terminal.hl:2306). -/
theorem EAR_DIH1_DELTA_0 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧
      cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      deltaY y1 y2 y3 y4 y5 y6 = 0 →
      dihY y1 y2 y3 y4 y5 y6 = Real.pi := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `OWZLKVY3` (terminal.hl:2333). -/
theorem OWZLKVY3 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧
      cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 ∧
      dihY y1 y2 y3 y4 y5 y6 = Real.pi →
      sol0 * (y1 - 2 * h0) / (2 * h0 - 2) ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `OWZLKVY1` (terminal.hl:2420). -/
theorem OWZLKVY1 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧
      cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      -sol0 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `OWZLKVY2` (terminal.hl:2496). -/
theorem OWZLKVY2 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      y1 = 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧
      cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      0 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `sqrt8_bounds` (terminal.hl:2549). -/
theorem sqrt8_bounds :
    Real.sqrt 8 ≤ 3.01 ∧ 2 ≤ Real.sqrt 8 ∧ Real.sqrt 8 ≤ 3.62 := by
  have hs1 : 8 ≤ (3.01 : ℝ) ^ 2 := by norm_num
  have hs2 : (2 : ℝ) ^ 2 ≤ 8 := by norm_num
  have hs3 : 8 ≤ (3.62 : ℝ) ^ 2 := by norm_num
  exact ⟨(Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3.01)).mpr hs1,
    (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 8)).mpr hs2,
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3.62)).mpr hs3⟩

/-- HOL `empty_3T2` (terminal.hl:2558). -/
theorem empty_3T2 (h : main_nonlinear_terminal_v11) :
    ∀ vv : ℕ → V3, BBsV39 scs3T2 vv → 0 ≤ taustarV39 scs3T2 vv := by
  sorry -- DISCHARGES: the scs_3T2 emptiness of the BB set
  -- BLOCKED: taustar_taum (tau3_taum hole) + LP registry OMKYNLT 3336871894.
    -- registry OMKYNLT 3336871894 (external anchor)

/-- HOL `ineq_5691615370_asym` (terminal.hl:2797). -/
theorem ineq_5691615370_asym (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      ineqP38 [(3.0, y1, 3.0), (2, y2, 2.52), (2, y3, 2.52), (3.0, y4, 3.0),
        (2, y5, 2.52), (2, y6, 2.52)]
        (deltaY y1 y2 y3 y4 y5 y6 < 0 ∨
          y2 + y3 + y5 + y6 > 8.472) := by
  sorry -- DISCHARGES: LEMMA_5691615370 (LP asymmetric variant)

/-- Helper (proved here 2026-09-28): the 4-element index set sum expanded
over `{0, 1, 2, 3}` (generic form of `setSum4_p38`). -/
private theorem setSum_lt4_p38 (f : ℕ → ℝ) :
    setSum {i | i < 4} f = f 0 + f 1 + f 2 + f 3 + 0 := by
  have hsub : {i | i < 4} ⊆ {0, 1, 2, 3} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases x with _ | _ | _ | _ | x <;> simp_all <;> omega
  have hfin : ({i | i < 4} : Set ℕ).Finite :=
    Set.Finite.subset (Set.toFinite ({0, 1, 2, 3} : Set ℕ)) hsub
  rw [setSumDifpos_p38 f hfin]
  have hfinsub : hfin.toFinset ⊆ ({0, 1, 2, 3} : Finset ℕ) := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases x with _ | _ | _ | _ | x <;> simp_all <;> omega
  have h0 : ∀ x ∈ ({0, 1, 2, 3} : Finset ℕ), x ∉ hfin.toFinset →
      (if x ∈ ({i | i < 4} : Set ℕ) then f x else 0) = 0 := by
    intro x _ hx
    exact if_neg (fun hm => hx ((Set.Finite.mem_toFinset hfin).mpr hm))
  have key : ∑ w ∈ hfin.toFinset, f w =
      ∑ w ∈ hfin.toFinset, (if w ∈ ({i | i < 4} : Set ℕ) then f w else 0) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    exact (if_pos hw).symm
  rw [key, Finset.sum_subset hfinsub h0]
  simp [Set.mem_setOf_eq]
  ring

/-- HOL `terminal_quad_lemma` (terminal.hl:2834). DISCHARGED 2026-09-28: the
`k = 4` BB transfer expands `taustar_v39` (`dsv_J_empty` gives `dsv = d`),
reindexes `tau_fun` over one period via `tau_fun_azim` + `setSum_lt4_p38`,
and reads off `h2` (the `a`-positivity gives the cycle injectivity). -/
theorem terminal_quad_lemma (d : ℝ) (a b : ℕ → ℕ → ℝ)
    (h : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ i ≠ j → 0 < a i j)
    (h2 : ∀ vv : ℕ → V3, Set.range vv ⊆ ballAnnulus → Periodic vv 4 →
      (∀ i j : ℕ, a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ b i j) →
      ConvexLocalFan (Set.range vv)
        (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) →
        d ≤ (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
          rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 4) +
          rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 5) +
          rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 4) (vv 6) + 0) -
          (Real.pi + sol0) * (4 - 2))
    (vv : ℕ → V3) (hbb : BBsV39 (mkUnadornedV39 4 d a b) vv) :
    0 ≤ taustarV39 (mkUnadornedV39 4 d a b) vv := by
  obtain ⟨hrange, hper, hdij, hfan⟩ := hbb
  simp only [mkUnadornedV39] at hper hdij hfan
  have hfan' : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) := by
    rcases hfan with hle | h
    · exact absurd hle (by norm_num)
    · exact h
  have hinj' : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j := by
    intro i j hijk
    by_contra hne
    have hd0 : a i j ≤ dist (vv i) (vv j) := (hdij i j).1
    rw [hijk.2.2, dist_self] at hd0
    linarith [h i j ⟨hijk.1, hijk.2.1, hne⟩]
  show 0 ≤ tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) - dsvV39 (mkUnadornedV39 4 d a b) vv
  rw [dsv_J_empty _ vv rfl]
  simp only [mkUnadornedV39]
  rw [tau_fun_azim vv 4 hper (by norm_num) hinj', setSum_lt4_p38]
  norm_num
  linarith [h2 vv hrange hper hdij hfan']

/-! ## Section G: the x-space residual kit and the 4680581274 bank
(terminal.hl:3069-3950) -/

/-- HOL `tau_x_tau_residual_x_general` (terminal.hl:3069). -/
theorem tau_x_tau_residual_x_general (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 4 ≤ x1) (h2 : Real.sqrt x1 ≤ 2 * h0) (h3 : 0 < x1) (h4 : 0 < x2)
    (h5 : 0 < x3) (h6 : 0 < x4) (h7 : 0 < x5) (h8 : 0 < x6)
    (h9 : deltaX4 x1 x2 x3 x4 x5 x6 < 0)
    (h10 : 0 < deltaX4 x2 x3 x1 x5 x6 x4)
    (h11 : 0 < deltaX4 x3 x1 x2 x6 x4 x5)
    (h12 : 0 ≤ deltaX x1 x2 x3 x4 x5 x6) :
    taumXP38 x1 x2 x3 x4 x5 x6 =
      Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) * tauResidualXP38 x1 x2 x3 x4 x5 x6 +
        flatTermXP38 x1 := by
  sorry -- DISCHARGES: taum_x residual form (tau_x kit external anchor)

/-- HOL `OWZLKVY4` (terminal.hl:3149). -/
theorem OWZLKVY4 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2 * h0 ∧ 2 ≤ y2 ∧ y2 ≤ 2 * h0 ∧ 2 ≤ y3 ∧ y3 ≤ 2 * h0 ∧
      cstab ≤ y4 ∧ y4 ≤ 3.915 ∧ y5 = 2 ∧ y6 = 2 ∧
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      taudP38 y1 y2 y3 y4 y5 y6 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `muR_alt` (terminal.hl:3436): `rfl` by the `muRP38` definition. -/
theorem muR_alt (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    muRP38 y1 y2 y3 y4 y5 y6 y7 y8 y9 =
      cayleyRP38 (y6 * y6) (y5 * y5) (y1 * y1) (y7 * y7) (y4 * y4) (y2 * y2)
        (y8 * y8) (y3 * y3) (y9 * y9) :=
  rfl

/-- HOL `quad_cross_diag2_x_cayleyR` (terminal.hl:3450): `rfl` by the
`quadCrossDiag2XP38` definition (the `0 ≤ x` hypotheses are unused). -/
theorem quad_cross_diag2_x_cayleyR (x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ)
    (_ : 0 ≤ x1) (_ : 0 ≤ x2) (_ : 0 ≤ x3) (_ : 0 ≤ x4) (_ : 0 ≤ x5) (_ : 0 ≤ x6)
    (_ : 0 ≤ x7) (_ : 0 ≤ x8) (_ : 0 ≤ x9) :
    quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      Real.sqrt (quadraticRootPlus
        (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).1
        (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).2.1
        (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).2.2) :=
  rfl

/-- HOL `quadratic_root_upper_bound` (terminal.hl:3471). -/
theorem quadratic_root_upper_bound (a b c e x : ℝ) (ha : 0 < a)
    (hb : 0 < 2 * a * e + b) (hc : 0 < a * e ^ 2 + b * e + c)
    (h : a * x ^ 2 + b * x + c = 0) : x < e := by
  by_contra hge
  push_neg at hge
  have hsub : (x - e) * (a * (x + e) + b) = -(a * e ^ 2 + b * e + c) := by
    linear_combination h
  have hpos2 : 0 ≤ a * (x - e) := mul_nonneg ha.le (sub_nonneg.mpr hge)
  have hfact : 0 < a * (x + e) + b := by
    have hkey : a * (x + e) + b = (2 * a * e + b) + a * (x - e) := by ring
    rw [hkey]
    linarith
  have hnonneg : 0 ≤ (x - e) * (a * (x + e) + b) :=
    mul_nonneg (sub_nonneg.mpr hge) hfact.le
  linarith

/-- HOL `quadratic_square_root_upper_bound` (terminal.hl:3496). -/
theorem quadratic_square_root_upper_bound (a b c e : ℝ) (ha : 0 < a)
    (hb : 0 < 2 * a * e + b) (hc : 0 < a * e ^ 2 + b * e + c)
    (hd : 0 ≤ b ^ 2 - 4 * a * c) (hbn : b ≤ 0) (he : 0 ≤ e) :
    Real.sqrt (quadraticRootPlus a b c) < Real.sqrt e := by
  have hexp : (b + 2 * a * e) ^ 2 - (b ^ 2 - 4 * a * c) =
      4 * a * (a * e ^ 2 + b * e + c) := by ring
  have hm : (0 : ℝ) < a * (a * e ^ 2 + b * e + c) := by nlinarith [ha, hc]
  have hsq2 : b ^ 2 - 4 * a * c < (b + 2 * a * e) ^ 2 := by linarith [hexp, hm]
  have hsq3 : Real.sqrt ((b + 2 * a * e) ^ 2) = b + 2 * a * e :=
    Real.sqrt_sq (show (0 : ℝ) ≤ b + 2 * a * e by linarith)
  have hs : Real.sqrt (b ^ 2 - 4 * a * c) < b + 2 * a * e := by
    have h2 : Real.sqrt (b ^ 2 - 4 * a * c) < Real.sqrt ((b + 2 * a * e) ^ 2) :=
      Real.sqrt_lt_sqrt hd hsq2
    rwa [hsq3] at h2
  have hqrp : 0 ≤ quadraticRootPlus a b c := by
    rw [quadraticRootPlus]
    have hsq0 : 0 ≤ Real.sqrt (b ^ 2 - 4 * a * c) := Real.sqrt_nonneg _
    have h2a : (0 : ℝ) ≤ 2 * a := by linarith
    exact div_nonneg (by linarith [hbn, hsq0]) h2a
  have hlt2 : quadraticRootPlus a b c < e := by
    rw [quadraticRootPlus]
    have h2a : (0 : ℝ) < 2 * a := by linarith
    have h3 : -b + Real.sqrt (b ^ 2 - 4 * a * c) < e * (2 * a) := by linarith
    exact (div_lt_iff₀ h2a).mpr h3
  exact Real.sqrt_lt_sqrt hqrp hlt2

/-- HOL `abc_of_quadratic_cayleyR` (terminal.hl:3518). -/
theorem abc_of_quadratic_cayleyR (x12 x13 x14 x15 x23 x24 x25 x34 x35 : ℝ) :
    abcOfQuadraticP38 (cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35) =
      (upsX x12 x13 x23,
        cayleytrP38 x12 x13 x14 x15 x23 x24 x25 x34 x35 0,
        cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35 0) := by
  sorry -- DISCHARGES: cayleyR coefficients (the a-conic = ups_x identity)

/-- HOL `cayleyR_disc` (terminal.hl:3535). -/
theorem cayleyR_disc (x12 x13 x14 x15 x23 x24 x25 x34 x35 : ℝ) :
    (abcOfQuadraticP38 (cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35)).2.1 ^ 2 -
      4 * (abcOfQuadraticP38 (cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35)).1 *
        (abcOfQuadraticP38 (cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35)).2.2 =
      16 * deltaP x12 x13 x14 x23 x24 x34 * deltaP x12 x13 x15 x23 x25 x35 := by
  sorry -- DISCHARGES: the cayleyR discriminant identity

/-- HOL `quad_cross_diag2_x_bound` (terminal.hl:3551). -/
theorem quad_cross_diag2_x_bound (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℝ)
    (_ : 0 ≤ x1) (_ : 0 ≤ x2) (_ : 0 ≤ x3) (_ : 0 ≤ x4) (_ : 0 ≤ x5) (_ : 0 ≤ x6)
    (_ : 0 ≤ x7) (_ : 0 ≤ x8) (_ : 0 ≤ x9) (_ : 0 ≤ x10)
    (hups : 0 < upsX x2 x3 x4)
    (hd1 : 0 ≤ deltaX x1 x2 x3 x4 x5 x6)
    (hd2 : 0 ≤ deltaX x7 x2 x3 x4 x8 x9)
    (hlin : 0 < 2 * upsX x2 x3 x4 * x10 +
      cayleytrP38 x3 x2 x1 x7 x4 x5 x8 x6 x9 0)
    (hcay : 0 < cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9 x10)
    (htr : cayleytrP38 x3 x2 x1 x7 x4 x5 x8 x6 x9 0 ≤ 0) :
    quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 < Real.sqrt x10 := by
  sorry -- DISCHARGES: quadratic_root_upper_bound over the cross Cayley

/-- HOL `sq_imp_nn` (terminal.hl:3592). -/
theorem sq_imp_nn (c x : ℝ) (h : c ^ 2 ≤ x) : 0 ≤ x :=
  le_trans (sq_nonneg c) h

/-- HOL `LEMMA_4680581274_delta_issue_ups` (terminal.hl:3604). DISCHARGED
2026-09-28: the first disjunct alone settles it — on the box
`x2, x3 ∈ [4, 6.3504]`, `x4 ∈ [9.0601, 10.023556]` one has
`upsX x2 x3 x4 = 4·x2·x3 − (x4 − x2 − x3)² ≥ 64 − 3.7² > 0`; every
out-of-box alternative closes its own `ineqP38` disjunct. -/
theorem LEMMA_4680581274_delta_issue_ups (x1 x2 x3 x4 x5 x6 : ℝ) :
    ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26),
      (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26), (3.01 * 3.01, x4, 3.166 * 3.166),
      (4.0, x5, 4.0), (4.0, x6, 4.0)]
      (0 < upsX x2 x3 x4 ∨
        10 + deltaX x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
        deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0) := by
  have hnum1 : (2.0 * 1.26 * 2.0 * 1.26 : ℝ) = 6.3504 := by norm_num
  have hnum2 : (3.01 * 3.01 : ℝ) = 9.0601 := by norm_num
  have hnum3 : (3.166 * 3.166 : ℝ) = 10.023556 := by norm_num
  rw [hnum1, hnum2, hnum3]
  rcases lt_or_ge x1 4.0 with c | c
  · exact Or.inl c
  rcases lt_or_ge 6.3504 x1 with c | c
  · exact Or.inr (Or.inl c)
  rcases lt_or_ge x2 4.0 with h2lo | h2lo
  · exact Or.inr (Or.inr (Or.inl h2lo))
  rcases lt_or_ge 6.3504 x2 with h2hi | h2hi
  · exact Or.inr (Or.inr (Or.inr (Or.inl h2hi)))
  rcases lt_or_ge x3 4.0 with h3lo | h3lo
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3lo))))
  rcases lt_or_ge 6.3504 x3 with h3hi | h3hi
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3hi)))))
  rcases lt_or_ge x4 9.0601 with c | c
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
  rcases lt_or_ge 10.023556 x4 with h4hi | h4hi
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4hi)))))))
  rcases lt_or_ge x5 4.0 with c | c
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl c))))))))
  rcases lt_or_ge 4.0 x5 with c | c
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl c)))))))))
  rcases lt_or_ge x6 4.0 with c | c
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl c))))))))))
  rcases lt_or_ge 4.0 x6 with c | c
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl c)))))))))))
  -- all six coordinates lie in their boxes
  have hge : (4 : ℝ) * x2 * x3 ≥ 64 := by nlinarith
  have htsq : (x4 - x2 - x3) ^ 2 ≤ 3.7 ^ 2 := by
    have hp : (0 : ℝ) ≤ 3.7 + (x4 - x2 - x3) := by linarith
    have hq : (0 : ℝ) ≤ 3.7 - (x4 - x2 - x3) := by linarith
    have hprod : (3.7 + (x4 - x2 - x3)) * (3.7 - (x4 - x2 - x3)) ≥ 0 :=
      mul_nonneg hp hq
    have hexp : 3.7 ^ 2 - (x4 - x2 - x3) ^ 2 =
        (3.7 + (x4 - x2 - x3)) * (3.7 - (x4 - x2 - x3)) := by ring
    linarith
  have hups : 0 < upsX x2 x3 x4 := by
    have hring : upsX x2 x3 x4 = 4 * x2 * x3 - (x4 - x2 - x3) ^ 2 := by
      simp only [upsX]
      ring
    rw [hring]
    linarith
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl hups))))))))))))

/-- HOL `quad_4680581274_delta_issue` (terminal.hl:3639; the leading
`// quad_nonlinear_v4 /` source-comment artifact is dropped, anchor kept). -/
theorem quad_4680581274_delta_issue (h : main_nonlinear_terminal_v11) :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ,
      0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
      0 ≤ deltaX x7 x2 x3 x4 x8 x9 →
      ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26),
        (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26),
        (3.01 * 3.01, x4, 3.166 * 3.166), (4.0, x5, 4.0), (4.0, x6, 4.0),
        (4.0, x7, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x8, 4.0),
        (3.01 * 3.01, x9, 3.01 * 3.01)]
        (unit6P38 x1 x2 x3 x4 x5 x6 * 10 + deltaX x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
          deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
          quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 +
            unit6P38 x1 x2 x3 x4 x5 x6 * -3.01 < 0) := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `quad_4680581274_a` (terminal.hl:3791; leading `//` artifact
dropped as above). -/
theorem quad_4680581274_a (h : main_nonlinear_terminal_v11) :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ,
      ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26),
        (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26),
        (3.01 * 3.01, x4, 3.166 * 3.166), (4.0, x5, 4.0), (4.0, x6, 4.0),
        (4.0, x7, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x8, 4.0),
        (3.01 * 3.01, x9, 3.01 * 3.01)]
        (unit6P38 x1 x2 x3 x4 x5 x6 * 0.513 +
            taumXP38 x1 x2 x3 x4 x5 x6 * -1 +
            taumXP38 x7 x2 x3 x4 x8 x9 * -1 < 0 ∨
          deltaX x1 x2 x3 x4 x5 x6 + unit6P38 x1 x2 x3 x4 x5 x6 * -10 < 0 ∨
          deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
          quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 +
            unit6P38 x1 x2 x3 x4 x5 x6 * -3.01 < 0) := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `quad_4680581274_y` (terminal.hl:3854; leading `//` artifact
dropped as above). -/
theorem quad_4680581274_y (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ,
      ineqP38 [(2.0, y1, 2 * h0), (2.0, y2, 2 * h0), (2.0, y3, 2 * h0),
        (3.01, y4, 3.166), (2.0, y5, 2), (2.0, y6, 2), (2.0, y7, 2 * h0),
        (2.0, y8, 2), (3.01, y9, 3.01)]
        (tauqP38 y1 y2 y3 y4 y5 y6 y7 y8 y9 > 0.513 ∨
          deltaY y1 y2 y3 y4 y5 y6 < 10 ∨
          delta4Y y1 y2 y3 y4 y5 y6 > 0 ∨
          enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 < 3.01) := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `taum_x_sym` (terminal.hl:3752): the x1/x2/x3-slot symmetry of
`taum_x`; the external-anchor stub body blocks `rfl`. -/
theorem taum_x_sym (x1 x2 x3 x4 x5 x6 : ℝ) :
    taumXP38 x1 x3 x2 x4 x6 x5 = taumXP38 x1 x2 x3 x4 x5 x6 := by
  sorry -- DISCHARGES: taum_x body (external anchor)

/-- HOL `taud_x_taum_x` (terminal.hl:3764). -/
theorem taud_x_taum_x (h : main_nonlinear_terminal_v11) :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      4 ≤ x1 → x1 ≤ (2 * h0) ^ 2 → 4 ≤ x2 → x2 ≤ (2 * h0) ^ 2 →
      4 ≤ x3 → x3 ≤ (2 * h0) ^ 2 → cstab ^ 2 ≤ x4 → x4 ≤ 3.915 ^ 2 →
      x5 = 4 → x6 = 4 → 0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
      taudXP38 x1 x2 x3 x4 x5 x6 ≤ taumXP38 x1 x2 x3 x4 x5 x6 := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-- HOL `quad_4680581274_derived` (terminal.hl:3886): conclusion after the
inline `// added Jun 28, 2014` / `// #0.616 - #0.11` source comments. -/
theorem quad_4680581274_derived (h : main_nonlinear_terminal_v11) :
    ∀ y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ,
      ineqP38 [(3.01, y0, 4), (2.0, y1, 2 * h0), (2.0, y2, 2 * h0),
        (2.0, y3, 2 * h0), (3.01, y4, 4), (2.0, y5, 2), (2.0, y6, 2),
        (2.0, y7, 2 * h0), (2.0, y8, 2), (3.01, y9, 3.01)]
        (enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 = y0 ∧
          y4 ≤ y0 ∧
          0 ≤ deltaY y0 y9 y8 y4 y5 y6 ∧
          0 ≤ deltaY y1 y2 y3 y4 y5 y6 ∧
          0 ≤ deltaY y7 y2 y3 y4 y8 y9 →
          0.513 < tauqP38 y1 y2 y3 y4 y5 y6 y7 y8 y9) := by
  sorry -- DISCHARGES: main_nonlinear_terminal_v11 + LP

/-! ## Section D cont.: the remaining funlist / periodicity kit
(terminal.hl:868-1000) -/

/-- HOL `funlist_kik` (terminal.hl:868). -/
theorem funlist_kik (b : List ((ℕ × ℕ) × ℝ)) (b0 : ℝ) (k i : ℕ) :
    funlistV39 b b0 k i k = funlistV39 b b0 k 0 i := by
  by_cases hik : i % k = 0
  · simp [funlistV39, psort, hik, Nat.mod_self]
  · simp [funlistV39, psort, hik, Nat.mod_self]
    omega

/-- HOL `periodic_mod_reduce` (terminal.hl:884). -/
theorem periodic_mod_reduce (P : ℕ → Prop) (k : ℕ) (hk : ¬(k = 0))
    (hper : Periodic P k) (hb : ∀ i, i < k → P i) (i : ℕ) : P i := by
  have hdown : ∀ a : ℕ, P a = P (a % k) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      rcases Nat.lt_or_ge a k with hak | hak
      · rw [Nat.mod_eq_of_lt hak]
      · rw [show a = (a - k) + k by omega, hper (a - k), ih (a - k) (by omega),
          Nat.add_mod_right]
  rw [hdown i]
  exact hb _ (Nat.mod_lt i (Nat.pos_of_ne_zero hk))

/-- HOL `periodic2_mod_reduce` (terminal.hl:897). -/
theorem periodic2_mod_reduce (P : ℕ → ℕ → Prop) (k : ℕ) (hk : ¬(k = 0))
    (hper : Periodic2 P k) (hb : ∀ i j : ℕ, i < k ∧ j < k → P i j) (i j : ℕ) :
    P i j := by
  have hred : ∀ a b : ℕ, P a b = P (a % k) (b % k) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a iha =>
      intro b
      induction b using Nat.strong_induction_on with
      | _ b ihb =>
        rcases Nat.lt_or_ge a k with hak | hak
        · rcases Nat.lt_or_ge b k with hbk | hbk
          · rw [Nat.mod_eq_of_lt hak, Nat.mod_eq_of_lt hbk]
          · rw [show b = (b - k) + k by omega, (hper a (b - k)).2,
              ihb (b - k) (by omega), Nat.mod_eq_of_lt hak, Nat.add_mod_right]
        · rw [show a = (a - k) + k by omega, (hper (a - k) b).1,
            iha (a - k) (by omega) b, Nat.add_mod_right]
  rw [hred i j]
  exact hb _ _ ⟨Nat.mod_lt i (Nat.pos_of_ne_zero hk),
    Nat.mod_lt j (Nat.pos_of_ne_zero hk)⟩

/-- HOL `periodic2_mod_sym_reduce` (terminal.hl:923). -/
theorem periodic2_mod_sym_reduce (P : ℕ → ℕ → Prop) (k : ℕ)
    (hk : ¬(k = 0)) (hper : Periodic2 P k) (hdiag : ∀ i, P i i)
    (hsym : ∀ i j, P i j = P j i)
    (htri : ∀ i j, i < j ∧ j < k → P i j) (i j : ℕ) : P i j := by
  have hmod := periodic2_mod_reduce P k hk hper (by
    intro a b hab
    rcases Nat.lt_trichotomy a b with hlt | heq | hgt
    · exact htri a b ⟨hlt, hab.2⟩
    · rw [heq]
      exact hdiag b
    · rw [← hsym b a]
      exact htri b a ⟨hgt, hab.1⟩)
  exact hmod i j

/-- HOL `periodic2_SUC_periodic` (terminal.hl:944). -/
theorem periodic2_SUC_periodic (f : ℕ → ℕ → Prop) (k : ℕ)
    (h : Periodic2 f k) : Periodic (fun i => f i (i + 1)) k := by
  intro i
  have h1 := (h i ((i + k) + 1)).1
  have h2 := (h i (i + 1)).2
  show f (i + k) ((i + k) + 1) = f i (i + 1)
  rw [h1, show (i + k) + 1 = (i + 1) + k by omega, h2]

/-- HOL `periodic_vv_inj` (terminal.hl:957). -/
theorem periodic_vv_inj {A : Sort u} (vv : ℕ → A) (k : ℕ) (hper : Periodic vv k)
    (hk : ¬(k = 0))
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (i j : ℕ) : vv i = vv j ↔ i % k = j % k := by
  have hdown : ∀ a : ℕ, vv a = vv (a % k) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      rcases Nat.lt_or_ge a k with hak | hak
      · rw [Nat.mod_eq_of_lt hak]
      · rw [show a = (a - k) + k by omega, hper (a - k), ih (a - k) (by omega),
          Nat.add_mod_right]
  constructor
  · intro h
    refine hinj (i % k) (j % k) ⟨Nat.mod_lt i (Nat.pos_of_ne_zero hk),
      Nat.mod_lt j (Nat.pos_of_ne_zero hk), ?_⟩
    rw [← hdown i, ← hdown j, h]
  · intro h
    rw [hdown i, hdown j, h]

/-- HOL `I_LT_J_LT_3_EXPLICIT` (terminal.hl:975). -/
theorem I_LT_J_LT_3_EXPLICIT (i j : ℕ) :
    (i < j ∧ j < 3) ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) :=
  by omega

/-- HOL `I_LT_J_LT_4_EXPLICIT` (terminal.hl:983). -/
theorem I_LT_J_LT_4_EXPLICIT (i j : ℕ) :
    (i < j ∧ j < 4) ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) :=
  by omega

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
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto23
import Kepler.Text.SphereKit
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

/-- HOL `DIH_X_NN` (terminal.hl:85). -/
theorem DIH_X_NN :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      0 < x1 → 0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
      0 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  intro x1 x2 x3 x4 x5 x6 _ _
  sorry -- DISCHARGES: dih_x nonneg from the arccos form

/-- HOL `DIH_Y_NN` (terminal.hl:114). -/
theorem DIH_Y_NN :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      0 < y1 → 0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      0 ≤ dihY y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6 _ _
  sorry -- DISCHARGES: dih_y nonneg from the arccos form

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

/-- HOL `taum_taum_x` (terminal.hl:169): `taum` is `y_of_x taum_x`. -/
theorem taum_taum_x :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, 0 ≤ y1 → 0 ≤ y2 → 0 ≤ y3 → 0 ≤ y4 → 0 ≤ y5 →
      0 ≤ y6 →
      taum y1 y2 y3 y4 y5 y6 = yOfX taumXP38 y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6 _ _ _ _ _ _
  sorry -- DISCHARGES: taum_x body (external anchor taumXP38 = stub)

/-! ## Section B: the scs record kit (terminal.hl:184-309) -/

/-- HOL `BBs_terminal` (terminal.hl:184): the terminal SCS case bank. -/
theorem BBs_terminal :
    ∀ s ∈ scsTerminalV116_p38, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv := by
  intro s _ _
  sorry -- DISCHARGES: the scs_terminal_v116 case list (local-fan lane anchor)

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

/-- HOL `SUM_INTER` (terminal.hl:233). The HOL `sum` junk convention (0 on
infinite sets) matches `setSum`; proved here for finite `A`, and in the junk
regime (`A` infinite) for `(A ∩ B)` infinite; the remaining mixed case is
the flyspeck-junk hole (their use sites keep `A` finite). -/
theorem SUM_INTER {α : Type*} (A B : Set α) (f : α → ℝ) :
    setSum (A ∩ B) f = setSum A (fun i => if i ∈ B then f i else 0) := by
  by_cases hAB : (A ∩ B).Finite
  · rw [setSumDifpos_p38 f hAB]
    by_cases hAf : A.Finite
    · rw [setSumDifpos_p38 (fun i => if i ∈ B then f i else 0) hAf]
      have hsub : hAB.toFinset ⊆ hAf.toFinset := by
        intro w hw
        rw [Set.Finite.mem_toFinset] at hw ⊢
        exact hw.1
      have h0 : ∀ w ∈ hAf.toFinset, w ∉ hAB.toFinset →
          (if w ∈ B then f w else 0) = 0 := by
        intro w hAw hw
        rw [if_neg (fun hB => hw ((Set.Finite.mem_toFinset hAB).mpr
          ⟨(Set.Finite.mem_toFinset hAf).mp hAw, hB⟩))]
      have key : ∑ w ∈ hAB.toFinset, f w =
          ∑ w ∈ hAB.toFinset, (if w ∈ B then f w else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [Set.Finite.mem_toFinset] at hw
        rw [if_pos hw.2]
      rw [key, Finset.sum_subset hsub h0]
    · rw [setSumDifneg_p38 (fun i => if i ∈ B then f i else 0) hAf]
      sorry -- junk caveat: `A ∩ B` finite while `A` infinite (never used)
  · by_cases hAf : A.Finite
    · exact absurd (Set.Finite.subset hAf Set.inter_subset_left) hAB
    · rw [setSumDifneg_p38 f hAB, setSumDifneg_p38 _ hAf]

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

/-- HOL `NONPARALLEL_BALL_ANNULUS40` (terminal.hl:383). -/
theorem NONPARALLEL_BALL_ANNULUS40 (v w : V3) :
    2 ≤ ‖v - w‖ → ‖v - w‖ < 4 → v ∈ ballAnnulus → w ∈ ballAnnulus →
    ¬ Collinear ℝ ({0, v, w} : Set V3) := by
  intro _ _ _ _ h
  sorry -- DISCHARGES: Cauchy-Schwarz equality route (NORM_CAUCHY_SCHWARZ_EQUAL)

/-- HOL `NONPARALLEL_BALL_ANNULUS_ALT` (terminal.hl:451; the `// was cstab`
comment is verbatim source). -/
theorem NONPARALLEL_BALL_ANNULUS_ALT (v w : V3) :
    2 ≤ dist v w → dist v w ≤ 3.62 → v ∈ ballAnnulus → w ∈ ballAnnulus →
    ¬ Collinear ℝ ({0, v, w} : Set V3) := by
  intro _ _ _ _ h
  sorry -- DISCHARGES: as NONPARALLEL_BALL_ANNULUS40

/-- HOL `NONPARALLEL_BALL_ANNULUS40_ALT` (terminal.hl:470). -/
theorem NONPARALLEL_BALL_ANNULUS40_ALT (v w : V3) :
    2 ≤ dist v w → dist v w < 4 → v ∈ ballAnnulus → w ∈ ballAnnulus →
    ¬ Collinear ℝ ({0, v, w} : Set V3) := by
  intro _ _ _ _ h
  sorry -- DISCHARGES: as NONPARALLEL_BALL_ANNULUS40

/-- HOL `tau3_taum` (terminal.hl:489). -/
theorem tau3_taum (v0 v1 v2 : V3) :
    v0 ∈ ballAnnulus → v1 ∈ ballAnnulus → v2 ∈ ballAnnulus →
    2 ≤ dist v0 v1 → 2 ≤ dist v0 v2 → 2 ≤ dist v1 v2 →
    dist v0 v1 ≤ 3.62 → dist v0 v2 ≤ 3.62 → dist v1 v2 ≤ 3.62 →
    tau3 v0 v1 v2 =
      taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  intro _ _ _ _ _ _ _ _ _
  sorry -- DISCHARGES: tau3-to-taum formula transfer

/-- HOL `tau3_taum_40` (terminal.hl:513): the `< &4` variant. -/
theorem tau3_taum_40 (v0 v1 v2 : V3) :
    v0 ∈ ballAnnulus → v1 ∈ ballAnnulus → v2 ∈ ballAnnulus →
    2 ≤ dist v0 v1 → 2 ≤ dist v0 v2 → 2 ≤ dist v1 v2 →
    dist v0 v1 < 4 → dist v0 v2 < 4 → dist v1 v2 < 4 →
    tau3 v0 v1 v2 =
      taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  intro _ _ _ _ _ _ _ _ _
  sorry -- DISCHARGES: tau3-to-taum formula transfer

/-- HOL `DELTA_Y_POS_4POINTS` (terminal.hl:537). -/
theorem DELTA_Y_POS_4POINTS (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) := by
  sorry -- DISCHARGES: Cayley-Menger positivity of a 4-point simplex

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
  sorry -- DISCHARGES: tau3_taum

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
  sorry -- DISCHARGES: tau3_taum

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

/-! ## Section D: taum symmetry and the funlist/periodicity kit
(terminal.hl:684-1211) -/

/-- HOL `taum_sym2` (terminal.hl:684). -/
theorem taum_sym2 (y1 y2 y3 y4 y5 y6 : ℝ) :
    taum y1 y2 y3 y4 y5 y6 = taum y2 y1 y3 y5 y4 y6 ∧
    taum y1 y2 y3 y4 y5 y6 = taum y1 y3 y2 y4 y6 y5 := by
  sorry -- DISCHARGES: taum symmetry (canonical SphereKit body, deduped
  -- from the opaque `taum_p23` stub)

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
  sorry -- DISCHARGES: mechanical unfolding of isScsV39 over the funlist kit

/-- HOL `is_ear_scs3` (terminal.hl:1103). -/
theorem is_ear_scs3 (a b : ℕ → ℕ → ℝ) (jf : ℕ → ℕ → Prop) :
    isEarV39 (ScsV39.mk 3 0.11 a a b b jf (fun _ => False) (fun _ => False)
      (fun _ => False)) ↔
    isScsV39 (ScsV39.mk 3 0.11 a a b b jf (fun _ => False) (fun _ => False)
      (fun _ => False)) ∧ (∀ i, b i i = 0) ∧
    (∃ i, {j | j < 3 ∧ jf j (j + 1)} = {i} ∧ a i (i + 1) = Real.sqrt 8 ∧
      b i (i + 1) = cstab ∧
      (∀ j, j < 3 ∧ j ≠ i → a j (j + 1) = 2 ∧ b j (j + 1) = 2 * h0)) := by
  sorry -- DISCHARGES: isEarV39 unfolding

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
      (funlistV39 b b0 3) (funlistV39 b b0 3) (funlistAV39 jf False j0 3)
      (fun _ => False) (fun _ => False) (fun _ => False)) := by
  sorry -- DISCHARGES: mechanical unfolding of isScsV39 at k = 3

/-- HOL `is_scs_ear_3603097872` (terminal.hl:1186). -/
theorem is_scs_ear_3603097872 :
    isScsV39 (ScsV39.mk 3 0.11
      (funlistV39 [((0, 1), Real.sqrt 8)] 2 3) (funlistV39 [((0, 1), Real.sqrt 8)] 2 3)
      (funlistV39 [((0, 1), cstab)] (2 * h0) 3) (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
      (funlistAV39 [((0, 1), True)] False False 3)
      (fun _ => False) (fun _ => False) (fun _ => False)) := by
  sorry -- DISCHARGES: the concrete 3-ear system's scs certificate

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
  sorry -- DISCHARGES: real wlog over the cyclic rotation of (y1, y2, y3, y4)

/-- HOL `REAL_WLOG_SQUARE2_LEMMA` (terminal.hl:1237). -/
theorem REAL_WLOG_SQUARE2_LEMMA (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hrot : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5 ∧
      P y1 y2 y3 y4 y5 y6 = P y1 y4 y3 y2 y6 y5)
    (hmax : ∀ y1 y2 y3 y4 y5 y6 : ℝ, y2 ≤ y1 → y3 ≤ y1 → y4 ≤ y1 → y4 ≤ y2 →
      P y1 y2 y3 y4 y5 y6) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6 := by
  sorry -- DISCHARGES: real wlog over the two square symmetries

/-! ## Section E: the fan / azim bank (terminal.hl:1254-2230) -/

/-- HOL `EE_vv` (terminal.hl:1254). -/
theorem EE_vv (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    ee (vv i) (Set.range fun i => {vv i, vv (i + 1)}) =
      {vv (i + 1), vv (i + (k - 1))} := by
  sorry -- DISCHARGES: ee-of-cycle-edge characterization

/-- HOL `tau_fun_azim` (terminal.hl:1316). -/
theorem tau_fun_azim (vv : ℕ → V3) (k : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j) :
    tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) =
      setSum {i | i < k}
          (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1)))) -
        (Real.pi + sol0) * (k - 2) := by
  sorry -- DISCHARGES: tau_fun over a periodic fan (sol_local characterization)

/-- HOL `vv_rho_node1` (terminal.hl:1382). -/
theorem vv_rho_node1 (vv : ℕ → V3) (k : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (i : ℕ) :
    rhoNode1 (Set.range fun i => (vv i, vv (i + 1))) (vv i) = vv (i + 1) := by
  sorry -- DISCHARGES: rho_node1 of the cycle dart

/-- HOL `ITER_vv_rho_node1` (terminal.hl:1418). -/
theorem ITER_vv_rho_node1 (vv : ℕ → V3) (k j : ℕ) (hper : Periodic vv k)
    (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (i : ℕ) :
    (rhoNode1 (Set.range fun i => (vv i, vv (i + 1))))^[j] (vv i) = vv (i + j) := by
  sorry -- DISCHARGES: iterates of rho_node1 along the cycle

/-- HOL `PRIOR_TO_LESS_THAN_PI_LEMMA_ALT` (terminal.hl:1440). -/
theorem PRIOR_TO_LESS_THAN_PI_LEMMA_ALT (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (hcf : ConvexLocalFan V E FF) (hv : v ∈ V)
    (w : V3) (hw : w ∈ V) :
    azim 0 v (rhoNode1 FF v) w ≤
      azim 0 v (rhoNode1 FF v)
        (azimCycle_p18 (ee v E) 0 v (rhoNode1 FF v)) := by
  sorry -- DISCHARGES: prior-to-less-than-pi fan lemma

/-- HOL `vv_azim_le` (terminal.hl:1452). -/
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
  sorry -- DISCHARGES: vv_azim_le fan geometry

/-- HOL `vv_split_azim` (terminal.hl:1492). -/
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
  sorry -- DISCHARGES: azim splitting in the fan

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

/-- HOL `IN_V_IMP_AZIM_LESS_PI_ALT` (terminal.hl:1768). -/
theorem IN_V_IMP_AZIM_LESS_PI_ALT (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (hcf : ConvexLocalFan V E FF) (hv : v ∈ V)
    (w : V3) (hw : w ∈ V) :
    azim 0 v (rhoNode1 FF v) w ≤ Real.pi := by
  sorry -- DISCHARGES: fan azim < pi

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

/-- HOL `enclosed_sym` (terminal.hl:1930). -/
theorem enclosed_sym (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 =
      enclosedP38 y1 y6 y5 y4 y3 y2 y7 y9 y8 := by
  sorry -- DISCHARGES: enclosedP38 body (external anchor)

/-- HOL `enclosed_sym2` (terminal.hl:1946). -/
theorem enclosed_sym2 (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 =
      enclosedP38 y7 y8 y9 y4 y2 y3 y1 y5 y6 := by
  sorry -- DISCHARGES: enclosedP38 body (external anchor)

/-- HOL `convex_local_fan_azim_le_pi` (terminal.hl:1962). -/
theorem convex_local_fan_azim_le_pi (vv : ℕ → V3) (k i : ℕ)
    (hper : Periodic vv k) (hk : 3 ≤ k)
    (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
    (hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
    (hsub : Set.range vv ⊆ ballAnnulus) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≤ Real.pi := by
  sorry -- DISCHARGES: fan wedge closure

/-- HOL `vv_quad_split012` (terminal.hl:1996). -/
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
  sorry -- DISCHARGES: quad azim sum splitting

/-- HOL `vv_quad_split123` (terminal.hl:2049). -/
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
  sorry -- DISCHARGES: quad azim sum splitting

/-- HOL `vv_quad_split_short` (terminal.hl:2103). -/
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
  sorry -- DISCHARGES: the short-diagonal quad split

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

/-- HOL `delta_4680581274` (terminal.hl:2179). -/
theorem delta_4680581274 (y1 y4 : ℝ) (hy1 : cstab ≤ y1) (hy4 : 4 ≤ y4) :
    deltaY y1 2 2 y4 2 cstab < 0 := by
  sorry -- DISCHARGES: the 4680581274 delta drop on the 2-2 spine

/-- HOL `tau3_sym` (terminal.hl:2218). -/
theorem tau3_sym (v0 v1 v2 : V3) :
    tau3 v0 v1 v2 = tau3 v0 v2 v1 ∧ tau3 v0 v1 v2 = tau3 v1 v0 v2 := by
  sorry -- DISCHARGES: tau3 symmetry (dih symmetry lemmas)

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

/-- HOL `ineq_5691615370_asym` (terminal.hl:2797). -/
theorem ineq_5691615370_asym (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      ineqP38 [(3.0, y1, 3.0), (2, y2, 2.52), (2, y3, 2.52), (3.0, y4, 3.0),
        (2, y5, 2.52), (2, y6, 2.52)]
        (deltaY y1 y2 y3 y4 y5 y6 < 0 ∨
          y2 + y3 + y5 + y6 > 8.472) := by
  sorry -- DISCHARGES: LEMMA_5691615370 (LP asymmetric variant)

/-- HOL `terminal_quad_lemma` (terminal.hl:2834). -/
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
  sorry -- DISCHARGES: the k = 4 BB-minimality transfer (tau_fun side)

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

/-- HOL `LEMMA_4680581274_delta_issue_ups` (terminal.hl:3604). -/
theorem LEMMA_4680581274_delta_issue_ups (x1 x2 x3 x4 x5 x6 : ℝ) :
    ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26),
      (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26), (3.01 * 3.01, x4, 3.166 * 3.166),
      (4.0, x5, 4.0), (4.0, x6, 4.0)]
      (0 < upsX x2 x3 x4 ∨
        10 + deltaX x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
        deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0) := by
  sorry -- DISCHARGES: the 4680581274 ups escape (LP)

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

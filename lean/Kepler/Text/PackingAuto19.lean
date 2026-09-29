/-
Packing chapter, cluster annulus inequalities (S19 stage): the
`UPFZBZM` + `RDWKARC` lane.

HOL sources (chapter Packing, VU KHAC KY):
- `scripts/packing/UPFZBZM_support_lemmas.hl` (374 lines): the support kit of
  UPFZBZM — Flyspeck-constants positivity (`tau0_not_zero`,
  `ZERO_LT_MM2_LEMMA`), the sqrt calculus (`SQRT_RULE_Euler_lemma`,
  `SQRT_OF_32_lemma`), the bookkeeping identity `m1_minus_12m2`
  (`mm1 - 12 * mm2 = sqrt(1/2)`, the exact `sqrt 32` density gap), finiteness
  of the cell-edge families (`FINITE_edgeX`, `FINITE_critical_edgeX`),
  dihedral sign/symmetry (`DIHV_LE_0`, `DIHV_SYM`, `DIHX_POS`), elementary
  sums (`SUM_SET_OF_2_ELEMENTS`) and the `negligible_fun_0` C-form
  (`pos_lemma`, `negligible_fun_any_C`). Tactic glue (`CHANGED_SET_TAC`,
  `john_harrison_lemma1/2`) is subsumed by Lean's lambda/choice machinery and
  not ported; `FINITE_PERMUTE_3/4` and `DIHV_SYM` are already on the Lean side
  (PackingAuto12, marchal2 lane) and imported from there.
- `scripts/packing/UPFZBZM.hl` (238 lines): parts 1-2 of book lemma UPFZBZM
  (`FCC_COMPATABILITY_FUNC`, `NEGLIGIBLE_FUNC`) and the capstone `UPFZBZM`
  (existence of an `fcc_compatible` + `negligible_fun_0` functional from the
  cluster/density hypothesis bundle).
- `scripts/packing/RDWKARC.hl` (318 lines): book lemma RDWKARC — the density
  bound `JGXZYGW_KY` (point-0 specialization of pack1.hl JGXZYGW), packing /
  saturation translation lemmas (`PACKING_SUBSET`, `PACKING_TRANS`,
  `SATURATED_TRANS`, `RADV_TRANS_EQ`) and the capstone `RDWKARC`: if the
  Kepler density bound fails, some packing in the ball annulus violates the
  local annulus inequality.

## File map

1. Support kit (UPFZBZM_support_lemmas.hl).
2. `SUM_GAMMAX_LMFUN_ESTIMATE_p19` (sum_gamma.hl:53-57 — parallel-owned
   PackingAuto18, NOT importable here: `_p19` copy + NEEDS).
3. UPFZBZM.hl: `FCC_COMPATABILITY_FUNC` (proved), `NEGLIGIBLE_FUNC`
   (proved 2026-09-29 from the PA15/PA16/PA18 inputs below), `UPFZBZM`
   (proved from parts 1-2).
4. RDWKARC.hl: `JGXZYGW_p19` copy + `JGXZYGW_KY` (proved),
   `PACKING_SUBSET`/`PACKING_TRANS`/`SATURATED_TRANS`/`RADV_TRANS_EQ`
   (proved), `RDWKARC` (GIANT, sorried).

## DISCHARGES convention

- `UPFZBZM` matches the `pack_concl` interface verbatim: DISCHARGES
  PackingAuto2.UPFZBZM_concl (PackingAuto2.lean:850).
- `RDWKARC` matches the interface verbatim: DISCHARGES
  PackingAuto2.RDWKARC_concl (PackingAuto2.lean:856).
- `GOTCJAH` (fan solid-angle bound, pack_concl.hl:251) belongs to the
  polyhedron/fan lane and has no source in this lane's three files; NOT
  restated here.
- Import policy: PackingAuto2 + PackingAuto12 + PackingAuto15 + PackingAuto16 +
  PackingAuto18 (2026-09-29: the PA15/PA16 oleans have landed, so the
  `NEGLIGIBLE_FUNC` fill-in below imports `KIZHLTL1/2/4` (PA16) and
  `FINITE_MCELL_SET_LEMMA` (PA15) directly; PA18 was already imported
  2026-09-19 for the SUM_GAMMAX shim). `DIHX_POS` is still proved directly
  from the `dihX` case split via `DIHV_LE_0` (no PA15 dependency). No import
  cycle: PA15 ← PA2, 5-8, 10-13; PA16 ← PA2, 12; PA19 is consumed only by
  PackingConcl.

## NEEDS (giant fill-in markers)

- `NEGLIGIBLE_FUNC`: PROVED (2026-09-29, architecture fill). It consumes the
  four upstream inputs — KIZHLTL1 / KIZHLTL2 / KIZHLTL4 (PackingAuto16, still
  `sorry`ed there), SUM_GAMMAX_LMFUN_ESTIMATE (shimmed to PackingAuto18, still
  `sorry`ed there) and FINITE_MCELL_SET_LEMMA (PackingAuto15, still `sorry`ed
  there) for the `T1 + T2 + T3 = sum B (gammaX V X lmfun)` regrouping, plus
  the PROVED `Kepler.Statement.Packing.finite_inter_ball` for the sums over
  `V ∩ ball 0 r`. The KIZHLTL1 `voronoiOpenP16` → `voronoiOpenP19` bridge and
  the `gammaX`/`KIZHLTL4` epsilon-guard alignment are handled inside the
  fill-in (`p19_epsilon_pair`/`p19_inner_guard_congr` + a definitional
  ascription of the KIZHLTL1 hypothesis); no MEASURE_VORONOI_CLOSED_OPEN
  step is needed on the Lean side. The upstream four remain the chain's
  open giants (Wave 2/3 lanes).
- `SUM_GAMMAX_LMFUN_ESTIMATE_p19`: SHIMMED (2026-09-19) to
  `PackingAuto18.SUM_GAMMAX_LMFUN_ESTIMATE` (import added; upstream sorry
  remains in Auto18).
- `JGXZYGW_p19`: NEEDS PackingAuto1.JGXZYGW (pack1.hl:519; PA1's ported
  statement uses a different (`Space3`/private-`fcc_compatible`) encoding, so
  the `_p19` copy stays; the HL proof runs through measure_ineq_lm53_2 /
  ineq_lm5_3_step3/4, not on the Lean side).
- `tau0_gt_p19` / `mm2_gt_p19`: PROVED (2026-09-19) from Mathlib's certified
  π-interval + an in-file 9th-order Taylor bracket of `sin` pinning
  `arcsin(1/3)` — no `Flyspeck_constants` dependency remains.

## Encoding notes

- HOL `real^3` ↔ `V3` (Kepler.Geom); `packing` ↔ `Packing`
  (Kepler.Statement); `saturated`, `voronoi_closed`/`voronoi_open`, `VX`,
  `edgeX`, `critical_edgeX` ↔ `criticalEdgeX`, `dihX`, `dihV`, `gammaX`,
  `lmfun`, `h0`, `mm1`, `mm2`, `tau0`, `sol0`, `hl`, `cell_params` ↔
  `cellParams`, `cell_cluster_inequality` ↔ `cellClusterInequality`,
  `lmfun_inequality` ↔ `lmfunInequality`, `negligible_fun_p/0` ↔
  `negligibleFunP/negligibleFun0`, `fcc_compatible` ↔ `fccCompatible`,
  `kepler_conjecture` ↔ `keplerConjecture`, `ball_annulus` ↔ `ballAnnulus`,
  `local_annulus_inequality` ↔ `localAnnulusInequality`,
  `TSKAJXY_statement` (a `new_definition` of a proposition) are the
  PackingAuto2 definitions.
- HOL `sum S f` ↔ `setSum` (junk 0 on infinite sets); `vol`/`measure` ↔
  `volume.real`; `ball (vec 0, r)` (open) ↔ `Metric.ball 0 r`; `CARD` ↔
  `Nat.card`; `&x pow 2` ↔ `x ^ 2`.
- `voronoiOpenP19` is a `_p19` copy of HOL `voronoi_open`
  (sphere.hl:304; PackingAuto2's `voronoiOpen` and PackingAuto16's
  `voronoiOpenP16` have identical bodies but are private to their files):
  delete the copies at merge in favor of one public definition. Note the Lean
  `fccCompatible` is stated with `voronoiOpen` (HOL `fcc_compatible` uses
  `voronoi_closed`), so part 1 of UPFZBZM needs no
  MEASURE_VORONOI_CLOSED_OPEN step: the volume terms cancel verbatim.
- `UPFZBZM`'s existential witness is the functional `G` of parts 1-2; the
  capstone is a 2-line assembly of `FCC_COMPATABILITY_FUNC` and
  `NEGLIGIBLE_FUNC` (in HL: `ASM_MESON_TAC` over the two parts).
- `RDWKARC`'s proof shape (for the fill-in harness): unfold
  `keplerConjecture`, move the failure to `¬∃c`, derive `¬lmfunInequality V`
  from UPFZBZM + JGXZYGW_KY (contradiction), pick `u` with edge sum > 12,
  translate by `-u` (`PACKING_TRANS`, `SATURATED_TRANS`), intersect with the
  annulus (`PACKING_SUBSET`), and re-index the annulus sum
  `lmfun (hl [0, v])` to the `V`-sum via `hl` translation invariance
  (`RADV_TRANS_EQ`, `hl [0, v] = hl [-u, v - u]`).

Proof status (2026-09-29): the mechanical support chain, both UPFZBZM parts
(`FCC_COMPATABILITY_FUNC` and `NEGLIGIBLE_FUNC` — the latter filled in
2026-09-29 as the setSum-regrouping architecture consuming KIZHLTL1/2/4,
SUM_GAMMAX_LMFUN_ESTIMATE and FINITE_MCELL_SET_LEMMA from the PA15/16/18
oleans), the capstone `UPFZBZM`, `JGXZYGW_KY`, the four RDWKARC translation
lemmas and the two numerical Flyspeck-constants bounds (`tau0_gt_p19`,
`mm2_gt_p19`, proved from Mathlib π-bounds + a certified Taylor bracket of
`sin`) are proved here; `RDWKARC` and `JGXZYGW_p19` remain the only sorried
giants in this file; `SUM_GAMMAX_LMFUN_ESTIMATE_p19` is a documented shim to
PackingAuto18's (still-sorried-upstream) capstone.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto16
import Kepler.Text.PackingAuto18
import Kepler.Text.PackingJGXZYGW
import Mathlib

set_option maxHeartbeats 5000000

noncomputable section

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Support kit (UPFZBZM_support_lemmas.hl) -/

/-! ### Certified numerics for `tau0`/`mm2` (2026-09-19 fill)

`Flyspeck_constants.bounds` (`#1.54065 < tau0`, `#0.02541 < mm2`) is proved
from first principles: Mathlib's rational π-interval
(`pi_gt_d6`/`pi_lt_d6`, error `10⁻⁶`) plus an alternating-series Taylor
bracket of `sin` derived to order 9 (each step by a derivative-sign
monotonicity argument on `[0, ∞)`, bootstrapped from Mathlib's
`Real.sin_ge_sub_cube`). The bracket pins `arcsin(1/3)` to
`0.3398369 < arcsin(1/3) < 0.3398370` (error `10⁻⁷`), which determines
`sol0 = π/2 − 3·arcsin(1/3)`, `tau0 = 60·arcsin(1/3) − 6π` and
`mm2 = (6·sol0 − π)·√2/(6·tau0)` with ample slack for the two Flyspeck
bounds. All final comparisons are exact rational `norm_num` checks. -/

private theorem p19_mono {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f)
    (hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ deriv f x) : MonotoneOn f (Set.Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
    (fun x hx => hd x (by
      have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      exact hlt.le))

private theorem p19_antitone {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f)
    (hd : ∀ x : ℝ, 0 ≤ x → deriv f x ≤ 0) : AntitoneOn f (Set.Ici 0) :=
  antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
    (fun x hx => hd x (by
      have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      exact hlt.le))

private theorem p19_cos_le_taylor4 {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  have hC : Continuous (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) := by
    fun_prop
  have step := p19_antitone (f := fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) x
            = -Real.sin x + x - x ^ 3 / 6 := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := Real.sin_ge_sub_cube hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem p19_sin_le_taylor5 {t : ℝ} (ht : 0 ≤ t) :
    Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 := by
  have hC : Continuous (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) := by
    fun_prop
  have step := p19_antitone (f := fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) x
            = Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := p19_cos_le_taylor4 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem p19_cos_ge_taylor6 {t : ℝ} (ht : 0 ≤ t) :
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
  have hC : Continuous (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) := by fun_prop
  have step := p19_mono (f := fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.cos s -
            (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) x
            = -Real.sin x + x - x ^ 3 / 6 + x ^ 5 / 120 := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := p19_sin_le_taylor5 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem p19_sin_ge_taylor7 {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 ≤ Real.sin t := by
  have hC : Continuous (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) := by fun_prop
  have step := p19_mono (f := fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.sin s -
            (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) x
            = Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := p19_cos_ge_taylor6 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem p19_cos_le_taylor8 {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 := by
  have hC : Continuous (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) := by fun_prop
  have step := p19_antitone (f := fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.cos s -
            (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) x
            = -Real.sin x + x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := p19_sin_ge_taylor7 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.cos s -
      (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720 + s ^ 8 / 40320)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem p19_sin_le_taylor9 {t : ℝ} (ht : 0 ≤ t) :
    Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 := by
  have hC : Continuous (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) := by fun_prop
  have hD : Differentiable ℝ (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) := by
    fun_prop
  have step := p19_antitone (f := fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) hC hD
    (by intro x hx
        have hderiv : deriv (fun s : ℝ => Real.sin s -
            (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) x
            = Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) := by
          simp (disch := fun_prop); ring
        rw [hderiv]
        have := p19_cos_le_taylor8 hx
        linarith)
  have step2 := step (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hz : (fun s : ℝ => Real.sin s -
      (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040 + s ^ 9 / 362880)) 0 = 0 := by simp
  rw [hz] at step2
  linarith

private theorem p19_arcsin_bounds :
    (0.3398369 : ℝ) < Real.arcsin (1 / 3) ∧ Real.arcsin (1 / 3) < 0.3398370 := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  set a := Real.arcsin (1 / 3) with hdef
  have hamem : a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have ht1mem : (0.3398369 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have ht2mem : (0.3398370 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hsa : Real.sin a = 1 / 3 := Real.sin_arcsin (by norm_num) (by norm_num)
  have h9 := p19_sin_le_taylor9 (t := 0.3398369) (by norm_num)
  have hlt : Real.sin 0.3398369 < Real.sin a := by
    rw [hsa]
    have hr : 0.3398369 - 0.3398369 ^ 3 / 6 + 0.3398369 ^ 5 / 120
        - 0.3398369 ^ 7 / 5040 + 0.3398369 ^ 9 / 362880 < (1 : ℝ) / 3 := by norm_num
    linarith
  have h7 := p19_sin_ge_taylor7 (t := 0.3398370) (by norm_num)
  have hgt : Real.sin a < Real.sin 0.3398370 := by
    rw [hsa]
    have hr : (1 : ℝ) / 3 < 0.3398370 - 0.3398370 ^ 3 / 6 + 0.3398370 ^ 5 / 120
        - 0.3398370 ^ 7 / 5040 := by norm_num
    linarith
  exact ⟨(Real.strictMonoOn_sin.lt_iff_lt ht1mem hamem).mp hlt,
    (Real.strictMonoOn_sin.lt_iff_lt hamem ht2mem).mp hgt⟩

/-- The regular-tetrahedron solid angle in `arcsin` form:
`sol0 = π/2 − 3·arcsin(1/3)` (via `Real.arccos_eq_pi_div_two_sub_arcsin`). -/
private theorem p19_sol0_eq : sol0 = Real.pi / 2 - 3 * Real.arcsin (1 / 3) := by
  have h : Real.arccos (1 / 3) = Real.pi / 2 - Real.arcsin (1 / 3) :=
    Real.arccos_eq_pi_div_two_sub_arcsin _
  show 3 * Real.arccos (1 / 3) - Real.pi = _
  rw [h]; ring

/-- Flyspeck-constants bound `#1.54065 < tau0` (UPFZBZM_support_lemmas.hl:93),
PROVED here (2026-09-19 pass): Mathlib's certified π-interval
(`Real.pi_gt_d6`/`Real.pi_lt_d6`) + a rigorous 9th-order Taylor bracket of
`sin` (private `p19_sin_le_taylor9`/`p19_sin_ge_taylor7` above) pin
`arcsin(1/3)` between `0.3398369` and `0.3398370`; `tau0 = 60·arcsin(1/3) − 6π`
(unfolded via `Real.arccos_eq_pi_div_two_sub_arcsin`) then gives the bound
with slack `6·10⁻⁶`. No `Flyspeck_constants` dependency remains. -/
private theorem tau0_gt_p19 : 1.54065 < tau0 := by
  obtain ⟨hlow, _⟩ := p19_arcsin_bounds
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsol := p19_sol0_eq
  show (1.54065 : ℝ) < 4 * Real.pi - 20 * sol0
  rw [hsol]
  linarith

/-- Flyspeck-constants bound `#0.02541 < mm2` (UPFZBZM_support_lemmas.hl:101),
PROVED here (2026-09-19 pass) on the same `arcsin(1/3)` bracket
(`p19_arcsin_bounds`): `6·sol0 − π = 2π − 18·arcsin(1/3) > 0.166118`,
`tau0 ≤ 1.540668`, `√2 > 1.414213` (exact rational square check), and
`0.02541 · 9.244008 < 0.166118 · 1.414213` (exact) chain to the bound
with slack `3.5·10⁻⁶`. -/
private theorem mm2_gt_p19 : 0.02541 < mm2 := by
  obtain ⟨hlow, hupp⟩ := p19_arcsin_bounds
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hsol := p19_sol0_eq
  have hN : (0.166118 : ℝ) < 6 * sol0 - Real.pi := by rw [hsol]; linarith
  have htauub : tau0 ≤ 1.540668 := by
    have h6 : tau0 = 60 * Real.arcsin (1 / 3) - 6 * Real.pi := by
      show 4 * Real.pi - 20 * sol0 = _
      rw [hsol]; ring
    linarith
  have hs2 : (1.414213 : ℝ) < Real.sqrt 2 := by
    have hsq : (1.414213 : ℝ) ^ 2 < 2 := by norm_num
    exact Real.lt_sqrt_of_sq_lt hsq
  have h6t : (6 : ℝ) * tau0 ≤ 9.244008 := by linarith
  have key : (0.02541 : ℝ) * (6 * tau0) < (6 * sol0 - Real.pi) * Real.sqrt 2 := by
    have hle : (0.166118 : ℝ) ≤ 6 * sol0 - Real.pi := by linarith
    have hprod : (0.166118 : ℝ) * 1.414213 < (6 * sol0 - Real.pi) * Real.sqrt 2 :=
      mul_lt_mul_of_le_of_lt_of_pos_of_nonneg hle hs2 (by norm_num)
        (Real.sqrt_nonneg 2)
    have step1 : (0.02541 : ℝ) * (6 * tau0) ≤ 0.02541 * 9.244008 :=
      mul_le_mul_of_nonneg_left h6t (by norm_num)
    calc (0.02541 : ℝ) * (6 * tau0) ≤ 0.02541 * 9.244008 := step1
      _ < 0.166118 * 1.414213 := by norm_num
      _ < (6 * sol0 - Real.pi) * Real.sqrt 2 := hprod
  have hmm : mm2 = (6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0) := rfl
  rw [hmm, lt_div_iff₀ (c := 6 * tau0) (by
    have htau0pos : (0 : ℝ) < tau0 :=
      lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 1.54065) tau0_gt_p19
    linarith)]
  exact key

/-- HOL `tau0_not_zero` (UPFZBZM_support_lemmas.hl:91). -/
theorem tau0_not_zero : tau0 ≠ 0 := by
  have h : (0 : ℝ) < tau0 := lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 1.54065) tau0_gt_p19
  exact ne_of_gt h

/-- HOL `ZERO_LT_MM2_LEMMA` (UPFZBZM_support_lemmas.hl:100). -/
theorem ZERO_LT_MM2_LEMMA : (0 : ℝ) < mm2 := by
  have := mm2_gt_p19
  linarith

/-- HOL `ZERO_LE_MM2_LEMMA` (UPFZBZM_support_lemmas.hl:194). -/
theorem ZERO_LE_MM2_LEMMA : 0 ≤ mm2 := le_of_lt ZERO_LT_MM2_LEMMA

/-- HOL `SQRT_RULE_Euler_lemma` (UPFZBZM_support_lemmas.hl:127): a
nonnegative square root of `y`. -/
theorem SQRT_RULE_Euler_lemma (x y : ℝ) (h2 : x ^ 2 = y) (h0 : 0 ≤ x) :
    x = Real.sqrt y := by
  rw [← Real.sqrt_sq h0, h2]

/-- HOL `SQRT_OF_32_lemma` (UPFZBZM_support_lemmas.hl:134). -/
theorem SQRT_OF_32_lemma : Real.sqrt 32 = 8 * Real.sqrt (1 / 2) := by
  have h64 : (64 : ℝ) = (8 : ℝ) ^ 2 := by norm_num
  have h8 : (8 : ℝ) = Real.sqrt 64 := by
    rw [h64]
    exact (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)).symm
  have h32 : (32 : ℝ) = 64 * (1 / 2) := by norm_num
  calc Real.sqrt 32 = Real.sqrt (64 * (1 / 2)) := by rw [h32]
    _ = Real.sqrt 64 * Real.sqrt (1 / 2) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64) (1 / 2)
    _ = 8 * Real.sqrt (1 / 2) := by rw [h8]

/-- HOL `m1_minus_12m2` (UPFZBZM_support_lemmas.hl:147): the density gap
identity `mm1 - 12 * mm2 = sqrt(1/2)`; combined with `SQRT_OF_32_lemma` this
is exactly `sqrt 32 = 8 * (mm1 - 12 * mm2)`. -/
theorem m1_minus_12m2 : mm1 - 12 * mm2 = Real.sqrt (1 / 2) := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
    calc Real.sqrt 8 = Real.sqrt (4 * 2) := by rw [show (8 : ℝ) = 4 * 2 from by norm_num]
      _ = Real.sqrt 4 * Real.sqrt 2 := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) 2
      _ = 2 * Real.sqrt 2 := by rw [h4]
  have hin : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) 2, Real.sqrt_one]
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnz : Real.sqrt 2 ≠ 0 := by
      rintro h
      rw [h] at hsq
      norm_num at hsq
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hne : tau0 ≠ 0 := tau0_not_zero
  have htau : tau0 = 4 * (Real.pi - 5 * sol0) := by
    unfold tau0 sol0
    ring
  have hD : Real.pi - 5 * sol0 ≠ 0 := by
    intro h0
    apply hne
    rw [htau, h0]
    ring
  have h4D : (4 : ℝ) * (Real.pi - 5 * sol0) ≠ 0 := mul_ne_zero (by norm_num) hD
  have h24D : (24 : ℝ) * (Real.pi - 5 * sol0) ≠ 0 := mul_ne_zero (by norm_num) hD
  have key : mm1 - 12 * mm2 = Real.sqrt 2 / 2 := by
    unfold mm1 mm2
    rw [h8, htau]
    apply mul_right_cancel₀ (b := 24 * (Real.pi - 5 * sol0)) h24D
    field_simp [hD, h4D]
    apply mul_right_cancel₀ hD
    field_simp
    ring
  rw [key, hin]

/-- The set of list members is finite (used by `FINITE_edgeX` for
`VX V X = set_of_list (...)`). -/
private theorem setOfList_finite {α : Type*} (ul : List α) :
    ({x | x ∈ ul} : Set α).Finite :=
  Set.Finite.ofFinset ul.toFinset (by simp)

/-- HOL `FINITE_edgeX` (UPFZBZM_support_lemmas.hl:200): the cell-edge family
is finite, unconditionally (`VX V X` is a list-image by construction). -/
theorem FINITE_edgeX (V X : Set V3) : (edgeX V X).Finite := by
  have hvx : (VX V X).Finite := by
    by_cases h : nullSet X
    · rw [VX, if_pos h]
      exact Set.finite_empty
    · by_cases h0 : (cellParams V X).1 = 0
      · rw [VX, if_neg h, if_pos h0]
        exact Set.finite_empty
      · rw [VX, if_neg h, if_neg h0]
        exact setOfList_finite _
  refine Set.Finite.subset (Set.Finite.image (fun p : V3 × V3 => {p.1, p.2})
    (hvx.prod hvx)) ?_
  rintro e ⟨u, v, rfl, hu, hv, -⟩
  exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩

/-- HOL `FINITE_critical_edgeX` (UPFZBZM_support_lemmas.hl:229). -/
theorem FINITE_critical_edgeX (V X : Set V3) : (criticalEdgeX V X).Finite :=
  Set.Finite.subset (FINITE_edgeX V X) (by
    rintro e ⟨u, v, rfl, he, -, -⟩
    exact he)

/-- HOL `DIHV_LE_0` (UPFZBZM_support_lemmas.hl:244): `dihV` is an arccos,
hence nonnegative. -/
theorem DIHV_LE_0 (x y z t : V3) : 0 ≤ dihV x y z t := by
  simp only [dihV, Kepler.Geom.arcV]
  exact Real.arccos_nonneg _

/-- HOL `DIHV_SYM` (UPFZBZM_support_lemmas.hl:256, marchal2.hl:194): the
PackingAuto12 port (imported; no restatement of the proof). -/
theorem DIHV_SYM_p19 (x y z t : V3) : dihV x y z t = dihV y x z t :=
  DIHV_SYM x y z t

/-- HOL `DIHX_POS` (UPFZBZM_support_lemmas.hl:317): nonnegativity of the
cell dihedral across an oriented edge (marchal3 `DIHX_RANGE`'s lower half;
proved here directly from the `dihX` case split — no Auto15 dependency). -/
theorem DIHX_POS (u v : V3) (V X : Set V3) : 0 ≤ dihX V X (u, v) := by
  simp only [dihX]
  split_ifs with h h2 h3 h4
  · exact le_refl 0
  · exact DIHV_LE_0 _ _ _ _
  · exact DIHV_LE_0 _ _ _ _
  · exact DIHV_LE_0 _ _ _ _
  · exact le_refl 0

/-- HOL `SUM_SET_OF_2_ELEMENTS` (UPFZBZM_support_lemmas.hl:334). -/
theorem SUM_SET_OF_2_ELEMENTS {s t : V3} (h : s ≠ t) (f : V3 → ℝ) :
    setSum {s, t} f = f s + f t := by
  classical
  have hfin : ({s, t} : Set V3).Finite := Set.Finite.insert s (Set.finite_singleton t)
  rw [setSum, dif_pos hfin, Set.Finite.toFinset_insert' (hs := Set.finite_singleton t),
    Set.Finite.toFinset_singleton, Finset.sum_insert (by simp [h]),
    Finset.sum_singleton]

/-- HOL `pos_lemma` (UPFZBZM_support_lemmas.hl:345): a nonnegativity
constraint on the quadratic-growth constant is removable. -/
theorem pos_lemma (Q : ℝ → ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → Q r ≤ C * r ^ 2) ↔
      ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → Q r ≤ C * r ^ 2 := by
  constructor
  · rintro ⟨C, -, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨|C|, abs_nonneg C, fun r hr => ?_⟩
    calc Q r ≤ C * r ^ 2 := hC r hr
      _ ≤ |C| * r ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg r)

/-- HOL `negligible_fun_any_C` (UPFZBZM_support_lemmas.hl:366): the
`negligible_fun_0` definition with the C-nonnegativity stripped
(`pos_lemma` applied to `negligible_fun_p`). -/
theorem negligible_fun_any_C (f : V3 → ℝ) (S : Set V3) :
    negligibleFun0 f S ↔ ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      setSum (S ∩ Metric.ball 0 r) f ≤ C * r ^ 2 := by
  unfold negligibleFun0 negligibleFunP
  exact pos_lemma _

/-! ## sum_gamma.hl: SUM_GAMMAX_LMFUN_ESTIMATE (parallel-owned Auto18) -/

/-- GIANT — HOL `SUM_GAMMAX_LMFUN_ESTIMATE` (sum_gamma.hl:53-62): the
cell-cluster inequality (plus TSKAJXY) forces a quadratic lower bound on the
total `gammaX` deficit of the Marchal cells inside `ball 0 r`. The HL proof
(in sum_gamma.hl, module `Sum_gammax_lmfun_estimate`) picks uniform constants
cc1 (BOUND_GAMMA_X_lmfun), cc2 (CARD_MCELL_CONTAINS_POINT_klemma), cc3
(beta-bump bound) and re-groups the cluster sums over the finite cell family.

NEEDS: the leaf_cell / sum_gamma kit — SHIM (2026-09-19): the parallel
PackingAuto18 olean HAS landed in this checkout, so the `_p19` copy now
discharges to `Kepler.Text.PackingAuto18.SUM_GAMMAX_LMFUN_ESTIMATE`
(statement-identical; that theorem is still `sorry`ed upstream in Auto18 —
the giant leaf-cell/sum_gamma chains carry `sorry` there — so this is a
documented transitive-shim fill, deleting the statement duplication). -/
theorem SUM_GAMMAX_LMFUN_ESTIMATE_p19 (V : Set V3) :
    ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V → 1 ≤ r →
      cellClusterInequality V → TSKAJXY_statement →
      c * r ^ 2 ≤ setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
        (fun X => gammaX V X lmfun) :=
  SUM_GAMMAX_LMFUN_ESTIMATE V

/-! ## UPFZBZM.hl -/

/-- HOL `voronoi_open` (sphere.hl:304; pack1.hl:153). `_p19` copy:
PackingAuto2's `voronoiOpen` and PackingAuto16's `voronoiOpenP16` have
identical bodies but are private to their files — keep one public copy at
merge. -/
private def voronoiOpenP19 (V : Set V3) (v : V3) : Set V3 :=
  {x | ∀ w ∈ V, w ≠ v → dist x v < dist x w}

/-- Delta bridge: `fccCompatible` (whose body mentions PackingAuto2's
private `voronoi_open`) transfers along any functional-equality verbatim; the
private constant and the `_p19` copy are definitionally equal (identical
bodies), so a single `exact` closes the transfer. -/
private theorem p19_fcc_congr (V : Set V3) (G : V3 → ℝ)
    (h : ∀ v ∈ V, Real.sqrt 32 ≤ volume.real (voronoiOpenP19 V v) + G v) :
    fccCompatible G V := h

/-- HOL `FCC_COMPATABILITY_FUNC` (UPFZBZM.hl:58-105, part 1 of UPFZBZM):
the explicit functional `G = -vol(voronoi_open) + 8 mm1 - 8 mm2 * (edge
lmfun-sum)` is `fcc_compatible`. Core: `vol(voronoi_open) + G v = 8 mm1 -
8 mm2 * (edge sum)` and `edge sum ≤ 12` (`lmfunInequality`) give
`sqrt 32 = 8 * (mm1 - 12 * mm2) ≤ 8 mm1 - 8 mm2 * (edge sum)`.

DISCHARGES: none (internal part of UPFZBZM; feeds the capstone). -/
theorem FCC_COMPATABILITY_FUNC (V : Set V3) (hs : saturated V) (hp : Packing V)
    (hcc : cellClusterInequality V) (_hT : TSKAJXY_statement)
    (hlm : lmfunInequality V) (G : V3 → ℝ)
    (hG : G = fun u => -volume.real (voronoiOpenP19 V u) + 8 * mm1 -
      8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        (fun v => lmfun (hl [u, v]))) : fccCompatible G V := by
  subst hG
  refine p19_fcc_congr V _ ?_
  intro v hv
  show Real.sqrt 32 ≤ volume.real (voronoiOpenP19 V v) +
    (-volume.real (voronoiOpenP19 V v) + 8 * mm1 -
      8 * mm2 * setSum {w | w ∈ V ∧ w ≠ v ∧ dist v w ≤ 2 * h0}
        (fun w => lmfun (hl [v, w])))
  obtain ⟨S, hSdef, hsum⟩ : ∃ S : ℝ,
      S = setSum {w | w ∈ V ∧ w ≠ v ∧ dist v w ≤ 2 * h0}
        (fun w => lmfun (hl [v, w])) ∧ S ≤ 12 :=
    ⟨_, rfl, hlm v hv⟩
  rw [← hSdef]
  have h8 : 8 * mm2 * S ≤ 96 * mm2 := by
    have h10 : (8 : ℝ) * mm2 * S ≤ 8 * mm2 * 12 :=
      mul_le_mul_of_nonneg_left hsum (by linarith [ZERO_LE_MM2_LEMMA])
    have h12 : (8 : ℝ) * mm2 * 12 = 96 * mm2 := by ring
    linarith
  have key : Real.sqrt 32 = 8 * mm1 - 96 * mm2 := by
    rw [SQRT_OF_32_lemma, ← m1_minus_12m2]
    ring
  calc Real.sqrt 32 = 8 * mm1 - 96 * mm2 := key
    _ ≤ 8 * mm1 - 8 * mm2 * S := by linarith
    _ = volume.real (voronoiOpenP19 V v) +
        (-volume.real (voronoiOpenP19 V v) + 8 * mm1 - 8 * mm2 * S) := by ring

/-! ### setSum rearrangement kit for the `NEGLIGIBLE_FUNC` body

UPFZBZM.hl:113-220 runs the whole part-2 argument as `SUM_ADD`/`SUM_SUB`/
`SUM_NEG`/`SUM_CONST`/`SUM_LMUL` re-indexings of HOL `sum` over the finite
families `V ∩ ball (vec 0, r)` and `B = {X | X ⊆ ball (vec 0, r) ∧ mcell_set
V X}`. The Lean `setSum` (junk 0 on infinite sets) supports the same
algebra; `_p19`-private to avoid clashing with the parallel lanes
(cf. PackingAuto2's private `setSumCongr_p2`). -/

/-- Pointwise congruence of the summand (same junk-0 convention on both
sides; pattern of PackingAuto2's private `setSumCongr_p2`). -/
private theorem p19_setSumCongr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : setSum s f = setSum s g := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs]
    exact Finset.sum_congr rfl fun a ha => h a (hs.mem_toFinset.mp ha)
  · unfold setSum
    rw [dif_neg hs, dif_neg hs]

/-- HOL `SUM_ADD` in `setSum` form. -/
private theorem p19_setSum_add {α : Type*} {s : Set α} (f g : α → ℝ) :
    setSum s (fun a => f a + g a) = setSum s f + setSum s g := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs, dif_pos hs]
    exact Finset.sum_add_distrib
  · unfold setSum
    rw [dif_neg hs, dif_neg hs, dif_neg hs]
    simp

/-- HOL `SUM_SUB` in `setSum` form. -/
private theorem p19_setSum_sub {α : Type*} {s : Set α} (f g : α → ℝ) :
    setSum s (fun a => f a - g a) = setSum s f - setSum s g := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs, dif_pos hs, Finset.sum_sub_distrib]
  · unfold setSum
    rw [dif_neg hs, dif_neg hs, dif_neg hs]
    simp

/-- HOL `SUM_NEG` in `setSum` form. -/
private theorem p19_setSum_neg {α : Type*} {s : Set α} (f : α → ℝ) :
    setSum s (fun a => -f a) = -setSum s f := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs, Finset.sum_neg_distrib]
  · unfold setSum
    rw [dif_neg hs, dif_neg hs]
    simp

/-- HOL `SUM_LMUL` in `setSum` form. -/
private theorem p19_setSum_smul {α : Type*} {s : Set α} (c : ℝ) (f : α → ℝ) :
    setSum s (fun a => c * f a) = c * setSum s f := by
  by_cases hs : Set.Finite s
  · unfold setSum
    rw [dif_pos hs, dif_pos hs]
    exact (Finset.mul_sum _ _ _).symm
  · unfold setSum
    rw [dif_neg hs, dif_neg hs]
    simp

/-- HOL `SUM_CONST` in `setSum` form, folded into the `Nat.card` shape of
`KIZHLTL2` (finiteness consumed from `Statement.Packing.finite_inter_ball`). -/
private theorem p19_setSum_const {α : Type*} {s : Set α} (hs : s.Finite) (c : ℝ) :
    setSum s (fun _ => c) = (Nat.card s : ℝ) * c := by
  unfold setSum
  rw [dif_pos hs, Finset.sum_const, nsmul_eq_mul]
  simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

/-- The `T1 + T2 + T3 = Σ_B gammaX` regrouping core over the finite cell
family `B` (finiteness is consumed exactly where the HL proof consumes
`FINITE_MCELL_SET_LEMMA`, PackingAuto15). -/
private theorem p19_setSum_split3 {s : Set (Set V3)} (hf : s.Finite)
    (volF tsF inG : Set V3 → ℝ) (a b : ℝ) :
    setSum s volF - a * setSum s tsF + b * setSum s inG
      = setSum s (fun X => volF X - a * tsF X + b * inG X) := by
  unfold setSum
  rw [dif_pos hf, dif_pos hf, dif_pos hf, dif_pos hf,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ x ∈ hf.toFinset, a * tsF x = a * ∑ x ∈ hf.toFinset, tsF x :=
    (Finset.mul_sum _ _ _).symm
  have e2 : ∑ x ∈ hf.toFinset, b * inG x = b * ∑ x ∈ hf.toFinset, inG x :=
    (Finset.mul_sum _ _ _).symm
  rw [e1, e2]

/-- The epsilon-fixed pair representation of an edge: if `e` is a two-point
set `{u, v}` then `Classical.epsilon` returns a pair whose unordered pair is
`e` (used to align the `gammaX` and `KIZHLTL4` guard encodings). -/
private theorem p19_epsilon_pair {e : Set V3} (h : ∃ p : V3 × V3, e = {p.1, p.2}) :
    {(Classical.epsilon fun w : V3 × V3 => e = {w.1, w.2}).1,
      (Classical.epsilon fun w : V3 × V3 => e = {w.1, w.2}).2} = e :=
  Eq.symm (Classical.epsilon_spec_aux (by infer_instance)
    (fun w : V3 × V3 => e = {w.1, w.2}) h)

/-- The two encodings of the cell-edge inner sum agree: `gammaX` (PA2:448)
guards on `e ∈ edgeX V X` and then fixes the pair representation `q` of `e`
by `Classical.epsilon`, while `KIZHLTL4` (PackingAuto16:310) fixes `q` first
and guards on `{q.1, q.2} ∈ edgeX V X`. On the summation domain `edgeX V X`
every `e` is a pair `{u, v}`, so the two guards coincide. -/
private theorem p19_inner_guard_congr (V X : Set V3) :
    setSum (edgeX V X) (fun e =>
        if e ∈ edgeX V X then
          let q := Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}
          dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
        else 0)
      = setSum (edgeX V X) (fun e =>
          let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
          if {q.1, q.2} ∈ edgeX V X then
            dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
          else 0) := by
  refine p19_setSumCongr (fun e he => ?_)
  simp only [edgeX, Set.mem_setOf_eq] at he
  obtain ⟨u, v, rfl, hu, hv, hne⟩ := he
  have hmemUV : {u, v} ∈ edgeX V X := ⟨u, v, rfl, hu, hv, hne⟩
  -- zeta-normalize the `let q := …` guard, then identify the epsilon pair
  simp only []
  rw [p19_epsilon_pair (e := {u, v}) ⟨(u, v), rfl⟩, if_pos hmemUV]

/-- GIANT — HOL `NEGLIGIBLE_FUNC` (UPFZBZM.hl:66-220, part 2 of UPFZBZM):
the same functional `G` has quadratic growth (`negligible_fun_0`). HL proof
architecture: split `sum (V ∩ ball 0 r) G = sum f1 + sum f3 - sum f4`
(SUM_ADD/SUB/NEG/CONST/LMUL over the finite packing — NEEDS FINITE_PACK_LEMMA
/ `Packing3.KIUMVTC`); bound `sum f1` by KIZHLTL1 (volume of the cells vs
Voronoi volume, `c * r^2`), `sum f3` (`&CARD * 8 mm1`) by KIZHLTL2
(`c' * r^2`), the edge term `f4` by KIZHLTL4 (`c'' * r^2`), and the total
`T1 + T2 + T3 = sum {X | X ⊆ ball 0 r ∧ mcell_set V X} (gammaX V X lmfun)`
by SUM_GAMMAX_LMFUN_ESTIMATE (`c''' * r^2`) — the regrouping is SUM_ADD/SUB/
LMUL over the finite cell family (NEEDS FINITE_MCELL_SET_LEMMA, PackingAuto15)
plus the `gammaX` unfolding; the witness constant is `G = -c''' - c - c' -
c''`.

DISCHARGES: none (internal part of UPFZBZM; feeds the capstone). -/
theorem NEGLIGIBLE_FUNC (V : Set V3) (hs : saturated V) (hp : Packing V)
    (hcc : cellClusterInequality V) (_hT : TSKAJXY_statement)
    (_hlm : lmfunInequality V) (G : V3 → ℝ)
    (hG : G = fun u => -volume.real (voronoiOpenP19 V u) + 8 * mm1 -
      8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        (fun v => lmfun (hl [u, v]))) : negligibleFun0 G V := by
  subst hG
  rw [negligible_fun_any_C]
  -- the four upstream inputs (KIZHLTL.hl ×3 + sum_gamma.hl)
  obtain ⟨c, hc1⟩ := KIZHLTL1 V
  obtain ⟨c', hc2⟩ := KIZHLTL2 V
  obtain ⟨c'', hc3⟩ := KIZHLTL4 V
  obtain ⟨c''', hc4⟩ := SUM_GAMMAX_LMFUN_ESTIMATE_p19 V
  refine ⟨-c''' - c - c' - c'', fun r hr => ?_⟩
  -- finiteness of the two summation families (HL FINITE_PACK_LEMMA via
  -- `Statement.Packing.finite_inter_ball`, FINITE_MCELL_SET_LEMMA via PA15)
  have hfinV : (V ∩ Metric.ball 0 r).Finite := hp.finite_inter_ball r
  have hfinB : ({X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}).Finite :=
    FINITE_MCELL_SET_LEMMA V r hp hs
  -- the three cell-family aggregates (HL abbreviations T1/T2/T3)
  obtain ⟨T1, hT1⟩ : ∃ T : ℝ,
      T = setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real :=
    ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T : ℝ, T = -((2 * mm1 / Real.pi) *
      setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V)) :=
    ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T : ℝ, T = (8 * mm2 / Real.pi) *
      setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
        (fun X : Set V3 => setSum (edgeX V X) fun e =>
          let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
          if {q.1, q.2} ∈ edgeX V X then
            dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
          else 0) :=
    ⟨_, rfl⟩
  -- Σ_B gammaX unfolds to the vol / totalSolid / edge triple, with the
  -- inner epsilon-guard aligned to KIZHLTL4's encoding
  have hgam : setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
      (fun X => gammaX V X lmfun)
      = setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (fun X : Set V3 =>
          volume.real X - (2 * mm1 / Real.pi) * totalSolid V X
            + (8 * mm2 / Real.pi) * setSum (edgeX V X) fun e =>
              let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
              if {q.1, q.2} ∈ edgeX V X then
                dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
              else 0) := by
    refine p19_setSumCongr (fun X _ => ?_)
    unfold gammaX
    rw [p19_inner_guard_congr V X]
  -- the `T1 + T2 + T3 = Σ_B gammaX` regrouping over the finite family B
  have hsplitB : setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real
        - (2 * mm1 / Real.pi) *
          setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V)
        + (8 * mm2 / Real.pi) *
          setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
            (fun X : Set V3 => setSum (edgeX V X) fun e =>
              let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
              if {q.1, q.2} ∈ edgeX V X then
                dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
              else 0)
      = setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (fun X : Set V3 =>
          volume.real X - (2 * mm1 / Real.pi) * totalSolid V X
            + (8 * mm2 / Real.pi) * setSum (edgeX V X) fun e =>
              let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
              if {q.1, q.2} ∈ edgeX V X then
                dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
              else 0) :=
    p19_setSum_split3 hfinB volume.real (totalSolid V) (fun X : Set V3 =>
      setSum (edgeX V X) fun e =>
        let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
        if {q.1, q.2} ∈ edgeX V X then
          dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
        else 0) (2 * mm1 / Real.pi) (8 * mm2 / Real.pi)
  have hregroup : T1 + T2 + T3
      = setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
          (fun X => gammaX V X lmfun) := by
    linarith [hT1, hT2, hT3, hsplitB, hgam]
  have hkey : c''' * r ^ 2 ≤ T1 + T2 + T3 := by
    linarith [hc4 r hs hp hr hcc _hT, hregroup]
  -- sum(V ∩ ball 0 r) G = sum f1 + sum f3 - sum f4 (HL f1/f2/f3/f4/f5 split)
  have hsplit : setSum (V ∩ Metric.ball 0 r)
        (fun u : V3 => -volume.real (voronoiOpenP19 V u) + 8 * mm1 -
          8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
            (fun v => lmfun (hl [u, v])))
      = setSum (V ∩ Metric.ball 0 r)
          (fun u : V3 => -volume.real (voronoiOpenP19 V u)) +
        setSum (V ∩ Metric.ball 0 r) (fun u : V3 => 8 * mm1 -
          8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
            (fun v => lmfun (hl [u, v]))) := by
    have hre : setSum (V ∩ Metric.ball 0 r)
        (fun u : V3 => -volume.real (voronoiOpenP19 V u) + 8 * mm1 -
          8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
            (fun v => lmfun (hl [u, v])))
        = setSum (V ∩ Metric.ball 0 r) (fun u : V3 =>
            -volume.real (voronoiOpenP19 V u) +
              (8 * mm1 - 8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
                (fun v => lmfun (hl [u, v])))) :=
      p19_setSumCongr (fun u _ => by ring)
    rw [hre, p19_setSum_add]
  have hsplit2 : setSum (V ∩ Metric.ball 0 r) (fun u : V3 => 8 * mm1 -
        8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
          (fun v => lmfun (hl [u, v])))
      = setSum (V ∩ Metric.ball 0 r) (fun _ : V3 => (8 : ℝ) * mm1)
        - 8 * mm2 * setSum (V ∩ Metric.ball 0 r) (fun u : V3 =>
            setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
              (fun v => lmfun (hl [u, v]))) := by
    rw [p19_setSum_sub, p19_setSum_smul (8 * mm2) (fun u : V3 =>
      setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0} (fun v => lmfun (hl [u, v])))]
  -- bound sum f1 by KIZHLTL1 (voronoiOpenP16 summand is definitionally the
  -- voronoiOpenP19 one, so the ascribed statement type-checks verbatim)
  have hb1 : setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real
        + c * r ^ 2
      ≤ setSum (V ∩ Metric.ball 0 r)
          (fun u : V3 => volume.real (voronoiOpenP19 V u)) :=
    hc1 r hs hp hr
  have hneg1 : setSum (V ∩ Metric.ball 0 r)
      (fun u : V3 => -volume.real (voronoiOpenP19 V u))
      = -setSum (V ∩ Metric.ball 0 r)
          (fun u : V3 => volume.real (voronoiOpenP19 V u)) :=
    p19_setSum_neg _
  have hb1' : setSum (V ∩ Metric.ball 0 r)
      (fun u : V3 => -volume.real (voronoiOpenP19 V u)) ≤ -T1 - c * r ^ 2 := by
    linarith [hneg1, hb1, hT1]
  -- bound sum f3 by KIZHLTL2 (SUM_CONST fold + card shape)
  have hb2 : ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1
        + c' * r ^ 2
      ≤ (2 * mm1 / Real.pi) *
        setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V) :=
    hc2 r hs hp hr
  have hconst : setSum (V ∩ Metric.ball 0 r) (fun _ : V3 => (8 : ℝ) * mm1)
      = ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1 :=
    p19_setSum_const hfinV (8 * mm1) |>.trans (by ring)
  have hb2' : setSum (V ∩ Metric.ball 0 r) (fun _ : V3 => (8 : ℝ) * mm1)
      ≤ -T2 - c' * r ^ 2 := by
    linarith [hconst, hb2, hT2]
  -- bound sum f4 by KIZHLTL4
  have hb3 : (8 * mm2 / Real.pi) *
        setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
          (fun X : Set V3 => setSum (edgeX V X) fun e =>
            let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
            if {q.1, q.2} ∈ edgeX V X then
              dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
            else 0)
      + c'' * r ^ 2 ≤
      8 * mm2 * setSum (V ∩ Metric.ball 0 r)
        (fun u : V3 => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
          (fun v => lmfun (hl [u, v]))) :=
    hc3 r hs hp hr
  have hb3' : T3 + c'' * r ^ 2 ≤ 8 * mm2 * setSum (V ∩ Metric.ball 0 r)
      (fun u : V3 => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
        (fun v => lmfun (hl [u, v]))) := by
    linarith [hT3, hb3]
  -- witness arithmetic: C = -c''' - c - c' - c''
  have hwit : (-c''' - c - c' - c'') * r ^ 2
      = -(c''' * r ^ 2) - (c * r ^ 2 + c' * r ^ 2 + c'' * r ^ 2) := by ring
  linarith [hsplit, hsplit2, hb1', hb2', hb3', hkey, hwit]

/-- HOL `UPFZBZM` (UPFZBZM.hl:227-235), the book-lemma capstone: from the
cluster/density hypothesis bundle there exists an `fcc_compatible` and
`negligible_fun_0` functional (witness: the functional of parts 1-2).

DISCHARGES: PackingAuto2.UPFZBZM_concl (PackingAuto2.lean:850). -/
theorem UPFZBZM (V : Set V3) (hs : saturated V) (hp : Packing V)
    (hcc : cellClusterInequality V) (hT : TSKAJXY_statement)
    (hlm : lmfunInequality V) :
    ∃ G : V3 → ℝ, negligibleFun0 G V ∧ fccCompatible G V := by
  refine ⟨fun u => -volume.real (voronoiOpenP19 V u) + 8 * mm1 -
    8 * mm2 * setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
      (fun v => lmfun (hl [u, v])),
    NEGLIGIBLE_FUNC V hs hp hcc hT hlm _ rfl,
    FCC_COMPATABILITY_FUNC V hs hp hcc hT hlm _ rfl⟩

/-! ## RDWKARC.hl -/

/-- HOL `JGXZYGW` (pack1.hl:519) — `_p19` copy. NOTE: PackingAuto1 carries a
ported `JGXZYGW` (over `Space3` with its private `fcc_compatible`-style
hypotheses), but its olean is not built in this checkout, so the statement is
copied here against the PackingAuto2 encoding (`volume.real`,
`fccCompatible`, `negligibleFunP`). NEEDS discharged (2026-09-29): the chain
is now carried by the new leaf module `Kepler.Text.PackingJGXZYGW`
(`jgxzygw_p`, axioms standard-three only); see docs/jgxzygw-scout.md §5. -/
private theorem JGXZYGW_p19 (S : Set V3) (p : V3) (hV : Packing S)
    (hs : saturated S)
    (hA : ∃ A : V3 → ℝ, fccCompatible A S ∧ negligibleFunP A S p) :
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      volume.real ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) /
        volume.real (Metric.ball p r) ≤ Real.pi / Real.sqrt 18 + c / r := by
  obtain ⟨A, hfcc, hneg⟩ := hA
  obtain ⟨C, hC0, hC⟩ := hneg
  exact jgxzygw_p S p hV hs ⟨A, fun v hv => hfcc v hv, C, hC0,
    fun r hr hfin => by simpa only [setSum, dif_pos hfin] using hC r hr⟩

/-- HOL `JGXZYGW_KY` (RDWKARC.hl:76-91): `JGXZYGW` at the origin with the
`negligible_fun_0` functional form. -/
theorem JGXZYGW_KY (S : Set V3) (hV : Packing S) (hs : saturated S)
    (hA : ∃ A : V3 → ℝ, fccCompatible A S ∧ negligibleFun0 A S) :
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      volume.real ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball (0 : V3) r) /
        volume.real (Metric.ball (0 : V3) r) ≤ Real.pi / Real.sqrt 18 + c / r :=
  JGXZYGW_p19 S 0 hV hs hA

/-- HOL `PACKING_SUBSET` (RDWKARC.hl:95): a subset of a packing is a
packing. -/
theorem PACKING_SUBSET (V S : Set V3) (hV : Packing V) (hsub : S ⊆ V) :
    Packing S := by
  intro u hu v hv hlt
  exact hV u (hsub hu) v (hsub hv) hlt

/-- HOL `PACKING_TRANS` (RDWKARC.hl:115): packings are translation
invariant. -/
theorem PACKING_TRANS (V : Set V3) (hV : Packing V) (x : V3) :
    Packing {u | u + x ∈ V} := by
  intro u hu v hv hlt
  have hd : dist (u + x) (v + x) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm]
    abel
  exact add_right_cancel (hV _ hu _ hv (by rwa [hd]))

/-- HOL `SATURATED_TRANS` (RDWKARC.hl:146): saturation is translation
invariant. -/
theorem SATURATED_TRANS (V : Set V3) (hs : saturated V) (x : V3) :
    saturated {u | u + x ∈ V} := by
  intro y
  obtain ⟨z, hz, hd⟩ := hs (y + x)
  refine ⟨z - x, ?_, ?_⟩
  · simpa using hz
  · have hd2 : dist y (z - x) = dist (y + x) z := by
      rw [dist_eq_norm, dist_eq_norm]
      abel
    rwa [hd2]

/-- The circumradius of a two-point set is half the distance
(RDWKARC.hl `RADV_TRANS_EQ` core: `radV {u,v}` via `Marchal_cells_3.HL_2`). -/
private theorem radV_pair (u v : V3) (huv : u ≠ v) :
    radV {u, v} = dist u v / 2 := by
  have hmem : AffineMap.lineMap (k := ℝ) u v (1 / 2) ∈ (affineSpan ℝ {u, v} : Set V3) :=
    AffineMap.lineMap_mem_affineSpan_pair (1 / 2) u v
  have hmd1 : dist u v / 2 = dist (AffineMap.lineMap (k := ℝ) u v (1 / 2)) u := by
    rw [dist_lineMap_left]
    norm_num
    ring
  have hmd2 : dist u v / 2 = dist (AffineMap.lineMap (k := ℝ) u v (1 / 2)) v := by
    rw [dist_lineMap_right]
    norm_num
    ring
  have hwit : ∃ y : V3, y ∈ (affineSpan ℝ {u, v} : Set V3) ∧
      ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3), c = dist y w := by
    refine ⟨AffineMap.lineMap (k := ℝ) u v (1 / 2), hmem, dist u v / 2, fun w hw => ?_⟩
    rcases Set.mem_insert_iff.mp hw with rfl | rfl
    · exact hmd1
    · exact hmd2
  have hcc : (fun v0 : V3 => v0 ∈ (affineSpan ℝ {u, v} : Set V3) ∧
      ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3), c = dist v0 w) (circumcenter {u, v}) :=
    Classical.epsilon_spec hwit
  obtain ⟨hccmem, c₀, hc₀⟩ := hcc
  have hu : u ∈ (affineSpan ℝ {u, v} : Set V3) := mem_affineSpan (k := ℝ) (by simp)
  have hdir : circumcenter {u, v} - u ∈ vectorSpan ℝ {u, v} := by
    have h5 : circumcenter {u, v} -ᵥ u ∈ (affineSpan ℝ {u, v}).direction :=
      AffineSubspace.vsub_mem_direction hccmem hu
    rwa [direction_affineSpan] at h5
  rw [vectorSpan_pair (k := ℝ) u v] at hdir
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdir
  have ht' : t • (u - v) = circumcenter {u, v} - u := ht
  have hduv : dist u v ≠ 0 := fun hzz => huv (dist_eq_zero.mp hzz)
  have h1 : |t| * dist u v = dist (circumcenter {u, v}) u := by
    rw [dist_eq_norm, dist_eq_norm, ← ht', norm_smul, Real.norm_eq_abs]
  have hv2 : circumcenter {u, v} - v = (t + 1) • (u - v) := by
    rw [show (t + 1) • (u - v) = t • (u - v) + (u - v) from by rw [add_smul, one_smul], ht']
    abel
  have h2 : |t + 1| * dist u v = dist (circumcenter {u, v}) v := by
    rw [dist_eq_norm, dist_eq_norm, hv2, norm_smul, Real.norm_eq_abs]
  have habs : |t| = |t + 1| := by
    have h3 : |t| * dist u v = |t + 1| * dist u v := by
      rw [h1, h2, ← hc₀ _ (Set.mem_insert u {v}),
        ← hc₀ _ (Set.mem_insert_of_mem _ (by simp))]
    exact mul_right_cancel₀ hduv h3
  have hhalf : t = -(1 / 2) := by
    rcases abs_eq_abs.mp habs with h | h
    · linarith
    · linarith
  have hfin : dist (circumcenter {u, v}) u = dist u v / 2 := by
    rw [← h1, hhalf, abs_of_neg (show (0 : ℝ) > -(1 / 2) from by norm_num)]
    ring
  have hQ : (fun c : ℝ => ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter {u, v}) w) (radV {u, v}) :=
    Classical.epsilon_spec
      (p := fun c : ℝ => ∀ w ∈ ({u, v} : Set V3), c = dist (circumcenter {u, v}) w)
      ⟨c₀, hc₀⟩
  rw [hQ u (Set.mem_insert u {v})]
  exact hfin

/-- HOL `RADV_TRANS_EQ` (RDWKARC.hl:171): the circumradius of a pair is
translation invariant. -/
theorem RADV_TRANS_EQ (u v x : V3) (h : ¬(u = v)) :
    radV {u, v} = radV {u + x, v + x} := by
  have hd : dist (u + x) (v + x) = dist u v := by
    rw [dist_eq_norm, dist_eq_norm]
    abel
  rw [radV_pair u v (fun huv => h huv),
    radV_pair (u + x) (v + x) (by simp [h]), hd]

/-- GIANT — HOL `RDWKARC` (RDWKARC.hl:180-314): if the Kepler density bound
fails then some packing inside the ball annulus violates the local annulus
inequality. HL proof architecture: unfold `kepler_conjecture` and move the
failure to `¬(?c ...)` (MESON); if `lmfun_inequality V` held, UPFZBZM +
JGXZYGW_KY would give the density bound — contradiction; hence some `u ∈ V`
has edge lmfun-sum `> 12`; translate by `-u` (`PACKING_TRANS`,
`SATURATED_TRANS`) and intersect with `ball_annulus` (`PACKING_SUBSET`); the
local annulus inequality fails because the annulus sum re-indexes to the
`V`-edge sum (SUM_EQ_GENERAL_INVERSES along `v ↦ v + u`, `cball`/`DIFF`
set algebra, packing separation for the `v = u` junk case, and the `hl`
translation invariance `radV {0, v} = radV {-u, v - u}` via RADV_TRANS_EQ).

DISCHARGES: PackingAuto2.RDWKARC_concl (PackingAuto2.lean:856). -/
theorem RDWKARC : ¬keplerConjecture →
    (∀ V : Set V3, Packing V → saturated V → cellClusterInequality V) →
    TSKAJXY_statement →
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V := by
  sorry

end Kepler.Text

/-
LocalAuto18 — Local Fan chapter, four-file bundle (skeleton-first pass):

  - `scripts/local/WJSCPRO.hl` (3216 ln, 4 thms; H. L. Truong 2012) — the
    `POWER_MOD_FUN` cycle-iteration identity and the closed/bounded/compact
    kit `CLOSED_SY` / `BOUNDED_SY` / `WJSCPRO` for the stable-system space
    `{matvec v | rows in ball_annulus ∧ CONDITION1_SY ∧ CONDITION2_SY}`.
  - `scripts/local/IUNBUIG.hl` (1888 ln, 22 thms; T. Hales 2013) — the
    main-estimate toolkit: quadratic-root finiteness, `arcV`/`aff_ge` angle
    addition, ε-merge lemmas, the `re_eqvl` positivity/sign kit, the
    coplanarity ↔ `delta_y` criterion, finite-range constancy, the planar
    deformation rigidity lemma, the `EGHNAVX` azimuth-ordering over scs
    realisations, the cross/aff_gt reductions, the a5/b5 assumption
    reductions, `azim_dih_y`, `azim5_reduction`, `L13_LEMMA`, `IUNBUIG`.
  - `scripts/local/AURSIPD.hl` (1850 ln, 4 thms) — numseg/periodic-image
    bookkeeping, the azim/interior-angle sum identity, and the stratum
    count bound `AURSIPD`.
  - `scripts/local/CNICGSF.hl` (908 ln, 15 thms) — the marching arrows of
    the 5-cycle registries: `scs_diag` facts for `scs_5I1`/`scs_5I2`/
    `scs_5M1`, the slice arrows `SCS_*_SLICE_*`, and `CNICGSF1..5`.

FILE MAP
  Section 0 (verbatim `_p18` copies; see ENCODING): `deltaX4_p18`,
    `deltaY_p18`, `dihY_p18`, `EE_p18`, `azimCycle_p18`, `rhoNode1_p18`,
    `azimInFan_p18`, `torsor_p18`, `constraintSystem_p18`,
    `stableSystem_p18`, `rowV3_p18`, `CONDITION2_SY_p18`, `BSY1body_p18`.
  Section A (WJSCPRO): `POWER_MOD_FUN_p18` (proved), the space
    `SYset_p18` (= `BSY1body_p18` ∩ `CONDITION2_SY_p18`), `CLOSED_SY_p18`
    (sorry; the HOL proof spans WJSCPRO.hl:63-3174), `BOUNDED_SY_p18`
    (proved from `COMPACT_BALL_ANNULUS_MATVEC`), `WJSCPRO_p18` (proved =
    closed + bounded).
  Section B (IUNBUIG): `re_eqvl_imp_le_p18`, `re_eqvl_real_sgn_p18`,
    `quadratic_at_most_2_roots_p18`, `SUM_NUMSEG4_p18`,
    `epsilon_pent/hex/hept_p18`,
    `real_continuous_finite_range_constant_p18`,
    `a5_assumption_reduction_p18`, `b5_assumption_reduction_p18`
    (proved); `ARCV_ADD_AFF_GE_p18`, `coplanar_delta_y_zero_p18`,
    `planar_deform_dist_p18`, `deform_pent_exists_p18`,
    `EGHNAVX_COLL_SCS_p18`, `EGHNAVX_SCS_p18`,
    `coplanar_cross_reduction_p18`, `coplanar_aff_gt_simple_p18`,
    `azim_dih_y_p18`, `azim5_reduction_p18`, `L13_LEMMA_p18`,
    `IUNBUIG_p18` (sorry giants; `Deformation` from LocalAuto1).
  Section C (AURSIPD): `REP_NUMSEG_p18`, `PERIODIC_IMAGE2_p18` (proved);
    `SUM_AZIM_EQ_ANGLE_LE4_FUN_p18`, `AURSIPD_p18` (sorry).
  Section D (CNICGSF): the five `SCS_DIAG_*_p18` (proved, decidable);
    the five slice arrows `SCS_*_SLICE_*_p18` (sorry; `LKGRQUI` lane);
    `CNICGSF1..5_p18` (sorry; need the `PRO_EQU_ID1`/`YXIONXL3` kit on
    top of the slices).

ENCODING NOTES
  - Import discipline: this file sits on the LocalAuto1/`PackingAuto18`
    side of the fatal `atn2` duplication — LocalAuto2/`PackingAuto20`
    (also LocalAuto9/LocalAuto11, which import LocalAuto2) must NOT be
    imported next to LocalAuto1. Everything needed from those lanes is
    carried as a verbatim `_p18` copy with a NEEDS merge marker:
    `deltaX4_p18`/`deltaY_p18`/`dihY_p18` (PackingAuto20:80-92,
    LocalAuto11:129-151), `EE_p18`/`azimCycle_p18`/`rhoNode1_p18`/
    `azimInFan_p18` (LocalAuto2:82-203), `torsor_p18`/
    `constraintSystem_p18`/`stableSystem_p18`/`rowV3_p18`/
    `CONDITION2_SY_p18`/`BSY1body_p18` (LocalAuto9:145-160,396,1044-1058).
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `real^N^M` /
    `(M,3)finite_product` ↔ `FinVec`/`FinMat` (LocalAuto4); HOL 1-based
    `row i (vecmats l)` ↔ `rowV3_p18 l i`; `IMAGE v (:num)` ↔
    `Set.range v`; `num->bool` ↔ `Finset ℕ` where relevant.
  - Importable kit (no new copies): `reEqvl`, `cross3`, `upsX`, `deltaX`,
    `atn2`, `arcV`, `azim`, `affGt`/`affGe`, `projection`, `Collinear3`,
    `Coplanar`, `ballAnnulus`, `h0`, `cstab`, `cstab_p4`, `setSum`,
    `Periodic`/`Periodic2`, `ScsV39` + `isScsV39`/`BBsV39`/`MMsV39`/
    `scsGeneric`/`scsIsStr`/`scsDiag`/`scsStabDiagV39`/`scsPropEquV39`/
    `scsArrowV39` and the registry objects `scs5I1`,…,`scs4M5'`
    (LocalAuto1), `interiorAngle1`, `Deformation`, `Generic`,
    `ConvexLocalFan` (LocalAuto1), `vecmatsV3_p4`/`V_SY_p4`/`E_SY_p4`/
    `F_SY_p4`/`convexLocalFan_p4`/`COMPACT_BALL_ANNULUS_MATVEC`/
    `ballAnnulus_norm_bounds` (LocalAuto4), `MainNonlinearTerminalV11`
    (LocalAnchors). Same-wave lanes LocalAuto12-17 are NOT imported
    (bundle rules).
  - HOL `real_interval (a,b)` ↔ `Set.Ioo a b`; `f real_continuous_on` ↔
    `ContinuousOn f`; `ITER i (rho_node1 FF) u` ↔ `(rhoNode1_p18 FF)^[i] u`.
  - `ff` in `SUM_AZIM_EQ_ANGLE_LE4_FUN` has no locatable port in the
    corpus (absent from QKNVMLB/localization/hypermap.hl); it is carried
    as an explicit `V3 → ℝ` parameter of the statement. NEEDS: locate the
    HOL def at merge.
  - `main_nonlinear_terminal_v11` (terminal.hl:37, bare Prop) ↔
    `mainNonlinearTerminalV11_p18 := ∀ y, MainNonlinearTerminalV11 y`.
  - No `native_decide` anywhere; `sorry` bodies carry `-- DISCHARGES:`
    markers naming the missing HOL inputs.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: verbatim `_p18` copies (atn2 two-sides clash) -/

/-- HOL `delta_x4` (sphere.hl:110): partial derivative of `delta_x` at
`x4`. Verbatim twin of PackingAuto20's `deltaX4f`. NEEDS: merge. -/
noncomputable def deltaX4_p18 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `delta_y` (sphere.hl): `delta_x` at squared lengths; verbatim twin
of LocalAuto11's `deltaY_p11` (body = `deltaX` of PackingAuto18). NEEDS:
merge. -/
noncomputable def deltaY_p18 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `dih_y` (sphere.hl:159). Verbatim twin of PackingAuto20's `dihY`
(via `dihXf`). NEEDS: merge. -/
noncomputable def dihY_p18 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  Real.pi / 2 + atn2
    (Real.sqrt (4 * (y1 * y1) *
      deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
    (-(deltaX4_p18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6)))

/-- HOL `EE v E` (localization.hl:27): the `E`-neighbours of `v`. Verbatim
twin of `EE_p2`. NEEDS: merge. -/
def EE_p18 {α : Type*} (v : α) (S : Set (Set α)) : Set α := {w | {v, w} ∈ S}

/-- HOL `azim_cycle` (sphere.hl:414). Verbatim twin of `azimCycle_p2`.
NEEDS: merge. -/
noncomputable def azimCycle_p18 (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-- HOL `rho_node1` (localization.hl:115, the overriding second copy).
Verbatim twin of `rhoNode1_p2`. NEEDS: merge. -/
noncomputable def rhoNode1_p18 (FF : Set (V3 × V3)) (v : V3) : V3 :=
  Classical.epsilon fun w => (v, w) ∈ FF

/-- HOL `azim_in_fan` (localization.hl:74). Verbatim twin of
`azimInFan_p2`. NEEDS: merge. -/
noncomputable def azimInFan_p18 (d : V3 × V3) (E : Set (Set V3)) : ℝ :=
  if 1 < (EE_p18 d.1 E).ncard then azim 0 d.1 d.2 (azimCycle_p18 (EE_p18 d.1 E) 0 d.1 d.2)
  else 2 * Real.pi

/-- HOL `torsor` (dih2k.hl:48), `Finset ℕ` instance. Verbatim twin of
`torsor_p9`. NEEDS: merge. -/
def torsor_p18 (s : Finset ℕ) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ s.card = k

/-- HOL `constraint_system` (dih2k.hl:52) with `d : ℝ`. Verbatim twin of
`constraintSystem_p9`. NEEDS: merge. -/
def constraintSystem_p18 (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor_p18 s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ s.image (fun i => {i, f i}) ∧
    J.card + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61) with `d : ℝ`. Verbatim twin of
`stableSystem_p9`. NEEDS: merge. -/
def stableSystem_p18 (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p18 k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab_p4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab_p4)

/-- HOL `row i (vecmats l)`: the `i`-th row (1-based, junk value `0`
off-range) as a `V3`. Verbatim twin of `rowV3_p9`. NEEDS: merge. -/
def rowV3_p18 {m : ℕ} (l : FinVec m 3) (i : ℕ) : V3 :=
  if h : 1 ≤ i ∧ i ≤ m then vecmatsV3_p4 l ⟨i - 1, by omega⟩ else 0

/-- HOL `CONDITION2_SY` (dih2k.hl:88) at `ℕ` index type. Verbatim twin of
`CONDITION2_SY_p9`. NEEDS: merge. -/
def CONDITION2_SY_p18 (k : ℕ) (l : FinVec k 3) : Prop :=
  convexLocalFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    (F_SY_p4 (vecmatsV3_p4 l))

/-- The `B_SY1` body-set: HOL `{matvec v | rows v in ball_annulus ∧
CONDITION1_SY a b v}` (k = dimindex(:M)). Verbatim twin of
`BSY1body_p9`. NEEDS: merge. -/
def BSY1body_p18 (k : ℕ) (a b : ℕ → ℕ → ℝ) : Set (FinVec k 3) :=
  {l | (∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus) ∧
    ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
      a i j ≤ ‖rowV3_p18 l i - rowV3_p18 l j‖ ∧
        ‖rowV3_p18 l i - rowV3_p18 l j‖ ≤ b i j}

/-- EXTERNAL-ANCHOR twin of `LocalAnchors.MainNonlinearTerminalV11`
(terminal.hl:24-44): the box-constraint shape of the opaque
`main_nonlinear_terminal_v11` hypothesis (LocalAnchors itself is not
importable next to LocalAuto1: duplicate `scsBasicV39`). NEEDS: merge. -/
def MainNonlinearTerminalV11_p18 (y : Fin 6 → ℝ) : Prop :=
  2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧
    2 ≤ y 1 ∧ y 1 ≤ 2 * h0 ∧
    2 ≤ y 2 ∧ y 2 ≤ 2 * h0 ∧
    3.01 ≤ y 3 ∧ y 3 ≤ 3.915 ∧
    y 4 = 2 ∧ y 5 = 2

/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:37) as a bare Prop;
opaque in scripts/local (164 uses). -/
def mainNonlinearTerminalV11_p18 : Prop := ∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11_p18 y

/-! ## Section A: WJSCPRO (Wjscpro.hl) -/

/-- HOL `POWER_MOD_FUN` (WJSCPRO.hl:42): the successor-mod cycle,
iterated `n` times, advances by `n`. -/
theorem POWER_MOD_FUN_p18 (n i k : ℕ) (_hn : 1 ≤ n) (_hk : 1 < k) :
    (fun j => (1 + j) % k)^[n] i = (n + i) % k := by
  obtain ⟨m, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have key : ∀ p i, (fun j => (1 + j) % k)^[p + 1] i = (p + 1 + i) % k := by
    intro p
    induction p with
    | zero => intro i; rfl
    | succ p ih =>
      intro i
      rw [Function.iterate_succ', Function.comp_apply, ih]
      have hstep : ∀ x : ℕ, (1 + x % k) % k = (1 + x) % k := fun x => by
        rw [Nat.add_comm 1 (x % k), Nat.mod_add_mod, Nat.add_comm x 1]
      rw [hstep]
      congr 1
      omega
  exact key m i

/-- The `WJSCPRO` space: HOL `{matvec v | !i. row i v IN ball_annulus /\
CONDITION1_SY a b v /\ CONDITION2_SY v}` at ambient size `k`, rendered as
the `BSY1body_p18` rows/CONDITION1 body intersected with `CONDITION2_SY_p18`
(since `vecmats ∘ matvec = id`, the members agree with the HOL matrix
image). -/
def SYset_p18 (k : ℕ) (a b : ℕ → ℕ → ℝ) : Set (FinVec k 3) :=
  {l | l ∈ BSY1body_p18 k a b ∧ CONDITION2_SY_p18 k l}

/-- HOL `CLOSED_SY` (WJSCPRO.hl:63). Giant (the HOL proof spans
WJSCPRO.hl:63-3174, threading sequential limits through the rows,
`CONDITION1_SY` and the fan-convexity clause `CONDITION2_SY`). -/
theorem CLOSED_SY_p18 {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (_hsys : stableSystem_p18 k d s a b J f) (_hk1 : 1 < k) (_hk2 : 2 < k) :
    IsClosed (SYset_p18 k a b) := by
  sorry
  -- DISCHARGES: the `BSY1body_p18` factor is closed exactly as in
  -- LocalAuto9's `CLOSED_TRI_SY_p9` (proved there; blocked here only by
  -- that theorem's `triStable_p9` hypothesis, so the intersection
  -- argument must be redone locally); the `CONDITION2_SY_p18` factor
  -- needs the limit argument on `V_SY`/`E_SY`/`F_SY`
  -- (HOL: CLOSED_SY's SKOLEM/sequential-lims part).

/-- HOL `BOUNDED_SY` (WJSCPRO.hl:3179): the space sits inside the compact
rows-in-`ball_annulus` product. -/
theorem BOUNDED_SY_p18 {k : ℕ} {a b : ℕ → ℕ → ℝ} :
    Bornology.IsBounded (SYset_p18 k a b) := by
  refine Bornology.IsBounded.subset COMPACT_BALL_ANNULUS_MATVEC.isBounded ?_
  intro l hl
  have h : l ∈ BSY1body_p18 k a b := hl.1
  simpa only [BSY1body_p18, Set.mem_setOf_eq, vecmatsV3_p4] using h.1

/-- HOL `WJSCPRO` (WJSCPRO.hl:3194): compactness = closed + bounded. -/
theorem WJSCPRO_p18 {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
    (hsys : stableSystem_p18 k d s a b J f) (hk1 : 1 < k) (hk2 : 2 < k) :
    IsCompact (SYset_p18 k a b) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨CLOSED_SY_p18 hsys hk1 hk2, BOUNDED_SY_p18⟩

/-! ## Section B: IUNBUIG (Iunbuig.hl) -/

/-- HOL `re_eqvl_imp_le` (IUNBUIG.hl:98): `re_eqvl`-equivalent reals agree
on nonnegativity (`reEqvl` is the importable PackingAuto18 rendering of
Trigonometry2.re_eqvl). -/
theorem re_eqvl_imp_le_p18 {a b : ℝ} (h : reEqvl a b) : 0 ≤ a ↔ 0 ≤ b := by
  obtain ⟨t, ht, he⟩ := h
  rw [he]
  constructor
  · intro hle
    by_contra hneg
    have hbneg : b < 0 := lt_of_not_ge hneg
    have hlt := mul_neg_of_pos_of_neg ht hbneg
    linarith
  · intro hle
    exact mul_nonneg ht.le hle

/-- HOL `re_eqvl_real_sgn` (IUNBUIG.hl:112), with Mathlib's
`Real.sign` rendering of HOL `real_sgn`. -/
theorem re_eqvl_real_sgn_p18 {x y : ℝ} : reEqvl x y ↔ Real.sign x = Real.sign y := by
  constructor
  · rintro ⟨t, ht, hx⟩
    by_cases hyz : y = 0
    · rw [hx, hyz, mul_zero]
    · rcases lt_trichotomy 0 y with hypos | hyz' | hyneg
      · rw [hx, Real.sign_of_pos (by nlinarith), Real.sign_of_pos hypos]
      · exact absurd hyz'.symm hyz
      · rw [hx, Real.sign_of_neg (by nlinarith), Real.sign_of_neg hyneg]
  · intro hsgn
    by_cases hx0 : x = 0
    · have hy0 : y = 0 := by
        rw [hx0, Real.sign_zero] at hsgn
        exact (Real.sign_eq_zero_iff).mp hsgn.symm
      exact ⟨1, one_pos, by rw [hx0, hy0]; ring⟩
    · have hy0 : y ≠ 0 := by
        intro h
        rw [h, Real.sign_zero] at hsgn
        exact hx0 ((Real.sign_eq_zero_iff).mp hsgn)
      refine ⟨x / y, ?_, by field_simp⟩
      rcases lt_trichotomy 0 x with hxpos | hxz | hxneg
      · have hypos : 0 < y := by
          rcases lt_trichotomy 0 y with h | h | h
          · exact h
          · exact False.elim (hy0 h.symm)
          · rw [Real.sign_of_neg h, Real.sign_of_pos hxpos] at hsgn
            norm_num at hsgn
        exact div_pos hxpos hypos
      · exact False.elim (hx0 hxz.symm)
      · have hyneg : y < 0 := by
          rcases lt_trichotomy 0 y with h | h | h
          · rw [Real.sign_of_pos h, Real.sign_of_neg hxneg] at hsgn
            norm_num at hsgn
          · exact False.elim (hy0 h.symm)
          · exact h
        exact div_pos_of_neg_of_neg hxneg hyneg

/-- HOL `quadratic_at_most_2_roots` (IUNBUIG.hl:19). -/
theorem quadratic_at_most_2_roots_p18 (a b c : ℝ) :
    ∃ x₁ x₂ : ℝ, ∀ x, a ≠ 0 → a * x ^ 2 + b * x + c = 0 → x = x₁ ∨ x = x₂ := by
  by_cases hroot : ∃ x₁, a * x₁ ^ 2 + b * x₁ + c = 0
  · obtain ⟨x₁, h₁⟩ := hroot
    by_cases h1 : ∀ x₂, a * x₂ ^ 2 + b * x₂ + c = 0 → x₂ = x₁
    · exact ⟨x₁, x₁, fun x _ hx => Or.inl (h1 x hx)⟩
    · push_neg at h1
      obtain ⟨x₂, h₂, hx21⟩ := h1
      refine ⟨x₁, x₂, fun x ha hroot' => ?_⟩
      by_contra hne
      push_neg at hne
      have key : ∀ u z : ℝ, a * u ^ 2 + b * u + c = 0 →
          a * z ^ 2 + b * z + c = 0 → (z - u) * (a * (z + u) + b) = 0 := by
        intro u z hu hz
        have hexp : (z - u) * (a * (z + u) + b) =
            a * z ^ 2 + b * z - (a * u ^ 2 + b * u) := by ring
        have hu' : a * u ^ 2 + b * u = -c := by linarith
        have hz' : a * z ^ 2 + b * z = -c := by linarith
        rw [hexp, hz', hu']
        ring
      have hu : a * (x + x₁) + b = 0 := by
        rcases mul_eq_zero.mp (key x₁ x h₁ hroot') with h0 | h0
        · exact absurd (sub_eq_zero.mp h0) hne.1
        · exact h0
      have hv : a * (x + x₂) + b = 0 := by
        rcases mul_eq_zero.mp (key x₂ x h₂ hroot') with h0 | h0
        · exact absurd (sub_eq_zero.mp h0) hne.2
        · exact h0
      have h12 : a * (x₁ - x₂) = 0 := by
        have : a * (x + x₁) - a * (x + x₂) = 0 := by linarith
        nlinarith
      have h12' : x₁ = x₂ := by
        rcases mul_eq_zero.mp h12 with h | h
        · exact absurd h ha
        · exact sub_eq_zero.mp h
      exact hx21 h12'.symm
  · exact ⟨0, 0, fun x _ hx => absurd ⟨x, hx⟩ hroot⟩

/-- HOL `SUM_NUMSEG4` (IUNBUIG.hl:53). -/
theorem SUM_NUMSEG4_p18 (t : ℕ → ℝ) :
    ∑ i ∈ Finset.range 5, t i = t 0 + t 1 + t 2 + t 3 + t 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- HOL `epsilon_pent` (IUNBUIG.hl:62): five positive epsilons have a
common positive refinement. -/
theorem epsilon_pent_p18 {e e₁ e₂ e₃ e₄ : ℝ} (he : 0 < e) (he₁ : 0 < e₁)
    (he₂ : 0 < e₂) (he₃ : 0 < e₃) (he₄ : 0 < e₄) :
    ∃ e₅ > 0, (∀ t, |t| < e₅ → |t| < e) ∧ (∀ t, |t| < e₅ → |t| < e₁) ∧
      (∀ t, |t| < e₅ → |t| < e₂) ∧ (∀ t, |t| < e₅ → |t| < e₃) ∧
      (∀ t, |t| < e₅ → |t| < e₄) := by
  refine ⟨min e (min e₁ (min e₂ (min e₃ e₄))),
    lt_min he (lt_min he₁ (lt_min he₂ (lt_min he₃ he₄))), ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro t ht
    simp only [lt_min_iff] at ht
    tauto

/-- HOL `epsilon_hex` (IUNBUIG.hl:74). -/
theorem epsilon_hex_p18 {e e₁ e₂ e₃ e₄ e₅ : ℝ} (he : 0 < e) (he₁ : 0 < e₁)
    (he₂ : 0 < e₂) (he₃ : 0 < e₃) (he₄ : 0 < e₄) (he₅ : 0 < e₅) :
    ∃ e₆ > 0, (∀ t, |t| < e₆ → |t| < e) ∧ (∀ t, |t| < e₆ → |t| < e₁) ∧
      (∀ t, |t| < e₆ → |t| < e₂) ∧ (∀ t, |t| < e₆ → |t| < e₃) ∧
      (∀ t, |t| < e₆ → |t| < e₄) ∧ (∀ t, |t| < e₆ → |t| < e₅) := by
  refine ⟨min e (min e₁ (min e₂ (min e₃ (min e₄ e₅)))),
    lt_min he (lt_min he₁ (lt_min he₂ (lt_min he₃ (lt_min he₄ he₅)))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro t ht
    simp only [lt_min_iff] at ht
    tauto

/-- HOL `epsilon_hept` (IUNBUIG.hl:86). -/
theorem epsilon_hept_p18 {e e₁ e₂ e₃ e₄ e₅ e₆ : ℝ} (he : 0 < e) (he₁ : 0 < e₁)
    (he₂ : 0 < e₂) (he₃ : 0 < e₃) (he₄ : 0 < e₄) (he₅ : 0 < e₅)
    (he₆ : 0 < e₆) :
    ∃ e₇ > 0, (∀ t, |t| < e₇ → |t| < e) ∧ (∀ t, |t| < e₇ → |t| < e₁) ∧
      (∀ t, |t| < e₇ → |t| < e₂) ∧ (∀ t, |t| < e₇ → |t| < e₃) ∧
      (∀ t, |t| < e₇ → |t| < e₄) ∧ (∀ t, |t| < e₇ → |t| < e₅) ∧
      (∀ t, |t| < e₇ → |t| < e₆) := by
  refine ⟨min e (min e₁ (min e₂ (min e₃ (min e₄ (min e₅ e₆))))),
    lt_min he (lt_min he₁ (lt_min he₂ (lt_min he₃ (lt_min he₄ (lt_min he₅ he₆))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro t ht
    simp only [lt_min_iff] at ht
    tauto

/-- HOL `ARCV_ADD_AFF_GE` (IUNBUIG.hl:44). -/
theorem ARCV_ADD_AFF_GE_p18 (u v w x : V3) (hv : v ≠ u) (hw : w ≠ u)
    (hx : x ≠ u) (haff : x ∈ affGe {u} {v, w}) :
    arcV u v x + arcV u x w = arcV u v w := by
  sorry
  -- DISCHARGES: HOL ANGLES_ADD_AFF_GE (Harrison, fan geometry); the `arcV`
  -- rendering is Kepler.Geom.LuneVolume's (HOL sphere.hl:375).

/-- HOL `coplanar_delta_y_zero` (IUNBUIG.hl:144). -/
theorem coplanar_delta_y_zero_p18 (u₀ u₁ u₂ u₃ : V3) :
    Coplanar ({u₀, u₁, u₂, u₃} : Set V3) ↔
      deltaY_p18 (dist u₀ u₁) (dist u₀ u₂) (dist u₀ u₃) (dist u₂ u₃)
        (dist u₁ u₃) (dist u₁ u₂) = 0 := by
  sorry
  -- DISCHARGES: HOL Terminal.DELTA_Y_POS_4POINTS (delta_y > 0 off
  -- coplanarity) + Oxlzlez.coplanar_delta_y (coplanarity criterion).

/-- HOL `real_continuous_finite_range_constant` (IUNBUIG.hl:157): a real
function continuous on an open interval with finite range is constant
there. -/
theorem real_continuous_finite_range_constant_p18 (f : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (Set.Ioo a b)) (hf : (f '' Set.Ioo a b).Finite) :
    ∃ c, ∀ x ∈ Set.Ioo a b, f x = c := by
  rcases Set.eq_empty_or_nonempty (Set.Ioo a b) with hE | hE
  · refine ⟨0, fun x hx => absurd hx ?_⟩
    rw [hE]
    exact Set.notMem_empty x
  · obtain ⟨x, hx⟩ := hE
    have himg : f x ∈ f '' Set.Ioo a b := Set.mem_image_of_mem f hx
    have hord : (f '' Set.Ioo a b).OrdConnected :=
      isPreconnected_iff_ordConnected.mp ((isPreconnected_Ioo).image f hc)
    refine ⟨f x, fun y hy => ?_⟩
    have hyimg : f y ∈ f '' Set.Ioo a b := Set.mem_image_of_mem f hy
    by_contra hne
    rcases lt_trichotomy (f x) (f y) with hcase | hcase | hcase
    · have hinf : (Set.Icc (f x) (f y)).Infinite := Set.Icc_infinite hcase
      exact hf.not_infinite (Set.Infinite.mono (hord.out himg hyimg) hinf)
    · exact absurd hcase.symm hne
    · have hinf : (Set.Icc (f y) (f x)).Infinite := Set.Icc_infinite hcase
      exact hf.not_infinite (Set.Infinite.mono (hord.out hyimg himg) hinf)

/-- HOL `planar_deform_dist` (IUNBUIG.hl:191): a planar deformation
preserving the two dist constraints at `v₁`/`v₂` preserves their distance.
Giant (quadratic-root + `delta_quadratic` computation). -/
theorem planar_deform_dist_p18 (v₀ v₁ v₂ : V3) (f : V3 → ℝ → V3) (V : Set V3)
    (e' : ℝ) (h₁ : v₁ ∈ V) (h₂ : v₂ ∈ V) (hv₀ : v₀ ≠ 0) (he : 0 < e')
    (hdef : Deformation f V (-e') e')
    (hfix : ∀ v : V3, ∀ t : ℝ, v ≠ v₁ → v ≠ v₂ → f v t = v)
    (h : ∀ t, |t| < e' → Coplanar ({0, v₀, f v₁ t, f v₂ t} : Set V3) ∧
      dist v₀ (f v₁ t) = dist v₀ v₁ ∧ ‖f v₁ t‖ = ‖v₁‖ ∧
      dist (f v₂ t) v₀ = dist v₂ v₀ ∧ ‖f v₂ t‖ = ‖v₂‖) :
    ∀ t, |t| < e' → dist (f v₁ t) (f v₂ t) = dist v₁ v₂ := by
  sorry
  -- DISCHARGES: quadratic_at_most_2_roots_p18 (proved above) + the
  -- `delta_quadratic` identity (Nonlinear_lemma) on deltaY_p18 via
  -- coplanar_delta_y_zero_p18, plus the continuity clause of `Deformation`.

/-- HOL `deform_pent_exists` (IUNBUIG.hl:269). Giant (needs
`deform_684_pent_exists` / `deform_planar_exists` from Cuxvzoz). -/
theorem deform_pent_exists_p18 (V : Set V3) (g₂₃ : ℝ → ℝ) (v₀ v₁ v₂ v₃ : V3)
    (e : ℝ) (h₁ : v₁ ∈ V) (h₂ : v₂ ∈ V)
    (hcp : Coplanar ({0, v₀, v₁, v₂} : Set V3) →
      0 < (cross3 v₁ v₀) ⬝ᵥ (cross3 v₂ v₀))
    (hncp : ¬ Coplanar ({0, v₀, v₂, v₃} : Set V3))
    (hcol : ¬ Collinear3 0 v₁ v₂) (haz : azim 0 v₁ v₂ v₀ ≤ Real.pi)
    (hcr : 0 < v₂ ⬝ᵥ (cross3 v₃ v₀)) (he : 0 < e)
    (hcont : ContinuousOn g₂₃ (Set.Ioo (-e) e)) (hg₀ : g₂₃ 0 = 0) :
    ∃ f : V3 → ℝ → V3, ∃ e' > 0, Deformation f V (-e') e' ∧
      (∀ v : V3, ∀ t : ℝ, v ≠ v₁ → v ≠ v₂ → f v t = v) ∧
      (∀ t, |t| < e' → dist v₀ (f v₁ t) = dist v₀ v₁ ∧
        dist (f v₂ t) (f v₁ t) = dist v₂ v₁ ∧ ‖f v₁ t‖ = ‖v₁‖ ∧
        dist (f v₂ t) v₀ = dist v₂ v₀ ∧
        dist (f v₂ t) v₃ = dist v₂ v₃ + g₂₃ t ∧ ‖f v₂ t‖ = ‖v₂‖ ∧
        (Coplanar ({0, v₀, v₁, v₂} : Set V3) →
          Coplanar ({0, v₀, f v₁ t, f v₂ t} : Set V3))) := by
  sorry
  -- DISCHARGES: Cuxvzoz.deform_684_pent_exists / Cuxvzoz.deform_planar_exists
  -- plus planar_deform_dist_p18 for the coplanar branch.

/-- HOL `EGHNAVX_COLL_SCS` (IUNBUIG.hl:336), with `bta j = azim 0 (v p)
(v (p+1)) (v (p+j))` inlined. Giant. -/
theorem EGHNAVX_COLL_SCS_p18 (s : ScsV39) (k : ℕ) (v : ℕ → V3) (p : ℕ)
    (his : isScsV39 s) (hk : s.k = k) (hk₃ : 3 < k) (hBB : BBsV39 s v)
    (hbas : scsBasicV39 s)
    (hcol : ∀ i : ℕ, v i ≠ v p → ¬ Collinear3 0 (v p) (v i)) :
    azim 0 (v p) (v (p + 1)) (v (p + 1)) = 0 ∧
      azim 0 (v p) (v (p + 1)) (v (p + (k - 1))) ≤ Real.pi ∧
      (∀ i j, i < j → j < k → azim 0 (v p) (v (p + 1)) (v (p + i)) ≤
        azim 0 (v p) (v (p + 1)) (v (p + j))) ∧
      (∀ q j, azim 0 (v p) (v (p + 1)) (v (p + q)) = 0 → 0 < j → j ≤ q → q < k →
        ((j < q → azim 0 (v (p + j)) (v (p + j + 1)) (v (p + j + (k - 1))) = Real.pi) ∧
          v (p + j) ∈ affGt {0, v p} {v (p + 1)})) ∧
      (∀ q j, azim 0 (v p) (v (p + 1)) (v (p + q)) =
          azim 0 (v p) (v (p + 1)) (v (p + (k - 1))) → 0 < q → q < k - 1 →
          q ≤ j → j < k →
          ((q < j → azim 0 (v (p + j)) (v (p + j + 1)) (v (p + j + (k - 1))) = Real.pi) ∧
            v (p + j) ∈ affGt {0, v p} {v (p + (k - 1))})) := by
  sorry
  -- DISCHARGES: HOL Cuxvzoz.BBs_inj, Terminal.ITER_vv_rho_node1,
  -- Odxlstc.CARD_V_EQ_SCS_K1, Local_lemmas.EGHNAVX and
  -- Ocbicby.INTERIOR_ANGLE1_AZIM (the LocalAuto2-side kit).

/-- HOL `EGHNAVX_SCS` (IUNBUIG.hl:432): same conclusion from `scs_generic`.
Giant (reduces to EGHNAVX_COLL_SCS). -/
theorem EGHNAVX_SCS_p18 (s : ScsV39) (k : ℕ) (v : ℕ → V3) (p : ℕ)
    (his : isScsV39 s) (hk : s.k = k) (hk₃ : 3 < k) (hBB : BBsV39 s v)
    (hbas : scsBasicV39 s) (hgen : scsGeneric v) :
    azim 0 (v p) (v (p + 1)) (v (p + 1)) = 0 ∧
      azim 0 (v p) (v (p + 1)) (v (p + (k - 1))) ≤ Real.pi ∧
      (∀ i j, i < j → j < k → azim 0 (v p) (v (p + 1)) (v (p + i)) ≤
        azim 0 (v p) (v (p + 1)) (v (p + j))) ∧
      (∀ q j, azim 0 (v p) (v (p + 1)) (v (p + q)) = 0 → 0 < j → j ≤ q → q < k →
        ((j < q → azim 0 (v (p + j)) (v (p + j + 1)) (v (p + j + (k - 1))) = Real.pi) ∧
          v (p + j) ∈ affGt {0, v p} {v (p + 1)})) ∧
      (∀ q j, azim 0 (v p) (v (p + 1)) (v (p + q)) =
          azim 0 (v p) (v (p + 1)) (v (p + (k - 1))) → 0 < q → q < k - 1 →
          q ≤ j → j < k →
          ((q < j → azim 0 (v (p + j)) (v (p + j + 1)) (v (p + j + (k - 1))) = Real.pi) ∧
            v (p + j) ∈ affGt {0, v p} {v (p + (k - 1))})) := by
  sorry
  -- DISCHARGES: EGHNAVX_COLL_SCS_p18 once the generic-local-fan
  -- collinearity property (Nkezbfc_local.PROPERTIES_GENERIC_LOCAL_FAN,
  -- LocalAuto2 side) gives the `hcol` hypothesis from `scsGeneric`.

/-- HOL `coplanar_cross_reduction` (IUNBUIG.hl:477). Giant. -/
theorem coplanar_cross_reduction_p18 (s : ScsV39) (k : ℕ) (v : ℕ → V3) (i : ℕ)
    (his : isScsV39 s) (hk : s.k = k) (hk₃ : 3 < k) (hMM : v ∈ MMsV39 s)
    (hbas : scsBasicV39 s) (hgen : scsGeneric v)
    (hcp : Coplanar ({0, v i, v (i + 1), v (i + 2)} : Set V3)) :
    0 < (cross3 (v (i + 1)) (v i)) ⬝ᵥ (cross3 (v (i + 2)) (v i)) := by
  sorry
  -- DISCHARGES: EGHNAVX_SCS_p18 + FEKTYIY + COLL_AFF_GT_2_1 +
  -- AFFINE_HULL_3_GENERATED / periodic-image machinery (HOL proof
  -- IUNBUIG.hl:486-660).

/-- HOL `coplanar_aff_gt_simple` (IUNBUIG.hl:663). Giant. -/
theorem coplanar_aff_gt_simple_p18 (s : ScsV39) (k : ℕ) (v : ℕ → V3) (i : ℕ)
    (his : isScsV39 s) (hk : s.k = k) (hk₃ : 3 < k) (hMM : v ∈ MMsV39 s)
    (hbas : scsBasicV39 s)
    (hcol : ∀ j : ℕ, v j ≠ v i → ¬ Collinear3 0 (v i) (v j))
    (hcp : Coplanar ({0, v i, v (i + 1), v (i + 2)} : Set V3)) :
    v (i + 1) ∈ affGt {0} {v i, v (i + 2)} := by
  sorry
  -- DISCHARGES: EGHNAVX_COLL_SCS_p18 + FAN_IN_AFF_GE_IMP_EQ +
  -- fan_in_e_imp_neq + the affine-hull argument of HOL IUNBUIG.hl:672-906.

/-- Mod-reduction of a `Periodic` family (helper). -/
theorem periodic_mod_p18 {α : Sort*} {f : ℕ → α} {n : ℕ} (h : Periodic f n)
    (i : ℕ) : f (i % n) = f i := by
  have key : ∀ m i, f (i % n + n * m) = f (i % n) := by
    intro m
    induction m with
    | zero => intro i; rw [Nat.mul_zero, Nat.add_zero]
    | succ m ih =>
      intro i
      have he : i % n + n * (m + 1) = i % n + n * m + n := by ring
      rw [he, h]
      exact ih i
  have hfin := key (i / n) i
  rw [Nat.mod_add_div i n] at hfin
  exact hfin.symm

/-- Mod-reduction of a `Periodic2` family (helper). -/
theorem periodic2_mod_p18 {α : Sort*} {g : ℕ → ℕ → α} {n : ℕ}
    (h : Periodic2 g n) (i j : ℕ) : g (i % n) (j % n) = g i j := by
  have e1 : g (i % n) (j % n) = g i (j % n) :=
    periodic_mod_p18 (f := fun k => g k (j % n)) (fun k => (h k (j % n)).1) i
  have e2 : g i (j % n) = g i j :=
    periodic_mod_p18 (f := fun k => g i k) (fun k => (h i k).2) j
  rw [e1, e2]

/-- HOL `a5_assumption_reduction` (IUNBUIG.hl:909). Proved by the mod-5
case bash: cyclic edges (0,1) and (0,4) come from the deformation
hypotheses, (1,2), (2,3), (3,4) are rigid or fixed-point pairs, and the
five pentagon diagonals are vacuous by the strict `scs_diag` hypothesis. -/
theorem a5_assumption_reduction_p18 (s : ScsV39) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (his : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s v)
    (hdiag : ∀ i j, scsDiag 5 i j → s.a i j < dist (v i) (v j))
    (_hdef : Deformation f (Set.range v) (-e) e)
    (hfix : ∀ (w : V3) (t : ℝ), w ≠ v 4 → w ≠ v 0 → f w t = w)
    (h40 : ∃ d > 0, ∀ t : ℝ, |t| < d →
      dist (f (v 4) t) (f (v 0) t) = dist (v 4) (v 0) ∧
        dist (f (v 4) t) (v 3) = dist (v 4) (v 3))
    (h01 : ∃ d > 0, ∀ t : ℝ, |t| < d → s.a 0 1 ≤ dist (f (v 0) t) (v 1)) :
    ∀ i j : ℕ, ∃ d > 0, s.a i j = dist (v i) (v j) →
      ∀ t : ℝ, |t| < d → s.a i j ≤ dist (f (v i) t) (f (v j) t) := by
  obtain ⟨-, -, -, -, -, -, -, hp2a, -, -, -, -, hsym, -, hdiag0, hage, -, -, -, -, -⟩ :=
    his
  have hp2a5 : Periodic2 s.a 5 := by rw [← hk]; exact hp2a
  have hamod : ∀ i j, s.a (i % 5) (j % 5) = s.a i j := fun i j =>
    periodic2_mod_p18 hp2a5 i j
  have hasym : ∀ i j, s.a i j = s.a j i := fun i j => (hsym i j).1
  have hper : Periodic v 5 := by rw [← hk]; exact hBB.2.1
  have hvmod : ∀ i, v (i % 5) = v i := fun i => periodic_mod_p18 hper i
  have hage5 : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → 2 ≤ s.a i j := by
    intro i j hi hj hij
    exact hage i j ⟨by rw [hk]; omega, by rw [hk]; omega, hij⟩
  have hapos : ∀ i j : ℕ, i % 5 ≠ j % 5 → 0 < dist (v i) (v j) := by
    intro i j hij
    rw [← hvmod i, ← hvmod j]
    have h2 : 2 ≤ s.a (i % 5) (j % 5) :=
      hage5 (i % 5) (j % 5) (by omega) (by omega) hij
    have hle := (hBB.2.2.1 (i % 5) (j % 5)).1
    linarith
  have hne : ∀ i j : ℕ, i % 5 ≠ j % 5 → v i ≠ v j := by
    intro i j hij hveq
    have hd : dist (v i) (v j) = 0 := by rw [hveq, dist_self]
    have hbad := hapos i j hij
    rw [hd] at hbad
    exact absurd hbad (by norm_num)
  have hf1 : ∀ t, f (v 1) t = v 1 := fun t =>
    hfix (v 1) t (hne 1 4 (by norm_num)) (hne 1 0 (by norm_num))
  have hf2 : ∀ t, f (v 2) t = v 2 := fun t =>
    hfix (v 2) t (hne 2 4 (by norm_num)) (hne 2 0 (by norm_num))
  have hf3 : ∀ t, f (v 3) t = v 3 := fun t =>
    hfix (v 3) t (hne 3 4 (by norm_num)) (hne 3 0 (by norm_num))
  -- the unordered-pair case analysis (p ≤ q < 5, 10 non-diagonal pairs)
  have hd02 : scsDiag 5 0 2 := by
    show ¬(0 % 5 = 2 % 5) ∧ ¬((0 + 1) % 5 = 2 % 5) ∧ ¬(0 % 5 = (2 + 1) % 5)
    decide
  have hd03 : scsDiag 5 0 3 := by
    show ¬(0 % 5 = 3 % 5) ∧ ¬((0 + 1) % 5 = 3 % 5) ∧ ¬(0 % 5 = (3 + 1) % 5)
    decide
  have hd13 : scsDiag 5 1 3 := by
    show ¬(1 % 5 = 3 % 5) ∧ ¬((1 + 1) % 5 = 3 % 5) ∧ ¬(1 % 5 = (3 + 1) % 5)
    decide
  have hd14 : scsDiag 5 1 4 := by
    show ¬(1 % 5 = 4 % 5) ∧ ¬((1 + 1) % 5 = 4 % 5) ∧ ¬(1 % 5 = (4 + 1) % 5)
    decide
  have hd24 : scsDiag 5 2 4 := by
    show ¬(2 % 5 = 4 % 5) ∧ ¬((2 + 1) % 5 = 4 % 5) ∧ ¬(2 % 5 = (4 + 1) % 5)
    decide
  have aux : ∀ p q : ℕ, p < 5 → q < 5 → p ≤ q →
      ∃ d > 0, s.a p q = dist (v p) (v q) →
        ∀ t, |t| < d → s.a p q ≤ dist (f (v p) t) (f (v q) t) := by
    intro p q hp₅ hq₅ hpq
    rcases eq_or_lt_of_le hpq with hpq' | hpq'
    · subst hpq'
      exact ⟨1, one_pos, fun heq t _ => by simp [hdiag0 p]⟩
    have hqcyc : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 2 ∨ p = 2 ∧ q = 3 ∨ p = 3 ∧ q = 4 ∨
        p = 0 ∧ q = 4 ∨ p = 0 ∧ q = 2 ∨ p = 0 ∧ q = 3 ∨ p = 1 ∧ q = 3 ∨
        p = 1 ∧ q = 4 ∨ p = 2 ∧ q = 4 := by omega
    rcases hqcyc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
    · -- (0, 1)
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨d, hd, hdd⟩ := h01
      exact ⟨d, hd, fun _ t ht => by rw [hf1]; exact hdd t ht⟩
    · -- (1, 2)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by rw [heq, hf1, hf2]⟩
    · -- (2, 3)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by rw [heq, hf2, hf3]⟩
    · -- (3, 4)
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨d, hd, hdd⟩ := h40
      exact ⟨d, hd, fun heq t ht => by
        rw [heq, hf3, dist_comm (v 3) (f (v 4) t), (hdd t ht).2,
          dist_comm (v 3) (v 4)]⟩
    · -- (0, 4)
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨d, hd, hdd⟩ := h40
      exact ⟨d, hd, fun heq t ht => by
        rw [heq, dist_comm (v 0) (v 4), dist_comm (f (v 0) t) (f (v 4) t),
          (hdd t ht).1]⟩
    · -- (0, 2)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq _ _ => absurd heq.symm ((hdiag 0 2 hd02).ne')⟩
    · -- (0, 3)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq _ _ => absurd heq.symm ((hdiag 0 3 hd03).ne')⟩
    · -- (1, 3)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq _ _ => absurd heq.symm ((hdiag 1 3 hd13).ne')⟩
    · -- (1, 4)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq _ _ => absurd heq.symm ((hdiag 1 4 hd14).ne')⟩
    · -- (2, 4)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq _ _ => absurd heq.symm ((hdiag 2 4 hd24).ne')⟩
  -- assemble for arbitrary indices
  intro i j
  rcases le_or_gt (i % 5) (j % 5) with hle | hgt
  · obtain ⟨d, hd, hdd⟩ := aux (i % 5) (j % 5) (by omega) (by omega) hle
    refine ⟨d, hd, fun heq t ht => ?_⟩
    have heq' : s.a (i % 5) (j % 5) = dist (v (i % 5)) (v (j % 5)) := by
      rw [hamod i j, hvmod i, hvmod j]
      exact heq
    rw [← hamod i j, ← hvmod i, ← hvmod j]
    exact hdd heq' t ht
  · obtain ⟨d, hd, hdd⟩ := aux (j % 5) (i % 5) (by omega) (by omega) (le_of_lt hgt)
    refine ⟨d, hd, fun heq t ht => ?_⟩
    have heq' : s.a (j % 5) (i % 5) = dist (v (j % 5)) (v (i % 5)) := by
      rw [hamod j i, hasym j i, hvmod j, hvmod i, dist_comm (v j) (v i)]
      exact heq
    have hres := hdd heq' t ht
    rw [hasym (j % 5) (i % 5), dist_comm (f (v (j % 5)) t) (f (v (i % 5)) t)] at hres
    rw [← hamod i j, ← hvmod i, ← hvmod j]
    exact hres

/-- HOL `b5_assumption_reduction` (IUNBUIG.hl:990). Same mod-5 bash as
`a5_assumption_reduction_p18`; the pentagon diagonals are vacuous by the
strict `4 * h0 < b` hypothesis against the `ball_annulus` diameter bound. -/
theorem b5_assumption_reduction_p18 (s : ScsV39) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (his : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s v)
    (hbdiag : ∀ i j, scsDiag 5 i j → 4 * h0 < s.b i j)
    (_hdef : Deformation f (Set.range v) (-e) e)
    (hfix : ∀ (w : V3) (t : ℝ), w ≠ v 4 → w ≠ v 0 → f w t = w)
    (h40 : ∃ d > 0, ∀ t : ℝ, |t| < d →
      dist (f (v 4) t) (f (v 0) t) = dist (v 4) (v 0) ∧
        dist (f (v 4) t) (v 3) = dist (v 4) (v 3))
    (h01 : ∃ d > 0, ∀ t : ℝ, |t| < d →
      dist (f (v 0) t) (v 1) ≤ dist (v 0) (v 1)) :
    ∀ i j : ℕ, ∃ d > 0, dist (v i) (v j) = s.b i j →
      ∀ t : ℝ, |t| < d → dist (f (v i) t) (f (v j) t) ≤ s.b i j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hp2b, -, hsym, -, -, hage, -, -, -, -, -⟩ :=
    his
  have hp2b5 : Periodic2 s.b 5 := by rw [← hk]; exact hp2b
  have hbmod : ∀ i j, s.b (i % 5) (j % 5) = s.b i j := fun i j =>
    periodic2_mod_p18 hp2b5 i j
  have hbsym : ∀ i j, s.b i j = s.b j i := fun i j => (hsym i j).2.2.2.1
  have hper : Periodic v 5 := by rw [← hk]; exact hBB.2.1
  have hvmod : ∀ i, v (i % 5) = v i := fun i => periodic_mod_p18 hper i
  have hbdiam : ∀ i j : ℕ, dist (v i) (v j) ≤ 4 * h0 := by
    intro i j
    have hi : v i ∈ ballAnnulus := hBB.1 (Set.mem_range_self i)
    have hj : v j ∈ ballAnnulus := hBB.1 (Set.mem_range_self j)
    have hb1 := (ballAnnulus_norm_bounds hi).2
    have hb2 := (ballAnnulus_norm_bounds hj).2
    have htri : dist (v i) (v j) ≤ ‖v i‖ + ‖v j‖ := by
      simpa using dist_triangle (v i) 0 (v j)
    linarith
  have hapos : ∀ i j : ℕ, i % 5 ≠ j % 5 → 0 < dist (v i) (v j) := by
    intro i j hij
    rw [← hvmod i, ← hvmod j]
    have h2 : 2 ≤ s.a (i % 5) (j % 5) :=
      hage (i % 5) (j % 5) ⟨by rw [hk]; omega, by rw [hk]; omega, hij⟩
    have hle := (hBB.2.2.1 (i % 5) (j % 5)).1
    linarith
  have hne : ∀ i j : ℕ, i % 5 ≠ j % 5 → v i ≠ v j := by
    intro i j hij hveq
    have hd : dist (v i) (v j) = 0 := by rw [hveq, dist_self]
    have hbad := hapos i j hij
    rw [hd] at hbad
    exact absurd hbad (by norm_num)
  have hf1 : ∀ t, f (v 1) t = v 1 := fun t =>
    hfix (v 1) t (hne 1 4 (by norm_num)) (hne 1 0 (by norm_num))
  have hf2 : ∀ t, f (v 2) t = v 2 := fun t =>
    hfix (v 2) t (hne 2 4 (by norm_num)) (hne 2 0 (by norm_num))
  have hf3 : ∀ t, f (v 3) t = v 3 := fun t =>
    hfix (v 3) t (hne 3 4 (by norm_num)) (hne 3 0 (by norm_num))
  have aux : ∀ p q : ℕ, p < 5 → q < 5 → p ≤ q →
      ∃ d > 0, dist (v p) (v q) = s.b p q →
        ∀ t, |t| < d → dist (f (v p) t) (f (v q) t) ≤ s.b p q := by
    intro p q hp₅ hq₅ hpq
    have hd02 : scsDiag 5 0 2 := by
      show ¬(0 % 5 = 2 % 5) ∧ ¬((0 + 1) % 5 = 2 % 5) ∧ ¬(0 % 5 = (2 + 1) % 5)
      decide
    have hd03 : scsDiag 5 0 3 := by
      show ¬(0 % 5 = 3 % 5) ∧ ¬((0 + 1) % 5 = 3 % 5) ∧ ¬(0 % 5 = (3 + 1) % 5)
      decide
    have hd13 : scsDiag 5 1 3 := by
      show ¬(1 % 5 = 3 % 5) ∧ ¬((1 + 1) % 5 = 3 % 5) ∧ ¬(1 % 5 = (3 + 1) % 5)
      decide
    have hd14 : scsDiag 5 1 4 := by
      show ¬(1 % 5 = 4 % 5) ∧ ¬((1 + 1) % 5 = 4 % 5) ∧ ¬(1 % 5 = (4 + 1) % 5)
      decide
    have hd24 : scsDiag 5 2 4 := by
      show ¬(2 % 5 = 4 % 5) ∧ ¬((2 + 1) % 5 = 4 % 5) ∧ ¬(2 % 5 = (4 + 1) % 5)
      decide
    rcases eq_or_lt_of_le hpq with hpq' | hpq'
    · subst hpq'
      exact ⟨1, one_pos, fun heq t _ => by
        rw [dist_self]
        exact heq ▸ dist_nonneg⟩
    have hqcyc : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 2 ∨ p = 2 ∧ q = 3 ∨ p = 3 ∧ q = 4 ∨
        p = 0 ∧ q = 4 ∨ p = 0 ∧ q = 2 ∨ p = 0 ∧ q = 3 ∨ p = 1 ∧ q = 3 ∨
        p = 1 ∧ q = 4 ∨ p = 2 ∧ q = 4 := by omega
    rcases hqcyc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
    · -- (0, 1)
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨d, hd, hdd⟩ := h01
      exact ⟨d, hd, fun heq t ht => by rw [hf1]; exact le_trans (hdd t ht) (le_of_eq heq)⟩
    · -- (1, 2)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by rw [← heq, hf1, hf2]⟩
    · -- (2, 3)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by rw [← heq, hf2, hf3]⟩
    · -- (3, 4)
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨d, hd, hdd⟩ := h40
      exact ⟨d, hd, fun heq t ht => by
        rw [← heq, hf3, dist_comm (v 3) (f (v 4) t), (hdd t ht).2,
          dist_comm (v 3) (v 4)]⟩
    · -- (0, 4)
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨d, hd, hdd⟩ := h40
      exact ⟨d, hd, fun heq t ht => by
        rw [← heq, dist_comm (f (v 0) t) (f (v 4) t), (hdd t ht).1,
          dist_comm (v 0) (v 4)]⟩
    · -- (0, 2)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by
        have hle := hbdiam 0 2
        have hlt := hbdiag 0 2 hd02
        rw [heq] at hle
        linarith⟩
    · -- (0, 3)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by
        have hle := hbdiam 0 3
        have hlt := hbdiag 0 3 hd03
        rw [heq] at hle
        linarith⟩
    · -- (1, 3)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by
        have hle := hbdiam 1 3
        have hlt := hbdiag 1 3 hd13
        rw [heq] at hle
        linarith⟩
    · -- (1, 4)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by
        have hle := hbdiam 1 4
        have hlt := hbdiag 1 4 hd14
        rw [heq] at hle
        linarith⟩
    · -- (2, 4)
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨1, one_pos, fun heq t _ => by
        have hle := hbdiam 2 4
        have hlt := hbdiag 2 4 hd24
        rw [heq] at hle
        linarith⟩
  intro i j
  rcases le_or_gt (i % 5) (j % 5) with hle | hgt
  · obtain ⟨d, hd, hdd⟩ := aux (i % 5) (j % 5) (by omega) (by omega) hle
    refine ⟨d, hd, fun heq t ht => ?_⟩
    have heq' : dist (v (i % 5)) (v (j % 5)) = s.b (i % 5) (j % 5) := by
      rw [hvmod i, hvmod j, hbmod i j]
      exact heq
    rw [← hbmod i j, ← hvmod i, ← hvmod j]
    exact hdd heq' t ht
  · obtain ⟨d, hd, hdd⟩ := aux (j % 5) (i % 5) (by omega) (by omega) (le_of_lt hgt)
    refine ⟨d, hd, fun heq t ht => ?_⟩
    have heq' : dist (v (j % 5)) (v (i % 5)) = s.b (j % 5) (i % 5) := by
      rw [hvmod j, hvmod i, dist_comm (v j) (v i), hbmod j i, hbsym j i]
      exact heq
    have hres := hdd heq' t ht
    rw [hbsym (j % 5) (i % 5), dist_comm (f (v (j % 5)) t) (f (v (i % 5)) t)] at hres
    rw [← hbmod i j, ← hvmod i, ← hvmod j]
    exact hres

/-- HOL `azim_dih_y` (IUNBUIG.hl:1088, was `dihV_dih_y`). Giant (needs
AZIM_DIHV_SAME_STRONG + DIHV_DIH_X + the `ups_x`-positivity kit). -/
theorem azim_dih_y_p18 (v₀ v₁ v₂ v₃ : V3)
    (h₂ : ¬ Collinear3 v₀ v₁ v₂) (h₃ : ¬ Collinear3 v₀ v₁ v₃)
    (hpi : azim v₀ v₁ v₂ v₃ ≤ Real.pi) :
    azim v₀ v₁ v₂ v₃ = dihY_p18 (dist v₀ v₁) (dist v₀ v₂) (dist v₀ v₃)
      (dist v₂ v₃) (dist v₁ v₃) (dist v₁ v₂) := by
  sorry
  -- DISCHARGES: HOL AZIM_DIHV_SAME_STRONG (LocalAuto2-side azimuth kit),
  -- Merge_ineq.DIHV_DIH_X and Collect_geom2.NOT_COL_EQ_UPS_X_POS
  -- (`upsX`-positivity off the non-collinearity hypotheses).

/-- HOL `azim5_reduction` (IUNBUIG.hl:1106). Monster statement + giant. -/
theorem azim5_reduction_p18 (s : ScsV39) (f : V3 → ℝ → V3) (v : ℕ → V3)
    (e : ℝ) (his : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s v)
    (hgen : scsGeneric v) (hdef : Deformation f (Set.range v) (-e) e)
    (hfix : ∀ (w : V3) (t : ℝ), w ≠ v 4 → w ≠ v 0 → f w t = w)
    (ha04 : azim 0 (v 0) (v 1) (v 4) < Real.pi)
    (ha10 : azim 0 (v 1) (v 2) (v 0) < Real.pi)
    (ha03 : 0 < azim 0 (v 0) (v 1) (v 3))
    (he1a : ∃ d > 0, ∀ t, |t| < d →
      azim 0 (v 3) (f (v 0) t) (v 1) ≤ azim 0 (v 3) (v 0) (v 1))
    (he1b : ∃ d > 0, ∀ t, |t| < d →
      dist (v 3) (f (v 4) t) = dist (v 3) (v 4) ∧
      dist (f (v 0) t) (f (v 4) t) = dist (v 0) (v 4) ∧
      ‖f (v 4) t‖ = ‖v 4‖ ∧
      dist (f (v 0) t) (v 3) = dist (v 0) (v 3) ∧
      dist (f (v 0) t) (v 1) = dist (v 0) (v 1) - |t| ∧
      ‖f (v 0) t‖ = ‖v 0‖ ∧
      (Coplanar ({0, v 3, v 4, v 0} : Set V3) →
        Coplanar ({0, v 3, f (v 4) t, f (v 0) t} : Set V3))) :
    azim 0 (v 3) (v 4) (v 2) =
        azim 0 (v 3) (v 4) (v 0) + azim 0 (v 3) (v 0) (v 1) +
          azim 0 (v 3) (v 1) (v 2) ∧
      azim 0 (v 0) (v 1) (v 4) =
        azim 0 (v 0) (v 1) (v 3) + azim 0 (v 0) (v 3) (v 4) ∧
      azim 0 (v 1) (v 2) (v 0) =
        azim 0 (v 1) (v 2) (v 3) + azim 0 (v 1) (v 3) (v 0) ∧
      (∃ d > 0, ∀ t, |t| < d →
        azim 0 (v 3) (f (v 4) t) (v 2) =
          azim 0 (v 3) (f (v 4) t) (f (v 0) t) +
            azim 0 (v 3) (f (v 0) t) (v 1) + azim 0 (v 3) (v 1) (v 2) ∧
        azim 0 (f (v 0) t) (v 1) (f (v 4) t) =
          azim 0 (f (v 0) t) (v 1) (v 3) +
            azim 0 (f (v 0) t) (v 3) (f (v 4) t) ∧
        azim 0 (v 1) (v 2) (f (v 0) t) =
          azim 0 (v 1) (v 2) (v 3) + azim 0 (v 1) (v 3) (f (v 0) t) ∧
        0 < azim 0 (f (v 0) t) (v 1) (v 3) ∧
        azim 0 (f (v 0) t) (v 1) (v 3) < Real.pi) ∧
      (∀ i : ℕ, ∃ d₀ > 0, azim 0 (v i) (v (i + 1)) (v (i + 4)) = Real.pi →
        ∀ t, |t| < d₀ →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + 4)) t) ≤ Real.pi) ∧
      (∃ d > 0, ∀ t, |t| < d →
        azim 0 (v 3) (f (v 4) t) (f (v 0) t) = azim 0 (v 3) (v 4) (v 0) ∧
        azim 0 (f (v 4) t) (f (v 0) t) (v 3) = azim 0 (v 4) (v 0) (v 3) ∧
        azim 0 (f (v 0) t) (v 3) (f (v 4) t) = azim 0 (v 0) (v 3) (v 4)) := by
  sorry
  -- DISCHARGES: Terminal.vv_split_azim_generic (the three "addition"
  -- conjuncts), the colinearity kit (Zlzthic.PROPERTIES_GENERIC_LOCAL_FAN_ALT)
  -- and the deformation-invariance of `azim` under the he1b constraints.

/-- HOL `L13_LEMMA` (IUNBUIG.hl:1454). -/
theorem L13_LEMMA_p18 (h : mainNonlinearTerminalV11_p18) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (s : ScsV39) (v : ℕ → V3)
    (hFF : (Set.range fun i => (v i, v (i + 1))) = FF) (his : isScsV39 s)
    (hk : s.k = 5) (hbas : scsBasicV39 s) (hgen : scsGeneric v)
    (hBB : BBsV39 s v) (hV : Set.range v = V)
    (hE : (Set.range fun i => {v i, v (i + 1)}) = E)
    (hcp : ¬ Coplanar ({0, v 1, v 2, v 0} : Set V3)) :
    0 < azim 0 (v 0) (v 1) (v 3) := by
  sorry
  -- DISCHARGES: Counting_spheres.AZIM_NN (azim nonnegativity) +
  -- EGHNAVX_SCS_p18 with `bta q = 0` at q = 0 giving `v 2 ∈ aff_gt`,
  -- hence coplanarity — contradicting `hcp` unless the azimuth is
  -- positive.

/-- HOL `IUNBUIG` (IUNBUIG.hl:1496): the main estimate for the 5-cycle.
Giant. -/
theorem IUNBUIG_p18 (h : mainNonlinearTerminalV11_p18) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3)
    (hFF : (Set.range fun i => (v i, v (i + 1))) = FF) (his : isScsV39 s)
    (hk : s.k = 5) (hMM : v ∈ MMsV39 s) (hbas : scsBasicV39 s)
    (hgen : scsGeneric v)
    (hdiag : ∀ i j, scsDiag 5 i j →
      s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (ha01 : s.a 0 1 = 2) (hb01 : s.b 0 1 ≤ cstab)
    (hia0 : interiorAngle1 0 FF (v 0) < Real.pi)
    (hia1 : interiorAngle1 0 FF (v 1) < Real.pi)
    (hdist : ∀ i, i % 5 ≠ 0 → dist (v i) (v (i + 1)) = 2)
    (hxrr1 : xrr ‖v 0‖ ‖v 3‖ (dist (v 0) (v 3)) ≤ 15.53)
    (hxrr2 : xrr ‖v 1‖ ‖v 3‖ (dist (v 1) (v 3)) ≤ 15.53) :
    dist (v 0) (v 1) = 2 := by
  sorry
  -- DISCHARGES: the full main-estimate chain (BBprime/BBs transport,
  -- LOCAL_FAN_AZIM_POS, deform_pent_exists_p18, a5/b5 reductions,
  -- azim5_reduction_p18, the `xrr` monotone LP bounds and L13_LEMMA_p18).

/-! ## Section C: AURSIPD (Aursipd.hl) -/

/-- HOL `REP_NUMSEG` (AURSIPD.hl:94); HOL `0..(k-1)` ↔ `Finset.range k`. -/
theorem REP_NUMSEG_p18 (k : ℕ) (_hk : k ≠ 0) :
    {i : ℕ | i < k} = Finset.range k := by
  ext i
  simp [Finset.mem_range]

/-- HOL `SUM_AZIM_EQ_ANGLE_LE4_FUN` (AURSIPD.hl:100). Giant; `ff` is
carried as an explicit parameter (its HOL home was not locatable in the
corpus). -/
theorem SUM_AZIM_EQ_ANGLE_LE4_FUN_p18 (ff : V3 → ℝ) (s : ScsV39)
    (vv : ℕ → V3) (p : ℕ) (u : V3) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (hk : ¬s.k ≤ 3) (hBB : BBsV39 s vv)
    (his : isScsV39 s) (hu : vv (p % s.k) = u) (hV : Set.range vv = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)}) = E)
    (hFF : (Set.range fun i => (vv i, vv (i + 1))) = FF) :
    setSum {i | i < s.k}
        (fun i => ff (vv (i + p % s.k)) *
          interiorAngle1 0 FF ((rhoNode1_p18 FF)^[i] u)) =
      setSum FF (fun e => ff e.1 * azimInFan_p18 e E) := by
  sorry
  -- DISCHARGES: SUM_EQ_GENERAL + the periodicity/injectivity transport of
  -- HOL AURSIPD.hl:114-197 (PERIODIC_PROPERTY, VV_SUC_EQ_RHO_NODE_PRIME,
  -- CONVEX_LOFA_IMP_INANGLE_EQ_AZIM — LocalAuto2-side kit).

/-- HOL `PERIODIC_IMAGE2` (AURSIPD.hl:202). -/
theorem PERIODIC_IMAGE2_p18 {α : Type*} {f : ℕ → α} {n : ℕ} (hn : n ≠ 0)
    (hper : Periodic f n) : (f '' {i | i < n}) = Set.range f := by
  refine Set.ext fun y => ?_
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    have hx : x % n < n := Nat.mod_lt x (by omega)
    exact ⟨x % n, hx, by rw [periodic_mod_p18 hper x]⟩

/-- HOL `AURSIPD` (AURSIPD.hl:218): the stratum-count bound. Giant. -/
theorem AURSIPD_p18 : ∀ (s : ScsV39) (v : ℕ → V3),
    3 < s.k → isScsV39 s → scsGeneric v → v ∈ MMsV39 s →
    3 + {i : ℕ | i < s.k ∧ scsIsStr s v i}.ncard ≤ s.k := by
  sorry
  -- DISCHARGES: the stratum is `{i | azim ... = pi}`; the bound comes from
  -- CARD_SUBSET over `0..k-1` plus the scs diagonal-count budget
  -- (isScsV39's final conjunct) in HOL AURSIPD.hl:218-1850.

/-! ## Section D: CNICGSF (Cnicgsf.hl) -/

/-- HOL `SCS_DIAG_SCS_5I1_02` (CNICGSF.hl:78). -/
theorem SCS_DIAG_SCS_5I1_02_p18 : scsDiag scs5I1.k 0 2 := by
  have hk : scs5I1.k = 5 := rfl
  rw [hk]
  show ¬(0 % 5 = 2 % 5) ∧ ¬((0 + 1) % 5 = 2 % 5) ∧ ¬(0 % 5 = (2 + 1) % 5)
  decide

/-- HOL `SCS_DIAG_SCS_5I2_02` (CNICGSF.hl:231). -/
theorem SCS_DIAG_SCS_5I2_02_p18 : scsDiag scs5I2.k 0 2 := by
  have hk : scs5I2.k = 5 := rfl
  rw [hk]
  show ¬(0 % 5 = 2 % 5) ∧ ¬((0 + 1) % 5 = 2 % 5) ∧ ¬(0 % 5 = (2 + 1) % 5)
  decide

/-- HOL `SCS_DIAG_SCS_5M1_02` (CNICGSF.hl:387). -/
theorem SCS_DIAG_SCS_5M1_02_p18 : scsDiag scs5M1.k 0 2 := by
  have hk : scs5M1.k = 5 := rfl
  rw [hk]
  show ¬(0 % 5 = 2 % 5) ∧ ¬((0 + 1) % 5 = 2 % 5) ∧ ¬(0 % 5 = (2 + 1) % 5)
  decide

/-- HOL `SCS_DIAG_SCS_5M1_03` (CNICGSF.hl:391). -/
theorem SCS_DIAG_SCS_5M1_03_p18 : scsDiag scs5M1.k 0 3 := by
  have hk : scs5M1.k = 5 := rfl
  rw [hk]
  show ¬(0 % 5 = 3 % 5) ∧ ¬((0 + 1) % 5 = 3 % 5) ∧ ¬(0 % 5 = (3 + 1) % 5)
  decide

/-- HOL `SCS_DIAG_SCS_5M1_24` (CNICGSF.hl:395). -/
theorem SCS_DIAG_SCS_5M1_24_p18 : scsDiag scs5M1.k 2 4 := by
  have hk : scs5M1.k = 5 := rfl
  rw [hk]
  show ¬(2 % 5 = 4 % 5) ∧ ¬((2 + 1) % 5 = 4 % 5) ∧ ¬(2 % 5 = (4 + 1) % 5)
  decide

/-- HOL `SCS_5I1_SLICE_02` (CNICGSF.hl:86). Giant (`LKGRQUI` lane). -/
theorem SCS_5I1_SLICE_02_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M2 1} := by
  sorry
  -- DISCHARGES: LKGRQUI + STAB_5I1_SCS + the is_scs_slice_v39 computation
  -- for (p,q) = (0,2), including the PSORT/FUNLIST normalisation of
  -- scs_half_slice_v39 against scs_3M1/scs_4M2 (HOL CNICGSF.hl:86-204).

/-- HOL `SCS_5I2_SLICE_02` (CNICGSF.hl:237). Giant. -/
theorem SCS_5I2_SLICE_02_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2}
      {scsPropEquV39 scs3T1 1, scsPropEquV39 scs4M3' 1} := by
  sorry
  -- DISCHARGES: LKGRQUI + STAB_5I2_SCS + the (0,2)-slice computation
  -- against scs_3T1/scs_4M3' (HOL CNICGSF.hl:237-358).

/-- HOL `SCS_5M1_SLICE_02` (CNICGSF.hl:400). Giant. -/
theorem SCS_5M1_SLICE_02_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2}
      {scsPropEquV39 scs3T4 2, scsPropEquV39 scs4M2 1} := by
  sorry
  -- DISCHARGES: LKGRQUI + STAB_5M1_SCS + the (0,2)-slice computation
  -- against scs_3T4/scs_4M2 (HOL CNICGSF.hl:400-525).

/-- HOL `SCS_5M1_SLICE_03` (CNICGSF.hl:552). Giant. -/
theorem SCS_5M1_SLICE_03_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3}
      {scsPropEquV39 scs4M4' 1, scsPropEquV39 scs3M1 1} := by
  sorry
  -- DISCHARGES: LKGRQUI + STAB_5M1_SCS + the (0,3)-slice computation
  -- against scs_4M4'/scs_3M1 (HOL CNICGSF.hl:552-694).

/-- HOL `SCS_5M1_SLICE_24` (CNICGSF.hl:729). Giant. -/
theorem SCS_5M1_SLICE_24_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M5' 1} := by
  sorry
  -- DISCHARGES: LKGRQUI + STAB_5M1_SCS + the (2,4)-slice computation
  -- against scs_3M1/scs_4M5' (HOL CNICGSF.hl:729-874).

/-- HOL `CNICGSF1` (CNICGSF.hl:207). -/
theorem CNICGSF1_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs3M1, scs4M2} := by
  sorry
  -- DISCHARGES: SCS_5I1_SLICE_02_p18 + FZIOTEF_TRANS/FZIOTEF_UNION +
  -- PRO_EQU_ID1 (MMsV39 ∘ scsPropEquV39 = MMsV39) + YXIONXL3 +
  -- SCS_3M1_IS_SCS/SCS_4M2_IS_SCS.

/-- HOL `CNICGSF2` (CNICGSF.hl:361). -/
theorem CNICGSF2_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs3T1, scs4M3'} := by
  sorry
  -- DISCHARGES: SCS_5I2_SLICE_02_p18 + the PRO_EQU_ID1/YXIONXL3 kit with
  -- SCS_3T1_IS_SCS/SCS_4M3_IS_SCS.

/-- HOL `CNICGSF3` (CNICGSF.hl:527). -/
theorem CNICGSF3_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs3T4, scs4M2} := by
  sorry
  -- DISCHARGES: SCS_5M1_SLICE_02_p18 + the PRO_EQU_ID1/YXIONXL3 kit with
  -- SCS_3T4_IS_SCS/SCS_4M2_IS_SCS.

/-- HOL `CNICGSF4` (CNICGSF.hl:696). -/
theorem CNICGSF4_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1} := by
  sorry
  -- DISCHARGES: SCS_5M1_SLICE_03_p18 + the PRO_EQU_ID1/YXIONXL3 kit with
  -- SCS_4M4_IS_SCS/SCS_3M1_IS_SCS.

/-- HOL `CNICGSF5` (CNICGSF.hl:876). -/
theorem CNICGSF5_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs3M1, scs4M5'} := by
  sorry
  -- DISCHARGES: SCS_5M1_SLICE_24_p18 + the PRO_EQU_ID1/YXIONXL3 kit with
  -- SCS_3M1_IS_SCS/SCS_4M5_IS_SCS.

end Kepler.Text

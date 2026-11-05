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
  Section 0 (verbatim `_p18` copies; see ENCODING): `EE_p18`,
    `azimCycle_p18`, `rhoNode1_p18`, `azimInFan_p18`, `torsor_p18`,
    `constraintSystem_p18`, `stableSystem_p18`, `rowV3_p18`,
    `CONDITION2_SY_p18`, `BSY1body_p18`.  DEDUP 2026-09-17: the
    sphere-kit copies `deltaX4`/`deltaY`/`dihY` were
    deleted against `Kepler.Text.SphereKit` (bodies verified
    identical; the inlined `dihY` twin included).
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
    `SUM_AZIM_EQ_ANGLE_LE4_FUN_p18` (proved 2026-11-05, la18-sumazim kit),
    `AURSIPD_p18` (proved 2026-11-05, la18-aursipd kit).
  Section D (CNICGSF): the five `SCS_DIAG_*_p18` (proved, decidable);
    the five slice arrows `SCS_*_SLICE_*_p18` (discharged 2026-11-01 as `LKGRQUI_p27` instances; see the la18slice kit);
    the in-file rotation kit `funlistV39_add_period_p18` /
    `funlistV39_add_mul_period_p18` / `propEqu_propEqu_mkUnadorned_p18` /
    `scsArrowV39_pair_union_p18` / `scsArrowV39_lift_p18`; `CNICGSF1..5_p18`
    (proved 2026-09-21 from the slice arrows + the importable
    `LocalAuto1.YXIONXL3_concl`; no `PRO_EQU_ID1`/`FZIOTEF_UNION` import
    needed — the rotation identity is re-derived in-file).

ENCODING NOTES
  - Import discipline: this file sits on the LocalAuto1/`PackingAuto18`
    side of the fatal `atn2` duplication — LocalAuto2/`PackingAuto20`
    (also LocalAuto9/LocalAuto11, which import LocalAuto2) must NOT be
    imported next to LocalAuto1. DEDUP 2026-09-17: the sphere-kit trio
    (the `deltaX4`/`deltaY`/`dihY` twins of PackingAuto20:80-92 /
    LocalAuto11:129-151) is deleted against `Kepler.Text.SphereKit`;
    everything else needed from the other lanes is still carried as a
    verbatim `_p18` copy with a NEEDS merge marker:
    `EE_p18`/`azimCycle_p18`/`rhoNode1_p18`/
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
import Kepler.Text.SphereKit
import Kepler.Text.ClosedSyKit
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto27
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: verbatim `_p18` copies (atn2 two-sides clash)

-- DEDUP 2026-09-17: the sphere-kit trio that used to open this section
-- (`deltaX4`/`deltaY`/`dihY` `_p18` twins; `dihY` carried the inlined
-- `dih_x`-at-squares formula) is deleted against the canonical
-- `Kepler.Text.SphereKit` definitions — every body was verified
-- identical.  Remaining uses resolve through the SphereKit import.
-- The localization.hl / dih2k.hl `_p18` copies below stay until their
-- rendering bridge lands (plan §6). -/

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
    (_hsys : stableSystem_p18 k d s a b J f) (_hs : s = Finset.Iic (k - 1))
    (_hf : f = fun j => (1 + j) % k) (_hk1 : 1 < k) (_hk2 : 2 < k) :
    IsClosed (SYset_p18 k a b) := by
  -- bodyclosed-w2b: the statement is a verbatim twin of `CLOSED_SY_cs`
  -- (Kepler.Text.ClosedSyKit); the verbatim twin defs make this redirect
  -- definitional, with zero new proof debt: the giant obligation is now
  -- rooted at `CLOSED_SY_cs` alone.
  exact CLOSED_SY_cs (d := d) _hsys _hs _hf _hk1 _hk2
  -- DISCHARGES (history of the former local gap): the
  -- `BSY1body_p18` factor is closed exactly as in LocalAuto9's
  -- `CLOSED_TRI_SY_p9` (proved there; blocked here only by that theorem's
  -- `triStable_p9` hypothesis, so the intersection argument must be redone
  -- locally); the `CONDITION2_SY_p18` factor needs the limit argument on
  -- `V_SY`/`E_SY`/`F_SY` (HOL: CLOSED_SY's SKOLEM/sequential-lims part).
  -- The obligation now lives at `CLOSED_SY_cs` (W3–W7 bodyclosed waves).

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
    (hsys : stableSystem_p18 k d s a b J f) (hs : s = Finset.Iic (k - 1))
    (hf : f = fun j => (1 + j) % k) (hk1 : 1 < k) (hk2 : 2 < k) :
    IsCompact (SYset_p18 k a b) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨CLOSED_SY_p18 hsys hs hf hk1 hk2, BOUNDED_SY_p18⟩

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
      deltaY (dist u₀ u₁) (dist u₀ u₂) (dist u₀ u₃) (dist u₂ u₃)
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
  -- `delta_quadratic` identity (Nonlinear_lemma) on deltaY via
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

/-- In-plane azimuth dichotomy (HOL `AZIM_COND_FOR_COPLANAR` consumption
shape): a point of the linear plane through `0`, `a`, `b` sits at azimuth
`0` or `π`. Adapted from the `lkgrqui-sectortri-asm-w3` kit item. -/
private theorem w4sg_azim_plane_p18 {a b x : V3} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hnc : ¬ Collinear3 0 a b) (hx : ∃ s t : ℝ, x - 0 = s • (a - 0) + t • (b - 0)) :
    azim 0 a b x = 0 ∨ azim 0 a b x = Real.pi := by
  obtain ⟨s, t, hx'⟩ := hx
  by_cases hcolx : Collinear3 0 a x
  · exact Or.inl (by rw [azim, if_pos (Or.inr hcolx)])
  rcases lt_trichotomy t 0 with ht0 | ht00 | ht1
  · -- negative side: azimuth π (frame computation)
    have hge : (0:ℝ) ≤ azim 0 a b x := azim_nonneg 0 a b x
    have hlt : azim 0 a b x < 2 * Real.pi := azim_lt_two_pi 0 a b x
    obtain ⟨e1, e2, e3, hon, hal⟩ := exists_on3_eq_smul (a - 0) (sub_ne_zero.mpr ha0)
    have hax : (a - 0 : V3) = dist a 0 • e3 := by rw [dist_eq_norm]; exact hal
    obtain ⟨ψ, r1, r2, hr1, hr2, hzb, hzx⟩ := azim_frame_spec hnc hcolx hon hax
      (by simpa using ha0)
    have hza : zOf e1 e2 (a - 0) = 0 := zOf_axis hax hon
    have hlin : zOf e1 e2 (x - 0) = (t:ℂ) * zOf e1 e2 (b - 0) := by
      rw [hx', zOf_add, zOf_smul, zOf_smul, hza, mul_zero, zero_add]
    have hexp : Complex.exp (((Real.pi:ℝ):ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
    have hkey : (r2:ℂ) * Complex.exp (((ψ + azim 0 a b x : ℝ):ℂ) * Complex.I)
        = (((-t) * r1 : ℝ):ℂ) * Complex.exp (((ψ + Real.pi : ℝ):ℂ) * Complex.I) := by
      have hex : Complex.exp (((ψ + Real.pi : ℝ):ℂ) * Complex.I)
          = Complex.exp (((ψ:ℝ):ℂ) * Complex.I) * (-1) := by
        have hsplit : ((ψ + Real.pi : ℝ):ℂ) * Complex.I
            = ((ψ:ℝ):ℂ) * Complex.I + ((Real.pi:ℝ):ℂ) * Complex.I := by
          rw [Complex.ofReal_add]
          ring
        rw [hsplit, Complex.exp_add, hexp]
      rw [← hzx, hlin, hzb, hex]
      push_cast
      ring
    have hexeq : Complex.exp (((ψ + azim 0 a b x : ℝ):ℂ) * Complex.I)
        = Complex.exp (((ψ + Real.pi : ℝ):ℂ) * Complex.I) :=
      exp_pos_mul_eq hr2 (mul_pos (by linarith : (0:ℝ) < -t) hr1) hkey
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexeq
    have hθ : azim 0 a b x = Real.pi + (n:ℝ) * (2 * Real.pi) := by
      have h4 := hn
      push_cast at h4
      rw [add_mul, add_mul] at h4
      have h5 : ((azim 0 a b x : ℝ):ℂ) * Complex.I
          = ((Real.pi:ℝ):ℂ) * Complex.I
            + ((n:ℂ) * (2 * ((Real.pi:ℝ):ℂ) * Complex.I)) := by
        linear_combination h4
      have h6 : (((azim 0 a b x : ℝ) - Real.pi : ℝ):ℂ) * Complex.I
          = ((n:ℂ) * (2 * ((Real.pi:ℝ):ℂ))) * Complex.I := by
        rw [Complex.ofReal_sub]
        linear_combination h5
      have h10 := mul_right_cancel₀ Complex.I_ne_zero h6
      have h11 := congrArg Complex.re h10
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero] at h11
      norm_num at h11
      linarith
    have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
    have h2π : (0:ℝ) < 2 * Real.pi := by linarith
    rcases Int.lt_trichotomy n 0 with hn0 | hn00 | hn1
    · exfalso
      have hnle : ((n:ℤ):ℝ) ≤ ((-1:ℤ):ℝ) := Int.cast_le.mpr (by omega)
      simp only [Int.cast_neg, Int.cast_one] at hnle
      have hmul : (2:ℝ) * Real.pi * ((n:ℤ):ℝ) ≤ (2:ℝ) * Real.pi * (-1) :=
        mul_le_mul_of_nonneg_left hnle h2π.le
      rw [hθ] at hge
      nlinarith [hmul, hπ0]
    · refine Or.inr ?_
      rw [hθ, hn00]
      push_cast
      ring
    · exfalso
      have hnge : ((1:ℤ):ℝ) ≤ ((n:ℤ):ℝ) := Int.cast_le.mpr (by omega)
      simp only [Int.cast_one] at hnge
      have hmul : (2:ℝ) * Real.pi * 1 ≤ (2:ℝ) * Real.pi * ((n:ℤ):ℝ) :=
        mul_le_mul_of_nonneg_left hnge h2π.le
      rw [hθ] at hlt
      nlinarith [hmul, hπ0]
  · -- t = 0: x on the axis
    exfalso
    simp only [ht00, zero_smul, add_zero] at hx'
    exact hcolx ((collinear3_iff_smul ha0).mpr ⟨s, hx'⟩)
  · -- positive side: azimuth 0
    refine Or.inl ((azim_eq_zero_iff_alt hnc hcolx).mpr ?_)
    refine (affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := b) (y := x)
      (Ne.symm ha0) hb0 (fun he => hnc (by rw [he]; exact collinear3_pair_right rfl))).mpr
      ⟨t, ht1, s, by rw [hx']; module⟩

/-- `BBsV39` under `3 < k` yields the periodicity and the fan at the
origin (structural projections of `ConvexLocalFan`/`LocalFan`). -/
private theorem w4sg_bbs_fan_p18 {s : ScsV39} {k : ℕ} {v : ℕ → V3}
    (hk : s.k = k) (hk₃ : 3 < k) (hBB : BBsV39 s v) :
    Periodic v k ∧
      Kepler.Text.Fan.FAN 0 (Set.range v) (Set.range fun j => {v j, v (j + 1)}) := by
  obtain ⟨-, hper, -, hclf⟩ := hBB
  rcases hclf with hle | hclf
  · omega
  · obtain ⟨hLF, -⟩ := hclf
    obtain ⟨hfan, -⟩ := hLF
    exact ⟨by rw [← hk]; exact hper, hfan⟩

-- W4 (lane scsgeneric-w4) wave 1: real staging kit toward this theorem.
-- The three w4sg_* lemmas above are real (axioms = standard three):
--   * w4sg_azim_plane_p18  - in-plane azimuth dichotomy (the
--     AZIM_COND_FOR_COPLANAR consumption shape; LA6's sorried giant is
--     out of the import closure, this is the plane-through-0 case);
--   * w4sg_azim_pi_mem_p18 - azim = pi places w1 in affineSpan {v0, v1, w2};
--   * w4sg_bbs_fan_p18     - BBsV39 + 3 < k gives Periodic + FAN 0
--     (range v) (range edges) via ConvexLocalFan/LocalFan projections.
-- Wave-2 gap (HOL IUNBUIG.hl:672-906, still open):
--   * EGHNAVX_COLL_SCS_p18 (in-file sorried giant) supplies conclusions
--     2/3/4/5; FEKTYIY_p27 (LA27, sorried, in-closure) supplies the
--     case-2 non-coplanarity contradiction; both are already in the e2e
--     cone, so assembling with them is net -1 with zero new sorries;
--   * still to port: w4sg_periodic_shift (periodicity window shift),
--     w4sg_coplanar_mem_span (the la5_coplanar_diff_span-style span
--     argument, LA5/PackingAuto4 shapes in-closure), the barycentric
--     goal-builder via Affsign.of_triple, and the two-case assembly
--     (fan6 edge kit + hcol give all non-collinearity instances; no
--     injectivity lemma is needed - degenerate sub-cases die via the
--     azim definition's collinear branches).
/-! ## W4 wave 2 (lane scsgeneric-w4b): staging kit toward
`coplanar_aff_gt_simple_p18` -/

/-- A point with barycentric coordinates summing to one lies in the
affine span of the three reference points (`spanPoints` constructor). -/
private theorem w4sg_mem_affineSpan3_p18 {y a b c : V3} {r s t : ℝ}
    (hsum : r + s + t = 1) (hy : y = r • a + s • b + t • c) :
    y ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := by
  have hst : s = 1 - r - t := by linarith
  show y ∈ spanPoints ℝ ({a, b, c} : Set V3)
  refine ⟨a, Set.mem_insert a ({b, c} : Set V3),
    s • (b -ᵥ a) + t • (c -ᵥ a), ?_, ?_⟩
  · have hvsb : ((b : V3) -ᵥ a) ∈ vectorSpan ℝ ({a, b, c} : Set V3) :=
      vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem (a : V3)
          (Set.mem_insert b ({c} : Set V3)))
        (Set.mem_insert (a : V3) (insert (b : V3) ({c} : Set V3)))
    have hvsc : ((c : V3) -ᵥ a) ∈ vectorSpan ℝ ({a, b, c} : Set V3) :=
      vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem (a : V3) (Set.mem_insert_of_mem
          (b : V3) (Set.mem_singleton c)))
        (Set.mem_insert (a : V3) (insert (b : V3) ({c} : Set V3)))
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hvsb)
      (Submodule.smul_mem _ _ hvsc)
  · rw [hy, hst, vadd_eq_add]
    simp only [vsub_eq_sub]
    module

/-- An `affGt` point lies in the affine span of its three reference
points; no distinctness hypotheses are needed. -/
private theorem w4sg_affGt_pair_mem3_p18 {y p q : V3}
    (hmem : y ∈ affGt ({0, p} : Set V3) ({q} : Set V3)) :
    y ∈ (affineSpan ℝ ({0, p, q} : Set V3) : Set V3) := by
  obtain ⟨f, hfin, hsum, -, -⟩ := hmem
  have hsp : ((p : V3) -ᵥ (0 : V3)) ∈ vectorSpan ℝ ({0, p, q} : Set V3) :=
    vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem (0 : V3)
        (Set.mem_insert p ({q} : Set V3)))
      (Set.mem_insert (0 : V3) (insert p ({q} : Set V3)))
  have hp : (p : V3) ∈ vectorSpan ℝ ({0, p, q} : Set V3) := by
    rwa [vsub_eq_sub, sub_zero] at hsp
  have hsq : ((q : V3) -ᵥ (0 : V3)) ∈ vectorSpan ℝ ({0, p, q} : Set V3) :=
    vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem (0 : V3) (Set.mem_insert_of_mem p
        (Set.mem_singleton q)))
      (Set.mem_insert (0 : V3) (insert p ({q} : Set V3)))
  have hq : (q : V3) ∈ vectorSpan ℝ ({0, p, q} : Set V3) := by
    rwa [vsub_eq_sub, sub_zero] at hsq
  refine ⟨(0 : V3), Set.mem_insert (0 : V3) ({p, q} : Set V3), y -ᵥ (0 : V3), ?_,
    (vsub_vadd y (0 : V3)).symm⟩
  rw [hsum, vsub_eq_sub, sub_zero]
  refine Submodule.sum_mem _ ?_
  intro w hw
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hw
  rcases hw with hw2 | hq'
  · rcases hw2 with rfl | rfl
    · rw [smul_zero]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ hp
  · rw [hq']
    exact Submodule.smul_mem _ _ hq

/-- Azimuth `π` places the reference point in the affine span of the axis
pair and the target point (frame polar form + `rep_smul_of_zOf`). -/
private theorem w4sg_azim_pi_mem_p18 {v0 v1 w1 w2 : V3} (hw : v1 ≠ v0)
    (hnc1 : ¬ Collinear3 v0 v1 w1) (hnc2 : ¬ Collinear3 v0 v1 w2)
    (hπ : azim v0 v1 w1 w2 = Real.pi) :
    w1 ∈ (affineSpan ℝ ({v0, v1, w2} : Set V3) : Set V3) := by
  have hv01 : v0 ≠ v1 := Ne.symm hw
  obtain ⟨e1, e2, e3, hon, hal⟩ := exists_on3_eq_smul (v1 - v0) (sub_ne_zero.mpr hw)
  have hax : (v1 - v0 : V3) = dist v1 v0 • e3 := by rw [dist_eq_norm]; exact hal
  obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ := azim_frame_spec hnc1 hnc2 hon hax hw
  have hexp : Complex.exp (((Real.pi:ℝ):ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have hz2' : zOf e1 e2 (w2 - v0)
      = ((-r2 : ℝ):ℂ) * Complex.exp (((ψ : ℝ):ℂ) * Complex.I) := by
    have hsplit : ((ψ + Real.pi : ℝ):ℂ) * Complex.I
        = ((ψ:ℝ):ℂ) * Complex.I + ((Real.pi:ℝ):ℂ) * Complex.I := by
      rw [Complex.ofReal_add]; ring
    rw [hπ] at hz2
    rw [hz2, hsplit, Complex.exp_add, hexp]
    push_cast
    ring
  have hlin : zOf e1 e2 (w1 - v0)
      = ((-(r1 / r2) : ℝ):ℂ) * zOf e1 e2 (w2 - v0) := by
    have hr2c : (r2 : ℂ) ≠ 0 := by exact_mod_cast hr2.ne'
    have hx1 : zOf e1 e2 (w1 - v0) * (r2 : ℂ)
        = (-(r1 : ℂ)) * zOf e1 e2 (w2 - v0) := by
      rw [hz1, hz2']
      push_cast
      ring
    push_cast
    rw [eq_div_of_mul_eq hr2c hx1, neg_mul ((r1 : ℂ) / (r2 : ℂ))
      (zOf e1 e2 (w2 - v0)), div_mul_eq_mul_div]
    ring
  obtain ⟨h, hmem⟩ := rep_smul_of_zOf hon hax hw w2 w1 (-(r1 / r2)) hlin
  show w1 ∈ spanPoints ℝ ({v0, v1, w2} : Set V3)
  rw [show w1 = (w1 -ᵥ v0) +ᵥ v0 from (vsub_vadd w1 v0).symm]
  have hvec : (w1 -ᵥ v0 : V3) ∈ vectorSpan ℝ ({v0, v1, w2} : Set V3) := by
    show w1 - v0 ∈ vectorSpan ℝ ({v0, v1, w2} : Set V3)
    have hkey : w1 - v0 = h • (v1 - v0) + (-(r1 / r2)) • (w2 - v0) := by
      rw [hmem]
      module
    have hvv1 : (v1 -ᵥ v0 : V3) ∈ vectorSpan ℝ ({v0, v1, w2} : Set V3) :=
      vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem (v0 : V3)
          (Set.mem_insert (v1 : V3) ({w2} : Set V3)))
        (Set.mem_insert (v0 : V3) (insert (v1 : V3) ({w2} : Set V3)))
    have hvv2 : (w2 -ᵥ v0 : V3) ∈ vectorSpan ℝ ({v0, v1, w2} : Set V3) :=
      vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem (v0 : V3) (Set.mem_insert_of_mem
          (v1 : V3) (Set.mem_singleton w2)))
        (Set.mem_insert (v0 : V3) (insert (v1 : V3) ({w2} : Set V3)))
    rw [hkey]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hvv1)
      (Submodule.smul_mem _ _ hvv2)
  exact ⟨v0, by simp, w1 -ᵥ v0, hvec, rfl⟩

/-- Window shift along a periodic family: every index is `k`-adjacent to a
representative `i + j` with `j < k`. -/
private theorem w4sg_periodic_shift_p18 {f : ℕ → V3} {k : ℕ} (hk : k ≠ 0)
    (hper : Periodic f k) (i x : ℕ) : ∃ j < k, f x = f (i + j) := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hmod : ∀ n : ℕ, f (n % k) = f n := by
    intro n
    have key : ∀ m n : ℕ, f (n % k + k * m) = f (n % k) := by
      intro m
      induction m with
      | zero => intro n; rw [Nat.mul_zero, Nat.add_zero]
      | succ m ih =>
        intro n
        have he : n % k + k * (m + 1) = n % k + k * m + k := by ring
        rw [he, hper, ih n]
    have h1 := key (n / k) n
    rw [Nat.mod_add_div n k] at h1
    exact h1.symm
  refine ⟨(x + k - i % k) % k, Nat.mod_lt _ hkpos, ?_⟩
  have hA : (i % k + (x + k - i % k)) % k = x % k := by
    have hle2 : i % k ≤ x + k :=
      le_trans (Nat.le_of_lt (Nat.mod_lt _ hkpos)) (by omega : k ≤ x + k)
    rw [Nat.add_sub_cancel' hle2, Nat.add_mod_right]
  have hkey : (i + ((x + k - i % k) % k)) % k = x % k :=
    Eq.trans (Eq.trans (Nat.ModEq.add_right _ (Nat.ModEq.symm (Nat.mod_modEq i k)))
      (Nat.ModEq.add_left (i % k) (Nat.mod_modEq (x + k - i % k) k))) hA
  rw [← hmod (i + ((x + k - i % k) % k)), ← hmod x, hkey]

/-- Lane support: `WithLp.toLp` zero test (Pi level). -/
private theorem w4sg_toLp_eq_zero {f : Fin 3 → ℝ} :
    (WithLp.toLp 2 f : V3) = 0 ↔ f = 0 := by
  constructor
  · intro h
    simpa [WithLp.ofLp_toLp, WithLp.ofLp_zero] using
      congrArg (fun w : V3 => (w : Fin 3 → ℝ)) h
  · intro h
    subst h
    rfl

/-- Lane support: `Set.range ![p, q, r]` is the three-point set. -/
private theorem w4sg_range3 {p q r : V3} :
    (Set.range ![p, q, r] : Set V3) = ({p, q, r} : Set V3) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hw
    rcases Set.mem_insert_iff.mp hw with rfl | h
    · exact ⟨0, rfl⟩
    rcases Set.mem_insert_iff.mp h with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Coplanarity with a non-collinear triple through the origin puts the
fourth point in the linear span of the two non-collinear ones
(`la5_coplanar_diff_span` shape re-derived inline). -/
private theorem w4sg_coplanar_mem_span_p18 {p q r : V3}
    (hnc : ¬ Collinear3 0 p q) (hcop : Coplanar ({0, p, q, r} : Set V3)) :
    ∃ μ ν : ℝ, r = μ • p + ν • q := by
  have hLI : LinearIndependent ℝ ![((p - 0 : V3) : Fin 3 → ℝ), ((q - 0 : V3) : Fin 3 → ℝ)] := by
    have hne : ¬((crossProduct ((p - 0 : V3) : Fin 3 → ℝ)
        ((q - 0 : V3) : Fin 3 → ℝ)) = 0) := fun h =>
      hnc ((COLLINEAR_CROSS_0 (x := 0) (y := p) (z := q)).mpr
        (w4sg_toLp_eq_zero.mpr h))
    exact crossProduct_ne_zero_iff_linearIndependent.mp hne
  obtain ⟨u, v', w', hsub⟩ := hcop
  have h0K : 0 ∈ (affineSpan ℝ ({u, v', w'} : Set V3) : Set V3) := hsub (by simp)
  have hpK : p ∈ (affineSpan ℝ ({u, v', w'} : Set V3) : Set V3) := hsub (by simp)
  have hqK : q ∈ (affineSpan ℝ ({u, v', w'} : Set V3) : Set V3) := hsub (by simp)
  have hrK : r ∈ (affineSpan ℝ ({u, v', w'} : Set V3) : Set V3) := hsub (by simp)
  have hp : (p - 0 : V3) ∈ (affineSpan ℝ ({u, v', w'} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction hpK h0K
  have hq : (q - 0 : V3) ∈ (affineSpan ℝ ({u, v', w'} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction hqK h0K
  have hr : (r - 0 : V3) ∈ (affineSpan ℝ ({u, v', w'} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction hrK h0K
  have hLIV3 : LinearIndependent ℝ ![(p - 0 : V3), (q - 0 : V3)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hPi : (∑ j, g j • ((![((p - 0 : V3) : Fin 3 → ℝ), ((q - 0 : V3) : Fin 3 → ℝ)] :
        Fin 2 → (Fin 3 → ℝ)) j)) = 0 := by
      simpa using congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hg
    exact Fintype.linearIndependent_iff.mp hLI g hPi i
  have hset : (Set.range ![p - 0, q - 0] : Set V3) = ({p - 0, q - 0} : Set V3) := by
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hs
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simpa using (Set.mem_singleton_iff.mp hs).symm⟩
  have hf2 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![p - 0, q - 0] : Set V3)) = 2 := by
    have := finrank_span_eq_card (R := ℝ) (M := V3) hLIV3
    simpa using this
  have hvs : vectorSpan ℝ ({u, v', w'} : Set V3)
      = vectorSpan ℝ (Set.range ![u, v', w'] : Set V3) := by
    rw [w4sg_range3]
  have hfrK : Module.finrank ℝ (affineSpan ℝ ({u, v', w'} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact finrank_vectorSpan_range_le ℝ ![u, v', w'] (by norm_num)
  haveI hfdK : FiniteDimensional ℝ (affineSpan ℝ ({u, v', w'} : Set V3)).direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ (Set.toFinite _)
  have hle : Submodule.span ℝ (Set.range ![p - 0, q - 0] : Set V3)
      ≤ (affineSpan ℝ ({u, v', w'} : Set V3)).direction := by
    rw [Submodule.span_le, hset]
    rintro s (rfl | rfl)
    · exact hp
    · exact hq
  have hEq : Submodule.span ℝ ({p - 0, q - 0} : Set V3)
      = (affineSpan ℝ ({u, v', w'} : Set V3)).direction := by
    rw [← hset]
    exact Submodule.eq_of_le_of_finrank_eq hle
      (le_antisymm (Submodule.finrank_mono hle) (hfrK.trans hf2.ge))
  obtain ⟨μ, ν, hμν⟩ := Submodule.mem_span_pair.mp (hEq ▸ hr)
  simp only [sub_zero] at hμν
  exact ⟨μ, ν, hμν.symm⟩

/-- HOL `coplanar_aff_gt_simple` (IUNBUIG.hl:663). Giant. -/
theorem coplanar_aff_gt_simple_p18 (s : ScsV39) (k : ℕ) (v : ℕ → V3) (i : ℕ)
    (his : isScsV39 s) (hk : s.k = k) (hk₃ : 3 < k) (hMM : v ∈ MMsV39 s)
    (hbas : scsBasicV39 s)
    (hcol : ∀ j : ℕ, v j ≠ v i → ¬ Collinear3 0 (v i) (v j))
    (hcp : Coplanar ({0, v i, v (i + 1), v (i + 2)} : Set V3)) :
    v (i + 1) ∈ affGt {0} {v i, v (i + 2)} := by
  -- MMs → BBs → periodic + fan (LA27 + wave-1 kit)
  obtain ⟨hBB, -⟩ := mm_BBs_taustar_p27 s v hMM
  obtain ⟨hper, hfan⟩ := w4sg_bbs_fan_p18 hk hk₃ hBB
  have hfan2 := hfan.2.2.2.1
  have hv0 : ∀ j : ℕ, v j ≠ 0 := by
    intro j he
    exact hfan2 (Set.mem_range.mpr ⟨j, he⟩)
  have heI : ({v i, v (i + 1)} : Set V3) ∈
      Set.range (fun j : ℕ => ({v j, v (j + 1)} : Set V3)) := Set.mem_range.mpr ⟨i, rfl⟩
  have heI1 : ({v (i + 1), v (i + 2)} : Set V3) ∈
      Set.range (fun j : ℕ => ({v j, v (j + 1)} : Set V3)) :=
    Set.mem_range.mpr ⟨i + 1, rfl⟩
  have hi0 : v i ≠ 0 := hv0 i
  have hnc01 : ¬ Collinear3 0 (v i) (v (i + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan heI
  have hnc12 : ¬ Collinear3 0 (v (i + 1)) (v (i + 2)) :=
    Kepler.Text.Fan.fan_not_collinear hfan heI1
  have hi1 : v i ≠ v (i + 1) := by
    intro he
    exact hnc01 (by rw [he]; exact collinear3_pair_right rfl)
  -- the sorried giant (in-file, already in the e2e cone)
  obtain ⟨-, E2, E3, E4, E5⟩ := EGHNAVX_COLL_SCS_p18 s k v i his hk hk₃ hBB hbas hcol
  -- azimuth dichotomy from the coplanarity hypothesis
  obtain ⟨μ, ν, hμν⟩ := w4sg_coplanar_mem_span_p18 hnc01 hcp
  have hx1 : v (i + 2) - 0 = μ • (v i - 0) + ν • (v (i + 1) - 0) := by
    rw [sub_zero, sub_zero, sub_zero, hμν]
  rcases w4sg_azim_plane_p18 hi0 (hv0 (i + 1)) hnc01 ⟨μ, ν, hx1⟩ with haz0 | hazπ
  · -- Case azim = 0
    obtain ⟨-, h4⟩ := E4 2 2 haz0 (by norm_num) (by norm_num) (by omega)
    obtain ⟨c1, hc1, h1c, hexp1⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := v i) (x := v (i+1)) (y := v (i+2))
        (Ne.symm hi0) (hv0 (i+1)) (Ne.symm hi1)).mp h4
    simp only [sub_zero] at hexp1
    -- hexp1 : v (i+2) = c1 • v (i+1) + h1c • v i  with 0 < c1
    have hvi_eq : v (i + 2) = v i → False := by
      intro hexpd
      apply hnc01
      have hvi : v i = c1 • v (i + 1) + h1c • v i := by
        rw [← hexp1]; exact hexpd.symm
      have h2 : (1 - h1c) • v i + h1c • v i = c1 • v (i + 1) + h1c • v i := by
        rw [← hvi]; module
      have hrel := add_right_cancel h2
      have hc1' : c1 ≠ 0 := hc1.ne'
      refine (collinear3_iff_smul hi0).mpr ⟨(1 - h1c) / c1, ?_⟩
      rw [sub_zero, sub_zero, show ((1 - h1c : ℝ) / c1) • (v i : V3)
          = (1 / c1) • ((1 - h1c) • v i) from by
            rw [smul_smul, mul_comm, show (1 - h1c : ℝ) * (1 / c1)
                = (1 - h1c) / c1 from by ring]]
      rw [hrel, one_div, inv_smul_smul₀ hc1']
    have hi2 : v (i + 2) ≠ v i := fun h => hvi_eq h
    have hncI2 : ¬ Collinear3 0 (v i) (v (i + 2)) := hcol (i + 2) hi2
    obtain ⟨c2, hc2, h2c, hexp2⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := v i) (x := v (i+2)) (y := v (i+1))
        (Ne.symm hi0) (hv0 (i+2)) hi2).mp ((azim_eq_zero_iff hnc01 hncI2).mp haz0)
    simp only [sub_zero] at hexp2
    -- hexp2 : v (i+1) = c2 • v (i+2) + h2c • v i  with 0 < c2
    have hcomp2 : v (i + 1) = (c2 * c1) • v (i + 1) + (c2 * h1c + h2c) • v i := by
      have hcomp : v (i + 1) = c2 • (c1 • v (i + 1) + h1c • v i) + h2c • v i := by
        conv_rhs => rw [← hexp1]
        exact hexp2
      nth_rewrite 1 [hcomp]
      module
    have hkeyA : (1 - c2 * c1) • v (i + 1) - (c2 * h1c + h2c) • v i = 0 := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [hcomp2]
      module
    by_cases hzero : 1 - c2 * c1 = 0
    · have hDv : (c2 * h1c + h2c) • v i = 0 := by
        rw [hzero] at hkeyA
        simpa using hkeyA
      have hs0 : c2 * h1c + h2c = 0 := by
        rcases smul_eq_zero.mp hDv with hn | hvz
        · linarith
        · exact absurd hvz hi0
      by_cases h1n : h1c < 0
      · -- h1c < 0 forces h2c > 0: the goal witness
        have h2cp : 0 < h2c := by
          have he : h2c = -(c2 * h1c) := by linarith
          rw [he]
          simpa [neg_mul] using mul_pos hc2 (neg_pos.mpr h1n)
        show Affsign (fun x : ℝ => 0 < x) ({0} : Set V3) ({v i, v (i + 2)} : Set V3)
          (v (i + 1))
        exact Affsign.of_triple h2c c2 h2cp hc2
          (by rw [smul_zero, zero_add, hexp2]; module) (Ne.symm hi0)
          (Ne.symm (hv0 (i + 2))) (Ne.symm hi2)
      · -- h1c ≥ 0: v (i+2) ∈ affGe {0} {v i, v (i+1)} and the fan kills both disjuncts
        exfalso
        have h1ge : 0 ≤ h1c := le_of_not_gt h1n
        have hmem_ge : v (i + 2) ∈ affGe ({0} : Set V3) ({v i, v (i + 1)} : Set V3) := by
          show Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3) ({v i, v (i + 1)} : Set V3)
            (v (i + 2))
          exact Affsign.of_triple h1c c1 h1ge hc1.le
            (by rw [smul_zero, zero_add, hexp1]; module) (Ne.symm hi0)
            (Ne.symm (hv0 (i + 1))) hi1
        exact (FAN_IN_AFF_GE_IMP_EQ hfan (Set.mem_range.mpr ⟨i + 2, rfl⟩) heI
          hmem_ge).elim hvi_eq
          (fun hexpd2 => hnc12 (by rw [hexpd2]; exact collinear3_pair_right rfl))
    · -- 1 - c2 * c1 ≠ 0: v (i+1) is a real multiple of v i, collinear contradiction
      exfalso
      have hden : 1 - c2 * c1 ≠ 0 := hzero
      refine absurd ((collinear3_iff_smul hi0).mpr
        ⟨(c2 * h1c + h2c) / (1 - c2 * c1), ?_⟩) hnc01
      rw [sub_zero, sub_zero, show ((c2 * h1c + h2c : ℝ) / (1 - c2 * c1)) • (v i : V3)
          = (1 / (1 - c2 * c1)) • ((c2 * h1c + h2c) • v i) from by
            rw [smul_smul, mul_comm (1 / (1 - c2 * c1)) (c2 * h1c + h2c),
              show (c2 * h1c + h2c : ℝ) * (1 / (1 - c2 * c1))
                = (c2 * h1c + h2c) / (1 - c2 * c1) from by ring]]
      rw [← sub_eq_zero.mp hkeyA, one_div, inv_smul_smul₀ hden]
  · -- Case azim = π
    have hk0 : k ≠ 0 := by omega
    have hk2 : 2 < k - 1 := by omega
    have hge : Real.pi ≤ azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) := by
      rw [← hazπ]; exact E3 2 (k - 1) hk2 (by omega)
    have hreq : azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi :=
      le_antisymm E2 hge
    have h0 : azim 0 (v i) (v (i + 1)) (v i) = 0 := by
      rw [azim, if_pos (Or.inr (collinear3_pair_right rfl))]
    have hncIK : ¬ Collinear3 0 (v i) (v (i + (k - 1))) := by
      by_contra hnc'
      have hne : v (i + (k - 1)) ≠ v i := by
        intro he
        rw [he] at hreq
        rw [h0] at hreq
        exact Real.pi_ne_zero hreq.symm
      exact hcol (i + (k - 1)) hne hnc'
    refine absurd (?_ : Coplanar ({0} ∪ Set.range v : Set V3))
      (FEKTYIY_p27 s v his hMM (by rw [hk]; omega))
    refine ⟨(0:V3), v i, v (i + (k - 1)), ?_⟩
    intro z hz
    rcases hz with h0z | hj
    · rw [h0z]
      have hz0 : (0:V3) = (1:ℝ) • (0:V3) + (0:ℝ) • v i + (0:ℝ) • v (i + (k - 1)) := by
        simp
      exact w4sg_mem_affineSpan3_p18 (hy := hz0) (by norm_num)
    · obtain ⟨j, hjv⟩ := Set.mem_range.mp hj
      rw [← hjv]
      obtain ⟨d, hdlt, hdv⟩ := w4sg_periodic_shift_p18 hk0 hper i j
      rw [hdv]
      rcases Nat.eq_zero_or_pos d with hd0 | hd1p
      · rw [hd0, Nat.add_zero]
        have hvi : v i = (0:ℝ) • (0:V3) + (1:ℝ) • v i + (0:ℝ) • v (i + (k - 1)) := by
          simp
        exact w4sg_mem_affineSpan3_p18 (hy := hvi) (by norm_num)
      · by_cases hd1 : d = 1
        · rw [hd1]
          exact w4sg_azim_pi_mem_p18 hi0 hnc01 hncIK hreq
        · have hd2 : 2 ≤ d := by omega
          have h5 := (E5 2 d (hazπ.trans hreq.symm) (by norm_num) hk2 hd2 hdlt).2
          exact w4sg_affGt_pair_mem3_p18 h5
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
    azim v₀ v₁ v₂ v₃ = dihY (dist v₀ v₁) (dist v₀ v₂) (dist v₀ v₃)
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

/-! ### la18-sumazim kit (lane la18-sumazim-w1, 2026-11-05): the `_p18`
cyclic-fan transport helpers for `SUM_AZIM_EQ_ANGLE_LE4_FUN_p18`

LA35 proves the `rhoFun`-weighted specialization (`SUM_AZIM_EQ_ANGLE_LE4_p35`,
LocalAuto35:18316) from its private kit (`vvModEq/vvRhoDet/vvMemEdge/...`,
LA35:993-18290).  Those helpers are `private`, so the `ff`-general identity is
re-proved here through the same route, re-instantiated at the `_p18`
renderings `rhoNode1_p18`/`azimInFan_p18`; the public LA35 theorems
`VV_INJ_p35` and `VV_SUC_EQ_RHO_NODE_PRIME_p35` (in the import cone through
`Kepler.Text.LocalAuto27`) supply window injectivity and the rho-orbit.  The
sum bookkeeping is `setSum_Iio`/`setSum_FF`/`sum_shift` (LA35:18214-18290,
copied because private). -/

/-- `Classical.epsilon` collapse under a uniqueness hypothesis. -/
private theorem la18sz_epsFixed {α : Type*} [Nonempty α] {pr : α → Prop} {a : α}
    (hpa : pr a) (huniq : ∀ y, pr y → y = a) : Classical.epsilon pr = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- Equal `vv`-values have equal residues (periodicity + window injectivity). -/
private theorem la18sz_vvModEq {vv : ℕ → V3} {k : ℕ} (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) {i j : ℕ} (h : vv i = vv j) :
    i % k = j % k := by
  by_contra hne
  have h1 : vv (i % k) = vv (j % k) := by
    rw [periodic_mod_eq_p23 hper i, periodic_mod_eq_p23 hper j, h]
  exact hinj (i % k) (j % k) (Nat.mod_lt i hk0) (Nat.mod_lt j hk0) hne h1

/-- Successor respects residue equality (periodicity). -/
private theorem la18sz_vvStep {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) {i j : ℕ}
    (h : i % k = j % k) : vv (i + 1) = vv (j + 1) := by
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have e2 : (j + 1) % k = (j % k + 1) % k := by simp [Nat.add_mod]
  rw [← periodic_mod_eq_p23 hper (i + 1), ← periodic_mod_eq_p23 hper (j + 1), e1, e2, h]

/-- Predecessor respects successor-residue equality. -/
private theorem la18sz_vvModPred {k : ℕ} {i j : ℕ} (hk0 : 0 < k)
    (h : (i + 1) % k = (j + 1) % k) : i % k = j % k := by
  have hik : i % k < k := Nat.mod_lt i hk0
  have hjk : j % k < k := Nat.mod_lt j hk0
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have e2 : (j + 1) % k = (j % k + 1) % k := by simp [Nat.add_mod]
  rw [e1, e2] at h
  have hs : i % k + 1 = j % k + 1 ∨ (i % k + 1 = k ∧ j % k + 1 = k) := by
    rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h
      rcases Nat.lt_or_ge (j % k + 1) k with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at h
        exact Or.inl h
      · have h2 : j % k + 1 = k := by omega
        rw [h2, Nat.mod_self] at h
        exact absurd h (by omega)
    · have h2 : i % k + 1 = k := by omega
      rw [h2, Nat.mod_self] at h
      rcases Nat.lt_or_ge (j % k + 1) k with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at h
        exact absurd h (by omega)
      · have h3 : j % k + 1 = k := by omega
        exact Or.inr ⟨h2, h3⟩
  omega

/-- Mod-k cancellation of a common summand. -/
private theorem la18sz_modAddCancel {k a b c : ℕ} (h : (a + c) % k = (b + c) % k) :
    a % k = b % k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0] at h ⊢
    simpa [Nat.mod_zero] using h
  have hak : a % k < k := Nat.mod_lt a hk0
  have hbk : b % k < k := Nat.mod_lt b hk0
  have hck : c % k < k := Nat.mod_lt c hk0
  have e1 : (a + c) % k = (a % k + c % k) % k := by rw [Nat.add_mod]
  have e2 : (b + c) % k = (b % k + c % k) % k := by rw [Nat.add_mod]
  rw [e1, e2] at h
  have d1 : (a % k + c % k) % k = a % k + c % k ∨
      (a % k + c % k) % k + k = a % k + c % k := by
    rcases Nat.lt_or_ge (a % k + c % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : a % k + c % k = (a % k + c % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show a % k + c % k - k < k by omega)]
        omega)
  have d2 : (b % k + c % k) % k = b % k + c % k ∨
      (b % k + c % k) % k + k = b % k + c % k := by
    rcases Nat.lt_or_ge (b % k + c % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hY : b % k + c % k = (b % k + c % k - k) + k * 1 := by omega
        rw [hY, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show b % k + c % k - k < k by omega)]
        omega)
  rcases d1 with d1 | d1 <;> rcases d2 with d2 | d2 <;> omega

/-- Unordered-pair equality splits into the two pairings. -/
private theorem la18sz_pairMem {a w b c : V3} (h : ({a, w} : Set V3) = {b, c}) :
    (a = b ∨ a = c) ∧ (w = b ∨ w = c) := by
  have m1 : a ∈ ({b, c} : Set V3) := by rw [← h]; simp
  have m2 : w ∈ ({b, c} : Set V3) := by rw [← h]; simp
  refine ⟨?_, ?_⟩
  · rcases Set.mem_insert_iff.mp m1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Set.mem_singleton_iff.mp h1)
  · rcases Set.mem_insert_iff.mp m2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Set.mem_singleton_iff.mp h2)

/-- `k ∣ t` from `i ≡ i + t (mod k)`. -/
private theorem la18sz_modEqAddCancel {k i t : ℕ} (hk0 : 0 < k) (h : i % k = (i + t) % k) :
    t % k = 0 := by
  have h1 : (i % k + t % k) % k = i % k := by
    have e : (i % k + t % k) % k = (i + t) % k := by rw [Nat.add_mod i t k]
    rw [e, h]
  have hik : i % k < k := Nat.mod_lt i hk0
  have htk : t % k < k := Nat.mod_lt t hk0
  have d : (i % k + t % k) % k = i % k + t % k ∨
      (i % k + t % k) % k + k = i % k + t % k := by
    rcases Nat.lt_or_ge (i % k + t % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : i % k + t % k = (i % k + t % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show i % k + t % k - k < k by omega)]
        omega)
  rcases d with d | d <;> omega

/-- `k`-shifted indices carry the same `vv`-value. -/
private theorem la18sz_vvAddK {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) (i : ℕ) :
    vv (i + k) = vv i := by
  rw [← periodic_mod_eq_p23 hper (i + k), Nat.add_mod_right]
  exact periodic_mod_eq_p23 hper i

/-- A `1 % k = 0` hypothesis forces `k ≤ 1`. -/
private theorem la18sz_modOneZero_le {k : ℕ} (h : (1:ℕ) % k = 0) : k ≤ 1 := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · omega
  · have h1 : (1:ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
    omega

/-- The vertex and its cyclic successor differ once `3 ≤ k`. -/
private theorem la18sz_vvNeStep {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have h := la18sz_modEqAddCancel hk0 (i := i) (t := 1) (la18sz_vvModEq hk0 hper hinj hh)
  exact absurd hk3 (by have := la18sz_modOneZero_le h; omega)

/-- The vertex and its cyclic predecessor differ once `3 ≤ k`. -/
private theorem la18sz_vvNePred {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + k - 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hh2 : vv i = vv (i + (k - 1)) := by
    have hsub : (i + k) - 1 = i + (k - 1) := by omega
    calc vv i = vv (i + k - 1) := hh
      _ = vv ((i + k) - 1) := rfl
      _ = vv (i + (k - 1)) := by rw [hsub]
  have h := la18sz_modEqAddCancel hk0 (i := i) (t := k - 1)
    (la18sz_vvModEq hk0 hper hinj hh2)
  have hmod : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  omega

/-- Edge membership in the cyclic edge set: the two neighbours. -/
private theorem la18sz_vvMemEdge {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k) (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) (w : V3) :
    w ∈ ee (vv i) E ↔ w = vv (i + k - 1) ∨ w = vv (i + 1) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hnosing : ∀ j : ℕ, vv j ≠ vv (j + 1) := fun j => la18sz_vvNeStep hk3 hper hinj j
  show {vv i, w} ∈ E ↔ _
  constructor
  · intro hw
    rw [← hE] at hw
    obtain ⟨j, hj⟩ := hw
    obtain ⟨ha, hwbc⟩ := la18sz_pairMem hj.symm
    rcases ha with hai | hai
    · have hmod : i % k = j % k := la18sz_vvModEq hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · exfalso
        have hsucc : vv j = vv (j + 1) := by
          have m : vv (j + 1) ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
          rw [hw1, hai] at m
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
          exact m.elim (fun h => h.symm) (fun h => h.symm)
        exact absurd hsucc (hnosing j)
      · refine Or.inr ?_
        rw [hw1, la18sz_vvStep hper hmod]
    · have hmod1 : i % k = (j + 1) % k := la18sz_vvModEq hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · refine Or.inl ?_
        have hpred : (i + k - 1) % k = j % k := by
          have hstep : (i + k - 1 + 1) % k = (j + 1) % k := by
            rw [show i + k - 1 + 1 = i + k from by omega, Nat.add_mod_right]
            exact hmod1
          exact la18sz_vvModPred hk0 hstep
        rw [hw1, ← periodic_mod_eq_p23 hper j, ← hpred,
          periodic_mod_eq_p23 hper (i + k - 1)]
      · exfalso
        rw [← hai] at hw1
        have m : vv j ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
        rw [hw1] at m
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
        have hvj : vv j = vv i := m.elim id id
        exact absurd (hvj.trans hai) (hnosing j)
  · rintro (rfl | rfl)
    · show {vv i, vv (i + k - 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i + k - 1, by
        show {vv (i + k - 1), vv (i + k - 1 + 1)} = {vv i, vv (i + k - 1)}
        rw [show i + k - 1 + 1 = i + k from by omega, la18sz_vvAddK hper i]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto⟩
    · show {vv i, vv (i + 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i, rfl⟩

/-- Cyclic-fan dart determinism: the rho-successor of a first coordinate is
unique (the `vv`-fan specialization used inside the angle identity). -/
private theorem la18sz_vvRhoDet {vv : ℕ → V3} {FF : Set (V3 × V3)} {k : ℕ}
    (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    {a b : V3} (hab : (a, b) ∈ FF) : rhoNode1 FF a = b := by
  refine la18sz_epsFixed hab ?_
  intro y hy
  rw [← hFF] at hab hy
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hy
  have hia : vv i = a := congrArg Prod.fst hi
  have hib : vv (i + 1) = b := congrArg Prod.snd hi
  have hja : vv j = a := congrArg Prod.fst hj
  have hjy : vv (j + 1) = y := congrArg Prod.snd hj
  have hmod := la18sz_vvModEq hk0 hper hinj (hia.trans hja.symm)
  have hstep := la18sz_vvStep hper hmod
  rw [← hjy, ← hstep]
  exact hib

/-- Cyclic-fan dart determinism, mirror direction (`ivs_rho_node1`). -/
private theorem la18sz_vvIvsDet {vv : ℕ → V3} {FF : Set (V3 × V3)} {k : ℕ}
    (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    {a b : V3} (hab : (a, b) ∈ FF) : ivsRhoNode1 FF b = a := by
  refine la18sz_epsFixed hab ?_
  intro c hc
  rw [← hFF] at hab hc
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hc
  have hia : vv i = a := congrArg Prod.fst hi
  have hib : vv (i + 1) = b := congrArg Prod.snd hi
  have hjc : vv j = c := congrArg Prod.fst hj
  have hjb : vv (j + 1) = b := congrArg Prod.snd hj
  have hmod1 := la18sz_vvModEq hk0 hper hinj (hib.trans hjb.symm)
  have hmod2 := la18sz_vvModPred hk0 hmod1
  rw [← hjc, ← periodic_mod_eq_p23 hper j, ← hmod2, periodic_mod_eq_p23 hper i]
  exact hia

/-- The interior angle at a cyclic vertex equals the `_p18` fan azimuth of its
dart (two-point neighbour specialization of `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM`;
LA35's private `vvInangleEq_p35` re-rendered through `azimCycle_p18`). -/
private theorem la18sz_vvInangleEq {vv : ℕ → V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) (i : ℕ) :
    interiorAngle1 0 FF (vv i) = azimInFan_p18 (vv i, vv (i + 1)) E := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := by
    intro hh
    have hmod := la18sz_vvModEq hk0 hper hinj hh
    have hplus : ((i + k - 1) + 1) % k = ((i + 1) + 1) % k := by
      have g1 : ((i + k - 1) + 1) % k = ((i + k - 1) % k + 1 % k) % k := by
        rw [Nat.add_mod]
      have g2 : ((i + 1) + 1) % k = ((i + 1) % k + 1 % k) % k := by rw [Nat.add_mod]
      rw [g1, g2, hmod]
    rw [show (i + k - 1) + 1 = i + k from by omega, Nat.add_mod_right] at hplus
    have h3 := la18sz_modEqAddCancel hk0 (i := i) (t := 2) hplus
    have h4 : (2:ℕ) % k = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hee : EE_p18 (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact la18sz_vvMemEdge hk3 hper hinj hE i w
  have hnc : (EE_p18 (vv i) E).ncard = 2 := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  have hcond : 1 < (EE_p18 (vv i) E).ncard := by rw [hnc]; omega
  have hsucc : azimCycle_p18 (EE_p18 (vv i) E) 0 (vv i) (vv (i + 1)) =
      vv (i + k - 1) := by
    unfold azimCycle_p18
    rw [if_neg ?_]
    · refine la18sz_epsFixed ?_ ?_
      · refine ⟨hstep, ?_, ?_⟩
        · rw [hee]; simp
        · intro q hq hqne
          rw [hee] at hq
          rcases Set.mem_insert_iff.mp hq with h | h
          · right
            rw [h]
            exact ⟨rfl, le_refl _⟩
          · exact absurd (Set.mem_singleton_iff.mp h) hqne
      · intro y hy
        obtain ⟨hyne, hyW, -⟩ := hy
        rw [hee] at hyW
        rcases Set.mem_insert_iff.mp hyW with h | h
        · exact h
        · exact absurd (Set.mem_singleton_iff.mp h) hyne
    · intro hsub
      have hmem : vv (i + k - 1) ∈ EE_p18 (vv i) E := by rw [hee]; simp
      exact hstep (Set.mem_singleton_iff.mp (hsub hmem))
  have hrho : rhoNode1 FF (vv i) = vv (i + 1) :=
    la18sz_vvRhoDet hk0 hper hinj hFF (by rw [← hFF]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  have hivs : ivsRhoNode1 FF (vv i) = vv (i + k - 1) :=
    la18sz_vvIvsDet hk0 hper hinj hFF (by
      rw [← hFF]
      refine Set.mem_range.mpr ⟨i + k - 1, ?_⟩
      show (vv (i + k - 1), vv (i + k - 1 + 1)) = (vv (i + k - 1), vv i)
      rw [show i + k - 1 + 1 = i + k from by omega, la18sz_vvAddK hper i])
  show azim 0 (vv i) (rhoNode1 FF (vv i)) (ivsRhoNode1 FF (vv i))
    = azimInFan_p18 (vv i, vv (i + 1)) E
  rw [hrho, hivs, ← hsucc, azimInFan_p18, if_pos hcond]

/-- `setSum` over `{i | i < k}` folds to a `Finset.range k` sum. -/
private theorem la18sz_setSum_Iio (f : ℕ → ℝ) (k : ℕ) :
    setSum {i | i < k} f = ∑ i ∈ Finset.range k, f i := by
  rw [setSum]
  have hfin : {i | i < k}.Finite := Set.finite_Iio k
  rw [dif_pos hfin]
  have hEq : hfin.toFinset = Finset.range k := by
    ext i
    simp [Set.mem_toFinset, Finset.mem_range]
  rw [hEq]

/-- The cyclic dart set folds to a `Finset.range k` sum. -/
private theorem la18sz_setSum_FF (vv : ℕ → V3) (g : V3 × V3 → ℝ) (k : ℕ) (hk0 : 0 < k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) :
    setSum (Set.range (fun i => (vv i, vv (i + 1)))) g
      = ∑ i ∈ Finset.range k, g (vv i, vv (i + 1)) := by
  have hperd : Periodic (fun i => (vv i, vv (i + 1))) k := by
    intro i
    show (vv (i + k), vv (i + k + 1)) = (vv i, vv (i + 1))
    rw [hper i, Nat.add_right_comm i k 1, hper (i + 1)]
  have hrange : Set.range (fun i => (vv i, vv (i + 1)))
      = (fun i => (vv i, vv (i + 1))) '' Set.Iio k :=
    range_periodic_image_p23 _ k hk0 hperd
  have hfin : ((fun i => (vv i, vv (i + 1))) '' Set.Iio k).Finite :=
    Set.Finite.image _ (Set.finite_Iio k)
  have hinj3 : ∀ x ∈ (Set.Finite.toFinset (Set.finite_Iio k)),
      ∀ y ∈ (Set.Finite.toFinset (Set.finite_Iio k)),
      (vv x, vv (x + 1)) = (vv y, vv (y + 1)) → x = y := by
    intro x hx y hy hxy
    have hxk : x < k := by simpa [Set.mem_toFinset, Set.mem_Iio] using hx
    have hyk : y < k := by simpa [Set.mem_toFinset, Set.mem_Iio] using hy
    by_contra hne
    have hfst : vv x = vv y := congrArg Prod.fst hxy
    exact hinj x y hxk hyk hne hfst
  have hEq2 : hfin.toFinset =
      (Set.Finite.toFinset (Set.finite_Iio k)).image (fun i => (vv i, vv (i + 1))) := by
    ext x
    simp
  have hEq3 : (Set.Finite.toFinset (Set.finite_Iio k)) = Finset.range k := by
    ext i
    simp [Finset.mem_range]
  rw [hrange, setSum, dif_pos hfin, hEq2, Finset.sum_image hinj3, hEq3]

/-- Cyclic shift of a `range k` sum. -/
private theorem la18sz_sum_shift (G : ℕ → ℝ) (k c : ℕ) (hk0 : 0 < k)
    (hper : Periodic G k) :
    ∑ i ∈ Finset.range k, G (i + c) = ∑ i ∈ Finset.range k, G i := by
  have hstep : ∀ i ∈ Finset.range k, G (i + c) = G ((i + c) % k) := fun i _ =>
    (periodic_mod_eq_p23 hper (i + c)).symm
  refine Finset.sum_bij (fun i _ => (i + c) % k)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hk0))
    (fun i hi j hj hij =>
      have h1 : i % k = j % k := la18sz_modAddCancel (c := c) hij
      have h2 : i = j := by
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
          Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h1
        exact h1
      h2)
    (fun t ht =>
      have htk : t < k := Finset.mem_range.mp ht
      have hck : c % k < k := Nat.mod_lt c hk0
      have hck2 : c % k ≤ c := Nat.mod_le c k
      ⟨(t + k - c % k) % k, Finset.mem_range.mpr (Nat.mod_lt _ hk0),
        by
          have e1 : Nat.ModEq k ((t + k - c % k) % k) (t + k - c % k) :=
            Nat.mod_mod_of_dvd _ (Nat.dvd_refl k)
          have e2 : Nat.ModEq k ((t + k - c % k) % k + c) ((t + k - c % k) + c) :=
            Nat.ModEq.add_right c e1
          have e4 : Nat.ModEq k (t + k) t := Nat.add_mod_right t k
          have gc : Nat.ModEq k c (c % k) :=
            Nat.ModEq.symm (Nat.mod_mod_of_dvd c (Nat.dvd_refl k))
          have ee : Nat.ModEq k ((t + k - c % k) + c) ((t + k - c % k) + c % k) :=
            Nat.ModEq.add_left _ gc
          have g2 : (t + k - c % k) + c % k = t + k := by omega
          rw [g2] at ee
          have hchain : Nat.ModEq k ((t + k - c % k) % k + c) t := e2.trans (ee.trans e4)
          rw [hchain]
          exact Nat.mod_eq_of_lt htk⟩)
    (fun a ha => hstep a ha)

/-- HOL `SUM_AZIM_EQ_ANGLE_LE4_FUN` (AURSIPD.hl:100). `ff` is carried as an
explicit parameter (its HOL home was not locatable in the corpus). -/
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
  have hk3 : 3 < s.k := by omega
  have hk0 : 0 < s.k := by omega
  have hper : Periodic vv s.k := hBB.2.1
  have hinj : ∀ i j, i < s.k → j < s.k → i ≠ j → vv i ≠ vv j :=
    fun i j hi hj hne => VV_INJ_p35 s s.k vv rfl his hBB i j ⟨hi, hj, hne⟩
  have horbit : ∀ m, (rhoNode1_p18 FF)^[m] u = vv (m + p % s.k) := by
    have h := VV_SUC_EQ_RHO_NODE_PRIME_p35 s s.k (p % s.k) p 0 u V E FF vv
      rfl hu hV hE hFF his hk hBB
    exact h
  have hterm : ∀ i : ℕ,
      interiorAngle1 0 FF (vv i) = azimInFan_p18 (vv i, vv (i + 1)) E :=
    fun i => la18sz_vvInangleEq (by omega) hper hinj hE hFF i
  have hGper : Periodic
      (fun j => ff (vv j) * azimInFan_p18 (vv j, vv (j + 1)) E) s.k := by
    intro j
    show ff (vv (j + s.k)) * azimInFan_p18 (vv (j + s.k), vv (j + s.k + 1)) E
      = ff (vv j) * azimInFan_p18 (vv j, vv (j + 1)) E
    rw [hper j, Nat.add_right_comm j s.k 1, hper (j + 1)]
  have hL : setSum {i | i < s.k}
      (fun i => ff (vv (i + p % s.k)) *
        interiorAngle1 0 FF ((rhoNode1_p18 FF)^[i] u))
      = ∑ i ∈ Finset.range s.k,
          (fun j => ff (vv j) * azimInFan_p18 (vv j, vv (j + 1)) E)
            (i + p % s.k) := by
    rw [la18sz_setSum_Iio]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [horbit i, hterm (i + p % s.k)]
  have hR : setSum FF (fun e => ff e.1 * azimInFan_p18 e E)
      = ∑ i ∈ Finset.range s.k,
          (fun j => ff (vv j) * azimInFan_p18 (vv j, vv (j + 1)) E) i := by
    rw [← hFF, la18sz_setSum_FF vv (fun e => ff e.1 * azimInFan_p18 e E) s.k hk0 hper hinj]
  rw [hL, hR]
  exact la18sz_sum_shift _ s.k (p % s.k) hk0 hGper

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

/-! ## Section C aux: AURSIPD assembly kit (lane la18-aursipd-w1) -/

private theorem la18au_azimInFan_p18_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hLF : LocalFan V E FF) {d : V3 × V3} (hd : d ∈ FF) :
    azimInFan_p18 d E = azimInFan d E := by
  have hfan : Fan.FAN 0 V E := hLF.1
  obtain ⟨-, d0, hd0, -, -, hsub, -⟩ := localFan_data hLF
  have hdart : d ∈ Fan.dart1OfFan V E := hsub hd
  have hdE : ({d.1, d.2} : Set V3) ∈ E := hdart
  have hw : d.2 ∈ Fan.setOfEdge d.1 V E := by
    rw [← Fan.properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan]
    exact hdE
  have hso : Fan.setOfEdge d.1 Set.univ E = Fan.setOfEdge d.1 V E := by
    rw [← EE_elim hfan d.1]
    simp [Fan.setOfEdge, EE_p2]
  have hsf : Fan.sigmaFan 0 Set.univ E d.1 d.2 = Fan.sigmaFan 0 V E d.1 d.2 := by
    unfold Fan.sigmaFan
    rw [hso]
  have hcyc : azimCycle_p18 (EE_p18 d.1 E) 0 d.1 d.2
      = azimCycle_p2 (Fan.setOfEdge d.1 V E) 0 d.1 d.2 := by
    rw [show EE_p18 d.1 E = Fan.setOfEdge d.1 V E from by
      rw [← EE_elim hfan d.1]; rfl]
    rfl
  unfold azimInFan_p18 azimInFan
  by_cases hnc : 1 < (EE_p18 d.1 E).ncard
  · have hnc2 : 1 < (ee d.1 E).ncard := hnc
    rw [if_pos hnc, if_pos hnc2, hcyc, AZIM_CYCLE_EQ_SIGMA_FAN_ALT hfan hw, ← hsf]
  · have hnc2 : ¬ 1 < (ee d.1 E).ncard := hnc
    rw [if_neg hnc, if_neg hnc2]

/-- Arc propagation: along a run of straight (`azim = π`) vertices, all vertices
of the run lie in the plane through `0`, `v a`, `v (a+1)`. -/
private theorem la18au_arc_mem (v : ℕ → V3) (k a b : ℕ)
    (hk3 : 3 < k) (hper : Periodic v k)
    (hinj : ∀ x y, x < k → y < k → x ≠ y → v x ≠ v y)
    (hgen : ∀ x y : ℕ, v x ≠ v y → ¬ Collinear ℝ ({0, v x, v y} : Set V3))
    (hflat : ∀ t, a < t → t < b →
      azim 0 (v t) (v (t + 1)) (v (t + (k - 1))) = Real.pi)
    (_hb : b < a + k) :
    ∀ t, a ≤ t → t ≤ b → v t ∈ affineSpan ℝ ({0, v a, v (a + 1)} : Set V3) := by
  have hk0 : 0 < k := by omega
  let P : AffineSubspace ℝ V3 := affineSpan ℝ ({0, v a, v (a + 1)} : Set V3)
  have hva : v a ∈ P := mem_affineSpan ℝ (by simp)
  have hva1 : v (a + 1) ∈ P := mem_affineSpan ℝ (by simp)
  have hstep : ∀ t, a + 1 ≤ t → t < b → v (t - 1) ∈ P → v t ∈ P → v (t + 1) ∈ P := by
    intro t hat htb hprev hvt
    have hflat_t := hflat t (by omega) htb
    have hper1 : v (t + (k - 1)) = v (t - 1) := by
      have he : t + (k - 1) = (t - 1) + k := by omega
      rw [he, hper (t - 1)]
    have hcop0 : Coplanar ({0, v t, v (t + 1), v (t - 1)} : Set V3) :=
      AZIM_EQ_0_PI_IMP_COPLANAR 0 (v t) (v (t + 1)) (v (t - 1))
        (Or.inr (by rw [← hper1]; exact hflat_t))
    have hcop : Coplanar ({v (t + 1), 0, v t, v (t - 1)} : Set V3) := by
      have hs : ({v (t + 1), 0, v t, v (t - 1)} : Set V3) = {0, v t, v (t + 1), v (t - 1)} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hs]
      exact hcop0
    have hne : v t ≠ v (t - 1) := by
      intro heq
      have hmod : t % k = (t - 1) % k := by
        by_contra hne'
        exact hinj (t % k) ((t - 1) % k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) hne'
          (by rw [periodic_mod_eq_p23 hper t, periodic_mod_eq_p23 hper (t - 1)]; exact heq)
      have hA : (t % k + 1) % k = ((t - 1) % k + 1) % k := by rw [hmod]
      have hB : ((t - 1) % k + 1) % k = ((t - 1) + 1) % k := by
        rw [Nat.add_mod (t - 1) 1 k, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
      have hC : ((t - 1) + 1) % k = t % k := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ t)]
      have hmodstep : (t % k + 1) % k = t % k := hA.trans (hB.trans hC)
      rcases lt_or_ge (t % k + 1) k with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hmodstep
        omega
      · have hr : t % k < k := Nat.mod_lt _ hk0
        have heqk : t % k + 1 = k := by omega
        rw [heqk, Nat.mod_self] at hmodstep
        omega
    have hnc : ¬ Collinear ℝ ({0, v t, v (t - 1)} : Set V3) := hgen t (t - 1) hne
    have hmem := coplanar_in_affine_hull_p14 0 (v t) (v (t - 1)) (v (t + 1)) hnc hcop
    have hle : affineSpan ℝ ({0, v t, v (t - 1)} : Set V3) ≤ P := by
      rw [affineSpan_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact hvt
      · exact hprev
    exact hle hmem
  have hmain : ∀ t, a + 1 ≤ t → t ≤ b → v t ∈ P := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro hat htb
      by_cases ht : t = a + 1
      · rw [ht]
        exact hva1
      · have ht2 : a + 2 ≤ t := by omega
        have hb1 : t - 1 < b := by omega
        have h1 : a + 1 ≤ t - 1 := by omega
        have hprev : v ((t - 1) - 1) ∈ P := by
          rcases Nat.eq_or_lt_of_le (by omega : a ≤ (t - 1) - 1) with heq | hlt
          · rw [← heq]
            exact hva
          · exact ih ((t - 1) - 1) (by omega) (by omega) (by omega)
        have hvt : v (t - 1) ∈ P := by
          rcases Nat.eq_or_lt_of_le h1 with heq | hlt
          · rw [← heq]
            exact hva1
          · exact ih (t - 1) (by omega) h1 (by omega)
        have hstepv := hstep (t - 1) h1 hb1 hprev hvt
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hstepv
  intro t hat htb
  rcases Nat.eq_or_lt_of_le hat with heq | hlt
  · rw [← heq]
    exact hva
  · exact hmain t (by omega) htb

/-- HOL `AURSIPD` (AURSIPD.hl:218): the stratum-count bound. Giant. -/
theorem AURSIPD_p18 : ∀ (s : ScsV39) (v : ℕ → V3),
    3 < s.k → isScsV39 s → scsGeneric v → v ∈ MMsV39 s →
    3 + {i : ℕ | i < s.k ∧ scsIsStr s v i}.ncard ≤ s.k := by
  intro s v hk3 his hgen0 hMM
  classical
  let V : Set V3 := Set.range v
  let E : Set (Set V3) := Set.range fun i : ℕ => ({v i, v (i + 1)} : Set V3)
  let FF : Set (V3 × V3) := Set.range fun i : ℕ => (v i, v (i + 1))
  have hk0 : 0 < s.k := by omega
  have hBB : BBsV39 s v := by
    have h := hMM
    simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
    exact h.1.1.1
  have hta : taustarV39 s v < 0 := by
    have h := hMM
    simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
    exact h.1.1.2.2
  have hper : Periodic v s.k := hBB.2.1
  have hinj : ∀ i j, i < s.k → j < s.k → i ≠ j → v i ≠ v j := by
    intro i j hi hj hne
    exact VV_INJ_p35 s s.k v rfl his hBB i j ⟨hi, hj, hne⟩
  have hclf : ConvexLocalFan V E FF := by
    rcases hBB.2.2.2 with hle | hcf
    · omega
    · exact hcf
  have hedge : ∀ u ∈ V, ∃ w, {u, w} ∈ E := by
    rintro u ⟨i, rfl⟩
    exact ⟨v (i + 1), ⟨i, rfl⟩⟩
  have hlf2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hclf.1 hedge
  have hgen : Generic V E := hgen0
  have hgen_ncol : ∀ x y : ℕ, v x ≠ v y → ¬ Collinear ℝ ({0, v x, v y} : Set V3) := by
    intro x y hxy
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 V E FF (v x) (v y) hclf.1
      (Set.mem_range.mpr ⟨x, rfl⟩) (Set.mem_range.mpr ⟨y, rfl⟩) hxy hgen
  have hsol : solLocal E FF < Real.pi := by
    have h := JKQEWGV1_p23 s v his hk3 hBB hta
    simpa only [Set.image_univ] using h
  have hdiag : scsDiag s.k 0 2 := by
    unfold scsDiag
    have h1 : 1 % s.k = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : 2 % s.k = 2 := Nat.mod_eq_of_lt (by omega)
    have h3 : 3 % s.k = 3 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.zero_mod, h1, h2, h3]
    omega
  have hcardV : V.ncard = s.k := CARD_V_EQ_SCS_K_p35 s s.k 0 2 V v rfl rfl his hdiag hBB
  have hcardFF : FF.ncard = s.k := by
    rw [LOFA_IMP_CARD_FF_V_EQ hlf2, hcardV]
  have hrho : ∀ i, rhoNode1 FF (v i) = v (i + 1) := by
    intro i
    exact DETER_RHO_NODE hlf2 (v := v i) (w := v (i + 1)) (Set.mem_range.mpr ⟨i, rfl⟩)
  have horbit : ∀ p1 m : ℕ, (rhoNode1 FF)^[m] (v p1) = v (m + p1) := by
    intro p1 m
    exact VV_SUC_EQ_RHO_NODE_PRIME_p35 s s.k p1 0 0 (v p1) V E FF v
      rfl rfl rfl rfl rfl his (by omega) hBB m
  have hivs : ∀ i, ivsRhoNode1 FF (v i) = v (i + (s.k - 1)) := by
    intro i
    have h1 := ITER_CARD_MINUS1_EQ_IVS_RN1 hlf2 (v := v i) (Set.mem_range.mpr ⟨i, rfl⟩)
    rw [hcardV] at h1
    have h2 : (rhoNode1_p2 FF)^[s.k - 1] (v i) = v (s.k - 1 + i) := horbit i (s.k - 1)
    rw [h2, Nat.add_comm (s.k - 1) i] at h1
    exact h1.symm
  let a : ℕ → ℝ := fun i => interiorAngle1 0 FF (v i)
  have hstr_angle : ∀ i, scsIsStr s v i → a i = Real.pi := by
    intro i hstr
    have h1 : a i = azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1))) := by
      unfold a interiorAngle1
      rw [hrho i, hivs i]
    exact h1.trans hstr
  have hanle : ∀ i, 0 ≤ a i := by
    intro i
    unfold a interiorAngle1
    exact azim_nonneg _ _ _ _
  have hiter0 : ∀ i, (rhoNode1_p18 FF)^[i] (v 0) = v i := by
    intro i
    exact horbit 0 i
  have hSUM0 := SUM_AZIM_EQ_ANGLE_LE4_FUN_p18 (fun _ => (1:ℝ)) s v 0 (v 0) V E FF
    (by omega) hBB his (by simp) rfl rfl rfl
  have hSUM : setSum {i : ℕ | i < s.k} a = setSum FF (fun e => azimInFan_p18 e E) := by
    simpa [a, hiter0] using hSUM0
  have hfoldL : setSum {i : ℕ | i < s.k} a = ∑ i ∈ Finset.range s.k, a i :=
    la18sz_setSum_Iio a s.k
  have hfoldFF : setSum FF (fun e => azimInFan_p18 e E)
      = ∑ i ∈ Finset.range s.k, azimInFan_p18 (v i, v (i + 1)) E := by
    change setSum (Set.range fun i : ℕ => (v i, v (i + 1)))
      (fun e => azimInFan_p18 e E) = _
    exact la18sz_setSum_FF v (fun e => azimInFan_p18 e E) s.k hk0 hper hinj
  have hsum_p18 : (∑ i ∈ Finset.range s.k, a i)
      = ∑ i ∈ Finset.range s.k, azimInFan_p18 (v i, v (i + 1)) E := by
    rw [← hfoldL, hSUM, hfoldFF]
  have hsum_canon : (∑ i ∈ Finset.range s.k, a i)
      = ∑ i ∈ Finset.range s.k, azimInFan (v i, v (i + 1)) E := by
    rw [hsum_p18]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact la18au_azimInFan_p18_eq hclf.1 (Set.mem_range.mpr ⟨i, rfl⟩)
  have hsol_eq : solLocal E FF
      = 2 * Real.pi + (∑ i ∈ Finset.range s.k, a i) - (s.k : ℝ) * Real.pi := by
    unfold solLocal
    have hsub : setSum FF (fun e => azimInFan e E - Real.pi)
        = ∑ i ∈ Finset.range s.k, (azimInFan (v i, v (i + 1)) E - Real.pi) := by
      change setSum (Set.range fun i : ℕ => (v i, v (i + 1)))
        (fun e => azimInFan e E - Real.pi) = _
      exact la18sz_setSum_FF v (fun e => azimInFan e E - Real.pi) s.k hk0 hper hinj
    rw [hsub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hsum' : (∑ i ∈ Finset.range s.k, azimInFan (v i, v (i + 1)) E)
        = ∑ i ∈ Finset.range s.k, a i := hsum_canon.symm
    rw [hsum']
    simp only [nsmul_eq_mul]
    ring
  have hsum_expr : (∑ i ∈ Finset.range s.k, a i)
      = ((s.k : ℝ) - 2) * Real.pi + solLocal E FF := by
    have h := hsol_eq
    linarith
  have htotal_lt : (∑ i ∈ Finset.range s.k, a i) < ((s.k : ℝ) - 1) * Real.pi := by
    rw [hsum_expr]
    nlinarith [hsol, Real.pi_pos]
  have hsum_ge : ∀ (St : Finset ℕ), St ⊆ Finset.range s.k →
      (∀ i ∈ St, scsIsStr s v i) → (St.card : ℝ) * Real.pi ≤ ∑ i ∈ Finset.range s.k, a i := by
    intro St hsub hstr
    have h1 : (∑ i ∈ St, a i) = (St.card : ℝ) * Real.pi := by
      calc (∑ i ∈ St, a i) = ∑ i ∈ St, Real.pi :=
            Finset.sum_congr rfl (fun i hi => hstr_angle i (hstr i hi))
        _ = (St.card : ℝ) * Real.pi := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ i ∈ St, a i) ≤ ∑ i ∈ Finset.range s.k, a i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hanle i)
    linarith
  set St : Finset ℕ := (Finset.range s.k).filter (fun i => scsIsStr s v i) with hStdef
  set Tt : Finset ℕ := (Finset.range s.k).filter (fun i => ¬ scsIsStr s v i) with hTtdef
  have hSTcard : St.card + Tt.card = s.k := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range s.k) (p := fun i => scsIsStr s v i)
    simpa [hStdef, hTtdef, Finset.card_range] using h
  have hcard_le : St.card ≤ s.k := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun i => scsIsStr s v i) (Finset.range s.k))
    simpa [hStdef, Finset.card_range] using h
  have hgoal : 3 + St.card ≤ s.k := by
    by_contra hcon
    push_neg at hcon
    have hcases : St.card = s.k - 2 ∨ St.card = s.k - 1 ∨ St.card = s.k := by omega
    rcases hcases with h2 | h1c | h0c
    · -- exactly two exceptions: all other turns are straight, forcing coplanarity
      have hTt2 : Tt.card = 2 := by
        have := hSTcard
        omega
      obtain ⟨i0, j0, hi0j0, hTt_eq0⟩ := Finset.card_eq_two.mp hTt2
      have geo : ∀ p q : ℕ, p < q → Tt = {p, q} → False := by
        intro p q hpq hTt_eq
        have hpk : p < s.k := by
          have hmem : p ∈ Tt := by rw [hTt_eq]; simp
          have h := (Finset.mem_filter.mp hmem).1
          simpa using h
        have hqk : q < s.k := by
          have hmem : q ∈ Tt := by rw [hTt_eq]; simp
          have h := (Finset.mem_filter.mp hmem).1
          simpa using h
        have hflat : ∀ t, t < s.k → t ≠ p → t ≠ q → scsIsStr s v t := by
          intro t htk htp htq
          by_contra hnt
          have hmem : t ∈ Tt := by
            rw [hTtdef, Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr htk, hnt⟩
          rw [hTt_eq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h
          · exact htp h
          · exact htq h
        have hflat1 : ∀ t, p < t → t < q →
            azim 0 (v t) (v (t + 1)) (v (t + (s.k - 1))) = Real.pi := by
          intro t hpt htq
          exact hflat t (by omega) (by omega) (by omega)
        have hflat2 : ∀ t, q < t → t < p + s.k →
            azim 0 (v t) (v (t + 1)) (v (t + (s.k - 1))) = Real.pi := by
          intro t hqt htp
          have htmod : t % s.k < s.k := Nat.mod_lt _ hk0
          have hnei : t % s.k ≠ p := by
            intro heq
            have ht_eq : t = s.k * (t / s.k) + p := by
              rw [← heq]
              exact (Nat.div_add_mod t s.k).symm
            have ht_i : t - p = s.k * (t / s.k) := by omega
            have hpos : 0 < t - p := by omega
            have hlt' : t - p < s.k := by omega
            have hdvd : s.k ∣ t - p := ⟨t / s.k, by rw [ht_i]⟩
            have hle := Nat.le_of_dvd hpos hdvd
            omega
          have hnej : t % s.k ≠ q := by
            intro heq
            have ht_eq : t = s.k * (t / s.k) + q := by
              rw [← heq]
              exact (Nat.div_add_mod t s.k).symm
            have ht_j : t - q = s.k * (t / s.k) := by omega
            have hpos : 0 < t - q := by omega
            have hlt' : t - q < s.k := by omega
            have hdvd : s.k ∣ t - q := ⟨t / s.k, by rw [ht_j]⟩
            have hle := Nat.le_of_dvd hpos hdvd
            omega
          have hstr := hflat (t % s.k) htmod hnei hnej
          have hv1 : v t = v (t % s.k) := (periodic_mod_eq_p23 hper t).symm
          have hv2 : v (t + 1) = v (t % s.k + 1) := by
            have hmod : (t + 1) % s.k = (t % s.k + 1) % s.k := by
              rw [Nat.add_mod t 1 s.k, Nat.mod_eq_of_lt (by omega : (1:ℕ) < s.k)]
            calc v (t + 1) = v ((t + 1) % s.k) := (periodic_mod_eq_p23 hper (t + 1)).symm
              _ = v ((t % s.k + 1) % s.k) := by rw [hmod]
              _ = v (t % s.k + 1) := periodic_mod_eq_p23 hper (t % s.k + 1)
          have hv3 : v (t + (s.k - 1)) = v (t % s.k + (s.k - 1)) := by
            have hmod : (t + (s.k - 1)) % s.k = (t % s.k + (s.k - 1)) % s.k := by
              rw [Nat.add_mod t (s.k - 1) s.k,
                Nat.mod_eq_of_lt (by omega : s.k - 1 < s.k)]
            calc v (t + (s.k - 1)) = v ((t + (s.k - 1)) % s.k) :=
                  (periodic_mod_eq_p23 hper (t + (s.k - 1))).symm
              _ = v ((t % s.k + (s.k - 1)) % s.k) := by rw [hmod]
              _ = v (t % s.k + (s.k - 1)) := periodic_mod_eq_p23 hper (t % s.k + (s.k - 1))
          rw [hv1, hv2, hv3]
          exact hstr
        have harc1 := la18au_arc_mem v s.k p q hk3 hper hinj hgen_ncol hflat1 (by omega)
        have harc2 := la18au_arc_mem v s.k q (p + s.k) hk3 hper hinj hgen_ncol hflat2 (by omega)
        have hP1_le : affineSpan ℝ ({0, v p, v (p + 1)} : Set V3)
            ≤ affineSpan ℝ ({0, v p, v q} : Set V3) := by
          rw [affineSpan_le]
          intro x hx
          rcases hx with rfl | rfl | rfl
          · exact mem_affineSpan ℝ (by simp)
          · exact mem_affineSpan ℝ (by simp)
          · have hnc : ¬ Collinear ℝ ({0, v p, v q} : Set V3) :=
              hgen_ncol p q (hinj p q hpk hqk (by omega))
            have hcop : Coplanar ({v (p + 1), 0, v p, v q} : Set V3) := by
              refine ⟨0, v p, v (p + 1), ?_⟩
              intro z hz
              rcases hz with rfl | rfl | rfl | rfl
              · exact mem_affineSpan ℝ (by simp)
              · exact mem_affineSpan ℝ (by simp)
              · exact mem_affineSpan ℝ (by simp)
              · exact harc1 q (by omega) (by omega)
            exact coplanar_in_affine_hull_p14 0 (v p) (v q) (v (p + 1)) hnc hcop
        have hQsub : affineSpan ℝ ({0, v q, v (q + 1)} : Set V3)
            ≤ affineSpan ℝ ({0, v p, v q} : Set V3) := by
          rw [affineSpan_le]
          intro x hx
          rcases hx with rfl | rfl | rfl
          · exact mem_affineSpan ℝ (by simp)
          · exact mem_affineSpan ℝ (by simp)
          · have hnc : ¬ Collinear ℝ ({0, v p, v q} : Set V3) :=
              hgen_ncol p q (hinj p q hpk hqk (by omega))
            have hcop : Coplanar ({v (q + 1), 0, v p, v q} : Set V3) := by
              refine ⟨0, v q, v (q + 1), ?_⟩
              intro z hz
              rcases hz with rfl | rfl | rfl | rfl
              · exact mem_affineSpan ℝ (by simp)
              · exact mem_affineSpan ℝ (by simp)
              · have hiQ : v (p + s.k) ∈ affineSpan ℝ ({0, v q, v (q + 1)} : Set V3) :=
                  harc2 (p + s.k) (by omega) (le_refl _)
                have hp_eq : v (p + s.k) = v p := hper p
                rw [hp_eq] at hiQ
                exact hiQ
              · exact mem_affineSpan ℝ (by simp)
            exact coplanar_in_affine_hull_p14 0 (v p) (v q) (v (q + 1)) hnc hcop
        have hPall : ∀ t, v t ∈ affineSpan ℝ ({0, v p, v q} : Set V3) := by
          intro t
          have htmod : t % s.k < s.k := Nat.mod_lt _ hk0
          have hvmod : v t = v (t % s.k) := (periodic_mod_eq_p23 hper t).symm
          rw [hvmod]
          by_cases hti : t % s.k < p
          · have hmem := harc2 (t % s.k + s.k) (by omega) (by omega)
            have heq : v (t % s.k + s.k) = v (t % s.k) := hper (t % s.k)
            rw [heq] at hmem
            exact hQsub hmem
          · have hge : p ≤ t % s.k := by omega
            by_cases hle : t % s.k ≤ q
            · exact hP1_le (harc1 (t % s.k) hge hle)
            · exact hQsub (harc2 (t % s.k) (by omega) (by omega))
        have hcopv : Coplanar ({0} ∪ Set.range v : Set V3) := by
          refine ⟨0, v p, v q, ?_⟩
          intro z hz
          rcases hz with rfl | hz
          · exact mem_affineSpan ℝ (by simp)
          · obtain ⟨t, rfl⟩ := hz
            exact hPall t
        exact (FEKTYIY_p27 s v his hMM hk3) hcopv
      rcases lt_or_gt_of_ne hi0j0 with hlt | hgt
      · exact geo i0 j0 hlt hTt_eq0
      · exact geo j0 i0 hgt (by
          rw [hTt_eq0]
          ext t
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto)
    · -- one exception
      have hge := hsum_ge St (by rw [hStdef]; exact Finset.filter_subset _ _)
        (fun i hi => by rw [hStdef] at hi; exact (Finset.mem_filter.mp hi).2)
      rw [h1c] at hge
      have hcast : ((s.k - 1 : ℕ) : ℝ) = (s.k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ s.k)]
        norm_num
      rw [hcast] at hge
      nlinarith [hge, htotal_lt, Real.pi_pos]
    · -- all str
      have hge := hsum_ge St (by rw [hStdef]; exact Finset.filter_subset _ _)
        (fun i hi => by rw [hStdef] at hi; exact (Finset.mem_filter.mp hi).2)
      rw [h0c] at hge
      nlinarith [hge, htotal_lt, Real.pi_pos]
  have hset : {i : ℕ | i < s.k ∧ scsIsStr s v i} = (St : Set ℕ) := by
    ext t
    rw [hStdef]
    simp
  rw [hset, Set.ncard_coe_finset]
  exact hgoal

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

/-! ### la18slice kit (lane la18-slice-w1, 2026-11-01): the CNICGSF slice
arrows closed natively as `LKGRQUI_p27` instances

The five `SCS_*_SLICE_*_p18` arrows discharge as direct `LKGRQUI_p27`
(LA27) instances: `STAB_*_SCS` supplies `isScsV39` of the stabilised
source, the in-file diag lemmas supply `scsDiag`, and the `isScsSliceV39`
slot is the half-table record identities below (PSORT/FUNLIST table
bashes, HOL CNICGSF.hl route — the same ten identities the LocalConcl
W-D landing carries privately; this file's copies make the five arrows
native, sorry-free donors again).  `la18slice_isScs_stab` is a copy of
LA24's private `la24isScs_stab` (deps public), `la18slice_STAB_5I1_SCS`
fills the one diag-stabilisation SCS lemma LA24 does not carry
(LA29's `STAB_5I1_SCS_p29` is not in this file's import cone). -/

private theorem la18slice_csAdj_far {a1 a2 : ℝ} {i j x y : ℕ} (hd : scsDiag 5 i j)
    (hxy : (i % 5 = x % 5 ∧ j % 5 = y % 5) ∨ (i % 5 = y % 5 ∧ j % 5 = x % 5)) :
    csAdj 5 a1 a2 x y = a2 := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [csAdj, ← h1, ← h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl
  · simp only [csAdj, ← h1, ← h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl

private theorem la18slice_isScs_stab (s : ScsV39) (i j : ℕ) (hd : scsDiag s.k i j)
    (hs : isScsV39 s)
    (hdom : ∀ u v, psort s.k (i, j) = psort s.k (u, v) → s.a u v ≤ cstab) :
    isScsV39 (scsStabDiagV39 s i j) := by
  have hk0 : s.k ≠ 0 := by have := hs.2.1; omega
  have hk2 : 1 < s.k := by have := hs.2.1; omega
  obtain ⟨hdd, hk1, hk6, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, hdiag0, h2a, hb3,
    hbc, -, -, hcard⟩ := hs
  have hpb1 : ∀ u v, s.b (u + s.k) v = s.b u v := fun u v => (hpb u v).1
  have hpb2 : ∀ u v, s.b u (v + s.k) = s.b u v := fun u v => (hpb u v).2
  set b' : ℕ → ℕ → ℝ := fun x y =>
    if psort s.k (i, j) = psort s.k (x, y) then cstab else s.b x y with hb'def
  rw [show scsStabDiagV39 s i j = mkUnadornedV39 s.k s.d s.a b' from by
    simp only [scsStabDiagV39, mkUnadornedV39, hb'def]]
  simp only [isScsV39, mkUnadornedV39]
  have psort_add1 : ∀ u v : ℕ, psort s.k (u + s.k, v) = psort s.k (u, v) := by
    intro u v
    rw [(PSORT_MOD s.k (u + s.k) v hk0).symm, Nat.add_mod_right, PSORT_MOD s.k u v hk0]
  have psort_add2 : ∀ u v : ℕ, psort s.k (u, v + s.k) = psort s.k (u, v) := by
    intro u v
    rw [(PSORT_MOD s.k u (v + s.k) hk0).symm, Nat.add_mod_right, PSORT_MOD s.k u v hk0]
  have hb'edge : ∀ u, b' u (u + 1) = s.b u (u + 1) := by
    intro u
    simp only [hb'def]
    rw [if_neg (diag_not_edge_psort_p20 u hk2 hd)]
  have hsymB' : ∀ u v, b' u v = b' v u := by
    intro u v
    simp only [hb'def]
    by_cases hcls : psort s.k (i, j) = psort s.k (u, v)
    · rw [if_pos hcls, psort_swap_p20 s.k v u, if_pos hcls]
    · rw [if_neg hcls, psort_swap_p20 s.k v u, if_neg hcls]
      exact (hsym u v).2.2.2.1
  have hpb' : Periodic2 b' s.k := by
    intro u v
    refine ⟨?_, ?_⟩
    · show b' (u + s.k) v = b' u v
      simp only [hb'def]
      rw [psort_add1, hpb1 u v]
    · show b' u (v + s.k) = b' u v
      simp only [hb'def]
      rw [psort_add2, hpb2 u v]
  have hdomcase : ∀ u v, s.a u v ≤ b' u v := by
    intro u v
    by_cases hcls : psort s.k (i, j) = psort s.k (u, v)
    · simp only [hb'def, if_pos hcls]
      exact hdom u v hcls
    · simp only [hb'def, if_neg hcls]
      exact (hch u v).1.trans ((hch u v).2.1.trans (hch u v).2.2)
  refine ⟨hdd, hk1, hk6, periodic_empty s.k, periodic_empty s.k, periodic_empty s.k,
    periodic_empty s.k, hpa, hpa, hpb', hpb', fun _ _ => ⟨rfl, rfl⟩,
    fun u v => ⟨(hsym u v).1, (hsym u v).1, hsymB' u v, hsymB' u v, trivial⟩,
    fun u v => ⟨le_refl _, hdomcase u v, le_refl _⟩, hdiag0, h2a,
    fun u h3 => by rw [hb'edge u]; exact hb3 u h3,
    fun u h3 => by rw [hb'edge u]; exact hbc u h3,
    fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
  simp only [hb'edge]
  exact hcard

/-- `STAB_5I1_SCS` (missing from LA24): diag-stabilisations of `scs5I1` are
SCS; the stab overrides the diag b-slot to `cstab` and the a-table far value
`2 * h0` is `≤ cstab` on the stabilised class. -/
private theorem la18slice_STAB_5I1_SCS (i j : ℕ) (hd : scsDiag scs5I1.k i j) :
    isScsV39 (scsStabDiagV39 scs5I1 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I1 i j) := by
  refine ⟨la18slice_isScs_stab scs5I1 i j hd SCS_5I1_IS_SCS ?_,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩⟩
  intro u v hcls
  rw [show scs5I1.k = 5 from rfl] at hcls
  show csAdj 5 2 (2 * h0) u v ≤ cstab
  rw [la18slice_csAdj_far hd (psort_eq_cases_p20 hcls)]
  norm_num [h0, cstab]

/-! ## wd copies of the LA18 rotation kit (LA18-privates are not visible) -/

private theorem la18slice_pair_eq02 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 2} ↔ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h2 : (2 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h2
    rcases h0 with ha | ha <;> rcases h2 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem la18slice_pair_eq03 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 3} ↔ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h3 : (3 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h3
    rcases h0 with ha | ha <;> rcases h3 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem la18slice_sing_ne02 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 2}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h2 : (2 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h2
  omega

private theorem la18slice_sing_ne03 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 3}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h3 : (3 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h3
  omega

/-! ## The ten half-table record bashes -/

private theorem la18slice_half_5I1_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5I1 0 2) 0 2 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs5I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5I1_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5I1 0 2) 2 0 0.3789 False =
      scsPropEquV39 scs4M2 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M2, scs5I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5I2_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5I2 0 2) 0 2 0.11 False =
      scsPropEquV39 scs3T1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3T1, scs5I2]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5I2_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5I2 0 2) 2 0 0.513 False =
      scsPropEquV39 scs4M3' 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M3', scs5I2]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5M1_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 2) 0 2 0.2759 False =
      scsPropEquV39 scs3T4 2 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3T4, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5M1_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 2) 2 0 0.3789 False =
      scsPropEquV39 scs4M2 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M2, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5M1_03_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 3) 0 3 0.513 False =
      scsPropEquV39 scs4M4' 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M4', scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5M1_03_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 3) 3 0 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5M1_24_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 2 4) 2 4 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq02, la18slice_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem la18slice_half_5M1_24_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 2 4) 4 2 0.513 False =
      scsPropEquV39 scs4M5' 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M5', scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, la18slice_pair_eq03, la18slice_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

/-- HOL `SCS_5I1_SLICE_02` (CNICGSF.hl:86). Giant (`LKGRQUI` lane). -/
theorem SCS_5I1_SLICE_02_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M2 1} := by
  have mkjF : (scsPropEquV39 scs3M1 1).J 0
      ((scsPropEquV39 scs3M1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5I1 0 2)
      (scsPropEquV39 scs3M1 1) (scsPropEquV39 scs4M2 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨la18slice_half_5I1_02_lo.symm, la18slice_half_5I1_02_hi.symm⟩
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.3789 : ℝ) < 0.9
      norm_num
    · show dTame 5 ≤ 0.103 + 0.3789
      norm_num [dTame]
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5I1 0 2) (scsPropEquV39 scs3M1 1)
    (scsPropEquV39 scs4M2 1) 0 2 0 0 True
    (la18slice_STAB_5I1_SCS 0 2 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

/-- HOL `SCS_5I2_SLICE_02` (CNICGSF.hl:237). Giant. -/
theorem SCS_5I2_SLICE_02_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2}
      {scsPropEquV39 scs3T1 1, scsPropEquV39 scs4M3' 1} := by
  have mkjF : (scsPropEquV39 scs3T1 1).J 0
      ((scsPropEquV39 scs3T1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5I2 0 2)
      (scsPropEquV39 scs3T1 1) (scsPropEquV39 scs4M3' 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨la18slice_half_5I2_02_lo.symm, la18slice_half_5I2_02_hi.symm⟩
    · show (0.11 : ℝ) < 0.9
      norm_num
    · show (0.513 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.11 + 0.513
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5I2 0 2) (scsPropEquV39 scs3T1 1)
    (scsPropEquV39 scs4M3' 1) 0 2 0 0 True
    (STAB_5I2_SCS 0 2 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

/-- HOL `SCS_5M1_SLICE_02` (CNICGSF.hl:400). Giant. -/
theorem SCS_5M1_SLICE_02_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2}
      {scsPropEquV39 scs3T4 2, scsPropEquV39 scs4M2 1} := by
  have mkjF : (scsPropEquV39 scs3T4 2).J 0
      ((scsPropEquV39 scs3T4 2).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5M1 0 2)
      (scsPropEquV39 scs3T4 2) (scsPropEquV39 scs4M2 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨la18slice_half_5M1_02_lo.symm, la18slice_half_5M1_02_hi.symm⟩
    · show (0.2759 : ℝ) < 0.9
      norm_num
    · show (0.3789 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.2759 + 0.3789
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5M1 0 2) (scsPropEquV39 scs3T4 2)
    (scsPropEquV39 scs4M2 1) 0 2 0 0 True
    (STAB_5M1_SCS 0 2 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

/-- HOL `SCS_5M1_SLICE_03` (CNICGSF.hl:552). Giant. -/
theorem SCS_5M1_SLICE_03_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3}
      {scsPropEquV39 scs4M4' 1, scsPropEquV39 scs3M1 1} := by
  have mkjF : (scsPropEquV39 scs4M4' 1).J 0
      ((scsPropEquV39 scs4M4' 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5M1 0 3)
      (scsPropEquV39 scs4M4' 1) (scsPropEquV39 scs3M1 1) 0 3 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨la18slice_half_5M1_03_lo.symm, la18slice_half_5M1_03_hi.symm⟩
    · show (0.513 : ℝ) < 0.9
      norm_num
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.513 + 0.103
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5M1 0 3) (scsPropEquV39 scs4M4' 1)
    (scsPropEquV39 scs3M1 1) 0 3 0 0 True
    (STAB_5M1_SCS 0 3 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

/-- HOL `SCS_5M1_SLICE_24` (CNICGSF.hl:729). Giant. -/
theorem SCS_5M1_SLICE_24_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M5' 1} := by
  have mkjF : (scsPropEquV39 scs3M1 1).J 0
      ((scsPropEquV39 scs3M1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5M1 2 4)
      (scsPropEquV39 scs3M1 1) (scsPropEquV39 scs4M5' 1) 2 4 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨la18slice_half_5M1_24_lo.symm, la18slice_half_5M1_24_hi.symm⟩
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.513 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.103 + 0.513
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5M1 2 4) (scsPropEquV39 scs3M1 1)
    (scsPropEquV39 scs4M5' 1) 2 4 0 0 True
    (STAB_5M1_SCS 2 4 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

/-! ### Rotation kit for the `CNICGSF` arrows

`funlistV39`-table registries are `k`-periodic, so a double `scsPropEquV39`
rotation by `i` then `m` with `i + m ≡ 0 (mod k)` returns the original system.
This is the in-file `PRO_EQU_ID1` instance used by the HOL `CNICGSF*` proofs
(the general LocalAuto12 `PRO_EQU_ID1` is not importable next to LocalAuto1). -/

private theorem funlistV39_add_period_p18 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (k j j' : ℕ) :
    funlistV39 data d k (k + j) (k + j') = funlistV39 data d k j j' := by
  unfold funlistV39 psort
  have h1 : (k + j) % k = j % k := by
    rw [Nat.add_comm k j]
    simpa using (Nat.add_mul_mod_self_left j 1 k)
  have h2 : (k + j') % k = j' % k := by
    rw [Nat.add_comm k j']
    simpa using (Nat.add_mul_mod_self_left j' 1 k)
  rw [h1, h2]

private theorem funlistV39_add_mul_period_p18 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (k c j j' : ℕ) :
    funlistV39 data d k (k * c + j) (k * c + j') = funlistV39 data d k j j' := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show k * (c + 1) + j = k + (k * c + j) from by ring,
        show k * (c + 1) + j' = k + (k * c + j') from by ring,
        funlistV39_add_period_p18, ih]

private theorem propEqu_propEqu_mkUnadorned_p18 (k : ℕ) (d : ℝ)
    (data1 : List ((ℕ × ℕ) × ℝ)) (d1 : ℝ) (data2 : List ((ℕ × ℕ) × ℝ)) (d2 : ℝ)
    (i m c : ℕ) (h : i + m = k * c) :
    scsPropEquV39 (scsPropEquV39
        (mkUnadornedV39 k d (funlistV39 data1 d1 k) (funlistV39 data2 d2 k)) i) m
      = mkUnadornedV39 k d (funlistV39 data1 d1 k) (funlistV39 data2 d2 k) := by
  rw [ScsV39.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    ext j j'
    simp only [scsPropEquV39, mkUnadornedV39]
    rw [show i + (m + j) = k * c + j from by omega,
        show i + (m + j') = k * c + j' from by omega]
    exact funlistV39_add_mul_period_p18 _ _ k c j j'

/-- Two-element union of arrows (`FZIOTEF_UNION` at singletons; the LocalAuto20
copy is not importable next to LocalAuto1). -/
private theorem scsArrowV39_pair_union_p18 {a b c d : ScsV39}
    (h1 : scsArrowV39 {a} {b}) (h2 : scsArrowV39 {c} {d}) :
    scsArrowV39 {a, c} {b, d} := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hs with h | h
    · rw [h]; exact h1.1 b (by simp)
    · rw [h]; exact h2.1 d (by simp)
  · rcases h1.2 with h1e | ⟨s, hs, hne⟩
    · rcases h2.2 with h2e | ⟨t, ht, hne'⟩
      · left
        intro u hu
        rcases hu with h | h
        · rw [h]; exact h1e a (by simp)
        · rw [h]; exact h2e c (by simp)
      · exact Or.inr ⟨t, Or.inr (Set.mem_singleton_iff.mp ht), hne'⟩
    · exact Or.inr ⟨s, Or.inl (Set.mem_singleton_iff.mp hs), hne⟩

/-- Rewrite the target of a singleton arrow along an equality of systems. -/
private theorem scsArrowV39_lift_p18 {a b b' : ScsV39} (h : scsArrowV39 {a} {b'})
    (heq : b' = b) : scsArrowV39 {a} {b} := by rw [← heq]; exact h

/-- HOL `CNICGSF1` (CNICGSF.hl:207). Composes the `(0,2)`-slice arrow with the
`scsPropEquV39`-rotations of the `scs3M1`/`scs4M2` terminals back to their
unrotated forms (HOL `PRO_EQU_ID1`/`YXIONXL3` route). -/
theorem CNICGSF1_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs3M1, scs4M2} := by
  have his1 : isScsV39 (scsPropEquV39 scs3M1 1) := SCS_5I1_SLICE_02_p18.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M2 1) := SCS_5I1_SLICE_02_p18.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    propEqu_propEqu_mkUnadorned_p18 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M2 1) 3 = scs4M2 :=
    propEqu_propEqu_mkUnadorned_p18 4 0.3789
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  exact FZIOTEF_TRANS _ _ _ SCS_5I1_SLICE_02_p18
    (scsArrowV39_pair_union_p18 (scsArrowV39_lift_p18 (YXIONXL3_concl _ 2 his1) heq1)
      (scsArrowV39_lift_p18 (YXIONXL3_concl _ 3 his2) heq2))
  -- NEEDS: SCS_5I1_SLICE_02_p18 (above, still sorried: LKGRQUI lane) +
  -- LocalAuto1.YXIONXL3_concl (importable, discharged at assembly by
  -- LocalAuto12.YXIONXL3); the rotation identity is the in-file
  -- `propEqu_propEqu_mkUnadorned_p18` (PRO_EQU_ID1 twin).

/-- HOL `CNICGSF2` (CNICGSF.hl:361). Same route as `CNICGSF1_p18` with the
`(0,2)`-slice of `scs5I2`. -/
theorem CNICGSF2_p18 :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs3T1, scs4M3'} := by
  have his1 : isScsV39 (scsPropEquV39 scs3T1 1) := SCS_5I2_SLICE_02_p18.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M3' 1) := SCS_5I2_SLICE_02_p18.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3T1 1) 2 = scs3T1 := by
    have h := propEqu_propEqu_mkUnadorned_p18 3 0.11
      [((0, 1), Real.sqrt 8)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
    rwa [← scs_3T1] at h
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M3' 1) 3 = scs4M3' :=
    propEqu_propEqu_mkUnadorned_p18 4 0.513
      [((0, 1), Real.sqrt 8), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  exact FZIOTEF_TRANS _ _ _ SCS_5I2_SLICE_02_p18
    (scsArrowV39_pair_union_p18 (scsArrowV39_lift_p18 (YXIONXL3_concl _ 2 his1) heq1)
      (scsArrowV39_lift_p18 (YXIONXL3_concl _ 3 his2) heq2))
  -- NEEDS: SCS_5I2_SLICE_02_p18 (still sorried) + LocalAuto1.YXIONXL3_concl.

/-- HOL `CNICGSF3` (CNICGSF.hl:527). Same route with the `(0,2)`-slice of
`scs5M1`; note the `scs3T4` terminal is reached by a `2`-rotation. -/
theorem CNICGSF3_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs3T4, scs4M2} := by
  have his1 : isScsV39 (scsPropEquV39 scs3T4 2) := SCS_5M1_SLICE_02_p18.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M2 1) := SCS_5M1_SLICE_02_p18.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3T4 2) 1 = scs3T4 :=
    propEqu_propEqu_mkUnadorned_p18 3 0.2759
      [((0, 1), 2)] (2 * h0) [((0, 1), 2 * h0)] cstab 2 1 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M2 1) 3 = scs4M2 :=
    propEqu_propEqu_mkUnadorned_p18 4 0.3789
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  exact FZIOTEF_TRANS _ _ _ SCS_5M1_SLICE_02_p18
    (scsArrowV39_pair_union_p18 (scsArrowV39_lift_p18 (YXIONXL3_concl _ 1 his1) heq1)
      (scsArrowV39_lift_p18 (YXIONXL3_concl _ 3 his2) heq2))
  -- NEEDS: SCS_5M1_SLICE_02_p18 (still sorried) + LocalAuto1.YXIONXL3_concl.

/-- HOL `CNICGSF4` (CNICGSF.hl:696). Same route with the `(0,3)`-slice of
`scs5M1`. -/
theorem CNICGSF4_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1} := by
  have his1 : isScsV39 (scsPropEquV39 scs4M4' 1) := SCS_5M1_SLICE_03_p18.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs3M1 1) := SCS_5M1_SLICE_03_p18.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs4M4' 1) 3 = scs4M4' :=
    propEqu_propEqu_mkUnadorned_p18 4 0.513
      [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1
      (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    propEqu_propEqu_mkUnadorned_p18 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  exact FZIOTEF_TRANS _ _ _ SCS_5M1_SLICE_03_p18
    (scsArrowV39_pair_union_p18 (scsArrowV39_lift_p18 (YXIONXL3_concl _ 3 his1) heq1)
      (scsArrowV39_lift_p18 (YXIONXL3_concl _ 2 his2) heq2))
  -- NEEDS: SCS_5M1_SLICE_03_p18 (still sorried) + LocalAuto1.YXIONXL3_concl.

/-- HOL `CNICGSF5` (CNICGSF.hl:876). Same route with the `(2,4)`-slice of
`scs5M1`. -/
theorem CNICGSF5_p18 :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs3M1, scs4M5'} := by
  have his1 : isScsV39 (scsPropEquV39 scs3M1 1) := SCS_5M1_SLICE_24_p18.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M5' 1) := SCS_5M1_SLICE_24_p18.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    propEqu_propEqu_mkUnadorned_p18 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M5' 1) 3 = scs4M5' :=
    propEqu_propEqu_mkUnadorned_p18 4 0.513
      [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1
      (by norm_num)
  exact FZIOTEF_TRANS _ _ _ SCS_5M1_SLICE_24_p18
    (scsArrowV39_pair_union_p18 (scsArrowV39_lift_p18 (YXIONXL3_concl _ 2 his1) heq1)
      (scsArrowV39_lift_p18 (YXIONXL3_concl _ 3 his2) heq2))
  -- NEEDS: SCS_5M1_SLICE_24_p18 (still sorried) + LocalAuto1.YXIONXL3_concl.

end Kepler.Text

/- EV32 (lane la18-slice-w1): the five slice arrows must be standard-three. -/
#print axioms Kepler.Text.SCS_5I1_SLICE_02_p18
#print axioms Kepler.Text.SCS_5I2_SLICE_02_p18
#print axioms Kepler.Text.SCS_5M1_SLICE_02_p18
#print axioms Kepler.Text.SCS_5M1_SLICE_03_p18
#print axioms Kepler.Text.SCS_5M1_SLICE_24_p18


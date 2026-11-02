/-
LocalAuto23 — Local Fan chapter appendix leftovers, two-file bundle
(skeleton-first pass):

  - `scripts/local/JOTSWIX.hl` (3922 ln, 20 thms; H. L. Truong / T. Hales
    main-work leftovers) — the `taum` attain-inf / extremal / std-pos kit,
    the `scs_3I1` arrow `LFLACKU`, the `s_init_list_v39` explicit-list
    identity, the `JEJTVGB` arrow-case breakdown (the full registry
    conjunction ending in `JEJTVGB_assume_v39`), the mod-4 / periodic
    injectivity arithmetic kit, the three `ab4_assumption_reduction`
    deform variants, `deform_azim_sum`, the quad endpoint lemmas
    `NEHXMWH` / `BZQNDMN` / `JOTSWIX`, the pentagon `LEMMA_PWE1..4`
    and the dihedral registry bound `LINDIH_11`.
  - `scripts/local/JKQEWGV.hl` (3307 ln, 26 thms; H. L. Truong 2012) — the
    `stable_system` / `tri_stable` realisability of an scs (`IS_SCS_STABLE_SYSTEM`,
    `IS_SCS_TRI_STABLE_SYSTEM`), the `V_SY`/`E_SY`/`F_SY` image identifications
    and `B_SY1` membership for k = 3,4,5,6 (`V_E_FF_IS_SCS_CASES_*`,
    `IN_IS_SCS_CASES_*`), the `taustar_v39 = tau_star` bridge at the matvec
    (`TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_*`), `IS_EAR_V25_EQ_EAR_SY`, and the
    main local-fan conclusions `JKQEWGV1*` (`sol_local < pi`),
    `JKQEWGV2*` (`~circular`), `JKQEWGV3` (lunar interior angle < pi/2),
    plus the `IS_SCS_POINT_IN_BBS_IS_NOT_0*` / `IS_SCS_NOT_COLLINEAR_*` kit.

FILE MAP
  Section 0 (`_p23` substrate; see ENCODING): `torsor_p23`,
    (DEDUP 2026-09-19: the former `deltaX4_p23`, `deltaY_p23`, `dihY_p23`,
    `taum_p23` registry-twin block is deleted — verbatim-equal to the
    canonical `deltaX4`/`deltaY`/`dihY`/`taum` of
    `Kepler.Text.SphereKit`, now imported; use sites renamed),
    `constraintSystem_p23`, `stableSystem_p23`, `StableSyP23`,
    `aEar0_p23`, `bEar0_p23`, `earSy_p23`, `rowSy_p23`, `J1_SY_p23`,
    `dFun_p23`, `tauStar_p23`, `cycRow_p23` (the HOL row vector
    `vector[vv 1;..;vv k;vv 0]` read 0-based), `scsJSet_p23`
    (`change_type_v2 (scs_J_v39 s) k`), `scsToStableSy_p23` (the
    `stable_sy (...) = s1` record; SF-81 案①: moved to Section B — it cites
    `IS_SCS_STABLE_SYSTEM_p23` as its `stable` field evidence, so it postdates
    that theorem; SF-C3: the `d` slot carries `s.d` (FIDELITY-FIX, see the
    def docstring)), `ballAnnulus_ne_0_p23`,
    `periodic_mod_eq_p23`, `range_periodic_image_p23`.
  Section A (JOTSWIX): `taum_attains_inf_p23`, `TAUM_EXTREMAL_p23`,
    `TAUM_STD_POS_p23`, `LFLACKU_p23` (sorry; need the
    `taustar_taum_dfun` bridge), `s_init_list_alt_p23` (proved),
    `JEJTVGB_case_breakdown_p23` (sorry; twin of LocalAuto16's),
    `MOD_4_CASES_p23` (proved), `ab4_assumption_reduction_p23`,
    `PERIODIC_INJ_MOD_p23` (proved),
    `ab4_assumption_reduction2_p23` / `_sym_p23`, `deform_azim_sum_p23`,
    `NEHXMWH_p23`, `BZQNDMN_p23`, `JOTSWIX_p23`, `LEMMA_PWE1_p23`,
    `LEMMA_PWE2_p23`, `LINDIH_11_p23`, `LEMMA_PWE3_p23`,
    `LEMMA_PWE4_p23` (sorry giants).
  Section B (JKQEWGV): `IS_SCS_STABLE_SYSTEM_p23`,
    `IS_SCS_TRI_STABLE_SYSTEM_p23` (sorry; torsor unpacking), the row
    bookkeeping tactic-lemmas `IS_SCS_IN_V_SY_*_p23`,
    `IS_SCS_IN_BALL_ANNULUS_*_p23`, `IS_SCS_IN_E_SY_*_p23` (proved; the
    HOL `fun (so:term)->` tactics), `V_E_FF_IS_SCS_CASES_3_p23` (proved)
    and `_4/_5/_6` (sorry), `IN_IS_SCS_CASE_*_p23`,
    `TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_*_p23`, `IS_EAR_V25_EQ_EAR_SY_p23`,
    `JKQEWGV1_CASE_*_p23`, `JKQEWGV1_p23`, `JKQEWGV2_CASE_*_p23`,
    `JKQEWGV2_p23`, `JKQEWGV3_p23` (sorry),
    `IS_SCS_POINT_IN_BBS_IS_NOT_0_3_p23` (proved),
    `IS_SCS_POINT_IN_BBS_IS_NOT_0_LE_3_p23` (proved),
    `IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23` / `_LE_3_p23` (sorry).
  The HOL `INJ_H_FUN_TAC` / `EXISTS_SCS_J_TAC` / `IN_IMAGE_VV_EQ_3`
  proof-tactics are absorbed into the statements above (their content is
  `periodic_mod_eq_p23` + the `IS_SCS_IN_*_p23` row lemmas);
  `check_completeness_claimA_concl` is commented out in the source.

ENCODING NOTES
   - Import discipline: this file sits entirely on the LocalAuto1 side of
     the fatal `atn2` duplication (LocalAuto2/9/11 and PackingAuto20 are
     NOT imported; LocalAuto19-27 same-wave lanes are NOT imported). The
     sphere-kit half of the split is resolved by importing
     `Kepler.Text.SphereKit` (DEDUP 2026-09-19: the `_p23`
     `delta_x4`/`delta_y`/`dih_y`/`taum` twins below were verbatim-equal
     to its canonical `deltaX4`/`deltaY`/`dihY`/`taum` and are deleted;
     `taum` upgrades the opaque stub to the real body — every consumer
     here is `sorry`, so no proof exploited the stub's opacity). The
     scs record (`ScsV39`, `isScsV39`, `BBsV39`, `taustarV39`, `MMsV39`,
     `scsArrowV39`, the `scs_*I*/T*/M*` registry, `scsStabDiagV39`) and
     `main_nonlinear_terminal_v11` come from LocalAuto1; the dih2k matrix
     substrate (`FinVec`, `vecmats_p4`, `vecmatsV3_p4`, `matvec_p4`,
     `V_SY_p4`/`E_SY_p4`/`F_SY_p4`, `CONDITION*_SY_p4`) from LocalAuto4
     (via its import). The LocalAuto8 stable-system kit (`torsor`,
     `constraint_system`, `stable_system`, `stable_sy`, `a_ear0`, `b_ear0`,
     `ear_sy`, `J1_SY`, `d_fun`, `tau_star`) is still carried as verbatim
     `_p23` twins with NEEDS merge markers (the dih2k fan kit is shape-C,
     not a verbatim twin of the canonical shape-A systems — deferred).
  - HOL `real^3^M` / `dimindex(:M)=k` / `vector[...]` bookkeeping is
    replaced by the 0-based row function `cycRow_p23 vv k = fun i =>
    vv ((i+1) % k)`; HOL `matvec v = a` hypotheses are absorbed (the
    flattening `vecmats_p4 (cycRow_p23 vv k)` plays the role of `a`).
  - HOL `change_type_v3` is the identity on `ℕ → ℕ → ℝ` functions and is
    dropped; HOL `change_type_v2 (scs_J_v39 s) k` is `scsJSet_p23 s`.
  - HOL `stable_sy`/`stable_system` dummy field `d` (unused in dih2k.hl):
    `stableSystem_p23` keeps the `0` dummy (LocalAuto8 typed it `ℕ`);
    `scsToStableSy_p23` carries `s.d` since SF-C3 (FIDELITY-FIX 2026-10-28,
    the record's `d` slot is `scs_d_v39 s` — see the def docstring).
  - HOL `dist(x,y)` ↦ `dist x y`; `norm x` ↦ `norm x`; `vec 0` ↦ `0`;
    `collinear` ↦ `Collinear ℝ`; `interior_angle1` ↦ `interiorAngle1`;
    `sol_local` ↦ `solLocal`; `circular` ↦ `Circular`; `lunar` ↦ `Lunar`;
    `taustar_v39 s vv < &0` ↦ `taustarV39 s vv < 0`; `xrr`/`cstab`/`h0`
    are LocalAuto1/`PackingAuto2` ports.
  - DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
    kit; proved items are mechanical (mod arithmetic, image bookkeeping,
    ball-annulus nontriviality, Mathlib compactness).
-/

import Kepler.Text.ClosedSyKit
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto9
import Kepler.Text.SphereKit
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p23` substrate -/

/- DEDUP (2026-09-19, atn2 merge plan §5.27): the former registry-twin
block `deltaX4_p23`, `deltaY_p23`, `dihY_p23` and the opaque `taum_p23`
stub is deleted — verbatim-equal to `Kepler.Text.SphereKit`'s `deltaX4`,
`deltaY`, `dihY` and `taum` (use sites renamed; `taum` upgrades the stub
to the real body, and every consumer in this file is `sorry`, so no proof
leaned on the stub's opacity). -/

/-- HOL `torsor` (dih2k.hl). Verbatim twin of LocalAuto8 `torsor_p8` /
LocalAuto18 `torsor_p18`. NEEDS: merge. -/
def torsor_p23 (s : Set ℕ) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ Nat.card s = k

/-- HOL `constraint_system` (dih2k.hl:52); `d` is the (unused) HOL dummy.
Verbatim twin of LocalAuto8 `constraintSystem_p8`. NEEDS: merge. -/
def constraintSystem_p23 (k d : ℕ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Set (Set ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor_p23 s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ {e | ∃ i ∈ s, e = {i, f i}} ∧ Nat.card J + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61). Verbatim twin of LocalAuto8
`stableSystem_p8`. NEEDS: merge. -/
def stableSystem_p23 (k d : ℕ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Set (Set ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p23 k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab)

/-- HOL `stable_sy` (HDPLYGY.hl:204): the 7-tuple record of stable
systems. Verbatim twin of LocalAuto8 `StableSy`. NEEDS: merge. -/
structure StableSyP23 where
  k : ℕ
  d : ℝ
  I : Set ℕ
  a : ℕ → ℕ → ℝ
  b : ℕ → ℕ → ℝ
  J : Set (Set ℕ)
  f : ℕ → ℕ
  stable : stableSystem_p23 k 0 I a b J f

/-- HOL `a_ear0` (HDPLYGY.hl:35 = localization.hl:135). Twin of LocalAuto8
`aEar0_p8`. NEEDS: merge. -/
noncomputable def aEar0_p23 (J : Set (Set ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if ({i % 3, j % 3} : Set ℕ) ∈ J then Real.sqrt 8 else 2

/-- HOL `b_ear0` (HDPLYGY.hl:39). Twin of LocalAuto8 `bEar0_p8`.
NEEDS: merge. -/
noncomputable def bEar0_p23 (J : Set (Set ℕ)) (i j : ℕ) : ℝ :=
  if i % 3 = j % 3 then 0 else if ({i % 3, j % 3} : Set ℕ) ∈ J then cstab else 2 * h0

/-- HOL `ear_sy` (HDPLYGY.hl:228). Twin of LocalAuto8 `earSy_p8`.
NEEDS: merge. -/
def earSy_p23 (s : StableSyP23) : Prop :=
  Nat.card s.I = 3 ∧ s.d = (11 : ℝ) / 100 ∧ Nat.card s.J = 1 ∧
    s.a = aEar0_p23 s.J ∧ s.b = bEar0_p23 s.J

/-- HOL `row i (vecmats l)` (1-based `i`, junk `0` off-range). Twin of
LocalAuto8 `rowSy`. NEEDS: merge. -/
def rowSy_p23 {m : ℕ} (l : FinVec m 3) (i : ℕ) : V3 :=
  if h : i < m then vecmatsV3_p4 l ⟨i, h⟩ else 0

/-- HOL `J1_SY` (HDPLYGY.hl:234). Twin of LocalAuto8 `J1_SY_p8`.
NEEDS: merge. -/
def J1_SY_p23 (s : StableSyP23) : Set (ℕ × ℕ) :=
  {x | ∃ i : ℕ, {i % s.k, s.f (i % s.k)} ∈ s.J ∧ i ∈ Set.Icc 1 s.k ∧
    x = (i, i % s.k + 1)}

/-- HOL `d_fun` (HDPLYGY.hl:236) with the `sigma_sy` if inlined. Twin of
LocalAuto8 `dFun_p8`. NEEDS: merge. -/
noncomputable def dFun_p23 (s : StableSyP23) {m : ℕ} (l : FinVec m 3) : ℝ :=
  s.d + (1 : ℝ) / 10 * (if earSy_p23 s then 1 else -1) *
    setSum (J1_SY_p23 s)
      (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖)

/-- HOL `tau_star` (HDPLYGY.hl:238). Twin of LocalAuto8 `tauStar_p8`.
NEEDS: merge. -/
noncomputable def tauStar_p23 (s : StableSyP23) {m : ℕ} (l : FinVec m 3) : ℝ :=
  tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
    (F_SY_p4 (vecmatsV3_p4 l)) - dFun_p23 s l

/-- HOL row vector `vector[vv 1; vv 2; ...; vv k; vv 0] : real^k^3`, read
0-based: row `i` holds `vv ((i+1) % k)`. -/
def cycRow_p23 (vv : ℕ → V3) (k : ℕ) : Fin k → V3 := fun i => vv ((i + 1) % k)

/-- HOL `matvec (vector[vv 1;..;vv k;vv 0])`: the cyclic k×3 matrix
flattened, read as a 0-based `FinVec k 3` (= `Fin (k * 3) → ℝ`). -/
def flattenRow_p23 (vv : ℕ → V3) (k : ℕ) : FinVec k 3 :=
  fun i : Fin (k * 3) =>
    (cycRow_p23 vv k ⟨(i : ℕ) / 3, by
          have := i.isLt
          omega⟩ :
          Fin 3 → ℝ) ⟨(i : ℕ) % 3, by omega⟩

/-- HOL `change_type_v2 (scs_J_v39 s) (scs_k_v39 s)`: the set of unordered
index pairs `{i, j}` with `scs_J_v39 s i j` (indices taken mod `k` via the
`Periodic2 s.J s.k` conjunct of `isScsV39`). -/
noncomputable def scsJSet_p23 (s : ScsV39) : Set (Set ℕ) :=
  {e | ∃ i j, i < s.k ∧ j < s.k ∧ s.J i j ∧ e = {i, j}}

/-- Every point of the ball annulus is nonzero (`dist ≥ 2` from the origin). -/
theorem ballAnnulus_ne_0_p23 (x : V3) (hx : x ∈ ballAnnulus) : x ≠ 0 := by
  obtain ⟨_, hlt⟩ := hx
  refine fun hzero => hlt ?_
  simp [hzero]

/-- A periodic sequence agrees with its residue-indexed value. -/
theorem periodic_mod_eq_p23 {α : Sort u} {v : ℕ → α} {k : ℕ} (hp : Periodic v k)
    (i : ℕ) : v (i % k) = v i := by
  have gen : ∀ q r : ℕ, v (k * q + r) = v r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ n ih =>
        intro r
        rw [show k * (n + 1) + r = k * n + r + k by ring]
        exact hp (k * n + r) ▸ ih r
  have hi : i = k * (i / k) + i % k := (Nat.div_add_mod i k).symm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hlt : i % k < k := Nat.mod_lt i hk
    have hmod : (k * (i / k) + i % k) % k = i % k := by
      rw [show k * (i / k) + i % k = i % k + k * (i / k) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rw [hi, hmod]
    exact (gen (i / k) (i % k)).symm

/-- A periodic sequence has range equal to its first `k` values. -/
theorem range_periodic_image_p23 {α : Type u} (vv : ℕ → α) (k : ℕ) (hk0 : 0 < k)
    (hp : Periodic vv k) : Set.range vv = vv '' Set.Iio k := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i % k, Set.mem_Iio.mpr (Nat.mod_lt i hk0), periodic_mod_eq_p23 hp i⟩
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩

/-! ## Section A: JOTSWIX.hl -/

/-- HOL `taum_attains_inf` (JOTSWIX.hl:9): `taum` attains its minimum in
the `y4` slot over the box. NEEDS: `real_continuous_taum_p23` plus the
delta_y / ups_x positivity facts from the terminal registry entry
`4717061266` (opaque in scripts/local); compactness skeleton is
Mathlib `IsCompact.exists_isMinOn`. -/
theorem taum_attains_inf_p23 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y5 y6 : ℝ) :
    ∃ y4' : ℝ, 2 ≤ y4' ∧ y4' ≤ 2 * h0 ∧ ∀ y4 : ℝ, 2 ≤ y4 → y4 ≤ 2 * h0 →
      taum y1 y2 y3 y4' y5 y6 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `TAUM_EXTREMAL` (JOTSWIX.hl:48): the attained minimiser is at an
endpoint. NEEDS: `taum_attains_inf_p23` plus `LEMMA_1834976363` /
`xrr_simple_*` bounds (Ocbicby). -/
theorem TAUM_EXTREMAL_p23 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2 * h0) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * h0)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * h0) :
    ∃ y4' : ℝ, (y4' = 2 * h0 ∨ y4' = 2) ∧
      taum y1 y2 y3 y4' y5 y6 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `TAUM_STD_POS` (JOTSWIX.hl:108): `taum ≥ 0` on the box. NEEDS:
`TAUM_EXTREMAL_p23`, the terminal registry entries `5541487347` /
`OMKYNLT 3336871894` and `taum_sym2`. -/
theorem TAUM_STD_POS_p23 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2 * h0) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * h0)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * h0) :
    0 ≤ taum y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `LFLACKU` (JOTSWIX.hl:191): `scs_arrow_v39 {scs_3I1} {}`. NEEDS:
the `taustar_taum_dfun` / `FUNLIST_EXPLICIT` bridge (Terminal lane) to
reduce `MMsV39 scs3I1 = ∅` to `TAUM_STD_POS_p23`. -/
theorem LFLACKU_p23 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs3I1} ∅ := by
  sorry

/-- The `{0, 1}` residue-pair test of `a_pro` (JOTSWIX.hl:216-257): the
two-element set `{a, b}` is `{0, 1}` iff the pair is `{0, 1}` or `{1, 0}`. -/
private theorem la23pair01 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 1} ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have ha : a = 0 ∨ a = 1 := by
      have hm : a ∈ ({a, b} : Set ℕ) := by simp
      rw [h] at hm
      simpa using hm
    have hb : b = 0 ∨ b = 1 := by
      have hm : b ∈ ({a, b} : Set ℕ) := by simp
      rw [h] at hm
      simpa using hm
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd h (by
        rw [show ({0, 0} : Set ℕ) = {0} from by ext x; simp] at h
        have hm : (1:ℕ) ∈ ({0, 1} : Set ℕ) := by simp
        rw [← h] at hm
        simp at hm)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd h (by
        rw [show ({1, 1} : Set ℕ) = {1} from by ext x; simp] at h
        have hm : (0:ℕ) ∈ ({0, 1} : Set ℕ) := by simp
        rw [← h] at hm
        simp at hm)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- HOL `s_init_list_alt` (JOTSWIX.hl:216): the init list spelled out.
The first six entries are `rfl`; the `5I3`/`4I3` entries go through the
`a_pro` ↔ `funlist_v39` function equalities (JOTSWIX.hl:241-257): `a_pro`'s
`p`-slot is the cycle edge `(0, 1)`, its `a1`-slot the remaining cycle edges
(funlist default), and its `a2`-slot the diagonals (the remaining table
slots), checked over all residue pairs by `interval_cases`. -/
theorem s_init_list_alt_p23 :
    sInitListV39 =
      [scs6I1, scs5I1, scs4I1, scs3I1, scs5I2, scs4I2, scs5I3, scs4I3] := by
  have key5 : ∀ p q r : ℝ,
      ((fun (i j : ℕ) =>
          if i % 5 = j % 5 then (0:ℝ)
          else if ({i % 5, j % 5} : Set ℕ) = {0, 1} then p
          else if j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5 then q else r) =
        funlistV39 [((0, 1), p), ((0, 2), r), ((0, 3), r), ((1, 3), r), ((1, 4), r),
          ((2, 4), r)] q 5) := by
    intro p q r
    funext i j
    have hfl : funlistV39 [((0, 1), p), ((0, 2), r), ((0, 3), r), ((1, 3), r),
        ((1, 4), r), ((2, 4), r)] q 5 i j =
        funlistV39 [((0, 1), p), ((0, 2), r), ((0, 3), r), ((1, 3), r), ((1, 4), r),
          ((2, 4), r)] q 5 (i % 5) (j % 5) := by
      simp [funlistV39, psort, Nat.mod_mod]
    rw [hfl, ← Nat.mod_add_mod i 5 1, ← Nat.mod_add_mod j 5 1]
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;>
      simp [funlistV39, psort, assocdV39, la23pair01] <;> norm_num
  have key4 : ∀ p q r : ℝ,
      ((fun (i j : ℕ) =>
          if i % 4 = j % 4 then (0:ℝ)
          else if ({i % 4, j % 4} : Set ℕ) = {0, 1} then p
          else if j % 4 = (i + 1) % 4 ∨ (j + 1) % 4 = i % 4 then q else r) =
        funlistV39 [((0, 1), p), ((0, 2), r), ((1, 3), r)] q 4) := by
    intro p q r
    funext i j
    have hfl : funlistV39 [((0, 1), p), ((0, 2), r), ((1, 3), r)] q 4 i j =
        funlistV39 [((0, 1), p), ((0, 2), r), ((1, 3), r)] q 4 (i % 4) (j % 4) := by
      simp [funlistV39, psort, Nat.mod_mod]
    rw [hfl, ← Nat.mod_add_mod i 4 1, ← Nat.mod_add_mod j 4 1]
    have hz1 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hz2 : j % 4 < 4 := Nat.mod_lt j (by omega)
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [funlistV39, psort, assocdV39, la23pair01] <;> norm_num
  simp only [sInitListV39, scs6I1, scs5I1, scs4I1, scs3I1, scs5I2, scs4I2, scs5I3,
    scs4I3]
  rw [key5 (2 * h0) 2 (2 * h0), key5 (Real.sqrt 8) (2 * h0) 6,
    key4 (2 * h0) 2 (Real.sqrt 8), key4 (Real.sqrt 8) (2 * h0) 6]

/-- HOL `JEJTVGB_case_breakdown` (JOTSWIX.hl:260): the arrow-registry
conjunction ending in `JEJTVGB_assume_v39`. Twin of LocalAuto16's
`JEJTVGB_case_breakdown_p16` (the OEHDBEN arrow's tail is `scs3T1` in
JOTSWIX per hexagons.hl vs `scs3M1` in the appendix registry — see the
`_p16` NEEDS note). NEEDS: the mechanical assembly from the `*_concl`
registry arrows (LocalAuto1:1416-1541). -/
theorem JEJTVGB_case_breakdown_p23 (h : main_nonlinear_terminal_v11)
    (a01 : scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3T1})               -- OEHDBEN
    (a02 : scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2})            -- OTMTOTJ1
    (a03 : scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2})            -- OTMTOTJ2
    (a04 : scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4, scs5M2})            -- OTMTOTJ3
    (a05 : scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4, scs5M2})            -- OTMTOTJ4
    (a06 : scsArrowV39 {scs5M2} {scs3T1, scs3T4, scs4M6', scs4M7, scs4M8,
      scs5T1, scsStabDiagV39 scs5I2 0 2, scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4})                    -- HIJQAHA
    (a07 : scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs4M2, scs3M1})            -- CNICGSF1
    (a08 : scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs4M3', scs3T1})           -- CNICGSF2
    (a09 : scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs4M2, scs3T4})            -- CNICGSF3
    (a10 : scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1})           -- CNICGSF4
    (a11 : scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs4M5', scs3M1})           -- CNICGSF5
    (a12 : scsArrowV39 {scs4I1} {scs4I2, scsStabDiagV39 scs4I1 0 2})            -- FYSSVEV
    (a13 : scsArrowV39 {scs4I2} {scs4T1, scs4T2})                               -- ARDBZYE
    (a14 : scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1})                    -- AUEAHEH
    (a15 : scsArrowV39 {scs4I3} {scs4T4, scs4M6'})                              -- VQFYMZY
    (a16 : scsArrowV39 {scs4M2} {scs3M1, scs3T4, scs4M6'})                      -- BNAWVNH
    (a17 : scsArrowV39 {scs4M3'} {scs3T1, scs3T6', scs4M6'})                    -- RAWZDIB
    (a18 : scsArrowV39 {scs4M4'} {scs3M1, scs3T4, scs3T3, scs4M7})              -- MFKLVDK
    (a19 : scsArrowV39 {scs4M5'} {scs3T4, scs4M8})                              -- RYPDIXT
    (a20 : scsArrowV39 {scs4M6'} {scs4T3, scs4T5})                              -- NWDGKXH
    (a21 : scsArrowV39 {scs4M7} {scs3M1, scs3T3, scs3T4})                       -- YOBIMPP
    (a22 : scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4})                      -- MIQMCSN
    (a23 : scsArrowV39 {scs3M1} {scs3T1, scs3T5}) :                             -- BKOSSGE
    JEJTVGB_assume_v39 := by
  sorry

/-- HOL `MOD_4_CASES` (JOTSWIX.hl:454). -/
theorem MOD_4_CASES_p23 (j p : ℕ) (hj : j < 4) :
    j = (p + 0) % 4 ∨ j = (p + 1) % 4 ∨ j = (p + 2) % 4 ∨ j = (p + 3) % 4 := by
  omega

/-- HOL `ab4_assumption_reduction` (JOTSWIX.hl:476): a k=4 deformation
fixing all but `v p` propagates the a/b endpoint bounds. NEEDS: the full
HOL proof (JOTSWIX.hl:487-668). -/
theorem ab4_assumption_reduction_p23 (s : ScsV39) (p : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (hdef : Deformation f (Set.range v) (-e) e) (he : 0 < e)
    (hfix : ∀ w t, w ≠ v p → f w t = w)
    (hdist : ∀ t, |t| < e → dist (v (p + 3)) (f (v p) t) = dist (v (p + 3)) (v p))
    (hab : s.a p (p + 1) < dist (v p) (v (p + 1)) ∧
      dist (v p) (v (p + 1)) < s.b p (p + 1)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  sorry

/-- HOL `PERIODIC_INJ_MOD` (JOTSWIX.hl:668). -/
theorem PERIODIC_INJ_MOD_p23 {α : Sort u} (v : ℕ → α) (k : ℕ) (hk : k ≠ 0)
    (hp : Periodic v k) (hinj : ∀ i j, i < k → j < k → v i = v j → i = j)
    (i j : ℕ) : (v i = v j ↔ i % k = j % k) := by
  constructor
  · intro hij
    apply hinj _ _ (Nat.mod_lt _ (by omega : 0 < k)) (Nat.mod_lt _ (by omega : 0 < k))
    rw [periodic_mod_eq_p23 hp i, periodic_mod_eq_p23 hp j, hij]
  · intro hmod
    rw [← periodic_mod_eq_p23 hp i, ← periodic_mod_eq_p23 hp j, hmod]

/-- HOL `ab4_assumption_reduction2` (JOTSWIX.hl:693): same propagation,
with the upper-bound side assumed only along the deformed edge. NEEDS:
the full HOL proof (JOTSWIX.hl:700-900). -/
theorem ab4_assumption_reduction2_p23 (s : ScsV39) (p : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (hdef : Deformation f (Set.range v) (-e) e) (he : 0 < e)
    (hfix : ∀ w t, w ≠ v p → f w t = w)
    (hdist : ∀ t, |t| < e → dist (v (p + 3)) (f (v p) t) = dist (v (p + 3)) (v p))
    (hab : s.a p (p + 1) < dist (v p) (v (p + 1)))
    (hb3 : ∃ e3 : ℝ, 0 < e3 ∧ ∀ t, |t| < e3 →
      dist (f (v p) t) (v (p + 1)) ≤ s.b p (p + 1)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  sorry

/-- HOL `ab4_assumption_reduction_sym` (JOTSWIX.hl:900): the `_sym`
twin, moving the fixed vertex to `v (p+1)`. NEEDS: the full HOL proof
(JOTSWIX.hl:908-1084). -/
theorem ab4_assumption_reduction_sym_p23 (s : ScsV39) (p : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (hdef : Deformation f (Set.range v) (-e) e) (he : 0 < e)
    (hfix : ∀ w t, w ≠ v (p + 1) → f w t = w)
    (hdist : ∀ t, |t| < e → dist (f (v (p + 1)) t) (v (p + 2)) =
      dist (v (p + 1)) (v (p + 2)))
    (hab : s.a p (p + 1) < dist (v p) (v (p + 1)) ∧
      dist (v p) (v (p + 1)) < s.b p (p + 1)) :
    (∀ i j, ∃ e1 : ℝ, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
    (∀ i j, ∃ e2 : ℝ, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) := by
  sorry

/-- HOL `deform_azim_sum` (JOTSWIX.hl:1084): a deformation of a 4-point
fan preserving one azimuth summand preserves the summed azimuth, off a
collinearity set. NEEDS: `CONTINUOUS_PRESERVE_COLLINEAR`
(Local_lemmas1) + the real-continuity of `f` from `Deformation`. -/
theorem deform_azim_sum_p23 (v1 v2 v3 v4 : V3) (f : V3 → ℝ → V3) (e : ℝ)
    (hdef : Deformation f {v1, v2, v3, v4} (-e) e)
    (ha4 : 0 < azim 0 v1 v2 v4) (ha4' : azim 0 v1 v2 v4 < Real.pi)
    (hc2 : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hc3 : ¬ Collinear ℝ ({0, v1, v3} : Set V3))
    (hc4 : ¬ Collinear ℝ ({0, v1, v4} : Set V3))
    (hsum : azim 0 v1 v2 v3 + azim 0 v1 v3 v4 = azim 0 v1 v2 v4)
    (hcase : ((∀ t, azim 0 (f v1 t) (f v2 t) (f v3 t) = azim 0 v1 v2 v3) ∧
        0 < azim 0 v1 v3 v4 ∧ azim 0 v1 v3 v4 < Real.pi) ∨
      ((∀ t, azim 0 (f v1 t) (f v3 t) (f v4 t) = azim 0 v1 v3 v4) ∧
        0 < azim 0 v1 v2 v3 ∧ azim 0 v1 v2 v3 < Real.pi)) :
    ∃ e1 : ℝ, 0 < e1 ∧ ∀ t, |t| < e1 →
      ¬ Collinear ℝ ({0, f v1 t, f v2 t} : Set V3) ∧
      ¬ Collinear ℝ ({0, f v1 t, f v3 t} : Set V3) ∧
      ¬ Collinear ℝ ({0, f v1 t, f v4 t} : Set V3) ∧
      azim 0 (f v1 t) (f v2 t) (f v3 t) + azim 0 (f v1 t) (f v3 t) (f v4 t) =
        azim 0 (f v1 t) (f v2 t) (f v4 t) := by
  sorry

/-- HOL `NEHXMWH` (JOTSWIX.hl:1171): the quad endpoint lemma for the
`(p+2)`-opposite interior angles. NEEDS: `BBprime2_v39`/`BBs_v39`
descent and the terminal registry entry `5541487347`. -/
theorem NEHXMWH_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ)
    (hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF)
    (hs : isScsV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s) (hb : scsBasicV39 s)
    (hg : scsGeneric v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hang : ∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  sorry

/-- HOL `BZQNDMN` (JOTSWIX.hl:1679): the `NEHXMWH` twin for the
`(p+3)`-opposite interior angles. NEEDS: same kit as `NEHXMWH_p23`. -/
theorem BZQNDMN_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ)
    (hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF)
    (hs : isScsV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s) (hb : scsBasicV39 s)
    (hg : scsGeneric v)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hang : ∀ i, i % 4 ≠ (p + 3) % 4 → interiorAngle1 0 FF (v i) < Real.pi) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  sorry

/-- HOL `JOTSWIX` (JOTSWIX.hl:2204): the master quad lemma — under the
xrr bound at least one of the two edges of the quad is under `cstab`.
NEEDS: `NEHXMWH_p23` + the `xrr` registry bounds. -/
theorem JOTSWIX_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ)
    (hFF : (fun i : ℕ => (v i, v (i + 1))) '' Set.univ = FF)
    (hs : isScsV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s) (hb : scsBasicV39 s)
    (hg : scsGeneric v) (hsa : s.a p (p + 1) < cstab)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hang : ∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi)
    (hxrr : xrr (norm (v (p + 3))) (norm (v (p + 1)))
      (dist (v (p + 3)) (v (p + 1))) ≤ 15.53) :
    dist (v p) (v (p + 1)) < cstab ∨ dist (v p) (v (p + 3)) < cstab := by
  sorry

/-- HOL `LEMMA_PWE1` (JOTSWIX.hl:2706). NEEDS: the terminal registry
inequalities + `tau_fun`-`dih` kit (giant). -/
theorem LEMMA_PWE1_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha01 : s.a p (p + 1) = 2) (ha31 : s.a (p + 3) p = 2)
    (hd : dist (v (p + 1)) (v (p + 2)) ≤ 2 * h0) :
    Real.pi / 2 < dihV 0 (v (p + 1)) (v (p + 2)) (v p) := by
  sorry

/-- HOL `LEMMA_PWE2` (JOTSWIX.hl:2994): the `PWE1` mirror across the
`(p+2),(p+3)` edge. NEEDS: same kit as `LEMMA_PWE1_p23`. -/
theorem LEMMA_PWE2_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha01 : s.a p (p + 1) = 2) (ha31 : s.a (p + 3) p = 2)
    (hd : dist (v (p + 2)) (v (p + 3)) ≤ 2 * h0) :
    Real.pi / 2 < dihV 0 (v (p + 3)) (v p) (v (p + 2)) := by
  sorry

/-- HOL `LINDIH_11` (JOTSWIX.hl:3291): the registry box
`[(2,y1,2);(2,y2,2.52);(2,y3,2.52);(2,y4,2);(3.01,y5,3.55);(2*h0,y6,3.01)]`
forces small dihedral or negative delta. NEEDS: the terminal Ineq
registry entry for the box (opaque). -/
theorem LINDIH_11_p23 (h : main_nonlinear_terminal_v11) (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : y1 = 2) (hy2 : 2 ≤ y2 ∧ y2 ≤ 2.52) (hy3 : 2 ≤ y3 ∧ y3 ≤ 2.52)
    (hy4 : y4 = 2) (hy5 : 3.01 ≤ y5 ∧ y5 ≤ 3.55)
    (hy6 : 2 * h0 ≤ y6 ∧ y6 ≤ 3.01) :
    dihY y1 y2 y3 y4 y5 y6 < 1.1 ∨ deltaY y1 y2 y3 y4 y5 y6 < 0 := by
  sorry

/-- HOL `LEMMA_PWE3` (JOTSWIX.hl:3370). NEEDS: same kit as
`LEMMA_PWE1_p23`. -/
theorem LEMMA_PWE3_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha01 : s.a p (p + 1) = 2) (ha30 : s.a (p + 3) p = 2 * h0)
    (hd1 : dist (v (p + 2)) (v (p + 3)) = 2)
    (hd2 : 2 * h0 ≤ dist (v (p + 1)) (v (p + 2))) :
    Real.pi / 2 < dihV 0 (v (p + 1)) (v p) (v (p + 2)) := by
  sorry

/-- HOL `LEMMA_PWE4` (JOTSWIX.hl:3648). NEEDS: same kit as
`LEMMA_PWE1_p23`. -/
theorem LEMMA_PWE4_p23 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hb : scsBasicV39 s) (hk : s.k = 4) (hMM : v ∈ MMsV39 s)
    (hdg : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hab : ∀ i, s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0 ∨
      s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)
    (hg : scsGeneric v)
    (hns1 : ¬ scsIsStr s v (p + 1)) (hns3 : ¬ scsIsStr s v (p + 3))
    (hs1 : scsIsStr s v p) (hn : norm (v p) = 2)
    (ha30 : s.a (p + 3) p = 2) (ha01 : s.a p (p + 1) = 2 * h0)
    (hd1 : dist (v (p + 2)) (v (p + 1)) = 2)
    (hd2 : 2 * h0 ≤ dist (v (p + 3)) (v (p + 2))) :
    Real.pi / 2 < dihV 0 (v (p + 3)) (v p) (v (p + 2)) := by
  sorry

/-! ## Section B: JKQEWGV.hl -/

/-- HOL `tri_stable` (PCRTTID.hl:32); `d` is the unused dummy. Verbatim
`twin` of LocalAuto9 `triStable_p9` (that lane is not importable here).
NEEDS: merge. -/
def triStable_p23 (k d : ℕ) (s : Set ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Set (Set ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p23 k d s a b J f ∧ k = 3 ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) < 4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab)

/-! ### SF-C2 feed: the torsor kit for `IS_SCS_STABLE_SYSTEM_p23`
(la23prereq-w1 draft B2, verbatim-bodies; fills the frozen sorry) -/

/-- successor-mod iterate stays below `k` (LA36 twin). -/
theorem succModIter_lt_p23 (k : ℕ) (hk : 0 < k) {j : ℕ} (hj : j < k) (n : ℕ) :
    (fun i => (1 + i) % k)^[n] j = (j + n) % k := by
  induction n with
  | zero => exact (Nat.mod_eq_of_lt hj).symm
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, Nat.add_comm]
      exact Nat.ModEq.add_right (c := 1) (Nat.mod_modEq (j + m) k)

/-- the `k`-fold successor-mod lands back on the residue. -/
theorem iterate_mod_eq_p23 (k : ℕ) (hk : 0 < k) (j : ℕ) :
    (fun i => (1 + i) % k)^[k] j = j % k := by
  have hkey : ∀ n m : ℕ, (fun i => (1 + i) % k)^[n] m % k = (n + m) % k := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ p ih =>
        intro m
        have h1 : (fun i => (1 + i) % k)^[p + 1] m
            = (1 + (fun i => (1 + i) % k)^[p] m) % k := by
          rw [Function.iterate_succ_apply']
        rw [h1, Nat.mod_mod, Nat.add_comm 1 ((fun i => (1 + i) % k)^[p] m),
          ← Nat.mod_add_mod ((fun i => (1 + i) % k)^[p] m) k 1, ih,
          Nat.mod_add_mod (p + m) k 1]
        rw [show (p + m) + 1 = p + 1 + m from by omega]
  have hfin := hkey k j
  rw [Nat.add_comm k j, Nat.add_mod_right] at hfin
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · omega
  · have hlt : (fun i => (1 + i) % k)^[k] j < k := by
      have hks : (fun i => (1 + i) % k)^[k] j
          = (1 + (fun i => (1 + i) % k)^[k - 1] j) % k := by
        have h1 : (fun i => (1 + i) % k)^[k] j
            = (fun i => (1 + i) % k)^[(k - 1) + 1] j := by
          rw [show (k - 1) + 1 = k from by omega]
        rw [h1, Function.iterate_succ_apply']
      rw [hks]
      exact Nat.mod_lt _ h0
    rw [← Nat.mod_eq_of_lt hlt]
    exact hfin

/-- unordered pair swap. -/
theorem setPair_comm_p23 {α : Type*} (a b : α) : ({a, b} : Set α) = {b, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- `Periodic2` residue pullback, second argument. -/
theorem periodic2_mod_r_p23 {α : Sort*} {f : ℕ → ℕ → α} {k : ℕ} (hp : Periodic2 f k)
    (i m : ℕ) : f i m = f i (m % k) := by
  have h1 : f i m = f i (m % k + m / k * k) := by
    conv_lhs => rw [(Nat.mod_add_div m k).symm, Nat.mul_comm k (m / k)]
  rw [h1]
  induction m / k with
  | zero => simp
  | succ n ih =>
      have hrw : m % k + (n + 1) * k = (m % k + n * k) + k := by ring
      rw [hrw, (hp i (m % k + n * k)).2, ih]

private theorem two_lt_sqrt8_p23 : (2 : ℝ) < Real.sqrt 8 :=
  Real.lt_sqrt_of_sq_lt (by norm_num : (2 : ℝ) ^ 2 < 8)

/-- the successor-mod cycle is a torsor over `0..k-1` (LA36 twin). -/
theorem torsor_succ_mod_p23 {k : ℕ} (hk : 0 < k) :
    torsor_p23 (Set.Iic (k - 1)) k (fun i => (1 + i) % k) := by
  have hxl : ∀ x ∈ Set.Iic (k - 1), x < k := fun x hx => by
    rw [Set.mem_Iic] at hx; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxl := hxl x hx
    show (1 + x) % k ≤ k - 1
    rcases Nat.lt_or_ge (1 + x) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · intro x1 hx1 x2 hx2 heq
    have h1 : x1 < k := hxl x1 hx1
    have h2 : x2 < k := hxl x2 hx2
    have hme' : Nat.ModEq k (x1 + 1) (x2 + 1) := by
      rw [Nat.add_comm x1 1, Nat.add_comm x2 1]; exact heq
    have hc : x1 % k = x2 % k := Nat.ModEq.add_right_cancel' 1 hme'
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hc
    exact hc
  · intro i x hi hik hxi
    have hxl := hxl x hxi
    rw [succModIter_lt_p23 k hk hxl i]
    intro heq
    have h1 : (x + i) % k = x % k := by rw [heq, Nat.mod_eq_of_lt hxl]
    have hdvd : k ∣ (x + i) - x := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
    rw [Nat.add_sub_cancel_left] at hdvd
    exact absurd (Nat.eq_zero_of_dvd_of_lt hdvd (by omega)) (by omega)
  · intro x hx
    have hxlt := hxl x hx
    show (fun i => (1 + i) % k)^[k] x = x
    rw [iterate_mod_eq_p23 k hk x, Nat.mod_eq_of_lt hxlt]
  · rw [Nat.card_coe_set_eq, Set.ncard_Iic_nat]
    omega

/-- HOL `IS_SCS_STABLE_SYSTEM` (JKQEWGV.hl:65): an scs with `k > 3` is a
stable system on `0..k-1` with successor cycling. FILL (la23prereq-w1
draft B2 torsor unpacking; also feeds the SF-81a `stable` field of the
record def below): the `isScsV39`
unpacking — the `torsor` cycle facts for `f = (1 + ·) % k` at k = 4,5,6
(HOL proof JKQEWGV.hl:73-409, `POWER_MOD_FUN`-driven). -/
theorem IS_SCS_STABLE_SYSTEM_p23 (s : ScsV39) (hs : isScsV39 s) (hk : 3 < s.k) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1)) s.a s.b (scsJSet_p23 s)
      (fun i => (1 + i) % s.k) := by
  -- FILL (la23prereq-w1 draft B2; CLEAN, general k > 3)
  obtain ⟨-, h3le, h6le, -, -, -, -, haP, -, -, hbP, -, hsymm, hchain, hadiag,
    hage2, -, hk4, hJadj, hJsqrt, hcard⟩ := hs
  refine ⟨⟨h3le, h6le, torsor_succ_mod_p23 (by omega), ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- symmetry of a, b and a ≤ b
    intro i j
    exact ⟨(hsymm i j).1, (hsymm i j).2.2.2.1,
      le_trans (hchain i j).1 (le_trans (hchain i j).2.1 (hchain i j).2.2)⟩
  · -- periodicity under the successor cycle
    intro i j
    have hit : (fun n => (1 + n) % s.k)^[s.k] j = j % s.k :=
      iterate_mod_eq_p23 s.k (by omega) j
    constructor
    · rw [hit]; exact periodic2_mod_r_p23 haP i j
    · rw [hit]; exact periodic2_mod_r_p23 hbP i j
  · -- every J edge is a successor edge {i, f i}
    intro e he
    simp only [scsJSet_p23, Set.mem_setOf_eq] at he
    obtain ⟨i, j, hi, hj, hJm, rfl⟩ := he
    simp only [Set.mem_setOf_eq]
    rcases hJadj i j hJm with hadj | hadj
    · refine ⟨i, by rw [Set.mem_Iic]; omega, ?_⟩
      have hjeq : j = (i + 1) % s.k := by
        rw [Nat.mod_eq_of_lt hj] at hadj; exact hadj
      show ({i, j} : Set ℕ) = {i, (1 + i) % s.k}
      rw [hjeq, Nat.add_comm 1 i]
    · refine ⟨j, by rw [Set.mem_Iic]; omega, ?_⟩
      have hieq : i = (j + 1) % s.k := by
        rw [Nat.mod_eq_of_lt hi] at hadj; exact hadj
      show ({i, j} : Set ℕ) = {j, (1 + j) % s.k}
      rw [hieq, setPair_comm_p23, Nat.add_comm 1 j]
  · -- the card bound: scsJSet routes into the bad-index set
    have hsub : scsJSet_p23 s ⊆
        (fun i : ℕ => ({i, (1 + i) % s.k} : Set ℕ)) ''
          {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} := by
      rintro e he
      simp only [scsJSet_p23, Set.mem_setOf_eq] at he
      obtain ⟨i, j, hi, hj, hJm, rfl⟩ := he
      rcases hJadj i j hJm with hadj | hadj
      · refine ⟨i, ⟨hi, Or.inr ?_⟩, ?_⟩
        · have hshift : s.a i (i + 1) = s.a i ((i + 1) % s.k) :=
            periodic2_mod_r_p23 haP i (i + 1)
          have hjeq : (i + 1) % s.k = j := by
            rw [Nat.mod_eq_of_lt hj] at hadj; exact hadj.symm
          rw [hshift, hjeq]
          exact lt_of_lt_of_eq two_lt_sqrt8_p23 (hJsqrt i j hJm).1.symm
        · have hjeq : j = (i + 1) % s.k := by
            rw [Nat.mod_eq_of_lt hj] at hadj; exact hadj
          show ({i, (1 + i) % s.k} : Set ℕ) = {i, j}
          rw [hjeq, Nat.add_comm 1 i]
      · refine ⟨j, ⟨hj, Or.inr ?_⟩, ?_⟩
        · have hshift : s.a j (j + 1) = s.a j ((j + 1) % s.k) :=
            periodic2_mod_r_p23 haP j (j + 1)
          have hieq : (j + 1) % s.k = i := by
            rw [Nat.mod_eq_of_lt hi] at hadj; exact hadj.symm
          rw [hshift, hieq, (hsymm j i).1]
          exact lt_of_lt_of_eq two_lt_sqrt8_p23 (hJsqrt i j hJm).1.symm
        · have hieq : i = (j + 1) % s.k := by
            rw [Nat.mod_eq_of_lt hi] at hadj; exact hadj
          show ({j, (1 + j) % s.k} : Set ℕ) = {i, j}
          rw [hieq, setPair_comm_p23, Nat.add_comm 1 j]
    have hfinB : {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.Finite :=
      Set.Finite.subset (Set.finite_Ico 0 s.k) (fun x hx => ⟨Nat.zero_le _, hx.1⟩)
    have h1 : Nat.card (scsJSet_p23 s) = Set.ncard (scsJSet_p23 s) :=
      Nat.card_coe_set_eq _
    have h2 : Set.ncard (scsJSet_p23 s) ≤
        Set.ncard ((fun i : ℕ => ({i, (1 + i) % s.k} : Set ℕ)) ''
          {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}) :=
      Set.ncard_le_ncard hsub (Set.Finite.image _ hfinB)
    have h3 : Set.ncard ((fun i : ℕ => ({i, (1 + i) % s.k} : Set ℕ)) ''
          {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))})
        ≤ Set.ncard {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} :=
      Set.ncard_image_le hfinB
    have h6 : s.k ≤ 6 := by omega
    omega
  · -- off-diagonal a-bound
    intro i hi j hj hne
    exact hage2 i j ⟨by rw [Set.mem_Iic] at hi; omega,
      by rw [Set.mem_Iic] at hj; omega, hne⟩
  · -- diagonal + successor b-bound
    intro i hi
    refine ⟨hadiag i, ?_⟩
    have hshift : s.b i (i + 1) = s.b i ((i + 1) % s.k) :=
      periodic2_mod_r_p23 hbP i (i + 1)
    show s.b i ((1 + i) % s.k) ≤ cstab
    rw [show (1 + i) % s.k = (i + 1) % s.k from by rw [Nat.add_comm], ← hshift]
    exact hk4 i hk
  · -- J edges carry the sqrt8 / cstab pair
    intro i j hmem
    simp only [scsJSet_p23, Set.mem_setOf_eq] at hmem
    obtain ⟨i', j', hi', hj', hJ', hpair⟩ := hmem
    rcases Set.pair_eq_pair_iff.mp hpair with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · subst he1; subst he2; exact hJsqrt i j hJ'
    · subst he2; subst he1
      constructor
      · rw [(hsymm i j).1]; exact (hJsqrt j i hJ').1
      · rw [(hsymm i j).2.2.2.1]; exact (hJsqrt j i hJ').2


/-- HOL `IS_SCS_TRI_STABLE_SYSTEM` (JKQEWGV.hl:409): the `k = 3` twin.
FILLED (sf80-case3-w1): the same torsor unpacking at k = 3, mirroring the
`IS_SCS_STABLE_SYSTEM_p23` body above (`hb3` supplies the `b i (f i) < 4`
diagonal bound the `stableSystem` variant replaced by `≤ cstab`). -/
theorem IS_SCS_TRI_STABLE_SYSTEM_p23 (s : ScsV39) (hs : isScsV39 s)
    (hk : s.k = 3) :
    triStable_p23 s.k 0 (Set.Iic (s.k - 1)) s.a s.b (scsJSet_p23 s)
      (fun i => (1 + i) % s.k) := by
  obtain ⟨-, h3le, h6le, -, -, -, -, haP, -, -, hbP, -, hsymm, hchain, hadiag,
    hage2, hb3, -, hJadj, hJsqrt, hcard⟩ := hs
  refine ⟨⟨h3le, h6le, torsor_succ_mod_p23 (by omega), ?_, ?_, ?_, ?_⟩, hk, ?_, ?_, ?_⟩
  · -- symmetry of a, b and a ≤ b
    intro i j
    exact ⟨(hsymm i j).1, (hsymm i j).2.2.2.1,
      le_trans (hchain i j).1 (le_trans (hchain i j).2.1 (hchain i j).2.2)⟩
  · -- periodicity under the successor cycle
    intro i j
    have hit : (fun n => (1 + n) % s.k)^[s.k] j = j % s.k :=
      iterate_mod_eq_p23 s.k (by omega) j
    constructor
    · rw [hit]; exact periodic2_mod_r_p23 haP i j
    · rw [hit]; exact periodic2_mod_r_p23 hbP i j
  · -- every J edge is a successor edge {i, f i}
    intro e he
    simp only [scsJSet_p23, Set.mem_setOf_eq] at he
    obtain ⟨i, j, hi, hj, hJm, rfl⟩ := he
    simp only [Set.mem_setOf_eq]
    rcases hJadj i j hJm with hadj | hadj
    · refine ⟨i, by rw [Set.mem_Iic]; omega, ?_⟩
      have hjeq : j = (i + 1) % s.k := by
        rw [Nat.mod_eq_of_lt hj] at hadj; exact hadj
      show ({i, j} : Set ℕ) = {i, (1 + i) % s.k}
      rw [hjeq, Nat.add_comm 1 i]
    · refine ⟨j, by rw [Set.mem_Iic]; omega, ?_⟩
      have hieq : i = (j + 1) % s.k := by
        rw [Nat.mod_eq_of_lt hi] at hadj; exact hadj
      show ({i, j} : Set ℕ) = {j, (1 + j) % s.k}
      rw [hieq, setPair_comm_p23, Nat.add_comm 1 j]
  · -- the card bound: scsJSet routes into the bad-index set
    have hsub : scsJSet_p23 s ⊆
        (fun i : ℕ => ({i, (1 + i) % s.k} : Set ℕ)) ''
          {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} := by
      rintro e he
      simp only [scsJSet_p23, Set.mem_setOf_eq] at he
      obtain ⟨i, j, hi, hj, hJm, rfl⟩ := he
      rcases hJadj i j hJm with hadj | hadj
      · refine ⟨i, ⟨hi, Or.inr ?_⟩, ?_⟩
        · have hshift : s.a i (i + 1) = s.a i ((i + 1) % s.k) :=
            periodic2_mod_r_p23 haP i (i + 1)
          have hjeq : (i + 1) % s.k = j := by
            rw [Nat.mod_eq_of_lt hj] at hadj; exact hadj.symm
          rw [hshift, hjeq]
          exact lt_of_lt_of_eq two_lt_sqrt8_p23 (hJsqrt i j hJm).1.symm
        · have hjeq : j = (i + 1) % s.k := by
            rw [Nat.mod_eq_of_lt hj] at hadj; exact hadj
          show ({i, (1 + i) % s.k} : Set ℕ) = {i, j}
          rw [hjeq, Nat.add_comm 1 i]
      · refine ⟨j, ⟨hj, Or.inr ?_⟩, ?_⟩
        · have hshift : s.a j (j + 1) = s.a j ((j + 1) % s.k) :=
            periodic2_mod_r_p23 haP j (j + 1)
          have hieq : (j + 1) % s.k = i := by
            rw [Nat.mod_eq_of_lt hi] at hadj; exact hadj.symm
          rw [hshift, hieq, (hsymm j i).1]
          exact lt_of_lt_of_eq two_lt_sqrt8_p23 (hJsqrt i j hJm).1.symm
        · have hieq : i = (j + 1) % s.k := by
            rw [Nat.mod_eq_of_lt hi] at hadj; exact hadj
          show ({j, (1 + j) % s.k} : Set ℕ) = {i, j}
          rw [hieq, setPair_comm_p23, Nat.add_comm 1 j]
    have hfinB : {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.Finite :=
      Set.Finite.subset (Set.finite_Ico 0 s.k) (fun x hx => ⟨Nat.zero_le _, hx.1⟩)
    have h1 : Nat.card (scsJSet_p23 s) = Set.ncard (scsJSet_p23 s) :=
      Nat.card_coe_set_eq _
    have h2 : Set.ncard (scsJSet_p23 s) ≤
        Set.ncard ((fun i : ℕ => ({i, (1 + i) % s.k} : Set ℕ)) ''
          {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}) :=
      Set.ncard_le_ncard hsub (Set.Finite.image _ hfinB)
    have h3 : Set.ncard ((fun i : ℕ => ({i, (1 + i) % s.k} : Set ℕ)) ''
          {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))})
        ≤ Set.ncard {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} :=
      Set.ncard_image_le hfinB
    have h6 : s.k ≤ 6 := by omega
    omega
  · -- off-diagonal a-bound
    intro i hi j hj hne
    exact hage2 i j ⟨by rw [Set.mem_Iic] at hi; omega,
      by rw [Set.mem_Iic] at hj; omega, hne⟩
  · -- diagonal + successor b-bound (k = 3: the `hb3` conjunct)
    intro i hi
    refine ⟨hadiag i, ?_⟩
    have hshift : s.b i (i + 1) = s.b i ((i + 1) % s.k) :=
      periodic2_mod_r_p23 hbP i (i + 1)
    show s.b i ((1 + i) % s.k) < 4
    rw [show (1 + i) % s.k = (i + 1) % s.k from by rw [Nat.add_comm], ← hshift]
    exact hb3 i hk
  · -- J edges carry the sqrt8 / cstab pair
    intro i j hmem
    simp only [scsJSet_p23, Set.mem_setOf_eq] at hmem
    obtain ⟨i', j', hi', hj', hJ', hpair⟩ := hmem
    rcases Set.pair_eq_pair_iff.mp hpair with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · subst he1; subst he2; exact hJsqrt i j hJ'
    · subst he2; subst he1
      constructor
      · rw [(hsymm i j).1]; exact (hJsqrt j i hJ').1
      · rw [(hsymm i j).2.2.2.1]; exact (hJsqrt j i hJ').2

/-- The `stable_sy ((k),(d),(0..k-1),(a),(b),(J),(\i. (1+i) MOD k)) = s1`
record of the JKQEWGV hypotheses, built from `s`.  SF-81 案①: the `stable`
field is the Lean rendering of the HOL `stable_sy` SUBTYPE predicate
(HDPLYGY.hl:200-205 — the type only contains tuples satisfying
`stable_system`, cf. `stable_sy_lemma`), so the builder takes the evidence
as parameters and feeds it from `IS_SCS_STABLE_SYSTEM_p23` — the def-body
`sorry` placeholder is gone and the taint is carried by that TRACKED M0
theorem instead (it self-heals when the torsor unpacking lands).  Position:
after `IS_SCS_STABLE_SYSTEM_p23` (SF-81 moved the def here from Section 0 —
it cites that theorem, so it must postdate it).

FIDELITY-FIX (SF-C3, 2026-10-28): the HOL record's `d` slot is
`scs_d_v39 s` (UXCKFPE.hl:450, `stable_sy ((scs_k_v39 s),(scs_d_v39 s),...)`;
also XWITCCN.hl:2772), NOT `0`.  The `d := 0` rendering made every `k ≥ 4`
`TAUSTAR_EQ_TAU_STAR_*` bridge false: `taustar_v39` subtracts
`dsv_v39 = scs_d_v39 s + 0.1*eps*Σ{J-edges}` while `tau_star s1` subtracted
`0 + 0.1*eps'*Σ{J1_SY}` (the two d-parts then differ by `scs_d_v39 s`, which
`isScsV39` does not pin — it only bounds `s.d < 0.9`).  This is the same
defect LA36 repaired on 2026-09-17 as `scsToStableSyD_p36` (`d := s.d`);
the fix is now applied here, so the record is field-for-field the LA36 twin
(except the `stable` slot, which keeps the SF-81 案① evidence parameter). -/
noncomputable def scsToStableSy_p23 (s : ScsV39) (hs : isScsV39 s)
    (hk : 3 < s.k) : StableSyP23 where
  k := s.k
  d := s.d
  I := Set.Iic (s.k - 1)
  a := s.a
  b := s.b
  J := scsJSet_p23 s
  f := fun i => (1 + i) % s.k
  stable := IS_SCS_STABLE_SYSTEM_p23 s hs hk

/-! ### Row bookkeeping (the HOL `fun (so:term)->` tactics, as lemmas) -/

/-- `IS_SCS_IN_V_SY_4` (JKQEWGV.hl:721): row `j` of the k=4 vector is the
`vv j`-labelled point. -/
theorem IS_SCS_IN_V_SY_4_p23 (vv : ℕ → V3) (j : ℕ) (hj : j < 4) :
    vv j ∈ V_SY_p4 (cycRow_p23 vv 4) := by
  refine Set.mem_range.mpr ⟨⟨(j + 3) % 4, by omega⟩, ?_⟩
  show vv (((j + 3) % 4 + 1) % 4) = vv j
  rw [show ((j + 3) % 4 + 1) % 4 = j % 4 by omega, Nat.mod_eq_of_lt hj]

/-- `IS_SCS_IN_V_SY_5` (JKQEWGV.hl:1186). -/
theorem IS_SCS_IN_V_SY_5_p23 (vv : ℕ → V3) (j : ℕ) (hj : j < 5) :
    vv j ∈ V_SY_p4 (cycRow_p23 vv 5) := by
  refine Set.mem_range.mpr ⟨⟨(j + 4) % 5, by omega⟩, ?_⟩
  show vv (((j + 4) % 5 + 1) % 5) = vv j
  rw [show ((j + 4) % 5 + 1) % 5 = j % 5 by omega, Nat.mod_eq_of_lt hj]

/-- `IS_SCS_IN_V_SY_6` (JKQEWGV.hl:1668). -/
theorem IS_SCS_IN_V_SY_6_p23 (vv : ℕ → V3) (j : ℕ) (hj : j < 6) :
    vv j ∈ V_SY_p4 (cycRow_p23 vv 6) := by
  refine Set.mem_range.mpr ⟨⟨(j + 5) % 6, by omega⟩, ?_⟩
  show vv (((j + 5) % 6 + 1) % 6) = vv j
  rw [show ((j + 5) % 6 + 1) % 6 = j % 6 by omega, Nat.mod_eq_of_lt hj]

/-- `IS_SCS_IN_BALL_ANNULUS_4` (JKQEWGV.hl:707): every row of the k=4
vector lies in the ball annulus. -/
theorem IS_SCS_IN_BALL_ANNULUS_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hBB : BBsV39 s vv) (i : Fin 4) : cycRow_p23 vv 4 i ∈ ballAnnulus :=
  hBB.1 ⟨((i : ℕ) + 1) % 4, rfl⟩

/-- `IS_SCS_IN_BALL_ANNULUS_5` (JKQEWGV.hl:1329). -/
theorem IS_SCS_IN_BALL_ANNULUS_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (hBB : BBsV39 s vv) (i : Fin 5) : cycRow_p23 vv 5 i ∈ ballAnnulus :=
  hBB.1 ⟨((i : ℕ) + 1) % 5, rfl⟩

/-- `IS_SCS_IN_BALL_ANNULUS_6` (JKQEWGV.hl:1822). -/
theorem IS_SCS_IN_BALL_ANNULUS_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (hBB : BBsV39 s vv) (i : Fin 6) : cycRow_p23 vv 6 i ∈ ballAnnulus :=
  hBB.1 ⟨((i : ℕ) + 1) % 6, rfl⟩

/-- `PROVE_E_SY_INV_TAC_4` (JKQEWGV.hl:729) membership content: the cyclic
edge at `r` is an `E_SY` edge of the k=4 vector. -/
theorem IS_SCS_IN_E_SY_4_p23 (vv : ℕ → V3) (r : ℕ) (hr : r < 4)
    (hp : Periodic vv 4) :
    ({vv r, vv (r + 1)} : Set V3) ∈ E_SY_p4 (cycRow_p23 vv 4) := by
  refine ⟨⟨(r + 3) % 4, by omega⟩, Set.mem_univ _, ?_⟩
  show ({vv (((r + 3) % 4 + 1) % 4),
    vv ((((r + 3) % 4 + 1) % 4 + 1) % 4)} : Set V3) = ({vv r, vv (r + 1)} : Set V3)
  rw [show ((r + 3) % 4 + 1) % 4 = r % 4 by omega,
    show ((r % 4) + 1) % 4 = (r + 1) % 4 by omega,
    ← periodic_mod_eq_p23 hp (r + 1), Nat.mod_eq_of_lt hr]

/-- `PROVE_E_SY_INV_TAC_5` (JKQEWGV.hl:1195). -/
theorem IS_SCS_IN_E_SY_5_p23 (vv : ℕ → V3) (r : ℕ) (hr : r < 5)
    (hp : Periodic vv 5) :
    ({vv r, vv (r + 1)} : Set V3) ∈ E_SY_p4 (cycRow_p23 vv 5) := by
  refine ⟨⟨(r + 4) % 5, by omega⟩, Set.mem_univ _, ?_⟩
  show ({vv (((r + 4) % 5 + 1) % 5),
    vv ((((r + 4) % 5 + 1) % 5 + 1) % 5)} : Set V3) = ({vv r, vv (r + 1)} : Set V3)
  rw [show ((r + 4) % 5 + 1) % 5 = r % 5 by omega,
    show ((r % 5) + 1) % 5 = (r + 1) % 5 by omega,
    ← periodic_mod_eq_p23 hp (r + 1), Nat.mod_eq_of_lt hr]

/-- `PROVE_E_SY_INV_TAC_6` (JKQEWGV.hl:1679). -/
theorem IS_SCS_IN_E_SY_6_p23 (vv : ℕ → V3) (r : ℕ) (hr : r < 6)
    (hp : Periodic vv 6) :
    ({vv r, vv (r + 1)} : Set V3) ∈ E_SY_p4 (cycRow_p23 vv 6) := by
  refine ⟨⟨(r + 5) % 6, by omega⟩, Set.mem_univ _, ?_⟩
  show ({vv (((r + 5) % 6 + 1) % 6),
    vv ((((r + 5) % 6 + 1) % 6 + 1) % 6)} : Set V3) = ({vv r, vv (r + 1)} : Set V3)
  rw [show ((r + 5) % 6 + 1) % 6 = r % 6 by omega,
    show ((r % 6) + 1) % 6 = (r + 1) % 6 by omega,
    ← periodic_mod_eq_p23 hp (r + 1), Nat.mod_eq_of_lt hr]

/-! ### la23prereq-w1 fill kit: V/E/F image bookkeeping (draft B1) + the
HDPLYGY minimizer port (la24casebank probe2, general-m) + the SF-C3
d-part identity and the TAUSTAR core (casebank-close-w1 probe A).
All CLEAN except the two explicitly-rooted NEEDS pieces
(`continuousOn_tauFun_p23`, `bodyClosed_p23`). -/

/-- (LA36 `modShift_p36` twin.) the cyclic predecessor shift. -/
theorem modShift_p23 (k r : ℕ) (hrk : r < k) :
    ((r + k - 1) % k + 1) % k = r % k := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k),
      show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod]
  · rw [show r + k - 1 = r - 1 + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : r - 1 < k), show r - 1 + 1 = r by omega]

/-- (LA36 `cycRow_shift_p36` twin.) the cyclic index decoding. -/
theorem cycRow_shift_p23 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k)
    (n : ℕ) : ∃ i : Fin k, cycRow_p23 vv k i = vv n ∧
      cycRow_p23 vv k (finNext i) = vv (n + 1) := by
  have e1 : ((n % k + k - 1) % k + 1) % k = n % k := by
    rw [modShift_p23 k (n % k) (Nat.mod_lt n hk), Nat.mod_mod]
  have e2 : (((n % k + k - 1) % k + 1) % k + 1) % k = (n + 1) % k := by
    rw [e1]
    exact Nat.mod_add_mod n k 1
  refine ⟨⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩, ?_, ?_⟩
  · have h1 : cycRow_p23 vv k (⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩ : Fin k)
        = vv (((n % k + k - 1) % k + 1) % k) := rfl
    rw [h1, e1]
    exact periodic_mod_eq_p23 hper n
  · have h2 : cycRow_p23 vv k
        (finNext (⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩ : Fin k))
        = vv ((((n % k + k - 1) % k + 1) % k + 1) % k) := rfl
    rw [h2, e2]
    exact periodic_mod_eq_p23 hper (n + 1)

/-- `V_SY = range vv`. -/
theorem vSy_eq_range_p23 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k) :
    V_SY_p4 (cycRow_p23 vv k) = Set.range vv := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, rfl⟩
    exact ⟨(i : ℕ) + 1, (periodic_mod_eq_p23 hper ((i : ℕ) + 1)).symm⟩
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨(n % k + k - 1) % k, Nat.mod_lt _ hk⟩, ?_⟩
    show vv (((n % k + k - 1) % k + 1) % k) = vv n
    rw [modShift_p23 k (n % k) (Nat.mod_lt n hk), Nat.mod_mod]
    exact periodic_mod_eq_p23 hper n

/-- `E_SY = image vv-adjacent-pairs`. -/
theorem eSy_eq_image_p23 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k) :
    E_SY_p4 (cycRow_p23 vv k) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, -, rfl⟩
    refine ⟨(i : ℕ) + 1, Set.mem_univ _, ?_⟩
    show ({vv (((i : Fin k) : ℕ) + 1), vv (((i : Fin k) : ℕ) + 1 + 1)} : Set V3)
        = {vv ((((i : Fin k) : ℕ) + 1) % k),
           vv (((((i : Fin k) : ℕ) + 1) % k + 1) % k)}
    rw [Nat.mod_add_mod (((i : Fin k) : ℕ) + 1) k 1,
      periodic_mod_eq_p23 hper (((i : Fin k) : ℕ) + 1),
      periodic_mod_eq_p23 hper (((i : Fin k) : ℕ) + 1 + 1)]
  · rintro _ ⟨n, -, rfl⟩
    obtain ⟨i, hi1, hi2⟩ := cycRow_shift_p23 hk hper n
    exact ⟨i, Set.mem_univ i, by simp only; rw [hi1, hi2]⟩

/-- `F_SY = image vv-adjacent-darts`. -/
theorem fSy_eq_image_p23 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} (hper : Periodic vv k) :
    F_SY_p4 (cycRow_p23 vv k) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨i, -, rfl⟩
    refine ⟨(i : ℕ) + 1, Set.mem_univ _, ?_⟩
    show ((vv (((i : Fin k) : ℕ) + 1), vv (((i : Fin k) : ℕ) + 1 + 1)) : V3 × V3)
        = (vv ((((i : Fin k) : ℕ) + 1) % k),
           vv (((((i : Fin k) : ℕ) + 1) % k + 1) % k))
    rw [Nat.mod_add_mod (((i : Fin k) : ℕ) + 1) k 1,
      periodic_mod_eq_p23 hper (((i : Fin k) : ℕ) + 1),
      periodic_mod_eq_p23 hper (((i : Fin k) : ℕ) + 1 + 1)]
  · rintro _ ⟨n, -, rfl⟩
    obtain ⟨i, hi1, hi2⟩ := cycRow_shift_p23 hk hper n
    exact ⟨i, Set.mem_univ i, by simp only; rw [hi1, hi2]⟩

/-! ### HDPLYGY port kit (general m; the CASE_4/5/6 minimizer) -/

/-- row/coordinate continuity (LA9 twin; la23prereq draft A). -/
theorem continuous_vecmatsV3_row_p23 {m : ℕ} (j : Fin m) :
    Continuous (fun l : FinVec m 3 => vecmatsV3_p4 l j) := by
  unfold vecmatsV3_p4 vecmats_p4
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun _ => continuous_apply _)

/-- `rowSy` continuity. -/
theorem continuous_rowSy_p23 {m : ℕ} (i : ℕ) :
    Continuous (fun l : FinVec m 3 => rowSy_p23 l i) := by
  unfold rowSy_p23
  split_ifs with h
  · exact continuous_vecmatsV3_row_p23 ⟨i, h⟩
  · exact continuous_const

/-- `J1_SY` finiteness (draft A `FINITE_J1_SY`). -/
theorem finite_J1_SY_p23 (s : StableSyP23) : (J1_SY_p23 s).Finite := by
  refine Set.Finite.subset
    (Set.Finite.image (fun i : ℕ => (i, i % s.k + 1)) (Set.finite_Icc 1 s.k)) ?_
  intro x hx
  simp only [J1_SY_p23, Set.mem_setOf_eq] at hx
  obtain ⟨i, -, hi, rfl⟩ := hx
  exact ⟨i, hi, rfl⟩

/-- HOL `CONTINUOUS_ON_D_FUN` at full strength (draft A leg 1, CLEAN). -/
theorem continuous_dFun_p23 (s : StableSyP23) {m : ℕ} :
    Continuous (fun l : FinVec m 3 => dFun_p23 s l) := by
  classical
  unfold dFun_p23
  have hterms : ∀ x ∈ J1_SY_p23 s,
      Continuous (fun l : FinVec m 3 =>
        cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖) := fun x _ =>
    Continuous.sub continuous_const
      (((continuous_rowSy_p23 (x.1 - 1)).sub (continuous_rowSy_p23 (x.2 - 1))).norm)
  have hsum : Continuous (fun l : FinVec m 3 => setSum (J1_SY_p23 s)
      (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖)) := by
    simp only [setSum]
    split
    · rename_i h
      refine continuous_finsetSum _ (fun x hx => hterms x (h.mem_toFinset.mp hx))
    · exact continuous_const
  exact Continuous.add continuous_const
    (Continuous.const_mul hsum ((1 : ℝ) / 10 * (if earSy_p23 s then 1 else -1)))

/-- the annulus box is bounded (draft A leg 4 core). -/
theorem annulusBox_bounded_p23 (m : ℕ) :
    Bornology.IsBounded {v : Fin m → V3 | ∀ i, v i ∈ ballAnnulus} := by
  refine Metric.isBounded_iff.mpr ⟨4 * h0, fun a ha b hb => ?_⟩
  rw [dist_pi_le_iff (by
    have hh : h0 = 1.26 := rfl
    norm_num [hh])]
  intro i
  have h1 : ‖a i‖ ≤ 2 * h0 := (ballAnnulus_norm_bounds (ha i)).2
  have h2 : ‖b i‖ ≤ 2 * h0 := (ballAnnulus_norm_bounds (hb i)).2
  have hd : dist (a i) (b i) = ‖a i - b i‖ := dist_eq_norm _ _
  rw [hd]
  calc ‖a i - b i‖ ≤ ‖a i‖ + ‖b i‖ := norm_sub_le _ _
    _ ≤ 4 * h0 := by linarith

/-- the `B_SY1` body is bounded (draft A leg 4, CLEAN; conjunct order = the
`B_SY1_p4` body order). -/
theorem bodyBounded_p23 (m : ℕ) (aR bR : Fin m → Fin m → ℝ) :
    Bornology.IsBounded {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v} := by
  refine Bornology.IsBounded.subset (annulusBox_bounded_p23 m) ?_
  intro v hv
  exact hv.1

/-- the (annulus ∧ CONDITION1) factor is closed (draft A leg 3 factor, CLEAN;
the remaining CONDITION2 factor is the CLOSED_SY giant). -/
theorem annulus_c1_closed_p23 (m : ℕ) (aR bR : Fin m → Fin m → ℝ) :
    IsClosed {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v} := by
  have hrw : {v : Fin m → V3 | ∀ i, v i ∈ ballAnnulus}
      = ⋂ i : Fin m, (fun p : Fin m → V3 => p i) ⁻¹' ballAnnulus := by
    ext v
    simp [Set.mem_iInter]
  have h1 : IsClosed {v : Fin m → V3 | ∀ i, v i ∈ ballAnnulus} := by
    rw [hrw]
    exact isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) CLOSED_BALL_ANNULUS
  have hrw2 : {v : Fin m → V3 | CONDITION1_SY_p4 aR bR v}
      = ⋂ (i : Fin m), ⋂ j : Fin m,
          {v : Fin m → V3 | aR i j ≤ ‖v i - v j‖ ∧ ‖v i - v j‖ ≤ bR i j} := by
    ext v
    simp [CONDITION1_SY_p4, Set.mem_iInter]
  have key : ∀ i j : Fin m, IsClosed {v : Fin m → V3 |
      aR i j ≤ ‖v i - v j‖ ∧ ‖v i - v j‖ ≤ bR i j} := by
    intro i j
    have hc : Continuous fun v : Fin m → V3 => ‖v i - v j‖ :=
      ((continuous_apply i).sub (continuous_apply j)).norm
    have hrw3 : {v : Fin m → V3 | aR i j ≤ ‖v i - v j‖ ∧ ‖v i - v j‖ ≤ bR i j}
        = (fun v : Fin m → V3 => ‖v i - v j‖) ⁻¹' Set.Ici (aR i j)
          ∩ (fun v : Fin m → V3 => ‖v i - v j‖) ⁻¹' Set.Iic (bR i j) := by
      ext w
      simp [Set.mem_inter_iff]
    rw [hrw3]
    exact (IsClosed.preimage hc isClosed_Ici).inter (IsClosed.preimage hc isClosed_Iic)
  have h2 : IsClosed {v : Fin m → V3 | CONDITION1_SY_p4 aR bR v} := by
    rw [hrw2]
    exact isClosed_iInter fun i => isClosed_iInter fun j => key i j
  exact h1.inter h2

/-! ### fanchain-w8 (W8 收口): discharge of `continuousOn_tauFun_p23` through
LA9 `CONTINUOUS_ON_TAU_FUN_p9` (W7, standard three axioms). Carrier → record:
the p23 carrier's `a b` are re-wrapped as `fun i j => a (i % m) (j % m)` so the
1-based ℕ row `i` of `B_SY1_p9` reads the same entry as Fin row `⟨i-1⟩` of
`aR`/`bR` (the `%m` wrap absorbs the row-`m` ↔ row-`0` wrap line; sf91b
Evidence §3 item 3). `J_SY` is the faithful Set→Finset container bridge: the
carrier's `J` enumerated over the edge family and filtered by membership
(card ≤ `Nat.card J` via the coe injection). `d_sy := 0` (the unused HOL
dummy; the S10 tauFun chain is `d`-blind, sf91b Evidence §3). -/

/-- fw8: `Finset.Icc 0 (m-1)` ↔ `Set.Iic (m-1)` membership bridge
(sf91b machine check C3a/C9). -/
private theorem fw8_mem_Icc {m x : ℕ} :
    x ∈ (Finset.Icc 0 (m - 1) : Finset ℕ) ↔ x ∈ Set.Iic (m - 1) := by
  constructor
  · exact fun h => (Finset.mem_Icc.mp h).2
  · exact fun h => Finset.mem_Icc.mpr ⟨Nat.zero_le x, h⟩

/-- fw8: congruence lemma for the wrapped-table period clause. -/
private theorem fw8_add_mod_congr {m a b c : ℕ} (h : a % m = b % m) :
    (c + a) % m = (c + b) % m := by
  calc (c + a) % m = (c % m + a % m) % m := Nat.add_mod c a m
    _ = (c % m + b % m) % m := by rw [h]
    _ = (c + b) % m := (Nat.add_mod c b m).symm

/-- fw8: the pinned successor `fun i => (1 + i) % m` iterated `n` times sends
`x` to `(n + x) % m` modulo `m` (makes the `f^[m]` period clause of the
wrapped table definitional). -/
private theorem fw8_iter_mod (m : ℕ) :
    ∀ (n x : ℕ), ((fun i => (1 + i) % m)^[n] x) % m = (n + x) % m := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have h1 : ((fun i => (1 + i) % m)^[n + 1] x)
        = (fun i => (1 + i) % m)^[n] ((1 + x) % m) :=
      Function.iterate_succ_apply _ n x
    rw [h1, ih]
    have h2 : (1 + x) % m = (x + 1) % m := by rw [Nat.add_comm]
    have h3 : (n + ((x + 1) % m)) % m = (n + (x + 1)) % m :=
      fw8_add_mod_congr (Nat.mod_mod (x + 1) m)
    calc (n + (1 + x) % m) % m = (n + ((x + 1) % m)) % m := by rw [h2]
      _ = (n + (x + 1)) % m := h3
      _ = (n + 1 + x) % m := by congr 1; omega

/-- fw8: the `B_SY1_p4` image map (matrix flattening of a `Fin m → V3` row
family; body verbatim-twin of the lambda inside `B_SY1_p4`). -/
private def fw8_flat {m : ℕ} (w : Fin m → V3) : FinVec m 3 :=
  fun i : Fin (m * 3) =>
    (w ⟨(i : ℕ) / 3, by have := i.isLt; omega⟩).ofLp ⟨(i : ℕ) % 3, by omega⟩

/-- fw8: `vecmatsV3_p4` undoes the flattening (`MATVEC_VECMATS_ID` twin on the
`V3`-typed rows). -/
private theorem fw8_flat_roundtrip {m : ℕ} (w : Fin m → V3) :
    vecmatsV3_p4 (fw8_flat w) = w := by
  funext j
  show (WithLp.toLp 2 (vecmats_p4 (fw8_flat w) j) : V3) = w j
  rw [WithLp.ext_iff, WithLp.ofLp_toLp]
  funext k
  have hdm := div_mod_row (by norm_num : (0:ℕ) < 3) j k j.isLt k.isLt
  show (w ⟨(finProdEquiv m 3 ⟨j, k⟩ : ℕ) / 3, _⟩).ofLp
      ⟨(finProdEquiv m 3 ⟨j, k⟩ : ℕ) % 3, _⟩ = (w j).ofLp k
  simp only [finProdEquiv_val, hdm.1, hdm.2]

/-- fw8: `vecmatsV3_p4` is injective (through `MATVEC_VECMATS_ID`). -/
private theorem fw8_vecmats_inj {m : ℕ} : Function.Injective (vecmatsV3_p4 (m := m)) := by
  intro l₁ l₂ h
  have h' : vecmats_p4 l₁ = vecmats_p4 l₂ := by
    funext j
    have h2 : (WithLp.toLp 2 (vecmats_p4 l₁ j) : V3) = WithLp.toLp 2 (vecmats_p4 l₂ j) :=
      congrFun h j
    rw [WithLp.ext_iff 2] at h2
    rwa [WithLp.ofLp_toLp, WithLp.ofLp_toLp] at h2
  exact (MATVEC_VECMATS_ID l₁).symm.trans
    ((congrArg (fun v : FinMat m 3 => matvec_p4 v) h').trans (MATVEC_VECMATS_ID l₂))

/-- fw8: the flattening of `vecmatsV3_p4 l` is `l` again. -/
private theorem fw8_vecmats_flat {m : ℕ} (l : FinVec m 3) :
    fw8_flat (vecmatsV3_p4 l) = l := by
  refine fw8_vecmats_inj ?_
  rw [fw8_flat_roundtrip (vecmatsV3_p4 l)]

/-- fw8: `rowV3_p9` at a `Fin` index (LA9 `fw6_row_fin` shape; the original is
private to LocalAuto9). -/
private theorem fw8_row_fin {m : ℕ} (l : FinVec m 3) (p : Fin m) :
    rowV3_p9 l (p.val + 1) = vecmatsV3_p4 l p := by
  unfold rowV3_p9
  rw [dif_pos (by exact ⟨by omega, by have := p.isLt; omega⟩)]
  refine congrArg (vecmatsV3_p4 l) (Fin.eq_of_val_eq ?_)
  show (p.val + 1 - 1 : ℕ) = p.val
  omega

/-- fw8: `rowV3_p9` at a ℕ index in `1..m`. -/
private theorem fw8_row_nat {m : ℕ} (l : FinVec m 3) (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
    rowV3_p9 l i = vecmatsV3_p4 l ⟨i - 1, by omega⟩ := by
  unfold rowV3_p9
  rw [dif_pos ⟨hi, him⟩]

/-- fw8 (G2 bridge): `azimInFan` ≡ `azimInFan_p2` on a fan dart — the
`ee`/`EE_p2` guard is definitional, the positive branch is
`AZIM_CYCLE_EQ_SIGMA_FAN_ALT` (LA2) after `EE_elim`. -/
private theorem fw8_azim_eq {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E)
    {e : V3 × V3} (hw : e.2 ∈ Fan.setOfEdge e.1 V E) :
    azimInFan e E = azimInFan_p2 e E := by
  -- LA1's `azimInFan` hardwires `sigmaFan 0 univ E`; transport to the fan's
  -- own vertex set through the `EE_elim`-equality of the two neighbour sets
  have hso : Fan.setOfEdge e.1 Set.univ E = Fan.setOfEdge e.1 V E := by
    rw [← EE_elim hfan e.1]
    simp [Fan.setOfEdge, EE_p2]
  have hsf : Fan.sigmaFan 0 Set.univ E e.1 e.2 = Fan.sigmaFan 0 V E e.1 e.2 := by
    unfold Fan.sigmaFan
    rw [hso]
  unfold azimInFan azimInFan_p2
  by_cases hnc : 1 < (ee e.1 E).ncard
  · rw [if_pos hnc, if_pos (show 1 < (EE_p2 e.1 E).ncard from hnc), hsf,
      EE_elim hfan e.1]
    exact congrArg (azim 0 e.1 e.2) (AZIM_CYCLE_EQ_SIGMA_FAN_ALT hfan hw).symm
  · rw [if_neg hnc, if_neg (show ¬(1 < (EE_p2 e.1 E).ncard) from hnc)]

/-- fw8: `setSum` respects pointwise equality of summands. -/
private theorem fw8_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) : setSum s f = setSum s g := by
  unfold setSum
  by_cases hs : Set.Finite s
  · rw [dif_pos hs, dif_pos hs]
    exact Finset.sum_congr rfl fun x hx => h x (hs.mem_toFinset.mp hx)
  · rw [dif_neg hs, dif_neg hs]

/-- fw8 (G3a+G3 bridges): `tauFun ≡ tauFun_p9` on a fan's dart set —
`rhoFun ≡ rhoFun_p9` is definitional, the azimuth factor is G2. -/
private theorem fw8_tauFun_eq {V : Set V3} {E : Set (Set V3)} {F : Set (V3 × V3)}
    (hfan : Fan.FAN 0 V E) (hdart : ∀ e ∈ F, e.2 ∈ Fan.setOfEdge e.1 V E) :
    tauFun V E F = tauFun_p9 V E F := by
  have hsum : ∀ e ∈ F, rhoFun ‖e.1‖ * azimInFan e E = rhoFun_p9 ‖e.1‖ * azimInFan_p2 e E := by
    intro e he
    calc rhoFun ‖e.1‖ * azimInFan e E = rhoFun ‖e.1‖ * azimInFan_p2 e E := by
          rw [fw8_azim_eq hfan (hdart e he)]
      _ = rhoFun_p9 ‖e.1‖ * azimInFan_p2 e E := rfl
  unfold tauFun tauFun_p9
  rw [fw8_setSum_congr hsum]

/-- fw8 (G1′ bridge, p4 → p9): `B_SY1_p4 aR bR ⊆ B_SY1_p9 m A B` whenever the
Fin tables are the `(p+1)`-shifts of the ℕ tables (`A (p+1) (q+1) = aR p q`). -/
private theorem fw8_memB9_of_memB4 {m : ℕ} {aR bR : Fin m → Fin m → ℝ}
    {A B : ℕ → ℕ → ℝ}
    (hsh : ∀ p q : Fin m, aR p q = A (p.val + 1) (q.val + 1) ∧
      bR p q = B (p.val + 1) (q.val + 1))
    {l : FinVec m 3} (hl : l ∈ (B_SY1_p4 aR bR : Set (FinVec m 3))) :
    l ∈ B_SY1_p9 m A B := by
  obtain ⟨w, hw, hfl⟩ := hl
  obtain ⟨hb, hc1, hc2⟩ := hw
  have hrt : vecmatsV3_p4 l = w := by
    have hfl' : fw8_flat w = l := hfl
    rw [← hfl']
    exact fw8_flat_roundtrip w
  rw [← hrt] at hb hc1
  have hc2' : convexLocalFan_p4 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)) := by
    rw [hrt]; exact hc2
  refine ⟨hb, ?_, hc2'⟩
  intro i j hi him hj hjm
  have pq : A ((⟨i - 1, by have := him; omega⟩ : Fin m).val + 1)
      ((⟨j - 1, by have := hjm; omega⟩ : Fin m).val + 1) = A i j := by
    show A (i - 1 + 1) (j - 1 + 1) = A i j
    rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]
  have pqB : B ((⟨i - 1, by have := him; omega⟩ : Fin m).val + 1)
      ((⟨j - 1, by have := hjm; omega⟩ : Fin m).val + 1) = B i j := by
    show B (i - 1 + 1) (j - 1 + 1) = B i j
    rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]
  have h1 := hc1 (⟨i - 1, by have := him; omega⟩ : Fin m)
    (⟨j - 1, by have := hjm; omega⟩ : Fin m)
  rw [(hsh _ _).1, (hsh _ _).2, pq, pqB, hrt] at h1
  rw [fw8_row_nat l i hi him, fw8_row_nat l j hj hjm, hrt]
  exact h1

/-- fw8 (G1′ bridge, p9 → p4): the reverse inclusion. -/
private theorem fw8_memB4_of_memB9 {m : ℕ} {aR bR : Fin m → Fin m → ℝ}
    {A B : ℕ → ℕ → ℝ}
    (hsh : ∀ p q : Fin m, aR p q = A (p.val + 1) (q.val + 1) ∧
      bR p q = B (p.val + 1) (q.val + 1))
    {l : FinVec m 3} (hl : l ∈ B_SY1_p9 m A B) :
    l ∈ (B_SY1_p4 aR bR : Set (FinVec m 3)) := by
  refine ⟨vecmatsV3_p4 l, ⟨hl.1, ?_, hl.2.2⟩, fw8_vecmats_flat l⟩
  intro p q
  have h := hl.2.1 (p.val + 1) (q.val + 1) (by omega) (by have := p.isLt; omega)
    (by omega) (by have := q.isLt; omega)
  rw [fw8_row_fin l p, fw8_row_fin l q] at h
  rw [(hsh p q).1, (hsh p q).2]
  exact h

/-- NEEDS (HOL CONTINUOUS_ON_TAU_FUN analog, general m): `tau_fun` is
continuous on the body set. Isolated roots, both outside the case bank:
  (i)  darts-injectivity on the body (INJ_B_SY twin; root
       `PROPERTIES_OF_FAN_IN_B_SY_p11` = sorry giant, LA11:1489, HOL
       TECOXBM.hl:207);
  (ii) `azimInFan` continuity along the cyclic darts (HOL
       CONTINUOUS_ON_RHO_FUN_AND_AZIM, HDPLYGY.hl:1534-1770; Lean roots
       SEQUENTIALLY_DIVH_p9 / COLLINEAR_B_SY_p9 / AZIM_EQ_DIHV_IN_B_SY_p9,
       LA9:568-660, all rooted at (i)).
la23-analysis (2026-10-28) addenda: the promised reduction
`continuousOn_tauFun_of_azim_p23` does NOT exist in this file. Numeric recon
(snapshots/la23-analysis): no falsity evidence — `fan7` blocks every
multiplicity-change approach path tried (vertex splits of the fan-legal
periodic point `(q,r,s,q,r,s)` violate fan7 by cone overlap), yet dart
collisions DO occur fan-legally on the body (`ncard F_SY = 3 < 6` there), so
the missing lemma is local constancy of the collision pattern under `fan7`,
then the standard re-index (`CHANGE_SUM_TAU_FUN_p9` twin) plus (ii).
REPAIRED (SF-91 案②, 2026-10-28): the frozen strong form took arbitrary
`aR bR`. The carrier premise is now the full `stableSystem_p23` (LA23:146,
verbatim twin of dih2k.hl:61-67 — the HOL `stable_sy` record's class
invariant) over existentially witnessed ℕ tables, with `f` pinned to the
cyclic successor `fun i => (1 + i) % m` — exactly the tuple
`IS_SCS_STABLE_SYSTEM_p23` (LA23:762) supplies, so the CASE_4/5/6 consumers
feed it in one step (LA24 `fullStable_of_isScsV39`, SF-89 `stabAdj` mode).
The shifted-agreement legs tie the witnesses to the Fin tables the
conclusion ranges over (`rfl` at the consumers: `aRk s i j = s.a
((i+1)%k) ((j+1)%k)` by definition).  Why the full carrier and not the
三条款 minimal form: the W8 discharge builds a `StableSyP9` record for
`CONTINUOUS_ON_TAU_FUN_p9` (LA9) whose `prop` is the whole
`constraintSystem_p9` bundle — three clauses cannot build the record
(fanchain-w7 DELIVERY §6 item 5).  Honest edges: the p23 `d` slot is the
unused HOL dummy and the S10 tauFun chain is `d`-blind, so the future
record's `d_sy` is NOT pinned here (W8 selects it freely); `J_SY` reaches
the p9 `Finset` shape through the Set→Finset container bridge; `f` had to
be pinned explicitly because `torsor` alone does not force the successor
(any single k-cycle is a torsor witness, e.g. `fun i => (i+2) % m` for odd
m — 91b machine check C4).  `hm : 2 < m` is kept as an explicit premise
for §89/bodyClosed parity at the shared feed sites although carrier clause
1 (`3 ≤ m`) already implies it.  W8 bridge plan: fanchain-w7 DELIVERY §6
(G1′/G2/G3/G3a).
(Discharged fanchain-w8: the full-carrier premise builds a `StableSyP9`
record (wrapped tables `fun i j => a (i % m) (j % m)`, faithful filtered-image
`J_SY`, `d_sy := 0` free dummy) and `CONTINUOUS_ON_TAU_FUN_p9` (LA9, W7,
standard three axioms) transports along the G1' body-set bridge and the
G3a+G2+G3 tauFun bridge.  Root 1/2 of this kit is closed.) -/
theorem continuousOn_tauFun_p23 {m : ℕ} (aR bR : Fin m → Fin m → ℝ)
    (hm : 2 < m)
    (hstab : ∃ a b : ℕ → ℕ → ℝ, ∃ J : Set (Set ℕ),
      stableSystem_p23 m 0 (Set.Iic (m - 1)) a b J (fun i => (1 + i) % m) ∧
      (∀ i j : Fin m, a (((i : ℕ) + 1) % m) (((j : ℕ) + 1) % m) = aR i j) ∧
      (∀ i j : Fin m, b (((i : ℕ) + 1) % m) (((j : ℕ) + 1) % m) = bR i j)) :
    ContinuousOn (fun l : FinVec m 3 =>
      tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (F_SY_p4 (vecmatsV3_p4 l))) (B_SY1_p4 aR bR) := by
  -- W8 discharge (fanchain-w8): build the StableSyP9 record from the full
  -- stableSystem_p23 carrier and transport along G1′/G3a+G2+G3 into
  -- CONTINUOUS_ON_TAU_FUN_p9 (LA9, standard three axioms).
  obtain ⟨a, b, J, hcar, hsa, hsb⟩ := hstab
  obtain ⟨hsys, hS2, hS3, hS4⟩ := hcar
  obtain ⟨h3m, hm6, htorsor, hsymm, -, hJsub, hJcard⟩ := hsys
  -- faithful Set→Finset container bridge for J (sf91b Evidence §3, C3/C6)
  haveI hdec : DecidablePred (fun p : Finset ℕ => (p : Set ℕ) ∈ J) :=
    fun _ => Classical.propDecidable _
  set J_SY : Finset (Finset ℕ) := ((Finset.Icc 0 (m - 1)).image
      (fun i : ℕ => ({i, (1 + i) % m} : Finset ℕ))).filter
      (fun p : Finset ℕ => (p : Set ℕ) ∈ J) with hJ_SY
  have hIfin : ((Set.Iic (m - 1) : Set ℕ)).Finite := Set.finite_Iic (m - 1)
  have hJfin : J.Finite :=
    Set.Finite.subset (hIfin.image fun i : ℕ => ({i, (1 + i) % m} : Set ℕ)) (by
      intro e he
      obtain ⟨i, hi, rfl⟩ := hJsub he
      exact ⟨i, hi, rfl⟩)
  -- G1′ shift pairing: Fin row (p, q) reads ℕ row (p+1, q+1) of the wrapped
  -- tables (the %m wrap absorbs the row-m ↔ row-0 wrap line)
  have hsh : ∀ p q : Fin m, aR p q = a ((p.val + 1) % m) ((q.val + 1) % m) ∧
      bR p q = b ((p.val + 1) % m) ((q.val + 1) % m) :=
    fun p q => ⟨(hsa p q).symm, (hsb p q).symm⟩
  -- record clause: torsor over Icc 0 (m-1)
  have htorsor9 : torsor_p9 (Finset.Icc 0 (m - 1)) m (fun i => (1 + i) % m) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; exact fw8_mem_Icc.mpr (htorsor.1 x (fw8_mem_Icc.mp hx))
    · intro x₁ hx₁ x₂ hx₂ h12
      exact htorsor.2.1 x₁ (fw8_mem_Icc.mp hx₁) x₂ (fw8_mem_Icc.mp hx₂) h12
    · intro n x hn hnm hx
      exact htorsor.2.2.1 n x hn hnm (fw8_mem_Icc.mp hx)
    · intro x hx; exact htorsor.2.2.2.1 x (fw8_mem_Icc.mp hx)
    · rw [Nat.card_Icc]; omega
  -- record clause: 2 ≤ a off-diagonal (wrapped tables)
  have hS2' : ∀ i ∈ (Finset.Icc 0 (m - 1) : Finset ℕ),
      ∀ j ∈ (Finset.Icc 0 (m - 1) : Finset ℕ), i ≠ j →
        2 ≤ (fun i j => a (i % m) (j % m)) i j := by
    intro i hi j hj hne
    have hi' := fw8_mem_Icc.mp hi
    have hj' := fw8_mem_Icc.mp hj
    show 2 ≤ a (i % m) (j % m)
    rw [Nat.mod_eq_of_lt (by have := Set.mem_Iic.mp hi'; omega),
      Nat.mod_eq_of_lt (by have := Set.mem_Iic.mp hj'; omega)]
    exact hS2 i hi' j hj' hne
  -- record clause: diagonal + cstab (cstab = cstab_p4 = 3.01, sf91b C8)
  have hS3' : ∀ i ∈ (Finset.Icc 0 (m - 1) : Finset ℕ),
      (fun i j => a (i % m) (j % m)) i i = 0 ∧
        (fun i j => b (i % m) (j % m)) i ((fun i => (1 + i) % m) i) ≤ cstab_p4 := by
    intro i hi
    have hi' := fw8_mem_Icc.mp hi
    obtain ⟨h3a, h3b⟩ := hS3 i hi'
    have hii : i % m = i := Nat.mod_eq_of_lt (by have := Set.mem_Iic.mp hi'; omega)
    have hfi : ((1 + i) % m) % m = (1 + i) % m := Nat.mod_mod _ _
    refine ⟨?_, ?_⟩
    · show a (i % m) (i % m) = 0
      rw [hii]; exact h3a
    · show b (i % m) (((1 + i) % m) % m) ≤ cstab_p4
      rw [hii, hfi]; exact h3b
  -- record clause: J-edges carry √8 / cstab
  have hS4' : ∀ i j : ℕ, {i, j} ∈ J_SY →
      (fun i j => a (i % m) (j % m)) i j = Real.sqrt 8 ∧
        (fun i j => b (i % m) (j % m)) i j = cstab_p4 := by
    intro i j hij
    have hmem := (Finset.mem_filter.mp hij).1
    have hq : ({i, j} : Set ℕ) ∈ J := by
      have hq' := (Finset.mem_filter.mp hij).2
      simpa [Finset.coe_insert, Finset.coe_singleton] using hq'
    obtain ⟨i₀, hi₀, hpi⟩ := Finset.mem_image.mp hmem
    have hi₀' : i₀ ≤ m - 1 := by
      have := Finset.mem_Icc.mp hi₀; omega
    have hfi₀ : (1 + i₀) % m ≤ m - 1 := htorsor.1 i₀ hi₀'
    have hii : i ∈ ({i₀, (1 + i₀) % m} : Finset ℕ) := by
      rw [hpi]; exact Finset.mem_insert_self i {j}
    have hjj : j ∈ ({i₀, (1 + i₀) % m} : Finset ℕ) := by
      rw [hpi]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    have him : i ≤ m - 1 := by
      rcases Finset.mem_insert.mp hii with hc | hc
      · omega
      · have := Finset.mem_singleton.mp hc; omega
    have hjm : j ≤ m - 1 := by
      rcases Finset.mem_insert.mp hjj with hc | hc
      · omega
      · have := Finset.mem_singleton.mp hc; omega
    show a (i % m) (j % m) = Real.sqrt 8 ∧ b (i % m) (j % m) = cstab_p4
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact hS4 i j hq
  -- the record: k=m, d=0 (unused dummy), I=Icc 0 (m-1), f=pinned successor
  have hprop : stableSystem_p9 m 0 (Finset.Icc 0 (m - 1))
      (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m)) J_SY
      (fun i => (1 + i) % m) := by
    refine ⟨?_, hS2', hS3', hS4'⟩
    refine ⟨h3m, hm6, htorsor9, fun i j => hsymm (i % m) (j % m), ?_, ?_, ?_⟩
    · -- period clause: f^[m] j ≡ j (mod m) makes the wrapped table periodic
      intro i j
      have hmod : ((fun i => (1 + i) % m)^[m] j) % m = j % m := by
        rw [fw8_iter_mod m m j, Nat.add_mod_left]
      constructor
      · show a (i % m) (j % m) = a (i % m) (((fun i => (1 + i) % m)^[m] j) % m)
        rw [hmod]
      · show b (i % m) (j % m) = b (i % m) (((fun i => (1 + i) % m)^[m] j) % m)
        rw [hmod]
    · -- C5: J_SY ⊆ edge image
      rw [hJ_SY]
      exact Finset.filter_subset _ _
    · -- C6: card bridge through the coe injection into J
      haveI : Finite (J : Set (Set ℕ)) := hJfin.to_subtype
      have hcard1 : Nat.card ((J_SY : Finset (Finset ℕ)) : Set (Finset ℕ))
          ≤ Nat.card (J : Set (Set ℕ)) :=
        Nat.card_le_card_of_injective
          (fun p : {x : Finset ℕ // x ∈ ((J_SY : Finset (Finset ℕ)) : Set (Finset ℕ))} =>
            ⟨((p.1 : Finset ℕ) : Set ℕ), (Finset.mem_filter.mp p.2).2⟩)
          (fun x y hxy => Subtype.ext (Finset.coe_injective (Subtype.ext_iff.mp hxy)))
      have hcardFin : Nat.card ((J_SY : Finset (Finset ℕ)) : Set (Finset ℕ)) = J_SY.card :=
        (Nat.card_eq_fintype_card).trans (Fintype.card_coe J_SY)
      have hc := hcard1
      have hf := hcardFin
      rw [← hf]
      omega
  -- LA9 S10 with the record; StableSysHyp_p9 is definitional here
  have h9 : ContinuousOn (fun l : FinVec m 3 => tauFun_p9 (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
      (B_SY1_p9 m (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m))) :=
    CONTINUOUS_ON_TAU_FUN_p9
      (⟨m, 0, Finset.Icc 0 (m - 1), fun i j => a (i % m) (j % m),
        fun i j => b (i % m) (j % m), J_SY, fun i => (1 + i) % m, hprop⟩ : StableSyP9)
      ⟨rfl, rfl, rfl, hm⟩
  -- G1′: the two body sets agree
  have hBeq : B_SY1_p9 m (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m))
      = (B_SY1_p4 aR bR : Set (FinVec m 3)) :=
    Set.ext fun l => ⟨fun hl => @fw8_memB4_of_memB9 m aR bR
      (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m)) hsh l hl,
      fun hl => @fw8_memB9_of_memB4 m aR bR
      (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m)) hsh l hl⟩
  -- G3a + G2 + G3: tauFun ≡ tauFun_p9 pointwise on the body
  have hfw : Set.EqOn (fun l : FinVec m 3 => tauFun (V_SY_p4 (vecmatsV3_p4 l))
      (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
      (fun l : FinVec m 3 => tauFun_p9 (V_SY_p4 (vecmatsV3_p4 l))
        (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
      (B_SY1_p4 aR bR) := by
    intro l hl
    have hl9 := @fw8_memB9_of_memB4 m aR bR
      (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m)) hsh l hl
    refine fw8_tauFun_eq hl9.2.2.1.1 ?_
    intro e he
    obtain ⟨i, -, rfl⟩ := he
    exact ⟨EDGE_IN_E_SY l i, ⟨finNext i, rfl⟩⟩
  rw [hBeq] at h9
  exact ContinuousOn.congr h9 hfw

/-! ### bodyclosed-w2b: private G-B2 carrier translation

Code copied verbatim from bodyclosed-w2's `bcw2_stableSystem_p18_of_p23`
(LA18 block) with the `p18` names redirected to the `ClosedSyKit` twins
(`torsor_cs` / `stableSystem_cs` / `POWER_MOD_FUN_cs`).  The
`stableSystem_p23` carrier over `Set.Iic (m-1)` with the successor cycle
(SF-89b shape) translates to the `stableSystem_cs` carrier over
`Finset.Icc 0 (m-1)` with the `% m`-wrapped tables; the edge set is
re-rendered as a `Finset (Finset ℕ)` injected into `J` (cardinality is all
the carrier clause consumes).  Private: LA23-internal glue for
`bodyClosed_p23`; fully proved, zero proof debt. -/

private theorem bcw2b_stableSystem_cs_of_p23 {m : ℕ} {a b : ℕ → ℕ → ℝ}
    {J : Set (Set ℕ)}
    (hsys : stableSystem_p23 m 0 (Set.Iic (m - 1)) a b J (fun i => (1 + i) % m)) :
    ∃ Jf : Finset (Finset ℕ),
      stableSystem_cs m 0 (Finset.Icc 0 (m - 1))
        (fun i j => a (i % m) (j % m)) (fun i j => b (i % m) (j % m)) Jf
        (fun i => (1 + i) % m) := by
  obtain ⟨hcar, hS2, hS3, hS4⟩ := hsys
  obtain ⟨h3m, hm6, ht, hsymm, hper, hJsub, hJcard⟩ := hcar
  have hm0 : 0 < m := by omega
  have hmemS : ∀ x : ℕ, x ≤ m - 1 → x ∈ (Finset.Icc 0 (m - 1) : Finset ℕ) :=
    fun x hx => Finset.mem_Icc.mpr ⟨by omega, hx⟩
  have hIic : ∀ x : ℕ, x ∈ (Finset.Icc 0 (m - 1) : Finset ℕ) → x ∈ Set.Iic (m - 1) :=
    fun x hx => Set.mem_Iic.mpr (Finset.mem_Icc.mp hx).2
  -- torsor: clause translation (outputs re-bridged Iic → Icc); card computed
  have ht18 : torsor_cs (Finset.Icc 0 (m - 1)) m (fun i => (1 + i) % m) := by
    refine ⟨fun x hx => hmemS _ (ht.1 x (hIic x hx)),
      fun x₁ hx₁ x₂ hx₂ h12 => ht.2.1 x₁ (hIic x₁ hx₁) x₂ (hIic x₂ hx₂) h12,
      fun i x hi hik hx => ht.2.2.1 i x hi hik (hIic x hx),
      fun x hx => ht.2.2.2.1 x (hIic x hx), ?_⟩
    rw [Nat.card_Icc]
    omega
  -- J container: finiteness of J (subset of a finite edge image)
  have hIicfin : (Set.Iic (m - 1) : Set ℕ).Finite := Set.finite_Iic _
  have hJfin : J.Finite := Set.Finite.subset
    (hIicfin.image (fun i : ℕ => ({i, (1 + i) % m} : Set ℕ))) (by
      intro S hS
      obtain ⟨i, hi, rfl⟩ := hJsub hS
      exact ⟨i, hi, rfl⟩)
  -- the Finset-graded preimage of J under the coercion
  have hJcfin : {e : Finset ℕ | (e : Set ℕ) ∈ J}.Finite := Set.Finite.subset
    (hIicfin.image (fun i : ℕ => ({i, (1 + i) % m} : Finset ℕ))) (by
      intro e he
      obtain ⟨i, hi, hxe⟩ := hJsub he
      refine Set.mem_image _ _ _ |>.mpr ⟨i, hi, ?_⟩
      refine Finset.coe_injective ?_
      simp only [Finset.coe_insert, Finset.coe_singleton]
      exact hxe.symm)
  -- edges of J have both endpoints < m
  have hlt_of_memJ : ∀ i j : ℕ, ({i, j} : Set ℕ) ∈ J → i < m ∧ j < m := by
    intro i j hij
    obtain ⟨p, hp, hpx⟩ := hJsub hij
    have hii : i ∈ ({p, (1 + p) % m} : Set ℕ) := by rw [← hpx]; simp
    have hjj : j ∈ ({p, (1 + p) % m} : Set ℕ) := by rw [← hpx]; simp
    have hp' : p ≤ m - 1 := Set.mem_Iic.mp hp
    refine ⟨?_, ?_⟩
    · rcases hii with rfl | rfl
      · omega
      · exact Nat.mod_lt (1 + p) hm0
    · rcases hjj with rfl | rfl
      · omega
      · exact Nat.mod_lt (1 + p) hm0
  -- wrapped-table clauses of the carrier
  have hsymm18 : ∀ i j : ℕ, a (i % m) (j % m) = a (j % m) (i % m) ∧
      b (i % m) (j % m) = b (j % m) (i % m) ∧ a (i % m) (j % m) ≤ b (i % m) (j % m) :=
    fun i j => ⟨(hsymm (i % m) (j % m)).1, (hsymm (i % m) (j % m)).2.1,
      (hsymm (i % m) (j % m)).2.2⟩
  have hper18 : ∀ i j : ℕ, a (i % m) (j % m) =
      a (i % m) ((fun j => (1 + j) % m)^[m] j % m) ∧
      b (i % m) (j % m) = b (i % m) ((fun j => (1 + j) % m)^[m] j % m) := by
    have hpm : ∀ x : ℕ, ((fun j => (1 + j) % m)^[m] x) % m = x % m := by
      intro x
      rw [POWER_MOD_FUN_cs m x m (by omega) (by omega), Nat.add_mod_left, Nat.mod_mod]
    exact fun i j => ⟨by rw [hpm j], by rw [hpm j]⟩
  have hS218 : ∀ i ∈ (Finset.Icc 0 (m - 1) : Finset ℕ),
      ∀ j ∈ (Finset.Icc 0 (m - 1) : Finset ℕ), i ≠ j → 2 ≤ a (i % m) (j % m) := by
    intro i hi j hj hne
    rw [Nat.mod_eq_of_lt (by have := Finset.mem_Icc.mp hi; omega),
      Nat.mod_eq_of_lt (by have := Finset.mem_Icc.mp hj; omega)]
    exact hS2 i (hIic i hi) j (hIic j hj) hne
  have hS318 : ∀ i ∈ (Finset.Icc 0 (m - 1) : Finset ℕ),
      a (i % m) (i % m) = 0 ∧
        b (i % m) ((fun i => (1 + i) % m) i % m) ≤ cstab_p4 := by
    intro i hi
    have him : i < m := by have := Finset.mem_Icc.mp hi; omega
    obtain ⟨h3a, h3b⟩ := hS3 i (hIic i hi)
    refine ⟨?_, ?_⟩
    · rw [Nat.mod_eq_of_lt him]; exact h3a
    · rw [Nat.mod_eq_of_lt him, Nat.mod_mod]
      exact h3b
  have hS418 : ∀ i j : ℕ, ({i, j} : Finset ℕ) ∈ hJcfin.toFinset →
      a (i % m) (j % m) = Real.sqrt 8 ∧ b (i % m) (j % m) = cstab_p4 := by
    intro i j hij
    have hmemJ : ({i, j} : Set ℕ) ∈ J := by
      have h := (Set.Finite.mem_toFinset hJcfin).mp hij
      simpa only [Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton] using h
    obtain ⟨h8, hb8⟩ := hS4 i j hmemJ
    obtain ⟨him, hjm⟩ := hlt_of_memJ i j hmemJ
    exact ⟨by rw [Nat.mod_eq_of_lt him, Nat.mod_eq_of_lt hjm]; exact h8,
      by rw [Nat.mod_eq_of_lt him, Nat.mod_eq_of_lt hjm]; exact hb8⟩
  have hJsub18 : hJcfin.toFinset ⊆
      (Finset.Icc 0 (m - 1)).image (fun i : ℕ => ({i, (1 + i) % m} : Finset ℕ)) := by
    intro e he
    have hE : (e : Set ℕ) ∈ J := (Set.Finite.mem_toFinset hJcfin).mp he
    obtain ⟨i, hi, hxe⟩ := hJsub hE
    refine Finset.mem_image.mpr ⟨i, hmemS i (Set.mem_Iic.mp hi), ?_⟩
    refine Finset.coe_injective ?_
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact hxe.symm
  have hJcard18 : hJcfin.toFinset.card + m ≤ 6 := by
    have h1 : (hJcfin.toFinset.image (fun e : Finset ℕ => (e : Set ℕ))) ⊆
        hJfin.toFinset := by
      intro S hS
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hS
      have hJ' : (e : Set ℕ) ∈ J := by
        have h := (Set.Finite.mem_toFinset hJcfin).mp he
        simpa only [Set.mem_setOf_eq] using h
      exact (Set.Finite.mem_toFinset (s := J) (a := (e : Set ℕ)) hJfin).mpr hJ'
    have hinjOn : Set.InjOn (fun e : Finset ℕ => (e : Set ℕ))
        (hJcfin.toFinset : Finset (Finset ℕ)) :=
      fun p _ q _ hpq => Finset.coe_injective hpq
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injOn hinjOn] at h2
    have h4 : Nat.card ↑J = hJfin.toFinset.card :=
      (Nat.card_coe_set_eq J).trans (Set.ncard_eq_toFinset_card J hJfin)
    omega
  refine ⟨hJcfin.toFinset, ⟨⟨h3m, hm6, ht18, hsymm18, hper18, hJsub18, hJcard18⟩,
    hS218, hS318, hS418⟩⟩

/-- NEEDS (HOL CLOSED_SY analog, general m): the joint body locus is closed.
The (annulus ∧ CONDITION1) factor is CLEAN (`annulus_c1_closed_p23`); the
genuine content is the CONDITION2 (fan) factor — HOL CLOSED_SY
(WJSCPRO.hl:63-3174, sequential limits through the fan-convexity clause);
Lean carrier `CLOSED_SY_p18` (LA18:236, `stableSystem_p18`-indexed form)
needs reindexing glue. The joint (not isolated-fan) form is kept because the
isolated fan-factor closedness is unverified (la23prereq-w1 PREREQ-PLAN §1
leg-3 shape note).
la23-analysis (2026-10-28) WARNING: at THIS generality (arbitrary `aR bR`,
no stability bounds) the statement is probably FALSE — numeric recon
(snapshots/la23-analysis) gives the flex family `m=3, aR≡0, bR≡5`,
rows `(2.2·e(0°), 2.2·e(60°+δ), 2.2·e(240°))`: every small δ>0 satisfies
CONDITION2 (verified against the exact `FAN`/`localFan_p4`/`convexLocalFan_p4`
clauses incl. fan7 and the hypermap face structure), the family converges to
the δ=0 config where the edge `{r,s}` is antiparallel through 0, so `fan6`
fails and CONDITION2 fails — the locus is not closed. HOL CLOSED_SY needs
its stableSystem context (adjacent-edge upper bound `≤ cstab`: antiparallel
annulus rows force edge length ≥ 4 > 3.01). REPAIRED (SF-89, 2026-10-28):
stability-shaped hypotheses added — `hm : 2 < m` (HOL `2 < k`) and
`hstab : ∀ i : Fin m, bR i (finNext i) ≤ cstab_p4` (HOL stable_system's
`b(i, f i) ≤ cstab` clause, dih2k.hl:65; carrier twin `CLOSED_SY_p18`
LA18:236 takes the full `stableSystem_p18`); discharged at the CASE_4/5/6
consumers from `isScsV39` via `stabAdj_of_isScsV39` (LA24: the `3 < s.k →
s.b i (i + 1) ≤ cstab` conjunct shifted onto the `aRk/bRk` tables). The
flex family above is out of scope: `bR ≡ 5` fails `hstab` (5 > 3.01).
(Sorry 2/2 of this kit.)
REPAIRED AGAIN (SF-89b, 2026-11-02, bodyclosed-recon): the SF-89 minimal
two-clause premise is still insufficient — HOL CLOSED_SY's proof consumes
three stable_system clauses (`2 ≤ a(i,j)` dih2k.hl:64 at the limit-point
sandwich / row-distinctness / six wrap sites, `b(i,f i) ≤ cstab` :65,
periodicity constraint_system :57), and the m=6 collapse family (angles
(0,δ,85,170,255,340)°, R=2.2, aR≡0, bR ring-adjacent 3.0 ≤ cstab) stays in
the body for every δ>0 while its δ=0 limit (row 0 = row 1 ⇒ `E_SY` singleton
edge ⇒ Graph false) leaves CONDITION2 — the minimal-form locus is not
closed. `hstab` is therefore upgraded to the full `stableSystem_p23` carrier,
verbatim the shape of `continuousOn_tauFun_p23` (SF-91 案②); the CASE_4/5/6
consumers feed it with the already-proved `fullStable_of_isScsV39` (LA24),
exactly as the tauFun feed. Discharge route (B): bridge to LA18
`CLOSED_SY_p18`. EXECUTED (bodyclosed-w2b, 2026-10-28): via the
`Kepler.Text.ClosedSyKit` twin `CLOSED_SY_cs` — LA23 cannot import LA18
(LA18→LA27→LA24→LA23 cycle), so the carrier kit moved upstream of LA23;
G-B2 (`bcw2b_stableSystem_cs_of_p23`, above) + G-B1
(`bcw2b_bodyClosed_of_SYset_cs`, ClosedSyKit) assemble below. -/
theorem bodyClosed_p23 {m : ℕ} (aR bR : Fin m → Fin m → ℝ) (hm : 2 < m)
    (hstab : ∃ a b : ℕ → ℕ → ℝ, ∃ J : Set (Set ℕ),
      stableSystem_p23 m 0 (Set.Iic (m - 1)) a b J (fun i => (1 + i) % m) ∧
      (∀ i j : Fin m, a (((i : ℕ) + 1) % m) (((j : ℕ) + 1) % m) = aR i j) ∧
      (∀ i j : Fin m, b (((i : ℕ) + 1) % m) (((j : ℕ) + 1) % m) = bR i j)) :
    IsClosed {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v} := by
  obtain ⟨a, b, J, hcar, hsa, hsb⟩ := hstab
  obtain ⟨Jf, hsys_cs⟩ := bcw2b_stableSystem_cs_of_p23 hcar
  exact bcw2b_bodyClosed_of_SYset_cs aR bR _ _
    (fun p q => hsa p q) (fun p q => hsb p q)
    (CLOSED_SY_cs hsys_cs (by ext x; simp) rfl (by omega) hm)

/-- the EVT core of HDPLYGY / MINIMUM_IN_B_SY (Mathlib only, CLEAN). -/
theorem hdplygy_min_core_p23 {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {f : β → ℝ} {K : Set β} (hK : IsCompact K) (hne : K.Nonempty)
    (hcont : ContinuousOn f K) : ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hcont
  exact ⟨x, hx, fun _ hy => hmin hy⟩

/-- HOL `HDPLYGY` (HDPLYGY.hl:1831) port: the `tau_star` minimizer over the
body set, with the two hard legs as explicit hypotheses. -/
theorem HDPLYGY_p23 {m : ℕ} (s1 : StableSyP23) (aR bR : Fin m → Fin m → ℝ)
    (hcomp : IsCompact (B_SY1_p4 aR bR : Set (FinVec m 3)))
    (hcont : ContinuousOn (tauStar_p23 s1) (B_SY1_p4 aR bR))
    (hne : (B_SY1_p4 aR bR : Set (FinVec m 3)) ≠ ∅) :
    ∃ x : FinVec m 3, x ∈ B_SY1_p4 aR bR ∧
      ∀ y : FinVec m 3, y ∈ B_SY1_p4 aR bR → tauStar_p23 s1 x ≤ tauStar_p23 s1 y :=
  hdplygy_min_core_p23 hcomp (Set.nonempty_iff_ne_empty.mpr hne) hcont

/-- HOL `CONTINUOUS_ON_TAU_STAR` (HDPLYGY.hl:1805): glue only. -/
theorem continuousOn_tauStar_p23 {m : ℕ} (s1 : StableSyP23)
    (aR bR : Fin m → Fin m → ℝ)
    (hd : ContinuousOn (fun l : FinVec m 3 => dFun_p23 s1 l) (B_SY1_p4 aR bR))
    (hfun : ContinuousOn (fun l : FinVec m 3 =>
      tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
        (F_SY_p4 (vecmatsV3_p4 l))) (B_SY1_p4 aR bR)) :
    ContinuousOn (tauStar_p23 s1) (B_SY1_p4 aR bR) := by
  unfold tauStar_p23
  exact ContinuousOn.sub hfun hd

/-- compactness reduction (Heine–Borel + continuous flattening; glue). -/
theorem B_SY1_p4_compact_of_fan_p23 {m : ℕ} (aR bR : Fin m → Fin m → ℝ)
    (hcl : IsClosed {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v})
    (hbd : Bornology.IsBounded {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v}) :
    IsCompact (B_SY1_p4 aR bR : Set (FinVec m 3)) := by
  have hS : IsCompact {v : Fin m → V3 | (∀ i, v i ∈ ballAnnulus) ∧
      CONDITION1_SY_p4 aR bR v ∧ CONDITION2_SY_p4 v} :=
    Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hcont : Continuous (fun (v : Fin m → V3) (i : Fin (m * 3)) =>
      (v ⟨(i : ℕ) / 3, (Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr i.isLt⟩ :
            Fin 3 → ℝ) ⟨(i : ℕ) % 3, Nat.mod_lt (i : ℕ) (by norm_num : 0 < 3)⟩) := by
    fun_prop
  exact hS.image hcont

/-! ### the SF-C3 d-part identity and the TAUSTAR core (probe A) -/

/-- LA36 `vecmatsV3_flattenRow_p36` twin (LA23 stays LA36-free). -/
theorem vecmatsV3_flattenRow_p23 {k : ℕ} (vv : ℕ → V3) :
    vecmatsV3_p4 (flattenRow_p23 vv k) = cycRow_p23 vv k := by
  funext j
  have h1 : flattenRow_p23 vv k
      = matvec_p4 (fun j : Fin k => (cycRow_p23 vv k j : Fin 3 → ℝ)) := by
    funext i
    simp only [flattenRow_p23, matvec_p4]
  have h2 : vecmats_p4 (flattenRow_p23 vv k) j = (cycRow_p23 vv k j : Fin 3 → ℝ) := by
    rw [h1, VECMATS_MATVEC_ID]
  show (WithLp.toLp 2 (vecmats_p4 (flattenRow_p23 vv k) j) : V3) = cycRow_p23 vv k j
  rw [h2, WithLp.toLp_ofLp]

/-- row `m < k` of the flattening reads back as the cyclic row. -/
theorem rowSy_flattenRow_p23 {k : ℕ} (vv : ℕ → V3) (m : ℕ) (hm : m < k) :
    rowSy_p23 (flattenRow_p23 vv k) m = vv ((m + 1) % k) := by
  rw [rowSy_p23, dif_pos hm, vecmatsV3_flattenRow_p23]
  rfl

/-- generic setSum reindexing (LA12 `setSum_image_bij` twin). -/
private theorem setSum_image_bij_p23 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (φ : β → α) {A : Set α} {B : Set β} {f : α → ℝ} {g : β → ℝ}
    (hB : B.Finite) (hmem : ∀ x ∈ B, φ x ∈ A) (hinj : Set.InjOn φ B)
    (hsurj : ∀ y ∈ A, ∃ x ∈ B, φ x = y) (hfg : ∀ x ∈ B, g x = f (φ x)) :
    setSum A f = setSum B g := by
  have hAB : A = φ '' B := by
    refine Set.ext fun z => ?_
    simp only [Set.mem_image]
    constructor
    · intro hz
      obtain ⟨x, hx, hφ⟩ := hsurj z hz
      exact ⟨x, hx, hφ⟩
    · rintro ⟨x, hx, rfl⟩
      exact hmem x hx
  rw [hAB, setSum, setSum, dif_pos (hB.image φ), dif_pos hB,
    Set.Finite.toFinset_image φ hB (hB.image φ),
    Finset.sum_image fun x hx y hy => hinj (by simpa using hx) (by simpa using hy)]
  refine Finset.sum_congr rfl fun x hx => ?_
  exact (hfg x (hB.mem_toFinset.mp hx)).symm

private theorem setSum_congr_p23 {α : Type*} {S : Set α} {f g : α → ℝ}
    (h : ∀ i ∈ S, f i = g i) : setSum S f = setSum S g := by
  simp only [setSum]
  split
  · rename_i hfin
    exact Finset.sum_congr rfl fun i hi => h i (hfin.mem_toFinset.mp hi)
  · rfl

private theorem j1Sy_eq_image_p23 (s1 : StableSyP23) :
    J1_SY_p23 s1 = (fun i : ℕ => (i, i % s1.k + 1)) ''
      {i : ℕ | i ∈ Set.Icc 1 s1.k ∧ ({i % s1.k, s1.f (i % s1.k)} : Set ℕ) ∈ s1.J} := by
  ext x
  simp only [J1_SY_p23, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨i, hmem, hicc, rfl⟩
    exact ⟨i, ⟨hicc, hmem⟩, rfl⟩
  · rintro ⟨i, ⟨hicc, hmem⟩, rfl⟩
    exact ⟨i, hmem, hicc, rfl⟩

/-- `{a, b} ∈ scsJSet s` for in-range `a b` is exactly `s.J a b`. -/
private theorem scsJSet_pair_mem_iff_p23 (s : ScsV39) (hs : isScsV39 s)
    (a b : ℕ) (ha : a < s.k) (hb : b < s.k) :
    ({a, b} : Set ℕ) ∈ scsJSet_p23 s ↔ s.J a b := by
  have hsym : ∀ i j, s.J i j = s.J j i :=
    fun i j => (hs.2.2.2.2.2.2.2.2.2.2.2.2.1 i j).2.2.2.2
  constructor
  · rintro ⟨i, j, hi, hj, hJ, hpair⟩
    rcases Set.pair_eq_pair_iff.mp hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact e1 ▸ e2 ▸ hJ
    · rw [hsym a b]; exact e2 ▸ e1 ▸ hJ
  · exact fun hJ => ⟨a, b, ha, hb, hJ, rfl⟩

/-- `earSy` is false for the record at `k > 3` (`I = Iic (k-1)` has card k). -/
private theorem not_earSy_scs_p23 (s : ScsV39) (hs : isScsV39 s) (hk3 : 3 < s.k) :
    ¬ earSy_p23 (scsToStableSy_p23 s hs hk3) := by
  intro he
  have hcard : Nat.card (Set.Iic ((s.k - 1 : ℕ))) = s.k := by
    rw [Nat.card_coe_set_eq, Set.ncard_Iic_nat]; omega
  have h1 : Nat.card (Set.Iic ((s.k - 1 : ℕ))) = 3 := by
    have h := he.1
    simp only [scsToStableSy_p23] at h
    exact h
  omega

/-- `isEarV39` needs `k = 3`. -/
private theorem not_isEarV39_of_gt3_p23 (s : ScsV39) (hk3 : 3 < s.k) : ¬ isEarV39 s := by
  intro he
  obtain ⟨-, -, hk, -, -, -⟩ := he
  omega

/-- THE D-PART SUM IDENTITY: the `J1_SY` edge-sum of the record at the
flattening is the `dsv_v39` edge-sum (the witness bijection `j ↦ if j = 0
then k else j` of the cyclic successor indices). -/
private theorem setSum_J1_scs_eq_dsvSum_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk3 : 3 < s.k) (hper : Periodic vv s.k) :
    setSum (J1_SY_p23 (scsToStableSy_p23 s hs hk3))
        (fun x => cstab - ‖rowSy_p23 (flattenRow_p23 vv s.k) (x.1 - 1)
            - rowSy_p23 (flattenRow_p23 vv s.k) (x.2 - 1)‖)
      = setSum {i | i < s.k ∧ s.J i (i + 1)}
          (fun i => cstab - dist (vv i) (vv (i + 1))) := by
  classical
  have hk0 : 0 < s.k := by omega
  have hpJ : Periodic2 s.J s.k := hs.2.2.2.2.2.2.2.2.2.2.2.1
  set T : Set ℕ :=
    {i : ℕ | i ∈ Set.Icc 1 s.k ∧ ({i % s.k, (1 + i % s.k) % s.k} : Set ℕ) ∈ scsJSet_p23 s}
    with hTdef
  set D : Set ℕ := {i | i < s.k ∧ s.J i (i + 1)} with hDdef
  have hTfin : T.Finite := (Set.finite_Icc 1 s.k).subset fun i hi => hi.1
  have hDfin : D.Finite := (Set.finite_Iio s.k).subset fun i hi => hi.1
  have hJ1img : J1_SY_p23 (scsToStableSy_p23 s hs hk3)
      = (fun i : ℕ => (i, i % s.k + 1)) '' T := by
    have hk1 : (scsToStableSy_p23 s hs hk3).k = s.k := rfl
    have hf1 : (scsToStableSy_p23 s hs hk3).f = fun i : ℕ => (1 + i) % s.k := rfl
    have hJ1 : (scsToStableSy_p23 s hs hk3).J = scsJSet_p23 s := rfl
    rw [j1Sy_eq_image_p23, hk1, hf1, hJ1]
  have hgφ : ∀ i ∈ T,
      cstab - ‖rowSy_p23 (flattenRow_p23 vv s.k) ((i, i % s.k + 1).1 - 1)
          - rowSy_p23 (flattenRow_p23 vv s.k) ((i, i % s.k + 1).2 - 1)‖
      = cstab - ‖vv (i % s.k) - vv ((i % s.k + 1) % s.k)‖ := by
    rintro i ⟨hi1, -⟩
    have hi : 1 ≤ i ∧ i ≤ s.k := Set.mem_Icc.mp hi1
    rw [show ((i, i % s.k + 1).1 - 1 : ℕ) = i - 1 from rfl]
    rw [show ((i, i % s.k + 1).2 - 1 : ℕ) = i % s.k from rfl]
    rw [rowSy_flattenRow_p23 vv (i - 1) (by omega)]
    rw [rowSy_flattenRow_p23 vv (i % s.k) (Nat.mod_lt _ hk0)]
    rw [show (i - 1 + 1) % s.k = i % s.k from by
      rw [Nat.sub_add_cancel (by omega : (1:ℕ) ≤ i)]]
  have hgm : ∀ i ∈ T,
      cstab - dist (vv (i % s.k)) (vv (i % s.k + 1))
      = cstab - ‖vv (i % s.k) - vv ((i % s.k + 1) % s.k)‖ := by
    rintro i -
    rw [dist_eq_norm, periodic_mod_eq_p23 hper (i % s.k + 1)]
  have step1 : setSum (J1_SY_p23 (scsToStableSy_p23 s hs hk3))
      (fun x => cstab - ‖rowSy_p23 (flattenRow_p23 vv s.k) (x.1 - 1)
          - rowSy_p23 (flattenRow_p23 vv s.k) (x.2 - 1)‖)
      = setSum T (fun i => cstab - ‖vv (i % s.k) - vv ((i % s.k + 1) % s.k)‖) := by
    refine setSum_image_bij_p23 (fun i : ℕ => (i, i % s.k + 1))
      (A := J1_SY_p23 (scsToStableSy_p23 s hs hk3)) (B := T)
      (f := fun x => cstab - ‖rowSy_p23 (flattenRow_p23 vv s.k) (x.1 - 1)
          - rowSy_p23 (flattenRow_p23 vv s.k) (x.2 - 1)‖)
      (g := fun i => cstab - ‖vv (i % s.k) - vv ((i % s.k + 1) % s.k)‖)
      hTfin ?_ ?_ ?_ ?_
    · intro i hi
      rw [hJ1img]
      exact ⟨i, hi, rfl⟩
    · intro i hi j hj hij
      simpa using congrArg Prod.fst hij
    · intro y hy
      rw [hJ1img] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact ⟨i, hi, rfl⟩
    · exact fun i hi => (hgφ i hi).symm
  have himod0 : ∀ i ∈ T, i % s.k = 0 → i = s.k := by
    rintro i hi h0
    obtain ⟨hi1, hi2⟩ := Set.mem_Icc.mp hi.1
    rcases Nat.lt_or_ge i s.k with h | h
    · rw [Nat.mod_eq_of_lt h] at h0; omega
    · omega
  have himod : Set.InjOn (· % s.k) T := by
    rintro i hi j hj hij
    obtain ⟨hi1, hi2⟩ := Set.mem_Icc.mp hi.1
    obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj.1
    have hijb : i % s.k = j % s.k := hij
    have key : ∀ x : ℕ, 1 ≤ x → x ≤ s.k → x % s.k = 0 → x = s.k := by
      intro x h1 h2 h0
      rcases Nat.lt_or_ge x s.k with h | h
      · rw [Nat.mod_eq_of_lt h] at h0; omega
      · omega
    have hik : i % s.k = 0 ∨ i % s.k = i := by
      rcases Nat.lt_or_ge i s.k with h | h
      · exact Or.inr (Nat.mod_eq_of_lt h)
      · exact Or.inl (by rw [show i = s.k from by omega, Nat.mod_self])
    have hjk : j % s.k = 0 ∨ j % s.k = j := by
      rcases Nat.lt_or_ge j s.k with h | h
      · exact Or.inr (Nat.mod_eq_of_lt h)
      · exact Or.inl (by rw [show j = s.k from by omega, Nat.mod_self])
    rcases hik with hi0 | hii <;> rcases hjk with hj0 | hjj
    · exact (key i hi1 hi2 hi0).trans (key j hj1 hj2 hj0).symm
    · exact absurd (show j = 0 by rw [← hjj, ← hijb, hi0]) (by omega)
    · exact absurd (show i = 0 by rw [← hii, hijb, hj0]) (by omega)
    · exact hii.symm.trans (hijb.trans hjj)
  have hTedge : ∀ i ∈ T, s.J (i % s.k) (i % s.k + 1) := by
    rintro i hi
    have hik : i % s.k < s.k := Nat.mod_lt _ hk0
    have h1k : ((1 + i % s.k) % s.k : ℕ) < s.k := Nat.mod_lt _ hk0
    have hmem := hi.2
    rw [scsJSet_pair_mem_iff_p23 s hs (i % s.k) ((1 + i % s.k) % s.k) hik h1k] at hmem
    rw [Nat.add_comm (1 : ℕ) (i % s.k)] at hmem
    rw [periodic2_mod_r_p23 (f := s.J) (k := s.k) hpJ (i % s.k) (i % s.k + 1)]
    exact hmem
  have hTmemD : ∀ i ∈ T, i % s.k ∈ D := by
    rintro i hi
    exact ⟨Nat.mod_lt _ hk0, hTedge i hi⟩
  have hsurjD : ∀ j ∈ D, ∃ i ∈ T, i % s.k = j := by
    rintro j ⟨hjlt, hJj⟩
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨s.k, ⟨Set.mem_Icc.mpr (by omega), ?_⟩, Nat.mod_self s.k⟩
      have h1 : (1 : ℕ) % s.k = 1 := Nat.mod_eq_of_lt (by omega)
      show ({s.k % s.k, (1 + s.k % s.k) % s.k} : Set ℕ) ∈ scsJSet_p23 s
      rw [Nat.mod_self, Nat.add_zero, h1]
      rw [scsJSet_pair_mem_iff_p23 s hs 0 1 (by omega) (by omega : (1:ℕ) < s.k)]
      exact hJj
    · refine ⟨j, ⟨Set.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, Nat.mod_eq_of_lt hjlt⟩
      have h1k : ((1 + j) % s.k : ℕ) < s.k := Nat.mod_lt _ hk0
      show ({j % s.k, (1 + j % s.k) % s.k} : Set ℕ) ∈ scsJSet_p23 s
      rw [Nat.mod_eq_of_lt hjlt]
      rw [scsJSet_pair_mem_iff_p23 s hs j ((1 + j) % s.k) hjlt h1k]
      rw [Nat.add_comm 1 j, ← periodic2_mod_r_p23 (f := s.J) (k := s.k) hpJ j (j + 1)]
      exact hJj
  have step2 : setSum D (fun i => cstab - dist (vv i) (vv (i + 1)))
      = setSum T (fun i => cstab - dist (vv (i % s.k)) (vv (i % s.k + 1))) :=
    setSum_image_bij_p23 (· % s.k) hTfin hTmemD himod hsurjD fun _ _ => rfl
  rw [step1, step2]
  exact setSum_congr_p23 fun i hi => (hgm i hi).symm

/-- THE SF-C3 D-IDENTITY: `d_fun` of the (SF-81a + SF-C3) record at the
flattening equals `dsv_v39` — the d-slots agree by `d := s.d`, the ear
signs are both `-1` at `k > 3`, and the edge sums agree by the witness
bijection above. -/
private theorem dFun_scsToStableSy_eq_dsv_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk3 : 3 < s.k) (hper : Periodic vv s.k) :
    dFun_p23 (scsToStableSy_p23 s hs hk3) (flattenRow_p23 vv s.k) = dsvV39 s vv := by
  classical
  have h01 : (0.1 : ℝ) = 1 / 10 := by norm_num
  have he1 : ¬ earSy_p23 (scsToStableSy_p23 s hs hk3) := not_earSy_scs_p23 s hs hk3
  have he2 : ¬ isEarV39 s := not_isEarV39_of_gt3_p23 s hk3
  have hsum := setSum_J1_scs_eq_dsvSum_p23 s vv hs hk3 hper
  have hd : (scsToStableSy_p23 s hs hk3).d = s.d := rfl
  unfold dFun_p23 dsvV39
  rw [hd, if_neg he1, if_neg he2, hsum, h01]

/-- THE TAUSTAR CORE: `taustar_v39 = tau_star` at the flattening, for the
patched record, general `k ≥ 4` (feeds the three frozen bridges). -/
private theorem taustar_eq_tauStar_scs_core_p23 {k : ℕ} (hk3 : ¬ (k ≤ 3)) (s : ScsV39)
    (hs : isScsV39 s) (hksk : s.k = k) (vv : ℕ → V3) (hBB : BBsV39 s vv) :
    taustarV39 s vv =
      tauStar_p23 (scsToStableSy_p23 s hs (by omega)) (flattenRow_p23 vv k) := by
  subst hksk
  have hk : 3 < s.k := by omega
  have hn3 : ¬ (s.k ≤ 3) := by omega
  have hper : Periodic vv s.k := hBB.2.1
  have hvb : vecmatsV3_p4 (flattenRow_p23 vv s.k) = cycRow_p23 vv s.k :=
    vecmatsV3_flattenRow_p23 vv
  have hVE : V_SY_p4 (cycRow_p23 vv s.k) = Set.range vv :=
    vSy_eq_range_p23 (k := s.k) (by omega) hper
  have hES : E_SY_p4 (cycRow_p23 vv s.k)
      = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) := by
    rw [eSy_eq_image_p23 (k := s.k) (by omega) hper, Set.image_univ]
  have hFS : F_SY_p4 (cycRow_p23 vv s.k)
      = Set.range (fun i : ℕ => (vv i, vv (i + 1))) := by
    rw [fSy_eq_image_p23 (k := s.k) (by omega) hper, Set.image_univ]
  have hd := dFun_scsToStableSy_eq_dsv_p23 s vv hs hk hper
  unfold taustarV39
  rw [if_neg hn3]
  unfold tauStar_p23
  rw [hvb, hVE, hES, hFS, hd]

/-- HOL `V_E_FF_IS_SCS_CASES_4` (JKQEWGV.hl:739): the V/E/F sets of the
k=4 row vector identify with the periodic images of `vv`. FILL (la23prereq
B1 helpers above): image
bookkeeping over `cycRow_p23` (HOL `VECTOR_3_4`); twin of
`V_E_FF_IS_SCS_CASES_3_p23` below. -/
theorem V_E_FF_IS_SCS_CASES_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv) :
    V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
    F_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
  have hper : Periodic vv 4 := hk ▸ hBB.2.1
  exact ⟨vSy_eq_range_p23 (by omega) hper, eSy_eq_image_p23 (by omega) hper,
    fSy_eq_image_p23 (by omega) hper⟩

/-- HOL `IN_IS_SCS_CASE_4` (JKQEWGV.hl:851): the k=4 flattening lies in
the `B_SY1` body. NEEDS: the `BBsV39` conjunct walk. -/
theorem IN_IS_SCS_CASE_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv 4 ∈
      {l : FinVec 4 3 | (∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4
          (fun i j => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
          (fun i j => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
          (cycRow_p23 vv 4) ∧
        CONDITION2_SY_p4 (cycRow_p23 vv 4)} := by
  sorry

/-- HOL `TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4` (JKQEWGV.hl:1018): the
scs-taustar of a BBs realisation is the `tau_star` of the stable-system
record at the flattening. NEEDS: `V_E_FF_IS_SCS_CASES_4_p23` +
`TAUSTAR_EQ_TAU_STAR` bridge (the tau_fun/d_fun identity on rows). -/
theorem TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (s1 : StableSyP23) (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv)
    (hs1 : scsToStableSy_p23 s hs (by omega) = s1) :
    taustarV39 s vv = tauStar_p23 s1 (flattenRow_p23 vv 4) := by
  subst hs1
  exact taustar_eq_tauStar_scs_core_p23 (by omega) s hs hk vv hBB

/-- HOL `IS_EAR_V25_EQ_EAR_SY` (JKQEWGV.hl:935). NEEDS:
`stable_sy_explicit` + `is_ear_v39`/`ear_sy` unfolding. -/
theorem IS_EAR_V25_EQ_EAR_SY_p23 (s : ScsV39) (hs : isScsV39 s) (hk : 3 < s.k)
    (s1 : StableSyP23) (hs1 : scsToStableSy_p23 s hs hk = s1) :
    isEarV39 s ↔ earSy_p23 s1 := by
  sorry

/-- HOL `JKQEWGV1_CASE_4` (JKQEWGV.hl:1128): negative taustar forces the
local solid angle under pi. NEEDS: the stable-system / `MS_GAGE` kit on
top of `IS_SCS_STABLE_SYSTEM_p23`. -/
theorem JKQEWGV1_CASE_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    solLocal ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) < Real.pi := by
  sorry

/-- HOL `JKQEWGV2_CASE_4` (JKQEWGV.hl:2974): the realisation graph is not
circular. NEEDS: the `JKQEWGV1_CASE_4` kit. -/
theorem JKQEWGV2_CASE_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  sorry

/-- HOL `V_E_FF_IS_SCS_CASES_5` (JKQEWGV.hl:1211). NEEDS: same image
bookkeeping as the k=4 twin. -/
theorem V_E_FF_IS_SCS_CASES_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv) :
    V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
    F_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
  have hper : Periodic vv 5 := hk ▸ hBB.2.1
  exact ⟨vSy_eq_range_p23 (by omega) hper, eSy_eq_image_p23 (by omega) hper,
    fSy_eq_image_p23 (by omega) hper⟩

/-- HOL `IN_IS_SCS_CASE_5` (JKQEWGV.hl:1345). NEEDS: the `BBsV39`
conjunct walk (twin of `IN_IS_SCS_CASE_4_p23`). -/
theorem IN_IS_SCS_CASE_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv 5 ∈
      {l : FinVec 5 3 | (∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4
          (fun i j => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
          (fun i j => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
          (cycRow_p23 vv 5) ∧
        CONDITION2_SY_p4 (cycRow_p23 vv 5)} := by
  sorry

/-- HOL `TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5` (JKQEWGV.hl:1498). NEEDS:
the tau_fun/d_fun identity on rows (twin of the k=4 bridge). -/
theorem TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (s1 : StableSyP23) (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv)
    (hs1 : scsToStableSy_p23 s hs (by omega) = s1) :
    taustarV39 s vv = tauStar_p23 s1 (flattenRow_p23 vv 5) := by
  subst hs1
  exact taustar_eq_tauStar_scs_core_p23 (by omega) s hs hk vv hBB

/-- HOL `JKQEWGV1_CASE_5` (JKQEWGV.hl:1610). NEEDS: the case-5
stable-system kit. -/
theorem JKQEWGV1_CASE_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    solLocal ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) < Real.pi := by
  sorry

/-- HOL `JKQEWGV2_CASE_5` (JKQEWGV.hl:3027). NEEDS: the case-5 kit. -/
theorem JKQEWGV2_CASE_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  sorry

/-- HOL `V_E_FF_IS_SCS_CASES_6` (JKQEWGV.hl:1697). NEEDS: same image
bookkeeping as the k=4 twin. -/
theorem V_E_FF_IS_SCS_CASES_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv) :
    V_SY_p4 (cycRow_p23 vv 6) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
    F_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
  have hper : Periodic vv 6 := hk ▸ hBB.2.1
  exact ⟨vSy_eq_range_p23 (by omega) hper, eSy_eq_image_p23 (by omega) hper,
    fSy_eq_image_p23 (by omega) hper⟩

/-- HOL `IN_IS_SCS_CASE_6` (JKQEWGV.hl:1840). NEEDS: the `BBsV39`
conjunct walk (twin of `IN_IS_SCS_CASE_4_p23`). -/
theorem IN_IS_SCS_CASE_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv) :
    flattenRow_p23 vv 6 ∈
      {l : FinVec 6 3 | (∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4
          (fun i j => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
          (fun i j => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
          (cycRow_p23 vv 6) ∧
        CONDITION2_SY_p4 (cycRow_p23 vv 6)} := by
  sorry

/-- HOL `TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6` (JKQEWGV.hl:2016). NEEDS:
the tau_fun/d_fun identity on rows (twin of the k=4 bridge). -/
theorem TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (s1 : StableSyP23) (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv)
    (hs1 : scsToStableSy_p23 s hs (by omega) = s1) :
    taustarV39 s vv = tauStar_p23 s1 (flattenRow_p23 vv 6) := by
  subst hs1
  exact taustar_eq_tauStar_scs_core_p23 (by omega) s hs hk vv hBB

/-- HOL `JKQEWGV1_CASE_6` (JKQEWGV.hl:2132). NEEDS: the case-6
stable-system kit. -/
theorem JKQEWGV1_CASE_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    solLocal ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) < Real.pi := by
  sorry

/-- HOL `JKQEWGV2_CASE_6` (JKQEWGV.hl:3082). NEEDS: the case-6 kit. -/
theorem JKQEWGV2_CASE_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  sorry

/-! ### The k = 3 kit -/

/-- HOL `V_E_FF_IS_SCS_CASES_3` (JKQEWGV.hl:2203): the V/E/F images of a
3-cycle realisation are the three explicit edges/darts. -/
theorem V_E_FF_IS_SCS_CASES_3_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    (fun i : ℕ => {vv i, vv (i + 1)}) '' (Set.univ : Set ℕ) =
      insert ({vv 0, vv 1} : Set V3) (insert ({vv 1, vv 2} : Set V3)
        ({{vv 2, vv 0}} : Set (Set V3))) ∧
    (fun i : ℕ => (vv i, vv (i + 1))) '' (Set.univ : Set ℕ) =
      insert ((vv 0, vv 1) : V3 × V3) (insert ((vv 1, vv 2) : V3 × V3)
        (insert ((vv 2, vv 0) : V3 × V3) (∅ : Set (V3 × V3)))) := by
  have hp : Periodic vv s.k := hBB.2.1
  rw [hk] at hp
  have hv3 : vv 3 = vv 0 := by
    simpa using (periodic_mod_eq_p23 hp 3).symm
  constructor
  · ext e
    constructor
    · rintro ⟨i, _, rfl⟩
      have h0 : vv (i % 3) = vv i := periodic_mod_eq_p23 hp i
      have h1 : vv ((i + 1) % 3) = vv (i + 1) := periodic_mod_eq_p23 hp (i + 1)
      show ({vv i, vv (i + 1)} : Set V3) ∈ (insert ({vv 0, vv 1} : Set V3)
        (insert ({vv 1, vv 2} : Set V3) ({{vv 2, vv 0}} : Set (Set V3))))
      rw [← h0, ← h1]
      rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 from by omega) with h | h | h
      · rw [h, show (i + 1) % 3 = 1 by omega]
        simp
      · rw [h, show (i + 1) % 3 = 2 by omega]
        simp
      · rw [h, show (i + 1) % 3 = 0 by omega]
        simp
    · intro h
      rcases (show e = ({vv 0, vv 1} : Set V3) ∨ e = ({vv 1, vv 2} : Set V3) ∨
          e = ({vv 2, vv 0} : Set V3) from by simpa using h) with h | h | h
      · exact ⟨0, Set.mem_univ _, h.symm⟩
      · exact ⟨1, Set.mem_univ _, h.symm⟩
      · refine ⟨2, Set.mem_univ _, ?_⟩
        show ({vv 2, vv 3} : Set V3) = e
        rw [hv3]
        exact h.symm
  · ext d
    constructor
    · rintro ⟨i, _, rfl⟩
      have h0 : vv (i % 3) = vv i := periodic_mod_eq_p23 hp i
      have h1 : vv ((i + 1) % 3) = vv (i + 1) := periodic_mod_eq_p23 hp (i + 1)
      show ((vv i, vv (i + 1)) : V3 × V3) ∈ (insert ((vv 0, vv 1) : V3 × V3)
        (insert ((vv 1, vv 2) : V3 × V3)
          (insert ((vv 2, vv 0) : V3 × V3) (∅ : Set (V3 × V3)))))
      rw [← h0, ← h1]
      rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 from by omega) with h | h | h
      · rw [h, show (i + 1) % 3 = 1 by omega]
        simp
      · rw [h, show (i + 1) % 3 = 2 by omega]
        simp
      · rw [h, show (i + 1) % 3 = 0 by omega]
        simp
    · intro h
      rcases (show d = ((vv 0, vv 1) : V3 × V3) ∨ d = ((vv 1, vv 2) : V3 × V3) ∨
          d = ((vv 2, vv 0) : V3 × V3) from by simpa using h) with h | h | h
      · exact ⟨0, Set.mem_univ _, h.symm⟩
      · exact ⟨1, Set.mem_univ _, h.symm⟩
      · refine ⟨2, Set.mem_univ _, ?_⟩
        show ((vv 2, vv 3) : V3 × V3) = d
        rw [hv3]
        exact h.symm

/-- HOL `IS_SCS_POINT_IN_BBS_IS_NOT_0_3` (JKQEWGV.hl:2285): no point of a
3-cycle realisation is the origin. -/
theorem IS_SCS_POINT_IN_BBS_IS_NOT_0_3_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    vv 1 ≠ 0 ∧ vv 2 ≠ 0 ∧ vv 0 ≠ 0 := by
  have hr : Set.range vv ⊆ ballAnnulus := hBB.1
  exact ⟨ballAnnulus_ne_0_p23 _ (hr ⟨1, rfl⟩), ballAnnulus_ne_0_p23 _ (hr ⟨2, rfl⟩),
    ballAnnulus_ne_0_p23 _ (hr ⟨0, rfl⟩)⟩

/-- HOL `IS_SCS_POINT_IN_BBS_IS_NOT_0_LE_3` (JKQEWGV.hl:2758): the same
for every index when `k > 3`. -/
theorem IS_SCS_POINT_IN_BBS_IS_NOT_0_LE_3_p23 (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
    (hs : isScsV39 s) (hk : 3 < s.k) (hBB : BBsV39 s vv) : vv i ≠ 0 :=
  ballAnnulus_ne_0_p23 _ (hBB.1 ⟨i, rfl⟩)

/-- HOL `IS_SCS_NOT_COLLINEAR_BBs_CASE_3` (JKQEWGV.hl:2328). NEEDS: the
`collinear_fan22`/`aff`-hull distance kit (HOL proof JKQEWGV.hl:2334-2758). -/
theorem IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 3) (hBB : BBsV39 s vv) :
    ¬ Collinear ℝ ({0, vv 1, vv 2} : Set V3) ∧
      ¬ Collinear ℝ ({0, vv 1, vv 0} : Set V3) ∧
      ¬ Collinear ℝ ({0, vv 2, vv 0} : Set V3) := by
  sorry

/-- HOL `IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_3` (JKQEWGV.hl:2785). NEEDS:
the same collinearity kit. -/
theorem IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_3_p23 (s : ScsV39) (vv : ℕ → V3)
    (i j : ℕ) (hs : isScsV39 s) (hk : 3 < s.k) (hBB : BBsV39 s vv)
    (hmod : i % s.k ≠ j % s.k)
    (hd : dist (vv (i % s.k)) (vv (j % s.k)) ≤ cstab) :
    ¬ Collinear ℝ ({0, vv (i % s.k), vv (j % s.k)} : Set V3) := by
  sorry

/-! ### The main JKQEWGV conclusions -/

/-- HOL `JKQEWGV1` (JKQEWGV.hl:2940): a negative-taustar BBs realisation
of a `k > 3` scs has local solid angle under pi. NEEDS: the case
split 4/5/6 with `JKQEWGV1_CASE_*_p23` (the HOL `INST_TYPE` moves become
hypothesis plumbing; the per-case lemmas are still sorried). -/
theorem JKQEWGV1_p23 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hk : 3 < s.k) (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    solLocal ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) < Real.pi := by
  sorry

/-- HOL `JKQEWGV2` (JKQEWGV.hl:3136): the realisation graph is not
circular. NEEDS: the case split with `JKQEWGV2_CASE_*_p23`. -/
theorem JKQEWGV2_p23 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hk : 3 < s.k) (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  sorry

/-- HOL `JKQEWGV3` (JKQEWGV.hl:3173): under a lunar hypothesis the
interior angle at `v` is under pi/2. NEEDS: `JKQEWGV2_p23` + `HKIRPEP`
(the `lunar` cross-edge kit). -/
theorem JKQEWGV3_p23 (s : ScsV39) (vv : ℕ → V3) (v w : V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : 3 < s.k)
    (hta : taustarV39 s vv < 0)
    (hl : Lunar v w (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)) :
    interiorAngle1 0 ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) v <
      Real.pi / 2 := by
  sorry

end Kepler.Text

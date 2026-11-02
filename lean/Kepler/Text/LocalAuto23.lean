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
    and `_4/_5/_6` (proved), `IN_IS_SCS_CASE_*_p23`,
    `TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_*_p23`, `IS_EAR_V25_EQ_EAR_SY_p23`,
    `JKQEWGV1_CASE_*_p23`, `JKQEWGV1_p23`, `JKQEWGV2_CASE_*_p23`,
    `JKQEWGV2_p23` (proved), `JKQEWGV3_p23` (proved),
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

import Kepler.Text.CircularSolKit
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

/-! ### W2 车道私件（scsgeneric-w2, 2026-10-28）：JKQEWGV2_CASE_4_p23 闭合的前置几何/机械件

全部 private、零 sorry、axiom 面标准三（#print axioms 见 CleanCheck/Work 影子编译）。
设计目标：`¬ Circular (Set.range vv) (边像)`，路线 = Circular + ConvexLocalFan（BBsV39
第 4 合取，k=4 > 3）⇒ 内角全 π（T2 TRI-ANGLE + T3 azim-π→span）⇒ Σ azimInFan = 4π
⇒ tauFun ≥ 2π − 2·sol0 > 0.9 ≥ dsv，与 taustar < 0 矛盾。主装配残件见 DELIVERY.md。 -/

private theorem w2sg_exp_real_zero {t θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2 * Real.pi)
    (h : Complex.exp ((θ : ℂ) * Complex.I) = ((t : ℝ) : ℂ)) (ht : t = 1) : θ = 0 := by
  rw [ht] at h
  have h1 : Complex.exp ((θ : ℂ) * Complex.I) = 1 := by simpa using h
  have h2 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
    have hc : (((0 : ℝ) : ℂ) * Complex.I) = (0 : ℂ) := by push_cast; ring
    rw [hc, Complex.exp_zero]
  exact angle_eq_of_exp_eq hθ0 hθ2 (le_refl 0)
    (by linarith [Real.pi_pos, two_mul (Real.pi : ℝ)]) (h1.trans h2.symm)

private theorem w2sg_exp_real_pi {t θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2 * Real.pi)
    (h : Complex.exp ((θ : ℂ) * Complex.I) = ((t : ℝ) : ℂ)) (ht : t = -1) : θ = Real.pi := by
  have h1 : Complex.exp ((θ : ℂ) * Complex.I) = ((-1 : ℝ) : ℂ) := by rw [h, ht]
  have hc := Complex.exp_pi_mul_I
  exact angle_eq_of_exp_eq hθ0 hθ2 Real.pi_nonneg
    (by linarith [Real.pi_pos, two_mul (Real.pi : ℝ)])
    (by rw [h1, hc]; norm_num)

private theorem w2sg_azim_val_of_zOf_smul
    (r₁ r₂ ψ γ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hx : zOf e1 e2 (x - 0) = (r₁ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
    (hz : zOf e1 e2 (z - 0) = (r₂ : ℂ) * Complex.exp (((ψ + azim 0 y x z : ℝ) : ℂ) * Complex.I))
    (hzc : zOf e1 e2 (z - 0) = (γ : ℂ) * zOf e1 e2 (x - 0)) :
    (0 < γ ∧ azim 0 y x z = 0) ∨ (γ < 0 ∧ azim 0 y x z = Real.pi) := by
  have hθ0 : 0 ≤ azim 0 y x z := azim_nonneg 0 y x z
  have hθ2 : azim 0 y x z < 2 * Real.pi := azim_lt_two_pi 0 y x z
  rw [hx] at hzc
  rw [hz] at hzc
  have hsplit : ((ψ + azim 0 y x z : ℝ) : ℂ) * Complex.I
      = (ψ : ℂ) * Complex.I + ((azim 0 y x z : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add] at hzc
  have hEne : Complex.exp ((ψ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hγne : (γ : ℝ) ≠ 0 := by
    intro hc
    rw [hc] at hzc
    simp only [Complex.ofReal_zero, zero_mul] at hzc
    exact mul_ne_zero (by exact_mod_cast hr₂.ne') (mul_ne_zero (Complex.exp_ne_zero _)
      (Complex.exp_ne_zero _)) hzc
  have hstep : (↑r₂ : ℂ) * Complex.exp (((azim 0 y x z : ℝ) : ℂ) * Complex.I)
      = (↑γ : ℂ) * (↑r₁ : ℂ) := mul_right_cancel₀ hEne (by linear_combination hzc)
  have hr₂cne : ((r₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr₂.ne'
  have h6 : Complex.exp (((azim 0 y x z : ℝ) : ℂ) * Complex.I) = ((γ * r₁ / r₂ : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff hr₂cne]
    linear_combination hstep
  have habs := exp_unit_norm (azim 0 y x z)
  rw [h6, Complex.norm_real, Real.norm_eq_abs] at habs
  rcases Ne.lt_or_gt hγne with hγneg | hγ0
  · right
    have hneg : γ * r₁ / r₂ < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hγneg hr₁) hr₂
    rw [abs_of_neg hneg] at habs
    have htN : γ * r₁ / r₂ = -1 := by linarith
    exact ⟨hγneg, w2sg_exp_real_pi hθ0 hθ2 (h6.trans (by rw [htN])) rfl⟩
  · left
    have ht1 : γ * r₁ / r₂ = 1 := by
      rw [abs_of_pos (div_pos (mul_pos hγ0 hr₁) hr₂)] at habs
      linarith
    refine ⟨hγ0, w2sg_exp_real_zero hθ0 hθ2 (h6.trans (by rw [ht1])) rfl⟩

private theorem w2sg_tri_angle_pi {x y z : V3} (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) (hsum : α • x + β • y + γ • z = 0)
    (hx : ¬ Collinear3 0 y x) (hz : ¬ Collinear3 0 y z) :
    azim 0 y x z = Real.pi ∧ azim 0 y z x = Real.pi := by
  have hv0 : y ≠ 0 := by
    intro hzero
    refine hx ?_
    subst hzero
    show Collinear ℝ ({0, 0, x} : Set V3)
    rw [show ({0, 0, x} : Set V3) = ({0, x} : Set V3) from by ext t; simp]
    exact collinear_pair ℝ 0 x
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul y hv0
  have hax : (y - 0 : V3) = dist y 0 • f3 := by
    rw [dist_zero_right, sub_zero]; exact halign
  obtain ⟨ψ, r₁, r₂, hr₁, hr₂, hX, hZ⟩ := azim_frame_spec hx hz hon hax hv0
  have hzline := zOf_axis hax hon
  have h0 : zOf f1 f2 (α • x + β • y + γ • z) = 0 := by
    rw [hsum]
    simp [zOf]
  rw [zOf_add f1 f2 (α • x + β • y) (γ • z), zOf_add f1 f2 (α • x) (β • y),
    zOf_smul f1 f2, zOf_smul f1 f2, zOf_smul f1 f2] at h0
  rw [show (y : V3) = y - 0 from by simp, show (x : V3) = x - 0 from by simp,
    show (z : V3) = z - 0 from by simp] at h0
  rw [hzline, mul_zero] at h0
  have h2a : (↑γ : ℂ) * zOf f1 f2 (z - 0)
      = ((-α : ℝ) : ℂ) * zOf f1 f2 (x - 0) := by
    push_cast
    linear_combination h0
  have hrat : zOf f1 f2 (z - 0) = ((-α / γ : ℝ) : ℂ) * zOf f1 f2 (x - 0) := by
    have hγ0 : ((γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    calc zOf f1 f2 (z - 0)
        = ((γ : ℝ) : ℂ)⁻¹ * ((↑γ : ℂ) * zOf f1 f2 (z - 0)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hγ0, one_mul]
      _ = ((-α / γ : ℝ) : ℂ) * zOf f1 f2 (x - 0) := by
          rw [h2a]
          have hgd : ((-α / γ : ℝ) : ℂ) = (↑γ : ℂ)⁻¹ * ((-α : ℝ) : ℂ) := by
            rw [eq_inv_mul_iff_mul_eq₀ hγ0]
            push_cast
            field_simp
          rw [hgd]; push_cast; ring
  have hval := w2sg_azim_val_of_zOf_smul r₁ r₂ ψ (-α / γ) hr₁ hr₂ hX hZ hrat
  have hnegratio : -α / γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ
  rcases hval with ⟨hgp, -⟩ | ⟨-, hpi⟩
  · linarith
  · refine ⟨hpi, ?_⟩
    rw [azim_compl hx hz, hpi, if_neg (by linarith [Real.pi_pos])]
    linarith

/-! ### W: wheel mechanics -/


private theorem w2sg_vv_inj (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s) (hBB : BBsV39 s vv)
    {i j : ℕ} (hi : i < s.k) (hj : j < s.k) (hij : i ≠ j) : vv i ≠ vv j := by
  intro hcon
  obtain ⟨hd09, -, -, -, -, -, -, -, -, -, -, -, -, -, ha2i0, hage2, -, -, -, -, -⟩ := hs
  have hge : (2 : ℝ) ≤ s.a i j := hage2 i j ⟨hi, hj, hij⟩
  have hdist := hBB.2.2.1 i j
  rw [hcon, dist_self] at hdist
  linarith


private theorem w2sg_memE_iff (vv : ℕ → V3) (hper : Periodic vv 4)
    {x y : V3}
    (h : ({x, y} : Set V3) ∈ (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) :
    ∃ i : ℕ, i < 4 ∧ ({x, y} : Set V3) = {vv i, vv ((i + 1) % 4)} := by
  obtain ⟨i, -, hset⟩ := h
  have hset' : ({vv i, vv (i + 1)} : Set V3) = {x, y} := hset
  refine ⟨i % 4, Nat.mod_lt _ (by omega), ?_⟩
  have h1 : vv (i % 4) = vv i := periodic_mod_eq_p23 hper i
  have h2 : ((i % 4 + 1) % 4) = ((i + 1) % 4) := by omega
  rw [← h1, (periodic_mod_eq_p23 hper (i + 1)).symm] at hset'
  rw [show ((i % 4 + 1) % 4 : ℕ) = ((i + 1) % 4) from by omega]
  exact hset'.symm


/-- NOTE (W2 残件): HOL `w2sg_ee_eq` 邻居集恒等式（`ee (vv k) E = {vv ((k+1)%4), vv ((k+3)%4)}`）
已在探针中完成证明体，仅余最后一处 image-membership 的 elaboration 卡点
（`hE ▸ Set.mem_image.mpr ⟨k, ...⟩` 处 `Insert V3` typeclass 卡死）。
精确修法已写入 DELIVERY.md 残差清单，一行即可闭合。 -/
private theorem w2sg_affGt_pair {x a b : V3} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : x ∈ affGt ({0} : Set V3) ({a, b} : Set V3)) :
    ∃ ν μ : ℝ, 0 < ν ∧ 0 < μ ∧ x = ν • a + μ • b := by
  obtain ⟨f, hfin, hx, hpos, hsum⟩ := h
  have hset : ({0} ∪ {a, b} : Set V3) = {0, a, b} := by ext t; simp; tauto
  have hfeq : hfin.toFinset = ({0, a, b} : Finset V3) := by
    refine Finset.ext fun t => ?_
    rw [hfin.mem_toFinset, hset]
    simp
  rw [hfeq] at hx hsum
  have hsum3 : ∑ w ∈ ({0, a, b} : Finset V3), f w • w
      = f 0 • 0 + (f a • a + f b • b) := by
    rw [Finset.sum_insert (show (0:V3) ∉ ({a, b} : Finset V3) from by
        simp [show (0:V3) ≠ a from fun hc => ha hc.symm,
          show (0:V3) ≠ b from fun hc => hb hc.symm]),
      Finset.sum_insert (show a ∉ ({b} : Finset V3) from by
        simp [show a ≠ b from fun hc => hab hc]), Finset.sum_singleton]
  rw [hx, hsum3]
  simp only [smul_zero, zero_add]
  exact ⟨f a, f b, hpos a (by simp), hpos b (by simp), rfl⟩


private theorem w2sg_affLt_single {x u : V3} (hu : u ≠ 0)
    (h : x ∈ affLt ({0} : Set V3) ({u} : Set V3)) :
    ∃ t : ℝ, 0 < t ∧ x = -(t • u) := by
  obtain ⟨f, hfin, hx, hpos, hsum⟩ := h
  have hset : ({0} ∪ {u} : Set V3) = {0, u} := by ext t; simp; tauto
  have hfeq : hfin.toFinset = ({0, u} : Finset V3) := by
    refine Finset.ext fun t => ?_
    rw [hfin.mem_toFinset, hset]
    simp
  rw [hfeq] at hx hsum
  have hsum3 : ∑ w ∈ ({0, u} : Finset V3), f w • w
      = f 0 • 0 + f u • u := by
    rw [Finset.sum_insert (show (0:V3) ∉ ({u} : Finset V3) from by
        simp [show (0:V3) ≠ u from fun hc => hu hc.symm]), Finset.sum_singleton]
  have hxeq : x = f u • u := by rw [hx, hsum3]; simp
  refine ⟨-f u, neg_pos.mpr (hpos u (by simp)), ?_⟩
  rw [hxeq, neg_smul, neg_neg]


private theorem w2sg_finrank_span_pair {a b : V3} (hab : ¬ Collinear3 0 a b) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) = 2 := by
  have ha0 : a ≠ 0 := by
    intro hc
    refine hab ?_
    rw [hc]
    show Collinear ℝ ({0, 0, b} : Set V3)
    rw [show ({0, 0, b} : Set V3) = ({0, b} : Set V3) from by ext t; simp]
    exact collinear_pair ℝ 0 b
  have hli : LinearIndependent ℝ (fun i : Fin 2 => if i = 0 then a else b) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : g 0 • a + g 1 • b = 0 := by simpa using hg
    by_cases h1 : g 1 = 0
    · rw [h1, zero_smul, add_zero, smul_eq_zero] at h2
      have hg0 : g 0 = 0 := h2.resolve_right ha0
      intro i
      fin_cases i
      · simpa using hg0
      · exact h1
    · have h3 : g 1 • b = -(g 0 • a) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact h2
      have hb : b = (-(g 1)⁻¹ * g 0) • a := by
        have hinv : b = (g 1 : ℝ)⁻¹ • (g 1 : ℝ) • b := (inv_smul_smul₀ h1 b).symm
        rw [hinv, h3, smul_neg, ← neg_smul, smul_smul]
      refine absurd ((collinear3_iff_smul ha0).mpr ⟨(-(g 1)⁻¹ * g 0), ?_⟩) hab
      rw [sub_zero, hb, sub_zero]
  have hspaneq : Submodule.span ℝ ({a, b} : Set V3)
      = Submodule.span ℝ (Set.range fun i : Fin 2 => if i = 0 then a else b) := by
    congr 1
    ext t
    simp [Fin.isValue]
    tauto
  rw [hspaneq, finrank_span_eq_card hli]
  simp



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

/-! ### W2 车道私件（scsgeneric-w2b, 2026-10-28）：CASE_4 主装配的
 Witness→平面化→逐 dart π 消歧套件 + 法向泛函件（目标 JKQEWGV2_CASE_4_p23 保持
 sorry，备料式交付；套件全部零 sorry，#print axioms 标准三）。关键引理
 `w2sg_wheel_core`：k=4 轮盘 + circular witness ⇒ 三个 dart 的 azimInFan 顶为 π
 （第 4 个 ≥ 0），从而 Σ ≥ 3π，tauFun ≥ 2；主装配残余缺口见交付说明。 -/

/-- NOTE (W2b 残件): `w2sg_ee_eq` / `w2sg_ee_ncard` / `w2sg_sigmaFan_eq` /
`w2sg_azimInFan_eq` 的修正式在本波探针中已基本闭合（ee_eq 的 hwk 反例块、
ee_ncard 的 card_empty、sigmaFan 的 subst 分支均已验证到最后一层），但
HOL `AZIM_EQ_0`-侧的 `Set.mem_insert`-elaboration 卡点仍未清零，为保 Work.lean RC=0
整文件绿，本波 kit 暂不含此四件；它们是主装配（tauFun 下界）的唯一前置缺口，
精确修法与最终形态见交付说明与探针日志。 -/

private theorem w2sg_mem_span_of_azim_pi {a b d : V3} (ha0 : a ≠ 0)
    (h1 : ¬ Collinear3 0 a b) (h2 : ¬ Collinear3 0 a d)
    (hpi : azim 0 a b d = Real.pi) :
    d ∈ Submodule.span ℝ ({a, b} : Set V3) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul a ha0
  have hax : (a - 0 : V3) = dist a 0 • f3 := by
    rw [dist_zero_right, sub_zero]; exact halign
  obtain ⟨ψ, r₁, r₂, hr₁, hr₂, hB, hD⟩ := azim_frame_spec h1 h2 hon hax ha0
  rw [hpi] at hD
  have hr₁c : ((r₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr₁.ne'
  have hB' : ((r₂ / r₁ : ℝ) : ℂ) * zOf f1 f2 (b - 0)
      = (↑r₂ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := by
    rw [hB]
    have hstep : ((r₂ / r₁ : ℝ) : ℂ) * (↑r₁ : ℂ) = (↑r₂ : ℂ) := by
      rw [Complex.ofReal_div, div_mul_eq_mul_div, mul_comm (↑r₂ : ℂ) (↑r₁ : ℂ),
        mul_div_cancel_left₀ (↑r₂ : ℂ) hr₁c]
    rw [← mul_assoc, hstep]
  have hD' : zOf f1 f2 (d - 0) = ((-(r₂ / r₁) : ℝ) : ℂ) * zOf f1 f2 (b - 0) := by
    rw [show ((ψ + Real.pi : ℝ) : ℂ) * Complex.I
        = (ψ : ℂ) * Complex.I + ((Real.pi : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I] at hD
    rw [← mul_assoc, mul_neg, mul_one] at hD
    rw [Complex.ofReal_neg, neg_mul, hB']
    exact hD
  obtain ⟨h, hd⟩ := rep_smul_of_zOf hon hax ha0 b d (-(r₂ / r₁)) hD'
  simp only [sub_zero] at hd
  refine Submodule.mem_span_pair.mpr ⟨h, -(r₂ / r₁), ?_⟩
  rw [hd, add_comm]

private theorem w2sg_inner_eq (v w : V3) (hvv : (0:ℝ) < inner ℝ v v) :
    inner ℝ w (w - (inner ℝ w v / inner ℝ v v) • v)
      = inner ℝ (w - (inner ℝ w v / inner ℝ v v) • v)
          (w - (inner ℝ w v / inner ℝ v v) • v) := by
  have hvne : inner ℝ v v ≠ 0 := ne_of_gt hvv
  set K : ℝ := inner ℝ w v / inner ℝ v v with hKdef
  have hkey : K * inner ℝ v v = inner ℝ w v := by
    rw [hKdef]; field_simp [hvne]
  have h1 : inner ℝ w (w - K • v) = inner ℝ w w - K * inner ℝ w v := by
    simp only [inner_sub_right, real_inner_smul_right]
  have h2 : inner ℝ (w - K • v) (w - K • v)
      = inner ℝ w w - 2 * (K * inner ℝ w v) + K * K * inner ℝ v v := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right, real_inner_comm]
    ring
  rw [h1, h2, ← hkey]
  ring

private theorem w2sg_normal_exists (hv0 : v ≠ 0) (hnc : ¬ Collinear3 0 v w) :
    ∃ n : V3, (inner ℝ n v = 0) ∧ (0 < inner ℝ n n) ∧ (inner ℝ w n = inner ℝ n n) := by
  have hvv : (0:ℝ) < inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_iff.mpr (ne_of_gt (norm_pos_iff.mpr hv0))
  have hvne : inner ℝ v v ≠ 0 := ne_of_gt hvv
  refine ⟨w - (inner ℝ w v / inner ℝ v v) • v, ?_, ?_, ?_⟩
  · rw [inner_sub_left, real_inner_smul_left]
    have hkm : inner ℝ w v / inner ℝ v v * inner ℝ v v = inner ℝ w v := by
      field_simp [hvne]
    rw [hkm, sub_self]
  · have hn0 : (w - (inner ℝ w v / inner ℝ v v) • v) ≠ 0 := by
      intro hzero
      have hc : w = (inner ℝ w v / inner ℝ v v) • v := sub_eq_zero.mp hzero
      refine hnc ?_
      exact (collinear3_iff_smul hv0).mpr ⟨_, by rw [hc, sub_zero, sub_zero]⟩
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_iff.mpr (ne_of_gt (norm_pos_iff.mpr hn0))
  · exact w2sg_inner_eq v w hvv

private theorem w2sg_arcsin_third_ge : (1/3 : ℝ) ≤ Real.arcsin (1/3) := by
  have h1 : Real.sin (1/3) ≤ (1/3 : ℝ) := le_of_lt (Real.sin_lt (by norm_num))
  have h2 : Real.arcsin (Real.sin (1/3)) ≤ Real.arcsin (1/3) := Real.arcsin_le_arcsin h1
  rw [Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])] at h2
  exact h2

private theorem w2sg_sol0_nonneg : 0 ≤ sol0 := by
  have hb : Real.arcsin (1/3 : ℝ) ≤ Real.pi / 6 := by
    have h2 : Real.arcsin (1/3 : ℝ) ≤ Real.arcsin (1/2 : ℝ) :=
      Real.arcsin_le_arcsin (by norm_num)
    have h3 : Real.arcsin (1/2 : ℝ) = Real.pi / 6 := by
      rw [show (1/2 : ℝ) = Real.sin (Real.pi / 6) from Real.sin_pi_div_six.symm,
        Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])]
    rw [h3] at h2
    exact h2
  rw [show sol0 = 3 * (Real.pi / 2 - Real.arcsin (1/3 : ℝ)) - Real.pi from by
    unfold sol0; rw [Real.arccos_eq_pi_div_two_sub_arcsin]]
  linarith

private theorem w2sg_sol0_le_pi_half : sol0 ≤ Real.pi / 2 - 1 := by
  have hb := w2sg_arcsin_third_ge
  rw [show sol0 = 3 * (Real.pi / 2 - Real.arcsin (1/3 : ℝ)) - Real.pi from by
    unfold sol0; rw [Real.arccos_eq_pi_div_two_sub_arcsin]]
  linarith

/-! ### Wheel kit (wave 2): coordinate / dichotomy tools -/

private theorem w2sg_hncol_ne {a b : V3} (h : ¬ Collinear3 0 a b) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    refine h ?_
    rw [ha]
    show Collinear ℝ ({0, (0:V3), b} : Set V3)
    rw [show ({0, (0:V3), b} : Set V3) = ({0, b} : Set V3) from by
      ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact collinear_pair ℝ 0 b
  · intro hb
    refine h ?_
    rw [hb]
    show Collinear ℝ ({0, a, (0:V3)} : Set V3)
    rw [show ({0, a, (0:V3)} : Set V3) = ({0, a} : Set V3) from by
      ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact collinear_pair ℝ 0 a

private theorem w2sg_coll3_symm {a b : V3} : Collinear3 0 a b ↔ Collinear3 0 b a := by
  unfold Collinear3
  rw [show ({0, a, b} : Set V3) = ({0, b, a} : Set V3) from by
    ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]

private theorem w2sg_coord_uniq {a b : V3} (_ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hncol : ¬ Collinear3 0 a b) {ξ₁ η₁ ξ₂ η₂ : ℝ}
    (h₁ : ξ₁ • a + η₁ • b = ξ₂ • a + η₂ • b) : ξ₁ = ξ₂ ∧ η₁ = η₂ := by
  have hsub : (ξ₁ - ξ₂) • a + (η₁ - η₂) • b = 0 := by
    have e1 : (ξ₁ - ξ₂) • a = ξ₁ • a - ξ₂ • a := by rw [sub_smul]
    have e2 : (η₁ - η₂) • b = η₁ • b - η₂ • b := by rw [sub_smul]
    rw [e1, e2, sub_add_sub_comm, h₁, sub_self]
  have hξ : ξ₁ = ξ₂ := by
    by_contra hne
    have hd : (ξ₁ - ξ₂ : ℝ) ≠ 0 := sub_ne_zero.mpr hne
    have hsplit : (ξ₁ - ξ₂) • a = (η₂ - η₁) • b := by
      have hXneg : (ξ₁ - ξ₂) • a = -((η₁ - η₂) • b) := eq_neg_of_add_eq_zero_left hsub
      rw [hXneg, ← neg_smul, show (η₂ - η₁ : ℝ) = -(η₁ - η₂) from by ring]
    have ha : a = ((ξ₁ - ξ₂ : ℝ)⁻¹ * (η₂ - η₁)) • b := by
      have h1 := congrArg ((ξ₁ - ξ₂ : ℝ)⁻¹ • ·) hsplit
      rw [inv_smul_smul₀ hd, smul_smul] at h1
      exact h1
    refine hncol ((w2sg_coll3_symm).mp
      ((collinear3_iff_smul (v := (0:V3)) (w := b) (w1 := a) hb0).mpr
        ⟨((ξ₁ - ξ₂ : ℝ)⁻¹ * (η₂ - η₁)), by rw [ha, sub_zero, sub_zero]⟩))
  constructor
  · exact hξ
  · have heq : ξ₁ - ξ₂ = 0 := sub_eq_zero.mpr hξ
    rw [heq] at hsub
    simp only [zero_smul, zero_add] at hsub
    rcases smul_eq_zero.mp hsub with hc | hc
    · linarith
    · exact absurd hc hb0


private theorem w2sg_azim_plane_dich {β x y : V3} (hβ0 : β ≠ 0)
    (h1 : ¬ Collinear3 0 β x) (h2 : ¬ Collinear3 0 β y)
    (γ δ : ℝ) (hrel : y = γ • x + δ • β) :
    (0 < γ ∧ azim 0 β x y = 0) ∨ (γ < 0 ∧ azim 0 β x y = Real.pi) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul β hβ0
  have hax : (β - 0 : V3) = dist β 0 • f3 := by
    rw [dist_zero_right, sub_zero]; exact halign
  obtain ⟨ψ, r₁, r₂, hr₁, hr₂, hB, hD⟩ := azim_frame_spec h1 h2 hon hax hβ0
  have hzβ : zOf f1 f2 β = 0 := by
    rw [show (β : V3) = β - 0 from by simp]
    exact zOf_axis hax hon
  have hx0 : zOf f1 f2 (x - 0) = zOf f1 f2 x := by rw [sub_zero]
  have hzy : zOf f1 f2 (y - 0) = ((γ : ℝ) : ℂ) * zOf f1 f2 (x - 0) := by
    rw [hrel, show ((γ • x + δ • β : V3) - 0) = γ • x + δ • β from by simp,
      zOf_add f1 f2 (γ • x) (δ • β), zOf_smul f1 f2, zOf_smul f1 f2, hzβ, mul_zero,
      add_zero, hx0]
  exact w2sg_azim_val_of_zOf_smul r₁ r₂ ψ γ hr₁ hr₂ hB hD hzy

private theorem w2sg_coll3_of_smul_sum {a b u : V3} (hncol : ¬ Collinear3 0 a b)
    {f₁ f₂ t : ℝ} (hf₁ : 0 < f₁) (hf₂ : 0 < f₂) (_ht : 0 < t)
    (hsum : f₁ • a + f₂ • b + t • u = 0) :
    ¬ Collinear3 0 a u ∧ ¬ Collinear3 0 b u ∧ a ≠ 0 ∧ b ≠ 0 ∧ u ≠ 0 := by
  obtain ⟨ha0, hb0⟩ := w2sg_hncol_ne hncol
  refine ⟨?_, ?_, ha0, hb0, ?_⟩
  · intro hc
    obtain ⟨(c : ℝ), hcu⟩ := (collinear3_iff_smul (v := (0:V3)) (w := a) ha0).mp hc
    rw [show (u : V3) = u - 0 from by simp, hcu, smul_smul, sub_zero] at hsum
    have hfac : (t * c + f₁) • a + f₂ • b = 0 := by
      rw [add_smul, add_assoc, add_comm ((t * c : ℝ) • a) (f₁ • a + f₂ • b)]
      exact hsum
    have hneg : f₂ • b = (-(t * c + f₁)) • a := by
      have h0 := eq_neg_of_add_eq_zero_right hfac
      rw [← neg_smul] at h0
      exact h0
    have hb' : b = ((f₂ : ℝ)⁻¹ * -(t * c + f₁)) • a := by
      have h2 := congrArg ((f₂ : ℝ)⁻¹ • ·) hneg
      rw [inv_smul_smul₀ (ne_of_gt hf₂), smul_smul] at h2
      exact h2
    exact hncol ((collinear3_iff_smul (v := (0:V3)) (w := a) ha0).mpr
      ⟨_, by rw [hb', sub_zero, sub_zero]⟩)
  · intro hc
    obtain ⟨(c : ℝ), hcu⟩ := (collinear3_iff_smul (v := (0:V3)) (w := b) hb0).mp hc
    rw [show (u : V3) = u - 0 from by simp, hcu, smul_smul, sub_zero] at hsum
    have hfac : f₁ • a + (f₂ + t * c) • b = 0 := by
      rw [add_smul, ← add_assoc]
      exact hsum
    have hneg : f₁ • a = (-(f₂ + t * c)) • b := by
      have h0 := eq_neg_of_add_eq_zero_left hfac
      rw [← neg_smul] at h0
      exact h0
    have ha' : a = ((f₁ : ℝ)⁻¹ * -(f₂ + t * c)) • b := by
      have h2 := congrArg ((f₁ : ℝ)⁻¹ • ·) hneg
      rw [inv_smul_smul₀ (ne_of_gt hf₁), smul_smul] at h2
      exact h2
    exact hncol ((w2sg_coll3_symm).mp
      ((collinear3_iff_smul (v := (0:V3)) (w := b) hb0).mpr
        ⟨_, by rw [ha', sub_zero, sub_zero]⟩))
  · intro hu0
    rw [hu0, smul_zero, add_zero] at hsum
    have hneg : f₁ • a = (-f₂) • b := by
      have h0 := eq_neg_of_add_eq_zero_left hsum
      rw [← neg_smul] at h0
      exact h0
    have ha' : a = ((f₁ : ℝ)⁻¹ * -f₂) • b := by
      have h2 := congrArg ((f₁ : ℝ)⁻¹ • ·) hneg
      rw [inv_smul_smul₀ (ne_of_gt hf₁), smul_smul] at h2
      exact h2
    exact hncol ((w2sg_coll3_symm).mp
      ((collinear3_iff_smul (v := (0:V3)) (w := b) hb0).mpr
        ⟨_, by rw [ha', sub_zero, sub_zero]⟩))



private theorem w2sg_span_pair_eq {a b c d : V3}
    (h1 : ¬ Collinear3 0 a b) (h2 : ¬ Collinear3 0 c d)
    (hc : c ∈ Submodule.span ℝ ({a, b} : Set V3))
    (hd : d ∈ Submodule.span ℝ ({a, b} : Set V3)) :
    Submodule.span ℝ ({c, d} : Set V3) = Submodule.span ℝ ({a, b} : Set V3) := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc
    · exact hd
  · rw [w2sg_finrank_span_pair h2, w2sg_finrank_span_pair h1]

private theorem w2sg_neg_of_pos_mul_neg {r s : ℝ} (hrs : 0 < r * s) (hs : s < 0) : r < 0 := by
  rcases Classical.em (r < 0) with h | h
  · exact h
  · exfalso
    have h2 : (0:ℝ) ≤ r := not_lt.mp h
    nlinarith [hrs, h2, hs]

private theorem w2sg_neg_of_pos_mul_neg' {r s : ℝ} (hrs : 0 < r * s) (hr : r < 0) : s < 0 := by
  rcases Classical.em (s < 0) with h | h
  · exact h
  · exfalso
    have h2 : (0:ℝ) ≤ s := not_lt.mp h
    nlinarith [hrs, h2, hr]

set_option maxHeartbeats 1600000 in
private theorem w2sg_wheel_core {a b w₂ w₃ u : V3} {f₁ f₂ t : ℝ}
    (hf₁ : 0 < f₁) (hf₂ : 0 < f₂) (ht : 0 < t)
    (hsum : f₁ • a + f₂ • b + t • u = 0)
    (hu : u = w₂ ∨ u = w₃)
    (hncAB : ¬ Collinear3 0 a b) (hncBW₂ : ¬ Collinear3 0 b w₂)
    (hncW₂W₃ : ¬ Collinear3 0 w₂ w₃) (hncW₃A : ¬ Collinear3 0 w₃ a)
    (hwAB : azim 0 a b u ≤ azim 0 a b w₃)
    (hwBW₂ : azim 0 b w₂ u ≤ azim 0 b w₂ a)
    (hwW₃A : azim 0 w₃ a b ≤ azim 0 w₃ a w₂)
    (hpileAB : azim 0 a b w₃ ≤ Real.pi)
    (hpileBW₂ : azim 0 b w₂ a ≤ Real.pi)
    (hpileW₃A : azim 0 w₃ a w₂ ≤ Real.pi) :
    azim 0 a b w₃ = Real.pi ∧ azim 0 b w₂ a = Real.pi ∧ azim 0 w₃ a w₂ = Real.pi := by
  obtain ⟨hAu, hBu, ha0, hb0, hu0⟩ := w2sg_coll3_of_smul_sum hncAB hf₁ hf₂ ht hsum
  obtain ⟨hw₃0, -⟩ := w2sg_hncol_ne hncW₃A
  have hncAW₃ : ¬ Collinear3 0 a w₃ := fun hc => hncW₃A ((w2sg_coll3_symm).mpr hc)
  have hncBA : ¬ Collinear3 0 b a := fun hc => hncAB ((w2sg_coll3_symm).mpr hc)
  have hsum' : f₂ • b + f₁ • a + t • u = 0 := by
    rw [add_comm (f₂ • b) (f₁ • a)]
    exact hsum
  obtain ⟨htri1, -⟩ := w2sg_tri_angle_pi f₂ f₁ t hf₂ hf₁ ht hsum' hncAB hAu
  have huP : u ∈ Submodule.span ℝ ({a, b} : Set V3) :=
    w2sg_mem_span_of_azim_pi ha0 hncAB hAu htri1
  obtain ⟨ξu, ηu, hcu⟩ := Submodule.mem_span_pair.mp huP
  have hcu' : u = ξu • a + ηu • b := hcu.symm
  have hcoord : f₁ + t * ξu = 0 ∧ f₂ + t * ηu = 0 := by
    have h2 : f₁ • a + f₂ • b + t • u = 0 := hsum
    rw [hcu'] at h2
    have hsplit : f₁ • a + f₂ • b + t • (ξu • a + ηu • b)
        = (f₁ + t * ξu) • a + (f₂ + t * ηu) • b := by
      module
    have h3 : f₁ • a + f₂ • b + t • (ξu • a + ηu • b)
        = (0:ℝ) • a + (0:ℝ) • b := by rw [h2, zero_smul, zero_smul, add_zero]
    rw [hsplit] at h3
    exact w2sg_coord_uniq ha0 hb0 hncAB h3
  obtain ⟨hc1, hc2⟩ := hcoord
  have hξu : ξu = -f₁ / t := by
    rw [eq_div_iff (ne_of_gt ht)]
    linear_combination hc1
  have hηu : ηu = -f₂ / t := by
    rw [eq_div_iff (ne_of_gt ht)]
    linear_combination hc2
  have hξun : ξu < 0 := by
    rw [hξu]
    exact div_neg_of_neg_of_pos (by linarith [hf₁]) ht
  have hηun : ηu < 0 := by
    rw [hηu]
    exact div_neg_of_neg_of_pos (by linarith [hf₂]) ht
  have haP : a ∈ Submodule.span ℝ ({a, b} : Set V3) :=
    Submodule.mem_span_pair.mpr ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hbP : b ∈ Submodule.span ℝ ({a, b} : Set V3) :=
    Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
  rcases hu with huw₂ | huw₃
  · -- case A: u = w₂
    rw [← huw₂] at hwW₃A hpileW₃A hncW₂W₃
    have hg0 : azim 0 a b w₃ = Real.pi :=
      le_antisymm hpileAB (by rw [← htri1]; exact hwAB)
    have hw₃P : w₃ ∈ Submodule.span ℝ ({a, b} : Set V3) :=
      w2sg_mem_span_of_azim_pi ha0 hncAB hncAW₃ hg0
    obtain ⟨ξ₃, η₃, hw₃c⟩ := Submodule.mem_span_pair.mp hw₃P
    have hw₃c' : w₃ = ξ₃ • a + η₃ • b := hw₃c.symm
    -- hg₁ : dichotomy on azim 0 b u a
    have hspBU : Submodule.span ℝ ({b, u} : Set V3)
        = Submodule.span ℝ ({a, b} : Set V3) :=
      w2sg_span_pair_eq hncAB hBu hbP huP
    obtain ⟨γ₁, δ₁, h⟩ := Submodule.mem_span_pair.mp (by rw [hspBU]; exact haP)
    have hrel₁ : a = δ₁ • u + γ₁ • b := by rw [h.symm, add_comm (γ₁ • b) (δ₁ • u)]
    have htr₁ : δ₁ • u + γ₁ • b = (δ₁ * ξu) • a + (δ₁ * ηu + γ₁) • b := by
      rw [hcu']; module
    have hkey₁ := w2sg_coord_uniq ha0 hb0 hncAB (ξ₁ := δ₁ * ξu)
      (η₁ := δ₁ * ηu + γ₁) (ξ₂ := 1) (η₂ := 0) (by
        rw [← htr₁, ← hrel₁, one_smul, zero_smul, add_zero])
    obtain ⟨hδ₁ξ, -⟩ := hkey₁
    have hpδ₁ : (0:ℝ) < δ₁ * ξu := by rw [hδ₁ξ]; norm_num
    have hδ₁ : δ₁ < 0 := w2sg_neg_of_pos_mul_neg hpδ₁ hξun
    rcases w2sg_azim_plane_dich hb0 hBu hncBA δ₁ γ₁ hrel₁ with ⟨hδ₁pos, hz1⟩ | hg₁'
    · exfalso
      linarith [hδ₁pos, hδ₁]
    · have hg₁ : azim 0 b w₂ a = Real.pi := by rw [← huw₂]; exact hg₁'.2
      -- hg₃ : dichotomy on azim 0 w₃ a u
      have hncW₃U : ¬ Collinear3 0 w₃ u :=
        fun hc => hncW₂W₃ ((w2sg_coll3_symm).mpr hc)
      have hspW₃A : Submodule.span ℝ ({w₃, a} : Set V3)
          = Submodule.span ℝ ({a, b} : Set V3) :=
        w2sg_span_pair_eq hncAB hncW₃A hw₃P haP
      obtain ⟨γ₃, δ₃, h⟩ := Submodule.mem_span_pair.mp (by rw [hspW₃A]; exact huP)
      have hrel₃ : u = δ₃ • a + γ₃ • w₃ := by rw [h.symm, add_comm (γ₃ • w₃) (δ₃ • a)]
      rcases w2sg_azim_plane_dich hw₃0 hncW₃A hncW₃U δ₃ γ₃ hrel₃ with
        ⟨hδ₃pos, hz3⟩ | ⟨hγ₃neg, hg₃'⟩
      · exfalso
        -- bad branch: wedge at dart (w₃, a) collapses at z = b
        have hcol : azim 0 w₃ a b = 0 := by
          have h1 : azim 0 w₃ a b ≤ azim 0 w₃ a u := hwW₃A
          rw [hz3] at h1
          exact le_antisymm h1 (azim_nonneg 0 w₃ a b)
        rcases Classical.em (Collinear3 0 w₃ b) with hcolWB | hncW₃B
        · -- degenerate: b = c • w₃ forces δ₃ = ξu < 0
          exfalso
          obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0:V3)) (w := w₃) hw₃0).mp hcolWB
          have hbeq' : b = c • w₃ := by simpa using hc
          have husub : u = ξu • a + ηu • (c • w₃) := by rw [hcu', hbeq']
          have hkeyD := w2sg_coord_uniq (ha0) (hw₃0) (hncAW₃) (ξ₁ := δ₃) (η₁ := γ₃)
            (ξ₂ := ξu) (η₂ := ηu * c) (by
              rw [← hrel₃, husub, mul_smul])
          obtain ⟨hDD, -⟩ := hkeyD
          linarith [hDD, hδ₃pos, hξun]
        · -- generic: dichotomy on azim 0 w₃ a b
          obtain ⟨γ₄, δ₄, h⟩ := Submodule.mem_span_pair.mp (by rw [hspW₃A]; exact hbP)
          have hrel₄ : b = δ₄ • a + γ₄ • w₃ := by
            rw [h.symm, add_comm (γ₄ • w₃) (δ₄ • a)]
          rcases w2sg_azim_plane_dich hw₃0 hncW₃A hncW₃B δ₄ γ₄ hrel₄ with
            ⟨hδ₄pos, hz4⟩ | ⟨hγ₄neg, hπ₄⟩
          · exfalso
            have htr₃ : δ₃ • a + γ₃ • w₃ = (δ₃ + γ₃ * ξ₃) • a + (γ₃ * η₃) • b := by
              rw [hw₃c']; module
            have hkey₃ := w2sg_coord_uniq ha0 hb0 hncAB (ξ₁ := δ₃ + γ₃ * ξ₃)
              (η₁ := γ₃ * η₃) (ξ₂ := ξu) (η₂ := ηu) (by
                rw [← htr₃, ← hrel₃, ← hcu'])
            obtain ⟨he3, he4⟩ := hkey₃
            have htr₄ : δ₄ • a + γ₄ • w₃ = (δ₄ + γ₄ * ξ₃) • a + (γ₄ * η₃) • b := by
              rw [hw₃c']; module
            have hkey₄ := w2sg_coord_uniq ha0 hb0 hncAB (ξ₁ := δ₄ + γ₄ * ξ₃)
              (η₁ := γ₄ * η₃) (ξ₂ := 0) (η₂ := 1) (by
                rw [← htr₄, ← hrel₄, zero_smul, one_smul, zero_add])
            obtain ⟨he5, he6⟩ := hkey₄
            have hη₃ne : η₃ ≠ 0 := by
              intro h0
              rw [h0, mul_zero] at he6
              linarith
            have ht1 : t * ξu = -f₁ := by linear_combination hc1
            have ht2 : t * ηu = -f₂ := by linear_combination hc2
            have hrel3 : f₁ * η₃ - f₂ * ξ₃ + t * (ξu * η₃ - ηu * ξ₃) = 0 := by
              linear_combination ht1 * η₃ - ht2 * ξ₃
            have hsum3 : -(f₁ * η₃ - f₂ * ξ₃ + t * (ξu * η₃ - ηu * ξ₃)) = 0 := by
              rw [hrel3]; ring
            rw [show ξu * η₃ - ηu * ξ₃ = δ₃ * η₃ from by
                linear_combination ξ₃ * he4 - η₃ * he3,
              show ξ₃ = δ₄ * (0 - η₃) from by
                linear_combination η₃ * he5 - ξ₃ * he6] at hsum3
            rw [show -(f₁ * η₃ - f₂ * (δ₄ * (0 - η₃)) + t * (δ₃ * η₃))
                = -((f₁ + f₂ * δ₄ + t * δ₃) * η₃) from by ring] at hsum3
            rw [neg_eq_zero, mul_eq_zero] at hsum3
            rcases hsum3 with hc | hc
            · have hp1 : (0:ℝ) < f₂ * δ₄ := mul_pos hf₂ hδ₄pos
              have hp2 : (0:ℝ) < t * δ₃ := mul_pos ht hδ₃pos
              linarith [hf₁, hp1, hp2, hc]
            · exact hη₃ne hc
          · exfalso
            have h1 : azim 0 w₃ a b ≤ azim 0 w₃ a u := hwW₃A
            rw [hπ₄, hz3] at h1
            linarith [h1, Real.pi_pos]
      · have hg₃ : azim 0 w₃ a w₂ = Real.pi := by rw [← huw₂]; exact hg₃'
        exact ⟨hg0, hg₁, hg₃⟩
  · -- case B: u = w₃
    have hw₃c : w₃ = ξu • a + ηu • b := by rw [← huw₃]; exact hcu.symm
    have hg0 : azim 0 a b w₃ = Real.pi := by rw [← huw₃]; exact htri1
    have hw₃P : w₃ ∈ Submodule.span ℝ ({a, b} : Set V3) :=
      w2sg_mem_span_of_azim_pi ha0 hncAB hncAW₃ hg0
    -- hg₃ : wedge at dart (w₃, a) with z = b forces π
    have hspW₃A : Submodule.span ℝ ({w₃, a} : Set V3)
        = Submodule.span ℝ ({a, b} : Set V3) :=
      w2sg_span_pair_eq hncAB hncW₃A hw₃P haP
    rcases Classical.em (Collinear3 0 w₃ b) with hcolWB | hncW₃B
    · exfalso
      -- degenerate: b = c • w₃ forces ξu = 0
      obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0:V3)) (w := w₃) hw₃0).mp hcolWB
      have hbeq' : b = c • w₃ := by simpa using hc
      have hkeyD := w2sg_coord_uniq (ha0) (hw₃0) (hncAW₃) (ξ₁ := 0) (η₁ := 1)
        (ξ₂ := ξu) (η₂ := ηu * c) (by
          rw [zero_smul, zero_add, one_smul, mul_smul, ← hbeq', hw₃c])
      obtain ⟨hDD, -⟩ := hkeyD
      rw [hDD] at hξun
      linarith
    · -- generic: dichotomy on azim 0 w₃ a b
      obtain ⟨γ₄, δ₄, h⟩ := Submodule.mem_span_pair.mp (by rw [hspW₃A]; exact hbP)
      have hrel₄ : b = δ₄ • a + γ₄ • w₃ := by
        rw [h.symm, add_comm (γ₄ • w₃) (δ₄ • a)]
      have htr₄ : δ₄ • a + γ₄ • w₃ = (δ₄ + γ₄ * ξu) • a + (γ₄ * ηu) • b := by
        rw [hw₃c]; module
      have hkey₄ := w2sg_coord_uniq ha0 hb0 hncAB (ξ₁ := δ₄ + γ₄ * ξu)
        (η₁ := γ₄ * ηu) (ξ₂ := 0) (η₂ := 1) (by
          rw [← htr₄, ← hrel₄, zero_smul, one_smul, zero_add])
      obtain ⟨he5, he6⟩ := hkey₄
      have hpγ₄ : (0:ℝ) < γ₄ * ηu := by rw [he6]; norm_num
      have hγ₄ : γ₄ < 0 := w2sg_neg_of_pos_mul_neg hpγ₄ hηun
      have hpgξ : (0:ℝ) < γ₄ * ξu := by nlinarith [hγ₄, hξun]
      have hδ₄n : δ₄ < 0 := by
        rcases Classical.em (δ₄ < 0) with h | h
        · exact h
        · exfalso
          have h2 : (0:ℝ) ≤ δ₄ := not_lt.mp h
          nlinarith [he5, hpgξ, h2]
      rcases w2sg_azim_plane_dich hw₃0 hncW₃A hncW₃B δ₄ γ₄ hrel₄ with
        ⟨hδ₄pos, hz0⟩ | ⟨hγ₄neg, hzAB⟩
      · exact absurd hδ₄pos (not_lt.mpr hδ₄n.le)
      · -- hzAB : azim 0 w₃ a b = Real.pi
        have hg₃ : azim 0 w₃ a w₂ = Real.pi := by
          have h1 : Real.pi ≤ azim 0 w₃ a w₂ := by
            have h2 : azim 0 w₃ a b ≤ azim 0 w₃ a w₂ := hwW₃A
            rw [hzAB] at h2
            exact h2
          exact le_antisymm hpileW₃A h1
        -- planarize w₂ via T3 on hg₃
        have hncW₃W₂ : ¬ Collinear3 0 w₃ w₂ :=
          fun hc => hncW₂W₃ ((w2sg_coll3_symm).mpr hc)
        have hw₂P : w₂ ∈ Submodule.span ℝ ({a, b} : Set V3) := by
          have h1 := w2sg_mem_span_of_azim_pi hw₃0 hncW₃A hncW₃W₂ hg₃
          rw [hspW₃A] at h1
          exact h1
        -- hg₁ : dichotomy on azim 0 b w₂ a
        have hspBW₂ : Submodule.span ℝ ({b, w₂} : Set V3)
            = Submodule.span ℝ ({a, b} : Set V3) :=
          w2sg_span_pair_eq hncAB hncBW₂ hbP hw₂P
        obtain ⟨ξ₂, η₂, hw₂c⟩ := Submodule.mem_span_pair.mp hw₂P
        have hw₂c' : w₂ = ξ₂ • a + η₂ • b := hw₂c.symm
        obtain ⟨γ₁, δ₁, h⟩ := Submodule.mem_span_pair.mp (by rw [hspBW₂]; exact haP)
        have hrel₁ : a = δ₁ • w₂ + γ₁ • b := by
          rw [h.symm, add_comm (γ₁ • b) (δ₁ • w₂)]
        have htr₁ : δ₁ • w₂ + γ₁ • b = (δ₁ * ξ₂) • a + (δ₁ * η₂ + γ₁) • b := by
          rw [hw₂c']; module
        have hkey₁ := w2sg_coord_uniq ha0 hb0 hncAB (ξ₁ := δ₁ * ξ₂)
          (η₁ := δ₁ * η₂ + γ₁) (ξ₂ := 1) (η₂ := 0) (by
            rw [← htr₁, ← hrel₁, one_smul, zero_smul, add_zero])
        obtain ⟨hδ₁ξ, -⟩ := hkey₁
        rcases w2sg_azim_plane_dich hb0 hncBW₂ hncBA δ₁ γ₁ hrel₁ with
          ⟨hδ₁pos, hz1⟩ | ⟨hγ₁neg, hg₁'⟩
        · exfalso
          -- bad branch: wedge at dart (b, w₂) collapses at z = u
          have hcol : azim 0 b w₂ u = 0 := by
            have h2 : azim 0 b w₂ u ≤ azim 0 b w₂ a := hwBW₂
            rw [hz1] at h2
            exact le_antisymm h2 (azim_nonneg 0 b w₂ u)
          have hξ₂p : (0:ℝ) < ξ₂ := by nlinarith [hδ₁pos, hδ₁ξ]
          obtain ⟨γ₂, δ₂, h⟩ := Submodule.mem_span_pair.mp (by rw [hspBW₂]; exact huP)
          have hrel₂ : u = δ₂ • w₂ + γ₂ • b := by
            rw [h.symm, add_comm (γ₂ • b) (δ₂ • w₂)]
          have htr₂ : δ₂ • w₂ + γ₂ • b = (δ₂ * ξ₂) • a + (δ₂ * η₂ + γ₂) • b := by
            rw [hw₂c']; module
          have hkey₂ := w2sg_coord_uniq ha0 hb0 hncAB (ξ₁ := δ₂ * ξ₂)
            (η₁ := δ₂ * η₂ + γ₂) (ξ₂ := ξu) (η₂ := ηu) (by
              rw [← htr₂, ← hrel₂, ← hcu'])
          obtain ⟨hδ₂ξ, -⟩ := hkey₂
          rcases w2sg_azim_plane_dich hb0 hncBW₂ hBu δ₂ γ₂ hrel₂ with
            ⟨hδ₂pos, hz2⟩ | ⟨hγ₂neg, hπ₂⟩
          · exfalso
            have hp : (0:ℝ) < ξu := by rw [← hδ₂ξ]; exact mul_pos hδ₂pos hξ₂p
            linarith [hp, hξun]
          · linarith [hπ₂, hcol, Real.pi_pos]
        · have hg₁ : azim 0 b w₂ a = Real.pi := hg₁'
          exact ⟨hg0, hg₁, hg₃⟩

/-! ### W2′ 车道私件（scsgeneric-w2c, 2026-10-28）：JKQEWGV2_CASE_4_p23 收口套件。

四件 ee-链（ee_eq / ee_ncard / sigmaFan_eq / azimInFan_eq，修 w2b §4.1 的
`Set.mem_insert` 族 elaboration 卡点）+ 装配桥（fan6→¬Coll3、ConvexLocalFan 楔形
投影、F 的四元插入形与 ncard/setSum 计算）+ tauFun 下界 + dsv 上界，供
`JKQEWGV2_CASE_4_p23` 终算。全部 private、零 sorry、零 native_decide。 -/

private theorem w2sg_coll3_self (z : V3) : Collinear3 0 z z := by
  have h : ({0, z, z} : Set V3) = {0, z} := by
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  show Collinear ℝ ({0, z, z} : Set V3)
  rw [h]
  exact collinear_pair ℝ 0 z

private theorem w2sg_ee_eq (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j) (E : Set (Set V3))
    (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (k : ℕ) (hk : k < 4) :
    ee (vv k) E = {vv ((k + 1) % 4), vv ((k + 3) % 4)} := by
  ext w
  have hlt1 : (k + 1) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hlt2 : (k + 3) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hmem1 : ({vv k, w} : Set V3) ∈ E ↔ w = vv ((k + 1) % 4) ∨ w = vv ((k + 3) % 4) := by
    constructor
    · intro hm
      rw [hE] at hm
      obtain ⟨i, hi, hset⟩ := w2sg_memE_iff vv hper hm
      have hi4 : (i + 1) % 4 < 4 := Nat.mod_lt _ (by omega)
      have hme1 : vv k ∈ ({vv i, vv ((i + 1) % 4)} : Set V3) := by rw [← hset]; simp
      have hme2 : w ∈ ({vv i, vv ((i + 1) % 4)} : Set V3) := by rw [← hset]; simp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme1 hme2
      have hwk : w ≠ vv k := by
        intro hc
        rw [hc] at hset
        have hpair : ∀ t : V3, t ∈ ({vv k, vv k} : Set V3) → t = vv k := by
          intro t ht
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
          rcases ht with ht | ht <;> exact ht
        have g1 : vv i = vv k := hpair _ (by rw [hset]; simp)
        have g2 : vv ((i + 1) % 4) = vv k := hpair _ (by rw [hset]; simp)
        exact hinj i ((i + 1) % 4) hi hi4 (by omega) (g1.trans g2.symm)
      rcases hme1 with hc | hc
      · have hik : i = k := by
          by_contra hne
          exact hinj i k hi hk hne hc.symm
        rcases hme2 with hw | hw
        · exact absurd (hw.trans hc.symm) hwk
        · rw [hik] at hw
          exact Or.inl hw
      · have hik2 : (i + 1) % 4 = k := by
          by_contra hne
          exact hinj ((i + 1) % 4) k hi4 hk hne hc.symm
        rcases hme2 with hw | hw
        · have hik3 : i = (k + 3) % 4 := by omega
          rw [hik3] at hw
          exact Or.inr hw
        · rw [hik2] at hw
          exact absurd hw hwk
    · rintro (hw | hw)
      · have hb : ({vv k, vv (k + 1)} : Set V3) = ({vv k, w} : Set V3) := by
          rw [(periodic_mod_eq_p23 hper (k + 1)).symm, hw]
        rw [hE, ← hb]
        exact Set.mem_image_of_mem (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) (Set.mem_univ k)
      · have hb : ({vv ((k + 3) % 4), vv ((k + 3) % 4 + 1)} : Set V3)
            = ({vv k, w} : Set V3) := by
          rw [← periodic_mod_eq_p23 hper ((k + 3) % 4 + 1),
            show (((k + 3) % 4 + 1) % 4) = k % 4 from by omega,
            periodic_mod_eq_p23 hper k, hw]
          exact Set.pair_comm _ _
        rw [hE, ← hb]
        exact Set.mem_image_of_mem (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          (Set.mem_univ ((k + 3) % 4))
  simp only [ee, Set.mem_setOf_eq, hmem1, Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem w2sg_ee_ncard (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j) (E : Set (Set V3))
    (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (k : ℕ) (hk : k < 4) : (ee (vv k) E).ncard = 2 := by
  rw [w2sg_ee_eq vv hper hinj E hE k hk]
  have hne : vv ((k + 1) % 4) ≠ vv ((k + 3) % 4) :=
    fun hc => hinj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by omega) hc
  have hfin : ({vv ((k + 1) % 4), vv ((k + 3) % 4)} : Set V3).Finite := by simp
  rw [Set.ncard_eq_toFinset_card ({vv ((k + 1) % 4), vv ((k + 3) % 4)} : Set V3) hfin]
  have htf : hfin.toFinset
      = insert (vv ((k + 1) % 4)) (insert (vv ((k + 3) % 4)) (∅ : Finset V3)) := by
    ext t; simp
  rw [htf, Finset.card_insert_of_notMem (by simp [hne]),
    Finset.card_insert_of_notMem (by simp), Finset.card_empty]

private theorem w2sg_sigmaFan_eq (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j) (E : Set (Set V3))
    (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (k : ℕ) (hk : k < 4) :
    Fan.sigmaFan (0:V3) Set.univ E (vv k) (vv ((k + 1) % 4)) = vv ((k + 3) % 4) ∧
    Fan.sigmaFan (0:V3) Set.univ E (vv k) (vv ((k + 3) % 4)) = vv ((k + 1) % 4) := by
  have hE2 : Fan.setOfEdge (vv k) Set.univ E = {vv ((k + 1) % 4), vv ((k + 3) % 4)} := by
    ext w'
    simp only [Fan.setOfEdge, Set.mem_setOf_eq, Set.mem_univ, and_true,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [show ({vv k, w'} : Set V3) ∈ E ↔ w' ∈ ee (vv k) E from Iff.rfl,
      w2sg_ee_eq vv hper hinj E hE k hk]
    simp
  have hlt1 : (k + 1) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hlt2 : (k + 3) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hne : vv ((k + 1) % 4) ≠ vv ((k + 3) % 4) :=
    fun hc => hinj _ _ hlt1 hlt2 (by omega) hc
  unfold Fan.sigmaFan
  have hnotsing1 : Fan.setOfEdge (vv k) Set.univ E ≠ {vv ((k + 1) % 4)} := by
    rw [hE2]
    intro hc
    have hmem : vv ((k + 3) % 4) ∈ ({vv ((k + 1) % 4), vv ((k + 3) % 4)} : Set V3) := by simp
    rw [hc] at hmem
    simp only [Set.mem_singleton_iff] at hmem
    exact hne hmem.symm
  have hnotsing2 : Fan.setOfEdge (vv k) Set.univ E ≠ {vv ((k + 3) % 4)} := by
    rw [hE2]
    intro hc
    have hmem : vv ((k + 1) % 4) ∈ ({vv ((k + 1) % 4), vv ((k + 3) % 4)} : Set V3) := by simp
    rw [hc] at hmem
    simp only [Set.mem_singleton_iff] at hmem
    exact hne hmem
  constructor
  · rw [if_neg hnotsing1]
    refine epsilonFixed ?_ ?_
    · show vv ((k + 3) % 4) ∈ Fan.setOfEdge (vv k) Set.univ E ∧
        vv ((k + 3) % 4) ≠ vv ((k + 1) % 4) ∧
        ∀ w₁ ∈ Fan.setOfEdge (vv k) Set.univ E,
          w₁ ≠ vv ((k + 1) % 4) →
            azim 0 (vv k) (vv ((k + 1) % 4)) (vv ((k + 3) % 4)) ≤
              azim 0 (vv k) (vv ((k + 1) % 4)) w₁
      rw [hE2]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨Or.inr trivial, hne.symm, ?_⟩
      intro w₁ hw₁ hw₁n
      rcases hw₁ with hw₁ | hw₁
      · exact absurd hw₁ hw₁n
      · rw [hw₁]
    · intro y hy
      rw [hE2] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy.1 with hc | hc
      · exact absurd hc hy.2.1
      · exact hc
  · rw [if_neg hnotsing2]
    refine epsilonFixed ?_ ?_
    · show vv ((k + 1) % 4) ∈ Fan.setOfEdge (vv k) Set.univ E ∧
        vv ((k + 1) % 4) ≠ vv ((k + 3) % 4) ∧
        ∀ w₁ ∈ Fan.setOfEdge (vv k) Set.univ E,
          w₁ ≠ vv ((k + 3) % 4) →
            azim 0 (vv k) (vv ((k + 3) % 4)) (vv ((k + 1) % 4)) ≤
              azim 0 (vv k) (vv ((k + 3) % 4)) w₁
      rw [hE2]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨Or.inl trivial, hne, ?_⟩
      intro w₁ hw₁ hw₁n
      rcases hw₁ with hw₁ | hw₁
      · rw [hw₁]
      · exact absurd hw₁ hw₁n
    · intro y hy
      rw [hE2] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy.1 with hc | hc
      · exact hc
      · exact absurd hc hy.2.1

private theorem w2sg_azimInFan_eq (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j) (E : Set (Set V3))
    (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (k : ℕ) (hk : k < 4) :
    azimInFan (vv k, vv ((k + 1) % 4)) E
      = azim 0 (vv k) (vv ((k + 1) % 4)) (vv ((k + 3) % 4)) := by
  have hnc : 1 < (ee (vv k) E).ncard := by
    rw [w2sg_ee_ncard vv hper hinj E hE k hk]
    norm_num
  rw [azimInFan, if_pos hnc]
  rw [(w2sg_sigmaFan_eq vv hper hinj E hE k hk).1]

/-! #### 装配桥：FAN 投影 / 楔形 / F 的插入形 -/

private theorem w2sg_fan6_ncol (vv : ℕ → V3) (hper : Periodic vv 4)
    (E : Set (Set V3)) (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (hf6 : ∀ e ∈ E, ¬ Collinear ℝ (insert (0:V3) e))
    {k : ℕ} (hk : k < 4) : ¬ Collinear3 0 (vv k) (vv ((k + 1) % 4)) := by
  have hem : ({vv k, vv ((k + 1) % 4)} : Set V3) ∈ E := by
    rw [hE]
    exact ⟨k, Set.mem_univ _, by rw [(periodic_mod_eq_p23 hper (k + 1))]⟩
  exact hf6 _ hem

private theorem w2sg_wedge_le (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j)
    (E : Set (Set V3)) (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (V : Set V3)
    (hw : ∀ x ∈ (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ,
      V ⊆ wedgeInFanGe x E)
    {k : ℕ} (hk : k < 4) {z : V3} (hz : z ∈ V) :
    azim 0 (vv k) (vv ((k + 1) % 4)) z
      ≤ azim 0 (vv k) (vv ((k + 1) % 4)) (vv ((k + 3) % 4)) := by
  have hd : (vv k, vv ((k + 1) % 4))
      ∈ (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ :=
    ⟨k, Set.mem_univ _, by rw [(periodic_mod_eq_p23 hper (k + 1))]⟩
  have hncard : 1 < (ee (vv k) E).ncard := by
    rw [w2sg_ee_ncard vv hper hinj E hE k hk]
    norm_num
  have hz2 := hw _ hd hz
  rw [wedgeInFanGe, if_pos hncard] at hz2
  rw [(w2sg_sigmaFan_eq vv hper hinj E hE k hk).1] at hz2
  simp only [wedgeGe, Set.mem_setOf_eq] at hz2
  exact hz2.2

private theorem w2sg_norm_ge_two (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    (m : ℕ) : (2:ℝ) ≤ norm (vv m) := by
  have h1 : vv m ∈ ballAnnulus := hBB.1 (Set.mem_range.mpr ⟨m, rfl⟩)
  obtain ⟨-, h2⟩ := h1
  rw [Metric.mem_ball, dist_zero_right] at h2
  exact le_of_not_gt h2

private theorem w2sg_rhoFun_ge_one {y : ℝ} (hy : 2 ≤ y) : (1:ℝ) ≤ rhoFun y := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hd1 : (0:ℝ) ≤ 1 / (2 * h0 - 2) :=
    div_nonneg (by norm_num) (by norm_num [h0])
  have hd2 : (0:ℝ) ≤ (1 / (2 * h0 - 2)) * (1 / Real.pi) :=
    mul_nonneg hd1 (div_nonneg (by norm_num) hpi.le)
  have hy2 : (0:ℝ) ≤ y - 2 := by linarith
  unfold rhoFun
  have hterm : (0:ℝ) ≤ (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (y - 2) :=
    mul_nonneg (mul_nonneg hd2 w2sg_sol0_nonneg) hy2
  linarith

private theorem w2sg_dsv_le (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s) (hk : s.k = 4)
    (hBB : BBsV39 s vv) : dsvV39 s vv ≤ s.d := by
  obtain ⟨hd09, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbc, -, -, -⟩ := hs
  have hne : ¬ isEarV39 s := by
    intro hc
    obtain ⟨-, -, hkear, -, -, -⟩ := hc
    omega
  have hsum : (0:ℝ) ≤ setSum {i : ℕ | i < s.k ∧ s.J i (i + 1)}
      (fun i => cstab - dist (vv i) (vv (i + 1))) := by
    rw [setSum]
    split
    · rename_i hfin
      refine Finset.sum_nonneg ?_
      intro i hi
      have hmem := hfin.mem_toFinset.mp hi
      obtain ⟨hi4, hj⟩ := hmem
      have hdle := (hBB.2.2.1 i (i + 1)).2
      have hcb := hbc i (by omega)
      exact sub_nonneg.mpr (le_trans hdle hcb)
    · exact le_refl 0
  unfold dsvV39
  rw [if_neg hne]
  linarith

private theorem w2sg_F_insert (vv : ℕ → V3) (hper : Periodic vv 4) :
    (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ
      = insert (vv 0, vv (0 + 1)) (insert (vv 1, vv (1 + 1))
          (insert (vv 2, vv (2 + 1))
            (insert (vv 3, vv (3 + 1)) (∅ : Set (V3 × V3))))) := by
  ext d
  constructor
  · rintro ⟨i, -, hd⟩
    have h1 : vv i = vv (i % 4) := (periodic_mod_eq_p23 hper i).symm
    have h2 : vv (i + 1) = vv ((i % 4 + 1) % 4) := by
      rw [← periodic_mod_eq_p23 hper (i + 1)]
      congr 1
      omega
    rw [← hd]
    simp only
    rw [h1, h2]
    rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h, show ((3 + 1) % 4 : ℕ) = 0 from by norm_num, ← hper 0]
      simp
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hd
    rcases hd with hd | hd
    · exact ⟨0, Set.mem_univ _, hd.symm⟩
    · rcases hd with hd | hd
      · exact ⟨1, Set.mem_univ _, hd.symm⟩
      · rcases hd with hd | hd
        · exact ⟨2, Set.mem_univ _, hd.symm⟩
        · exact ⟨3, Set.mem_univ _, hd.symm⟩

private theorem w2sg_F_ncard (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j) :
    Set.ncard ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) = 4 := by
  rw [w2sg_F_insert vv hper]
  have hne : ∀ m n : ℕ, m < 4 → n < 4 → m ≠ n →
      (vv m, vv (m + 1)) ≠ (vv n, vv (n + 1)) := by
    intro m n hm hn hmn hc
    simp only [Prod.mk.injEq] at hc
    exact hinj m n hm hn hmn hc.1
  have hd0 : (vv 0, vv (0 + 1)) ∉ insert ((vv 1, vv (1 + 1)) : V3 × V3)
      (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1)) (∅ : Set (V3 × V3)))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 0 1 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 0 2 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hne 0 3 (by omega) (by omega) (by omega) hc
        · exact absurd hc (Set.notMem_empty _)
  have hd1 : (vv 1, vv (1 + 1)) ∉ insert ((vv 2, vv (2 + 1)) : V3 × V3)
      (insert (vv 3, vv (3 + 1)) (∅ : Set (V3 × V3))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 1 2 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 1 3 (by omega) (by omega) (by omega) hc
      · exact absurd hc (Set.notMem_empty _)
  have hd2 : (vv 2, vv (2 + 1)) ∉ insert ((vv 3, vv (3 + 1)) : V3 × V3)
      (∅ : Set (V3 × V3)) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 2 3 (by omega) (by omega) (by omega) hc
    · exact absurd hc (Set.notMem_empty _)
  have hd3 : (vv 3, vv (3 + 1)) ∉ (∅ : Set (V3 × V3)) := Set.notMem_empty _
  rw [Set.ncard_insert_of_notMem hd0, Set.ncard_insert_of_notMem hd1,
    Set.ncard_insert_of_notMem hd2, Set.ncard_insert_of_notMem hd3, Set.ncard_empty]

private theorem w2sg_setSum_F (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j)
    (g : V3 × V3 → ℝ) :
    setSum ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) g
      = g (vv 0, vv ((0 + 1) % 4)) + g (vv 1, vv ((1 + 1) % 4))
          + g (vv 2, vv ((2 + 1) % 4)) + g (vv 3, vv ((3 + 1) % 4)) := by
  have hnd : ∀ m n : ℕ, m < 4 → n < 4 → m ≠ n →
      (vv m, vv (m + 1)) ≠ (vv n, vv (n + 1)) := by
    intro m n hm hn hmn hc
    simp only [Prod.mk.injEq] at hc
    exact hinj m n hm hn hmn hc.1
  rw [w2sg_F_insert vv hper]
  simp only [setSum]
  split
  · rename_i hfin
    have htf : hfin.toFinset
        = insert (vv 0, vv (0 + 1)) (insert (vv 1, vv (1 + 1))
            (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1)) (∅ : Finset (V3 × V3))))) := by
      ext t; simp
    rw [htf]
    have hd0 : (vv 0, vv (0 + 1)) ∉ insert (vv 1, vv (1 + 1))
        (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1))
          (∅ : Finset (V3 × V3)))) := by
      intro hc
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        or_false] at hc
      rcases hc with hc | hc
      · exact hnd 0 1 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hnd 0 2 (by omega) (by omega) (by omega) hc
        · exact hnd 0 3 (by omega) (by omega) (by omega) hc
    have hd1 : (vv 1, vv (1 + 1)) ∉ insert (vv 2, vv (2 + 1))
        (insert (vv 3, vv (3 + 1)) (∅ : Finset (V3 × V3))) := by
      intro hc
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        or_false] at hc
      rcases hc with hc | hc
      · exact hnd 1 2 (by omega) (by omega) (by omega) hc
      · exact hnd 1 3 (by omega) (by omega) (by omega) hc
    have hd2 : (vv 2, vv (2 + 1)) ∉
        insert (vv 3, vv (3 + 1)) (∅ : Finset (V3 × V3)) := by
      intro hc
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hc
      exact hnd 2 3 (by omega) (by omega) (by omega) hc
    have hd3 : (vv 3, vv (3 + 1)) ∉ (∅ : Finset (V3 × V3)) := Finset.notMem_empty _
    rw [Finset.sum_insert hd0, Finset.sum_insert hd1, Finset.sum_insert hd2,
      Finset.sum_insert hd3]
    have hb3 : ((vv 3, vv (3 + 1)) : V3 × V3) = (vv 3, vv ((3 + 1) % 4)) := by
      rw [show ((3 + 1) % 4 : ℕ) = 0 from by norm_num, ← hper 0]
    rw [hb3]
    ring
  · rename_i hnofin
    exact absurd
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
        (Set.Finite.insert _ (Set.finite_empty (α := V3 × V3))))))
      hnofin

private theorem w2sg_tau_ge (vv : ℕ → V3) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j)
    (E : Set (Set V3)) (hE : E = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
    (i : ℕ) (hi : i < 4)
    (h1 : azim 0 (vv i) (vv ((i + 1) % 4)) (vv ((i + 3) % 4)) = Real.pi)
    (h2 : azim 0 (vv ((i + 1) % 4)) (vv ((i + 2) % 4)) (vv i) = Real.pi)
    (h3 : azim 0 (vv ((i + 3) % 4)) (vv i) (vv ((i + 2) % 4)) = Real.pi)
    (hρ : ∀ m : ℕ, m < 4 → (1:ℝ) ≤ rhoFun (norm (vv m))) :
    (Real.pi - 2 * sol0) ≤ tauFun (Set.range vv) E
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) := by
  have hsum := w2sg_setSum_F vv hper hinj
    (fun e => rhoFun (norm e.1) * azimInFan e E)
  have hcard := w2sg_F_ncard vv hper hinj
  unfold tauFun
  simp only [hsum, hcard]
  have hcoef : (((4 - 2 : ℕ) : ℝ)) = 2 := by norm_num
  rw [hcoef]
  have hz0 : rhoFun (norm (vv 0)) * azimInFan (vv 0, vv ((0 + 1) % 4)) E
      = rhoFun (norm (vv 0)) * azim 0 (vv 0) (vv ((0 + 1) % 4)) (vv ((0 + 3) % 4)) := by
    rw [w2sg_azimInFan_eq vv hper hinj E hE 0 (by omega)]
  have hz1 : rhoFun (norm (vv 1)) * azimInFan (vv 1, vv ((1 + 1) % 4)) E
      = rhoFun (norm (vv 1)) * azim 0 (vv 1) (vv ((1 + 1) % 4)) (vv ((1 + 3) % 4)) := by
    rw [w2sg_azimInFan_eq vv hper hinj E hE 1 (by omega)]
  have hz2 : rhoFun (norm (vv 2)) * azimInFan (vv 2, vv ((2 + 1) % 4)) E
      = rhoFun (norm (vv 2)) * azim 0 (vv 2) (vv ((2 + 1) % 4)) (vv ((2 + 3) % 4)) := by
    rw [w2sg_azimInFan_eq vv hper hinj E hE 2 (by omega)]
  have hz3 : rhoFun (norm (vv 3)) * azimInFan (vv 3, vv ((3 + 1) % 4)) E
      = rhoFun (norm (vv 3)) * azim 0 (vv 3) (vv ((3 + 1) % 4)) (vv ((3 + 3) % 4)) := by
    rw [w2sg_azimInFan_eq vv hper hinj E hE 3 (by omega)]
  rw [hz0, hz1, hz2, hz3]
  have hge : ∀ m : ℕ, m < 4 →
      rhoFun (norm (vv m)) * azim 0 (vv m) (vv ((m + 1) % 4)) (vv ((m + 3) % 4))
        ≥ azim 0 (vv m) (vv ((m + 1) % 4)) (vv ((m + 3) % 4)) := by
    intro m hm
    have hρm := hρ m hm
    have haz : (0:ℝ) ≤ azim 0 (vv m) (vv ((m + 1) % 4)) (vv ((m + 3) % 4)) :=
      azim_nonneg _ _ _ _
    have hle := mul_le_mul_of_nonneg_right hρm haz
    linarith
  have haz : ∀ m : ℕ, m < 4 →
      (0:ℝ) ≤ azim 0 (vv m) (vv ((m + 1) % 4)) (vv ((m + 3) % 4)) := fun m _ =>
    azim_nonneg _ _ _ _
  have hge0 := hge 0 (by omega)
  have hge1 := hge 1 (by omega)
  have hge2 := hge 2 (by omega)
  have hge3 := hge 3 (by omega)
  have haz0 := haz 0 (by omega)
  have haz1 := haz 1 (by omega)
  have haz2 := haz 2 (by omega)
  have haz3 := haz 3 (by omega)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simp only [show ((0 + 1) % 4 : ℕ) = 1 from by norm_num,
      show ((0 + 2) % 4 : ℕ) = 2 from by norm_num,
      show ((0 + 3) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 1) % 4 : ℕ) = 2 from by norm_num,
      show ((1 + 2) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 3) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 1) % 4 : ℕ) = 3 from by norm_num,
      show ((2 + 2) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 3) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 1) % 4 : ℕ) = 0 from by norm_num,
      show ((3 + 2) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 3) % 4 : ℕ) = 2 from by norm_num] at h1 h2 h3 hge0 hge1 hge2 hge3 haz0 haz1 haz2 haz3 ⊢
    linarith [h1, h2, h3, hge0, hge1, hge2, hge3, haz0, haz1, haz2, haz3, Real.pi_pos]
  · simp only [show ((0 + 1) % 4 : ℕ) = 1 from by norm_num,
      show ((0 + 2) % 4 : ℕ) = 2 from by norm_num,
      show ((0 + 3) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 1) % 4 : ℕ) = 2 from by norm_num,
      show ((1 + 2) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 3) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 1) % 4 : ℕ) = 3 from by norm_num,
      show ((2 + 2) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 3) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 1) % 4 : ℕ) = 0 from by norm_num,
      show ((3 + 2) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 3) % 4 : ℕ) = 2 from by norm_num] at h1 h2 h3 hge0 hge1 hge2 hge3 haz0 haz1 haz2 haz3 ⊢
    linarith [h1, h2, h3, hge0, hge1, hge2, hge3, haz0, haz1, haz2, haz3, Real.pi_pos]
  · simp only [show ((0 + 1) % 4 : ℕ) = 1 from by norm_num,
      show ((0 + 2) % 4 : ℕ) = 2 from by norm_num,
      show ((0 + 3) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 1) % 4 : ℕ) = 2 from by norm_num,
      show ((1 + 2) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 3) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 1) % 4 : ℕ) = 3 from by norm_num,
      show ((2 + 2) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 3) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 1) % 4 : ℕ) = 0 from by norm_num,
      show ((3 + 2) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 3) % 4 : ℕ) = 2 from by norm_num] at h1 h2 h3 hge0 hge1 hge2 hge3 haz0 haz1 haz2 haz3 ⊢
    linarith [h1, h2, h3, hge0, hge1, hge2, hge3, haz0, haz1, haz2, haz3, Real.pi_pos]
  · simp only [show ((0 + 1) % 4 : ℕ) = 1 from by norm_num,
      show ((0 + 2) % 4 : ℕ) = 2 from by norm_num,
      show ((0 + 3) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 1) % 4 : ℕ) = 2 from by norm_num,
      show ((1 + 2) % 4 : ℕ) = 3 from by norm_num,
      show ((1 + 3) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 1) % 4 : ℕ) = 3 from by norm_num,
      show ((2 + 2) % 4 : ℕ) = 0 from by norm_num,
      show ((2 + 3) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 1) % 4 : ℕ) = 0 from by norm_num,
      show ((3 + 2) % 4 : ℕ) = 1 from by norm_num,
      show ((3 + 3) % 4 : ℕ) = 2 from by norm_num] at h1 h2 h3 hge0 hge1 hge2 hge3 haz0 haz1 haz2 haz3 ⊢
    linarith [h1, h2, h3, hge0, hge1, hge2, hge3, haz0, haz1, haz2, haz3, Real.pi_pos]

/-! ### W3 车道私件（scsgeneric-w3b, 2026-10-28）：CASE_5/6 引擎路线终算套件。

`circularAzimInFanPi_cs`（CircularSolKit，HOL `CIRCULAR_SOL_EQ_2PI` 的 per-dart
面）给每 dart `azimInFan = π`，绕开 k=4 wheel 路线在 k=5/6 的 slot-枚举缺口
（scsgeneric-w2c DELIVERY §4.2：k=5/6 时弦 {vv (i+3), vv i} 非边、fan6 断链）。
本套件仅需：F 的 5/6 元插入形 + ncard/setSum 计数（w2sg_F_* 的 `%4 → %k` 机械
泛化，k=5 补集基数 2 / k=6 基数 3）+ tauFun 下界 `2π − 4·sol0`（k=5/6 统一形，
因 `2π − (k−2)(π+sol0) ≥ 2π − 4sol0` 对 k ∈ {5,6} 成立）+ dsv 上界的 k-泛化形
（w2sg_dsv_le 的 `3 < s.k` 形）。全部 private、零 sorry、零 native_decide。 -/

private theorem w3sg_dsv_le (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s) (hk : 3 < s.k)
    (hBB : BBsV39 s vv) : dsvV39 s vv ≤ s.d := by
  obtain ⟨hd09, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbc, -, -, -⟩ := hs
  have hne : ¬ isEarV39 s := by
    intro hc
    obtain ⟨-, -, hkear, -, -, -⟩ := hc
    omega
  have hsum : (0:ℝ) ≤ setSum {i : ℕ | i < s.k ∧ s.J i (i + 1)}
      (fun i => cstab - dist (vv i) (vv (i + 1))) := by
    rw [setSum]
    split
    · rename_i hfin
      refine Finset.sum_nonneg ?_
      intro i hi
      have hmem := hfin.mem_toFinset.mp hi
      obtain ⟨hik, hj⟩ := hmem
      have hdle := (hBB.2.2.1 i (i + 1)).2
      have hcb := hbc i hk
      exact sub_nonneg.mpr (le_trans hdle hcb)
    · exact le_refl 0
  unfold dsvV39
  rw [if_neg hne]
  linarith

private theorem w3sg_F_insert5 (vv : ℕ → V3) (hper : Periodic vv 5) :
    (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ
      = insert (vv 0, vv (0 + 1)) (insert (vv 1, vv (1 + 1))
          (insert (vv 2, vv (2 + 1))
            (insert (vv 3, vv (3 + 1))
              (insert (vv 4, vv (4 + 1)) (∅ : Set (V3 × V3)))))) := by
  ext d
  constructor
  · rintro ⟨i, -, hd⟩
    have h1 : vv i = vv (i % 5) := (periodic_mod_eq_p23 hper i).symm
    have h2 : vv (i + 1) = vv ((i % 5 + 1) % 5) := by
      rw [← periodic_mod_eq_p23 hper (i + 1)]
      congr 1
      omega
    rw [← hd]
    simp only
    rw [h1, h2]
    rcases (by omega : i % 5 = 0 ∨ i % 5 = 1 ∨ i % 5 = 2 ∨ i % 5 = 3 ∨ i % 5 = 4) with h | h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h, show ((4 + 1) % 5 : ℕ) = 0 from by norm_num, ← hper 0]
      simp
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hd
    rcases hd with hd | hd
    · exact ⟨0, Set.mem_univ _, hd.symm⟩
    · rcases hd with hd | hd
      · exact ⟨1, Set.mem_univ _, hd.symm⟩
      · rcases hd with hd | hd
        · exact ⟨2, Set.mem_univ _, hd.symm⟩
        · rcases hd with hd | hd
          · exact ⟨3, Set.mem_univ _, hd.symm⟩
          · exact ⟨4, Set.mem_univ _, hd.symm⟩

private theorem w3sg_F_ncard5 (vv : ℕ → V3) (hper : Periodic vv 5)
    (hinj : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → vv i ≠ vv j) :
    Set.ncard ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) = 5 := by
  rw [w3sg_F_insert5 vv hper]
  have hne : ∀ m n : ℕ, m < 5 → n < 5 → m ≠ n →
      (vv m, vv (m + 1)) ≠ (vv n, vv (n + 1)) := by
    intro m n hm hn hmn hc
    simp only [Prod.mk.injEq] at hc
    exact hinj m n hm hn hmn hc.1
  have hd0 : (vv 0, vv (0 + 1)) ∉ insert ((vv 1, vv (1 + 1)) : V3 × V3)
      (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1))
        (insert (vv 4, vv (4 + 1)) (∅ : Set (V3 × V3))))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 0 1 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 0 2 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hne 0 3 (by omega) (by omega) (by omega) hc
        · rcases hc with hc | hc
          · exact hne 0 4 (by omega) (by omega) (by omega) hc
          · exact absurd hc (Set.notMem_empty _)
  have hd1 : (vv 1, vv (1 + 1)) ∉ insert ((vv 2, vv (2 + 1)) : V3 × V3)
      (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (∅ : Set (V3 × V3)))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 1 2 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 1 3 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hne 1 4 (by omega) (by omega) (by omega) hc
        · exact absurd hc (Set.notMem_empty _)
  have hd2 : (vv 2, vv (2 + 1)) ∉ insert ((vv 3, vv (3 + 1)) : V3 × V3)
      (insert (vv 4, vv (4 + 1)) (∅ : Set (V3 × V3))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 2 3 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 2 4 (by omega) (by omega) (by omega) hc
      · exact absurd hc (Set.notMem_empty _)
  have hd3 : (vv 3, vv (3 + 1)) ∉ insert ((vv 4, vv (4 + 1)) : V3 × V3)
      (∅ : Set (V3 × V3)) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 3 4 (by omega) (by omega) (by omega) hc
    · exact absurd hc (Set.notMem_empty _)
  have hd4 : (vv 4, vv (4 + 1)) ∉ (∅ : Set (V3 × V3)) := Set.notMem_empty _
  rw [Set.ncard_insert_of_notMem hd0, Set.ncard_insert_of_notMem hd1,
    Set.ncard_insert_of_notMem hd2, Set.ncard_insert_of_notMem hd3,
    Set.ncard_insert_of_notMem hd4, Set.ncard_empty]

private theorem w3sg_setSum_F5 (vv : ℕ → V3) (hper : Periodic vv 5)
    (hinj : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → vv i ≠ vv j)
    (g : V3 × V3 → ℝ) :
    setSum ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) g
      = g (vv 0, vv ((0 + 1) % 5)) + g (vv 1, vv ((1 + 1) % 5))
          + g (vv 2, vv ((2 + 1) % 5)) + g (vv 3, vv ((3 + 1) % 5))
          + g (vv 4, vv ((4 + 1) % 5)) := by
  have hnd : ∀ m n : ℕ, m < 5 → n < 5 → m ≠ n →
      (vv m, vv (m + 1)) ≠ (vv n, vv (n + 1)) := by
    intro m n hm hn hmn hc
    simp only [Prod.mk.injEq] at hc
    exact hinj m n hm hn hmn hc.1
  rw [w3sg_F_insert5 vv hper]
  simp only [setSum]
  split
  · rename_i hfin
    have htf : hfin.toFinset
        = insert (vv 0, vv (0 + 1)) (insert (vv 1, vv (1 + 1))
            (insert (vv 2, vv (2 + 1))
              (insert (vv 3, vv (3 + 1))
                (insert (vv 4, vv (4 + 1)) (∅ : Finset (V3 × V3)))))) := by
      ext t; simp
    rw [htf]
    have hd4 : (vv 4, vv (4 + 1)) ∉ (∅ : Finset (V3 × V3)) := Finset.notMem_empty _
    have hd3 : (vv 3, vv (3 + 1)) ∉ (insert (vv 4, vv (4 + 1)) (∅ : Finset (V3 × V3))) := by
      intro hc
      refine hnd 3 4 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc) (Finset.notMem_empty _)
    have hd2 : (vv 2, vv (2 + 1)) ∉ (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (∅ : Finset (V3 × V3)))) := by
      intro hc
      refine hnd 2 3 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 2 4 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc2) (Finset.notMem_empty _)
    have hd1 : (vv 1, vv (1 + 1)) ∉ (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (∅ : Finset (V3 × V3))))) := by
      intro hc
      refine hnd 1 2 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 1 3 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc2) ?_
      intro hc3
      refine hnd 1 4 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc3) (Finset.notMem_empty _)
    have hd0 : (vv 0, vv (0 + 1)) ∉ (insert (vv 1, vv (1 + 1)) (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (∅ : Finset (V3 × V3)))))) := by
      intro hc
      refine hnd 0 1 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 0 2 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc2) ?_
      intro hc3
      refine hnd 0 3 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc3) ?_
      intro hc4
      refine hnd 0 4 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc4) (Finset.notMem_empty _)
    rw [Finset.sum_insert hd0, Finset.sum_insert hd1, Finset.sum_insert hd2,
      Finset.sum_insert hd3, Finset.sum_insert hd4]
    have hb4 : ((vv 4, vv (4 + 1)) : V3 × V3) = (vv 4, vv ((4 + 1) % 5)) := by
      rw [show ((4 + 1) % 5 : ℕ) = 0 from by norm_num, ← hper 0]
    rw [hb4]
    ring
  · rename_i hnofin
    exact absurd
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
        (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_empty (α := V3 × V3)))))))
      hnofin

private theorem w3sg_tau_ge5 (vv : ℕ → V3) (hper : Periodic vv 5)
    (hinj : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → vv i ≠ vv j)
    (hdart : ∀ d ∈ (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ,
      azimInFan d ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) = Real.pi)
    (hρ : ∀ m : ℕ, (1:ℝ) ≤ rhoFun (norm (vv m))) :
    ((2 * Real.pi - 4 * sol0) : ℝ) ≤ tauFun (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) := by
  have hsum := w3sg_setSum_F5 vv hper hinj
    (fun e => rhoFun (norm e.1) * azimInFan e
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ))
  have hcard := w3sg_F_ncard5 vv hper hinj
  unfold tauFun
  simp only [hsum, hcard]
  have hcoef : (((5 - 2 : ℕ) : ℝ)) = 3 := by norm_num
  rw [hcoef]
  have hd0 : (vv 0, vv ((0 + 1) % 5)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨0, Set.mem_univ _, rfl⟩
  have hd1 : (vv 1, vv ((1 + 1) % 5)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨1, Set.mem_univ _, rfl⟩
  have hd2 : (vv 2, vv ((2 + 1) % 5)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨2, Set.mem_univ _, rfl⟩
  have hd3 : (vv 3, vv ((3 + 1) % 5)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨3, Set.mem_univ _, rfl⟩
  have hd4 : (vv 4, vv ((4 + 1) % 5)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
    refine ⟨4, Set.mem_univ _, ?_⟩
    show (vv 4, vv (4 + 1)) = (vv 4, vv ((4 + 1) % 5))
    rw [show ((4 + 1) % 5 : ℕ) = 0 from by norm_num, ← hper 0]
  have hz0 : rhoFun (norm (vv 0)) * azimInFan (vv 0, vv ((0 + 1) % 5))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 0)) * Real.pi := by rw [hdart _ hd0]
  have hz1 : rhoFun (norm (vv 1)) * azimInFan (vv 1, vv ((1 + 1) % 5))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 1)) * Real.pi := by rw [hdart _ hd1]
  have hz2 : rhoFun (norm (vv 2)) * azimInFan (vv 2, vv ((2 + 1) % 5))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 2)) * Real.pi := by rw [hdart _ hd2]
  have hz3 : rhoFun (norm (vv 3)) * azimInFan (vv 3, vv ((3 + 1) % 5))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 3)) * Real.pi := by rw [hdart _ hd3]
  have hz4 : rhoFun (norm (vv 4)) * azimInFan (vv 4, vv ((4 + 1) % 5))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 4)) * Real.pi := by rw [hdart _ hd4]
  rw [hz0, hz1, hz2, hz3, hz4]
  have hge : ∀ m : ℕ, (1:ℝ) * Real.pi ≤ rhoFun (norm (vv m)) * Real.pi := fun m =>
    mul_le_mul_of_nonneg_right (hρ m) (le_of_lt Real.pi_pos)
  linarith [hge 0, hge 1, hge 2, hge 3, hge 4, w2sg_sol0_nonneg]

private theorem w3sg_F_insert6 (vv : ℕ → V3) (hper : Periodic vv 6) :
    (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ
      = insert (vv 0, vv (0 + 1)) (insert (vv 1, vv (1 + 1))
          (insert (vv 2, vv (2 + 1))
            (insert (vv 3, vv (3 + 1))
              (insert (vv 4, vv (4 + 1))
                (insert (vv 5, vv (5 + 1)) (∅ : Set (V3 × V3))))))) := by
  ext d
  constructor
  · rintro ⟨i, -, hd⟩
    have h1 : vv i = vv (i % 6) := (periodic_mod_eq_p23 hper i).symm
    have h2 : vv (i + 1) = vv ((i % 6 + 1) % 6) := by
      rw [← periodic_mod_eq_p23 hper (i + 1)]
      congr 1
      omega
    rw [← hd]
    simp only
    rw [h1, h2]
    rcases (by omega : i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 2 ∨ i % 6 = 3 ∨ i % 6 = 4 ∨ i % 6 = 5) with h | h | h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h, show ((5 + 1) % 6 : ℕ) = 0 from by norm_num, ← hper 0]
      simp
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hd
    rcases hd with hd | hd
    · exact ⟨0, Set.mem_univ _, hd.symm⟩
    · rcases hd with hd | hd
      · exact ⟨1, Set.mem_univ _, hd.symm⟩
      · rcases hd with hd | hd
        · exact ⟨2, Set.mem_univ _, hd.symm⟩
        · rcases hd with hd | hd
          · exact ⟨3, Set.mem_univ _, hd.symm⟩
          · rcases hd with hd | hd
            · exact ⟨4, Set.mem_univ _, hd.symm⟩
            · exact ⟨5, Set.mem_univ _, hd.symm⟩

private theorem w3sg_F_ncard6 (vv : ℕ → V3) (hper : Periodic vv 6)
    (hinj : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → vv i ≠ vv j) :
    Set.ncard ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) = 6 := by
  rw [w3sg_F_insert6 vv hper]
  have hne : ∀ m n : ℕ, m < 6 → n < 6 → m ≠ n →
      (vv m, vv (m + 1)) ≠ (vv n, vv (n + 1)) := by
    intro m n hm hn hmn hc
    simp only [Prod.mk.injEq] at hc
    exact hinj m n hm hn hmn hc.1
  have hd0 : (vv 0, vv (0 + 1)) ∉ insert ((vv 1, vv (1 + 1)) : V3 × V3)
      (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1))
        (insert (vv 4, vv (4 + 1)) (insert (vv 5, vv (5 + 1))
          (∅ : Set (V3 × V3)))))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 0 1 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 0 2 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hne 0 3 (by omega) (by omega) (by omega) hc
        · rcases hc with hc | hc
          · exact hne 0 4 (by omega) (by omega) (by omega) hc
          · rcases hc with hc | hc
            · exact hne 0 5 (by omega) (by omega) (by omega) hc
            · exact absurd hc (Set.notMem_empty _)
  have hd1 : (vv 1, vv (1 + 1)) ∉ insert ((vv 2, vv (2 + 1)) : V3 × V3)
      (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1))
        (insert (vv 5, vv (5 + 1)) (∅ : Set (V3 × V3))))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 1 2 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 1 3 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hne 1 4 (by omega) (by omega) (by omega) hc
        · rcases hc with hc | hc
          · exact hne 1 5 (by omega) (by omega) (by omega) hc
          · exact absurd hc (Set.notMem_empty _)
  have hd2 : (vv 2, vv (2 + 1)) ∉ insert ((vv 3, vv (3 + 1)) : V3 × V3)
      (insert (vv 4, vv (4 + 1)) (insert (vv 5, vv (5 + 1))
        (∅ : Set (V3 × V3)))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 2 3 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 2 4 (by omega) (by omega) (by omega) hc
      · rcases hc with hc | hc
        · exact hne 2 5 (by omega) (by omega) (by omega) hc
        · exact absurd hc (Set.notMem_empty _)
  have hd3 : (vv 3, vv (3 + 1)) ∉ insert ((vv 4, vv (4 + 1)) : V3 × V3)
      (insert (vv 5, vv (5 + 1)) (∅ : Set (V3 × V3))) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 3 4 (by omega) (by omega) (by omega) hc
    · rcases hc with hc | hc
      · exact hne 3 5 (by omega) (by omega) (by omega) hc
      · exact absurd hc (Set.notMem_empty _)
  have hd4 : (vv 4, vv (4 + 1)) ∉ insert ((vv 5, vv (5 + 1)) : V3 × V3)
      (∅ : Set (V3 × V3)) := by
    intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · exact hne 4 5 (by omega) (by omega) (by omega) hc
    · exact absurd hc (Set.notMem_empty _)
  have hd5 : (vv 5, vv (5 + 1)) ∉ (∅ : Set (V3 × V3)) := Set.notMem_empty _
  rw [Set.ncard_insert_of_notMem hd0, Set.ncard_insert_of_notMem hd1,
    Set.ncard_insert_of_notMem hd2, Set.ncard_insert_of_notMem hd3,
    Set.ncard_insert_of_notMem hd4, Set.ncard_insert_of_notMem hd5,
    Set.ncard_empty]

private theorem w3sg_setSum_F6 (vv : ℕ → V3) (hper : Periodic vv 6)
    (hinj : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → vv i ≠ vv j)
    (g : V3 × V3 → ℝ) :
    setSum ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) g
      = g (vv 0, vv ((0 + 1) % 6)) + g (vv 1, vv ((1 + 1) % 6))
          + g (vv 2, vv ((2 + 1) % 6)) + g (vv 3, vv ((3 + 1) % 6))
          + g (vv 4, vv ((4 + 1) % 6)) + g (vv 5, vv ((5 + 1) % 6)) := by
  have hnd : ∀ m n : ℕ, m < 6 → n < 6 → m ≠ n →
      (vv m, vv (m + 1)) ≠ (vv n, vv (n + 1)) := by
    intro m n hm hn hmn hc
    simp only [Prod.mk.injEq] at hc
    exact hinj m n hm hn hmn hc.1
  rw [w3sg_F_insert6 vv hper]
  simp only [setSum]
  split
  · rename_i hfin
    have htf : hfin.toFinset
        = insert (vv 0, vv (0 + 1)) (insert (vv 1, vv (1 + 1))
            (insert (vv 2, vv (2 + 1))
              (insert (vv 3, vv (3 + 1))
                (insert (vv 4, vv (4 + 1))
                  (insert (vv 5, vv (5 + 1)) (∅ : Finset (V3 × V3))))))) := by
      ext t; simp
    rw [htf]
    have hd5 : (vv 5, vv (5 + 1)) ∉ (∅ : Finset (V3 × V3)) := Finset.notMem_empty _
    have hd4 : (vv 4, vv (4 + 1)) ∉ (insert (vv 5, vv (5 + 1)) (∅ : Finset (V3 × V3))) := by
      intro hc
      refine hnd 4 5 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc) (Finset.notMem_empty _)
    have hd3 : (vv 3, vv (3 + 1)) ∉ (insert (vv 4, vv (4 + 1)) (insert (vv 5, vv (5 + 1)) (∅ : Finset (V3 × V3)))) := by
      intro hc
      refine hnd 3 4 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 3 5 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc2) (Finset.notMem_empty _)
    have hd2 : (vv 2, vv (2 + 1)) ∉ (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (insert (vv 5, vv (5 + 1)) (∅ : Finset (V3 × V3))))) := by
      intro hc
      refine hnd 2 3 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 2 4 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc2) ?_
      intro hc3
      refine hnd 2 5 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc3) (Finset.notMem_empty _)
    have hd1 : (vv 1, vv (1 + 1)) ∉ (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (insert (vv 5, vv (5 + 1)) (∅ : Finset (V3 × V3)))))) := by
      intro hc
      refine hnd 1 2 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 1 3 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc2) ?_
      intro hc3
      refine hnd 1 4 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc3) ?_
      intro hc4
      refine hnd 1 5 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc4) (Finset.notMem_empty _)
    have hd0 : (vv 0, vv (0 + 1)) ∉ (insert (vv 1, vv (1 + 1)) (insert (vv 2, vv (2 + 1)) (insert (vv 3, vv (3 + 1)) (insert (vv 4, vv (4 + 1)) (insert (vv 5, vv (5 + 1)) (∅ : Finset (V3 × V3))))))) := by
      intro hc
      refine hnd 0 1 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc) ?_
      intro hc2
      refine hnd 0 2 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc2) ?_
      intro hc3
      refine hnd 0 3 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc3) ?_
      intro hc4
      refine hnd 0 4 (by omega) (by omega) (by omega) ?_
      refine Or.resolve_right (Finset.mem_insert.mp hc4) ?_
      intro hc5
      refine hnd 0 5 (by omega) (by omega) (by omega) ?_
      exact Or.resolve_right (Finset.mem_insert.mp hc5) (Finset.notMem_empty _)
    rw [Finset.sum_insert hd0, Finset.sum_insert hd1, Finset.sum_insert hd2,
      Finset.sum_insert hd3, Finset.sum_insert hd4, Finset.sum_insert hd5]
    have hb5 : ((vv 5, vv (5 + 1)) : V3 × V3) = (vv 5, vv ((5 + 1) % 6)) := by
      rw [show ((5 + 1) % 6 : ℕ) = 0 from by norm_num, ← hper 0]
    rw [hb5]
    ring
  · rename_i hnofin
    exact absurd
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
        (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
          (Set.finite_empty (α := V3 × V3))))))))
      hnofin

private theorem w3sg_tau_ge6 (vv : ℕ → V3) (hper : Periodic vv 6)
    (hinj : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → vv i ≠ vv j)
    (hdart : ∀ d ∈ (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ,
      azimInFan d ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) = Real.pi)
    (hρ : ∀ m : ℕ, (1:ℝ) ≤ rhoFun (norm (vv m))) :
    ((2 * Real.pi - 4 * sol0) : ℝ) ≤ tauFun (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) := by
  have hsum := w3sg_setSum_F6 vv hper hinj
    (fun e => rhoFun (norm e.1) * azimInFan e
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ))
  have hcard := w3sg_F_ncard6 vv hper hinj
  unfold tauFun
  simp only [hsum, hcard]
  have hcoef : (((6 - 2 : ℕ) : ℝ)) = 4 := by norm_num
  rw [hcoef]
  have hd0 : (vv 0, vv ((0 + 1) % 6)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨0, Set.mem_univ _, rfl⟩
  have hd1 : (vv 1, vv ((1 + 1) % 6)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨1, Set.mem_univ _, rfl⟩
  have hd2 : (vv 2, vv ((2 + 1) % 6)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨2, Set.mem_univ _, rfl⟩
  have hd3 : (vv 3, vv ((3 + 1) % 6)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨3, Set.mem_univ _, rfl⟩
  have hd4 : (vv 4, vv ((4 + 1) % 6)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := ⟨4, Set.mem_univ _, rfl⟩
  have hd5 : (vv 5, vv ((5 + 1) % 6)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
    refine ⟨5, Set.mem_univ _, ?_⟩
    show (vv 5, vv (5 + 1)) = (vv 5, vv ((5 + 1) % 6))
    rw [show ((5 + 1) % 6 : ℕ) = 0 from by norm_num, ← hper 0]
  have hz0 : rhoFun (norm (vv 0)) * azimInFan (vv 0, vv ((0 + 1) % 6))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 0)) * Real.pi := by rw [hdart _ hd0]
  have hz1 : rhoFun (norm (vv 1)) * azimInFan (vv 1, vv ((1 + 1) % 6))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 1)) * Real.pi := by rw [hdart _ hd1]
  have hz2 : rhoFun (norm (vv 2)) * azimInFan (vv 2, vv ((2 + 1) % 6))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 2)) * Real.pi := by rw [hdart _ hd2]
  have hz3 : rhoFun (norm (vv 3)) * azimInFan (vv 3, vv ((3 + 1) % 6))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 3)) * Real.pi := by rw [hdart _ hd3]
  have hz4 : rhoFun (norm (vv 4)) * azimInFan (vv 4, vv ((4 + 1) % 6))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 4)) * Real.pi := by rw [hdart _ hd4]
  have hz5 : rhoFun (norm (vv 5)) * azimInFan (vv 5, vv ((5 + 1) % 6))
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      = rhoFun (norm (vv 5)) * Real.pi := by rw [hdart _ hd5]
  rw [hz0, hz1, hz2, hz3, hz4, hz5]
  have hge : ∀ m : ℕ, (1:ℝ) * Real.pi ≤ rhoFun (norm (vv m)) * Real.pi := fun m =>
    mul_le_mul_of_nonneg_right (hρ m) (le_of_lt Real.pi_pos)
  linarith [hge 0, hge 1, hge 2, hge 3, hge 4, hge 5, w2sg_sol0_nonneg]

/-- HOL `JKQEWGV2_CASE_4` (JKQEWGV.hl:2974): the realisation graph is not
circular. NEEDS: the `JKQEWGV1_CASE_4` kit. -/
theorem JKQEWGV2_CASE_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  intro hc
  obtain ⟨p, q, u₀, hem, huV, hnc⟩ := hc
  have hper : Periodic vv 4 := hk ▸ hBB.2.1
  have hinj : ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → vv i ≠ vv j :=
    fun i j hi4 hj4 hij =>
      w2sg_vv_inj s vv hs hBB (by rw [hk]; exact hi4) (by rw [hk]; exact hj4) hij
  have hCLF : ConvexLocalFan (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) := by
    rcases hBB.2.2.2 with hle | hcl
    · rw [hk] at hle; omega
    · have hconv1 : (Set.range fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          = ((fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      have hconv2 : (Set.range fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3))
          = ((fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      rw [hconv1, hconv2] at hcl
      exact hcl
  obtain ⟨hf, -, -, -, -, -⟩ := hCLF.1
  obtain ⟨i, hi, hset⟩ := w2sg_memE_iff vv hper hem
  rw [hset] at hnc
  have hncAB := w2sg_fan6_ncol vv hper _ rfl hf.2.2.2.2.1 hi
  obtain ⟨ha0, hb0⟩ := w2sg_hncol_ne hncAB
  have hne : (affGt ({0} : Set V3) ({vv i, vv ((i + 1) % 4)} : Set V3) ∩
      affLt ({0} : Set V3) ({u₀} : Set V3)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hnc
  obtain ⟨x, hx1, hx2⟩ := hne
  have hab : (vv i : V3) ≠ vv ((i + 1) % 4) :=
    fun hcon => hinj i ((i + 1) % 4) hi (Nat.mod_lt _ (by omega)) (by omega) hcon
  obtain ⟨ν, μ, hν, hμ, hxg⟩ := w2sg_affGt_pair ha0 hb0 hab hx1
  have hu₀ne : u₀ ≠ 0 := fun hcon => hf.2.2.2.1 (hcon ▸ huV)
  obtain ⟨τ, hτ, hxl⟩ := w2sg_affLt_single hu₀ne hx2
  have hxeq : ν • (vv i : V3) + μ • (vv ((i + 1) % 4)) = -(τ • u₀) := hxg.symm.trans hxl
  have hsum : ν • (vv i : V3) + μ • (vv ((i + 1) % 4)) + τ • u₀ = 0 := by
    rw [hxeq]
    simp
  obtain ⟨hAu, hBu, -, -, -⟩ := w2sg_coll3_of_smul_sum hncAB hν hμ hτ hsum
  obtain ⟨j, hjV⟩ := huV
  have hu₀V : u₀ ∈ Set.range vv := ⟨j, hjV⟩
  have hj4 : j % 4 < 4 := Nat.mod_lt _ (by omega)
  have hu₀slot : u₀ = vv (j % 4) := by rw [← hjV, periodic_mod_eq_p23 hper j]
  have hji : j % 4 ≠ i := by
    intro hcon
    rw [hcon] at hu₀slot
    exact hAu (by rw [hu₀slot]; exact w2sg_coll3_self _)
  have hjnext : j % 4 ≠ (i + 1) % 4 := by
    intro hcon
    rw [hcon] at hu₀slot
    exact hBu (by rw [hu₀slot]; exact w2sg_coll3_self _)
  have hslot : u₀ = vv ((i + 2) % 4) ∨ u₀ = vv ((i + 3) % 4) := by
    rw [hu₀slot]
    rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h
    · have e2 : ((i + 2) % 4 : ℕ) = 2 := by rw [Nat.add_mod, h]
      have e3 : ((i + 3) % 4 : ℕ) = 3 := by rw [Nat.add_mod, h]
      rcases (by omega : (j : ℕ) % 4 = (i + 2) % 4 ∨ j % 4 = (i + 3) % 4) with hh | hh
      · exact Or.inl (congrArg vv hh)
      · exact Or.inr (congrArg vv hh)
    · have e2 : ((i + 2) % 4 : ℕ) = 3 := by rw [Nat.add_mod, h]
      have e3 : ((i + 3) % 4 : ℕ) = 0 := by rw [Nat.add_mod, h]
      rcases (by omega : (j : ℕ) % 4 = (i + 2) % 4 ∨ j % 4 = (i + 3) % 4) with hh | hh
      · exact Or.inl (congrArg vv hh)
      · exact Or.inr (congrArg vv hh)
    · have e2 : ((i + 2) % 4 : ℕ) = 0 := by rw [Nat.add_mod, h]
      rcases (by omega : (j : ℕ) % 4 = (i + 2) % 4 ∨ j % 4 = (i + 3) % 4) with hh | hh
      · exact Or.inl (congrArg vv hh)
      · exact Or.inr (congrArg vv hh)
    · have e3 : ((i + 3) % 4 : ℕ) = 2 := by rw [Nat.add_mod, h]
      rcases (by omega : (j : ℕ) % 4 = (i + 2) % 4 ∨ j % 4 = (i + 3) % 4) with hh | hh
      · exact Or.inl (congrArg vv hh)
      · exact Or.inr (congrArg vv hh)
  have hwedge : ∀ k : ℕ, k < 4 → ∀ z : V3, z ∈ Set.range vv →
      azim 0 (vv k) (vv ((k + 1) % 4)) z
        ≤ azim 0 (vv k) (vv ((k + 1) % 4)) (vv ((k + 3) % 4)) :=
    fun k hk4 z hz => w2sg_wedge_le vv hper hinj _ rfl (Set.range vv)
      (fun y hy => (hCLF.2 y hy).2) hk4 hz
  have hwAB := hwedge i hi u₀ hu₀V
  have hwBW₂ := hwedge ((i + 1) % 4) (by omega) u₀ hu₀V
  have hwW₃A := hwedge ((i + 3) % 4) (by omega) (vv ((i + 1) % 4))
    (Set.mem_range.mpr ⟨(i + 1) % 4, rfl⟩)
  rw [show (((i + 1) % 4 + 1) % 4 : ℕ) = (i + 2) % 4 from by omega,
    show (((i + 1) % 4 + 3) % 4 : ℕ) = i % 4 from by omega,
    periodic_mod_eq_p23 hper i] at hwBW₂
  rw [show (((i + 3) % 4 + 1) % 4 : ℕ) = i % 4 from by omega, periodic_mod_eq_p23 hper i,
    show (((i + 3) % 4 + 3) % 4 : ℕ) = (i + 2) % 4 from by omega] at hwW₃A
  have hdA : (vv i, vv ((i + 1) % 4)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ :=
    ⟨i, Set.mem_univ _, by rw [(periodic_mod_eq_p23 hper (i + 1))]⟩
  have hdB : (vv ((i + 1) % 4), vv ((i + 2) % 4)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
    refine ⟨(i + 1) % 4, Set.mem_univ _, ?_⟩
    show (vv ((i + 1) % 4), vv ((i + 1) % 4 + 1)) = (vv ((i + 1) % 4), vv ((i + 2) % 4))
    rw [← periodic_mod_eq_p23 hper ((i + 1) % 4 + 1),
      show (((i + 1) % 4 + 1) % 4) = (i + 2) % 4 from by omega]
  have hdD : (vv ((i + 3) % 4), vv ((i + 3) % 4 + 1)) ∈
      (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ :=
    ⟨(i + 3) % 4, Set.mem_univ _, rfl⟩
  have hpileAB : azim 0 (vv i) (vv ((i + 1) % 4)) (vv ((i + 3) % 4)) ≤ Real.pi := by
    have hp := (hCLF.2 _ hdA).1
    rw [w2sg_azimInFan_eq vv hper hinj _ rfl i hi] at hp
    exact hp
  have hpileBW₂ : azim 0 (vv ((i + 1) % 4)) (vv ((i + 2) % 4)) (vv i) ≤ Real.pi := by
    have hp := (hCLF.2 _ hdB).1
    rw [show ((i + 2) % 4 : ℕ) = ((i + 1) % 4 + 1) % 4 from by omega] at hp
    rw [w2sg_azimInFan_eq vv hper hinj _ rfl ((i + 1) % 4) (by omega)] at hp
    rw [show (((i + 1) % 4 + 1) % 4 : ℕ) = (i + 2) % 4 from by omega,
      show (((i + 1) % 4 + 3) % 4 : ℕ) = i % 4 from by omega,
      periodic_mod_eq_p23 hper i] at hp
    exact hp
  have hpileW₃A : azim 0 (vv ((i + 3) % 4)) (vv i) (vv ((i + 2) % 4)) ≤ Real.pi := by
    have hp := (hCLF.2 _ hdD).1
    rw [← periodic_mod_eq_p23 hper ((i + 3) % 4 + 1)] at hp
    rw [w2sg_azimInFan_eq vv hper hinj _ rfl ((i + 3) % 4) (by omega)] at hp
    rw [show (((i + 3) % 4 + 1) % 4 : ℕ) = i % 4 from by omega, periodic_mod_eq_p23 hper i,
      show (((i + 3) % 4 + 3) % 4 : ℕ) = (i + 2) % 4 from by omega] at hp
    exact hp
  have hncBW₂ := w2sg_fan6_ncol vv hper _ rfl hf.2.2.2.2.1 (k := (i + 1) % 4) (by omega)
  rw [show (((i + 1) % 4 + 1) % 4 : ℕ) = (i + 2) % 4 from by omega] at hncBW₂
  have hncW₂W₃ := w2sg_fan6_ncol vv hper _ rfl hf.2.2.2.2.1 (k := (i + 2) % 4) (by omega)
  rw [show (((i + 2) % 4 + 1) % 4 : ℕ) = (i + 3) % 4 from by omega] at hncW₂W₃
  have hncW₃A : ¬ Collinear3 0 (vv ((i + 3) % 4)) (vv i) := by
    have h := w2sg_fan6_ncol vv hper _ rfl hf.2.2.2.2.1 (k := (i + 3) % 4) (by omega)
    rw [show (((i + 3) % 4 + 1) % 4 : ℕ) = i % 4 from by omega, periodic_mod_eq_p23 hper i] at h
    exact h
  obtain ⟨hπ1, hπ2, hπ3⟩ := w2sg_wheel_core hν hμ hτ hsum hslot hncAB hncBW₂ hncW₂W₃
    hncW₃A hwAB hwBW₂ hwW₃A hpileAB hpileBW₂ hpileW₃A
  have hρfun : ∀ m : ℕ, m < 4 → (1:ℝ) ≤ rhoFun (norm (vv m)) := fun m hm =>
    w2sg_rhoFun_ge_one (w2sg_norm_ge_two s vv hBB m)
  have htau := w2sg_tau_ge vv hper hinj _ rfl i hi hπ1 hπ2 hπ3 hρfun
  have hdsv := w2sg_dsv_le s vv hs hk hBB
  have hta' : tauFun (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) - dsvV39 s vv < 0 := by
    have hta'' : taustarV39 s vv = tauFun (Set.range vv)
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) - dsvV39 s vv := by
      unfold taustarV39
      rw [if_neg (show ¬(s.k ≤ 3) from by omega)]
      have hc1 : (Set.range fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          = ((fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      have hc2 : (Set.range fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3))
          = ((fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      rw [hc1, hc2]
    rw [← hta'']
    exact hta
  linarith [htau, w2sg_sol0_le_pi_half, hdsv, hs.1, hta']

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

/-- HOL `JKQEWGV2_CASE_5` (JKQEWGV.hl:3027): discharged by the CircularSolKit
  engine (`circularAzimInFanPi_cs`, per-dart `azimInFan = π`) + the `w3sg_*` k=5
  final-computation kit (`2π − 4sol0 ≥ 4 > 0.9` vs `taustar < 0`). -/
theorem JKQEWGV2_CASE_5_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  intro hc
  have hper : Periodic vv 5 := hk ▸ hBB.2.1
  have hinj : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → vv i ≠ vv j :=
    fun i j hi5 hj5 hij =>
      w2sg_vv_inj s vv hs hBB (by rw [hk]; exact hi5) (by rw [hk]; exact hj5) hij
  have hCLF : ConvexLocalFan (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) := by
    rcases hBB.2.2.2 with hle | hcl
    · rw [hk] at hle; omega
    · have hconv1 : (Set.range fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          = ((fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      have hconv2 : (Set.range fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3))
          = ((fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      rw [hconv1, hconv2] at hcl
      exact hcl
  have hρfun : ∀ m : ℕ, (1:ℝ) ≤ rhoFun (norm (vv m)) := fun m =>
    w2sg_rhoFun_ge_one (w2sg_norm_ge_two s vv hBB m)
  have htau := w3sg_tau_ge5 vv hper hinj (circularAzimInFanPi_cs hCLF hc) hρfun
  have hdsv := w3sg_dsv_le s vv hs (by omega) hBB
  have hta' : tauFun (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) - dsvV39 s vv < 0 := by
    have hta'' : taustarV39 s vv = tauFun (Set.range vv)
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) - dsvV39 s vv := by
      unfold taustarV39
      rw [if_neg (show ¬(s.k ≤ 3) from by omega)]
      have hc1 : (Set.range fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          = ((fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      have hc2 : (Set.range fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3))
          = ((fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      rw [hc1, hc2]
    rw [← hta'']
    exact hta
  linarith [htau, w2sg_sol0_le_pi_half, hdsv, hs.1, hta']

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

/-- HOL `JKQEWGV2_CASE_6` (JKQEWGV.hl:3082): discharged by the CircularSolKit
  engine (`circularAzimInFanPi_cs`, per-dart `azimInFan = π`) + the `w3sg_*` k=6
  final-computation kit (`2π − 4sol0 ≥ 4 > 0.9` vs `taustar < 0`). -/
theorem JKQEWGV2_CASE_6_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 6) (hBB : BBsV39 s vv)
    (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  intro hc
  have hper : Periodic vv 6 := hk ▸ hBB.2.1
  have hinj : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → vv i ≠ vv j :=
    fun i j hi6 hj6 hij =>
      w2sg_vv_inj s vv hs hBB (by rw [hk]; exact hi6) (by rw [hk]; exact hj6) hij
  have hCLF : ConvexLocalFan (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) := by
    rcases hBB.2.2.2 with hle | hcl
    · rw [hk] at hle; omega
    · have hconv1 : (Set.range fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          = ((fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      have hconv2 : (Set.range fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3))
          = ((fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      rw [hconv1, hconv2] at hcl
      exact hcl
  have hρfun : ∀ m : ℕ, (1:ℝ) ≤ rhoFun (norm (vv m)) := fun m =>
    w2sg_rhoFun_ge_one (w2sg_norm_ge_two s vv hBB m)
  have htau := w3sg_tau_ge6 vv hper hinj (circularAzimInFanPi_cs hCLF hc) hρfun
  have hdsv := w3sg_dsv_le s vv hs (by omega) hBB
  have hta' : tauFun (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
      ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) - dsvV39 s vv < 0 := by
    have hta'' : taustarV39 s vv = tauFun (Set.range vv)
        ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)
        ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) - dsvV39 s vv := by
      unfold taustarV39
      rw [if_neg (show ¬(s.k ≤ 3) from by omega)]
      have hc1 : (Set.range fun i : ℕ => ({vv i, vv (i + 1)} : Set V3))
          = ((fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      have hc2 : (Set.range fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3))
          = ((fun i : ℕ => ((vv i, vv (i + 1)) : V3 × V3)) '' Set.univ) := by
        ext t; simp [Set.mem_range, Set.mem_image]
      rw [hc1, hc2]
    rw [← hta'']
    exact hta
  linarith [htau, w2sg_sol0_le_pi_half, hdsv, hs.1, hta']

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
circular. The case split `s.k ∈ {4,5,6}` (from `hs.2.1`/`hs.2.2.1` + `hk`) dispatches
  to the three real `JKQEWGV2_CASE_*_p23 theorems. -/
theorem JKQEWGV2_p23 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hk : 3 < s.k) (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0) :
    ¬ Circular (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
  have hle6 : s.k ≤ 6 := hs.2.2.1
  rcases (by omega : s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with h4 | h5 | h6
  · exact JKQEWGV2_CASE_4_p23 s vv hs h4 hBB hta
  · exact JKQEWGV2_CASE_5_p23 s vv hs h5 hBB hta
  · exact JKQEWGV2_CASE_6_p23 s vv hs h6 hBB hta

/-! ### W5b lane (scsgeneric-w5b1): the `JKQEWGV3` lunar-kit block

Private `w5sg3_*` pieces inserted before `JKQEWGV3_p23` (2026-10-28). The
proof of `JKQEWGV3_p23` below is the direct curvature route: the negative
`taustar` hypothesis is converted into `solLocal < 9/10 + 4·sol0 < π`
(no `JKQEWGV1` consumption), `HKIRPEP` identifies the two lunar interior
angles with half the solid angle, and the goal follows. -/

private theorem w5sg3_sin_pi_twelve : Real.sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2 : ℝ) / 4 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num) 3, show (2:ℝ) * 3 = 6 from by norm_num]
  have h : Real.pi / 12 = Real.pi / 3 - Real.pi / 4 := by linarith [Real.pi_pos]
  rw [h, Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three,
    Real.sin_pi_div_four, Real.cos_pi_div_four, h6]
  ring

/-- cos(π/12) = (√6 + √2)/4. -/
private theorem w5sg3_cos_pi_twelve : Real.cos (Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2 : ℝ) / 4 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num) 3, show (2:ℝ) * 3 = 6 from by norm_num]
  have h : Real.pi / 12 = Real.pi / 3 - Real.pi / 4 := by linarith [Real.pi_pos]
  rw [h, Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three,
    Real.cos_pi_div_four, Real.sin_pi_div_four, h6]
  ring

/-- `43√6 − 37√2 < 160/3`. -/
private theorem w5sg3_sqrt_key : 43 * Real.sqrt 6 - 37 * Real.sqrt 2 < 160 / 3 := by
  have s6 : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt (by positivity)
  have s2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by positivity)
  have m62 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 6 by norm_num) 2,
      show (6:ℝ) * 2 = 4 * 3 from by norm_num,
      Real.sqrt_mul (show (0:ℝ) ≤ 4 by norm_num) 3,
      show (Real.sqrt 4 : ℝ) = 2 from by
        rw [show (4:ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (show (0:ℝ) ≤ 2 by norm_num)]]
  have hexp : (43 * Real.sqrt 6 - 37 * Real.sqrt 2 : ℝ)^2
      = 13832 - 6364 * Real.sqrt 3 := by
    have he : (43 * Real.sqrt 6 - 37 * Real.sqrt 2 : ℝ)^2
        = 43^2 * (Real.sqrt 6)^2 + 37^2 * (Real.sqrt 2)^2
          - 2 * (43 * Real.sqrt 6) * (37 * Real.sqrt 2) := by ring
    rw [he, s6, s2]
    linear_combination (-(2 * 43 * 37)) * m62
  have h3 : (98888 / 57276 : ℝ) < Real.sqrt 3 := by
    have hsq : ((98888 / 57276 : ℝ))^2 < 3 := by norm_num
    have hpos : 0 ≤ (98888 / 57276 : ℝ) := by norm_num
    have h := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
    rwa [Real.sqrt_sq hpos] at h
  have hpos : 0 < 43 * Real.sqrt 6 - 37 * Real.sqrt 2 := by
    have hs37 : Real.sqrt (37 ^ 2) = 37 := Real.sqrt_sq (show (0:ℝ) ≤ 37 by norm_num)
    have hs43 : Real.sqrt (43 ^ 2) = 43 := Real.sqrt_sq (show (0:ℝ) ≤ 43 by norm_num)
    have h1 : Real.sqrt ((37:ℝ)^2 * 2) < Real.sqrt ((43:ℝ)^2 * 6) :=
      Real.sqrt_lt_sqrt (by positivity) (by norm_num)
    rw [Real.sqrt_mul (show (0:ℝ) ≤ (37:ℝ)^2 by norm_num) 2, hs37,
      Real.sqrt_mul (show (0:ℝ) ≤ (43:ℝ)^2 by norm_num) 6, hs43] at h1
    linarith
  have hsq : (43 * Real.sqrt 6 - 37 * Real.sqrt 2 : ℝ)^2 < (160/3 : ℝ)^2 := by
    rw [hexp]; linarith
  nlinarith [hpos]

/-- The arcsin lower bound: `π/12 + 3/40 < arcsin(1/3)`. -/
private theorem w5sg3_arcsin_third_gt : Real.pi / 12 + 3 / 40 < Real.arcsin (1 / 3 : ℝ) := by
  have htsin := w5sg3_sin_pi_twelve
  have htc := w5sg3_cos_pi_twelve
  have hkey := w5sg3_sqrt_key
  have hmain : (Real.sqrt 6 - Real.sqrt 2 : ℝ) / 4
      + (Real.sqrt 6 + Real.sqrt 2 : ℝ) / 4 * (3 / 40) < 1 / 3 := by linarith
  have hp0 : 0 ≤ Real.pi / 12 + 3 / 40 := by linarith [Real.pi_pos]
  have hp1 : Real.pi / 12 + 3 / 40 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsinpos : 0 ≤ Real.sin (Real.pi / 12 + 3 / 40) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hbound : Real.sin (Real.pi / 12 + 3 / 40) < 1 / 3 := by
    have hadd : Real.sin (Real.pi / 12 + 3 / 40)
        = Real.sin (Real.pi / 12) * Real.cos (3 / 40)
          + Real.cos (Real.pi / 12) * Real.sin (3 / 40) := Real.sin_add _ _
    have hc1 : Real.cos (3 / 40 : ℝ) ≤ 1 := Real.cos_le_one _
    have hs1 : Real.sin (3 / 40 : ℝ) ≤ 3 / 40 := le_of_lt (Real.sin_lt (by norm_num))
    have hsqpos : 0 ≤ (Real.sqrt 6 - Real.sqrt 2 : ℝ) / 4 := by
      have h2 : (Real.sqrt (2:ℝ)) < Real.sqrt 6 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith [Real.sqrt_nonneg 2]
    have hsqpos2 : 0 ≤ (Real.sqrt 6 + Real.sqrt 2 : ℝ) / 4 := by positivity
    have hp1' : (Real.sqrt 6 - Real.sqrt 2 : ℝ) / 4 * Real.cos (3 / 40)
        ≤ (Real.sqrt 6 - Real.sqrt 2 : ℝ) / 4 := by
      have h := mul_le_mul_of_nonneg_left hc1 hsqpos
      rwa [mul_one] at h
    have hp2' : (Real.sqrt 6 + Real.sqrt 2 : ℝ) / 4 * Real.sin (3 / 40)
        ≤ (Real.sqrt 6 + Real.sqrt 2 : ℝ) / 4 * (3 / 40) :=
      mul_le_mul_of_nonneg_left hs1 hsqpos2
    rw [hadd, htsin, htc]
    linarith
  have hneg : -(Real.pi / 2) ≤ Real.pi / 12 + 3 / 40 := by linarith [Real.pi_pos]
  have hlt := Real.arcsin_lt_arcsin (by linarith : (-1:ℝ) ≤ Real.sin (Real.pi / 12 + 3 / 40))
    hbound (by norm_num : (1 / 3 : ℝ) ≤ 1)
  rw [Real.arcsin_sin hneg hp1] at hlt
  linarith

/-- `9/10 + 4·sol0 < π`. -/
private theorem w5sg3_nine_add_4sol0_lt_pi : 9 / 10 + 4 * sol0 < Real.pi := by
  have harc := w5sg3_arcsin_third_gt
  have hsol : sol0 = 3 * (Real.pi / 2 - Real.arcsin (1/3 : ℝ)) - Real.pi := by
    unfold sol0
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  rw [hsol]
  linarith

private theorem w5sg3_vv_shift {α : Type*} {vv : ℕ → α} {k : ℕ} (hper : ∀ i, vv (i + k) = vv i) :
    ∀ m r : ℕ, vv (m * k + r) = vv r := by
  intro m
  induction m with
  | zero => intro r; simp
  | succ n ih =>
    intro r
    have he : (n + 1) * k + r = (n * k + r) + k := by ring
    rw [he, hper, ih r]

private theorem w5sg3_dart_mod {s : ScsV39} {vv : ℕ → V3} (hper : Periodic vv s.k) (i : ℕ) :
    (vv (i % s.k), vv (i % s.k + 1)) = (vv i, vv (i + 1)) := by
  have h1 := w5sg3_vv_shift (by intro j; exact hper j) (i / s.k) (i % s.k)
  have h2 := w5sg3_vv_shift (by intro j; exact hper j) (i / s.k) (i % s.k + 1)
  have hda : s.k * (i / s.k) + i % s.k = i := Nat.div_add_mod i s.k
  have heq : (i / s.k) * s.k + i % s.k = i := by rw [Nat.mul_comm]; omega
  have heq2 : (i / s.k) * s.k + (i % s.k + 1) = i + 1 := by rw [Nat.mul_comm]; omega
  have hv1 : vv i = vv (i % s.k) := (h1.symm.trans (by rw [heq])).symm
  have hv2 : vv (i + 1) = vv (i % s.k + 1) := (h2.symm.trans (by rw [heq2])).symm
  rw [hv1, hv2]

private theorem w5sg3_vv_inj {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s) (hBB : BBsV39 s vv)
    {i j : ℕ} (hi : i < s.k) (hj : j < s.k) (hne : i ≠ j) : vv i ≠ vv j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag, -, -, -, -, -⟩ := hs
  have hdist : s.a i j ≤ dist (vv i) (vv j) := (hBB.2.2.1 i j).1
  have h2 : (2:ℝ) ≤ s.a i j := hdiag i j ⟨hi, hj, hne⟩
  intro heq
  rw [heq, dist_self] at hdist
  linarith

private theorem w5sg3_dart_inj {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s) (hBB : BBsV39 s vv)
    {i j : ℕ} (hi : i < s.k) (hj : j < s.k)
    (heq : (vv i, vv (i + 1)) = (vv j, vv (j + 1))) : i = j := by
  simp only [Prod.mk.injEq] at heq
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd heq.1 (w5sg3_vv_inj hs hBB hi hj (by omega))
  · exact h
  · exact absurd heq.1.symm (w5sg3_vv_inj hs hBB hj hi (by omega))

private theorem w5sg3_F_ncard {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s) (hBB : BBsV39 s vv) :
    Set.ncard (Set.range fun i : ℕ => (vv i, vv (i + 1))) = s.k := by
  have hk3 : 3 ≤ s.k := hs.2.1
  refine Set.ncard_eq_of_bijective (fun i (_ : i < s.k) => (vv i, vv (i + 1)))
    (fun d hd => ?_) (fun i hi => ⟨i, rfl⟩) (fun i j hi hj heq => w5sg3_dart_inj hs hBB hi hj heq)
  · obtain ⟨i, rfl⟩ := hd
    exact ⟨i % s.k, Nat.mod_lt i (by omega), w5sg3_dart_mod hBB.2.1 i⟩

private theorem w5sg3_setSum_F {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s) (hBB : BBsV39 s vv)
    (hfinFF : (Set.range fun i : ℕ => (vv i, vv (i + 1))).Finite)
    (E : Set (Set V3)) (g : V3 × V3 → ℝ) :
    setSum (Set.range fun i : ℕ => (vv i, vv (i + 1))) g
      = ∑ i ∈ Finset.range s.k, g (vv i, vv (i + 1)) := by
  have hk3 : 3 ≤ s.k := hs.2.1
  rw [setSum, dif_pos hfinFF]
  have himg : hfinFF.toFinset = Finset.image (fun i : ℕ => (vv i, vv (i + 1)))
      (Finset.range s.k) := by
    ext d
    rw [Set.Finite.mem_toFinset]
    simp only [Finset.mem_image, Set.mem_range, Finset.mem_range]
    refine ⟨fun hd => ?_, fun ⟨i, hi, hd'⟩ => ⟨i, hd'⟩⟩
    obtain ⟨i, rfl⟩ := hd
    have hm : i % s.k < s.k := Nat.mod_lt i (by omega)
    exact ⟨i % s.k, hm, w5sg3_dart_mod hBB.2.1 i⟩
  rw [himg, Finset.sum_image]
  intro i hi j hj heq
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  simp only [] at heq
  exact w5sg3_dart_inj hs hBB hi hj heq

private theorem w5sg3_sum_pi {f : ℕ → ℝ} {k : ℕ} :
    (∑ i ∈ Finset.range k, (f i - Real.pi))
      = (∑ i ∈ Finset.range k, f i) - Real.pi * k := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

private theorem w5sg3_azimInFan_nonneg (d : V3 × V3) (E : Set (Set V3)) :
    0 ≤ azimInFan d E := by
  unfold azimInFan
  split_ifs
  · exact azim_nonneg 0 d.1 d.2 _
  · positivity

private theorem w5sg3_hedge {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E) ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

private theorem w5sg3_ffSubDart {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : localFan_p2 V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    FF ⊆ Fan.dart1OfFan V E := by
  obtain ⟨H, hd, -, -, -, -, hface, -⟩ := hlf
  obtain ⟨z, hzd, hFF⟩ := hface
  intro d hdF
  have hsub := H.face_subset_darts hzd (hFF ▸ hdF)
  rw [hd] at hsub
  exact (hno_p2_of_no_isolated hedge) ▸ hsub

private theorem w5sg3_ffFinite {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : localFan_p2 V E FF) : FF.Finite := by
  have h1 := LOCAL_FAN_RHO_NODE_PROS hlf
  have hV := LOCAL_FAN_FINITE_V hlf
  have hsub : FF ⊆ (fun v : V3 => (v, rhoNode1_p2 FF v)) '' V := by
    intro d hd
    have hinV := LOCAL_FAN_IMP_IN_V hlf hd hd
    rw [h1.2 d hd]
    exact ⟨d.1, hinV.1, rfl⟩
  exact (hV.image fun v : V3 => (v, rhoNode1_p2 FF v)).subset hsub

private theorem w5sg3_clf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf (w5sg3_hedge h2reg)
  have hsub := w5sg3_ffSubDart hlf2 (w5sg3_hedge h2reg)
  refine ⟨hlf2, ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · have hb : azimInFan d E = azimInFan_p3 d E :=
      azimInFan_eq_azimInFan_p3 hfan (hsub hd)
    show azimInFan_p2 d E ≤ Real.pi
    rw [show azimInFan_p2 d E = azimInFan_p3 d E from rfl, ← hb]
    exact (hcvx d hd).1
  · show V ⊆ wedgeInFanGe_p2 d E
    rw [show wedgeInFanGe_p2 d E = wedgeInFanGe_p3 d E from rfl,
      ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfan (hsub hd)]
    exact (hcvx d hd).2

private theorem w5sg3_azimInFan_p2 {V : Set V3} {E : Set (Set V3)} {F : Set (V3 × V3)}
    (hclf : ConvexLocalFan V E F) {d : V3 × V3} (hd : d ∈ F) :
    azimInFan d E = azimInFan_p2 d E := by
  have hcopy := hclf.1
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  have hsub := w5sg3_ffSubDart (w5sg3_clf2 hclf).1 (w5sg3_hedge h2reg)
  rw [azimInFan_eq_azimInFan_p3 hfan (hsub hd)]
  rfl

private theorem w5sg3_solLocal_eq_p9 {V : Set V3} {E : Set (Set V3)} {F : Set (V3 × V3)}
    (hclf : ConvexLocalFan V E F) (hfinFF : F.Finite) :
    solLocal E F = solLocal_p9 E F := by
  show 2 * Real.pi + setSum F (fun d => azimInFan d E - Real.pi)
      = 2 * Real.pi + setSum F (fun d => azimInFan_p2 d E - Real.pi)
  have h1 : setSum F (fun d => azimInFan d E - Real.pi)
      = setSum F (fun d => azimInFan_p2 d E - Real.pi) := by
    simp only [setSum, dif_pos hfinFF]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [w5sg3_azimInFan_p2 hclf ((Set.Finite.mem_toFinset hfinFF).mp hd)]
  rw [h1]

/-- The curvature core: negative taustar gives `solLocal < 9/10 + 4·sol0`
(direct route, no `JKQEWGV1`). -/
private theorem w5sg3_solLocal_lt {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
    (hBB : BBsV39 s vv) (hk : 3 < s.k)
    (hta : tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)})
        (Set.range fun i : ℕ => (vv i, vv (i + 1))) - dsvV39 s vv < 0)
    (hfinFF : (Set.range fun i : ℕ => (vv i, vv (i + 1))).Finite) :
    solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)})
        (Set.range fun i : ℕ => (vv i, vv (i + 1))) < 9 / 10 + 4 * sol0 := by
  have hsd := hs.1
  have hk6 := hs.2.2.1
  have hdsv := w3sg_dsv_le s vv hs hk hBB
  have hcard0 := w5sg3_F_ncard hs hBB
  have hsol : solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) = 2 * Real.pi + setSum (Set.range fun i : ℕ => (vv i, vv (i + 1))) (fun d => azimInFan d (Set.range fun i : ℕ => {vv i, vv (i + 1)}) - Real.pi) := rfl
  have htaufun : tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1)))
      = setSum (Set.range fun i : ℕ => (vv i, vv (i + 1))) (fun d => rhoFun (norm d.1) * azimInFan d (Set.range fun i : ℕ => {vv i, vv (i + 1)}))
        - (Real.pi + sol0) * (((Set.range fun i : ℕ => (vv i, vv (i + 1))).ncard - 2 : ℕ) : ℝ) := rfl
  have hsum1 := w5sg3_setSum_F hs hBB hfinFF (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (fun d => rhoFun (norm d.1) * azimInFan d (Set.range fun i : ℕ => {vv i, vv (i + 1)}))
  have hsum2 := w5sg3_setSum_F hs hBB hfinFF (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (fun d => azimInFan d (Set.range fun i : ℕ => {vv i, vv (i + 1)}))
  have h1 := w5sg3_setSum_F hs hBB hfinFF (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (fun d => azimInFan d (Set.range fun i : ℕ => {vv i, vv (i + 1)}) - Real.pi)
  have hρ : ∀ i : ℕ, azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      ≤ rhoFun (norm (vv i, vv (i + 1)).1) * azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) := by
    intro i
    have h2 : (2:ℝ) ≤ norm (vv i, vv (i + 1)).1 := w2sg_norm_ge_two s vv hBB i
    have hρ1 := w2sg_rhoFun_ge_one h2
    have haz : 0 ≤ azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) := w5sg3_azimInFan_nonneg _ (Set.range fun i : ℕ => {vv i, vv (i + 1)})
    calc azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)})
        = azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) * 1 := (mul_one _).symm
      _ ≤ azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) * rhoFun (norm (vv i, vv (i + 1)).1) :=
          mul_le_mul_of_nonneg_left hρ1 haz
      _ = rhoFun (norm (vv i, vv (i + 1)).1) * azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) := mul_comm _ _
  have hSum : ∑ i ∈ Finset.range s.k, azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      ≤ ∑ i ∈ Finset.range s.k, rhoFun (norm (vv i, vv (i + 1)).1) * azimInFan (vv i, vv (i + 1)) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) :=
    by refine Finset.sum_le_sum fun i _ => ?_; exact hρ i
  rcases (by omega : s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with hkc | hkc | hkc
  · rw [hkc] at hsum1 hsum2 h1 hSum hcard0
    rw [w5sg3_sum_pi] at h1
    norm_num at h1
    have hcast : (((Set.range fun i : ℕ => (vv i, vv (i + 1))).ncard - 2 : ℕ) : ℝ) = 2 := by rw [hcard0]; norm_num
    have htauge : solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) - 2 * sol0 ≤ tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
      rw [htaufun, hcast]
      linarith [hsum1, hSum, hsum2, h1, hsol]
    linarith [htauge, hta, hdsv, hsd, w5sg3_nine_add_4sol0_lt_pi, w2sg_sol0_nonneg]
  · rw [hkc] at hsum1 hsum2 h1 hSum hcard0
    rw [w5sg3_sum_pi] at h1
    norm_num at h1
    have hcast : (((Set.range fun i : ℕ => (vv i, vv (i + 1))).ncard - 2 : ℕ) : ℝ) = 3 := by rw [hcard0]; norm_num
    have htauge : solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) - 3 * sol0 ≤ tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
      rw [htaufun, hcast]
      linarith [hsum1, hSum, hsum2, h1, hsol]
    linarith [htauge, hta, hdsv, hsd, w5sg3_nine_add_4sol0_lt_pi, w2sg_sol0_nonneg]
  · rw [hkc] at hsum1 hsum2 h1 hSum hcard0
    rw [w5sg3_sum_pi] at h1
    norm_num at h1
    have hcast : (((Set.range fun i : ℕ => (vv i, vv (i + 1))).ncard - 2 : ℕ) : ℝ) = 4 := by rw [hcard0]; norm_num
    have htauge : solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) - 4 * sol0 ≤ tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)}) (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
      rw [htaufun, hcast]
      linarith [hsum1, hSum, hsum2, h1, hsol]
    linarith [htauge, hta, hdsv, hsd, w5sg3_nine_add_4sol0_lt_pi]

/-- The full JKQEWGV3-style body (probe). -/
example (s : ScsV39) (vv : ℕ → V3) (v w : V3)
    (hs : isScsV39 s) (hBB : BBsV39 s vv) (hk : 3 < s.k)
    (hta : taustarV39 s vv < 0)
    (hl : Lunar v w (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ)) :
    interiorAngle1 0 ((fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) v <
      Real.pi / 2 := by
  rw [Set.image_univ] at hl ⊢
  obtain ⟨hann, hper, hdist, h4⟩ := hBB
  rcases h4 with hkle3 | hclf
  · omega
  have hk' : ¬(s.k ≤ 3) := by omega
  have hclf2 := w5sg3_clf2 hclf
  have hlp2 : lunar_p2 v w (Set.range vv)
      (Set.range fun i : ℕ => {vv i, vv (i + 1)}) := hl
  obtain ⟨hflat, -, -, hveq, -, -⟩ := HKIRPEP hclf2 hlp2
  have hfinFF : (Set.range fun i : ℕ => (vv i, vv (i + 1))).Finite :=
    w5sg3_ffFinite hclf2.1
  have hfinV : (Set.range vv).Finite := LOCAL_FAN_FINITE_V hclf2.1
  have hta' : tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1))) - dsvV39 s vv < 0 := by
    have h := hta
    rw [taustarV39, if_neg hk'] at h
    exact h
  have hfinal : solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1))) < 9 / 10 + 4 * sol0 :=
    w5sg3_solLocal_lt hs ⟨hann, hper, hdist, Or.inr hclf⟩ hk hta' hfinFF
  have hsoleq := w5sg3_solLocal_eq_p9 hclf hfinFF
  have hlofa := SOL_LOFA_EQ_SUM_INANGLE_p9 hclf2
  have hvV : v ∈ Set.range vv := hl.2.1 (by simp)
  have hwV : w ∈ Set.range vv := hl.2.1 (by simp)
  have hVsum : setSum (Set.range vv)
      (fun u => interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) u - Real.pi)
      = interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
        + interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) w - 2 * Real.pi := by
    rw [setSum, dif_pos hfinV]
    have hvS : v ∈ hfinV.toFinset := (Set.Finite.mem_toFinset hfinV).mpr hvV
    have hwS : w ∈ hfinV.toFinset := (Set.Finite.mem_toFinset hfinV).mpr hwV
    have hvwne : v ≠ w := hl.2.2.1
    rw [← Finset.insert_erase hwS, Finset.sum_insert (Finset.notMem_erase w hfinV.toFinset)]
    have hvS' : v ∈ hfinV.toFinset.erase w := Finset.mem_erase.mpr ⟨hvwne, hvS⟩
    rw [← Finset.insert_erase hvS',
      Finset.sum_insert (Finset.notMem_erase v (hfinV.toFinset.erase w))]
    have hz : ∑ x ∈ (hfinV.toFinset.erase w).erase v,
        (interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) x - Real.pi) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨hnv, hxw⟩ := Finset.mem_erase.mp hx
      obtain ⟨hnw, hxS⟩ := Finset.mem_erase.mp hxw
      have hxS' : x ∈ Set.range vv := (Set.Finite.mem_toFinset hfinV).mp hxS
      have hsd' : x ∈ Set.range vv \ {v, w} := by
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨hxS', by tauto⟩
      rw [hflat x hsd']
      ring
    rw [hz, add_zero]
    ring
  have h9 : solLocal_p9 (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1)))
      = interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
        + interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) w := by
    rw [hlofa, hVsum]; ring
  have hintv : interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
      < Real.pi / 2 := by
    have h2v : 2 * interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
        = solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)})
          (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
      rw [hsoleq, h9, ← hveq]; ring
    linarith [h2v, hfinal, w5sg3_nine_add_4sol0_lt_pi]
  rw [show interiorAngle1 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
      = interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v from rfl]
  exact hintv

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
  rw [Set.image_univ] at hl ⊢
  obtain ⟨hann, hper, hdist, h4⟩ := hBB
  rcases h4 with hkle3 | hclf
  · omega
  have hk' : ¬(s.k ≤ 3) := by omega
  have hclf2 := w5sg3_clf2 hclf
  have hlp2 : lunar_p2 v w (Set.range vv)
      (Set.range fun i : ℕ => {vv i, vv (i + 1)}) := hl
  obtain ⟨hflat, -, -, hveq, -, -⟩ := HKIRPEP hclf2 hlp2
  have hfinFF : (Set.range fun i : ℕ => (vv i, vv (i + 1))).Finite :=
    w5sg3_ffFinite hclf2.1
  have hfinV : (Set.range vv).Finite := LOCAL_FAN_FINITE_V hclf2.1
  have hta' : tauFun (Set.range vv) (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1))) - dsvV39 s vv < 0 := by
    have h := hta
    rw [taustarV39, if_neg hk'] at h
    exact h
  have hfinal : solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1))) < 9 / 10 + 4 * sol0 :=
    w5sg3_solLocal_lt hs ⟨hann, hper, hdist, Or.inr hclf⟩ hk hta' hfinFF
  have hsoleq := w5sg3_solLocal_eq_p9 hclf hfinFF
  have hlofa := SOL_LOFA_EQ_SUM_INANGLE_p9 hclf2
  have hvV : v ∈ Set.range vv := hl.2.1 (by simp)
  have hwV : w ∈ Set.range vv := hl.2.1 (by simp)
  have hVsum : setSum (Set.range vv)
      (fun u => interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) u - Real.pi)
      = interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
        + interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) w - 2 * Real.pi := by
    rw [setSum, dif_pos hfinV]
    have hvS : v ∈ hfinV.toFinset := (Set.Finite.mem_toFinset hfinV).mpr hvV
    have hwS : w ∈ hfinV.toFinset := (Set.Finite.mem_toFinset hfinV).mpr hwV
    have hvwne : v ≠ w := hl.2.2.1
    rw [← Finset.insert_erase hwS, Finset.sum_insert (Finset.notMem_erase w hfinV.toFinset)]
    have hvS' : v ∈ hfinV.toFinset.erase w := Finset.mem_erase.mpr ⟨hvwne, hvS⟩
    rw [← Finset.insert_erase hvS',
      Finset.sum_insert (Finset.notMem_erase v (hfinV.toFinset.erase w))]
    have hz : ∑ x ∈ (hfinV.toFinset.erase w).erase v,
        (interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) x - Real.pi) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨hnv, hxw⟩ := Finset.mem_erase.mp hx
      obtain ⟨hnw, hxS⟩ := Finset.mem_erase.mp hxw
      have hxS' : x ∈ Set.range vv := (Set.Finite.mem_toFinset hfinV).mp hxS
      have hsd' : x ∈ Set.range vv \ {v, w} := by
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨hxS', by tauto⟩
      rw [hflat x hsd']
      ring
    rw [hz, add_zero]
    ring
  have h9 : solLocal_p9 (Set.range fun i : ℕ => {vv i, vv (i + 1)})
      (Set.range fun i : ℕ => (vv i, vv (i + 1)))
      = interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
        + interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) w := by
    rw [hlofa, hVsum]; ring
  have hintv : interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
      < Real.pi / 2 := by
    have h2v : 2 * interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
        = solLocal (Set.range fun i : ℕ => {vv i, vv (i + 1)})
          (Set.range fun i : ℕ => (vv i, vv (i + 1))) := by
      rw [hsoleq, h9, ← hveq]; ring
    linarith [h2v, hfinal, w5sg3_nine_add_4sol0_lt_pi]
  rw [show interiorAngle1 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v
      = interiorAngle1_p2 0 (Set.range fun i : ℕ => (vv i, vv (i + 1))) v from rfl]
  exact hintv

end Kepler.Text

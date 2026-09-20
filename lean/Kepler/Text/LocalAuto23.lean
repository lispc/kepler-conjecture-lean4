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
  Section 0 (`_p23` substrate; see ENCODING): `deltaX4_p23`, `deltaY_p23`,
    `dihY_p23`, `taum_p23` (registry signature), `torsor_p23`,
    `constraintSystem_p23`, `stableSystem_p23`, `StableSyP23`,
    `aEar0_p23`, `bEar0_p23`, `earSy_p23`, `rowSy_p23`, `J1_SY_p23`,
    `dFun_p23`, `tauStar_p23`, `cycRow_p23` (the HOL row vector
    `vector[vv 1;..;vv k;vv 0]` read 0-based), `scsJSet_p23`
    (`change_type_v2 (scs_J_v39 s) k`), `scsToStableSy_p23` (the
    `stable_sy (...) = s1` record), `ballAnnulus_ne_0_p23`,
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
    the fatal `atn2PA18` duplication (LocalAuto2/9/11 and PackingAuto20 are
    NOT imported; LocalAuto19-27 same-wave lanes are NOT imported). The
    scs record (`ScsV39`, `isScsV39`, `BBsV39`, `taustarV39`, `MMsV39`,
    `scsArrowV39`, the `scs_*I*/T*/M*` registry, `scsStabDiagV39`) and
    `main_nonlinear_terminal_v11` come from LocalAuto1; the dih2k matrix
    substrate (`FinVec`, `vecmats_p4`, `vecmatsV3_p4`, `matvec_p4`,
    `V_SY_p4`/`E_SY_p4`/`F_SY_p4`, `CONDITION*_SY_p4`) from LocalAuto4
    (via its import). The LocalAuto8 stable-system kit (`torsor`,
    `constraint_system`, `stable_system`, `stable_sy`, `a_ear0`, `b_ear0`,
    `ear_sy`, `J1_SY`, `d_fun`, `tau_star`), the LocalAuto16 `taum`
    registry signature and the LocalAuto18 `delta_y`/`dih_y` bodies are
    NOT importable next to LocalAuto1 (no oleans / parallel lanes) and
    are carried as verbatim `_p23` twins with NEEDS merge markers.
  - HOL `real^3^M` / `dimindex(:M)=k` / `vector[...]` bookkeeping is
    replaced by the 0-based row function `cycRow_p23 vv k = fun i =>
    vv ((i+1) % k)`; HOL `matvec v = a` hypotheses are absorbed (the
    flattening `vecmats_p4 (cycRow_p23 vv k)` plays the role of `a`).
  - HOL `change_type_v3` is the identity on `ℕ → ℕ → ℝ` functions and is
    dropped; HOL `change_type_v2 (scs_J_v39 s) k` is `scsJSet_p23 s`.
  - HOL `stable_sy`/`stable_system` dummy field `d` (unused in dih2k.hl)
    is carried as `0` in `scsToStableSy_p23` / the `stableSystem_p23`
    calls (LocalAuto8 typed it `ℕ`).
  - HOL `dist(x,y)` ↦ `dist x y`; `norm x` ↦ `norm x`; `vec 0` ↦ `0`;
    `collinear` ↦ `Collinear ℝ`; `interior_angle1` ↦ `interiorAngle1`;
    `sol_local` ↦ `solLocal`; `circular` ↦ `Circular`; `lunar` ↦ `Lunar`;
    `taustar_v39 s vv < &0` ↦ `taustarV39 s vv < 0`; `xrr`/`cstab`/`h0`
    are LocalAuto1/`PackingAuto2` ports.
  - DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
    kit; proved items are mechanical (mod arithmetic, image bookkeeping,
    ball-annulus nontriviality, Mathlib compactness).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p23` substrate -/

/-- HOL `delta_x4` (sphere.hl:110): partial derivative of `delta_x` at
`x4`. Verbatim twin of PackingAuto20 `deltaX4f` / LocalAuto18
`deltaX4_p18` / LocalAuto16 `deltaX4f_p16`. NEEDS: merge. -/
noncomputable def deltaX4_p23 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `delta_y` (sphere.hl): `delta_x` at squared lengths. Verbatim twin
of LocalAuto11 `deltaY_p11` / LocalAuto18 `deltaY_p18`. NEEDS: merge. -/
noncomputable def deltaY_p23 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `dih_y` (sphere.hl:159). Verbatim twin of LocalAuto11
`dihY_p11` / LocalAuto18 `dihY_p18`. NEEDS: merge. -/
noncomputable def dihY_p23 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  Real.pi / 2 + atn2PA18
    (Real.sqrt (4 * (y1 * y1) *
      deltaXPA18 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
    (-(deltaX4_p23 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6)))

/-- NEEDS: HOL `taum` (Terminal.hl); opaque registry signature (twin of
LocalAuto11 `taum_p11` / LocalAuto16 `taum_p23`, which are on lanes not
importable next to LocalAuto1). -/
noncomputable def taum_p23 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

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

/-- The `stable_sy ((k),(d),(0..k-1),(a),(b),(J),(\i. (1+i) MOD k)) = s1`
record of the JKQEWGV hypotheses, built from `s`. The `stable` field is the
`IS_SCS_STABLE_SYSTEM_p23` unpacking (NEEDS). The unused dih2k dummy `d`
is carried as `0` (LocalAuto8 `StableSy.d : ℕ`). -/
noncomputable def scsToStableSy_p23 (s : ScsV39) : StableSyP23 where
  k := s.k
  d := 0
  I := Set.Iic (s.k - 1)
  a := s.a
  b := s.b
  J := scsJSet_p23 s
  f := fun i => (1 + i) % s.k
  stable := sorry -- NEEDS: IS_SCS_STABLE_SYSTEM_p23 (torsor over Iic (k-1))

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
      taum_p23 y1 y2 y3 y4' y5 y6 ≤ taum_p23 y1 y2 y3 y4 y5 y6 := by
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
      taum_p23 y1 y2 y3 y4' y5 y6 ≤ taum_p23 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `TAUM_STD_POS` (JOTSWIX.hl:108): `taum ≥ 0` on the box. NEEDS:
`TAUM_EXTREMAL_p23`, the terminal registry entries `5541487347` /
`OMKYNLT 3336871894` and `taum_sym2`. -/
theorem TAUM_STD_POS_p23 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2 * h0) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * h0)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * h0) :
    0 ≤ taum_p23 y1 y2 y3 y4 y5 y6 := by
  sorry

/-- HOL `LFLACKU` (JOTSWIX.hl:191): `scs_arrow_v39 {scs_3I1} {}`. NEEDS:
the `taustar_taum_dfun` / `FUNLIST_EXPLICIT` bridge (Terminal lane) to
reduce `MMsV39 scs3I1 = ∅` to `TAUM_STD_POS_p23`. -/
theorem LFLACKU_p23 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs3I1} ∅ := by
  sorry

/-- HOL `s_init_list_alt` (JOTSWIX.hl:216): the init list spelled out.
NEEDS (for the `5I3`/`4I3` entries): the `a_pro` ↔ `funlist_v39`
periodic-2 mod reduction (HOL proof JOTSWIX.hl:241-257; the first six
entries are `rfl`). -/
theorem s_init_list_alt_p23 :
    sInitListV39 =
      [scs6I1, scs5I1, scs4I1, scs3I1, scs5I2, scs4I2, scs5I3, scs4I3] := by
  sorry

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
    dihY_p23 y1 y2 y3 y4 y5 y6 < 1.1 ∨ deltaY_p23 y1 y2 y3 y4 y5 y6 < 0 := by
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

/-- HOL `IS_SCS_STABLE_SYSTEM` (JKQEWGV.hl:65): an scs with `k > 3` is a
stable system on `0..k-1` with successor cycling. NEEDS: the `isScsV39`
unpacking — the `torsor` cycle facts for `f = (1 + ·) % k` at k = 4,5,6
(HOL proof JKQEWGV.hl:73-409, `POWER_MOD_FUN`-driven). -/
theorem IS_SCS_STABLE_SYSTEM_p23 (s : ScsV39) (hs : isScsV39 s) (hk : 3 < s.k) :
    stableSystem_p23 s.k 0 (Set.Iic (s.k - 1)) s.a s.b (scsJSet_p23 s)
      (fun i => (1 + i) % s.k) := by
  sorry

/-- HOL `IS_SCS_TRI_STABLE_SYSTEM` (JKQEWGV.hl:409): the `k = 3` twin.
NEEDS: same torsor unpacking at k = 3. -/
theorem IS_SCS_TRI_STABLE_SYSTEM_p23 (s : ScsV39) (hs : isScsV39 s)
    (hk : s.k = 3) :
    triStable_p23 s.k 0 (Set.Iic (s.k - 1)) s.a s.b (scsJSet_p23 s)
      (fun i => (1 + i) % s.k) := by
  sorry

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

/-- HOL `V_E_FF_IS_SCS_CASES_4` (JKQEWGV.hl:739): the V/E/F sets of the
k=4 row vector identify with the periodic images of `vv`. NEEDS: image
bookkeeping over `cycRow_p23` (HOL `VECTOR_3_4`); twin of
`V_E_FF_IS_SCS_CASES_3_p23` below. -/
theorem V_E_FF_IS_SCS_CASES_4_p23 (s : ScsV39) (vv : ℕ → V3)
    (hs : isScsV39 s) (hk : s.k = 4) (hBB : BBsV39 s vv) :
    V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
    E_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
    F_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ := by
  sorry

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
    (hs1 : scsToStableSy_p23 s = s1) :
    taustarV39 s vv = tauStar_p23 s1 (flattenRow_p23 vv 4) := by
  sorry

/-- HOL `IS_EAR_V25_EQ_EAR_SY` (JKQEWGV.hl:935). NEEDS:
`stable_sy_explicit` + `is_ear_v39`/`ear_sy` unfolding. -/
theorem IS_EAR_V25_EQ_EAR_SY_p23 (s : ScsV39) (hs : isScsV39 s) (hk : 3 < s.k)
    (s1 : StableSyP23) (hs1 : scsToStableSy_p23 s = s1) :
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
  sorry

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
    (hs1 : scsToStableSy_p23 s = s1) :
    taustarV39 s vv = tauStar_p23 s1 (flattenRow_p23 vv 5) := by
  sorry

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
  sorry

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
    (hs1 : scsToStableSy_p23 s = s1) :
    taustarV39 s vv = tauStar_p23 s1 (flattenRow_p23 vv 6) := by
  sorry

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

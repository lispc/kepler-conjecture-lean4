/-
LocalAuto26 — Local Fan chapter appendix leftovers, four-file bundle
(skeleton-first pass):

  - `scripts/local/RRCWNSJ.hl` (878 ln, 8 thms; H. L. Truong 2012) — the
    `BB_VV_FUN_EQ` / `WL_IN_E` / `LUNAR_IN_V` folio used by the terminal
    nonlinear argument, the `B_LE_2h0_A_EQ2_IN_CASES_6` /
    `J_EMPY_CASES_6` k=6 arithmetic kit, `BB_RHO_NODE_IVS`, `BB_F_SUC_PRE`
    and the main `RRCWNSJ` (`main_nonlinear_terminal_v11 ==> generic`).
  - `scripts/local/AXJRPNC.hl` (1058 ln, 9 thms) — the `DIST_LE_2h0_IN_CASES_6`
    / `DIST_EDGE_IN_BB_LE_2` / `is_scs_k_le_3` / `NORM_V_IN_BB_LE_CSTAB`
    scs bound kit, the `arclength222h0` / `arclength_2h0_cstab` numeric
    lemmas, the pentagon / quadrilateral `DIST_LE2_BB_CASSE_4/5`, and the
    main `AXJRPNC` (a lunar pair in `MMs` is the k=6 switch with
    `v j = v (i+3)`).
  - `scripts/local/PPBTYDQ.hl` (614 ln, 15 thms) — `PPBTYDQ` / `OIQKKEP`
    geometry lemmas, the `MXQTIED` monotonic-permutation family
    (`MXQTIED`, `MXQTIED_PRIME2`, `MXQTIED_PRIME`, `MXQTIED_TAU`,
    `MXQTIED_TAU_DSV`, `MXQTIED_BB`, `MXQTIED_INDEX`, `BBPRIME_IMP_BB`),
    `SCS_BASIC_DSV` / `SCS_BASIC_TAUSTAR` / `TAUSTAR_LE_0_XWNHLMD` and
    `XWNHLMD_MM` / `XWNHLMD`.
  - `scripts/local/GBYCPXS.hl` (690 ln, 12 thms) — the `stable_sy` fan
    bounds: `CARD_F_SY_IN_B_SY`, `SOL0_POS`, `SIGMA_SY_LE1`,
    `B_SY_LE_CSTAB`, `PROPERTIES_EAR_SY`, `SING_J1_SY`, `D_FUN_LE`,
    `TAU_FUN_LE`, `TAU_STAR_POS`, `CIRCULAR_SOL_EQ_2PI`,
    `NOT_CIRCULAR_SY`, `GBYCPXS`.

FILE MAP
  Section 0 (`_p26` helpers): `periodic2_mod_eq_p26` (two-index periodic
    reduction, used by every `CHANGE_*_SCS_MOD` step), `succ_mod_ne_p26`
    (adjacent indices are distinct mod `k`), `sigmaSy_p26` / `aSyRow_p26`
    / `bSyRow_p26` (the GBYCPXS `sigma_sy` / 1-based row lifts feeding
    `B_SY1_p4`).
  Section A (RRCWNSJ): `BB_VV_FUN_EQ_p26`, `WL_IN_E_p26`,
    `LUNAR_IN_V_p26`, `B_LE_2h0_A_EQ2_IN_CASES_6_p26`,
    `J_EMPY_CASES_6_p26`, `BB_RHO_NODE_IVS_p26`, `BB_F_SUC_PRE_p26`,
    `RRCWNSJ_p26` (with the `w5sg_*` / `w5sg3b_*` prep blocks inserted before it).
  Section B (AXJRPNC): `DIST_LE_2h0_IN_CASES_6_p26`,
    `DIST_EDGE_IN_BB_LE_2_p26`, `arclength222h0_p26`,
    `is_scs_k_le_3_p26`, `DIST_LE2_BB_CASSE_4_p26`,
    `NORM_V_IN_BB_LE_CSTAB_p26`, `arclength_2h0_cstab_p26`,
    `DIST_LE2_BB_CASSE_5_p26`, `AXJRPNC_p26`.
  Section C (PPBTYDQ): `PPBTYDQ_p26`, `OIQKKEP_p26`, `MXQTIED_p26`,
    `MXQTIED_PRIME2_p26`, `MXQTIED_PRIME_p26`, `MXQTIED_TAU_p26`,
    `MXQTIED_TAU_DSV_p26`, `MXQTIED_BB_p26`, `MXQTIED_INDEX_p26`,
    `BBPRIME_IMP_BB_p26`, `SCS_BASIC_DSV_p26`, `SCS_BASIC_TAUSTAR_p26`,
    `TAUSTAR_LE_0_XWNHLMD_p26`, `XWNHLMD_MM_p26`, `XWNHLMD_p26`.
  Section D (GBYCPXS): `CARD_F_SY_IN_B_SY_p26`, `SOL0_POS_p26`,
    `SIGMA_SY_LE1_p26`, `B_SY_LE_CSTAB_p26`, `PROPERTIES_EAR_SY_p26`,
    `SING_J1_SY_p26`, `D_FUN_LE_p26`, `TAU_FUN_LE_p26`,
    `TAU_STAR_POS_p26`, `CIRCULAR_SOL_EQ_2PI_p26`,
    `NOT_CIRCULAR_SY_p26`, `GBYCPXS_p26`.

ENCODING NOTES
  - Import discipline: this file sits entirely on the LocalAuto1 side
    (LocalAuto2/9/11 and PackingAuto20 are NOT imported; LocalAuto19-27
    same-wave lanes are NOT imported).  The historic "fatal `atn2PA18`
    duplication" is resolved: atn2-merge wave 3 single-sourced `atn2` into
    `SphereKit`, the clash does not exist and the trees coexist
    (la35-access-recon-w1 ruling, 2026-10-28); the non-imports are now lane
    discipline, not a blocker. The
    scs record (`ScsV39`, `isScsV39`, `BBsV39`, `taustarV39`, `MMsV39`,
    `BBprimeV39`/`BBprime2V39`/`BBindexV39`, `dsvV39`, `scsBasicV39`,
    `scsM`, `scsArrowV39`, `scsDiag`, `scsGeneric`,
    `main_nonlinear_terminal_v11`), the local-fan kit (`Lunar`,
    `Circular`, `Generic`, `solLocal`, `ConvexLocalFan`,
    `rhoNode1`/`ivsRhoNode1`) and the `sol0`/`h0`/`cstab` constants come
    from LocalAuto1; the dih2k matrix / stable-system substrate
    (`FinVec`, `vecmatsV3_p4`, `V_SY_p4`/`E_SY_p4`/`F_SY_p4`,
    `CONDITION*_SY_p4`, `B_SY1_p4`, `StableSyP23`, `rowSy_p23`,
    `J1_SY_p23`, `dFun_p23`, `tauStar_p23`, `earSy_p23`) from
    LocalAuto23/LocalAuto4 (via import); `arclength` ↦ `arcLength`
    (PackingAuto18); `arcV` from LuneVolume.
  - HOL `SUC i` ↦ `i + 1` (defeq via `Nat.succ`); HOL `dist(x,y)` ↦
    `dist x y`; `vec 0` ↦ `(0 : V3)`; `scs_k_v39 s` ↦ `s.k`; the HOL
    `scs_J_v39 s i = {}` writing is ported as `∀ j, ¬ s.J i j` in the
    k=6 J-emptiness lemmas (the `=`-form `scsM`/`scs_basic`-reduction uses
    `scsJSet_p23`-style sets only where the source does).
  - GBYCPXS: HOL `k_sy s = k /\ dimindex(:M) = k /\ I_SY s = 0..k-1 /\
    f_sy s = (\i. (1+i) MOD k)` is rendered with `k` fixed at `s.k`
    (`k_sy` is the record field `s.k`, the `dimindex` dummy is the
    `FinVec s.k 3` argument), `I_SY s = 0..k-1` as the set equality
    `s.I = {i | i < s.k}`, `f_sy s` as the field `s.f`, and
    `B_SY1 (a_sy s) (b_sy s)` as `B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)`
    (1-based HOL rows `1..k` read off 0-based).  `sigma_sy` is the new
    `sigmaSy_p26 = if ear_sy s then 1 else -1`.
  - DISCHARGES: proved items are mechanical (set/image bookkeeping, mod
    arithmetic, `isScsV39`/`BBsV39` unpacking, `arccos` monotonicity,
    `Set.ncard = 1` singleton extraction, solid-angle positivity); the
    giants are `sorry` with NEEDS markers naming the blocking kit.
    Section D: `SOL0_POS`/`SIGMA_SY_LE1`/`PROPERTIES_EAR_SY`/`SING_J1_SY`
    proved (the last via `j1SingAux_p26` + `Nat.modEq_iff_dvd'`);
    `TAU_STAR_POS`/`GBYCPXS` are proved compositions over the `sorry`ed
    `D_FUN_LE`/`TAU_FUN_LE`/`CIRCULAR_SOL_EQ_2PI`; `NOT_CIRCULAR_SY`
    reduces to the single `convexLocalFan_p4 -> ConvexLocalFan` bridge
    sorry; `CARD_F_SY_IN_B_SY`/`B_SY_LE_CSTAB` need the `INJ_ROW_B_SY`
    1-based-row bridge.
-/

import Kepler.Text.CircularSolKit
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto27
-- LA1 root unlock (lane la1-bimport-w1): the clean `_p28` engines
-- (`ODXLSTCv2_p28` / `IMJXPHRv2_p28`) live in LocalAuto28, which this
-- module could not previously see.  Static import DAG: no path LA28 ->* LA26.
import Kepler.Text.LocalAuto28
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p26` helpers -/

/-- HOL `CHANGE_A_SCS_MOD`/`CHANGE_B_SCS_MOD` role: a `Periodic2 f k`
family is unchanged when both indices are reduced mod `k`. -/
theorem periodic2_mod_eq_p26 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : 0 < k)
    (hp : Periodic2 f k) (i j : ℕ) : f i j = f (i % k) (j % k) := by
  have hstep : ∀ q r j, f (q * k + r) j = f r j := by
    intro q
    induction q with
    | zero =>
        intro r j
        simp
    | succ q ih =>
        intro r j
        have hq : q.succ * k + r = q * k + r + k := by
          rw [Nat.succ_eq_add_one]
          ring_nf
        rw [hq]
        rw [(hp (q * k + r) j).1]
        exact ih r j
  have hcol : ∀ q r i, f i (q * k + r) = f i r := by
    intro q
    induction q with
    | zero =>
        intro r i
        simp
    | succ q ih =>
        intro r i
        have hq : q.succ * k + r = q * k + r + k := by
          rw [Nat.succ_eq_add_one]
          ring_nf
        rw [hq, (hp i (q * k + r)).2]
        exact ih r i
  have hrow : ∀ j, f i j = f (i % k) j := by
    intro j
    calc
      f i j = f (k * (i / k) + i % k) j := by rw [Nat.div_add_mod i k]
      _ = f ((i / k) * k + i % k) j := by rw [Nat.mul_comm k (i / k)]
      _ = f (i % k) j := hstep (i / k) (i % k) j
  have hcol' : ∀ i, f i j = f i (j % k) := by
    intro i
    calc
      f i j = f i (k * (j / k) + j % k) := by rw [Nat.div_add_mod j k]
      _ = f i ((j / k) * k + j % k) := by rw [Nat.mul_comm k (j / k)]
      _ = f i (j % k) := hcol (j / k) (j % k) i
  exact (hrow j).trans (hcol' (i % k))

/-- The HOL `SUC_MOD_NOT_EQ` fact: consecutive indices are distinct mod
`k` when `1 < k`. -/
theorem succ_mod_ne_p26 {a n : ℕ} (hn : 1 < n) : a % n ≠ (a + 1) % n := by
  intro h
  have hn0 : 0 < n := by omega
  have hm : a % n < n := Nat.mod_lt a hn0
  have ha1 : (a + 1) % n = (a % n + 1) % n := by
    exact (Nat.ModEq.add (Nat.mod_modEq a n) (Nat.ModEq.refl (1 : ℕ))).symm
  rw [ha1] at h
  by_cases hcase : a % n + 1 < n
  · have hlt : (a % n + 1) % n = a % n + 1 := Nat.mod_eq_of_lt hcase
    omega
  · have hcol : a % n + 1 = n := by omega
    have hz : (a % n + 1) % n = 0 := by
      rw [hcol, Nat.mod_self]
    have hz2 : a % n = 0 := by
      rw [hz] at h
      exact h
    omega

/-- HOL `sigma_sy` (HDPLYGY.hl:39, inlined in `d_fun`). -/
noncomputable def sigmaSy_p26 (s : StableSyP23) : ℝ :=
  if earSy_p23 s then 1 else -1

/-- The `a_sy s` k×k matrix read 0-based (HOL row `i` = 1-based). -/
def aSyRow_p26 (s : StableSyP23) : Fin s.k → Fin s.k → ℝ :=
  fun i j => s.a (i.val + 1) (j.val + 1)

/-- The `b_sy s` k×k matrix read 0-based (HOL row `i` = 1-based). -/
def bSyRow_p26 (s : StableSyP23) : Fin s.k → Fin s.k → ℝ :=
  fun i j => s.b (i.val + 1) (j.val + 1)

/-! ## Section A: RRCWNSJ -/

/-- HOL `BB_VV_FUN_EQ` (RRCWNSJ.hl:92).
DISCHARGED: forward = the `W_IN_BB_FUN_EQ` quasi-injectivity (mirrored from
the LocalAuto28 fill: the 16th `isScsV39` conjunct `2 ≤ a i j` off the
residue diagonal, with `BBsV39` bounds collapsing `dist = 0`); backward =
mod-folding of the `Periodic vv s.k` realisation (`periodic_mod_eq_p23`). -/
theorem BB_VV_FUN_EQ_p26 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hv : BBsV39 s vv) : ∀ i j, vv i = vv j ↔ i % s.k = j % s.k := by
  obtain ⟨-, h3k, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag, -, -, -, -, -⟩ := hs
  have hk0 : 0 < s.k := by omega
  intro i j
  constructor
  · intro heq
    have hwx : vv (i % s.k) = vv i := periodic_mod_eq_p23 hv.2.1 i
    have hwy : vv (j % s.k) = vv j := periodic_mod_eq_p23 hv.2.1 j
    by_contra hne
    have hdist : dist (vv (i % s.k)) (vv (j % s.k)) = 0 := by
      rw [hwx, hwy, heq, dist_self]
    have hle := (hv.2.2.1 (i % s.k) (j % s.k)).1
    rw [hdist] at hle
    exact absurd (hdiag (i % s.k) (j % s.k)
      ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, fun hc => hne (by rw [hc])⟩)
      (by linarith)
  · intro hmod
    rw [← periodic_mod_eq_p23 hv.2.1 i, hmod, periodic_mod_eq_p23 hv.2.1 j]

/-- HOL `WL_IN_E` (RRCWNSJ.hl:100). -/
theorem WL_IN_E_p26 (w : ℕ → V3) (l : ℕ) :
    ({w l, w (l + 1)} : Set V3) ∈ Set.range (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) := by
  exact ⟨l, rfl⟩

/-- HOL `LUNAR_IN_V` (RRCWNSJ.hl:108). -/
theorem LUNAR_IN_V_p26 (v w : V3) (V : Set V3) (E : Set (Set V3))
    (h : Lunar v w V E) : v ∈ V ∧ w ∈ V := by
  unfold Lunar at h
  exact ⟨h.2.1 (by simp), h.2.1 (by simp)⟩

/-- HOL `B_LE_2h0_A_EQ2_IN_CASES_6` (RRCWNSJ.hl:114). -/
theorem B_LE_2h0_A_EQ2_IN_CASES_6_p26 (s : ScsV39) (hk : s.k = 6)
    (hs : isScsV39 s) : ∀ i, s.b i (i + 1) ≤ 2 * h0 ∧ s.a i (i + 1) = 2 := by
  unfold isScsV39 at hs
  obtain ⟨hd, h3k, hk6, hlo, hhi, hstr1, hstr2, hpa, hpam, hpbm, hpb, hpJ,
    hsym, hch, hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  rw [hk] at hpa hpb hdiag
  have hcard6 : {i | i < 6 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.ncard = 0 := by
    rw [hk] at hcard
    omega
  have hfin : ({i | i < 6 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} : Set ℕ).Finite := by
    exact Set.Finite.subset (Set.finite_Iio (6 : ℕ)) (by intro x hx; exact hx.1)
  have hempty : ({i | i < 6 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} : Set ℕ) = ∅ := by
    exact (Set.ncard_eq_zero hfin).mp hcard6
  have hempt : ∀ j, j < 6 → ¬(2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1)) := by
    intro j hj hh
    have : j ∈ ({i | i < 6 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} : Set ℕ) := ⟨hj, hh⟩
    simpa [hempty] using this
  intro i
  have hnot := hempt (i % 6) (Nat.mod_lt _ (by norm_num : 0 < 6))
  have hnotb : ¬2 * h0 < s.b (i % 6) ((i % 6) + 1) := fun h => hnot (Or.inl h)
  have hnota : ¬2 < s.a (i % 6) ((i % 6) + 1) := fun h => hnot (Or.inr h)
  have hmod : (i % 6 + 1) % 6 = (i + 1) % 6 :=
    Nat.ModEq.add (Nat.mod_modEq i 6) (Nat.ModEq.refl (1 : ℕ))
  have hred {f : ℕ → ℕ → ℝ} (hp : Periodic2 f 6) :
      f (i % 6) ((i % 6) + 1) = f (i % 6) ((i + 1) % 6) := by
    have hlt : (i % 6) % 6 = i % 6 := Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num : 0 < 6))
    have hp0 := periodic2_mod_eq_p26 (by norm_num : 0 < 6) hp (i % 6) ((i % 6) + 1)
    rwa [hlt, hmod] at hp0
  have hb : s.b i (i + 1) ≤ 2 * h0 := by
    have hrb : s.b i (i + 1) = s.b (i % 6) ((i % 6) + 1) :=
      (periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpb i (i + 1)).trans (hred hpb).symm
    rw [hrb]
    exact le_of_not_gt hnotb
  have h2le : 2 ≤ s.a i (i + 1) := by
    have hll : 2 ≤ s.a (i % 6) ((i + 1) % 6) :=
      hdiag (i % 6) ((i + 1) % 6)
        ⟨Nat.mod_lt _ (by norm_num : 0 < 6), Nat.mod_lt _ (by norm_num : 0 < 6),
          succ_mod_ne_p26 (by norm_num : 1 < 6)⟩
    rw [periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpa i (i + 1)]
    exact hll
  have ha_eq : s.a i (i + 1) = 2 := by
    have hra : s.a i (i + 1) ≤ 2 := by
      have hr : s.a i (i + 1) = s.a (i % 6) ((i % 6) + 1) :=
        (periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpa i (i + 1)).trans (hred hpa).symm
      rw [hr]
      exact le_of_not_gt hnota
    exact le_antisymm hra h2le
  exact ⟨hb, ha_eq⟩

/-- HOL `J_EMPY_CASES_6` (RRCWNSJ.hl:158). -/
theorem J_EMPY_CASES_6_p26 (s : ScsV39) (i : ℕ) (hk : s.k = 6)
    (hs : isScsV39 s) : ∀ j, ¬ s.J i j := by
  have hscs : isScsV39 s := hs
  unfold isScsV39 at hs
  obtain ⟨hd, h3k, hk6, hlo, hhi, hstr1, hstr2, hpa, hpam, hpbm, hpb, hpJ,
    hsym, hch, hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  rw [hk] at hJmod hpa hpb
  intro j hJ
  have hB : s.b i j = cstab := (hJsq i j hJ).2
  have hmodJ := hJmod i j hJ
  rcases hmodJ with hcase | hcase
  · have hEq : s.b i j = s.b i (i + 1) := by
      have h1 := periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpb i j
      have h2 := periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpb i (i + 1)
      rw [hcase] at h1
      exact h1.trans h2.symm
    have hle : s.b i (i + 1) ≤ 2 * h0 := (B_LE_2h0_A_EQ2_IN_CASES_6_p26 s hk hscs i).1
    have hbad : cstab ≤ 2 * h0 := by
      rw [← hB, hEq]
      exact hle
    norm_num [cstab, h0] at hbad
  · have hEq : s.b i j = s.b j (j + 1) := by
      have hs_ij : s.b i j = s.b j i := (hsym i j).2.2.2.1
      have h1 := periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpb j i
      have h2 := periodic2_mod_eq_p26 (by norm_num : 0 < 6) hpb j (j + 1)
      rw [hcase] at h1
      calc
        s.b i j = s.b j i := hs_ij
        _ = s.b (j % 6) ((j + 1) % 6) := h1
        _ = s.b j (j + 1) := h2.symm
    have hle : s.b j (j + 1) ≤ 2 * h0 := (B_LE_2h0_A_EQ2_IN_CASES_6_p26 s hk hscs j).1
    have hbad : cstab ≤ 2 * h0 := by
      rw [← hB, hEq]
      exact hle
    norm_num [cstab, h0] at hbad

/-- HOL `BB_RHO_NODE_IVS` (RRCWNSJ.hl:195).
DISCHARGED 2026-10-28 (scsgeneric-recon): the fan-free route — both
`rho_node1`/`ivs_rho_node1` are epsilon picks over the dart set, and `FF`
is the periodic image of the successor darts, so the predecessor/successor
of `u = vv p1` along the cycle is unique by mod-k injectivity
(`BB_VV_FUN_EQ_p26` + `periodic_mod_eq_p23`, both already standard-three in
this file's import closure); no `ConvexLocalFan`/`CVLF_LF_F` input is
consumed.  The HOL route (`VV_SUC_EQ_RHO_NODE_PRIME` iterate + `CARD V = k`
iterate tail) is replaced by the direct dart-characterisation. -/
theorem BB_RHO_NODE_IVS_p26 (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (u : V3)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (p1 : ℕ)
    (hk' : s.k = k) (hu : vv p1 = u) (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hs : isScsV39 s) (h3k : 3 < k) (hv : BBsV39 s vv) :
    rhoNode1 FF u = vv (p1 + 1) ∧ ivsRhoNode1 FF u = vv (p1 + k - 1) := by
  subst hk'
  -- dart membership: FF is exactly the successor-dart image.
  have hmem : ∀ x y : V3, (x, y) ∈ FF ↔ ∃ i, (vv i, vv (i + 1)) = (x, y) := by
    intro x y
    rw [← hFF, Set.mem_range]
  have hmod : ∀ n, vv (n % s.k) = vv n := fun n => periodic_mod_eq_p23 hv.2.1 n
  -- mod-k injectivity (Section A, already discharged).
  have hinj : ∀ i j, vv i = vv j → i % s.k = j % s.k :=
    fun i j hij => (BB_VV_FUN_EQ_p26 s vv hs hv i j).mp hij
  -- the successor along the cycle: witness + uniqueness.
  have hwsucc : (fun w => (u, w) ∈ FF) (vv (p1 + 1)) := by
    show (u, vv (p1 + 1)) ∈ FF
    rw [hmem]
    exact ⟨p1, by rw [hu]⟩
  have huniqsucc : ∀ w, (u, w) ∈ FF → w = vv (p1 + 1) := by
    intro w hw
    obtain ⟨i, hfi⟩ := (hmem u w).mp hw
    have h1 : vv i = u := congrArg Prod.fst hfi
    have h2 : vv (i + 1) = w := congrArg Prod.snd hfi
    have hpi : vv p1 = vv i := by rw [hu, h1]
    have heq : i % s.k = p1 % s.k := (hinj p1 i hpi).symm
    have hshift : (i + 1) % s.k = (p1 + 1) % s.k := by
      have e1 : (i + 1) % s.k = (i % s.k + 1) % s.k := (Nat.mod_add_mod i s.k 1).symm
      have e2 : (p1 + 1) % s.k = (p1 % s.k + 1) % s.k := (Nat.mod_add_mod p1 s.k 1).symm
      rw [e1, heq, e2]
    calc w = vv (i + 1) := h2.symm
      _ = vv ((i + 1) % s.k) := (hmod _).symm
      _ = vv ((p1 + 1) % s.k) := by rw [hshift]
      _ = vv (p1 + 1) := hmod _
  -- the predecessor along the cycle: witness + uniqueness.
  have hkwrap : (p1 + s.k) % s.k = p1 % s.k := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have hkpred : vv (p1 + s.k - 1 + 1) = u := by
    have hsk : p1 + s.k - 1 + 1 = p1 + s.k := by omega
    rw [hsk]
    rw [← hu, ← hmod (p1 + s.k), hkwrap, hmod p1]
  have hwpred : (fun a => (a, u) ∈ FF) (vv (p1 + s.k - 1)) := by
    show (vv (p1 + s.k - 1), u) ∈ FF
    rw [hmem]
    refine ⟨p1 + s.k - 1, ?_⟩
    rw [hkpred]
  have huniqpred : ∀ a, (a, u) ∈ FF → a = vv (p1 + s.k - 1) := by
    intro a ha
    obtain ⟨i, hfi⟩ := (hmem a u).mp ha
    have h1 : vv i = a := congrArg Prod.fst hfi
    have h2 : vv (i + 1) = u := congrArg Prod.snd hfi
    have hp1eq : vv p1 = vv (i + 1) := by rw [hu, ← h2]
    have heq : (i + 1) % s.k = p1 % s.k := (hinj p1 (i + 1) hp1eq).symm
    -- i + 1 ≡ p1 (mod k), k ≥ 1 ⇒ i ≡ p1 + k - 1 (mod k).
    have hshift : i % s.k = (p1 + s.k - 1) % s.k := by
      have hB : (p1 + s.k) % s.k = p1 % s.k := hkwrap
      have hD : Nat.ModEq s.k i (p1 + s.k - 1) := by
        have hE : (i + 1) % s.k = ((p1 + s.k - 1) + 1) % s.k := by
          rw [heq, show (p1 + s.k - 1) + 1 = p1 + s.k from by omega, hB]
        exact Nat.ModEq.add_right_cancel' 1 hE
      exact hD
    calc a = vv i := h1.symm
      _ = vv (i % s.k) := (hmod _).symm
      _ = vv ((p1 + s.k - 1) % s.k) := by rw [hshift]
      _ = vv (p1 + s.k - 1) := hmod _
  refine ⟨?_, ?_⟩
  · show Classical.epsilon (fun w => (u, w) ∈ FF) = vv (p1 + 1)
    exact huniqsucc _ (Classical.epsilon_spec (p := fun w => (u, w) ∈ FF)
      ⟨vv (p1 + 1), hwsucc⟩)
  · show Classical.epsilon (fun a => (a, u) ∈ FF) = vv (p1 + s.k - 1)
    exact huniqpred _ (Classical.epsilon_spec (p := fun a => (a, u) ∈ FF)
      ⟨vv (p1 + s.k - 1), hwpred⟩)

/-- HOL `BB_F_SUC_PRE` (RRCWNSJ.hl:223). -/
theorem BB_F_SUC_PRE_p26 (s : ScsV39) (f : ℕ → V3) (hs : isScsV39 s)
    (hv : BBsV39 s f) : ∀ i, f (i + s.k - 1 + 1) = f i := by
  have h1k : 1 ≤ s.k := by
    unfold isScsV39 at hs
    omega
  have heq : ∀ i, i + s.k - 1 + 1 = i + s.k := by
    intro i
    omega
  intro i
  rw [heq, hv.2.1]

/-! ## w5sg prep block for `RRCWNSJ_p26` (lane scsgeneric-w5a): in-place
re-derivations of the LA28/LA34 legs (outside this file's import closure)
and assembly bridges for the RRCWNSJ.hl:248-861 materialization. -/

/-- HOL `MMS_IMP_BBS` (NUXCOEA.hl:213; LA28:190) — in-place re-derivation
(LA28 is outside LA26's import closure). -/
private theorem w5sg_mms_bbs_p26 (s : ScsV39) (w : ℕ → V3) (h : w ∈ MMsV39 s) :
    BBsV39 s w := by
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
  exact h.1.1.1

/-- HOL `MMS_IMP_BBPRIME` (NUXCOEA.hl:217; LA28:196) — in-place re-derivation. -/
private theorem w5sg_mms_bbprime_p26 (s : ScsV39) (w : ℕ → V3) (h : w ∈ MMsV39 s) :
    w ∈ BBprimeV39 s := by
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
  exact h.1.1

/-- The `taustar < 0` leg consumed by `JKQEWGV2_p23`'s `hta` hypothesis
(HOL `MRESAL_TAC MMS_IMP_BBPRIME` at RRCWNSJ.hl:258 supplies it via
`BBprime_v39`). -/
private theorem w5sg_mms_taustar_neg_p26 (s : ScsV39) (w : ℕ → V3)
    (h : w ∈ MMsV39 s) : taustarV39 s w < 0 := by
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
  exact h.1.1.2.2

/-- HOL `BBS_IMP_CONVEX_LOCAL_FAN` (IMJXPHR.hl:97; LA34:494) — in-place
re-derivation (LA34 is outside LA26's import closure); body verbatim. -/
private theorem w5sg_bbs_convexlocalfan_p26 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (hk : 3 < k) (hkk : s.k = k) (hBB : BBsV39 s w) :
    ConvexLocalFan (Set.range w)
      (Set.range fun i => ({w i, w (i + 1)} : Set V3))
      (Set.range fun i => (w i, w (i + 1))) := by
  rcases hBB.2.2.2 with h3 | hcf
  · exact absurd h3 (by omega)
  · exact hcf

/-- HOL `WL_IN_V` (Odxlstc; LA28:172 twin) — in-place re-derivation. -/
private theorem w5sg_wl_in_v_p26 (w : ℕ → V3) (l : ℕ) : w l ∈ Set.range w := ⟨l, rfl⟩

/-- Diagonal-premise extraction (RRCWNSJ.hl:404-414 / 682-692 shape):
on a diagonal pair the frozen premises give `a i j < dist (v i) (v j)`
(`a ≤ cstab < dist`). -/
private theorem w5sg_diag_lt_dist_p26 (s : ScsV39) (v : ℕ → V3)
    (hdiag : ∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j))
    {i j : ℕ} (hd : scsDiag s.k i j) : s.a i j < dist (v i) (v j) :=
  lt_of_le_of_lt (hdiag i j hd).1 (hdiag i j hd).2

/-- `scsDiag` is invariant under reducing both indices mod `k` (role of HOL
`Ocbicby.MOD_EQ_MOD_SHIFT` in the RRCWNSJ case bash). -/
private theorem w5sg_diag_mod_p26 {k i j : ℕ} :
    scsDiag k i j ↔ scsDiag k (i % k) (j % k) := by
  have hred : ∀ a : ℕ, a % k % k = a % k := fun a => Nat.mod_mod a k
  have hshift1 : ∀ a : ℕ, (a % k + 1) % k = (a + 1) % k := fun a =>
    Nat.ModEq.add (Nat.mod_modEq a k) (Nat.ModEq.refl 1)
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hc => h1 (by rw [hred i, hred j] at hc; exact hc), ?_, ?_⟩
    · intro hc
      rw [hshift1 i, hred j] at hc
      exact h2 hc
    · intro hc
      rw [hred i, hshift1 j] at hc
      exact h3 hc
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hc => h1 (by rw [hred i, hred j]; exact hc),
      fun hc => h2 (by rw [hshift1 i, hred j]; exact hc),
      fun hc => h3 (by rw [hred i, hshift1 j]; exact hc)⟩

/-- The RRCWNSJ.hl:829-833 diagonal instance: for `4 ≤ k` the pair
`(x+1, x+k-1)` (one step after `x` against the `k-1`-th predecessor) is a
diagonal. -/
private theorem w5sg_diag_ends_p26 {k x : ℕ} (hk : 4 ≤ k) :
    scsDiag k (x + 1) (x + k - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    have hdvd := (Nat.modEq_iff_dvd' (show (x + 1) ≤ x + k - 1 by omega)).mp hc
    have hle : k ≤ (x + k - 1) - (x + 1) := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro hc
    have hdvd := (Nat.modEq_iff_dvd' (show x + 1 + 1 ≤ x + k - 1 by omega)).mp hc
    have hle : k ≤ (x + k - 1) - (x + 2) := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro hc
    have hdvd := (Nat.modEq_iff_dvd' (show (x + 1) ≤ x + k - 1 + 1 by omega)).mp hc
    have hle : k ≤ (x + k - 1 + 1) - (x + 1) := Nat.le_of_dvd (by omega) hdvd
    omega

/-! ### The `ConvexLocalFan` → `convexLocalFan_p2` gate

LA5's lunar kit (`HKIRPEP` / `LUNAR_IMP_HALF_CIRCLE_SUBSET_AFF_GT` /
`AFF_IVS_RHO_NODE_EQQ` / `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` / `CVLF_LF_F` /
`ITER_CARD_MINUS1_EQ_IVS_RN1`) is stated over the LA2 `convexLocalFan_p2`
encoding, while `BBsV39` (and hence the RRCWNSJ assembly) carries the LA1
`ConvexLocalFan`.  The transport exists as the private `kcs_clf2` inside
CircularSolKit; this is its public-consumer re-derivation (bodies carried
verbatim from CircularSolKit.lean, whose private helpers are re-made here).
-/

/-- 2-regularity ⇒ every vertex lies on some edge (CircularSolKit `kcs_hedge`). -/
private theorem w5sg_hedge_p26 {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E) ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

/-- `localFan_p2 ⇒ FF ⊆ dart1OfFan` (CircularSolKit `kcs_ffSubDart`). -/
private theorem w5sg_ffSubDart_p26 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : localFan_p2 V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    FF ⊆ Fan.dart1OfFan V E := by
  obtain ⟨H, hd, -, -, -, -, hface, -⟩ := hlf
  obtain ⟨z, hzd, hFF⟩ := hface
  intro d hdF
  have hsub := H.face_subset_darts hzd (hFF ▸ hdF)
  rw [hd] at hsub
  exact (hno_p2_of_no_isolated hedge) ▸ hsub

/-- LA1 `ConvexLocalFan` → LA2 `convexLocalFan_p2` (CircularSolKit `kcs_clf2`,
carried verbatim; that copy is `private` and not importable). -/
private theorem w5sg_clf2_p26 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf (w5sg_hedge_p26 h2reg)
  have hsub := w5sg_ffSubDart_p26 hlf2 (w5sg_hedge_p26 h2reg)
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

/-! ### Def-family bridges for `CIZMRRH` (LA3, `p3` family) -/

/-- `lunar_p3` (LA3, pair-curried) is the LA1 `Lunar` (RRCWNSJ assembly form);
bodies coincide modulo the `Collinear3` notation (`Geom/Azim.lean:43`). -/
private theorem w5sg_lunar_p3_p26 {V : Set V3} {E : Set (Set V3)} {a b : V3} :
    lunar_p3 (a, b) V E ↔ Lunar a b V E := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4⟩
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4⟩

/-! ### The `w5sg3b` block (lane scsgeneric-w5b3): in-place re-derivations of
the two remaining lunar-bank debts consumed by the `RRCWNSJ` assembly — debt
#3 (`LOCAL_CONVEX_NOT_COLLINEAR`, LA37:991; LA37 is outside this file's
import closure) and debt #4 (`AXJRPNC` forward port).  Engines: the LA5
lunar-fan inventory `HKIRPEP`, `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` /
`LOFA_IMP_NOT_COLL_IVS`, the LA5 rho-orbit map, and
`PlanarityAngle.aff_gt_imp_not_collinear` — all inside this file's import
closure via `CircularSolKit`; the LA1→LA2 gate is the in-file
`w5sg_clf2_p26` block above. -/

/-- Iterate mod-folding: a point of period `k` folds iterate indices
mod `k`. -/
private theorem w5sg3b_iter_mod {α : Type*} {f : α → α} {x : α} {k : ℕ} (hk : 0 < k)
    (hper : f^[k] x = x) (m : ℕ) : f^[m] x = f^[m % k] x := by
  have hstep : ∀ r : ℕ, f^[r + k] x = f^[r] x := by
    intro r
    rw [Function.iterate_add_apply f r k x, hper]
  have hmain : ∀ q r : ℕ, f^[q * k + r] x = f^[r] x := by
    intro q
    induction q with
    | zero =>
        intro r
        simp
    | succ q ih =>
        intro r
        have hq : q.succ * k + r = (q * k + r) + k := by
          rw [Nat.succ_eq_add_one]
          ring_nf
        rw [hq, hstep, ih r]
  calc f^[m] x = f^[m / k * k + m % k] x := by
        conv_lhs =>
          rw [show m = m / k * k + m % k from by
            rw [Nat.mul_comm (m / k) k]
            exact (Nat.div_add_mod m k).symm]
    _ = f^[m % k] x := hmain (m / k) (m % k)

/-- HOL `LOCAL_CONVEX_NOT_COLLINEAR` (lunar_deform.hl:3616; LA37:991,
assembly debt #3) — in-place re-derivation.  Route: the LA5 lunar-fan
inventory `HKIRPEP` describes the two rho-cycle arcs between `v` and `w`
as exact `affGt {0, v} {-} ∩ V` equalities; every other vertex lies on one
of the two arcs, hence in one of the two open half-cones bounded by
`line (0, v)`; `LOCAL_FAN_CHARACTER_OF_RHO_NODE2` (successor direction) and
`LOFA_IMP_NOT_COLL_IVS` (predecessor direction) give the non-collinearity of
the cone directions and `PlanarityAngle.aff_gt_imp_not_collinear`
transports it to `u`.  (The HOL route consumes
`LUNAR_IMP_IN_TWO_HAFLS_PLANE`, which is only available as a `sorry` in
LA37; the arc equalities of `HKIRPEP` subsume it here.) -/
private theorem w5sg3b_localConvexNotCollinear_p26 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3} (h : ConvexLocalFan V E FF) (hl : Lunar v w V E) :
    ∀ u ∈ V, u ≠ v → u ≠ w → ¬Collinear ℝ ({0, v, u} : Set V3) := by
  have hclf : convexLocalFan_p2 V E FF := w5sg_clf2_p26 h
  have hl2 : lunar_p2 v w V E := hl
  obtain ⟨hlf, -⟩ := CVLF_LF_F hclf
  have hvV : v ∈ V := hl.2.1 (by simp)
  obtain ⟨-, -, -, -, harcv, harcw⟩ := HKIRPEP hclf hl2
  obtain ⟨t, htV, ht0, ht1, htw, harcvE⟩ := harcv
  obtain ⟨t2, ht2V, ht20, ht21, ht2v, harcwE⟩ := harcw
  have hrho := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hvV
  have hivs := LOFA_IMP_NOT_COLL_IVS hlf hvV
  -- the rho-cycle closes: `v` has period `t + t2` (both ≥ 2 by HKIRPEP)
  have htpos : 0 < t := by omega
  have ht2pos : 0 < t2 := by omega
  have hper : (rhoNode1_p2 FF)^[t + t2] v = v := by
    rw [show t + t2 = t2 + t from Nat.add_comm t t2, Function.iterate_add_apply,
      ← htw, ← ht2v]
  intro u hu hne1 hne2
  -- `u` lies on the rho-orbit of `v`
  have hu2 : u ∈ orbitF_p2 (rhoNode1_p2 FF) v := by
    rw [LOCAL_FAN_ORBIT_MAP_V hlf hvV]
    exact hu
  simp only [orbitF_p2, Set.mem_setOf_eq] at hu2
  obtain ⟨m, hm⟩ := hu2
  have hf := w5sg3b_iter_mod (by omega) hper m
  have hur : (rhoNode1_p2 FF)^[m % (t + t2)] v = u := hf.symm.trans hm
  rcases Nat.lt_trichotomy (m % (t + t2)) t with hri | hri | hri
  · -- before `w` on the forward arc (or at `v` itself)
    rcases Nat.eq_zero_or_pos (m % (t + t2)) with hr0 | hrpos
    · rw [hr0, Function.iterate_zero_apply] at hur
      exact fun _hc => absurd hur.symm hne1
    · have huarc : u ∈
        (fun l => (rhoNode1_p2 FF)^[l] v) '' {l : ℕ | 0 < l ∧ l < t} :=
        ⟨m % (t + t2), ⟨hrpos, hri⟩, hur⟩
      have humem : u ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3) ∩ V := by
        rw [← harcvE]
        exact huarc
      exact aff_gt_imp_not_collinear hrho humem.1
  · -- at `w` itself
    rw [hri, ← htw] at hur
    exact fun _hc => absurd hur.symm hne2
  · -- past `w`: on the return arc, in the `ivs v` cone
    have hrlt : m % (t + t2) < t + t2 :=
      Nat.mod_lt _ (by omega)
    have hsplit : (rhoNode1_p2 FF)^[m % (t + t2)] v
        = (rhoNode1_p2 FF)^[m % (t + t2) - t] ((rhoNode1_p2 FF)^[t] v) := by
      have hradd : m % (t + t2) = m % (t + t2) - t + t := by omega
      conv_lhs =>
        rw [hradd, Function.iterate_add_apply]
    rw [hsplit, ← htw] at hur
    have huarc : u ∈
        (fun l => (rhoNode1_p2 FF)^[l] w) '' {l : ℕ | 0 < l ∧ l < t2} :=
      ⟨m % (t + t2) - t, ⟨by omega, by omega⟩, hur⟩
    have humem : u ∈ affGt ({0, v} : Set V3) ({ivsRhoNode1_p2 FF v} : Set V3) ∩ V := by
      rw [← harcwE]
      exact huarc
    exact aff_gt_imp_not_collinear hivs humem.1

/-- HOL `AXJRPNC` (AXJRPNC.hl:380; assembly debt #4) — forward port with the
single metric-elimination premise `helim`.  The HOL body is a ~670-line case
bash: the structural core (MMs → fan, `HKIRPEP` lunar inventory, `CARD V = k`,
rho-successor orbit bookkeeping, minimal period, the cyclic-distance case
bash) is proved here in full; the distance-2 lunar eliminations that power
the `k = 4/5` branches and the `k = 6` distance-2/4 sub-branches consume
`Ppbtydq.PPBTYDQ` + `OIQKKEP` in HOL (Lean twins `PPBTYDQ_concl` /
`OIQKKEP_concl`, LocalAuto1, are `sorryAx`), so exactly those legs are
carried as the explicit premise `helim` below (a lunar pair at cyclic
distance 2 is impossible).  W5d closes the target by proving `helim` and
applying this piece verbatim. -/
private theorem w5sg3b_axjrpnc_p26 (s : ScsV39) (v : ℕ → V3) (i j : ℕ)
    (hs : isScsV39 s) (hbasic : scsBasicV39 s)
    (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : MMsV39 s v)
    (hlunar : Lunar (v i) (v j) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)))
    (helim : ∀ p : ℕ, ¬ Lunar (v p) (v (p + 2)) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)))
    (h4 : 4 ≤ s.k) :
    s.k = 6 ∧ v j = v (i + 3) := by
  have hBB : BBsV39 s v := w5sg_mms_bbs_p26 s v hv
  have hk0 : 0 < s.k := by
    have h3 : 3 ≤ s.k := hs.2.1
    omega
  have h3k : 3 < s.k := by omega
  have h6k : s.k ≤ 6 := hs.2.2.1
  have hper : Periodic v s.k := hBB.2.1
  -- the range-form fan (LA1 form, from the `BBsV39` disjunction) and its p2 transport
  have hcfan : ConvexLocalFan (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))
      (Set.range fun l : ℕ => (v l, v (l + 1))) :=
    hBB.2.2.2.resolve_left (by omega)
  have hclf2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))
      (Set.range fun l : ℕ => (v l, v (l + 1))) := w5sg_clf2_p26 hcfan
  obtain ⟨-, -, -, -, harcv, harcw⟩ :=
    HKIRPEP hclf2 (hlunar : lunar_p2 (v i) (v j) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)))
  obtain ⟨t, htV, ht0, ht1, htw, -⟩ := harcv
  obtain ⟨t2, ht2V, ht20, ht21, ht2v, -⟩ := harcw
  -- rho = successor on the dart cycle (in-file kit), under the p2 name
  have hrho1 : ∀ p : ℕ,
      rhoNode1_p2 (Set.range fun l : ℕ => (v l, v (l + 1))) (v p) = v (p + 1) := by
    intro p
    exact (BB_RHO_NODE_IVS_p26 s s.k v (v p) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))
      (Set.range fun l : ℕ => (v l, v (l + 1))) p rfl rfl rfl rfl rfl hs h3k hBB).1
  -- iterate step: `rho^[n] (v p) = v (p + n)`
  have hstep : ∀ n p : ℕ,
      ((rhoNode1_p2 (Set.range fun l : ℕ => (v l, v (l + 1))))^[n]) (v p)
        = v (p + n) := by
    intro n
    induction n with
    | zero =>
        intro p
        rw [Function.iterate_zero_apply, Nat.add_zero]
    | succ n ih =>
        intro p
        rw [Function.iterate_succ_apply', ih p, hrho1, Nat.add_assoc]
  -- CARD V = s.k (in-place `CARD_V_EQ_SCS_K1`)
  have hVcard : (Set.range v).ncard = s.k := by
    rw [range_periodic_image_p23 v s.k hk0 hper, Set.InjOn.ncard_image]
    · rw [Set.ncard_Iio_nat]
    · intro a ha b hbv hab
      have hmod := (BB_VV_FUN_EQ_p26 s v hs hBB a b).mp hab
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hbv] at hmod
      exact hmod
  have htlt : t < s.k := by rw [← hVcard]; exact htV
  have ht2lt : t2 < s.k := by rw [← hVcard]; exact ht2V
  -- the lunar partner is the `t`-th successor of `v i`, and vice versa
  have hvj_t : v j = v (i + t) := by rw [htw, hstep]
  have hvi_t2 : v i = v (j + t2) := by rw [ht2v, hstep]
  have hback : v (i + t + t2) = v i := by
    rw [← hstep (t2) (i + t), ← hstep t i, ← htw, ← ht2v]
  -- minimal period: `s.k ∣ t + t2`
  have hdvd : s.k ∣ (i + t + t2) - i := by
    have hme := (BB_VV_FUN_EQ_p26 s v hs hBB (i + t + t2) i).mp hback
    exact (Nat.modEq_iff_dvd' (by omega)).mp hme.symm
  have hsub : (i + t + t2) - i = t + t2 := by omega
  rw [hsub] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · rcases Nat.lt_or_ge q 1 with hq0 | hq1'
    · -- q = 0: contradicts t, t2 ≥ 2
      have hqv : q = 0 := by omega
      rw [hqv, Nat.mul_zero] at hq
      exfalso
      omega
    · -- q = 1: the only survivor
      have hqv : q = 1 := by omega
      rw [hqv, Nat.mul_one] at hq
      -- t, t2 ∈ [2, s.k - 1], t + t2 = s.k
      rcases Nat.lt_or_ge s.k 6 with hk5 | hk6
      · rcases Nat.lt_or_ge s.k 5 with hk4 | hk5'
        · -- k = 4: t = t2 = 2, a distance-2 lunar pair
          have hkv : s.k = 4 := by omega
          have htv : t = 2 := by omega
          rw [htv] at hvj_t
          rw [hvj_t] at hlunar
          exact absurd hlunar (helim i)
        · -- k = 5: t = 2 or t = 3
          rcases Nat.lt_or_ge t 3 with htv | htv2
          · have htv3 : t = 2 := by omega
            rw [htv3] at hvj_t
            rw [hvj_t] at hlunar
            exact absurd hlunar (helim i)
          · have htv3 : t = 3 := by omega
            have hkv : s.k = 5 := by omega
            rw [htv3] at hvj_t
            rw [hkv] at hper
            have hb5 : v ((i + 3) + 2) = v i := by
              rw [show (i + 3) + 2 = i + 5 from by omega]
              exact hper i
            rw [hvj_t] at hlunar
            have h1p : lunar_p2 (v i) (v (i + 3)) (Set.range v)
                (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)) := hlunar
            have h2p := (LUNAR_COMM (v i) (v (i + 3)) (Set.range v)
              (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))).mp h1p
            rw [← hb5] at h2p
            exact absurd h2p (helim (i + 3))
      · -- k = 6
        have hkv : s.k = 6 := by omega
        rcases Nat.lt_or_ge t 3 with htv | htv4
        · have htv2 : t = 2 := by omega
          rw [htv2] at hvj_t
          rw [hvj_t] at hlunar
          exact absurd hlunar (helim i)
        · rcases Nat.lt_or_ge t 4 with htv3 | htv4'
          · have htv3 : t = 3 := by omega
            rw [htv3] at hvj_t
            exact ⟨hkv, hvj_t⟩
          · have htv4 : t = 4 := by omega
            rw [htv4] at hvj_t
            rw [hkv] at hper
            have hb6 : v ((i + 4) + 2) = v i := by
              rw [show (i + 4) + 2 = i + 6 from by omega]
              exact hper i
            rw [hvj_t] at hlunar
            have h1p : lunar_p2 (v i) (v (i + 4)) (Set.range v)
                (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)) := hlunar
            have h2p := (LUNAR_COMM (v i) (v (i + 4)) (Set.range v)
              (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))).mp h1p
            rw [← hb6] at h2p
            exact absurd h2p (helim (i + 4))
  · -- q ≥ 2: t + t2 ≥ 2·s.k contradicts t, t2 < s.k
    have h2 : s.k * 2 ≤ s.k * q := Nat.mul_le_mul (Nat.le_refl s.k) hq2
    rw [← hq] at h2
    exfalso
    omega

/-- HOL `RRCWNSJ` (RRCWNSJ.hl:248). Proof pending (needs
`MMS_IMP_BBPRIME` / `JKQEWGV2` / `BBS_IMP_CONVEX_LOCAL_FAN`). -/
theorem RRCWNSJ_p26 :
    main_nonlinear_terminal_v11 →
      ∀ s : ScsV39, ∀ v : ℕ → V3,
        isScsV39 s → scsBasicV39 s → MMsV39 s v → 3 < s.k →
        (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) →
        (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
        (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v := by
  sorry

/-! ## Section B: AXJRPNC -/

/-- HOL `DIST_LE_2h0_IN_CASES_6` (AXJRPNC.hl:92). -/
theorem DIST_LE_2h0_IN_CASES_6_p26 (s : ScsV39) (v : ℕ → V3) (hk : s.k = 6)
    (hv : BBsV39 s v) (hs : isScsV39 s) : ∀ i, ‖v i - v (i + 1)‖ ≤ 2 * h0 := by
  intro i
  have hB : s.b i (i + 1) ≤ 2 * h0 := (B_LE_2h0_A_EQ2_IN_CASES_6_p26 s hk hs i).1
  have hd : dist (v i) (v (i + 1)) ≤ s.b i (i + 1) := (hv.2.2.1 i (i + 1)).2
  rw [← dist_eq_norm]
  exact le_trans hd hB

/-- HOL `is_scs_k_le_3` (AXJRPNC.hl:175). -/
theorem is_scs_k_le_3_p26 (s : ScsV39) (hs : isScsV39 s) : 3 ≤ s.k := by
  unfold isScsV39 at hs
  exact hs.2.1

/-- HOL `DIST_EDGE_IN_BB_LE_2` (AXJRPNC.hl:131). -/
theorem DIST_EDGE_IN_BB_LE_2_p26 (s : ScsV39) (v : ℕ → V3) (hv : BBsV39 s v)
    (hs : isScsV39 s) : ∀ i, 2 ≤ ‖v i - v (i + 1)‖ := by
  unfold isScsV39 at hs
  obtain ⟨hd, h3k, hk6, hlo, hhi, hstr1, hstr2, hpa, hpam, hpbm, hpb, hpJ,
    hsym, hch, hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  have h0k : 0 < s.k := by omega
  have h1k : 1 < s.k := by omega
  intro i
  have hred : s.a i (i + 1) = s.a (i % s.k) ((i + 1) % s.k) :=
    periodic2_mod_eq_p26 h0k hpa i (i + 1)
  have hll : 2 ≤ s.a (i % s.k) ((i + 1) % s.k) :=
    hdiag (i % s.k) ((i + 1) % s.k)
      ⟨Nat.mod_lt _ h0k, Nat.mod_lt _ h0k, succ_mod_ne_p26 h1k⟩
  have h2 : 2 ≤ s.a i (i + 1) := by
    rw [← hred] at hll
    exact hll
  have hd : s.a i (i + 1) ≤ dist (v i) (v (i + 1)) := (hv.2.2.1 i (i + 1)).1
  rw [← dist_eq_norm]
  exact le_trans h2 hd

/-- HOL `NORM_V_IN_BB_LE_CSTAB` (AXJRPNC.hl:259). -/
theorem NORM_V_IN_BB_LE_CSTAB_p26 (s : ScsV39) (v : ℕ → V3)
    (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : BBsV39 s v) :
    ∀ i, ‖v i - v (i + 1)‖ ≤ cstab := by
  intro i
  have hd : dist (v i) (v (i + 1)) ≤ s.b i (i + 1) := (hv.2.2.1 i (i + 1)).2
  rw [← dist_eq_norm]
  exact le_trans hd (hb i)

/-- HOL `arclength222h0` (AXJRPNC.hl:152).
DISCHARGED: numerically — `h0 = #1.26` makes `|c²-a²-b²| < sqrt (upsX 4 4
4h0²)` (the `atn2` first branch, the `ATN_UPS_X_BREAKDOWN1` role) and
`c²-a²-b² < 0`, so the arctangent is negative and `arclength < pi/2`. -/
theorem arclength222h0_p26 : arcLength 2 2 (2 * h0) < Real.pi / 2 := by
  have hh0 : h0 = 1.26 := rfl
  have hy : ((2 * h0) * (2 * h0) - 2 * 2 - 2 * 2 : ℝ) = -1.6496 := by
    rw [hh0]; norm_num
  have hsqrt : Real.sqrt (upsX (2 * 2) (2 * 2) ((2 * h0) * (2 * h0)))
      = Real.sqrt 61.27881984 := by
    rw [hh0]; unfold upsX; norm_num
  have hbranch : |((2 * h0) * (2 * h0) - 2 * 2 - 2 * 2 : ℝ)|
      < Real.sqrt (upsX (2 * 2) (2 * 2) ((2 * h0) * (2 * h0))) := by
    rw [hy, hsqrt, abs_of_neg (by norm_num : (-1.6496 : ℝ) < 0)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold arcLength atn2
  rw [if_pos hbranch, hy, hsqrt]
  have hneg : Real.arctan ((-1.6496 : ℝ) / Real.sqrt 61.27881984) < 0 := by
    rw [neg_div, Real.arctan_neg]
    linarith [Real.arctan_pos.mpr (by norm_num :
      (0 : ℝ) < 1.6496 / Real.sqrt 61.27881984)]
  linarith

/-- HOL `arclength_2h0_cstab` (AXJRPNC.hl:272).
DISCHARGED: numerically — both `atn2`s hit the first branch (`h0 = #1.26`,
`cstab = #3.01`); the sum is `pi + (negative arctangent) + (small positive
arctangent)`, and `1.0601 / sqrt 143.8… < 1.6496 / sqrt 98.9…` (squared:
`111.1 < 391.4`) folds the two arctangent terms negative via the strict
monotonicity of `arctan` (the `ATN_UPS_X_BREAKDOWN1` role). -/
theorem arclength_2h0_cstab_p26 :
    arcLength 2 2 (2 * h0) + arcLength 2 2 cstab < Real.pi := by
  have hh0 : h0 = 1.26 := rfl
  have hcst : cstab = 3.01 := by norm_num [cstab]
  have hy1 : ((2 * h0) * (2 * h0) - 2 * 2 - 2 * 2 : ℝ) = -1.6496 := by
    rw [hh0]; norm_num
  have hy2 : (cstab * cstab - 2 * 2 - 2 * 2 : ℝ) = 1.0601 := by
    rw [hcst]; norm_num
  have hs1 : Real.sqrt (upsX (2 * 2) (2 * 2) ((2 * h0) * (2 * h0)))
      = Real.sqrt 61.27881984 := by rw [hh0]; unfold upsX; norm_num
  have hs2 : Real.sqrt (upsX (2 * 2) (2 * 2) (cstab * cstab))
      = Real.sqrt 62.87618799 := by rw [hcst]; unfold upsX; norm_num
  have hb1 : |((2 * h0) * (2 * h0) - 2 * 2 - 2 * 2 : ℝ)|
      < Real.sqrt (upsX (2 * 2) (2 * 2) ((2 * h0) * (2 * h0))) := by
    rw [hy1, hs1, abs_of_neg (by norm_num : (-1.6496 : ℝ) < 0), neg_neg]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  have hb2 : |(cstab * cstab - 2 * 2 - 2 * 2 : ℝ)|
      < Real.sqrt (upsX (2 * 2) (2 * 2) (cstab * cstab)) := by
    rw [hy2, hs2, abs_of_pos (by norm_num : (0 : ℝ) < 1.0601)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold arcLength atn2
  rw [if_pos hb1, if_pos hb2, hy1, hy2, hs1, hs2]
  have hneg : Real.arctan ((-1.6496 : ℝ) / Real.sqrt 61.27881984) < 0 := by
    rw [neg_div, Real.arctan_neg]
    linarith [Real.arctan_pos.mpr (by norm_num :
      (0 : ℝ) < 1.6496 / Real.sqrt 61.27881984)]
  have hmono : Real.arctan ((1.0601 : ℝ) / Real.sqrt 62.87618799)
      < -Real.arctan ((-1.6496 : ℝ) / Real.sqrt 61.27881984) := by
    rw [neg_div, Real.arctan_neg, neg_neg, Real.arctan_lt_arctan_iff]
    refine lt_of_mul_lt_mul_left ?_
      (mul_nonneg (Real.sqrt_nonneg 62.87618799) (Real.sqrt_nonneg 61.27881984))
    have hkey : (Real.sqrt 62.87618799 * Real.sqrt 61.27881984)
        * (1.0601 / Real.sqrt 62.87618799)
        < (Real.sqrt 62.87618799 * Real.sqrt 61.27881984)
          * (1.6496 / Real.sqrt 61.27881984) := by
      have hc1 : (Real.sqrt 62.87618799 * Real.sqrt 61.27881984)
          * (1.0601 / Real.sqrt 62.87618799)
          = 1.0601 * Real.sqrt 61.27881984 := by field_simp
      have hc2 : (Real.sqrt 62.87618799 * Real.sqrt 61.27881984)
          * (1.6496 / Real.sqrt 61.27881984)
          = 1.6496 * Real.sqrt 62.87618799 := by field_simp
      rw [hc1, hc2]
      have h1 : 0 ≤ (1.0601 : ℝ) * Real.sqrt 61.27881984 := by positivity
      have h2 : 0 ≤ (1.6496 : ℝ) * Real.sqrt 62.87618799 := by positivity
      rw [mul_self_lt_mul_self_iff h1 h2,
        show (1.0601 : ℝ) * Real.sqrt 61.27881984 * (1.0601 * Real.sqrt 61.27881984)
          = 1.0601 ^ 2 * 61.27881984 from by
            rw [← pow_two, mul_pow,
              Real.sq_sqrt (show (0 : ℝ) ≤ 61.27881984 by norm_num)],
        show (1.6496 : ℝ) * Real.sqrt 62.87618799 * (1.6496 * Real.sqrt 62.87618799)
          = 1.6496 ^ 2 * 62.87618799 from by
            rw [← pow_two, mul_pow,
              Real.sq_sqrt (show (0 : ℝ) ≤ 62.87618799 by norm_num)]]
      norm_num
    linarith [hkey]
  linarith

/-- HOL `DIST_LE2_BB_CASSE_4` (AXJRPNC.hl:180).
DISCHARGED: the 21st `isScsV39` conjunct gives at most `6 - 4 = 2` bad
indices, so not all four residue edges can have `b > 2*h0`; an edge with
`b ≤ 2*h0` bounds the corresponding `‖v i - v (i+1)‖` via `BBsV39`. -/
theorem DIST_LE2_BB_CASSE_4_p26 (s : ScsV39) (v : ℕ → V3) (hk : s.k = 4)
    (hv : BBsV39 s v) (hs : isScsV39 s) : ∃ i, ‖v i - v (i + 1)‖ ≤ 2 * h0 := by
  unfold isScsV39 at hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcard⟩ := hs
  rw [hk] at hcard
  have hfin : ({i | i < 4 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio 4) fun x hx => hx.1
  by_contra hcon
  push_neg at hcon
  have hsub : (Set.Iio 4 : Set ℕ) ⊆
      {i | i < 4 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} := by
    intro r hr
    refine ⟨hr, Or.inl ?_⟩
    have hd : ‖v r - v (r + 1)‖ ≤ s.b r (r + 1) := by
      rw [← dist_eq_norm]; exact (hv.2.2.1 r (r + 1)).2
    exact lt_of_lt_of_le (hcon r) hd
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_Iio_nat] at hle
  omega

/-- HOL `DIST_LE2_BB_CASSE_5` (AXJRPNC.hl:298).
DISCHARGED: the bad-index set has at most one element (`ncard + 5 ≤ 6`); if
both edges `i, i+1` had `> 2*h0` b-bounds, their two distinct residues would
both be bad, by `periodic2_mod_eq_p26`/`periodic_mod_eq_p23` transfer. -/
theorem DIST_LE2_BB_CASSE_5_p26 (s : ScsV39) (v : ℕ → V3) (hk : s.k = 5)
    (hv : BBsV39 s v) (hs : isScsV39 s) (i : ℕ) :
    ‖v i - v (i + 1)‖ ≤ 2 * h0 ∨ ‖v (i + 1) - v (i + 2)‖ ≤ 2 * h0 := by
  unfold isScsV39 at hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hpb, _, _, _, _, _, _, _, _, _, hcard⟩ := hs
  rw [hk] at hpb hcard
  have h5 : 0 < 5 := by norm_num
  have hbmod : ∀ u : ℕ, s.b (u % 5) ((u % 5) + 1) = s.b u (u + 1) := by
    intro u
    have h1 := periodic2_mod_eq_p26 h5 hpb (u % 5) ((u % 5) + 1)
    have h2 := periodic2_mod_eq_p26 h5 hpb u (u + 1)
    rw [Nat.mod_mod, show ((u % 5) + 1) % 5 = (u + 1) % 5 from
      Nat.ModEq.add_right 1 (Nat.mod_modEq u 5)] at h1
    exact h1.trans h2.symm
  have hp5 : Periodic v 5 := by
    have := hv.2.1
    rw [hk] at this
    exact this
  have hvmod : ∀ u : ℕ, dist (v (u % 5)) (v ((u % 5) + 1)) = dist (v u) (v (u + 1)) := by
    intro u
    have h1 : v (u % 5) = v u := periodic_mod_eq_p23 hp5 u
    have h2 : v ((u % 5) + 1) = v (u + 1) := by
      rw [← periodic_mod_eq_p23 hp5 (u + 1), ← Nat.ModEq.add_right 1 (Nat.mod_modEq u 5),
        periodic_mod_eq_p23 hp5 (u % 5 + 1)]
    rw [h1, h2]
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2⟩ := hcon
  have hbad : ∀ (u : ℕ), 2 * h0 < ‖v u - v (u + 1)‖ →
      (u % 5 : ℕ) ∈ {i | i < 5 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} := by
    intro u hcu
    refine ⟨Nat.mod_lt _ h5, Or.inl ?_⟩
    have hd : dist (v (u % 5)) (v ((u % 5) + 1)) ≤ s.b (u % 5) ((u % 5) + 1) :=
      (hv.2.2.1 (u % 5) ((u % 5) + 1)).2
    have hgt : 2 * h0 < dist (v (u % 5)) (v ((u % 5) + 1)) := by
      rw [hvmod u, dist_eq_norm]
      exact hcu
    exact lt_of_lt_of_le hgt hd
  have hpair : ({(i % 5), ((i + 1) % 5)} : Set ℕ) ⊆
      {i | i < 5 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} := by
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hbad i c1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hbad (i + 1) c2
  have hfin : ({i | i < 5 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio 5) fun x hx => hx.1
  have hle := Set.ncard_le_ncard hpair hfin
  rw [Set.ncard_pair (show (i % 5 : ℕ) ≠ (i + 1) % 5 from succ_mod_ne_p26 (by norm_num))] at hle
  omega

/-! ### Lane m1a-root-w3: the distance-2 lunar elimination (`helim` of
`w5sg3b_axjrpnc_p26`) -/

/-- Positive convex combinations of two distinct points lie in their convex
hull (`conv0_p2` ⊆ `convexHull`). -/
private theorem w3sg_conv0_subset_convexHull {a b : V3} (hab : a ≠ b) :
    conv0_p2 ({a, b} : Set V3) ⊆ convexHull ℝ ({a, b} : Set V3) := by
  intro x hx
  simp only [conv0_p2, Set.mem_setOf_eq] at hx
  obtain ⟨f, hfin, hvec, hpos, hsum⟩ := hx
  have hEq : hfin.toFinset = ({a, b} : Finset V3) := by ext w; simp [hab]
  rw [hEq] at hvec hsum
  simp only [Finset.sum_insert (by simp [hab] : ¬(a ∈ ({b} : Finset V3))),
    Finset.sum_singleton] at hvec hsum
  have hfa : 0 < f a := hpos a (by simp [hab])
  have hfb : 0 < f b := hpos b (by simp [hab])
  rw [convexHull_pair, mem_segment_iff_div]
  refine ⟨f a, f b, le_of_lt hfa, le_of_lt hfb, by linarith, ?_⟩
  rw [hsum, div_one, div_one]
  exact hvec.symm

/-- Distance-2 helper: the LocalAuto1-proved `OIQKKEP_concl` (faithful
twin, standard axioms), restated here because Section C is below Section B. -/
private theorem w3sg_oiqkkep (u v : V3) (c : ℝ) (hu : u ∈ ballAnnulus)
    (hv : v ∈ ballAnnulus) (hc : c < 4) (hdist : dist u v ≤ c) (h2 : 2 ≤ dist u v) :
    arcV 0 u v ≤ arcLength 2 2 c :=
  OIQKKEP_concl u v c hu hv hc h2 hdist

/-- Distance-2 helper: the LocalAuto1-proved `PPBTYDQ_concl`. -/
private theorem w3sg_ppbtydq (u v p : V3) (hu : ¬Collinear ℝ ({0, v, p} : Set V3))
    (hv : ¬Collinear ℝ ({0, u, p} : Set V3))
    (harc : arcV 0 u p + arcV 0 p v < Real.pi) :
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3)) :=
  PPBTYDQ_concl u v p hu hv harc

/-- A distance-2 lunar pair is impossible when one of the two intervening
edges has length `≤ 2*h0` (all edges are `≤ cstab` by `hb`): the two `arcV`
bounds sum to `< π`, `PPBTYDQ` forbids `0` from the convex hull, while the
fan's `FAN_SUB_NOT_EQ_COLL_IN_CONV0` puts `0` there. -/
private theorem w3sg_d2_kill_p26 (s : ScsV39) (v : ℕ → V3) (i : ℕ)
    (hs : isScsV39 s) (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : MMsV39 s v)
    (h4 : 4 ≤ s.k)
    (hshort : ‖v i - v (i + 1)‖ ≤ 2 * h0 ∨ ‖v (i + 1) - v (i + 2)‖ ≤ 2 * h0) :
    ¬ Lunar (v i) (v (i + 2)) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)) := by
  intro hlun
  have hBB : BBsV39 s v := w5sg_mms_bbs_p26 s v hv
  have hcfan : ConvexLocalFan (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))
      (Set.range fun l : ℕ => (v l, v (l + 1))) :=
    hBB.2.2.2.resolve_left (by omega)
  have hclf2 := w5sg_clf2_p26 hcfan
  obtain ⟨hlf, hFAN⟩ := CVLF_LF_F hclf2
  have hedge : ∀ l, (v l, v (l + 1)) ∈
      (Set.range fun l : ℕ => (v l, v (l + 1))) := fun l => ⟨l, rfl⟩
  have hnc1 : ¬ Collinear ℝ ({0, v i, v (i + 1)} : Set V3) :=
    LOCAL_FAN_IN_FF_NOT_COLLINEAR (d := (v i, v (i + 1))) hlf (hedge i)
  have hnc2 : ¬ Collinear ℝ ({0, v (i + 1), v (i + 2)} : Set V3) :=
    LOCAL_FAN_IN_FF_NOT_COLLINEAR (d := (v (i + 1), v (i + 2))) hlf (hedge (i + 1))
  have hnc2' : ¬ Collinear ℝ ({0, v (i + 2), v (i + 1)} : Set V3) := by
    rwa [show ({0, v (i + 2), v (i + 1)} : Set V3) = {0, v (i + 1), v (i + 2)} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hmem_ann : ∀ l, v l ∈ ballAnnulus := fun l => hBB.1 ⟨l, rfl⟩
  have hdist2 : ∀ l, 2 ≤ dist (v l) (v (l + 1)) := by
    intro l
    rw [dist_eq_norm]
    exact DIST_EDGE_IN_BB_LE_2_p26 s v hBB hs l
  have hdistc : ∀ l, dist (v l) (v (l + 1)) ≤ cstab := by
    intro l
    rw [dist_eq_norm]
    exact NORM_V_IN_BB_LE_CSTAB_p26 s v hb hBB l
  have h2h04 : 2 * h0 < (4:ℝ) := by norm_num [h0]
  have hcst4 : cstab < (4:ℝ) := by norm_num [cstab]
  have hsum : arcV 0 (v i) (v (i + 1)) + arcV 0 (v (i + 1)) (v (i + 2)) < Real.pi := by
    have h := arclength_2h0_cstab_p26
    rcases hshort with h1 | h1
    · have hb1 : arcV 0 (v i) (v (i + 1)) ≤ arcLength 2 2 (2 * h0) :=
        w3sg_oiqkkep _ _ _ (hmem_ann i) (hmem_ann (i + 1)) h2h04
          (by rw [dist_eq_norm]; exact h1) (hdist2 i)
      have hb2' : arcV 0 (v (i + 1)) (v (i + 2)) ≤ arcLength 2 2 cstab :=
        w3sg_oiqkkep _ _ _ (hmem_ann (i + 1)) (hmem_ann (i + 2)) hcst4
          (hdistc (i + 1)) (hdist2 (i + 1))
      linarith
    · have hb1' : arcV 0 (v i) (v (i + 1)) ≤ arcLength 2 2 cstab :=
        w3sg_oiqkkep _ _ _ (hmem_ann i) (hmem_ann (i + 1)) hcst4
          (hdistc i) (hdist2 i)
      have hb2 : arcV 0 (v (i + 1)) (v (i + 2)) ≤ arcLength 2 2 (2 * h0) :=
        w3sg_oiqkkep _ _ _ (hmem_ann (i + 1)) (hmem_ann (i + 2)) h2h04
          (by rw [dist_eq_norm]; exact h1) (hdist2 (i + 1))
      linarith
  have hconv : (0:V3) ∈ convexHull ℝ ({v i, v (i + 2)} : Set V3) := by
    have hsub : ({v i, v (i + 2)} : Set V3) ⊆ Set.range v := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨i, rfl⟩
      · rw [Set.mem_singleton_iff] at hz
        exact ⟨i + 2, hz.symm⟩
    have hne : v i ≠ v (i + 2) := hlun.2.2.1
    have hcol : Collinear ℝ ({0, v i, v (i + 2)} : Set V3) := hlun.2.2.2
    exact w3sg_conv0_subset_convexHull hne
      (FAN_SUB_NOT_EQ_COLL_IN_CONV0 hFAN hsub hne hcol)
  exact (w3sg_ppbtydq (v i) (v (i + 2)) (v (i + 1)) hnc2' hnc1 hsum) hconv

/-- `k = 4`: one of the two arcs between `p` and `p+2` carries an edge of
length `≤ 2*h0`.  At most two residues are bad (`ncard + 4 ≤ 6`); if both
edges of the first arc are bad, both edges of the second are good. -/
private theorem w3sg_short_k4_p26 (s : ScsV39) (v : ℕ → V3) (p : ℕ)
    (hs : isScsV39 s) (hv : MMsV39 s v) (hk : s.k = 4) :
    (‖v p - v (p + 1)‖ ≤ 2 * h0 ∨ ‖v (p + 1) - v (p + 2)‖ ≤ 2 * h0) ∨
    (‖v (p + 2) - v (p + 3)‖ ≤ 2 * h0 ∨ ‖v (p + 3) - v (p + 4)‖ ≤ 2 * h0) := by
  obtain ⟨-, hk3, -, -, -, -, -, hpa, -, -, hpb, -, -, -, -, -, -, -, -, -, hcard⟩ := hs
  have hBB : BBsV39 s v := w5sg_mms_bbs_p26 s v hv
  have hper : Periodic v 4 := hk ▸ hBB.2.1
  rw [hk] at hpb hcard
  set BAD : Set ℕ :=
    {i | i < 4 ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} with hBADdef
  have hcardBAD : BAD.ncard ≤ 2 := by
    omega
  have hfinBAD : BAD.Finite := by
    rw [hBADdef]
    exact Set.Finite.subset (Set.finite_Iio 4) (fun x hx => hx.1)
  have hshift : ∀ l r : ℕ, v (l + r) = v ((l % 4 + r) % 4) := by
    intro l r
    rw [← periodic_mod_eq_p23 hper (l + r)]
    congr 1
    exact Nat.ModEq.add_right r (Nat.mod_modEq l 4).symm
  have hbad : ∀ l, 2 * h0 < ‖v l - v (l + 1)‖ → (l % 4) ∈ BAD := by
    intro l hl
    have hb_eq : s.b l (l + 1) = s.b (l % 4) ((l % 4) + 1) := by
      have h1 := periodic2_mod_eq_p26 (by norm_num : 0 < 4) hpb l (l + 1)
      have hm : (l + 1) % 4 = (l % 4 + 1) % 4 :=
        Nat.ModEq.add_right 1 (Nat.mod_modEq l 4).symm
      rw [hm] at h1
      have h2 : s.b (l % 4) (((l % 4) + 1) % 4) =
          s.b (l % 4) ((l % 4) + 1) := by
        have h3 := periodic2_mod_eq_p26 (by norm_num : 0 < 4) hpb (l % 4) ((l % 4) + 1)
        rw [Nat.mod_mod] at h3
        exact h3.symm
      exact h1.trans h2
    have hdist_eq : dist (v l) (v (l + 1)) = dist (v (l % 4)) (v ((l % 4) + 1)) := by
      rw [dist_eq_norm, dist_eq_norm]
      have hv_l : v l = v (l % 4) := (periodic_mod_eq_p23 hper l).symm
      have hv_l1 : v (l + 1) = v ((l % 4 + 1) % 4) := hshift l 1
      have hv_r1 : v ((l % 4) + 1) = v ((l % 4 + 1) % 4) :=
        (periodic_mod_eq_p23 hper ((l % 4) + 1)).symm
      rw [hv_l, hv_l1, hv_r1]
    have hdle : dist (v l) (v (l + 1)) ≤ s.b l (l + 1) := (hBB.2.2.1 l (l + 1)).2
    rw [hb_eq] at hdle
    rw [← dist_eq_norm] at hl
    rw [hdist_eq] at hl hdle
    refine ⟨Nat.mod_lt _ (by norm_num : 0 < 4), Or.inl ?_⟩
    exact lt_of_lt_of_le hl hdle
  have hgood : ∀ l, (l % 4) ∉ BAD → ‖v l - v (l + 1)‖ ≤ 2 * h0 := by
    intro l hmem
    by_contra hgt
    push_neg at hgt
    exact hmem (hbad l hgt)
  -- residue arithmetic helpers
  have hm1 : (p + 1) % 4 = (p % 4 + 1) % 4 := Nat.ModEq.add_right 1 (Nat.mod_modEq p 4).symm
  have hm2 : (p + 2) % 4 = (p % 4 + 2) % 4 := Nat.ModEq.add_right 2 (Nat.mod_modEq p 4).symm
  have hm3 : (p + 3) % 4 = (p % 4 + 3) % 4 := Nat.ModEq.add_right 3 (Nat.mod_modEq p 4).symm
  have hp4 : p % 4 < 4 := Nat.mod_lt _ (by norm_num : 0 < 4)
  have h12 : (p % 4) ≠ ((p + 1) % 4) := by
    rw [hm1]
    exact ne_step_mod_p27 (r := p % 4) (c := 1) (by norm_num) (by norm_num) hp4
  have h13 : (p % 4) ≠ ((p + 2) % 4) := by
    rw [hm2]
    exact ne_step_mod_p27 (r := p % 4) (c := 2) (by norm_num) (by norm_num) hp4
  have h14 : (p % 4) ≠ ((p + 3) % 4) := by
    rw [hm3]
    exact ne_step_mod_p27 (r := p % 4) (c := 3) (by norm_num) (by norm_num) hp4
  have hq1 : (p + 2) % 4 = ((p + 1) % 4 + 1) % 4 := by
    rw [show p + 2 = (p + 1) + 1 from by omega]
    exact Nat.ModEq.add_right 1 (Nat.mod_modEq (p + 1) 4).symm
  have hq2 : (p + 3) % 4 = ((p + 1) % 4 + 2) % 4 := by
    rw [show p + 3 = (p + 1) + 2 from by omega]
    exact Nat.ModEq.add_right 2 (Nat.mod_modEq (p + 1) 4).symm
  have hq4 : (p + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num : 0 < 4)
  have h23 : ((p + 1) % 4) ≠ ((p + 2) % 4) := by
    rw [hq1]
    exact ne_step_mod_p27 (r := (p + 1) % 4) (c := 1) (by norm_num) (by norm_num) hq4
  have h24 : ((p + 1) % 4) ≠ ((p + 3) % 4) := by
    rw [hq2]
    exact ne_step_mod_p27 (r := (p + 1) % 4) (c := 2) (by norm_num) (by norm_num) hq4
  have htriple : ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      ({a, b, c} : Set ℕ).ncard = 3 := by
    intro a b c hab hac hbc
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
  by_cases hA1 : (p % 4) ∈ BAD
  · by_cases hA2 : ((p + 1) % 4) ∈ BAD
    · -- both first-arc edges are bad ⇒ both second-arc edges are good
      right
      have hB1 : ((p + 2) % 4) ∉ BAD := by
        intro hmem
        have hsub : ({(p % 4), ((p + 1) % 4), ((p + 2) % 4)} : Set ℕ) ⊆ BAD := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact hA1
          · exact hA2
          · exact hmem
        have hle := Set.ncard_le_ncard hsub hfinBAD
        have h3 := htriple _ _ _ h12 h13 h23
        omega
      have hB2 : ((p + 3) % 4) ∉ BAD := by
        intro hmem
        have hsub : ({(p % 4), ((p + 1) % 4), ((p + 3) % 4)} : Set ℕ) ⊆ BAD := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact hA1
          · exact hA2
          · exact hmem
        have hle := Set.ncard_le_ncard hsub hfinBAD
        have h3 := htriple _ _ _ h12 h14 h24
        omega
      exact Or.inl (by simpa [show p + 2 + 1 = p + 3 from by omega] using hgood (p + 2) hB1)
    · left
      exact Or.inr (hgood (p + 1) hA2)
  · left
    exact Or.inl (hgood p hA1)

/-- The `¬ Lunar (v p) (v (p+2))` premise consumed by
`w5sg3b_axjrpnc_p26`, for `k = 4, 5, 6`. -/
private theorem w3sg_helim_p26 (s : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : MMsV39 s v)
    (h4 : 4 ≤ s.k) :
    ∀ p, ¬ Lunar (v p) (v (p + 2)) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)) := by
  intro p hlun
  have hBB : BBsV39 s v := w5sg_mms_bbs_p26 s v hv
  have hk6 : s.k ≤ 6 := hs.2.2.1
  rcases (by omega : s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with hk4 | hk5 | hk6
  · have hshort := w3sg_short_k4_p26 s v p hs hv hk4
    have hper : Periodic v 4 := hk4 ▸ hBB.2.1
    rcases hshort with hA | hB
    · exact w3sg_d2_kill_p26 s v p hs hb hv h4 hA hlun
    · have hlun2 : Lunar (v (p + 2)) (v (p + 2 + 2)) (Set.range v)
          (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3)) := by
        rw [show p + 2 + 2 = p + 4 from by omega, hper p]
        exact (LUNAR_COMM (v p) (v (p + 2)) (Set.range v)
          (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))).mp hlun
      have hB' : ‖v (p + 2) - v (p + 2 + 1)‖ ≤ 2 * h0 ∨
          ‖v (p + 2 + 1) - v (p + 2 + 2)‖ ≤ 2 * h0 := by
        simpa [show p + 2 + 1 = p + 3 from by omega,
          show p + 2 + 2 = p + 4 from by omega] using hB
      exact w3sg_d2_kill_p26 s v (p + 2) hs hb hv h4 hB' hlun2
  · exact w3sg_d2_kill_p26 s v p hs hb hv h4
      (DIST_LE2_BB_CASSE_5_p26 s v hk5 hBB hs p) hlun
  · exact w3sg_d2_kill_p26 s v p hs hb hv h4
      (Or.inl (DIST_LE_2h0_IN_CASES_6_p26 s v hk6 hBB hs p)) hlun

/-- HOL `AXJRPNC` (AXJRPNC.hl:380).  DISCHARGED (2026-11-05, lane
m1a-root-w3): the private `w5sg3b_axjrpnc_p26` carries the whole case bash
except the distance-2 lunar elimination `helim`; `w3sg_helim_p26` proves it
from the now-standard `OIQKKEP_p26` / `PPBTYDQ_p26` + `arclength222h0_p26`
(`k = 3` dies on `IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23`). -/
theorem AXJRPNC_p26 (s : ScsV39) (v : ℕ → V3) (i j : ℕ)
    (hs : isScsV39 s) (hbasic : scsBasicV39 s)
    (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : MMsV39 s v)
    (hlunar : Lunar (v i) (v j) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))) :
    s.k = 6 ∧ v j = v (i + 3) := by
  by_cases hk3 : s.k = 3
  · exfalso
    have hBB : BBsV39 s v := w5sg_mms_bbs_p26 s v hv
    obtain ⟨hnc1, hnc2, hnc3⟩ := IS_SCS_NOT_COLLINEAR_BBs_CASE_3_p23 s v hs hk3 hBB
    have hper : Periodic v 3 := hk3 ▸ hBB.2.1
    have hswap : ∀ x y : ℕ, ({0, v x, v y} : Set V3) = {0, v y, v x} := by
      intro x y
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hnc : ∀ a b : ℕ, a < 3 → b < 3 → a ≠ b →
        ¬ Collinear ℝ ({0, v a, v b} : Set V3) := by
      intro a b ha hb hab
      have hcases : (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨
          (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hswap 0 1]; exact hnc2
      · rw [hswap 0 2]; exact hnc3
      · exact hnc2
      · exact hnc1
      · exact hnc3
      · rw [hswap 2 1]; exact hnc1
    have hcol : Collinear ℝ ({0, v (i % 3), v (j % 3)} : Set V3) := by
      have h := hlunar.2.2.2
      rwa [← periodic_mod_eq_p23 hper i, ← periodic_mod_eq_p23 hper j] at h
    have hne : v (i % 3) ≠ v (j % 3) := by
      have h := hlunar.2.2.1
      rwa [← periodic_mod_eq_p23 hper i, ← periodic_mod_eq_p23 hper j] at h
    have hres : i % 3 ≠ j % 3 := fun h => hne (by rw [h])
    exact hnc (i % 3) (j % 3) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      hres hcol
  · have h4 : 4 ≤ s.k := by
      have h3 := hs.2.1
      have h6 := hs.2.2.1
      omega
    exact w5sg3b_axjrpnc_p26 s v i j hs hbasic hb hv hlunar
      (w3sg_helim_p26 s v hs hb hv h4) h4
/-! ## Section C: PPBTYDQ -/

/-! ### `_p26` row/flatten helpers for the GBYCPXS fills (2026-09-18)

The `B_SY1_p4` body set encodes a vertex family `v : Fin m → V3` by the
`matvec` flattening `i ↦ v ⟨i/3⟩ ⟨i%3⟩`; `vecmatsV3_p4` inverts it.  These
private lemmas give the 1-based-row ↔ 0-based-vertex bridge that plays the
role of HOL `INJ_ROW_B_SY` (the LocalAuto9 twin lives on the other side of
the `atn2` split and is not importable here). -/

private theorem encApp_p26 {m : ℕ} (v : Fin m → V3) (r : Fin m) (k : Fin 3)
    (x : ℕ) (hx : x = r * 3 + k) :
    (v ⟨x / 3, ((Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr
        (by rw [hx]; exact INDEX_VECMAT r k))⟩ : Fin 3 → ℝ)
      ⟨x % 3, Nat.mod_lt _ (by norm_num : (0:ℕ) < 3)⟩
      = (v r).ofLp k := by
  have hr : (⟨x / 3, ((Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr
      (by rw [hx]; exact INDEX_VECMAT r k))⟩ : Fin m) = r := by
    refine Fin.ext ?_
    show x / 3 = r.val
    rw [hx]
    exact (div_mod_row (m := m) (n := 3) (by norm_num) (r : ℕ) (k : ℕ) r.isLt k.isLt).1
  have hk : (⟨x % 3, Nat.mod_lt _ (by norm_num : (0:ℕ) < 3)⟩ : Fin 3) = k := by
    refine Fin.ext ?_
    show x % 3 = k.val
    rw [hx]
    exact (div_mod_row (m := m) (n := 3) (by norm_num) (r : ℕ) (k : ℕ) r.isLt k.isLt).2
  rw [hr, hk]

private theorem rowId_p26 {m : ℕ} {v : Fin m → V3} {l : FinVec m 3}
    (hvl : (fun w : Fin m → V3 => fun i : Fin (m * 3) =>
        (v ⟨(i : ℕ) / 3, (Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr i.isLt⟩ :
          Fin 3 → ℝ) ⟨(i : ℕ) % 3, Nat.mod_lt (i : ℕ) (by norm_num : 0 < 3)⟩) v = l)
    (r : Fin m) : vecmatsV3_p4 l r = v r := by
  have h : (WithLp.ofLp (vecmatsV3_p4 l r) : Fin 3 → ℝ) = WithLp.ofLp (v r) := by
    show vecmats_p4 l r = _
    rw [← hvl]
    funext k
    exact encApp_p26 v r k (finProdEquiv m 3 (⟨r, k⟩)) (finProdEquiv_val r k)
  exact (WithLp.equiv (2 : ENNReal) (Fin 3 → ℝ)).injective h

private theorem fIterateSuccMod_p26 {k : ℕ} {f : ℕ → ℕ} (hf : ∀ j, f j = (j + 1) % k)
    (hk0 : 0 < k) (j : ℕ) : f^[k] j = j % k := by
  have key : ∀ n j : ℕ, 0 < n → f^[n] j = (j + n) % k := by
    intro n
    induction n with
    | zero => intro j hn; exact absurd hn (Nat.not_lt_zero (0:ℕ))
    | succ n ih =>
        intro j hn
        rcases Nat.eq_zero_or_pos n with h0 | hp
        · rw [h0]
          simp [hf]
        · rw [Function.iterate_succ_apply, hf, ih ((j + 1) % k) hp, Nat.mod_add_mod]
          congr 1
          ring
  rw [key k j hk0, Nat.add_mod_right]

private theorem ballUb_p26 {x : V3} (hx : x ∈ ballAnnulus) : ‖x‖ ≤ 2 * h0 := by
  have hd : dist x 0 ≤ 2 * h0 := Metric.mem_closedBall.mp hx.1
  rwa [dist_zero_right] at hd

private theorem setSum_le_of_le_p26 {α : Type*} {A : Set α} (hA : A.Finite) {f g : α → ℝ}
    (h : ∀ x ∈ A, f x ≤ g x) : setSum A f ≤ setSum A g := by
  simp only [setSum, dif_pos hA]
  exact Finset.sum_le_sum (fun x hx => h x (hA.mem_toFinset.mp hx))

private theorem setSum_nonneg_of_nonneg_p26 {α : Type*} {A : Set α} (hA : A.Finite)
    {f : α → ℝ} (h : ∀ x ∈ A, 0 ≤ f x) : 0 ≤ setSum A f := by
  simp only [setSum, dif_pos hA]
  exact Finset.sum_nonneg (fun x hx => h x (hA.mem_toFinset.mp hx))

private theorem setSum_empty_p26 {α : Type*} (f : α → ℝ) : setSum (∅ : Set α) f = 0 := by
  simp [setSum]

private theorem setSum_singleton_p26 {α : Type*} [DecidableEq α] {a : α} (f : α → ℝ) :
    setSum ({a} : Set α) f = f a := by
  simp [setSum]

/-- HOL `BBPRIME_IMP_BB` (PPBTYDQ.hl:402). -/
theorem BBPRIME_IMP_BB_p26 (s : ScsV39) (w : ℕ → V3) (h : w ∈ BBprimeV39 s) :
    BBsV39 s w := by
  exact h.1

/-- HOL `MXQTIED_TAU_DSV` (PPBTYDQ.hl:273). -/
theorem MXQTIED_TAU_DSV_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1)) : dsvV39 s' v = dsvV39 s v := by
  have hJ : s.J = fun _ _ => False := funext fun i => funext fun j => hb.2 i j
  have hJ' : s'.J = fun _ _ => False := funext fun i => funext fun j => hb'.2 i j
  have hdsv : dsvV39 s v = s.d := dsv_J_empty s v hJ
  have hdsv' : dsvV39 s' v = s'.d := dsv_J_empty s' v hJ'
  rw [hdsv', hdsv, hd]

/-- HOL `MXQTIED_TAU` (PPBTYDQ.hl:265). -/
theorem MXQTIED_TAU_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1)) : taustarV39 s' v = taustarV39 s v := by
  have hJ : s.J = fun _ _ => False := funext fun i => funext fun j => hb.2 i j
  have hJ' : s'.J = fun _ _ => False := funext fun i => funext fun j => hb'.2 i j
  have hdsv : dsvV39 s v = s.d := dsv_J_empty s v hJ
  have hdsv' : dsvV39 s' v = s'.d := dsv_J_empty s' v hJ'
  unfold taustarV39
  rw [hk, hdsv', hdsv, hd]

/-- HOL `SCS_BASIC_DSV` (PPBTYDQ.hl:516). -/
theorem SCS_BASIC_DSV_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hds : s.d ≤ s'.d) : dsvV39 s v ≤ dsvV39 s' v := by
  have hJ : s.J = fun _ _ => False := funext fun i => funext fun j => hb.2 i j
  have hJ' : s'.J = fun _ _ => False := funext fun i => funext fun j => hb'.2 i j
  have hdsv : dsvV39 s v = s.d := dsv_J_empty s v hJ
  have hdsv' : dsvV39 s' v = s'.d := dsv_J_empty s' v hJ'
  rw [hdsv, hdsv']
  exact hds

/-- HOL `SCS_BASIC_TAUSTAR` (PPBTYDQ.hl:529). -/
theorem SCS_BASIC_TAUSTAR_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hds : s.d ≤ s'.d) : taustarV39 s' v ≤ taustarV39 s v := by
  have hdsv : dsvV39 s v ≤ dsvV39 s' v := SCS_BASIC_DSV_p26 s s' v hs hs' hb hb' hk hds
  unfold taustarV39
  rw [hk]
  by_cases h3 : s'.k ≤ 3
  · simp [h3]
    nlinarith
  · simp [h3]
    nlinarith

/-- HOL `TAUSTAR_LE_0_XWNHLMD` (PPBTYDQ.hl:543). -/
theorem TAUSTAR_LE_0_XWNHLMD_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v) (hds : s.d ≤ s'.d) :
    taustarV39 s' v < 0 := by
  have hmm : taustarV39 s v < 0 := hv.1.1.2.2
  have hle : taustarV39 s' v ≤ taustarV39 s v :=
    SCS_BASIC_TAUSTAR_p26 s s' v hs hs' hb hb' hk hds
  exact lt_of_le_of_lt hle hmm

/-- HOL `MXQTIED_INDEX` (PPBTYDQ.hl:297). -/
theorem MXQTIED_INDEX_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : BBsV39 s' v) (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) :
    BBindexV39 s' v = BBindexV39 s v := by
  unfold BBindexV39
  congr 1
  ext i
  simp [hk, ha]

/-- HOL `MXQTIED_BB` (PPBTYDQ.hl:282). -/
theorem MXQTIED_BB_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : BBsV39 s' v) (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : BBsV39 s v := by
  constructor
  · exact hv.1
  · constructor
    · simpa [Periodic, ← hk] using hv.2.1
    · constructor
      · intro i j
        exact ⟨le_trans (hab i j).1 (hv.2.2.1 i j).1, le_trans (hv.2.2.1 i j).2 (hab i j).2⟩
      · rcases hv.2.2.2 with hk3 | hclf
        · rw [← hk] at hk3
          exact Or.inl hk3
        · exact Or.inr hclf

/-- `minNum` is attained and is a lower bound on a nonempty set of naturals
(the `LocalAuto1.la1minNum_spec` clone, private there). -/
private theorem w2minNum_spec (S : Set ℕ) (hne : S.Nonempty) :
    minNum S ∈ S ∧ ∀ m ∈ S, minNum S ≤ m := by
  have hex : ∃ n : ℕ, n ∈ S ∧ ∀ m ∈ S, n ≤ m :=
    ⟨sInf S, Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩
  exact Classical.epsilon_spec hex

/-- HOL `MXQTIED_PRIME` (PPBTYDQ.hl:252). Proof pending (needs
`MXQTIED_BB` / `BB_simplify` machinery for the minimising condition). -/
theorem MXQTIED_PRIME_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : v ∈ BBprimeV39 s) (hv' : BBsV39 s' v)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : v ∈ BBprimeV39 s' := by
  -- DISCHARGED (2026-11-04, lane m1a-root-w2): `MXQTIED_TAU` transfers the
  -- minimising value and `MXQTIED_BB` the `BBs` window nesting.
  refine ⟨hv', ?_, ?_⟩
  · intro w hw'
    rw [MXQTIED_TAU_p26 s s' w hs hs' hb hb' hM hk hd ha,
        MXQTIED_TAU_p26 s s' v hs hs' hb hb' hM hk hd ha]
    exact hv.2.1 w
      (MXQTIED_BB_p26 s s' w hs hs' hb hb' hM hk hd hw' ha hab)
  · rw [MXQTIED_TAU_p26 s s' v hs hs' hb hb' hM hk hd ha]
    exact hv.2.2

/-- HOL `MXQTIED_PRIME2` (PPBTYDQ.hl:241). Proof pending (needs
`MXQTIED_PRIME` / `MXQTIED_INDEX`). -/
theorem MXQTIED_PRIME2_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : v ∈ BBprime2V39 s' := by
  -- DISCHARGED (2026-11-04, lane m1a-root-w2): `MXQTIED_PRIME` for the
  -- minimality conjunct; the index conjunct is the HOL `MIN_LEAST` argument:
  -- a `BBprime s'`-member with strictly smaller `s`-index would itself be
  -- `BBprime s` (its value is squeezed by `v`'s `s`-minimality), contradicting
  -- `v`'s `BBindex_min`.
  have hvp : v ∈ BBprimeV39 s := hv.1.1
  have hvp' : v ∈ BBprimeV39 s' :=
    MXQTIED_PRIME_p26 s s' v hs hs' hb hb' hM hk hd hvp hv' ha hab
  refine ⟨hvp', ?_⟩
  by_contra hne
  have himg : (BBindexV39 s' '' BBprimeV39 s').Nonempty := ⟨_, v, hvp', rfl⟩
  have hle : BBindexMinV39 s' ≤ BBindexV39 s' v :=
    (w2minNum_spec _ himg).2 _ ⟨v, hvp', rfl⟩
  have hlt : BBindexMinV39 s' < BBindexV39 s' v :=
    lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨hmin_mem, -⟩ := w2minNum_spec _ himg
  obtain ⟨w, hw', hwidx⟩ := hmin_mem
  have hw'BB : BBsV39 s' w := by
    have h := hw'
    simp only [BBprimeV39, Set.mem_setOf_eq] at h
    exact h.1
  have hw'min : ∀ u, BBsV39 s' u → taustarV39 s' w ≤ taustarV39 s' u := by
    have h := hw'
    simp only [BBprimeV39, Set.mem_setOf_eq] at h
    exact h.2.1
  have hltw : BBindexV39 s' w < BBindexV39 s' v := by
    rw [hwidx]; exact hlt
  -- w is also `BBprime s` (squeezed between the two minimal values)
  have hwBB : BBsV39 s w :=
    MXQTIED_BB_p26 s s' w hs hs' hb hb' hM hk hd hw'BB ha hab
  have hwv : taustarV39 s w ≤ taustarV39 s v := by
    rw [← MXQTIED_TAU_p26 s s' w hs hs' hb hb' hM hk hd ha,
        ← MXQTIED_TAU_p26 s s' v hs hs' hb hb' hM hk hd ha]
    exact hw'min v hv'
  have hwneg : taustarV39 s w < 0 := lt_of_le_of_lt hwv hvp.2.2
  have hwprime : w ∈ BBprimeV39 s :=
    ⟨hwBB, fun u hu => le_trans hwv (hvp.2.1 u hu), hwneg⟩
  -- the two index equalities and `BBindex_min`
  have hbidxw : BBindexV39 s' w = BBindexV39 s w :=
    MXQTIED_INDEX_p26 s s' w hs hs' hb hb' hM hk hd hw'BB ha hab
  have hbidxv : BBindexV39 s' v = BBindexV39 s v :=
    MXQTIED_INDEX_p26 s s' v hs hs' hb hb' hM hk hd hv' ha hab
  have hlt' : BBindexV39 s w < BBindexV39 s v := by
    rw [← hbidxw, ← hbidxv]; exact hltw
  have himgs : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨_, w, hwprime, rfl⟩
  have hminle : BBindexMinV39 s ≤ BBindexV39 s w :=
    (w2minNum_spec _ himgs).2 _ ⟨w, hwprime, rfl⟩
  have hveq : BBindexV39 s v = BBindexMinV39 s := hv.1.2
  omega

/-- HOL `MXQTIED` (PPBTYDQ.hl:231). Proof pending (needs
`MXQTIED_PRIME2` / `BB_simplify` / `dsv_J_empty`). -/
theorem MXQTIED_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : v ∈ MMsV39 s' := by
  -- DISCHARGED (2026-11-04, lane m1a-root-w2): `MXQTIED_PRIME2` + the
  -- `unadorned_MMs` conversion for the basic system `s'`.
  have h2 : v ∈ BBprime2V39 s' :=
    MXQTIED_PRIME2_p26 s s' v hs hs' hb hb' hM hk hd hv hv' ha hab
  rw [unadorned_MMs_concl s' hb'.1]
  exact h2

/-- HOL `OIQKKEP` (PPBTYDQ.hl:172). Delegates to the existing
`sorry`-based `OIQKKEP_concl` in LocalAuto1. -/
theorem OIQKKEP_p26 (u v : V3) (c : ℝ) (hu : u ∈ ballAnnulus) (hv : v ∈ ballAnnulus)
    (hc : c < 4) (hdist : dist u v ≤ c) (h2 : 2 ≤ dist u v) :
    arcV 0 u v ≤ arcLength 2 2 c := by
  exact OIQKKEP_concl u v c hu hv hc h2 hdist

/-- HOL `PPBTYDQ` (PPBTYDQ.hl:92).  DISCHARGED (2026-11-05, lane
m1a-root-w3): the LocalAuto1 W5c-F1 analytic kit proves the faithful twin
`PPBTYDQ_concl` (same statement, standard axioms). -/
theorem PPBTYDQ_p26 (u v p : V3) (hu : ¬Collinear ℝ ({0, v, p} : Set V3))
    (hv : ¬Collinear ℝ ({0, u, p} : Set V3))
    (harc : arcV 0 u p + arcV 0 p v < Real.pi) :
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3)) :=
  PPBTYDQ_concl u v p hu hv harc

/-- HOL `XWNHLMD_MM` (PPBTYDQ.hl:560).
DISCHARGED (2026-09-20): the HOL proof is `TAUSTAR_LE_0_XWNHLMD` +
`SGTRNAF` (sgtrnaf.hl:166); `SGTRNAF_p27` (LocalAuto27, proved via
`UXCKFPE2_p27` ← `UXCKFPE_p24`) is now importable and `scsBasicV39 s'`
supplies its `unadornedV39 s'` side condition directly. -/
theorem XWNHLMD_MM_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v) (hds : s.d ≤ s'.d) :
    MMsV39 s' ≠ ∅ := by
  have hta : taustarV39 s' v < 0 :=
    TAUSTAR_LE_0_XWNHLMD_p26 s s' v hs hs' hb hb' hk hv hv' hds
  exact SGTRNAF_p27 s' v hs' hb'.1 hv' hta

/-- HOL `XWNHLMD` (PPBTYDQ.hl:574). -/
theorem XWNHLMD_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hds : s.d ≤ s'.d) (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v) :
    scsArrowV39 ({s} : Set ScsV39) ({s'} : Set ScsV39) := by
  unfold scsArrowV39
  constructor
  · intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact hs'
  · right
    have hnon : MMsV39 s' ≠ ∅ := XWNHLMD_MM_p26 s s' v hs hs' hb hb' hk hv hv' hds
    exact ⟨s', by simp, hnon⟩

/-! ## Section D: GBYCPXS -/

/-- HOL `SOL0_POS` (GBYCPXS.hl:59): the regular-tetrahedron solid angle
`sol0 = 3*arccos(1/3) - pi` is positive (`pi/3 < arccos(1/3)` since
`cos` is strictly decreasing on `[0,pi]` and `1/3 < cos(pi/3) = 1/2`). -/
theorem SOL0_POS_p26 : 0 < sol0 := by
  have h2 : (1 / 2 : ℝ) = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
  have h3 : Real.arccos (1 / 2) = Real.pi / 3 := by
    rw [h2]; exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h4 : Real.arccos (1 / 2) < Real.arccos (1 / 3) :=
    Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have h5 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  linarith

/-- HOL `SIGMA_SY_LE1` (GBYCPXS.hl:72). -/
theorem SIGMA_SY_LE1_p26 (s : StableSyP23) : sigmaSy_p26 s ≤ 1 := by
  unfold sigmaSy_p26
  by_cases h : earSy_p23 s
  · rw [if_pos h]
  · rw [if_neg h]
    norm_num

/-- HOL `PROPERTIES_EAR_SY` (GBYCPXS.hl:178): an ear stable system has a
singleton `J_SY` of the form `{i, f_sy s i}` with `i IN I_SY s`. -/
theorem PROPERTIES_EAR_SY_p26 (s : StableSyP23) (h : earSy_p23 s) :
    ∃ i, s.J = {({i, s.f i} : Set ℕ)} ∧ i ∈ s.I := by
  have hcard : s.J.ncard = 1 := h.2.2.1
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hcard
  have hJsub : s.J ⊆ {e | ∃ i ∈ s.I, e = {i, s.f i}} := s.stable.1.2.2.2.2.2.1
  have heJ : e ∈ s.J := by simp [he]
  obtain ⟨i, hi, hie⟩ := hJsub heJ
  refine ⟨i, ?_, hi⟩
  rw [he, hie]


/-- Aux for `SING_J1_SY_p26`: with `J_SY s` the singleton `{{c, s.f c}}`
(`c < s.k`, `s.f` the successor-mod cycle, `w` the unique element of
`[1, s.k]` with `w % s.k = c`), `J1_SY s` is `{(w, w % s.k + 1)}`. -/
private theorem j1SingAux_p26 (s : StableSyP23) (w c : ℕ) (hwc : w % s.k = c)
    (hw1 : 1 ≤ w) (hwk : w ≤ s.k) (hck : c < s.k) (hk : 2 < s.k)
    (hf : ∀ i, s.f i = (i + 1) % s.k)
    (hJ : s.J = {({c, s.f c} : Set ℕ)}) :
    J1_SY_p23 s = {(w, w % s.k + 1)} := by
  have hk0 : 0 < s.k := by omega
  ext x
  simp only [J1_SY_p23, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hje, hjIcc, rfl⟩
    rw [hJ, Set.mem_singleton_iff] at hje
    have hj1 : 1 ≤ j := hjIcc.1
    have hjk : j ≤ s.k := hjIcc.2
    have hm : j % s.k ∈ ({c, s.f c} : Set ℕ) := by rw [← hje]; simp
    rcases Set.mem_insert_iff.mp hm with hjc | hjc'
    · have hmod : j % s.k = w % s.k := by rw [hjc, hwc]
      have hjw : j = w := by
        rcases Nat.lt_or_ge j s.k with hjlt | hjge
        · have hjm : j % s.k = j := Nat.mod_eq_of_lt hjlt
          rcases Nat.lt_or_ge w s.k with hwlt | hwge
          · rw [hjm, Nat.mod_eq_of_lt hwlt] at hmod
            exact hmod
          · have hw0 : w % s.k = 0 := by
              rw [le_antisymm hwk hwge, Nat.mod_self]
            rw [hjm, hw0] at hmod
            omega
        · have hjm : j % s.k = 0 := by
            rw [le_antisymm hjk hjge, Nat.mod_self]
          rcases Nat.lt_or_ge w s.k with hwlt | hwge
          · rw [hjm, Nat.mod_eq_of_lt hwlt] at hmod
            omega
          · omega
      rw [hjw]
    · -- `j % k = f c` is impossible: `f (f c) = (c+2) % k` would meet
      -- `{c, f c}`, forcing `k | 2` or `k | 1`, contradicting `2 < k`.
      have hjf : j % s.k = s.f c := Set.mem_singleton_iff.mp hjc'
      rw [hf c] at hjf
      have hfu : s.f (j % s.k) = (c + 2) % s.k := by
        rw [hf (j % s.k), hjf, Nat.mod_add_mod]
      have hm2 : (c + 2) % s.k ∈ ({c, s.f c} : Set ℕ) := by rw [← hje, hfu]; simp
      rcases Set.mem_insert_iff.mp hm2 with hA | hA'
      · have hd : (c + 2) % s.k = c % s.k := by rw [hA, Nat.mod_eq_of_lt hck]
        have hdvd : s.k ∣ (c + 2) - c :=
          (Nat.modEq_iff_dvd' (by omega)).mp hd.symm
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · have hd : (c + 2) % s.k = (c + 1) % s.k := by
          rw [Set.mem_singleton_iff.mp hA', hf c]
        have hdvd : s.k ∣ (c + 2) - (c + 1) :=
          (Nat.modEq_iff_dvd' (by omega)).mp hd.symm
        have := Nat.le_of_dvd (by omega) hdvd
        omega
  · rintro rfl
    refine ⟨w, ?_, ⟨hw1, hwk⟩, rfl⟩
    rw [hJ, Set.mem_singleton_iff, hwc]

/-- HOL `SING_J1_SY` (GBYCPXS.hl:202): an ear stable system has `J1_SY s`
a singleton `(i, SUC (i MOD k))` and `J_SY s = {{i MOD k, f_sy s i}}` with
`1 <= i <= k`. -/
theorem SING_J1_SY_p26 (s : StableSyP23) (h : earSy_p23 s)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k) :
    ∃ i, J1_SY_p23 s = {(i, i % s.k + 1)} ∧
      s.J = {({i % s.k, s.f (i % s.k)} : Set ℕ)} ∧ i ≤ s.k ∧ 1 ≤ i := by
  obtain ⟨c, hJc, hcI⟩ := PROPERTIES_EAR_SY_p26 s h
  have hck : c < s.k := by
    rw [hI] at hcI
    exact hcI
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0
    refine ⟨s.k, ?_, ?_, le_rfl, by omega⟩
    · exact j1SingAux_p26 s s.k 0 (Nat.mod_self s.k) (by omega) le_rfl hck hk hf hJc
    · have hmk : s.k % s.k = 0 := Nat.mod_self s.k
      rw [hmk]
      exact hJc
  · refine ⟨c, ?_, ?_, le_of_lt hck, hcpos⟩
    · exact j1SingAux_p26 s c c (Nat.mod_eq_of_lt hck) hcpos (le_of_lt hck) hck hk hf hJc
    · rw [Nat.mod_eq_of_lt hck]
      exact hJc

/-- HOL `CARD_F_SY_IN_B_SY` (GBYCPXS.hl:43).
DISCHARGED: the 1-based-row / 0-based-vertex bridge (`rowId_p26`, the local
stand-in for the `INJ_ROW_B_SY` kit) shows distinct rows; `CONDITION1_SY_p4`
with the stable system's off-diagonal bound `2 ≤ a i j` (`s.stable.2.1`,
indices shifted by one via `aSyRow_p26`) gives row injectivity, and the
proved LocalAuto4 `CARD_F_SY_EQ` counts the `k` cyclic darts. -/
theorem CARD_F_SY_IN_B_SY_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    (F_SY_p4 (vecmatsV3_p4 l)).ncard = s.k := by
  obtain ⟨v, ⟨hball, hC1, -⟩, hvl⟩ := Iff.mp (Set.mem_image _ _ _) hl
  have hrow : ∀ r : Fin s.k, vecmatsV3_p4 l r = v r := fun r => rowId_p26 hvl r
  have hmemI : ∀ u : ℕ, u < s.k → u ∈ s.I := fun u hu => by
    rw [hI]; exact hu
  have hk0 : 0 < s.k := by omega
  have h2off : ∀ x y : ℕ, x < s.k → y < s.k → x ≠ y → 2 ≤ s.a x y :=
    fun x y hx hy hne => s.stable.2.1 x (hmemI x hx) y (hmemI y hy) hne
  -- the wrap row `s.k` reduces to row `0` by symmetry + `f^[s.k]`-periodicity
  have hwrap : ∀ x : ℕ, 1 ≤ x → x < s.k → 2 ≤ s.a x s.k := by
    intro x hx1 hx
    have hper : ∀ u w : ℕ, s.a u w = s.a u (s.f^[s.k] w) :=
      fun u w => (s.stable.1.2.2.2.2.1 u w).1
    have hsym : ∀ u w : ℕ, s.a u w = s.a w u := fun u w => (s.stable.1.2.2.2.1 u w).1
    have hzero : s.f^[s.k] s.k = 0 := by
      rw [fIterateSuccMod_p26 hf hk0 s.k]
      simp
    have h2x0 : 2 ≤ s.a x (s.f^[s.k] s.k) := by
      rw [hzero]
      exact h2off x 0 hx (by omega) (by omega)
    rw [← hper x s.k] at h2x0
    exact h2x0
  have hinj : ∀ i j : Fin s.k, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j := by
    intro i j hij
    by_contra hne
    have hne2 : ((i : ℕ) + 1) ≠ ((j : ℕ) + 1) := fun he =>
      hne (Fin.ext (Nat.succ_injective he))
    have hvi : v i = v j := by rw [← hrow i, ← hrow j]; exact hij
    have hz : ‖v i - v j‖ = 0 := by rw [hvi]; simp
    have hC := (hC1 i j).1
    simp only [aSyRow_p26] at hC
    rw [hz] at hC
    have hzero : s.f^[s.k] s.k = 0 := by
      rw [fIterateSuccMod_p26 hf hk0 s.k]
      simp
    rcases Nat.lt_or_ge ((i : ℕ) + 1) s.k with hix | hix
    · rcases Nat.lt_or_ge ((j : ℕ) + 1) s.k with hjy | hjy
      · have ha2 := h2off ((i : ℕ) + 1) ((j : ℕ) + 1) hix hjy hne2
        linarith
      · have hjk : ((j : ℕ) + 1) = s.k := le_antisymm (by omega) hjy
        have ha2 : 2 ≤ s.a ((i : ℕ) + 1) ((j : ℕ) + 1) := by
          rw [hjk]
          exact hwrap ((i : ℕ) + 1) (by omega) hix
        linarith
    · have hik2 : ((i : ℕ) + 1) = s.k := le_antisymm (by omega) hix
      have hsym : ∀ u w : ℕ, s.a u w = s.a w u := fun u w => (s.stable.1.2.2.2.1 u w).1
      have hper : ∀ u w : ℕ, s.a u w = s.a u (s.f^[s.k] w) :=
        fun u w => (s.stable.1.2.2.2.2.1 u w).1
      rcases Nat.lt_or_ge ((j : ℕ) + 1) s.k with hjy | hjy
      · have h0I : (0 : ℕ) ∈ s.I := hmemI 0 (by omega)
        have h2j0 := s.stable.2.1 ((j : ℕ) + 1) (hmemI _ hjy) 0 h0I (by omega)
        have ha2' : 2 ≤ s.a ((i : ℕ) + 1) ((j : ℕ) + 1) := by
          rw [hik2, hsym _ _, hper _ _, hzero]
          exact h2j0
        linarith
      · have hik3 : (i : ℕ) = s.k - 1 := by omega
        have hjk2 : (j : ℕ) = s.k - 1 := by omega
        exact hne (Fin.ext (by rw [hik3, hjk2]))
  exact CARD_F_SY_EQ l hinj

/-- HOL `B_SY_LE_CSTAB` (GBYCPXS.hl:80): every cyclic adjacent row pair of
`vecmats l` is at most `cstab` apart.
DISCHARGED: the row bridge `rowId_p26` reads the statement off
`CONDITION1_SY_p4` (`bSyRow_p26` shift), with the `b i (f i) ≤ cstab` stable
bound transported by `fIterateSuccMod_p26` + symmetry; the two out-of-range
cyclic indices (`i = s.k` resp. `i = s.k - 1`) fall back to the ball-annulus
upper bound `‖v‖ ≤ 2*h0 < cstab`. -/
theorem B_SY_LE_CSTAB_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    ∀ i, 1 ≤ i → i ≤ s.k →
      ‖rowSy_p23 l i - rowSy_p23 l (i % s.k + 1)‖ ≤ cstab := by
  intro i hi1 hi2
  obtain ⟨v, ⟨hball, hC1, -⟩, hvl⟩ := Iff.mp (Set.mem_image _ _ _) hl
  have hrow : ∀ r : Fin s.k, vecmatsV3_p4 l r = v r := fun r => rowId_p26 hvl r
  have hballle : ∀ r : Fin s.k, ‖v r‖ ≤ 2 * h0 := fun r => ballUb_p26 (hball r)
  -- the stable-system bound `b j (f j) ≤ cstab` transported to `b u (u%k+1)`
  have hbnd : ∀ u : ℕ, 1 ≤ u → u ≤ s.k → s.b u (u % s.k + 1) ≤ cstab := by
    intro u hu1 hu2
    have hk0 : 0 < s.k := by omega
    have hmemI : ∀ w : ℕ, w < s.k → w ∈ s.I := fun w hw => by rw [hI]; exact hw
    have hper : ∀ u w : ℕ, s.b u w = s.b u (s.f^[s.k] w) :=
      fun u w => (s.stable.1.2.2.2.2.1 u w).2
    have hsym : ∀ u w : ℕ, s.b u w = s.b w u :=
      fun u w => (s.stable.1.2.2.2.1 u w).2.1
    have hfit : (u % s.k) ∈ s.I := hmemI _ (Nat.mod_lt _ hk0)
    have hle := (s.stable.2.2.1 (u % s.k) hfit).2
    rw [hf] at hle
    have hf1 : s.f^[s.k] u = u % s.k := fIterateSuccMod_p26 hf hk0 u
    have hf2 : s.f^[s.k] (u % s.k + 1) = (u % s.k + 1) % s.k := fIterateSuccMod_p26 hf hk0 _
    calc s.b u (u % s.k + 1)
        _ = s.b (u % s.k + 1) u := hsym u _
        _ = s.b (u % s.k + 1) (s.f^[s.k] u) := hper _ _
        _ = s.b (u % s.k + 1) (u % s.k) := by rw [hf1]
        _ = s.b (u % s.k) (u % s.k + 1) := hsym _ _
        _ = s.b (u % s.k) (s.f^[s.k] (u % s.k + 1)) := hper _ _
        _ = s.b (u % s.k) ((u % s.k + 1) % s.k) := by rw [hf2]
        _ ≤ cstab := hle
  by_cases hik : i = s.k
  · -- rows `s.k` (junk `0`) and `1`: `‖0 - v 1‖ = ‖v 1‖ ≤ 2*h0 < cstab`
    have h1lt : s.k % s.k + 1 < s.k := by rw [Nat.mod_self]; omega
    have hr1 : rowSy_p23 l (s.k % s.k + 1) = v ⟨s.k % s.k + 1, h1lt⟩ := by
      show (if h : s.k % s.k + 1 < s.k then vecmatsV3_p4 l ⟨s.k % s.k + 1, h⟩ else 0) = _
      rw [dif_pos h1lt, hrow]
    have hr0 : rowSy_p23 l s.k = 0 := by
      show (if h : s.k < s.k then vecmatsV3_p4 l ⟨s.k, h⟩ else 0) = 0
      rw [dif_neg (by omega)]
    rw [hik, hr0, hr1]
    calc ‖(0 : V3) - v ⟨s.k % s.k + 1, h1lt⟩‖
        = ‖v ⟨s.k % s.k + 1, h1lt⟩‖ := by simp
      _ ≤ 2 * h0 := hballle ⟨s.k % s.k + 1, h1lt⟩
      _ ≤ cstab := by norm_num [h0, cstab]
  · -- adjacent in-range rows: `CONDITION1_SY_p4` + the `b i (f i) ≤ cstab` bound
    have hilt : i < s.k := by omega
    have hr1 : rowSy_p23 l i = v ⟨i, hilt⟩ := by
      show (if h : i < s.k then vecmatsV3_p4 l ⟨i, h⟩ else 0) = _
      rw [dif_pos hilt, hrow]
    by_cases hip1 : i + 1 = s.k
    · have hr2 : rowSy_p23 l (i % s.k + 1) = 0 := by
        show (if h : i % s.k + 1 < s.k then vecmatsV3_p4 l ⟨i % s.k + 1, h⟩ else 0) = 0
        rw [dif_neg (show ¬(i % s.k + 1 < s.k) from by
          have := Nat.mod_eq_of_lt hilt
          have := hip1
          omega)]
      rw [hr1, hr2]
      have hle := hballle ⟨i, hilt⟩
      calc ‖v ⟨i, hilt⟩ - (0 : V3)‖ = ‖v ⟨i, hilt⟩‖ := by simp
        _ ≤ 2 * h0 := hle
        _ ≤ cstab := by norm_num [h0, cstab]
    · have hip1lt : i % s.k + 1 < s.k := by
        have h1 := Nat.mod_eq_of_lt hilt
        have h2 := hip1
        omega
      have hr2 : rowSy_p23 l (i % s.k + 1) = v ⟨i % s.k + 1, hip1lt⟩ := by
        show (if h : i % s.k + 1 < s.k then vecmatsV3_p4 l ⟨i % s.k + 1, h⟩ else 0) = _
        rw [dif_pos hip1lt, hrow]
      have hC := (hC1 ⟨i, hilt⟩ ⟨i % s.k + 1, hip1lt⟩).2
      simp only [bSyRow_p26] at hC
      rw [hr1, hr2]
      have hmeq : (i % s.k + 1) % s.k = (i + 1) % s.k :=
        Nat.ModEq.add_right 1 (Nat.mod_modEq i s.k)
      have h5 := hbnd (i + 1) (by omega) (by omega)
      have h5' : s.b (i + 1) ((i % s.k + 1) % s.k + 1) ≤ cstab := by rwa [← hmeq] at h5
      have h5'' : s.b (i + 1) (i % s.k + 1 + 1) ≤ cstab := by
        rwa [Nat.mod_eq_of_lt hip1lt] at h5'
      calc ‖v ⟨i, hilt⟩ - v ⟨i % s.k + 1, hip1lt⟩‖
          _ ≤ s.b ((⟨i, hilt⟩ : Fin s.k).val + 1)
              ((⟨i % s.k + 1, hip1lt⟩ : Fin s.k).val + 1) := hC
          _ ≤ cstab := h5''

set_option maxHeartbeats 20000000 in
/-- HOL `D_FUN_LE` (GBYCPXS.hl:365).
DISCHARGED: the summand `cstab - ‖row (x.1-1) - row (x.2-1)‖` is bounded by
`CONDITION1_SY_p4` + `hbnd` (the `B_SY_LE_CSTAB` transport of the stable
`b j (f j) ≤ cstab` bound).  Ear case: `SING_J1_SY_p26` collapses `J1_SY` to
a singleton and `d = 0.11`, so `d_fun ≤ 0.11 + 0.1*cstab ≤ 0.92`; otherwise
the `-1` coefficient makes `d_fun ≤ d ≤ 0.9`. -/
theorem D_FUN_LE_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hd : s.d ≤ 0.9)
    (hsol : Real.pi ≤ solLocal (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    dFun_p23 s l ≤ 0.92 := by
  obtain ⟨v, ⟨hball, hC1, -⟩, hvl⟩ := Iff.mp (Set.mem_image _ _ _) hl
  have hrow : ∀ r : Fin s.k, vecmatsV3_p4 l r = v r := fun r => rowId_p26 hvl r
  have hbnd : ∀ u : ℕ, 1 ≤ u → u ≤ s.k → s.b u (u % s.k + 1) ≤ cstab := by
    intro u hu1 hu2
    have hk0 : 0 < s.k := by omega
    have hmemI : ∀ w : ℕ, w < s.k → w ∈ s.I := fun w hw => by rw [hI]; exact hw
    have hper : ∀ u w : ℕ, s.b u w = s.b u (s.f^[s.k] w) :=
      fun u w => (s.stable.1.2.2.2.2.1 u w).2
    have hsym : ∀ u w : ℕ, s.b u w = s.b w u :=
      fun u w => (s.stable.1.2.2.2.1 u w).2.1
    have hfit : (u % s.k) ∈ s.I := hmemI _ (Nat.mod_lt _ hk0)
    have hle := (s.stable.2.2.1 (u % s.k) hfit).2
    rw [hf] at hle
    have hf1 : s.f^[s.k] u = u % s.k := fIterateSuccMod_p26 hf hk0 u
    have hf2 : s.f^[s.k] (u % s.k + 1) = (u % s.k + 1) % s.k := fIterateSuccMod_p26 hf hk0 _
    calc s.b u (u % s.k + 1)
        _ = s.b (u % s.k + 1) u := hsym u _
        _ = s.b (u % s.k + 1) (s.f^[s.k] u) := hper _ _
        _ = s.b (u % s.k + 1) (u % s.k) := by rw [hf1]
        _ = s.b (u % s.k) (u % s.k + 1) := hsym _ _
        _ = s.b (u % s.k) (s.f^[s.k] (u % s.k + 1)) := hper _ _
        _ = s.b (u % s.k) ((u % s.k + 1) % s.k) := by rw [hf2]
        _ ≤ cstab := hle
  -- every `J1_SY` element is a cyclic adjacent row pair bounded by `cstab`
  have hJ1fin : (J1_SY_p23 s : Set (ℕ × ℕ)).Finite :=
    Set.Finite.subset
      (Set.Finite.image (fun i : ℕ => (i, i % s.k + 1)) (Set.finite_Icc 1 s.k))
      (by
        intro x hx
        simp only [J1_SY_p23, Set.mem_setOf_eq] at hx
        obtain ⟨w, -, hwI, rfl⟩ := hx
        exact Set.mem_image_of_mem _ hwI)
  have hterm : ∀ x ∈ J1_SY_p23 s,
      0 ≤ cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖ := by
    intro x hx
    simp only [J1_SY_p23, Set.mem_setOf_eq] at hx
    obtain ⟨w, -, hwI, rfl⟩ := hx
    obtain ⟨hw1, hw2⟩ := hwI
    have hw : w ≤ s.k := hw2
    have hwpos : 0 < s.k := by omega
    have h1 : rowSy_p23 l (w - 1) = v ⟨w - 1, by omega⟩ := by
      show (if h : w - 1 < s.k then vecmatsV3_p4 l ⟨w - 1, h⟩ else 0) = _
      rw [dif_pos (by omega), hrow]
    have h2 : rowSy_p23 l (w % s.k + 1 - 1) = v ⟨w % s.k, Nat.mod_lt _ hwpos⟩ := by
      show (if h : w % s.k + 1 - 1 < s.k then vecmatsV3_p4 l ⟨w % s.k + 1 - 1, h⟩ else 0) = _
      rw [Nat.succ_sub_one, dif_pos (Nat.mod_lt _ hwpos), hrow]
    have hC := (hC1 ⟨w - 1, by omega⟩ ⟨w % s.k, Nat.mod_lt _ hwpos⟩).2
    simp only [bSyRow_p26] at hC
    have hw1 : (w - 1) + 1 = w := by omega
    rw [hw1] at hC
    rw [h1, h2]
    exact sub_nonneg.mpr (le_trans hC (hbnd w (by omega) hw))
  show s.d + (1 : ℝ) / 10 * (if earSy_p23 s then 1 else -1) *
      setSum (J1_SY_p23 s)
        (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖) ≤ 0.92
  by_cases hear : earSy_p23 s
  · -- ear: singleton sum, d = 0.11
    have hsing := SING_J1_SY_p26 s hear hI hf hk
    obtain ⟨-, hdd, -, -, -⟩ := id hear
    obtain ⟨w, hJ1, -, -⟩ := hsing
    have hcst : (cstab : ℝ) = 3.01 := by norm_num [cstab]
    have hnorm : 0 ≤ ‖rowSy_p23 l ((w, w % s.k + 1).1 - 1)
        - rowSy_p23 l ((w, w % s.k + 1).2 - 1)‖ := norm_nonneg _
    have hseq : setSum (J1_SY_p23 s)
        (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖)
        = cstab - ‖rowSy_p23 l ((w, w % s.k + 1).1 - 1)
            - rowSy_p23 l ((w, w % s.k + 1).2 - 1)‖ := by
      rw [hJ1]
      exact setSum_singleton_p26 (f := fun x => cstab - ‖rowSy_p23 l (x.1 - 1) -
        rowSy_p23 l (x.2 - 1)‖) (a := (w, w % s.k + 1))
    rw [if_pos hear, hseq]
    linarith
  · -- non-ear: the coefficient is -1 and the sum is nonnegative
    rw [if_neg hear]
    have hsum : 0 ≤ setSum (J1_SY_p23 s)
        (fun x => cstab - ‖rowSy_p23 l (x.1 - 1) - rowSy_p23 l (x.2 - 1)‖) :=
      setSum_nonneg_of_nonneg_p26 hJ1fin hterm
    linarith

/-- HOL `TAU_FUN_LE` (GBYCPXS.hl:467). Proof pending (needs
`CARD_F_SY_IN_B_SY` / `LOFA_DETERMINE_AZIM_IN_FA` / the Flyspeck-constants
bound `sol0 < #0.551286`). -/
theorem TAU_FUN_LE_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hsol : Real.pi ≤ solLocal (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    0.92 < tauFun (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)) := by
  sorry

/-- HOL `TAU_STAR_POS` (GBYCPXS.hl:578): `tau_star = tau_fun - d_fun` is
positive, by `TAU_FUN_LE` (`#0.92 <`) and `D_FUN_LE` (`d_fun <= #0.92`). -/
theorem TAU_STAR_POS_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hd : s.d ≤ 0.9)
    (hsol : Real.pi ≤ solLocal (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    0 < tauStar_p23 s l := by
  have htf := TAU_FUN_LE_p26 s l hI hf hk hsol hl
  have hdf := D_FUN_LE_p26 s l hI hf hk hd hsol hl
  unfold tauStar_p23
  linarith

/-- HOL `CIRCULAR_SOL_EQ_2PI` (GBYCPXS.hl:592): on a circular fan every
dart azimuth equals `pi`, so the solid angle is `2 * pi` (KCHMAMG engine,
discharged by `circularSolEq2Pi_cs`, CircularSolKit). -/
theorem CIRCULAR_SOL_EQ_2PI_p26 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hclf : ConvexLocalFan V E FF) (hc : Circular V E) : solLocal E FF = 2 * Real.pi := by
  exact circularSolEq2Pi_cs hclf hc

/-- HOL `NOT_CIRCULAR_SY` (GBYCPXS.hl:621): `tau_star s l <= 0` forces the
fan of `l` to be non-circular, since circularity would give
`sol_local = 2*pi >= pi`, hence `tau_star > 0` by `TAU_STAR_POS`. -/
theorem NOT_CIRCULAR_SY_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hd : s.d ≤ 0.9) (htau : tauStar_p23 s l ≤ 0)
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    ¬ Circular (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) := by
  intro hc
  have hclf : ConvexLocalFan (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))
      (F_SY_p4 (vecmatsV3_p4 l)) := by
    sorry -- NEEDS: `convexLocalFan_p4`/`CONDITION2_SY_p4` (from B_SY1) ->
    -- `ConvexLocalFan` bridge
  have h2pi := CIRCULAR_SOL_EQ_2PI_p26 _ _ _ hclf hc
  have hpi : Real.pi ≤ solLocal (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) := by
    rw [h2pi]
    linarith [Real.pi_pos]
  exact absurd (TAU_STAR_POS_p26 s l hI hf hk hd hpi hl) (not_lt.mpr htau)

/-- HOL `GBYCPXS` (GBYCPXS.hl:668): the main stable-system disjunct — under
`l IN B_SY1 (a_sy s) (b_sy s)`, either `tau_star` is positive, or the fan is
not circular. -/
theorem GBYCPXS_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    (s.d ≤ 0.9 →
        Real.pi ≤ solLocal (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)) →
        0 < tauStar_p23 s l) ∧
      (s.d ≤ 0.9 → tauStar_p23 s l ≤ 0 →
        ¬ Circular (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) := by
  refine ⟨fun hd hsol => TAU_STAR_POS_p26 s l hI hf hk hd hsol hl, fun hd htau => ?_⟩
  exact NOT_CIRCULAR_SY_p26 s l hI hf hk hd htau hl

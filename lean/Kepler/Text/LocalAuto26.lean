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
    `RRCWNSJ_p26`.
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
  - Import discipline: this file sits entirely on the LocalAuto1 side of
    the fatal `atn2PA18` duplication (LocalAuto2/9/11 and PackingAuto20 are
    NOT imported; LocalAuto19-27 same-wave lanes are NOT imported). The
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

import Kepler.Text.LocalAuto23
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

/-- HOL `BB_VV_FUN_EQ` (RRCWNSJ.hl:92). Proof pending (needs
`W_IN_BB_FUN_EQ` / `CHANGE_W_IN_BBS_MOD_IS_SCS`). -/
theorem BB_VV_FUN_EQ_p26 (s : ScsV39) (vv : ℕ → V3) (hs : isScsV39 s)
    (hv : BBsV39 s vv) : ∀ i j, vv i = vv j ↔ i % s.k = j % s.k := by
  sorry

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

/-- HOL `BB_RHO_NODE_IVS` (RRCWNSJ.hl:195). Proof pending (needs
`VV_SUC_EQ_RHO_NODE_PRIME` / `BBS_IMP_CONVEX_LOCAL_FAN` / `CVLF_LF_F`). -/
theorem BB_RHO_NODE_IVS_p26 (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (u : V3)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (p1 : ℕ)
    (hk' : s.k = k) (hu : vv p1 = u) (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hs : isScsV39 s) (h3k : 3 < k) (hv : BBsV39 s vv) :
    rhoNode1 FF u = vv (p1 + 1) ∧ ivsRhoNode1 FF u = vv (p1 + k - 1) := by
  sorry

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

/-- HOL `arclength222h0` (AXJRPNC.hl:152). Proof pending (needs
`ATN_UPS_X_BREAKDOWN1` / atn.inner normnum). -/
theorem arclength222h0_p26 : arcLength 2 2 (2 * h0) < Real.pi / 2 := by
  sorry

/-- HOL `arclength_2h0_cstab` (AXJRPNC.hl:272). Proof pending (needs
`ATN_UPS_X_BREAKDOWN1` / atn.inner normnum). -/
theorem arclength_2h0_cstab_p26 :
    arcLength 2 2 (2 * h0) + arcLength 2 2 cstab < Real.pi := by
  sorry

/-- HOL `DIST_LE2_BB_CASSE_4` (AXJRPNC.hl:180). Proof pending (needs
finitary cardinal arithmetic over bad index sets). -/
theorem DIST_LE2_BB_CASSE_4_p26 (s : ScsV39) (v : ℕ → V3) (hk : s.k = 4)
    (hv : BBsV39 s v) (hs : isScsV39 s) : ∃ i, ‖v i - v (i + 1)‖ ≤ 2 * h0 := by
  sorry

/-- HOL `DIST_LE2_BB_CASSE_5` (AXJRPNC.hl:298). Proof pending (needs
card-2 bad-index subset argument / `SUC_MOD_NOT_EQ`). -/
theorem DIST_LE2_BB_CASSE_5_p26 (s : ScsV39) (v : ℕ → V3) (hk : s.k = 5)
    (hv : BBsV39 s v) (hs : isScsV39 s) (i : ℕ) :
    ‖v i - v (i + 1)‖ ≤ 2 * h0 ∨ ‖v (i + 1) - v (i + 2)‖ ≤ 2 * h0 := by
  sorry

/-- HOL `AXJRPNC` (AXJRPNC.hl:380). Proof pending (needs
`RRCWNSJ` / local fan machinery / lunar EDGE/IVS case elimination). -/
theorem AXJRPNC_p26 (s : ScsV39) (v : ℕ → V3) (i j : ℕ)
    (hs : isScsV39 s) (hbasic : scsBasicV39 s)
    (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : MMsV39 s v)
    (hlunar : Lunar (v i) (v j) (Set.range v)
      (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))) :
    s.k = 6 ∧ v j = v (i + 3) := by
  sorry
/-! ## Section C: PPBTYDQ -/

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

/-- HOL `MXQTIED_PRIME` (PPBTYDQ.hl:252). Proof pending (needs
`MXQTIED_BB` / `BB_simplify` machinery for the minimising condition). -/
theorem MXQTIED_PRIME_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : v ∈ BBprimeV39 s) (hv' : BBsV39 s' v)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : v ∈ BBprimeV39 s' := by
  sorry

/-- HOL `MXQTIED_PRIME2` (PPBTYDQ.hl:241). Proof pending (needs
`MXQTIED_PRIME` / `MXQTIED_INDEX`). -/
theorem MXQTIED_PRIME2_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : v ∈ BBprime2V39 s' := by
  sorry

/-- HOL `MXQTIED` (PPBTYDQ.hl:231). Proof pending (needs
`MXQTIED_PRIME2` / `BB_simplify` / `dsv_J_empty`). -/
theorem MXQTIED_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
    (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
    (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
    (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) : v ∈ MMsV39 s' := by
  sorry

/-- HOL `OIQKKEP` (PPBTYDQ.hl:172). Delegates to the existing
`sorry`-based `OIQKKEP_concl` in LocalAuto1. -/
theorem OIQKKEP_p26 (u v : V3) (c : ℝ) (hu : u ∈ ballAnnulus) (hv : v ∈ ballAnnulus)
    (hc : c < 4) (hdist : dist u v ≤ c) (h2 : 2 ≤ dist u v) :
    arcV 0 u v ≤ arcLength 2 2 c := by
  exact OIQKKEP_concl u v c hu hv hc h2 hdist

/-- HOL `PPBTYDQ` (PPBTYDQ.hl:92). Proof pending (needs
convex-hull / arcV angle comparison kit). -/
theorem PPBTYDQ_p26 (u v p : V3) (hu : ¬Collinear ℝ ({0, v, p} : Set V3))
    (hv : ¬Collinear ℝ ({0, u, p} : Set V3))
    (harc : arcV 0 u p + arcV 0 p v < Real.pi) :
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3)) := by
  sorry

/-- HOL `XWNHLMD_MM` (PPBTYDQ.hl:560). Proof pending (needs
`XWITCCN` / `MMS_NONEMPTY` from taustar<0). -/
theorem XWNHLMD_MM_p26 (s s' : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v) (hds : s.d ≤ s'.d) :
    MMsV39 s' ≠ ∅ := by
  sorry

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

/-- HOL `CARD_F_SY_IN_B_SY` (GBYCPXS.hl:43). Proof pending (needs the
`INJ_ROW_B_SY` / `CARD_F_SY_EQ` row-injectivity kit over the 1-based
`vecmats` rows). -/
theorem CARD_F_SY_IN_B_SY_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    (F_SY_p4 (vecmatsV3_p4 l)).ncard = s.k := by
  sorry

/-- HOL `B_SY_LE_CSTAB` (GBYCPXS.hl:80): every cyclic adjacent row pair of
`vecmats l` is at most `cstab` apart. Proof pending (needs the 1-based row /
0-based vertex bridge used by `INJ_ROW_B_SY` to read `b_sy s i (f i) <= cstab`
off `B_SY1`/`CONDITION1_SY`). -/
theorem B_SY_LE_CSTAB_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    ∀ i, 1 ≤ i → i ≤ s.k →
      ‖rowSy_p23 l i - rowSy_p23 l (i % s.k + 1)‖ ≤ cstab := by
  sorry

/-- HOL `D_FUN_LE` (GBYCPXS.hl:365). Proof pending (needs `B_SY_LE_CSTAB`
plus the `SING_J1_SY` singleton sum reduction). -/
theorem D_FUN_LE_p26 (s : StableSyP23) (l : FinVec s.k 3)
    (hI : s.I = {i | i < s.k}) (hf : ∀ i, s.f i = (i + 1) % s.k) (hk : 2 < s.k)
    (hd : s.d ≤ 0.9)
    (hsol : Real.pi ≤ solLocal (E_SY_p4 (vecmatsV3_p4 l)) (F_SY_p4 (vecmatsV3_p4 l)))
    (hl : l ∈ B_SY1_p4 (aSyRow_p26 s) (bSyRow_p26 s)) :
    dFun_p23 s l ≤ 0.92 := by
  sorry

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

/-- HOL `CIRCULAR_SOL_EQ_2PI` (GBYCPXS.hl:592). Proof pending (needs
`LOCAL_FAN_RHO_NODE_PROS` / `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM` / `KCHMAMG`:
on a circular fan every dart azimuth equals `pi`). -/
theorem CIRCULAR_SOL_EQ_2PI_p26 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hclf : ConvexLocalFan V E FF) (hc : Circular V E) : solLocal E FF = 2 * Real.pi := by
  sorry

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

/-
LocalAuto28 — port of `scripts/local/NUXCOEA.hl` (7741 ln; 1 def + 100
theorems — the BBs/MMs annulus *deformation* bank of the appendix-to-Local-Fan
chapter).  The file is organised as the source: a shared deformation substrate
(`v3_defor_v4`/`v3_defor_v5`), the mod/annulus toolkit, the `MK` deformation
family around the index `l` (using `w (l+k-1)` as the fixed neighbour), the
`TWO_CASES` twins of the same family (using `w (SUC l)`), the local-fan
deformation tower, and the terminal `NUXCOEA` / `*v2` registry twins.

Encoding:
- HOL `real^3` <-> `V3`; `norm v pow 2` <-> `norm v ^ 2`; `dist(x,y)` <->
  `dist x y`; `SUC n` <-> `n + 1`; `w (l + k - 1)` kept verbatim.
- `collinear {vec 0, a, b}` <-> `Collinear ℝ ({0, a, b} : Set V3)`;
  `aff_gt {vec 0} {u, v}` <-> `affGt {0} {u, v}` (Kepler.Geom);
  `azim (vec 0) u v w` <-> `azim 0 u v w` (4-point `azim`, Kepler.Geom).
- scs accessors: `scs_k_v39 s` <-> `s.k`, `scs_a_v39` <-> `s.a`,
  `scs_b_v39` <-> `s.b`, `scs_J_v39 s l i` <-> `s.J l i`, `scs_diag k l i` <->
  `scsDiag k l i`; `is_scs_v39`/`MMs_v39`/`BBs_v39`/`BBprime_v39`/`taustar_v39`/
  `dsv_v39` <-> `isScsV39`/`MMsV39`/`BBsV39`/`BBprimeV39`/`taustarV39`/`dsvV39`
  (LocalAuto1); `ball_annulus`/`h0` <-> `ballAnnulus`/`h0` (PackingAuto2).
- `v3_defor_v1 a v1 v2 x1 x2 x5 x6 x3` <-> `v3DeforV1_p17` (LocalAuto17,
  EYYPQDW lane; `ups_x` <-> `upsX`).  `rho_node1` <-> `rhoNode1`,
  `interior_angle1` <-> `interiorAngle1`, `deformation` <-> `Deformation`,
  `lunar` <-> `Lunar`, `generic` <-> `Generic`, `convex_local_fan` <->
  `ConvexLocalFan` (LocalAuto1).
- `IMAGE w (:num)` <-> `Set.range w`; `IMAGE (\i. w i, w (SUC i)) (:num)` <->
  `Set.range fun i => (w i, w (i + 1))`; `ITER i f x` <-> `f^[i] x`;
  `@a. a, x IN FF` <-> `Classical.epsilon`, abbreviated `epPair_p28`;
  `--e < t /\ t < e` <-> `-ε < t ∧ t < ε`.
- `v3_defor_v4` (IMJXPHR.hl:87) is copied as `v3DeforV4_p28` — NEEDS: the
  IMJXPHR lane (same wave, LocalAuto29+) should delete this copy and import.
- The composed registry twins `NUXCOEA`/`NUXCOEAv2`/`IMJXPHRv2`/`ODXLSTCv2`
  are `mk_imp(ZLZTHIC_concl, mk_imp (MHAEYJN_concl, _concl))`; the two
  antecedents are carried as the hypothesis arguments `ZLZTHIC_concl` /
  `MHAEYJN_concl` (LocalAuto1 statements).  DISCHARGES: proving the local
  giants below discharges those registry `sorry`s.  `IMJXPHR_concl`
  (IMJXPHR.hl:9682) and `ODXLSTCv2_concl` (ODXLSTC.hl:1695) are restated
  verbatim (their owners are same-wave LocalAuto29-33; not imported).
- `check_completeness_claimA_concl` is commented out in the source
  (NUXCOEA.hl:7735) and is not ported.
- No `native_decide`; the proved items are mechanical (mod arithmetic,
  annulus membership, definitional unfolding of `v3_defor_v5`, continuity
  lift).  The deformation/fan giants are `sorry` (skeleton-first).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto17
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Definitions -/

/-- HOL `v3_defor_v4 a x1 x2 x6 v1 w v t` (IMJXPHR.hl:87); the base
deformation fixing every point except `w`.  NEEDS: IMJXPHR lane copy. -/
noncomputable def v3DeforV4_p28 (a x1 x2 x6 : ℝ) (v1 w v : V3) (t : ℝ) : V3 :=
  if v = w then v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - t) else v

/-- HOL `v3_defor_v5 a x1 x5 x2 v1 v2 v t` (NUXCOEA.hl:152): the affine
re-centring of `v3_defor_v4` around `v1`. -/
noncomputable def v3DeforV5_p28 (a x1 x5 x2 : ℝ) (v1 v2 v : V3) (t : ℝ) : V3 :=
  v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (v - v1) t + v1

/-- HOL `@a. a, x IN FF` (epsilon witness of an edge at `x`). -/
noncomputable def epPair_p28 (FF : Set (V3 × V3)) (x : V3) : V3 :=
  Classical.epsilon fun a => (a, x) ∈ FF

/-! ## Section 0: mod arithmetic, annulus membership, scs mod-invariance -/

/-- HOL `EQ_SUC_K_SUB` (NUXCOEA.hl:156). -/
theorem EQ_SUC_K_SUB_p28 {k l i : ℕ} (h : l % k = (i + 1) % k) (hk : 1 < k) :
    (l + k - 1) % k = i % k := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h0k : 0 < k := by omega
    have hm : i % k < k := Nat.mod_lt _ h0k
    have h2 : i % k + 1 = k := by
      have h1 : (i + 1) % k = 0 := by simpa using h.symm
      rw [Nat.add_mod, Nat.mod_eq_of_lt hk] at h1
      rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h1; omega
      · have hsub : i % k + 1 - k < k := by omega
        have e : i % k + 1 = i % k + 1 - k + k := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hsub] at h1
        omega
    rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
    omega
  · have h' : ((l - 1) + 1) % k = (i + 1) % k := by rwa [Nat.sub_add_cancel hl]
    have h'' : (l - 1) % k = i % k :=
      Nat.ModEq.add_right_cancel' 1 h'
    have e1 : l + k - 1 = (l - 1) + k := by omega
    rw [e1, Nat.add_mod_right]
    exact h''

/-- HOL `EQ_SUC_K_SUB3` (NUXCOEA.hl:164); same statement, `3 < k`. -/
theorem EQ_SUC_K_SUB3_p28 {k l i : ℕ} (h : l % k = (i + 1) % k) (hk : 3 < k) :
    (l + k - 1) % k = i % k :=
  EQ_SUC_K_SUB_p28 h (by omega)

/-- One-index mod-folding under periodicity (shared by the `CHANGE_*` kit). -/
theorem modPeriodic_p28 {α : Sort u} {f : ℕ → α} {k : ℕ} (hk : 0 < k)
    (hper : ∀ i, f (i + k) = f i) {j j1 : ℕ} (hj : j % k = j1 % k) : f j = f j1 := by
  have key : ∀ q j : ℕ, f (j + q * k) = f j := by
    intro q
    induction q with
    | zero => intro j; simp
    | succ q ih =>
        intro j
        have e : j + Nat.succ q * k = (j + q * k) + k := by
          rw [Nat.succ_mul]; omega
        rw [e, hper, ih]
  rcases Nat.le_total j j1 with hle | hle
  · have h0k : 0 < k := hk
    have hm : j % k < k := Nat.mod_lt _ h0k
    have hr : (j1 - j) % k < k := Nat.mod_lt _ h0k
    have hjj : j + (j1 - j) = j1 := by omega
    have hsum : (j % k + (j1 - j) % k) % k = j % k := by
      rw [← Nat.add_mod, hjj, hj]
    rcases Nat.lt_or_ge (j % k + (j1 - j) % k) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hsum
      have hd0 : (j1 - j) % k = 0 := by omega
      have hkey := Nat.div_add_mod (j1 - j) k
      rw [hd0, Nat.mul_comm, Nat.add_zero] at hkey
      obtain ⟨q, hq⟩ : ∃ q, j1 - j = q * k := ⟨(j1 - j) / k, hkey.symm⟩
      have hje : j1 = j + q * k := by omega
      rw [hje, key]
    · have hsub : j % k + (j1 - j) % k - k < k := by omega
      have e : j % k + (j1 - j) % k = j % k + (j1 - j) % k - k + k := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hsub] at hsum
      omega
  · have h0k : 0 < k := hk
    have hm : j1 % k < k := Nat.mod_lt _ h0k
    have hr : (j - j1) % k < k := Nat.mod_lt _ h0k
    have hjj : j1 + (j - j1) = j := by omega
    have hsum : (j1 % k + (j - j1) % k) % k = j1 % k := by
      rw [← Nat.add_mod, hjj, ← hj]
    rcases Nat.lt_or_ge (j1 % k + (j - j1) % k) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hsum
      have hd0 : (j - j1) % k = 0 := by omega
      have hkey := Nat.div_add_mod (j - j1) k
      rw [hd0, Nat.mul_comm, Nat.add_zero] at hkey
      obtain ⟨q, hq⟩ : ∃ q, j - j1 = q * k := ⟨(j - j1) / k, hkey.symm⟩
      have hje : j = j1 + q * k := by omega
      rw [hje, key]
    · have hsub : j1 % k + (j - j1) % k - k < k := by omega
      have e : j1 % k + (j - j1) % k = j1 % k + (j - j1) % k - k + k := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hsub] at hsum
      omega

/-- HOL `WL_IN_V` (NUXCOEA.hl:177). -/
theorem WL_IN_V_p28 (w : ℕ → V3) (l : ℕ) : w l ∈ Set.range w := ⟨l, rfl⟩

/-- HOL `WL_IN_FF` (NUXCOEA.hl:185). -/
theorem WL_IN_FF_p28 (w : ℕ → V3) (l : ℕ) :
    (w l, w (l + 1)) ∈ Set.range (fun i : ℕ => (w i, w (i + 1))) := ⟨l, rfl⟩

/-- HOL `WL_IN_BALL_ANNULUS` (NUXCOEA.hl:192). -/
theorem WL_IN_BALL_ANNULUS_p28 (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : BBsV39 s w) :
    w l ∈ ballAnnulus := h.1 ⟨l, rfl⟩

/-- HOL `NORM_LE_2_IN_BBS` (NUXCOEA.hl:205). -/
theorem NORM_LE_2_IN_BBS_p28 (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : BBsV39 s w) :
    2 ≤ ‖w l‖ := by
  have h1 : w l ∈ ballAnnulus := h.1 ⟨l, rfl⟩
  have h2 : ballAnnulus = Metric.closedBall (0:V3) (2 * h0) \ Metric.ball (0:V3) 2 := rfl
  rw [h2, Set.mem_sdiff, Metric.mem_ball, dist_eq_norm, sub_zero] at h1
  linarith

/-- HOL `MMS_IMP_BBS` (NUXCOEA.hl:213). -/
theorem MMS_IMP_BBS_p28 (s : ScsV39) (w : ℕ → V3) (h : w ∈ MMsV39 s) : BBsV39 s w := by
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
  exact h.1.1.1

/-- HOL `MMS_IMP_BBPRIME` (NUXCOEA.hl:217). -/
theorem MMS_IMP_BBPRIME_p28 (s : ScsV39) (w : ℕ → V3) (h : w ∈ MMsV39 s) :
    w ∈ BBprimeV39 s := by
  simp only [MMsV39, BBprime2V39, Set.mem_setOf_eq] at h
  exact h.1.1

/-- HOL `NORM_LE_2_IN_MMS` (NUXCOEA.hl:221). -/
theorem NORM_LE_2_IN_MMS_p28 (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : w ∈ MMsV39 s) :
    2 ≤ ‖w l‖ :=
  NORM_LE_2_IN_BBS_p28 s w l (MMS_IMP_BBS_p28 s w h)

/-- Mod-folding of the first scs index under `periodic2`. -/
theorem modPeriodic2_first_p28 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : 0 < k)
    (hper : Periodic2 f k) {j j1 l : ℕ} (hj : j % k = j1 % k) : f j l = f j1 l :=
  modPeriodic_p28 (f := fun i => f i l) hk (fun i => (hper i l).1) hj

/-- Mod-folding of the second scs index under `periodic2`. -/
theorem modPeriodic2_second_p28 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : 0 < k)
    (hper : Periodic2 f k) {j j1 l : ℕ} (hj : j % k = j1 % k) : f l j = f l j1 :=
  modPeriodic_p28 (f := fun i => f l i) hk (fun i => (hper l i).2) hj

/-- HOL `CHANGE_A_SCS_MODL` (NUXCOEA.hl:227). -/
theorem CHANGE_A_SCS_MODL_p28 (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
    (hj : j % s.k = j1 % s.k) : s.a j l = s.a j1 l :=
  modPeriodic2_first_p28 (by have := hs.2.1; omega) hs.2.2.2.2.2.2.2.1 hj

/-- HOL `CHANGE_A_SCS_MODR` (NUXCOEA.hl:239). -/
theorem CHANGE_A_SCS_MODR_p28 (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
    (hj : j % s.k = j1 % s.k) : s.a l j = s.a l j1 :=
  modPeriodic2_second_p28 (by have := hs.2.1; omega) hs.2.2.2.2.2.2.2.1 hj

/-- HOL `CHANGE_A_SCS_MOD` (NUXCOEA.hl:251). -/
theorem CHANGE_A_SCS_MOD_p28 (s : ScsV39) (hs : isScsV39 s) (j j1 l l1 : ℕ)
    (hj : j % s.k = j1 % s.k) (hl : l % s.k = l1 % s.k) : s.a l j = s.a l1 j1 :=
  (CHANGE_A_SCS_MODL_p28 s hs l l1 j hl).trans (CHANGE_A_SCS_MODR_p28 s hs j j1 l1 hj)

/-- HOL `CHANGE_B_SCS_MODL` (NUXCOEA.hl:263). -/
theorem CHANGE_B_SCS_MODL_p28 (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
    (hj : j % s.k = j1 % s.k) : s.b j l = s.b j1 l :=
  modPeriodic2_first_p28 (by have := hs.2.1; omega) hs.2.2.2.2.2.2.2.2.2.2.1 hj

/-- HOL `CHANGE_B_SCS_MODR` (NUXCOEA.hl:275). -/
theorem CHANGE_B_SCS_MODR_p28 (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
    (hj : j % s.k = j1 % s.k) : s.b l j = s.b l j1 :=
  modPeriodic2_second_p28 (by have := hs.2.1; omega) hs.2.2.2.2.2.2.2.2.2.2.1 hj

/-- HOL `CHANGE_B_SCS_MOD` (NUXCOEA.hl:287). -/
theorem CHANGE_B_SCS_MOD_p28 (s : ScsV39) (hs : isScsV39 s) (j j1 l l1 : ℕ)
    (hj : j % s.k = j1 % s.k) (hl : l % s.k = l1 % s.k) : s.b l j = s.b l1 j1 :=
  (CHANGE_B_SCS_MODL_p28 s hs l l1 j hl).trans (CHANGE_B_SCS_MODR_p28 s hs j j1 l1 hj)

/-- HOL `CHANGE_W_IN_BBS_MOD_LE3` (NUXCOEA.hl:299). -/
theorem CHANGE_W_IN_BBS_MOD_LE3_p28 (s : ScsV39) (w : ℕ → V3) (j j1 : ℕ)
    (hk : 3 ≤ s.k) (hbb : BBsV39 s w) (hj : j % s.k = j1 % s.k) : w j = w j1 :=
  modPeriodic_p28 (by omega) hbb.2.1 hj

/-- HOL `CHANGE_W_IN_BBS_MOD_IS_SCS` (NUXCOEA.hl:311). -/
theorem CHANGE_W_IN_BBS_MOD_IS_SCS_p28 (s : ScsV39) (w : ℕ → V3) (j j1 : ℕ)
    (hs : isScsV39 s) (hbb : BBsV39 s w) (hj : j % s.k = j1 % s.k) : w j = w j1 :=
  CHANGE_W_IN_BBS_MOD_LE3_p28 s w j j1 (by have := hs.2.1; omega) hbb hj

/-- HOL `EXPAND_PERIODIC` (NUXCOEA.hl:325). -/
theorem EXPAND_PERIODIC_p28 (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : BBsV39 s w) :
    w (l + s.k) = w l := h.2.1 l

/-- Origin-based three-point collinearity (the shape of every `collinear
{vec 0, _, _}` hypothesis in this file). -/
theorem collinear_origin_pair_p28 (a b : V3) :
    Collinear ℝ ({0, a, b} : Set V3) ↔
      ∃ v : V3, (∃ r : ℝ, a = r • v) ∧ ∃ r : ℝ, b = r • v := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · rintro ⟨p₀, v, hv⟩
    obtain ⟨r0, h0⟩ := hv 0 (by simp)
    obtain ⟨ra, ha⟩ := hv a (by simp)
    obtain ⟨rb, hb⟩ := hv b (by simp)
    simp only [vadd_eq_add] at h0 ha hb
    have hpa : p₀ = -(r0 • v : V3) := by
      have h : p₀ + r0 • v = 0 := by rw [add_comm]; exact h0.symm
      rw [← eq_neg_iff_add_eq_zero] at h
      exact h
    refine ⟨v, ⟨ra - r0, ?_⟩, ⟨rb - r0, ?_⟩⟩
    · rw [ha, hpa, sub_smul, sub_eq_add_neg]
    · rw [hb, hpa, sub_smul, sub_eq_add_neg]
  · rintro ⟨v, ⟨r1, hr1⟩, ⟨r2, hr2⟩⟩
    refine ⟨(0:V3), v, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by rw [vadd_eq_add, add_zero, zero_smul]⟩
    · exact ⟨r1, by rw [hr1, vadd_eq_add, add_zero]⟩
    · exact ⟨r2, by rw [hr2, vadd_eq_add, add_zero]⟩

/-- HOL `COLLINEAR_EQ_SUB_NEG` (NUXCOEA.hl:329). -/
theorem COLLINEAR_EQ_SUB_NEG_p28 (v1 v2 : V3) :
    Collinear ℝ ({0, -v1, v2 - v1} : Set V3) ↔ Collinear ℝ ({0, v1, v2} : Set V3) := by
  rw [collinear_origin_pair_p28, collinear_origin_pair_p28]
  constructor
  · rintro ⟨v, ⟨r1, hr1⟩, ⟨r2, hr2⟩⟩
    refine ⟨v, ⟨-r1, ?_⟩, ⟨r2 - r1, ?_⟩⟩
    · rw [neg_smul, ← hr1, neg_neg]
    · have e1 : v1 = -(r1 • v) := by rw [← hr1, neg_neg]
      have h := hr2
      rw [e1, sub_eq_add_neg] at h
      rw [sub_smul]
      exact by rw [eq_sub_of_add_eq h, neg_neg]
  · rintro ⟨v, ⟨r1, hr1⟩, ⟨r2, hr2⟩⟩
    refine ⟨v, ⟨-r1, ?_⟩, ⟨r2 - r1, ?_⟩⟩
    · rw [neg_smul, ← hr1]
    · rw [sub_smul, hr2, hr1]

/-- HOL `MIN_LEAST` (NUXCOEA.hl:3664). -/
theorem MIN_LEAST_p28 (X : Set ℕ) (c : ℕ) (hc : c ∈ X) :
    minNum X ∈ X ∧ minNum X ≤ c := by
  have hne : X.Nonempty := ⟨c, hc⟩
  have hleast : ∃ y, y ∈ X ∧ ∀ m ∈ X, y ≤ m :=
    ⟨sInf X, Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩
  have hspec := Classical.epsilon_spec (p := fun n => n ∈ X ∧ ∀ m ∈ X, n ≤ m) hleast
  simp only [minNum]
  exact ⟨hspec.1, hspec.2 c hc⟩

/-- HOL `W_IN_BB_FUN_EQ` (NUXCOEA.hl:3647) — quasi-injectivity of an `MMs`
realisation modulo `k`.  NEEDS: the convex-local-fan injectivity content of
the HOL proof; not mechanical. -/
theorem W_IN_BB_FUN_EQ_p28 (s : ScsV39) (w : ℕ → V3) (x y : ℕ) (hs : isScsV39 s)
    (hbb : BBsV39 s w) (h : w x = w y) : x % s.k = y % s.k := by
  sorry

/-! ## Section 1: the v3_defor_v5 substrate -/

/-- HOL `FUN_V3_DEFOR_V5` (NUXCOEA.hl:2817). -/
theorem FUN_V3_DEFOR_V5_p28 (a x1 x5 x2 : ℝ) (v1 w v : V3) :
    v3DeforV5_p28 a x1 x5 x2 v1 w v = fun t => v3DeforV5_p28 a x1 x5 x2 v1 w v t :=
  rfl

/-- HOL `V_DEFORMATION_V3_DEFOR_V5` (NUXCOEA.hl:2871). -/
theorem V_DEFORMATION_V3_DEFOR_V5_p28 (w : ℕ → V3) (x1 x5 x2 t : ℝ) (v1 v2 : V3) :
    Set.range (fun i => v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1) =
      (fun v => v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) '' Set.range w := by
  ext x
  simp only [Set.mem_range, Set.mem_image, v3DeforV5_p28]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨w i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- HOL `E_DEFORMATION_V3_DEFOR_V5` (NUXCOEA.hl:2880). -/
theorem E_DEFORMATION_V3_DEFOR_V5_p28 (w : ℕ → V3) (x1 x5 x2 t : ℝ) (v1 v2 : V3) :
    Set.range (fun i => {v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
        v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1}) =
      (fun S => (fun v => v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) '' S) ''
        Set.range (fun i : ℕ => {w i, w (i + 1)}) := by
  ext x
  simp only [Set.mem_range, Set.mem_image, v3DeforV5_p28]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨{w i, w (i + 1)}, ⟨i, rfl⟩, by simp [Set.image_pair]⟩
  · rintro ⟨S, ⟨i, rfl⟩, hx⟩
    rw [← hx]
    simp [Set.image_pair]

/-- HOL `F_DEFORMATION_V3_DEFOR_V5` (NUXCOEA.hl:2905). -/
theorem F_DEFORMATION_V3_DEFOR_V5_p28 (w : ℕ → V3) (x1 x5 x2 t : ℝ) (v1 v2 : V3) :
    Set.range (fun i => (v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
        v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1)) =
      (fun uv => (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.1 t,
        v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.2 t)) ''
        Set.range (fun i : ℕ => (w i, w (i + 1))) := by
  ext x
  simp only [Set.mem_range, Set.mem_image, v3DeforV5_p28]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(w i, w (i + 1)), ⟨i, rfl⟩, rfl⟩
  · rintro ⟨uv, ⟨i, rfl⟩, hxy⟩
    exact ⟨i, hxy⟩

/-- HOL `EYYPQDW_CONTINUOUS_LIFT_DIST_ADD` (NUXCOEA.hl:363); `lift` collapses
to the identity (LocalAuto11 convention). -/
theorem EYYPQDW_CONTINUOUS_LIFT_DIST_ADD_p28 (v1 v2 w v : V3)
    (x1 x2 x3 x4 x5 x6 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5) :
    ContinuousAt (fun y => dist (v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 y + w) v) x3 := by
  have hc := EYYPQDW_CONTINUOUS_AT_X_p17 a v1 v2 x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6
    hnc hx1 hx2 hx6 ha hups
  exact (hc.add continuousAt_const).dist continuousAt_const

/-- The deformed edge set `IMAGE (\uv. (v5 (FST uv) t, v5 (SND uv) t)) FF`
(abbreviation used in every azim/interior-angle statement below). -/
noncomputable def deformedFF_p28 (x1 x5 x2 : ℝ) (v1 v2 : V3) (t : ℝ)
    (FF : Set (V3 × V3)) : Set (V3 × V3) :=
  (fun uv => (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.1 t,
    v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.2 t)) '' FF

/-! ## Section 2: the MK deformation family (companion `w (l + k - 1)`) -/

/-- HOL `DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS` (NUXCOEA.hl:336). -/
theorem DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS_p28 (v1 v2 : V3) (x1 x2 x5 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5) (hnorm : ‖v2‖ = 2)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (v2 - v1) t + v1 ∈ ballAnnulus := by
  sorry

/-- HOL `EXISTS_SMALL_LE_CONST_ADD` (NUXCOEA.hl:387). -/
theorem EXISTS_SMALL_LE_CONST_ADD_p28 (v1 v2 w : V3) (x1 x2 x5 c a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hlt : c < dist v2 w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      c < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) w := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_MK_A` (NUXCOEA.hl:413). -/
theorem DEFORMATION_DIST_LE_MK_A_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k)
    (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) → s.a l i < dist v2 (w i)) :
    ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
        s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK` (NUXCOEA.hl:440). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
    (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) → s.a l i < dist v2 (w i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧
        ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) →
        s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `EXISTS_SMALL_LT_CONST_ADD` (NUXCOEA.hl:569). -/
theorem EXISTS_SMALL_LT_CONST_ADD_p28 (v1 v2 w : V3) (x1 x2 x5 c a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hlt : dist v2 w < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) w < c := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_MK` (NUXCOEA.hl:595). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, scsDiag k l i → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i := by
  sorry

/-- HOL `V3_DEFOR_IN_AFF_GT_V1_MK` (NUXCOEA.hl:655). -/
theorem V3_DEFOR_IN_AFF_GT_V1_MK_p28 (v1 v2 w : V3) (x1 x2 x5 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hncw : ¬ Collinear ℝ ({0, v1, w} : Set V3))
    (haff : v2 ∈ affGt {0} {v1, w}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 ∈ affGt {0} {v1, w} := by
  sorry

/-- HOL `V3_DEFOR_INCREASING_IN_ANGLE` (NUXCOEA.hl:705). -/
theorem V3_DEFOR_INCREASING_IN_ANGLE_p28 (v1 v2 w : V3) (x1 x2 x5 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hncw : ¬ Collinear ℝ ({0, v1, w} : Set V3))
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (haff : v2 ∈ affGt {0} {v1, w}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      dist v2 w < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) w := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1` (NUXCOEA.hl:814). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_p28 (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
    (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (l + 1) % k = j % k) (haj : s.a l j = dist v2 (w j)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      s.a l j < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK` (NUXCOEA.hl:848). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
    (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (l + 1) % k = j % k) (haj : s.a l j = dist v2 (w j))
    (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) → s.a l i < dist v2 (w i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
      s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE` (NUXCOEA.hl:890). -/
theorem EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28 (v1 v2 w : V3) (x1 x2 x5 a : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hncw : ¬ Collinear ℝ ({0, v1, w} : Set V3))
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (haff : v2 ∈ affGt {0} {v1, w}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) v1 < dist v2 v1 := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB` (NUXCOEA.hl:927). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))}) :
    ∀ j : ℕ, l % k = (j + 1) % k → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j := by
  sorry

/-- HOL `DIST_V3_DEFOR_EDGE_SUC` (NUXCOEA.hl:981). -/
theorem DIST_V3_DEFOR_EDGE_SUC_p28 (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hj : (l + 1) % k = j % k) (hlt : dist v2 (w j) < s.b l j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1` (NUXCOEA.hl:1004). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_p28 (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (l + 1) % k = j % k) (hlt : dist v2 (w j) < s.b l j)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i : ℕ, ¬(l % k = i % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK` (NUXCOEA.hl:1066). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (l + 1) % k = j % k) (hlt : dist v2 (w j) < s.b l j)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_MK` (NUXCOEA.hl:1189). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) :
    ∀ i : ℕ, ¬(i % k = l % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      0 < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK` (NUXCOEA.hl:1229). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
      0 < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK` (NUXCOEA.hl:1325). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 ≠ w i := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_MK` (NUXCOEA.hl:1347). -/
theorem V3_DEFOR_EQ_IN_FF_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (v2, a') ∈ FF := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_MK_SYM` (NUXCOEA.hl:1438). -/
theorem V3_DEFOR_EQ_IN_FF_MK_SYM_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (a', v2) ∈ FF := by
  sorry

/-- Common hypotheses block of the `DEFORMATION_AZIM_*` family (NUXCOEA.hl:1527). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)) =
      azim 0 v2 (rhoNode1 FF v2) (epPair_p28 FF v2) := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUB_MK` (NUXCOEA.hl:1655). -/
theorem V3_DEFOR_EQ_IN_FF_SUB_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t) =
      v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUB_MK_SYM` (NUXCOEA.hl:1740). -/
theorem V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (a', v1) ∈ FF := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_SUB_MK` (NUXCOEA.hl:1859). -/
theorem DEFORMATION_AZIM_V3_DEFOR_SUB_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)) =
      azim 0 v1 (rhoNode1 FF v1) (epPair_p28 FF v1) := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUC_MK` (NUXCOEA.hl:2003). -/
theorem V3_DEFOR_EQ_IN_FF_SUC_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3,
      (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (w (l + 1), a') ∈ FF := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUC_MK_SYM` (NUXCOEA.hl:2116). -/
theorem V3_DEFOR_EQ_IN_FF_SUC_MK_SYM_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t) =
      v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_SUC_MK` (NUXCOEA.hl:2201). -/
theorem DEFORMATION_AZIM_V3_DEFOR_SUC_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t)) =
      azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) (epPair_p28 FF (w (l + 1))) := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_NOT_MK` (NUXCOEA.hl:2344). -/
theorem V3_DEFOR_EQ_IN_FF_NOT_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) (hv1 : v ≠ v1) (hv2 : v ≠ v2) (hvs : v ≠ w (l + 1))
    (hvV : v ∈ V) :
    ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (v, a') ∈ FF := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_NOT_MK_SYM` (NUXCOEA.hl:2452). -/
theorem V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) (hv1 : v ≠ v1) (hv2 : v ≠ v2) (hvs : v ≠ w (l + 1))
    (hvV : v ∈ V) :
    ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (a', v) ∈ FF := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_NOT_MK` (NUXCOEA.hl:2560). -/
theorem DEFORMATION_AZIM_V3_DEFOR_NOT_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ≠ v1 ∧ v ≠ v2 ∧ v ≠ w (l + 1) ∧
        v ∈ V →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
      azim 0 v (rhoNode1 FF v) (epPair_p28 FF v) := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK` (NUXCOEA.hl:2664). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
      azim 0 v (rhoNode1 FF v) (epPair_p28 FF v) := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK` (NUXCOEA.hl:2741). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_p28 (s : ScsV39) (k : ℕ)
    (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
    (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
      interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) = interiorAngle1 0 FF v := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK` (NUXCOEA.hl:2776). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_p28 (s : ScsV39) (k : ℕ)
    (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
    (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V ∧
        interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ≤ Real.pi := by
  sorry

/-- HOL `V3_DEFOR_DEFORMATION_V5` (NUXCOEA.hl:2820). -/
theorem V3_DEFOR_DEFORMATION_V5_p28 (v1 v2 : V3) (x1 x2 x5 : ℝ) (V : Set V3)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) :
    ∃ ε : ℝ, 0 < ε ∧ Deformation (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2) V (-ε) ε := by
  sorry

/-- HOL `DEFORMATION_LUNAR_AFFINE_HULL_MK` (NUXCOEA.hl:2929). -/
theorem DEFORMATION_LUNAR_AFFINE_HULL_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (v w1 : V3) (x1 x2 x5 a : ℝ) (E : Set (Set V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) (hv : v ≠ v2) (hw1 : w1 ≠ v2)
    (hE : (Set.range fun i : ℕ => {w i, w (i + 1)}) = E) (hlun : Lunar v w1 V E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ∈ Set.Ioo (-ε) ε →
      v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3) := by
  sorry

/-- HOL `V3_DEFOR_CONVEX_LOCAL_FAN_MK` (NUXCOEA.hl:3091, via
`V3_DEFOR_CONVEX_LOCAL_FAN_MK_concl` composed with `ZLZTHIC_concl` and
`MHAEYJN_concl`). -/
theorem V3_DEFOR_CONVEX_LOCAL_FAN_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hnorm2 : ‖v2‖ = 2)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3),
      V = Set.range w → E = (Set.range fun i : ℕ => {w i, w (i + 1)}) →
        ¬ Lunar v (w l) V E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan
        (Set.range fun i : ℕ =>
          v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1)
        (Set.range fun i : ℕ =>
          {v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
           v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1})
        (Set.range fun i : ℕ =>
          (v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
           v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1)) := by
  sorry

/-- HOL `CARD_FF_EQ_V3_DEFOR_DEFORMATION_MK` (NUXCOEA.hl:3271). -/
theorem CARD_FF_EQ_V3_DEFOR_DEFORMATION_MK_p28 (s : ScsV39) (w : ℕ → V3) (k : ℕ)
    (v1 v2 : V3) (a x1 x5 x2 e1 : ℝ) (V : Set V3)
    (hk : s.k = k) (hV : Set.range w = V) (hs : isScsV39 s) (hk3 : 3 < k)
    (hbb : BBsV39 s w)
    (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
      BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) :
    ∀ t : ℝ, 0 < t ∧ t < e1 →
      Nat.card (Set.range fun i : ℕ =>
          (v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t,
           v3DeforV5_p28 a x1 x5 x2 v1 v2 (w (i + 1)) t)) =
      Nat.card (Set.range fun i : ℕ => (w i, w (i + 1))) := by
  sorry

/-- HOL `DSV_V3_DEFOR_EQ_MK` (NUXCOEA.hl:3306). -/
theorem DSV_V3_DEFOR_EQ_MK_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 : V3)
    (a x1 x5 x2 t : ℝ) (hk : s.k = k) (hs : isScsV39 s) (hbb : BBsV39 s w)
    (hJ : ∀ i, ¬ s.J l i) :
    dsvV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 (w l) (w i) t) = dsvV39 s w := by
  sorry

/-- HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1_MK` (NUXCOEA.hl:3440). -/
theorem INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V)
    (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
      BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε →
      interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          ((rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF))^[i]
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k))) := by
  sorry

/-- HOL `TAUSTAR_V3_DEFOR_MK` (NUXCOEA.hl:3551, via `TAUSTAR_V3_DEFOR_MK_concl`). -/
theorem TAUSTAR_V3_DEFOR_MK_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
      BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      taustarV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t) = taustarV39 s w := by
  sorry

/-! ## Section 3: the TWO_CASES family (companion `w (SUC l)`) -/

/-- HOL `DEFORMATION_DIST_LE_MK_A_TWO_CASES` (NUXCOEA.hl:3677). -/
theorem DEFORMATION_DIST_LE_MK_A_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
    (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) → s.a l i < dist v2 (w i)) :
    ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
        s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_TWO_CASES` (NUXCOEA.hl:3703). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (hk : s.k = k) (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) → s.a l i < dist v2 (w i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧
        ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) →
        s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_MK_TWO_CASES` (NUXCOEA.hl:3829). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i, scsDiag k l i → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_TWO_CASES` (NUXCOEA.hl:3889). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (hk : s.k = k) (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : l % k = (j + 1) % k) (haj : s.a l j = dist v2 (w j)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      s.a l j < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_TWO_CASES` (NUXCOEA.hl:3927). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (hk : s.k = k) (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : l % k = (j + 1) % k) (haj : s.a l j = dist v2 (w j))
    (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) → s.a l i < dist v2 (w i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
      s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_TWO_CASES` (NUXCOEA.hl:3975). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))}) :
    ∀ j : ℕ, (l + 1) % k = j % k → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j := by
  sorry

/-- HOL `DIST_V3_DEFOR_EDGE_SUC_TWO_CASES` (NUXCOEA.hl:4018). -/
theorem DIST_V3_DEFOR_EDGE_SUC_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
    (hj : l % k = (j + 1) % k) (hlt : dist v2 (w j) < s.b l j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_TWO_CASES` (NUXCOEA.hl:4042). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : l % k = (j + 1) % k) (hlt : dist v2 (w j) < s.b l j)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∀ i : ℕ, ¬(l % k = i % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i := by
  sorry

/-- HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_TWO_CASES` (NUXCOEA.hl:4109). -/
theorem DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : l % k = (j + 1) % k) (hlt : dist v2 (w j) < s.b l j)
    (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
      dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_MK_TWO_CASES` (NUXCOEA.hl:4224). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) :
    ∀ i : ℕ, ¬(i % k = l % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      0 < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_TWO_CASES` (NUXCOEA.hl:4265). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
      0 < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) := by
  sorry

/-- HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_TWO_CASES` (NUXCOEA.hl:4366). -/
theorem DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3)
    (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
    (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 ≠ w i := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_MK_TWO_CASES` (NUXCOEA.hl:4388). -/
theorem V3_DEFOR_EQ_IN_FF_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
    (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
    (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (v2, a') ∈ FF := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_MK_SYM_TWO_CASES` (NUXCOEA.hl:4478). -/
theorem V3_DEFOR_EQ_IN_FF_MK_SYM_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (a', v2) ∈ FF := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_MK_TWO_CASES` (NUXCOEA.hl:4565). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)) =
      azim 0 v2 (rhoNode1 FF v2) (epPair_p28 FF v2) := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUB_MK_TWO_CASES` (NUXCOEA.hl:4698). -/
theorem V3_DEFOR_EQ_IN_FF_SUB_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t) =
      v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_TWO_CASES` (NUXCOEA.hl:4787). -/
theorem V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (v1, a') ∈ FF := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_SUB_MK_TWO_CASES` (NUXCOEA.hl:4905). -/
theorem DEFORMATION_AZIM_V3_DEFOR_SUB_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)) =
      azim 0 v1 (rhoNode1 FF v1) (epPair_p28 FF v1) := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUC_MK_TWO_CASES` (NUXCOEA.hl:5052). -/
theorem V3_DEFOR_EQ_IN_FF_SUC_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∀ a' : V3,
      (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (a', w (l + k - 1)) ∈ FF := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_SUC_MK_SYM_TWO_CASES` (NUXCOEA.hl:5177). -/
theorem V3_DEFOR_EQ_IN_FF_SUC_MK_SYM_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t) =
      v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_SUC_MK_TWO_CASES` (NUXCOEA.hl:5264). -/
theorem DEFORMATION_AZIM_V3_DEFOR_SUC_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t)) =
      azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1)))
        (epPair_p28 FF (w (l + k - 1))) := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_NOT_MK_TWO_CASES` (NUXCOEA.hl:5404). -/
theorem V3_DEFOR_EQ_IN_FF_NOT_MK_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) (hv : v ≠ w (l + k - 1)) (hv2 : v ≠ v2) (hv1 : v ≠ v1)
    (hvV : v ∈ V) :
    ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (v, a') ∈ FF := by
  sorry

/-- HOL `V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_TWO_CASES` (NUXCOEA.hl:5513). -/
theorem V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_TWO_CASES_p28 (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
    (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
    (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
    (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
    (het : -e < t)
    (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
      v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
    (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) (hv : v ≠ w (l + k - 1)) (hv2 : v ≠ v2) (hv1 : v ≠ v1)
    (hvV : v ∈ V) :
    ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
      (a', v) ∈ FF := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_NOT_MK_TWO_CASES` (NUXCOEA.hl:5620). -/
theorem DEFORMATION_AZIM_V3_DEFOR_NOT_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ≠ w (l + k - 1) ∧ v ≠ v2 ∧
        v ≠ v1 ∧ v ∈ V →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
      azim 0 v (rhoNode1 FF v) (epPair_p28 FF v) := by
  sorry

/-- HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES` (NUXCOEA.hl:5726). -/
theorem DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ)
    (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
    (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
      azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
        (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
        (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
      azim 0 v (rhoNode1 FF v) (epPair_p28 FF v) := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES` (NUXCOEA.hl:5803). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES_p28 (s : ScsV39)
    (k : ℕ) (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
    (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
      interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) = interiorAngle1 0 FF v := by
  sorry

/-- HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_TWO_CASES`
(NUXCOEA.hl:5844). -/
theorem DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_TWO_CASES_p28 (s : ScsV39)
    (k : ℕ) (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
    (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V ∧
        interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
        (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ≤ Real.pi := by
  sorry

/-- HOL `DEFORMATION_LUNAR_AFFINE_HULL_MK_TWO_CASES` (NUXCOEA.hl:5887). -/
theorem DEFORMATION_LUNAR_AFFINE_HULL_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (v w1 : V3) (x1 x2 x5 a : ℝ) (E : Set (Set V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V) (hv : v ≠ v2) (hw1 : w1 ≠ v2)
    (hE : (Set.range fun i : ℕ => {w i, w (i + 1)}) = E) (hlun : Lunar v w1 V E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ∈ Set.Ioo (-ε) ε →
      v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3) := by
  sorry

/-- HOL `V3_DEFOR_CONVEX_LOCAL_FAN_MK_TWO_CASES` (NUXCOEA.hl:6046, via
`V3_DEFOR_CONVEX_LOCAL_FAN_MK_TWO_CASES_concl`). -/
theorem V3_DEFOR_CONVEX_LOCAL_FAN_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hnorm2 : ‖v2‖ = 2)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3),
      V = Set.range w → E = (Set.range fun i : ℕ => {w i, w (i + 1)}) →
        ¬ Lunar v (w l) V E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan
        (Set.range fun i : ℕ =>
          v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1)
        (Set.range fun i : ℕ =>
          {v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
           v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1})
        (Set.range fun i : ℕ =>
          (v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
           v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1)) := by
  sorry

/-- HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_TWO_CASES` (NUXCOEA.hl:6228). -/
theorem INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3)
    (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
    (hV : Set.range w = V)
    (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
      BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε →
      interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
          ((rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF))^[i]
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l % k)) t)) =
      interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k))) := by
  sorry

/-- HOL `TAUSTAR_V3_DEFOR_MK_TWO_CASES` (NUXCOEA.hl:6343, via
`TAUSTAR_V3_DEFOR_MK_TWO_CASES_concl`). -/
theorem TAUSTAR_V3_DEFOR_MK_TWO_CASES_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
    (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
    (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
    (ha : a = -1)
    (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
      BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
      taustarV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t) = taustarV39 s w := by
  sorry

/-! ## Section 4: the terminal registry twins -/

/-- HOL `MHAEYJN_concl` as a proposition (appendix.hl:25; theorem statement
in LocalAuto1).  NEEDS: the Lunar_deform lane. -/
def MHAEYJN_prop_p28 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (v w u : V3),
    ConvexLocalFan V E FF →
    Lunar v w V E →
    Deformation f V a b →
    interiorAngle1 0 FF v < Real.pi →
    u ∈ V → u ≠ v → u ≠ w →
    (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
    (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Lunar v w ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- HOL `ZLZTHIC_concl` as a proposition (appendix.hl:45; theorem statement
in LocalAuto1).  NEEDS: the ZLZTHIC lane (LocalAuto14). -/
def ZLZTHIC_prop_p28 : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3),
    ConvexLocalFan V E FF →
    Generic V E →
    Deformation f V a b →
    (∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Generic ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- HOL `NUXCOEA` (NUXCOEA.hl:6469; `mk_imp (ZLZTHIC_concl, mk_imp
(MHAEYJN_concl, NUXCOEA_concl))`).  DISCHARGES: proving this discharges the
`ZLZTHIC_p14`/`MHAEYJN` registry antecedents for the a-edge pin. -/
theorem NUXCOEA_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (hz : ZLZTHIC_prop_p28) (hm : MHAEYJN_prop_p28)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k ∨ (j + 1) % k = l % k)
    (haj : s.a j l = dist (w j) (w l)) (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3),
      V = Set.range w → E = (Set.range fun i : ℕ => {w i, w (i + 1)}) →
        ¬ Lunar v (w l) V E) :
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
    s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) := by
  sorry

/-- HOL `NUXCOEAv2` (NUXCOEA.hl:7711; `NUXCOEA_concl` without the
`ZLZTHIC`/`MHAEYJN` antecedents, via `NUXCOEA` + the registry theorems). -/
theorem NUXCOEAv2_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hj : j % k = (l + 1) % k ∨ (j + 1) % k = l % k)
    (haj : s.a j l = dist (w j) (w l)) (hbj : dist (w j) (w l) < s.b j l)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3),
      V = Set.range w → E = (Set.range fun i : ℕ => {w i, w (i + 1)}) →
        ¬ Lunar v (w l) V E) :
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
    s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) := by
  sorry

/-- HOL `IMJXPHRv2` (NUXCOEA.hl:7717; statement `IMJXPHR_concl`,
IMJXPHR.hl:9682). -/
theorem IMJXPHRv2_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ)
    (hk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
    (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
    (hk3 : 3 < k)
    (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
    (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hnorm : ‖w l‖ ≠ 2)
    (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3),
      V = Set.range w → E = (Set.range fun i : ℕ => {w i, w (i + 1)}) →
        ¬ Lunar v (w l) V E) :
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
    s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) := by
  sorry

/-- HOL `ODXLSTCv2` (NUXCOEA.hl:7723; statement `ODXLSTCv2_concl`,
ODXLSTC.hl:1695; a `False`-shaped no-go lemma). -/
theorem ODXLSTCv2_p28 (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ)
    (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k)
    (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
    (hnorm : ‖w l‖ ≠ 2)
    (hlt : ∀ i : ℕ, ¬(i % k = l % k) → s.a l i < dist (w l) (w i))
    (hJ : ∀ i, ¬ s.J l i)
    (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3),
      V = Set.range w → E = (Set.range fun i : ℕ => {w i, w (i + 1)}) →
        ¬ Lunar v (w l) V E) :
    False := by
  sorry

end Kepler.Text

/-
Kepler/Text/LocalFanStepW22.lean — wave W22 §0：v2 链条（槽范围收紧的机械复刻）。

三件 v2（证明体与 v1 逐字，仅签名收紧）：
* `pW6k7_v2`：`hslot_w` 加 `0 < j`（j=0 假支剔除，W21 判定）；
* `pW6k8_v2`：affGe `hslot_w` 加 `0 < j`；
* `pW19_v2`：`hprev` 收紧为 `2 ≤ n`（n=1 假支剔除，W20 反证）+
  `pW19_nkezbfc_prep_p9_v2`（下游重述 v2，hslots 的 hprev 分量为 n ≥ 2 形）。
既有 v1 陈述零改。
-/
import Kepler.Text.LocalFanStepW21

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **W6-K6 patch B v2（stepB 核心，槽范围收紧）**：hslot_w 加 `0 < j`
（j=0 假支剔除，W21 判定）；其余同 v1。 -/
theorem pW6k7_stepB_sol_nonneg_v2
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hk4 : 3 < V.ncard)
    (hslot_u : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 1 < V.ncard →
      azim 0 ((rhoNode1_p2 FF)^[j] p)
        (ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)) p = 0)
    (hslot_w : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 2 < V.ncard →
      azim 0 ((rhoNode1_p2 FF)^[j+1] p)
        (rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p)) p = 0) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  by_cases hallpi : ∀ x ∈ V, Real.pi ≤ interiorAngle1_p2 0 FF x
  · exact pC_sol_nonneg_of_angle_ge_pi hcl hallpi
  · push Not at hallpi
    obtain ⟨v₀, hv₀, hnge⟩ := hallpi
    have hint : interiorAngle1_p2 0 FF v₀ < Real.pi := hnge
    by_cases hB : ¬ ∀ i : ℕ, i < V.ncard →
      azim 0 v₀ ((rhoNode1_p2 FF)^[1] v₀) ((rhoNode1_p2 FF)^[i] v₀) = 0 ∨
        azim 0 v₀ ((rhoNode1_p2 FF)^[1] v₀) ((rhoNode1_p2 FF)^[i] v₀) =
          azim 0 v₀ ((rhoNode1_p2 FF)^[1] v₀) ((rhoNode1_p2 FF)^[V.ncard - 1] v₀)
    · exact False.elim (pW3c_gap_contradiction hcl hg hnc hv₀ hk4 hint hB)
    · push Not at hB
      -- B 支：vv/bta 装配
      let vv : ℕ → V3 := fun n => (rhoNode1_p2 FF)^[n] v₀
      let bta : ℕ → ℝ := fun i => azim 0 v₀ (vv 1) (vv i)
      have hiter : ∀ n, (rhoNode1_p2 FF)^[n] v₀ = vv n := fun _ => rfl
      have hbta : ∀ i, azim 0 v₀ (vv 1) (vv i) = bta i := fun _ => rfl
      have hcol : ∀ z ∈ V, z ≠ v₀ → ¬ Collinear ℝ ({0, v₀, z} : Set V3) :=
        PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg v₀ hv₀
      have hB' : ∀ i : ℕ, i < V.ncard → bta i = 0 ∨ bta i = bta (V.ncard - 1) := by
        intro i hi
        rw [← hbta i, ← hbta (V.ncard - 1), ← hiter 1, ← hiter i,
          ← hiter (V.ncard - 1)]
        exact hB i hi
      obtain ⟨i, hikm1, hbi0, hbilast⟩ :=
        pW2b_jump_exists hcl hv₀ rfl hk4 hiter hbta hB'
      have hvvV : ∀ n, vv n ∈ V := fun n => by
        rw [← hiter n]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hv₀ n
      rcases Nat.eq_zero_or_pos i with hiz | hpos
      · -- i = 0：int(v₀) = bta(k−1) = bta 1 = 0，与内角正性矛盾
        obtain ⟨hfirst, -, -, -⟩ :=
          EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hv₀ rfl hcol hiter hbta
        have h01 : i + 1 = 1 := by rw [hiz]
        have hbk : bta (V.ncard - 1) = 0 := by
          rw [← hbilast, h01]
          exact hfirst
        have hint0 : 0 < interiorAngle1_p2 0 FF v₀ := INTERIOR_ANGLE1_POS hlf hv₀
        have hzero : interiorAngle1_p2 0 FF v₀ = 0 := by
          show azim 0 v₀ (rhoNode1_p2 FF v₀) (ivsRhoNode1_p2 FF v₀) = 0
          have hlast := pW1_azim_last hlf hv₀ rfl hiter hbta
          rw [hbk] at hlast
          exact hlast
        exact (hint0.ne' hzero).elim
      · -- 0 < i：K 案装配
        have hD := pW2_interior_eq_pi hcl hv₀ rfl hk4 hikm1 hpos hcol hiter hbta
          hbi0 hbilast
        have hcollapse := pW2_sum_collapse hcl hv₀ rfl hiter hD
        have huV : vv i ∈ V := hvvV i
        have hwV : vv (i + 1) ∈ V := hvvV (i + 1)
        by_cases hF : ∃ x, x ∈ ({v₀, vv i, vv (i + 1)} : Set V3) ∧
          Real.pi ≤ interiorAngle1_p2 0 FF x
        · have hsV : ({v₀, vv i, vv (i + 1)} : Set V3) ⊆ V := by
            intro p hp
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
            rcases hp with rfl | rfl | rfl
            · exact hv₀
            · exact huV
            · exact hwV
          exact pW2_some_ge_pi_nonneg hcl hsV hcollapse hF
        · push Not at hF
          -- else：三点全 < π，K 案
          have hltV : interiorAngle1_p2 0 FF v₀ < Real.pi := hint
          have hltU : interiorAngle1_p2 0 FF (vv i) < Real.pi :=
            hF (vv i) (by simp)
          have hltW : interiorAngle1_p2 0 FF (vv (i + 1)) < Real.pi :=
            hF (vv (i + 1)) (by simp)
          -- ρ(u) = w、ι(w) = u
          have hrho : rhoNode1_p2 FF (vv i) = vv (i + 1) := by
            rw [← hiter i, ← hiter (i + 1), show i + 1 = Nat.succ i from rfl,
              Function.iterate_succ_apply']
          have hivs : ivsRhoNode1_p2 FF (vv (i + 1)) = vv i := by
            have h := pW6k6_iter_ivs hlf hv₀ hiter (by omega : 0 < i + 1)
            rw [show i + 1 - 1 = i from by omega] at h
            exact h
          -- M1/M2
          have hM1 : vv i ∈ affGt ({0, v₀} : Set V3) {rhoNode1_p2 FF v₀} :=
            (pW4_flat_run hcl hg hv₀ rfl hiter hbta (by omega : i < V.ncard) hpos
              hbi0).1
          have hM2 : vv (i + 1) ∈ affGt ({0, v₀} : Set V3)
              {ivsRhoNode1_p2 FF v₀} :=
            pW5b_flat_mem hcl hg hv₀ rfl hiter hbta hikm1 hbilast (by omega)
              (by omega)
          -- 槽实例化（径向零点形态）
          have hS3 : azim 0 (vv i) (ivsRhoNode1_p2 FF (vv i)) v₀ = 0 := by
            have hs := hslot_u v₀ hv₀ i hpos (by omega)
            rwa [hiter i] at hs
          have hS4 : azim 0 (vv (i + 1)) (rhoNode1_p2 FF (vv (i + 1))) v₀ = 0 := by
            rcases Nat.lt_or_ge (i + 2) V.ncard with hlt2 | hge2
            · have hs := hslot_w v₀ hv₀ i hpos (by omega)
              rwa [hiter (i + 1)] at hs
            · -- i + 2 = k：ρ(w) = v₀（周期回卷），azim_self
              have heq : i + 2 = V.ncard := by omega
              have hid : (rhoNode1_p2 FF)^[V.ncard] v₀ = v₀ :=
                LOFA_IMP_ITER_RHO_NODE_ID hlf hv₀
              have hρw : rhoNode1_p2 FF (vv (i + 1)) = v₀ := by
                rw [← hiter (i + 1)]
                have hstep : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[i + 1] v₀)
                    = (rhoNode1_p2 FF)^[i + 2] v₀ := by
                  rw [show i + 2 = Nat.succ (i + 1) from rfl]
                  exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (i + 1) v₀).symm
                rw [hstep, heq, hid]
              rw [hρw]
              exact azim_self (0 : V3) (vv (i + 1)) v₀
          -- hcop：u 项识别式（仅扇性质）+ AZIM_COND_FOR_COPLANAR 两向
          have hρuw : ¬ Collinear3 (0 : V3) (vv i) (vv (i + 1)) := by
            have h := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf huV
            rwa [hrho] at h
          have hncI : ¬ Collinear3 (0 : V3) (vv i) (ivsRhoNode1_p2 FF (vv i)) :=
            LOFA_IMP_NOT_COLL_IVS hlf huV
          have hvne : vv i ≠ v₀ := by
            have hd := LOFA_IMP_DIS_ELMS23 hlf hv₀ 0 i (by omega) (by omega)
            rw [hiter i, show (rhoNode1_p2 FF)^[0] v₀ = v₀ from rfl] at hd
            exact hd
          have hncv : ¬ Collinear3 (0 : V3) (vv i) v₀ := by
            have h := hcol (vv i) huV hvne
            rw [show ({0, v₀, vv i} : Set V3) = ({0, vv i, v₀} : Set V3) from by
              ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
            exact h
          have hmem5 : v₀ ∈ affGt ({0, vv i} : Set V3)
              {ivsRhoNode1_p2 FF (vv i)} :=
            (azim_eq_zero_iff_alt hncI hncv).mp hS3
          have haid_u : interiorAngle1_p2 0 FF (vv i)
              = azim 0 (vv i) (vv (i + 1)) v₀ := by
            show azim 0 (vv i) (rhoNode1_p2 FF (vv i))
              (ivsRhoNode1_p2 FF (vv i)) = azim 0 (vv i) (vv (i + 1)) v₀
            rw [hrho, (azim_eq_azim_iff hρuw hncI hncv).mpr hmem5]
          have hintUpos : 0 < interiorAngle1_p2 0 FF (vv i) :=
            INTERIOR_ANGLE1_POS hlf huV
          have hcop : ¬ Coplanar ({0, v₀, vv i, vv (i + 1)} : Set V3) := by
            intro hc
            have hset : ({0, vv i, vv (i + 1), v₀} : Set V3)
                = ({0, v₀, vv i, vv (i + 1)} : Set V3) := by
              ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
            rw [← hset] at hc
            rcases (AZIM_COND_FOR_COPLANAR (0 : V3) (vv i) (vv (i + 1)) v₀).mpr hc
              with h0 | hπ
            · rw [← haid_u] at h0
              exact hintUpos.ne' h0
            · rw [← haid_u] at hπ
              exact hltU.ne hπ
          -- 识别式（patch A §5 主件，槽已实例化）+ W6K5 ④ 收口
          have haid := pW6k6_identification hlf hv₀ huV hwV hrho hivs hM1 hM2
            hS3 hS4 hcop
          exact pW6k5_sol_nonneg_of_azim_id hcl hcollapse hcop
            ⟨haid.1.symm, haid.2.1.symm, haid.2.2.symm⟩ ⟨hltV, hltU, hltW⟩


/-- **patch ① 孪生形 v2**：槽为望远镜直供的 affGe 成员形态（hslot_w 加 `0 < j`），
`ι(vv j p) ∈ affGe {0} {p, vv j p}`、`ρ(vv(j+1) p) ∈ affGe {0} {p, vv(j+1) p}`。 -/
theorem pW6k8_stepB_sol_nonneg_affGe_v2
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hk4 : 3 < V.ncard)
    (hslot_u : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 1 < V.ncard →
      ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)
        ∈ affGe ({0} : Set V3) {p, (rhoNode1_p2 FF)^[j] p})
    (hslot_w : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 2 < V.ncard →
      rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p)
        ∈ affGe ({0} : Set V3) {p, (rhoNode1_p2 FF)^[j+1] p}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ p ∈ V, ∀ n : ℕ, (rhoNode1_p2 FF)^[n] p ∈ V :=
    fun p hp n => LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  refine pW6k7_stepB_sol_nonneg_v2 hcl hg hnc hk4 ?_ ?_
  · -- hslot_u：affGe 成员 ⇒ 径向零点
    intro p hp j hj0 hj
    have huV : (rhoNode1_p2 FF)^[j] p ∈ V := hVV p hp j
    have hpu : p ≠ (rhoNode1_p2 FF)^[j] p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 j (by omega) (by omega)
      rw [show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
      exact fun h => hd h.symm
    have hmem := hslot_u p hp j hj0 hj
    rw [Set.pair_comm] at hmem
    have hnc_up : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j] p) p := by
      have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
        ((rhoNode1_p2 FF)^[j] p) huV (Ne.symm hpu)
      rwa [← show ({0, (rhoNode1_p2 FF)^[j] p, p} : Set V3)
        = ({0, p, (rhoNode1_p2 FF)^[j] p} : Set V3) from by
        ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    have hι : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j] p)
        (ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)) :=
      LOFA_IMP_NOT_COLL_IVS hlf huV
    have hz := pW6k6_azim_zero_of_affGe
      (a := (rhoNode1_p2 FF)^[j] p) (x := p)
      (y := ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p))
      (fun h => h0V (h ▸ huV)) hpu (fun h => h0V (h ▸ hp)) hnc_up hmem
    exact (azim_eq_zero_symm hnc_up hι).mp hz
  · -- hslot_w：affGe 成员 ⇒ 径向零点
    intro p hp j hj0 hj
    have hwV : (rhoNode1_p2 FF)^[j+1] p ∈ V := hVV p hp (j + 1)
    have hpw : p ≠ (rhoNode1_p2 FF)^[j+1] p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 (j + 1) (by omega) (by omega)
      rw [show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
      exact fun h => hd h.symm
    have hmem := hslot_w p hp j hj0 hj
    rw [Set.pair_comm] at hmem
    have hnc_wp : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j+1] p) p := by
      have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
        ((rhoNode1_p2 FF)^[j+1] p) hwV (Ne.symm hpw)
      rwa [← show ({0, (rhoNode1_p2 FF)^[j+1] p, p} : Set V3)
        = ({0, p, (rhoNode1_p2 FF)^[j+1] p} : Set V3) from by
        ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    have hρ : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j+1] p)
        (rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p)) :=
      LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hwV
    have hz := pW6k6_azim_zero_of_affGe
      (a := (rhoNode1_p2 FF)^[j+1] p) (x := p)
      (y := rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p))
      (fun h => h0V (h ▸ hwV)) hpw (fun h => h0V (h ▸ hp)) hnc_wp hmem
    exact (azim_eq_zero_symm hnc_wp hρ).mp hz


/-- **W19 装配 v2**：`hprev` 槽范围收紧为 `2 ≤ n`（n=1 假支剔除，W20 反证）；`hstep` 不变。 -/
theorem pW19_stepB_sol_nonneg_v2
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 0 < n → n + 1 < V.ncard →
        vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
    (hprev : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
        vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  by_cases hlt : 3 < V.ncard
  · refine pW6k8_stepB_sol_nonneg_affGe_v2 hcl hg hnc hlt ?_ ?_
    · -- u 侧 affGe 槽：pW4_telescope_u + 端点自成员
      intro p hp j hj0 hj
      have hstepb : ∀ n : ℕ, 0 < n → n + 1 ≤ j →
          (rhoNode1_p2 FF)^[n] p ∈ affGt ({0} : Set V3)
            {p, (rhoNode1_p2 FF)^[n + 1] p} :=
        fun n hn hnj => hstep p hp (fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl)
          n hn (by omega)
      have htel := pW4_telescope_u (i := j) hcl hp
        (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hstepb
      have hne1 : (rhoNode1_p2 FF)^[j - 1] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[j - 1] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp (j - 1)
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne2 : (rhoNode1_p2 FF)^[j] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[j] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp j
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne12 : (rhoNode1_p2 FF)^[j - 1] p ≠ (rhoNode1_p2 FF)^[j] p := by
        have hd := LOFA_IMP_DIS_ELMS23 hlf hp (j - 1) j (by omega) (by omega)
        exact Ne.symm hd
      have hidxj : j - 1 + 1 = j := by omega
      have hmemL : (rhoNode1_p2 FF)^[j - 1] p ∈ affGe ({0} : Set V3)
          {(rhoNode1_p2 FF)^[j - 1] p, (rhoNode1_p2 FF)^[j - 1 + 1] p} := by
        rw [hidxj]
        exact pW19_mem_affGe_pair_left hne1 hne2 hne12
      have hz := (htel (j - 1) (by omega) ((rhoNode1_p2 FF)^[j - 1] p)).mpr
        ⟨j - 1, le_rfl, hmemL⟩
      rw [hidxj] at hz
      have hιeq : ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)
          = (rhoNode1_p2 FF)^[j - 1] p :=
        pW6k6_iter_ivs hlf hp (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hj0
      rw [hιeq]
      exact hz
    · -- w 侧 affGe 槽：pW5w_telescope（i := 1，hprev-v2）+ 端点自成员
      intro p hp j hj0 hj
      have hprevb : ∀ n : ℕ, 1 + 1 ≤ n → n ≤ V.ncard - 1 →
          (rhoNode1_p2 FF)^[n] p ∈ affGt ({0} : Set V3)
            {p, (rhoNode1_p2 FF)^[n - 1] p} :=
        fun n hn hk => hprev p hp (fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl)
          n (by omega) hk
      have htel := pW5w_telescope (i := 1) hcl hp
        (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hprevb
      have hjt : V.ncard - j - 2 < V.ncard - 1 - 1 := by omega
      have hne1 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp _
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne2 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp _
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne12 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p
          ≠ (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p := by
        have hd := LOFA_IMP_DIS_ELMS23 hlf hp
          (V.ncard - (V.ncard - j - 2) - 1) (V.ncard - (V.ncard - j - 2))
          (by omega) (by omega)
        exact Ne.symm hd
      have hidx1 : V.ncard - (V.ncard - j - 2) - 1 = j + 1 := by omega
      have hidx2 : V.ncard - (V.ncard - j - 2) = j + 2 := by omega
      have hz := (htel (V.ncard - j - 2) hjt
        ((rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p)).mpr
        ⟨V.ncard - j - 2, le_rfl,
          pW19_mem_affGe_pair_right hne1 hne2 hne12⟩
      rw [hidx1] at hz
      rw [hidx2] at hz
      have hρw : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j + 1] p) = (rhoNode1_p2 FF)^[j + 2] p := by
        rw [show j + 2 = Nat.succ (j + 1) from rfl]
        exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (j + 1) p).symm
      rw [hρw]
      exact hz
  · -- 假支：ncard = 3
    have h3 : 3 ≤ V.ncard := CARD_VERTEX_GE_3_LOCAL_FAN_p9 hcl
    exact SOL_LOCAL_FAN_POS_CASE3_p9 hcl (by omega)

/-! ## ## §3 LA9:3196 下游同形重述 -/

/-- `NKEZBFC_PREP_p9`（LA9:3196，证明体占位桩）的下游同形重述：陈述逐字 + 几何槽前提。 -/
theorem pW19_nkezbfc_prep_p9_v2
    (h : EJRCFJD_concl_p9)
    (hslots : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      (∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 0 < n → n + 1 < V.ncard →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
      ∧ (∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)})) :
    ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      convexLocalFan_p2 V E FF → generic_p2 V E → 0 ≤ solLocal_p9 E FF := by
  intro V E FF hcl hg
  exact p9_main_induction h
    (fun V' E' FF' hcl' hg' hnc' =>
      pW19_stepB_sol_nonneg_v2 hcl' hg' hnc'
        (hslots V' E' FF' hcl' hg').1 (hslots V' E' FF' hcl' hg').2)
    V.ncard V E FF hcl hg rfl


end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW6k7_stepB_sol_nonneg_v2
#print axioms Kepler.Text.pW6k8_stepB_sol_nonneg_affGe_v2
#print axioms Kepler.Text.pW19_stepB_sol_nonneg_v2
#print axioms Kepler.Text.pW19_nkezbfc_prep_p9_v2

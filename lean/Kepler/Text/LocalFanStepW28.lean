/-
Kepler/Text/LocalFanStepW28.lean — wave W28：v4 链 part 1（run 前件 hstep 的槽层复刻）。

W26 §2 方案落地：v2 链的 `hslot_u` 槽被 **run 前件 hstep** 取代——
`hstep : ∀ p ∈ V, ∀ vv, hiter → ∀ i, i+1 < V.ncard → hflat → hnc →
  ∀ n, 0 < n → n+1 ≤ i → vv n ∈ affGt{0}{p, vv(n+1)}`
（即 `pW5_flat_cone_order` 的实例化形：消费者（K 案）处由 EGHNAVX 本地供给
hflat、hcol 供给 hnc；槽的最终放电 = `pW26_hstep_at_run`）。
`hslot_w` 用 W27 的诚实域 `0 < j`（j=0 假支已由 W27 反证）。

件目：
* §1 私有支 `pW28_slot_u_at`：hstep 在跳跃索引处的 u 侧径向零点实例
  （run 前件本地供给 + 望远镜 + `pW6k6_azim_zero_of_affGe` 换序）。
* §2 `pW6k7_stepB_sol_nonneg_v4`：v2 主件机械复刻（hslot_u → hstep）。
* §3 `pW6k8_stepB_sol_nonneg_affGe_v4`：v2 孪生形机械复刻（w 侧转换照旧，
  hstep 直传）。
`pW19_v4` 留 part 2。
-/
import Kepler.Text.LocalFanStepW27

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 私有支：hstep 在跳跃索引的 u 侧放电 -/

/-- run 前件 hstep ⇒ u 侧径向零点实例 `azim 0 (vv i) (ι(vv i)) p = 0`
（hflat 由 EGHNAVX 首 run 本地供给、hnc 由 hcol 供给；望远镜到 affGe
成员后经 `pW6k6_azim_zero_of_affGe` + `azim_eq_zero_symm` 换序）。 -/
private theorem pW28_slot_u_at (hcl : convexLocalFan_p2 V E FF)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {i : ℕ}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    (hbta : ∀ n, azim 0 p (vv 1) (vv n) = bta n)
    (hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3))
    (hik : i + 1 < V.ncard) (hbi : bta i = 0) (hi0 : 0 < i)
    (hstep : ∀ (i : ℕ), i + 1 < V.ncard →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1}) →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n)) →
      ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)}) :
    azim 0 (vv i) (ivsRhoNode1_p2 FF (vv i)) p = 0 := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hvvV : ∀ n : ℕ, vv n ∈ V := fun n => by
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  -- run 前件本地供给：hflat（EGHNAVX 首 run）+ hnc（hcol）
  obtain ⟨-, -, -, hflatE⟩ :=
    EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hp rfl hcol hiter hbta
  have hrun := (hflatE i).1 ⟨hbi, by omega⟩
  have hflatI : ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1} := by
    intro n hn hni
    exact hrun.2 ⟨n, hn, by omega, rfl⟩
  have hncI : ∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n) := by
    intro n hn hni
    have hne : vv n ≠ p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 n (by omega) (by omega)
      rw [hiter n, show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
      exact hd
    have h := hcol (vv n) (hvvV n) hne
    simpa only [Collinear3] using h
  -- 槽应用 @ i → 望远镜 → affGe 成员
  have hrun2 := hstep i hik hflatI hncI
  have htel := pW4_telescope_u (i := i) hcl hp hiter hrun2
  have hne1 : vv (i - 1) ≠ 0 := fun h => h0V (h ▸ hvvV (i - 1))
  have hne2 : vv i ≠ 0 := fun h => h0V (h ▸ hvvV i)
  have hne12 : vv (i - 1) ≠ vv i := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp (i - 1) i (by omega) (by omega)
    rw [hiter i, hiter (i - 1)] at hd
    exact Ne.symm hd
  have hidxj : i - 1 + 1 = i := by omega
  have hmemL : vv (i - 1) ∈ affGe ({0} : Set V3) {vv (i - 1), vv (i - 1 + 1)} := by
    rw [hidxj]
    exact pW19_mem_affGe_pair_left hne1 hne2 hne12
  have hz := (htel (i - 1) (by omega) (vv (i - 1))).mpr ⟨i - 1, le_rfl, hmemL⟩
  rw [hidxj] at hz
  have hιeq : ivsRhoNode1_p2 FF (vv i) = vv (i - 1) := pW6k6_iter_ivs hlf hp hiter hi0
  have hz' : ivsRhoNode1_p2 FF (vv i) ∈ affGe ({0} : Set V3) {p, vv i} := hιeq ▸ hz
  rw [Set.pair_comm] at hz'
  -- 换序：affGe 成员 ⇒ 径向零点
  have hpv : p ≠ vv i := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 i (by omega) (by omega)
    rw [hiter i, show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
    exact fun h => hd h.symm
  have hnc_up : ¬ Collinear3 (0 : V3) (vv i) p := by
    have h := hcol (vv i) (hvvV i) (Ne.symm hpv)
    simp only [Collinear3] at h ⊢
    rwa [show ({0, p, vv i} : Set V3) = ({0, vv i, p} : Set V3) from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hι : ¬ Collinear3 (0 : V3) (vv i) (ivsRhoNode1_p2 FF (vv i)) := by
    simpa only [Collinear3] using LOFA_IMP_NOT_COLL_IVS hlf (hvvV i)
  have hz2 := pW6k6_azim_zero_of_affGe (a := vv i) (x := p)
    (y := ivsRhoNode1_p2 FF (vv i))
    (fun h => h0V (h ▸ hvvV i)) hpv (fun h => h0V (h ▸ hp)) hnc_up hz'
  exact (azim_eq_zero_symm hnc_up hι).mp hz2

/-! ## §2 v4 主件（hslot_u → run 前件 hstep） -/

/-- **W6-K6 patch B v4（stepB 核心，hstep 槽 run 前件形）**：v2 主件的机械复刻
——`hslot_u` 被 run 前件 hstep 取代（K 案处本地供给 hflat/hnc），`hslot_w`
保持 W27 诚实域 `0 < j`；其余与 v2 逐字一致。 -/
theorem pW6k7_stepB_sol_nonneg_v4
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hk4 : 3 < V.ncard)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ (i : ℕ), i + 1 < V.ncard →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1}) →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n)) →
      ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
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
          -- 槽实例化：u 侧（hstep run 前件，K 案处本地放电）+ w 侧（径向零点）
          have hS3 : azim 0 (vv i) (ivsRhoNode1_p2 FF (vv i)) v₀ = 0 :=
            pW28_slot_u_at hcl hv₀ hiter hbta hcol (by omega) hbi0 hpos
              (fun i' => hstep v₀ hv₀ vv hiter i')
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
                have hstep2 : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[i + 1] v₀)
                    = (rhoNode1_p2 FF)^[i + 2] v₀ := by
                  rw [show i + 2 = Nat.succ (i + 1) from rfl]
                  exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (i + 1) v₀).symm
                rw [hstep2, heq, hid]
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

/-! ## §3 v4 孪生形（affGe 槽层，hstep 直传） -/

/-- **patch ① 孪生形 v4**：`hslot_u` 被 run 前件 hstep 取代（直传主件），
`hslot_w` 保持 W27 诚实域 `0 < j` 的 affGe 形态；w 侧转换与 v2 逐字一致。 -/
theorem pW6k8_stepB_sol_nonneg_affGe_v4
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hk4 : 3 < V.ncard)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ (i : ℕ), i + 1 < V.ncard →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1}) →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n)) →
      ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
    (hslot_w : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 2 < V.ncard →
      rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p)
        ∈ affGe ({0} : Set V3) {p, (rhoNode1_p2 FF)^[j+1] p}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ p ∈ V, ∀ n : ℕ, (rhoNode1_p2 FF)^[n] p ∈ V :=
    fun p hp n => LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  refine pW6k7_stepB_sol_nonneg_v4 hcl hg hnc hk4 hstep ?_
  -- hslot_w：affGe 成员 ⇒ 径向零点
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

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW6k7_stepB_sol_nonneg_v4
#print axioms Kepler.Text.pW6k8_stepB_sol_nonneg_affGe_v4

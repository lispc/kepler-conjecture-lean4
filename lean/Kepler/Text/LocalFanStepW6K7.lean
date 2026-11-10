/-
Kepler/Text/LocalFanStepW6K7.lean — wave C-W6-K6 patch B：三分支总装（stepB 核心）。

分支骨架（HOL NKEZBFC.hl:1718-2614 总装结构）：
* `hallpi` 支：`pC_sol_nonneg_of_angle_ge_pi`（C0，已落）。
* violator + ¬B 支：`pW3c_gap_contradiction`（BW3c，已闭合 False）。
* violator + B 支：`pW2b_jump_exists` 跳跃索引 → D/E（BW2）→ F 支
  （`pW2_some_ge_pi_nonneg`）收口 / else 支（三点全 < π）进 K 案：
  - i = 0 子情形：bta 1 = bta(k−1) = 0（EGHNAVX 首合取支）+ `pW1_azim_last`
    给 int(v) = 0，与 `INTERIOR_ANGLE1_POS` 矛盾；
  - 0 < i：M1/M2（`pW4_flat_run`/`pW5b_flat_mem`）+ 望远镜槽（径向零点
    形态，hprev 终点显式槽保留）+ `pW6k6_identification` + hcop
    （`AZIM_COND_FOR_COPLANAR`，公开标准三，probe 实测）⇒
    `pW6k5_sol_nonneg_of_azim_id`（W6K5 ④）。
-/
import Kepler.Text.LocalFanStepW6K6
import Kepler.Text.LocalFanStepBW3c

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## ## 三分支总装主件 -/

/-- **W6-K6 patch B（stepB 核心）**：generic、无 flat 对（hnc）、`3 < V.ncard`
的凸局部扇上，配合望远镜槽（径向零点形态，hprev 终点显式槽保留），
`0 ≤ solLocal_p9 E FF`。 -/
theorem pW6k7_stepB_sol_nonneg
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hk4 : 3 < V.ncard)
    (hslot_u : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 1 < V.ncard →
      azim 0 ((rhoNode1_p2 FF)^[j] p)
        (ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)) p = 0)
    (hslot_w : ∀ p : V3, p ∈ V → ∀ j : ℕ, j + 2 < V.ncard →
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
            · have hs := hslot_w v₀ hv₀ i (by omega)
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

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6k7_stepB_sol_nonneg
#print axioms Kepler.Text.pW6k7_stepB_sol_nonneg

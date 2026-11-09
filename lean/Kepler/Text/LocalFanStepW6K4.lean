/-
Kepler/Text/LocalFanStepW6K4.lean — wave C-W6-K3 步骤 ②（1_3 形开性）+ ③（ΣdihV ≥ π）。

路线勘误（机器证据，logs/probe2.log）：工单的「半空间表示 + Cramer 反向」
路线不需要——库内 PlanarityAuto12:877 `OPEN_AFF_GT_1_3` 是公开件且标准三
（probe2 输出：'Kepler.Text.OPEN_AFF_GT_1_3' depends on axioms:
[propext, choice, Quot.sound]），② 一步消费；省出预算落 ③（工单标记
「就绪」的接线，本波一并闭合）。被替换的自证草稿（半空间路线，~180 行，
未过编译）存快照 `LocalFanStepW6K4.selfproof_draft.lean` 备查。

件目：
* §1 `pW6k4_affGt_1_3_isOpen`：消费 `OPEN_AFF_GT_1_3`。
* §2 `pW6k4_notCoplanar_distinct`：`SolidAngle:396` private 版公开复制
  （逐字模式，未改原文件）。
* §3 `pW6k4_dihV_sum_ge_pi`：② 开 + W6K3① 非空 + `IsOpen.measure_pos`
  + `volume_solid_triangle` + `ENNReal.ofReal_pos`。
-/
import Kepler.Text.PlanarityAuto12
import Kepler.Text.LocalFanStepW6K3
import Kepler.Geom.SolidAngle

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## §1 1_3 形开性（消费公开件） -/

/-- **W6-K3 ②**：`affGt {0}{v,u,w}` 开。 -/
theorem pW6k4_affGt_1_3_isOpen {v u w : V3}
    (hcop : ¬ Coplanar ({0, v, u, w} : Set V3)) :
    IsOpen (affGt ({0} : Set V3) ({v, u, w} : Set V3)) :=
  OPEN_AFF_GT_1_3 0 v u w hcop

/-! ## §2 非共面四点的两两互异 -/

/-- `¬ Coplanar {0,v,u,w}` 给出两两互异（`SolidAngle:396` private 版的
公开复制，逐字模式）。 -/
theorem pW6k4_notCoplanar_distinct {v u w : V3}
    (hcop : ¬ Coplanar ({0, v, u, w} : Set V3)) :
    v ≠ 0 ∧ u ≠ 0 ∧ w ≠ 0 ∧ v ≠ u ∧ v ≠ w ∧ u ≠ w := by
  have hsub : ∀ {x y z : V3}, ({0, v, u, w} : Set V3) ⊆ ({x, y, z} : Set V3) →
      Coplanar ({0, v, u, w} : Set V3) :=
    fun {x y z} h => (coplanar_triple x y z).subset h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hcop (hsub (x := 0) (y := u) (z := w) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v) (z := w) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v) (z := u) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := u) (z := w) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := u) (z := v) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))
  · intro h
    exact hcop (hsub (x := 0) (y := v) (z := u) (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl <;> simp [h]))

/-! ## ## §3 ΣdihV ≥ π -/

/-- **W6-K3 ③**：`dihV 0 v u w + dihV 0 u w v + dihV 0 w v u ≥ π`。 -/
theorem pW6k4_dihV_sum_ge_pi {v u w : V3}
    (hcop : ¬ Coplanar ({0, v, u, w} : Set V3)) :
    Real.pi ≤ dihV 0 v u w + dihV 0 u w v + dihV 0 w v u := by
  obtain ⟨hv0, hu0, hw0, hvu, hvw, huw⟩ := pW6k4_notCoplanar_distinct hcop
  have hopen := pW6k4_affGt_1_3_isOpen hcop
  have hne := pW6k2_affGt_nonempty hv0 hu0 hw0 hvu hvw huw
  have hvolpos : 0 < volume (affGt ({0} : Set V3) {v, u, w} ∩ Metric.ball (0 : V3) 1) :=
    (hopen.inter Metric.isOpen_ball).measure_pos volume hne
  rw [Set.inter_comm] at hvolpos
  rw [volume_solid_triangle (by norm_num : (0 : ℝ) < 1) hcop] at hvolpos
  have hpos := (ENNReal.ofReal_pos).mp hvolpos
  have h1 : (1 : ℝ) ^ 3 = 1 := one_pow 3
  rw [h1, mul_one] at hpos
  have hdiv : 0 < dihV 0 v u w + dihV 0 u w v + dihV 0 w v u - Real.pi :=
    (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mp hpos
  linarith

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6k4_affGt_1_3_isOpen
#print axioms Kepler.Text.pW6k4_affGt_1_3_isOpen
#print axioms Kepler.Text.pW6k4_notCoplanar_distinct
#print axioms Kepler.Text.pW6k4_dihV_sum_ge_pi

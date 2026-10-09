/-
  probe_sum_volD_falsity.lean — 2026-10-08 GT-sumvolD 波独立探针（最小必要）。
  目的：判定 PA23 冻结巨人 `grutoti_sum_volD`（PackingAuto23.lean:4418-4424）
  在冻结前提面（仅 `he : e = {u0, u1}`，V u0 u1 r d 全自由）下是否可证。
  结论（本探针全真证、零 sorry）：不可证——反例 `V = ∅`。
    · `mcellSet ∅ = ∅`：`barV ∅ 3 ul` 要求非空初始子列的 `setOfList ⊆ ∅`，
      而长度 = 4 的列必有成员，矛盾；故 `grutotiEdgeCells ∅ e = ∅`，
      `setSum ∅ _ = 0`。
    · 而 `volume.real (grutotiConicCap u0 u1 1 (1/2)) > 0`（u0 ≠ u1）——
      ConicCapVolume:961 公共件 `volumeConicCapPos`（PA23 `grutoti_volD_pos`
      的共享版，即 GRUTOTI §I 锚）。左端 0 ≠ 右端正数，恒等式假。
  头部结构复刻 PA23（import 面取 PA23 头部的同款；触及的件全部来自
  PA2 公共 defs + ConicCapVolume 公共定理）。两 defs 逐字私拷
  （PA23 内 private，探针不可 import）。
-/
import Kepler.Text.PackingAuto2
import Kepler.Text.ConicCapVolume
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto17
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/- PA23:175-178 逐字私拷。 -/
private def grutotiConicCap (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩ rconeGt v0 v1 a

/- PA23:197-200 逐字私拷。 -/
private def grutotiEdgeCells (V : Set V3) (e : Set V3) : Set (Set V3) :=
  {X | X ∈ mcellSet V ∧ e ∈ edgeX V X}

/-- 反例主件：对每对 `u0 ≠ u1`（无需任何 V-成员/饱和/装填前提），取
`V := ∅`、`r := 1`、`d := 1/2`、`e := {u0, u1}`，冻结陈述为假。 -/
theorem probe_sum_volD_frozen_false (u0 u1 : V3) (hne : u0 ≠ u1) :
    ¬ ∀ (V : Set V3) (e : Set V3) (r d : ℝ), e = {u0, u1} →
        (grutotiEdgeCells V e).Finite ∧
          setSum (grutotiEdgeCells V e)
            (fun X => volume.real (X ∩ grutotiConicCap u0 u1 r d)) =
            volume.real (grutotiConicCap u0 u1 r d) := by
  intro h
  obtain ⟨-, hsum⟩ := h (∅ : Set V3) {u0, u1} 1 (1 / 2) rfl
  -- 第一步：`mcellSet ∅ = ∅`（barV 的 voronoiNondg 门要求非空子列落在 ∅ 里）。
  have hms : mcellSet (∅ : Set V3) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    simp only [mcellSet, Set.mem_setOf_eq]
    rintro X ⟨i, ul, -, hbar⟩
    exfalso
    rcases ul with _ | ⟨a, t⟩
    · have h4 := hbar.1
      simp at h4
    · obtain ⟨_, hsub, _⟩ :=
        hbar.2 (a :: t) ⟨⟨[], (List.append_nil (a :: t)).symm⟩, by simp⟩
      exact Set.notMem_empty a (hsub (by simp [setOfList]))
  -- 第二步：`grutotiEdgeCells ∅ e = ∅`（成员式第一合取支已封死）。
  have hempty : grutotiEdgeCells (∅ : Set V3) {u0, u1} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun X hX => ?_
    have hXm : X ∈ mcellSet (∅ : Set V3) := hX.1
    rw [hms] at hXm
    exact Set.notMem_empty X hXm
  -- 第三步：空指标集上 `setSum = 0`。
  have h0 : setSum (∅ : Set (Set V3))
      (fun X => volume.real (X ∩ grutotiConicCap u0 u1 1 (1 / 2))) = 0 := by
    rw [setSum, dif_pos Set.finite_empty, Set.Finite.toFinset_empty]
    exact Finset.sum_empty
  rw [hempty, h0] at hsum
  -- 第四步：右端体积为正（volumeConicCapPos；ccvConicCap 与 grutotiConicCap 同体）。
  have hvol : (0 : ℝ) < volume.real (grutotiConicCap u0 u1 1 (1 / 2)) :=
    volumeConicCapPos (by norm_num) (by norm_num) (by norm_num) hne
  rw [← hsum] at hvol
  linarith

/-- 封闭推论：冻结陈述（PA23:4418-4423 全量词形式逐字）蕴含 `False`——
具体反例点 `0 ≠ single 0 1`。 -/
theorem probe_frozen_statement_contra :
    (∀ (V : Set V3) (u0 u1 : V3) (e : Set V3) (r d : ℝ), e = {u0, u1} →
        (grutotiEdgeCells V e).Finite ∧
          setSum (grutotiEdgeCells V e)
            (fun X => volume.real (X ∩ grutotiConicCap u0 u1 r d)) =
            volume.real (grutotiConicCap u0 u1 r d)) → False := by
  intro hst
  obtain ⟨w, hw⟩ : ∃ w : V3, w ≠ 0 :=
    ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
      intro hcon
      exact absurd (Iff.mp (PiLp.single_eq_zero_iff 2 (0 : Fin 3)) hcon)
        (by norm_num : (1 : ℝ) ≠ 0)⟩
  exact probe_sum_volD_frozen_false 0 w (fun hcon => hw hcon.symm)
    (fun V e r d lhe => hst V 0 w e r d lhe)

/-- SF 最小前提面的机器验证（有限性半边）：冻结签名**只补** `hp hs` 两条
前提后，第一合取支 `(grutotiEdgeCells V e).Finite` 一行即得——PA15:775
`FINITE_EDGE_X2 V e u0 u1 hp hs he`（真证，GT-2 波 FILLED）的结论
`{X | mcellSet V X ∧ edgeX V X e}.Finite` 与 `grutotiEdgeCells V e` 同体
（`∈`-定义 unfolding）。即：SF 立案后有限性支零数学内容、纯接线。 -/
theorem probe_finite_with_hp_hs (V : Set V3) (e : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hs : saturated V) (he : e = {u0, u1}) :
    (grutotiEdgeCells V e).Finite :=
  FINITE_EDGE_X2 V e u0 u1 hp hs he

end Kepler.Text

/-
  Kepler.Text.Reduction5J5K4N1 — K4 C3：HOL `n1_diff_n0`（reduction4.hl:3314–3655；
  与 K2CONCLUSION BETWN 2 / reductionK2Concl 同式）。

  ┌─ 替位判词（派单第 2 条，先侦察后写证）──────────────────────────
  │ 两条 HOL 零命中依赖均有在库原生替身，且**无需补写 75–120**：
  │ ① `Aq1.betwn_not_in_fst_faltten`（AQ1.hl:1241）
  │    ↦ `TameSpine.windowFstNotMemNFlatten`（JcajyduAqSplit1D:87；文件头
  │      明记 = 该 HOL 件 Lean 内核，AQ1.hl:1247；链层经 ly/lz/findFace 三桥折回）。
  │ ② `Aq9.CASES_CORE`（AQ9.hl:421，610 HOL 行）
  │    ↦ `TameSpine.aq9_provenance`（JcajyduAqLeaf9W1b:170；文件头明记
  │      「原生 CASES_CORE 等价物」：`v ∈ quotient N' ⇒ v ∈ quotient N ∨ v ∈ 窗口 FST`）。
  │ 其余 HOL 依赖（`rtrans_diff_r` → `rtransDiffR`、`quotient_list_elements` →
  │ `quotientListElements`）亦全在库。
  └────────────────────────────────────────────────────────────────

  路线：集合相等双向。
  · A\\B ⊆ C：A（新表首点）→ `quotientListElements` 转新表 quotient 顶点 →
    `aq9_provenance` 二分；旧表支与 B 相抵（`quotientListElements` 反用），
    窗口支折回链层即 C。
  · C ⊆ A\\B：d ∈ 窗口 ⇒ d ∈ rtrans 1（`rtransDiffR` 反用）⇒ z ∈ A；
    B 由 `windowFstNotMemNFlatten` 直接给（d.1 = z）。

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf9W1b
import Kepler.Text.TameSpine.JcajyduAqSplit1D
import Kepler.Text.Reduction5J5Red2Pieces
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.PwssratFace

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList elementsOfList)
open Kepler.Text.ChainLists (markedList)

/-- **HOL `n1_diff_n0`**（reduction4.hl:3314–3655；K2 BETWN 2 同式）：
一步后的顶点集增量 = 窗口 `betwn (find_face x) (l'y) (l'z)` 的首点集。 -/
theorem n1DiffN0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    {z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
        z ∉ N.flatten.map (fun d => d.1)} =
      {z : ℕ | z ∈ (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).map
        (fun d => d.1)} := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r :=
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have hmS1 : Kepler.Text.TameSpine.MarkedListSpineFull hL
      (Kepler.Text.TameSpine.ntransSpine L N r x 1)
      (Kepler.Text.TameSpine.rtransSpine L N r x 1) x :=
    Kepler.Text.TameSpine.aqiunpp3_top L hL 1 hgn hmS
  have hnt : ntrans L N r x 1 = Kepler.Text.TameSpine.ntransSpine L N r x 1 :=
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm 1
  have hy : ly L r x = Kepler.Text.TameSpine.lYSpine L r x :=
    Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf
  have hz : lz L N r x = Kepler.Text.TameSpine.lZSpine L N r x :=
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf
  obtain ⟨hlyf, -, -⟩ := Kepler.Text.Reduction4Idx.pplhuljV0 L hL hgn hunL hm hnf
  have hff : findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x) = findFaceDarts L x := by
    rw [← hy]
    exact Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hlyf
  have hdBet_chain : ∀ {d : Dart}, d ∈ between (findFaceDarts L x) (ytrans L N r x 0)
      (ztrans L N r x 0) → d ∈ between (findFaceDarts L x) (ly L r x) (lz L N r x) := by
    intro d hd
    simpa [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.ztrans_def,
      Kepler.Text.Reduction5.rtrans_zero, Kepler.Text.Reduction5.ntrans_zero] using hd
  ext z
  constructor
  · -- A\B ⊆ C
    rintro ⟨hzA, hzB⟩
    obtain ⟨d, hdfl, hd1⟩ := List.mem_map.mp hzA
    have hdflS : d ∈ (Kepler.Text.TameSpine.ntransSpine L N r x 1).flatten := by
      rwa [← hnt]
    have hzElNew : z ∈ elementsOfList
        (Kepler.Text.TameSpine.quotientListSpine L
          (Kepler.Text.TameSpine.ntransSpine L N r x 1)) := by
      have hEl := Kepler.Text.TameSpine.quotientListElements L hL hmS1.1.2.1
      rw [hEl]
      exact List.mem_map.mpr ⟨d, hdflS, hd1⟩
    have hv : z ∈ (Kepler.Text.TameSpine.quotientListSpine L
        (Kepler.Text.TameSpine.ntransSpine L N r x 1)).flatten := by
      have h' : z ∈ (Kepler.Text.TameSpine.quotientListSpine L
          (Kepler.Text.TameSpine.ntransSpine L N r x 1)).flatten.eraseDups := hzElNew
      rwa [List.mem_eraseDups] at h'
    rcases Kepler.Text.TameSpine.aq9_provenance L hL hgn hunL hmS hfS hv with hOld | hWin
    · -- 旧表支：与 z ∉ B 相抵
      exfalso
      apply hzB
      have hEl := Kepler.Text.TameSpine.quotientListElements L hL hmS.1.2.1
      have h' : z ∈ elementsOfList (Kepler.Text.TameSpine.quotientListSpine L N) := by
        show z ∈ (Kepler.Text.TameSpine.quotientListSpine L N).flatten.eraseDups
        rw [List.mem_eraseDups]
        exact hOld
      rw [hEl] at h'
      simpa [Kepler.Text.TameSpine.setOfListNatSpine] using h'
    · -- 窗口支：折回链层
      rw [hff, ← hy, ← hz] at hWin
      simpa [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.ztrans_def,
        Kepler.Text.Reduction5.rtrans_zero, Kepler.Text.Reduction5.ntrans_zero] using hWin
  · -- C ⊆ A\B
    rintro hzC
    obtain ⟨d, hdBet, hd1⟩ := List.mem_map.mp hzC
    constructor
    · -- z ∈ A：窗口 dart ∈ rtrans 1 ⊆ ntrans 1
      have hdR : d ∈ rtrans L N r x 1 := by
        have h := hdBet_chain hdBet
        rw [← rtransDiffR L hL hgn hm hnf] at h
        exact (List.mem_filter.mp h).1
      have hdfl : d ∈ (ntrans L N r x 1).flatten :=
        List.mem_flatten.mpr ⟨rtrans L N r x 1, (haq hgn N r x hm 1).2.2.1, hdR⟩
      exact List.mem_map.mpr ⟨d, hdfl, hd1⟩
    · -- z ∉ B：窗口首点不进旧表首点表
      have hdBetS : d ∈ between (findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x))
          (Kepler.Text.TameSpine.lYSpine L r x) (Kepler.Text.TameSpine.lZSpine L N r x) := by
        rw [hff, ← hy, ← hz]
        exact hdBet_chain hdBet
      have hnot := Kepler.Text.TameSpine.windowFstNotMemNFlatten L hL hgn hunL hmS hfS hdBetS
      simpa [hd1] using hnot

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.n1DiffN0

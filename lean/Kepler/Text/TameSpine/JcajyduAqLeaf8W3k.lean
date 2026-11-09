/-
  JcajyduAqLeaf8W3k — AQ8 波 3k：GSUBGOAL#3（环状细化）的**可闭半边**。

  ┌─ 判定（先报）─────────────────────────────────────────────────
  │ #3 的合取两项判然不同：
  │ ① `FST (HD u) = FST (HD v)`：**可闭**（partsFst 两次 + 弧 ⊆ r +
  │    `partsMemExists`）——本文件落成无条件（相对塔接口槽）。
  │ ② `∀ a ∈ u, a ∈ v`（containment）：**需新的分区边界归纳**——
  │    即「线性/环状子弧的 parts 被整体 parts 细化」。已落的两件都不够：
  │    - `aqs_partsContiguousRefine` 需两处 junction 断点（wrap 情形 + 断点
  │      在应用侧不可得，W3d-i 已证）；
  │    - `partsCat` 的断点前提同样不可得。
  │    精确缺口形状见 DELIVERY §AQ8W3k-2（估 60–100），**本波不硬凑**。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① aq8w3k_partRefineFst  #3 的 FST 半边：
  │    `∀ u ∈ parts L (弧 3 段), ∃ v ∈ parts L r, (HD u).1 = (HD v).1`
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）────────────────────────────────────────────────
  │ 弧 3 段取 HOL 的 `s = [z] ++ betwn r z y ++ [y]` 具体项；
  │ `FST o HD` ↦ `fun p => p.head!.1`；`MEM` 逐字。
  │ 塔接口槽 `h1..h5` 与 `hsN`（弧 ∈ ntrans）为既有口径（AA 与 W1a 同）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3k_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3i
import Kepler.Text.TameSpine.JcajyduBetwnMap

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- **#3 的 FST 半边**（零槽）：`u` 取自环状弧 `[z] ++ between r z y ++ [y]`
的 parts，则存在 `v ∈ parts L r` 使 `(HD u).1 = (HD v).1`。

路径：`d = HD u ∈ u ⊆ 弧 ⊆ r`（`memPartsImp` + `aq8w3b_arcSubset`）
⇒ `partsMemExists` 取 `v ∋ d` ⇒ `partsFst`（r 侧）直接给 `d.1 = v.head!.1`
= `(HD u).1`（左端 rfl）。弧的 Nodup/非空由 `r.Nodup` + 端点
（`uniqBetwn`、`zMemRtransClean`、`ytransMemRtrans`、`hyneSupply`）就地供。 -/
theorem aq8w3k_partRefineFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ u ∈ partsSpine L ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]),
      ∃ v ∈ partsSpine L r, (u.head!).1 = (v.head!).1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnR : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  have hrnd : r.Nodup := (normalListUniqNonnil hnR hrN).1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzyd : lZSpine L N r x ≠ lYSpine L r x := Ne.symm (hyneSupply L hL hgn hunL hm hf)
  have hnd' : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]).Nodup := uniqAppendBetwn hrnd hz hy hzyd
  have hne : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ≠ [] := by
    intro h0
    have h1 : lZSpine L N r x ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_singleton_self _))))
    rw [h0] at h1
    exact List.not_mem_nil h1
  have harc : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x])
      = [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x] := rfl
  intro u hu
  have hune : u ≠ [] := partsAllNonnil L hnd' hne u hu
  have hup : u.head! ∈ u := List.head!_mem_self hune
  have hus : u.head! ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) := memPartsImp L hnd' hne hu _ hup
  have hur : u.head! ∈ r := aq8w3b_arcSubset L hL hgn hm hf harc _ hus
  obtain ⟨v, hv, hdv⟩ := partsMemExists L hrnd hur
  exact ⟨v, hv, partsFst L hL hnR hrN hv hdv⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3k_partRefineFst

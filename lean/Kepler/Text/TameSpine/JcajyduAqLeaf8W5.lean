/-
  JcajyduAqLeaf8W5 — AQ8 `aq8Concl` 装配骨架（A 路 + C 路 + final 支；B 路显式槽）。

  目标：`aq8Concl_of_uniqSnd (hB : …) : aq8Concl L hL`
  （B 路 `uniq (core L SND)` 落地后一行代入；**本件不是叶收口件**）。

  `aq8Concl L hL`（TowerBase:277）=
  `∀ N r x, hgn → hm → ∀ q ∈ quotientListSpine L (ntrans 1), q.Nodup`。

  结构（HOL AQ8.hl:3341-3406 AQ8 主证）：
  · final 支：`ntransId` ⇒ `ntrans 1 = N`；目标回到 `hm.1.2.2.2.2.1.1`
    （marked 合取 5 前件 `∀ q ∈ quotientListSpine L N, q.Nodup`）。
  · ¬final 支：`ntrans1` 展开 `replace r [S] N ++ [F]`；逐行 `s ∈ ntrans 1` 三路：
    - `s = S` ⇒ **`hB` 槽**（B 路；SND 的 core Nodup）；
    - `s = F` ⇒ **`aq8w4d_uniqFstSplitNormalParts`**（A 路；注意其陈述 = `parts F` 头表，
      与 `quotientListSpine` 的 `coreListSpine`/`coreSpine` 定义形逐字对齐，见 §1 的 `hqmap`）；
    - `s ∈ N`（旧行，含 spurious `s = r`）⇒ `hm.1.2.2.2.2.1.1` 投影
      （`s ∈ N` ⇒ `core s ∈ quotientListSpine L N`）。
  · `quotientListSpine L (ntrans 1)` 展开为 `(ntrans 1).map (fun s => core s)`（`hqmap`），
    逐 `q` 取行 `s` 归到上面的 `hrow`。

  DIFFERS：`hB` 用 `(partsSpine L SND).map (fun p => p.head!.1)` 直接形（= `coreSpine L SND`
  的定义展开；避免 `coreSpine` 包装层的 rw 雷区）。
  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W4d
import Kepler.Text.TameSpine.TameList7
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **AQ8 装配骨架**：SND 路（B 路）作为显式槽，A 路（FST）+ C 路（旧行）+ final 支已接。 -/
theorem aq8Concl_of_uniqSnd (L : fgraph ℕ) (hL : GoodList L)
    (hB : ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
      GoodListNodesTl L hL → MarkedListSpineFull hL N r x → ¬finalListSpine L r →
      ((partsSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2).map
          (fun p => p.head!.1)).Nodup) :
    aq8Concl L hL := by
  intro N r x hgn hm
  by_cases hfin : finalListSpine L r
  · -- final 支：ntrans 1 = N，直接投影旧 quotient
    rw [ntransId L N r x hfin]
    exact hm.1.2.2.2.2.1.1
  · -- ¬final 支
    have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    have hfaceY : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hfin).1
    set S := (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).2 with hSdef
    set F := (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 with hFdef
    have hsplitS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 = S := by
      rw [hSdef, hfaceY]
    have hsplitF : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 = F := by
      rw [hFdef, hfaceY]
    have hn : ntransSpine L N r x 1 = replaceSpine r [S] N ++ [F] := by
      rw [ntrans1 L N r x hfin, hsplitS, hsplitF]
    -- 逐行：core Nodup
    have hrow : ∀ s ∈ ntransSpine L N r x 1,
        ((partsSpine L s).map (fun p => p.head!.1)).Nodup := by
      intro s hs
      have hscat : s ∈ replaceSpine r [S] N ++ [F] := hn ▸ hs
      rcases List.mem_append.mp hscat with hrep | hlast
      · rcases memReplaceCases hrep with hN | ⟨-, hS⟩
        · -- C 路：旧行（含 s = r 幻影支——r ∈ N，其 core 本就在 quotient 内）
          have hqN : ((partsSpine L s).map (fun p => p.head!.1)) ∈ quotientListSpine L N := by
            show _ ∈ coreListSpine (N.map (partsSpine L))
            exact List.mem_map.mpr
              ⟨partsSpine L s, List.mem_map.mpr ⟨s, hN, rfl⟩, rfl⟩
          exact (hm.1.2.2.2.2.1.1) _ hqN
        · -- B 路槽
          have hseq : s = S := List.mem_singleton.mp hS
          rw [hseq]
          have hBs := hB N r x hgn hm hfin
          rwa [hsplitS] at hBs
      · -- A 路
        have hFeq : s = F := List.mem_singleton.mp hlast
        rw [hFeq]
        have hA := aq8w4d_uniqFstSplitNormalParts L hL hgn hm hfin
        rwa [hsplitF] at hA
    -- quotientListSpine 展开为逐行 core 表
    have hqmap : quotientListSpine L (ntransSpine L N r x 1)
        = (ntransSpine L N r x 1).map
            (fun s => (partsSpine L s).map (fun p => p.head!.1)) := by
      simp only [quotientListSpine, coreListSpine, List.map_map]
      rfl
    rw [hqmap]
    intro q hq
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    exact hrow s hs

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq8Concl_of_uniqSnd

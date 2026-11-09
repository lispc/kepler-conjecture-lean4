/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W3b — AQ4 叶主证 `aq4`（`aq4Concl` 槽，冻结陈述）。

  骨架（W3 DELIVERY §4）：
  - final 支：`ntransId`（ntrans = N）⇒ 旧 `NormalListSpine` 的 loop 投影；
  - ¬final 支：`ntrans1`（list 级 replace 形）⇒ `memReplaceCases` 两源
    （`s ∈ N` 旧投影 / `s = s2`）+ `List.mem_append` 右支（`s = s1`）；
    三源分别 = 旧环投影 / W2 `aq4_loopS2` / W3a-iii `aq4_loopS1`。
  落库即塔 9/13。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3aIII

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **AQ4 叶主证**（HOL `AQ4_concl`，AQ4.hl:692；槽陈述冻结于 TowerBase:248）。 -/
theorem aq4 (L : fgraph ℕ) (hL : GoodList L) : aq4Concl L hL := by
  intro N r x hgn hm s hs
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin] at hs
    exact hm.1.2.1.2.2.2.1 s hs
  · rw [ntrans1 L N r x hfin] at hs
    have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
    have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
      nextElPrevElUniq hrnd _
    rcases List.mem_append.mp hs with h | h
    · -- replace 段：`s ∈ N` 或 `s = s2`
      rcases memReplaceCases h with hN | ⟨-, hs2⟩
      · exact hm.1.2.1.2.2.2.1 s hN
      · rw [List.mem_singleton.mp hs2]
        have hs2eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
            = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
                ++ [lYSpine L r x])
              ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                  (lZSpine L N r x) := by
          simp only [splitNormalListSpine]
          rw [hnextz1]
        rw [hs2eq]
        exact aq4_loopS2 L hL hgn hm hfin
    · -- 尾段：`s = s1`
      rw [List.mem_singleton.mp h]
      have hs1eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
          = (((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)).map (ndSpine L)).flatten).reverse
            ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
                (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
        rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x)), hnextz1]
      rw [hs1eq]
      exact aq4_loopS1 L hL hgn hm hfin

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4

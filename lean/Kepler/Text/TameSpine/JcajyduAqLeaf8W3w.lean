/-
  JcajyduAqLeaf8W3w — AQ8 波 3w：junction ⑤ 主件**去槽**（支 2b 补齐）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① aq8w3w_betwnFaceHead  无 `hd0` 槽的完整三支：
  │    `between f y z ≠ [] ⇒ (between f y z).head! = fList L (l'y)`
  │    （支 1 / 支 2a 由 W3v `aq8w3v_betwnFaceHead`，支 2b 本波补）
  └────────────────────────────────────────────────────────────────

  ┌─ 支 2b 的关键：`obtain ⟨a,t,rfl⟩ : ∃ a t, f = a :: t` ───────────
  │ 该形在子证明内**直接替换** `f`（W3b 同款），避免 `cases h : f` 在
  │ `hy : l'y ∈ f` 依赖下的 generalize 失败；替换后 head! 与 [0] 同值为 rfl 级。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3w_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3v

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup mem_darts_of_mem_findFace)

/-- **junction ⑤ 完整形（无 `hd0` 槽）**：`between f y z ≠ []` 时
其首元 = `fList L (l'y)`。支 2b（`y` 为面表末元、`between` 走 wrap-take）
本波补：`f = a :: t` 形态下 `head! = [0]` 与 `nextEl` 的 `getD 0` 同值。 -/
theorem aq8w3w_betwnFaceHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hfarne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) ≠ []) :
    (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).head! = fList L (lYSpine L r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hy : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr (memYtransListOfDarts L hL hgn hm hf)
  have hz : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  by_cases hd0 : (findFaceDarts L (lYSpine L r x)).drop
      ((findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1) = []
  · -- 支 2b：drop 空 ⇒ y 为末元 ⇒ between 的 take 支
    have hfl : fList L (lYSpine L r x)
        = nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) := rfl
    rw [hfl, betwnTakeDrop hfnd hz]
    rw [if_neg (show ¬ (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x)
        < (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x) from by
      have hle := List.drop_eq_nil_iff.mp hd0
      have hlt : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x)
          < (findFaceDarts L (lYSpine L r x)).length := List.idxOf_lt_length_iff.mpr hy
      have h2 : (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)
          < (findFaceDarts L (lYSpine L r x)).length :=
        List.idxOf_lt_length_iff.mpr hz
      omega)]
    rw [hd0, List.nil_append]
    -- 目标：`(f.take (idx z)).head! = nextEl f y`
    have hidx : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x)
        = (findFaceDarts L (lYSpine L r x)).length - 1 := by
      have hle := List.drop_eq_nil_iff.mp hd0
      have hlt : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x)
          < (findFaceDarts L (lYSpine L r x)).length := List.idxOf_lt_length_iff.mpr hy
      omega
    have hp : 0 < (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x) := by
      rcases Nat.eq_zero_or_pos
        ((findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)) with h0 | h0
      · exfalso
        apply hfarne
        rw [betwnTakeDrop hfnd hz]
        rw [if_neg (show ¬ (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x)
            < (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x) from by
          have hle := List.drop_eq_nil_iff.mp hd0
          have hlt : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x)
              < (findFaceDarts L (lYSpine L r x)).length :=
            List.idxOf_lt_length_iff.mpr hy
          have h2 : (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)
              < (findFaceDarts L (lYSpine L r x)).length :=
            List.idxOf_lt_length_iff.mpr hz
          omega)]
        rw [hd0, List.nil_append, h0, List.take_zero]
      · exact h0
    have hpos : 0 < (findFaceDarts L (lYSpine L r x)).length := List.length_pos_of_mem hy
    rw [aq8w3u_head!_take_pos _ hp, Kepler.Text.TameLp.nextEl_eq_getD hy, hidx,
      show (findFaceDarts L (lYSpine L r x)).length - 1 + 1
        = (findFaceDarts L (lYSpine L r x)).length from by omega, Nat.mod_self,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos (lYSpine L r x)]
    rw [show (findFaceDarts L (lYSpine L r x)).head!
        = (findFaceDarts L (lYSpine L r x)).getD 0 default from by
      rw [← List.drop_zero (l := findFaceDarts L (lYSpine L r x))]
      exact aq8w3u_head!_drop_getD _ 0]
    rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos default]

  · exact aq8w3v_betwnFaceHead L hL hgn hm hf hfarne hd0

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3w_betwnFaceHead

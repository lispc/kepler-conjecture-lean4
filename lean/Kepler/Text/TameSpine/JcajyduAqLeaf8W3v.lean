/-
  JcajyduAqLeaf8W3v — AQ8 波 3v：junction ⑤ 主件（三支闭合）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① aq8w3v_betwnFaceHead  面表非空开弧的首元 = `y` 的面后继：
  │    `(between f y z).head! = nextEl f y`（= `fList L y`）
  │    三支：drop 支 / wrap-drop 支 / y 为末元的 wrap-take 支
  └────────────────────────────────────────────────────────────────

  ┌─ 折算与载体 ───────────────────────────────────────────────────
  │ `betwnTakeDrop`（TameList3:986）两支；`aq8w3u_head!_take_pos` /
  │ `aq8w3u_head!_drop_getD`（W3u，本版无公开件）；`nextEl_eq_getD`
  │ （TameLp:4797，`getD ((idx+1) % len)` 形）；`List.head!_append`、
  │ `List.drop_eq_nil_iff`、`List.length_take`、`List.take_zero`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3v_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3u

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

/-- **junction ⑤ 主件**：`f = findFaceDarts L (l'y)`、`between f y z ≠ []` 时
`(between f y z).head! = fList L y`（`fList` 定义 = `nextEl f`）。

三支：`betwnTakeDrop` 的 drop 支（`idx y < idx z`）/ wrap-drop 支（`idx z < idx y`
且 `y` 非末元）/ wrap-take 支（`y` 为末元，`nextEl` 走 `getD 0 = head!`）。 -/
theorem aq8w3v_betwnFaceHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hfarne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) ≠ [])
    (hd0 : (findFaceDarts L (lYSpine L r x)).drop
      ((findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1) ≠ []) :
    (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).head! = fList L (lYSpine L r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hy : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr (memYtransListOfDarts L hL hgn hm hf)
  have hz : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  have hfl : fList L (lYSpine L r x)
      = nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) := rfl
  rw [hfl, betwnTakeDrop hfnd hz]
  split
  · -- 支 1：drop 支
    rename_i hlt
    have hlen : (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)
        < (findFaceDarts L (lYSpine L r x)).length := List.idxOf_lt_length_iff.mpr hz
    have htake_ne : ((findFaceDarts L (lYSpine L r x)).drop
        ((findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1)).take
        ((findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)
          - ((findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1)) ≠ [] := by
      intro h0
      apply hfarne
      rw [betwnTakeDrop hfnd hz, if_pos hlt, h0]
    have hm0 : 0 < (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)
        - ((findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1) := by
      have hpos := List.length_pos_of_ne_nil htake_ne
      rw [List.length_take] at hpos
      omega
    have hk : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1
        < (findFaceDarts L (lYSpine L r x)).length := by omega
    rw [aq8w3u_head!_take_pos _ hm0, aq8w3u_head!_drop_getD,
      Kepler.Text.TameLp.nextEl_eq_getD hy, Nat.mod_eq_of_lt hk,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hk default,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hk (lYSpine L r x)]
  · -- 支 2：wrap（`¬ idx y < idx z`）；`hd0`（y 非末元）⇒ drop 非空 ⇒ 直接取 drop 首元
    have hlen : (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x)
        < (findFaceDarts L (lYSpine L r x)).length := List.idxOf_lt_length_iff.mpr hz
    have hk : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1
        < (findFaceDarts L (lYSpine L r x)).length := by
      have h1 : ¬ (findFaceDarts L (lYSpine L r x)).length
          ≤ (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) + 1 := by
        intro hle
        exact hd0 (List.drop_eq_nil_iff.mpr hle)
      omega
    rw [List.head!_append _ hd0, aq8w3u_head!_drop_getD,
      Kepler.Text.TameLp.nextEl_eq_getD hy, Nat.mod_eq_of_lt hk,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hk default,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hk (lYSpine L r x)]

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3v_betwnFaceHead

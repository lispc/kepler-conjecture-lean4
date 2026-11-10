/-
  Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2 — W2-件2 Wave B2（部分）：
  `loopFaceAgree` —— NCVIBWU-spine i=0 后半的唯一新几何件。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ Ncvibwu.hl:425/:1132 `NCVIBWU2`/`NCVIBWU3`（i=0 剪枝）后半的几何内核。
  │ HOL 用 ~1000 行案析证明「face 轨道 w..z 段 ∈ rtrans 且 indexf 精确」；
  │ 其几何实质 = **split condition 的 loop-face 一致**（Hypermap.exists_hyp_m
  │ 的结论）在具体载体上的折叠。本件把该内核抽为独立公开件：
  │   i ≤ l'm+1 ⇒ (next_el r)^i x = (next_el (find_face L x))^i x。
  │ 后续 Wave C（newvertexPreppedTransformSpine）与 NCVIBWU 后半消费。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（比 HOL 案析短 ~10 倍）────────────────────────────────────
  │ hypM_spec（Hypermap:9958：IsSplitCondition ⇒ loop.map^ = faceMap^ 于
  │ hypM+1 步内）+ hypMLm（TameList12:408：hypM = l'm）+ 两条幂桥：
  │   loop 侧 ((loopOfListSpine r).map)^i x = (nextEl r)^i x
  │     [loopMapNextEl（TameList6:348 公开）逐次归纳，私件同证重推导]
  │   face 侧 (faceMap)^i x = (fList)^i x [faceMapListPower（TameList13:187 公开）]
  │   再 (fList)^i = (nextEl f)^i [fListPowEqNextElPow（ZIndexf）]。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入（/tmp 岛编）；
  │ 既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl nextEl_mem_of_mem dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace)
open Kepler.Text

/-- loop 幂桥（TameList12 私件同证重推导）：
`((loopOfListSpine r).map)^i d = (nextEl r)^[i] d`。 -/
private theorem loopMapNextElIterB2 {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ [])
    (d : ℕ × ℕ) (i : ℕ) :
    ((loopOfListSpine r).map ^ i) d = (nextEl r)^[i] d := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, loopMapNextEl hn hne,
      Function.iterate_succ_apply']

/-- **NCVIBWU 后半几何内核（spine）**：split condition 的 loop-face 一致，
在具体载体上：`i ≤ l'm+1 ⇒ (next_el r)^i x = (next_el (find_face L x))^i x`。 -/
theorem loopFaceAgree (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ i ≤ lMSpine L r x + 1,
      (nextEl r)^[i] x = (nextEl (findFaceDarts L x))^[i] x := by
  have hsc : splitConditionListSpine hL N r x := markListSplitConditionList L hL hm.1 hf
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hMLm := hypMLm L hL hgn hunL hnext hsc
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hrne : r ≠ [] := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).2
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  intro i hi
  have hspec := ((Kepler.Text.TameLp.hypermapOfList L hL).hypM_spec hsplit).1
  have h1 : ((loopOfListSpine r).map ^ i) x
      = ((Kepler.Text.TameLp.hypermapOfList L hL).faceMap ^ i) x :=
    hspec i (by rw [hMLm]; exact hi)
  calc (nextEl r)^[i] x = ((loopOfListSpine r).map ^ i) x :=
        (loopMapNextElIterB2 hrnd hrne x i).symm
    _ = ((Kepler.Text.TameLp.hypermapOfList L hL).faceMap ^ i) x := h1
    _ = (fList L)^[i] x := faceMapListPower L hL i hxd
    _ = (nextEl (findFaceDarts L x))^[i] x := fListPowEqNextElPow L hL x hxx i

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.loopFaceAgree

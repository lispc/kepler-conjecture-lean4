/-
  JcajyduAqLeaf10D — AQ10-b 首批：`aq10` 主证的**分解件**（非主证）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ aq10_rtransOneEqSplit  rtrans(1) = ([z]++betwn r z y++[y]) ++ betwn f y z
  │ aq10_PLast             ([z]++betwn r z y++[y]).getLast! = y
  │ 主证 `aq10` 不在本批（AQ10-b 后段；见 DELIVERY 边界表）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ────────────────────────────────────────────────────
  │ P = [l'z] ++ betwn r l'z l'y ++ [l'y]（Lean ++ 左结合，与
  │ split_normal_list 的 f2 定义形逐字一致）；S = betwn f l'y l'z
  │ （f = find_face L x，经 mem_find_face_imp_faces_eq 对齐）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.JcajyduAqLeaf10C
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.TameList9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl fList findFaceDarts listOfDarts GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- 非终态 `rtrans L N r x 1` 的显式分解：
`([z] ++ betwn r z y ++ [y]) ++ betwn f y z`（z=l'z, y=l'y, f=find_face L x）。 -/
theorem aq10_rtransOneEqSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    rtransSpine L N r x 1
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
          [lYSpine L r x]) ++
        between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hprev : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    Kepler.Text.TameLp.nextEl_prevEl hnd hz
  have hfaceEq : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 ((pplhuljV0 L hL hgn hunL hm hf).1)
  show (Kepler.Text.TameSpine.transformListSpine L x (N, r)).2 = _
  rw [Kepler.Text.TameSpine.transformListSpine]
  rw [if_neg hf]
  unfold Kepler.Text.TameSpine.splitNormalListSpine
  dsimp only
  rw [hprev, hfaceEq]

/-- `P = [z] ++ betwn r z y ++ [y]` 的末元为 `y`。 -/
theorem aq10_PLast {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    (r : List α) (z y : α) :
    ([z] ++ between r z y ++ [y] : List α).getLast! = y := by
  rw [List.getLast!_eq_getLast?_getD]
  rw [List.getLast?_append_of_ne_nil _ (by simp : (([y] : List α)) ≠ [])]
  simp

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq10_rtransOneEqSplit
#print axioms Kepler.Text.TameSpine.aq10_PLast

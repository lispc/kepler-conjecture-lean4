/-
  Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2e — W2-件2 Wave B2e：
  hnest 填充 + OHCGKFU-spine i=0 成员性装配。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ OHCGKFU.hl:162 `OHCGKFU`（i=0 剪枝）的成员性面：
  │ ① `hnestFill`：显式槽 `hnest`（B2d §4，ERRATA 后形）填充——
  │    face 段 sList = `(fList)^[1..lM] x`（不含终点 y）⊆ **r-弧** l'z→l'y；
  │    证 = `aqs_sListInBetwn`（JcajyduAqLeaf12U = HOL AQ12
  │    `s_list_in_betwn`，:3086）+ §0 轨道枚举桥
  │    `(nextEl f)^[k] x = (fList)^[k] x`（fListPowEqNextElPow）；
  │ ② `ohcgkfuSpineV0`：spine-i0 成员性——`j ≤ indexf w l'z f` 的 face 轨道
  │    点 ∈ r' = rtransSpine 1。三段拼装：
  │      j < lM      → hnestFill（r-弧）+ rtransCat（r' = [z]++弧++[y]++F段）
  │      j = lM      → d = l'y，rtransCat 的 [y] 段直投
  │      j > lM      → B1 `ncvibwuSpineV0FPart`（F-弧半件）
  │    （lM = indexf w l'y f 由 `indexfYtransEqLm` 锚定）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ─────────────────────────────────────────────────────
  │ ① `ohcgkfuSpineV0` 只装**成员性**半（Wave C 消费面；B1 §3 判定
  │    index 等式半非 Wave C 所需，留 QCDVKEA 原形补）；
  │ ② hnest 容器 = r-弧（非 r'-弧）：r' 侧成员性经 rtransCat 直投，
  │    无需把 r' 写进槽（B2d 落地形的 ERRATA 见该条 DEF 注释）；
  │ ③ j = lM 位（= l'y 自身）不入 betwn（端点排除），由 rtransCat 的
  │    [l'y] 段供——这是 B2d 槽形修正的机器根据。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰
  │ （B2d 的 hnest ERRATA 修正随本 patch，见 DELIVERY_2B2e §2）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2d
import Kepler.Text.TameSpine.JcajyduAqLeaf12U

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face findFaceDarts_nodup
  nextEl_mem_of_mem)

/-! ## §1 hnest 填充（三要素之「填法」落机器） -/

/-- **hnest 填充**：face 段 `(nextEl f)^[1..lM] x` 整段落在 r-弧
`l'z → l'y` 内（槽名 `hnest`；目标定理 `ohcgkfuSpineV0`）。

证：sList 定义即 `(fList)^[1..lM] x`（TameList13:198），轨道枚举桥
`fListPowEqNextElPow` 换成 nextEl 幂；`aqs_sListInBetwn`（AQ12
`s_list_in_betwn`）直给 r-弧成员性。 -/
theorem hnestFill (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    hnest L N r x := by
  intro j hj
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hjd : (nextEl (findFaceDarts L x))^[j + 1] x ∈ sListSpine L r x := by
    rw [← fListPowEqNextElPow L hL x hxx (j + 1)]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  exact aqs_sListInBetwn L hL hgn hm hf rfl rfl rfl hjd

/-! ## §2 OHCGKFU-spine i=0 成员性装配 -/

/-- **OHCGKFU-spine（i=0）成员性**：`j ≤ indexf w l'z f`
⇒ face 轨道第 j 步 ∈ r'（spine-i0 成员性 = 头段 ∪ F-弧）。

三案（见文件头）：j < lM（hnestFill + rtransCat）、j = lM（l'y ∈ [y] 段）、
j > lM（B1 `ncvibwuSpineV0FPart`）。 -/
theorem ohcgkfuSpineV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {j : ℕ}
    (hj : j ≤ indexf w (lZSpine L N r x) f) :
    (nextEl f)^[j] w ∈ rtransSpine L N r x 1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hMLm : indexf w (lYSpine L r x) f = lMSpine L r x := by
    have h := indexfYtransEqLm L hL hgn hunL hm hf
    rwa [hfind, hw] at h
  have hyW : (nextEl f)^[indexf w (lYSpine L r x) f] w = lYSpine L r x := by
    have h := dLMeqY L hL hgn hunL hm hf
    rwa [hfind, hw] at h
  by_cases hjY : j ≤ indexf w (lYSpine L r x) f
  · have hjlM : j ≤ lMSpine L r x := by rw [← hMLm]; exact hjY
    rcases Nat.lt_or_eq_of_le hjlM with hlt | heq
    · -- j < lM：头段（sList ⊆ r-弧 ⊆ r'）
      have hb := hnestFill L hL hgn hm hf j hlt
      have hdw : (nextEl f)^[j] w = (nextEl (findFaceDarts L x))^[j + 1] x := by
        rw [← hw, ← Function.iterate_succ_apply, hfind]
      rw [hdw, rtransCat L N r x hf hrnd]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb))
    · -- j = lM：d = l'y（rtransCat 的 [y] 段）
      have hdw : (nextEl f)^[j] w = lYSpine L r x := by
        rw [heq, ← hMLm]
        exact hyW
      rw [hdw, rtransCat L N r x hf hrnd]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  · -- j > lM：F-弧半件（B1 直投）
    have hjY' : indexf w (lYSpine L r x) f < j := Nat.lt_of_not_le hjY
    have hF := ncvibwuSpineV0FPart L hL hgn hm hf (j := j) ?_ ?_
    · simpa only [hfind, hw] using hF
    · show indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x)
        (findFaceDarts L x) < j
      rw [hfind, hw]
      exact hjY'
    · show j ≤ indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x)
        (findFaceDarts L x)
      rw [hfind, hw]
      exact hj

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.hnestFill
#print axioms Kepler.Text.TameSpine.ohcgkfuSpineV0

/-
  Kepler.Text.PwssratFace — 铺装 patch7：PPLHULJ_v0 面（0a + 0b）

  PLAN-P7 裁决 (b)：`ly/lz ∈ find_face L x`（0a）+ `pplhulj3V0` 链侧（0b）——
  T1（r_trans_eq）/T2（core_split）/OHCGKFU 三件的共同上游。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ HOJODCM.hl:359  `PPLHULJ_v0`（三合取） → pplhuljV0（本批总装）
  │   ├ ① `l'y L r x ∈ find_face L x`        → lyMemFindFaceDarts（0a）
  │   ├ ② `l'z L N r x ∈ find_face L x`      → lzMemFindFaceDacts（0a）
  │   └ ③ `indexf w (l'y) f < indexf w (l'z) f` → pplhulj3V0（0b）
  │ pplhulj.hl      `indexf_ytrans_eq_l_m`（面指数形）
  │   → indexfYtransEqLm（0b 引擎；QCDVKEA 消费面，scout 落簇后直供）
  │ PWSSRAT.hl:502  `f_list_power_next_el`   → fListPowEqNextElPow（0b 引擎）
  │ （Spine 侧同名件：JcajyduAqZIndexf.pplhuljV0/pplhulj3V0/indexfYtransEqLm、
  │   Leaf8W3.fListPowEqNextElPow——链层载体独立，双家记账沿 parts_cat 先例。）
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与路线（链层，零直接 TameSpine import）──────────────────
  │ ① 0a 两件走 fList 轨道保面：`ly = (fList)^(l'm+1) x`（def 直取）+
  │    `memFListPower`（MoreLemma2a23）+ `memFindFaceImpFacesEq`（面折叠）。
  │    **前提比 HOL 弱**：HOL PPLHULJ_v0 整体携带 `~final_list`，本两件
  │    只需 `markedList`（DIFFERS 记档：加强形，消费侧恒可实例化）。
  │ ② 0b 主件走 patch5 `hqymrtx1List` 第二合取（`l'z ≠ f^k x`，k ∈ [1,l'm+1]）
  │    + `indexfN` 定位（`l'z = f^(i+1) x`，i = indexf w l'z f）⇒ `l'm < i`；
  │    面指数引擎 `indexfYtransEqLm`（= l'm）+ `hypM_lt_face`（Hypermap 公开）+
  │    `cardFaceOfList`（TameCorrCard）+ `hypMLmChain`/`isSplitConditionOfMarkedList`
  │    （ChainMarkedTranslate 公开）供界 `l'm < |find_face L x|`。
  │ ③ 实例纪律：`Dart` 双 BEq 世界同 patch4/6——BEq 世界的
  │    `TameSpine.indexfN/nextElnIndexf` 经公开桥 `Reduction3.indexf_eq_spine`
  │    （propext）折回 `Reduction5.indexf`；轨道成员性本地归纳，不复制引擎。
  │ ④ `hs` 槽：`hqymrtx1List` 的 hs 由 `sListEqOfMarked`（本批 private→public，
  │    PwssratMemberBase 陈述零改动）现产。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；零直接 TameSpine import；
  不改既有陈述；主仓 tracked 仅 PwssratMemberBase 可见性一字改 + 本新文件。
-/

import Kepler.Text.PwssratMemberBase
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.TameCorrCard
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart lz ztrans rtrans finalList indexf)

/-! ## §0 引擎：`f_list` 幂 = 自面 `next_el` 幂（PWSSRAT:502 链侧自证） -/

/-- **HOL `Pwssrat.f_list_power_next_el`**（PWSSRAT.hl:502）：
`y ∈ find_face L y ⇒ (f_list L)^m y = ((next_el (find_face L y))^m) y`。
面轨道保面（`findFace_fList` 的幂版）：每步基点的面沿轨道不变。 -/
theorem fListPowEqNextElPow (L : fgraph ℕ) (hL : GoodList L) {y : Dart}
    (hy : y ∈ findFaceDarts L y) (m : ℕ) :
    (fList L)^[m] y = (nextEl (findFaceDarts L y))^[m] y := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have hyD : y ∈ listOfDarts L := Kepler.Text.TameLp.mem_darts_of_mem_findFace L hy
    have hzmem : (nextEl (findFaceDarts L y))^[k] y ∈ findFaceDarts L y := by
      rw [← ih]
      exact Kepler.Text.MoreLemma2a23.memFListPower L hL.1 hy k
    have hcongr : findFaceDarts L ((nextEl (findFaceDarts L y))^[k] y)
        = findFaceDarts L y :=
      Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hyD hzmem
    have hstep : fList L ((nextEl (findFaceDarts L y))^[k] y)
        = nextEl (findFaceDarts L y) ((nextEl (findFaceDarts L y))^[k] y) := by
      show nextEl (findFaceDarts L ((nextEl (findFaceDarts L y))^[k] y))
          ((nextEl (findFaceDarts L y))^[k] y) = _
      rw [hcongr]
    rw [hstep]

/-! ## §1 0a：`l'y`/`l'z` 的面成员性（PPLHULJ_v0 前两合取） -/

/-- **PPLHULJ_v0 第 ① 合取（链侧）**：`l'y L r x ∈ find_face L x`。
证体：`l'y = (f_list)^(l'm+1) x`（def 直取）+ `memFListPower` 轨道保面。
前提仅需 `markedList`（HOL 整体携带的 `~final_list` 在此不需要——加强形）。 -/
theorem lyMemFindFaceDarts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x := by
  have hxd : x ∈ listOfDarts L :=
    Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  show (fList L)^[Kepler.Text.Reduction5.lm L r x + 1] x ∈ findFaceDarts L x
  exact Kepler.Text.MoreLemma2a23.memFListPower L hL.1 hxx _

/-- **PPLHULJ_v0 第 ② 合取（链侧）**：`l'z L N r x ∈ find_face L x`。
证体：`l'z = (f_list)^(l'p+1) (l'y)`（def 直取）+ ① 的面折叠。 -/
theorem lzMemFindFaceDarts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    lz L N r x ∈ findFaceDarts L x := by
  have hy : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x :=
    lyMemFindFaceDarts L hL hm
  have hyD : Kepler.Text.Reduction5.ly L r x ∈ listOfDarts L :=
    Kepler.Text.TameLp.mem_darts_of_mem_findFace L hy
  have hyy : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L
      (Kepler.Text.Reduction5.ly L r x) :=
    (Kepler.Text.TameLp.dart_in_face L _).mpr hyD
  have hcongr : findFaceDarts L (Kepler.Text.Reduction5.ly L r x)
      = findFaceDarts L x := Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hy
  show (fList L)^[Kepler.Text.Reduction5.lp L N r x + 1]
      (Kepler.Text.Reduction5.ly L r x) ∈ findFaceDarts L x
  have h := Kepler.Text.MoreLemma2a23.memFListPower L hL.1 hyy
    (Kepler.Text.Reduction5.lp L N r x + 1)
  rwa [hcongr] at h

/-- 消费辅件：`find_face (l'y L r x) = find_face L x`（faces_eq 桥）。 -/
theorem lyFindFaceEq (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x :=
  Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 (lyMemFindFaceDarts L hL hm)

/-! ## §2 0b 引擎一：界 `l'm < |find_face L x|` 与面指数 `indexf w l'y f = l'm` -/

/-- `l'm L r x < sizel (find_face L x)`（ZIndexf `aq10_lmLtFaceLen` 链侧同证）：
`hypM_lt_face`（Hypermap 公开；IsSplitCondition 由 ChainMarkedTranslate 公开件供）
+ `hypMLmChain`（hypM = l'm）+ `cardFaceOfList`（ncard = 面表长）。 -/
private theorem lmLtFaceLen (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    Kepler.Text.Reduction5.lm L r x < (findFaceDarts L x).length := by
  have hxd : x ∈ listOfDarts L :=
    Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hsplit := Kepler.Text.ChainMarkedTranslate.isSplitConditionOfMarkedList
    L hL hgn hunL hm hf
  have hlt := (Kepler.Text.TameLp.hypermapOfList L hL).hypM_lt_face hsplit
  rw [Kepler.Text.ChainMarkedTranslate.hypMLmChain L hL hgn hunL hm hf] at hlt
  rw [Kepler.Text.TameCorrCard.cardFaceOfList hL hxd] at hlt
  omega

/-- **HOL `Pplhulj.indexf_ytrans_eq_l_m`**（面指数形）：
`indexf w (l'y) (find_face L x) = l'm`（`w = next_el (find_face L x) x`）。
证体：`l'y = (next_el f)^(l'm) w`（`fListPowEqNextElPow` 换基）+
`nextElnIndexf`（步数 ↔ indexf）+ `lmLtFaceLen` 界。 -/
theorem indexfYtransEqLm (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x)
        (findFaceDarts L x)
      = Kepler.Text.Reduction5.lm L r x := by
  have hxd : x ∈ listOfDarts L :=
    Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hfnd : (findFaceDarts L x).Nodup :=
    Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    Kepler.Text.TameLp.nextEl_mem_of_mem hxx
  have hyx : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x :=
    lyMemFindFaceDarts L hL hm
  have hwD : nextEl (findFaceDarts L x) x ∈ listOfDarts L :=
    Kepler.Text.TameLp.mem_darts_of_mem_findFace L hwf
  have hww : nextEl (findFaceDarts L x) x ∈ findFaceDarts L
      (nextEl (findFaceDarts L x) x) := (Kepler.Text.TameLp.dart_in_face L _).mpr hwD
  have hcW : findFaceDarts L (nextEl (findFaceDarts L x) x)
      = findFaceDarts L x := Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hwf
  have hyW : Kepler.Text.Reduction5.ly L r x
      = (nextEl (findFaceDarts L x))^[Kepler.Text.Reduction5.lm L r x]
          (nextEl (findFaceDarts L x) x) := by
    show (fList L)^[Kepler.Text.Reduction5.lm L r x + 1] x = _
    rw [Function.iterate_succ_apply,
      show fList L x = nextEl (findFaceDarts L x) x from rfl,
      fListPowEqNextElPow L hL hww (Kepler.Text.Reduction5.lm L r x), hcW]
  have h := Kepler.Text.TameSpine.nextElnIndexf hwf hyx hfnd hyW.symm
    (lmLtFaceLen L hL hgn hunL hm hf)
  rw [← Kepler.Text.Reduction3.indexf_eq_spine
    (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x)
      (findFaceDarts L x)] at h
  exact h

/-! ## §3 0b 主件：`indexf w (l'y) f < indexf w (l'z) f`（pplhulj3V0） -/

/-- **HOL `pplhulj3V0`**（PPLHULJ_v0 第 ③ 合取；AQ7/ZIndexf 链侧同证）：
`indexf w (l'y) f < indexf w (l'z) f`（`w = next_el (find_face L x) x`）。
证体（ZIndexf:261-:355 同构）：`indexfN` 定位 `l'z = f^(i+1) x`
（`i = indexf w l'z f`）→ patch5 `hqymrtx1List` 第二合取排除 `i+1 ≤ l'm+1`
⇒ `l'm < i`；左端 `indexfYtransEqLm` 折成 `l'm`。 -/
theorem pplhulj3V0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x)
        (findFaceDarts L x)
      < indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x) := by
  have hxd : x ∈ listOfDarts L :=
    Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hfnd : (findFaceDarts L x).Nodup :=
    Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    Kepler.Text.TameLp.nextEl_mem_of_mem hxx
  have hzf : lz L N r x ∈ findFaceDarts L x := lzMemFindFaceDarts L hL hm
  -- i := indexf w l'z f 的轨道定位：l'z = (next_el f)^i w
  have hzi : (nextEl (findFaceDarts L x))^[
      indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x)]
      (nextEl (findFaceDarts L x) x) = lz L N r x := by
    have h := Kepler.Text.TameSpine.indexfN hwf hzf hfnd
    rw [← Kepler.Text.Reduction3.indexf_eq_spine
      (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x)] at h
    exact h
  -- l'z = (f_list)^(i+1) x（fListPowEqNextElPow 换基 + w = f_list x）
  have hwD : nextEl (findFaceDarts L x) x ∈ listOfDarts L :=
    Kepler.Text.TameLp.mem_darts_of_mem_findFace L hwf
  have hww : nextEl (findFaceDarts L x) x ∈ findFaceDarts L
      (nextEl (findFaceDarts L x) x) := (Kepler.Text.TameLp.dart_in_face L _).mpr hwD
  have hcW : findFaceDarts L (nextEl (findFaceDarts L x) x)
      = findFaceDarts L x := Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hwf
  have hzF : lz L N r x
      = (fList L)^[
          indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x)
            + 1] x := by
    have hwp : (fList L)^[
        indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x)]
        (nextEl (findFaceDarts L x) x)
        = (nextEl (findFaceDarts L x))^[
            indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
              (findFaceDarts L x)] (nextEl (findFaceDarts L x) x) := by
      rw [fListPowEqNextElPow L hL hww _, hcW]
    calc lz L N r x
        = (nextEl (findFaceDarts L x))^[
            indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
              (findFaceDarts L x)] (nextEl (findFaceDarts L x) x) := hzi.symm
      _ = (fList L)^[
            indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
              (findFaceDarts L x)] (nextEl (findFaceDarts L x) x) := hwp.symm
      _ = (fList L)^[
            indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
              (findFaceDarts L x)] (fList L x) := rfl
      _ = (fList L)^[
            indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
              (findFaceDarts L x) + 1] x :=
            (Function.iterate_succ_apply (fList L) _ x).symm
  -- patch5 排除：l'z ≠ f^k x（k ∈ [1, l'm+1]）⇒ l'm < i
  have hexcl : ∀ k : ℕ, 1 ≤ k → k ≤ Kepler.Text.Reduction5.lm L r x + 1 →
      lz L N r x ≠ (fList L)^[k] x :=
    (hqymrtx1List L hL hgn hunL hm hf (sListEqOfMarked L hL hm hf)).2
  have hgt : Kepler.Text.Reduction5.lm L r x
      < indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x) := by
    rcases Nat.lt_or_ge
        (indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x))
        (Kepler.Text.Reduction5.lm L r x + 1) with h | h
    · exact (hexcl
        (indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
          (findFaceDarts L x) + 1) (by omega) (by omega) hzF).elim
    · omega
  rw [indexfYtransEqLm L hL hgn hunL hm hf]
  exact hgt

/-! ## §4 总装：`PPLHULJ_v0` 三合取（HOJODCM.hl:359 链层形） -/

/-- **HOL `PPLHULJ_v0`**（HOJODCM.hl:359）链层三合取：
`l'y ∈ f ∧ l'z ∈ f ∧ indexf w l'y f < indexf w l'z f`。 -/
theorem pplhuljV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x ∧
      lz L N r x ∈ findFaceDarts L x ∧
      indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x)
          (findFaceDarts L x)
        < indexf (nextEl (findFaceDarts L x) x) (lz L N r x)
            (findFaceDarts L x) :=
  ⟨lyMemFindFaceDarts L hL hm, lzMemFindFaceDarts L hL hm,
    pplhulj3V0 L hL hgn hunL hm hf⟩

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.fListPowEqNextElPow
#print axioms Kepler.Text.Reduction4Idx.lyMemFindFaceDarts
#print axioms Kepler.Text.Reduction4Idx.lzMemFindFaceDarts
#print axioms Kepler.Text.Reduction4Idx.indexfYtransEqLm
#print axioms Kepler.Text.Reduction4Idx.pplhulj3V0
#print axioms Kepler.Text.Reduction4Idx.pplhuljV0

/-
  Kepler.Text.Reduction5J5BetwnNil — J5-1 余量段（chain 载体）第一文件：
  `bet_eq_nil_imp_next_y_z`（reduction4.hl:4897）与两 mem 小件
  `mem_y_rtrans1`（:5035）/ `mem_ytrans_rtrans_suc`（:5053），
  另附 reduction2.hl:443 `find_face_x_eq_y` 的链层形（两主件消费面）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ reduction2.hl:443 `find_face_x_eq_y` → `findFaceXEqY`：
  │   good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list
  │   ⇒ find_face L (l'y L r x) = find_face L x
  │ reduction4.hl:5035 `mem_y_rtrans1`（18L）→ `memYRtrans1`：
  │   good_list ∧ good_list_nodes ∧ ¬final_list L r ∧ marked_list L N r x
  │   ⇒ MEM (ytrans L N r x 0) (rtrans L N r x 1)
  │ reduction4.hl:5053 `mem_ytrans_rtrans_suc`（22L）→ `memYtransRtransSuc`：
  │   同上 ∧ i < transform_count ⇒ MEM (ytrans … i) (rtrans … (SUC i))
  │ reduction4.hl:4897 `bet_eq_nil_imp_next_y_z`（73L）→ `betEqNilImpNextYZ`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final_list ∧
  │   transform_count = k ∧ i < k ∧ betwn (find_face L x) (ytrans … i) (ztrans … i) = []
  │   ⇒ next_el (rtrans … (SUC i)) (ytrans … i) = ztrans … i
  └────────────────────────────────────────────────────────────────

  ┌─ 证体路线（与 HOL 逐步对照；纯 chain，不经 spine）────────────────
  │ · findFaceXEqY：`ytranMeF`（MoreLemma2a23:119）+ `memFindFaceImpFacesEq`
  │   （BetwnBase:554）＝ HOL 的 marked_lemma_yz_in_face 支路。
  │ · memYRtrans1：`rtrans1`（Reduction3Thm1:119，非 final 一步展开）后
  │   split.2 = [ram2'] ++ (betwn r ram2' ram1 ++ [ram1]) ++ new2，ram1 = ly
  │   即 ytrans 0，成员平凡（HOL 经 Aq12.y_mem_split_snd；展开即达，免支件）。
  │ · memYtransRtransSuc：trans_add（Reduction3Thm1:106）+ memYRtrans1 于
  │   (ntrans i, rtrans i)；`transformCount_not`（Reduction4:701）供非 final；
  │   AQIUNPP 以 `AqiunppSlot` 槽供给（树内既定惯例）。
  │ · betEqNilImpNextYZ：trans_add 把 SUC i 折到状态 i 的一步；rtrans1 展开
  │   split.2；`nextPrevId`（BetwnBase:498）把 ram2' 折回 z；betwn = [] 前提
  │   消掉 new2 ⇒ rtrans (SUC i) = [z] ++ (betwn r z y ++ [y])，HD = z、
  │   LAST = y；`nextElLastHd`（MoreLemma2Naming:99）收口。跨实例
  │   `nextElInstEq`（Reduction5Kbwpbhq:86）桥 R1 双 BEq 实例（雷区⑪同款）。
  └────────────────────────────────────────────────────────────────

  ┌─ 语义查重记档（工单要求：别只按名）───────────────────────────────
  │ 两 mem 小件树内确缺：按名（memYRtrans1/memYtransRtransSuc/y_rtrans1
  │ 族）零命中；按结论形「ytrans i ∈ rtrans (i+1)」「ytrans 0 ∈ rtrans 1」
  │ 检索 chain 与 spine 两世界均无同陈述件。最近邻为异态件：
  │ `ytransMemRtrans`（MoreLemma2Naming:221，ytrans 0 ∈ r）、
  │ `PwssratMemberBase.ytransMemRtrans`（ytrans i ∈ rtrans i）、spine
  │ `aqs_yMemSplitSnd`（split 级 y ∈ SND）。均非本件。
  │ `find_face_x_eq_y` 按名零命中（j51b 冻结表「◐ 替位 congr」为逐点内联，
  │ 无公开陈述件）；本笔落公开形。
  └────────────────────────────────────────────────────────────────

  前提位：照 HOL 原文逐字（顺序同原文；is_restricted 以显式入参保留，
  与 Reduction4Subseg9.finalAssumptionMemXCore 同款）。good_list ↦ hL、
  good_list_nodes ↦ hgn 为树内既定载体折算（DIFFERS-①）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5CoreNextF
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.Reduction3Thm1
import Kepler.Text.Reduction4
import Kepler.Text.MoreLemma2a23
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction4Subseg9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList markedList)

/-- **HOL `find_face_x_eq_y`**（reduction2.hl:443）：y = l'y 与 x 同面。 -/
theorem findFaceXEqY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x := by
  have hy : ytrans L N r x 0 ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl 0
  exact memFindFaceImpFacesEq hL.1 hy

/-- **HOL `mem_y_rtrans1`**（reduction4.hl:5035）：ytrans 0 落 rtrans 1。 -/
theorem memYRtrans1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hnf : ¬ finalList L r) (hm : markedList L hL N r x) :
    ytrans L N r x 0 ∈ rtrans L N r x 1 := by
  rw [Kepler.Text.Reduction3.rtrans1 L N r x hnf]
  show Kepler.Text.Reduction5.ly L r x ∈
    (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2
  simp [splitNormalList]

/-- **HOL `mem_ytrans_rtrans_suc`**（reduction4.hl:5053）：ytrans i 落
rtrans (SUC i)。 -/
theorem memYtransRtransSuc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hnf : ¬ finalList L r) (hm : markedList L hL N r x)
    (hi : i < transformCount L N r x) :
    ytrans L N r x i ∈ rtrans L N r x (i + 1) := by
  have hnfi := Kepler.Text.Reduction4.transformCount_not i hi
  have hmI := haq hgn N r x hm i
  have h := memYRtrans1 L hL hgn hnfi hmI
  rw [← (Kepler.Text.Reduction3.transAdd L N r x i 1).2.1,
    ← (Kepler.Text.Reduction3.transAdd L N r x i 0).2.2.1] at h
  rw [Nat.add_comm 1 i, Nat.zero_add] at h
  exact h

/-- 非最终态、同面 betwn 空 ⇒ 一步变换环的显式结构：
`rtrans (SUC i) = [ztrans i] ++ (betwn (rtrans i) (ztrans i) (ytrans i) ++ [ytrans i])`
（betEqNilImpNextYZ 的私有支件；HOL 证体 :4936-:4958 的结构步）。 -/
private theorem rtransSucStruct (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : markedList L hL N r x)
    (hnfi : ¬ finalList L (rtrans L N r x i))
    (hbet : between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = []) :
    rtrans L N r x (i + 1) =
      [ztrans L N r x i] ++
        (between (rtrans L N r x i) (ztrans L N r x i) (ytrans L N r x i) ++
          [ytrans L N r x i]) := by
  have hmI : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
  have hrnd : (rtrans L N r x i).Nodup :=
    (List.nodup_flatten.mp hmI.2.1.1).1 _ hmI.2.2.1
  have hstep : rtrans L N r x (i + 1)
      = rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1 := by
    rw [Nat.add_comm]
    exact (Kepler.Text.Reduction3.transAdd L N r x i 1).2.1
  have hface : findFaceDarts L (ytrans L N r x i) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 (Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl i)
  rw [hstep, Kepler.Text.Reduction3.rtrans1 L _ _ x hnfi]
  show (splitNormalList L (rtrans L N r x i) (findFaceDarts L (ytrans L N r x i))
      (ytrans L N r x i) (prevEl (rtrans L N r x i) (ztrans L N r x i))).2 = _
  simp only [splitNormalList]
  rw [nextElInstEq, nextPrevId hrnd, hface, hbet, List.append_nil]

/-- **HOL `bet_eq_nil_imp_next_y_z`**（reduction4.hl:4897）：同面 betwn 空时，
一步后环上的 ytrans i 的后继即 ztrans i。 -/
theorem betEqNilImpNextYZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k i : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) (hik : i < k)
    (hbet : between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = []) :
    nextEl (rtrans L N r x (i + 1)) (ytrans L N r x i) = ztrans L N r x i := by
  have hnfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  have hs := rtransSucStruct L hL hgn haq i hm hnfi hbet
  have hmI1 : markedList L hL (ntrans L N r x (i + 1)) (rtrans L N r x (i + 1)) x :=
    haq hgn N r x hm (i + 1)
  have hsnd : (rtrans L N r x (i + 1)).Nodup :=
    (List.nodup_flatten.mp hmI1.2.1.1).1 _ hmI1.2.2.1
  have hsne : rtrans L N r x (i + 1) ≠ [] := hmI1.2.1.2.1 _ hmI1.2.2.1
  -- HD 与 LAST 的显式化（证体依赖 s 的形状，抽象成引理后回代）
  have key : ∀ (s : List Dart) (hne : s ≠ []) (z y : Dart) (X : List Dart),
      s = [z] ++ (X ++ [y]) → s.getLast hne = y ∧ s.headD z = z := by
    intro s hne z y X hsx
    subst hsx
    simp
  obtain ⟨hlast, hhd⟩ := key _ hsne _ _ _ hs
  have h := Kepler.Text.MoreLemma2Naming.nextElLastHd (x := ztrans L N r x i) hsnd hsne
  rw [hlast, hhd] at h
  rw [nextElInstEq]
  exact h

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.findFaceXEqY
#print axioms Kepler.Text.Reduction5.memYRtrans1
#print axioms Kepler.Text.Reduction5.memYtransRtransSuc
#print axioms Kepler.Text.Reduction5.betEqNilImpNextYZ

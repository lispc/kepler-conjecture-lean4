/-
  Kepler.Text.Reduction5J5NotNextCore — J5-1 主线收口段（chain 载体）第二文件：
  两主件 `final_assumptions_not_next_core0_z_y`（reduction4.hl:5217）与
  `final_assumptions_not_next_core_0_i`（:5139）。前者落 HOL 原文形（无槽）；
  后者落**显式槽版**（两条上游未落，槽各对应一条，见下）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ reduction4.hl:5217 `final_assumptions_not_next_core0_z_y`（102L）
  │   → `finalAssumptionsNotNextCore0ZY`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list L N r x ∧
  │   ¬final_list L r ⇒
  │   (betwn (find_face L x) (ytrans … 0) (ztrans … 0) = [] ⇒
  │    ¬(next_el (core L (rtrans … 0)) (FST (ztrans … 0)) = FST (ytrans … 0)))
  │ reduction4.hl:5139 `final_assumptions_not_next_core_0_i`（78L）
  │   → `finalAssumptionsNotNextCore0IOfSlots`（槽版；原文名留给日后的无槽形）：
  │   同前五项 ∧ transform_count L N r x = k ⇒
  │   (∀ i. i < k ∧ betwn (find_face L x) (ytrans … i) (ztrans … i) = [] ⇒
  │    ¬(next_el (core L r) (FST (ytrans … i)) = FST (ztrans … i)))
  │   `∀ i. A ∧ B ⇒ C` 写成柯里化 `∀ i, A → B → C`，与树内
  │   `betwnCoreReductionLemma`（Reduction5:129）及九槽顶层 `hnn0i` 槽同形。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线差异记账（U1 裁决条件 (c)）──────────────────────────────────
  │ **z_y 主件**：HOL 证体 :5279-:5281 取 FST y ≠ FST z 的方式是
  │ `fst_yi_ne_fst_zi [k := transform_count L N r x; i := 0]`，其 `0 < k` 由
  │ `Reduction3.transform_count_non0`（终止定理支）供给。Lean 改走
  │ `QRDYXYJ_list`：直接取 `qrdyxyjFstYNeFstZ` 于状态 0（marked_list 与
  │ ¬final_list 即本件前提）。**没有经 `fstYiNeFstZi` 的 i = 0 实例**——
  │ 那样仍需 `0 < transform_count`，而 `transform_count_non0` 树内只有
  │ hfinal 条件形。其余步骤与 HOL 证体逐步同构。
  │ **0_i 主件**：FST y_i ≠ FST z_i 取自本波 `fstYiNeFstZi`（其路线差异见
  │ Reduction5J5FstNe 头注）。HOL 证体另引 `final_assumption_mem_uniq`（:171）
  │ 的第 6、7 合取：第 7 合取 `MEM (ytrans i) (find_face L x)` = 在库
  │ `ytranMeF`；第 6 合取 `MEM (ytrans i) r` 在 HOL 里来自
  │ `Pnxvwfs.PNXVWFS1` + `transform_count_not`，本件由槽 ① + 在库
  │ `transformCount_not` 现推。:171 整件（11 合取）未移植，也不需要。
  └────────────────────────────────────────────────────────────────

  ┌─ 槽版说明（0_i 主件；编排者续派「以显式槽版落，槽各标明上游与归属」）──
  │ 槽 ① `hpnx1` ↔ HOL `Pnxvwfs.PNXVWFS1`（PNXVWFS.hl:120）：
  │   transform_assumption_v2 L ∧ good_list ∧ good_list_nodes ∧
  │   ¬final_list L (rtrans L N r x i) ∧ marked_list L N r x ⇒ MEM (ytrans L N r x i) r。
  │   槽形 = 该结论在本件 (L, N, r, x) 的实例，对 i 全称，只留本件上下文没有的
  │   那条前提 ¬final_list L (rtrans … i)。
  │   归属：tame-corr（PNXVWFS 港；门控链 nc6 ← `w_betwn`，台账续845 ③）。
  │ 槽 ② `hkb1` ↔ HOL `Kbwpbhq.KBWPBHQ1`（KBWPBHQ.hl:1114）：
  │   transform_assumption_v2 L ∧ good_list ∧ good_list_nodes ∧ marked_list L N r x ∧
  │   MEM u r ∧ MEM u (find_face L x) ⇒
  │   ((∃ i. ytrans L N r x i = u ∧ i < transform_count L N r x) ⇔
  │    ¬(next_el (find_list N u) u = f_list L u))。
  │   槽形 = 该结论在本件 (L, N, r, x) 的实例，对 u 全称，留 MEM u r 与
  │   MEM u (find_face L x) 两条前提。
  │   归属：tame-corr（KBWPBHQ 港，台账续845 ③）。
  │ 两槽里 HOL 的 transform_assumption_v2 前提都不写入：HOL 在消费处用
  │ `transform_assumption_v2_lemma` 当场消掉，它不是消费方的前提。
  │ 两条上游落库后，原文名 `finalAssumptionsNotNextCore0I`（无槽）= 本件代入
  │ 两槽的一行推论；本件不占原文名，免得届时改既有陈述。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5FstNe
import Kepler.Text.Reduction5J5SplitNorm
import Kepler.Text.Reduction4Subseg8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList markedList findList)

/-- **HOL `final_assumptions_not_next_core0_z_y`**（reduction4.hl:5217）：
同面 betwn 空时，core 环上 FST (ztrans 0) 的后继不是 FST (ytrans 0)。 -/
theorem finalAssumptionsNotNextCore0ZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠ (ytrans L N r x 0).1 := by
  intro hbet hcon
  -- l'y / l'z 形（HOL `Reduction2.trans0`；定义级）
  have hcon' : nextEl (core L r) (lz L N r x).1 = (Kepler.Text.Reduction5.ly L r x).1 := hcon
  -- FST y ≠ FST z：`QRDYXYJ_list` 第 5 合取于状态 0（路线差异见文件头）
  have hfst : (Kepler.Text.Reduction5.ly L r x).1 ≠ (lz L N r x).1 :=
    qrdyxyjFstYNeFstZ L hL hgn hm hnf
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hen : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hN : normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hN.1).1 _ hrN
  -- z、z' = prev_el r z 落 r（`mem_ztrans_rtrans_v0` / `mem_prev_el`）
  have hzr : lz L N r x ∈ r := lzMemR hL hgn hunL haq hm hnf
  have hz'r : prevEl r (lz L N r x) ∈ r := memPrevEl hzr
  obtain ⟨p, hp, hz'p⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hz'r
  have hcu : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  -- 状态 1 的 marked_list（AQIUNPP）
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
  have hN1 : normalList L hL (ntrans L N r x 1) := hm1.2.1
  have hface : findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x :=
    findFaceXEqY L hL hgn hm hnf
  -- f1 = FST split
  obtain ⟨f1, hf1⟩ : ∃ f1, (splitNormalList L r (findFaceDarts L x)
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1 = f1 := ⟨_, rfl⟩
  -- `Aq8.fst_mem_rtran1`：f1 ∈ ntrans 1（transform_list 展开即达）
  have hf1mem : f1 ∈ ntrans L N r x 1 := by
    have hnt : ntrans L N r x 1 =
        Kepler.Graphs.replace r
          [(splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
            (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2] N ++
          [(splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
            (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1] := by
      simp [ntrans, transformList, hnf]
    rw [hnt, hface, hf1]
    exact List.mem_append_right _ List.mem_cons_self
  -- `Aq12.prev_z_mem_split_snd`：z' ∈ f1（split 展开即达）
  have hz'f1 : prevEl r (lz L N r x) ∈ f1 := by
    rw [← hf1]
    simp [splitNormalList]
  -- `Aq1.uniq_fst_split_norm`：uniq f1
  have hu1 : f1.Nodup := by
    have h := uniqFstSplitNorm L hL hgn hm hnf
    rw [hface, hf1] at h
    exact h
  obtain ⟨p', hp', hz'p'⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hu1 hz'f1
  -- uniq (core L f1)：状态 1 的 quotient 合取 + quotient_list_core + MEMf_MAP
  have hcu1 : (core L f1).Nodup := by
    have h5 : ∀ s ∈ quotientList L (ntrans L N r x 1), s.Nodup := hm1.2.2.2.2.1.1
    rw [Kepler.Text.MoreLemma2Island1.quotientListCore] at h5
    exact h5 (core L f1) (List.mem_map.mpr ⟨f1, hf1mem, rfl⟩)
  -- `bet_eq_nil_imp_next_z_y`
  have H1 : nextEl f1 (prevEl r (lz L N r x)) = nextEl r (Kepler.Text.Reduction5.ly L r x) :=
    betEqNilImpNextZY L hL hgn hres f1 hm hnf hf1 hbet
  -- `FST_EQ_NEXT_YTRANS_v0` / `FST_EQ_PREV_ZTRANS_v0`
  have hy : (nextEl r (Kepler.Text.Reduction5.ly L r x)).1 = (Kepler.Text.Reduction5.ly L r x).1 :=
    fstEqNextYtransV0 L hL hgn hm hnf rfl
  have hz : (prevEl r (lz L N r x)).1 = (lz L N r x).1 :=
    fstEqPrevZtransV0 L hL hgn hm hnf rfl rfl
  have hne : (prevEl r (lz L N r x)).1 ≠ (nextEl r (Kepler.Text.Reduction5.ly L r x)).1 := by
    rw [hz, hy]
    exact fun h => hfst h.symm
  -- `next_core_ne_FST` 于 (ntrans 1, f1, z', y')
  have hc1 : nextEl (core L f1) (prevEl r (lz L N r x)).1 =
      (nextEl r (Kepler.Text.Reduction5.ly L r x)).1 :=
    nextCoreNeFST L hL hgn hres hN1 hf1mem hz'f1 hcu1 hne H1
  have hnext : nextEl (core L r) (prevEl r (lz L N r x)).1 =
      nextEl (core L f1) (prevEl r (lz L N r x)).1 := by
    rw [hc1, hz, hy]
    exact hcon'
  -- `ne_fst_imp_f_list`
  have hfl : fList L (prevEl r (lz L N r x)) = nextEl r (Kepler.Text.Reduction5.ly L r x) :=
    neFstImpFList L hL hgn hres hN1 hf1mem hz'f1 hcu1 hne H1
  -- `next_el_core_imp_next_f`
  have hfin : nextEl r (prevEl r (lz L N r x)) = fList L (prevEl r (lz L N r x)) :=
    nextElCoreImpNextF L hL hgn hunL hen hN hrN hp hcu hN1 hf1mem hp' hcu1 hz'p hz'p'
      hnext (H1.trans hfl.symm)
  -- `next_prev_id`：next_el r z' = z ⇒ z = y'，与 FST y ≠ FST z 矛盾
  have hzz : nextEl r (prevEl r (lz L N r x)) = lz L N r x := by
    rw [nextElInstEq]
    exact nextPrevId hrnd _
  have hzy : lz L N r x = nextEl r (Kepler.Text.Reduction5.ly L r x) := by
    rw [← hzz, hfin, hfl]
  exact hfst (by rw [hzy, hy])

/-- **HOL `final_assumptions_not_next_core_0_i`**（reduction4.hl:5139）的
**显式槽版**：i < transform_count 且同面 betwn 空时，core 环上 FST (ytrans i) 的
后继不是 FST (ztrans i)。
槽 ① `hpnx1` = `Pnxvwfs.PNXVWFS1`（PNXVWFS.hl:120）在本实例的结论，
归属 tame-corr（PNXVWFS 港）；
槽 ② `hkb1` = `Kbwpbhq.KBWPBHQ1`（KBWPBHQ.hl:1114）在本实例的结论，
归属 tame-corr（KBWPBHQ 港）。
除两槽外，前提集 = HOL 原文前提集（另带 `AqiunppSlot`，树内既定惯例）。 -/
theorem finalAssumptionsNotNextCore0IOfSlots (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (hpnx1 : ∀ i, ¬ finalList L (rtrans L N r x i) → ytrans L N r x i ∈ r)
    (hkb1 : ∀ u, u ∈ r → u ∈ findFaceDarts L x →
      ((∃ i, ytrans L N r x i = u ∧ i < transformCount L N r x) ↔
        ¬ (nextEl (findList N u) u = fList L u))) :
    ∀ i, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
      nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 := by
  intro i hik hbet hcon
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hen : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hN : normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hN.1).1 _ hrN
  have hit : i < transformCount L N r x := by rw [hk]; exact hik
  have hnfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i hit
  -- `fst_yi_ne_fst_zi`（本波，Reduction5J5FstNe）
  have hfst : (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 :=
    fstYiNeFstZi L hL hgn hres haq k i hm hnf hk hik
  -- `final_assumption_mem_uniq` 第 6 合取（槽 ① + transform_count_not）与第 7 合取
  have hyr : ytrans L N r x i ∈ r := hpnx1 i hnfi
  have hyf : ytrans L N r x i ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl i
  -- `bet_eq_nil_imp_next_y_z`
  have Hyz : nextEl (rtrans L N r x (i + 1)) (ytrans L N r x i) = ztrans L N r x i :=
    betEqNilImpNextYZ L hL hgn hres haq k i hm hnf hk hik hbet
  obtain ⟨p, hp, hyp⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hyr
  have hcu : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  -- 状态 SUC i 的 marked_list（AQIUNPP）
  have hmS : markedList L hL (ntrans L N r x (i + 1)) (rtrans L N r x (i + 1)) x :=
    haq hgn N r x hm (i + 1)
  have hNS : normalList L hL (ntrans L N r x (i + 1)) := hmS.2.1
  have hrS : rtrans L N r x (i + 1) ∈ ntrans L N r x (i + 1) := hmS.2.2.1
  have hrSnd : (rtrans L N r x (i + 1)).Nodup := (List.nodup_flatten.mp hNS.1).1 _ hrS
  -- `mem_ytrans_rtrans_suc`
  have hyS : ytrans L N r x i ∈ rtrans L N r x (i + 1) :=
    memYtransRtransSuc L hL hgn haq i hnf hm hit
  obtain ⟨p', hp', hyp'⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrSnd hyS
  have hcuS : (core L (rtrans L N r x (i + 1))).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hmS
  -- `next_core_ne_FST` 于 (ntrans (SUC i), rtrans (SUC i), ytrans i, ztrans i)
  have hc1 : nextEl (core L (rtrans L N r x (i + 1))) (ytrans L N r x i).1 =
      (ztrans L N r x i).1 :=
    nextCoreNeFST L hL hgn hres hNS hrS hyS hcuS hfst Hyz
  have hnext : nextEl (core L r) (ytrans L N r x i).1 =
      nextEl (core L (rtrans L N r x (i + 1))) (ytrans L N r x i).1 := by
    rw [hc1]
    exact hcon
  -- `ne_fst_imp_f_list`
  have hfl : fList L (ytrans L N r x i) = ztrans L N r x i :=
    neFstImpFList L hL hgn hres hNS hrS hyS hcuS hfst Hyz
  -- `next_el_core_imp_next_f`
  have hfin : nextEl r (ytrans L N r x i) = fList L (ytrans L N r x i) :=
    nextElCoreImpNextF L hL hgn hunL hen hN hrN hp hcu hNS hrS hp' hcuS hyp hyp'
      hnext (Hyz.trans hfl.symm)
  -- `find_list_uniq`
  have hfind : findList N (ytrans L N r x i) = r := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListUniq hN.1 hyr hrN
  -- `KBWPBHQ1`（槽 ②）于 u := ytrans i 收口
  have hneg := (hkb1 (ytrans L N r x i) hyr hyf).mp ⟨i, rfl, hit⟩
  rw [hfind] at hneg
  exact hneg hfin

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.finalAssumptionsNotNextCore0ZY
#print axioms Kepler.Text.Reduction5.finalAssumptionsNotNextCore0IOfSlots

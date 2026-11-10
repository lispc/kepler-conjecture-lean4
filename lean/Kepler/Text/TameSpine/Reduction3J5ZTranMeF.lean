/-
  Kepler.Text.TameSpine.Reduction3J5ZTranMeF — tame-corr nb10：J5-5 前置
  小叶四件（ztran_me_f 双世界 + FST_next_face_eq_SND + MEM_CORE）。

  ┌─ 归属对账（HOL → Lean）─────────────────────────────────────
  │ ① `ztranMeFSpine`（HOL `Pplhulj.ztran_me_f`，PPLHULJ.hl:60）塔层 i
  │    spine 形：`¬final(i) ⇒ MEM (l'z(i)) f`（f = find_face L x）。
  │    证 = pplhuljV0（PPLHULJ 主件塔形）的第二合取直投——一行。
  │ ② `ztranMeFChain` 链世界形（无 ¬final、无 hta）：`MEM (ztrans i)
  │    (find_face L x)`。证 = `lzMemFindFaceDarts`（PwssratFace:101，
  │    namespace Kepler.Text.Reduction4Idx）在塔层 (ntrans i, rtrans i)
  │    实例化（haq 供塔层 marked）；ztrans 定义级 = lz 复合。**比 HOL
  │    原文强**（HOL 带 ¬final + TAV2）：链侧 fList 幂恒在面内。
  │ ③ `ytranMeFSpine`（HOL `Pplhulj.ytran_me_f`）：`¬final(i) ⇒
  │    MEM (l'y(i)) f`——pplhuljV0 第一合取直投（链世界孪生
  │    `MoreLemma2a23.ytranMeF` 已在库，不重落）。
  │ ④ `fstNextFaceEqSndSpine`（HOL `More_lemma2.FST_next_face_eq_SND`，
  │    more_lemma2:39）：`marked ∧ ¬final r ⇒ FST (next_el f x) = SND x`。
  │    证 = fList 定义级（next_el f x ≡ f_list L x）+ `fListFstSnd`
  │    （TameList10:319）。¬final 在 Lean 侧未消费（前提按 HOL 原文保留）。
  │ ⑤ `memCoreSpine`（HOL `More_lemma2.MEM_CORE`，more_lemma2:59）：
  │    `MEM d r ∧ ¬final r ⇒ MEM (FST d) (core L r)`。
  │    证 = partsMemExists（JcajyduBetwnMap:72）+ partsFst（TameList10:442）
  │    + coreSpine 定义（map head!.1）。¬final 同未消费（保留）。
  │ 链世界孪生查重：`Reduction5McCore.memCore` 已在库（陈述同 HOL，
  │  chain 形）；本件为 spine 形，非重落。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ spine 件（MarkedListSpineFull）+ 一个链世界件（markedList/haq）；
  │ 消费件：pplhuljV0 / aqiunpp3 / normalListUniqNonnil /
  │ normalListListOfDarts / fListFstSnd / partsMemExists / partsFst /
  │ lzMemFindFaceDarts；零 Dart-default 碰撞（本文件无 prevEl/nextEl 混合）。
  │ 默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pnxvwfs
import Kepler.Text.TameSpine.JcajyduBetwnMap
import Kepler.Text.PwssratFace

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart rtrans ntrans ztrans)

/-! ## §1 ztran_me_f / ytran_me_f 塔层形（PPLHULJ.hl:39/:60） -/

/-- **HOL `Pplhulj.ztran_me_f`**（PPLHULJ.hl:60）塔层 i spine 形：
`¬final(i) ⇒ MEM (l'z(i)) f`（f = find_face L x）。证 = pplhuljV0 第二合取。 -/
theorem ztranMeFSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} (hfind : findFaceDarts L x = f) :
    ztransSpine L N r x i ∈ f := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨-, hzf, -⟩ := pplhuljV0 L hL hgn hunL hmr hf
  rw [hfind] at hzf
  exact hzf

/-- **HOL `Pplhulj.ytran_me_f`** 塔层 i spine 形：`¬final(i) ⇒ MEM (l'y(i)) f`。
证 = pplhuljV0 第一合取（链世界孪生 MoreLemma2a23.ytranMeF 已在库）。 -/
theorem ytranMeFSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} (hfind : findFaceDarts L x = f) :
    ytransSpine L N r x i ∈ f := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf, -, -⟩ := pplhuljV0 L hL hgn hunL hmr hf
  rw [hfind] at hyf
  exact hyf

/-- **HOL `Pplhulj.ztran_me_f`**（PPLHULJ.hl:60）链世界形（强于 HOL：免 ¬final
与 TAV2 假设）：`MEM (ztrans i) (find_face L x)`。证 = lzMemFindFaceDarts
（PwssratFace:101，命名空间 Reduction4Idx）塔层实例化。 -/
theorem ztranMeFChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ) :
    ztrans L N r x i ∈ findFaceDarts L x :=
  Kepler.Text.Reduction4Idx.lzMemFindFaceDarts L hL (haq hgn N r x hm i)

/-! ## §2 FST_next_face_eq_SND / MEM_CORE（more_lemma2 :39 / :59） -/

/-- **HOL `More_lemma2.FST_next_face_eq_SND`**（more_lemma2:39）spine 形：
`marked ∧ ¬final r ⇒ FST (next_el (find_face L x) x) = SND x`。
证 = fList 定义级 + fListFstSnd（TameList10:319）。 -/
theorem fstNextFaceEqSndSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    (_hf : ¬ finalListSpine L r) :
    (nextEl (findFaceDarts L x) x).1 = x.2 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hx : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  exact fListFstSnd L hunL hx

/-- **HOL `More_lemma2.MEM_CORE`**（more_lemma2:59）spine 形：
`MEM d r ∧ ¬final r ⇒ MEM (FST d) (core L r)`。
证 = partsMemExists + partsFst + coreSpine 定义（map head!.1）。 -/
theorem memCoreSpine (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {d : ℕ × ℕ} (hd : d ∈ r) (_hf : ¬ finalListSpine L r) :
    d.1 ∈ coreSpine L r := by
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  obtain ⟨p, hp, hdp⟩ := partsMemExists L hrnd hd
  refine List.mem_map.mpr ⟨p, hp, ?_⟩
  exact (partsFst L hL hm.1.2.1 hm.1.2.2.1 hp hdp).symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ztranMeFSpine
#print axioms Kepler.Text.TameSpine.ytranMeFSpine
#print axioms Kepler.Text.TameSpine.ztranMeFChain
#print axioms Kepler.Text.TameSpine.fstNextFaceEqSndSpine
#print axioms Kepler.Text.TameSpine.memCoreSpine

/-
  Kepler.Text.TameSpine.Reduction3Kbwpbhq1Chain — tame-corr nb8：KBWPBHQ1
  的链世界形 `kbwpbhq1Chain`（aq13 F3 `hkb1` 槽形）+ transform_count 桥。

  ┌─ 归属对账─────────────────────────────────────────────────────
  │ ① `transformCountEqSpine`（桥件）：chain marked + ¬final r ⇒
  │    `transformCount = transformCountSpine`。证 = rtransEqSpine 逐点换
  │    定义集 + kbwpbhq0Spine（nb2）供非空 + minNumEqMinNumSpine
  │    （ChainTav2Interface:95，minNum = epsilon ↔ sInf 非空桥）。
  │ ② `kbwpbhq1Chain`（HOL `Kbwpbhq.KBWPBHQ1`，KBWPBHQ.hl:1114-1242 的
  │    链世界逐字形，**无 ¬final 前提**，与 HOL 及 aq13 F3 `hkb1` 槽同形）：
  │    MEM u r ∧ MEM u (find_face L x) ⇒ ((∃ i, ytrans i = u ∧
  │    i < transform_count) ⟺ ¬(next_el (find_list N u) u = f_list L u))。
  │    证（按 r 是否 final 二分）：
  │    · final 支（两侧皆假，纯链侧）：minNum_spec（Reduction5:65）⟹
  │      transform_count = 0；markedListCore_iff_markedListSpine
  │      （ChainBridgeParts:210，免 hs 槽）+ findListUniq ⟹
  │      find_list N u = r；final_list 定义点态。
  │    · ¬final 支：桥助件（nb8 PnxvwfsChain）换 marked/ytrans 形 +
  │      ① 换 transform_count + kbwpbhq1Spine（nb8）。
  │ 双 TAV2 槽（haq + hta）口径同 `pnxvwfs1Chain`（见该文件头）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）───────────────────────────────────────────
  │ 双载体桥接件（chain `markedList`/`rtrans`/`ytrans`/`transformCount`/
  │ `findList`/`finalList` ↔ spine 同名 Spine 件）；消费件：
  │ markedSpineFullOfChain / ytransEqSpineOfNotFinal（nb8）/
  │ kbwpbhq1Spine（nb8）/ kbwpbhq0Spine（nb2）/ transformCountSpineNot /
  │ rtransEqSpine / findList_eq_findListSpine /
  │ markedListCore_iff_markedListSpine / minNumEqMinNumSpine / minNum_spec
  │ / findListUniq；零 Dart-default 载体件。默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Kbwpbhq1
import Kepler.Text.TameSpine.Reduction3PnxvwfsChain
import Kepler.Text.TameSpine.ChainTav2Interface
import Kepler.Text.Reduction5

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList rtrans ntrans ytrans ztrans transformCount)

/-- **桥件**：chain `markedList` + `¬final r` ⇒
`transformCount = transformCountSpine`。
证 = rtransEqSpine 逐点换定义集 + kbwpbhq0Spine 供非空 +
minNumEqMinNumSpine（非空集上 epsilon 极小 = sInf）。 -/
theorem transformCountEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hta : transformAssumptionSpine L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    transformCount L N r x = transformCountSpine L N r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  obtain ⟨hmS, -⟩ := markedSpineFullOfChain L hL hgn haq hm 0 hf
  have hset : {i : ℕ | finalList L (rtrans L N r x i)}
      = {i : ℕ | finalListSpine L (rtransSpine L N r x i)} := by
    ext i
    show finalList L (rtrans L N r x i)
      ↔ finalListSpine L (rtransSpine L N r x i)
    rw [Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i]
    exact Iff.rfl
  have hne : ({i : ℕ | finalListSpine L (rtransSpine L N r x i)} : Set ℕ).Nonempty :=
    kbwpbhq0Spine L hL hta hgn hmS
  show Kepler.Text.Reduction5.minNum {i : ℕ | finalList L (rtrans L N r x i)}
    = minNumSpine {i : ℕ | finalListSpine L (rtransSpine L N r x i)}
  rw [hset]
  exact minNumEqMinNumSpine hne

/-- **HOL `Kbwpbhq.KBWPBHQ1`**（KBWPBHQ.hl:1114-1242）链世界逐字形
（无 ¬final 前提）：`MEM u r ∧ MEM u (find_face L x) ⇒
((∃ i, ytrans i = u ∧ i < transform_count) ⟺
¬(next_el (find_list N u) u = f_list L u))`。
双 TAV2 槽（haq + hta）。证：final r 支两侧皆假（纯链侧）；¬final 支
经桥助件 + transformCountEqSpine + kbwpbhq1Spine。 -/
theorem kbwpbhq1Chain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hta : transformAssumptionSpine L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {u : Dart} (hur : u ∈ r) (huf : u ∈ findFaceDarts L x) :
    (∃ i, ytrans L N r x i = u ∧ i < transformCount L N r x)
      ↔ ¬ (nextEl (Kepler.Text.ChainLists.findList N u) u = fList L u) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  rw [Kepler.Text.ChainBridge.findList_eq_findListSpine N u]
  by_cases hfr : finalList L r
  · -- final 支：transform_count = 0，find_list N u = r，两侧皆假
    have hcore : MarkedListSpine hL N r x :=
      (Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine L hL N r x).mp
        ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.1⟩
    rw [findListUniq hcore.2.1.1 hur hcore.2.2.1]
    have h0 : (0 : ℕ) ∈ {i : ℕ | finalList L (rtrans L N r x i)} := hfr
    have htc0 : transformCount L N r x = 0 :=
      Nat.le_zero.mp ((Kepler.Text.Reduction5.minNum_spec ⟨0, h0⟩).2 0 h0)
    constructor
    · rintro ⟨i, -, hit⟩
      rw [htc0] at hit
      exact absurd hit (Nat.not_lt_zero i)
    · intro h
      exact absurd (hfr u hur).symm h
  · -- ¬final 支：载体桥 + kbwpbhq1Spine
    obtain ⟨hmS, -⟩ := markedSpineFullOfChain L hL hgn haq hm 0 hfr
    have hK := kbwpbhq1Spine L hL hta hgn hunL hmS hur huf
    rw [transformCountEqSpine L hL hgn haq hta hm hfr]
    constructor
    · rintro ⟨i, hyu, hit⟩
      have hfi : ¬ finalList L (rtrans L N r x i) := by
        rw [Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i]
        exact transformCountSpineNot L N r x hit
      rw [ytransEqSpineOfNotFinal L hL hgn haq hm i hfi] at hyu
      exact hK.mp ⟨i, hyu, hit⟩
    · intro h
      obtain ⟨i, hyu, hit⟩ := hK.mpr h
      have hfi : ¬ finalList L (rtrans L N r x i) := by
        rw [Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i]
        exact transformCountSpineNot L N r x hit
      refine ⟨i, ?_, hit⟩
      rw [ytransEqSpineOfNotFinal L hL hgn haq hm i hfi]
      exact hyu

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.transformCountEqSpine
#print axioms Kepler.Text.TameSpine.kbwpbhq1Chain

/-
  Kepler.Text.TameSpine.Reduction3J5PowerCore — tame-corr nb12：J5-5 波 1 余量
  `next_power_core` 族四件（more_lemma2.hl :292 / :371 / :844 / :1287）的链层形。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/more_lemma2.hl`）──
  │ :292  `next_power_core`       → `nextPowerCore`
  │       `good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ∧
  │        n ≤ indexf w (ytrans L N r x 0) r ∧ find_face L x = f ∧ next_el f x = w
  │        ⇒ (next_el (core L r) POWER n) (FST x) = FST ((next_el r POWER n) x)`
  │ :371  `next_power_core_w`     → `nextPowerCoreW`（同上，起点 w）
  │ :844  `next_power_core_pre`   → `nextPowerCorePre`（起点 ztrans (PRE k)，k = count）
  │ :1287 `next_power_core_ytran` → `nextPowerCoreYtran`（起点 ztrans i，i+1 < k，
  │        上界经 ytrans (SUC i)）
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（证体，逐条对照 HOL）─────────────────────────────────────
  │ 四件同构：对 n 归纳。零支 = FST 恒等；步支取 d := (next_el r)^n 起点，
  │ ① `next_core_FST`（more_lemma2:221，在库 `Reduction5.nextCoreFst`，链层
  │    逐字形）于 d 处实例化——需 `d ∈ r`（`memPowerNextEl`）与
  │    `f_list L d = next_el r d`；
  │ ② `f_list L d` 的定义级展开 + `mem_find_face_imp_faces_eq`（d ∈ f）+
  │    起点差一步的幂关系；
  │ ③ 幂关系来源分三路：
  │    · `next_power_core` / `_w`：`next_el_power_trans_eq_f`@0
  │      （在库 `Reduction5.nextElPowerTransEqFv0`，链层）；
  │    · `_pre`：`CASES2`@(PRE k)（spine 件 `cases2Spine` + 链桥 `cases2Chain`）；
  │    · `_ytran`：`betwn_ztran_ytrans_suc_const`@i（spine 件
  │      `betwnZtranYtransSucConstSpine` + 链桥 `betwnZtranYtransSucConstChain`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 查重记账（本笔实测）───────────────────────────────────────────
  │ `next_core_FST` 的链层形 `Reduction5.nextCoreFst`（Reduction5J5M2Core:173）
  │ 与两件 Hypermap 核 `isRestrictedEListNondeg` / `edgeNondegFXorNi`
  │ （MoreLemma2Island3:165/:182 + TameList6:591 / TameList8:368 双份）均已
  │ 在库（前笔冻结表为 stale 盘点）；本文件零重落，直接消费。
  │ 族四件在库零命中（精确式 + 子串式两遍实测）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.Reduction5TwelveT
import Kepler.Text.TameSpine.Reduction3PnxvwfsChain
import Kepler.Text.TameSpine.Reduction3KbwpbhqCases2
import Kepler.Text.TameSpine.Reduction3KbwpbhqBetwn
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.ChainSpineBridge
import Kepler.Text.Reduction5Qcdvkea
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList core rtrans ntrans ytrans ztrans
  transformCount indexf)

/-! ## §0 私有桥件 -/

/-- 链层 `transform_count = k > 0` ⇒ 初始状态非 final（HOL `transform_count_not`@0）。 -/
private theorem notFinalOfTransformCountPos (L : fgraph ℕ) {N : List (List Dart)}
    {r : List Dart} {x : Dart} {k : ℕ}
    (hk : transformCount L N r x = k) (hk0 : 0 < k) : ¬ finalList L r := by
  have h0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  rw [Kepler.Text.Reduction5.rtrans_zero] at h0
  exact h0

/-- 链层第 i 状态非 final ⇒ `ztrans i` 与 spine 形相等（`ytrans` 的同款桥
在库 `Reduction3PnxvwfsChain.ytransEqSpineOfNotFinal`，本文件直接消费）。 -/
private theorem ztransEqSpineOfNotFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hfi : ¬ finalList L (rtrans L N r x i)) :
    ztrans L N r x i = ztransSpine L N r x i := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  show Kepler.Text.Reduction5.lz L (Kepler.Text.Reduction5.ntrans L N r x i)
      (Kepler.Text.Reduction5.rtrans L N r x i) x
    = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
  rw [Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL
      (haq hgn N r x hm i) hfi,
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i,
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i]

/-- **链桥：HOL `Kbwpbhq.CASES2`**（KBWPBHQ.hl:935）链层形。证 = spine 件
`cases2Spine` + `transformCountEqSpineOfAq` + `indexf_eq_spine` 换词。 -/
private theorem cases2Chain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) w f) :
    (nextEl r)^[n] (ztrans L N r x (k - 1))
      = (nextEl f)^[n] (ztrans L N r x (k - 1)) := by
  have hf : ¬ finalList L r := notFinalOfTransformCountPos L hk hk0
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hta : transformAssumptionSpine L hL :=
    Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
  have hmS : MarkedListSpineFull hL N r x :=
    markedSpineFullOfChainAlways L hL hgn haq hm
  have htc : transformCountSpine L N r x = k := by
    rw [← transformCountEqSpineOfAq L hL hgn haq hm hf, hk]
  have hfi : ¬ finalList L (rtrans L N r x (k - 1)) :=
    Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)
  have hzEq : ztrans L N r x (k - 1) = ztransSpine L N r x (k - 1) :=
    ztransEqSpineOfNotFinal L hL hgn haq hm (k - 1) hfi
  have hn' : n ≤ Kepler.Text.TameSpine.indexf
      (Kepler.Text.TameSpine.ztransSpine L N r x (k - 1)) w f := by
    rw [← hzEq, ← Kepler.Text.Reduction3.indexf_eq_spine]
    exact hn
  have h := cases2Spine L hL hta hgn hunL hmS hfind hw hk0 htc hn'
  rwa [← hzEq] at h

/-- **链桥：HOL `Kbwpbhq.betwn_ztran_ytrans_suc_const`**（KBWPBHQ.hl:623）
链层形。证 = spine 件 `betwnZtranYtransSucConstSpine` + 双 `ztrans`/`ytrans`
换词 + `indexf_eq_spine`。 -/
private theorem betwnZtranYtransSucConstChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) f) :
    (nextEl r)^[n] (ztrans L N r x i) = (nextEl f)^[n] (ztrans L N r x i) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hta : transformAssumptionSpine L hL :=
    Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
  have hmS : MarkedListSpineFull hL N r x :=
    markedSpineFullOfChainAlways L hL hgn haq hm
  have hfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.finalListInduct i hf
  have hzEq : ztrans L N r x i = ztransSpine L N r x i :=
    ztransEqSpineOfNotFinal L hL hgn haq hm i hfi
  have hyEq : ytrans L N r x (i + 1) = ytransSpine L N r x (i + 1) :=
    ytransEqSpineOfNotFinal L hL hgn haq hm (i + 1) hf
  have hfSpine : ¬ finalListSpine L (rtransSpine L N r x (i + 1)) := by
    rw [← Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm (i + 1)]
    exact hf
  have hn' : n ≤ Kepler.Text.TameSpine.indexf
      (Kepler.Text.TameSpine.ztransSpine L N r x i)
      (Kepler.Text.TameSpine.ytransSpine L N r x (i + 1)) f := by
    rw [← hzEq, ← hyEq, ← Kepler.Text.Reduction3.indexf_eq_spine]
    exact hn
  have h := betwnZtranYtransSucConstSpine L hL hta hgn hunL hmS i hfSpine hfind hw hn'
  rwa [← hzEq] at h

/-! ## §1 族四件 -/

/-- **HOL `More_lemma2.next_power_core`**（more_lemma2.hl:292-370）：
`good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ∧
  n ≤ indexf w (ytrans L N r x 0) r ∧ find_face L x = f ∧ next_el f x = w
  ⇒ (next_el (core L r) POWER n) (FST x) = FST ((next_el r POWER n) x)`。 -/
theorem nextPowerCore (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r) :
    (nextEl (core L r))^[n] x.1 = ((nextEl r)^[n] x).1 := by
  have hxr : x ∈ r := hm.2.2.2.1
  have hxf : x ∈ f := by
    rw [← hfind]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hwr : w = nextEl r x := by
    rw [← hw, ← hfind]
    exact hm.2.2.2.2.2.1.symm
  have hP : ∀ {j : ℕ}, j ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r →
      (nextEl r)^[j] w = (nextEl f)^[j] w := by
    intro j hj
    rw [← hfind]
    exact Kepler.Text.Reduction5.nextElPowerTransEqFv0 hL hgn haq hm hf (by rw [hfind]; exact hw) hj
  induction n with
  | zero => rfl
  | succ m ih =>
    have hnm : m ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r :=
      Nat.le_trans (Nat.le_succ m) hn
    have hih := ih hnm
    set d : Dart := (nextEl r)^[m] x with hd
    have hdr : d ∈ r := by
      rw [hd]
      exact memPowerNextEl hxr m
    have hwk : (nextEl r)^[m] x = (nextEl f)^[m] x := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        rfl
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hmpos)
        rw [Function.iterate_succ_apply (nextEl r) j x, hwr.symm,
          Function.iterate_succ_apply (nextEl f) j x, hw]
        exact hP (Nat.le_trans (Nat.le_succ j) hnm)
    have hwk1 : (nextEl r)^[Nat.succ m] x = (nextEl f)^[Nat.succ m] x := by
      rw [Function.iterate_succ_apply (nextEl r) m x, hwr.symm,
        Function.iterate_succ_apply (nextEl f) m x, hw]
      exact hP hnm
    have hdf : d ∈ findFaceDarts L x := by
      rw [hfind, hd, hwk]
      exact memPowerNextEl hxf m
    have hfaces : findFaceDarts L d = findFaceDarts L x :=
      Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hdf
    have hfd : fList L d = nextEl r d := by
      show nextEl (findFaceDarts L d) d = nextEl r d
      rw [hfaces, hfind, hd]
      calc nextEl f ((nextEl r)^[m] x)
          = nextEl f ((nextEl f)^[m] x) := by rw [hwk]
        _ = (nextEl f)^[Nat.succ m] x :=
            (Function.iterate_succ_apply' (nextEl f) m x).symm
        _ = (nextEl r)^[Nat.succ m] x := hwk1.symm
        _ = nextEl r ((nextEl r)^[m] x) :=
            Function.iterate_succ_apply' (nextEl r) m x
    have hcore := Kepler.Text.Reduction5.nextCoreFst L hL hgn hm hf hdr hfd
    rw [Function.iterate_succ_apply' (nextEl (core L r)) m x.1, hih,
      Function.iterate_succ_apply' (nextEl r) m x]
    exact hcore

/-- **HOL `More_lemma2.next_power_core_w`**（more_lemma2.hl:371-426）：
同前件，起点换 `w`：
`(next_el (core L r) POWER n) (FST w) = FST ((next_el r POWER n) w)`。 -/
theorem nextPowerCoreW (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r) :
    (nextEl (core L r))^[n] w.1 = ((nextEl r)^[n] w).1 := by
  have hxf : x ∈ f := by
    rw [← hfind]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hwr : w ∈ r := by
    have hwr' : w = nextEl r x := by
      rw [← hw, ← hfind]
      exact hm.2.2.2.2.2.1.symm
    rw [hwr']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hm.2.2.2.1
  have hwf : w ∈ f := by
    rw [← hw]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hP : ∀ {j : ℕ}, j ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r →
      (nextEl r)^[j] w = (nextEl f)^[j] w := by
    intro j hj
    rw [← hfind]
    exact Kepler.Text.Reduction5.nextElPowerTransEqFv0 hL hgn haq hm hf (by rw [hfind]; exact hw) hj
  induction n with
  | zero => rfl
  | succ m ih =>
    have hnm : m ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r :=
      Nat.le_trans (Nat.le_succ m) hn
    have hih := ih hnm
    set d : Dart := (nextEl r)^[m] w with hd
    have hdr : d ∈ r := by
      rw [hd]
      exact memPowerNextEl hwr m
    have hwk : (nextEl r)^[m] w = (nextEl f)^[m] w := hP hnm
    have hwk1 : (nextEl r)^[Nat.succ m] w = (nextEl f)^[Nat.succ m] w := hP hn
    have hdf : d ∈ findFaceDarts L x := by
      rw [hfind, hd, hwk]
      exact memPowerNextEl hwf m
    have hfaces : findFaceDarts L d = findFaceDarts L x :=
      Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hdf
    have hfd : fList L d = nextEl r d := by
      show nextEl (findFaceDarts L d) d = nextEl r d
      rw [hfaces, hfind, hd]
      calc nextEl f ((nextEl r)^[m] w)
          = nextEl f ((nextEl f)^[m] w) := by rw [hwk]
        _ = (nextEl f)^[Nat.succ m] w :=
            (Function.iterate_succ_apply' (nextEl f) m w).symm
        _ = (nextEl r)^[Nat.succ m] w := hwk1.symm
        _ = nextEl r ((nextEl r)^[m] w) :=
            Function.iterate_succ_apply' (nextEl r) m w
    have hcore := Kepler.Text.Reduction5.nextCoreFst L hL hgn hm hf hdr hfd
    rw [Function.iterate_succ_apply' (nextEl (core L r)) m w.1, hih,
      Function.iterate_succ_apply' (nextEl r) m w]
    exact hcore

/-- **HOL `More_lemma2.next_power_core_pre`**（more_lemma2.hl:844-889）：
`good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ transform_count = k ∧ 0 < k ∧
  n ≤ indexf zk w f ∧ find_face L x = f ∧ ztrans (PRE k) = zk ∧ next_el f x = w
  ⇒ (next_el (core L r) POWER n) (FST zk) = FST ((next_el r POWER n) zk)`。 -/
theorem nextPowerCorePre (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {zk : Dart}
    (hz : ztrans L N r x (k - 1) = zk) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf zk w f) :
    (nextEl (core L r))^[n] zk.1 = ((nextEl r)^[n] zk).1 := by
  have hf : ¬ finalList L r := notFinalOfTransformCountPos L hk hk0
  have hzkr : zk ∈ r := by
    rw [← hz]
    exact Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq (k - 1)
      (Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)) hm
  have hzkf : zk ∈ f := by
    rw [← hz, ← hfind]
    exact Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm (k - 1)
  have hC : ∀ {j : ℕ}, j ≤ Kepler.Text.Reduction5.indexf zk w f →
      (nextEl r)^[j] zk = (nextEl f)^[j] zk := by
    intro j hj
    rw [← hz] at hj ⊢
    exact cases2Chain L hL hgn haq hm hfind hw hk hk0 hj
  induction n with
  | zero => rfl
  | succ m ih =>
    have hnm : m ≤ Kepler.Text.Reduction5.indexf zk w f := Nat.le_trans (Nat.le_succ m) hn
    have hih := ih hnm
    set d : Dart := (nextEl r)^[m] zk with hd
    have hdr : d ∈ r := by
      rw [hd]
      exact memPowerNextEl hzkr m
    have hwk : (nextEl r)^[m] zk = (nextEl f)^[m] zk := hC hnm
    have hwk1 : (nextEl r)^[Nat.succ m] zk = (nextEl f)^[Nat.succ m] zk := hC hn
    have hdf : d ∈ findFaceDarts L x := by
      rw [hfind, hd, hwk]
      exact memPowerNextEl hzkf m
    have hfaces : findFaceDarts L d = findFaceDarts L x :=
      Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hdf
    have hfd : fList L d = nextEl r d := by
      show nextEl (findFaceDarts L d) d = nextEl r d
      rw [hfaces, hfind, hd]
      calc nextEl f ((nextEl r)^[m] zk)
          = nextEl f ((nextEl f)^[m] zk) := by rw [hwk]
        _ = (nextEl f)^[Nat.succ m] zk :=
            (Function.iterate_succ_apply' (nextEl f) m zk).symm
        _ = (nextEl r)^[Nat.succ m] zk := hwk1.symm
        _ = nextEl r ((nextEl r)^[m] zk) :=
            Function.iterate_succ_apply' (nextEl r) m zk
    have hcore := Kepler.Text.Reduction5.nextCoreFst L hL hgn hm hf hdr hfd
    rw [Function.iterate_succ_apply' (nextEl (core L r)) m zk.1, hih,
      Function.iterate_succ_apply' (nextEl r) m zk]
    exact hcore

/-- **HOL `More_lemma2.next_power_core_ytran`**（more_lemma2.hl:1287-1335）：
`good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ transform_count = k ∧
  SUC i < k ∧ n ≤ indexf zi yi f ∧ find_face L x = f ∧ ztrans i = zi ∧
  ytrans (SUC i) = yi ∧ next_el f x = w
  ⇒ (next_el (core L r) POWER n) (FST zi) = FST ((next_el r POWER n) zi)`。 -/
theorem nextPowerCoreYtran (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {k : ℕ} (hk : transformCount L N r x = k) {i : ℕ} (hi : Nat.succ i < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {zi : Dart}
    (hzi : ztrans L N r x i = zi) {yi : Dart}
    (hyi : ytrans L N r x (Nat.succ i) = yi) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf zi yi f) :
    (nextEl (core L r))^[n] zi.1 = ((nextEl r)^[n] zi).1 := by
  have hk0 : 0 < k := by omega
  have hf : ¬ finalList L r := notFinalOfTransformCountPos L hk hk0
  have hir : i < k := by omega
  have hzkr : zi ∈ r := by
    rw [← hzi]
    exact Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq i
      (Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hir)) hm
  have hzkf : zi ∈ f := by
    rw [← hzi, ← hfind]
    exact Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
  have hfi1 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1)
      (by rw [hk]; omega)
  have hB : ∀ {j : ℕ}, j ≤ Kepler.Text.Reduction5.indexf zi yi f →
      (nextEl r)^[j] zi = (nextEl f)^[j] zi := by
    intro j hj
    rw [← hzi, ← hyi] at hj
    rw [← hzi]
    exact betwnZtranYtransSucConstChain L hL hgn haq hm i hfi1 hfind hw hj
  induction n with
  | zero => rfl
  | succ m ih =>
    have hnm : m ≤ Kepler.Text.Reduction5.indexf zi yi f := Nat.le_trans (Nat.le_succ m) hn
    have hih := ih hnm
    set d : Dart := (nextEl r)^[m] zi with hd
    have hdr : d ∈ r := by
      rw [hd]
      exact memPowerNextEl hzkr m
    have hwk : (nextEl r)^[m] zi = (nextEl f)^[m] zi := hB hnm
    have hwk1 : (nextEl r)^[Nat.succ m] zi = (nextEl f)^[Nat.succ m] zi := hB hn
    have hdf : d ∈ findFaceDarts L x := by
      rw [hfind, hd, hwk]
      exact memPowerNextEl hzkf m
    have hfaces : findFaceDarts L d = findFaceDarts L x :=
      Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hdf
    have hfd : fList L d = nextEl r d := by
      show nextEl (findFaceDarts L d) d = nextEl r d
      rw [hfaces, hfind, hd]
      calc nextEl f ((nextEl r)^[m] zi)
          = nextEl f ((nextEl f)^[m] zi) := by rw [hwk]
        _ = (nextEl f)^[Nat.succ m] zi :=
            (Function.iterate_succ_apply' (nextEl f) m zi).symm
        _ = (nextEl r)^[Nat.succ m] zi := hwk1.symm
        _ = nextEl r ((nextEl r)^[m] zi) :=
            Function.iterate_succ_apply' (nextEl r) m zi
    have hcore := Kepler.Text.Reduction5.nextCoreFst L hL hgn hm hf hdr hfd
    rw [Function.iterate_succ_apply' (nextEl (core L r)) m zi.1, hih,
      Function.iterate_succ_apply' (nextEl r) m zi]
    exact hcore

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.nextPowerCore
#print axioms Kepler.Text.TameSpine.nextPowerCoreW
#print axioms Kepler.Text.TameSpine.nextPowerCorePre
#print axioms Kepler.Text.TameSpine.nextPowerCoreYtran

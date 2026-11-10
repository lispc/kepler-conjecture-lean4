/-
  Kepler.Text.PwssratCase — 铺装 batch A8：next_mark_case_mem 链侧 + Aq13

  PLAN-P7 §6 件 1 + 件 2（裁决：本批 A8；件 4 复核后报 BLOCKED-on-layer，见 DELIVERY）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ NCVIBWU.hl:333  `next_mark_case_mem`            → nextMarkCaseMem
  │ AQ13.hl:42      `next_mark_in_rtrans_suc`       → nextMarkInRtransSuc
  │ AQ7.hl:128      `indexf_const_le_indexf_ytrans_v0` → indexfConstLe
  │ AQ7.hl:181      `indexf_y_le_z_in_r_0`          → indexfYLeZInR0
  │ NCVIBWU.hl:190  `l_y_rep_power_le`              → lYRepPowerLe
  │ （Spine 侧同名件：JcajyduAqLeaf10.aq10_indexfConstLe /
  │   aq10_indexfYLeZInR0 / aq10_lYRepPowerLe、JcajyduAqLeaf12T.aqs_nextMarkCaseMem。）
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（链侧；0 直接 TameSpine import）────────────────────────
  │ ① `indexfConstLe`（r-index ↔ f-index 转移）：`l'y = (f_list)^(l'm+1) x`
  │    （`lYRepPowerLe`，minNotEqImpEq）+ `fListPowEqNextElPow`（patch7）+
  │    `nextElnIndexf` + 界 `l'm < |find_face x|`（`lmLtFaceLen` 本地重证，
  │    patch7 私件同体）。
  │ ② `indexfYLeZInR0`：patch7 `pplhulj3V0`（f-index 不等式）+ ① 双向转移
  │    （ZIndexf aq10_indexfYLeZInR0 同构）。
  │ ③ `nextMarkCaseMem`：② + `indexfBetwnEq`/`indexfCompl`/`indexf_add_left`/
  │    `indexf_eq_zero`/`indexfRefl` 环算术（Leaf12T 同构）。
  │ ④ `nextMarkInRtransSuc`：③ + `rtrans 1` 拆分形（Reduction3Thm1.rtrans1 +
  │    splitNormalList 展开 + `nextEl_prevEl`）⇒ `between r l'z l'y ⊆ rtrans 1`
  │    与 `l'y ∈ rtrans 1`。
  │ ⑤ 无 `haq`：件 1/2 均在当前 loop r 上（Spine v0 同口径）；patch8 前置把
  │    `PwssratTail.lmLtLength`/`indexfYtransEqLM1Core` 上调 public
  │    （陈述/证体逐字未动）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；零直接 TameSpine import；
  不改既有陈述；主仓 tracked 仅 PwssratTail 可见性 + 本新文件。
-/

import Kepler.Text.PwssratMemberBase
import Kepler.Text.PwssratFace
import Kepler.Text.PwssratTail
import Kepler.Text.Reduction3Thm1
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

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart lz ztrans rtrans finalList indexf)

/-! ## §0 界件（patch7 私件同体重证） -/

/-- `l'm L r x < sizel (find_face L x)`（ZIndexf `aq10_lmLtFaceLen` 链侧同证）：
`hypM_lt_face`（Hypermap 公开）+ `hypMLmChain` + `cardFaceOfList`。 -/
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

/-! ## §1 `l_y_rep_power_le`（NCVIBWU.hl:190）：f 幂 = next_el 幂直到 l'm -/

/-- **HOL `Ncvibwu.l_y_rep_power_le`**（NCVIBWU.hl:190）：`f_list L x = next_el r x`
⇒ `∀ j ≤ l'm, (f_list)^(j+1) x = (next_el r)^(j+1) x`。 -/
theorem lYRepPowerLe (L : fgraph ℕ) (r : List Dart) (x : Dart)
    (hnext : fList L x = nextEl r x) :
    ∀ j : ℕ, j ≤ Kepler.Text.Reduction5.lm L r x →
      (fList L)^[j + 1] x = (nextEl r)^[j + 1] x := by
  intro j hj
  have hset : {m : ℕ | (nextEl r)^[m + 2] x
        ≠ fList L ((nextEl r)^[m + 1] x)}
      = {m : ℕ | nextEl r (nextEl r ((nextEl r)^[m] x))
          ≠ fList L (nextEl r ((nextEl r)^[m] x))} := by
    ext m
    simp only [Set.mem_setOf_eq]
    rw [show (nextEl r)^[m + 2] x
          = nextEl r (nextEl r ((nextEl r)^[m] x)) from by
        rw [show m + 2 = (m + 1) + 1 from rfl, Function.iterate_succ_apply',
          Function.iterate_succ_apply'],
      Function.iterate_succ_apply']
  have hmin : Kepler.Text.Reduction5.minNum
      {m : ℕ | nextEl r (nextEl r ((nextEl r)^[m] x))
        ≠ fList L (nextEl r ((nextEl r)^[m] x))}
      = Kepler.Text.Reduction5.lm L r x := by
    show Kepler.Text.Reduction5.minNum _ =
      Kepler.Text.Reduction5.minNum
        {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)}
    rw [hset]
  have h := Kepler.Text.MoreLemma2Aux.minNotEqImpEq (nextEl r) (fList L) x
    (n := Kepler.Text.Reduction5.lm L r x) hmin j hj
  rw [← hnext] at h
  rw [Function.iterate_succ_apply]
  exact h.symm

/-! ## §2 `indexf_const_le_indexf_ytrans`（Aq7.hl:128 v0）：r-index ↔ f-index 转移 -/

/-- **HOL `Aq7.indexf_const_le_indexf_ytrans_v0`**（AQ7.hl:128）链层形：
`d ∈ r ∧ indexf w d r ≤ indexf w (l'y) r ⇒ indexf w d r = indexf w d (find_face L x)`
（`w = next_el (find_face L x) x`）。 -/
theorem indexfConstLe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r)
    {d : Dart} (hd : d ∈ r)
    (hle : indexf (nextEl (findFaceDarts L x) x) d r
      ≤ indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x) r) :
    indexf (nextEl (findFaceDarts L x) x) d r
      = indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) := by
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hw : nextEl (findFaceDarts L x) x ∈ r := by
    show fList L x ∈ r
    rw [← hnext]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hY : indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x) r
      = Kepler.Text.Reduction5.lm L r x :=
    indexfYtransEqLM1Core L hL hm hf
  have hle' : indexf (nextEl (findFaceDarts L x) x) d r
      ≤ Kepler.Text.Reduction5.lm L r x := by
    rw [← hY]; exact hle
  have hiterR : (nextEl r)^[indexf (nextEl (findFaceDarts L x) x) d r]
      (nextEl (findFaceDarts L x) x) = d := by
    have h := Kepler.Text.TameSpine.indexfN hw hd hrnd
    rw [← Kepler.Text.Reduction3.indexf_eq_spine
      (nextEl (findFaceDarts L x) x) d r] at h
    exact h
  have hwEq : nextEl (findFaceDarts L x) x = nextEl r x := hnext.symm
  have hstepR : (nextEl r)^[indexf (nextEl (findFaceDarts L x) x) d r + 1] x = d := by
    rw [Function.iterate_succ_apply, ← hwEq]
    exact hiterR
  have hLY := lYRepPowerLe L r x hnext.symm
    (indexf (nextEl (findFaceDarts L x) x) d r) hle'
  have hfl : (fList L)^[indexf (nextEl (findFaceDarts L x) x) d r + 1] x = d :=
    hLY.trans hstepR
  have hxd : x ∈ listOfDarts L :=
    Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hface : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hfpow := fListPowEqNextElPow L hL hface
    (indexf (nextEl (findFaceDarts L x) x) d r + 1)
  have hflW : (nextEl (findFaceDarts L x))^[
      indexf (nextEl (findFaceDarts L x) x) d r] (nextEl (findFaceDarts L x) x) = d := by
    have h := hfl
    rw [hfpow] at h
    rwa [Function.iterate_succ_apply] at h
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    Kepler.Text.TameLp.nextEl_mem_of_mem hface
  have hdf : d ∈ findFaceDarts L x := by
    have key : ∀ m : ℕ, (nextEl (findFaceDarts L x))^[m]
        (nextEl (findFaceDarts L x) x) ∈ findFaceDarts L x := by
      intro m
      induction m with
      | zero => simpa using hwf
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
    rw [← hflW]
    exact key _
  have hfnd : (findFaceDarts L x).Nodup :=
    Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hlt : indexf (nextEl (findFaceDarts L x) x) d r
      < (findFaceDarts L x).length := by
    have := lmLtFaceLen L hL hgn hunL hm hf
    omega
  have hF : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x)
      = indexf (nextEl (findFaceDarts L x) x) d r := by
    have h := Kepler.Text.TameSpine.nextElnIndexf hwf hdf hfnd hflW hlt
    rw [← Kepler.Text.Reduction3.indexf_eq_spine
      (nextEl (findFaceDarts L x) x) d (findFaceDarts L x)] at h
    exact h
  exact hF.symm

/-! ## §3 `indexf_y_le_z_in_r_0`（Aq7.hl:181）：r 上 l'y 在 l'z 之前 -/

/-- **HOL `Aq7.indexf_y_le_z_in_r_0`**（AQ7.hl:181）链层形：
`indexf w (l'y) r < indexf w (l'z) r`（`w = next_el (find_face L x) x`）。 -/
theorem indexfYLeZInR0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x) r
      < indexf (nextEl (findFaceDarts L x) x) (lz L N r x) r := by
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hyr : Kepler.Text.Reduction5.ly L r x ∈ r := by
    have key : ∀ m : ℕ, (nextEl r)^[m] x ∈ r := by
      intro m
      induction m with
      | zero => simpa using hxr
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
    have hly : Kepler.Text.Reduction5.ly L r x
        = (nextEl r)^[Kepler.Text.Reduction5.lm L r x + 1] x :=
      lYRepPowerLe L r x hnext.symm _ le_rfl
    rw [hly]
    exact key _
  have hzr : lz L N r x ∈ r :=
    (hqymrtx1List L hL hgn hunL hm hf (sListEqOfMarked L hL hm hf)).1
  have hpp := pplhulj3V0 L hL hgn hunL hm hf
  have hconstY := indexfConstLe L hL hgn hunL hm hf hyr (Nat.le_refl _)
  by_contra hge
  push Not at hge
  have hconstZ := indexfConstLe L hL hgn hunL hm hf hzr hge
  rw [← hconstY, ← hconstZ] at hpp
  omega

/-! ## §4 `next_mark_case_mem`（NCVIBWU.hl:333）：标记后继落在 z→y 弧上 -/

/-- **HOL `Ncvibwu.next_mark_case_mem`**（NCVIBWU.hl:333）链层形：
`find_face L x = f`、`next_el f x = w` ⇒ `w = l'y ∨ w ∈ betwn r l'z l'y`。 -/
theorem nextMarkCaseMem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart}
    (hfind : findFaceDarts L x = f) (hnext : nextEl f x = w) :
    w = Kepler.Text.Reduction5.ly L r x
      ∨ w ∈ between r (lz L N r x) (Kepler.Text.Reduction5.ly L r x) := by
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hnextR : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind]; exact hnext
  have hwr : w ∈ r := by
    rw [← hw']
    show fList L x ∈ r
    rw [← hnextR]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hyr : Kepler.Text.Reduction5.ly L r x ∈ r := by
    have key : ∀ m : ℕ, (nextEl r)^[m] x ∈ r := by
      intro m
      induction m with
      | zero => simpa using hxr
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
    have hly : Kepler.Text.Reduction5.ly L r x
        = (nextEl r)^[Kepler.Text.Reduction5.lm L r x + 1] x :=
      lYRepPowerLe L r x hnextR.symm _ le_rfl
    rw [hly]
    exact key _
  have hzr : lz L N r x ∈ r :=
    (hqymrtx1List L hL hgn hunL hm hf (sListEqOfMarked L hL hm hf)).1
  have hyz : Kepler.Text.Reduction5.ly L r x ≠ lz L N r x := by
    have hexcl := (hqymrtx1List L hL hgn hunL hm hf (sListEqOfMarked L hL hm hf)).2
      (Kepler.Text.Reduction5.lm L r x + 1) (by omega) le_rfl
    have hly : Kepler.Text.Reduction5.ly L r x
        = (fList L)^[Kepler.Text.Reduction5.lm L r x + 1] x := rfl
    rw [hly]
    exact fun e => hexcl e.symm
  have hpp : indexf w (Kepler.Text.Reduction5.ly L r x) r
      < indexf w (lz L N r x) r := by
    have h := indexfYLeZInR0 L hL hgn hunL hm hf
    rwa [hw'] at h
  by_cases h0 : indexf w (Kepler.Text.Reduction5.ly L r x) r = 0
  · left
    exact Kepler.Text.Reduction4.indexf_eq_zero hwr hyr h0
  · right
    have hpos_wy : 0 < indexf w (Kepler.Text.Reduction5.ly L r x) r :=
      Nat.pos_of_ne_zero h0
    have hwz : w ≠ lz L N r x := by
      intro h
      rw [h, Kepler.Text.Reduction4.indexfRefl hzr] at hpp
      omega
    have hadd1 : indexf w (Kepler.Text.Reduction5.ly L r x) r
        + indexf (Kepler.Text.Reduction5.ly L r x) (lz L N r x) r
        = indexf w (lz L N r x) r :=
      Kepler.Text.Reduction4.indexf_add_left hwr hyr hzr (le_of_lt hpp)
    have hanti1 : indexf w (lz L N r x) r
        + indexf (lz L N r x) w r = r.length :=
      Kepler.Text.Reduction5.indexfCompl hwr hzr hwz
    have hanti2 : indexf (lz L N r x) (Kepler.Text.Reduction5.ly L r x) r
        + indexf (Kepler.Text.Reduction5.ly L r x) (lz L N r x) r = r.length :=
      Kepler.Text.Reduction5.indexfCompl hzr hyr (Ne.symm hyz)
    have hpos_zw : 0 < indexf (lz L N r x) w r := by
      rcases Nat.eq_zero_or_pos (indexf (lz L N r x) w r) with h | h
      · exact absurd (Kepler.Text.Reduction4.indexf_eq_zero hzr hwr h).symm hwz
      · exact h
    have hlt_zw : indexf (lz L N r x) w r
        < indexf (lz L N r x) (Kepler.Text.Reduction5.ly L r x) r := by
      omega
    refine (Kepler.Text.TameSpine.indexfBetwnEq (Ne.symm hyz) hrnd hzr hyr).mpr
      ⟨?_, ?_⟩
    · rwa [← Kepler.Text.Reduction3.indexf_eq_spine (lz L N r x) w r]
    · rw [← Kepler.Text.Reduction3.indexf_eq_spine (lz L N r x) w r,
          ← Kepler.Text.Reduction3.indexf_eq_spine (lz L N r x)
            (Kepler.Text.Reduction5.ly L r x) r]
      exact hlt_zw

/-! ## §5 `rtrans 1` 拆分形 + Aq13 `next_mark_in_rtrans_suc` -/

/-- `rtrans L N r x 1` 的展开拆形（Reduction3Thm1.rtrans1 + splitNormalList +
`nextEl_prevEl` + `lyFindFaceEq`）：
`[l'z] ++ (betwn r l'z l'y ++ [l'y]) ++ betwn (find_face x) l'y l'z`。 -/
private theorem rtransOneEqSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    rtrans L N r x 1
      = [lz L N r x] ++ (between r (lz L N r x) (Kepler.Text.Reduction5.ly L r x)
          ++ [Kepler.Text.Reduction5.ly L r x])
        ++ between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
            (lz L N r x) := by
  rw [Kepler.Text.Reduction3.rtrans1 L N r x hf]
  have hzr : lz L N r x ∈ r :=
    (hqymrtx1List L hL hgn hunL hm hf (sListEqOfMarked L hL hm hf)).1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hstep : nextEl r (prevEl r (lz L N r x)) = lz L N r x :=
    Kepler.Text.TameLp.nextEl_prevEl hrnd hzr
  have hface : findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x :=
    lyFindFaceEq L hL hm
  simp only [Kepler.Text.Reduction5.splitNormalList, hstep, hface]

/-- **HOL `Aq13.next_mark_in_rtrans_suc`**（AQ13.hl:42）链层形：
`good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list ∧ find_face L x = f ∧
next_el f x = w ⇒ w ∈ rtrans L N r x 1`。 -/
theorem nextMarkInRtransSuc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart}
    (hfind : findFaceDarts L x = f) (hnext : nextEl f x = w) :
    w ∈ rtrans L N r x 1 := by
  have hcase := nextMarkCaseMem L hL hgn hunL hm hf hfind hnext
  have hdec := rtransOneEqSplit L hL hgn hunL hm hf
  rw [hdec]
  rcases hcase with h | h
  · rw [h]
    simp
  · simp only [List.mem_append]
    exact Or.inl (Or.inr (Or.inl h))

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.lYRepPowerLe
#print axioms Kepler.Text.Reduction4Idx.indexfConstLe
#print axioms Kepler.Text.Reduction4Idx.indexfYLeZInR0
#print axioms Kepler.Text.Reduction4Idx.nextMarkCaseMem
#print axioms Kepler.Text.Reduction4Idx.nextMarkInRtransSuc

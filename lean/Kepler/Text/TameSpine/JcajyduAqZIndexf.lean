/-
  Kepler.Text.TameSpine.JcajyduAqZIndexf — hsnd 批 1a（面几何早段）：
  indexf 交错族（HOL PPLHULJ3_v0 / indexf_ytrans_eq_l_m_v0 /
  indexf_ytrans_suc_lp_v0 及最小性件）。

  件目：
  ① `fListPowEqNextElPow`：fList 幂 ↔ nextEl(face) 幂在面轨道上一致；
  ② `indexfYtransEqLm`（HOL indexf_ytrans_eq_l_m_v0，HOJODCM.hl:224）：
     `indexf w (l'y) f = l'm`——l'y 幂表示（E1 lYRepPower + minNotEqImpEq）
     + nextElnIndexf + hypM_lt_face（hypermap 侧，标准三，经 hypMLm 传输
     + TameList56.cardFaceOfList 换 sizel）；
  ③ `fListPowYtransNotMem`（HOL f_list_power_ytrans_not_mem_v0，AQ1:235）：
     `j < l'p → f^{j+1} y ∉ r`（l'p 极小性直取）；
  ④ `indexfYtransSucLp`（HOL indexf_ytrans_suc_lp_v0，AQ1:284）：
     `indexf y z (find_face y) = l'p + 1`（z = f^{p+1} y 定义性 +
     nextElnIndexf + 三分叉：p+1 = sizel 支由周回排除（y=z 违 hyne）、
     p+1 > sizel 支由 ③ 在 PRE sizel 处排除、正常支直取）；
  ⑤ `pplhulj3V0`（HOL PPLHULJ3_v0，HOJODCM:204）：
     `indexf w y f < indexf w z f`——**比 HOL 窄的路线**：HOL 的
     idxOf-三分叉+分圆除法在 Lean 侧由 `hypZMemDartsOfSplit.2`
     （k∈[1,l'm+1] 的精确排除区间）直接消去：z = (nextEl f)^[i+1] x
     （i := indexf w z f，nextEln/indexfN 链）；若 i ≤ l'm 则
     i+1 ≤ l'm+1 与干净 HQYMRTX 排除矛盾；
  ⑥ `pplhuljV0`（HOL PPLHULJ_v0 包装）：y,z ∈ f ∧ 不等式。

  查重记账：HOL `ytran_me_f`/`mem_next_mark_inface` 已在
  `Kepler.Text.MoreLemma2a23.ytranMeF/memNextMarkInface`（j1w1，另一
  载体支线）——本文件不重落，仅在需要处引用 Spine 侧等价件。
  债账：本批零消费 TameList16:1095（HQYMRTX 排除用
  hypZMemDartsOfSplit.2 干净版；z ∈ face 用 b2 zMemFindFaceDarts）。

  纪律：零 sorry/admit/native_decide/axiom；主仓树零写入（经 patch 交付）。
-/
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqZUnlock

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem nextEl_eq_getD getD_eq_getElem_of_lt faceMap_hypermapOfList)
open Kepler.Text (orbitMap mem_orbitMap_self pow_apply_mem_orbitMap)

/-! ## §0 私件：nextEl 轨道基础 -/

/-- nextEl 迭代保成员（TameList3 私件同证重推导）。 -/
private theorem memNextElIterate' {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact nextEl_mem_of_mem ih

/-- `(a % n + 1) % n = (a + 1) % n`（模后继平移）。 -/
private theorem modSuccMod (a n : ℕ) : (a % n + 1) % n = (a + 1) % n := by
  have h : a + 1 = n * (a / n) + (a % n + 1) := by
    have := Nat.div_add_mod a n
    omega
  rw [h, Nat.add_comm (n * (a / n)), Nat.add_mul_mod_self_left]

/-- idxOf 沿 nextEl 迭代的模长平移：`idxOf ((nextEl s)^[k] x) = (idxOf x + k) % len`
（归纳 + J0-a idxOfNextElMod + modSuccMod）。 -/
private theorem idxOfNextElIterate {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hnd : s.Nodup) (hx : x ∈ s) :
    ∀ k : ℕ, s.idxOf ((nextEl s)^[k] x) = (s.idxOf x + k) % s.length := by
  intro k
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.add_zero,
      Nat.mod_eq_of_lt (List.idxOf_lt_length_iff.mpr hx)]
  | succ k ih =>
    rw [Function.iterate_succ_apply', idxOfNextElMod hnd (memNextElIterate' hx k), ih,
      ← Nat.add_assoc, modSuccMod]

/-- **周回**：`(nextEl s)^[s.length] y = y`（nodup + 成员；idxOf 模长回到
原点 + getElem_idxOf 拉直）。 -/
private theorem nextElPeriod {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {y : α} (hnd : s.Nodup) (hy : y ∈ s) :
    (nextEl s)^[s.length] y = y := by
  have hiylt : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hidx : s.idxOf ((nextEl s)^[s.length] y) = s.idxOf y := by
    rw [idxOfNextElIterate hnd hy]
    have h : s.idxOf y + s.length = s.length + s.idxOf y := Nat.add_comm _ _
    rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt hiylt]
  have hmem := memNextElIterate' hy s.length
  have hilt : s.idxOf ((nextEl s)^[s.length] y) < s.length :=
    List.idxOf_lt_length_iff.mpr hmem
  have hmid : s[s.idxOf ((nextEl s)^[s.length] y)]'hilt
      = s[s.idxOf y]'hiylt := by
    have h := congrArg (fun i => s.getD i y) hidx
    rwa [getD_eq_getElem_of_lt hilt, getD_eq_getElem_of_lt hiylt] at h
  calc (nextEl s)^[s.length] y
      = s[s.idxOf ((nextEl s)^[s.length] y)]'hilt :=
        (List.getElem_idxOf hilt).symm
    _ = s[s.idxOf y]'hiylt := hmid
    _ = y := List.getElem_idxOf hiylt

/-- **fList 幂 ↔ nextEl(face) 幂一致**：`(fList L)^[k] x = (nextEl f)^[k] x`
（f := findFaceDarts L x；归纳步经同面等表 congr + fList 定义）。 -/
theorem fListPowEqNextElPow (L : fgraph ℕ) (hL : GoodList L) (x : ℕ × ℕ)
    (hx : x ∈ findFaceDarts L x) :
    ∀ k : ℕ, (fList L)^[k] x = (nextEl (findFaceDarts L x))^[k] x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have hmem : (nextEl (findFaceDarts L x))^[k] x ∈ findFaceDarts L x :=
      memNextElIterate' hx k
    have hcongr : findFaceDarts L ((nextEl (findFaceDarts L x))^[k] x)
        = findFaceDarts L x :=
      findFaceDarts_congr_of_mem hL.1 (mem_darts_of_mem_findFace L hx) hmem
    show fList L (((nextEl (findFaceDarts L x))^[k]) x)
      = nextEl (findFaceDarts L x) (((nextEl (findFaceDarts L x))^[k]) x)
    rw [show fList L (((nextEl (findFaceDarts L x))^[k]) x)
        = nextEl (findFaceDarts L (((nextEl (findFaceDarts L x))^[k]) x))
            (((nextEl (findFaceDarts L x))^[k]) x) from rfl, hcongr]

/-! ## §1 indexfYtransEqLm（HOL indexf_ytrans_eq_l_m_v0） -/

/-- **HOL `indexf_ytrans_eq_l_m_v0`**（HOJODCM.hl:224）：
`indexf w (l'y) f = l'm`——`w = next_el f x`、`f = find_face L x`、
`l'y = ITER (SUC l'm) (next_el r) x`（E1 lYRepPower）经 minNotEqImpEq
换 fList 幂，nextElnIndexf 收口；界 `l'm < sizel f` 由 hypermap 侧
`hypM_lt_face`（标准三）经 `hypMLm`（l'm = hypM）与
`TameList56.cardFaceOfList`（face.ncard = sizel face）落地。 -/
theorem indexfYtransEqLm (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) (findFaceDarts L x)
      = lMSpine L r x := by
  have hnext := hm.1.2.2.2.2.2.1
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    nextEl_mem_of_mem hxx
  -- l'y = (fList L)^[l'm + 1] x
  have hyF : lYSpine L r x = (fList L)^[lMSpine L r x + 1] x := by
    have h1 : lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x :=
      lYRepPower L r x hnext.symm
    have h2 := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl
      (lMSpine L r x) (Nat.le_refl _)
    calc lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x := h1
      _ = (fList L)^[lMSpine L r x] (nextEl r x) := h2
      _ = (fList L)^[lMSpine L r x] (fList L x) := by rw [hnext]
      _ = (fList L)^[lMSpine L r x + 1] x :=
        (Function.iterate_succ_apply (fList L) (lMSpine L r x) x).symm
  -- l'y = (nextEl f)^[l'm] w
  have hyW : lYSpine L r x
      = (nextEl (findFaceDarts L x))^[lMSpine L r x] (nextEl (findFaceDarts L x) x) := by
    rw [hyF, fListPowEqNextElPow L hL x hxx (lMSpine L r x + 1)]
    show (nextEl (findFaceDarts L x))^[lMSpine L r x + 1] x
      = (nextEl (findFaceDarts L x))^[lMSpine L r x]
          (nextEl (findFaceDarts L x) x)
    rw [Function.iterate_succ_apply]
  -- 界：l'm < sizel f
  have hylt : lMSpine L r x < (findFaceDarts L x).length := by
    have hsc := markListSplitConditionList L hL hm.1 hf
    have hsplit := splitConditionListSplit L hL hgn hunL hsc
    have hM := hypMLm L hL hgn hunL hnext hsc
    have hlt := (hypermapOfList L hL).hypM_lt_face hsplit
    rw [hM] at hlt
    have hcard := cardFaceOfList L hL hxd
    rw [hcard] at hlt
    omega
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hyW ▸ memNextElIterate' hwf _
  exact nextElnIndexf hwf hyf (findFaceDarts_nodup hL.1 x) hyW.symm hylt

/-! ## §2 l'p 极小性（HOL f_list_power_ytrans_not_mem_v0） -/

/-- **HOL `f_list_power_ytrans_not_mem_v0`**（AQ1.hl:235）：
`j < l'p → (f_list POWER SUC j) (l'y) ∉ r`——l'p 的 min_num 极小性：
若落在 r 则落 flatten N，与 l'p 最小矛盾。 -/
theorem fListPowYtransNotMem (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    ∀ j : ℕ, j < lPSpine L N r x →
      (fList L)^[j + 1] (lYSpine L r x) ∉ r := by
  intro j hj hmem
  have hrN := hm.1.2.2.1
  have hfl : (fList L)^[j + 1] (lYSpine L r x) ∈ N.flatten :=
    List.mem_flatten.mpr ⟨r, hrN, hmem⟩
  have hle : lPSpine L N r x ≤ j := Nat.sInf_le hfl
  omega

/-! ## §3 indexfYtransSucLp（HOL indexf_ytrans_suc_lp_v0） -/

/-- **HOL `indexf_ytrans_suc_lp_v0`**（AQ1.hl:284）：
`indexf (l'y) (l'z) (find_face l'y) = SUC (l'p)`——z = f^{p+1} y（l'z
定义性）+ nextElnIndexf；界 p+1 < sizel：三分叉——等号支由周回
（f^{sizel} y = y，`nextElPeriod`）得 z = y 违 hyne；大于支由 §2 在
j = sizel - 1 处得 f^{sizel} y ∉ r 而它 = y ∈ r 矛盾。 -/
theorem indexfYtransSucLp (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L (lYSpine L r x))
      = lPSpine L N r x + 1 := by
  have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hyL1 : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L (lYSpine L r x)).mpr hyd
  have hzL1 : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hzdef : lZSpine L N r x = (fList L)^[lPSpine L N r x + 1] (lYSpine L r x) := rfl
  have hzW : lZSpine L N r x
      = (nextEl (findFaceDarts L (lYSpine L r x)))^[lPSpine L N r x + 1]
          (lYSpine L r x) := by
    rw [hzdef, fListPowEqNextElPow L hL (lYSpine L r x) hyL1 (lPSpine L N r x + 1)]
  -- 界：p + 1 < sizel L1
  have hple : lPSpine L N r x + 1 < (findFaceDarts L (lYSpine L r x)).length := by
    have hz1 : 1 ≤ (findFaceDarts L (lYSpine L r x)).length :=
      List.length_pos_of_mem hyL1
    have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
    have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
    rcases lt_trichotomy (lPSpine L N r x + 1) (findFaceDarts L (lYSpine L r x)).length
      with hlt | heq | hgt
    · exact hlt
    · -- p+1 = sizel：f^{sizel} y = y（周回）→ z = y，违 hyne
      exfalso
      have hper : (nextEl (findFaceDarts L (lYSpine L r x)))^[lPSpine L N r x + 1]
          (lYSpine L r x) = lYSpine L r x := by
        rw [heq]
        exact nextElPeriod (findFaceDarts_nodup hL.1 (lYSpine L r x)) hyL1
      rw [hper] at hzW
      exact hyne hzW.symm
    · -- sizel < p+1：§2 在 j = sizel-1 处矛盾
      exfalso
      have hj : (findFaceDarts L (lYSpine L r x)).length - 1 < lPSpine L N r x := by
        omega
      have hnot := fListPowYtransNotMem L hL hm
        ((findFaceDarts L (lYSpine L r x)).length - 1) hj
      apply hnot
      have h1 : ((findFaceDarts L (lYSpine L r x)).length - 1) + 1
          = (findFaceDarts L (lYSpine L r x)).length := by omega
      rw [h1, fListPowEqNextElPow L hL (lYSpine L r x) hyL1 _,
        nextElPeriod (findFaceDarts_nodup hL.1 (lYSpine L r x)) hyL1]
      exact hyr
  exact nextElnIndexf hyL1 hzL1 (findFaceDarts_nodup hL.1 (lYSpine L r x)) hzW.symm hple

/-! ## §4 PPLHULJ3_v0（HOL HOJODCM:204——Lean 窄路线） -/

/-- **HOL `PPLHULJ3_v0`**（HOJODCM.hl:204）：`indexf w y f < indexf w z f`。
Lean 路线比 HOL 窄：设 i := indexf w z f，nextEln/indexfN 给
z = (fList L)^[i+1] x；若 i ≤ l'm 则 i+1 ∈ [1, l'm+1]，与干净
HQYMRTX 排除（hypZMemDartsOfSplit.2 + hypZLz transport）矛盾——
省去 HOL 的 idxOf 三分叉与分圆除法。 -/
theorem pplhulj3V0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) (findFaceDarts L x)
      < indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) (findFaceDarts L x) := by
  have hnext := hm.1.2.2.2.2.2.1
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    nextEl_mem_of_mem hxx
  -- y ∈ f（fList 幂成员）
  have hyF : lYSpine L r x = (fList L)^[lMSpine L r x + 1] x := by
    have h1 : lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x :=
      lYRepPower L r x hnext.symm
    have h2 := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl
      (lMSpine L r x) (Nat.le_refl _)
    calc lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x := h1
      _ = (fList L)^[lMSpine L r x] (nextEl r x) := h2
      _ = (fList L)^[lMSpine L r x] (fList L x) := by rw [hnext]
      _ = (fList L)^[lMSpine L r x + 1] x :=
        (Function.iterate_succ_apply (fList L) (lMSpine L r x) x).symm
  have hyx : lYSpine L r x ∈ findFaceDarts L x := by
    rw [hyF, fListPowEqNextElPow L hL x hxx]
    exact memNextElIterate' hxx _
  -- z ∈ f
  have hzLy := zMemFindFaceDarts L hL hgn hunL hm hf
  have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 hxd hyx
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hcongr ▸ hzLy
  -- z = (fList L)^[i+1] x，i := indexf w z f
  set i := indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x)
    (findFaceDarts L x) with hidef
  have hzi : (nextEl (findFaceDarts L x))^[i] (nextEl (findFaceDarts L x) x)
      = lZSpine L N r x := indexfN hwf hzf hfnd
  have hcW : findFaceDarts L (nextEl (findFaceDarts L x) x) = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 (mem_darts_of_mem_findFace L hxx) hwf
  have hww : nextEl (findFaceDarts L x) x
      ∈ findFaceDarts L (nextEl (findFaceDarts L x) x) := by
    rw [hcW]; exact hwf
  have hzF : lZSpine L N r x = (fList L)^[i + 1] x := by
    have hwp : (nextEl (findFaceDarts L x))^[i] (nextEl (findFaceDarts L x) x)
        = (fList L)^[i] (nextEl (findFaceDarts L x) x) := by
      have hF' := fListPowEqNextElPow L hL (nextEl (findFaceDarts L x) x) hww i
      rw [hcW] at hF'
      exact hF'.symm
    rw [← hzi, hwp]
    have hwfl : nextEl (findFaceDarts L x) x = fList L x := rfl
    rw [hwfl, Function.iterate_succ_apply]
  -- 干净 HQYMRTX 排除：l'z ≠ f^k x（k ∈ [1, l'm+1]）
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have hsflag := markListSFlagged L hL hgn hunL hm hf
  have hedge : (hypermapOfList L hL).edgeMap x
      ∈ (hypermapOfList L hL).dartsInFinalLoops (loopFamilyOfListSpine N) :=
    markedListEdgeMapFinal hL hm.1
  have hq := Kepler.Text.Hypermap.hypZMemDartsOfSplit (H := hypermapOfList L hL)
    (hnf := normalListNormal hL hgn hm.1.1 hm.1.2.1)
    (NF := loopFamilyOfListSpine N) (L := loopOfListSpine r) (x := x)
    hsplit hsflag hedge
  have hzEq := hypZLz L hL hgn hunL hnext hsc
  -- faceMap 幂 = fList 幂（面轨道上）
  have hFMP : ∀ k : ℕ, ((hypermapOfList L hL).faceMap ^ k) x = (fList L)^[k] x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      have hmem : (fList L)^[k] x ∈ findFaceDarts L x :=
        fListPowEqNextElPow L hL x hxx k ▸ memNextElIterate' hxx k
      have hmd : (fList L)^[k] x ∈ listOfDarts L := mem_darts_of_mem_findFace L hmem
      rw [Function.iterate_succ_apply']
      show (hypermapOfList L hL).faceMap ((fList L)^[k] x) = fList L ((fList L)^[k] x)
      exact faceMap_hypermapOfList L hL (List.mem_toFinset.mpr hmd)
  have hzNe : ∀ k : ℕ, 1 ≤ k → k ≤ lMSpine L r x + 1 →
      lZSpine L N r x ≠ (fList L)^[k] x := by
    intro k hk1 hk2 hcon
    have hz2 : lZSpine L N r x = ((hypermapOfList L hL).faceMap ^ k) x := by
      rw [hcon, hFMP k]
    exact (hzEq ▸ hq.2 k hk1 (by rw [hypMLm L hL hgn hunL hnext hsc]; exact hk2)) hz2
  -- i ≤ l'm ⇒ 矛盾
  have hgt : lMSpine L r x < i := by
    rcases Nat.lt_or_ge i (lMSpine L r x + 1) with h | h
    · exfalso
      exact hzNe (i + 1) (by omega) (by omega) hzF
    · omega
  rw [indexfYtransEqLm L hL hgn hunL hm hf]
  exact hgt

/-! ## §5 PPLHULJ_v0（HOL HOJODCM:359 包装） -/

/-- **HOL `PPLHULJ_v0`**（HOJODCM.hl:359）：y,z ∈ f ∧ 不等式。 -/
theorem pplhuljV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lYSpine L r x ∈ findFaceDarts L x ∧
      lZSpine L N r x ∈ findFaceDarts L x ∧
      indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) (findFaceDarts L x)
        < indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) (findFaceDarts L x) := by
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hyF : lYSpine L r x = (fList L)^[lMSpine L r x + 1] x := by
    have h1 : lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x :=
      lYRepPower L r x hm.1.2.2.2.2.2.1.symm
    have h2 := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl
      (lMSpine L r x) (Nat.le_refl _)
    calc lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x := h1
      _ = (fList L)^[lMSpine L r x] (nextEl r x) := h2
      _ = (fList L)^[lMSpine L r x] (fList L x) := by rw [hm.1.2.2.2.2.2.1]
      _ = (fList L)^[lMSpine L r x + 1] x :=
        (Function.iterate_succ_apply (fList L) (lMSpine L r x) x).symm
  have hyx : lYSpine L r x ∈ findFaceDarts L x := by
    rw [hyF, fListPowEqNextElPow L hL x hxx]
    exact memNextElIterate' hxx _
  have hzLy := zMemFindFaceDarts L hL hgn hunL hm hf
  have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 hxd hyx
  exact ⟨hyx, hcongr ▸ hzLy, pplhulj3V0 L hL hgn hunL hm hf⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.fListPowEqNextElPow
#print axioms Kepler.Text.TameSpine.indexfYtransEqLm
#print axioms Kepler.Text.TameSpine.fListPowYtransNotMem
#print axioms Kepler.Text.TameSpine.indexfYtransSucLp
#print axioms Kepler.Text.TameSpine.pplhulj3V0
#print axioms Kepler.Text.TameSpine.pplhuljV0

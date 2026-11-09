/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12T — AQ12 叶 F3 首波（decls 55–58, 63, 66）。

  HOL：AQ12.hl:2907-:3085 + :3497-:3499 + :3618-:3642（170 行）
  · 55 `next_el_power_trans_eq_f_v0`（44）
  · 56 `s_list_subset_r`（37）
  · 57 `condition_s_list`（44）
  · 58 `next_mark_case_mem_v0`（54）
  · 63 `e_n_list`（3）
  · 66 `condition_last_parts`（25）

  ┌─ F3 拆分表（开工报价）────────────────────────────────────────
  │ W-F3a（本文件）：55, 56, 57, 58, 63, 66 —— 6 件 / 170 HOL / 估 ≤350。
  │ W-F3b（12U）：59 `s_list_in_betwn`(93) + 60 `s_list_in_rtrans`(22)
  │   + 61 `s_list_not_in_fst`(35) —— 3 件 / 150 HOL。
  │ W-F3c（12V）：62 `cat_fst_split_normal_parts`(261) 单列一泼。
  │ W-F3d（12W）：64 `next_s_list_eq_rtrans`(66) + 65 `power_next_s_list_eq_rtrans`(52)
  │   —— 2 件 / 118 HOL。
  │ 之后：decl 68 主证（444 HOL）。
  │ **F3 全段不吃 `h4`**（sList/parts/indexf 层，不涉及 split 行 loopList；
  │ 逐波以 #check 为准）。DIFFERS：F2 的 40/41/45/46/51/53/54 吃 h4。
  └────────────────────────────────────────────────────────────────

  陈述对表（命名方程代入）：HOL 的自由 `f/w/y/z/z1` 在本文件按具体项
  `findFaceDarts L x` / `nextEl f x` / `lYSpine` / `lZSpine` / `prevEl r (lZSpine)`
  实例化（decl 55/58 保留 `w` + 方程，与 HOL 同形；56/57 用具体 `w`）。
  `LAST` ↦ `getLast!`（非空时由 `getLast!EqGetLast` 折算）。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12S

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face)

/-- **HOL `next_el_power_trans_eq_f_v0`**（AQ12.hl:2907-:2950）：
沿 r 环从 `w = nextEl f x` 走 `n ≤ indexf w y r` 步，`nextEl r` 与 `nextEl f` 一致。 -/
theorem aqs_nextElPowerTransEqF (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {w : ℕ × ℕ} (hw : nextEl (findFaceDarts L x) x = w) {n : ℕ}
    (hn : n ≤ indexf w (lYSpine L r x) r) :
    (nextEl r)^[n] w = (nextEl (findFaceDarts L x))^[n] w := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hidx : indexf w (lYSpine L r x) r = lMSpine L r x := by
    rw [← hw]
    exact aq10_indexfYtransEqLm1 L hL hgn hm hf
  have hn' : n ≤ lMSpine L r x := by rw [← hidx]; exact hn
  have hxd : x ∈ listOfDarts L := normalListListOfDarts hm.1.2.1 x
    (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hstep : (nextEl r)^[n + 1] x = (fList L)^[n + 1] x := by
    have h1 := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl n hn'
    rw [h1, hm.1.2.2.2.2.2.1]
    exact (Function.iterate_succ_apply (fList L) n x).symm
  have hface : (fList L)^[n + 1] x = (nextEl (findFaceDarts L x))^[n + 1] x :=
    fListPowEqNextElPow L hL x hxx (n + 1)
  have hwr : w = nextEl r x := by
    rw [← hw, hm.1.2.2.2.2.2.1, fList]
  calc (nextEl r)^[n] w = (nextEl r)^[n] ((nextEl r) x) := by rw [hwr]
    _ = (nextEl r)^[n + 1] x := (Function.iterate_succ_apply (nextEl r) n x).symm
    _ = (fList L)^[n + 1] x := hstep
    _ = (nextEl (findFaceDarts L x))^[n + 1] x := hface
    _ = (nextEl (findFaceDarts L x))^[n] ((nextEl (findFaceDarts L x)) x) :=
        Function.iterate_succ_apply (nextEl (findFaceDarts L x)) n x
    _ = (nextEl (findFaceDarts L x))^[n] w := by rw [hw]

/-- **HOL `s_list_subset_r`**（AQ12.hl:2951-:2987）：`sList ⊆ r`。 -/
theorem aqs_sListSubsetR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ sListSpine L r x) : d ∈ r := by
  obtain ⟨i, hi, hie⟩ := List.mem_map.mp hd
  rw [List.mem_range] at hi
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hmin := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl i (by omega)
  have hEq : (nextEl r)^[i + 1] x = (fList L)^[i + 1] x := by
    rw [hmin, hm.1.2.2.2.2.2.1]
    exact (Function.iterate_succ_apply (fList L) i x).symm
  rw [← hie, ← hEq]
  exact memPowerNextEl hxr (i + 1)

/-- **HOL `condition_s_list`**（AQ12.hl:2988-:3031）：
`d ∈ r` 且 `indexf w d r < indexf w y r`（`w = nextEl f x`）⇒ `d ∈ sList`。 -/
theorem aqs_conditionSList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ r)
    (hlt : indexf (nextEl (findFaceDarts L x) x) d r
      < indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r) :
    d ∈ sListSpine L r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hwr : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  have hidx : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r = lMSpine L r x :=
    aq10_indexfYtransEqLm1 L hL hgn hm hf
  have hn : indexf (nextEl (findFaceDarts L x) x) d r < lMSpine L r x := by
    rw [← hidx]; exact hlt
  have hdEq : (nextEl r)^[indexf (nextEl (findFaceDarts L x) x) d r]
      (nextEl (findFaceDarts L x) x) = d := indexfN hwr hd hrnd
  have hpow := aqs_nextElPowerTransEqF L hL hgn hm hf
    (w := nextEl (findFaceDarts L x) x) rfl (le_of_lt (by rw [hidx]; exact hn))
  have hxx : x ∈ findFaceDarts L x :=
    (dart_in_face L x).mpr (normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩))
  have hfEq : (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) d r]
      (nextEl (findFaceDarts L x) x)
      = (fList L)^[indexf (nextEl (findFaceDarts L x) x) d r + 1] x := by
    rw [fListPowEqNextElPow L hL x hxx, Function.iterate_succ_apply]
  refine List.mem_map.mpr ⟨indexf (nextEl (findFaceDarts L x) x) d r, ?_, ?_⟩
  · rw [List.mem_range]; exact hn
  · rw [← hfEq, ← hpow]
    exact hdEq

/-- **HOL `next_mark_case_mem_v0`**（AQ12.hl:3032-:3085）：
`w = nextEl f x` 或等于 ytrans，或落在 `betwn r z y`。 -/
theorem aqs_nextMarkCaseMem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    w = lYSpine L r x ∨ w ∈ between r (lZSpine L N r x) (lYSpine L r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind]; exact hw
  have hwr : w ∈ r := by rw [← hw']; exact aq10_nextMarkMemRTrans L hL hgn hm
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hpp : indexf w (lYSpine L r x) r < indexf w (lZSpine L N r x) r := by
    have h := aq10_indexfYLeZInR0 L hL hgn hm hf
    rwa [hw'] at h
  by_cases h0 : indexf w (lYSpine L r x) r = 0
  · left
    exact indexfZeroEq hwr hyr h0
  · right
    have hpos_wy : 0 < indexf w (lYSpine L r x) r := Nat.pos_of_ne_zero h0
    have hwz : w ≠ lZSpine L N r x := by
      intro h
      rw [h, indexfRefl hzr] at hpp
      omega
    have hadd1 : indexf w (lYSpine L r x) r
        + indexf (lYSpine L r x) (lZSpine L N r x) r
        = indexf w (lZSpine L N r x) r :=
      indexfAddLeft hwr hyr hzr (le_of_lt hpp)
    have hanti1 : indexf w (lZSpine L N r x) r + indexf (lZSpine L N r x) w r
        = r.length := indexfAntisym hwr hzr hwz
    have hanti2 : indexf (lZSpine L N r x) (lYSpine L r x) r
        + indexf (lYSpine L r x) (lZSpine L N r x) r = r.length :=
      indexfAntisym hzr hyr (Ne.symm hyz)
    have hpos_zw : 0 < indexf (lZSpine L N r x) w r := by
      rcases Nat.eq_zero_or_pos (indexf (lZSpine L N r x) w r) with h | h
      · exfalso
        exact hwz (indexfZeroEq hzr hwr h).symm
      · exact h
    have hlt_zw : indexf (lZSpine L N r x) w r
        < indexf (lZSpine L N r x) (lYSpine L r x) r := by omega
    exact (indexfBetwnEq (Ne.symm hyz) hrnd hzr hyr).mpr ⟨hpos_zw, hlt_zw⟩

/-- **HOL `e_n_list`**（AQ12.hl:3497-3499）：`eList (nList d) = prevEl (findFace d) d`。 -/
theorem aqs_eListNList (L : fgraph ℕ) (d : ℕ × ℕ) :
    eList (nList L d) = prevEl (findFaceDarts L d) d := by
  rw [nList, eList_eList]

/-- **HOL `condition_last_parts`**（AQ12.hl:3618-:3642）：
part 内 `d` 的 r-后继离开 face ⟺ `d` 是该 part 的末元。 -/
theorem aqs_conditionLastParts (L : fgraph ℕ) {r p : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hrnd : r.Nodup) (hne : r ≠ []) (hp : p ∈ partsSpine L r) (hd : d ∈ p)
    (hlastr : d ≠ r.getLast!) :
    (¬(nextEl r d = fList L (eList d)) ↔ d = p.getLast!) := by
  have hpne : p ≠ [] := List.ne_nil_of_mem hd
  constructor
  · intro hcon
    by_contra hdne
    have h1 := partsNextUnlast L hrnd hne p hp d hd hdne
    have h2 := nextElPartsUnlast L hrnd hne hp hd hdne
    exact hcon (h2.trans h1)
  · intro heq
    exact partsNextLast L hrnd hne p hp d hd heq hlastr

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_nextElPowerTransEqF
#print axioms Kepler.Text.TameSpine.aqs_sListSubsetR
#print axioms Kepler.Text.TameSpine.aqs_conditionSList
#print axioms Kepler.Text.TameSpine.aqs_nextMarkCaseMem
#print axioms Kepler.Text.TameSpine.aqs_eListNList
#print axioms Kepler.Text.TameSpine.aqs_conditionLastParts

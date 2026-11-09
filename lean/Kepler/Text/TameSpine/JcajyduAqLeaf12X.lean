/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12X — AQ12 叶 W-F3d（decls 64–65）。

  HOL：AQ12.hl:3500-:3617（118 行）
  · 64 `next_s_list_eq_rtrans`（66）
  · 65 `power_next_s_list_eq_rtrans`（52）

  件目/依赖（开工报价）：2 件 / 1 文件；估 130–180（≤350）。依赖 57/59（已落）。
  **不吃 h4**。

  64 路线：`condition_s_list`（57）→ `sListInBetwn`（59）给 `d ∈ betwn r z y`；
  `rtrans 1 = canonical SND = (([z] ++ betwn r z y) ++ [y]) ++ new2`；
  三段降（`nextElCat1` ×2 / `nextElCatLast1`）；块尾 `d = betwn.getLast!` 支
  两边都 = y（`nextLastBetwn`）；非尾支 `nextEl (betwn) d = nextEl r d`
  （`aq10_nextElBetwnSame` + `aq10_eqMemNextElLast`）。
  **64 保持严格 `<`（`indexf w d < indexf w l'Y`），不放宽成 `≤`**。

  65 路线：**对 n 归纳**（`n ≤ l'm` 为陈述显式前提）：
  base `rfl`；step 用 64 于 `d = (nextEl r)^[n] w`，两条同成立前提
  `indexf w d = n`（`nextElnIndexf`）与 `indexf w d < l'm`（`aq10_indexfYtransEqLm1`）。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12W
import Kepler.Text.TameSpine.JcajyduAqLeaf12U
import Kepler.Text.TameSpine.JcajyduAqLeaf12E

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face mem_darts_of_mem_findFace
  findFaceDarts_nodup nextEl_mem_of_mem)

/-! ## §0 列表末元私件 -/

private theorem aq12x_getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

private theorem aq12x_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-! ## §1 HOL AQ12.hl:3500 `next_s_list_eq_rtrans` -/

/-- **HOL `next_s_list_eq_rtrans`**（AQ12.hl:3500-:3565）：
`d ∈ r` 且 `indexf w d < indexf w l'Y`（严格）⇒ `nextEl (rtrans 1) d = nextEl r d`。 -/
theorem aqs_nextSListEqRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ r)
    (hlt : indexf (nextEl (findFaceDarts L x) x) d r
      < indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r) :
    nextEl (rtransSpine L N r x 1) d = nextEl r d := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hzy : lZSpine L N r x ≠ lYSpine L r x := Ne.symm hyz
  let B := between r (lZSpine L N r x) (lYSpine L r x)
  let f2 := ([lZSpine L N r x] ++ B) ++ [lYSpine L r x]
  let new2 := between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
    (lZSpine L N r x)
  have hS : d ∈ sListSpine L r x := aqs_conditionSList L hL hgn hm hf hd hlt
  have hB : d ∈ B := aqs_sListInBetwn L hL hgn hm hf rfl rfl rfl hS
  have hBne : B ≠ [] := List.ne_nil_of_mem hB
  have hrtrans : rtransSpine L N r x 1
      = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2 := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
  have hsplitSND : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 = f2 ++ new2 := by
    simp only [splitNormalListSpine]
    rw [nextElPrevElUniq hrnd _]
  have hmemS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 :=
    sndMemRtran1 L hm.1.2.2.1 hf
  have hndS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2.Nodup :=
    uniqFlattenUniq _ (aq1 L hL N r x hgn hm) _ hmemS
  have hndS' : (f2 ++ new2).Nodup := by
    rw [← hsplitSND]
    exact hndS
  have hndF2 : f2.Nodup := (List.nodup_append.mp hndS').1
  have hndZB : ([lZSpine L N r x] ++ B).Nodup := by
    have h := (List.nodup_append.mp hndF2).1
    exact h
  have hdy : d ≠ lYSpine L r x := fun h => by
    have hyB : lYSpine L r x ∈ between r (lZSpine L N r x) (lYSpine L r x) := by
      have h' := hB
      rw [h] at h'
      exact h'
    exact notBetwn2 (s := r) (x := lZSpine L N r x) (z := lYSpine L r x) hrnd hyB
  have hF2last : f2.getLast! = lYSpine L r x := by
    dsimp only [f2]
    rw [aq12x_getLast!_append _ (by simp : ([lYSpine L r x] : List (ℕ × ℕ)) ≠ [])]
    simp
  have hZBlast : ([lZSpine L N r x] ++ B).getLast! = B.getLast! :=
    aq12x_getLast!_append _ hBne
  have hmemF2 : d ∈ f2 := by
    dsimp only [f2]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hB)))
  have hstep1 : nextEl (f2 ++ new2) d = nextEl f2 d :=
    nextElCat1 hndF2 hmemF2 (by rw [hF2last]; exact hdy)
  rw [hrtrans, hsplitSND, hstep1]
  by_cases hlastB : d = B.getLast!
  · -- 块尾：两边都 = y
    have hsd : ([lZSpine L N r x] ++ B).getLast! = d := hZBlast.trans hlastB.symm
    have hstep2 : nextEl f2 d = lYSpine L r x := by
      dsimp only [f2]
      have hcat := nextElCatLast1 (s := [lZSpine L N r x] ++ B)
        (t := [lYSpine L r x]) hndF2 (by simp) (by simp)
      rw [← hsd]
      exact hcat.trans (by simp)
    have hlastE : d = B.getLast hBne :=
      hlastB.trans (aq12x_getLast!_eq_getLast hBne)
    have hnextr : nextEl r d = lYSpine L r x := by
      rw [hlastE]
      exact nextLastBetwn hzr hyr hrnd hzy hBne
    exact hstep2.trans hnextr.symm
  · -- 非尾：三段降到 nextEl r d
    have hstep2 : nextEl f2 d = nextEl ([lZSpine L N r x] ++ B) d := by
      dsimp only [f2]
      exact nextElCat1 hndZB (List.mem_append.mpr (Or.inr hB))
        (by rw [hZBlast]; exact hlastB)
    have hstep3 : nextEl ([lZSpine L N r x] ++ B) d = nextEl B d :=
      nextElCat2 hndZB hB hlastB
    have hnextB : nextEl r d ∈ B :=
      (aq10_eqMemNextElLast hzy hzr hyr hB hrnd).mpr
        (fun h => hlastB (h.symm.trans (aq12x_getLast!_eq_getLast hBne).symm))
    have hstep4 : nextEl B d = nextEl r d :=
      aq10_nextElBetwnSame hzy hzr hyr hB hnextB hrnd
    exact hstep2.trans (hstep3.trans hstep4)

/-! ## §2 HOL AQ12.hl:3566 `power_next_s_list_eq_rtrans` -/

/-- **HOL `power_next_s_list_eq_rtrans`**（AQ12.hl:3566-:3617）：
`n ≤ l'm` ⇒ `(nextEl (rtrans 1))^n w = (nextEl r)^n w`（`w = nextEl f x`）。 -/
theorem aqs_powerNextSListEqRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ n : ℕ, n ≤ lMSpine L r x →
      (nextEl (rtransSpine L N r x 1))^[n] (nextEl (findFaceDarts L x) x)
        = (nextEl r)^[n] (nextEl (findFaceDarts L x) x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hwr : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  have hiy : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r = lMSpine L r x :=
    aq10_indexfYtransEqLm1 L hL hgn hm hf
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ lMSpine L r x := by omega
    have hd : (nextEl r)^[k] (nextEl (findFaceDarts L x) x) ∈ r := memPowerNextEl hwr k
    have hklen : k < r.length := by
      have h1 : lMSpine L r x ≤ indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r :=
        le_of_eq hiy.symm
      have h2 := indexfLtSizel hwr hyr
      omega
    have hidx : indexf (nextEl (findFaceDarts L x) x)
        ((nextEl r)^[k] (nextEl (findFaceDarts L x) x)) r = k :=
      nextElnIndexf hwr hd hrnd rfl hklen
    have hlt : indexf (nextEl (findFaceDarts L x) x)
        ((nextEl r)^[k] (nextEl (findFaceDarts L x) x)) r
        < indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r := by
      rw [hidx, hiy]
      omega
    have hstep := aqs_nextSListEqRtrans L hL hgn hm hf hd hlt
    rw [Function.iterate_succ_apply' (nextEl (rtransSpine L N r x 1)) k
        (nextEl (findFaceDarts L x) x),
      Function.iterate_succ_apply' (nextEl r) k (nextEl (findFaceDarts L x) x)]
    rw [ih hk']
    exact hstep

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_nextSListEqRtrans
#print axioms Kepler.Text.TameSpine.aqs_powerNextSListEqRtrans

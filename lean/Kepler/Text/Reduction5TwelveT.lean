/-
  Kepler.Text.Reduction5TwelveT — W2-c-1b 收口：AQ12 两件链孪生
  （`next_el_power_trans_eq_f_v0` AQ12.hl:2907 / `condition_last_parts` AQ12.hl:3618）。

  ┌─ 账目对表（编排者 2026-11-11 派单；「以 DELIVERY_W2C1A 的账为准」）──
  │ 派单括注的三个名（mem_cat_betwn_same :1769 / LAST_cat_betwn_same :1840 /
  │ cat_betwn_same :1941）与本树账不符（AQ12.hl 仅 :4011 处出现
  │ `Aq8.next_cat_betwn_same` 消费者引用）；按派单指示以 W2C-1b 余二账为准：
  │ 本文件 = `nextElPowerTransEqFv0` + `conditionLastParts` 两件。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（链侧；零 TameSpine import）────────────────────────────
  │ ① `conditionLastParts`：HOL 证体两引理合成——`parts_next_unlast`
  │    ↦ `MoreLemma2PartsFst.partsNextUnlast`、`parts_next_last` ↦
  │    `MoreLemma2QuotientAlt.partsNextLast`、`next_el_parts_unlast` ↦
  │    `MoreLemma2Island3.nextElPartsUnlast`（均已在库）。
  │ ② `nextElPowerTransEqFv0`：HOL 的 Aq7/indexf 双引路线换成
  │    `indexfYtransEqLM1Core`（indexf w (l'y) r = l'm）+
  │    `lYRepPowerLe`（f_list 幂 = next_el r 幂，j ≤ l'm）+ 迭代代数
  │    （`iterate_add_apply`）+ `fListPowEqNextElPow`（f 侧幂桥）——
  │    比 HOL 短，免 indexf_lt_sizel/MEM_POWER_NEXT_EL/indexf_const_le 三件。
  └────────────────────────────────────────────────────────────────

  **纪律**：零占位证明、零新增公理、零反射式判定；主仓双零写入。禁词零。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2QuotientAlt
import Kepler.Text.MoreLemma2a23
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.PwssratTail
import Kepler.Text.PwssratCase
import Kepler.Text.PwssratFace

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (nextEl fList eList listOfDarts findFaceDarts GoodList)

/-- **HOL `Aq12.condition_last_parts`**（AQ12.hl:3618）：`p ∈ parts L r ∧ d ∈ p ∧
d ≠ LAST r ∧ r ≠ [] ∧ uniq r ⇒ (¬(next_el r d = f_list L (e_list d)) ⇔ d = LAST p)`。
合成 = `partsNextUnlast`（d 非末 ⇒ next_el p d = f_list）+ `nextElPartsUnlast`
（next_el r d = next_el p d）+ `partsNextLast`（d = 末且非 r 末 ⇒ ≠）。 -/
theorem conditionLastParts {L : fgraph ℕ} {r p : List Dart} {d : Dart}
    (hp : p ∈ parts L r) (hd : d ∈ p) (hdlast : d ≠ r.getLast!)
    (hne : r ≠ []) (hnd : r.Nodup) :
    (¬ (nextEl r d = fList L (eList d))) ↔ d = p.getLast! := by
  constructor
  · intro hb
    by_contra hdl
    exact hb ((Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hnd hne hp hd hdl).trans
      (Kepler.Text.MoreLemma2PartsFst.partsNextUnlast L hnd hne p hp d hd hdl))
  · intro hdl
    exact Kepler.Text.MoreLemma2QuotientAlt.partsNextLast L hnd hne p hp d hd hdl hdlast

/-- **HOL `Aq12.next_el_power_trans_eq_f_v0`**（AQ12.hl:2907）：
`good_list L ∧ good_list_nodes L ∧ AQIUNPP 槽 ∧ marked_list L N r x ∧
¬final_list L r ∧ next_el (find_face L x) x = w ∧
n ≤ indexf w (ytrans L N r x 0) r ⇒ (next_el r)^n w = (next_el (find_face L x))^n w`。
（HOL 前提的 `transform_assumption_v2` 按本树 Pwssrat 簇惯例以 `AqiunppSlot`
显式槽供给——链侧 `aqiunpp` 经 `JcajyduRed2Tav2` 桥即可填。） -/
theorem nextElPowerTransEqFv0 {L : fgraph ℕ} {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r)
    {w : Dart} (hnext : nextEl (findFaceDarts L x) x = w)
    {n : ℕ} (hn : n ≤ indexf w (ytrans L N r x 0) r) :
    (nextEl r)^[n] w = (nextEl (findFaceDarts L x))^[n] w := by
  -- w = f_list x（fList 定义级）
  have hwx : w = fList L x := hnext.symm
  -- w ∈ find_face x
  have hwf : w ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.memNextMarkInface L hL hm rfl hnext.symm
  -- indexf 桥：indexf w (l'y) r = l'm 且 ytrans 0 = l'y
  have hy_eq : ytrans L N r x 0 = Kepler.Text.Reduction5.ly L r x := by
    simp [Kepler.Text.Reduction5.ytrans, Kepler.Text.Reduction5.rtrans_zero]
  have hn_lm0 : n ≤ indexf w (Kepler.Text.Reduction5.ly L r x) r := by
    rwa [hy_eq] at hn
  have hn_lm : n ≤ Kepler.Text.Reduction5.lm L r x := by
    rw [hnext.symm] at hn_lm0
    rw [Kepler.Text.Reduction4Idx.indexfYtransEqLM1Core L hL hm hf] at hn_lm0
    exact hn_lm0
  -- l'y 幂桥
  have hpow := Kepler.Text.Reduction4Idx.lYRepPowerLe L r x
    (hm.2.2.2.2.2.1.symm)
  -- w = (next_el r)^1 x
  have hw1 : w = (nextEl r)^[1] x := by
    rw [hwx, Function.iterate_one]
    simpa [Function.iterate_one] using hpow 0 (Nat.zero_le _)
  -- 左端 = (next_el r)^(n+1) x
  have hlhs : (nextEl r)^[n] w = (nextEl r)^[n + 1] x := by
    rw [hw1]
    exact (Function.iterate_add_apply (nextEl r) n 1 x).symm
  -- f 侧幂桥（在 w 处）
  have hff : findFaceDarts L w = findFaceDarts L x :=
    Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm) hwf
  have hw_self : w ∈ findFaceDarts L w := by
    rw [hff]
    exact hwf
  have hF : (fList L)^[n] w = (nextEl (findFaceDarts L x))^[n] w := by
    have h1 := Kepler.Text.Reduction4Idx.fListPowEqNextElPow L hL hw_self n
    rwa [hff] at h1
  calc (nextEl r)^[n] w = (nextEl r)^[n + 1] x := hlhs
    _ = (fList L)^[n + 1] x := (hpow n hn_lm).symm
    _ = (fList L)^[n] (fList L x) := by
        rw [Function.iterate_add_apply, Function.iterate_one]
    _ = (fList L)^[n] w := by rw [hwx]
    _ = (nextEl (findFaceDarts L x))^[n] w := hF

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三） -/
#print axioms Kepler.Text.Reduction5.conditionLastParts
#print axioms Kepler.Text.Reduction5.nextElPowerTransEqFv0

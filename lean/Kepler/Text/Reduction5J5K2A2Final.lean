/-
  Kepler.Text.Reduction5J5K2A2Final — Lane A2.1 收官（nb48）：
  强形 `hmisc`（`z0` 持久性）+ `final_assumption_yz_in_core` 无条件形。

  ┌─ 归属对账（HOL reduction4.hl）────────────────────────────────────
  │ ① `indexfZtransLtFindFace` = `More_lemma2.indexf_ztrans_lt_find_face`
  │    （more_lemma2.hl:1801–1829）：`indexf w z0 f ≤ indexf w zi f`
  │    （`i < transform_count`）。证 = `qcdvkeaTowerI` + `pplhulj3V0`
  │    逐步链（HOL 同款归纳，base rfl）。
  │ ② `finalReductionMemZ0Ri` = `final_reduction_mem_z0_ri`
  │    （reduction4.hl:3753–3791，754 HOL 行的**结论**）：
  │    `i < transform_count ⇒ ztrans 0 ∈ rtrans i`。证 = 对 i 归纳，
  │    base `lzMemR`，step `ncvibwuTowerI`（塔层 NCVIBWU）+ `indexfN`。
  │    **不搬 HOL 754 行证体**——用已落 `ncvibwuTowerI`（`Reduction3ChainTower`）
  │    一步塔层实例化。
  │ ③ `hmiscStrong`：把 ② 包装成 `yz_in_core` 所需的强形 `hmisc`
  │    （∀ N' r' i'，K1Asm ⇒ z0 ∈ rtrans i'）。
  │ ④ `finalAssumptionYzInCoreUncond`：nb47 条件形 + ③，A2.1 **无条件收官**。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5J5K2A2
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.PwssratFace
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)

/-- **HOL `More_lemma2.indexf_ztrans_lt_find_face`**（more_lemma2.hl:1801–1829，
`≤` 形）：`findFace L x = f`、`nextEl f x = w`、`i < transform_count`
⇒ `indexf w z0 f ≤ indexf w zi f`。

证 = `qcdvkeaTowerI`（`zi → y(i+1)`）+ `pplhulj3V0`（`y(i+1) < z(i+1)`）
逐步链；HOL 同款对 i 归纳，base `le_refl`。 -/
theorem indexfZtransLtFindFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    ∀ i : ℕ, i < transformCount L N r x →
      Kepler.Text.TameSpine.indexf w (ztrans L N r x 0) f
        ≤ Kepler.Text.TameSpine.indexf w (ztrans L N r x i) f
  | 0, _ => Nat.le_refl _
  | i + 1, hlt => by
    have hlt_i : i < transformCount L N r x := by omega
    have hIH := indexfZtransLtFindFace L hL hgn hres haq hm hnf hfind hw i hlt_i
    have hnf_i1 : ¬ finalList L (rtrans L N r x (i + 1)) :=
      Kepler.Text.Reduction4.transformCount_not (i + 1) hlt
    have h1 := Kepler.Text.TameSpine.qcdvkeaTowerI L hL hgn haq i hm hnf_i1 hfind hw
    have hunL : ∀ l ∈ L, l.Nodup :=
      Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
    have hm_i1 : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x (i + 1)) (rtrans L N r x (i + 1)) x :=
      haq hgn N r x hm (i + 1)
    have h2 := Kepler.Text.Reduction4Idx.pplhulj3V0 L hL hgn hunL hm_i1 hnf_i1
    rw [hfind, hw] at h2
    rw [Kepler.Text.Reduction3.indexf_eq_spine,
      Kepler.Text.Reduction3.indexf_eq_spine] at h2
    exact le_trans hIH (le_trans h1 (le_of_lt h2))

/-- **HOL `final_reduction_mem_z0_ri`**（reduction4.hl:3753–3791）：
`i < transform_count ⇒ ztrans L N r x 0 ∈ rtrans L N r x i`。

证 = 对 i 归纳：base `lzMemR`（`rtrans 0 = r`）；step 用
`ncvibwuTowerI`（塔层 NCVIBWU，`Reduction3ChainTower:88`）于
`j = indexf w z0 f`（界由 `indexfZtransLtFindFace`），再 `indexfN`
把 `(nextEl f)^j w` 折回 `z0`。 -/
theorem finalReductionMemZ0Ri (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k) :
    ∀ i : ℕ, i < k → ztrans L N r x 0 ∈ rtrans L N r x i
  | 0, _ => by
    rw [rtrans_zero]
    exact Kepler.Text.Reduction5.lzMemR hL hgn
      (Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres) haq hm hnf
  | i + 1, hlt => by
    have hlt_i : i < k := by omega
    have hIH := finalReductionMemZ0Ri L hL hgn hres haq hm hnf hk i hlt_i
    have hlt_tc : i < transformCount L N r x := by rw [hk]; exact hlt_i
    have hnf_i : ¬ finalList L (rtrans L N r x i) :=
      Kepler.Text.Reduction4.transformCount_not i hlt_tc
    -- 基本结构件
    have hunL : ∀ l ∈ L, l.Nodup :=
      Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
    have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
    have hxf : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hx
    have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
      Kepler.Text.TameLp.nextEl_mem_of_mem hxf
    have hfnd : (findFaceDarts L x).Nodup :=
      Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
    have hz0f : ztrans L N r x 0 ∈ findFaceDarts L x :=
      Kepler.Text.Reduction4Idx.lzMemFindFaceDarts L hL hm
    -- 界：indexf w z0 f ≤ indexf w zi f
    have hj := indexfZtransLtFindFace L hL hgn hres haq hm hnf rfl rfl i hlt_tc
    -- 塔层 NCVIBWU
    have h := Kepler.Text.TameSpine.ncvibwuTowerI L hL hgn haq i hm hnf_i rfl rfl
      (j := Kepler.Text.TameSpine.indexf (nextEl (findFaceDarts L x) x)
        (ztrans L N r x 0) (findFaceDarts L x)) hj
    -- (nextEl f)^j w = z0
    have hz0 : (nextEl (findFaceDarts L x))^[
        Kepler.Text.TameSpine.indexf (nextEl (findFaceDarts L x) x)
          (ztrans L N r x 0) (findFaceDarts L x)]
        (nextEl (findFaceDarts L x) x) = ztrans L N r x 0 :=
      Kepler.Text.TameSpine.indexfN hwf hz0f hfnd
    have h' := h
    rw [hz0] at h'
    exact h'.1

/-- 强形 `hmisc`（`yz_in_core` 的前提）：任意 K1Asm 态 `(N', r')` 与
`i' < transform_count`，`z0` 都在 `rtrans i'` 里。
直接由 `finalReductionMemZ0Ri` 在 `k' := transformCount L N' r' x` 处实例化。 -/
theorem hmiscStrong (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k) :
    ∀ (N' : List (List Dart)) (r' : List Dart) (i' : ℕ),
      i' < transformCount L N' r' x → Kepler.Text.ChainLists.markedList L hL N' r' x →
      Kepler.Text.Reduction3.newvertexPrepped L N' r' x → ¬ finalList L r' →
      Kepler.Text.Reduction3.elementPre L N' →
      ztrans L N' r' x 0 ∈ rtrans L N' r' x i' :=
  fun N' r' i' hlt hm' _ hnf' _ =>
    finalReductionMemZ0Ri L hL hgn hres haq hm' hnf' rfl i' hlt

/-- **HOL `final_assumption_yz_in_core` 无条件形**（reduction4.hl:727–794）：
nb47 条件形 + `hmiscStrong` 一行代入。**A2.1 收官件。** -/
theorem finalAssumptionYzInCoreUncond (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (hnvp0 : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep0 : Kepler.Text.Reduction3.elementPre L N) :
    ∀ i j : ℕ, 0 < i → i < k → j < k →
      (ytrans L N r x j).1 ∈ core L (rtrans L N r x i) ∧
      (ztrans L N r x j).1 ∈ core L (rtrans L N r x i) :=
  finalAssumptionYzInCore L hL hgn hres haq hm hnf hk hnvp0 hep0
    (hmiscStrong L hL hgn hres haq hm hnf hk)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.indexfZtransLtFindFace
#print axioms Kepler.Text.Reduction5.finalReductionMemZ0Ri
#print axioms Kepler.Text.Reduction5.hmiscStrong
#print axioms Kepler.Text.Reduction5.finalAssumptionYzInCoreUncond

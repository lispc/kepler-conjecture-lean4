/-
  Kepler.Text.Reduction5Ml1W5a — 8b W5a（T1+T2 链形 + `indexfZtransLt`）
  （HOL DIOWAAS.hl / RYIUUVK.hl / more_lemma1.hl:868–:913）。

  件目：链形 lengYtransZtransConst / lengYtransWConst / lengZtransWConst（T1）、
  diowaasR / ryiuuvkR（T2）、indexfZtransLt（T3 = W5a）。
  路线：spine 证体（Reduction5Ml1W5Spine）+ `spineInputs` 桥（Pnxvwfs 模式）+ 端点
  ytrans/ztrans/rtrans 链↔spine 等式 + `indexf_eq_spine`。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5Ml1W5Spine
import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction4
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)
open Kepler.Text.TameSpine (ntransSpine rtransSpine ytransSpine ztransSpine finalListSpine
  MarkedListSpineFull lYSpine lZSpine)

/-- 第 i 状态非 final ⇒ 初始状态非 final（同 Pnxvwfs 私件）。 -/
private theorem w5NotFinalBase (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : ∀ i, ¬ finalList L (rtrans L N r x i) → ¬ finalList L r
  | 0, h => h
  | i + 1, h => w5NotFinalBase L N r x i (finalListInduct i h)

/-- chain marked + 第 i 状态非 final ⇒ spine 侧全套入参（Pnxvwfs `spineInputs` 同体）。 -/
private theorem w5SpineInputs (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hnfi : ¬ finalList L (rtrans L N r x i)) (hm : markedList L hL N r x) :
    (∀ l ∈ L, l.Nodup) ∧ MarkedListSpineFull hL N r x ∧
      ntrans L N r x i = ntransSpine L N r x i ∧
      rtrans L N r x i = rtransSpine L N r x i ∧
      ¬ finalListSpine L (rtransSpine L N r x i) := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hf : ¬ finalList L r := w5NotFinalBase L N r x i hnfi
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hf
  have hrt : rtrans L N r x i = rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
  refine ⟨hunL,
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm,
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i, hrt, ?_⟩
  rw [← hrt]
  exact fun h => hnfi ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mpr h)

/-- 链 `AqiunppSlot`（无条件；`aqu` 逐点）。 -/
private theorem w5AqSlot (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
  fun hgn N r x hm i => Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i

/-- `ytrans i = ytransSpine i`（第 i 状态非 final）。 -/
private theorem w5YtransEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ytrans L N r x i = ytransSpine L N r x i := by
  have hf0 : ¬ finalList L r := w5NotFinalBase L N r x i hf
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hrt : rtrans L N r x i = rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL (w5AqSlot L hL) hm i
  have hly : Kepler.Text.Reduction5.ly L (rtrans L N r x i) x
      = lYSpine L (rtrans L N r x i) x :=
    Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL (w5AqSlot L hL hgn N r x hm i) hf
  show Kepler.Text.Reduction5.ly L (rtrans L N r x i) x
    = lYSpine L (rtransSpine L N r x i) x
  rw [hly, hrt]

/-- `ztrans i = ztransSpine i`（第 i 状态非 final）。 -/
private theorem w5ZtransEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ztrans L N r x i = ztransSpine L N r x i := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hrt : rtrans L N r x i = rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL (w5AqSlot L hL) hm i
  have hnt : ntrans L N r x i = ntransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL (w5AqSlot L hL) hm i
  have hlz : lz L (ntrans L N r x i) (rtrans L N r x i) x
      = lZSpine L (ntrans L N r x i) (rtrans L N r x i) x :=
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL (w5AqSlot L hL hgn N r x hm i) hf
  show lz L (ntrans L N r x i) (rtrans L N r x i) x
    = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
  rw [hlz, hnt, hrt]

/-! ## §1 T1 链形（r↔rtrans 转移包） -/

/-- **T1-a 链形（HOL `leng_ytrans_ztrans_const`）**：
`indexf (l'y(i)) (l'z(i)) r_i = indexf (l'y(i)) (l'z(i)) r`。 -/
theorem lengYtransZtransConst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    indexf (ytrans L N r x i) (ztrans L N r x i) (rtrans L N r x i)
      = indexf (ytrans L N r x i) (ztrans L N r x i) r := by
  obtain ⟨hunL, hmS, -, hrt, hfS⟩ := w5SpineInputs L hL hgn (w5AqSlot L hL) i hf hm
  have hy := w5YtransEq L hL hgn hm i hf
  have hz := w5ZtransEq L hL hgn hm i hf
  rw [hy, hz, hrt, Kepler.Text.Reduction3.indexf_eq_spine,
    Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.lengYtransZtransConstSpine L hL
    (transformAssumptionSpineOfAqiunpp L hL (w5AqSlot L hL)) hgn hunL hmS i hfS

/-- **T1-b 链形（HOL `leng_ytrans_w_const`）**：
`indexf (l'y(i)) w r_i = indexf (l'y(i)) w r`。 -/
theorem lengYtransWConst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i))
    {w : Dart} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf (ytrans L N r x i) w (rtrans L N r x i)
      = indexf (ytrans L N r x i) w r := by
  obtain ⟨hunL, hmS, -, hrt, hfS⟩ := w5SpineInputs L hL hgn (w5AqSlot L hL) i hf hm
  have hy := w5YtransEq L hL hgn hm i hf
  rw [hy, hrt, Kepler.Text.Reduction3.indexf_eq_spine,
    Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.lengYtransWConstSpine L hL
    (transformAssumptionSpineOfAqiunpp L hL (w5AqSlot L hL)) hgn hunL hmS i hfS hw

/-- **T1-c 链形（HOL `leng_ztrans_w_const`）**：
`indexf (l'z(i)) w r_i = indexf (l'z(i)) w r`。 -/
theorem lengZtransWConst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i))
    {w : Dart} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf (ztrans L N r x i) w (rtrans L N r x i)
      = indexf (ztrans L N r x i) w r := by
  obtain ⟨hunL, hmS, -, hrt, hfS⟩ := w5SpineInputs L hL hgn (w5AqSlot L hL) i hf hm
  have hz := w5ZtransEq L hL hgn hm i hf
  rw [hz, hrt, Kepler.Text.Reduction3.indexf_eq_spine,
    Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.lengZtransWConstSpine L hL
    (transformAssumptionSpineOfAqiunpp L hL (w5AqSlot L hL)) hgn hunL hmS i hfS hw

/-! ## §2 T2 链形（r 侧两不等式） -/

/-- **T2-a 链形（HOL `DIOWAAS`）**：r 侧 `indexf w y_i r < indexf w z_i r`。 -/
theorem diowaasR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i))
    {w : Dart} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf w (ytrans L N r x i) r < indexf w (ztrans L N r x i) r := by
  have hf0 : ¬ finalList L r := w5NotFinalBase L N r x i hf
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hf0
  have hmS : MarkedListSpineFull hL N r x :=
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
  have hfS : ¬ finalListSpine L (rtransSpine L N r x i) := by
    have hrt : rtrans L N r x i = rtransSpine L N r x i :=
      Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL (w5AqSlot L hL) hm i
    rw [← hrt]
    exact fun h => hf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mpr h)
  have hy := w5YtransEq L hL hgn hm i hf
  have hz := w5ZtransEq L hL hgn hm i hf
  rw [hy, hz, Kepler.Text.Reduction3.indexf_eq_spine,
    Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.diowaasRSpine L hL
    (transformAssumptionSpineOfAqiunpp L hL (w5AqSlot L hL)) hgn hunL hmS i hfS hw

/-- **T2-b 链形（HOL `RYIUUVK`）**：r 侧 `indexf w z_i r ≤ indexf w y_{i+1} r`。 -/
theorem ryiuuvkR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x (i + 1)))
    {w : Dart} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf w (ztrans L N r x i) r ≤ indexf w (ytrans L N r x (i + 1)) r := by
  have hf0 : ¬ finalList L r := w5NotFinalBase L N r x (i + 1) hf
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hf0
  have hmS : MarkedListSpineFull hL N r x :=
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
  have hrt : rtrans L N r x (i + 1) = rtransSpine L N r x (i + 1) :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL (w5AqSlot L hL) hm (i + 1)
  have hfS : ¬ finalListSpine L (rtransSpine L N r x (i + 1)) := by
    rw [← hrt]
    exact fun h => hf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mpr h)
  have hzi : ¬ finalList L (rtrans L N r x i) := finalListInduct i hf
  have hz := w5ZtransEq L hL hgn hm i hzi
  have hy := w5YtransEq L hL hgn hm (i + 1) hf
  rw [hz, hy, Kepler.Text.Reduction3.indexf_eq_spine,
    Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.ryiuuvkRSpine L hL
    (transformAssumptionSpineOfAqiunpp L hL (w5AqSlot L hL)) hgn hunL hmS i hfS hw

/-! ## §3 T3 = W5a：`indexfZtransLt`（HOL more_lemma1.hl:868–:913） -/

/-- 单步：`indexf w z_k r < indexf w z_{k+1} r`（`k+1 < transform_count`）。 -/
private theorem indexfZtransStep (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (k : ℕ)
    (hk : k + 1 < transformCount L N r x)
    {w : Dart} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf w (ztrans L N r x k) r < indexf w (ztrans L N r x (k + 1)) r := by
  have hnf1 : ¬ finalList L (rtrans L N r x (k + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (k + 1) hk
  have hry := ryiuuvkR L hL hgn hm k hnf1 hw
  have hdi := diowaasR L hL hgn hm (k + 1) hnf1 hw
  exact lt_of_le_of_lt hry hdi

/-- **W5a（HOL `indexf_ztrans_lt`，more_lemma1.hl:868–:913）**：
`0 < i ∧ i < transform_count ⇒ indexf w z_0 r < indexf w z_i r`。 -/
theorem indexfZtransLt (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {f : List Dart} {w : Dart}
    (hfind : findFaceDarts L x = f) (hwf : nextEl f x = w) :
    ∀ i, 0 < i → i < transformCount L N r x →
      indexf w (ztrans L N r x 0) r < indexf w (ztrans L N r x i) r := by
  have hw : nextEl (findFaceDarts L x) x = w := by rw [hfind]; exact hwf
  intro i
  induction i with
  | zero => intro h0 _; omega
  | succ k ih =>
      intro h0 hlt
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact indexfZtransStep L hL hgn hm 0 hlt hw
      · have hprev : indexf w (ztrans L N r x 0) r < indexf w (ztrans L N r x k) r :=
          ih hkpos (by omega)
        exact lt_trans hprev (indexfZtransStep L hL hgn hm k hlt hw)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.lengYtransZtransConst
#print axioms Kepler.Text.Reduction5.lengYtransWConst
#print axioms Kepler.Text.Reduction5.lengZtransWConst
#print axioms Kepler.Text.Reduction5.diowaasR
#print axioms Kepler.Text.Reduction5.ryiuuvkR
#print axioms Kepler.Text.Reduction5.indexfZtransLt

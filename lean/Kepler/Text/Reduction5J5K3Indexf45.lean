/-
  Kepler.Text.Reduction5J5K3Indexf45 — K3 Lane B2
  （more_lemma2.hl:1833 indexf4_final_lemmas / :1946 indexf5_final_lemmas）。

  陈述逐字对 HOL（`find_face ↦ findFaceDarts`、`SUC i ↦ i + 1`）。
  `transform_assumption_v2_lemma`/`AQIUNPP3` 类槽由在库 `aqiunpp` 逐点供给
  （`aqSlotOf`），故陈述保持 HOL 的五前提、不另加 `haq`。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1
import Kepler.Text.PwssratFace
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §0 私有供料 -/

/-- `AqiunppSlot` 的无条件实例（`aqiunpp` 逐点；HOL `AQIUNPP3` 槽）。 -/
private theorem aqSlotOf (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
  fun hgn N r x hm i => Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i

/-- 一般 `i` 的 PPLHULJ3（f 世界）：`indexf w y_i f < indexf w z_i f`。 -/
private theorem pplhulj3Gen (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x i) (findFaceDarts L x)
      < indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i) (findFaceDarts L x) := by
  have hm_i : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have h := Kepler.Text.Reduction4Idx.pplhulj3V0 L hL hgn hunL hm_i hf
  simpa only [Kepler.Text.Reduction5.ytrans, Kepler.Text.Reduction5.ztrans] using h

/-- `ztrans` 沿塔单调（w 序，f 世界）：`indexf w z_0 f ≤ indexf w z_i f`。 -/
private theorem indexfZtransLeGen (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    ∀ i, i < transformCount L N r x →
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x 0) (findFaceDarts L x)
        ≤ indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i) (findFaceDarts L x) := by
  intro i
  induction i with
  | zero => intro _; exact Nat.le_refl _
  | succ i ih =>
    intro hlt
    have hlt_i : i < transformCount L N r x := by omega
    have hIH := ih hlt_i
    have hnf_i1 : ¬ finalList L (rtrans L N r x (i + 1)) :=
      Kepler.Text.Reduction4.transformCount_not (i + 1) hlt
    have h1 := qcdvkeaChain L hL hgn i hm hnf_i1
      (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x) rfl rfl
    have h2 := pplhulj3Gen L hL hgn hm (i + 1) hnf_i1
    exact le_trans hIH (le_trans h1 (le_of_lt h2))

/-- `ytrans` 沿塔单调（w 序，f 世界）：`indexf w y_0 f ≤ indexf w y_i f`。 -/
private theorem indexfYtransLeGen (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    ∀ i, i < transformCount L N r x →
      indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x)
        ≤ indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x i) (findFaceDarts L x) := by
  intro i
  induction i with
  | zero => intro _; exact Nat.le_refl _
  | succ i ih =>
    intro hlt
    have hlt_i : i < transformCount L N r x := by omega
    have hIH := ih hlt_i
    have hnf_i : ¬ finalList L (rtrans L N r x i) :=
      Kepler.Text.Reduction4.transformCount_not i hlt_i
    have hnf_i1 : ¬ finalList L (rtrans L N r x (i + 1)) :=
      Kepler.Text.Reduction4.transformCount_not (i + 1) hlt
    have h1 := pplhulj3Gen L hL hgn hm i hnf_i
    have h2 := qcdvkeaChain L hL hgn i hm hnf_i1
      (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x) rfl rfl
    exact le_trans hIH (le_trans (le_of_lt h1) h2)

/-! ## §1 `indexf4_final_lemmas`（more_lemma2.hl:1833-1910） -/

/-- HOL `indexf4_final_lemmas`（more_lemma2.hl:1833）：
`good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ transform_count = k ⇒
∀ i, i+1 < k ⇒ indexf (y_0) (z_i) f ≤ indexf (y_0) (y_{i+1}) f`。 -/
theorem indexf4FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hk : transformCount L N r x = k) :
    ∀ i, i + 1 < k →
      indexf (ytrans L N r x 0) (ztrans L N r x i) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x) := by
  intro i hi
  -- finality
  have hf0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  have hf : ¬ finalList L r := by
    rwa [Kepler.Text.Reduction5.rtrans_zero] at hf0
  have hf_i1 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1) (by rw [hk]; omega)
  -- memberships in f
  have hxd : x ∈ findFaceDarts L x := by
    have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hx
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    Kepler.Text.TameLp.nextEl_mem_of_mem hxd
  have hy0f : ytrans L N r x 0 ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl 0
  have hzif : ztrans L N r x i ∈ findFaceDarts L x :=
    Kepler.Text.TameSpine.ztranMeFChain L hL hgn (aqSlotOf L hL) hm i
  have hyif : ytrans L N r x (i + 1) ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl (i + 1)
  -- w 序
  have hy0_lt_z0 : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
      (findFaceDarts L x) <
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x 0) (findFaceDarts L x) :=
    pplhulj3Gen L hL hgn hm 0 hf0
  have hz0_le_zi : indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x 0)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i) (findFaceDarts L x) :=
    indexfZtransLeGen L hL hgn hm hf i (by rw [hk]; omega)
  have hzi_le_yi : indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x (i + 1)) (findFaceDarts L x) :=
    qcdvkeaChain L hL hgn i hm hf_i1
      (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x) rfl rfl
  have hy0_le_zi : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i) (findFaceDarts L x) :=
    le_trans (le_of_lt hy0_lt_z0) hz0_le_zi
  have hy0_le_yi : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x (i + 1)) (findFaceDarts L x) :=
    le_trans hy0_le_zi hzi_le_yi
  -- indexf_add_left 平移两个端点
  have e1 := Kepler.Text.Reduction4.indexf_add_left hwf hy0f hzif hy0_le_zi
  have e2 := Kepler.Text.Reduction4.indexf_add_left hwf hy0f hyif hy0_le_yi
  omega

/-! ## §2 `indexf5_final_lemmas`（more_lemma2.hl:1946-1995） -/

/-- HOL `indexf5_final_lemmas`（more_lemma2.hl:1946）：
`good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ transform_count = k ⇒
∀ i, i+1 < k ⇒ indexf (y_0) (y_{i+1}) f ≤ indexf (y_0) (z_{i+1}) f`。 -/
theorem indexf5FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hk : transformCount L N r x = k) :
    ∀ i, i + 1 < k →
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) (findFaceDarts L x) := by
  intro i hi
  -- finality
  have hf0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  have hf : ¬ finalList L r := by
    rwa [Kepler.Text.Reduction5.rtrans_zero] at hf0
  have hf_i1 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1) (by rw [hk]; omega)
  -- memberships in f
  have hxd : x ∈ findFaceDarts L x := by
    have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hx
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    Kepler.Text.TameLp.nextEl_mem_of_mem hxd
  have hy0f : ytrans L N r x 0 ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl 0
  have hyif : ytrans L N r x (i + 1) ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl (i + 1)
  have hzif : ztrans L N r x (i + 1) ∈ findFaceDarts L x :=
    Kepler.Text.TameSpine.ztranMeFChain L hL hgn (aqSlotOf L hL) hm (i + 1)
  -- w 序
  have hy0_lt_z0 : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
      (findFaceDarts L x) <
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x 0) (findFaceDarts L x) :=
    pplhulj3Gen L hL hgn hm 0 hf0
  have hy0_le_yi : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x (i + 1)) (findFaceDarts L x) :=
    indexfYtransLeGen L hL hgn hm hf (i + 1) (by rw [hk]; omega)
  have hz0_le_zi : indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x 0)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (i + 1)) (findFaceDarts L x) :=
    indexfZtransLeGen L hL hgn hm hf (i + 1) (by rw [hk]; omega)
  have hy0_le_zi : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
      (findFaceDarts L x) ≤
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (i + 1)) (findFaceDarts L x) :=
    le_trans (le_of_lt hy0_lt_z0) hz0_le_zi
  have hyi_lt_zi : indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x (i + 1))
      (findFaceDarts L x) <
      indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (i + 1)) (findFaceDarts L x) :=
    pplhulj3Gen L hL hgn hm (i + 1) hf_i1
  -- indexf_add_left 平移三个端点
  have e1 := Kepler.Text.Reduction4.indexf_add_left hwf hy0f hyif hy0_le_yi
  have e2 := Kepler.Text.Reduction4.indexf_add_left hwf hy0f hzif hy0_le_zi
  omega

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction5.indexf4FinalLemmas
#print axioms Kepler.Text.Reduction5.indexf5FinalLemmas

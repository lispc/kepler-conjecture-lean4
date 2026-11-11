/-
  Kepler.Text.TameSpine.Reduction3J5IndexfSizeZTranPre — tame-corr nb31：J5-6
  `indexf_size_ztran_pre`（HOL betwn_corek_z_x.hl:128，body 90 行）。

  陈述（HOL 逐字）：
  `good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧
   transform_count = k ∧ 0<k ∧ ¬(FST (ztrans (PRE k)) = FST x)
   ⇒ indexf (ztrans (PRE k)) (next_el (find_face L x) x) (find_face L x) < sizel r`。

  路线（HOL 同构，换成链侧在库引擎）：
  - `ztrans (k-1) ∈ r` ← `pnxvwfs2`（AqiunppSlot 局部由 `aqiunpp` 无条件供出）；
  - `ztrans (k-1) ∈ f`、`w = next_el f x ∈ f`、`f.Nodup`；
  - `cases2Chain`：n ≤ indexf zk w f 时 r-弧与 f-弧重合 ⇒ 各幂迭代 ∈ r；
  - 幂迭代在 [0, indexf zk w f] 上单射（`nextElnIndexf` 定位）；
  - 基数收口：`card_image_of_injOn` + `card_le_card` + `cardLeSize`
    ⇒ `indexf zk w f + 1 ≤ |r|` ⇒ `< |r|`。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.Reduction4
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart ztrans transformCount)

/-- **HOL `indexf_size_ztran_pre`**（betwn_corek_z_x.hl:128）。 -/
theorem indexfSizeZTranPre (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1) :
    Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1))
      (nextEl (findFaceDarts L x) x) (findFaceDarts L x) < r.length := by
  -- AQIUNPP 槽：由 `aqiunpp` 无条件供出（陈述保持 HOL 七前提形，不额外加槽）
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  set f : List Dart := findFaceDarts L x with hf
  set w : Dart := nextEl f x with hw
  set zk : Dart := ztrans L N r x (k - 1) with hz
  -- 结构件
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxf : x ∈ f := by
    rw [hf]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hx
  have hwf : w ∈ f := by
    rw [hw]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hfnd : f.Nodup := by
    rw [hf]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hzkf : zk ∈ f := by
    rw [hz, hf]
    exact Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm (k - 1)
  have hzkr : zk ∈ r := by
    rw [hz]
    exact Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq (k - 1)
      (Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)) hm
  have hilt : Kepler.Text.Reduction5.indexf zk w f < f.length :=
    Kepler.Text.Reduction4.indexf_lt_length_of_mem hzkf hwf
  -- CASES2：r-弧与 f-弧在 [0, indexf zk w f] 上重合
  have hcongr : ∀ n, n ≤ Kepler.Text.Reduction5.indexf zk w f →
      (nextEl r)^[n] zk = (nextEl f)^[n] zk := by
    intro n hn
    exact Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm
      (f := f) (w := w) hf.symm hw.symm hk hk0 hn
  -- 幂迭代成员
  have hmemIter : ∀ n, (nextEl f)^[n] zk ∈ f := fun n =>
    Kepler.Text.TameSpine.memPowerNextEl hzkf n
  -- 单射：`nextElnIndexf` 把每个迭代点定位回其指数
  have hinj : ∀ n1 ∈ Finset.range (Kepler.Text.Reduction5.indexf zk w f + 1),
      ∀ n2 ∈ Finset.range (Kepler.Text.Reduction5.indexf zk w f + 1),
      (nextEl f)^[n1] zk = (nextEl f)^[n2] zk → n1 = n2 := by
    intro n1 h1 n2 h2 heq
    simp only [Finset.mem_range] at h1 h2
    have h1le : n1 ≤ Kepler.Text.Reduction5.indexf zk w f := by omega
    have h2le : n2 ≤ Kepler.Text.Reduction5.indexf zk w f := by omega
    have e1 : Kepler.Text.Reduction5.indexf zk ((nextEl f)^[n1] zk) f = n1 := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact Kepler.Text.TameSpine.nextElnIndexf hzkf (hmemIter n1) hfnd rfl (by omega)
    have e2 : Kepler.Text.Reduction5.indexf zk ((nextEl f)^[n2] zk) f = n2 := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact Kepler.Text.TameSpine.nextElnIndexf hzkf (hmemIter n2) hfnd rfl (by omega)
    rw [heq] at e1
    omega
  -- 像集 ⊆ r
  have hsub : (Finset.range (Kepler.Text.Reduction5.indexf zk w f + 1)).image
        (fun n => (nextEl f)^[n] zk) ⊆ r.toFinset := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    simp only [Finset.mem_range] at hn
    have hnr : (nextEl r)^[n] zk ∈ r :=
      Kepler.Text.TameSpine.memPowerNextEl hzkr n
    rw [← hcongr n (by omega)]
    exact List.mem_toFinset.mpr hnr
  -- 基数收口
  have hinjOn : Set.InjOn (fun n => (nextEl f)^[n] zk)
      ↑(Finset.range (Kepler.Text.Reduction5.indexf zk w f + 1)) := by
    intro n1 h1 n2 h2 heq
    exact hinj n1 (Finset.mem_coe.mp h1) n2 (Finset.mem_coe.mp h2) heq
  have hcard : ((Finset.range (Kepler.Text.Reduction5.indexf zk w f + 1)).image
        (fun n => (nextEl f)^[n] zk)).card
      = Kepler.Text.Reduction5.indexf zk w f + 1 := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
  have hle : Kepler.Text.Reduction5.indexf zk w f + 1 ≤ r.length := by
    calc Kepler.Text.Reduction5.indexf zk w f + 1
        = ((Finset.range (Kepler.Text.Reduction5.indexf zk w f + 1)).image
            (fun n => (nextEl f)^[n] zk)).card := hcard.symm
      _ ≤ r.toFinset.card := Finset.card_le_card hsub
      _ ≤ r.length := Kepler.Text.MoreLemma2Island1.cardLeSize r
  omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.indexfSizeZTranPre

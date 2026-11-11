/-
  Kepler.Text.Reduction5J5K3Indexf678 — K3 Lane B3
  （more_lemma2.hl:1996 indexf6 / :2061 indexf7 / :2172 indexf8）。

  陈述逐字对 HOL（`PRE k ↦ k-1`、`next_el ↦ nextEl`、`find_face ↦ findFaceDarts`、`FST ↦ .1`）。
  B2 的 `aqSlotOf`/`pplhulj3Gen`/`indexfZtransLeGen` 为 private，本文件内重建（不改已落库文件）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1
import Kepler.Text.Reduction5J5K2A2Final
import Kepler.Text.PwssratFace
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction5Kbwpbhq

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §0 私有供料（B2 同形重建） -/

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

/-- `w = nextEl f x` 时 `w ≠ x`（否则 `r = [x]` 且 `finalList L r`）。 -/
private theorem nextElNeSelfOfMarked (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    nextEl (findFaceDarts L x) x ≠ x := by
  intro hwx
  have hxr : x ∈ r := hm.2.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hnext : nextEl r x = x := hm.2.2.2.2.2.1.trans hwx
  have hnext' : @nextEl Dart (instBEqOfDecidableEq) r x = x :=
    (Kepler.Text.Reduction5.nextElInstEq r x) ▸ hnext
  have hr_eq : r = [x] := Kepler.Text.MoreLemma2Island1.nextElRefl hxr hnext' hrnd
  have hfin : finalList L r := by
    rw [hr_eq]
    intro d hd
    rw [List.mem_singleton] at hd
    subst d
    show fList L x = nextEl [x] x
    have h1 : fList L x = x := by
      have h2 : fList L x = nextEl (findFaceDarts L x) x := rfl
      exact h2.trans hwx
    rw [h1]
    simp [Kepler.Assembly.nextEl]
  exact hnf hfin

/-! ## §1 `indexf6_final_lemmas`（more_lemma2.hl:1996-2060） -/

/-- HOL `indexf6_final_lemmas`（more_lemma2.hl:1996）：
五前提 + `0 < k` ⇒ `indexf w z_{k-1} f ≤ indexf w x f`。 -/
theorem indexf6FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hk : transformCount L N r x = k) (hk0 : 0 < k) :
    indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) x (findFaceDarts L x) := by
  set w : Dart := nextEl (findFaceDarts L x) x with hwdef
  set f : List Dart := findFaceDarts L x with hfdef
  have hf0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  have hf : ¬ finalList L r := by
    rwa [Kepler.Text.Reduction5.rtrans_zero] at hf0
  have hkm1 : k - 1 < k := by omega
  have hfkm1 : ¬ finalList L (rtrans L N r x (k - 1)) :=
    Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; exact hkm1)
  have hxd : x ∈ f := by
    have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
    rw [hfdef]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hx
  have hwf : w ∈ f := by
    rw [hwdef, hfdef]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxd
  have hzkf : ztrans L N r x (k - 1) ∈ f := by
    rw [hfdef]
    exact Kepler.Text.TameSpine.ztranMeFChain L hL hgn (aqSlotOf L hL) hm (k - 1)
  have hfnd : f.Nodup := by
    rw [hfdef]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  by_cases hzero : indexf w (ztrans L N r x (k - 1)) f = 0
  · rw [hzero]
    exact Nat.zero_le _
  · have hwzk : w ≠ ztrans L N r x (k - 1) := by
      intro h
      apply hzero
      rw [h]
      exact Kepler.Text.Reduction4.indexfRefl hzkf
    have hwz : ztrans L N r x (k - 1) ≠ w := fun h => hwzk h.symm
    have hzkw : indexf (ztrans L N r x (k - 1)) w f ≠ 0 := by
      intro h0
      exact hwz (Kepler.Text.Reduction4.indexf_eq_zero hzkf hwf h0)
    have hwx : w ≠ x := by
      intro h
      rw [hwdef] at h
      exact nextElNeSelfOfMarked L hL hm hf h
    have hwxn : x ≠ w := fun h => hwx h.symm
    have hanti1 : indexf w (ztrans L N r x (k - 1)) f +
        indexf (ztrans L N r x (k - 1)) w f = f.length :=
      Kepler.Text.Reduction5.indexfCompl hwf hzkf hwzk
    have hanti2 : indexf w x f + indexf x w f = f.length :=
      Kepler.Text.Reduction5.indexfCompl hwf hxd hwx
    have hlt := Kepler.Text.Reduction5.indexfLtSizel hwf hzkf
    have hlt1 : 1 < f.length := by omega
    have hnextf : @nextEl Dart (instBEqOfDecidableEq) f x = w :=
      (Kepler.Text.Reduction5.nextElInstEq f x) ▸ (show @nextEl Dart instBEqProd f x = w from by
        rw [hwdef, hfdef])
    have hif1 : indexf x w f = 1 :=
      Kepler.Text.MoreLemma2Island1.nextElIndexf hxd hwf hfnd hnextf hlt1
    omega

/-! ## §2 `indexf7_final_lemmas`（more_lemma2.hl:2061-2119） -/

/-- HOL `indexf7_final_lemmas`（more_lemma2.hl:2061）：
五前提 + `0 < k` ⇒ `indexf w y_0 f ≤ indexf w z_{k-1} f`。 -/
theorem indexf7FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hk : transformCount L N r x = k) (hk0 : 0 < k) :
    indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x) := by
  have hf0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  have hf : ¬ finalList L r := by
    rwa [Kepler.Text.Reduction5.rtrans_zero] at hf0
  have hkm1 : k - 1 < k := by omega
  have hy0_lt_z0 := pplhulj3Gen L hL hgn hm 0 hf0
  have hz0_le_zk := indexfZtransLeGen L hL hgn hm hf (k - 1) (by rw [hk]; exact hkm1)
  exact le_trans (le_of_lt hy0_lt_z0) hz0_le_zk

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction5.indexf6FinalLemmas
#print axioms Kepler.Text.Reduction5.indexf7FinalLemmas

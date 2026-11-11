/-
  Kepler.Text.Reduction5J5K3Indexf678 — K3 Lane B3
  （more_lemma2.hl:1996 indexf6 / :2061 indexf7 / :2172 indexf8）。

  陈述逐字对 HOL（`PRE k ↦ k-1`、`next_el ↦ nextEl`、`find_face ↦ findFaceDarts`、`FST ↦ .1`）。
  B2 的 `aqSlotOf`/`pplhulj3Gen`/`indexfZtransLeGen` 为 private，本文件内重建（不改已落库文件）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1
import Kepler.Text.Reduction5J7W1d
import Kepler.Text.Reduction5J7W2c
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5J5K2A2Final
import Kepler.Text.PwssratFace
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.Reduction3J5PowerCoreFace
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizel
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.Reduction5McCore
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

/-! ## §1.5 私有件 `indexfFaceOfLe`（HOL `indexf1_final_lemmas_face`，more_lemma2.hl:2120-2168） -/

/-- `ytrans` 在子状态 0 处退化回原状态（定义级）。 -/
private theorem ytransSubStateZero (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (i : ℕ) :
    ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0 = ytrans L N r x i := rfl

/-- `indexf w (ytrans 0) f = indexf w (ytrans 0) r`
（HOL `indexf_ytrans_eq_l_m` + `indexf_ytrans_eq_l_m1` 同态；与 `dMemROfSetup` 内联同式）。 -/
private theorem indexfYtransZeroEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf w (ytrans L N r x 0) f = indexf w (ytrans L N r x 0) r := by
  have hwr : w = nextEl r x := by
    rw [← hw, ← hfind]
    exact hm.2.2.2.2.2.1.symm
  have hf1 : indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x)
      (findFaceDarts L x) = Kepler.Text.Reduction5.lm L r x :=
    Kepler.Text.Reduction4Idx.indexfYtransEqLm L hL hgn hunL hm hnf
  have hr1 : indexf w (ytrans L N r x 0) r = Kepler.Text.Reduction5.lm L r x := by
    have h := Kepler.Text.Reduction4Idx.indexfYtransEqLM1 L hL haq hgn 0 hm hnf
      (w := w) (by rw [Kepler.Text.Reduction5.rtrans_zero]; exact hwr.symm)
    simpa only [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.rtrans_zero] using h
  have hf1' : indexf w (ytrans L N r x 0) f = Kepler.Text.Reduction5.lm L r x := by
    rw [← hw, ← hfind]
    exact hf1
  rw [hf1', hr1]

/-- **HOL `indexf1_final_lemmas_face`**（more_lemma2.hl:2120-2168）：
`d ∈ find_face L x` 且 `indexf w d f ≤ indexf w (ytrans 0) f`
⇒ `indexf (FST w) (FST d) (core L r) = indexf w d f`（`w = next_el f x`、`f = find_face L x`）。 -/
private theorem indexfFaceOfLe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x d : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hd : d ∈ findFaceDarts L x)
    (hle : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x)
      ≤ indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x)) :
    indexf (nextEl (findFaceDarts L x) x).1 d.1 (core L r)
      = indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL := aqSlotOf L hL
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  set f : List Dart := findFaceDarts L x with hfdef
  set w : Dart := nextEl f x with hwdef
  have hxf : x ∈ f := by
    rw [hfdef]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hwf : w ∈ f := by
    rw [hwdef]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hdf : d ∈ f := by rw [hfdef]; exact hd
  have hfnd : f.Nodup := by
    rw [hfdef]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hle' : indexf w d f ≤ indexf w (ytrans L N r x 0) f := by
    simpa [← hfdef, ← hwdef] using hle
  have hdr : d ∈ r :=
    Kepler.Text.Reduction5.dMemROfSetup L hL hgn hres haq hm hnf
      (hfind := hfdef.symm) (hw := hwdef.symm) hdf hle'
  have hwr : w ∈ r := by
    have hwr' : w = nextEl r x := by
      rw [hwdef, hfdef]
      exact hm.2.2.2.2.2.1.symm
    rw [hwr']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hm.2.2.2.1
  have hwcore : w.1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hwr hnf
  have hdcore : d.1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hdr hnf
  have hcund : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hy0eq : indexf w (ytrans L N r x 0) f = indexf w (ytrans L N r x 0) r :=
    indexfYtransZeroEq L hL hgn hunL haq hm hnf hfdef.symm hwdef.symm
  have hbound : indexf w d f < (core L r).length := by
    have h1 : indexf w (ytrans L N r x 0) r < (core L r).length :=
      Kepler.Text.TameSpine.indexfYltSizel L hL hgn haq hm hnf
        (f := f) (w := w) hfdef.symm hwdef.symm
    omega
  have hpow1 : (nextEl (core L r))^[indexf w d f] w.1
      = ((nextEl f)^[indexf w d f] w).1 :=
    Kepler.Text.TameSpine.nextPowerCoreWFace L hL hgn haq hm hnf
      (f := f) (w := w) hfdef.symm hwdef.symm (n := indexf w d f) hle'
  have hpowf : (nextEl f)^[indexf w d f] w = d := by
    rw [Kepler.Text.Reduction5.iterateInstEq f w (indexf w d f)]
    exact Kepler.Text.MoreLemma2Island1.indexfN hwf hdf hfnd
  have hpow : (nextEl (core L r))^[indexf w d f] w.1 = d.1 := by
    rw [hpow1, hpowf]
  exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hwcore hdcore hcund hpow hbound

/-! ## §3 `indexf8_final_lemmas`（more_lemma2.hl:2172-2288） -/

/-- HOL `indexf8_final_lemmas`（more_lemma2.hl:2172）逐字：
`∀ i, 0 < i ∧ i < k →` 两个 core 上的 `nextEl` 邻接断言等价（`PRE i ↦ i-1`）。 -/
theorem indexf8FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hk : transformCount L N r x = k) :
    ∀ i, 0 < i ∧ i < k →
      (nextEl (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 ↔
        nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1) := by
  intro i hi
  obtain ⟨hi0, hik⟩ := hi
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL := aqSlotOf L hL
  have hk0 : 0 < k := by omega
  have hf : ¬ finalList L r := by
    have hf0 : ¬ finalList L (rtrans L N r x 0) :=
      Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
    rwa [Kepler.Text.Reduction5.rtrans_zero] at hf0
  have hf_i : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  have hf_im1 : ¬ finalList L (rtrans L N r x (i - 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i - 1) (by rw [hk]; omega)
  have hm_i : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i
  set f : List Dart := findFaceDarts L x with hfdef
  set w : Dart := nextEl f x with hwdef
  set zp : Dart := ztrans L N r x (i - 1) with hzpdef
  set yi : Dart := ytrans L N r x i with hyidef
  have hxf : x ∈ f := by
    rw [hfdef]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hwf : w ∈ f := by
    rw [hwdef]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hzpf : zp ∈ f := by
    rw [hzpdef, hfdef]
    exact Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm (i - 1)
  have hyif : yi ∈ f := by
    rw [hyidef, hfdef]
    exact Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl i
  have hfnd : f.Nodup := by
    rw [hfdef]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have he : i - 1 + 1 = i := by omega
  -- QCDVKEA @ i-1：`indexf w zp f ≤ indexf w yi f`
  have hface_le : indexf w zp f ≤ indexf w yi f := by
    have h := qcdvkeaChain L hL hgn (i - 1) hm (by simpa [he] using hf_i)
      (f := f) (w := w) hfdef.symm hwdef.symm
    simpa [he, ← hzpdef, ← hyidef] using h
  -- `indexf w zp f > 0`（PPLHULJ3 @ i-1 的上界）
  have hBpos : 0 < indexf w zp f := by
    have h := pplhulj3Gen L hL hgn hm (i - 1) hf_im1
    rw [← hzpdef] at h
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have hwz : w ≠ zp := by
    intro h
    have h0 : indexf w zp f = 0 := by
      rw [h]
      exact Kepler.Text.Reduction4.indexfRefl hzpf
    omega
  -- state-i 侧 f 世界不等式（子状态 ytrans 0 = yi）
  have hstate_le : indexf (nextEl (findFaceDarts L x) x) zp (findFaceDarts L x)
      ≤ indexf (nextEl (findFaceDarts L x) x)
          (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0) (findFaceDarts L x) := by
    simpa [← hwdef, ← hfdef, ← hyidef, ytransSubStateZero L N r x i] using hface_le
  have hyi_le : indexf (nextEl (findFaceDarts L x) x) yi (findFaceDarts L x)
      ≤ indexf (nextEl (findFaceDarts L x) x)
          (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0) (findFaceDarts L x) := by
    simp [← hwdef, ← hfdef, ← hyidef, ytransSubStateZero L N r x i]
  -- state-i 侧两枚 core↔f 换算
  have hface_zp : indexf w.1 zp.1 (core L (rtrans L N r x i)) = indexf w zp f := by
    have h := indexfFaceOfLe L hL hgn hres (N := ntrans L N r x i)
      (r := rtrans L N r x i) (x := x) (d := zp) hm_i hf_i hzpf hstate_le
    simpa [← hwdef, ← hfdef] using h
  have hface_yi : indexf w.1 yi.1 (core L (rtrans L N r x i)) = indexf w yi f := by
    have h := indexfFaceOfLe L hL hgn hres (N := ntrans L N r x i)
      (r := rtrans L N r x i) (x := x) (d := yi) hm_i hf_i hyif hyi_le
    simpa [← hwdef, ← hfdef] using h
  -- state-i 侧成员：w、zp、yi 的 FST 都在 core_i
  have hw_ri : w ∈ rtrans L N r x i := by
    have hwr' : w = nextEl (rtrans L N r x i) x := by
      rw [hwdef, hfdef]
      exact hm_i.2.2.2.2.2.1.symm
    rw [hwr']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hm_i.2.2.2.1
  have hw_ci : w.1 ∈ core L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm_i hw_ri hf_i
  have hpow_zp_i : (nextEl (core L (rtrans L N r x i)))^[indexf w zp f] w.1 = zp.1 := by
    have h1 := Kepler.Text.TameSpine.nextPowerCoreWFace L hL hgn haq hm_i hf_i
      (f := f) (w := w) hfdef.symm hwdef.symm (n := indexf w zp f) hstate_le
    have h2 : (nextEl f)^[indexf w zp f] w = zp := by
      rw [Kepler.Text.Reduction5.iterateInstEq f w (indexf w zp f)]
      exact Kepler.Text.MoreLemma2Island1.indexfN hwf hzpf hfnd
    rw [h1, h2]
  have hpow_yi_i : (nextEl (core L (rtrans L N r x i)))^[indexf w yi f] w.1 = yi.1 := by
    have h1 := Kepler.Text.TameSpine.nextPowerCoreWFace L hL hgn haq hm_i hf_i
      (f := f) (w := w) hfdef.symm hwdef.symm (n := indexf w yi f) hyi_le
    have h2 : (nextEl f)^[indexf w yi f] w = yi := by
      rw [Kepler.Text.Reduction5.iterateInstEq f w (indexf w yi f)]
      exact Kepler.Text.MoreLemma2Island1.indexfN hwf hyif hfnd
    rw [h1, h2]
  have hzp_ci : zp.1 ∈ core L (rtrans L N r x i) := by
    rw [← hpow_zp_i]
    exact Kepler.Text.TameSpine.memPowerNextEl hw_ci _
  have hyi_ci : yi.1 ∈ core L (rtrans L N r x i) := by
    rw [← hpow_yi_i]
    exact Kepler.Text.TameSpine.memPowerNextEl hw_ci _
  have hnd_i : (core L (rtrans L N r x i)).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm_i
  -- 基侧成员
  have hzp_r : zp ∈ r := by
    rw [hzpdef]
    exact Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq (i - 1) hf_im1 hm
  have hyi_r : yi ∈ r := by
    rw [hyidef]
    exact Kepler.Text.Reduction5.pnxvwfs1 L hL hgn haq i hf_i hm
  have hzp_cr : zp.1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hzp_r hf
  have hyi_cr : yi.1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hyi_r hf
  have hw_cr : w.1 ∈ core L r := by
    have hwr : w ∈ r := by
      have hwr' : w = nextEl r x := by
        rw [hwdef, hfdef]
        exact hm.2.2.2.2.2.1.symm
      rw [hwr']
      exact Kepler.Text.TameLp.nextEl_mem_of_mem hm.2.2.2.1
    exact Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hwr hf
  have hnd_r : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  -- 两个 core 的 `indexf zp yi` 都等于 f 世界值
  have hadd_f : indexf w zp f + indexf zp yi f = indexf w yi f :=
    Kepler.Text.Reduction4.indexf_add_left hwf hzpf hyif hface_le
  have hadd_ci : indexf w.1 zp.1 (core L (rtrans L N r x i))
      + indexf zp.1 yi.1 (core L (rtrans L N r x i))
      = indexf w.1 yi.1 (core L (rtrans L N r x i)) := by
    apply Kepler.Text.Reduction4.indexf_add_left hw_ci hzp_ci hyi_ci
    rw [hface_zp, hface_yi]
    exact hface_le
  have hstate : indexf zp.1 yi.1 (core L (rtrans L N r x i)) = indexf zp yi f := by
    have h2 := hadd_ci
    rw [hface_zp, hface_yi] at h2
    omega
  have hbase : indexf zp.1 yi.1 (core L r) = indexf zp yi f := by
    have h := indexf3FinalLemmas L hL hgn hres haq hm hk (i := i - 1) (by omega)
    rw [he] at h
    simpa [← hzpdef, ← hyidef, ← hfdef] using h
  -- 长度 > 1（两侧）
  have hlen_i : 1 < (core L (rtrans L N r x i)).length := by
    have hlt := Kepler.Text.Reduction4.indexf_lt_length_of_mem hw_ci hzp_ci
    rw [hface_zp] at hlt
    omega
  have hlen_r : 1 < (core L r).length := by
    have huniqFst : (f.map (fun d => d.1)).Nodup := by
      rw [hfdef]
      exact Kepler.Text.Reduction5.uniqFstFindFace L hL hgn hres hm
    have hinj : ∀ a ∈ f, ∀ b ∈ f, a.1 = b.1 → a = b :=
      (List.nodup_map_iff_inj_on hfnd).mp huniqFst
    have hwzp1 : w.1 ≠ zp.1 := fun h1 => hwz (hinj w hwf zp hzpf h1)
    have hlt := Kepler.Text.Reduction4.indexf_lt_length_of_mem hw_cr hzp_cr
    have hpos : 0 < indexf w.1 zp.1 (core L r) := by
      rcases Nat.eq_zero_or_pos (indexf w.1 zp.1 (core L r)) with h0 | hpos
      · exact absurd (Kepler.Text.Reduction4.indexf_eq_zero hw_cr hzp_cr h0) hwzp1
      · exact hpos
    omega
  -- iff 归约到 `indexf zp yi = 1`
  have hp_i : nextEl (core L (rtrans L N r x i)) zp.1 = yi.1
      ↔ indexf zp.1 yi.1 (core L (rtrans L N r x i)) = 1 :=
    ⟨fun hny => Kepler.Text.MoreLemma2Island1.nextElIndexf hzp_ci hyi_ci hnd_i hny hlen_i,
     fun h1 => Kepler.Text.MoreLemma2Island1.indexfOne hzp_ci hyi_ci hnd_i h1⟩
  have hp_r : nextEl (core L r) zp.1 = yi.1
      ↔ indexf zp.1 yi.1 (core L r) = 1 :=
    ⟨fun hny => Kepler.Text.MoreLemma2Island1.nextElIndexf hzp_cr hyi_cr hnd_r hny hlen_r,
     fun h1 => Kepler.Text.MoreLemma2Island1.indexfOne hzp_cr hyi_cr hnd_r h1⟩
  simp only [hp_i, hp_r, hstate, hbase]

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction5.indexf6FinalLemmas
#print axioms Kepler.Text.Reduction5.indexf7FinalLemmas
#print axioms Kepler.Text.Reduction5.indexf8FinalLemmas

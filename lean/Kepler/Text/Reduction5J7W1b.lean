/-
  Kepler.Text.Reduction5J7W1b — J5-7 W1-2 的几何核（两件，先行落）：
  · `nextElConstLeIndexfFArc` —— f-弧上的 `nextEl r` 常数：
    `k+1 ≤ indexf zi yi f ⇒ nextEl r ((nextEl f)^k zi) = fList L ((nextEl f)^k zi)`。
    证 = `betwnZtranYtransSucConstChain`（在库公开形，KBWPBHQ.hl:623）在 k 与 k+1
    两处 + `findFaceDarts_congr_of_mem` + `fList` 定义级。
  · `singletonPartOfFArc` —— f-弧内部点（`0 < k < indexf zi yi f`）的 atom 是单点：
    `[(nextEl f)^k zi] ∈ parts L r`。证 = 上件于 k/k-1 两处给两个 atom 切点
    （`nextEl r d = fList d ≠ fList (eList d)`，`edgeNondegFXorNi`）+
    `memPartsSingleton`（nb14 在库）——**不需要 HOL 的 LAST/HD 冗长分支**。

  余下（计数 + 严格性）见 DELIVERY_W1B §2 冻结表。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelAtom
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.PwssratMemberBase
import Kepler.Text.MoreLemma2Island3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **W1-2 几何核 ①**：f-弧上的 `nextEl r` 常数（HOL `indexf_z_lt_sizel_ytran`
证体 `betwn_ztran_ytrans_suc_const` 支的 Lean 抽象）：
`k+1 ≤ indexf zi yi f ⇒ nextEl r ((nextEl f)^k zi) = fList L ((nextEl f)^k zi)`。 -/
theorem nextElConstLeIndexfFArc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {i : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf2 : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {k : ℕ} (hk : k + 1 ≤ indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) f) :
    nextEl r ((nextEl f)^[k] (ztrans L N r x i))
      = fList L ((nextEl f)^[k] (ztrans L N r x i)) := by
  set zi := ztrans L N r x i with hzi
  have hziF : zi ∈ f := by
    have h := Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
    rwa [hfind] at h
  have hdF : (nextEl f)^[k] zi ∈ f :=
    Kepler.Text.TameSpine.memPowerNextEl hziF k
  have hxD : x ∈ listOfDarts L :=
    (hm.2.1.2.2.2.1 r hm.2.2.1 x hm.2.2.2.1).1
  have hdFind : (nextEl f)^[k] zi ∈ findFaceDarts L x := by
    rw [hfind]
    exact hdF
  have hfindD : findFaceDarts L ((nextEl f)^[k] zi) = f := by
    have h := Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hxD hdFind
    rwa [hfind] at h
  have hk' : k ≤ indexf zi (ytrans L N r x (i + 1)) f :=
    Nat.le_trans (Nat.le_succ k) hk
  have hpowk : (nextEl r)^[k] zi = (nextEl f)^[k] zi :=
    Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2 hfind hw hk'
  have hpowk1 : (nextEl r)^[k + 1] zi = (nextEl f)^[k + 1] zi :=
    Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2 hfind hw hk
  calc nextEl r ((nextEl f)^[k] zi)
      = nextEl r ((nextEl r)^[k] zi) := by rw [hpowk]
    _ = (nextEl r)^[k + 1] zi := (Function.iterate_succ_apply' (nextEl r) k zi).symm
    _ = (nextEl f)^[k + 1] zi := hpowk1
    _ = nextEl f ((nextEl f)^[k] zi) := Function.iterate_succ_apply' (nextEl f) k zi
    _ = fList L ((nextEl f)^[k] zi) := by
        show nextEl f ((nextEl f)^[k] zi)
          = nextEl (findFaceDarts L ((nextEl f)^[k] zi)) ((nextEl f)^[k] zi)
        rw [hfindD]

/-- **W1-2 几何核 ②**：f-弧内部点是单点 atom：
`0 < k < indexf zi yi f ⇒ [(nextEl f)^k zi] ∈ parts L r`。
两处 atom 切点由 `nextElConstLeIndexfFArc`（k 与 k-1）给，
`memPartsSingleton`（nb14）收口。 -/
theorem singletonPartOfFArc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {i : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf2 : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {k : ℕ} (hk0 : 0 < k)
    (hkn : k < indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) f) :
    [(nextEl f)^[k] (ztrans L N r x i)] ∈ parts L r := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk0)
  set zi := ztrans L N r x i with hzi
  set d := (nextEl f)^[k' + 1] zi with hd
  have hkn' : k' + 1 < indexf zi (ytrans L N r x (i + 1)) f := by
    rw [hzi]
    exact hkn
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
  have hziR : zi ∈ r :=
    Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq i
      (Kepler.Text.Reduction5.finalListInduct i hf2) hm
  have hpowk : (nextEl r)^[k' + 1] zi = d :=
    Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2 hfind hw
      (by omega : k' + 1 ≤ indexf zi (ytrans L N r x (i + 1)) f)
  have hdR : d ∈ r := by
    rw [← hpowk]
    exact Kepler.Text.TameSpine.memPowerNextEl hziR (k' + 1)
  -- 右切点
  have hA : nextEl r d = fList L d :=
    nextElConstLeIndexfFArc L hL hgn haq hm hf2 hfind hw (k := k' + 1) (by rw [← hzi]; omega)
  have hdD : d ∈ listOfDarts L := (hm.2.1.2.2.2.1 r hm.2.2.1 d hdR).1
  have hlast : nextEl r d ≠ fList L (eList d) := by
    rw [hA]
    exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL
      hm.1.edgeNondegenerate hdD
  -- 左切点
  have hprevR : Kepler.Assembly.prevEl r d = (nextEl r)^[k'] zi := by
    rw [hpowk.symm, Function.iterate_succ_apply']
    exact Kepler.Text.TameLp.prevEl_nextEl hnd
      (Kepler.Text.TameSpine.memPowerNextEl hziR k')
  have hprevF : Kepler.Assembly.prevEl r d = (nextEl f)^[k'] zi := by
    rw [hprevR]
    exact Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2 hfind hw
      (by omega : k' ≤ indexf zi (ytrans L N r x (i + 1)) f)
  have hprevRmem : Kepler.Assembly.prevEl r d ∈ r :=
    Kepler.Text.TameLp.prevEl_mem_of_mem hdR
  have hprevD : Kepler.Assembly.prevEl r d ∈ listOfDarts L :=
    (hm.2.1.2.2.2.1 r hm.2.2.1 (Kepler.Assembly.prevEl r d) hprevRmem).1
  have hA' : nextEl r (Kepler.Assembly.prevEl r d) = fList L (Kepler.Assembly.prevEl r d) := by
    rw [hprevF]
    exact nextElConstLeIndexfFArc L hL hgn haq hm hf2 hfind hw (k := k') (by rw [← hzi]; omega)
  have hhead : nextEl r (Kepler.Assembly.prevEl r d)
      ≠ fList L (eList (Kepler.Assembly.prevEl r d)) := by
    rw [hA']
    exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL
      hm.1.edgeNondegenerate hprevD
  exact Kepler.Text.TameSpine.memPartsSingleton L hnd hdR (Or.inr hhead) (Or.inr hlast)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.nextElConstLeIndexfFArc
#print axioms Kepler.Text.Reduction5.singletonPartOfFArc

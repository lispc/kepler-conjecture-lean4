/-
  Kepler.Text.TameSpine.Reduction3J5IndexfYltSizel — tame-corr nb18：双怪件
  `indexf_y_lt_sizel`（more_lemma2:427）第④段收尾（主怪件收官）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ `marked ∧ ¬final ∧ find_face=f ∧ next_el f x=w ⇒
  │  indexf w (ytrans 0) r < sizel (core L r)`。
  │ 路线：③ `indexfWLePartsCard`（nb17 绿）+ `partsToFinsetCardLe` +
  │ `coreLengthEqParts`（nb14 绿）；等号支用 z = ztrans 0 的 atom∈S 与链形
  │ 在库 `Reduction4Idx.indexfYLeZInR0` 的 `q < indexf w z r` 矛盾。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfWLeParts
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase
import Kepler.Text.PwssratCase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart parts core finalList rtrans ntrans ytrans ztrans
  lz ly indexf)

/-- **双怪件主件（HOL `indexf_y_lt_sizel`，more_lemma2:427）**：
`indexf w (ytrans 0) r < sizel (core L r)`。 -/
theorem indexfYltSizel (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r < (core L r).length := by
  set q := Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r with hq
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hwx : w = nextEl r x := by
    rw [← hw, ← hfind]
    exact hm.2.2.2.2.2.1.symm
  have hwr : w ∈ r := by
    rw [hwx]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hyr : ytrans L N r x 0 ∈ r :=
    Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm hf
  have hqlt : q < r.length := Kepler.Text.Reduction5.indexfLtSizel hwr hyr
  have hqle : q ≤ (parts L r).toFinset.card :=
    indexfWLePartsCard L hL hgn haq hm hf hfind hw
  have hcorelen : (core L r).length = (parts L r).length := coreLengthEqParts L r
  have hcardle : (parts L r).toFinset.card ≤ (parts L r).length := partsToFinsetCardLe L r
  by_contra hcon
  push Not at hcon
  have hqple : q ≤ (parts L r).length := le_trans hqle hcardle
  have hcard : (parts L r).toFinset.card = q := by omega
  -- ③ 的两块中间件（为 ④ 重建）
  have hmem : ∀ i ∈ Finset.range q, [(nextEl r)^[i] w] ∈ (parts L r).toFinset := by
    intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    have hilen : i < r.length := Nat.lt_trans hiq hqlt
    have hdi : (nextEl r)^[i] w ∈ r := memPowerNextEl hwr i
    have hdi' : Kepler.Text.Reduction5.indexf w ((nextEl r)^[i] w) r = i :=
      (Kepler.Text.MoreLemma2Island1.nextElnIndexf hwr hdi hnd
        ((Kepler.Text.Reduction5.iterateInstEq r w i).symm) hilen)
    have hlt' : Kepler.Text.Reduction5.indexf w ((nextEl r)^[i] w) r
        < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := by
      rw [hdi']
      exact hiq
    exact List.mem_toFinset.mpr
      (singletonAtomSubset L hL hgn haq hm hf hfind hw hdi hlt')
  have hinj : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q,
      [(nextEl r)^[a] w] = [(nextEl r)^[b] w] → a = b := by
    intro a ha b hb heq
    have haq : a < q := Finset.mem_range.mp ha
    have hbq : b < q := Finset.mem_range.mp hb
    have halen : a < r.length := Nat.lt_trans haq hqlt
    have hblen : b < r.length := Nat.lt_trans hbq hqlt
    have hd : (nextEl r)^[a] w = (nextEl r)^[b] w := List.singleton_inj.mp heq
    have hidxa : Kepler.Text.Reduction5.indexf w ((nextEl r)^[a] w) r = a :=
      Kepler.Text.MoreLemma2Island1.nextElnIndexf hwr (memPowerNextEl hwr a) hnd
        ((Kepler.Text.Reduction5.iterateInstEq r w a).symm) halen
    have hidxb : Kepler.Text.Reduction5.indexf w ((nextEl r)^[b] w) r = b :=
      Kepler.Text.MoreLemma2Island1.nextElnIndexf hwr (memPowerNextEl hwr b) hnd
        ((Kepler.Text.Reduction5.iterateInstEq r w b).symm) hblen
    rw [hd] at hidxa
    omega
  -- S = parts.toFinset
  have hsub : (Finset.range q).image (fun i => [(nextEl r)^[i] w])
      ⊆ (parts L r).toFinset := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact hmem i hi
  have hcardImg : ((Finset.range q).image (fun i => [(nextEl r)^[i] w])).card = q := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSeq : (Finset.range q).image (fun i => [(nextEl r)^[i] w])
      = (parts L r).toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcardImg])
  -- z 的 atom 落在 S，与 indexfYLeZInR0 矛盾
  have hzr : ztrans L N r x 0 ∈ r :=
    Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq 0 (by
      show ¬ finalList L r
      exact hf) hm
  obtain ⟨p, hp, hzp⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hnd hzr
  have hpS : p ∈ (parts L r).toFinset := List.mem_toFinset.mpr hp
  rw [← hSeq] at hpS
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hpS
  have hiq : i < q := Finset.mem_range.mp hi
  have hilen : i < r.length := Nat.lt_trans hiq hqlt
  have hzi : ztrans L N r x 0 = (nextEl r)^[i] w := by
    have hmem_single : ztrans L N r x 0 ∈ [(nextEl r)^[i] w] := by
      rw [hpi]
      exact hzp
    simpa using hmem_single
  have hziidx : Kepler.Text.Reduction5.indexf w (ztrans L N r x 0) r = i := by
    rw [hzi]
    exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hwr (memPowerNextEl hwr i) hnd
      ((Kepler.Text.Reduction5.iterateInstEq r w i).symm) hilen
  have hzilt : Kepler.Text.Reduction5.indexf w (ztrans L N r x 0) r < q := by
    rw [hziidx]
    exact hiq
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hileq := Kepler.Text.Reduction4Idx.indexfYLeZInR0 L hL hgn hunL hm hf
  have hw' : nextEl (findFaceDarts L x) x = w := by
    rw [hfind]
    exact hw
  have hyz : Kepler.Text.Reduction5.ly L r x = ytrans L N r x 0 := rfl
  have hzz : Kepler.Text.Reduction5.lz L N r x = ztrans L N r x 0 := rfl
  rw [hw', hyz, hzz] at hileq
  omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfYltSizel

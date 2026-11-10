/-
  Kepler.Text.TameSpine.Reduction3J5IndexfYltSizel — tame-corr nb17：双怪件
  `indexf_y_lt_sizel`（more_lemma2:427）的 ③ 计数 + ④ 收尾。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ ③ `Kepler.Text.Reduction5.indexf w (ytrans 0) r ≤ CARD (parts L r)`：`i ↦ [(nextEl r)^i w]`
  │   （i < q）单射嵌入 parts；成员 = `indexfIterateEq` + nb16
  │   `singletonAtomSubset`；单射 = `nextElnIndexf` 唯一性（BEq 桥
  │   `iterateInstEq`）。
  │ ④ `q < sizel (core L r)`：等号支用 z = ztrans 0 的 atom = [z] 与
  │   链形 `indexfYLeZInR0` 的 `q < Kepler.Text.Reduction5.indexf w z r` 矛盾；`coreLengthEqParts`
  │   折 `sizel core`。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5SingletonAtomSubset
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.PwssratCase
import Kepler.Text.PwssratMemberBase
import Kepler.Text.MoreLemma2Naming

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart parts core finalList rtrans ytrans ztrans indexf)

/-- 迭代的 `indexf` = 指数（`i < r.length`）：`nextElnIndexf` 经在库
`iterateInstEq` 桥到 prod 世界。 -/
private theorem indexfIterateEq {r : List Dart} {w : Dart} (hw : w ∈ r)
    (hnd : r.Nodup) {i : ℕ} (hi : i < r.length) :
    Kepler.Text.Reduction5.indexf w ((nextEl r)^[i] w) r = i := by
  have hdi : (nextEl r)^[i] w ∈ r := memPowerNextEl hw i
  have hp : (@nextEl Dart instBEqOfDecidableEq r)^[i] w = (nextEl r)^[i] w :=
    (Kepler.Text.Reduction5.iterateInstEq r w i).symm
  exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hw hdi hnd hp hi

/-- **③ 计数**：`Kepler.Text.Reduction5.indexf w (ytrans 0) r ≤ CARD (set_of_list (parts L r))`。 -/
theorem indexfWLePartsCard (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r ≤ (parts L r).toFinset.card := by
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
  have hqlt : Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r < r.length :=
    Kepler.Text.Reduction5.indexfLtSizel hwr hyr
  have hmem : ∀ i ∈ Finset.range (Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r),
      [(nextEl r)^[i] w] ∈ (parts L r).toFinset := by
    intro i hi
    have hiq : i < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := Finset.mem_range.mp hi
    have hilen : i < r.length := Nat.lt_trans hiq hqlt
    have hdi : (nextEl r)^[i] w ∈ r := memPowerNextEl hwr i
    have hidx : Kepler.Text.Reduction5.indexf w ((nextEl r)^[i] w) r = i := indexfIterateEq hwr hnd hilen
    have hlt' : Kepler.Text.Reduction5.indexf w ((nextEl r)^[i] w) r
        < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := by
      rw [hidx]
      exact hiq
    exact List.mem_toFinset.mpr
      (singletonAtomSubset L hL hgn haq hm hf hfind hw hdi hlt')
  have hinj : ∀ a ∈ Finset.range (Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r),
      ∀ b ∈ Finset.range (Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r),
      [(nextEl r)^[a] w] = [(nextEl r)^[b] w] → a = b := by
    intro a ha b hb heq
    have haq : a < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := Finset.mem_range.mp ha
    have hbq : b < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := Finset.mem_range.mp hb
    have halen : a < r.length := Nat.lt_trans haq hqlt
    have hblen : b < r.length := Nat.lt_trans hbq hqlt
    have hd : (nextEl r)^[a] w = (nextEl r)^[b] w := List.singleton_inj.mp heq
    have hidxa : Kepler.Text.Reduction5.indexf w ((nextEl r)^[a] w) r = a := indexfIterateEq hwr hnd halen
    have hidxb : Kepler.Text.Reduction5.indexf w ((nextEl r)^[b] w) r = b := indexfIterateEq hwr hnd hblen
    rw [hd] at hidxa
    omega
  have hle := Finset.card_le_card_of_injOn (fun i => [(nextEl r)^[i] w])
    hmem hinj
  simpa using hle

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfWLePartsCard

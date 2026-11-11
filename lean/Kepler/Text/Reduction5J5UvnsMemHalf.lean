/-
  Kepler.Text.Reduction5J5UvnsMemHalf — U1c 全 vs 装配的 **mem 半**（与 tame-corr
  的 Cl 半并行；不改 `Reduction5J5UvnsChainCl.lean`）。

  ┌─ 两件 ─────────────────────────────────────────────────────────
  │ `memInit`  : `MemIn (core L r)` 对
  │   `init = if v = y0 then [] else [some v] ++ (between (core L r) v y0).map some`
  │   （`y0 = (ytrans L N r x 0).1`）。
  │ `memFinal` : `MemIn (core L r)` 对
  │   `final = if z = prevEl (core L r) v then []
  │            else (between (core L r) z (prevEl (core L r) v)).map some
  │                 ++ [some (prevEl (core L r) v)]`
  │   （`z = (ztrans L N r x (k-1)).1`）。
  └────────────────────────────────────────────────────────────────

  假设集与在库 `memMid` 同形（`hm/hnf/hk` + 上下文），另加 `v` 与 UVNS 槽前提
  `(prevEl (core L r) v, v) = x`。要点（tame-corr DELIVERY-nb63 §2.2/2.3）：
  · `v ∈ core`：`nextPrevId`（BetwnBase:498）+ `nextEl_mem_of_mem`；
  · `y0 ∈ core`：`hym 0 hk0`（`pnxvwfs1` + `finalAssumptionMemFstCore`）；
  · `z ∈ core`：`hzm (k-1)`；
  · `prevEl v ∈ core`：`hprev` 的 FST = `x.1`，`x ∈ r`；
  · `between` 段：`List.getD` 取出 + `betwnMem`。

  **纪律**：零公理、零占位证明、零反射式判定；不改已落库陈述/定义；主仓 tracked 零写入。
-/
import Kepler.Text.Reduction5J5UvnsChainCl
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction4Subseg4
import Kepler.Text.Reduction4Subseg8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts)
open Kepler.Graphs (fgraph between)

/-- `S` 在 `l` 上逐点成立 ⇒ `MemIn S (l.map some)`。 -/
private theorem memInMapSome {S : ℕ → Prop} {l : List ℕ} (h : ∀ t ∈ l, S t) :
    MemIn S (l.map some) := by
  intro j hj _hsome
  have hgd : (l.map some).getD j none = some (l.getD j 0) := by
    have hmap := uvnsGetDMapSomeApp (r := l) [] (t := j) (by simpa using hj)
    simpa using hmap
  rw [hgd]
  show S (l.getD j 0)
  exact h _ (by
    have hj' : j < l.length := by simpa using hj
    rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hj' 0]
    exact List.getElem_mem _)

/-- **U1c mem 半 ①（init）**：`MemIn (core L r)` 对
`if v = y0 then [] else [some v] ++ (between (core L r) v y0).map some`。 -/
theorem memInit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (v : ℕ) (hprev : (prevEl (core L r) v, v) = x) :
    MemIn (fun w => w ∈ core L r)
      (if v = (ytrans L N r x 0).1 then []
       else [some v] ++ ((between (core L r) v (ytrans L N r x 0).1).map some)) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hym : ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs1 L hL hgn haq i (hnf_i i hi) hm)
  have hnd : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hxr : x ∈ r := hm.2.2.2.1
  have hxcore : x.1 ∈ core L r := hcoreof x hxr
  have hfst : prevEl (core L r) v = x.1 := congrArg Prod.fst hprev
  have hvcore : v ∈ core L r := by
    have hnp : nextEl (core L r) (prevEl (core L r) v) = v :=
      Kepler.Text.Reduction5.nextPrevId hnd v
    rw [hfst] at hnp
    rw [← hnp]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxcore
  have hy0core : (ytrans L N r x 0).1 ∈ core L r := hym 0 hk0
  by_cases hvy : v = (ytrans L N r x 0).1
  · rw [if_pos hvy]
    intro j hj _
    simp at hj
  · rw [if_neg hvy]
    exact memInAppend (fun w => w ∈ core L r) _ _
      (memInSingle (fun w => w ∈ core L r) v hvcore)
      (memInMapSome (fun t ht => Kepler.Text.Reduction5.betwnMem ht))

/-- **U1c mem 半 ②（final）**：`MemIn (core L r)` 对
`if z = prevEl v then [] else (between (core L r) z (prevEl v)).map some ++ [some (prevEl v)]`
（`z = (ztrans L N r x (k-1)).1`）。 -/
theorem memFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (v : ℕ) (hprev : (prevEl (core L r) v, v) = x) :
    MemIn (fun w => w ∈ core L r)
      (if (ztrans L N r x (k - 1)).1 = prevEl (core L r) v then []
       else ((between (core L r) (ztrans L N r x (k - 1)).1
          (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)])) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnf_i : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hzcore : (ztrans L N r x (k - 1)).1 ∈ core L r :=
    hcoreof _ (pnxvwfs2 L hL hgn haq (k - 1) (hnf_i (k - 1) (by omega)) hm)
  have hxr : x ∈ r := hm.2.2.2.1
  have hxcore : x.1 ∈ core L r := hcoreof x hxr
  have hfst : prevEl (core L r) v = x.1 := congrArg Prod.fst hprev
  have hprevcore : prevEl (core L r) v ∈ core L r := by
    rw [hfst]
    exact hxcore
  by_cases hz : (ztrans L N r x (k - 1)).1 = prevEl (core L r) v
  · rw [if_pos hz]
    intro j hj _
    simp at hj
  · rw [if_neg hz]
    exact memInAppend (fun w => w ∈ core L r) _ _
      (memInMapSome (fun t ht => Kepler.Text.Reduction5.betwnMem ht))
      (memInSingle (fun w => w ∈ core L r) _ hprevcore)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.memInMapSome
#print axioms Kepler.Text.Reduction5.memInit
#print axioms Kepler.Text.Reduction5.memFinal

/-
  Kepler.Text.Reduction5J7W1 — J5-7 `betwn_core0_z_y` 塔 W1 基建缺口：
  · `qcdvkeaChain` —— HOL `QCDVKEA.hl:64` 的链形。**不重写本体**：
    在库 `TameSpine.qcdvkeaTowerI` 已是逐字链形（qcdvkeaV0 + 塔层换词），
    其唯一槽 `AqiunppSlot L hL` 由 `TameSpine.aqiunpp`（JcajyduRed2Tav2，
    由 `transformAssumptionV2_of_goodList` 无条件供）逐状态实例化。
  · `memFstCoreOfMem` —— HOL `betwn_corek_z_x.hl:84` 的 `mem_core`（normal_list
    形）：`TameList34.memCore`（`v ∈ coreSpine ↔ v ∈ r.map FST`）+
    `Reduction5Ml1Leaves.coreEqCoreSpine` + `List.mem_map` 一行桥，
    **不重落 memCore 本体**。
  对表：`betwnZtranYtransSucConstChain`（W1-5）**已在树**
  （`TameSpine.Reduction3J5PowerCorePublic:120`，公开形、同签名），本文件不重落。
  余下 W1-2/W1-3 见 DELIVERY_J7W1 §3 冻结表。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.Reduction5Ml1Leaves
import Kepler.Text.TameSpine.TameList34

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **W1-1：QCDVKEA 链形**（HOL `QCDVKEA.hl:64-157` 的结论）：
`good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final(rtrans (SUC i)) ∧
find_face L x = f ∧ next_el f x = w ⇒ indexf w (ztrans i) f ≤
indexf w (ytrans (SUC i)) f`。在库 `qcdvkeaTowerI` 直投；`AqiunppSlot`
槽 = `aqiunpp` 的逐状态实例（**零本体重写**）。 -/
theorem qcdvkeaChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf2 : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf w (ztrans L N r x i) f ≤ indexf w (ytrans L N r x (i + 1)) f := by
  have h := Kepler.Text.TameSpine.qcdvkeaTowerI L hL hgn
    (fun hgn' N' r' x' hm' i' =>
      Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i')
    i hm hf2 hfind hw
  rwa [← Kepler.Text.Reduction3.indexf_eq_spine,
    ← Kepler.Text.Reduction3.indexf_eq_spine] at h

/-- **W1-4：`mem_core` 链桥**（HOL `betwn_corek_z_x.hl:84`，normal_list 形；
该文件被 `betwn_core0_z_y.hl` 以 `open Betwn_corek_z_x` + `mem_core` 消费）：
`y ∈ r` ⇒ `FST y ∈ core L r`。证：`coreEqCoreSpine` 换载体 +
`TameList34.memCore` 的 ⇐ 向 + `List.mem_map` 证人 `y`。 -/
theorem memFstCoreOfMem {L : fgraph ℕ} (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : Kepler.Text.TameSpine.NormalListSpine hL N)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) {y : ℕ × ℕ} (hy : y ∈ r) :
    y.1 ∈ core L r := by
  rw [coreEqCoreSpine L r]
  exact (Kepler.Text.TameSpine.memCore L hL hn hr y.1).mpr
    (List.mem_map.mpr ⟨y, hy, rfl⟩)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.qcdvkeaChain
#print axioms Kepler.Text.Reduction5.memFstCoreOfMem

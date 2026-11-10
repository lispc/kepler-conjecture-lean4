/-
  Kepler.Text.Reduction5J5NotNextCore0I — J5-1c 收口：F3 的无槽全形
  `final_assumptions_not_next_core_0_i`（reduction4.hl:5139，78L），占原文名。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ reduction4.hl:5139 `final_assumptions_not_next_core_0_i` → `finalAssumptionsNotNextCore0I`：
  │   good_list L ∧ good_list_nodes L ∧ is_restricted (hypermap_of_list L) ∧
  │   marked_list L N r x ∧ ¬final_list L r ∧ transform_count L N r x = k ⇒
  │   (!i. i < k ∧ betwn (find_face L x) (ytrans … i) (ztrans … i) = [] ⇒
  │        ¬(next_el (core L r) (FST (ytrans … i)) = FST (ztrans … i)))
  │ `∀ i. A ∧ B ⇒ C` 写成柯里化 `∀ i, A → B → C`，同 `betwnCoreReductionLemma`
  │ 与九槽顶层 `hnn0i` 槽形。
  └────────────────────────────────────────────────────────────────

  ┌─ 前提集对账 ──────────────────────────────────────────────────────
  │ HOL 六前提逐条对应（good_list ↦ hL、good_list_nodes ↦ hgn、is_restricted ↦ hres、
  │ marked_list ↦ hm、¬final_list ↦ hnf、transform_count = k ↦ hk）。
  │ 额外只有 `haq : AqiunppSlot L hL`（链惯例的 TAV2 槽，同 `betEqNilImpNextYZ` 等件）。
  │ **`hta` 不是前提**：`kbwpbhq1Chain` 要双槽（haq + hta），其中的 `hta` 由本文件用
  │ `transformAssumptionSpineOfAqiunpp`（Reduction5J5Tav2Bridge，由 `haq` 供出）在证体内
  │ 补上。因此本件比「haq + hta 双槽」形强：结论相同、前提少一条。
  └────────────────────────────────────────────────────────────────

  ┌─ 两个槽的供料（塔内既有 / 本波落库）─────────────────────────────
  │ 槽 ① `hpnx1`（PNXVWFS1 形）← `pnxvwfs1`（本车道 J5-2，Reduction5J5Pnxvwfs，
  │   单槽 haq）。**查重记账**：tame-corr nb8 另有 `pnxvwfs1Chain`
  │   （TameSpine/Reduction3PnxvwfsChain，双槽 haq + hta），与本件结论同一、
  │   前提多一条；本文件用单槽版，未用双槽版。另：派单提到的 `pnxvwfs2Chain`
  │   树内不存在（实测 grep 零命中；PNXVWFS2 的链形是本车道的 `pnxvwfs2`，
  │   Reduction5J5Pnxvwfs 内，本件不消费它）。
  │ 槽 ② `hkb1`（KBWPBHQ1 形）← `kbwpbhq1Chain`（tame-corr nb8，
  │   TameSpine/Reduction3Kbwpbhq1Chain，双槽 haq + hta；hta 由本文件桥补）。
  │ 证体 = 在库槽版 `finalAssumptionsNotNextCore0IOfSlots`（Reduction5J5NotNextCore，
  │ 已落库 `599ab6ea`，陈述不动）代入两槽。该件证体与本件同构于 HOL :5145-:5235
  │ 的消费面：`bet_eq_nil_imp_next_y_z` / `mem_ytrans_rtrans_suc` /
  │ `next_core_ne_FST` / `ne_fst_imp_f_list` / `next_el_core_imp_next_f` /
  │ parts 族 / `marked_list_uniq_core`，全部在库。
  └────────────────────────────────────────────────────────────────

  ┌─ 对主线的影响 ────────────────────────────────────────────────────
  │ 九槽顶层 `hnn0i` 槽（JcajyduRed5Top:73-82）的供料 = 本件；接线时只需再给
  │ `AqiunppSlot`（链侧无条件形见 JcajyduRed2Tav2.aqiunpp，按 U3 口径由编排者接）。
  │ `…OfSlots` 槽版保留不删（既有文件零触碰）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5NotNextCore
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.TameSpine.Reduction3Kbwpbhq1Chain

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList findList)

/-- **HOL `final_assumptions_not_next_core_0_i`**（reduction4.hl:5139）：i < transform_count
且同面 betwn 空时，core 环上 FST (ytrans i) 的后继不是 FST (ztrans i)。无槽全形。 -/
theorem finalAssumptionsNotNextCore0I (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    ∀ i, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
      nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 :=
  finalAssumptionsNotNextCore0IOfSlots L hL hgn hres haq k hm hnf hk
    (fun i hnfi => pnxvwfs1 L hL hgn haq i hnfi hm)
    (fun u hur huf =>
      Kepler.Text.TameSpine.kbwpbhq1Chain L hL hgn haq
        (transformAssumptionSpineOfAqiunpp L hL haq) hm hur huf)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.finalAssumptionsNotNextCore0I

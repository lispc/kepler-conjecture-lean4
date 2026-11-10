/-
  Kepler.Text.Reduction1W4b — J4 Wave W4 第二波（部分）：`marked_list_x_quotient`
  （HOL reduction1.hl:4615-:4654）。

  本波范围与本文件所含（如实）：工单列的 W4-3 flag 链（`HKBGWJI` /
  `final_list_prev_quotient_list_rot` / `loop_choice_crit`）与余量三件中，
  本文件只落 `marked_list_x_quotient` 一件——它是六件里唯一「具名依赖在库内
  已逐个核实签名」的；其余五件的证体已通读、孪生已批查，未落原因与逐件
  依赖表见 DELIVERY_W4B（非结构性阻塞，是本轮预算止于此）。

  陈述折算：
  · `MEM x (list_of_darts (quotient_list L N))` ↦
    `x ∈ listOfDarts (quotientList L N)`（chain 载体，同 W3a 文件头定案）；
  · 五前提保 HOL 原序，仅 `good_list L` 因载体依赖前移为首参
    （`normalList`/`hypermapOfList`/`markedList` 均持 GoodList 证人参；
    与 `flagListSeed` 同一处理）。零省前提。

  证体（HOL 同构）：`x ∈ r`、`r ∈ N`（marked_list 第 3/4 合取）→
  `parts_flatten` 取 `x` 所在的 part `p` → 断言 `x = LAST p`：否则
  `parts_next_unlast`（part 内非末元的 next_el = `f_list ∘ e_list`）+
  `next_el_parts_unlast`（`next_el r x = next_el p x`）+ marked_list 第 6 合取
  （`next_el r x = f_list L x`）给出 `f_list L x = f_list L (e_list x)`，
  与 `edge_nondeg_f_xor_ni` 矛盾 → `mem_list_of_darts_quotient`（TameList10
  iff 形，免 HOL 的 `list_of_darts_quotient` 展开 + MEMf_MAP 手工组装）收口。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.ChainListsL2
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList10

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts eList fList nextEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.ChainLists (normalList markedList)
open Kepler.Text.Reduction5 (Dart quotientList parts)
open Kepler.Text.TameLp (hypermapOfList)

/-- **HOL `marked_list_x_quotient`**（reduction1.hl:4615-:4654）：
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\ good_list L /\
all uniq L /\ marked_list L N r x ==>
MEM x (list_of_darts (quotient_list L N))`。 -/
theorem markedListXQuotient {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    {x : Dart} (hL : GoodList L)
    (hnl : normalList L hL N)
    (hend : (hypermapOfList L hL).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hm : markedList L hL N r x) :
    x ∈ listOfDarts (quotientList L N) := by
  have hnlS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  have hrN : r ∈ N := hm.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  obtain ⟨hun, hne⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hnlS hrN
  have hxD : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  -- x 所在的 part
  have hxfl : x ∈ (parts L r).flatten := by
    rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hun hne]
    exact hxr
  obtain ⟨p, hp, hxp⟩ := List.mem_flatten.mp hxfl
  -- LAST p = x（否则与边非退化矛盾）
  have hlast : x = p.getLast! := by
    by_contra hcon
    have h1 := Kepler.Text.MoreLemma2PartsFst.partsNextUnlast L hun hne p hp x hxp hcon
    have h2 := Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hun hne hp hxp hcon
    have h3 : fList L x = fList L (eList x) := by rw [← hnext, h2, h1]
    exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hend hxD h3
  rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
  refine (Kepler.Text.TameSpine.memListOfDartsQuotient L hL hnlS hend hall x).mpr
    ⟨p, r, ?_, hrN, hlast⟩
  rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
  exact hp

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.markedListXQuotient

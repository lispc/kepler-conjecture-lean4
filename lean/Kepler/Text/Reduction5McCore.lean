/-
  Kepler.Text.Reduction5McCore — W2-c-2 首件：`more_lemma2.MEM_CORE` 链孪生
  （more_lemma2.hl:59：`d ∈ r ⇒ FST d ∈ core L r`）。

  ┌─ 路线（链侧；零 TameSpine import）────────────────────────────
  │ HOL 证体走 `quotient_all_uniq` + `MEMf_MAP` 的间接路线；链侧直接走
  │ **parts 原子结构**：`partsMemExists`（d 落在某原子 p）+ `partsFst`
  │ （p 内 FST 恒定 = p.head!.1，需 markedList 合取 2 normalList /
  │ 合取 3 r ∈ N）+ core 的定义级 mem_map——比 HOL 短且无商层中转。
  └────────────────────────────────────────────────────────────────

  **纪律**：零占位证明、零新增公理、零反射式判定；主仓双零写入。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2PartsFst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)

/-- 非空表 `headD (0,0)` = `head!`（private；Dart 载体）。 -/
private theorem headD_eq_headBang {l : List Dart} (hne : l ≠ []) :
    l.headD (0, 0) = l.head! := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- **HOL `more_lemma2.MEM_CORE`**（more_lemma2.hl:59）：`MEM d r ∧ good_list ∧
good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ⇒ MEM (FST d) (core L r)`。 -/
theorem memCore {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    {x d : Dart} (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hd : d ∈ r) (hf : ¬ finalList L r) :
    d.1 ∈ core L r := by
  have hN : Kepler.Text.ChainLists.normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  obtain ⟨p, hp, hdp⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hd
  have hfst : d.1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hp hdp
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p hp
  rw [hfst]
  unfold core
  exact List.mem_map.mpr ⟨p, hp, by
    show (p.headD (0, 0)).1 = p.head!.1
    rw [headD_eq_headBang hpne]⟩

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三） -/
#print axioms Kepler.Text.Reduction5.memCore

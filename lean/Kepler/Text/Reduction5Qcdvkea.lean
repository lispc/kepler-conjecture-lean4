/-
  Kepler.Text.Reduction5Qcdvkea — W2-c-3 波：Qcdvkea 簇链孪生
  （`FINAL_LIST_INDUCT` Qcdvkea.hl:1-20 与后续 `QCDVKEA` 主件）。

  ┌─ DIFFERS（对 HOL 陈述；链侧更强形记档）────────────────────────
  │ `FINAL_LIST_INDUCT`：HOL 前提 = `transform_assumption_v2 ∧ good_list ∧
  │ good_list_nodes ∧ marked_list ∧ ¬final_list (rtrans (SUC i))`；链侧
  │ `transformList` 的 `if finalList L r then (N,r) else …` 使该件**纯
  │ 定义级**（final 态变换恒等 ⇒ 反证一步），故只保留结论侧前提
  │ `¬final_list (rtrans (SUC i))`——**前提子集（更强形）**，与
  │ `MoreLemma2Island3`…（t8b 先例）同口径；消费者携全前提时直接可喂。
  └────────────────────────────────────────────────────────────────

  **纪律**：零占位证明、零新增公理、零反射式判定；主仓双零写入。禁词零。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList prevEl listOfDarts findFaceDarts)

/-- **HOL `Qcdvkea.FINAL_LIST_INDUCT`**（Qcdvkea.hl）：`¬final_list (rtrans (SUC i)) ⇒
¬final_list (rtrans i)`（链侧更强形：免 TAV2/marked 前提，见文件头 DIFFERS）。 -/
theorem finalListInduct {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart} {x : Dart}
    (i : ℕ) (hf : ¬ finalList L (rtrans L N r x (Nat.succ i))) :
    ¬ finalList L (rtrans L N r x i) := by
  intro hfin
  apply hf
  have hfin' : finalList L
      (((Kepler.Text.Reduction5.transformList L x)^[i] (N, r)).2) := hfin
  have hstep : rtrans L N r x (Nat.succ i) = rtrans L N r x i := by
    show ((Kepler.Text.Reduction5.transformList L x)^[Nat.succ i] (N, r)).2
        = ((Kepler.Text.Reduction5.transformList L x)^[i] (N, r)).2
    rw [Function.iterate_succ_apply']
    simp only [Kepler.Text.Reduction5.transformList]
    rw [if_pos hfin']
  rw [hstep]
  exact hfin

/-- **HOL `Kbwpbhq.change_f_list_prev_el`**（KBWPBHQ.hl）：`uniq darts ∧
MEM y darts ∧ f_list L y = x ⇒ prev_el (find_face L x) x = y`。
链侧 = `TameLp.prev_fList_inverse` 直投（x 换元）。 -/
theorem changeFListPrevEl {L : fgraph ℕ} {x y : Dart}
    (hn : (listOfDarts L).Nodup) (hy : y ∈ listOfDarts L)
    (hxy : fList L y = x) :
    prevEl (findFaceDarts L x) x = y := by
  subst hxy
  exact Kepler.Text.TameLp.prev_fList_inverse hn hy

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三） -/
#print axioms Kepler.Text.Reduction5.finalListInduct
#print axioms Kepler.Text.Reduction5.changeFListPrevEl

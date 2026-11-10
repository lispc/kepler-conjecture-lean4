/-
  Kepler.Text.Reduction5Kbwpbhq — W2-c-3：KBWPBHQ2 支撑波三件链孪生
  （`mem_ytrans_list_of_darts` HOJODCM.hl / `prev_el_betwn_ztran_rtrans`
  KBWPBHQ.hl / `Nuxcoea.MIN_LEAST` local/NUXCOEA.hl）。

  ┌─ 路线（链侧；零 TameSpine import）────────────────────────────
  │ ① `memYtransListOfDarts`：HOL 走 marked_list 展开 + HQYMRTX1_list；
  │    链侧利用 `ly = (f_list)^(l'm+1)` 的 **rfl 定义** + f_list 迭代成员
  │    闭包（`TameLp.fList_mem_darts`）直证——免 HQYMRTX1 链侧化。
  │ ② `prevElBetwnZtranRtrans`：HOL 的 change_next_prev/MEM_POWER/
  │    indexf_n/indexf_lt_sizel/next_eln_indexf 五引路线，链侧对应
  │    `prevEl_nextEl` / `memNextElIterate` / `indexfN`（隔位迭代等式）/
  │    `indexf_lt_length_of_mem` / `nextElnIndexf`，算术全交 omega；
  │    主不等式 = `indexfYLeZInR0` 在 (ntrans i, rtrans i) 状态实例化。
  │ ③ `minLeast`：`Reduction5.minNum_spec` 直投。
  └────────────────────────────────────────────────────────────────

  **纪律**：零占位证明、零新增公理、零反射式判定；主仓双零写入。禁词零。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.PwssratMemberBase
import Kepler.Text.PwssratCase
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList listOfDarts findFaceDarts)

/-! ## §1 `Nuxcoea.MIN_LEAST`（local/NUXCOEA.hl：`c ∈ X ⇒ min_num X ∈ X ∧ min_num X ≤ c`） -/

/-- **HOL `Nuxcoea.MIN_LEAST`**：`minNum_spec` 直投。 -/
theorem minLeast {X : Set ℕ} {c : ℕ} (hc : c ∈ X) :
    Kepler.Text.Reduction5.minNum X ∈ X ∧ Kepler.Text.Reduction5.minNum X ≤ c := by
  obtain ⟨h1, h2⟩ := Kepler.Text.Reduction5.minNum_spec ⟨c, hc⟩
  exact ⟨h1, h2 c hc⟩

/-! ## §2 `mem_ytrans_list_of_darts`（HOJODCM.hl） -/

/-- f_list 迭代成员闭包（private）。 -/
private theorem fListIterateDarts {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : Dart}
    (hd : d ∈ listOfDarts L) : ∀ m, (fList L)^[m] d ∈ listOfDarts L := by
  intro m
  induction m with
  | zero => simpa using hd
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Text.TameLp.fList_mem_darts hn ih

/-- **HOL `Hojodcm.mem_ytrans_list_of_darts`**（HOJODCM.hl，v0 形）：`good_list ∧
good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ⇒
MEM (ytrans L N r x 0) (list_of_darts L)`。 -/
theorem memYtransListOfDarts {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    {x : Dart} (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    ytrans L N r x 0 ∈ listOfDarts L := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hy_eq : ytrans L N r x 0 = Kepler.Text.Reduction5.ly L r x := by
    simp [Kepler.Text.Reduction5.ytrans, Kepler.Text.Reduction5.rtrans_zero]
  have hly : Kepler.Text.Reduction5.ly L r x
      = (fList L)^[Kepler.Text.Reduction5.lm L r x + 1] x := rfl
  rw [hy_eq, hly]
  exact fListIterateDarts hL.1 hx _

/-! ## §3 `prev_el_betwn_ztran_rtrans` —— 移交下一笔

熔断诊断（实例桥）：该件七步链需在 Island1 系（nextEl 烤派生实例：`indexfN`/
`memNextElIterate`/`nextElnIndexf`）与 TameLp 系（`prevEl_nextEl` 在本树实例
上下文烤 `instBEqProd`）之间拼接等式——两实例非 defeq（`instBEqProd` ≠
`instBEqOfDecidableEq`，LawfulBEq 只保证行为相等）。修复形 = 私件桥簇：
`findIdx` 点态一致引理 → `idxOf` 跨实例等值 → `nextEl` 跨实例等值 →
迭代桥（各 ~10–15 行）。本笔按止损纪律先交两件绿件，prevElBetwn 随桥簇下笔。 -/

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三） -/
#print axioms Kepler.Text.Reduction5.minLeast
#print axioms Kepler.Text.Reduction5.memYtransListOfDarts

/-
  Kepler.Text.TameSpine.JcajyduAqSplit1H — E4d-b：**`aq3Concl` 全式**

  目标（工单件 B）：`aq3Concl L hL`（AQ 塔第 3 叶，
  HOL `AQ3_concl` / AQ23.hl:263-:266 `all (f_last L) (ntrans L N r x 1)`）。

  路线（`aq2` 同款骨架 + 两槽同式）：
  - `final` 支：`ntransId` 把 `ntrans … 1` 折回 `N`，逐点取
    `NormalListSpine` 合取 3（`all (f_last L) N`）；
  - `¬final` 支：`ntrans1` 展开成 `replace r [split.2] N ++ [split.1]`，
    `memReplaceCases` 双源 + `List.mem_cons` 拆尾单元素：
    · `s ∈ N` → `NormalListSpine` 合取 3；
    · `s = split.2` → `aq3Split2FLastClean`（E2/E3 已落）；
    · `s = split.1` → `fLastSplit1`（本车道 E4d-a-4）。

  载体记账：`aq3Concl` 的陈述无 `∀ l ∈ L, l.Nodup` 槽（既有 def，**不改陈述**），
  但两槽都吃它 ⇒ 从 `hm.1.1 : IsRestricted` 的 `simple` 字段经
  `simpleHypermapUniq`（TameList14，`simple ↔ all uniq L`）现取：
  `(simpleHypermapUniq L hL hgn).mp hm.1.1.simple`（HOL `AQ3` 证明
  第 2 行 `DICH_ASM_TAC (0)[Tame_defs2.marked_list]` 后的 `good_list` 展开
  同源消费，零新前提）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1G

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **HOL `AQ3_concl`**（AQ23.hl:263-:266）真证：`all (f_last L) (ntrans L N r x 1)`。
final 支 = `ntransId` + `normal_list` 合取 3；¬final 支 = `ntrans1` +
`memReplaceCases` 双源，split.2 槽 = `aq3Split2FLastClean`、split.1 槽 =
`fLastSplit1`（HOL AQ23:269 起证明体：split.2 支 :311-:352、split.1 支 :359 起）。 -/
theorem aq3 (L : fgraph ℕ) (hL : GoodList L) : aq3Concl L hL := by
  intro N r x hgn hm s hs
  -- `aq3Concl` 无 `all uniq L` 槽：由 `IsRestricted.simple` + `simple ↔ all uniq` 现取
  have hunL : ∀ l ∈ L, l.Nodup :=
    (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin] at hs
    exact hm.1.2.1.2.2.1 s hs
  · rw [ntrans1 L N r x hfin] at hs
    rcases List.mem_append.mp hs with hs1 | hs1
    · rcases memReplaceCases hs1 with hN | ⟨_, hsf2⟩
      · exact hm.1.2.1.2.2.1 s hN
      · rcases List.mem_cons.mp hsf2 with rfl | h0
        · exact aq3Split2FLastClean L hL hgn hunL hm hfin
        · exact absurd h0 (by simp)
    · rcases List.mem_cons.mp hs1 with rfl | h0
      · exact fLastSplit1 L hL hgn hunL hm hfin
      · exact absurd h0 (by simp)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq3

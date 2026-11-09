/-
  JcajyduAqLeaf8W3u — AQ8 波 3u：junction ⑤ 的两个基础私引理 + 主件（三支）。

  ┌─ 本版缺失的公开件（探针 logs/probe_w3u.log 实测）────────────────
  │ `List.head!_drop` / `List.head!_take` / `List.drop_succ` / `List.getD_zero`
  │ 均 Unknown；`List.getD_cons_succ` / `List.take_succ_cons` / `List.drop_zero`
  │ / `List.head!_cons` 在库。⇒ P1/P2 私证（各 5 行，`cases` 后全 rfl 级）。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① head!_drop_getD (私)  `(l.drop k).head! = l.getD k default`
  │ ② head!_take_pos  (私)  `0 < m → (l.take m).head! = l.head!`
  │ ③ aq8w3u_betwnFaceHead  `between f y z` 非空 ⇒ `其 head! = nextEl f y`
  │    （= `fList L y`，f = 面表）——junction ⑤ 的核心
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3u_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3l
import Kepler.Text.TameSpine.JcajyduBetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup mem_darts_of_mem_findFace)

/-! ## §0 两个基础私引理（本版无公开件） -/

/-- `(l.drop k).head! = l.getD k default`（`drop`/`getD` 均按表递归，`cases` 后 rfl 级）。 -/
theorem aq8w3u_head!_drop_getD {α : Type} [Inhabited α] (l : List α) (k : ℕ) :
    (l.drop k).head! = l.getD k default := by
  induction k generalizing l with
  | zero => cases l <;> rfl
  | succ k ih =>
    cases l with
    | nil => rfl
    | cons a t => exact ih t

/-- `0 < m ⇒ (l.take m).head! = l.head!`（`take` 按表/下标双递归，`cases` 后 rfl 级）。 -/
theorem aq8w3u_head!_take_pos {α : Type} [Inhabited α] (l : List α) {m : ℕ}
    (hm : 0 < m) : (l.take m).head! = l.head! := by
  cases l with
  | nil => simp
  | cons a t =>
    cases m with
    | zero => omega
    | succ m' => rfl

/-! ## §1 junction ⑤ 主件（本波未落，见 DELIVERY §AQ8W3u-1）

三支结构已定形；主件落体前的三处修正已登记（P2 nil 支、`drop_eq_nil_iff` 用法、
`hm0` 的非空来源改为「take 非空 ⇒ length_take > 0 ⇒ m > 0」）。 -/

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3u_head!_drop_getD
#print axioms Kepler.Text.TameSpine.aq8w3u_head!_take_pos

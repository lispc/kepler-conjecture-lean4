/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12A — AQ12 叶 W1a（`eq_last_next`）。

  锚：reference/flyspeck/text_formalization/tame/AQ12.hl:39-:159（121 HOL 行）
  `eq_last_next`：
  `!s r. uniq r /\ uniq s /\ (!x. MEM x s <=> MEM x r) /\
    (!x. MEM x s ==> next_el s x = next_el r x) /\ LAST s = LAST r ==> s = r`
  ——「同一元素集 + 同一后继 + 同一 LAST ⇒ 同一条循环表」。

  ┌─ 命名（编排者 2026-11-09 指令）──────────────────────────────────
  │ 本件按 **中立前缀 `aqs_`** 落：`eq_last_next` 在 HOL 全树的消费者是
  │ AQ12 自己的 `map_betwn`（:351）与 `betwn_cap_point`（:987），而
  │ `betwn_cap_point` 被 **reduction3.hl** 消费（J2 下游）；另 AQ13 的
  │ helper 闭包经 `exists_contour_combinatoric` 不需要它。即本件是
  │ 「AQ12 + 下游」共享件，不挂 `aq12_` 叶名。
  └────────────────────────────────────────────────────────────────

  ┌─ 证明路线（与 HOL 的分支法不同，Lean 侧改「LAST 起沿后继行走」）──
  │ HOL（:41-:159）是 `LIST_INDUCT_TAC` + `TL r = []` 八支情形分析，
  │ 依赖 next_el_cat_last1/2、next_el_last_hd、CONS_HD_TL 等。
  │ Lean 侧走等价的干净路线（AGENTS §8「原版思路是路线参考」）：
  │ ① 两边 `Nodup` + 同成员 ⇒ `s.Perm r`（`List.Subperm.antisymm`）；
  │ ② 令 `L = getLast`（由 `LAST s = LAST r` 与 `getLast!EqGetLast` 对齐）；
  │ ③ 归纳证明 `(nextEl s)^[k] L = (nextEl r)^[k] L`（步进用假设 hnext，
  │    成员性由本文件 universe-多态的 `aqs_memNextElIterate`）；
  │ ④ 「行走引理」`s[i] = (nextEl s)^[i+1] L`（`idxOf` 沿迭代的模长平移
  │    `idxOfNextElMod` + `idxOf getLast = n-1` + `getElem_idxOf`）；
  │ ⑤ `List.ext_getElem` 收口（k = i+1，(n-1)+(i+1) ≡ i mod n）。
  └────────────────────────────────────────────────────────────────

  载体折算：`LAST` ↦ `List.getLast!`（HOL 的 total LAST；非空支经
  `getLast!EqGetLast` 转 `getLast`，空表由成员等价直接 `s = r = []`）；
  `next_el` ↦ `Kepler.Assembly.nextEl`；`uniq` ↦ `List.Nodup`。
  泛型实例沿 TameLp/TameList3 约定：`[BEq α] [LawfulBEq α] [DecidableEq α]`；
  `getLast!` 需 `[Inhabited α]`（消费点 α = ℕ × ℕ 均齐备）。

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameLp
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList5

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl)

/-! ## §0 私件：idxOf 沿 nextEl 迭代的模长平移 + LAST 位 -/

/-- `(a % n + 1) % n = (a + 1) % n`（模后继平移；同证重推导，per-file private 约定）。 -/
private theorem aqs_modSuccMod (a n : ℕ) : (a % n + 1) % n = (a + 1) % n := by
  have h : a + 1 = n * (a / n) + (a % n + 1) := by
    have := Nat.div_add_mod a n
    omega
  rw [h, Nat.add_comm (n * (a / n)), Nat.add_mul_mod_self_left]

/-- `nextEl` 迭代不出表（`aq10_memNextElIterate` 的 universe-多态孪生；
`aq10_*` 版本钉在 `Type`，本件泛型 `Type*` 需本合同证重推导）。 -/
private theorem aqs_memNextElIterate {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem ih

/-- `idxOf` 沿 `nextEl` 迭代的模长平移：
`s.idxOf ((nextEl s)^[k] x) = (s.idxOf x + k) % s.length`（TameList 系同证重推导）。 -/
private theorem aqs_idxOfNextElIterate {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hnd : s.Nodup) (hx : x ∈ s) :
    ∀ k : ℕ, s.idxOf ((nextEl s)^[k] x) = (s.idxOf x + k) % s.length := by
  intro k
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.add_zero,
      Nat.mod_eq_of_lt (List.idxOf_lt_length_iff.mpr hx)]
  | succ k ih =>
    rw [Function.iterate_succ_apply', idxOfNextElMod hnd (aqs_memNextElIterate hx k), ih,
      ← Nat.add_assoc, aqs_modSuccMod]

/-- `LAST` 在表内的位置：`s.idxOf (getLast s) = s.length - 1`。 -/
private theorem aqs_idxOfGetLast {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} (hnd : s.Nodup) (hne : s ≠ []) :
    s.idxOf (s.getLast hne) = s.length - 1 := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  rw [List.getLast_eq_getElem hne]
  exact Kepler.Text.TameLp.idxOf_getElem hnd (by omega)

/-- `getElem` 的索引相等搬运（依赖索引的 `rw` 会被 proof 参数卡住，故显式给出）。 -/
private theorem aqs_getElem_congr_idx {α : Type*} {s : List α} {i j : ℕ} (h : i = j)
    (hi : i < s.length) (hj : j < s.length) : s[i]'hi = s[j]'hj := by
  cases h
  rfl

/-- 行走引理：`s[i] = (nextEl s)^[i+1] (getLast s)`（i < |s|，s 非空）。
从 `getLast` 出发沿后继走 `i+1` 步，正好落在 `(n-1) + (i+1) ≡ i (mod n)` 位。 -/
private theorem aqs_getElem_eq_walk {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} (hnd : s.Nodup) (hne : s ≠ []) (i : ℕ) (hi : i < s.length) :
    s[i] = (nextEl s)^[i + 1] (s.getLast hne) := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  have hLs : s.getLast hne ∈ s := List.getLast_mem hne
  have hwalk : (nextEl s)^[i + 1] (s.getLast hne) ∈ s :=
    aqs_memNextElIterate hLs (i + 1)
  have hidx : s.idxOf ((nextEl s)^[i + 1] (s.getLast hne)) = i := by
    rw [aqs_idxOfNextElIterate hnd hLs (i + 1), aqs_idxOfGetLast hnd hne]
    have e : s.length - 1 + (i + 1) = s.length + i := by omega
    rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt hi]
  have hj : s.idxOf ((nextEl s)^[i + 1] (s.getLast hne)) < s.length :=
    List.idxOf_lt_length_iff.mpr hwalk
  calc s[i] = s[s.idxOf ((nextEl s)^[i + 1] (s.getLast hne))] :=
        aqs_getElem_congr_idx hidx.symm hi hj
    _ = (nextEl s)^[i + 1] (s.getLast hne) := Kepler.Text.TameLp.getElem_idxOf hwalk

/-! ## §1 AQ12.hl:39 `eq_last_next` -/

/-- **HOL `eq_last_next`**（AQ12.hl:39-:159）：`uniq r ∧ uniq s ∧
(∀ x, x ∈ s ↔ x ∈ r) ∧ (∀ x ∈ s, next_el s x = next_el r x) ∧
LAST s = LAST r ⇒ s = r`——同一循环表的「元素集 + 后继 + LAST」三不变式刻画
（AQ12 `map_betwn`/`betwn_cap_point` 的消费马；后者经 reduction3 进 J2 下游）。 -/
theorem aqs_eq_last_next {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] [Inhabited α]
    {s r : List α} (hr : r.Nodup) (hs : s.Nodup) (hmem : ∀ x, x ∈ s ↔ x ∈ r)
    (hnext : ∀ x, x ∈ s → nextEl s x = nextEl r x)
    (hlast : s.getLast! = r.getLast!) : s = r := by
  -- 同成员 + 双 Nodup ⇒ Perm ⇒ 同长
  have hperm : s.Perm r :=
    List.Subperm.antisymm (hs.subperm fun x hx => (hmem x).mp hx)
      (hr.subperm fun x hx => (hmem x).mpr hx)
  have hlen : s.length = r.length := hperm.length_eq
  by_cases hsne : s = []
  · -- 空表支：成员等价 ⇒ r 也空
    have hr0 : r = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
      have h : x ∈ s := (hmem x).mpr hx
      rw [hsne] at h
      exact List.not_mem_nil h
    rw [hsne, hr0]
  · have hrne : r ≠ [] := by
      intro hr0
      exact hsne (List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
        have h : x ∈ r := (hmem x).mp hx
        rw [hr0] at h
        exact List.not_mem_nil h)
    -- `LAST` 对齐到 `getLast`
    have hL : s.getLast hsne = r.getLast hrne := by
      rw [← getLast!EqGetLast hsne, ← getLast!EqGetLast hrne]
      exact hlast
    -- 从 LAST 出发的后继迭代在两边相同
    have hiter : ∀ k : ℕ,
        (nextEl s)^[k] (s.getLast hsne) = (nextEl r)^[k] (r.getLast hrne) := by
      intro k
      induction k with
      | zero => simpa using hL
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        exact hnext _ (ih ▸ aqs_memNextElIterate (List.getLast_mem hsne) k)
    -- 逐位相等 ⇒ 表相等
    refine List.ext_getElem hlen (fun i hi hir => ?_)
    rw [aqs_getElem_eq_walk hs hsne i hi, aqs_getElem_eq_walk hr hrne i hir, hiter (i + 1)]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx——本件零消费 TameList16:1109 债链。） -/
#print axioms Kepler.Text.TameSpine.aqs_eq_last_next

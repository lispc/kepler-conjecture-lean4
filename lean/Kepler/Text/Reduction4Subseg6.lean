/-
  Kepler.Text.Reduction4Subseg6 — J 战役 J1 板 F3（reduction4.hl `rot_core`）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl:3873`）──
  │ `rot_core` → rot_core
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（HOL 证体逐句转写）─────────────────────────────────────
  │ 令 `m = k % sizel r`。`r' = rot k r = drop m r ++ take m r`
  │ （`List.rotate_eq_drop_append_take_mod`，无 `k ≤ sizel` 副作用条件；
  │  HOL 的 `Seq.rot` 带该条件，故本树取 mod 形）、
  │ `r = take m r ++ drop m r`（`List.take_append_drop`）。两次 `core_cat`：
  │   · `core L r  = core L (take m) ++ core L (drop m)`
  │   · `core L r' = core L (drop m) ++ core L (take m)`
  │ 两次的切口条件都用「旋转不改 `next_el`」+ 题设的两个
  │ `next_el … ≠ f_list …` 供给（HOL `Seq2.next_el_rot_eq`；本岛自建
  │ `nextEl_rotate`，下沿 = public 的 `TameLp.la7_nextEl_rotOne` 单步件）。
  │ 收尾 `k' = (core L (take m r)).length` + `List.rotate_append_length_eq`
  │ （= HOL `Seq.rot_size_cat`：`(A ++ B).rotate A.length = B ++ A`）。
  │ 退化支 `m = 0` 取 `k' = 0`（此时 `r' = r`）。`m < sizel r` 保证
  │ `drop m r`/`take m r` 都非空，故只有一个退化支（比 HOL 少一支）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；载体全具体（`Dart = ℕ × ℕ`）。
  环安全：新增 import 只有 `Kepler.Graphs.FaceDivisionProps4`（`getLast!_append_of_ne_nil`
  = HOL `LAST_cat`）——其 Kepler.* 闭包实测 13 个 Graphs 模块，零 `Kepler.Assembly`、
  零 `Kepler.Text.TameSpine.*`。
-/

import Kepler.Text.Reduction4Subseg5
import Kepler.Graphs.FaceDivisionProps4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph getLast!_append_of_ne_nil)
open Kepler.Assembly (nextEl fList eList)
open Kepler.Text.Reduction5 (Dart parts core)
open Kepler.Text.TameLp (la7_nextEl_rotOne)

/-! ## §0 旋转不变式（HOL `Seq2.next_el_rot_eq`，seq2-compiled.hl:1866） -/

/-- `uniq l ⇒ next_el (rot n l) = next_el l`（函数等）。下沿 =
`TameLp.la7_nextEl_rotOne`（单步；`la7RotOne l = l.rotate 1`）+ `List.rotate_rotate` 归纳。 -/
private theorem nextEl_rotate (l : List Dart) (hn : l.Nodup) :
    ∀ n : ℕ, nextEl (l.rotate n) = nextEl l := by
  intro n
  induction n with
  | zero => rw [List.rotate_zero]
  | succ k ih =>
    have h1 : nextEl ((l.rotate k).rotate 1) = nextEl (l.rotate k) :=
      funext (la7_nextEl_rotOne (List.nodup_rotate.mpr hn))
    rw [← List.rotate_rotate, h1, ih]

/-! ## §1 `rot_core`（reduction4.hl:3873） -/

/-- **HOL `rot_core`**（reduction4.hl:3873）：
`uniq r`、`r ≠ []`、`rot k r = r'`、两个「末元处不接 `f_list`」条件
⇒ `∃ k', rot k' (core L r) = core L r'`。

证体见文件头路线表：`m = k % sizel r`，两次 `core_cat` 把 `core L r` /
`core L r'` 拆成 `(take m)`/`(drop m)` 段的两种拼接，收尾
`List.rotate_append_length_eq`（HOL `Seq.rot_size_cat`）把 `A ++ B` 旋到 `B ++ A`。 -/
theorem rot_core (L : fgraph ℕ) {r r' : List Dart} {k : ℕ}
    (hnd : r.Nodup) (hne : r ≠ []) (hrot : r.rotate k = r')
    (hbrk : nextEl r (r.getLast!) ≠ fList L (eList (r.getLast!)))
    (hbrk' : nextEl r' (r'.getLast!) ≠ fList L (eList (r'.getLast!))) :
    ∃ k', (core L r).rotate k' = core L r' := by
  have hlen_pos : 0 < r.length := List.length_pos_of_ne_nil hne
  have hmod_lt : k % r.length < r.length := Nat.mod_lt _ hlen_pos
  -- `r' = drop m ++ take m`（`m = k % sizel r`；mod 形免 `k ≤ sizel` 条件）
  have hr' : r' = r.drop (k % r.length) ++ r.take (k % r.length) := by
    rw [← hrot]
    exact List.rotate_eq_drop_append_take_mod
  by_cases hm0 : k % r.length = 0
  · -- 退化支：`r' = r`
    refine ⟨0, ?_⟩
    have hrr : r' = r := by
      rw [hr', hm0, List.drop_zero, List.take_zero, List.append_nil]
    rw [List.rotate_zero, hrr]
  · -- 主支：两段都非空
    have htake_ne : r.take (k % r.length) ≠ [] := by
      intro h
      rcases List.take_eq_nil_iff.mp h with h1 | h1
      · exact hm0 h1
      · exact hne h1
    have hdrop_ne : r.drop (k % r.length) ≠ [] := by
      intro h
      have hpos : 0 < (r.drop (k % r.length)).length := by
        rw [List.length_drop]
        omega
      rw [h] at hpos
      simp at hpos
    have hd : r = r.take (k % r.length) ++ r.drop (k % r.length) :=
      (List.take_append_drop _ r).symm
    have hnd' : r'.Nodup := by
      rw [← hrot]
      exact List.nodup_rotate.mpr hnd
    have hrotfun : ∀ x, nextEl r' x = nextEl r x := by
      intro x
      rw [← hrot]
      exact congrFun (nextEl_rotate r hnd k) x
    have hnd_td : (r.take (k % r.length) ++ r.drop (k % r.length)).Nodup := by
      rw [← hd]
      exact hnd
    have hnd_dt : (r.drop (k % r.length) ++ r.take (k % r.length)).Nodup := by
      rw [← hr']
      exact hnd'
    -- 第二支切口：`take` 段末元 = `r'` 末元
    have hgl_take : (r.take (k % r.length)).getLast! = r'.getLast! := by
      rw [hr', getLast!_append_of_ne_nil htake_ne]
    have hbrk2 : nextEl (r.take (k % r.length) ++ r.drop (k % r.length))
        ((r.take (k % r.length)).getLast!) ≠
        fList L (eList ((r.take (k % r.length)).getLast!)) := by
      rw [List.take_append_drop, hgl_take]
      intro h
      exact hbrk' ((hrotfun _).trans h)
    -- 第一支切口：`drop` 段末元 = `r` 末元
    have hgl_drop : (r.drop (k % r.length)).getLast! = r.getLast! := by
      have h := getLast!_append_of_ne_nil (l₁ := r.take (k % r.length)) hdrop_ne
      rw [List.take_append_drop] at h
      exact h.symm
    have hbrk1 : nextEl (r.drop (k % r.length) ++ r.take (k % r.length))
        ((r.drop (k % r.length)).getLast!) ≠
        fList L (eList ((r.drop (k % r.length)).getLast!)) := by
      rw [← hr', hgl_drop]
      intro h
      exact hbrk ((hrotfun _).symm.trans h)
    have hcat2 : core L r = core L (r.take (k % r.length)) ++ core L (r.drop (k % r.length)) := by
      have h := core_cat L (u := r.take (k % r.length)) (v := r.drop (k % r.length))
        hnd_td htake_ne hbrk2
      simpa using h
    have hcat1 : core L r' = core L (r.drop (k % r.length)) ++ core L (r.take (k % r.length)) := by
      have h := core_cat L (u := r.drop (k % r.length)) (v := r.take (k % r.length))
        hnd_dt hdrop_ne hbrk1
      rwa [← hr'] at h
    refine ⟨(core L (r.take (k % r.length))).length, ?_⟩
    rw [hcat2, List.rotate_append_length_eq, hcat1]

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.rot_core

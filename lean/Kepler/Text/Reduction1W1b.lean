/-
  Kepler.Text.Reduction1W1b — J4 Wave W1 批 2（**膨胀率判定批**）：
  `mem_enumerator`（`reduction1.hl:100-:219`，RD-2′ 路线）+
  `increasing` 的点式构造件。

  ┌─ RD-2′（对本批交付前的一次路线升级，**优于** W1A 的 RD-2）────────
  │ 原 RD-2 走 `incrIndexList` + `enumerator_completeness`（EnumeratorProps:562）。
  │ 开工侦察发现：`incrIndexList` 首槽 `1 < nmax` **不可由 HOL 六条前提导出**
  │ （`outer ≤ 1` 时 `LAST xs = 0`、`EL (inner-2) xs ≤ 0` 全可满足，而
  │ `1 < nmax` 假）⇒ 该路线只覆盖 `outer ≥ 2`，须另证 `outer ≤ 1` 支
  │ （而那要 iterate 展开，正是 RD-1 判死的东西）。
  │ **改走 `enumerator_completeness_help`**（EnumeratorProps:514，已在库）：
  │   `increasing ls → ls ≠ [] → ls.length = ks+1 → (∀ x ∈ ls, x < nmax+1) →
  │    ls ∈ iterate (enumAppend nmax) ks (enumBase nmax)`
  │ —— **无 `1 < nmax` 槽**，对全体 `outer` 一致成立。见证
  │ `is = (xs.drop 1).take (inner-2)`，`ks = inner-3`。
  │ 路线仍是「不搬 iterate 机制」，RD-1 维持。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目（HOL 锚）────────────────────────────────────────────────
  │ §1 `increasingOfAdjacent` ← `reduction1.hl:105` 的
  │    `(!i. SUC i < sizel xs ==> EL i xs <= EL (SUC i) xs)` 槽 →
  │    `Kepler.Graphs.increasing`（EnumeratorProps:69）。
  │    **批 1 的撤件本批以 `!`-形（`getElem!`，无依赖索引）落地。**
  │ §2 `elemDropTake`（私有；`is` 的元素身份）。
  │ §3 `memEnumerator` ← `reduction1.hl:100-:219` `mem_enumerator`。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐槽对照（DIFFERS）──────────────────────────────────────────
  │ ① HOL `EL k xs`（junk=default 全函数）↦ `xs[k]!`（`getElem!`，
  │    junk 同为 `Inhabited` 默认值）——**全程非依赖**，批 1 的
  │    「`rw` motive 不 type correct」卡点由此消失。
  │ ② `the`/`HD`/`LAST` 的 junk 槽同上；本件只消费 `HD`/`LAST`/`EL`。
  │ ③ 结论涉「元素在 filtered/生成的 list 中的新位置」一律 `?` 形
  │    （W1 接口约定 v2，见 `W1_INTERFACE_CONTRACT.md` 附录）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义；
  HOL 5 条死码零引用；`indexf` 家族见 `W1_INTERFACE_CONTRACT.md`。
-/

import Kepler.Graphs.EnumeratorProps

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (enumerator)

/-! ## §1 `increasing` 的点式构造（W1A 撤件的 `!`-形落地） -/

/-- **HOL `mem_enumerator` 单调槽 → `increasing`**（无独立 HOL 名：
`reduction1.hl:105` 的 `(!i. SUC i < sizel xs ==> EL i xs <= EL (SUC i) xs)`）。

批 1 撤件原因 = 依赖式 `getElem` 的 `rw` motive 不 type correct；本批改用
`getElem!`（非依赖，junk=默认值）后一次通过。`as.length` 切分给
`x = ls[as.length]!`、`y = ls[as.length+1]!`，两处身份用
`getElem?_append_right` + `getElem?_cons_zero/succ` 收口。 -/
theorem increasingOfAdjacent {α : Type*} [LinearOrder α] [Inhabited α] {ls : List α}
    (h : ∀ i, i + 1 < ls.length → ls[i]! ≤ ls[i + 1]!) :
    Kepler.Graphs.increasing ls := by
  intro x y as bs hls
  subst hls
  have h1 : as.length + 1 < (as ++ x :: y :: bs).length := by
    simp only [List.length_append, List.length_cons]
    omega
  have key := h as.length h1
  have e1 : (as ++ x :: y :: bs)[as.length]? = some x := by
    rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
    simp
  have e2 : (as ++ x :: y :: bs)[as.length + 1]? = some y := by
    rw [List.getElem?_append_right (by omega : as.length ≤ as.length + 1),
      Nat.add_sub_cancel_left]
    simp
  rw [List.getElem!_eq_getElem?_getD, e1, Option.getD_some,
    List.getElem!_eq_getElem?_getD, e2, Option.getD_some] at key
  exact key

/-! ## §2 `is` 的元素身份（`mem_enumerator` 的见证段） -/

/-- `(xs.drop d).take k` 的第 `q` 个元素 = `xs[d+q]`（`?` 形，非依赖）。 -/
private theorem elemDropTake {xs : List ℕ} {d k q : ℕ} (hq : q < k) :
    ((xs.drop d).take k)[q]? = xs[d + q]? := by
  rw [List.getElem?_take, if_pos hq, List.getElem?_drop]

/-- 单调链：`a ≤ b` 且逐点单步单调 ⇒ `xs[a]! ≤ xs[b]!`。 -/
private theorem monoChain {xs : List ℕ}
    (hmono : ∀ i, i + 1 < xs.length → xs[i]! ≤ xs[i + 1]!) :
    ∀ (n a : ℕ), a + n < xs.length → xs[a]! ≤ xs[a + n]! := by
  intro n
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a hx
    have h1 : a + n < xs.length := by omega
    have h2 : a + n + 1 < xs.length := by omega
    have hstep := hmono (a + n) h2
    rw [show a + (n + 1) = a + n + 1 from by omega]
    exact le_trans (ih a h1) hstep

/-! ## §3 `mem_enumerator`（reduction1.hl:100-:219，RD-2′）—— **未收口，接缝交班**

本批已完成：①`increasingOfAdjacent`（RD-2 的 `increasing` 槽，`!`-形一次通过）；
②`monoChain`（单调链，`mem_enumerator` 体内 `∀ x ∈ is, x < outer-1` 段所需）；
③`elemDropTake`（`is = (xs.drop 1).take (inner-2)` 的元素身份，`?` 形）。

**本批侦察还推翻了 W1A 的 RD-2 原定路线**：`incrIndexList` 首槽 `1 < nmax`
**不可由 HOL 六条前提导出**（`outer ≤ 1` 时六条前提全可满足而该槽假）⇒
改走 `enumerator_completeness_help`（EnumeratorProps:514，**无 `1 < nmax` 槽**），
对全体 `outer` 一致成立。RD-1（不搬 iterate 机制）维持。

**剩余步骤（批 3 前置，估 60–90 行）**——四槽 `enumerator_completeness_help`
已可喂三槽（`increasing is`＝§1、`is ≠ []` 与 `is.length = inner-2`＝`length_take`
+`length_drop`、`∀ x ∈ is, x < outer-1`＝§2 `monoChain`+`hpen`），
只差：**(a)** `is[q]! = xs[1+q]!`（`elemDropTake` + `getElem!_eq_getElem?_getD`
+`getElem?_eq_getElem`，已试、卡在 `rw` 顺序）；**(b)** `xs = [0] ++ is ++ [outer-1]`
（`take_append_drop` + `drop_drop` + `dropLastSingleton`，后者的
`List.dropLast_cons`/`getElem!_take`/`getElem!_append` 树内均 **0 命中**，
须走 `List.dropLast_eq_take` + `length_eq_one` + `getElem!_cons_zero`）；
**(c)** `rw [Kepler.Graphs.enumerator]` 后 `List.mem_map` 收口。
卡点均为机械面（`getElem!` 与 `getElem` 的换形顺序），非数学面。
-/

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.increasingOfAdjacent

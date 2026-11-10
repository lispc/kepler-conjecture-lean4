/-
  Kepler.Text.Reduction1W1a — J4 Wave W1 批 1。

  ┌─ 件目（HOL 锚）────────────────────────────────────────────────
  │ §1 `filterEl`   ← `reduction1.hl:777-:827`  `filter_el`
  │      `vs' = filter f vs /\ i < j < sizel vs /\ f (EL i vs) /\ f (EL j vs)`
  │      `==> ?r s. r < s /\ s < sizel vs' /\ EL i vs = EL r vs' /\ EL j vs = EL s vs'`
  └────────────────────────────────────────────────────────────────

  ┌─ W1 批 1 的两条**路线决定**（去机制，非省事）──────────────────
  │ **RD-1：`mem_enumAppend_pow`（:28-:99，72 行）不移植。**
  │   全树唯一消费者 = `mem_enumerator`（`:153`，在 `:100-:219` 内）——
  │   `grep -n mem_enumAppend_pow reduction1.hl` = `28`（定义）+ `153`（唯一用点）。
  │   `mem_enumerator` 走 RD-2 路线后**不再需要它**。硬搬的代价：结论形是
  │   `CAT a us ∈ (enumAppend nmax POWER k) iss`，而 Lean 的
  │   `Kepler.Graphs.iterate` 是 `Nat.brecOn` 原语定义、树内**零**
  │   `iterate_zero`/`iterate_succ` 展开引理（`#check` 全 unknown，
  │   见 `logs/probe_iter.log`）⇒ 搬它要先造 40–60 行 iterate 展开件，换 **0 消费者**。
  │   判定：不搬，记 DECISION。
  │ **RD-2：`mem_enumerator`（:100-:219，120 行）留 W1 批 2，走
  │   `enumerator_completeness`（EnumeratorProps:562）路线。**
  │   HOL 120 行是手搓 `LIST_INDUCT_TAC` + `BUTLAST/TL`；其内容只等于
  │   「六条前提 ⇒ `incrIndexList xs inner outer`」（~40 行）+ 一发
  │   `enumerator_completeness`。估 **50–70 行**（非 180+）。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐槽对照（DIFFERS）──────────────────────────────────────────
  │ ① `sizel` ↦ `List.length`。
  │ ② `EL k l` ↦ **`l[k]?`**（`getElem?`）。理由：HOL `EL` 是 junk-defaulting
  │    全函数，但 Lean 的依赖式 `l[k]` 在 `∃` 绑定内无法携带界证明
  │    （`∃ r s, … ∧ x = vs'[r]` 会因缺 `r < vs'.length` 而 elabor­ation 失败）。
  │    等价性：本件前提已给 `i < j < vs.length`，故 `vs[i]? = some vs[i]`；
  │    结论里的 `vs'[r]?`/`vs'[s]?` 在已证界 `r < s < vs'.length` 下同样
  │    等值于 `some (vs'[·])` ⇒ **`?` 形与 HOL `EL` 形逐点等价**（前提+已证界）。
  │ ③ `f` 在 HOL 是 `num → bool`（`f (EL i vs)` 当 Prop 用）↦ Lean
  │    `f : α → Bool`，前提写 `f vs[i] = true`（`List.filter` 的谓词载体）。
  │ ④ `(~(vs = []) ==> isSome (HD vs))` 一类头件本件无。
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义；
  HOL 5 条死码零引用。**indexf 家族**：见 `W1_INTERFACE_CONTRACT.md` §3。
-/

import Kepler.Graphs.EnumeratorProps

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

/-! ## §1 `filter_el`（reduction1.hl:777-:827） -/

/-- **HOL `filter_el`**（`reduction1.hl:777-:827`）：`filter` 保持严格下标序
（只前移不下移）。路线（**非** HOL 的 `LIST_INDUCT_TAC`+`num_CASES`）：
前缀计数 `cnt k = ((vs.take k).filter f).length`，
用 `take j = take i ++ (drop i).take (j-i)` 把 `filter` 拆前缀，两段长度单调严格。 -/
theorem filterEl {α : Type*} {f : α → Bool} {vs vs' : List α}
    (hvs' : vs' = vs.filter f) {i j : ℕ} (hij : i < j) (hj : j < vs.length)
    (hfi : f vs[i] = true) (hfj : f vs[j] = true) :
    ∃ r s, r < s ∧ s < vs'.length ∧ vs[i]? = vs'[r]? ∧ vs[j]? = vs'[s]? := by
  have hi : i < vs.length := lt_trans hij hj
  -- (a) 前缀分解：`filter` 沿 `take k` 拆两段
  have hsplit : ∀ k, k ≤ vs.length →
      vs.filter f = (vs.take k).filter f ++ (vs.drop k).filter f := by
    intro k _
    conv_lhs => rw [← List.take_append_drop k vs]
    rw [List.filter_append]
  -- (b) 真前缀里的元素：`vs[k]` 是 `drop k` 过滤后的首元
  have hhead : ∀ k (hk : k < vs.length), f vs[k] = true →
      ((vs.drop k).filter f)[0]? = some vs[k] := by
    intro k hk hx
    have hd : vs.drop k = vs[k] :: vs.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [hd, List.filter_cons, if_pos hx]
    rfl
  -- (c) `take j` 的过滤 = `take i` 的过滤 ++ `(drop i).take (j-i)` 的过滤
  have hstep : vs.take j = vs.take i ++ (vs.drop i).take (j - i) := by
    conv_lhs => rw [← List.take_append_drop i vs]
    rw [List.take_append, List.take_take, Nat.min_eq_right (le_of_lt hij),
      List.length_take, Nat.min_eq_left (le_of_lt hi)]
  refine ⟨((vs.take i).filter f).length, ((vs.take j).filter f).length, ?_, ?_, ?_, ?_⟩
  · -- r < s
    have hmem : vs[i] ∈ (vs.drop i).take (j - i) := by
      rw [List.mem_iff_getElem]
      refine ⟨0, ?_, ?_⟩
      · rw [List.length_take, List.length_drop]; omega
      · rw [List.getElem_take, List.getElem_drop]; simp
    have hfil : vs[i] ∈ ((vs.drop i).take (j - i)).filter f :=
      List.mem_filter.mpr ⟨hmem, by simpa using hfi⟩
    have happ : (vs.take j).filter f
        = (vs.take i).filter f ++ ((vs.drop i).take (j - i)).filter f := by
      rw [hstep, List.filter_append]
    rw [happ, List.length_append]
    have hpos : 0 < (((vs.drop i).take (j - i)).filter f).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem hfil)
    omega
  · -- s < vs'.length
    have h1 : vs'.length = ((vs.take j).filter f).length
        + ((vs.drop j).filter f).length := by
      rw [hvs', hsplit j (le_of_lt hj), List.length_append]
    have hmem : vs[j] ∈ (vs.drop j).filter f := by
      have hd : vs.drop j = vs[j] :: vs.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [hd, List.filter_cons, if_pos hfj]
      exact List.mem_cons_self ..
    have hpos : 0 < ((vs.drop j).filter f).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
    omega
  · -- vs[i]? = vs'[r]?
    have h1 : vs'.length = ((vs.take i).filter f).length
        + ((vs.drop i).filter f).length := by
      rw [hvs', hsplit i (le_of_lt hi), List.length_append]
    have hget : vs'[((vs.take i).filter f).length]?
        = ((vs.drop i).filter f)[0]? := by
      rw [hvs', hsplit i (le_of_lt hi), List.getElem?_append_right (le_refl _), Nat.sub_self]
    rw [hget, hhead i hi hfi, List.getElem?_eq_getElem hi]
  · -- vs[j]? = vs'[s]?
    have h1 : vs'.length = ((vs.take j).filter f).length
        + ((vs.drop j).filter f).length := by
      rw [hvs', hsplit j (le_of_lt hj), List.length_append]
    have hget : vs'[((vs.take j).filter f).length]?
        = ((vs.drop j).filter f)[0]? := by
      rw [hvs', hsplit j (le_of_lt hj), List.getElem?_append_right (le_refl _), Nat.sub_self]
    rw [hget, hhead j hj hfj, List.getElem?_eq_getElem hj]

/-! ## §2 未落件（接缝，批 2 处理）

`increasingOfAdjacent`（本批试做，**撤件**）：`increasing` 的点式充分条件，
服务 RD-2 的 `incrIndexList` 构造。Lean 卡点 = **依赖式 `getElem` 的 rewrite
motive 不 type correct**（AGENTS §7.1-#10 同款）：`h : ∀ i (h1) (h2),
ls[i]'h1 ≤ ls[i+1]'h2` 的实例在 `ls = as ++ x :: y :: bs` 处要 `rw`
`List.getElem_append_right`，motive 跨 `i` 依赖而失败（已试 3 种写法：
无界 getElem 报 elaboration 缺证明；`'h` 显式证明版卡在 rw motive）。
**批 2 的正确路线**：走 `getElem?` + `Option` 形式重述前提
（`∀ i, ls[i]? = some a → ls[i+1]? = some b → a ≤ b`，全程非依赖），
或在 `increasing` 的 `as`/`bs` 分解上直接做 `List.take`/`List.drop`
算术（`x = ls[as.length]` 用 `List.getElem_append_right` 的**等式两端**
各自 `show`，不做 `rw`）。估 20–30 行。 -/

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.filterEl

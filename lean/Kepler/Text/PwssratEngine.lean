/-
  Kepler.Text.PwssratEngine — 铺装 batch B：r_rtrans_eq 前置 engines（件 3 剩余四件）

  PLAN-P7 §6 件 3（裁决：batch B）。`fListPowerNextEl` 已于 patch7 落
  （`fListPowEqNextElPow`），本批补其余四件。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ tame_list.hl:14016 `final_list_power_fn`    → finalListPowerFn
  │ more_lemma1.hl:818 `mem_prev_power`         → memPrevPower
  │ more_lemma1.hl:830 `sym_power_prev_next`    → symPowerPrevNext
  │ PWSSRAT.hl:449     `minnum_not`            → minnumNot
  │ （消费面：More_lemma1.r_rtrans_eq_thm 证体 4 处；T1 主机等 scout 落簇后直供。）
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；链侧载体；零直接 TameSpine import。
-/

import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction5
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Assembly (nextEl prevEl fList)
open Kepler.Text.Reduction5 (Dart finalList)

/-! ## §1 `final_list_power_fn`（tame_list.hl:14016） -/

/-- **HOL `Tame_list.final_list_power_fn`**（tame_list.hl:14016）：
`final_list L r ⇒ ∀ d ∈ r, (f_list L)^i d = (next_el r)^i d`。
归纳步：`f_list d = next_el r d`（final）后用 `next_el` 保成员性喂 IH。 -/
theorem finalListPowerFn (L : fgraph ℕ) (i : ℕ) {r : List Dart}
    (hf : finalList L r) :
    ∀ d ∈ r, (fList L)^[i] d = (nextEl r)^[i] d := by
  induction i with
  | zero => intro d _; rfl
  | succ k ih =>
    intro d hd
    rw [Function.iterate_succ_apply (fList L),
      Function.iterate_succ_apply (nextEl r), hf d hd]
    exact ih (nextEl r d) (Kepler.Text.TameLp.nextEl_mem_of_mem hd)

/-! ## §2 `mem_prev_power`（more_lemma1.hl:818）与
`sym_power_prev_next`（more_lemma1.hl:830） -/

/-- **HOL `mem_prev_power`**（more_lemma1.hl:818）：`d ∈ r ⇒
∀ n, (prev_el r)^n d ∈ r`（HOL 的 `uniq r` 前提在证体中未用——加强形）。 -/
theorem memPrevPower {r : List Dart} {d : Dart} (hd : d ∈ r) :
    ∀ n : ℕ, (prevEl r)^[n] d ∈ r := by
  intro n
  induction n with
  | zero => simpa using hd
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Text.Reduction5.memPrevEl ih

/-- **HOL `sym_power_prev_next`**（more_lemma1.hl:830）：
`uniq r ∧ d,z ∈ r ⇒ ((prev_el r)^n d = z ↔ (next_el r)^n z = d)`。
证体：两条互逆幂等式（`nextPrevId`/`prevNextId` + 成员性归纳）。 -/
theorem symPowerPrevNext {r : List Dart} {d z : Dart} (hr : r.Nodup)
    (hd : d ∈ r) (hz : z ∈ r) :
    ∀ n : ℕ, ((prevEl r)^[n] d = z ↔ (nextEl r)^[n] z = d) := by
  have key1 : ∀ n : ℕ, ∀ w ∈ r, (nextEl r)^[n] ((prevEl r)^[n] w) = w := by
    intro n
    induction n with
    | zero => intro w _; rfl
    | succ k ih =>
      intro w hw
      rw [Function.iterate_succ_apply (prevEl r),
        Function.iterate_succ_apply' (nextEl r),
        ih (prevEl r w) (Kepler.Text.Reduction5.memPrevEl hw)]
      exact Kepler.Text.TameLp.nextEl_prevEl hr hw
  have key2 : ∀ n : ℕ, ∀ w ∈ r, (prevEl r)^[n] ((nextEl r)^[n] w) = w := by
    intro n
    induction n with
    | zero => intro w _; rfl
    | succ k ih =>
      intro w hw
      rw [Function.iterate_succ_apply' (prevEl r),
        Function.iterate_succ_apply (nextEl r),
        ih (nextEl r w) (Kepler.Text.TameLp.nextEl_mem_of_mem hw)]
      exact Kepler.Text.TameLp.prevEl_nextEl hr hw
  intro n
  constructor
  · intro h
    have := key1 n d hd
    rwa [h] at this
  · intro h
    have := key2 n z hz
    rwa [h] at this

/-! ## §3 `minnum_not`（PWSSRAT.hl:449） -/

/-- **HOL `Pwssrat.minnum_not`**（PWSSRAT.hl:449）：
`min_num {m | P m} = n ∧ i < n ⇒ ¬ P i`（`minNum_spec` 取下界 + omega）。 -/
theorem minnumNot {P : ℕ → Prop} {n i : ℕ}
    (hn : Kepler.Text.Reduction5.minNum {m : ℕ | P m} = n) (hi : i < n) :
    ¬ P i := by
  intro hP
  have hne : {m : ℕ | P m}.Nonempty := ⟨i, hP⟩
  have hle := (Kepler.Text.Reduction5.minNum_spec hne).2 i hP
  omega

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.finalListPowerFn
#print axioms Kepler.Text.Reduction4Idx.memPrevPower
#print axioms Kepler.Text.Reduction4Idx.symPowerPrevNext
#print axioms Kepler.Text.Reduction4Idx.minnumNot

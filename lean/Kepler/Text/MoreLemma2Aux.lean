/-
  Kepler.Text.MoreLemma2Aux — J 战役 J1 第四批（M0a 首片）：
  more_lemma2.hl 闭包内的**纯 min_num / 纯 list** 件（不依赖 marked_list 族
  定义层——该层仍待 J3-D3b 裁决，见 DELIVERY-M0a §2）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──────
  │ 本片 3 件：
  │   qcdvkea.hl:32   `min_num_le`           → minNumLE
  │     （QCDVKEA 的 min_num 引擎；QCDVKEA 被 more_lemma2.hl:1911
  │      indexf_ytrans_lt_find_face 与 pnxvwfs.hl:107 消费）
  │   pplhulj.hl:78   `indexl_hd`             → indexlHd
  │     （`indexl (HD t) t = 0`；AQ8.hl:289 消费 → parts 族）
  │   Pwssrat.hl:50   `min_not_eq_imp_eq`     → minNotEqImpEq
  │     （f/g 迭代最小离轨点的等值传播；pplhulj.hl 的
  │      indexf_ytrans_eq_l_m 消费 → PPLHULJ 族）
  │ 三件均以 Reduction5Base.minNum / List 为唯一载体，零新定义。
  └────────────────────────────────────────────────────────────────

  ┌─ M0a 其余件为何不在此片（定义层阻塞，详见 DELIVERY-M0a §2）────
  │ pnxvwfs 5 件 / qcdvkea.FINAL_LIST_INDUCT+QCDVKEA / pplhulj 的
  │ marked_list_of_dart/ytran_me_f/ztran_me_f/indexf_ytrans_eq_l_m/
  │ PPLHULJ3/PPLHULJ 全部以 `marked_list` 为载体，而链世界的忠实
  │ `marked_list`（及其 normal_list/loop_list/flag_list/s_flag_list/
  │ find_list 五件子定义）正是 J3-D3b `Reduction3DefsAssumption` 头注
  │ ①的待裁决件（Spine 双载体分叉未裁）。裁决前不单方面落定义
  │ （AGENTS §2 DEF-FIX 纪律）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；泛型 binder 只
  `[BEq α] [LawfulBEq α]`（本文件仅 List.idxOf 载体，与链岛一致）；
  主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.MoreLemma2Aux

open Kepler.Text.Reduction5 (minNum minNum_spec)

/-! ## §1 min_num 件 -/

/-- **HOL `min_num_le`**（qcdvkea.hl:32）：
`min_num {m | P m} = n`、`m` 是 `{m | P m}` 的下界（`∀ i < m, ¬P i`）、
集合非空 ⇒ `m ≤ n`。QCDVKEA（more_lemma2.hl:1911 消费）的 min_num 引擎。 -/
theorem minNumLE {P : ℕ → Prop} {m n : ℕ}
    (h1 : minNum {k : ℕ | P k} = n)
    (h2 : ∀ i, i < m → ¬ P i)
    (hne : ({k : ℕ | P k} : Set ℕ).Nonempty) :
    m ≤ n := by
  have hspec := minNum_spec hne
  by_contra hmn
  have hlt : n < m := by omega
  exact absurd (h1 ▸ hspec.1) (h2 n hlt)

/-- **HOL `min_not_eq_imp_eq`**（Pwssrat.hl:50）：设 `n` 是首次使
`f^[m+2] x ≠ g (f^[m+1] x)` 的 `m`，则对一切 `i ≤ n` 有
`f^[i+1] x = g^[i] (f x)`（「离开 `g ∘ f` 轨道之前轨道吻合」）。
pplhulj.hl `indexf_ytrans_eq_l_m`（→ PPLHULJ 族）消费。 -/
theorem minNotEqImpEq {α : Type*} (f g : α → α) (x : α) {n : ℕ}
    (h : minNum {m : ℕ | f (f ((f^[m]) x)) ≠ g (f ((f^[m]) x))} = n) :
    ∀ i, i ≤ n → (f^[i + 1]) x = (g^[i]) (f x) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp
  | succ i ih =>
    intro hi
    have hi' : i ≤ n := by omega
    have hprev := ih hi'
    have hgood : f (f ((f^[i]) x)) = g (f ((f^[i]) x)) := by
      by_contra hbad
      have hmem : i ∈ {m : ℕ | f (f ((f^[m]) x)) ≠ g (f ((f^[m]) x))} := hbad
      have hle : n ≤ i := h ▸ (minNum_spec ⟨i, hmem⟩).2 i hmem
      omega
    have e : (g^[i]) (f x) = f ((f^[i]) x) := by
      rw [← hprev]
      exact Function.iterate_succ_apply' f i x
    calc (f^[i + 2]) x
        = f ((f^[i + 1]) x) := by rw [Function.iterate_succ_apply']
      _ = f ((g^[i]) (f x)) := by rw [hprev]
      _ = f (f ((f^[i]) x)) := by rw [e]
      _ = g (f ((f^[i]) x)) := hgood
      _ = g ((g^[i]) (f x)) := by rw [e]
      _ = (g^[i + 1]) (f x) := by rw [Function.iterate_succ_apply']

/-! ## §2 list 件 -/

/-- **HOL `indexl_hd`**（pplhulj.hl:78，`indexl (HD t) t = 0`）：
表首元素的首现下标为零。AQ8.hl:289 消费（→ parts 族）。 -/
theorem indexlHd {α : Type*} [BEq α] [LawfulBEq α] (a : α) (t : List α) :
    t.idxOf (t.headD a) = 0 := by
  cases t with
  | nil => rfl
  | cons b s => exact List.idxOf_cons_self

end Kepler.Text.MoreLemma2Aux

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2Aux.minNumLE
#print axioms Kepler.Text.MoreLemma2Aux.minNotEqImpEq
#print axioms Kepler.Text.MoreLemma2Aux.indexlHd

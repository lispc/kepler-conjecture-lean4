/-
  Kepler.Text.TameSpine.JcajyduAqLeaf9W1 — AQ9 波 1a：行分解 + 计数引擎（侦察件表 P1/P5）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① `aq9_rowDecomp` : `ntrans 1 = N₁ ++ [s2] ++ N₂ ++ [s1]`（行级首现分解）
  │ ② `aq9_twoPositions`（公开）：`filter` 两个不同位次 ⇒ `1 < filter 长`
  │    （位次计数引擎；替代 HOL 的「两个不同元 ⇒ 长>1」值级路线）
  └───────────────────────────────────────────────────────────────
  路线裁决：本波按 AQ9_SURVEY §4 的 Lean 原生短路线先落 P1/P5 两件引擎；
  P2/P3/P4（行覆盖/窗口双行/provenance）在 W1b。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3b
import Kepler.Text.TameSpine.JcajyduAqLeaf1B

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-- **新表行分解**（AQ9 侦察件表 P1，AQ12/AQ13 可复用）：
`ntrans 1 = N₁ ++ [s2] ++ N₂ ++ [s1]`（`r` 的首现位置换成 `s2`，`s1` 追加在后）。
`ntrans1`（list 级 replace 形）+ `aq1b_replaceSpineOfNotMem`（首现替换）。 -/
theorem aq9_rowDecomp (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∃ N₁ N₂ : List (List (ℕ × ℕ)), N = N₁ ++ r :: N₂ ∧ r ∉ N₁ ∧
      ntransSpine L N r x 1
        = N₁ ++ [(splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2]
          ++ N₂ ++ [(splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).1] := by
  obtain ⟨N₁, N₂, hN, hnot, _⟩ := aq1b_flattenNtrans1 L hL hgn hunL hm hf
  refine ⟨N₁, N₂, hN, hnot, ?_⟩
  rw [ntrans1 L N r x hf, hN, aq1b_replaceSpineOfNotMem r _ N₁ N₂ hnot]

/-- 私件：单个 `P` 命中位次给 `filter` 长 ≥ 1。 -/
private theorem aq9_onePos {α : Type*} {l : List α} {P : α → Bool} {i : ℕ}
    (hi : i < l.length) (h : P l[i] = true) : 1 ≤ (l.filter P).length :=
  List.length_pos_of_mem (List.mem_filter.mpr ⟨List.getElem_mem hi, h⟩)

/-- **位次计数引擎**（公开，AQ9 侦察件表 P5）：`filter` 的两个**不同位次**命中
⇒ `filter` 长 > 1。替代 HOL 值级路线（两个不同**元** ⇒ 长>1），
从而 AQ9 计数不需要行值互异判定（HOL ⑨⑩⑪ 三件）。 -/
theorem aq9_twoPositions {α : Type*} {P : α → Bool} (l : List α) :
    ∀ (i j : ℕ) (hij : i ≠ j) (hi : i < l.length) (hj : j < l.length),
      P l[i] = true → P l[j] = true → 1 < (l.filter P).length := by
  induction l with
  | nil =>
    intro i j _ hi
    exact absurd hi (Nat.not_lt_zero i)
  | cons a t ih =>
    intro i j hij hi hj hPi hPj
    by_cases ha : P a = true
    · rw [List.filter_cons_of_pos ha, List.length_cons]
      have h1 : 1 ≤ (t.filter P).length := by
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · subst hi0
          rcases Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega) with ⟨j', rfl⟩
          rw [List.getElem_cons_succ] at hPj
          exact aq9_onePos (by simpa using hj) hPj
        · rcases Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega) with ⟨i', rfl⟩
          rw [List.getElem_cons_succ] at hPi
          exact aq9_onePos (by simpa using hi) hPi
      omega
    · rw [List.filter_cons_of_neg ha]
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact ha hPi
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact ha hPj
      rcases Nat.exists_eq_succ_of_ne_zero hi0 with ⟨i', rfl⟩
      rcases Nat.exists_eq_succ_of_ne_zero hj0 with ⟨j', rfl⟩
      rw [List.getElem_cons_succ] at hPi hPj
      exact ih i' j' (by omega) (by simpa using hi) (by simpa using hj) hPi hPj

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq9_rowDecomp
#print axioms Kepler.Text.TameSpine.aq9_twoPositions

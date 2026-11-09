/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12J — AQ12 叶 W4b-iii（decl 29，F1 封顶件）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1340-:1386（47 HOL 行）
  `uniq(flatten r) ∧ MEM y v ∧ MEM z v1 ∧ ~(v=v1) ∧ MEM v r ∧ MEM v1 r ∧
     all nonempty r ∧ MEM d (betwn (flatten r) y z)
   ==> MEM d v ∨ MEM d (flatten (betwn r v v1)) ∨ MEM d v1`

  ┌─ 路线（与 W4b-ii 对偶的「位置⇒归属」）──────────────────────
  │ d ∈ betwn (r.flatten) y z 先化到 parts 层：取 d 所在的 parts `l`
  │ （hflat Nodup ⇒ 唯一），只需证 `l = v ∨ l ∈ betwn r v v1 ∨ l = v1`。
  │ ① flat 层两情形（`betwnTakeDrop` on r.flatten）：线性支给
  │    `idx y < idx d < idx z`，环绕支给 `idx d > idx y` 或 `idx d < idx z`；
  │ ② 用 `aqs_flatIdx_lt_of_partIdx_lt`（12I 已公开）的逆否把 flat 序翻成
  │    parts 序：`partIdx v ≤ partIdx l`（或 ≤ v1）；
  │ ③ parts 序三分：`l = v`（AQ12 leaf 第一支）/ `idx v < idx l < idx v1`
  │    ⇒ `l ∈ betwn r v v1`（`aqs_mem_between_linear`）/ `l = v1`。
  └────────────────────────────────────────────────────────────────

  复用：12I 已公开的 `aqs_idxOf_inj` / `aqs_idxOf_ge_of_mem_drop` /
  `aqs_idxOf_lt_of_mem_take` / `aqs_idxOf_mem_drop_eq` /
  `aqs_flatIdx_lt_of_partIdx_lt`（本文件零重复）。F1 封顶件。

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12I

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)

/-! ## §0 idx 范围的 take/drop 成员件 + between 的三条入口 -/

/-- `getElem` 的索引相等搬运（依赖索引的 `rw` 会卡 proof 参数，故显式给出）。 -/
private theorem aqs_getElem_congr_idx {α : Type*} {s : List α} {i j : ℕ} (h : i = j)
    (hi : i < s.length) (hj : j < s.length) : s[i]'hi = s[j]'hj := by
  cases h
  rfl

/-- `idxOf x ≥ n` 且 `x ∈ r` ⇒ `x ∈ r.drop n`。 -/
private theorem aqs_mem_drop_of_idx_le {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} (hr : r.Nodup) {x : α} {n : ℕ} (hx : x ∈ r) (h : n ≤ r.idxOf x) :
    x ∈ r.drop n := by
  have hi : r.idxOf x < r.length := List.idxOf_lt_length_iff.mpr hx
  have hlt : r.idxOf x - n < (r.drop n).length := by rw [List.length_drop]; omega
  have hnk : n + (r.idxOf x - n) < r.length := by omega
  have hget : (r.drop n)[r.idxOf x - n]'hlt = x := by
    calc (r.drop n)[r.idxOf x - n]'hlt
        = r[n + (r.idxOf x - n)]'hnk := List.getElem_drop
      _ = r[r.idxOf x]'hi := aqs_getElem_congr_idx (by omega) hnk hi
      _ = x := List.getElem_idxOf hi
  exact hget ▸ List.getElem_mem hlt

/-- `idxOf x < n` 且 `x ∈ r` ⇒ `x ∈ r.take n`。 -/
private theorem aqs_mem_take_of_idx_lt {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} (hr : r.Nodup) {x : α} {n : ℕ} (hx : x ∈ r) (h : r.idxOf x < n) :
    x ∈ r.take n := by
  have hi : r.idxOf x < r.length := List.idxOf_lt_length_iff.mpr hx
  have hlt : r.idxOf x < (r.take n).length := by rw [List.length_take]; omega
  have hget : (r.take n)[r.idxOf x]'hlt = x := by
    rw [show (r.take n)[r.idxOf x]'hlt = r[r.idxOf x]'hi from List.getElem_take]
    exact List.getElem_idxOf hi
  exact hget ▸ List.getElem_mem hlt

/-- `idxOf` 区间 ⇒ 线性支的 between 成员（parts 层）。 -/
private theorem aqs_mem_between_linear {r : List (List (ℕ × ℕ))} (hrnd : r.Nodup)
    {v v1 l : List (ℕ × ℕ)} (hv : v ∈ r) (hv1 : v1 ∈ r) (hl : l ∈ r)
    (h1 : r.idxOf v < r.idxOf l) (h2 : r.idxOf l < r.idxOf v1) : l ∈ between r v v1 := by
  have hvlt : r.idxOf v < r.idxOf v1 := lt_trans h1 h2
  have hBform : between r v v1
      = (r.drop (r.idxOf v + 1)).take (r.idxOf v1 - (r.idxOf v + 1)) := by
    rw [betwnTakeDrop hrnd hv1, if_pos hvlt]
  rw [hBform]
  have hdrop : l ∈ r.drop (r.idxOf v + 1) :=
    aqs_mem_drop_of_idx_le hrnd hl (by omega)
  have hsubidx : (r.drop (r.idxOf v + 1)).idxOf l
      < r.idxOf v1 - (r.idxOf v + 1) := by
    have heq : r.idxOf l = (r.idxOf v + 1) + (r.drop (r.idxOf v + 1)).idxOf l :=
      aqs_idxOf_mem_drop_eq hrnd hdrop
    omega
  exact aqs_mem_take_of_idx_lt ((List.drop_sublist _ _).nodup hrnd) hdrop hsubidx

/-- `idxOf` 区间 ⇒ 环绕支 between 的 drop 段（parts 层）。 -/
private theorem aqs_mem_between_wrap_left {r : List (List (ℕ × ℕ))} (hrnd : r.Nodup)
    {v v1 l : List (ℕ × ℕ)} (hv1 : v1 ∈ r)
    (hne : ¬ r.idxOf v < r.idxOf v1) (hl : l ∈ r) (h : r.idxOf v < r.idxOf l) :
    l ∈ between r v v1 := by
  have hBform : between r v v1 = r.drop (r.idxOf v + 1) ++ r.take (r.idxOf v1) := by
    rw [betwnTakeDrop hrnd hv1, if_neg hne]
  rw [hBform]
  exact List.mem_append.mpr (Or.inl (aqs_mem_drop_of_idx_le hrnd hl (by omega)))

/-- `idxOf` 区间 ⇒ 环绕支 between 的 take 段（parts 层）。 -/
private theorem aqs_mem_between_wrap_right {r : List (List (ℕ × ℕ))} (hrnd : r.Nodup)
    {v v1 l : List (ℕ × ℕ)} (hv1 : v1 ∈ r)
    (hne : ¬ r.idxOf v < r.idxOf v1) (hl : l ∈ r) (h : r.idxOf l < r.idxOf v1) :
    l ∈ between r v v1 := by
  have hBform : between r v v1 = r.drop (r.idxOf v + 1) ++ r.take (r.idxOf v1) := by
    rw [betwnTakeDrop hrnd hv1, if_neg hne]
  rw [hBform]
  exact List.mem_append.mpr (Or.inr (aqs_mem_take_of_idx_lt hrnd hl h))

/-! ## §1 HOL AQ12.hl:1340 `mem_flatten_betwn_sym_case` -/

/-- **HOL `mem_flatten_betwn_sym_case`**（AQ12.hl:1340-:1386）：
`d ∈ betwn (flatten r) y z` ⇒ `d` 落在 `v` / 环段 flatten / `v1` 三处之一。 -/
theorem aqs_memFlattenBetwnSymCase {r : List (List (ℕ × ℕ))} {v v1 : List (ℕ × ℕ)}
    {d y z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hy : y ∈ v) (hz : z ∈ v1)
    (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) (hall : ∀ l ∈ r, l ≠ [])
    (hd : d ∈ between r.flatten y z) :
    d ∈ v ∨ d ∈ (between r v v1).flatten ∨ d ∈ v1 := by
  have hrnd : r.Nodup := uniqFlatten hflat hall
  have hyS : y ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hy⟩
  have hzS : z ∈ r.flatten := List.mem_flatten.mpr ⟨v1, hv1, hz⟩
  have hdS : d ∈ r.flatten := betwnMem hd
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hdS
  suffices h : l = v ∨ l ∈ between r v v1 ∨ l = v1 by
    rcases h with h | h | h
    · exact Or.inl (h ▸ hdl)
    · exact Or.inr (Or.inl (List.mem_flatten.mpr ⟨l, h, hdl⟩))
    · exact Or.inr (Or.inr (h ▸ hdl))
  by_cases hord : r.flatten.idxOf y < r.flatten.idxOf z
  · -- flat 线性支
    have hSform : between r.flatten y z
        = (r.flatten.drop (r.flatten.idxOf y + 1)).take
            (r.flatten.idxOf z - (r.flatten.idxOf y + 1)) := by
      rw [betwnTakeDrop hflat hzS, if_pos hord]
    have hd_take : d ∈ (r.flatten.drop (r.flatten.idxOf y + 1)).take
        (r.flatten.idxOf z - (r.flatten.idxOf y + 1)) := by
      rw [hSform] at hd
      exact hd
    have hd_drop : d ∈ r.flatten.drop (r.flatten.idxOf y + 1) :=
      List.mem_of_mem_take hd_take
    have hi_yd : r.flatten.idxOf y < r.flatten.idxOf d := by
      have := aqs_idxOf_ge_of_mem_drop hflat hd_drop
      omega
    have hi_dz : r.flatten.idxOf d < r.flatten.idxOf z := by
      have hsub := aqs_idxOf_lt_of_mem_take ((List.drop_sublist _ _).nodup hflat) hd_take
      have heq := aqs_idxOf_mem_drop_eq hflat hd_drop
      omega
    have hvl : r.idxOf v ≤ r.idxOf l := by
      by_contra hcon
      push Not at hcon
      have hlt : r.idxOf l < r.idxOf v := by omega
      have := aqs_flatIdx_lt_of_partIdx_lt hflat hl hv hlt hdl hy
      omega
    have hlv1 : r.idxOf l ≤ r.idxOf v1 := by
      by_contra hcon
      push Not at hcon
      have hlt : r.idxOf v1 < r.idxOf l := by omega
      have := aqs_flatIdx_lt_of_partIdx_lt hflat hv1 hl hlt hz hdl
      omega
    rcases lt_or_eq_of_le hvl with hlt | heq
    · right
      by_cases hl1 : l = v1
      · exact Or.inr hl1
      · refine Or.inl (aqs_mem_between_linear hrnd hv hv1 hl hlt ?_)
        rcases lt_or_eq_of_le hlv1 with h' | h'
        · exact h'
        · exact absurd (aqs_idxOf_inj hrnd hl hv1 h') hl1
    · left
      exact (aqs_idxOf_inj hrnd hv hl heq).symm
  · -- flat 环绕支
    have hyz : y ≠ z := by
      intro hcon
      have hvv : v = v1 := uniqSublistUnique r hflat v hv v1 hv1 ⟨y, hy, hcon ▸ hz⟩
      exact hvne hvv
    have hne_parts : ¬ r.idxOf v < r.idxOf v1 := by
      intro hcon
      have := aqs_flatIdx_lt_of_partIdx_lt hflat hv hv1 hcon hy hz
      omega
    have hSform : between r.flatten y z
        = r.flatten.drop (r.flatten.idxOf y + 1)
          ++ r.flatten.take (r.flatten.idxOf z) := by
      rw [betwnTakeDrop hflat hzS, if_neg hord]
    rcases List.mem_append.mp (by rw [← hSform]; exact hd) with hdd | hdt
    · -- d 在 drop 段：flat idx y < idx d
      have hi_yd : r.flatten.idxOf y < r.flatten.idxOf d := by
        have := aqs_idxOf_ge_of_mem_drop hflat hdd
        omega
      have hvl : r.idxOf v ≤ r.idxOf l := by
        by_contra hcon
        push Not at hcon
        have hlt : r.idxOf l < r.idxOf v := by omega
        have := aqs_flatIdx_lt_of_partIdx_lt hflat hl hv hlt hdl hy
        omega
      rcases lt_or_eq_of_le hvl with hlt | heq
      · right
        exact Or.inl (aqs_mem_between_wrap_left hrnd hv1 hne_parts hl hlt)
      · left
        exact (aqs_idxOf_inj hrnd hv hl heq).symm
    · -- d 在 take 段：flat idx d < idx z
      have hi_dz : r.flatten.idxOf d < r.flatten.idxOf z := by
        have := aqs_idxOf_lt_of_mem_take hflat hdt
        omega
      have hlv1 : r.idxOf l ≤ r.idxOf v1 := by
        by_contra hcon
        push Not at hcon
        have hlt : r.idxOf v1 < r.idxOf l := by omega
        have := aqs_flatIdx_lt_of_partIdx_lt hflat hv1 hl hlt hz hdl
        omega
      rcases lt_or_eq_of_le hlv1 with hlt | heq
      · right
        exact Or.inl (aqs_mem_between_wrap_right hrnd hv1 hne_parts hl hlt)
      · right; right
        exact aqs_idxOf_inj hrnd hl hv1 heq

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_memFlattenBetwnSymCase

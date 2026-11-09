/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12F — AQ12 叶 W3b（decl 26 `betwn_cap_point`）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:987-:1140（154 HOL 行）
  `uniq r ∧ MEM l (betwn r v v1) ∧ ~(v = v1) ∧ MEM v r ∧ MEM v1 r
    ==> betwn r v v1 = cat (cat (betwn r v l) [l]) (betwn r l v1)`。

  ┌─ 路线：**betwnTakeDrop 纯算术**（编排者 2026-11-09 拍板，非 HOL 的 next_el 逐支）──
  │ HOL 原证走 `betwn_cat_point_mem/sizel/uniq/last` 四件装配 `eq_last_next`，
  │ 再对 `next_el` 做 6–8 支 case split（约 110 行）。
  │ 本文件改走**确定性算术**：用 `betwnTakeDrop` 把三段都写成
  │ `take/drop`，再按 `idxOf` 三序关系分三情形，用「在位置 a 切开 Nodup 表」
  │ 的两条 splice 恒等式直接得列表相等：
  │   `X.take (a+1+b) = X.take a ++ [X[a]] ++ X.take b (X.drop (a+1))`
  │   `X = X.take a ++ [X[a]] ++ X.drop (a+1)`
  │ 位置关系（`iv < il < iv1` 等）由 `indexfBetwnEq` + `indexfCond` 算术给出，
  │ 不消费 decl 22–25（四件仍按 HOL 陈述独立在库，供 AQ13 消费）。
  └────────────────────────────────────────────────────────────────

  ┌─ 与 W1a 的关系（按编排者裁定记档）──────────────────────────
  │ 本路线**不消费** `aqs_eq_last_next`。该件仍**无生产消费者**（与
  │ `mapBetwn` 同状态）：零债务、标准三，保留供后续 AQ13/J2 需要时消费。
  │ 类型级接驳已由 `ProbeAQ12W3Hookup.lean`（W3a 交付，RC=0）验证。
  │ **不为此另造消费点**（编排者明令）。
  └────────────────────────────────────────────────────────────────

  载体：`List (ℕ × ℕ)`（与 AQ12 全段一致）。
  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12E

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (between)

/-! ## §0 两条 splice 恒等式（cut at an index of a Nodup list） -/

/-- 在位置 `a` 切开（保留 `[a+1+b)` 前缀）：
`X.take (a+1+b) = X.take a ++ [X[a]] ++ X.take b (X.drop (a+1))`。 -/
theorem aqs_takeSplit3 {α : Type*} (X : List α) {a b : ℕ} (ha : a < X.length) :
    X.take (a + 1 + b) = X.take a ++ [X[a]] ++ List.take b (X.drop (a + 1)) := by
  have h1 : a + 1 + b = a + (1 + b) := by omega
  rw [h1, List.take_add, List.append_assoc]
  congr 1
  rw [List.take_add]
  have h2 : List.take 1 (X.drop a) = [X[a]] := by
    rw [List.drop_eq_getElem_cons ha]
    simp only [List.take_succ_cons, List.take_zero]
  have h3 : List.drop 1 (X.drop a) = X.drop (a + 1) := List.drop_drop
  rw [h2, h3]

/-- 在位置 `a` 切开（整表形）：`X = X.take a ++ [X[a]] ++ X.drop (a+1)`。 -/
theorem aqs_takeSplitCons {α : Type*} (X : List α) {a : ℕ} (ha : a < X.length) :
    X = X.take a ++ [X[a]] ++ X.drop (a + 1) := by
  have h := aqs_takeSplit3 X (a := a) (b := 0) ha
  have h' : X.take (a + 1) = X.take a ++ [X[a]] := by
    simpa using h
  calc X = X.take (a + 1) ++ X.drop (a + 1) := (List.take_append_drop (a + 1) X).symm
    _ = (X.take a ++ [X[a]]) ++ X.drop (a + 1) := by rw [h']

/-- splice 引理（区间形，末元素记为 `x`）。 -/
private theorem aqs_splitAtIdx {α : Type*} (X : List α) {a b c : ℕ} (ha : a < X.length)
    (hc : c = a + 1 + b) (x : α) (hx : X[a] = x) :
    X.take c = (X.take a ++ [x]) ++ List.take b (X.drop (a + 1)) := by
  subst hc
  calc X.take (a + 1 + b)
      = X.take a ++ [X[a]] ++ List.take b (X.drop (a + 1)) := aqs_takeSplit3 X ha
    _ = X.take a ++ [x] ++ List.take b (X.drop (a + 1)) := by rw [hx]

/-- splice 引理（整表形，末元素记为 `x`）。 -/
private theorem aqs_splitConsAtIdx {α : Type*} (X : List α) {a : ℕ} (ha : a < X.length)
    (x : α) (hx : X[a] = x) :
    X = (X.take a ++ [x]) ++ X.drop (a + 1) := by
  have h := aqs_takeSplitCons X ha
  rw [hx] at h
  exact h

/-- `idxOf` 在 Nodup 表上单射到元素：同位置 ⇒ 同元素（`getElem_idxOf` 直接搬运）。 -/
private theorem aqs_idxOfInj {s : List (ℕ × ℕ)} (hnd : s.Nodup) {a b : ℕ × ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (h : s.idxOf a = s.idxOf b) : a = b := by
  have hlt_a : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  have hlt_b : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  have e1 : s[s.idxOf a]? = some a := by
    rw [List.getElem?_eq_getElem hlt_a, List.getElem_idxOf hlt_a]
  have e2 : s[s.idxOf b]? = some b := by
    rw [List.getElem?_eq_getElem hlt_b, List.getElem_idxOf hlt_b]
  have h' : s[s.idxOf a]? = s[s.idxOf b]? := by rw [h]
  rw [e1, e2] at h'
  exact Option.some.inj h'


/-- `getElem` 的索引相等搬运（依赖索引的 `rw` 会卡 proof 参数，故显式给出）。 -/
private theorem aqs_getElem_congr {α : Type*} {s : List α} {i j : ℕ} (h : i = j)
    (hi : i < s.length) (hj : j < s.length) : s[i]'hi = s[j]'hj := by
  cases h
  rfl

/-! ## §1 HOL AQ12.hl:987 `betwn_cap_point` -/

/-- **HOL `betwn_cap_point`**（AQ12.hl:987-:1140）：环段在点 `l` 处可切开——
`betwn r v v1 = betwn r v l ++ [l] ++ betwn r l v1`。
消费：AQ12 decl 26 主链 / **reduction3.hl（J2 下游）**。 -/
theorem aqs_betwnCapPoint {r : List (ℕ × ℕ)} {v v1 l : ℕ × ℕ} (hr : r.Nodup)
    (hl : l ∈ between r v v1) (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) :
    between r v v1 = ((between r v l ++ [l]) ++ between r l v1) := by
  have hl_r : l ∈ r := betwnMem hl
  have hlv : l ≠ v := fun h => notBetwn1 (s := r) (x := v) (z := v1) hr hv1 (h ▸ hl)
  have hlv1 : l ≠ v1 := fun h => notBetwn2 (s := r) (x := v) (z := v1) hr (h ▸ hl)
  have hiv : r.idxOf v < r.length := List.idxOf_lt_length_iff.mpr hv
  have hiv1 : r.idxOf v1 < r.length := List.idxOf_lt_length_iff.mpr hv1
  have hil : r.idxOf l < r.length := List.idxOf_lt_length_iff.mpr hl_r
  have hlne : r.idxOf l ≠ r.idxOf v := fun h => hlv (aqs_idxOfInj hr hl_r hv h)
  have hvvne : r.idxOf v ≠ r.idxOf v1 := fun h => hvne (aqs_idxOfInj hr hv hv1 h)
  have hb := (indexfBetwnEq hvne hr hv hv1).mp hl
  have hcond1 := indexfCond (s := r) hv hv1
  have hcondl := indexfCond (s := r) hv hl_r
  by_cases h1 : r.idxOf v < r.idxOf v1
  · -- 情形 1：iv < iv1（两侧同向、都在 take 支）
    have hvv1 : indexf v v1 r = r.idxOf v1 - r.idxOf v := by
      rw [hcond1, if_pos (le_of_lt h1)]
    have hvil : r.idxOf v < r.idxOf l := by
      by_contra hle
      push Not at hle
      have hvl : indexf v l r = r.idxOf l + (r.length - r.idxOf v) := by
        rw [hcondl, if_neg (by omega)]
      omega
    have hvl : indexf v l r = r.idxOf l - r.idxOf v := by
      rw [hcondl, if_pos (le_of_lt hvil)]
    have hil1 : r.idxOf l < r.idxOf v1 := by omega
    rw [betwnTakeDrop hr hv1, if_pos h1, betwnTakeDrop hr hl_r, if_pos hvil,
      betwnTakeDrop hr hv1, if_pos hil1]
    have hXlen : r.idxOf l - (r.idxOf v + 1) < (r.drop (r.idxOf v + 1)).length := by
      rw [List.length_drop]
      omega
    have hXa : (r.drop (r.idxOf v + 1))[r.idxOf l - (r.idxOf v + 1)]'hXlen = l := by
      have e1 : (r.drop (r.idxOf v + 1))[r.idxOf l - (r.idxOf v + 1)]'hXlen
          = r[(r.idxOf v + 1) + (r.idxOf l - (r.idxOf v + 1))]'(by omega) :=
        List.getElem_drop (h := hXlen)
      rw [e1]
      exact (aqs_getElem_congr (by omega) _ _).trans (List.getElem_idxOf hil)
    have hdrop : (r.drop (r.idxOf v + 1)).drop
        (r.idxOf l - (r.idxOf v + 1) + 1) = r.drop (r.idxOf l + 1) := by
      have e : r.idxOf l - (r.idxOf v + 1) + 1 = r.idxOf l - r.idxOf v := by omega
      rw [e, List.drop_drop]
      congr 1
      omega
    have hsplit := aqs_splitAtIdx (X := r.drop (r.idxOf v + 1))
      (a := r.idxOf l - (r.idxOf v + 1)) (b := r.idxOf v1 - (r.idxOf l + 1))
      (c := r.idxOf v1 - (r.idxOf v + 1)) hXlen (by omega) l hXa
    rw [hdrop] at hsplit
    exact hsplit
  · -- 情形 2：iv1 < iv（`S` 走 drop++take 支）
    have hvv1 : indexf v v1 r = r.idxOf v1 + (r.length - r.idxOf v) := by
      rw [hcond1, if_neg (by omega)]
    by_cases h2 : r.idxOf v < r.idxOf l
    · -- 情形 2a：iv < il（A 走 take 支，B 走 drop++take 支）
      rw [betwnTakeDrop hr hv1, if_neg (by omega), betwnTakeDrop hr hl_r, if_pos h2,
        betwnTakeDrop hr hv1, if_neg (by omega)]
      have hXlen : r.idxOf l - (r.idxOf v + 1) < (r.drop (r.idxOf v + 1)).length := by
        rw [List.length_drop]
        omega
      have hXa : (r.drop (r.idxOf v + 1))[r.idxOf l - (r.idxOf v + 1)]'hXlen = l := by
        have e1 : (r.drop (r.idxOf v + 1))[r.idxOf l - (r.idxOf v + 1)]'hXlen
            = r[(r.idxOf v + 1) + (r.idxOf l - (r.idxOf v + 1))]'(by omega) :=
          List.getElem_drop (h := hXlen)
        rw [e1]
        exact (aqs_getElem_congr (by omega) _ _).trans (List.getElem_idxOf hil)
      have hdrop : (r.drop (r.idxOf v + 1)).drop
          (r.idxOf l - (r.idxOf v + 1) + 1) = r.drop (r.idxOf l + 1) := by
        have e : r.idxOf l - (r.idxOf v + 1) + 1 = r.idxOf l - r.idxOf v := by omega
        rw [e, List.drop_drop]
        congr 1
        omega
      have hcons := aqs_splitConsAtIdx (X := r.drop (r.idxOf v + 1))
        (a := r.idxOf l - (r.idxOf v + 1)) hXlen l hXa
      have hcons' : r.drop (r.idxOf v + 1)
          = (List.take (r.idxOf l - (r.idxOf v + 1)) (r.drop (r.idxOf v + 1)) ++ [l])
            ++ r.drop (r.idxOf l + 1) := by
        have h1 := hcons
        rw [hdrop] at h1
        exact h1
      have hcons'' : r.drop (r.idxOf v + 1)
          = List.take (r.idxOf l - (r.idxOf v + 1)) (r.drop (r.idxOf v + 1))
            ++ ([l] ++ r.drop (r.idxOf l + 1)) := by
        have h1 := hcons
        rw [hdrop, List.append_assoc] at h1
        exact h1
      rw [congrArg (fun s => s ++ List.take (r.idxOf v1) r) hcons'']
      simp only [List.append_assoc]
    · -- 情形 2b：il ≤ iv（A 走 drop++take 支，B 走 take 支）
      push Not at h2
      have hvl : indexf v l r = r.idxOf l + (r.length - r.idxOf v) := by
        rw [hcondl, if_neg (by omega)]
      have hil1 : r.idxOf l < r.idxOf v1 := by omega
      rw [betwnTakeDrop hr hv1, if_neg (by omega), betwnTakeDrop hr hl_r, if_neg (by omega),
        betwnTakeDrop hr hv1, if_pos hil1]
      have hXa : r[r.idxOf l] = l := List.getElem_idxOf hil
      have hsplit := aqs_splitAtIdx (X := r) (a := r.idxOf l)
        (b := r.idxOf v1 - (r.idxOf l + 1)) (c := r.idxOf v1) hil (by omega) l hXa
      rw [hsplit]
      simp only [List.append_assoc]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_takeSplit3
#print axioms Kepler.Text.TameSpine.aqs_takeSplitCons
#print axioms Kepler.Text.TameSpine.aqs_betwnCapPoint

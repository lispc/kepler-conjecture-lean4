/-
  Kepler.Text.TameSpine.JcajyduBetwnRot — j2w2 顺带批（续422 交接）：c2 车道
  betwnRot 止损稿的三修正点落地 + 闭合。

  本批对象（HOL 逐条锚）：
  - Reduction2.hl:107 `betwn_rot`（本批 `betwnRot`；HOL 的 `n ≤ sizel s` 前提
    在 Lean `List.rotate` 全函数化下冗余，省略——诚实强化）。

  c2 止损三修正点（本批落地形）：
  ① singleton-length 原子：`[a].length = 1` 以 `lenSingleton`（rfl 直供）
     显式喂 ω；
  ② drop_append 双形式按支供给：`(l ++ [a]).drop k` 第二因子
     `[a].drop (k - l.length)`——案 1（k = l.length + 1）Nil 化、
     案 2/3（k = l.idxOf x + 1）**保持 [a]**（k - l.length = 0）——
     omega 所需的 idxOf 界一律以 hxlt/hylt 具名 have 显式入上下文
     （c2 ②「ω 闭包需原子在场」的落实形）；
  ③ cons-shift 次序前置：`(a :: l).drop/take (n + 1)` 收缩以 rfl 直供私件
     （`List.drop`/`take` 对字面量后继 + cons 的 whnf 定义性），不依赖
     本工具链不存在的 `List.drop_succ_cons`/`take_succ_cons`。
  另：c2 修正点②的 flex-metavar 固定（`have hndR := by rw [← hrot];
  exact List.nodup_rotate.mpr hnd`）保留。

  载体折算（沿批 J0-a/J0-b₁ 约定）：`betwn` ↦ `Kepler.Graphs.between`、
  `uniq` ↦ `List.Nodup`、`indexl` ↦ `List.idxOf`、`sizel` ↦ `List.length`、
  `rot n` ↦ `List.rotate n`。

  红线：零 sorry、零 axiom、零 native_decide、零既有文件触碰、
  主仓树零写入（含未追踪——`lean/Kepler/Text/TameSpine/JcajyduBetwnRot.lean`
  现存 c2 未追踪旧稿，落库时编排者清理后 apply 本 patch）。
-/
import Kepler.Text.TameSpine.JcajyduBetwnBase

namespace Kepler.Text.TameSpine

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)

/-! ## §0 私件（修正点 ①③ 的载体；rfl 直供零引理依赖） -/

/-- 修正点①：singleton-length 原子（`List.length` 对 `cons` 字面量定义性）。 -/
private theorem lenSingleton {α : Type*} (a : α) : ([a] : List α).length = 1 :=
  rfl

/-- 修正点③：cons 头收缩（drop 形）——`List.drop` 对字面量后继 + cons 的
whnf 定义性（本工具链无 `List.drop_succ_cons` 名）。 -/
private theorem dropConsSucc {α : Type*} {l : List α} (a : α) (n : ℕ) :
    ((a :: l : List α)).drop (n + 1) = l.drop n :=
  rfl

/-- 修正点③：cons 头收缩（take 形）。 -/
private theorem takeConsSucc {α : Type*} {l : List α} (a : α) (n : ℕ) :
    ((a :: l : List α)).take (n + 1) = a :: l.take n :=
  rfl

/-! ## §1 betwnRotateOne（betwnRot 的 n = 1 内核） -/

/-- **HOL `Reduction2.betwn_rot` 的 n = 1 内核**：`uniq t ∧ x ∈ t ∧ y ∈ t ∧
x ≠ y → betwn t x y = betwn (t.rotate 1) x y`。四案例（x=a / y=a / 双∈l-take /
双∈l-else），每案例 = t 侧与 R := l ++ [a] 侧的 `betwnTakeDrop` 展开 +
§0 分解件（修正点②③）。 -/
private theorem betwnRotateOne [BEq α] [LawfulBEq α] {t : List α} {x y : α}
    (hnd : t.Nodup) (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    between t x y = between (t.rotate 1) x y := by
  cases t with
  | nil => exact absurd hx (by simp)
  | cons a l =>
    have hndc : a ∉ l ∧ l.Nodup := List.nodup_cons.1 hnd
    have hrot : (a :: l).rotate 1 = l ++ [a] := by
      rw [List.rotate_cons_succ l a 0, List.rotate_zero]
    have hndR : (l ++ [a]).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hnd
    have hidxL : ∀ u ∈ l, (l ++ [a]).idxOf u = l.idxOf u := fun u hu =>
      List.idxOf_append_of_mem hu
    have hidxa : (l ++ [a]).idxOf a = l.length := by
      rw [List.idxOf_append_of_notMem hndc.1]
      simp
    have hmemRa : a ∈ l ++ [a] := List.mem_append.mpr (Or.inr (by simp))
    rw [hrot]
    by_cases hxa : x = a
    · -- 案 1：x = a（y ∈ l）。t 侧 take 支；R 侧 else 支；同落 l.take (l.idxOf y)。
      rw [hxa] at hxy ⊢
      have hyl : y ∈ l := by
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h.symm hxy
        · exact h
      have hylt : l.idxOf y < l.length := List.idxOf_lt_length_iff.mpr hyl
      have hyR : y ∈ l ++ [a] := List.mem_append.mpr (Or.inl hyl)
      have hioy : (a :: l).idxOf y = l.idxOf y + 1 := List.idxOf_cons_ne l hxy
      have hdropr : (l ++ [a]).drop (l.length + 1) = [] := by
        rw [List.drop_append, List.drop_of_length_le (by omega),
          List.drop_of_length_le (by rw [lenSingleton a]; omega), List.append_nil]
      have htaker : (l ++ [a]).take (l.idxOf y) = l.take (l.idxOf y) := by
        rw [List.take_append, show l.idxOf y - l.length = 0 from (by omega),
          List.take_zero, List.append_nil]
      rw [betwnTakeDrop hnd hy, List.idxOf_cons_self, hioy,
        if_pos (by omega : (0 : ℕ) < l.idxOf y + 1), dropConsSucc a 0,
        List.drop_zero]
      rw [betwnTakeDrop hndR hyR, hidxa, hidxL y hyl,
        if_neg (show ¬(l.length < l.idxOf y) from (by omega)), hdropr, htaker,
        List.nil_append]
      congr 1
    · by_cases hya : y = a
      · -- 案 2：y = a（x ∈ l）。t 侧 else 支；R 侧 take 支；同落 l.drop (l.idxOf x + 1)。
        rw [hya] at hy hxy ⊢
        have hxl : x ∈ l := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hxy
          · exact h
        have hxlt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hxl
        have hxR : x ∈ l ++ [a] := List.mem_append.mpr (Or.inl hxl)
        have hiox : (a :: l).idxOf x = l.idxOf x + 1 :=
          List.idxOf_cons_ne l (Ne.symm hxy)
        have hsubR : l.idxOf x + 1 - l.length = 0 := by omega
        have htakeR : ((l ++ [a]).drop (l.idxOf x + 1)).take
            (l.length - (l.idxOf x + 1)) = l.drop (l.idxOf x + 1) := by
          rw [List.drop_append, hsubR, List.drop_zero, List.take_append,
            List.length_drop, Nat.sub_self, List.take_zero,
            List.take_of_length_le (by rw [List.length_drop]), List.append_nil]
        rw [betwnTakeDrop hnd hy, List.idxOf_cons_self, hiox,
          if_neg (by omega : ¬(l.idxOf x + 1 < (0 : ℕ))),
          dropConsSucc a (l.idxOf x + 1), List.take_zero, List.append_nil]
        rw [betwnTakeDrop hndR hmemRa, hidxL x hxl, hidxa,
          if_pos (show l.idxOf x < l.length from List.idxOf_lt_length_iff.mpr hxl),
          htakeR]
      · -- 案 3：x, y ∈ l。idxOf 同步平移 1，t 与 R 同分支。
        have hxl : x ∈ l := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hxa
          · exact h
        have hyl : y ∈ l := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm (Ne.symm hya)
          · exact h
        have hxlt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hxl
        have hylt : l.idxOf y < l.length := List.idxOf_lt_length_iff.mpr hyl
        have hxR : x ∈ l ++ [a] := List.mem_append.mpr (Or.inl hxl)
        have hyR : y ∈ l ++ [a] := List.mem_append.mpr (Or.inl hyl)
        have hiox : (a :: l).idxOf x = l.idxOf x + 1 :=
          List.idxOf_cons_ne l (Ne.symm hxa)
        have hioy : (a :: l).idxOf y = l.idxOf y + 1 :=
          List.idxOf_cons_ne l (Ne.symm hya)
        have hsubR : l.idxOf x + 1 - l.length = 0 := by omega
        have hsubR2 : l.idxOf y - l.length = 0 := by omega
        by_cases hlt : l.idxOf x < l.idxOf y
        · -- take 支：同落 (l.drop (l.idxOf x + 1)).take (l.idxOf y - (l.idxOf x + 1))
          have htakeR : ((l ++ [a]).drop (l.idxOf x + 1)).take
              (l.idxOf y - (l.idxOf x + 1))
              = (l.drop (l.idxOf x + 1)).take (l.idxOf y - (l.idxOf x + 1)) := by
            rw [List.drop_append, hsubR, List.drop_zero, List.take_append,
              List.length_drop,
              show l.idxOf y - (l.idxOf x + 1) - (l.length - (l.idxOf x + 1)) = 0
                from (by omega),
              List.take_zero, List.append_nil]
          rw [betwnTakeDrop hnd hy, hiox, hioy, if_pos (by omega),
            dropConsSucc a (l.idxOf x + 1)]
          rw [betwnTakeDrop hndR hyR, hidxL x hxl, hidxL y hyl, if_pos hlt, htakeR]
          congr 1
          omega
        · -- else 支：同落 l.drop (l.idxOf x + 1) ++ a :: l.take (l.idxOf y)
          have htakeR : ((l ++ [a]).drop (l.idxOf x + 1))
              ++ ((l ++ [a]).take (l.idxOf y))
              = l.drop (l.idxOf x + 1) ++ a :: l.take (l.idxOf y) := by
            rw [List.drop_append, hsubR, List.drop_zero, List.take_append,
              hsubR2, List.take_zero, List.append_nil, List.append_assoc]
            simp
          rw [betwnTakeDrop hnd hy, hiox, hioy, if_neg (by omega),
            dropConsSucc a (l.idxOf x + 1), takeConsSucc a (l.idxOf y)]
          rw [betwnTakeDrop hndR hyR, hidxL x hxl, hidxL y hyl, if_neg hlt, htakeR]

/-! ## §2 betwnRot（HOL Reduction2.hl:107） -/

/-- **HOL `Reduction2.betwn_rot`**（reduction2.hl:107）：
`uniq s ∧ MEM x s ∧ MEM y s ∧ x ≠ y → betwn s x y = betwn (s.rotate n) x y`。
（HOL 的 `n ≤ sizel s` 前提在 Lean `List.rotate` 全函数化下冗余，省略——
诚实强化。）对 n 归纳折叠单步 `betwnRotateOne`（`rotate (n+1)` 经
`List.rotate_rotate` 换 `(rotate n) ∘ rotate 1`）。 -/
theorem betwnRot [BEq α] [LawfulBEq α] {s : List α} {x y : α} (hnd : s.Nodup)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (n : ℕ) :
    between s x y = between (s.rotate n) x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnd1 : (s.rotate n).Nodup := List.nodup_rotate.mpr hnd
    have hx1 : x ∈ s.rotate n := List.mem_rotate.2 hx
    have hy1 : y ∈ s.rotate n := List.mem_rotate.2 hy
    rw [← List.rotate_rotate, ih]
    exact betwnRotateOne hnd1 hx1 hy1 hxy

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.betwnRot

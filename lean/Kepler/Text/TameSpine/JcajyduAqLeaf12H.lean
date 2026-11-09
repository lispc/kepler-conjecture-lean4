/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12H — AQ12 叶 W4b-i（decl 27）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1141-:1214（74 HOL 行）
  `!a v v1. uniq(flatten r) ∧ ~(v=v1) ∧ MEM v r ∧ MEM v1 r ∧ all nonempty r ∧
     betwn r v v1 = a ∧ ~(a=[]) ==>
     indexf (HD (next_el r v)) (LAST (prev_el r v1)) (flatten r) = sizel (flatten a) - 1`

  ┌─ 路线（HOL 的 r 结构归纳 vs Lean 的 betwnTakeDrop 分解 + 三个 block 件）──
  │ ① `next_el r v = betwn.head!`（基底层泛型原件 `HD_BETWN2`，TameList71:614）、
  │    `prev_el r v1 = betwn.getLast!`（本文件泛型私件
  │    `aqs_lastBetwnEqPrevGen`，同 W3a 陈述的 parts 层版本）；
  │ ② flatten 的 head/last 件：`(l.flatten).head! = l.head!.head!`、
  │    `(l.flatten).getLast! = l.getLast!.getLast!`（本文件 private）；
  │ ③ 两个 `betwnTakeDrop` 情形把 `r.flatten` 重排成
  │    - iv<iv1：`P ++ a.flatten ++ T`（块在中间）⇒ `aqs_indexf_block`；
  │    - iv1<iv：`A' ++ M ++ D` 且 `a.flatten = D ++ A'`（块环绕）
  │      ⇒ `aqs_indexf_block_wrap`（三分支：D=[]/A'=[]/两者非空）。
  │ ④ 三个 block 件全部用 `indexfCond` + `idxOf_append` 直接算，
  │    不用旋转/周回论证。
  └────────────────────────────────────────────────────────────────

  （W4b-ii = decls 28–29，:1215-:1386，另交；二者将复用本文件的
   private block 件思路与公开的 `aqs_indexfSizelBetwnFlatten`。）

  载体：`List (ℕ × ℕ)` / `List (List (ℕ × ℕ))`。
  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12G

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)

/-! ## §0 辅件：flatten 的 head/last、三个 indexf block 件 -/

/-- `getLast!` 的拼接律（泛型版本；W3a 的 `aqs_getLastAppend` 只对 ℕ×ℕ 固定）。 -/
private theorem aqs_getLastAppendGen {α : Type*} [Inhabited α] [DecidableEq α]
    (l l' : List α) :
    (l ++ l').getLast! = if l' = [] then l.getLast! else l'.getLast! := by
  by_cases h : l' = []
  · subst h
    simp
  · rw [if_neg h, List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD,
      List.getLast?_append, List.getLast?_eq_some_getLast h]
    simp

/-- `betwn` 的 LAST 是右端点的前驱（泛型版本；W3a 的 `aqs_lastBetwnEqPrev`
只对 ℕ×ℕ 固定，本文件在 parts 层（α = List (ℕ × ℕ)）需要泛型形）。 -/
private theorem aqs_lastBetwnEqPrevGen {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [Inhabited α] {r : List α} {y z : α} (hr : r.Nodup) (hy : y ∈ r) (hz : z ∈ r)
    (hyz : y ≠ z) (hne : between r y z ≠ []) :
    (between r y z).getLast! = prevEl r z := by
  have hmem : (between r y z).getLast! ∈ between r y z := aqs_getLastMem hne
  have hmemr : (between r y z).getLast! ∈ r := betwnMem hmem
  have hnext : nextEl r (between r y z).getLast! = z := by
    have h := nextLastBetwn (r := r) hy hz hr hyz hne
    rwa [← getLast!EqGetLast hne] at h
  calc (between r y z).getLast!
      = prevEl r (nextEl r (between r y z).getLast!) :=
        (Kepler.Text.TameLp.prevEl_nextEl hr hmemr).symm
    _ = prevEl r z := by rw [hnext]

/-- 全非空 ⇒ flatten 非空。 -/
private theorem aqs_flatten_ne_nil {l : List (List (ℕ × ℕ))} (hl : l ≠ [])
    (hall : ∀ x ∈ l, x ≠ []) : l.flatten ≠ [] := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hl
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil p (hall p hp)
  exact List.ne_nil_of_mem (List.mem_flatten.mpr ⟨p, hp, hx⟩)

/-- `flatten` 的 head!：`(l.flatten).head! = l.head!.head!`（全非空）。 -/
private theorem aqs_headBang_flatten {l : List (List (ℕ × ℕ))} (hl : l ≠ [])
    (hall : ∀ x ∈ l, x ≠ []) : l.flatten.head! = l.head!.head! := by
  cases l with
  | nil => exact absurd rfl hl
  | cons p t =>
    have hp : p ≠ [] := hall p (by simp)
    have hflat : (p :: t).flatten = p ++ t.flatten := List.flatten_cons
    rw [hflat, List.head!_append _ hp, List.head!_cons]

/-- `flatten` 的 getLast!：`(l.flatten).getLast! = l.getLast!.getLast!`（全非空）。 -/
private theorem aqs_getLastBang_flatten {l : List (List (ℕ × ℕ))} (hl : l ≠ [])
    (hall : ∀ x ∈ l, x ≠ []) : l.flatten.getLast! = l.getLast!.getLast! := by
  cases l with
  | nil => exact absurd rfl hl
  | cons p t =>
    have hflat : (p :: t).flatten = p ++ t.flatten := List.flatten_cons
    by_cases ht : t = []
    · subst ht
      rw [hflat]
      simp
    · have htn : ∀ x ∈ t, x ≠ [] := fun x hx => hall x (List.mem_cons_of_mem _ hx)
      have htflat : t.flatten ≠ [] := aqs_flatten_ne_nil ht htn
      have hgl : (p :: t).getLast! = t.getLast! := by
        have h := aqs_getLastAppendGen ([p] : List (List (ℕ × ℕ))) t
        rw [List.singleton_append, if_neg ht] at h
        exact h
      rw [hflat, aqs_getLastAppend, if_neg htflat,
        aqs_getLastBang_flatten ht htn, hgl]

/-- 非空左段的拼接 head!。 -/
private theorem aqs_headBang_append_eq' {s r : List (ℕ × ℕ)} (hs : s ≠ []) :
    (s ++ r).head! = s.head! := List.head!_append r hs

/-- **block（中间段）**：`(P ++ X ++ T).Nodup ∧ X ≠ [] ⇒
indexf X.head! X.getLast! (P ++ X ++ T) = |X| - 1`。 -/
private theorem aqs_indexf_block {P X T : List (ℕ × ℕ)}
    (hnd : (P ++ X ++ T).Nodup) (hX : X ≠ []) :
    indexf X.head! X.getLast! (P ++ X ++ T) = X.length - 1 := by
  obtain ⟨hPXnd, -, hdisjT⟩ := List.nodup_append.mp hnd
  obtain ⟨-, hXnd, hdisjPX⟩ := List.nodup_append.mp hPXnd
  have hhead : X.head! ∈ X := aqs_headMem hX
  have hlast : X.getLast! ∈ X := aqs_getLastMem hX
  have hnotP : X.head! ∉ P := fun h => hdisjPX _ h _ hhead rfl
  have hnotP2 : X.getLast! ∉ P := fun h => hdisjPX _ h _ hlast rfl
  have hnotT2 : X.head! ∉ T :=
    fun h => hdisjT _ (List.mem_append.mpr (Or.inr hhead)) _ h rfl
  have hAmem : X.head! ∈ (P ++ X) ++ T :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hhead)))
  have hBmem : X.getLast! ∈ (P ++ X) ++ T :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hlast)))
  have h1 : ((P ++ X) ++ T).idxOf X.head! = P.length := by
    rw [List.idxOf_append, if_pos (List.mem_append.mpr (Or.inr hhead)),
      List.idxOf_append_of_notMem hnotP, aqs_idxOfHead X, Nat.add_zero]
  have h2 : ((P ++ X) ++ T).idxOf X.getLast! = P.length + (X.length - 1) := by
    rw [List.idxOf_append, if_pos (List.mem_append.mpr (Or.inr hlast)),
      List.idxOf_append_of_notMem hnotP2, aqs_idxOfGetLast hXnd hX]
  have hxpos : 0 < X.length := List.length_pos_of_ne_nil hX
  rw [indexfCond hAmem hBmem, h1, h2, if_pos (by omega)]
  omega

/-- **block（后缀段）**：`(T ++ X).Nodup ∧ X ≠ [] ⇒
indexf X.head! X.getLast! (T ++ X) = |X| - 1`。 -/
private theorem aqs_indexf_block_suffix {T X : List (ℕ × ℕ)}
    (hnd : (T ++ X).Nodup) (hX : X ≠ []) :
    indexf X.head! X.getLast! (T ++ X) = X.length - 1 := by
  obtain ⟨-, hXnd, hdisj⟩ := List.nodup_append.mp hnd
  have hhead : X.head! ∈ X := aqs_headMem hX
  have hlast : X.getLast! ∈ X := aqs_getLastMem hX
  have hnotT : X.head! ∉ T := fun h => hdisj _ h _ hhead rfl
  have hnotT2 : X.getLast! ∉ T := fun h => hdisj _ h _ hlast rfl
  have hAmem : X.head! ∈ T ++ X := List.mem_append.mpr (Or.inr hhead)
  have hBmem : X.getLast! ∈ T ++ X := List.mem_append.mpr (Or.inr hlast)
  have h1 : (T ++ X).idxOf X.head! = T.length := by
    rw [List.idxOf_append_of_notMem hnotT, aqs_idxOfHead X, Nat.add_zero]
  have h2 : (T ++ X).idxOf X.getLast! = T.length + (X.length - 1) := by
    rw [List.idxOf_append_of_notMem hnotT2, aqs_idxOfGetLast hXnd hX]
  have hxpos : 0 < X.length := List.length_pos_of_ne_nil hX
  rw [indexfCond hAmem hBmem, h1, h2, if_pos (by omega)]
  omega

/-- **block（环绕段）**：`(A' ++ M ++ D).Nodup ∧ D ++ A' ≠ [] ⇒
indexf (D ++ A').head! (D ++ A').getLast! (A' ++ M ++ D) = |D ++ A'| - 1`。 -/
private theorem aqs_indexf_block_wrap {A' M D : List (ℕ × ℕ)}
    (hnd : (A' ++ M ++ D).Nodup) (hX : D ++ A' ≠ []) :
    indexf (D ++ A').head! (D ++ A').getLast! (A' ++ M ++ D) = (D ++ A').length - 1 := by
  by_cases hD : D = []
  · subst hD
    have hnd' : ([] ++ A' ++ M).Nodup := by simpa using hnd
    have hA'ne : A' ≠ [] := by simpa using hX
    simpa using aqs_indexf_block (P := ([] : List (ℕ × ℕ))) (X := A') (T := M) hnd' hA'ne
  · by_cases hA' : A' = []
    · subst hA'
      have hnd' : (M ++ D).Nodup := by simpa using hnd
      have hDne : D ≠ [] := by simpa using hX
      simpa using aqs_indexf_block_suffix (T := M) (X := D) hnd' hDne
    · -- 两者非空
      obtain ⟨hA'Md, -, hdisjD⟩ := List.nodup_append.mp hnd
      obtain ⟨hA'nd, hMnd, hdisjM⟩ := List.nodup_append.mp hA'Md
      have hDh : (D ++ A').head! = D.head! := aqs_headBang_append_eq' hD
      have hAl : (D ++ A').getLast! = A'.getLast! := by
        rw [aqs_getLastAppend, if_neg hA']
      rw [hDh, hAl]
      have hDhead : D.head! ∈ D := aqs_headMem hD
      have hAlast : A'.getLast! ∈ A' := aqs_getLastMem hA'
      have hnotA' : D.head! ∉ A' := fun h =>
        hdisjD _ (List.mem_append.mpr (Or.inl h)) _ hDhead rfl
      have hnotM : D.head! ∉ M := fun h =>
        hdisjD _ (List.mem_append.mpr (Or.inr h)) _ hDhead rfl
      have hnotM2 : A'.getLast! ∉ M := fun h => hdisjM _ hAlast _ h rfl
      have hAmem : D.head! ∈ (A' ++ M) ++ D := List.mem_append.mpr (Or.inr hDhead)
      have hBmem : A'.getLast! ∈ (A' ++ M) ++ D :=
        List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hAlast)))
      have h1 : ((A' ++ M) ++ D).idxOf D.head! = A'.length + M.length := by
        rw [List.idxOf_append, if_neg (by
          intro h
          rcases List.mem_append.mp h with h' | h'
          · exact hnotA' h'
          · exact hnotM h'), aqs_idxOfHead D, Nat.zero_add, List.length_append]
      have h2 : ((A' ++ M) ++ D).idxOf A'.getLast! = A'.length - 1 := by
        rw [List.idxOf_append, if_pos (List.mem_append.mpr (Or.inl hAlast)),
          List.idxOf_append, if_pos hAlast, aqs_idxOfGetLast hA'nd hA']
      have hA'pos : 0 < A'.length := List.length_pos_of_ne_nil hA'
      have hlen1 : (A' ++ M ++ D).length = A'.length + M.length + D.length := by
        rw [List.length_append, List.length_append]
      have hlen2 : (D ++ A').length = D.length + A'.length := List.length_append
      rw [indexfCond hAmem hBmem, h1, h2, if_neg (by omega)]
      omega

/-! ## §1 HOL AQ12.hl:1141 `indexf_sizel_betwn_flatten` -/

/-- **HOL `indexf_sizel_betwn_flatten`**（AQ12.hl:1141-:1214）：
环段的 flatten 长度 − 1 = 从下一 parts 的头到上一 parts 的尾的 flatten 级 indexf。 -/
theorem aqs_indexfSizelBetwnFlatten {r : List (List (ℕ × ℕ))}
    {a : List (List (ℕ × ℕ))} {v v1 : List (ℕ × ℕ)} (hflat : r.flatten.Nodup)
    (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r) (hall : ∀ l ∈ r, l ≠ [])
    (ha : between r v v1 = a) (hane : a ≠ []) :
    indexf (nextEl r v).head! (prevEl r v1).getLast! r.flatten = a.flatten.length - 1 := by
  subst ha
  have hrnd : r.Nodup := uniqFlatten hflat hall
  have hBne : between r v v1 ≠ [] := hane
  have hallB : ∀ l ∈ between r v v1, l ≠ [] := fun l hl => hall l (betwnMem hl)
  have hXne : (between r v v1).flatten ≠ [] := aqs_flatten_ne_nil hBne hallB
  -- 端点对齐
  have hA : (nextEl r v).head! = (between r v v1).flatten.head! := by
    rw [← Kepler.Text.TameSpine.HD_BETWN2 hv hv1 hvne hrnd hBne,
      aqs_headBang_flatten hBne hallB]
  have hB : (prevEl r v1).getLast! = (between r v v1).flatten.getLast! := by
    rw [← aqs_lastBetwnEqPrevGen hrnd hv hv1 hvne hBne, aqs_getLastBang_flatten hBne hallB]
  rw [hA, hB]
  by_cases h1 : r.idxOf v < r.idxOf v1
  · -- 情形 1：iv < iv1（块在中间）
    have hBform : between r v v1
        = (r.drop (r.idxOf v + 1)).take (r.idxOf v1 - (r.idxOf v + 1)) := by
      rw [betwnTakeDrop hrnd hv1, if_pos h1]
    have h1a : r.flatten = (r.take (r.idxOf v + 1)).flatten
        ++ (r.drop (r.idxOf v + 1)).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    have h1b : (r.drop (r.idxOf v + 1)).flatten
        = (between r v v1).flatten ++ (r.drop (r.idxOf v1)).flatten := by
      have h2' : r.drop (r.idxOf v + 1)
          = (r.drop (r.idxOf v + 1)).take (r.idxOf v1 - (r.idxOf v + 1))
            ++ r.drop (r.idxOf v1) := by
        have h := (List.take_append_drop (r.idxOf v1 - (r.idxOf v + 1))
          (r.drop (r.idxOf v + 1))).symm
        rwa [List.drop_drop, show r.idxOf v + 1 + (r.idxOf v1 - (r.idxOf v + 1))
          = r.idxOf v1 from by omega] at h
      have hcongr := congrArg List.flatten h2'
      rw [hcongr, List.flatten_append]
      congr 1
      exact (hBform ▸ rfl)
    have hdecomp : r.flatten = (r.take (r.idxOf v + 1)).flatten
        ++ (between r v v1).flatten ++ (r.drop (r.idxOf v1)).flatten := by
      rw [h1a, h1b, List.append_assoc]
    rw [hdecomp]
    exact aqs_indexf_block (by rw [← hdecomp]; exact hflat) hXne
  · -- 情形 2：iv1 < iv（块环绕）
    have hBform : between r v v1 = r.drop (r.idxOf v + 1) ++ r.take (r.idxOf v1) := by
      rw [betwnTakeDrop hrnd hv1, if_neg h1]
    have h1a : r.flatten = (r.take (r.idxOf v1)).flatten
        ++ (r.drop (r.idxOf v1)).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    have h1b : (r.drop (r.idxOf v1)).flatten
        = ((r.drop (r.idxOf v1)).take (r.idxOf v + 1 - r.idxOf v1)).flatten
          ++ (r.drop (r.idxOf v + 1)).flatten := by
      have h2' : r.drop (r.idxOf v1)
          = (r.drop (r.idxOf v1)).take (r.idxOf v + 1 - r.idxOf v1)
            ++ r.drop (r.idxOf v + 1) := by
        have h := (List.take_append_drop (r.idxOf v + 1 - r.idxOf v1)
          (r.drop (r.idxOf v1))).symm
        rwa [List.drop_drop, show r.idxOf v1 + (r.idxOf v + 1 - r.idxOf v1)
          = r.idxOf v + 1 from by omega] at h
      have hcongr := congrArg List.flatten h2'
      rw [hcongr, List.flatten_append]
    have hdecomp : r.flatten = (r.take (r.idxOf v1)).flatten
        ++ ((r.drop (r.idxOf v1)).take (r.idxOf v + 1 - r.idxOf v1)).flatten
        ++ (r.drop (r.idxOf v + 1)).flatten := by
      rw [h1a, h1b, List.append_assoc]
    have hAform : (between r v v1).flatten
        = (r.drop (r.idxOf v + 1)).flatten ++ (r.take (r.idxOf v1)).flatten := by
      rw [hBform, List.flatten_append]
    rw [hdecomp, hAform]
    exact aqs_indexf_block_wrap (by rw [← hdecomp]; exact hflat)
      (by rw [← hAform]; exact hXne)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_indexfSizelBetwnFlatten

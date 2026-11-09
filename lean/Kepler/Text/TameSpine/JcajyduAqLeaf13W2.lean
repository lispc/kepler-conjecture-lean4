/-
  JcajyduAqLeaf13W2 — AQ13 叶 W2：合取 (i) 复用 + 合取 (ii) N 支。
  · 合取 (i)：直接实例化 AQ12 已落 `aq12y_flagListConjunctOne`（12Y:52）。
  · N 支：照 12Z:132-160 重放（replace 精确分解 + 旧 SFlag 第二合取 +
    sList ③ + FinalDart N→N' 转移），前提 `r' ∈ N`、`r' ≠ r`。
  · 另公开 `aq13w2_memReplaceCasesNodup`（W3 主装用的 replace 精确分解）。
  纪律：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf12Y
import Kepler.Text.TameSpine.JcajyduAqLeaf13W1
import Kepler.Text.TameSpine.JcajyduAqLeaf13W1b

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face)

/-! ## §0 私件：getLast! 成员 -/

private theorem aq13w2_getLast!_mem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [getLast!EqGetLast h]
  exact List.getLast_mem h

/-! ## §1 replaceSpine 的 Nodup 精确分解（W3 主装接口） -/

/-- `g.Nodup` 时 `replaceSpine f xs g` 成员的精确分解：
`(x ∈ g ∧ x ≠ f) ∨ (f ∈ g ∧ x ∈ xs)`（= 12Z 私件公开化）。 -/
theorem aq13w2_memReplaceCasesNodup {α : Type*} [DecidableEq α]
    {f x : α} {xs g : List α} (hg : g.Nodup)
    (h : x ∈ replaceSpine f xs g) : (x ∈ g ∧ x ≠ f) ∨ f ∈ g ∧ x ∈ xs := by
  induction g with
  | nil => simp [replaceSpine] at h
  | cons z zs ih =>
    rw [List.nodup_cons] at hg
    by_cases hzx : z = f
    · simp only [replaceSpine, if_pos hzx] at h
      rcases List.mem_append.mp h with hx1 | hx2
      · exact Or.inr ⟨by rw [hzx]; exact List.mem_cons_self .., hx1⟩
      · exact Or.inl ⟨List.mem_cons_of_mem _ hx2,
          fun hxf => hg.1 (hzx ▸ (hxf ▸ hx2))⟩
    · simp only [replaceSpine, if_neg hzx] at h
      rcases List.mem_cons.mp h with hxl | hxr
      · exact Or.inl ⟨by rw [hxl]; exact List.mem_cons_self ..,
          fun hxf => hzx (hxl.symm.trans hxf)⟩
      · rcases ih hg.2 hxr with ⟨hxg, hxf⟩ | hcase
        · exact Or.inl ⟨List.mem_cons_of_mem _ hxg, hxf⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ hcase.1, hcase.2⟩

/-! ## §2 合取 (i)：直接复用 AQ12 首合取 -/

/-- **AQ13 合取 (i)** = `aq12y_flagListConjunctOne`（12Y:52）的实例化：
`FinalDartListSpine L N'` 内任两点 u→v 存在 contour，支撑仍在 `FinalDartListSpine L N'`。
陈述与 `SFlagListSpine`（TameList13:254-263）首合取逐字相同。 -/
theorem aq13w2_flagConjunctOne (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    ∀ u : ℕ × ℕ, u ∈ FinalDartListSpine L (ntransSpine L N r x 1) →
      ∀ v : ℕ × ℕ, v ∈ FinalDartListSpine L (ntransSpine L N r x 1) →
        ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
          s.getLast! = v ∧ ∀ z ∈ s, z ∈ FinalDartListSpine L (ntransSpine L N r x 1) :=
  aq12y_flagListConjunctOne L hL hgn hm

/-! ## §3 合取 (ii) N 支（r' ∈ N、r' ≠ r） -/

/-- **AQ13 合取 (ii) 的 N 支**（HOL AQ13.hl:1033-1077 的 r'∈N 段）：
`r' ∈ N`、`r' ≠ r`、`y = LAST p`、`p ∈ parts r'`、`¬final r'`、
`y ∉ sList rtr x` ⇒ `eList y ∈ sList rtr x ++ FinalDartList N'`。 -/
theorem aq13w2_flagConjunctTwoN (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) :
    ∀ (r' p : List (ℕ × ℕ)) (y : ℕ × ℕ),
      r' ∈ N → r' ≠ r → y = p.getLast! → p ∈ partsSpine L r' →
      ¬finalListSpine L r' →
      y ∉ sListSpine L (rtransSpine L N r x 1) x →
      eList y ∈ sListSpine L (rtransSpine L N r x 1) x ++
        FinalDartListSpine L (ntransSpine L N r x 1) := by
  intro r' p y hN hNne hy hp hnf' hyNot
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  -- 三段 1：y ∉ sList r x（③ 的逆否 + parts 行唯一性）
  have hyNotOld : y ∉ sListSpine L r x := by
    intro hyS
    have hyr : y ∈ r := aqs_sListSubsetR L hL hgn hm hf hyS
    have hyr' : y ∈ r' := by
      have hpn := partsUniqNonnil L hL hm.1.2.1 hN hp
      have hpne : p ≠ [] := hpn.2.2.2.1
      have hyp : y ∈ p := by rw [hy]; exact aq13w2_getLast!_mem hpne
      exact hpn.2.2.2.2 y hyp
    exact hNne (uniqSublistUnique N hm.1.2.1.1 r' hN r hm.1.2.2.1 ⟨y, hyr', hyr⟩)
  -- 三段 2：旧 SFlag 第二合取
  have hSF := (hm.2.2 hf).2 r' p y hy hp hN hnf' hyNotOld
  rcases List.mem_append.mp hSF with hSl | hFin
  · -- 2a：eList y ∈ sList r x → ③ 升到 rtr
    exact List.mem_append.mpr (Or.inl (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf hSl))
  · -- 3：eList y ∈ FinalDart N → FinalDart N'
    obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp hFin
    obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
    have hlF : finalListSpine L l := decide_eq_true_iff.mp hlfin
    have hlr : l ≠ r := fun h => hf (h ▸ hlF)
    have hfindcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
    have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))) =
        (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))) := by rw [hfindcanon]
    have hn : ntransSpine L N r x 1 =
        replaceSpine r [(splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2] N ++
        [(splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1] := by
      rw [ntrans1 L N r x hf, hsplit_eq]
    rw [hn]
    have hrow : l ∈ (replaceSpine r [(splitNormalListSpine L r (findFaceDarts L x)
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2] N ++
        [(splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).1]).filter
        (fun r => decide (finalListSpine L r)) := by
      rw [List.mem_filter]
      exact ⟨List.mem_append.mpr (Or.inl (memReplaceOfNeMem hlr hlN)),
        by simpa using hlF⟩
    exact List.mem_append.mpr (Or.inr (List.mem_flatten.mpr ⟨l, hrow, hel⟩))

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.TameSpine.aq13w2_memReplaceCasesNodup
#print axioms Kepler.Text.TameSpine.aq13w2_flagConjunctOne
#print axioms Kepler.Text.TameSpine.aq13w2_flagConjunctTwoN

/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12Z — AQ12 叶 W-F3e-ii
  （decl 68 合取 2 的 N/S 两支）。

  HOL：AQ12.hl:3643-:4092 主证 `flag_list` 第二合取，r' 三源中的
  **r' ∈ N** 与 **r' = SND split** 两支（F 支 → 12AA）。

  件目/依赖（开工报价）：1 件 / 1 文件；估 120–180（≤280）。
  · 依赖：SFlag 第二合取（`hm.2.2 hf`）、decl 59/60（12U）、`notBetwn2`、
    `uniqFlattenUniq`、`memReplaceCases`/`memReplaceFstMem`/`memReplaceOfNeMem`
    （TowerBase）、`ntrans1`（Red2Trans）。
  · **不吃 `h4`**；`hfinRtrans : finalListSpine L (rtrans 1)` 是本件唯一新接口
    （见下）。

  ⭐ `hfinRtrans` 接口来源（下游 12AA/总装复用）：
  主证前提 `final_list L (rtrans L N r x 1)`；非 final 支由
  `rtransSpine L N r x 1 = (splitNormalListSpine L r …).2 = S`（`transform_list`
  的 `if_neg hf` + canonical↔f-split 对齐）得 **`hfinS : finalListSpine L S`**。
  S 支矛盾（¬final S 撞 final S）与 sList→S 转移都消费它。

  ⭐ y ∉ sList 的路线（替代 HOL 的 `uniq_sublist_unique` +
  `Hojodcm.NOT_MEM_REPLACE` + `r_not_eq_snd_split_norm_v0` 后两件深链——
  后两件在 Lean 库零移植）：本件 §0 先证 **`replaceSpine` 的 Nodup 精确分解**
  `x ∈ replace f xs g → (x ∈ g ∧ x ≠ f) ∨ (f ∈ g ∧ x ∈ xs)`（`g.Nodup`；
  TowerBase 的 `memReplaceCases` 第一支缺 `x ≠ f`，在 x=f 时是空真）。
  于 N 支直接得 `r' ∈ N ∧ r' ≠ r`；若 `y ∈ sList`，则 `y ∈ r`（56）、
  `y ∈ r'`（partsUniqNonnil 第五合取），`uniqSublistUnique` 给 `r' = r`
  ——撞 `r' ≠ r`。**无需** `r ≠ SND`。sList→S 支用 60；FinalDart N→N' 支
  用行 l final（l ≠ r）走 `memReplaceOfNeMem`。

  陈述对表：`aq12Concl`（TowerBase:307）的第二合取
  `∀ r' p y, y = p.getLast! → p ∈ parts r' → r' ∈ ntrans 1 → ¬final r' → eList y ∈ FinalDart (ntrans 1)`
  在非 final 支、`r' ∈ replace r [S] N`（N∪{S} 段）上的**逐字片段**；
  final 支（r' ∈ N 由 `ntrans_id` 直接给 `hm.2.1 hfin`) 留总装。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12U

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §0 私件：replaceSpine 的 Nodup 精确分解 + getLast! 成员 -/

/-- `g.Nodup` 时 `MEM_replace` 的**精确形**：
`x ∈ replaceSpine f xs g → (x ∈ g ∧ x ≠ f) ∨ (f ∈ g ∧ x ∈ xs)`。
（TowerBase:116 的 `memReplaceCases` 第一支只是 `x ∈ g`，在 `x = f`
时是空真——本件补回 `x ≠ f`，正是 AQ12 合取 2 排除 r'=r 幻影支所需。） -/
private theorem aq12z_memReplaceCasesNodup {α : Type*} [DecidableEq α]
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

/-- `l ≠ [] ⇒ l.getLast! ∈ l`（core 无 `getLast!_mem`，经 `getLast!EqGetLast` 折算）。 -/
private theorem aq12z_getLast!_mem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [getLast!EqGetLast h]
  exact List.getLast_mem h

/-! ## §1 合取 2：r' ∈ N 与 r' = S 两支 -/

/-- **HOL `AQ12_concl` 第二合取的 N/S 段**（AQ12.hl:3643-:4092）：
非 final 支、`r' ∈ replace r [S] N`（即 r' ∈ N 或 r' = S）时
`eList y ∈ FinalDartList (ntrans 1)`。 -/
theorem aq12z_flagConjunctTwoNS (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hfinRtrans : finalListSpine L (rtransSpine L N r x 1)) :
    ∀ (r' : List (ℕ × ℕ)) (p : List (ℕ × ℕ)) (y : ℕ × ℕ),
      y = p.getLast! → p ∈ partsSpine L r' →
      r' ∈ replaceSpine r [(splitNormalListSpine L r (findFaceDarts L x)
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2] N →
      ¬finalListSpine L r' →
      eList y ∈ FinalDartListSpine L (ntransSpine L N r x 1) := by
  intro r' p y hy hp hr' hnf'
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hNnd : N.Nodup := uniqFlatten hm.1.2.1.1 hm.1.2.1.2.1
  -- canonical split ↔ f-split 对齐（12S/12U 同款）
  have hfindcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x)) := by
    rw [hfindcanon]
  -- ntrans 1 的 f-split 写形
  have hn : ntransSpine L N r x 1
      = replaceSpine r [(splitNormalListSpine L r (findFaceDarts L x)
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2] N
        ++ [(splitNormalListSpine L r (findFaceDarts L x)
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1] := by
    rw [ntrans1 L N r x hf, hsplit_eq]
  -- ⭐ hfinRtrans ⇒ final S（rtrans 1 = SND split，if_neg + 对齐）
  have hrtrans : rtransSpine L N r x 1
      = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2 := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf, hsplit_eq]
  have hfinS : finalListSpine L (splitNormalListSpine L r (findFaceDarts L x)
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
    rw [← hrtrans]
    exact hfinRtrans
  rcases aq12z_memReplaceCasesNodup hNnd hr' with ⟨hN, hNne⟩ | ⟨-, hS'⟩
  · -- r' ∈ N：先证 y ∉ sList（56 + parts + 行唯一性撞 r' ≠ r），再用 SFlag 第二合取
    have hyNotS : y ∉ sListSpine L r x := by
      intro hyS
      have hyr : y ∈ r := aqs_sListSubsetR L hL hgn hm hf hyS
      have hyr' : y ∈ r' := by
        have hpn := partsUniqNonnil L hL hm.1.2.1 hN hp
        have hpne : p ≠ [] := hpn.2.2.2.1
        have hyp : y ∈ p := by rw [hy]; exact aq12z_getLast!_mem hpne
        exact hpn.2.2.2.2 y hyp
      exact hNne (uniqSublistUnique N hm.1.2.1.1 r' hN r hm.1.2.2.1 ⟨y, hyr', hyr⟩)
    have hSF := (hm.2.2 hf).2 r' p y hy hp hN hnf' hyNotS
    rcases List.mem_append.mp hSF with hSl | hFin
    · -- eList y ∈ sList → 60 给 ∈ S；S final ⇒ S ∈ filter final N'
      have hSnd : eList y ∈ (splitNormalListSpine L r (findFaceDarts L x)
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 :=
        aqs_sListInRtrans L hL hgn hm hf (findFaceDarts L x) rfl rfl rfl rfl hSl
      rw [hn]
      refine List.mem_flatten.mpr ⟨_, List.mem_filter.mpr ⟨?_, by simpa using hfinS⟩, hSnd⟩
      exact List.mem_append.mpr (Or.inl
        (memReplaceFstMem hm.1.2.2.1 (List.mem_singleton_self _)))
    · -- eList y ∈ FinalDart N → 行 l final（l ≠ r）走 memReplaceOfNeMem
      obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp hFin
      obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
      have hlfinal : finalListSpine L l := decide_eq_true_iff.mp hlfin
      have hlr : l ≠ r := fun h => hf (h ▸ hlfinal)
      rw [hn]
      refine List.mem_flatten.mpr ⟨l, List.mem_filter.mpr
        ⟨List.mem_append.mpr (Or.inl (memReplaceOfNeMem hlr hlN)),
          by simpa using hlfinal⟩, hel⟩
  · -- r' = S：¬final S 撞 hfinS
    have hSeq : r' = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2 := List.mem_singleton.mp hS'
    exact absurd hfinS (hSeq ▸ hnf')

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12z_flagConjunctTwoNS

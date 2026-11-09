/-
  Kepler.Text.TameSpine.JcajyduAqLeaf1B — AQ1 叶第二批：`ntrans 1` 的
  flatten 分解 + `split.1`/`split.2` 的成员二分（HOL `AQ1` 末段的前置）。

  目标链（HOL `AQ1`，AQ1.hl:2153-:2201）：
  `ntrans L N r x 1 = replace r [s2] N ++ [s1]`（`ntrans1`），故
  `(ntrans 1).flatten = (flatten (replace r [s2] N)) ++ s1`；
  本批把它化成 **按 `r` 位置切开** 的具体形：

    `N = N₁ ++ r :: N₂`（`r` **首现**，故 `r ∉ N₁`）⇒
    `replaceSpine r [s2] N = N₁ ++ [s2] ++ N₂` ⇒
    `(ntrans 1).flatten = (N₁.flatten ++ s2) ++ N₂.flatten ++ s1`

  （HOL 用一般形 `change_flatten_replace_filter` + `Perm` + `sizel` 论证；
  本处 `r ∈ N` 特化后直接分解，省掉 `Perm`/计数层——见 DELIVERY_AQ1 §2 第 1 项。）

  ┌─ 件表（`patch_leaf1b.diff`）─────────────────────────────────
  │ ① `aq1b_splitAtMem`：`r ∈ N` ⇒ `N = N₁ ++ r :: N₂` 且 **`r ∉ N₁`**（首现分解）；
  │ ② `aq1b_replaceSpineOfNotMem`：`r ∉ N₁` ⇒
  │    `replaceSpine r [s2] (N₁ ++ r :: N₂) = N₁ ++ [s2] ++ N₂`；
  │ ③ `aq1b_flattenNtrans1`：总合 ①②+`ntrans1` 的 flatten 分解；
  │ ④ `aq1b_split1Mem`：`d ∈ split.1 → d ∈ r ∨ d ∉ N.flatten`
  │    （new1 侧 = Leaf1 ⑦；f1 侧 ⊆ r）；
  │ ⑤ `aq1b_split2Mem`：`d ∈ split.2 → d ∈ r ∨ d ∉ N.flatten`
  │    （f2 ⊆ r；window 侧 = `windowFstNotMemNFlatten`）。
  └──────────────────────────────────────────────────────────────

  ┌─ 边界（未落，见 DELIVERY_AQ1B §2）────────────────────────────
  │ 互不交（new1×window / new1×f2 / f1×window 三块引擎已有；
  │ f1×f2 走 TameList72 公开化后的 `betwn_succ_subset`/`betwn_next_subset`/
  │ `betwn_or_betwn_cover` + 弧恒等式）与总装（`nodup_append` ×3）。
  └──────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem)

/-! ## §1 按 `r` 首现切开 `N`，`replace`/`flatten` 落到具体形 -/

/-- `r ∈ N` ⇒ `N` 可按 **`r` 的首现** 切成 `N₁ ++ r :: N₂`，且 `r ∉ N₁`。 -/
theorem aq1b_splitAtMem (r : List (ℕ × ℕ)) :
    ∀ N : List (List (ℕ × ℕ)), r ∈ N → ∃ N₁ N₂ : List (List (ℕ × ℕ)),
      N = N₁ ++ r :: N₂ ∧ r ∉ N₁ := by
  intro N
  induction N with
  | nil => intro h; exact absurd h (by simp)
  | cons a t ih =>
    intro h
    by_cases har : a = r
    · exact ⟨[], t, by rw [har]; rfl, by simp⟩
    · obtain ⟨N₁, N₂, hN, hnot⟩ := ih (by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm har
        · exact h)
      refine ⟨a :: N₁, N₂, by rw [hN]; rfl, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => har h.symm, hnot⟩

/-- `r ∉ N₁` ⇒ `replace` 只替换 `r` 的首现：`replaceSpine r [s2] (N₁ ++ r :: N₂)
= N₁ ++ [s2] ++ N₂`。 -/
theorem aq1b_replaceSpineOfNotMem (r : List (ℕ × ℕ)) (s2 : List (ℕ × ℕ)) :
    ∀ (N₁ N₂ : List (List (ℕ × ℕ))), r ∉ N₁ →
      replaceSpine r [s2] (N₁ ++ r :: N₂) = N₁ ++ [s2] ++ N₂ := by
  intro N₁
  induction N₁ with
  | nil => intro N₂ _; simp [replaceSpine]
  | cons a t ih =>
    intro N₂ hnot
    have hat : a ≠ r := fun h => hnot (by simp [h])
    have ht : r ∉ t := fun h => hnot (List.mem_cons_of_mem _ h)
    rw [List.cons_append, replaceSpine]
    rw [if_neg (fun h : a = r => hat h)]
    rw [ih N₂ ht]
    rfl

/-- **`(ntrans 1).flatten` 的切口形**（`r` 的首现分解）：
`∃ N₁ N₂, N = N₁ ++ r :: N₂ ∧ r ∉ N₁ ∧
  (ntrans 1).flatten = (N₁.flatten ++ split.2) ++ N₂.flatten ++ split.1`。 -/
theorem aq1b_flattenNtrans1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∃ N₁ N₂ : List (List (ℕ × ℕ)), N = N₁ ++ r :: N₂ ∧ r ∉ N₁ ∧
      (ntransSpine L N r x 1).flatten
        = (N₁.flatten ++ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2)
          ++ N₂.flatten
          ++ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
  obtain ⟨N₁, N₂, hN, hnot⟩ := aq1b_splitAtMem r N hm.1.2.2.1
  refine ⟨N₁, N₂, hN, hnot, ?_⟩
  rw [ntrans1 L N r x hf, hN, List.flatten_append]
  rw [aq1b_replaceSpineOfNotMem r _ N₁ N₂ hnot]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

/-! ## §2 `split.1` / `split.2` 的成员二分 -/

/-- `split.1` 的成员二分（new1 侧 ∉ `flatten N`；f1 侧 ⊆ r）。 -/
theorem aq1b_split1Mem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hd : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1) :
    d ∈ r ∨ d ∉ N.flatten := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hsplit : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (ndSpine L)).flatten.reverse
        ++ ([nextEl r (lYSpine L r x)] ++ between r (nextEl r (lYSpine L r x))
            (prevEl r (lZSpine L N r x)) ++ [prevEl r (lZSpine L N r x)]) := by
    rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x)), hnextz1]
  rw [hsplit] at hd
  rcases List.mem_append.mp hd with h1 | h1
  · exact Or.inr (aq1_new1NotMemFlatten L hL hgn hunL hm hf d (List.mem_reverse.mp h1))
  · rcases List.mem_append.mp h1 with h2 | h2
    · rcases List.mem_append.mp h2 with h3 | h3
      · exact Or.inl (by rw [List.mem_singleton.mp h3]; exact nextEl_mem_of_mem hyr)
      · exact Or.inl (memBetweenOfMem h3)
    · exact Or.inl (by rw [List.mem_singleton.mp h2]; exact hz1r)

/-- `split.2` 的成员二分（f2 侧 ⊆ r；window 侧 ∉ `flatten N`）。 -/
theorem aq1b_split2Mem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ}
    (hd : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2) :
    d ∈ r ∨ d ∉ N.flatten := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hsplit2 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [hnextz1]
  rw [hsplit2] at hd
  rcases List.mem_append.mp hd with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · rcases List.mem_append.mp h2 with h3 | h3
      · exact Or.inl (by rw [List.mem_singleton.mp h3]; exact hzr)
      · exact Or.inl (memBetweenOfMem h3)
    · exact Or.inl (by rw [List.mem_singleton.mp h2]; exact hyr)
  · exact Or.inr (fun hemem =>
      windowFstNotMemNFlatten L hL hgn hunL hm hf h1 (List.mem_map.mpr ⟨d, hemem, rfl⟩))

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq1b_splitAtMem
#print axioms Kepler.Text.TameSpine.aq1b_replaceSpineOfNotMem
#print axioms Kepler.Text.TameSpine.aq1b_flattenNtrans1
#print axioms Kepler.Text.TameSpine.aq1b_split1Mem
#print axioms Kepler.Text.TameSpine.aq1b_split2Mem

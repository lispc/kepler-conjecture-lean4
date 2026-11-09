/-
  JcajyduAqLeaf8W3ad — AQ8 波 3ad：**farc 侧分派**（SND-part 的 head 在 farc ⇒ 该 part 属 farc）。

  ┌─ 件（两件，≤60）─────────────────────────────────────────────
  │ ① aq8w3ad_arcFarcExcl   `arc3` 与 `farc` 元素互异（`nodup_append` 三分量）
  │ ② aq8w3ad_memFarcOfHead `u ∈ parts L SND` 且 `HD u ∈ farc` ⇒ `u ∈ parts L farc`
  │    （junction = W3ab 的 `parts L SND = parts L arc3 ++ parts L farc`）
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3ad_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3ac

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- **arc3 与 farc 元素互异**：`SND = arc3 ++ farc` 无重 ⇒ 两段无公共元素。 -/
theorem aq8w3ad_arcFarcExcl (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x) ∈ ntransSpine L N r x 1) :
    ∀ a ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]),
      ∀ b ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x), a ≠ b := by
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  obtain ⟨hndS, -⟩ := normalListUniqNonnil hnN hsN
  exact (List.nodup_append.mp hndS).2.2

/-- **farc 侧分派**：SND-part 的 head 在 farc ⇒ 该 part 属 `parts L farc`。

junction（W3ab）拆出 `u ∈ parts arc3 ∨ u ∈ parts farc`；
前者给 `HD u ∈ arc3`，与 `HD u ∈ farc` 撞 ①。 -/
theorem aq8w3ad_memFarcOfHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x) ∈ ntransSpine L N r x 1)
    (hfarne : between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x) ≠ [])
    {u : List (ℕ × ℕ)}
    (hu : u ∈ partsSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))
    (hufc : u.head! ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)) :
    u ∈ partsSpine L (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)) := by
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  have hsplit := aq8w3ab_partsSndSplit L hL hgn h1 h2 h3 h4 h5 hm hf hsN hfarne
  have hu' := hu
  rw [hsplit] at hu'
  rcases List.mem_append.mp hu' with h3' | hf'
  · exfalso
    have hune : u ≠ [] := partsAllNonnil L hndS hneS u hu
    have harc3nd : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]).Nodup := (List.nodup_append.mp hndS).1
    have harc3ne : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ≠ [] := by
      intro h0
      have hmem : lZSpine L N r x ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
          (lYSpine L r x) ++ [lYSpine L r x]) :=
        List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_singleton_self _))))
      rw [h0] at hmem
      exact List.not_mem_nil hmem
    have hd3 : u.head! ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) :=
      memPartsImp L harc3nd harc3ne h3' _ (List.head!_mem_self hune)
    exact (aq8w3ad_arcFarcExcl L hL hgn h1 h2 h3 h4 h5 hm hf hsN _ hd3 _ hufc) rfl
  · exact hf'

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3ad_arcFarcExcl
#print axioms Kepler.Text.TameSpine.aq8w3ad_memFarcOfHead

/-
  JcajyduAqLeaf8W3e — AQ8 波 3e：路线 3（只证 `s` 分段在面 x）。

  ┌─ 分段账（逐段判定，先报）─────────────────────────────────────
  │ `s = SND split` 展开 = `[z] ++ between r z y ++ [y] ++ between f y z`
  │ （z = l'z、y = l'y、f = findFaceDarts L (l'y)）。四段：
  │ ① `[z]`：`pplhuljV0 .2.1` 给 `z ∈ findFaceDarts L x` —— **零缺口**
  │ ② `[y]`：`pplhuljV0 .1` 给 `y ∈ findFaceDarts L x` —— **零缺口**
  │ ③ `between f y z`：f 是面表 ⇒ `betwnMem` 给 `a ∈ findFaceDarts L (l'y)`
  │    = `findFaceDarts L x`（面相等 `aq10_memFindFaceImpFacesEq`）—— **零缺口**
  │    （本文件 ① 落成**无条件**定理）
  │ ④ `between r z y`：**唯一残余段**——需「r-弧在面 x」；本件以命名前提
  │    `harcF` 接住（不偷塞新槽：它是 ②③① 之外唯一显式缺口，
  │    已记 DELIVERY §AQ8W3e-2）。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ ① aq8w3e_betwnFaceSubFaceX   ③ 段无条件：面内弧 ⊆ findFaceDarts L x
  │ ② aq8w3e_sSubFaceDartsOfArc  SND 四段 ⇒ `∀ a ∈ s, a ∈ findFaceDarts L x`
  │    （前提 = ① + `harcF`（④ 段）+ 面相等载体）
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）────────────────────────────────────────────────
  │ `betwn f y z` 的 `f` 取具体项 `findFaceDarts L (lYSpine L r x)`（HOL
  │ 的 `f` 由 `mem_find_face_imp_faces_eq` 折算为此项）；`MEM` 逐字。
  │ `harcF` 是④段的**显式命名缺口**，非新数学前提（应用侧 = r-弧块性质）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3e_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3d

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 面内弧段（③ 段，无条件） -/

/-- **③ 段无条件**：面 `findFaceDarts L (l'y)` 内的开弧
`between … (l'y) (l'z)` 的成员都在 `findFaceDarts L x` 内。

`betwnMem` 给成员在面表 `findFaceDarts L (l'y)` 内；面相等
（`aq10_memFindFaceImpFacesEq` + `pplhuljV0 .1`）折到 `findFaceDarts L x`。 -/
theorem aq8w3e_betwnFaceSubFaceX (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ a ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x), a ∈ findFaceDarts L x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hface : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hpp.1
  intro a ha
  rw [hface] at ha
  exact betwnMem ha

/-! ## §1 SND 四段 ⇒ 全体在面 x -/

/-- **路线 3 的 `s`-版**：SND 展开四段（`[z] ++ between r z y ++ [y] ++
between f y z`）中，①②③ 段无条件闭合（`pplhuljV0`、§0），④ 段
（`between r z y`）以命名前提 `harcF` 接住。 -/
theorem aq8w3e_sSubFaceDartsOfArc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {s : List (ℕ × ℕ)}
    (harc : s = [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x))
    (harcF : ∀ a ∈ between r (lZSpine L N r x) (lYSpine L r x),
      a ∈ findFaceDarts L x) :
    ∀ a ∈ s, a ∈ findFaceDarts L x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  intro a ha
  rw [harc] at ha
  -- ha : a ∈ ([z] ++ arc) ++ [y] ++ faceArc
  rcases List.mem_append.mp ha with h1 | h4
  · rcases List.mem_append.mp h1 with h2 | h3
    · rcases List.mem_append.mp h2 with hz | harc'
      · rw [List.mem_singleton] at hz
        rw [hz]
        exact hpp.2.1
      · exact harcF a harc'
    · rw [List.mem_singleton] at h3
      rw [h3]
      exact hpp.1
  · exact aq8w3e_betwnFaceSubFaceX L hL hgn hm hf a h4

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3e_betwnFaceSubFaceX
#print axioms Kepler.Text.TameSpine.aq8w3e_sSubFaceDartsOfArc

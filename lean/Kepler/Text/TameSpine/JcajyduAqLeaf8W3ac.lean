/-
  JcajyduAqLeaf8W3ac — AQ8 波 3ac：**farc 侧单点表**（B 路收口的第一块）。

  ┌─ 件 ──────────────────────────────────────────────────────────
  │ ① aq8w3ac_farcPartsSingleton
  │    `u ∈ parts L farc ⇒ u = [u.head!]`（farc 的 parts 全为单点）
  │    依据：`aqs_partsFBetwnPure`（W1b，窗口 = `findFaceDarts L x` 面表弧）
  │    + 面相等把 `findFaceDarts L (l'y)` 折到 `findFaceDarts L x`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3ac_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3ab

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- **farc 侧 parts 是单点**：`u ∈ parts L farc ⇒ u = [u.head!]`。

`aqs_partsFBetwnPure`（W1b:106）给窗口 parts = `map (fun d => [d])`；
窗口面用面相等（`aq10_memFindFaceImpFacesEq` + `pplhuljV0 .1`）从
`findFaceDarts L x` 折到 `findFaceDarts L (l'y)`（反向 rw）。 -/
theorem aq8w3ac_farcPartsSingleton (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {u : List (ℕ × ℕ)}
    (hu : u ∈ partsSpine L (between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x))) :
    u = [u.head!] := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hface : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hpp.1
  have hparts : partsSpine L (between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x))
      = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (fun d => [d]) := by
    rw [hface]
    exact aqs_partsFBetwnPure L hL hgn hm hf
  rw [hparts] at hu
  obtain ⟨d, -, hd⟩ := List.mem_map.mp hu
  rw [← hd]
  rfl

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3ac_farcPartsSingleton

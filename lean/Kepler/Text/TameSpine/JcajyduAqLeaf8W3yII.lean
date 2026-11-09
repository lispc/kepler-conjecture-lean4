/-
  JcajyduAqLeaf8W3yII — AQ8 波 3y-ii：`partsFstHdInjSND` 的**异侧**分支。

  ┌─ 范围 ────────────────────────────────────────────────────────
  │ 异侧：一 head 在 `farc`（f-弧）、另一在 `arc3`（r-弧三段）
  │ ⇒ 两端 FST 必不同（`betwnNotInFstRtrans` vs r-弧 FST ∈ `map FST r`）。
  │ ⇒ 该情形在 `(HD u).1 = (HD v).1` 前提下为空 ⇒ 单射自动成立。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3yII_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3yI

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl mem_darts_of_mem_findFace)

/-- **异侧 FST 必异**：`u.head!` 在 f-弧内、`v.head!` 在 r-弧三段内
（`[z] ++ between r z y ++ [y]`）⇒ 两者 `FST` 不相等。

f-弧端：`aq8w3_betwnNotInFstRtrans`（W3a ①，无条件）⇒ FST ∉ `r.map fst`；
r-弧端：三段元素都在 `r` 内（`zMemRtransClean` / `betwnMem` / `ytransMemRtrans`）
⇒ FST ∈ `r.map fst`。 -/
theorem aq8w3yII_crossHeadsNe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {u v : List (ℕ × ℕ)}
    (huf : u.head! ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x))
    (hvr : v.head! ∈ [lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) :
    (u.head!).1 ≠ (v.head!).1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  -- f-弧端：FST ∉ r.map fst
  have hfac : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hpp.1
  have huf' : u.head! ∈ between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x) := by
    rw [← hfac]; exact huf
  have hnotmem : (u.head!).1 ∉ r.map Prod.fst :=
    aq8w3_betwnNotInFstRtrans L hL hgn hunL hm hf huf'
  -- r-弧端：FST ∈ r.map fst
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hvr' : v.head! ∈ r := by
    rcases List.mem_append.mp hvr with h1 | hy'
    · rcases List.mem_append.mp h1 with hz' | hb
      · rw [List.mem_singleton] at hz'
        rw [hz']; exact hz
      · exact betwnMem hb
    · rw [List.mem_singleton] at hy'
      rw [hy']; exact hy
  have hmem : (v.head!).1 ∈ r.map Prod.fst :=
    List.mem_map.mpr ⟨v.head!, hvr', rfl⟩
  intro heq
  exact hnotmem (heq ▸ hmem)

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3yII_crossHeadsNe

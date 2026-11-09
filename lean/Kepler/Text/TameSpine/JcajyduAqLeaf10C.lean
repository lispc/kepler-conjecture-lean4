/-
  JcajyduAqLeaf10C — AQ10-a3：`aq10_pointRemarkMemSplit`（AQ10.hl:39-95）收口。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ aq10_pointRemarkMemSplit  AQ10.hl:39-95（point_remark_mem_split）
  │ 主证 aq10 不在本批（AQ10-b）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字）───────────────────────────────────
  │ ① `ztrans L N r x 0` ↦ `lZSpine L N r x`、`l'y` ↦ `lYSpine`
  │    （trans0 第三/四合取，JcajyduRed2Trans:153）。
  │ ② Spine 载体：`good_list`↦`GoodList`（经 hL）、`marked_list`↦
  │    `MarkedListSpineFull`。
  │ ③ 结论 `MEM x (APPEND [z] (APPEND (betwn r z y) [y]))` 逐字同形。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ────────────────────────────────────────────────────────
  │ `betwnCases` 四支：x=z / x=y 直取；x ∈ between r z y 直取；
  │ x ∈ between r y z 用 `aq10_indexfYLeZInR0`（indexf w y < indexf w z）
  │ + `indexfAddLeft/Right/Betwn` + `indexfPrev`（w = next_el r x ⇒
  │ indexf w x = len-1）+ `indexf_lt_sizel` 反证（0 < indexf x z 与
  │ len-1+indexf x z < len 矛盾）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `aq10_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList53

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl fList findFaceDarts listOfDarts GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- HOL `point_remark_mem_split`（AQ10.hl:39-95）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ ~(final_list L r) ⇒
MEM x (APPEND [z] (APPEND (betwn r z y) [y]))`，`z = ztrans … 0 = l'z`、
`y = l'y`。 -/
theorem aq10_pointRemarkMemSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    x ∈ [lZSpine L N r x] ++
      (between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
  have hexp : x ∈ [lZSpine L N r x] ++
        (between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x])
      ↔ (x = lZSpine L N r x ∨
          x ∈ between r (lZSpine L N r x) (lYSpine L r x) ∨
          x = lYSpine L r x) := by
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]
    tauto
  rw [hexp]
  rcases betwnCases (s := r) (x := lZSpine L N r x) (y := x) (z := lYSpine L r x)
    hyz.symm hnd hz hxr hy with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exfalso
    have hpp := aq10_indexfYLeZInR0 L hL hgn hm hf
    have hw : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
    have hwEq : nextEl (findFaceDarts L x) x = nextEl r x :=
      (hm.1.2.2.2.2.2.1).symm
    have hbetw := indexfBetwn (x := lYSpine L r x) (y := x)
      (z := lZSpine L N r x) hyz hnd hy hz h
    have haddB := indexfAddBetwn (x := lYSpine L r x) (y := x)
      (z := lZSpine L N r x) hyz hnd hy h hz
    have hxzpos : 0 < indexf x (lZSpine L N r x) r := by omega
    have haddL := indexfAddLeft (x := nextEl (findFaceDarts L x) x)
      (y := lYSpine L r x) (z := lZSpine L N r x) hw hy hz (le_of_lt hpp)
    have hleR : indexf x (lZSpine L N r x) r
        ≤ indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r := by omega
    have haddR := indexfAddRight (x := nextEl (findFaceDarts L x) x) (y := x)
      (z := lZSpine L N r x) hw hxr hz hleR
    have hprev : indexf (nextEl (findFaceDarts L x) x) x r = r.length - 1 :=
      indexfPrev hxr hw hnd hwEq.symm
    have hlt := indexfLtSizel hw hz
    have hlen : 0 < r.length := List.length_pos_of_mem hxr
    omega

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq10_pointRemarkMemSplit

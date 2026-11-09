/-
  JcajyduAqLeaf8W3yI — AQ8 波 3y-i：`partsFstHdInjSND` 的 **farc-同侧**分支。

  ┌─ 范围（按 W3y 骨架 §① 的第 3 步）────────────────────────────
  │ 两 part 的 head 都落在 `farc = between (find_face L (l'y)) y z` 内
  │ ⇒ 同面（f-弧 ⇒ `findFaceDarts L x`）+ 同 node（同 FST + dart 集）
  │ ⇒ `simpleHypermapList` 塌出 `HD v = HD u` ⇒ `uniqSublistUnique` 收口。
  │ 异侧与 r-弧同侧两支另发。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3yI_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3w
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl mem_darts_of_mem_findFace)

/-- **farc-同侧**：`u, v ∈ parts L SND` 且两 head 都在 f-弧内、`FST` 相等
⇒ `u = v`。

链：`betwnMem` ⇒ head ∈ 面表 `findFaceDarts L (l'y)` ⇒ 面相等
（`aq10_memFindFaceImpFacesEq`）⇒ head ∈ `findFaceDarts L x`；
`memHypermapOfListNode` 给 `HD v ∈ node (HD u)`；
`faceTableSubset` 给 `HD v ∈ face (HD u)`；`simpleHypermapList` 塌出
`HD v = HD u`；两 part 共享该元素 ⇒ `uniqSublistUnique`。 -/
theorem aq8w3yI_farcHeadsEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hsN : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x) ∈ ntransSpine L N r x 1)
    {u v : List (ℕ × ℕ)}
    (hu : u ∈ partsSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))
    (hv : v ∈ partsSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)))
    (huf : u.head! ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x))
    (hvf : v.head! ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x))
    (heq : (u.head!).1 = (v.head!).1) : u = v := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  have hsn : (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x)).Nodup ∧ _ ≠ [] := normalListUniqNonnil hnN hsN
  obtain ⟨hndS, hneS⟩ := hsn
  have hune : u ≠ [] := partsAllNonnil L hndS hneS u hu
  have hvne : v ≠ [] := partsAllNonnil L hndS hneS v hv
  have hup : u.head! ∈ u := List.head!_mem_self hune
  have hvp : v.head! ∈ v := List.head!_mem_self hvne
  -- dart 集（f-弧 ⇒ 面表 ⇒ dart）
  have huD : u.head! ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L (betwnMem huf)
  have hvD : v.head! ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L (betwnMem hvf)
  -- 同面 ⇒ 同面表 x
  have hufx : u.head! ∈ findFaceDarts L x :=
    aq8w3e_betwnFaceSubFaceX L hL hgn hm hf _ huf
  have hvfx : v.head! ∈ findFaceDarts L x :=
    aq8w3e_betwnFaceSubFaceX L hL hgn hm hf _ hvf
  -- 同 node
  have hnode : v.head! ∈ (hypermapOfList L hL).node u.head! :=
    (memHypermapOfListNode hL hgn huD).mpr ⟨heq, hvD⟩
  -- 同面 ⇒ `HD v ∈ face (HD u)`
  have hfin : v.head! ∈ findFaceDarts L (u.head!) := by
    rw [aq10_memFindFaceImpFacesEq hL.1 hufx]
    exact hvfx
  have hface : v.head! ∈ (hypermapOfList L hL).face u.head! :=
    Kepler.Text.TameCorrCard.faceTableSubset hL huD hfin
  -- Simple 塌缩
  have hsimple := simpleHypermapList L hL hgn hunL
  have hinter : v.head! ∈ (hypermapOfList L hL).node u.head!
      ∩ (hypermapOfList L hL).face u.head! := ⟨hnode, hface⟩
  rw [hsimple u.head! (List.mem_toFinset.mpr huD)] at hinter
  have hheadEq : v.head! = u.head! := Set.mem_singleton_iff.mp hinter
  -- 两 part 共享 head ⇒ 同一 part
  have hfl : (partsSpine L (([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))).flatten.Nodup := by
    rw [partsFlatten L hndS hneS]; exact hndS
  exact uniqSublistUnique _ hfl u hu v hv
    ⟨u.head!, hup, by rw [← hheadEq]; exact hvp⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3yI_farcHeadsEq

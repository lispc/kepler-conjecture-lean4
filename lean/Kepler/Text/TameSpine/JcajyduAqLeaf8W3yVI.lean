/-
  JcajyduAqLeaf8W3yVI — AQ8 波 3y-vi：`partsFstHdInjSND` 的 **同面支**。

  ┌─ 范围 ────────────────────────────────────────────────────────
  │ `u, v ∈ parts L SND`、两 head **同面**（`findFaceDarts L (HD u) =
  │ findFaceDarts L (HD v)`）、`(HD u).1 = (HD v).1` ⇒ `u = v`。
  │ 与 W3yI（farc-同侧）同构，只把「farc 成员性」换成「同面」假设。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3yVI_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3yII

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  mem_darts_of_mem_findFace)

/-- **同面支**：`u, v ∈ parts L SND` 且两 head 同面、`FST` 相等 ⇒ `u = v`。

`memHypermapOfListNode`（同 FST ⇒ `HD v ∈ node (HD u)`）+
`dart_in_face`/`faceTableSubset`（同面 ⇒ `HD v ∈ face (HD u)`）+
`simpleHypermapList`（`node ∩ face = {HD u}`）⇒ `HD v = HD u`
⇒ 两 part 共享 head ⇒ `uniqSublistUnique`。 -/
theorem aq8w3yVI_sameFaceHeadsEq (L : fgraph ℕ) (hL : GoodList L)
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
    (hfaceEq : findFaceDarts L (u.head!) = findFaceDarts L (v.head!))
    (heq : (u.head!).1 = (v.head!).1) : u = v := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  obtain ⟨hndS, hneS⟩ := normalListUniqNonnil hnN hsN
  have hune : u ≠ [] := partsAllNonnil L hndS hneS u hu
  have hvne : v ≠ [] := partsAllNonnil L hndS hneS v hv
  have hup : u.head! ∈ u := List.head!_mem_self hune
  have hvp : v.head! ∈ v := List.head!_mem_self hvne
  -- dart 集（SND 是 normal_list 成员 ⇒ 其元素都是 dart）
  have hus : u.head! ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) :=
    memPartsImp L hndS hneS hu _ hup
  have hvs : v.head! ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) :=
    memPartsImp L hndS hneS hv _ hvp
  have huD : u.head! ∈ listOfDarts L :=
    normalListListOfDarts hnN _ (List.mem_flatten.mpr ⟨_, hsN, hus⟩)
  have hvD : v.head! ∈ listOfDarts L :=
    normalListListOfDarts hnN _ (List.mem_flatten.mpr ⟨_, hsN, hvs⟩)
  -- 同 node
  have hnode : v.head! ∈ (hypermapOfList L hL).node u.head! :=
    (memHypermapOfListNode hL hgn huD).mpr ⟨heq, hvD⟩
  -- 同面 ⇒ `HD v ∈ face (HD u)`
  have hfin : v.head! ∈ findFaceDarts L (u.head!) := by
    rw [hfaceEq]
    exact (dart_in_face L _).mpr hvD
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
#print axioms Kepler.Text.TameSpine.aq8w3yVI_sameFaceHeadsEq

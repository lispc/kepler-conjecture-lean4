/-
  Kepler.Text.Reduction1AqtE — 批③ AUQTZYZ_list：五叶件（冻结表叶序）+ e_list 两件实件。

  本文件（按工单叶序）：
  · 叶 3 `lemmaInNode3` —— HOL hypermap.hl:9998；在库
    `Hypermap.mem_node_of_atomChoice_mem_node_quotient`（同名同陈述）薄转发。
  · 叶 4 `memFindFaceNonempty` + `headMemListOfDarts` —— HOL
    list_hypermap `mem_find_face_nonempty`；在库 `TameLp.mem_darts_of_mem_findFace`
    直转 + 面首元入 dart 表（`List.mem_flatten` 直拼）。
  · 叶 5 `valueLoopMapOfHeadOfAtom` —— HOL hypermap.hl:8633；证体：
    `headOfAtom_mem_atom`（第二分量即 `≠ nodeMap.symm`）+
    `loopMap_eq_faceMap_or_nodeMap_symm` 二分。
  · 叶 2 `fstNodeHypermapOfList` —— HOL list_hypermap；在库
    `TameSpine.memHypermapOfListNode`（node 轨道 = 同首分量 dart 全类）两向直取。
  · 叶 1（部分，实件两枚）——
    `eListNotMemFaceOfNormal`：normal 面 f 内 d 的 e_list 伙伴不在 f
    （simple + node 非退化 + `SIMPLE_FACE_EDGE_INJ`，PackingAuto22:13184 在库件）；
    `eListMemPartsOfMemR`：若 eList d ∈ r，则 eList d 是 r 的某 part 的末元
    （`normalConditionLastParts` 断点判据 + `partsFlatten` + 面互斥）。
    缺口（冻结）：`eList d ∈ f ∪ r` 的第三面排除 / 覆盖前提，见 DELIVERY §4。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.TameList63
import Kepler.Text.Reduction1AqtD
import Kepler.Text.PackingAuto22
import Kepler.Text.TameCorrCard
import Kepler.Text.TameSpine.JcajyduAqSplit1F
import Kepler.Text.TameSpine.Reduction3CoreSplitNormal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)
open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList listPairs listOfDarts findFaceDarts eList fList nextEl)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.TameSpine (NormalListSpine Dih2kListSpine quotientListSpine listOfFaces
  partsSpine)

/-! ## §1 叶 3：`lemma_in_node3`（hypermap.hl:9998） -/

/-- **HOL `lemma_in_node3`**（hypermap.hl:9998）：`is_normal H NF ∧
x ∈ darts_of_family NF ∧ atomChoice y ∈ node (quotient) (atomChoice x) ⇒ y ∈ node H x`。
在库 `mem_node_of_atomChoice_mem_node_quotient` 薄转发。 -/
theorem lemmaInNode3 {α : Type*} [DecidableEq α] {H : Hypermap α} {NF : Set (Loop α)}
    (hnf : H.IsNormalFamily NF) {x : α} (hx : x ∈ Kepler.Text.Hypermap.dartsOfFamily NF)
    {y : α} (h : H.atomChoice NF y
      ∈ (H.quotientHypermap hnf).node (H.atomChoice NF x)) :
    y ∈ H.node x :=
  H.mem_node_of_atomChoice_mem_node_quotient hnf hx h

/-! ## §2 叶 4：`mem_find_face_nonempty` + 面首元入 dart 表 -/

/-- **HOL `mem_find_face_nonempty`**（list_hypermap）：`find_face L d` 的成员
必是 dart。在库 `mem_darts_of_mem_findFace`（TameLp:5041）直转。 -/
theorem memFindFaceNonempty {L : fgraph ℕ} {y d : ℕ × ℕ}
    (h : y ∈ findFaceDarts L d) : y ∈ listOfDarts L :=
  Kepler.Text.TameLp.mem_darts_of_mem_findFace L h

/-- `f ∈ list_of_faces L` 的成员都是 dart（`listOfDarts = (L.map listPairs).flatten`，
`List.mem_flatten` 一步）。 -/
theorem memListOfDartsOfMemFace {L : fgraph ℕ} {f : List (ℕ × ℕ)}
    (hf : f ∈ listOfFaces L) {d : ℕ × ℕ} (hd : d ∈ f) : d ∈ listOfDarts L :=
  List.mem_flatten.mpr ⟨f, hf, hd⟩

/-- `f ∈ list_of_faces L` 且非空 ⇒ `f.head! ∈ list_of_darts L`。 -/
theorem headMemListOfDarts {L : fgraph ℕ} {f : List (ℕ × ℕ)}
    (hf : f ∈ listOfFaces L) (hne : f ≠ []) : f.head! ∈ listOfDarts L :=
  memListOfDartsOfMemFace hf (List.head!_mem_self hne)

/-! ## §3 叶 5：`value_loop_map_of_head_of_atom`（hypermap.hl:8633） -/

/-- **HOL `value_loop_map_of_head_of_atom`**（hypermap.hl:8633）：
`is_normal H NF ∧ L ∈ NF ∧ x ∈ L.darts ⇒ loop_map L (head_of_atom x) =
face_map H (head_of_atom x)`。证体：`headOfAtom_mem_atom` 第二分量（head 处
loop_map ≠ nodeMap.symm）+ `loopMap_eq_faceMap_or_nodeMap_symm` 二分。 -/
theorem valueLoopMapOfHeadOfAtom {α : Type*} [DecidableEq α] {H : Hypermap α}
    {NF : Set (Loop α)} {L : Loop α} {x : α}
    (hnf : H.IsNormalFamily NF) (hL : L ∈ NF) (hx : x ∈ L.darts) :
    L.map (H.headOfAtom NF x) = H.faceMap (H.headOfAtom NF x) := by
  have hhead := H.headOfAtom_mem_atom hnf hL hx
  have hhd : H.headOfAtom NF x ∈ L.darts :=
    H.mem_darts_of_mem_atom hx hhead.1
  rcases H.loopMap_eq_faceMap_or_nodeMap_symm hnf hL hhd with h | h
  · exact h
  · exact absurd h hhead.2

/-! ## §4 叶 2：`fst_node_hypermap_of_list` -/

/-- **HOL `fst_node_hypermap_of_list`**（list_hypermap，首分量方向）：
`good_list L ∧ good_list_nodes L ∧ x ∈ list_of_darts L ∧ y ∈ node H x ⇒
FST x = FST y`。在库 `memHypermapOfListNode`（node 轨道 = 同首分量 dart 全类）
的 `.mp` 第一分量。 -/
theorem fstNodeHypermapOfList {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {x y : ℕ × ℕ} (hx : x ∈ listOfDarts L)
    (hy : y ∈ (hypermapOfList L hL).node x) : x.1 = y.1 :=
  ((Kepler.Text.TameSpine.memHypermapOfListNode hL hgn hx).mp hy).1

/-- 同上的 dart 集分量（HOL `fst_node_hypermap_of_list` 的第二合取向）。 -/
theorem memDartsOfMemNodeHypermapOfList {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {x y : ℕ × ℕ} (hx : x ∈ listOfDarts L)
    (hy : y ∈ (hypermapOfList L hL).node x) : y ∈ listOfDarts L :=
  ((Kepler.Text.TameSpine.memHypermapOfListNode hL hgn hx).mp hy).2

/-! ## §5 叶 1（实件两枚）：e_list 与 normal 面 -/

/-- **`e_list` 伙伴不在 final 面内**（HOL e_list_on_normal2 证明中的
`SIMPLE_FACE_EDGE_INJ` 支的 Lean 化）：`d ∈ f`、f 是 L 的面、H 受限
⇒ `eList d ∉ f`。

证体：反设 `eList d ∈ f`；`face H d = set f`（`faceOfList` + `findFaceEq`），
故 `y := eList d ∈ face H d`；`y = edge_map H d`（`edgeMap_hypermapOfList`）；
`1 < CARD (node H (face_map H y))`（受限 ⇒ node 非退化，`nodeNondegenerate_two_le`）；
`SIMPLE_FACE_EDGE_INJ`（PackingAuto22:13184）给 `y ≠ edge_map H d`——矛盾。 -/
theorem eListNotMemFaceOfNormal {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    {f : List (ℕ × ℕ)} (hf : f ∈ listOfFaces L) {d : ℕ × ℕ} (hd : d ∈ f) :
    eList d ∉ f := by
  intro helf
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hdH : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  have heD : eList d ∈ listOfDarts L := by
    have h := hL.2.2 d hdD
    simpa [eList] using h
  have heH : eList d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr heD
  -- face H d = set f
  have hfind : findFaceDarts L d = f := (Kepler.Text.TameSpine.findFaceEq hL hdD f).mpr
    ⟨hf, hd⟩
  have hfy : eList d ∈ (hypermapOfList L hL).face d := by
    rw [Kepler.Text.TameCorrCard.faceOfList hL hdD, hfind]
    exact helf
  -- node 非退化：1 < ncard (node (faceMap y))
  have hnode : 1 < ((hypermapOfList L hL).node
      ((hypermapOfList L hL).faceMap (eList d))).ncard := by
    have hfd : (hypermapOfList L hL).faceMap (eList d)
        ∈ (hypermapOfList L hL).darts :=
      (hypermapOfList L hL).faceMap_permutes.apply_mem heH
    have h2 : 2 ≤ ((hypermapOfList L hL).node
        ((hypermapOfList L hL).faceMap (eList d))).ncard :=
      (Kepler.Text.Hypermap.nodeNondegenerate_two_le (hypermapOfList L hL)).mp
        hres.nodeNondegenerate _ hfd
    omega
  have hne := Kepler.Text.SIMPLE_FACE_EDGE_INJ (hypermapOfList L hL) (eList d) d
    hres.simple hnode heH hfy
  apply hne
  show eList d = (hypermapOfList L hL).edgeMap d
  rw [Kepler.Text.TameLp.edgeMap_hypermapOfList L hL hdH]

/-- **e_list 伙伴落在 r 内 ⇒ 是 r 的某 part 的末元**
（HOL e_list_on_normal2 证明的断点支 Lean 化）：
`[f, r]` normal、`d ∈ f`、`eList d ∈ r` ⇒
`eList d ∈ MAP LAST (parts L r)`。

证体：`partsFlatten` 给 `eList d ∈ parts.flatten`，取所在 part `p`
（`List.mem_flatten`）；断点判据 `normalConditionLastParts`
（`¬(nextEl r y = fList L (eList y)) ↔ y = LAST p`）在 `y := eList d` 处：
若 `nextEl r (eList d) = fList L (eList (eList d)) = fList L d`，则
`fList L d ∈ r`（`nextEl_mem_of_mem`）且 `fList L d ∈ f`
（`fList = nextEl (findFace d) d` + `findFaceEq`），撞 `[f,r].flatten` 的
Nodup 面互斥。 -/
theorem eListMemPartsOfMemR {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    {f r : List (ℕ × ℕ)} (hn : NormalListSpine hL [f, r])
    (hf : f ∈ listOfFaces L) {d : ℕ × ℕ} (hd : d ∈ f)
    (hr : eList d ∈ r) :
    eList d ∈ (partsSpine L r).map (fun p => p.getLast!) := by
  have hrn : r ∈ [f, r] := List.mem_cons_of_mem f List.mem_cons_self
  obtain ⟨hrnd, hrne⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hn hrn
  -- eList d ∈ parts.flatten
  have hflat : eList d ∈ (partsSpine L r).flatten := by
    rw [Kepler.Text.TameSpine.partsFlatten L hrnd hrne]
    exact hr
  obtain ⟨p, hp, hep⟩ := List.mem_flatten.mp hflat
  -- 断点：nextEl r (eList d) ≠ fList L d
  have hnot : ¬(nextEl r (eList d) = fList L (eList (eList d))) := by
    rw [Kepler.Text.TameSpine.eList_eList]
    intro heq
    have hnext : fList L d ∈ r := heq ▸ Kepler.Text.TameLp.nextEl_mem_of_mem hr
    have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
    have hfind : findFaceDarts L d = f := (Kepler.Text.TameSpine.findFaceEq hL hdD f).mpr
      ⟨hf, hd⟩
    have hfd : d ∈ findFaceDarts L d := (Kepler.Text.TameLp.dart_in_face L d).mpr hdD
    have hfl : fList L d ∈ findFaceDarts L d := by
      show nextEl (findFaceDarts L d) d ∈ findFaceDarts L d
      exact Kepler.Text.TameLp.nextEl_mem_of_mem hfd
    have hff : fList L d ∈ f := by
      rw [← hfind]
      exact hfl
    -- f 与 r 互斥（flatten [f,r] Nodup ⇒ append 的 Nodup）
    have hn1 : (f ++ r).Nodup := by simpa using hn.1
    have hdisj : ∀ a ∈ f, ∀ b ∈ r, a ≠ b := (List.nodup_append.mp hn1).2.2
    exact hdisj (fList L d) hff (fList L d) hnext rfl
  have hlast : eList d = p.getLast! :=
    (Kepler.Text.TameSpine.normalConditionLastParts L hL hn hres.edgeNondegenerate hrn
      hp hep).mp hnot
  exact List.mem_map.mpr ⟨p, hp, hlast.symm⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.lemmaInNode3
#print axioms Kepler.Text.Reduction1.memFindFaceNonempty
#print axioms Kepler.Text.Reduction1.headMemListOfDarts
#print axioms Kepler.Text.Reduction1.valueLoopMapOfHeadOfAtom
#print axioms Kepler.Text.Reduction1.fstNodeHypermapOfList
#print axioms Kepler.Text.Reduction1.memDartsOfMemNodeHypermapOfList
#print axioms Kepler.Text.Reduction1.eListNotMemFaceOfNormal
#print axioms Kepler.Text.Reduction1.eListMemPartsOfMemR

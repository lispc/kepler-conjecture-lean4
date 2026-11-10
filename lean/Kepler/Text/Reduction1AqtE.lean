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
  · 叶 1 **全形**（三件）——
    `eListNotMemFaceOfNormal`：normal 面 f 内 d 的 e_list 伙伴不在 f
    （simple + node 非退化 + `SIMPLE_FACE_EDGE_INJ`，PackingAuto22:13184 在库件）；
    `eListMemPartsOfMemR`：若 eList d ∈ r，则 eList d 是 r 的某 part 的末元
    （`normalConditionLastParts` 断点判据 + `partsFlatten` + 面互斥）；
    `eListMemFlattenOfNormal`：`eList d ∈ f ∪ r`（`nList (fList d) = eList d` +
    node 闭包，不涉第三面）；三件合一 = `eListOnNormal2`（HOL 逐字）。
  · B 段 `normalListSpineOfIsNormal`：`NormalListSpine hL [f, r]` 五合取组装
    （AUQTZYZ_list.hl:62-215）。
  · §8 主定理收口（C 槽版）`auqtzyzListSlotOfDih2kSlot`：A/B 内置的旧槽形
    （**C 段落定后已被 §12 的直装定理取代**；该槽形的假设过弱、不可填，留作历史形）。
  · §9-§11 C 段：`Dih2kListSpine (quotientListSpine L [f, r])` 实件
    （C1 `core f = f0` / C2 `partsListPairs` / C3 `eListOnNormal2` /
    C4 长度（`listOfDartsQuotient` + `atomListBij` + `dih2k` 首合取）/
    C5 HD-LAST（`exists_mem_node_inter_loop` 原子回译 + `partsFst`）/
    C6 `eListPairsRev` 收口）。
  · §12 **J4 线收官**：`auqtzyzListSlot` —— **`AuqtzyzListSlot` 无条件实例化**
    （`GoodList` + `GoodListNodesTl` + `IsRestricted` ⇒ 槽成立；hAuq 供料链全通）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.TameList63
import Kepler.Text.Reduction1AqtD
import Kepler.Text.Reduction1W4g
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


/-! ## §6 叶 1 合一：覆盖件 + `eListOnNormal2` 全形 -/

/-- **覆盖件**：`[f, r]` normal、`d ∈ f` ⇒ `eList d ∈ f ∨ eList d ∈ r`。
证体（不涉第三面排除）：`x := fList d ∈ f`（face 闭包）；
`nodeMap x = nList x = eList (prevEl (findFace x) x) = eList d`
（`findFace_fList` + `prevEl_nextEl`）；`nodeMap x ∈ node x ⊆ flatten`
（normal_list 第五合取）⇒ `eList d ∈ flatten = f ++ r`。 -/
theorem eListMemFlattenOfNormal {L : fgraph ℕ} (hL : GoodList L)
    {f r : List (ℕ × ℕ)} (hn : NormalListSpine hL [f, r])
    (hf : f ∈ listOfFaces L) {d : ℕ × ℕ} (hd : d ∈ f) :
    eList d ∈ f ∨ eList d ∈ r := by
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hfind : findFaceDarts L d = f :=
    (Kepler.Text.TameSpine.findFaceEq hL hdD f).mpr ⟨hf, hd⟩
  have hfd : d ∈ findFaceDarts L d := (Kepler.Text.TameLp.dart_in_face L d).mpr hdD
  have hfl : fList L d ∈ f := by
    rw [← hfind]
    show nextEl (findFaceDarts L d) d ∈ findFaceDarts L d
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hfd
  have hxflat : fList L d ∈ [f, r].flatten :=
    List.mem_flatten.mpr ⟨f, by simp, hfl⟩
  have hnode_sub := hn.2.2.2.2 (fList L d) hxflat
  have hxD : fList L d ∈ listOfDarts L := memListOfDartsOfMemFace hf hfl
  have hxH : fList L d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hxD
  have hnm : (hypermapOfList L hL).nodeMap (fList L d) = eList d := by
    rw [Kepler.Text.TameLp.nodeMap_hypermapOfList L hL hxH]
    show eList (Kepler.Assembly.prevEl (findFaceDarts L (fList L d)) (fList L d)) = eList d
    rw [Kepler.Text.TameLp.findFace_fList hL.1 hdD]
    exact congrArg eList (Kepler.Text.TameLp.prevEl_nextEl
      (Kepler.Text.TameLp.findFaceDarts_nodup hL.1 d) hfd)
  have hnmem : (hypermapOfList L hL).nodeMap (fList L d)
      ∈ (hypermapOfList L hL).node (fList L d) := by
    have hself : fList L d ∈ (hypermapOfList L hL).node (fList L d) :=
      Kepler.Text.mem_orbitMap_self _ _
    exact Kepler.Text.Hypermap.nodeMap_mem_node_of_mem_node (hypermapOfList L hL) hself
  have hmem : eList d ∈ [f, r].flatten := by
    rw [← hnm]
    exact hnode_sub hnmem
  have happ : eList d ∈ f ++ r := by simpa using hmem
  exact List.mem_append.mp happ

/-- **HOL `e_list_on_normal2`**（tame_list.hl:11496-:11563）全形：
`good_list L ∧ good_list_nodes L ∧ is_restricted ∧ normal_list L [f;r] ∧
MEM f (list_of_faces L) ∧ MEM d f ⇒ MEM (e_list d) (MAP LAST (parts L r))`。
由覆盖件（§6）+ MEM-f 矛盾（`eListNotMemFaceOfNormal`）+ 断点件
（`eListMemPartsOfMemR`）三件合成。 -/
theorem eListOnNormal2 {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    {f r : List (ℕ × ℕ)} (hn : NormalListSpine hL [f, r])
    (hf : f ∈ listOfFaces L) {d : ℕ × ℕ} (hd : d ∈ f) :
    eList d ∈ (partsSpine L r).map (fun p => p.getLast!) := by
  rcases eListMemFlattenOfNormal hL hn hf hd with h | h
  · exact absurd h (eListNotMemFaceOfNormal hL hres hf hd)
  · exact eListMemPartsOfMemR hL hres hn hf hd h

/-! ## §7 批③ B 段：`NormalListSpine hL [f, r]` 组装（AUQTZYZ_list.hl:62-:215） -/

/-- `s ≠ [] ⇒ s.getLast! ∈ s`（`TameSpine.memLastBang` 的本地副本，
该模块不在 TameList63 依赖链）。 -/
private theorem memGetLastBang {α : Type} [Inhabited α] {s : List α} (hne : s ≠ []) :
    s.getLast! ∈ s := by
  induction s with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => exact List.mem_singleton.mpr rfl
    | cons b u =>
      exact List.mem_cons_of_mem _ (ih (List.cons_ne_nil b u))

/-- 两面对 `[f, r]` 的环族集 = `{loopOfListSpine f, loopOfListSpine r}` 的
`{L1, L2}` 形（B/C 段共用）。 -/
theorem loopFamilyPairEq {f r : List (ℕ × ℕ)} {L1 L2 : Loop (ℕ × ℕ)}
    (hL1 : L1 = Kepler.Text.TameSpine.loopOfListSpine f)
    (hL2 : Kepler.Text.TameSpine.loopOfListSpine r = L2) :
    Kepler.Text.TameSpine.loopFamilyOfListSpine [f, r]
      = ({L1, L2} : Set (Loop (ℕ × ℕ))) := by
  ext L'
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases List.mem_cons.mp hs with rfl | hs
    · rw [Set.mem_insert_iff]
      exact Or.inl hL1.symm
    · rw [List.mem_singleton.mp hs, Set.mem_insert_iff]
      exact Or.inr (Set.mem_singleton_iff.mpr hL2)
  · intro hL'
    rcases Set.mem_insert_iff.mp hL' with rfl | hL'
    · exact ⟨f, List.mem_cons_self, hL1⟩
    · rw [Set.mem_singleton_iff.mp hL']
      exact ⟨r, List.mem_cons_of_mem f List.mem_cons_self, hL2.symm⟩

/-- **B 段装配**：`f ∈ listOfFaces L`、`f ≠ []`、AUQTZYZ 结论包 `(L2, hnf, hdih)`
（`L1 = loopOfFace (f.head!)`）⇒ 存在 `r` 使 `NormalListSpine hL [f, r]`。

`r` 取 `L2` 的 loop 表表示（`loopOfListSurj2`，末元 = `headOfAtom NF0 x0`，
使 `fLastSpine L r` 由 `valueLoopMapOfHeadOfAtom`（叶 5）供）。五合取：
① flatten Nodup（f＝findFace 的 Nodup + r.Nodup + 面互斥，互斥用
`dih2kQuotientCardNF` 排 `L1 = L2`）；② nonempty；③ fLast（f：`finalListFace`；
r：叶 5 + `loopMapNextEl` + `faceMap_hypermapOfList`）；④ loopList
（`isNormalLoopList`）；⑤ node 闭包（`isNormalNodal`）。 -/
theorem normalListSpineOfIsNormal {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {f : List (ℕ × ℕ)} (hf : f ∈ listOfFaces L) (hfne : f ≠ [])
    {L2 : Loop (ℕ × ℕ)}
    (hnf : (hypermapOfList L hL).IsNormalFamily
      ({(hypermapOfList L hL).loopOfFace (f.head!), L2} : Set (Loop (ℕ × ℕ))))
    (hdih : Kepler.Text.dih2k_p3
      ((hypermapOfList L hL).quotientHypermap hnf)
      ((hypermapOfList L hL).face (f.head!)).ncard)
    {x0 : ℕ × ℕ} (hx0L2 : x0 ∈ L2.darts)
    (hx0node : x0 ∈ (hypermapOfList L hL).node (f.head!)) :
    ∃ r : List (ℕ × ℕ), NormalListSpine hL [f, r] ∧
      Kepler.Text.TameSpine.loopOfListSpine r = L2 ∧
      r.getLast! = (hypermapOfList L hL).headOfAtom
        ({(hypermapOfList L hL).loopOfFace (f.head!), L2} : Set (Loop (ℕ × ℕ))) x0 := by
  set d := f.head! with hddef
  have hd : d ∈ f := List.head!_mem_self hfne
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hdH : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  have hfind : findFaceDarts L d = f :=
    (Kepler.Text.TameSpine.findFaceEq hL hdD f).mpr ⟨hf, hd⟩
  set L1 := (hypermapOfList L hL).loopOfFace d with hL1def
  have hL1mem : L1 ∈ ({L1, L2} : Set (Loop (ℕ × ℕ))) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hL2mem : L2 ∈ ({L1, L2} : Set (Loop (ℕ × ℕ))) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  -- x0 由调用方供（C 段要求 ∈ node d；§8 由 atom 回译件供）
  have hx0H : x0 ∈ (hypermapOfList L hL).darts :=
    (hypermapOfList L hL).darts_subset_darts_of_isNormalFamily hnf hL2mem
      (Finset.mem_coe.mpr hx0L2)
  set xh := (hypermapOfList L hL).headOfAtom ({L1, L2} : Set (Loop (ℕ × ℕ))) x0 with hxhdef
  have hxhL2 : xh ∈ L2.darts :=
    (hypermapOfList L hL).mem_darts_of_mem_atom hx0L2
      ((hypermapOfList L hL).headOfAtom_mem_atom hnf hL2mem hx0L2).1
  have hxhH : xh ∈ (hypermapOfList L hL).darts :=
    (hypermapOfList L hL).darts_subset_darts_of_isNormalFamily hnf hL2mem
      (Finset.mem_coe.mpr hxhL2)
  -- r 的表表示
  obtain ⟨r, hrLoop, -, hrnd, hrne, hrlast⟩ :=
    Kepler.Text.TameSpine.loopOfListSurj2 hxhL2
  -- f 侧：Nodup / final / fLast
  have hfnod : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 d
  have hfinalF : Kepler.Text.TameSpine.finalListSpine L f :=
    Kepler.Text.TameSpine.finalListFace hL (List.mem_map.mpr ⟨d, hdD, hfind⟩)
  have hL1eq : L1 = Kepler.Text.TameSpine.loopOfListSpine f :=
    Kepler.Text.TameSpine.loopOfFaceList hL hfinalF hfnod hd hdD
  -- L1 ≠ L2（dih2k 排除单元正规族）
  have hk : ((hypermapOfList L hL).face d).ncard ≠ 0 := by
    have h3 := hres.three_le_ncard_face hdH
    omega
  have hNotSing := Kepler.Text.TameSpine.dih2kQuotientCardNF (hypermapOfList L hL) d
    hk hnf hdih
  have hL1neL2 : L1 ≠ L2 := by
    intro heq
    exact hNotSing ⟨L1, by
      ext L'
      simp [heq]⟩
  -- 面互斥
  have hdisj : ∀ x, x ∈ f → x ∈ r → False := by
    intro x hxf hxr
    have hxL1 : x ∈ L1.darts := by
      rw [hL1eq]
      exact (Kepler.Text.TameSpine.inDartLoopOfList hfnod hfne x).mpr hxf
    have hxL2 : x ∈ L2.darts := by
      rw [← hrLoop]
      exact (Kepler.Text.TameSpine.inDartLoopOfList hrnd hrne x).mpr hxr
    exact hL1neL2 (hnf.2.2.1 L1 hL1mem L2 hL2mem x hxL1 hxL2)
  -- ① flatten Nodup
  have hflat : ([f, r]).flatten.Nodup := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact List.nodup_append.mpr ⟨hfnod, hrnd,
      fun a ha b hb heq => hdisj a ha (heq ▸ hb)⟩
  -- ② nonempty
  have hneN : ∀ s ∈ [f, r], s ≠ [] := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hfne
    · rw [List.mem_singleton.mp hs]
      exact hrne
  -- ③ fLast 两支
  have hfLast : Kepler.Text.TameSpine.fLastSpine L f :=
    (hfinalF f.getLast! (memGetLastBang hfne)).symm
  have hrLast : Kepler.Text.TameSpine.fLastSpine L r := by
    show nextEl r r.getLast! = fList L r.getLast!
    rw [hrlast]
    have hnext : nextEl r xh = L2.map xh := by
      rw [← hrLoop]
      exact (Kepler.Text.TameSpine.loopMapNextEl hrnd hrne xh).symm
    rw [hnext]
    rw [Kepler.Text.Reduction1.valueLoopMapOfHeadOfAtom hnf hL2mem hx0L2]
    rw [Kepler.Text.TameLp.faceMap_hypermapOfList L hL hxhH]
  have hlastAll : ∀ s ∈ [f, r], Kepler.Text.TameSpine.fLastSpine L s := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hfLast
    · rw [List.mem_singleton.mp hs]
      exact hrLast
  -- ④⑤ 环族等价 + isNormalLoopList/isNormalNodal
  have hNodupAll : ∀ s ∈ [f, r], s.Nodup := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hfnod
    · rw [List.mem_singleton.mp hs]
      exact hrnd
  have hfamEq : Kepler.Text.TameSpine.loopFamilyOfListSpine [f, r]
      = ({L1, L2} : Set (Loop (ℕ × ℕ))) := loopFamilyPairEq hL1eq hrLoop
  have hnor : (hypermapOfList L hL).IsNormalFamily
      (Kepler.Text.TameSpine.loopFamilyOfListSpine [f, r]) := hfamEq ▸ hnf
  have hloopAll := Kepler.Text.TameSpine.isNormalLoopList hL hgn hres hneN hNodupAll hnor
  have hnodeAll := Kepler.Text.TameSpine.isNormalNodal hL hgn hres hneN hNodupAll hnor
  exact ⟨r, ⟨hflat, hneN, hlastAll, hloopAll, hnodeAll⟩, hrLoop, hrlast⟩

/-- **C5 原子回译**：`dih2k` + `is_normal` ⇒ 存在 `x0 ∈ L2.darts ∩ node d`
（HOL `DIH_IMP_EVERY_NODE_INTER_FACE` 于商 + `lemma_in_node3` 回译）。
商上取 `A ∈ node_Q(atomChoice d) ∩ face_Q(atomChoice x0')`（`dihImpEveryNodeInterFace`）；
`face_Q(atom L2 x0') = atomsOfLoop L2`（`face_quotient_atom`）拆出
`A = atom L2 y`；`atomChoice y = A ∈ node_Q(atomChoice d)`
经 `mem_node_of_atomChoice_mem_node_quotient` 回译为 `y ∈ node d`。 -/
theorem exists_mem_node_inter_loop {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    {f : List (ℕ × ℕ)} (hf : f ∈ listOfFaces L) (hfne : f ≠ [])
    {L2 : Loop (ℕ × ℕ)}
    (hnf : (hypermapOfList L hL).IsNormalFamily
      ({(hypermapOfList L hL).loopOfFace (f.head!), L2} : Set (Loop (ℕ × ℕ))))
    (hdih : Kepler.Text.dih2k_p3
      ((hypermapOfList L hL).quotientHypermap hnf)
      ((hypermapOfList L hL).face (f.head!)).ncard) :
    ∃ x0 : ℕ × ℕ, x0 ∈ L2.darts ∧ x0 ∈ (hypermapOfList L hL).node (f.head!) := by
  classical
  set d := f.head! with hddef
  set NF0 := ({(hypermapOfList L hL).loopOfFace (f.head!), L2} : Set (Loop (ℕ × ℕ))) with hNF0
  set L1 := (hypermapOfList L hL).loopOfFace d with hL1def
  have hd : d ∈ f := List.head!_mem_self hfne
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hdL1 : d ∈ L1.darts := by
    rw [hL1def]
    exact ((hypermapOfList L hL).mem_faceFinset d d).mpr
      ((hypermapOfList L hL).mem_face_self d)
  have hL1mem : L1 ∈ NF0 := by
    rw [hNF0]
    exact Set.mem_insert _ _
  have hL2mem : L2 ∈ NF0 := by
    rw [hNF0]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨-, x0', hx0'H, hx0'L2⟩ := hnf.1 L2 hL2mem
  have hdFam : d ∈ Kepler.Text.Hypermap.dartsOfFamily NF0 := ⟨L1, hL1mem, hdL1⟩
  have hx0'Fam : x0' ∈ Kepler.Text.Hypermap.dartsOfFamily NF0 := ⟨L2, hL2mem, hx0'L2⟩
  -- 商 darts 两个见证
  have hq_d : (hypermapOfList L hL).atomChoice NF0 d
      ∈ ((hypermapOfList L hL).quotientHypermap hnf).darts := by
    rw [mem_darts_quotient (H := hypermapOfList L hL) hnf]
    exact ((hypermapOfList L hL).atomChoice_mem_atomsOfFamily_iff hnf d).mpr hdFam
  have hq_x : (hypermapOfList L hL).atomChoice NF0 x0'
      ∈ ((hypermapOfList L hL).quotientHypermap hnf).darts := by
    rw [mem_darts_quotient (H := hypermapOfList L hL) hnf]
    exact ((hypermapOfList L hL).atomChoice_mem_atomsOfFamily_iff hnf x0').mpr hx0'Fam
  obtain ⟨A, hAnode, hAface⟩ := dihImpEveryNodeInterFace hdih hq_d hq_x
  -- face_Q(atomChoice x0') = atomsOfLoop L2
  have hx0'eq : (hypermapOfList L hL).atomChoice NF0 x0'
      = (hypermapOfList L hL).atom L2 x0' :=
    (hypermapOfList L hL).atomChoice_eq_atom hnf hL2mem hx0'L2
  rw [hx0'eq, Kepler.Text.Hypermap.face_quotient_atom (hypermapOfList L hL) hnf
    hL2mem hx0'L2] at hAface
  obtain ⟨y, hyL2, hAeq⟩ := hAface
  refine ⟨y, hyL2, ?_⟩
  -- y ∈ node d：lemma_in_node3 回译
  refine Kepler.Text.Reduction1.lemmaInNode3 hnf hdFam ?_
  have hyChoice : (hypermapOfList L hL).atomChoice NF0 y = A := by
    rw [(hypermapOfList L hL).atomChoice_eq_atom hnf hL2mem hyL2]
    exact hAeq.symm
  rw [hyChoice]
  exact hAnode


/-! ## §8 主定理收口（C 槽版）：`AuqtzyzListSlot` 装配 -/

/-- **批③ 主定理收口（`Dih2kListSpine` 槽版）**：给定 C 段槽
（任意 normal 面对 `[f,r]` 的 `Dih2kListSpine (quotientListSpine L [f,r])`），
`AuqtzyzListSlot L hL` 无条件实例化——A 段（`eListOnNormal2`）与 B 段
（`normalListSpineOfIsNormal`）已内置；**J4 收官仅剩 C 槽一件**。 -/
theorem auqtzyzListSlotOfDih2kSlot
    (hC : ∀ (L : fgraph ℕ) (hL : GoodList L) (f r : List (ℕ × ℕ)),
      NormalListSpine hL [f, r] → Dih2kListSpine (quotientListSpine L [f, r])) :
    ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted → AuqtzyzListSlot L hL := by
  intro L hL hgn hres f hf
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
  have hlne : l ≠ [] := hL.2.1 l hl
  have hfne : listPairs l ≠ [] := by
    cases l with
    | nil => exact absurd rfl hlne
    | cons a t => simp [listPairs]
  set d := (listPairs l).head! with hddef
  have hd : d ∈ listPairs l := List.head!_mem_self hfne
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hdH : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  -- AUQTZYZ 主定理无条件形（AqtD）
  obtain ⟨L2, hnf, -, hdih⟩ :=
    auqtzyzConclUncond (hypermapOfList L hL) d ((hypermapOfList L hL).loopOfFace d)
      hres hdH rfl
  -- C5 原子回译：取 x0 ∈ L2.darts ∩ node d
  obtain ⟨x0, hx0L2, hx0node⟩ := exists_mem_node_inter_loop hL hres hf hfne hnf hdih
  -- B 段：normal_list 组装
  obtain ⟨r, hnorm, -, -⟩ :=
    normalListSpineOfIsNormal hL hgn hres hf hfne (L2 := L2) hnf hdih hx0L2 hx0node
  exact ⟨r, hnorm, hC L hL (listPairs l) r hnorm⟩

/-! ## §9 C 段地基：List 小件（`head!`/`getLast!` 沿 map / flatten） -/

private theorem headBangMap {α β : Type} [Inhabited α] [Inhabited β] {l : List α}
    (h : l ≠ []) (f : α → β) : (l.map f).head! = f l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

private theorem getLastBangMap {α β : Type} [Inhabited α] [Inhabited β] {l : List α}
    (h : l ≠ []) (f : α → β) : (l.map f).getLast! = f l.getLast! := by
  induction l with
  | nil => exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u =>
      simpa using ih (List.cons_ne_nil b u)

private theorem getLast?_flatten_of_all_ne {α : Type} {L : List (List α)}
    (h : L ≠ []) (hne : ∀ l ∈ L, l ≠ []) :
    L.flatten.getLast? = (L.getLast!).getLast? := by
  induction L with
  | nil => exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b u =>
      have htne : (b :: u) ≠ [] := List.cons_ne_nil b u
      have hbne : b ≠ [] := hne b (by simp)
      have htall : ∀ l ∈ (b :: u), l ≠ [] :=
        fun l hl => hne l (List.mem_cons_of_mem a hl)
      have hflatne : (b :: u).flatten ≠ [] := by
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b hbne
        intro hnil
        have hxm : x ∈ (b :: u).flatten :=
          List.mem_flatten.mpr ⟨b, List.mem_cons_self, hx⟩
        rw [hnil] at hxm
        exact List.not_mem_nil hxm
      rw [List.flatten_cons, List.getLast?_append,
        List.getLast?_eq_some_getLast hflatne]
      have hgl : (a :: b :: u).getLast! = (b :: u).getLast! := rfl
      have hor : (some ((b :: u).flatten.getLast hflatne)).or a.getLast?
          = some ((b :: u).flatten.getLast hflatne) := rfl
      rw [hgl, hor, ← List.getLast?_eq_some_getLast hflatne]
      exact ih htne htall

private theorem getLastBangFlatten_of_all_ne {α : Type} [Inhabited α]
    {L : List (List α)} (h : L ≠ []) (hne : ∀ l ∈ L, l ≠ []) :
    L.flatten.getLast! = (L.getLast!).getLast! :=
  calc L.flatten.getLast! = L.flatten.getLast?.getD default :=
        List.getLast!_eq_getLast?_getD
    _ = (L.getLast!).getLast?.getD default := by
        rw [getLast?_flatten_of_all_ne h hne]
    _ = (L.getLast!).getLast! := (List.getLast!_eq_getLast?_getD).symm

/-! ## §10 C 段 C1-C3：core 面 = f0 / listPairs 桥 / e_list 全体对称 -/

/-- **C1**：final 面 f 的 `parts` 头表 = `f0`（`goodFaceRep` 证人；
`finalListParts` 展开后 `[x].head!.1 = x.1`）。 -/
theorem partsHeadEqOfFinal {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    {f : List (ℕ × ℕ)} (hD : ∀ x ∈ f, x ∈ listOfDarts L)
    (hfin : Kepler.Text.TameSpine.finalListSpine L f) (hfnod : f.Nodup)
    {f0 : List ℕ} (hfst : f.map Prod.fst = f0) :
    (Kepler.Text.TameSpine.partsSpine L f).map (fun p => p.head!.1) = f0 := by
  rw [Kepler.Text.TameSpine.finalListParts L hL f hD hres.edgeNondegenerate hfin hfnod]
  have hcongr : (f.map (fun x => [x])).map (fun p => p.head!.1) = f.map Prod.fst := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => rfl
  rw [hcongr, hfst]

/-- **C2**：`listPairs (parts 头表) = parts 末元表`（`partsListPairs` 直投）。 -/
theorem listPairsPartsHeadEq {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) :
    listPairs ((Kepler.Text.TameSpine.partsSpine L r).map (fun p => p.head!.1))
      = (Kepler.Text.TameSpine.partsSpine L r).map (fun p => p.getLast!) :=
  Kepler.Text.TameSpine.partsListPairs L hL hn hres.edgeNondegenerate
    ((Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hres.simple) hr

/-- **C3**：normal 面 f 的每个 dart 的 e_list 伙伴都在 `parts r` 的末元表内
（`eListOnNormal2` 逐点）。 -/
theorem eListMemPartsOfNormalAll {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    {f r : List (ℕ × ℕ)} (hn : NormalListSpine hL [f, r])
    (hf : f ∈ listOfFaces L) :
    ∀ d ∈ f, eList d ∈ (Kepler.Text.TameSpine.partsSpine L r).map
      (fun p => p.getLast!) :=
  fun d hd => eListOnNormal2 hL hres hn hf hd

/-! ## §11 C 段：`Dih2kListSpine (quotientListSpine L [f, r])`（AUQTZYZ_list :216-:325） -/

/-- **C 段主件**：normal 面对 `[f, r]` + AUQTZYZ 结论包（`L2`, `hnf`, `hdih`，
`x0 ∈ L2.darts ∩ node d`，`r` 的末元 = `headOfAtom x0`）⇒
`Dih2kListSpine (quotientListSpine L [f, r])`。

证人 `u = f0`（`goodFaceRep`）。C1 `core f = f0`（`finalListParts`）；
C2 `listPairs (core r) = parts r 末元表`（`partsListPairs`）；C3 e_list 对称
（`eListOnNormal2`）；C4 长度相等（`listOfDartsQuotient` + `atomListBij` +
`dih2k` 首合取 + `cardFaceOfList`）；C5 HD-LAST（`partsFst` + 末 part 末元 +
`fstNodeHypermapOfList`）；C6 `eListPairsRev` 收口。 -/
theorem dih2kListSpineOfNormal {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {f r : List (ℕ × ℕ)} (hn : NormalListSpine hL [f, r])
    (hf : f ∈ listOfFaces L) (hfne : f ≠ [])
    {L2 : Loop (ℕ × ℕ)}
    (hnf : (hypermapOfList L hL).IsNormalFamily
      ({(hypermapOfList L hL).loopOfFace (f.head!), L2} : Set (Loop (ℕ × ℕ))))
    (hdih : Kepler.Text.dih2k_p3
      ((hypermapOfList L hL).quotientHypermap hnf)
      ((hypermapOfList L hL).face (f.head!)).ncard)
    (hrLoop : Kepler.Text.TameSpine.loopOfListSpine r = L2)
    {x0 : ℕ × ℕ} (hx0L2 : x0 ∈ L2.darts)
    (hx0node : x0 ∈ (hypermapOfList L hL).node (f.head!))
    (hrlast : r.getLast! = (hypermapOfList L hL).headOfAtom
      ({(hypermapOfList L hL).loopOfFace (f.head!), L2} : Set (Loop (ℕ × ℕ))) x0) :
    Kepler.Text.TameSpine.Dih2kListSpine
      (Kepler.Text.TameSpine.quotientListSpine L [f, r]) := by
  classical
  set d := f.head! with hddef
  have hd : d ∈ f := List.head!_mem_self hfne
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hdH : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  have hfind : findFaceDarts L d = f :=
    (Kepler.Text.TameSpine.findFaceEq hL hdD f).mpr ⟨hf, hd⟩
  have hfnod : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 d
  have hfinalF : Kepler.Text.TameSpine.finalListSpine L f :=
    Kepler.Text.TameSpine.finalListFace hL (List.mem_map.mpr ⟨d, hdD, hfind⟩)
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hres.simple
  obtain ⟨f0, hpair, -, hfst, hf0nod, hf0ne⟩ :=
    Kepler.Text.TameSpine.goodFaceRep L f hL hgn hres.simple hf
  set A := (Kepler.Text.TameSpine.partsSpine L f).map (fun p => p.head!.1) with hAdef
  set B := (Kepler.Text.TameSpine.partsSpine L r).map (fun p => p.head!.1) with hBdef
  have hrn : r ∈ [f, r] := List.mem_cons_of_mem f List.mem_cons_self
  obtain ⟨hrnd, hrne⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hn hrn
  -- C1
  have hA : A = f0 := partsHeadEqOfFinal hL hres
    (fun x hx => memListOfDartsOfMemFace hf hx) hfinalF hfnod hfst
  -- C2
  have hBpair : listPairs B = (Kepler.Text.TameSpine.partsSpine L r).map
      (fun p => p.getLast!) := listPairsPartsHeadEq hL hgn hres hn hrn
  -- C4：长度相等
  have hkface : ((hypermapOfList L hL).face d).ncard = f.length := by
    rw [Kepler.Text.TameCorrCard.cardFaceOfList hL hdD, hfind]
  have hquot2 : ((hypermapOfList L hL).quotientHypermap hnf).darts.card
      = 2 * ((hypermapOfList L hL).face d).ncard := hdih.1
  have hL1eq : (hypermapOfList L hL).loopOfFace d
      = Kepler.Text.TameSpine.loopOfListSpine f :=
    Kepler.Text.TameSpine.loopOfFaceList hL hfinalF hfnod hd hdD
  have hbij := Kepler.Text.TameSpine.atomListBij L hL hn hres.edgeNondegenerate hunL
  rw [loopFamilyPairEq hL1eq hrLoop] at hbij
  have hsrc : ({z : ℕ × ℕ | z ∈ listOfDarts
        (Kepler.Text.TameSpine.quotientListSpine L [f, r])} : Set (ℕ × ℕ)).ncard
      = (listOfDarts (Kepler.Text.TameSpine.quotientListSpine L [f, r])).length := by
    have hset : {z : ℕ × ℕ | z ∈ listOfDarts
          (Kepler.Text.TameSpine.quotientListSpine L [f, r])}
        = ((listOfDarts (Kepler.Text.TameSpine.quotientListSpine L [f, r])).toFinset
            : Set (ℕ × ℕ)) := by
      ext z
      simp
    rw [hset, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup
        (Kepler.Text.TameSpine.goodListQuotient L hL hn hres.edgeNondegenerate hunL).1]
  have htgt : ((hypermapOfList L hL).atomsOfFamily
        ({(hypermapOfList L hL).loopOfFace d, L2} : Set (Loop (ℕ × ℕ)))).ncard
      = ((hypermapOfList L hL).quotientHypermap hnf).darts.card := by
    have hset : ((hypermapOfList L hL).atomsOfFamily
          ({(hypermapOfList L hL).loopOfFace d, L2} : Set (Loop (ℕ × ℕ)))
          : Set (Set (ℕ × ℕ)))
        = ↑((hypermapOfList L hL).quotientHypermap hnf).darts := by
      ext a
      exact (mem_darts_quotient (H := hypermapOfList L hL) hnf (a := a)).symm
    rw [hset, Set.ncard_coe_finset]
  have hcardEq : (listOfDarts (Kepler.Text.TameSpine.quotientListSpine L [f, r])).length
      = ((hypermapOfList L hL).quotientHypermap hnf).darts.card := by
    have h1 : ({z : ℕ × ℕ | z ∈ listOfDarts
          (Kepler.Text.TameSpine.quotientListSpine L [f, r])} : Set (ℕ × ℕ)).ncard
        = ((hypermapOfList L hL).atomsOfFamily
          ({(hypermapOfList L hL).loopOfFace d, L2} : Set (Loop (ℕ × ℕ)))).ncard := by
      rw [← Set.InjOn.ncard_image hbij.2.1, Set.BijOn.image_eq hbij]
    rw [← hsrc, h1, htgt]
  have hlistLen : (listOfDarts (Kepler.Text.TameSpine.quotientListSpine L [f, r])).length
      = f.length + B.length := by
    rw [Kepler.Text.TameSpine.listOfDartsQuotient L hL hn hres.edgeNondegenerate hunL]
    have hflat : (List.map (Kepler.Text.TameSpine.partsSpine L) [f, r]).flatten
        = Kepler.Text.TameSpine.partsSpine L f
            ++ Kepler.Text.TameSpine.partsSpine L r := by
      simp
    rw [hflat, List.map_append, List.length_append, List.length_map, List.length_map]
    have hpf : (Kepler.Text.TameSpine.partsSpine L f).length = f.length := by
      rw [Kepler.Text.TameSpine.finalListParts L hL f
        (fun x hx => memListOfDartsOfMemFace hf hx) hres.edgeNondegenerate hfinalF hfnod]
      simp
    have hpr : (Kepler.Text.TameSpine.partsSpine L r).length = B.length := by
      show (Kepler.Text.TameSpine.partsSpine L r).length
        = ((Kepler.Text.TameSpine.partsSpine L r).map (fun p => p.head!.1)).length
      rw [List.length_map]
    rw [hpf, hpr]
  have hBlen : B.length = f0.length := by
    have h2 : f.length + B.length = 2 * f.length := by
      rw [← hlistLen, hcardEq, hquot2, hkface]
    have h3 : B.length = f.length := by omega
    rw [h3, ← hfst, List.length_map]
  -- C5：HD-LAST
  have hL2mem : L2 ∈ ({(hypermapOfList L hL).loopOfFace d, L2}
      : Set (Loop (ℕ × ℕ))) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hpartsne : (Kepler.Text.TameSpine.partsSpine L r) ≠ [] :=
    Kepler.Text.TameSpine.partsNonnil L hrnd hrne
  have hpartsall : ∀ l ∈ Kepler.Text.TameSpine.partsSpine L r, l ≠ [] :=
    fun l hl => Kepler.Text.TameSpine.partsAllNonnil L hrnd hrne l hl
  have hxhnode : r.getLast! ∈ (hypermapOfList L hL).node d := by
    rw [hrlast]
    have h1 : (hypermapOfList L hL).headOfAtom
        ({(hypermapOfList L hL).loopOfFace d, L2} : Set (Loop (ℕ × ℕ))) x0
        ∈ (hypermapOfList L hL).atom L2 x0 :=
      ((hypermapOfList L hL).headOfAtom_mem_atom hnf hL2mem hx0L2).1
    have h2 : (hypermapOfList L hL).headOfAtom
        ({(hypermapOfList L hL).loopOfFace d, L2} : Set (Loop (ℕ × ℕ))) x0
        ∈ (hypermapOfList L hL).node x0 :=
      (hypermapOfList L hL).atom_subset_node L2 x0 h1
    have h3 : (hypermapOfList L hL).node d = (hypermapOfList L hL).node x0 :=
      Kepler.Text.Hypermap.node_eq_of_mem (hypermapOfList L hL) hx0node
    rw [h3]
    exact h2
  have hfst_eq : d.1 = (r.getLast!).1 :=
    fstNodeHypermapOfList hL hgn hdD hxhnode
  have hrlastmem : r.getLast! ∈ (Kepler.Text.TameSpine.partsSpine L r).getLast! := by
    have hflatr : (Kepler.Text.TameSpine.partsSpine L r).flatten = r :=
      Kepler.Text.TameSpine.partsFlatten L hrnd hrne
    have hflatr' : r.getLast!
        = (Kepler.Text.TameSpine.partsSpine L r).flatten.getLast! :=
      congrArg (fun s => s.getLast!) hflatr.symm
    have h1 : r.getLast! = ((Kepler.Text.TameSpine.partsSpine L r).getLast!).getLast! := by
      rw [hflatr']
      exact getLastBangFlatten_of_all_ne
        (L := Kepler.Text.TameSpine.partsSpine L r) hpartsne hpartsall
    rw [h1]
    exact memGetLastBang (hpartsall _ (memGetLastBang hpartsne))
  have hplast : r.getLast!.1
      = (Kepler.Text.TameSpine.partsSpine L r).getLast!.head!.1 :=
    Kepler.Text.TameSpine.partsFst L hL hn hrn (memGetLastBang hpartsne) hrlastmem
  have hBget : B.getLast!
      = (Kepler.Text.TameSpine.partsSpine L r).getLast!.head!.1 := by
    show ((Kepler.Text.TameSpine.partsSpine L r).map (fun p => p.head!.1)).getLast! = _
    rw [getLastBangMap hpartsne (fun p => p.head!.1)]
  have hf0head : f0.head! = d.1 := by
    rw [← hfst]
    exact headBangMap hfne Prod.fst
  have hhd : f0.head! = B.getLast! := by
    rw [hf0head, hBget, ← hplast, hfst_eq]
  -- C3 + C6：eListPairsRev
  have hlist : ∀ x ∈ listPairs f0, eList x ∈ listPairs B := by
    intro x hx
    rw [hpair] at hx
    rw [hBpair]
    exact eListOnNormal2 hL hres hn hf hx
  have hrev : B = f0.reverse :=
    Kepler.Text.TameSpine.eListPairsRev hf0nod hf0ne hBlen.symm hlist hhd
  refine ⟨f0, hf0nod, ?_⟩
  show Kepler.Text.TameSpine.quotientListSpine L [f, r] = [f0, f0.reverse]
  have hq : Kepler.Text.TameSpine.quotientListSpine L [f, r] = [A, B] := rfl
  rw [hq, hA, hrev]

/-! ## §12 J4 线收官：`AuqtzyzListSlot` 无条件实例化 -/

/-- **批③ 主定理（无条件形）**：`GoodList L` + `GoodListNodesTl` + `IsRestricted`
⇒ **`AuqtzyzListSlot L hL`**（`hAuq` 供料链的最后一环）。
`f` 取 `listPairs l`、`d = f.head!`、AUQTZYZ 无条件主定理给 `(L2, hnf, hdih)`；
C5 原子回译取 `x0 ∈ L2.darts ∩ node d`；B 段组装 `NormalListSpine hL [f, r]`；
C 段给 `Dih2kListSpine (quotientListSpine L [f, r])`。 -/
theorem auqtzyzListSlot : ∀ (L : fgraph ℕ) (hL : GoodList L),
    GoodListNodesTl L hL → (hypermapOfList L hL).IsRestricted → AuqtzyzListSlot L hL := by
  intro L hL hgn hres f hf
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
  have hlne : l ≠ [] := hL.2.1 l hl
  have hfne : listPairs l ≠ [] := by
    cases l with
    | nil => exact absurd rfl hlne
    | cons a t => simp [listPairs]
  set d := (listPairs l).head! with hddef
  have hd : d ∈ listPairs l := List.head!_mem_self hfne
  have hdD : d ∈ listOfDarts L := memListOfDartsOfMemFace hf hd
  have hdH : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  obtain ⟨L2, hnf, -, hdih⟩ :=
    auqtzyzConclUncond (hypermapOfList L hL) d ((hypermapOfList L hL).loopOfFace d)
      hres hdH rfl
  obtain ⟨x0, hx0L2, hx0node⟩ :=
    exists_mem_node_inter_loop hL hres hf hfne hnf hdih
  obtain ⟨r, hnorm, hrLoop, hrlast⟩ :=
    normalListSpineOfIsNormal hL hgn hres hf hfne (L2 := L2) hnf hdih hx0L2 hx0node
  exact ⟨r, hnorm,
    dih2kListSpineOfNormal hL hgn hres hnorm hf hfne hnf hdih hrLoop hx0L2 hx0node hrlast⟩

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
#print axioms Kepler.Text.Reduction1.eListMemFlattenOfNormal
#print axioms Kepler.Text.Reduction1.eListOnNormal2
#print axioms Kepler.Text.Reduction1.normalListSpineOfIsNormal
#print axioms Kepler.Text.Reduction1.auqtzyzListSlotOfDih2kSlot
#print axioms Kepler.Text.Reduction1.partsHeadEqOfFinal
#print axioms Kepler.Text.Reduction1.listPairsPartsHeadEq
#print axioms Kepler.Text.Reduction1.eListMemPartsOfNormalAll
#print axioms Kepler.Text.Reduction1.loopFamilyPairEq
#print axioms Kepler.Text.Reduction1.exists_mem_node_inter_loop
#print axioms Kepler.Text.Reduction1.dih2kListSpineOfNormal
#print axioms Kepler.Text.Reduction1.auqtzyzListSlot

/-
  Kepler.Text.Reduction1W2g — J4 Wave W2 收官段（W2-2 簇第 7-8 件 + 基座）：

  · `memFindFaceImpMemDarts`（HOL `List_hypermap.mem_find_face_imp_mem_darts`，
    list_hypermap-compiled.hl:438：`MEM d (find_face L y) ⇒ MEM d (list_of_darts L)`）
  · `listPairsMemTwo` / `listPairsMap`（`list_pairs` 的逐元/`map` 运输基座）
  · `findFaceMap`（HOL tame_list.hl:3450：`good_list ∧ inj_on phi (elements_of_list) ∧
    MEM (p1,p2) (list_of_darts) ⇒ find_face (MAP (MAP phi) x) (phi p1, phi p2) =
    MAP (\d. phi (FST d), phi (SND d)) (find_face x (p1,p2))`）
  · `mapNewvertex`（HOL reduction1.hl:1998，W2-2 验收点）
  · `findFaceDartMemFlatten`（`oldnew_vertex_disjoint` 证体的 node-子集内半件：
    同 FST ⇒ 同 node ⇒ 入 `flatten N`）
  · `oldnewVertexDisjointOfObdatyb`（HOL reduction1.hl:1803 的槽版：OBDATYB 槽显式；
    无条件形待 OBDATYB 本体落库后一行收口，见 DELIVERY 勘误）

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2e
import Kepler.Text.TameLp
import Kepler.Text.ChainListsL1
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.PackingAuto2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs findFaceDarts)
open Kepler.Text.ChainLists (normalList markedList)
open Kepler.Text.Reduction3 (newvertex)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face elementsOfList)
open Kepler.Text.TameSpine (rotateTo)

/-! ## §0 `find_face` 元即 dart、`list_pairs` 逐元/`map` 运输 -/

/-- **HOL `List_hypermap.mem_find_face_imp_mem_darts`**（list_hypermap-compiled.hl:438）：
`MEM d (find_face L y) ⇒ MEM d (list_of_darts L)`。 -/
theorem memFindFaceImpMemDarts {L : Kepler.Graphs.fgraph ℕ} {d y : ℕ × ℕ}
    (hd : d ∈ findFaceDarts L y) : d ∈ listOfDarts L := by
  by_cases hval : L.find? (fun l => decide (y ∈ listPairs l)) = none
  · rw [Kepler.Text.TameLp.findFaceDarts_none hval] at hd
    exact absurd hd (by simp)
  · obtain ⟨f, hf⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : findFaceDarts L y = listPairs f := by
      simp only [findFaceDarts, ← hf, Option.getD_some]
    rw [hfeq] at hd
    exact List.mem_flatten.mpr ⟨listPairs f,
      List.mem_map.mpr ⟨f, List.mem_of_find?_eq_some hf.symm, rfl⟩, hd⟩

/-- `list_pairs` 的对元的两分量都在面表中。 -/
theorem listPairsMemTwo {l : List ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listPairs l) : d.1 ∈ l ∧ d.2 ∈ l := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  rw [listPairsEqZip, List.getElem?_zipWith_eq_some] at hi
  obtain ⟨a, b, ha, hb, hab⟩ := hi
  subst hab
  exact ⟨List.mem_of_getElem? ha, List.mem_rotate.mp (List.mem_of_getElem? hb)⟩

/-- **`list_pairs` 的 `map` 运输**：`list_pairs (MAP phi l) =
MAP (\d. phi (FST d), phi (SND d)) (list_pairs l)`。 -/
theorem listPairsMap {l : List ℕ} {phi : ℕ → ℕ} :
    listPairs (l.map phi) = (listPairs l).map (fun d => (phi d.1, phi d.2)) := by
  unfold Kepler.Assembly.listPairs
  rw [← List.map_drop, ← List.map_take, ← List.map_append, List.zip_map]
  rfl

/-! ## §1 `find_face_map`（HOL tame_list.hl:3450） -/

/-- 面元在元素表中（`elements_of_list` 载体换装）。 -/
private theorem memElementsOfMemFace {L : Kepler.Graphs.fgraph ℕ} {g : List ℕ} {a : ℕ}
    (hg : g ∈ L) (ha : a ∈ g) : a ∈ elementsOfList L :=
  Set.mem_setOf.mpr (List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨g, hg, ha⟩))

/-- **HOL `find_face_map`**：`good_list x ∧ inj_on phi (elements_of_list x) ∧
MEM (p1,p2) (list_of_darts x) ⇒ find_face (MAP (MAP phi) x) (phi p1, phi p2) =
MAP (\d. phi (FST d), phi (SND d)) (find_face x (p1,p2))`。 -/
theorem findFaceMap {L : Kepler.Graphs.fgraph ℕ} {d1 d2 : ℕ} {phi : ℕ → ℕ}
    (hgood : GoodList L)
    (hinj : Set.InjOn phi (elementsOfList L))
    (hd : (d1, d2) ∈ listOfDarts L) :
    findFaceDarts (L.map (fun f => f.map phi)) (phi d1, phi d2) =
      (findFaceDarts L (d1, d2)).map (fun d => (phi d.1, phi d.2)) := by
  have hdE : d1 ∈ elementsOfList L ∧ d2 ∈ elementsOfList L := by
    obtain ⟨f, hf, htf⟩ := List.mem_flatten.mp hd
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    obtain ⟨he1, he2⟩ := listPairsMemTwo htf
    exact ⟨memElementsOfMemFace hg he1, memElementsOfMemFace hg he2⟩
  have hPtransport : ∀ g ∈ L,
      ((fun l => decide ((phi d1, phi d2) ∈ listPairs l)) ∘ fun f : List ℕ => f.map phi) g =
        (fun l => decide ((d1, d2) ∈ listPairs l)) g := by
    intro g hg
    show decide ((phi d1, phi d2) ∈ listPairs (g.map phi)) =
      decide ((d1, d2) ∈ listPairs g)
    rw [listPairsMap]
    apply decide_eq_decide.mpr
    constructor
    · intro hmem
      obtain ⟨t, ht, hEq⟩ := List.mem_map.mp hmem
      obtain ⟨he1, he2⟩ := listPairsMemTwo ht
      have hc1 : t.1 = d1 := hinj (memElementsOfMemFace hg he1) hdE.1
        (congrArg Prod.fst hEq)
      have hc2 : t.2 = d2 := hinj (memElementsOfMemFace hg he2) hdE.2
        (congrArg Prod.snd hEq)
      have htEq : t = (d1, d2) := Prod.ext hc1 hc2
      rw [htEq] at ht
      exact ht
    · intro h2
      exact List.mem_map.mpr ⟨(d1, d2), h2, rfl⟩
  unfold findFaceDarts
  rw [List.find?_map, List.find?_congr hPtransport]
  cases hfind : L.find? (fun l => decide ((d1, d2) ∈ listPairs l)) with
  | none => simp [Kepler.Assembly.listPairs]
  | some f =>
    simp only [Option.map_some, Option.getD_some]
    exact listPairsMap

/-! ## §2 `map_newvertex`（HOL reduction1.hl:1998，W2-2 验收点） -/

/-- filter 的 `map` 运输（`pm d ∉ r.map pm ↔ d ∉ r`：⇐ 向平凡，⇒ 向用 `pm`
在 `S` 上的单射；HOL `Seq.eq_in_filter` 槽）。 -/
private theorem filterMapNotMem {l r : List (ℕ × ℕ)} {pm : ℕ × ℕ → ℕ × ℕ}
    {S : Set (ℕ × ℕ)}
    (hpmInj : Set.InjOn pm S) (hl : ∀ d ∈ l, d ∈ S) (hr : ∀ e ∈ r, e ∈ S) :
    (l.map pm).filter (fun a => decide (a ∉ r.map pm)) =
      (l.filter (fun d => decide (d ∉ r))).map pm := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun d hd => decide_eq_decide.mpr ?_
  constructor
  · intro hcon hdr
    exact hcon (List.mem_map.mpr ⟨d, hdr, rfl⟩)
  · intro hcon hmem
    obtain ⟨e, he, hEq⟩ := List.mem_map.mp hmem
    have hde : e = d := hpmInj (hr e he) (hl d hd) hEq
    exact hcon (hde ▸ he)

/-- **HOL `map_newvertex`**（reduction1.hl:1998，W2-2 验收点）：
`good_list L ∧ MEM x (list_of_darts L) ∧ set_of_list r SUBSET darts_of_list L ∧
inj_on phi (elements_of_list L) ⇒ newvertex (MAP (MAP phi) L)
(MAP (\x. phi (FST x), phi (SND x)) r) (phi (FST x), phi (SND x)) =
MAP phi (newvertex L r x)`
（`set_of_list r SUBSET darts_of_list L` 取展开形 `∀ e ∈ r, e ∈ listOfDarts L`）。 -/
theorem mapNewvertex {L : Kepler.Graphs.fgraph ℕ}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} {phi : ℕ → ℕ}
    (hgood : GoodList L) (hx : x ∈ listOfDarts L)
    (hsub : ∀ e ∈ r, e ∈ listOfDarts L)
    (hinj : Set.InjOn phi (elementsOfList L)) :
    newvertex (L.map (fun f => f.map phi))
      (r.map (fun d => (phi d.1, phi d.2))) (phi x.1, phi x.2) =
      (newvertex L r x).map phi := by
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hgood.1 x
  have hvx : x ∈ findFaceDarts L x := dart_in_face L x |>.mpr hx
  -- 1. find_face 槽（findFaceMap，`x = (x.1, x.2)`）
  have hFF : findFaceDarts (L.map (fun f => f.map phi)) (phi x.1, phi x.2) =
      (findFaceDarts L x).map (fun d => (phi d.1, phi d.2)) :=
    findFaceMap hgood hinj hx
  -- 2. rotate 槽的 InjOn：find_face ⊆ listOfDarts 上 pairPhi 单射
  have hInjD := Kepler.Text.TameSpine.injOnDartOfList L hinj
  have hInjRot : Set.InjOn (fun d : ℕ × ℕ => (phi d.1, phi d.2))
      (Kepler.Text.setOfList (findFaceDarts L x)) :=
    hInjD.mono (fun s hs => memFindFaceImpMemDarts hs)
  -- 3. rotate 槽（W2e.rotateToMap）
  have hRot : rotateTo ((findFaceDarts L x).map (fun d => (phi d.1, phi d.2)))
      (phi x.1, phi x.2) =
      (rotateTo (findFaceDarts L x) x).map (fun d => (phi d.1, phi d.2)) :=
    rotateToMap hnd hvx hInjRot
  -- 4. filter 槽（filterMapNotMem）
  have hFilt : ((rotateTo (findFaceDarts L x) x).map
        (fun d => (phi d.1, phi d.2))).filter
        (fun a => decide (a ∉ r.map (fun d => (phi d.1, phi d.2)))) =
      ((rotateTo (findFaceDarts L x) x).filter
        (fun d => decide (d ∉ r))).map (fun d => (phi d.1, phi d.2)) :=
    filterMapNotMem hInjD
      (fun d hd => memFindFaceImpMemDarts ((memRotateTo2 hvx hnd).mpr hd)) hsub
  -- 总装：两半 newvertex 定义性展开（`Reduction3.rotateTo` 与 `TameSpine.rotateTo`
  -- 按 `rotateToBridge` 同值）+ map/filter 链
  show List.map (fun d : ℕ × ℕ => d.1)
      (List.filter (fun d => decide (d ∉ r.map (fun d => (phi d.1, phi d.2))))
        (rotateTo (findFaceDarts (L.map (fun f => f.map phi)) (phi x.1, phi x.2))
          (phi x.1, phi x.2))) =
    List.map phi
      (List.map (fun d : ℕ × ℕ => d.1)
        (List.filter (fun d => decide (d ∉ r))
          (rotateTo (findFaceDarts L x) x)))
  rw [hFF, hRot, hFilt, List.map_map, List.map_map]
  rfl

/-! ## §3 `oldnew_vertex_disjoint` 的 node-内半件 + 槽版 -/

/-- **oldnew_vertex_disjoint 内半件**（HOL 证体 node-子集四段：
`MEM_hypermap_of_list_node` + `normal_list` 第 5 合取）：与 `flatten N` 某 dart
同 FST 的 `list_of_darts` 元落入 `flatten N`。 -/
theorem findFaceDartMemFlatten {L : Kepler.Graphs.fgraph ℕ}
    {N : List (List (ℕ × ℕ))} {s w : ℕ × ℕ}
    (hgood : GoodList L) (hgn : GoodListNodesTl L hgood)
    (hnl : normalList L hgood N)
    (hw : w ∈ N.flatten) (hsD : s ∈ listOfDarts L) (hFST : s.1 = w.1) :
    s ∈ N.flatten := by
  have hwD : w ∈ listOfDarts L := by
    obtain ⟨face, hface, hwf⟩ := List.mem_flatten.mp hw
    exact (hnl.2.2.2.1 face hface w hwf).1
  have hwH : w ∈ (Kepler.Text.TameLp.hypermapOfList L hgood).darts := by
    have h2 : w ∈ ((Kepler.Text.TameLp.hypermapOfList L hgood).darts : Set (ℕ × ℕ)) := by
      rw [Kepler.Text.TameLp.darts_hypermapOfList]
      exact hwD
    exact Finset.mem_coe.mp h2
  have hnodeW : (Kepler.Text.TameLp.hypermapOfList L hgood).node w ∈
      (Kepler.Text.TameLp.hypermapOfList L hgood).nodeSet :=
    ⟨w, hwH, rfl⟩
  have hEq : (Kepler.Text.TameLp.hypermapOfList L hgood).nodeSet =
      Kepler.Text.TameLp.nodesOfListSet L := hgn
  rw [hEq, Kepler.Text.TameLp.nodesOfListSet] at hnodeW
  obtain ⟨x0, _, hx0Eq⟩ := hnodeW
  have hwself := Kepler.Text.Hypermap.mem_node_self
    (Kepler.Text.TameLp.hypermapOfList L hgood) w
  rw [← hx0Eq] at hwself
  have hwx0 : w.1 = x0 := hwself.2
  have hsNode : s ∈ (Kepler.Text.TameLp.hypermapOfList L hgood).node w := by
    rw [← hx0Eq]
    exact ⟨hsD, hFST.trans hwx0⟩
  exact hnl.2.2.2.2 w hw hsNode

/-- **HOL `oldnew_vertex_disjoint`**（reduction1.hl:1803）槽版：OBDATYB 槽
（`hOb`）显式携带；无条件形待 OBDATYB 本体落库后一行收口。
（HOL 前提 `transform_assumption_v2 L` 在其证明体内零消费，本形省略。）
`marked_list` 槽给 `x ∈ listOfDarts L`（`markedListOfDart`）与
`normal_list`（第 2 合取）。 -/
theorem oldnewVertexDisjointOfObdatyb
    {L : Kepler.Graphs.fgraph ℕ} {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hgood : GoodList L) (hgn : GoodListNodesTl L hgood)
    (hm : markedList L hgood N r x)
    (hOb : ∀ d : ℕ × ℕ, d ∈ findFaceDarts L x → d ∈ N.flatten → d ∈ r) :
    Kepler.Text.setOfList (N.flatten.map (fun d => d.1)) ∩
      Kepler.Text.setOfList (newvertex L r x) = ∅ := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hgood hm
  rw [setOfListNewvertex hgood hx]
  ext v
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hv1, ⟨s, ⟨hsF, hsNr⟩, hsv⟩⟩
  obtain ⟨w, hwF, hwv⟩ := List.mem_map.mp hv1
  have hs := findFaceDartMemFlatten hgood hgn hm.2.1 hwF
    (memFindFaceImpMemDarts hsF) (hsv.trans hwv.symm)
  exact absurd (hOb s hsF hs) hsNr

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.memFindFaceImpMemDarts
#print axioms Kepler.Text.Reduction1.listPairsMemTwo
#print axioms Kepler.Text.Reduction1.listPairsMap
#print axioms Kepler.Text.Reduction1.findFaceMap
#print axioms Kepler.Text.Reduction1.mapNewvertex
#print axioms Kepler.Text.Reduction1.findFaceDartMemFlatten
#print axioms Kepler.Text.Reduction1.oldnewVertexDisjointOfObdatyb

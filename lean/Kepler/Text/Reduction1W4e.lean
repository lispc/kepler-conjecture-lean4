/-
  Kepler.Text.Reduction1W4e — J4 Wave W4 第三波（下）：`loop_choice_crit`
  （HOL reduction1.hl:4563-:4614）+ 补前置件 `iso_list_good_list_nodes`
  （tame_list.hl:3570-:3605，别名 `OISRWOF`）+ `iso_list_x`
  （HOL reduction1.hl:4655-:4708）+ `iso_list_loop_choice`
  （HOL reduction1.hl:4709-:4783）。

  载体沿 Reduction1W3a 文件头定案（chain）与 Reduction1W4b 文件头
  （`markedList`、`quotientList`、`listOfDarts`）；iso 侧沿 TameList1 批 1
  定案：`iso_list` ↦ `IsoListSpine L L' N N'`（四参数平铺，
  HOL 把 (L,N) 捆成单参）。

  **陈述对账（逐字对 HOL 原文；四件均零省前提、保 HOL 原序）**：
  · `loop_choice_crit`：十四前提；`prev_el (FST f) v = u` ↦
    `prevEl f.vertices v = u`，`(u,v) = x` 保朝向。末前提
    `MEM x (list_of_darts (fgraph g))` 在 Lean 证体内未被消费（HOL 证体的
    `find_list_uniq` 收口亦只用 `uniq (flatten N) /\ MEM x r /\ MEM r N`），
    按原文保留不省。
  · `iso_list_good_list_nodes`（**新增件**，reduction1 之外的前置，按 HOL 原名
    全树搜定理零命中——TameList4:40 记档「结论载体 GoodListNodes 当时是 True
    占位故跳过」，现 `GoodListNodesTl` 已忠实化）：三前提保原序。结论
    `good_list_nodes L'` ↦ `∀ hL' : GoodList L', GoodListNodesTl L' hL'`
    （Assembly `GoodListNodes L := ∀ hL, nodeSet = …` 同形，免 HOL 无前提
    hypermap 与 Lean 持证人参 hypermap 的载体差）。
  · `iso_list_x`：十三前提保原序（`good_list L`/`good_list L'` 为 Lean 载体
    证人参）。
  · `iso_list_loop_choice`：HOL 十三前提；Lean 面增载体证人参
    `hL' : GoodList L'`——非数学新前提：由 `iso_list (L,[x]::r::N)
    (L',[x']::r'::N')` 首支 `L' = MAP (MAP phi) L` + `good_list L` 经
    `iso_list_good_list`（TameList1 `isoListSpine_goodList`）可导出，且 Prop 层
    proof irrelevance 使任意证人等价。`r,x = loop_choice2 g L N` 保朝向。

  **查重记账（按 HOL 原名搜 docstring；消费件逐个核签名，经本文件编译实证）**：
  · `loop_choice_crit` 的 Lean 证体比 HOL 短：`loop_choice_props` 已给
    `MEM r' N /\ MEM x r'`，与前提 `MEM x r /\ MEM r N` 经 `uniq_sublist_unique`
    直接逼出 `r' = r`（HOL 展开 LOOP_CHOICE 后以 `find_list_uniq` 收口，
    同一事实）；`is_restricted_all_uniq`（T59）在库，本文件证体未消费。
  · `iso_list_good_list_nodes`：HOL 走 `iso_number_of_nodes` 计数（GoodListNodes
    集合等式 def 的 Lean 载体下不可用）；Lean 侧轨道像内容已在库
    （JcajyduRxBridge `isoNodeSetImageGen`/`rxNodesOfListSetMap`/
    `rxNodesOfListSetEq` 泛型形）+ MAP 型层 `la7_hypermapOfList_map`（TameLp）
    组装，等价于该文件 `rxNumTransportBridge` 第三槽在 α = ℕ、φ 给定时的实例。
  · `iso_list_x`：`marked_list_x_quotient`（Reduction1W4b）、
    `isop_list_quotient`（TameList41 `isopListQuotientSpine`，Spine 载体，
    经 ChainBridge `quotientList_eq_quotientListSpine` 换装）、
    `inj_on_list_of_darts`（TameList57 `injOnListOfDarts`）、
    `map_id_eq`（TameList59 `mapIdEq`）、`isop_list_iso_list`（T59 定义性
    `Iff.rfl`，证体内联 ∃ 展开）。HOL 证体引的 L' 侧
    `marked_list_x_quotient` 实例在本路线不消费（前提保留）。
  · `iso_list_loop_choice`：`loop_choice_props`（T4TheoryA）、`loop_choice_crit`
    （本文件）、`iso_list_x`（本文件）、`simple_hypermap_all_uniq`（T14）。
    HOL 证体在 L' 侧 SUBANTS 里引的 `iso_list_sym_nil`/`iso_list_good_list`/
    `iso_list_restricted`/`iso_list_good_list_nodes`/`mem_minimalVertex`/
    `minimalFace_nonnil` 六件：前两件被本路线吸收（`marked_list L'` 首合取直给
    `is_restricted`；`hL'` 载体参直给 `good_list`），`iso_list_good_list_nodes`
    本文件新落后消费，`mem_minimalVertex`/`minimalFace_nonnil` 在
    `loop_choice_props` 体内，本文件不直接消费。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W3a
import Kepler.Text.Reduction1W4b
import Kepler.Text.T4TheoryA
import Kepler.Text.ChainListsL2
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2QuotientAlt
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList1
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList41
import Kepler.Text.TameSpine.TameList57
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameSpine.JcajyduRxBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts prevEl)
open Kepler.Graphs (fgraph Graph Face minimalFace minimalVertex nonFinals)
open Kepler.Text.ChainLists (normalList markedList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph loopChoice2)
open Kepler.Text.Reduction5 (Dart quotientList finalList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl nodesOfListSet)
open Kepler.Text.TameSpine (NormalListSpine quotientListSpine IsoListSpine
  IsopListSpine)

/-! ## §1 `loop_choice_crit`（reduction1.hl:4563-:4614） -/

/-- **HOL `loop_choice_crit`**（reduction1.hl:4563-:4614）：
`good_list L /\ good_list_nodes L /\ is_restricted (hypermap_of_list L) /\
normal_list L N /\ ~finalGraph g /\ all uniq (quotient_list L N) /\
match_quotient_list g L N /\ minimalFace (nonFinals g) = f /\
minimalVertex g f = v /\ prev_el (FST f) v = u /\ (u,v) = x /\ MEM x r /\
MEM r N /\ MEM x (list_of_darts (fgraph g)) ==> loop_choice2 g L N = r,x`。
`loop_choice_props` 于 `(r', x') := loop_choice2 g L N`：`x' = (prev_el (FST f) v, v)
= x`、`r' ∈ N`、`x ∈ r'`；与 `x ∈ r`、`r ∈ N` 经 `uniq_sublist_unique`
（`uniq (flatten N)` = `normal_list` 首合取）得 `r' = r`。 -/
theorem loopChoiceCrit {g : Graph} {L : fgraph ℕ} {N : List (List Dart)}
    {f : Face} {v u : ℕ} {r : List Dart} {x : Dart} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hnl : normalList L hL N)
    (hnf : Kepler.Graphs.Graph.final g = false)
    (hqu : ∀ s ∈ quotientList L N, s.Nodup)
    (hmq : matchQuotientList g L N)
    (hf : minimalFace (nonFinals g) = f)
    (hv : minimalVertex g f = v)
    (hu : prevEl f.vertices v = u)
    (hx : (u, v) = x)
    (hxr : x ∈ r)
    (hrN : r ∈ N)
    (hxfg : x ∈ listOfDarts (fgraphOfGraph g)) :
    loopChoice2 g L N = (r, x) := by
  rcases hlc : loopChoice2 g L N with ⟨r', x'⟩
  obtain ⟨hr'N, hx'r', -, hx'eq⟩ :=
    Kepler.Text.Reduction3.loopChoiceProps L hL hgn hres N hnl g hnf hqu hmq
      r' x' f v hf hv hlc
  have hxx' : x' = x := by rw [← hx'eq, hu, hx]
  rw [hxx'] at hx'r' ⊢
  have hrr' : r' = r :=
    Kepler.Text.TameSpine.uniqSublistUnique N hnl.1 r' hr'N r hrN ⟨x, hx'r', hxr⟩
  rw [hrr']

/-! ## §2 `iso_list_good_list_nodes`（tame_list.hl:3570-:3605） -/

/-- **HOL `iso_list_good_list_nodes`**（tame_list.hl:3570-:3605，别名
`OISRWOF` :3607）：`iso_list (L,[]) (L',[]) /\ good_list L /\
good_list_nodes L ==> good_list_nodes L'`。
证体路线偏离记档：HOL 走 `iso_number_of_nodes` 计数（GoodListNodes 的 Lean
集合等式载体下不可用）；Lean 侧按 JcajyduRxBridge §3/§4 的轨道像形组装——
`la7_hypermapOfList_map`（MAP 型层 BijOn + nodeMap 共轭）+
`isoNodeSetImageGen`（node 轨道族沿 iso 搬运）+ `rxNodesOfListSetMap`/
`rxNodesOfListSetEq`（`nodes_of_list` 集沿 pair-lift 的像链，α = ℕ 折算）。 -/
theorem isoListGoodListNodes {L L' : fgraph ℕ} (hiso : IsoListSpine L L' [] [])
    (hL : GoodList L) (hgn : GoodListNodesTl L hL) :
    ∀ hL' : GoodList L', GoodListNodesTl L' hL' := by
  obtain ⟨phi, hinj, hL'map, -⟩ := hiso
  subst hL'map
  intro hL'
  have hinj' : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, phi u = phi v → u = v :=
    Kepler.Text.TameSpine.injOn_elementsOfList_iff.mp hinj
  have hmap := Kepler.Text.TameLp.la7_hypermapOfList_map L hinj' hL
  have hbij : Set.BijOn (fun d : ℕ × ℕ => (phi d.1, phi d.2))
      (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ))
      (↑(hypermapOfList (L.map (List.map phi)) hL').darts : Set (ℕ × ℕ)) := by
    rw [Kepler.Text.TameLp.darts_hypermapOfList L hL,
      Kepler.Text.TameLp.darts_hypermapOfList (L.map (List.map phi)) hL']
    exact hmap.1
  have hcomm : ∀ x ∈ (hypermapOfList L hL).darts,
      (hypermapOfList (L.map (List.map phi)) hL').nodeMap (phi x.1, phi x.2)
        = (phi ((hypermapOfList L hL).nodeMap x).1,
          phi ((hypermapOfList L hL).nodeMap x).2) := by
    intro x hx
    have hxd : x ∈ listOfDarts L := by
      have h5 : x ∈ (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) := hx
      rw [Kepler.Text.TameLp.darts_hypermapOfList] at h5
      exact h5
    have hx2 : (phi x.1, phi x.2) ∈
        (hypermapOfList (L.map (List.map phi)) hL').darts := by
      have h6 : (phi x.1, phi x.2) ∈
          (↑(hypermapOfList (L.map (List.map phi)) hL').darts : Set (ℕ × ℕ)) := by
        rw [Kepler.Text.TameLp.darts_hypermapOfList]
        exact hmap.1.1 hxd
      exact h6
    rw [Kepler.Text.TameLp.nodeMap_hypermapOfList (L.map (List.map phi)) hL' hx2,
      Kepler.Text.TameLp.nodeMap_hypermapOfList L hL hx]
    exact (hmap.2 x hxd).1
  show (hypermapOfList (L.map (List.map phi)) hL').nodeSet =
    nodesOfListSet (L.map (List.map phi))
  rw [Kepler.Text.TameSpine.isoNodeSetImageGen
      (H := hypermapOfList L hL)
      (G := hypermapOfList (L.map (List.map phi)) hL')
      (f := fun d : ℕ × ℕ => (phi d.1, phi d.2)) hcomm hbij,
    show (hypermapOfList L hL).nodeSet = nodesOfListSet L from hgn,
    ← Kepler.Text.TameSpine.rxNodesOfListSetEq L,
    ← Kepler.Text.TameSpine.rxNodesOfListSetEq (L.map (List.map phi)),
    Kepler.Text.TameSpine.rxNodesOfListSetMap hinj']

/-! ## §3 `iso_list_x`（reduction1.hl:4655-:4708） -/

/-- **HOL `iso_list_x`**（reduction1.hl:4655-:4708）：
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\ good_list L /\
all uniq L /\ normal_list L' N' /\ is_edge_nondegenerate (hypermap_of_list L')
/\ good_list L' /\ all uniq L' /\ marked_list L N r x /\
marked_list L' N' r' x' /\ match_quotient_list g L N /\
match_quotient_list g L' N' /\ iso_list (L,([x]::r::N)) (L',([x']::r'::N')) ==>
x = x'`。
证体（HOL 同构）：cons 形展开取 `x' = (phi x.1, phi x.2)` 与 `N' = MAP … N`；
`isop_list_quotient` 于 (L,N)；两侧 `match_quotient_list` 给
`quotient_list L' N' = quotient_list L N`；`marked_list_x_quotient` +
`inj_on_list_of_darts` + `map_id_eq` 收口（x 是商层 dart 表 pair-lift 像的
不动点）。 -/
theorem isoListX {g : Graph} {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    {x : Dart} {L' : fgraph ℕ} {N' : List (List Dart)} {r' : List Dart}
    {x' : Dart} (hL : GoodList L) (hL' : GoodList L')
    (hnl : normalList L hL N)
    (hend : (hypermapOfList L hL).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hnl' : normalList L' hL' N')
    (hend' : (hypermapOfList L' hL').EdgeNondegenerate)
    (hall' : ∀ l ∈ L', l.Nodup)
    (hm : markedList L hL N r x)
    (hm' : markedList L' hL' N' r' x')
    (hmq : matchQuotientList g L N)
    (hmq' : matchQuotientList g L' N')
    (hiso : IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N')) :
    x = x' := by
  obtain ⟨phi, hinj, hL'map, hN'map⟩ := hiso
  have h1 : [x'] :: r' :: N' =
      [(phi x.1, phi x.2)] :: r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) ::
        N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) := hN'map
  obtain ⟨hx1, h2⟩ := List.cons.inj h1
  obtain ⟨-, hN'⟩ := List.cons.inj h2
  have hx' : x' = (phi x.1, phi x.2) := (List.cons.inj hx1).1
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  obtain ⟨hinjq, hqmap, -⟩ :=
    Kepler.Text.TameSpine.isopListQuotientSpine L hL hnlS hend hall phi
      ⟨hinj, hL'map, hN'⟩
  have hqq : quotientListSpine L' N' = quotientListSpine L N := by
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine,
      ← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, ← hmq'.2]
    exact hmq.2
  have hxq : x ∈ listOfDarts (quotientListSpine L N) := by
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact markedListXQuotient hL hnl hend hall hm
  have hmapid : (listOfDarts (quotientListSpine L N)).map
      (fun d : ℕ × ℕ => (phi d.1, phi d.2)) =
      (listOfDarts (quotientListSpine L N)).map id := by
    rw [List.map_id,
      ← Kepler.Text.TameSpine.injOnListOfDarts (quotientListSpine L N) phi hinjq,
      ← hqmap, hqq]
  have hfix := (Kepler.Text.TameSpine.mapIdEq _ _ _).mp hmapid x hxq
  rw [hx']
  exact hfix.symm

/-! ## §4 `iso_list_loop_choice`（reduction1.hl:4709-:4783） -/

/-- **HOL `iso_list_loop_choice`**（reduction1.hl:4709-:4783）：
`good_list L /\ good_list_nodes L /\ is_restricted (hypermap_of_list L) /\
normal_list L N /\ ~finalGraph g /\ match_quotient_list g L N /\
match_quotient_list g L' N' /\ all uniq (quotient_list L N) /\
good_list (quotient_list L N) /\ marked_list L N r x /\
marked_list L' N' r' x' /\ iso_list (L,([x]::r::N)) (L',([x']::r'::N')) /\
r,x = loop_choice2 g L N ==> (x = x') /\ (loop_choice2 g L' N' = r',x')`。
证体：`x = x'` 由 `iso_list_x`；L' 侧的 `is_restricted`/`normal_list`/
`all uniq (quotient_list L' N')` 取自 `marked_list L' N' r' x'`（HOL SUBANTS
的 `marked_list` 直取同构），`good_list_nodes L'` 由 `iso_list_good_list_nodes`
（§2）沿 `(L,[]) (L',[])` 运输，`loop_choice_crit` 于 L' 收口。
载体证人参 `hL'`（非数学新前提，见文件头）。`hgq`（HOL
`good_list (quotient_list L N)` 前提）在 Lean 证体内未被消费，按原文保留。 -/
theorem isoListLoopChoice {g : Graph} {L : fgraph ℕ} {N : List (List Dart)}
    {r : List Dart} {x : Dart} {L' : fgraph ℕ} {N' : List (List Dart)}
    {r' : List Dart} {x' : Dart} (hL : GoodList L) (hL' : GoodList L')
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hnl : normalList L hL N)
    (hnf : Kepler.Graphs.Graph.final g = false)
    (hmq : matchQuotientList g L N)
    (hmq' : matchQuotientList g L' N')
    (hqu : ∀ s ∈ quotientList L N, s.Nodup)
    (hgq : GoodList (quotientList L N))
    (hm : markedList L hL N r x)
    (hm' : markedList L' hL' N' r' x')
    (hiso : IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N'))
    (hlc : (r, x) = loopChoice2 g L N) :
    x = x' ∧ loopChoice2 g L' N' = (r', x') := by
  obtain ⟨-, -, hxfg, hxeq⟩ :=
    Kepler.Text.Reduction3.loopChoiceProps L hL hgn hres N hnl g hnf hqu hmq
      r x _ _ rfl rfl hlc.symm
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L hL hgn hres.simple
  -- L' 侧：is_restricted / normal_list / all uniq (quotient) 取自 marked_list L'
  have hres' : (hypermapOfList L' hL').IsRestricted := hm'.1
  have hnl' : normalList L' hL' N' := hm'.2.1
  have hqu' : ∀ s ∈ quotientList L' N', s.Nodup := hm'.2.2.2.2.1.1
  have hiso0 : IsoListSpine L L' [] [] := by
    obtain ⟨phi, hinj, hL'map, -⟩ := hiso
    exact ⟨phi, hinj, hL'map, rfl⟩
  have hgn' : GoodListNodesTl L' hL' := isoListGoodListNodes hiso0 hL hgn hL'
  have hall' : ∀ l ∈ L', l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L' hL' hgn' hres'.simple
  have hxx' : x = x' :=
    isoListX hL hL' hnl hres.edgeNondegenerate hall hnl' hres'.edgeNondegenerate
      hall' hm hm' hmq hmq' hiso
  refine ⟨hxx', ?_⟩
  refine loopChoiceCrit hL' hgn' hres' hnl' hnf hqu' hmq' rfl rfl rfl
    (hxeq.trans hxx') hm'.2.2.2.1 hm'.2.2.1 ?_
  rw [← hxx']
  exact hxfg

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.loopChoiceCrit
#print axioms Kepler.Text.Reduction1.isoListGoodListNodes
#print axioms Kepler.Text.Reduction1.isoListX
#print axioms Kepler.Text.Reduction1.isoListLoopChoice

/-
  Kepler.Text.Reduction1W4c — J4 Wave W4 第三波（上）：
  `final_list_prev_quotient_list_rot`（HOL reduction1.hl:4292-:4368）+
  `mem_makeFaceFinal_planeGraphP_etc`（HOL reduction1.hl:4393-:4548，W4 区最大件）。

  载体沿 Reduction1W3a 文件头定案（chain）；图侧沿 Reduction1W4a 文件头④
  （`GoodFacesV3`/`VerticesSet2Eq` 取 TameCorrList 载体、`finalGraph g` ↦
  `Graph.final g = true`、`fgraph g` ↦ `Graph.fgraph g`、`FST f` ↦ `f.vertices`、
  `sizel (finals g)` ↦ `(finals g).length`）。

  **陈述对账（逐字对 HOL 原文）**：
  · `final_list_prev_quotient_list_rot`：十前提保 HOL 原序（`good_list L` 本就是
    首前提）；`MAP FST r` ↦ `r.map Prod.fst`、`rot n fq` ↦ `fq.rotate n`。
    零省前提。
  · `mem_makeFaceFinal_planeGraphP_etc`：HOL 十五前提里 `good_list L` 出现两次
    （第 3 与第 12 位，原文如此）；Lean 侧 `GoodList L` 是 `normalList`/
    `hypermapOfList` 的载体证人参，只能绑定一次且须前移为首参（同
    `flagListSeed`/`markedListXQuotient` 的处理）——其余十三前提保 HOL 原序。
    **零省前提**：`~(N = [])` 一条在 Lean 证体内未被消费（HOL 证体所引诸件
    亦无一以它为前提），按原文保留不省；其余前提全部被消费。
    `foldr maxn 0 (MAP sizel L) - 3 = p` ↦ `(L.map List.length).foldr max 0 - 3 = p`
    （与 `isRestrictedSizeFace2`/`maxFinalsGExists` 同载体）。

  **查重记账（按 HOL 原名搜 docstring；命中后逐个核签名并经本文件编译实证）**：
  · `Dpzgbyf.planegraph_all_nonempty` 与 `Dpzgbyf.DPZGBYF` 全树零命中。HOL 证体
    里这两件只用来得 `~(FST f = [])`（:4451-:4456）。本文件改用已在库的
    `minimalFaceNonnil`（T4TheoryA，HOL `minimalFace_nonnil` reduction1.hl:3728）：
    其前提集 `good_list L / good_list_nodes L / is_restricted / normal_list L N /
    match_quotient_list g L N / ~finalGraph g` 恰是本件前提的子集（编译实证）。
    这是**证体路线偏离**（不经 planegraph ⇒ 面全非空），陈述不受影响。
  · HOL 末段 `list_pairs (FST f) = FST rx` 的手工链（`rot_sym` + `map_rot` +
    `rot_list_pairs` + `fst_list_pairs`，:4533-:4546）= 已在库
    `finalListPairs`（Reduction3Thm7C，HOL `final_list_pairs` reduction3.hl:2571，
    `list_pairs (MAP FST r) = r`）一步。
  · `final_list_prev_quotient_list_rot` 的子断言
    `MEM r N /\ MEM d (list_pairs (core L r)) ==> MEM d r` 与 `flag_list_seed` /
    `poioj` 同（Reduction1W3c 体内内联、Reduction1W3f 私件）；本文件私件同证
    重落（私件不可跨文件消费）。HOL 证体里引入的 `good_list_quotient`
    （:4326-:4328）之后零消费，Lean 侧不引。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W3a
import Kepler.Text.Reduction1W3e
import Kepler.Text.Reduction1W4a
import Kepler.Text.T4TheoryA
import Kepler.Text.Reduction3Thm4
import Kepler.Text.Reduction3Thm7C
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.ChainBridgeParts
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList16
import Kepler.Text.TameSpine.TameList34
import Kepler.Text.TameSpine.TameList47
import Kepler.Text.TameSpine.TameList49
import Kepler.Text.TameSpine.TameList50
import Kepler.Text.TameSpine.TameList52
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs prevEl nextEl findFaceDarts)
open Kepler.Graphs (fgraph Graph Face makeFaceFinal setFinal finals minimalFace
  minimalVertex nonFinals)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph loopChoice2)
open Kepler.Text.Reduction5 (Dart quotientList finalList parts)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine quotientListSpine coreSpine partsSpine
  finalListSpine PlaneGraphPSpine PlaneGraphSpine listOfFaces)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)

/-! ## §0 私件：`list_pairs (core L r)` 的元皆在 `r` -/

/-- HOL `flag_list_seed` / `poioj` / `final_list_prev_quotient_list_rot` 三处
内联的同一子断言：`MEM r N /\ MEM d (list_pairs (core L r)) ==> MEM d r`
（list_pairs_core + parts_uniq_nonnil + MEM_LAST；Reduction1W3f 私件同证）。 -/
private theorem listPairsCoreMemAux {L : fgraph ℕ} (hL : GoodList L)
    {N : List (List Dart)} (hnlS : NormalListSpine hL N)
    (hend : (hypermapOfList L hL).EdgeNondegenerate) (hall : ∀ l ∈ L, l.Nodup)
    {r : List Dart} (hr : r ∈ N) {d : Dart} (hd : d ∈ listPairs (coreSpine L r)) :
    d ∈ r := by
  obtain ⟨hun', hne'⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hnlS hr
  have hmapEq : (parts L r).map (fun q => q.getLast!) =
      (parts L r).map (fun q => q.getLastD (0, 0)) :=
    List.map_congr_left fun q _ => Kepler.Text.ChainBridge.getLast!_eq_getLastD q
  rw [Kepler.Text.TameSpine.listPairsCore L hL hnlS hend hall hr,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine, hmapEq] at hd
  have hfl := memMapLast (Kepler.Text.MoreLemma2Island2.partsNonnil L hne')
    (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r) hd
  rwa [Kepler.Text.MoreLemma2Island2.partsFlatten L hun' hne'] at hfl

/-! ## §1 `final_list_prev_quotient_list_rot`（reduction1.hl:4292-:4368） -/

/-- **HOL `final_list_prev_quotient_list_rot`**（reduction1.hl:4292-:4368）：
`good_list L /\ is_edge_nondegenerate (hypermap_of_list L) /\ final_list L r /\
MEM v fq /\ uniq fq /\ MEM (prev_el fq v,v) r /\ MEM r N /\ normal_list L N /\
all uniq L /\ MEM fq (quotient_list L N) ==>
(MAP FST r = fq /\ (?n. MEM (rot n fq) L))`。
证体（HOL 同构）：`fq = core L r1`（`quotient_list_core`），
`(prev_el fq v, v) ∈ list_pairs fq`（`prev_el_list_pairs_eq`）落在 `r1` 内
（§0 私件），与 `r` 有公共 dart ⇒ `r1 = r`（`uniq_sublist_unique`）；
`core L r = MAP FST r`（`final_list_core`）给首合取；`rot n r = find_face L x`
（`final_list_rot`）+ `mem_find_face` + `fst_list_of_faces` 给次合取。 -/
theorem finalListPrevQuotientListRot {L : fgraph ℕ} {N : List (List Dart)}
    {fq : List ℕ} {r : List Dart} {v : ℕ} (hL : GoodList L)
    (hend : (hypermapOfList L hL).EdgeNondegenerate)
    (hfin : finalList L r)
    (hv : v ∈ fq)
    (hun : fq.Nodup)
    (hpr : (prevEl fq v, v) ∈ r) (hrN : r ∈ N)
    (hnl : normalList L hL N)
    (hall : ∀ l ∈ L, l.Nodup)
    (hfq : fq ∈ quotientList L N) :
    r.map Prod.fst = fq ∧ ∃ n, fq.rotate n ∈ L := by
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  obtain ⟨hrun, hrne⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hnlS hrN
  have hrD : ∀ y ∈ r, y ∈ listOfDarts L := fun y hy =>
    Kepler.Text.TameSpine.normalListListOfDarts hnlS y
      (List.mem_flatten.mpr ⟨r, hrN, hy⟩)
  have hxD : (prevEl fq v, v) ∈ listOfDarts L := hrD _ hpr
  have hfinS : finalListSpine L r :=
    (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp hfin
  obtain ⟨n, hn⟩ := Kepler.Text.TameSpine.finalListRot hL hfinS hpr hrun hxD
  have hcore : coreSpine L r = r.map Prod.fst :=
    Kepler.Text.TameSpine.finalListCore hL hrD hend hrun hfinS
  -- fq = core L r1
  rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine,
    Kepler.Text.TameSpine.quotientListCore] at hfq
  obtain ⟨r1, hr1N, hr1⟩ := List.mem_map.mp hfq
  -- x ∈ r1
  have hx1 : (prevEl fq v, v) ∈ r1 := by
    refine listPairsCoreMemAux hL hnlS hend hall hr1N ?_
    rw [hr1]
    exact Kepler.Text.Reduction3.prevElListPairsEq hun hv
  have heq : r1 = r :=
    Kepler.Text.TameSpine.uniqSublistUnique N hnlS.1 r1 hr1N r hrN ⟨_, hx1, hpr⟩
  rw [heq, hcore] at hr1
  refine ⟨hr1, n, ?_⟩
  rw [← hr1, ← List.map_rotate, hn]
  have hmem := Kepler.Text.TameSpine.memFindFace L hxD
  have h2 : (findFaceDarts L (prevEl fq v, v)).map Prod.fst ∈
      (L.map listPairs).map (fun r => r.map Prod.fst) :=
    List.mem_map.mpr ⟨_, hmem, rfl⟩
  rwa [Kepler.Text.TameSpine.fstListOfFaces] at h2

/-! ## §2 `mem_makeFaceFinal_planeGraphP_etc`（reduction1.hl:4393-:4548） -/

/-- **HOL `mem_makeFaceFinal_planeGraphP_etc`**（reduction1.hl:4393-:4548）：
`~finalGraph g /\ all uniq (fgraph g) /\ good_list L /\ normal_list L N /\
~(N=[]) /\ planegraphP p g /\ foldr maxn 0 (MAP sizel L) - 3 = p /\
match_quotient_list g L N /\ is_restricted (hypermap_of_list L) /\
all uniq (quotient_list L N) /\ final_list L (FST (loop_choice2 g L N)) /\
good_list L /\ good_list_nodes L /\
vertices_set2 g = elements_of_list (fgraph g) /\ good_faces_v3 g ==>
(?g'. match_quotient_list g' L N /\ planegraphP p g' /\
vertices_set2 g' = elements_of_list (fgraph g') /\ good_faces_v3 g' /\
sizel (finals g) < sizel (finals g'))`。
证人 `g' := makeFaceFinal f g`（`f` = 最小非终面）。证体沿 HOL：
`loop_choice_props` 取 `(r, x)` 的性质 → `final_list_rot` + `mem_find_face` +
`is_restricted_size_face2` 给面长界 → `final_list_prev_quotient_list_rot`（§1）
给 `MAP FST r = FST f` → `makeFaceFinal_planegraphP` /
`facesAt_filter_makeFaceFinal` / `fgraph_makeFaceFinal` / `makeFaceFinal_mono`
四合取 → `mem_faces_makeFaceFinal` 两支闭 `match_quotient_list` 滤面条款。
两处路线偏离见文件头查重记账（`minimalFaceNonnil` 代 Dpzgbyf 两件；
`finalListPairs` 代末段手工 rot 链）。 -/
theorem memMakeFaceFinalPlaneGraphPEtc {g : Graph} {L : fgraph ℕ}
    {N : List (List Dart)} {p : ℕ} (hL : GoodList L)
    (hnf : Kepler.Graphs.Graph.final g = false)
    (hung : ∀ l ∈ g.fgraph, l.Nodup)
    (hnl : normalList L hL N)
    (hNne : N ≠ [])
    (hpg : PlaneGraphPSpine p g)
    (hp : (L.map List.length).foldr max 0 - 3 = p)
    (hmq : matchQuotientList g L N)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hqu : ∀ s ∈ quotientList L N, s.Nodup)
    (hfin : finalList L (loopChoice2 g L N).1)
    (hgn : GoodListNodesTl L hL)
    (hvs2 : VerticesSet2Eq g)
    (hgf : GoodFacesV3 g) :
    ∃ g' : Graph, matchQuotientList g' L N ∧ PlaneGraphPSpine p g' ∧
      VerticesSet2Eq g' ∧ GoodFacesV3 g' ∧
      (finals g).length < (finals g').length := by
  -- 记号：f = 最小非终面，v = 其最小顶点，(r, x) = loop_choice2 g L N
  obtain ⟨f, hf⟩ : ∃ f, minimalFace (nonFinals g) = f := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, minimalVertex g f = v := ⟨_, rfl⟩
  rcases hlc : loopChoice2 g L N with ⟨r, x⟩
  rw [hlc] at hfin
  have hfinr : finalList L r := hfin
  obtain ⟨hrN, hxr, hxfg, hxeq⟩ :=
    Kepler.Text.Reduction3.loopChoiceProps L hL hgn hres N hnl g hnf hqu hmq
      r x f v hf hv hlc
  have hend : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L hL hgn hres.simple
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  obtain ⟨hrun, hrne⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hnlS hrN
  have hxD : x ∈ listOfDarts L := by
    refine Kepler.Text.TameSpine.listOfDartsQuotientDarts L hL hnlS hend hall ?_
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, ← hmq.2]
    exact hxfg
  -- rot n r = find_face L x，面长界（is_restricted_size_face2）
  obtain ⟨n, hn⟩ := Kepler.Text.TameSpine.finalListRot hL
    ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp hfinr)
    hxr hrun hxD
  have hf'mem : findFaceDarts L x ∈ listOfFaces L :=
    Kepler.Text.TameSpine.memFindFace L hxD
  obtain ⟨h3', hle'⟩ := isRestrictedSizeFace2 L hL hres hf'mem
  -- FST f ≠ []（minimalFace_nonnil）、v ∈ FST f（mem_minimalVertex）
  have hfvne : f.vertices ≠ [] := by
    rw [← hf]
    exact Kepler.Text.Reduction3.minimalFaceNonnil L hL hgn hres N hnl g hmq hnf
  have hvm : v ∈ f.vertices := by
    rw [← hv]
    exact Kepler.Text.TameSpine.memMinimalVertex g f hfvne
  have hfm : f.vertices ∈ g.fgraph := by
    rw [← hf]
    exact Kepler.Text.TameSpine.memMinimalFaceFgraph g hnf
  have hfq : f.vertices ∈ quotientList L N := by
    rw [← hmq.2]
    exact hfm
  have hfun : f.vertices.Nodup := hqu _ hfq
  have hpr : (prevEl f.vertices v, v) ∈ r := by
    rw [hxeq]
    exact hxr
  obtain ⟨hmapr, -⟩ :=
    finalListPrevQuotientListRot hL hend hfinr hvm hfun hpr hrN hnl hall hfq
  have hlen : f.vertices.length = (findFaceDarts L x).length := by
    rw [← hn, List.length_rotate, ← hmapr, List.length_map]
  have h3 : 3 ≤ f.vertices.length := by omega
  have hle : f.vertices.length ≤ p + 3 := by omega
  -- 图侧四合取
  have hpg' : PlaneGraphPSpine p (makeFaceFinal f g) :=
    makeFaceFinalPlanegraphP hpg hnf hf hv h3 hle hvm hfm hung hgf hvs2
  have hgf' : GoodFacesV3 (makeFaceFinal f g) :=
    facesAtFilterMakeFaceFinal rfl ⟨p, hpg⟩ hgf
  have hfg' : (makeFaceFinal f g).fgraph = g.fgraph :=
    Kepler.Text.TameSpine.fgraphMakeFaceFinal f g
  have hvs2' : VerticesSet2Eq (makeFaceFinal f g) := by
    show Kepler.Text.TameCorrList.verticesSet2 (makeFaceFinal f g) =
      Kepler.Text.TameLp.elementsOfList (makeFaceFinal f g).fgraph
    rw [hfg']
    exact hvs2
  -- finals 严格增（makeFaceFinal_mono + mem_minimalFace_nonFinals）
  have hne : nonFinals g ≠ [] := by
    intro hc
    have h1 : Kepler.Graphs.Graph.final g = true := by
      show (nonFinals g).isEmpty = true
      rw [hc]
      rfl
    rw [h1] at hnf
    exact Bool.noConfusion hnf
  have hmem : f ∈ g.faces.filter (fun f => !f.final) := by
    rw [← hf]
    exact Kepler.Text.TameSpine.memMinimalFaceNonFinals g hne
  obtain ⟨hfF, hfnf⟩ := List.mem_filter.mp hmem
  have hffin : f.final = false := by simpa using hfnf
  have hmono : (finals g).length < (finals (makeFaceFinal f g)).length :=
    makeFaceFinalMono g f hfF hffin
  -- list_pairs (FST f) = r（final_list_pairs）
  have hlp : listPairs f.vertices = r := by
    rw [← hmapr]
    exact Kepler.Text.Reduction3.finalListPairs L r x hL hrun hfinr hxr hxD
  refine ⟨makeFaceFinal f g, ⟨?_, ?_⟩, hpg', hvs2', hgf', hmono⟩
  · -- match_quotient_list 滤面条款：mem_faces_makeFaceFinal 两支
    intro d hd
    obtain ⟨f'', hf'', hf''d⟩ := List.mem_map.mp hd
    have hf''fin : f'' ∈ finals (makeFaceFinal f g) := hf''
    rcases memFacesMakeFaceFinal g f f'' hf''fin with h1 | h1
    · have hd2 : d = r := by
        rw [← hf''d, h1]
        exact hlp
      rw [hd2]
      exact List.mem_filter.mpr ⟨hrN, decide_eq_true hfinr⟩
    · exact hmq.1 d (List.mem_map.mpr ⟨f'', h1, hf''d⟩)
  · show fgraphOfGraph (makeFaceFinal f g) = quotientList L N
    rw [← hmq.2]
    exact hfg'

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.finalListPrevQuotientListRot
#print axioms Kepler.Text.Reduction1.memMakeFaceFinalPlaneGraphPEtc

/-
  Kepler.Text.Reduction1W4g — J4 W4 后波（上）：`hne`（种子可许性）供料 +
  主定理「仅剩 AUQTZYZ_list + MEEIXJO」的积分件。

  本文件两件：
  · `seedFinalsAdmissibleOfAuq` —— HOL `max_finals_g_exists`
    （reduction1.hl:3561-:3727）证体里「种子三元组非空」那一段
    （:3629-:3727）的装配：取 `l` = 最长面（`foldr_maxn_exists`）、
    `f = list_pairs l`、`g = Seed (sizel f - 3)`，十合取逐条供
    （W3g 四件 + `flagListSeed` + T24 三件 + `isoList*` 与
    `isoListGoodListNodes`）。**带一条 `hAuq` 槽**（= HOL `AUQTZYZ_list`
    （AUQTZYZ_list.hl:19-24）结论的全称形，见 `AuqtzyzListSlot`）。
  · `restrictedHypermapsArePlanegraphsReduction1OfAuqMee` —— 上件供掉
    `restrictedHypermapsArePlanegraphsReduction1OfSlots`（Reduction1W4f）的
    `hne` 槽，主定理只剩 `hAuq`（AUQTZYZ_list）+ `hMee`（MEEIXJO）两槽。
    这是「无条件形差额表」的机器可查形态。

  **依赖判词（hne 是否必经 AUQTZYZ_list）**：是。`hne` 的结论要求
  `normal_list L' N'` 且 `iso_list (L,[f;r]) (L',N')`：N' 的内容由
  `r`（第二面）决定，而 `r` 的存在性与 `normal_list L [f;r]` /
  `dih2k_list (quotient_list L [f;r])` 恰是 AUQTZYZ_list 的结论。
  在库唯一的供料点 `uyouixgOfAuqtzyzList`（W2n）已把这一点立成 `hAuq`；
  全树按结论语义查重（`Dih2kListSpine` 与 `NormalListSpine [f, ·]` 的
  存在性结论）零其它落点，AUQTZYZ.hl 主定理 :1859-:2624（765 行）与
  AUQTZYZ_list.hl（329 行）均未落库。故**绕不过**：hne 的完全无条件形是
  AUQTZYZ 链的下游。本文件落「一条 hAuq 槽」版，槽逐字 = AUQTZYZ_list
  结论（前提已折进槽外的前提）。

  **陈述对账**：本文件两件均为**装配件**（非 HOL 具名件）；`hne` 的目标形
  逐字取自 `maxFinalsGExists`（W3d）的槽形与 `restrictedHypermapsArePlaneGraphsV4`
  （JcajyduShell）的入口形。`AuqtzyzListSlot` 是 AUQTZYZ_list 结论的
  Spine 载体形（`normal_list` ↦ `NormalListSpine hL`，`dih2k_list` ↦
  `Dih2kListSpine`，`MEM f (list_of_faces L)` ↦ `f ∈ listOfFaces L`——
  与 W2n `uyouixgOfAuqtzyzList` 的 `hAuq` 同载体）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2n
import Kepler.Text.Reduction1W3c
import Kepler.Text.Reduction1W3d
import Kepler.Text.Reduction1W3g
import Kepler.Text.Reduction1W4e
import Kepler.Text.Reduction1W4f
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList19
import Kepler.Text.TameSpine.TameList24
import Kepler.Text.TameSpine.TameList25
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.TameSpine.TameList58

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs)
open Kepler.Graphs (fgraph Graph)
open Kepler.Text.ChainLists (normalList flagList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph)
open Kepler.Text.Reduction5 (Dart quotientList finalList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine Dih2kListSpine quotientListSpine
  listOfFaces PlaneGraphPSpine)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq GoodListNodes)

/-! ## §0 `AUQTZYZ_list` 的槽形 -/

/-- **HOL `AUQTZYZ_list`**（AUQTZYZ_list.hl:19-24）结论的槽形（Spine 载体，
与 W2n `uyouixgOfAuqtzyzList` 的 `hAuq` 同载体）：
`good_list L /\ good_list_nodes L /\ is_restricted (hypermap_of_list L) /\
MEM f (list_of_faces L) ==> (?r. normal_list L [f;r] /\
dih2k_list (quotient_list L [f;r]))` 的全称结论。**纯缩写 `def : Prop`**
（零证明义务；`FinalsAdmissible`/`restrictedHypermapsArePlaneGraphsV4`
先例）。**未落库**：AUQTZYZ.hl 主定理 :1859-:2624 与 AUQTZYZ_list.hl 均未移植。 -/
def AuqtzyzListSlot (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ f ∈ listOfFaces L, ∃ r : List (ℕ × ℕ),
    NormalListSpine hL [f, r] ∧ Dih2kListSpine (quotientListSpine L [f, r])

/-! ## §1 `hne` 供料：种子三元组的可许性（reduction1.hl:3629-:3727 装配） -/

/-- **`max_finals_g_exists` 的种子段**（HOL reduction1.hl:3629-:3727）：
`good_list L /\ good_list_nodes L /\ is_restricted (hypermap_of_list L)` +
`p = foldr maxn 0 (MAP sizel L) - 3` + AUQTZYZ_list 槽 ==>
`∃ g L' hL' N', FinalsAdmissible L p g L' hL' N'`（即 W3d
`maxFinalsGExists` 的 `hne` 槽）。证人：`l` = 最长面，
`f = list_pairs l`，`g = Seed (sizel f - 3)`，`(L', N', r)` 取自
`UYOUIXG` 槽版；十合取逐条见证体注释。 -/
theorem seedFinalsAdmissibleOfAuq
    (hAuq : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted → AuqtzyzListSlot L hL)
    (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodes L)
    (hres : (hypermapOfList L hL).IsRestricted)
    (p : ℕ) (hp : p = (L.map List.length).foldr max 0 - 3) :
    ∃ (g : Graph) (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart)),
      FinalsAdmissible L p g L' hL' N' := by
  classical
  -- is_restricted_nonnil：`MAP sizel L ≠ []`
  have hLnne : L ≠ [] := Kepler.Text.TameSpine.isRestrictedNonnil hL hres
  have hmapne : L.map List.length ≠ [] := by simpa using hLnne
  -- foldr_maxn_exists：取最长面 l
  obtain ⟨n, hnmem, hnval⟩ := foldrMaxnExists (L.map List.length) hmapne
  obtain ⟨l, hlL, hln⟩ := List.mem_map.mp hnmem
  have hfold : l.length = (L.map List.length).foldr max 0 := by rw [hln, hnval]
  set f : List (ℕ × ℕ) := listPairs l with hfdef
  have hf : f ∈ listOfFaces L := by
    show listPairs l ∈ L.map listPairs
    exact List.mem_map.mpr ⟨l, hlL, rfl⟩
  have hfl : f.length = (L.map List.length).foldr max 0 := by
    rw [hfdef, Kepler.Text.TameLp.la7_length_listPairs]
    exact hfold
  have hfp : f.length - 3 = p := by rw [hfl, hp]
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L hL (hgn hL) hres.simple
  -- UYOUIXG（槽版）：(L', N', r, hL') 与 iso/`normal_list`/`match_quotient_list`
  obtain ⟨L', N', r, hL', hiso, hnl, hmq⟩ :=
    uyouixgOfAuqtzyzList hL hres hall (hgn hL) hf (hAuq L hL (hgn hL) hres f hf)
  -- ⑤ iso_list (L,[]) (L',[])：掉 N 分量
  have hiso0 : Kepler.Text.TameSpine.IsoListSpine L L' [] [] := by
    obtain ⟨phi, hinj, hLmap, -⟩ := hiso
    exact ⟨phi, hinj, hLmap, rfl⟩
  -- ④ ~(N' = [])：N' = MAP (MAP lift) [f;r] 是双元素表
  have hNne : N' ≠ [] := by
    obtain ⟨phi, hinj, hLmap, hNmap⟩ := hiso
    have hlen : N'.length = 2 := by rw [hNmap]; simp
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  -- ③ all uniq (quotient_list L' N')：quotient = fgraph (Seed …) + all_uniq_seed
  have hqnodup : ∀ s ∈ quotientList L' N', s.Nodup := by
    intro s hs
    rw [← hmq.2] at hs
    exact Kepler.Text.TameSpine.allUniqSeed (f.length - 3) s hs
  -- ⑦ vertices_set2 (Seed …) = elements_of_list (fgraph (Seed …))
  have hvs2 : VerticesSet2Eq (Kepler.Graphs.Seed (f.length - 3)) :=
    Kepler.Text.TameSpine.goodVerticesSet2Seed (f.length - 3)
  -- ⑧ good_faces_v3 (Seed …)：facesAt = filter（good_facesAt_seed）→ Perm refl
  have hgf : GoodFacesV3 (Kepler.Graphs.Seed (f.length - 3)) := by
    intro v hv
    rw [Kepler.Text.TameSpine.goodFacesAtSeed (f.length - 3) v hv]
    exact List.Perm.refl _
  -- ⑨ flag_list L' N'：flag_list_seed（p := f.length - 3）
  have hsym : Kepler.Text.TameSpine.IsoListSpine L' L [] [] :=
    Kepler.Text.TameSpine.isoListSpineSymNil hL hiso0
  have hres' : (hypermapOfList L' hL').IsRestricted :=
    Kepler.Text.TameSpine.isoListRestricted hL' hsym hres
  have hgn' : GoodListNodesTl L' hL' := isoListGoodListNodes hiso0 hL (hgn hL) hL'
  have hall' : ∀ l ∈ L', l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L' hL' hgn' hres'.simple
  have hflag : flagList L' N' :=
    flagListSeed hL' hnl hres'.edgeNondegenerate hall' hres'.connected hmq
  -- ⑩ 每个顶点在 quotient 的 >1 个面中：quotient = fgraph (Seed …) + seed_size_v_gt_1
  have hq1 : ∀ v ∈ (quotientList L' N').flatten,
      1 < ((quotientList L' N').filter (fun r => decide (v ∈ r))).length := by
    intro v hv
    rw [← hmq.2] at hv ⊢
    exact seedSizeVGt1 (f.length - 3) v hv
  refine ⟨Kepler.Graphs.Seed (f.length - 3), L', hL', N', ?_⟩
  unfold FinalsAdmissible
  refine ⟨hmq, hnl, hqnodup, hNne, hiso0, ?_, hvs2, hgf, hflag, hq1⟩
  -- ⑥ planegraphP p (Seed …)：seed_planegraphP + p = f.length - 3
  rw [← hfp]
  exact seedPlanegraphP (f.length - 3)

/-! ## §2 积分件：主定理只剩 `hAuq` + `hMee` 两槽 -/

/-- 主定理（HOL reduction1.hl:4784-:4975）在 `hne` 槽由 §1 供掉后的形态：
两槽 = `hAuq`（AUQTZYZ_list，`AuqtzyzListSlot` 的全称形）+ `hMee`
（MEEIXJO.hl:325 陈述逐字）。HOL 两前提 `hv7`/`htav2` 原样。 -/
theorem restrictedHypermapsArePlanegraphsReduction1OfAuqMee
    (hv7 : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
        (g : Graph) (p : ℕ) (fs : List Kepler.Graphs.Face) (f : Kepler.Graphs.Face) (v k : ℕ)
        (r : List Dart) (x : Dart),
        GoodListNodesTl L hL →
        (hypermapOfList L hL).IsRestricted →
        Kepler.Text.Reduction3.newvertexPrepped L N r x →
        Kepler.Text.ChainLists.markedList L hL N r x →
        ¬ finalList L r →
        matchQuotientList g L N →
        Kepler.Graphs.Graph.final g = false →
        PlaneGraphPSpine p g →
        GoodFacesV3 g →
        VerticesSet2Eq g →
        p = (L.map List.length).foldr max 0 - 3 →
        fs = Kepler.Graphs.nonFinals g →
        f = Kepler.Graphs.minimalFace fs →
        v = Kepler.Graphs.minimalVertex g f →
        (r, x) = Kepler.Text.Reduction3.loopChoice2 g L N →
        k = Kepler.Text.Reduction5.transformCount L N r x →
        N' = Kepler.Text.Reduction5.ntrans L N r x k →
        ∃ (g' : Graph) (i : ℕ), matchQuotientList g' L N' ∧ 3 ≤ i ∧
          i ≤ Kepler.Graphs.maxGon p ∧ GoodFacesV3 g' ∧ VerticesSet2Eq g' ∧
          g' ∈ Kepler.Graphs.generatePolygon i v f g)
    (htav2 : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
        Kepler.Text.Reduction5.transformAssumptionV2 L)
    (hAuq : ∀ (L : fgraph ℕ) (hL : GoodList L), GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted → AuqtzyzListSlot L hL)
    (hMee : ∀ (L : fgraph ℕ) (hL : GoodList L) (N : List (List Dart))
        (r : List Dart) (x : Dart) (L' : fgraph ℕ) (hL' : GoodList L')
        (N' : List (List Dart)) (r' : List Dart) (x' : Dart),
        GoodListNodesTl L hL →
        Kepler.Text.TameSpine.IsoListSpine L L' ([x] :: r :: N) ([x'] :: r' :: N') →
        Kepler.Text.ChainLists.markedList L hL N r x →
        Kepler.Text.ChainLists.markedList L' hL' N' r' x') :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 :=
  restrictedHypermapsArePlanegraphsReduction1OfSlots hv7 htav2
    (fun L hL hgn hres p hp => seedFinalsAdmissibleOfAuq hAuq L hL hgn hres p hp)
    hMee

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.seedFinalsAdmissibleOfAuq
#print axioms Kepler.Text.Reduction1.restrictedHypermapsArePlanegraphsReduction1OfAuqMee

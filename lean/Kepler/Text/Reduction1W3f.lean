/-
  Kepler.Text.Reduction1W3f — J4 Wave W3 第二波（余量）：finals 簇列表层三件
  （HOL reduction1.hl:2777-:2885：`poioj` / `match_quotient_list_finalGraph` /
  `restricted_match_finalGraph`）。

  载体沿 Reduction1W3a 文件头定案（chain）。两处载体折算：
  · `finalGraph g` ↦ `Kepler.Graphs.Graph.final g = true`（TameList56
    `finalGraphFilter` 同形）；
  · 结论 `hypermap_of_list (fgraph g) = hypermap_of_list L`：Lean 载体
    `hypermapOfList` 持 GoodList 证人参，以 `∃ hg : GoodList (fgraphOfGraph g)`
    显式入结论（同 UYOUIXG 的 `∃ hL'` 惯例，Prop 层 proof irrelevance 零收窄；
    证人实为 `goodListQuotient` 沿 `fgraph g = quotient_list L N` 换装）。

  `poioj` 的核心子断言 `MEM d (list_pairs (core L r)) ==> MEM d r` 与
  `flag_list_seed` 同（HOL 两处各自内联）；Reduction1W3c 的 flagListSeed 体内
  内联，本文件私件同证重落（两文件互不依赖，闸序自由）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W3a
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList34
import Kepler.Text.TameSpine.TameList51
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction3DefsLayer

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs)
open Kepler.Graphs (fgraph Graph)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph)
open Kepler.Text.Reduction5 (Dart quotientList finalList parts)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine quotientListSpine coreSpine partsSpine)

/-! ## §0 私件：`list_pairs (core L r)` 的元皆在 `r` -/

/-- HOL `flag_list_seed` / `poioj` 两处内联的同一子断言：
`MEM r N /\ MEM d (list_pairs (core L r)) ==> MEM d r`（list_pairs_core +
parts_flatten + mem_map_last + parts_nonnil/parts_all_nonnil）。 -/
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

/-! ## §1 `poioj`（reduction1.hl:2777-:2831） -/

/-- **HOL `poioj`**（reduction1.hl:2777-:2831）：
`good_list L /\ normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
all uniq L /\ (!x. MEM x (MAP list_pairs (quotient_list L N)) ==>
MEM x (filter (final_list L) N)) ==> all (final_list L) N`——对 `x ∈ N`，
`list_pairs (core L x)` 在滤表内（quotient_list_core）；它与 `x` 同为 `N`
的成员且有公共 dart（子断言 + parts_nonnil），`uniq_sublist_unique` 逼出
二者相等，终面性随之转给 `x`。 -/
theorem poioj {L : fgraph ℕ} {N : List (List Dart)} (hL : GoodList L)
    (hnl : normalList L hL N)
    (hend : (hypermapOfList L hL).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hsub : ∀ x ∈ (quotientList L N).map listPairs,
      x ∈ N.filter (fun r => decide (finalList L r))) :
    ∀ r ∈ N, finalList L r := by
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  intro x hx
  have hmemQ : listPairs (coreSpine L x) ∈ (quotientList L N).map listPairs := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine,
      Kepler.Text.TameSpine.quotientListCore, List.map_map]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨hlpN, hdec⟩ := List.mem_filter.mp (hsub _ hmemQ)
  obtain ⟨hunx, hnex⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hnlS hx
  have hlpne : listPairs (coreSpine L x) ≠ [] := by
    rw [Kepler.Text.TameSpine.listPairsCore L hL hnlS hend hall hx,
      ← Kepler.Text.ChainBridge.parts_eq_partsSpine]
    intro hc
    exact Kepler.Text.MoreLemma2Island2.partsNonnil L hnex (List.map_eq_nil_iff.mp hc)
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hlpne
  have heq : listPairs (coreSpine L x) = x :=
    Kepler.Text.TameSpine.uniqSublistUnique N hnlS.1 _ hlpN x hx
      ⟨d, hd, listPairsCoreMemAux hL hnlS hend hall hx hd⟩
  have hfin : finalList L (listPairs (coreSpine L x)) := of_decide_eq_true hdec
  rw [heq] at hfin
  exact hfin

/-! ## §2 `match_quotient_list_finalGraph`（reduction1.hl:2833-:2862） -/

/-- **HOL `match_quotient_list_finalGraph`**（reduction1.hl:2833-:2862）：
`good_list L /\ normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
all uniq L /\ connected_hypermap (hypermap_of_list L) /\ ~(N = []) /\
match_quotient_list g L N /\ finalGraph g ==>
hypermap_of_list (fgraph g) = hypermap_of_list L`——`finalGraph_filter` 把
match_quotient_list 的滤面条款升为「全体面」，`poioj` 得
`all (final_list L) N`，`hypermap_of_quotient_list_final` 收口，再沿
`fgraph g = quotient_list L N` 换装。 -/
theorem matchQuotientListFinalGraph {g : Graph} {L : fgraph ℕ} {N : List (List Dart)}
    (hL : GoodList L) (hnl : normalList L hL N)
    (hend : (hypermapOfList L hL).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hconn : (hypermapOfList L hL).Connected)
    (hne : N ≠ [])
    (hmq : matchQuotientList g L N)
    (hfinal : Kepler.Graphs.Graph.final g = true) :
    ∃ hg : GoodList (fgraphOfGraph g),
      hypermapOfList (fgraphOfGraph g) hg = hypermapOfList L hL := by
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  obtain ⟨hmqF, hmqQ⟩ := hmq
  have hfin : Kepler.Graphs.finals g = g.faces :=
    (Kepler.Text.TameSpine.finalGraphFilter g).mp hfinal
  -- poioj 前提：quotient_list 各面的 list_pairs 都在滤表内
  have hsub : ∀ x ∈ (quotientList L N).map listPairs,
      x ∈ N.filter (fun r => decide (finalList L r)) := by
    intro x hx
    rw [← hmqQ] at hx
    obtain ⟨vs, hvs, hvsx⟩ := List.mem_map.mp hx
    have hvs' : vs ∈ g.faces.map (fun f => f.vertices) := hvs
    obtain ⟨f, hf, hfvs⟩ := List.mem_map.mp hvs'
    have hfF : f ∈ g.faces.filter (fun f => f.isFinal) := by
      have h0 : f ∈ Kepler.Graphs.finals g := by rw [hfin]; exact hf
      exact h0
    refine hmqF x (List.mem_map.mpr ⟨f, hfF, ?_⟩)
    rw [hfvs]
    exact hvsx
  have hallfin := poioj hL hnl hend hall hsub
  have hQ := Kepler.Text.TameSpine.hypermapOfQuotientListFinal L hnlS
    (fun r hr => (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp
      (hallfin r hr)) hend hall hconn hne
  have heq : fgraphOfGraph g = quotientListSpine L N := by
    rw [hmqQ, Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
  have key : ∀ X : fgraph ℕ, X = quotientListSpine L N →
      ∃ hX : GoodList X, hypermapOfList X hX = hypermapOfList L hL := by
    intro X hX
    subst hX
    exact ⟨_, hQ⟩
  exact key _ heq

/-! ## §3 `restricted_match_finalGraph`（reduction1.hl:2864-:2885） -/

/-- **HOL `restricted_match_finalGraph`**（reduction1.hl:2864-:2885）：
`good_list L /\ good_list_nodes L /\ normal_list L N /\
is_restricted (hypermap_of_list L) /\ match_quotient_list g L N /\
finalGraph g /\ ~(N = []) ==> hypermap_of_list (fgraph g) = hypermap_of_list L`
——上件实例化：is_restricted 供 edge 非退化与连通，`simple_hypermap_uniq`
供 `all uniq L`。 -/
theorem restrictedMatchFinalGraph {g : Graph} {L : fgraph ℕ} {N : List (List Dart)}
    (hL : GoodList L) (hgn : GoodListNodesTl L hL) (hnl : normalList L hL N)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hmq : matchQuotientList g L N)
    (hfinal : Kepler.Graphs.Graph.final g = true) (hne : N ≠ []) :
    ∃ hg : GoodList (fgraphOfGraph g),
      hypermapOfList (fgraphOfGraph g) hg = hypermapOfList L hL :=
  matchQuotientListFinalGraph hL hnl hres.edgeNondegenerate
    ((Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hres.simple)
    hres.connected hne hmq hfinal

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.poioj
#print axioms Kepler.Text.Reduction1.matchQuotientListFinalGraph
#print axioms Kepler.Text.Reduction1.restrictedMatchFinalGraph

/-
  Kepler.Text.Reduction1W3c — J4 Wave W3 第二波：`all_final_list_dart`
  （HOL reduction1.hl:3013-:3029）+ `flag_list_seed`（:3358-:3560，W3 簇
  验收点）。

  载体沿 Reduction1W3a 文件头定案（chain：`Dart`/`finalList`/`normalList`/
  `flagList`/`finalDartList`）。`connected_hypermap (hypermap_of_list L)` ↦
  `(hypermapOfList L hL).Connected`（Hypermap.lean，`numberOfComponents = 1`；
  与 Assembly `ConnectedHypermap` 同体——塔线 `connectedInduction`/
  `finalListComplete` 即消费此形）。

  `flag_list_seed` 证体（HOL 同构，顺序按 Lean 依赖重排）：
  · `quotient_list_eq_cons` ⇒ `N = [r1; r2]`；`quotient_list_core` + fgraph_seed
    ⇒ `core L r1 = iota 0 k`、`core L r2 = rev (iota 0 k)`（k = maxGon p）；
  · HOL 子断言 `MEM d (list_pairs (core L r')) ==> MEM d r'`（list_pairs_core +
    parts_flatten + mem_map_last + parts_nonnil/parts_all_nonnil）；
  · match_quotient_list 滤出的终面 `list_pairs (upt 0 k)` 即 `r1`（若是 `r2`，
    则 `(1,0) ∈ r2`，list_pairs_iota 逼出 `k = 2`，与 `k = p + 3` 矛盾）；
  · 合取 2（`e_list y`）：非终面只能是 `r2`，`y ∈ list_pairs (rev (iota 0 k))`
    ⇒ `e_list y ∈ list_pairs (iota 0 k) ⊆ r1`（list_pairs_rev_iota/_iota 算术）；
  · 合取 1（contour 连通）分 `final_list L r2`：
    真支 `all_final_list_dart` 把终面 dart 集换成 `darts_of_list L`，再对
    `S = {w | u 连通到 w}` 走 `connected_induction`（闭包 = contour 簇的
    `f_list_right`/`fe_list_right`，`face_map_list`/`node_inverse_map_list`
    把超映射两映射折回 `f_list`/`f_list ∘ e_list`）；
    假支 u、v 同在 `r1`，`final_list_connected` 直收。
  HOL 证体里的 `final_dart_list_final_list`/`find_list_uniq` 绕行（先定
  `find_list N (p+2,0) = r1`）在 Lean 侧不需要：filter 成员直接给出终面性。

  `list_pairs_iota`（tame_list.hl:727）与 `list_pairs_rev_iota`（:764）已在库：
  `TameSpine.memListPairsIota`（TameList2:605）/`memListPairsRevIota`（:689），
  陈述逐字，本文件直接消费、不重落。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2l
import Kepler.Text.Reduction1W3a
import Kepler.Text.Reduction1W3b
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList2
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList21
import Kepler.Text.TameSpine.TameList34
import Kepler.Text.TameSpine.TameList46
import Kepler.Text.TameSpine.TameList47
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.ChainListsL2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs eList fList)
open Kepler.Graphs (fgraph)
open Kepler.Text.ChainLists (normalList contourList finalDartList flagList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph)
open Kepler.Text.Reduction5 (Dart quotientList finalList parts)
open Kepler.Text.TameLp (hypermapOfList)
open Kepler.Text.TameSpine (NormalListSpine quotientListSpine coreSpine partsSpine)

/-! ## §1 `all_final_list_dart`（reduction1.hl:3013-:3029） -/

/-- **HOL `all_final_list_dart`**（reduction1.hl:3013-:3029）：
`good_list L /\ connected_hypermap (hypermap_of_list L) /\ ~(N = []) /\
normal_list L N /\ all (final_list L) N ==>
set_of_list (final_dart_list L N) = darts_of_list L`——`all` 前提使
`filter (final_list L) N = N`（HOL `Seq.all_filterP`），余下即
`final_list_complete`（TameList47 `finalListComplete`）。
载体：`set_of_list l` ↦ `{d | d ∈ l}`、`darts_of_list L` ↦
`{d | d ∈ listOfDarts L}`。 -/
theorem allFinalListDart {L : fgraph ℕ} {N : List (List Dart)} (hL : GoodList L)
    (hconn : (hypermapOfList L hL).Connected) (hne : N ≠ [])
    (hnl : normalList L hL N) (hfinal : ∀ r ∈ N, finalList L r) :
    {d : Dart | d ∈ finalDartList L N} = {d : Dart | d ∈ listOfDarts L} := by
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  have hfilt : N.filter (fun r => decide (finalList L r)) = N :=
    List.filter_eq_self.mpr fun r hr => decide_eq_true (hfinal r hr)
  have hfd : finalDartList L N = N.flatten := by
    unfold finalDartList
    rw [hfilt]
  rw [hfd]
  exact Kepler.Text.TameSpine.finalListComplete hconn hne hnlS fun r hr =>
    (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp (hfinal r hr)

/-! ## §2 `flag_list_seed`（reduction1.hl:3358-:3560） -/

/-- **HOL `flag_list_seed`**（reduction1.hl:3358-:3560）：
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
good_list L /\ all uniq L /\ connected_hypermap (hypermap_of_list L) /\
match_quotient_list (Seed p) L N ==> flag_list L N`。
六前提均为顶层前件（与 HOL 同层，无内层量词夹带）；`good_list` 因载体依赖
前移为首参（`normalList`/`hypermapOfList` 持 GoodList 证人参），其余五件保
HOL 原序。证体结构见文件头。 -/
theorem flagListSeed {p : ℕ} {L : fgraph ℕ} {N : List (List Dart)} (hL : GoodList L)
    (hnl : normalList L hL N)
    (hend : (hypermapOfList L hL).EdgeNondegenerate)
    (hall : ∀ l ∈ L, l.Nodup)
    (hconn : (hypermapOfList L hL).Connected)
    (hmq : matchQuotientList (Kepler.Graphs.Seed p) L N) :
    flagList L N := by
  have hk : Kepler.Graphs.maxGon p = p + 3 := rfl
  have hkpos : 0 < Kepler.Graphs.maxGon p := by rw [hk]; omega
  obtain ⟨hmqF, hmqQ⟩ := hmq
  -- N = [r1; r2]（fgraph_seed + quotient_list_eq_cons）
  have hfg : fgraphOfGraph (Kepler.Graphs.Seed p) =
      [List.range (Kepler.Graphs.maxGon p),
        (List.range (Kepler.Graphs.maxGon p)).reverse] :=
    Kepler.Text.TameSpine.fgraphSeed p
  have hq2 : quotientList L N =
      [List.range (Kepler.Graphs.maxGon p),
        (List.range (Kepler.Graphs.maxGon p)).reverse] := hmqQ.symm.trans hfg
  obtain ⟨r1, r2, rfl⟩ := quotientListEqCons hq2
  have hnlS : NormalListSpine hL [r1, r2] :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL [r1, r2]).mp hnl
  have hr1N : r1 ∈ [r1, r2] := List.mem_cons.mpr (Or.inl rfl)
  have hr2N : r2 ∈ [r1, r2] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  -- quotient_list_core：core L r1 = iota 0 k、core L r2 = rev (iota 0 k)
  have hqS : quotientListSpine L [r1, r2] =
      [List.range (Kepler.Graphs.maxGon p),
        (List.range (Kepler.Graphs.maxGon p)).reverse] := by
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact hq2
  rw [Kepler.Text.TameSpine.quotientListCore, List.map_cons, List.map_cons,
    List.map_nil] at hqS
  injection hqS with hc1 htl
  injection htl with hc2 _
  -- HOL 子断言：`!r' d. MEM r' N /\ MEM d (list_pairs (core L r')) ==> MEM d r'`
  have hcoreMem : ∀ r' ∈ [r1, r2], ∀ d ∈ listPairs (coreSpine L r'), d ∈ r' := by
    intro r' hr' d hd
    obtain ⟨hun', hne'⟩ := Kepler.Text.TameSpine.normalListUniqNonnil hnlS hr'
    have hmapEq : (parts L r').map (fun q => q.getLast!) =
        (parts L r').map (fun q => q.getLastD (0, 0)) :=
      List.map_congr_left fun q _ => Kepler.Text.ChainBridge.getLast!_eq_getLastD q
    rw [Kepler.Text.TameSpine.listPairsCore L hL hnlS hend hall hr',
      ← Kepler.Text.ChainBridge.parts_eq_partsSpine, hmapEq] at hd
    have hfl := memMapLast (Kepler.Text.MoreLemma2Island2.partsNonnil L hne')
      (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r') hd
    rwa [Kepler.Text.MoreLemma2Island2.partsFlatten L hun' hne'] at hfl
  -- 滤出的终面 list_pairs (upt 0 k) 就是 r1
  have hdl : listPairs (List.range (Kepler.Graphs.maxGon p)) ∈
      [r1, r2].filter (fun r => decide (finalList L r)) :=
    hmqF _ (by
      rw [finalFaceSeed]
      exact List.mem_map.mpr ⟨⟨List.range (Kepler.Graphs.maxGon p), true⟩,
        List.mem_cons.mpr (Or.inl rfl), rfl⟩)
  obtain ⟨hdlN, hdlDec⟩ := List.mem_filter.mp hdl
  have hr1eq : listPairs (List.range (Kepler.Graphs.maxGon p)) = r1 := by
    rcases List.mem_cons.mp hdlN with h | h
    · exact h
    · exfalso
      have h2 : listPairs (List.range (Kepler.Graphs.maxGon p)) = r2 :=
        List.mem_singleton.mp h
      have h10 : ((1 : ℕ), (0 : ℕ)) ∈ listPairs (coreSpine L r2) := by
        rw [hc2, Kepler.Text.TameSpine.memListPairsRevIota hkpos]
        omega
      have h10r := hcoreMem r2 hr2N _ h10
      rw [← h2, Kepler.Text.TameSpine.memListPairsIota] at h10r
      omega
  have hfin1 : finalList L r1 := by
    rw [← hr1eq]
    exact of_decide_eq_true hdlDec
  have hr1fd : ∀ x ∈ r1, x ∈ finalDartList L [r1, r2] := fun x hx => by
    show x ∈ ([r1, r2].filter (fun r => decide (finalList L r))).flatten
    exact List.mem_flatten.mpr
      ⟨r1, List.mem_filter.mpr ⟨hr1N, decide_eq_true hfin1⟩, hx⟩
  unfold flagList
  refine ⟨?_, ?_⟩
  · -- 合取 1：终面 dart 两两 contour 连通
    intro u v hu hv
    by_cases hfin2 : finalList L r2
    · -- final_list L r2 支：all_final_list_dart + connected_induction
      have hallfin : ∀ r ∈ [r1, r2], finalList L r := by
        intro r hr
        rcases List.mem_cons.mp hr with h | h
        · rw [h]; exact hfin1
        · rw [List.mem_singleton.mp h]; exact hfin2
      have hfdEq := allFinalListDart hL hconn (List.cons_ne_nil r1 [r2]) hnl hallfin
      have huD : u ∈ listOfDarts L := by
        have h0 : u ∈ {d : Dart | d ∈ finalDartList L [r1, r2]} := hu
        rw [hfdEq] at h0
        exact h0
      have hvD : v ∈ listOfDarts L := by
        have h0 : v ∈ {d : Dart | d ∈ finalDartList L [r1, r2]} := hv
        rw [hfdEq] at h0
        exact h0
      -- S = {w | u 连通到 w}（X = darts_of_list L）= dart H
      have hS : {w : Dart | contourListConnected L {d : Dart | d ∈ listOfDarts L} u w}
          = ↑(hypermapOfList L hL).darts := by
        refine Kepler.Text.TameSpine.connectedInduction hconn ?_ ?_ ?_
        · intro w hw
          exact Finset.mem_coe.mpr
            (List.mem_toFinset.mpr (contourListConnectedMem hw).2.1)
        · exact ⟨u, contourListConnectedRefl huD huD⟩
        · intro x hx
          have hxD : x ∈ listOfDarts L := (contourListConnectedMem hx).2.1
          refine ⟨?_, ?_⟩
          · rw [Kepler.Text.TameLp.faceMap_hypermapOfList L hL
              (List.mem_toFinset.mpr hxD)]
            exact contourListConnectedFListRight hx
              (Kepler.Text.TameLp.fList_mem_darts hL.1 hxD)
          · rw [Kepler.Text.MoreLemma2Island3.inverseNodeMapList L hL hxD]
            exact contourListConnectedFeListRight hL hx
              (Kepler.Text.TameLp.fList_mem_darts hL.1 (hL.2.2 x hxD))
      have hvS : contourListConnected L {d : Dart | d ∈ listOfDarts L} u v := by
        have h0 : v ∈ (↑(hypermapOfList L hL).darts : Set Dart) :=
          Finset.mem_coe.mpr (List.mem_toFinset.mpr hvD)
        rw [← hS] at h0
        exact h0
      obtain ⟨s, hsne, hsH, hsL, hsC, hsSub⟩ := hvS
      refine ⟨s, hsC, hsne, hsH, hsL, ?_⟩
      intro x hx
      have hxD := hsSub hx
      rw [← hfdEq] at hxD
      exact hxD
    · -- ¬final_list L r2 支：u、v 同在 r1，final_list_connected 直收
      have hinr1 : ∀ x ∈ finalDartList L [r1, r2], x ∈ r1 := by
        intro x hx
        have hx' : x ∈ ([r1, r2].filter (fun r => decide (finalList L r))).flatten :=
          hx
        obtain ⟨r', hr', hxr'⟩ := List.mem_flatten.mp hx'
        obtain ⟨hr'N, hdec⟩ := List.mem_filter.mp hr'
        rcases List.mem_cons.mp hr'N with h | h
        · rw [← h]; exact hxr'
        · have hr'2 : r' = r2 := List.mem_singleton.mp h
          rw [hr'2] at hdec
          exact absurd (of_decide_eq_true hdec) hfin2
      obtain ⟨s, hsne, hsH, hsL, hsC, hsSub⟩ :=
        finalListConnected (hinr1 u hu) (hinr1 v hv) hr1N hfin1 hnl
      exact ⟨s, hsC, hsne, hsH, hsL, fun x hx => hr1fd x (hsSub hx)⟩
  · -- 合取 2：非终面 parts 末端的 e_list 落在终面 dart 表
    intro r' pp y hy hpp hr'N hnfin
    have hr'2 : r' = r2 := by
      rcases List.mem_cons.mp hr'N with h | h
      · rw [h] at hnfin
        exact absurd hfin1 hnfin
      · exact List.mem_singleton.mp h
    rw [hr'2] at hpp
    have hyL : y ∈ listPairs (List.range (Kepler.Graphs.maxGon p)).reverse := by
      rw [← hc2, Kepler.Text.TameSpine.listPairsCore L hL hnlS hend hall hr2N,
        ← Kepler.Text.ChainBridge.parts_eq_partsSpine]
      exact List.mem_map.mpr ⟨pp, hpp,
        (Kepler.Text.ChainBridge.getLast!_eq_getLastD pp).trans hy.symm⟩
    have hey : eList y ∈ listPairs (List.range (Kepler.Graphs.maxGon p)) := by
      obtain ⟨i, j⟩ := y
      rw [Kepler.Text.TameSpine.memListPairsRevIota hkpos] at hyL
      show (j, i) ∈ listPairs (List.range (Kepler.Graphs.maxGon p))
      rw [Kepler.Text.TameSpine.memListPairsIota]
      omega
    exact hr1fd _ (hcoreMem r1 hr1N _ (by rw [hc1]; exact hey))

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.allFinalListDart
#print axioms Kepler.Text.Reduction1.flagListSeed

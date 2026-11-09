/-
  Kepler.Text.TameSpine.JcajyduRxBridge — jcajydu-rxbridge 波：`rxNumTransport`
  跨型桥填证（J 战役独立批；消费方 `JcajyduShell.rxNumTransport` 槽，壳已落库
  `0c520618`，本模块不改其任何声明）。

  ┌─ 交付内容 ────────────────────────────────────────────────────
  │ 深侦结论（DELIVERY §1）：桥 = HOL 壳证明 JCAJYDU.hl:55-73 跨型段
  │ （JXBJOAB 编码 + iso_list_good_list / iso_list_good_list_nodes +
  │ GNBEVVU=hypermap_of_list_map）的 rx 层泛型化，不依赖 reduction 链。
  │ 树内状态：MAP MAP φ 运输族只有 ℕ 单态形（TameLp la7_*，TameList1 §2）；
  │ 泛型 rx 词表（TameList65-69）与泛型序列件（la7_prevEl_map/la7_nextEl_map/
  │ la7_listPairs_map/la7_nodup_map_on，TameLp §10 全泛型 α→β）已就位。
  │ 本模块：编码件 + 泛型运输族 + nodeSet 轨道像运输 + num 侧折算 + 桥本体。
  └────────────────────────────────────────────────────────────────

  ┌─ HOL 对照表（tame_list.hl）───────────────────────────────────
  │ INJ_NUM_EXISTS   :3719 → injNumExists（TameList5:213，已移植，本模块只装配）
  │ JXBJOAB          :3733 → §1 rxEncodeExists（顶点集 ℕ 编码）
  │ map_list_of_darts:3435 → §2 rxListOfDartsMap
  │ map_good_list    :3403 → §2 rxMapGoodList
  │ find_face_map    :3450 → §2 rxFindFaceMap
  │ hypermap_of_list_map :3486 → §2 rxHypermapListOfListMap（列表层）+
  │                              rxHypermapOfListGIsoMap（Hypermap.Iso 形）
  │ iso_list_good_list_nodes :3570 → §3/§4 nodeSet 轨道像链
  │   （HOL 走 iso_number_of_nodes 计数；Lean 树 GoodListNodes 是集合等式 def，
  │   本模块走 iso_node_set 轨道像形 = TameList69:455-505 RxOkData 件的泛型化，
  │   与 TameList15 私件 isoNodeSetImage 同构，公理面相同）
  └────────────────────────────────────────────────────────────────

  ┌─ 环安全 ──────────────────────────────────────────────────────
  │ imports = JcajyduShell（rxNumTransport 槽 + rx 词表 + hypermapOfListG）
  │ + TameList5（injNumExists）+ TameLp（hypermapOfList/nodesOfListSet/泛型
  │ la7 序列件）。闭包零 `Kepler.Assembly` 主模块（GoodList 经
  │ GoodListDefs 非环底座，P6-C 设计）。无 axiom/sorry/native_decide；
  │ 不改既有陈述；主仓 tracked 零改动。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.JcajyduShell
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Text (Hypermap)
open Kepler.Graphs (fgraph)
open Kepler.Assembly (listPairs listOfDarts GoodList)
open Kepler.Text.TameLp
  (hypermapOfList nodesOfListSet listOfElements darts_hypermapOfList
    nodeMap_hypermapOfList la7_listPairs_map la7_nodup_map_on la7_prevEl_map
    la7_nextEl_map)
open Kepler.Text.TameCorrList (GoodListNodes)

/-! ## §1 编码层（HOL JXBJOAB :3733 的前件；内容 = INJ_NUM_EXISTS :3719 装配） -/

/-- `rxElementsOfList L` 有限（`rxListOfElements = L.flatten.dedup` 的像集；
HOL `FINITE_SET_OF_LIST` 段，JXBJOAB :3736 消费形）。 -/
theorem rxElementsOfListFinite {α : Type*} [DecidableEq α] (L : List (List α)) :
    (rxElementsOfList L).Finite :=
  Set.Finite.ofFinset L.flatten.dedup.toFinset
    (fun x => List.mem_toFinset.trans Iff.rfl)

/-- flatten 成员 → 顶点集成员（`rxElementsOfList = {x | x ∈ L.flatten.dedup}`）。 -/
theorem memRxElementsOfList_of_mem_flatten {α : Type*} [DecidableEq α]
    {L : List (List α)} {u : α} (hu : u ∈ L.flatten) : u ∈ rxElementsOfList L :=
  List.mem_dedup.mpr hu

/-- 顶点集成员 → flatten 成员（对偶向）。 -/
theorem mem_flatten_of_memRxElementsOfList {α : Type*} [DecidableEq α]
    {L : List (List α)} {u : α} (hu : u ∈ rxElementsOfList L) : u ∈ L.flatten := by
  have hu' : u ∈ (L.flatten.dedup : List α) := hu
  exact List.mem_dedup.mp hu'

/-- **HOL `JXBJOAB` 前件**（tame_list.hl:3733-3744 `?j. inj_on j (elements_of_list L)`
段；内容 = `injNumExists`（TameList5:213 = INJ_NUM_EXISTS :3719 移植）实例化）。 -/
theorem rxEncodeExists {α : Type*} [DecidableEq α] (L : List (List α)) :
    ∃ φ : α → ℕ, Set.InjOn φ (rxElementsOfList L) :=
  injNumExists (rxElementsOfListFinite L)

/-! ## §2 MAP (MAP φ) 运输族（HOL :3403/:3435/:3450/:3486 泛型化；
ℕ 单态先例 = TameLp la7_* / TameList1 §2，本节把顶层 α 钉死 ℕ 的证明逐字泛化） -/

/-- dart 表成员的面分解（`rxListOfDarts = (L.map listPairs).flatten`）。 -/
theorem memRxListOfDarts_iff {α : Type*} {L : List (List α)} {d : α × α} :
    d ∈ rxListOfDarts L ↔ ∃ l ∈ L, d ∈ listPairs l := by
  constructor
  · intro hm
    obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hm
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    exact ⟨l', hl', hdl⟩
  · rintro ⟨l, hl, hdl⟩
    exact List.mem_flatten.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩, hdl⟩

/-- HOL `map_list_of_darts`（tame_list.hl:3435-3440）泛型形
（ℕ 先例 `la7_listOfDarts_map` TameLp:5724，本体逐字）。 -/
theorem rxListOfDartsMap {α β : Type*} (φ : α → β) (L : List (List α)) :
    rxListOfDarts (L.map (List.map φ))
      = (rxListOfDarts L).map (fun d : α × α => (φ d.1, φ d.2)) := by
  show ((L.map (List.map φ)).map listPairs).flatten
    = ((L.map listPairs).flatten).map (fun d : α × α => (φ d.1, φ d.2))
  rw [List.map_map,
    List.map_congr_left (f := listPairs ∘ List.map φ)
      (g := fun l => (listPairs l).map (fun d : α × α => (φ d.1, φ d.2)))
      (fun l _ => la7_listPairs_map φ l)]
  show List.flatMap (fun l => (listPairs l).map (fun d : α × α => (φ d.1, φ d.2))) L
    = List.map (fun d : α × α => (φ d.1, φ d.2)) (List.flatMap listPairs L)
  rw [List.map_flatMap]

/-- HOL `inj_on_dart_of_list`（tame_list.hl:3746-3756）内容件：pair-lift 在
dart 表上单射（ℕ 先例 `la7_injOn_listOfDarts` TameLp:5738，本体逐字）。 -/
theorem rxInjOnListOfDarts {α β : Type*} {L : List (List α)} {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v)
    (d e : α × α) (hd : d ∈ rxListOfDarts L) (he : e ∈ rxListOfDarts L)
    (h : (φ d.1, φ d.2) = (φ e.1, φ e.2)) : d = e := by
  have h1 : φ d.1 = φ e.1 := congrArg Prod.fst h
  have h2 : φ d.2 = φ e.2 := congrArg Prod.snd h
  obtain ⟨l, hl, hdl⟩ := memRxListOfDarts_iff.mp hd
  obtain ⟨m, hm, hem⟩ := memRxListOfDarts_iff.mp he
  have hd1 : d.1 ∈ l ∧ d.2 ∈ l.drop 1 ++ l.take 1 :=
    List.of_mem_zip (show (d.1, d.2) ∈ l.zip (l.drop 1 ++ l.take 1) from hdl)
  have he1 : e.1 ∈ m ∧ e.2 ∈ m.drop 1 ++ m.take 1 :=
    List.of_mem_zip (show (e.1, e.2) ∈ m.zip (m.drop 1 ++ m.take 1) from hem)
  have hd2 : d.2 ∈ l := by
    rcases List.mem_append.mp hd1.2 with h | h
    · exact List.drop_subset 1 l h
    · exact List.take_subset 1 l h
  have he2 : e.2 ∈ m := by
    rcases List.mem_append.mp he1.2 with h | h
    · exact List.drop_subset 1 m h
    · exact List.take_subset 1 m h
  have h11 : d.1 = e.1 :=
    hinj d.1 (List.mem_flatten.mpr ⟨l, hl, hd1.1⟩) e.1
      (List.mem_flatten.mpr ⟨m, hm, he1.1⟩) h1
  have h12 : d.2 = e.2 :=
    hinj d.2 (List.mem_flatten.mpr ⟨l, hl, hd2⟩) e.2
      (List.mem_flatten.mpr ⟨m, hm, he2⟩) h2
  show Prod.mk d.1 d.2 = Prod.mk e.1 e.2
  rw [h11, h12]

/-- HOL `map_good_list`（tame_list.hl:3403-3407）泛型形：
`good_list L ∧ inj_on φ (elements_of_list L) → good_list (MAP (MAP φ) L)`
（ℕ 先例 `la7_mapGoodList` TameLp:5770，本体逐字；iso_list_good_list :3554
的 unwrap 后本体）。 -/
theorem rxMapGoodList {α β : Type*} {L : List (List α)} {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v)
    (hgood : rxGoodList L) : rxGoodList (L.map (List.map φ)) := by
  obtain ⟨hnd, hne, hswap⟩ := hgood
  refine ⟨?_, ?_, ?_⟩
  · rw [rxListOfDartsMap]
    exact la7_nodup_map_on (f := fun d : α × α => (φ d.1, φ d.2))
      (fun u hu v hv huv => rxInjOnListOfDarts hinj u v hu hv huv) hnd
  · intro l hl
    obtain ⟨m, hm, hme⟩ := List.mem_map.mp hl
    rw [← hme]
    intro hc
    exact hne m hm (List.map_eq_nil_iff.mp hc)
  · intro d hd
    rw [rxListOfDartsMap, List.mem_map] at hd
    obtain ⟨c, hc, hcd⟩ := hd
    rw [← hcd, rxListOfDartsMap, List.mem_map]
    exact ⟨(c.2, c.1), hswap c hc, rfl⟩

/-- HOL `find_face_map`（tame_list.hl:3450-3454）泛型形：
`find_face (MAP (MAP φ) L) (φ p1, φ p2) = MAP (\d. φ(FST d),φ(SND d))
(find_face L (p1,p2))`（ℕ 先例 `la7_findFace_map` TameLp:5867，本体逐字）。
HOL 消费 GNBEVVU 的 node/face 交换义务全经此件。 -/
theorem rxFindFaceMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    {L : List (List α)} {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v)
    (d : α × α) (hd : d ∈ rxListOfDarts L) :
    rxFindFace (L.map (List.map φ)) (φ d.1, φ d.2)
      = (rxFindFace L d).map (fun x : α × α => (φ x.1, φ x.2)) := by
  have hdm : d.1 ∈ L.flatten ∧ d.2 ∈ L.flatten := by
    obtain ⟨l, hl, hdl⟩ := memRxListOfDarts_iff.mp hd
    have h1 : d.1 ∈ l ∧ d.2 ∈ l.drop 1 ++ l.take 1 :=
      List.of_mem_zip (show (d.1, d.2) ∈ l.zip (l.drop 1 ++ l.take 1) from hdl)
    refine ⟨List.mem_flatten.mpr ⟨l, hl, h1.1⟩, ?_⟩
    rcases List.mem_append.mp h1.2 with h | h
    · exact List.mem_flatten.mpr ⟨l, hl, List.drop_subset 1 l h⟩
    · exact List.mem_flatten.mpr ⟨l, hl, List.take_subset 1 l h⟩
  unfold rxFindFace
  rw [List.find?_map]
  show listPairs ((Option.map (List.map φ)
    (L.find? (fun l => decide ((φ d.1, φ d.2) ∈ listPairs (l.map φ))))).getD [])
    = (rxFindFace L d).map (fun x : α × α => (φ x.1, φ x.2))
  have hpred : ∀ l ∈ L, decide ((φ d.1, φ d.2) ∈ listPairs (l.map φ))
      = decide (d ∈ listPairs l) := by
    intro l hl
    have hstep : (φ d.1, φ d.2) ∈ listPairs (l.map φ) ↔ d ∈ listPairs l := by
      rw [la7_listPairs_map, List.mem_map]
      constructor
      · rintro ⟨c, hc, hcd⟩
        have h1 : φ c.1 = φ d.1 := congrArg Prod.fst hcd
        have h2 : φ c.2 = φ d.2 := congrArg Prod.snd hcd
        have hc1 : c.1 ∈ l ∧ c.2 ∈ l.drop 1 ++ l.take 1 := List.of_mem_zip hc
        have hc2 : c.2 ∈ l := by
          rcases List.mem_append.mp hc1.2 with h | h
          · exact List.drop_subset 1 l h
          · exact List.take_subset 1 l h
        have h11 : c.1 = d.1 :=
          hinj c.1 (List.mem_flatten.mpr ⟨l, hl, hc1.1⟩) d.1 hdm.1 h1
        have h12 : c.2 = d.2 :=
          hinj c.2 (List.mem_flatten.mpr ⟨l, hl, hc2⟩) d.2 hdm.2 h2
        have hcd' : c = d := by
          show Prod.mk c.1 c.2 = Prod.mk d.1 d.2
          rw [h11, h12]
        rw [← hcd']
        exact hc
      · rintro hmem
        exact ⟨d, hmem, rfl⟩
    exact Bool.decide_congr hstep
  rw [List.find?_congr hpred]
  cases hf : List.find? (fun l => decide (d ∈ listPairs l)) L with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hf
    obtain ⟨l, hl, hdl⟩ := memRxListOfDarts_iff.mp hd
    exact hnone l hl (decide_eq_true hdl)
  | some m =>
    have hFF : rxFindFace L d = listPairs m := by
      show listPairs ((L.find? (fun l => decide (d ∈ listPairs l))).getD [])
        = listPairs m
      rw [hf]
      rfl
    rw [hFF]
    exact la7_listPairs_map φ m

/-- HOL `hypermap_of_list_map` 列表层核心（tame_list.hl:3493 hyp-iso 形；
ℕ 先例 `la7_hypermapOfList_map` TameLp:6065，本体逐字，e-交换支由
pair-swap 自逆 rfl 内联）。 -/
theorem rxHypermapListOfListMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    {L : List (List α)} {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v)
    (hgood : rxGoodList L) :
    Set.BijOn (fun d : α × α => (φ d.1, φ d.2)) {d | d ∈ rxListOfDarts L}
      {d | d ∈ rxListOfDarts (L.map (List.map φ))}
    ∧ ∀ d ∈ rxListOfDarts L,
        rxNList (L.map (List.map φ)) (φ d.1, φ d.2)
          = (φ (rxNList L d).1, φ (rxNList L d).2)
        ∧ rxFList (L.map (List.map φ)) (φ d.1, φ d.2)
          = (φ (rxFList L d).1, φ (rxFList L d).2) := by
  refine ⟨?_, fun d hd => ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [rxListOfDartsMap]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · intro x hx y hy hxy
      exact rxInjOnListOfDarts hinj x y hx hy hxy
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy
      rw [rxListOfDartsMap, List.mem_map] at hy
      obtain ⟨c, hc, hcd⟩ := hy
      exact ⟨c, hc, hcd⟩
  · have hFF := rxFindFaceMap hinj d hd
    have hinjF : ∀ u ∈ rxFindFace L d, ∀ v ∈ rxFindFace L d,
        (φ u.1, φ u.2) = (φ v.1, φ v.2) → u = v :=
      fun u hu v hv huv =>
        rxInjOnListOfDarts hinj u v (rxMemDarts_of_mem_rxFindFace hu)
          (rxMemDarts_of_mem_rxFindFace hv) huv
    have hFd : d ∈ rxFindFace L d := (rxDartInFindFace L d).mpr hd
    refine ⟨?_, ?_⟩
    · unfold rxNList
      rw [hFF, la7_prevEl_map (f := fun x : α × α => (φ x.1, φ x.2)) hinjF hFd]
      rfl
    · unfold rxFList
      rw [hFF, la7_nextEl_map (f := fun x : α × α => (φ x.1, φ x.2)) hinjF hFd]

/-- HOL `hypermap_of_list_map`（tame_list.hl:3486-3488）rx 层 Hypermap.Iso 形：
`iso (hypermap_of_list L) (hypermap_of_list (MAP (MAP φ) L))`（ℕ 先例
`hypermapOfList_iso_map` TameLp:6218，本体逐字；四槽 = TameList67
darts/edgeMap/nodeMap/faceMap_hypermapOfListG）。 -/
theorem rxHypermapOfListGIsoMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    {L : List (List α)} {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v)
    (hgood : rxGoodList L) :
    Hypermap.Iso (hypermapOfListG L hgood)
      (hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)) := by
  have hbij := (rxHypermapListOfListMap hinj hgood).1
  have hmaps := (rxHypermapListOfListMap hinj hgood).2
  have hbij' : Set.BijOn (fun d : α × α => (φ d.1, φ d.2))
      (↑(hypermapOfListG L hgood).darts : Set (α × α))
      (↑(hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)).darts :
        Set (β × β)) := by
    rw [darts_hypermapOfListG L hgood,
      darts_hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)]
    exact hbij
  refine ⟨fun d => (φ d.1, φ d.2), hbij', fun d hd => ?_⟩
  have hd2 : (φ d.1, φ d.2) ∈
      (hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)).darts :=
    hbij'.1 hd
  have hds : d ∈ {e : α × α | e ∈ rxListOfDarts L} := by
    have h4 : d ∈ (↑(hypermapOfListG L hgood).darts : Set (α × α)) := hd
    rw [darts_hypermapOfListG] at h4
    exact h4
  obtain ⟨hn, hf⟩ := hmaps d hds
  refine ⟨?_, ?_, ?_⟩
  · show (hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)).edgeMap
        (φ d.1, φ d.2) = (φ ((hypermapOfListG L hgood).edgeMap d).1,
          φ ((hypermapOfListG L hgood).edgeMap d).2)
    rw [edgeMap_hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood) hd2,
      edgeMap_hypermapOfListG L hgood hd]
    rfl
  · show (hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)).nodeMap
        (φ d.1, φ d.2) = (φ ((hypermapOfListG L hgood).nodeMap d).1,
          φ ((hypermapOfListG L hgood).nodeMap d).2)
    rw [nodeMap_hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood) hd2,
      nodeMap_hypermapOfListG L hgood hd]
    exact hn
  · show (hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood)).faceMap
        (φ d.1, φ d.2) = (φ ((hypermapOfListG L hgood).faceMap d).1,
          φ ((hypermapOfListG L hgood).faceMap d).2)
    rw [faceMap_hypermapOfListG (L.map (List.map φ)) (rxMapGoodList hinj hgood) hd2,
      faceMap_hypermapOfListG L hgood hd]
    exact hf

/-! ## §3 nodeSet 轨道像运输（HOL iso_list_good_list_nodes :3570 的
iso_node_set 段；TameList69:455-505 RxOkData 件的泛型形，本体逐字；
TameList15 私件 isoNodeSetImage 同构件零共享，本节独立落地） -/

/-- iso 共轭下的 nodeMap 幂交换（TameList69 `isoMap_node_pow` 泛型形）。 -/
theorem isoNodePowComm {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hcomm : ∀ x ∈ H.darts, G.nodeMap (f x) = f (H.nodeMap x)) (k : ℕ) {z : α}
    (hz : z ∈ H.darts) : (G.nodeMap ^ k) (f z) = f ((H.nodeMap ^ k) z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    have hz' : (H.nodeMap ^ k) z ∈ H.darts := H.nodeMap_permutes.pow_apply_mem k hz
    rw [hcomm _ hz']
    congr 1
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- 节点轨道在 iso 下的像（TameList69 `orbit_iso` 泛型形；
HOL :728-:761 set_of_orbits 转移步）。 -/
theorem isoNodeOrbitImage {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hcomm : ∀ x ∈ H.darts, G.nodeMap (f x) = f (H.nodeMap x)) {z : α}
    (hz : z ∈ H.darts) :
    orbitMap G.nodeMap (f z) = f '' orbitMap H.nodeMap z := by
  ext w
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(H.nodeMap ^ k) z, ⟨k, rfl⟩, (isoNodePowComm hcomm k hz).symm.trans hk⟩
  · rintro ⟨v, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, isoNodePowComm hcomm k hz⟩

/-- **HOL `iso_node_set`**（hypermap_iso.vhl:487；TameList15 私件
isoNodeSetImage 的非私有泛型形）：
node 轨道族沿 iso 共轭搬运为像族。 -/
theorem isoNodeSetImageGen {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hcomm : ∀ x ∈ H.darts, G.nodeMap (f x) = f (H.nodeMap x))
    (hbij : Set.BijOn f (↑H.darts) (↑G.darts)) :
    G.nodeSet = (fun s : Set α => f '' s) '' H.nodeSet := by
  ext N
  constructor
  · intro hN
    simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq] at hN
    obtain ⟨d, hd, rfl⟩ := hN
    obtain ⟨z, hz, hzd⟩ := hbij.2.2 hd
    refine ⟨orbitMap H.nodeMap z, ⟨z, hz, rfl⟩, ?_⟩
    rw [← hzd]
    show f '' orbitMap H.nodeMap z = orbitMap G.nodeMap (f z)
    exact (isoNodeOrbitImage hcomm hz).symm
  · rintro ⟨S, hS, rfl⟩
    simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq] at hS
    obtain ⟨x, hx, hSx⟩ := hS
    refine ⟨f x, hbij.1 hx, ?_⟩
    rw [isoNodeOrbitImage hcomm hx, hSx]

/-! ## §4 纤维集运输与 num 侧折算（iso_list_good_list_nodes :3570 的
list_of_elements/size 段集合形 + dedup/eraseDups 索引折算） -/

/-- 节点纤维沿 pair-lift 的像（iso_list_good_list_nodes 的纤维转移内容）。 -/
private theorem rxFiberMap {α β : Type*} [DecidableEq α] {L : List (List α)}
    {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v) (x : α)
    (hx : x ∈ rxElementsOfList L) :
    {d : β × β | d ∈ rxListOfDarts (L.map (List.map φ)) ∧ d.1 = φ x}
      = (fun d : α × α => (φ d.1, φ d.2)) ''
        {d : α × α | d ∈ rxListOfDarts L ∧ d.1 = x} := by
  ext d'
  constructor
  · rintro ⟨hd', h1⟩
    rw [rxListOfDartsMap, List.mem_map] at hd'
    obtain ⟨d, hdmem, rfl⟩ := hd'
    have hd1x : d.1 ∈ L.flatten := by
      obtain ⟨l, hl, hdl⟩ := memRxListOfDarts_iff.mp hdmem
      have hz : d.1 ∈ l :=
        (List.of_mem_zip (show (d.1, d.2) ∈ l.zip (l.drop 1 ++ l.take 1)
          from hdl)).1
      exact List.mem_flatten.mpr ⟨l, hl, hz⟩
    have heq : φ d.1 = φ x := by simpa using h1
    exact ⟨d, ⟨hdmem, hinj d.1 hd1x x (mem_flatten_of_memRxElementsOfList hx) heq⟩,
      rfl⟩
  · rintro ⟨d, ⟨hdmem, hd1⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show (φ d.1, φ d.2) ∈ rxListOfDarts (L.map (List.map φ))
      rw [rxListOfDartsMap]
      exact List.mem_map.mpr ⟨d, hdmem, rfl⟩
    · show (φ d.1, φ d.2).1 = φ x
      rw [hd1]

/-- HOL `map_good_list_nodes` 的集合形（iso_list_good_list_nodes :3570 内容）：
`rxNodesOfListSet (MAP (MAP φ) L) = (\S. pair-lift '' S) '' rxNodesOfListSet L`。 -/
theorem rxNodesOfListSetMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    {L : List (List α)} {φ : α → β}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v) :
    rxNodesOfListSet (L.map (List.map φ))
      = (fun S : Set (α × α) => (fun d : α × α => (φ d.1, φ d.2)) '' S) ''
        rxNodesOfListSet L := by
  show (fun x : β => {d : β × β | d ∈ rxListOfDarts (L.map (List.map φ)) ∧ d.1 = x})
      '' rxElementsOfList (L.map (List.map φ))
    = (fun S : Set (α × α) => (fun d : α × α => (φ d.1, φ d.2)) '' S) ''
      ((fun x : α => {d : α × α | d ∈ rxListOfDarts L ∧ d.1 = x}) '' rxElementsOfList L)
  have hE : rxElementsOfList (L.map (List.map φ))
      = (fun u : α => φ u) '' rxElementsOfList L := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (L.map (List.map φ)).flatten :=
        mem_flatten_of_memRxElementsOfList hx
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
      obtain ⟨v, hv, hxv⟩ := List.mem_map.mp hxl
      exact ⟨v, memRxElementsOfList_of_mem_flatten
        (List.mem_flatten.mpr ⟨a, ha, hv⟩), hxv⟩
    · rintro ⟨u, hu, rfl⟩
      have huF : u ∈ L.flatten := mem_flatten_of_memRxElementsOfList hu
      obtain ⟨l, hl, hul⟩ := List.mem_flatten.mp huF
      exact memRxElementsOfList_of_mem_flatten
        (List.mem_flatten.mpr ⟨List.map φ l, List.mem_map_of_mem hl,
          List.mem_map_of_mem hul⟩)
  rw [hE, ← Set.image_comp, Set.image_image]
  exact Set.image_congr
    (fun x hx => rxFiberMap hinj x hx)

/-- `rxNodesOfListSet` 与 TameLp `nodesOfListSet` 在 α = ℕ 的折算：
纤维函数同体（rxListOfDarts = listOfDarts 逐字同体），索引集
`flatten.dedup` vs `flatten.eraseDups` 同元素（`List.mem_eraseDups`）。 -/
theorem rxNodesOfListSetEq (Ln : fgraph ℕ) :
    rxNodesOfListSet Ln = nodesOfListSet Ln := by
  unfold rxNodesOfListSet nodesOfListSet
  have hfun : (fun x : ℕ => {d : ℕ × ℕ | d ∈ rxListOfDarts Ln ∧ d.1 = x})
      = (fun x : ℕ => {d : ℕ × ℕ | d ∈ listOfDarts Ln ∧ d.1 = x}) := rfl
  have hset : rxElementsOfList Ln = {x | x ∈ listOfElements Ln} := by
    ext x
    show x ∈ (Ln.flatten.dedup : List ℕ) ↔ x ∈ Ln.flatten.eraseDups
    rw [List.mem_dedup, List.mem_eraseDups]
  rw [hfun, hset]

/-- `hypermapOfList` 的 GoodList 见证无关性（构造的四映射字段经 extendPerm
只依赖 dart 表与序列函数，见证差全在证明字段，proof irrelevance 吸收）。 -/
theorem hypermapOfListNodeSetCongr {Ln : fgraph ℕ} (h1 h2 : GoodList Ln) :
    (hypermapOfList Ln h1).nodeSet = (hypermapOfList Ln h2).nodeSet := rfl

/-! ## §5 桥本体（JCAJYDU.hl:55-73 跨型段打包 = `rxNumTransport` 填证） -/

/-- **`rxNumTransport` 填证**（J 战役缺口件，c1 DELIVERY §5-UNRESOLVED-1）：
HOL 壳证明 JCAJYDU.hl:57-73 四件（JXBJOAB 编码 + iso_list_good_list +
iso_list_good_list_nodes + GNBEVVU）的 rx 层跨型打包。路线：`injNumExists`
取顶点编码 φ，`Ln := MAP (MAP φ) L`，GoodList/GoodListNodes/Iso 三槽分别经
§2 运输族、§3/§4 轨道像链（hgn 供 nodeSet 侧义务）与 rxHypermapOfListGIsoMap
供给。零 reduction 链依赖。 -/
theorem rxNumTransportBridge {α : Type*} [DecidableEq α] : rxNumTransport α := by
  intro L hL hgn
  obtain ⟨φ, hinj⟩ := rxEncodeExists L
  have hinj' : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v :=
    fun u hu v hv huv =>
      hinj (memRxElementsOfList_of_mem_flatten hu)
        (memRxElementsOfList_of_mem_flatten hv) huv
  refine ⟨L.map (List.map φ), rxMapGoodList hinj' hL, ?_,
    rxHypermapOfListGIsoMap hinj' hL⟩
  intro hLn'
  rw [hypermapOfListNodeSetCongr hLn' (rxMapGoodList hinj' hL)]
  have hgnEq : (hypermapOfListG L hL).nodeSet = rxNodesOfListSet L := hgn
  have hbijN : Set.BijOn (fun d : Set α × Set α => (φ d.1, φ d.2))
      (↑(hypermapOfListG L hL).darts : Set (Set α × Set α))
      (↑(hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)).darts :
        Set (ℕ × ℕ)) := by
    rw [darts_hypermapOfListG L hL,
      darts_hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)]
    exact (rxHypermapListOfListMap hinj' hL).1
  have hcommN : ∀ x ∈ (hypermapOfListG L hL).darts,
      (hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)).nodeMap
        (φ x.1, φ x.2)
        = (φ ((hypermapOfListG L hL).nodeMap x).1,
          φ ((hypermapOfListG L hL).nodeMap x).2) := by
    intro x hx
    have hxd : x ∈ rxListOfDarts L := by
      have h5 : x ∈ (↑(hypermapOfListG L hL).darts : Set (Set α × Set α)) := hx
      rw [darts_hypermapOfListG] at h5
      exact h5
    have hx2 : (φ x.1, φ x.2) ∈
        (hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)).darts := by
      have h6 : (φ x.1, φ x.2) ∈
          (↑(hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)).darts :
            Set (ℕ × ℕ)) := by
        rw [darts_hypermapOfList]
        show (φ x.1, φ x.2) ∈ {d | d ∈ rxListOfDarts (L.map (List.map φ))}
        rw [rxListOfDartsMap]
        exact List.mem_map.mpr ⟨x, hxd, rfl⟩
      exact h6
    show (hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)).nodeMap
        (φ x.1, φ x.2)
      = (φ ((hypermapOfListG L hL).nodeMap x).1,
        φ ((hypermapOfListG L hL).nodeMap x).2)
    rw [nodeMap_hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL) hx2,
      nodeMap_hypermapOfListG L hL hx]
    exact (rxHypermapListOfListMap hinj' hL).2 x hxd |>.1
  calc (hypermapOfList (L.map (List.map φ)) (rxMapGoodList hinj' hL)).nodeSet
      = (fun S : Set (Set α × Set α) =>
          (fun d : Set α × Set α => (φ d.1, φ d.2)) '' S) ''
        (hypermapOfListG L hL).nodeSet :=
      isoNodeSetImageGen hcommN hbijN
    _ = (fun S : Set (Set α × Set α) =>
          (fun d : Set α × Set α => (φ d.1, φ d.2)) '' S) '' rxNodesOfListSet L :=
      by rw [hgnEq]
    _ = rxNodesOfListSet (L.map (List.map φ)) := (rxNodesOfListSetMap hinj').symm
    _ = nodesOfListSet (L.map (List.map φ)) := rxNodesOfListSetEq _

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 `[propext, Classical.choice,
Quot.sound]`，零 sorryAx——桥为纯真证，槽消费零占位）。落库时编排者可整体
注释本节，不影响任何声明。 -/
#print axioms Kepler.Text.TameSpine.rxNumTransportBridge

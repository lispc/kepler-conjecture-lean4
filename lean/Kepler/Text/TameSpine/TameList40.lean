/-
  Kepler.Text.TameSpine.TameList40 — B1 Tame_list 地基批 40：parts 运输主件
  归纳主体（tamespine-port-plan §4 批次表 B1 行；接续批 39 =
  TameList39.lean，批 39 终点 = HOL :12106；本批起点 = HOL :12108
  `iso_list_parts`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12108-:12265）：

  主件：`iso_list_parts` :12108-:12238
  `!phi L N r. good_list L /\ normal_list L N /\
  is_edge_nondegenerate (hypermap_of_list L) /\ MEM r N /\
  flatten (parts L r) = r /\
  all (\x. MEM x (list_of_darts L)) r /\
  inj_on phi (elements_of_list L) ==>
  parts (MAP (MAP phi) L) (MAP nphi r) =
    MAP (MAP nphi) (parts L r)`（nphi = \u. phi (FST u), phi (SND u)）
  ↦ `isoListParts`（真证）。HOL 证体 parts_characterize 直取 + 五前提
  逐条：uniq 面经 inj_on_dart_of_list 的点式本体（批 2
  injOnLiftListOfDarts）在 r 上单向 + Seq.map_inj_in_uniq；flatten 面
  经 MAP_flatten（批 2 mapFlattenSpine ← 向）+ 前提 flatten (parts L r)
  = r 直回；all 面经 parts_all_nonnil + MAP 保非空；主前提逐件 (p, d)
  拆（p = MAP nphi q，d = nphi d0）：next_el 运输经 next_el_MEM_map
  （la7_nextEl_map）+ e_list 交换（批 5 eListFun）+ f_list_map（批 5
  fListMap，e_list d0 支经 good_list_e_list）+ LAST_MAP（批 5
  lastMapSpine + getLast! 两步私件桥），nphi 在 list_of_darts 上双向
  单射桥（EQ_EXPAND 面 = hiff）换面后按 d0 = LAST q 二分：
  = 支经 normal_list_parts_next_last_not（批 10；is_edge_nondegenerate
  在此实消费——非死前提）换面收口；≠ 支经 parts_next_unlast +
  next_el_parts_unlast（批 9 双件）反证。

  随收件：`iso_list_map_parts` :12239-:12265
  `!phi L N. good_list L /\ normal_list L N /\
  is_edge_nondegenerate (hypermap_of_list L) /\
  inj_on phi (elements_of_list L) ==> MAP (parts (MAP (MAP phi) L))
  (MAP (MAP nphi) N) = MAP (MAP (MAP nphi)) (MAP (parts L) N)`
  ↦ `isoListMapParts`（真证）。HOL 证体 GSYM MAP_o + MAP_EQ 逐点化后
  iso_list_parts 直取；Lean 面 List.map_map 双发（MAP_o 面）+
  List.map_congr_left 逐点（MAP_EQ 面）+ isoListParts 直取（flatten
  面 parts_flatten、darts 面 normal_list_list_of_darts 逐点供给）。

  载体折算盘点（批 39 头注预记侦察面，经全库 grep（含 LocalAuto 族）
  + TameList7/9 头注对拍——流程雷 #39 第四批实录：预记缺口全数在库，
  零新领土）：
  - `normal_list_uniq_nonnil` :4498 = 批 6 normalListUniqNonnil
    （TameList6.lean:630）；
  - `parts_characterize` :11946 = 批 39 partsCharacterize
    （TameList39.lean:161，直取）；
  - `inj_on_dart_of_list` :3746 = 批 5 injOnDartOfList
    （TameList5.lean:227；点式本体 = 批 2 injOnLiftListOfDarts，
    TameList2.lean:857）；
  - `lower_case`/`upper_case` :1397/:1401 = 重写包（Seq.map_MAP/
    last_LAST/APPEND_cat/ALL_all 核心件），批 31 已记档零镜像，
    Lean 面 core List 引理吸收；
  - `Seq.map_inj_in_uniq`（seq-compiled.hl:3135）= la7_nodup_map_on
    （TameLp.lean:4134）；
  - `MAP_flatten` :873 = 批 2 mapFlattenSpine（TameList2.lean:716）；
  - `next_el_MEM_map` :1011 = la7_nextEl_map（TameLp.lean:4376）；
  - `Seq2.mem_flatten`（seq2-compiled.hl:224）= Mathlib
    List.mem_flatten；
  - `parts_flatten` :6334 / `parts_all_nonnil` :6357 = 批 9
    partsFlatten（TameList9.lean:1063）/ partsAllNonnil（:1227）；
  - `parts_next_unlast` :6380 / `next_el_parts_unlast` :6490 = 批 9
    partsNextUnlast（TameList9.lean:1293）/ nextElPartsUnlast（:1368）；
  - `Seq2.mem_next_el`（seq2-compiled.hl:1754）= nextEl_mem_of_mem
    （TameLp.lean:3614）；
  - `e_list_fun` :3827 / `f_list_map` :3840 / `good_list_e_list` :3883
    = 批 5 eListFun（TameList5.lean:291）/ fListMap（:298）/
    goodListEList（:336）；
  - `LAST_MAP` :3975 = 批 5 lastMapSpine（TameList5.lean:386）；
  - `MEM_LAST` :1364 = 批 9/37/39 同证私件（本批复推 getLastMem''）；
  - `mem_f_list` :7255 = 批 10 memFList（TameList10.lean:835）；
  - `normal_list_parts_next_last_not` :7208 = 批 10
    normalListPartsNextLastNot（TameList10.lean:483）；
  - `normal_list_list_of_darts` :3643 = 批 5 normalListListOfDarts
    （TameList5.lean:146）；
  - `MAP_EQ`/`MAP_o` 面 = core List.map_congr_left/List.map_map。
  `is_edge_nondegenerate (hypermap_of_list L)` 前提按原文保留（Lean 面
  `(hypermapOfList L hL).EdgeNondegenerate`，批 10 同形），主件
  d0 = LAST q 支经 normalListPartsNextLastNot 实消费。parts_characterize
  主前提的 `~(d = LAST r)` 槽在 HOL iso_list_parts 证体内亦未显式
  消费（parts_characterize 前提面统一携带），Lean 同按原文保留
  （_hdne）。

  新落地载体：零（纯消费批）。私件（惯例同证重推导，非新领土）：
  getLast!_eq_getLast/getLastMem（批 37/9/39 同证，泛型 α 面）。

  诚实记账：主件 + 随收件全真证，零新 def、零 sorry、零止损件、
  零记账债。红线遵守：零既有文件触碰、零 git 写操作。
  批 41 接续点：HOL :12267 `iso_list_quotient`（quotient 章 iso_list
  面；需侦察 quotient_list/core_list（批 7 quotientListSpine/
  coreListSpine）、inj_on_quotient_list（批 37 injOnQuotientList）、
  parts_uniq_nonnil（批 9 partsUniqNonnil）+ 本批 isoListMapParts
  直取；其后 :12311 `isop_list_quotient` 同章随收候选）。
-/

import Kepler.Text.TameSpine.TameList39

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList GoodList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList elementsOfList)

/-! ### §1 私件（批 37/9/39 同证重推导，非新领土） -/

/-- 非空表 `getLast!` = `getLast`（批 37/39 私件同证重推导）。 -/
private theorem getLast!EqGetLast'' {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-- 非空表 `getLast!` 必是成员（批 9/37/39 私件同证重推导）。 -/
private theorem getLastMem'' {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rw [List.getLast!_cons_eq_getLastD]; exact List.getLastD_mem_cons

/-! ### §2 主件 iso_list_parts（tame_list.hl:12108-:12238） -/

/-- **HOL `iso_list_parts`**（tame_list.hl:12108-:12238）
`good_list L /\ normal_list L N /\ is_edge_nondegenerate
(hypermap_of_list L) /\ MEM r N /\ flatten (parts L r) = r /\
all (\x. MEM x (list_of_darts L)) r /\ inj_on phi (elements_of_list L)
==> parts (MAP (MAP phi) L) (MAP nphi r) = MAP (MAP nphi) (parts L r)`
——parts 章 iso_list 运输主件：parts_characterize（批 39）直取 + 五前提
逐条（uniq/flatten/all 面 + 主前提逐件 next_el/LAST 单射换面二分）。 -/
theorem isoListParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (phi : ℕ → ℕ) (hinj : Set.InjOn phi (elementsOfList L))
    {r : List (ℕ × ℕ)} (hr : r ∈ N)
    (hfl : (partsSpine L r).flatten = r)
    (hall : ∀ x ∈ r, x ∈ listOfDarts L) :
    partsSpine (L.map (List.map phi)) (r.map (fun u => (phi u.1, phi u.2)))
      = (partsSpine L r).map (fun p => p.map (fun u => (phi u.1, phi u.2))) := by
  obtain ⟨hunS, hneS⟩ := normalListUniqNonnil hn hr
  -- nphi 在 r 上的单向单射（inj_on_dart_of_list 点式本体）
  have hdinj : ∀ u ∈ r, ∀ v ∈ r,
      (phi u.1, phi u.2) = (phi v.1, phi v.2) → u = v :=
    fun u hu v hv huv => injOnLiftListOfDarts L hinj (hall u hu) (hall v hv) huv
  have hqne : ∀ q ∈ partsSpine L r, q ≠ [] := partsAllNonnil L hunS hneS
  have hqr : ∀ q ∈ partsSpine L r, ∀ x ∈ q, x ∈ r := by
    intro q hq x hx
    have hxm : x ∈ (partsSpine L r).flatten := List.mem_flatten.mpr ⟨q, hq, hx⟩
    rw [hfl] at hxm
    exact hxm
  -- LAST_MAP 面：getLast! 两步私件桥 + lastMapSpine（不赌 rfl）
  have hlastMap : ∀ q ∈ partsSpine L r,
      (q.map (fun u => (phi u.1, phi u.2))).getLast!
        = (phi q.getLast!.1, phi q.getLast!.2) := by
    intro q hq
    have hneQ : q ≠ [] := hqne q hq
    have hmapne : q.map (fun u => (phi u.1, phi u.2)) ≠ [] :=
      fun hc => hneQ (List.map_eq_nil_iff.mp hc)
    rw [getLast!EqGetLast'' hmapne, lastMapSpine _ hneQ, getLast!EqGetLast'' hneQ]
  -- nphi 在 list_of_darts L 上的双向单射桥（EQ_EXPAND 面）
  have hiff : ∀ u ∈ listOfDarts L, ∀ v ∈ listOfDarts L,
      (phi u.1, phi u.2) = (phi v.1, phi v.2) ↔ u = v :=
    fun u hu v hv =>
      ⟨injOnLiftListOfDarts L hinj hu hv, fun hc => by rw [hc]⟩
  -- parts_characterize 五前提
  have hneT : r.map (fun u => (phi u.1, phi u.2)) ≠ [] :=
    fun hc => hneS (List.map_eq_nil_iff.mp hc)
  have hunT : (r.map (fun u => (phi u.1, phi u.2))).Nodup :=
    Kepler.Text.TameLp.la7_nodup_map_on hdinj hunS
  have hflT : ((partsSpine L r).map (fun p => p.map (fun u => (phi u.1, phi u.2)))).flatten
      = r.map (fun u => (phi u.1, phi u.2)) := by
    rw [← mapFlattenSpine (f := fun u : ℕ × ℕ => (phi u.1, phi u.2)), hfl]
  have hallT : ∀ p ∈ (partsSpine L r).map (fun p => p.map (fun u => (phi u.1, phi u.2))),
      p ≠ [] := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    intro hc
    exact hqne q hq (List.map_eq_nil_iff.mp hc)
  refine partsCharacterize (L := L.map (List.map phi)) hneT hunT hflT hallT ?_
  -- 主前提：逐件 (p, d) 拆 + next_el/e_list/f_list 运输 + 二分
  intro p hp d hd _hdne
  rw [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [List.mem_map] at hd
  obtain ⟨d0, hd0, rfl⟩ := hd
  have hd0L : d0 ∈ listOfDarts L := hall d0 (hqr q hq d0 hd0)
  have hneQ : q ≠ [] := hqne q hq
  have hqlastD : q.getLast! ∈ listOfDarts L :=
    hall _ (hqr q hq _ (getLastMem'' hneQ))
  show nextEl (r.map (fun u => (phi u.1, phi u.2))) (phi d0.1, phi d0.2)
      ≠ fList (L.map (List.map phi)) (eList (phi d0.1, phi d0.2))
    ↔ (phi d0.1, phi d0.2) = (q.map (fun u => (phi u.1, phi u.2))).getLast!
  rw [Kepler.Text.TameLp.la7_nextEl_map hdinj (hqr q hq d0 hd0), eListFun phi d0,
    fListMap (hL := hL) hinj (goodListEList hL hd0L), hlastMap q hq,
    hiff _ hd0L _ hqlastD]
  by_cases hdLast : d0 = q.getLast!
  · -- d0 = LAST q 支：is_edge_nondegenerate 经 normal_list_parts_next_last_not 实消费
    have hN : nextEl r d0 ≠ fList L (eList d0) := by
      rw [hdLast]; exact normalListPartsNextLastNot L hL hn hnedg hr hq
    exact ⟨fun _ => hdLast, fun _hcon heq =>
      hN ((hiff _ (hall _ (Kepler.Text.TameLp.nextEl_mem_of_mem (hqr q hq d0 hd0)))
        _ (memFList L (goodListEList hL hd0L))).1 heq)⟩
  · -- d0 ≠ LAST q 支：parts_next_unlast + next_el_parts_unlast 反证
    refine ⟨fun hcon => ?_, fun hcon => (hdLast hcon).elim⟩
    have hqN := partsNextUnlast L hunS hneS q hq d0 hd0 hdLast
    have hrN := nextElPartsUnlast L hunS hneS hq hd0 hdLast
    exact absurd (by rw [hrN, hqN]) hcon

/-! ### §3 随收件 iso_list_map_parts（tame_list.hl:12239-:12265） -/

/-- **HOL `iso_list_map_parts`**（tame_list.hl:12239-:12265）
`good_list L /\ normal_list L N /\ is_edge_nondegenerate
(hypermap_of_list L) /\ inj_on phi (elements_of_list L) ==>
MAP (parts (MAP (MAP phi) L)) (MAP (MAP nphi) N) =
MAP (MAP (MAP nphi)) (MAP (parts L) N)`——MAP_EQ 逐点化后 iso_list_parts
直取（MAP_o 面 List.map_map 双发 + List.map_congr_left）。 -/
theorem isoListMapParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (phi : ℕ → ℕ) (hinj : Set.InjOn phi (elementsOfList L)) :
    (N.map (fun s => s.map (fun u => (phi u.1, phi u.2)))).map
        (partsSpine (L.map (List.map phi)))
      = (N.map (partsSpine L)).map
          (fun s => s.map (fun p => p.map (fun u => (phi u.1, phi u.2)))) := by
  have hpoint : ∀ r ∈ N,
      partsSpine (L.map (List.map phi)) (r.map (fun u => (phi u.1, phi u.2)))
        = (partsSpine L r).map (fun p => p.map (fun u => (phi u.1, phi u.2))) := by
    intro r hr
    exact isoListParts L hL hn hnedg phi hinj hr
      (partsFlatten L (normalListUniqNonnil hn hr).1 (normalListUniqNonnil hn hr).2)
      (fun x hx => normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hr, hx⟩))
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun r hr => hpoint r hr)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.isoListParts
#print axioms Kepler.Text.TameSpine.isoListMapParts
-/

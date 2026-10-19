/-
  Kepler.Text.TameSpine.TameList47 — B1 Tame_list 地基批 47：
  final_list_complete 运输面 + final_list 核心/商章（tamespine-port-plan
  §4 批次表 B1 行；接续批 46 = TameList46.lean，批 46 终点 = HOL
  :12758；本批起点 = HOL :12760 `final_list_complete`，随收
  :12786/:12802 core-quotient 面。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  载体折算盘点（批 46 尾处方预记对拍面，经主仓全库 grep（含
  LocalAuto 族）+ 工具链 core v4.32.2/mathlib/batteries 三处对拍
  复核）：**全族在册，零新 def，本批纯消费**：
  - `normal_list_complete`（:12723）= 批 46 normalListComplete
    （TameList46.lean:198，本批主件直投槽）；
  - `final_list`（tame_defs2.hl:138-:142：
    `final_list L r <=> all (\d. f_list L d = next_el r d) r`）= 批 7
    finalListSpine（TameList7.lean:481，定义形逐点 ∀∈，零展开步）；
  - `Seq2.mem_flatten`（seq2-compiled.hl:224）= core List.mem_flatten
    （批 40 头注已记档；flatten 谓词拆块 `∃ l, MEM l L ∧ MEM x l`
    两向 = .mp/.mpr）；
  - `Seq2.mem_next_el`（seq2-compiled.hl:1754）= TameLp
    nextEl_mem_of_mem（TameLp.lean:3614，S1HypermapOfList/GenericList
    节 `[BEq α] [LawfulBEq α] [DecidableEq α]` 槽，ℕ × ℕ 实例全备）；
  - `final_list_parts`（:11413-:11425）= 批 33 finalListParts
    （TameList33.lean:171，partsImpure + edgeNondegFXorNi 装配件，
    本批 final_list_core 第 1 槽直取——诚实记账：起笔首轮侦察
    grep 清点被 head 截断漏看此在册件，写件撞名报错逮住后改判
    纯消费；雷区记档：在册性清点必须无截断全量看）；
  - `parts_impure`（:11369-:11412）= 批 33 partsImpure
    （TameList33.lean:109）、`edge_nondeg_f_xor_ni`（:4933-:4944）
    = 批 8 edgeNondegFXorNi（TameList8.lean:368）——两件为
    finalListParts 的内部装配槽，本批不直接消费，记档备查；
  - `core`（tame_defs2.hl:130-:131）= 批 7 coreSpine
    （TameList7.lean:466）；`quotient_list`（:133-:134）= 批 7
    quotientListSpine（:476）；
  - `quotient_list_core`（:11576-:11591）= 批 34 quotientListCore
    （TameList34.lean:186，`quotientListSpine L N = N.map (coreSpine L)`，
    MAP (core L) 面 = N.map coreSpine 全形同构）；
  - `normal_list_list_of_darts`（:3643）= 批 5 normalListListOfDarts
    （TameList5.lean:146）；`normal_list_uniq_nonnil`（:4498）= 批 6
    normalListUniqNonnil（TameList6.lean:630）；
  - `MAP_EQ`/`MAP_o`/`MEM_MAP`/`HD` 面 = core List.map_congr_left/
    List.map_map/List.mem_map/List.head!（`[a].head!.1` 点式 defeq
    rfl 收口，批 34 quotientListCore 同款 show 换形先例）。
  全库 grep（含 LocalAuto 族 + core/mathlib/batteries 三处）
  finalListComplete/finalListCore/finalListQuotient 三件名零撞车
  零现成载体——镜像本体即本批件。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12760-:12830）：

  件一（本批主件）：`final_list_complete` :12760-:12784
  `!L N. good_list L /\ connected_hypermap (hypermap_of_list L) /\
  ~(N = []) /\ normal_list L N /\ all (final_list L) N ==>
  set_of_list (flatten N) = darts_of_list L` ↦ `finalListComplete`
  （真证）。normalListComplete 直投 + `all (final_list L) N` 谓词
  展开（↦ `∀ r ∈ N, finalListSpine L r`，Seq.allP 面零镜像）+
  Seq2.mem_flatten 拆块取内层面证人 l + finalListSpine 逐点回喂 +
  Seq2.mem_next_el（↦ nextEl_mem_of_mem）收 f_list ∈ l 支。与既有
  finalListSpine 槽对拍：批 43 isoListFinalListSpine/批 18
  MarkedListSpineFull 同款谓词形消费，零新增展开步。

  件二：`final_list_core` :12786-:12800
  `!L r. good_list L /\ all (\x. MEM x (list_of_darts L)) r /\
  is_edge_nondegenerate (hypermap_of_list L) /\ uniq r /\
  final_list L r ==> core L r = MAP FST r` ↦ `finalListCore`（真证）。
  coreSpine show 换形（批 34 同款）+ finalListParts（批 33）项式
  直投 + MAP_EQ 面 map_congr_left 逐点 rfl（`[a].head!.1 = a.1`
  defeq）。

  件三（章 capstone）：`final_list_quotient` :12802-:12830
  `!L N. good_list L /\ is_edge_nondegenerate (hypermap_of_list L) /\
  normal_list L N /\ all (final_list L) N ==> quotient_list L N =
  MAP (MAP FST) N` ↦ `finalListQuotient`（真证）。quotientListCore
  （批 34）换装 + MAP_EQ 面单层 map_congr_left：r ∈ N 槽
  finalListCore 直取（darts 支 = normalListListOfDarts +
  mem_flatten 组装、uniq 支 = normalListUniqNonnil 第 1 合取、
  final_list 支 = hfinal r hr）。

  新落地载体：零（全族 def 在批 7 coreSpine/partsSpine/
  quotientListSpine/finalListSpine 在册，装配槽全在批 5/6/8/33/34/
  46/TameLp 既有件——本批纯消费批）。私件：零。

  诚实记账：三件全真证，零新 def、零 sorry、零止损件、零记账债；
  起笔侦察一处纠错（finalListParts 在册漏看，撞名报错逮住，见
  载体盘点条目）如实入册。范围决策：批 47 射程收口至 :12830
  （final_list_complete 运输面 + core/quotient 面，自然边界 = rot
  章开章前）；:12831 `rot_final_list`（rot 旋转章开章，
  rot_final_list/ALL2_MEM/ALL2_rot_flatten/rot_eq_nil/loop_list_rot/
  normal_list_rot/all_final_list_rot/quotient_list_rot
  :12831-:12990；批 8 TameList8.lean:383 已有 rot/轨道词典块先例
  领土）留批 48。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 48 接续点：HOL :12831 `rot_final_list`（rot 章开章；先侦察批 8
  rot 词典块（rotateSpine 族）与 :12831-:12990 逐件对拍，其后
  :12991 ALL2_MAP2/:13001 normal_list_as_list_of_faces 同章随收候选）。
-/

import Kepler.Text.TameSpine.TameList46

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts fList)
open Kepler.Graphs (fgraph)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList nextEl_mem_of_mem)

/-! ### §1 final_list_complete（tame_list.hl:12760-:12784，本批主件） -/

/-- **HOL `final_list_complete`**（tame_list.hl:12760-:12784）
`!L N. good_list L /\ connected_hypermap (hypermap_of_list L) /\
~(N = []) /\ normal_list L N /\ all (final_list L) N ==>
set_of_list (flatten N) = darts_of_list L`——normalListComplete
（批 46 capstone）直投；`all (final_list L) N` 谓词展开 ↦
`∀ r ∈ N, finalListSpine L r`（Seq.allP 面零镜像）；f_list 运输支：
Seq2.mem_flatten（↦ core List.mem_flatten）拆块取内层面证人 l，
finalListSpine L l 逐点回喂 `f_list L x = next_el l x`，
Seq2.mem_next_el（↦ nextEl_mem_of_mem，TameLp:3614）收口
`next_el l x ∈ l ⊆ flatten N`。 -/
theorem finalListComplete {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (hconn : (hypermapOfList L hL).Connected)
    (hne : N ≠ []) (hnorm : NormalListSpine hL N)
    (hfinal : ∀ r ∈ N, finalListSpine L r) :
    {d | d ∈ N.flatten} = {d | d ∈ listOfDarts L} := by
  refine normalListComplete hconn hne hnorm fun x hx => ?_
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  exact List.mem_flatten.mpr ⟨l, hl, by rw [hfinal l hl x hxl]; exact nextEl_mem_of_mem hxl⟩

/-! ### §2 final_list_core（tame_list.hl:12786-:12800） -/

/-- **HOL `final_list_core`**（tame_list.hl:12786-:12800）
`!L r. good_list L /\ all (\x. MEM x (list_of_darts L)) r /\
is_edge_nondegenerate (hypermap_of_list L) /\ uniq r /\
final_list L r ==> core L r = MAP FST r`——coreSpine show 换形
（批 34 quotientListCore 同款 defeq 展开）+ finalListParts（批 33）
项式直投 + MAP_EQ 面 = List.map_congr_left 逐点 rfl
（`[a].head!.1` 点式 defeq 收口）。 -/
theorem finalListCore (hL : GoodList L) {r : List (ℕ × ℕ)}
    (hdarts : ∀ x ∈ r, x ∈ listOfDarts L)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hun : r.Nodup) (hf : finalListSpine L r) :
    coreSpine L r = r.map (fun x => x.1) := by
  show (partsSpine L r).map (fun a => a.head!.1) = r.map (fun x => x.1)
  rw [finalListParts L hL r hdarts hnedg hf hun, List.map_map]
  exact List.map_congr_left fun a _ => rfl

/-! ### §3 final_list_quotient（tame_list.hl:12802-:12830，章 capstone） -/

/-- **HOL `final_list_quotient`**（tame_list.hl:12802-:12830）
`!L N. good_list L /\ is_edge_nondegenerate (hypermap_of_list L) /\
normal_list L N /\ all (final_list L) N ==> quotient_list L N =
MAP (MAP FST) N`——quotientListCore（批 34）换装 +
MAP_EQ 面单层 map_congr_left：r ∈ N 槽 finalListCore 直取（darts
支 = normalListListOfDarts（批 5）+ List.mem_flatten 组装、uniq 支
= normalListUniqNonnil（批 6）第 1 合取、final_list 支 = hfinal r
hr）。 -/
theorem finalListQuotient {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hnorm : NormalListSpine hL N)
    (hfinal : ∀ r ∈ N, finalListSpine L r) :
    quotientListSpine L N = N.map (fun r => r.map (fun x => x.1)) := by
  rw [quotientListCore]
  exact List.map_congr_left fun r hr =>
    finalListCore hL
      (fun x hx => normalListListOfDarts hnorm x (List.mem_flatten.mpr ⟨r, hr, hx⟩))
      hnedg (normalListUniqNonnil hnorm hr).1 (hfinal r hr)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；三件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.finalListComplete
#print axioms Kepler.Text.TameSpine.finalListCore
#print axioms Kepler.Text.TameSpine.finalListQuotient
-/

/-
  Kepler.Text.TameSpine.TameList44 — B1 Tame_list 地基批 44：find_list
  章（tamespine-port-plan §4 批次表 B1 行；接续批 43 =
  TameList43.lean，批 43 终点 = HOL :12516；本批起点 = HOL :12518
  `find_list_map`。行号均按主仓 reference/flyspeck（commit
  1ce0353）实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12518-:12590）：

  主件一：`find_list_map` :12518-:12544
  `!f r d. uniq (flatten r) /\ MEM d (flatten r) /\ (!x y. MEM x
  (flatten r) /\ MEM y (flatten r) /\ f x = f y ==> x = y) ==>
  find_list (MAP (MAP f) r) (f d) = MAP f (find_list r d)`
  ↦ `findListMapSpine`（真证）。HOL 证体 find_list_uniq（:5731）三槽
  直投：uniq 槽经 MAP_flatten（:873）+ lower_case +
  Seq.map_inj_in_uniq（seq-compiled.hl:3135）+ ASM 收尾；两 MEM 槽各
  经 MEMf_MAP（:157）+ mem_find_list1（:4706）/mem_find_list（
  formal_lp list_hypermap-compiled.hl:97）命中半向；Lean 面同链——
  flatten 面 mapFlattenSpine（批 2，← 向换装）+
  la7_nodup_map_on（TameLp；批 40 同记账），两 MEM 面 memfMap（批 2）
  + memFindList1/findListSpineMemN（批 8 命中合并件两投影），
  findListUniq（批 9）三槽收口。f 特化 `ℕ × ℕ → ℕ × ℕ`
  （findListSpine 载体 dart 面锁定 `MAP (MAP f) r` 须落在
  List (List (ℕ × ℕ))，HOL 无类型参数的 Lean 折算惯例，沿
  la7_nextEl_map on-集单射形同族）。

  主件二：`marked_list_x_last` :12546-:12590
  `!L N r x. good_list L /\ marked_list L N r x /\
  is_edge_nondegenerate (hypermap_of_list L) ==> (?p. MEM p
  (parts L r) /\ LAST p = x)`
  ↦ `markListXLast`（真证）。HOL 证体 marked_list 展开（normal_list +
  MEM r N + MEM x r 三合取项直取，proof body 零消费旗塔块）+
  normal_list_uniq_nonnil（:4498）+ parts_flatten（:6334）+
  MEM_EXTENSION（:8365）逐点化出 ∃p. MEM x p /\ MEM p (parts L r)；
  反证 ~（LAST p = x）后 parts_next_unlast（:6380）+
  next_el_parts_unlast（:6490）把 next_el r x 接到 next_el p x 再接
  f_list L (e_list x)，与 marked_list 合取项 3（next_el r x =
  f_list L x）及 edge_nondeg_f_xor_ni（:4933，darts 槽经
  normal_list_list_of_darts :3643）相抵；Lean 面全链在库——
  MarkedListSpine（批 7）合取项解构 + normalListUniqNonnil（批 6）+
  partsFlatten（批 9）flatten 换装逐点化 + partsNextUnlast/
  nextElPartsUnlast（批 9 双件）+ edgeNondegFXorNi（批 8）+ 合取项 6
  hfx 反向 rw 三步链；LAST p ↦ p.getLast!（全链惯例，本批结论仅
  相等式无两步相等/junk 桥需求）。

  载体折算盘点（批 43 头注预记侦察面，经全库 grep（含 LocalAuto 族）
  对拍——预记缺口全数在库，零新领土）：
  - `find_list_uniq`（tame_list.hl:5731）= 批 9 findListUniq
    （TameList9.lean:582）；
  - `mem_find_list1`（tame_list.hl:4706）= 批 8 memFindList1
    （TameList8.lean:318）；
  - `mem_find_list` 命中半向（formal_lp/hypermap/ssreflect/
    list_hypermap-compiled.hl:97-:104）= 批 8 findListSpineMemN
    （TameList8.lean:324；批 8/9 合并件 findListSpineHit 两投影，
    find_list 定义面 :49-:50 内联于 findListSpine，批 7 记账）；
  - `MAP_flatten`（tame_list.hl:873）= 批 2 mapFlattenSpine
    （TameList2.lean:716；本批 ← 向消费）；
  - `Seq.map_inj_in_uniq`（jHOLLight seq-compiled.hl:3135）=
    la7_nodup_map_on（TameLp.lean:4134；批 40 同记账）；
  - `MEMf_MAP`（tame_list.hl:157）= 批 2 memfMap（TameList2.lean:195）；
  - `normal_list_uniq_nonnil`（tame_list.hl:4498）= 批 6
    normalListUniqNonnil（TameList6.lean:630）；
  - `parts_flatten`（tame_list.hl:6334）= 批 9 partsFlatten
    （TameList9.lean:1063）；
  - `parts_next_unlast`（tame_list.hl:6380）= 批 9 partsNextUnlast
    （TameList9.lean:1293）；
  - `next_el_parts_unlast`（tame_list.hl:6490）= 批 9
    nextElPartsUnlast（TameList9.lean:1368）；
  - `edge_nondeg_f_xor_ni`（tame_list.hl:4933）= 批 8
    edgeNondegFXorNi（TameList8.lean:368）；
  - `normal_list_list_of_darts`（tame_list.hl:3643）= 批 5
    normalListListOfDarts（TameList5.lean:146）；
  - `marked_list`（tame_defs2.hl:550-:564）前 7 合取块 = 批 7
    MarkedListSpine（旗塔末两合取块 reduction 领土，批 7 头注记账
    沿用；本批证明体只消费合取项 2/3/4/6，结论零收窄）；
  - `parts` = 批 7 partsSpine；`MEM_EXTENSION`（tame_list.hl:8365）
    = Lean 面 mem_flatten 逐点化零折算；`LAST` ↦ `getLast!`（全链
    惯例）；`find_list` 命中块 = 批 8/9 公开件直引（本批免批 12/13
    式私件重推）。
  全库无 find_list_map/marked_list_x_last 现成载体（grep 全库含
  LocalAuto 族零撞车）——两件即镜像本体。

  新落地载体：零（纯消费批）。私件：零。

  诚实记账：两件全真证，零新 def、零 sorry、零止损件、零记账债。
  范围决策：批 44 射程收口至 :12590（find_list 章 + marked_list_x_last
  同章随收毕）；:12593 `sumn_cons` 起 sumn/sizel 算术章换族，不属
  find_list 章射程，留批 45（侦察注记：Seq.sumn ↦ List.sum 换装
  候选；`Seq.uniq_leq_size` 面 = Batteries `List.subperm_of_subset`
  + `List.Subperm.length_le` 路线在册；sumn_le 逐点 ≤ 面 = Mathlib
  Algebra.Order.BigOperators.Group.List `sum_le_sum`（to_additive）
  形在册；`Seq.size_flatten` 面 Mathlib `List.length_flatten` 件名
  本工具链（mathlib + batteries 全量 grep）不在册，需 induction
  自证或寻替代面——如实记档）。红线遵守：零既有文件触碰、零 git
  写操作。
  批 45 接续点：HOL :12593 `sumn_cons`（sumn/sizel 算术章——
  sumn_cons :12593/sumn_size :12601/sumn_le :12612 三件 +
  :12633 `normal_list_size_bound` 章末 capstone，载体链侦察注记见
  上）→ :12658 `connected_induction` 换章（connected_hypermap/
  contour 领土）。
-/

import Kepler.Text.TameSpine.TameList43

namespace Kepler.Text.TameSpine

open Kepler.Assembly (eList fList GoodList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList)

/-! ### §1 find_list_map（tame_list.hl:12518-:12544） -/

/-- **HOL `find_list_map`**（tame_list.hl:12518-:12544）
`uniq (flatten r) /\ MEM d (flatten r) /\ (!x y. MEM x (flatten r) /\
MEM y (flatten r) /\ f x = f y ==> x = y) ==> find_list (MAP (MAP f) r)
(f d) = MAP f (find_list r d)`——find_list 沿 dart 换标运输：
find_list_uniq 三槽直投（uniq 槽 MAP_flatten + map_inj_in_uniq、
两 MEM 槽 MEMf_MAP + mem_find_list1/mem_find_list 命中半向）。 -/
theorem findListMapSpine (f : ℕ × ℕ → ℕ × ℕ) {r : List (List (ℕ × ℕ))}
    {d : ℕ × ℕ} (hun : r.flatten.Nodup) (hd : d ∈ r.flatten)
    (hinj : ∀ x ∈ r.flatten, ∀ y ∈ r.flatten, f x = f y → x = y) :
    findListSpine (r.map (fun s => s.map f)) (f d)
      = (findListSpine r d).map f := by
  -- 第 1 槽：uniq (flatten (MAP (MAP f) r))（HOL MAP_flatten +
  -- lower_case + Seq.map_inj_in_uniq）
  have hfl : (r.map (fun s => s.map f)).flatten = r.flatten.map f :=
    (mapFlattenSpine (f := f) r).symm
  have hun2 : (r.map (fun s => s.map f)).flatten.Nodup := by
    rw [hfl]
    exact Kepler.Text.TameLp.la7_nodup_map_on hinj hun
  -- 第 2/3 槽：MEM (f d) / MEM (MAP f (find_list r d))（HOL 两发
  -- MEMf_MAP：mem_find_list1 面 + mem_find_list 命中半向面）
  exact findListUniq hun2 (memfMap (memFindList1 hd))
    (memfMap (findListSpineMemN hd))

/-! ### §2 marked_list_x_last（tame_list.hl:12546-:12590） -/

/-- **HOL `marked_list_x_last`**（tame_list.hl:12546-:12590）
`good_list L /\ marked_list L N r x /\ is_edge_nondegenerate
(hypermap_of_list L) ==> (?p. MEM p (parts L r) /\ LAST p = x)`
——每个 marked dart 是 parts 内某段的 LAST：parts_flatten 逐点化出
命中段 p，反证 LAST p ≠ x 后 parts_next_unlast +
next_el_parts_unlast 把 next_el p x 接到 f_list L (e_list x)，与
marked_list 合取项 3（next_el r x = f_list L x）及
edge_nondeg_f_xor_ni 相抵。 -/
theorem markListXLast {L : fgraph ℕ} (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpine hL N r x)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate) :
    ∃ p ∈ partsSpine L r, p.getLast! = x := by
  obtain ⟨-, hn, hr, hx, -, hfx, -⟩ := hm
  obtain ⟨hun, hne⟩ := normalListUniqNonnil hn hr
  -- MEM x (flatten (parts L r)) 逐点化（HOL parts_flatten +
  -- MEM_EXTENSION 槽）
  obtain ⟨p, hp, hxp⟩ := List.mem_flatten.mp
    (by rw [partsFlatten L hun hne]; exact hx)
  refine ⟨p, hp, ?_⟩
  by_contra hcon
  have hx2 : x ≠ p.getLast! := fun hxx => hcon hxx.symm
  have hxdarts : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hr, hx⟩)
  -- next_el r x → next_el p x → f_list L (e_list x) 三步链与
  -- 合取项 6 hfx 反接
  have habs : fList L x = fList L (eList x) := by
    rw [← hfx, nextElPartsUnlast L hun hne hp hxp hx2,
      partsNextUnlast L hun hne p hp x hxp hx2]
  exact edgeNondegFXorNi hL hnedg hxdarts habs

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.findListMapSpine
#print axioms Kepler.Text.TameSpine.markListXLast
-/

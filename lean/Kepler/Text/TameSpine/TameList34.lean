/-
  Kepler.Text.TameSpine.TameList34 — B1 Tame_list 地基批 34：dih2k 章主件 +
  quotient 章开局（tamespine-port-plan §4 批次表 B1 行；接续批 33 =
  TameList33.lean，批 33 终点 = HOL :11425（final_list_parts 已落）；
  本批起点 = HOL :11428 `dih2k_card_face`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  **重大勘误（批 33 预记 vs 主仓实测；雷区 #36 全量复查先行）**：
  批 33 头注/commit 预记「Lvducxu 模块面 DIH2K_IMP_SIMPLE_HYPERMAP2
  （LVDUCXU.hl:1829）+ DIH2K_FACE_SIMPLIZED（:1838）全库 grep 零命中
  ——批 34 首桩即库建」。主仓实测：二名**在库**
  `Kepler.Text.LocalAuto10.lean:703/:709` 均有落地——
  · :703 `DIH2K_IMP_SIMPLE_HYPERMAP2` 系**真件**（一行转发
    `DIH2K_IMP_SIMPLE_HYPERMAP`，与 HOL 同链）；
  · :709 `DIH2K_FACE_SIMPLIZED` 系 **sorry 桩**（DISCHARGES registry
    巨件；同文件 :691 SIMPLE_FACE_DISJOINT_NODE_MAP_2、:717
    DIH_K_HYP_E_PRIME、:732 LVDUCXU 同为 sorry 桩）。
  归因：批 33 grep 面未覆盖 LocalAuto 族（TameSpine import 树不可见
  ——批 29 起唯一 LocalAuto 边 = LocalAuto3，import 传递可见面不含
  LocalAuto10）。处置：TameSpine 可见面缺口仍在，本批沿批 29 体例在
  TameSpine 命名空间自落可见件，分述：
  · DIH2K_IMP_SIMPLE_HYPERMAP2 ↦ `dih2kImpSimpleHypermap2` 真证（转发
    在库真件 `DIH2K_IMP_SIMPLE_HYPERMAP`，LocalAuto3.lean:1807，axiom
    三零批 29 实测）——体例同 LocalAuto10:703；
  · DIH2K_FACE_SIMPLIZED **本批不落**（真证规模：HOL 证体 ~160 行——
    SIMPLE_FACE_DISJOINT_NODE_MAP_2 的 nodeMap²=id 引擎 + 
    inverse2_hypermap_maps 面-node 交换 + ITER 归纳轨道交换 + 
    ITER_CYCLIC_ORBIT / CARD_LE_K_OF_SET_K_FIRST_ELMS 计数，独占批 35
    规模）；**主件消费侧直算绕道**（下件头注记档），本批 TameSpine 链
    对该桩零消费、零牵连、零记账债。批 35 处方：若下游（DIH_K_HYP_
    E_PRIME / LVDUCXU 本体 / Localization 章件）需 ⇐ 向，先落
    SIMPLE_FACE_DISJOINT_NODE_MAP_2（LVDUCXU.hl:1673-:1727，前提面
    x IN dart /\ face SUBSET dart /\ simple_hypermap /\ 不相交 /\ 覆盖
    ⇒ nodeMap 无不动点 ∧ nodeMap²=id 于 dart）再落交换+计数三层。

  **主件消费侧直算绕道（记档）**：HOL `dih2k_card_face` 证体经
  ENOUGH_TO_SHOW_TAC 折 `simple_hypermap /\ 不相交` 两槽，再以
  Lvducxu.DIH2K_FACE_SIMPLIZED ⇐ 折回 `dih2k H (CARD (face H x))`，
  末以 `2*k = 2*u <=> k = u` 收口。Lean 面绕开该折返（零消费
  DIH2K_FACE_SIMPLIZED）：dih2k_p3 覆盖合取（hd.2.1 于 x）+ 两侧不
  相交（dih2kImpPreSimpleHyp2 于 z ∈ face x：face_eq_of_mem 换面 +
  face_subset_darts 入 dart）+ nodeMap 全单（Equiv.Perm 结构场）⇒
  ncard(像) = ncard(face x)，故 `(↑darts : Set).ncard = 2·ncard(face x)`
  与 `darts.card = 2*k`（hd.1；HOL 子目标 `FINITE(dart H)` 半支在 Lean
  Finset finiteness 内建下零镜像）联立收口——绕道后主件证体五行。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11428-:11627 +
  LVDUCXU.hl:1829）：

  主件：`dih2k_card_face` :11428-:11575
  `!k H x. ~(k=0) /\ dih2k H k /\ x IN dart H ==> CARD (face H x) = k`
  ↦ `dih2kCardFace`（真证，绕道如上）。载体逐槽：`dih2k` ↦
  `Kepler.Text.dih2k_p3`（LocalAuto3.lean:127，批 29/30 惯例）；
  `CARD (face H x)` ↦ `(H.face x).ncard`（批 30 形）；`simple_hypermap`
  槽 ↦ `H.Simple`（批 32 惯例，本件经转发件直取）；`DIH2K_IMP_PRE_
  SIMPLE_HYP2` ↦ 批 29 `dih2kImpPreSimpleHyp2`（TameList29.lean:106）；
  `lemma_face_identity`（hypermap.hl:2144）↦ `Hypermap.face_eq_of_mem`
  （Hypermap.lean:2486）；`lemma_face_subset`（hypermap.hl:1283）↦
  `Hypermap.face_subset_darts`（Hypermap.lean:854）；HYP_MAPS_INJ/
  CARD_IMAGE_INJ（LVDUCXU.hl:1662/:1859 面）↦ Mathlib
  `Set.ncard_image_of_injective`（nodeMap : Equiv.Perm 全单强形）。

  库建桩：Lvducxu.`DIH2K_IMP_SIMPLE_HYPERMAP2`（LVDUCXU.hl:1829-:1832）
  ↦ `dih2kImpSimpleHypermap2`（真证转发，勘误如上）。

  quotient 章开局（:11576 起，载体 TameList7 全数在库）：
  · `quotient_list_core` :11576-:11591 ↦ `quotientListCore`
    `!L N. quotient_list L N = MAP (core L) N`——纯 def 展开装配：
    quotientListSpine/coreListSpine/coreSpine（TameList7.lean:466-477）
    + `List.map_map` + rfl；HOL REWRITE_TAC[quotient_list;core_list;
    core] + GSYM MAP_o + MAP_EQ 两层全部被 def 同形吸收，零新件。
  · `mem_core` :11593-:11627 ↦ `memCore`
    `good_list L /\ normal_list L N /\ MEM r N ==> (MEM v (core L r)
    <=> MEM v (MAP FST r))`——⇒ 向：core 块首元非 nil（partsAllNonnil）
    + `head!_mem_self` + `parts_flatten = r`（partsFlatten）折回 r；
    ⇐ 向：`parts_flatten` 展开 + mem_flatten 拆块 + `parts_fst`
    （partsFst）首元换装。载体全数批 6/9/10 处方件：
    normalListUniqNonnil（TameList6.lean:630）/ partsFlatten+
    partsAllNonnil（TameList9.lean:1063/:1227）/ partsFst
    （TameList10.lean:442）——批 9→10 处方「parts_fst 在 mem_core
    下游消费」于本批兑现。

  终点自然边界：`mem_core` 后 = :11633 `set_of_list_cat`（一行为，
  `SET_OF_LIST_APPEND` 折算）→ :11641 `quotient_list_elements`
  （quotient 章主体）。

  依赖面：批链全批 1-33；在库 LocalAuto3（DIH2K_IMP_SIMPLE_HYPERMAP，
  TameList29 起 import 边传递可见）/ TameList6（normalListUniqNonnil）/
  TameList7（quotientListSpine/coreListSpine/coreSpine）/ TameList9
  （partsFlatten/partsAllNonnil）/ TameList10（partsFst）/ TameList29
  （dih2kImpPreSimpleHyp2）+ Hypermap face API（face_eq_of_mem/
  face_subset_darts）+ Mathlib Set.ncard 族（ncard_coe_finset
  Card.lean:668 / ncard_union_eq :1035 / ncard_image_of_injective
  :831）。
  泛型幅度裁定：主件二件纯 hypermap 面无列表载体牵连（HOL 语句本身
  (A) 泛型），保持泛型 α（批 25/29 先例）；quotient 二件 fgraph ℕ
  列表载体（章惯例）。

  诚实记账：本批四件全部真证，零新 def、零 sorry、零止损件、零记账
  债；DIH2K_FACE_SIMPLIZED 明记批 35 处方（本批零消费，TameSpine 链
  零牵连）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零
  git 写操作。批 35 接续点：HOL :11633 `set_of_list_cat`
  `!u v. set_of_list (cat u v) = set_of_list u UNION set_of_list v`
  （`setOfListSpine` TameList11.lean:88 + `SET_OF_LIST_APPEND` 折算，
  一行为）随收后入 :11641 `quotient_list_elements`
  `!L N r. good_list L /\ MEM r N ==> set_of_list (quotient_list L N)
  = ...`（quotient 章主体；依赖 mem_core 本批已落 + parts 族）。
-/

import Kepler.Text.TameSpine.TameList33

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList listOfDarts GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList)

/-! ### §1 Lvducxu.DIH2K_IMP_SIMPLE_HYPERMAP2（LVDUCXU.hl:1829）——库建桩 -/

/-- **HOL `Lvducxu.DIH2K_IMP_SIMPLE_HYPERMAP2`**（LVDUCXU.hl:1829-:1832）
`dih2k (H:(A)hypermap) k /\ ~(k = 0) ==> simple_hypermap H`
——face_map_and_darts + DIH2K_IMP_SIMPLE_HYPERMAP 单行 MESON 的模块面
转发。勘误记档：批 33 预记「全库 grep 零命中」不成立——
`Kepler.Text.DIH2K_IMP_SIMPLE_HYPERMAP2` 已在库（LocalAuto10.lean:703，
真证一行转发 DIH2K_IMP_SIMPLE_HYPERMAP，同一 HOL 链）；唯 TameSpine
import 树不含 LocalAuto10（批 29 起唯一 LocalAuto 边 = LocalAuto3），
本件沿批 29 体例在 TameSpine 命名空间自落可见同形件。 -/
theorem dih2kImpSimpleHypermap2 {α : Type*} [DecidableEq α] {H : Hypermap α}
    {k : ℕ} (hd : dih2k_p3 H k) (hk : k ≠ 0) : H.Simple :=
  DIH2K_IMP_SIMPLE_HYPERMAP hd hk

/-! ### §2 dih2k_card_face（tame_list.hl:11428-:11575）——dih2k 章主件 -/

/-- **HOL `dih2k_card_face`**（tame_list.hl:11428-:11575）
`!k H x. ~(k=0) /\ dih2k H k /\ x IN dart H ==> CARD (face H x) = k`
——dih2k 下每面恰 k dart。HOL 证体两段：子目标 `FINITE (dart H) /\
CARD (dart H) = 2 * k`（node_map_and_darts + Localization.dih2k——
Lean 面 dih2k_p3 首合取直取，darts 系 Finset finiteness 内建，零镜像）；
ENOUGH 槽 `simple_hypermap H /\ face H x INTER IMAGE (node_map H)
(face H x) = {}` 经 Lvducxu.DIH2K_FACE_SIMPLIZED ⇐ 折回
`dih2k H (CARD (face H x))` 再以 `2*k = 2*u <=> k = u` 收口。Lean 面
消费侧直算绕道（模块头注记档）：覆盖合取（hd.2.1 于 x）+ 两侧不相交
（dih2kImpPreSimpleHyp2 于 z ∈ face x：face_eq_of_mem 换面 +
face_subset_darts 入 dart）+ nodeMap 全单 ⇒ ncard(像) = ncard(face x)
⇒ `(↑darts : Set).ncard = 2 * ncard(face x)` 与 `darts.card = 2 * k`
联立收口。`CARD (face H x)` ↦ `(H.face x).ncard`（批 30 形）。 -/
theorem dih2kCardFace {α : Type*} [DecidableEq α] {H : Hypermap α}
    {k : ℕ} (hd : dih2k_p3 H k) (hk : k ≠ 0) (x : α) (hx : x ∈ H.darts) :
    (H.face x).ncard = k := by
  -- 两侧不相交（HOL ENOUGH 槽 2 = DIH2K_IMP_PRE_SIMPLE_HYP2 链）：
  -- y ∈ face x ∩ nodeMap''(face x) 时 y = nodeMap z、z ∈ face x ⊆ dart，
  -- 而 nodeMap z ∉ face z = face x（face_eq_of_mem 换面）
  have hdisj : Disjoint (H.face x) ((H.nodeMap : α → α) '' H.face x) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    obtain ⟨z, hz, rfl⟩ := hy2
    refine dih2kImpPreSimpleHyp2 hd hk z (Finset.mem_coe.mp ?_) ?_
    · exact H.face_subset_darts hx hz
    · rw [← H.face_eq_of_mem hz]
      exact hy1
  -- 像与原像等势（HOL CARD_IMAGE_INJ + HYP_MAPS_INJ 面；
  -- nodeMap : Equiv.Perm 全单强形，HYP_MAPS_INJ 零镜像）
  have himg : ((H.nodeMap : α → α) '' H.face x).ncard = (H.face x).ncard :=
    Set.ncard_image_of_injective _ H.nodeMap.injective
  -- 不相交覆盖折算（HOL CARD_UNION 面；face x ⊆ dart 的有限性桥）
  have hfin : (H.face x).Finite := (H.darts.finite_toSet).subset (H.face_subset_darts hx)
  have hcard : (↑H.darts : Set α).ncard
      = (H.face x).ncard + ((H.nodeMap : α → α) '' H.face x).ncard := by
    rw [hd.2.1 x hx]
    exact Set.ncard_union_eq hdisj hfin (hfin.image _)
  rw [Set.ncard_coe_finset, himg] at hcard
  -- hcard : H.darts.card = 2 * ncard(face x)；与 dih2k 首合取联立收口
  have hd0 := hd.1
  omega

/-! ### §3 quotient 章开局（tame_list.hl:11576-:11627） -/

/-- **HOL `quotient_list_core`**（tame_list.hl:11576-:11591）
`!L N. quotient_list L N = MAP (core L) N`——quotient_list = core_list
（map (parts L) N）与 core 的 def 展开装配：HOL REWRITE_TAC[quotient_
list;core_list;core] + GSYM MAP_o + MAP_EQ 两层全被在库 def 同形吸收
（quotientListSpine/coreListSpine/coreSpine，TameList7.lean:466-477），
`List.map_map` 一步 + rfl。 -/
theorem quotientListCore (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) :
    quotientListSpine L N = N.map (coreSpine L) := by
  show (N.map (partsSpine L)).map (fun f => f.map (fun a => a.head!.1))
      = N.map (coreSpine L)
  rw [List.map_map]
  rfl

/-- **HOL `mem_core`**（tame_list.hl:11593-:11627）
`good_list L /\ normal_list L N /\ MEM r N ==> (MEM v (core L r) <=>
MEM v (MAP FST r))`——core（parts 块首元表）与 MAP FST r 同元集。
⇒ 向：块首元非 nil（partsAllNonnil）+ head! ∈ 块 + `parts_flatten = r`
（partsFlatten）折回 r；⇐ 向：`parts_flatten` 展开 + mem_flatten 拆块 +
`parts_fst`（partsFst）首元换装。载体批 6/9/10 处方件全数兑现
（批 9→10 处方「parts_fst 于 mem_core 下游消费」于本批落地）。 -/
theorem memCore (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) {r : List (ℕ × ℕ)} (hr : r ∈ N) (v : ℕ) :
    v ∈ coreSpine L r ↔ v ∈ r.map (fun d => d.1) := by
  obtain ⟨hun, hne⟩ := normalListUniqNonnil hn hr
  constructor
  · -- ⇒（HOL parts_uniq_nonnil + MEM (HD x) x + parts_flatten 链）：
    -- core 元 = 某 parts 块首元，块非 nil，首元落 flatten = r
    intro hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp
      (show v ∈ (partsSpine L r).map (fun a => a.head!.1) from hmem)
    show p.head!.1 ∈ r.map (fun d => d.1)
    refine List.mem_map.mpr ⟨p.head!, ?_, rfl⟩
    rw [← partsFlatten L hun hne]
    exact List.mem_flatten.mpr ⟨p, hp,
      List.head!_mem_self (partsAllNonnil L hun hne p hp)⟩
  · -- ⇐（HOL MEM_EXTENSION + parts_flatten + parts_fst 链）：
    -- r 之元 d 拆入某 parts 块 p，parts_fst 换装 d.1 = p 首元
    intro hmem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
    have hd0 : d ∈ (partsSpine L r).flatten := by
      rw [partsFlatten L hun hne]
      exact hd
    obtain ⟨p, hp, hx⟩ := List.mem_flatten.mp hd0
    refine List.mem_map.mpr ⟨p, hp, ?_⟩
    rw [partsFst L hL hn hr hp hx]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；四件预期标准三
[propext, Classical.choice, Quot.sound]，零 sorryAx）：
#print axioms Kepler.Text.TameSpine.dih2kImpSimpleHypermap2
#print axioms Kepler.Text.TameSpine.dih2kCardFace
#print axioms Kepler.Text.TameSpine.quotientListCore
#print axioms Kepler.Text.TameSpine.memCore
-/

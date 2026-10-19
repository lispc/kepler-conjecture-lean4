/-
  Kepler.Text.TameSpine.TameList35 — B1 Tame_list 地基批 35：quotient 章续
  （tamespine-port-plan §4 批次表 B1 行；接续批 34 = TameList34.lean，批 34
  终点 = HOL :11627（mem_core 已落）；本批起点 = HOL :11633
  `set_of_list_cat`。行号均按主仓 reference/flyspeck（commit 1ce0353）实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11633-:11682）：

  随收件：`set_of_list_cat` :11633-:11637
  `!u v. set_of_list (cat u v) = set_of_list u UNION set_of_list v`
  ↦ `setOfListCat`（真证）。折算：`cat u v` ↦ `u ++ v`（upper_case =
  GSYM lower_case（tame_list.hl:1397/:1401）含 APPEND_cat 的 cat↦++
  展开；TameSpine 惯例 cat 语义直接以 ++ 载体）+ `SET_OF_LIST_APPEND`
  （ssreflect seq2 层）↦ `List.mem_append` 逐点折算——HOL REWRITE_TAC
  [upper_case;SET_OF_LIST_APPEND] 两步在 `ext x` 逐点形下被
  setOfListSpine 的 {x | x ∈ _} def 同形吸收。载体 = 批 11
  `setOfListSpine`（TameList11.lean:88，(ℕ×ℕ) 级）；HOL 语句泛型，
  实测下游消费 tame_list.hl:12461（iso_list_sym_normal_cat）在 dart
  级（A#A 列表），载体层级匹配，泛型幅度裁定沿批 34 惯例按章定格
  （quotient 章 fgraph ℕ 列表载体）。

  主件：`quotient_list_elements` :11641-:11682
  `!L N. good_list L /\ normal_list L N ==> (elements_of_list
  (quotient_list L N)) = set_of_list (MAP FST (flatten N))`
  ↦ `quotientListElements`（真证，quotient 章主体）。HOL 证体
  EXTENSION + EQ_EXPAND 双向：⇒ 向 list_of_elements + mem_undup +
  mem_flatten + quotient_list_core + mem_core 链；⇐ 向同链 + 证人
  `core L r` + MEMf_MAP。Lean 面逐点折算：LHS `elements_of_list`
  ↦ `TameLp.elementsOfList`（TameLp.lean:4072，{x | x ∈
  L.flatten.eraseDups}；fgraph ℕ = List (List ℕ)（PlaneGraphIso.lean:
  80），quotientListSpine L N : List (List ℕ) 直配）经 core
  `List.mem_eraseDups` 消解（批 1 injOn_elementsOfList_iff 同款）；
  `quotient_list` 槽 = 批 34 `quotientListCore`（= N.map (coreSpine L)
  纯 def 形）+ `mem_flatten` 拆块；`mem_core` 槽 = 批 34 `memCore`
  双向直取（批 34 处方「本件依赖 memCore」于本批兑现）；
  `MEMf_MAP` ↦ 批 2 `memfMap` 形（匿名构造器吸收）。RHS
  `set_of_list (MAP FST (flatten N))` 的 set_of_list 在 ℕ（面-顶点
  元）级 ↦ 批 19 `setOfListNatSpine`（TameList19.lean:204，批 19
  惯例：面元级走 NatSpine、dart 级走 setOfListSpine）。载体全数在库
  零新 def：setOfListNatSpine（批 19）/ elementsOfList（TameLp）/
  quotientListCore + memCore（批 34）/ quotientListSpine + coreSpine
  （批 7）/ NormalListSpine（批 5）。

  **DIH2K_FACE_SIMPLIZED 处置记档（批 34 三层处方决策准则执行）**：
  批 34 处方「仅当下游消费 ⇐ 向（DIH_K_HYP_E_PRIME / LVDUCXU 本体 /
  Localization 章件）时才值得落」。本批侦察结论（全库 grep 含
  LocalAuto 族，雷区 #39）：
  · B1 车道领土（tame_list.hl + reduction1-4.hl）：DIH2K_FACE_
    SIMPLIZED 消费仅 :11439 `dih2k_card_face` 一处——批 34 已直算
    绕道零消费落地，B1 链对该桩零消费；
  · ⇐ 向消费者：`REWRITE_TAC[GSYM DIH2K_FACE_SIMPLIZED]` 唯一见
    LVDUCXU.hl:2106 `DIH_K_HYP_E_PRIME`（:2101-:2135，其自身唯一
    消费点 :2300 LVDUCXU 本体）——全链居 text_formalization/local/
    Localization 领土，非 B1 车道前瞻件；Lean 面 LocalAuto10.lean:
    717/:732 系 DISCHARGES registry 巨桩，属 LocalAuto lane 处置。
  按批 34 决策准则：**不消费 → 记档跳过（纪律非止损）**，三层处方
  原样挂档（SIMPLE_FACE_DISJOINT_NODE_MAP_2（LVDUCXU.hl:1673-:1727）
  打底 + inverse2_hypermap_maps 面-node 交换 + ITER 轨道计数）移交
  消费 lane。本批 TameSpine 链对 LocalAuto10 桩零牵连、零记账债。

  终点自然边界：`quotient_list_elements` 后 tame_list.hl 入 iso_list
  章：:11684 `iso_list_nilfamily`（`iso_list (L,N) (L',N') ==> iso_list
  (L,[]) (L',[])`，一行为；其后 :11688-:11701 iso_list_cons 系 HOL
  源注释块、:11703 iso_list_marked_rN = 0 系非定理占位）→ :11709
  `iso_list_mem_rN`（MEMf_MAP 面）。

  依赖面：批链全批 1-34；本批零新 def，消费面 = TameLp
  elementsOfList + 批 2 memfMap 形 + 批 5 NormalListSpine + 批 7
  quotientListSpine/coreSpine + 批 11 setOfListSpine + 批 19
  setOfListNatSpine + 批 34 quotientListCore/memCore + core
  List.mem_eraseDups / List.mem_flatten / List.mem_append。

  诚实记账：本批两件全部真证，零新 def、零 sorry、零止损件、零记账
  债；DIH2K_FACE_SIMPLIZED 记档跳过如上（非止损件）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零
  git 写操作。批 36 接续点：HOL :11684 `iso_list_nilfamily`
  `!L L' N N'. iso_list (L,N) (L',N') ==> iso_list (L,[]) (L',[])`
  （一行为，iso_list ↦ IsoListSpine 平铺序——雷区 #11 记档）随收后
  入 :11709 `iso_list_mem_rN`
  `!L N r x L' N' r' x'. good_list L' /\ MEM r N /\ iso_list
  (L,([x]::r::N)) (L',([x']::r'::N')) ==> MEM r' N'`（MEMf_MAP 面，
  批 2 memfMap 在库）。
-/

import Kepler.Text.TameSpine.TameList34

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (elementsOfList)

/-! ### §1 set_of_list_cat（tame_list.hl:11633-:11637）——随收件 -/

/-- **HOL `set_of_list_cat`**（tame_list.hl:11633-:11637）
`!u v. set_of_list (cat u v) = set_of_list u UNION set_of_list v`
——`cat` 语义经 upper_case（GSYM lower_case，tame_list.hl:1397/:1401，
含 APPEND_cat）折算为 `++`；`SET_OF_LIST_APPEND`（ssreflect seq2 层）
逐点折算为 `List.mem_append`。载体 = 批 11 `setOfListSpine`
（(ℕ×ℕ) 级；下游消费 :12461 iso_list_sym_normal_cat 系 dart 级，
层级匹配）。 -/
theorem setOfListCat (u v : List (ℕ × ℕ)) :
    setOfListSpine (u ++ v) = setOfListSpine u ∪ setOfListSpine v := by
  ext x
  show x ∈ u ++ v ↔ x ∈ u ∨ x ∈ v
  exact List.mem_append

/-! ### §2 quotient_list_elements（tame_list.hl:11641-:11682）——章主体 -/

/-- **HOL `quotient_list_elements`**（tame_list.hl:11641-:11682）
`good_list L /\ normal_list L N ==> (elements_of_list (quotient_list
L N)) = set_of_list (MAP FST (flatten N))`——quotient_list 的元素集
= N 各面 FST 元的集合。HOL EXTENSION + EQ_EXPAND 双向，两向同为
list_of_elements + mem_undup + mem_flatten + quotient_list_core +
mem_core 链（⇐ 向证人 `core L r` + MEMf_MAP）。Lean 面逐点：
`List.mem_eraseDups` 消解 undup 层、批 34 `quotientListCore` 折
quotient_list、`List.mem_flatten` 拆块、批 34 `memCore` 双向直取
（MEMf_MAP 槽 = mem_map 匿名构造器吸收）。RHS 面元级 set_of_list
↦ 批 19 `setOfListNatSpine`（批 19 惯例）。 -/
theorem quotientListElements (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N) :
    elementsOfList (quotientListSpine L N)
      = setOfListNatSpine (N.flatten.map (fun d => d.1)) := by
  have hq := quotientListCore L N
  ext x
  show x ∈ (quotientListSpine L N).flatten.eraseDups
      ↔ x ∈ N.flatten.map (fun d => d.1)
  rw [List.mem_eraseDups, hq, List.mem_flatten]
  constructor
  · -- ⇒（HOL quotient_list_core + mem_core 链）：x ∈ 某 core 块
    -- ⇔ x ∈ 对应面 r 的 FST 元表 ⇒ r ∈ N ∧ FST d = x 证人入 flatten
    rintro ⟨q, hq', hx⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
    have hx' : x ∈ r.map (fun d => d.1) := (memCore L hL hn hr x).mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map.mpr ⟨d, List.mem_flatten.mpr ⟨r, hr, hd⟩, rfl⟩
  · -- ⇐（HOL 证人 core L r + MEMf_MAP 面）：x = FST d、d ∈ r ∈ N
    -- ⇒ d ∈ flatten N ⇒ x ∈ core L r（memCore ⇐ 向）∈ quotient 块
    intro h
    rw [List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    obtain ⟨r, hr, hd⟩ := List.mem_flatten.mp he
    exact ⟨coreSpine L r, List.mem_map.mpr ⟨r, hr, rfl⟩,
      (memCore L hL hn hr e.1).mpr (List.mem_map.mpr ⟨e, hd, rfl⟩)⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件预期标准三
[propext, Classical.choice, Quot.sound]，零 sorryAx）：
#print axioms Kepler.Text.TameSpine.setOfListCat
#print axioms Kepler.Text.TameSpine.quotientListElements
-/

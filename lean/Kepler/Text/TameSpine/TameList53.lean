/-
  Kepler.Text.TameSpine.TameList53 — B1 Tame_list 地基批 53：
  next_el/list_pairs 机制章开章（tamespine-port-plan §4 批次表 B1 行；接续批 52 =
  TameList52.lean，批 52 终点 = HOL :13407；本批起点 = HOL :13409
  `next_el_list_pairs_eq`。行号均按主仓 reference/flyspeck（commit 1ce0353）实测；
  批 52 头注预记 :13409/:13436/:13449 三锚点与实测一致，零偏移。

  槽面侦察裁定（批 52 头注预记面的对拍结论）：

  - **next_el/list_pairs 泛型载体全部在册，零新 def 面**：
    - `next_el`（seq2-compiled.hl:24-25）↦ `Kepler.Assembly.nextEl`
      （GoodListDefs.lean:44，indexl/headl/nth ↦ idxOf/headD/getD 逐句镜像，
      批 1 既档）；`uniq` ↦ `List.Nodup` 批内既档；
    - `list_pairs`（list_hypermap-compiled.hl:19 `zip list (rot 1 list)`）↦
      `Kepler.Assembly.listPairs`（GoodListDefs.lean:34，rot 1 = drop 1 ++
      take 1 内联）+ zip·rotate 桥 `listPairsEqZipRotate`（TameList2.lean:333）；
    - **五槽机制对拍**（HOL 证体 Seq.nth_index/index_mem/index_el/nth_zip/
      next_el_alt）：nth_index ↦ TameLp `getElem_idxOf`（TameLp.lean:3560）、
      size_zip/size_rot/Ssrnat.minnn ↦ core `List.length_zip` +
      `List.length_rotate` + `Nat.min_eq_left`、nth_zip ↦ core
      `List.getElem_zip`（全隐式参——term 拼装经 Prop 证明无关性 defeq 收，
      下标注 `'` 证明槽与引理内 get_elem_tactic 槽 defeq 直通）、
      next_el_alt ↦ TameLp `nextEl_eq_getD`（TameLp.lean:3602）+
      `getD_eq_getElem_of_lt`（TameLp.lean:3526）、index_mem ↦ core
      `List.getElem_mem`；HOL 的 indexl-eq/index_el 槽（下标单射定位）在
      Lean 由 getElem_mem 免单射直证旁路——机制简化记档，非语义损失
      （getElem_mem 只需下标界，Mumni 环上 (x,next_el) 对由 idxOf x 下标
      直接Witness）。
  - **新雷区（TameLp 桥件隐式实例槽）**：`getElem_idxOf`/
    `getD_eq_getElem_of_lt`/`nextEl_eq_getD` 签名内藏隐式 `[DecidableEq α]`
    （TameLp.lean:3524 section variable）——消费件须显式加 [DecidableEq α]
    实例参，BEq+LawfulBEq 不自动提供（本批实测记档，
    nextElListPairsEq 按此加参）。
  - **card_le_size :13436**：mathlib `List.toFinset_card_le`
    （Mathlib/Data/Finset/Card.lean:209 `#l.toFinset ≤ l.length`）逐字同语句
    零镜像记档（批 52 预记命中）；set_of_list ↦ `List.toFinset` 批 2 既档。
  - **betwn_nil 槽件全部在册**：size_betwn（:2520）↦ sizeBetwn
    （TameList3.lean:1031）、indexf0（:1542 形）↦ indexfZeroEq
    （TameList3.lean:171）、indexf1（:1758）↦ indexfOne（TameList3.lean:391）、
    next_el_indexf（:1796）↦ nextElIndexf（TameList3.lean:418）；`1 < sizel f`
    槽（HOL 证体经 CARD (set_of_list f) > 1 + Counting_spheres.
    TWO_IMP_HAS_SIZE_GE_2 + card_le_size 三跳）在 Lean 以 `List.idxOf_inj`
    （Mathlib/Data/List/Basic.lean:656，免 Finset/DecidableEq 依赖）下标相异
    + omega 两行直证（机制简化记档）。
  - **directedLength 载体在册**：tame_defs.hl:438 `if (a=b) then 0 else
    LENGTH(betwn(FST f) a b) + 1` ↦ `Kepler.Graphs.directedLength`
    （Graph.lean:162 逐句同语句 Face 载体）；`betwn` ↦
    `Kepler.Graphs.between`（Isabelle Graph.thy 同源，批 3 betwn 家族载体）。
  - **showDups/hideDups/enum 载体在册**：showDups0/showDups/enumOfVertexList
    ↦ TameList4.lean:107/115/129（tame_defs2.hl:642/648/652 逐句镜像，
    `the` ↦ `Option.get!`）；hideDupsRec/hideDups/indexToVertexList ↦
    Kepler.Graphs.Enumerator.lean:44/49/54（Enumerator.thy 同源；
    indexToVertexList Face 载体，`nextVertices` = Graph.lean:72 消费）。
  - **Face/Vertex 名碰撞雷区**：本模块导入面上另有同名 Face/Vertex 常量
    winning resolution——directedLengthNext/sizeIndexToVertexList 语句与
    证体内一律写全限定 `Kepler.Graphs.Face`/`Kepler.Graphs.Vertex`
    （本批实测记档）。
  - **hd/last/all 约定既档**：`HD`/`LAST` ↦ `head!`/`getLast!`（批 11/12），
    junk 面由非空前提封死；`all` ↦ `List.all`（Bool 谓词，MEM 谓词面经
    decide + [DecidableEq α] 实例参折算）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13409-:13581，十二件）：

  §1 机制章开章：`next_el_list_pairs_eq` :13409 `!x s. uniq s /\ MEM x s ==>
  MEM (x, next_el s x) (list_pairs s)` ↦ nextElListPairsEq（真证；五槽机制
  如上对拍落地；hnd 前提 Lean 证体未消费——HOL 同样仅 uniq_list_pairs 消费
  于已旁路的 index_el 槽，保真闲置 unusedVariables 记档批 50/52 体例）。

  §2 集合尺寸：`card_le_size` :13436 ↦ cardLeSize（零镜像直投）。

  §3 betwn 章回补：`betwn_nil` :13449 `!f a b. uniq f /\ ~(a = b) /\ MEM a f /\
  MEM b f ==> (betwn f a b = [] <=> b = next_el f a)` ↦ betwnNil（真证；
  正向 sizeBetwn + indexfZeroEq 反证锁 indexf = 1 + indexfOne；反向
  nextElIndexf + length_eq_zero_iff；EQ_EXPAND 两向按 Iff 构造子分装）。

  §4 directedLength 章开章：`directedLength_next` :13474 ↦ directedLengthNext
  （真证；a = b 分流——directedLength 定义性归零双 False simp 收口；a ≠ b 支
  dAB/dBA 两条 if_neg 换装 + betwnNil 双向 instance + `2 ≤ l + 1 ↔ l ≠ 0`
  omega 桥）。

  §5 showDups/enum 家族（尺寸四件）：`size_showDups0` :13490 ↦
  sizeShowDups0（vs 归纳 generalizing a——recursion 首参换装雷区：
  some 支递归首参取 SOME 元而非原 a，`!vs v` HOL 序即 binder 序）、
  `size_showDups` :13501 ↦ sizeShowDups（cons 支 sizeShowDups0 直投）、
  `size_enum_of_VertexList` :13511 ↦ sizeEnumOfVertexList（length_map 桥）、
  `hd_enum_of_vertexlist` :13520 ↦ hdEnumOfVertexlist（calc 三步：enum/
  showDups/get! 定义性 defeq 折叠至 indexf v v f :: 形 + head! iota +
  indexfRefl 直投；List.head!_map 不在册实测记档）。

  §6 filter/last/all 家族：`last_filter` :13538 ↦ lastFilter（rconsButlast
  批 52 承接 + filter_append/filter_singleton + hp 换装 + Graphs
  getLast!_append_of_ne_nil；conv lhs 单侧换面保 RHS 原形）、
  `all_mem_filter` :13548 ↦ allMemFilter（all_map 桥 + comp beta rfl）。

  §7 hideDupsRec/indexToVertexList 尺寸件：`size_hideDupsRec` :13558 ↦
  sizeHideDupsRec（vs 归纳 generalizing a 同 §5 雷区；length_cons 尾消
  ——`length (x :: l) = length l + 1` 头项无关，if 支免 split 直落）、
  `size_indexToVertexList` :13569 ↦ sizeIndexToVertexList（map_cons β 归一 +
  hideDups 展开 + length_map 桥 + hideDupsRec 件 trans 收口）。

  诚实记账：十二件全真证（nextElListPairsEq/cardLeSize/betwnNil/
  directedLengthNext/sizeShowDups0/sizeShowDups/sizeEnumOfVertexList/
  hdEnumOfVertexlist/lastFilter/allMemFilter/sizeHideDupsRec/
  sizeIndexToVertexList），零 sorry、零止损件、零记账债；card_le_size 零镜像
  记档如上（非止损件）。范围决策：批 53 射程收口至 :13581（next_el 机制章
  开章件 + card/betwn/directedLength + showDups/enum 家族 + filter/last/all
  家族 + hideDupsRec/indexToVertexList 尺寸件，自然边界）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 54 接续点：HOL :13582 `unadj_alt`（:13582-:13614，`unadj` alt 刻画——
  EL/HD/TL 机制十九行；`unadj` 定义层批 4 已落 TameList4 `Unadj`，alt 面
  语义对拍开工先核；其后 :13615 hd_rotate_to/:13623 next_el_el/
  :13639 mem_rotate_to——`rotate_to` 载体在册性未侦察，tame_defs 系
  开工先核）。
-/

import Kepler.Text.TameSpine.TameList52

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl listPairs)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf)
open Kepler.Graphs (between directedLength indexToVertexList hideDups hideDupsRec
  getLast!_append_of_ne_nil)

variable {α : Type*}

/-! ### §1 next_el/list_pairs 机制章开章（tame_list.hl:13409） -/

/-- **HOL `next_el_list_pairs_eq`**（tame_list.hl:13409 `!x s. uniq s /\
MEM x s ==> MEM (x, next_el s x) (list_pairs s)`）。证体（五槽机制对拍）：
list_pairs ↦ zip·rotate 1 桥 + length_zip/length_rotate/min_eq_len 长度槽 +
getElem_zip（nth_zip）+ getElem_rotate（rot 逐点）+ nextEl_eq_getD/
getD_eq_getElem_of_lt（next_el_alt）+ getElem_mem（index_mem）；
HOL index_el 槽（indexl 单射）由 getElem_mem 免下标单射旁路。 -/
theorem nextElListPairsEq [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) {x : α} (hx : x ∈ s) : (x, nextEl s x) ∈ listPairs s := by
  rw [listPairsEqZipRotate]
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hi : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hrotlen : (s.rotate 1).length = s.length := List.length_rotate s 1
  have hir : s.idxOf x < (s.rotate 1).length := by rw [hrotlen]; exact hi
  have hlen : (s.zip (s.rotate 1)).length = s.length := by
    rw [List.length_zip, hrotlen]; exact Nat.min_eq_left (by omega)
  have hil : s.idxOf x < (s.zip (s.rotate 1)).length := by rw [hlen]; exact hi
  have e1 : (s.zip (s.rotate 1))[s.idxOf x]'hil
      = (s[s.idxOf x]'hi, (s.rotate 1)[s.idxOf x]'hir) := List.getElem_zip
  have e2 : (s.rotate 1)[s.idxOf x]'hir
      = s[(s.idxOf x + 1) % s.length]'(Nat.mod_lt _ hpos) :=
    List.getElem_rotate s 1 (s.idxOf x) hir
  have e3 : s[(s.idxOf x + 1) % s.length]'(Nat.mod_lt _ hpos) = nextEl s x := by
    rw [nextEl_eq_getD hx]
    exact (getD_eq_getElem_of_lt (Nat.mod_lt _ hpos) x).symm
  have h1 : s[s.idxOf x]'hi = x := getElem_idxOf hx
  have e4 : (s.zip (s.rotate 1))[s.idxOf x]'hil = (x, nextEl s x) := by
    rw [e1, e2, e3, h1]
  rw [← e4]
  exact List.getElem_mem hil

/-! ### §2 集合尺寸（tame_list.hl:13436） -/

/-- **HOL `card_le_size`**（tame_list.hl:13436 `!s. CARD (set_of_list s) <=
sizel s`）。mathlib `List.toFinset_card_le`（Mathlib/Data/Finset/Card.lean:209
`#l.toFinset ≤ l.length`）逐字同语句零镜像直投。 -/
theorem cardLeSize [DecidableEq α] (s : List α) : s.toFinset.card ≤ s.length :=
  List.toFinset_card_le s

/-! ### §3 betwn 章回补（tame_list.hl:13449） -/

/-- **HOL `betwn_nil`**（tame_list.hl:13449 `!f a b. uniq f /\ ~(a = b) /\
MEM a f /\ MEM b f ==> (betwn f a b = [] <=> b = next_el f a)`）。证体：
正向 sizeBetwn + indexfZeroEq（a = b 反证）锁 indexf = 1 + indexfOne；
反向 nextElIndexf（`1 < sizel f` 槽由 idxOf_inj 下标相异 + omega 直证，
HOL 的 CARD>1/TWO_IMP_HAS_SIZE_GE_2/card_le_size 三跳机制简化记档）+
length_eq_zero_iff。 -/
theorem betwnNil [BEq α] [LawfulBEq α] {f : List α} (hnd : f.Nodup)
    {a b : α} (hab : a ≠ b) (ha : a ∈ f) (hb : b ∈ f) :
    between f a b = [] ↔ b = nextEl f a := by
  have h2 : 2 ≤ f.length := by
    have hia : f.idxOf a < f.length := List.idxOf_lt_length_iff.mpr ha
    have hib : f.idxOf b < f.length := List.idxOf_lt_length_iff.mpr hb
    have hne : f.idxOf a ≠ f.idxOf b :=
      fun e => hab ((List.idxOf_inj ha).mp e)
    omega
  have hlt : 1 < f.length := h2
  have hsize := sizeBetwn hnd ha hb hab
  constructor
  · intro hnil
    have h0 : (between f a b).length = 0 := by rw [hnil]; rfl
    have hne0 : indexf a b f ≠ 0 := by
      intro h0; exact hab (indexfZeroEq ha hb h0)
    have h1 : indexf a b f = 1 := by omega
    exact (indexfOne ha hb hnd h1).symm
  · intro hbna
    have h1 : indexf a b f = 1 := nextElIndexf ha hb hnd hbna.symm hlt
    have h0 : (between f a b).length = 0 := by rw [hsize, h1]
    exact List.length_eq_zero_iff.mp h0

/-! ### §4 directedLength（tame_list.hl:13474） -/

/-- **HOL `directedLength_next`**（tame_list.hl:13474 `!f a b. uniq (FST f) /\
MEM a (FST f) /\ MEM b f ==> (2 <= directedLength f a b /\
2 <= directedLength f b a <=> ~(a = b) /\ ~(b = next_el (FST f) a) /\
~(a = next_el (FST f) b))`）。载体 `Kepler.Graphs.directedLength`
（Face 逐句镜像）；证体：a = b 分流（定义性归零双 False simp 收口），
a ≠ b 支定义方程 if_neg 换装 + betwnNil 双向 instance +
`2 ≤ l + 1 ↔ l ≠ 0` omega 桥。 -/
theorem directedLengthNext (f : Kepler.Graphs.Face)
    {a b : Kepler.Graphs.Vertex} (hnd : f.vertices.Nodup)
    (ha : a ∈ f.vertices) (hb : b ∈ f.vertices) :
    (2 ≤ directedLength f a b ∧ 2 ≤ directedLength f b a) ↔
      a ≠ b ∧ b ≠ nextEl f.vertices a ∧ a ≠ nextEl f.vertices b := by
  by_cases hab : a = b
  · subst hab
    simp [directedLength]
  · have dAB : directedLength f a b = (between f.vertices a b).length + 1 := by
      simp [directedLength, hab]
    have dBA : directedLength f b a = (between f.vertices b a).length + 1 := by
      simp [directedLength, Ne.symm hab]
    have hfwd := betwnNil hnd hab ha hb
    have hbwd := betwnNil hnd (Ne.symm hab) hb ha
    constructor
    · rintro ⟨h1, h2⟩
      rw [dAB] at h1
      rw [dBA] at h2
      refine ⟨hab, ?_, ?_⟩
      · intro hh
        rw [List.length_eq_zero_iff.mpr (hfwd.mpr hh)] at h1
        omega
      · intro hh
        rw [List.length_eq_zero_iff.mpr (hbwd.mpr hh)] at h2
        omega
    · rintro ⟨habne, hbna, anb⟩
      have hf := betwnNil hnd habne ha hb
      have hbw := betwnNil hnd (Ne.symm habne) hb ha
      refine ⟨?_, ?_⟩
      · rw [dAB]
        have hn0 : (between f.vertices a b).length ≠ 0 := by
          intro h0; exact hbna (hf.mp (List.length_eq_zero_iff.mp h0))
        omega
      · rw [dBA]
        have hn0 : (between f.vertices b a).length ≠ 0 := by
          intro h0; exact anb (hbw.mp (List.length_eq_zero_iff.mp h0))
        omega

/-! ### §5 showDups/enum 家族（tame_list.hl:13490-:13536） -/

/-- **HOL `size_showDups0`**（tame_list.hl:13490 `!vs v. sizel (showDups0 v vs)
= sizel vs`）。证体：vs 归纳 `generalizing a`——some 支递归首参换装
（showDups0 取 SOME 元续递归，非原 a），HOL `!vs v` 序即 binder 序。 -/
theorem sizeShowDups0 (vs : List (Option α)) (a : α) :
    (showDups0 a vs).length = vs.length := by
  induction vs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | none =>
      simp only [showDups0, List.length_cons]
      exact congrArg (fun n => n + 1) (ih a)
    | some c =>
      simp only [showDups0, List.length_cons]
      exact congrArg (fun n => n + 1) (ih c)

/-- **HOL `size_showDups`**（tame_list.hl:13501 `!vs. sizel (showDups vs) =
sizel vs`）。cons 支定义展开后 sizeShowDups0 直投。 -/
theorem sizeShowDups [Inhabited α] (vs : List (Option α)) :
    (showDups vs).length = vs.length := by
  cases vs with
  | nil => rfl
  | cons b bs => exact sizeShowDups0 (b :: bs) b.get!

/-- **HOL `size_enum_of_VertexList`**（tame_list.hl:13511
`!v f vs. sizel (enum_of_VertexList f v vs) = sizel vs`）。定义展开 +
length_map 桥 + sizeShowDups 承接。 -/
theorem sizeEnumOfVertexList [BEq α] [LawfulBEq α] [Inhabited α]
    (f : List α) (v : α) (vs : List (Option α)) :
    (enumOfVertexList f v vs).length = vs.length := by
  show ((showDups vs).map (fun u => indexf v u f)).length = vs.length
  rw [List.length_map, sizeShowDups]

/-- **HOL `hd_enum_of_vertexlist`**（tame_list.hl:13520 `!vs f v. ~(vs = []) /\
HD vs = SOME v /\ MEM v f ==> HD (enum_of_VertexList f v vs) = 0`）。证体：
calc 三步——enum/showDups/get! 定义性 defeq 折叠至 `indexf v v f ::` 形 +
head! iota + indexfRefl 直投（List.head!_map 不在册，calc defeq 面记档）。 -/
theorem hdEnumOfVertexlist [BEq α] [LawfulBEq α] [Inhabited α]
    {vs : List (Option α)} {f : List α} {v : α} (hvs : vs ≠ [])
    (hv : vs.head! = some v) (hvf : v ∈ f) :
    (enumOfVertexList f v vs).head! = 0 := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hvs
  have hb : b = some v := hv
  subst hb
  calc (enumOfVertexList f v (some v :: bs)).head!
      = (indexf v v f :: (showDups0 v bs).map (fun u => indexf v u f)).head! := rfl
    _ = indexf v v f := rfl
    _ = 0 := indexfRefl hvf

/-! ### §6 filter/last/all 家族（tame_list.hl:13538-:13556） -/

/-- **HOL `last_filter`**（tame_list.hl:13538 `!f xs. ~(xs = []) /\
f (LAST xs) ==> LAST (filter f xs) = LAST xs`）。证体：rconsButlast（批 52）
+ conv lhs 单侧换面保 RHS 原形 + filter_append/filter_singleton + hp 换装 +
Graphs `getLast!_append_of_ne_nil`。 -/
theorem lastFilter {α : Type*} [Inhabited α] {p : α → Bool} {xs : List α}
    (h : xs ≠ []) (hp : p xs.getLast!) : (xs.filter p).getLast! = xs.getLast! := by
  have hxs : xs = xs.dropLast ++ [xs.getLast!] := rconsButlast h
  have h1 : List.filter p [xs.getLast!] = [xs.getLast!] := by
    rw [List.filter_singleton, hp]; rfl
  have hne : [xs.getLast!] ≠ [] := by simp
  have h2 : (xs.dropLast.filter p ++ [xs.getLast!]).getLast!
      = [xs.getLast!].getLast! := getLast!_append_of_ne_nil hne
  have h3 : xs.filter p = xs.dropLast.filter p ++ [xs.getLast!] := by
    conv => lhs; rw [hxs]
    rw [List.filter_append, h1]
  rw [h3, h2]
  rfl

/-- **HOL `all_mem_filter`**（tame_list.hl:13548 `all (\t. MEM t f)
(MAP r (filter g vs)) = all (\t. MEM (r t) f) (filter g vs)`）。all_map 桥 +
comp beta rfl；MEM 谓词面 decide 折算须 [DecidableEq α] 实例参记档。 -/
theorem allMemFilter {α β : Type*} [DecidableEq α] (f : List α) (r : β → α)
    (g : β → Bool) (vs : List β) :
    ((vs.filter g).map r).all (fun t => decide (t ∈ f))
      = (vs.filter g).all (fun t => decide (r t ∈ f)) := by
  rw [List.all_map]
  rfl

/-! ### §7 hideDupsRec/indexToVertexList 尺寸件（tame_list.hl:13558-:13581） -/

/-- **HOL `size_hideDupsRec`**（tame_list.hl:13558 `!vs a. sizel (hideDupsRec
a vs) = sizel vs`）。证体：vs 归纳 generalizing a（some/none 分支同 §5 尾消
雷区）；`length (x :: l) = length l + 1` 头项无关——if 支免 split 直落。 -/
theorem sizeHideDupsRec [BEq α] (vs : List α) (a : α) :
    (hideDupsRec a vs).length = vs.length := by
  induction vs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [hideDupsRec, List.length_cons]
    exact congrArg (fun n => n + 1) (ih b)

/-- **HOL `size_indexToVertexList`**（tame_list.hl:13569 `!e f v. sizel
(indexToVertexList f v e) = sizel e`）。载体 Face 版（Enumerator.lean:54）；
证体：定义展开 + map_cons β 归一 + hideDups 展开 + length_map 桥 +
sizeHideDupsRec trans 收口。 -/
theorem sizeIndexToVertexList (f : Kepler.Graphs.Face)
    (v : Kepler.Graphs.Vertex) (e : List Nat) :
    (indexToVertexList f v e).length = e.length := by
  show (hideDups (e.map (fun k => f.nextVertices k v))).length = e.length
  cases e with
  | nil => rfl
  | cons c cs =>
    simp only [List.map_cons, hideDups, List.length_cons]
    have hm : (cs.map (fun k => f.nextVertices k v)).length = cs.length := by
      rw [List.length_map]
    exact congrArg (fun n => n + 1)
      ((sizeHideDupsRec _ (f.nextVertices c v)).trans hm)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；十二件正文 + 消费链槽全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.nextElListPairsEq
#print axioms Kepler.Text.TameSpine.cardLeSize
#print axioms Kepler.Text.TameSpine.betwnNil
#print axioms Kepler.Text.TameSpine.directedLengthNext
#print axioms Kepler.Text.TameSpine.sizeShowDups0
#print axioms Kepler.Text.TameSpine.sizeShowDups
#print axioms Kepler.Text.TameSpine.sizeEnumOfVertexList
#print axioms Kepler.Text.TameSpine.hdEnumOfVertexlist
#print axioms Kepler.Text.TameSpine.lastFilter
#print axioms Kepler.Text.TameSpine.allMemFilter
#print axioms Kepler.Text.TameSpine.sizeHideDupsRec
#print axioms Kepler.Text.TameSpine.sizeIndexToVertexList
-/

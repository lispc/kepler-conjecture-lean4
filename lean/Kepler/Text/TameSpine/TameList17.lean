/-
  Kepler.Text.TameSpine.TameList17 — B1 Tame_list 地基批 17：transform 定义层 +
  marked/HQYMRTX 族（tamespine-port-plan §4 批次表 B1 行；接续批 16 =
  TameList16.lean，批 16 终点 = HOL :10144（marked_conclusion :10071 已落，
  final_loops_list_iff :10050 已落）；本批起点 = HOL :9905
  marked_list_marked）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_defs.hl + tame_defs2.hl + tame_list.hl）：

  - transform 定义层进场（批 7/批 16 两次记账的「旗塔上游/reduction 波
    领土」）：`replace`（tame_defs.hl:317-320）↦ `replaceSpine`、
    `split_normal_list`（tame_defs2.hl:167-180）↦ `splitNormalListSpine`、
    `transform_list`（:458-467）↦ `transformListSpine`、
    `ntrans`/`rtrans`（:469-:473）↦ `ntransSpine`/`rtransSpine`、
    `transform_assumption(_v2)`（:568-:571）↦ `transformAssumptionSpine`；
  - 目标章 tame_list.hl :9905-:10211 十件：
    `marked_list_marked` :9905 / `AQIUNPP1` :9990 / `AQIUNPP2` :10004 /
    `transform_list_pair` :10018 / `AQIUNPP3` :10026 / `marked_translate`
    :10100 / `normal_list_in_dart_of_loop2` :10146 / `HQYMRTX1_list` :10165 /
    `HQYMRTX2_list` :10188 / `HQYMRTX3_list` :10201
    （`final_loops_list_iff` :10050 / `marked_conclusion` :10071 批 16 已落
    直引；`PMBRINH` :9903 是 good_list_nodes_quotient 别名，零移植；
    `marked_lemma_yz_in_face` :10214 起留给批 18）。

  载体折算（沿批 1-16 约定）：transform_list 的打包参数 `(N, r)` ↦ Prod、
  `POWER i`（函数迭代）↦ `Function.iterate · i`、split_normal_list 的
  `upt 1 k` ↦ `List.range' 1 k`（HOL `upt m n = [m..n]` 双闭 = iota 形，
  批 13 iota 记账同源）、`betwn` ↦ `Kepler.Graphs.between`（批 3）、
  `replace` 原地递归直移植、`sizel (filter (\t. t = x) (flatten L))` ↦
  `length`（批 12 sizel 记账）、split_normal_list 的 `L` 是**顶点面表**
  （`fgraph ℕ`，HOL 同型：`sz` 数顶点重数、`sz (FST x)` 数 dart 首顶点——
  与 dart 面 `find_face` 回路无类型冲突，HOL list_hypermap-compiled.hl
  :53 `find_face L d = find_list (list_of_faces L) d` 侦察记档）、
  `final_list` 的 Prop-if ↦ Classical（noncomputable，批 12 hypY 同款）、
  marked_list ↦ `MarkedListSpineFull`（批 13 全量 9 合取进场；本批各件
  HOL 证明消费旗塔双分支，故取全量，前 7 块版 `MarkedListSpine` 经 .1
  投影零收窄消费批 7-16 诸件）、`is_marked` 的 IsNormalFamily 证明参
  显式量化入结论（批 12 lQSpine「Skolem 函数无证明参」折算同款）、
  `hyp'q = l'q` 合取沿批 12 hypQLq 的证明参全称化形（rfl 平凡真）。

  诚实记账（本批零止损件）：批 17 十件 + 定义层六件全部真证，零新增
  记账债（NEW_SORRY_ALLOW = 0）。公理审计继承注记：
  `markedListMarked`/`markedTranslate`/`hqymrtx1List` 的 sorryAx 系经批 16
  在案记账件 `quotient_list_iso_quotient` :8223（P1/P2 私件债）与
  `marked_list_is_node_nondegenerate` :9362（ql 侧支债）传入（批 16 交付
  报告已记「下游 iso capstone 同步」），本批照常消费其陈述，零收窄。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 18 接续点：HOL :10214 `marked_lemma_yz_in_face` 起的 marked
  几何章（marked_lemma_yz_in_face :10214 / mem_l_z_dart :10234 起，依
  赖本批 marked_translate + List_hypermap.face_of_list 桥）。
-/

import Kepler.Text.TameSpine.TameList16

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl eList fList GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph between)
open Kepler.Text (orbitMap setOfOrbits)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem dart_in_face findFaceDarts_ex_of_self
  findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup
  mem_darts_of_mem_findFace nextEl_mem_of_mem flatten_nodup_mem
  faceMap_hypermapOfList nodeMap_hypermapOfList GoodListNodesTl)

/-! ### §0 transform 定义层（tame_defs.hl:317-320 + tame_defs2.hl:167-180、
:458-:473、:568-:571） -/

/-- HOL `replace`（tame_defs.hl:317-320）逐句镜像：
`replace x ys [] = []`；`replace x ys (z::zs) = if z = x then APPEND ys zs
else z :: replace x ys zs`——首处命中整段替换（真支不递归，保留尾部）。 -/
def replaceSpine {α : Type*} [DecidableEq α] (x : α) (ys : List α) :
    List α → List α
  | [] => []
  | z :: zs => if z = x then ys ++ zs else z :: replaceSpine x ys zs

/-- HOL `split_normal_list`（tame_defs2.hl:167-180）逐句镜像。

载体记账：`L` 是顶点面表（`fgraph ℕ`，HOL 同型）；`sz` 数顶点 `v` 在
`flatten L` 的重数，`sz (FST x)` 数 dart `x` 首顶点重数（HOL 无类型冲突，
见模块头注侦察记档）；`upt 1 k` ↦ `List.range' 1 k`（双闭 = iota 形）；
`betwn` ↦ `Kepler.Graphs.between`（批 3）；`n_list L POWER i` ↦
`Function.iterate (nList L) i`。 -/
noncomputable def splitNormalListSpine (L : fgraph ℕ) (r f : List (ℕ × ℕ))
    (ram1 ram2 : ℕ × ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  let ram1' := nextEl r ram1
  let ram2' := nextEl r ram2
  let sz : ℕ → ℕ := fun v => (L.flatten.filter (fun t => decide (t = v))).length
  let nd : ℕ × ℕ → List (ℕ × ℕ) :=
    fun x => (List.range' 1 (sz x.1)).map fun i => (nList L)^[i] x
  let new2 := between f ram1 ram2'
  let new1 := (new2.map nd).flatten
  let f1 := [ram1'] ++ between r ram1' ram2 ++ [ram2]
  let f2 := [ram2'] ++ between r ram2' ram1 ++ [ram1]
  (new1.reverse ++ f1, f2 ++ new2)

open Classical in
/-- HOL `transform_list`（tame_defs2.hl:458-467）逐句镜像
（打包参数 `(N, r)` ↦ Prod；`final_list` 的 Prop-if 经 Classical 求决，
noncomputable，批 12 hypY 同款）。 -/
noncomputable def transformListSpine (L : fgraph ℕ) (x : ℕ × ℕ)
    (Nr : List (List (ℕ × ℕ)) × List (ℕ × ℕ)) :
    List (List (ℕ × ℕ)) × List (ℕ × ℕ) :=
  let N := Nr.1
  let r := Nr.2
  let y := lYSpine L r x
  let z := lZSpine L N r x
  let ram2 := prevEl r z
  let f := findFaceDarts L y
  let split := splitNormalListSpine L r f y ram2
  if finalListSpine L r then (N, r)
  else (replaceSpine r [split.2] N ++ [split.1], split.2)

/-- HOL `ntrans`（tame_defs2.hl:469-471）
`ntrans L N r x i = FST ((transform_list L x POWER i) (N,r))`。 -/
noncomputable def ntransSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ) : List (List (ℕ × ℕ)) :=
  ((transformListSpine L x)^[i] (N, r)).1

/-- HOL `rtrans`（tame_defs2.hl:472-473）
`rtrans L N r x i = SND ((transform_list L x POWER i) (N,r))`。 -/
noncomputable def rtransSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  ((transformListSpine L x)^[i] (N, r)).2

/-- HOL `transform_assumption`（tame_defs2.hl:568-571）
`transform_assumption_v2 L <=> (!N r x. good_list L /\ good_list_nodes L /\
marked_list L N r x ==> marked_list L (ntrans L N r x 1)
(rtrans L N r x 1) x)`——`good_list L` 由证人 `hL` 显式入参承载（批 7
NormalListSpine/MarkedListSpine 约定），marked_list ↦ 全量
`MarkedListSpineFull`（批 13）。 -/
def transformAssumptionSpine (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ),
    GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
      MarkedListSpineFull hL (ntransSpine L N r x 1) (rtransSpine L N r x 1) x

/-! ### §1 marked_list_marked（tame_list.hl:9905-:9987） -/

/-- **HOL `marked_list_marked`**（tame_list.hl:9905-:9987）
`good_list L /\ good_list_nodes L /\ marked_list L N r x ==> is_marked
(hypermap_of_list L, loop_family_of_list N, loop_of_list r, x)`——九合取塔
装配：合取 1-4 = 批 7 markList 五桥前四；合取 5（商 Simple）=
quotient_all_uniq（批 9）+ simple_hypermap_list（批 14）+
quotient_list_iso_quotient（批 16）+ iso_simple_imp（批 15，经 Iso.symm）；
合取 6 = marked_list_is_node_nondegenerate（批 16）；合取 7 =
marked_list_edge_map_final（批 8）；合取 8/9 = marked_list_empty_flagged /
marked_list_s_flagged（批 13）经 final_loops_list_iff（批 16）换向。
载体记账：`is_marked` 的 IsNormalFamily 证明参在 Lean 提升为参数
（Hypermap.lean:10359），此处全称量化入结论（零收窄；两证同一 Prop 经
证明无关性可交换）。 -/
theorem markedListMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    ∀ hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N),
      (hypermapOfList L hL).IsMarked (loopFamilyOfListSpine N) hnf
        (loopOfListSpine r) x := by
  have hres := hm.1.1
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hgnq : GoodListNodesTl (quotientListSpine L N)
    (goodListQuotient L hL hn hnedg hunL) :=
    goodListNodesQuotient L hL hgn hn hnedg hunL
  have hiff := finalLoopsListIff L hL hrN hn
  intro hnf
  refine ⟨markListRestricted hL hm.1, markListMemFamily hL hm.1,
    markListMemLoop hL hgn hm.1, markListLoopEqFaceMap hL hm.1, ?_, ?_,
    markedListEdgeMapFinal hL hm.1, ?_, ?_⟩
  · -- 合取 5：商 hypermap Simple（iso 运输）
    have hsim : (hypermapOfList (quotientListSpine L N)
        (goodListQuotient L hL hn hnedg hunL)).Simple :=
      simpleHypermapList (quotientListSpine L N)
        (goodListQuotient L hL hn hnedg hunL) hgnq (quotientAllUniq hL hm.1)
    exact isoSimple (quotientListIsoQuotient L hL hgn hres hn hnedg hunL).symm
      hsim
  · -- 合取 6：商 node 非退化（批 16）
    exact markedListIsNodeNondegenerate L hL hgn hres hn hnedg hunL hgnq hm.1
  · -- 合取 8：final 环 ⇒ empty_flagged
    intro hcon
    exact markListEmptyFlagged L hL hgn hunL hm (hiff.mp hcon)
  · -- 合取 9：非 final 环 ⇒ s_flagged
    intro hLnot
    exact markListSFlagged L hL hgn hunL hm (fun hcon => hLnot (hiff.mpr hcon))

/-! ### §2 AQIUNPP 族 + transform_list_pair（tame_list.hl:9990-:10047） -/

/-- **HOL `AQIUNPP1`**（tame_list.hl:9990-:10002）
`transform_assumption_v2 L /\ good_list L /\ good_list_nodes L /\
marked_list L N r x ==> normal_list L (ntrans L N r x 1)`——
transform_assumption 展开 + 换位 marked_list 首二合取直取（HOL
ASM_MESON_TAC[marked_list; transform_assumption]）。 -/
theorem aqiunpp1 (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    NormalListSpine hL (ntransSpine L N r x 1) :=
  (hta N r x hgn hm).1.2.1

/-- **HOL `AQIUNPP2`**（tame_list.hl:10004-:10016）
`transform_assumption_v2 L /\ good_list L /\ good_list_nodes L /\
marked_list L N r x ==> marked_list L (ntrans L N r x 1)
(rtrans L N r x 1) x`——transform_assumption 定义性直取。 -/
theorem aqiunpp2 (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    MarkedListSpineFull hL (ntransSpine L N r x 1) (rtransSpine L N r x 1) x :=
  hta N r x hgn hm

/-- **HOL `transform_list_pair`**（tame_list.hl:10018-:10024）
`transform_list L x (N,r) = (ntrans L N r x 1, rtrans L N r x 1)`——
ntrans/rtrans 定义 + POWER_1 + Prod η（HOL REWRITE_TAC[ntrans; rtrans;
PAIR; POWER_1]）。 -/
theorem transformListPair (L : fgraph ℕ) (x : ℕ × ℕ)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) :
    transformListSpine L x (N, r)
      = (ntransSpine L N r x 1, rtransSpine L N r x 1) := rfl

/-- **HOL `AQIUNPP3`**（tame_list.hl:10026-:10047）归纳内核：i 归纳且
N/r/x 随步换槽（HOL 归纳步 REWRITE_TAC[transform_list_pair] 后
GSYM ntrans/rtrans 重实例化归纳假设——Lean 侧归纳假设须对 N r x 全称
方能换槽，私有 aux 承载）。 -/
private theorem aqiunpp3_aux (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL) :
    ∀ (i : ℕ) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ},
      MarkedListSpineFull hL N r x →
      MarkedListSpineFull hL (ntransSpine L N r x i) (rtransSpine L N r x i) x := by
  intro i
  induction i with
  | zero => intro N r x hm; exact hm
  | succ k ih =>
    intro N r x hm
    have h1 := hta N r x hgn hm
    have e1 : ntransSpine L N r x (k + 1)
        = ntransSpine L (ntransSpine L N r x 1) (rtransSpine L N r x 1) x k := by
      show ((transformListSpine L x)^[k + 1] (N, r)).1 = _
      rw [Function.iterate_succ_apply, transformListPair L x N r]
      rfl
    have e2 : rtransSpine L N r x (k + 1)
        = rtransSpine L (ntransSpine L N r x 1) (rtransSpine L N r x 1) x k := by
      show ((transformListSpine L x)^[k + 1] (N, r)).2 = _
      rw [Function.iterate_succ_apply, transformListPair L x N r]
      rfl
    rw [e1, e2]
    exact ih h1

/-- **HOL `AQIUNPP3`**（tame_list.hl:10026-:10047）
`!L i N r x. transform_assumption_v2 L /\ good_list L /\ good_list_nodes L /\
marked_list L N r x ==> marked_list L (ntrans L N r x i)
(rtrans L N r x i) x`——见 aqiunpp3_aux。 -/
theorem aqiunpp3 (L : fgraph ℕ) (hL : GoodList L) (i : ℕ)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    MarkedListSpineFull hL (ntransSpine L N r x i) (rtransSpine L N r x i) x :=
  aqiunpp3_aux L hL hta hgn i hm

/-! ### §3 marked_translate + normal_list_in_dart_of_loop2
（tame_list.hl:10100-:10162） -/

/-- **HOL `marked_translate`**（tame_list.hl:10100-:10144）
`good_list L /\ good_list_nodes L /\ marked_list L N r d /\
~final_list L r ==> (hyp'm ... = l'm L r d /\ hyp'p ... = l'p L N r d /\
hyp'q ... = l'q L N r d /\ hyp'y ... = l'y L r d /\ hyp'z ... = l'z L N r d /\
is_marked (...) /\ ~(loop_of_list r IN final_loops ...) /\
is_split_condition ... d)`——hyp↔l' 五桥（批 12 hypMLm/hypPLp/hypQLq/hypYL/
hypZLz）+ marked_list_marked（本批）+ final_loops_list_iff（批 16）+
split_condition_list_split（批 12）。载体记账：hyp'q 合取沿批 12 hypQLq
的证明参全称化形（对一切 IsMarked/非 final 证人 rfl 成立，零收窄）。 -/
theorem markedTranslate (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r d) (hf : ¬finalListSpine L r) :
    ∀ hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N),
      (hypermapOfList L hL).hypM (loopFamilyOfListSpine N) (loopOfListSpine r) d
          = lMSpine L r d ∧
        (hypermapOfList L hL).hypP (loopFamilyOfListSpine N)
            (loopOfListSpine r) d = lPSpine L N r d ∧
        (∀ (hmk : (hypermapOfList L hL).IsMarked (loopFamilyOfListSpine N) hnf
              (loopOfListSpine r) d)
          (hl : loopOfListSpine r ∉ (hypermapOfList L hL).finalLoops
            (loopFamilyOfListSpine N)),
          (hypermapOfList L hL).hypQ hmk hl = lQSpine L hL hnf hmk hl) ∧
        (hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
            (loopOfListSpine r) d = lYSpine L r d ∧
        (hypermapOfList L hL).hypZ (loopFamilyOfListSpine N)
            (loopOfListSpine r) d = lZSpine L N r d ∧
        (hypermapOfList L hL).IsMarked (loopFamilyOfListSpine N) hnf
          (loopOfListSpine r) d ∧
        loopOfListSpine r ∉ (hypermapOfList L hL).finalLoops
          (loopFamilyOfListSpine N) ∧
        (hypermapOfList L hL).IsSplitCondition (loopFamilyOfListSpine N)
          (loopOfListSpine r) d := by
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hiff := finalLoopsListIff L hL hm.1.2.2.1 hm.1.2.1
  intro hnf
  refine ⟨hypMLm L hL hgn hunL hnext hsc, hypPLp L hL hgn hunL hnext hsc,
    fun hmk _ => rfl, hypYL L hL hgn hunL hnext hsc,
    hypZLz L hL hgn hunL hnext hsc,
    markedListMarked L hL hgn hunL hm hnf, ?_,
    splitConditionListSplit L hL hgn hunL hsc⟩
  intro hcon
  exact hf (hiff.mp hcon)

/-- **HOL `normal_list_in_dart_of_loop2`**（tame_list.hl:10146-:10162）
`normal_list L N /\ MEM r N ==> (in_dart_of_loop u (loop_of_list r) <=>
MEM u r)`——normal_list_uniq_nonnil（批 6）+ in_dart_loop_of_list（批 6）
（载体记账：`in_dart_of_loop` ↦ Loop.darts 成员，批 6）。 -/
theorem normalListInDartOfLoop2 (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    (hn : NormalListSpine hL N) (hr : r ∈ N) (u : ℕ × ℕ) :
    u ∈ (loopOfListSpine r).darts ↔ u ∈ r := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  exact inDartLoopOfList hr1 hr2 u

/-! ### §4 HQYMRTX 族（tame_list.hl:10165-:10211） -/

/-- **HOL `HQYMRTX1_list`**（tame_list.hl:10165-:10186）
`good_list L /\ good_list_nodes L /\ marked_list L N r x /\
~final_list L r ==> MEM (l'z L N r x) r /\ (!i. 1 <= i /\
i <= SUC (l'm L r x) ==> ~(l'z L N r x = (f_list L POWER i) x))`——
Hypermap.lemmaHQYMRTX（Hypermap.lean hqymrtx）+ marked_translate 运输 +
face_map_list_power（批 12 fListExtFListPower 幂桥）+ marked_conclusion
（批 16）给 x ∈ list_of_darts L。 -/
theorem hqymrtx1List (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lZSpine L N r x ∈ r ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ lMSpine L r x + 1 →
        lZSpine L N r x ≠ (fList L)^[i] x := by
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  obtain ⟨-, -, -, -, -, -, hxd, -, -⟩ :=
    markedConclusion L hL hgn hunL hm.1 hf
  have hnf := normalListNormal hL hgn hm.1.1 hn
  have hmark := markedListMarked L hL hgn hunL hm hnf
  have hLnot : loopOfListSpine r ∉
      (hypermapOfList L hL).finalLoops (loopFamilyOfListSpine N) := fun hcon =>
    hf ((finalLoopsListIff L hL hrN hn).mp hcon)
  have hq := (hypermapOfList L hL).hqymrtx hmark hLnot
  have hz : (hypermapOfList L hL).hypZ (loopFamilyOfListSpine N)
      (loopOfListSpine r) x = lZSpine L N r x :=
    hypZLz L hL hgn hunL hnext hsc
  rw [hz] at hq
  refine ⟨(inDartLoopOfList hr1 hr2 _).mp hq.1, ?_⟩
  intro i hi1 hi2 hcon
  refine hq.2 i hi1 ?_ ?_
  · rw [hypMLm L hL hgn hunL hnext hsc]
    exact hi2
  · rw [fListExtFListPower L hL hxd i]
    exact hcon

/-- **HOL `HQYMRTX2_list`**（tame_list.hl:10188-:10199）
`good_list L /\ good_list_nodes L /\ marked_list L N r x /\
~final_list L r ==> ~(x = l'y L r x)`——lemma_on_hyp_y（Hypermap.lean
on_hypY）node 支 + marked_translate 的 hyp'y = l'y 运输。 -/
theorem hqymrtx2List (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ¬(x = lYSpine L r x) := by
  intro hcon
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have h3 := ((hypermapOfList L hL).on_hypY hsplit).2.2
  rw [hypYL L hL hgn hunL hnext hsc, ← hcon] at h3
  exact h3 rfl

/-- **HOL `HQYMRTX3_list`**（tame_list.hl:10201-:10211）
`good_list L /\ good_list_nodes L /\ marked_list L N r x /\
~final_list L r ==> ~(l'y L r x = l'z L N r x)`——lemma_on_hyp_z
（Hypermap.lean on_hypZ）node 支 + marked_translate 的 hyp'y/hyp'z 运输。 -/
theorem hqymrtx3List (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ¬(lYSpine L r x = lZSpine L N r x) := by
  intro hcon
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hsplit := splitConditionListSplit L hL hgn hunL hsc
  have h3 := ((hypermapOfList L hL).on_hypZ hsplit).1
  rw [hypYL L hL hgn hunL hnext hsc, hypZLz L hL hgn hunL hnext hsc, hcon] at h3
  exact h3 rfl

end Kepler.Text.TameSpine

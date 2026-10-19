/-
  Kepler.Text.TameSpine.TameList21 — B1 Tame_list 地基批 21：Seed 章三连
  （tamespine-port-plan §4 批次表 B1 行；接续批 20 = TameList19→TameList20.lean，
  批 20 终点 = HOL :10592（e_list_pairs_rev 已落，:10595 起留本批）；
  本批起点 = HOL :10595）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10595-:10650）——Seed 章三连 3 枚 +
  §0 私件 2 枚，共 5 枚全量：

  主件：`fgraph_seed` :10595-:10602
  `!p. fgraph (Seed p) = [iota 0 (maxGon p);rev (iota 0 (maxGon p))]`；
  `uniq_list_of_darts_seed` :10604-:10636
  `!p. uniq(list_of_darts(fgraph (Seed p)))`；
  `all_nonempty_seed` :10638-:10650
  `!p. all (\l. ~(l = [])) (fgraph (Seed p))`。
  :10652 `mem_transpose_seed` 起自然边界收批（留批 22）。

  层级侦察定论（全量形记档，本批新核）：
  · HOL `fgraph`（tame_defs.hl:433 `MAP FST (faces g)`）在 Lean 是投影函数
    （Lean `fgraph` 已为类型缩写 `List (List α)`），按批 2 §1 先例 ↦
    `facesVertexLists`（Graph→List (List ℕ) 投影）；`Seed` ↦
    `Kepler.Graphs.Seed`（AFI Plane.thy 载体，Plane.lean:67
    `Seed p = graph (maxGon p)`）；`maxGon` ↦ `Kepler.Graphs.maxGon`
    （Plane.lean:33，同形 p + 3）；`iota 0 k` ↦ `List.range k`
    （批 2 zip·iota 家族折算）。
  · graphl/LET_THM/GRAPH/MAP 展开面与 lower_case/upt0（tame_list.hl:614/
    :1397）全部为定义方程：批 2 `graphAlt` 已证 `graph n` 四字段显式形
    （rfl），本批 `fgraphSeed` 一步 rfl 收口，零新增侦察件。
  · `uniq_list_of_darts_seed` 的 HOL 链 list_of_darts_cons/nil + cats0 +
    cat_uniq（↦ `List.Nodup.append` + `List.Disjoint`，batteries
    List.Disjoint = 无公共元谓词）+ uniq_list_pairs（list_hypermap-
    compiled.hl:284，本批 §0 私件 listPairsNodupD 同证重推导：
    getElem?-injection 路线——`List.nodup_iff_getElem?_ne_getElem?` +
    `List.getElem_zip` 首分量投影 + `List.Nodup.getElem_inj_iff`，与 HOL
    uniq_nthP/nth_list_pairs 长链同构）+ iota_uniq（↦ `List.nodup_range`）
    + rev_uniq（↦ `List.nodup_reverse`）。
  · hasP/NOT_EXISTS 不交支（证明体 :10623-:10635）= 两面 dart 互斥：
    PAIR_SURJECTIVE + mem_rev + list_pairs_iota（批 2 `memListPairsIota`，
    tame_list.hl:727）+ list_pairs_rev_iota（批 2 `memListPairsRevIota`，
    :764）展开后 ARITH——门槛是 k = maxGon p = p + 3 ≥ 3（k = 2 退化时
    两面 dart 相撞 (0,1)，HOL 的 ARITH_TAC 恰由 maxGon 展开排除）；
    本批 §0 私件 listPairsRangeReverseDisjointD 显式持 `3 ≤ k` 门槛。

  依赖面（全为在案真件，零新增债）：批 2 `facesVertexLists`/`graphAlt`/
  `memListPairsIota`/`memListPairsRevIota` + Mathlib
  List.nodup_range/nodup_reverse/Nodup.append +
  nodup_iff_getElem?_ne_getElem?/Nodup.getElem_inj_iff/getElem_zip +
  batteries List.Disjoint。

  载体折算（沿批 1-20 约定）：`fgraph`（函数）↦ `facesVertexLists`；
  `Seed`/`maxGon` ↦ Kepler.Graphs 同名件；`iota 0 k` ↦ `List.range k`；
  `rev` ↦ `List.reverse`；`uniq` ↦ `List.Nodup`；`list_of_darts` ↦
  `Kepler.Assembly.listOfDarts`；`all (\l. ~(l = []))` ↦
  `∀ l ∈ L, l ≠ []`（GoodListDefs GoodList 第二合取项同形）。

  诚实记账：本批五件全部真证，零新增记账债（零止损件）。三主件的 HOL
  展开面（fgraph/SEED/faces/graphl/LET_THM/GRAPH/MAP/lower_case/upt0/
  list_of_darts_cons/nil/cats0/Seq.all/size_rev/size_iota）在 Lean 侧全部
  为定义方程与 List.length_* simp 面，无信息丢失。批 2 记账在册的
  :1249 list_of_darts_rev_uniq（NEEDS：reverse-lods nodup 迁移链）与本批
  无涉（Seed 章走面级不交直证，不依赖该件）。:10812 有同名 `fgraph_seed`
  再证（dih2k_list 展开面，属后续章），不在本批射程。公理审计实测
  （#print axioms，2026-10-19，隔离 clone /tmp/p4t21）：fgraphSeed 零公理，
  uniqListOfDartsSeed 仅标准三 [propext, Classical.choice, Quot.sound]，
  allNonemptySeed 仅 propext + Quot.sound（标准三子集），零 sorryAx、
  零记账传入（审计锚见文末注释块）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 22 接续点：HOL :10652 `mem_transpose_seed`
  （`!p d. MEM d (list_of_darts (fgraph (Seed p))) ==> MEM (SND d,FST d)
  (list_of_darts (fgraph (Seed p)))`，后随 `good_list_seed` :10680——
  Seed 章 good_list 收口件，走本批三连 + GoodList 三合取直拼）。
-/

import Kepler.Text.TameSpine.TameList20

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs listOfDarts)
open Kepler.Graphs (fgraph Seed maxGon)

/-! ### §0 私件引擎（Seed 章展开面：list_pairs nodup + 两面 dart 互斥） -/

/-- **HOL `uniq_list_pairs`**（ssreflect list_hypermap-compiled.hl:284-294
`uniq s ==> uniq (list_pairs s)`）的 List ℕ 面（批 19 私件引擎惯例，List ℕ
层同证重推导）。getElem?-injection 路线：`list_pairs l` 第 i 项首分量即
`l[i]`（`List.getElem_zip` 投影），nodup 表 getElem 单射逼 i = j。 -/
private theorem listPairsNodupD {l : List ℕ} (hnd : l.Nodup) :
    (listPairs l).Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hjl hopt
  rw [List.getElem?_eq_getElem (hij.trans hjl), List.getElem?_eq_getElem hjl] at hopt
  have hpair := Option.some.inj hopt
  unfold listPairs at hpair
  rw [List.getElem_zip, List.getElem_zip] at hpair
  have hijeq : i = j :=
    (List.Nodup.getElem_inj_iff hnd).mp (congrArg Prod.fst hpair)
  omega

/-- Seed 两面 dart 互斥（HOL `uniq_list_of_darts_seed` 证明体 :10623-:10635
hasP/NOT_EXISTS 支的提取件：`list_pairs_iota`（tame_list.hl:727）+
`list_pairs_rev_iota`（:764）展开后纯算术；门槛 `3 ≤ k` 即 maxGon 展开
p + 3 ≥ 3，k = 2 退化时两面 dart 相撞 (0,1)）。 -/
private theorem listPairsRangeReverseDisjointD {k : ℕ} (hk : 3 ≤ k) :
    List.Disjoint (listPairs (List.range k)) (listPairs (List.range k).reverse) := by
  intro d hd1 hd2
  obtain ⟨i, j, rfl⟩ : ∃ i j : ℕ, d = (i, j) := ⟨d.1, d.2, rfl⟩
  rw [memListPairsIota] at hd1
  rw [memListPairsRevIota (k := k) (by omega)] at hd2
  rcases hd1 with (⟨h1, rfl⟩ | ⟨h1, rfl⟩) <;>
    rcases hd2 with (⟨h2, h3⟩ | ⟨h2, h3, h4⟩) <;> omega

/-! ### §1 fgraph_seed（tame_list.hl:10595-:10602） -/

/-- **HOL `fgraph_seed`**（tame_list.hl:10595-:10602）
`!p. fgraph (Seed p) = [iota 0 (maxGon p);rev (iota 0 (maxGon p))]`
——HOL REWRITE[fgraph;SEED;faces;graphl;LET_THM;GRAPH;MAP] +
lower_case/upt0 的 Lean 面：`Seed p = graph (maxGon p)`（Plane.lean:67）
与批 2 `graphAlt` 四字段显式形全部为定义方程，`facesVertexLists` 投影后
一步 rfl 收口（`iota 0 k` ↦ `List.range k`，`rev` ↦ `List.reverse`）。 -/
theorem fgraphSeed (p : ℕ) :
    facesVertexLists (Seed p) =
      [List.range (maxGon p), (List.range (maxGon p)).reverse] := rfl

/-! ### §2 uniq_list_of_darts_seed（tame_list.hl:10604-:10636） -/

/-- **HOL `uniq_list_of_darts_seed`**（tame_list.hl:10604-:10636）
`!p. uniq(list_of_darts(fgraph (Seed p)))`——两面清单经 `listOfDarts` 展开
为 `list_pairs 面1 ++ list_pairs 面2`，`List.Nodup.append` 收口：两侧
`listPairsNodupD`（= uniq_list_pairs）+ `listPairsRangeReverseDisjointD`
（= cat_uniq 的 hasP 支）；`iota_uniq`/`rev_uniq` ↦ `List.nodup_range`/
`List.nodup_reverse`。 -/
theorem uniqListOfDartsSeed (p : ℕ) :
    (listOfDarts (facesVertexLists (Seed p))).Nodup := by
  have hk : 3 ≤ maxGon p := by
    show 3 ≤ p + 3
    omega
  rw [fgraphSeed p]
  simp only [listOfDarts, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  refine List.Nodup.append (listPairsNodupD List.nodup_range)
    (listPairsNodupD (List.nodup_reverse.mpr List.nodup_range)) ?_
  exact listPairsRangeReverseDisjointD hk

/-! ### §3 all_nonempty_seed（tame_list.hl:10638-:10650） -/

/-- **HOL `all_nonempty_seed`**（tame_list.hl:10638-:10650）
`!p. all (\l. ~(l = [])) (fgraph (Seed p))`——HOL Seq.all/size_eq0/
size_rev/size_iota + ARITH 的 Lean 面：两面长 = maxGon p = p + 3 ≥ 3
（`List.length_range`/`List.length_reverse`），`∀ l ∈ L, l ≠ []` 形
（GoodList 第二合取项同形）。 -/
theorem allNonemptySeed (p : ℕ) :
    ∀ l ∈ facesVertexLists (Seed p), l ≠ [] := by
  have hk : 3 ≤ maxGon p := by
    show 3 ≤ p + 3
    omega
  rw [fgraphSeed p]
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · intro hnil
    have h0 : (List.range (maxGon p)).length = 0 := by
      rw [hnil]; rfl
    rw [List.length_range] at h0
    omega
  · rcases List.mem_cons.mp hl with rfl | hl
    · intro hnil
      have h0 : ((List.range (maxGon p)).reverse).length = 0 := by
        rw [hnil]; rfl
      rw [List.length_reverse, List.length_range] at h0
      omega
    · exact absurd hl (by simp)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.fgraphSeed
#print axioms Kepler.Text.TameSpine.uniqListOfDartsSeed
#print axioms Kepler.Text.TameSpine.allNonemptySeed
-/

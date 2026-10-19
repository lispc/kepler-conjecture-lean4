/-
  Kepler.Text.TameSpine.TameList22 — B1 Tame_list 地基批 22：Seed 章收口
  （tamespine-port-plan §4 批次表 B1 行；接续批 21 = TameList20→TameList21.lean，
  批 21 终点 = HOL :10650（all_nonempty_seed 已落，:10652 起留本批）；
  本批起点 = HOL :10652）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10652-:10686）——Seed 章收口
  主件 2 枚 + §0 私件 1 枚，共 3 枚全量：

  主件：`mem_transpose_seed` :10652-:10678
  `!p d. MEM d (list_of_darts (fgraph (Seed p))) ==> MEM (SND d,FST d)
  (list_of_darts (fgraph (Seed p)))`；
  `good_list_seed` :10680-:10686
  `!p. good_list (fgraph (Seed p))`（HOL 证体一行 REWRITE_TAC[
  List_hypermap.good_list;mem_transpose_seed;all_nonempty_seed;
  uniq_list_of_darts_seed]，Lean 面同构：批 21 三连 + 匿名构造子直拼）。
  :10690 `list_of_elements_seed` 起自然边界收批（留批 23）。:10812 有同名
  `fgraph_seed` 再证（dih2k_list 展开面），属后续章，不在本批射程。

  层级侦察定论（全量形记档，本批新核）：
  · mem_transpose_seed 证明体（:10657-:10677）展开面 SEED/graphl/LET_THM/
    fgraph_graph/MAP + list_of_darts_cons/nil + Seq.mem_cat + PAIR_SURJECTIVE
    全为定义方程与已知折算：批 21 `fgraphSeed` + listOfDarts simp 面 +
    obtain ⟨i,j,rfl⟩ 三步到位；核心 = 两面 list_pairs 的 dart 转置闭合
    2×2 逐支——`list_pairs_iota`（批 2 `memListPairsIota`，tame_list.hl:727）
    × `list_pairs_rev_iota`（批 2 `memListPairsRevIota`，:764）往返 +
    MEM 算术（omega），与 HOL 的 REWRITE + ARITH_TAC 链同构。
  · `good_list`（list_hypermap-compiled.hl:63 三合取 `uniq (list_of_darts L)
    /\ all (\l. ~(l = [])) L /\ (!d. MEM d … ==> MEM (SND d,FST d) …)`）↦
    `Kepler.Assembly.GoodList`（GoodListDefs.lean:72 逐句镜像），第三合取
    项形恰为本批 mem_transpose_seed。
  · 门槛 `3 ≤ maxGon p`（k = 2 退化两面 dart 相撞，HOL ARITH_TAC 由
    maxGon = p + 3 展开排除）沿批 21 私件惯例在 §0 显式持有。

  依赖面（全为在案真件，零新增债）：批 21 `fgraphSeed`/`uniqListOfDartsSeed`/
  `allNonemptySeed` + 批 2 `memListPairsIota`/`memListPairsRevIota` +
  Kepler.Assembly `GoodList`（GoodListDefs）+ Mathlib List.mem_append。

  载体折算（沿批 1-21 约定）：`fgraph`（函数）↦ `facesVertexLists`；
  `Seed`/`maxGon` ↦ Kepler.Graphs 同名件（Plane.lean:67/:33）；`iota 0 k` ↦
  `List.range k`；`rev` ↦ `List.reverse`；`uniq` ↦ `List.Nodup`；
  `list_of_darts` ↦ `Kepler.Assembly.listOfDarts`；`MEM` ↦ `∈`；
  `good_list` ↦ `Kepler.Assembly.GoodList`。

  诚实记账：本批三件全部真证，零新增记账债（零止损件）。good_list_seed
  依批 21 三连（其公理面 propext/Classical.choice/Quot.sound 标准三在案），
  本批零新增外部依赖。公理审计实测（#print axioms，2026-10-19，隔离 clone
  /tmp/p4t21）：memTransposeSeed/memAppendTransposeD 仅标准三
  [propext, Classical.choice, Quot.sound]，goodListSeed 同标准三（批 21
  三连传递），零 sorryAx、零记账传入（审计锚见文末注释块）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 23 接续点：HOL :10690 `list_of_elements_seed`
  （`!p. list_of_elements (fgraph (Seed p)) = REVERSE (upt 0 (p+3))`，
  证体 :10693-:10707 undup_cat/undup_id 面起）。
-/

import Kepler.Text.TameSpine.TameList21

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs listOfDarts GoodList)
open Kepler.Graphs (fgraph Seed maxGon)

/-! ### §0 私件引擎（Seed 章 dart 转置闭合：两面 list_pairs 2×2 逐支往返） -/

/-- **HOL `mem_transpose_seed` 证明体核**（tame_list.hl:10658-:10677 的
List ℕ 面：`list_pairs_iota`（:727）+ `list_pairs_rev_iota`（:764）展开后
REWRITE + ARITH 的逐支往返）。门槛 `3 ≤ k` 即 maxGon 展开 p + 3 ≥ 3
（批 21 私件同款；k = 1 时 list_pairs 单点自环已闭合、k = 2 两面 dart
相撞仍闭合，门槛取宽即可，本批持 3 ≤ k 与批 21 对齐）。 -/
private theorem memAppendTransposeD {k : ℕ} (hk : 3 ≤ k) {d : ℕ × ℕ}
    (hd : d ∈ listPairs (List.range k) ++ listPairs (List.range k).reverse) :
    (d.2, d.1) ∈ listPairs (List.range k) ++ listPairs (List.range k).reverse := by
  obtain ⟨i, j, rfl⟩ : ∃ i j : ℕ, d = (i, j) := ⟨d.1, d.2, rfl⟩
  show (j, i) ∈ listPairs (List.range k) ++ listPairs (List.range k).reverse
  rw [List.mem_append] at hd
  rw [List.mem_append]
  rcases hd with hd | hd
  · rw [memListPairsIota] at hd
    rcases hd with (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
    · exact Or.inr ((memListPairsRevIota (k := k) (by omega)).mpr
        (Or.inr ⟨by omega, by omega, by omega⟩))
    · exact Or.inr ((memListPairsRevIota (k := k) (by omega)).mpr
        (Or.inl ⟨rfl, by omega⟩))
  · rw [memListPairsRevIota (k := k) (by omega)] at hd
    rcases hd with (⟨rfl, rfl⟩ | ⟨h1, h2, rfl⟩)
    · exact Or.inl (memListPairsIota.mpr (Or.inr ⟨by omega, rfl⟩))
    · exact Or.inl (memListPairsIota.mpr (Or.inl ⟨by omega, by omega⟩))

/-! ### §1 mem_transpose_seed（tame_list.hl:10652-:10678） -/

/-- **HOL `mem_transpose_seed`**（tame_list.hl:10652-:10678）
`!p d. MEM d (list_of_darts (fgraph (Seed p))) ==> MEM (SND d,FST d)
(list_of_darts (fgraph (Seed p)))`——Seed 两面清单（fgraphSeed）经
listOfDarts simp 面展为 `list_pairs 面1 ++ list_pairs 面2` 后，dart 转置
闭合由 §0 `memAppendTransposeD` 收口；GoodList 第三合取项形。 -/
theorem memTransposeSeed (p : ℕ) :
    ∀ d ∈ listOfDarts (facesVertexLists (Seed p)),
      (d.2, d.1) ∈ listOfDarts (facesVertexLists (Seed p)) := by
  have hk : 3 ≤ maxGon p := by
    show 3 ≤ p + 3
    omega
  rw [fgraphSeed p]
  simp only [listOfDarts, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  intro d hd
  exact memAppendTransposeD hk hd

/-! ### §2 good_list_seed（tame_list.hl:10680-:10686） -/

/-- **HOL `good_list_seed`**（tame_list.hl:10680-:10686）
`!p. good_list (fgraph (Seed p))`——HOL 一行 REWRITE_TAC[good_list;
mem_transpose_seed;all_nonempty_seed;uniq_list_of_darts_seed] 的 Lean 面：
`GoodList`（GoodListDefs.lean:72，list_hypermap-compiled.hl:63 三合取逐句
镜像）展开后批 21 三连（uniqListOfDartsSeed/allNonemptySeed）+ 本批
memTransposeSeed 匿名构造子直拼，零新增论证。 -/
theorem goodListSeed (p : ℕ) : GoodList (facesVertexLists (Seed p)) :=
  ⟨uniqListOfDartsSeed p, allNonemptySeed p, memTransposeSeed p⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.memTransposeSeed
#print axioms Kepler.Text.TameSpine.goodListSeed
#print axioms Kepler.Text.TameSpine.memAppendTransposeD
-/

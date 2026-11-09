/-
  Kepler.Text.MoreLemma2ChainUniqC — more_lemma2 岛 `simple_hypermap` 机器片 §3（收官）：
  `simple_hypermap_uniq` 及其两向（HOL tame_list.hl:9127–:9262）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ :9127 `simple_hypermap_list`      → simpleHypermapList
  │ :9210 `simple_hypermap_all_uniq`  → simpleHypermapAllUniq
  │ :9254 `simple_hypermap_uniq`      → simpleHypermapUniq（#33 收官）
  └────────────────────────────────────────────────────────────────

  ┌─ 依赖（全部已落，本片零重落）──────────────────────────────
  │ §1 `listPairsUnique` / `listPairsNotUniq`（MoreLemma2ChainUniqA）
  │ §2 `faceOrbitSubsetFindFace` / `faceTableSubsetFaceOrbit`（MoreLemma2ChainUniqB）
  │ 借 `Kepler.Text.TameCorrNode.memHypermapOfListNode`（public，零 Spine）
  │ TameLp public：`dart_in_face`/`findFaceDarts_ex_of_self`/`findFaceDarts_eq_of_mem`/
  │   `flatten_nodup_mem`/`GoodListNodesTl`
  │ `SimpleHypermapTl`（`Kepler.Text.ChainSimpleHypermap`，`f40ce982`，defeq `H.Simple`）
  │ 唯一现证小件：`memOrbitMapSelf`（`⟨0, rfl⟩` 级）
  └────────────────────────────────────────────────────────────────

  **口径**（派单）：`all uniq L` ↦ `∀ l ∈ L, l.Nodup`（= Assembly.AllUniq 同口径，
  也正是 `simpleHypermapAllUniq` 的结论形状，零桥）；`simple_hypermap (hypermap_of_list L)`
  ↦ `SimpleHypermapTl (hypermapOfList L hL)`。

  **纪律**：零 axiom/sorry/admit/native_decide；零 Spine import。
-/

import Kepler.Text.MoreLemma2ChainUniqA
import Kepler.Text.MoreLemma2ChainUniqB
import Kepler.Text.ChainSimpleHypermap

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2ChainUniqC

open Kepler.Graphs (fgraph)
open Kepler.Assembly (listOfDarts findFaceDarts GoodList)
open Kepler.Text.TameLp (dart_in_face mem_darts_of_mem_findFace findFaceDarts_nodup
  hypermapOfList GoodListNodesTl flatten_nodup_mem findFaceDarts_eq_of_mem
  findFaceDarts_ex_of_self findFaceDarts_congr_of_mem nextEl_mem_of_mem)
open Kepler.Text.MoreLemma2ChainUniqA (listPairsUnique listPairsNotUniq)
open Kepler.Text.MoreLemma2ChainUniqB (faceOrbitSubsetFindFace faceTableSubsetFaceOrbit)
open Kepler.Text.TameCorrNode (memHypermapOfListNode)
open Kepler.Text.ChainSimpleHypermap (SimpleHypermapTl)

/-! ## §0 私有小件 -/

/-- 轨道零次幂自含：`x ∈ orbitMap f x`。 -/
private theorem memOrbitMapSelf {α : Type*} (f : Equiv.Perm α) (x : α) :
    x ∈ Kepler.Text.orbitMap f x :=
  ⟨0, by simp⟩

/-! ## §1 `simple_hypermap_list`（tame_list.hl:9127） -/

/-- **HOL `simple_hypermap_list`**（tame_list.hl:9127-:9172）：
`good_list L ∧ good_list_nodes L ∧ all uniq L ⇒ simple_hypermap (hypermap_of_list L)`
（`all uniq L` 取 `∀ l ∈ L, l.Nodup`）。

证体：`Simple` 双包含。⊇ 向 = 轨道零次幂（`memOrbitMapSelf`）；
⊆ 向 = node 轨道给同 FST（`memHypermapOfListNode`）+ face 轨道落在面表
（`faceOrbitSubsetFindFace`）+ 面表定位（`findFaceDarts_ex_of_self`）+
`listPairsUnique` 收口。 -/
theorem simpleHypermapList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup) :
    (hypermapOfList L hL).Simple := by
  intro x hx
  have hxL : x ∈ listOfDarts L := List.mem_toFinset.mp hx
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    have hyn : y ∈ (hypermapOfList L hL).node x := hy.1
    have hyf : y ∈ (hypermapOfList L hL).face x := hy.2
    obtain ⟨hfst, hyd⟩ := (memHypermapOfListNode hL hgn hxL).mp hyn
    have hyf' : y ∈ findFaceDarts L x := faceOrbitSubsetFindFace hL hxL hyf
    obtain ⟨f, hfl, hfeq, hxf⟩ := findFaceDarts_ex_of_self
      (dart_in_face L x |>.mpr hxL)
    have hyf'' : y ∈ Kepler.Assembly.listPairs f := by rw [← hfeq]; exact hyf'
    exact (listPairsUnique (hunL f hfl) hxf hyf'' hfst).symm
  · intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact ⟨memOrbitMapSelf _ _, memOrbitMapSelf _ _⟩

/-! ## §2 `simple_hypermap_all_uniq`（tame_list.hl:9210） -/

/-- **HOL `simple_hypermap_all_uniq`**（tame_list.hl:9210-:9253）：
`good_list L ∧ good_list_nodes L ∧ simple_hypermap (hypermap_of_list L) ⇒ all uniq L`。

证体：反证 `¬ l.Nodup`——`listPairsNotUniq` 给同 FST 异元 `x ≠ x'`，
两者都在 `list_of_darts L` 内；`x' ∈ node x`（同 FST）∧ `x' ∈ face x`
（`findFaceDarts L x = listPairs l` + `faceTableSubsetFaceOrbit`）与 `Simple` 的
`{x}` 收口矛盾。 -/
theorem simpleHypermapAllUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hs : (hypermapOfList L hL).Simple) :
    ∀ l ∈ L, l.Nodup := by
  intro l hl
  by_contra hnl
  have hplnod : (Kepler.Assembly.listPairs l).Nodup :=
    flatten_nodup_mem hL.1 (List.mem_map.mpr ⟨l, hl, rfl⟩)
  obtain ⟨x, x', hxmem, hx'mem, hxx', hxfst⟩ := listPairsNotUniq hnl hplnod
  have hxdL : x ∈ listOfDarts L :=
    List.mem_flatten.mpr ⟨Kepler.Assembly.listPairs l,
      List.mem_map.mpr ⟨l, hl, rfl⟩, hxmem⟩
  have hx'dL : x' ∈ listOfDarts L :=
    List.mem_flatten.mpr ⟨Kepler.Assembly.listPairs l,
      List.mem_map.mpr ⟨l, hl, rfl⟩, hx'mem⟩
  have hsx := hs x (List.mem_toFinset.mpr hxdL)
  have hx'n : x' ∈ (hypermapOfList L hL).node x :=
    (memHypermapOfListNode hL hgn hxdL).mpr ⟨hxfst, hx'dL⟩
  have hfeq : findFaceDarts L x = Kepler.Assembly.listPairs l :=
    findFaceDarts_eq_of_mem hL.1 hl hxmem
  have hx'f : x' ∈ (hypermapOfList L hL).face x :=
    faceTableSubsetFaceOrbit hL hxdL (by rw [hfeq]; exact hx'mem)
  have hx'inter : x' ∈ (hypermapOfList L hL).node x ∩
      (hypermapOfList L hL).face x := ⟨hx'n, hx'f⟩
  rw [hsx] at hx'inter
  exact absurd (Set.mem_singleton_iff.mp hx'inter).symm hxx'

/-! ## §3 `simple_hypermap_uniq`（tame_list.hl:9254，收 #33） -/

/-- **HOL `simple_hypermap_uniq`**（tame_list.hl:9254-:9262）：
`good_list L ∧ good_list_nodes L ⇒ (simple_hypermap (hypermap_of_list L) ⇔ all uniq L)`
（`simple_hypermap` 取 `SimpleHypermapTl (hypermapOfList L hL)`，
`all uniq L` 取 `∀ l ∈ L, l.Nodup`；两向 = 上两件，HOL MESON 同构）。 -/
theorem simpleHypermapUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) :
    (SimpleHypermapTl (hypermapOfList L hL) ↔ ∀ l ∈ L, l.Nodup) :=
  ⟨fun hs => simpleHypermapAllUniq L hL hgn hs,
    fun hun => simpleHypermapList L hL hgn hun⟩

end Kepler.Text.MoreLemma2ChainUniqC

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2ChainUniqC.simpleHypermapList
#print axioms Kepler.Text.MoreLemma2ChainUniqC.simpleHypermapAllUniq
#print axioms Kepler.Text.MoreLemma2ChainUniqC.simpleHypermapUniq

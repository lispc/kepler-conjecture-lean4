/-
  Kepler.Text.TameSpine.TameList32 — B1 Tame_list 地基批 32：good_face_rep
  章（tamespine-port-plan §4 批次表 B1 行；接续批 31 = TameList31.lean，
  批 31 终点 = HOL :11366（parts1 已落）；本批起点 = HOL :11321
  `good_face_rep`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测）。

  **章级侦察定论（本批头条，任务书处方修正）**：批 31 预记
  「simple_hypermap_uniq 证体链 = 完整 hypermap_of_list face API 章，
  章级工程量宜独占一批」——实测**全章早已在库**（批 7/14 落地），
  七件链载体定名清单（HOL 锚 ↦ 在库件，逐条主仓实测）：
  · `list_pairs_not_uniq` :9173-:9208 ↦ `listPairsNotUniq`
    （TameList14.lean:269，泛型 α 公开件）；
  · `simple_hypermap_list` :9127（⇒ 向）↦ `simpleHypermapList`
    （TameList14.lean:244）；
  · `simple_hypermap_all_uniq` :9210-:9253 ↦ `simpleHypermapAllUniq`
    （TameList14.lean:297，证体即 HOL uniq_flatten_uniq + face_of_list +
    MEM_hypermap_of_list_node 拼装）；
  · `simple_hypermap_uniq` :9254-:9262（双向往返）↦ `simpleHypermapUniq`
    （TameList14.lean:325）；
  · `MEM_hypermap_of_list_node` :4399-:4406 ↦ `memHypermapOfListNode`
    （TameList7.lean:243）；
  · `face_of_list`（list_hypermap.vhl:1063）↦ `faceTableSubsetFaceOrbit`
    （TameList14.lean:142 私件，批 14 内消费）；
  · `find_pair_list_unique`（list_hypermap.vhl:275）↦
    `TameLp.findFaceDarts_eq_of_mem`（TameLp.lean:3870）；
  · `uniq_flatten_uniq` :3872-:3881 ↦ `TameLp.flatten_nodup_mem`
    （TameLp.lean:3809）；`dart_hypermap_of_list` :4095-:4102 ↦
    `TameLp.darts_hypermapOfList`（:4025）；`find_face_alt`
    （list_hypermap.vhl:135）↦ `findFaceDarts` 定义形
    （GoodListDefs.lean:55）。
  故本批零新载体、零新 def：主件 goodFaceRep 纯装配（两行证人直取）。

  **载体处方勘误（批 31 头注注记修正，入档）**：批 31 预记
  「good_list_nodes 消费形直取 GoodListNodes = True 桩
  （Assembly.lean:1344）」——实测 `hypermapOfList` 构造（TameLp §9，
  TameLp.lean:3993）与语义本体 `GoodListNodesTl`
  （TameLp.lean:4083，`(hypermapOfList L hL).nodeSet =
  nodesOfListSet L`）均已落地，批 14/16 章级消费惯例 =
  `GoodListNodesTl L hL`（True 桩喂不进 `simpleHypermapUniq` 的
  good_list_nodes 槽）；本批沿批 14 惯例。`simple_hypermap`
  （text_formalization/hypermap/hypermap.hl:186）↦ `Hypermap.Simple`
  （Hypermap.lean:1058，语句逐字同形）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11321-:11347）：

  主件：`good_face_rep` :11321-:11347
  `!L f. good_list L /\ good_list_nodes L /\
  simple_hypermap (hypermap_of_list L) /\ MEM f (list_of_faces L) ==>
  (?f0. list_pairs f0 = f /\ MEM f0 L /\ MAP FST f = f0 /\ uniq f0 /\
  ~(f0 = []))`（证体五行）——list_of_faces 每元皆 L 某面的 list_pairs
  像，且像表非空、无重。HOL 五槽两路逐槽：face_rep 槽 = 批 31
  `faceRep` 直取（`list_pairs f0 = f`/`MEM f0 L`/`MAP FST f = f0`
  三合取）；`uniq f0` 槽 = 批 14 `simpleHypermapUniq` ⇐ 向（HOL
  ASM_SIMP_TAC[simple_hypermap_uniq] + MESON allP 同构，消费面即
  `∀ l ∈ L, l.Nodup` 逐点）；`~(f0 = [])` 槽 = good_list 第 2 合取
  （`GoodList` 的 `∀ l ∈ L, l ≠ []`，GoodListDefs.lean:73，直取）；
  `good_list_nodes` 槽 = `GoodListNodesTl L hgood`（勘误见上）。

  终点自然边界：`good_face_rep` 后的 parts 段（`parts_nil` :11348 /
  `uniq_sing` :11356 / `parts1` :11359-:11366）批 31 已收；下一未收件
  = `parts_impure` :11367。

  依赖面：批链全批 1-31；在库 TameList7（memHypermapOfListNode）/
  TameList14（listPairsNotUniq/simpleHypermapList/simpleHypermapAllUniq/
  simpleHypermapUniq）+ TameLp（hypermapOfList/GoodListNodesTl）+
  Kepler.Assembly.GoodListDefs（GoodList/listPairs）。

  诚实记账：本批一件全真证，零新 def、零止损件、零记账债；记批 31
  头注载体处方勘误一条（good_list_nodes 槽，见上）；章级侦察七件
  全在库零镜像（定名清单见头注首段）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 33 接续点：HOL :11367 `parts_impure`
  `!L f. (!x. MEM x f ==> x = LAST f \/ ~(next_el f x =
  f_list L (e_list x))) /\ uniq f ==> parts L f = MAP (\x. [x]) f`
  （依赖侦察预记：partsr/parts_pure 在库批 9
  partitionIntoAtom0rCases/partsPure；cat1s 槽批 12 载体侦察时未见独立
  件，届时按 Seq.cat1s = 取头并入定义形折算）。
-/

import Kepler.Text.TameSpine.TameList31

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ### 主件 good_face_rep（tame_list.hl:11321-:11347） -/

/-- **HOL `good_face_rep`**（tame_list.hl:11321-:11347）
`!L f. good_list L /\ good_list_nodes L /\
simple_hypermap (hypermap_of_list L) /\ MEM f (list_of_faces L) ==>
(?f0. list_pairs f0 = f /\ MEM f0 L /\ MAP FST f = f0 /\ uniq f0 /\
~(f0 = []))`——list_of_faces 每元皆 L 某面的 list_pairs 像，且像表
非空、无重。HOL 五槽两路：face_rep 槽 ↦ 批 31 `faceRep` 直取；
`uniq f0` 槽 ↦ 批 14 `simpleHypermapUniq` ⇐ 向；`~(f0 = [])` 槽 ↦
`GoodList` 第 2 合取直取。 -/
theorem goodFaceRep (L : fgraph ℕ) (f : List (ℕ × ℕ))
    (hgood : GoodList L) (hgn : GoodListNodesTl L hgood)
    (hs : (hypermapOfList L hgood).Simple)
    (hf : f ∈ listOfFaces L) :
    ∃ f0 : List ℕ, listPairs f0 = f ∧ f0 ∈ L ∧ f.map Prod.fst = f0 ∧
      f0.Nodup ∧ f0 ≠ [] := by
  -- face_rep 槽（HOL INTRO_TAC face_rep + ASM_REWRITE + EXISTS f0）
  obtain ⟨f0, hEq, hf0, hmfst⟩ := faceRep L f hf
  refine ⟨f0, hEq, hf0, hmfst, ?_, hgood.2.1 f0 hf0⟩
  -- uniq f0 槽：simple_hypermap_uniq ⇐ 向（HOL ASM_SIMP_TAC 同构）
  exact (simpleHypermapUniq L hgood hgn).mp hs f0 hf0

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.goodFaceRep
-/

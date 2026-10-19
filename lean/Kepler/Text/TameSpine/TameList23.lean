/-
  Kepler.Text.TameSpine.TameList23 — B1 Tame_list 地基批 23：elements 章开局
  （tamespine-port-plan §4 批次表 B1 行；接续批 22 = TameList21→TameList22.lean，
  批 22 终点 = HOL :10686（good_list_seed 已落，:10690 起留本批）；
  本批起点 = HOL :10690）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10690-:10707）——elements 章开局，
  主件 1 枚：

  主件：`list_of_elements_seed` :10690-:10707
  `!p. list_of_elements (fgraph (Seed p)) = REVERSE (upt 0 (p+3))`。
  :10709 `good_vertices_set2_seed` 起自然边界收批（留批 24）。
  :10812 有同名 `fgraph_seed` 再证（dih2k_list 展开面，:10796
  iso_list_imp_dih2k 起属 dih2k 章），不在本批射程。

  诚实收窄记账（本批核心语义事实，clone 探针实测）：
  HOL 语句为列表等式形，证体（:10693-:10707）两支——
  ① GMATCH_SIMP_TAC undup_cat（tame_list.hl:1309
  `(!x. MEM x s ==> MEM x t) ==> undup (cat s t) = undup t`，此处
  s = iota 0 (p+3)、t = rev (iota 0 (p+3))，成员包含支由
  ASM_MESON_TAC[Seq.mem_rev;REVERSE_rev] 闭）；② MATCH_MP_TAC
  Seq.undup_id（jHOLLight seq-compiled.hl:1843 `uniq s ==> undup s = s`，
  门槛经 Seq.rev_uniq :1797 + REVERSE_rev + Seq.iota_uniq :3317 +
  upt0 :614 喂入）。但 HOL `undup`（seq-compiled.hl:1814）为
  「保最后一次出现」递归（`undup (x::s') = if x <- s' then undup s'
  else x :: undup s'`），Lean `List.eraseDups`（本语句载体
  TameLp.listOfElements，TameLp.lean:4069 `L.flatten.eraseDups`）
  为「保首次出现」——对同一表 `range (p+3) ++ reverse (range (p+3))`，
  HOL 形去重得 reverse（各元素末现全在第二面），eraseDups 去重得
  range（各元素首现全在第一面；clone 探针 #eval 实测
  `(range 5 ++ (range 5).reverse).eraseDups = [0,1,2,3,4] ≠ [4,3,2,1,0]`），
  列表等式形在本载体下为假，不可直译。沿批 2 undupCat_mem
  （TameList2.lean:948，同为本批 undup_cat 面的载体形）先例按成员谓词形
  收窄落地：两语义下成员谓词一致（List.mem_eraseDups 无条件）；
  HOL 证体第②支（undup_id/rev_uniq/iota_uniq 的 uniq 门槛链）在成员形下
  解散，不另入形。

  层级侦察定论（全量形记档，本批新核）：
  · fgraph (Seed p) 面 = 批 21 fgraphSeed（rfl 一步两字段形
    `[List.range (maxGon p), (List.range (maxGon p)).reverse]`）+ flatten
    两步 simp（批 22 listOfDarts 同款 simp 集：flatten_cons/flatten_nil/
    append_nil）；`maxGon p = p + 3` 定义等式（Plane.lean:23
    `def maxGon p := p + 3`，rfl 实测在案）。
  · undup_cat 面成员包含支实例化 `!y. MEM y (iota 0 (p+3)) ==>
    MEM y (rev (iota 0 (p+3)))` ↦ `List.mem_reverse` 单步（HOL
    Seq.mem_rev :1567 + REVERSE_rev 两引理的 Lean 合一面）。
  · 批 2 undupCat_mem 签名 `∀ b, b ∈ (s ++ t).eraseDups ↔ b ∈ t.eraseDups`
    与本批 s/t 实例直拼，尾巴 List.mem_eraseDups 剥壳两步收口。

  依赖面（全为在案真件，零新增债）：批 2 `undupCat_mem`（tame_list.hl:1309
  载体形）+ 批 21 `fgraphSeed` + TameLp `listOfElements`（TameLp.lean:4069）+
  Mathlib List.mem_eraseDups/List.mem_reverse/List.flatten_cons/
  List.flatten_nil/List.append_nil。

  载体折算（沿批 1-22 约定）：`fgraph`（函数）↦ `facesVertexLists`；
  `Seed`/`maxGon` ↦ Kepler.Graphs 同名件（Plane.lean:67/:23）；`iota 0 k` ↦
  `List.range k`；`rev` ↦ `List.reverse`；`list_of_elements` ↦
  `TameLp.listOfElements`（flatten.eraseDups）；`MEM` ↦ `∈`。

  诚实记账：本批一件真证，零新增记账债（零止损件）。语句面为成员谓词形
  收窄（语义差异实测记账见上）——批 2 undupCat_mem 先例第二例，非列表
  等式直译。公理审计预期：本件仅传递标准三
  [propext, Classical.choice, Quot.sound]（证体仅 rw/simp/exact 拼装）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 24 接续点：HOL :10709 `good_vertices_set2_seed`
  （`!p. vertices_set2 (Seed p) = elements_of_list (fgraph (Seed p))`，
  证体 :10712-:10718，EXTENSION/IN_SET_OF_LIST 成员面）——vertices_set2
  （tame_defs.hl:392 `set_of_list (vertices_graph g)`）折叠面须先侦察：
  批 2 verticesGraphAlt（TameList2.lean:121）与 GoodGraph.verticesSet2
  （AFP Graph 面，GoodGraph.lean:57）双载体择一；随后 :10720
  all_uniq_seed（`all uniq (fgraph (Seed p))` 面，List.nodup_range +
  nodup_reverse 直拼）；:10732 good_facesAt_seed（facesAt/FACE_LIST_AT
  面，批 2 elReplicate TameList2.lean:962 在案）；:10752 uniq_inj_on
  （sizel/uniq ⇒ inj_on 运输件，批 4 inj_on/iso_list 运输家族面侦察）；
  :10785 elements_of_list_pr（set_of_list [u;rev u] 面）。:10796 起
  dih2k 章（:10812 同名 fgraph_seed 再证在其内）不在本批射程。
-/

import Kepler.Text.TameSpine.TameList22

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph Seed maxGon)
open Kepler.Text.TameLp (listOfElements)

/-! ### §1 list_of_elements_seed（tame_list.hl:10690-:10707） -/

/-- **HOL `list_of_elements_seed`**（tame_list.hl:10690-:10707）
`!p. list_of_elements (fgraph (Seed p)) = REVERSE (upt 0 (p+3))`——
成员谓词形收窄落地（诚实记账见头部）：undup_cat（:1309）面成员包含支
实例化 `∀ y ∈ List.range (p+3), y ∈ (List.range (p+3)).reverse`
（List.mem_reverse 单步，即 HOL Seq.mem_rev + REVERSE_rev 面）交批 2
undupCat_mem；undup_id 面（Seq.undup_id `uniq s ==> undup s = s` 的
iota_uniq 门槛链）在成员谓词形下解散（List.mem_eraseDups 无条件）。 -/
theorem listOfElementsSeed (p : ℕ) :
    ∀ x : ℕ, x ∈ listOfElements (facesVertexLists (Seed p)) ↔
      x ∈ (List.range (p + 3)).reverse := by
  intro x
  have hcat : ∀ y ∈ List.range (p + 3), y ∈ (List.range (p + 3)).reverse :=
    fun _ hy => List.mem_reverse.mpr hy
  rw [fgraphSeed p]
  simp only [listOfElements, List.flatten_cons, List.flatten_nil, List.append_nil]
  exact ⟨fun h => List.mem_eraseDups.mp (undupCat_mem hcat x |>.mp h),
    fun h => undupCat_mem hcat x |>.mpr (List.mem_eraseDups.mpr h)⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.listOfElementsSeed
-/

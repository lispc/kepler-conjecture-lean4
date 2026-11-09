/-
  Kepler.Text.Reduction3Thm4 — J 战役 J3 定理层 T4 批（支撑件 + 阻碍树交班）。

  ┌─ 本批范围（AGENTS §7：T4 主件按依赖树裁决，先交可证支撑件）──────
  │ T4 规划件 4：minimalFace_core :1179 / mem_core_triple_minimalFace
  │ :1268 / dest_triple_full_all_filter :1322 / reduction_subdivFace2 :1379。
  │ 裁决（逐件依赖树见 DELIVERY §15）：
  │   · mem_core_triple_minimalFace —— **J2 门禁**（证明首行即从
  │     Reduction2.transform_assumption_v2_lemma 推出 transform_assumption_v2）；
  │   · dest_triple_full_all_filter —— 依赖上件（同一 J2 门禁）；
  │   · reduction_subdivFace2 —— 装配件，依赖 T6 的 reduction_subdivFace
  │     + 上两件 + T3 缓件（hd_vs_some_v/last_vs_some_prev/sizel_3_concl）；
  │   · minimalFace_core —— 非 J2 门禁，但需 find_pair_list/loop_choice
  │     理论批（loop_choice_props/prev_el_list_pairs_eq/minimalFace_nonnil
  │     + listPairsInj/findFaceAlt/findPairListUnique 的链侧装配），
  │     估 200-300 行，立 T4-theory 专批。
  │ 本批交付其 3 件链侧支撑（下），全部无条件、只吃树内既有件：
  │   prevElListPairsEq      reduction1.hl:3799 → §A
  │   minimalFaceMem        （minimalFace_face 链侧形，Reduction1 外部）
  │   minimalFaceVerticesMemFgraph（mem_minimalFace_fgraph 链侧基础形）
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3Thm3`（定理层链）+
  │ `Kepler.Text.TameSpine.TameList53`（nextElListPairsEq；**单文件闭包
  │ 核验**：1172 模块，Assembly 条目仅 `Kepler.Assembly.GoodListDefs`，
  │ 无伞模块——按编排者 2026-11-09 新口径放行）+
  │ `Kepler.Graphs.ListAuxLemmas`（minimal_mem）。零 axiom/sorry/
  │ admit/native_decide。泛型 binder 沿 nextEl 族三例
  │ `[BEq α] [LawfulBEq α] [DecidableEq α]`（j2w1 雷区记档）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm3
import Kepler.Text.TameSpine.TameList53
import Kepler.Graphs.ListAuxLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (Face Graph minimalFace nonFinals)

/-! ## §A `prev_el_list_pairs_eq`（reduction1.hl:3799）

`uniq s ∧ MEM x s ==> MEM (prev_el s x, x) (list_pairs s)`——
`prev_el s x` 在 `s` 中（`prevEl_mem_of_mem`）、其 `next_el` 回到 `x`
（`nextEl_prevEl`），再用 `nextElListPairsEq`（TameList53，共享
`listPairs`/`nextEl` 常量，**无需跨载体桥**）。 -/

/-- HOL `prev_el_list_pairs_eq`（reduction1.hl:3799）。 -/
theorem prevElListPairsEq {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hnd : s.Nodup) (hx : x ∈ s) :
    (prevEl s x, x) ∈ Kepler.Assembly.listPairs s := by
  have hy : prevEl s x ∈ s := Kepler.Text.TameLp.prevEl_mem_of_mem hx
  have hnext : nextEl s (prevEl s x) = x :=
    Kepler.Text.TameLp.nextEl_prevEl hnd hx
  have hp := Kepler.Text.TameSpine.nextElListPairsEq hnd hy
  rwa [hnext] at hp

/-! ## §B `minimalFace` 成员基础（`minimalFace_face`/`mem_minimalFace_fgraph`
的链侧投影形；HOL 原件归 Reduction1/外部章） -/

/-- `nonFinals g` 非空时 `minimalFace (nonFinals g)` 在其内
（`minimal_mem` 直取；HOL `minimalFace_face` 的成员半边）。 -/
theorem minimalFaceMem {g : Graph} (h : nonFinals g ≠ []) :
    minimalFace (nonFinals g) ∈ nonFinals g :=
  Kepler.Graphs.minimal_in_set (fun f : Face => f.vertices.length) h

/-- 上式投影到 `fgraph g = MAP FST (faces g)`：最小面的顶点表在
`fgraph g` 中（HOL `mem_minimalFace_fgraph` 的链侧基础形）。 -/
theorem minimalFaceVerticesMemFgraph {g : Graph} (h : nonFinals g ≠ []) :
    (minimalFace (nonFinals g)).vertices ∈ g.faces.map (fun f => f.vertices) := by
  have hm := minimalFaceMem h
  rw [nonFinals] at hm
  obtain ⟨hf, _⟩ := List.mem_filter.mp hm
  exact List.mem_map.mpr ⟨_, hf, rfl⟩

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.prevElListPairsEq
#print axioms Kepler.Text.Reduction3.minimalFaceMem
#print axioms Kepler.Text.Reduction3.minimalFaceVerticesMemFgraph

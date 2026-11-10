/-
  Kepler.Text.Reduction1W3g — J4 W3d 批补齐：`hne` 槽（`maxFinalsGExists`
  的「种子可许性」供料）的四件种子章小件（HOL reduction1.hl:2958-:3011：
  `foldr_maxn_exists` / `seed_finals` / `seed_planegraphP` / `seed_size_v_gt_1`）。

  这四件在 W0+W3d 落库（`a8dc86c1`）时随 `hne` 显式槽一并缓办（W3d 文件头
  「(b) S ≠ {} ← 种子三元组」），未随批落定理；本文件补齐。均为小件：
  · `foldr_maxn_exists`：非空自然数表的 foldr max 取到某元（对表归纳两支）；
  · `seed_finals`：`finals (Seed p) = [⟨iota 0 (maxGon p), T⟩]`——与已落
    `finalFaceSeed`（Reduction1W2l）同体（`finals g = g.faces.filter
    Face.final` 与 HOL `filter SND (faces g)` 定义性同形），一行换装；
  · `seed_planegraphP`：`planegraphP p (Seed p)` = `PlaneGraphPSpine p
    (Seed p)`（RTranCl 自反，一行）；
  · `seed_size_v_gt_1`：种子 fgraph 展平的每个顶点在多于 1 个面中
    （fgraph_seed 两元素表 + 成员经 reverse 往返 + filter 全过 ⇒ 长度 2）。

  下游接线（W4 侦察章·消槽）：四件 + `flagListSeed`（W3c）+ UYOUIXG 槽版
  （W2n `uyouixgOfAuqtzyzList`，带 `hAuq` 槽）+ `isoListRestricted`/
  `isoListSpineSymNil`（T19/T5）+ `allUniqSeed`/`goodFacesAtSeed`/
  `goodVerticesSet2Seed`（T24）⇒ `FinalsAdmissible L p (Seed (f.length - 3))
  L' hL' N'` 十合取装配（即 `maxFinalsGExists` 的 `hne` 槽消除）；装配本体
  见 W4 侦察（两道载体桥备忘：T24 `goodVerticesSet2Seed` 的
  `elementsOfList (facesVertexLists …)` 与 `fgraphOfGraph` 定义性同形；
  `GoodFacesV3` 的 Perm 形需再核 `facesAtV2` 定义体）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2l
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.TameSpine.TameList21
import Kepler.Text.TameSpine.TameList58
import Kepler.Graphs.Plane

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (Graph finals RTranCl Seed)
open Kepler.Text.Reduction3 (fgraphOfGraph)
open Kepler.Text.TameSpine (PlaneGraphPSpine)

/-! ## §1 `foldr_maxn_exists`（reduction1.hl:2958-:2976） -/

/-- **HOL `foldr_maxn_exists`**（reduction1.hl:2958-:2976）：
`~(xs = []) ==> (?n. MEM n xs /\ n = foldr maxn 0 xs)`——对表归纳两支
（尾空/尾非空）。 -/
theorem foldrMaxnExists (xs : List ℕ) (h : xs ≠ []) :
    ∃ n, n ∈ xs ∧ n = xs.foldr max 0 := by
  induction xs with
  | nil => exact absurd rfl h
  | cons x t ih =>
    by_cases ht : t = []
    · refine ⟨x, List.mem_cons.mpr (Or.inl rfl), ?_⟩
      rw [ht]
      simp
    · obtain ⟨n, hn, hnval⟩ := ih ht
      refine ⟨max x n, ?_, ?_⟩
      · rcases Nat.le_total x n with hle | hge
        · rw [Nat.max_eq_right hle]; exact List.mem_cons_of_mem _ hn
        · rw [Nat.max_eq_left hge]; exact List.mem_cons.mpr (Or.inl rfl)
      · rw [List.foldr_cons, ← hnval]

/-! ## §2 种子三件（reduction1.hl:2977-:3011） -/

/-- **HOL `seed_finals`**（reduction1.hl:2977-:2986）：
`finals (Seed p) = [iota 0 (maxGon p),T]`——已落 `finalFaceSeed`
（reduction1.hl:2337，Reduction1W2l）的换装（`finals g = g.faces.filter
Face.final` 与 `filter SND (faces g)` 定义性同形）。 -/
theorem seedFinals (p : ℕ) :
    finals (Seed p) = [⟨List.range (Kepler.Graphs.maxGon p), true⟩] :=
  finalFaceSeed p

/-- **HOL `seed_planegraphP`**（reduction1.hl:2988-:2996）：
`planegraphP p (Seed p)`——RTranCl 自反（`PlaneGraphPSpine p g =
RTranCl (next_plane p) (Seed p) g`，TameList58）。 -/
theorem seedPlanegraphP (p : ℕ) : PlaneGraphPSpine p (Seed p) :=
  RTranCl.refl

/-- **HOL `seed_size_v_gt_1`**（reduction1.hl:2997-:3011）：
`all (\v. sizel (filter (MEM v) (fgraph (Seed p))) > 1)
(flatten (fgraph (Seed p)))`——fgraph_seed 两元素表（面与其反转）成员经
reverse 往返互通，filter 全过 ⇒ 长度 2。 -/
theorem seedSizeVGt1 (p : ℕ) :
    ∀ v ∈ (fgraphOfGraph (Seed p)).flatten,
      1 < ((fgraphOfGraph (Seed p)).filter (fun r => decide (v ∈ r))).length := by
  have hfg : fgraphOfGraph (Seed p) =
      [List.range (Kepler.Graphs.maxGon p),
        (List.range (Kepler.Graphs.maxGon p)).reverse] :=
    Kepler.Text.TameSpine.fgraphSeed p
  intro v hv
  rw [hfg] at hv
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append,
    List.mem_reverse] at hv
  have hvR : v ∈ List.range (Kepler.Graphs.maxGon p) := hv.elim id id
  rw [hfg]
  have heq : ([List.range (Kepler.Graphs.maxGon p),
      (List.range (Kepler.Graphs.maxGon p)).reverse].filter
      (fun r => decide (v ∈ r))) =
      [List.range (Kepler.Graphs.maxGon p),
        (List.range (Kepler.Graphs.maxGon p)).reverse] :=
    List.filter_eq_self.mpr fun f hf => by
      rcases List.mem_cons.mp hf with hf1 | hf1
      · rw [hf1]; exact decide_eq_true hvR
      · rw [List.mem_singleton.mp hf1, decide_eq_true_eq]
        exact List.mem_reverse.mpr hvR
  rw [heq, List.length_cons, List.length_cons, List.length_nil]
  omega

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.foldrMaxnExists
#print axioms Kepler.Text.Reduction1.seedFinals
#print axioms Kepler.Text.Reduction1.seedPlanegraphP
#print axioms Kepler.Text.Reduction1.seedSizeVGt1

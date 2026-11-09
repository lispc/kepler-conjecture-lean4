/-
  JcajyduAqLeaf8W2b — AQ8 波 2b-i-1：`parts_rev_f_betwn_pure` 的前置件 + 形状半。

  ┌─ 本波为何是 i-1（按内容实报）─────────────────────────────────
  │ HOL `parts_rev_f_betwn_pure`（AQ8.hl:1627-2118）主体 490 行，
  │ 内含 parts_characterize 四前件的构造、块边界 next_el 判别、
  │ count_node_face 计数、两块（l 与 l2）双发；Lean 实测预估 >450，
  │ 按编排者放行条款拆 W2b-i-1（本波：前置 + 形状半，可独立闭环）/
  │ W2b-i-2（下一波：块边界 + partsCharacterize 总装）。
  │ 本波三件均为 i-2 的直接输入，且自身独立可验。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① aq8w2b_fstMemRtran1   AQ8.hl:1357（40 行，i-2 的硬前置）
  │    `FST (split_normal_list L r (find_face L (l'y)) (l'y) (prev_el r (l'z)))
  │     IN ntrans L N r x 1`
  │ ② aq8w2b_flattenRevBlocks  AQ8.hl:1627 的 g 形状半（flatten_rev 实例化）
  │    `flatten (rev (map (fun d => rev (F d)) W)) = rev (flatten (map F W))`
  │ ③ aq8w2b_blocksNonnil / aq8w2b_blockNonnil  AQ8.hl:1627 的 all-nonnil 半
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重（全 4 名；全闭包负探针 probe_aq8w2bi.log）────────
  │ ① 目标名全 Unknown（import 到 JcajyduAqLeaf8W2aB + Leaf8W0 +
  │    TameList39/Split1B/TameLp；AGENTS §7.1 #18）。
  │ ② 引擎全在库、标准三：`flattenRev`（W0）、`partsCharacterize`
  │    （TameList39:161，HOL parts_characterize 的逐字镜像，含
  │    `r.getLast!`/`p.getLast!` 形）、`countNodeFace`（Split1B:145）、
  │    `la7_nextEl_reverse`/`la7_prevEl_reverse`（TameLp:5591/5618，
  │    HOL next_el_rev 已在库）、`List.length_range'`、`List.map_eq_nil_iff`。
  │ ③ `List.reverse_map`/`List.range'_eq_nil` 在本版 Lean 无此名
  │    （探针 Unknown constant）⇒ 私有 `aq8w2b_mapReverse` 自证。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `FST (split_normal_list …)` ↦ `.1`（Prod.fst 与 HOL FST 同）。
  │ ② HOL `MAP (\x. map (\i. n_list^i x) (upt 1 (sizel …)))` ↦
  │    `List.range' 1 (sz d)`（`upt 1 k` 双闭 = range' 1 k 的既有批内
  │    约定）；`POWER` ↦ `Function.iterate`；`rev` ↦ `List.reverse`。
  │ ③ `parts_characterize` 的 `LAST` ↦ `getLast!`；all ↦ 逐点 ∀∈。
  │ ④ `fst_mem_rtran1` 的 HOL 前件（good_list/good_list_nodes/marked/
  │    ~final）在 Lean 侧只用 `¬final`（结构成员关系与 good 无关），
  │    按条件槽风格显式 `hnf`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w2b_` 前缀，私件同前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2aB
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.TameList39
import Kepler.Text.TameSpine.JcajyduAqSplit1B
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 `fst_mem_rtran1`（HOL AQ8.hl:1357，i-2 硬前置） -/

/-- HOL `fst_mem_rtran1`（AQ8.hl:1357）：split 的**前半**进 `ntrans … 1`。
非终态支 `ntrans 1 = replace … N ++ [split.1]`，直接 `mem_append_right`
+ 单点成员（与 W0 `sndMemRtran1` 同构、更简：右侧无需 `r ∈ N`）。 -/
theorem aq8w2b_fstMemRtran1 (L : fgraph ℕ) {N : List (List (ℕ × ℕ))}
    {r : List (ℕ × ℕ)} {x : ℕ × ℕ} (hnf : ¬finalListSpine L r) :
    (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 := by
  unfold ntransSpine
  rw [Function.iterate_one]
  unfold transformListSpine
  dsimp only
  rw [if_neg hnf]
  exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))

/-! ## §1 形状半：`rev/map` 与 `range'` 块代数 -/

/-- `map f` 与 `reverse` 的交换律（本版 Lean 无 `List.reverse_map` 名，
自证；post-hoc 记档）。 -/
private theorem aq8w2b_mapReverse {α β : Type} (f : α → β) (l : List α) :
    (l.map f).reverse = l.reverse.map f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, ih]

/-- `parts_rev_f_betwn_pure` 的 g 形状半（AQ8.hl:1627）：
`flatten (rev (map (fun d => rev (F d)) W)) = rev (flatten (map F W))`，
其中 `F d = map (fun i => nList^i d) (range' 1 (sz d))`。
由 W0 `flattenRev` + `mapReverse` 逐字得到（i-2 把 g 的假设折成本式）。 -/
theorem aq8w2b_flattenRevBlocks (L : fgraph ℕ) (W : List (ℕ × ℕ))
    (sz : ℕ × ℕ → ℕ) :
    ((W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse).flatten
      = (((W.map (fun d =>
          (List.range' 1 (sz d)).map (fun i => (nList L)^[i] d))).flatten)).reverse := by
  simp only [← aq8w2b_mapReverse]
  exact flattenRev W (fun d => (List.range' 1 (sz d)).map (fun i => (nList L)^[i] d))

/-! ## §2 非空半：每块非空 -/

/-- `0 < k ⇒ map (fun i => nList^i d) (rev (range' 1 k)) ≠ []`（i-2 的
all-nonnil 单块件；`length_range'` 直接给出块长 = k）。 -/
theorem aq8w2b_blockNonnil (L : fgraph ℕ) {k : ℕ} (hk : 0 < k) (d : ℕ × ℕ) :
    (List.range' 1 k).reverse.map (fun i => (nList L)^[i] d) ≠ [] := by
  intro h
  have hlen : ((List.range' 1 k).reverse.map (fun i => (nList L)^[i] d)).length = k := by
    rw [List.length_map, List.length_reverse, List.length_range']
  rw [h] at hlen
  simp at hlen
  omega

/-- all-nonnil 半（AQ8.hl:1627 前件之一）：逐点 `0 < sz d` ⇒ 映射出的块表
无空块（`partsCharacterize` 的 `hall` 槽形）。 -/
theorem aq8w2b_blocksNonnil (L : fgraph ℕ) (W : List (ℕ × ℕ))
    (sz : ℕ × ℕ → ℕ) (hpos : ∀ d ∈ W, 0 < sz d) :
    ∀ p ∈ W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d)), p ≠ [] := by
  intro p hp
  obtain ⟨d, hdW, rfl⟩ := List.mem_map.mp hp
  exact aq8w2b_blockNonnil L (hpos d hdW) d

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：四件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w2b_fstMemRtran1
#print axioms Kepler.Text.TameSpine.aq8w2b_flattenRevBlocks
#print axioms Kepler.Text.TameSpine.aq8w2b_blockNonnil
#print axioms Kepler.Text.TameSpine.aq8w2b_blocksNonnil

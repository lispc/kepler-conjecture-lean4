/-
  JcajyduAqLeaf8W2bB — AQ8 波 2b-i-2a：`parts_rev_f_betwn_pure` 主体上半。

  ┌─ 范围（按 §AQ8W2bi-2 五步；本波 = 步 1–3，hH 见 DELIVERY 分支表）──
  │ ① aq8w2b_fstMemFlatten  d ∈ listOfDarts L ⇒ d.1 ∈ L.flatten（步 2 引擎）
  │ ② aq8w2b_szPos          ∀d∈W, d∈darts ⇒ 0 < 节点计数（步 2 抽象形）
  │ ③ aq8w2bB_szPosBetwn    窗口 W 的实例（步 2 具体形）
  │ ④ aq8w2bB_hall          窗口块表的 all-nonnil（步 3，partsCharacterize hall 槽）
  │ ⑤ aq8w2bB_flattenEq     prt.flatten = g（步 1，形状）
  │ 步 4（hH 边界判别）与步 5（总装）留 i-2b：E3（块边界 one-step）
  │ 在 AQ4 车道尚未落库，按编排者指令先报不等待。
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重（全闭包负探针 probe_aq8w2bii.log）────────────────
  │ 目标名全 Unknown；引擎：`fstListPairs`（TameList50:155，公开）、
  │ `mem_darts_of_mem_findFace`（TameLp）、`betwnMem`、
  │ `aq8w2b_flattenRevBlocks`/`aq8w2b_blocksNonnil`（i-1，本批复用）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `sizel (filter (\t. t = FST d) (flatten L))` ↦
  │    `(L.flatten.filter (fun t => decide (t = d.1))).length`（既有批内
  │    载体，与 countNodeFace 同形）。
  │ ② `upt 1 k` ↦ `range' 1 k`；`POWER` ↦ iterate；`rev` ↦ reverse；
  │    `MAP (\x. [x])`/块映射与 i-1 的 `flattenRevBlocks` 逐字对齐。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w2b_`/`aq8w2bB_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b
import Kepler.Text.TameSpine.TameList50

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl mem_darts_of_mem_findFace)

/-! ## §0 darts → FST 进 flatten（步 2 引擎） -/

/-- `d ∈ listOfDarts L ⇒ d.1 ∈ L.flatten`：listOfDarts 拆块后由
`fstListPairs`（`(listPairs l).map fst = l`）落回面表。 -/
theorem aq8w2b_fstMemFlatten {L : fgraph ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d.1 ∈ L.flatten := by
  have hd' : d ∈ (L.map listPairs).flatten := hd
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd'
  obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
  have hfst : d.1 ∈ (listPairs l0).map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hdl
  rw [fstListPairs] at hfst
  exact List.mem_flatten.mpr ⟨l0, hl0, hfst⟩

/-- 节点计数正性（步 2 抽象形）：`d` 是 dart ⇒ 其 FST 至少出现一次。 -/
theorem aq8w2b_szPos (L : fgraph ℕ) (W : List (ℕ × ℕ))
    (hW : ∀ d ∈ W, d ∈ listOfDarts L) :
    ∀ d ∈ W, 0 < (L.flatten.filter (fun t => decide (t = d.1))).length := by
  intro d hd
  have hmem : d.1 ∈ L.flatten := aq8w2b_fstMemFlatten (hW d hd)
  have hfilt : d.1 ∈ L.flatten.filter (fun t => decide (t = d.1)) :=
    List.mem_filter.mpr ⟨hmem, by simp⟩
  exact List.length_pos_of_mem hfilt

/-! ## §1 窗口实例与 all-nonnil（步 2 具体形 / 步 3） -/

/-- 窗口每个 dart 都在 `listOfDarts L`。 -/
theorem aq8w2bB_WDarts (L : fgraph ℕ)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ} :
    ∀ d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x),
      d ∈ listOfDarts L := by
  intro d hd
  exact mem_darts_of_mem_findFace L (betwnMem hd)

/-- 窗口的节点计数正性（步 2 具体形）。 -/
theorem aq8w2bB_szPosBetwn (L : fgraph ℕ)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ} :
    ∀ d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x),
      0 < (L.flatten.filter (fun t => decide (t = d.1))).length :=
  aq8w2b_szPos L _ (aq8w2bB_WDarts L)

/-- 窗口块表的 all-nonnil（步 3，`partsCharacterize` 的 `hall` 槽形）。 -/
theorem aq8w2bB_hall (L : fgraph ℕ)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ} :
    ∀ p ∈ (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
      (fun d => (List.range' 1
          ((L.flatten.filter (fun t => decide (t = d.1))).length)).reverse.map
        (fun i => (nList L)^[i] d)), p ≠ [] :=
  aq8w2b_blocksNonnil L _ _ (aq8w2bB_szPosBetwn L)

/-! ## §2 形状：`prt.flatten = g`（步 1） -/

/-- 形状半具体形：若 `g` 是正序块展平的反序，则反序块表的展平 = `g`。 -/
theorem aq8w2bB_flattenEq (L : fgraph ℕ) (W : List (ℕ × ℕ))
    (sz : ℕ × ℕ → ℕ) (g : List (ℕ × ℕ))
    (hg : g = (((W.map (fun d =>
          (List.range' 1 (sz d)).map (fun i => (nList L)^[i] d))).flatten)).reverse) :
    ((W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse).flatten
      = g := by
  rw [hg]
  exact aq8w2b_flattenRevBlocks L W sz

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：五件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w2b_fstMemFlatten
#print axioms Kepler.Text.TameSpine.aq8w2b_szPos
#print axioms Kepler.Text.TameSpine.aq8w2bB_WDarts
#print axioms Kepler.Text.TameSpine.aq8w2bB_szPosBetwn
#print axioms Kepler.Text.TameSpine.aq8w2bB_hall
#print axioms Kepler.Text.TameSpine.aq8w2bB_flattenEq

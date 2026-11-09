/-
  JcajyduAqLeaf8W2bC — AQ8 波 2b-i-2b：`parts_rev_f_betwn_pure` 的
  `partsCharacterize` 总装（hH 条件槽）。

  ┌─ 范围 ────────────────────────────────────────────────────────
  │ ① aq8w2bC_partsCharacterizeAssembly  五前件 → parts 等式（总装骨架）
  │ ② aq8w2bC_partsRevFBetwnPure         具体形：hfl/hall 由 i-1/i-2a
  │    供应，hH 为条件槽（hH 本体属 i-2c，依赖 hE3/E3 与 B2/B3 组装）。
  │ 条件槽口径：hH 与 hE3 均为接口面，非新前提；`hfl`/`hall` 已真证，
  │ 故本件在 hH 落库后一行代入即得 `parts_rev_f_betwn_pure` 无条件形。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `parts_characterize` 的 `LAST` ↦ `getLast!`；`all` ↦ 逐点 ∀∈（与
  │    TameList39 `partsCharacterize` 逐字同形）。
  │ ② `upt 1 k` ↦ `range' 1 k`；`POWER` ↦ iterate；`rev` ↦ reverse；
  │    `sizel (filter …)` ↦ `.length`（与 countNodeFace 载体同）。
  │ ③ E3 对接面（转 AQ4 车道）：`hE3 : ∀ k f, 0 < k → ∀ i, 1 ≤ i → i ≤ k →
  │    prevEl ((range' 1 k).map f) (f i) = f (i-1)`——数学上即 HOL
  │    `PREV_EL_UPT` 的 map 形；落库后本文件升级为无条件形只需
  │    `exact aq4_...` 一行。属条件槽口径，非新前提。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w2bC_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2bB
import Kepler.Text.TameSpine.TameList39

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 总装骨架（五前件逐字同形） -/

/-- `partsCharacterize` 的装配骨架：五前件齐 ⇒ `parts L r = prt`。 -/
theorem aq8w2bC_partsCharacterizeAssembly (L : fgraph ℕ) {r : List (ℕ × ℕ)}
    {prt : List (List (ℕ × ℕ))} (hne : r ≠ []) (hun : r.Nodup)
    (hfl : prt.flatten = r) (hall : ∀ p ∈ prt, p ≠ [])
    (hH : ∀ p ∈ prt, ∀ d ∈ p, d ≠ r.getLast! →
      (nextEl r d ≠ fList L (eList d) ↔ d = p.getLast!)) :
    partsSpine L r = prt :=
  partsCharacterize L hne hun hfl hall hH

/-! ## §1 具体形：`parts L g = prt`（hH 条件槽） -/

/-- `parts_rev_f_betwn_pure` 的总装形：给定 `g` 的正序块展平等式、
非空/无重、块长正性，以及 hH 边界判别（条件槽），得 `parts L g = prt`。 -/
theorem aq8w2bC_partsRevFBetwnPure (L : fgraph ℕ) (W : List (ℕ × ℕ))
    (sz : ℕ × ℕ → ℕ) (g : List (ℕ × ℕ))
    (hg : g = (((W.map (fun d =>
          (List.range' 1 (sz d)).map (fun i => (nList L)^[i] d))).flatten)).reverse)
    (hne : g ≠ []) (hun : g.Nodup)
    (hpos : ∀ d ∈ W, 0 < sz d)
    (hH : ∀ p ∈ (W.map (fun d =>
            (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse,
          ∀ d ∈ p, d ≠ g.getLast! →
            (nextEl g d ≠ fList L (eList d) ↔ d = p.getLast!)) :
    partsSpine L g = (W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse := by
  have hfl : ((W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse).flatten
      = g :=
    aq8w2bB_flattenEq L W sz g hg
  have hallW := aq8w2b_blocksNonnil L W sz hpos
  have hall : ∀ p ∈ (W.map (fun d =>
        (List.range' 1 (sz d)).reverse.map (fun i => (nList L)^[i] d))).reverse,
      p ≠ [] := by
    intro p hp
    exact hallW p (List.mem_reverse.mp hp)
  exact partsCharacterize L hne hun hfl hall hH

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w2bC_partsCharacterizeAssembly
#print axioms Kepler.Text.TameSpine.aq8w2bC_partsRevFBetwnPure

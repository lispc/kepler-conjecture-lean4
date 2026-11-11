/-
  Kepler.Text.Reduction5J5K2 — Lane A3：`reduction_K2` 陈述定义面（K2 包装的
  K2CONCLUSION / K2Asm 孪生；HOL reduction4.hl:1276–1442）。

  ┌─ 本件范围（PARTIAL）─────────────────────────────────────────────
  │ 本文件只落**陈述定义面**（`reductionK2Asm` / `reductionK2Concl` 两个
  │ `def` + 展开引理），不落 `reductionK2` 本体——28 合取装配的精确卡点
  │ 见 DELIVERY-nb45 §2（多处非投影换向 + A2 两件上游阻塞）。
  │ 定义面落库后，下一轮 `reductionK2` 可直接 `refine ⟨?_, …, ?_⟩` 开写。
  └────────────────────────────────────────────────────────────────

  陈述逐字对 HOL reduction4.hl:1276–1442（活合取；注释掉的旧合取不携入）。
-/

import Kepler.Text.Reduction5J5K1Statement
import Kepler.Text.Reduction3DefsAssumption
import Kepler.Assembly.GoodListDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts listPairs)
open Kepler.Text.Reduction3 (elementPre newvertexPrepped)

/-- **HOL `reduction_K2` 假设块**（reduction4.hl:1280–1287，八前提逐字）：
`good_list / good_list_nodes / is_restricted / element_pre /
newvertex_prepped / marked_list / ¬final_list / transform_count = k`。
与 `reductionK1Asm` 逐字同形（K1/K2 共用同一假设块）。 -/
def reductionK2Asm (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ) : Prop :=
  GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
    elementPre L N ∧ newvertexPrepped L N r x ∧
    Marked L N r x ∧ ¬ finalList L r ∧ transformCount L N r x = k

/-- **HOL `reduction_K2` 结论块**（reduction4.hl:1289–1341，14 个活合取逐字序）：
INDEX 7（:1289–1310）/ MISC（:1312）/ BETWN 5（:1315–1334）/ UVNS（:1336–1341）。
不携入 HOL 注释掉的旧合取（mem_z0_ri / not_next_core0_y_z 通用 i /
not_mem_yi_zi_list_of_darts / n1_diff_n0 / index_snd_x / not_mem_snd_x_zx /
not_mem_snd_x_fy / old19）。 -/
def reductionK2Concl (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k : ℕ) : Prop :=
  -- INDEX 1（:1289）
  (indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
    indexf (ztrans L N r x (k - 1)) x (findFaceDarts L x)) ∧
  -- INDEX 2（:1292）
  (∀ i : ℕ, i + 1 < k →
    indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
      indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  -- INDEX 3（:1295）
  (∀ i : ℕ, i + 1 < k →
    indexf (ytrans L N r x 0) (ztrans L N r x i) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  -- INDEX 4（:1298）
  (∀ i : ℕ, i + 1 < k →
    indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  -- INDEX 5（:1301）
  (indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) x (findFaceDarts L x)) ∧
  -- INDEX 6（:1304）
  (indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x)) ∧
  -- INDEX 7（:1307）
  (∀ i : ℕ, i + 1 < k →
    (nextEl (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1 =
        (ytrans L N r x (i + 1)).1 ↔
      nextEl (core L r) (ztrans L N r x i).1 = (ytrans L N r x (i + 1)).1)) ∧
  -- MISC（:1312）
  (∀ i : ℕ, i < k → ztrans L N r x 0 ∈ rtrans L N r x i) ∧
  -- BETWN 1：betwn_corek_z_x（:1315）
  ((ztrans L N r x (k - 1)).1 ≠ x.1 →
    between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
      between (core L r) (ztrans L N r x (k - 1)).1 x.1) ∧
  -- BETWN 2：n1_diff_n0（:1318）
  ({z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
      z ∉ N.flatten.map (fun d => d.1)} =
    {z : ℕ | z ∈ (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).map
      (fun d => d.1)}) ∧
  -- BETWN 3：not_next_core_0_i 通用 i（:1320）
  (∀ i : ℕ, i < k →
    between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
    nextEl (core L (rtrans L N r x i)) (ytrans L N r x i).1 ≠
      (ztrans L N r x i).1) ∧
  -- BETWN 4：not_next_core_0_i 在 0（:1324）
  (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
    nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
      (ytrans L N r x 0).1) ∧
  -- BETWN 5：betwn_core0_z_y（:1328）
  (∀ i : ℕ, i + 1 < k → (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1 →
    between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 =
      between (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1
        (ytrans L N r x (i + 1)).1) ∧
  -- UVNS（:1336）
  (∀ v : ℕ, (Kepler.Assembly.prevEl (core L r) v, v) = x →
    (let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
     let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v uvns
     let vs' := vs.filterMap id
     (∀ i : ℕ, i + 1 < vs'.length →
        indexf v (vs'.getD i 0) (core L r) < indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
      (∀ i : ℕ,
        let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
        ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
          i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
        d ∈ listPairs (core L r))))

end Kepler.Text.Reduction5

/-! 探针（编译即执行；两 `def` 零证明义务，公理面应为空） -/
#print axioms Kepler.Text.Reduction5.reductionK2Asm
#print axioms Kepler.Text.Reduction5.reductionK2Concl
#check @Kepler.Text.Reduction5.reductionK2Asm
#check @Kepler.Text.Reduction5.reductionK2Concl

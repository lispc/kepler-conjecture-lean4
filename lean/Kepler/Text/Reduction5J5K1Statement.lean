/-
  Kepler.Text.Reduction5J5K1Statement — J5-2 续段：`reduction_K1`（reduction4.hl:253，170L）
  的**陈述段**（本波只落陈述，不落证体）。

  ┌─ 为什么是 def ────────────────────────────────────────────────────
  │ 树内 K 链的陈述按 `Reduction5K5` 的既定形打包：`reductionK4Asm` /
  │ `reductionK4Concl` / `reductionK5Concl` 都是 `def … : Prop`，主定理形是
  │ `(∀ L N r x k, K4Asm → K4Concl) → assumptionSetK10 …`。本文件照此补
  │ K1 的三件：`reductionK1Asm` / `reductionK1Concl` / `reductionK1Statement`。
  │ 证体（`reductionK1Statement` 的证明）留下一波；本文件全部是定义，无证明义务。
  └────────────────────────────────────────────────────────────────

  ┌─ 归属对账（HOL Light Flyspeck reduction4.hl:253-373）─────────────
  │ `reductionK1Asm`（:257-264，八前提逐字）：
  │   good_list L ∧ good_list_nodes L ∧ is_restricted (hypermap_of_list L) ∧
  │   element_pre L N ∧ newvertex_prepped L N r x ∧ marked_list L N r x ∧
  │   ¬final_list L r ∧ transform_count L N r x = k
  │ `reductionK1Concl`（:268-371，前件表）：28 个顶层合取，逐条对账见下表。
  │ `reductionK1Statement`（:254/:373 全句形）：
  │   (∀ L N r x k, reductionK1Asm … → reductionK1Concl L N r x k) ⇒ assumption_setK10
  └────────────────────────────────────────────────────────────────

  ┌─ 合取对账表（HOL 行号 → Lean 合取序号；组名用 HOL 注释里的原文）────
  │ #   HOL 行    组                内容摘要
  │ 1   270-273   (V)               ∀ v, (prev_el (core L r) v, v) = x ⇒
  │                                 (∀ i < k, prev_el (core L (rtrans i)) v, v = x) ∧
  │                                 FST (next_el (find_face L x) x) = v
  │ 2   276-277   (INDEX)           indexf (FST (next_el fx x)) (FST y0) (core L r) = …
  │ 3   278-279   (INDEX)           indexf (FST z(PRE k)) (FST x) (core L r) = …
  │ 4   280-282   (INDEX)           ∀ i, SUC i < k ⇒ indexf (FST z_i) (FST y(SUC i)) …
  │ 5   283-285   (INDEX)           ∀ i, SUC i < k ⇒ indexf y0 z_i fx ≤ indexf y0 y(SUC i) fx
  │ 6   286-288   (INDEX)           ∀ i, SUC i < k ⇒ indexf y0 y(SUC i) fx ≤ indexf y0 z(SUC i) fx
  │ 7   289-290   (INDEX)           indexf (next_el fx x) z(PRE k) fx ≤ indexf … x fx
  │ 8   291-292   (INDEX)           indexf (next_el fx x) y0 fx ≤ indexf … z(PRE k) fx
  │ 9   293-296   (INDEX)           ∀ i, 0 < i ∧ i < k ⇒
  │                                 (next_el (core (rtrans i)) (FST z(PRE i)) = FST y_i ⇔
  │                                  next_el (core L r) (FST z(PRE i)) = FST y_i)
  │ 10  299-301   (BETWN)           FST (z(PRE k)) ≠ FST x ⇒ betwn (core (rtrans k)) … = betwn (core L r) …
  │ 11  304-305   (BETWN)           set_of_list DIFF 等式（FST 集合，ntrans 1 ∖ N = betwn y0 z0）
  │ 12  308-310   (BETWN)           ¬(next_el (core L r) (FST y0) = FST z0 ∧ sizel (betwn y0 z0) = 0)
  │ 13  311-314   (BETWN)           ∀ i, 0 < i ∧ i < k ⇒ ¬(next_el (core (rtrans i)) (FST y_i) = FST z_i ∧ …)
  │ 14  317-320   (BETWN)           ∀ i, 0 < i ∧ i < k ⇒ (FST z(PRE i) ≠ FST y_i ⇒ betwn 等式)
  │ 15  328       (MEM)             MEM (FST x) (core (rtrans k))
  │ 16  329       (MEM)             MEM (FST z(PRE k)) (core (rtrans k))
  │ 17  330       (MEM)             ∀ u, MEM u r ⇒ MEM (FST u) (core L r)
  │ 18  331       (MEM)             ∀ i < k, MEM (FST y_i) (core L r)
  │ 19  332       (MEM)             ∀ i < k, MEM (FST z_i) (core L r)
  │ 20  333-335   (MEM)             ∀ i j, 0 < i ∧ i < k ∧ j < k ⇒
  │                                 MEM (FST y_j) (core (rtrans i)) ∧ MEM (FST z_j) (core (rtrans i))
  │ 21  338       (SIZE AND MISC)   FST (prev_el r z0) = FST z0
  │ 22  339       (SIZE AND MISC)   ¬(FST y0 = FST z0)
  │ 23  340       (SIZE AND MISC)   ∀ i < k, ¬(y_i = z_i)
  │ 24  341       (SIZE AND MISC)   1 ≤ sizel (find_face L x)
  │ 25  342       (SIZE AND MISC)   1 < sizel (core L r)
  │ 26  345-347   (PREPPED)         ∀ i < k, iota (sizel (undup (MAP FST (flatten (ntrans i)))))
  │                                 (sizel (betwn y_i z_i)) = MAP FST (betwn y_i z_i)
  │ 27  350-353   (split_normal_list) let (f1,f2) = split_normal_list … in
  │                                 ¬MEM (core L f1) (quotient_list L N) ∧ ¬MEM (core L f2) (quotient_list L N)
  │ 28  356-371   (UVNS)            ∀ v, (prev_el (core L r) v, v) = x ⇒
  │                                 let uvns = core_triple_v4 …; let vs = dest_triple_full …;
  │                                 let vs' = MAP the (filter isSome vs) in
  │                                 (∀ i, SUC i < sizel vs' ⇒ indexf v (EL i vs') (core L r) < …) ∧
  │                                 (∀ i, (… isSome 两相邻 ∧ SUC i < sizel vs ∧
  │                                        MEM d (list_of_darts (quotient_list L N))) ⇒ MEM d (list_pairs (core L r)))
  │ 顶层合取 28 个；含嵌套（#1 的 2 子合取、#9/#20 的合取与双论域、#28 的 2 子合取）
  │ 约 40 个。行号已剔除原文件中的注释行（:295/:302/:306/:307/:326/:337/:344/:355）。
  └────────────────────────────────────────────────────────────────

  ┌─ 渲染约定（按 `assumptionSetK10`（Reduction3DefsAssumption:145）与
  │  `reductionK4Concl`（Reduction5K5:70）的既有写法）──────────────────
  │ · `PRE k` ↦ `k - 1`；`SUC i` ↦ `i + 1`；`FST` ↦ `.1`；`sizel` ↦ `List.length`；
  │   `iota a b` ↦ `List.range' a b`；`undup` ↦ `List.dedup`；
  │   `MAP the (filter isSome vs)` ↦ `vs.filterMap id`；`EL i vs` ↦ `vs.getD i none`；
  │   `set_of_list X DIFF set_of_list Y` ↦ 集合差集等式（`{z | z ∈ X ∧ z ∉ Y} = {z | z ∈ W}`）；
  │   `list_of_darts` ↦ `listOfDarts`；`list_pairs` ↦ `listPairs`。
  │ · `∀ i, A ∧ B ⇒ C` 一律柯里化 `∀ i, A → B → C`（同 `betwnCoreReductionLemma`）。
  │ · (UVNS) 的 `let d = the (EL i vs),the (EL (SUC i) vs)` 按 `assumptionSetK10`
  │   的写法：`let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0)`。
  │ · 槽参数化：`GoodNodesL` / `IsRestrictedL` / `Marked` 与 `reductionK4Asm` 同款；
  │   结论侧 `assumptionSetK10` 原样引用 `Reduction3.assumptionSetK10`。
  └────────────────────────────────────────────────────────────────

  ┌─ 下一波证体路线（本文件不落证）──────────────────────────────────
  │ HOL 证体 48 行（:375-:422）：展开 `assumption_setK10`，取内层全称的 (L N r x k)，
  │ 用假设表 H 的实例，再用 `final_assumption_mem_uniq`（本车道已落
  │ `finalAssumptionMemUniq`，Reduction5J5Termination）补 MEM / 计数非零两条，
  │ 其余靠定义级/重写收口。Lean 侧预计是「前件表 → 结论表」的逐条对账，
  │ 实际规模待试写。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
  本文件不含证明（全部为 def）；下一波的 `reductionK1Statement` 证明另起文件。
-/

import Kepler.Text.Reduction3DefsAssumption
import Kepler.Text.Reduction5K5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts fList listOfDarts listPairs)

/-- **HOL `reduction_K1` 的假设块**（reduction4.hl:257-264，八前提逐字）：
good_list / good_list_nodes / is_restricted / element_pre / newvertex_prepped /
marked_list / ¬final_list / transform_count = k，后三者与 `reductionK4Asm` 同槽形。 -/
def reductionK1Asm (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ) : Prop :=
  GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
    Kepler.Text.Reduction3.elementPre L N ∧
    Kepler.Text.Reduction3.newvertexPrepped L N r x ∧
    Marked L N r x ∧ ¬ finalList L r ∧ transformCount L N r x = k

/-- **HOL `reduction_K1` 的前件表**（reduction4.hl:268-371）：28 个顶层合取，
顺序与原文一致（对账表见文件头）。 -/
def reductionK1Concl (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k : ℕ) : Prop :=
  -- 1 (V)
  (∀ v,
    (prevEl (core L r) v, v) = x →
      (∀ i, i < k → (prevEl (core L (rtrans L N r x i)) v, v) = x) ∧
        (nextEl (findFaceDarts L x) x).1 = v) ∧
  -- 2-9 (INDEX)
  (indexf (nextEl (findFaceDarts L x) x).1 (ytrans L N r x 0).1 (core L r) =
    indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x)) ∧
  (indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
    indexf (ztrans L N r x (k - 1)) x (findFaceDarts L x)) ∧
  (∀ i, i + 1 < k →
    indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
      indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  (∀ i, i + 1 < k →
    indexf (ytrans L N r x 0) (ztrans L N r x i) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  (∀ i, i + 1 < k →
    indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) (findFaceDarts L x) ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) (findFaceDarts L x)) ∧
  (indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) x (findFaceDarts L x)) ∧
  (indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0) (findFaceDarts L x) ≤
    indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x (k - 1)) (findFaceDarts L x)) ∧
  (∀ i, 0 < i → i < k →
    (nextEl (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 ↔
      nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1)) ∧
  -- 10-14 (BETWN)
  ((ztrans L N r x (k - 1)).1 ≠ x.1 →
    between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
      between (core L r) (ztrans L N r x (k - 1)).1 x.1) ∧
  {z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
      z ∉ N.flatten.map (fun d => d.1)} =
    {z : ℕ | z ∈ (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).map
      (fun d => d.1)} ∧
  ¬ ((nextEl (core L r) (ytrans L N r x 0).1 = (ztrans L N r x 0).1) ∧
      (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length = 0) ∧
  (∀ i, 0 < i → i < k →
    ¬ ((nextEl (core L (rtrans L N r x i)) (ytrans L N r x i).1 = (ztrans L N r x i).1) ∧
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length = 0)) ∧
  (∀ i, 0 < i → i < k → (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 →
    between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1 =
      between (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1) ∧
  -- 15-20 (MEM)
  x.1 ∈ core L (rtrans L N r x k) ∧
  (ztrans L N r x (k - 1)).1 ∈ core L (rtrans L N r x k) ∧
  (∀ u, u ∈ r → u.1 ∈ core L r) ∧
  (∀ i, i < k → (ytrans L N r x i).1 ∈ core L r) ∧
  (∀ i, i < k → (ztrans L N r x i).1 ∈ core L r) ∧
  (∀ i j, 0 < i → i < k → j < k →
    (ytrans L N r x j).1 ∈ core L (rtrans L N r x i) ∧
      (ztrans L N r x j).1 ∈ core L (rtrans L N r x i)) ∧
  -- 21-25 (SIZE AND MISC)
  (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1 ∧
  (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1 ∧
  (∀ i, i < k → ytrans L N r x i ≠ ztrans L N r x i) ∧
  1 ≤ (findFaceDarts L x).length ∧
  1 < (core L r).length ∧
  -- 26 (PREPPED)
  (∀ i, i < k →
    (List.range' ((ntrans L N r x i).flatten.map (fun d => d.1)).dedup.length
      (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length) =
    (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).map (fun d => d.1)) ∧
  -- 27 (split_normal_list)
  (let s := splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0) (prevEl r (ztrans L N r x 0))
   core L s.1 ∉ quotientList L N ∧ core L s.2 ∉ quotientList L N) ∧
  -- 28 (UVNS)
  (∀ v,
    (prevEl (core L r) v, v) = x →
      (let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
       let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v uvns
       let vs' := vs.filterMap id
       (∀ i, i + 1 < vs'.length →
          indexf v (vs'.getD i 0) (core L r) < indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
        (∀ i,
          let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
          ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
            i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
          d ∈ listPairs (core L r))))

/-- **HOL `reduction_K1` 的整句形**（reduction4.hl:254/:373）：
「前件表对一切 (L,N,r,x,k) 成立 ⇒ assumption_setK10」。与九槽顶层 `hK4` 的槽类型
（`(∀ …, reductionK4Asm → reductionK4Concl) → assumptionSetK10`）同构。 -/
def reductionK1Statement (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop) : Prop :=
  (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK1Asm GoodNodesL IsRestrictedL Marked L N r x k →
        reductionK1Concl L N r x k) →
    Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked

end Kepler.Text.Reduction5

/-! 探针（编译即执行）：签名与公理面（defs 无公理依赖） -/
#check @Kepler.Text.Reduction5.reductionK1Asm
#check @Kepler.Text.Reduction5.reductionK1Concl
#check @Kepler.Text.Reduction5.reductionK1Statement
#print axioms Kepler.Text.Reduction5.reductionK1Asm
#print axioms Kepler.Text.Reduction5.reductionK1Concl
#print axioms Kepler.Text.Reduction5.reductionK1Statement

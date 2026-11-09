/-
  Kepler.Text.Reduction3DefsAssumption — J 战役 J3 定义层 D3b（大合取规格层）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction3.hl`）──
  │   assumption_set3    reduction3.hl:1818-1880 → §A assumptionSet3
  │   assumption_setK10  reduction3.hl:3559-3676 → §B assumptionSetK10
  │ **双落指针**：`assumption_setK10` 在 reduction4.hl:33 有第二份定义
  │ （`open Reduction3` 下同名遮蔽，逐字对齐）——**只在此处落一处**，
  │ J1 的 Reduction4 车道**勿重落**；J3 装配时以本件为唯一家
  │ （j1w1 DELIVERY §2-6 同判）。assumption_set3 无第二份。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体插槽设计（保守 + 可逆；两项挂起裁决的解耦手段）────────────
  │ 三合取原子无法直接落成（理由逐条）：
  │ ① `marked_list`（tame_defs2.hl:550-564）**树内双载体分叉未裁**：
  │    Spine 侧 `TameList13.MarkedListSpineFull {L} (hL : GoodList L) N r d`
  │    吃显式 hL；链岛侧尚无忠实移植（需 is_restricted/normal_list/
  │    flag_list/s_flag_list/find_list 五件新定义）。→ 槽 `Marked`。
  │ ② `good_list_nodes`（tame_defs2.hl:67-68）：树内忠实形
  │    `TameLp.GoodListNodesTl L (hL : GoodList L)` 同样吃 hL
  │    （TameLp.lean:5278）→ 槽 `GoodNodesL`（避免把 good_list 从
  │    合取挪进 binder 的陈述变形）。
  │ ③ `is_restricted (hypermap_of_list L)`：`Hypermap.IsRestricted`
  │    （Hypermap.lean:9645）经 `TameLp.hypermapOfList L hL`
  │    （TameLp:5188，吃 hL）→ 槽 `IsRestrictedL`。
  │ **实例化配方**（裁决后一行代入，陈述零改）：
  │   GoodNodesL  := fun L => ∀ (hL : GoodList L), GoodListNodesTl L hL
  │   IsRestrictedL := fun L => ∀ (hL : GoodList L), (hypermapOfList L hL).IsRestricted
  │   Marked := fun L N r x => ∀ (hL : GoodList L), MarkedListSpineFull hL N r x
  │            （Spine 载体，j1w1-B5 先例——待裁决，见 DELIVERY §6-1）
  │   `good_list L` 原子直接 ↦ `GoodList L`（GoodListDefs.lean:72，无 hL）。
  │ 其余原子全部直落：newvertexPrepped（D3a）/elementPre（D1）/
  │ coreTripleV4/destTripleFull（D1）/finalList/quotientList/
  │ transformCount/ytrans/ztrans/rtrans/ntrans/splitNormalList/core/
  │ indexf（Reduction5Base）/findFaceDarts/listOfDarts/listPairs（Assembly）。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐字折算记档（DIFFERS）─────────────────────────────────────
  │ `S/SUC n` ↦ `n + 1`；`PRE k` ↦ `k - 1`（Nat 截断）；`sizel` ↦ `.length`；
  │ `uniq` ↦ `.Nodup`；`MEM` ↦ `∈`；`0..`/`iota m l` ↦ `List.range' m l`；
  │ `EL i vs` ↦ `vs.getD i none`、`the (EL i vs)` ↦ `… .getD 0`
  │ （HOL EL 越界为任意值；此处分支均被 `isSome`/`SUC i < sizel` 守卫，
  │  junk 支不可达——D1 同制式）；`DIFF` ↦ 集合差（set-builder）；
  │ `MAP the (filter isSome vs)` ↦ `vs.filterMap id`；
  │ `prev_el (core L r) v, v = x` 是**对组**等式 ↦ `(prevEl …, v) = x`。
  │ 合取顺序逐字保留（set3 与 K10 的 newvertex_prepped/element_pre
  │ 先后不同，各自照抄，勿统一）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3DefsNewVertex`（D3a，闭包含 D1）。
  │ 闭包零 `Kepler.Assembly` 主模块、零 TameSpine。本文件零证明义务；
  │ 零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsNewVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core finalList indexf ntrans quotientList rtrans
  splitNormalList transformCount ytrans ztrans)

/-! ## §A `assumption_set3`（reduction3.hl:1818-1880）

14 条前提原子 + 26 条结论合取。前提：good_list / good_list_nodes /
is_restricted / newvertex_prepped / marked_list / element_pre / ¬final_list /
core_triple_v4 = uvns / dest_triple_full (core L r) v uvns = vs /
MAP the (filter isSome vs) = vs' / transform_count = k / find_face = fx /
(prev_el (core L r) v, v) = x。 -/

/-- HOL `assumption_set3`（reduction3.hl:1818-1880）。三载体插槽见文件头。 -/
def assumptionSet3
    (GoodNodesL : fgraph ℕ → Prop)
    (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop) : Prop :=
  ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (k : ℕ) (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ)) (vs' : List ℕ)
    (fx : List Dart) (v : ℕ),
    GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
    newvertexPrepped L N r x ∧ Marked L N r x ∧ elementPre L N ∧
    ¬ finalList L r ∧
    coreTripleV4 L N r x = uvns ∧
    destTripleFull (core L r) v uvns = vs ∧
    vs.filterMap id = vs' ∧
    transformCount L N r x = k ∧
    findFaceDarts L x = fx ∧
    (prevEl (core L r) v, v) = x →
    transformCount L N r x ≠ 0 ∧
    0 < transformCount L N r x ∧
    x.1 = prevEl (core L r) v ∧
    x ∈ fx ∧ fx.Nodup ∧
    1 ≤ fx.length ∧
    1 < (core L r).length ∧
    (∀ i, i + 1 < k → indexf (ytrans L N r x 0) (ztrans L N r x i) fx ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx) ∧
    (∀ i, i + 1 < k → indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) fx) ∧
    indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ≤ indexf (nextEl fx x) x fx ∧
    indexf (nextEl fx x) (ytrans L N r x 0) fx ≤
      indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ∧
    nextEl fx x ∈ r ∧
    (∀ i, i < k → ytrans L N r x i ≠ ztrans L N r x i) ∧
    (∀ i, i < k → ztrans L N r x i ∈ r) ∧
    (∀ i, i < k → ytrans L N r x i ∈ r) ∧
    nextEl fx x ∈ fx ∧
    (∀ i, i < k → ytrans L N r x i ∈ fx) ∧
    (∀ i, i < k → ztrans L N r x i ∈ fx) ∧
    (core L r).Nodup ∧
    (nextEl fx x).1 = v ∧
    (∀ u ∈ r, u.1 ∈ core L r) ∧
    indexf v (ytrans L N r x 0).1 (core L r) =
      indexf (nextEl fx x) (ytrans L N r x 0) fx ∧
    indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
      indexf (ztrans L N r x (k - 1)) x fx ∧
    (∀ i, i + 1 < k →
      indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
      indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) fx) ∧
    (∀ i, i + 1 < vs'.length →
      indexf v (vs'.getD i 0) (core L r) <
      indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
    (∀ i, (let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
      ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
        i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
      d ∈ listPairs (core L r)))

/-! ## §B `assumption_setK10`（reduction3.hl:3559-3676；双落见文件头）

前提与 set3 同集（**但 element_pre 在 newvertex_prepped 之前**，逐字保留），
结论 = 42 条合取：set3 的 26 条 + core L (rtrans … k) 三件 + betwn 桥两件
+ iota/MAP FST 端点件 + ∀i∈(0,transform_count) 的八合一嵌套块
（含四个内层 `∀ i/∀ i'` 影子绑定，逐字保留）+ prev_el r z 首步等式
+ ntrans 一步的集合差等式 + 元素不交 + FST(y₀)≠FST(z₀)
+ split_normal_list 两片 core 不在 quotient_list。 -/

/-- HOL `assumption_setK10`（reduction3.hl:3559-3676）。**全树唯一落点**
（reduction4.hl:33 的第二份勿重落）。三载体插槽同 `assumptionSet3`。 -/
def assumptionSetK10
    (GoodNodesL : fgraph ℕ → Prop)
    (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop) : Prop :=
  ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (k : ℕ) (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ)) (vs' : List ℕ)
    (fx : List Dart) (v : ℕ),
    GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
    elementPre L N ∧ newvertexPrepped L N r x ∧ Marked L N r x ∧
    ¬ finalList L r ∧
    coreTripleV4 L N r x = uvns ∧
    destTripleFull (core L r) v uvns = vs ∧
    vs.filterMap id = vs' ∧
    transformCount L N r x = k ∧
    findFaceDarts L x = fx ∧
    (prevEl (core L r) v, v) = x →
    (core L (rtrans L N r x k)).Nodup ∧
    x.1 ∈ core L (rtrans L N r x k) ∧
    (ztrans L N r x (k - 1)).1 ∈ core L (rtrans L N r x k) ∧
    ((ztrans L N r x (k - 1)).1 ≠ x.1 →
      between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
      between (core L r) (ztrans L N r x (k - 1)).1 x.1) ∧
    (∀ i, i < k →
      List.range' ((ntrans L N r x i).flatten.map (fun d => d.1)).dedup.length
        (between fx (ytrans L N r x i) (ztrans L N r x i)).length =
      (between fx (ytrans L N r x i) (ztrans L N r x i)).map (fun d => d.1)) ∧
    (∀ i, i < k → (prevEl (core L (rtrans L N r x i)) v, v) = x) ∧
    (core L r).Nodup ∧
    ¬ ((nextEl (core L r) (ytrans L N r x 0).1 = (ztrans L N r x 0).1) ∧
        (between fx (ytrans L N r x 0) (ztrans L N r x 0)).length = 0) ∧
    (∀ i, i < transformCount L N r x → (ytrans L N r x i).1 ∈ core L r) ∧
    (∀ i, i < transformCount L N r x → (ztrans L N r x i).1 ∈ core L r) ∧
    (∀ i, 0 < i → i < transformCount L N r x →
      (core L (rtrans L N r x i)).Nodup ∧
      ¬ ((nextEl (core L (rtrans L N r x i)) (ytrans L N r x i).1 =
            (ztrans L N r x i).1) ∧
          (between fx (ytrans L N r x i) (ztrans L N r x i)).length = 0) ∧
      (((ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1) →
        between (core L r) (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1 =
        between (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1
          (ytrans L N r x i).1) ∧
      (nextEl (core L (rtrans L N r x i)) (ztrans L N r x (i - 1)).1 =
          (ytrans L N r x i).1 ↔
        nextEl (core L r) (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1) ∧
      (∀ i, i < transformCount L N r x → (ytrans L N r x i).1 ∈ core L r) ∧
      (∀ i, i < transformCount L N r x → (ztrans L N r x i).1 ∈ core L r) ∧
      (∀ i', i' < transformCount L N r x →
        (ytrans L N r x i').1 ∈ core L (rtrans L N r x i)) ∧
      (∀ i', i' < transformCount L N r x →
        (ztrans L N r x i').1 ∈ core L (rtrans L N r x i))) ∧
    (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1 ∧
    {z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
        z ∉ N.flatten.map (fun d => d.1)} =
      {z : ℕ | z ∈ (between fx (ytrans L N r x 0) (ztrans L N r x 0)).map
        (fun d => d.1)} ∧
    (∀ i, i ∈ N.flatten.map (fun d => d.1) →
      i ∉ (between fx (ytrans L N r x 0) (ztrans L N r x 0)).map (fun d => d.1)) ∧
    (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1 ∧
    (let s := splitNormalList L r fx (ytrans L N r x 0) (prevEl r (ztrans L N r x 0));
      core L s.1 ∉ quotientList L N ∧ core L s.2 ∉ quotientList L N) ∧
    transformCount L N r x ≠ 0 ∧
    0 < transformCount L N r x ∧
    x.1 = prevEl (core L r) v ∧
    x ∈ fx ∧ fx.Nodup ∧
    1 ≤ fx.length ∧
    1 < (core L r).length ∧
    (∀ i, i + 1 < k → indexf (ytrans L N r x 0) (ztrans L N r x i) fx ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx) ∧
    (∀ i, i + 1 < k → indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) fx) ∧
    indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ≤ indexf (nextEl fx x) x fx ∧
    indexf (nextEl fx x) (ytrans L N r x 0) fx ≤
      indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ∧
    nextEl fx x ∈ r ∧
    (∀ i, i < k → ytrans L N r x i ≠ ztrans L N r x i) ∧
    (∀ i, i < k → ztrans L N r x i ∈ r) ∧
    (∀ i, i < k → ytrans L N r x i ∈ r) ∧
    nextEl fx x ∈ fx ∧
    (∀ i, i < k → ytrans L N r x i ∈ fx) ∧
    (∀ i, i < k → ztrans L N r x i ∈ fx) ∧
    (core L r).Nodup ∧
    (nextEl fx x).1 = v ∧
    (∀ u ∈ r, u.1 ∈ core L r) ∧
    indexf v (ytrans L N r x 0).1 (core L r) =
      indexf (nextEl fx x) (ytrans L N r x 0) fx ∧
    indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
      indexf (ztrans L N r x (k - 1)) x fx ∧
    (∀ i, i + 1 < k →
      indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
      indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) fx) ∧
    (∀ i, i + 1 < vs'.length →
      indexf v (vs'.getD i 0) (core L r) <
      indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
    (∀ i, (let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
      ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
        i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
      d ∈ listPairs (core L r)))

end Kepler.Text.Reduction3

-- 探针（编译即执行；陈述槽零证明义务，此处核对形与打印）
#check @Kepler.Text.Reduction3.assumptionSet3
#check @Kepler.Text.Reduction3.assumptionSetK10
#print axioms Kepler.Text.Reduction3.newvertexPreppedOfFinal

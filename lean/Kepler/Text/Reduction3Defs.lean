/-
  Kepler.Text.Reduction3 — J 战役 J3 定义层首批（D1：列表级自含核心）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──────
  │ 本批 = reduction3.hl 定义层（reduction3.hl:28-164 NEW DEFS 段 +
  │ tame_defs2.hl 枚举段）的**最底自含切片**（全列表级，不触图层）：
  │   triple_data_v4     reduction3.hl:28-34  → §B tripleDataV4
  │   core_triple_v4     reduction3.hl:36-38  → §B coreTripleV4
  │   dest_triple0_step  reduction3.hl:110-119 → §C destTriple0Step
  │   dest_triple0_rcons reduction3.hl:155-164 → §C destTriple0Rcons
  │   prebatch           reduction3.hl:148-151 → §C prebatch
  │   batch0             reduction3.hl:131-133 → §C batch0
  │   dest_triple0       tame_defs2.hl:599-613 → §C destTriple0
  │   dest_triple_full   tame_defs2.hl:615-624 → §C destTripleFull
  │   element_pre        reduction3.hl:72-74   → §A elementPre
  │ 复用树内既有件（不重落，S11 忠实 def 层 TameLp.lean:5264/5267）：
  │   list_of_elements / elements_of_list → TameLp.listOfElements /
  │   elementsOfList
  │ 旁置基座（已在树内，复用不重落）：
  │   list_of_elements   :28 → TameLp.listOfElements（TameLp:5264）
  │   elements_of_list   :29 → TameLp.elementsOfList（TameLp:5267）
  │   （勘误：工单/初稿曾记"零命中本批落"，S11 层已落，语义同形）
  │ 定义即引理（零义务直证件 3 条）：
  │   coreTripleV4_length / prebatchZero / destTriple0Nil。
  │ **触发器判词**（工单「nfgtrans'/match_quotient_list 最高风险」）：
  │   两者均**不需要 quot/商类型**——`quotient_list` 是纯列表分区函数
  │   （W0 已落 `Reduction5.quotientList`），`match_quotient_list` 是
  │   布尔合取（子集 + 等式）；`nfgtrans'` 是 foldl（本批 D1 已把其
  │   foldl 载荷 core_triple_v4 落净，D2 只需图层步进）。自然可移植，
  │   **不触发规模重估**。判词全文见车道 DELIVERY.md §风险判词。
  │ D2（图层：subdiv_triple_step/subdiv_single_step/subdivFace0_beta/
  │ nfgtrans'/b_nfgtrans0/match_quotient_list）与 D3（合取规格层：
  │ core_split_normal_list_assumption/r_trans_eq_assumption/newvertex/
  │ newvertex_prepped/assumption_set3/assumption_setK10）本批未落，
  │ 路线图见 DELIVERY.md §路线图。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ 与 j1w1 `Kepler.Text.Reduction4` 同岛（Reduction 链岛）：imports =
  │ `Kepler.Text.Reduction5Base`（W0 定义基座：transform 塔/quotientList）
  │ + `Kepler.Graphs.ListAuxLemmas`。import 闭包零 `Kepler.Assembly`
  │ 主模块、零 `Kepler.Text.TameSpine.*`（岛纪律见 Reduction5Base 头注）。
  │ **不消费** TameList17 侧 splitNormalListSpine（TameList17:93
  │ off-by-one DEF-FIX 在案件）；本批定义全部经 Reduction5Base 侧
  │ （splitNormalList 正确形 `range' 1 (sz-1)`），零 TameSpine 触点。
  │ 零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────

  ┌─ junk-value 约定（DIFFERS 记档，与树内既有惯例同制式）─────────
  │ HOL 的 `HD/LAST/THE` 在空表/None 上取 Hilbert 选择（任意值）；
  │ Lean 侧统一换成**确定性缺省**：`LAST` ↦ `List.getLastD <缺省>`、
  │ `HD` ↦ `List.headD <缺省>`、`the x` ↦ `x.getD 0`。可达输入上
  │ 分支结构保证 junk 支不可达（prebatch/prebatch 的段表元素恒非空、
  │ core_triple 的段恒以 SOME 收尾），junk 支差异不影响任何消费定理
  │ 的语义；与 Reduction5Base `headD (0,0)`、Graphs `getD` 同制式。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Graphs.ListAuxLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart quotientList transformCount ytrans ztrans)
open Kepler.Text.TameLp (listOfElements elementsOfList)

/-! ## §A 旁置基座：`element_pre`

`list_of_elements`/`elements_of_list`（list_hypermap-compiled.hl:28-29）
**树内已有**：`Kepler.Text.TameLp.listOfElements`/`elementsOfList`
（TameLp.lean:5264/5267，S11 忠实 def 层），复用不重落。
`element_pre`（reduction3.hl:72-74）说 `quotient_list L N` 的元素集恰为
`{0, …, sizel (undup (MAP FST (flatten N))) - 1}`。HOL 右端 `0..PRE n` 是
**闭区间数段集合**（HOL Light `sets.ml` 的 `m..n = {x | m ≤ x ∧ x ≤ n}`，
CARD_NUMSEG 语义；非 `upt` 列表——reduction2.hl:281 `set_of_list_numseg` +
`CARD_NUMSEG` 为证）。`0 ≤ x` 在 ℕ 上恒真，故 Lean 侧落
`{i : ℕ | i ≤ n - 1}`（Nat 截断减即 HOL `PRE`）。-/

/-- HOL `element_pre`（reduction3.hl:72-74）。Prop 形定义，
陈述槽零证明义务。 -/
def elementPre (L : fgraph ℕ) (N : List (List Dart)) : Prop :=
  elementsOfList (quotientList L N) =
    {i : ℕ | i ≤ ((N.flatten.map (fun d => d.1)).dedup).length - 1}

/-! ## §B 变换塔派生：`triple_data_v4` / `core_triple_v4`

J1-B7（uvns 族）与 J3 本体（assumption_set3/K10、main_induction）的共同
载荷。`iota 0 k` ↦ `List.range k`。第三分量 `betwn (find_face L x) yᵢ zᵢ`
是 **dart 段**（非顶点段）；`core_triple_v4` 把前两支投影到顶点、第三支
折成长度（assumption_set3/K10 的消费形即 `(顶点, 顶点, 长度)` 三元表）。 -/

/-- HOL `triple_data_v4`（reduction3.hl:28-34）。 -/
noncomputable def tripleDataV4 (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : List (Dart × Dart × List Dart) :=
  let k := transformCount L N r x
  let fx := findFaceDarts L x
  (List.range k).map fun i =>
    (ytrans L N r x i, ztrans L N r x i,
      between fx (ytrans L N r x i) (ztrans L N r x i))

/-- HOL `core_triple_v4`（reduction3.hl:36-38）：
`MAP (\(u,v,ns). (FST u, FST v, sizel ns)) (triple_data_v4 L N r x)`。 -/
noncomputable def coreTripleV4 (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : List (ℕ × ℕ × ℕ) :=
  (tripleDataV4 L N r x).map fun (u, v, ns) => (u.1, v.1, ns.length)

/-- 「定义即引理」①：`core_triple_v4` 的长度 = `transform_count`
（reduction4.hl:846 `size_core_triple` 消费的形状；HOL 由
size_triple_data + MAP size 两条组合）。 -/
@[simp] theorem coreTripleV4_length (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) :
    (coreTripleV4 L N r x).length = transformCount L N r x := by
  simp [coreTripleV4, tripleDataV4, List.length_range]

/-! ## §C `dest_triple0` 步进机器（prebatch/batch0/dest_triple0/dest_triple_full）

消费口径（reduction3.hl assumption_set3:1828-1829 / reduction4.hl:1994-2002
实测）：`f = core L r`（**顶点**列表）、`uvns = core_triple_v4 L N r x`、
段表 `s : List (List (Option ℕ))`（每段以 `SOME u` 开、`SOME v` 收，
`ns = nseq n NONE` 为中段占位）。`dest_triple0_step` 的累加器是**段表**，
`dest_triple0`（tame_defs2）的累加器是**扁平表**——两形并存，逐字分落。 -/

/-- HOL `dest_triple0_step`（reduction3.hl:110-119）。段表步进：
`flatten s = []` 时开新段表，否则按 `u0 = u` / `next_el f u0 = u` /
一般三种情形 `rcons` 追加新段。 -/
def destTriple0Step (f : List ℕ) (s : List (List (Option ℕ))) (t : ℕ × ℕ × ℕ) :
    List (List (Option ℕ)) :=
  let (u, v, n) := t
  let ns := List.replicate n (none : Option ℕ)
  if s.flatten = [] then [[some u] ++ ns ++ [some v]]
  else
    let u0 := ((s.getLastD []).getLastD none).getD 0
    if u0 = u then s ++ [ns ++ [some v]]
    else if nextEl f u0 = u then s ++ [[some u] ++ ns ++ [some v]]
    else s ++ [(between f u0 u).map some ++ [some u] ++ ns ++ [some v]]

/-- HOL `dest_triple0_rcons`（reduction3.hl:155-164）：`dest_triple0_step`
的**单段展开形**（返回本步应追加的那一段，不裹 rcons）。
reduction4.hl:4953-4998（dest_triple0_rcons_paired 族）按此消费。 -/
def destTriple0Rcons (f : List ℕ) (s : List (List (Option ℕ))) (t : ℕ × ℕ × ℕ) :
    List (Option ℕ) :=
  let (u, v, n) := t
  let ns := List.replicate n (none : Option ℕ)
  if s.flatten = [] then [some u] ++ ns ++ [some v]
  else
    let u0 := ((s.getLastD []).getLastD none).getD 0
    if u0 = u then ns ++ [some v]
    else if nextEl f u0 = u then [some u] ++ ns ++ [some v]
    else (between f u0 u).map some ++ [some u] ++ ns ++ [some v]

/-- HOL `prebatch`（reduction3.hl:148-151）：`foldl (dest_triple0_step f0) []
(take i (core_triple_v4 L N r x))`。消费锚：reduction4.hl:1994
`prebatch (core L r) L N r x k`。 -/
noncomputable def prebatch (f0 : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i : ℕ) : List (List (Option ℕ)) :=
  List.foldl (destTriple0Step f0) [] ((coreTripleV4 L N r x).take i)

/-- HOL `batch0`（reduction3.hl:131-133）：`flatten (prebatch …)`（绝对
索引批；reduction4.hl prebatch_batch :4910 消费的形状）。 -/
noncomputable def batch0 (f0 : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i : ℕ) : List (Option ℕ) :=
  (prebatch f0 L N r x i).flatten

/-- 「定义即引理」②：零步 `prebatch` 是空段表（HOL 消费处
`take 0` = `[]` + `foldl` 空表 = `[]`，reduction4.hl:1994-1996 的
`SUC (PRE k)` 分裂即以它为基例）。 -/
theorem prebatchZero (f0 : List ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) : prebatch f0 L N r x 0 = [] := by
  simp [prebatch]

/-- HOL `dest_triple0`（tame_defs2.hl:599-613）：**扁平累加器**形
（`flatten [sofar;…]` 语义即扁平表拼接；与 destTriple0Step 的段表形
并存，消费锚 dest_triple_full）。 -/
def destTriple0 (f : List ℕ) (sofar : List (Option ℕ)) (uvns : List (ℕ × ℕ × ℕ)) :
    List (Option ℕ) :=
  match uvns with
  | [] => sofar
  | (u, v, n) :: uvns' =>
    let ns := List.replicate n (none : Option ℕ)
    if sofar = [] then destTriple0 f ([some u] ++ ns ++ [some v]) uvns'
    else
      let u0 := (sofar.getLastD none).getD 0
      if u0 = u then destTriple0 f (sofar ++ ns ++ [some v]) uvns'
      else if nextEl f u0 = u then
        destTriple0 f (sofar ++ [some u] ++ ns ++ [some v]) uvns'
      else
        destTriple0 f (sofar ++ (between f u0 u).map some ++ [some u] ++ ns
          ++ [some v]) uvns'

/-- 「定义即引理」③：`dest_triple0` 的 nil 方程（HOL 递归方程第一支，
tame_defs2.hl:600；reduction4.hl uvns 族逐支展开的边界件）。 -/
theorem destTriple0Nil (f : List ℕ) (sofar : List (Option ℕ)) :
    destTriple0 f sofar [] = sofar := rfl

/-- HOL `dest_triple_full`（tame_defs2.hl:615-624）：初段 + `dest_triple0`
+ 末段的拼接。消费锚：assumption_set3:1828
`dest_triple_full (core L r) v uvns = vs`、reduction4.hl:2061
`dest_triple_full (core L r) (SND x) (core_triple_v4 L N r x)`。 -/
def destTripleFull (f : List ℕ) (v0 : ℕ) (uvns : List (ℕ × ℕ × ℕ)) :
    List (Option ℕ) :=
  let uvn := uvns.headD (0, 0, 0)
  let (u, v, _) := uvn
  let initialSeg : List (Option ℕ) :=
    if v0 = u then [] else some v0 :: (between f v0 u).map some
  let uvn' := uvns.getLastD (0, 0, 0)
  let (u', v', _) := uvn'
  let u0 := prevEl f v0
  let finalSeg : List (Option ℕ) :=
    if v' = u0 then [] else (between f v' u0).map some ++ [some u0]
  initialSeg ++ destTriple0 f [] uvns ++ finalSeg

end Kepler.Text.Reduction3

-- 公理探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.coreTripleV4_length
#print axioms Kepler.Text.Reduction3.prebatchZero
#print axioms Kepler.Text.Reduction3.destTriple0Nil

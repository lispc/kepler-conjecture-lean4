/-
  Kepler.Text.Reduction3DefsLayer — J 战役 J3 定义层 D2（图层步进 6 件）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──────
  │ 本批 = reduction3.hl 定义层 NEW DEFS 段的**图层步进组**
  │ （reduction3.hl:79-144），全部只依赖 Kepler.Graphs（AFP 移植，
  │ 与 tame_defs.hl:357-433 / tame_defs2.hl:245-360 逐行对齐）：
  │   subdivFace0_beta     reduction3.hl:79-90   → §B subdivFace0Beta
  │   subdiv_single_step   reduction3.hl:92-101  → §B subdivSingleStep
  │   subdiv_triple_step   reduction3.hl:103-108 → §B subdivTripleStep
  │   nfgtrans'            reduction3.hl:123-126 → §C nfgtrans'
  │   b_nfgtrans0          reduction3.hl:138-144 → §C bNfgtrans0
  │   match_quotient_list  tame_defs2.hl:528-534 → §D matchQuotientList
  │ 桥（tame_defs.hl:433 `fgraph g = MAP FST (faces g)`）：
  │   §A fgraphOfGraph。
  │ 定义即引理（1 条）：nfgtrans'Zero（take 0 + foldl 空基例）。
  │ 前置：D1 `Kepler.Text.Reduction3Defs`（coreTripleV4/batch0 等，
  │ 落库 0785ce0e）。**触发器判词已在 D1 DELIVERY §1.1 结案**
  │ （GREEN：无商类型），本批为该判词的落地验证。
  └────────────────────────────────────────────────────────────────

  ┌─ 与树内 Graphs 层的接口（逐项勘对）──────────────────────────
  │ `splitFace` ↦ `Kepler.Graphs.splitFace`（FaceDivision.lean:40，
  │   AFP `split_face` 系，与 HOL tame_defs2.hl:332-350 同算法；
  │   `#!# h ram` 已按 getD 折算，见该文件头注）；
  │ `face` ↦ `Face { vertices, isFinal }`（Graph.lean:28）；
  │ `graph` ↦ `Graph { faces, countVertices, faceListAt, heights }`
  │   （Graph.lean:90，字段序逐一对齐）；
  │ `nextVertex` ↦ `Face.nextVertex`（Graph.lean:68）；
  │ `upt n0 (n0+n)` ↦ `List.range' n0 n`（截断减恒等，逐字折算）；
  │ `nseq`/`rcons`/`flatten` ↦ `List.replicate`/`++[·]`/`flatten`。
  │ **subdivFace0_beta ≠ subdivFace0**：前者返回余态 ((uo,n),f,g)，
  │   后者（tame_defs2.hl:352，树内 subdivFace' 已落）尾调
  │   makeFaceFinal——两件不可互相定义（D1 DELIVERY §6-2 预警）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3Defs`（D1 岛）+ 
  │ `Kepler.Graphs.FaceDivision`（splitFace）。闭包零 `Kepler.Assembly`
  │ 主模块、零 TameSpine（岛纪律同 Reduction5Base 头注）。
  │ 零 axiom/sorry/admit/native_decide。
  │ junk 约定：本批无 HD/LAST/THE 触点（splitFace 的 getD 折算在
  │ Graphs 层已档）；`Face.nextVertex` 的 `head!` 仅空面不可达支。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Defs
import Kepler.Graphs.FaceDivision

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts listPairs)
open Kepler.Graphs (Face Graph splitFace fgraph)
open Kepler.Text.Reduction5 (Dart quotientList finalList ytrans)

/-! ## §A 图层 → fgraph 桥

HOL `fgraph g = MAP FST (faces g)`（tame_defs.hl:433）。`faces g` 的
元素是 `num list # bool`，`FST` 投影为顶点表；`match_quotient_list`
的右端与 `quotient_list L N` 同型（`(num list) list`）。 -/

/-- HOL `fgraph`（tame_defs.hl:433）：`MAP FST (faces g)`。 -/
def fgraphOfGraph (g : Graph) : fgraph ℕ :=
  g.faces.map (fun f => f.vertices)

/-! ## §B 图层步进三件

`subdivFace0_beta` 是 `subdivFace0`（tame_defs2.hl:352）的**返回余态**
变体：`[]` 支停在 `((uo,n),f,g)` 而不 makeFaceFinal（reduction3 用它
做「批」的残局重放；消费锚 reduction3.hl:456/623/720 族）。
`subdiv_single_step`/`subdiv_triple_step` 是它的单步核（分别喂
`b_nfgtrans0` 的 `batch0` 扁平流与 `nfgtrans'` 的三元流）。 -/

/-- HOL `subdivFace0_beta`（reduction3.hl:79-90）。**余态形**：
返回 `((uo,n),(f,g))`（与 `subdivFace0` 的 makeFaceFinal 尾不同件）。 -/
def subdivFace0Beta (g : Graph) (f : Face) (uo : Option ℕ) (n : ℕ) :
    List (Option ℕ) → (Option ℕ × ℕ) × Face × Graph
  | [] => ((uo, n), f, g)
  | vo :: vos =>
    match uo with
    | none => subdivFace0Beta g f vo 0 vos
    | some u =>
      match vo with
      | none => subdivFace0Beta g f uo (n + 1) vos
      | some v =>
        if f.nextVertex u == v && n == 0 then subdivFace0Beta g f vo 0 vos
        else
          let ws := List.range' g.countVertices n
          let (_, f2, g') := splitFace g u v f ws
          subdivFace0Beta g' f2 vo 0 vos

/-- HOL `subdiv_single_step`（reduction3.hl:92-101）：`uo : Option ℕ`
状态的单步（`b_nfgtrans0` 的 foldl 步进）。 -/
def subdivSingleStep (s : (Option ℕ × ℕ) × Face × Graph) (vo : Option ℕ) :
    (Option ℕ × ℕ) × Face × Graph :=
  let ((uo, n), f, g) := s
  match uo with
  | none => ((vo, 0), f, g)
  | some u =>
    match vo with
    | none => ((uo, n + 1), f, g)
    | some v =>
      if f.nextVertex u == v && n == 0 then ((vo, 0), f, g)
      else
        let ws := List.range' g.countVertices n
        let (_, f2, g') := splitFace g u v f ws
        ((vo, 0), f2, g')

/-- HOL `subdiv_triple_step`（reduction3.hl:103-108）：`(n0,f,g)` 状态的
三元步进（`nfgtrans'` 的 foldl 步进；`n0` 为已累计顶点数）。 -/
def subdivTripleStep (t : ℕ × Face × Graph) (uvn : ℕ × ℕ × ℕ) : ℕ × Face × Graph :=
  let (n0, f, g) := t
  let (u, v, n) := uvn
  let ws := List.range' n0 n
  let (_, f2, g') := splitFace g u v f ws
  (n + n0, f2, g')

/-! ## §C foldl 层：`nfgtrans'` / `b_nfgtrans0`

`nfgtrans'` 在 D1 `coreTripleV4`（`(顶点,顶点,段长)` 三元表）上 foldl；
`b_nfgtrans0` 在 D1 `batch0`（顶点 option 扁平流）上 foldl。两件的
`f0`/`p` 参数形状与 reduction3.hl:3559 assumption_setK10 的消费
（`nfgtrans' (countVertices g,f,g) L N r x k`）逐字对齐。 -/

/-- HOL `nfgtrans'`（reduction3.hl:123-126）：
`foldl subdiv_triple_step p (take i (core_triple_v4 L N r x))`。 -/
noncomputable def nfgtrans' (p : ℕ × Face × Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (i : ℕ) : ℕ × Face × Graph :=
  List.foldl subdivTripleStep p ((coreTripleV4 L N r x).take i)

/-- 「定义即引理」：零步 `nfgtrans'` 是恒等（take 0 + foldl 空表；
reduction3.hl:4277 `nfgtrans0` 的 Lean 形）。 -/
theorem nfgtrans'Zero (p : ℕ × Face × Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) :
    nfgtrans' p L N r x 0 = p := by
  simp [nfgtrans']

/-- HOL `b_nfgtrans0`（reduction3.hl:138-144）：首状态 `fst_u0`（据
`FST (next_el fx x)` 与 `FST (ytrans … 0)` 是否相等决定 NONE/SOME
prev_el），在 `batch0 (FST f0) …` 上 foldl `subdiv_single_step`。 -/
noncomputable def bNfgtrans0 (f0 : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (i : ℕ) :
    (Option ℕ × ℕ) × Face × Graph :=
  let fx := findFaceDarts L x
  let fst_u0 : Option ℕ :=
    if (nextEl fx x).1 = (ytrans L N r x 0).1 then none
    else some (prevEl f0.vertices (ytrans L N r x 0).1)
  List.foldl subdivSingleStep ((fst_u0, 0), f0, g) (batch0 f0.vertices L N r x i)

/-! ## §D `match_quotient_list`

布尔合取：①图 `g` 的**终面**（isFinal）逐面展开的相邻顶点对表
（`list_pairs ∘ FST`，即该面作为平面多边形的 dart 表）必须全部落在
`N` 的终面（`final_list L`）之集中；②`fgraph g = quotient_list L N`。
（D1 DELIVERY §1.1 判词：纯列表级，无商类型。） -/
/-- HOL `match_quotient_list`（tame_defs2.hl:528-534）。 -/
def matchQuotientList (g : Graph) (L : fgraph ℕ) (N : List (List Dart)) : Prop :=
  (∀ d ∈ (g.faces.filter (fun f => f.isFinal)).map (fun f => listPairs f.vertices),
      d ∈ N.filter (fun r => decide (finalList L r))) ∧
  fgraphOfGraph g = quotientList L N

end Kepler.Text.Reduction3

-- 公理探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.nfgtrans'Zero
#check @Kepler.Text.Reduction3.nfgtrans'
#check @Kepler.Text.Reduction3.bNfgtrans0
#check @Kepler.Text.Reduction3.matchQuotientList

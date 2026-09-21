/-
  Kepler/Assembly — Phase 6 装配脊柱（P6-A 工作副本，编译验证在 /tmp/p6a/）。

  设计：`docs/phase6-spine.md`（2026-09-19 审定稿）。
  政策：`DECISIONS.md` 2026-09-17 条——sanctioned sorry 仅允许出现在显式接口占位。

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  - `text_formalization/general/the_kepler_conjecture.hl`：最终装配
    `import_tame_classification ∧ linear_programming_results ∧ the_nonlinear_inequalities
      ⟹ the_kepler_conjecture`（`kepler_conjecture_with_assumptions_and_archive`，:69-85）；
  - `text_formalization/general/the_main_statement.hl:170-175`：
    `kepler_conjecture_with_assumptions`（文字侧 capstone）。

  接口冻结 2026-09-19，2026-09-21 方向 A 深挖：`textCapstone` 已从 sorry
  占位展开为真证明（§2b TameSpine 骨架 + §2c 接口占位承接其债务）；
  `nonlinearInequalities` / `linearProgrammingResults` 两个占位定理仍在；
  第四占位 `goodListArchive` 已由 P6-C 闭合为真证明；
  `assembly` 本体是真证明（对照 HOL tactic 脚本逐行翻译）。
-/
import Kepler.Statement
import Kepler.Graphs
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto18
import Kepler.Text.PackingAuto21
import Kepler.Text.PackingAuto25
import Kepler.Text.Hypermap
import Kepler.Text.LocalAuto16
import Kepler.Assembly.GoodListDefs
import Kepler.Assembly.GoodListAll

open Classical Metric Set
open Kepler.Geom Kepler.Text Kepler.Text.Fan Kepler.Graphs

namespace Kepler.Assembly

/-! ## 1. 缺失谓词的最小镜像 def（各带 HOL 出处） -/

/-- HOL `ESTD`（`tame/tame_defs.hl:191-192`）：
`ESTD V = {{v,w} | v IN V /\ w IN V /\ ~(v = w) /\ dist(v,w) <= (&2)*h0}`。 -/
def ESTD (V : Set V3) : Set (Set V3) :=
  {e | ∃ v w : V3, e = {v, w} ∧ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w ≤ 2 * h0}

/-- HOL `ECTC`（`tame/tame_defs.hl:194-195`）：
`ECTC V = {{v,w} | v IN V /\ w IN V /\ ~(v = w) /\ dist(v,w) = &2}`。 -/
def ECTC (V : Set V3) : Set (Set V3) :=
  {e | ∃ v w : V3, e = {v, w} ∧ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w = 2}

/-- HOL `scriptL`（`tame/tame_defs.hl:245-246`）：
`scriptL V = sum V (λv. lmfun (norm v / &2))`。
折算说明：HOL `sum` 对无限集按约定取 0（`sum` 的支撑约定）；
此处以 `V.Finite` 分支镜像该约定。`lmfun` 复用 `Kepler.Text.lmfun`
（PackingAuto2.lean:464）。 -/
noncomputable def scriptL (V : Set V3) : ℝ :=
  if h : V.Finite then Finset.sum h.toFinset (fun v => lmfun (‖v‖ / 2)) else 0

/-- HOL `contravening`（`tame/tame_defs.hl:248-253`），逐句镜像：
`contravening V <=> packing V /\ V SUBSET ball_annulus /\ scriptL V > &12 /\
  (!W. packing W /\ W SUBSET ball_annulus ==> scriptL W <= scriptL V) /\
  (CARD V = 13 \/ CARD V = 14 \/ CARD V = 15) /\
  (!v. v IN V ==> surrounded_node (V, ESTD V) v) /\
  (!v. v IN V ==> (surrounded_node (V, ECTC V) v \/ (norm v = &2)))`。
折算说明：`packing` ↦ `Kepler.Packing`（Statement.lean:35，sphere.hl:425 的镜像）；
`ball_annulus` ↦ `Kepler.Text.ballAnnulus`（PackingAuto2.lean:533）；
`CARD` ↦ `Set.ncard`（无限集为 0，与 HOL `CARD` 约定一致）；
`surrounded_node` ↦ `Kepler.Text.Fan.surroundedNode`（Fan.lean:214-216）。 -/
def Contravening (V : Set V3) : Prop :=
  Packing V ∧ V ⊆ ballAnnulus ∧ scriptL V > 12 ∧
    (∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL V) ∧
    (V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15) ∧
    (∀ v ∈ V, surroundedNode V (ESTD V) v) ∧
    (∀ v ∈ V, surroundedNode V (ECTC V) v ∨ ‖v‖ = 2)

/-! ### 1a. list_hypermap 机器（`formal_lp/hypermap/ssreflect/list_hypermap-compiled.hl`）

`listPairs` / `listOfDarts` / `nextEl` / `prevEl` / `findFaceDarts` /
`eList` / `fList` / `nList` / `GoodList` / `AllGoodList` 已下沉至
`Kepler/Assembly/GoodListDefs.lean`（P6-C：使 archive 逐图 `native_decide`
分片不必 import 本脊柱、公理审计不被接口 sorry 污染），经 import 可见，
对外签名不变。 -/

/-! ### 1b. hypermap 同构与 `hypermap_of_list` 的规格级镜像 -/

/-- HOL `iso`（`hypermap/hypermap.hl:9614`）逐句镜像：
`H iso H' <=> ?f. BIJ f (dart H) (dart H') /\ (!x. x IN dart H ==>
  edge_map H' (f x) = f (edge_map H x) /\ node_map H' (f x) = f (node_map H x) /\
  face_map H' (f x) = f (face_map H x))`。
折算：`BIJ f s t` ↦ `Set.BijOn f s t`；dart 集为 `Finset`（有限性内置）。 -/
def HypermapIso {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Hypermap α) (H' : Hypermap β) : Prop :=
  ∃ f : α → β, Set.BijOn f (↑H.darts) (↑H'.darts) ∧
    ∀ x ∈ H.darts,
      H'.edgeMap (f x) = f (H.edgeMap x) ∧
      H'.nodeMap (f x) = f (H.nodeMap x) ∧
      H'.faceMap (f x) = f (H.faceMap x)

/-- HOL `hypermap_of_list`（list_hypermap-compiled.hl:60）的**规格级**镜像：
`H` 是列表 `L` 的超映射，当且仅当 dart 集恰为 `list_of_darts L` 且三个映射在
dart 上与 `e_list`/`n_list`/`f_list` 一致（HOL 侧 `res` 使映射在 dart 集外为恒等；
Lean `Hypermap` 的 `PermutesOn` 字段已内置此约定，故无需额外合取项）。

**差距说明（P6-C 桥未落地）**：Lean 侧尚无 `hypermapOfList` 的**构造**——
`Hypermap` 结构打包了 `edgeMap * nodeMap * faceMap = 1` 等证明字段，
构造需先证 `good_list` 层面的 dart 引理，超出脊柱预算（> 50 行）。
本谓词只钉死语义；P6-C 落地构造后须证明 `IsHypermapOfList L (hypermapOfList L)`，
届时 `FanHypermapIsoList` 可展开回 HOL 原句 `iso (hypermap_of_fan …) (hypermap_of_list L)`。 -/
structure IsHypermapOfList (L : fgraph ℕ) (H : Hypermap (ℕ × ℕ)) : Prop where
  /-- `dart (hypermap_of_list L) = darts_of_list L`（list_hypermap-compiled.hl:22,60）。 -/
  darts_eq : (↑H.darts : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L}
  /-- `edge_map` 在 dart 上 = `e_list`（:54,57,60）。 -/
  edgeMap_eq : ∀ d ∈ H.darts, H.edgeMap d = eList d
  /-- `node_map` 在 dart 上 = `n_list`（:55,58,60）。 -/
  nodeMap_eq : ∀ d ∈ H.darts, H.nodeMap d = nList L d
  /-- `face_map` 在 dart 上 = `f_list`（:53,56,60）。 -/
  faceMap_eq : ∀ d ∈ H.darts, H.faceMap d = fList L d

/-- HOL `iso (hypermap_of_fan (V,ESTD V)) (hypermap_of_list L)`
（the_kepler_conjecture.hl:25）的最弱保真形态：存在由 `L` 决定的超映射
（`IsHypermapOfList` 钉死语义）与 fan 超映射同构。
折算说明：HOL 的 `hypermap_of_fan` 以 `vec 0` 为原点、为全函数；
Lean `hypermapOfFan`（Fan.lean:1169）proof-parameterized，原点 `0` 显式给出，
`FAN 0 V (ESTD V)` 前提由 `LinearProgrammingResultsOn` 统一携带。
另注：Lean `hypermapOfFan` 的 dart 集为 `dart1_of_fan`（不含孤立 dart `(v,v)`）；
在 `Contravening V` 语境下每个节点被包围（无孤立点），两编码一致——
消除接口 sorry 时此折算需随 `Contravening → FAN` 一并补证。 -/
def FanHypermapIsoList (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ) : Prop :=
  ∃ H : Hypermap (ℕ × ℕ), IsHypermapOfList L H ∧
    HypermapIso (hypermapOfFan 0 V (ESTD V) hfan) H

/-! ### 1c. archive 数据与 tame_classification 形态 -/

/- HOL `tame_archive_lists`（`archive = set_of_list tame_archive_lists`，
the_kepler_conjecture.hl:40）的 Lean 侧数据形态 `tameArchiveLists`
已随 §1a 下沉至 `Kepler/Assembly/GoodListDefs.lean`（Phase 2 archive 的底层
清单，`Archive` 的数据部分，RelativeCompleteness.lean:110），经 import 可见。 -/

/-- HOL `tame_classification`（the_main_statement.hl:61-64）逐句镜像：
`!a. tame_classification a =
  (!g. PlaneGraphs g /\ tame g ==> (?y. y IN set_of_list a /\ iso_fgraph (fgraph g) y))`。
折算：`(?y. y IN set_of_list a /\ iso_fgraph x y)` = Phase 2 的
`inIso x {y | y ∈ a}`（PlaneGraphIso.lean:312 `inQle` 展开即此二合取）；
Lean 的 `iso_fgraph` 移植自 AFP `PlaneGraphIso.thy`，允许镜像
（improper iso，`is_Iso` 的 reverse 析取），与 HOL `iso_fgraph` 语义一致
（保真审 P6-B 复核点）。 -/
def TameClassification (a : List (fgraph ℕ)) : Prop :=
  ∀ g : Graph, PlaneGraphs g → tame g → inIso g.fgraph {y | y ∈ a}

/-! ## 2. 三个接口 Prop -/

/-! ### 2a. `the_nonlinear_inequalities`：993 条合取的折算形态（清单为数据 + 量化命题）

HOL `the_nonlinear_inequalities`（the_main_statement.hl:55-59）是六件**生成式**合取：
`pack_nonlinear_non_ox3q1h /\ ox3q1h /\ main_nonlinear_terminal_v11 /\ lp_ineqs /\
  pack_ineq_def_a /\ kcblrqc_ineq_def`，
各分量均为非线性证书数据库（`Ineq`）按标签过滤出的字面不等式合取——
993 条主体在 `main_nonlinear_terminal_v11`（`scripts/local/terminal.hl:24-44`，
由 `Main_estimate` 标签构造）；`lp_ineqs` 的构造见 the_main_statement.hl:29-45
（`Lp`/`Tablelp`/`Lp_aux` 标签 + `"6170936724"`，剔除 `deprecated_quads`）。

已批准折算（docs/phase6-spine.md §3 决策点）：每分量 = ID 清单（数据）+ 量化命题；
折算合理性须登记 `docs/statement-fidelity.md`（P6-B）。
**占位差距**：六个 ID 清单暂为空、`CertifiedIneqHolds` 语义暂为 `True` 占位——
二者均由 Phase 4（G4 内核证书 + 155 定义闭包粘合，P6-E）填实；
清单填入前本接口的量化部分无内容。仓库中无现成注册表形态
（`get_main_nonlinear` 仅见于 HOL 脚本与 LocalAuto16/19 的 NEEDS 注释），故按批准新造。 -/

/-- 单条证书不等式成立的语义。**PLACEHOLDER(G4)**：填实时按 `id` 查表展开为
对应的字面量化不等式（`!y1..y6. box ==> ineq` 形），并由 G4 内核证书定理闭合。 -/
def CertifiedIneqHolds (_id : String) : Prop := True

/-- 注册表量化：清单中每条 ID 对应的不等式成立。 -/
def AllCertified (ids : List String) : Prop := ∀ id ∈ ids, CertifiedIneqHolds id

/-- PLACEHOLDER(G4)：HOL `lp_ineqs` 分量的 ID 清单（the_main_statement.hl:29-45）。 -/
def idsLpIneqs : List String := []

/-- HOL `lp_ineqs`（the_main_statement.hl:29-45）的注册表折算形态。
在 HOL 中它同时是 `the_nonlinear_inequalities` 的第四合取项和
`linear_programming_results` 的前提——此处同样被两处共享。 -/
def LpIneqs : Prop := AllCertified idsLpIneqs

/-- PLACEHOLDER(P6-E)：HOL `pack_ineq_def_a` 分量（PA22 `packIneqDefAP22` 同形
占位；G4 证书数据库过滤形态落地后真化）。 -/
def PackIneqDefA : Prop := True

/-- PLACEHOLDER(P6-E)：HOL `kcblrqc_ineq_def` 分量（无既有 Lean 对应物；
新造占位，语义由 G4/P6-E 填实）。 -/
def KcblrqcIneqDef : Prop := True

/-- **接口 1**：HOL `the_nonlinear_inequalities`（the_main_statement.hl:55-59）
的六件合取。前三分量已用 Lean 侧真 Prop 真化（2026-09-21 骨架化精化，取代
原 ID 清单占位）：`pack_nonlinear_non_ox3q1h`（PA21:147）、`ox3q1hP25`（PA25:87）、
`main_nonlinear_terminal_v11`（LocalAuto1:793，Phase 4/G4 的主叶子）；
后三分量 `LpIneqs` 为注册表折算，`PackIneqDefA`/`KcblrqcIneqDef` 为标明的
占位。 -/
def TheNonlinearInequalities : Prop :=
  pack_nonlinear_non_ox3q1h ∧ ox3q1hP25 ∧ main_nonlinear_terminal_v11 ∧ LpIneqs ∧
    PackIneqDefA ∧ KcblrqcIneqDef

/-- **接口 2**：HOL `linear_programming_results`（the_kepler_conjecture.hl:21-26）
逐句镜像，archive 清单参数化（HOL 内嵌 `tame_archive_lists`；参数化是为了与
`good_linear_programming_results`（the_main_statement.hl:47-53）共享同一形状）：
`!V. lp_ineqs /\ lp_main_estimate /\
   (?L. MEM L tame_archive_lists /\ iso (hypermap_of_fan (V,ESTD V)) (hypermap_of_list L))
   ==> ~(contravening V)`。
折算说明：`FAN 0 V (ESTD V)` 提为显式前提（Lean `hypermapOfFan` proof-parameterized，
见 `FanHypermapIsoList` 注释）；`lp_main_estimate` 复用 `Kepler.Text.lp_main_estimate`
（LocalAuto16.lean:185，JEJTVGB.hl:232 的镜像）。 -/
def LinearProgrammingResultsOn (a : List (fgraph ℕ)) : Prop :=
  ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)),
    LpIneqs ∧ lp_main_estimate ∧ (∃ L, L ∈ a ∧ FanHypermapIsoList V hfan L) →
      ¬Contravening V

/-- HOL `linear_programming_results` 本体（archive = `tame_archive_lists` 实例化）。 -/
def LinearProgrammingResults : Prop := LinearProgrammingResultsOn tameArchiveLists

/-- HOL `good_linear_programming_results`（the_main_statement.hl:47-53）逐句镜像：
`good_linear_programming_results a <=> (ALL good_list a) /\
  (!V. lp_ineqs /\ lp_main_estimate /\ (?L. MEM L a /\ iso …) ==> ~(contravening V))`。 -/
def GoodLinearProgrammingResults (a : List (fgraph ℕ)) : Prop :=
  AllGoodList a ∧ LinearProgrammingResultsOn a

/-- HOL `the_kepler_conjecture`（the_main_statement.hl:19-24）的命题形态；
与 `Kepler.Statement.the_kepler_conjecture`（Statement.lean:111-115）的 type 逐句相同
（本脊柱独立重述，不消费 Statement.lean 的 Phase-1 sorry 定理）。 -/
def TheKeplerConjecture : Prop :=
  ∀ V : Set Space3, Packing V →
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
        Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2

/-- **接口 3**：HOL `kepler_conjecture_with_assumptions`
（the_main_statement.hl:170-175）的陈述形态——注意它本身是三前提蕴含式：
`!a. tame_classification a /\ good_linear_programming_results a /\
      the_nonlinear_inequalities ==> the_kepler_conjecture`。
（HOL 侧 80 行 tactic 脚本消费的引理链：Oxlzlez.PACKING_CHAPTER_MAIN_CONCLUSION、
Fnjlbxs.local_annulus_inequality_scriptL/FCDJDOT、Jejtvgb.nonlinear_imp_lp_main_estimate、
MQMSMAB、tame_planar_hypermap_restricted、Jcajydu.JCAJYDU、Wmlnymd.tame_correspondence_iso、
Reduction5.restricted_hypermaps_are_planegraphs_thm、Asfutbf.hypermap_of_fan_neg/
contravening_negative——Phase 5 的 PackingConcl/LocalConcl 流水线逐条闭合。） -/
def TextCapstone : Prop :=
  ∀ a : List (fgraph ℕ),
    TameClassification a ∧ GoodLinearProgrammingResults a ∧ TheNonlinearInequalities →
      TheKeplerConjecture

/-! ## 2b. TameSpine —— tame 文字章 capstone 骨架（方向 A，2026-09-21）

缺口盘点：capstone 脚本（the_main_statement.hl:170-251）消费的 12 件中 8 件属
`text_formalization/tame/` 文字章（64 个 .hl，4.6MB，未移植）。骨架策略：
原语 def 逐条忠实镜像（标 HOL 出处），capstone 级引理以 sorry 占位——主定理
可达债务图由此展开至章节出口。`PLACEHOLDER(tame章)` 标记的 def 为形状占位，
P6-B 保真审补录。 -/

section TameSpine

variable {α : Type*} [DecidableEq α]

/-- 幂轨道集（hypermap.hl:57,63,69 的 `edge/node/face H x`）。 -/
def orbitSet (p : Equiv.Perm α) (x : α) : Set α :=
  Set.range fun n : ℕ => (p ^ n) x

def edgeOrbit (H : Hypermap α) (x : α) : Set α := orbitSet H.edgeMap x
def nodeOrbit (H : Hypermap α) (x : α) : Set α := orbitSet H.nodeMap x
def faceOrbit (H : Hypermap α) (x : α) : Set α := orbitSet H.faceMap x

/-- `number_of_edges`（hypermap.hl）。 -/
noncomputable def numberOfEdges (H : Hypermap α) : ℕ := H.edgeSet.ncard

/-- `plain_hypermap`（hypermap.hl；tame_defs.hl:136 tame_1 前半）。 -/
def PlainHypermap (H : Hypermap α) : Prop := H.edgeMap * H.edgeMap = 1

/-- `planar_hypermap`（hypermap.hl；tame_1 后半）。 -/
def PlanarHypermap (H : Hypermap α) : Prop :=
  H.numberOfNodes + numberOfEdges H + H.numberOfFaces =
    H.darts.card + 2 * H.numberOfComponents

/-- `connected_hypermap`。 -/
def ConnectedHypermap (H : Hypermap α) : Prop := H.numberOfComponents = 1

/-- `simple_hypermap`。 -/
def SimpleHypermap (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, nodeOrbit H x ∩ faceOrbit H x = {x}

/-- `is_edge_nondegenerate`（tame_defs.hl:147 tame_3）。 -/
def IsEdgeNondegenerate (H : Hypermap α) : Prop := ∀ x ∈ H.darts, H.edgeMap x ≠ x

/-- `no_loops`（tame_4）。 -/
def NoLoops (H : Hypermap α) : Prop :=
  ∀ x y, x ∈ edgeOrbit H y → x ∈ nodeOrbit H y → x = y

/-- `is_no_double_joins`（tame_5a）。 -/
def IsNoDoubleJoins (H : Hypermap α) : Prop :=
  ∀ x y, x ∈ H.darts → y ∈ nodeOrbit H x → H.edgeMap y ∈ nodeOrbit H (H.edgeMap x) →
    x = y

/-- `exceptional_face`。 -/
def ExceptionalFace (H : Hypermap α) (x : α) : Prop := 5 ≤ (faceOrbit H x).ncard

/-- `set_of_triangles_meeting_node`。 -/
def setOfTrianglesMeetingNode (H : Hypermap α) (x : α) : Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = faceOrbit H y ∧ (faceOrbit H y).ncard = 3 ∧ y ∈ nodeOrbit H x}

/-- `set_of_quadrilaterals_meeting_node`。 -/
def setOfQuadrilateralsMeetingNode (H : Hypermap α) (x : α) : Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = faceOrbit H y ∧ (faceOrbit H y).ncard = 4 ∧ y ∈ nodeOrbit H x}

/-- `set_of_exceptional_meeting_node`。 -/
def setOfExceptionalMeetingNode (H : Hypermap α) (x : α) : Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = faceOrbit H y ∧ 5 ≤ (faceOrbit H y).ncard ∧ y ∈ nodeOrbit H x}

/-- `set_of_face_meeting_node`。 -/
def setOfFaceMeetingNode (H : Hypermap α) (x : α) : Set (Set α) :=
  {F | ∃ y ∈ H.darts, F = faceOrbit H y ∧ y ∈ nodeOrbit H x}

/-- `type_of_node`。 -/
noncomputable def typeOfNode (H : Hypermap α) (x : α) : ℕ × ℕ × ℕ :=
  ((setOfTrianglesMeetingNode H x).ncard,
    (setOfQuadrilateralsMeetingNode H x).ncard,
    (setOfExceptionalMeetingNode H x).ncard)

/-- `node_type_exceptional_face`。 -/
def NodeTypeExceptionalFace (H : Hypermap α) (x : α) : Prop :=
  ExceptionalFace H x ∧ (nodeOrbit H x).ncard = 6 → typeOfNode H x = (5, 0, 1)

/-- `node_exceptional_face`。 -/
def NodeExceptionalFace (H : Hypermap α) (x : α) : Prop :=
  ExceptionalFace H x → (nodeOrbit H x).ncard ≤ 6

/-- `tgt`（tame_defs 表格常数）。 -/
noncomputable def tgt : ℝ := 1.541

/-- `d_tame`。 -/
noncomputable def dTame : ℕ → ℝ := fun n =>
  if n = 3 then 0 else if n = 4 then 0.206 else if n = 5 then 0.4819 else
    if n = 6 then 0.712 else tgt

/-- `b_tame`。 -/
noncomputable def bTame : ℕ → ℕ → ℝ := fun p q =>
  if p = 0 ∧ q = 3 then 0.618 else if p = 0 ∧ q = 4 then 0.97 else
    if p = 1 ∧ q = 2 then 0.656 else if p = 1 ∧ q = 3 then 0.618 else
      if p = 2 ∧ q = 1 then 0.797 else if p = 2 ∧ q = 2 then 0.412 else
        if p = 2 ∧ q = 3 then 1.2851 else if p = 3 ∧ q = 1 then 0.311 else
          if p = 3 ∧ q = 2 then 0.817 else if p = 4 ∧ q = 0 then 0.347 else
            if p = 4 ∧ q = 1 then 0.366 else if p = 5 ∧ q = 0 then 0.04 else
              if p = 5 ∧ q = 1 then 1.136 else if p = 6 ∧ q = 0 then 0.686 else
                if p = 7 ∧ q = 0 then 1.450 else tgt

/-- 有限集和（支撑约定同 §1 `scriptL`）。 -/
noncomputable def setSumSpec (s : Set (Set α)) (w : Set α → ℝ) : ℝ :=
  if h : s.Finite then h.toFinset.sum w else 0

/-- `total_weight`。 -/
noncomputable def totalWeight (H : Hypermap α) (w : Set α → ℝ) : ℝ :=
  setSumSpec H.faceSet w

/-- `adm_1`。 -/
def Adm1 (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, dTame (faceOrbit H x).ncard ≤ w (faceOrbit H x)

/-- `adm_2`。 -/
def Adm2 (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, (setOfExceptionalMeetingNode H x).ncard = 0 →
    bTame (setOfTrianglesMeetingNode H x).ncard
        (setOfQuadrilateralsMeetingNode H x).ncard ≤
      setSumSpec (setOfFaceMeetingNode H x) w

/-- `adm_3`。PLACEHOLDER(tame章)：结论子句待抄录（adm_3 尾部）。 -/
def Adm3 (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) → True

/-- `admissible_weight`。 -/
def AdmissibleWeight (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  Adm1 H w ∧ Adm2 H w ∧ Adm3 H w

/-- tame_1（tame_defs.hl:136）。 -/
def Tame1 (H : Hypermap α) : Prop := PlainHypermap H ∧ PlanarHypermap H
/-- tame_2。 -/
def Tame2 (H : Hypermap α) : Prop := ConnectedHypermap H ∧ SimpleHypermap H
/-- tame_3。 -/
def Tame3 (H : Hypermap α) : Prop := IsEdgeNondegenerate H
/-- tame_4。 -/
def Tame4 (H : Hypermap α) : Prop := NoLoops H
/-- tame_5a。 -/
def Tame5a (H : Hypermap α) : Prop := IsNoDoubleJoins H
/-- tame_8。 -/
def Tame8 (H : Hypermap α) : Prop := 3 ≤ H.numberOfFaces
/-- tame_9a。 -/
def Tame9a (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, 3 ≤ (faceOrbit H x).ncard ∧ (faceOrbit H x).ncard ≤ 6
/-- tame_10。 -/
def Tame10 (H : Hypermap α) : Prop :=
  H.numberOfNodes = 13 ∨ H.numberOfNodes = 14 ∨ H.numberOfNodes = 15
/-- tame_11a。 -/
def Tame11a (H : Hypermap α) : Prop := ∀ x ∈ H.darts, 3 ≤ (nodeOrbit H x).ncard
/-- tame_11b。 -/
def Tame11b (H : Hypermap α) : Prop := ∀ x ∈ H.darts, (nodeOrbit H x).ncard ≤ 7
/-- tame_12o。 -/
def Tame12o (H : Hypermap α) : Prop :=
  ∀ x ∈ H.darts, NodeTypeExceptionalFace H x ∧ NodeExceptionalFace H x
/-- tame_13a。 -/
def Tame13a (H : Hypermap α) : Prop :=
  ∃ w, AdmissibleWeight H w ∧ totalWeight H w < tgt

/-- HOL `tame_planar_hypermap`（tame_defs.hl:180）。 -/
def TamePlanarHypermap (H : Hypermap α) : Prop :=
  Tame1 H ∧ Tame2 H ∧ Tame3 H ∧ Tame4 H ∧ Tame5a H ∧ Tame8 H ∧ Tame9a H ∧
    Tame10 H ∧ Tame11a H ∧ Tame11b H ∧ Tame12o H ∧ Tame13a H

/-- HOL `opposite_hypermap`（tame_defs.hl:185）。镜像绕行用；四个 proof 字段为
置换代数（骨架期 sorry，填证波秒证）。 -/
def oppositeHypermap (H : Hypermap α) : Hypermap α where
  darts := H.darts
  edgeMap := H.faceMap * H.nodeMap
  nodeMap := H.nodeMap.symm
  faceMap := H.faceMap.symm
  edgeMap_permutes := sorry -- 置换代数
  nodeMap_permutes := sorry
  faceMap_permutes := sorry
  comp_eq_one := sorry

/-- PLACEHOLDER(tame章)（tame_defs2.hl `finalGraph`）。 -/
def FinalGraph (_ : Graph) : Prop := True
/-- PLACEHOLDER(tame章)（`all uniq`）。 -/
def AllUniq (_ : Graph) : Prop := True
/-- PLACEHOLDER(tame章)（`good_faces_v3`）。 -/
def GoodFacesV3 (_ : Graph) : Prop := True
/-- PLACEHOLDER(tame章)（`vertices_set2 g = elements_of_list (fgraph g)`）。 -/
def VerticesSet2Eq (_ : Graph) : Prop := True

/-- HOL `good_list_nodes`（tame_defs'）。本体依赖 `hypermapOfList` 构造
（P6-C 未落地），骨架期为形状占位。 -/
def GoodListNodes (_ : fgraph ℕ) : Prop := True

/-- HOL `good_graph_v4`（tame_defs2.hl）。后四合取项为骨架占位（见上）。 -/
def GoodGraphV4 (g : Graph) : Prop :=
  GoodList g.fgraph ∧ GoodListNodes g.fgraph ∧ FinalGraph g ∧ AllUniq g ∧
    GoodFacesV3 g ∧ VerticesSet2Eq g

end TameSpine

/-! ### 2c. TameSpine 接口占位（capstone 消费链；全部骨架 sorry） -/

/-- 接口占位：`contravening_lp_fan` 群（tame 章）——contravening 给出 fan 结构。 -/
theorem contraveningFan (V : Set V3) (hc : Contravening V) : FAN 0 V (ESTD V) := by
  sorry

/-- 接口占位：HOL `Mqmsmab.MQMSMAB`（tame_concl / MQMSMAB-compiled.hl；section
前提 `kcblrqc_ineq_def` ∧ `lp_main_estimate` 显式化）。 -/
theorem mqmsmab (V : Set V3) (hkcblrqc : KcblrqcIneqDef) (hmain : lp_main_estimate)
    (hfan : FAN 0 V (ESTD V)) (hc : Contravening V) :
    TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfan) := by
  sorry

/-- 接口占位：HOL `tame_planar_hypermap_restricted`（the_main_statement.hl:143）。 -/
theorem tamePlanarHypermapRestricted {α : Type*} [DecidableEq α] (H : Hypermap α)
    (ht : TamePlanarHypermap H) : H.IsRestricted := by
  sorry

/-- 接口占位：HOL `Jcajydu.JCAJYDU` 一般形（premise 版由 Reduction5 供应 list
版的前提折入——填证时按 HOL 原形拆回，phase6-spine.md §5）。 -/
theorem jcajydu {α : Type*} [DecidableEq α] (H : Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Graph, PlaneGraphs g ∧ GoodGraphV4 g ∧
      ∃ H' : Hypermap (ℕ × ℕ), IsHypermapOfList g.fgraph H' ∧ HypermapIso H H' := by
  sorry

/-- 接口占位：HOL `Wmlnymd.tame_correspondence_iso`（WMLNYMD.hl）。 -/
theorem tameCorrespondenceIso {α : Type*} [DecidableEq α] (g : Graph) (H : Hypermap α)
    (H' : Hypermap (ℕ × ℕ)) (hgg : GoodGraphV4 g) (ht : TamePlanarHypermap H)
    (hiso : HypermapIso H H') (hIs : IsHypermapOfList g.fgraph H') : tame g := by
  sorry

/-- 接口占位：HOL `Elllnyz.ELLLNYZ`（ELLLNYZ.hl）——镜像析取形，脊柱的图桥
必须保持此形（phase6-spine.md §5）。`hypermap_of_list y` 侧为存在性产出。 -/
theorem elllnyz (x y : fgraph ℕ) (hx : GoodList x) (hy : GoodList y)
    (hiso : iso_fgraph x y) (Hx : Hypermap (ℕ × ℕ)) (hHx : IsHypermapOfList x Hx) :
    ∃ Hy : Hypermap (ℕ × ℕ), IsHypermapOfList y Hy ∧
      (HypermapIso Hx Hy ∨ HypermapIso (oppositeHypermap Hx) Hy) := by
  sorry

/-- 接口占位：HOL `Asfutbf.hypermap_of_fan_neg`（ASFUTBF.hl）。 -/
theorem hypermapOfFanNeg (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hfan' : FAN 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V))) :
    HypermapIso
      (hypermapOfFan 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V)) hfan')
      (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfan)) := by
  sorry

/-- 接口占位：HOL `Asfutbf.iso_opposite_eq`（ASFUTBF.hl）。 -/
theorem isoOppositeEq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Hypermap α) (H' : Hypermap β) :
    HypermapIso H H' ↔ HypermapIso (oppositeHypermap H) (oppositeHypermap H') := by
  sorry

/-- 接口占位：HOL `Asfutbf.contravening_negative`（ASFUTBF.hl；
`contravening_negative_concl`）。 -/
theorem contraveningNegative (V : Set V3) (hc : Contravening V) :
    Contravening ((fun v => -v) '' V) := by
  sorry

/-- 接口占位：HOL `Fnjlbxs.local_annulus_inequality_scriptL`（FNJLBXS-compiled.hl）。 -/
theorem localAnnulusInequalityScriptL (V : Set V3) :
    localAnnulusInequality V ↔ scriptL V ≤ 12 := by
  sorry

/-- 接口占位：HOL `Fnjlbxs.FCDJDOT`（FNJLBXS-compiled.hl；前提
`pack_ineq_def_a` 显式化）。 -/
theorem fcdjdot (hpa : PackIneqDefA)
    (h : ∃ W : Set V3, Packing W ∧ W ⊆ ballAnnulus ∧ scriptL W > 12) :
    ∃ V : Set V3, Contravening V := by
  sorry

/-- 接口占位：HOL `kc_imp_the_kc`（the_main_statement.hl:82）——
Pack_defs `kepler_conjecture`（体积形）⟹ 密度计数形。 -/
theorem kcImpTheKc (hkc : keplerConjecture) : TheKeplerConjecture := by
  sorry

/-- 骨架辅助：`Hypermap.Iso` 传递性（置换复合；填证波由 `Hypermap.Iso.trans`
转换或直证）。 -/
theorem hypermapIsoTrans {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] {H : Hypermap α} {G : Hypermap β} {K : Hypermap γ}
    (h1 : HypermapIso H G) (h2 : HypermapIso G K) : HypermapIso H K := by
  sorry

/-! ### 2d. LP 接口结构化（方向 D，2026-09-21）

HOL 蓝图（tame/linear_programming_results.hl）：`linear_programming_results` 的
证明 = 计算层（`Verify_all.verify_all` 逐图 LP，15+ 小时）产出逐图
`tame_linear_result` 实例 + 纯逻辑桥 `tame_result_lemma`（MESON 一步）。
Lean 镜像同构：唯一新接口 = 逐图证书总库（Phase 3 持久化填实，现 24k/43058；
桥章 formal_lp/hypermap 的 KCBLRQC/BDJYFFB/CRTTXAT 群为填实依赖）；
`linear_programming_results` 本体降级为纯逻辑真推导。 -/

/-- 接口占位：逐图 LP 证书总库（HOL `Verify_all` 的 Lean 形——每张 archive 图
的 `tame_linear_result` 实例；前提 `LpIneqs`/`lp_main_estimate` 对应 HOL 证书
定理的 DISCH 假设）。 -/
theorem lpArchiveCertificates (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
    ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V := by
  sorry

/-- HOL `tame_result_lemma` + `linear_programming_results_th` 最终装配
（纯逻辑部分真证明；债务集中于 `lpArchiveCertificates`）。 -/
theorem linearProgrammingResultsOf (hnl : TheNonlinearInequalities)
    (hcert : ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V) :
    LinearProgrammingResults :=
  fun V hfan ⟨_, _, ⟨L, hLa, hiso⟩⟩ => hcert V hfan L hLa hiso

/-! ## 3. 接口 sorry 占位（原三接口冻结 2026-09-19；§2b/2c 的骨架占位为
2026-09-21 方向 A 深挖新增，均计入主定理可达债务图） -/

/-- 接口占位（冻结 2026-09-19）。债务归属：Phase 4 / G4 粘合（P6-E）。
消除顺序：先填六个 ID 清单与 `CertifiedIneqHolds` 语义，再逐条闭合证书。 -/
theorem nonlinearInequalities : TheNonlinearInequalities := by
  sorry

/-- 接口 2 → 真推导（2026-09-21 方向 D）：`linear_programming_results` 从
非线性接口的 `LpIneqs` 分量与 `main_nonlinear_terminal_v11`→`lp_main_estimate`
链 + 逐图证书库真推导；剩余债务集中于 `lpArchiveCertificates` 单枚接口
（Phase 3 计算层）。原 P6-D 桥与 P6-C `hypermapOfList` 构造依赖移入
`lpArchiveCertificates` 的填实路径。 -/
theorem linearProgrammingResults (hnl : TheNonlinearInequalities) :
    LinearProgrammingResults :=
  linearProgrammingResultsOf hnl (lpArchiveCertificates hnl.2.2.2.1
    (nonlinear_imp_lp_main_estimate_p16 hnl.2.2.1))

/-- **接口 3 → 真证明（2026-09-21 方向 A）**：HOL `kepler_conjecture_with_assumptions`
（the_main_statement.hl:170-251，80 行 tactic 脚本）的镜像。消费 §2c 骨架占位
+ PA25 `PACKING_CHAPTER_MAIN_CONCLUSION` + LA16 `nonlinear_imp_lp_main_estimate_p16`
+ Phase 2 `tame_classification` + §4 `goodListArchive`。 -/
theorem textCapstone : TextCapstone := by
  intro a ⟨hTC, ⟨hAllGood, hLPR⟩, hNL⟩
  obtain ⟨hpnn, hox3, hmnt, hlpineq, hpacka, hkcblrqc⟩ := hNL
  have hmain : lp_main_estimate := nonlinear_imp_lp_main_estimate_p16 hmnt
  refine kcImpTheKc ?_
  by_contra hneg
  -- packing 章主结论：¬kc ∧ pnn ∧ ox3q1h → ∃W. packing ∧ ⊆annulus ∧ ¬localAnnulus
  obtain ⟨W, hWp, hWsub, hWlai⟩ := PACKING_CHAPTER_MAIN_CONCLUSION hneg hpnn hox3
  have hW12 : 12 < scriptL W := by
    by_contra hle
    exact hWlai ((localAnnulusInequalityScriptL W).mpr (not_lt.1 hle))
  obtain ⟨V, hcV⟩ := fcdjdot hpacka ⟨W, hWp, hWsub, hW12⟩
  -- contravening V → tame_planar_hypermap (fan-H V)（MQMSMAB）
  have hfanV : FAN 0 V (ESTD V) := contraveningFan V hcV
  have htpH : TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfanV) :=
    mqmsmab V hkcblrqc hmain hfanV hcV
  have hresH : (hypermapOfFan 0 V (ESTD V) hfanV).IsRestricted :=
    tamePlanarHypermapRestricted _ htpH
  -- JCAJYDU：restricted → 图对应 gH
  obtain ⟨g, hgPlane, hgg4, Hg, hHgIs, hIsoFanHg⟩ := jcajydu _ hresH
  have htameg : tame g := tameCorrespondenceIso g _ _ hgg4 htpH hIsoFanHg hHgIs
  -- tame_classification：tame g → ∃y ∈ a, iso_fgraph (fgraph g) y
  obtain ⟨y, hyA, hyG⟩ := hTC g hgPlane htameg
  -- ELLLNYZ 镜像析取
  obtain ⟨Hy, hHyIs, hbr1 | hbr2⟩ :=
    elllnyz g.fgraph y hgg4.1 (hAllGood y hyA) hyG Hg hHgIs
  · -- 正向分支：iso (fan-H) (hol y) 经 iso_trans，LP 结果给 ¬contravening V
    exact hLPR V hfanV ⟨hlpineq, hmain, ⟨y, hyA, ⟨Hy, hHyIs,
      hypermapIsoTrans hIsoFanHg hbr1⟩⟩⟩ hcV
  · -- 镜像分支：绕行 IMAGE (--) V
    have hnegV : Contravening ((fun v => -v) '' V) := contraveningNegative V hcV
    have hfanN : FAN 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V)) :=
      contraveningFan _ hnegV
    have hfn : HypermapIso
        (hypermapOfFan 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V)) hfanN)
        (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfanV)) :=
      hypermapOfFanNeg V hcV hfanV hfanN
    have hop : HypermapIso (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfanV))
        (oppositeHypermap Hg) := (isoOppositeEq _ _).mp hIsoFanHg
    exact hLPR _ hfanN ⟨hlpineq, hmain, ⟨y, hyA, ⟨Hy, hHyIs,
      hypermapIsoTrans (hypermapIsoTrans hfn hop) hbr2⟩⟩⟩ hnegV

/-- HOL `Good_list_archive.good_list_archive`（HOL 侧由计算求得 archive 每张图
满足 `good_list`）。**已闭合（P6-C，2026-09-19）**：19715 张图（Tri 9 / Quad 1253 /
Pent 16080 / Hex 2373）逐片 `native_decide`（`Kepler/Assembly/GoodListShard*.lean`，
23 分片，DECISIONS.md 2026-08-10 scoped exception + 2026-09-19 P6-C 扩展），
纯内核组合器 `Kepler/Assembly/GoodListAll.lean` 的 `goodListArchiveAll` 收拢。 -/
theorem goodListArchive : AllGoodList tameArchiveLists := goodListArchiveAll

/-! ## 4. 装配定理 -/

/-- **装配定理**：HOL `kepler_conjecture_with_assumptions_and_archive`
（the_kepler_conjecture.hl:69-85）的镜像。

HOL tactic 脚本逐步对应：
- `INTRO_TAC kepler_conjecture_with_assumptions [`tame_archive_lists`];
   DISCH_THEN MATCH_MP_TAC` ↦ `hTC tameArchiveLists`；
- `ASM_REWRITE_TAC[GSYM import_tame_classification_tame]`
  （`import_tame_classification = tame_classification tame_archive_lists`，:46-52）
  ↦ 第一分量由 Phase 2 **已证**定理 `Kepler.Graphs.tame_classification`
  （TameClassification.lean:23-25）给出——`Archive`（RelativeCompleteness.lean:110）
  与 `{y | y ∈ tameArchiveLists}` 定义上相等；
- `ASM_REWRITE_TAC[good_linear_programming_results; GSYM linear_programming_results]`
  ↦ 第二分量拆为 `⟨goodListArchive, hLP⟩`；
- `MP_TAC Good_list_archive.good_list_archive` ↦ 引用已闭合的 `goodListArchive`。 -/
theorem assembly (hNL : TheNonlinearInequalities) (hLP : LinearProgrammingResults)
    (hTC : TextCapstone) : TheKeplerConjecture := by
  refine hTC tameArchiveLists ⟨?_, ⟨goodListArchive, hLP⟩, hNL⟩
  intro g hpg ht
  exact Kepler.Graphs.tame_classification hpg ht

/-- 闭合形态：消费三个接口占位 + 已闭合的 `goodListArchive` 后的主定理。
`#print axioms` 的 sorryAx 清单即全项目债务图（docs/phase6-spine.md §1）。 -/
theorem the_kepler_conjecture_from_interfaces : TheKeplerConjecture :=
  assembly nonlinearInequalities (linearProgrammingResults nonlinearInequalities)
    textCapstone

/-! ## 5. 公理审计 -/

#print axioms assembly
#print axioms the_kepler_conjecture_from_interfaces
#print axioms Kepler.the_kepler_conjecture

end Kepler.Assembly

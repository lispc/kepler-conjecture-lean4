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

  接口冻结 2026-09-19：`nonlinearInequalities` / `linearProgrammingResults` /
  `textCapstone` 三个 sorry 占位定理是本文件**唯一**允许的 sorry
  （第四占位 `goodListArchive` 已由 P6-C 闭合为真证明，2026-09-19）；
  `assembly` 本体是真证明（对照 HOL tactic 脚本逐行翻译）。
-/
import Kepler.Statement
import Kepler.Graphs
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
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

/-- PLACEHOLDER(G4)：HOL `pack_nonlinear_non_ox3q1h` 分量的 ID 清单。 -/
def idsPackNonlinearNonOx3q1h : List String := []
/-- PLACEHOLDER(G4)：HOL `ox3q1h` 分量的 ID 清单。 -/
def idsOx3q1h : List String := []
/-- PLACEHOLDER(G4)：HOL `main_nonlinear_terminal_v11` 分量的 ID 清单（993 条主体）。 -/
def idsMainNonlinearTerminalV11 : List String := []
/-- PLACEHOLDER(G4)：HOL `lp_ineqs` 分量的 ID 清单（the_main_statement.hl:29-45）。 -/
def idsLpIneqs : List String := []
/-- PLACEHOLDER(G4)：HOL `pack_ineq_def_a` 分量的 ID 清单。 -/
def idsPackIneqDefA : List String := []
/-- PLACEHOLDER(G4)：HOL `kcblrqc_ineq_def` 分量的 ID 清单。 -/
def idsKcblrqcIneqDef : List String := []

/-- HOL `lp_ineqs`（the_main_statement.hl:29-45）的注册表折算形态。
在 HOL 中它同时是 `the_nonlinear_inequalities` 的第四合取项和
`linear_programming_results` 的前提——此处同样被两处共享。 -/
def LpIneqs : Prop := AllCertified idsLpIneqs

/-- **接口 1**：HOL `the_nonlinear_inequalities`（the_main_statement.hl:55-59）
的折算形态——六件合取，逐分量 =（ID 清单，量化命题）。 -/
def TheNonlinearInequalities : Prop :=
  AllCertified idsPackNonlinearNonOx3q1h ∧ AllCertified idsOx3q1h ∧
    AllCertified idsMainNonlinearTerminalV11 ∧ LpIneqs ∧
    AllCertified idsPackIneqDefA ∧ AllCertified idsKcblrqcIneqDef

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

/-! ## 3. 接口 sorry 占位（接口冻结 2026-09-19；本文件仅有的三个 sorry） -/

/-- 接口占位（冻结 2026-09-19）。债务归属：Phase 4 / G4 粘合（P6-E）。
消除顺序：先填六个 ID 清单与 `CertifiedIneqHolds` 语义，再逐条闭合证书。 -/
theorem nonlinearInequalities : TheNonlinearInequalities := by
  sorry

/-- 接口占位（冻结 2026-09-19）。债务归属：Phase 3 LP 桥量产（P6-D）。
依赖 P6-C 的 `hypermapOfList` 构造落地（见 `IsHypermapOfList` 差距说明）。 -/
theorem linearProgrammingResults : LinearProgrammingResults := by
  sorry

/-- 接口占位（冻结 2026-09-19）。债务归属：Phase 5 capstone
（PackingConcl/LocalConcl 流水线，按 the_main_statement.hl:177-251 脚本复现）。 -/
theorem textCapstone : TextCapstone := by
  sorry

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
  assembly nonlinearInequalities linearProgrammingResults textCapstone

/-! ## 5. 公理审计 -/

#print axioms assembly
#print axioms the_kepler_conjecture_from_interfaces
#print axioms Kepler.the_kepler_conjecture

end Kepler.Assembly

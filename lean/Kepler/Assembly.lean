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
  `linearProgrammingResults` 占位定理仍在；
  第四占位 `goodListArchive` 已由 P6-C 闭合为真证明；
  `assembly` 本体是真证明（对照 HOL tactic 脚本逐行翻译）。
  2026-10-08 T1 自上而下第一波：接口 1 `nonlinearInequalities` 的单根 sorry
  展开为 §2a' 六分量具名骨架件的显式装配（15 枚：14 开放骨架 + 1 真装配）；
  `CertifiedIneqHolds` 语义按 §2a 处方落诚实最小形（试点查表，键
  `"3397113841"` 端到端闭合 = 会师点）。
-/
import Kepler.Statement
import Kepler.Graphs
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto18
import Kepler.Text.PackingAuto21
import Kepler.Text.PackingAuto25
import Kepler.Text.Hypermap
import Kepler.Text.ContraFan
import Kepler.Text.LocalAuto16
import Kepler.Text.TameLp
import Kepler.Assembly.GoodListDefs
import Kepler.Assembly.GoodListAll
-- T1 自上而下第一波（2026-10-08）：六 ID 清单数据（P6-E 生成件，零依赖）+
-- `CertifiedIneqHolds` 查表的试点链（G4 证书 C3397113841 + 粘合 + 语义命题）。
import Kepler.Assembly.IdLists
import Kepler.Assembly.IneqPilot

open Classical Metric Set
open Kepler.Geom Kepler.Text Kepler.Text.Fan Kepler.Graphs

-- 实例盾（2026-10-12 A7，随 `import Kepler.Text.TameLp` 引入）：TameLp 的闭包
-- 带入全局实例 `LocalAuto2.dartDecEq2 : DecidableEq (V3 × V3)`，与本文件既有的
-- `instDecidableEqProd` 解析竞争（§2c.8 A5 代码按后者钉死）。此处把 dartDecEq2
-- 在本文件内降为 0 优先级 local instance，恢复 import 前的解析行为。
attribute [local instance 0] dartDecEq2

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

/-! **Contravening 七合取具名投影族（2026-10-13 nli 接线波前置；纯 addition）**：
七分量逐一具名化（对照 PA21 `proj_bank_*` 家族章程 §6.5 "no bare chains"）。
消费点样板 = §2c `contraveningFan` 的 `hc.2.2.2.2.1` 裸链（:660 附近）与
`contraveningNegative` 的 `hc.2.2…` 裸链族（:2557/:2587-2603 附近，本波时
行号）；本波只补件不改写消费点（改写属后续波，涉语句冻结面）。 -/

/-- Named projection of `Contravening` component 1/7（HOL `packing V`）. -/
theorem proj_nliContrav_Packing (V : Set V3) (hc : Contravening V) :
    Packing V := hc.1

/-- Named projection of `Contravening` component 2/7
（HOL `V SUBSET ball_annulus`）. -/
theorem proj_nliContrav_BallAnnulus (V : Set V3) (hc : Contravening V) :
    V ⊆ ballAnnulus := hc.2.1

/-- Named projection of `Contravening` component 3/7（HOL `scriptL V > &12`）. -/
theorem proj_nliContrav_ScriptL (V : Set V3) (hc : Contravening V) :
    scriptL V > 12 := hc.2.2.1

/-- Named projection of `Contravening` component 4/7（HOL scriptL 极大性）. -/
theorem proj_nliContrav_ScriptLMax (V : Set V3) (hc : Contravening V) :
    ∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL V :=
  hc.2.2.2.1

/-- Named projection of `Contravening` component 5/7（HOL
`CARD V = 13 \/ CARD V = 14 \/ CARD V = 15`；:660 裸链位 `hc.2.2.2.2.1`
的具名形态）. -/
theorem proj_nliContrav_Card (V : Set V3) (hc : Contravening V) :
    V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := hc.2.2.2.2.1

/-- Named projection of `Contravening` component 6/7（HOL
`surrounded_node (V, ESTD V)`；:2598 裸链位 `hc.2.2.2.2.2.1` 的具名形态）. -/
theorem proj_nliContrav_SurroundedESTD (V : Set V3) (hc : Contravening V) :
    ∀ v ∈ V, surroundedNode V (ESTD V) v := hc.2.2.2.2.2.1

/-- Named projection of `Contravening` component 7/7（HOL
`surrounded_node (V, ECTC V) \/ (norm v = &2)`；:2603 裸链位
`hc.2.2.2.2.2.2` 的具名形态）. -/
theorem proj_nliContrav_SurroundedECTC (V : Set V3) (hc : Contravening V) :
    ∀ v ∈ V, surroundedNode V (ECTC V) v ∨ ‖v‖ = 2 := hc.2.2.2.2.2.2

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

/-- 单条证书不等式成立的语义。**T1 骨架波（2026-10-08）按上方处方落地的诚实
最小形**：查表体 = `certifiedIneqHolds_pilot`（IneqPilot.lean 的量产样板表）——
表内键按 `id` 展开为 ineq.hl 字面量化不等式命题（`!y1..y6. box ==> ineq` 形；
现含唯一端到端键 `"3397113841"`：G4 证书 `C3397113841_pos`（1504 叶）+ 粘合
`C3397113841_evalReal` + 语义命题 `ineqProp_3397113841`，`#print axioms` =
标准三公理，IneqPilot.lean:96-97 实证），表外键回落 `True`（原占位语义）。
回落分支不可达性由量产波「ID 清单 = 查表定义域」不变量钉死（IdLists.lean
`certLookupDomain`；其 :699 else-True 静默退化警告在案：表未覆盖定义域前，
§2a' 的注册表侧骨架**不得**经回落分支平凡闭合）。签名（`String → Prop`，
2026-09-19 冻结）一字未动，仅按处方替换函数体。 -/
def CertifiedIneqHolds (_id : String) : Prop := certifiedIneqHolds_pilot _id

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
def KcblrqcIneqDef : Prop := Kepler.Text.TameLp.KcblrqcIneqDef

/-- **接口 1**：HOL `the_nonlinear_inequalities`（the_main_statement.hl:55-59）
的六件合取。前三分量已用 Lean 侧真 Prop 真化（2026-09-21 骨架化精化，取代
原 ID 清单占位）：`pack_nonlinear_non_ox3q1h`（PA21:147）、`ox3q1hP25`（PA25:87）、
`main_nonlinear_terminal_v11`（LocalAuto1:793，Phase 4/G4 的主叶子）；
后三分量 `LpIneqs` 为注册表折算，`PackIneqDefA`/`KcblrqcIneqDef` 为标明的
占位。 -/
def TheNonlinearInequalities : Prop :=
  pack_nonlinear_non_ox3q1h ∧ ox3q1hP25 ∧ main_nonlinear_terminal_v11 ∧ LpIneqs ∧
    PackIneqDefA ∧ KcblrqcIneqDef

/-! **六分接口具名投影族（2026-10-13 nli 接线波前置；纯 addition）**：
`TheNonlinearInequalities` 六分量逐一具名化（对照 PA21 `proj_bank_*` 家族，
章程 §6.5 "no bare chains"）。消费点样板 = §3 `linearProgrammingResults` 的
`hnl.2.2.2.1` 裸链（:5381 附近，本波时行号）；本波只补件不改写消费点
（改写属 nli 28+127 接线主波，涉语句冻结面）。 -/

/-- Named projection of `TheNonlinearInequalities` component 1/6
（`pack_nonlinear_non_ox3q1h`）. -/
theorem proj_nli_PackNonlinearNonOx3q1h (h : TheNonlinearInequalities) :
    pack_nonlinear_non_ox3q1h := h.1

/-- Named projection of `TheNonlinearInequalities` component 2/6
（`ox3q1hP25`）. -/
theorem proj_nli_Ox3q1hP25 (h : TheNonlinearInequalities) : ox3q1hP25 := h.2.1

/-- Named projection of `TheNonlinearInequalities` component 3/6
（`main_nonlinear_terminal_v11`）. -/
theorem proj_nli_MainNonlinearTerminalV11 (h : TheNonlinearInequalities) :
    main_nonlinear_terminal_v11 := h.2.2.1

/-- Named projection of `TheNonlinearInequalities` component 4/6（`LpIneqs`；
:5381 裸链位 `hnl.2.2.2.1` 的具名形态）. -/
theorem proj_nli_LpIneqs (h : TheNonlinearInequalities) : LpIneqs := h.2.2.2.1

/-- Named projection of `TheNonlinearInequalities` component 5/6
（`PackIneqDefA`）. -/
theorem proj_nli_PackIneqDefA (h : TheNonlinearInequalities) : PackIneqDefA :=
  h.2.2.2.2.1

/-- Named projection of `TheNonlinearInequalities` component 6/6
（`KcblrqcIneqDef`）. -/
theorem proj_nli_KcblrqcIneqDef (h : TheNonlinearInequalities) :
    KcblrqcIneqDef := h.2.2.2.2.2

/-! ### 2a'. T1 中层骨架 —— 单根接口 sorry 的六分量展开（2026-10-08，
自上而下第一波）

`nonlinearInequalities`（§3）的证明体从单根 `sorry` 换成对下方具名骨架件的
显式装配；sorryAx 债务从「一个黑箱接口」分解为**按分量、按清单结构记账**的
骨架节点（主定理可达债务图 T 线第一层：15 枚具名骨架件 = 14 枚开放骨架 +
1 枚真装配，另有 §2a 查表上的会师点真叶 1 枚）。骨架形一律
`theorem nliX : <分量> := sorry`（内联形），每件带 HOL/ineq.hl 出处 +
底层资产状态（已闭合可证 / deferred-compute / 真缺口）+ `-- NEEDS:` 记账。

底层资产口径（STATUS.md Phase 4，诚实标记用）：非线性求解层 **68/176 y 空间
闭合**（bb_arb 证书多数不在库——旧机丢失）、**G4 内核端到端 8 案**、92 prep
家族证据链降级**待重做**、**16 条真残余**；155 定义闭包 **B=112/124 就位**
（余批赖 LA38 未移植 lane）。自下而上会师点 = `CertifiedIneqHolds` 查表
（§2a，现含试点键）+ `Kepler.Interval.Cases.*` 在库证书
（C3397113841 / C1965189142x34 / C3253650737 / C4717061266 /
C2570626711p200 / C549*）。 -/

/-! #### 分量 1/6 `pack_nonlinear_non_ox3q1h`（81 条；PA21 MERGE-INEQ wave 0
route A' 结构化：19 条消费切片 = cell3 7 + TSKAJXY 10 + GRKIBMP 2，加 62 条
rest 叶） -/

/-! **中层骨架 1a/1b 拆条波（2026-10-13 nli 接线波前置展开，rest 波样式套用）**：
`cell3_bank` 七条与 `tsk_bank` 十条逐条具名拆单——`nliCell3<NAME>` /
`nliTsk<NAME>` 共 17 枚，与 PA21 对应 `bank_*` def 一一对应（盒形/结论直录
PackingAuto21.lean:205-355），位次 1a k/7、1b k/10 = bank 合取序
（PackingAuto21.lean:388/382；cell3_hyp = merge_ineq.hl:3490-3495、
tsk_hyp = merge_ineq.hl:1370-1377 string 序）。本波真闭合 2/17
（`#print axioms` = 标准三公理，路线照 rest 2 常数算术先例）：1b-9
`TSKAJXY-delta_x4`（`deltaX4` 二次型盒区间算术，十枚单项 `mul_le_mul`
界 + linarith，最坏角组合 ≈58.58 > 0）与 1b-10 `TSKAJXY-eulerA`
（`Real.le_sqrt` 单调性 + 常数区间算术，`eulerAX` 四项逐项下界
11.2+0+7.7999+7.7999，真余量 ≈26.8）。其余 15 条为几何/实分析内容件
（`gamma3fXDivSqrtdelta`/`gamma4fgcy`/`eta_y`/`solEuler*`/`rad2X`/
`lmfun` 族，需逐条 G4 证书），维持 NEEDS 记账骨架。 -/

/-- 1a 1/7：HOL ineq entry `QZECFIC wt0`（ineq.hl:1372；PA21
`bank_QZECFICwt0`，盒 [1,1]³×[2.01,2hmin]×[2,2hmin]²）。资产状态：
deferred-compute（`gamma3fXDivSqrtdelta` 实分析内容，证书不在库）。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3QZECFICwt0 : bank_QZECFICwt0 := sorry

/-- 1a 2/7：HOL ineq entry `QZECFIC wt0 corner`（ineq.hl:1389；PA21
`bank_QZECFICwt0corner`，盒 [1,1]³×[2,2.01]³）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3QZECFICwt0corner : bank_QZECFICwt0corner := sorry

/-- 1a 3/7：HOL ineq entry `QZECFIC wt0 sqrt8`（ineq.hl:1406；PA21
`bank_QZECFICwt0sqrt8`，盒 [1,1]³×[2hplus,√8]×[2,2hmin]²，析取第二支
`eta_y y4 y5 y6 ^ 2 > 2`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3QZECFICwt0sqrt8 : bank_QZECFICwt0sqrt8 := sorry

/-- 1a 4/7：HOL ineq entry `QZECFIC wt1`（ineq.hl:1425；PA21
`bank_QZECFICwt1`，盒 [√2,√2]³×[2hmin,2hplus]×[2,2hmin]²，`h0cut y4`
参数化双支）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3QZECFICwt1 : bank_QZECFICwt1 := sorry

/-- 1a 5/7：HOL ineq entry `QZECFIC wt2 A`（ineq.hl:1443；PA21
`bank_QZECFICwt2A`，盒 [√2,√2]³×[2hmin,√8]²×[2,2hmin]，`h0cut y4/y5`
参数化双支）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3QZECFICwt2A : bank_QZECFICwt2A := sorry

/-- 1a 6/7：HOL ineq entry `CIHTIUM`（ineq.hl:1462；PA21 `bank_CIHTIUM`，
盒 [1,1]³×[2hmin,√8]³，结论 `eta_y y4 y5 y6 ^ 2 > 2`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3CIHTIUM : bank_CIHTIUM := sorry

/-- 1a 7/7：HOL ineq entry `CJFZZDW`（ineq.hl:1479；PA21 `bank_CJFZZDW`，
盒 [1,1]³×[2hplus,√8]²×[2,√8]，结论同 CIHTIUM）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliCell3CJFZZDW : bank_CJFZZDW := sorry

/-- 中层骨架 1a 本体：cell3 七条的显式合取装配（照 PA21 `cell3_bank` def
逐位对齐；每枚组件 = 上方具名骨架件）。
-- NEEDS: 无独立债务——骨架债仅自上方 7 枚开放组件流入。 -/
theorem nliCell3Bank : cell3_bank :=
  ⟨nliCell3QZECFICwt0, nliCell3QZECFICwt0corner, nliCell3QZECFICwt0sqrt8,
    nliCell3QZECFICwt1, nliCell3QZECFICwt2A, nliCell3CIHTIUM, nliCell3CJFZZDW⟩

/-- 1b 1/10：HOL ineq entry `TSKAJXY-GXSABWC DIV`（ineq.hl:359；PA21
`bank_TSKAJXYGXSA`，x-空间盒 [2.8²,8]×[4,2.01²]²×[2.8²,8]×[4,2.01²]²，
solEuler/ldih 四项和折减 `1/12`，析取第二支 `deltaX < 0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskGXSA : bank_TSKAJXYGXSA := sorry

/-- 1b 2/10：HOL ineq entry `TSKAJXY-IYOUOBF sharp v2`（ineq.hl:242；PA21
`bank_TSKAJXYIYOUOBFsharpv2`，盒 [2hplus,√8]×[2,2.001]²×[2,2hmin]×
[2,2.001]²）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskIYOUOBFsharpv2 : bank_TSKAJXYIYOUOBFsharpv2 := sorry

/-- 1b 3/10：HOL ineq entry `TSKAJXY-IYOUOBF sym`（ineq.hl:223；PA21
`bank_TSKAJXYIYOUOBFsym`，盒 [2hplus,√8]×[2.001,2hmin]×[2,2hmin]⁴，析取
三排序支 `y2 < y3/y5/y6`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskIYOUOBFsym : bank_TSKAJXYIYOUOBFsym := sorry

/-- 1b 4/10：HOL ineq entry `TSKAJXY-RIBCYXU sharp`（ineq.hl:165；PA21
`bank_TSKAJXYRIBCYXUsharp`，盒 [2,2.001]⁶）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskRIBCYXUsharp : bank_TSKAJXYRIBCYXUsharp := sorry

/-- 1b 5/10：HOL ineq entry `TSKAJXY-RIBCYXU sym`（ineq.hl:183；PA21
`bank_TSKAJXYRIBCYXUsym`，盒 [2.001,2hmin]×[2,2hmin]⁵，析取八排序支）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskRIBCYXUsym : bank_TSKAJXYRIBCYXUsym := sorry

/-- 1b 6/10：HOL ineq entry `TSKAJXY-TADIAMB`（ineq.hl:127；PA21
`bank_TSKAJXYTADIAMB`，盒 [2hplus,√8]²×[2,√8]⁴，结论
`2 < yOfX rad2X …`（外接半径平方））。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskTADIAMB : bank_TSKAJXYTADIAMB := sorry

/-- 1b 7/10：HOL ineq entry `TSKAJXY-WKGUESB sym`（ineq.hl:281；PA21
`bank_TSKAJXYWKGUESBsym`，盒 [2hplus,√8]×[2.01,2hmin]×[2,2hmin]×
[2hplus,√8]×[2,2hmin]²，析取四排序支）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskWKGUESBsym : bank_TSKAJXYWKGUESBsym := sorry

/-- 1b 8/10：HOL ineq entry `TSKAJXY-XLLIPLS`（ineq.hl:304；PA21
`bank_TSKAJXYXLLIPLS`，盒 [2hplus,√8]×[2,2.01]²×[2hplus,2.8]×[2,2.01]²）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliTskXLLIPLS : bank_TSKAJXYXLLIPLS := sorry

/-- 1b 9/10：HOL ineq entry `TSKAJXY-delta_x4`（ineq.hl:341；PA21
`bank_TSKAJXYdx4`，x-空间盒 [4,2.01²]²×[2.8²,8]×[4,2.01²]²×[2.8²,8]）。
本波真闭合：`deltaX4` 二次型逐单项盒区间算术——`mul_le_mul` 十枚单项界
（x1² ≤ 4.0401²、x2x3/x5x6 ≤ 4.0401·8、x3x6 ≥ 2.8²·2.8² 等）+ linarith，
最坏角组合下界 ≈58.58 > 0（常数余量）。 -/
theorem nliTskdx4 : bank_TSKAJXYdx4 := by
  intro x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have e : (2.01 : ℝ) ^ 2 = 4.0401 := by norm_num
  have h1h' : x1 ≤ 4.0401 := by linarith [h1h, e]
  have h2h' : x2 ≤ 4.0401 := by linarith [h2h, e]
  have h4h' : x4 ≤ 4.0401 := by linarith [h4h, e]
  have h5h' : x5 ≤ 4.0401 := by linarith [h5h, e]
  have n1 : (0 : ℝ) ≤ x1 := by linarith
  have n2 : (0 : ℝ) ≤ x2 := by linarith
  have n3 : (0 : ℝ) ≤ x3 := by linarith
  have n4 : (0 : ℝ) ≤ x4 := by linarith
  have n5 : (0 : ℝ) ≤ x5 := by linarith
  have n6 : (0 : ℝ) ≤ x6 := by linarith
  have p11 : x1 * x1 ≤ 4.0401 * 4.0401 := mul_le_mul h1h' h1h' n1 (by norm_num)
  have p12 : (4 : ℝ) * 4 ≤ x1 * x2 := mul_le_mul h1l h2l (by norm_num) n1
  have p13 : (4 : ℝ) * (2.8 : ℝ) ^ 2 ≤ x1 * x3 :=
    mul_le_mul h1l h3l (by norm_num) n1
  have p14 : x1 * x4 ≤ 4.0401 * 4.0401 :=
    mul_le_mul h1h' h4h' n4 (by norm_num)
  have p15 : (4 : ℝ) * 4 ≤ x1 * x5 := mul_le_mul h1l h5l (by norm_num) n1
  have p16 : (4 : ℝ) * (2.8 : ℝ) ^ 2 ≤ x1 * x6 :=
    mul_le_mul h1l h6l (by norm_num) n1
  have p23 : x2 * x3 ≤ 4.0401 * 8 := mul_le_mul h2h' h3h n3 (by norm_num)
  have p25 : (4 : ℝ) * 4 ≤ x2 * x5 := mul_le_mul h2l h5l (by norm_num) n2
  have p36 : (2.8 : ℝ) ^ 2 * (2.8 : ℝ) ^ 2 ≤ x3 * x6 :=
    mul_le_mul h3l h6l (by norm_num) n3
  have p56 : x5 * x6 ≤ 4.0401 * 8 := mul_le_mul h5h' h6h n6 (by norm_num)
  unfold deltaX4
  linarith [p11, p12, p13, p14, p15, p16, p23, p25, p36, p56]

/-- 1b 10/10：HOL ineq entry `TSKAJXY-eulerA`（ineq.hl:324；PA21
`bank_TSKAJXYeulerA`，x-空间盒 [2.8²,8]×[4,2.01²]²×[2.8²,8]×[4,2.01²]²）。
本波真闭合：√ 单调性（`Real.le_sqrt`：√x1 ≥ 2.8、√x2/√x3 ≥ 2）+ 常数
区间算术——`eulerAX` 四项逐项下界 11.2 + 0 + 7.7999 + 7.7999（首项
√x1√x2√x3 ≥ 2.8·2·2；第二项线性因子 x2+x3−x4 ≥ 0；三/四项线性因子
x1+x3−x5、x1+x2−x6 ≥ 7.84+4−4.0401），真余量 ≈26.8。 -/
theorem nliTskeulerA : bank_TSKAJXYeulerA := by
  intro x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have e : (2.01 : ℝ) ^ 2 = 4.0401 := by norm_num
  have h5h' : x5 ≤ 4.0401 := by linarith [h5h, e]
  have h6h' : x6 ≤ 4.0401 := by linarith [h6h, e]
  have r1 : (2.8 : ℝ) ≤ Real.sqrt x1 :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr h1l
  have r2 : (2 : ℝ) ≤ Real.sqrt x2 :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have r3 : (2 : ℝ) ≤ Real.sqrt x3 :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hsx1 : (0 : ℝ) ≤ Real.sqrt x1 := Real.sqrt_nonneg x1
  have hsx2 : (0 : ℝ) ≤ Real.sqrt x2 := Real.sqrt_nonneg x2
  have hsx3 : (0 : ℝ) ≤ Real.sqrt x3 := Real.sqrt_nonneg x3
  have t2 : (0 : ℝ) ≤ x2 + x3 - x4 := by linarith
  have t3 : (7.84 : ℝ) + 4 - 4.0401 ≤ x1 + x3 - x5 := by
    have e1 : (2.8 : ℝ) ^ 2 = 7.84 := by norm_num
    linarith [e1, h1l, h3l, h5h']
  have t4 : (7.84 : ℝ) + 4 - 4.0401 ≤ x1 + x2 - x6 := by
    have e1 : (2.8 : ℝ) ^ 2 = 7.84 := by norm_num
    linarith [e1, h1l, h2l, h6h']
  have p12 : (2.8 : ℝ) * 2 ≤ Real.sqrt x1 * Real.sqrt x2 :=
    mul_le_mul r1 r2 (by norm_num) hsx1
  have p123 : (2.8 : ℝ) * 2 * 2 ≤ Real.sqrt x1 * Real.sqrt x2 * Real.sqrt x3 :=
    mul_le_mul p12 r3 (by norm_num) (mul_nonneg hsx1 hsx2)
  have z2 : (0 : ℝ) ≤ Real.sqrt x1 * (x2 + x3 - x4) :=
    mul_nonneg hsx1 t2
  have q3 : (2 : ℝ) * ((7.84 : ℝ) + 4 - 4.0401) ≤ Real.sqrt x2 * (x1 + x3 - x5) :=
    mul_le_mul r2 t3 (by linarith [t3]) hsx2
  have q4 : (2 : ℝ) * ((7.84 : ℝ) + 4 - 4.0401) ≤ Real.sqrt x3 * (x1 + x2 - x6) :=
    mul_le_mul r3 t4 (by linarith [t4]) hsx3
  unfold eulerAX
  linarith [p12, p123, z2, q3, q4]

/-- 中层骨架 1b 本体：TSKAJXY 十条的显式合取装配（照 PA21 `tsk_bank` def
逐位对齐 = merge_ineq.hl:1370-1377 string 序）。
-- NEEDS: 无独立债务——骨架债仅自上方 8 枚开放组件流入。 -/
theorem nliTskBank : tsk_bank :=
  ⟨nliTskGXSA, nliTskIYOUOBFsharpv2, nliTskIYOUOBFsym, nliTskRIBCYXUsharp,
    nliTskRIBCYXUsym, nliTskTADIAMB, nliTskWKGUESBsym, nliTskXLLIPLS,
    nliTskdx4, nliTskeulerA⟩

/-- 中层骨架 1c：GRKIBMP 切片组（merge_ineq.hl:3795 add_hyp 序；
PackingAuto21.lean:389，`GRKIBMP A V2` + `GRKIBMP B V2`，ineq.hl:1520/1537）。
资产状态：**两半均已 PA21 解析手证闭合**（2026-10-12：A V2 =
`bank_GRKIBMPAV2_proof` h0cut 三分+三倍角 arccos 种子+mm1 双侧围闭；
B V2 = `bank_GRKIBMPBV2_proof` 因式分解+单调+mm1<4/3 种子——尖锐边界组
两枚 residue16 销账，81 条记账"1c 两条"清零）。
-- RESOLVED: nliGrkBank := ⟨A V2, B V2⟩ 一行装配（编排者机械收口）。 -/
theorem nliGrkBank : grk_bank :=
  ⟨bank_GRKIBMPAV2_proof, bank_GRKIBMPBV2_proof⟩

/-! **中层骨架 1d（2026-10-13 nli 接线波前置展开）：81 条清单的其余 62 条
rest 叶**。PA21 已把 rest 叶拆为 62 条显式盒式 `bank_*` 合取
（PackingAuto21.lean:935 `pack_nonlinear_rest`，顺序 = IdLists 注册序；
PackingAuto21.lean:395 原 `PLACEHOLDER(G4)` 桩已废）并备齐 62 枚具名投影
`proj_bank_*`（PackingAuto21.lean:2488 起；消费样板 = PA25
`IXPOTPA_MERGED` 的 `proj_bank_IXPOTPA hnl y1 …` 逐应用法）。本节按"拆
单条"口径同步展开：62 枚具名骨架件 `nliRest*`（↔ PA21 62 枚 `proj_bank_*`
一一对应，rest 位次 k/62 记于各 docstring）+ 末端显式合取装配
`nliPackNonlinearRest`（签名至 `:=` 与冻结版逐字一致）。
应用签名审计（照 PA25 逐应用法逐条过）：60/62 为标准 6 变量盒（应用 =
`proj_bank_* hnl y1 … y6` + 12 盒前件）；例外 rest 2 `6096597438 a` 与
rest 60 `ZTGIJCF0` 为 1 变量盒（应用 = `proj_bank_* hnl h hh hhh` 形，
bank 定义体 delta 展开后照常逐应用，不构成接线障碍）。
本波真闭合 3/62（`#print axioms` = 标准三公理）：rest 2 `6096597438 a`
（常数算术）、rest 4 `1965189142 34`（`lfunY1 ≤ 1` 上界 + 线艺；
Interval/Cases.C1965189142x34 的 G4 证书在库冗余，其粘合引理归量产波，
与本体闭合互不依赖）、rest 60 `ZTGIJCF0`（spine 常数 + `Real.pi_lt_d4`
夹逼，真余量 ≈3.9e-5）。其余 59 条 deferred-compute（92 prep 家族重做
口径覆盖其中多数）；rest 9 `QITNPEA 3725403817` 内核闭合证书（964,984 叶，
2026-09-18，公理标准三）不在本仓，粘合引理归 nli 28+127 接线主波。 -/

/-- rest 1/62：HOL ineq entry `6096597438 b`（ineq.hl:1661，盒
[3,64]×[1,1]⁵；PA21 `bank_6096597438b` / `proj_bank_6096597438b`）。
资产状态：deferred-compute（`asn797k` 实分析内容，证书不在库）。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRest6096597438b : bank_6096597438b := sorry

/-- rest 2/62：HOL ineq entry `6096597438 a`（ineq.hl:1650，1 变量盒
[1,1]；PA21 `bank_6096597438a` / `proj_bank_6096597438a`）。
本波真闭合：`lfun 1 = 1`（`div_self`）后纯常数算术
（0.591 − 0.0331·64 + 0.506 + 1 = −0.0214 < 0）。 -/
theorem nliRest6096597438a : bank_6096597438a := by
  intro _h _hl _hh
  have hne : (h0 - 1 : ℝ) ≠ 0 := by norm_num [h0]
  have hlf : lfun 1 = 1 := by
    unfold lfun
    exact div_self hne
  rw [hlf]
  norm_num

/-- rest 3/62：HOL ineq entry `1965189142 a`（ineq.hl:1598，盒
[1.0,1.26]×[3,34]×[1,1]⁴；PA21 `bank_1965189142a` /
`proj_bank_1965189142a`）。资产状态：deferred-compute（`asnFnhk` 实分析
内容，证书不在库）。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRest1965189142a : bank_1965189142a := sorry

/-- rest 4/62：HOL ineq entry `1965189142 34`（ineq.hl:1587，盒
[1.0,1.26]×[1,1]⁵；PA21 `bank_1965189142x34` /
`proj_bank_1965189142x34`）。
本波真闭合：x1 ≥ 1 给 `lfunY1 … ≤ 1`，常数部 0.591 − 0.0331·34 = −0.5344
主导（余量 ≈0.0284）。Interval/Cases.C1965189142x34 的 G4 证书在库冗余
（其粘合引理归量产接线波，与本体闭合互不依赖）。 -/
theorem nliRest1965189142x34 : bank_1965189142x34 := by
  intro x1 x2 x3 x4 x5 x6 h1l _h1h _h2l _h2h _h3l _h3h _h4l _h4h _h5l _h5h _h6l _h6h
  have hlf : lfunY1 x1 x2 x3 x4 x5 x6 ≤ 1 := by
    unfold lfunY1 lfun h0
    exact (div_le_one (by norm_num : (0 : ℝ) < 1.26 - 1)).mpr (by linarith)
  have hc : (0.591 : ℝ) - 0.0331 * 34 = -0.5344 := by norm_num
  linarith

/-- rest 5/62：HOL ineq entry `JSPEVYT`（ineq.hl:1495，盒
[1,1]³×[2hmin,√8]²×[2,√8]；PA21 `bank_JSPEVYT` / `proj_bank_JSPEVYT`）。
资产状态：deferred-compute（证书不在库）。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestJSPEVYT : bank_JSPEVYT := sorry

/-- rest 6/62：HOL ineq entry `QITNPEA 4003532128 a`（ineq.hl:1290，盒
[2hmin,2hplus]×[2,√8]×[√2,√2]³×[2,√8]；PA21 `bank_QITNPEA4003532128a` /
`proj_bank_QITNPEA4003532128a`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA4003532128a : bank_QITNPEA4003532128a := sorry

/-- rest 7/62：HOL ineq entry `IXPOTPA`（ineq.hl:1265，盒
[2hmin,2hplus]×[2,2hmin]²×[√8,4hmin]×[2,2hmin]²；PA21 `bank_IXPOTPA` /
`proj_bank_IXPOTPA`——PA25 `IXPOTPA_MERGED` 已按逐应用法消费此投影）。
资产状态：deferred-compute（证书不在库）。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestIXPOTPA : bank_IXPOTPA := sorry

/-- rest 8/62：HOL ineq entry `TXQTPVC`（ineq.hl:1241，盒
[2hmin,2hplus]×[2,2hmin]²×[2,√8]×[2,2hmin]²；PA21 `bank_TXQTPVC` /
`proj_bank_TXQTPVC`——PA25 `TXQTPVC_MERGED` 已消费）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestTXQTPVC : bank_TXQTPVC := sorry

/-- rest 9/62：HOL ineq entry `QITNPEA 3725403817`（ineq.hl:1221，盒
[2hmin,2hplus]×[2,2hmin]³×[2,2.1]×[2,2hmin]²；PA21
`bank_QITNPEA3725403817` / `proj_bank_QITNPEA3725403817`）。
资产状态：内核闭合证书在库外（964,984 叶，2026-09-18，公理标准三），
本仓无证书件。
-- NEEDS: 在库外证书移植或重发射 + 粘合引理入 §2a 查表（量产主波）。 -/
theorem nliRestQITNPEA3725403817 : bank_QITNPEA3725403817 := sorry

/-- rest 10/62：HOL ineq entry `QITNPEAv2 4003532128`（ineq.hl:1193，盒
[2hmin,2hplus]×[2,2hmin]³×[2,√8]×[2,2hmin]²；PA21
`bank_QITNPEAv24003532128` / `proj_bank_QITNPEAv24003532128`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEAv24003532128 : bank_QITNPEAv24003532128 := sorry

/-- rest 11/62：HOL ineq entry `PEMKWKU`（ineq.hl:1169，盒
[2hmin,2hplus]×[2,√8]×[2,2hmin]×[2,√8]×[2,2hmin]×[2,√8]；PA21
`bank_PEMKWU` / `proj_bank_PEMKWU`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestPEMKWU : bank_PEMKWU := sorry

/-- rest 12/62：HOL ineq entry `TEWNSCJ`（ineq.hl:1146，盒
[2hmin,2hplus]×[2,2hmin]³×[2,√8]×[2,2hmin]²；PA21 `bank_TEWNSCJ` /
`proj_bank_TEWNSCJ`——PA25 `TEWNSCJ_MERGED` 已消费，hrad/he1/he2 桥
`p25_gamma23Full8X_yOfX_eq` 就位）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestTEWNSCJ : bank_TEWNSCJ := sorry

/-- rest 13/62：HOL ineq entry `QITNPEA 5400790175 b`（ineq.hl:1121，盒
[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]²；PA21
`bank_QITNPEA5400790175b` / `proj_bank_QITNPEA5400790175b`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA5400790175b : bank_QITNPEA5400790175b := sorry

/-- rest 14/62：HOL ineq entry `QITNPEA 5400790175 a`（ineq.hl:1103，
盒同 rest 13；PA21 `bank_QITNPEA5400790175a` /
`proj_bank_QITNPEA5400790175a`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA5400790175a : bank_QITNPEA5400790175a := sorry

/-- rest 15/62：HOL ineq entry `QITNPEA 3848804089`（ineq.hl:1059，盒
[2hmin,2hplus]×[2,2hmin]⁵；PA21 `bank_QITNPEA3848804089` /
`proj_bank_QITNPEA3848804089`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA3848804089 : bank_QITNPEA3848804089 := sorry

/-- rest 16/62：HOL ineq entry `QITNPEA 5814748276`（ineq.hl:1041，盒同
rest 15；PA21 `bank_QITNPEA5814748276` / `proj_bank_QITNPEA5814748276`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA5814748276 : bank_QITNPEA5814748276 := sorry

/-- rest 17/62：HOL ineq entry `QITNPEA 6206775865`（ineq.hl:1023，盒同
rest 15；PA21 `bank_QITNPEA6206775865` / `proj_bank_QITNPEA6206775865`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA6206775865 : bank_QITNPEA6206775865 := sorry

/-- rest 18/62：HOL ineq entry `QITNPEA 5653753305`（ineq.hl:1004，盒
[2hmin,2hplus]×[2,2hmin]⁵；PA21 `bank_QITNPEA5653753305` /
`proj_bank_QITNPEA5653753305`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA5653753305 : bank_QITNPEA5653753305 := sorry

/-- rest 19/62：HOL ineq entry `BIXPCGW 9455898160`（ineq.hl:985，盒
[2hmin,2hplus]×[2,2hmin]⁵，HOL 字面 `-- #0.00569` 双重负号；PA21
`bank_BIXPCGW9455898160` / `proj_bank_BIXPCGW9455898160`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestBIXPCGW9455898160 : bank_BIXPCGW9455898160 := sorry

/-- rest 20/62：HOL ineq entry `FWGKMBZ`（ineq.hl:967，盒
[2hmin,2hplus]×[2,√8]⁵；PA21 `bank_FWGKMBZ` / `proj_bank_FWGKMBZ`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestFWGKMBZ : bank_FWGKMBZ := sorry

/-- rest 21/62：HOL ineq entry `FHBVYXZ b`（ineq.hl:942；PA21
`bank_FHBVYXZb` / `proj_bank_FHBVYXZb`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestFHBVYXZb : bank_FHBVYXZb := sorry

/-- rest 22/62：HOL ineq entry `FHBVYXZ a`（ineq.hl:914；PA21
`bank_FHBVYXZa` / `proj_bank_FHBVYXZa`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestFHBVYXZa : bank_FHBVYXZa := sorry

/-- rest 23/62：HOL ineq entry `FHBVYXZv2 a`（ineq.hl:888；PA21
`bank_FHBVYXZv2a` / `proj_bank_FHBVYXZv2a`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestFHBVYXZv2a : bank_FHBVYXZv2a := sorry

/-- rest 24/62：HOL ineq entry `QITNPEA 2134082733`（ineq.hl:864，盒
[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]²；PA21
`bank_QITNPEA2134082733` / `proj_bank_QITNPEA2134082733`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA2134082733 : bank_QITNPEA2134082733 := sorry

/-- rest 25/62：HOL idv `QITNPEA1 2 2 9063653052 A`（ineq.hl:845-862
make_F4/add_QITNPEA1 循环；PA21 `bank_QITNPEA1_2_2 = bank_QITNPEA1tmpl
2 2` / `proj_bank_QITNPEA1_2_2`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA1_2_2 : bank_QITNPEA1_2_2 := sorry

/-- rest 26/62：HOL idv `QITNPEA1 2 1 9063653052 A`（同循环；PA21
`bank_QITNPEA1_2_1` / `proj_bank_QITNPEA1_2_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA1_2_1 : bank_QITNPEA1_2_1 := sorry

/-- rest 27/62：HOL idv `QITNPEA1 2 0 9063653052 A`（同循环；PA21
`bank_QITNPEA1_2_0` / `proj_bank_QITNPEA1_2_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA1_2_0 : bank_QITNPEA1_2_0 := sorry

/-- rest 28/62：HOL idv `QITNPEA1 1 2 9063653052 A`（同循环；PA21
`bank_QITNPEA1_1_2` / `proj_bank_QITNPEA1_1_2`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA1_1_2 : bank_QITNPEA1_1_2 := sorry

/-- rest 29/62：HOL idv `QITNPEA1 1 1 9063653052 A`（同循环；PA21
`bank_QITNPEA1_1_1` / `proj_bank_QITNPEA1_1_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA1_1_1 : bank_QITNPEA1_1_1 := sorry

/-- rest 30/62：HOL idv `QITNPEA1 1 0 9063653052 A`（同循环；PA21
`bank_QITNPEA1_1_0` / `proj_bank_QITNPEA1_1_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA1_1_0 : bank_QITNPEA1_1_0 := sorry

/-- rest 31/62：HOL ineq entry `QITNPEA 9939613598`（ineq.hl:798，盒
[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]²；PA21
`bank_QITNPEA9939613598` / `proj_bank_QITNPEA9939613598`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestQITNPEA9939613598 : bank_QITNPEA9939613598 := sorry

/-- rest 32/62：HOL ineq entry `BIXPCGW 7274157868 a`（ineq.hl:776，盒同
rest 31；PA21 `bank_BIXPCGW7274157868a` /
`proj_bank_BIXPCGW7274157868a`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestBIXPCGW7274157868a : bank_BIXPCGW7274157868a := sorry

/-- rest 33/62：HOL ineq entry `BIXPCGW b`（ineq.hl:758，盒
[2hmin,2hplus]×[2,√8]²×[2,2hplus]×[2,√8]²；PA21 `bank_BIXPCGWb` /
`proj_bank_BIXPCGWb`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestBIXPCGWb : bank_BIXPCGWb := sorry

/-- rest 34/62：HOL ineq entry `BIXPCGW 1738910218 a2`（ineq.hl:739，盒
同 rest 33；PA21 `bank_BIXPCGW1738910218a2` /
`proj_bank_BIXPCGW1738910218a2`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestBIXPCGW1738910218a2 : bank_BIXPCGW1738910218a2 := sorry

/-- rest 35/62：HOL ineq entry `BIXPCGW 7080972881 a2`（ineq.hl:721，盒
[2hmin,2hplus]×[2hmin,√8]×[2,√8]⁴；PA21 `bank_BIXPCGW7080972881a2` /
`proj_bank_BIXPCGW7080972881a2`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestBIXPCGW7080972881a2 : bank_BIXPCGW7080972881a2 := sorry

/-- rest 36/62：HOL ineq entry `BIXPCGW 6652007036 a2`（ineq.hl:701，盒
[2hmin,2hplus]×[2,√8]⁵；PA21 `bank_BIXPCGW6652007036a2` /
`proj_bank_BIXPCGW6652007036a2`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestBIXPCGW6652007036a2 : bank_BIXPCGW6652007036a2 := sorry

/-- rest 37/62：HOL ineq entry `GLFVCVK4 2477216213 y4subcrit`
（ineq.hl:675，盒 [2hmin,2hplus]×[2hmin,√8]×[2,2hmin]⁴；PA21
`bank_GLFVCVK4y4subcrit` / `proj_bank_GLFVCVK4y4subcrit`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestGLFVCVK4y4subcrit : bank_GLFVCVK4y4subcrit := sorry

/-- rest 38/62：HOL ineq entry `GLFVCVK4 2477216213 y4supercrit`
（ineq.hl:649，盒 [2hmin,2hplus]×[2,2h0]×[2,2hmin]×[2hplus,√8]×
[2,2hmin]²；PA21 `bank_GLFVCVK4y4supercrit` /
`proj_bank_GLFVCVK4y4supercrit`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestGLFVCVK4y4supercrit : bank_GLFVCVK4y4supercrit := sorry

/-- rest 39/62：HOL ineq entry `GLFVCVK4 2477216213 y4crit`
（ineq.hl:623，盒 [2hmin,2hplus]×[2hmin,2hplus]×[2,2hmin]×
[2hmin,2hplus]×[2,2hmin]²；PA21 `bank_GLFVCVK4y4crit` /
`proj_bank_GLFVCVK4y4crit`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestGLFVCVK4y4crit : bank_GLFVCVK4y4crit := sorry

/-- rest 40/62：HOL ineq entry `GLFVCVK4a 8328676778`（ineq.hl:586，盒
[2hmin,2hplus]×[2,2hmin]²×[2hmin,2hplus]×[2,2hmin]²；PA21
`bank_GLFVCVK4a8328676778` / `proj_bank_GLFVCVK4a8328676778`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestGLFVCVK4a8328676778 : bank_GLFVCVK4a8328676778 := sorry

/-- rest 41/62：HOL ineq entry `GLFVCVK4 2477216213`（ineq.hl:559，盒
[2hmin,2hplus]×[2,√8]⁵；PA21 `bank_GLFVCVK4` / `proj_bank_GLFVCVK4`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestGLFVCVK4 : bank_GLFVCVK4 := sorry

/-- rest 42/62：HOL ineq entry `MKFKQWU halfwt`（ineq.hl:523，盒
[2hmin,2hplus]×[2hplus,√8]×[2,√8]×[2hmin,√8]×[2,√8]²；PA21
`bank_MKFKQWUhalfwt` / `proj_bank_MKFKQWUhalfwt`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestMKFKQWUhalfwt : bank_MKFKQWUhalfwt := sorry

/-- rest 43/62：HOL ineq entry `MKFKQWU`（ineq.hl:502，盒
[2hmin,2hplus]×[2hmin,√8]²×[2,√8]×[2hmin,√8]²；PA21 `bank_MKFKQWU` /
`proj_bank_MKFKQWU`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestMKFKQWU : bank_MKFKQWU := sorry

/-- rest 44/62：HOL idv `ZTGIJCF4 1 1 1 1 1821661595`（ineq.hl:486-499
make_F4 循环；PA21 `bank_ZTGIJCF4_1_1_1_1 = bank_ZTGIJCF4tmpl 1 1 1 1` /
`proj_bank_ZTGIJCF4_1_1_1_1`）。资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_1_1_1 : bank_ZTGIJCF4_1_1_1_1 := sorry

/-- rest 45/62：HOL idv `ZTGIJCF4 1 1 1 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_1_1_0` / `proj_bank_ZTGIJCF4_1_1_1_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_1_1_0 : bank_ZTGIJCF4_1_1_1_0 := sorry

/-- rest 46/62：HOL idv `ZTGIJCF4 1 1 0 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_1_0_1` / `proj_bank_ZTGIJCF4_1_1_0_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_1_0_1 : bank_ZTGIJCF4_1_1_0_1 := sorry

/-- rest 47/62：HOL idv `ZTGIJCF4 1 1 0 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_1_0_0` / `proj_bank_ZTGIJCF4_1_1_0_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_1_0_0 : bank_ZTGIJCF4_1_1_0_0 := sorry

/-- rest 48/62：HOL idv `ZTGIJCF4 1 0 1 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_0_1_1` / `proj_bank_ZTGIJCF4_1_0_1_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_0_1_1 : bank_ZTGIJCF4_1_0_1_1 := sorry

/-- rest 49/62：HOL idv `ZTGIJCF4 1 0 1 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_0_1_0` / `proj_bank_ZTGIJCF4_1_0_1_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_0_1_0 : bank_ZTGIJCF4_1_0_1_0 := sorry

/-- rest 50/62：HOL idv `ZTGIJCF4 1 0 0 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_0_0_1` / `proj_bank_ZTGIJCF4_1_0_0_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_0_0_1 : bank_ZTGIJCF4_1_0_0_1 := sorry

/-- rest 51/62：HOL idv `ZTGIJCF4 1 0 0 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_1_0_0_0` / `proj_bank_ZTGIJCF4_1_0_0_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_1_0_0_0 : bank_ZTGIJCF4_1_0_0_0 := sorry

/-- rest 52/62：HOL idv `ZTGIJCF4 0 1 1 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_1_1_1` / `proj_bank_ZTGIJCF4_0_1_1_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_1_1_1 : bank_ZTGIJCF4_0_1_1_1 := sorry

/-- rest 53/62：HOL idv `ZTGIJCF4 0 1 1 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_1_1_0` / `proj_bank_ZTGIJCF4_0_1_1_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_1_1_0 : bank_ZTGIJCF4_0_1_1_0 := sorry

/-- rest 54/62：HOL idv `ZTGIJCF4 0 1 0 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_1_0_1` / `proj_bank_ZTGIJCF4_0_1_0_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_1_0_1 : bank_ZTGIJCF4_0_1_0_1 := sorry

/-- rest 55/62：HOL idv `ZTGIJCF4 0 1 0 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_1_0_0` / `proj_bank_ZTGIJCF4_0_1_0_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_1_0_0 : bank_ZTGIJCF4_0_1_0_0 := sorry

/-- rest 56/62：HOL idv `ZTGIJCF4 0 0 1 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_0_1_1` / `proj_bank_ZTGIJCF4_0_0_1_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_0_1_1 : bank_ZTGIJCF4_0_0_1_1 := sorry

/-- rest 57/62：HOL idv `ZTGIJCF4 0 0 1 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_0_1_0` / `proj_bank_ZTGIJCF4_0_0_1_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_0_1_0 : bank_ZTGIJCF4_0_0_1_0 := sorry

/-- rest 58/62：HOL idv `ZTGIJCF4 0 0 0 1 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_0_0_1` / `proj_bank_ZTGIJCF4_0_0_0_1`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_0_0_1 : bank_ZTGIJCF4_0_0_0_1 := sorry

/-- rest 59/62：HOL idv `ZTGIJCF4 0 0 0 0 1821661595`（同循环；PA21
`bank_ZTGIJCF4_0_0_0_0` / `proj_bank_ZTGIJCF4_0_0_0_0`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestZTGIJCF4_0_0_0_0 : bank_ZTGIJCF4_0_0_0_0 := sorry

/-- rest 60/62：HOL ineq entry `ZTGIJCF0`（ineq.hl:446，1 变量盒 [1,1]，
5-叶以上聚簇常数核算 `5a + b·2π > 0`；PA21 `bank_ZTGIJCF0` /
`proj_bank_ZTGIJCF0`）。
本波真闭合：spine 常数（`aSpine5 = 0.0560305`、`bSpine5 = −0.0445813`）
+ `Real.pi_lt_d4`（π < 3.1416）夹逼，真余量 ≈3.9e-5。 -/
theorem nliRestZTGIJCF0 : bank_ZTGIJCF0 := by
  intro _d _hl _hh
  have hm : (0.0891626 : ℝ) * Real.pi < 0.0891626 * 3.1416 :=
    mul_lt_mul_of_pos_left Real.pi_lt_d4 (by norm_num)
  unfold aSpine5 bSpine5
  norm_num at hm ⊢
  linarith

/-- rest 61/62：HOL ineq entry `GCKBQEA`（ineq.hl:1352，盒
[2hmin,2hplus]×[2,√8]⁵；PA21 `bank_GCKBQEA` / `proj_bank_GCKBQEA`）。
资产状态：deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestGCKBQEA : bank_GCKBQEA := sorry

/-- rest 62/62：HOL ineq entry `RQWUDDU`（ineq.hl:1332，盒同 rest 61；
PA21 `bank_RQWUDDU` / `proj_bank_RQWUDDU`）。资产状态：
deferred-compute。
-- NEEDS: G4 证书发射 + 粘合入 §2a 查表（nli 28+127 接线主波）。 -/
theorem nliRestRQWUDDU : bank_RQWUDDU := sorry

/-- 中层骨架 1d 本体：62 条 rest 叶的显式合取装配（照 PA21
`pack_nonlinear_rest` 逐位对齐，位次 = IdLists 注册序；每枚组件 =
上方具名骨架件，与 PA21 62 枚 `proj_bank_*` 一一对应）。
-- NEEDS: 无独立债务——骨架债仅自上方 59 枚开放组件流入。 -/
theorem nliPackNonlinearRest : pack_nonlinear_rest :=
  ⟨nliRest6096597438b, nliRest6096597438a, nliRest1965189142a,
    nliRest1965189142x34, nliRestJSPEVYT, nliRestQITNPEA4003532128a,
    nliRestIXPOTPA, nliRestTXQTPVC, nliRestQITNPEA3725403817,
    nliRestQITNPEAv24003532128, nliRestPEMKWU, nliRestTEWNSCJ,
    nliRestQITNPEA5400790175b, nliRestQITNPEA5400790175a,
    nliRestQITNPEA3848804089, nliRestQITNPEA5814748276,
    nliRestQITNPEA6206775865, nliRestQITNPEA5653753305,
    nliRestBIXPCGW9455898160, nliRestFWGKMBZ, nliRestFHBVYXZb,
    nliRestFHBVYXZa, nliRestFHBVYXZv2a, nliRestQITNPEA2134082733,
    nliRestQITNPEA1_2_2, nliRestQITNPEA1_2_1, nliRestQITNPEA1_2_0,
    nliRestQITNPEA1_1_2, nliRestQITNPEA1_1_1, nliRestQITNPEA1_1_0,
    nliRestQITNPEA9939613598, nliRestBIXPCGW7274157868a, nliRestBIXPCGWb,
    nliRestBIXPCGW1738910218a2, nliRestBIXPCGW7080972881a2,
    nliRestBIXPCGW6652007036a2, nliRestGLFVCVK4y4subcrit,
    nliRestGLFVCVK4y4supercrit, nliRestGLFVCVK4y4crit,
    nliRestGLFVCVK4a8328676778, nliRestGLFVCVK4, nliRestMKFKQWUhalfwt,
    nliRestMKFKQWU, nliRestZTGIJCF4_1_1_1_1, nliRestZTGIJCF4_1_1_1_0,
    nliRestZTGIJCF4_1_1_0_1, nliRestZTGIJCF4_1_1_0_0,
    nliRestZTGIJCF4_1_0_1_1, nliRestZTGIJCF4_1_0_1_0,
    nliRestZTGIJCF4_1_0_0_1, nliRestZTGIJCF4_1_0_0_0,
    nliRestZTGIJCF4_0_1_1_1, nliRestZTGIJCF4_0_1_1_0,
    nliRestZTGIJCF4_0_1_0_1, nliRestZTGIJCF4_0_1_0_0,
    nliRestZTGIJCF4_0_0_1_1, nliRestZTGIJCF4_0_0_1_0,
    nliRestZTGIJCF4_0_0_0_1, nliRestZTGIJCF4_0_0_0_0, nliRestZTGIJCF0,
    nliRestGCKBQEA, nliRestRQWUDDU⟩

/-! **A11 车道记账（2026-10-08，纯注释块，骨架代码逐字零改动）**：上游 PA21
的 GIANT 已诚实收窄——`pack_nonlinear_rest` 的 def 体从 unknown-Prop
（`:= sorry`，语句本身未定形）换成 62 条显式盒式 `bank_*` 合取（PA21
"bank rest" 节；字面 40 条直录 ineq.hl，行号经 ineqs.json 交叉验证；生成
22 条按 make_F4 / add_QITNPEA1 循环模板参数化；QITNPEA1 模板残段
`// + &m *beta_bump_lb` 按 ineq.hl:855 doc 注记「Removed beta_bump_lb」
转录并登记 registered reconciliation）。效果链（`#print axioms` 实证）：
PA21 侧 `pack_nonlinear_rest` / `pack_nonlinear_non_ox3q1h` / 三枚
`proj_*_bank` / `tsk_hyp` = 标准三公理零 sorryAx；本节 1a-1d 四骨架件的
陈述自此全部 pin 死在显式盒式上。
-- NEEDS（重记账）: ①81 条逐条证书债务不变（1a 七条 + 1b 十条 + 1c 两条
+ 1d 六十二条；GRKIBMP B V2 属 16 条真残余清单）；②在库两案粘合接线：
`bank_QITNPEA3725403817`（内核闭合 2026-09-18）与 `bank_1965189142x34`
（Cases.C1965189142x34）→ §2a 查表（量产波）；③`nliPackNonlinearNonOx3q1h`
（骨架 1）的 sorryAx 仍来自四骨架件的 sorry 体——证书灌装波按件转真。 -/

/-- 中层骨架 1：HOL `pack_nonlinear_non_ox3q1h`（merge_ineq.hl:118-122）分量
本体 = 四切片组骨架件的显式装配（**真推导**，无独立债务；对照 PA21:403-405
def 的四个合取项）。 -/
theorem nliPackNonlinearNonOx3q1h : pack_nonlinear_non_ox3q1h :=
  ⟨nliCell3Bank, nliTskBank, nliGrkBank, nliPackNonlinearRest⟩

/-! #### 分量 2/6 `ox3q1hP25`（230 条 = ineqdata3q1h.hl 46 record × 5 支） -/

/-- 中层骨架 2：HOL `ox3q1h`（Oxl_def.hl；cc_v11 模型 4-基数 quarter case 的
证书不等式库）接口分量本体。
资产状态：**真缺口（语句级）**——Lean 对应物 `ox3q1hP25`（PackingAuto25.lean:89）
本体即 `sorry` 型 opaque def（原注 `NEEDS: exact Oxl_def.hl body`）。
-- NEEDS: ①Oxl_def.hl 本体移植（P6-B 保真审补录）；②与注册表侧骨架
`nliOx3q1hIds` 的定义级桥（清单常量代入 + 查表语义，量产接线波）。 -/
theorem nliOx3q1h : ox3q1hP25 := sorry

/-- 中层骨架 2'：ox3q1h 注册表侧（merge_ineq.hl:78-92 清单，n 主 i 次序
230 条，IdLists.lean:131-361）。
资产状态：deferred-compute（230 条逐条证书）+ **退化防线**——§2a 查表
表外回落 `True`，本骨架**不得**经回落分支平凡闭合（IdLists.lean:699
else-True 静默退化警告），须逐条接线后闭合。
-- NEEDS: 230 条逐条 ineq.hl 字面展开 + G4 证书 + 查表扩表。 -/
theorem nliOx3q1hIds : AllCertified ox3q1hIds := sorry

/-! #### 分量 3/6 `main_nonlinear_terminal_v11`（109 条 Main_estimate 标签；
993 条主体） -/

/-- 中层骨架 3：HOL `main_nonlinear_terminal_v11`（terminal.hl:24-44；
LocalAuto1.lean:975 `sorry` 型 opaque def）接口分量本体。
可见盒形锚 = `LocalAnchors.MainNonlinearTerminalV11`（`2 ≤ y1..y3 ≤ 2*h0 ∧
cstab ≤ y4 ≤ 3.915 ∧ y5 = y6 = 2`）；消费链 `JEJTVGB_p16` →
`lp_main_estimate`（LocalAuto16.lean:180-195）已就位。
资产状态：**真缺口（语句级）** + deferred-compute（证书级）——155 定义
闭包 B=112/124 为展开式资产。
-- NEEDS: ①terminal.hl 本体按 109 条清单展开（取代 LA1 opaque def）；
②109 条逐条证书（`4717061266` 在库 Cases.C4717061266，补粘合）。 -/
theorem nliMainNonlinearTerminalV11 : main_nonlinear_terminal_v11 := sorry

/-- 中层骨架 3'：Main_estimate 注册表侧（terminal.hl:24-44 清单，109 条，
IdLists.lean:368-477；含 4680581274 delta 族、7550003505 全 5³ 族、
9563139965 d/e/f）。
资产状态：deferred-compute + 退化防线（同 2'：不得经回落分支平凡闭合）。
-- NEEDS: 109 条逐条接线 + 证书；在库 `4717061266` 优先粘合。 -/
theorem nliMainNonlinearTerminalV11Ids : AllCertified mainNonlinearTerminalV11Ids := sorry

/-! #### 分量 4/6 `LpIneqs`（127 条；the_main_statement.hl:29-45） -/

/-- 中层骨架 4：HOL `lp_ineqs` 接口分量的当前形态 `AllCertified idsLpIneqs`
（`idsLpIneqs = []`，§2a 占位清单）。资产状态：**占位空洞**——清单为空使
本件当前空洞地成立；真化 = 把 IdLists.lean `lpIneqsIds`（127 条）代入
`idsLpIneqs` 后由骨架 4' 承接。
退化防线：**不得**利用 `idsLpIneqs = []` 或查表回落分支平凡闭合（两者皆是
IdLists.lean:699 else-True 静默退化的变体；接线落地方可闭合）。
-- NEEDS: `idsLpIneqs := lpIneqsIds` 接线（随查表量产波）。 -/
theorem nliLpIneqs : LpIneqs := sorry

/-- 中层骨架 4'：lp_ineqs 注册表侧（Lp/Tablelp/Lp_aux 标签 + `"6170936724"`
特例、剔除 deprecated_quads，127 条，IdLists.lean:484-611）。
资产状态：混合——在库 G4 证书 `3253650737` / `2570626711` / `5490182221`；
试点案 `3397113841`（IneqPilot，端到端闭合、已入 §2a 查表）的**分量归属
待对账**（IneqPilot 注记其 HOL 标签 Xconvert/Lp_aux/Tablelp 属 lp_ineqs，
但该 10 位键不在生成清单 `lpIneqsIds` 中——gen_idlists.py 口径 vs 试点
注记的分歧）。
-- NEEDS: 127 条逐条接线 + 证书；3397113841 归属对账；清单内多数条目归
92 prep 家族重做口径。 -/
theorem nliLpIneqsIds : AllCertified lpIneqsIds := sorry

/-! #### 分量 5/6 `PackIneqDefA`（5 条；YSSKQOY.hl:24-28） -/

/-- 中层骨架 5：HOL `pack_ineq_def_a` 接口分量的当前形态（§2a `:= True`
占位；`fcdjdot`/`textCapstone` 的前提件）。真化 = `packIneqDefAIds` 代入 +
查表接线（同分量 4 形）。
退化防线：**不得**经占位 `True` 平凡闭合。
-- NEEDS: 语义真化（`PLACEHOLDER(P6-E)` → 注册表折算）。 -/
theorem nliPackIneqDefA : PackIneqDefA := sorry

/-- 中层骨架 5'：pack_ineq_def_a 注册表侧（YSSKQOY.hl:24-28，Flypaper ∩
{UKBRPFE,WAZLDCD,BIEFJHU} ≠ ∅，5 条，IdLists.lean:618-623）。
资产状态：混合——`1965189142 34` 证书在库（Cases.C1965189142x34），其余
deferred-compute。
-- NEEDS: 5 条逐条接线 + 证书；C1965189142x34 补粘合引理。 -/
theorem nliPackIneqDefAIds : AllCertified packIneqDefAIds := sorry

/-! #### 分量 6/6 `KcblrqcIneqDef`（28 条；tame_lemmas-compiled.hl:34-46） -/

/-- 中层骨架 6：HOL `kcblrqc_ineq_def` 接口分量的当前形态（§2a `:= True`
占位；`mqmsmab`/`textCapstone` 的前提件）。真化同分量 5。
退化防线：**不得**经占位 `True` 平凡闭合。
-- NEEDS: 语义真化（无既有 Lean 对应物，新造注册表折算）。 -/
theorem nliKcblrqcIneqDef : KcblrqcIneqDef := sorry

/-- 中层骨架 6'：kcblrqc_ineq_def 注册表侧（tame_lemmas-compiled.hl:34-46，
Flypaper ∩ {KCBLRQC} ∪ extra_ids、剔除 deprecated_quads，28 条，
IdLists.lean:630-658）。
资产状态：混合——`3253650737` / `5490182221` / `2570626711` 三条证书在库，
其余 deferred-compute/残余清单。
-- NEEDS: 28 条逐条接线 + 证书；KCBLRQC 消费链（`mqmsmab` 填实）所需最小
闭合集待定级。 -/
theorem nliKcblrqcIneqDefIds : AllCertified kcblrqcIneqDefIds := sorry

/-- **会师点（自上而下 ↔ 自下而上第一例）**：§2a 查表键 `"3397113841"` 的
非空洞闭合——接口语义自此含一个由 G4 内核证书（`C3397113841_pos`，1504 叶
bb_arb）+ 粘合引理支撑的真条目（`#print axioms` = 标准三公理）。后续
自下而上波逐键扩表后，本形即量产样板。 -/
theorem certifiedIneqHoldsPilotCase : CertifiedIneqHolds "3397113841" :=
  certifiedIneqHolds_pilot_holds "3397113841"

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

/-- HOL `opposite_hypermap`（tame_defs.hl:185）。四个 proof 字段为置换代数
（**已闭合 2026-09-21 填证波**）：复合仍 permutes（`PermutesOn.mul`）、symm 仍
permutes（`PermutesOn.symm`）、结合律 + 逆元消去（`mul_assoc`/`mul_inv_cancel`）。 -/
def oppositeHypermap (H : Hypermap α) : Hypermap α where
  darts := H.darts
  edgeMap := H.faceMap * H.nodeMap
  nodeMap := H.nodeMap.symm
  faceMap := H.faceMap.symm
  edgeMap_permutes := H.faceMap_permutes.mul H.nodeMap_permutes
  nodeMap_permutes := H.nodeMap_permutes.symm
  faceMap_permutes := H.faceMap_permutes.symm
  comp_eq_one := by
    have hnn : H.nodeMap * H.nodeMap.symm = 1 := mul_inv_cancel H.nodeMap
    have hff : H.faceMap * H.faceMap.symm = 1 := mul_inv_cancel H.faceMap
    rw [mul_assoc H.faceMap H.nodeMap H.nodeMap.symm, hnn, mul_one, hff]

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

/-! ### 2c. TameSpine 接口占位（capstone 消费链；`contraveningFan` 已真化
2026-09-24，其余为骨架 sorry） -/

/-- **接口 → 真证明（2026-09-24 接线波 T5）**：HOL `CONTRAVENING_FAN`
（tame_general.hl:247-259）——contravening 给出 fan 结构。证明内核为
CKQOWSA 章移植 `Kepler.Text.ContraFan`（18 条定理 16 条真证明；仅深几何核
LEMMA_3_POINTS_FINAL / LEMMA_4_POINTS_FINAL 为骨架，sorryAx 仅沿该双核
流动，与 `TameLp.contravening_fanTl` 同型）。三前提取自 `Contravening V`
合取项：`hpack = hc.1`、`hann = hc.2.1`、`hne` 由 card 合取项（13/14/15，
ncard > 0 排除空集）推出；`ContraFan.ESTD` 与本文件 §1 `ESTD` 同体 defeq，
`exact` 直接消化。 -/
theorem contraveningFan (V : Set V3) (hc : Contravening V) : FAN 0 V (ESTD V) := by
  have hne : V ≠ ∅ := by
    have hcard : V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := hc.2.2.2.2.1
    rintro rfl
    simp at hcard
  exact ContraFan.contraveningFanTl V hc.1 hc.2.1 hne

/-! #### 2c' MQMSMAB 终接线桥层（2026-10-13 A10 第四波；scout §4 B3/B4 规格）

消费 `Kepler.Text.TameLp.MQMSMAB`（hypermapOfFanTl 版帽石，commit 67f65438），
经 B4 十二短引理换实例（`dartDecEq2` → 裸 `instDecidableEqProd`，§0b congr
家族 + 字段函数相等搬运）+ B3 语义桥（TameLp 十二合取 → §2b orbitSet 版十二
合取；轨道 `orbitSet` ≡ `Hypermap.orbitMap` 定义等价、`setSumSpec` ≡
`setSum`、`dTame`/`bTame`/`tgt` 表值同体，唯一非等价项 `Adm3` 尾以 `True`
占位支承接）。装配体 `mqmsmabWired` 即 `mqmsmab` 证明体的备件；`mqmsmab`
当前唯一前提缺口 = `KcblrqcIneqDef` 占位统一（STATEMENT-FIX 提案 SF-39，
`docs/statement-fix-proposals.md` 待批）。 -/

/-- B4-1a plain 换实例（§0b 字段函数相等搬运；TameLp §0b `edgeMapTl_eq`
rfl 桥为同型先证）。 -/
private theorem b4_plain (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @Hypermap.Plain (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @Hypermap.Plain (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := by
  show (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) *
    (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan)) = 1
  rw [← TameLp.edgeMapTl_eq]
  exact h

/-- B4-1 tame_1 换实例（plain 走字段搬运，planar 走 §0b `Planar_congr_inst`）；
其余合取项对 `DecidableEq` 实例不敏感（字段投影不用实例），定义等价直传。 -/
private theorem b4_tame1 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame1 (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame1 (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) :=
  ⟨b4_plain V E hfan h.1,
    (TameLp.Planar_congr_inst TameLp.dartsTl_eq TameLp.edgeMapTl_eq
      TameLp.nodeMapTl_eq TameLp.faceMapTl_eq).mp h.2⟩

/-- B4-2 tame_2 换实例（§0b `Connected_congr_inst`/`Simple_congr_inst`）。 -/
private theorem b4_tame2 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame2 (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame2 (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) :=
  ⟨(TameLp.Connected_congr_inst TameLp.dartsTl_eq TameLp.edgeMapTl_eq
      TameLp.nodeMapTl_eq TameLp.faceMapTl_eq).mp h.1,
    (TameLp.Simple_congr_inst TameLp.dartsTl_eq TameLp.edgeMapTl_eq
      TameLp.nodeMapTl_eq TameLp.faceMapTl_eq).mp h.2⟩

/-- B4-3 tame_3 换实例（定义等价直传）。 -/
private theorem b4_tame3 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame3 (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame3 (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-4 tame_4 换实例（定义等价直传）。 -/
private theorem b4_tame4 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame4 (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame4 (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-5 tame_5a 换实例（定义等价直传）。 -/
private theorem b4_tame5a (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame5a (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame5a (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-6 tame_8 换实例（定义等价直传）。 -/
private theorem b4_tame8 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame8 (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame8 (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-7 tame_9a 换实例（定义等价直传）。 -/
private theorem b4_tame9a (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame9a (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame9a (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-8 tame_10 换实例（定义等价直传）。 -/
private theorem b4_tame10 (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame10 (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame10 (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-9 tame_11a 换实例（定义等价直传）。 -/
private theorem b4_tame11a (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame11a (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame11a (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-10 tame_11b 换实例（定义等价直传）。 -/
private theorem b4_tame11b (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame11b (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame11b (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-11 tame_12o 换实例（定义等价直传）。 -/
private theorem b4_tame12o (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame12o (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame12o (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B4-12 tame_13a 换实例（定义等价直传）。 -/
private theorem b4_tame13a (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (h : @TameLp.Tame13a (V3 × V3) dartDecEq2 (TameLp.hypermapOfFanTl V E hfan)) :
    @TameLp.Tame13a (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan 0 V E hfan) := h

/-- B3：语义桥——TameLp 十二合取（`Hypermap.node/face` 轨道版）→ §2b 十二
合取（`orbitSet` 轨道版）。同一 H 同一实例，逐槽定义等价；`Adm3` 尾
（§2b `True` 占位较 TameLp 忠实原形弱）以平凡支承接，下游 A9 真化时同步。 -/
private theorem b3_tamePlanarHypermap {α : Type*} [DecidableEq α] {H : Hypermap α}
    (h : TameLp.TamePlanarHypermap H) : TamePlanarHypermap H := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
  obtain ⟨w, ha, hlt⟩ := h12
  obtain ⟨ha1, ha2, ha3⟩ := ha
  exact ⟨w, ⟨ha1, ha2, fun x _ _ => trivial⟩, hlt⟩

/-- MQMSMAB 终接线本体：消费 TameLp `hypermapOfFanTl` 版帽石 `MQMSMAB`
（commit 67f65438），经 B4 十二短引理换实例 + B3 语义桥收 §2b 裸版结论。
前提 `hkcblrqc` 取 TameLp 真切片——`KcblrqcIneqDef` 占位统一（SF-39）
批准后，`mqmsmab` 证明体即 `mqmsmabWired V hkcblrqc hmain hfan hc` 一行。 -/
theorem mqmsmabWired (V : Set V3) (hkcblrqc : TameLp.KcblrqcIneqDef)
    (hmain : lp_main_estimate) (hfan : FAN 0 V (ESTD V)) (hc : Contravening V) :
    TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfan) := by
  have htl := TameLp.MQMSMAB V hc hfan hmain hkcblrqc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := htl
  have htc : TameLp.TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfan) :=
    ⟨b4_tame1 V (ESTD V) hfan h1, b4_tame2 V (ESTD V) hfan h2,
      b4_tame3 V (ESTD V) hfan h3, b4_tame4 V (ESTD V) hfan h4,
      b4_tame5a V (ESTD V) hfan h5, b4_tame8 V (ESTD V) hfan h6,
      b4_tame9a V (ESTD V) hfan h7, b4_tame10 V (ESTD V) hfan h8,
      b4_tame11a V (ESTD V) hfan h9, b4_tame11b V (ESTD V) hfan h10,
      b4_tame12o V (ESTD V) hfan h11, b4_tame13a V (ESTD V) hfan h12⟩
  exact b3_tamePlanarHypermap htc

/-- 接口占位：HOL `Mqmsmab.MQMSMAB`（tame_concl / MQMSMAB-compiled.hl；section
前提 `kcblrqc_ineq_def` ∧ `lp_main_estimate` 显式化）。
-- NEEDS（A10 第四波接线记账 2026-10-13）：证明体已备于本文件 §2c'
`mqmsmabWired`（B4 十二短引理换实例 + B3 语义桥全绿，探针/构建零错）。
唯一前提缺口 = `KcblrqcIneqDef`（本文件 `:= True` 占位 → `TameLp.KcblrqcIneqDef`
真切片）的统一裁决 = **SF-39**（`docs/statement-fix-proposals.md`，待批）。
SF-39 批准后本定理证明体一行替换为 `mqmsmabWired V hkcblrqc hmain hfan hc`，
textCapstone 消费链（:5263 调用点）随之转真（上游 TameLp 六枚占位件按
「消费含占位前提定理」惯例合法流动）。 -/
theorem mqmsmab (V : Set V3) (hkcblrqc : KcblrqcIneqDef) (hmain : lp_main_estimate)
    (hfan : FAN 0 V (ESTD V)) (hc : Contravening V) :
    TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfan) := by
  exact mqmsmabWired V hkcblrqc hmain hfan hc

/-- **接口 → 真证明（2026-09-21 填证波）**：HOL `tame_planar_hypermap_restricted`
（the_main_statement.hl:143-170；ssreflect/tms.hl 同名引理）。HOL 脚本四步：
① 定义展开；② `Hypermap.lemma_node_nondegenerate`（tame_11a ⟹ node 非退化）；
③ tame_9a ⟹ face 基数 ≥ 3；④ tame_8 ⟹ dart 非空（`face_collection H = ∅`
与 `3 ≤ number_of_faces` 矛盾）。Lean 镜像逐条同构：§2b 幂轨道
（`nodeOrbit`/`faceOrbit` = `orbitSet`）与 `Hypermap.orbitMap` 依
`Set.range`/`setOf` 定义可相互 defeq 折算；单点轨道用
`Hypermap.orbitMap_singleton_iff`；face 集空用 `setOfOrbits` 对空 dart 集
的坍缩。其余合取项（planar/plain/connected/simple/no-double-joins/edge-
nondegenerate）与 §2b 对应原语逐项 defeq 传递。 -/
theorem tamePlanarHypermapRestricted {α : Type*} [DecidableEq α] (H : Hypermap α)
    (ht : TamePlanarHypermap H) : H.IsRestricted := by
  obtain ⟨⟨hplain, hplanar⟩, ⟨hconn, hsimple⟩, h3, -, h5a, h8, h9a, -, h11a, -, -, -⟩ := ht
  refine ⟨?_, hplanar, hplain, hconn, hsimple, h5a, h3, ?_, ?_⟩
  · -- ④ tame_8 ⟹ dart 非空（HOL：face_collection = ∅ 与 3 ≤ number_of_faces 矛盾）
    intro hempty
    have hnf : H.numberOfFaces = (setOfOrbits H.darts H.faceMap).ncard := rfl
    have hfs : setOfOrbits H.darts H.faceMap = ∅ := by
      ext t
      simp [setOfOrbits, hempty]
    have h8' : 3 ≤ H.numberOfFaces := h8
    rw [hnf, hfs, Set.ncard_empty] at h8'
    omega
  · -- ② tame_11a ⟹ node 非退化（HOL lemma_node_nondegenerate）
    intro x hx hfix
    have hmem : 3 ≤ (orbitMap H.nodeMap x).ncard := h11a x hx
    have hnc : (orbitMap H.nodeMap x).ncard = 1 := by
      rw [(orbitMap_singleton_iff H.nodeMap x).mpr hfix, Set.ncard_singleton]
    rw [hnc] at hmem
    linarith
  · -- ③ tame_9a ⟹ face 基数 ≥ 3
    exact fun x hx => (h9a x hx).1

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

/-! 收获记录（elllnyz，2026-10-12 A7 填证 lane；原 2026-09-28 接口占位注记转此归档）：
HOL `Elllnyz.ELLLNYZ`（ELLLNYZ.hl:548-587）已收口，定理块依依赖序移至 §2c.4'
（本文件 `ell_isoOfHom`/`ell_reverseIso` 私件之后），陈述冻结逐字未动（块移动经
逐字加回豁免合法化，先例 = A5 波 hypermapOfFanNeg 同款）。实战分解：proper 支 =
`iso_fgraph` 的 is_pr_Iso 析取直接给面级 cong 匹配（`is_pr_Hom` 双向 + InjOn 折算成
`x.flatten` 上的单射），跨图 `n_list`/`f_list` 共轭走「y 侧包含面的 findFace 唯一性
+ cong 旋转搬面 + `la7_prevEl_map`/rotate 不变式」三步，替代 HOL 的
`CONG_hypermap_of_list` 字面超映射等式路线；improper 支 = 同一 proper 机器作用于
y' = `MAP REVERSE y`（`la7_goodList_reverse` 供 GoodList）+ REVERSE 共轭件
`ell_reverseIso`（ witnessing `nodeMap.symm`，燃料 = la7 face/node reverse 平移 +
hypermapOfList 的三条点态群律 N·F=E / F·E=N⁻¹ / F⁻¹·N⁻¹=E，由 edge 对合 +
comp_eq_one 纯置换代数导出）+ `hypermapIsoOpposite`/`oppositeHypermapOpposite`
（§2c.4 现成件，= HOL `iso_opposite_adjoint`）。**本节依赖新增
`import Kepler.Text.TameLp`**——原 playbook 挂账的编排者裁决项（import 方向），
lane 落地前完成三项审计：①传递闭包（TameLp 闭包 112 模块零触及 Kepler.Assembly
主模块，无环）；②命名空间（TameLp 全在 `Kepler.Text.TameLp` 内，不向本文件
open 的命名空间注入新名）；③全局泄漏（TameLp 零 `@[simp]`/instance/abbrev）。
回退方案 = 删 §2c.4' 节与移动后的定理块、原位恢复占位注记与接口骨架，其余零改动。
下游消费点 textCapstone :2150-2152 镜像分支不受影响（签名未动）。 -/

/-! （原接口占位文本，2026-09-28）：HOL `Elllnyz.ELLLNYZ`（ELLLNYZ.hl）——
镜像析取形，脊柱的图桥必须保持此形（phase6-spine.md §5）。
`hypermap_of_list y` 侧为存在性产出。theorem 本体现居 §2c.4'。 -/

/-! 收获记录（hypermapOfFanNeg，2026-10-12 A5 填证 lane；原 2026-09-28 NEEDS 注记
转此归档）：HOL ASFUTBF.hl:1007 `hypermap_of_fan_neg` 已收口。原四件套的实战分解：
①`azimMirror`（AzimSpec 级 `azimSpecNeg` + `on3Mirror`/`mirrorRep`，末两参换位形，
非 2π−azim）；②sigmaFan 镜像共轭 = `sigmaFanNeg`（本文件 §2c.8：σ'_(-v)(-w) =
−inv1_v w——核心是「前驱方位角极小性」descent（`azimPredLe`：σ-坏集有限 + 单射 +
逐点方位角严格递降 ⟹ 无周期点），单射化由 `unique_azim_point_fan` 闭合，无需
Localization 的 cyclic_set/ivs_azim_cycle 群论）；③setOfEdge 像集 = `setOfEdgeNegEq`
（A2 已备）；④hypermapOfFan 构造层 = §2c.8 的 dart 层求值件（`memDartsHypermapOfFan`
+ `evalEdge/evalNode/evalFace/evalNodeSymm/evalFaceSymm`，extendPerm/res 在 dart1 上
逐点展开）。同构映射不是 N=(--,--)：f(-v,-w) = (v, inv1_v w)（HOL 的 hyp_conj 复合
同款），三交换中 edge 侧纯代数、node 侧用 σ-共轭、face 侧用 inv1-共轭。定理本体
依依赖序移至 §2c.8（`surroundedNodeImageNeg` 之后），陈述冻结逐字未动。 -/

/-- 私件：`oppositeHypermap` 对合（HOL `Tame_opposite.opposite_opposite_hypermap_eq_hypermap`）。
数据字段：`edgeMap = faceMap.symm * nodeMap.symm` 由 `comp_eq_one`（E·N·F = 1 ⇒
E = (N·F)⁻¹ = F⁻¹·N⁻¹）给出；四个证明字段由命题的证明无关性 `rfl` 消去。 -/
private theorem oppositeHypermapOpposite {α : Type*} [DecidableEq α] (H : Hypermap α) :
    oppositeHypermap (oppositeHypermap H) = H := by
  have hE : H.edgeMap = H.faceMap.symm * H.nodeMap.symm := by
    have h1 : H.edgeMap * (H.nodeMap * H.faceMap) = 1 := by
      rw [← mul_assoc]; exact H.comp_eq_one
    calc H.edgeMap = (H.edgeMap⁻¹)⁻¹ := (inv_inv H.edgeMap).symm
      _ = (H.nodeMap * H.faceMap)⁻¹ := by rw [eq_inv_of_mul_eq_one_right h1]
      _ = H.faceMap⁻¹ * H.nodeMap⁻¹ := mul_inv_rev _ _
      _ = H.faceMap.symm * H.nodeMap.symm := by simp [Equiv.Perm.inv_def]
  simp only [oppositeHypermap]
  congr 1
  exact hE.symm

/-- 私件：同构经 `oppositeHypermap` 保持（同一 dart 双射 `f`，三映射交换式对
opp 的 E=F·N / N=N⁻¹ / F=F⁻¹ 逐条改写；N⁻¹/F⁻¹ 情形经
`Equiv.symm_apply_eq` + dart 集闭包 `PermutesOn.symm_apply_mem`）。 -/
private theorem hypermapIsoOpposite {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {H' : Hypermap β} (h : HypermapIso H H') :
    HypermapIso (oppositeHypermap H) (oppositeHypermap H') := by
  obtain ⟨f, hf, hfc⟩ := h
  refine ⟨f, hf, ?_⟩
  intro x hx
  obtain ⟨he, hn, hfa⟩ := hfc x hx
  have hxN : H.nodeMap x ∈ H.darts := H.nodeMap_permutes.apply_mem hx
  obtain ⟨_, _, hfaN⟩ := hfc (H.nodeMap x) hxN
  have hx' : H.nodeMap.symm x ∈ H.darts := H.nodeMap_permutes.symm_apply_mem hx
  have hx'' : H.faceMap.symm x ∈ H.darts := H.faceMap_permutes.symm_apply_mem hx
  obtain ⟨_, hn2, _⟩ := hfc (H.nodeMap.symm x) hx'
  obtain ⟨_, _, hfa2⟩ := hfc (H.faceMap.symm x) hx''
  refine ⟨?_, ?_, ?_⟩
  · show (H'.faceMap * H'.nodeMap) (f x) = f ((H.faceMap * H.nodeMap) x)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hn, hfaN]
  · show H'.nodeMap.symm (f x) = f (H.nodeMap.symm x)
    have h1 : f x = H'.nodeMap (f (H.nodeMap.symm x)) := by
      rw [hn2]; simp
    exact (Equiv.symm_apply_eq H'.nodeMap).mpr h1
  · show H'.faceMap.symm (f x) = f (H.faceMap.symm x)
    have h1 : f x = H'.faceMap (f (H.faceMap.symm x)) := by
      rw [hfa2]; simp
    exact (Equiv.symm_apply_eq H'.faceMap).mpr h1

/-- 接口占位：HOL `Asfutbf.iso_opposite_eq`（ASFUTBF.hl）。 -/
theorem isoOppositeEq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Hypermap α) (H' : Hypermap β) :
    HypermapIso H H' ↔ HypermapIso (oppositeHypermap H) (oppositeHypermap H') := by
  constructor
  · exact hypermapIsoOpposite
  · intro h
    have h2 : HypermapIso (oppositeHypermap (oppositeHypermap H))
        (oppositeHypermap (oppositeHypermap H')) := hypermapIsoOpposite h
    rw [oppositeHypermapOpposite, oppositeHypermapOpposite] at h2
    exact h2

/-! ### 2c.4' ELLLNYZ 镜像析取 ∃-侧 kit（2026-10-12 A7 填证 lane）

**本节依赖 `import Kepler.Text.TameLp`**（P6-C 构造层 `hypermapOfList` 所在）。
import 方向原为 playbook 挂账的编排者裁决项（"Assembly import TameLp 前须核
TameLp 闭包"）；本 lane 落地前完成三项审计：①传递闭包检查（TameLp 闭包 112 模块
零个触及 `Kepler.Assembly` 主模块，无环）；②命名空间审计（TameLp 全文件位于
`namespace Kepler.Text.TameLp`，不向本文件 open 的 `Kepler.Text`/`Kepler.Text.Fan`/
`Kepler.Graphs` 注入任何新名）；③全局泄漏审计（TameLp 零 `@[simp]`、零 instance、
零 abbrev）。若编排者裁决回退此 import，删除本节与移动后的 `elllnyz` 定理块、
原位恢复收获注记即可，其余文件零改动。

对照 HOL ELLLNYZ.hl:548-587（`ELLLNYZ`）：陈述的 ∃-侧 = `hypermap_of_list y` 的
构造 + iso 析取。HOL 的 iso 函数是面级 cong 类匹配下的 pair-lift `φ̂ d = (φ d.1, φ d.2)`；
本 kit 的核心 = `ell_isoOfHom`（跨图 findFace 唯一性论证，替代 HOL 的
`CONG_hypermap_of_list` 字面超映射等式——Lean 侧 `hypermapOfList` 构造带
`GoodList` 证明字段，字面等式路线需再走一遍 rotate 运输，不划算）。 -/

/-- `List.rotate 1` 的 drop/take 展开式（listPairs 的定义体形态）。 -/
private theorem ell_rotateOne (l : List ℕ) : l.rotate 1 = l.drop 1 ++ l.take 1 := by
  cases l with
  | nil => simp [List.rotate]
  | cons a t =>
    cases t with
    | nil => simp [List.rotate]
    | cons b s =>
      have hmod : 1 % (s.length + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [List.rotate, hmod]

/-- dart 的两个分量都落在 `L.flatten` 里（lift 单射性的燃料）。 -/
private theorem ell_mem_flatten_of_dart {L : fgraph ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d.1 ∈ L.flatten ∧ d.2 ∈ L.flatten := by
  unfold listOfDarts at hd
  obtain ⟨s, hs, hds⟩ := List.mem_flatten.mp hd
  obtain ⟨F, hF, hsF⟩ := List.mem_map.mp hs
  rw [← hsF] at hds
  have hdF : (d.1, d.2) ∈ listPairs F := hds
  obtain ⟨h1, h2⟩ := List.of_mem_zip hdF
  rw [← ell_rotateOne] at h2
  exact ⟨List.mem_flatten.mpr ⟨F, hF, h1⟩, List.mem_flatten.mpr ⟨F, hF, List.mem_rotate.mp h2⟩⟩

/-- pair-lift 在 dart 集上单射（φ 在 `L.flatten` 上单射时）。 -/
private theorem ell_lift_inj {φ : ℕ → ℕ} {L : fgraph ℕ}
    (hinj : ∀ u ∈ L.flatten, ∀ v ∈ L.flatten, φ u = φ v → u = v)
    {a b : ℕ × ℕ} (ha : a ∈ listOfDarts L) (hb : b ∈ listOfDarts L)
    (h : (φ a.1, φ a.2) = (φ b.1, φ b.2)) : a = b := by
  obtain ⟨ha1, ha2⟩ := ell_mem_flatten_of_dart ha
  obtain ⟨hb1, hb2⟩ := ell_mem_flatten_of_dart hb
  rw [Prod.mk.injEq] at h
  exact Prod.ext (hinj a.1 ha1 b.1 hb1 h.1) (hinj a.2 ha2 b.2 hb2 h.2)

/-- 面内的 pair 都是 dart。 -/
private theorem ell_listPairs_sub_darts {L : fgraph ℕ} {F : List ℕ} (hF : F ∈ L) :
    ∀ d ∈ listPairs F, d ∈ listOfDarts L := by
  intro d hd
  exact List.mem_flatten.mpr ⟨listPairs F, List.mem_map.mpr ⟨F, hF, rfl⟩, hd⟩

/-- `prevEl` 的旋转不变式（一般 n；`la7_prevEl_rotOne` 的归纳版）。 -/
private theorem ell_prevEl_rotate {l : List (ℕ × ℕ)} (hn : l.Nodup) (n : ℕ) {x : ℕ × ℕ}
    (hx : x ∈ l) : prevEl (l.rotate n) x = prevEl l x := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc prevEl (l.rotate (k + 1)) x
        = prevEl ((l.rotate k).rotate 1) x := by rw [List.rotate_rotate]
      _ = prevEl (l.rotate k) x :=
          TameLp.la7_prevEl_rotOne (List.nodup_rotate.mpr hn) (List.mem_rotate.mpr hx)
      _ = prevEl l x := ih

/-- `nextEl` 的旋转不变式（一般 n；`la7_nextEl_rotOne` 的归纳版）。 -/
private theorem ell_nextEl_rotate {l : List (ℕ × ℕ)} (hn : l.Nodup) (n : ℕ) (x : ℕ × ℕ) :
    nextEl (l.rotate n) x = nextEl l x := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc nextEl (l.rotate (k + 1)) x
        = nextEl ((l.rotate k).rotate 1) x := by rw [List.rotate_rotate]
      _ = nextEl (l.rotate k) x :=
          TameLp.la7_nextEl_rotOne (List.nodup_rotate.mpr hn) x
      _ = nextEl l x := ih

/-- `listPairs` 与 `map` 交换（HOL `list_pairs2` 的 map 形）。 -/
private theorem ell_listPairs_map (g : ℕ → ℕ) (l : List ℕ) :
    listPairs (l.map g) = (listPairs l).map (fun p : ℕ × ℕ => (g p.1, g p.2)) := by
  unfold listPairs
  rw [← List.map_drop, ← List.map_take, ← List.map_append, List.zip_map]
  rfl

/-- `listPairs` 与 `rotate` 交换（cong 搬面的钥匙）。 -/
private theorem ell_listPairs_rotate (l : List ℕ) (n : ℕ) :
    listPairs (l.rotate n) = (listPairs l).rotate n := by
  have hlen : l.length = (l.drop 1 ++ l.take 1).length := by simp; omega
  have hfold : listPairs l = List.zipWith Prod.mk l (l.drop 1 ++ l.take 1) :=
    List.zip_eq_zipWith
  calc listPairs (l.rotate n)
      = List.zipWith Prod.mk (l.rotate n) ((l.rotate n).drop 1 ++ (l.rotate n).take 1) :=
        List.zip_eq_zipWith
    _ = List.zipWith Prod.mk (l.rotate n) ((l.rotate n).rotate 1) := by
        rw [ell_rotateOne]
    _ = List.zipWith Prod.mk (l.rotate n) (l.rotate (n + 1)) := by rw [List.rotate_rotate]
    _ = List.zipWith Prod.mk (l.rotate n) ((l.rotate 1).rotate n) := by
        rw [List.rotate_rotate, Nat.add_comm]
    _ = (List.zipWith Prod.mk l (l.rotate 1)).rotate n :=
        (List.zipWith_rotate_distrib Prod.mk l (l.rotate 1) n
          (List.length_rotate l 1).symm).symm
    _ = (List.zipWith Prod.mk l (l.drop 1 ++ l.take 1)).rotate n := by rw [ell_rotateOne l]
    _ = (listPairs l).rotate n := by rw [hfold]

/-- `hypermapOfList` 的 edge 置换是对合（dart 上 eList 自逆、dart 外恒等）。 -/
private theorem ell_edgeMulSelf (L : fgraph ℕ) (hL : GoodList L) :
    (TameLp.hypermapOfList L hL).edgeMap * (TameLp.hypermapOfList L hL).edgeMap = 1 := by
  refine Equiv.Perm.ext fun d => ?_
  by_cases hd : d ∈ (TameLp.hypermapOfList L hL).darts
  · have hmem : eList d ∈ ((TameLp.hypermapOfList L hL).darts : Set (ℕ × ℕ)) := by
      rw [TameLp.darts_hypermapOfList]
      have hd' : d ∈ (↑(TameLp.hypermapOfList L hL).darts : Set (ℕ × ℕ)) := hd
      rw [TameLp.darts_hypermapOfList] at hd'
      exact hL.2.2 d hd'
    rw [Equiv.Perm.mul_apply, TameLp.edgeMap_hypermapOfList L hL hd,
      TameLp.edgeMap_hypermapOfList L hL hmem]
    rfl
  · rw [Equiv.Perm.mul_apply]
    rw [(TameLp.hypermapOfList L hL).edgeMap_permutes d hd]
    rw [(TameLp.hypermapOfList L hL).edgeMap_permutes d hd]
    rfl

/-- edge 对合超映射的群律一：`N·F = E`。 -/
private theorem ell_nf_eq_e {α : Type*} [DecidableEq α] (K : Hypermap α)
    (hE : K.edgeMap * K.edgeMap = 1) : K.nodeMap * K.faceMap = K.edgeMap := by
  have h1 : K.edgeMap * (K.nodeMap * K.faceMap) = 1 := by
    rw [← mul_assoc]; exact K.comp_eq_one
  rw [eq_inv_of_mul_eq_one_right h1]
  exact (eq_inv_of_mul_eq_one_right hE).symm

/-- edge 对合超映射的群律二：`F·E = N⁻¹`。 -/
private theorem ell_fe_eq_nsymm {α : Type*} [DecidableEq α] (K : Hypermap α)
    (hE : K.edgeMap * K.edgeMap = 1) : K.faceMap * K.edgeMap = K.nodeMap.symm := by
  have hNF := ell_nf_eq_e K hE
  have hF : K.faceMap = K.nodeMap⁻¹ * K.edgeMap := by
    calc K.faceMap = K.nodeMap⁻¹ * (K.nodeMap * K.faceMap) := (inv_mul_cancel_left _ _).symm
      _ = K.nodeMap⁻¹ * K.edgeMap := by rw [hNF]
  rw [hF, mul_assoc, hE, mul_one]
  rfl

/-- edge 对合超映射的群律三：`E·N = F⁻¹`。 -/
private theorem ell_en_eq_fsymm {α : Type*} [DecidableEq α] (K : Hypermap α)
    (hE : K.edgeMap * K.edgeMap = 1) : K.edgeMap * K.nodeMap = K.faceMap.symm := by
  have hNF := ell_nf_eq_e K hE
  have hN : K.nodeMap = K.edgeMap * K.faceMap⁻¹ := by
    calc K.nodeMap = K.nodeMap * K.faceMap * K.faceMap⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = K.edgeMap * K.faceMap⁻¹ := by rw [hNF]
  rw [hN, ← mul_assoc, hE, one_mul]
  rfl

/-- 主件：proper 同构（跨图 findFace 共轭）。
面级 cong 匹配（`hForw`/`hBack`）+ φ 在 `x.flatten` 上单射 ⟹
`Hx ≅ hypermapOfList y`，同构函数 = pair-lift `d ↦ (φ d.1, φ d.2)`。
node/face 交换的核心：y 侧包含面经 `findFaceDarts_ex_of_self` + `hBack` 写成
`(listPairs F).map lift` 的旋转，再经 `ell_prevEl_rotate` + `la7_prevEl_map`
两级搬运回到 x 侧（HOL `CONG_hypermap_of_list` 的 Lean 替代形态）。 -/
private theorem ell_isoOfHom (x y : fgraph ℕ) (φ : ℕ → ℕ)
    (hx : GoodList x) (hy : GoodList y)
    (hinj : ∀ u ∈ x.flatten, ∀ v ∈ x.flatten, φ u = φ v → u = v)
    (hForw : ∀ F ∈ x, ∃ F' ∈ y, cong (F.map φ) F')
    (hBack : ∀ F' ∈ y, ∃ F ∈ x, cong (F.map φ) F')
    (Hx : Hypermap (ℕ × ℕ)) (hHx : TameLp.IsHypermapOfListTl x Hx) :
    HypermapIso Hx (TameLp.hypermapOfList y hy) := by
  have hxMem : ∀ d ∈ Hx.darts, d ∈ listOfDarts x := by
    intro d hd
    have h : d ∈ (↑Hx.darts : Set (ℕ × ℕ)) := hd
    rw [hHx.darts_eq] at h
    exact h
  have hyMem : ∀ d ∈ listOfDarts y, d ∈ (TameLp.hypermapOfList y hy).darts := by
    intro d hd
    have h : d ∈ (↑(TameLp.hypermapOfList y hy).darts : Set (ℕ × ℕ)) := by
      rw [TameLp.darts_hypermapOfList]; exact hd
    exact h
  -- 面旋转搬运：cong (F.map φ) F' 给出 pair 列表的旋转等式
  have faceRot : ∀ F ∈ x, ∀ F' ∈ y, cong (F.map φ) F' →
      ∃ n, listPairs F' =
        ((listPairs F).map (fun d : ℕ × ℕ => (φ d.1, φ d.2))).rotate n := by
    intro F hF F' hF' hc
    obtain ⟨n, hn⟩ := hc
    refine ⟨n, ?_⟩
    rw [hn, ell_listPairs_rotate, ell_listPairs_map]
  -- x-dart 的像落在 y-dart 集
  have fwdMem : ∀ d ∈ listOfDarts x,
      (φ d.1, φ d.2) ∈ listOfDarts y := by
    intro d hd
    obtain ⟨F, hF, hdF⟩ : ∃ F ∈ x, d ∈ listPairs F := by
      obtain ⟨s, hs, hds⟩ := List.mem_flatten.mp hd
      obtain ⟨F, hF, hsF⟩ := List.mem_map.mp hs
      rw [← hsF] at hds
      exact ⟨F, hF, hds⟩
    obtain ⟨F', hF'y, hc⟩ := hForw F hF
    obtain ⟨n, hn⟩ := faceRot F hF F' hF'y hc
    have hm : (φ d.1, φ d.2) ∈ (listPairs F).map (fun d : ℕ × ℕ => (φ d.1, φ d.2)) :=
      List.mem_map.mpr ⟨d, hdF, rfl⟩
    have h2 : (φ d.1, φ d.2) ∈
        ((listPairs F).map (fun e : ℕ × ℕ => (φ e.1, φ e.2))).rotate n :=
      List.mem_rotate.mpr hm
    rw [← hn] at h2
    exact ell_listPairs_sub_darts hF'y _ h2
  -- y-dart 的原像存在
  have bwdMem : ∀ d' ∈ listOfDarts y, ∃ d ∈ listOfDarts x, (φ d.1, φ d.2) = d' := by
    intro d' hd'
    obtain ⟨F', hF'y, hdF'⟩ : ∃ F' ∈ y, d' ∈ listPairs F' := by
      obtain ⟨s, hs, hds⟩ := List.mem_flatten.mp hd'
      obtain ⟨F, hF, hsF⟩ := List.mem_map.mp hs
      rw [← hsF] at hds
      exact ⟨F, hF, hds⟩
    obtain ⟨F, hFx, hc⟩ := hBack F' hF'y
    obtain ⟨n, hn⟩ := faceRot F hFx F' hF'y hc
    rw [hn] at hdF'
    have hm : d' ∈ (listPairs F).map (fun d : ℕ × ℕ => (φ d.1, φ d.2)) :=
      List.mem_rotate.mp hdF'
    obtain ⟨p, hpf, hpl⟩ := List.mem_map.mp hm
    exact ⟨p, ell_listPairs_sub_darts hFx p hpf, hpl⟩
  refine ⟨(fun d => (φ d.1, φ d.2)), ?_, ?_⟩
  · rw [hHx.darts_eq, TameLp.darts_hypermapOfList]
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      exact fwdMem d hd
    · intro a ha b hb heq
      exact ell_lift_inj hinj ha hb heq
    · intro d' hd'
      obtain ⟨d, hd, hEq⟩ := bwdMem d' hd'
      exact ⟨d, hd, hEq⟩
  · intro d hd
    have hdL : d ∈ listOfDarts x := hxMem d hd
    have hdlift : (φ d.1, φ d.2) ∈ listOfDarts y := fwdMem d hdL
    have hself : (φ d.1, φ d.2) ∈ findFaceDarts y (φ d.1, φ d.2) :=
      (TameLp.dart_in_face y (φ d.1, φ d.2)).mpr hdlift
    obtain ⟨F', hF'y, heqF', hmemF'⟩ := TameLp.findFaceDarts_ex_of_self hself
    obtain ⟨F, hFx, hc⟩ := hBack F' hF'y
    obtain ⟨n, hn⟩ := faceRot F hFx F' hF'y hc
    rw [hn] at hmemF'
    have hliftmem : (φ d.1, φ d.2) ∈ (listPairs F).map (fun e : ℕ × ℕ => (φ e.1, φ e.2)) :=
      List.mem_rotate.mp hmemF'
    obtain ⟨p, hpf, hpl⟩ := List.mem_map.mp hliftmem
    have hpd : p = d := ell_lift_inj hinj (ell_listPairs_sub_darts hFx p hpf) hdL hpl
    have hdF : d ∈ listPairs F := by rw [← hpd]; exact hpf
    have hfdx : findFaceDarts x d = listPairs F := by
      have h0 := TameLp.findFaceDarts_eq_of_mem hx.1 hFx hpf
      rw [hpd] at h0
      exact h0
    have hinjF : ∀ u ∈ listPairs F, ∀ v ∈ listPairs F,
        (φ u.1, φ u.2) = (φ v.1, φ v.2) → u = v := fun u hu v hv huv =>
      ell_lift_inj hinj (ell_listPairs_sub_darts hFx u hu) (ell_listPairs_sub_darts hFx v hv) huv
    have hndFF : (listPairs F).Nodup :=
      TameLp.flatten_nodup_mem hx.1 (List.mem_map.mpr ⟨F, hFx, rfl⟩)
    have hnodM : ((listPairs F).map (fun e : ℕ × ℕ => (φ e.1, φ e.2))).Nodup :=
      TameLp.la7_nodup_map_on (l := listPairs F)
        (f := fun e : ℕ × ℕ => (φ e.1, φ e.2)) hinjF hndFF
    refine ⟨?_, ?_, ?_⟩
    · -- edge
      rw [TameLp.edgeMap_hypermapOfList y hy (hyMem _ hdlift), hHx.edgeMap_eq d hd]
      rfl
    · -- node
      rw [TameLp.nodeMap_hypermapOfList y hy (hyMem _ hdlift), hHx.nodeMap_eq d hd]
      show nList y (φ d.1, φ d.2) = (fun e : ℕ × ℕ => (φ e.1, φ e.2)) (nList x d)
      unfold nList
      rw [heqF', hn, ell_prevEl_rotate hnodM n hliftmem,
        TameLp.la7_prevEl_map (f := fun e : ℕ × ℕ => (φ e.1, φ e.2)) hinjF hdF, hfdx]
      rfl
    · -- face
      rw [TameLp.faceMap_hypermapOfList y hy (hyMem _ hdlift), hHx.faceMap_eq d hd]
      show fList y (φ d.1, φ d.2) = (fun e : ℕ × ℕ => (φ e.1, φ e.2)) (fList x d)
      unfold fList
      rw [heqF', hn, ell_nextEl_rotate hnodM n (φ d.1, φ d.2),
        TameLp.la7_nextEl_map (f := fun e : ℕ × ℕ => (φ e.1, φ e.2)) hinjF hdF, hfdx]

/-- 私件：`HypermapIso` 传递（组合两同构，见证 `g ∘ f`）。 -/
private theorem ell_isoTrans {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : Hypermap α} {B : Hypermap β} {C : Hypermap γ}
    (h1 : HypermapIso A B) (h2 : HypermapIso B C) : HypermapIso A C := by
  obtain ⟨f, hbij, hcom⟩ := h1
  obtain ⟨g, hbij', hcom'⟩ := h2
  refine ⟨g ∘ f, Set.BijOn.comp hbij' hbij, ?_⟩
  intro x hx
  obtain ⟨he, hn, hfa⟩ := hcom x hx
  have hfx : f x ∈ B.darts := hbij.1 hx
  obtain ⟨he', hn', hfa'⟩ := hcom' (f x) hfx
  refine ⟨?_, ?_, ?_⟩
  · show C.edgeMap (g (f x)) = g (f (A.edgeMap x))
    rw [he', he]
  · show C.nodeMap (g (f x)) = g (f (A.nodeMap x))
    rw [hn', hn]
  · show C.faceMap (g (f x)) = g (f (A.faceMap x))
    rw [hfa', hfa]

/-- 私件：REVERSE 共轭件——`H_y' ≅ opposite H_y`，见证 `nodeMap.symm`。
    点态群律 `N·F = E` / `F·E = N⁻¹` / `F⁻¹·N⁻¹ = E` + la7 face/node reverse 平移。 -/
private theorem ell_reverseIso (y : fgraph ℕ) (hy : GoodList y) :
    HypermapIso (TameLp.hypermapOfList (y.map List.reverse) (TameLp.la7_goodList_reverse y hy))
      (oppositeHypermap (TameLp.hypermapOfList y hy)) := by
  have hgood' : GoodList (y.map List.reverse) := TameLp.la7_goodList_reverse y hy
  have hE := ell_edgeMulSelf y hy
  have hNF : ∀ z : ℕ × ℕ, (TameLp.hypermapOfList y hy).nodeMap ((TameLp.hypermapOfList y hy).faceMap z)
      = (TameLp.hypermapOfList y hy).edgeMap z := by
    intro z
    have := congrArg (fun q : Equiv.Perm (ℕ × ℕ) => q z) (ell_nf_eq_e _ hE)
    rw [Equiv.Perm.mul_apply] at this
    exact this
  have hFE : ∀ z : ℕ × ℕ, (TameLp.hypermapOfList y hy).faceMap ((TameLp.hypermapOfList y hy).edgeMap z)
      = (TameLp.hypermapOfList y hy).nodeMap.symm z := by
    intro z
    have := congrArg (fun q : Equiv.Perm (ℕ × ℕ) => q z) (ell_fe_eq_nsymm _ hE)
    rw [Equiv.Perm.mul_apply] at this
    exact this
  have hFsN : ∀ z : ℕ × ℕ,
      (TameLp.hypermapOfList y hy).faceMap.symm ((TameLp.hypermapOfList y hy).nodeMap.symm z)
      = (TameLp.hypermapOfList y hy).edgeMap z := by
    intro z
    have h1 := ell_nf_eq_e (TameLp.hypermapOfList y hy) hE
    have hEE : (TameLp.hypermapOfList y hy).edgeMap = (TameLp.hypermapOfList y hy).edgeMap.symm :=
      eq_inv_of_mul_eq_one_right hE
    have h2 : (TameLp.hypermapOfList y hy).faceMap⁻¹ * (TameLp.hypermapOfList y hy).nodeMap⁻¹
        = (TameLp.hypermapOfList y hy).edgeMap := by
      calc (TameLp.hypermapOfList y hy).faceMap⁻¹ * (TameLp.hypermapOfList y hy).nodeMap⁻¹
          = ((TameLp.hypermapOfList y hy).nodeMap * (TameLp.hypermapOfList y hy).faceMap)⁻¹ :=
            (mul_inv_rev _ _).symm
        _ = (TameLp.hypermapOfList y hy).edgeMap⁻¹ := by rw [h1]
        _ = (TameLp.hypermapOfList y hy).edgeMap := hEE.symm
    have := congrArg (fun q : Equiv.Perm (ℕ × ℕ) => q z) h2
    rw [Equiv.Perm.mul_apply] at this
    exact this
  refine ⟨(TameLp.hypermapOfList y hy).nodeMap.symm, ?_, ?_⟩
  · rw [TameLp.darts_hypermapOfList_reverse y hy]
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      exact (TameLp.hypermapOfList y hy).nodeMap_permutes.symm_apply_mem hd
    · intro a _ b _ heq
      exact Equiv.injective _ heq
    · intro y' hy'
      exact ⟨(TameLp.hypermapOfList y hy).nodeMap y',
        (TameLp.hypermapOfList y hy).nodeMap_permutes.apply_mem hy',
        Equiv.symm_apply_apply _ _⟩
  · intro u hu
    have huD : u ∈ (↑(TameLp.hypermapOfList y hy).darts : Set (ℕ × ℕ)) := by
      rw [← TameLp.darts_hypermapOfList_reverse y hy]; exact hu
    have huL : u ∈ listOfDarts y := by
      rw [TameLp.darts_hypermapOfList] at huD; exact huD
    have hEu : eList u ∈ (↑(TameLp.hypermapOfList y hy).darts : Set (ℕ × ℕ)) := by
      rw [TameLp.darts_hypermapOfList]; exact hy.2.2 u huL
    have hspecE : (TameLp.hypermapOfList y hy).edgeMap u = eList u :=
      TameLp.edgeMap_hypermapOfList y hy huD
    have hspecEu : (TameLp.hypermapOfList y hy).edgeMap (eList u) = eList (eList u) :=
      TameLp.edgeMap_hypermapOfList y hy hEu
    have hspecNu : (TameLp.hypermapOfList y hy).nodeMap (eList u) = nList y (eList u) :=
      TameLp.nodeMap_hypermapOfList y hy hEu
    have hspecF : (TameLp.hypermapOfList y hy).faceMap u = fList y u :=
      TameLp.faceMap_hypermapOfList y hy huD
    have hspecE' : (TameLp.hypermapOfList (y.map List.reverse) hgood').edgeMap u = eList u :=
      TameLp.edgeMap_hypermapOfList (y.map List.reverse) hgood' hu
    have hspecN' : (TameLp.hypermapOfList (y.map List.reverse) hgood').nodeMap u
        = nList (y.map List.reverse) u :=
      TameLp.nodeMap_hypermapOfList (y.map List.reverse) hgood' hu
    have hspecF' : (TameLp.hypermapOfList (y.map List.reverse) hgood').faceMap u
        = fList (y.map List.reverse) u :=
      TameLp.faceMap_hypermapOfList (y.map List.reverse) hgood' hu
    have hFEu : (TameLp.hypermapOfList y hy).faceMap (eList u)
        = (TameLp.hypermapOfList y hy).nodeMap.symm u := by
      have h1 := hFE u
      rw [hspecE] at h1
      exact h1
    have hN'u : (TameLp.hypermapOfList (y.map List.reverse) hgood').nodeMap u
        = (TameLp.hypermapOfList y hy).nodeMap.symm u := by
      rw [show (TameLp.hypermapOfList (y.map List.reverse) hgood').nodeMap u
          = (TameLp.hypermapOfList (y.map List.reverse) hgood').nodeMap (eList (eList u)) from rfl,
        TameLp.nodeMap_hypermapOfList_reverse y hy (d := eList u) hEu]
      exact hFEu
    have hF'u : (TameLp.hypermapOfList (y.map List.reverse) hgood').faceMap u
        = (TameLp.hypermapOfList y hy).nodeMap (eList u) := by
      rw [show (TameLp.hypermapOfList (y.map List.reverse) hgood').faceMap u
          = (TameLp.hypermapOfList (y.map List.reverse) hgood').faceMap (eList (eList u)) from rfl,
        TameLp.faceMap_hypermapOfList_reverse y hy (d := eList u) hEu]
    have hF'u' : fList (y.map List.reverse) u = (TameLp.hypermapOfList y hy).nodeMap (eList u) :=
      hspecF'.symm.trans hF'u
    refine ⟨?_, ?_, ?_⟩
    · -- edge
      rw [show (oppositeHypermap (TameLp.hypermapOfList y hy)).edgeMap
          = (TameLp.hypermapOfList y hy).faceMap * (TameLp.hypermapOfList y hy).nodeMap from rfl,
        Equiv.Perm.mul_apply, Equiv.apply_symm_apply, hspecF, hspecE']
      rw [← hFE (eList u), hspecEu, ← hspecF]
      rfl
    · -- node
      rw [show (oppositeHypermap (TameLp.hypermapOfList y hy)).nodeMap
          = (TameLp.hypermapOfList y hy).nodeMap.symm from rfl, hN'u]
    · -- face
      rw [show (oppositeHypermap (TameLp.hypermapOfList y hy)).faceMap
          = (TameLp.hypermapOfList y hy).faceMap.symm from rfl, hspecF', hF'u',
        Equiv.symm_apply_apply, ← hspecE]
      exact hFsN u

/-- **接口 → 真证明（2026-10-12 A7 填证 lane）**：HOL `Elllnyz.ELLLNYZ`
（ELLLNYZ.hl:548-587）——镜像析取形，脊柱的图桥必须保持此形（phase6-spine.md §5）。
`hypermap_of_list y` 侧为存在性产出。HOL 两支：proper 支 =
`good_list_iso_fgraph_proper`（面 cong 类匹配 ⟹ 跨图 `n_list`/`f_list` 共轭，
本文件 `ell_isoOfHom`；Lean 侧无需 HOL 的 `CONG_hypermap_of_list` 字面等式——
同构见证 pair-lift 直接构造）；improper 支 = iso 换向 `MAP REVERSE y`
（`ell_isoOfHom` 作用于 y'）+ `hypermap_of_list_reverse` 的 eList-共轭语义
（本文件 `ell_reverseIso`：REVERSE 束 + 三条点态群律）+
`iso_opposite_adjoint`（= `hypermapIsoOpposite` + `oppositeHypermapOpposite`，
均为本文件 §2c.4 件）。 -/
theorem elllnyz (x y : fgraph ℕ) (hx : GoodList x) (hy : GoodList y)
    (hiso : iso_fgraph x y) (Hx : Hypermap (ℕ × ℕ)) (hHx : IsHypermapOfList x Hx) :
    ∃ Hy : Hypermap (ℕ × ℕ), IsHypermapOfList y Hy ∧
      (HypermapIso Hx Hy ∨ HypermapIso (oppositeHypermap Hx) Hy) := by
  obtain ⟨φ, hφ⟩ := hiso
  unfold is_iso is_Iso at hφ
  rcases hφ with hpr | himp
  · -- proper 支
    obtain ⟨hhom, hinjOn⟩ := hpr
    have hflat : (⋃ F ∈ {F | F ∈ x}, {v | v ∈ F}) = {u | u ∈ x.flatten} := by
      ext u
      constructor
      · intro hu
        obtain ⟨F, hFx, huF⟩ := Set.mem_iUnion₂.mp hu
        exact List.mem_flatten.mpr ⟨F, hFx, huF⟩
      · intro hu
        obtain ⟨F, hFx, huF⟩ := List.mem_flatten.mp hu
        exact Set.mem_iUnion₂.mpr ⟨F, hFx, huF⟩
    have hinj : ∀ u ∈ x.flatten, ∀ v ∈ x.flatten, φ u = φ v → u = v := by
      intro u hu v hv huv
      exact hinjOn (by rw [hflat]; exact hu) (by rw [hflat]; exact hv) huv
    refine ⟨TameLp.hypermapOfList y hy,
      ⟨(TameLp.hypermapOfList_isHypermapOfListTl y hy).darts_eq,
        (TameLp.hypermapOfList_isHypermapOfListTl y hy).edgeMap_eq,
        (TameLp.hypermapOfList_isHypermapOfListTl y hy).nodeMap_eq,
        (TameLp.hypermapOfList_isHypermapOfListTl y hy).faceMap_eq⟩,
      Or.inl (ell_isoOfHom x y φ hx hy hinj hhom.1 hhom.2 Hx
        ⟨hHx.darts_eq, hHx.edgeMap_eq, hHx.nodeMap_eq, hHx.faceMap_eq⟩)⟩
  · -- improper 支
    obtain ⟨hhom, hinjOn⟩ := himp
    rw [← set_map_reverse y] at hhom
    have hy' : GoodList (y.map List.reverse) := TameLp.la7_goodList_reverse y hy
    have hflat : (⋃ F ∈ {F | F ∈ x}, {v | v ∈ F}) = {u | u ∈ x.flatten} := by
      ext u
      constructor
      · intro hu
        obtain ⟨F, hFx, huF⟩ := Set.mem_iUnion₂.mp hu
        exact List.mem_flatten.mpr ⟨F, hFx, huF⟩
      · intro hu
        obtain ⟨F, hFx, huF⟩ := List.mem_flatten.mp hu
        exact Set.mem_iUnion₂.mpr ⟨F, hFx, huF⟩
    have hinj : ∀ u ∈ x.flatten, ∀ v ∈ x.flatten, φ u = φ v → u = v := by
      intro u hu v hv huv
      exact hinjOn (by rw [hflat]; exact hu) (by rw [hflat]; exact hv) huv
    have hHxTl : TameLp.IsHypermapOfListTl x Hx :=
      ⟨hHx.darts_eq, hHx.edgeMap_eq, hHx.nodeMap_eq, hHx.faceMap_eq⟩
    have comp := ell_isoTrans
      (ell_isoOfHom x (y.map List.reverse) φ hx hy' hinj hhom.1 hhom.2 Hx hHxTl)
      (ell_reverseIso y hy)
    have conv := hypermapIsoOpposite comp
    refine ⟨TameLp.hypermapOfList y hy,
      ⟨(TameLp.hypermapOfList_isHypermapOfListTl y hy).darts_eq,
        (TameLp.hypermapOfList_isHypermapOfListTl y hy).edgeMap_eq,
        (TameLp.hypermapOfList_isHypermapOfListTl y hy).nodeMap_eq,
        (TameLp.hypermapOfList_isHypermapOfListTl y hy).faceMap_eq⟩,
      Or.inr ?_⟩
    rw [oppositeHypermapOpposite] at conv
    exact conv

/-! ### 2c.5 `contravening_negative` 数据合取项私件（2026-09-28 脊柱 lane）

对照 HOL ASFUTBF.hl:182-298（`scriptL_negative` / `CARD_NEGATIVE` / `ESTD_NEG` /
`ECTC_NEG` / `packing_negative` / `ball_annulus_negative`，六件全真证明镜像）。
`contravening V` 的前五个数据合取项（packing / ball_annulus / scriptL / max /
card）由它们直接装配；第 6/7 合取项 `surroundedNode` 已于 2026-10-12 经下方
§2c.6/§2c.7 镜像 kit（`azimSpecNeg`/`azimMirror`/`setOfEdgeNegEq`/`dartOfFanNegMem`/
`azimDartNegLt`/`surroundedNodeImageNeg`）收口——`contraveningNegative` 全七合取
项真证明，零 sorry。-/

private theorem negInjOn (V : Set V3) : Set.InjOn (fun v : V3 => -v) V :=
  fun _ _ _ _ h => by simpa using congrArg Neg.neg h

private theorem negInjPre (V : Set V3) :
    Set.InjOn (fun v : V3 => -v) ((fun v : V3 => -v) ⁻¹' ((fun v : V3 => -v) '' V)) :=
  fun _ _ _ _ h => by simpa using congrArg Neg.neg h

/-- HOL `packing_negative`（ASFUTBF.hl:127）。 -/
private theorem packingNegative {V : Set V3} (h : Packing V) :
    Packing ((fun v => -v) '' V) := by
  intro u hu v hv hlt
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  rw [h v' hv' u' hu' (by simpa [dist_comm] using hlt)]

/-- HOL `ball_annulus_negative`（ASFUTBF.hl:139）：`ballAnnulus` 的 membership
只依赖范数，`‖-v‖ = ‖v‖`。 -/
private theorem ballAnnulusNegative {V : Set V3} (h : V ⊆ ballAnnulus) :
    ((fun v => -v) '' V) ⊆ ballAnnulus := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := hw
  have key : ∀ z : V3, z ∈ ballAnnulus ↔ -z ∈ ballAnnulus := by
    intro z
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, norm_neg]
  exact (key v).mp (h hv)

/-- HOL `CARD_NEGATIVE`（ASFUTBF.hl:204；`InjOn.ncard_image` 一步）。 -/
private theorem cardNegative (V : Set V3) :
    ((fun v => -v) '' V).ncard = V.ncard :=
  (negInjOn V).ncard_image

/-- HOL `ESTD_NEG`（ASFUTBF.hl:210）：`ESTD` 的边条件 `dist ≤ 2*h0` 在
`dist (-u) (-w) = dist u w` 下不变。 -/
private theorem estdNegative (V : Set V3) :
    ESTD ((fun v => -v) '' V) = (fun e => Set.image (fun v : V3 => -v) e) '' (ESTD V) := by
  ext e
  constructor
  · rintro ⟨u, w, rfl, hu, hw, hne, hdist⟩
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨{u', w'}, ⟨u', w', rfl, hu', hw', ?_, ?_⟩, ?_⟩
    · simpa using hne
    · simpa using hdist
    · simp
  · rintro ⟨e', he', rfl⟩
    obtain ⟨v, w, rfl, hv, hw, hne, hdist⟩ := he'
    refine ⟨-v, -w, by simp, ?_, ?_, ?_, ?_⟩
    · exact ⟨v, hv, rfl⟩
    · exact ⟨w, hw, rfl⟩
    · rintro hh
      exact hne (by simpa using hh)
    · simpa using hdist

/-- HOL `ECTC_NEG`（ASFUTBF.hl:240，同 `estdNegative`，边条件 `dist = 2`）。 -/
private theorem ectrNegative (V : Set V3) :
    ECTC ((fun v => -v) '' V) = (fun e => Set.image (fun v : V3 => -v) e) '' (ECTC V) := by
  ext e
  constructor
  · rintro ⟨u, w, rfl, hu, hw, hne, hdist⟩
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨{u', w'}, ⟨u', w', rfl, hu', hw', ?_, ?_⟩, ?_⟩
    · simpa using hne
    · simpa using hdist
    · simp
  · rintro ⟨e', he', rfl⟩
    obtain ⟨v, w, rfl, hv, hw, hne, hdist⟩ := he'
    refine ⟨-v, -w, by simp, ?_, ?_, ?_, ?_⟩
    · exact ⟨v, hv, rfl⟩
    · exact ⟨w, hw, rfl⟩
    · rintro hh
      exact hne (by simpa using hh)
    · simpa using hdist

/-- HOL `scriptL_negative`（ASFUTBF.hl:182）：求和经 `Finset.sum_image` 沿
`v ↦ -v` 换元（`‖-v‖ = ‖v‖`；无限集分支两侧同为约定 0）。 -/
private theorem scriptLNegative (V : Set V3) :
    scriptL ((fun v => -v) '' V) = scriptL V := by
  by_cases hV : V.Finite
  · have him : ((fun v => -v) '' V).Finite := hV.image (fun v : V3 => -v)
    have hinj' : Set.InjOn (fun v : V3 => -v) (↑hV.toFinset : Set V3) := by
      rw [Set.Finite.coe_toFinset hV]
      exact negInjOn V
    rw [scriptL, dif_pos him, Set.Finite.toFinset_image (fun v : V3 => -v) hV him,
      Finset.sum_image (f := fun v : V3 => lmfun (‖v‖ / 2)) hinj']
    rw [scriptL, dif_pos hV]
    exact Finset.sum_congr rfl fun v _ => by simp only [norm_neg]
  · have hnot : ¬((fun v => -v) '' V).Finite := by
      rintro him
      exact hV (Set.Finite.subset (him.preimage (negInjPre V)) (Set.subset_preimage_image _ V))
    rw [scriptL, dif_neg hnot, scriptL, dif_neg hV]

/-- `contravening` 第 4 合取项（max 条件）的负号版，由 `scriptLNegative` 传递。 -/
private theorem scriptLMaxNegative (V : Set V3)
    (hmax : ∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL V) :
    ∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL ((fun v => -v) '' V) :=
  fun W hW hsub => by
    rw [scriptLNegative V]
    exact hmax W hW hsub

/-- `Pi` 级点积负号桥（分量法，`mirrorRep`/`on3Mirror` 的地基）。 -/
private theorem dotPi_neg_left (f g : Fin 3 → ℝ) : (-f) ⬝ᵥ g = -(f ⬝ᵥ g) := by
  simp [dotProduct, Pi.neg_apply, Finset.sum_neg_distrib]

private theorem dotPi_neg_right (f g : Fin 3 → ℝ) : f ⬝ᵥ (-g) = -(f ⬝ᵥ g) := by
  simp [dotProduct, Pi.neg_apply, Finset.sum_neg_distrib, mul_comm]

private theorem dotPi_neg_neg (f g : Fin 3 → ℝ) : (-f) ⬝ᵥ (-g) = f ⬝ᵥ g := by
  simp [dotProduct, Pi.neg_apply, neg_mul, mul_neg]

private theorem cross_neg_left (f g : Fin 3 → ℝ) :
    crossProduct (-f) g = -(crossProduct f g) := by
  funext i
  fin_cases i <;> simp [cross_apply, Pi.neg_apply] <;> ring

/-- 镜像标架 `(-e1, e2, -e3)` 保持标准正交 + 右手性。 -/
private theorem on3Mirror {e1 e2 e3 : V3} (he : Orthonormal3 e1 e2 e3) :
    Orthonormal3 (-e1) e2 (-e3) := by
  obtain ⟨h11, h22, h33, h12, h13, h23, hc⟩ := he
  refine ⟨?_, h22, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_neg, h11]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_neg, h33]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_left, h12, neg_zero]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_neg, h13]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_right, h23, neg_zero]
  · have h1 : (((-e1 : V3) : Fin 3 → ℝ)) = -(e1 : Fin 3 → ℝ) := by simp
    have h2 : (((-e3 : V3) : Fin 3 → ℝ)) = -(e3 : Fin 3 → ℝ) := by simp
    rw [h1, cross_neg_left, h2, dotPi_neg_left, dotPi_neg_right, neg_neg]
    exact hc

/-- 共线三点集取反稳定性（原点固定）：`{0,a,b}` ↔ `{0,-a,-b}`。 -/
private theorem collinear3_zero_neg {a b : V3} :
    Collinear3 0 a b ↔ Collinear3 0 (-a) (-b) := by
  by_cases ha : a = 0
  · subst ha
    simp only [neg_zero]
    exact ⟨fun _ => collinear3_of_eq rfl, fun _ => collinear3_of_eq rfl⟩
  · rw [collinear3_iff_smul ha, collinear3_iff_smul (by simpa using ha)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hc' : (b : V3) = c • a := by simpa using hc
      rw [sub_zero, sub_zero, smul_neg, hc']
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hc' : (-b : V3) = c • (-a) := by simpa using hc
      rw [smul_neg] at hc'
      have h2 := congrArg Neg.neg hc'
      simpa using h2

/-- 镜像坐标传输：neg 取反把 `(cos β, sin β)` 分量变为 `(cos (-β), sin (-β))`。 -/
private theorem mirrorRep (e1 e2 u t : V3) (α β h : ℝ)
    (hrep : u - 0 = (α * Real.cos β) • (-e1) + (α * Real.sin β) • e2 + h • (t - 0)) :
    -u - 0 = (α * Real.cos (-β)) • e1 + (α * Real.sin (-β)) • e2 + h • (-t - 0) := by
  have hsub : (-u : V3) - 0 = -(u - 0) := by simp
  have key : (-u : V3) - 0
      = -((α * Real.cos β) • (-e1) + (α * Real.sin β) • e2 + h • (t - 0)) := by
    rw [hsub, hrep]
  rw [Real.cos_neg, Real.sin_neg, key]
  simp [neg_smul, smul_neg, mul_neg]
  abel
/-! NEEDS（2026-10-12 A2 填证 lane，已收口——本注记转收获记录）：
第 6/7 合取项（`surroundedNode` 镜像链）已全数落地，`contraveningNegative`
零 sorry。原蓝图 vs 实战的差异：
1. `azimMirror` 已落地（见 `azimMirror` docstring 的病理对策：Collinear3 侧条件
   必须 `intro`+`simpa` 传输而非 term 端 `.mp` 链；spec 的 θ 槽先 `obtain`/`rw`
   换成不透明变元再 `exact azim_eq_of_spec`）。前车"五构造全灭"的真凶是 ①——
   `fun hc => h1 ((collinear3_zero_neg).mp hc)` 的 `-(-v) ≡ v` 裸 isDefEq 下潜。
2. `setOfEdgeNegEq` / `dartOfFanNegMem` 落地（机械传输 + Graph-E 二元素恢复）。
3. 合取项收口无 σ 群论：σ_neg = −(σ-前驱)——前驱 `INVERSE1_SIGMA_FAN` 已证直接
   取用，σ' 的 ε-极小性经 `SIGMA_FAN`（Fan.lean，已证）逐点镜像夹出；fan 结构三件
   = `contraveningFan`（本文件）+ `ContraFan.contraveningFanTl`（负号像）+
   `CTVTAQA`（TopologyFan，FAN 对边集子集封闭）+ `ECTC ⊆ ESTD`。
   不需要 LA3 EXIS_SMALLEST_WITH_AZIM_ORD 重构（`SIGMA_FAN`/`exists_sigmaFan`
   已内含最小元论证）。
4. ECTC 版同构（`surroundedNodeImageNeg` 双用）；‖v‖ = 2 逃逸支 `norm_neg` 直传。
`hypermapOfFanNeg`（A5）与 tamespine-port-plan §4 B-D4 可直接复用 §2c.6/§2c.7
全套私件（同文件内可见；跨文件需去 private）。 -/

/-! ### 2c.6 镜像 kit（2026-10-12 A2 填证 lane）：azim 镜像与 neg''V 传输件

已证部分（`azimSpecNeg` 为核心件）；`azimMirror` 本体亦已落地
（收获记录见上方「已收口」注记：Collinear3 侧条件 `intro`+`simpa` 传输 +
`azimSpec_exists` 取不透明 θ 槽，默认心跳限额内 elaboration）。
【2026-10-12 A5 填证 lane 刷新】本 kit 已被 A5 `hypermapOfFanNeg` 消费收口
（见下方 §2c.8：σ-镜像共轭走 `azimPredLe` descent + `unique_azim_point_fan`
单射化，无需 cyclic_set 群论）；tamespine-port-plan §4 B-D4 仍可复用。-/

/-- HOL `AZIM_NEG`（YXIONXL2.hl:2014）的 AzimSpec 级形态：
`AzimSpec 0 v w2 w1 θ → AzimSpec 0 (-v) (-w1) (-w2) θ`。证明：解构源 spec
（高度 hh1/hh2 随交换对调），帧取镜像 `(-e1, e2, -e3)`（`on3Mirror` 保持
右手性），坐标恒等式 `mirrorRep` 传输，角度 `ψ' := -(ψ + θ)`。 -/
private theorem azimSpecNeg {v w1 w2 : V3} {θ : ℝ}
    (h1 : ¬ Collinear3 0 v w1) (h2 : ¬ Collinear3 0 v w2)
    (hsp : AzimSpec 0 v w2 w1 θ) : AzimSpec 0 (-v) (-w1) (-w2) θ := by
  obtain ⟨hb1, hb2, hh1, hh2, hbody⟩ := hsp
  refine ⟨hb1, hb2, hh2, hh1, fun e1 e2 e3 he hax hvn => ?_⟩
  have hdd : dist (-v) 0 = dist v 0 := by
    rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero, norm_neg]
  have h2v : (-v - 0 : V3) = dist v 0 • e3 := hax.trans (congrArg (fun d : ℝ => d • e3) hdd)
  have h3v : (-((-v) - 0 : V3)) = -(dist v 0 • e3) := congrArg Neg.neg h2v
  have h1v : (v - 0 : V3) = -((-v) - 0) := by simp
  have haxv : (v - 0 : V3) = dist v 0 • (-e3) :=
    h1v.trans (h3v.trans (smul_neg (dist v 0) e3).symm)
  have hv0 : v ≠ 0 := fun he => hvn (by simpa using he)
  obtain ⟨ψ, rA, rB, hw2rep, hw1rep, hposA', hposB'⟩ :=
    hbody (-e1) e2 (-e3) (on3Mirror he) haxv hv0
  have key1 : (-w1 - 0 : V3) = (rB * Real.cos (-(ψ + θ))) • e1
      + (rB * Real.sin (-(ψ + θ))) • e2 + hh2 • ((-v) - 0) :=
    mirrorRep e1 e2 w1 v rB (ψ + θ) hh2 hw1rep
  have key2 : (-w2 - 0 : V3) = (rA * Real.cos (-(ψ + θ) + θ)) • e1
      + (rA * Real.sin (-(ψ + θ) + θ)) • e2 + hh1 • ((-v) - 0) := by
    have hring : (-(ψ + θ) + θ : ℝ) = -ψ := by ring
    have eqA : (rA * Real.cos (-(ψ + θ) + θ) : ℝ) = rA * Real.cos (-ψ) :=
      congrArg (fun x : ℝ => rA * Real.cos x) hring
    have eqB : (rA * Real.sin (-(ψ + θ) + θ) : ℝ) = rA * Real.sin (-ψ) :=
      congrArg (fun x : ℝ => rA * Real.sin x) hring
    have hb : (-w2 - 0 : V3) = (rA * Real.cos (-ψ)) • e1
        + (rA * Real.sin (-ψ)) • e2 + hh1 • ((-v) - 0) :=
      mirrorRep e1 e2 w2 v rA ψ hh1 hw2rep
    rw [eqA, eqB]
    exact hb
  exact ⟨-(ψ + θ), rB, rA, key1, key2, hposB', hposA'⟩

/-- HOL `AZIM_NEG`（YXIONXL2.hl:2014）的 azim 级形态（末两参换位形）：
`azim 0 (-v) (-w1) (-w2) = azim 0 v w2 w1`。
**elaborator 病理对策（2026-10-12 实战收口，AzimSpec 类目标公共解）**：
①Collinear3 侧条件必须经 `intro hc; have := collinear3_zero_neg.mp hc; simpa using this`
传输——term 端写法 `fun hc => h1 ((collinear3_zero_neg).mp hc)` 的返回类型检查要把
`-(-v) ≡ v` 交给裸 isDefEq，会无限下潜（200k 心跳不减）；`simpa` 用 `neg_neg` 改写，
绕开裸 defeq。②先 `obtain θ₀`（`azimSpec_exists`）把 spec 的 θ 槽换成不透明变元并
`rw` 目标，再 `exact azim_eq_of_spec`——θ 槽全程不含 azim 应用项，统一全走句法匹配，
无需 Classical.epsilon_spec。 -/
private theorem azimMirror {v w1 w2 : V3} (h1 : ¬ Collinear3 0 v w1) (h2 : ¬ Collinear3 0 v w2) :
    azim 0 (-v) (-w1) (-w2) = azim 0 v w2 w1 := by
  have hn1 : ¬ Collinear3 0 (-v) (-w1) := by
    intro hc
    refine h1 ?_
    have h2' := collinear3_zero_neg.mp hc
    simpa using h2'
  have hn2 : ¬ Collinear3 0 (-v) (-w2) := by
    intro hc
    refine h2 ?_
    have h2' := collinear3_zero_neg.mp hc
    simpa using h2'
  obtain ⟨θ₀, hθ₀spec⟩ := azimSpec_exists h2 h1
  have hθ₀eq : azim 0 v w2 w1 = θ₀ := azim_eq_of_spec h2 h1 hθ₀spec
  rw [hθ₀eq]
  exact azim_eq_of_spec hn1 hn2 (azimSpecNeg h1 h2 hθ₀spec)

/-! ### 2c.7 neg''V 传输件与被包围 dart 界的镜像（2026-10-12 A2 填证 lane）

HOL ASFUTBF.hl:374-699 的 `azim_dart`-负号链（`azim_dart_neg` /
`AZIM_LT_PI_IMP_CARD_GT_1` / Localization.ivs 的角色全部内联）：
`setOfEdge`/`dartOfFan` 在 `V ↦ -V, E ↦ -''E` 下的传输 + 镜像侧 σ-极小性
（`SIGMA_FAN`）夹出被包围 dart 界。σ_neg = −(σ-前驱)（前车勘误：无需
Localization 群论；前驱取 `INVERSE1_SIGMA_FAN`，极小性逐点镜像）。-/

/-- neg 的单射（V3）。 -/
private theorem negInj3 {a b : V3} (h : -a = -b) : a = b := by
  simpa using congrArg Neg.neg h

/-- 二元集的交换。 -/
private theorem pairSetComm (p q : V3) : ({p, q} : Set V3) = {q, p} := by
  ext r
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- HOL `set_of_edge_neg`（ASFUTBF.hl 传输件）：`setOfEdge (-v) (-''V) (-''E)
= -''(setOfEdge v V E)`。 -/
private theorem setOfEdgeNegEq (v : V3) (V : Set V3) (E : Set (Set V3)) :
    setOfEdge (-v) ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)
      = (fun u : V3 => -u) '' (setOfEdge v V E) := by
  ext u
  simp only [setOfEdge, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨e, he, hEq⟩, ⟨z, hzV, hzu⟩⟩
    have hEq' : (fun x : V3 => -x) '' e = {-v, u} := hEq
    have hzu' : z = -u := by simpa using congrArg Neg.neg hzu
    have hpair : e = {v, -u} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hx
        have hx' : -x ∈ (fun y : V3 => -y) '' e := ⟨x, hx, rfl⟩
        rw [hEq'] at hx'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
        rcases hx' with hxc | hxc
        · exact Or.inl (negInj3 hxc)
        · exact Or.inr (by simpa using congrArg Neg.neg hxc)
      · rintro (hxv | hxu)
        · have hmem : -v ∈ (fun y : V3 => -y) '' e := by rw [hEq']; simp
          obtain ⟨y, hy, hxy⟩ := hmem
          rw [hxv, ← negInj3 hxy]
          exact hy
        · have hmem : u ∈ (fun y : V3 => -y) '' e := by rw [hEq']; simp
          obtain ⟨y, hy, hxy⟩ := hmem
          have hy' : y = -u := by simpa using congrArg Neg.neg hxy
          rw [hxu, ← hy']
          exact hy
    refine ⟨-u, ⟨?_, ?_⟩, ?_⟩
    · rw [hpair] at he
      exact he
    · rw [← hzu']
      exact hzV
    · simp
  · rintro ⟨z, ⟨hzE, hzV⟩, rfl⟩
    exact ⟨⟨{v, z}, hzE, by simp⟩, ⟨z, hzV, rfl⟩⟩

/-- HOL `dart_of_fan_neg` 的前向形：镜像侧 dart 必为 `-''dartOfFan V E` 的像。 -/
private theorem dartOfFanNegMem {V : Set V3} {E : Set (Set V3)} (hgraph : Graph E)
    {d : V3 × V3}
    (hd : d ∈ dartOfFan ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)) :
    ∃ a b : V3, d = (-a, -b) ∧ (a, b) ∈ dartOfFan V E := by
  have hpairEq : ∀ (x y : V3) (p : V3 × V3), p.1 = x → p.2 = y → p = (x, y) := by
    intro x y p hf hs
    obtain ⟨r, s⟩ := p
    have hf' : r = x := hf
    have hs' : s = y := hs
    rw [hf', hs']
  simp only [dartOfFan, dart1OfFan, Set.mem_union, Set.mem_setOf_eq] at hd
  rcases hd with ⟨hab, hdV, hsoe⟩ | hd1
  · rw [Set.mem_image] at hdV
    obtain ⟨v₀, hv₀V, hv₀d⟩ := hdV
    refine ⟨v₀, v₀, ?_, Or.inl ⟨rfl, hv₀V, ?_⟩⟩
    · have het : (d.1, d.2) = d := Prod.mk.eta
      rw [← het, show d.1 = -v₀ from hv₀d.symm, show d.2 = -v₀ from hab.symm.trans hv₀d.symm]
    · have h2 : setOfEdge (-v₀) ((fun u : V3 => -u) '' V)
          ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) = ∅ := by
        rw [show (-v₀ : V3) = d.1 from hv₀d]
        exact hsoe
      rw [setOfEdgeNegEq v₀ V E] at h2
      refine Set.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      have hxx : -x ∈ (fun y : V3 => -y) '' setOfEdge v₀ V E := ⟨x, hx, rfl⟩
      rw [h2] at hxx
      simp at hxx
  · obtain ⟨e, he, hEq⟩ := hd1
    obtain ⟨hfin, hcard⟩ := hgraph e he
    obtain ⟨u, w, huw, huwcard⟩ := Finset.card_eq_two.mp hcard
    have hEpair : e = {u, w} := by
      rw [← hfin.coe_toFinset, huwcard]
      simp
    rw [hEpair] at hEq
    have hEq' : (fun x : V3 => -x) '' {u, w} = {d.1, d.2} := hEq
    have hm1 : d.1 ∈ (fun x : V3 => -x) '' {u, w} := by rw [hEq']; simp
    have hm2 : d.2 ∈ (fun x : V3 => -x) '' {u, w} := by rw [hEq']; simp
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] at hm1 hm2
    obtain ⟨y, hy, hxy⟩ := hm1
    obtain ⟨y', hy', hxy'⟩ := hm2
    have he' : {u, w} ∈ E := by rw [← hEpair]; exact he
    have h1 : d.1 = -u ∨ d.1 = -w := by
      rcases hy with hyy | hyy
      · rw [hyy] at hxy
        exact Or.inl hxy.symm
      · rw [hyy] at hxy
        exact Or.inr hxy.symm
    have h2 : d.2 = -u ∨ d.2 = -w := by
      rcases hy' with hyy | hyy
      · rw [hyy] at hxy'
        exact Or.inl hxy'.symm
      · rw [hyy] at hxy'
        exact Or.inr hxy'.symm
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · -- d.1 = d.2 = -u：与 u ≠ w 矛盾
      exfalso
      have hww : -w ∈ (fun x : V3 => -x) '' {u, w} := ⟨w, by simp, rfl⟩
      rw [hEq', h1, h2] at hww
      have h1' : -w = -u := by
        rcases Set.mem_insert_iff.mp hww with h | h
        · exact h
        · exact Set.mem_singleton_iff.mp h
      exact huw (negInj3 h1').symm
    · exact ⟨u, w, hpairEq _ _ d h1 h2, Or.inr he'⟩
    · have he'' : ({w, u} : Set V3) ∈ E := by
        rw [pairSetComm]
        exact he'
      exact ⟨w, u, hpairEq _ _ d h1 h2, Or.inr he''⟩
    · -- d.1 = d.2 = -w：矛盾
      exfalso
      have huu : -u ∈ (fun x : V3 => -x) '' {u, w} := ⟨u, by simp, rfl⟩
      rw [hEq', h1, h2] at huu
      have h2' : -u = -w := by
        rcases Set.mem_insert_iff.mp huu with h | h
        · exact h
        · exact Set.mem_singleton_iff.mp h
      exact huw (negInj3 h2')

/-- HOL `azim_dart`-负号链的核心：被包围 dart 界的镜像版（`azim_dart_neg` +
`AZIM_LT_PI_IMP_CARD_GT_1` + Localization.ivs_azim_cycle_elim 的合并体）。
前驱 z₀ 取 `INVERSE1_SIGMA_FAN`；σ' 的极小性经 `SIGMA_FAN` 逐点镜像夹出。 -/
private theorem azimDartNegLt {V : Set V3} {E : Set (Set V3)} {v w : V3}
    (hfan : FAN 0 V E)
    (hfan' : FAN 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E))
    (hsur : surroundedNode V E v) (hd : (v, w) ∈ dart1OfFan V E) :
    azimDart ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v, -w) < Real.pi := by
  have he : {v, w} ∈ E := hd
  have hwv : v ≠ w := edge_ne_of_fan hfan he
  have hwE : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan 0 V E v w hfan).mp he
  have hbound : azimDart V E (v, w) < Real.pi :=
    hsur (v, w) ((Or.inr hd : (v, w) ∈ dartOfFan V E)) rfl
  unfold azimDart at hbound
  unfold Fan.azimFan at hbound
  rw [if_neg (show (v, w).1 ≠ (v, w).2 from fun h => hwv h)] at hbound
  by_cases hnc : 1 < (setOfEdge v V E).ncard
  · rw [if_pos hnc] at hbound
    have hivs := INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := E) (v := v) hfan
    have hz₀edge : {v, inverse1SigmaFan 0 V E v w} ∈ E := hivs.1 w he
    have hz₀mem : inverse1SigmaFan 0 V E v w ∈ setOfEdge v V E :=
      (properties_of_setOfEdge_fan 0 V E v _ hfan).mp hz₀edge
    have hz₀sig : sigmaFan 0 V E v (inverse1SigmaFan 0 V E v w) = w := hivs.2.1 w he
    have hz₀w : inverse1SigmaFan 0 V E v w ≠ w := by
      intro hz
      have hne : setOfEdge v V E ≠ {w} := by
        intro hEq
        rw [hEq] at hnc
        simp at hnc
      have h2c := hz₀sig
      rw [hz] at h2c
      exact (SIGMA_FAN hne hfan hwE).2.1 h2c
    have hvz₀ : v ≠ inverse1SigmaFan 0 V E v w := edge_ne_of_fan hfan hz₀edge
    have hboundz : azimDart V E (v, inverse1SigmaFan 0 V E v w) < Real.pi :=
      hsur _ ((Or.inr hz₀edge : (v, _) ∈ dartOfFan V E)) rfl
    unfold azimDart at hboundz
    unfold Fan.azimFan at hboundz
    rw [if_neg (show (v, inverse1SigmaFan 0 V E v w).1
        ≠ (v, inverse1SigmaFan 0 V E v w).2 from fun h => hvz₀ h), if_pos hnc] at hboundz
    rw [hz₀sig] at hboundz
    have hmirr : azim 0 (-v) (-w) (-(inverse1SigmaFan 0 V E v w))
        = azim 0 v (inverse1SigmaFan 0 V E v w) w :=
      azimMirror (fan_not_collinear hfan he) (fan_not_collinear hfan hz₀edge)
    have hW' : -w ∈ setOfEdge (-v) ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) := by
      rw [setOfEdgeNegEq]
      exact ⟨w, hwE, rfl⟩
    have hZ' : -(inverse1SigmaFan 0 V E v w) ∈ setOfEdge (-v) ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) := by
      rw [setOfEdgeNegEq]
      exact ⟨inverse1SigmaFan 0 V E v w, hz₀mem, rfl⟩
    have hinj : Set.InjOn (fun u : V3 => -u) (setOfEdge v V E) :=
      fun a b _ _ h => negInj3 h
    have hnc' : 1 < (setOfEdge (-v) ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)).ncard := by
      rw [setOfEdgeNegEq, hinj.ncard_image]
      exact hnc
    have hsne : setOfEdge (-v) ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) ≠ {-w} := by
      intro hEq
      rw [hEq] at hnc'
      simp at hnc'
    obtain ⟨hψ₁, -, hψ₃⟩ := SIGMA_FAN hsne hfan' hW'
    have hgoal : azimDart ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v, -w)
        = azim 0 (-v) (-w) (sigmaFan 0 ((fun u : V3 => -u) '' V)
            ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) (-w)) := by
      unfold azimDart
      unfold Fan.azimFan
      rw [if_neg (show (-v, -w).1 ≠ (-v, -w).2 from fun h => hwv (negInj3 h))]
      try rw [if_pos hnc']
      try rw [if_pos hnc']
    rw [hgoal]
    have hmin := hψ₃ (-(inverse1SigmaFan 0 V E v w)) hZ' (fun h => hz₀w (negInj3 h))
    rw [hmirr] at hmin
    exact lt_of_le_of_lt hmin hboundz
  · rw [if_neg hnc] at hbound
    exfalso
    linarith [Real.pi_pos]

/-- `surroundedNode` 的镜像版（conjunct 6/7 的共同核心）。 -/
private theorem surroundedNodeImageNeg {V : Set V3} {E : Set (Set V3)} {v : V3} (hv : v ∈ V)
    (hfan : FAN 0 V E)
    (hfan' : FAN 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E))
    (hsur : surroundedNode V E v) :
    surroundedNode ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) := by
  intro d hd hdu
  have hgraph : Graph E := hfan.2.1
  obtain ⟨a, b, hdab, hd₀⟩ := dartOfFanNegMem hgraph hd
  have ha : a = v := by
    refine negInj3 ?_
    have h1 : (-a : V3) = d.1 := by simp [hdab]
    exact h1.trans hdu
  rw [ha] at hdab hd₀
  rw [hdab]
  simp only [dartOfFan, dart1OfFan, Set.mem_union, Set.mem_setOf_eq] at hd₀
  rcases hd₀ with ⟨hab, hvb, hsoe⟩ | hd1
  · exfalso
    have hcontra : azimDart V E (v, v) < Real.pi :=
      hsur (v, v) ((Or.inl ⟨rfl, hvb, hsoe⟩ : (v, v) ∈ dartOfFan V E)) rfl
    unfold azimDart at hcontra
    rw [if_pos (rfl : (v, v).1 = (v, v).2)] at hcontra
    linarith [Real.pi_pos]
  · exact azimDartNegLt hfan hfan' hsur hd1

/-! ### 2c.8 `hypermapOfFanNeg` 镜像共轭 kit（2026-10-12 A5 填证 lane）

HOL ASFUTBF.hl:1007 `hypermap_of_fan_neg` 的 Lean 全套。四层：
(1) `hypermapOfFan` 的 dart 层求值件（`memDartsHypermapOfFan` +
`evalEdgeHypermapOfFan`/`evalNodeHypermapOfFan`/`evalFaceHypermapOfFan`/
`evalNodeSymmHypermapOfFan`/`evalFaceSymmHypermapOfFan`——extendPerm/res 在
dart1 上逐点展开，symm 侧经 `Equiv.symm_apply_eq` 归约为正侧求值）；
(2) `azimPredLe`：前驱方位角极小性——σ-坏集（`azimPredLe` 内 T）有限 + σ 单射 +
沿 σ 每步方位角严格递降（`sum2_azim_fan` 分解 + `unique_azim0_point_fan` 正性）
⟹ 坏集非空即导出 σ-周期点与严格递降链矛盾（鸽笼：`Set.InjOn.ncard_image` +
`Set.ncard_le_ncard`）；
(3) σ / inv1 镜像共轭 `sigmaFanNeg`/`inv1FanNeg`：SIGMA_FAN 镜像极小性经
`azimMirror` 回传 + (2) 的前驱极小性 + `azim_compl` 换向 + `unique_azim_point_fan`
单射化；inv1 侧由 σ 侧经镜像 `mono_sigma_fan` 传递；
(4) `hypermapOfFanNeg` 装配：同构映射 f(-v,-w) = (v, inv1_v w)（HOL 的
hyp_conj (node_map) 复合同款），edge 交换纯代数（σ_v(inv1_v w) = w）、node 交换
用 (3)σ-共轭、face 交换用 (3)inv1-共轭。陈述冻结逐字未动（依依赖序自 §2c 上段
移入本节）。-/

/-- `hypermapOfFan` 的 dart 集（coe 后）= `dart1OfFan`。 -/
private theorem memDartsHypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    d ∈ (hypermapOfFan x V E hfan).darts ↔ d ∈ dart1OfFan V E := by
  have hcoe : (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E :=
    (finite_dart1_fan hfan).coe_toFinset
  constructor
  · intro hmem
    have h2 : d ∈ (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) :=
      Finset.mem_coe.mp hmem
    rw [hcoe] at h2
    exact h2
  · intro hmem
    have h2 : d ∈ (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) := by
      rw [hcoe]
      exact hmem
    exact Finset.mem_coe.mpr h2

private theorem evalEdgeHypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).edgeMap d = (d.2, d.1) := by
  have hif : (hypermapOfFan x V E hfan).edgeMap d
      = if d ∈ dart1OfFan V E then eFanPair V E d else d := by
    show (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d = _
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [(finite_dart1_fan hfan).coe_toFinset]
  rw [hif, if_pos hd]
  rfl

private theorem evalNodeHypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).nodeMap d = (d.1, sigmaFan x V E d.1 d.2) := by
  have hif : (hypermapOfFan x V E hfan).nodeMap d
      = if d ∈ dart1OfFan V E then nFanPair x V E d else d := by
    show (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d = _
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [(finite_dart1_fan hfan).coe_toFinset]
  rw [hif, if_pos hd]
  rfl

private theorem evalFaceHypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d
      = (d.2, inverse1SigmaFan x V E d.2 d.1) := by
  have hif : (hypermapOfFan x V E hfan).faceMap d
      = if d ∈ dart1OfFan V E then fFanPair x V E d else d := by
    show (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (hypermapOfFan x V E hfan)) d = _
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [(finite_dart1_fan hfan).coe_toFinset]
  rw [hif, if_pos hd]
  show (d.2, inverseSigmaFan x V E d.2 d.1) = _
  rw [inverse_sigma_fan_eq_inverse1 hfan (v := d.2) (w := d.1)
    (by rw [pairSetComm]; exact hd)]

private theorem evalNodeSymmHypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).nodeMap.symm d
      = (d.1, inverse1SigmaFan x V E d.1 d.2) := by
  rw [Equiv.symm_apply_eq]
  have hmem : (d.1, inverse1SigmaFan x V E d.1 d.2) ∈ dart1OfFan V E :=
    (INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := d.1) hfan).1 d.2 hd
  rw [evalNodeHypermapOfFan hfan hmem]
  show d = (d.1, sigmaFan x V E d.1 (inverse1SigmaFan x V E d.1 d.2))
  exact Prod.ext rfl ((INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := d.1)
    hfan).2.1 d.2 hd).symm

private theorem evalFaceSymmHypermapOfFan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap.symm d
      = (sigmaFan x V E d.1 d.2, d.1) := by
  rw [Equiv.symm_apply_eq]
  have hsoe : d.2 ∈ setOfEdge d.1 V E :=
    (properties_of_setOfEdge_fan x V E d.1 d.2 hfan).mp hd
  have hsoe2 : sigmaFan x V E d.1 d.2 ∈ setOfEdge d.1 V E :=
    sigma_fan_in_setOfEdge hfan hsoe
  have hmem : (sigmaFan x V E d.1 d.2, d.1) ∈ dart1OfFan V E := by
    show ({(sigmaFan x V E d.1 d.2, d.1).1, (sigmaFan x V E d.1 d.2, d.1).2} : Set V3) ∈ E
    rw [pairSetComm]
    exact (properties_of_setOfEdge_fan x V E d.1 _ hfan).mpr hsoe2
  rw [evalFaceHypermapOfFan hfan hmem]
  show d = (d.1, inverse1SigmaFan x V E d.1 (sigmaFan x V E d.1 d.2))
  exact Prod.ext rfl ((INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := d.1)
    hfan).2.2 d.2 hd).symm

/-- 前驱方位角极小性（descent 核心）：p = inv1_v w 最小化 `azim 0 v · w`。
坏集（方位角严格更小者）经 σ 映入自身且逐点严格递降，有限集中无严格递降
无限链（σ 单射 + 鸽笼导出周期点矛盾）。 -/
private theorem azimPredLe {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {v w : V3} (hw : ({v, w} : Set V3) ∈ E) :
    ∀ z : V3, z ∈ setOfEdge v V E → z ≠ w →
      azim 0 v (inverse1SigmaFan 0 V E v w) w ≤ azim 0 v z w := by
  classical
  set p : V3 := inverse1SigmaFan 0 V E v w with hpdef
  have hSw : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan 0 V E v w hfan).mp hw
  have hinv := INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := E) (v := v) hfan
  have hpE : {v, p} ∈ E := hinv.1 w hw
  have hSp : p ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan 0 V E v _ hfan).mp hpE
  have hσp : sigmaFan 0 V E v p = w := hinv.2.1 w hw
  by_cases hpw : p = w
  · intro z _ _
    rw [hpw]
    have hn := azim_nonneg 0 v z w
    rw [azim_self 0 v w]
    exact hn
  · have hSne : ∀ y : V3, setOfEdge v V E ≠ {y} := by
      intro y hEq
      refine hpw ?_
      rw [hEq] at hSw hSp
      have h1 : w = y := Set.mem_singleton_iff.mp hSw
      have h2 : p = y := Set.mem_singleton_iff.mp hSp
      rw [h2, h1]
    have hpos : 0 < azim 0 v p w := by
      rcases lt_trichotomy (azim 0 v p w) 0 with hlt | heq | hgt
      · exact absurd hlt (by linarith [azim_nonneg 0 v p w])
      · exact absurd heq (by
          intro h0
          exact hpw (unique_azim0_point_fan hfan hpE hw h0))
      · exact hgt
    have hσmin : ∀ y ∈ setOfEdge v V E, ∀ z ∈ setOfEdge v V E, z ≠ y →
        azim 0 v y (sigmaFan 0 V E v y) ≤ azim 0 v y z := by
      intro y hy z hz hzy
      exact (SIGMA_FAN (hSne y) hfan hy).2.2 z hz hzy
    have hδ : ∀ y ∈ setOfEdge v V E, 0 < azim 0 v y (sigmaFan 0 V E v y) := by
      intro y hy
      have hyE : {v, y} ∈ E := (properties_of_setOfEdge_fan 0 V E v y hfan).mpr hy
      have hσyE : {v, sigmaFan 0 V E v y} ∈ E :=
        (properties_of_setOfEdge_fan 0 V E v _ hfan).mpr (sigma_fan_in_setOfEdge hfan hy)
      rcases lt_trichotomy (azim 0 v y (sigmaFan 0 V E v y)) 0 with hlt | heq | hgt
      · exact absurd hlt (by linarith [azim_nonneg 0 v y (sigmaFan 0 V E v y)])
      · exact absurd ((unique_azim0_point_fan hfan hyE hσyE heq).symm)
          ((SIGMA_FAN (hSne y) hfan hy).2.1)
      · exact hgt
    have hstep : ∀ y ∈ setOfEdge v V E, y ≠ w →
        azim 0 v y w = azim 0 v y (sigmaFan 0 V E v y) + azim 0 v (sigmaFan 0 V E v y) w := by
      intro y hy hyw
      exact sum2_azim_fan hfan ((properties_of_setOfEdge_fan 0 V E v y hfan).mpr hy)
        ((properties_of_setOfEdge_fan 0 V E v _ hfan).mpr (sigma_fan_in_setOfEdge hfan hy))
        hw (hσmin y hy w hSw hyw.symm)
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₀, hz₀S, hz₀w, hz₀lt⟩ := hcon
    set T : Set V3 := {z | z ∈ setOfEdge v V E ∧ z ≠ w ∧ azim 0 v p w > azim 0 v z w} with hTdef
    have hTfin : T.Finite :=
      (remark_finite_fan1 v V E hfan.2.2.1.1).subset (fun z hz => hz.1)
    have hσT : ∀ z ∈ T, sigmaFan 0 V E v z ∈ T := by
      intro z hz
      have hσzS : sigmaFan 0 V E v z ∈ setOfEdge v V E := sigma_fan_in_setOfEdge hfan hz.1
      have hσzw : sigmaFan 0 V E v z ≠ w := by
        intro he
        have hzp : z = p := mono_sigma_fan hfan hz.1 hSp (he.trans hσp.symm)
        rw [hzp] at hz
        exact absurd hz.2.2 (lt_irrefl _)
      have hσlt : azim 0 v p w > azim 0 v (sigmaFan 0 V E v z) w := by
        have h1 := hstep z hz.1 hz.2.1
        have h2 := hδ z hz.1
        have h3 := hz.2.2
        linarith
      exact ⟨hσzS, hσzw, hσlt⟩
    have hchainS : ∀ k : ℕ, (sigmaFan 0 V E v)^[k] z₀ ∈ setOfEdge v V E := by
      intro k
      induction k with
      | zero => exact hz₀S
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact sigma_fan_in_setOfEdge hfan ih
    have hchainT : ∀ k : ℕ, (sigmaFan 0 V E v)^[k] z₀ ∈ T := by
      intro k
      induction k with
      | zero => exact ⟨hz₀S, hz₀w, hz₀lt⟩
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact hσT _ ih
    have hdec : ∀ k : ℕ, azim 0 v ((sigmaFan 0 V E v)^[k] z₀) w
        > azim 0 v ((sigmaFan 0 V E v)^[k + 1] z₀) w := by
      intro k
      have h1 := hstep _ (hchainS k) (hchainT k).2.1
      have h2 := hδ _ (hchainS k)
      rw [Function.iterate_succ_apply' (sigmaFan 0 V E v) k z₀]
      linarith
    have hanti : ∀ (i j : ℕ), i < j →
        azim 0 v ((sigmaFan 0 V E v)^[j] z₀) w
          < azim 0 v ((sigmaFan 0 V E v)^[i] z₀) w := by
      intro i j
      induction j with
      | zero => intro hij; exact absurd hij (Nat.not_lt_zero i)
      | succ m ih =>
        intro hij
        rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
        · exact lt_trans (hdec m) (ih h)
        · rw [h]
          exact hdec m
    have hinj : ∀ (i j : ℕ), (sigmaFan 0 V E v)^[i] z₀ = (sigmaFan 0 V E v)^[j] z₀ →
        i = j := by
      intro i j heq
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (hanti i j h) (by rw [heq]; exact lt_irrefl _)
      · exact h
      · exact absurd (hanti j i h) (by rw [heq]; exact lt_irrefl _)
    have hinjOn : Set.InjOn (fun k : ℕ => (sigmaFan 0 V E v)^[k] z₀)
        ((Finset.range (T.ncard + 1) : Finset ℕ) : Set ℕ) := by
      intro i _ j _ heq
      exact hinj i j heq
    have himg : ((fun k : ℕ => (sigmaFan 0 V E v)^[k] z₀) ''
          ((Finset.range (T.ncard + 1) : Finset ℕ) : Set ℕ)).ncard = T.ncard + 1 := by
      rw [hinjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
    have hsub : ((fun k : ℕ => (sigmaFan 0 V E v)^[k] z₀) ''
          ((Finset.range (T.ncard + 1) : Finset ℕ) : Set ℕ)) ⊆ T := by
      intro y hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact hchainT k
    have hle := Set.ncard_le_ncard hsub hTfin
    rw [himg] at hle
    omega

/-- σ 的镜像共轭：`sigmaFan 0 (-''V) (-''E) (-v) (-w) = -(inv1_v w)`。
镜像侧 σ 的极小性经 `azimMirror` 回传为 z' = -σ' 的反向方位角极小性，与前驱的
极小性（`azimPredLe`）夹出方位角相等；`azim_compl` 换向后由
`unique_azim_point_fan` 闭合。 -/
private theorem sigmaFanNeg {V : Set V3} {E : Set (Set V3)} {v w : V3}
    (hfan : FAN 0 V E)
    (hfan' : FAN 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E))
    (hw : ({v, w} : Set V3) ∈ E) :
    sigmaFan 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) (-w)
      = -(inverse1SigmaFan 0 V E v w) := by
  classical
  set V' : Set V3 := (fun u : V3 => -u) '' V with hV'def
  set E' : Set (Set V3) := (fun e : Set V3 => (fun u : V3 => -u) '' e) '' E with hE'def
  set σ' : V3 := sigmaFan 0 V' E' (-v) (-w) with hσ'def
  have hSw : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan 0 V E v w hfan).mp hw
  have hinv := INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := E) (v := v) hfan
  have hpE : {v, inverse1SigmaFan 0 V E v w} ∈ E := hinv.1 w hw
  have hSp : inverse1SigmaFan 0 V E v w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan 0 V E v _ hfan).mp hpE
  have hS'mem : ∀ z : V3, z ∈ setOfEdge v V E → -z ∈ setOfEdge (-v) V' E' := by
    intro z hz
    rw [setOfEdgeNegEq v V E]
    exact ⟨z, hz, rfl⟩
  have hS'inv : ∀ q : V3, q ∈ setOfEdge (-v) V' E' → -q ∈ setOfEdge v V E := by
    intro q hq
    rw [setOfEdgeNegEq v V E] at hq
    obtain ⟨z, hz, hzq⟩ := hq
    rw [← hzq]
    simp only [neg_neg]
    exact hz
  by_cases hSing : setOfEdge v V E = ({w} : Set V3)
  · have hpw : inverse1SigmaFan 0 V E v w = w := by
      have h1 : inverse1SigmaFan 0 V E v w ∈ ({w} : Set V3) := hSing ▸ hSp
      exact Set.mem_singleton_iff.mp h1
    have hS'eq : setOfEdge (-v) V' E' = ({-w} : Set V3) := by
      rw [setOfEdgeNegEq v V E, hSing]
      ext u
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Set.mem_singleton_iff.mp hz]
      · intro hu
        exact ⟨w, by simp, by simpa using hu.symm⟩
    have hσ'eq : sigmaFan 0 V' E' (-v) (-w) = -w := by
      rw [sigmaFan, if_pos hS'eq]
    rw [hpw, hσ'def, hσ'eq]
  · have hσw : sigmaFan 0 V E v w ≠ w := (SIGMA_FAN hSing hfan hSw).2.1
    have hwp : w ≠ inverse1SigmaFan 0 V E v w := by
      intro he
      have h2 : sigmaFan 0 V E v w = w := by rw [he, hinv.2.1 w hw]; exact he
      exact hσw h2
    have hne' : setOfEdge (-v) V' E' ≠ ({-w} : Set V3) := by
      intro heq
      refine hSing (Set.eq_singleton_iff_unique_mem.mpr ⟨hSw, fun u hu => ?_⟩)
      have hu2 : -u ∈ setOfEdge (-v) V' E' := hS'mem u hu
      rw [heq] at hu2
      have h3 : -u = -w := Set.mem_singleton_iff.mp hu2
      simpa using congrArg Neg.neg h3
    obtain ⟨h₁, h₂, h₃⟩ := SIGMA_FAN hne' hfan' (hS'mem w hSw)
    have hz'S : -σ' ∈ setOfEdge v V E := hS'inv σ' h₁
    have hz'w : -σ' ≠ w := by
      intro he
      refine h₂ ?_
      have h5 : -(-σ') = -w := congrArg Neg.neg he
      rw [neg_neg] at h5
      exact h5
    have hz'E : {v, -σ'} ∈ E :=
      (properties_of_setOfEdge_fan 0 V E v _ hfan).mpr hz'S
    have hncw : ¬ Collinear3 0 v w := fan_not_collinear hfan hw
    have hncz' : ¬ Collinear3 0 v (-σ') := fan_not_collinear hfan hz'E
    have hncp : ¬ Collinear3 0 v (inverse1SigmaFan 0 V E v w) := fan_not_collinear hfan hpE
    have hminz' : ∀ z ∈ setOfEdge v V E, z ≠ w →
        azim 0 v (-σ') w ≤ azim 0 v z w := by
      intro z hz hzw
      have hncz : ¬ Collinear3 0 v z := fan_not_collinear hfan
        ((properties_of_setOfEdge_fan 0 V E v z hfan).mpr hz)
      have hne2 : -z ≠ -w := fun hh => hzw (negInj3 hh)
      have hmin := h₃ (-z) (hS'mem z hz) hne2
      rw [hσ'def.symm, show σ' = -(-σ') from (neg_neg σ').symm,
        azimMirror hncw hncz', azimMirror hncw hncz] at hmin
      exact hmin
    have hminp := azimPredLe hfan hw
    have hEq : azim 0 v (-σ') w = azim 0 v (inverse1SigmaFan 0 V E v w) w :=
      le_antisymm (hminz' _ hSp hwp.symm) (hminp _ hz'S hz'w)
    have hnz' : azim 0 v (-σ') w ≠ 0 := by
      intro h0
      exact hz'w (unique_azim0_point_fan hfan hz'E hw h0)
    have hnp : azim 0 v (inverse1SigmaFan 0 V E v w) w ≠ 0 := by
      intro h0
      exact hwp (unique_azim0_point_fan hfan hpE hw h0).symm
    have hcom1 : azim 0 v w (-σ') = 2 * Real.pi - azim 0 v (-σ') w := by
      rw [azim_compl hncz' hncw, if_neg hnz']
    have hcom2 : azim 0 v w (inverse1SigmaFan 0 V E v w)
        = 2 * Real.pi - azim 0 v (inverse1SigmaFan 0 V E v w) w := by
      rw [azim_compl hncp hncw, if_neg hnp]
    have hkey : azim 0 v w (-σ') = azim 0 v w (inverse1SigmaFan 0 V E v w) := by
      rw [hcom1, hcom2, hEq]
    have hfinal := unique_azim_point_fan hfan hw hz'E hpE hkey
    have h8 : σ' = -(inverse1SigmaFan 0 V E v w) := by
      have h7 := congrArg Neg.neg hfinal
      rw [neg_neg] at h7
      exact h7
    rw [hσ'def]
    exact h8

/-- inv1 的镜像共轭：`inverse1SigmaFan 0 (-''V) (-''E) (-v) (-w) = -(σ_v w)`，
由 σ-共轭（`sigmaFanNeg`）+ 镜像 `mono_sigma_fan` 传递。 -/
private theorem inv1FanNeg {V : Set V3} {E : Set (Set V3)} {v w : V3}
    (hfan : FAN 0 V E)
    (hfan' : FAN 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E))
    (hw : ({v, w} : Set V3) ∈ E) :
    inverse1SigmaFan 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) (-w)
      = -(sigmaFan 0 V E v w) := by
  classical
  have hSw : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan 0 V E v w hfan).mp hw
  have hσS : sigmaFan 0 V E v w ∈ setOfEdge v V E := sigma_fan_in_setOfEdge hfan hSw
  have hσE : {v, sigmaFan 0 V E v w} ∈ E :=
    (properties_of_setOfEdge_fan 0 V E v _ hfan).mpr hσS
  have hE'vw : ({-v, -w} : Set V3) ∈ ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) :=
    ⟨{v, w}, hw, by simp⟩
  have hmem : -(sigmaFan 0 V E v w) ∈ setOfEdge (-v) ((fun u : V3 => -u) '' V)
      ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) := by
    rw [setOfEdgeNegEq]
    exact ⟨sigmaFan 0 V E v w, hσS, rfl⟩
  have hmem2 : inverse1SigmaFan 0 ((fun u : V3 => -u) '' V)
      ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) (-w)
      ∈ setOfEdge (-v) ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) :=
    (properties_of_setOfEdge_fan 0 _ _ (-v) _ hfan').mp
      ((INVERSE1_SIGMA_FAN (x := 0) (V := _) (E := _) (v := -v) hfan').1 (-w) hE'vw)
  have hB : sigmaFan 0 ((fun u : V3 => -u) '' V)
      ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v)
        (-(sigmaFan 0 V E v w)) = -w := by
    rw [sigmaFanNeg hfan hfan' hσE,
      (INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := E) (v := v) hfan).2.2 w hw]
  exact mono_sigma_fan hfan' hmem2 hmem
    (((INVERSE1_SIGMA_FAN (x := 0) (V := (fun u : V3 => -u) '' V)
      (E := (fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (v := -v)
      hfan').2.1 (-w) hE'vw).trans hB.symm)

/-- Graph 版边不等：边的两端相异（Graph 的 card = 2 约定）。 -/
private theorem edgeNeOfGraph {E : Set (Set V3)} (hG : Graph E) {v w : V3}
    (h : ({v, w} : Set V3) ∈ E) : v ≠ w := by
  intro hveq
  subst hveq
  obtain ⟨hf, hcard⟩ := hG _ h
  have h5 : hf.toFinset ⊆ ({v} : Finset V3) := by
    intro x hx
    have hx2 : x ∈ ({v, v} : Set V3) := (Set.Finite.mem_toFinset (a := x) hf).mp hx
    simpa using hx2
  have h6 : hf.toFinset.card ≤ 1 := by simpa using Finset.card_le_card h5
  omega

/-- 镜像边集隶属的往返：{v,w} ∈ E ↔ {-v,-w} ∈ (-'')E（v ≠ w）。 -/
private theorem memNegPairImageIff {v w : V3} {E : Set (Set V3)} (hne : v ≠ w) :
    ({-v, -w} : Set V3) ∈ ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)
      ↔ ({v, w} : Set V3) ∈ E := by
  constructor
  · rintro ⟨e₀, he₀, hEq⟩
    have hEq' : (fun u : V3 => -u) '' e₀ = ({-v, -w} : Set V3) := hEq
    have hmemv : v ∈ e₀ := by
      have h1 : (-v : V3) ∈ (fun u : V3 => -u) '' e₀ := by rw [hEq']; simp
      obtain ⟨x, hx, hx'⟩ := h1
      have hx'' : -x = -v := hx'
      have hxv : x = v := negInj3 hx''
      rw [← hxv]
      exact hx
    have hmemw : w ∈ e₀ := by
      have h1 : (-w : V3) ∈ (fun u : V3 => -u) '' e₀ := by rw [hEq']; simp
      obtain ⟨x, hx, hx'⟩ := h1
      have hx'' : -x = -w := hx'
      have hxw : x = w := negInj3 hx''
      rw [← hxw]
      exact hx
    have hsub : e₀ ⊆ ({v, w} : Set V3) := by
      intro x hx
      have h1 : (-x : V3) ∈ (fun u : V3 => -u) '' e₀ := ⟨x, hx, rfl⟩
      rw [hEq'] at h1
      rcases Set.mem_insert_iff.mp h1 with hc | hc
      · exact Or.inl (negInj3 hc)
      · exact Or.inr (negInj3 hc)
    have heq : e₀ = ({v, w} : Set V3) :=
      Set.eq_of_subset_of_subset hsub
        (Set.insert_subset hmemv (Set.singleton_subset_iff.mpr hmemw))
    rw [← heq]
    exact he₀
  · intro he
    exact ⟨{v, w}, he, by simp⟩

/-- 镜像 dart 的对应拆解：镜像侧 dart 必为 (-v,-w) 且 {v,w} ∈ E。 -/
private theorem dartCorrNeg {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E)
    (hfan' : FAN 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E))
    {d : V3 × V3} (hd : d ∈ dart1OfFan ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)) :
    ∃ v w : V3, d = (-v, -w) ∧ ({v, w} : Set V3) ∈ E ∧ v ≠ w := by
  obtain ⟨v, w, rfl⟩ : ∃ v w : V3, d = (-v, -w) := ⟨-d.1, -d.2, by simp⟩
  have hne : v ≠ w := by
    intro hc
    rw [hc] at hd
    exact edgeNeOfGraph hfan'.2.1 hd rfl
  exact ⟨v, w, rfl, (memNegPairImageIff hne).mp hd, hne⟩

/-- σ-共轭的 ESTD 形式（镜像 fan 的邻边集等式 `estdNegative` 运输）。 -/
private theorem sigmaFanNegESTD {V : Set V3} {E : Set (Set V3)}
    (hEeq : ESTD ((fun v : V3 => -v) '' V)
      = (fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)
    (h1 : sigmaFan 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) (-w)
      = -(inverse1SigmaFan 0 V E v w)) :
    sigmaFan 0 ((fun u : V3 => -u) '' V) (ESTD ((fun u : V3 => -u) '' V)) (-v) (-w)
      = -(inverse1SigmaFan 0 V E v w) := by
  rw [hEeq]
  exact h1

/-- inv1-共轭的 ESTD 形式（同上运输）。 -/
private theorem inv1FanNegESTD {V : Set V3} {E : Set (Set V3)}
    (hEeq : ESTD ((fun v : V3 => -v) '' V)
      = (fun e : Set V3 => (fun u : V3 => -u) '' e) '' E)
    (h1 : inverse1SigmaFan 0 ((fun u : V3 => -u) '' V)
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' E) (-v) (-w)
      = -(sigmaFan 0 V E v w)) :
    inverse1SigmaFan 0 ((fun u : V3 => -u) '' V)
        (ESTD ((fun u : V3 => -u) '' V)) (-v) (-w)
      = -(sigmaFan 0 V E v w) := by
  rw [hEeq]
  exact h1

/-- 同构映射：镜像 dart ↦ (原侧第一分量, 原侧前驱)。 -/
noncomputable def isoMapFanNeg (V : Set V3) (E : Set (Set V3)) :
    V3 × V3 → V3 × V3 :=
  fun d => (-d.1, inverse1SigmaFan 0 V E (-d.1) (-d.2))

private theorem isoMapFanNeg_neg {V : Set V3} {E : Set (Set V3)} {v w : V3} :
    isoMapFanNeg V E (-v, -w) = (v, inverse1SigmaFan 0 V E v w) := by
  simp only [isoMapFanNeg, neg_neg]

/-- 接口 → 真证明（2026-10-12 A5 填证 lane）：HOL `Asfutbf.hypermap_of_fan_neg`
（ASFUTBF.hl:1007）。陈述自 §2c 上段依依赖序移入本节（逐字冻结）。
证明 = 四层 kit 装配（见本节头注）：BijOn 三件（映入/单射/满射）+ 三映射交换
（edge 纯代数 / node 经 `sigmaFanNeg` / face 经 `inv1FanNeg`）。 -/
theorem hypermapOfFanNeg (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hfan' : FAN 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V))) :
    HypermapIso
      (hypermapOfFan 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V)) hfan')
      (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfan)) := by
  classical
  have hE'img : ESTD ((fun v : V3 => -v) '' V)
      = (fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ESTD V) := estdNegative V
  have hfanI0 : FAN 0 ((fun v : V3 => -v) '' V) (ESTD ((fun v : V3 => -v) '' V)) := hfan'
  rw [hE'img] at hfanI0
  have hfanI : FAN 0 ((fun v : V3 => -v) '' V)
      ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ESTD V)) := hfanI0
  refine ⟨isoMapFanNeg V (ESTD V), ?_, ?_⟩
  · -- BijOn (↑H'.darts) (↑H.darts)
    refine ⟨?_, ?_, ?_⟩
    · -- 映入
      intro d hd
      have hd1 : d ∈ dart1OfFan ((fun v : V3 => -v) '' V) (ESTD ((fun v => -v) '' V)) :=
        (memDartsHypermapOfFan hfan' d).mp hd
      rw [hE'img] at hd1
      obtain ⟨v, w, hdvw, hwE, hvw⟩ := dartCorrNeg hfan hfanI hd1
      rw [hdvw]
      refine (memDartsHypermapOfFan hfan (isoMapFanNeg V (ESTD V) (-v, -w))).mpr ?_
      rw [isoMapFanNeg_neg]
      exact (properties_of_setOfEdge_fan 0 V (ESTD V) v _ hfan).mpr
        ((properties_of_setOfEdge_fan 0 V (ESTD V) v _ hfan).mp
          ((INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := v) hfan).1 w hwE))
    · -- 单射
      intro a ha b hb heq
      obtain ⟨v₁, w₁, hav₁, hwE₁, -⟩ :=
        dartCorrNeg hfan hfanI (by
          have h := (memDartsHypermapOfFan hfan' a).mp ha
          rw [hE'img] at h
          exact h)
      obtain ⟨v₂, w₂, hav₂, hwE₂, -⟩ :=
        dartCorrNeg hfan hfanI (by
          have h := (memDartsHypermapOfFan hfan' b).mp hb
          rw [hE'img] at h
          exact h)
      rw [hav₁, hav₂, isoMapFanNeg_neg, isoMapFanNeg_neg] at heq
      have h11 : v₁ = v₂ := congrArg Prod.fst heq
      subst h11
      have h22 : inverse1SigmaFan 0 V (ESTD V) v₁ w₁
          = inverse1SigmaFan 0 V (ESTD V) v₁ w₂ := congrArg Prod.snd heq
      have hw₁w₂ : w₁ = w₂ := by
        rw [← (INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := v₁)
          hfan).2.1 w₁ hwE₁, h22,
          (INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := v₁)
          hfan).2.1 w₂ hwE₂]
      rw [hav₁, hav₂, hw₁w₂]
    · -- 满射
      intro y hy
      have hy1 : y ∈ dart1OfFan V (ESTD V) := (memDartsHypermapOfFan hfan y).mp hy
      refine ⟨(-y.1, -(sigmaFan 0 V (ESTD V) y.1 y.2)), ?_, ?_⟩
      · have hσE : {y.1, sigmaFan 0 V (ESTD V) y.1 y.2} ∈ ESTD V :=
          (properties_of_setOfEdge_fan 0 V (ESTD V) y.1 _ hfan).mpr
            (sigma_fan_in_setOfEdge hfan
              ((properties_of_setOfEdge_fan 0 V (ESTD V) y.1 y.2 hfan).mp hy1))
        have hm : (-y.1, -(sigmaFan 0 V (ESTD V) y.1 y.2))
            ∈ dart1OfFan ((fun v : V3 => -v) '' V)
              ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ESTD V)) :=
          ⟨{y.1, sigmaFan 0 V (ESTD V) y.1 y.2}, hσE, by simp⟩
        rw [← hE'img] at hm
        exact (memDartsHypermapOfFan hfan' _).mpr hm
      · show (-(-y.1),
          inverse1SigmaFan 0 V (ESTD V) (-(-y.1))
            (-(-(sigmaFan 0 V (ESTD V) y.1 y.2)))) = y
        simp only [neg_neg]
        exact Prod.ext rfl
          ((INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := y.1)
            hfan).2.2 y.2 hy1)
  · -- 三映射交换
    intro x hx
    have hd1 : x ∈ dart1OfFan ((fun v : V3 => -v) '' V) (ESTD ((fun v => -v) '' V)) :=
      (memDartsHypermapOfFan hfan' x).mp hx
    obtain ⟨v, w, hxvw, hwE, hvw⟩ := dartCorrNeg hfan hfanI (by
      have h := (memDartsHypermapOfFan hfan' x).mp hx
      rw [hE'img] at h
      exact h)
    rw [hxvw] at hd1
    have hpE : {v, inverse1SigmaFan 0 V (ESTD V) v w} ∈ ESTD V :=
      (INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := v) hfan).1 w hwE
    have hpmem : inverse1SigmaFan 0 V (ESTD V) v w ∈ setOfEdge v V (ESTD V) :=
      (properties_of_setOfEdge_fan 0 V (ESTD V) v _ hfan).mp hpE
    have hσp : sigmaFan 0 V (ESTD V) v (inverse1SigmaFan 0 V (ESTD V) v w) = w :=
      (INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := v) hfan).2.1 w hwE
    have hwE' : ({w, v} : Set V3) ∈ ESTD V := Set.pair_comm _ _ ▸ hwE
    have hσpE : {v, sigmaFan 0 V (ESTD V) v (inverse1SigmaFan 0 V (ESTD V) v w)}
        ∈ ESTD V :=
      (properties_of_setOfEdge_fan 0 V (ESTD V) v _ hfan).mpr
        (sigma_fan_in_setOfEdge hfan hpmem)
    have hL : (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfan)).edgeMap
        (v, inverse1SigmaFan 0 V (ESTD V) v w)
        = (hypermapOfFan 0 V (ESTD V) hfan).faceMap
            ((hypermapOfFan 0 V (ESTD V) hfan).nodeMap
              (v, inverse1SigmaFan 0 V (ESTD V) v w)) := rfl
    have hN : (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfan)).nodeMap
        (v, inverse1SigmaFan 0 V (ESTD V) v w)
        = (hypermapOfFan 0 V (ESTD V) hfan).nodeMap.symm
            (v, inverse1SigmaFan 0 V (ESTD V) v w) := rfl
    have hF : (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfan)).faceMap
        (v, inverse1SigmaFan 0 V (ESTD V) v w)
        = (hypermapOfFan 0 V (ESTD V) hfan).faceMap.symm
            (v, inverse1SigmaFan 0 V (ESTD V) v w) := rfl
    rw [hxvw]
    refine ⟨?_, ?_, ?_⟩
    · -- edge：两面皆化至 (w, inv1_w v)
      rw [evalEdgeHypermapOfFan hfan' hd1]
      rw [show isoMapFanNeg V (ESTD V) ((-v, -w).2, (-v, -w).1)
          = isoMapFanNeg V (ESTD V) (-w, -v) from rfl]
      rw [isoMapFanNeg_neg (v := v) (w := w), hL,
        evalNodeHypermapOfFan hfan (by exact hpE),
        evalFaceHypermapOfFan hfan (by exact hσpE), hσp,
        isoMapFanNeg_neg (v := w) (w := v)]
    · -- node：σ'-镜像共轭
      rw [isoMapFanNeg_neg (v := v) (w := w), evalNodeHypermapOfFan hfan' hd1,
        sigmaFanNegESTD hE'img (sigmaFanNeg hfan hfanI hwE),
        isoMapFanNeg_neg (v := v) (w := inverse1SigmaFan 0 V (ESTD V) v w), hN,
        evalNodeSymmHypermapOfFan hfan (by exact hpE)]
    · -- face：inv1'-镜像共轭
      rw [isoMapFanNeg_neg (v := v) (w := w), evalFaceHypermapOfFan hfan' hd1]
      simp only [neg_neg]
      rw [inv1FanNegESTD hE'img (inv1FanNeg hfan hfanI hwE'),
        isoMapFanNeg_neg (v := w) (w := sigmaFan 0 V (ESTD V) w v), hF,
        evalFaceSymmHypermapOfFan hfan (by exact hpE), hσp,
        (INVERSE1_SIGMA_FAN (x := 0) (V := V) (E := ESTD V) (v := w) hfan).2.2 v hwE']
/-- **接口 → 真证明（2026-10-12 A2 填证 lane）**：HOL
`Asfutbf.contravening_negative`（ASFUTBF.hl:699）。前五数据合取项由 §2c.5
私件直接装配；第 6/7 合取项（`surroundedNode` 镜像链）经 §2c.7 kit：
fan 结构三件（`contraveningFan` / `ContraFan.contraveningFanTl` 于负号像 /
`CTVTAQA` + `ECTC ⊆ ESTD` 得 ECTC-fan，即 HOL CKQOWSA/ESTD_FAN_NEG/
ECTC_FAN_NEG/UBHDEUU2 四步）+ `surroundedNodeImageNeg`（σ_neg = −σ-前驱，
`azimMirror` 夹出）。 -/
theorem contraveningNegative (V : Set V3) (hc : Contravening V) :
    Contravening ((fun v => -v) '' V) := by
  have hfanE : FAN 0 V (ESTD V) := contraveningFan V hc
  have hVne : V ≠ ∅ := by
    have hcard := hc.2.2.2.2.1
    rintro rfl
    simp at hcard
  have hV'ne : ((fun v : V3 => -v) '' V) ≠ ∅ := by
    intro hcon
    apply hVne
    refine Set.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
    have hx' : -x ∈ ((fun v : V3 => -v) '' V) := ⟨x, hx, rfl⟩
    rw [hcon] at hx'
    simp at hx'
  have hESTD' : ESTD ((fun v : V3 => -v) '' V)
      = (fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ESTD V) := estdNegative V
  have hECTC' : ECTC ((fun v : V3 => -v) '' V)
      = (fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ECTC V) := ectrNegative V
  have hfanE'' : FAN 0 ((fun v : V3 => -v) '' V) (ESTD ((fun v : V3 => -v) '' V)) :=
    ContraFan.contraveningFanTl _ (packingNegative hc.1) (ballAnnulusNegative hc.2.1) hV'ne
  rw [hESTD'] at hfanE''
  have hECTCsub : ECTC V ⊆ ESTD V := by
    intro e he
    obtain ⟨u, w, rfl, hu, hw, hne, hdist⟩ := he
    exact ⟨u, w, rfl, hu, hw, hne, by rw [hdist]; norm_num [ContraFan.two_h0]⟩
  have hfanC : FAN 0 V (ECTC V) := CTVTAQA hfanE hECTCsub
  have hfanC' : FAN 0 ((fun v : V3 => -v) '' V)
      ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ECTC V)) := by
    have hsub : ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ECTC V)) ⊆
        ((fun e : Set V3 => (fun u : V3 => -u) '' e) '' (ESTD V)) := by
      intro e he
      obtain ⟨e₀, he₀, rfl⟩ := he
      exact ⟨e₀, hECTCsub he₀, rfl⟩
    exact CTVTAQA hfanE'' hsub
  refine ⟨packingNegative hc.1, ballAnnulusNegative hc.2.1, ?_, scriptLMaxNegative V hc.2.2.2.1,
    ?_, ?_, ?_⟩
  · rw [scriptLNegative V]
    exact hc.2.2.1
  · rw [cardNegative V]
    exact hc.2.2.2.2.1
  · intro u hu
    obtain ⟨v, hv, huv⟩ := hu
    have huv' : u = -v := by simpa using huv.symm
    subst huv'
    rw [hESTD']
    exact surroundedNodeImageNeg hv hfanE hfanE'' (hc.2.2.2.2.2.1 v hv)
  · intro u hu
    obtain ⟨v, hv, huv⟩ := hu
    have huv' : u = -v := by simpa using huv.symm
    subst huv'
    rcases hc.2.2.2.2.2.2 v hv with hs | hn2
    · left
      rw [hECTC']
      exact surroundedNodeImageNeg hv hfanC hfanC' hs
    · right
      rw [norm_neg]
      exact hn2

/-- 接口占位：HOL `Fnjlbxs.local_annulus_inequality_scriptL`（FNJLBXS-compiled.hl）。 -/
theorem localAnnulusInequalityScriptL (V : Set V3) :
    localAnnulusInequality V ↔ scriptL V ≤ 12 := by
  -- HOL FNJLBXS-compiled.hl:1758 的证明是定义性恒等：`hl [vec 0; v] = norm v / &2`
  -- （hl2 = radV_2，经 OAPVION2/CIRCUMCENTER_2；此处对应物 `RADV2`，PackingAuto25）
  -- + 求和约定（两侧同一 Finite 分支）。
  have hhl : ∀ v : V3, hl [0, v] = ‖v‖ / 2 := by
    intro v
    have hso : setOfList [0, v] = ({0, v} : Set V3) := by
      ext x; simp [setOfList]
    show radV (setOfList [0, v]) = ‖v‖ / 2
    rw [hso, RADV2 0 v, dist_zero_left]
    ring
  by_cases hV : V.Finite
  · have e1 : setSum V (fun v => lmfun (hl [0, v]))
        = Finset.sum hV.toFinset (fun v => lmfun (‖v‖ / 2)) := by
      simp only [setSum]
      rw [dif_pos hV]
      exact Finset.sum_congr rfl fun v _ => by rw [hhl]
    have e2 : scriptL V = Finset.sum hV.toFinset (fun v => lmfun (‖v‖ / 2)) := by
      rw [scriptL, dif_pos hV]
    simp only [localAnnulusInequality]
    rw [e1, e2]
  · simp only [localAnnulusInequality, setSum, scriptL, dif_neg hV]

/-- 接口占位：HOL `Fnjlbxs.FCDJDOT`（FNJLBXS-compiled.hl；前提
`pack_ineq_def_a` 显式化）。 -/
theorem fcdjdot (hpa : PackIneqDefA)
    (h : ∃ W : Set V3, Packing W ∧ W ⊆ ballAnnulus ∧ scriptL W > 12) :
    ∃ V : Set V3, Contravening V := by
  sorry

/-! NEEDS（2026-09-28 脊柱 lane 定级；2026-10-12 A4 填证 lane 依赖图更新）：
A4 侧三件套已全部闭合于本文件（见下 `cpnknxn`/`flyspeckDevolution` 与
`Set.ncard_le_ncard` 直接消费），`kcImpTheKc` 已转真证。
A6 本体（FCDJDOT，FNJLBXS-compiled.hl:1766）仍是开放接口，其证明依赖四根
HOL 柱子，全树零移植（2026-10-12 侦察，grep 实证）：
①`scriptL_attains_max_in_ball_annulus`（FNJLBXS-compiled.hl:1296）：存在
scriptL 最大元的 packing。HOL 经 ℝ^150 配置空间章（compactS/max_onS/
set_of_listS/scriptL_continuous/type150_ineq/card_packing_ball_annulus）紧致性
论证。Lean 路线（可用）：对每个 k ≤ card 界（测度计数可得显式界，如 27：
unit 球互斥含于 ball 0 3），packing k-元组集 `{f : Fin k → V3 | ∀ i, f i ∈
ballAnnulus ∧ 两两 dist ≥ 2}` 是紧集（annulus 紧 + 闭条件）且 scriptL 连续，
最大值存在；再对 k 有限取最大。
②`FNJLBXS`（FNJLBXS-compiled.hl:1324）：归一化——∃W φ，双射 + 保范数 +
每点孤立或 surrounded。HOL ~215 行：同一 ℝ^150 紧致集上极小化 min_k 距离
向量 + 扰动论证（not_surrounded_ECTC:1547 + perturbation_lemma +
not_surrounded_imp_on_one_side_of_plane + isolated_node_norm_ECTC:1631 +
not_surrounded_node_norm_ECTC:1727，其中 FCDJDOT section :1543-1806 的三件
系中等档几何，可移植）。
③Counting_spheres：`DLWCHEM`（counting_spheres.hl:7063）与 `XULJEPR`
（:7191）——消费 pack_ineq_def_a 的计数柱：card ∈ {13,14,15} 与最大性转移，
内部是球面几何计数（EXISTS_M_POLYHEDRON/YSSKQOY_VECTOR/THETA_BOUNDS），
深 GIANT。
④`bij_scriptL`——双射 + 保范数 ⟹ scriptL 相等；已由本文件 `bijScriptL`
闭合（见下）。`local_annulus_inequality_scriptL` 已闭合（本文件
`localAnnulusInequalityScriptL`）。

**2026-10-12 A6 续作 lane 收获——柱①已落**：`scriptL_attains_max_in_ball_annulus`
（FNJLBXS-compiled.hl:1296-1299）已作为本文件真证私件
`scriptLAttainsMaxInBallAnnulus` 落地（公理面 propext/choice/Quot.sound 标准
三，无新增债务），按 NEEDS 原记的 Lean 路线，且无需 ℝ^150 配置空间章：
①逐 k 紧致性——`packingConfigCompact`：`(Fin k → V3)` 上 packing 配置集
（annulus 坐标 + 两两 dist ≥ 2）为 `univ.pi` annulus 紧集（Tychonov
`isCompact_univ_pi`）的闭子集（annulus 闭 + 距离条件 = `Ici` 的 preimage）；
②`configScriptL` 连续（`lmfunContinuous`：`lmfun h = max ((h0-h)/(h0-1)) 0`
恒等绕开 ite 分段）+ `IsCompact.exists_isMaxOn` 取逐 k 最大者
（`scriptLMaxOfCard`，支配一切 card 恰为 k 的 annulus packing；
`packingConfigEnumerate` 经 `Finset.equivFinOfCardEq` 枚举）；
③`packingCardLe64`（HOL `card_packing_ball_annulus` 的 43 界粗化为 64，
测度计数：单位球互斥含于 ball 0 4，模板同 `flyspeckDevolution`）+
`Finset.exists_max_image` 对 k ∈ range 65 取有限最大。
剩余柱②（FNJLBXS 归一化）与柱③（`DLWCHEM`/`XULJEPR` 计数 GIANT，
消费 pack_ineq_def_a）；`fcdjdot` 本体维持冻结接口。
【2026-10-14 更新：柱② 已清，见下段。】

**2026-10-12 A6 续作 lane 补件——柱②解析件已落**：`perturbation_lemma`
（FNJLBXS-compiled.hl:746-748）已作为本文件真证私件 `perturbationLemma`
落地（HOL dot 以 `inner ℝ` 镜像，`Kepler.Geom.inner_eq_dot` 桥；
构造 v2 = a•v + b•n 纯内积代数，无 WithLp 形状坑）。
**柱②剩余缺口**（诚实降级记账）：`not_surrounded_imp_on_one_side_of_plane`
（FNJLBXS-compiled.hl:714-745）全树零机器——`DART1_NOT_COLLINEAR`
（Hypermap_and_fan）与 `azim_ge_azim_dart`（Fatugpd）均未移植，且 Lean
`surroundedNode`（Fan.lean:215，azimDart/dartOfFan 编码）与 HOL
`surrounded_node (V,E)`（set_of_edge 求和编码）的桥也未建；FCDJDOT section
三件（not_surrounded_ECTC :1547 / isolated_node_norm_ECTC :1631 /
not_surrounded_node_norm_ECTC :1727）全部经它消费，须开专门 Fan-machine
lane（顺序：dart 机器移植 → not_surrounded_imp_on_one_side_of_plane
（v cross w 分离平面路线，azim 正弦界 JBDNJJB 已在 LA5/PolyAuto7 可查）
→ 三件中等档 → FNJLBXS 归一化本体）。

**2026-10-12 A6 续四波收获——柱②前置件全部在树**：本节 2c⁗ 五件真证落地
（`ectrPairMem` 边隶属刻画 + HOL :1547/:1631/:1727 三件中等档，含
`notSurroundedECTC` 的 u-插入换元构造与 `isolatedNodeNormECTC` 的单点集
对径点对 / 多点集径向内移两分支）。至此 FCDJDOT 的四柱距离精确化：
①柱 scriptL_attains_max ✅（`scriptLAttainsMaxInBallAnnulus`）；
②柱 FNJLBXS 归一化 = **仅剩本体一件**：FNJLBXS-compiled.hl:1324-1537
（~213 行，ℝ^150 配置空间章）。HOL 内容 = 在「annulus packing 且范数剖面
与 V 匹配」的紧配置集上，对 min-距离向量 (min_dist_k j) 作字典序极小化
（嵌套紧集链 C i + CONTINUOUS_ATTAINS_SUP），末步对「既不孤立又不
surrounded」的配置点经 not_surrounded_imp_on_one_side_of_plane +
perturbation_lemma 扰动一点，与字典序极小矛盾。Lean 路线（无需 ℝ^150，
模板 = 本文件柱①的 `packingConfig`/`packingConfigCompact`/
`packingConfigEnumerate`/`scriptLMaxOfCard`）：配置集 = `(Fin k → V3)` 的
annulus 坐标 + 两两 dist ≥ 2 + 范数剖面匹配（经 `Finset.equivFinOfCardEq`
枚举 V），c : Fin k → ℝ 连续（`min_k`-向量 = 逐点 min 有限和，连续性初
等），字典序极小 = k 步递归取 argmin（每步 `IsCompact.exists_isMinOn`，
步进集仍紧非空），末步扰动矛盾 = 本节三件 + `perturbationLemma` +
`notSurroundedImpOnOneSideOfPlane` 直接拼装。规模评估：~600-900 行 Lean，
独立专项波（非本波尾巴）；其中 bijection 簿记（HOL BIJ_from_lists/indexl）
经枚举 equiv 大幅简化。③柱 DLWCHEM/XULJEPR 计数维持 GIANT（不在近期波）；
④bij_scriptL ✅ + local_annulus_inequality_scriptL ✅。
**公理面记账**：`isolatedNodeNormECTC` 标准三无债；`notSurroundedECTC`/
`notSurroundedNodeNormECTC` 经 `ContraFan.contraveningFanTl`（CKQOWSA 链）
继承树内既有债务 `ContraFan.LEMMA_4_POINTS_FINAL`（ContraFan.lean:605，
骨架占位桩）——该件落地后此二件自动转标准三。

**2026-10-14 A6 柱② 落地——柱② 全清**：FNJLBXS 本体已作为本文件私件
`fnjlbxsCore`（本节末，`notSurroundedNodeNormECTC` 之后）真证落地，
零桩、零新增公理（全部前置件树内已有），陈述逐字对照 HOL
FNJLBXS-compiled.hl:1324-1537。Lean 路线（按 NEEDS 原记，无需 ℝ^150）：
配置空间 = `(Fin k → V3)` 的 annulus 坐标 + 两两 dist ≥ 2 + 范数剖面匹配
（经 `packingConfigEnumerate` 枚举），min-距离向量的字典序极小化 =
`fnxOrdStat`（第 j 小值 = 各 j+1 元子集最大值之最小，Master-iff
`fnxOrdStatLeIff`：第 j 小 ≤ t ⟺ 至少 j+1 项 ≤ t；连续性
`fnxOrdStatCont`）+ `fnxChain` 紧集链逐级 argmax（`fnxChainProps`）；
末步对「既不孤立又不 surrounded」的配置点 r：`contraveningFanTl` 的
ESTD 扇 + `notSurroundedImpOnOneSideOfPlane` 取分离法向量，S = 边邻居 +
`perturbationLemma` 沿之推离，扰动配置 `Function.update xst r u` 仍是
合法配置（hK：所有 i ≠ r 的距离被推过 dy ≥ 2，packing 存活），dy-以下
计数严格减 1（hPa：r 行移出），分歧级 n0 = fp 侧 dy-以下计数处
`c n0 xst ≤ dy < c n0 fp`，与 `xst ∈ C (n0+1)` 的 argmax 性质矛盾。
五个前置桩消费树内真证：`packingConfigCompact`/`packingFiniteOfBallAnnulus`/
`perturbationLemma`/`notSurroundedImpOnOneSideOfPlane`/`packingConfigEnumerate`。
`fnjlbxsCore` 继承 `ContraFan.contraveningFanTl` 的 CKQOWSA 链债务
（同 `notSurroundedECTC`）；目前零消费者——`fcdjdot` 装配等柱③
（`DLWCHEM`/`XULJEPR` 计数 GIANT）。 -/


/-- **annulus 有限性**（2026-10-12 A6 填证 lane 落地；HOL
`finite_packing_ball_annulus` 的替代路线）：packing + 含于 annulus ⟹ 有限
（annulus ⊆ closedBall 0 (2·h0) ⊆ ball 0 3，经 `Packing.finite_inter_ball`）。 -/
private theorem packingFiniteOfBallAnnulus {V : Set V3} (hV : Packing V)
    (hsub : V ⊆ ballAnnulus) : V.Finite := by
  have hVb : V ⊆ Metric.ball 0 3 := by
    intro v hv
    have hmem : ‖v‖ ≤ 2 * h0 := by
      have hp := hsub hv
      simp only [ballAnnulus, Set.mem_sdiff] at hp
      have h'd := Metric.mem_closedBall.mp hp.1
      rw [dist_zero_right] at h'd
      exact h'd
    have hh0 : (2:ℝ) * h0 < 3 := by
      show (2:ℝ) * 1.26 < 3
      norm_num
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hmem]
  have hveq : V = V ∩ Metric.ball 0 3 := (Set.inter_eq_left.mpr hVb).symm
  rw [hveq]
  exact hV.finite_inter_ball 3

/-- **card ≥ 13 下界**（2026-10-12 A6 填证 lane 落地；HOL
`LMFUN_INEQ_CENTER_IMP_13` + `fat_lemma1` 的消费侧内容）：annulus 中每点的
scriptL 贡献 `lmfun (‖v‖/2) ≤ 1`，故 `scriptL V > 12` 强制 `ncard V ≥ 13`。 -/
private theorem thirteenLeCardOfScriptLGt12 {V : Set V3} (hsub : V ⊆ ballAnnulus)
    (hfin : V.Finite) (hgt : 12 < scriptL V) : 13 ≤ V.ncard := by
  rw [scriptL, dif_pos hfin] at hgt
  have hterm : ∀ v ∈ V, lmfun (‖v‖ / 2) ≤ 1 := by
    intro v hv
    have hp := hsub hv
    simp only [ballAnnulus, Set.mem_sdiff] at hp
    have hlo : (2:ℝ) ≤ ‖v‖ := by
      have h' := hp.2
      rw [Metric.mem_ball, dist_zero_right] at h'
      exact le_of_not_gt h'
    have hup : ‖v‖ ≤ 2 * h0 := by
      have h'd := Metric.mem_closedBall.mp hp.1
      rw [dist_zero_right] at h'd
      exact h'd
    have hbranch : ‖v‖ / 2 ≤ h0 := by
      rw [div_le_iff₀ (show (0:ℝ) < 2 by norm_num)]
      linarith
    rw [lmfun, if_pos hbranch, div_le_iff₀ (show (0:ℝ) < h0 - 1 by norm_num [h0])]
    have hge1 : (1:ℝ) ≤ ‖v‖ / 2 := by
      rw [le_div_iff₀ (show (0:ℝ) < 2 by norm_num)]
      linarith
    linarith
  have hsum : ∑ v ∈ hfin.toFinset, lmfun (‖v‖ / 2) ≤ (hfin.toFinset.card : ℝ) := by
    have h0' : ∑ v ∈ hfin.toFinset, lmfun (‖v‖ / 2) ≤
        ∑ v ∈ hfin.toFinset, 1 :=
      Finset.sum_le_sum (fun v hv => hterm v (hfin.mem_toFinset.mp hv))
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h0'
    exact h0'
  rw [Set.ncard_eq_toFinset_card _ hfin]
  by_contra hcon
  have h1 : (12:ℝ) < (hfin.toFinset.card : ℝ) := by linarith [hgt, hsum]
  have h2 : 12 < hfin.toFinset.card := Nat.cast_lt.mp h1
  omega

/-- **bij_scriptL**（FNJLBXS 章，2026-10-12 A6 填证 lane 落地）：双射且
逐点保范数 ⟹ scriptL 相等。有限性由 `V.Finite` 显式给出（消费语境
packing + annulus 有界性即得，见上 `packingFiniteOfBallAnnulus`；W 的
有限性经 BijOn 传递）。 -/
private theorem bijScriptL {V W : Set V3} (hV : V.Finite) (f : V3 → V3)
    (hbij : Set.BijOn f V W) (hnorm : ∀ u ∈ V, ‖u‖ = ‖f u‖) :
    scriptL V = scriptL W := by
  -- W = f '' V 且有限
  have himg : f '' V = W := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hbij.1 hv
    · exact fun hx => hbij.2.2 hx
  have hfin : (f '' V).Finite := Finite.image f hV
  rw [himg] at hfin
  have hW : W.Finite := hfin
  rw [scriptL, scriptL, dif_pos hV, dif_pos hW]
  -- W 的枚举 = V 的枚举在 f 下的像
  have himgEq : hW.toFinset = hV.toFinset.image f := by
    ext x
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · exact fun hx => hbij.2.2 hx
    · rintro ⟨v, hvT, rfl⟩
      exact hbij.1 hvT
  rw [himgEq, Finset.sum_image (fun x hx y hy hxy =>
    hbij.2.1 (hV.mem_toFinset.mp hx) (hV.mem_toFinset.mp hy) hxy)]
  exact Finset.sum_congr rfl fun v hv => by rw [hnorm v (hV.mem_toFinset.mp hv)]

/-! ### 2c'. `scriptL_attains_max_in_ball_annulus`（FNJLBXS 章，2026-10-12 A6 续作 lane）

HOL FNJLBXS-compiled.hl:1296-1299。Lean 路线**不需要 ℝ^150 配置空间章**：
对每个 k，把 k 元组空间 `(Fin k → V3)` 里的 packing 配置集证明为紧集
（`univ.pi` annulus 紧集的闭子集，`isCompact_univ_pi` Tychonov + 闭条件
preimage），`scriptL` 在其上连续（`lmfun = max 0 ((h0-h)/(h0-1))` 的连续性
+ 有限和），故取最大；再对 k ∈ range 65（card ≤ 64，测度计数）取有限最大。
-/

/-- `scriptL` 的配置泛函在 k 元组上的形式：第 i 项为 `lmfun (‖f i‖ / 2)`。 -/
private noncomputable def configScriptL (k : ℕ) (f : Fin k → V3) : ℝ :=
  ∑ i, lmfun (‖f i‖ / 2)

/-- `lmfun` 的连续性（h0 = 1.26 > 1）：`lmfun h = max ((h0 - h) / (h0 - 1)) 0`，
两支在 h0 处同值 0，`max` 型恒等绕开 ite 分段连续性。 -/
private theorem lmfunEqMax (h : ℝ) : lmfun h = max ((h0 - h) / (h0 - 1)) 0 := by
  rw [lmfun]
  by_cases hh : h ≤ h0
  · rw [if_pos hh]
    exact (max_eq_left (show (0:ℝ) ≤ (h0 - h) / (h0 - 1) by
      exact div_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (by norm_num [h0])))).symm
  · rw [if_neg hh]
    exact (max_eq_right (show (h0 - h) / (h0 - 1) ≤ (0:ℝ) by
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (not_le.mp hh).le)
        (sub_nonneg.mpr (by norm_num [h0])))).symm

private theorem lmfunContinuous : Continuous lmfun := by
  have hfun : lmfun = fun h : ℝ => max ((h0 - h) / (h0 - 1)) 0 := funext lmfunEqMax
  rw [hfun]
  exact ((continuous_const.sub continuous_id).div
    (continuous_const.sub continuous_const)
    (fun _ => sub_ne_zero.mpr (by norm_num [h0]))).max continuous_const

/-- 配置泛函连续：有限和 + 范数连续 + 求值连续。 -/
private theorem configScriptLContinuous (k : ℕ) :
    Continuous (configScriptL k) := by
  unfold configScriptL
  exact continuous_finsetSum _ (fun i _ =>
    lmfunContinuous.comp ((continuous_norm.comp (continuous_apply i)).div_const 2))

/-- k 元 packing 配置集：全部坐标在 annulus 内 + 两两距离 ≥ 2。 -/
private def packingConfig (k : ℕ) : Set (Fin k → V3) :=
  {f | (∀ i, f i ∈ ballAnnulus) ∧ ∀ i j, i ≠ j → 2 ≤ dist (f i) (f j)}

/-- 距离-条件闭集的显式 iInter 形。 -/
private theorem packingConfigDistEq (k : ℕ) :
    {f : Fin k → V3 | ∀ i j, i ≠ j → 2 ≤ dist (f i) (f j)}
      = ⋂ (p : Fin k × Fin k) (_ : p.1 ≠ p.2),
          (fun f => dist (f p.1) (f p.2)) ⁻¹' {r : ℝ | 2 ≤ r} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h p hp
    exact h p.1 p.2 hp
  · intro h i j hij
    exact h (i, j) hij

/-- annulus 闭（closedBall 减开 ball）。 -/
private theorem ballAnnulusClosed : IsClosed ballAnnulus :=
  Metric.isClosed_closedBall.sdiff Metric.isOpen_ball

/-- annulus 紧（有界闭，V3 有限维）。 -/
private theorem ballAnnulusCompact : IsCompact ballAnnulus :=
  (isCompact_closedBall (0 : V3) (2 * h0)).of_isClosed_subset ballAnnulusClosed
    Set.sdiff_subset

/-- 配置集紧：annulus-柱（Tychonov `isCompact_univ_pi`）的闭子集
（annulus 闭 + 距离条件为 `Ici` 的 preimage）。 -/
private theorem packingConfigCompact (k : ℕ) : IsCompact (packingConfig k) := by
  have h1 : IsClosed {f : Fin k → V3 | ∀ i, f i ∈ ballAnnulus} := by
    have heq : {f : Fin k → V3 | ∀ i, f i ∈ ballAnnulus}
        = ⋂ i : Fin k, (fun f => f i) ⁻¹' ballAnnulus := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact isClosed_iInter (fun i => ballAnnulusClosed.preimage (continuous_apply i))
  have hKsub : {f : Fin k → V3 | ∀ i, f i ∈ ballAnnulus} ⊆
      Set.univ.pi (fun _ : Fin k => Metric.closedBall (0 : V3) (2 * h0)) := by
    intro f hf
    rw [Set.mem_univ_pi]
    intro i
    have hi : f i ∈ ballAnnulus := hf i
    simp only [ballAnnulus, Set.mem_sdiff] at hi
    exact hi.1
  have hKcpt : IsCompact {f : Fin k → V3 | ∀ i, f i ∈ ballAnnulus} :=
    (isCompact_univ_pi (fun _ : Fin k => isCompact_closedBall (0 : V3) (2 * h0))).of_isClosed_subset
      h1 hKsub
  have h2 : IsClosed {f : Fin k → V3 | ∀ i j, i ≠ j → 2 ≤ dist (f i) (f j)} := by
    rw [packingConfigDistEq k]
    refine isClosed_iInter (fun p => isClosed_iInter (fun _ => ?_))
    exact (isClosed_Ici : IsClosed {r : ℝ | 2 ≤ r}).preimage
      (Continuous.dist (continuous_apply p.1) (continuous_apply p.2))
  unfold packingConfig
  exact hKcpt.of_isClosed_subset (h1.inter h2) Set.inter_subset_left

/-- **枚举**（card k 的 packing 配置可实现为 k 元组）：card k 的 annulus packing
V 可枚举为单射 `f : Fin k → V3`，`range f = V` 且 `f` 是合法配置
（injectivity 由 packing 的距离条件给出）。`Finset.equivFinOfCardEq` 取枚举。 -/
private theorem packingConfigEnumerate {V : Set V3} (hV : Packing V) (hsub : V ⊆ ballAnnulus)
    {k : ℕ} (hk : V.ncard = k) :
    ∃ f : Fin k → V3, Set.range f = V ∧ Function.Injective f ∧ f ∈ packingConfig k := by
  classical
  have hfin : V.Finite := packingFiniteOfBallAnnulus hV hsub
  rw [Set.ncard_eq_toFinset_card V hfin] at hk
  have he : ↥hfin.toFinset ≃ Fin k := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hk)
  refine ⟨fun i => ((he.symm i : V3)), ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.mp (he.symm i).property
    · rintro hx
      exact ⟨he ⟨x, hfin.mem_toFinset.mpr hx⟩, by simp⟩
  · intro i j hij
    exact he.symm.injective (Subtype.ext hij)
  · refine ⟨fun i => hsub (hfin.mem_toFinset.mp (he.symm i).property), fun i j hij => ?_⟩
    have hne : (he.symm i : V3) ≠ (he.symm j : V3) := fun hc => hij (he.symm.injective (Subtype.ext hc))
    exact hV.dist_ge_two (hfin.mem_toFinset.mp (he.symm i).property)
      (hfin.mem_toFinset.mp (he.symm j).property) hne

/-- **card ≤ 64**（card_packing_ball_annulus 的替代路线，FNJLBXS-compiled.hl:674
只用任意显式界即可）：annulus packing 的单位球互斥且含于 ball 0 4
（annulus ⊆ closedBall 0 (2·h0) ⊆ ball 0 3），测度计数
`card · (4π/3) ≤ 64 · (4π/3)` 给 `card ≤ 64`（HOL 界 43 的粗化，收口用）。 -/
private theorem packingCardLe64 {V : Set V3} (hV : Packing V) (hsub : V ⊆ ballAnnulus) :
    V.ncard ≤ 64 := by
  classical
  have hfin : V.Finite := packingFiniteOfBallAnnulus hV hsub
  set T : Finset V3 := hfin.toFinset with hTeq
  have hmem : ∀ v ∈ T, v ∈ V := fun v hv => hfin.mem_toFinset.mp hv
  -- 单位球族互斥（packing ⇒ 距离 ≥ 2）
  have hdisj : ((T : Set V3)).PairwiseDisjoint (fun v => Metric.ball v 1) := by
    intro u hu v hv hne
    simp only [Function.onFun]
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne'
    obtain ⟨w, hwu, hwv⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    have hdist := hV.dist_ge_two (hmem u hu) (hmem v hv) hne
    have htri : dist u v ≤ dist u w + dist w v := dist_triangle u w v
    rw [Metric.mem_ball] at hwu hwv
    linarith [dist_comm u w ▸ hwu]
  -- 计数 = 测度
  have htopEach : ∀ v ∈ T, MeasureTheory.volume (Metric.ball v 1) ≠ (⊤:ENNReal) := by
    intro v _
    rw [EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hcount : MeasureTheory.volume.real (⋃ v ∈ T, Metric.ball v 1)
      = (T.card : ℝ) * (Real.pi * 4 / 3) := by
    rw [MeasureTheory.Measure.real_def,
      MeasureTheory.measure_biUnion_finset hdisj
        (fun v _ => measurableSet_ball),
      ENNReal.toReal_sum htopEach]
    have hsumreal : ∀ v ∈ T,
        (MeasureTheory.volume (Metric.ball v 1)).toReal = Real.pi * 4 / 3 := by
      intro v _
      rw [EuclideanSpace.volume_ball_fin_three,
        ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 by norm_num),
        ENNReal.toReal_ofReal (show (0:ℝ) ≤ Real.pi * 4 / 3 by linarith [Real.pi_pos])]
      norm_num
    rw [Finset.sum_congr rfl hsumreal, Finset.sum_const, nsmul_eq_mul]
  -- 单位球并 ⊆ ball 0 4（annulus ⊆ ball 0 3）
  have hvb : ∀ v ∈ T, dist v 0 < 3 := by
    intro v hv
    have hp := hsub (hmem v hv)
    simp only [ballAnnulus, Set.mem_sdiff] at hp
    have h' := Metric.mem_closedBall.mp hp.1
    rw [dist_zero_right] at h' ⊢
    have hh0 : (2:ℝ) * h0 < 3 := by
      show (2:ℝ) * 1.26 < 3
      norm_num
    linarith
  have hsub4 : (⋃ v ∈ T, Metric.ball v 1) ⊆ Metric.ball (0 : V3) 4 := by
    intro w hw
    simp only [mem_iUnion, exists_prop] at hw
    obtain ⟨v, hvT, hwv⟩ := hw
    rw [Metric.mem_ball] at hwv ⊢
    calc dist w 0 ≤ dist w v + dist v 0 := dist_triangle w v 0
      _ < 4 := by linarith [hvb v hvT]
  have hvol4 : MeasureTheory.volume.real (Metric.ball (0 : V3) 4)
      = 64 * (Real.pi * 4 / 3) := by
    rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (show (0:ℝ) ≤ 4 by norm_num),
      ENNReal.toReal_ofReal (show (0:ℝ) ≤ Real.pi * 4 / 3 by linarith [Real.pi_pos])]
    norm_num
  have hbigtop : MeasureTheory.volume (Metric.ball (0 : V3) 4) ≠ (⊤:ENNReal) := by
    rw [EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hmono : MeasureTheory.volume.real (⋃ v ∈ T, Metric.ball v 1) ≤
      MeasureTheory.volume.real (Metric.ball (0 : V3) 4) := by
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
    refine (ENNReal.toReal_le_toReal ?_ hbigtop).mpr
      (MeasureTheory.measure_mono hsub4 (μ := MeasureTheory.volume))
    intro h
    have h1 := MeasureTheory.measure_mono hsub4 (μ := MeasureTheory.volume)
    rw [h] at h1
    exact hbigtop (top_le_iff.mp h1)
  have hc : (0:ℝ) < Real.pi * 4 / 3 := by linarith [Real.pi_pos]
  have h4 := hmono
  rw [hcount, hvol4] at h4
  have hcard : (T.card : ℝ) ≤ 64 := le_of_mul_le_mul_right h4 hc
  rw [Set.ncard_eq_toFinset_card V hfin]
  exact_mod_cast hcard

/-- **scriptL 在 range 上 = 配置泛函**（单射枚举下 scriptL 与 k 元组形式重合）。 -/
private theorem scriptLRangeConfig (k : ℕ) (f : Fin k → V3) (hinj : Function.Injective f) :
    scriptL (Set.range f) = configScriptL k f := by
  have hfin : (Set.range f).Finite := Set.finite_range f
  rw [scriptL, dif_pos hfin, configScriptL]
  have he : hfin.toFinset = Finset.univ.image f := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_range]
    exact ⟨fun h => ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩,
      fun h => ⟨h.choose, h.choose_spec.2⟩⟩
  rw [he, Finset.sum_image (fun x _ y _ hxy => hinj hxy)]

/-- **每个 k 的最大者**（FNJLBXS-compiled.hl:1296 的逐 k 版本）：card 恰为 k 的
annulus packing 的 scriptL 被某个 annulus packing 支配。 -/
private theorem scriptLMaxOfCard (k : ℕ) :
    ∃ W : Set V3, Packing W ∧ W ⊆ ballAnnulus ∧
      ∀ V : Set V3, Packing V → V ⊆ ballAnnulus → V.ncard = k → scriptL V ≤ scriptL W := by
  by_cases hne : (packingConfig k).Nonempty
  · obtain ⟨z, hzcfg, hzmax⟩ :=
      (packingConfigCompact k).exists_isMaxOn hne (configScriptLContinuous k).continuousOn
    have hz2 : (∀ i, z i ∈ ballAnnulus) ∧ ∀ i j, i ≠ j → 2 ≤ dist (z i) (z j) := hzcfg
    obtain ⟨hzann, hzdist⟩ := hz2
    have hzinj : Function.Injective z := by
      intro i j hij
      by_contra hne'
      have h2 := hzdist i j hne'
      rw [hij, dist_self] at h2
      norm_num at h2
    refine ⟨Set.range z, ?_, ?_, ?_⟩
    · intro u hu v hv hd
      obtain ⟨i, rfl⟩ := hu
      obtain ⟨j, rfl⟩ := hv
      rcases eq_or_ne i j with rfl | hij
      · rfl
      · exact absurd hd (not_lt.2 (hzdist i j hij))
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact hzann i
    · intro V hpack hsub hk
      obtain ⟨f, hfr, hfinj, hfcfg⟩ := packingConfigEnumerate hpack hsub hk
      have hfinV : V.Finite := packingFiniteOfBallAnnulus hpack hsub
      have hfinW : (Set.range z).Finite := Set.finite_range z
      rw [scriptL, dif_pos hfinV, scriptL, dif_pos hfinW]
      have eV : hfinV.toFinset = Finset.univ.image f := by
        ext x
        rw [Set.Finite.mem_toFinset, ← hfr]
        simp [Set.mem_range, Finset.mem_image]
      have eW : hfinW.toFinset = Finset.univ.image z := by
        ext x
        simp [Set.Finite.mem_toFinset, Set.mem_range, Finset.mem_image]
      rw [eV, eW, Finset.sum_image (fun x _ y _ hxy => hfinj hxy),
        Finset.sum_image (fun x _ y _ hxy => hzinj hxy)]
      exact isMaxOn_iff.mp hzmax f hfcfg
  · refine ⟨∅, ?_, ?_, ?_⟩
    · intro u hu
      exact absurd hu (by simp)
    · intro x hx
      exact absurd hx (by simp)
    · intro V hpack hsub hk
      exfalso
      obtain ⟨f, _, _, hfcfg⟩ := packingConfigEnumerate hpack hsub hk
      exact hne ⟨f, hfcfg⟩

/-- **scriptL_attains_max_in_ball_annulus**（FNJLBXS-compiled.hl:1296-1299，
2026-10-12 A6 续作 lane 落地）：存在 annulus packing 达到 scriptL 全局最大。
Lean 路线无需 ℝ^150 配置空间章：逐 k 紧致性（`packingConfigCompact` 的
`(Fin k → V3)` Tychonov 闭子集）+ `configScriptL` 连续取最大
（`IsCompact.exists_isMaxOn`），再对 k ∈ range 65（`packingCardLe64` 测度计数界）
取有限最大（`Finset.exists_max_image`）。 -/
private theorem scriptLAttainsMaxInBallAnnulus :
    ∃ W : Set V3, Packing W ∧ W ⊆ ballAnnulus ∧
      ∀ V : Set V3, Packing V → V ⊆ ballAnnulus → scriptL V ≤ scriptL W := by
  classical
  have key : ∀ k : ℕ, ∃ W : Set V3, Packing W ∧ W ⊆ ballAnnulus ∧
      ∀ V : Set V3, Packing V → V ⊆ ballAnnulus → V.ncard = k → scriptL V ≤ scriptL W :=
    scriptLMaxOfCard
  choose Wf hWp hWs hWd using key
  have hfam : (Finset.range 65).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image (Finset.range 65)
    (fun j => scriptL (Wf j)) hfam
  refine ⟨Wf k, hWp k, hWs k, ?_⟩
  intro V hpack hsub
  have hle : V.ncard ≤ 64 := packingCardLe64 hpack hsub
  have hmem : V.ncard ∈ Finset.range 65 := Finset.mem_range.mpr (by omega)
  have h1 := hWd V.ncard V hpack hsub rfl
  have h2 := hkmax V.ncard hmem
  linarith


/-- **perturbation_lemma**（FNJLBXS-compiled.hl:746-748，2026-10-12 A6 续作 lane
落地）：HOL 逐句镜像——存在与 v 等长、离 S 中每点更远、且位移 < d 的 v2。
折算说明：HOL dot 以 `inner ℝ` 镜像（`Kepler.Geom.inner_eq_dot` 桥）；
构造 v2 = a•v + b•n（a = max 0 (1 - d²/(4⟪v,v⟫))，b = √(⟪v,v⟫(1-a²)/⟪n,n⟫)），
等长性经 ⟪v2,v2⟫ = ⟪v,v⟫ 的内积展开 + `sq_eq_sq₀`，远离性经二次差
2(1-a)⟪w,v⟫ - 2b⟪w,n⟫ ≥ 0 分解，位移界经 ‖v-v2‖² = 2(1-a)⟪v,v⟫ ≤ d²/2。
供 FNJLBXS 归一化（柱②）消费。 -/
private theorem perturbationLemma (d : ℝ) (hd : 0 < d) {n : Kepler.Geom.V3} (hn : n ≠ 0)
    {v : Kepler.Geom.V3} (hvn : inner ℝ v n = 0) (S : Set Kepler.Geom.V3)
    (hS : ∀ w ∈ S, inner ℝ w n ≤ 0 ∧ 0 < inner ℝ w v) :
    ∃ v2 : Kepler.Geom.V3, ‖v2‖ = ‖v‖ ∧ (∀ w ∈ S, dist v w < dist v2 w) ∧ dist v v2 < d := by
  classical
  by_cases hS0 : S = ∅
  · refine ⟨v, rfl, ?_, by rw [dist_self]; exact hd⟩
    intro w hw
    exact absurd hw (by rw [hS0]; simp)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨w, hwS⟩ := Set.nonempty_iff_ne_empty.mpr hS0
    have h3 := (hS w hwS).2
    rw [inner_zero_right] at h3
    exact absurd h3 (by norm_num)
  have hnpos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hvv : 0 < inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos hnpos 2
  have hnn : 0 < inner ℝ n n := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hn) 2
  have hvn' : inner ℝ n v = 0 := by rw [real_inner_comm]; exact hvn
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = max 0 (1 - d ^ 2 / (4 * inner ℝ v v)) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha_def]; exact le_max_left _ _
  have ha1 : a < 1 := by
    rw [ha_def]
    refine max_lt (by norm_num) ?_
    have hquot : 0 < d ^ 2 / (4 * inner ℝ v v) :=
      div_pos (pow_pos hd 2) (by linarith)
    linarith
  have ha2 : a * a ≤ 1 := by nlinarith
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ,
      b = Real.sqrt (inner ℝ v v * (1 - a * a) / inner ℝ n n) := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb_def]; exact Real.sqrt_nonneg _
  have hbdef : b * b * inner ℝ n n = (1 - a * a) * inner ℝ v v := by
    rw [hb_def, Real.mul_self_sqrt]
    · field_simp
    · exact div_nonneg (mul_nonneg hvv.le (by linarith)) hnn.le
  refine ⟨a • v + b • n, ?_, ?_, ?_⟩
  · have hvv2 : inner ℝ (a • v + b • n) (a • v + b • n)
        = a * a * inner ℝ v v + b * b * inner ℝ n n := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hvn, hvn']
      ring
    have hn2 : ‖a • v + b • n‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hvv2, hbdef]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn2
  · intro w hw
    obtain ⟨hwn, hwv⟩ := hS w hw
    have hvv2 : inner ℝ (a • v + b • n) (a • v + b • n)
        = a * a * inner ℝ v v + b * b * inner ℝ n n := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hvn, hvn']
      ring
    have hinnerwX : inner ℝ w (a • v + b • n)
        = a * inner ℝ w v + b * inner ℝ w n := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hnormeq : inner ℝ (a • v + b • n) (a • v + b • n) = inner ℝ v v := by
      rw [hvv2, hbdef]
      ring
    have hI : ‖w - (a • v + b • n)‖ ^ 2
        = inner ℝ w w - 2 * inner ℝ w (a • v + b • n)
          + inner ℝ (a • v + b • n) (a • v + b • n) := by
      rw [show ‖w - (a • v + b • n)‖ ^ 2
          = inner ℝ (w - (a • v + b • n)) (w - (a • v + b • n))
          from (real_inner_self_eq_norm_sq _).symm,
        inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_comm (a • v + b • n) w]
      ring
    have hJ : ‖w - v‖ ^ 2 = inner ℝ w w - 2 * inner ℝ w v + inner ℝ v v := by
      rw [show ‖w - v‖ ^ 2 = inner ℝ (w - v) (w - v)
          from (real_inner_self_eq_norm_sq _).symm,
        inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v w]
      ring
    obtain ⟨u', hu'def⟩ : ∃ u' : ℝ, u' = -(b * inner ℝ w n) := ⟨_, rfl⟩
    have hu'0 : 0 ≤ u' := by
      rw [hu'def]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hb0 hwn)
    have hfinal : ‖w - (a • v + b • n)‖ ^ 2 - ‖w - v‖ ^ 2
        = 2 * ((1 - a) * inner ℝ w v) + 2 * ((1 - a) * u') + 2 * (a * u') := by
      rw [hI, hJ, hinnerwX, hnormeq, hu'def]
      ring
    have e1 : (0:ℝ) < 2 * ((1 - a) * inner ℝ w v) := by
      have : (0:ℝ) < (1 - a) * inner ℝ w v := mul_pos (by linarith) hwv
      linarith
    have e2 : (0:ℝ) ≤ 2 * ((1 - a) * u') :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hu'0)
    have e3 : (0:ℝ) ≤ 2 * (a * u') :=
      mul_nonneg (by norm_num) (mul_nonneg ha0 hu'0)
    have hdiff : (0:ℝ) < ‖w - (a • v + b • n)‖ ^ 2 - ‖w - v‖ ^ 2 := by
      rw [hfinal]
      linarith
    have hlt : ‖w - v‖ < ‖w - (a • v + b • n)‖ :=
      (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (a • v + b • n) w, norm_sub_rev v w]
    exact hlt
  · have hvv2 : inner ℝ (a • v + b • n) (a • v + b • n)
        = a * a * inner ℝ v v + b * b * inner ℝ n n := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hvn, hvn']
      ring
    have hinner_vX : inner ℝ v (a • v + b • n) = a * inner ℝ v v := by
      simp only [inner_add_right, real_inner_smul_right, hvn]
      ring
    have hvv2 : inner ℝ (a • v + b • n) (a • v + b • n)
        = a * a * inner ℝ v v + b * b * inner ℝ n n := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hvn, hvn']
      ring
    rw [hbdef] at hvv2
    have hdd : ‖v - (a • v + b • n)‖ ^ 2 = 2 * ((1 - a) * inner ℝ v v) := by
      rw [show ‖v - (a • v + b • n)‖ ^ 2
          = inner ℝ (v - (a • v + b • n)) (v - (a • v + b • n))
          from (real_inner_self_eq_norm_sq _).symm]
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hvn, hvn']
      have hcancel : inner ℝ v v * a ^ 2 + b ^ 2 * inner ℝ n n = inner ℝ v v := by
        have h2 : b ^ 2 * inner ℝ n n = (1 - a * a) * inner ℝ v v := by
          rw [pow_two, hbdef]
        rw [h2]
        ring
      linarith [hcancel]
    have hsub : 1 - a ≤ d ^ 2 / (4 * inner ℝ v v) := by
      have := le_max_right (0:ℝ) (1 - d ^ 2 / (4 * inner ℝ v v))
      linarith
    have hmul : (1 - a) * inner ℝ v v ≤ d ^ 2 / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hsub hvv.le
      have h2 : (d ^ 2 / (4 * inner ℝ v v)) * inner ℝ v v = d ^ 2 / 4 := by
        field_simp
      linarith [h1, h2]
    have hbound : ‖v - (a • v + b • n)‖ ^ 2 < d ^ 2 := by
      rw [hdd]
      have h2 : (0:ℝ) < d ^ 2 := pow_pos hd 2
      have hle : 2 * ((1 - a) * inner ℝ v v) ≤ d ^ 2 / 2 := by linarith
      linarith
    have hlt : ‖v - (a • v + b • n)‖ < d :=
      (sq_lt_sq₀ (norm_nonneg _) hd.le).mp hbound
    rw [dist_eq_norm]
    exact hlt

/-! ### 2c''. FCDJDOT 柱②门钥匙：JBDNJJB 正弦符号桥（2026-10-12 A6 续三波）

HOL FNJLBXS-compiled.hl:714-745 `not_surrounded_imp_on_one_side_of_plane` 的
v cross w 分离平面路线需要两件上游：正弦/叉积符号桥（Trigonometry2.JBDNJJB 的
符号内容，trig2.hl:4253，全树零移植——LA5 `SIN_AZIM_MUTUAL_CROSS` 与 LA9
`JBDNJJB3_p9` 均为开放债务，不可依赖）与 azim/dart 机器
（`DART1_NOT_COLLINEAR` + `azim_ge_azim_dart`，下一块落地）。

本块路线：`azim_master`（Geom/Azim.lean，零债）给出 azim 在任意右手 ON 标架
下的极坐标表示，取 `exists_on3_eq_smul` 的标架（u 轴向），从表示式纯代数推出
`(u cross v)·w = ‖u‖·r1·r2·sin(azim 0 u v w)`，其中 `‖u‖ > 0`、`r1 > 0`
（非共线支）、`r2 ≥ 0`（azim_master 的条件正性）；w 共线退化支
`azim = 0` 且叉积点 w = 0，取 c = 0。符号端 `π ≤ azim < 2π ⟹ sin ≤ 0`
（HOL SIN_NEG_PI_2PI，`Real.sin_nonneg_of_nonneg_of_le_pi` + 移角）。
-/


/-! ## V3 → Pi 的 coe 辅助（rfl 桥） -/

private theorem fnCoeZero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem fnCoeSub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem fnCoeAdd (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

private theorem fnCoeSmul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • ((a : V3) : Fin 3 → ℝ) := rfl

/-! ## Pi 侧 crossProduct 分配律 -/

private theorem fnCrossAdd (p q r : Fin 3 → ℝ) :
    crossProduct (p + q) r = crossProduct p r + crossProduct q r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.add_apply]

private theorem fnCrossSmul (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

private theorem fnCrossAdd' (p q r : Fin 3 → ℝ) :
    crossProduct p (q + r) = crossProduct p q + crossProduct p r := by
  rw [← cross_anticomm (q + r) p, ← cross_anticomm q p, ← cross_anticomm r p, fnCrossAdd,
    neg_add]

private theorem fnCrossSmul' (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct p (t • r) = t • crossProduct p r := by
  rw [← cross_anticomm (t • r) p, fnCrossSmul, ← cross_anticomm p r, smul_neg, neg_neg]

/-! ## 右手 ON 标架的循环 cross 恒等式 -/

private theorem fnCrossE3E1 {f1 f2 f3 : V3} (h : Orthonormal3 f1 f2 f3) :
    crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ) = (f2 : Fin 3 → ℝ) := by
  have hXf1 : (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) ⬝ᵥ (f1 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  have hXf2 : (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) ⬝ᵥ (f2 : Fin 3 → ℝ) = 1 := by
    rw [dotProduct_comm, triple_product_permutation, on3_cross h]
    have h33 : ((f3 : Fin 3 → ℝ)) ⬝ᵥ ((f3 : Fin 3 → ℝ)) = 1 := h.2.2.1
    exact h33
  have hXf3 : (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) ⬝ᵥ (f3 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  have hexp := on3_expand h (WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) : V3)
  rw [hXf1, hXf2, hXf3] at hexp
  simp only [zero_smul, one_smul, zero_add, add_zero] at hexp
  have hcoe : ((WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) : V3) :
      Fin 3 → ℝ) = (f2 : Fin 3 → ℝ) := by rw [hexp]
  rwa [coe_toLp] at hcoe

private theorem fnCrossE3E2 {f1 f2 f3 : V3} (h : Orthonormal3 f1 f2 f3) :
    crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ) = -(f1 : Fin 3 → ℝ) := by
  have hXf1 : (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) ⬝ᵥ (f1 : Fin 3 → ℝ) = -1 := by
    rw [dotProduct_comm, triple_product_permutation,
      ← cross_anticomm (f1 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ), dotProduct_comm, neg_dotProduct,
      on3_cross h]
    have h33 : ((f3 : Fin 3 → ℝ)) ⬝ᵥ ((f3 : Fin 3 → ℝ)) = 1 := h.2.2.1
    rw [h33]
  have hXf2 : (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) ⬝ᵥ (f2 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  have hXf3 : (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) ⬝ᵥ (f3 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  have hexp := on3_expand h (WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) : V3)
  rw [hXf1, hXf2, hXf3] at hexp
  simp only [zero_smul, zero_add, add_zero, neg_smul, one_smul] at hexp
  have hcoe : ((WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) : V3) :
      Fin 3 → ℝ) = -(f1 : Fin 3 → ℝ) := by
    rw [hexp]
    rfl
  rwa [coe_toLp] at hcoe

/-! ## 主恒等式：cross·w = c · sin(azim)（c ≥ 0；JBDNJJB 的符号内容） -/

private theorem crossDotEqSmulSin (u v w : V3) (hu : u ≠ 0) (hnc : ¬ Collinear3 0 u v) :
    ∃ c : ℝ, 0 ≤ c ∧
      (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)
        = c * Real.sin (azim 0 u v w) := by
  classical
  obtain ⟨g1, g2, g3, hf, halign⟩ := exists_on3_eq_smul u hu
  have huc : (u : Fin 3 → ℝ) = ‖u‖ • (g3 : Fin 3 → ℝ) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) halign
    simpa using h
  have hax : (u - 0 : V3) = dist u 0 • g3 := by
    rw [dist_eq_norm]
    simpa using halign
  have hθ := azim_master 0 u v w
  obtain ⟨-, hθ2, hmain⟩ := hθ
  obtain ⟨k1, k2, hframe⟩ := hmain
  obtain ⟨ψ, r1, r2, hv, hw, hr1, hr2⟩ := hframe g1 g2 g3 hf hax hu
  have hr1pos : 0 < r1 := hr1 hnc
  -- ON 标架正交坐标（Pi 侧）
  have o11 : ((g1 : Fin 3 → ℝ)) ⬝ᵥ ((g1 : Fin 3 → ℝ)) = 1 := hf.1
  have o22 : ((g2 : Fin 3 → ℝ)) ⬝ᵥ ((g2 : Fin 3 → ℝ)) = 1 := hf.2.1
  have o12 : ((g1 : Fin 3 → ℝ)) ⬝ᵥ ((g2 : Fin 3 → ℝ)) = 0 := hf.2.2.2.1
  have o13 : ((g1 : Fin 3 → ℝ)) ⬝ᵥ ((g3 : Fin 3 → ℝ)) = 0 := hf.2.2.2.2.1
  have o23 : ((g2 : Fin 3 → ℝ)) ⬝ᵥ ((g3 : Fin 3 → ℝ)) = 0 := hf.2.2.2.2.2.1
  have o21 : ((g2 : Fin 3 → ℝ)) ⬝ᵥ ((g1 : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm]
    exact o12
  have o1u : ((g1 : Fin 3 → ℝ)) ⬝ᵥ (u : Fin 3 → ℝ) = 0 := by
    rw [huc, dotProduct_smul, o13, smul_zero]
  have o2u : ((g2 : Fin 3 → ℝ)) ⬝ᵥ (u : Fin 3 → ℝ) = 0 := by
    rw [huc, dotProduct_smul, o23, smul_zero]
  -- v/w 的 g-坐标（Pi 侧）
  have hv' : (v : Fin 3 → ℝ) = (r1 * Real.cos ψ) • (g1 : Fin 3 → ℝ)
      + (r1 * Real.sin ψ) • (g2 : Fin 3 → ℝ) + k1 • (u : Fin 3 → ℝ) := by
    have hcc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hv
    rw [fnCoeAdd, fnCoeSmul, fnCoeAdd, fnCoeSmul, fnCoeSmul, fnCoeSub, fnCoeZero,
      sub_zero, fnCoeSub, fnCoeZero, sub_zero] at hcc
    exact hcc
  have hw' : (w : Fin 3 → ℝ) = (r2 * Real.cos (ψ + azim 0 u v w)) • (g1 : Fin 3 → ℝ)
      + (r2 * Real.sin (ψ + azim 0 u v w)) • (g2 : Fin 3 → ℝ)
      + k2 • (u : Fin 3 → ℝ) := by
    have hcc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hw
    rw [fnCoeAdd, fnCoeSmul, fnCoeAdd, fnCoeSmul, fnCoeSmul, fnCoeSub, fnCoeZero,
      sub_zero, fnCoeSub, fnCoeZero, sub_zero] at hcc
    exact hcc
  -- W 的 g1/g2 坐标
  have hd1 : (g1 : Fin 3 → ℝ) ⬝ᵥ (w : Fin 3 → ℝ)
      = r2 * Real.cos (ψ + azim 0 u v w) := by
    rw [hw', dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_smul]
    rw [o11, o12, o1u]
    ring
  have hd2 : (g2 : Fin 3 → ℝ) ⬝ᵥ (w : Fin 3 → ℝ)
      = r2 * Real.sin (ψ + azim 0 u v w) := by
    rw [hw', dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_smul]
    rw [o21, o22, o2u]
    ring
  -- cross 积展开
  have hcross : crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      = (‖u‖ * (r1 * Real.cos ψ)) • (g2 : Fin 3 → ℝ)
        + (-(‖u‖ * (r1 * Real.sin ψ))) • (g1 : Fin 3 → ℝ) := by
    rw [hv', huc, fnCrossSmul, fnCrossAdd', fnCrossAdd', fnCrossSmul', fnCrossSmul',
      fnCrossSmul', fnCrossSmul', fnCrossE3E1 hf, fnCrossE3E2 hf, cross_self, smul_zero,
      smul_zero, add_zero, smul_add, smul_smul, smul_neg, smul_neg, smul_smul, neg_smul]
  have hkey : (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)
      = (‖u‖ * r1 * r2) * Real.sin (azim 0 u v w) := by
    rw [hcross, add_dotProduct, neg_smul, neg_dotProduct, smul_dotProduct,
      smul_dotProduct, hd2, hd1]
    have hsub : Real.sin ((ψ + azim 0 u v w) - ψ)
        = Real.sin (ψ + azim 0 u v w) * Real.cos ψ
          - Real.cos (ψ + azim 0 u v w) * Real.sin ψ := Real.sin_sub _ _
    rw [show (ψ + azim 0 u v w) - ψ = azim 0 u v w from by ring] at hsub
    rw [hsub]
    ring
  by_cases hcolw : Collinear3 0 u w
  · -- 退化支：w 在轴上，sin azim = 0 且 cross·w = 0
    have hazim0 : azim 0 u v w = 0 := by
      show (if Collinear3 0 u v ∨ Collinear3 0 u w then (0:ℝ)
        else Classical.epsilon (AzimSpec 0 u v w)) = 0
      rw [if_pos (Or.inr hcolw)]
    obtain ⟨kk, hkw⟩ := (collinear3_iff_smul hu).mp hcolw
    have haxw : (w : Fin 3 → ℝ) = kk • (u : Fin 3 → ℝ) := by
      have hcc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hkw
      rw [fnCoeSub, fnCoeZero, sub_zero, fnCoeSmul, fnCoeSub, fnCoeZero, sub_zero] at hcc
      exact hcc
    refine ⟨0, le_refl 0, ?_⟩
    rw [hazim0, Real.sin_zero, haxw, dotProduct_smul, dotProduct_comm,
      dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ), smul_zero]
    ring
  · refine ⟨‖u‖ * r1 * r2,
      mul_nonneg (mul_nonneg (norm_nonneg u) hr1pos.le) (hr2 hcolw).le, hkey⟩

/-- 正弦符号桥（FNJLBXS-compiled.hl:714-745 消费的 JBDNJJB 符号内容 +
SIN_NEG_PI_2PI）：`π ≤ azim 0 u v w` 时 `u cross v · w ≤ 0`。 -/
private theorem sinAzimCrossSign (u v w : V3) (hu : u ≠ 0) (hnc : ¬ Collinear3 0 u v)
    (hge : Real.pi ≤ azim 0 u v w) :
    (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ) ≤ 0 := by
  obtain ⟨c, hc0, hcid⟩ := crossDotEqSmulSin u v w hu hnc
  have hθ2 := azim_lt_two_pi 0 u v w
  have h1 : 0 ≤ azim 0 u v w - Real.pi := by linarith
  have h2 : azim 0 u v w - Real.pi ≤ Real.pi := by linarith
  have h3 := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  have h4 : Real.sin (azim 0 u v w) = -Real.sin (azim 0 u v w - Real.pi) := by
    rw [show azim 0 u v w = (azim 0 u v w - Real.pi) + Real.pi from by ring]
    rw [Real.sin_add]
    simp
  have hs : Real.sin (azim 0 u v w) ≤ 0 := by rw [h4]; linarith
  rw [hcid]
  exact mul_nonpos_of_nonneg_of_nonpos hc0 hs


/-! ### 2c′′′. FCDJDOT 柱②门钥钥匙落地（2026-10-12 A6 续三波）

**门钥匙① `dart1NotCollinear`**（HOL Hypermap_and_fan.hl:2679
`DART1_NOT_COLLINEAR`）：真 dart 的 `{v,w} ∈ E` 经 fan6 直接给出
`¬Collinear3 0 v w`（HOL 经 PAIR_IN_DART1_OF_FAN 展开，Lean 的
`dart1OfFan` 定义即集合形式，零内容）。

**门钥匙② `azimGeAzimDart`**（HOL Fatugpd.hl:394 `azim_ge_azim_dart`）：
FAN + 双邻居 + 互异下 `azim 0 w u v2 ≥ azimDart V E (w, u)`。路线：
card 计数（两互异邻居 ⟹ ncard > 1，`Set.ncard_le_ncard`）展开
`azimFan` 的 if 取 σ-分支，`SIGMA_FAN`（Fan.lean:317，零债）第三分量
即最小性。

**主件 `notSurroundedImpOnOneSideOfPlane`**（FNJLBXS-compiled.hl:714-745
`not_surrounded_imp_on_one_side_of_plane`）：非 surrounded 取 azimDart ≥ π
的 dart（v, w），取 n := v cross w（`fnCrossNeZero` 经
`crossProduct_ne_zero_iff_linearIndependent` + pair 线性无关证 n ≠ 0，
即 HOL CROSS_EQ_0 反向），`inner v n = 0`（dot_self_cross），任一邻居
w2 按 w2 = w 分支（dot_cross_self = 0）或 azim_ge_azim_dart 链 +
`sinAzimCrossSign` 得 inner w2 n ≤ 0。
-/

/-! ## 门钥匙①：DART1_NOT_COLLINEAR（Hypermap_and_fan.hl:2679） -/

private theorem dart1NotCollinear {V : Set V3} {E : Set (Set V3)} {v w : V3}
    (hfan : FAN 0 V E) (hd : (v, w) ∈ dart1OfFan V E) : ¬ Collinear3 0 v w :=
  fan_not_collinear hfan hd

/-! ## ¬collinear {0,v,w} 的射线性展开与 cross 非零（CROSS_EQ_0 反向） -/

private theorem fnNotCollinearSmul {v w : V3}
    (h : ¬ Collinear ℝ ({0, v, w} : Set V3)) :
    v ≠ 0 ∧ w ≠ 0 ∧ ∀ c : ℝ, w ≠ c • v := by
  have hv0 : v ≠ 0 := by
    intro he
    refine h ?_
    have hset : ({0, v, w} : Set V3) = ({0, w} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ (0:V3) w
  have hw0 : w ≠ 0 := by
    intro he
    refine h ?_
    have hset : ({0, v, w} : Set V3) = ({0, v} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ (0:V3) v
  refine ⟨hv0, hw0, ?_⟩
  intro c hc
  refine h ?_
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0:V3), v, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | hx
  · exact ⟨0, by rw [zero_smul, vadd_eq_add, add_zero]⟩
  rcases hx with rfl | hx
  · exact ⟨1, by rw [one_smul, vadd_eq_add, add_zero]⟩
  · exact ⟨c, by rw [hx, hc, vadd_eq_add, add_zero]⟩

private theorem fnCoeInj {x y : V3} (h : (x : Fin 3 → ℝ) = (y : Fin 3 → ℝ)) : x = y := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y, h]

private theorem fnCrossNeZero {v w : V3} (h : ¬ Collinear3 0 v w) :
    (WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3) ≠ 0 := by
  obtain ⟨hv0, hw0, hc⟩ := fnNotCollinearSmul h
  have hindep : LinearIndependent ℝ ![(v : Fin 3 → ℝ), (w : Fin 3 → ℝ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hv3 : (s • v + t • w : V3) = 0 := by
      apply fnCoeInj
      rw [WithLp.ofLp_add, fnCoeSmul, fnCoeSmul]
      simpa using hst
    rcases eq_or_ne s 0 with hs0 | hs0
    · rw [hs0, zero_smul, zero_add, smul_eq_zero] at hv3
      rcases hv3 with h1 | h1
      · exact ⟨hs0, h1⟩
      · exact absurd h1 hw0
    · rcases eq_or_ne t 0 with ht0 | ht0
      · rw [ht0, zero_smul, add_zero, smul_eq_zero] at hv3
        rcases hv3 with h1 | h1
        · exact absurd h1 hs0
        · exact absurd h1 hv0
      · have hyw : w = (-(s / t)) • v := by
          have hst' : t • w = -(s • v) := eq_neg_iff_add_eq_zero.mpr
            (by rw [add_comm]; exact hv3)
          have h2 := congrArg (fun z : V3 => (t⁻¹) • z) hst'
          rw [inv_smul_smul₀ ht0, smul_neg, smul_smul] at h2
          have hsc : (t:ℝ)⁻¹ * s = s / t := by field_simp
          rw [h2, hsc, neg_smul]
        exact (hc (-(s / t)) hyw).elim
  intro hzero
  have hcne : crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ) ≠ 0 :=
    (crossProduct_ne_zero_iff_linearIndependent (v := (v : Fin 3 → ℝ))
      (w := (w : Fin 3 → ℝ))).mpr hindep
  have hcoe : ((WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3) :
      Fin 3 → ℝ) = crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ) := coe_toLp _
  rw [← hcoe, hzero] at hcne
  simpa using hcne

/-! ## dot_toLp 的右置形 -/

private theorem fnDotToLpRight (p : Fin 3 → ℝ) (y : V3) :
    y ⬝ᵥ (WithLp.toLp 2 p : V3) = (y : Fin 3 → ℝ) ⬝ᵥ p := by
  rw [dotProduct_comm, dot_toLp, dotProduct_comm]

/-! ## 门钥匙②：azim_ge_azim_dart（Fatugpd.hl:394） -/

private theorem azimGeAzimDart {V : Set V3} {E : Set (Set V3)} {w u v2 : V3}
    (hfan : FAN 0 V E) (hu : u ∈ setOfEdge w V E) (hv2 : v2 ∈ setOfEdge w V E)
    (hwu : w ≠ u) (hvu : v2 ≠ u) : azim 0 w u v2 ≥ azimDart V E (w, u) := by
  have hVfin : V.Finite := hfan.2.2.1.1
  have huv2 : u ≠ v2 := fun he => hvu he.symm
  have hne : setOfEdge w V E ≠ {u} := by
    intro he
    rw [he] at hv2
    exact hvu (Set.mem_singleton_iff.mp hv2)
  have hdart : azimDart V E (w, u) = Fan.azimFan 0 V E w u := by
    show (if (w, u).1 = (w, u).2 then (2:ℝ) * Real.pi
      else Fan.azimFan 0 V E (w, u).1 (w, u).2) = Fan.azimFan 0 V E w u
    rw [if_neg hwu]
  rw [hdart]
  show (if (setOfEdge w V E).ncard > 1 then azim 0 w u (sigmaFan 0 V E w u)
    else (2:ℝ) * Real.pi) ≤ azim 0 w u v2
  by_cases hcard : (setOfEdge w V E).ncard > 1
  · rw [if_pos hcard]
    exact (SIGMA_FAN hne hfan hu).2.2 v2 hv2 hvu
  · push_neg at hcard
    exfalso
    have hsub2 : ({u, v2} : Set V3) ⊆ setOfEdge w V E := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | hx
      · exact hu
      · rw [hx]
        exact hv2
    have hle : ({u, v2} : Set V3).ncard ≤ (setOfEdge w V E).ncard :=
      Set.ncard_le_ncard hsub2 (remark_finite_fan1 w V E hVfin)
    have h2 : ({u, v2} : Set V3).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simp [huv2] : u ∉ ({v2} : Set V3))]
      simp
    omega

/-! ## 主件：not_surrounded_imp_on_one_side_of_plane（FNJLBXS-compiled.hl:714-745） -/

private theorem notSurroundedImpOnOneSideOfPlane {V : Set V3} {E : Set (Set V3)} {v : V3}
    (hfan : FAN 0 V E) (hv : v ∈ V) (hiso : setOfEdge v V E ≠ ∅)
    (hns : ¬ surroundedNode V E v) :
    ∃ n : V3, n ≠ 0 ∧ inner ℝ v n = 0 ∧ ∀ w ∈ setOfEdge v V E, inner ℝ w n ≤ 0 := by
  classical
  unfold surroundedNode at hns
  push_neg at hns
  obtain ⟨d, hdD, hd1v, hdge⟩ := hns
  have hd : (v, d.2) ∈ dartOfFan V E := by rw [← hd1v]; exact hdD
  have hd1 : (v, d.2) ∈ dart1OfFan V E := by
    have hunion : dartOfFan V E
        = {x | x.1 = x.2 ∧ x.1 ∈ V ∧ setOfEdge x.1 V E = ∅} ∪ dart1OfFan V E := rfl
    rw [hunion] at hd
    rcases (Set.mem_union _ _ _).mp hd with h0 | h1
    · exact absurd (Set.mem_setOf_eq.mp h0).2.2 hiso
    · exact h1
  have he : {v, d.2} ∈ E := hd1
  have hvw : v ≠ d.2 := edge_ne_of_fan hfan he
  have hncol : ¬ Collinear3 0 v d.2 := fan_not_collinear hfan he
  have hv0 : v ≠ 0 := fun hzero => hfan.2.2.2.1 (hzero ▸ hv)
  have hmem2 : d.2 ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan 0 V E v d.2 hfan).mp he
  have h2dart : azimDart V E d = Fan.azimFan 0 V E v d.2 := by
    show (if d.1 = d.2 then (2:ℝ) * Real.pi
      else Fan.azimFan 0 V E d.1 d.2) = Fan.azimFan 0 V E v d.2
    rw [if_neg (show d.1 ≠ d.2 from by rw [hd1v]; exact hvw), hd1v]
  rw [h2dart] at hdge
  refine ⟨(WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (d.2 : Fin 3 → ℝ)) : V3),
    fnCrossNeZero hncol, ?_, ?_⟩
  · rw [inner_eq_dot, fnDotToLpRight]
    exact dot_self_cross (v : Fin 3 → ℝ) (d.2 : Fin 3 → ℝ)
  · intro w2 hw2
    by_cases hw2d2 : w2 = d.2
    · rw [hw2d2]
      rw [inner_eq_dot, fnDotToLpRight]
      exact le_of_eq (dot_cross_self (v : Fin 3 → ℝ) (d.2 : Fin 3 → ℝ))
    · have h1 := azimGeAzimDart hfan hmem2 hw2 hvw hw2d2
      have heq2 : (v, d.2) = d := by
        calc (v, d.2) = (d.1, d.2) := by rw [hd1v]
          _ = d := Prod.mk.eta
      rw [heq2, h2dart] at h1
      have hge : Real.pi ≤ azim 0 v d.2 w2 := by
        calc Real.pi ≤ Fan.azimFan 0 V E v d.2 := hdge
          _ ≤ azim 0 v d.2 w2 := h1.le
      rw [inner_eq_dot, fnDotToLpRight, dotProduct_comm]
      exact sinAzimCrossSign v d.2 w2 hv0 hncol hge


/-! ### 2c⁗. FCDJDOT 柱②三件中等档（2026-10-12 A6 续四波）

镜像 FNJLBXS-compiled.hl 的 FCDJDOT section 三件：
①`not_surrounded_ECTC`（:1547）——非 surrounded 点经分离平面 + 扰动迁移
（消费 `notSurroundedImpOnOneSideOfPlane` + `perturbationLemma`，双件已在树）；
②`isolated_node_norm_ECTC`（:1631）——孤立点必落球面 `‖v‖ = 2`（单点集取
对径点对 / 多点集径向内移 + 距离-最小值松弛）；
③`not_surrounded_node_norm_ECTC`（:1727）——②经保范双射的转移。 -/

/-! ## ECTC 边隶属刻画（HOL in_set_of_edge_ECTC，FNJLBXS-compiled.hl:504） -/

private theorem ectrPairMem {V : Set V3} {v w : V3} :
    ({v, w} : Set V3) ∈ ECTC V ↔ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w = 2 := by
  constructor
  · rintro ⟨a, b, hab, haV, hbV, hne, hd⟩
    have hv' : v = a ∨ v = b := by
      have hmem : v ∈ ({a, b} : Set V3) := by rw [← hab]; simp
      simpa using hmem
    have hw' : w = a ∨ w = b := by
      have hmem : w ∈ ({a, b} : Set V3) := by rw [← hab]; simp
      simpa using hmem
    rcases hv' with hv1 | hv1
    · have hwb : w = b := by
        rcases hw' with h | h
        · exfalso
          have hmem : b ∈ ({v, w} : Set V3) := by rw [hab]; simp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with h2 | h2
          · exact hne (hv1.symm.trans h2.symm)
          · exact hne (h.symm.trans h2.symm)
        · exact h
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hv1]; exact haV
      · rw [hwb]; exact hbV
      · intro hc
        rw [hv1, hwb] at hc
        exact hne hc
      · rw [hv1, hwb, hd]
    · have hwa : w = a := by
        rcases hw' with h | h
        · exact h
        · exfalso
          have hmem : a ∈ ({v, w} : Set V3) := by rw [hab]; simp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with h2 | h2
          · exact hne (h2.trans hv1)
          · exact hne (h2.trans h)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hv1]; exact hbV
      · rw [hwa]; exact haV
      · intro hc
        rw [hv1, hwa] at hc
        exact hne hc.symm
      · rw [hv1, hwa, dist_comm, hd]
  · rintro ⟨hvV, hwV, hne, hd⟩
    exact ⟨v, w, rfl, hvV, hwV, hne, hd⟩

/-! ## 中档①：not_surrounded_ECTC（FNJLBXS-compiled.hl:1547）

非 surrounded ⟹ 存在保范双射迁移 W 使 f v 孤立。X = v 的 ECTC-邻居，
Y = V \ {v} 中 dist > 2 的点（有限），e 取 Y 上 dist 余量的最小（Y 空取 1），
`perturbationLemma` 沿分离平面 n 把 v 推离全部 X-点得 u；W = {u} ∪ (V \ {v})
换元 v ↦ u：远离性使 W 仍 packing 且 f v = u 无 ECTC 边。 -/

private theorem notSurroundedECTC {V : Set V3} (hpack : Packing V) (hsub : V ⊆ ballAnnulus)
    {v : V3} (hv : v ∈ V) (hns : ¬ surroundedNode V (ECTC V) v) :
    ∃ W : Set V3, ∃ f : V3 → V3, Set.BijOn f V W ∧ Packing W ∧ W ⊆ ballAnnulus ∧
      (∀ u ∈ V, ‖u‖ = ‖f u‖) ∧ setOfEdge (f v) W (ECTC W) = ∅ := by
  classical
  have hfin : V.Finite := packingFiniteOfBallAnnulus hpack hsub
  have hVne : V ≠ ∅ := fun hmem => by rw [hmem] at hv; exact hv.elim
  have hvb : v ∈ ballAnnulus := hsub hv
  obtain ⟨hvh2, hvh0⟩ := ContraFan.inBallAnnulus hvb
  -- ECTC-fan（HOL UBHDEUU2：contraveningFanTl + ECTC ⊆ ESTD + CTVTAQA）
  have hECTCsub : ECTC V ⊆ ESTD V := by
    intro e he
    obtain ⟨a, b, rfl, ha, hb, hne, hd⟩ := he
    exact ⟨a, b, rfl, ha, hb, hne, by rw [hd]; norm_num [ContraFan.two_h0]⟩
  have hfan : FAN 0 V (ECTC V) :=
    CTVTAQA (ContraFan.contraveningFanTl V hpack hsub hVne) hECTCsub
  by_cases hX0 : setOfEdge v V (ECTC V) = ∅
  · -- 已孤立：恒等迁移
    refine ⟨V, fun x => x, ⟨fun x hx => hx, fun x y _ _ hxy => hxy, fun x hx => ⟨x, hx, rfl⟩⟩,
      hpack, hsub, fun u _ => rfl, hX0⟩
  obtain ⟨n, hn0, hvn, hwn⟩ := notSurroundedImpOnOneSideOfPlane hfan hv hX0 hns
  have inX : ∀ x : V3, x ∈ setOfEdge v V (ECTC V) ↔ (x ∈ V ∧ x ≠ v ∧ dist x v = 2) := by
    intro x
    simp only [setOfEdge, Set.mem_setOf_eq, ectrPairMem]
    constructor
    · rintro ⟨⟨-, hxV, hvx, hd⟩, -⟩
      exact ⟨hxV, fun hh => hvx hh.symm, by rw [dist_comm]; exact hd⟩
    · rintro ⟨hxV, hxv, hd⟩
      exact ⟨⟨hv, hxV, fun hh => hxv hh.symm, by rw [dist_comm]; exact hd⟩, hxV⟩
  have hXne : (setOfEdge v V (ECTC V)).Nonempty := Set.nonempty_iff_ne_empty.mpr hX0
  obtain ⟨Y, hYdef⟩ : ∃ Y : Set V3, Y = (V \ {v}) \ setOfEdge v V (ECTC V) := ⟨_, rfl⟩
  have finY : Y.Finite := by
    rw [hYdef]
    exact (hfin.subset Set.sdiff_subset).subset (Set.sdiff_subset)
  have inY : ∀ y : V3, y ∈ Y ↔ (y ∈ V ∧ y ≠ v ∧ 2 < dist y v) := by
    intro y
    rw [hYdef, Set.mem_diff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hyV, hyv⟩, hx⟩
      have h2 : 2 ≤ dist y v := hpack.dist_ge_two hyV hv hyv
      rcases lt_or_eq_of_le h2 with hlt | heq
      · exact ⟨hyV, hyv, hlt⟩
      · exact absurd ((inX y).mpr ⟨hyV, hyv, heq.symm⟩) hx
    · rintro ⟨hyV, hyv, hgt⟩
      refine ⟨⟨hyV, fun hh => hyv (Set.mem_singleton_iff.mp hh)⟩, fun hx => ?_⟩
      obtain ⟨-, -, hd⟩ := (inX y).mp hx
      linarith
  -- e：Y 空取 1，非空取 dist 余量最小；0 < e ≤ 1 且 Y 上 e + 2 ≤ dist y v
  obtain ⟨e, he0, he1, hYbound⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ y ∈ Y, e + 2 ≤ dist y v := by
    by_cases hY0 : Y = ∅
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      rw [hY0]
      rintro y hy
      exact absurd hy (Set.notMem_empty y)
    · have hYpos : ∀ y ∈ Y, 0 < dist y v - 2 := by
        intro y hy
        have hy' := (inY y).mp hy
        linarith
      obtain ⟨y0, hy0Y⟩ := Set.nonempty_iff_ne_empty.mpr hY0
      have hTne : ((finY.toFinset.image fun y : V3 => dist y v - 2)).Nonempty :=
        ⟨dist y0 v - 2, Finset.mem_image.mpr ⟨y0, finY.mem_toFinset.mpr hy0Y, rfl⟩⟩
      have hmin' : ∀ z ∈ finY.toFinset.image (fun y : V3 => dist y v - 2),
          (finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne ≤ z := by
        intro z hz
        exact Finset.min'_le (finY.toFinset.image (fun y : V3 => dist y v - 2)) z hz
      have hminMem : (finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne
          ∈ finY.toFinset.image (fun y : V3 => dist y v - 2) := Finset.min'_mem _ hTne
      obtain ⟨y1, hy1, hy1v⟩ := Finset.mem_image.mp hminMem
      have hy1v' : (finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne
          = dist y1 v - 2 := hy1v.symm
      have hmpos : 0 < (finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne := by
        rw [hy1v']
        exact hYpos y1 (finY.mem_toFinset.mp hy1)
      refine ⟨min ((finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne) 1,
        lt_min hmpos (by norm_num), min_le_right _ _, ?_⟩
      intro y hy
      have hz' : (finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne
          ≤ dist y v - 2 :=
        hmin' _ (Finset.mem_image.mpr ⟨y, finY.mem_toFinset.mpr hy, rfl⟩)
      have he' : min ((finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne) 1
          ≤ (finY.toFinset.image (fun y : V3 => dist y v - 2)).min' hTne :=
        min_le_left _ _
      linarith
  -- 扰动前提：X 上 0 < w·v（dot_pos_lemma）+ w·n ≤ 0（分离平面）
  have hXv : ∀ w ∈ setOfEdge v V (ECTC V), 0 < inner ℝ w v := by
    intro w hw
    obtain ⟨hwV, hwv, hd⟩ := (inX w).mp hw
    have hwb : w ∈ ballAnnulus := hsub hwV
    have hdle : dist w v ≤ 2 * h0 := by
      rw [hd]
      have h1 : (1:ℝ) ≤ h0 := by norm_num [h0]
      linarith
    exact ContraFan.dot_pos_lemma hwb hvb hdle
  obtain ⟨u, hunorm, hdlt, hduv⟩ :=
    perturbationLemma e he0 hn0 hvn (setOfEdge v V (ECTC V))
      (fun w hw => ⟨hwn w hw, hXv w hw⟩)
  have hvu : v ≠ u := by
    intro hcon
    obtain ⟨x, hx⟩ := hXne
    have h1 := hdlt x hx
    rw [hcon] at h1
    exact lt_irrefl _ h1
  have huV : u ∉ V := by
    intro hu
    have h2 := hpack.dist_ge_two hu hv (fun hh => hvu hh.symm)
    have h3 : dist v u < e := hduv
    rw [dist_comm] at h3
    linarith
  -- u 离 V \ {v} 中每点 > 2（ packing 与 u-孤立共用）
  have hgt : ∀ z : V3, z ∈ V → z ≠ v → 2 < dist u z := by
    intro z hz hzv
    by_cases hzX : z ∈ setOfEdge v V (ECTC V)
    · have h2 : dist z v = 2 := ((inX z).mp hzX).2.2
      calc (2:ℝ) = dist v z := by rw [dist_comm]; exact h2.symm
        _ < dist u z := hdlt z hzX
    · have hyz : z ∈ Y := by
        rw [hYdef, Set.mem_diff, Set.mem_diff, Set.mem_singleton_iff]
        exact ⟨⟨hz, hzv⟩, hzX⟩
      have hbound := hYbound z hyz
      have htri : dist z v ≤ dist z u + dist u v := dist_triangle z u v
      have hdc : dist u v = dist v u := dist_comm u v
      rw [dist_comm]
      linarith
  refine ⟨insert u (V \ {v}), fun x => if x = v then u else x, ?_, ?_, ?_, ?_, ?_⟩

  · -- BijOn
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      show (if x = v then u else x) ∈ insert u (V \ {v})
      by_cases hxv : x = v
      · rw [if_pos hxv]
        exact Set.mem_insert u (V \ {v})
      · rw [if_neg hxv]
        exact Set.mem_insert_of_mem u ⟨hx, hxv⟩
    · intro x hx y hy hxy
      have hxy' : (if x = v then u else x) = (if y = v then u else y) := hxy
      by_cases hxv : x = v
      · by_cases hyv : y = v
        · exact hxv.trans hyv.symm
        · rw [if_pos hxv, if_neg hyv] at hxy'
          exact absurd (hxy'.symm ▸ hy) huV
      · by_cases hyv : y = v
        · rw [if_neg hxv, if_pos hyv] at hxy'
          exact absurd (hxy' ▸ hx) huV
        · rw [if_neg hxv, if_neg hyv] at hxy'
          exact hxy'
    · intro z hz
      by_cases hzu : z = u
      · refine ⟨v, hv, ?_⟩
        show (if v = v then u else v) = z
        rw [if_pos rfl, hzu]
      · have hz' : z ∈ V ∧ z ≠ v := by
          rcases Set.mem_insert_iff.mp hz with h | h
          · exact absurd h hzu
          · exact ⟨h.1, fun hh => h.2 (by rw [hh]; simp)⟩
        refine ⟨z, hz'.1, ?_⟩
        show (if z = v then u else z) = z
        rw [if_neg hz'.2]
  · -- packing：u 离 V \ {v} 中每点 > 2
    intro a ha b hb hab
    rcases Set.mem_insert_iff.mp ha with ha0 | ha' <;>
      rcases Set.mem_insert_iff.mp hb with hb0 | hb'
    · rw [ha0, hb0]
    · have h2 : (2:ℝ) ≤ dist a b := by
        rw [ha0]
        exact le_of_lt (hgt b hb'.1 hb'.2)
      exact absurd hab (not_lt.mpr h2)
    · have h2 : (2:ℝ) ≤ dist a b := by
        rw [hb0, dist_comm]
        exact le_of_lt (hgt a ha'.1 ha'.2)
      exact absurd hab (not_lt.mpr h2)
    · exact hpack a ha'.1 b hb'.1 hab
  · -- ⊆ ballAnnulus：u 与 v 等长
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx0 | hx'
    · rw [hx0, ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
        dist_zero_right]
      refine ⟨?_, ?_⟩
      · rw [hunorm]; exact hvh0
      · rw [hunorm]; exact not_lt.mpr hvh2
    · exact hsub hx'.1
  · -- 保范
    intro x hx
    show ‖x‖ = ‖(if x = v then u else x)‖
    by_cases hxv : x = v
    · rw [if_pos hxv, hunorm, hxv]
    · rw [if_neg hxv]
  · -- f v = u 孤立
    show setOfEdge (if v = v then u else v) (insert u (V \ {v}))
      (ECTC (insert u (V \ {v}))) = ∅
    rw [if_pos rfl, setOfEdge, Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨he, hzW⟩ := hz
    obtain ⟨-, hzW', huz, hduz⟩ := ectrPairMem.mp he
    have hzu : z ≠ u := fun hh => huz hh.symm
    have hz' : z ∈ V \ {v} := by
      rcases Set.mem_insert_iff.mp hzW with h | h
      · exact absurd h hzu
      · exact h
    have h2 := hgt z hz'.1 hz'.2
    rw [hduz] at h2
    linarith

/-! ## 中档②：isolated_node_norm_ECTC（FNJLBXS-compiled.hl:1631）

v 无 ECTC-邻居 ⟹ ‖v‖ = 2。反设 2 < ‖v‖：单点集取对径点对 {w, -w}；
否则 D = {dist(u,v) - 2 | u ∈ V, u ≠ v} 有限非空且全正，取最小 m，把 v 径向
内移 (1-e)·v（e = min(m, ‖v‖-2)/‖v‖）：新点仍在 annulus、与其余点距离 ≥ 2，
scriptL 严格增大（lmfun 在 ≤ h0 段递减），与最大性矛盾。 -/

private theorem isolatedNodeNormECTC {V : Set V3} (hpack : Packing V) (hsub : V ⊆ ballAnnulus)
    (hmax : ∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL V)
    {v : V3} (hv : v ∈ V) (hedges : setOfEdge v V (ECTC V) = ∅) : ‖v‖ = 2 := by
  classical
  have hvb : v ∈ ballAnnulus := hsub hv
  obtain ⟨hvh2, hvh0⟩ := ContraFan.inBallAnnulus hvb
  by_cases hgt2 : 2 < ‖v‖
  · exfalso
    have hfin : V.Finite := packingFiniteOfBallAnnulus hpack hsub
    have hnormpos : (0:ℝ) < ‖v‖ := by linarith
    by_cases hV0 : V = {v}
    · -- 情形 A：单点集，{w, -w} 的 scriptL = 2 > 1 ≥ scriptL V
      set w : V3 := (2 / ‖v‖) • v with hwdef
      have hvne : ‖v‖ ≠ 0 := ne_of_gt hnormpos
      have hwnorm : ‖w‖ = 2 := by
        rw [hwdef, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) hnormpos)]
        field_simp
      have hwne : w ≠ -w := by
        intro hcon
        have hsum : w + w = 0 := eq_neg_iff_add_eq_zero.mp hcon
        have hprod : (2:ℝ) • w = (0:V3) := by rw [two_smul ℝ]; exact hsum
        have hnorm0 : ‖w‖ = 0 := by
          have h2 : ‖(2:ℝ) • w‖ = ‖(0:V3)‖ := by rw [hprod]
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (show (0:ℝ) < 2 by norm_num), norm_zero] at h2
          linarith
        rw [hwnorm] at hnorm0
        norm_num at hnorm0
      have h4 : dist w (-w) = 4 := by
        have he : w - (-w) = (2:ℝ) • w := by rw [sub_eq_add_neg, neg_neg, ← two_smul ℝ]
        rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show (0:ℝ) < 2 by norm_num), hwnorm]
        norm_num
      have hWpack : Packing ({w, -w} : Set V3) := by
        intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with ha0 | ha1
        · rcases Set.mem_insert_iff.mp hb with hb0 | hb1
          · rw [ha0, hb0]
          · rw [ha0] at hab
            have hb2 : b = -w := Set.mem_singleton_iff.mp hb1
            rw [hb2, h4] at hab
            norm_num at hab
        · rcases Set.mem_insert_iff.mp hb with hb0 | hb1
          · have ha2 : a = -w := Set.mem_singleton_iff.mp ha1
            rw [ha2] at hab
            rw [hb0, dist_comm, h4] at hab
            norm_num at hab
          · have ha2 : a = -w := Set.mem_singleton_iff.mp ha1
            have hb2 : b = -w := Set.mem_singleton_iff.mp hb1
            rw [ha2, hb2]
      have hWsub : ({w, -w} : Set V3) ⊆ ballAnnulus := by
        intro x hx
        rcases Set.mem_insert_iff.mp hx with hx0 | hx1
        · rw [hx0, ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
            dist_zero_right, hwnorm]
          exact ⟨by norm_num [ContraFan.two_h0], not_lt.mpr le_rfl⟩
        · have hx2 : x = -w := Set.mem_singleton_iff.mp hx1
          rw [hx2, ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
            dist_zero_right, norm_neg, hwnorm]
          exact ⟨by norm_num [ContraFan.two_h0], not_lt.mpr le_rfl⟩
      have hWfin : ({w, -w} : Set V3).Finite := Set.Finite.insert w (Set.finite_singleton (-w))
      have hWtofin : hWfin.toFinset = insert w ({-w} : Finset V3) := by
        ext x
        simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff]
      have hWscript : scriptL ({w, -w} : Set V3) = 2 := by
        rw [scriptL, dif_pos hWfin, hWtofin,
          Finset.sum_insert (fun hc => hwne (Finset.mem_singleton.mp hc)),
          Finset.sum_singleton, norm_neg]
        have h1 : lmfun 1 = 1 := by
          rw [lmfun, if_pos (show (1:ℝ) ≤ h0 by norm_num [h0])]
          exact div_self (show (h0:ℝ) - 1 ≠ 0 by norm_num [h0])
        rw [show ‖w‖ / 2 = (1:ℝ) from by rw [hwnorm]; norm_num, h1]
        norm_num
      have hV1 : ({v} : Set V3).Finite := Set.finite_singleton v
      have hVscript : scriptL ({v} : Set V3) = lmfun (‖v‖ / 2) := by
        rw [scriptL, dif_pos hV1]
        have hto : hV1.toFinset = {v} := by ext x; simp
        rw [hto, Finset.sum_singleton]
      have hVsc : scriptL V = lmfun (‖v‖ / 2) := by rw [hV0]; exact hVscript
      have hcon := hmax ({w, -w} : Set V3) hWpack hWsub
      rw [hWscript, hVsc] at hcon
      have hlt1 : lmfun (‖v‖ / 2) < 1 := by
        rw [lmfun, if_pos (by linarith : ‖v‖ / 2 ≤ h0),
          div_lt_one (show (0:ℝ) < h0 - 1 by norm_num [h0])]
        linarith
      linarith
    · -- 情形 B：V ≠ {v}，径向内移
      obtain ⟨u0, hu0V, hu0v⟩ : ∃ u : V3, u ∈ V ∧ u ≠ v := by
        by_contra hcon
        push_neg at hcon
        exact hV0 (Set.eq_singleton_iff_unique_mem.mpr ⟨hv, fun x hx => hcon x hx⟩)
      have hmin : ∀ y ∈ V, y ≠ v → dist y v - 2
          ∈ (hfin.toFinset.erase v).image (fun z : V3 => dist z v - 2) := by
        intro y hy hyv
        exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hyv, hfin.mem_toFinset.mpr hy⟩,
          rfl⟩
      have hEne : ((hfin.toFinset.erase v).image fun z : V3 => dist z v - 2).Nonempty :=
        ⟨dist u0 v - 2, hmin u0 hu0V hu0v⟩
      obtain ⟨m, hmpos, hminle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y ∈ V, y ≠ v → m ≤ dist y v - 2 := by
        obtain ⟨y1, hy1, hy1v⟩ :=
          Finset.mem_image.mp (((hfin.toFinset.erase v).image
            fun z : V3 => dist z v - 2).min'_mem hEne)
        obtain ⟨hy1v', hy1D⟩ := Finset.mem_erase.mp hy1
        have hy1V : y1 ∈ V := hfin.mem_toFinset.mp hy1D
        have hy1eq : ((hfin.toFinset.erase v).image
            fun z : V3 => dist z v - 2).min' hEne = dist y1 v - 2 := hy1v.symm
        refine ⟨((hfin.toFinset.erase v).image fun z : V3 => dist z v - 2).min' hEne, ?_, ?_⟩
        · rw [hy1eq]
          by_contra hcon
          push_neg at hcon
          have h2le : dist y1 v ≤ 2 := by linarith
          have h2ge : 2 ≤ dist y1 v := hpack.dist_ge_two hy1V hv hy1v'
          have hy1edge : y1 ∈ setOfEdge v V (ECTC V) := by
            refine ⟨?_, hy1V⟩
            exact ectrPairMem.mpr ⟨hv, hy1V, fun hh => hy1v' hh.symm,
              by rw [dist_comm]; linarith⟩
          rw [hedges] at hy1edge
          exact hy1edge
        · intro y hy hyv
          exact Finset.min'_le ((hfin.toFinset.erase v).image fun z : V3 => dist z v - 2)
            (dist y v - 2) (hmin y hy hyv)
      obtain ⟨e, he0, he1, hedvw⟩ :
          ∃ e : ℝ, 0 < e ∧ e < 1 ∧ dist v ((1 - e) • v) = min m (‖v‖ - 2) := by
        refine ⟨min m (‖v‖ - 2) / ‖v‖, ?_, ?_, ?_⟩
        · apply div_pos _ hnormpos
          exact lt_min hmpos (by linarith)
        · have h1 : min m (‖v‖ - 2) / ‖v‖ ≤ (‖v‖ - 2) / ‖v‖ :=
            (div_le_div_iff_of_pos_right hnormpos).mpr (min_le_right m (‖v‖ - 2))
          have h2 : (‖v‖ - 2) / ‖v‖ < 1 := by
            rw [div_lt_one hnormpos]
            linarith
          linarith
        · have hsub : v - (1 - min m (‖v‖ - 2) / ‖v‖) • v
              = (min m (‖v‖ - 2) / ‖v‖) • v := by
            have hexpand : (1 - min m (‖v‖ - 2) / ‖v‖) • v
                = v - (min m (‖v‖ - 2) / ‖v‖) • v := by rw [sub_smul, one_smul]
            rw [hexpand, sub_sub_cancel]
          rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
            abs_of_pos (div_pos (lt_min hmpos (by linarith)) hnormpos), mul_comm]
          exact mul_div_cancel₀ (min m (‖v‖ - 2)) (ne_of_gt hnormpos)
      obtain ⟨w, hwdef⟩ : ∃ w : V3, w = (1 - e) • v := ⟨_, rfl⟩
      have hdvw' : dist v w = min m (‖v‖ - 2) := by rw [hwdef]; exact hedvw
      have hdisteq : dist v w = e * ‖v‖ := by
        rw [hwdef, dist_eq_norm]
        have hsub : v - (1 - e) • v = e • v := by
          have hexpand : (1 - e) • v = v - e • v := by rw [sub_smul, one_smul]
          rw [hexpand, sub_sub_cancel]
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < e)]
      have hnormeq : ‖w‖ + dist v w = ‖v‖ := by
        have h1 : ‖w‖ = (1 - e) * ‖v‖ := by
          rw [hwdef, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (show (0:ℝ) ≤ 1 - e by linarith)]
        rw [h1, hdisteq]
        have h2 : (1 - e) * ‖v‖ + e * ‖v‖ = (1 - e + e) * ‖v‖ := by ring
        rw [h2]
        have h3 : (1 - e + e : ℝ) = 1 := by ring
        rw [h3, one_mul]
      have hwnormge : (2:ℝ) ≤ ‖w‖ := by
        have hle : min m (‖v‖ - 2) ≤ ‖v‖ - 2 := min_le_right m (‖v‖ - 2)
        linarith [hnormeq, hdvw', hle]
      have hwnormlt : ‖w‖ < ‖v‖ := by
        have hposd : 0 < dist v w := by
          rw [hdisteq]
          exact mul_pos he0 hnormpos
        linarith [hnormeq, hposd]
      have hwne : w ≠ v := fun hcon => lt_irrefl _ (hcon ▸ hwnormlt)
      have hwVd : w ∉ V \ {v} := by
        rintro ⟨hwV, hwv⟩
        have hminle' := hminle w hwV hwv
        have hle : min m (‖v‖ - 2) ≤ dist w v - 2 :=
          le_trans (min_le_left m (‖v‖ - 2)) hminle'
        rw [dist_comm, hdvw'] at hle
        linarith
      have hdgw : ∀ z : V3, z ∈ V → z ≠ v → 2 ≤ dist z w := by
        intro z hz hzv
        have hminle' := hminle z hz hzv
        have htri : dist z v ≤ dist z w + dist w v := dist_triangle z w v
        have hdwv : dist w v = dist v w := dist_comm w v
        rw [hdwv] at htri
        have hle : min m (‖v‖ - 2) ≤ m := min_le_left m (‖v‖ - 2)
        linarith [htri, hminle', hle, hdvw']
      have hWpack : Packing (insert w (V \ {v})) := by
        intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with ha0 | ha' <;>
          rcases Set.mem_insert_iff.mp hb with hb0 | hb'
        · rw [ha0, hb0]
        · have h2 : (2:ℝ) ≤ dist a b := by
            rw [ha0, dist_comm]
            exact hdgw b hb'.1 hb'.2
          exact absurd hab (not_lt.mpr h2)
        · have h2 : (2:ℝ) ≤ dist a b := by
            rw [hb0]
            exact hdgw a ha'.1 ha'.2
          exact absurd hab (not_lt.mpr h2)
        · exact hpack a ha'.1 b hb'.1 hab
      have hWsub : insert w (V \ {v}) ⊆ ballAnnulus := by
        intro x hx
        rcases Set.mem_insert_iff.mp hx with hx0 | hx'
        · rw [hx0, ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
            dist_zero_right]
          refine ⟨?_, ?_⟩
          · linarith [hwnormge, hwnormlt, hvh0]
          · exact not_lt.mpr hwnormge
        · exact hsub hx'.1
      have hcon := hmax (insert w (V \ {v})) hWpack hWsub
      have hVsum : scriptL V
          = lmfun (‖v‖ / 2) + ∑ x ∈ hfin.toFinset.erase v, lmfun (‖x‖ / 2) := by
        rw [scriptL, dif_pos hfin]
        have hsplit : insert v (hfin.toFinset.erase v) = hfin.toFinset :=
          Finset.insert_erase (hfin.mem_toFinset.mpr hv)
        nth_rewrite 1 [← hsplit]
        rw [Finset.sum_insert (fun hc => (Finset.mem_erase.mp hc).1 rfl)]
      have hWsum : scriptL (insert w (V \ {v}))
          = lmfun (‖w‖ / 2) + ∑ x ∈ hfin.toFinset.erase v, lmfun (‖x‖ / 2) := by
        have hWfin : (insert w (V \ {v})).Finite :=
          Set.Finite.insert w (hfin.subset Set.sdiff_subset)
        have htofin : hWfin.toFinset = insert w (hfin.toFinset.erase v) := by
          ext x
          simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Set.mem_insert_iff,
            Finset.mem_erase, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        rw [scriptL, dif_pos hWfin, htofin,
          Finset.sum_insert (fun hc => hwVd ⟨hfin.mem_toFinset.mp (Finset.mem_erase.mp hc).2,
            (Finset.mem_erase.mp hc).1⟩)]
      have hlmgood : lmfun (‖v‖ / 2) < lmfun (‖w‖ / 2) := by
        have hb1 : ‖v‖ / 2 ≤ h0 := by linarith
        have hb2 : ‖w‖ / 2 ≤ h0 := by linarith
        have e1 : lmfun (‖v‖ / 2) = (h0 - ‖v‖ / 2) / (h0 - 1) := by
          rw [lmfun, if_pos hb1]
        have e2 : lmfun (‖w‖ / 2) = (h0 - ‖w‖ / 2) / (h0 - 1) := by
          rw [lmfun, if_pos hb2]
        rw [e1, e2]
        have hd : (0:ℝ) < h0 - 1 := by norm_num [h0]
        have k1 : (0:ℝ) ≤ h0 - ‖w‖ / 2 := by linarith
        have k2 : h0 - ‖v‖ / 2 < h0 - ‖w‖ / 2 := by linarith
        exact (div_lt_div_iff_of_pos_right hd).mpr k2
      rw [hWsum, hVsum] at hcon
      linarith
  · -- ‖v‖ ≤ 2：与 annulus 下界 2 ≤ ‖v‖ 夹出等式
    linarith

/-! ## 中档③：not_surrounded_node_norm_ECTC（FNJLBXS-compiled.hl:1727）

中档①给出保范双射迁移（f v 孤立），中档②给孤立点落球面；
bijScriptL 把最大性转移到 W 上，范数回传即得。 -/

private theorem notSurroundedNodeNormECTC {V : Set V3} (hpack : Packing V)
    (hsub : V ⊆ ballAnnulus)
    (hmax : ∀ W : Set V3, Packing W → W ⊆ ballAnnulus → scriptL W ≤ scriptL V)
    {v : V3} (hv : v ∈ V) (hns : ¬ surroundedNode V (ECTC V) v) : ‖v‖ = 2 := by
  classical
  have hfin : V.Finite := packingFiniteOfBallAnnulus hpack hsub
  obtain ⟨W, f, hbij, hWp, hWs, hnorm, hiso⟩ := notSurroundedECTC hpack hsub hv hns
  have hmaxW : ∀ U : Set V3, Packing U → U ⊆ ballAnnulus → scriptL U ≤ scriptL W := by
    intro U hUp hUs
    have h1 := hmax U hUp hUs
    rw [bijScriptL hfin f hbij hnorm] at h1
    exact h1
  have hfvW : f v ∈ W := hbij.1 hv
  have hfvnorm := isolatedNodeNormECTC hWp hWs hmaxW hfvW hiso
  rw [hnorm v hv]
  exact hfvnorm
/-! ## 柱②：FNJLBXS 归一化本体（FNJLBXS-compiled.hl:1324-1537，2026-10-14 A6 柱② lane 落地）

配置空间 = `(Fin k → V3)` 的 annulus-坐标 + 两两 dist ≥ 2 + 范数剖面匹配（经
`packingConfigEnumerate` 枚举 V）；`fnxOrdStat`（第 j 小值 = 各 j+1 元子集最大值的
最小值）给 min-距离向量的字典序极小化机器（Master-iff：第 j 小值 ≤ t ⟺ 至少 j+1 项
≤ t），`fnxChain` 紧集链逐级取 argmax；末步对「既不孤立又不 surrounded」的配置点经
`notSurroundedImpOnOneSideOfPlane` + `perturbationLemma` 扰动一点 r，与字典序极小矛盾。
五个前置桩全部消费树内真证（`packingConfigCompact`/`packingFiniteOfBallAnnulus`/
`perturbationLemma`/`notSurroundedImpOnOneSideOfPlane`/`packingConfigEnumerate`）。 -/

/-! ### 基建：阶次统计量与最近邻距离 -/

section
variable {k : ℕ}

/-- inf' 的求取归属（经 image + min'）。 -/
private theorem fnxInfAttained {ι : Type*} {P : Finset ι} {h : P.Nonempty} {g : ι → ℝ} :
    ∃ x, x ∈ P ∧ g x = P.inf' h g := by
  have himg : (P.image g).Nonempty := h.image g
  have hmem : (P.image g).min' himg ∈ P.image g := Finset.min'_mem _ himg
  obtain ⟨x, hx, hxg⟩ := Finset.mem_image.mp hmem
  refine ⟨x, hx, ?_⟩
  have hEq : P.inf' h g = (P.image g).min' himg := by
    rw [Finset.min'_eq_inf', Finset.inf'_image]
    rfl
  rw [hEq, hxg]

private theorem fnxLtInf' {ι : Type*} {P : Finset ι} {h : P.Nonempty} {g : ι → ℝ} {t : ℝ}
    (hlt : ∀ i ∈ P, t < g i) : t < P.inf' h g := by
  obtain ⟨x, hx, hxg⟩ := fnxInfAttained
  exact (hlt x hx).trans_le (le_of_eq hxg)

/-- 有限集上的最大值（带 junk 0 分支）。 -/
private noncomputable def fnxFinSup (s : Finset (Fin k)) (d : Fin k → ℝ) : ℝ :=
  if hs : s.Nonempty then s.sup' hs (fun i => d i) else 0

private theorem fnxFinSupLe {s : Finset (Fin k)} (hs : s.Nonempty) {d : Fin k → ℝ} {t : ℝ}
    (h : ∀ i ∈ s, d i ≤ t) : fnxFinSup s d ≤ t := by
  unfold fnxFinSup
  rw [dif_pos hs]
  exact Finset.sup'_le hs (fun i => d i) h

private theorem fnxFinSupGe {s : Finset (Fin k)} (hs : s.Nonempty) {d : Fin k → ℝ} {t : ℝ}
    (h : ∃ i ∈ s, t ≤ d i) : t ≤ fnxFinSup s d := by
  unfold fnxFinSup
  rw [dif_pos hs]
  obtain ⟨i, hi, hle⟩ := h
  exact hle.trans (Finset.le_sup' (f := fun i => d i) (b := i) hi)

private theorem fnxContSup' {ι : Type*} {X : Type*} [TopologicalSpace X] (P : Finset ι) :
    ∀ (h : P.Nonempty) (g : ι → X → ℝ), (∀ i, Continuous (g i)) →
      Continuous (fun x => P.sup' h (fun i => g i x)) := by
  classical
  intro h
  induction P using Finset.cons_induction_on with
  | empty => exact absurd h (by simp)
  | @cons a P hpa ih =>
      intro g hg
      rcases Finset.eq_empty_or_nonempty P with hP0 | hPne
      · subst hP0
        have hset : (Finset.cons a ∅ hpa : Finset ι) = {a} := by
          ext x
          simp
        simp only [hset] at h ⊢
        have hE : ∀ x, ({a} : Finset ι).sup' h (fun i => g i x) = g a x := fun x =>
          Finset.sup'_singleton (b := a) (f := fun i => g i x)
        exact Continuous.congr (hg a) (fun x => (hE x).symm)
      · have hE : ∀ x, (Finset.cons a P hpa).sup' h (fun i => g i x)
            = g a x ⊔ P.sup' hPne (fun i => g i x) := fun x =>
          Finset.sup'_cons hPne (fun i => g i x)
        exact Continuous.congr (Continuous.max (hg a) (ih hPne g hg))
          (fun x => (hE x).symm)

private theorem fnxContInf' {ι : Type*} {X : Type*} [TopologicalSpace X] (P : Finset ι) :
    ∀ (h : P.Nonempty) (g : ι → X → ℝ), (∀ i, Continuous (g i)) →
      Continuous (fun x => P.inf' h (fun i => g i x)) := by
  classical
  intro h
  induction P using Finset.cons_induction_on with
  | empty => exact absurd h (by simp)
  | @cons a P hpa ih =>
      intro g hg
      rcases Finset.eq_empty_or_nonempty P with hP0 | hPne
      · subst hP0
        have hset : (Finset.cons a ∅ hpa : Finset ι) = {a} := by
          ext x
          simp
        simp only [hset] at h ⊢
        have hE : ∀ x, ({a} : Finset ι).inf' h (fun i => g i x) = g a x := fun x =>
          Finset.inf'_singleton (b := a) (f := fun i => g i x)
        exact Continuous.congr (hg a) (fun x => (hE x).symm)
      · have hE : ∀ x, (Finset.cons a P hpa).inf' h (fun i => g i x)
            = g a x ⊓ P.inf' hPne (fun i => g i x) := fun x =>
          Finset.inf'_cons hPne (fun i => g i x)
        exact Continuous.congr (Continuous.min (hg a) (ih hPne g hg))
          (fun x => (hE x).symm)

private theorem fnxFinSupCont (s : Finset (Fin k)) :
    Continuous (fun d : Fin k → ℝ => fnxFinSup s d) := by
  unfold fnxFinSup
  split_ifs with hs
  · exact fnxContSup' s hs (fun (i : Fin k) (d : Fin k → ℝ) => d i)
      (fun i => continuous_apply i)
  · exact continuous_const

/-- 阶次统计量：`d` 的第 `j` 小值 = 各 `j+1` 元子集最大值的最小值。 -/
private noncomputable def fnxOrdStat (j : ℕ) (d : Fin k → ℝ) : ℝ :=
  if h : ((Finset.univ : Finset (Fin k)).powersetCard (j + 1)).Nonempty then
    (Finset.univ.powersetCard (j + 1)).inf' h (fun s => fnxFinSup s d)
  else 0

private theorem fnxOrdStatNonempty {j : ℕ} (hj : j < k) :
    ((Finset.univ : Finset (Fin k)).powersetCard (j + 1)).Nonempty := by
  have hcard : (Finset.univ : Finset (Fin k)).card = k :=
    Finset.card_univ.trans (Fintype.card_fin k)
  refine Finset.powersetCard_nonempty.mpr ?_
  rw [hcard]
  exact hj

private theorem fnxOrdStatCont (j : ℕ) :
    Continuous (fun d : Fin k → ℝ => fnxOrdStat j d) := by
  unfold fnxOrdStat
  split_ifs with h
  · exact fnxContInf' _ h (fun s d => fnxFinSup s d) (fun s => fnxFinSupCont s)
  · exact continuous_const

/-- Master 刻画：第 `j` 小值 ≤ t ⟺ 至少 `j+1` 项 ≤ t。 -/
private theorem fnxOrdStatLeIff {j : ℕ} (hj : j < k) (d : Fin k → ℝ) (t : ℝ) :
    fnxOrdStat j d ≤ t ↔ j + 1 ≤ (Finset.univ.filter (fun i => d i ≤ t)).card := by
  constructor
  · -- ordStat ≤ t → 计数 ≥ j+1
    intro h
    by_contra hcon
    push_neg at hcon
    have hall : ∀ S ∈ Finset.univ.powersetCard (j + 1), t < fnxFinSup S d := by
      intro S hS
      obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
      have hex : ∃ i ∈ S, t < d i := by
        by_contra hcon2
        push_neg at hcon2
        have hSsub2 : S ⊆ Finset.univ.filter (fun i => d i ≤ t) :=
          fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon2 i hi⟩
        have hcard := Finset.card_le_card hSsub2
        rw [hScard] at hcard
        exact absurd hcard (not_le.mpr hcon)
      obtain ⟨i, hi, hlt⟩ := hex
      exact lt_of_lt_of_le hlt
        (fnxFinSupGe (hs := ⟨i, hi⟩) (h := Exists.intro i (And.intro hi (le_refl _))))
    have hgt : t < fnxOrdStat j d := by
      unfold fnxOrdStat
      rw [dif_pos (fnxOrdStatNonempty hj)]
      exact fnxLtInf' hall
    exact absurd hgt (not_lt.mpr h)
  · -- 计数 ≥ j+1 → ordStat ≤ t
    intro h
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq h
    have hSne : S.Nonempty := by
      refine Finset.nonempty_iff_ne_empty.mpr (fun he => ?_)
      rw [he, Finset.card_empty] at hScard
      omega
    refine le_trans ?_ (fnxFinSupLe hSne (fun i hi => (Finset.mem_filter.mp (hSsub hi)).2))
    unfold fnxOrdStat
    rw [dif_pos (fnxOrdStatNonempty hj)]
    exact Finset.inf'_le (fun s => fnxFinSup s d)
      (Finset.mem_powersetCard.mpr ⟨hSsub.trans (Finset.subset_univ _), hScard⟩)

private theorem fnxOrdStatEqOfCount {j : ℕ} (hj : j < k) {d₁ d₂ : Fin k → ℝ}
    (h : ∀ t, (j + 1 ≤ (Finset.univ.filter (fun i => d₁ i ≤ t)).card ↔
      j + 1 ≤ (Finset.univ.filter (fun i => d₂ i ≤ t)).card)) :
    fnxOrdStat j d₁ = fnxOrdStat j d₂ := by
  refine le_antisymm ?_ ?_
  · exact (fnxOrdStatLeIff hj d₁ (fnxOrdStat j d₂)).2
      ((h (fnxOrdStat j d₂)).2 ((fnxOrdStatLeIff hj d₂ _).1 le_rfl))
  · exact (fnxOrdStatLeIff hj d₂ (fnxOrdStat j d₁)).2
      ((h (fnxOrdStat j d₁)).1 ((fnxOrdStatLeIff hj d₁ _).1 le_rfl))

/-- 最近邻距离。 -/
private noncomputable def fnxNnDist {k : ℕ} (f : Fin k → V3) (i : Fin k) : ℝ :=
  if h : (Finset.univ.erase i).Nonempty then
    (Finset.univ.erase i).inf' h (fun j => dist (f i) (f j))
  else 0

private theorem fnxNnDistLe {k : ℕ} {f : Fin k → V3} {i : Fin k} {t : ℝ}
    (h : ∃ j₀, j₀ ≠ i ∧ dist (f i) (f j₀) ≤ t) : fnxNnDist f i ≤ t := by
  obtain ⟨j₀, hj₀, hle⟩ := h
  unfold fnxNnDist
  rw [dif_pos (by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro he
    rw [Finset.eq_empty_iff_forall_notMem] at he
    exact he j₀ (Finset.mem_erase.mpr ⟨hj₀, Finset.mem_univ j₀⟩))]
  exact le_trans (Finset.inf'_le (fun j => dist (f i) (f j))
    (Finset.mem_erase.mpr ⟨hj₀, Finset.mem_univ j₀⟩)) hle

private theorem fnxNnDistGe {k : ℕ} {f : Fin k → V3} {i : Fin k} {t : ℝ}
    (hne : (Finset.univ.erase i).Nonempty) (h : ∀ j, j ≠ i → t ≤ dist (f i) (f j)) :
    t ≤ fnxNnDist f i := by
  unfold fnxNnDist
  rw [dif_pos hne]
  exact Finset.le_inf' hne (fun j => dist (f i) (f j))
    (fun j hj => h j (Finset.ne_of_mem_erase hj))

private theorem fnxNnDistAttained {k : ℕ} {f : Fin k → V3} {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) :
    ∃ j₀, j₀ ≠ i ∧ dist (f i) (f j₀) = fnxNnDist f i := by
  unfold fnxNnDist
  rw [dif_pos hne]
  obtain ⟨x, hx, hxg⟩ := fnxInfAttained (P := Finset.univ.erase i) (h := hne)
    (g := fun j => dist (f i) (f j))
  exact ⟨x, Finset.ne_of_mem_erase hx, hxg⟩

private theorem fnxUpdNnDistLe {k : ℕ} {f : Fin k → V3} {r : Fin k} {u : V3} {i : Fin k}
    {t : ℝ} (hir : i ≠ r) (h : ∃ j₀, j₀ ≠ i ∧ j₀ ≠ r ∧ dist (f i) (f j₀) ≤ t) :
    fnxNnDist (Function.update f r u) i ≤ t := by
  obtain ⟨j₀, hji, hjr, hle⟩ := h
  refine fnxNnDistLe ⟨j₀, hji, ?_⟩
  rw [Function.update_of_ne hir, Function.update_of_ne hjr]
  exact hle

private theorem fnxUpdNnDistGe {k : ℕ} {f : Fin k → V3} {r : Fin k} {u : V3} {i : Fin k}
    {t : ℝ} (hir : i ≠ r) (hne : (Finset.univ.erase i).Nonempty)
    (h1 : ∀ j, j ≠ i → j ≠ r → t ≤ dist (f i) (f j))
    (h2 : t ≤ dist (f i) u) :
    t ≤ fnxNnDist (Function.update f r u) i := by
  refine fnxNnDistGe hne (fun j hj => ?_)
  rcases eq_or_ne j r with rfl | hjr
  · rw [Function.update_self, Function.update_of_ne hir]
    exact h2
  · rw [Function.update_of_ne hir, Function.update_of_ne hjr]
    exact h1 j hj hjr

private theorem fnxNnDistCont {k : ℕ} (i : Fin k) :
    Continuous (fun f : Fin k → V3 => fnxNnDist f i) := by
  unfold fnxNnDist
  split_ifs with h
  · exact fnxContInf' _ h (fun (j : Fin k) (f : Fin k → V3) => dist (f i) (f j))
      (fun j => (continuous_apply i).dist (continuous_apply j))
  · exact continuous_const

/-- 链集：`C 0 = R`，`C (j+1) = C j ∩ argmax (c j) (C j)`。 -/
private noncomputable def fnxChain {k : ℕ} (R : Set (Fin k → V3))
    (c : ℕ → (Fin k → V3) → ℝ) : ℕ → Set (Fin k → V3)
  | 0 => R
  | j + 1 => {x | x ∈ fnxChain R c j ∧ ∀ y ∈ fnxChain R c j, c j y ≤ c j x}

private theorem fnxChainSuccSub {k : ℕ} {R : Set (Fin k → V3)} {c : ℕ → (Fin k → V3) → ℝ}
    (j : ℕ) : fnxChain R c (j + 1) ⊆ fnxChain R c j := fun _ hx => hx.1

private theorem fnxChainMemZero {k : ℕ} {R : Set (Fin k → V3)} {c : ℕ → (Fin k → V3) → ℝ}
    {x : Fin k → V3} (hx : x ∈ R) : x ∈ fnxChain R c 0 := hx

private theorem fnxChainSuccMem {k : ℕ} {R : Set (Fin k → V3)} {c : ℕ → (Fin k → V3) → ℝ}
    {x : Fin k → V3} {j : ℕ} (hx : x ∈ fnxChain R c j)
    (hmax : ∀ y ∈ fnxChain R c j, c j y ≤ c j x) :
    x ∈ fnxChain R c (j + 1) := ⟨hx, hmax⟩

private theorem fnxChainSuccMemImp {k : ℕ} {R : Set (Fin k → V3)} {c : ℕ → (Fin k → V3) → ℝ}
    {x : Fin k → V3} {j : ℕ} (hx : x ∈ fnxChain R c (j + 1)) :
    x ∈ fnxChain R c j ∧ ∀ y ∈ fnxChain R c j, c j y ≤ c j x := hx

private theorem fnxChainSubOfLe {k : ℕ} {R : Set (Fin k → V3)} {c : ℕ → (Fin k → V3) → ℝ} :
    ∀ j m, m ≤ j → fnxChain R c j ⊆ fnxChain R c m := by
  intro j
  induction j with
  | zero =>
      intro m hm x hx
      have h0 : m = 0 := Nat.le_zero.mp hm
      subst h0
      exact hx
  | succ j ih =>
      intro m hm x hx
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact hx
      · exact ih m (Nat.le_of_lt_succ hlt) (fnxChainSuccSub j hx)

private theorem fnxChainProps {k : ℕ} {R : Set (Fin k → V3)} {c : ℕ → (Fin k → V3) → ℝ}
    (hR : IsCompact R) (hRne : R.Nonempty) (hc : ∀ j, Continuous (c j)) (j : ℕ) :
    (fnxChain R c j).Nonempty ∧ IsCompact (fnxChain R c j) := by
  induction j with
  | zero => exact ⟨hRne, hR⟩
  | succ j ih =>
      obtain ⟨hne, hcpt⟩ := ih
      obtain ⟨x, hx, hxmax⟩ := hcpt.exists_isMaxOn hne (hc j).continuousOn
      refine ⟨⟨x, hx, hxmax⟩, ?_⟩
      have hclosed : IsClosed (fnxChain R c (j + 1)) := by
        have heq : fnxChain R c (j + 1)
            = fnxChain R c j ∩ ⋂ y ∈ fnxChain R c j, (c j) ⁻¹' Set.Ici (c j y) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
            Set.mem_Ici]
          exact ⟨fun hx => ⟨hx.1, fun y hy => hx.2 y hy⟩,
            fun hx => ⟨hx.1, fun y hy => hx.2 y hy⟩⟩
        rw [heq]
        exact IsClosed.inter hcpt.isClosed
          (isClosed_iInter fun y => isClosed_iInter fun _ =>
            (isClosed_Ici (a := c j y)).preimage (hc j))
      exact hcpt.of_isClosed_subset hclosed Set.inter_subset_left

/-- 双点集等式的端点互换（四情形统一引理）。 -/
private theorem fnxPairEnds {a b x y : V3} (hab : ({a, b} : Set V3) = ({x, y} : Set V3))
    (hne : a ≠ b) : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hx : x = a ∨ x = b := by
    have h1 : x ∈ ({x, y} : Set V3) := by simp
    have h2 : x ∈ ({a, b} : Set V3) := hab ▸ h1
    simpa using h2
  have hy : y = a ∨ y = b := by
    have h1 : y ∈ ({x, y} : Set V3) := by simp
    have h2 : y ∈ ({a, b} : Set V3) := hab ▸ h1
    simpa using h2
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · -- x = a, y = a
    exfalso
    have h0 : b ∈ ({a, b} : Set V3) := by simp
    have hmem : b ∈ ({x, y} : Set V3) := hab ▸ h0
    rw [hx, hy] at hmem
    simp at hmem
    exact hne hmem.symm
  · -- x = a, y = b
    exact Or.inl ⟨hx, hy⟩
  · -- x = b, y = a
    exact Or.inr ⟨hx, hy⟩
  · -- x = b, y = b
    exfalso
    have h0 : a ∈ ({a, b} : Set V3) := by simp
    have hmem : a ∈ ({x, y} : Set V3) := hab ▸ h0
    rw [hx, hy] at hmem
    simp at hmem
    exact hne hmem

end
/-- 余量存在（HOL FNJLBXS:1411 `e_cond` 的指标形式）：`dy` 为第 `r` 行最近邻距离，
`j ≠ r` 的距离要么恰为 `dy`，要么以 `dy + e` 为下界（`e` 取有限正差集的最小元，
空集时取 1）。 -/
private theorem fnxMarginExists {k : ℕ} (xst : Fin k → V3) (r : Fin k) (dy : ℝ)
    (hdy : ∀ j : Fin k, j ≠ r → dy ≤ dist (xst j) (xst r)) :
    ∃ e : ℝ, 0 < e ∧ ∀ i : Fin k, i ≠ r → dist (xst i) (xst r) ≠ dy →
      dy + e ≤ dist (xst i) (xst r) := by
  by_cases hE : (Finset.univ.filter
      (fun j : Fin k => j ≠ r ∧ dist (xst j) (xst r) ≠ dy)).Nonempty
  · obtain ⟨j₀, hj₀⟩ := hE
    obtain ⟨-, hjr₀, hne₀⟩ := Finset.mem_filter.mp hj₀
    have hge : dy ≤ dist (xst j₀) (xst r) := hdy j₀ hjr₀
    have hlt : dy < dist (xst j₀) (xst r) := lt_of_le_of_ne hge hne₀.symm
    have hmem : dist (xst j₀) (xst r) - dy ∈ (Finset.univ.filter
        (fun j : Fin k => j ≠ r ∧ dist (xst j) (xst r) ≠ dy)).image
        (fun j => dist (xst j) (xst r) - dy) :=
      Finset.mem_image.mpr ⟨j₀, hj₀, rfl⟩
    refine ⟨((Finset.univ.filter
        (fun j : Fin k => j ≠ r ∧ dist (xst j) (xst r) ≠ dy)).image
        (fun j => dist (xst j) (xst r) - dy)).min'
        ⟨dist (xst j₀) (xst r) - dy, hmem⟩, ?_, ?_⟩
    · obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp (Finset.min'_mem _ ⟨dist (xst j₀) (xst r) - dy, hmem⟩)
      obtain ⟨-, hjr, hne⟩ := Finset.mem_filter.mp hj
      have hlt2 : dy < dist (xst j) (xst r) :=
        lt_of_le_of_ne (hdy j hjr) hne.symm
      rw [← hEq]
      linarith
    · intro i hir hdne
      have hmem2 : dist (xst i) (xst r) - dy ∈ (Finset.univ.filter
          (fun j : Fin k => j ≠ r ∧ dist (xst j) (xst r) ≠ dy)).image
          (fun j => dist (xst j) (xst r) - dy) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hir, hdne⟩, rfl⟩
      have hle := Finset.min'_le ((Finset.univ.filter
          (fun j : Fin k => j ≠ r ∧ dist (xst j) (xst r) ≠ dy)).image
          (fun j => dist (xst j) (xst r) - dy)) (dist (xst i) (xst r) - dy) hmem2
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro i hir hdne
    exact (hE ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hir, hdne⟩⟩).elim



/-! ### 本体：FNJLBXS（FNJLBXS-compiled.hl:1324-1537） -/

set_option maxHeartbeats 1000000 in
private theorem fnjlbxsCore {V : Set V3} (hpack : Packing V) (hsub : V ⊆ ballAnnulus) :
    ∃ W : Set V3, ∃ φ : V3 → V3, Set.BijOn φ V W ∧ Packing W ∧ W ⊆ ballAnnulus ∧
      (∀ v ∈ V, ‖v‖ = ‖φ v‖) ∧
      ∀ w ∈ W, setOfEdge w W (ESTD W) = ∅ ∨ surroundedNode W (ESTD W) w := by
  classical
  have hfin : V.Finite := packingFiniteOfBallAnnulus hpack hsub
  by_cases hk0 : V.ncard = 0
  · have hV : V = ∅ := (Set.ncard_eq_zero (s := V) (hs := hfin)).mp hk0
    subst hV
    exact ⟨∅, id, ⟨fun x hx => hx.elim, fun x _ y _ hxy => hxy, fun x hx => hx.elim⟩,
      fun a ha _ _ _ => ha.elim, fun x hx => hx.elim, fun v hv => hv.elim, fun w hw => hw.elim⟩
  by_cases hk1 : V.ncard = 1
  · obtain ⟨v, hV⟩ := (Set.ncard_eq_one (s := V)).mp hk1
    refine ⟨V, id, ⟨fun z hz => hz, fun z _ y _ hxy => hxy, fun z hz => ⟨z, hz, rfl⟩⟩,
      hpack, hsub, fun z _ => rfl, ?_⟩
    intro w hw
    refine Or.inl (Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_)
    obtain ⟨hedge, -⟩ := hz
    obtain ⟨a, b, hab, haV, hbV, hne, -⟩ := hedge
    rw [hV] at haV hbV
    rw [Set.mem_singleton_iff.mp haV, Set.mem_singleton_iff.mp hbV] at hne
    exact hne rfl
  -- 主情形：2 ≤ k
  have hk2 : (2:ℕ) ≤ V.ncard := by omega
  set k := V.ncard with hkdef
  have hk2' : (2:ℕ) ≤ k := hk2
  haveI hkne : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨enum, henumrange, henuminj, -⟩ := packingConfigEnumerate hpack hsub rfl
  set R : Set (Fin k → V3) :=
    {f | (∀ i, f i ∈ ballAnnulus) ∧ (∀ i j, i ≠ j → 2 ≤ dist (f i) (f j)) ∧
      ∃ σ : Equiv.Perm (Fin k), ∀ i, ‖f (σ i)‖ = ‖enum i‖} with hRdef
  have hRsub : R ⊆ {f : Fin k → V3 | (∀ i, f i ∈ ballAnnulus) ∧
      ∀ i j, i ≠ j → 2 ≤ dist (f i) (f j)} := fun f hf => ⟨hf.1, hf.2.1⟩
  have hRclosed : IsClosed R := by
    have heq : R = {f : Fin k → V3 | (∀ i, f i ∈ ballAnnulus) ∧
        ∀ i j, i ≠ j → 2 ≤ dist (f i) (f j)} ∩
        {f : Fin k → V3 | ∃ σ : Equiv.Perm (Fin k), ∀ i, ‖f (σ i)‖ = ‖enum i‖} := by
      ext f
      simp only [hRdef, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    have hbij : ∀ σ : Equiv.Perm (Fin k),
        IsClosed {f : Fin k → V3 | ∀ i, ‖f (σ i)‖ = ‖enum i‖} := by
      intro σ
      have heq2 : {f : Fin k → V3 | ∀ i, ‖f (σ i)‖ = ‖enum i‖}
          = ⋂ i : Fin k, (fun f : Fin k → V3 => ‖f (σ i)‖) ⁻¹' {‖enum i‖} := by
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      rw [heq2]
      exact isClosed_iInter fun i =>
        isClosed_singleton.preimage ((continuous_norm.comp (continuous_apply (σ i))))
    rw [heq]
    refine IsClosed.inter (packingConfigCompact k).isClosed ?_
    have heq0 : {f : Fin k → V3 | ∃ σ : Equiv.Perm (Fin k), ∀ i, ‖f (σ i)‖ = ‖enum i‖}
        = ⋃ σ ∈ (Set.univ : Set (Equiv.Perm (Fin k))),
          {f : Fin k → V3 | ∀ i, ‖f (σ i)‖ = ‖enum i‖} := by
      ext f
      rw [Set.mem_iUnion₂]
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨σ, hf⟩; exact ⟨σ, trivial, hf⟩
      · rintro ⟨σ, -, hf⟩; exact ⟨σ, hf⟩
    rw [heq0]
    exact Set.Finite.isClosed_biUnion (Set.finite_univ (α := Equiv.Perm (Fin k)))
      (fun σ (_ : σ ∈ Set.univ) => hbij σ)
  have hRcpt : IsCompact R :=
    (packingConfigCompact k).of_isClosed_subset hRclosed hRsub
  have hRne : R.Nonempty := by
    have hmem : ∀ i, enum i ∈ V := by
      intro i
      rw [← henumrange]
      exact Set.mem_range_self i
    have hm1 : ∀ i, enum i ∈ ballAnnulus := fun i => hsub (hmem i)
    have hm2 : ∀ i j, i ≠ j → 2 ≤ dist (enum i) (enum j) := fun i j hij =>
      hpack.dist_ge_two (hmem i) (hmem j) (fun hcon => hij (henuminj hcon))
    exact ⟨enum, hm1, hm2, ⟨_root_.Equiv.refl (α := Fin k), fun i => rfl⟩⟩
  set d : (Fin k → V3) → Fin k → ℝ := fun f i => fnxNnDist f i with hdd
  set c : ℕ → (Fin k → V3) → ℝ := fun j f => fnxOrdStat j (d f) with hcc
  have hcd : ∀ j, Continuous (c j) := fun j =>
    (fnxOrdStatCont j).comp (continuous_pi fun i => fnxNnDistCont i)
  obtain ⟨hneC, hcptC⟩ := fnxChainProps hRcpt hRne hcd k
  obtain ⟨xst, hxst⟩ := hneC
  have hxstR : xst ∈ R := fnxChainSubOfLe k 0 (Nat.zero_le _) hxst
  obtain ⟨hann, hpair, σ, hnorm⟩ := hxstR
  have hxinj : Function.Injective xst := by
    intro i j hij
    by_contra hne
    have h2 := hpair i j hne
    rw [hij] at h2
    norm_num at h2
  have hWpack : Packing (Set.range xst) := by
    intro u hu v hv hd
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hv
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exact absurd hd (not_lt.2 (hpair i j hij))
  have hWsub : Set.range xst ⊆ ballAnnulus := fun z hz => by
    obtain ⟨i, rfl⟩ := hz
    exact hann i
  have hWne : Set.range xst ≠ ∅ := by
    intro hcon
    have hw : xst ⟨0, by omega⟩ ∈ Set.range xst := Set.mem_range_self (⟨0, by omega⟩ : Fin k)
    rw [hcon] at hw
    exact absurd hw (by simp)
  refine ⟨Set.range xst, fun v => xst (σ (Function.invFun enum v)), ?_, hWpack, hWsub, ?_, ?_⟩
  · refine ⟨fun z hz => Set.mem_range_self _, ?_, ?_⟩
    · intro u hu v hv huv
      have h1 : σ (Function.invFun enum u) = σ (Function.invFun enum v) := hxinj huv
      have h2 : Function.invFun enum u = Function.invFun enum v := by
        have h3 := congrArg (fun x : Fin k => σ.symm x) h1
        simpa using h3
      rw [← henumrange] at hu hv
      calc u = enum (Function.invFun enum u) :=
            (Function.invFun_eq (Set.mem_range.mp hu)).symm
        _ = enum (Function.invFun enum v) := by rw [h2]
        _ = v := Function.invFun_eq (Set.mem_range.mp hv)
    · intro z hz
      obtain ⟨i, rfl⟩ := hz
      have hmem : enum (σ.symm i) ∈ V := by
        rw [← henumrange]
        exact Set.mem_range_self _
      refine ⟨enum (σ.symm i), hmem, ?_⟩
      have hinv : ∀ j : Fin k, Function.invFun enum (enum j) = j := fun j =>
        henuminj (Function.invFun_eq ⟨j, rfl⟩)
      show xst (σ (Function.invFun enum (enum (σ.symm i)))) = xst i
      rw [hinv, Equiv.apply_symm_apply]
  · intro v hv
    rw [← henumrange] at hv
    have hv' : enum (Function.invFun enum v) = v := Function.invFun_eq (Set.mem_range.mp hv)
    have h1 : ‖v‖ = ‖enum (Function.invFun enum v)‖ := by rw [hv']
    calc ‖v‖ = ‖enum (Function.invFun enum v)‖ := h1
      _ = ‖xst (σ (Function.invFun enum v))‖ := (hnorm (Function.invFun enum v)).symm
      _ = ‖(fun w => xst (σ (Function.invFun enum w))) v‖ := rfl
  · -- 逐点二分
    intro w hw
    obtain ⟨r, rfl⟩ := hw
    by_cases hiso : setOfEdge (xst r) (Set.range xst) (ESTD (Set.range xst)) = ∅
    · exact Or.inl hiso
    by_cases hsurr : surroundedNode (Set.range xst) (ESTD (Set.range xst)) (xst r)
    · exact Or.inr hsurr
    exfalso
    set W : Set V3 := Set.range xst with hWdef
    -- 分离法向量（contraveningFanTl 的 ESTD 折算到 Assembly.ESTD）
    have hfanW' : FAN 0 W (ESTD W) := ContraFan.contraveningFanTl W hWpack hWsub hWne
    obtain ⟨nrm, hn0, hydot, hwnle⟩ :=
      notSurroundedImpOnOneSideOfPlane hfanW' (Set.mem_range_self r) hiso hsurr
    have hWrAnn : xst r ∈ ballAnnulus := hann r
    set S : Set V3 := setOfEdge (xst r) W (ESTD W) with hSdef
    have hEstDMem : ∀ z : V3, z ∈ W → xst r ≠ z → dist z (xst r) ≤ 2 * h0 →
        z ∈ S := by
      intro z hzW hzne hdle
      have hdle' : dist (xst r) z ≤ 2 * h0 := by
        rw [dist_comm]
        exact hdle
      exact ⟨⟨xst r, z, rfl, Set.mem_range_self r, hzW, hzne, hdle'⟩, hzW⟩
    have hSsub : ∀ z : V3, z ∈ S → z ∈ W ∧ z ≠ xst r ∧ dist z (xst r) ≤ 2 * h0 := by
      intro z hz
      obtain ⟨hedge, hzW⟩ := hz
      obtain ⟨a, b, hab, haW, hbW, hne, hd⟩ := hedge
      refine ⟨hzW, ?_, ?_⟩
      · rcases fnxPairEnds (x := xst r) (y := z) hab.symm hne with ⟨hzc, hvc⟩ | ⟨hzc, hvc⟩
        · intro hcon
          exact hne ((hzc.symm.trans hcon.symm).trans hvc)
        · intro hcon
          exact hne.symm ((hzc.symm.trans hcon.symm).trans hvc)
      · rcases fnxPairEnds (x := xst r) (y := z) hab.symm hne with ⟨hzc, hvc⟩ | ⟨hzc, hvc⟩
        · rw [hvc, hzc, dist_comm b a]; exact hd
        · rw [hvc, hzc]; exact hd
    have hSip : ∀ z : V3, z ∈ S → inner ℝ z nrm ≤ 0 ∧ (0:ℝ) < inner ℝ z (xst r) := by
      intro z hz
      obtain ⟨hzW, hzWne, hdle⟩ := hSsub z hz
      exact ⟨hwnle z hz, ContraFan.dot_pos_lemma (hWsub hzW) hWrAnn hdle⟩
    -- 最近邻行索引的擦除集恒非空（k ≥ 2）
    have hneEr : ∀ i : Fin k, (Finset.univ.erase i).Nonempty := by
      intro i
      by_cases hi0 : i.val = 0
      · refine ⟨⟨1, by omega⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
        intro hc
        have hv : (1:ℕ) = Fin.val i := congrArg Fin.val hc
        omega
      · refine ⟨⟨0, by omega⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
        intro hc
        have hv : (0:ℕ) = Fin.val i := congrArg Fin.val hc
        omega
    -- dy := 第 r 行最近邻距离，及其上界 hdyh0（S 非空给出一条 ≤ 2·h0 的边）
    set dy : ℝ := fnxNnDist xst r with hdydef
    have hdyEq : fnxNnDist xst r = dy := hdydef.symm
    have hdyh0 : dy ≤ 2 * h0 := by
      obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hiso
      obtain ⟨hedge, hzW⟩ := hz
      obtain ⟨a, b, hab, haW, hbW, hne, hd⟩ := hedge
      have hzne : z ≠ xst r := by
        rcases fnxPairEnds (x := xst r) (y := z) hab.symm hne with ⟨hzc, hvc⟩ | ⟨hzc, hvc⟩
        · intro hcon
          exact hne ((hzc.symm.trans hcon.symm).trans hvc)
        · intro hcon
          exact hne.symm ((hzc.symm.trans hcon.symm).trans hvc)
      rw [hWdef] at hzW
      obtain ⟨j₀, hj₀⟩ := hzW
      have j₀ne : j₀ ≠ r := fun hc => hzne (by rw [hc] at hj₀; exact hj₀.symm)
      have hdle : dist (xst r) z ≤ 2 * h0 := by
        rcases fnxPairEnds (x := xst r) (y := z) hab.symm hne with ⟨hzc, hvc⟩ | ⟨hzc, hvc⟩
        · rw [hzc, hvc]; exact hd
        · rw [hzc, hvc, dist_comm b a]; exact hd
      rw [hdydef]
      calc fnxNnDist xst r ≤ dist (xst r) z :=
          fnxNnDistLe (f := xst) (i := r) (t := dist (xst r) z)
            ⟨j₀, j₀ne, by rw [← hj₀]⟩
        _ ≤ 2 * h0 := hdle
    have hdyGe2 : (2:ℝ) ≤ dy := by
      rw [hdydef]
      exact fnxNnDistGe (hneEr r) (fun j hj => hpair r j hj.symm)
    -- 余量 e（HOL e_cond 指标形式）
    obtain ⟨e, he0, hem⟩ := fnxMarginExists xst r dy (fun j hj => by
      rw [hdydef]
      exact fnxNnDistLe (f := xst) (i := r) (t := dist (xst j) (xst r))
        ⟨j, hj, by rw [dist_comm]⟩)
    -- 扰动 u（经 perturbationLemma：等范数 + S 上远离 + 位移 < e）
    obtain ⟨u, hunorm, haway, hdu⟩ := perturbationLemma e he0 hn0 hydot S hSip
    have hdur : dist (xst r) u < e := hdu
    -- 关键估计 hK：dy < dist (xst i, u) 对一切 i ≠ r（= dy 者经扰动远离；≠ dy 者经余量）
    have hK : ∀ i, i ≠ r → dy < dist (xst i) u := by
      intro i hir
      by_cases hiD : dist (xst i) (xst r) = dy
      · have hiS : xst i ∈ S :=
          hEstDMem (xst i) (Set.mem_range_self i) (fun h => hir (hxinj h.symm))
            (by rw [hiD]; exact hdyh0)
        have h1 := haway (xst i) hiS
        rw [dist_comm (xst r) (xst i), hiD, dist_comm u (xst i)] at h1
        exact h1
      · have hm := hem i hir hiD
        have htri : dist (xst i) (xst r) ≤ dist (xst i) u + dist u (xst r) :=
          dist_triangle (xst i) u (xst r)
        have hdur' : dist u (xst r) < e := by
          rw [dist_comm]
          exact hdur
        linarith
    -- hPa：扰动后 r 行最近邻距离严格增大
    have hPa : dy < fnxNnDist (Function.update xst r u) r := by
      obtain ⟨j₀, hj₀r, hd0⟩ := fnxNnDistAttained
        (f := Function.update xst r u) (i := r) (hneEr r)
      rw [Function.update_self, Function.update_of_ne hj₀r, dist_comm u (xst j₀)] at hd0
      rw [← hd0]
      exact hK j₀ hj₀r
    -- hD：dy 以下的行为保持严格在 dy 之上
    have hD : ∀ i : Fin k, i ≠ r → dy < fnxNnDist xst i →
        dy < fnxNnDist (Function.update xst r u) i := by
      intro i hir hgt
      by_contra hcon
      push_neg at hcon
      obtain ⟨j₀, hj₀i, hd0⟩ := fnxNnDistAttained
        (f := Function.update xst r u) (i := i) (hneEr i)
      rcases eq_or_ne j₀ r with hj₀r | hj₀r
      · rw [hj₀r, Function.update_of_ne hir, Function.update_self] at hd0
        rw [← hd0] at hcon
        exact absurd (hK i hir) (not_lt.mpr hcon)
      · rw [Function.update_of_ne hir, Function.update_of_ne hj₀r] at hd0
        rw [← hd0] at hcon
        have hle : fnxNnDist xst i ≤ dist (xst i) (xst j₀) :=
          fnxNnDistLe (f := xst) (i := i) (t := dist (xst i) (xst j₀))
            ⟨j₀, hj₀i, le_refl _⟩
        exact absurd hgt (not_lt.mpr (hle.trans hcon))
    -- annulus 成员只依赖范数
    have hAnnNorm : ∀ v w : V3, v ∈ ballAnnulus → ‖w‖ = ‖v‖ → w ∈ ballAnnulus := by
      intro v w hv hweq
      simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        dist_zero_right] at hv ⊢
      rw [hweq]
      exact hv
    -- 扰动配置 fp := update xst r u 仍是合法配置
    have hfpAnn : ∀ i, Function.update xst r u i ∈ ballAnnulus := by
      intro i
      by_cases hir : i = r
      · rw [hir, Function.update_self]
        exact hAnnNorm _ _ (hann r) hunorm
      · rw [Function.update_of_ne hir]
        exact hann i
    have hfpPair : ∀ i j : Fin k, i ≠ j →
        2 ≤ dist (Function.update xst r u i) (Function.update xst r u j) := by
      intro i j hij
      by_cases hir : i = r
      · have hjr : j ≠ r := fun hc => hij (hir.trans hc.symm)
        rw [hir, Function.update_self, Function.update_of_ne hjr, dist_comm u (xst j)]
        exact hdyGe2.trans (hK j hjr).le
      · by_cases hjr : j = r
        · rw [Function.update_of_ne hir, hjr, Function.update_self]
          exact hdyGe2.trans (hK i hir).le
        · rw [Function.update_of_ne hir, Function.update_of_ne hjr]
          exact hpair i j hij
    have hfpR : Function.update xst r u ∈ R :=
      ⟨hfpAnn, hfpPair, σ, fun i => by
        by_cases hir : σ i = r
        · have h1 := hnorm i
          rw [hir] at h1
          rw [hir, Function.update_self, hunorm]
          exact h1
        · rw [Function.update_of_ne hir]
          exact hnorm i⟩
    -- 计数：fp 侧 dy-以下计数比 xst 侧严格小（r 行移出），以此定出分歧级 n0
    have hfrnotin : r ∉ Finset.univ.filter
        (fun i => fnxNnDist (Function.update xst r u) i ≤ dy) := by
      intro hmem
      have hle : fnxNnDist (Function.update xst r u) r ≤ dy :=
        (Finset.mem_filter.mp hmem).2
      linarith
    set n0 : ℕ := (Finset.univ.filter
      (fun i => fnxNnDist (Function.update xst r u) i ≤ dy)).card with hn0def
    have hn0lt : n0 < k := by
      have hsub : Finset.univ.filter (fun i => fnxNnDist (Function.update xst r u) i ≤ dy)
          ⊆ Finset.univ.erase r := by
        intro i hi
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
        intro hc
        rw [hc] at hi
        exact hfrnotin hi
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_erase_of_mem (Finset.mem_univ (α := Fin k) r)
      have h3 : (Finset.univ : Finset (Fin k)).card = k :=
        Finset.card_univ.trans (Fintype.card_fin k)
      omega
    have hDsub : ∀ i : Fin k, fnxNnDist (Function.update xst r u) i ≤ dy →
        fnxNnDist xst i ≤ dy := by
      intro i hi
      by_cases hir : i = r
      · rw [hir, hdyEq]
      · rcases lt_or_ge dy (fnxNnDist xst i) with hlt | hle'
        · have hcon := hD i hir hlt
          linarith
        · exact hle'
    have hcntxdy : n0 + 1 ≤ (Finset.univ.filter (fun i => fnxNnDist xst i ≤ dy)).card := by
      have hsub : insert r (Finset.univ.filter
          (fun i => fnxNnDist (Function.update xst r u) i ≤ dy))
          ⊆ Finset.univ.filter (fun i => fnxNnDist xst i ≤ dy) := by
        intro i hi
        rcases Finset.mem_insert.mp hi with hc | hi
        · rw [hc]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hdyEq.le⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
            hDsub i (Finset.mem_filter.mp hi).2⟩
      have hcard := Finset.card_insert_of_notMem hfrnotin
      have hle := Finset.card_le_card hsub
      omega
    -- 低于 dy 处两侧计数逐点相等
    have hLowSetEq : ∀ t : ℝ, t < dy →
        (Finset.univ.filter (fun i => fnxNnDist xst i ≤ t))
          = Finset.univ.filter (fun i => fnxNnDist (Function.update xst r u) i ≤ t) := by
      intro t htlt
      refine Finset.ext fun i => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hir : i = r
      · constructor
        · intro hx
          rw [hir, hdyEq] at hx
          have hx' : dy ≤ t := hx
          linarith
        · intro hf
          rw [hir] at hf
          have hf' : fnxNnDist (Function.update xst r u) r ≤ t := hf
          have hgt := htlt.trans hPa
          linarith
      · constructor
        · intro hx
          obtain ⟨j₀, hj₀i, hd0⟩ := fnxNnDistAttained (f := xst) (i := i) (hneEr i)
          rcases eq_or_ne j₀ r with hj₀r | hj₀r
          · rw [hj₀r] at hd0
            have hdy : dy ≤ dist (xst r) (xst i) :=
              fnxNnDistLe (f := xst) (i := r) (t := dist (xst r) (xst i))
                ⟨i, hir, le_refl _⟩
            rw [dist_comm (xst r) (xst i), hd0] at hdy
            have hdy' : dy ≤ fnxNnDist xst i := hdy
            have hx' : fnxNnDist xst i ≤ t := hx
            linarith
          · refine fnxUpdNnDistLe hir ⟨j₀, hj₀i, hj₀r, ?_⟩
            rw [hd0]
            exact hx
        · intro hf
          obtain ⟨j₀, hj₀i, hd0⟩ := fnxNnDistAttained
            (f := Function.update xst r u) (i := i) (hneEr i)
          rcases eq_or_ne j₀ r with hj₀r | hj₀r
          · rw [hj₀r, Function.update_of_ne hir, Function.update_self] at hd0
            rw [← hd0] at hf
            have hf' : dist (xst i) u ≤ t := hf
            have hgt := htlt.trans (hK i hir)
            linarith
          · rw [Function.update_of_ne hir, Function.update_of_ne hj₀r] at hd0
            rw [← hd0] at hf
            have hf' : dist (xst i) (xst j₀) ≤ t := hf
            exact fnxNnDistLe (f := xst) (i := i) (t := t) ⟨j₀, hj₀i, hf'⟩
    have hCntMono : ∀ (d : Fin k → V3) (s t : ℝ), s ≤ t →
        (Finset.univ.filter (fun i => fnxNnDist d i ≤ s)).card ≤
          (Finset.univ.filter (fun i => fnxNnDist d i ≤ t)).card := by
      intro d s t hst
      refine Finset.card_le_card ?_
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.trans hst⟩
    -- Master-iff：n0 以下各级阶次统计量相等
    have hcEq : ∀ j : ℕ, j < n0 →
        fnxOrdStat j (fun i => fnxNnDist (Function.update xst r u) i)
          = fnxOrdStat j (fun i => fnxNnDist xst i) := by
      intro j hj
      refine fnxOrdStatEqOfCount (j := j) (hj := by have := hn0lt; omega) ?_
      intro t
      by_cases ht : t < dy
      · rw [hLowSetEq t ht]
      · push_neg at ht
        constructor
        · intro _
          have h1 : j + 1 ≤ n0 + 1 := by omega
          have h3 := hCntMono xst dy t ht
          have h4 := hcntxdy
          omega
        · intro _
          have h1 : j + 1 ≤ n0 := by omega
          have h2 : n0 ≤ (Finset.univ.filter
              (fun i => fnxNnDist (Function.update xst r u) i ≤ t)).card := by
            rw [hn0def]
            exact hCntMono (Function.update xst r u) dy t ht
          omega
    -- 分歧级：xst 侧 n0 级 ≤ dy < fp 侧 n0 级
    have hF2b : fnxOrdStat n0 (fun i => fnxNnDist xst i) ≤ dy :=
      (fnxOrdStatLeIff (hj := hn0lt) (d := fun i => fnxNnDist xst i) (t := dy)).2 hcntxdy
    have hF2a : dy < fnxOrdStat n0
        (fun i => fnxNnDist (Function.update xst r u) i) := by
      by_contra hcon
      push_neg at hcon
      have hle := (fnxOrdStatLeIff (hj := hn0lt)
        (d := fun i => fnxNnDist (Function.update xst r u) i) (t := dy)).1 hcon
      rw [hn0def] at hle
      omega
    -- c 与 fnxOrdStat 的桥（绕 set-不透明）
    have hcjFp : ∀ j : ℕ, c j (Function.update xst r u)
        = fnxOrdStat j (fun i => fnxNnDist (Function.update xst r u) i) := by
      intro j
      simp only [hcc, hdd]
    have hcjXs : ∀ j : ℕ, c j xst = fnxOrdStat j (fun i => fnxNnDist xst i) := by
      intro j
      simp only [hcc, hdd]
    -- fp 沿链逐级驻留（前 n0 级统计量与 xst 相同）
    have hfpChain : ∀ j : ℕ, j ≤ n0 →
        Function.update xst r u ∈ fnxChain R c j := by
      intro j
      induction j with
      | zero => intro _; exact fnxChainMemZero hfpR
      | succ j ih =>
          intro hj
          refine fnxChainSuccMem (ih (by omega)) ?_
          intro y hy
          have hxs : xst ∈ fnxChain R c (j + 1) :=
            fnxChainSubOfLe k (j + 1) (by have := hn0lt; omega) hxst
          have hmax := (fnxChainSuccMemImp hxs).2 y hy
          rw [hcjFp j, hcEq j (by omega), ← hcjXs j]
          exact hmax
    -- 末步矛盾：xst ∈ C (n0+1) 的 argmax 性质撞上 c n0 xst ≤ dy < c n0 fp
    have hxsC : xst ∈ fnxChain R c (n0 + 1) :=
      fnxChainSubOfLe k (n0 + 1) (by omega) hxst
    have hcon := (fnxChainSuccMemImp hxsC).2
      (Function.update xst r u) (hfpChain n0 (le_refl _))
    rw [hcjFp n0, hcjXs n0] at hcon
    exact absurd hF2a (not_lt.mpr (hcon.trans hF2b))

/-- **CPNKNXN**（flyspeck_devol.hl:135，2026-10-12 A4 填证 lane）：
packing 可扩为 saturated packing 超集（Zorn：`zorn_subset_nonempty`，链并
仍是 packing；饱和性经极大性的单点扩充论证，HOL :135-167 逐步镜像）。 -/
private theorem cpnknxn {V : Set V3} (hV : Packing V) :
    ∃ V' : Set V3, Packing V' ∧ saturated V' ∧ V ⊆ V' := by
  classical
  have hchain : ∀ c ⊆ {W : Set V3 | Packing W ∧ V ⊆ W}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ ({W : Set V3 | Packing W ∧ V ⊆ W} : Set (Set V3)), ∀ s ∈ c, s ⊆ ub := by
    intro c hcsub hchain hcne
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · -- packing (⋃₀ c)：两点落在链的同一（较大）元内
      intro u hu v hv hd
      obtain ⟨W₁, hW₁c, hu₁⟩ := hu
      obtain ⟨W₂, hW₂c, hv₁⟩ := hv
      by_cases hWeq : W₁ = W₂
      · subst hWeq
        exact (hcsub hW₂c).1 u hu₁ v hv₁ hd
      · rcases hchain hW₁c hW₂c hWeq with hsub | hsub
        · exact (hcsub hW₂c).1 u (hsub hu₁) v hv₁ hd
        · exact (hcsub hW₁c).1 u hu₁ v (hsub hv₁) hd
    · -- V ⊆ ⋃₀ c
      intro x hx
      obtain ⟨W₀, hW₀c⟩ := hcne
      exact ⟨W₀, hW₀c, (hcsub hW₀c).2 hx⟩
  obtain ⟨V', hxin, hmax⟩ :=
    zorn_subset_nonempty ({W : Set V3 | Packing W ∧ V ⊆ W} : Set (Set V3)) hchain V
      ⟨hV, Subset.rfl⟩
  refine ⟨V', hmax.1.1, ?_, hmax.1.2⟩
  -- saturated：单点扩充的极大性论证
  intro x
  by_contra hx0
  have hx0 : ∀ y ∈ V', 2 ≤ dist x y := by
    intro y hy
    by_contra hlt
    exact hx0 ⟨y, hy, not_le.mp hlt⟩
  have hins : insert x V' ∈ ({W : Set V3 | Packing W ∧ V ⊆ W} : Set (Set V3)) := by
    refine ⟨?_, Subset.trans hmax.1.2 (Set.subset_insert x V')⟩
    intro u hu v hv hd
    rcases Set.mem_insert_iff.mp hu with rfl | hu' <;>
      rcases Set.mem_insert_iff.mp hv with rfl | hv'
    · rfl
    · exact absurd hd (not_lt.2 (hx0 v hv'))
    · exact absurd hd (not_lt.2 (by rw [dist_comm]; exact hx0 u hu'))
    · exact hmax.1.1 u hu' v hv' hd
  have heq : insert x V' = V' :=
    (hmax.eq_of_subset hins (Set.subset_insert x V')).symm
  have hxin' : x ∈ insert x V' := Set.mem_insert x V'
  rw [heq] at hxin'
  have hxx := hx0 x hxin'
  rw [dist_self] at hxx
  linarith

/-- 单位球体积（实值测度；`EuclideanSpace.volume_ball_fin_three` 的 toReal
折算，2026-10-12 A4 填证 lane）。 -/
private theorem kcUnitBallVol (v : V3) :
    MeasureTheory.volume.real (Metric.ball v 1) = Real.pi * 4 / 3 := by
  rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 by norm_num),
    ENNReal.toReal_ofReal (show (0:ℝ) ≤ Real.pi * 4 / 3 by linarith [Real.pi_pos])]
  norm_num

/-- **FLYSPECK_DEVOLUTION**（flyspeck_devol.hl:25，2026-10-12 A4 填证 lane）：
体积形界 ⟹ 计数形界。测度论证：V∩ball(0,r) 中每点的单位球互斥且含于
ball(0,r+1)，`card · vol(ball 1) = vol(⋃ unit balls) ≤ vol(体积界集)`，在 r+1
处折算 c ↦ π/√18·7 + |c|·4；有限性用 `Packing.finite_inter_ball`
（HOL FINITE_PACK_LEMMA 对应）。注：HOL 原文以 saturated V 为前提，但证明
只消费 packing（有限性/互斥性），饱和性不在本步使用。 -/
private theorem flyspeckDevolution {V : Set V3} (hV : Packing V)
    (hvol : ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      MeasureTheory.volume.real ((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 r) /
        MeasureTheory.volume.real (Metric.ball (0 : V3) r) ≤
          Real.pi / Real.sqrt 18 + c / r) :
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r → ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
      Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2 := by
  obtain ⟨c₀, hc₀⟩ := hvol
  refine ⟨Real.pi / Real.sqrt 18 * 7 + |c₀| * 4, fun r hr => ?_⟩
  have hfF : (V ∩ Metric.ball 0 r).Finite := hV.finite_inter_ball r
  set T : Finset V3 := hfF.toFinset with hTeq
  have hmem : ∀ v ∈ T, v ∈ V := fun v hv => (hfF.mem_toFinset.mp hv).1
  have hballr : ∀ v ∈ T, dist v 0 < r := fun v hv => Metric.mem_ball.mp
    ((hfF.mem_toFinset.mp hv).2)
  -- 单位球族互斥（packing ⇒ 距离 ≥ 2）
  have hdisj : ((T : Set V3)).PairwiseDisjoint (fun v => Metric.ball v 1) := by
    intro u hu v hv hne
    simp only [Function.onFun]
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne'
    obtain ⟨w, hwu, hwv⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    have hdist := hV.dist_ge_two (hmem u hu) (hmem v hv) hne
    have htri : dist u v ≤ dist u w + dist w v := dist_triangle u w v
    rw [Metric.mem_ball] at hwu hwv
    linarith [dist_comm u w ▸ hwu]
  -- 计数 = 测度
  have htopEach : ∀ v ∈ T, MeasureTheory.volume (Metric.ball v 1) ≠ (⊤:ENNReal) := by
    intro v _
    rw [EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hcount : MeasureTheory.volume.real (⋃ v ∈ T, Metric.ball v 1)
      = (T.card : ℝ) * (Real.pi * 4 / 3) := by
    rw [MeasureTheory.Measure.real_def,
      MeasureTheory.measure_biUnion_finset hdisj
        (fun v _ => measurableSet_ball),
      ENNReal.toReal_sum htopEach]
    have hsumreal : ∀ v ∈ T,
        (MeasureTheory.volume (Metric.ball v 1)).toReal = Real.pi * 4 / 3 :=
      fun v _ => kcUnitBallVol v
    rw [Finset.sum_congr rfl hsumreal, Finset.sum_const, nsmul_eq_mul]
  -- 包含
  have hsub : (⋃ v ∈ T, Metric.ball v 1) ⊆
      ((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 (r + 1) : Set V3) := by
    intro w hw
    refine ⟨?_, ?_⟩
    · simp only [mem_iUnion, exists_prop] at hw ⊢
      obtain ⟨v, hvT, hwv⟩ := hw
      exact ⟨v, hmem v hvT, hwv⟩
    · simp only [mem_iUnion, exists_prop] at hw
      obtain ⟨v, hvT, hwv⟩ := hw
      rw [Metric.mem_ball] at hwv ⊢
      have hvr := hballr v hvT
      calc dist w 0 ≤ dist w v + dist v 0 := dist_triangle w v 0
        _ < 1 + r := by linarith
        _ = r + 1 := by ring
  -- 体积界在 r+1 处
  have hm : (0:ℝ) < Real.pi * 4 / 3 := by linarith [Real.pi_pos]
  have hr1 : 1 ≤ r + 1 := by linarith
  have hvkc := hc₀ (r + 1) hr1
  have hbig : MeasureTheory.volume.real (Metric.ball (0 : V3) (r + 1))
      = (r + 1) ^ 3 * (Real.pi * 4 / 3) := by
    rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ r + 1),
      ENNReal.toReal_ofReal (show (0:ℝ) ≤ Real.pi * 4 / 3 by linarith [Real.pi_pos])]
  have hbpos : (0:ℝ) < MeasureTheory.volume.real (Metric.ball (0 : V3) (r + 1)) := by
    rw [hbig]
    exact mul_pos (pow_pos (by linarith : (0:ℝ) < r + 1) 3)
      (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi * 4 / 3)
  have hballtop : MeasureTheory.volume (Metric.ball (0 : V3) (r + 1)) ≠ (⊤:ENNReal) := by
    rw [EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hBIGsub : ((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 (r + 1) : Set V3) ⊆
      Metric.ball (0 : V3) (r + 1) := Set.inter_subset_right
  have hmonoENN := MeasureTheory.measure_mono hBIGsub (μ := MeasureTheory.volume)
  have hBIGtop : MeasureTheory.volume
      ((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 (r + 1) : Set V3) ≠ (⊤:ENNReal) := by
    intro h
    rw [h] at hmonoENN
    exact hballtop (top_le_iff.mp hmonoENN)
  have hmono : MeasureTheory.volume.real (⋃ v ∈ T, Metric.ball v 1) ≤
      MeasureTheory.volume.real ((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 (r + 1) : Set V3) := by
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
    refine (ENNReal.toReal_le_toReal ?_ hBIGtop).mpr
      (MeasureTheory.measure_mono hsub (μ := MeasureTheory.volume))
    intro h
    have h1 := MeasureTheory.measure_mono hsub (μ := MeasureTheory.volume)
    rw [h] at h1
    exact hballtop (top_le_iff.mp (le_trans h1 hmonoENN))
  -- 折算链
  have h2 := (div_le_iff₀ hbpos).mp hvkc
  rw [hbig] at h2
  have hchain : (T.card : ℝ) * (Real.pi * 4 / 3) ≤
      (Real.pi / Real.sqrt 18 * (r + 1) ^ 3 + c₀ * (r + 1) ^ 2) * (Real.pi * 4 / 3) := by
    have hsplit : (Real.pi / Real.sqrt 18 + c₀ / (r + 1)) *
        ((r + 1) ^ 3 * (Real.pi * 4 / 3))
        = (Real.pi / Real.sqrt 18 * (r + 1) ^ 3 + c₀ * (r + 1) ^ 2) *
            (Real.pi * 4 / 3) := by
      have hrne : (r + 1 : ℝ) ≠ 0 := by linarith
      field_simp
      all_goals { ring }
    rw [hsplit] at h2
    have h1 : (T.card : ℝ) * (Real.pi * 4 / 3) ≤
        MeasureTheory.volume.real
          ((⋃ v ∈ V, Metric.ball v 1) ∩ Metric.ball 0 (r + 1) : Set V3) := by
      rw [← hcount]
      exact hmono
    linarith
  have hstep : (T.card : ℝ) ≤
      Real.pi / Real.sqrt 18 * (r + 1) ^ 3 + c₀ * (r + 1) ^ 2 :=
    le_of_mul_le_mul_right hchain hm
  -- 初等不等式收尾（(r+1)³ ≤ r³+7r²、(r+1)² ≤ 4r²，r ≥ 1）
  have hsq1 : (0:ℝ) ≤ 4 * r ^ 2 - 3 * r - 1 := by nlinarith
  have h41 : (r + 1) ^ 3 ≤ r ^ 3 + 7 * r ^ 2 := by
    have e : (r + 1) ^ 3 = r ^ 3 + 3 * r ^ 2 + 3 * r + 1 := by ring
    rw [e]
    linarith [sq_nonneg r, hsq1]
  have hsq2 : (0:ℝ) ≤ 3 * r ^ 2 - 2 * r - 1 := by nlinarith
  have h42 : (r + 1) ^ 2 ≤ 4 * r ^ 2 := by
    have e : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    rw [e]
    linarith
  have hK : (0:ℝ) ≤ Real.pi / Real.sqrt 18 :=
    div_nonneg Real.pi_nonneg (le_of_lt (by positivity))
  have hfin1 : Real.pi / Real.sqrt 18 * (r + 1) ^ 3
      ≤ Real.pi / Real.sqrt 18 * r ^ 3 + Real.pi / Real.sqrt 18 * (7 * r ^ 2) :=
    (mul_le_mul_of_nonneg_left h41 hK).trans (by rw [mul_add])
  have hfin2 : c₀ * (r + 1) ^ 2 ≤ |c₀| * (r + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c₀) (sq_nonneg _)
  have hfin3 : |c₀| * (r + 1) ^ 2 ≤ |c₀| * (4 * r ^ 2) :=
    mul_le_mul_of_nonneg_left h42 (abs_nonneg _)
  rw [Set.ncard_eq_toFinset_card _ hfF]
  rw [hTeq] at hstep
  have hnorm : Real.pi * r ^ 3 / Real.sqrt 18 = Real.pi / Real.sqrt 18 * r ^ 3 := by ring
  rw [hnorm]
  have hdistr : (Real.pi / Real.sqrt 18 * 7 + |c₀| * 4) * r ^ 2
      = Real.pi / Real.sqrt 18 * (7 * r ^ 2) + |c₀| * (4 * r ^ 2) := by ring
  rw [hdistr]
  linarith [hstep, hfin1, hfin2, hfin3]

/-- 接口 → 真证明（2026-10-12 A4 填证 lane）：HOL `kc_imp_the_kc`
（the_main_statement.hl:82-107 逐步镜像）——CPNKNXN 扩 saturated 超集 →
hkc 给体积形界 → FLYSPECK_DEVOLUTION 折计数形界 → KIUMVTC（ncard 单调）
回传 V。 -/
theorem kcImpTheKc (hkc : keplerConjecture) : TheKeplerConjecture := by
  intro V hpackV
  obtain ⟨V', hpackV', hsatV', hsub⟩ := cpnknxn hpackV
  obtain ⟨cv, hcv⟩ := hkc V' ⟨hpackV', hsatV'⟩
  obtain ⟨c, hc⟩ := flyspeckDevolution hpackV' ⟨cv, hcv⟩
  exact ⟨c, fun r hr => by
    have hsubr : V ∩ Metric.ball 0 r ⊆ V' ∩ Metric.ball 0 r := by
      intro z hz
      exact ⟨hsub hz.1, hz.2⟩
    have hnc : ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
        ((V' ∩ Metric.ball 0 r).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsubr (hpackV'.finite_inter_ball r)
    linarith [hnc, hc r hr]⟩

/-- 骨架辅助：`Hypermap.Iso` 传递性（**已闭合 2026-09-21 填证波**；纯逻辑：
同构 = 双射 + 三映射交换，复合 `g ∘ f` 即得。对应 HOL `ISO_TRANS`/
`hypermap.hl:9614 iso` 的传递性）。 -/
theorem hypermapIsoTrans {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] {H : Hypermap α} {G : Hypermap β} {K : Hypermap γ}
    (h1 : HypermapIso H G) (h2 : HypermapIso G K) : HypermapIso H K := by
  obtain ⟨f, hf, hfc⟩ := h1
  obtain ⟨g, hg, hgc⟩ := h2
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  intro x hx
  have hfx : f x ∈ (G.darts : Set β) := hf.1 hx
  obtain ⟨he1, hn1, hfa1⟩ := hfc x hx
  obtain ⟨he2, hn2, hfa2⟩ := hgc (f x) hfx
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Function.comp_apply, he2, he1, hn2, hn1, hfa2, hfa1]

/-! ### 2d. LP 接口结构化（方向 D，2026-09-21）

HOL 蓝图（tame/linear_programming_results.hl）：`linear_programming_results` 的
证明 = 计算层（`Verify_all.verify_all` 逐图 LP，15+ 小时）产出逐图
`tame_linear_result` 实例 + 纯逻辑桥 `tame_result_lemma`（MESON 一步）。
Lean 镜像同构：唯一新接口 = 逐图证书总库（Phase 3 持久化填实，现 24k/43058；
桥章 formal_lp/hypermap 的 KCBLRQC/BDJYFFB/CRTTXAT 群为填实依赖）；
`linear_programming_results` 本体降级为纯逻辑真推导。 -/

/-- 中层骨架（**T2 展开波 2026-10-08**）：`lpArchiveCertificates` 的具名债点，
签名 = 冻结接口逐字。资产状态：deferred-compute（LP 重跑，等强机器）+
语义桥缺口。旁挂骨架层 = `Kepler.Text.LP.*`（Assembly 零 import 纯旁挂，
无循环）：记录清单数据 `LPIds`（43,078 条终端记录 = root 19,237 + easy
4,403 + hard 19,438，盘点与 STATUS 43,078 口径逐项吻合；infeasible 189）
+ per-record 独立具名叶 43,078 枚（`LPLeaf*`，open sorry，NEEDS 逐叶
deferred-compute）+ 内核真证量化装配 `LPAll`（`lpTerminalBoundAll`
42,889 bound 形 + `lpAllInfeas` 189 infeasible 形，master 清单分治覆盖）。
-- NEEDS: ①42,889 bound 叶逐条以重跑产物（`socert.py --col-major` 形，
PilotCM204880136538 样板）转发闭合 + 189 不可行证书通道定形；
②覆盖桥 = HOL formal_lp（verify_all/lp_certificate 链）的 Lean 移植：
per-record 总量 → 本骨架语句（每图终端树在 Contravening V + iso L
语境下的分支覆盖）。 -/
theorem lpArchiveCertificatesDebt (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
    ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V := by
  sorry

/-- 接口占位：逐图 LP 证书总库（HOL `Verify_all` 的 Lean 形——每张 archive 图
的 `tame_linear_result` 实例；前提 `LpIneqs`/`lp_main_estimate` 对应 HOL 证书
定理的 DISCH 假设）。**T2 展开波（2026-10-08）**：冻结签名一字未动，
证明体由匿名 `sorry` 重接线为具名债点 `lpArchiveCertificatesDebt`
（债务记账粒度自接口级下沉至 per-record 级，见 §3''）。 -/
theorem lpArchiveCertificates (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
    ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V :=
  lpArchiveCertificatesDebt hlpineq hmain

/-- HOL `tame_result_lemma` + `linear_programming_results_th` 最终装配
（纯逻辑部分真证明；债务集中于 `lpArchiveCertificates`）。 -/
theorem linearProgrammingResultsOf (hnl : TheNonlinearInequalities)
    (hcert : ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V) :
    LinearProgrammingResults :=
  fun V hfan ⟨_, _, ⟨L, hLa, hiso⟩⟩ => hcert V hfan L hLa hiso

/-! ## 3. 接口装配层（原三接口冻结 2026-09-19；§2b/2c 的骨架占位为
2026-09-21 方向 A 深挖新增，均计入主定理可达债务图）。
2026-10-08 T1 自上而下第一波：接口 1 `nonlinearInequalities` 已展开为
§2a' 具名骨架件的显式装配（冻结签名不变，单根 sorry 分解为按分量记账的
骨架节点）。 -/

/-- **接口 1 → T1 显式装配（2026-10-08；冻结签名 2026-09-19 一字未动）**。
证明体 = 六分量骨架件（§2a'）逐个引用的显式构造；原单根 `sorry` 由此分解：
sorryAx 仅自 14 枚开放骨架节点流入（1a-1d 切片组、2/2'、3/3'、4/4'、5/5'、
6/6'），分量 1 本体与 §2a 查表会师点为真推导/真叶。
债务归属（原冻结注记，继续有效）：Phase 4 / G4 粘合（P6-E）。消除顺序：
先填六个 ID 清单与 `CertifiedIneqHolds` 语义（语义已按处方落最小形——§2a），
再逐条闭合证书（自下而上波经 §2a 查表对接）。 -/
theorem nonlinearInequalities : TheNonlinearInequalities :=
  ⟨nliPackNonlinearNonOx3q1h, nliOx3q1h, nliMainNonlinearTerminalV11, nliLpIneqs,
    nliPackIneqDefA, nliKcblrqcIneqDef⟩

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

/-! ### 3'. T4 packing 分支前提树（2026-10-08；SF31 debt-bridge 形——
本节为**纯记账段**，冻结接口零扰动）

拓扑结论（T4 侦察）：packing 分支的债务在上游冻结接口中**不独占任何一根
Assembly 级 sorry**——`textCapstone` 证明体本身是真推导（与 tame 分支共用
同一真推导脊柱），packing 子树唯一的模块级入口是 PA25 导出锚
`PackingAuto25.PACKING_CHAPTER_MAIN_CONCLUSION`（:1033 处被冻结体逐字消费，
其签名随 textCapstone 冻结；`PackingAuto25.OXLZLEZ` 另被 PackingConcl
OXLZLEZ_concl 桥消费，签名同冻结）。故本波展开全部住在 PA25 模块内
（SF31 形：冻结签名不动、体经具名骨架重接线），本节只落拓扑与对账
（† = T1 波时行号，PA25 行位自 T4 波起漂移，以 grep 为准）：

```
textCapstone（§3，真推导，冻结）
├─ PACKING_CHAPTER_MAIN_CONCLUSION（PA25:3692†，真装配；HOL Oxlzlez 装配）
│  ├─ RDWKARC 臂（PA2:5199 ✅真证）：余债 = UPFZBZM_concl（PA2:5048 ⬜桩；
│  │    PA19.UPFZBZM ✅孪生已在 PackingConcl 桥接线，PA2 桩删除属 B4 波）
│  ├─ OXLZLEZ 臂（PA25:3674†，真装配）＝ CELL_CLUSTER_ESTIMATE_PROPS
│  │    （PA25 ⬜；T4 已展开：LEAF_RANK_PROPS 见证层 + cc_real_model_data
│  │     六切片 + 基数真叶）→ GRHIDFA_concl（PA3:711 ⬜，cc_v11 组合引擎，
│  │    1000-3000 行，材料单 §4 需新波 5）
│  └─ TSKAJXY 臂（PA21 ✅真装配）：余债 = TSKAJXY_034（PA21:1335 ⬜）
│       ← PA20 gammaX 双巨（B3 在飞）+ mi_gamma3f（PA21:973 ⬜）
├─ ox3q1hP25 / pack_nonlinear_non_ox3q1h（两枚 bank 前提）：
│    已由 §2a' T1 骨架 nliOx3q1h / nliPackNonlinearNonOx3q1h 具名承接；
│    PA25 侧消费位 = pkrmQuarter ← real_model_ox3q1h_merge（同根对账）
├─ fcdjdot（§2c，⬜）：FNJLBXS 章（FCDJDOT section :1543-1806，
│    not_surrounded_ECTC + perturbation_lemma）未移植；忠实重述需 setOfEdge
│    镜像（同 hypermapOfFanNeg 的 NEEDS 工具链），本波不动其体
└─ kcImpTheKc（§2c，⬜）：共用根（处方已备：FLYSPECK_DEVOLUTION + CPNKNXN
     + KIUMVTC），非 packing 拓扑独占，不动

B→T 会师对账（PA25 侧，本波接线）：real_periodic_data ✅ / cc_card_data ✅ /
cc_real_data ✅ / cc_bool_data ✅ / cc_real_dat_def ✅ 五枚在库真件自 T4
切片层进入 e2e 依赖闭包（此前为孤儿真件）；PK25 债务图自本波起 = W1/W2 +
pkrmAzim/Quarter/Qu/Qx/Qy 五切片 + 29 枚 bank 叶 + LEAF_RANK 既有叶
（全具名，见 PA25 T4 两节注记）。 -/

/-! ### 3''. T2 LP 分支 per-record 骨架层（2026-10-08；纯记账段，
冻结接口零扰动——`lpArchiveCertificates` 证明体重接线至 §2d'
`lpArchiveCertificatesDebt`，骨架层全部住 `Kepler/Text/LP/` 旁挂模块）

LP 分支拓扑（T2 侦察）：接口 2 的唯一上游 sorry 根 =
`lpArchiveCertificates`（:984†，†=T2 波前行号）；`linearProgrammingResultsOf`
本体为真推导，`linearProgrammingResults` 消费
`nonlinear_imp_lp_main_estimate_p16`（真链）。展开形 = P6-C goodListArchive
先例（数据层 + 分片叶 + 内核组合器）× T1 SF36 先例（ID 清单 + 注册表
量化命题），全库确定性重导：

```
lpArchiveCertificates（§2d'，冻结签名）
└─ lpArchiveCertificatesDebt（§2d'，具名债点，同签名 ⬜）
   ├─ 覆盖桥（⬜ 真缺口）：HOL formal_lp verify_all/lp_certificate 链
   │    未移植——per-record 总量 ⟹ ¬Contravening V
   ├─ lpTerminalBoundAll（Kepler.Text.LP.LPAll ✅内核真证装配）
   │  └─ 42,889 枚 bound 形 per-record 叶（LPLeaf{Root,Easy,Hard}*.lean，
   │     root 19,237 / easy 4,362 / hard 19,290；逐叶 ⬜ deferred-compute：
   │     LP 重跑 = SoPlex 精确主批 + glpsol 精确对偶尾部）
   └─ lpAllInfeas（✅内核真证装配）
      └─ 189 枚 infeasible 形叶（LPLeafInfeas00；PLACEHOLDER(LP-infeas)
         语义，不可行性证书通道 ⬜ 待定形）

记录清单口径（PLAN §5 T2 的 6,925 对账）：6,925 = 2026-09-24 旧持久化波的
dedup 任务队列数（主批 6,866 + glpsol 尾部 59；results.jsonl 随旧服务器
丢失，不可重建）——那是运行工件粒度；本层按**终端记录粒度**展开全库可
导出的 43,078 条（root 19,237 + easy 4,403 + hard 19,438，19,715 图全覆盖，
与 STATUS「43,078 个终端 LP 内核验证」逐项吻合；盘点器 =
lean/scripts/gen_lp_skeleton.py，--check 基线校验，退出码 2 = 清单漂移
须人工裁决）。旧波 6,925 任务中的每条记录均在本层 43,078 全集内
（dedup 不产生新记录），零编造、零遗漏。

退化防线（对齐 §2a else-True 警告文化）：`LpTerminalCertified` 的见证
存在性对 id 不敏感（LPCert 保真缺口在案）——叶闭合只准走该记录自己的
重跑产物模块转发，不准跨记录借用见证；接线波落「记录 ↔ 产物模块」
恒等钉定后收敛。infeasible 形 189 条不得经 `:= True` 占位计为已证。 -/

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
#print axioms contraveningFan
#print axioms the_kepler_conjecture_from_interfaces
#print axioms Kepler.the_kepler_conjecture

end Kepler.Assembly

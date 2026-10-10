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
import Kepler.Assembly.GoodListDefs
import Kepler.Assembly.GoodListAll
-- T1 自上而下第一波（2026-10-08）：六 ID 清单数据（P6-E 生成件，零依赖）+
-- `CertifiedIneqHolds` 查表的试点链（G4 证书 C3397113841 + 粘合 + 语义命题）。
import Kepler.Assembly.IdLists
import Kepler.Assembly.IneqPilot

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

/-- 中层骨架 1a：cell3 切片组（HOL `cell3_hyp` merge_ineq.hl:3490-3495；
PackingAuto21.lean:376 显式盒式 `∀ y…` 七条：QZECFIC wt0/wt0corner/wt0sqrt8/
wt1/wt2A + CIHTIUM + CJFZZDW）。
资产状态：deferred-compute——语句已在 PA21 显式成形，证书不在库（68 例
旧机丢失口径）。
-- NEEDS: 七条逐条 G4 证书 + 粘合入 §2a 查表（对接 IneqPilot 样板链）。 -/
theorem nliCell3Bank : cell3_bank := sorry

/-- 中层骨架 1b：TSKAJXY 切片组（merge_ineq.hl:1370-1377 string 序；
PackingAuto21.lean:381 十条显式盒式不等式）。
资产状态：deferred-compute（同 1a）。
-- NEEDS: 十条逐条 G4 证书 + 粘合入查表。 -/
theorem nliTskBank : tsk_bank := sorry

/-- 中层骨架 1c：GRKIBMP 切片组（merge_ineq.hl:3795 add_hyp 序；
PackingAuto21.lean:389，`GRKIBMP A V2` + `GRKIBMP B V2`，ineq.hl:1520/1537）。
资产状态：**真缺口**——`GRKIBMP B V2` 属 16 条真残余清单（尖锐边界组：
有真反例叶，需 ε 余量或弱编码，STATUS.md Phase 4）。
-- NEEDS: A V2 出证书；B V2 定策略（ε 余量/弱编码/域剖分）后重解。 -/
theorem nliGrkBank : grk_bank := sorry

/-- 中层骨架 1d：81 条清单的其余 62 条 rest 叶（PackingAuto21.lean:395
`PLACEHOLDER(G4)`；JSPEVYT/IXPOTPA/TXQTPVC/TEWNSCJ/QITNPEA 家族/
ZTGIJCF0/4 生成族/GCKBQEA/RQWUDDU/6096597438/1965189142 等）。
资产状态：混合——`QITNPEA 3725403817` 已内核闭合（964,984 叶，2026-09-18，
公理标准三）；`1965189142 34` 证书在库（Interval/Cases/C1965189142x34）；
其余 deferred-compute（92 prep 家族重做口径覆盖其中多数）。
-- NEEDS: PA21 rest 叶拆单条时同步展开本骨架；在库两案补粘合引理入查表。 -/
theorem nliPackNonlinearRest : pack_nonlinear_rest := sorry

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

/-- 接口占位：HOL `Mqmsmab.MQMSMAB`（tame_concl / MQMSMAB-compiled.hl；section
前提 `kcblrqc_ineq_def` ∧ `lp_main_estimate` 显式化）。 -/
theorem mqmsmab (V : Set V3) (hkcblrqc : KcblrqcIneqDef) (hmain : lp_main_estimate)
    (hfan : FAN 0 V (ESTD V)) (hc : Contravening V) :
    TamePlanarHypermap (hypermapOfFan 0 V (ESTD V) hfan) := by
  sorry

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

/-- 接口占位：HOL `Elllnyz.ELLLNYZ`（ELLLNYZ.hl）——镜像析取形，脊柱的图桥
必须保持此形（phase6-spine.md §5）。`hypermap_of_list y` 侧为存在性产出。 -/
theorem elllnyz (x y : fgraph ℕ) (hx : GoodList x) (hy : GoodList y)
    (hiso : iso_fgraph x y) (Hx : Hypermap (ℕ × ℕ)) (hHx : IsHypermapOfList x Hx) :
    ∃ Hy : Hypermap (ℕ × ℕ), IsHypermapOfList y Hy ∧
      (HypermapIso Hx Hy ∨ HypermapIso (oppositeHypermap Hx) Hy) := by
  sorry

/-! NEEDS(hypermapOfFanNeg，2026-09-28 脊柱 lane)：HOL ASFUTBF.hl:1007
`hypermap_of_fan_neg` 的结论是 `iso (hypermap_of_fan (IMAGE -- …)) (opposite_hypermap …)`
——负号 fan 是镜像（V ↦ -V 定向反转），Lean 侧需整套 negation-equivariance 工具链：
①`azim_mirror`（azim (−v) (−w) (−w1) (−w2) = 2π − azim v w w1 w2，零情形单独；
经 Geom/Azim.lean 的 AzimSpec + azim_eq_of_spec，frame 取 e_i ↦ −e_i 时右手性翻转，
ψ ↦ −ψ）；②`sigmaFan` 镜像/逆（sigmaFan(−V)(−E)(−v)(−w) = −σ⁻¹(V)(v,w)，需
azim_mirror + argmin 最小值传递，即 HOL Localization 的 ivs_azim_cycle 群）；
③setOfEdge/dartOfFan 像集引理（机械）；④hypermapOfFan 构造层（dartsetLeadsInto
三个 permutes 字段的像集搬运）。HOL 全套在 ASFUTBF.hl:182-699（scriptL_negative/
CARD_NEGATIVE/ESTD_NEG/ECTC_NEG/set_of_edge_neg/dart_of_fan_neg/azim_fan_neg/
azim_dart_neg）；数据合取项的 Lean 私件已备（见 `contraveningNegative` 上方
`negInjOn`—`scriptLMaxNegative` 块），镜像链三件（①②④）仍缺。 -/

/-- 接口占位：HOL `Asfutbf.hypermap_of_fan_neg`（ASFUTBF.hl）。 -/
theorem hypermapOfFanNeg (V : Set V3) (hc : Contravening V) (hfan : FAN 0 V (ESTD V))
    (hfan' : FAN 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V))) :
    HypermapIso
      (hypermapOfFan 0 ((fun v => -v) '' V) (ESTD ((fun v => -v) '' V)) hfan')
      (oppositeHypermap (hypermapOfFan 0 V (ESTD V) hfan)) := by
  sorry

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

/-! ### 2c.5 `contravening_negative` 数据合取项私件（2026-09-28 脊柱 lane）

对照 HOL ASFUTBF.hl:182-298（`scriptL_negative` / `CARD_NEGATIVE` / `ESTD_NEG` /
`ECTC_NEG` / `packing_negative` / `ball_annulus_negative`，六件全真证明镜像）。
`contravening V` 的前五个数据合取项（packing / ball_annulus / scriptL / max /
card）由它们直接装配；**剩余卡点** = 第 6/7 合取项 `surroundedNode`：负号 fan 是
镜像（定向反转），需要 `azim (−v) (−w) (−w1) (−w2) = 2π − azim`（非平凡不变式，
经 AzimSpec frame 取反）+ `sigmaFan` 镜像逆（HOL Localization ivs_azim_cycle 群）
——该工具链全树未移植，见 `hypermapOfFanNeg` 上方 NEEDS 注记。 -/

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

/-! NEEDS（2026-09-28 脊柱 lane）：前五数据合取项已由上方私件装配齐
（`contraveningNegative` 证明体只剩
`refine ⟨packingNegative hc.1, ballAnnulusNegative hc.2.1, scriptLNegative V ▸ hc.2.2.1,
  scriptLMaxNegative V hc.2.2.1, cardNegative V ▸ hc.2.2.2.2.1, ?_, ?_⟩`），
第 6/7 合取项 `surroundedNode (neg''V) (ESTD/ECTC (neg''V)) v` 卡**镜像链**：
V ↦ -V 定向反转，azim 非不变而是 `azim(−) = 2π − azim`，需 `azim_mirror`
（AzimSpec frame 取反版）+ `sigmaFan` 镜像逆（HOL Localization.ivs_azim_cycle 群，
全树未移植）+ setOfEdge/dartOfFan 像集 + AZIM_LT_PI_IMP_CARD_GT_1 对应物
（HOL ASFUTBF.hl:182-699，~500 行）。工具链落地后本占位即机械装配。 -/

/-- 接口占位：HOL `Asfutbf.contravening_negative`（ASFUTBF.hl；
`contravening_negative_concl`）。 -/
theorem contraveningNegative (V : Set V3) (hc : Contravening V) :
    Contravening ((fun v => -v) '' V) := by
  sorry

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

/-! NEEDS（2026-09-28 脊柱 lane 定级确认「中等」，三件套）：
①`FLYSPECK_DEVOLUTION`（flyspeck_devol.hl:25）——体积形界 ⟹ 计数形界：对
saturated V，V∩ball(0,r) 中每点的单位球互斥且含于 ball(0,r+1)，故
`CARD(V∩ball(0,r)) * vol(ball 1) ≤ vol(⋃ unit balls ∩ ball(0,r+1))`，再由体积界
在 r+1 处折算（c ↦ π/√18·7 + |c|·4）；Lean 侧需测度论侧条件
（MEASURE_SUBSET/MEASURABLE_UNIONS + FINITE_PACK_LEMMA 的有限性——
PackingAuto19 的 `Finite` 套件或 PA2 `Upfzbzm` 支撑引理群）。
②`CPNKNXN`（flyspeck_devol.hl:135）——packing ⟹ saturated 超集（Zorn：
ZL_SUBSETS_UNIONS_NONEMPTY，链并的 packing 论证），Mathlib Zorn 可移植。
③`KIUMVTC`（Pack2）——V ⊆ V' ⟹ CARD(V∩ball) ≤ CARD(V'∩ball)（机械：
Set.inter_subset_inter + ncard mono）。HOL 证明体 the_main_statement.hl:84-110
为 ~25 行装配（ENOUGH_TO_SHOW + REAL_ARITH）。 -/

/-- 接口占位：HOL `kc_imp_the_kc`（the_main_statement.hl:82）——
Pack_defs `kepler_conjecture`（体积形）⟹ 密度计数形。 -/
theorem kcImpTheKc (hkc : keplerConjecture) : TheKeplerConjecture := by
  sorry

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

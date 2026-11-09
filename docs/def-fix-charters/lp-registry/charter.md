# DEF-FIX 章程 — `lp-registry`：`LpIneqs` 分量从空量化恒真 → 127 条真命题

> 状态：**编排者已核，待闸**。日期 2026-11-06。车道 `lp-registry`。
> 依据：用户 2026-11-06 裁决「Lp 就按照你的建议来吧」= 先修缺陷 #1（`idsLpIneqs := []`）
> 与 #2（`else True` 回落）；`lp-idfix`（只修 #3 索引盲）另行排在后面。

## 1. 为什么走 DEF-FIX 通道

本次改动**触碰定义**，不是删 `sorry`：

- `def CertifiedIneqHolds (_id : String) : Prop := certifiedIneqHolds_pilot _id`
  → `def CertifiedIneqHolds (id : String) : Prop := lpIneqProp id`
- `def idsLpIneqs : List String := []` → `def idsLpIneqs : List String := lpIneqsIds`

签名（`String → Prop` / `List String`）一字未动，**只有函数体/取值变**。
按 `AGENTS.md` §2「定义改动只走 DEF-FIX 通道」，本文件即章程。

## 2. 改动内容（§2.1 为逐字 diff 围栏，闸按它做多重集包含）

### 2.1 逐字 diff（`lean/Kepler/Assembly.lean`，由 `git diff HEAD` 直接生成）

```diff
@@ -20,6 +20,9 @@
   展开为 §2a' 六分量具名骨架件的显式装配（15 枚：14 开放骨架 + 1 真装配）；
   `CertifiedIneqHolds` 语义按 §2a 处方落诚实最小形（试点查表，键
   `"3397113841"` 端到端闭合 = 会师点）。
+  2026-11-06 lp-registry 车道：LP 分量真化——`idsLpIneqs := lpIneqsIds`
+  （127 条），`CertifiedIneqHolds := lpIneqProp`（`LpIneqProps.lean`
+  机械转写的 127 条字面命题）；`LpIneqs` 从空量化恒真变为 127 条真债。
 -/
 import Kepler.Statement
 import Kepler.NliBanks16
@@ -57,6 +60,9 @@ import Kepler.Assembly.GoodListAll
 -- `CertifiedIneqHolds` 查表的试点链（G4 证书 C3397113841 + 粘合 + 语义命题）。
 import Kepler.Assembly.IdLists
 import Kepler.Assembly.IneqPilot
+-- lp-registry 车道（2026-11-06）：HOL `lp_ineqs` 127 条注册表（生成件），
+-- `CertifiedIneqHolds` / `idsLpIneqs` 在此接线。
+import Kepler.Assembly.LpIneqProps
 -- nli A1 车道（2026-10-22）：rest 20 `FWGKMBZ` 的在库 G4 证书（605 分片 + Base，
 -- 205,418 叶；导出 `CFWGKMBZ_pos`）。证书模块自包含，不依赖 Assembly。
 import Kepler.Interval.Cases.CFWGKMBZ
@@ -256,28 +262,36 @@ HOL `the_nonlinear_inequalities`（the_main_statement.hl:55-59）是六件**生
 
 已批准折算（docs/phase6-spine.md §3 决策点）：每分量 = ID 清单（数据）+ 量化命题；
 折算合理性须登记 `docs/statement-fidelity.md`（P6-B）。
-**占位差距**：六个 ID 清单暂为空、`CertifiedIneqHolds` 语义暂为 `True` 占位——
-二者均由 Phase 4（G4 内核证书 + 155 定义闭包粘合，P6-E）填实；
-清单填入前本接口的量化部分无内容。仓库中无现成注册表形态
+**占位差距（2026-11-06 lp-registry 车道更新）**：LP 分量已真化——
+`idsLpIneqs = IdLists.lpIneqsIds`（127 条，rfl 钉子 `lpIneqsIds_length`），
+`CertifiedIneqHolds = lpIneqProp`（`LpIneqProps.lean` 的 127 条字面命题
+注册表）。其余五个分量的 ID 清单/语义仍是既有占位债务：
+`certLookupDomain` 内非 LP 键回落 `True`（本轮不动，见
+`lp-registry` DELIVERY 的健全性说明）。仓库中无现成注册表形态
 （`get_main_nonlinear` 仅见于 HOL 脚本与 LocalAuto16/19 的 NEEDS 注释），故按批准新造。 -/
 
-/-- 单条证书不等式成立的语义。**T1 骨架波（2026-10-08）按上方处方落地的诚实
-最小形**：查表体 = `certifiedIneqHolds_pilot`（IneqPilot.lean 的量产样板表）——
-表内键按 `id` 展开为 ineq.hl 字面量化不等式命题（`!y1..y6. box ==> ineq` 形；
-现含唯一端到端键 `"3397113841"`：G4 证书 `C3397113841_pos`（1504 叶）+ 粘合
-`C3397113841_evalReal` + 语义命题 `ineqProp_3397113841`，`#print axioms` =
-标准三公理，IneqPilot.lean:96-97 实证），表外键回落 `True`（原占位语义）。
-回落分支不可达性由量产波「ID 清单 = 查表定义域」不变量钉死（IdLists.lean
-`certLookupDomain`；其 :699 else-True 静默退化警告在案：表未覆盖定义域前，
-§2a' 的注册表侧骨架**不得**经回落分支平凡闭合）。签名（`String → Prop`，
-2026-09-19 冻结）一字未动，仅按处方替换函数体。 -/
-def CertifiedIneqHolds (_id : String) : Prop := certifiedIneqHolds_pilot _id
+/-- 单条证书不等式成立的语义（2026-11-06 lp-registry 车道接线）。
+
+**LP 分量已真化**：`lpIneqProp`（`Kepler.Assembly.LpIneqProps`，**生成件**）
+把 HOL `lp_ineqs` 的 127 条字面不等式（`!y1..y6. box ==> ineq` 形）按 id
+注册为 Lean 命题：LP 清单内 id 查表命中即得该命题（真实但未证 = 127 条债务）；
+LP 清单外的历史试点键 `"3397113841"`（HOL 里是 `skip` 记录，不在 lp_ineqs）
+仍映射到已证的 `ineqProp_3397113841`；六分量定义域 `certLookupDomain` 内其余
+id 仍为既有占位 `True`（五个兄弟分量的债务，本轮不动）；域外为 `False`。
+
+**健全性顺序**（先填表、再让清单 = 定义域）：127 条真命题先入表，
+`idsLpIneqs` 才等于定义域；「清单内 id 必命中查表」由
+`lpIneqs_domain_covered` 真证（`#print axioms` = 标准三公理），故 LP 域的
+`False` 回落是不可达死代码。签名（`String → Prop`）未动。 -/
+def CertifiedIneqHolds (id : String) : Prop := lpIneqProp id
 
 /-- 注册表量化：清单中每条 ID 对应的不等式成立。 -/
 def AllCertified (ids : List String) : Prop := ∀ id ∈ ids, CertifiedIneqHolds id
 
-/-- PLACEHOLDER(G4)：HOL `lp_ineqs` 分量的 ID 清单（the_main_statement.hl:29-45）。 -/
-def idsLpIneqs : List String := []
+/-- HOL `lp_ineqs` 分量的 ID 清单（the_main_statement.hl:29-45）：127 条。
+逐字等于 `IdLists.lpIneqsIds`（其 `lpIneqsIds_length = 127` 是 rfl 钉子；
+`LpIneqProps.lpIneqIds_eq` 用 rfl 钉死「注册表 id 列 = 本清单」）。 -/
+def idsLpIneqs : List String := lpIneqsIds
 
 /-- HOL `lp_ineqs`（the_main_statement.hl:29-45）的注册表折算形态。
 在 HOL 中它同时是 `the_nonlinear_inequalities` 的第四合取项和
@@ -1901,22 +1915,35 @@ theorem nliMainNonlinearTerminalV11Ids : AllCertified mainNonlinearTerminalV11Id
 
 /-! #### 分量 4/6 `LpIneqs`（127 条；the_main_statement.hl:29-45） -/
 
-/-- 中层骨架 4：HOL `lp_ineqs` 接口分量的当前形态 `AllCertified idsLpIneqs`
-（`idsLpIneqs = []`，§2a 占位清单）。资产状态：**占位空洞**——清单为空使
-本件当前空洞地成立；真化 = 把 IdLists.lean `lpIneqsIds`（127 条）代入
-`idsLpIneqs` 后由骨架 4' 承接。
-退化防线：**不得**利用 `idsLpIneqs = []` 或查表回落分支平凡闭合（两者皆是
-IdLists.lean:699 else-True 静默退化的变体；接线落地方可闭合）。
+/-- 中层骨架 4：HOL `lp_ineqs` 接口分量的注册表形态 `AllCertified idsLpIneqs`
+（`idsLpIneqs = lpIneqsIds`，127 条；`LpIneqProps.lpIneqTable` 把每条 id
+展开为 ineq.hl 字面命题）。资产状态：**真实但未证**——127 条全部是 G4
+证书级债务（既不是空量化，也不是 `else True` 回落）。
+退化防线：**不得**经任何回落分支平凡闭合；本占位只能由 127 条逐条证书
+消解。`False` 回落对 LP 域不可达由 `lpIneqs_domain_covered` 真证钉死。
+-- NEEDS: 127 条逐条 G4 证书（`nliLpIneqsIds` 仍是同一债务的清单侧形态）。 -/
 theorem nliLpIneqs : LpIneqs := sorry
 
+/-- **LP 定义域覆盖（`certLookupDomain` 的 LP 片段）**：`idsLpIneqs` 的每个 id
+都命中查表 ⇒ `CertifiedIneqHolds` 的 `False` 回落对本分量不可达。
+真证（依赖 `LpIneqProps.lpIneqLookup_isSome_of_mem_lpIneqsIds`，
+`#print axioms` = 标准三公理）。 -/
+theorem lpIneqs_domain_covered {id : String} (h : id ∈ idsLpIneqs) :
+    (lpIneqLookup id).isSome :=
+  lpIneqLookup_isSome_of_mem_lpIneqsIds h
+
+/-- 覆盖的语义形态：LP 清单上的 `CertifiedIneqHolds` 就是注册表里那条字面命题。 -/
+theorem certifiedIneqHolds_eq_table_of_mem {id : String} (h : id ∈ idsLpIneqs) :
+    ∃ q ∈ lpIneqTable, q.1 = id ∧ CertifiedIneqHolds id = q.2 :=
+  lpIneqProp_eq_of_mem h
+
 /-- 中层骨架 4'：lp_ineqs 注册表侧（Lp/Tablelp/Lp_aux 标签 + `"6170936724"`
 特例、剔除 deprecated_quads，127 条，IdLists.lean:484-611）。
 资产状态：混合——在库 G4 证书 `3253650737` / `2570626711` / `5490182221`；
-试点案 `3397113841`（IneqPilot，端到端闭合、已入 §2a 查表）的**分量归属
-待对账**（IneqPilot 注记其 HOL 标签 Xconvert/Lp_aux/Tablelp 属 lp_ineqs，
-但该 10 位键不在生成清单 `lpIneqsIds` 中——gen_idlists.py 口径 vs 试点
-注记的分歧）。
+试点案 `3397113841` 的**分量归属已对账（2026-11-06 lp-registry 车道）**：
+该记录在 `ineq.hl:2055` 是 `skip { … }`（不是 `add`），故不进
+`!Ineq.ineqs`、也就不进 `lp_ineqs`——其 Lp_aux/Tablelp 标签因此不生效；
+`lpIneqProp` 只把它保留为 LP 清单外的历史试点键（`certifiedIneqHoldsPilotCase`）。
 -- NEEDS: 127 条逐条接线 + 证书；3397113841 归属对账；清单内多数条目归
 92 prep 家族重做口径。 -/
 theorem nliLpIneqsIds : AllCertified lpIneqsIds := sorry
@@ -1958,8 +1985,11 @@ theorem nliKcblrqcIneqDefIds : AllCertified kcblrqcIneqDefIds := sorry
 非空洞闭合——接口语义自此含一个由 G4 内核证书（`C3397113841_pos`，1504 叶
 bb_arb）+ 粘合引理支撑的真条目（`#print axioms` = 标准三公理）。后续
 自下而上波逐键扩表后，本形即量产样板。 -/
-theorem certifiedIneqHoldsPilotCase : CertifiedIneqHolds "3397113841" :=
-  certifiedIneqHolds_pilot_holds "3397113841"
+theorem certifiedIneqHoldsPilotCase : CertifiedIneqHolds "3397113841" := by
+  unfold CertifiedIneqHolds lpIneqProp
+  rw [if_neg (by decide : ¬ ("3397113841" ∈ lpIneqIds))]
+  rw [if_pos rfl]
+  exact ineq_3397113841
 
 /-- **接口 2**：HOL `linear_programming_results`（the_kepler_conjecture.hl:21-26）
 逐句镜像，archive 清单参数化（HOL 内嵌 `tame_archive_lists`；参数化是为了与
@@ -7074,7 +7104,8 @@ theorem linearProgrammingResultsOf (hnl : TheNonlinearInequalities)
 sorryAx 仅自 14 枚开放骨架节点流入（1a-1d 切片组、2/2'、3/3'、4/4'、5/5'、
 6/6'），分量 1 本体与 §2a 查表会师点为真推导/真叶。
 债务归属（原冻结注记，继续有效）：Phase 4 / G4 粘合（P6-E）。消除顺序：
-先填六个 ID 清单与 `CertifiedIneqHolds` 语义（语义已按处方落最小形——§2a），
+先填六个 ID 清单与 `CertifiedIneqHolds` 语义——**LP 分量已于 2026-11-06
+完成**（127 条真命题注册表 + 覆盖定理），其余五分量仍待填；
 再逐条闭合证书（自下而上波经 §2a 查表对接）。 -/
 theorem nonlinearInequalities : TheNonlinearInequalities :=
   ⟨nliPackNonlinearNonOx3q1h, nliOx3q1h, nliMainNonlinearTerminalV11, nliLpIneqs,
```

### 2.2 新增文件（不在本围栏内，独立计入 LANE_FILES）

`lean/Kepler/Assembly/LpIneqProps.lean` — 1,714 行，**生成件**
（`emit_lean.py`；再生成命令写在文件头）。含 127 条 `lpIneqStatement_NNN`、
`lpIneqTable`、`lpIneqIds`、`lpIneqLookup`、`lpIneqProp`，以及 5 条真证引理。

## 3. 语义：健全性顺序（这是本次改动的核心论证）

我先前的实现顺序是错的，这里明确记下来：

- 若**先**让 `idsLpIneqs := lpIneqsIds` 而表还是空的，则 `LpIneqs` 变成
  「127 条未命中 → `False`」⇒ **`LpIneqs` 是假命题** ⇒ 作为锥内 sorry
  `nliLpIneqs : LpIneqs` 的前提，**根定理本身可能为假**。这比原来的
  「空量化恒真」坏得多。
- 正确顺序：**先把 127 条真命题填进表，再让清单等于表定义域**。此时
  `False` 回落分支对 LP 域**不可达**，并由 `lpIneqs_domain_covered` 真证钉死。

`lpIneqProp` 的四路分派（`LpIneqProps.lean:1632`）：

| 条件 | 结果 | 理由 |
|---|---|---|
| `id ∈ lpIneqIds`（127 条 LP 清单） | 查表所得的字面不等式命题；查不到则 `False` | **真化**：真实但未证 |
| `id = "3397113841"` | 已证的 `ineqProp_3397113841` | 保留既有会师点；该记录在 HOL `ineq.hl` 是 `skip` 而非 `add`，本就不属 `lp_ineqs` |
| `id ∈ certLookupDomain`（其余五分量） | `True`（既有占位） | **本轮不动**：动它会把五个兄弟分量的 sorry 骨架变成假命题；那个是 `lp-idfix` 与本表后续波的活 |
| 其余（域外） | `False` | 硬化：表外键不再静默变真 |

### 3a 白名单声明（`DF_NAMES`）

`CertifiedIneqHolds idsLpIneqs certifiedIneqHoldsPilotCase lpIneqs_domain_covered certifiedIneqHolds_eq_table_of_mem`

## 4. 债务账

### 4.2-6 `sorry` 净变化 = **0**

`lean/Kepler/Assembly.lean` 的 `:= sorry` 行数 **62 → 62**，
`declaration uses sorry` **62 → 62**（编排者独立重编实测）。本笔**不闭合任何 sorry**，
只把一条债务从"假真空"改成"真未证"。

## 5. HOL 锚点与转写保真（可复核）

- **id 清单**：`the_main_statement.hl:29-45` 的 `lp_ineqs`，过滤
  `tag ∈ {Lp, Tablelp, Lp_aux _} ∨ idv = "6170936724"`，剔除 `Tame_lemmas.deprecated_quads`
  ⇒ 127 条，与 `IdLists.lpIneqsIds`（`lpIneqsIds_length = 127` rfl 钉子）逐字相等。
- **命题正文**：`nonlinear/ineq.hl` 与 `nonlinear/main_estimate_ineq.hl` 的 `ineq` 字面项。
  缺的 4 个 HOL 定义逐字补齐：`delta_x1`（`nonlin_def.hl:418-421`）、
  `delta_234_x`（`sphere.hl:848-850`）、`delta_4_squared_x`/`y`（`sphere.hl:835-836`、`838`）。
- **机器对账**：正文 AST 与独立解析器 `pipeline/interval/out/ineqs_ast.json`
  **99/99 相同**、bounds 36 条相同；Lean 文本回读 **127/127 与源 AST 相同**
  （逐条 sha256 在 `artifacts/roundtrip_hashes.json`）。
- **编排者独立抽查 3 条**（含 1 条 g4e 未覆盖的）：
  - `5490182221` → `dih_y < 1.893`，盒 `dart_std3` = [2.0, 2.52]^6 — 与 `ineq.hl:2709` 逐字一致
  - `5735387903` → `dih_y > 0.852`，同盒 — 与 `ineq.hl:2710` 逐字一致
  - `6184614449`（g4e 无覆盖）→ `delta4_y < 0`，盒 `(&2,y1,&2*h0)`…`(#3.3,y4,&4*h0)`
    — 与 `main_estimate_ineq.hl:1068-1081` 逐字一致

## 6. 验收实测（编排者跑，非车道自述）

| 项 | 结果 |
|---|---|
| `LpIneqProps.lean` 独立 `-o` 编译 | **RC=0 / 0 error / 5.5 s** |
| 5 条引理 `#print axioms` | **全 = `[propext, Classical.choice, Quot.sound]`** |
| `Assembly.lean` 独立 `-o` 编译 | **RC=0 / 0 error / 62 sorry / 35.8 s** |
| 根面 `#print axioms the_kepler_conjecture_e2e` | **591 = 587 native + 标准三 + `sorryAx`，逐项不变** |
| 新增公理名 | **0**（591 条里 587 条仍是 `native_decide.ax_*`） |

## 7. 残余风险 / UNRESOLVED

1. **28 条（5 `main_estimate` + 23 程序化 iqd/mk_iqd）不在 g4e JSON 覆盖内**，
   只有回读检查 + 模板机械展开 + 上述 1 条人工抽查。要更强保证需为这 28 条单独造解析器对账。
2. 127 条命题**全部未证**。本笔之后 `LpIneqs` 是**真债**，不是成就。
3. `certLookupDomain` 内非 LP 键仍是 `True`（五个兄弟分量）。

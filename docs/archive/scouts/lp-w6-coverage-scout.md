# W6_SCOUT — LP 覆盖桥精确侦察 + 接口骨架

> 落库版说明（2026-10-23）：正本与可编译骨架在
> `~/c17_backup/lane_snapshots/lpw6/`（`LPCoverage.lean` 267 行、build 日志、
> 公理探针、MD5SUMS）。骨架**未入仓**：它 import `Kepler.Assembly`，
> 最终接线前需先把共享类型下沉以拆环；且顶层债点保留 1 处 sorry，
> 入仓会新增一条默认闭包外债。下一波从快照取用。


日期：2026-10-23。工作区：`/tmp/p4p12`（main HEAD `4053ef5a` 的 APFS 克隆，
`.lake` 暖）。本车道：侦察 + 接口骨架 + 能证的前置引理；**未做** git /
auto_gate / commit，**未改** `Assembly.lean`/`LPAll.lean`/`LPLeaf*`/
`LPSchema`/`LPCert`/`LPIds`。

---

## 0. 结论速览

1. **W6 可以在本机继续**，但它不是「补几条组合引理」的规模：
   - 覆盖组合层（每图终端树 ⟹ 每记录 id ⟹ 全局 42,889 + 189 登记表）
     **已经真证**（`LPCoverage.lean` §1–§3，10 条引理 + 2 条真归约/装配）。
   - 真正的缺口是 **终端 LP 语义**：HOL `prove_flyspeck_lp.hl`
     （1,066 行）+ `lp_ineqs_proofs-compiled.hl`（3,162 行）+
     `lp_main_estimate-compiled.hl`（2,179 行）+
     `lp_ineqs_proofs2-compiled.hl`（1,396 行）等约 **8,700+ 行 HOL
     证明机器**的 Lean 移植；这不是 5 小时量级，是独立多波项目。
2. **数据边界干净**：覆盖桥只需要 `lpTerminalBoundAll`（42,889）与
   `lpAllInfeas`（189）两条全局总量定理，**不需要**逐叶证明；43k 叶闭合
   与 W6 可并行。真正的接口风险是 `LpTerminalCertified` 的 id 不敏感
   （`LPCert.lean:61`，文档 :52-59 在案）——语义桥必须 id 敏感，叶证明
   必须走各自产物模块（`LpTerminalPin` 钉定形已在 `LPSchema` §2 就位，
   但 `LPAll` 仍用冻结的 id 不敏感谓词）。
3. **本波交付**：`LPCoverage.lean` 267 行，`lake build` EXIT=0；1 处
   开放占位（顶层债点，带 `-- NEEDS`），10 条真证明引理，2 条真归约
   定理；纯组合引理 `#print axioms` = `[propext, Quot.sound]`。
4. **第一波建议**：W6-A 证书树数据（light shape + archive 对齐，机械）、
   W6-B `lp_fan`/`lp_cond`/`lp_tau` 定义 + `contravening_lp_fan`
   （最小语义核）、W6-C `ye_list`/`yn_list` + split 算术引理（纯实证明）。
   **不要**从 `prove_flyspeck_lp_step1`/`compute_all` 起手——它们依赖
   127 族不等式数据库与 LP 数据对齐，是第 3–4 波。

---

## (a) 顶层签名对照

### a.1 现有债点（`lean/Kepler/Assembly.lean:6224`，未改动）

```lean
theorem lpArchiveCertificatesDebt (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
    ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V := by
  sorry
```

消费链（Assembly 内）：`:6234 lpArchiveCertificates := lpArchiveCertificatesDebt`；
`:6271 linearProgrammingResults := linearProgrammingResultsOf hnl (lpArchiveCertificates
hnl.2.2.2.1 (nonlinear_imp_lp_main_estimate_p16 hnl.2.2.1))`。

### a.2 `LPCoverage.lean` 的逐字同陈述副本

```lean
-- namespace Kepler.Text.LP.Coverage（不是 Kepler.Assembly）
theorem lpArchiveCertificatesDebt (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
    ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V := by
  sorry -- NEEDS: ...
```

`#check` 对照（`signature_axioms_probe.log`）确认两者类型**逐字相同**，仅
命名空间不同；`LPCoverage` 不被任何既有模块 import，不进默认闭包/根。
显式差异仅有一处：`Assembly` 的行内注记要求“不弱化陈述”，本副本保持
全强形；§3 的 `lpArchiveCertificatesDebt_of_coverage` 是**带显式接口前提**
的归约定理，结论与上式逐字相同，不冒充无前提债务闭合。

---

## (b) 子引理表（HOL 位置 / 自然语言 / Lean 草案 / 可复用 / 缺口）

图例：**P**=已真证（本波），**E**=既有 Lean 件，**N**=需新定义/移植。

| # | HOL 位置 | 自然语言陈述 | Lean 目标陈述草案 | 可复用件 | 缺口类型 / 状态 |
|---|---|---|---|---|---|
| S0 | `text_formalization/tame/linear_programming_results.hl:24-29` (`tame_result_lemma`) | `(∃L∈archive. iso V L) → ¬contravening V` 等价于 `∀L∈archive. iso V L → contravening V → False`（纯量词交换） | `linearProgrammingResultsOn_iff_perList : LinearProgrammingResultsOn a ↔ ∀ L∈a, ∀ V hfan, LpIneqs → lp_main_estimate → FanHypermapIsoList V hfan L → ¬Contravening V` | `LinearProgrammingResultsOn`（Assembly:1301） | **P**（`LPCoverage.lean`）`axioms=[propext, Classical.choice, Quot.sound]` |
| S1 | `linear_programming_results.hl:40-71` (`linear_programming_results_th`) | 逐证书 `tame_linear_result V L` 对 archive 全称化，再用 `tame_result_lemma` 装配成 `linear_programming_results` | `linearProgrammingResults_of_debt : (∀V hfan L, L∈tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V) → LinearProgrammingResults` | `LinearProgrammingResults`/`LinearProgrammingResultsOn` | **P**（真装配，标准三）；逐证书生产见 S3 |
| S2 | `formal_lp/hypermap/verify_all.hl:40-84,116-120` (`verify_file`/`verify_all`) | 读 `{easy,hard}_*.dat` 的 `lp_certificate` 列表，逐证书调 `verify_lp_certificate`，返回 `(id, theorem)` 表 | 数据层：`List LpGraphCert` + `id = lpHypermapId hypermapString`；无证书数据则无法启动 | `LpGraphCert`（LPSchema:288）、`lpHypermapId`/`lpRecordId`、`parse_lpcert.py`（在库读器） | **N/数据**（W6-A）：生成 light shape + archive 对齐；`hdata`/`hcov` 的 `decide` 证明 |
| S3 | `formal_lp/hypermap/main/prove_flyspeck_lp.hl:1042-1063` (`verify_lp_certificate`) | 由 `hypermap_string` 得 `L`；`compute_all` 得不等式集；`contravening_conditions` 得 `lp_cond`/`lp_tau`；`verify_lp_case` 验树；`DISCH contravening` + `EXPAND L/g/h` 得 `tame_linear_result V L` | `hsem : ... → LpGraphTreeCertified g → ¬Contravening V`（归约中的显式语义前提） | 本节以下 S4–S10 全部 | **N/语义**（最大缺口） |
| S4 | `lp_certificate.hl:39-43` (`count_terminals`) | 证书树终端叶计数 | `LpCaseTree.countTerminals`（LPSchema:268） | **E** `countTerminals`/`dfsTerminals`/`flags` | **P**：`dfsTerminals_map_fst`（`ti` 恰为 `0..count-1`）、`dfsTerminals_length`、`fst_nodup`、`fst_lt_of_mem`、`exists_mem_of_lt`、`recordIdAt_dfs` |
| S5 | `prove_flyspeck_lp.hl:287-350` (`prove_flyspeck_lp_step1`) | 终端支：把 `constraints` 中每个 `(family, indices, coeff)` 经 `get_ineqs` 取实例、`transform_le_ineq` 乘系数、求和；非 infeasible 支再加 `lnsum_ineq`；`target_variables`/`variable_bounds` 消元；`FINAL_INEQ` 把 `lin_f [] <= -n` 闭合为矛盾/上界 | 需先有 HOL 家族语义 `getIneqs`/`transformLeIneq`/`sumStep` 与 `LPCM` 数据对齐定理 | `checkDualCMTF`/`LPCM`（`Kepler.LP.ColMajor`）、`LPFarkas` | **N/定义对齐 + 移植**：HOL 是“族名+下标+整数系数”的线性组合；Lean 产物是 `socert` 的列主序精确对偶。**两者等价性没有在库定理** |
| S6 | `prove_flyspeck_lp.hl:483-523` | 六个纯实数 split 事实：quad 5 析取、pent 11 析取、hex 7 析取、`2.18/2.36/2.25` 二择一 | 先在 Lean 定义 `ynList`/`yeList`，再证 `split4/5/6/218/236/225`（`linarith`/`nlinarith`） | `tauVEF_p2`、Fan 几何量、Real 库 | **N/移植（纯证明）**：无 `ye_list`/`yn_list`；W6-C |
| S7 | `prove_flyspeck_lp.hl:865-1040` (`verify_lp_case` + 10 个 `verify_*`) | 递归验证证书树：终端走 S5；`add_big`/`mid`/`high` 加额外不等式；`218/236/edge` 用实数全序二分；`tri/quad/pent/hex` 用几何 split 生成不等式并合并 2/5/11/7 个子支 | Lean 侧需 `LpCaseTree → (terminal semantics → False) → False` 的组合子，参数化每个 split 的几何生成引理 | `LpCaseTree` 树形、S6 split 事实 | **N/移植**：组合骨架可仿 `LPSchema` 归纳；每个 split 的 `gen_*_ineqs` 依赖 S5/S8 |
| S8 | `prove_flyspeck_lp.hl:611-618` (`contravening_conditions`) + `lp_ineqs_proofs-compiled.hl:394-411` (`contravening_lp_cond`/`_alt`) + `lp_main_estimate-compiled.hl:1682-1706` (`contravening_lp_tau`) | `Contravening V` + `iso` + `good_list` ⇒ `∃g h. lp_cond (L,g,h) (V,ESTD V)`；`Contravening V` + `lp_main_estimate` ⇒ `lp_tau (V,ESTD V)` | `contraveningHasLpCond : Contravening V → FanHypermapIsoList V hfan L → ∃ g h, LpCond L g h V hfan`；`contraveningHasLpTau : Contravening V → lp_main_estimate → LpTau V` | `contraveningFan`（Assembly:1548）、`hypIso_p37`（LocalAuto37:488）、`GoodList`/`listOfDarts`（GoodListDefs）、`tauVEF_p2`（LocalAuto2:369）、`CRTTXAT` 帽石（TameLp） | **N/定义 + 移植**；`GoodListNodes` 当前是 `True` 占位（Assembly:1526-1528），必须先真化；`hyp_iso` 可用 `hypIso_p37` 桥接 |
| S9 | `lp_ineqs_proofs-compiled.hl:9-23` (`lp_fan`/`lp_cond`/`lp_tau` 定义) | `lp_fan` = FAN + fully_surrounded + 非边点距 ≥ 2.52 + ball_annulus + packing；`lp_cond` = lp_fan + good_list + good_list_nodes + hyp_iso + `BIJ h elements V` + `g d = (h (FST d), h (SND d))` + 元素/顶点对应；`lp_tau` = 每个面 `tauVEF ≥ 0` | 逐字定义到 Lean（`LpFan`/`LpCond`/`LpTau`），并把 `ESTD`/`ballAnnulus`/`Packing` 对上 | `FAN`、`Packing`、`ballAnnulus`、`surroundedNode`、`faceSet`、`tauVEF_p2` | **N/定义对齐**；`fully_surrounded`/`elements_of_list`/`hyp_iso` 需逐一落 |
| S10 | `prove_flyspeck_lp.hl:855-863` (`compute_hypermap`) + `725-853` (`split_lp_conditions`/`get_tau_split_th`) + `prove_lp.hl:263-330` (`get_ineqs`) | 从 `(L,g,h)` 的 fan 数据生成/检索每个终端的不等式实例；split 时更新 `L`/`E` 并算新 `lp_cond`/`lp_tau` | Lean 需 127 族不等式数据库的语义层 + `getIneqs`/`splitLpConditions`/`getTauSplit` | 大量 LocalAuto 不等式件（逐族，不统一）；无统一注册表 | **N/最大数据+语义缺口**；`LpIneqs` 现在是空清单占位（Assembly:249-254），不可消费 |
| S11 | `linear_programming_results.hl:19-22` (`tame_linear_result`) | `tame_linear_result V L <=> iso ... ==> contravening V ==> F` | `LpGraphTreeCertified g → FanHypermapIsoList V hfan L → ¬Contravening V`（即 S3 的 `hsem`） | `LpGraphTreeCertified`（本波：注册表覆盖） | **N/语义**；本波只证到“注册表覆盖 ⟹ 每树认证”，未证到 `¬Contravening` |

### b.1 组合层已真证的引理（本波）

| Lean 引理 | 陈述 | axioms |
|---|---|---|
| `dfsTerminals_map_fst` | `t.dfsTerminals.map Prod.fst = List.range t.countTerminals` | `[propext, Quot.sound]` |
| `dfsTerminals_length` | `t.dfsTerminals.length = t.countTerminals` | 标准三/二 |
| `dfsTerminals_fst_nodup` | `(t.dfsTerminals.map Prod.fst).Nodup` | 标准 |
| `fst_lt_of_mem` | `p ∈ t.dfsTerminals → p.1 < t.countTerminals` | 标准 |
| `exists_mem_of_lt` | `i < t.countTerminals → ∃ p ∈ t.dfsTerminals, p.1 = i` | 标准 |
| `recordIdAt_dfs` | `p ∈ t.dfsTerminals → t.recordIdAt gid p.1 = some (lpRecordId gid p.1)` | 标准 |
| `lpTreeTerminalCertified_of_coverage` | `LpTreeTerminalCovered gid t → LpTreeTerminalCertified gid t`（消费 `lpAllInfeas`/`lpTerminalBoundAll`） | 含 `sorryAx`（叶未闭合的 deferred-compute 传递） |
| `lpGraphTreeCertified_of_coverage` | 每图版本 | 同上 |
| `mem_lpTerminalBoundIds_of_segments` | root/easy/hard 任一段成员 → `lpTerminalBoundIds` | 标准 |
| `mem_lpTerminalIds` | infeas/root/easy/hard 任一段成员 → `lpTerminalIds` | 标准 |

`lpTreeTerminalCertified_of_coverage` 的 `sorryAx` 来自既有 42,889 枚未闭合
叶（`lpTerminalBoundAll`），**不是本文件新增**；本文件只有 1 处显式占位
（§0 顶层债点，带 `-- NEEDS`）。

---

## (c) 最小可行攻击顺序（第一波 1–3 件）

### W6-0（本波已完成，无需再派）

- DFS 终端枚举 = `0..count-1`（无重、全覆盖、`recordIdAt` 对齐）；
- 注册表覆盖 ⟹ 每树认证（消费两条全局总量）；
- `tame_result_lemma` 镜像 + `LinearProgrammingResults` 装配；
- 顶层债点逐字副本 + 显式接口归约（`hdata`/`hcov`/`hsem`）。

### W6-A（第一优先，机械数据）

**内容**：从 `reference/flyspeck/formal_lp/glpk/binary/{easy,hard}_*.dat`
（39 文件，404 MB，在库）生成：

1. 每图 light `LpCaseTree`（split 型 + splitFace + 每终端 `precision`/
   `infeasible` 旗标）；**不**生成 constraints/target/variableBounds
   （覆盖桥不需要，语义桥第 3 波才需要）。
2. `LpGraphCert` 的 `hypermapString` + `rootCase`。
3. archive 对齐：`CertOf : fgraph ℕ → LpGraphCert → Prop` 的生成表
   （图 id / 树 vs `tameArchiveLists` 位置），`hdata`/`hcov` 用 `decide`
   或 `rfl` 闭合。

**为什么先打**：这是 `lpArchiveCertificatesDebt_of_coverage` 唯一的数据前提；
不依赖任何未移植语义，产物小（light 树，估计 1–5 MB Lean 源码），
`decide` 成本可控（19,715 图 × 小树）。

**风险**：`tameArchiveLists` 是 `TriData ++ QuadData ++ PentData ++ HexData`
的具体 `fgraph` 列表；证书 `hypermap_string` 的 `L` 必须与其中一条逐字相等。
需要先用 `parse_lpcert.py --extract` 抽样对账；若不匹配，是数据对齐事件，
不得静默跳过。

### W6-B（第二优先，最小语义核）

**内容**：移植 `lp_fan`/`lp_cond`/`lp_tau` 定义（S9）+ `contravening_lp_fan`
（`contraveningFan` 已给 FAN，只需补 fully_surrounded / 2.52 距离 /
ball_annulus / packing 四件）。**先不要**碰 `contravening_lp_cond_alt`
的 `good_list_nodes` 与 `hyp_iso` 细节，除非先真化 `GoodListNodes`
（现为 `True` 占位）。

**为什么第二**：它是 `contravening_conditions` 的第一合取项，也是
`lp_cond`/`lp_tau` 的载体；`contravening_lp_fan` 在 HOL 里只有 ~10 行，
Lean 侧预计 100–250 行，且大部分几何件在 `ContraFan`/`TameLp` 已有。

**风险**：`lp_fan` 的 `fully_surrounded` 与 `2.52 <= dist` 需要
`Contravening` 的 surrounded 分量 + ESTD 翻译；`2.52` 是十进制常量，
需与 `#2.52` 的近似口径对齐（不能引入浮点）。

### W6-C（第三优先，纯算术）

**内容**：定义 `ynList`/`yeList`（从 `LpCond` 的 `g`/`h` 与 `L` 读取），
移植 `split218/236/225`（`REAL_LE_TOTAL` 即 `le_total`）与
`split4/5/6`（5/11/7 析取，`linarith`/`nlinarith`）。

**为什么第三**：纯实数证明，无数据依赖，可作为 W6-B 的并行 lane；
但只有接到 `verify_lp_case` 才有语义价值。

**规模**：定义 + 证明约 150–300 行；`split5/6` 的析取组合可能需要
`rcases` 大分叉，建议先证 `yeList` 的区间界引理再拆。

### 明确不建议先打

- `prove_flyspeck_lp_step1`（S5）：依赖 127 族不等式数据库 + LP 数据
  对齐；在没有 `getIneqs` 语义层前，只能写成抽象假设，价值低。
- `compute_all`/`get_ineqs`（S10）：最大数据缺口，`LpIneqs` 仍是空清单；
  应与 G4 非线性不等式数据库的收口同步。
- 43k 叶灌装：与本桥正交；W6 只消费两条总量定理。

---

## (d) 现有 Lean 件可直接复用 / 需要新定义

### d.1 可直接复用（在库、已证或接口冻结）

| 件 | 位置 | 用法 |
|---|---|---|
| `LpCaseTree`/`dfsTerminals`/`flags`/`countTerminals`/`recordIdAt` | `LPSchema.lean:187-286` | 树形、`ti` 枚举、id 规范形 |
| `LpGraphCert`/`LpTerminalPin`/`LpTerminalCertifiedPinned` | `LPSchema.lean:288-360` | 每图证书 + 记录级钉定（尚未接 LPAll） |
| `LpTerminalCertified`/`LpTerminalInfeasibleCertified`/`All*` | `LPCert.lean:61-88` | 冻结语义谓词 |
| `LpFarkasCore`/`farkasCheck` | `LPFarkas.lean` | 189 infeas 的内核 checker |
| `checkDualCMTF`/`LPCM` | `Kepler/LP/ColMajor.lean` | 42,889 bound 的内核 checker |
| `lpTerminalBoundAll`/`lpAllInfeas` | `LPAll.lean:553/190` | 全局总量（42,889/189） |
| `lpRootIds`/`lpEasyIds`/`lpHardIds`/`lpInfeasIds` + 长度定理 | `LPIds.lean` | 数据边界与总账 |
| `LpIneqs`/`lp_main_estimate` | `Assembly.lean:254`/`LocalAuto16:185` | 顶层前提（当前不可消费：`idsLpIneqs=[]`） |
| `tameArchiveLists` | `GoodListDefs.lean:82` | archive 数据 |
| `FanHypermapIsoList`/`Contravening`/七投影 | `Assembly.lean:192/92/99-137` | 顶层结论 |
| `contraveningFan` | `Assembly.lean:1548` | `Contravening → FAN` 真证 |
| `hypermapOfFan` | `Fan.lean:1169` | fan 超映射构造 |
| `hypIso_p37` | `LocalAuto37.lean:488` | `hyp_iso` 形状（需与 HOL 逐字核对） |
| `tauVEF_p2` | `LocalAuto2.lean:369` | `lp_tau` 的面 tau |
| `CRTTXAT`/TameLp tau 群 | `TameLp.lean` | `contravening_lp_tau` 的几何输入 |
| `GoodList`/`listOfDarts`/`eList`/`nList`/`fList` | `GoodListDefs.lean:38-77` | `good_list`/`hyp_set` |
| `LPPilot` 的真实树字面量 | `LPPilot.lean:309-666` | 生成器的样板形制 |

### d.2 需要新定义（W6 特有）

| 新件 | 形状 | 依赖 |
|---|---|---|
| `LpFan` | HOL `lp_fan` 逐字 | `FAN`、`fully_surrounded`、`ballAnnulus`、`Packing` |
| `LpCond` | HOL `lp_cond` 逐字，含 `g`/`h` 见证 | `LpFan`、`GoodList`、`GoodListNodes`（真化）、`HypIso`、`elements_of_list` |
| `LpTau` | HOL `lp_tau` 逐字 | `faceSet`、`tauVEF_p2` |
| `ContraveningLpCond` | `Contravening V → FanHypermapIsoList → ∃g h, LpCond` | `contraveningFan` + `hypIso` 桥 |
| `ContraveningLpTau` | `Contravening V → lp_main_estimate → LpTau` | `CRTTXAT`、tau 界 |
| `ynList`/`yeList` | `LpCond` 的 `g`/`h` 派生的节点/边高度 | `L`、`g`、`h` |
| `getIneqs`/`transformLeIneq`/`sumStep` | HOL 族名+下标+系数 → 实数不等式 | 127 族数据库（最大新件） |
| `VerifyLpCase` | 树递归组合子（10 split 型） | S5–S7 |
| `CertOf`/light `LpGraphCert` 数据 | 每图树 shape + archive 对齐 | `parse_lpcert.py` + 生成器 |

### d.3 定义对齐事件（必须先裁决）

1. `GoodListNodes` 当前 `def GoodListNodes (_ : fgraph ℕ) : Prop := True`
   （`Assembly.lean:1526-1528`）。`contravening_lp_cond` 需要真定义；
   在真化前，任何依赖它的 `lp_cond` 证明都是假绿。
2. `LpTerminalCertified` 对 `id` 不敏感（`LPCert.lean:61` 的 `_id`）。
   覆盖桥的 `hsem` 是 id 敏感的；`LPAll` 仍用不敏感谓词。钉定形
   `LpTerminalPin` 已就位但未接入 `LPAll`。这是**语义正确性**问题，
   不是单纯的证明缺口。
3. `LpIneqs` 的 `idsLpIneqs = []`（`Assembly.lean:249`）是空清单占位；
   不得经 `AllCertified []` 平凡闭合 `LpIneqs`（文档在案）。
4. `FanHypermapIsoList` 的 `IsHypermapOfList` 是规格级镜像，尚未有
   `hypermapOfList` 构造（P6-C 未落地）；`Contravening` 语境下
   `dart1_of_fan` 去孤立点的折算需随桥补证。

---

## (e) 与 43k 叶 / 189 infeas 的数据接口边界

### e.1 账本口径

| 量 | 值 | 定义 |
|---|---:|---|
| bound 登记表 | 42,889 | `lpTerminalBoundIds = lpRootIds ++ lpEasyIds ++ lpHardIds`（`LPIds.lean:44515`） |
| infeas 登记表 | 189 | `lpInfeasIds`（`LPIds.lean:213`） |
| master | 43,078 | `lpTerminalIds = lpInfeasIds ++ lpTerminalBoundIds`（`LPIds.lean:44524`） |
| 全局 bound 总量 | 42,889 | `lpTerminalBoundAll : AllLpTerminalCertified lpTerminalBoundIds`（`LPAll.lean:553`） |
| 全局 infeas 总量 | 189 | `lpAllInfeas : AllLpTerminalInfeasibleCertified lpInfeasIds`（`LPAll.lean:190`） |

### e.2 路由规则（本波真证）

```
tree terminal p
  ├─ p.2.infeasible = true  → id = lpRecordId gid p.1 ∈ lpInfeasIds
  │                            → LpTerminalInfeasibleCertified id（lpAllInfeas）
  └─ p.2.infeasible = false → id = lpRecordId gid p.1 ∈ lpTerminalBoundIds
                               → LpTerminalCertified id（lpTerminalBoundAll）
```

- `LpTreeTerminalCovered`/`LpTreeTerminalCertified` 的 `if` 正是这条路由；
- `lpTreeTerminalCertified_of_coverage` 消费两条总量定理，**不消费任何
  单枚叶**；
- 数据生成器必须按 `infeasible` 旗标把 id 发射到正确段；旗标与段不匹配
  = 数据错误，不是证明错误（应停批，不得静默改段）；
- `ti` 的唯一性/完备性由 `dfsTerminals_map_fst` 保证（`0..count-1`）；
- 图 id = `lpHypermapId hypermapString`（首 token 去 `_`），记录 id =
  `lpRecordId graphId ti`；两者与 `gen_lp_skeleton.py` 逐字符同构。

### e.3 本桥**不**需要的

- 不需要 42,889/189 个叶的逐条证明体；
- 不需要 `LpTerminalPin` 的 43k 个实例（覆盖桥只用冻结谓词 + 总量）；
- 不需要重新求解 LP 或重新生成证书数据（W1–W5 的事）。

### e.4 本桥**必须**补的

- `CertOf`/light tree 数据（W6-A）；
- `hsem` 的终端语义（W6-B..，见 b 表 S5–S11）；
- `GoodListNodes` 真化与 `LpTerminalCertified` 的 id 敏感升级（若要让
  `hsem` 的“每记录证书”确实对应图/终端，而不是任意 LP 见证）。

---

## (f) 明确“未做 / 未声称”

1. **未改** `Assembly.lean`（`lpArchiveCertificatesDebt` 原样，:6224）、
   `LPAll.lean`、`LPLeaf*`、`LPSchema`、`LPCert`、`LPIds`。
2. **未填任何叶**、**未生成任何证书数据**、**未重跑 LP**、**未改 43k
   数据面**。
3. **未证明 `hsem`**：`LPCoverage.lean` §3 的归约把缺口显式命名为
   `hdata`/`hcov`/`hsem`，不代表债务已清；`lpArchiveCertificatesDebt`
   在 `LPCoverage` 内仍是 1 处带 `-- NEEDS` 的开放占位。
4. **未声称** LP 已入 e2e；`linearProgrammingResults` 的既有 sorryAx
   不受本波影响。
5. **未引入** `axiom`/`opaque`/`native_decide`；新增行禁词扫描零
   （`admit|native_decide|axiom`），唯一 `sorry` 带 `-- NEEDS`。
6. `lpTreeTerminalCertified_of_coverage` 等依赖 `lpTerminalBoundAll`/
   `lpAllInfeas` 的定理传递依赖既有叶的 `sorryAx`——这是 deferred-compute
   账，不是本文件新增占位；本文件的纯组合引理与
   `linearProgrammingResults_of_debt` 的 axioms 为标准三。
7. **未做** git/auto_gate/commit；工作区只新增
   `lean/Kepler/Text/LP/LPCoverage.lean`（`git status` 实证）。

---

## 附录 A：HOL 链精确位置

```
reference/flyspeck/text_formalization/tame/linear_programming_results.hl
  :12-17  linear_programming_results (definition)
  :19-22  tame_linear_result
  :24-29  tame_result_lemma
  :31-40  eval_tame_linear_result
  :40-71  linear_programming_results_th (verify_all + ALL + MESON)

reference/flyspeck/formal_lp/hypermap/verify_all.hl
  :40-84   verify_file
  :87-99   verify_easy
  :101-114 verify_hard
  :116-120 verify_all

reference/flyspeck/formal_lp/hypermap/main/lp_certificate.hl
  :3-35    schema (constraint_type/terminal_case/split_case/lp_certificate_case/lp_certificate)
  :39-43   count_terminals

reference/flyspeck/formal_lp/hypermap/main/prove_flyspeck_lp.hl
  :287-350 prove_flyspeck_lp_step1
  :483-523 split4/5/6/218/236/225 lemmas
  :611-618 contravening_conditions
  :717-730 split_lp_conditions / get_tau_split_th
  :855-863 compute_hypermap
  :865-903 verify_lp_case dispatch
  :905-1040 verify_add_big/mid/high/218/236/edge/split3/4/5/6
  :1042-1063 verify_lp_certificate

reference/flyspeck/formal_lp/hypermap/ineqs/lp_ineqs_proofs-compiled.hl
  :9-23    lp_fan / lp_cond / lp_tau definitions
  :186-327 lp_cond_lemma
  :229-248 lp_fan_trans1
  :248-326 lp_cond_trans1
  :332-384 lp_cond_trans (list version)
  :385-392 contravening_lp_fan
  :394-402 contravening_lp_cond
  :405-411 contravening_lp_cond_alt

reference/flyspeck/formal_lp/hypermap/ineqs/lp_main_estimate-compiled.hl
  :1682-1706 contravening_lp_tau

reference/flyspeck/formal_lp/more_arith/prove_lp.hl
  :215-262 transform_le_ineq
  :263-330 get_ineqs

reference/flyspeck/formal_lp/glpk/build_certificates.hl
  :341-350 build_certificate
  :356-395 build_and_save_all (easy/hard .dat generation)
```

## 附录 B：HOL 证明机器体量（移植规模下界参考）

| 文件 | 行数 |
|---|---:|
| `prove_flyspeck_lp.hl` | 1,066 |
| `lp_ineqs_proofs-compiled.hl` | 3,162 |
| `lp_ineqs_proofs2-compiled.hl` | 1,396 |
| `lp_main_estimate-compiled.hl` | 2,179 |
| `lp_gen_theory-compiled.hl` | 497 |
| `prove_lp.hl` | 440 |
| `lp_certificate.hl` | 158 |
| **合计（不含验证器外的几何/不等式章）** | **~8,898** |

结论：W6 的“无 sorry 债务闭合”是一个 **5,000–10,000 行 Lean 证明工程**
（含定义对齐与 127 族不等式语义），不是单波可完成；本波已把可机械的
组合层与接口层做完，并把剩余缺口精确命名。

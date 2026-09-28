# Phase 6 装配脊柱 — 设计草案（2026-09-19，待审）

> 目标：把 `Statement.lean` 的 sanctioned sorry 替换为真实证明项，
> 代价是若干条**显式、可枚举、逐个保真审查过**的接口 sorry。
> 落地后 `#print axioms the_kepler_conjecture` 的 sorryAx 清单 = 全项目债务图。

## 1. HOL 原版装配结构（考古：`reference/flyspeck/text_formalization/general/the_kepler_conjecture.hl`）

最终定理一句话：

```
import_tame_classification ∧ linear_programming_results ∧ the_nonlinear_inequalities
  ⟹ the_kepler_conjecture
```

三个前提的定义：

- `import_tame_classification`：`∀g. PlaneGraphs g ∧ tame g ⟹ ∃y ∈ archive. iso_fgraph (fgraph g) y`
- `linear_programming_results`：`∀V. lp_ineqs ∧ lp_main_estimate ∧ (∃L ∈ tame_archive_lists. iso (hypermap_of_fan (V, ESTD V)) (hypermap_of_list L)) ⟹ ¬contravening V`
- `the_nonlinear_inequalities`：993 条非线性不等式的巨型合取（`mk_all_ineq.hl` 生成）

文字侧最终 capstone `kepler_conjecture_with_assumptions`
（`the_main_statement.hl:170`）的 tactic 脚本消费链：

| HOL 件 | 角色 |
|---|---|
| `Oxlzlez.PACKING_CHAPTER_MAIN_CONCLUSION` | packing 章主结论（contravening ⇒ 得分上界） |
| `Fnjlbxs.local_annulus_inequality_scriptL` / `FCDJDOT` | local 章引理 |
| `Jejtvgb.nonlinear_imp_lp_main_estimate` | 非线性 ⇒ LP 主估计（Phase 4→3 桥！） |
| `contravening_tame_planar_hypermap` / `tame_planar_hypermap_restricted` | contravening ⇒ fan ⇒ restricted hypermap |
| `Jcajydu.JCAJYDU` / `Wmlnymd.tame_correspondence_iso` | hypermap 对应与同构桥 |
| `Reduction5.restricted_hypermaps_are_planegraphs_thm` | hypermap → 平面图 |
| `Good_list_archive.good_list_archive` | archive 每张图"好"（逐图 LP+非线性检查的总账） |

## 2. Lean 侧映射现状

| HOL 件 | Lean 状态 |
|---|---|
| `import_tame_classification` | ✅ **已证**（`Kepler.Graphs.tame_classification`，Phase 2 内核闭合；注意 HOL 版允许镜像 iso_fgraph，与我们的 `inIso` 语义对齐——需在保真审中复核） |
| `the_kepler_conjecture` | ✅ 陈述（Statement.lean），sorry 本体 |
| `hypermap_of_fan` / `ESTD` | ✅ fan 章已收官（hypermapOfFan 完整构造） |
| `kepler_conjecture_with_assumptions` | ⬜ 未陈述——Phase 5 的最终 capstone；`PackingConcl.lean`/`LocalConcl.lean` 正在逐条闭合其引理 |
| `the_nonlinear_inequalities` | ⬜ 未陈述——993 条合取；Lean 侧落点 = G4 内核证书定理 + 155 定义闭包粘合 |
| `linear_programming_results`（含 `lp_ineqs`/`lp_main_estimate`） | ⬜ 未陈述——P6-D 原型在探（agent-12） |
| `good_list_archive` | ⬜ 未查——Phase 2 可能已有对应物，待盘 |
| `contravening` | ⬜ 待查（packing 章骨架可能已有定义） |

## 3. 脊柱模块设计（`Kepler/Assembly.lean`，暂定）

1. 三个接口 `def ... : Prop`，逐句镜像 HOL 陈述，每条注释标明 HOL 出处
   （文件:行号）+ 保真折算说明；
2. `theorem assembly : lpResults ∧ nonlinearIneqs ∧ textCapstone → the_kepler_conjecture`
   ——证明照搬 HOL 的 tactic 脚本（脚本不长，见原文 141 行文件）；
3. 三个接口初值全部 sorry；每条 sorry 的消除分别挂到 Phase 3 桥（量产）、
   Phase 4 粘合（G4）、Phase 5 capstone（opencode 流水线）。

### 陈述形态决策点（需要保真审把关）

- `the_nonlinear_inequalities`：HOL 是 993 条字面合取，Lean 照抄会产生
  巨 term。建议改为量化形式 `∀ e ∈ ineqList, IneqHolds e`（清单为数据、
  语义为命题）——折算合理性必须写进 `docs/statement-fidelity.md`。
- `archive` 在 Lean 侧用 Phase 2 现成的 Archive 定义，不要新造。

## 4. 第一批并行子任务（2026-09-19 启动）

| 编号 | 内容 | 负责 | 依赖 |
|---|---|---|---|
| P6-A | 脊柱本体（Assembly.lean 三接口 + assembly 定理） | Kimi | 本文档审定 |
| P6-B | 脊柱陈述逐条保真审查 | Kimi | A 完成后 |
| P6-C | Phase 2 图编码桥原型（Graph/fgraph ↔ hypermap_of_list） | subagent | 无 |
| P6-D | Phase 3 LP 桥单图原型（已启动，agent-12） | subagent | 无 |
| P6-E | Phase 4 桥 = 155 定义闭包粘合 | Kimi（G4 线） | packing 定义（已在 main） |
| P6-F | DEBT.md 增加"主定理可达 sorry"节 | Kimi | A 完成后 |

## 5. 风险

- **（P6-C 实证的结构性问题）fgraph 层允许镜像、hypermap 层不允许**——
  `iso_fgraph` 含 mirror（PlaneGraphIso.lean:257），而文字侧 `Hypermap.Iso`
  保定向。HOL 原版同样如此，且自带桥梁 `ELLLNYZ`（tame/ELLLNYZ.hl:548）：
  `good_list x ∧ good_list y ∧ iso_fgraph x y ⟹ iso (hol x) (hol y) ∨
  iso (opposite (hol x)) (hol y)`——**析取形**，镜像分支在主定理里走
  镜像 fan 绕行（`hypermap_of_fan_neg` + `contravening_negative`，
  the_main_statement.hl:213-249）。脊柱的图桥接口必须是这个析取形，
  不能是单一蕴涵；装配证明需要镜像 fan 绕行段（可作独立接口 sorry）。
  P6-C 单图原型（Tri 最小图，66 dart）已全链内核闭合（/tmp/p6c/Bridge.lean，
  10.3s，公理标准三），通用定义层（listPairs…nList）量产可行
  （~16 CPU·h 优化后，分片并行）。
- 接口陈述若失之毫厘（e.g. `iso` vs `iso_fgraph` 镜像语义），sorry 消除时
  才发现就晚了——P6-B 不可省。
- LP 侧 43,078 终端定理的模块形态：已确认**生产定理未持久化**
  （P6-D：driver.py 验完即删，仅存账本 jsonl）。不挡脊柱（接口层只要 Prop），
  但最终交付前需一次持久化重跑（~324 核时 ≈ 64 核 5 天）。桥接模式已验证：
  `bound_lt ⟹ ¬LpCounterexampleFeasible` 一条通用引理 + 每图一行实例化
  （/tmp/p6d/LpBridgePilot.lean，3.5s，公理标准三）；注意 batch1（<12）与
  batch2a（slack<0）两种 schema 需两个模板，只认列主序 PilotCM 形态。
- 脊柱会引用 packing/local 的 sorry 定理名；骨架期接口名可能漂移——
  脊柱落地后把接口名冻结写进本文档。

## 6. 2026-09-28 现状盘点与 M5′ 路线图（用户拍板）

**里程碑重定义**：下一个 milestone = **M5′ 主定理端到端可达**。骨架即本脊柱——
`Kepler.Assembly.the_kepler_conjecture_from_interfaces : TheKeplerConjecture` 已在
main 编译。目标 = 其 sorryAx 可达债务图完全枚举 + 按杠杆率分段归零。
度量 = 单一数字（主定理可达 sorry 数）+ DAG（`docs/e2e-debt-map.md`，Step 0 产出）。

### 6.1 装配链真伪现状（2026-09-28 逐件核对）

真证明：`assembly`、`textCapstone`（方向 A，2026-09-21，含镜像 fan 绕行分支）、
`linearProgrammingResults`（方向 D 降级为真推导，债务集中于 `lpArchiveCertificates`
单枚）、`goodListArchive`（P6-C，19715 图）、`contraveningFan`（T5，经 ContraFan）、
`tamePlanarHypermapRestricted`、`hypermapIsoTrans`、`oppositeHypermap`、
LA16 `nonlinear_imp_lp_main_estimate_p16`（term 级，LocalAuto16:192）。

脊柱接口 sorry（12，全部带 HOL 出处，Assembly.lean）：`nonlinearInequalities`、
`lpArchiveCertificates`、`mqmsmab`、`jcajydu`、`tameCorrespondenceIso`、`elllnyz`、
`hypermapOfFanNeg`、`isoOppositeEq`、`contraveningNegative`、
`localAnnulusInequalityScriptL`、`fcdjdot`、`kcImpTheKc`。

已达的直接下游债务（经消费链流入主定理；探针刷新时精确枚举）：
- `PACKING_CHAPTER_MAIN_CONCLUSION`（PA25:3438，sorry——textCapstone 直接消费）；
- ContraFan 深几何双核 `LEMMA_3_POINTS_FINAL`/`LEMMA_4_POINTS_FINAL`
  （经 `contraveningFan` → `CKQOWSA`）；
- LA16 `JEJTVGB_p16` 链（经 `nonlinear_imp_lp_main_estimate_p16`）。
（DEBT.md"脊柱公理探针"节"剩三接口"的记载已 stale：textCapstone 已真化、
§2c 11 枚在账，Step 0 一并刷新。）

### 6.2 四步路线（用户批准 2026-09-28）

- **Step 0 instrumentation**（本机，~1–2h，本波收工后立即）：刷新探针 + 写
  spine-debt 枚举工具（从 `the_kepler_conjecture_from_interfaces` 遍历 Lean 环境
  依赖闭包，枚举 value 含 sorryAx 的常量 → 自动生成 `docs/e2e-debt-map.md`，
  DEBT.md 主定理可达节改由工具生成）+ M5′ 写进 STATUS。
- **Step 1 廉价接口波**（sub-agent）：`isoOppositeEq`（置换代数）、
  `contraveningNegative`（V↦−V 对称）、`localAnnulusInequalityScriptL`
  （`hl [vec 0;v] = ‖v‖/2` 定义性恒等 + 求和约定，需一次 HOL 对照确认）、
  `kcImpTheKc`（体积形⟹计数密度形，中等）、`hypermapOfFanNeg`（中等）。
- **Step 2 填证主线转向"脊柱可达优先"**：lane 选择标准从"模块进度"改为
  "是否减少主定理可达 sorry"。优先序：`PACKING_CHAPTER_MAIN_CONCLUSION`
  （最高优先，RDWKARC 链 + TSKAJXY 表面对齐，已可达）→ MQMSMAB 小章
  （ssreflect 17KB，contravening→tame_planar_hypermap）→ tame 文字章
  （64 个 .hl / 4.6MB 最大领土：`jcajydu`/`tameCorrespondenceIso`/`elllnyz`
  + P6-C 遗留 `hypermapOfList` 构造）。假陈述修复波直接服务于此。
  情报源：docs/fill-worker-playbook.md §5（GLTVHUM 五级链 / DUUNHOR
  前提缺失第 11 项，2026-09-28 侦察 lane 入库）。
- **Step 3 数据密集接口**（本机只冻结形态，重型机到位灌数据）：
  `lpArchiveCertificates`（LP 43,078 持久化重跑 ~324 核时 + P6-D 两 schema
  逐行实例化模板已试点）；`nonlinearInequalities`/G4（993 条注册表
  `CertifiedIneqHolds` 语义填实 + 549 重跑；CertTM.lean 线在铺）。

现役 wave 的 lane 不打断；下一波（Step 0 之后）按可达性排。

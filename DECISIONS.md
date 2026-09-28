# DECISIONS.md — 决策日志

> 依据 PLAN.md §2：任何偏离已锁定决策的变更必须先在此记录理由并向人类汇报。
> 新条目追加在顶部（倒序）。

## 2026-09-28 — 硬件迁移：旧服务器报废 + 工人通道换 ZCode sub agent + 重型计算挂起

**事件**：旧生产服务器（128 核 / 503G RAM）于 2026-09-28 确认硬件报废，磁盘不可恢复。
仓库本体零损失（git 全量，origin GitHub，cron 自动 push 保持至 2026-09-26 HEAD
`a5b5aba8`）；**仅存本机外部存储的产物随盘丢失**：

- `cert549_tight.json`（549 全量重演输入，212,798 叶 tight 证书，原在 /tmp）
- LP 43,078 持久化产物 + 账本（~/lprun-persist、~/lprun-logs）
- bb_arb 重跑证书 35 份（~/bb-cert-rerun/certs）
- 549/257 内核构建分片源 + olean（kepler-g4e 工作树，6,321 + 12,553 shard）
- 全量 `.lake` 构建缓存（Phase 2 分片 ~7 天重建成本归零重来）

以上全部可由 git 内工具链重生成；重算在新硬件基线下重估，**不因换机降低验收标准**。

**新硬件基线与算力政策**：Apple M3 Pro（12 核 6P+6E / 36GB / 磁盘余 183GB）。
运行预算上限：kernel decide ≤2 路、native_decide ≤4 路、stage-A ≤8 路、lake `-J 6`。
**重型批处理挂起待强机器**：549 全量重演主体（single+straddle）、LP 43,078 持久化
重跑、145 证书批量重跑、Phase 2 CertShards 全量重建、92 prep 家族重解。
期间主力 = Phase 5 填证 + 轻量 Lean 任务（单文件编译级）+ 小时级单进程 C。

**工人通道变更**：Phase 5 填证与卫星任务的 LLM 工人从 opencode CLI（deepseek 等
外部通道）改为 **ZCode Agent sub agents**。`auto_pipeline.sh` 五道机械闸与
`auto_gate.sh` 验收流程不变（闸与工人实现本就解耦）；HANDOFF 中 opencode 特有
经验（auth.json、external_directory、配额重置等）转为历史记录。

**政策强化（数据丢失教训）**：证书/大产物"仅活在本机外部存储"不再可接受。今后
批次产物落盘即登记 `certificates/README.md`（该表自项目启动起仍为空，即此教训）
并同步第二份外部存储（私有仓/release/协作强机器），哈希清单与本体分离存储的旧
做法补充"本体必须有异机副本"。

**审批状态**：已执行（2026-09-28 用户在会话中确认换机并批准新工作模式：
"只跑非重型计算任务……主要用 sub agents 干活"）。

## 2026-09-25 — native_decide scoped exception 扩展至 `Kepler.Interval.Cases.C549*`（549 加速项目）

> **状态：已批准（2026-09-26，用户拍板"允许 native decide"）。** native_decide
> 允许范围在 2026-08-10 与 2026-09-19 两条（`Kepler.Graphs.Cert*` +
> `Kepler.Assembly.GoodListShard*`）之上，新增 `Kepler.Interval.Cases.C549*`，
> 形态与审计要求按下文执行（50 叶合取 = 1 axiom/shard、逐 shard `#print axioms`
> 台账、sorryAx/Classical.choice 出现即 fail）。量产 native 发射自本批准起开闸。

**变更（拟议）**：在上述两条范围之上，另允许 `native_decide` 出现在
`Kepler.Interval.Cases.C549*`（5490182221 案例的 hull/HullD2/mono 折叠/
ArcBatch 等证书 shard 模块及其汇总定理）。用途：549 全量 212,798 叶证书的
内核验证提速——kernel `decide` 21.4 s/叶 → `native_decide` ~3.5 s/叶
（6.1×，C549HullSpeed 实测）；全量口径 **529 → 109 core·h**（mono 折叠 +
cert 瘦身 + rung-128 + 曲率紧致化组合口径）。

**公理形态（推荐：50 叶/shard 一次 native = 1 axiom/shard）**：

- 推荐发射形态：每 shard 对"50 叶合取"整体做**一次** `native_decide`，
  逐叶定理用 `.1`/`.2` 投影导出——每 shard 恰 **1** 条 scoped axiom
  `<shard>._native.native_decide.ax_1_1 : decide P = true`。
- **已有实测证据**（构建捕获）：`C549Hull200Shard_speed depends on axioms:
  [propext, Quot.sound, C549Hull200Shard_speed._native.native_decide.ax_1_1]`
  （`C549HullSpeed.lean` 文件头 FOLLOW-UP 记录）。
- 形态与 2026-08-10 / 2026-09-19 两批**逐字同形**：本工具链（v4.32.2）的
  公理足迹 = 每定理一条作用域公理（`Lean.Meta.nativeEqTrue`，
  Lean.Meta/Native.lean:31-33）；`#print axioms` = propext + Quot.sound +
  N 条 scoped axiom，无 sorryAx、无 Classical.choice。
- 对照：逐叶 native 形态（同文件叶 2..50）为 49 axiom/50 叶 shard，全量
  ~2×10⁵ 条；合取形态把公理面压 ~50×。合取形态另有共享求值收益（
  `C549Hull200Expr` 单 AST 一次求值 vs 逐叶内核重复展开），十五更外推
  全量可再降至 **~11 core·h**（逼近 M5 ≤ 10 core·h；以全量重演实测为准）。

**影响面（axiom 面数字）**：549 全量 **~10,600 shard → ~10,600 条 scoped
axioms**（1 条/shard；确切 shard 数以全量重演实际发射为准，straddle 修复后
叶数或再降）。相对现存两批总量（2026-08-10 批 ~624 + 2026-09-19 批 23 =
~647 条）约 **16×**。TCB 增量类别不变：Lean 编译器+运行时进 TCB，与
2026-08-10 条同一性质，无新信任基类别。

**审计要求**：

- 每 shard 模块尾部固定 `#print axioms <shard 汇总定理>`（既有惯例，同
  `C549HullSpeed.lean` 与 CertTM 曲率轮 :1683-1688 print 块），并入
  `lean/scripts/AxiomAudit.lean` 台账（逐 shard 行或每族代表行 + 计数台账，
  批准时定案）；
- 审计口径：propext + Quot.sound + N 条 `..._native.native_decide.ax_1_1`；
  出现 sorryAx / Classical.choice / 任何非预期公理即 fail；
- native axiom 计数随轮次入 `docs/549-lane-log.md` 阶段位置节（可度量、
  可对账）。

**结构配套**：发射器默认产 50 叶合取 shard（模块叶数上限沿用管线缺口单的
stage-A shard 化参数 ≤20-50）；`make check` 纪律与双回归（裸路径逐字节）
照旧；549 全量重演（十六更第 1 项）先行，量产 native 发射在本条获批后
开闸。

**风险**：

1. TCB：信任边界 = Lean 编译器+运行时正确性；被决策命题 `decide P = true`
   本身内核可读，撤销后 kernel `decide` 可独立重验任一 shard。
2. 公理面规模：~10,600 条使 `#print axioms` 输出与审计台账线性膨胀
   （~16× 现存）；以 shard 汇总定理为审计单位控制输出体积。
3. 形态漂移：549 全量重演未完成，shard 尺寸/合取结构可能调整；形态微调
   不需新条目，但 axiom 面数字须随轮次在 lane log 更新。
4. 双路径一致性：native 与 kernel decide 消费同一命题，不存在两套判据；
   唯一风险源是编译器误编译——与既有两批同型。

**撤销路径**：发射器单旗标切回 kernel `decide` 重发（正确性零影响，成本
退回 529 core·h 口径），或整体回退本条范围（CI/lint 恢复零命中拦截）。
任何一次审计出现非预期公理 = 即时撤销 + 全量排查，无需另行决议。

**审批状态**：[DRAFT 待批准]。批准后在本节追加批准日期与批准人，并将标题
的 [DRAFT 待批准] 改记为已决。

## 2026-09-19 — P6-C：native_decide scoped exception 扩展至 `Kepler.Assembly.GoodList*`

**变更**：2026-08-10 条"native_decide 只允许出现在 `Kepler.Graphs.Cert*`"
扩展为——另允许出现在 `Kepler.Assembly.GoodListShard*`（archive 逐图
`good_list` 量产分片，23 片覆盖全部 19715 图：Tri 9 / Quad 1253 /
Pent 16080 / Hex 2373）。用途：闭合装配脊柱第 4 个接口占位
`Kepler.Assembly.goodListArchive : AllGoodList tameArchiveLists`
（HOL `Good_list_archive.good_list_archive`）。

**信任基影响**：与 2026-08-10 条完全相同——Lean 编译器+运行时进 TCB。
本工具链（v4.32.2）`native_decide` 的公理足迹为每定理一条作用域公理
`<thm>._native.native_decide.ax_1_1 : decide P = true`
（`Lean.Meta.nativeEqTrue`，Lean.Meta/Native.lean:31-33），与既有
`Kepler.Graphs.Cert*` 分片的足迹逐字一致；`#print axioms goodListArchive`
= propext + Quot.sound + 23 条 native_decide 公理，无 sorryAx、无
Classical.choice。组合器 `Kepler/Assembly/GoodListAll.lean` 为纯内核
（`List.take_append_drop`/`List.all_append` 链），不做任何计算。

**结构配套**：`GoodList`/`listOfDarts`/`tameArchiveLists` 等纯列表机器
从 `Assembly.lean` §1a/§1c 下沉至 `Kepler/Assembly/GoodListDefs.lean`
（本脊柱改为 import 之，对外签名不变），分片因而不必 import 装配脊柱，
接口 sorry 不进入分片公理审计。生成器 `lean/scripts/gen_goodlist_shards.py`
（slice=1000），runner `lean/scripts/run_goodlist_shards.sh`（幂等，
状态文件 `p6c_goodlist.status`）。

## 2026-09-17 — main 分支允许携带 sorry 债务（原"main 零 sorry"纪律放宽）

**变更**：原纪律"main 上除 `Statement.lean` sanctioned 占位外零 sorry"
（2026-09-13 已放宽为"在制骨架 sorry 可短暂存在"）正式修订为——
**main 允许携带 sorry 债务，债务以 `DEBT.md`（由 `lean/scripts/debt_ledger.py`
生成）为唯一权威刻度**。wip/auto-packing（packing 25 模块 + local 39 模块，
64 模块骨架）已合入 main（`aad4fb35`）。**已向人类汇报并获批准**
（2026-09-17 会话，用户原话："我考虑去掉 main 不能有 sorry 这个限制"）。

**理由**：

- packing/local 骨架（64 模块、~3000 定理陈述）长期养在 wip 分支上，
  合入代价随时间单调上升（跨模块撞名、接口漂移）；
- 终验标准不变、只是推迟：主定理证明本体零 sorry 可达 + 公理仅标准三
  （+ Phase 2 限定 native_decide）仍是项目终点验收条件；
- Lean 编译器即判官：sorry 无法冒充证明，`#print axioms` 里的 `sorryAx`
  永远可见；债务账本使"慢慢填"成为可度量的烧账过程而非口头承诺。

**配套约束**：

- 陈述保真审查成为唯一质量阀门：sorry 定理的**陈述**（尤其装配脊柱接口与
  各章 capstone）必须过 `docs/statement-fidelity.md` 审查，不得随本政策放宽；
- 每批次闭合后刷新 DEBT.md；新增未经授权的 sorry 会在 diff 中现形；
- G4 生成的巨型案例证书文件（百万行级）暂缓合 main，按波次验收后分批合入。


## 2026-08-10 — 修订"禁用 native_decide"：枚举完备性计算改为限定范围 native_decide

**变更**：PLAN.md §2 的"`native_decide` 禁用"修订为——**仅** tame 图枚举的
完备性计算（`next_tame` 工作列表闭包 + 终图同构比对的 Bool 求值）允许
`native_decide`；其余一切（全部数学证明、Archive 数据、checker 正确性定理、
主定理组装）维持内核检验不变。**已向人类汇报并获批准**（2026-08-10 会话）。

**理由**（实测数据）：

- 全枚举树规模（AFP `ArchStat.thy` 官方 `count` 注释，Python 复算 Tri 逐位吻合）：
  Tri 312,764 / Quad 134,291,356 / Pent 1,401,437,009 / Hex 334,466,383，
  合计 ~18.7 亿次扩展；AFP 用编译代码 `by eval` 需 11 小时。
- 实测 Lean 内核 `decide` 重放：~5-13 s/节点（Pent 规模；瓶颈
  `generatePolygonTame` 的候选过滤，比 Python 慢 ~2000×，系内核 whnf
  本质速度，预期优化空间 10-50×，不够）。全树内核重放 ≈ 10⁶ 核时 +
  TB 级证书数据——差 4-5 个数量级，不可行。
- 枚举完备性不存在非对称证书：验证"没有漏图" = 重新枚举，逐节点证书
  只改变并行度不改变总内核工作量。
- 同构意义上的去重（worklist 模同构）在数学上对本枚举器**不成立**
  （`minimalFace` 平局打破依赖面列表顺序，非同构不变），故无法借此
  缩小闭包集。AFP 的 trie worklist 也只对收集集去重、照样全树扩展。
- 信任基影响：`#print axioms tame_classification` 将多出
  `Lean.ofReduceBool`（Lean 编译器+运行时进 TCB），与 AFP `eval`、
  HOL Light Flyspeck 的信任基持平，仍远优于 1998 年不可信代码。
- 缓解：Tri 种子（312k 节点，内核重放 ≈ 26 核时）另行做**纯内核
  `decide`** 版本，与 native 路径交叉校验同一套 checker 代码语义。

**范围控制**：`native_decide` 只允许出现在 `Kepler.Graphs.Cert*`
（枚举闭包分片定理）中；CI/lint 检查其余文件零命中。

## 2026-08-09 — Phase 2 启动：两个工具链决定

1. **求解器版本锁定方式：pinned 源码包 + sha256，而非 nix/docker**（对 PLAN.md §3
   建议的偏离，在此记录）。理由：本机无 nix；docker 对 plantri 这类单文件 C
   程序是过度工程；源码包（plantri55.tar.gz，sha256 记入 `reference/LOCK.md`）
   已满足可复现性。若后续求解器（SoPlex/dReal）依赖复杂，再评估 docker 并另行记录。
2. **Phase 2 蓝本从 flyspeck 仓库内的 `formal_graph/isabelle_tame` 换成 AFP 条目
   Flyspeck-Tame**。理由：AFP 版是维护中的完整版本（含 `Invariants.thy`、
   `TameEnumProps.thy` 等剪枝正确性证明，flyspeck 仓库副本缺这些 Props 理论）；
   两者共有文件内容一致（Archive 四个 .ML 逐字节相同）。不构成对 §2
   锁定决策的变更（"参考 Nipkow–Bauer 的 Isabelle 工作"不变，只是取更全的副本）。
3. **Phase 2 证书策略微调**：枚举函数已移植为 Lean 可执行定义，因此完备性靠
   移植剪枝正确性定理（Invariants/GeneratorProps/TameEnumProps）+ 逐图可达性
   证书在内核重放，而非导出整棵搜索树。与 PLAN.md §4 Phase 2 的精神一致
   （"枚举树 + 剪枝依据作为完备性证书"），但载体从"数据"变为"逐图见证 +
   一次性数学证明"。详见 `docs/architecture.md` Phase 2 节。

## 2026-08-09 — 初始化：确认 PLAN.md §2 全部锁定决策

- 证明助手：Lean 4 + Mathlib。toolchain 锁定 `leanprover/lean4:v4.32.2`（elan），
  Mathlib 锁定 tag `v4.32.2`（见 `lean/lean-toolchain` 与 `lean/lakefile.toml`）。
- 计算信任模型：证书化计算；`native_decide` 项目内禁用。
- 证明蓝图：Hales《Dense Sphere Packings》(Cambridge, 2012)。
- 图枚举：plantri/nauty 生成 + 完备性证书 + Lean checker。
- LP：SoPlex exact / QSopt_ex 有理精确求解 + VIPR 证书；HiGHS 仅交叉验证。
- 非线性：dReal 优先，Arb 球算术分支定界兜底。
- 硬件：本机（128 核 / 1 TB RAM）。
- 参考库只读克隆于 `reference/`，commit hash 记入 `reference/LOCK.md`。

# DECISIONS.md — 决策日志

> 依据 PLAN.md §2：任何偏离已锁定决策的变更必须先在此记录理由并向人类汇报。
> 新条目追加在顶部（倒序）。

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

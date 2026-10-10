# Kepler 猜想机器证明重做项目 — 计划与路线图（原 Kickoff Plan，2026-10-10 合并 HANDOFF 并收录当前战略）

> 本文档是项目的权威计划文件：项目目标、锁定决策、阶段定义与现状、**当前战略
> （从上到下-从下往上-会师，2026-10-10 用户批准）**、执行规程。
> 设计背景：1998 年 Hales–Ferguson 原始证明（300 页文本 + 4 万行不可信代码），
> 2014 年 Flyspeck 项目完成形式化（HOL Light/Isabelle，11 人年）。
> 本项目的目标不是"重新发明证明"，而是用 2026 年的工具链**以证书化计算范式重造一个
> 端到端形式化证明**，并沉淀一条可复用的"求解器 → 证书 → 形式化 checker"流水线。
> 实时进度看板 = `STATUS.md`（每批次刷新）；债务刻度 = `DEBT.md`；长期决策 =
> `DECISIONS.md`；端到端对象 = `lean/Kepler/Final.lean` 的
> `the_kepler_conjecture_e2e`（2026-10-10 立）。
> 原 `HANDOFF.md`（2026-09-18 交接文档）已并入本文件后退役，历史版本见 git。

---

## 1. 项目目标

**主目标**：在 Lean 4 + Mathlib 中完成定理

```
开普勒猜想：三维欧氏空间中全等球堆积的密度上确界 = π / √18 ≈ 0.74048
```

要求：

- 定理陈述与 Flyspeck 的形式化陈述（`the_kepler_conjecture`）语义一致；
- `lake build` 通过，证明体中**零 `sorry`、零自引入公理**（仅依赖 Lean 内核与 Mathlib）；
- 所有计算性断言（图枚举、线性规划、非线性不等式）均由**证书 + 已验证 checker** 支撑，
  不信任任何生成器/求解器的代码本身。

**次目标**：图枚举、LP、非线性验证三条流水线独立可复用，文档齐全。

**明确的非目标**（防止范围蔓延）：

- 不寻求新的数学证明路线；严格以 Hales《Dense Sphere Packings》为蓝图；
- 不做 GPU 移植（最重的 kernel 要求 FP64 + 定向舍入 + 确定性，CPU 已足够）；
- 不把 Flyspeck 的 HOL Light 库机械翻译一遍——它是对照参考，不是输入；
- 不向上游 Mathlib 提交 PR（除非顺手），优先项目内闭环。

**状态注（2026-10-10）**：主目标当前以"带 3 个冻结接口占位的端到端对象
`the_kepler_conjecture_e2e`"形态活着（`Kepler/Final.lean`，axiom 面 = sorryAx(3
接口) + 624 特许 shard + 标准三）；零 sorry 终点 = 会师后的清叶阶段（见 §5）。

## 2. 已锁定的关键决策（不要重新摇摆）

| 决策点 | 选择 | 理由 |
|---|---|---|
| 证明助手 | Lean 4 + Mathlib（`elan` 锁定 toolchain） | 社区与库生态最活跃，AI 辅助工具链最好 |
| 计算信任模型 | 证书化计算（certifying algorithms） | 可信基 = Lean 内核 + 小 checker，最小化 |
| 证明蓝图 | Hales《Dense Sphere Packings》(Cambridge, 2012) | 该书就是为形式化写的，章节即模块划分 |
| 图枚举 | plantri/nauty 生成 + 完备性证书 + 验证 checker | 不重写枚举器；参考 Nipkow–Bauer 的 Isabelle 工作 |
| LP | 精确有理单纯形（SoPlex exact / QSopt_ex）+ VIPR 证书 | 从根上消除浮点问题 |
| 非线性不等式 | 分层：dReal 自动证 → Arb 球算术分支定界兜底 | 对应 Hales 2002 年"自动化不足"的批评 |
| `native_decide` | 禁用（它把编译器纳入可信基） | 坚持内核可检验的证书 |

如确需推翻某条决策，必须先在 `DECISIONS.md` 中记录理由并向人类汇报，不得静默变更。

**已记录的决策演化**（详见 DECISIONS.md 对应日期条，非静默变更）：
`native_decide` 于 2026-08-10 起对 `Kepler.Graphs.Cert*` 枚举闭包开 scoped
exception（2026-09-19/26 扩展并锁定公理足迹形态，现 624 个特许 shard 公理）；
main 于 2026-09-17 起允许携带 sorry 债务（债务刻度 = `DEBT.md`）；
生产环境 2026-09-28 从旧 128 核服务器迁移至 Apple M3 Pro 12 核/36GB（重型计算
挂起，见 §5 计算约束）。

## 3. 环境现状

- **现行基线**：Apple M3 Pro 12 核 / 36GB（2026-09-28 起；旧 128 核/503G 服务器
  报废，磁盘不可恢复，代码与文档零损失）。
- Lean 工具链 v4.32.2（elan 锁定）；`lake` 在 `~/.elan/bin`。
- 参考库只读克隆 `reference/`（`LOCK.md` 记 hash）；关键 HOL 原文已入库
  `lean/scripts/*.hl`。
- 求解器（SoPlex/glpsol/dReal/FLINT）在 macOS **需重装**（旧机二进制不可用）——
  Phase 3/4 计算战役的前置（见 §5 计算约束）。
- LLM 工人 = ZCode sub agents（opencode CLI 已退役）；编排者 = 主 agent，
  滚动批次制（用户 2026-10-10 令：每批清空即开下一批 3-5 线）。

## 4. 分阶段计划与现状

### Phase 1 — 定理陈述形式化 ✅

陈述层完成：`Kepler/Statement.lean` 的 `the_kepler_conjecture`（fidelity 文档
`docs/statement-fidelity.md`）。`Statement.lean:111` 的 Phase-1 占位 sorry 为
sanctioned 占位，终版去重时退役（端到端承载 = `Kepler/Final.lean`）。

### Phase 2 — tame 平面图枚举 ✅ 100%（闭合）

19,715 图 + 完备性证书 + 内核验证；换机后 585 片 olean 重建收官（2026-10-10，
五片孤儿经批准删除，glob 收敛 G2 已验证态）；wire 588 片零缺失。
验收门 G2 = `tame_classification` 闭合 ✅。

### Phase 3 — 线性规划 ✅ 100%（求解+内核验证层）

43,078 终端 LP 全部内核验证（SoPlex 精确 + glpsol 精确对偶兜底，`glpsol_dual.py`）。
**⚠️ 换机丢失重跑产物**（DECISIONS 2026-09-28 清单）——管线在 git，产物需在
macOS 重装环境后重跑（见 §5 计算约束与 T2 波）；P6-D 桥原型已验证。

### Phase 4 — 非线性不等式 🟡 长杆

求解层 68/176 可信闭合 + 92 prep 家族待重做（旧证据链作废）+ 16 真残余；
内核层 8 案端到端 + 两巨兽重放暂停（784/6321、770/12553，olean 保留可幂等续跑）
+ BIXPCGW 诚实 STUCK（归 TM/mono-convex 车道）。naive 区间过估导致叶数爆炸
（BIXPCGW 2.0× 膨胀零收敛、MKFKWU 级 ≥10⁹ 叶）——对策 = Taylor 模型
（200s→3.2s/叶）+ mono/convex 降维（ite-hull 4.8× 削减）+ 证书瘦身 78.3% +
arctan 曲率紧致化，样本曾达 ~95% 可验证。**重计算按 §5 约束挂起**。

### Phase 5 — 文字证明移植 🟡 主战场

骨架 100%（25+39 模块，2713 sorry 起步）；hypermap/fan/topology/planarity/
Conforming/polyhedron 全书收官（~61.8k 行 HOL 全证）。当前滚动批次制清债：
账本 1951→1719（2026-10-10）。大块剩余：tame 文字章移植（64 .hl/4.6MB，T3 线
立项侦察在飞）、GRUTOTI 终章（在飞）、p24 路线图（2/5 档落地）、gammaX
Wave V/E/M（侦察翻案 C→B）。

### Phase 6 — 集成与交付 🟡（**终装配已立**）

`Kepler/Final.lean` 的 `the_kepler_conjecture_e2e`：主定理以自身形态自脊柱
（`Kepler/Assembly.lean` 四接口）导出；`lake build Kepler.Final` 全项目源码闭合
（9368 jobs）。`#print axioms` 即主定理实时债务图。剩余：三接口清债（§5 会师
战略的主战场）+ Statement 占位去重 + 全量公理审计终验 + 复现文档。

## 5. 当前战略（2026-10-10 用户批准）：从上到下 — 从下往上 — 会师

**模型**：端到端对象已立；中部层（接口与叶子之间的结构）尚未显式化。战略 =
三线并进直至"会师"，然后按 BFS/DFS 清叶。

```
e2e ＝ nonlinearInequalities ⊕ lpArchiveCertificates ⊕ textCapstone
  ├─ T 线（从上到下）：把每根粗 sorry 显式化为具名中层陈述骨架
  │   （temporary sorry 增多 = 健康：债从粗变细、逼近内核）
  ├─ B 线（从下往上）：用已完成的低层真证节点逐个顶死中层
  └─ 会师判据：e2e 依赖闭包内不存在"未展开的中层节点"——
      每根 sorry 要么是叶子（数学/计算债），要么已被下层顶死
会师后 = BFS/DFS 清叶（按链清，不再有结构性工作）
```

**会师仪表**：reachable-sorry census（沿 `the_kepler_conjecture_e2e` 依赖闭包
清点，按文件/章聚合）——与全仓账本 1719 区分，会师看可达口径。

### T 线（展开波）

- **T1**：扩 `TheNonlinearInequalities` → 六分量 ID 清单（539 去重 ID）逐 ID
  陈述骨架 + `CertifiedIneqHolds` 语义。已闭合案例当场转真；92 prep/16 残余留
  叶子并标 `deferred-compute`。
- **T2**：扩 `lpArchiveCertificates` → per-record（6,925）陈述骨架（P6-D 形）。
  数据重跑标 deferred-compute；桥的 Lean 工程照做。
- **T3**：扩 textCapstone 的 TameSpine 分支 → tame 文字章移植立项（64 .hl 盘点
  → 批次表），随后按 planarity/Conforming 成熟流水线分批移植。**最大的单一工作
  量，纯编译，Mac 全可行。**
- **T4**：扩 packing 分支 → `PACKING_CHAPTER_MAIN_CONCLUSION`（PA25）前提树
  显式化（材料单已备：TIWWFYQ 侦察 + PA2 桩地图）。

### B 线（上拉波）

- **B1** GRUTOTI 终章（在飞）：pivot ¬nullSet 支清零（首向+反向 k=2 力争全清；
  G3 反向 k=3/4 允许精确记账收窄）。
- **B2** p24 路线图（三阶段在飞）：余情形 B + 正体积工具 + 装配波（√2→√8 修正
  扫描；一阶段签名 vacuous 缺陷修复）。
- **B3** PA20 gammaX Wave V/E/M（体积桥 C→B 已翻案；SUM_PAIR_2_SET 转正即可）。
- **B4** PA2 桩收割三波（DUUNHOR 接口升级 −1 → A 类 20 根 → XNHPWAB1/4 杠杆件）。
- **B5** LUNAR 链向上审计（转真后的免费连带清点）。

### 计算约束（用户 2026-10-10：Mac 不跑重计算）

| 项 | 处置 |
|---|---|
| Phase 4 两巨兽重放（784/6321、770/12553） | deferred-compute，等强机器 |
| 92 prep 家族重求解 | deferred-compute + 策略决策（TM/BBTreeGD） |
| LP 主批 6,866 + glpsol 尾部 59 重跑 | deferred-compute；桥工程照做 |
| tame 章移植、PA2x 填证、全部桥/骨架工程 | 纯编译，Mac 全可行 |

### 会师后（清叶期）

叶子三分：纯 Lean 填证（批次流水线）/ deferred-compute（等强机器）/ 真数学缺口
（已知清点：pivot 反向 k=3/4、GRKIBMP 尖锐边界组等）。清叶顺序 = BFS（接口向
下逐层）为主、DFS（单链贯通）为辅——按 census 的递减斜率择路。

## 6. 仓库结构

```
kepler-conjecture-lean4/
├── PLAN.md                 # 本文档（计划 + 当前战略）
├── STATUS.md               # 实时进度看板（每批次刷新）
├── DEBT.md                 # sorry 债务账本（debt_ledger.py 生成）
├── DECISIONS.md            # 决策日志
├── lean/
│   ├── Kepler/Statement.lean     # Phase 1（占位待终版退役）
│   ├── Kepler/Final.lean         # Phase 6 终装配（e2e 承载）
│   ├── Kepler/Assembly.lean      # Phase 6 脊柱（四接口）
│   ├── Kepler/Graphs/            # Phase 2 checker + CertShards wire
│   ├── Kepler/LP/                # Phase 3 checker
│   ├── Kepler/Interval/          # Phase 4 证书 checker
│   ├── Kepler/Geom/              # 体积/测度/方位角地基
│   ├── Kepler/Text/              # Phase 5 文字证明模块（PackingAuto*/LocalAuto*）
│   └── scripts/                  # auto_gate.sh / debt_ledger.py / 生成器
├── pipeline/               # 不受信任的生成器/求解器封装
├── reference/              # flyspeck 只读克隆 + LOCK.md
└── docs/                   # 侦察报告/章程/交接/架构文档
```

## 7. 执行规程（执行 agent 必须遵守）

1. **闸门纪律**：一切 Lean 变更经 `lean/scripts/auto_gate.sh` 五道机械闸后由编排
   者提交；新文件先 `git add`（未跟踪文件对规则①不可见）；探针不可信，落盘终
   探针硬条款为准（/tmp 副本 EXIT=0 → cp → diff 字节一致 → 真路径复探）。
2. **陈述冻结**：陈述改动仅经 SF 通道（提案条目 + 用户批准 + 执行版补丁 +
   GATE_MODE=STATEMENT-FIX）；名字空间/可见性修复循 arcLengthICD 先例。
3. **不信任生成器**：pipeline/ 输出必须经 checker 核验后才可被 Lean 证明引用。
4. **诚实记账**：新 sorry 必须带 `-- NEEDS`；不可达成的目标诚实收窄 + 路线图；
   探针同名失明（改名探针法）、错误掩蔽链（迭代到零错）入纪律。
5. **版本锁定**：toolchain/Mathlib/求解器版本锁定；升级单独成 commit。
6. **卡壳处理**：同一问题失败 3 次 → `docs/hard-cases.md` 并切换降级路线；推翻
   §2 决策 → 停止并向人类汇报。
7. **滚动批次**（2026-10-10 用户令）：每批 sub agents 清空即开下一批 3-5 线；
   编排者闸/提交/推送全部 lane 产物；lane 禁 git/build/gate。
8. **已知坑精选**（全量见 git 历史与 docs/session-*-wrap.md）：验收构建必须自然
   退出（掐死时 error 未 flush 是假绿）；`#print axioms` 长输出折行须
   `tr '\n' ' '`；后台命令的 cd 不改持久 cwd；BSD grep `\+` 静默空（用 `[+]`）；
   docstring 折行以 sorry 开头会被规则③误计；探针头同名 import 致证明体静默跳
   过（改名探针法）；`set` ε-类定义可卡死 whnf（改 obtain/E-结构）。

## 8. 里程碑

| 里程碑 | 内容 | 状态 |
|---|---|---|
| M0-M4 | 环境/陈述/图枚举/LP/非线性求解 | ✅（M4 求解层 68/176 + 内核 8 案，重计算部分 deferred） |
| **M5′** | **端到端对象立于主定理形态** | ✅ **2026-10-10（`the_kepler_conjecture_e2e`）** |
| **M5″** | **会师**（依赖闭包内无未展开中层节点） | 🟡 T/B 线推进中 |
| M5 = G5 | 主定理证明零 sorry 组装 | 🟡 = M5″ + 清叶期 |
| M6 = G6 | 交付（干净机器 `make reprove` 全绿） | ⬜ |

已知风险排序：Phase 4 重计算量（等强机器/加速车道）、tame 章移植体量（批次流水
线缓解）、Mathlib 缺口（项目内自证）、陈述保真（fidelity 文档 + SF 通道）。

## 9. 参考资料

- Hales, *Dense Sphere Packings: A Blueprint for Formal Proofs*, Cambridge, 2012
- Hales et al., *A Formal Proof of the Kepler Conjecture*, Forum of Mathematics, Pi, 2017
- Hales, *Some algorithms arising in the proof of the Kepler conjecture*, arXiv:math/0205209
- Solovyev 博士论文（2012）；Nipkow & Bauer tame enumeration（Isabelle）
- 仓库：flyspeck/flyspeck、flyspeck/kepler98、leanprover-community/mathlib4
- 工具：plantri/nauty、SoPlex、QSopt_ex、VIPR、dReal、Arb/FLINT

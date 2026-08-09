# Kepler 猜想机器证明重做项目 — 启动计划（Kickoff Plan）

> 本文档是项目的唯一权威启动说明，供执行 agent 在服务器上自主推进使用。
> 设计背景：1998 年 Hales–Ferguson 原始证明（300 页文本 + 4 万行不可信代码），
> 2014 年 Flyspeck 项目完成形式化（HOL Light/Isabelle，11 人年）。
> 本项目的目标不是"重新发明证明"，而是用 2026 年的工具链**以证书化计算范式重造一个
> 端到端形式化证明**，并沉淀一条可复用的"求解器 → 证书 → 形式化 checker"流水线。

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

## 2. 已锁定的关键决策（不要重新摇摆）

| 决策点 | 选择 | 理由 |
|---|---|---|
| 证明助手 | Lean 4 + Mathlib（`elan` 锁定 toolchain） | 社区与库生态最活跃，AI 辅助工具链最好 |
| 计算信任模型 | 证书化计算（certifying algorithms） | 可信基 = Lean 内核 + 小 checker，最小化 |
| 证明蓝图 | Hales《Dense Sphere Packings》(Cambridge, 2012) | 该书就是为形式化写的，章节即模块划分 |
| 图枚举 | plantri/nauty 生成 + 完备性证书 + 验证 checker | 不重写枚举器；参考 Nipkow–Bauer 的 Isabelle 工作 |
| LP | 精确有理单纯形（SoPlex exact / QSopt_ex）+ VIPR 证书 | 从根上消除浮点问题 |
| 非线性不等式 | 分层：dReal 自动证 → Arb 球算术分支定界兜底 | 对应 Hales 2002 年"自动化不足"的批评 |
| 硬件 | 本机多核 CPU / 云 spot 实例，预算 < 500 美元 | 总计算量约为"一台 128 核机器几天" |
| `native_decide` | 禁用（它把编译器纳入可信基） | 坚持内核可检验的证书 |

如确需推翻某条决策，必须先在 `DECISIONS.md` 中记录理由并向人类汇报，不得静默变更。

## 3. 环境准备（Phase -1，第一周内完成）

服务器：Linux，≥64 核、≥256 GB RAM、≥2 TB 磁盘即可（全部计算绰绰有余）。

```bash
# Lean 工具链
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
# 求解器与库（用 nix 或 docker 锁定版本，写入 flake.nix / Dockerfile）
#   - plantri, nauty        （图枚举）
#   - SoPlex (exact mode), QSopt_ex, HiGHS  （LP，HiGHS 做交叉验证）
#   - dReal                 （δ-完备非线性 SMT）
#   - FLINT / Arb           （球算术）
#   - 可选：Julia + IntervalArithmetic.jl（交叉验证用）
```

同时 `git clone` 以下只读参考库到 `reference/`（记录 commit hash 入 `reference/LOCK.md`）：

- `github.com/flyspeck/flyspeck` — Flyspeck 形式化库（HOL Light/Isabelle）
- `github.com/flyspeck/kepler98` — 1998 原始代码与数据（含 3 GB 归档的索引）
- `github.com/IPOL-Studio/... ` 不需要；其余按需

**验收门 G0**：`lake build` 空项目通过；`reference/LOCK.md` 落盘；CI（GitHub Actions 或本地 runner）能跑通一个 hello-checker 测试。

## 4. 分阶段计划

### Phase 1 — 定理陈述形式化（先行，2–4 周）

任务：

1. 形式化堆积密度定义：R³ 中无重叠单位球族，密度为以大球截断取极限（沿 Flyspeck 的陈述）；
2. 形式化主定理 `the_kepler_conjecture : density ≤ π / Real.sqrt 18`；
3. 用 `sorry` 占位证明体，但**陈述本身必须完整、无 sorry**；
4. 与 Flyspeck 的 `the_kepler_conjecture` 逐条对照，写 `docs/statement-fidelity.md` 论证语义等价（这步防止"证错了定理"——本项目最大的无声风险）。

**验收门 G1**：陈述通过类型检查；fidelity 文档完成；向人类汇报一次。

### Phase 2 — tame 平面图枚举流水线（4–6 周，可与 Phase 1 并行）

背景：证明的关键引理之一是"任何反例分解星对应一张 tame 平面图，而 tame 平面图穷尽于一个有限 Archive"。

任务：

1. 在 Lean 中定义 tame 平面图谓词（面大小 3–6、权重上界等，逐条对照 Flyspeck 定义）；
2. 用 plantri 生成带剪枝的平面图枚举，输出 (a) Archive 图清单，(b) 枚举树 + 剪枝依据作为**完备性证书**；
3. 写 Lean checker：验证 (i) 证书枚举树确实完备（剪枝条件逐项成立），(ii) Archive 中每张图满足 tame 谓词——checker 本身在 Lean 内核里验证；
4. 与 Flyspeck 仓库中的 Archive 文件交叉核对图清单（同构意义下应一致；Flyspeck 版 Archive 比 1998 版小，以其仓库文件为准，不要硬编码数量）。

**验收门 G2**：`theorem tame_classification : 任何 tame 平面图同构于 Archive 中某图` 在 Lean 中闭合（证明依赖 checker 的运行结果，但运行由内核检验）。

风险提示：完备性论证是本阶段唯一真正微妙的部分——1998 年 Java 版就漏过图。不要信任 plantri 的输出完整性，一切从证书走。

### Phase 3 — 线性规划流水线（4–6 周）

任务：

1. 把每张 Archive 图对应的优化问题按蓝图松弛为 LP 族（生成器可用任意顺手的语言，不受信任）；
2. 用 SoPlex exact / QSopt_ex 以**有理数精确求解**，输出 VIPR 格式证书（原始界 + 对偶解/Farkas 证书）；
3. 用 HiGHS 浮点解做交叉 sanity check（仅作报警，不入证明）；
4. 写 Lean VIPR checker（纯有理数算术，数百行），验证"每张图的 LP 上界 < 阈值 8 pt"；
5. 约 10 万个小 LP：本地多核批量跑，预计墙钟分钟到小时级。

**验收门 G3**：`theorem lp_bounds : ∀ G ∈ Archive, lp_bound G < 8 * pt` 闭合。

### Phase 4 — 非线性不等式验证（6–10 周，算力大头）

背景：约一千个低维（≤6 维）非线性不等式，定义域经剖分后约 23,000 个子断言。

任务（分层策略，先易后难逐层过滤）：

1. **第一层 dReal**：把不等式翻译为 SMT-LIB 实数公式，δ-完备判定；能自动证掉的直接出 δ-证迹；
2. **第二层 Arb 球算术**：对剩余不等式做自适应精度分支定界，输出"盒子剖分 + 每盒区间界"证书；
3. **Lean checker**：验证每个盒子的区间界计算（复用 Flyspeck/Solovyev 的浮点形式化思路，但改为内核可检验的证书格式）；
4. 交叉验证：抽样 1% 用 Julia IntervalArithmetic.jl 独立重算比对（报警用，不入证明）。

**验收门 G4**：`theorem nonlinear_inequalities : …` 闭合。

降级预案：若某不等式 dReal 超时且 Arb 剖分爆炸，先记录到 `docs/hard-cases.md`，可回退到 Flyspeck 对该不等式的处理方式（查其证明脚本中的剖分参数直接复用）。连续 3 个硬案例无法闭合 → 向人类汇报。

### Phase 5 — 文字证明移植（人力大头，启动后即持续推进，预计占总工期 60%+）

任务：把《Dense Sphere Packings》的文本证明（Fejes Tóth 归约、分解星、打分函数、8 pt 上界论证）逐章形式化为 Lean 模块。

1. 先建立模块依赖图（书的章节 → Lean 文件），写入 `docs/module-map.md`；
2. 顺序：先形式化"组合骨架"（分解星 → 平面图 → 打分不等式的归约），它把 Phase 2/3/4 的三个定理串成主定理；
3. 再填几何与分析引理（Voronoi、扇形体积、局部密度界等）——这部分允许调用 Mathlib 实分析，缺的引理在项目内自证；
4. 全程可用 Flyspeck 的 HOL Light 证明作对照（遇到卡住的引理，先查 Flyspeck 怎么证的）。

**验收门 G5**：主定理证明体仅剩"引理 → 引理"的组装，无 sorry。

### Phase 6 — 集成与交付（2–4 周）

1. 主定理闭合：`the_kepler_conjecture` 无 sorry、无额外公理，`#print axioms` 输出仅标准公理；
2. 复现性：nix/Docker 锁定全部依赖；一条 `make reprove` 从头重建（含重跑 checker）；
3. 交付文档：`README.md`（如何复现）、`docs/architecture.md`（证书格式与流水线）、`DECISIONS.md`（决策日志）；
4. 归档：全部证书压缩存档（预计 GB 级），记录 SHA-256。

**验收门 G6（Definition of Done）**：干净机器上 `make reprove` 全绿。

## 5. 仓库结构（Phase 0 时建立）

```
kepler/
├── PLAN.md                 # 本文档
├── DECISIONS.md            # 决策日志（每次偏离/选择必记）
├── lean/                   # Lean 4 项目（lakefile + lean-toolchain）
│   ├── Kepler/Statement.lean     # Phase 1
│   ├── Kepler/Graphs/            # Phase 2 checker + tame 谓词
│   ├── Kepler/LP/                # Phase 3 VIPR checker
│   ├── Kepler/Interval/          # Phase 4 区间证书 checker
│   └── Kepler/Text/              # Phase 5 文字证明模块
├── pipeline/               # 不受信任的生成器/求解器封装（nix/docker 锁定）
├── certificates/           # 产出的证书（git-lfs 或外部存储，记哈希）
├── reference/              # flyspeck / kepler98 只读克隆 + LOCK.md
├── docs/                   # statement-fidelity / module-map / hard-cases / architecture
└── Makefile                # reprove / check / compute 目标
```

## 6. 执行规程（执行 agent 必须遵守）

1. **零 sorry 纪律**：除 Phase 1 明确允许的证明体占位外，任何 sorry 不得超过一个里程碑周期；每周自查并记录在进度报告里。
2. **不信任生成器**：pipeline/ 下的一切输出都必须经 checker 核验后才允许被 Lean 证明引用。
3. **版本锁定**：Lean toolchain、Mathlib commit、求解器版本全部锁定并记录；升级必须单独成 commit。
4. **卡壳处理**：同一问题失败 3 次 → 写入 `docs/hard-cases.md` 并切换降级路线；涉及推翻第 2 节决策 → 停止并向人类汇报。
5. **里程碑汇报**：每过一个验收门 G1–G6，向人类提交一次简报（做了什么、机时、剩余风险）。
6. **进度跟踪**：维护 TODO 列表；Phase 5 的引理级进度用 `docs/module-map.md` 中的勾选表维护。
7. **成本控制**：总机时预算按"128 核 × 7 天"为上限；超出 50% 时预警。

## 7. 里程碑与量级估算

| 里程碑 | 内容 | 估算（AI agent 墙钟，高度不确定，仅作锚点） |
|---|---|---|
| M0 = G0 | 环境 + 仓库骨架 | 第 1 周 |
| M1 = G1 | 定理陈述 + fidelity | 第 4 周 |
| M2 = G2 | 图枚举闭合 | 第 8 周 |
| M3 = G3 | LP 闭合 | 第 10 周 |
| M4 = G4 | 非线性不等式闭合 | 第 16 周 |
| M5 = G5 | 文字证明组装完成 | 主要不确定项，按月计 |
| M6 = G6 | 交付 | M5 后 2–4 周 |

已知风险排序（从高到低）：

1. **Phase 5 文字证明的体量**——Flyspeck 当年 11 人年的主体就在这里；AI 辅助能压缩但不可能消失。缓解：尽早启动、章节并行、卡住先查 Flyspeck 对应引理。
2. **Mathlib 缺口**（球面几何/特殊函数不等式可能缺引理）——缓解：项目内自证，不等待上游。
3. **陈述保真度**（证出一个语义偏弱的定理）——缓解：G1 的 fidelity 文档 + 人类审阅。
4. **证书格式对接返工**——缓解：每个 Phase 先用 10 个小案例打通"求解器→证书→checker→Lean 定理"全链路，再规模化。

## 8. 参考资料

- Hales, *Dense Sphere Packings: A Blueprint for Formal Proofs*, Cambridge, 2012（蓝图）
- Hales et al., *A Formal Proof of the Kepler Conjecture*, Forum of Mathematics, Pi, 2017（arXiv:1501.02155）
- Hales, *Some algorithms arising in the proof of the Kepler conjecture*, arXiv:math/0205209
- Solovyev 博士论文（2012，非线性不等式形式化验证方法）
- Nipkow & Bauer, tame plane graph enumeration in Isabelle（Archive 完备性论证的范本）
- 仓库：flyspeck/flyspeck、flyspeck/kepler98、leanprover-community/mathlib4
- 工具文档：plantri/nauty、SoPlex、QSopt_ex、VIPR 格式、dReal、Arb/FLINT

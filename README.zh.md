# 开普勒猜想：Lean 4 重证项目

[English README](README.md)

在 **Lean 4 + Mathlib** 中以证书化计算范式重造的**开普勒猜想**端到端形式化证明：

> 三维欧氏空间中全等球堆积的密度上确界 = **π / √18 ≈ 0.74048**。

本项目不重新发明证明：蓝图是 Hales《Dense Sphere Packings》（Cambridge, 2012，
为形式化而写的书），Flyspeck 项目（HOL Light/Isabelle，2014）作为只读对照参考
而非输入。所有计算性断言（图枚举、线性规划、非线性不等式）均由**证书 + 已验证
checker** 支撑——不信任任何生成器/求解器的代码本身。

## 设计原则

- **证书化计算**：不受信任的生成器（plantri/nauty、SoPlex / QSopt_ex、dReal、
  Arb/FLINT）产出证书，Lean 侧 checker 在内核中核验。可信基 = Lean 内核 +
  小 checker，仅此而已。
- **`native_decide` 全项目禁用**（它会把编译器纳入可信基），唯一特许例外 =
  Phase 2 图枚举分片（624 个 shard 公理，足迹登记于 `DECISIONS.md`）。
- **陈述保真是唯一质量阀门**：终版陈述与 Flyspeck `the_kepler_conjecture`
  语义一致；所有折算登记于 `docs/statement-fidelity.md`；陈述改动仅经 SF 通道
  （`docs/statement-fix-proposals.md`）。
- **诚实记账**：sorry 必须带 `-- NEEDS` 注记；实时运营账本
  （`docs/priority-queue.md`）与端到端定理的实时公理面是客观进度刻度。
  不可复现的证据一律降级，不保留。数字要么带 commit 与日期实测，要么标 stale
  ——**禁止在文档之间手抄**。

## 仓库结构

```
kepler-conjecture-lean4/
├── README.md / README.zh.md
├── PLAN.md                 # 2026-10-10 计划快照（不是当前状态）
├── DECISIONS.md            # 决策日志（根级唯一 current 文档）
├── lean/                   # Lean 4 工程（toolchain v4.32.2，elan 锁定）
│   ├── Kepler/Statement.lean     # Phase 1：定理陈述
│   ├── Kepler/Final.lean         # Phase 6：端到端定理 the_kepler_conjecture_e2e
│   ├── Kepler/Assembly.lean      # Phase 6：装配脊柱（四接口）
│   ├── Kepler/Graphs/            # Phase 2：tame 图枚举 checker
│   ├── Kepler/LP/                # Phase 3：LP 证书 checker
│   ├── Kepler/Interval/          # Phase 4：区间/Taylor 证书 checker
│   ├── Kepler/Geom/              # 体积/测度/方位角地基
│   ├── Kepler/Text/              # Phase 5：文字证明移植模块
│   └── scripts/                  # 闸门 / 账本 / 生成器
├── pipeline/               # 不受信任的生成器与求解器封装（永不入可信基）
├── certificates/           # 证书登记处（SHA-256 + 复现命令）
├── reference/              # 只读参考克隆（flyspeck 等，LOCK.md 锁 hash）
└── docs/
    ├── README.md           # 导航：想查什么去哪个文件
    ├── priority-queue.md   # 唯一实时账本：在飞 + 排队 + 最近日志
    ├── archive/            # 历史（scouts / handoffs / projects / lane-archives /
    │                       #   根级旧总览）。只读证词，不是当前状态。
    ├── assets/             # 产物/草稿/探针日志
    └── statement-fix-proposals-patches/  # SF 通道补丁存档（活跃）
```

## 构建与验证

前置：[elan](https://github.com/leanprover/elan)（工具链由
`lean/lean-toolchain` 锁定，当前 **Lean v4.32.2**）。

```sh
make build     # cd lean && lake build
make check     # 构建 + 公理审计（无 sorryAx、除特许 shard 外无自引入公理）
make reprove   # 从零重建 + 审计——Definition of Done
```

注：重型重计算（LP 重跑、非线性证书重放）当前挂起等强机器，见 `PLAN.md`
§5 计算约束表；纯 Lean 编译工作在本机基线（笔记本）上全部可行。

## 状态（2026-11-09）

端到端对象 `Kepler.the_kepler_conjecture_e2e` 已立。实时公理面 = **589 行**
= **585 个 `native_decide` 图枚举 shard 公理**（信任基座，2026-11-09 定格：
580 shard-range + 5 tri-single-seed，仅 2 种形状）+ `propext` + `Classical.choice` +
`Quot.sound` + `sorryAx`（锥内 65 条，唯一真债）。

**终局标准（用户 2026-11-06 裁决，见 `AGENTS.md` §1）**：不比 Flyspeck/Isabelle 更差——
即 585 条声明信任基座（与 Isabelle `by eval` 同类、同数据）+ 零 `sorryAx` 目标，
**不是**「只剩标准三公理」（"真·标准三"明确不做；goodList 23 条已改 kernel 证明追平 HOL）。

阶段级状态（定性——**实时数字只有一个出处**）：

| Phase | 内容 | 状态 |
|---|---|---|
| 1 | 定理陈述 | ✅ 陈述已定稿 |
| 2 | tame 平面图枚举 | ✅ 19,715 图 + 完备性真证；585 条 shard 公理 = 声明信任基座（数据与原版三路对账 SAME） |
| 3 | 线性规划 | ✅ 43,078 终端 LP 证书已核；LP 检查器内核 soundness 真证；灌装债 = `lpArchiveCertificatesDebt`（锥内） |
| 4 | 非线性不等式 | 🟡 hNL 六分量 5 条接口 sorry（`nli*`）；sqrt/atan 档重型农场重放挂起（原版同为农场） |
| 5 | 文字证明移植 | 🟡 几何塔群大部分已塌（LA 系引擎层 16 文件零 sorry）；§5 两根在攻（J 战役 `jcajydu` + WSEWPCH 程序） |
| 6 | 集成与交付 | 🟡 e2e 已立且总装链真证；根面 589；信任基座 manifest `--check` 全绿 |

**数字在哪读**：唯一实时账本是
[`docs/priority-queue.md`](docs/priority-queue.md)——在飞车道、排队、最近落库、
塔群看板。指标定义与 cone / union 可达基线在
[`docs/e2e-reachability-map.md`](docs/e2e-reachability-map.md)。旧看板
（`STATUS.md` / `HANDOFF.md` / `DEBT.md`）已归档到
[`docs/archive/root/`](docs/archive/root/)，冻结于 2026-10-23，只作证词。
决策见 [`DECISIONS.md`](DECISIONS.md)；阶段计划见 [`PLAN.md`](PLAN.md)
（2026-10-10 快照，不是当前状态）。

主定理的实时债务图仍然是一条命令：

```lean
#print axioms Kepler.the_kepler_conjecture_e2e
```

## 参考资料

- T. Hales,《Dense Sphere Packings: A Blueprint for Formal Proofs》, Cambridge, 2012
- T. Hales et al.,《A Formal Proof of the Kepler Conjecture》, Forum of Mathematics, Pi, 2017
- T. Hales,《Some algorithms arising in the proof of the Kepler conjecture》, arXiv:math/0205209
- Flyspeck：`flyspeck/flyspeck`、`flyspeck/kepler98`；mathlib4：`leanprover-community/mathlib4`
- 工具：plantri/nauty、SoPlex、QSopt_ex、VIPR、dReal、Arb/FLINT

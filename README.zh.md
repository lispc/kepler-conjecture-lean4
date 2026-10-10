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
- **诚实记账**：sorry 必须带 `-- NEEDS` 注记；债务账本（`DEBT.md`）与端到端
  定理的实时公理面是客观进度刻度。不可复现的证据一律降级，不保留。

## 仓库结构

```
kepler-conjecture-lean4/
├── README.md / README.zh.md
├── PLAN.md                 # 权威计划 + 当前战略
├── STATUS.md               # 实时进度看板（每批次刷新）
├── DEBT.md                 # sorry 债务账本（脚本生成）
├── DECISIONS.md            # 决策日志
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
└── docs/                   # 根层 = 常住参考；
    ├── scouts/             #   侦察报告（写完即归档）
    ├── handoffs/           #   lane 交接与班次日志
    ├── projects/           #   专项设计与路线图
    ├── assets/             #   产物/草稿/探针日志
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

## 当前状态（2026-10-10）

| Phase | 内容 | 状态 |
|---|---|---|
| 1 | 定理陈述 | ✅ 完成（占位 sorry 待终版退役） |
| 2 | tame 平面图枚举 | ✅ 19,715 图 + 完备性证书，内核验证 |
| 3 | 线性规划 | ✅ 43,078 终端 LP 内核验证（重跑产物待补，见 PLAN §5） |
| 4 | 非线性不等式 | 🟡 求解层 68/176 可信闭合，内核 8 案；重计算挂起 |
| 5 | 文字证明移植 | 🟡 hypermap/fan/topology/planarity/Conforming/polyhedron 收官；packing+local 骨架 100%，滚动批次填证中 |
| 6 | 集成与交付 | 🟡 端到端对象 `the_kepler_conjecture_e2e` 已立；余 3 个冻结接口 sorry + 终版去重 |

权威的实时信息源：`STATUS.md`（看板）、`DEBT.md`（债务账本）、`PLAN.md`
（计划与战略）、`DECISIONS.md`（决策日志）。主定理的实时债务图：

```lean
#print axioms Kepler.the_kepler_conjecture_e2e
```

## 参考资料

- T. Hales,《Dense Sphere Packings: A Blueprint for Formal Proofs》, Cambridge, 2012
- T. Hales et al.,《A Formal Proof of the Kepler Conjecture》, Forum of Mathematics, Pi, 2017
- T. Hales,《Some algorithms arising in the proof of the Kepler conjecture》, arXiv:math/0205209
- Flyspeck：`flyspeck/flyspeck`、`flyspeck/kepler98`；mathlib4：`leanprover-community/mathlib4`
- 工具：plantri/nauty、SoPlex、QSopt_ex、VIPR、dReal、Arb/FLINT

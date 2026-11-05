# certtm-root — CertTM hull 栈候选根归档（lane certtm-root-w1，2026-11-03）

> 归档性质：**候选根登记 + NO-GO 边勘定记录**（W2 禁造边裁决）。基线
> HEAD `0c445f94`（certtm-mat-scout 交付笔）；侦察正本
> `lane_snapshots/certtm-mat-scout/`（GO 判决 + 618 解剖），本册 = 落地波
> `certtm-root-w1` 的 W1 登记 + W2 勘边结论。源 .lean 文件零改动。

## 0. 状态一行

`Kepler.Interval.CertTM` hull 栈 = **引擎完备、待接整车**：618 孤儿健全
（岛闭包 fresh 646 / direct-sorry 0 / Kepler axiom 0，公理面标准三），但
**e2e 锥内零 proof-term 消费边**——CertG 只消费经典核 `checkPosTM_sound`
（锥内既有），hull/L 层全栈对锥内任何陈述无数学锚。接线等 TM3/549 量产波
或 Mono* 进 universe；届时按下表 designate，勘边成本已付清。

## 1. 候选根表（锥实测，官方仪器 e2e_reach_map.lean REACH_ROOT 口径）

| 根 | 形状 | 锚（CertTM.lean） | K_REACH | K_SORRIED | K_AXIOM | fresh 增量（island WIRE 口径） | `#print axioms`（HEAD `0c445f94` 复验） |
|---|---|---|---:|---:|---:|---:|---|
| **R1** `Kepler.Interval.checkPosTMHullL_sound` | thm（L 层 let-table checker 顶层 soundness） | :4949 | 483（8 模块） | 0 | 0 | **+76**（CertTM 68 + Expr 8） | 标准三 |
| **R2** `Kepler.Interval.exA_straddle_end_to_end` | thm（atn2 层 D2A 栈 Real 端到端 demo） | :5628 | 462（8 模块） | 0 | 0 | **+55**（CertTM 53 + Expr 2） | 标准三 |
| **R3** `Kepler.Interval.checkPosTMHull_sound` | thm（549 驱动入口 checker soundness） | :4105 | 430（8 模块） | 0 | 0 | +≤24（簇大半 ⊆ R1） | 标准三 |

- R1 簇 ∈ L 栈、R2 簇 ∈ D2A 栈：**R1+R2 组合精确实测 +110**（双种子 BFS
  对同一 e2e 锥；R1 独占 76 + R2 独占 55 − 两簇重叠 21；`UNION_SORRY 0 /
  UNION_AXIOMS 0`）。 scout 交付的「+121（±4）」为两增量求和的未扣重叠
  估算，本册以精确数修正。全岛闭包上限 fresh = 646（618 孤儿 + 28 邻接
  Kepler 件）。
- 接线**不新增**非标公理：三根 K_AXIOM = 0，K_AXIOM 624 护栏 / K_SORRIED
  面零扰动预期（岛闭包 sorryFresh = 0）。
- 618 构成（侦察交付口径，HEAD 复测逐位一致）：418 机械伴生件（无消费者，
  designate 不会带入）+ 156 手写理论层 + 44 demo。根 designate 只能转正
  NAMED+demo ≈ 200 件里的出口可达部分。

## 2. W2 勘边记录（2026-11-03，lane certtm-root-w1）——NO-GO

按优先序勘定的两类候选消费点，均不成立：

| # | 候选锚 | 勘定结果 | 证据 |
|---|---|---|---|
| P1 | CertG docstring/HOL 锚声明依赖 TM hull 检查器健全性（`checkPosTMHull_sound`/`checkPosTMHullL_sound`） | **不成立** | CertG.lean 全文 685 行零 `checkPosTMHull*`/`evalTMHull*`/`checkPosTMH*` 引用；其 TM 义务唯一形态 = `BBTreeG.taylorLeaf` 的 `covers_point` 一支调用 `checkPosTM_sound`（CertG.lean:81；定理本体 CertTM.lean:4019，**已在锥内**）。taylorLeaf 叶证明项 `exGTM_cert := by decide` 不引 soundness → CertG proof-term 只拉入经典核（岛 INTREE=114 的构成），不拉 hull 栈 |
| P2 | Assembly/CertG 链上其他数学上该引用 TM soundness 的点 | **不成立（当前宇宙）** | ① `Kepler.lean` 根模块只 import `Cert`/`CertDisj`（零 CertTM）；② 锥内在库证书叶形全为裸区间 `checkPos`：C3397113841 / CFWGKMBZ / CQITNPEAx3725403817（A2 shards `(.leaf … (by decide +kernel))`，全 2,775 文件零 `taylorLeaf`）/ C6096597438b（BBTreeGD）；③ hull 栈的正当数学消费者 `MonoCorner.checkMonoCorner`（:776）/ `MonoTree.monoTree_sound`（:256）与全部 C549* hull 证书模块（C549HullPilot/C549StraddleBatch*/C549ProdK* 等，native_decide 豁免族除外）**全在 universe 外**（import 闭包零入口：MonoCorner ← MonoTree ← 无；C549* ← 无 Assembly 消费）；④ `C5490182221_pos` 主证不在库（构建至 784/6321 后暂停，STATUS.md）；⑤ §2a/4'/6' 注册表槽位（`nliLpIneqsIds` 等）全 `sorry` 等证书，无 hull 形陈述 |

grep 面（`checkPosTMHull`/`TMHull`/`evalTMHull`/`replay`）：锥内命中仅
CertTM 本体 + CertG 的经典核路径 + 案例模块 import 行；`replay` 命中仅在
HOL/trust-audit 文档（LP shard 抽样 replay，非 TM）。

## 3. 重锚条件（修复工单——何时本册可直接 GO）

合法消费边出现的两条路线（任一落地即按 §1 表 designate R1/R2/R3）：

1. **TM3 量产波**（设计正本 `pipeline/interval/taylor-model-design.md` §4
   行 TM3）：emit_lean schema v3 的 `taylorLeaf`/hull 叶量产进锥内证书模块
   （CertG/GD taylorLeaf 量产或 549 主证 `C5490182221` 落库进 Assembly 消费
   面）→ 叶 proof-term 将真实引用 `checkPosTMHull*` 族，hull 栈随波入锥
   （R3 优先；届时多数孤儿的转正走「机械层解冻」路径而非本册 designate）。
2. **Mono* 进 universe**：`MonoCorner`/`MonoTree`（`checkMonoCorner` /
   `monoTree_sound`，premises 形即 `checkPosTMHull` 成功）被任一锥内模块
   import 且 proof-term 消费 → R1 簇经 MonoCorner→CertTM 边入锥。

两条路线都不需要本册之外的额外勘边；本册根表与 fresh 实测（对基线 E 锥
`C_e2e`，K_REACH 2,079,707）可直接复用，唯 olean 推进后需按当时锥重测差值。

## 4. W1 复测记录（lane certtm-root-w1，HEAD `0c445f94`）

- 岛仪器 `certtm_island.lean`（侦察交付原样）复跑：census 732 /
  INTREE 114 / ORPHAN 618 / ISLAND_TOTAL freshKepler=646 sorryFresh=0
  axiomsKepler=0 —— 与侦察交付逐位一致（`logs/island_rerun.out`）。
- 五探针 `#print axioms` 全标准三零 sorryAx：R1/R2/R3 +
  `exGTM_end_to_end` + `checkPosTM_sound`（`logs/probe_axioms.out`）。
- REACH_ROOT 单根地图 R1/R2（基线 E 锥上复验）：K_REACH 483 / 462，
  SORRIED/AXIOM 段空（`logs/reachmap_r1.out` / `reachmap_r2.out`）。
- 双种子精确 union（`logs/union_r1r2.out`）：`UNION_R1_R2 110`
  （r1only 76 + r2only 55，overlap 21）、`UNION_SORRY 0`、
  `UNION_AXIOMS 0`。
- 注：以上复测在 `0c445f94` 共享 oleans 上完成；后续 docs-only 提交
  （如 `aafb4d83`）零 .lean 变化，读数不漂移。

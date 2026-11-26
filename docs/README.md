# docs/ — 文档地图

> 规则：**当前 / 历史 / 归档** 三层分离。当前状态只有一个出处（`priority-queue.md`），
> 历史只搬不删，归档件是只读证词。路径一律用仓库根相对路径。
> 指标不手抄：数字要么带 commit + 日期实测，要么标 stale。

## 我想查什么？

### 当前进度 / 下一步

- **[`priority-queue.md`](priority-queue.md)** — 唯一 operational 账本：
  里程碑对表（§0）、在飞车道（§1）、排队与工单（§2–§6）、最近日志（§8）。
  2026-11-18 重组前全文（含 J/Text 旧排产与续990–1242）在
  [`archive/priority-queue-2026-11-18-pre-nli-math.md`](archive/priority-queue-2026-11-18-pre-nli-math.md)；
  续306–续989 在 [`history/changelog-archive-2.md`](history/changelog-archive-2.md)，
  续1–续344 在 [`history/changelog-archive.md`](history/changelog-archive.md)。
  更早队列/战术/J 战役表在
  [`archive/priority-queue-legacy-2026-10.md`](archive/priority-queue-legacy-2026-10.md)。
- [`history/lanes-landed.md`](history/lanes-landed.md) — 已完成车道总表。
- [`handoff-2026-11-26.md`](handoff-2026-11-26.md) — **2026-11-26 交接（换 agent 用）**
  （wt1 已闭 + B 落库；A/L3 1 箱探针在飞；用户三线计划 wt1/wt0/QITNPEA 的入口/边界/
  第一动作；census 修复与干净 checkout 先 `make gen-wt1`；PR-66）。
- [`handoff-2026-11-20.md`](handoff-2026-11-20.md) — **2026-11-20 交接（换 agent 用）**
  （额度停车道令 [1310] 重置 11-23；W1 增量2 待闸 / 三探针批断点 + 孤儿进程 /
  池链 v5 链尾三件套 / 裁决存量 / 今日普查两勘误与 kit 裁决）。
- [`handoff-2026-11-18.md`](handoff-2026-11-18.md) — **2026-11-18 交接（换 agent 用）**
  （基线 AQ / TSKAJXY 装配落地 / SF 111 / farm-ops 排产 / 复现命令与易失池风险 / 待裁决 4 项）。
- [`handoff-2026-11-17.md`](handoff-2026-11-17.md) — **2026-11-16/17 战役收获与现状交接**
  （Gate-0 NO-GO→实测复测、math5 四代接力、ZTGIJCF4 dihY 收口+γ4 侦察 GO、
  ixpotpa 负结果、文档重组、排产队列）。
- [`handoff-2026-11-16.md`](handoff-2026-11-16.md) — **2026-11-15/16 两日收获总览**
  （TSKAJXY 全盒战役、CertTM2 引擎路线、ox3q1h/ZTGIJCF4/recost/audit 判词、排产队列）。
- 历次 session 交接：[`handoff-2026-11-06.md`](handoff-2026-11-06.md)（裁决/死路/环境坑正本）、
  [`handoff-2026-11-12.md`](handoff-2026-11-12.md)、
  [`handoff-2026-11-13.md`](handoff-2026-11-13.md)、
  [`handoff-2026-11-14.md`](handoff-2026-11-14.md)（OCBICBY 移交）。
- [`nli-campaign.md`](nli-campaign.md) — nli* 非线性债路线图/结论（分诊、已闭件、
  负结果、下一步；实时数字仍以 pq 为准）。
- [`wt1-campaign.md`](wt1-campaign.md) — **wt1 战役档案**（`nliCell3QZECFICwt1`
  已关闭：四层形态、R0–R12 历程、成本与 PARITY（原 18.28× → L1 实测 6.30×，
  用户明批 B）、11 条勘误、给未来战役的 10 条经验与复用清单；2026-11-26）。
- [`../strategy/nli-next-phase-20261123b.md`](../strategy/nli-next-phase-20261123b.md) —
  **NLI 下一阶段：共享机件层 + 分层收口**（2026-11-23 下午版，以此为准：
  原版 5 类机件考古、`NliKit` 三包 P-A/P-B/P-C、M1–M4、短期 S1–S10）。
- [`../strategy/nli-strategy-20261123.md`](../strategy/nli-strategy-20261123.md) —
  **NLI 战略复盘与 1–2 周车道规划**（2026-11-23 上午版：49 件分档 1/15/27/1/2/3；
  主线根面恢复→wt1→ZTG trio；5 个方向与池混世界约束。三处前提已被下午实测修正，
  见下一阶段文档 §1）。
- [`certshard-code-shape.md`](certshard-code-shape.md) — **CertShards 重片同语义代码写法**
  （2026-11-21 `certshard-code-shape-w1`：99.9% 时间在 IR 解释器；C1+C2+C3
  Pent 1.237×/Quad 1.205×/HexR 1.298×（含 C4）；全部 DEF-FIX，未施工；
  含 C4–C9 负结果与 Hex 首测）。
- [`shard-math-roadmap.md`](shard-math-roadmap.md) — **编译量压缩路线（数学/算法层）**：
  notame7 native、585 合并、Interval P3、通用 Bernstein 定理；含“不要再试”清单
  （2026-11-21 `shard-math-research-w1`，数字出处见 pq 续1367 与同名快照）。
- [`history/nli-six-lanes-2026-11-18.md`](history/nli-six-lanes-2026-11-18.md) —
  **2026-11-18 六车道总结**：实测加速、失败边界、Lean 资产与下一步（历史总结）。
- [`DECISIONS.md`](../DECISIONS.md) — 用户裁决与长期政策（根级唯一 current 文档）。
- [`PLAN.md`](../PLAN.md) — 项目目标、锁定决策、阶段定义（**2026-10-10 计划快照，
  不是当前状态**）。

### 债在哪

- **现役**：`priority-queue.md` 文件头（基线 AQ：SORRIED 51 = 50 `nli*` + 1 hLP；
  wt2A 小模块验收后 2026-11-20 为 49 = 48 `nli*` + 1 hLP；**wt1 全量证书闭合后
  2026-11-26 `4bcbd7ad` 为 48 = 47 `nli*` + 1 hLP**；Text 0、AXIOM 585）+
  [`trust-base.md`](trust-base.md)（信任基座依据与逐类对照）+
  [`e2e-reachability-map.md`](e2e-reachability-map.md)（逐基线 SORRIED/AXIOM 清单，
  tsv 为仪器原样输出）。
- [`archive/scouts/axiom-ledger-2026-10-28.md`](archive/scouts/axiom-ledger-2026-10-28.md) —
  逐声明 axiom 台账（**点时快照 2026-10-28**，151-SORRIED/624-axiom 时代；已归档）。
- [`archive/scouts/main-theorem-trust-audit-2026-10-22.md`](archive/scouts/main-theorem-trust-audit-2026-10-22.md) —
  主定理锥结构、弱形/替身风险审计（历史，2026-10-22）。
- [`archive/scouts/debt-ledger-w1.md`](archive/scouts/debt-ledger-w1.md) —
  SORRIED 134 逐条 7 列挂账（历史；**塔群表已过期**，见文件头注）。
- [`statement-fix-proposals.md`](statement-fix-proposals.md) — SF 通道提案账本
  （顶部有编号索引；正文 6,121 行，拆分延后）。

### 数学架构 / 陈述保真

- [`architecture.md`](architecture.md) — 证书格式、流水线、信任模型。
- [`statement-fidelity.md`](statement-fidelity.md) — 与 Flyspeck
  `the_kepler_conjecture` 的逐条对照。
- [`module-map.md`](module-map.md) / [`local-manifest.md`](local-manifest.md) /
  [`packing-manifest.md`](packing-manifest.md) — 章节 → 模块映射与移植清单。
- [`phase6-spine.md`](phase6-spine.md) — 装配脊柱设计与 M5′ 历史路线。

### 可达图 / 可视化

- [`e2e-reachability-map.md`](e2e-reachability-map.md) — cone 可达图 + 指标定义
  + 历史基线 A–M。
- [`global-reachability-map.md`](global-reachability-map.md) — union 多根快照。
- [`e2e-tree-visualization.md`](e2e-tree-visualization.md) — 本地树页面数据口径与重建。
- [`e2e-reachability-map.tsv`](e2e-reachability-map.tsv) — 生成物；
  **当前 = 基线 AQ @`e4c384e6`（2026-11-18：K_REACH 2,108,657 / SORRIED 51 /
  AXIOM 585；Text 0）**，与 `docs/priority-queue.md` 文件头同口径；
  历史基线叙事看 md 的对应节。

### 怎么跑闸 / 怎么开工

- **[`tools.md`](tools.md)** — 工具总入口：当前 NLI/Text 源图、HOL 单根 instrument、
  受 guard 的单模块编译与复制式岛、`#print axioms`、precompile/dylib、trust manifest、
  检索/补丁/哈希工具，以及已停止 olean 恢复链的交接位置。
- [`compile-speed.md`](compile-speed.md) — **编译速度活文档：现状、族级成本、优化与实验台账**
  （2026-11-21 基线：import 固定费、分层归因、`-j2`、import kit、按内存排槽；
  2026-11-22/23 `precompile` 三族 **580/580**、7.184 h、13.889×，未接入正式构建；
  2026-11-26 增补：闭包 9,137 的族级成本普查（TskXLLIPLS ~55 h、W1DC L1 3.73 h、
  Shard/Hull/TopReplay/LocalAuto 等）、W1DC L1 成功、TskXLLIPLS M1 失败
  （15.3 s 地板、4.5× HOL、`BUDGET_EXHAUSTED`）、4.36 全量重放预算，以及
  “为什么是 6,612 叶而不是几个”（HOL 7,763 单元对照）。
- [`fill-worker-playbook.md`](fill-worker-playbook.md) — 工人纪律、闸规则、雷区表。
- [`lane-brief-template.md`](lane-brief-template.md) — 工单模板（§0 硬约束逐字复制）。
- [`../lean/scripts/auto_gate.sh`](../lean/scripts/auto_gate.sh) — 五道机械闸；
  SF 闸按路径读 `statement-fix-proposals.md`，**不要移动该文件**。
- [`def-fix-charters/`](def-fix-charters/) — 执行章程（当前：`sf99/` DEF-FIX 围栏）。

### 历史 / 死档

- [`archive/README.md`](archive/README.md) — 归档索引：仍被当前文档引用的
  scout / runbook 一页。
- `archive/scouts/`（56）/ `archive/handoffs/`（18）/ `archive/projects/`（21）/
  `archive/lane-archives/`（8）— 只读；内部旧链接不回溯修复。
- `archive/root/` — `STATUS.md` / `HANDOFF.md` / `DEBT.md` 的根级历史副本，
  冻结于 2026-10-23。
- [`scouts/`](scouts/) — 只剩**机器可读数据表**（14 个 TSV，见其 README）；
  侦察报告已全部归档。
- [`assets/`](assets/) — 产物、探针日志、草稿（不在文档索引内逐件登记）。

## 维护规则（三条）

1. **一笔落库 = 一条日志**：只在 `priority-queue.md` §8 追加（新→旧）；§8 超过窗口
   （当前约 20 条）时机械迁入 `history/` 或带日期的 `archive/` 快照，原文不改。
   2026-11-26 迁出窗口在 `history/changelog-archive-3.md`；更早依次见
   `history/changelog-archive-2.md`、`history/changelog-archive.md`。
2. **数字只引用不抄**：同一指标不允许多个文档各写一份；引用时带
   `（实测 <commit>，<日期>）` 或标 `stale`。
3. **历史只搬不删**：`archive/` 与 `history/` 只增不改；需要纠正时加 `ERRATA` 行，
   不覆写原文。

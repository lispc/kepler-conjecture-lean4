# docs/ — 文档地图

> 规则：**当前 / 历史 / 归档** 三层分离。当前状态只有一个出处（`priority-queue.md`），
> 历史只搬不删，归档件是只读证词。路径一律用仓库根相对路径。
> 指标不手抄：数字要么带 commit + 日期实测，要么标 stale。

## 我想查什么？

### 当前进度 / 下一步

- **[`priority-queue.md`](priority-queue.md)** — 唯一 operational 账本：
  里程碑对表（§0）、在飞车道（§1）、排队与工单（§2–§6）、最近日志（§8）。
  §8 只保留最近窗口（续990 起）；续306–续989 在
  [`history/changelog-archive-2.md`](history/changelog-archive-2.md)，续1–续344 在
  [`history/changelog-archive.md`](history/changelog-archive.md)。旧队列/战术/J 战役表在
  [`archive/priority-queue-legacy-2026-10.md`](archive/priority-queue-legacy-2026-10.md)。
- [`history/lanes-landed.md`](history/lanes-landed.md) — 已完成车道总表。
- [`DECISIONS.md`](../DECISIONS.md) — 用户裁决与长期政策（根级唯一 current 文档）。
- [`PLAN.md`](../PLAN.md) — 项目目标、锁定决策、阶段定义（**2026-10-10 计划快照，
  不是当前状态**）。

### 债在哪

- [`axiom-ledger.md`](axiom-ledger.md) — 逐声明 axiom / sorryAx / 标准三状态。
- [`main-theorem-trust-audit.md`](main-theorem-trust-audit.md) — 主定理锥结构、
  弱形 / 替身风险（历史审计，2026-10-22）。
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
  **当前 = 基线 T（2026-11-09：2,088,969 / SORRIED 78 / AXIOM 585）**，
  与 `docs/priority-queue.md` 文件头同口径；历史基线叙事看 md 的对应节。

### 怎么跑闸 / 怎么开工

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
   （当前约 20 条）时移入 `history/changelog-archive-2.md`（按续号升序），原文不改；
   续1–续344 的旧档在 `history/changelog-archive.md`。
2. **数字只引用不抄**：同一指标不允许多个文档各写一份；引用时带
   `（实测 <commit>，<日期>）` 或标 `stale`。
3. **历史只搬不删**：`archive/` 与 `history/` 只增不改；需要纠正时加 `ERRATA` 行，
   不覆写原文。

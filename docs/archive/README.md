# docs/archive — 历史归档索引

> **性质**：本目录下的内容都是**历史记录**，不再维护、不随 HEAD 更新。
> 数字、行号、commit 均停在写作时点；引用它们时请当作「当时的证词」，不要当当前状态。
> **政策**：归档内部的历史引用不回溯修复；只有**当前文档**（本目录之外）指向归档的链接会被维护。
>
> 归档动作：2026-11-05（`docs-audit-w1` 审计 + 用户批准），纯 `git mv`，文件内容逐字节未变。
> 当前状态请回 [`../priority-queue.md`](../priority-queue.md) 与 [`../README.md`](../README.md)。

## 目录

| 目录 | 内容 | 件数 |
|---|---|---|
| `scouts/` | 一次性侦察报告（覆盖测绘、可行性、翻案） | 56 |
| `handoffs/` | 车道交接单（含 549 系列长日志） | 18 |
| `projects/` | 专项计划与裁决批次（含其自身的 `archive/`） | 21 |
| `lane-archives/` | 已结车道的正式归档（DELIVERY/Evidence/README） | 8 |
| `maps/` | 旧版地图快照（`e2e-debt-map-2026-09-29.md`） | 1 |
| `design/` | 已过时的设计文档（`hard-cases.md`） | 1 |
| `templates/` | 旧版工单模板（`phase5-worker-template.md`） | 1 |

## 仍被当前文档引用的归档件

下列文件虽然归档，但**当前文档仍然指向它们**（引用已随迁移改写为 `docs/archive/...`）。
按用途分组，方便从入口直接跳转。

### 债与可达性（最常被引用）

- `scouts/debt-ledger-w1.md` — 全库证书债/证明债总账本（SORRIED 134 逐条 7 列挂账）。
  **注意：其中的塔群表已过期**（写作时五塔 170 件；2026-11-05 实测五塔 8 件 / 八塔 31 件）。
- `scouts/orphan-scout.md` — ORPHANS 量级口径与上行空间测算。
- `scouts/tiwwfyq-coverage-scout.md` — 覆盖缺口 G1 等。
- `scouts/terminal11-scout.md` — terminal11 分账（20+87+2）。

### 车道设计与施工路线

- `scouts/lp-design-scout.md` — hLP 终端语义移植路线（W6-A/W6-B 的立项依据）。
- `scouts/grutoti-scout.md` — GRUTOTI 路线 (d) 的依据（§5.1 / §0.2）。
- `scouts/bola1-registry-scout.md` — LA1 注册表 98 项对齐测绘（62 WIRE / 28 HOLD）。
- `scouts/la1-localfan-scout.md` — LA1 `LocalFan` 弱编码实锤（SF-54/55/56 的立案依据）。
- `scouts/la2027-scout.md` — LA20/LA27 环与引擎。
- `scouts/contrafan-scout.md` — ContraFan 侧测绘。
- `scouts/ajripqn-scout.md` — AJRIPQN 分期侦察（§4 B1）。
- `scouts/nli-rest-scout.md` — nli rest 叶（§2.3）。
- `scouts/mqmsmab-scout.md` — 占位两类病分类（§6.1）。
- `scouts/encoding-risk-sweep.md` — 编码风险扫雷（C2-1 等）。
- `scouts/lean4-ecosystem-scout.md` — Lean 4 生态调研。

### 运行手册

- `scouts/EMISSION-RUNBOOK.md` — MISSING 证书发射侦察与直配通路（nli 农场）。

### 被 SF 提案引用的裁决存档

- `projects/archive/sf-decision-batch-2026-10-12.md` — SF 批次裁决正本（多项 `(f)` 状态指向它）。
- `projects/archive/planar-encoding-fix.md` — planar 编码定义纠正（§2 补丁）。
- `projects/archive/merge-ineq-channel.md` — 不等式通道合并章程。

## 找东西的建议

1. **先看当前状态**：`docs/priority-queue.md`（在飞 + 排队）与 `docs/README.md`（导航）。
2. **再查历史证据**：用文件名关键词在本目录 `grep -r`，不要从入口逐层点。
3. **引用归档件时写全路径**：`docs/archive/<来源>/<文件>`，并在句子里注明「（历史，时点 …）」。
4. **不要把新文档写进本目录**。归档门是单向的：新内容进 `docs/`，只有结项的历史件才搬进来。

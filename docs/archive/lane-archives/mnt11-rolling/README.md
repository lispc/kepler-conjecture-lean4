# `mnt11-rolling` — 常驻车道账本

常驻编制：`DECISIONS.md` 2026-11-06「mnt11 设常驻车道（用户指令）」——车道池 5 个名额中永久保留 1 个给
`main_nonlinear_terminal_v11`，按波滚动，不因单波收工而释放。

## 宪法摘要（每波继承）

1. **陈述冻结**：证明写在新文件（`Kepler/T11Proofs.lean`，或向 `Kepler/T11Glue.lean` 追加）；
   **不改** `Kepler/Text/LocalAuto1.lean` 的 109 条 `mainEstimate_*` 陈述。陈述修正只走 SF 通道，
   定义修正只走 DEF-FIX 通道。
2. **验收唯一语言**：`#print axioms` = `[propext, Classical.choice, Quot.sound]`。
   禁 `axiom` / `sorry` / `admit` / `native_decide` / 假定理 / 改陈述凑证。
3. **证书农场只登记不施工**：凡判 `NEEDS-CERT` 的不发射证书（本机禁重型计算）；只更新本账本。
4. **分诊口径**：`PROVED` 必须 `#print axioms` 实测；`PROVABLE` 必须在 `/tmp/mnt11-rolling*/` 探针
   RC=0（否则降级）；`NEEDS-CERT` 必须点名 `Interval.Cases.C*` 并核实 olean 存否；不确定写 UNRESOLVED。
5. **账本只增不改**：本目录 `TRIAGE.tsv` 是逐条状态账；纠错追加 `ERRATA` 行/节，不覆写历史。
6. 单件 >450 行或 3 轮结构性卡死 ⇒ 止损交班（`AGENTS.md` §7）。

## 每波日志

| 波 | 日期 | HEAD | 范围 | 结果 | 产物 | 备注 |
|---|---|---|---|---|---|---|
| M0 | 2026-11-05 | `7e5ed1c1` | 109 条全量分诊（只读；不施工） | PROVED 20 / PROVABLE 1 / NEEDS-CERT 88 / NEEDS-MATH 0；剩余人工行 2,590–4,840 | `TRIAGE.tsv`（本目录）、`~/c17_backup/lane_snapshots/mnt11-rolling-M0/`（SUMMARY/WORKORDER-M1/EVIDENCE/conclusions/logs） | T11Glue 岛协议 RC=0（30.91 s，20/20 标准三）；`6843920790` 探针 RC=0；其余 88 条等证书农场 |

## 状态字段

`PROVED` / `PROVABLE` / `NEEDS-CERT` / `NEEDS-MATH`，判定依据见 `TRIAGE.tsv` 各行的
`certified_in` / `provable_by` / `notes` 与母交付的 `EVIDENCE.md`。

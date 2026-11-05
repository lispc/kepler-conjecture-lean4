# lane-archives — 未落库车道工件归档

**为什么存在**：2026-11-03 用户拍板「树越大越好」后，仍然会有车道交付了有价值但暂不落库的工件
（例如 F1 的 PA25 rewire、条件形分段件）。这些工件若只放在 `~/c17_backup/lane_snapshots/`，
不在 git 里，会腐烂甚至丢失。本目录是它们的**入库归档位**。

## 约定

- 每个车道一个目录：`docs/lane-archives/<lane-name>/`。
- 必放入：
  - `kit-<lane>.diff`（对已知 HEAD 可 `git apply --check` 的补丁）；
  - `DELIVERY.md`（闭合件表 / 残件缺口 / 搬债审计 / 下波工单）；
  - `Evidence.md`（`#print axioms` 原文 / RC / error / sorry 计数）。
- **不放** `Work.lean`（可由 `kit + HEAD` 重建；避免大文件入库）。
- 目录内 `README.md` 写一行：基线 HEAD、为什么不落库、消费条件（什么之后可以落）、
  以及对应的 queue §8 条目号。
- 落库后：把该目录标记为 `已消费`（或删除），并在 queue §8 记录。

## 与 snapshots 的关系

`~/c17_backup/lane_snapshots/<lane>/` 仍是车道的原始工作区；本目录只保存
“要长期记住的最小工件集”。两者内容应一致；以本目录为准（它在 git 里）。

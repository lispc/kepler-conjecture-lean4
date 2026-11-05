# la11-mksimplex-cont-w1 — 归档说明

- **基线 HEAD**：`b89ee8b45bc9ecbe197dd9e0551423326a9e8873`（`b89ee8b4`）。
- **为什么不落库**：本车道的硬约束是「主仓 tracked 零改动」，故代码只以 kit 形式交付，
  由编排者在 `b89ee8b4`（或 rebase 后的 HEAD）上 apply。kit 本身是**已完成品**（2/2 件真证、
  整文件 RC=0 / 0 error），不是半成品。
- **消费条件**：`git apply kit-la11-mksimplex-cont-w1.diff` 于 `b89ee8b4` 时
  `git apply --check` PASS（本车道已实测）；apply 后跑一次 standalone 整文件复核
  （期望 RC=0 / 0 error / `declaration uses sorry` 24→22），再跑 e2e 仪器确认
  `K_SORRIED` −1（锥内 `PQCSXWG2_WITHINREAL_p11` 断根，连带 `PQCSXWG2_ATREAL_p11` /
  `PQCSXWG2_p11` 的 `sorryAx` 一并消失）。
- **queue §8 条目号**：`docs/priority-queue.md` §1 在飞行 `la11-mksimplex-cont-w1`；
  §8 变更日志对应条目 = **2026-11-05（23:55，续365）** 的「④ 补位」。
- **不入库**：`Work.lean`（可由 `kit + HEAD` 重建）。
- **本目录内容**：`kit-la11-mksimplex-cont-w1.diff`、`DELIVERY.md`、`Evidence.md`、
  `RECON.md`（侦察结论 + Mathlib API 踩坑记录）、本 `README.md`。

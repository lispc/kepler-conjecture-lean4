# pa25-rolling-w4 — 归档说明

- **基线 HEAD**：`4ab6a8e7`（PA25 `14,393` 行 / 25 裸 `sorry` / 26 编译器 sorry 警告，
  MD5 `ca2eaedb3d421951635dd07119dbde9e`）。
- **本波闭合 3 件**：`gamma4fgcy_POS`、`cc_prep_model_data`（锥内）、`EDGE_IMP_K23`；
  own-sorry 25 → 22，编译器 sorry 警告 26 → 23，整文件 standalone RC=0 / 0 error。
- **为什么不直接改主仓**：本车道硬约束是「主仓 tracked 零改动」，代码以 kit 形式交付，
  由编排者在 `4ab6a8e7`（或 rebase 后的 HEAD）上 apply。kit 是**已完成品**
  （3/3 件真证、整文件 RC=0），不是半成品。
- **消费条件**：`git apply kit-pa25-rolling-w4.diff` 于 `4ab6a8e7` 时
  `git apply --check` PASS（本车道已实测）；apply 后跑一次 standalone 整文件复核
  （期望 RC=0 / 0 error / `declaration uses sorry` 26→23），再跑 e2e 仪器确认
  `K_SORRIED` −1（锥内 `cc_prep_model_data` 断根）。
- **不入库**：`Work.lean`（可由 `kit + HEAD` 重建；MD5 `2fe12c2150f5aee916d5fd89efda08ca`）。
- **本目录内容**：`kit-pa25-rolling-w4.diff`、`DELIVERY.md`、`Evidence.md`、本 `README.md`。

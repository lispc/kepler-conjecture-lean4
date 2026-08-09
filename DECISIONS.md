# DECISIONS.md — 决策日志

> 依据 PLAN.md §2：任何偏离已锁定决策的变更必须先在此记录理由并向人类汇报。
> 新条目追加在顶部（倒序）。

## 2026-08-09 — 初始化：确认 PLAN.md §2 全部锁定决策

- 证明助手：Lean 4 + Mathlib。toolchain 锁定 `leanprover/lean4:v4.32.2`（elan），
  Mathlib 锁定 tag `v4.32.2`（见 `lean/lean-toolchain` 与 `lean/lakefile.toml`）。
- 计算信任模型：证书化计算；`native_decide` 项目内禁用。
- 证明蓝图：Hales《Dense Sphere Packings》(Cambridge, 2012)。
- 图枚举：plantri/nauty 生成 + 完备性证书 + Lean checker。
- LP：SoPlex exact / QSopt_ex 有理精确求解 + VIPR 证书；HiGHS 仅交叉验证。
- 非线性：dReal 优先，Arb 球算术分支定界兜底。
- 硬件：本机（128 核 / 1 TB RAM）。
- 参考库只读克隆于 `reference/`，commit hash 记入 `reference/LOCK.md`。

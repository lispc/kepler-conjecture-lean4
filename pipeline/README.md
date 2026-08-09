# pipeline/

不受信任的生成器与求解器封装（plantri/nauty、SoPlex/QSopt_ex、dReal、Arb）。

纪律（PLAN.md §6.2）：本目录下的一切输出都必须经 Lean checker 核验后
才允许被证明引用；本目录代码本身不属于可信基。

版本锁定方式（nix 或 docker）待 Phase -1 收尾时确定并记录于 DECISIONS.md。

## 目录规划

- `graphs/`  plantri/nauty 封装 + 枚举树证书导出
- `lp/`      LP 生成器 + SoPlex/QSopt_ex 调用 + VIPR 证书导出
- `nlin/`    dReal / Arb 驱动 + 区间剖分证书导出

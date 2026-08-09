# reference/LOCK.md — 只读参考库锁定

克隆日期：2026-08-09。均为 `--depth 1` 浅克隆，只读使用，禁止修改。

| 仓库 | 路径 | commit hash | 用途 |
|---|---|---|---|
| flyspeck/flyspeck | `reference/flyspeck` | `1ce0353008eba83d3c76ae9a25c3c242e4802d53` | Flyspeck 形式化库（HOL Light/Isabelle），定理陈述与证明对照 |
| flyspeck/kepler98 | `reference/kepler98` | `90350ab8b897a577c16cff2bd72643b3f9e32227` | 1998 原始代码与数据（图 Archive、LP 数据等的来源索引） |

## 关键文件索引（Phase 1/2 会用到）

- Flyspeck 主定理陈述：`reference/flyspeck/text_formalization/general/the_kepler_conjecture.hl`（由 `load_flyspeck.ml:42` 载入）
- tame 图 Archive：`reference/flyspeck/formal_graph/archive/`（`string_archive.txt` 等；以仓库文件为准，不硬编码数量）
- 非线性不等式：`reference/flyspeck/text_formalization/nonlinear/`
- LP 相关：`reference/flyspeck/formal_lp/`

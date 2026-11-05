# docs/scouts — 机器可读数据表

> 本目录**只放数据**（`.tsv`）。所有侦察**报告**（`.md`）已于 2026-11-05 归档到
> [`../archive/scouts/`](../archive/scouts/)（56 件），索引见
> [`../archive/README.md`](../archive/README.md)。
>
> 这里的 TSV 是**仍在使用的仪器输出/账本**，被当前文档直接引用；
> 它们不是历史证词，但也不是自动生成的——改数请重跑对应脚本，不要手改。

| 文件 | 内容 | 生成/来源 |
|---|---|---|
| `bola1-dep-map.tsv` | LA1 注册表 90 条 `_concl` 的依赖图（62 WIRE / 28 HOLD 分诊） | `bola1-registry-scout` |
| `direct-source-triage.tsv` | 直源全量分诊（A3/B27/C14/D0/E106/F0） | `triage-w1` |
| `fchkugt-dep-map.tsv` | FCHKUGT 族依赖图 | `fchkugt` 波 |
| `fidconf-triage.tsv` | 陈述保真冲突分诊 | `fidelity-v1` |
| `fidelity-audit-v1.tsv` / `-v2.tsv` | 陈述保真审计配对率（69.4% 等） | `fidelity-v1` / `-v2` |
| `grhidfa-dep-map.tsv` | GRHIDFA 族依赖图 | GRHIDFA 波 |
| `la2027-dep-map.tsv` | LA20/LA27 环与引擎映射 | `la2027-scout` |
| `lp-family-census.tsv` | 183 族 ↔ 127 `lpIneqsIds` 交集普查（交集 = 0） | `hlp-w6a` |
| `m1-ledger.tsv` | M1 全库 sorry 逐条账本 | `debt-ledger-w1` |
| `nli-rest-params.tsv` | 57 条 nli rest 的农场参数化模板（桥族 B1–B6） | `nli-glue-template-w1` |
| `terminal11-inventory.tsv` | terminal11 分账（20 + 87 + 2） | `terminal11-w1` |
| `w0-wire-inventory.tsv` | W0 接线盘点 | `w0` 波 |
| `wsewpch-dep-map.tsv` | WSEWPCH 族依赖图 | WSEWPCH 波 |

**维护规则**：新增 TSV 必须在本表登记一行（用途 + 生成来源）；不再被引用的表
随其报告一起移入 `../archive/scouts/`。

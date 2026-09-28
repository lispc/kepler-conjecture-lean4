# DEBT.md — sorry 债务账本

> 由 `lean/scripts/debt_ledger.py` 生成；勿手改。总计 **1951** 个 sorry。

| 区域 | sorry 数 | 涉及文件数 |
|---|---|---|
| Text | 1938 | 68 |
| (root) | 13 | 2 |
| **合计** | **1951** | **70** |

<details><summary>逐文件明细</summary>

| 文件 | sorry 数 |
|---|---|
| Text/PackingAuto25.lean | 144 |
| Text/LocalAuto5.lean | 114 |
| Text/LocalAuto1.lean | 91 |
| Text/LocalAuto22.lean | 84 |
| Text/PackingAuto18.lean | 71 |
| Text/LocalAuto32.lean | 69 |
| Text/LocalAuto24.lean | 65 |
| Text/LocalAuto28.lean | 63 |
| Text/LocalAuto34.lean | 60 |
| Text/LocalAuto6.lean | 60 |
| Text/PackingAuto22.lean | 53 |
| Text/LocalAuto38.lean | 50 |
| Text/PackingAuto2.lean | 49 |
| Text/PackingAuto7.lean | 48 |
| Text/LocalAuto23.lean | 42 |
| Text/LocalAuto13.lean | 40 |
| Text/LocalAuto14.lean | 40 |
| Text/PackingAuto4.lean | 39 |
| Text/PackingAuto21.lean | 37 |
| Text/LocalAuto11.lean | 36 |
| Text/LocalAuto2.lean | 35 |
| Text/LocalAuto4.lean | 35 |
| Text/LocalAuto9.lean | 35 |
| Text/LocalAuto7.lean | 34 |
| Text/LocalAuto19.lean | 30 |
| Text/LocalAuto21.lean | 30 |
| Text/LocalConcl.lean | 30 |
| Text/PackingAuto1.lean | 30 |
| Text/LocalAuto29.lean | 28 |
| Text/LocalAuto37.lean | 27 |
| Text/PackingAuto15.lean | 26 |
| Text/LocalAuto33.lean | 25 |
| Text/PackingAuto5.lean | 24 |
| Text/LocalAuto35.lean | 22 |
| Text/LocalAuto18.lean | 20 |
| Text/LocalAuto3.lean | 18 |
| Text/LocalAuto10.lean | 17 |
| Text/LocalAuto16.lean | 17 |
| Text/LocalAuto31.lean | 17 |
| Text/PackingAuto6.lean | 15 |
| Text/LocalAuto36.lean | 13 |
| Text/LocalAuto8.lean | 13 |
| Assembly.lean | 12 |
| Text/LocalAuto15.lean | 12 |
| Text/LocalAuto26.lean | 10 |
| Text/PackingConcl.lean | 10 |
| Text/PackingAuto3.lean | 9 |
| Text/LocalAuto17.lean | 8 |
| Text/LocalAuto27.lean | 8 |
| Text/PackingAuto10.lean | 8 |
| Text/PackingAuto12.lean | 8 |
| Text/LocalAuto20.lean | 7 |
| Text/TameLp.lean | 7 |
| Text/PackingAuto16.lean | 6 |
| Text/PackingAuto20.lean | 6 |
| Text/PackingAuto24.lean | 6 |
| Text/PackingAuto11.lean | 5 |
| Text/PackingAuto23.lean | 5 |
| Text/LocalAuto25.lean | 4 |
| Text/PackingAuto13.lean | 4 |
| Text/PackingAuto9.lean | 4 |
| Text/LocalAnchors.lean | 3 |
| Text/PackingAuto14.lean | 3 |
| Text/PackingAuto19.lean | 3 |
| Text/ContraFan.lean | 2 |
| Statement.lean | 1 |
| Text/LocalAuto12.lean | 1 |
| Text/LocalAuto30.lean | 1 |
| Text/LocalBridge.lean | 1 |
| Text/PackingAuto17.lean | 1 |

</details>

## 主定理可达债务（脊柱公理探针）

> **mac 移植状态（2026-09-28）**：探针（`spine_axioms.py`）信任缓存中的 Phase 2
> Graphs olean，本机从未构建（Graphs 证书链重建 = 重型计算，挂起待强机器），
> 故 Lean 级全闭包探针在本机**结构性不可用**；脚本已完成 mac 移植
> （`SPINE_CACHE_ROOT` 环境变量，`/home/scroll` 硬编码清除），Graphs olean
> 就位后即可复跑。下方保留旧服务器最后一次成功探针结果（2026-09-26，
> main @ 8a5d87ad）。
> **现行度量文件 = `docs/e2e-debt-map.md`（2026-09-28 结构性债务图，手工核对版）**
> ——M5′ 里程碑（`docs/phase6-spine.md` §6）的 lane 排序依据。

| 类别 | 公理 |
|---|---|
| sorry 占位（接口债务） | sorryAx |
| 特许 native_decide（DECISIONS.md 2026-08-10 scoped exception） | 624 个 shard 公理 / ofReduceBool 族 |
| 标准三公理 | Classical.choice, Quot.sound, propext |
| 其它（**异常，需排查**） | 无 |

2026-09-26 探针时的"剩三接口"口径已过期：`textCapstone` 已真化（现消费 PA25
`PACKING_CHAPTER_MAIN_CONCLUSION` sorry + Assembly §2c 接口占位 12 枚 + ContraFan
深几何双核；逐枚清单/分级/成本见 `docs/e2e-debt-map.md`）。

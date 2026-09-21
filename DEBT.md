# DEBT.md — sorry 债务账本

> 由 `lean/scripts/debt_ledger.py` 生成；勿手改。总计 **2063** 个 sorry。

| 区域 | sorry 数 | 涉及文件数 |
|---|---|---|
| Text | 2059 | 65 |
| (root) | 4 | 2 |
| **合计** | **2063** | **67** |

<details><summary>逐文件明细</summary>

| 文件 | sorry 数 |
|---|---|
| Text/PackingAuto25.lean | 162 |
| Text/LocalAuto5.lean | 134 |
| Text/PackingAuto22.lean | 95 |
| Text/PackingAuto18.lean | 94 |
| Text/LocalAuto1.lean | 91 |
| Text/LocalAuto22.lean | 84 |
| Text/LocalAuto32.lean | 69 |
| Text/LocalAuto38.lean | 66 |
| Text/LocalAuto28.lean | 63 |
| Text/LocalAuto24.lean | 61 |
| Text/LocalAuto34.lean | 60 |
| Text/LocalAuto6.lean | 60 |
| Text/PackingAuto4.lean | 59 |
| Text/PackingAuto2.lean | 52 |
| Text/PackingAuto7.lean | 48 |
| Text/LocalAuto23.lean | 42 |
| Text/LocalAuto13.lean | 40 |
| Text/LocalAuto14.lean | 40 |
| Text/LocalAuto4.lean | 40 |
| Text/PackingAuto21.lean | 37 |
| Text/LocalAuto11.lean | 36 |
| Text/LocalAuto2.lean | 35 |
| Text/LocalAuto9.lean | 35 |
| Text/LocalAuto7.lean | 34 |
| Text/LocalAuto19.lean | 30 |
| Text/LocalAuto21.lean | 30 |
| Text/PackingAuto1.lean | 30 |
| Text/LocalAuto29.lean | 28 |
| Text/LocalAuto36.lean | 27 |
| Text/LocalAuto37.lean | 27 |
| Text/PackingAuto15.lean | 26 |
| Text/LocalAuto18.lean | 25 |
| Text/LocalAuto33.lean | 25 |
| Text/PackingAuto5.lean | 24 |
| Text/LocalAuto35.lean | 22 |
| Text/LocalAuto3.lean | 18 |
| Text/PackingAuto6.lean | 18 |
| Text/LocalAuto10.lean | 17 |
| Text/LocalAuto16.lean | 17 |
| Text/LocalAuto31.lean | 17 |
| Text/LocalAuto8.lean | 13 |
| Text/LocalAuto15.lean | 12 |
| Text/LocalAuto26.lean | 10 |
| Text/LocalAuto27.lean | 10 |
| Text/PackingAuto12.lean | 9 |
| Text/PackingAuto3.lean | 9 |
| Text/LocalAuto17.lean | 8 |
| Text/PackingAuto10.lean | 8 |
| Text/LocalAuto20.lean | 7 |
| Text/PackingAuto16.lean | 6 |
| Text/PackingAuto20.lean | 6 |
| Text/PackingAuto24.lean | 6 |
| Text/PackingAuto11.lean | 5 |
| Text/PackingAuto23.lean | 5 |
| Text/PackingAuto13.lean | 4 |
| Text/PackingAuto9.lean | 4 |
| Assembly.lean | 3 |
| Text/AzimBridge.lean | 3 |
| Text/LocalAnchors.lean | 3 |
| Text/LocalAuto25.lean | 3 |
| Text/PackingAuto14.lean | 3 |
| Text/PackingAuto19.lean | 3 |
| Statement.lean | 1 |
| Text/LocalAuto12.lean | 1 |
| Text/LocalAuto30.lean | 1 |
| Text/LocalBridge.lean | 1 |
| Text/PackingAuto17.lean | 1 |

</details>

## 主定理可达债务（脊柱公理探针）

> `Kepler.Assembly.the_kepler_conjecture_from_interfaces` 的 `#print axioms`，探针运行时间 2026-09-21 10:32 +0000（main @ 25ad3bb3，全闭包自主源编译）。
> 与上面的 token 计数不同：这里只统计**装配后主定理实际依赖**的公理。

| 类别 | 公理 |
|---|---|
| sorry 占位（接口债务） | sorryAx |
| 特许 native_decide（DECISIONS.md 2026-08-10 scoped exception） | 624 个 shard 公理 / ofReduceBool 族 |
| 标准三公理 | Classical.choice, Quot.sound, propext |
| 其它（**异常，需排查**） | 无 |

`sorryAx` 当前来源 = Assembly.lean 的冻结接口占位（剩余 `nonlinearInequalities` / `linearProgrammingResults` / `textCapstone` 三个；`goodListArchive` 已于 2026-09-19 由 P6-C 闭合，见 docs/phase6-spine.md §1）；每闭合一个接口，此处可达债务随之消减。


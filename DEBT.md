# DEBT.md — sorry 债务账本

> 由 `lean/scripts/debt_ledger.py` 生成；勿手改。总计 **2025** 个 sorry。

| 区域 | sorry 数 | 涉及文件数 |
|---|---|---|
| Text | 2021 | 64 |
| (root) | 4 | 2 |
| **合计** | **2025** | **66** |

<details><summary>逐文件明细</summary>

| 文件 | sorry 数 |
|---|---|
| Text/PackingAuto25.lean | 157 |
| Text/LocalAuto5.lean | 134 |
| Text/LocalAuto1.lean | 91 |
| Text/PackingAuto18.lean | 89 |
| Text/LocalAuto22.lean | 84 |
| Text/PackingAuto22.lean | 84 |
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
| Text/LocalAuto36.lean | 13 |
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

> `Kepler.Assembly.the_kepler_conjecture_from_interfaces` 的 `#print axioms`（探针 2026-09-21 重跑，wip `ad99bee4`）。只统计**装配后主定理实际依赖**的公理：标准三公理 + sorryAx + 特许 native_decide shard 族（624 个，DECISIONS.md 2026-08-10 scoped exception）+ 无异常项。

`sorryAx` 来源（2026-09-21 方向 A/B/D 深挖后）——骨架已从 3 枚粗接口展开为**分层可达债务图**：
1. **粗接口 2 枚**：`nonlinearInequalities`（内含主叶子 `main_nonlinear_terminal_v11`，G4 汇合点）、`lpArchiveCertificates`（逐图 LP 证书总库，Phase 3 持久化 24k/43058 填实）；
2. **TameSpine 13 枚骨架占位**（tame 文字章 capstone：contraveningFan/mqmsmab/tamePlanarHypermapRestricted/jcajydu/tameCorrespondenceIso/elllnyz 镜像析取/hypermapOfFanNeg/isoOppositeEq/contraveningNegative/localAnnulusInequalityScriptL/fcdjdot/kcImpTheKc/hypermapIsoTrans + oppositeHypermap 置换代数字段）；
3. **章节出口 HOLD**：LocalConcl 30/90、PackingConcl 10/62（逐条原因见文件内 ledger）；
4. **已真化**（不再计债）：`textCapstone`（capstone 脚本逐行翻译）、`linearProgrammingResults`（纯逻辑推导，方向 D 降级）、`assembly`、Concl 层 112 条 WIRE（公理沿证明项流动）。

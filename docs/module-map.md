# module-map.md — Phase 5 文字证明模块映射与进度

> PLAN.md §4 Phase 5 任务 1：《Dense Sphere Packings》（蓝图书）章节 → Lean 模块
> 依赖图。§6.6：引理级进度用本文件的勾选表维护。
> 对照基准：`reference/flyspeck/text_formalization/`（其 README 说明该目录
> 按 flypaper 蓝皮书章节组织）。

## 模块依赖图

```
Statement（Phase 1，已完成陈述）
   ↑
Assembly（主定理组装：组合骨架归约 + 三个计算定理）
   ↑                    ↑              ↑
Tame（Phase 2 图枚举） LP（Phase 3）   Nonlinear（Phase 4）
   ↑
LocalFan（局部扇、归约到 8pt 打分不等式）
   ↑
Packing（Voronoi 胞腔、局部密度）
   ↑
Fan（扇与叶片几何） ← Hypermap（超图/平面性，Phase 2 图论地基也在此层）
   ↑
Volume（体积、楔、立体角测度） ← Trig（三角、方位角）
```

原则（PLAN.md §4 Phase 5）：先形式化**组合骨架**（把 G2/G3/G4 三个计算定理
串成主定理的归约），再回填几何与分析引理；卡住的引理先查 Flyspeck 对应证明。

## 章节 → 模块映射

| 蓝皮书章节 | Flyspeck 目录 | Lean 模块（计划） | 状态 |
|---|---|---|---|
| 1 Close Packing（陈述） | `general/` | `Kepler/Statement.lean` | ✅ 陈述完成（G1），证明体 sorry（ sanctioned） |
| 2 Trigonometry | `trigonometry/` | `Kepler/Text/Trig.lean` | ⬜ 未开始 |
| 3 Volume | `volume/` | `Kepler/Text/Volume.lean` | ⬜ 未开始 |
| 4 Hypermap | `hypermap/` | `Kepler/Text/Hypermap.lean` | 🟡 覆盖 hypermap.hl 至 12307/13575（90.7%）：Jordan 曲线、Euler 主定理、loop/atom/正规环族、商 hypermap、`Iso`、face collections（`XWCNBMA`/`lemmaSTKBEPH`）、补等值线（10643–11173）、受限 hypermap/final loops/split condition/hyp'm·S·y·p·q·z 选择函数族与 `lemmaHQYMRTX`（11174–12307，`IsMarked`/`on_hypZ`/`loopSeparation`/`parameters` 等）已移植；is_transform 机器（12308+）待做 |
| 5 Fan | `fan/` | `Kepler/Text/Fan.lean` | ⬜ 未开始 |
| 6 Packing | `packing/` | `Kepler/Text/Packing.lean` | 🟡 `Packing`/`finite_inter_ball` 已在 Statement.lean |
| 7 Local Fan | `local/` + `leg/` | `Kepler/Text/LocalFan.lean` | ⬜ 未开始 |
| 8 Tame Hypermap | `tame/` | Phase 2 已覆盖图侧；`Kepler/Text/TameHypermap.lean`（hypermap 版 tame + 与 fgraph 桥接） | 🟡 图枚举链进行中（见下） |
| 9 组装（Final Conclusion） | `general/the_kepler_conjecture.hl` | `Kepler/Text/Assembly.lean` | ⬜ 未开始 |
| 非线性不等式 | `nonlinear/` | Phase 4（`Kepler/Interval/`：`Basic` 二进制有理数端点区间算术 + `checkPos` soundness；`Div` 除法/倒数（`divFloorQ` 显式误差，`Option` 语义）；`Sqrt` 证书式平方根（内核仅验证 `s²≤n<(s+1)²`）；`Ball` 中点半径包装 + 与 `DInterval` 双向换算；`Trans` Leibniz 交替级数界 + `sin` 的 Taylor dyadic 区间/球（[0,1]）） | 🟡 区间 checker 试点进行中（Kepler/Interval；除法/√/超越层已落地，公理仅标准三） |
| LP | `formal_lp/` | Phase 3（`Kepler/LP/`：`Cert` 稀疏整数对偶证书 checker + 逐列分片 `checkDualColShards`；`Pilot204880136538/` 真实图 915 片端到端闭合） | 🟡 真实图试点已闭合；全量化待转置证书表示（见 architecture.md Phase 3） |

## Phase 2 引理移植进度（tame 图枚举完备性，AFP Flyspeck-Tame 对照）

- [x] 定义层：Graph/Rotation/ListAux/Enumerator/FaceDivision/Plane/Plane1/Tame/Generator/TameEnum
- [x] ListAuxLemmas + RotationLemmas（cong、rotate_min 规范化）
- [x] GraphProps（42 条全量）
- [x] ListSum + TameProps
- [x] EnumeratorProps（enumerator 正确性/完备性）
- [x] PlaneGraphIso + QuasiOrder（≃ 关系、iso_test 含镜像分支 + 正确性）
- [x] FaceDivisionProps（4958 行全量，含 pre_subdivFace'_Some1' 大证明）
- [x] Invariants（2827 行全量：minGraphProps/inv、主不变量定理）
- [x] PlaneProps（全量）
- [x] Plane1Props
- [x] ScoreProps + LowerBound（tame13a 下界正确性）
- [x] GeneratorProps + TameEnumProps（剪枝保持 tame 可达性）
- [x] Completeness 组装（→ `tame_classification`，**G2 已于 2026-08-12 闭合**：
  三种子 575 分片证书 + 接线 + 总装构建通过，公理审计干净，
  详见 `docs/architecture.md` 枚举完备性节"建成状态"）
- [x] 不受信生成器对拍：四种子 19715 张与 Archive 双向一致

## G2 之后待办（证书层）

- [x] ~~逐图可达性见证 + 权重见证 + 同构见证的证书格式落地~~
  （已被 native_decide 分片方案取代，见 DECISIONS.md 2026-08-10）
- [x] ~~Lean checker 重放证书 + `tame_classification` 闭合（验收门 G2）~~（已闭合）
- [ ] （可选）Tri 种子纯内核 `decide` 交叉校验（与 native 路径同一套 loop/check）

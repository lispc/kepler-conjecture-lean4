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
| 2 Trigonometry | `trigonometry/` | `Kepler/Text/Trig.lean` | 🟡 ~30%（PA20/PA22/PA25 消费到的 sin/cos/azim 界与 azim_dihv 桥已随用随证） |
| 3 Volume | `volume/` | `Kepler/Text/Volume.lean` | ✅ 2026-09-11 体积层五件全落（Volume/SectorArea/WedgeVolume/LuneVolume/SolidAngle，零 sorry）；2026-10-12 增 `Geom/SimplexVolume.lean` 标准单形测度桥（1/n! 归纳 + Gram 行列式，713 行零 sorry） |
| 4 Hypermap | `hypermap/` | `Kepler/Text/Hypermap.lean` | ✅ 覆盖 hypermap.hl **全书 13575/13575（100%）**：Jordan 曲线、Euler 主定理、loop/atom/正规环族、商 hypermap、`Iso`、face collections（`XWCNBMA`/`lemmaSTKBEPH`）、补等值线（10643–11173）、受限 hypermap/final loops/split condition/hyp'm·S·y·p·q·z 选择函数族与 `lemmaHQYMRTX`（11174–12307）、transform 机器与主定理 `normal_family_transform`（AQIUNPP1，12308–13575）全部移植完毕；2026-10-12 增 `face_symm_mem`（face 轨道对称封闭泛型件） |
| 5 Fan | `fan/` | `Kepler/Text/Fan.lean` | 🟡 ~25%（TopologyFan/fan7 与 PA 章消费到的扇几何随用随证；LocalFan 本体仍 stub） |
| 6 Packing | `packing/` | `Kepler/Text/Packing.lean`（PA1-25） | 🟡 定义层 100%；定理级 ~65%（1,295 HOL 定理中约 840 真证；PA2 收割后 28 桩/PA23 全章闭合/PA24 剩 B2 单支/PA25 leaf-rank 已清偿；尾部=leaf-cell 链 GIANT） |
| 7 Local Fan | `local/` + `leg/` | `Kepler/Text/LocalFan.lean`（实为 LA1-38 系列） | 🟡 ~65%（1,181 HOL 定理中约 770 真证；LUNAR 链/WRGCVDR 族全净；LA5 剩 48、尾部两根子=POS_DIRECT→SUCCESEOR 与月形链 10 件；deformation 词表族未动） |
| 8 Tame Hypermap | `tame/` | Phase 2 已覆盖图侧；`Kepler/Text/TameSpine/`（tame_list 直译放量） | 🟡 文字章 T3 线启动：W0 keystone + TameList1/2/3 累计约 300 件真证（tame_list.hl 前半）；tame 章全域 1,493 定理中约 15% |
| 9 组装（Final Conclusion） | `general/the_kepler_conjecture.hl` | `Kepler/Text/Assembly.lean` | ✅ M5′（2026-10-10）：`the_kepler_conjecture_e2e` 端到端立起，公理面 = 三冻结接口 sorry + 624 shard + 标准三；T1/T2/T4 展开波已把三接口全部拆为具名骨架 |
| 非线性不等式 | `nonlinear/` | Phase 4（`Kepler/Interval/`：`Basic` 二进制有理数端点区间算术；`Div` 除法/倒数（`divFloorQ` 显式误差，`Option` 语义）；`Sqrt` 证书式平方根（内核仅验证 `s²≤n<(s+1)²`）；`Ball` 中点半径包装 + 与 `DInterval` 双向换算；`Trans` Leibniz 交替级数界 + sin/cos/arctan 的 Taylor dyadic 区间/球 + π-shift 范围缩减（`sinRed`）；`Expr` 扩节点 AST（div/sqrt/trans + Option 求值 + `checkPos_sound`）；`Cert` 分支定界二分树（`BBTree.covers`/`bb_sound`，叶为内核 decide 的 checkPos）） | 🟡✅ **证书替代已闭（2026-10-08 增记）**：612 条非线性 HOL 定理的数学内容由 549 shard native_decide + G4 证书链等价承担；A11 波已把 `pack_nonlinear_rest` 62 条 bank 合取显式化（语句级 debt pin 死）；余 81 条逐条证书灌装 = deferred-compute（等强机器） |
| LP | `formal_lp/` | Phase 3（`Kepler/LP/`：`Cert` 稀疏整数对偶证书 checker + 逐列分片 `checkDualColShards`；`Pilot204880136538/` 真实图 915 片端到端闭合） | 🟡✅ **证书替代已闭 + 43,078 叶立户（2026-10-08 T2）**：43,078 终端 LP 内核验证数与 STATUS 对账吻合；Lean 侧 `Text/LP/` 177 模块（LPCert 语义 + LPIds 清单 + per-record 叶 + LPAll 量化装配，8,833 jobs 绿）；叶数据灌装 = deferred-compute（等强机器），覆盖桥（formal_lp verify_all 链移植）待立项 |

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

## 全库三态覆盖度普查（2026-10-12，编排者实测账）

> 口径：HOL 侧 = `reference/flyspeck` 实测（text_formalization 5,935 定理/620,018 行
> + formal_ineqs 463/43,311 + formal_lp 137/21,194 + formal_graph 4/1,907，
> 合计 ≈6,540 定理 / ≈686,000 行；定理计数模式
> `^let X = (prove|prove_by|new_theorem…)`）。Lean 侧 = 98,080 枚定理/引理声明、
> bare sorry 44,469（其中 43,078 = LP 数据叶，**真实在树债 ≈1,391**）。
> 章节归类带估计成分（章内不均匀），量级可靠。

| HOL 章 | 行数 | 定理 | 已移植(真证) | 定义/骨架/证书替代 | 未移植 |
|---|---|---|---|---|---|
| packing | 99k | 1,295 | ~65% | ~30% | ~5% |
| local | 175k | 1,181 | ~65% | ~20% | ~15%（deformation 词表族） |
| nonlinear | 93k | 612 | 证书替代（549 shard+G4/dReal/Arb） | 少量粘合 | ~0 真缺口 |
| general（工具箱） | 66k | 42 | 定义层 ~80% 散入各文件 | — | ~20% |
| tame | 98k | 1,493 | ~15%（TameSpine W0+TameList1-3） | ~5% | **~80%** |
| fan | 49k | 223 | ~25% | ~30% | ~45% |
| hypermap | 14k | 534 | 100%（见上表第 4 章行） | — | 0 |
| trigonometry | 11k | 193 | ~30% | ~20% | ~50% |
| jordan | 7k | 200 | ~10% | ~10% | ~80% |
| leg+volume | 7k | 162 | ~45% | — | ~55% |
| （证书三章）formal_ineqs/lp/graph | 66k | 604 | **证书替代已闭** | 全部 | 0 |

**头条数字**：按定理数已移植 ~38%（≈2,500）/ 证书替代与定义 ~20% / 未移植 ~42%；
按行数 ~40% / ~28% / ~32%。未移植主体 = tame 章（98k 行）+ fan 尾部 + jordan。
关键结构结论：①"只移植定义"的半成品章几乎不存在——各章要么基本真证、要么整章
未动，中间态集中在 packing/local 尾部骨架（≈1,391 在树 sorry 分布）；
②**证书替代类（≈1,200 定理）是 Flyspeck 的计算性内容**，不逐行移植，
等强机器灌数据即终态（A11 993 证书/A12 43,078 LP/92 prep/Phase 4 重放）；
③贪心触达制下 tame 章按 A7/A8/A9 前提树需求批推进，无需线性全搬。

> 刷新纪律：每重大波次随 e2e-debt-map 一起更新本节（编排者职责）。

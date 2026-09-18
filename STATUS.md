# 项目总进度（Status）— 2026-09-18

> 一页看板：各 Phase 完成度、已完成什么、还差什么。每 24h 由主 agent 例行刷新（cron 自动 push）。
> 详细交接信息见 `HANDOFF.md`，阶段定义见 `PLAN.md`，长期决策见 `DECISIONS.md`。
> 当前 main @ 见本 commit；最近验收：各批次根构建绿（wip/auto-packing 批次提交信息 "38-way root clean"，`aa4baf6b`；HANDOFF 记录 `make check` 绿 `c425db2`，2026-09-14）。
> 注意：2026-09-13 起接班 agent 改为 main 直推模式，允许在制骨架 sorry 短暂存在；
> 历史 sanctioned 占位仍为 `Statement.lean` 主定理（见 Phase 1）。
> **重大进展**：**packing 章 25 模块骨架 100% 就位（2026-09-15，`5b470efc` 起）**——
> ~1114 定理全部陈述（含各 capstone），20.5k 行 Lean / 920 sorry 进入纯填证期；
> **local 章骨架 100% 就位（2026-09-16，`aa4baf6b`）：39 模块覆盖 174.7k 行 HOL 源，
> 1793 sorry 进入纯填证期**——至此 Phase 5 全部主体章节（packing + local）骨架齐备。
> **Phase 4 G4 由 Kimi 并行推进（wip/g4-emit）：首个 sqrt/atan 全量案
> QITNPEA_3725403817（964,984 叶，2775 BBTreeG shards）内核构建中（86%，2379/2775）；
> 封闭 atan Taylor 阶 1024→128 固化（四档验证全过，`1db69bd8`，内核成本 ~8x↓）；
> 5490182221 全量 stage-a（360 chunk 数据模式）运行中（175/360）**。
> 政策变更（2026-09-17 用户批准，已执行 2026-09-18）：main 允许携带 sorry 债务，
> wip/auto-packing 已合入 main（`aad4fb35`），债务刻度 = `DEBT.md`（基线 2400）。

图例：✅ 完成并验证 / 🟡 进行中 / ⬜ 未启动。完成度为行数或条目数口径的粗略估计。

---

## Phase 0 — 环境与参考库 ✅

- [x] Lean 4 toolchain（v4.32.2，elan 锁定）、lake 构建可用
- [x] 参考库落盘 `reference/`（flyspeck 文本形式化等，`reference/LOCK.md`）
- [x] 求解器：SoPlex 8.0.3（精确模式）、glpsol --exact、GLPK
- [x] 128 核 / 503G RAM 生产机器；系统盘已扩容至 936G（2026-09-16 起弃用 tmpfs，日志/工件直落盘）

## Phase 1 — 定理陈述形式化 ✅（陈述层）

- [x] 堆积密度定义与主定理陈述 `the_kepler_conjecture`（`Kepler/Statement.lean`）
- [x] 陈述保真性对照文档（`docs/statement-fidelity.md`）
- [ ] 主定理**证明**本体（`Statement.lean:111` 的唯一 sanctioned sorry）——全项目终点，Phase 6 装配

## Phase 2 — tame 平面图枚举 ✅ 100%（闭合）

- [x] 19,715 张 tame 平面图全量枚举 + 内核验证（585 个 CertShards 分片）
- [x] 公理审计通过（`make check`；601 个限定范围 native_decide 信任公理，零 sorryAx）
- [x] 新机器全量重建验证过
- ⚠️ 红线：绝不 `rm -rf lean/.lake`，分片重建需 ~7 天

## Phase 3 — 线性规划 ✅ 100%（2026-09-07 全闭合）

- [x] 证书链路全通：Flyspeck 证书解析 → LP 展开/扁平化 → SoPlex 精确求解 → 整数对偶证书 → Lean 内核弱对偶 checker（`Kepler/LP/Cert.lean`、`ColMajor.lean`）
- [x] 试点图端到端闭合（行主序 + 列主序，`3cbe979`）；生产 harness 入 git（`pipeline/lp/run/`）
- [x] easy 23,640/23,640 终端内核验证通过
- [x] hard_1 偏差根因修复（`d5e32af`：branch.py 逐节点数值收紧重放）
- [x] **全部 43,078 个终端 LP 内核验证通过**：SoPlex 数值放弃的 51 例全部经 glpsol 精确对偶通道闭合（`glpsol_dual.py`，glpsol --exact 最慢 13.5h/例 + 内核 decide ~245s/例）。账本 `~/lprun-logs/results.jsonl`（43,078/43,078 exit=0）

## Phase 4 — 非线性不等式 🟡 求解层 ~85% / 内核闭合 0%

- [x] 区间算术全层（`Kepler/Interval/`：Basic/Div/Sqrt/Ball/Trans/Expr/BBTree 分支定界，`f3cea0f`）
- [x] dyadic 精确算术、证书式 sqrt、Taylor/sin soundness、分支定界证书格式
- [x] 量产流水线：`ineq.hl` 记录解析（181 条）→ 公式 AST（176 条）→ 定义表（348 定义依赖闭包零缺失）→ RPN case JSON（176/176，`f99dd04`）
- [x] **bb_arb：C/FLINT 球算术分支定界器**（`8b7c3c4`）：RPN 求值 + dyadic 二分 + ite guard + disj + 证书 JSON 输出；sqrt8 端点精度 bug 已修（2⁻³⁰ 网格）
- [x] y 空间直跑：**65/176 闭合**（dReal 41 + bb_arb 新增）
- [x] **prep（x=y² 归一化，Flyspeck 官方形式）路线大胜**：812 条 prep 记录全解析 → 745 案例生成（四脚本 CLI 化，`59d3a1b`）；pass1+pass2（900s/4M 节点）**745/745 全闭合（100%）**
- [x] **家族级分析（2026-09-09）**：176 条不等式 = 68 y 空间闭合 + **92 条 prep 家族覆盖闭合（实质已解决）** + 16 条真残余（清单 `pipeline/interval/out/residue16.txt`：TSKAJXY 系 4 条、TEWNSCJ/PEMKWKU/TXQTPVC/IXPOTPA、QZECFIC wt0 ×2、GRKIBMP B V2 等）。**求解层合计 160/176（91%）**
- [ ] 16 条真残余逐条定策略（GRKIBMP B V2 有真反例叶=尖锐边界组，需 ε 余量或弱编码；其余先试更大预算/域剖分）
- [ ] **BBTree 证书 → Lean 内核闭合**（G4）：bb_arb 已能出 cert JSON；Lean 侧扩展进度：
  - [x] `IExpr.abs` + `DInterval.abs` + soundness（`Basic.lean`/`Expr.lean`）
  - [x] `IExpr.ite`：**区间决定 guard**（`C.hi<0`→then，`C.lo≥0`→else，跨 0→STRADDLE 返回 none），`eval_mem` 证分支一致——无需单独 guard 证书
  - [x] 析取证书 `Kepler/Interval/CertDisj.lean`：`DisjGoal = pos e | varLt i j`，`BBTreeD` + `bb_sound_disj`（覆盖 58 条 disj 案例）
  - [x] `TKind.lnK` + `logI` 全链（2026-09-13，`3aed260` 进 main）：`log2D` dyadic 常数证书、`lnI`/`logInterval` soundness（`[1,2]` artanh 级数）、试点 2/3 < log x on [2,4]，公理仅标准三
  - [x] **`emit_lean.py` 证书→Lean 分片生成器 + 端到端通路（2026-09-13/14，wip/g4-emit 分支，Kimi 负责）**：
    - 树重建：扁平叶表 → 二分树（任意无横跨维满足 splitOK，优先最宽维）
    - 分片三层结构 Base/ShardK/根（公理标准三）：**7 案例端到端闭合**——`C1965189142x34`（1 叶）、`C3397113841`（1.5k 叶 35.7s）、`C4717061266`（55k 叶 4m50s）、`CFWGKMBZ`（205k 叶 59m50s，`642fa5c`）、`C6078657299`（694k 叶，首个真实 disj 大案例，`625fd10`）、`C8425800388`（**1.35M 叶** 4h47m，`8b31098`）、`C3253650737`（**1.67M 叶** 5h19m，`a55b02d`）
    - `CertBool.lean`：`splitOKB`/`coversB`（BBTree + BBTreeD）——整树覆盖一次内核 `decide`
    - `CertG.lean`/`BBTreeG`：**跨叶 sqrt/div/trans 参数机制**——`evalReal` 忽略证书参数，逐叶特化表达式 + `rfl` 语义桥（试点端到端绿）
    - disj 发射（BBTreeD/var_lt 校验）已实现，合成 mixed-hits 案例端到端绿（假证书被内核正确拒收）
    - **4 个真缺陷治本**：`divFloorQ` 缩放空间缺陷（深负指数除法 none→双分支精确取整）；`atan(1)` 边界不可求值（Abel 式极限放宽为 ≤）；修复扫描假绿防护（驱动错误即中止）；**dyadic 规范化形态 vs 内核 midRadius 形态**（偶数 mantissa 中点结构不等——全管线改 (m,e) 表示 + midRadius 同款中点，`0aea134`）
  - [x] **FillParams 参数填充工具链（2026-09-14，`0588df2`）**：Lean 编译态逐叶算 sqrt mantissa（零镜像失真）+ (N,out) 阶梯 + 279 叶小样端到端绿；封闭 atan 参数高 Taylor 阶 trick（阶数后经实测下调，见下）
  - [x] **FillParams stage-a 分片并行化（2026-09-15，wip/g4-emit）**：单体驱动（354MB/96万叶数组字面量）elaboration 不可扩展（11.5h 未果）→ 改造为 `--stage-a-shards=K` 连续切块小驱动 + `runMain` argv 派发（无参走阶梯 / `N out` 钉死单点）+ `stagea_merge.py`（全局 rung 裁定 + STALE 补算 + 全局索引合并）；256 chunk × 64 路并行
  - [x] **repair_leaves.py 叶修复回路（`85f5ae7`）**：编译态逐叶扫描 → 失败叶二分加深（splitOK 对任意细化保持）→ 修复证书
  - [ ] 现存 16 证书收尾：已闭合 6 份（另加早期 2 小案共 8 案例）；波1 sqrt4/atan7 三份——**QITNPEA_3725403817 已闭合（2026-09-18，`184d4a86`：964,984 叶 = 964,792 + 192 修复衍生，2775 BBTreeG shards，11,441 jobs，根 decide 180s，公理标准三）**；**封闭 atan Taylor 阶 1024→128 已固化（`1db69bd8`：四档 3762 叶全过、rung 不变，内核 decide 成本 ~1/N，~8x 提速）**；5490182221（135万叶）stage-a 356/360 完成（全局 rung (12,-64)），4 chunk 结构性失败叶（7491 个）repair 进行中，随后 params 合并 → --bbg → 构建；2570626711（190万叶）stage-a 数据已备货；波2 disj+sqrt 家族 6 份（79~83 sqrt，FillParams 待扩 disj）；末位 2 份 3112-sqrt 怪物（需参数共享优化）
  - [ ] 证书量产：145 个已闭合案例需 bb_arb `--cert` 重跑出证书（机时 1-3 天；9893763499 案例 bb_arb 失控吐 117GB 日志已记录）
  - [ ] G4 粘合收尾：155 定义闭包的 Lean 定义 + 每案例 `evalReal e ρ = 展开式 ρ` 对应引理（依赖 packing 章定义，**主体剩余**）
  - 规格：`pipeline/interval/arb-layer.md` §3/§4
- [ ] GRKIBMP_B_V2 尖锐边界组单独处理（我们把 ≥ 加强成严格 > 导致等号边界不可闭，需 ε 余量或弱编码）
- [ ] `ineqdata3q1h.hl` 7 条 Mathematica record 单独解析
- 数字口径：底账 181 条记录（+3q1h 的 35 条）；y 空间 176 案例 / prep 空间 745 案例

## Phase 5 — 文字证明移植 🟡（全项目最大头，已全自动化）

**生产模式（2026-09-10 v2）**：`lean/scripts/auto_pipeline.sh` 全自动批次流水线——
deepseek-v4-flash 全权负责：骨架设计（陈述冻结）→ 工人填空 → 机械闸五道 →
批次审计 → 自动 ff-push main。满血 glm-5.3 留作 NEEDS-HUMAN 前最后兜底；
**Kimi 降为每 4h 汇报 + STATUS.md + 陈述保真抽查 + 处理熔断**。
模板：`docs/phase5-worker-template.md`。
实测吞吐：批次 4（10 枚）21 分钟、批次 5（10 枚）15 分钟，全 deepseek 一次过。

| 模块（HOL 源文件） | 行数 | 状态 | 完成度 |
|---|---|---|---|
| hypermap/hypermap.hl | 13,575 | ✅ 全书收官 | 100% |
| fan/fan.hl 系列（fan_defs/fan_misc/fan/CFYXFTY/hypermap_and_fan） | ~7,800 | ✅ 全书收官（hypermapOfFan 完整构造） | 100% |
| fan/topology.hl | 4,718 | ✅ 全书收官（`36c37c6`，dart_leads_into 全套） | 100% |
| fan/planarity.hl | 15,463 | ✅ **全书收官（2026-09-11，`48ff904`）**：批次 1-15 自动闭合 + 批次 16 的 `solid_of`/`MOZNWEH` 经体积层人工攻坚闭合，全部进 main | **100%** |
| fan/Conforming.hl | 17,033 | ✅ **全书收官（2026-09-12）**：批次 1-23 全闭合（~230 枚定理，全部零 sorry、标准公理），含巨证 `lemma_connect_hypermap`（~1900 行 HOL 证明，6 段 sub-agent 流水攻克）与收尾 Euler/`Hypermap.Planar`；已合入 main | **100%** |
| fan/polyhedron.hl | 3,200 | ✅ **全书收官（2026-09-14）**：71 条定理 + Polytope 面理论基层（`Kepler/Text/Polytope.lean` ~2.5k 行，0 sorry）全部闭合进 main；巨证 `FLVNSME`（~1000 行 HOL）经 6 段 sub-agent 流水 + 两阶段规划攻克；曾发现 FaceOf 闭/开线段编码 bug，已修正为 Brøndsted 开线段规范并诚实重做受污染证明 | **100%** |
| packing/（Rogers/OXLZLEZ3/REUHADY/counting_spheres/marchal…） | **99,350（43 文件，2026-09-13 实测）** | 🟡 **骨架 100% 就位（2026-09-15）**：25 模块 20.5k 行 Lean，~1114 定理全部陈述（GRUTOTI/OXLZLEZ/URRPHBZ3 等多个 capstone 已证），920 sorry 纯填证期 | 骨架100% / 证~25% |
| local/（IMJXPHR/QKNVMLB/XWITCCN/local_lemmas/terminal…） | **174,694（68 文件，2026-09-13 实测）** | 🟡 **骨架 100% 就位（2026-09-16，`aa4baf6b`）**：W1-W7 七波 39 模块（LocalAuto1-38 + LocalAnchors），174.7k 行 HOL 源全部骨架化，各批根构建绿（38-way root clean），1793 sorry 纯填证期 | 骨架100% / 证~10% |
| trigonometry/（trig1/trig2/euler） | 10,511 | ⬜ 未启动（部分语义已被 azim 层覆盖，正式移植未做） | 0% |
| volume/vol1.hl | 1,421 | 🟡 已用 :18/:458/:651 三段（`radialNorm`/`sol`），其余待移植 | ~25% |
| fan/ 残余（hypermap_iso-compiled 1,174 + GMLWKPK 297） | 1,471 | ⬜ 未评估（可能为编译产物/可跳过） | — |
| assembly（ch9 终装配） | — | ⬜ 未启动 | 0% |

> 行数口径说明（2026-09-13 实测 `reference/flyspeck/text_formalization/`）：Phase 5 全书总量
> ≈ **359k 行**（已完成 60.8k + 剩余 ~298.6k）。旧估计"packing 28k / local 30k"实测为
> 99k / 175k，此前完成度高估约 3 倍，已据此下修。不计入：nonlinear/（93k，Phase 4 数据）、
> tame/（98k，Phase 2 数据）、general/theorem_digest*（60k，自动生成索引）。

已落地的公共地基（`Kepler/Geom/` + `Kepler/Text/`）：

- [x] **体积层基础设施 `Kepler/Geom/Volume.lean`（2026-09-11 新增，已验证无 sorry、
  公理仅标准三）**：`radialNorm`（vol1.hl:18）、`sol`（vol1.hl:651，用
  `Classical.choose` 编码 HOL `new_specification`）、`sol_spec`（体积密度规格）、
  `radialNorm.volume_scaling`（vol1.hl:458 `lemma_r_r'` 的标度不变性）、
  `sol_radius_independent`，以及 `volume.real` 在平移/标度下的引理。这是
  Conforming/packing/local 大量 `sol` 代数定理的前置；**不依赖** VOLUME_SOLID_TRIANGLE。
- [x] Azim 方位角全层（Azim/AzimLemmas：ON 标架、角加法、AZIM_EQ/COMPL 等）
- [x] Aff 仿射符号层（affGe/affGt/affLt/affsign）
- [x] Coplanar 移植（`Kepler/Geom/Coplanar.lean`，`757a33d`）
- [x] vectorAngle/angle 引理族（`VectorAngleLemmas.lean` + 三点角）
- [x] azim 平移桥 `azim_sub_self` + JBDNJJB 混合积 + cross_dot 族
- [ ] 遗留去重：`Kepler.Text.fan80/fan81`（Planarity）与 `Kepler.Text.Fan.fan80/fan81`（Fan.lean:222）重复定义，待合并

生产经验（新）：工人读不了仓库外路径（external_directory auto-reject 杀会话）；
标量-标量乘在 ascription 里写 `*` 不写 `•`（isDefEq 死循环）；定理应用严格按签名
参数个数；验收构建必须自然退出（掐死时 error 未 flush 是假绿）；闸误杀先修闸
（`--relative` 路径事故，`1a32e53`）。

**planarity 收官（2026-09-11，已解决，`48ff904`）**：原先卡住的 2 枚
（`solid_of_dartset_leads_into_fan_triangle_fan` + `MOZNWEH`）已通过自建体积层闭合。
关键技术路线（可复用于后续 Volume/Packing/Local 章节）：
- `Kepler/Geom/Volume.lean`：`sol` / `sol_spec`（vol1.hl，`Classical.choose` 编码）。
- `Kepler/Geom/SectorArea.lean`：2D 扇形面积 = ρ²θ/2（`Complex.polarCoord` 变量替换）。
- `Kepler/Geom/WedgeVolume.lean`：HOL `VOLUME_BALL_WEDGE`（球∩楔形 = azim·2r³/3）——
  含平移/旋转归约、ON 标架等距、`azim↔arg` 桥、Fubini + 扇形积分。
- `Kepler/Geom/LuneVolume.lean`：`dihV`、`azim_dihv_same`、`WEDGE_LUNE_GT`、
  `HAS_MEASURE_LUNE(_SIMPLE)`。
- `Kepler/Geom/SolidAngle.lean`：HOL `VOLUME_SOLID_TRIANGLE`（= (Σ dihV − π)r³/3）。
全部零 sorry、公理仅标准三。`solid_of`/`MOZNWEH` 改用 `sol` 陈述后由上述引理组装。
**经验**：这类研究级引理用「专项子 agent（同一主模型）+ 迭代编译 + 允许诚实部分完成」
可以攻下（本会话 4 个子 agent 分别拿下扇形、楔形、lune、solid triangle）。

**Conforming.hl 收官（2026-09-13，`d77c13f` 进 main）**：流水线
`scripts/auto_pipeline_conforming.sh` 批次 1-23 全部闭合（~230 枚定理，零 sorry、
标准公理）。收尾两枚 `WGVWSKE`/`GGRLKHP` 依赖 `lemma_connect_hypermap`
（~1900 行 HOL 巨证，6 段 sub-agent 流水攻克）+ Euler 恒等式 ⇒ `Hypermap.Planar`。
工作流在本书期间两次升级：多 lane 并行分支 + "axiom closure pending" 暂存机制、
two-stage（planner+executor）难题拆解法。已知坑：HOL 原文存在同名不同义的重复绑定
（如 `add_edge_graph` :2304/:2431），跨模块同环境会撞名——骨架设计阶段必须查重。

**polyhedron blocker 台账（2026-09-13 建，用户批准；2026-09-14 全部核销）**：
原 12 枚真实 sorry 全部闭合——前 9 枚（`FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`、
`EXISTS_EDGE_POLYTOPE`、`AMHFNXP_BIJ`、`EXISTS_EDGE_AT_VERTICES`、
`CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`、`BSXAQBQ`、`POLYTOPE_FAN80`、`WBLARHH`）+
末 3 枚（`POLYHEDRON_FAN`、`EXPAND_EDGE_POLYTOPE`、`FLVNSME` ~990 行巨证经
P1-P5 分段流水攻克）。**polyhedron.hl 100% 达成（71/71 定理零 sorry + 根构建绿，
`c425db2` 进 main）**。

## Phase 6 — 集成与交付 ⬜

- [ ] Phase 2–5 闭合后装配主定理证明（替换 Statement.lean:111 的 sorry）
- [ ] 全量公理审计终验（目标：仅 propext / Classical.choice / Quot.sound + Phase 2 限定 native_decide）
- [ ] 最终文档与复现脚本

---

## 整体估计

- **计算三线**（Phase 2/3/4）：图枚举 ✅100%；LP ✅100%；非线性求解层 **160/176（91%）**（68 y + 92 prep），残余 16 条已列清单；内核闭合 **G4 已百万叶级量产**（**8 案例端到端进内核**：最大 1,670,962 叶 5h19m；2026-09-18 首个 sqrt/atan 全量案 QITNPEA_3725403817 闭合——96.5 万叶 2775 分片，公理标准三，`184d4a86`；封闭 atan 阶 1024→128 固化 ~8x 提速；5490182221 stage-a 356/360 完成、4 chunk 结构性失败叶修复中；剩 10 证书收尾 + 145 案例证书重跑 + 155 定义粘合）。
- **文字证明**（Phase 5，占全项目工作量 60%+）：已完成 hypermap + fan + topology + **planarity 100%** + **Conforming 100%** + **polyhedron 100%（2026-09-14）** ≈ **61.8k 行 HOL 源全证**；**packing 99.4k 骨架 100% 陈述（2026-09-15，25 模块 20.5k 行 Lean / 920 sorry 填证期）**；**local 174.7k 骨架 100% 陈述（2026-09-16，39 模块 / 1793 sorry 填证期）**——至此全书主体三章陈述层齐备，剩余：填证 2713 sorry + trigonometry 10.5k / volume 1.1k / fan 残余。**按行数口径 ~17%+全部骨架**；考虑已完成部分含大量最难地基（hypermap 构造、体积测度层从零建），而 local/packing 多为模式重复引理工厂，**工作量口径估计 35-45%**（opencode 侧按骨架完成口径自估 ~75%，口径不同：其将骨架陈述计入完成度）。按 packing 实测吞吐（99.4k 行骨架 2 天）线性外推，剩余填证约需 30-45 天连轴。
  另：**体积/测度论层已从零建成**（`Kepler/Geom/*.lean`，~3.4k 行，含 HOL Light 多元库的球面立体角链），这是原计划里没算到的关键前置，现已就位，后续 Packing/Local 可复用。
- **全项目粗略完成度：~55%（packing + local 骨架全部就位，填证期全面开启）**。

## 验证纪律

1. main 分支：`lake build Kepler` 全绿；**2026-09-17 政策变更（DECISIONS.md）：main 允许携带 sorry 债务，债务刻度 = `DEBT.md`（`lean/scripts/debt_ledger.py` 生成，基线 2400）**；终验标准不变只是推迟——项目终点要求主定理证明本体零 sorry 可达 + `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`（+ Phase 2 限定 native_decide）；陈述保真审查（`docs/statement-fidelity.md`）是唯一质量阀门，不随本政策放宽；
2. 批次闭合标准：该批全部定理零 sorry + 根模块构建绿 + 陈述保真抽查；
3. 自动化 harness 的提交由机械闸背书 + 主 agent 审计兜底；人工派工的提交由主 agent 逐块验收。

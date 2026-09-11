# 项目总进度（Status）— 2026-09-11

> 一页看板：各 Phase 完成度、已完成什么、还差什么。每 24h 由主 agent 例行刷新（cron 自动 push）。
> 详细交接信息见 `HANDOFF.md`，阶段定义见 `PLAN.md`，长期决策见 `DECISIONS.md`。
> 当前 main @ `7395bc9`，`lake build Kepler` 全绿，
> 唯一 sorry 是 `Statement.lean:111` 的主定理占位（sanctioned，见 Phase 1）。
> Phase 5 auto_pipeline 已 FAIL-STOP：planarity 收官批剩最后 2 枚（压轴主定理），
> 卡在测度论前置 VOLUME_SOLID_TRIANGLE 未移植（见 Phase 5 节与 HANDOFF）。

图例：✅ 完成并验证 / 🟡 进行中 / ⬜ 未启动。完成度为行数或条目数口径的粗略估计。

---

## Phase 0 — 环境与参考库 ✅

- [x] Lean 4 toolchain（v4.32.2，elan 锁定）、lake 构建可用
- [x] 参考库落盘 `reference/`（flyspeck 文本形式化等，`reference/LOCK.md`）
- [x] 求解器：SoPlex 8.0.3（精确模式）、glpsol --exact、GLPK
- [x] 128 核 / 503G RAM 生产机器；大工件放 tmpfs（/dev/shm），日志双备份

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
- [ ] **BBTree 证书 → Lean 内核闭合**（G4）：bb_arb 已能出 cert JSON；Lean 侧需扩展 IExpr（abs 节点）/TKind（ln）/Cert 叶（guard 符号 + disj 备选），规格在 `pipeline/interval/arb-layer.md` §3/§4
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
| fan/planarity.hl | 15,463 | 🟡 main 覆盖至 :15280（**98.8%**）：批次 1-15 全自动闭合入 main；批次 16（收官批）4/6 闭合在 wip，**剩 2 枚 NEEDS-HUMAN**（见下） | **99%** |
| fan/Conforming.hl | 17,033 | ⬜ 未启动 | 0% |
| fan/ 其余（polyhedron 等） | ~3,200 | ⬜ 未启动 | 0% |
| packing/（Rogers/OXLZLEZ3/REUHADY…） | ~28,000 | ⬜ 未启动 | 0% |
| local/（IMJXPHR/QKNVMLB/XWITCCN…） | ~30,000 | ⬜ 未启动 | 0% |
| assembly（ch9 终装配） | — | ⬜ 未启动 | 0% |

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

**当前卡点（2026-09-11，planarity 收官批批次 16，FAIL-STOP）**：剩 2 枚耦合定理
在 `Kepler/Text/PlanarityAuto16.lean`（wip 分支）：
1. `solid_of_dartset_leads_into_fan_triangle_fan`（planarity.hl:15370）——三角面
   dartset 的立体角公式。deepseek×2 + 满血 glm-5.3×1 均失败。根因：前置
   `VOLUME_SOLID_TRIANGLE`（measure(ball∩aff_gt) = (Girard 盈余)·r³/3）**不在
   planarity.hl，在 HOL Light 本体 `Multivariate/flyspeck.ml:5883`**（已抓到
   /tmp/flyspeck_ml.txt；测度论证明链较长）。`sol`/`dihV`/`AZIM_DIVH` 也未移植
   （骨架 docstring 里有 sol 的 ε 规格编码方案）。
2. `MOZNWEH`（planarity.hl:15443，**全书主定理**）——纯 MESON 组装，
   待 solid_of 闭合后秒过。

**2026-09-11 接手评估（新）**：已确认这是全项目第一个真正的**研究级数学墙**，
不是流水线调度问题：
- `sol` 基础设施已落地（见上 `Kepler/Geom/Volume.lean`），所以 `solid_of` 现在
  只需「`sol_spec`（r=1）+ `VOLUME_SOLID_TRIANGLE`」，剩下的唯一硬骨头就是
  **球面三角形体积（Girard 球面盈余 / lune 体积）**。该链依赖
  `VOLUME_BALL_WEDGE`（球与楔形交的体积 = azim·2r³/3，HOL 用 Fubini + 2D 扇形
  面积证）、`MEASURE_LUNE_DECOMPOSITION`、`AFF_GT_SHUFFLE`、`SOLID_TRIANGLE_CONGRUENT_NEG`。
- Mathlib 现状：有 `volume_ball`、`toSphere`（球面测度）、`Complex.polarCoord`
  变量替换、`addHaar_smul`（标度）、平移不变、Fubini；**没有**球面盈余 / lune /
  扇形面积 / 半空间球体积。移植该链需要自建球面测度几何（估计 1–2k 行，且是
  自动化工人最不擅长的分析/积分证明）。
- 结论：**不要再用 deepseek/glm 盲派 `solid_of`**；应先把体积链作为专项
  （独立文件 + 人工/强模型逐引理）攻克，或先绕开它推进不依赖立体角公式的部分。

路线（修订）：① 用新 `sol_spec` 重启流水线移植 `Conforming.hl`（228 定理中仅
`version_JUTSTKG` 等少数依赖 `solid_of`；其余为 `sol` 代数/测度/径向，可闭合）；
② 并行专项移植 VOLUME_SOLID_TRIANGLE 链；③ 回补 solid_of → MOZNWEH → 批次 16 进 main。

## Phase 6 — 集成与交付 ⬜

- [ ] Phase 2–5 闭合后装配主定理证明（替换 Statement.lean:111 的 sorry）
- [ ] 全量公理审计终验（目标：仅 propext / Classical.choice / Quot.sound + Phase 2 限定 native_decide）
- [ ] 最终文档与复现脚本

---

## 整体估计

- **计算三线**（Phase 2/3/4）：图枚举 ✅100%；LP ✅100%；非线性求解层 **160/176（91%）**（68 y + 92 prep），残余 16 条已列清单；内核闭合 0%（G4 待开工）。
- **文字证明**（Phase 5，占全项目工作量 60%+）：已完成 hypermap + fan + topology + planarity 75% ≈ 38k 行 HOL 源；待移植 ≈ 82k 行。按行数口径 **~32%**。auto_pipeline 无人值守批次推进中。
- **全项目粗略完成度：~55%**。

## 验证纪律

1. main 分支：`lake build Kepler` 全绿 + `grep sorry/admit/native_decide` 零命中（Statement.lean:111 与 Graphs.Cert* 例外）+ 新定理 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；
2. wip 分支：允许 sorry（骨架占位），进 main 前由主 agent 批次审计陈述保真；
3. 自动化 harness 的提交由机械闸背书 + 主 agent 审计兜底；人工派工的提交由主 agent 逐块验收。

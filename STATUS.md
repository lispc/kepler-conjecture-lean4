# 项目总进度（Status）— 2026-09-08

> 一页看板：各 Phase 完成度、已完成什么、还差什么。每 24h 由主 agent 例行刷新。
> 详细交接信息见 `HANDOFF.md`，阶段定义见 `PLAN.md`，长期决策见 `DECISIONS.md`。
> 当前 main @ `8a81d0b`，`lake build Kepler` 全绿（9304 jobs），
> 唯一 sorry 是 `Statement.lean:111` 的主定理占位（sanctioned，见 Phase 1）。

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

## Phase 4 — 非线性不等式 🟡 求解层 22% / 内核闭合 0%

- [x] 区间算术全层（`Kepler/Interval/`：Basic/Div/Sqrt/Ball/Trans/Expr/BBTree 分支定界，`f3cea0f`）
- [x] dyadic 精确算术、证书式 sqrt、Taylor/sin soundness、分支定界证书格式
- [x] 量产流水线（2026-09-08 一天内建成，`9673f92`–`8a81d0b`）：
  `ineq.hl` 记录解析（181 条，grep 对账零残留）→ 公式 AST（176 条，往返零误差）
  → 定义表（sphere.hl+nonlin_def.hl 348 个定义，依赖闭包 155 符号零缺失）
  → SMT-LIB2 发射（176/176，dReal 逐文件解析零错误）
- [x] **dReal 第一层批跑 pass 1**（δ=1e-3，300s/条）：**39/176 unsat 证掉**；
  6 条 δ-sat（均为 Branching/Eps/Sharp 边界尖锐组，已逐条排除翻译错误）；
  131 条超时 → pass 2（1800s/条）进行中
- [ ] dReal 超时/δ-sat 案例 → Arb 球算术分支定界（第二层）
- [ ] **求解结果 → Lean 内核证书闭合**（BBTree 分片 + checkPos，内核验收门 G4）
- [ ] `ineqdata3q1h.hl` 7 条 Mathematica record（每条 5 不等式）单独解析
- [ ] cos/arctan 实例化、sin 范围缩减放宽（按需）
- 数字口径修正：旧文档"~993 个"为过时估计；实际底账 181 条记录
  （+3q1h 的 35 条），子断言 ~23k 来自 Branching 定义域剖分

## Phase 5 — 文字证明移植 🟡（人力主线，全项目最大头）

**生产模式（2026-09-07 起）**：opencode + GLM coding plan（glm-5.3-flash 常规 / glm-5.3 攻坚）工人研磨，Kimi 主 agent 切分任务 + 验收（build/sorry/公理）+ 提交 + 卡壳手写兜底。模板：`docs/phase5-worker-template.md`。

| 模块（HOL 源文件） | 行数 | 状态 | 完成度 |
|---|---|---|---|
| hypermap/hypermap.hl | 13,575 | ✅ 全书收官 | 100% |
| fan/fan.hl 系列（fan_defs/fan_misc/fan/CFYXFTY/hypermap_and_fan） | ~7,800 | ✅ 全书收官（hypermapOfFan 完整构造） | 100% |
| fan/topology.hl | 4,718 | ✅ 全书收官（`36c37c6`，dart_leads_into 全套） | 100% |
| fan/planarity.hl | 15,463 | 🟡 流水线推进中，覆盖至 :3635（`771fbcb`）；巨块 not_cut_inside_fan（:3667–5182）在 wip 分支切片推进，~85% | ~24% |
| fan/Conforming.hl | 17,033 | ⬜ 未启动 | 0% |
| fan/ 其余（polyhedron 等） | ~3,200 | ⬜ 未启动 | 0% |
| packing/（Rogers/OXLZLEZ3/REUHADY…） | ~28,000 | ⬜ 未启动 | 0% |
| local/（IMJXPHR/QKNVMLB/XWITCCN…） | ~30,000 | ⬜ 未启动 | 0% |
| assembly（ch9 终装配） | — | ⬜ 未启动 | 0% |

已落地的公共地基（`Kepler/Geom/` + `Kepler/Text/`）：

- [x] Azim 方位角全层（Azim/AzimLemmas：ON 标架、角加法、AZIM_EQ/COMPL 等）
- [x] Aff 仿射符号层（affGe/affGt/affLt/affsign）
- [x] Coplanar 移植（`Kepler/Geom/Coplanar.lean`，`757a33d`）
- [x] vectorAngle/angle 引理族（`VectorAngleLemmas.lean`：SYM/RANGE/EQ_0/EQ_PI/sin/cos + 三点角；`fe3855d`–`c8c81b9`）
- [x] azim 平移桥 `azim_sub_self` + JBDNJJB 混合积 + cross_dot 族（`f16b544` 等）
- [ ] 遗留去重：`Kepler.Text.fan80/fan81`（Planarity）与 `Kepler.Text.Fan.fan80/fan81`（Fan.lean:222）重复定义，待合并

前方难点攻坚中：planarity.hl:3667 `not_cut_inside_fan`（1,515 行单证明）已在
`wip/not-cut-inside-fan` 分支切成 6 片（18a–18d4）：骨架+系数 2×2 分支+
中点事实链+azim 三分裂前两案已绿；azim=0 支已证（结构拆为独立 private 引理，
heartbeat 按 declaration 计的教训已沉淀）；仅剩 azim=π 镜像支 [BLOCK18D4]。
生产经验：对称镜像分支可下沉 flash（18c 一次通过）；工人读不了 /tmp；
单定理超 ~600 行必须拆 declaration。

## Phase 6 — 集成与交付 ⬜

- [ ] Phase 2–5 闭合后装配主定理证明（替换 Statement.lean:111 的 sorry）
- [ ] 全量公理审计终验（目标：仅 propext / Classical.choice / Quot.sound + Phase 2 限定 native_decide）
- [ ] 最终文档与复现脚本

---

## 整体估计

- **计算三线**（Phase 2/3/4）：图枚举 ✅100%；LP ✅100%；非线性流水线建成、dReal 第一层 39/176（求解层 22%），内核闭合 0%。
- **文字证明**（Phase 5，占全项目工作量 60%+）：已完成 hypermap + fan + topology + planarity 前段 ≈ 30k 行 HOL 源；待移植 ≈ 89k 行。按行数口径 **~25%**。
- **全项目粗略完成度：~49%**。

## 验证纪律（每个提交前必做）

1. `lake build Kepler` 全绿；
2. `grep sorry/admit/native_decide` 零命中（Statement.lean:111 与 Graphs.Cert* 例外）；
3. 新定理 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；
4. 工人 agent（opencode/GLM、子代理）不许 git commit，由主 agent 验证后代为提交。

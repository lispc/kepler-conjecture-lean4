# 项目总进度（Status）— 2026-09-09

> 一页看板：各 Phase 完成度、已完成什么、还差什么。每 24h 由主 agent 例行刷新（cron 自动 push）。
> 详细交接信息见 `HANDOFF.md`，阶段定义见 `PLAN.md`，长期决策见 `DECISIONS.md`。
> 当前 main @ `ae6af2f`，`lake build Kepler` 全绿（9307 jobs），
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

## Phase 4 — 非线性不等式 🟡 求解层 ~85% / 内核闭合 0%

- [x] 区间算术全层（`Kepler/Interval/`：Basic/Div/Sqrt/Ball/Trans/Expr/BBTree 分支定界，`f3cea0f`）
- [x] dyadic 精确算术、证书式 sqrt、Taylor/sin soundness、分支定界证书格式
- [x] 量产流水线：`ineq.hl` 记录解析（181 条）→ 公式 AST（176 条）→ 定义表（348 定义依赖闭包零缺失）→ RPN case JSON（176/176，`f99dd04`）
- [x] **bb_arb：C/FLINT 球算术分支定界器**（`8b7c3c4`）：RPN 求值 + dyadic 二分 + ite guard + disj + 证书 JSON 输出；sqrt8 端点精度 bug 已修（2⁻³⁰ 网格）
- [x] y 空间直跑：**65/176 闭合**（dReal 41 + bb_arb 新增）
- [x] **prep（x=y² 归一化，Flyspeck 官方形式）路线大胜**：812 条 prep 记录全解析 → 745 案例生成（四脚本 CLI 化，`59d3a1b`）；pass2 批跑（900s/4M 节点）**~98% 闭合率**（573 例时 561 闭合，2026-09-09 06:00 数据，仍在跑）
- [ ] prep 残余案例家族级分析（y 空间未闭合 ~111 条的 prep 家族覆盖核对）→ 残余再定策略
- [ ] **BBTree 证书 → Lean 内核闭合**（G4）：bb_arb 已能出 cert JSON；Lean 侧需扩展 IExpr（abs 节点）/TKind（ln）/Cert 叶（guard 符号 + disj 备选），规格在 `pipeline/interval/arb-layer.md` §3/§4
- [ ] GRKIBMP_B_V2 尖锐边界组单独处理（我们把 ≥ 加强成严格 > 导致等号边界不可闭，需 ε 余量或弱编码）
- [ ] `ineqdata3q1h.hl` 7 条 Mathematica record 单独解析
- 数字口径：底账 181 条记录（+3q1h 的 35 条）；y 空间 176 案例 / prep 空间 745 案例

## Phase 5 — 文字证明移植 🟡（全项目最大头，已全自动化）

**生产模式（2026-09-09 起）**：自动化移植 harness（`lean/scripts/auto_loop.sh` + `auto_gate.sh`，分支 `wip/auto-phase5`）：
满血 glm-5.3 批量设计骨架（**陈述定稿冻结**，docstring 嵌 HOL 原文+证法+候选引理）
→ big-pickle（opencode 免费）逐定理填空 → 机械闸五道（单文件 diff / 签名冻结 /
禁词扫描 / lake build 绿 / 公理白名单）→ 过闸自动 commit，3 次失败跳过、连续 3 跳闸熔断
→ **Kimi 主 agent 降为每日批次审计（陈述 vs HOL），审过才 ff-push 进 main**。
升级链：big-pickle ×2 → glm-5.3 ×1 → NEEDS-HUMAN。模板：`docs/phase5-worker-template.md`。

| 模块（HOL 源文件） | 行数 | 状态 | 完成度 |
|---|---|---|---|
| hypermap/hypermap.hl | 13,575 | ✅ 全书收官 | 100% |
| fan/fan.hl 系列（fan_defs/fan_misc/fan/CFYXFTY/hypermap_and_fan） | ~7,800 | ✅ 全书收官（hypermapOfFan 完整构造） | 100% |
| fan/topology.hl | 4,718 | ✅ 全书收官（`36c37c6`，dart_leads_into 全套） | 100% |
| fan/planarity.hl | 15,463 | 🟡 覆盖至 :9296（main @ `ae6af2f`，60%）；两个巨块（not_cut_inside_fan :3667-5182、AFF_GT_CUT_XFAN_IMP_EDGE_FAN :7788-8998）已全闭合并入；angle/rcone 段 8 定理骨架在 wip 由 harness 自动推进 | **60%** |
| fan/Conforming.hl | 17,033 | ⬜ 未启动 | 0% |
| fan/ 其余（polyhedron 等） | ~3,200 | ⬜ 未启动 | 0% |
| packing/（Rogers/OXLZLEZ3/REUHADY…） | ~28,000 | ⬜ 未启动 | 0% |
| local/（IMJXPHR/QKNVMLB/XWITCCN…） | ~30,000 | ⬜ 未启动 | 0% |
| assembly（ch9 终装配） | — | ⬜ 未启动 | 0% |

已落地的公共地基（`Kepler/Geom/` + `Kepler/Text/`）：

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

## Phase 6 — 集成与交付 ⬜

- [ ] Phase 2–5 闭合后装配主定理证明（替换 Statement.lean:111 的 sorry）
- [ ] 全量公理审计终验（目标：仅 propext / Classical.choice / Quot.sound + Phase 2 限定 native_decide）
- [ ] 最终文档与复现脚本

---

## 整体估计

- **计算三线**（Phase 2/3/4）：图枚举 ✅100%；LP ✅100%；非线性：y 空间 65/176 + prep 路线 ~98% 案例闭合（求解层合计 ~85%），内核闭合 0%（G4 待开工）。
- **文字证明**（Phase 5，占全项目工作量 60%+）：已完成 hypermap + fan + topology + planarity 60% ≈ 36k 行 HOL 源；待移植 ≈ 84k 行。按行数口径 **~30%**。
- **全项目粗略完成度：~52%**。

## 验证纪律

1. main 分支：`lake build Kepler` 全绿 + `grep sorry/admit/native_decide` 零命中（Statement.lean:111 与 Graphs.Cert* 例外）+ 新定理 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；
2. wip 分支：允许 sorry（骨架占位），进 main 前由主 agent 批次审计陈述保真；
3. 自动化 harness 的提交由机械闸背书 + 主 agent 审计兜底；人工派工的提交由主 agent 逐块验收。

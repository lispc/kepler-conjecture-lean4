# 项目总进度（Status）— 2026-09-07

> 一页看板：各 Phase 完成度、已完成什么、还差什么。
> 详细交接信息见 `HANDOFF.md`，阶段定义见 `PLAN.md`，长期决策见 `DECISIONS.md`。
> 当前 main @ `b537a34`，`lake build Kepler` 全绿（9302 jobs），
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
- [ ] 主定理**证明**本体（`Statement.lean:111` 的唯一 sanctioned sorry）——这是全项目的终点，依赖 Phase 2–5 全部闭合后在 Phase 6 装配

## Phase 2 — tame 平面图枚举 ✅ 100%（闭合）

- [x] 19,715 张 tame 平面图全量枚举 + 内核验证（585 个 CertShards 分片）
- [x] 公理审计通过（`make check`；601 个限定范围 native_decide 信任公理，零 sorryAx）
- [x] 新机器全量重建验证过
- [ ] （无剩余工作）⚠️ 红线：绝不 `rm -rf lean/.lake`，分片重建需 ~7 天

## Phase 3 — 线性规划 🟢 ~99.9%（收尾中）

- [x] 证书链路全通：Flyspeck 证书解析 → LP 展开/扁平化 → SoPlex 精确求解 → 整数对偶证书 → Lean 内核弱对偶 checker（`Kepler/LP/Cert.lean`、`ColMajor.lean`）
- [x] 试点图端到端闭合（行主序 + 列主序，`3cbe979`）
- [x] 生产 harness 入 git（`pipeline/lp/run/`：driver/gen_one/make_tasks/glpsol_dual）
- [x] **easy 23,640/23,640 终端内核验证通过**（含 8 个 glpsol 通道救回例）
- [x] hard_1 偏差根因修复（`d5e32af`：branch.py 逐节点数值收紧重放）
- [x] hard 批次全量跑完：19,433/19,433，19,382 通过（99.74%）
- [ ] 51 个失败例 glpsol 通道清账（**进行中**，全部 exit=130 SoPlex 数值放弃，非内核拒绝；47 个来自图 161847242261）
- [ ] 清账后更新 HANDOFF + 汇总提交（Phase 3 正式闭合）

## Phase 4 — 非线性不等式 🟡 工具链 ~100% / 量产 0%

- [x] 区间算术全层（`Kepler/Interval/`：Basic/Div/Sqrt/Ball/Trans/Expr/BBTree 分支定界，`f3cea0f`）
- [x] dyadic 精确算术、证书式 sqrt、Taylor/sin soundness、分支定界证书格式
- [ ] **~993 个非线性不等式量产**（未启动；机器算力已释放，可随时开工）
- [ ] cos/arctan 实例化、sin 范围缩减放宽（按需）

## Phase 5 — 文字证明移植 🟡（人力主线，全项目最大头）

蓝图：Hypermap(ch4) → Fan(ch5) → LocalFan(ch7) → Assembly(ch9)。

| 模块（HOL 源文件） | 行数 | 状态 | 完成度 |
|---|---|---|---|
| hypermap/hypermap.hl | 13,575 | ✅ 全书收官 | 100% |
| fan/fan.hl 系列（fan_defs/fan_misc/fan/CFYXFTY/hypermap_and_fan） | ~7,800 | ✅ 全书收官（hypermapOfFan 完整构造） | 100% |
| fan/topology.hl | 4,718 | ✅ 全书收官（`36c37c6`，dart_leads_into 全套） | 100% |
| fan/planarity.hl | 15,463 | 🟡 block 1（:35–122）已提交（`b537a34`）后**暂停** | ~1% |
| fan/Conforming.hl | 17,033 | ⬜ 未启动 | 0% |
| fan/ 其余（polyhedron 等） | ~3,200 | ⬜ 未启动 | 0% |
| packing/（Rogers/OXLZLEZ3/REUHADY…） | ~28,000 | ⬜ 未启动 | 0% |
| local/（IMJXPHR/QKNVMLB/XWITCCN…） | ~30,000 | ⬜ 未启动 | 0% |
| assembly（ch9 终装配） | — | ⬜ 未启动 | 0% |

已落地的公共地基（`Kepler/Geom/` + `Kepler/Text/`）：

- [x] Azim 方位角全层（Azim/AzimLemmas：ON 标架、角加法、AZIM_EQ/COMPL 等）
- [x] Aff 仿射符号层（affGe/affsign）
- [x] vectorAngle 定义与连续性（Planarity.lean block 1）
- [ ] **coplanar 移植**（trig2.hl:1548；planarity.hl 从 :285 起大量使用——block 2 的前置缺口）
- [ ] vector_angle 引理族（COLLINEAR_VECTOR_ANGLE 等，Multivariate-geom.ml:325+）

## Phase 6 — 集成与交付 ⬜

- [ ] Phase 2–5 闭合后装配主定理证明（替换 Statement.lean:111 的 sorry）
- [ ] 全量公理审计终验（目标：仅 propext / Classical.choice / Quot.sound + Phase 2 限定 native_decide）
- [ ] 最终文档与复现脚本

---

## 整体估计

- **计算三线**（Phase 2/3/4）：图枚举 100%；LP ~99.9%（差 51 例清账）；非线性工具链就绪、量产 0%。
- **文字证明**（Phase 5，占全项目工作量 60%+）：已完成 hypermap + fan + topology ≈ 26k 行 HOL 源；待移植 ≈ 93k 行（planarity/Conforming/packing/local/assembly）。按行数口径 **~22%**。
- **全项目粗略完成度：~45%**（计算线权重低但已近完成；文字证明权重高、刚破两成）。

## 验证纪律（每个提交前必做）

1. `lake build Kepler` 全绿；
2. `grep sorry/admit/native_decide` 零命中（Statement.lean:111 与 Graphs.Cert* 例外）；
3. 新定理 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；
4. 子代理不许 git commit，由主代理验证后代为提交。

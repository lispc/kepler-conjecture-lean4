# 交接文档（Handoff）— 2026-09-10

> 面向接手者（人类或 agent）。本文件描述项目现状、验证纪律、环境细节、
> 待办与优先级。一页进度看板见 `STATUS.md`（每日刷新），长期设计决策见
> `DECISIONS.md`，阶段计划见 `PLAN.md`，模块对照见 `docs/module-map.md`。

## 0. 一句话现状

main @ `48ff904`（`make check` 全绿，唯一 sorry = `Statement.lean`
sanctioned 主定理占位）。**Phase 2/3 已闭合；Phase 4 求解层 160/176（91%），
内核闭合（G4）未开工；Phase 5：hypermap/fan/topology/planarity 100% 进 main**
——其中 planarity 收官所依赖的**体积/测度论层已从零建成**
（`Kepler/Geom/{Volume,SectorArea,WedgeVolume,LuneVolume,SolidAngle}.lean`，
含 HOL Light `VOLUME_BALL_WEDGE`/`HAS_MEASURE_LUNE`/`VOLUME_SOLID_TRIANGLE`，
零 sorry）。下一步 Conforming.hl，流水线 `scripts/auto_pipeline_conforming.sh`
已在 wip/auto-phase5 跑（commits to wip only；待 `DWFBRQY` 等依赖 solid_of 的
定理补齐后可合 main）。

## 1. 项目目标（不变）

Lean 4 + Mathlib（toolchain `leanprover/lean4:v4.32.2`）形式化开普勒猜想：

```
开普勒猜想（密度 ≤ π/√18）
  └── Phase 5 文字证明：堆积 → fan → hypermap → 归约为"tame 图得分 < 12"
        ├── Phase 2：tame 平面图分类（19,715 张）✅
        ├── Phase 3：每图 LP 上界（43,078 个终端 LP）✅
        └── Phase 4：176 条非线性不等式（支撑 LP 松弛与局部估计）🟡 91%
```

## 2. 各 Phase 状态

### Phase 2 — 图枚举 ✅ 闭合

- 19,715 张 tame 图全量枚举 + 内核验证（585 个 CertShards 分片）；
  公理 = 标准三公理 + 601 个限定范围 native_decide，零 sorryAx。
- **绝对不要** `rm -rf lean/.lake`：分片全量重建需 ~7 天。

### Phase 3 — LP ✅ 闭合（2026-09-07）

- 43,078/43,078 终端 LP 内核验证通过（SoPlex 精确模式 + 51 例
  glpsol --exact 对偶通道兜底）。账本 `~/lprun-logs/results.jsonl`。
- 链路细节与 SoPlex 用法（`-X/-Y` 有理输出才可信）见 `pipeline/lp/README.md`。

### Phase 4 — 非线性不等式 🟡 求解层 91% / 内核闭合 0%

- 流水线：ineq.hl 181 记录 → AST 176 → case JSON（y 空间 176 +
  prep 空间 745）→ bb_arb（C/FLINT 分支定界，二进制 /tmp/bb_arb_verify，
  编译命令在 `pipeline/interval/README.md`）。
- **2026-09-09 家族级对账**：176 条 = 68 y 空间闭合 + 92 prep 家族
  闭合（prep = Flyspeck 官方 x=y² 归一化，745/745 全闭合）+
  **16 条真残余**（清单 `pipeline/interval/out/residue16.txt`：
  TSKAJXY 系 4、TEWNSCJ/PEMKWKU/TXQTPVC/IXPOTPA、QZECFIC wt0 ×2、
  GRKIBMP B V2 等）。
- 待办：16 条逐条定策略（GRKIBMP B V2 有真反例叶=尖锐边界组，需 ε 余量
  或弱编码）；然后 **G4：BBTree 证书 → Lean 内核闭合**（bb_arb 已能出
  cert JSON；Lean 侧需扩 IExpr abs 节点 / TKind ln / Cert 叶带 guard
  符号+disj 备选——规格 `pipeline/interval/arb-layer.md` §3/§4）。

### Phase 5 — 文字证明 🟡 planarity 99%，流水线已 FAIL-STOP（等压轴攻坚）

- 已收官：hypermap.hl 13,575 行 100%、fan.hl 系列 ~7,800 行 100%、
  topology.hl 4,718 行 100%。
- **planarity.hl（15,463 行）**：main 覆盖至 :15280（98.8%，批次 1-15 全部
  自动闭合，~150 枚定理）。**批次 16（收官批）FAIL-STOP**：剩 2 枚在 wip
  `PlanarityAuto16.lean` 带 sorry：
  1. `solid_of_dartset_leads_into_fan_triangle_fan`（:15370）——卡在前置
     `VOLUME_SOLID_TRIANGLE` 未移植。**它不在 planarity.hl，在 HOL Light 本体
     `Multivariate/flyspeck.ml:5883`**（measure(ball∩aff_gt) = Girard 盈余·r³/3；
     测度论证明链长）；`sol`/`dihV`/`AZIM_DIVH` 也未移植（骨架 docstring 内有
     sol 的 Classical.epsilon 规格编码方案和所有已就绪引理的 file:line）。
  2. `MOZNWEH`（:15443，全书主定理）——纯 MESON 组装，solid_of 闭合后秒过。
  攻坚路线：专项移植 VOLUME_SOLID_TRIANGLE 链（独立文件，原文需从
  flyspeck.ml 粘进 prompt——工人读不了仓库外路径）→ 补 solid_of → MOZNWEH →
  批次 16 审计进 main。**流水线目前处于停止状态**，清堵后删除
  `PlanarityAuto16.lean` 的 2 个 sorry 并 ff 合 main，整个 planarity.hl 即收官。
- 后续队列：Conforming.hl 17,033 → polyhedron ~3,200 → packing/ ~28,000 →
  local/ ~30,000 → assembly（auto_pipeline 改 HL 变量即可复用）。
- **全自动流水线**（`lean/scripts/auto_pipeline.sh`，2026-09-10 上线）：
  1. 从 `lean/scripts/auto_pipeline_state.txt` 读当前位置（起始行+批次号）；
  2. deepseek 设计骨架（陈述冻结，docstring 嵌 HOL 原文+证法+候选引理）；
  3. `auto_loop.sh` 逐定理派 deepseek 填空，**机械闸五道**（单文件 diff /
     签名冻结=删除行只能是 sorry / 禁词扫描 / lake build 绿 / 公理白名单），
     过闸自动 commit；单定理 3 次失败跳过、连续 3 跳闸熔断；
  4. 批次审计（全量 build + 冻结核验 + 全定理公理）→ ff main + push；
  5. 推进状态文件，下一批。FAIL-STOP 即停等人类。
- **Kimi 的残余职责**：每 4h 汇报 + STATUS.md + 陈述保真抽查 +
  处理 FAIL-STOP/NEEDS-HUMAN。
- 工人模板与历史教训：`docs/phase5-worker-template.md`。

## 3. 验证纪律（红线）

1. **main 零 sorry**（唯一例外 `Statement.lean:111`）；wip 分支允许骨架
   sorry，但 wip 只有在"所有被 import 的文件均无 sorry"时才合入 main。
2. `native_decide` 只允许 `Kepler/Graphs.Cert*`（601 个限定信任公理）。
3. 内核无法归约 Rat 算术——checker 检查层用 Int/dyadic，语义层 cast 桥接。
4. 合 main 前：`lake build Kepler` 全绿 + 签名冻结核验 + 公理白名单。
5. 不信任任何生成器/求解器，信任基 = Lean 内核 + 项目内 checker。

## 4. 环境备忘（本机）

- 128 核 / 503G RAM / 磁盘 98G（紧）。tmpfs 在 `/dev/shm`（252G，
  重启即失）；`/tmp` 不是 tmpfs。
- Lean 命令前 `export PATH="$HOME/.elan/bin:$PATH"`；项目在 `lean/`。
- 参考库浅克隆在 `/dev/shm/kepler-ref/`，symlink 回 `reference/`；
  重启后重克隆约半分钟（命令见 git 历史或 `reference/LOCK.md`）。
  **关键参考已入库**：`lean/scripts/planarity.hl`。
- LLM 通道（`~/.local/share/opencode/auth.json`）：
  `deepseek/deepseek-v4-flash`（付费，现任主力，~1-2 分钟/定理），
  `opencode/big-pickle`（免费，前主力），
  `zhipuai-coding-plan/glm-5.3`（订阅，设计/兜底），`glm-5.3-flash`（备胎）。
  调用：`cd lean && timeout 5400 opencode run -m <model> "<prompt>"`。
- git 身份 Zhang Zhuo <mycinbrin@gmail.com>（仓库级已设）。
- 双 3090 GPU 是别人生产容器，**绝不碰**。

## 5. 当前运行中的东西

- **auto_pipeline.sh 已 FAIL-STOP（2026-09-11，批次 16 剩 2 枚，见 §2 Phase 5）**。
  清堵后重启：`cd lean && nohup bash scripts/auto_pipeline.sh >> /tmp/auto_pipeline_driver.log 2>&1 &`
  （但需先把状态文件指到收官之后或手工收尾批次 16）。
- 日志：`/tmp/auto_pipeline.log` / `/tmp/auto_loop.log` / `/tmp/auto_gate.log`；
  状态 `lean/scripts/auto_pipeline_state.txt`。
- Kimi 侧巡检 cron：每 4h 汇报+抽查（会话内，换会话即失效需重建）。

## 6. 待办队列（优先级序）

1. ~~**Phase 5 planarity 收官攻坚**~~ ✅ **已完成（2026-09-11，main `48ff904`）**：
   体积层从零建成（`Volume/SectorArea/WedgeVolume/LuneVolume/SolidAngle`），
   `solid_of`+`MOZNWEH` 已证，planarity.hl 100% 进 main。
2. **Conforming.hl 移植（进行中，wip/auto-phase5）**：定义层
   `Kepler/Text/ConformingDefs.lean` 已就位；流水线
   `scripts/auto_pipeline_conforming.sh` 已跑批次 1-2。**关键更新**：原 blocked 的
   `DWFBRQY`（Conforming.hl:550）依赖的 `solid_of` 现已可证——应把
   `auto_pipeline_conforming.sh` 的 `BLOCKED` 清空（或从 wip 里已跳过的
   `DWFBRQY`/`nonconformin_fan_imp_n_fan_ge0` 重新派工），跑通后即可把
   Conforming 合 main。Conforming 228 定理中仅极少数依赖立体角公式，其余为
   `sol` 代数/测度/径向（`sol_spec` 即可）。
3. Phase 4：16 条残余策略 + G4 内核闭合（见 §2 Phase 4）。
4. Phase 6：主定理装配 + 终验。
5. 零散：`Kepler.Text.fan80/fan81` 重复定义去重；`ineqdata3q1h.hl` 解析。

### 体积层文件（2026-09-11，全部零 sorry、仅标准三公理）

`Kepler/Geom/` 下（均 import 进 `Kepler.lean`）：
- `Volume.lean`：`radialNorm`、`EventuallyRadial`、`sol`、`sol_spec`、
  `volume_real_add_left/right`、`volume_real_smul`、`radialNorm.volume_scaling`。
- `SectorArea.lean`：`sector_area`（2D 扇形面积 = ρ²θ/2）。
- `WedgeVolume.lean`：`volume_ball_wedge`（HOL `VOLUME_BALL_WEDGE`）。
- `LuneVolume.lean`：`arcV`/`dihV`、`azim_dihv_same`、`wedge_eq_affGt`
  （`WEDGE_LUNE_GT`）、`volume_ball_affGt(_simple)`（`HAS_MEASURE_LUNE(_SIMPLE)`）。
- `SolidAngle.lean`：`volume_solid_triangle`（HOL `VOLUME_SOLID_TRIANGLE`）。
HOL 源在仓库内：`lean/scripts/flyspeck_multivariate.ml`（供后续 Volume/Packing
章节引用）。

### 体积层新文件（2026-09-11）

`Kepler/Geom/Volume.lean`（已 import 进 `Kepler.lean`，`lake build Kepler` 绿）：
- `radialNorm r x C`（HOL `radial_norm`）
- `EventuallyRadial x C`（HOL `eventually_radial`）
- `sol x C`（HOL `sol`，`Classical.choose` 选择见证半径）
- `volume_real_add_left/right`、`volume_real_smul`（实值体积的平移/标度）
- `radialNorm.volume_scaling`（HOL `lemma_r_r'`）
- `sol_radius_independent`、`sol_spec`（HOL `sol_spec`）
公理审计：仅 `[propext, Classical.choice, Quot.sound]`，零 sorry。

## 7. 已知坑（近期新增；历史坑见 git 历史与 worker 模板）

- **闸的三个已修 bug**（教训：GATE-FAIL 先怀疑闸）：git diff 路径要
  `--relative`；公理全名=命名空间.定理名（非模块名）；`#print axioms`
  长输出会折行，匹配前先 `tr '\n' ' '`，另有 "does not depend on any
  axioms" 合法情形。
- 改动正在运行的 bash 脚本会被 bash 按字节偏移续读——先停再改。
- `pkill -f 'opencode run'` 会自匹配杀自己——用 `pkill -f '[o]pencode run'`。
- nohup 包装壳的 pid ≠ 真循环 pid，用 `pgrep -f 'auto_l[o]op.sh'` 取。
- 验收构建必须自然退出：掐死时 error 未 flush，grep 0 是假绿。
- 整条命令链末尾加 `&` 会把整条链后台化，前台输出全丢——分两条命令。
- 工人（opencode）读不了仓库外路径（external_directory auto-reject
  会杀会话）：HOL 原文一律粘贴进 prompt 或放仓库内。
- 标量-标量乘在 ascription 里写 `*` 不写 `•`（isDefEq 死循环）。

## 8. 快速自检（接手后第一件事）

```sh
cd /home/scroll/repos/kepler-conjecture-lean4
export PATH="$HOME/.elan/bin:$PATH"
git log --oneline -3 main
make check                      # build + 公理审计，应全绿
tail -20 /tmp/auto_pipeline.log # 流水线状态（若在跑）
```

## 2026-09-12 里程碑：Conforming.hl 全书收官（main @ d77c13f）
- **fan/Conforming.hl（17,033 行）23 批 ~230 枚定理全部闭合，零 sorry、标准公理，已合入 main**（`make check` 绿）。批次 1-18 由 opencode-CLI 流水线完成；批次 19-23（含巨证 `lemma_connect_hypermap`，HOL 证明 ~1900 行）由主 agent 直接以 Task sub-agent 完成——CLI 派发方式已废弃（ARG_MAX 128KiB 上限 + 无必要）。
- **新架构**：主 agent 编排（派 worker / 跑 `auto_gate.sh` 验收 / git / state），sub-agent 干活；多批次用 `git worktree` 分道（lane-bNN 分支 + `cp -al` 硬链接 `.lake`）并行，完成后 merge 回 wip 再合 main。
- **两阶段攻坚法**（难定理标配）：先派"规划者"出可执行证明计划（目标分解+have 链+辅助引理清单+读取预算），再派"执行者"照计划落地——TXFBALB、`conforming_diagonal_fanadd1`、`lemma_connect_hypermap` 均如此拿下。
- **教训**：W2 曾冻结出假辅助命题（单面 vs 相邻双面，正四面体反例），被 W3 用反例挡下，W4 重述为交叉式（下侧∈face(w,v)、上侧∈face(v,w)，由 azim 符号决定）后闭合。假命题审查是流程的一部分。
- **state**：`scripts/auto_pipeline_conforming_state.txt = DONE 23`。下一目标：`polyhedron.hl`（~3.2k 行，依赖 Conforming 已就绪）→ packing → local → assembly。

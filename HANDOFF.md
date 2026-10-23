# HANDOFF.md — 交接文档（2026-10-23 更新，面向接手的 coding agent）

> 2026-10-10 曾退役并入 PLAN/STATUS；**2026-10-12 用户令恢复为独立交接文档**。
> 本文是接手入口，读完即可开工；权威计划 = `PLAN.md`（冲突时以它为准），
> 实时看板 = `STATUS.md`，债务刻度 = `DEBT.md`，决策日志 = `DECISIONS.md`。
> 车道工人开工另必读 `docs/fill-worker-playbook.md`。

## 移交令（2026-10-21，**已作废**）

> 用户令 2026-10-21 曾令 Phase 5 → opencode（ZCode 只收工三件）。**同日用户
> 改主意作废**："我改主意了。不用 opencode 了。以后还是你照旧。"——**ZCode
> 编排者照旧负责全线（含 Phase 5/TameSpine 接力、Phase 3/4/6）**。收工三件
> 已完成（root runner 终账 `95e6a037`/TameSpine 批 67 salvage `73f14f76`/
> TM 舰队终验 `f1a30a56`），Phase 5 产线由 ZCode 从批 68（RXOKSKC :523-:1105
> 章末处方全备）继续。接管简报 `docs/projects/phase5-opencode-takeover.md`
> 内容仍作 TameSpine 接力指南参考使用（其中"opencode 负责"字样读作"编排者"）。


---

## ⚡ 当前状态速览（2026-10-23 收波更新）

> **基线：main @ `e0d14810`，工作树干净，已推 origin/main。** e2e 可达
> 债务源 **133**（地图 2026-10-23；起点 149），可达声明 **216,032**，
> 可达公理 **624**（全部 `native_decide` 特许 shard，无异常公理）。
> DEBT.md token 总量 **44,448**（2026-10-23 重生成；42,889 枚 bound LP
> 叶占绝大部分，按旧口径扣 43,078 后可比 **1,370**；真正非 LP 文本债
> 1,559）。本波（10-22/23）六条线全部收口。

- **在飞**：无。三车道均已交付；PA25 试填按源数守恒规则回退。
- **最近提交**：`e5cd4abb` LP 审计 → `d6c72ee8` PA15 → `4053ef5a` R1 4 案
  → `5d57f21e` W6 侦察 → `fab33d0e` PA11 → `e0d14810` PA25 负结果。
- **e2e 133 源结构**：Assembly 81（57 `nliRest*` + 8 `nliTsk*` + 7
  `nliCell3*` + 5 直挂 + `fcdjdot`/`jcajydu`/`tameCorrespondenceIso`/
  `lpArchiveCertificatesDebt`）、PA25 38（**28 `real_model_*`** + 10 其他）、
  TameLp 6、PA18 2（`cc_pe_exists` + `pa18_ccCell_swap`）、其余 6
  （PA3/PA21/PA2/LocalAuto16/LocalAuto1/ContraFan 各 1）。
- **Phase 4**：prep R1 已闭 **22 案**（pilot 5 + P2 12 + 2125 + rest 4）；
  P3 2125 全树 132/132、46,099 叶；R1 余 10 个 closed 候选；R2/R3 未动。
- **Phase 3/LP**：root 19,237 全部有 exit=0 账（残余失败/缺失 0），试点
  5/5 sha 逐字节复现；easy 4,362 + hard 19,290 **必须重跑**（2026-09
  账本/产物不在本机）；W6 组合覆盖层真证、终端语义是多波项目；终装配
  olean ≈0.9–1 TB，本机 177 GB free ⇒ 需大磁盘。
- **环境**：M3 Pro 12C/36G；本波峰值约 26 GB、空闲 80%；磁盘 177 GB free。
  单 build 串行、`nice -n 19`、禁 `-j`/`-K`、空闲 <50% 暂停。

---

## 0. 30 秒速览

用 Lean 4 + Mathlib 以"证书化计算"范式重造 Kepler 猜想端到端形式化证明
（蓝图 = Hales《Dense Sphere Packings》/ Flyspeck）。当前形态：端到端对象
`the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean`）已立于主定理形态
（M5′ ✅）， axiom 面 = sorryAx(3 冻结接口) + 624 特许 Graphs shard + 标准三。
主战场 = **Phase 5 文字证明清债**（贪心触达制：每一步最大化接触既有已证质量），
用 5-6 个并发 sub agent 车道滚动生产，编排者统一闸/提交/推送。终局 = 会师
（M5″）后清叶，零 sorry 组装（M5/G5），干净机器复现交付（M6/G6）。

## 1. 现状（2026-10-23 收波时点，main @ `e0d14810`，工作树干净；无在飞车道）

### 1.1 阶段完成度

| Phase | 内容 | 状态 |
|---|---|---|
| 1 | 陈述形式化（`Statement.lean`） | ✅（:111 占位 sorry sanctioned，终版退役） |
| 2 | tame 平面图枚举（19,715 图 + 完备性证书） | ✅ `tame_classification` 闭合 |
| 3 | 线性规划（43,078 终端 LP 内核验证层） | ✅ 求解/checker 层；2026-10 审计：root 19,237 全账、5/5 sha；easy/hard 23,652 需重跑；W6 覆盖桥侦察完成，语义移植多波；叶户待灌数据 |
| 4 | 非线性不等式 | 🟡 求解层 68/176；内核 prep R1 22 案（P3 2125 全树 132/132）；重计算 deferred |
| 5 | 文字证明移植 | 🟡 主战场；e2e 直源 133；PA11/PA15 已归零；PA25 28 `real_model_*` 待 `cc_pe_exists` |
| 6 | 集成交付 | 🟡 e2e 已立；余 3 接口 + 133 源 + 占位去重 + 终验 |

里程碑：M0-M4 ✅（M4 重计算 deferred）、**M5′ ✅**（2026-10-10）、
M5″ 会师 🟡、M5=G5 零 sorry 组装 ⬜、M6 交付 ⬜。

### 1.2 债务与覆盖度账（2026-10-23）

- **DEBT.md 总量 44,448**（2026-10-23 重生成，旧 44,478；净 −30）。本次
  `--with-spine` 因 `debt_ledger.py` 传相对根给 `spine_axioms.py` 报错
  （已修：改传 `os.path.abspath(ROOT)`；脊柱节留待下次重跑，当前可达债务
  以 e2e 地图 133 源 / 624 公理为准）。
  其中 42,889 枚是 bound LP 叶（deferred-compute，灌数据即清，**勿当
  文字债攻击**）；按旧口径扣 43,078（含已闭合的 189 infeas 叶）后
  **可比口径 1,370**（10-13 基线 1,568，净 −198；对上一版 44,478 为 −30）。
  非 LP 文本 + root 实为 1,559。
- 非 LP 大户（新账本）：PA25 84 / LocalAuto1 82 / LocalAuto22 82 /
  LocalAuto32 65 / LocalAuto28 63 / LocalAuto34 60 / LocalAuto6 60 /
  LocalAuto24 53 / LocalAuto38 47 / PackingAuto4 39 / PackingAuto18 38。
- **e2e 刻度的权威口径**：`docs/e2e-reachability-map.tsv`（133 直源 /
  624 公理 / 216,032 可达）。DEBT token 总量含大量不可达/模板债，派工
  顺序看 e2e 地图与贪心排名，不看 token 总量。
- 全库三态覆盖度（`docs/module-map.md` 普查节，2026-10-12 实测）：
  HOL 6,540 定理 / 686k 行 → 已移植 38% / 证书替代 20% / 未移植 42%
  （按行 40/28/32）。无半成品章。

### 1.3 刚发生的事（2026-10-22/23 波，六线全收口）

| 线 | 结果 |
|---|---|
| PA15 DIHX_SYM（`d6c72ee8`） | `DIHX_SYM` + `LEFT_ACTION_LIST_2/3_EXISTS` 闭合，+1018/−3，闸 ×3 PASS；未消费 `HDTFNFZ`/`LEPJBDJ`；PA15 sorry 15→12；e2e 137→136 |
| R1 rest 4 案（`4053ef5a`） | 3078028960(1358)/JNTEFVP_1(3142)/2073661826(5929)/4680581274 cayleytr0(5422)，合计 15,851 叶/206 shards/4,083 s；四闸 PASS；R1 18→22；新雷区 #470（shard 缺 maxRecDepth），`emit_lean.py` +2/−1 |
| LP root 审计（`e5cd4abb`） | root 19,237/19,237 exit=0，残余失败/缺失 0；1,800 条 exit=1 全是环境性重试；4 pilot + 1 失败重试样本 **5/5 sha 逐字节复现**；计划 W1–W7 写入 `lane_snapshots/lpaudit/IMPORT_PLAN.md` |
| LP W6 侦察（`5d57f21e`） | 组合覆盖层真证（DFS 终端序/注册表覆盖/tame_result_lemma/三接口归约，267 行骨架 build 绿）；真正缺口=终端 LP 语义（HOL ~8,700 行 → Lean 5k–10k 行，多波）；报告 `docs/scouts/lp-w6-coverage-scout.md` |
| PA11 LEPJBDJ（`fab33d0e`） | `rogersInterVLemma`/`k3Subset`/`k2Case` 全闭，+434/−48，闸 PASS；`k3Subset` 不用 tainted `mxiExplicit`，改用 clean PA7/PA8 kit；LEPJBDJ/LEPJBDJ_0 值级标准三；e2e 136→133 |
| PA25 real_model（`e0d14810`） | 勘误 28 枚（非 25）；28/28 值级根在 `cc_pe_exists`/本文件骨架/缺 ALT kit；8 件试填 +177/−8 应用后地图 133→131，但新暴露 6 源（含 PA10 `RVFXZBU` 经 PA20 回归），净 −2=债务搬家，按守恒规则回退；试填留快照 |

**新雷区（详见 §5.7）**：①R1 深树 shard 的 `by decide` 需
`maxRecDepth 1000000`；②PA25 类“填 8 件净 −2”的债务搬家——合并前必须
重跑地图看新增源；③类型级 sorryAx（`#print axioms`）≠ 值级 direct 源
（地图口径），两者要分开记；④`cc_pe_exists` 已是 28 枚 real_model 的
唯一主根。

### 1.4 环境与基础设施

- Apple M3 Pro 12 核/36GB（2026-09-28 起；旧 128 核服务器报废）。Lean
  v4.32.2 + Mathlib v4.32.2（elan 锁定，勿升级）。`lake` 在 `~/.elan/bin`。
- 工人 = ZCode sub agents（后台 lane），编排者 = 主 agent。
- **已知故障模式**：① 5 小时用量配额帽（车道会死于"已达到 5 小时的使用上限"，
  重置后**以续作任务书重发**：先核盘上半成品、续作而非重写）；② API 连接超时
  等基础设施死亡（**salvage 协议**：对盘上 WIP 跑全文件编译探针——EXIT=0 则
  按规走闸落地，编译烂则诚实留盘入账等下一波，**绝不回滚丢工作**）。

## 2. 工作模式（怎么干活）

### 2.1 两种角色

- **编排者（主 agent）**：唯一 git 写入者。派工→收交付→闸→commit+push→
  补线（保持 5-6 线在飞，除非用户另令）→维护账本文档。
- **车道工人（sub agent）**：只改自己的 lane 文件，零 git/零 build 全项目/
  零 auto_gate。纪律全文见 `docs/fill-worker-playbook.md`（必读）。

### 2.2 车道纪律（对工人）

只改 lane 文件一个 tracked 文件；草稿/探针放 /tmp；只许删 sorry/空行/注释行；
**陈述冻结**；新增行禁词 `sorry`/`admit`/`native_decide`（连注释都不行）；
新辅助引理必须自身零 sorry；新 scaffold sorry 必须带 `-- NEEDS` 记账；
单 lake 进程串行；交付报告须含探针退出码与 NEEDS 清单。

### 2.3 编排者闸门实操（最容易踩坑的一段）

```bash
# 在 repo 根目录跑（闸内部自己 cd lean/）：
LANE_FILES="Kepler/Text/Xxx.lean,scripts/auto_gate.sh" \   # ① lean-相对！逗号分隔！
GATE_ROOTS="Kepler.Text.A Kepler.Text.B ..." \             # ④b 闭包根
bash lean/scripts/auto_gate.sh Kepler/Text/Xxx.lean <THM>  # ⑤ 公理审计对象
```

- **规则①**：盘上全部 tracked 脏文件必须被 LANE_FILES 白名单覆盖——
  并行车道的脏文件也要列进去（只是放行，不会被编译）。闸脚本自己改了
  （EVOLUTION）也要加 `scripts/auto_gate.sh`。新文件先 `git add`（否则对
  rule① 不可见 → "no tracked changes"）。
- **规则②**：陈述冻结。可删=sorry 行/空行/注释/docstring 内部/EV11 $sorbody
  （HEAD 带 sorry 声明的全文）/EV13 块移（删了又逐字加回）/EV20 重复件
  （import 同名提供+语句归一化全等；证明体不比对；脏 provider 不算）。
- **规则③**：sorry 净账（EV19 bare netting + EV21 代码行口径）。新 scaffold
  走 `NEW_SORRY_ALLOW=N` + 每枚带 `-- NEEDS`。
- **规则④/④b**：`lake build` 改动模块 + 根闭包，**从源码重建 stale import**
  ——所以脏的下游 import 会挡闸（活案：PA24/PA20 曾被 PA7 半成品挡，排队
  等 PA7 落地连闸；不要碰 mtime 绕行=削弱闸）。默认七根=Hypermap/PackingConcl/
  LocalConcl/LocalBridge/TameLp/AzimBridge/ContraFan；某根被 WIP 污染时裁根
  （活案：PA24 在盘时七根去 PackingConcl）。LA5 是汇（无人 import 它），
  永不污染别人。
- **规则⑤**：`#print axioms <THM>` ∈ {propext, Classical.choice, Quot.sound,
  sorryAx}；私有名传 mangled 名或依赖 EV18 自动发现。
- PASS 后编排者分主题 commit（交付与闸演进分笔）+ push。

### 2.4 贪心触达制与重排名循环（派工依据）

战略全文 = PLAN §5。机制：`lean/scripts/dep_scan_snippet.lean` +
`dep_sweep.sh`（逐模块直接依赖边扫描，import 擦 value 故走源码副本重
elaboration；私有名 mangling 与 `_stdin` 重写已在脚本内处理）→
`cleanable_rank.py`（不动点算 cleanable(L)：假设叶子 L 证毕连带变净的
tainted 常量数）→ TOP-N 给编排者。deferred-compute 叶（LP/prep/重放）不入
排名。**每当一批根波落地，对受影响模块局部重扫→重排名→按排名派工**；
头条指标 = meeting-ready 数（taint 路径全终结于 deferred-compute 叶的
tainted 常量）。上次全量排名的头部：ccPe1/ccUh/ccKe（PA18 cc 链，单根 `cc_pe_exists`）、
s_leaf/leaf_rank（PA25）、pack_nonlinear_rest（PA21 62 bank pin 死）。
**2026-10-23 更新**：PA11 三私件闭合后，`cc_pe_exists` 成为 28 枚
`real_model_*` 的唯一值级主根；下一轮局部重扫应聚焦 PA18 cc-chain 与
K3/K4 WIM kit（`K3_CC_WIM_ALT`/`K4_CC_WIM`/`FUEIMOV_3`/
`CC_4_BETA_BUMP_0`/`MCELL4_GG`）。

### 2.5 陈述冻结与 SF 通道

陈述改动仅经 SF 通道：`docs/statement-fix-proposals.md` 提案条目（须引 HOL
出处）→ 用户批准 → 执行版补丁存档
`docs/statement-fix-proposals-patches/` → 以 `GATE_MODE=STATEMENT-FIX` +
`SF_PATCH`/`SF_ITEM` 过闸（工作区 diff 与存档补丁逐文件 multiset 相等）。
定义体修复走 `GATE_MODE=DEF-FIX`（charter 指定净 sorry 配额）。命名空间/
可见性修复循 arcLengthICD 先例。

### 2.6 文档纪律

新文档按生命周期归位：侦察→`docs/scouts/`；交接/班次→`docs/handoffs/`；
专项设计→`docs/projects/`；产物/探针→`docs/assets/`；常住参考留 `docs/`
根层并在 `docs/README.md` 登记。编排者每波收工职责：e2e-debt-map.md 增量节、
重大波次随更 module-map.md 普查节、批次末 DEBT.md 重生成
（`python3 lean/scripts/debt_ledger.py . > DEBT.md`）、STATUS.md 刷新。

## 3. 短期计划（接手即干，按优先级；2026-10-23 收波时点）

### 3.1 可立即派工的车道

1. **PA18 `cc_pe_exists` 侦察/攻坚（最高优先）**
   - 位置：`lean/Kepler/Text/PackingAuto18.lean:206`；HOL
     `leaf_cell.hl:1052-1084`。文件内 NEEDS：证明 = `FUZBZGI_1` +
     `JDWAWAY` sign-split；`FUZBZGI_1` 消费 PA7 仍 sorry 的 `XYOFCGX`；
     `YBZFUPO` 需“1 维多胞形 = 线段”分类（仓库/Mathlib 无现成件）。
   - 影响：28 枚 `real_model_*` 的唯一值级主根；cc 链约 280 下游类型
     污染；闭合后 PA25 已试填的 8 件可原样转真（快照 `pa25real`）。
   - 建议：先派**侦察车道**拆 HOL 证明、评估 GIANT 规模与 PA7 `XYOFCGX`
     依赖，产出分波施工图；不要直接让填充车道硬啃整件。

2. **K3/K4 WIM kit（PA25 直接解锁面）**
   - 源：`K3_CC_WIM_ALT`（PA25:3704）、`K4_CC_WIM`（PA25:3684）、
     `FUEIMOV_3`（PA18:4121）、`CC_4_BETA_BUMP_0`（PA25:5878）、
     `MCELL4_GG`（PA25:3593）。
   - 这些是 PA25 试填暴露的 6 个新源（另含 PA10 `RVFXZBU` 经 PA20
     `gammaX_gamma3f → p20g_perm_wit3` 的回归路径）；`NO_4CELL_IMP_K3`
     已装配 `K4_CC_WI_ALT`/`K4_CC_WIM`/`STEM_EDGEX`/`FUEIMOV_3` 分支，
     缺的是 K3/K4 WIM 与 `FUEIMOV_3` 本体。
   - 建议顺序：`FUEIMOV_3`（同 stem 同胞 ⟹ 表相等 ⟹ 首两点相等 ⟹
     共线撞 `hnc`，HOL 在案）→ `K3_CC_WIM_ALT` → `K4_CC_WIM` →
     `CC_4_BETA_BUMP_0`/`MCELL4_GG`。规模远小于 PA18，适合先拿分。

3. **LP W6-A/B/C（数据 + 最小语义，Mac 可做）**
   - 依据 `docs/scouts/lp-w6-coverage-scout.md` 与
     `lane_snapshots/lpw6/LPCoverage.lean`。
   - **W6-A**：39 个 `.dat`（404 MB，在库）→ light `LpGraphCert` 树
     （split 型 + face + precision/infeasible 旗标）+ archive 对齐；
     `hdata`/`hcov` 用 `decide`/`rfl`。机械、产物小。
   - **W6-B**：`lp_fan`/`lp_cond`/`lp_tau` 定义 + `contravening_lp_fan`
     （复用 `contraveningFan`，补 fully_surrounded / 2.52 距离 /
     ball_annulus / packing）。
   - **W6-C**：`yeList`/`ynList` + `split218/236/225`、`split4/5/6`
     （纯实数 `linarith`/`nlinarith`）。
   - **不要**从 `prove_flyspeck_lp_step1`/`compute_all` 起手（依赖 127 族
     不等式数据库与 LP 数据对齐，是第 3–4 波）。

4. **R1 收尾 10 案（机械、e2e 中性，适合填充车道）**
   - 余：9424/14266/40785/49998/54771/75965/133228/154721 +
     `6096597438 b`/`ZTGIJCF0`。
   - Runbook：`lane_snapshots/r1rest/pipeline/build_case.sh` +
     `lane_snapshots/prep2/DELIVERY.md` §8；纯多项式直接复用，含 atan/sqrt
     需 `--fill`；深树 shard 记得 `maxRecDepth 1000000`。
   - 注意：R1 产物是 prep 材料层，`Interval.Cases.*` 尚未被 Assembly/Text
     根 import，闭合不直接改变 e2e 源数。

5. **624 公理 manifest + 抽样 replay（信任加固，P0）**
   - 23 条 `Assembly.GoodListShard*` + 601 条
     `Graphs.CertShards.*`/`CertTri/Quad/Pent/Hex`。
   - 建 manifest（模块/名字/shard 范围）+ 抽 3–5 shard 从源码重放，
     确认 `native_decide` 公理与证书内容一致；不削 e2e，但这是当前
     唯一非 sorry 信任面。

6. **PA25 已试填 8 件复用**
   - 快照 `lane_snapshots/pa25real/PackingAuto25.lean`（+177/−8，8 件
     真证、闸 PASS）。等 `cc_pe_exists` 或 K3/K4 WIM 落地后原样套用，
     再跑地图确认无新暴露源。

7. **TameLp 6 源 / nli 大案（暂缓）**
   - TameLp 6 源依赖 Polar_fan/Local_lemmas/Face3 未移植深章，先侦察
     再排；`main_nonlinear_terminal_v11` 链是 Phase 4 终端，不在本波。
   - nli A2 rest 9（964,792 叶 / 2,775 shards）冷构建 40–45 h，deferred。

### 3.2 待用户拍板项（不要自行做）

- **LP root W1–W3**：19,237 条重发射 + 构建，302.7 CPU-h ≈ **6.3 天
  @2 workers**，root olean ≈400 GB；需要明确窗口。
- **LP easy/hard 重跑**：23,652 条（easy 4,362 + hard 19,290），
  675–1,370 CPU-h ≈ **14–28.5 天**；2026-09 账本/产物丢失，必须重跑；
  51 例 SoPlex 放弃的 glpsol 尾部 id 清单也丢失。
- **W6 全语义移植**：HOL ~8,700 行 → Lean 5k–10k 行，多波；先 W6-A/B/C
  还是全力 W6，需要定节奏。
- **终装配 W7**：需 ≥1.5 TB 磁盘（本机 177 GB free），或换机器。
- **历史 SF 提案**（`docs/statement-fix-proposals.md` 排队项）与
  TameSpine Assembly §2b 五枚 True-placeholder DEF-FIX flip。
- **624 manifest** 是否现在插入（P0 信任项）。

### 3.3 deferred-compute（Mac 不做，等强机器）

| 项 | 说明 |
|---|---|
| A12：43,078 LP 数据灌装 | 审计+试点已完成（2026-10-23，`lane_snapshots/lpaudit/IMPORT_PLAN.md`）：root 19,237 可重发射灌装（≈6.3 天 @2 workers）；easy/hard 23,652 需重跑；覆盖桥 W6 独立多波；终装配需 ≥1.5 TB 磁盘 |
| A11：993 证书 + 81 G4 residue | 重跑产物丢失清单见 DECISIONS 2026-09-28 |
| 92 prep 家族重求解 | 附带策略决策（TM vs BBTreeGD）；R1 余 10 案先做 |
| Phase 4 两巨兽重放 | 784/6321、770/12553（olean 保留可幂等续跑） |

## 4. 长期路线（细节以 PLAN.md 为权威）

```
现在 ── e2e 清债（133→0；PA18 cc-chain / K3-K4 WIM / Assembly nli /
        PA25 / TameLp）──> M5″ 会师
     ── Phase 3 并行：W1-W3 root → W4/W5 重跑 → W6 语义 → W7 终装配
     ── 清叶 / 占位退役 / 全量公理审计 ──> M5=G5 零 sorry
     ── 复现文档 + 干净机器 make reprove ──> M6
```

已知真数学缺口（非工程量）：PA18 `cc_pe_exists`（cc 链 GIANT，
HOL `leaf_cell.hl:1052-1084`；`FUZBZGI_1` + `JDWAWAY`；`FUZBZGI_1`
依赖 PA7 `XYOFCGX`；`YBZFUPO` 需 1 维多胞形 = 线段分类）、K3/K4
WIM/`FUEIMOV_3`（edge-rigidity kit）、pivot 反向 k=3/4
（GRUTOTI 最后一块）、GRKIBMB 尖锐边界、PA24 B2 退化情形。
风险排序：LP 灌装/终装配磁盘 > PA18 GIANT > Phase 4 重计算 >
tame 章体量 > Mathlib 缺口 > 陈述保真（SF 通道）。

## 5. 已知坑（血泪清单，新人必读）

### 5.1 Lean/tactic 雷区

- **ε-词表 postponed-unification 心跳卡死**：`have h : <显式类型> := <应用>`
  再 `exact h`，勿让 ε 类定义卡 whnf。
- **rw 全局污染**：用显式 `have` 隔离；`set` 可能改语境。
- **`obtain ⟨-,…⟩ := h` 会清掉 h**；槽位数含 ∃ 主变量（localFan_p2=8 槽，
  FAN 第 6 个）。
- **迭代闭包**用 `Function.iterate_succ_apply'`，裸 rfl 不行。
- **`Kepler` 的 `projection v d` 第一参是向量**（HOL 参元序相反）。
- 探针同名声明会被静默跳过证明体——**改名探针法**；错误掩蔽链：探针必须
  `grep -icE 'error' = 0` 迭代到零。
- SOL_SOLID_TRIANGLE 的 c-项 = `dihV v0 v3 v1 v2`（不是表面对称形）。

### 5.2 闸与脚本坑

- LANE_FILES 必须 **lean-相对**路径（闸先 cd lean/）；
- rule④ 从源码重建 stale import（mtime 判断）——脏 import 挡闸，按依赖序
  排队连闸；
- docstring 折行以 sorry 开头会进规则③计数（EV21 已修，新增散文避开行首
  sorry）；
- 单行骨架 `… := sorry` 的删除靠 $sorbody 豁免——陈述重排别超出"空白归一化
  全等"；
- `-- NEEDS` 是新增 scaffold sorry 的唯一合法通道。

### 5.3 shell/环境坑

- **Bash 工具的 cwd 跨调用持久**——`cd` 过一次后续全歪，长命令一律
  `cd /Users/zhangzhuo/repos/kepler-conjecture-lean4 &&` 开头（血案两次）；
- macOS 无 `timeout` 命令（闸内置 perl 实现）；zsh 里 `echo ===` 会被解析
  成命令；BSD grep/awk：`\+` 静默空（用 `[+]`）、`\b` 在 awk 不可用
  （POSIX `([^[:alnum:]]|$)`）；
- 后台命令的 `cd` 不改持久 cwd；git index.lock 撞锁重试即可；
- `#print axioms` 长输出折行须 `tr '\n' ' '` 再看。

### 5.4 协作故障模式

- 车道配额死/API 死：见 §1.4（续作重发 / salvage 协议）；
- 并行车道互写干扰闸：LANE_FILES 白名单 + 根集裁剪 + 排队连闸；
- 会话超长：交接断点写进 `docs/handoffs/`，接力者从 HANDOFF.md 重入。

### 5.5 Lake 构建旗标（2026-10-20 十二发波首发事故）

- **Lake 5.0.0（Lean 4.32.2 捆绑）没有 `-j` 也没有 `--jobs` 旗标**——`lake build
  -j2` 直接 `unknown short option '-j'` EXIT=1（十二发波基线预热构建即死于此，
  车道自救去掉旗标后 8700 jobs 绿）。并发控制没有 CLI 开关，纪律是**操作性的**：
  每 lane 一次只跑一个 lake build、跨 lane 串行、只用热缓存（rsync 自主仓后仅
  变更闭包重编）、冷重建只在安静窗口做。
- **`-K<未知键>` 陷阱**：`lake -Kjobs=2 …` 不报错、静默接受，且任何 `-K` 键变更
  触发 workspace reconfigure → 共享热克隆缓存被毒化，下一次普通构建全量回放
  （实测 1:06 重放 9491 jobs）。共享克隆上**禁止用 `-K` 试任何键**。
- 冷全树重建是 36G 内存事故（10-16/17）的根因形态：PA 级模块 6–8G/个、shard
  7G/个，Lake 默认并行度会同时拉起多个 elaborator——冷重建前先看
  `memory_pressure -Q` 与在飞 lean 进程。

### 5.6 `reasoning_content` 400 与 provider 故障处置（2026-10-21 专项调研，报告 `lane_snapshots/rcprobe/REPORT.md`）

- **症状**：异步 subagent 运行中随机死于 `[invalid_request_error] The reasoning_content
  in the thinking mode must be passed back to the API`（今日 4 次，7–51 分钟不等）。
- **根因（调研结论）**：OpenCode Zen Go 中转对 DeepSeek thinking 模式的
  `reasoning_content` 回传做严格/不稳定校验；ZCode 侧固定发 `reasoning_effort:"max"`
  （`zcode.cjs:2112`）且对"本轮 reasoning=0"的 tool turn 省略 `reasoning_content`
  （转换器 `zcode.cjs:2102`）。公开 issue 佐证：Cline #14965（同 route/model 同 400）、
  OpenCode #48180（echo-back × effort 并存才 400）、ZCode #676/#938。**非历史裁剪、
  非"跑太久"**——幸存者形态相同，属请求/边缘副本间发性（长会话近似确定性）。
- **处置协议（outcome-proven）**：①遇该 400 **绝不重试/唤醒同一 subagent**——用磁盘
  交接状态（PROGRESS.md + 文件快照）**新开**一个窄任务 subagent（已验证零风险）；
  ②重启前先 `cp ~/.zcode/cli/rollout/model-io-<sid>.jsonl` 保住失败请求体
  （3 文件轮转 `eHs=3` 会秒吞证据，`modelIoFullRetentionEnabled=false`）；
  ③车道任务书一律带"每步落盘+5 分钟 PROGRESS 锚点"条款。
- **2026-10-21 17:13 复发一例**：AJRIPQN 侦察车道运行 22 分钟后死于同一 400；报告
  已完整落盘（零产物损失）。当时 `zcode.cjs` 补丁已打，但进程是否已重启未知；若用户
  重启后仍复发，则 v1 补丁不足，按 `~/bak/repatch_zcode.sh` 回滚或改走"换 provider /
  不发 effort"路线。
- **根治选项（需用户拍板/上游修复）**：把 subagent 模型从
  `opencode-go-chat/deepseek-v4.1-flash/reasoningLevel=max` 换非 thinking 模型或
  另一家 provider；或该 route 不发送 `reasoning_effort`。最小客户端修复点 =
  `zcode.cjs:2171` col 6296 的"anthropic-only 思考拒绝修复重试"扩展到
  openai-compatible `reasoning_content` 400。

### 5.7 LP/PA25 账目与验证雷区（2026-10-23 新增）

- **类型级 vs 值级**：`#print axioms` 会遍历冻结陈述的类型闭包（PA25 的
  `ccCell → ccUh → cc_pe_exists`），故很多 `real_model_*` 即使证明体干净
  也打印 `sorryAx`。地图的 direct source 只认**值里直接含 sorryAx**；
  值级检查用 `#valax3`/`taintprobe`（defs 原子、theorem 值展开）。记账时
  两栏分开，禁止互相掩盖。
- **债务搬家检测**：任何 PA25/PA18 填充批合并前，先重跑
  `cd lean && lake env lean scripts/e2e_reach_map.lean > /tmp/reachmap.out`，
  diff 源清单；若“消失 N、新增 M”且净减很小或出现 `RVFXZBU` 回归，按
  源数守恒规则**停批**。PA25 8 件试填（+177/−8）即因此回退，试填在
  `lane_snapshots/pa25real/`。
- **`mxiExplicit` 仍带 sorryAx**（经 PA2 `MXI_EXISTS_concl`），不得作为
  clean 件消费；PA11 `k3Subset` 已示范用 PA7/PA8 kit 内联替代。
- **`cc_pe_exists` 是枢纽**：PA18:206，HOL `leaf_cell.hl:1052-1084`，
  约 280 下游类型污染；不要用 `ccPe1`/`ccPe2` 的 choose 定义绕债。
- **R1 shard recDepth**：v1 发射器 `shard_file()` 缺 `maxRecDepth`，深链
  叶 `by decide` 爆默认 1000；已给 `emit_lean.py` +2/−1（`maxRecDepth
  1000000`），新案重发射会自动带；老案手工补 62 个 Shard。
- **LP 口径**：SoPlex 必须钉 8.1.0；`LpTerminalCertified` 对 id 不敏感
  （LPCert:61），叶必须由 `--emit-closure` 从本记录 pin 转发，禁止手写
  五元组/跨记录借用；`GoodListNodes` 仍是 `True` 占位（Assembly:1526），
  `LpIneqs` 空清单，`hypermapOfList` 未落地——W6 前必须先裁决。
- **W6 骨架**：`lane_snapshots/lpw6/LPCoverage.lean` import
  `Kepler.Assembly`，最终接线前必须先把共享类型下沉（否则环）；未入仓。

### 5.8 地图/闸/账本操作补充

- 闸的 `LANE_FILES` 与目标文件路径都用 **lean-相对**（如
  `Kepler/Text/PackingAuto25.lean`）；新文件先 `git add`。
- 车道并行时，`LANE_FILES` 要列出所有脏的 lean 文件（只放行不编译）；
  根集用 `GATE_ROOTS` 按需裁剪。
- e2e 地图再生成：`cd lean && lake env lean scripts/e2e_reach_map.lean >
  /tmp/reachmap.out`，再 `cp` 到 `docs/e2e-reachability-map.tsv`；热缓存
  数秒，冷启动会重建 Assembly olean。
- DEBT.md 再生成：`python3 lean/scripts/debt_ledger.py . > DEBT.md`
  （约 6 分钟）；带脊柱探针用 `--with-spine`（更久）。
- 快照的 `MD5SUMS` 有时是 sha256 而非 md5：用
  `shasum -a 256 -c MD5SUMS` 验，不要用 `md5sum -c`（会报 improperly
  formatted）。

## 6. 文档地图

| 要找什么 | 去哪 |
|---|---|
| 权威计划/战略/阶段现状/规程 | `PLAN.md` |
| 实时进度看板 | `STATUS.md` |
| 债务刻度（生成物勿手改） | `DEBT.md` |
| 决策与演化记录 | `DECISIONS.md` |
| 主定理端到端可达债务图（派工依据） | `docs/e2e-debt-map.md` |
| 章节→模块映射+全库覆盖度普查 | `docs/module-map.md` |
| 车道工人手册 | `docs/fill-worker-playbook.md` |
| 侦察报告 / 车道交接 / 专项设计 | `docs/scouts|handoffs|projects/` |
| LP W6 侦察 / A12 历史侦察 | `docs/scouts/lp-w6-coverage-scout.md` / `formal-lp-verify-scout.md` |
| 车道产物与证据快照 | `~/c17_backup/lane_snapshots/{lpaudit,pa15fin,pa11lep,lpw6,pa25real,r1rest,prep3}/` |
| SF 提案与执行补丁 | `docs/statement-fix-proposals.md` + `-patches/` |
| 架构与陈述保真 | `docs/architecture.md` / `docs/statement-fidelity.md` |
| 端到端对象 | `lean/Kepler/Final.lean`（`the_kepler_conjecture_e2e`） |

**文档债拐点（2026-10-20 专家评审记账，现不动、到点即立项）**：
`statement-fix-proposals.md` 十天 77KB→124KB（~5KB/天，追加型台账），
`fill-worker-playbook.md` 已 81KB。**重组触发线：任一破 200KB，或"查一条
已批 SF 的最终形态"需要翻三个节以上**——届时重组方案：proposals 已批且
已应用的项搬 `docs/statement-fix-history-<季度>.md` 卷宗（正本只留在册未决
+近 30 天），playbook 按章拆分（骨架纪律/闸体例/雷场分册）。两项都属"追加
即增值"文档，禁止为瘦身删历史记录，只许搬卷。

## 7. 接班 / 交班清单

**接班（按序）**：① `git log --oneline -15` + `git status`（盘上脏文件 =
在途半成品，先核盘再动）；② 读本文 §1.3/§3；③ `PLAN.md` §5 +
`docs/e2e-debt-map.md` 最新增量节（2026-10-23 PA25 节是当前末端）；
④ 重跑 e2e 地图核对 133/624；⑤ 若接 LP 线，读
`docs/scouts/lp-w6-coverage-scout.md` 与 `lane_snapshots/lpaudit/IMPORT_PLAN.md`；
⑥ 若是车道工人，读 `docs/fill-worker-playbook.md` 全文。

**交班（编排者，每波/每日）**：① 落地一切可落地（闸→commit→push）；
② e2e-debt-map 增量节 + DEBT.md 重生成 + STATUS 刷新；③ 重大波次随更
module-map；④ 波次 wrap 并入 STATUS.md 日期节即算数（2026-10-20 修订，
独立 `docs/handoffs/session-<date>-wrap.md` 仅当用户索要时写）；⑤ 全部
推远端，工作树干净或脏文件皆有归属记档；⑥ 项目收官/被取代即把
`docs/projects/` 对应文件挪 `archive/` 并全库同步路径引用。

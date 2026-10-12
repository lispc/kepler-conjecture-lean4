# HANDOFF.md — 交接文档（2026-10-12，面向接手的 coding agent）

> 2026-10-10 曾退役并入 PLAN/STATUS；**2026-10-12 用户令恢复为独立交接文档**。
> 本文是接手入口，读完即可开工；权威计划 = `PLAN.md`（冲突时以它为准），
> 实时看板 = `STATUS.md`，债务刻度 = `DEBT.md`，决策日志 = `DECISIONS.md`。
> 车道工人开工另必读 `docs/fill-worker-playbook.md`。

---

## 0. 30 秒速览

用 Lean 4 + Mathlib 以"证书化计算"范式重造 Kepler 猜想端到端形式化证明
（蓝图 = Hales《Dense Sphere Packings》/ Flyspeck）。当前形态：端到端对象
`the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean`）已立于主定理形态
（M5′ ✅）， axiom 面 = sorryAx(3 冻结接口) + 624 特许 Graphs shard + 标准三。
主战场 = **Phase 5 文字证明清债**（贪心触达制：每一步最大化接触既有已证质量），
用 5-6 个并发 sub agent 车道滚动生产，编排者统一闸/提交/推送。终局 = 会师
（M5″）后清叶，零 sorry 组装（M5/G5），干净机器复现交付（M6/G6）。

## 1. 现状（2026-10-12 收口时点，main @ `b1ab2803`，工作树干净）

### 1.1 阶段完成度

| Phase | 内容 | 状态 |
|---|---|---|
| 1 | 陈述形式化（`Statement.lean`） | ✅（:111 占位 sorry sanctioned，终版退役） |
| 2 | tame 平面图枚举（19,715 图 + 完备性证书） | ✅ `tame_classification` 闭合 |
| 3 | 线性规划（43,078 终端 LP 内核验证层） | ✅ 求解+checker 层；**重跑产物已丢失**（换机），Lean 侧叶户 `Text/LP/`（177 模块，43,078 枚 `lpT<id>` 叶）已立户待灌数据 |
| 4 | 非线性不等式 | 🟡 求解层 68/176 + 内核 8 案；重计算全部 deferred（见 §3.3） |
| 5 | 文字证明移植（`Text/` 25+39 模块） | 🟡 **主战场**，滚动清债中 |
| 6 | 集成交付（`Final.lean` e2e） | 🟡 e2e 已立；余三接口清债 + 占位去重 + 终验 |

里程碑：M0-M4 ✅（M4 重计算部分 deferred）、**M5′ ✅**（2026-10-10）、
M5″ 会师 🟡（T/B 线推进中）、M5=G5 零 sorry 组装 ⬜、M6 交付 ⬜。

### 1.2 债务与覆盖度账

- **DEBT.md 总量 44,717**——其中 43,078 是 LP 叶户（deferred-compute，灌数据
  即清，**勿当文字债攻击**）；**可比口径（Text 非LP + root + Geom）= 1,639**
  （上周 1,713）。Geom 区已清零。
- 非 LP 大户（按新账本）：PA25 131 / LA1 82 / LA22 82 / LA32 65 / LA28 63 /
  LA34 60 / LA6 60 / LA24 53 / PA18 53 / LA38 47 / LA5 43 / PA7 22。
  但**派工顺序不看这个表**——看贪心排名（§2.4 重排名循环）。
- 全库三态覆盖度（`docs/module-map.md` 普查节，2026-10-12 实测）：
  HOL 6,540 定理 / 686k 行 → 已移植 38% / 证书替代 20% / 未移植 42%
  （按行 40/28/32）。结论：无半成品章；证书替代类=计算性内容等灌装；
  tame 章按需求批移植、无需全搬。

### 1.3 刚发生的事（2026-10-12 五线波，全部已落地推送）

| 线 | 结果 |
|---|---|
| TameList3 | TameSpine 第三批 1,309 行/84 件零 sorry（indexf/split_at/betwn 家族）；三批累计 ~4,050 行/323 件 |
| PA7 | **XYOFCGX 本体闭合**（sorry 36→21，残余=GIANT 链）；BARV 前置两件+投影件八条就位 |
| PA20 | **文件级 sorry 归零**（gammaX 章 k=3/k=4 双件全闭） |
| PA24 | 情形 A/B3 全证，capstone 三分装配，B2 收窄为单支残件；侦察纠错 `MXI_EXISTS_concl` 在 B2 支为假 |
| POS_DIRECT | 线死于 API 超时，**盘上 salvage 走闸落地**：POS_DIRECT 根系五件真证（+815 行） |

闸门本次演进两笔（离线双向验证后入闸）：**EV20 重复件豁免**（被删声明由干净
直接 import 同名提供+语句空白归一化全等）、**EV21 sorry 计数代码行口径**
（docstring 散文行双侧剔除）。

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
tainted 常量）。上次全量排名的头部：ccPe1/ccUh/ccKe（PA18 cc 链，单根
cc_pe_exists）、s_leaf/leaf_rank（PA25）、pack_nonlinear_rest（PA21 62 bank
pin 死）。

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

## 3. 短期计划（接手即干，按优先级）

### 3.1 可立即派工的车道

1. **PA25 leaf_rank 车道**：`PackingAuto25.lean:3287 mcell3_gammaX_gamma3f`
   可接——其依赖 `gammaX_gamma3f` 本日已转真；ccCell/leaf_rank 机械照旧。
2. **PA7 下工位 XNHPWAB1**（编排者移交建议）：两大前置（BARV_AFFINE_INDEPENDENT、
   投影件八条）本日就位，预计中等规模；其后 omegaList 链（KSOQKWL/YIFVQDV/
   WAUFCHE2）与 WQPRRDY capstone（体量最大，单独立项）。
3. **LA5 SUCCESEOR 下游 10 件**：POS_DIRECT 根系五件已填，解锁面已开；
   LA2/LA5 链独立于 Packing 链，可随时并行。
4. **PA24 B2 两整波**：①泛具子情形四点凸包装配（~300-400 行，路线记档
   PA24 :4984-5026）；②退化子情形换叶=支撑面引理本体（~200-300 行，
   `docs/projects/pa24-nonflat-roadmap.md`）。
5. **TameSpine 下一批**：批次表在 `docs/projects/tamespine-port-plan.md`；
   T3 线已改"A7/A8/A9 前提树驱动的需求批"（防孤儿移植）。
6. **顺手账**（下一碰该文件的车道顺带）：PA21 :89-106 "PROVED" 降格诚实
   措辞；PA14 :42-43 "sorry-free"→"locally sorry-free"。
7. **重排名**：上述根波落地后局部重扫 PA18/PA25/PA21/LA2/LA5 → 重排名 →
   按新 TOP-N 派工（§2.4 循环）。

### 3.2 待用户拍板项（不要自行做）

- TameSpine Assembly §2b 五枚 True-placeholder DEF-FIX flip（flip 源已备于
  `Kepler/Text/TameSpine/GoodGraph.lean`，等 A7/A8/A9 波到位提请）。
- SF 提案项 18（volD_pos 缺 `hne`）等历史 SF 案 volume 补前提类，均在
  `docs/statement-fix-proposals.md` 排队等裁决。

### 3.3 deferred-compute（Mac 不做，等强机器）

| 项 | 说明 |
|---|---|
| A12：43,078 LP 数据灌装 | Lean 侧叶户已立（`Text/LP/`），等 `formal_lp verify_all` 移植立项 + 真证书数据 |
| A11：993 证书 + 81 G4 residue | 重跑产物丢失清单见 DECISIONS 2026-09-28 |
| 92 prep 家族重求解 | 附带策略决策（TM vs BBTreeGD） |
| Phase 4 两巨兽重放 | 784/6321、770/12553（olean 保留可幂等续跑） |

## 4. 长期路线（细节以 PLAN.md 为权威）

```
现在 ──贪心触达清债（Phase 5 主战场 + T1-T4 展开 / B1-B5 上拉）──> M5″ 会师
     ──BFS/DFS 清叶（纯填证批 / deferred-compute / 真数学缺口三拣）──> M5=G5 零 sorry
     ──Statement 占位退役 + 全量公理审计 + 复现文档──> M6 干净机器 make reprove 全绿
```

已知真数学缺口清点（非工程量）：pivot 反向 k=3/4（GRUTOTI 最后一块，
~200-400 行）、GRKIBMB 尖锐边界组、PA24 B2 退化情形。风险排序：Phase 4
重计算量 > tame 章体量（批次流水线缓解）> Mathlib 缺口（项目内自证）>
陈述保真（SF 通道）。

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
| SF 提案与执行补丁 | `docs/statement-fix-proposals.md` + `-patches/` |
| 架构与陈述保真 | `docs/architecture.md` / `docs/statement-fidelity.md` |
| 端到端对象 | `lean/Kepler/Final.lean`（`the_kepler_conjecture_e2e`） |

## 7. 接班 / 交班清单

**接班（按序）**：① `git log --oneline -15` + `git status`（盘上脏文件=
在途半成品，先核盘再动）；② 读本文 §1/§3；③ `PLAN.md` §5 + `docs/e2e-debt-map.md`
最新增量节；④ 若是车道工人，读 `docs/fill-worker-playbook.md` 全文。

**交班（编排者，每波/每日）**：① 落地一切可落地（闸→commit→push）；②
e2e-debt-map 增量节 + DEBT.md 重生成 + STATUS 刷新；③ 重大波次随更
module-map；④ 会话级 wrap 写 `docs/handoffs/session-<date>-wrap.md`；
⑤ 全部推远端，工作树干净或脏文件皆有归属记档。

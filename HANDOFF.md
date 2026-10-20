# HANDOFF.md — 交接文档（2026-10-12，面向接手的 coding agent）

> 2026-10-10 曾退役并入 PLAN/STATUS；**2026-10-12 用户令恢复为独立交接文档**。
> 本文是接手入口，读完即可开工；权威计划 = `PLAN.md`（冲突时以它为准），
> 实时看板 = `STATUS.md`，债务刻度 = `DEBT.md`，决策日志 = `DECISIONS.md`。
> 车道工人开工另必读 `docs/fill-worker-playbook.md`。


---

## ⚡ 当前状态速览（2026-10-17 收波更新；细节见 STATUS 2026-10-16/17 mega 波节 + e2e-debt-map 增量节四）

> **2026-10-16/17 mega 波**：**C1.7 全线收官**（七 commit 全闸绿，7b492f63..51f3403a）。
> 189 条 LP 不可行 Farkas 证书：列主序手术（B086 4h22m→7m45s = 33.8×；B087
> 6h+65.8GB 不可完成→9m10s）→ 189 闭合模块入库+列→行桥 LPFarkasCM →
> **infeas 段 sorry 清零** → 统一终账扫波 **189/189 全绿零失败**。SF-42 落地
> （sqrtRel 相对粒度，C549Mono 12/12 重烤；TM 舰队 197 模块重烤=尾波排队）；
> DomOK v2（mono stage-B 批化，真瓶颈=rung 2048 atan，witness 位降 rung 移交
> W8）；批 20（含前批脚手架虚账勘误）；PA25 wwtcount6_y finisher（行首裸
> sorry 87→86）。**16:13 内存打穿强重启事故**：五 lane 并发+巨物同机 → swap
> 打穿；/tmp 全清靠 diff 快照打捞零损失续跑；顺手破案"环境收割者"= 磁盘满→
> jetsam。**内存三规**（lane 串行/≥12GB/巨物禁并行）。DEBT 44,481（−193）。
> 六小时巡检 automation 在岗。

- **在飞**：EULER_TRIANGLE 三代车道（GIANT 级：:2081 需闭式立体角定理本体，
  W-乘积法施工图已备，dih 桥已证，二代 sympy 双验证）；root runner 长跑
  （16:13 阵亡当日复活账本零损失，~3,500/8,283 本轮 done 含历史 fail 重试，
  ETA ≈ 34h，配方 /Users/zhangzhuo/lprun/MONITOR.md §4，巡检自动化每 6h
  查活救活）。
- **脊柱接口**：A1-A5 已清；A6（柱②归一化本体一件）/A7/A8/A9（tame GIANT，
  **B1 地基 20 批全落，批 21 起点 = HOL :10595 fgraph_seed**）/A10（帽石全清，
  mqmsmab 装配波待立项）/A11/A12（C1.7 已收官，A12 数据绑定收口）。
- **A12/C1**：**C1.7 已全线收官**（189/189 内核验证+入库+骨架闭合+统一终账，
  见上）；root runner 长跑如上。
- **Phase 4**：DomOK v2 落地（sb12 真瓶颈=rung 2048 闭式 atan 内核 Taylor），
  **下一杆 = witness 位 trans 降 rung**（移交 W8 拍板）；TM 舰队重烤波
  （197 模块/18,477 站点，SF-42 后机械批量）排队；W9 判定的第三武器 C 侧
  集成仍 deferred。
- **排队待派**：舰队重烤波 / A6③（DLWCHEM/XULJEPR GIANT）/ PA24 B2 续 /
  W8 witness 位降 rung / EULER 三代（已在飞）。
- **⚠️ 发车冻结（用户令 2026-10-20，在先于上表）**："接下来每个 lane 结束后，
  不发新的了。等我新的指令。"——**2026-10-20 晚用户批准三发解冻**（"按你说的做吧，
  发车间隔 15 分钟"）：①十二发波 PA24 scaffold 3 收口（19:19 发，克隆 p4pa24f）
  ②TameSpine 批 60 = B3 入口 AUQTZYZ→RXOKSKC（19:04 发，克隆 p4t21）③W8 gen-8
  + decide-mode 开关（**错峰：等 TM 舰队 shard 排空再发**）。**此三条之外仍冻结**
  （AJRIPQN 本体 / Lean 4.35 升级波 / 雷场入 playbook 等待用户令）。容量纪律：
  12 核/36G，重 lean 构建同时 ≤3 + runner 2，车道 lake build 串行（禁止跨
  lane 并发构建）+ 只用热缓存；**Lake 5.0.0 无 `-j`/`--jobs` 旗标，禁用 `-K`
  未知键**（见 §5.5）。
  六小时巡检自动化同样钉死不得代发。

---

## 0. 30 秒速览

用 Lean 4 + Mathlib 以"证书化计算"范式重造 Kepler 猜想端到端形式化证明
（蓝图 = Hales《Dense Sphere Packings》/ Flyspeck）。当前形态：端到端对象
`the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean`）已立于主定理形态
（M5′ ✅）， axiom 面 = sorryAx(3 冻结接口) + 624 特许 Graphs shard + 标准三。
主战场 = **Phase 5 文字证明清债**（贪心触达制：每一步最大化接触既有已证质量），
用 5-6 个并发 sub agent 车道滚动生产，编排者统一闸/提交/推送。终局 = 会师
（M5″）后清叶，零 sorry 组装（M5/G5），干净机器复现交付（M6/G6）。

## 1. 现状（2026-10-13 收波时点，main @ `aaae330c`+文档笔，工作树干净；编排者停等中）

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

- **DEBT.md 总量 44,646**（2026-10-13 收波重生成）——其中 43,078 是 LP 叶户
  （deferred-compute，灌数据即清，**勿当文字债攻击**）；**可比口径（Text 非LP +
  root）= 1,568**（前波 1,639，净 −71：LA5 −10 / PA15 −2 / Assembly −3 /
  TameLp −1 等本波真实清偿）。Geom 区已清零。
- 非 LP 大户（按新账本）：PA25 131 / LA1 82 / LA22 82 / LA32 65 / LA28 63 /
  LA34 60 / LA6 60 / LA24 53 / PA18 53 / LA38 47 / PA7 22。
  但**派工顺序不看这个表**——看贪心排名（§2.4 重排名循环）。
- 全库三态覆盖度（`docs/module-map.md` 普查节，2026-10-12 实测）：
  HOL 6,540 定理 / 686k 行 → 已移植 38% / 证书替代 20% / 未移植 42%
  （按行 40/28/32）。结论：无半成品章；证书替代类=计算性内容等灌装；
  tame 章按需求批移植、无需全搬。

### 1.3 刚发生的事（2026-10-13 收波：三线全落地推送后停等）

| 线 | 结果 |
|---|---|
| TameSpine 批 10-12 | 三连批 +2,232 行/94 件零 sorry，**B1 链 :23-8920 无缺口**（批 10=阵亡草稿独立机械验收零编辑采用）；批 13 起点=HOL :8921 contour_list_cons 旗塔章 |
| A10 | **CRTTXAT 帽石装配完成 = B6 出口件一号全清**；arc kit 五件套全零；鸽笼原理替代 SUM_ORBIT 方法论突破；TameLp 7→6 |
| A6 | 柱② 三件中等档+钥匙件 salvage 落地，**柱② 仅剩归一化本体一件**（Lean 路线 spec 已入 NEEDS） |
| C1.6-G5 | **收官**：gen_farkas.py 1035 行——189/189 精确 Farkas 预检+试点 B 端到端 [propext]，93 族零 UNKNOWN；C1.7 批量发射处方已给 |
| Phase4-W3 | 四工位落账：**guard-straddle=证书结构缺口**（根因钉死+13 子盒修复路线量化）；disj stage-A/B 端到端首绿；decide 成本 122.7 s/叶实测；formal_ineqs 考古（monotonicity 降维=免费武器） |
| 决策 | Phase 4 路由表批准（R1-R4 混合）；92 prep 画像 94.3% 可立即灌装（R1 101/R2 665/R3 39/R4 7） |

闸门本次无演进（EV22-24 已在前波）；新雷区 3 条入 playbook §5.4''
（孤儿进程 PPID→1 / 解释跑 stdout 块缓冲假死象 / 探针层 Nat.sqrt 与内核层
baked 证书的分层纪律——decide 只吃后者）。

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

### 3.1 可立即派工的车道（2026-10-13 收波时点队列，**全部待用户令**）

1. **TameSpine 批 13**：HOL :8921 `contour_list_cons` 起旗塔章（contour_list_cons/
   contour_list_is_contour/face_map_list_power/hyp_S_list/marked_list_empty_flagged）；
   `ContourListSpine` 载体批 8 已备，`hyp_S_list` 差件（hypMLm+faceMap 幂桥）批 12
   已就位公开。批次表 `docs/projects/tamespine-port-plan.md`。
2. **C1.7 189 条批量发射**：遍历 /tmp/p4g5/batch_results.json 逐条 `gen_farkas.py
   --lean` 出 LpInfeasCert 套 pin 模板；排产=小编译批次+长预算（最大 327×230
   decide >40 分钟；注意 hard_7 解包副本 /tmp/p4g5/hard7 易失须先补）。
3. **W4 线（Phase 4）**：①镜像 gsplit 实施（Lean 侧 stage-A 批量驱动+子盒 params
   +stage-B 发射 BBTreeGD 分裂节点，`emit_lean.py --hull` 两段式现成）；
   ②第三武器 R&D（radicand 预切分/t=√u 换元，R3 39 条靶标已定标）；
   ③decide 成本工程（shard 粒度/并行/rung 降档）。
4. **A6 续五**：柱② 归一化本体一件（Lean 路线全文 spec 在 Assembly NEEDS：
   packingConfig 紧致机器+字典序极小化 k 步递归+末步扰动矛盾）；其后柱③
   DLWCHEM/XULJEPR 侦察。
5. **A10 装配波**：mqmsmab 章 CRTTXAT 消费点已解锁（B6 出口件一号全清）。
6. **PA25 leaf_rank 车道**：`PackingAuto25.lean` mcell3_gammaX_gamma3f 链照旧
   （127 残余，s_leaf/leaf_rank 贪心头）。
7. **INTERSECTION_LEMMA GIANT**（解锁 LA5 剩 6 件中的 2 件；LA5 可填面其余已清零）。
8. **顺手账**（下一碰该文件的车道顺带）：PA21 :89-106 "PROVED" 降格诚实措辞；
   PA14 :42-43 "sorry-free"→"locally sorry-free"。
9. **重排名**：上述根波落地后局部重扫受影响模块 → 重排名 → 按新 TOP-N 派工
   （§2.4 循环）。

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

**文档债拐点（2026-10-20 专家评审记账，现不动、到点即立项）**：
`statement-fix-proposals.md` 十天 77KB→124KB（~5KB/天，追加型台账），
`fill-worker-playbook.md` 已 81KB。**重组触发线：任一破 200KB，或"查一条
已批 SF 的最终形态"需要翻三个节以上**——届时重组方案：proposals 已批且
已应用的项搬 `docs/statement-fix-history-<季度>.md` 卷宗（正本只留在册未决
+近 30 天），playbook 按章拆分（骨架纪律/闸体例/雷场分册）。两项都属"追加
即增值"文档，禁止为瘦身删历史记录，只许搬卷。

## 7. 接班 / 交班清单

**接班（按序）**：① `git log --oneline -15` + `git status`（盘上脏文件=
在途半成品，先核盘再动）；② 读本文 §1/§3；③ `PLAN.md` §5 + `docs/e2e-debt-map.md`
最新增量节；④ 若是车道工人，读 `docs/fill-worker-playbook.md` 全文。

**交班（编排者，每波/每日）**：① 落地一切可落地（闸→commit→push）；②
e2e-debt-map 增量节 + DEBT.md 重生成 + STATUS 刷新；③ 重大波次随更
module-map；④ 波次 wrap 并入 STATUS.md 日期节即算数（2026-10-20 修订，
规则向实践靠拢：10-12 起的波次 wrap 实际全部写进 STATUS 日期节且功能完好；
独立 `docs/handoffs/session-<date>-wrap.md` 文件仅当用户索要时才写）；
⑤ 全部推远端，工作树干净或脏文件皆有归属记档；⑥ 项目收官/被取代即把
`docs/projects/` 对应文件挪 `archive/` 并全库同步路径引用（2026-10-20 首次
执行，见 `docs/projects/archive/README.md`）。

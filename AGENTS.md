# AGENTS.md — 本仓库的硬规则

> 给所有接手本仓库的 agent。**先读这 60 行，再动手。**
> 违反下面任何一条，产出作废——不是"下次注意"，是作废。

## 1. 目标与验收

- 终局（**用户 2026-11-06 裁决**）：**不比 Flyspeck/Isabelle 更差**，不是完美标准三。
  验收式：`#print axioms Kepler.the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean:22`）
  = `[propext, Classical.choice, Quot.sound]` ∪ **恰好 585 条地面 `native_decide` 公理**，且
  1. **零 `sorryAx`**（锥内 49 条 sorry 是唯一还算"债"的东西：48 `nli*` + 1 hLP；**Text 0**；
     wt2A 小模块验收后 2026-11-20 `1ec06b28`；AQ 基线 `e4c384e6` 时为 51）；
  2. 每条公理的陈述是**封闭可判定的地面事实**（无自由变量、无对无限类型的量词），
     进 manifest、可 replay、注明数据源与生成器版本；
  3. 与原文形式化的 `same*`/`pre_iso_test*` **同数据、同信任类别**（见
     `docs/handoff-2026-11-06.md` §0.1：HOL 跳过分类定理；HOL 零公理真证 `good_list`
     —— 我们这半边已于 2026-11-06 追平；Isabelle 用 8 条 `by eval` 做枚举）。
- 当前根面 **589 = 585 native + 标准三 + `sorryAx`**。**585 是信任基座，不是债**
  （基线 T `52275a1c`，2026-11-09 定格：580 shard-range + 5 tri-single-seed，仅 2 种形状；
  `docs/priority-queue.md` 文件头）。
- 在此原则下**明确不做**：把 585 条枚举 shard 拉进内核重放（实测 4,450–6,550 核时 +
  内存不可行）、证书农场、"真·标准三"。**但**下面这些没有 parity 借口，必须修：
  `else True` 回落、索引盲谓词、空量化注册表（`Prop := sorry` 型已于 `b85eaade` 清零）。
- 唯一验收语言：`#print axioms`。任何"完成了"的说法都必须附这条命令的输出。
- **nli 战役路线图/结论**：`docs/nli-campaign.md`（活文档：分诊 / 已闭件 / 负结果 /
  下一步；历史只读侦察在 `docs/archive/scouts/nli-*`；实时数字仍以 pq / 地图为准）。

## 2. 禁造边（最高优先）

- 不许**新增** `axiom` / `sorry` / `admit` / `native_decide` / 假定理。
  （在库的 585 条 `native_decide` shard 是 §1 声明的**信任基座**，不是违例；但也**不许再添一条**。
  能改 kernel `decide` 的必须改，改不动的不许换新的 `native_decide` 顶上。）
- 不许改陈述来让证明通过。陈述改动只走 **SF 通道**（`docs/statement-fix-proposals.md`）；
  定义改动只走 **DEF-FIX 通道**（章程在 `docs/def-fix-charters/`）。
- 不许删 `sorry` 假装关闭；删除面必须恰好等于被真证的声明。
- 上游是**假桩**（如 `POLYHEDRON_TGJISOK` 空洞化、`BIJ_DART_POLYEDGE` 在现桩下为假）
  时，判 **BLOCKED** 并报告，不许绕着假桩凑证。

## 3. 车道纪律

- 车道在 `/tmp/<lane>/` 工作；**主仓 tracked 文件零改动**。
- 产物（`patch.diff` / `DELIVERY.md` / `Evidence.md` / `logs/`）放
  `~/c17_backup/lane_snapshots/<lane>/`。
- 只允许独立 `nice -n 19 lake env lean <单文件>`；并发 ≤3。
- **禁止** `lake build`、`scripts/auto_gate.sh`、地图仪器（`e2e_reach_map` /
  `global_reach_map` / `orphan_histogram`）。这些由编排者跑。
- 所有子任务派发必须**异步**（`run_in_background: true`），不阻塞主会话。
- **派单记录必须与 `SendMessage` 的成功回执同批写下**：账本里的「派 X」= 消息已送达，
  不是「打算派」。2026-11-11 实发生过三次「只写账本、未发消息」，三条车道空转 1–2 小时
  （续650 ERRATA）。另：对 **1 小时无产出**的车道发一行状态检查是常规动作——本次正是靠它
  发现空转。

## 4. 本机限制

- 禁重型计算：证书农场、全库构建、LP/非线性重放一律挂起。
- **Assembly 级 `lake build` 永久禁止**（会触发全树重编与 shard trace 洪泛）。
  需要验证 Assembly 时走岛协议：standalone `lean -o /tmp/.../Kepler/Assembly.olean`
  + `LEAN_PATH` 探针 + 与基线根面逐字节比对 + olean 回灌。
- **`auto_gate.sh` 的 “Text roots 全量构建” 步永久禁用**（2026-11-09 实测：它重编
  8,801/8,816 个目标、在最后 15 个被 143 杀，把 swap 推到见底）。验收口径改为三件套：
  ① 模块级 `lake build <单模块>` PASS；② 岛协议 `lean -o /tmp/...` RC=0；
  ③ 编排者**亲跑** `#print axioms`（不许转述车道输出）。纯新增 diff（无既有模块改动）时，
  “全树不破”由 ①②③ 替代；闸的 roots 步失败**不作为拒绝理由**，只在日志里记一笔。
- **重编译并发护栏**：起前查 `vm_stat` free ≥ 200,000 pages（≈3 GB）作为**软性提醒**；
  硬闸是上一条（同一时刻 ≤3 个 lean ∧ 总 RSS ≤24 GB ∧ pressure <2）。不满足就等，
  不许“先跑起来再说”。
- **内存的真正约束是「同时最多 3 个 Lean 编译」（2026-11-19 用户裁定放宽，替代
  2026-11-09「同时只许 1 个」），不是 free pages。** 实测依据（`/usr/bin/time -l`）：
  单次编译峰值 RSS 5.66 GB（`Base.lean`）/ 6–10 GB（Rule P、LP `T*`）；本机 **36 GB
  物理**下 3 并发 ≈ 18–30 GB 尚有余量；普通进程不是问题（3 GB 分配 0 pageouts、
  压力不变）。**12 路扇出仍不可行**（见下条 lake 禁令）。
  ⇒ 护栏口径：**lean 进程数 ≤3 ∧ lean 总 RSS ≤24 GB ∧ pressure <2**；每车道仍
  ≤1 lean；编排者脚本内置 3 槽信号量 `/tmp/lean_slot{1,2,3}.d`（取槽编译、退出释放）。
- **swap 会动态伸缩**，不是只增不减：2026-11-09 实测从 **84.8 GB 回落到 25.5 GB**
  （无需重启），单次编译又会长回去 **+3.2 GB**。所以 **`swapused` 本身不是告警指标**；
  判据 = `kern.memorystatus_vm_pressure_level`（1 正常 / 2 警告 / 4 危急）+
  `pageouts` 增量 + 并发编译数。**不许只看 `Pages free`**（macOS 的 free 常年很小）。
- **lake 无并行度开关，默认全核扇出——编排者禁裸多目标 `lake build`（2026-11-13
  用户确认；00:35/09:05 两次崩溃的根因）**：一次 `lake build <N 模块>` 的闭包重编最多
  12 个 lean 并发；Graphs/Interval 的 native_decide **分片实测单进程峰值 12.6 GB**
  （`/usr/bin/time -l`，TopReplayHexShardS000）⇒ 12 路扇出 = 150 GB 需求 ≫ 36 GB 物理
  ⇒ swap 爆炸 ⇒ 驱动连环崩 ⇒ kernel panic（panic 表象 bcmwlan，实为内存枯竭）。
  ② **编译并发 = 3（2026-11-19 用户裁定放宽，替代 2026-11-13 的批=1；车道并行
  每车道仍 ≤1 lean）**；编译前过**编排者护栏**：
  `lean 进程数 ≤3` ∧ `lean 总 RSS ≤24 GB` ∧ `pressure <2`
  （护栏脚本 `~/c17_backup/orch_guard.sh`，编译前 source 之；3 槽信号量取槽、
  孤儿 PPID=1 自杀检查不变）；
  ②b **shard 类（Graphs/Interval native_decide）禁用 `lake build`**——单目标也会
  12 路扇出（2026-11-13 实测 pressure 4）；必须直编
  `lake env lean -o .lake/build/lib/lean/<Mod>.olean <Src>.lean`（严格 1 进程，
  岛协议同款），逐个串行。
  ③ **orphan 保险**：编排 build 脚本必须内嵌 PPID 自检（`[ $PPID = 1 ] → 自杀`），
  2026-11-13 实测应用退出后 detached build 变 orphan **整夜继续烧**直至机器崩溃。
- 用户保留项：certtm 的 TM3 / Mono* hold；D 证书层解冻 hold。不要单方面动。
  **专项解冻（2026-11-11 用户明批，仅此一项）**：BIEFJHU-a 的 TM 证书 pilot 可动 certtm；
  **TM3 量产扫全库、Mono\* 进 universe、D 证书层解冻仍然 hold**，跑完本 pilot 即回到 hold 态。
  **续批专项（2026-11-14 用户明批）**：`TSKAJXY-XLLIPLS` 单盒 TM pilot（车道 `tskajxy-tm-w1`，
  给 nli* 流水线定标）可动 certtm / `bb_arb`；**TM3 量产扫全库、Mono\*、D 证书层仍然 hold**，
  本 pilot 结束即回 hold 态。**（2026-11-14 已收线：glue 落库 `6f02985d` 全标准三；证书路线
  NO-GO——TM 精度在 2 万节点规模饱和、全量重放 36–72 CPU·天；certtm 已回 hold。）**
  **续批 2（2026-11-14 用户明批「按你建议走吧」）**：`ht4nn` 单盒 TM **有界微探针**
  （车道 `ht4nn-probe-w1`：4h 墙钟、root box + ≤400 叶 + 1–3 叶 checker 探针，不做量产）
  可动 certtm / `bb_arb`；**TM3 量产扫全库、Mono\*、D 证书层仍然 hold**，探针结束即回 hold。
  **续批 3（2026-11-15 用户明批「同意，发」）**：`nli-precision-w1` 精度车道（TSKAJXY 叶级
  `atan1_box`/检查器精度，可动 certtm / `bb_arb` 仅叶级）；**已收线 `2fd799ff`**（两 pilot 叶
  内核 PASS，+225/−3，全盒复刻 0→5012/6512），certtm 回 hold；TM3/Mono\*/D 仍 hold。
  **续批 4（2026-11-15 用户明批「批」）**：`guardrule-w1` 的 bounded certtm 解冻——**仅**
  `iteHullTM2` Rule P opt-in + point 证书字段 + emitter；**TM3 量产扫全库、Mono\*、D 证书层
  其它项、585 信任基座仍 hold**。**已收线 `058b2c12`**（Rule P 规则落库，4 叶内核 PASS；
  全量回放不改 certtm），certtm 回 hold。**Rule P 优化已落库 `229f731f`**（点求值 11–20×，
  4 叶 26.7–27.1 s / 10.2–10.3 GB；旧 checker 零改动）。

## 5. 落库流程

1. 车道交 `patch.diff`（相对某个 HEAD），编排者 `git apply --check` 后应用。
2. 编排者跑闸：`cd lean && bash scripts/auto_gate.sh Kepler/Text/<File>.lean <THM>`。
   新文件先 `git add -N`。零删除 diff 会被 NOTES-LANE 豁免（规则 5 跳过）。
   **该脚本的 “Text roots 全量构建” 步已禁用（§4）——只认它的模块 build 步 + 岛协议 +
   编排者亲跑的 `#print axioms`；roots 步挂了不拒绝，记日志。**
3. 闸 PASS 才 commit；**一个落库一笔 commit**，message 写清 文件/件数/commit 关系。
4. 对表：更新 `docs/priority-queue.md` §1（在飞）与 §8（一条日志）。

## 6. 文档纪律

- `docs/priority-queue.md` 是**唯一**实时账本（在飞 + 排队 + 最近日志）。
- **状态报告口径（2026-11-12 用户裁定）**：报锥内 sorry **必须给 Text / Assembly 分解**
  （如 `70 = 56 + 14`），不许只报总数；Text 侧逐条状态以 §2.1d 闭包矩阵 + §1/§8 为准。
- 数字**只引用不抄**：同一指标不许在多个文档各写一份。写数带
  `(实测 <commit>，<日期>)` 或标 `stale`。

### 6.1 文档三层清单（2026-11-09 用户裁定入档；基线刷新/重大落库时按层联动）

- **入口层**（门户/导航——写状态必须与账本层同口径，**刷新基线时一并刷**，
  外部评审 2026-11-09 抓出三处漂移即漏刷此层，`243111ef`）：
  `README.md` / `README.zh.md`（状态节）、`docs/README.md`（导航注）；
  `PLAN.md`（2026-10-10 快照——正文不改，只维护横幅）；`AGENTS.md` §1（验收式数字）。
- **账本层**（数字唯一出处，**只在这里存一份**）：
  `docs/priority-queue.md` 文件头（指标总出处 + §0 里程碑表）、
  `docs/trust-base.md`（信任基座）、`docs/hf-proof-map.md`（核心路线图，状态更新节）、
  `docs/handoff-2026-11-06.md` §0（接手档现状表）、
  `docs/e2e-reachability-map.tsv`（仪器原样输出）+ `.md`（基线叙事）。
- **历史层**（只增不改）：`docs/history/`、`docs/archive/`、`DECISIONS.md`（追加式）；
  旧数字报错就加 `ERRATA`，不覆写。
- 口径冲突时的权威序：账本层 > 入口层 > 历史层；发现入口层漂移 = 修入口层，不改账本层。
- `docs/history/` 与 `docs/archive/` 只增不改；纠正加 `ERRATA`，不覆写原文。
- `docs/statement-fix-proposals.md` 必须留在原路径：`auto_gate.sh:83` 按路径 +
  `^## N.` 切节读它。移动/拆分必须同 commit 改脚本。
- 旧看板（STATUS/HANDOFF/DEBT）已归档，别再往根目录加"总览"。

## 7. 止损比硬凑好

- 单件超过 ~450 行或 3 轮结构性卡死就止损，写清卡点交班。
- 侦察结论与工单冲突时，**以机器证据为准**（编译通过/`#print axioms`/probe），
  并把勘误写进交付。
- 不确定就标 UNRESOLVED。编造比空手更糟。

### 7.1 高频机械雷区（现行 20 条；全文、历史与降级条目见 `docs/pitfall-register.md`）

> 2026-11-19 用户裁定：本表最多维护 20 条。编号沿用历史号（外部大量引用
> `§7.1-N`，不改号；各条括注吸收的 PR 号，映射表在登记册 §0）。新雷区先入
> 登记册（全文+出处），两周内 ≥2 车道踩中或属禁造/锁/池级事故再晋升本表；
> 本表满 20 条时最低频者降级回登记册。

1. **注释 lexer**：正文禁字面「减斜杠」`-/`（引号内也算）——lexer 提前闭合注释，
   后续 import 全变垃圾；批量改注释前先跑 comment-depth（`/-` 与 `-/` 计数）核查。（PR-1/5）
2. **库形状**：`Nat.iterate` 右嵌套、`List.append` 左结合；`List.Disjoint` 真实形状
   `∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False`（收口 `(hdisp hx1 hx2).elim`），与
   `nodup_append` 裸双变量第三分量互转各需一个 lambda；`Perm` 裸文件写全名
   `List.Perm`；`List.append_eq_nil` 不存在；`getElem_append_right` 的 `h₂` 具名
   传参；`getLast!` 按前缀构造子递归。（PR-3/4/11/13 尾）
3. **改写次序**：`rw` 只重写首个匹配、`simp only [if_pos/if_neg h]` 重写全部——
   LHS/RHS 同条件 if 只改一边会伪造类型不匹配假象；`(ite c a b).2` 不 defeq——先
   `rw [show β = ite形 from rfl]` 再 `by_cases`；`rw [← h]` 在 `getElem` 上
   motive 不 type correct——改私有 `getElem_eq_of_eq`。（PR-6/12/10）
4. **签名/展开先查再写**：def 展开先 `#check foo.eq_N`（RHS 常是 Prop-ite）；
   新引理首次用前 `#check @Lemma.name`（`HasDerivAt.const_mul` c 在前、
   `hasDerivAt_const` x 在前）；`Real.sq_sqrt` 证 `√(a²)=a`、`(√a)²=a` 用
   `Real.mul_self_sqrt`；分母非原子时整值最外层必须括号；`HasDerivAt.add` 贪心
   拆分与分组不符时先 `have hfun : (fun t => poly) = fun t => (组₁)+(组₂)` 再
   `rw [hfun]`。（PR-2/29/30/31/28）
5. **本树无 Mathlib tactic**：`tauto` 不可用 ⇒ 命题收口用 core `grind`；
   unusedSimpArgs 警告不影响 RC。（PR-8）
6. **`#check` 报 unknown 先怀疑 import 面**：负探针必须按最新叶文件全集建
   import 闭包再逐名复核（unknown 两成因：改名 vs 闭包过窄）。（PR-4 尾/18）
7. **grep 命中 ≠ 声明**：判「已落」必须 `rg -E '^(theorem|lemma|def|noncomputable def) <name>'` 或 `#check`。（PR-7）
8. **`open Foo (…)` 写错一个名字整条失效**且只报该名一处：先 `#check` 真实命名空间。（PR-13）
9. **验收双检**：`error` 计数 0 与 `#print axioms` 缺一不可——未解目标静默带
   `sorryAx`、helper 的 error 污染下游；`Set.ncard_eq_toFinset_card` 的 autoParam
   静默插 `sorryAx`，必须显式给证人。（PR-14/15）
10. **陈述禁 `let (a,b,c) = f x` 模式绑定**（defeq 检验打爆 heartbeats）：改显式参数
    + `h : f x = (a,b,c)`；任何陈述写法变更（含 defeq 等价）记 DIFFERS。（PR-16）
11. **数学断言先写反例探针**：全称「单面/同面」类（e 步可跨面——`loopListSpine`
    的 e 步会跨到相邻面，此类断言四个已证假）；`Coplanar` 两读法（Mathlib 秩 ≤2
    vs Geom 存在形）不许混用，跨读法显式加桥。（PR-20/19）
12. **shell 检索一律 `~/.kimi-code/bin/rg`，禁裸 grep 扫仓**（实测 444 s）；裸 grep
    必须 `-I` + `--exclude-dir={.lake,.git,reference,_distfiles}`；`rg -r` 是
    replace 旗标，`-n` 独立写。（PR-21）
13. **状态以事实源为准**：通知（completed/failed 双向）都可能是假的——判活唯一
    准则 = agent wire.jsonl mtime 1 分钟内增长（仅 Kimi harness），通用三查 =
    进程 + 快照 mtime + 交付目录；「有 DELIVERY 无 LANDED commit」按 mtime 收账；
    车道交付物落快照入轮末例行（sync_lean.sh）。（PR-22/24/23/34）
14. **私有 def 实参序/形态「勘正」先双重对表**（直接消费者 + 对应 HOL 版本锚序）；
    改 def = 改所有消费者语义，视同陈述改动走 SF/DEF-FIX。（PR-25）
15. **patch 头双侧必须 `a/lean/... b/lean/...`**：b 侧 `/tmp/...` 会被判 rename
    （apply --check 照样 PASS）；apply 后 `git status` 必查（`D 目标` + 未跟踪
    `tmp/` = 事故签名）。（PR-26）
16. **长上下文退化 → 交接包落快照换 fresh session**（车道多轮 resume 与编排者
    接管同罪）；接管 3 轮未收即停手交回。（PR-27/33）
17. **量产文件批量错 → 改参数重跑生成器整文件重生成**，不做增量正则补丁
    （正则会截断供给行前缀）。（PR-32）
18. **tactic 块行首 `-` 是 case bullet**：多行项续行以 `-` 开头全乱——挪上一行行尾。（PR-35）
19. **池纪律**：建 island 池一律**复制式**（cp/rsync），禁 `ln -sfn`（2026-11-19
    实事故：farm 穿透把主仓 LP 池 193 个 olean 换成自指死链）；主仓 `.lake` 对
    车道只读；写前 `test -L`、开池后 `find <池> -type l | wc -l` 须为 0；
    LEAN_PATH 首个含 `Kepler/` 顶层目录的 entry 独占解析——引用 /tmp olean 时
    该 entry 须含完整 Kepler/ 树（最简法：新 olean 装进 `.lake`）。（PR-36/9）
20. **锁纪律**：编译脚本**禁 `exec` 起 lean**（exec 替换进程镜像、EXIT trap 不存活
    ⇒ 全局锁泄漏楔死全场，2026-11-19 实事故）；发现无主锁先取证（pgrep lean
    为空 + 无日志增长 + 无存活持锁脚本）再 rmdir，有效 PID 持锁绝不动。（PR-37）

> 已降级/历史条目全文见登记册：PR-17（TameSpine，已 ERRATA 作废）、PR-38–42
> （handoff-2026-11-18 §6 五条）+ 车道级雷区散件索引（hex51-w2 §5 六则、
> pent4-w1 §4 八则、la3/PA22g handoff、W5 mono 侦察）。

## 8. 遇难数学，先看原版（2026-11-09 用户裁定）

- 遇到**复杂数学问题**卡住时，**不许瞎猜瞎试**：动手或派车道之前，先查
  `reference/flyspeck/`（HOL Light）与 `reference/afp-flyspeck-tame/`（Isabelle AFP）
  里**同一对象的证明思路**，再定路线。原版做过同一套数学——
  死路它多半死过（有废弃注记），活路它多半留了标记（`tags`/`doc`/注释块）。
  先例：tsk_bank 三条难件，ds-envelope 的"买包络"路线被认证算术判死后，
  考古发现原版形态 = 对称缩域 + y→x 转换 + 按件手调切面 + 叶级 B&B 序列化重放
  （`pq 续408`）——三个候选方向全有原版背书，一轮考古顶几轮试错。
- 原版思路是**路线参考**，不是逐行翻译目标：注意口径差异
  （定义形状/层归约/类型层可能不同，如 jcajydu 的 Set α/ℕ→ℕ 跨型槽）。
- 考古结论必须**入档**（pq §8 日志 + 相关文档状态更新节），供后续工单直接引用。

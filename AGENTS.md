# AGENTS.md — 本仓库的硬规则

> 给所有接手本仓库的 agent。**先读这 60 行，再动手。**
> 违反下面任何一条，产出作废——不是"下次注意"，是作废。

## 1. 目标与验收

- 终局（**用户 2026-11-06 裁决**）：**不比 Flyspeck/Isabelle 更差**，不是完美标准三。
  验收式：`#print axioms Kepler.the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean:22`）
  = `[propext, Classical.choice, Quot.sound]` ∪ **恰好 585 条地面 `native_decide` 公理**，且
  1. **零 `sorryAx`**（锥内 65 条 sorry 是唯一还算"债"的东西：54 `nli*` + 1 hLP + 10 Text 章级；
     基线 AH `59208114`，2026-11-13）；
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
- **重编译串行**：起前查 `vm_stat` free ≥ 200,000 pages（≈3 GB）作为**软性提醒**；
  硬闸是上一条（同一时刻 1 个 lean）。不满足就等，不许“先跑起来再说”。
- **内存的真正约束是「同时只许 1 个 Lean 编译」，不是 free pages。** 2026-11-09 实测
  （`/usr/bin/time -l`，`Base.lean` 12 KB 源）：**单次编译峰值 RSS = 5.66 GB**、耗时 27.8 s；
  5 条车道并发编译 ⇒ 28 GB 需求（2026-11-12 用户更正：本机 **36G 物理**，
  并发 3–4 编译 ≈ 17–23 GB 尚有余量；pressure 纪律与 wait_low 不变）。
  普通进程不是问题：同一测量里 3 GB 分配 **0 pageouts、压力不变（1）**。
  ⇒ 车道起编译前必须确认“此刻没有别的 lean 在跑”；编排者侧只放行一个。
- **swap 会动态伸缩**，不是只增不减：2026-11-09 实测从 **84.8 GB 回落到 25.5 GB**
  （无需重启），单次编译又会长回去 **+3.2 GB**。所以 **`swapused` 本身不是告警指标**；
  判据 = `kern.memorystatus_vm_pressure_level`（1 正常 / 2 警告 / 4 危急）+
  `pageouts` 增量 + 并发编译数。**不许只看 `Pages free`**（macOS 的 free 常年很小）。
- **lake 无并行度开关，默认全核扇出——编排者禁裸多目标 `lake build`（2026-11-13
  用户确认；00:35/09:05 两次崩溃的根因）**：一次 `lake build <N 模块>` 的闭包重编最多
  12 个 lean 并发；Graphs/Interval 的 native_decide **分片实测单进程峰值 12.6 GB**
  （`/usr/bin/time -l`，TopReplayHexShardS000）⇒ 12 路扇出 = 150 GB 需求 ≫ 36 GB 物理
  ⇒ swap 爆炸 ⇒ 驱动连环崩 ⇒ kernel panic（panic 表象 bcmwlan，实为内存枯竭）。
  ② **编排者编译批 = 1（2026-11-13 用户裁定：保持 1 个 lean 进程，慢就慢点，
  单进程也就几个 GB）；车道并行每车道 ≤1 lean**；批/次间过**编排者护栏**：
  `lean 进程数 ≤2` ∧ `lean 总 RSS ≤20 GB` ∧ `pressure <2`
  （护栏脚本 `~/c17_backup/orch_guard.sh`，编译前 source 之）；
  ②b **shard 类（Graphs/Interval native_decide）禁用 `lake build`**——单目标也会
  12 路扇出（2026-11-13 实测 pressure 4）；必须直编
  `lake env lean -o .lake/build/lib/lean/<Mod>.olean <Src>.lean`（严格 1 进程，
  岛协议同款），逐个串行。
  ③ **orphan 保险**：编排 build 脚本必须内嵌 PPID 自检（`[ $PPID = 1 ] → 自杀`），
  2026-11-13 实测应用退出后 detached build 变 orphan **整夜继续烧**直至机器崩溃。
- 用户保留项：certtm 的 TM3 / Mono* hold；D 证书层解冻 hold。不要单方面动。
  **专项解冻（2026-11-11 用户明批，仅此一项）**：BIEFJHU-a 的 TM 证书 pilot 可动 certtm；
  **TM3 量产扫全库、Mono\* 进 universe、D 证书层解冻仍然 hold**，跑完本 pilot 即回到 hold 态。

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

### 7.1 高频机械雷区（2026-11-09 汇编，每条都实际烧过轮次）

1. **注释正文里禁出现字面「减斜杠」`-/`**（哪怕在引号内）——lexer 照样提前闭合注释，
   后续 `import` 全变垃圾。同车道 6 次、跨车道多次。注释框统一用 `└──…` 收尾。
2. **`def` 展开导致 `rfl`/`show` 失败时，先 `#check` 该 def 的自动生成方程引理**
   （`foo.eq_1/eq_2/eq_3`）——RHS 常是 Prop-ite 而非 `bif/cond`，按 `cond` 写必错。
3. `Nat.iterate` **右嵌套**、`List.append` **左结合（`infixl`）**：pow/拼接目标的构造树必须按此摆。
4. `List.append_eq_nil` 不存在；`List.getElem_append_right` 的 `h₂` 须具名传参。
   **`List.Disjoint`（Batteries `Data/List/Basic.lean:544`，随 Kepler 模块 transitively import）
   的真实形状是 `∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False`**（元素隐式、单成员、结论 `False`），
   收口用 `(hdisp hx1 hx2).elim`——**不是** `∀ a∈l₁, ∀ b∈l₂, a≠b`（旧措辞错）；
   而 `List.nodup_append` 的第三分量才是裸两变量 `∀ a, a∈l₁ → ∀ b, b∈l₂ → a≠b`。
   两者逻辑等价但形状不同，互转各需一个 lambda。
   **`#check foo` 报 unknown identifier 时先怀疑 import 面（探针有没有 import 到定义它的模块），
   再怀疑存在性**——2026-11-10 有车道因 bare-prelude 探针误判"`List.Disjoint` 不存在"。
5. 批量替换注释前先跑 **comment-depth 核查**（`/-` 与 `-/` 计数），否则层次归零。
6. **`rw` 只重写首个匹配，`simp only [if_pos/if_neg h]` 重写全部匹配 if**——
   LHS/RHS 各带同条件 `if` 时，`rw [if_pos]` 只改一边，会伪造"类型不匹配"假象
   （j3def 连续 8 轮踩坑，一替换即全绿）。另：`exact f a _ (by tactic)` 里
   元变量与 tactic 实参求值次序有坑，显式给实参。
7. **grep 命中 ≠ 声明**：树里同名符号可能只出现在注释/排期注记里
   （2026-11-09 实测：`indexf_rotn_alt`/`indexl_map_uniq`/`ifbetwn_indexf`/
   `flatten_indexf`/`indexf_map_uniq`/`transform_assumption_v2` 全树仅注释命中）。
   判"已落"必须 `#check` 或 `grep -E '^(theorem|lemma|def|noncomputable def) <name>'`。
8. **本树无 Mathlib tactic**：`tauto` 不可用（unknown tactic）⇒ 命题收口用 core 的
   `grind`（j3def T9 五处一次通过，产物仍标准三）。`simp only [...]` 的 unusedSimpArgs
   linter 警告不影响 RC，但替换表里不要写已被 simp 消掉的项。
9. **`LEAN_PATH` 解析 = 首个含 `Kepler/` 顶层目录的 entry 独占**（Lean 4.32 实测）：
   引用 `/tmp` 侧 olean 时，该 entry 必须自身含完整 `Kepler/` 树（symlink farm 镜像
   主仓 `.lake/build/lib/lean/Kepler` + 本车道新 olean），否则解析停在该 entry 报
   “object file … does not exist”。探针最简法：把 olean 装进 `.lake` 再跑（见 §4 岛协议）。
10. **`rw [← h]` 在 `getElem` 上 motive 不 type correct**（依赖索引）：改私有
   `getElem_eq_of_eq`（证明无关，`rfl` 级）+ `rw` 该等式，不要硬 `rw` 原式。
11. **`Perm` 的 `~` 是 scoped notation**：裸文件里写 `~p` 报 unexpected token，
   一律写 `List.Perm xs xs'`；`List.getD_eq_getElem` 的界证明参数名是 **`hn`**（非 `h`）。
   `Perm` 归纳的 cons 真支两侧退化为 `news ++ tail` 时 IH 不适用，用 `p.mem_iff`。
12. **`(ite c a b).2` 不 defeq `ite c a.2 b.2`**（`c : Bool` 变量表达式时 Decidable
   不归约）⇒ 别用 `change` 把 `.2/.2.1` 推进 ite 分支；先 `rw [show β = ite形 from rfl]`
   展开本体，再 `by_cases` + `if_pos/if_neg`。
13. **`open Foo (fList eList …)` 里写错一个名字会让整条 open 失效**，且只报该名字一处，
   随后满屏 unknown identifier（`Dart`/`parts`/`core`）⇒ 先核 `#check` 该名字的真实命名空间
   （`fList`/`eList` 在 `Kepler.Assembly`，不在 `Kepler.Text.Reduction5`）。另：
   `getLast!` 按前缀构造子递归（`(l++[a]).getLast! = a` 走 `getLastD_concat`；
   `l.reverse.getLast! = l.head!` 需对 `l.reverse` 用再 `reverse_reverse`）。
14. **有未解目标的声明仍会以 `sorryAx` 进入环境**（不只在 `error` 时）：文件里一处
   `error` 可能让另一处未收口的声明静默带债 ⇒ 验收必须 **"`error` 计数 0" 与 axioms 双检**，
   只跑 `#print axioms` 或只看 RC 都会漏。**新变体（2026-11-10，wsewpch wave1 实测）**：
   private helper 里的 `error`（如 `Finset.sum_nbij` 方向写反）会让 Lean 为失败声明**合成
   sorry 占位**并污染下游定理的 axioms 面 —— 见到"意外 `sorryAx`"先查**同文件 `error`**，
   再怀疑证明本身。
15. **`Set.ncard_eq_toFinset_card` 的 autoParam 会静默插 `sorryAx`**（Finiteness 解不出时）：
   必须显式给证人（`Fintype`/`Finite` 项），否则审计线被污染而编译仍 RC=0。
17. ~~**`TameSpine.markedListMarked` 带 `sorryAx`**（根 = `TameList16.lean:1109` 的显式
   `sorry`，经 `markedListIsNodeNondegenerate`；连带 `hqymrtx1List` 也脏）。~~
   **ERRATA（2026-11-10 编排者实测，作废本条）**：`TameList16:1109` 已于 `967ebbb5` 真证；
   现 `#print axioms Kepler.Text.TameSpine.markedListMarked` 与 `markedListIsNodeNondegenerate`
   均 = **`[propext, Classical.choice, Quot.sound]`**（零 `sorryAx`）。⇒ **`IsMarked` 路线已可安全消费**，
   此前按本条绕行的件（`Split1G:17-19` 旧注、`ChainMarkedQ` 部分条件槽、AQ8 W1a 等）可择机简化。
   历史事实保留：该债未清前，走它的件会把在案债注进自己 axioms（aqfin r4 实测 0 error 但探针出 sorryAx）。
16. **陈述里写 `let (a,b,c) = f x` 模式绑定，会在最终 defeq 检验时打爆 heartbeats**
   （实测 8M 仍爆，单件编译从分钟级失控）⇒ 改「显式 `a b c` 参数 + 假设
   `h : f x = (a,b,c)`」，前提/结论一字未改（下游传 `rfl` 实例化），编译降到 2 分钟级
   （j3-t9c2 T9D 实测：`splitFace` 三元 let，115 s）。**注意**：这是陈述写法变更，
   虽 defeq 等价也必须在该批 DIFFERS 里记档。
18. **负探针报 unknown 有两个成因，别只查名字**：(i) 名字面改名（HOL 名 → Lean 公开名，
   如 `aq1`/`aq10_*`/`findListSpineMemN`）；(ii) **导入闭包过窄**——探针没 import 到
   定义/已落库的叶文件，件明明在树仍报 Unknown（2026-11-10 AQ12 W1b 实测：
   `ProbeAQ12_neg.lean` 未 import `JcajyduAqLeaf8W0`，`memPartsImp`/`sndMemRtran1` 假阴性）。
   ⇒ 负探针必须按**最新叶文件全集**建 import 闭包，再逐名做语义 grep/`#check` 复核。
19. **`Coplanar` 有两个读法，不许混用**（2026-11-11 stepB W3b 实测）：
   Mathlib `Coplanar ℝ`（秩 ≤ 2，点集张成空间维数）与 `Kepler.Geom.Coplanar`
   （HOL 存在形，显式 `∃ a b c, … ∧ u = a•v + b•w + c•x`）**不是同一个谓词**，
   互转需桥接件。`aff_ge_3_1_rep_cross_dot_p9`（LA9:2773 桩）用 Mathlib 读法，
   而其消费者 `aff_gt_3_1_rep_cross_dot` 与 `properties_fully_surrounded` 用 Geom 读法。
   ⇒ 写/消费仿射几何件时先 `#check` 目标谓词的读法，**同文件内统一一种**；
   跨读法时显式加桥，不许把两者当同义。
20. **e 步跨面陷阱：对 `r`/`N` 的全称「单面/同面」断言先做反例探针**（2026-11-10 AQ8
   实测，**四个已证假**：`ChunkFace`、全 `r` 的 `hR`、`harcF`、`hsface`）。根因：
   `NormalListSpine` 的 `loopListSpine` 只保证每步 `nextEl r x = fList L x ∨ nextEl r x =
   fList L (eList x)`（TameList5:116），**e 步可跨到相邻面**；`fLastSpine` 只钉闭合步。
   配 `nextRNotEqF`（Split1C:50）在 `y = lYSpine` 处必走 e 步 ⇒ `r` 同时含两个面的 dart。
   ⇒ ① 面成员性只从 **f-弧**（`betwn (findFaceDarts L x) …`）或显式假设取（`betwnMem` +
   `aq10_memFindFaceImpFacesEq`），不从 `normal_list` 反推；② 任何「`parts L r` 上单射 /
   同 node ⇒ 同 part / 全 r 在面 x」类断言，先写 10 行反例探针再立件（AQ8 W3d/W3f/W3h/W3i
   四个判定件因此省下数百行死路）；③ 已落条件形若前提被证假，**保留件不动**、另立收窄件
   （`aq8w3i_fstHdInjPartsFaceArc` 是范例）。
21. **shell 文本搜索一律 rg，严禁裸 `grep -rn` 扫仓**（2026-11-13 用户裁定，实测裸 grep
   扫全仓 444 s——`.lake` 的 olean/二进制 + `reference/` 巨文件 + `_distfiles/` 全被逐字节啃）。
   本机 rg 在 `~/.kimi-code/bin/rg`（v15），**默认遵守 .gitignore**（本仓 `.lake/`、
   `*.olean` 已覆盖 ⇒ 自动跳过构建池）；确需兼容 grep 时必须 `-I`（跳二进制）+
   `--exclude-dir={.lake,.git,reference,_distfiles}`。车道的 Grep/Read 工具不受影响，
   但任何 shell 兜底检索都按本条执行；工单模板已同步改写。
22. **subagent 中断潮三形态 + 僵尸锁正解（2026-11-13 当日 17 例实战定性，零成果丢失）**：
   三形态——(a) turn 无终讯截断（wire 停在 `step.begin`、全程零 error 记录）；
   (b) **假失败**：通知 failed/completed 但 agent **还活着继续干活**（tmxllipls-w1 实证：
   「failed」后 14:06→14:40 连续产出含工具调用，继任车道 ps 侦察发现、核实其成果正确后主动退役）；
   (c) resume 撞 "already running" —— 两因：实例真的还在跑（假失败型），或实例已死但注册表
   未回收（截断型，ps 无进程仍撞锁）。
   **根因（2026-11-13 实证修正）**：当日下午中断潮 = **账户 5 小时滚动配额（429）逼近/触顶
   的症状**——续跑撞出硬错误 "You've reached your 5-hour usage limit"（官方 error-reference
   原文）；配额见底前请求被静默丢流，表现为形态 (a)/(b)。非引擎过载、非机器问题。
   办法（全链路已验证 18 例零成果丢失）：① fresh 接管**前必做 ps 预检**（`ps aux | grep <车道名>` + 工作区
   文件 mtime 双查）——前辈活着就让它干完（留 `ORCHESTRATOR_NOTE.md` 进其快照目录通信，
   不派继任）；② 工单硬纪律第一条 = **开场先把起点文件落盘 b/ 再干活**；③ 接管从快照
   WIP 续，绝不从 HEAD 重来；④ 里程碑落盘制（每轮编译/每段收口覆盖写快照）是生死线；
   ⑤ resume 撞锁等 90s 重试 ≤2 次即转 fresh，不三试。每次中断记 pq §8，
   假失败变体曾修正既有彻查结论（续1037 → 续1038 ERRATA 式更新）。

23. **交付泄漏（2026-11-13 pick 审计，用户令；jlxfdmj-w1 / vasw0-w1 / k4cprep-w3 三例）**：
   ① 车道**晚交付**——jlxfdmj-w1 被通知 failed/零工件、编排者已发 fresh w2，1.5h 后它又产出
   50KB patch + 完整 DELIVERY（假失败变体的延长版）；② **patch 未落快照**——vasw0-w1 的
   `make_patches.sh` 从未执行，DELIVERY 里列的 patch 文件在快照里不存在，只有 `/tmp` 工作区还有；
   ③ **交付≠picked**——k4cprep-w3 11:02 已交付 LA18 +135/−31（3 sorry），但编排者一直按
   「K4c 挂起、WIP 在 rescue」记，直到全面审计才发现。⇒ 硬纪律：**工单必须要求 patch 文件
   写进快照**；编排者每次接管/收工前按 mtime 扫最近目录，凡「有 DELIVERY/Evidence、无 LANDED
   commit、无 pq 落库记录」立即 pick 或显式退役；被 fresh 取代的前代目录不删，回扫到其最后
   mtime。审计方法：`git log --grep=<lane>` + `git apply --check` + pq 关键词三查。


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

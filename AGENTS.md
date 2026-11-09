# AGENTS.md — 本仓库的硬规则

> 给所有接手本仓库的 agent。**先读这 60 行，再动手。**
> 违反下面任何一条，产出作废——不是"下次注意"，是作废。

## 1. 目标与验收

- 终局（**用户 2026-11-06 裁决**）：**不比 Flyspeck/Isabelle 更差**，不是完美标准三。
  验收式：`#print axioms Kepler.the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean:22`）
  = `[propext, Classical.choice, Quot.sound]` ∪ **恰好 585 条地面 `native_decide` 公理**，且
  1. **零 `sorryAx`**（锥内 78 条 sorry 是唯一还算"债"的东西）；
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
  5 条车道并发编译 ⇒ **28 GB 需求 > 18 GB 物理**，这才是换页风暴/压力升到 critical(4) 的来源。
  普通进程不是问题：同一测量里 3 GB 分配 **0 pageouts、压力不变（1）**。
  ⇒ 车道起编译前必须确认“此刻没有别的 lean 在跑”；编排者侧只放行一个。
- **swap 会动态伸缩**，不是只增不减：2026-11-09 实测从 **84.8 GB 回落到 25.5 GB**
  （无需重启），单次编译又会长回去 **+3.2 GB**。所以 **`swapused` 本身不是告警指标**；
  判据 = `kern.memorystatus_vm_pressure_level`（1 正常 / 2 警告 / 4 危急）+
  `pageouts` 增量 + 并发编译数。**不许只看 `Pages free`**（macOS 的 free 常年很小）。
- 用户保留项：certtm 的 TM3 / Mono* hold；D 证书层解冻 hold。不要单方面动。

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
4. `List.append_eq_nil` 不存在；`List.getElem_append_right` 的 `h₂` 须具名传参；
   `List.Disjoint` 是 `∀ a∈l₁, ∀ b∈l₂, a≠b` 形，收口用 `(hdisp _ hx1 _ hx2) rfl`。
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

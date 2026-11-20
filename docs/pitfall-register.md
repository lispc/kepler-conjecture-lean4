# Pitfall Register — 全仓雷区登记册

> **定位（2026-11-19 用户裁定：AGENTS §7.1 最多维护 20 条）**：本册是雷区的
> **唯一全文登记处**；`AGENTS.md` §7.1 只保留 ≤20 条现行高频条的精简版。
> **维护规则**：
> 1. 新雷区先入册（全文 + 出处 lane + 日期），再视频率晋升 AGENTS；
>    晋升条件 = 两周内 ≥2 车道踩中，或属禁造/锁/池级基础设施事故。
> 2. AGENTS 满 20 条时，最低频者降级回本册，AGENTS 只留映射行。
> 3. 编号沿用历史号（PR-N ↔ 原 AGENTS §7.1-N），不改号——外部文档大量引用
>    `§7.1-N`；合并条目在 AGENTS 侧标注合并的 PR 号。
> 4. 降级 ≠ 作废；只有精确反例/勘误才作废（加 ERRATA 标记，不删原文）。

## 0. AGENTS §7.1 现行 20 条 ↔ PR 号映射（2026-11-19 重组）

| AGENTS 条 | 内容 | 吸收的 PR |
|---|---|---|
| 1 | 注释 lexer（字面 `-/` + comment-depth） | PR-1, PR-5 |
| 2 | 库形状（iterate/append/Disjoint/nodup/Perm/getLast!） | PR-3, PR-4, PR-11 |
| 3 | 改写次序（rw 首匹配 / ite .2 / getElem motive） | PR-6, PR-12, PR-10 |
| 4 | 签名与展开先查再写（eq_N / 实参序 / sq_sqrt 方向 / 括号 / HOF 拆分） | PR-2, PR-29, PR-30, PR-31, PR-28 |
| 5 | 本树无 Mathlib tactic（tauto→grind） | PR-8 |
| 6 | unknown 先查 import 面；负探针按最新叶闭包 | PR-4 尾注, PR-18 |
| 7 | grep 命中 ≠ 声明 | PR-7 |
| 8 | open 错名整条失效 | PR-13 |
| 9 | error 计数 0 与 axioms 双检 + autoParam 污染 | PR-14, PR-15 |
| 10 | 陈述禁 let 模式绑定；陈述写法变更记 DIFFERS | PR-16 |
| 11 | 数学断言先反例探针；Coplanar 两读法不混用 | PR-20, PR-19 |
| 12 | shell 一律 rg；`-r` 是 replace | PR-21 |
| 13 | 状态以事实源为准（通知双向假 / wire / mtime 收账 / sync_lean 例行） | PR-22, PR-24, PR-23, PR-34 |
| 14 | def 勘正双重对表；视同陈述改动 | PR-25 |
| 15 | patch 头双侧路径 + rename 事故签名 | PR-26 |
| 16 | 长上下文退化 → fresh；编排者 3 轮止损 | PR-27, PR-33 |
| 17 | 量产批量错 → 生成器整文件重生成 | PR-32 |
| 18 | tactic 块行首 `-` 是 bullet | PR-35 |
| 19 | 池纪律：复制式 island、禁 ln -s、.lake 只读、LEAN_PATH 独占解析 | PR-36, PR-9 |
| 20 | 锁纪律：禁 exec 起 lean（丢 trap）；无主锁取证后清 | PR-37 |

未入 AGENTS 的册内条目：PR-17（已 ERRATA）、PR-38–49（handoff 五条 + 2026-11-19 新增八条：linarith 原子化 / 短命脚本重写 / 时间戳实测 / guard-槽序 / 判死公式核对 / 语法恢复假绿 / 拷入核源池零链接）。
外部散件索引见 §F。

---

## A. Lean / tactic 陷阱

**PR-1 注释正文禁字面 `-/`**（同车道 6 次、跨车道多次）：哪怕在引号内，lexer
照样提前闭合注释，后续 `import` 全变垃圾。注释框统一用 `└──…` 收尾。

**PR-2 def 展开先查方程引理**：`rfl`/`show` 失败时先 `#check foo.eq_1/eq_2/eq_3`
——RHS 常是 Prop-ite 而非 `bif/cond`，按 `cond` 写必错。

**PR-3 构造树方向**：`Nat.iterate` 右嵌套、`List.append` 左结合（`infixl`）；
pow/拼接目标必须按此摆。

**PR-4 List 形状与 import 面**：`List.append_eq_nil` 不存在；
`List.getElem_append_right` 的 `h₂` 须具名传参；**`List.Disjoint`（Batteries
Data/List/Basic.lean:544）真实形状 `∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False`**，
收口用 `(hdisp hx1 hx2).elim`；`List.nodup_append` 第三分量才是裸两变量
`∀ a, a∈l₁ → ∀ b, a∈l₂ → a≠b`；互转各需一个 lambda。尾注：`#check` 报
unknown identifier 时先怀疑探针 import 面，再怀疑存在性（2026-11-10 有车道
因 bare-prelude 误判 `List.Disjoint` 不存在）。

**PR-5 批量改注释先跑 comment-depth 核查**（`/-` 与 `-/` 计数），否则层次归零。

**PR-6 `rw` 只重写首个匹配**：`simp only [if_pos/if_neg h]` 重写全部匹配 if；
LHS/RHS 各带同条件 `if` 时 `rw [if_pos]` 只改一边，会伪造「类型不匹配」假象
（j3def 连续 8 轮，一替换即全绿）。另：`exact f a _ (by tactic)` 里元变量与
tactic 实参求值次序有坑，显式给实参。

**PR-8 本树无 Mathlib tactic**：`tauto` 不可用（unknown tactic）⇒ 命题收口用
core 的 `grind`（j3def T9 五处一次通过，产物标准三）；`simp only [...]` 的
unusedSimpArgs linter 警告不影响 RC。

**PR-10 `rw [← h]` 在 `getElem` 上 motive 不 type correct**（依赖索引）：改私有
`getElem_eq_of_eq`（证明无关，`rfl` 级）+ `rw` 该等式。

**PR-11 命名法与参数名**：`Perm` 的 `~` 是 scoped notation——裸文件写
`List.Perm xs xs'`；`List.getD_eq_getElem` 界证明参数名是 `hn`（非 `h`）。

**PR-12 `(ite c a b).2` 不 defeq `ite c a.2 b.2`**（`c : Bool` 变量表达式时
Decidable 不归约）：别用 `change` 推进 ite 分支；先 `rw [show β = ite形 from rfl]`
展开本体，再 `by_cases` + `if_pos/if_neg`。

**PR-13 `open Foo (fList eList …)` 写错一个名字整条 open 失效**，且只报该名一处，
随后满屏 unknown identifier ⇒ 先核 `#check` 真实命名空间（`fList`/`eList` 在
`Kepler.Assembly`，不在 `Reduction5`）。`getLast!` 按前缀构造子递归
（`(l++[a]).getLast! = a` 走 `getLastD_concat`；`l.reverse.getLast!` 需对
`l.reverse` 用再 `reverse_reverse`）。

**PR-16 陈述里写 `let (a,b,c) = f x` 模式绑定，最终 defeq 检验打爆 heartbeats**
（实测 8M 仍爆）⇒ 改显式 `a b c` 参数 + 假设 `h : f x = (a,b,c)`，前提/结论
一字未改（j3-t9c2 T9D：115 s）。陈述写法变更（含 defeq 等价）必须记 DIFFERS。

**PR-28 `HasDerivAt` 链嵌套 add 的 HOF 贪心值拆分**（2026-11-18 ox3q1h S2a）：
`refine HasDerivAt.add` 的 unifier 贪心拆分与 piece 树分组不一致时逐层 mismatch。
对策 = hfun 分组括号重写：`have hfun : (fun t => poly) = fun t => (组₁)+(组₂) :=
by funext t; unfold D; ring`，然后 `rw [hfun]`。

**PR-29 Mathlib 实参序双坑**（同日连环实证）：`HasDerivAt.const_mul (c) (hc)` c 在前；
`hasDerivAt_const (x) (c)` x 在前。新引理首次使用先 `#check @Lemma.name`。

**PR-30 `Real.sq_sqrt` 是错引**：证 `(√a)² = a` 用 `pow_two` +
`Real.mul_self_sqrt hx`；`Real.sq_sqrt` 证 `√(a²)=a`（方向不同）。同文件踩两次。

**PR-31 整值最外层必须括号**：`Term / (DEN) x1` 中 `(DEN) x1` 被吃成函数应用。

**PR-32 生成器整文件重生成 > 增量正则补丁**（2026-11-18 ChainBatch1：kn-wrap
正则截断供给行 12 处）——量产文件批量错时不做增量补丁，改参数重跑生成器。

**PR-35 tactic 块行首 `-` 是 case bullet**（2026-11-18 S2a）：多行项续行以 `-`
开头被解析为 bullet → 后续全乱。续行 `-` 挪到上一行行尾（`… -\n    (…)`）。

**PR-48 语法错误后的 parse recovery 照样建声明，`#print axioms` 会假绿**
（2026-11-19 ztg-bernstein-pilot 编排者探针实证）：定理签名写成
`(x1 : ℝ, x2 : ℝ, …)` 逗号 binder（Lean 4 定理签名不收）⇒ 单点语法错误、
RC=1、不写 olean；但 Lean 的错误恢复**仍把该名声明进环境**，文件尾
`#print axioms <该名>` 照样打出「does not depend on any axioms」——
自审计行在**签名已损坏**的前提下假绿。探针三行复现：
`theorem t (x : Nat, y : Nat) : Nat := x + y` + `#print axioms t`
→ 一条 error + 一条假绿。这是 AGENTS #9「error 计数 0 与 axioms 双检
缺一不可」的最硬实证：**只看 axioms 行会收下一个陈述已损坏的定理**。
推论：任何文件的文件尾自审计在 error≠0 时全部作废；发射器顶层模板与
量产模板必须同构（本例量产 2,427 条全空格形 ✓、顶层 1 条逗号形 ✗）。

## B. 陈述与审计纪律

**PR-7 grep 命中 ≠ 声明**：同名符号可能只在注释/排期注记里（2026-11-09 实测
六件全树仅注释命中）。判「已落」必须 `#check` 或
`rg -E '^(theorem|lemma|def|noncomputable def) <name>'`。

**PR-14 error 计数与 axioms 双检**：有未解目标的声明会以 `sorryAx` 进入环境
（不只 error 时）；一处 error 可让另一处未收口声明静默带债；private helper 的
error 会为失败声明合成 sorry 占位污染下游（wsewpch wave1）——「意外 sorryAx」
先查同文件 error，再怀疑证明。

**PR-15 `Set.ncard_eq_toFinset_card` 的 autoParam 静默插 `sorryAx`**（Finiteness
解不出时）：必须显式给证人，否则审计线被污染而编译仍 RC=0。

**PR-25 私有 def 实参序勘正先双重对表**（2026-11-13 n2def-w1：车道把
`planar2F_p21` 实参序按 HOL 第一版 :1038 改，但被改 def 属第二版、锚序本来就
对）：① 先查 def 直接消费者；② HOL 同文件多版本定理时锚序对上对应版本；
③ 改 def = 改所有消费者语义，视同陈述改动走 SF/DEF-FIX。

**PR-26 patch 头必查 a/b 双侧路径**（2026-11-14 hexsym-w1：b 侧 `/tmp/...` 被
判 rename，apply --check 照样 PASS，应用后目标文件被删、成品落 tmp/）：apply 前
`head -5` 看双侧须 `a/lean/... b/lean/...`；apply 后 `git status` 必查（`D 目标`
+ 未跟踪 `tmp/` = 事故签名）。

**PR-38 patch 面常比工单多**（2026-11-18 SF 111 是 14 不是 12）：工单写「N 文件」
时以实际依赖闭包为准；两个 kit 可能是类型检查必需。

**PR-39 落地审计三件套**：`shasum -c manifest` → 从落地源按 import 序重编 →
自己写探针 `#print axioms`；不要只信车道日志。

**PR-40 SF 类独立断言**：逐文件数前提 + 检查所有删除行只落在调用点（SF 111：
387 前提、596 删除行全部 hstep/hsl/hslp）。

**PR-41 `decide +kernel` 证明项不引用数据 def**（kParams/kBox 只在类型里）⇒
K_REACH 增量远小于叶数×声明数，属正常，勿误判。

**PR-42 文件尾 `#print axioms <名>` 可能解析到同名旧定理**（ChainBatch2 尾部
解析到 Chain3 旧试点）：审计必须用显式探针。

**PR-43 linarith 对乘积项做语法原子化**（2026-11-19 `cell3-wt2a-core-w2`
v9 实测）：`Y·(A+B+C)` 无法与 `Y·A+Y·B+Y·C` 配对——linarith 按语法树匹配
而非模分配律。对策 = 把包络值分布成三个独立 `+` 项、`hmargin` 与部件同括法
书写；量产生成器必须沿用同一书写规范。
（同车道另两条 WIP 级勘误，入册供后人对照：① 前代 WIP 的 `dlt_anti_b/c`
恒等式本身写错——按真族交叉积 `4·b·c` 重写陈述与证明后才收口；② Lean 的
`lfun`（PackingAuto2.lean:466）是纯线性函数、无 ite，前代按 python 版 if 形
写错——**符号断言以 Lean 定义为准、不以数值脚本镜像为准**。）

**PR-44 重写「被反复调用的短命脚本」会咬在飞实例**（2026-11-19 编排者实事故：
重写 orch_compile.sh 锁协议时，一个正在锁循环里的旧实例按字节偏移继续读
**新脚本文本** → 撞上 `SLOT: unbound variable` 崩溃，编译静默未发生；外层
管道的 `head` 还把 rg 的失败码吞成 exit 0）。对策：① 改这类脚本用「新文件名 +
调用方切换」或先确认无存活实例（`pgrep -fl <script>`）；② 后台任务判定成败
以**产物存在性**（olean/日志里的 time 行）为准，不以管道 exit code 为准。

**PR-45 账本时间戳必须实测，不许估值**（2026-11-19 编排者自纠：续1281/1282
两条 pq 日志的时间戳是写时的估计值，比真实钟快了 25–70 分钟，已入 ERRATA）。
对策：写任何带时间戳的账目行之前先跑 `date`，禁止凭感觉填；条目已发出后
发现时间戳错，加 ERRATA 不覆写。

**PR-52 发射器 replica「逐位复现」≠ kernel 语义一致——验波必须含 kernel 真类抽样；
进度心跳必须墙钟制（2026-11-20 `iyou-build-w1` L23 实证）**：L23 叶数据坏源的定性
走了三步才到位——最初疑「salvage 谎报」，replica 对 20:15 json 逐位复现（lb/ntr/salv
全同）后又疑「数据没错」；最终 64MB 栈下的 kernel decide 判 **8/12 叶事实为假**。
根因 = **replica 与 kernel 在宽盒 regime 有语义暗区**（43-triple 真类与 55-triple 假类
之间的区域未定界），replica 自洽完全掩盖了它。对策：① 波验证**必须**含 kernel 真类
抽样——代表性叶送过真实内核（本例一次 1,097 s 的编译就揭穿了整批数据），replica
复现不构成免检；② cap-47 发射器的 TWOP 填充维在真维耗尽后**无限对半分裂**（旧版
零宽维天然免疫）——发射器改动引入新死症时，旧免疫不算新安全；③ **评估心跳用
eval 计数有盲区**（卡在循环前的根检查则永不打印，82229 楔死被它藏了数小时）——
长跑监控一律墙钟心跳。翻案资产：BLOCKED-forensics 与 15 件工具在
`~/c17_backup/lane_snapshots/iyou-build-w1/`。

**PR-51 车道 git 操作必须带 cwd 守卫；`git clean` 不可用于 scratch 管理
（2026-11-20 `cases-swap-c840-w1` 自愈事故）**：车道在 scratch 仓模拟 apply 时
先跑了 `git clean`（误删自身 sim 目录），随后一条 `cd` 失败且无守卫 →
`git apply` 落在**主仓工作树**（497 D + 1 M + 未跟踪件；index 未动）。08:38
车道自查发现后即刻 checkout+rm 还原，终态 tracked 零改动、68 未跟踪件与开工
同集（编排者闸前独立复核确认：`git status` 非?? 行=0、家族 499 件与 HEAD
零差异）。对策：① 车道任何 `git apply/add/rm` 前必须断言 cwd（非
`/tmp/<lane>/…` 即退出）；② scratch 清理一律 `rm -rf <具名目录>`，禁
`git clean`（cwd 漂移时清错树且无确认）；③ 车道工具每次 git 操作后顺手对
主仓跑 `git -C <主仓> status --porcelain | grep -v '^??'` 应为零（早检早报）。
PR-15 的「apply 后必查 status」检测面保留；本条补「车道侧防误」面。单次
自愈、零落地损伤，未达 §7.1 晋升门槛，先入册。

**PR-50 `pgrep 'bin/lean -o' 会把 `/usr/bin/time` 包装进程一并命中（2026-11-19
恢复链误杀）**：编排者看到「两个进程在编同一文件」误判为孤儿+现行双编译，
按 PPID 取证杀了「较老」者——实为**同一编译的 wrapper+lean 对**（time 包装的
命令行内嵌完整 lean 命令，etime 与子进程相同）。结果误杀现行编译（浪费 14 min，
链自愈进散件重试）。对策：pgrep 杀 lean 前必须沿 PPID 链核对——包装进程
PPID = 车道脚本、lean PPID = time 包装；「同文件双进程 + etime 相同」的签名
= 一对编译，不是两路。

**PR-49 向主池拷入前必须核「源池零链接」（2026-11-19 编排者自伤事故，
PR-36 同源）**：从历史岛池向主池回灌 olean 时，源池 `/tmp/tskasm-land-w1/pool`
是 11-17 旧链接式设计（其「文件」是指向主池自身的 symlink）；
`rsync -a --ignore-existing` 对「源=链接、dest=真文件」的**类型错配不做跳过**
——逐个把主池真实 olean 替换成自指死链（36,198 件、主池 Kepler 段全灭）。
教训：① 复制式纪律从「建池」扩展到「从任何历史池拷入」——拷前源必须过
`find <源> -type l | wc -l` = 0，非零即停；② `--ignore-existing` 不保护
类型错配，链接式源池永远不可作为 rsync 源；③ 编译缓存是唯一易失层——
git 源码 + 复制式物理件 + 快照是恢复三支柱（本次 XLLIPLS 物理件与今日
全部落库件幸存即因此）。恢复成本：4,499 件重编 ≈ 1–1.5 天。

**PR-46 护栏等待不得占槽（slot-after-guard）**（2026-11-19 iyou 车道饿死
事故实证：orch_compile.sh 先取槽后过 guard——一个 8.2 GB 大件把 pressure 顶到 2
后，**所有等待者各自占着一个槽在 guard_wait 里 45 s 轮询**，三槽被不推进的
等待者占满，全场死等 72+ 分钟、LP 双链 23 分钟零推进、iyou 车道全程 0 分钟
编译时间收线）。对策：① 正解 = guard 先行、过闸后再取槽（等待者不持槽）；
② 修复窗口须在无在飞调用方时（PR-44 mid-flight 重读约束）——当前以「杀掉
压力源头 + 人工排终局链」过渡，脚本改造排入下一次静默窗口。

## C. 车道流程与交付

**PR-18 负探针按最新叶闭包**（2026-11-10 AQ12 W1b：探针未 import
`JcajyduAqLeaf8W0`，`memPartsImp`/`sndMemRtran1` 假阴性）：负探针必须按最新叶
文件全集建 import 闭包，再逐名做语义 grep/`#check` 复核；unknown 有两个成因
（改名 vs 导入闭包过窄），别只查名字。

**PR-22 中断潮三形态 + 僵尸锁正解**（2026-11-13 17 例）：(a) turn 无终讯截断；
(b) 假失败（通知 failed 但 agent 活着继续干）；(c) resume 撞 already running
（真在跑 vs 注册表未回收）。办法：① fresh 接管前必做 ps 预检 + 快照 mtime 双查；
② 开场先落 b/ 起点文件；③ 从快照 WIP 续，不从 HEAD 重来；④ 里程碑落盘制是生死线；
⑤ resume 撞锁等 90 s 重试 ≤2 次转 fresh。

**PR-23 交付泄漏三态**（2026-11-13 三例）：① 晚交付（假失败后 1.5 h 又产出
patch）；② patch 未落快照（DELIVERY 列的文件不存在）；③ 交付≠picked（已交付
但账本按挂起记）。硬纪律：工单必须要求 patch 写进快照；接管/收工前按 mtime 扫
最近目录，「有 DELIVERY 无 LANDED commit」立即 pick 或显式退役。

**PR-24 通知双向误报**（agent-52/51 实证，仅 Kimi Code harness）：completed/
failed 都可能是假的。判死/判活唯一准则 = agent wire.jsonl mtime 是否 1 分钟内
增长；收 completed 通知也先查活性。绝不因通知就归档遗产/撤单/派接管。

**PR-27 长上下文退化 → 果断换 fresh**（2026-11-17/18 双向实证）：sub agent
多轮 resume 后 micro-turn 化；编排者接管也同退化。处置 = 交接包落快照后立即
spawn 新鲜 session；接管 3 轮未收即停手交回车道。

**PR-33 编排者接管也退化**：见 PR-27（合并记）。

**PR-34 车道交付物落快照入轮末例行**（ox3q1h 连续 5 次快照缺 lean/ 镜像）：
sync_lean.sh 固化到轮末例行；编排者代抄 5 次后移交车道自管。

**PR-36 symlink farm 穿透**（2026-11-19 lp-packed-single-leaf-w2 实事故：父目录
穿透后批量 `ln -sfn`，主仓大量 LP 构建产物被替换为自指死链，970 件受损、193
olean 待重编）：任何 `ln -sfn` 前必须对目标父路径每一级 `test -d && ! -L` 并
`readlink -f` 核到 farm 根；`Kepler` 根仍是 symlink 时严禁写其子层，先干跑打印。
发现误写立即停手、清点、保全快照并报告；构建池恢复另批不擅自重建。精确事故
范围以 `docs/priority-queue.md` 文件头为准。**现行正解 = 建 island 池一律复制式
（cp/rsync），主仓 `.lake` 对车道只读，写前 `test -L`、开池后
`find <池> -type l | wc -l` 须为 0。**

**PR-37 编译脚本禁 `exec` 起 lean**（2026-11-19 fat1-g-positivity-w1 实事故：
`exec nice lean …` 替换进程镜像，EXIT trap 不存活 ⇒ lean 退出后全局锁
`/tmp/lean_global_lock.d` 永不释放，两把无主锁把全场编译各楔死 ~20 min，
compile5–8 空日志 = 各自 20 min lock timeout）：锁脚本一律非 exec 调用 lean，
让 trap 在脚本退出时触发；发现无主锁先取证（`pgrep lean` 为空、无日志增长、
无等待外的存活脚本）再 `rmdir`，有效 PID 持锁绝不动。

## D. shell 与基础设施

**PR-9 LEAN_PATH 解析 = 首个含 `Kepler/` 顶层目录的 entry 独占**（Lean 4.32
实测）：引用 /tmp 侧 olean 时该 entry 必须自身含完整 Kepler/ 树，否则解析停在
该 entry 报「object file … does not exist」。探针最简法：把新 olean 装进
`.lake` 再跑（现行正解 = 复制式池，见 PR-36）。

**PR-21 shell 文本检索一律 rg，禁裸 `grep -rn` 扫仓**（实测裸 grep 全仓 444 s）：
本机 `~/.kimi-code/bin/rg`（v15）默认遵守 .gitignore（.lake/*.olean 自动跳过）；
兼容 grep 时必须 `-I` + `--exclude-dir={.lake,.git,reference,_distfiles}`。
变体：`rg -rn` 的 `-r` 是 replace 旗标（mangle 输出仍 RC=0）——`-n` 必须独立写。

## E. 数学认知陷阱

**PR-19 `Coplanar` 两个读法不许混用**（stepB W3b）：Mathlib `Coplanar ℝ`
（秩 ≤2）与 `Kepler.Geom.Coplanar`（存在形 `∃ a b c, … ∧ u = a•v+b•w+c•x`）
不是同一谓词，互转需桥接件；同文件内统一一种，跨读法显式加桥。

**PR-20 e 步跨面陷阱**（AQ8 四个已证假）：`NormalListSpine` 的 `loopListSpine`
只保证每步 f 弧或 e 步，**e 步可跨到相邻面**；⇒ 面成员性只从 f 弧或显式假设取；
「单射/同 node ⇒ 同 part/全 r 在面」类断言先写 10 行反例探针再立件；已落条件形
前提被证假时保留件不动、另立收窄件。

**PR-17（ERRATA 作废，历史保留）**：~~`TameSpine.markedListMarked` 带
sorryAx~~——`TameList16:1109` 已于 `967ebbb5` 真证，现标准三；`IsMarked` 路线
可安全消费；按本条绕行的旧件可择机简化。历史事实保留（该债未清前确实污染
下游 axioms 面）。

**PR-47 「不可能性」定量断言必须先对已落库已证规范形核公式**（2026-11-19
`cell3-sqrt8-sa-math-w1` 实证）：math5-w4 路线图 §9 的「sqrt8 a-矩形损失
0.0293 = 8×角点余量 ⇒ 必须 125–512 cell、不可写」判死，用的是与 `NliBanks20`
**已证规范形**（`ea4X/ea5X/ea6X` + `sol_euler4/5/6_eq`）在一般点不一致的
a-公式——两者仅在 y5=y6 对称点巧合相符，角点自检发现不了。真实 a-矩形超额
仅 **1.5×** 余量，朴素链损失大头在 dih/lfun 侧；原判死数字全盘失准。
对策：任何「X 不可行，因为数字」的定量判死入档前，必须先与已落库且
axioms-clean 的对应规范形在**非对称一般点**数值比对一致；对称点核对不算数。

## F. 外部散件索引（全文在各自出处，本册只登记不复制）

| 出处 | 内容 |
|---|---|
| `docs/fill-worker-playbook.md` §5.3 | 本 toolchain 的 Mathlib 改名速查（「这里是雷区清单」） |
| 同上 §5.4' | 2026-10-12 mega 波实测雷区汇总（按线归档） |
| 同上 §5.4 | 各 lane 已知卡点速查 |
| 同上 §6 | 教训日志（2026-11-01/03 收官波） |
| `~/c17_backup/lane_snapshots/hex51-w2/`（DELIVERY §5） | 雷区六则 |
| `~/c17_backup/lane_snapshots/pent4-w1/`（DELIVERY §4） | 雷区八则 + §6 遗留清单 |
| `docs/la3-wrgcvdr-handoff.md` | 新雷区五条（ncard 是 ℕ 值/autoParam/Equiv.Perm.coe_pow/‹›取回/eta 展开挡 rw） |
| `docs/assets/biefjhu/PA22g-handoff.md` | 四条（Real.sq_sqrt 方向/eq_div_iff≠0 槽/mul_le_mul 别名参数序/rw 含 x/2 被 ring_nf 展开） |
| `docs/archive/.../mono-corner-scout.md`（W5） | 六条（裸区间镜像≠内核宽度/isqrt 低精度/zip 截断静默/gsplit 队列须重排/subboxes 双层 pair/内核保真差） |
| `docs/handoff-2026-11-18.md` §6 | 本轮补充五条（已升格为 PR-38–42） |

> 用户记忆中的「两份丢失清单」即：① fill-worker-playbook 内嵌三节（在仓内但
> 埋在工人手册）；② 车道 DELIVERY 的「雷区 N 则」散件（hex51-w2/pent4-w1 等，
> 长期只在 ~/c17_backup 快照层、仓内无索引）。2026-11-19 起统一由本册吸收索引。

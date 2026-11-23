# NLI 战役下一阶段：共享机件层 + 分层收口（2026-11-23 下午版）

> 接续 [`nli-strategy-20261123.md`](nli-strategy-20261123.md)（上午版）。上午版的三处前提在当天下午被
> 实测推翻，本文以其为准；未提及处沿用上午版。
> 数字口径：SORRIED 49 = 48 `nli*` + 1 hLP、AXIOM 585（pq 文件头）；根面 589 已是 **HEAD 精确态**
> （`84c3b4b4` 后编排者亲跑，pq 续1428）。

## 0. 一页结论

1. **上午版的三个前提变了**：① 根面不再是 binding constraint（池 missing 0，589 可随时复跑）；
   ② cases-swap（W3）首案一天内落库，−82.9% 行数（`ce1b9c87`）；③ wt1 盒成本实测是估算的 5–6×。
2. **方向调整**：从"逐债硬啃"转向 **"先建共享机件层，再让债按机件成熟度分批掉落"**。
   依据：HOL 原版核心机件 14.2k 行（`taylor/` 6.3k + `arith/` 7.9k；另有 `lib/` 3.8k 是
   ssreflect 移植，不算数学机件）vs 逐例层 `ineq.hl` 4k 行，约 **3.5:1**；我们通用层只有 ~2k 行，
   却已长出 30+ 个单点 `*Kit.lean`——每条债都在重造一次同一种轮子。
3. **要建工具库，但不是"把 HOL 技巧翻译一遍"**：原版的"数学结构技巧"只有 5 类，其中 2 类我们已有、
   3 类缺失。缺失的 3 类正好覆盖 27 条农场债 + ZTG/QITNPEA/FHB 三族共享件的结构性瓶颈。
4. **Milestone**：M1 工程闸 + census（本周）→ M2 机件层三件（1–2 周）→ M3 49→38±3（2–3 周）
   → M4 农场解冻裁决的**证据包**（不请求现在解冻）。

## 1. 今天下午的实测修正（对上午版）

| 项 | 上午版 | 下午实测 | 影响 |
|---|---|---|---|
| 根面 | 缺 1,028 olean，不可复跑 | missing 0；589 HEAD 精确态亲验 | Wave 0 完成；每条 −1 可即时根面验收 |
| Assembly 可编译性 | 假设成立 | **自 11-20 起语法不可编译**（孤儿 docstring，`84c3b4b4` 修） | 落库闸新增"Assembly 全编译"硬检查 |
| wt1 单盒成本 | 估 1 盒 ≈ 43 min | p1 组单盒 search 1.5–4 h + 验收 3–4 h+；叶子 5–6× 第二盒 | 16 盒外候选 ≈ 今晚–明天；Lean 装配成本需重估 |
| Interval 压缩 | W3 "需批产" | 首案 `ce1b9c87` 一天落库，剩 4 族同形态 | W3 从"排产"降为"流水线" |
| 通用 Bernstein | W4 "期权，风险大" | ℚ-decide 卡死但 **ℤ-decide PASS**（1,459 条/2.40 s/539 MB） | W4 风险已消，转正式件 |
| 池完整性 | missing=0 即完整 | missing=0 只是 **Final 闭包口径**；非锥模块缺 ~600+ | 全仓可编译性是新债（挂账） |
| ZTG trio | 估 3–5 车道日，需自制 w=2 缩放版 | P1 的 M2 已过闸（18/18 标准三）；结构捷径：trio 凹性 = ½·(w=1 已落库闭式) + (b5/2)·dihY''；角点 439→199 | trio 可能显著快于估算；"复用已落库闭式"正是 §3 K1 的实证 |

## 2. 核心诊断：为什么逐债硬啃会停在 ~45

历史已闭 5 条的手法分布（`nli-strategy-review-w1` §A.3）：WIRE/纯代数 2 条（1 天级），
区间/BB→角点电池 2 条（1–2 车道日，但 margin<1e-5 时 cell 数爆炸），Rule P 农场 1 条
（39–45 h 单 lean，仅窄盒可行）。

**结构**：49 条里
- **6 条**可被"接线 + 共享面"直接收（ZTG trio 3、QITNPEA floor 3）
- **7 条**需要"二阶 + 盒结构"机件（wt1、wt0、FHB a/v2a、sym×3 的结构部分）
- **27 条农场 + 1 TerminalV11 + 2 阻塞 + 3 LP** 靠当前手法**不可清**

前 13 条每一条都在重做：盒分区、二阶包络、角点证书电池、置换对称归约、精确有理叶检查。
**重复的正是机件，不是数学**。这就是工具库的依据。

## 3. HOL 原版到底有哪些"数学结构技巧"（考古结论）

原版 `formal_ineqs` = 核心机件 14.2k 行（`taylor/` 6,299 + `arith/` 7,907；`lib/` 3,811 为
ssreflect 移植不计）；逐例层 `ineq.hl` 4,011 行、80 个 `let`。核心机件与逐例层之比 **约 3.5:1**。
`ineq.hl` 的 80 个 `let` 中，按名字可辨识的模板/`mk_*`/逐例 ID 类占 19 个，其余多为逐例辅助引理与
数据表——**逐例层本身几乎没有可跨例复用的数学，可复用的都在 `formal_ineqs`**。拆开看只有 5 类机件：

| # | 原版机件 | 原版位置 | 我们的现状 | 缺口 |
|---|---|---|---|---|
| K1 | **Taylor 模型区间算术**（一阶/二阶 + 余项 + 基本函数库 sqrt/atan/exp） | `taylor/m_taylor*.hl` 6.3k | `TaylorSecond` 1.2k（`13dee7c8`），仅覆盖 wt1 需要的 6 维 + inv/sqrt/matan | **部分**：基本函数库窄；只服务一个消费者 |
| K2 | **自适应细分 + 规约树**（`bisect_*`、树形证书、glue） | `taylor/` + `ineq.hl` 的 `mk_*`/`template_*` | 每个债一个发射器（`emit_*.py`），树结构手写 | **缺**：无统一树类型 + 无统一 glue 定理 |
| K3 | **凸性/单调性归约到角点/低维面**（`convex` 标签、mono 规则） | `arith/eval_interval.hl`、`ineq.hl` 的 tag 机制 | sqrt8/wt2A 的 `w2a_cell`、ZTG 的 `s26/s2536` 对合、QITNPEA floor——**四个债四种写法** | **缺**：无统一"反单调 ⇒ 角点"与"对称商"机件 |
| K4 | **精确算术底座**（浮点区间 → 有理，`float_theory`/`ipow`/`more_float`） | `arith/` 7.9k | `Base200`/`QInterval`（`13dee7c8`）+ ℤ-decide（W4 实测） | **部分**：ℤ-decide 是新发现，强于原版浮点路线 |
| K5 | **逐例证书的统一消费接口**（`ineq` → `mk_ineq_*` → 模板） | `ineq.hl` | 每债在 `Assembly.lean` 一个槽 + 一个私有桥 | **缺**：无统一 `NliCertificate` 消费形态 |

**结论**：K2、K3、K5 是真缺口；K1、K4 是"已有但太窄"。**原版没有的**（Bernstein 单证书、
ℤ-decide、precompile）是我们自己的优势，不该翻译，该产品化。

注意 W4 车道的考古结论与此一致：原版叶证书是 **float 区间 pass**（靠 `pp` 精度），
Bernstein 在原版只是外部基准例题——**"忠实复刻 HOL"在数值内核层并不成立，原版那一层我们不能照搬**
（我们的验收标准是精确有理 + kernel `decide`，比原版严）。

## 4. 方向：共享机件层（`Kepler.NliKit`）

### 4.1 不做什么
- 不做"HOL 技巧全集翻译"。原版 `ineq.hl` 的 80 个 `let` 里逐例辅助与数据表占多数（模板/ID 类 19 个），
  可跨例复用的数学都在 `formal_ineqs` 的 K1–K4 里，而那部分我们大部分已有（见 §3 表）。
- 不重写既有 30+ `*Kit.lean`。新机件层只对**新债**强制，旧 kit 保持不动（避免语义漂移，§7 风险 3）。
- 不碰 585 基座、不新增 `native_decide`、不走 certtm/TM（hold 不变）。

### 4.2 做什么：三个机件包（按"解锁多少债"排序）

**P-A 盒树机件 `NliKit.BoxTree`**（解锁：wt1 Lean 装配、fat1、ox3q1h、27 条农场的发射器统一）
- 统一二叉细分树类型 + **一条 glue 定理**（叶全负 ⇒ 整盒负），替代每债一条私有桥。
- 输入 = 外部候选（已是 JSON，wt1 盒扫正在量产）；输出 = 单模块 Lean 叶表。
- 验收：用已闭的 wt2A（62 cell）与 sqrt8（26 cell）做**回归**——同一树重放必须得到同一证明项的公理集。
- 这是今天最重要的杠杆：wt1 16 盒 ≈ 2–5 万行叶表，没有统一 glue，装配会是 16 份私有桥。

**P-B 归约机件 `NliKit.Reduce`**（解锁：ZTG joint-6、QITNPEA floor、FHB a/v2a、sym×3）
- 三个原语：反单调 ⇒ 角点；置换对合 ⇒ 商盒；共享下界面 ⇒ 多消费者。
- 把 sqrt8/wt2A/ZTG/QITNPEA 四处已有的写法**抽成一个带回归测试的实现**，不新造数学。
- ZTG trio 车道 P0 已定位两个具体缺口（w=2 二阶缩放版、trio-Wide 盒），正是这个包的第一批消费者。

**P-C 证书消费层 `NliKit.Cert`**（解锁：验收下沉普及 + 合取债的分量记账）
- 统一 `NliCertificate` 形态：`(声明, 证据模块, 公理审计)` 三元组。
- 让 wt2A 式"验收下沉到 90 件闭包"成为模板而非特例；每条 −1 的根面验收从 8.8k 模块降到 <200。
- 合取债（Ox3q1h 230、TerminalV11 109、LpIneqs 127、Kcblrqc 28）按分量记账，杜绝"部分写成 −1"。

### 4.3 与在飞车道的关系
| 在飞 | 状态 | 对机件层的贡献 |
|---|---|---|
| `interval-bernstein-univ-w1`（W4） | Phase 2a-2b | **P-A 的数值内核**：ℤ-decide + 单证书形态直接进 `NliKit.BoxTree` 的叶检查 |
| `ztg-joint6-trio-w1` | P1→M3 | **P-B 的第一个消费者**；M2 对称/转移模块已过闸（18/18 标准三），角点 439→199；其"复用 w=1 已落库闭式"的捷径是 P-B 的实证 |
| `cell3-wt1-box-sweep-w1` | 5 并行，首盒验收中 | **P-A 的第一批输入**（16 盒外部候选 JSON） |
| `eng-acceptance-gate-w1` | **已落库 `93d0f1f9`** | census TSV 是 P-C 记账的数据源 |

**顺序约束**：不在 W4/ZTG 收线前开 P-A/P-B 的 Lean 主工——它们的实测形态就是机件规格。
现在能做的零 Lean 工作：P-A 树类型 + glue 定理的**陈述草案**、P-B 的四债写法对照表。

## 5. Milestone

| M | 内容 | 判据（唯一验收语言 `#print axioms`） | 时程 |
|---|---|---|---|
| **M1** | 工程闸 + census + 池清理 | `eng-acceptance-gate-w1` 落库；`sorry_census --check` 过；D1/E1 两个 ERRATA 入 `DECISIONS.md` | 本周——**已达成**（`93d0f1f9`，pq 续1430） |
| **M2** | 机件层三包骨架 | `NliKit.BoxTree` glue 定理 + wt2A/sqrt8 回归一致；`NliKit.Reduce` 三原语 + ZTG trio 首用；`NliKit.Cert` 形态定义 | 1–2 周 |
| **M3** | 49 → 38±3 | wt1 −1、ZTG trio −3、QITNPEA floor −3、sym×3 −3（EST）；每条根面 589→递减且无意外公理 | 2–3 周 |
| **M4** | 农场解冻**证据包**（不请求现在解冻） | 用 P-A 统一发射器对 3 条代表性农场债做有界 pilot，给出"每条债的真实 CPU·h + 机件复用率" | 与 M3 并行——**架构已定（§4.4），pilot 按"借树+修补+ℤ重放"实测** |

### 4.4 农场架构裁定（2026-11-23 用户拍板）：离线搜索 + 便宜重放，搜索结果直接借 HOL 的

原版考古（`reference/flyspeck/azure/`）证实：原版农场 = **GNU parallel 120 路并发**批量重放
**23,237 个实例**（`ineqs.txt`，逐例带离线调好的 bisect 树），单例验证均值 **~1.0 s**（639 例记账，
`formal_tests/ineq_ids.hl`），验收 = **23,242 条 md5 定理哈希对表**（`theorem_nonlinear_digest.hl`）。
核心架构 = **搜索（离线，不进证明账单）/ 验证（重放已给树）分离**。

我们的对应物与差距：

| 环节 | 原版 | 我们现状 | 动作 |
|---|---|---|---|
| 搜索 | `ineqs.txt` 离线调树 | 盒扫 JSON（wt1 已在产）+ **可直接借 HOL 树**（农场债名 = HOL 家族名：ZTGIJCF4×142、QITNPEA×163、BIXPCGW×67；其余需 prep-/变体映射） | 新车道（待批）：HOL 树收割/翻译（解析 + x→我方编码 SF 逐案映射 + 冒烟角对账） |
| 验证重放 | 原生 OCaml float 区间，~1 s/例 | Rule P 27–31 s/叶（旧）；**W4 ℤ-decide 1.6 ms/条（新，`interval-bernstein-univ-w1` 实测）** | 叶级验证一律走 ℤ-decide 口径；Rule P 只留窄盒特例 |
| 验收 | md5 digest 23,242 条对表 | manifest + `#print axioms`（同构更严） | 不变 |

**信任边界**：借树不借信任——外来树只是候选（搜索不在证明账单里），验证独立（kernel decide on
our encodings）；最坏情形 = 叶太粗 → 离线修补或拒绝；零新增公理、零信任面变化。
**含义**：27 农场债的 21,156 CPU·h 旧估是按"贵重放"算的，按本架构重估可能降 1–2 个量级；
M4 的 3 条 pilot 必须按"借树+修补+ℤ重放"实测，产出可裁决的真实数字。
**已执行**：S5（`nlikit-boxtree-spec-w1`）规格增补——外来树摄入列为一等输入模式、
WT1_REESTIMATE 加"借树 vs 自搜"对照、验证口径换 ℤ-decide（续1433）。

M3 的 38±3 是 EST：ZTG trio 之后的 W2–W4 三债、qitnpea floor 的共享面覆盖（现 UNRESOLVED）、
sym×3 的 Rule P 管线成本都未实测，任一失败都会让数字回落到 42–45。

**M4 的性质**：27 条农场债现在 hold。不请求解冻，只请求允许 3 条有界 pilot——
上午版已算过（recost 26 条 21,156 CPU·h），没有机件层复用就解冻是纯烧机器；
有了 P-A 之后再算一次成本，才是可裁决的数字。

## 6. 短期任务（未来 3–5 天，按可派发性）

| # | 任务 | 类型 | 依赖 | 产出 |
|---|---|---|---|---|
| S1 | wt1 盒扫收线 + 编排者抽盒复核 | 在飞 | — | 16/16 外候选 |
| S2 | ZTG trio（在飞） | Lean | — | 49→46；P-B 规格实测 |
| S3 | W4 收线（在飞） | Lean | — | ℤ-decide + 单证书产品化；`C2485876245b` 翻案与否 |
| S4 | 工程闸落库 | 零 Lean | — | **已落库 `93d0f1f9`**：census TSV；Makefile/CI 不再能打爆机器 |
| S5 | **`nlikit-boxtree-spec-w1`**（新） | 零 Lean | S1 首批盒 JSON | 树类型 + glue 定理陈述草案；wt2A/sqrt8 回归用例清单；wt1 装配行数/编译时间预估 |
| S6 | **`nlikit-reduce-survey-w1`**（新） | 零 Lean | — | sqrt8/wt2A/ZTG/QITNPEA 四处归约写法的逐行对照；三原语的统一陈述；哪些能直接抽、哪些有语义差异 |
| S7 | W3 剩余 4 族 cases-swap | 零 Lean 发射 + 单槽编译 | 无 | 每族 −80~97% 行数；单槽错峰 |
| S8 | T11Glue 全文件补池（非锥 ~600 件） | 单槽编译 | 无 | 全仓可编译性；census 的 import 闭包口径 |
| S9 | 池内容级 stale 普查 | 零 Lean | — | E1 类"旧 olean 掩盖源码错误"的系统性排查 |
| S10 | `iyou` 散落件处置 + IYOUOBFsharpv2 重启评估 | 零 Lean | — | 两批发射对照；是否并入 P-A |

**立即可派**：S5、S6（零 Lean、零依赖冲突）。S7/S8 机器资源够但各占单槽，建议 S1 收线后错峰。

## 7. 风险

1. **机件层语义漂移**（上午版风险 3，机件层会放大它）：一处错误同时污染多条债。
   缓解：每个原语带"第二实现 + 已闭债回归"；常数括号标方向；跨件复用前做消费者形状探针。
2. **机件层变成新的拖延借口**：先建工具、债不动。缓解：P-A/P-B 各自绑定一个在飞的真消费者
   （wt1 装配、ZTG trio），没有消费者签字的机件不写。
3. **wt1 装配成本重估**：16 盒叶数 5–6× 估算，Lean 侧 `decide` 时间可能超出 6–10 GB/2–4 车道日规格。
   S5 的产出必须含这个重估；若超规格，wt1 转为"二阶底座 + 部分盒"的分量记账，不硬凑 −1。
4. **"复刻 HOL"的口径陷阱**：原版数值内核是 float 区间，比我们松；K1–K5 只借**结构**，
   数值验收一律精确有理 + kernel `decide`。

## 8. 证据
- 上午版战略：[`nli-strategy-20261123.md`](nli-strategy-20261123.md)；分诊报告
  `~/c17_backup/lane_snapshots/nli-strategy-review-w1/REPORT.md`（§A.3 已闭手法、§B.1 kit vs 单点）。
- 原版机件行数：`reference/flyspeck/formal_ineqs/` 实测 `wc -l`——`taylor/` 6,299、`arith/` 7,907
  （合计 14,206）、`lib/` 3,811（ssreflect 移植，不计）；`text_formalization/nonlinear/ineq.hl`
  4,011 行 / 80 个 `let`（名字可辨识的模板/`mk_*`/逐例 ID 类 19 个）。
- W4 考古（原版叶证书 = float 区间 pass）：`~/c17_backup/lane_snapshots/interval-bernstein-univ-w1/design.md`。
- 实测修正各项：pq §8 续1425（池归零）、续1428（E1/589/W3 落库/可视化）、续1429（D1）。

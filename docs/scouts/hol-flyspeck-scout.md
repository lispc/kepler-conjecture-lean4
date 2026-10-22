# HOL / Flyspeck 参考侦察报告：非线性不等式证书的数量级、粒度与并行组织

> 落库版说明（2026-10-22）：只读侦察产出；正本与证据在
> `~/c17_backup/lane_snapshots/holscout/{REPORT,EVIDENCE}.md`。本报告回答
> "251k 叶 / 121 天量级是否设计问题"，与同周 gen-10 常数烘表探针
> （同题 145 CPU-天、64 核约 2.3 天）互相印证，两份结论同批入档。

- 日期：2026-10-22
- 车道：HOL 参考侦察（只读；主仓 `/Users/zhangzhuo/repos/kepler-conjecture-lean4` 零改动）
- 证据：`EVIDENCE.md`（逐条 file:line / URL）；本文中 `[原文]` = 直接引自源文件/论文，`[实测]` = 本仓已有实测记录，`[推断]` = 我的推断，`[未找到]` = 仓库/公开材料中没有。

- 路径简写：首次给出完整路径后，`m_verifier.hl`/`informal_search.hl`/`certificate.hl` 等简写指同一目录；`gen9/REPORT.md` = `~/c17_backup/lane_snapshots/w8rung/gen9/REPORT.md`。

## 0. 结论先行

1. **Flyspeck 的非线性不等式不是"每叶一张 251k 级证书"**。公开口径是：约 1000 条不等式，定义域被预处理切成 **>23,000 个子域**（case），每个 case 跑一次 `verify_flyspeck_ineq`/`verify_ineq`；`formal_ineqs` 内部还有一棵 Taylor/单调性/二分搜索树，但它是**一个定理内部的结果树**，不是每叶一个 `decide` 定理。[原文：arXiv:1501.02155 §5；`reference/flyspeck/azure/README.md:42-50`]
2. **证书里检查的是形式化区间算术 + 二阶 Taylor 近似**，在 HOL Light 里用 base-200 的形式化浮点逐操作生成定理；不是 LP，也不是把整个表达式交给内核 `decide`。LP 是另一条独立流水线（43,078 个 LP，约 15 小时）。[原文：arXiv:1501.02155 §5、§9；`formal_ineqs/verifier/m_verifier.hl:1315-1328`；`formal_lp/README.txt:66-67`]
3. **搜索/剪枝顺序**：先裸区间快路径 → 再二阶 Taylor 上下界 → 再单调性（偏导定号，把维度钉到面）→ 再凸性（可选）→ 最后沿最宽维二分；`max_depth=200`、`mono_depth=200`；`default_params` 打开自适应精度。[原文：`informal/informal_search.hl:101-205`；`verifier/m_verifier_main.hl:556-562`]
4. **共享/复用是显式设计的**：`result_tree` 有 `Result_pass_ref`（同一子树证明在多个子域复用）和 `m_cell_pass_subdomain`（大域证明直接降到子域）；预处理把 5×46=230 条不等式合并成一条 13 变量不等式；最终用 MD5 校验把 120 路并行会话的小定理组装成 `the_nonlinear_inequalities`。[原文：`verifier/certificate.hl:18-36,240-281`；`verifier/m_verifier.hl:1351-1358`；`text_formalization/nonlinear/merge_ineq.hl:18-33`；arXiv:1501.02155 §6]
5. **成本量级**：官方 Azure 运行约 **5,000 processor-hours**（32 核 GNU parallel，墙钟 <1 周）；2014 年复检约 **9,370 processor-hours**（60 个 HT Xeon，6 天）。本仓 `reference/flyspeck/azure/results/` 里 23,237 条逐 case 计时合计 **33,389,493 s = 9,275 CPU-hours**，与复检数字几乎一致；单 case 平均 **1,437 s**、中位 **839 s**、最大 **32,676 s**。[原文：arXiv:1501.02155 §5；本报告 §3.2 实测聚合]
6. **他们的"叶"和我们的"叶"结构上可一一对应**：`Result_pass ↔ MonoTree.leaf`、`Result_mono ↔ MonoTree.restrict`、`Result_glue ↔ MonoTree.split`。差别不在数学层级，而在**证书表示与检查方式**：Flyspeck 的树是 OCaml 数据，由一个递归 checker 生成 HOL 定理并共享子证明；我们的树是 Lean 归纳类型，每个 `leaf`/`restrict`/`df` 都是独立的 `by decide` 定理，每次 `decide` 都要重新展开整个 `E`。[对照：`MonoTree.lean:220-237`；`m_verifier.hl:1240-1362`]
7. **他们不需要每叶 17-24GB 的 `decide`**，因为他们根本没有"整表达式内核 reduction"这一步：HOL Light 是 LCF 风格，每次区间/Taylor 运算只产生一个小的证明对象，叶与叶之间可 GC、可共享、可并行；精度是 pp=4-6（base 200），不是 2048 位 dyadic。我们的 17-24GB 来自 `checkPosTMHull` 在 `decide` 里重新执行 `evalTMHullD2` 整个表达式，叠加 2048 位常数 trans 与 dyadic 指数对齐产生的大整数。[原文+推断，详见 §5]
8. **"121 天"不是数学固有量级，而是"最大叶数 × 最贵单叶成本 × 串行"的乘积**。仓库自己的口径是 251k×360 CPU-s ≈ **1,046 CPU-天串行**；121 天相当于在这个模型上再有 ~8.6 路并行（或平均 ~42 s/叶）。关键事实：**251,054 叶是 TADIAMB（纯多项式、零 sqrt/trans、flat kd 树、零 restrict 节点）**，而 **150 s/17-24GB 是 BIXPCGW sb12-heavy（sqrt/trans、rung 2048）**——两个数字来自不同表达式。用同一条 TADIAMB 的 Lean 20 叶 pilot 实测 50.7 s（≈2.5 s/叶）外推，251k 叶约 **7.3 CPU-天串行**；Flyspeck 对**同一条 TADIAMB** 的公开总耗时是 **75.9 s**。[实测+原文，详见 §6]
9. **最重要的三条建议**（按杠杆）：(a) 先用单调性/面限制 + 最便宜证书路由把叶数压下来，再做二分；(b) 分片 + 多进程 + 薄根组装（Flyspeck 的 120 路/32 核模式，我们的 `run_full.sh` 已有 12 路/20 叶 shard 的成熟实现）；(c) 把每叶的 Taylor 模型烘成证书数据、让内核只做局部 dyadic 检查，而不是 `decide` 整个 `E`。
10. **对"121 天是我们的设计问题"的判断：支持，但需要精确化**。数学本身在 Flyspeck 口径下约 **1 CPU-年**（9,275 CPU-h）；我们最坏口径 251k×360 s ≈ **2.9 CPU-年**，只差约 2.7 倍。121 天/1,046 CPU-天不是"数学要求 251k 个 150 s 的证书"，而是证书表示、叶数策略和内存阻塞并行三者叠加的结果。

---

## 1. Flyspeck 非线性不等式 / Taylor 证书的数量级与粒度

### 1.1 到底有多少条

| 口径 | 数字 | 证据 |
|---|---:|---|
| 论文正文 | "nearly a thousand nonlinear inequalities" | arXiv:1501.02155 §1（PDF p.3） |
| 论文 §5 | "several hundred nonlinear inequalities"，定义域切分后 ">23,000 inequalities" | arXiv:1501.02155 §5（PDF p.10） |
| 仓库 `ineq_ids.hl` | 639 个 id（测试清单） | `reference/flyspeck/text_formalization/nonlinear/formal_tests/ineq_ids.hl`，计数 639 |
| 仓库 `prep.hl` | 812 条预处理不等式 | `reference/flyspeck/text_formalization/nonlinear/prep.hl`，`add_inequality` 计数 812 |
| Azure 最终数据 | 23,242 个 case（`ineqs.txt` 行数 23,237，索引 0..23241） | `reference/flyspeck/azure/ineqs.txt`；`pars.txt` 609 个 50-case 区间 |
| `break_case_log.hl` | 7,479 个 `Iarg_leaf`（该版本的分区树） | `reference/flyspeck/text_formalization/nonlinear/break_case_log.hl` |

**范围说明**：`tame` 分类是 Isabelle/HOL 的图枚举（旧 2×10^7、blueprint 2×10^9 个中间/最终图，数小时；archive 18,762 图），不是 interval/Taylor 证书；`marchal` 是 `TSKAJXY` 家族非线性不等式（`ineq.hl:83-255`），由同一条 formal_ineqs 管线验证，`packing/marchal2.hl`/`marchal3.hl` 是文本归约证明，不是另一套计算证书；`formal_lp` 是独立的 LP 流水线。[原文：arXiv:1501.02155 §7.3、§9；`reference/flyspeck/text_formalization/nonlinear/ineq.hl:83-255`]

**粒度结论**：
- **在不切分的单会话调用里，每条不等式一个 `verify_ineq` 调用/一个 HOL 定理**；其内部 `result_tree` 的节点是搜索树，不是独立定理文件。Azure 为了并行，把每条不等式切成多个 case，每个 case 产生一个定理片段，最后用 MD5 组装（§3.1/§6）。
- Azure 并行时，为了负载均衡和内存，把每条不等式的定义域预切成 ~1 秒 C++ 区间算术粒度的 case；**每个 case 是一个独立进程的验证单位**。`break_case_exec.hl:20-25` 明确写 `MSEC_INC = 1000`，"On each subdomain the verification takes a small number of milliseconds to run in C++"。
- 所以"叶"在 Flyspeck 里更接近我们的**case/子域**，而不是我们 `MonoTree.leaf` 的每一个 `decide` 定理。一个 Flyspeck case 内部可以包含很多 `Result_pass`/`Result_glue` 节点，但这些节点在同一个递归证明里被依次验证、共享、丢弃，不各自成为顶层定理。

### 1.2 证书里到底检查什么

`formal_ineqs` 的目标形如
`∀x ∈ D, f1(x) < 0 ∨ ... ∨ fk(x) < 0`（n ≤ 6），函数可含 sqrt/sin/cos/atan/asin/acos 及 atan(x)/x 的解析延拓。检查流程：

1. **裸区间快路径**：`eval0` 直接在 box 上做区间求值；若某个析取项的区间上界 <0，直接 `Result_pass(raw=true)`；若下界 ≥0，换下一个析取项。[原文：`informal_search.hl:111-126`]
2. **二阶 Taylor 区间**：否则计算该函数在 cell 上的二阶 Taylor 区间 `GTaylor([a,b])`；若上界 <0 → pass；若下界 ≥0 → 换下一个析取项；否则进入剪枝。[原文：`informal_search.hl:128-143`；论文 §5 给出 `g(x) ∈ GTaylor([a,b])` 的推导]
3. **单调性**：对每个宽度 >0 的维度，计算偏导的 Taylor 区间；若上界 <0（对该维严格递减）或下界 ≥0（严格递增），把该维钉到对应的面，递归验证面 box（`Result_mono`）。这相当于把 n 维问题降维。[原文：`informal_search.hl:150-179`]
4. **凸性（可选，非主路径）**：`Result_glue` 可带 `convex_flag`，用二阶偏导的区间下界做凸性 glue；`default_params.convex_flag=false`，主路径 `verify_ineq0` 的 `construct_certificate` 从不产生 convex glue，凸性只在旧的 `Verifier.run_test`/`Result_glue` 路径可用。机制在，但不是默认主路径。[原文：`m_verifier_main.hl:60-72,556-562,818-827`；`m_verifier.hl:1330-1349`]
5. **二分**：都不行时，沿 `find_max ws` 选最宽维，`split_domain` 在中点一分为二，递归两半（`Result_glue`）。`max_depth=200`（生产 `verify_ineq0`）。[原文：`informal_search.hl:181-205`；`m_verifier_main.hl:556-562`]
6. **形式化算术**：所有区间/浮点运算都是 HOL Light 里的形式化自然数/浮点运算，base 默认 200；每个算术结果都是一个 HOL 定理；**不使用本机浮点**。[原文：arXiv:1501.02155 §5；`formal_ineqs/arith_options.hl:9-19`]

**不是 LP**：`formal_lp` 是独立项目，用 GLPK 求对偶解、转成整数系数、在 HOL Light 里做整数线性组合验证；43,078 个 LP，约 15 小时（2.4GHz）。[原文：arXiv:1501.02155 §9；`formal_lp/README.txt:66-67`]

### 1.3 单 cert 成本

`formal_ineqs/docs/FormalVerifier.tex:403-413`（i5 2.67GHz，VirtualBox，OCaml 3.09.3，base 200，cache on）给出的例子：

| 不等式 | precision | total (s) | formal (s) |
|---|---:|---:|---:|
| 4717061266 | 4 | 27.1 | 0.250 |
| TSKAJXY-TADIAMB | 4 | **75.9** | **21.2** |
| 7067938795 | 4 | 431 | 387 |
| 5490182221 | 4 | 1,726 | 1,533 |
| 3318775219 | 4 | **17,091** | **15,226** |

这张表说明：**单条不等式的 formal 成本可以到小时级**（3318775219 ≈ 4.2 小时）。它只是 11 个例子，不能据此推断全部 639/~1000 条的分布；但它足以说明"每条不等式一个证书"与"每条不等式 251k 个叶证书"不是同一个粒度。

---

## 2. 盒分裂 / 剪枝 / 常数与共享

### 2.1 搜索启发式

- **维度选择**：`find_max` 选当前 domain 最宽的坐标（按 `w`），只在 `Cell_inconclusive` 时二分；没有"先验固定网格"。[原文：`informal_search.hl:196-201`]
- **单调性优先于二分**：`try_mono` 只在偏导定号时把维度钉面；如果所有维度都可钉，就直接在面 box 上递归，不需要二分整个体积。这是 TADIAMB 这类多项式不等式能在 75.9 s 内完成的关键机制（[推断]：论文没有逐例说明，但工具默认 `allow_derivatives=true`，且这是唯一能解释同一条不等式 75.9 s vs 我们 251k 叶的机制）。
- **凸性**：`convex_flag` 用 `ddf`（二阶偏导）下界做凸性 glue；机制在，但主路径 `verify_ineq0` 不产生 convex glue（见 §1.2 第 4 条）。[原文：`m_verifier.hl:1330-1349`]
- **自适应精度**：`adaptive_precision=true` 时，先做非形式验证，找每个子树能通过的最小 `pp`，写入 `p_result_tree` 的 `p_status {pp}`；然后形式验证按这个精度跑。[原文：`m_verifier_main.hl:50,573-590`；`certificate.hl:28-36`]
- **硬上限**：`max_depth=200`，`mono_depth=200`；`max_width=1e-10` 虽然写进 options，但当前 `construct` 只检查 `max_depth`，没有用 `max_width` 中止（[原文+代码阅读]）。
- **对称性不靠搜索器**：`formal_ineqs` 的搜索里没有 symmetry 剪枝；对称性以单独的 `... sym` 不等式形式进入数据库（如 `TSKAJXY-RIBCYXU sym`、`TSKAJXY-IYOUOBF sym`），由同一条管线验证。[原文：`reference/flyspeck/text_formalization/nonlinear/ineq.hl:183-199,223-237`]

### 2.2 常数与共享子表达式

1. **预处理**：`prep.hl` 是自动生成的 812 条预处理不等式；`merge_ineq.hl` 把 `ineqdata3q1h.hl` 的 5×46=230 条合并成一条 13 变量的 `ox3q1h_merge`，并合并 packing 章节的数百条不等式。合并后的形态供正文使用，证明时再拆开/组合。[原文：`merge_ineq.hl:18-33`]
2. **证书内共享**：`result_tree` 的 `Result_pass_ref` 允许一个已经证明的子树在多个 domain 复用；`transform_result` 用 domain hash + 子域包含检查，把 `Result_pass_mono` 重写成 `Result_mono [m] (Result_pass_ref (-i))`，即"面 box 的证明直接引用大 box 的证明"。[原文：`certificate.hl:18-36,240-281`；`m_verifier.hl:1351-1358`]
3. **逐函数闭包共享**：`mk_verification_functions` 为每条不等式的每个函数构造 `eval0`/`taylor`/`diff2`/`df`/`ddf` 闭包；搜索和形式验证共用同一套闭包。[原文：`m_verifier_main.hl:329-363`]
4. **算术缓存**：`Arith_options.cached=true`，自然数/浮点运算各有缓存，初始 10,000、上限 20,000；`float_cached=true`。[原文：`arith_options.hl:9-19`]
5. **预切分复用**：C++ `break_case` 程序先把每条不等式切成 ~1 秒的 case，结果序列化进 `break_case_log.hl`/`ineqs.txt`；正式验证直接消费这些 case，不重复搜索切分。[原文：`break_case_exec.hl:10-25,75-115`；`azure/README.md:42-50`]
6. **跨会话组装**：每个 case 在独立进程里证明，导出规范形式 theorem + 常量/类型/公理历史，算 MD5；主会话只导入 MD5 匹配的定理，不再重证。这就是"一次认证、多处复用"的最终形态。[原文：arXiv:1501.02155 §6]

**注意**：Flyspeck 的"共享"主要是**证明对象/子域**层面的，不是"把常数 Taylor 系数预烘成一个 JSON 表，让内核查表"。它的 leaf 形式验证仍会从函数项重新计算 Taylor 区间（`fs.taylor pp pp domain_th`），但因为 pp 低、算术有缓存、证明对象小，所以可接受。[原文：`m_verifier.hl:1315-1328`]

---

## 3. 实测成本与并行度

### 3.1 公开数字

| 项 | 数字 | 证据 |
|---|---:|---|
| 非线性不等式 Azure 验证 | ~5,000 processor-hours | arXiv:1501.02155 §5（PDF p.10）；Flyspeck wiki Installation Guide："This takes about 5000 CPU hours." |
| 并行方式 | 32 核，GNU parallel；墙钟 <1 周 | arXiv:1501.02155 §5 |
| 2014 复检 | ~9,370 processor-hours，60 个 HT Xeon 2.3GHz，6 天 | arXiv:1501.02155 §5 |
| 并行作业数 | README 示例 `./run-parallel 120`，120 个独立 `verifier` 进程 | `reference/flyspeck/azure/README.md:42-50` |
| 线性规划 | 43,078 个 LP，约 15 小时（2.4GHz） | arXiv:1501.02155 §9；`formal_lp/README.txt:66-67` |
| 主定理 | 直接验证约 5 小时（2GHz）；录制证明回放约 40 分钟 | arXiv:1501.02155 §1 |
| Tame 分类 | 旧 2×10^7、blueprint 2×10^9 个中间/最终图，枚举数小时；archive 18,762 图 | arXiv:1501.02155 §7.3 |

### 3.2 本仓 Azure 日志的逐 case 聚合（实测）

数据：`reference/flyspeck/azure/results/**/stdout` 中的 `Time <case>,...: <seconds>` 行；按 case 索引去重。

| 统计 | 值 |
|---|---:|
| 有计时的 case | 23,237（总 case 23,242，5 个缺失） |
| 总时间 | 33,389,493 s = 9,274.9 CPU-hours = 1.058 CPU-years |
| 平均 | 1,436.9 s/case |
| 中位 | 839 s/case |
| p90 | 3,191.6 s/case |
| 最大 | 32,676.4 s（≈9.1 h） |
| 最小 | ~0.007 s（异常值，可能是无需搜索的 case） |

这与论文的复检 9,370 CPU-h 几乎重合；与 Azure 的 5,000 CPU-h 有约 1.85 倍差（[推断]：5,000 可能是较早/较优的一遍，或未含重试；本仓日志包含重试/较慢的 case）。无论取哪个，**量级都是 10^3 CPU-hours 到 10^4 CPU-hours，不是 10^5-10^6**。

### 3.3 HOL Light checker：解释还是编译？

- 默认 HOL Light 是 OCaml 字节码（`hol.sh` 加载 `.ml`），**解释执行**；`INSTALL.md:209-211` 说用 `ocamlopt` 编译后"files loaded approximately 5 times faster"。
- Azure/复检使用**原生编译的 HOL Light + formal_ineqs**：`azure/Makefile` 用 `ocamlopt` 编译 `HOL_CORE_OBJ`/`INEQ_OBJ`/`FLYSPECK_OBJ` 并链接成 `verifier`；论文明确 "Nonlinear inequalities were verified with compiled versions of HOL Light"。[原文：`azure/Makefile` 的 `build` 目标；arXiv:1501.02155 §5]
- 但这不是"把 `decide` 编译成机器码"：HOL Light 的 kernel 仍是 OCaml 的 LCF kernel，每个 interval/Taylor 操作产生小的 HOL 定理；`ocamlopt` 只是让这些证明生成函数跑得更快。[原文+推断]

---

## 4. 他们的"叶"与我们的 mono-tree 叶的对应关系

| Flyspeck `result_tree` | 我们的 `MonoTree` | 说明 |
|---|---|---|
| `Result_pass (f.index, raw_flag)` | `MonoTree.leaf box ps (checkPosTMHull ...)` | 一个 cell 上某个析取项被 Taylor/裸区间证明；我们的 leaf 是 `checkPosTMHull` 定理 |
| `Result_pass_mono m` | `MonoTree.restrict` 的面子树 leaf | 单调性把维度钉面后在面 box 上的 pass |
| `Result_mono (mono, r1)` | `MonoTree.restrict box sgn psd hincr hdecr ... sub` | 两者都是"偏导定号 → 递归面 box"；我们每个 df 方向是独立 `checkPosTMHull` 定理，Flyspeck 在 `verify_mono` 里调用 `fs.df`/`eval_m_taylor_partial_*` |
| `Result_glue (j, convex, r1, r2)` | `MonoTree.split box d l r` | 都沿一维二分；`convex_flag` 是凸性 glue，我们现在没有对应凸性节点 |
| `Result_pass_ref i` | 无直接对应（`fold` 复用 `Der`/`Face` 定理是局部复用） | Flyspeck 的共享是跨 domain 的；我们目前没有跨叶的 proof ref |
| `p_status {pp}` | `TMParams`（sqrt/inv/trans 粒度、rung） | 都是逐子树/逐叶精度参数；我们的参数是 per-leaf 字面量，没有 per-node 自适应 |

**关键结构差异**：
- Flyspeck 的树是**数据**，由一个递归 checker `m_verify_raw` 解释；`Result_pass` 只是标记，checker 现场算 Taylor 并生成定理。整棵树在一个 HOL Light 会话里验证，`th_list` 保存已证子树供 `Result_pass_ref` 复用。[原文：`m_verifier.hl:1240-1362`]
- 我们的树是**证明项**：`MonoTree.leaf` 构造器带一个 `checkPosTMHull ... = true` 的证明字段；`restrict` 带 `hincr`/`hdecr`（每个方向一个 `decide` 定理）和 `sub`；`split` 带两个子树。每个字段都是独立定理，Lean 内核逐个检查。[原文：`MonoTree.lean:220-237`]
- 所以**同样的数学树**，我们的内核工作量是"每个 leaf/df 一次整表达式 reduction"，Flyspeck 是"一次递归 + 小证明对象"。这是 17-24GB vs 几 GB 的根本原因。

**关于 251k 的准确说法**：仓库里的 251,054 叶是 **TADIAMB 的 C 侧 kd 二分树**，`mono_witness_rung.md:69-71` 明确说 "kd split trees have zero restrict nodes"——也就是说这棵树**没有** `MonoTree.restrict` 节点，是纯 `split`/`leaf` 的扁平树。它不是"mono-tree 已经用了单调性还 251k 叶"；恰恰相反，它是"没有用单调性/面限制"的对照物。[原文：`pipeline/interval/mono_witness_rung.md:69-71`；`docs/projects/phase4-algo-lane-log.md:8`]

---

## 5. 为什么他们不需要每叶 17-24GB 的 `decide`

先拆我们的 17-24GB 来自哪里（按代码路径）：

1. `checkPosTMHull e box ps` 的定义是
   `(all wf) && match evalTMHullD2 box e ps with some (M,_) => (M.loBound box).isPos | none => false`。
   [原文：`CertTM.lean:4079-4084`]
2. `decide` 要对这个 Bool 做内核 reduction；`evalTMHullD2` 会**递归遍历整个 `e`**，对每个节点做 `M.add/sub/mul/div/sqrt/trans`，其中：
   - `Dyadic.add` 用 `2 ^ (a.e - min a.e b.e).toNat` 对齐指数；`Dyadic.mul` 把 mantissa 相乘、指数相加。rung 2048 的常数 trans 与 box 端点指数差很大时，mantissa 会变成几千位的大整数。[原文：`Basic.lean:105-109`]
   - `.trans` 非 closed 分支调用 `transOn`，每次从 `(N,out)` 重新算 Taylor 区间；常数 trans 节点与 box 无关，但每个 leaf 都重算。[原文：`CertTM.lean:3700-3709`]
   - `.div`/`.sqrt` 也按 per-leaf 证书队列消费，但队列里的粒度是固定的；没有跨 leaf 缓存。
3. Lean 的 `decide` 不会跨定理缓存 reduction 结果；每个 `MonoTree.leaf` 的 `theorem ... := by decide` 都重新展开 `E`（一个 `def`）并重新算一遍。于是每个 leaf 的峰值内存与表达式大小、rung 精度、dyadic 大整数成正比；在 BIX sb12-heavy 上实测 17.2-24.2GB。[实测：`docs/e2e-debt-map.md:486-488`；`mono_witness_rung.md:97-101`]
4. 251k 个 leaf 若放在同一个文件里，还会叠加已证定理/环境的内存；但 17-24GB 的单叶峰值已经足以让 36GB 机器只能串行。[推断，与 `mono_witness_rung.md:100-101` 的 "decide peak 17.2-24.2GB (×1 per 36GB)" 一致]

Flyspeck 避开了 1-4 的全部：
- **没有整表达式 `decide`**：`m_verify_raw` 是 OCaml 递归函数，叶子上调用 `fs.taylor pp pp domain_th` 生成 Taylor 区间定理，再 `m_taylor_cell_pass` 组合成 `f<0` 的定理；每个证明对象只包含当前 cell 的区间/Taylor 数据。[原文：`m_verifier.hl:1315-1328`]
- **精度低**：pp=4-6（base 200，≈9-14 位十进制），不是 2048 位；区间端点不会膨胀成几千位整数。[原文：`examples_flyspeck.hl` 的 `verify_flyspeck_ineq 4`；Azure `main_verifier.hl:verify_flyspeck_ineq 6`]
- **共享/复用**：`Result_pass_ref` 直接复用已证子树；`m_cell_pass_subdomain` 把大域证明降到子域；搜索树里的 monotonicity 减少了需要验证的体积。[原文：`m_verifier.hl:1351-1358`；`certificate.hl:240-281`]
- **进程级并行**：每个 case 一个独立 `verifier` 进程，120 个并行作业；每个进程只装载 HOL Light + 当前 case，`Gc.compact()` 在每个 case 后调用。内存是 per-process 的，不共享一个大 proof term。[原文：`azure/README.md:42-50`；`azure/main_verifier.hl` 的 `Gc.compact()`]
- **编译**：Azure 用 `ocamlopt` 原生编译，证明生成函数更快；这不是信任模型的改变，因为 HOL Light kernel 仍是 OCaml 的那一小段。[原文：`azure/Makefile`；`INSTALL.md:209-211`]

**内存数字的诚实边界**：Flyspeck 仓库没有公开每个 `verifier` 进程的 RSS；[未找到]。但可以间接推断它不是 17-24GB 级：README 让 120 个进程并行（[原文]），LP 验证能在 "Mac mini 2GHz, 2GB" 上跑 15 小时（[原文：`formal_lp/README.txt:66-67`]），说明 HOL Light + checker 的内存远小于 17GB。具体数字不要引用为事实。

---

## 6. "121 天"判断：哪些是数学，哪些是设计

### 6.1 先把数字拆开

- 仓库成本模型：每叶 ≈210 s 烘 + ≈150 s decide ≈ **360 CPU-s**；251k 叶 ≈ **1,046 CPU-天串行**；decide 峰值 17.2-24.2GB。[实测：`docs/e2e-debt-map.md:486-488`；`mono_witness_rung.md:97-101`]
- 121 天 = 10.45M s；除以 251k ≈ **41.6 s/叶**；或 1,046 CPU-天 / 8.64 ≈ 121 天。换句话说，121 天对应"1,046 CPU-天 + ~8.6 路并行"或"平均 42 s/叶"，不是 251k×150 s 的直接串行（那会是 436 天）。
- 251k 是 **TADIAMB**（`TSKAJXY-TADIAMB`），C 侧 141MB 证书、101.2 s 全闭；[实测：`docs/projects/phase4-algo-lane-log.md:8`] 该记录被 `docs/assets/p4profile/records_classified.json` 分类为 `class: poly`、`apps: ["rad2_x"]`、`route: R1`——`rad2_x = rho_x/(4*delta_x)` 是多项式（`y_of_x rad2_x` 把 y_i 平方代回），**零 sqrt/trans 节点**。[原文：`reference/flyspeck/text_formalization/general/sphere.hl:271,538`；`records_classified.json` 的 TADIAMB 记录]
- 150 s/17-24GB 是 **BIXPCGW sb12-heavy** 的测量：`mono_witness_rung.md` 的标题就是 `BIXPCGW_7274157868_a sb12-heavy`，rung 2048，53 个 trans 节点。注意 gen-9 的 BIX kd 队列本身只有 4/8 叶（深度 2/3），所以"251k × 150 s"是把 BIX 的单叶成本外推到 251k 规模，不是一棵实测的 251k 叶 BIX 树。[原文：`mono_witness_rung.md:1,15-21,58,78-101`；`~/c17_backup/lane_snapshots/w8rung/gen9/REPORT.md` §③]
- 同一个 TADIAMB 的 Lean 20 叶 pilot：**50.7 s**（≈2.5 s/叶）；C4717061266 127 叶 110 s（≈0.87 s/叶）。[实测：`docs/projects/phase4-algo-lane-log.md:24-26`]
- 所以"251k × 150 s"是把 **BIX 的重叶子成本**乘到 **TADIAMB 的多叶子树**上；这是本报告发现的最重要的口径错误。若按 TADIAMB 自己的 2.5 s/叶，251k ≈ 627,635 s = **7.3 CPU-天串行**；若按 C549 生产 interval 路线的 51.5 s/叶，251k ≈ 149.6 CPU-天串行。[实测+推断]

### 6.2 与 Flyspeck 的同题对比

同一条 `TSKAJXY-TADIAMB`：
- Flyspeck `examples_flyspeck.hl` 的公开测试：precision 4，total **75.9 s**，formal **21.2 s**（i5 2.67GHz/2009，解释 OCaml；脚注"reduced to a polynomial inequality"）。[原文：`formal_ineqs/docs/FormalVerifier.tex:410,417`]
- 我们：C 侧 251,054 叶、141MB、101.2 s 搜索；Lean 侧 20 叶 50.7 s；若按 2.5 s/叶全量发射，约 7.3 天串行 vs Flyspeck 75.9 s，约 **8,300 倍**。[实测+原文]
- 这不是说 Flyspeck 的 75.9 s 包含了我们所有的 Lean 证明义务（它是在 HOL Light 里生成定理，不需要发射 251k 个定理文件），也不是同硬件/同证明器的绝对秒数对比；但它至少证明：**同一条数学不等式不需要 251k 个叶证书**。Flyspeck 的搜索用单调性/面限制和较粗的 Taylor 分割（[推断]：论文未逐例说明）；我们的 251k 是**零 restrict 节点的 flat kd 树**。[原文：`mono_witness_rung.md:69-71`]

### 6.3 全项目量级

- Flyspeck：约 1000 条不等式 → 23,242 case → 9,275 CPU-h（本仓日志）/ 5,000 CPU-h（官方 Azure）/ 9,370 CPU-h（复检）。
- 我们：如果按仓库最坏口径 251k×360 s = 90.38M s = **2.87 CPU-年**；按 C549 interval 路线 251k×51.5 s = **0.41 CPU-年**；按 TADIAMB poly pilot 251k×2.5 s = **0.020 CPU-年**。
- 即便取最坏口径，我们也只是 Flyspeck 复检的 **~2.7 倍 CPU**，不是 100 倍。**121 天/1,046 CPU-天的墙钟差主要来自串行和内存，不是来自数学本身。**

### 6.4 裁决

**支持"121 天是我们的设计问题"**，但要把"设计问题"具体化为四条，而不是笼统地说"叶太多"：

1. **叶数策略**：251k 是 flat kd 二分树（零 restrict）；同一条 TADIAMB 在 Flyspeck 是 75.9 s。单调性/面限制和"最便宜证书路由"可以把叶数压低一到两个数量级。
2. **证书表示**：每叶一个 `checkPosTMHull ... := by decide`，每次 `decide` 重算整个 `E` 和 2048 位常数 trans；没有跨叶缓存/共享。Flyspeck 的树是一个递归 checker + `Result_pass_ref`。
3. **内存阻塞并行**：单叶 17-24GB → 36GB 机器只能 1 路；而 C549 interval 路线 20 叶 shard 只有 11-12GB，36GB 可跑 2-3 路；Flyspeck 用 120 个进程/32 核。内存不降，谈并行没有意义。
4. **精度策略**：全局 2048 位 rung，而 Flyspeck 是 pp=4-6 自适应；gen-9 已经实测 BIX 重叶在 keepconst-128 下 PASS、64 下 NEG，说明 **45 个非恒定 trans** 可以降到 128（8 个常数 trans 仍必须 2048），全 2048 是过度精度。[原文：`mono_witness_rung.md:78-87`；`gen9/REPORT.md` 结论 1]

---

## 7. 建议（按杠杆排序，含落点）

### R1（最高杠杆）：先剪枝/路由，再二分；把 251k 的 flat kd 树换成 restrict×bisect 树

**做法**：
- 在发射前用 stage-A 的偏导探测生成 `MonoTree.restrict` 节点：对每个维度，若 ∂ⱼ 在 node box 上定号，钉到对应面，只在面 box 上递归；只有不能钉的维度才二分。这正是 Flyspeck `try_mono`/`Result_mono` 的做法。[原文：`informal_search.hl:150-179`；`MonoTree.lean:226-234`]
- 叶证书按最便宜路线路由：先用 `checkPosI` 裸区间（C549 生产路线 51.5 s/叶、11GB/20 叶），只有临界带才用 `checkPosTMHull`；这对应 Flyspeck 的 `raw_intervals0` 快路径 + Taylor fallback。[原文：`emit_mono.py:1100-1113,1154-1172`；`informal_search.hl:111-143`]
- 实施 "stop at first screen-pass"：POS1 的根自身即可证，深 kd 是浪费；case 的 guard-straddle 根需要 guard 引导切分（W3 的 `gsplit2`），不要把整个域均匀二分到 251k。[原文：`mono_witness_rung.md:91-96`]

**落点**：
- `pipeline/interval/emit_lean.py` 的 `--mono-tree` 树构造：当前 kd 路径只发 `split`/`leaf`；加入 `restrict` 节点（stage-A 的 `df_*` 探测结果已在 `mono_witness_rung`/`emit_mono.py` 里有现成数据格式）。
- `pipeline/interval/emit_mono.py:1100-1113` 的 `CERT_ROUTE_I` 已经是 interval 路线；把 `cert_route` 选择做成 per-leaf（而不是整模块）。
- `lean/Kepler/Interval/MonoTree.lean:220-237` 的 `restrict`/`split` 构造器已经是现成的；不需要新 soundness 证明。

**预期**：TADIAMB 从 251k 叶降到可能 10^3-10^4 量级（以 Flyspeck 75.9 s 为对照）；即使只降 10 倍，1,046 CPU-天 → ~105 CPU-天。

### R2（最快见效）：分片 + 多进程 + 薄根组装（Flyspeck 的 120 路模式）

**做法**：
- 把 mono-tree stage B 从"一个文件包含所有 leaf"改成"每 N 叶一个 shard 模块，导出 `def ShardKTree : MonoTree n E` + `theorem ShardKCovers`；根模块 import 所有 shard，拼 `MonoTree.split/restrict` 骨架并证 `covers`"。Lean 的定理常量跨模块复用，不会重证。[推断，基于 Lean 模块语义；Flyspeck 的 §6 是同一思想]
- 用 `xargs -P`/`lake build` 并行构建 shard；每进程设 RSS 上限。36GB 机器按 11-12GB/shard 可跑 2-3 路；503GB 机器按现有 C549 口径 12 路。[实测：`LAUNCH_FULL.md:71-73,101-110`；`run_full.sh:539-543`]
- 在单机上用 DMTCP/olean 检查点减少重复装载（Flyspeck 的 INSTALL 也推荐 DMTCP）。[原文：`INSTALL.md:181-207`]

**落点**：
- `emit_lean.py:4067-4112` 已有 `cut_shards` 和 `Shard{i}.lean` 的写法（目前用于 BBTreeG/GD 和部分 mono）；把 mono stage B 的 `emit_node`（`:3350-3435`）接上同样的 shard 机制。
- `run_full.sh:539-543` 的 `xargs -P "$JOBS"` 和 `build_one` 已有 RSS 记录；直接复用。
- `LAUNCH_FULL.md:48-49,71-73` 是现成的运维口径。

**预期**：121 天 / 2-3 路（36GB）≈ 40-60 天；/12 路（大机器）≈ 10 天；再叠加 R1 的叶数下降，进入个位数天。

### R3（最深的结构修复）：每叶烘 Taylor 模型 + 局部 checker，去掉整表达式 `decide`

**做法**：
- 仿照 Flyspeck "informal search → formal checker"：stage A 已经用 `evalTMHullFill2` 在编译态算出每叶的 `TaylorM`（y, w, fB, dfB, err）和所有 sqrt/inv/trans 数据；stage B 不再让内核从 `E` 重算，而是把这些数据作为 `LeafTMCert` 字面量发射。
- 新增 `checkLeafTMCert : LeafTMCert → box → Bool`：
  - 局部检查 `M.Valid box e`（组合式：逐节点检查 const/var/add/mul/sqrt/trans 的区间包含；等价于 `evalTMHullD2_sound` 的逆过程，但数据已给，检查是 O(节点) 的局部 dyadic 比较）；
  - 检查 `M.loBound box` 为正。
  - 由 `Valid` + `loBound_sound` 直接得到 `checkPosTMHull_sound` 同款结论。
- 这样内核不再展开 `E` 的 2048 位常数 trans，也不再做大整数指数对齐；每叶只做几百个 dyadic 比较。[推断；数学依据是 `TaylorM.Valid` 语义和 `loBound_sound` 已在 `CertTM.lean`]
- 如果完整 `Valid` 检查工程量大，先做 R4+R5（常数 trans 烘进 TMParams + 自适应 rung），它们能把 `evalTMHullD2` 的常数部分去掉/降精度；R3 是终局。

**落点**：
- `lean/Kepler/Interval/CertTM.lean:4079-4104`（`checkPosTMHull`/`checkPosTMHull_sound`）；新增 `LeafTMCert` + `checkLeafTMCert`，复用 `TaylorM.Valid`/`loBound_sound`。
- `pipeline/interval/emit_lean.py:1183-1200`（stage A/B hull 注释和 `tmHullLeafProbe`）；stage A 的 `evalTMHullFill2` 已经输出每叶模型/参数（`hull_stage_a_file`），stage B 的 `emit_node` leaf（`:3375`）改成发 `LeafTMCert` 字面量。

**预期**：单叶 150 s/17-24GB → 秒级/<1GB（[推断]，基于局部 dyadic 检查的规模）；251k 叶可变成 10^5-10^6 秒级，且可并行。

### R4：常数 trans 盒烘进 `TMParams` + `LExpr` 共享子表达式

**做法**：
- `TransTMP` 目前只有 `o1/o2`，值 enclosure 每次 `transOn` 重算；把 `(N,out)` 对应的 `vLo/vHi`（以及可选的 slope/curv 界）在 stage A 算一次，写进 `TMParams.transCerts`；`TaylorM.trans` 直接消费。所有 leaf 共享同一批常数 trans 节点。
- 用 `LExpr`/`checkPosTMHullL`（已有，`CertTM.lean:4463,4923`）把重复子表达式（例如 rad2_x/delta_x/rho_x 的公共子项）表化，避免每叶重复展开；routing 文档自己的估计是 LExpr 去重 3-5×。[原文：`docs/projects/phase4-routing-decision.md` Tier 2 杠杆]

**落点**：
- `CertTM.lean:65-82`（`TransTMP`/`TMParams`）、`CertTM.lean:3700-3709`（`.trans` 分支）；`emit_lean.py` 的 `ps_lit`/`RUNG`（`:1324-1330` 附近）和 stage A 的 RUNG 输出。
- `CertTM.lean:4463-4934`（`LExpr`/`checkPosTMHullL`）；`emit_lean.py` mono stage B leaf 发射改成 `LExpr` 表 + `checkPosTMHullL`。

**预期**：仓库自己的 gen-10 估计 40-80 CPU-s/叶，251k ≈ 116-232 CPU-天；LExpr 再 3-5×。

### R5：每叶自适应 rung/精度，而不是全局 2048

**做法**：
- Flyspeck 的 `adaptive_precision`/`p_status {pp}`：每个子树用能通过的最小精度。我们的 stage A 阶梯已经能逐叶找最小 rung（`gen7/*.minrung.json` 的 99 行曲线；rung 8 已覆盖 97/99 行，只有两个 div 行需要 64）。[原文：`mono_witness_rung.md:23-50`]
- 对 leaf final value，gen-9 实测 keepconst-64 NEG、keepconst-128 PASS、128≈256；所以 45 个非恒定 trans 的 128 是可用档，8 个常数 trans 仍需 2048（gen-9 结论 1）。[原文：`mono_witness_rung.md:78-87`；`gen9/REPORT.md` 结论 1]
- 发射时每叶/每节点写自己的 `(N,out)`：45/53 个非恒定 trans 从 2048 降到 128，8 个常数 trans 保持 2048；失败再升档。这样大多数节点的 dyadic 位数从 2048 降到 128（16×），大整数/内存显著下降。[推断]

**落点**：
- `pipeline/interval/emit_lean.py` 的 RUNG 策略（`W8_WITNESS_RUNG_SB12HEAVY` 在 `:3555`，`_parse_rung_arg`/RUNG 选择在其后）；`mono_witness_rung.md` 的 policy。
- `TMParams`/`TransTMP` 逐叶字面量（已经是 per-leaf，只需让 stage A 选择最小 rung）；`emit_hull_pilot.py` 的 min-rung 阶梯（`params_lit`/RUNG 解析）。

**预期**：2048→128 的 16× 位宽下降；与 R3/R4 叠加可将单叶内存从 17-24GB 降到 GB 级（[推断]，需要实测）。

### 不建议

- **不要用 `native_decide` 作为最终证书**：它引入 `Lean.ofReduceBool` 公理，违背当前"标准三公理"的信任模型；仓库也明确 `--decide-mode=native` 是 DEV MODE。[原文：`emit_lean.py:3084-3088`]
- **不要试图用 LP 替代非线性区间/Taylor**：Flyspeck 的 LP 是另一条流水线（43,078 个 LP），不是非线性不等式的证书；我们的 LP 已经有自己的 Farkas 路线。[原文：arXiv:1501.02155 §9；`pipeline/lp/README.md`]
- **不要把 `max_width=1e-10` 当成实际终止条件**：当前 `construct` 只用 `max_depth`，没有用 `max_width`。[原文：`informal_search.hl:181-205`]

---

## 8. 找不到 / 不确定的点

1. **Flyspeck 每个 `verifier` 进程的 RSS**：仓库和论文都没有公开。[未找到] 不要引用具体 GB 数；本报告只用"120 进程并行 + LP 在 2GB Mac mini 上跑"做间接推断。
2. **TADIAMB 在 `verify_ineq` 内部的实际 `pass`/`mono`/`glue` 计数**：`certificate_stats` 会打印，但仓库没有保存该例的输出。[未找到] 因此"75.9 s vs 251k 叶"只能说明总成本差异，不能精确说"它用了多少叶"。
3. **Flyspeck 23,242 case 与 `break_case_log.hl` 7,479 leaf 的版本关系**：两者不是同一数据版本；[推断] Azure 的 `ineqs.txt` 是更细/更晚的切分，`break_case_log` 是较早的 prep 分区。不要混用。
4. **Flyspeck 的 "5,000 CPU-h" 与本仓日志 9,275 CPU-h 的差异**：论文说 5,000（Azure），复检 9,370；本仓日志合计 9,275。差异可能来自重试、版本、机器/编译；[未找到] 逐项对账。
5. **我们的 17-24GB 是否全部来自 dyadic 大整数**：没有逐项 profiling；[推断] 主因是 `decide` 整表达式 reduction + 2048 位常数 trans + 指数对齐，但不排除 Lean 环境/证明项本身的内存。
6. **Flyspeck 的 convexity 实际使用率**：`default_params.convex_flag=false`，主路径 `verify_ineq0` 不产生 convex glue；[未找到] 生产运行中是否对某些不等式打开过 convex。不要把 convexity 当成默认主路径。

---

## 附录 A：一页对照表

| 维度 | Flyspeck `formal_ineqs` | 我们的 `CertTM`/`MonoTree` |
|---|---|---|
| 证书单位 | 每不等式一个 `result_tree`；23,242 个预处理 case | 每叶一个 `checkPosTMHull ... = true := by decide` 定理 |
| 叶数 | 23,242 case（639 id / 812 prep）；`break_case_log` 版本 7,479 leaf | 251,054（TADIAMB flat kd；零 restrict） |
| 单叶检查 | 形式化区间 + 二阶 Taylor，pp=4-6，HOL Light 证明生成 | 内核 `decide`，`evalTMHullD2`，rung 2048，dyadic |
| 单叶成本 | 平均 1,437 s/case，中位 839 s，最大 32,676 s | BIX 重叶 ~150 s decide + 210 s 烘；TADIAMB pilot ~2.5 s/叶；C549 interval 51.5 s/叶 |
| 单叶内存 | 未公开；120 进程并行，LP 可在 2GB 机器跑 | 17.2-24.2GB（BIX hull）；11-12GB/20 叶 shard（C549 interval） |
| 分裂 | raw interval → Taylor → monotonicity → convexity(可选) → 最宽维二分；depth 200 | kd 最宽维二分；mono-tree 有 restrict 但 251k 树零 restrict |
| 共享 | `Result_pass_ref`、`m_cell_pass_subdomain`、预处理/合并、MD5 跨会话 | `MonoTree` fold 复用 Der/Face；`LExpr` 存在但 mono stage B 未用 |
| 常数 | 预处理/序列化/算术 cache；pp adaptive | `TMParams` per-leaf；常数 trans@2048 每叶重算；无跨叶 cache |
| 并行 | 120 jobs / 32 cores；Azure 5,000 CPU-h；recheck 9,370 CPU-h / 60 HT / 6 days | `run_full.sh` 12 路 / 20 叶 shard（interval）；hull 重叶 1 路/36GB |
| 总 CPU | ~1.06 CPU-year（本仓日志）/ ~0.57 CPU-year（官方 Azure） | 最坏 2.87 CPU-year（251k×360 s）；interval 0.41 CPU-year；poly pilot 0.02 CPU-year |


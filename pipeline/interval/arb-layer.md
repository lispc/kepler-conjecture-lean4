# Phase 4 (c) — Arb 分支定界层设计（框架 v1）

2026-09-08 定稿。dReal 已榨干：176 条中 41 unsat / 6 δ-sat / 129 超时（1800s/条）。
本层任务：兜底 135 条硬案例（129 超时 + 6 δ-sat 尖锐边界组），并给出
Lean 内核可重放的证书，最终闭合 G4。

## 已探明的输入事实（设计前提）

- 展开后算子集（全部 176 个 SMT 文件统计）：`+ - * / sqrt atan abs` +
  少量 `sin/cos`（1 个文件）+ **`ite` 分支**（定义展开引入，如 atan 参数
  符号保护、abs）+ `pi`（以 `4*atan 1` 出现）。
- 盒域端点是十进制（`2.0`、`2.52`）或 `sqrt8` —— 十进制非 dyadic
  （2.52=63/25），`sqrt8` 无理。dyadic 根盒必须外扩，实数侧用
  `norm_num` 级别的小引理把原域嵌入根盒。
- Lean 侧证书层已就绪（`lean/Kepler/Interval/`）：`IExpr` AST +
  `checkPos`（内核 `decide`）+ `BBTree`/`covers`/`bb_sound`。
  **本层只生产证书，不新增 soundness 定理**（除下列两处扩展）。
- IExpr 现有节点：const/var/neg/add/sub/mul/div(out)/sqrt(s₁,s₂)/trans
  (sin,cos,arctan; N,out)。**缺 abs，缺 ite 分支的证书形式**。

## 流水线四段

### 1. `emit_rpn.py`（Python，复用 parse_defs/emit_smt 展开闭包）

每案例输出一个机器可读 case 文件（JSON）：
- `vars`：变量表（顺序固定，对应 Lean 的 `Fin n`）；
- `box`：dyadic 外扩根盒（精度参数 `q`，默认 2⁻³⁰）；
- `prog`：RPN 指令流。ops：`push_var i`、`push_const <num/den>`
  （精确有理数；`sqrt8`、`pi` 等命名常量在展开期替换为
  `sqrt(const 8)`、`4*atan(1)` 子程序）、`add/sub/mul/neg/div/sqrt/atan/
  sin/cos/abs`、`guard_lt j k`（ite 的条件，见下）。
- ite 处理：不求值分支选择，发 `guard` 指令记录条件表达式区间符号；
  符号未定（跨 0）→ 返回 STRADDLE，驱动层继续二分。

### 2. `bb_arb.c`（C/FLINT 驱动，模板 `test_arb.c`，编译见 README）

- Arb 栈式求值器：按 RPN 逐指令球算术；`guard` 符号未定即 STRADDLE。
- 二分器：最大宽度维优先、精确 dyadic 中点（对应 `splitOK`）；
  精度阶梯 53→128→256 bit（叶内求值失败/不够紧时升精度重试）；
  叶闭合条件：目标表达式区间 `lo > 0`（严格不等式）且全部 guard
  符号已定。
- 节点上限（默认 2²⁰）+ 失败案例列表输出；爆炸案例走降级预案
  （查 Flyspeck nonlinear 证明脚本的剖分参数，作 per-case 提示输入）。
- 输出证书 JSON：树结构 + 每叶的盒 + 每叶的 cert 参数
  （div 的 `out`、sqrt 的 `s₁ s₂`、atan 的 `N out`、guard 符号）。

### 3. Lean 侧两处扩展（先于证书生成完成）

1. `IExpr.abs` 节点 + `DInterval.abs` + soundness（小）。
2. `Cert.lean` 叶证书格式扩展：叶 = 盒 + guard 符号证书序列
   （每条是某 guard 表达式在叶盒上 `checkPos`/`checkNeg` 成功）
   + 末表达式 `checkPos`。`bb_sound` 相应推广
   （covers_point 仍按 midpoint 二分，guard 只是把"取哪支"变成
   内核可检查的决定树路径）。

### 4. `emit_lean.py` + G4 粘合（最深的一段，单独立项）

- 证书 JSON → Lean 分片（抄 Phase 3 build_shards/socert 模式），
  每案例一条 `theorem case_<id> : ∀ ρ ∈ box, 0 < evalReal e ρ := bb_sound …`。
- G4 粘合：Lean 里要有 155 个定义闭包符号（delta_y、gamma4fgcy…）
  的 Lean 定义，以及每案例 `evalReal e ρ = <展开式> ρ` 的对应引理
  （生成器按 Lean 定义的结构镜像构造 IExpr 时，目标是 `by rfl/simp`）。
  这一段工作量大，是 G4 的主体剩余。

## 分工与顺序

1. 我先写 `emit_rpn.py` 的 case 文件格式 stub + `bb_arb.c` 骨架（本文件即规格）；
2. flash 工人填 `emit_rpn.py` 实现（有 emit_smt.py 模板，纯 AST 遍历）；
3. flash 工人填 `bb_arb.c`（有 test_arb.c + README 编译命令）；
4. Lean 扩展（IExpr.abs、Cert guard 叶）—— 满血工人或我亲手；
5. 冒烟：先打通 1 条已 unsat 案例全链（生成→求解→证书→内核），
   再放量 135 条（与 PLAN.md 风险 4 的"先 10 个打通再规模化"一致）。

## 风险

- **ite 爆炸**：guard 边界附近二分收敛慢 → 节点上限 + Flyspeck 剖分提示；
- **状态保真**：`evalReal e` 与原不等式的对应是 G4 最难段，生成器结构
  必须从一开始就镜像 Lean 定义（emit_rpn 与将来 Lean 定义共用同一
  展开顺序）；
- δ-sat 6 条是尖锐边界（等号可达），区间法在边界点永远 lo=0 →
  需要 Eps 标签的 ε 余量或对称性论证，可能个别走 Flyspeck 原证明脚本。

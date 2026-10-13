# mono-corner 侦察：enclosure 宽度解剖 + m_mono_pass_gen 落地定标（Phase 4 W5 线首波）

> 车道：Phase 4 algo lane W5（W4 线二任的直接延续）。任务两件：①用 W4 收编的
> `gsplit_eval` 家族对 split_0_2 叶 0 全盒与 sb1 盒做**逐 top-level sum 项宽度解剖**；
> ②精读 flyspeck `m_verifier.hl:1099 m_mono_pass_gen` 及其调用链，对照我方
> CertTM/BBTreeGD 基础设施写落地设计注记。本文是侦察交付物，不改任何 lane 文件。
> 探针全部在 /tmp/p4w5/（width_probe.py / tm_probe.py / tm_probe3.py + 三个 .out）。

## 0. 一句话结论

叶 0 的 ≈6 宽 enclosure **不是某个坏项，而是全体 ~7 个 √/atan/div 型原子各自贡献
0.2-2.3 的"民主式"堆积**；真函数在盒上几乎常数（sb1 真值域宽仅 0.0098）。
**∂ⱼf 在 sb1 上六维全部真单调**（有限差分实证），但一阶 TM 导数 enclosure 污染
~16×（±0.8 vs 真值 ±0.05）——mono 路线的正确形态不是"大盒上直接定号"，而是
**"细分→定号→restrict 到极值面→点盒精确求值"的递归**；点盒上 TM 退化为精确
（err=0，实测 fB 与 mpmath 真值全位吻合），这是整条路线的支点。

## 1. 仪器：内核同构 TM 镜像（本波主要基建遗产）

`gsplit_eval` 只能算 guard（无 atan/trans），且**裸区间语义会误报宽度**：主 prog
含 276 个 div、241 个 atan，非 guard 的除数在 b0/sb1 上大量跨 0（sb1 上 15 起、
ite_straddle=0 与 W4"guard 全定号"一致），裸区间下整叶 POISON——而内核实际成功
（−6.04）。原因：内核 `.div` 先走 `TaylorM.inv`（保斜率的倒数模型=仿射算术），
裸区间只是 fallback。**因此逐项解剖必须对齐 TaylorM 语义，不能停留在 gsplit_eval。**

`/tmp/p4w5/tm_probe3.py` = evalTMHullD2 的精确有理镜像（Fraction 端点替代 Dyadic
圆整，结构逐节点一致）：fB/dfB 区间模型、mul 误差 `W̃f·W̃g + …`、sqrt/inv 证书级
模型、atan 单调模型、ite decided→单支 / straddle→iteHullTM2 复合、div inv-else-
fallback、closed 走语法 var-free 判定。健全性已验证：b0/sb1 值域均含真值
[0.0257, 0.0356]；点盒求值 = 精确值。

镜像调试中钉死两个**我方镜像 bug**（非 emit_lean bug，不涉 tracked 文件）：
- 分数 isqrt 精度只有分母级（√(8/9)→[8/9,1]，宽 1/9）——常数折叠被污染；
  修复=2^150 精度开方（内核 sqrtI 证书是 gran −80 级，同理）。
- `zip` 截断：常数模型 dfB 用空列表，与变量模型 add/mul 后 dfB 变空、斜率全灭
  （对应内核 constTM 的 dfB 必须是 n 维零向量）。这两个坑在写 Lean 侧
  evalTMHullFill2 精度优化时同样会踩。

## 2. 交付①：逐项宽度贡献表

prog 结构：`0 − T1`，T1 = 1569-op 巨型和，**完全加性分解只有 9 个原子**
（atom=递归拆尽 add/sub 后的连续 RPN 切片）。变量 7 维
（hminus, x1..x6），盒 b0（叶 0 全盒）宽 0.037-0.061/维。

### 2.1 b0（叶 0 全盒）——镜像精确值 vs 内核

| 量 | 镜像（精确有理） | 内核（W4 实测） |
|---|---|---|
| whole enclosure 宽 | 5.68 | 6.30 |
| loBound | −2.81 | −6.30 |
| ite straddle | 3（iteHullTM2 jumpBound） | 同 |

top 原子（宽，降序）：**div(116 ops) 2.31 / mul(252) 1.42 / mul(252) 1.41 /
mul(252) 0.39 / mul(252) 0.30 / mul(252) 0.30 / mul(78) 0.26**，其余 ≈0。

### 2.2 sb1（gsplit 13 盒之一；注意 13 盒实为**只沿 x4 的一维分区**）

| 量 | 镜像 | 内核 |
|---|---|---|
| whole enclosure 宽 | 1.538 | ≈6.05 |
| loBound | −0.741 | −6.049 |
| ite straddle | 0（guard 全定号，复证 W4） | 同 |

top 原子：mul 0.339 / div 0.323 / mul 0.281 / mul 0.271 / mul 0.270 / mul 0.267 /
mul 0.232——**七个同量级原子，无主犯**。对照真值：f 在 sb1 的真值域宽仅
0.0098（[0.0259, 0.0356]），enclosure/真值 ≈ 157×。

13 盒镜像 loBound：sb0=−2.09（含 3 个 ite straddle 的残差盒），sb1..sb12 =
−0.741 → −0.659 单调收敛（x4 切片越细越好但**收敛到仍 NEG**——纯切盒死路，
W4 结论的镜像级复证）。

### 2.3 主贡献项结论

1. **无单项 ≈6**：宽度是 7 个 √/atan/div 积型原子的和式堆积；任何"找到坏项换
   表达式"的单点修复路线不成立，**必须降维（mono/角点）或换 enclosure 机制**。
2. b0 上 div 原子独大（2.31/5.68=41%）：gsplit 若在切 guard 时兼顾
   "除数跨 0 宽度"（除数定号面预切），b0 宽度可先砍 ~2.3——与 mono 路线正交、
   可叠加。
3. **镜像 vs 内核保真差**（−0.74 vs −6.05，~8×）是**内核侧额外松弛**（transOn
   atan 级数尾 ~0.004/节点×155、rung/chopCeilTo、cert 粒度的叠加），非镜像错误
   （镜像健全性已对拍真值）。悬案：建议 W6 用 `evalTMHullFill2` 追踪器做一次
   逐节点镜像-内核宽度对拍——若能把内核收紧到镜像量级（~1.5），大量 NEG 叶
   不必等 mono 就能翻正。这是本波挖出的**第二条免费武器线索**。

## 3. 交付②：∂ⱼf 定号候选清单

**真值层（mpmath 40 位，中心+39 随机点，步长 10⁻⁶ 盒宽）——sb1 全维严格单调**：

| 维 | ∂f/∂xⱼ 真值范围 | 定号 | 镜像 TM 导数 enclosure |
|---|---|---|---|
| hminus | ≡ 0.0（f 值表达式不含 hminus，只进 guard） | 平凡（ⵓ 维自由） | [0,0] |
| x1 | [−0.0291, −0.0274] | **负** | [−0.745, +0.847] 跨 |
| x2 | [+0.0433, +0.0448] | **正** | [−0.811, +0.716] 跨 |
| x3 | [+0.0484, +0.0502] | **正** | [−0.834, +0.729] 跨 |
| x4 | [−0.0054, −0.0047] | **负**（最弱，~10× 小于其他维） | [−0.738, +0.791] 跨 |
| x5 | [+0.0519, +0.0536] | **正** | [−0.865, +0.752] 跨 |
| x6 | [+0.0506, +0.0525] | **正** | [−0.841, +0.732] 跨 |

结论：**sb1 上 f 真单调（6/6 维）**，min 在角点（x1,x4=hi；x2,x3,x5,x6=lo），
角点真值 ≈ +0.0259 > 0——**叶 0 在 sb1 上是"真且可证"的，缺的只是导数
enclosure 的污染**（16×）。但一阶 TM 导数 enclosure 在当前盒宽下全维跨 0，
**"在大盒上直接 ∂ⱼf 定号"不成立**；定号需要的盒宽收缩比：
- 一般维（|∂|≈0.03-0.05，enclosure 半宽 0.8）：~5 次**单维**二分（32×）；
- x4（|∂|≈0.005）：~8 次单维二分（256×）——但 gsplit 已证明 x4 方向切分便宜
  （13 盒就是纯 x4 切分），且 x4 定号后该维直接 restrict 掉。
- 定号后 payoff：镜像数据显示 fB（中心 enclosure）本身含 +0.03；斜率定号后
  线性项从 −|dfB|·w 变 +|dfB|·w_min，再 restrict 到面/角点，点盒 TM=精确值。

## 4. 交付③：m_mono_pass_gen 机制摘要（考古）

### 4.1 三层结构（HOL 侧）

**证书层** `verifier/certificate.hl`：
- `result_tree = Result_pass(int,bool) | Result_mono(mono_status list, r1) |
  Result_glue(int*bool*r1*r2) | Result_pass_ref int | ...`
- `mono_status = {variable:int; decr_flag:bool; df0_flag:bool; ti_flag:bool}`——
  df0_flag 选择 formal 侧定号证明走**直接区间算术**（fs.df 编译期符号偏导）还是
  **Taylor partial bound**；证书只记决策，数值在 kernel 重放。
- `Result_glue(i, convex_flag, r1, r2)`：convex_flag=true ⇒ 两子证书是 i 维的
  左/右**面盒**（restrict_domain），另验 ∂²ᵢᵢf ≥ 0（凸⇒最大值在面上）；
  =false ⇒ 中心超平面二分、两半独立验证后无条件 glue。

**formal 层** `verifier/m_verifier.hl:1099`：`m_mono_pass_gen n j decr_flag
diff2_th partial_mono_th sub_th pass_th` 实例化
- `M_CELL_INCREASING_PASS_LEMMA`（:631）：`∂ⱼf ≥ lo ≥ 0` 于 domain + C² +
  面盒(u = x 仅 j 坐标换 z_j) 上 `m_cell_pass f (u,z)` ⇒ 全盒
  `m_cell_pass f (x,z)`（= ∀x∈box, f x < 0）。单调⇒最大值在极值面，面证了全盒
  就证了。`M_CELL_DECREASING_PASS_LEMMA`（:704）对称。
- `M_CELL_CONVEX_PASS_LEMMA`（:738）：∂²ⱼⱼf ≥ 0 ⇒ max 在两端点面，两面 pass
  经 `partial_convex_max` glue 成全盒。
- 调用链 `m_verify_raw`→`verify_mono`（:1257）：restrict_domain 逐 mono 变量
  嵌套 restricting → 递归验证**最内层面盒**证书 → `m_mono_pass_gen` 逐维展回。
  多变量 mono 是**同时**restrict（一个面盒装所有单调维的极值坐标）。

**搜索层** `informal/informal_search.hl:151 try_mono`：check_cell 三连失败后
（raw_intervals0 裸区间快查 → Taylor upper<0 → lower≥0），对每个宽度>0 的维 j
用 `eval_m_taylor_partial_upper/lower` 试 ∂ⱼf 定号；**把所有定号维一起 restrict**
到极值面，`construct_certificate0` 递归验证面盒（内部可再 mono/glue/二分），
成功则发 `Result_mono (st, result)`；`mono_depth` 选项控制 mono 嵌套深度
（:266 默认单测里 200）。**定号失败=该维不动，不是失败**；全部维都定不了号才
回退域二分。

**重放层** `informal/informal_verifier.hl:175 mono_test` + `m_verifier_main.hl`：
`find_p` 从 p_min..p_max 扫精度 pp 直到 mono_test 通过，**证书只存选中的 pp**
（adaptive_precision=每节点精度由搜索侧定、kernel 按证书重放）；`raw_intervals0/
raw_intervals1` = Taylor 之前的裸区间快查旗标（easy 单元免 Taylor）。

### 4.2 关键结构差（对照我方）

- formal_ineqs **无 ite**：分支在 bank 归一化层拆成独立不等式，verifier 永不面对
  guard-straddle；mono 的 C² 前提（diff2c_domain）因此总可满足。我方：mono 只能
  应用在 **guard 定号子盒**上（gsplit 先行），定号后分支解析、∂ⱼf 按支链符号微分。
- HOL 的 ∂ⱼf 定号=对**形式偏导表达式**做区间算术（df0 路线）或 Taylor partial；
  我方等价物 = **对符号微分后的 IExpr 跑 checkPosTMHull**（同一内核、零新证明
  即得 soundness，见 §5）。

## 5. 落地路线定标（推荐 A：编译期符号微分 + TM 定号 + 角点化）

### 5.1 我方内核的两个"latent mono"事实（本波镜像实验的机制发现）

1. `TaylorM.loBound = fB.lo + Σᵢ (dfBᵢ·[loᵢ−yᵢ, hiᵢ−yᵢ]).lo − err`——对称盒上
   dfB 跨 0 时线性项 = −|dfB|·w（最坏）；**dfB 定号后自动变成 +|dfB|·w_min**。
   即斜率定号的信息一旦进模型，loBound 机制原生受益。
2. **点盒退化**：w=0 的盒上 evalTMHullD2 的 W=0、err→0，fB=精确值（实测
   b0/sb1 中心点盒 fB 与 mpmath 真值全位吻合、err=0）。mono 把盒 restrict 到
   角点后，"验证"变成零成本精确算术。

### 5.2 路线比较

| 路线 | 内容 | 内核工作量 | Python 工作量 | 风险 |
|---|---|---|---|---|
| **A. 符号微分+TM 定号+角点化**（推荐） | 搜索/发射侧对分支解析表达式符号微分得 dfⱼ IExpr；`checkPosTMHull dfⱼ box ps`（现成）定号；新 lemma "盒上 ∂ⱼf 定号 ⇒ f ≥ 角点值"；角点用现成 TM 精确求值 | **中**：evalReal 链式法则 ~300-500 行（add/mul/div/neg 直接；sqrt/atan 用 Mathlib `Real` 导数）+ mono 归约 ~50-100 行（Mathlib `Monotone` Pi 积序）+ 驱动 glue | ~2-3 天（/tmp/p4w5/tm_probe3.py 的 diff+镜像可直接移植进 emit_lean `--mono`，含 gsA 驱动形态） | 中：evalReal 微分Lemma 的域前提（div≠0、sqrt>0）要逐 op 核对 |
| B. 区间差商定号（免符号微分） | 用 f 的差商 (f(x+h eⱼ)−f(x))/h 的 TM 定号 | 同样需要 evalReal 差商=∂ⱼf 的中值引理，**省不了实分析**，还多一变量 | 更大 | 高：不值 |
| C. 采样辅助 | 非内核可表达，只能做搜索侧启发（找最有希望定号的维/最先切哪个盒） | 0 | 小 | 无（仅作 A 的启发） |

纯切盒（无 mono）已被两层数据证死：内核 13 盒 −6.04 不动，镜像 13 盒收敛到
−0.659 仍 NEG。

### 5.3 路线 A 落地图（建议实施序）

1. **Python 发射侧**（~2-3 天）：`emit_lean.py --mono`：对 NEG 叶 (a) gsplit 到
   guard 定号子盒（现成 `--gsplit` 驱动）；(b) 每子盒上对解析后表达式符号微分
   （probe3 的 `diff()` 已验证，含 div/sqrt/atan/abs 规则与 RPN 切片拼接）；
   (c) 发射 dfⱼ 的 checkPosTMHull stage-A 探针（复用 hull 管线，sqrtCerts 按子盒
   追踪）；(d) 定号维收集进证书，非定号维按 §3 收缩比继续单维二分（x4 先行）。
2. **Lean 内核侧**（~1-2 周，单专用 lane）：
   - `evalReal_deriv`：`∂ⱼ (e.evalReal ρ) = (dfⱼ.evalReal ρ)` 逐 op 引理
     （域前提：divisor.evalReal ≠ 0、radicand ≥ 0、guard 已解析）；
   - `mono_corner`：盒上 ∀ⱼ ∂ⱼf 定号 ⇒ `∀ ρ∈box, f ρ ≥ f corner`（Mathlib
     `Monotone`/`Antitone` 积序，~80 行）；
   - 装配：`checkPosTMHull dfⱼ box ps ∧ cornerTM → checkPosTMHull(f, cornerBox)`
     ⇒ 全盒 POS。
3. **验收锚**（W3/W4 语境下的可测判据）：split_0_2 叶 0 的 13 个 gsplit 子盒在
   mono 降维后翻 POS——具体：sb1..sb12 的 min-角点真值 +0.0259 > 0，点盒 TM
   精确，故每子盒预期 ≤ 6^5 量级角点证书（x4 维由 13 切分预解）；**总叶数
   ≤ ~10³/叶**（vs 纯切盒 ∞）。反向锚：内核对拍 mpmath 角点值差 ≤ 2^-64。
4. **与第三武器（R3 radicand 预切）的正交性**：mono 处理"宽盒上和式堆积"，
   R3 处理"√ 定义域切分"；叶 0 的 div 原子（b0 宽 2.31）提示第三种廉价预切
   ——**除数定号面预切**（divisor-straddle 面切分），可作为 gsplit 的第二
   优先队列启发（`gsplit_subboxes` 的 strad() 目前只计 guard 跨宽，加一项
   div 除数跨宽即得，~10 行 Python）。

### 5.4 风险与悬案

- **镜像-内核 8× 保真差**（§2.3）：mono 的验收锚以内核实测为准；建议先跑
  evalTMHullFill2 逐节点宽度对拍（工具现成），若系 transOn atan 宽参数松弛
  所致，紧 transOn 本身就是一条独立提速线（HOL informal_atn 半角迭代同构）。
- x4 弱单调维（|∂|≈0.005）：定号需 ~8 次单维二分，证书叶数可能上浮一个量级；
  缓解 = x4 已是 13 切分方向，继续沿 x4 切到定号即止损。
- b0 的 3 个 ite straddle 残差（sb0）：mono 前仍需 gsplit 把 guard 清干净；
  iteHullTM2 的 df-hull 复合在 straddle 叶上与 mono 的交互未测。
- abs 节点（18 处）在内核是 fallback 常数模型（斜率死亡）；若 abs 出现在
  定号路径上会切断 dfB 信息——叶 0 的 abs 都在常数折叠区，实测无碍，其他叶
  需画像。

## 6. 新雷区（供编排者入 §5.4'/日志）

1. **裸区间镜像 ≠ 内核宽度**：gsplit_eval/naive interval 对主 prog 一律 POISON
   或巨宽（除数跨 0 由 Taylor inv 吸收）——任何"用 Python 精确区间预估内核
   enclosure"的实验必须上 TM 同构镜像，否则结论方向都会错（本波实证）。
2. 分数 isqrt 低精度陷阱（√(8/9)→[8/9,1]）：Python 侧开方一律升到 2^150 级，
   对应内核 sqrtI 证书粒度。
3. Python `zip` 截断陷阱：常数模型的斜率向量必须是 n 维零向量，不能空列表
   （镜像实测：一处空列表让全树斜率静默归零，且 valueRange 看起来仍"合理"）。
4. gsplit 13 盒是**一维分区**（纯 x4）：guard 引导切分会锁死在单一维度；
   mono 路线的切分队列必须按"最接近定号的维"重排，不能沿用 guard-straddle
   宽度启发。
5. subboxes.json 的 dim 是 pair-of-pair（[[m,e],[m,e]]），ad-hoc 脚本双层解包
   写成三层是高频手误（本波踩过）。

—— 探针与全部输出：/tmp/p4w5/（易失；关键数字已全部抄录上文）。

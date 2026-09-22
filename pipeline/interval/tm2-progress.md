# TM2 进度笔记（trans TM 规则：atan/ln/sin + BIXPCGW 复测）

> 接力记录。工作树 kepler-g4e（wip/g4-emit）。TM0/TM1 已合入
> （456011b5/90567ae0/e18532cc），详见 tm0/tm1 笔记。

## 0. 对齐与计划（2026-09-21）

任务书：evalTM 加 trans 臂（atan/ln/sin），延续纯代数 ∃a-Valid 路线；
BIXPCGW 150 叶复测；回归。

合成模式（同 sqrt/inv）：g∘f 的余项分解
`g(f(ρ)) − g(f(y)) − q·L = [g(f(ρ)) − g(f(y)) − q·Δf] + q·(Δf − L)`，
q = g′(f(y))，|Δf − L| ≤ err_f，|Δf| ≤ W。第一项 ≤ C·W²，C 为曲率界。

## 1. 路线选择与 Mathlib 实测（完成）

- **atan**（任务书批准的唯一分析节点）：`arctan_residual` 用
  `exists_hasDerivAt_eq_slope`（MeanValue.lean:122，实测签名
  `(hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hff' : ∀ x ∈ Ioo a b,
  HasDerivAt f (f' x) x)`，f/f'/a/b 隐式）+ `Real.hasDerivAt_arctan`
  （ArctanDeriv.lean:79）+ `Real.continuous_arctan`（Arctan.lean:366）。
  残差恒等式 `(s−t)(t²−ξ²)/((1+ξ²)(1+t²))`（分母 ≥ 1 直接吃掉），
  |·| ≤ |s−t|·|t−ξ|·(|t|+|ξ|) ≤ W²·2B，B := |fB|.abs.hi + W。
  曲率界 dyadic 精确、无 recip 证书。
- **ln**（纯初等，不用 MVT）：`Real.log_le_sub_one_of_pos` +
  `Real.one_sub_inv_le_log_of_pos`（Log/Basic.lean:306/311）+
  `Real.log_div` → R ∈ [−(s−t)²/(s·t), 0] → |R| ≤ W²/c²，
  c := fB.lo − W > 0 门。斜率 recip fB（o1），曲率 recip point c²（o2）。
- **sin**（纯初等）：`Real.one_sub_sq_div_two_le_cos`（Bounds.lean:123，
  x 隐式）+ `Real.abs_sub_sin_le`（:169）→ 残差 = sin t·(cos h−1) +
  cos t·(sin h − h)，|·| ≤ h²/2 + |h|³/6 ≤ W²/2 + W³/4（dyadic 精确，
  无条件、无证书）；斜率 cos(f(y)) 用 `transOn cosK`（节点自带 N/out）。
- **cosK** 本期无规则（hybrid fallback 兜住）；TMSafe 扩展：sinK/atanK/lnK
  true，cosK false。
- 结构：`TransTMP := ⟨o1 o2⟩`；TMParams 加第三字段 `transCerts`；
  `TaylorM.trans` 按 TKind 分发（cosK → none）；值包围统一
  `transOn k ⟨fB.lo, fB.hi⟩ N out`（复用节点 rung，`transOn_sound` 桥接，
  注意全名是 `IExpr.transOn_sound`——在 namespace IExpr 内）。

## 2. 实现与验证（完成）

CertTM.lean 新增 ~450 行：sin_residual/log_residual/arctan_residual +
valid_trans_sin/ln/atan + valid_trans 分发 + `DInterval.abs_lo_nonneg` +
evalTM trans 臂（evalTM_sound trans case）+ evalTMH trans 臂（失败回退，
evalTMH_sound trans case）。`lake env lean CertTM.lean` 零错误零警告零
sorry。

CertG.lean 三个 TM2 pilot（内核闭合 + 公理仅标准三）：
- sin：`sin x − x/2` on [1/4, 1/2]，根盒单叶闭合（rung 5/−20）。
- atan：`arctan x − x/2` on [1/2, 1]，根盒单叶闭合。
- ln：`log x + 3/4` on [1/2, 1]：根盒 TM 失败（c = 1/2 → 曲率 1/c² = 4
  吞余量），深度 1 树两叶闭合（对照：根盒 [1/2, 3/4] 边缘单叶可闭合，
  实测于 scratch）。
回归：TM0/TM1 全部 6 条 end-to-end + TM2 三条共 9 条公理审计
`[propext, Classical.choice, Quot.sound]`；lake build CertG/CertTM 绿。

## 3. BIXPCGW 150 叶复测（完成：性能墙拆除 + 诚实负面+根因）

### 性能墙：两个独立炸弹，全部拆除

1. **闭 trans 节点重复求值（主炸弹）**：BIXPCGW 主 prog 的闭式
   `trans arctanK (const …) 2048 (−64)`（N=2048！）在 evalFillC 里有 memo
   cache（"memoized 2 closed subterms"），而探针的 TM 臂每叶每目标重算
   2048 项 Taylor——分钟级/叶。修复（语义正确，不是 hack）：**闭 trans
   节点是常数函数**——`IExpr.isClosed` 上移到 `Expr.lean`（+
   `evalReal_const_of_isClosed` 归纳引理），CertTM 加 `closedTM`
   （err=0、零斜率的精确常数模型）+ `valid_closed`，evalTM/evalTMH 的
   trans 臂闭节点优先走它（不吃 transCerts）。FillParams.lean 删除重复
   定义（改从 Expr 引入）。
2. **mantissa 表示爆炸（次炸弹）**：`chopCeilTo`（上个 session 交接的既定
   方案）已实现并入 CertTM：`TaylorM.errScale`（2·最粗 w 指数 − 24 位
   slack），chop 插入 mul/inv/sqrt/trans 的 err 合成点（组合子级 =
   evalTM/evalTMH 天然双侧同点），`toReal_le_chopCeilTo` 证明完毕，
   六个 valid_* 的 err 收尾改为 `le_trans … (toReal_le_chopCeilTo …)`。
   探针侧 recip 粒度改**值相对**（`vscale d = |m|.log2 + e`，
   `out := −vscale − 32`：recipFloor 的 hk 恒成立且 mantissa ~32 位）——
   原 `out ≤ −b.e` 版在深链 b.e ~ −10⁵ 时造出 800K-bit 中间量。
   注意：probe5c（chop 但旧粒度）仍卡死证明单靠 chop 不够，粒度才是
   trans 臂的主爆点；两者都要。

### 拆除后的 A/B/C 时序对照（5 叶样本，每叶两目标）

- probe5nx（trans 纯 fallback）：2.6-3.1s/叶 ✓（基线）
- probe5v（trans 规则开 + vscale 粒度，**无闭-trans 修复**）：~200s/叶 ✗
- probe5w（全部修复）：**2.6-3.7s/叶** ✓ —— 回到基线量级

### 最终 150 叶数字与失败形态（如实报告）

**probeF（最终管线：chop + 值相对粒度 + 闭-trans 常数模型 + trans 规则
全开）：TMRATE pass=0 fail=150 total=150**（~4.3s/叶，性能墙已拆除，
运行 ~15min 完成）。逐叶输出留档 `TM1ProbeBIXPCGW.d/probeF.out`。

**失败形态（diag3 逐叶分解 fBlo/err/loBound，trans 规则全开）**：
TM err 仍 ~O(1)——**BIXPCGW r1 FAIL 叶的临界性在 `sqrt(≈0)` 与
`ite/abs` hull 上**：sqrt 的 TM 规则要求 radicand 认证下界 c > 0
（∃a-线性模型在 √ 的 0 处斜率爆炸，数学上不可能），这些叶的 radicand
下界 ≤ 0 是结构性的（零等值面穿盒），只能走零阶 fallback（err = 包围
宽度 O(1)）并沿 mul 链放大；ite 跨 0 的 hull 同理。裸区间在这些节点上
是单调精确的，所以 TM 在此样本上**不占优**（PASS 对照叶上 TM loBound
也比裸区间低 ~0.1）。

**结论修正（对设计 §0 的 TM1/TM2 验收预期）**：一阶 TM（含 trans 规则）
对 BIXPCGW 失败叶集的**直接判定**无增益——失败叶的瓶颈不是代数依赖
过估，而是 (a) sqrt 在 radicand≈0 的不可微奇异，(b) ite/abs hull，
(c) 真边缘≈0 需二分。Flyspeck 原版对这类 cell 也是二分到底。TM 的正确
定位是**临界带的收敛加速**（二分树中叶的判定），不是单叶直通率；这
要求测量口径改成"二分树总叶数"（TM3 驱动整合后测）。设计文档 TM1 验收
的"≥95% 单叶直通"口径应作废——见任务书偏差记录。

## 4. 交付清单（按 commit）

- d763cc34：trans 三规则 + valid_trans_* + TMSafe 扩展 + 三个 TM2 pilot。
- 30e84adf：chopCeilTo/errScale 与四处 err 合成点插入（main 已合入）。
- 本次：Expr.lean（isClosed 上移 + evalReal_const_of_isClosed）、
  FillParams.lean（删重复）、CertTM.lean（closedTM + valid_closed +
  evalTM/evalTMH 的 trans 臂闭节点优先常数模型）、tm2-progress.md 定稿。
- 探针工作区 `Cases/Repair/TM1ProbeBIXPCGW.d/` 不入库（Repair 惯例），
  再生：`python3 pipeline/interval/tm1_probe_gen.py`（TM2 的 trans/闭节点
  改造在 driver.lean 里，被 gen 脚本覆盖——注意下次 regenerate 会丢；
  最终 driver 的内容以 tm2-progress.md §3 描述为准）。

## 5. 验收对照（任务书三口径）

1. evalTM trans 臂 + valid_trans_*（atan/ln/sin）+ TMSafe 扩展：✓ 完成，
   零 sorry。
2. BIXPCGW 150 叶复测：✓ 完成，数字 = **0/150**（改善：无），逐叶分解
   与根因见 §3 失败形态——一阶 TM 在此样本的 sqrt(≈0)/ite/abs 结构上
   数学上不可判定，设计 §0 的"≥95% 单叶直通"口径作废，正确口径是
   TM3 的"二分树总叶数"。
3. 回归：✓ 9 条 end-to-end 公理仅标准三，lake build 绿（8667 jobs）。


## 4. 本 session 交付（commit d763cc34）

- evalTM trans 臂 + sin/atan/ln 三规则全证明（零 sorry，atan 走批准的 MVT
  路线，sin/ln 纯初等）+ TMSafe 扩展 + hybrid 回退 + CertG 三个 TM2 pilot
  （sin/atan 根盒单叶，ln 深度 1 树）+ 全回归 9 条 end-to-end 公理审计
  `[propext, Classical.choice, Quot.sound]`。
- BIXPCGW 复测：性能墙阻断，诊断与修复方案如上（§3）。
- 在跑：probe2（150 叶全量，probe5nx 对照已证实基线 0/150 立等可取——
  见 TM1 笔记；trans 规则对通过率的增益待 probe2 或 chop 版复测）。
- 验收对照：任务 1 ✓（三规则 + evalTM 臂 + TMSafe）；任务 2 部分（复测
  被性能墙阻断，根因与方案明确）；任务 3 ✓（回归全绿）。

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

## 3. BIXPCGW 150 叶复测（受阻：性能墙，诊断完成，方案已定）

探针升级：evalTMHA 加 trans 臂 + genTransTMP。复跑同一 150 叶样本。
**撞上性能墙**，A/B 对照定位：

- probe5nx（trans 臂 = 纯 fallback，其余全同）：5 叶 ×2.6-3.1s/叶，完成。
- probe5（trans 臂 = TM 规则）：>15min 未出叶 0。
- probe2（全量 150 叶，trans TM 开）：后台继续跑（截至笔记时 ~108min CPU
  未完成；nice 19 与其他 runner 共存）。

**根因（高置信）**：`TaylorM.mul`/`inv`/`trans` 的 err 项含 `W.mul W`
（平方）与 `c³` 级连——BIXPCGW 主 prog 是深左链（~27K op），dyadic 指数
沿链累加到 −10⁵ 量级，`W.mul W` 把 mantissa 翻倍成 ~10⁵ bit（~100KB
整数），再经链式 mul/add 复合增长——**值很小但表示爆炸**。裸区间 eval
（probe1/nx 快）没有 W² 项所以不炸。这不是算法错，是**表示不修剪**。

**方案（下一 session）**：给 TM 内核算术加**外向舍入修剪**：
err/W 类上界量 ceiling-chop 到目标指数（对上界语义安全：上界放大仍合法），
fB.lo floor / fB.hi ceil（包围向外放宽合法），dfB 同样外向——需要一个
`Dyadic.chopFloor/chopCeil : Dyadic → Int → Dyadic` 加 `toReal` 单调性引理
（~30 行）+ 在 mul/inv/sqrt/trans 规则的 err 合成处插入 chop（目标指数如
`min (2·box 指数) − 32`）。内核侧 checkPosTM 同样插入（保持 probe≡kernel
语义）。这使 TM 判定在 27K-op 程序上的成本回到 probe1 量级。
注意：chop 插入点必须在 evalTM/evalTMH 同一处双侧同步（现有 evalFill
双侧镜像纪律的 TM 版——设计文档 §5.1 的已知事故点）。

备选快速通道（若只要通过率数字）：探针侧把 W/err 在 VM 里 chop（内核语义
随后补），先出数。

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

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

## 3. BIXPCGW 150 叶复测（进行中）

探针升级（TM1ProbeBIXPCGW.d/driver.lean）：evalTMHA 加 trans 臂 +
`genTransTMP`（auto 粒度：recipFloor 成功性由 `out ≤ −b.e` 保证，精度
下限 2⁻³²）。复跑同一 150 叶样本（rung 12/−64），结果待填。

## 4. 收尾（待填）

# atn2 复合规则(div 越零 @227)设计与侦察报告

> 车道:Kimi 线(worktree `kepler-atn2`,分支 `wip/atn2-chop`,off main `61c8f9c0`)。
> 对应主仓接口:`docs/549-kimi-sync-2026-09-25.md` §2(K2 裁决)、
> `docs/549-lane-log.md` 十五更(div 6,565→5,928,@227 的 5,706"包络层数学不可救")。
> 落地:`lean/Kepler/Interval/CertTM.lean` 尾部新增一节(纯追加 559 行,
> 既有定义/定理**零改动**)。

## 1. 侦察:@227 的真实结构

case JSON(`pipeline/interval/out/cases/5490182221.json`)RPN 定位:
`prog[7].ite.else[0].ite.then`(= ite7-else → ite0-then 支)的
`ip=227 div` + `ip=228 atan`,即

```
then0 = π/2 − arctan( sqrt(4·y0²·(…)) / neg(多项式) )   -- num = ip156 sqrt, den = ip226 neg
```

根表达式语义(与发射模块 `C549StraddleBatchExpr` 一致):

```
E = 1893/1000 − (4·atan 1)/2 − ite值 = 1.893 − π/2 − V
叶检查 E > 0 ⟺ V < 0.32220…
```

在全部 1,354,264 张 cert 叶上用朴素区间算术(IA)评估 den 子式:

| 分类(采样 41 点/叶) | 叶数 | 占比 |
|---|---|---|
| den IA 跨零合计 | 26,415 | — |
| 其中采样全负(伪跨零偏负) | 19,087 | 72.3% |
| 其中采样全正(伪跨零偏正) | 3,114 | 11.8% |
| 其中真跨零(采样取到两号) | 4,214 | 16.0% |

- den 的 IA 值域宽 log2 ∈ (2,6](与 C 侧 tm_div_fail_diag 桶口径一致),但**真值域宽
  ~2³**(采样例证:IA [-36.4, 0.002] vs 采样值域 [-21.7, -14.1])——宽度差来自
  多项式抵消的依赖性膨胀,不是舍入/mantissa 问题。
- num = sqrt(…) ≥ 0 恒成立(sqrt 规则天然定号)。
- q = num/den 在部分叶上爆炸(采样 max ~1.3×10⁴)→ 真跨零叶上
  then0 = π/2 − atan(q) 下确界 ≈ 0(不取到,`arctan < π/2` 严格),Real 语义
  x/0 = 0 点处 then0 = π/2。

## 2. 关键障碍(方向性结论,先于设计)

**ite0 的 guard 在这 26,415 张叶上 IA 全部跨零**(采样:非负 19,185 = 72.6%、
全负 3,172 = 12.0%、真跨零 4,058 = 15.4%)。于是内核 `evalTMHullD2` 走
`iteHullTM2` df-hull:hull 的 V.hi 必含 then0 在 den<0 区域的值(> π/2 ≈ 1.57),
而检查要求 V < 0.3222。结论:

> **即便有完美的 atn2 规则,hull 语义下 guard 未定的叶结构性只能 NEG,不能
> PASS。** div 越零规则(none → some)是必要前提,但不是充分条件。救回主体需要
> (a) guard 定号化(guard 多项式求值收紧——本质是 M2b 根因③"区间积丢中心 AD
> 抵消",或 C 侧域切分);(b) guard 真跨零的 ~15% 叶必须盒切分语义。
> 同步包方案 A("chop 分母压至 ~2³ 转定号")的机制描述与 `Dyadic.chopCeilTo`
> 语义相反(chop 是向上放松,只能变宽);跨零包络不可能由 chop 转定号——
> 伪跨零的救回必须靠更紧的求值,不是 chop。

## 3. 交付的 Lean 规则(CertTM.lean,行号为本提交后)

| 名称 | 行 | 内容 |
|---|---|---|
| `atanDivHalfPiBound` | 4973 | π/2 的 dyadic 严格上界 `1609·2⁻¹⁰ = 1.5712890625` |
| `abs_arctan_le_atanDivHalfPiBound` | 4976 | `\|arctan x\| ≤ P`(由 `Real.pi_lt_d6` + arctan 值域界) |
| `TaylorM.atn2DivTM` | 4994 | 零斜率复合模型:`fB = transOn arctanK (fB₁/fB₂)`(中心商 enclosure,仅当 0∉fB₂)+ `err = P + \|fB\|`(中心收紧支);否则全宽 hull `fB = [−P,P]`, `err = 2P` |
| `TaylorM.atn2DivTM_y` / `_w` | 5006/5018 | 中心/包络保持 |
| `valid_atn2Div` | 5032 | **健全性**:不假设分母定号,`\|g(ρ) − g(y)\| ≤ \|g(ρ)\| + \|g(y)\| ≤ P + …`,覆盖 Real 语义 x/0 = 0 点 |
| `atn2DivFallback` | 5134 | trans 臂的复合 fallback(子模型经基线 `evalTMHullD2` 求值——健全性直接复用 `evalTMHullD2_sound`,规避孙子项归纳) |
| `evalTMHullD2A` | 5150 | 逐臂克隆 `evalTMHullD2`,仅 trans 臂在旧链(TM 规则→区间 fallback)none 后追加复合;消费 div 节点 1 枚 invCert + trans 节点 1 枚 transCert(遍历序对齐) |
| `evalTMHullD2A_sound` | 5208 | 结构归纳 + `valid_atn2Div` |
| `checkPosTMHullA` / `_sound` | 5404/5413 | 检查器与健全性(同 `checkPosTMHull` 形状) |

冒烟测试(全部 kernel `decide`/`rfl`,公理审计见文件尾 `#print axioms` 块):

- `exA_straddle_old_none`(5445,回归锚点):`5 − arctan(x/y)` on [1,2]×[−1,1],
  旧求值器 = none。
- `exA_D2A_agree_on_D2_success`(5449,回归):D2 成功处 D2A 逐字节一致(`rfl`)。
- `exA_straddle_checkPos`(5456,**真跨零 hull 支救回**):D2A 通过,
  loBound = 293·2⁻¹⁰ > 0。
- `exA_straddle_end_to_end`(5460):端到端 `0 < 5 − Real.arctan (x/y)`,
  y = 0 在盒内(Real 除法 x/0 = 0 被覆盖)。
- `exA_centered_checkPos` / `exA_centered_err_lt_hull`(5486/5495,**中心收紧支**):
  den = x − 5/8 on [1/2,1],中心值 1/8 > 0(fB 定号)但包络 [−1/8, 3/8] 跨零;
  err < 13/4 < 2P,与 hull 支结构性区分。

构建:`lake build Kepler.Interval.CertTM` 绿(增量 ~15s);
`#print axioms` 全部 ⊆ [propext, Classical.choice, Quot.sound],零 sorry、零新公理。

## 4. 实测救回率评估

复合规则把 @227 叶从"内核不可验证(none)"变为"可求值(some)"。但按 §2 的
结构分析,在现行 hull 语义下其 loBound  verdict 分布为:

- guard 采样非负(72.6%):hull hi 仍含 then0 ≥ π/2 的值 → 预期 NEG;
  真正救回需 guard 定号化后走 else 支(@227 div 不再被求值)。
- guard 采样全负(12.0%):then 支单独求值,then0 ≤ 0.3222 需 q ≥ 3.08 认证——
  需 den 定号,跨零包络给不出 → 仍需 guard/den 求值收紧。
- guard 真跨零(15.4%):只能盒切分。

即:**本规则是闭合这些叶的必要组件(消除 none),但 PASS 率取决于 guard 层的
后续收紧**。真实叶批量实测需要 emit_lean.py 侧发射 `checkPosTMHullA` 形态的证书
(schema 不变:队列纪律与既有节点对齐)+ Fill2A 镜像(生成器用)——建议列为
opencode 车道集成项。

## 5. 遗留问题 / 后续

1. `evalTMHullFill2A`(Fill 镜像,证书生成用)未实现——复合规则不消耗 sqrt
   mantissa,镜像仅用于探针预测;接入发射器时需要。
2. mul 规则的 AD 抵消修复(M2b 根因③)是 guard/den 多项式求值收紧的正解,
   独立大项。
3. guard 真跨零叶的盒切分语义不在本车道范围(驱动侧)。

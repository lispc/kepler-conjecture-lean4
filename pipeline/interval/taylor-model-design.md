# Taylor 模型（Taylor models）双侧落地设计

> 2026-09-21，Kimi。前置调研基于 kepler-g4e 工作树（`bb_arb.c` 1274 行、
> `Kepler/Interval/` 5373 行、`wave2-disj-design.md` §9 后状态）与
> kepler-conjecture-lean4 工作树的 `reference/flyspeck/formal_ineqs/`
> （`taylor/m_taylor.hl`、`taylor/theory/multivariate_taylor-compiled.hl`、
> `verifier/m_verifier.hl`）。行号引用以这两棵树为准。
> 目标：把裸区间算术的 O(w) 过估升级为**一阶多元 Taylor 模型 + 二阶导余项**
> 的 O(w²) 判定，打通 bb_arb（FLINT 侧）→ 证书 → Lean 内核（dyadic 重算侧）
> 的全链路。本文是设计文档，不含实现。

## 0. 问题界定（为什么必须做）

裸区间算术在边界曲面（f ≈ 0 的等值面）附近过估 O(w)：盒宽 w 减半，区间宽度
只减半，永不分离 f=0——bisection 在临界叶上不收敛。实测（任务书给定口径）：

- BIXPCGW 案例约半数失败叶的通过率 plateau 在 ~46-50%（stage-A 各档 rung 全 FAIL）；
- prep 家族 MKFKQWU 级案例固有叶数 ≥ 10⁹，不可发射。

原始 Flyspeck 证明的解法即 Taylor 模型：`m_verifier.hl` 的每个 cell 判定走
`m_taylor_cell_pass`（`verifier/m_verifier.hl:291`）——一阶 Taylor 展开 +
`diff2_domain`（盒上二阶可导）余项界，过估 O(w²)，w 减半时余项缩 4 倍，
bisection 在临界带上以有限深度终止。**我们移植的就是这个数学结构，不是
任意阶 Taylor 模型**——理由见 §1。

## 1. 语义层设计：一阶多元 Taylor 模型（对齐 m_taylor.hl）

### 1.1 Flyspeck 原型解剖（移植对象）

`multivariate_taylor-compiled.hl` 的核心定义：

```
m_cell_domain (x,z) y w   ⇔  ∀i. x$i ≤ y$i ≤ z$i ∧ max (y$i-x$i) (z$i-y$i) ≤ w$i   (:1349)
diff2c_domain domain f    ⇔  ∀p ∈ interval[domain]. diff2c f p                     (:1355)
m_lin_approx f y fB dfB   ⇔  f 在 y 可微 ∧ f(y) ∈ fB ∧ ∀i. partial i f y ∈ dfB[i]  (:22)
second_bounded f domain ddB ⇔ ∀p ∈ domain. ∀i j. partial2 j i f p ∈ ddB[i][j]
m_taylor_interval         =  m_cell_domain ∧ diff2c_domain ∧ m_lin_approx ∧ second_bounded  (:3007)
```

余项界（`m_taylor_error`，:936 + 等价形 `m_taylor_error_eq` :1409）：

```
error = Σᵢ wᵢ·( wᵢ·|∂²ᵢᵢ f| + 2·Σ_{j<i} wⱼ·|∂²ⱼᵢ f| ) ，余项 |R| ≤ error/2
```

注意这等价于 `½·Σ_{i,j 全序对} wᵢwⱼ·|∂²ᵢⱼ f|`（Schwarz 对称性把交叉项并成 2 倍）。
**设计决策 T-D0：我们直接求全序对和，不用 Schwarz 对称性**——避免依赖
Clairaut 定理的形式化（Mathlib 无现成好用的多元偏导交换定理），代价是
Hessian 项数 n(n+1)/2 → n²（n ≤ 6，可忽略）。

cell 判定（`m_verifier.hl:280`）：上界 `hi(fB) + Σᵢ hi(dfB[i]·tᵢ) + err/2 < 0`
则 cell 通过（Flyspeck 证 f < 0；我们证 f > 0，对偶地用 lo 侧）。

### 1.2 我们的数据结构：线性 Taylor 模型

语义（Lean，ℝ 层）：

```lean
/-- 一阶多元 Taylor 模型：中心点 y、半径包 w、f(y) 界、一阶偏导界、余项界。
    对齐 Flyspeck `m_taylor_interval`，但余项界 err 直接是"½·Σ wᵢwⱼHᵢⱼ"
    的 dyadic 上界（Hessian 界 Hᵢⱼ 不进证书，由内核重算，见 §3）。 -/
structure TaylorM (n : ℕ) where
  y   : Fin n → Dyadic      -- 中心点（盒内，通常取中点）
  w   : Fin n → Dyadic      -- cell 半径包：max(yᵢ−loᵢ, hiᵢ−yᵢ) ≤ wᵢ
  fB  : DInterval           -- f(y) 的包围
  dfB : Fin n → DInterval   -- ∂ᵢf(y) 的包围（线偏导，§3.2 定义）
  err : Dyadic              -- 余项界（≥ 0），|R(ρ)| ≤ err

/-- 语义有效性：对盒内任意 ρ，存在 aᵢ ∈ dfB[i] 使
    |f(ρ) − f(y) − Σᵢ aᵢ·(ρᵢ − yᵢ)| ≤ err。 -/
def TaylorM.Valid {n : ℕ} (M : TaylorM n) (box : Fin n → DInterval)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ i, (box i).mem (M.y i).toReal) ∧
  (∀ i, |((M.y i).toReal - (box i).lo.toReal)| ≤ (M.w i).toReal ∧
        |((box i).hi.toReal - (M.y i).toReal)| ≤ (M.w i).toReal) ∧
  (M.fB.mem (f fun i => (M.y i).toReal)) ∧
  ∀ ρ, boxMem box ρ → ∃ a : Fin n → ℝ,
    (∀ i, (M.dfB i).mem (a i)) ∧
    |f ρ - (f fun i => (M.y i).toReal) - ∑ i, a i * (ρ i - (M.y i).toReal)|
      ≤ (M.err).toReal
```

判定函数（全部落在现有 `DInterval` 算术上，Int 级 `decide`）：

```lean
/-- Taylor 下界：fB.lo + Σᵢ (dfB[i]·[loᵢ−yᵢ, hiᵢ−yᵢ]).lo − err。
    线性多项式在盒上的最小值逐维取端点，纯 DInterval 算术。 -/
def TaylorM.loBound {n : ℕ} (M : TaylorM n) (box : Fin n → DInterval) : Dyadic

/-- 内核判定：Taylor 下界严格为正。 -/
def checkPosTM {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (P : TMParams n) : Bool   -- P = 逐叶参数（§3.4），镜像 checkPos
```

### 1.3 各运算的 Taylor 模型算术规则

记号：M = (y, w, fB, dfB, R)（R := err），W(M) := Σᵢ |dfBᵢ|·wᵢ + R
（f 在 cell 上的振幅界 |f(ρ)−f(y)| ≤ W(M)，由 Valid 直接得）。

| op | fB' | dfB'ᵢ | R' | 条件 |
|---|---|---|---|---|
| const d | ⟨d,d⟩ | [0,0] | 0 | — |
| var k | ⟨yₖ,yₖ⟩ | [δᵢₖ,δᵢₖ] | 0 | — |
| neg | −fB | −dfBᵢ | R | — |
| add/sub | fB±gB | dfBᵢ±dgBᵢ | Rf+Rg | — |
| mul | fB·gB | dfBᵢ·gB + fB·dgBᵢ | Rf·‖g‖ + Rg·‖f‖ + Rf·Rg + Wf·Wg | ‖f‖:=|fB|+|Wf| 型幅值界 |
| div | f/g = f·(inv∘g) | 组合规则 | 组合规则 | gB 不含 0 |
| sqrt | √(f(y)) | dfBᵢ/(2√(f(y))) | Mg'·Rf + ½·Mg''·Wf² | fB.lo > 0 |
| atan | atan(f(y)) | dfBᵢ/(1+f(y)²) | 同上 | — |
| ln | ln(f(y)) | dfBᵢ/f(y) | 同上 | fB.lo > 0 |
| sin | sin(f(y)) | cos(f(y))·dfBᵢ | 同上 | — |

其中一元合成 g∘f 的余项公式（对应 Flyspeck `m_taylor_sqrt_compose`/
`m_taylor_atn_compose` 等，`multivariate_taylor-compiled.hl:3022` 起）：

```
R' = Mg'·Rf + ½·Mg''·Wf²
Mg'  = g' 在 f(cell) 上的区间界      Mg'' = g'' 在 f(cell) 上的区间界
g'' 解析形：sqrt: −1/(4t^{3/2})；atan: −2t/(1+t²)²；ln: −1/t²；sin: −sin t；inv: 2/t³
```

**关键观察**：g'、g'' 都是 `IExpr` 可表达的（cos 有 `TKind.cosK`；1/(1+t²)、
1/t、t^{−3/2} 由 div/mul/sqrt 组合）。所以 C 侧和内核侧都不需要新的"导数
黑盒"——g'/g'' 的区间界用**现有 eval 机制**算（§2、§3.3）。

mul 的 R' 公式推导（标准 Taylor 模型乘法，对齐 `m_taylor_arith.hl` 的
`m_taylor_mul` 思想）：f·g = (f_y + Lf + Rf)(g_y + Lg + Rg)，线性部
f_y·Lg + g_y·Lf，余项含 Lf·Lg（二次交叉项，|Lf| ≤ Σ|dfBᵢ|wᵢ ≤ Wf）与
各 R 交叉项。

## 2. bb_arb 侧（FLINT）

### 2.1 本机 FLINT 盘点（实测）

- 版本：**FLINT 3.3.1**（`pipeline/tools/flint-3.3.1/`，README 记录；头文件
  实测于 kepler-conjecture-lean4 树的同版本副本，
  `include/flint/arb_poly.h`、`gr_poly.h` 均存在）。
- `arb_poly.h` 可用的级数原语（行号实测）：`arb_poly_taylor_shift` (:330)、
  `arb_poly_compose_series` (:337)、`arb_poly_sqrt_series` (:485)、
  `arb_poly_rsqrt_series` (:480)、`arb_poly_log_series` (:488)、
  `arb_poly_atan_series` (:495)、`arb_poly_sin_cos_series` (:524)、
  `arb_poly_integral` (:422)。
- **结论：一阶多元模型不需要 arb_poly**。多元线性模型的系数是"中心点处的
  偏导球 + 盒上 Hessian 区间界"，用普通 `arb` 球 + 自动微分（AD）前向传播
  即可；arb_poly 的级数原语只在未来的单变量高阶扩展（§4 TM-X，明确不做）
  才有用。gr_poly 同理不需要。

### 2.2 C 数据结构草图

```c
/* 一阶多元 Taylor 模型（C 侧）：每 RPN 栈位一个。
   中心点 y 是 fmpq 精确点（盒中点，二分中点天然 dyadic-相容），
   不进 arb 球——求值时以 arb_set_fmpq 入球。 */
typedef struct {
    arb_t  f0;        /* f(y) 球（中心求值，精度 rung_c） */
    arb_t *df;        /* n 个 ∂ᵢf(y) 球（中心求值） */
    arb_t *ddf;       /* n² 个 ∂²ᵢⱼf 在盒上的区间界（粗精度 rung_h） */
    mag_t  err;       /* ½·Σᵢⱼ wᵢwⱼ·|ddfᵢⱼ| 的上界（mag 上取整） */
    int    valid;     /* 0 = 该子式 TM 不可用（ite/abs/div 越零等），退裸区间 */
} tm1_t;
```

求值方式：**单遍 RPN 前向 AD**——每栈位携带 (f0, df[], ddf[])，按
§1.3 规则传播。一阶项在中心点 y（退化盒 [y,y]）上做球算术；二阶项在整盒
上做区间算术（粗精度足够——Hessian 界只需数量级正确）。栈成本 O(n²)·prog
长度，n ≤ 6 时可忽略（对照：BIXPCGW 主 prog 已实测每叶 ~1s/档，TM 一遍
≈ 几十 ms）。

sqrt/atan/ln/sin 节点：g'、g'' 按 §1.3 的解析形用栈上已有量计算
（如 atan：g' = 1/(1+f0²) 球算术；g'' 界 = 区间版 −2t/(1+t²)² 在 f 的
盒值域上求值——f 的盒值域即 ddf 同一遍里顺带的区间求值，或复用现有
eval_prog 的裸区间结果）。

### 2.3 驱动整合与证书 schema v3

驱动判定顺序（每叶）：**TM 判定先行**（loBound > 0 → 闭合，不再二分），
失败退现有裸区间 + disj + 二分路径。TM 只在 w 小于阈值时启用（宽盒上裸
区间本来就够，TM 的中心求值是浪费）；阈值自适应，不影响 soundness。

证书叶 JSON 扩展（**advisory only**——内核不信任，只做 stage-A 种子）：

```json
{"box": [...], "hit": "main",
 "tm": {"center": [{"num":..., "den":...}, ...],
        "rung_c": [2048, -64], "rung_h": [32, -20],
        "err_exp": -40}}
```

- `center`：TM 中心点（默认中点，可省略）；
- `rung_c`/`rung_h`：bb_arb 实测够用的中心/二阶精度档，给 stage-A 当起点
  （省阶梯搜索）；
- `err_exp`：余项界的数量级 hint（调试/对账用，可省）。

## 3. Lean 内核侧（最重的部分）

纪律（与 CertG 一致）：**内核用 dyadic 重算全部 Taylor 系数并验证余项界，
证书只提供参数种子**（rung 档、sqrt 尾数槽位等），语义桥仍靠
`evalReal` 忽略参数的 `rfl` 技巧（`CertG.lean:11-25`）。

### 3.1 分析核心定理（新数学，一次性）

**T1：盒上一阶 Taylor 余项界**。陈述草图：

```lean
/-- 线偏导：第 i 坐标方向的导数（对齐 Flyspeck `partial`，
    避开 iteratedFDeriv，全部走一元 deriv 的链式法则）。 -/
def lineDeriv (i : Fin n) (f : (Fin n → ℝ) → ℝ) (ρ : Fin n → ℝ) : ℝ :=
  deriv (fun t => f (Function.update ρ i t)) (ρ i)

/-- 盒上 C² 谓词（对齐 `diff2c_domain`）：每条坐标线限制在盒上线段上 C²，
    且 lineDeriv 自身关于各坐标仍可线导。由逐运算合成引理建立（T3）。 -/
def Diff2OnBox {n : ℕ} (box : Fin n → DInterval) (f : (Fin n → ℝ) → ℝ) : Prop

theorem taylor_bound_on_box {n : ℕ} {box : Fin n → DInterval}
    {f : (Fin n → ℝ) → ℝ} {y : Fin n → Dyadic} {w : Fin n → Dyadic}
    {dfB : Fin n → DInterval} {ddfB : Fin n → Fin n → DInterval} {err : Dyadic}
    (hC2 : Diff2OnBox box f)
    (hcell : ∀ i, (box i).mem (y i).toReal ∧ …max(yᵢ−loᵢ, hiᵢ−yᵢ) ≤ wᵢ…)
    (hdf : ∀ i, (dfB i).mem (lineDeriv i f (fun i => (y i).toReal)))
    (hddf : ∀ i j ρ, boxMem box ρ →
      (ddfB i j).mem (lineDeriv i (fun σ => lineDeriv j f σ) ρ))
    (herr : (½ : ℝ) * ∑ i, ∑ j, (w i).toReal * (w j).toReal *
      (ddfB i j).abs.hi.toReal ≤ err.toReal) :
    TaylorM.Valid ⟨y, w, ⟨…f(y) 的包围…⟩, dfB, err⟩ box f
```

**证明路线**（全部基于 Mathlib 现成件，v4.32.2 实测存在）：
固定 ρ，令 u = ρ − y，g(t) = f(y + t·u)（t ∈ [0,1]，线段 ⊂ 盒，凸性平凡）。
- g' = Σᵢ uᵢ·lineDeriv i f（仿射复合的链式法则，`HasFDerivAt.comp_hasDerivAt`
  族 + `HasDerivAt.sum`）；
- g'' = Σᵢⱼ uᵢuⱼ·（混合线二阶导）——再套一次同一链式法则；**不需要
  Schwarz**，全序对直接展开（T-D0）；
- `Mathlib.Analysis.Calculus.Taylor.taylor_mean_remainder_bound`
  （Taylor.lean:390，n=1、E=ℝ 实例化）：
  `|g(1) − g(0) − g'(0)| ≤ C·(1)/2!`，C = max|g''| ≤ Σᵢⱼ wᵢwⱼ·|ddfᵢⱼ 上界|。
- 所需 ContDiffOn 前提由 Diff2OnBox 逐运算合成引理供给（T3），
  g 的 C² 性 = f 的线限制 C² 性，`ContDiffOn.comp` + 仿射 map 的
  `ContDiff`（`contDiff_const`/`contDiff_id` 组合）。

**Mathlib 缺口盘点**（实测 v4.32.2）：

| 需要 | 现状 | 缺口处置 |
|---|---|---|
| 一元 Taylor 余项界 | `taylor_mean_remainder_bound`（Taylor.lean:390）✅ | 无 |
| 线限制 C² 的合成 | `ContDiffOn.comp` + 仿射 ContDiff ✅ | 无（体力活） |
| 各 trans 的 C² | `contDiff_sin`/`contDiff_cos`（Deriv.lean:326/364）、`contDiff_arctan`（ArctanDeriv.lean:95）、`contDiffOn_log`（Log/Deriv.lean:92）、`ContDiffOn.sqrt`（Sqrt.lean:160，需 ∀x∈s, f x ≠ 0）✅ | 无 |
| 各 trans 的导数值 | `Real.hasDerivAt_sin/cos/arctan/log/sqrt`（均实测存在；log/sqrt 需 x≠0）✅ | 无 |
| 线偏导 = fderiv 的桥 | 不需——lineDeriv 直接用一元 deriv 定义，链式法则走 HasDerivAt | 无 |
| **g'' 展开为 Σᵢⱼ uᵢuⱼ·混合偏导** | 无现成定理 | **自证**（~100-200 行：两次链式法则 + Finset.sum 展开；本设计最大单笔数学债） |
| **Diff2OnBox 逐运算合成**（对齐 `diff2c_domain_*_compose`） | 无 | 自证：+−× 用 `ContDiff.add/mul`；div/sqrt/log 用非零前提版；sin/cos/atan 全平面 | 

### 3.2 符号求导 AST（ddf 界的可计算化）

余项界需要 ∂²ᵢⱼf 的**盒上区间界**。内核不信任证书，必须自己算——
做法：IExpr 上加符号求导：

```lean
/-- 第 i 坐标偏导的表达式（trans 的导数全部回落到 IExpr 可表达形式：
    sin→cosK；atan→div(1, 1+t²)；ln→div(1,t)；sqrt→div(1, 2·sqrt t)；
    div/mul 走商/积法则；ite/abs 无导数 → 由 TMSafe 排除）。 -/
def IExpr.deriv {n : ℕ} : IExpr n → Fin n → Option (IExpr n)

/-- 求导 soundness：ρ 处导数表达式语义 = 线偏导。
    前提 TMSafe：子式在盒上满足各运算的可导条件（sqrt/div/ln 底非零、
    无 ite/abs）——内核 Bool 可检。 -/
theorem IExpr.deriv_sound {n : ℕ} {e : IExpr n} {i : Fin n} {e' : IExpr n}
    (h : e.deriv i = some e') {box : Fin n → DInterval}
    (hsafe : TMSafe e box = true) {ρ : Fin n → ℝ} (hρ : boxMem box ρ) :
    HasLineDerivAt i (e.evalReal) ρ (e'.evalReal ρ)
```

∂²ᵢⱼ = `(e.deriv j).bind (deriv i)` 的 eval——**但注意性能设计 T-D1**：
内核的 `evalTM` 不做"生成 deriv 表达式再分别 eval"（n² 个表达式各 eval
一遍 = O(n²)·prog 长度次 decide，对 83-sqrt 主 prog 是灾难）。而是**单遍
递归同时产出** (f(y) 界, ∂ᵢf(y) 界, ∂²ᵢⱼf 盒界)——与 C 侧 AD 同构：

```lean
/-- 单遍 Taylor 模型求值：递归返回三元组（中心值界、一阶导界、二阶导盒界），
    子项共享（与 C 侧 tm1_t 前向传播镜像）。Option：TMSafe 违例 → none。 -/
def evalTM {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (P : TMParams n) : Option (TaylorM n)

theorem evalTM_sound {n : ℕ} {e : IExpr n} {box} {P} {M : TaylorM n}
    (h : evalTM e box P = some M) : TaylorM.Valid M box (e.evalReal ρ 抽象)
```

deriv AST 仍存在（soundness 证明的语义载体），但 evalTM 的递归类直
接实现 §1.3 表——证明 evalTM_sound 时逐步引用 deriv_sound 与 T1/T3。
**这是"生成式求导 + 单遍求值"双层：语义层用 AST 归纳，计算层单遍共享，
中间用 deriv 表达式的 eval 相等性桥接。**

### 3.3 中心求值与 rung 的对接

f(y)、∂ᵢf(y) 是**点求值**（退化盒），精度由 trans 节点的 rung (N, out)
决定——现有 `IExpr.trans k e N out`（`Expr.lean:99`）与 FillParams 阶梯
机制原样复用：

- `TMParams n` = 中心 rung 集（逐 trans 节点 (N,out)，紧）+ Hessian rung
  集（粗，Hessian 只需数量级）+ sqrt 尾数槽位（同 CertG 现行）。
- evalReal 忽略全部参数 → `hsame : el.evalReal = e.evalReal` 仍是 `rfl`，
  BBTreeG 的语义桥机制不变。
- Hessian 盒界的 trans 求值走现有 `transOn`（区间版），中心点求值走
  退化盒上的同一入口——无需新 trans 代码。

### 3.4 证书结构整合

`CertG.lean`/`CertGD.lean` 各加一个叶构造器：

```lean
/-- Taylor 叶：表达式不变（hsame 无关），叶携带 TM 参数与内核判定。
    soundness 结论形状与 posLeaf 相同：0 < e.evalReal ρ。 -/
| taylorLeaf (box : Fin n → DInterval) (P : TMParams n)
    (hcert : checkPosTM e box P = true) : BBTreeG n e
```

`checkPosTM_sound`（由 evalTM_sound + T1 组装）给出
`0 < e.evalReal ρ`，与 `checkPos_sound`（`Expr.lean:364`）同形——
`bb_soundG`/`bb_sound_disj_g` 的 covers_point 存在性分解原样走通，
**顶层定理零改动**。

内核每叶成本 = 单遍 evalTM 的 decide：O(n²)·prog 节点数的 Int 算术 +
中心点 trans 求值（rung_c 档，~秒级，对照 wave2 §7 实测 1s/档）。
**TM 叶的 decide 比裸区间叶贵约 (1+n+n²) 倍，但换来的叶数降幅是
数量级的**（O(w²) vs O(w) 收敛阶）——bb_arb 侧自适应策略保证只在
裸区间失效的临界带付这个价。

## 4. 分阶段路线

| 阶段 | 内容 | 验收标准 | 工作量粗估 |
|---|---|---|---|
| **TM0** | 一元 pilot：n=1 时 T1 退化为直接套 `taylor_mean_remainder_bound`（无 g'' 展开债）；evalTM 只支持 +−× 与 sqrt；新文件 `CertTM.lean` 骨架 | `Expr.lean` 现存 sqrt pilot（`CertG.lean:135` exGExpr）改用 taylorLeaf 闭合 + 一个刻意临界的一元例（如 x²−2 在 √2 邻域，裸区间永不收敛，TM 2-3 层二分收敛）内核通过，`#print axioms` 仅标准三 | 3-4 天 |
| **TM1** | 多元纯代数：g'' 展开引理（T1 完全体）+ deriv AST 代数规则 + Diff2OnBox 代数合成 + evalTM 单遍（+−×÷） | BIXPCGW 失败叶集中**纯代数段**的 TM 判定通过率实测 ≥ 95%（stage-A 镜像跑，不进内核亦可先测）；对照现 plateau ~46-50% | 4-6 天（g'' 引理是主风险） |
| **TM2** | trans 合成：sqrt/atan/ln/sin 的 Diff2OnBox 合成引理 + evalTM 全节点 + TMParams rung 对接 FillParams 阶梯 | MKFKQWU 级 prep 案例：bb_arb TM 驱动下固有叶数从 ≥10⁹ 降到可发射量级（< 10⁶）；BIXPCGW 全量叶 TM+裸区间混合判定闭合 | 4-6 天 |
| **TM3** | bb_arb 驱动整合（§2.3）+ emit_lean schema v3 + CertG/GD taylorLeaf 量产 + stage-A/repair 适配 | 至少 1 个此前不可闭合案例端到端内核闭合（公理审计仅标准三）；已闭合案例回归零变动 | 3-5 天 |

**最小可行切片 = TM0**（一元 + 多项式 + sqrt，正是任务书建议的切法）：
它单独价值有限（案例都是多元的），但把 T1 的证明模式、CertTM 骨架、
taylorLeaf 机制全部跑通，TM1 只剩 g'' 展开一块硬骨头。

总计 ~2.5–4 周，风险集中在 TM1 的 g'' 展开引理。

## 5. 风险与开放问题

1. **CertG/GD 逐叶特化兼容**：taylorLeaf 不动 hsame 机制（表达式不变，
   参数仍被 evalReal 忽略），但 params schema 要再扩一档（每叶中心/Hessian
   两组 rung）；wave2 的 W2.5 记忆化（`runMainDisj` chunk 缓存）与 stage-A
   的 evalFill 手抄镜像（`wave2-disj-design.md` §8 坑：evalFillC/evalFill
   双侧同步）都要加 TM 镜像——**镜像分叉风险是该管道的已知事故多发点**，
   evalTM 必须在 Lean 侧单源生成（如现状的 evalFill 手抄模式不能再复制一遍，
   考虑直接让 bb_arb 读 Lean 生成的判定表，或接受 stage-B decide 兜底）。
2. **ite/hull 语义**：TM 要求盒上 C²，ite guard 边界破坏可微性。对策：
   TMSafe 排除含 ite/abs 的子式 → evalTM 返回 none → 该叶退裸区间
   （ufall hull 语义不变）。更细的方案（逐支 TM + hull 合并）明确不做：
   hull 后的模型不再是线性的，soundness 论证复杂度不值得。
   disj 的 varLt 支是精确盒判定，本就不需要 TM。
3. **rung 阶梯与 Taylor 阶正交**：Taylor 阶固定为 1（余项 O(w²) 已够收敛）；
   rung 只管 trans 求值精度。注意 err 的 Hessian 区间界部分**不随 rung
   改善**（它是固有 O(w²) 量），rung 只收紧 fB/dfB——stage-A 阶梯搜索
   逻辑要相应改：TM 叶 FAIL 时先降盒（二分），不是先升档。
4. **abs 节点**：非 C¹，TMSafe 直接排除（Flyspeck 有
   `m_taylor_abs_pos_compose` 按符号分支处理，我们暂不做——实测 hit 支
   abs 出现率低）。
5. **内核性能**：单遍 evalTM 是硬约束（见 T-D1）；若 decide 仍超预算，
   备选 = CertShards 分片粒度调小（现成机制）。中心 trans 求值在 N=2048
   档的 decide 成本已被 closed-atan 先例验证可行（wave2 §4）。
6. **g'' 展开引理**（T1 完全体）是全设计最大单笔数学债；若卡住，降级
   路径 = 逐维全微分 MVT 上界（|f(ρ)−f(y)| ≤ Σ wᵢ·sup|∂ᵢf|，仍 O(w)，
   无改善——**不可接受**），或外包该引理为多变量 MVT 的特化
   （`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` 二次应用，
   需 fderiv 层面的 Hessian 界桥接，工作量相当）。无便宜退路，TM1 排期
   留 buffer。
7. **prep 家族归一化**：prep 案例 x=y² 代入后多项式次数翻倍，Hessian 界
   变大，err 收紧变慢——TM2 验收的叶数指标若达不到 <10⁶，回退方案是
   域剖分（现状 16 条真残余的既定策略），TM 仍是 y 空间案例的主路径。

## 6. 明确不做

- 任意阶（>1）Taylor 模型 / arb_poly 高阶级数路径（Flyspeck 也未用，
  一阶+二阶余项足够；arb_poly 原语清单留档 §2.1 备将来单变量强化）。
- ite 支级 TM 合并、abs 符号分支 TM。
- Schwarz 对称性优化（T-D0 已绕过）。
- 不动现有已闭合案例与在跑的 549/Q/BIXPCGW 管线；TM 是新增叶类型，
  不替换 checkPos 路径。

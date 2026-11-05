# Euler 泛型立体角定理 测绘侦察（SCOUT）

> 车道：TSKAJXY_034 收编前置——全泛型 Euler 立体角锚 `p21k_euler_anchor`
> （PA21:10973，public def，w5 交付态 md5 `0a3959ab…`）的移植工程只读侦察。
> 基线：PA21 = tskajxy-w5 交付态（11,562 行）；HOL 正本 =
> `reference/flyspeck/text_formalization/`。交付：本文件、`DEP_MAP.tsv`、
> `WAVES.md`、`MD5SUMS`。方法：euler_main_theorem/euler_complement/
> euler_multivariate 三件全文通读 + merge_ineq 钩子逐行读 + 树内 W2a 特化
> （PA21:2069-3010）与 SphereKit/IneqClosureDefs def 面逐件对拍 + Mathlib
> v4.32.2 覆盖面实测 grep + 消费面 NEEDS 注记逐条对账。

## 0. 结论速览

1. **目标命题数学内容已精确定位，且只欠一条主链。** 锚 = HOL 两条的合并：
   `sol_x_sol_euler_x`（merge_ineq.hl:841，六前提，`sol_x = sol_euler_x`，
   即 Euler 四面体顶点立体角闭式）⊕ `sol_x_sol_x_sqrtdelta`（:1060，
   `sol_euler_x = √Δ · sol_euler_x_div_sqrtdelta`，atn2→matan 重标）。
   背书件 = `EULER_TRIANGLE`（euler_main_theorem.hl:514）：α1+α2+α3−π
   = π − 2·atn2(√Δ, 2p)。**不是** tan(Ω/2) 分母四项那个常见教科书形——
   Flyspeck 的形是"球面超 Sheets 和 = π − 2·atn2(√Δ, 2p)"，其中
   p = euler_p = √(x1x2x3) + √x1(x2+x3−x4)/2 + √x2(x1+x3−x5)/2 +
   √x3(x1+x2−x6)/2 = 树内 `eulerAX`（两形恒等，sol_x_sol_euler_x 证明体
   :899-916 逐项放电）。
2. **最小泛型形 = 三件全套，没有可裁剪部分。** 名义 4,572 行
   （521+811+3240）中 euler_multivariate.hl 一个证明
   `DERIVATIVE_WRT_A_Euler_lemma`（:351→文件尾 3240）独占 **2,889 行
   （63%）**；加 merge_ineq 钩子 ~200 行 + delta_x.hl 非共线件 ~80 +
   trig1 atn2 件 ~90，闭包 ≈ **4,940 HOL 行**。但这 63% 是 HOL Light
   导数 tactic 噪声，Mathlib（`deriv_arctan` + HasDerivAt + MeanValue 一族）
   压缩比 ~6-10×。
3. **真数学缺口只有一处：EULER_TRIANGLE 本体（单位盒导数恒等式）。**
   Mathlib 无：atan2（全库零命中）、立体角、球面三角（Girard/球面余弦
   零命中）、二面角（dihedral 零命中）、Cayley–Menger。树内已自补的：
   `atn2`（SphereKit.lean:37）、几何二面角 `dihV`（**已在仓**，
   Kepler/Geom/LuneVolume.lean:35，含 `dihV_eq_arccos_cos_azim`）。
   其余全部是 (b) 机械 / (c) 桥。
4. **误植检查：锚与全部系 def 零误植**（§5 明细 10 项逐一通过）。
   唯一实质记录项：锚是**强化合并**——HOL `sol_x_sol_x_sqrtdelta` 自带
   `0<x2 ∧ 0<x3` 前提，锚没有（ups>0 不蕴涵 x2>0），证明该步不能照抄
   HOL 的 SQRT bookkeeping；缓解处方已备（§5.2，8 前提备用锚）。
5. **消费面：Lean 侧硬消费者只有 TSKAJXY_034（PA21:4166-4168，树内唯一
   sorry）。** PA21:4093 的 "wave-2a NEEDS, sol_x_sol_euler_x chain" 注记
   **已过时**——3 胞件 `mi_gamma3f_gamma3f_x_div_sqrtdelta` 已在 W2a
   EULER lane 4 证毕（PA21:2955-2972）。二阶消费者：LocalAuto22
   （OCBICBY 局部移植）的 `euler_p_eulerA_x_p22`（:161 sorry）与本车道
   W4 的 euler_p↔eulerAX 平移件同构，可直接喂。TSKAJXY_034 收口还有
   第二债务 `bank_TSKAJXYGXSA` 符号翻转（W5 §1.2，SF 通道），与本车道
   独立但同闸。
6. **推荐路线 A（HOL 忠实：几何层 + 导数核），总工作量 890–1,940 Lean 行
   （中位 ~1,400），5 波，全链成功率 ~80-85%。** W-乘积 6 元推广（路线 B）
   无 HOL 背书、系数爆炸风险高，不推荐；x-空间纯解析（路线 C）可作
   W2 卡壳时的 spike 备选。W1-W4 落独立新文件可完全避开 PA21 文件闸门。

## 1. 目标命题精确化

### 1.1 锚（PA21:10973-10978，逐字）

```lean
def p21k_euler_anchor : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ,
    0 < x1 → 0 < upsX x1 x2 x6 → 0 < upsX x2 x3 x4 → 0 < upsX x1 x3 x5 →
    0 < eulerAX x1 x2 x3 x4 x5 x6 → 0 < deltaX x1 x2 x3 x4 x5 x6 →
    solX x1 x2 x3 x4 x5 x6 =
      Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) * solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6
```

### 1.2 HOL 双源

- `sol_x_sol_euler_x`（merge_ineq.hl:841-847）：`0<x1 ∧ 0<ups_x x1 x2 x6 ∧
  0<ups_x x2 x3 x4 ∧ 0<ups_x x1 x3 x5 ∧ 0<eulerA_x ∧ 0<delta_x ⇒
  sol_x x1..x6 = sol_euler_x x1..x6`。六前提与锚逐一同序同形。
- `sol_x_sol_x_sqrtdelta`（merge_ineq.hl:1060-1065）：`0<x1 ∧ 0<x2 ∧ 0<x3 ∧
  0<eulerA_x ∧ 0≤delta_x ⇒ sol_euler_x = sqrt(delta_x)·sol_euler_x_div_sqrtdelta`。

### 1.3 数学内容（对象定义坐标）

| 对象 | HOL 定义 | 树内 def | 内容 |
|---|---|---|---|
| delta_x | sphere.hl:86-91 | SphereKit.deltaX:46 | Cayley–Menger 型六元行列式 |
| ups_x | sphere.hl:122-124 | upsX:72 | 三边 Heron–Gram 主子式 −x1²−x2²−x6²+2Σ |
| dih_x | sphere.hl:153-157 | dihXf:96 | π/2 + atn2(√(4x1Δ), −Δ4)，沿棱 x1 的二面角 |
| sol_x | sphere.hl:181-184 | solX（IneqClosureDefs:379） | dih_x 三循环 − π = 顶点立体角（Harriot–Euler） |
| eulerA_x | sphere.hl:830-833 | eulerAX（PA21:192） | p 的 x-空间闭式（见 §0.1） |
| sol_euler_x | sphere.hl:735-739 | （无独立 def；按 atn2 式内联） | 2·atn2(2·eulerA_x, √Δ) |
| sol_euler_x_div_sqrtdelta | nonlin_def.hl:115-119 | solEulerXDivSqrtdelta（ICD:173） | matan(Δ/(4·a²))/a，a = eulerA_x |
| matan | sphere.hl:728-731 | matan（ICD:31） | arctan(√x)/√x 的解析延拓 |
| euler_p / dihV | sphere.hl:394-399 / 377 | eulerP 无 / **dihV 已在仓**（Geom/LuneVolume:35） | 几何形：距离混合积 / 投影二面角 |

故锚读作：**顶点立体角（球面超 Sheets 和）= √Δ · matan(Δ/(4p²))/p**，
即 Euler 立体角闭式的 x-空间 √Δ 形（Ω = 2·atn2(2p, √Δ) 的重标等价形；
p>0 分支下 2·atn2(2p,√Δ) = 2√Δ·matan(Δ/(4p²))/p，正是 W2a
`mi_p21e_soltrig`（PA21:~2671-2698）已证的 p/t 对偶）。

### 1.4 EULER_TRIANGLE（背书主定理，euler_main_theorem.hl:497-517）

```
!v0 v1 v2 v3. p = euler_p v0v1v2v3 → (x1..x6) = xlist → αi = dihV（过 v0 三棱）→
  0 < delta_x x1..x6 → α1 + α2 + α3 − π = π − 2·atn2(√Δ, 2·p)
```

证明 = `EULER_FORMULA_RESCALE`（euler_complement.hl:326-684：单位盒
(x1=x2=x3=1，即 ‖wi‖=1) 形经边重标推广到全形）+ `EULER_ANGLE_SUM_rescal`
（euler_main_theorem.hl:59-496：单位盒形本体，对点积变量求导 = 0 +
边界一点定值）；后者收尾消费 `DERIVATIVE_WRT_A_Euler_lemma`
（euler_multivariate.hl:351-3240）。这是 Flyspeck 的"实区间 bash"
= 现代语言下的"两侧导数相等 + 连通区间 + 一点重合"。

## 2. 真数学缺口 vs 可用件清单

### 2.1 Mathlib v4.32.2 实测（grep 在案）

**有**（直接可用）：
- `Real.arctan` 全族 + `Real.deriv_arctan`（Mathlib/Analysis/SpecialFunctions/
  Trigonometric/ArctanDeriv.lean:92、:135、:163）；
- 完整 `HasDerivAt`/`HasDerivWithinAt`/`DerivWithin` + MeanValue 一族
  （"区间上导数为 0 ⟹ 常值"是 Convex ℝ + 两三行 glue）；
- `Convex ℝ`（对应 HOL `is_realinterval`——euler_multivariate:93-108 的
  REAL_INTERVAL_Euler_lemma 三个平凡区间件在 Lean 里是 1-3 行 each）；
- `Matrix.det`/Gram 行列式（delta_x = 4·det² 桥的代数侧）；
- `EuclideanGeometry.angle`/`InnerProductGeometry.angle`（dihV 投影定义
  用的只是 `⬝ᵥ` + `dist`，LuneVolume 已铺好）。

**无**（零命中，需自建）：
- `Real.atan2`：Trigonometric/ 目录无 Arctan2 文件，全库 `atan2|arctan2`
  大小写不敏感零命中——**树内 `atn2`（SphereKit:37）已补位**，且 W2a
  已建 `mi_p21e_atn2`/`mi_p21e_matan`（PA21:2089/2108）；
- 立体角 / 球面三角（sphericalTriangle|Girard|sphericalExcess|solidAngle
  零命中）：锚的陈述面完全 x-空间化，**不需要**球面三角——这是本工程
  能纯解析完成的根本原因；
- 二面角（dihedral 全库零命中）：**树内 Geom/LuneVolume.dihV 已补位**；
- Cayley–Menger：自建（delta_x = 4·det² 一步 ring，见 DEP_MAP W2 行）。

### 2.2 真数学缺口（(d) 类）只有一件

`EULER_TRIANGLE` 本体（W3 波）：单位盒三 arctan 恒等式
（DERIVATIVE_WRT_C1:109-351 一元 + DERIVATIVE_WRT_A:351-3240 二元，
两侧导数 = 0 + 连通区间 + 一点定值）。HOL 已给出完整可行路线，
Mathlib 导数机器强于 HOL Light，风险是 2,889 行 tactic 忠实转录中的
边界取值细节，不是可行性。

### 2.3 (a) 已证清单（本会话核实，全部真定义、零 stub）

- 树内 9 个系 def 全部 verbatim 真身（§5 表）；W2a EULER lane 全套：
  `mi_p21eJ:2069`、`mi_p21e_atn2:2089`、`mi_p21e_matan:2108`、
  `mi_p21e_dih_atn:2164`、`mi_p21e_euler:2211`、`mi_p21e_solE:~2642`、
  `mi_p21e_soltrig:~2671`、`mi_p21e_dihalg:2699`、`mi_p21e_sol_bridge:2727`
  （(2,2,2)-钉死切片，PA21:2069-3010 共 ~941 行）；
- W5 泛型二面角桥 `p21k_dih_bridge:10950`（hol:920 全泛型）与 sol_x
  三循环 `p21k_solX_c:10908`；
- 几何层 `Geom.LuneVolume.arcV:31 / dihV:35 / dihV_eq_arccos_cos_azim`；
- gamma3f 3 胞 Euler 件 `mi_gamma3f_gamma3f_x_div_sqrtdelta:2972`（PROVED）。

## 3. 依赖链全图与行数对账（详见 DEP_MAP.tsv，33 行）

```
EULER_TRIANGLE (main:514, 4 行)
 ├─ EULER_FORMULA_RESCALE (comp:326-684, 359)      ← W4 重标归约
 │   ├─ DIHV_RESCALE_UNCHANGED (comp:92-313, 222)  ← W2
 │   ├─ SQRT 重标 (√Δ 乘 m·n·p, comp:~280-325)      ← W2
 │   └─ euler_after_rescale 代数恒等式 (comp:20-55, 36) ← W4
 └─ EULER_ANGLE_SUM_rescal (main:59-496, 437)      ← W4 装配
     ├─ DELTA_X_LT_0_COLLINEAR (delta_x.hl:149+, ~80)← W2（Δ>0 ⇒ 三非共线）
     │   └─ COMPUTE_DELTA_X:53 / DELTA_X_DET_3:125 （Δ = 4·det²）← W2
     └─ DERIVATIVE_WRT_A_Euler_lemma (mv:351-3240, 2889) ← W3 真数学核
         ├─ DERIVATIVE_WRT_C1 (mv:109-351, 242)        ← W3
         ├─ REDUCE_WITH_DIV (mv:32-55) + Harrison 导数 kit (mv:56-108) ← W3（Mathlib 直代）
         └─ EULER_TRIANGLE_REAL_INTERVAL (comp:685-811, 127) ← W3（Convex ℝ 件）

sol_x_sol_euler_x (merge:841-919, 79) ← W4 总装
 ├─ simplex_exists (merge:746-768, 23)              ← W2 六棱定 simplex
 ├─ DIHV_DIH_X (merge:~806-840) ← DIHV_EQ_DIH_Y (782-800) ← W2 几何桥
 └─ euler_p ↔ eulerAX 平移 (merge:899-916 放电)      ← W4
sol_x_sol_x_sqrtdelta (merge:1060-1108, 49)          ← W1（matan 重标）
matan_pos / pi2_sub_atn2 / ATN2_POS (merge:584-640)  ← W1（树内 atn2 kit 推广）
```

行数实测：三件 521+811+3240 = **4,572**；闭包合计 ≈ **4,940**（merge 钩子
~200 + delta_x.hl 取用 ~80 + trig1 atn2 件 ~90）。DELIVERY/W5 头注的
"~4.5k 行"与实测吻合。

## 4. 路线对比与工作量口径

- **口径校准**：BDXKHTW 侦察经验 = 装配型 HOL→Lean ×1.24-1.77
  （408-540 → 505-955）。本车道质量中心不同：69% 行数是导数 tactic 噪声
  （Mathlib 压缩 6-10×），但几何构造件（simplex_exists、dihV 桥、重标
  归约）HOL 短、Lean 是真活（×1.5-3）。分波估计见 WAVES.md：
  **W1 100-210 / W2 260-580 / W3 190-460 / W4 320-640 / W5 20-50，
  合计 890-1,940（中位 ~1,400）**。
- **路线 A（推荐）**：HOL 忠实，几何 + 导数。有完整背书、每步已知可行。
- **路线 B（W-乘积 6 元推广）**：W2a 钉死版 941 Lean 行已是 3 自由度 +
  sympy 预计算；6 自由度的 W-乘积恒等式系数爆炸（钉死版多项式已近百项）
  且无 HOL 背书（Flyspeck 泛型不走此路）→ 不推荐。若坚持，先做 ≤200 行
  可行性探针（generic (E1,E2,E3)-积多项式的 sympy 项数实测）再立项。
- **路线 C（x-空间纯解析 spike）**：对 x1 求导、绕开几何层（省 W2）。
  两个新难点：{x1 : Δ>0} 区间连通性（x1 的三次式符号分析）+ 边界极限
  （Δ→0 时两侧 →0 的 dih 极限）。估 400-900 行。仅当 W2 卡壳时启用。

## 5. 陈述误植检查（零容忍明细，10 项全过）

### 5.1 逐件对拍表

| # | 树内件（坐标） | HOL 件（坐标） | 判定 |
|---|---|---|---|
| 1 | `p21k_euler_anchor` 六前提序（PA21:10974-10976） | merge:842-846 | **同序同形，无误植** |
| 2 | 锚结论 √Δ·solEuler 形（:10977-10978） | merge:847 ⊕ :1060-1065 合并 | **一致**（强化合并见 5.2） |
| 3 | `solEulerXDivSqrtdelta`（ICD:173-177） | nonlin_def:115-119 | **逐项一致**（matan(Δ/(4a²))/a，a 三因子 + 三修正项） |
| 4 | `solEuler246/345/156`（ICD:191-201）= rotate4/5/6 | nonlin_def:121-128 | **一致** |
| 5 | `eulerAX`（PA21:192-197） | sphere.hl:830-833 | **逐项一致** |
| 6 | `solX`（ICD:379-382）三循环 | sphere.hl:181-184 | **一致**（dih_x(x1..) + (x2,x3,x1,x5,x6,x4) + (x3,x1,x2,x6,x4,x5) − π） |
| 7 | `dihXf`（SphereKit:96-99） | sphere.hl:153-157 | **一致**（π/2 + atn2(√(4x1Δ), −Δ4)） |
| 8 | `matan`（ICD:31-36） | sphere.hl:728-731 | **一致**（三分支含 0 处赋 1） |
| 9 | `deltaX/upsX/deltaX4`（SphereKit:46/72/78） | sphere.hl:86-91/122-124/104-108 | **逐项一致** |
| 10 | W2a `mi_p21e_euler`（PA21:2211-2243） | （无逐一 HOL 对应） | 自洽形；编译 + 消费背书（见 5.3） |

### 5.2 唯一实质记录项（非误植，是强化合并的前提差）

HOL `sol_x_sol_x_sqrtdelta` 有 `0<x2 ∧ 0<x3` 前提（sqrt 分解
bookkeeping 用），锚没有；`upsX x1 x2 x6 > 0 ∧ upsX x2 x3 x4 > 0`
**不**蕴涵 x2 > 0。因此锚的证明不能在该步直接调 HOL 语句的转录件，
需在锚前提集下重走（delta=0 支 + matan_pos 支）。**缓解处方**：若卡死，
改立备用锚 `p21k_euler_anchor8`（加 `0<x2 → 0<x3 →` 两前提）——W5 消费位
`p21k_gamma4fgcy_div_sqrtdelta`（:11016）本就有 `h1..h6` 全正，8 前提锚
照样接线，收口配方不变。**建议 W1 直接按 8 前提形式开工，再补 6 前提
强化版**（把"强化"本身变成一个 20-40 行的独立小件，隔离风险）。

### 5.3 W2a 特化的定位说明

`mi_p21e_euler` 是 **(u,v,w,2,2,2)-钉死的 EULER_TRIANGLE**：三个
`π/2 − arctan(Ei/bi)` 和 − π = π − 2·arctan(X/t)。它与泛型锚的关系是
"3 胞切片已清、6 元全无"（W5 头注 :10797-10810 原话），其 X/t 恰为钉死形
下 `solEulerXDivSqrtdelta` 的 let-`a` 的 2 倍（`mi_p21e_solE` docstring
:2640-2646 原话"the let-bound `a` is `X/2`"）——两条内证一致，无误植。

## 6. 消费面

```
p21k_euler_anchor 真证明 (本车道 hE)
        │
        ▼
p21k_cell4_from_ineq_of_euler (PA21:11539) ──► TSKAJXY_034 翻除 (PA21:4166-4168, 树内唯一 sorry)
        │                                       （还需 hg: p21k_glsa_correct 真证明 = 第二债务
        │                                         bank_TSKAJXYGXSA 符号翻转, SF 通道独立立项）
        ▼ (W4 副产物)
euler_p ↔ eulerAX 平移件 ──► LocalAuto22.euler_p_eulerA_x_p22 (:161 sorry, OCBICBY 车道)
```

- **硬消费（Lean）**：TSKAJXY_034 一件。收口配方已验证（W5 交付书 §5）：
  `exact p21j_tskajxy034 hyp (p21k_cell4_from_ineq_of_euler hE hg hyp.2.2)`。
- **过时注记**：PA21:4089-4093（`cell3_from_ineq_thm` docstring）"track 7
  的 `mi_gamma3f_gamma3f_x_div_sqrtdelta`（wave-2a NEEDS, sol_x_sol_euler_x
  chain）"——该件 **已 PROVED**（PA21:2972，EULER lane 4，docstring
  :2955-2971 自证）。建议编排者顺手改注。
- **二阶消费**：LocalAuto22（OCBICBY 局部移植）`eulerP_p22:114` /
  `eulerAX_p22:118`（opaque 桩）+ `euler_p_eulerA_x_p22:161-165`（sorry）；
  HOL 侧 OCBICBY.hl:134 直接消费 EULER_TRIANGLE。OCBICBY 全闭包另有
  EAR_SOL_NN/empty_6T1 等自有巨案债务，非本车道义务，但 W4 平移件是白送。
- **Flyspeck 侧消费者（记录）**：EULER_TRIANGLE ← merge:854 + OCBICBY:134；
  sol_x_sol_euler_x ← merge:1210（gamma4fgcy 链）、merge:3049（gamma3f 链）、
  terminal.hl:72（sol_x_nn 立体角正性）、sharp.hl:356（对比锐界）。
  Lean 侧目前只有 gamma4fgcy 链有树内对应；terminal/sharp 的 sol_x_nn/
  锐界件是潜在未来消费，不在本车道范围。

## 7. 给编排者的笔记

1. **文件闸门**：W1-W4 落**独立新文件**（建议 `Kepler/Text/EulerSolidAngle.lean`
   或分 W1-W4 两文件；import SphereKit + IneqClosureDefs + Geom.LuneVolume，
   Geom 导入先例 = ConformingDefs:58 / ConicCapVolume:53-56），与 PA21
   零闸门冲突。仅 W5（锚翻转接线）触碰 PA21——与在飞收编波串行。
   严禁新文件 import PA21 取 W2a 件（后续 PA21 要反向消费锚件，成环）；
   W2a 桥件按 §0' bridge-copy 惯例复制（~150-250 行 kit）或先抽公共件
   （编排者决策）。
2. **邻产导数 kit**：LocalAuto1/LocalAuto22 stratum 有 derivedForm
   一元导数 kit（delta_x/delta_x4/dih_x 链式法则；LA22 头注 :4-8）。
   W3 开工前普查一次可省 50-150 行；注意它们在 LocalAuto1 闭包内、
   不在 SphereKit 侧，取用方式同上条。
3. **两债务同闸**：TSKAJXY_034 收口需 hE（本车道）+ hg（`bank_TSKAJXYGXSA`
   符号修复，SF 通道）齐备；本报告只测绘 hE。编排排程应把 SF 修复波与
   本车道 W5 并列。
4. **行号漂移**：本报告全部行号基于 w5 交付态 PA21（md5
   `0a3959ab84c18798cd7b85856c6eff94`，11,562 行）；HOL 行号基于
   reference/flyspeck 主仓现态（md5 见 MD5SUMS）。
5. **勿引名单**：`upsX_p6`（LocalAuto6:64，另一个 packing_defs ups_x）；
   PA18/PA20 的 deltaX/deltaXf 孪生（用 SphereKit 正典名）；
   LocalAuto22 的 `eulerAX_p22`（opaque 桩，勿当真定义消费——等 W4 平移件
   落地后回头喂它）。

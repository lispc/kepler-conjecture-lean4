# b1-family-map — B1 桥族（dihY，17 条 rest）族画像 + 公共核清单

> lane b1bridge-w1。基线主仓 HEAD `b8085328`（任务书基线 3e5039c1 之后）。
> 口径：**一切陈述形状以 B0 校准批 + A2 落库后签名为准**；本文及 drafts/ 全部
> 是内容预备草案，未编译（铁律 4）。
> 上游：nli-rest-params.tsv（57 rest 参数表）、glue-slots.md（S3 槽解剖/A1 签名）、
> a2-rest9-w1/Glue.lean（B1 桥先例，在飞）、GiFactorization.lean（实分析样板，
> untracked scout 件）、17 条 case JSON（盘上，`pipeline/interval/out/cases/`）。

## 0. 一句话总结

B1 族的 S3 公共核是**代数核**（A2 的 `iteTree_eq_atn2` 逐字复用 + 一个 dihY
定义锚 rfl-引理 + 方向收尾 linarith/norm_num），不是实分析核：17 条 case JSON
的 prog 解剖与数值验证（精确有理常数指纹 + 65–161 点零差）表明关键路径上
**没有一条**需要单调性/导数/端点极值论证；GiFactorization 的
`strictMonoOn_rad2X_y1` + `deriv_*` 系登记为储备核（当前 0 条消费）。

## 1. 族界定（对账 glue-slots「B1 dihY 直用 17 条」）

B1 族 = 认证支（case prog）**含显式 dihY 项**的 rest ∪ 因 gamma23/gamma4f
内部 dihY 原子而与 B1 核耦合的 rest。逐条对账：

- TSV 显式标 B1 的 14 条 + 「同上」链 2 条（QITNPEA6206775865、
  QITNPEA5653753305，与 3848804089 同模板）+ **TEWNSCJ**（TSV 记 B4+B2，
  但其认证支第一项 `gamma23Full8X(h0cut y1) > aSpine5 + bSpine5·dihY` 含
  显式 dihY 项）= **17 条** ✓。

## 2. 方法与证据链（零构建，全部只读）

1. case JSON prog = RPN 指令 + 3 层嵌套 ite（cond/then/else），`evalReal`
   语义 = Expr.lean:165 方程（ite 按 `< 0`、`.trans .arctanK` → `Real.arctan`、
   `.sqrt` 去证书化——证书 mantissa 不进 evalReal，与 A2 桥一致）。
2. **atan 算子计数指纹**：显式 `±c·dihY` 项 ≡ 恰好 +7 atan（ite 树 7 个
   arctan 节点）；纯 dihY prog = 7；gamma4fgcy 基座 = 143；Keep135 基座 =
   114；Full8X 基座 = 221。四组互证：3848804089 系 150=143+7；
   BIXPCGW7274157868a 143=143+0；TEWNSCJ 228=221+7；TXQTPVC 221=221+0。
3. **数值恒等验证**（Python 精确移植 deltaX/deltaX4/atn2/dihY/solY/volY/
   vol4f/lmfun，盒上 65 角点+中心 / 161 点）：
   - 6 条纯 dihY：prog ≡ ±(dihY − c)，**65 点零差**（c = 39/25、23/10、23/10、
     14/5、303/500、19/25，与 prog 常数表逐一相符）。
   - B3+B1 抽验 2 条（3848804089、5653753305）：prog ≡ gamma4fgcy(y,lmfun) ±
     c0 ± c1·dihY，**161 点零差**。
4. prog 常数表交叉核对：aSpine5 = 112061/2000000 = 0.0560305、
   bSpine5 = −445813/10000000 = −0.0445813（prog 记 +445813/10⁷，符号由
   bank 的负系数吸收）、betaBumpLb = −1/200、h0cut 的 h0 = 63/50、
   gamma23Full8X 修正系数 1/125 = 0.008——全部吻合。
5. **disj 案的 prog 只编码第一比较支**（case JSON notes：「核心为 K 路析取：
   prog 取第一比较项，其余入 disj」）。由此：TXQTPVC / BIXPCGW7274157868a /
   QITNPEAv24003532128 三条的**认证支无显式 dihY**（TSV 的 B1 标签是保守
   记账）；它们的 S3 分别归 B4/B3/B2 车道，B1 原子仅作为 gamma 基座的
   内部结构被复用。

## 3. 17 条族画像

通用盒端点 dyadic（除注明外每条相同）：dim0（hminus 槽）
`[322122547·2⁻²⁸, 348966093·2⁻²⁸]`；dim1（y1）
`[2576980377·2⁻³⁰, 711568707·2⁻²⁸]`；2 = `⟨1,1⟩`；2hmin 外扩 = `2791728743·2⁻³⁰`
（上）/`2576980377·2⁻³⁰`（下，=2.4）；2hplus 外扩 = `711568707·2⁻²⁸`（上）/
`2846274827·2⁻³⁰`（下）；√8 外扩 = `759250125·2⁻²⁸`；2.1 = `2254857831·2⁻³⁰`。

| # | stub | Assembly 桩 | PA21 bank | case JSON（态） | op / 认证支 | S3 桥类 | 阈值/系数 | S1 端点桥 |
|---|---|---|---|---|---|---|---|---|
| 1 | nliRestQITNPEA3725403817 | :739 | PA21:498 | QITNPEA_3725403817（在库 CQITNPEAx3725403817） | `<`：39/25 − dihY | **B1 纯**（A2 已写） | 1.56 | 2.1 dyadic（A2 已解） |
| 2 | nliRestBIXPCGW1738910218a2 | :956 | PA21:741 | BIXPCGW_1738910218_a2 | `<`：23/10 − dihY | **B1 纯** | 2.3 | √8 + 2hplus 上（y4） |
| 3 | nliRestBIXPCGW7080972881a2 | :962 | PA21:750 | BIXPCGW_7080972881_a2 | `<`：23/10 − dihY | **B1 纯** | 2.3 | √8 + 2hmin 下（y2） |
| 4 | nliRestBIXPCGW6652007036a2 | :968 | PA21:759 | BIXPCGW_6652007036_a2 | `<`：14/5 − dihY | **B1 纯** | 2.8 | √8（A1 盒） |
| 5 | nliRestGCKBQEA | :1130 | PA21:920 | GCKBQEA | `>`：dihY − 303/500 | **B1 纯（下界向）** | 0.606 | √8（A1 盒） |
| 6 | nliRestRQWUDDU | :1136 | PA21:928 | RQWUDDU | disj3 支1：dihY − 19/25 | **B1 纯** | 0.76 | √8（A1 盒） |
| 7 | nliRestQITNPEA3848804089 | :778 | PA21:563 | QITNPEA_3848804089 | `>`：gamma4fgcy − 0.161517 + 0.119482·dihY | **B3+B1** 单目标 | — | 免 |
| 8 | nliRestQITNPEA5814748276 | :784 | PA21:572 | QITNPEA_5814748276 | `>`：gamma4fgcy − 0.00127562 + 0.00522841·dihY | **B3+B1** 单目标 | — | 免 |
| 9 | nliRestQITNPEA6206775865 | :790 | PA21:581 | QITNPEA_6206775865 | `>`：gamma4fgcy + 0.0142852 − 0.00609451·dihY | **B3+B1** 单目标 | — | 免 |
| 10 | nliRestQITNPEA5653753305 | :796 | PA21:591 | QITNPEA_5653753305 | `>`：gamma4fgcy + 0.0659 − 0.042·dihY | **B3+B1** 单目标 | — | 免 |
| 11 | nliRestQITNPEA2134082733 | :895 | PA21:648 | QITNPEA_2134082733 | disj2 支1：gamma4fgcy/2 + betaBumpLb − 0.213849 + 0.119482·dihY | **B3+B1** | betaBumpLb=−1/200 | √8 + 2hmin 下（y4） |
| 12 | nliRestQITNPEA9939613598 | :938 | PA21:711 | QITNPEA_9939613598 | disj2 支1：gamma4fgcy − 0.00457511 − 0.00609451·dihY | **B3+B1** | — | √8 + 2hplus 下（y4） |
| 13 | nliRestTEWNSCJ | :759 | PA21:531 | TEWNSCJ | disj4 支1：gamma23Full8X(h0cut y1) − aSpine5 − bSpine5·dihY | **B4+B1** | spine 常数 | √8 |
| 14 | nliRestPEMKWU | :752 | PA21:518 | PEMKWKU.json（id=PEMKWU 一致；文件名漂移按 TSV 核对项） | disj6 支1：gamma23Keep135X(h0cut y1) − aSpine5 − bSpine5·dihY | **B4+B1** | spine 常数 | √8 |
| 15 | nliRestTXQTPVC | :731 | PA21:485 | TXQTPVC | disj6 支1：gamma23Full8X(h0cut y1) − 3·0.0057（**无显式 dihY**，atan=221=221+0） | B4（B1 仅内部原子） | — | √8 |
| 16 | nliRestBIXPCGW7274157868a | :944 | PA21:722 | BIXPCGW_7274157868_a | disj2 支1：gamma4fgcy − 0.0057（**无显式 dihY**，atan=143=143+0） | B3（B1 仅内部原子） | — | √8 + 2hplus 下（y4） |
| 17 | nliRestQITNPEAv24003532128 | :746 | PA21:506 | QITNPEAv2_4003532128 | disj7 支1：eta_y(y1,y2,y6)² − (67/50)²（**atan=0，零 dihY**） | B2（与 B1 无关） | 1.34 | √8 |

**B1 核真实消费计数：14 条**（#1-#14）；#15/#16 仅经 gamma 基座间接复用
（其 S3 归 B4/B3）；#17 与 B1 无关（TSV 保守标签）。

桩陈述（bank_*，PA21）形全部为 `∀ y1..y6 : ℝ, <12 hyp> → <goal>`；goal 逐条
见 §3 表与 PA21 原文，S5 方向：#5/#7-#12 为 `dihY > c` / `gamma…±c·dihY > 0`
（prog = 数学式本身），#1-#4/#6/#13/#14 为 `dihY < c` 型（prog = c − dihY 或
spine − bSpine5·dihY），#15-#17 的 S5 = Or.inl 投影。

## 4. 公共核清单（drafts/B1Common.lean）

每条：陈述草案 + 证明思路 + 工具 + 消费计数。**K0-K3 是关键路径核（代数），
K4/K5 是储备核（实分析，当前 0 消费）。**

### K0 π 锚 `four_arctan_one`
- 陈述：`(4 : ℝ) * Real.arctan 1 = Real.pi`
- 思路：`rw [Real.arctan_one]; ring`（A2 Glue.lean:79 逐字）。
- 工具：Mathlib `Real.arctan_one`。
- 消费：全部 17 条（经 K1/K2）。

### K1 ite 树恒等 `iteTree_eq_atn2 (A S : ℝ) : … = atn2 S (-A)`
- 陈述：A2 Glue.lean:73-101 **逐字**（发射 ite 树的 3 层分支 if-then-else
  = SphereKit `atn2` 定义分支，`4·arctan 1 = π` 由 K0）。
- 思路：`unfold atn2; split; … rw [if_pos/if_neg, hpi]`——对任意 A S 通用，
  不依赖具体 rest（**这就是族桥「一次性」的本体**）。
- 工具：`split`/`if_pos`/`if_neg` + K0。
- 消费：14 条直接消费（每条的 dihY 原子各一次 rw）；#15/#16 经 B4/B3 间接。
- 风险：若某条发射树分支结构与 A2 版不同（emit_lean.py 版本漂移），需按
  新树重证同构引理——发射后逐条核对 prog 前 8 指令即可拦截。

### K2 dihY 定义锚 `atn2_atom_eq_dihY`
- 陈述：`Real.pi / 2 + atn2 (Real.sqrt (4 * y1² * deltaX (y1²,…))) (-(deltaX4 (y1²,…)))
  = dihY y1 y2 y3 y4 y5 y6`（y1..y6 全自由）。
- 思路：`dihY ≡ dihXf(y1²,…)` 且 `dihXf ≡ π/2 + atn2 (√(4·x1·deltaX)) (−deltaX4)`
  （SphereKit:96-104），期望 `rfl` 或 `by unfold dihY dihXf; rfl`（GiFactorization
  的 pinning-example 风格，参其 `dX4 = Kepler.Text.deltaX4` pin）。
- 工具：`rfl`（definitional）。
- 消费：14 条（显式原子 → dihY）；gamma 基座内部原子同样按变元置换实例化。
- 意义：**B3/B4 车道的桥也以它收口**（gamma4fgcy 的 vol4f 显式含 6 个
  `f(yi/2)·dihY(置换)` 项、solY 含 3 个；gamma23Full8X 修正项含 dihXf 原子）
  ——K1+K2 是全 nli rest 波的公共尾件，不止 B1 族。

### K3 方向收尾微件
- `dihY_lt_of_pos (c d : ℝ) (h : 0 < c - d) : d < c`（linarith）；
  `dihY_gt_of_pos (c d : ℝ) (h : 0 < d - c) : c < d`（linarith）；
  阈值十进制转换 `example : (23:ℝ)/10 = 2.3 := by norm_num`（每条 c 一个，
  23/10、14/5、303/500、19/25、39/25、57/10000、67/50）。
- 消费：14 条的 S5。

### K4（储备）K1/S1 常数桥提升
- `sqrt8_le_dy : Real.sqrt 8 ≤ Dyadic.toReal ⟨759250125, -28⟩`——A1 S1 √8 桥
  从 have 块提升为族级引理（同 5 行，`rw [Dyadic.toReal_def]; norm_num;
  nlinarith [Real.sq_sqrt …, Real.sqrt_nonneg 8]`）。
- 2hplus 上/下桥、2hmin 下桥（`mi_hminus_prop` 组件 + hplus 定义 + norm_num
  + linarith；期望战术标注，见 B1Common 草案内 sorry 注记）。
- 消费：S1 需桥的 11 条（#1 用 2.1 桥 A2 已解）。

### K5（储备核，GiFactorization 风格，**当前 17 条 0 消费**）
- `deriv_rad2Xcomp_y1` / `strictMonoOn_rad2X_y1`（GiFactorization.lean:304/:338，
  已证在库-untracked）：rad2X 对 y1 的导数符号 → 盒上端点极值。
- **为什么 B1 用不上**：B1 的 S3 是恒等式（prog ≡ 数学式，逐点零差验证），
  不是界放缩；单调性论证只在「cert prog 用单调包络替代 dihY 本体」的场景
  才出场——17 条 prog 数据表明未发生。rad2X<2/rad2X>2 支（#6/#7 支2 等）
  走 B0 simp-only 通道，不走向导数。
- 保留场景：若 B0 校准批发现发射器对 rad2X 支生成的是单调包络而非直译，
  K5 立即启用（MKFKQWUhalfwt 首例即校准点）。
- Mathlib 工具：`strictMonoOn_of_deriv_pos`、`deriv_div`、`deriv_comp`、
  `HasDerivAt` 系（GiFactorization 已示范全链）。

## 5. 与 GlueTemplate 槽位的对齐（A1 签名，待 B0 校准）

- S0/S4 恒同构（glue-slots §2：57/57）——草案沿用 A2 具名前提槽形
  （`_pos` 作显式 hypothesis），落库时一行代入 `C<NAME>_pos`。
- S1：本族 11 条需桥（§3 表），6 条免/已解。
- S2：机器件；17 条证书盒端点 dyadic 字面量已全部导出（§3 通用端点 + 各
  drafts 文件内 S2 块）。
- S3：**本车道交付物**——14 条 = K0+K1+K2 + 每条 dsimp/simp-only 展开
  （未编译风险：simp 集合需以真实发射文件名/精度节点校准）；3 条无 S3
  dihY 内容（归 B2/B3/B4）。
- S5：#5/#7-#12 单目标 linarith/norm_num；#6/#13/#14/#15/#16/#17 disj 投影
  Or.inl（发射器已选第一支）。

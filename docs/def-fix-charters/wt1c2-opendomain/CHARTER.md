# DEF-FIX 章程 · `TaylorSecond.Wt1C2Data.box` 数字界零承重 + 冻结叶合同不可居住（续1476 立案）

立案：2026-11-24。立案人：编排者。触发：`wt1-taylor-leaf-w1` 车道按工单止损条款上报
（「LeafContract 形态 vs 实际 Taylor 数据错配 = 规格问题走 SF/DEF-FIX」），编排者对
`13dee7c8` 冻结源码亲验后定案。**待用户批；批前不动任何 base 文件。**

---

## 1. 缺陷（编排者亲验，源码级）

- `LeafContract.lean:11` 冻结 `selectedLo = ![4927/2000, 2, 709528000001/320000000000]`：
  x0 下沿 = 4927/2000 **恰等于** `Wt1C2Data.box` 的 x0 下界 2.4635；x1 下沿 = 2 **恰等于**
  x1 下界 2。`selectedBox = Box selectedLo selectedHi` 是 Icc 闭盒（含面点、非空）。
- `SelectedLeafEvidence U` 要求 `c2data : Wt1C2Data U`（含 `IsOpen U` +
  `box : ∀ x ∈ U, 2.4635 ≤ x 0 ∧ … ∧ (2:ℝ) ≤ x 1 ∧ …`）与
  `subset : ∀ x ∈ selectedBox, x ∈ U`。
- **不可居住证明**：任取 U 满足两字段，取面点 p = selectedLo ∈ selectedBox ⇒ p ∈ U；
  U 开 ⇒ 存球 B(p,r) ⊆ U；取 q ∈ B 使 q 0 = 2.4635 − r/2 ⇒ q ∈ U 但违反 box。
  ∎ 故 `SelectedLeafEvidence U` 对一切 U 为空，两个 gated 定理
  （`LeafContract.lean:67/78`）只能空洞成立——证书义务按冻结形态**不可满足**。
- **架构级影响（Phase B 主线）**：任何覆盖 wt1 闭域的盒分解必有贴域面叶；
  m4=1 区 f1 终端 117 个中仅 8 个内叶（y5lo>2 ∧ y6lo>2 严格，车道实测）——
  **贴面叶占比 ~93%**。不修则 597 终端计划在绝大多数叶上无法构造 evidence。

## 2. 承重分析（数字界为何可拆）

`Wt1C2Data.box` 的六个数字界对两个消费者**全部不承重**：

| 消费者 | 实际需要 | 数字界作用 |
|---|---|---|
| `contDiffAt_w1F3_of_data`（Wt1C2.lean:131） | `w1aF_eq_w1FexOpen3` 的证明只用 `0 ≤ x0 ∧ 0 < x1 ∧ 0 ≤ x2` + `cut`（Wt1C2.lean:95–97）；matan C² 链用 `t_pos/g_pos/area_ne/d4_ne` 字段（已是独立点条件） | 无 |
| `partial2_w1F3_eq_w1F2_of_data`（:145） | `w1aF_hasDerivAt_y5_box` 只是六界→`w1aF_hasDerivAt_y5` 15 条正性/非零条件的转译包装（Wt1TowerDomain:357，`linarith`+`w1a*_pos`）；而 `w1aF_hasDerivAt_y5`（Wt1TowerDeriv:1529）**本身就吃正性/非零**，与 `Wt1C2Data` 字段一一对应 | 无 |

数字界的真正职责（区间 payload 只在具体盒上有效）由 jet 字段 + `value_eq/first_eq/second_eq`
承担，不属于 C² 定义域结构。六界是**便利驱动的过度约束**（当时直接适配了六界签名的
现成引理）。

## 3. 修复（最小面）

1. **additive**：`w1aF_eq_w1FexOpen3` 增正性版变体（六界版零改动；该引理无外部消费者）。
2. **DEF-FIX** `Wt1C2Data.box`：`∀ x ∈ U, (0:ℝ) ≤ x 0 ∧ 0 < x 1 ∧ 0 ≤ x 2`
   （正性开条件；闭 wt1 盒含于 {x0>0, x1>0, x2>0} 的内部，贴面叶的 U 可向外扩 ε）。
3. 两个消费证明改从 data 字段取非零/正性条件（`w1aF_hasDerivAt_y5` 直供，
   绕开 `_box` 包装）。
4. **LeafContract 常量零改动**（SF 不需要）：selectedLo/Hi 与全部 payload 冻结不动；
   `U` 选显式有理开盒 ⊇ selectedBox + 窄余量（仅 x0/x1 触面方向外扩，如
   x0 下沿 −1/10⁶、x1 下沿 −1/10⁶；x2 与各上沿留在数字界内不外扩）。
   12 条件（area_ne/d4_ne/t_pos/g_pos on U）在窄余量上的证明 = evidence 构造义务
   （显式界 nlinarith 直推，不复用六界引理——`w1aA_pos` 的 hthird 步真用
   `y4 ≥ 2.4635`/`y6 ≤ 2.46352`，盒外窄条必须独立小证明）。

## 4. 验收

- 编排者三件套（模块 RC=0 + 岛协议 + 亲跑 `#print axioms`）。
- 冻结 gated 定理与全部常量 `git diff` = 0；`Wt1TowerDeriv`/`Wt1TowerDomain` 零改动
  （新变体 additive 除外）。
- **构造出第一个 inhabited `SelectedLeafEvidence`**（用 ①–③ 修复面 + 显式 U），
  gated 定理以**非空前提**给出 `w1F2 ≤ −101749/8000000`——这是修复成立的唯一内容级
  验收，空洞 `#print axioms` 不算数。
- 根面复验 589 同集。

## 5. 影响面与风险

- 爆炸半径：`Wt1C2Data`/`SelectedLeafEvidence`/`selectedLo` 仅出现于
  `TaylorSecond/Wt1C2.lean` + `LeafContract.lean`（rg 证实，零外部消费者；
  两文件均为 13dee7c8 base 内部）。
- 风险：窄余量上的 12 条件证明若个别失手（某正性在盒外窄条真破），缩小该方向 ε
  重试；若 x0 下界 2.4635 处某条件在**任意** ε 下都破（即数学上不延拓），停手上报，
  退回 SF 通道改选内叶冻结。
- 工时估计：0.5–1 个 lean 车道日（12 条件 × nlinarith + 两证明改线）。

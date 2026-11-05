# FCHKUGT 波次计划（WAVES）

> 配套 SCOUT.md §4。行数区间 = 低估–高估（×1.5–3 折算，噪声件已按池 B 经验收窄）。
> 全程无 (d) 真数学缺口；风险栏只列工期/装配/政策风险。

| 波 | 文件:位置 | 内容 | HOL行 | 估行数 | 前置 | 风险 | 成功率 |
|---|---|---|---|---|---|---|---|
| W1 | PA18 :5334(FUEIMOV_K) + :5342(MCELL4_EXTREME_POINT) | FUEIMOV_K：AJRIPQN(PA17:931,闭包内)接线 + CC_CELL_NOT_NULLSET + barV(cc_uh)；MCELL4_EXTREME_POINT：FUEIMOV_K + CC_CELL_CONVEX_HULL_INJ + SET_OF_LIST_CC_UH 三件装配 | 39 | 30–90 | **无（立即可开，不等 BG）**；开工动作 = 首建 `#print axioms AJRIPQN` 实测标准-三 | 低（纯装配）；政策风险 = axiom 实测若出 sorryAx 需编排者裁决落库口径 | ~90% |
| W2 | PA18 :5376(MXI_NOT_IN_V) + :5385(MCELL_V_INTER_EXTREME) + :5392(MCELL_EXTREME_DIFF_V) | MXI kit 三件：MXI_IN_VORONOI_LIST 供点 + packing 球分离 + sqrt2<2 算术 + 两条集合论推论 | 107 | 100–250 | 无（与 W1 并行） | 低-中（packing 定义展开 + 实数算术；BARV 微件 2 枚 def 级） | ~85–90% |
| W3 | PA18 :5364(FUEIMOV_4) | FUEIMOV_4：茎对二择（同序/交换）双支；LENGTH4_SET2/SWAP01 记账 + K4_CHI_MSB_POS + chi_msb_swap_23/01 符号排除；LIST_OF_CC_UH 收口 | 85 | 90–200 | W1 | 中（双支 chi_msb 记账，getD/EL 编码换算；分支 2 的 LENGTH4_SET2_SWAP01 对位是细致处） | ~85% |
| W4 | PA18 :5396(FUEIMOV_3) | FUEIMOV_3：ke(vl)=3 引子 + CC_CELL_CONVEX_HULL_INJ 极点集相等 + MXI kit 剥 mxi + 茎对二择 + chi_msb_swap_01 排除交换支 | 104 | 110–260 | W1 + W2 | 中（记账链最长；CARD4_IMP_DISTINCT 用 GBEWYFX+Nat.card 替代） | ~80–85% |
| W5 | PA18 :6685(FCHKUGT 本体) + 微件 | 本体四分支装配（骨架已完全解码，SCOUT §1.3）+ 3 微件本地复制（AFF_GT_SUBSET_AFFINE_HULL、X_IN_AFF_GT_X、BARV×2） | 97+30 | 100–230 | W3 + W4 | 低-中（case k=4 支 d 的 FUEIMOV_4 结论 + LIST_OF_CC_UH 对位记账是唯一细致处；hA 集合相等改写是全证明钥匙） | ~85–90% |

合计：**5 波 = 430–1030 Lean 行（中位 ~700）、2.5–4 个施工日（单工人）。**
无可选波（EWYBJUA 属池 B W6，非本 lane）。

## 波次间依赖图

```
W1(FUEIMOV_K+MCELL4_EP) ──► W3(FUEIMOV_4) ──┐
W1 ──► W2(MXI kit) ──► W4(FUEIMOV_3) ───────┼──► W5(FCHKUGT 本体)
                                            │
BG 落库（MCELL2/3_EDGE_FIRST）—无值级边，仅文件排队
```

## 首波开工时机（任务书第五问）

**W1/W2 可在 BG 落库当天开工：是。** 依据：
- W1/W2 与 BG 施工区（PA18 :5405-5480）无共享件、无值级依赖边（SCOUT §2.3）；
- 施工段物理不重叠（本 lane :5334-5396 + :6685；BG :5405-5480）；
- 唯一共享 = PA18 per-file `lake build` 闸门——两 lane 的**落库**必须串行（编排者排序），
  但 W1–W4 的**开发**可在独立分支先行（BG 落库后 rebase 成本低，段落不相交）。
- W5 依赖 W3+W4，自然排在文件队列的下一个空档。

## 与其他池的并行度

- **池 A（STATEMENT-FIX/CFFONNL）**：已落（SF-50，CFFONNL :4638 原序真证）——本 lane
  直接受益，无等待项。
- **池 B**：无值级耦合（池 B 的 EWYBJUA 是 REUHADY 的另一支前置，与本 lane 互补不冲突）；
  仅文件排队（池 B 施工区 PA18 :1983/:6959-7045）。
- **池 D**：**本报告收编了池 B 测绘时记在池 D 名下的 FUEIMOV_4**（以及未单列的
  FUEIMOV_3）——它们在 FCHKUGT 硬前置上，已并入本 lane W3/W4。若池 D 另有立项，
  编排者须合并或明示串行，避免双开工。
- **池 C（REUHADY/MCELL4_FULL_WEDGE 等）**：本 lane 清偿后 REUHADY 的楔二择支解锁，
  但 REUHADY 本体还欠 REUHADY1(PA24 污染闸)+EWYBJUA——池 C 的临界路径不因本 lane
  单独打通。

## 每波验收处方

- **W1**：`lake build Kepler.Text.PackingAuto18` 零 error；`#print axioms AJRIPQN` 输出
  仅 `[propext, Classical.choice, Quot.sound]`（若见 sorryAx → 触发 SCOUT §5.4 裁决预案）；
  FUEIMOV_K 消费形态照 HOL :2738-2748（AJRIPQN 以 ul:=ccUh V ul、vl:=ccUh V vl、
  i:=ccKe V ul、j:=ccKe V vl 实例化，hvol 由 ccCell 相等 + CC_CELL_NOT_NULLSET 供）。
- **W2**：MXI_NOT_IN_V 照 HOL :2894-2948 逐段：MXI_IN_VORONOI_LIST 的 ANTS（cc_ke=3 支
  的 barV 供给）→ EL 0 (cc_uh) ∈ V（BARV 链）→ sqrt2<2 → packing 反证（dist ≥ 2 对
  dist = sqrt2 < 2）。MCELL_V_INTER_EXTREME / MCELL_EXTREME_DIFF_V 各自独立可分块提交。
- **W3**：FUEIMOV_4 两支分块提交（先分支 1 同序茎、后分支 2 交换茎）；chi_msb 排除段
  照 PA18:2717/:2726 的 swap 件用法（CFFONNL 证明内已有 chi_msb_swap_01 消费先例）。
- **W4**：FUEIMOV_3 先走通 ke(vl)=3 引子与极点集剥层（MCELL_EXTREME_DIFF_V /
  MCELL_V_INTER_EXTREME 的 SET_TAC 段），再收 chi_msb 交换支；CARD4_IMP_DISTINCT 处
  直接 GBEWYFX（ne₁₂/ne₁₃/ne₂₃_of_not_collinear 已有派生，照 STEM_EDGEX :6667-6669 先例）。
- **W5**：本体按 SCOUT §1.3 七步骨架逐段 `have` 落账：hA 集合相等改写（`affGt {u0,u1} {u2}
  = affGt {u0,u1} {u2'}` 由 ccA0 定义展开直接得）→ CFFONNL 二择（TAUT 形，照 PA18
  CFFONNL 现行 getD 记法）→ k=3 双支 → k=4 反证双支 → CC_CELL_NOT_COPLANAR_EXTREME
  （pp := u2 走 getD-3 方程支）→ X_IN_AFF_GT_X + AFF_GT_SUBSET_AFFINE_HULL 收口。
  终验：`#print axioms FCHKUGT` 仅标准三 → PA25 侧 `#print axioms p25_leaf_azim_inj`
  同步转净（零编辑核对）。

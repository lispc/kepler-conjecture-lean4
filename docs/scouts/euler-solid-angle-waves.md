# Euler 泛型立体角 锚翻转 波次计划（WAVES）

> 配套 SCOUT.md §4/§7。行数 = 低估–高估（诚实区间，中位合计 ~1,400）。
> 全程仅 1 件 (d) 真数学缺口（W3 核）；W1/W2/W4/W5 均为机械/桥。
> W1-W4 落独立新文件（建议 `Kepler/Text/EulerSolidAngle.lean`，或 W1+W3 /
> W2+W4 两文件），与 PA21 零闸门冲突；仅 W5 触 PA21。

| 波 | 文件 | 内容 | 估行数 | 前置 | 风险 | 成功率 |
|---|---|---|---|---|---|---|
| W1 | 新文件 | atn2 全 kit（ATN2_BREAKDOWN 四分支/ATN2_RNEG/atn2_0/ATN2_POS/ATN2_LE_PI2/pi2_sub_atn2；SphereKit atn2 def unfold + 复制 W2a mi_p21e_atn2/mi_p21e_matan）+ `sol_euler_x = √Δ·solEulerXDivSqrtdelta` 泛型（merge:1060-1108）+ 备用 8 前提锚陈述 | 100–210 | 无（立即可开） | 低（全部 x-空间纯实数；唯一坑 = 强化合并前提差，按 8 前提锚开工、6 前提强化做独立小件） | ~90% |
| W2 | 新文件 | 几何层：Δ = 4·det² + Δ>0⇒三非共线（delta_x.hl:45-230）+ `simplex_exists`（merge:746，六棱定 tetrahedron，显式坐标构造）+ `dihV = dih_y`（merge:782-800）+ DIHV_DIH_X + DIHV_RESCALE_UNCHANGED + √Δ 重标 | 260–580 | 无 | 中（simplex_exists 是全车道最大单件；dihV 桥在 LuneVolume.dihV 展开角上做） | ~80% |
| W3 | 新文件 | 真数学核：DERIVATIVE_WRT_C1（一元，242 HOL）+ DERIVATIVE_WRT_A（二元，2889 HOL——两侧导数 0 + Convex ℝ + 一点定值）+ EULER_TRIANGLE_REAL_INTERVAL 的 Convex 件 + 单位盒 EULER_ANGLE_SUM 骨架 | 190–460 | W2（非共线/几何定义）；与 W1 并行可开（先只做 C1） | 中高（唯一 (d) 缺口；HOL 路线已知可行 + Mathlib 导数机器强，风险在边界取值细节与忠实转录；开工前普查 LocalAuto1/LA22 derivedForm kit 可省 50-150 行） | ~75–85% |
| W4 | 新文件 | 装配+重标：euler_p↔eulerAX 平移（merge:899-916；**副产物直接喂 LA22:161**）+ euler_after_rescale 代数恒等式 + EULER_FORMULA_RESCALE（单位盒→全形）+ EULER_ANGLE_SUM_rescal 收尾 + EULER_TRIANGLE + `sol_x_sol_euler_x` 总装 | 320–640 | W1+W2+W3 | 低-中（纯装配；分件提交防错误级联） | ~85–90% |
| W5 | PA21 | 锚翻转：`p21k_euler_anchor` 的真证明（由 W1 6/8 前提锚接线，20-50 行）+ TSKAJXY_034 翻除（1 行：`exact p21j_tskajxy034 hyp (p21k_cell4_from_ineq_of_euler hE hg hyp.2.2)`） | 20–50 | W1–W4 + **hg（bank_TSKAJXYGXSA 符号修复，SF 通道独立立项）** | 低（配方已验证）；工期风险 = SF 修复落地时机，非本车道可控 | ~85–90% |

合计：**W1–W5 = 890–1,940 Lean 行（中位 ~1,400）；单工人 1.5–3 周量级。**
对照：HOL 正本 4,572 行（三件）+ 钩子 ≈ 4,940；名义 4.5k 行中 69% 是导数
tactic 噪声（Mathlib 压缩 6-10×），几何构造件 HOL 短、Lean 是真活。

## 波次间依赖图

```
W1 ─────────────┐
W2 ──► W3 ──► W4 ──► W5 ──► TSKAJXY_034 翻除（另需 SF: bank_TSKAJXYGXSA 修复）
W1 ──► W4       │
W2 ─────────────┘
W4 副产物 ──► LocalAuto22.euler_p_eulerA_x_p22（白送件）
```

- W1 与 W2 无相互依赖，可双车道并行（不同文件或同文件不同段）。
- W3 的 C1 半件（一元恒等式）不依赖 W2，可在 W2 进行中提前开工。
- W5 是唯一 PA21 触点：与在飞 PA21 收编波**串行**（per-file 闸门）。

## 与其他在飞车道的关系

- **SF 通道**（bank_TSKAJXYGXSA 符号翻转，W5 交付书 §1.2）：TSKAJXY_034
  收口的第二债务入口；本车道只供 hE，两件齐才能翻 :4168。编排者应把
  SF 修复与 W5 并列排程。
- **LocalAuto22（OCBICBY 车道）**：二阶受益者（LA22:161 的 sorry 由 W4
  平移件白送）；OCBICBY 自身巨案债务（EAR_SOL_NN/empty_6T1 等）不归本车道。
- **路线备胎**：W2 若在 simplex_exists 卡壳（>1 周），启用路线 C spike
  （x-空间对 x1 求导 + 边界极限，估 400-900 行，见 SCOUT §4）；W1 期内
  可选做 W-乘积 6 元可行性探针（≤200 行）以封存路线 B。

## 每波验收处方

- W1：`lake env lean` 新文件 0 error；以 W5 现成的
  `p21k_gamma4fgcy_div_sqrtdelta` 反向单测——把 W1 的 sqrtdelta 件在
  (4,4,4,4,4,4) 正则四面体特例上数值/表达式对拍 `matan(2/25)/20`（ICD
  spot-check 同款）；8 前提与 6 前提锚两陈述并列入账。
- W2：先 Δ=4·det²（纯 ring 一步）→ 非共线 → simplex_exists → dihV 桥，
  四件各自 `have` 落账；dihV 桥用 LuneVolume 的
  `dihV_eq_arccos_cos_azim` 记法，勿重定义。
- W3：C1 先行（一元导数+一点值全流程走通）再做 A；导数侧一律
  `Real.deriv_arctan` + `HasDerivAt`，禁用 native_decide；Convex ℝ 件
  用 Mathlib MeanValue 一族（"区间导数 0 ⇒ 常值"两三行 glue）。
- W4：EULER_TRIANGLE 拼装先行（若 W3 两件签好，这一步应是 MESON 级）；
  euler_p↔eulerAX 平移件单独提交并跑 `#print axioms`（标准三面）。
- W5：翻除前先跑 W5 交付书 §5 的翻转配方（临时验证后回滚先例）；
  `#print axioms TSKAJXY_034` 必须无 sorryAx——全树 sorry 计数应归零。

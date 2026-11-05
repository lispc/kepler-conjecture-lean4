# WORKORDER — pa25-rolling-w6（接 w5，基线 = 主仓 HEAD `c831efac` + w5 `patch-pa25-rolling-w5.diff`）

> 工作副本建议：主仓 HEAD 打 w5 patch → PA25 应为
> **14,868 行 / 19 裸 sorry / 20 编译器 sorry 警告 / 0 error**，MD5
> `4f6fa20d2c0887efbe435299a8af764b`。唯一可改：`lean/Kepler/Text/PackingAuto25.lean`。
> 开工第一步必须整文件 standalone 打绿（继承字节 ≠ 已验证）：
> `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>`。

## 0. w5 已闭（勿重复做）

| 件 | 终稿行 | 锥内 | 证法 |
|---|---|---|---|
| `real_model_gamma8` | 12260 区 | N？→ **Y**（`parent=pkrmQx`） | `GG_MCELL_NONBETA` + 新私件 `p25w5_QITNPEA_9063653052`（六张 `QITNPEA1` 银行 + `wtcount6Y` 记账）+ `leaf_CIHTIUM` 顶边 + `sym26` 运回 |
| `real_model_gamma8b` | 12287 区 | **Y**（`parent=pkrmQx`） | 同核 + `(2 5)(3 6)` 复合换位（`p25w5_gamma4fgcy_perm`）/ `sym23` 二支 |
| `real_model_gckb` | 9730 区 | **Y**（`parent=pkrmAzim`） | `cc_4`：`c_4_azim_mcell_dih_y` + `MCELL4_DOMAIN` + `proj_bank_GCKBQEA`；`¬cc_4`：`CC_3_PROPS` 的 `∃ y4`（`dihY ≤ azim`）+ 同一银行 |

**w5 新增 8 个 `p25w5_*` private 助件**（全在 `real_model_gamma8` 之前，`:12217–12330` 区），
w6 可直接复用：

- `p25w5_QITNPEA_9063653052`：**这是 HOL `Merge_ineq.QITNPEA4_9063653052_weak_ALT` 的
  Lean 替身**——本波新造。语句：
  `y1 ∈ [2hmin,2hplus] → y2,y5,y6 ∈ [2,2hmin) → y3 ∈ [2hmin,√8] → y4 ∈ [2,√8] →
   rad2 < 2 → 0.0057 < gamma4fgcy y1..y6 lmfun / wtcount6Y y1..y6`。
  **凡是 HOL 里 `MP_TAC QITNPEA4_9063653052_weak_ALT` 的位置都可直接消费它**。
- `p25w5_rhoX_sym26` / `p25w5_rad2YP25_sym26` / `p25w5_rad2YP25_perm`：
  `rad2YP25` 的 26-换位与 `(2 5)(3 6)` 复合换位（w4 只做了 sym23）。
- `p25w5_wtcount6Y_sym26` / `_sym23` / `_perm`：`wtcount6Y` 的三种换位（`omega` 型）。
- `p25w5_gamma4fgcy_perm`：`gamma4fgcyP25` 的 `(2 5)(3 6)` 复合换位。

## 1. w6 推荐批次（按杠杆排序）

### W6-A ★ 单点解锁 8 件：`cell3_008_from_ineq` 桥（**锥外 → 锥内闸门**，~250 行，高）

**这是全文件当前最大的杠杆点**：`MCELL3_008` 一落，`GAMMAX_008a`、`GAMMAX_008b`、
`real_model_008`、`real_model_cell23_008`、`real_model_gr`、`real_model_pema`、
`real_model_pemb`、`real_model_txq`、`real_model_tew` **九件全部 ~40 行内可收**
（它们的 HOL 证明在其后都是纯装配，且依赖银行/装配件全在库）。

要补的两个 missing 桥（Lean 均无，`grep` 过）：

1. `cell3_008_from_ineq_ALT`（HOL `merge_ineq.hl:4588`）：纯 bootstrap，句子是
   ```
   pack_nonlinear ⇒ ∀ y1 y2 y6, 2hmin≤y1, 2≤y2, 2≤y6, y1≤2hplus, y2≤2√2, y6≤2√2,
     eta_y y1 y2 y6 < √2 ⇒ dih_y y1 y2 √2 √2 √2 y6 * 0.008
       ≤ gamma3f y1 y2 y6 √2 lmfun / wtcount3_y y1 y2 y6
   ```
   上游 `cell3_from_ineq_thm_ALT`（同样缺；Lean 已有等价物 **`cell3_from_ineq_thm`**，
   `real_model_3a` 在用，可直接顶替）。
2. `cell3_008_from_ineq_thm`（HOL `merge_ineq.hl:4455`，**真正的活**）：三步
   (a) 对称性归约 `y6 ≤ y2`（`gamma3f_sym` 在库、`dih_y` sym 私件在库）；
   (b) `Q` 盒 + `ETA_Y_BOUNDS`/`ETA_Y_LE_IMP_LT_ALL`（**两张都在 PA21**）清 `eta_y`；
   (c) `wtcount3_y = if critical_edge_y y2 then 2 else 1` + `y6 < 2hmin`，随后
   `undiv_gamma3_nn`（**Lean 缺**，需按 HOL 定义补一个 `gamma3f = gamma3_x/wtcount` 桥）
   + y2 二分支（`y2 < 2hmin` 取 `h0cut y2 = 1`、否则取 `2`）套三张银行
   `bank_QZECFICwt1` / `bank_QZECFICwt2A` / `bank_CIHTIUM`（**三张都在 PA21**）。

**卡点清单（诚实版）**：`undiv_gamma3_nn`、`cell3_from_ineq_thm_ALT` 两件缺失；
`h0cut` 的 0/1 分派与 `gamma3_x` 的 y-空间桥需自查 PA21 有无现成 `gamma3_x_gamma3f`
（HOL `gamma3_x_gamma3f` 在 `merge_ineq.hl:4100` 区，Lean 待 grep）。

### W6-B `real_model_gamma10` + `gamma11`（**锥内**，~60 行/件，中）

只差一张 missing 银行 `gamma10_gamma11_ALT`（HOL `merge_ineq.hl:4071`）：

```
pack_nonlinear ⇒ ∀ y1..y6,
  2hmin≤y1≤2hplus, 2≤y2<2hmin, 2≤y3<2hmin, 2hmin≤y4≤√8,
  2≤y5<2hmin, 2≤y6<2hmin, rad2<2 ⇒
  0.0057 ≤ gamma4fgcy/wtcount6 + beta_bumpA_y + gamma3f y1 y2 y6 √2 lmfun
```

它由 `gamma10_gamma11`（HOL 同文件）用四张**在库**银行
（`GLFVCVK4 2477216213` = `bank_GLFVCVK4`、`QITNPEA 5400790175 a/b`、`FWGKMBZ`）+
`cell3_from_ineq_thm_ALT`（同 W6-A 的 missing 桥！）导出。**若 W6-A 先做完，
本件几乎白送**：`beta_bumpA_yP25` 的 sym23（`beta_bumpA_y_sym23` 在库）、
`gamma3f_sym` 在库；装配面 `critical_weight1a/b`、`GG_MCELL_GENERAL`、
`mcell3_gammaX_gamma3f`、`mcell3_gammaXb_gamma3f` 全部已真证。
两个 `real_model_gamma10/11` 本体各 ~40 行（HOL 证明骨架：
`critical_weight1 → GG_MCELL_GENERAL → mcell3_gammaX_gamma3f → 银行 → MCELL4_DOMAIN 盒 → linarith`）。

### W6-C `real_model_sum_azim`（**锥外**，~20 行，低风险新发现）

w5 侦察发现：HOL 证明只用 `LEAF_RANK_GRUTOTI`（**已在 PA25 真证**）+ `HL_2` 化简 +
`0 < √2 − hplus`（`Flyspeck_constants.bounds` → Lean 侧用 `mi_sqrt8_eq` /
`mi_hminus_prop` 算术）。原 w5 工单把本件列为「深水不碰」，但依赖面已收窄到
**一件已在库的真件 + 常数算术**，w6 值得花 3–5 个探针先验。

### W6-D 不建议开（保持）

- `real_model_ox3q1h_merge`：需 `hox : ox3q1hP25`（DEF-FIX 冻结）。
- `pkLeafRankCriticalEdge` / `CELL_CLUSTER_ESTIMATE_REDUCE` / `CELL_CLUSTER_N_LE_1`：
  深水，无新工具不开。
- `real_model_quqy` / `quqy_sym`：w5 未侦察；w6 可先花半波读 HOL `OXLZLEZ3.hl`
  对应段判依赖面。

## 2. 雷区（w5 实测补充，接 w4 的 12 条）

1. **`Decidable` 陷阱（新增）**：`criticalEdgeY` 是 `Prop`；在不 `open Classical` 的
   文件里，**陈述位**写 `if criticalEdgeY _ then … else 0` 会
   `synthInstanceFailed: Decidable`. 解法：证明体首行 `classical`（tactic），
   随后局部 `propDecidable` 覆盖 `have`/`show` 的类型细化。
2. **`not_lt.mp` vs `not_le.mp`（新增）**：`leaf_CIHTIUM` 的两条距离前提是
   `2 * hminus ≤ d`。`by_contra h` 后：`not_lt.mp h : 2hmin ≤ d`（h : ¬ d < 2hmin）；
   `not_le.mp h : d < 2hmin`（h : ¬ 2hmin ≤ d）。写反即类型不符。
3. **`CC_3_PROPS` 33 元合取逐位表**（见 `Evidence.md` §6.4）：18–22 是五个下界、
   23–27 是五个 `≤ 2√2`、32 是 `azim_mcell = azim`、33 是 `∃ y4`（6 元）。
   数错一位不报错（同型命题）——**必须按位点**。
4. **`bank_QITNPEA1tmpl` 无 `i3 = 0`**：y3 箱 `[2hmin, √8]`，六张银行
   `(i3,i4) ∈ {1,2}×{0,1,2}`。所以 y3 槽必须 ≥ `2hmin`；若原构型不满足，
   用 `leaf_CIHTIUM` 把唯一非小边顶进来，再用 `sym26`/`sym23` 运回
   （w5 `gamma8`/`gamma8b` 即此套路）。
5. **`MCELL4_DOMAIN` 上界是 `2 * Real.sqrt 2`**，银行要 `Real.sqrt 8`：
   `le_trans (le_of_lt h) (le_of_eq mi_sqrt8_eq.symm)`。
6. **`w4` 只做了 sym23 私件**；本波补了 sym26/perm 系列（`p25w5_*`），
   w6 可直接用，别重写。
7. **`private` 作用域**：`p25w4_*`/`p25w5_*` 在本文件内可见，但**跨文件不可见**
   （探针文件 `import Kepler.Text.PackingAuto25` 时看不到），做探针要么内联、
   要么在原文件上整文件验。
8. 文件头 `open Kepler.Geom Set Classical MeasureTheory` 是 HEAD 遗留，**不得效仿**；
   新件要可判定性用 `classical` tactic。
9. 前向引用：`real_model_3a/3b` 在 `GAMMAX_008a` 之后，只能仿写不能 `exact`；
   `p25w5_*` 助件全在 `:12217–12330`（`gamma8` 之前、`leaf_CIHTIUM`/`gamma4fgcy_POS`
   之后），w6 新私件放同一区段或紧随其后再引用。
10. `w5` 已确认 **`bank_GCKBQEA` / `QITNPEA1_*` / `PEMKWU` / `TXQTPVC_MERGED` /
    `TEWNSCJ_MERGED` / `FHBVYXZv2a` 全在库**，无需重推。

## 3. 交付（`$S` 根下）

`patch-*.diff` + `Work.lean` + `Kit-draft-*.lean`（如有残件）+ 本工单续篇
`WORKORDER-w7.md` + `DELIVERY.md`（闭合件表 + 每件证法一句 + 残件精确缺口表 +
搬债审计地图 grep + 预算自报）+ `Evidence.md`（`#print axioms` 原文 +
整文件 RC/错误数/sorry 声明计数 N→M）+ `logs/`；归档
`docs/archive/lane-archives/pa25-rolling-w6/`。

**验收期望**：own-sorry 19 → **≤16**（W6-A 一落即 9 件，远超；W6-A 未落则
W6-B/C 两件保底）；闭合件 `#print axioms` = `[propext, Classical.choice, Quot.sound]`；
`ox3q1hP25` 与 624 shard 面零漂移。

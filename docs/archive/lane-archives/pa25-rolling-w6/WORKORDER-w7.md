# WORKORDER — pa25-rolling-w7（接 w6）

> 基线：主仓 HEAD ≥ `873d2a2c` + w6 `patch-pa25-rolling-w6.diff`
> → PA25 应为 **15,417 行 / 12 裸 sorry / 13 编译器 sorry 警告 / 0 error**，
> MD5 `766b6b2a86f6aacce24190a14d9a6077`。唯一可改：
> `lean/Kepler/Text/PackingAuto25.lean`。
> 开工第一步整文件 standalone 打绿（继承字节 ≠ 已验证）：
> `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>`。

## 0. w6 已闭（勿重复做）

| 件 | 行 | 证法 |
|---|---|---|
| `MCELL3_008` | 13429 | `MCELL3_EDGE_FIRST` 归一 stem + `gammaX_gamma3f` + `MCELL3_CRITICAL_WEIGHT` + `MCELL_BUMP_0` + 新桥 `p25w6_cell3_008_aux` |
| `real_model_008` | 13508 | 逐胞 SUM_LE；`EDGE_IMP_K23`：k=2 = `MCELL2_CRITICAL_WEIGHT1`+`CC_2_PROPS`，k=3 = `MCELL3_008` |
| `real_model_cell23_008` | 13681 | `CC_3_SUM_fn`×2（azim/gg）+ `real_model_008` + `Finset.mul_sum` |
| `GAMMAX_008a/b` | 13731 / 13757 | `CC_3_PROPS` + `EL_CC_UH` + `STEM_EDGEX` + `MCELL3_008` |
| `real_model_gr` | 13827 | cell23_008 + GAMMAX_008a/b + `linarith` |
| `real_model_sum_azim` | 9811 | 前置私拷贝 `p25w6_order_azim_sum2pi0` + `LEAF_RANK_REUHADY` + `GBEWYFX` + `hplus<√2` |

**新 private kit（9 枚，w7 可直接复用）**：
`p25w6_dihY_swap`、`p25w6_matan`、`p25w6_dihXf_atn`、`p25w6_dihalg`、
`p25w6_dihXf_bridge`、`p25w6_dihY_bridge`、`p25w6_undiv_gamma3_nn`、
`p25w6_cell3_008_aux`、`p25w6_order_azim_sum2pi0`。

- `p25w6_cell3_008_aux : cell3_bank → ∀ y1 y2 y6, 2hmin≤y1≤2hplus → 2≤y2 →
  2≤y6 → y2≤2√2 → y6≤2√2 → eta_y<√2 → 0.008*dih_y y1 y2 s s s y6 ≤
  gamma3f y1 y2 y6 s lmfun / wtcount3Y y1 y2 y6`——HOL
  `cell3_008_from_ineq_ALT` 的 Lean 实装，凡 HOL 里 `MP_TAC
  cell3_008_from_ineq_ALT` 的位置都可直接消费。
- `p25w6_undiv_gamma3_nn`：x-空间银行 → y-空间 rescaling 的通用桥
  （`dih_y = sqrt(Δ) * dih_x_div_sqrtdelta`），w7 的 pema/pemb 若需同类
  转换可直接用。

## 1. w7 推荐批次（按杠杆排序）

### W7-A ★ pema/pemb 双件（~80 行/件，高，几乎纯装配）

008 家族落地后这两件只剩装配（HOL OXLZLEZ3.hl:8296-8419）。骨架：

1. `real_model_cell23_008` 给
   `(gA − .008 dA) + (gB − .008 dB) + .008 azim ≤ gg`；
2. `GAMMAX_008b`（pema）/ `GAMMAX_008a`（pemb）给一侧 `0 ≤ g − .008 d`，
   把目标化为「另一侧 cc 胞 + 余项」的单侧不等式；
3. `CC_3_PROPS` 第 33 合取支取 `∃ y4`（`dihY … y4 … ≤ azim`）；
4. `JSP_BOUNDS` 把非 1.34 侧的两条边压到 `< 2hmin`；
5. `proj_bank_PEMKWU`（`bank_PEMKWU` 在库）+ `mi_gamma3_x_gamma3f` +
   `MCELL2_CRITICAL_WEIGHT1` + `mcell3_gammaX_gamma3f` +
   `mcell3_dihX_dih_y` 收口，末尾 `linarith`。

**雷**：HOL 的 `critical_weight1` = Lean `MCELL2_CRITICAL_WEIGHT1`；
`gamma3_x_gamma3f` = `mi_gamma3_x_gamma3f`；`dih_y` 槽序按
`p25m_dihY_rev`/`p25w4_dihY_sym23` 摆。

### W7-B txq/tew 双件（中，同型装配）

`real_model_cell23_008` + `proj_bank_TXQTPVC` / `proj_bank_TEWNSCJ`
（`TXQTPVC_MERGED`/`TEWNSCJ_MERGED` 在库）+ `LEAF_DOMAIN` 盒 +
`JSP_BOUNDS`。HOL 段 OXLZLEZ3.hl:8490-8770（txq）/ 8770-8900（tew）。
先在 HOL 里定位 `real_model_txq`/`real_model_tew` 的 bank 实例化盒子，
再写 Lean。

### W7-C gamma10/gamma11（中高，需补 3 个桥）

HOL `gamma10_gamma11_ALT`(:4071) 与上游 `gamma10_gamma11`(:4071 前) 均不在
Lean。已有：四银行（`proj_bank_GLFVCVK4_*`、`proj_bank_QITNPEA5400790175a/b`、
`proj_bank_FWGKMBZ`）、`beta_bumpA_y_sym23`、`ztg4w1_quarter_norm2hh`
（= HOL `quarter_norm2hh`）。缺：

1. `rad2_eta2`：`2≤y1,y2,y6 ∧ y_i<4 ∧ rad2_y<2 ∧ 0<delta_y ⇒ eta_y y1 y2 y6^2<2`
   （HOL :3869；可用 `rad2XP25` 定义 + `mi_ETA_Y_BOUNDS` 反向）；
2. `beta_bump_lb` / `beta_bumpA_lb1`：`beta_bumpA_y ≥ beta_bump_lb ≥ 0`
   与常数 `beta_bump_lb`（HOL `#0.0057` 分解；`bump` 值域
   `0 ≤ bump ≤ 0.005` 已有 `p25w5_bump_mem`）；
3. `wtcount6_y = 1/2` 分支的临界性记账（HOL :4018-4068）。

## 2. 不建议开（保持）

- `real_model_ox3q1h_merge`：需 `hox : ox3q1hP25`（DEF-FIX 冻结）。
- `pkLeafRankCriticalEdge` / `CELL_CLUSTER_ESTIMATE_REDUCE` /
  `CELL_CLUSTER_N_LE_1`：深水，无新工具不开。
- `real_model_quqy` / `quqy_sym`：仍未侦察；w7 可先花半波读 HOL
  `OXLZLEZ3.hl` 对应段（`g_quqya_goal` 区）判依赖面。

## 3. 雷区（w6 实测新增，接 w4/w5）

1. **`setSum` 两侧展开**：`rw [setSum, setSum, dif_pos hfin]` 只展开一侧；
   用 `simp only [setSum, dif_pos hfin]`（见 `probe-mini.lean`）。
2. **`dihY` 槽序**：`undiv_gamma3_nn` 的结论是
   `dihY y4 √2 y6 √2 y5 √2`（第 5 槽 y5、第 6 槽 √2），不是
   `dihY y4 √2 y6 √2 √2 y5`。`dihY y1 y2 s s s y6 = dihY y1 s y6 s y2 s`
   需 `p25m_dihY_rev` ∘ `p25w4_dihY_sym23`（= `p25w6_dihY_swap`）。
3. **前向引用**：`LEAF_RANK_GRUTOTI` / `ORDER_AZIM_SUM2Pi0` /
   `AZIM_ZERO_SHIFT` 都在文件末尾（>14000），而 `real_model_sum_azim`
   在 9811。w6 的处理是**同体私拷贝前置**（`p25w6_order_azim_sum2pi0`）；
   任何 9811 之前的新件不要直接引用末尾声明。
4. **`CC_3_PROPS` 33 元合取按位**：4/5 = 两 cc 胞 beta=0；15/16/17 = leaf；
   30/31 = 非空；32 = `azim_mcell=azim`；33 = `∃ y4`。数错一位不报错。
5. **`MCELL_BUMP_0` 的胞形**：结论在 `betaBump V e (mcell k V ul)` 上；
   与 `betaBumpV1 V e X`（X=`mcell k V ul`）是 `rfl`（PA25:1799 先例）。
6. **`private` 作用域**：`p25w6_*`/`p25w5_*`/`p25m_*` 在 PA25 内可见，
   跨文件探针不可见——探针需同体副本（w6 `probe1` 即此）。
7. **其余沿用 w5 工单 §2 的 10 条**（`Decidable` 用 `classical` tactic、
   `not_lt.mp` vs `not_le.mp`、`MCELL4_DOMAIN` 上界 2√2 vs 银行 √8 等）。

## 4. 交付（`$S` 根下）

`patch-*.diff` + `Work.lean` + `Kit-draft-*.lean`（如有残件）+
`WORKORDER-w8.md` + `DELIVERY.md` + `Evidence.md` + `logs/`；
归档 `docs/archive/lane-archives/pa25-rolling-w7/`。

**验收期望**：own-sorry 12 → **≤9**（W7-A 两件 + W7-B 两件即 8）；
闭合件 `#print axioms` = `[propext, Classical.choice, Quot.sound]`；
`ox3q1hP25` 与 624 shard 面零漂移。

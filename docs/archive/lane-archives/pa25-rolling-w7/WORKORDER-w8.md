# WORKORDER — pa25-rolling-w8（接 w7）

> 基线：主仓 HEAD ≥ `a509e470` + w7 `patch-pa25-rolling-w7.diff`
> → PA25 应为 **15,855 行 / 8 裸 sorry / 9 编译器 sorry 警告 / 0 error**，
> MD5 `6363af3367799573760fdef59983a46d`。唯一可改：
> `lean/Kepler/Text/PackingAuto25.lean`。
> 开工第一步整文件 standalone 打绿（继承字节 ≠ 已验证）：
> `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>`。

## 0. w7 已闭（勿重复做）

| 件 | 行 | 证法 |
|---|---|---|
| `real_model_txq` | 14812 | `real_model_cell23_008` + `TXQTPVC_MERGED` + `critical_weight1a/1b` + `mcell3_gammaX{,b}_gamma3f` + `azim = dihY`（`azim_dihv_same` ∘ `DIHV_EQ_DIH_Y_4PT_B`）+ `ring`/`linarith` |
| `real_model_tew` | 14928 | `TEWNSCJ_MERGED` + `CC_3_PROPS` 的 `∃y4`（`dihY … y4 … ≤ azim` 换成 `b_spine5 ≤ 0` 支）+ `mul_le_mul_of_nonpos_left` |
| `real_model_pema` | 13927 | `GAMMAX_008b` 消 b-侧 + `PEMKWU` 银行 **(2 3)(5 6) 换位实例** + `p25w7_gamma23Keep135X_yOfX_eq` + 六逃逸支否证 |
| `real_model_pemb` | 14040 | `GAMMAX_008a` 消 a-侧 + `PEMKWU` **自然序实例** + 同桥 + 同否证 |

**新 private kit（4 枚，零 sorry / 零新 import，w8 可直接复用）**：
`p25w7_rhoX_sym23`(13880)、`p25w7_rad2X_sym23`(13884)、`p25w7_rad2Y_sym23`(13889)、
`p25w7_gamma23Keep135X_yOfX_eq`(13900)。
`dihY` 的 23-换位用既证 `p25w4_dihY_sym23`(9475)；(2 6)(3 5) 反序用 `p25m_dihY_rev`(9958)。

**残 8 裸 sorry**：`real_model_gamma10`(12201)、`real_model_gamma11`(12221)、
`real_model_quqy`(10581)、`real_model_quqy_sym`(10598)、
`pkLeafRankCriticalEdge`(9877)、`CELL_CLUSTER_ESTIMATE_REDUCE`(6155)、
`CELL_CLUSTER_N_LE_1`(6503)、`real_model_ox3q1h_merge`(9954)；
另 `ox3q1hP25`(90) DEFHOLE。

## 1. w8 唯一瓶颈：`rad2_eta2` 分析核（W8-A，★ 最高杠杆）

**它一落地，锥内 4 件（gamma10/11 + quqy/quqy_sym）同波可收。**

`rad2_eta2`（HOL `merge_ineq.hl:3869`）目标陈述（Lean 化建议）：

```lean
theorem p25w8_rad2_eta2 (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1 : 2 ≤ y1) (h2 : 2 ≤ y2) (h6 : 2 ≤ y6)
    (h1' : y1 < 4) (h2' : y2 < 4) (h6' : y6 < 4)
    (hrad : rad2YP25 y1 y2 y3 y4 y5 y6 < 2)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    eta_y y1 y2 y6 ^ 2 < 2
```

HOL 路线 = 传递 `eta_y y1 y2 y6² ≤ rad2_y y1..y6 < 2`，核心子件
`rad2_x_eta_x`（`merge_ineq.hl:3844`）：

```
0 < x4, 0 < x5, 0 < x6, 0 < ups_x x4 x5 x6, 0 < delta_x x1..x6
  ⇒ eta_x x4 x5 x6 ^ 2 ≤ rad2_x x1..x6
```

Lean 侧落法（建议，全部为多项式恒等 + 正性）：

1. `etaX x4 x5 x6 = Real.sqrt (x4*x5*x6 / upsX x4 x5 x6)`（已真体，ICD:606）；
   `rad2X x1..x6 = rhoX x1..x6 / (deltaX x1..x6 * 4)`（已真体，ICD:628）。
2. 需先立 `UPS_X_POS : 0 < x4 ∧ 0 < x5 ∧ 0 < x6 → upsX x4 x5 x6 > 0`
   （`upsX x1 x2 x6 = -(x1²) - x2² - x6² + 2x1x6 + 2x1x2 + 2x2x6`
   = `(√x1+√x2+√x6)(-√x1+√x2+√x6)(√x1-√x2+√x6)(√x1+√x2-√x6)` 的 Heron 形；
   或直接 `nlinarith` 于 `0 < x4, x5, x6`——注意 `upsX` 在这里是**非**三角形判别式，
   需先确认符号：数值 `upsX 4 4 4 = 48 > 0`）。
3. 主恒等式（HOL `Collect_geom.RHUFIIB` + `Merge_ineq.delta_delta_x`）：
   `rhoX x1..x6 * upsX x4 x5 x6 = 4 * deltaX x1..x6 * (x4*x5*x6) + S ^ 2`
   其中 `S` 是三个「对边对」(x1,x4)(x2,x5)(x3,x6) 的 Gram/行列式表达式。
   **做法**：像 `p25_radv_etay_core`(1005) / `GDRQXLGv3`(1349) 一样引入点积原子
   （`obtain ⟨p, hp⟩ : ∃ p, p = inner …`），`unfold rhoX upsX deltaX`，再 `ring`。
   平方后 `nlinarith [sq_nonneg S]` 收口。
4. `rad2_x_sym`：HOL 用的是 `rad2_x x1 x2 x3 x4 x5 x6 = rad2_x x4 x5 x3 x1 x2 x6`
   （`merge_ineq.hl:3889`），Lean 已证的 `p21i_rad2X_sym{12,23,03}` **槽形不同**
   且是 PA21 `TSKAJXY034W3` 内 `private`。须另立本文件私拷（3 行 `unfold; ring`
   + 已证 `p25w7_{deltaX,rhoX}_sym23` 可作模板）。
5. 数值/正性收尾：`Real.sq_sqrt`、`Real.sqrt_lt`、`div_pos`、`mul_pos`。

**建议先写 1 页纸的探针**：`import Kepler.Text.PackingAuto25` +
`p25w8_rad2_x_eta_x`，用 `example : rad2X 4 4 4 4 4 4 = 1.5`（ICD:637 已有）做数值哨兵，
确认恒等式的 `S` 是什么，再写主证明。

## 2. W8-B ★★ gamma10 / gamma11（2 件，依赖 W8-A）

HOL 链：`real_model_gamma10`(OXLZLEZ3.hl:6947) → `gamma10_gamma11_ALT`
(merge_ineq.hl:4071) → `gamma10_gamma11`(merge_ineq.hl:3997)。
**三级 Lean 全无**，须按序补：

1. `gamma10_gamma11`（约 70 行）：前提
   `pack_nonlinear_non_ox3q1h` + 四银行 + `cell3_from_ineq`；框
   `[2hmin,2hplus]×[2,2hmin)²×[2hmin,√8]×[2,2hmin)²`；
   结论 `0.0057 ≤ gamma4fgcy y1..y6 lmfun / wtcount6_y y1..y6 + beta_bumpA_y y1..y6 + gamma3f y1 y2 y6 √2`。
   四银行业已真体投影：`proj_bank_GLFVCVK4*`、`proj_bank_QITNPEA5400790175a/b`、
   `proj_bank_FWGKMBZ`（PA21；`bank_*` 定义见 PA21:610/768-815 区）。
   证明骨架（HOL 逐字）：
   - `eta_y y1 y2 y6² < 1.34²` 支：直接 `linarith`（gamma4fgcy 项由银行给正）。
   - `wtcount6_y = 2` 支：`linarith`（HOL `ASM_REWRITE_TAC[]; REAL_ARITH_TAC`）。
   - `wtcount6_y = 1` 支：**需 `quarter_norm2hh`**——
     Lean 已有 `ztg4w1_quarter_norm2hh`(11291)，HOL 侧 `quarter_norm2hh` 是其否证支；
     再需 `critical_edge_y y1 ∧ ¬critical_edge_y y2..y6 ∧ wtcount6_y = 1` 的
     记账（`unfold wtcount6Y wtcount3Y; split_ifs; omega`，`GG_MCELL_GENERAL` 有同款先例）。
   - `beta_bumpA_y ≥ beta_bump_lb`：**新桥 `beta_bumpA_lb1`**（小件，
     `betaBumpLb = -0.005` ICD:493；`beta_bumpA_yP25` 真体 PA25:113；
     用 `0 ≤ bump ≤ 0.005`，先例 `p25w5_bump_mem`）。
   - `gamma4fgcy/wtcount6 ≥ gamma4fgcy/2`：由 `0 < gamma4fgcy` + `wtcount6 ≤ 2`。
2. `gamma10_gamma11_ALT`：trivial wrapper（把四银行换成 `proj_bank_* hnl`）。
3. `real_model_gamma10` / `gamma11`（各 ~50 行装配，HOL OXLZLEZ3.hl:6947/7008）：
   `critical_weight1a/1b` → `GG_MCELL_GENERAL`（`h4 : cc_4 …` 供）
   → `mcell3_gammaX{,b}_gamma3f`（`hno4` 供）
   → `gamma4fgcy_sym23` / `wtcount6_y_sym23`(10929) / `beta_bumpA_y_sym23`(10943)
   → `gamma10_gamma11_ALT` → `MCELL4_DOMAIN`(8998) 供框。
   **雷**：`gamma4fgcy_sym23` 在 Lean **无同名件**，须先查 `gamma4fgcyP25` 的
   23-换位是否另有具名件（`gamma4fgcyP25` 真体见 PA25:134，可 `unfold; ring` 现场立）。
   框里 `2*hminus ≤ y4`（y4 = `dist (f i) (f (i+1))`）**不是** `MCELL4_DOMAIN` 直接给的
   （它只给 `2 ≤ y4 < 2√2`），HOL 靠 `ASM_REWRITE_TAC[sqrt2; sqrt8_sqrt2]`
   + `hminus` 界补——须自查 `hminus` 与 `2` 的关系（`mi_two_le_two_hminus` 在库）。

## 3. W8-C ★ quqy / quqy_sym（2 件，同样依赖 W8-A）

HOL `g_quqya_goal`(merge_ineq.hl:3932) / `g_quqya_g_quqyb`(:3955)：
目标 `0 ≤ gamma4fgcy y1..y6 lmfun + gamma3f y1 y2 y6 √2`，框
`[2hmin,2hplus]×[2,2hmin]⁵`，前提 `rad2_y < 2`，银行 = `FHBVYXZ a/b` + `FWGKMBZ`
（+ `cell3_from_ineq`）。核心跳出支 = `rad2_eta2`（`eta_y² < 2`）。
`real_model_quqy` 的 HOL 段（OXLZLEZ3.hl 未定位，工单 w7 §2 已标「先侦察」）：
建议 w8 先花半波定位该 `prove_by_refinement` 段，再决定成本；
其结论是否就是 `g_quqya` 型（`0 ≤ …`）需核。

## 4. 不建议开（保持）

- `real_model_ox3q1h_merge`：需 `hox : ox3q1hP25`（DEF-FIX 冻结）。
- `pkLeafRankCriticalEdge` / `CELL_CLUSTER_ESTIMATE_REDUCE` / `CELL_CLUSTER_N_LE_1`：
  深水，无新工具不开。

## 5. 雷区（w7 实测新增，接 w4/w5/w6）

1. **`∀ i, (A ∧ B ∧ …) → C` 只有 2 个 binder**：`intro i hno4 hltA …` 会报
   「no additional binders」；必须 `intro i h; obtain ⟨…⟩ := h`。
2. **`le_of_not_lt` 在本 Mathlib 不存在**：用 `not_lt.mp`。
3. **`mul_self_le_mul_self` 签名** = `(0 ≤ a) → (a ≤ b) → a*a ≤ b*b`（顺序是最小/最大在前）。
4. **`rad2YP25` vs `yOfX rad2X` 是 defeq 但非 syntactic**：`rw` 前须
   `have h2' : rad2YP25 … := h2`，否则报「pattern 不在目标中」。
5. **`linarith [hbank, hEq, hc23]`**：`hEq` 必须是**等式**。`rw [← hEq]` 的
   方向若要「用 hEq 换掉目标」，写法是 `rw [hEq]`（← 反了会静默失败）。
6. **`rw [sym23 …]` 方向**：`p25w4_dihY_sym23 a b c d e g : dihY a b c d e g = dihY a c b d g e`。
   要把目标里的 `dihY a c b d g e` 换成 `dihY a b c d e g`，用 `rw [← p25w4_dihY_sym23 a b c d e g]`
   （实参必须按**源序**给，不能按目标序给——按目标序给会找不到 pattern）。
7. **`CC_3_PROPS` 33 元合取按位**：4/5 = 两 cc 胞 beta=0；15/16/17 = leaf；
   18–22 = 2 ≤ 五条边；23–27 = ≤ 2√2 五条；28/29 = eta_y < √2（a/b 侧）；
   30/31 = 非空；32 = `azim_mcell = azim`；33 = `∃ y4`。数错一位不报错。
8. **PEMKWU 的 y-槽序**：`pema` 用 (2 3)(5 6) 换位实例（y2=dist u0 f(i+1)，
   y3=dist u0 f(i)，y5=dist u1 f(i)，y6=dist u1 f(i+1)）才让 `gamma3f y1 y3 y5`
   落在 a-侧；`pemb` 用自然序。搞反会得到对侧 gamma3f、`ring` 不收。
9. **`private` 作用域**：PA21 `TSKAJXY034W3` 的 `p21i_*` 全是 `private`，跨文件不可见；
   跨文件探针也看不到 PA25 的 `p25w*`/`p25m_*`。
10. **探针提速（本波最大发现）**：`lean/.lake/build/lib/lean/Kepler/Text/PackingAuto25.olean`
    可用时，探针写 `import Kepler.Text.PackingAuto25` + `open Kepler.Text Kepler.Geom`，
    单轮 ~20s 而非 5–6 min。注意 `Packing` 须写全名 **`Kepler.Packing`**
    （`open Kepler.Text` 不够，会撞 autoImplicit 变成隐变量）。
    若 olean 过期（PA25 源改动后未重建），Lean 只报「invalid import」或静默用旧版——
    **改动后必须整文件 compile 复核**，不能只信探针。
11. 其余沿用 w5 工单 §2、w6 工单 §3 的条目。

## 6. 交付（`$S` 根下）

`patch-*.diff` + `Work.lean` + `Kit-draft-*.lean`（如残件移出）+
`WORKORDER-w9.md` + `DELIVERY.md` + `Evidence.md` + `logs/`；
归档 `docs/archive/lane-archives/pa25-rolling-w8/`（Work.lean 不入库）。

**验收期望**：own-sorry 8 → **≤4**（W8-A 落地 + W8-B 两件 + W8-C 两件 = 4）；
若 W8-A 卡住，退守「不动」（8 保持，交回精确缺口），**不要**把半成品留进 kit。
闭合件 `#print axioms` = `[propext, Classical.choice, Quot.sound]`；
`ox3q1hP25` 与 624 shard 面零漂移。

**章节收尾判定线**：当 PA25 只剩 `ox3q1hP25` + `CELL_CLUSTER_*`×2 +
`pkLeafRankCriticalEdge` + `real_model_ox3q1h_merge`（DEFHOLE 依赖）时，
可在 DELIVERY 写明「章节可宣布收尾（除 DEFHOLE）」。

# sf76-gaps.md — 塌缩链核对表 + 缺口清单（lane sf76draft-w1）

基线：主仓 HEAD = `1bd6a3fd`（2026-10-28，SF-65 后；TASK 所记 `b226b2a6` 已被
后续推进覆盖，PA25 现态 11242 行、sym23 锚 :9594）。零写入主仓、零构建；
全部核对凭 `sed -n`/`grep` 只读 + HOL 正本逐字比对。

---

## 一、塌缩链七件核对表（GG_MCELL_GENERAL 证填前提）

| # | 件 | PA25 锚 | 真证 | HOL 对应（OXLZLEZ3.hl） | 即插即用判定 |
|---|---|---|---|---|---|
| 1 | `critical_weight_wtcount6_y` | :8111 | ✓（六步 CARD_INSERT 配方，真证） | GMATCH_SIMP 于 :5660 | ✓ 签名 `(hp hs hr hnc hn h4 hcey)` → γ/wtcount 槽；经 BETA/NONBETA 体内消费，无需直接调用 |
| 2 | `c_4_azim_mcell_dih_y` | :8222 | ✓（LEAF_RANK_REUHADY + azim_dihv_same + DIHV_EQ_DIH_Y_4PT_B） | :6677 GMATCH_SIMP | ✓ ztg4 装配直供 `azim_mcell = dihY …`，参数序与 ztg4 box 逐一咬合 |
| 3 | `MCELL4_DOMAIN` | :8455 | ✓（CC_4_PROPS + p25m_card4_ne + hp.dist_ge_two） | :6696 INTRO_TAC | ✓ 14 重盒 + rad2YP25 < 2 + 0 < deltaY，盒迁移只需 2√2→√8（mi_sqrt8_eq） |
| 4 | `gammaX_gamma4fgcy_ALT` | :8572 | ✓（PA20 gammaX_gamm4fgcy i:=4 直消费） | :5658 GMATCH_SIMP | ✓ 经 QUARTER/BETA/NONBETA 体内消化 |
| 5 | `GG_MCELL_QUARTER` | :8588 | ✓（2026-10-13 M4 波装配） | —（Lean 先行件） | ✓ 佐证装配模板（hwt=1 支） |
| 6 | `GG_MCELL_BETA` | :8635 | ✓（poolc-w3 W1，p25w3_betaBumpV1_cc4 全临界支） | :5675-5683 正支 | ✓ **即插即用**：正支直接调用，21 参数逐一核对无差槽 |
| 7 | `GG_MCELL_NONBETA` | :8672 | ✓（poolc-w3 W1，非临界支） | :5684-5713 负支 | ✓ **即插即用**：负支直接调用，19 参数逐一核对无差槽 |

配套件核对：`CC_4_PROPS` :7583 ✓ / `cc_4_cc_cell` :7276 ✓ /
`CC_4_BETA_BUMP_EXPLICIT` :7941 ✓ / `CC_4_BETA_BUMP_0` :7956 ✓ /
`p25w3_betaBumpV1_cc4`（六重合取展开器）✓ / `LEAF_RANK_LEAF` ✓。

**判定：七件全部即插即用，签名差槽 = 0。** HOL 证体 :5641-5713 的每一步
（CC_4_PROPS 分解 → cc_4_cc_cell 塌缩 → γ_ALT → wtcount6 → BETA/NONBETA
二分 → beta_bumpA_y 展开 → 算术收口）在 Lean 侧均有已落地同型件或文件内
先例（QUARTER/BETA/NONBETA 三真证即同链产物）。草案一按此写满 43 行证体、
0 sorry。

## 二、ztg4 配件核对表

| 配件 | 锚 | 状态 |
|---|---|---|
| 19 张 bank（GLFVCVK4 + MKFKQWUhalfwt + MKFKQWU + ZTGIJCF4 ×16） | PA21 `pack_nonlinear_rest` :940-961；def :808/:819/:828/:865-895；`proj_bank_*` 具名投影 :3740-3905 | ✓ 全部在库，形状 = 显式盒式 `∀ y…, bounds → 结论 ∨ yOfX rad2X … > 2` |
| ZTGIJCF4 模板 w/m 语义（w = 1+ΣbankGenMid、m = (w=2 ∧ i4=1)） | PA21:850-862 `bank_ZTGIJCF4tmpl` 逐句 + :835-841 doc | ✓ 与 HOL ineq.hl:456-499 一致 |
| 抽查锚（PA21 :887） | 实为 :899-907 `example`（:887 是 0_1_0_0 def 行） | ✓ w'/m 字面量归约 `norm_num [bankGenMid]` 同款可复用（草案 B3 两代表支已按此写） |
| betaBumpLb = −0.005 | IneqClosureDefs:493（+ :497 `bump h0 = −betaBumpLb`） | ✓ |
| `p25w5_bump_mem`（0 ≤ bump ≤ 0.005） | poolc-w6/PackingAuto25.lean:10233（poolc-w5 私件） | ✓ 材料齐（mi_hminus_prop PA21:1892 真证）；落库态见缺口 #4 |
| √8 ↔ 2√2 / 2 ≤ 2hminus / 2hplus ≤ 2√2 | PA21:1652 / :1940 / :1949（mi_* 真证） | ✓ MCELL4_DOMAIN 2√2 界与 bank √8 界无缝衔接 |
| rad2 双态衔接（rad2YP25 vs yOfX rad2X） | PA25:91-101（rad2XP25 重指向 rad2X）+ TEWNSCJ/TXQTPVC_MERGED `:= rfl` 先例 | ✓ |
| sym kit（WLOG 引擎） | PA25 :9582/:9588/:9650 真证（wtcount sym23/26、γ sym26）；**PA21 :10470-10700 kit 全 `private`** | ✗→ 草案 Part A 重装 6 件 + 1 件 sorried（缺口 #1/#2/#3） |
| HOL `REAL_WLOG_SIMPLEX_LEMMA2_LE` 引擎 | merge_ineq.hl:1821 | ✗ Lean 无对应 → ztg4_ALT 本体 sorried（任务书预期内，缺口 #8） |

## 三、缺口清单（memo 之外新发现；按严重度降序）

1. **【高·任务书预期内】HOL ztg4 体 = 320 行 WLOG + 19-shard 覆盖胶合，
   Lean 无引擎对应。** REAL_WLOG_SIMPLEX_LEMMA2_LE（merge_ineq.hl:1821）+
   `ineq_branch_2hmin`/`quarter_norm2hh`/`gamma_wt`/`critical_edge_bound`
   四 helper（:1939/:2159/:2229/:2248）均无 Lean 件。本车道产出
   sorried 骨架（期望战术四步逐支注明）+ 胶合钥匙五件真证 + 两枚代表支
   全真收口（m=1/m=0 各一）。**这是编译窗的主要债（预估 5-10 小时）。**
2. **【中高】PA21 y-space sym kit 全 `private`，PA25 不可消费**
   （p21i_rad2X/rhoX/deltaX/deltaY/dihY/gamma4fgcy 的 sym12/23/03，
   PA21:10470-10700）。ztg4 WLOG 需要 sym23/sym26 两支全套。对策已落草案
   Part A：rhoX_sym23/26P25、deltaX_sym23P25、rad2YP25_sym23/26P25、
   dihY_sym23/26P25 六件 unfold+ring 真证草案（模板 = PA25 gamma4fgcy_sym26
   证内 hD1-hD4/hdy23/hdy26 具名化）。备选：SF-76 落库时顺手去私有（涉及
   PA21 第二文件，patch 面变大，不推荐本波做）。
3. **【中】`gamma4fgcy_sym23` PA25 无具名件**（只有 sym26 :9650）。WLOG
   第一支必需。草案以 `gamma4fgcy_sym23P25` sorried 占位（期望战术：
   按 sym26 模板对 (2 3)(5 6) 重排；solY 12 项置换链索引须编译窗实测）。
   memo 未列。
4. **【低·前置态】`p25w5_bump_mem` 私件可见性 + 落库时序。** 件在
   poolc-w5/w6 快照（poolc-w6 PA25 :10233），主仓 HEAD 无；`private` 限定
   同文件消费——两草案均按「插入 PA25 内部」落位故可见 ✓；若编译窗时
   w5 批次未先行落库，须内联其 ~15 行体（mi_hminus_prop 已真证，材料齐）。
   memo「p25w5_bump_mem 直供」成立，但隐含 w5 先落。
5. **【低·前置态】SF-75 尚未落主仓。** HEAD `1bd6a3fd` 的
   `beta_bumpA_yP25`（PA25:108）与 `beta_bumpA_y_sym23`（:9594）仍 sorry。
   两草案全部按任务书「SF-75 落定后有体」前提起草；编译窗序列必须
   SF-75 → 草案一 → 草案二 串行。
6. **【低】γ 双名 defeq 桥未机验。** real_model_ztg4 装配的
   `exact le_of_lt hz` 依赖 gamma4fgcyP25 ≡ PA20 gamma4fgcy（PA25:124 逐字
   def，gammaX_gamma4fgcy_ALT 在库 exact 级先例）与 a_spine5 ≡ aSpine5
   （PA3 重指向，TEWNSCJ_MERGED rfl 先例）。预期过；兜底 `show` 桥已在
   草案注明。
7. **【低】`beta_bumpA_y_sym26` 缺件**（SF-75 只带 sym23；WLOG 第二支需
   sym26）。两行 `simp only [beta_bumpA_yP25]; ring`，草案已真证化（依赖
   SF-75 体）。memo 未列。
8. **【记录】MCELL4_DOMAIN rad2 槽（rad2YP25 < 2）与 bank shard 析取支
   （yOfX rad2X > 2）双态衔接**靠 rad2XP25 重指向 rfl——非缺口，核对通过
   （TEWNSCJ_MERGED :10421 先例同款），草案 B3 两代表支已按 `heq := rfl`
   写。

## 四、编译窗串行序列建议

SF-75 落库 → 草案一（GG_MCELL_GENERAL 证填，0 sorry，预估 < 1 fix 循环）
→ 草案二 Part A/B（sym + 桥 + 代表支，≤ 1 循环）→ 草案二 Part B4 ztg4_ALT
四步胶合（4-7 循环）→ Part C real_model_ztg4 装配随 ztg4_ALT 闭合自动成立
→ e2e 直源 −1（父 pkrmQu，tsv :155）。

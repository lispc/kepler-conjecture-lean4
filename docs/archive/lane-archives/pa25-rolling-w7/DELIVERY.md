# DELIVERY — pa25-rolling-w7（章节收尾波）

基线：主仓 HEAD 入场时 `726faa79`；工作期间其他车道推进到 `a509e470`，
但 `lean/Kepler/Text/PackingAuto25.lean` **未变**（MD5 `766b6b2a86f6aacce24190a14d9a6077`，
15,417 行 / 12 裸 sorry / 13 编译器 sorry 警告 / 0 error）。本车道只改
`lean/Kepler/Text/PackingAuto25.lean`。

## 1. 闭合件（4 件，全部真证零 sorryAx）

| # | 件 | Work.lean 行 | 证法（一句） |
|---|---|---|---|
| 1 | `real_model_txq` | 14812 | `real_model_cell23_008` 给两 cc 胞 + 余项 ≤ gg；`TXQTPVC_MERGED`（y1=d01, y2=d0i, y3=d0i1, y4=dii1, y5=d1i1, y6=d1i）给 `3·0.0057 ≤ gA' + gB' + (dihY − (d1+d2))·0.008`；`mcell3_gammaX_gamma3f`/`mcell3_gammaXb_gamma3f`/`critical_weight1a`/`critical_weight1b` 把 cc 胞量归一到该形；`azim_mcell = azim u0 u1 (f i) (f (i+1)) = dihY`（`azim_dihv_same` + `DIHV_EQ_DIH_Y_4PT_B`）闭合 d=d'；`ring` + `linarith` |
| 2 | `real_model_tew` | 14928 | 同型但**无 azim 上下界**：直接取 `CC_3_PROPS` 第 33 合取支的 `∃ y4`（含 `dihY … y4 … ≤ azim`、`2 ≤ rad2YP25 … y4 …`、`y4 ≤ 2√2`），`TEWNSCJ_MERGED` 收口；目标侧用 `b_spine5 ≤ 0` + `mul_le_mul_of_nonpos_left` 把 `azim` 换成 `dihY … y4 …`，再 `linarith` |
| 3 | `real_model_pema` | 13927 | `GAMMAX_008b` 消 b-侧（`0 ≤ gB − .008 dB`）；`PEMKWU` 银行取 **(2 3)(5 6) 换位实例**（y2=d0i1, y3=d0i, y5=d1i, y6=d1i1），使 `yOfX gamma23Keep135X` 展开后的 `gamma3f y1 y3 y5` 恰为 a-侧；新桥 `p25w7_gamma23Keep135X_yOfX_eq` 展开 `yOfX`；六个逃逸支全否证（rad2 用 `p25w7_rad2Y_sym23` 归位；`dihY>1.074` 用 `dihY ≤ azim < 1.074`；两个 eta 上界支用 `eta_y < √2`；`eta<1.34²` 支用 `ETA_Y_LEMMA` + `¬(hl<1.34)`） |
| 4 | `real_model_pemb` | 14040 | 同型镜像：`GAMMAX_008a` 消 a-侧；`PEMKWU` 取**自然序实例**（与 `y4` 见证同序，rad2 无需换位）；新桥展开后 `gamma3f y1 y3 y5` = b-侧；六个逃逸支同法否证 |

**W7-A / W7-B 全部落地。** own-sorry **12 → 8**。

## 2. 新增 private kit（4 枚，全零 sorry / 零 admit / 零 native_decide）

| 件 | 行 | 内容 |
|---|---|---|
| `p25w7_rhoX_sym23` | 13880 | `rhoX x1 x2 x3 x4 x5 x6 = rhoX x1 x3 x2 x4 x6 x5`（`unfold; ring`） |
| `p25w7_rad2X_sym23` | 13884 | `rad2X` 的 23-换位（= `p25w7_deltaX` 既证 `p25w4_deltaX_sym23` + 上式） |
| `p25w7_rad2Y_sym23` | 13889 | `rad2YP25` 的 23-换位（y-空间版，`pema` 的 rad2 支归位用） |
| `p25w7_gamma23Keep135X_yOfX_eq` | 13900 | `yOfX (gamma23Keep135X (h0cut y1)) y1…y6 = gamma3f y1 y3 y5 √2 + (dihY y1…y6 − dihY y1 √2 y3 √2 y5 √2)·0.008` —— HOL `Functional_equation.nonf_gamma23_keep135_x` 的 Lean 实装，w6 `p25_gamma23Full8X_yOfX_eq` 同构 |

`dihY` 的 23-换位直接复用本文件既证 `p25w4_dihY_sym23`（PA25:9475），未新增重复件。
`p21i_rhoX_sym23`/`p21i_rad2X_sym23` 在 `TSKAJXY034W3` 内 `private`、跨文件不可见，
故按 w5/w6 惯例同体私拷（仅 3 行证明，非搬债）。

## 3. 整文件读数（命令原文 + 读数）

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q logs/w7-axioms.log lean $S/axioms-probe-pa25-rolling-w7.lean
RC=0
tr -d '\r' < logs/w7-axioms.log | grep -c ': error:'                        -> 0
tr -d '\r' < logs/w7-axioms.log | grep -c ': warning:'                      -> 171
tr -d '\r' < logs/w7-axioms.log | grep -c 'declaration uses `sorry`'        -> 9
wc -l $S/Work.lean                                                          -> 15855
md5  $S/Work.lean                                                           -> 6363af3367799573760fdef59983a46d
```

基线同口径：15,417 行 / 0 error / 175 warning / 13 sorry 警告（= `ox3q1hP25` + 12 裸）。
**own-sorry 12 → 8**；总 warning 175 → 171（恰好少 4 条 = 被替换的 4 条 sorry 警告；
本波 4 件证明体未引入任何新的 unused-variable 警告）。

`ox3q1hP25` 定义体（第 90 行）与基线**逐字一致**（脚本 `cmp` 行 90 → `True`），
624 shard 面未触碰（diff 只落 5 个 hunk：13870 / 13880 / 13892 / 14566 / 14577 区）。

## 4. 补丁与陈述冻结

- `patch-pa25-rolling-w7.diff`：`git apply --stat` → 1 file changed,
  **442 insertions(+), 4 deletions(-)**（4 条 `sorry` 体被替换 + 1 个 helper 块）；
  对主仓当前 HEAD `a509e470` `git apply --check` → **PASS**（只读，未改主仓）。
- 4 件签名与 HEAD `cmp` 逐字一致（正则抽 `theorem <name> … := by` 整段，输出
  `IDENTICAL ×4`；`real_model_pema` 619 字符 / `pemb` 619 / `txq` 614 / `tew` 572）。

## 5. 公理面（原文见 `Evidence.md`）

4 件 + 4 枚新私件 `#print axioms` 全部
`[propext, Classical.choice, Quot.sound]`（零 sorryAx）。

## 6. 残件精确缺口（8 裸 sorry + `ox3q1hP25`，行号为 Work.lean）

| # | 件 | 行 | 分类 | 缺口 |
|---|---|---|---|---|
| 1–2 | `real_model_gamma10` / `gamma11` | 12201 / 12221 | **锥内（W7-C，未闭）** | 见下 §6.1 |
| 3–4 | `real_model_quqy` / `quqy_sym` | 10581 / 10598 | **锥内（未侦察）** | HOL `g_quqya_goal` 区：FHBVYXZ a/b + FWGKMBZ + `cell3_from_ineq`；不是纯装配（见 §6.2） |
| 5 | `pkLeafRankCriticalEdge` | 9877 | 锥外（深水） | `CELL_CLUSTER_*` 链 |
| 6–7 | `CELL_CLUSTER_ESTIMATE_REDUCE` / `CELL_CLUSTER_N_LE_1` | 6155 / 6503 | 锥外（深水大件） | — |
| 8 | `real_model_ox3q1h_merge` | 9954 | 锥外（DEFHOLE） | 需 `hox : ox3q1hP25`（DEF-FIX 冻结） |
| — | `ox3q1hP25` | 90 | DEFHOLE | DEF-FIX 专属，冻结 |

### 6.1 gamma10/gamma11 缺口（本波侦察结论：**不是 3 座小桥**）

工单估计「缺 `rad2_eta2` + `beta_bumpA_lb1` + `beta_bumpA_lb1` 三桥」，实测**低估**。
HOL 链是 `real_model_gamma10` → `gamma10_gamma11_ALT` → `gamma10_gamma11`
（`merge_ineq.hl:3997-4085`），**三件 Lean 全无**。逐级缺口：

1. `gamma10_gamma11`（70 行）本身不在 Lean。其前提是四银行的**同时消解**
   （`proj_bank_GLFVCVK4*` / `proj_bank_QITNPEA5400790175a,b` / `proj_bank_FWGKMBZ`），
   且内含 `wtcount6_y = 2` 与 `= 1` 两支的临界性记账、`quarter_norm2hh`
   否证支、`eta_y y1 y2 y6² < 1.34²` 三分支。
2. `rad2_eta2` 需要新分析核 `rad2_x_eta_x`（HOL `merge_ineq.hl:3844`）：
   `0<x4,x5,x6 ∧ 0<ups_x x4 x5 x6 ∧ 0<delta_x x1..x6 ⇒ eta_x x4 x5 x6² ≤ rad2_x x1..x6`。
   Lean 侧缺 `UPS_X_POS`（`upsX x4 x5 x6 > 0` 的非共线版）与
   `rad2_x_sym03`（`rad2X x1 x2 x3 x4 x5 x6 = rad2X x4 x5 x3 x1 x2 x6`）——
   `p21i_rad2X_sym{12,23,03}` 是 PA21 `TSKAJXY034W3` 内的 `private`，且 `sym03`
   的槽形与本处 HOL 用的 `rad2_x_sym` **不同**，要另立。
   证明主恒等式：`rhoX x1..x6 * upsX x4 x5 x6 = 4 * deltaX x1..x6 * (x4*x5*x6) + S^2`
   （HOL `Collect_geom.RHUFIIB` + `delta_delta_x`），须引入点积原子做 `ring`
   （`p25_radv_etay_core` / `GDRQXLGv3` 同款路线）。
3. `beta_bumpA_lb1`：`betaBumpLb ≤ betaBumpA_yP25 y1..y6`（`betaBumpLb = -0.005`；
   体已真，见 PA25:113，用 `0 ≤ bump ≤ 0.005`）。**这一座确实是小桥**。
4. `critical_weight1a/1b`、`GG_MCELL_GENERAL`、`mcell3_gammaX{,b}_gamma3f`、
   `MCELL4_DOMAIN`、`wtcount6_y_sym23`、`beta_bumpA_y_sym23`、`ztg4w1_quarter_norm2hh`
   **均在库**，装配面不缺。
5. `gamma4fgcy_sym23` 在 Lean 无同名件（需核 `gamma4fgcyP25` 的 23-换位是否另有具名件）；
   `norm2hh`/`betaBumpLb`/`etaX` 在 `IneqClosureDefs` 有体。

**结论**：W7-C 是一整波（≈ 1 个 40–80 行分析核 + 1 个 70 行银行组合 + 2×50 行装配），
不是本波余量能收的装配件。已写入 `WORKORDER-w8.md` 并给出逐条起手点。

### 6.2 quqy/quqy_sym 侦察（新增情报）

HOL `g_quqya_goal` / `g_quqya_g_quqyb`（`merge_ineq.hl:3932-3980`）显示
`real_model_quqy` 的目标是 `0 ≤ gamma4fgcy + gamma3f`（**不是** 0.0057 型），
前提 `rad2_y < 2`，银行面 = `FHBVYXZ a/b` + `FWGKMBZ` + `cell3_from_ineq`，
同样需要 `rad2_eta2` 的 `eta_y² < 2` 跳出支。**与 gamma10/11 共享受阻点**：
`rad2_eta2` 一落地，quqy/quqy_sym 与 gamma10/11 四件可同波收割。

## 7. 章节收尾判定

**PA25 尚不能宣布收尾**。锥内残件 4 件（gamma10/11 + quqy/quqy_sym），
锥外 4 件（`CELL_CLUSTER_*` ×2、`pkLeafRankCriticalEdge`、`real_model_ox3q1h_merge`）
+ `ox3q1hP25` DEFHOLE。若 w8 收掉锥内 4 件，则 PA25 只剩
「`ox3q1hP25` + 锥外深水 3 件 + `ox3q1h_merge`（DEFHOLE 依赖）」，**届时可宣布
章节收尾（除 DEFHOLE）**。

## 8. 搬债审计

- 逐个 `grep` 新增 442 行对 8 个仍-sorry 声明 + `ox3q1hP25` 的引用：**全部 0**。
- 新引用依赖面全为既证件：`real_model_cell23_008`、`GAMMAX_008a/b`、`CC_3_PROPS`、
  `JSP_BOUNDS`、`proj_bank_PEMKWU`、`TXQTPVC_MERGED`、`TEWNSCJ_MERGED`、
  `cell3_from_ineq_thm`（经 `critical_weight1a/b`）、`MCELL4_DOMAIN`、
  `mcell3_gammaX_gamma3f`、`mcell3_gammaXb_gamma3f`、`mcell3_dihX_dih_y`、
  `mcell3_dihXb_dih_y`、`mi_gamma3_x_gamma3f`、`mi_gamma3f_sym`（经上两者）、
  `ETA_Y_LEMMA`/`ETA_Y_LEMMA_ALT`/`ETA_Y_POS_LE_ALT`、`GDRQXLGv3`、
  `RAD_PI_IMP_WEDGE4`、`DIST_I_SUCI`、`CC_3_AZIM_LT_PI_COPLANAR`、
  `coplanar_delta_y`、`DIHV_EQ_DIH_Y_4PT_B`、`azim_dihv_same`、
  `p25w4_deltaX_sym23`、`p25w4_deltaX4_sym23`、`p25w4_dihY_sym23`。
- **零搬债**；K-SORRIED 地图快照若刷新应见 119 → 115。

## 9. 预算自报

- 调用 ~68（上限 120）；墙钟 ~2h20m（上限 3h）。
- 探针：`p-txq.lean`、`p-tew.lean`、`p-pema.lean`、`p-pemb.lean`（各单文件 RC=0）；
  关键提速：`lean/.lake/build/lib/lean/Kepler/Text/PackingAuto25.olean` 可用，
  探针改 `import Kepler.Text.PackingAuto25` 后单轮 ~20s（原整文件 5–6min/轮）。
- 整文件 standalone 编译 3 次（基线 / w7 集成 / axioms 尾），未触 `lake`，
  未改 `lean/.lake/`，未写其它车道 scratch。

## 10. 交付物清单（`$S = /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w7/`）

```
patch-pa25-rolling-w7.diff        442+/4-，git apply --check PASS（HEAD a509e470）
Work.lean                         15855 行，RC=0 / 0 error / 171 warning / 9 sorry 警告
axioms-probe-pa25-rolling-w7.lean  （= Work.lean + 8 条 #print axioms）
WORKORDER-w8.md
DELIVERY.md（本文件）
Evidence.md
logs/                             base-full / p0 / p-txq / p-tew / p-pema / p-pemb / w7a-full / w7-axioms
probe/                            探针源（p-txq/tew/pema/pemb.lean，仅取证）
```

未建 `Kit-draft-pa25-rolling-w7.lean`：所有改动都在 `Work.lean` 内且整文件
RC=0 / 0 error；无「修不完的件」需移出 kit（gamma10/11/ quqy 保持原样 `sorry`，
未做半途改动——它们的陈述与基线逐字相同）。

归档（仓内，显式要求的未跟踪工件）：`docs/archive/lane-archives/pa25-rolling-w7/`
（patch + DELIVERY + Evidence + WORKORDER-w8；Work.lean 不入库）。

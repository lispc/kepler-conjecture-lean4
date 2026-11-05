# DELIVERY — pa25-rolling-w8（接 w7）

> 基线：主仓 `0e2e2dd4`（w7 落库后；PA25 MD5 `6363af3367799573760fdef59983a46d`，
> 15,855 行 / 8 裸 sorry / 9 条编译器 sorry 警告 / 0 error）。收尾时 HEAD 已被
> 其它车道 docs 提交推进到 `7e5ed1c1`，PA25 仍为基线字节，patch `git apply --check`
> 通过。本波唯一改动文件：`lean/Kepler/Text/PackingAuto25.lean`；主仓 tracked
> 零改动（收尾 `git status` 干净）。
> patch 头 `a/lean/Kepler/Text/PackingAuto25.lean`，`git apply --check` 通过。

## 1. 结论表

| 件 | 新文件行 | 判定 | 证法（模块内锚点） |
|---|---|---|---|
| W8-A `p25w8_rad2_x_eta_x` | 10600 | **CLOSED** | HOL merge_ineq.hl:3841；`etaX² = x4x5x6/upsX`（`Real.sq_sqrt`）+ 恒等式 `rhoX·upsX = chi² + 4·deltaX·x4x5x6`（chi 与 `EDGE_LE_2RAD`:7500 内联式逐字相同）+ `div_le_div_iff₀` |
| W8-A `p25w8_upsX_sq_pos`（UPS_X_POS） | 10582 | **CLOSED** | HOL merge_ineq.hl:2917；Heron 因式 `(a+b+c)(a+b-c)(a-b+c)(-a+b+c)`，由 `2≤a,b,c<4` 四因子正 |
| W8-A `p25w8_rad2_eta2` | 10628 | **CLOSED** | rad2_x 的 `(x1 x4)(x2 x5)` 槽对称（新私件 `p25w8_{deltaX,rhoX,rad2X}_sym14`，纯 `ring`）+ `p25w8_rad2_x_eta_x` 实例化 `(y4²,y5²,y3²,y1²,y2²,y6²)` |
| W8-B `real_model_gamma10` | 12455 | **CLOSED** | `critical_weight1a`(i+1) + `GG_MCELL_GENERAL`(i) + `mcell3_gammaX_gamma3f`(i+1) + `p25w8_gamma10_gamma11`(sym23 换位元组) + `MCELL4_DOMAIN`(i)；y4≥2hmin 由 `hnot` 反证 |
| W8-B `real_model_gamma11` | 12502 | **CLOSED** | `critical_weight1b`(i) + `mcell3_gammaXb_gamma3f`(i) + `GG_MCELL_GENERAL`(i+1) + `p25w8_gamma10_gamma11`(自然元组) + `MCELL4_DOMAIN`(i+1) |
| W8-B 分析核 `p25w8_gamma10_gamma11` | 12368 | **CLOSED** | `FWGKMBZ`→delta>0、`GLFVCVK4`→gamma>0（norm2hh 支撞 y4≥2hmin）、`QITNPEA5400790175a/b` 按 `eta²<1.34²` 二分、`cell3_from_ineq_thm`→gamma3f≥0、`betaBumpLb_le_beta_bumpA_yP25`、wtcount6=1/2 二分 |
| W8-C `real_model_quqy` | 10709 | **CLOSED** | `GG_MCELL_QUARTER`(i) + `critical_weight1a`(i+1) + `mcell3_gammaX_gamma3f`(i+1) + `p25w8_g_quqya`(sym23 元组，私件 `p25w4_*_sym23`) |
| W8-C `real_model_quqy_sym` | 10748 | **CLOSED** | `critical_weight1b`(i) + `mcell3_gammaXb_gamma3f`(i) + `GG_MCELL_QUARTER`(i+1) + `p25w8_g_quqya`(自然元组) |
| W8-C 分析核 `p25w8_g_quqya` | 10656 | **CLOSED** | `FWGKMBZ`→delta、`FHBVYXZa/b`（按 `eta²<1.34²` 二分）+ `cell3_from_ineq_thm` + `p25w8_rad2_eta2` |
| W8-D `CELL_CLUSTER_ESTIMATE_REDUCE`(6150) | — | **PROVABLE（未施工）** | 纯归约；`criticalEdgeX` 定义已含 `∈ edgeX`，故任意簇边自动是 2 元集 + 临界带，直接 `hedge`；空簇支 `setSum ∅ = 0`。估 60–120 行 |
| W8-D `CELL_CLUSTER_N_LE_1`(6498) | — | **PROVABLE（未施工）** | HOL OXLZLEZ3.hl:4186 路线；在库件齐：`MCELL4_EDGE_FIRST`(PA18) + `S_LEAF_CARD2`(3922) 排 4 胞，`EDGE_IMP_K2` + `GAMMAX_NO_BETA`(1793) + `TSKAJXY_2`(PA21:9141)/`TSKAJXY_3`(3610) 逐和项非负。估 150–300 行 |
| W8-D `pkLeafRankCriticalEdge`(9869) | — | **BLOCKED（上游两件未施工）** | 装配依赖上面两件（stub docstring 已自述）；两件落地后本件 ≈100 行 |
| W8-D `real_model_ox3q1h_merge`(9930) | — | **BLOCKED（DEFHOLE）** | 前提 `hox : ox3q1hP25` 而 `ox3q1hP25`(90) 是 DEF-FIX 冻结的 `:= sorry`，内容未知，不可证 |

**章收尾判定**：PA25 剩余债面已是 `ox3q1hP25`(DEFHOLE) + `CELL_CLUSTER_*`×2 +
`pkLeafRankCriticalEdge` + `real_model_ox3q1h_merge`（后四者中的两者依赖前两者、
末者依赖 DEFHOLE）——按 WORKORDER-w8 §6 判定线，**章节可宣布收尾（除 DEFHOLE）**。

## 2. 数字（实测）

| 指标 | 基线 `0e2e2dd4` | 本波后 |
|---|---|---|
| 行数 | 15,855 | 16,187（+332） |
| 裸 sorry | 8 | **4** |
| 编译器 sorry 警告 | 9 | **5**（4 裸 + `ox3q1hP25` DEFHOLE） |
| error | 0 | **0**（standalone 全文件，RC=0） |
| MD5 | `6363af3367799573760fdef59983a46d` | `2c18464087f8f871ae0b92468900b4bd` |
| patch | — | +336 / −4（删除面逐行 = 4 条 `  sorry`） |

## 3. 验收（`#print axioms`，逐字）

全文件 standalone 编译（含末尾 print，见 `logs/full_print.log`）：

```
'Kepler.Text.real_model_quqy'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_quqy_sym'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gamma10'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gamma11'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_rad2_eta2'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_rad2_x_eta_x'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_g_quqya'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.p25w8_gamma10_gamma11' depends on axioms: [propext, Classical.choice, Quot.sound]
```

零 `sorryAx`。删除面：恰好 4 条 `  sorry`（quqy/quqy_sym/gamma10/gamma11 的体），
陈述签名逐字未动；`ox3q1hP25`(PA25:90) DEFHOLE 未触；624 shard 面零接触
（无新 import / 无 axiom / 无 native_decide）。

## 4. 勘误与雷区（本波新增）

1. **工单 §1 第 2 条字面 `UPS_X_POS : 0<x4 ∧ 0<x5 ∧ 0<x6 → 0<upsX x4 x5 x6` 是假命题**
   （反例 `upsX 1 1 9 = -45`）。HOL 真件（merge_ineq.hl:2917）是 **y-空间平方长**形：
   `2 ≤ a,b,c ∧ a,b,c < 4 → 0 < upsX (a²) (b²) (c²)`，已按此立项为
   `p25w8_upsX_sq_pos`。`rad2_x_eta_x` 保持 HOL 原样，`0 < upsX x4 x5 x6` 是**假设**。
2. `rhoX·upsX` 恒等式的 `chi` = `EDGE_LE_2RAD`(:7500) 内联式；本波未重复发明。
3. `gamma10_gamma11` 采用「`hnl` + 四银行投影」单层收敛形（等价于 HOL
   `gamma10_gamma11` + `_ALT` 两层），未另立 `_ALT` wrapper。
4. **前向引用**：quqy(10709) 在 `gamma4fgcy_sym23P25`(11032)/`rad2YP25_sym23P25`(10970)
   之前，故必须用同文件更早的私件 `p25w4_gamma4fgcy_sym23`(9521) /
   `p25w4_rad2YP25_sym23`(9509)（private 同文件可见）。首轮整编即因用公开名报
   unknown identifier，已修。
5. 两处 `set_option maxHeartbeats 8000000 in`（仅预算修饰，陈述未动）。
6. `Real.lt_sqrt_of_sq_lt : x² < y → x < √y`（本 Mathlib 名）；`div_le_div_iff₀` 带
   两个 `0 <` 参数（承 w6 雷区）。
7. 整编耗时：本机全文件 standalone 约 4–5 分钟（olean 依赖就绪时）。

## 5. 产物

- `patch.diff` / `patch-pa25-rolling-w8.diff`（同内容，前者按父任务命名）
- `Work.lean`（改动后全文件，16,187 行，MD5 `2c18464087f8f871ae0b92468900b4bd`）
- `DELIVERY.md`、`Evidence.md`、`WORKORDER-w9.md`
- `logs/`：`full_print.log`（整编 + #print axioms，RC=0）、`full_w8a_b_c.log`
  （首轮整编，含前向引用 2 error，留档）、`probe1/2/3.log` + 三份探针源码
- 仓库归档 `docs/archive/lane-archives/pa25-rolling-w8/`：按父任务「主仓零改动」
  纪律**未直接写入主仓**；编排者可用本目录四件（patch/DELIVERY/Evidence/
  WORKORDER-w9）原样归档（Work.lean 不入库，与 w7 同制）。

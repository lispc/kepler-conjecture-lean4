# DELIVERY — la33-straight-w1

- 目标文件：`lean/Kepler/Text/LocalAuto33.lean`
- 开工 HEAD：`8c003d0d`；收尾时主仓 HEAD 已被其它车道推进到 `8635c297`。
  目标文件内容在两者之间**未变**（`diff` 实测），kit 对当前工作树/HEAD 均可应用。
- 编译口径：standalone
  `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q <log> lean <file>`
- 零新 import、零 `admit`/`native_decide`、零新增 `sorry`、未用 `open Classical`。
- 三个目标签名逐字冻结（Python 逐字比较 HEAD vs Work：`SIGNATURE-FROZEN: True` ×3）。

## 1. 闭合件（2 / 3）

| # | 件 | 行 | 证法一句话 | `#print axioms` |
|---|----|----|-----------|-----------------|
| 1 | `SCS_4I2_STRAIGHT_p33` | :2059 | `ear_acute_p33` 的 `dihY < π/2` 经 `azim = dihV`（`azim_dihv_same/_compl`）+ `dihV = dihY`（`DIHV_EQ_DIH_Y_4PT_B`）搬到 `azim < π/2`（`azim ≥ π` 支被 `ConvexLocalFan` 的楔形界 `azim ≤ π` 杀死），再用 `sum4_azim_fan` 沿扇区 `(v i, v(i+1), v(i+2), v(i+3))` 相加得 `< π` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `SCS_4I2_STRAIGHT_ALL_p33` | :2065 | 四残类实例化件 1，配 4-周期改写 `v 4 = v 0`、`v 5 = v 1`、`v 6 = v 2` | `[propext, Classical.choice, Quot.sound]` |

新增私有助件（sheet 内、无 sorry）：`upsX_pos_of_noncollinear_p33`（Gram/Cauchy–Schwarz
的 `upsX > 0`）、`azim_lt_half_pi_of_dihY_p33`、`azim_lt_half_pi_of_dihY_swap_p33`
（两条 `azim`/`dihY` 耳桥，第二条用 `DIHV_SYM_2` + `dist_comm`）。

关键几何输入（均实测 standard three）：`ConvexLocalFan`（`BBsV39` 第 4 合取，
经 `BBS_IMP_CONVEX_LOCAL_FAN_p34`）；该 fan 的 `hcvx` 给出
`azimInFan (v i, v(i+1)) E = azim 0 (v i) (v(i+1)) (v(i+3)) ≤ π` 与
`∀ w ∈ range v, azim 0 (v i) (v(i+1)) w ≤ azim 0 (v i) (v(i+1)) (v(i+3))`
（后者即 `sum4_azim_fan` 的排序前提）。为此在文件内证明了
`ee (v i) E = {v(i+1), v(i+3)}`（`BB_VV_FUN_EQ_p26` + 4-周期）与
`Fan.sigmaFan 0 univ E (v i) (v(i+1)) = v(i+3)`（`setOfEdge` 两点集 + ε-唯一性）。

## 2. BLOCKED：`MM_4I2_IMP_4T2_4T1_p33`（:2126，做保留 `sorry`，未结构闭合）

按编排者 2026-11-05 口径：所需前置 TAINTED → 目标判 BLOCKED，不结构闭合。

精确缺口表：

1. HOL 路线（`ARDBZYE.hl:2339-2514`）经 `ASSUME_MIN_DIAG` 后二分
   `dist(v(i+1),v(j+1)) = 3 ∨ 3 < dist(...)`（用 `SCS_4I2_3_LE_A` 的下界）。
   - `= 3` 支：可闭（`DIST_DIAG_2_CASES_EQ_3_p33` → 全部对角 = 3 → `BBsV39 scs4T2 v`
     → `XWNHLMD_MM_p33`）。所需前置实测全部 standard three。
   - `3 <` 支：HOL 用 `EDGE_EQ_2_4I2_ALL`（`ARDBZYE.hl:2282`）得
     `∀ k, dist (v k) (v (k+1)) = 2`，再走 `scs4T1`（其边 b = 2）。
2. 该前提的 Lean 孪生 `Kepler.Text.EDGE_EQ_2_4I2_ALL_p33`
   （`LocalAuto33.lean:2428`）当前是 `:= sorry` —— 实测
   `#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]` (TAINTED)。
3. 其 HOL 证明（`ARDBZYE.hl:2282-2332`）= 四个 `EDGE_EQ_2_4I2_{,1,2,3}`
   （`:1965/:2118/:2235/:2256`）实例，每个都是 `CJBDXXN`
   （`CUXVZOZ.hl:4319`，调用点如 `ARDBZYE.hl:2140`）在 `p1 = i+1` 等处的实例；
   `CJBDXXN` 的结论正是 “对角 > 3 ⇒ 相应边 = 2”（check completeness）。
4. Lean 侧 `CJBDXXN_p21`（`LocalAuto21:1225`）**不在** `LocalAuto33` 的 import
   闭包（BFS 闭包 120 模，无 `LocalAuto21`），且其体为
   `general_482_deformation_p21`（`LocalAuto21:1178`）= `:= sorry`
   （HOL `CUXVZOZ.hl:3649`，640 行）。闭包内 grep
   `EDGE_EQ_2` / `CJBDXXN` / `general_482` 均无 clean 孪生。
5. 非空洞性：纯度量约束不足以推出 “边 = 2”（随机搜索到满足 4I2 a/b 表与
   `d_02 ∈ [3,3.01] < d_13` 的 4 点构型：边 2.42/2.05/2.31/2.24，对角 3.008/3.356），
   故该支确实需要 `main_nonlinear_terminal_v11` 的终端形变内容，不能以纯几何替代。
6. 搬债状态：`MM_4I2_IMP_4T2_4T1_p33` 在 TSV 中有 1 行（`parent=Kepler.Text.ARDBZYE_p33`，锥内）；
   本波不动它（保持 SORRIED），`general_482_deformation_p21` 亦仍在锥内 1 行
   （`parent=Kepler.Text.CUXVZOZ_p21`）——无新增债行。

## 3. 前置审计（编排者口径：每条同时验 (a) 闭包内 #check、(b) #print axioms）

`#check` 全部通过（`p1.log`）；`#print axioms` 原文见 `Evidence.md` §3，
**全部 = `[propext, Classical.choice, Quot.sound]`**（32 条，含
`XWNHLMD_MM_p33` —— 其文件内 docstring 声称的 sorryAx 注记已过时，实测 clean）：

- 本车道 3 件的前置：`MMs_imp_BBs_p33`、`EDGE_4I2_LE_2H0_p33`、`SCS_4I2_3_LE_A_p33`、
  `SCS_DIAG_4_ADD0_p33`、`SCS_DIAG_4_ADD2_p33`、`SCS_DIAG_ADD1_p33`、
  `DIST_DIAG_2_CASES_EQ_3_p33`、`ASSUME_MIN_DIAG_p33`、`SCS_4I2_IS_SCS_p33`、
  `SCS_4T1/4T2_IS_SCS_p33`、`SCS_4I2/4T1/4T2_BASIC_p33`、`K_SCS_4I2/4T1/4T2_p33`、
  `SCS_4I2_GENERIC_p33`、`ear_acute_p33`、`BB_VV_FUN_EQ_p26`、`BB_RHO_NODE_IVS_p26`、
  `XWNHLMD_MM_p33`、`ballAnnulus_norm_bounds`、`WL_IN_BALL_ANNULUS_p28`、
  `NORM_LE_2_IN_BBS_p28`、`MMS_IMP_BBS_p28`。
- 新引入的库引理：`PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14`、`BBS_IMP_CONVEX_LOCAL_FAN_p34`、
  `IN_V_IMP_AZIM_LESS_PI`、`sum3_azim_fan`、`sum4_azim_fan`、
  `DIHV_EQ_DIH_Y_4PT_B`、`DIHV_SYM_2`、`azim_dihv_same`、`azim_dihv_compl`、
  `azim_nonneg`、`azim_lt_two_pi` —— 全部 standard three（同上 probe）。

## 4. 搬债审计（以 `docs/e2e-reachability-map.tsv` 行）

- `SCS_4I2_STRAIGHT_p33`：`grep` 0 行 → 不在锥（无债行）。
- `SCS_4I2_STRAIGHT_ALL_p33`：0 行 → 不在锥。
- `MM_4I2_IMP_4T2_4T1_p33`：1 行，`parent=Kepler.Text.ARDBZYE_p33` → 锥内，保持 SORRIED（未动）。
- 新体引用的每个件均查：全部在闭包内且 `#print axioms` 标准三；**没有一个 sorried 件被新体消费**
  （两件标准三公理即充分证明；无 sorryAx）。
- 本波无 import 变化 ⇒ 不需 BFS 无环证明/漂移核（未做，不适用）。

## 5. 验收读数

- own-sorry 声明数：**11 → 9**（`grep -c 'declaration uses \`sorry\`'`，基线 `base.log` vs 终版 `final.log`）。
- 整文件错误数：**0 → 0**（`grep -c ': error:'`）。
- 整文件 RC：`script ... lean Work.lean` → `COMPILE_RC=0`（`final.log`）。
- kit：`git apply --check` 对 HEAD **PASS**；`git apply --stat` 只显示
  `lean/Kepler/Text/LocalAuto33.lean | 336 +++...`（1 file, +330/−6）。
- 预算：约 72 次工具调用；挂钟 13:12→13:47（约 35 分钟），远在 ≤120 调用 / ≤3h 内。

## 6. 产物

- `$S/kit-la33-straight-w1.diff`（仓相对双头 `a/lean/...` / `b/lean/...`）
- `$S/Work.lean`（剥离探针尾后的终版；与 `final.log` 的 RC=0 编译对象逐字节一致）
- `$S/DELIVERY.md`、`$S/Evidence.md`、`$S/logs/`（base / p1 / p2 / p3 / sh1 / port1 / port2 / axprobe / final）
- 无 `Kit-draft-*.lean`（未闭件是原文件已有的 sorry，其助件不存在；本车道助件仅被两件闭合件消费，全部入 kit）
- 入库归档：`docs/archive/lane-archives/la33-straight-w1/{kit-la33-straight-w1.diff, DELIVERY.md, Evidence.md}`

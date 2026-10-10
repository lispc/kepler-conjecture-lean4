# grutoti-scout — GRUTOTI（短边二面角和 2π）GIANT 侦察报告（零改动只读侦察）

> 2026-09-29 侦察 lane 交付。对照基准 `lean/scripts/packing/GRUTOTI.hl`（与
> `reference/flyspeck/text_formalization/packing/GRUTOTI.hl` 经 `diff -q` 逐字节相同，
> 8005 行，模块 Grutoti，Vu Khac Ky 2012）。所有 file:line 经 grep/sed 实测核对；
> 纪律：零 .lean 改动、零 git 写操作、未跑 lake build / auto_gate。
>
> **核心结论先行**：
> ① **"尚未移植"已过时——PA23 骨架+capstone 在树**：`Kepler/Text/PackingAuto23.lean`
> （341 行，2026-09-19 过）已把 HL 单块 8005 行 `prove_by_refinement`（636 NEW_GOAL）
> 重构成"9 件已证机械链 + **5 枚 sorried giant** + 已证 capstone `GRUTOTI`"的骨架；
> 剩余工作 = 填 5 枚 giant，**不是**从零移植。
> ② **实际量级 = Lean 2800–5000 行**，全仓最大单章之一（HL 中三大案例块合计 ~4560 行
> tactic）。5 枚 giant 中 `grutoti_region`（HL 161–2636，~2476 行）与
> `grutoti_cell_vol`（HL 2652–7958，~5300 行）是双 GIANT；其余三枚（volD_pos /
> sum_volD / pivot）合计 S/M 档 ~350–700 行。
> ③ **三座共享银行决定排期**：(a) **锥帽体积套件**（VOLUME_CONIC_CAP /
> VOLUME_CONIC_CAP_WEDGE，源在 flyspeck_multivariate.ml、**不在本仓 reference 树**）
> 与 PA24 REUHADY 链的 `volumeConicCapWedgeGeVsConicCap`（PA24:428，sorried）同一缺口
> ——建一次双银行；(b) **Pack2.hl 测度桥**（MEASURE_NEGLIGIBLE_UNIONS_IMAGE 等）与
> UPFZBZM wave 2 的 KIZHLTL1 同一缺口（upfzbzm-scout 已标注"Lean 侧无移植"）；
> (c) **PA15 marchal3 骨架 19 sorries 中至少 9 枚**是 GRUTOTI 传递依赖
> （FINITE_EDGE_X2、MCELL_SUBSET_BALL8_1、FINITE_MCELL_SET_LEMMA_2、
> MCELL_SUBSET_BALL_4、HL_LE_SQRT2_IMP_BARV_1、MCELL_ID_OMEGA_LIST_N/MXI、
> DIHX_SYM、CONIC_CAP 三件套）。此外 PA10.HDTFNFZ / PA11.LEPJBDJ(_0) /
> PA17.AJRIPQN / PA12.VORONOI_LIST_3_SINGLETON_EXPLICIT 四枚上游 giant 也直接 sorried。
> ④ **GT-3（cell_vol）与 GT-4（region）相互独立可并行**：PA23 capstone 组装已写好
> （PA23:330–339 全 proved 调度），五枚 giant 只是五张独立欠条；建议按
> GT-1（共享银行）→ GT-2（机械收尾）/ GT-3 / GT-4（三线并行）排期。
> ⑤ **最小可交付波 = GT-1**（锥帽体积套件，400–800 行，同时解锁 GRUTOTI 与 REUHADY
> 两条链的入场券）；GRUTOTI 整链闭合 = GT-1+2+3+4 全收，届时
> `PackingConcl.GRUTOTI1_concl_discharged`（PackingConcl.lean:603）的 sorryAx 断流。

---

## §0 定位与消费链（Lean 侧实测）

### 0.1 HOL 源

- `lean/scripts/packing/GRUTOTI.hl`，8005 行；`module Grutoti`，open 29 个模块
  （Rogers/Pack1/Pack2/Packing3/Marchal_cells_2_new/Urrphbz*/Qzyzmjc/
  Upfzbzm_support_lemmas 等）。全文只有**一个定理**：陈述 `GRUTOTI1_concl`
  （:48–58）+ `prove_by_refinement` 巨块（:60–8001，**636 个 NEW_GOAL**，无显式
  子引理）。
- 陈述：`!V u0 u1 e. saturated V /\ packing V /\ u0 IN V /\ u1 IN V /\ ~(u0=u1) /\
  hl [u0;u1] < sqrt 2 /\ e = {u0,u1} ==> sum {X | mcell_set V X /\ e IN edgeX V X}
  (\t. dihX V t (u0,u1)) = &2*pi` —— 饱和堆积中一条短边（hl<√2）两侧所有 Marchal
  胞的二面角之和 = 2π（"边周围张角账本闭合"）。

### 0.2 Lean 侧落点与接线（全树 grep 实测）

```
PA2.GRUTOTI1_concl (PackingAuto2.lean:1280, sorry)          ← 接口陈述（pack_concl.hl:294-304 同形）
PA23.GRUTOTI (PackingAuto23.lean:325, 本体已证组装)          ← 5 枚 private giant sorried，capstone 待喂
  ├─ PA24.GRUTOTI1_concl_p24_pub (PA24:488-517, 现走 PA2 sorried)
  │    └─ PackingConcl.GRUTOTI1_concl_discharged (PackingConcl.lean:603, exact p24_pub)
  │         └─ #print axioms 锚点 (PackingConcl.lean:763)
  └─ PA25.LEAF_RANK_GRUTOTI (PackingAuto25.lean:1603, sorry；docstring 自述
       "consumes GRUTOTI via REUHADY"——leaf-rank 链的下游银行，非直接 import)
import 方向：PA23 ← {PA2, PA6, PA12, PA15}；全树**零文件 import PA23**
（PackingConcl.lean:96 明注 "PackingAuto23 — hosts no twin"）；PackingConcl 目前
不经 PA23 走线。PA24 ← {PA2, PA5, PA6, Polytope, Geom.Azim}：PA24/PackingConcl 加
import PA23 均无环（PA23 不 import 任何下游）。
```

- 消费形态固化：PA23.GRUTOTI 陈述与 `PA2.GRUTOTI1_concl` **逐字同形**（PA23:322-325
  注记 `exact GRUTOTI …` 一行即可 discharge）；PA24 已备 `_p24` 拷贝+公开 re-export
  桥。merge 时两选一：PackingConcl 加 `import PackingAuto23` 直接
  `exact PA23.GRUTOTI`，或把 PA24:504 的 `exact GRUTOTI1_concl …` 改指 PA23（推荐
  后者，diff 最小）。本侦察不裁决，留编排者。
- PA23 内部 5 枚 sorried giant（真实 sorry 恰 5 处：:263/:277/:289/:303/:317；
  其余 4 处 "sorry" 均在 docstring）：
  `grutoti_region`、`grutoti_cell_vol`、`grutoti_sum_volD`、`grutoti_pivot`、
  `grutoti_volD_pos`。已证机械件 9 枚：barV（shim→PA15）、trunc1、3mem、vor_cover
  （已填，吃 PA12 shim）、cap_subset_closedBall/ball、cap_rcone_mono、
  setSum_mul_div、cancel、concl_arith。

## §1 HOL 侧全图（GRUTOTI.hl 区间解剖）

### 1.1 十段区间行数表

| 段 | 行号 | 行数 | 内容 | Lean 现状 |
|---|---|---|---|---|
| §0 | 1–59 | 59 | 头/opens/陈述 | —（PA23 已落地） |
| §A | 60–160 | 101 | barV（HL_LE_SQRT2_IMP_BARV_1）+ GLTVHUM_lemma1 的 k∈1..3 集 + k=3 Voronoi/Rogers 覆盖 | ✅ 已证/shim/filled |
| §B | 161–2636 | **2476** | **region 块（giant 1）**，见 1.2 | ❌ grutoti_region sorry |
| §C | 2649–2664 | 16 | `D = conic_cap u0 u1 r d` 重写 + 每胞楔形体积目标 | ✅/❌ 边界 |
| §D | 2665–3739 | **1075** | **Case k=2**（giant 2 之一臂）：mcell2 = 双 rconeGe ∩ affGe{u0,u1}{mxi,ω₃}，`vol(X∩D) = vol(L∩D)`（L=aff_ge 楔），VOLUME_CONIC_CAP_WEDGE 收 | ❌ grutoti_cell_vol |
| §E | 3740–5461 | **1722** | **Case k≥4**：mcell4 全共面 → COPLANAR_IMP_NEGLIGIBLE 空交复读（34 次）+ LEPJBDJ/HDTFNFZ 截断分解 | ❌ 同上 |
| §F | 5462–7225 | **1764** | **Case k=3**：mcell3 = hull{u0,u1,v₂,mxi}，楔形 + **AZIM_COMPL** 补角恒等式（:7197–7223） | ❌ 同上 |
| §G | 7226–7505 | 280 | `sum s (vol(t∩D)) = vol D`：MEASURE_NEGLIGIBLE_UNIONS_IMAGE + FINITE_EDGE_X2 + D⊆ball1 + MCELL_SUBSET_BALL8 覆盖 | ❌ grutoti_sum_volD |
| §H | 7506–7958 | 453 | SUM_EQ 前提：对 s 全体逐胞重演 i−1=0/2/3 分解（CARD_MINUS_DIFF_TWO_SET、CONIC_CAP_INTER_CONVEX_HULL_4_GT_0、COPLANAR_IMP_NEGLIGIBLE） | ❌ grutoti_pivot |
| §I | 7959–8001 | 43 | SUM_LMUL 线性步 + `vol D > 0`（VOLUME_CONIC_CAP）+ 消元收网 | ✅ 已证（PA23 setSum_mul_div/cancel/concl_arith）+ ❌ volD_pos |

### 1.2 §B region 块内部（giant 1 的七个子块）

| 子块 | 行号 | 行数 | 内容 |
|---|---|---|---|
| B1 | 161–412 | 252 | p = circumcenter{u0,u1}（=中点，CIRCUMCENTER_2）；二分面超平面 `S1 = {x | 2(u0−u1)·x = ‖u0‖²−‖u1‖²}`；S2 = S1 \ relative_interior S；S1 闭、S1=affine hull S1、S 有界性反证 → 取 z ∈ S2，a = dist(p,u0)/dist(z,u0) |
| B2 | 413–589 | 177 | B = V ∩ ball(p,8)；A = B \ {u0,u1}；最近点 a' 选取；d₀ = (dist(p,a')−dist(p,u0))/4 |
| B3 | 590–1075 | 486 | 重心/仿射组合代数：`h = sum (s DELETE u0) u`、加权平均 y、VSUM_SUB/DOT_LSUM 机器 → `∃b. 0<b<1 ∧ rcone_gt u0 u1 b ⊆ aff_ge_alt {u0} S` |
| B4 | 1076–1143 | 68 | `c = max b (hl[u0;u1]/sqrt 2)`；`C = ball(u0,1) ∩ rcone_gt u0 u1 c` |
| B5 | 1144–1537 | 394 | rogers 胞族覆盖 kit：St/Sr/Ss/Sx + `mcell i V vl | i ≤ 4` 分解 + FINITE_IMAGE_EXPAND |
| B6 | 1538–2610 | **1073** | **P1–P4 极小值论证**：f1/f2/f3/f4 在 `{ul | barV V 3 ul ∧ truncate_simplex 1 ul = [u0;u1]}` 上取最小 → r1（:1591）、r2（:1734）、d1（:1871）、d2（:2272）；`r = min 1 (min r1 r2)`（:1809）；smallest_angle_line 装置 ×4（SMALLEST_ANGLE_LINE_EXISTS、convex hull 内最角点、affine hull 排斥论证） |
| B7 | 2611–2636 | 26 | `d = max c (max d1 d2)`；`D = ball(u0,r) ∩ rcone_gt u0 u1 d`；D ⊆ C；每胞覆盖陈述（:2631–2636）：`mcell_set V X ∧ ¬NULLSET(X∩D) → ∃k vl. 2≤k ∧ barV V 3 vl ∧ X = mcell k V vl ∧ truncate_simplex 1 vl = [u0;u1]` |

### 1.3 外部引理消费清单（频次 = MATCH_MP_TAC/SIMP 实测）

- **测度论**（Pack2.hl + 多元库）：MEASURE_NEGLIGIBLE_UNIONS_IMAGE（§G 主点）、
  MEASURE_NEGLIGIBLE_SYMDIFF ×7、MEASURE_EQ_0、NEGLIGIBLE_SUBSET ×118（最高频）、
  NEGLIGIBLE_UNION ×6、MEASURABLE_INTER、COPLANAR_IMP_NEGLIGIBLE ×34。
- **锥帽体积**（flyspeck_multivariate.ml，**本地树无源**）：VOLUME_CONIC_CAP ×6
  （含 §I 正性；从使用点反推公式 `vol(conic_cap u0 u1 r d) = if 1 ≤ d then 0 else
  2/3·π·(1−d)·r³`，HL:3356–3358 见证）、VOLUME_CONIC_CAP_WEDGE ×4–6
  （`vol(D ∩ wedge u0 u1 w1 w2) = vol D · azim/2π`，HL:3208/:3516/:4767）。
- **mcell/barV kit**：MCELL_EXPLICIT（数十次，PA12:623 **已证**）、BARV_3_EXPLICIT
  ×34（PA8:207 **已证**）、BARV_IMP_LENGTH_EQ_CARD ×26、HD/EL_TRUNCATE_SIMPLE ×30、
  TRUNCATE_SIMPLEX_SUBSET/BARV、HDTFNFZ（PA10:246 **sorried**）、LEPJBDJ/LEPJBDJ_0
  （PA11:338/366 **sorried**）、AJRIPQN ×8（PA17:310 **sorried**）、
  MCELL_SUBSET_BALL8（PA15:794 **sorried**）。
- **仿射/维数**：NOT_COPLANAR_NOT_COLLINEAR ×30、AFF_DIM_LE_2_IMP_COPLANAR ×10、
  Njiutiu.AFF_DEPENDENT_AFF_DIM_4 ×10、AFF_GE_MONO_RIGHT ×12、AFF_GE_AFF_GT_DECOMP、
  Qzksykg.SET_SUBSET_AFFINE_HULL、CLOSED_HYPERPLANE、relative_interior 族、
  Collect_geom.CHANGE_SIDE ×6。
- **角度**：AZIM_COMPL（§F 补角；Lean 侧 PA6:2107/PA7:156 AZIM_COMPL_EXT **已证**）、
  AZIM_DIHV_SAME ×6、AZIM_EQ_0_PI_IMP_COPLANAR（**Lean 零移植**，grep 实测 0 文件）、
  SMALLEST_ANGLE_LINE_EXISTS ×4（PA15:748 **已证**，连 PROPERTY/IN_CONVEX_HULL
  三件套全在）、PI_POS。
- **集合/算术**：SUBSET_BALL ×21、RCONE_GT_SUBSET ×19（PA15:579 **已证**）、
  SELECT_AX ×18、FINITE_IMAGE_EXPAND ×9、CARD_MINUS_DIFF_TWO_SET（Hypermap；
  Lean 仅 1 文件）、CONIC_CAP_INTER_CONVEX_HULL_4_GT_0（PA15:828 **sorried**）、
  Qzyzmjc.BARV_3_IMP_FINITE_lemma2 ×5（PA16 QZYZMJC 链 sorried）。

## §2 树内存量盘点

### 2.1 已在树、可直接复用（零成本）

| 件 | 落点 | 状态 |
|---|---|---|
| GRUTOTI 陈述接口 | PA2:1280（=PA24:498 拷贝=PackingConcl:603 discharge 位） | 形态冻结 |
| PA23 骨架 9 机械件 + capstone 组装 | PA23:90–170, 319–339 | **已证** |
| MCELL_EXPLICIT / BARV_3_EXPLICIT / CLOSEST_POINT_SING | PA12:623 / PA8:207 / PA12:1429 | **已证** |
| AZIM_COMPL_EXT | PA6:2107、PA7:156 | **已证** |
| SMALLEST_ANGLE_LINE 三件套 | PA15:748/774/782 | **已证** |
| RCONE_GT_SUBSET、HL_2、DIHX_RANGE/LE_PI、affGeAlt def | PA15:579/547/1061/1081/729 | **已证** |
| **WedgeVolume/SolidAngle/LuneVolume 三模块**（`volume_ball_wedge = azim·2r³/3`、measurable_ang、volume_sector_rot、volume_solid_triangle…） | Geom/WedgeVolume.lean:831、Geom/SolidAngle.lean、Geom/LuneVolume.lean | **全部零 sorry**——锥帽体积套件的极坐标先例与工具箱 |
| intrinsicInterior（relative_interior 对应物） | Mathlib Analysis/Convex/Intrinsic.lean:61（`intrinsicInterior/intrinsicFrontier/intrinsicClosure`） | Mathlib 现成 API |
| DIHX_SYM 桥（azim/dihV 互换需要） | PA15:1123 | **sorried**（小件） |

### 2.2 必须先填/同波填的传递依赖（⭐ 排期关键）

| 件 | 落点 | 档级 | 谁还要它（共享度） |
|---|---|---|---|
| VOLUME_CONIC_CAP + VOLUME_CONIC_CAP_WEDGE 套件 | **无 Lean 落点**（PA24:423 注记"not ported in any lane"；源不在本仓） | **GIANT（解析银行）** | GRUTOTI §D/§F/§I + **PA24 REUHADY 链** volumeConicCapWedgeGeVsConicCap（PA24:428）+ TSKAJXY3（HL:1959 用 STRONG 版）——**三链共享** |
| Pack2.hl 测度桥（MEASURE_NEGLIGIBLE_UNIONS_IMAGE 族） | 无移植（PA16:77-79/PA19:66-68 双注记；upfzbzm-scout §1.3） | 中-GIANT | GRUTOTI §G + **KIZHLTL1（UPFZBZM wave 2）**——两链共享 |
| FINITE_EDGE_X2 | PA15:672 sorry | S/M | GRUTOTI §G + OXLZLEZ 链 |
| MCELL_SUBSET_BALL8_1 / FINITE_MCELL_SET_LEMMA_2 / MCELL_SUBSET_BALL_4 | PA15:794/811/518 sorry | S–M | GRUTOTI §G/§H + KIZHLTL 链 |
| HL_LE_SQRT2_IMP_BARV_1 | PA15:574 sorry | S | GRUTOTI §A（现 shim 透传）+ REUHADY |
| MCELL_ID_OMEGA_LIST_N / MCELL_ID_MXI / MCELL_ID_MXI_2 / DIHX_SYM | PA15:654/661/1118/1123 sorry | S | GRUTOTI §D/§F dihX dispatch |
| CONIC_CAP_WEDGE_EQ_0 / CONIC_CAP_AFF_GT_EQ_0 / CONIC_CAP_INTER_CONVEX_HULL_4_GT_0 | PA15:818/823/828 sorry | M | GRUTOTI §H（第三件 §D 也用）|
| HDTFNFZ / LEPJBDJ / LEPJBDJ_0 | PA10:246 / PA11:338/366 sorry | M | GRUTOTI §G/§H + OXLZLEZ3/TSKAJXY 链（tskajxy12-scout 域） |
| AJRIPQN | PA17:310 sorry | M | GRUTOTI §G（negligible-symdiff 前提：双胞体正测度交 ⇒ 同胞） |
| VORONOI_LIST_3_SINGLETON_EXPLICIT | PA12:1233 sorry | GIANT（已注记） | PA23.grutoti_vor_cover（已填件的上游 taint） |
| AZIM_EQ_0_PI_IMP_COPLANAR | 无 Lean 落点（grep 0 文件） | S | GRUTOTI §F AZIM_COMPL 前提 |

**结论**：GRUTOTI 不是"孤岛 GIANT"——它踩在三座共享银行上（锥帽体积、Pack2 测度桥、
PA15 marchal3 套件），其中两座同时是 UPFZBZM/REUHADY 链的关键路径。**若 UPFZBZM
wave 2/3 已排 Pack2 测度桥与 PA15 套件，GRUTOTI 的边际成本显著下降**；反之先建
GT-1 锥帽银行是两链共同入场券。

### 2.3 Mathlib 可行性初判（对照 playbook §5.3 雷区）

- 锥帽体积换元：本仓已有**零 sorry 的完整先例**（WedgeVolume.lean 837 行用 ℂ 极坐标
  做 `volume_ball_wedge`）；圆锥扇形版用同款柱坐标（φ × 高度 × 半径，Jacobian ∝ ρ）
  或把 rcone 截断化为 angSet 截断，走 `volume_sector_rot`/`volume_angSet` 组合。
  M3 Pro 12 核 + maxHeartbeats 5000000 下无红灯，但换元类证明单 theorem 编译可达
  分钟级——建议逐 theorem checkpoint。
- relative_interior：Mathlib **无同名词**；用 `intrinsicInterior`（Intrinsic.lean:61）
  桥接，注意 HOL `relative_interior S` 对仿射集退化为其自身（B1 里 `S1 = affine hull
  S1 ⇒ relint S1 = S1` 一类步 Mathlib 侧写法不同）。
- 高频雷区（§5.3 实测表）：`Set.Finite.subset` 有限集在前；`div_le_iff₀`/
  `one_lt_inv₀`；`epsilon_spec (p := …)` 显式谓词（PA23:104 已示范）；omega 双
  nat-sub（`i − 1 = 0/2/3` 分解是重灾区）；build 模式点链式不可解析，全限定
  `Set.Finite.toFinset` 等。
- `sum`（HOL 有限集和）↔ `setSum`（PA2:125，无限集 junk=0）：§G/§H 的 index finiteness
  已折叠进 grutoti_sum_volD 的 `Finite` 合取（PA23:283-289 设计正确）。

## §3 数学内核诊断（自然语言）

**命题**：短边 {u0,u1} 周围所有 Marchal 胞对这条边的二面角之和为 2π。这是 Marchal
分体（mcell 分解）"每条短边在单位球面上恰好铺满一圈"的组合-测度事实，是
UPFZBZM/RDWKARC 密度上界链的输入之一（通过 leaf-rank/edge-sum 路径）。

**HOL 证法三步**：
1. **region（§B）**：造一个"测试域" D = ball(u0,r) ∩ rcone_gt(u0,u1,d)，使每个与 D
   正测度相交的 mcell 都是跨边 k=2/3 胞（k≥4 共面 → 零测）。D 的参数 c, r, d 由四轮
   "截断表列上取极小"的紧凑性论证（P1–P4，配 smallest_angle_line 装置）从 packing
   公理榨出——这是 2476 行的主体，本质是**仿射几何 + 有限选取**，无浮点无极限。
2. **per-cell wedge（§D/E/F）**：对 k=2 胞（aff_ge 楔与 D 的交）、k=3 胞
   （hull 加 mxi，需 AZIM_COMPL 补角）、k≥4/低维胞（共面 → COPLANAR_IMP_NEGLIGIBLE
   零测），证 `vol(X∩D) = vol(D)·dihX/2π`——把测度论问题化成**锥帽扇形体积公式**
   （锥帽体积 = 2/3·π·(1−d)·r³，其楔形截段按 azimuth 比例分账）。
3. **sum + cancel（§G/H/I）**：edge 胞族 s 上 `∑ vol(X∩D) = vol D`
   （MEASURE_NEGLIGIBLE_UNIONS_IMAGE：胞族几乎不交且覆盖 D），代回得
   `vol D = ∑ vol D·dihX/2π`，`vol D > 0` 消元 → `∑ dihX = 2π`。

**"深"在哪**：①锥帽体积公式是唯一的解析银行（但 Geom/WedgeVolume+SolidAngle 已把
同款球扇形测度计算零 sorry 落地，风险大降）；②region 块的 P1–P4 极小值论证是
1073 行的组合-仿射长跑（Lean 侧预计繁琐但不深）；③k=3 的补角恒等式（AZIM_COMPL）
与 dihX dispatch 是机械件。

## §4 定级表与波次提案

### 4.1 逐子块定级

| Lean 交付物 | HL 锚点 | 定级 | 预估 Lean 行数 | 备注 |
|---|---|---|---|---|
| **GT-1 锥帽体积套件**（新模块，建议 `Kepler/Text/ConicCapVolume.lean`） | flyspeck_multivariate.ml（无本地源）+ PA24:428 | **GIANT（解析）** | **400–800** | measurable + vol 公式 + 楔形分账 + 正性；**双银行**（GRUTOTI + REUHADY/PA24，顺带喂 TSKAJXY3 STRONG 版） |
| GT-2a `grutoti_volD_pos` | HL:7983–8000 | **S** | 40–80 | 两条路线：GT-1 供 vol 公式直取；或初等路线（帽含开球 → volume 正性，PA23:310-313 已写配方）。**注意补 `hne` 前提**（冻结陈述 u1=u0 时为假，PA23:307-314 诚实注记在案） |
| GT-2b `grutoti_sum_volD` | HL:7226–7505 | **M** | 150–300 | MEASURE_NEGLIGIBLE_UNIONS_IMAGE 有限版（Mathlib `measure_biUnion_finset` + 零交记账）；依赖 PA15 FINITE_EDGE_X2/MCELL_SUBSET_BALL8 填充或临时私件 |
| GT-2c `grutoti_pivot` | HL:7506–7958 | **M/L** | 150–300 | SUM_EQ 全族 + junk 分支（Lean dihX 对 k≤1/null 恒 0，PA2:410-420 编码已对齐）；i−1=0/2/3 分解需 CARD_MINUS_DIFF_TWO_SET 型计数 + PA15:828 |
| GT-3 `grutoti_cell_vol` | HL:2652–7958 | **GIANT** | **1200–2000** | 见 4.2 三臂拆分 |
| GT-4 `grutoti_region` | HL:161–2636 | **GIANT** | **1000–1800** | 见 4.2 两段拆分 |
| （随带）PA15 套件 9 枚 | 见 §2.2 | S–M | 300–500 | 可挂 GT-2/GT-3 波顺带，或并入 UPFZBZM wave 2 共享时窗 |
| （随带）AZIM_EQ_0_PI_IMP_COPLANAR | — | S | 20–40 | azim=0/π ⇒ 共面，Mathlib azim API 直取 |

**总量**：GRUTOTI 整链闭合 ≈ **Lean 2800–5000 行**（含随带件）。对照既有档级记录
（STATUS.md "920 sorry 纯填证期"），这是剩余最大单章之一。

### 4.2 波次拆分提案（CF-4 式 a/b/c）

**GT-1（先导波，共享银行，独立文件）**：新建 `Kepler/Text/ConicCapVolume.lean`，
import `Kepler.Geom.WedgeVolume + Kepler.Geom.Azim + Kepler.Text.PackingAuto2`
（conicCap 在 PA15，私拷或 +import PA15——PA15←{PA2..PA13} 无环；**不要** import
PA23/PA24）。目标三件：`volumeConicCap`（MeasurableSet + vol 公式 + 0<vol 正性）、
`volumeConicCapWedge`（楔形截段 = vol·azim/2π）、`AZIM_EQ_0_PI_IMP_COPLANAR` 桥。
路线：把 conicCap = closedBall ∩ rconeGt 化为以 u0 为原点的柱坐标扇形，复用
WedgeVolume 的 measurable_ang/volume_sector_rot 机器。**收账**：GRUTOTI §D/§F/§I
三处 + PA24.volumeConicCapWedgeGeVsConicCap（陈述形状已对齐，PA24:431-432，只需
wedgeGe vs wedge 的小桥）+ TSKAJXY3 银行。预估 400–800 行。

**GT-2（机械收尾波，lane 文件 = PA23 + PA15 小件，~350–700 行）**：
GT-2a volD_pos（S）→ GT-2b sum_volD（M，带 PA15 FINITE_EDGE_X2/MCELL_SUBSET_BALL8_1
二枚填充或私件化）→ GT-2c pivot（M/L）。零新概念，全是 setSum/测度代数 + 计数。
依赖 GT-1（volD_pos 走公式路线时；初等球内含路线可解耦，见风险 R2）。

**GT-3（cell_vol GIANT，三臂，1200–2000 行）**：
- GT-3a 空臂（HL §E，1722 行 HL → Lean 300–500）：抽 4–6 枚"共面 ⇒ 零测"私件后
  COPLANAR_IMP_NEGLIGIBLE 复读坍缩；MCELL_EXPLICIT（已证）dispatch + mcell4
  unfold（纯 hull，coplanar 判定走 AFF_DIM/NOT_COPLANAR kit）。
- GT-3b k=2 臂（HL §D，1075 → 300–500）：mcell2 unfold（rconeGe 双锥 + affGe 楔）→
  `X∩D = L∩D`（D 在双锥内、affGe 单调）→ GT-1 楔形分账 + dihu2 = dihV = azim 桥
  （AZIM_DIHV_SAME 对应物；PA15 DIHX_SYM 顺带填）。
- GT-3c k=3 臂（HL §F，1764 → 400–700）：mcell3 hull 楔化 + **AZIM_COMPL_EXT**
  （PA6 已证）补角分账 + dihu3 桥。
依赖：GT-1；PA8/PA12 已证件；PA17 AJRIPQN 与 PA11 LEPJBDJ 若届时仍未填，按
§2.2 清单临时私件化（各 ~60–120 行）。

**GT-4（region GIANT，两段，1000–1800 行）**：
- GT-4a B1–B4（HL 161–1143，~983 → 500–800）：intrinsicInterior 桥 + 超平面闭性
  （Mathlib 连续函数零点集）+ 最近点选取（`Metric.exists...` 或 epsilon_spec）+
  重心仿射代数（Finset.sum 化 vsum，PA23 已有 trunc1 的 epsilon 范本）。
- GT-4b B5–B7（HL 1144–2636，~1493 → 500–1000）：rogers/mcell 覆盖 kit +
  P1–P4 四轮极小值（PA15 SMALLEST_ANGLE_LINE 三件套已证是最大红利；
  Classical.epsilon 选最小元 + Finset.min' 模式）+ 组装 ∃c r d 陈述。
依赖：**与 GT-2/GT-3 完全独立**（PA23 capstone 组装已证，五枚 giant 是五张独立
欠条），可与 GT-3 并行开两条 lane。

**排期建议**：GT-1 必须最先（三链共享）；GT-2/3/4 三线并行（或单 lane 顺序收，
总量不变）；PA15 套件 9 枚建议并入 UPFZBZM wave 2 的 PA15/PA16 时窗统一处理
（FINITE_EDGE_X2 等是双消费件，避免两 lane 各私件一遍）。GT-1 + GT-2 收口后
GRUTOTI 链呈"忠实架构 + 2 枚具名 giant taint"，GT-3/GT-4 收口即
GRUTOTI1_concl_discharged axioms 干净。

## §5 风险清单

1. **VOLUME_CONIC_CAP 无本地 HOL 源**（flyspeck_multivariate.ml 不在 reference 树）：
   陈述只能从 GRUTOTI.hl:3356-3358 等使用点反推（`if 1 ≤ d then 0 else
   2/3·π·(1−d)·r³` 形状，含 d=1 边界分支需在 GT-1 里用 kernel 自验）；公式推导
   GT-1 是全链最大解析银行。缓解：WedgeVolume/SolidAngle/LuneVolume 三模块
   零 sorry 先例 + 工具箱齐全；若换元路线卡死，备胎是 "ball×cone 扇形 = angSet
   截断"的组合分解（SolidAngle.volume_solid_triangle 同款）。
2. **grutoti_volD_pos 冻结陈述在 u1=u0 时为假**（PA23:307-314 已诚实注记）：填证时
   必须同步给私有签名加 `hne : u0 ≠ u1`（capstone 调用点 PA23:334 已带，改签名
   即可）；漏改会在退化分支产生假绿 risk——kernel 不查陈述合理性。
3. **PA23 骨架陈述是重构（非逐字）**：`grutoti_region`/`grutoti_cell_vol`/
   `grutoti_sum_volD` 的冻结形状是侦察者（前 lane）的重构思，HL 中对应内容是
   NEW_GOAL 长链；若 GT-4a 过程发现陈述缺前提（如 C 的可测性、S 非空），需改
   private 签名并过编排者审查——骨架文件本就是本 lane 财产，改动合法但要记录。
4. **传递依赖深**（§2.2 表）：4 枚上游 giant（HDTFNFZ/LEPJBDJ/AJRIPQN/
   VORONOI_LIST_3_SINGLETON_EXPLICIT）+ PA15 套件 9 枚全 sorried。GRUTOTI 单章
   闭合≠axioms 干净；编排者排期时应把"GRUTOTI 闭合"与"GRUTOTI 链 taint 断流"
   分开记账（后者还需 OXLZLEZ/TSKAJXY/REUHADY 协同）。
5. **与 UPFZBZM wave 2 的共享件竞争**：Pack2 测度桥、FINITE_EDGE_X2、
   MCELL_SUBSET_BALL8 系、FINITE_MCELL_SET_LEMMA_2 两链都要；建议统一在
   PA15/Pack2-bridge 时窗做一次、两链 import（PA23←PA15 已就绪），防重复移植。
6. **改名雷区**（playbook §5.3）：relative_interior → `intrinsicInterior`；
   omega 双 nat-sub（i−1 分解）；`Set.Finite.subset` 参数序；build 模式点链式；
   `epsilon_spec (p := …)`。GT-4 的 vsum→∑ 翻译量大，建议每子块单 theorem 提交。
7. **编译成本**：M3 Pro 12 核；PA23 零 importer，单文件重建便宜；但填 PA15 会触发
   PA15←{PA18/19/21/25} 子树重建——PA15 件建议攒批提交。GT-1/GT-3 换元与
   测度大件设 maxHeartbeats 检查点，单 theorem 超时即拆引理。
8. **行数预估不确定性**：GT-4b（P1–P4）与 GT-3c（k=3 补角）是两个 ±40% 区间项；
   HL 中大量 SET_TAC/REAL_ARITH 短行在 Lean 折算系数不稳。建议 GT-3a（空臂）先做
   ——它是三臂中最机械的，可校准整波折算系数。

## §6 立项建议

- **不要按"独立 GIANT 单 lane"立项**：PA23 骨架已把"移植"做完，剩余是
  "5 枚 giant 填证 + 3 座共享银行"。建议拆 **4 波**（GT-1 共享银行先行 →
  GT-2 机械收尾 → GT-3/GT-4 双 GIANT 并行），GT-1 单独成 PR 落
  `ConicCapVolume.lean`（对照 ContraFanDeep/PackingJGXZYGW 先例：独立叶模块、
  私件前缀、唯一名公开 capstone，避免与 PA24 的 conicCapP24 撞名）。
- **性价比锚点**：GT-1（400–800 行）一次喂三链（GRUTOTI/REUHADY/TSKAJXY3），
  是本报告性价比最高的一波；GT-2 收口后 PA23 达"忠实架构 + 2 taint"状态。
- **merge 路径**（留编排者）：PackingConcl.lean:603 的 discharge 现走
  PA24.GRUTOTI1_concl_p24_pub → PA2 sorried 接口；PA23 填满后改指
  `PA23.GRUTOTI`（加 import PA23 无环，PA23 零下游），或经 PA24 转发；
  同时删 PA24:488-517 拷贝（文件头自注"delete at merge"）。

---

关键文件：`lean/scripts/packing/GRUTOTI.hl`（8005 行 HOL 源）、
`lean/Kepler/Text/PackingAuto23.lean`（骨架+5 giant+capstone）、
`lean/Kepler/Text/PackingAuto2.lean`（:1280 接口、:333-420 mcell/dihX defs）、
`lean/Kepler/Text/PackingAuto15.lean`（marchal3 套件 19 sorries + SMALLEST_ANGLE
已证件）、`lean/Kepler/Text/PackingAuto24.lean`（:428 锥帽共享缺口 + :488 GRUTOTI
桥）、`lean/Kepler/Geom/WedgeVolume.lean`（:831 零 sorry 极坐标先例）、
`lean/Kepler/Text/PackingConcl.lean`（:603 discharge 位）、
`.lake/packages/mathlib/Mathlib/Analysis/Convex/Intrinsic.lean`（:61
relative_interior 对应物）。

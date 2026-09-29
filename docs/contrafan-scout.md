# contrafan-scout — 深几何双核（LEMMA_3_POINTS_FINAL / LEMMA_4_POINTS_FINAL）专项侦察报告

> 2026-09-28 只读侦察交付物（纪律同 tame-chapter-scout / mqmsmab-scout：零 .lean 改动、
> 零 tracked 文件改动，唯一仓库写入 = 本文档；不跑 lake / auto_gate / git 写操作）。
> 对照基准：`reference/flyspeck`（HOL Light Flyspeck，tame/CKQOWSA_3.hl 1450 行、
> tame/CKQOWSA_4.hl 4272 行）。所有 file:line 均经 grep/sed 实测核对。
>
> **核心结论先行**：
> ① 两 sorry 的**陈述忠实无弱编码**（与 HOL 逐字同义，见 §1），B 表"深几何双核"的债务
> 全在证明体；
> ② `LEMMA_3_POINTS_FINAL` 存在一条**绕开 HOL 全链的新证明**（内积角 + 纯有理数算术，
> 本报告 §4.2 路线 B，数值见证已手算齐全），预估 **250–400 行 / 中等档**，无需 IVT、
> 旋转族与 delta_x；
> ③ `LEMMA_4_POINTS_FINAL` 无廉价捷径，需忠实移植"分离平面 + 双旋转 + 外心终局"链，
> 预估 **2000–3000 行 / GIANT**，最大难点是"segment ∩ cone 非空"不变量在连续旋转族下的
> 传递（HOL 连续性机器 ~1500 行，Lean 估 600–1000 行）；
> ④ 建议拆 **2 条 lane**（CF-3 先行、CF-4 随后），深几何放独立新模块
> `Kepler/Text/ContraFanDeep.lean`（import {Geom.Aff, Text.PackingAuto2}，反向被
> ContraFan 引用，无环），避免 ContraFan.lean 长期脏文件；双核闭合后
> `Assembly.lean:922 #print axioms contraveningFan` 应无 sorryAx，e2e-debt-map B 表
> 该行划除。

---

## §0 定位与消费链（Lean 侧实测）

全仓库仅 **2 枚 sorry** 位于 `lean/Kepler/Text/ContraFan.lean`（模块 docstring :23-36
自述移植状态）。该模块 18 条定理中 16 条已真化，双核是 CKQOWSA 章最后的欠账：

```
LEMMA_3_POINTS_FINAL (ContraFan.lean:400, sorry :405)   ← fan7_3 (:535)、fan7_4_1_one_case (:685/:703) 消费
LEMMA_4_POINTS_FINAL (ContraFan.lean:414, sorry :422)   ← fan7_4_0 (:754) 消费
  ↓ 三者汇入
ESTD_fan7 (ContraFan.lean:773) → CKQOWSA (:863) → contraveningFanTl (:873)
  ↓ exact 级同体 defeq（ESTD 三处同体：ContraFan:55 / TameLp:308 / Assembly:41）
TameLp.contravening_fanTl (TameLp.lean:796-801)        ← 真证明，透传双核 sorryAx
Assembly.contraveningFan (Assembly.lean:457-462)        ← 真证明，透传双核 sorryAx
  ↓ textCapstone :855（正向分支 hLPR 接收方）+ :874（镜像分支 contraveningNegative）
Assembly.textCapstone (:842, 真证明) → the_kepler_conjecture_from_interfaces (:917)
  ↓ 公理审计锚点：Assembly.lean:922 `#print axioms contraveningFan`
```

消费形态完全固化：三处调用（ContraFan:535/:685/:703 与 :754）都只消费**矛盾形/交平凡形
终局**，不依赖 HOL 的中间强化版 `LEMMA_3_POINTS`（∃v'. dist = 2 恰等式版，CKQOWSA_3.hl:1306）
——即证明体可整体替换为新路线，接口零改动。

## §1 两定理精确陈述与 sorry 现状

| 定理 | Lean 锚点 | 陈述（逐字要点） | HOL 原形 | 忠实性 |
|---|---|---|---|---|
| `LEMMA_3_POINTS_FINAL` | ContraFan.lean:**400-405**（sorry :405） | `v3 ∈ affGe {0} {v1,v2}` ∧ 三点 ∈ ballAnnulus ∧ `dist v1 v2 ≤ 2h0` ∧ `2 ≤ dist v1 v3` ∧ `2 ≤ dist v2 v3` → `False` | CKQOWSA_3.hl:**1350-1356**（`==> F`） | ✅ 逐字同义 |
| `LEMMA_4_POINTS_FINAL` | ContraFan.lean:**414-422**（sorry :422） | 四点 ∈ ballAnnulus ∧ `dist v1 v3 ≤ 2h0` ∧ `dist v2 v4 ≤ 2h0` ∧ 六对距离 ≥ 2 → `affGe {0} {v1,v3} ∩ affGe {0} {v2,v4} = {0}` | CKQOWSA_4.hl:**4093-4096** | ✅ 逐字同义 |

sorry 体现状：纯骨架（`by sorry`），但 DISCHARGES 注记完整记录了 HOL 依赖链锚点
（ContraFan.lean:392-399 与 :407-413），且同文件已备齐周边件：

- `affGe_0_1_char` :97、`affGe_0_2_char` :145（= HOL `aff_ge_0_2` CKQOWSA_3.hl:115 的
  二系数显式化，**两核证明的第一入口**）、`affGe_0_empty` :184、`affGe_0_subset` :211；
- `annulus_ray_absurd` :269（**private**，同射线反证——路线 B 的共线分支直接复用）；
- `dot_pos_lemma` :293（= CKQOWSA_3.hl:1071，已真化）、
  `estd_non_collinear_lemma` :317（= CKQOWSA_4.hl:45，已真化，L4 分离步的输入）。

## §2 HOL 对照：两条依赖链全景

### 2.1 三点链（CKQOWSA_3.hl，模块 Ckqowsa_3_points）

| HOL 引理 | 行号 | 内容 | Lean 现状 |
|---|---|---|---|
| `projection_lemma` | :42 | v = x + a%n 正交分解 | 未移植（路线 B 不需要） |
| `non_collinear_lemma` | :84 | annulus + 2≤dist + 0<v·w → ¬collinear{0,v,w} | 未移植（路线 B 不需要） |
| `aff_ge_0_2` | :115 | 锥的二系数显式化 | ✅ `affGe_0_2_char` |
| `in_aff_ge_0_2` | :143 | 锥内 w → 严格正系数 t1,t2 > 0 | 未移植（路线 B 不需要） |
| `in_aff_ge_0_2_imp_dot_pos` | :194 | 锥内非零 w → v1·w>0 ∧ v2·w>0 | 未移植 |
| `aff_ge_eq_lemma` | :244 | u = a%v2 (a>0) → 锥{v1,v2} = 锥{v1,u} | 未移植 |
| `triangle_height_lemma` | :283 | v = a%w + n, n⊥w, ‖n‖=‖v×w‖/‖w‖ | 未移植 |
| `in_aff_ge_dist_lemma` | :327 | 锥条件 → ‖n1−n2‖ = ‖n1‖+‖n2‖（法向对顶） | 未移植 |
| `in_aff_ge_dist_lower_bound` | :436 | dist(v1,v2) ≥ (‖v1×w‖+‖v2×w‖)/‖w‖ | 未移植 |
| `triangle_area_lower_bound` | :483 | dist=2 → 1.48√3 ≤ ‖v×w‖（Heron/UPS_X） | 未移植 |
| `DIST_LOWER_BOUND_lemma` | :536 | dist(v1,w)=dist(v2,w)=2 → 1 ≤ dist(v1,v2) | 未移植 |
| `aff_ge_trans` | :612 | 锥成员传递 v3∈cone{v1,v2} ∧ v∈cone{v1,v3} → v3∈cone{v,v2} | 未移植 |
| `rotation_dist_decrease` | :673 | 旋转不增距离（u∈cone{v,w}, ‖u‖=‖v‖ → dist(u,w)≤dist(v,w)） | 未移植 |
| `rotation_lemma` | **:828** | 连续旋转族 f：f(0)=v, f(1)=u, 保范、保锥、连续（sin/cos 构造） | 未移植 |
| `dot_pos_lemma` | :1071 | ✅ | ✅ ContraFan:293 |
| `dist_decreasing_ivt_lemma` | :1106 | IVT 打靶 dist(f t,v)=d 恰等式 | 未移植 |
| `lemma_3_points` | **:1147** | 主构造：旋转 v1→v3 方向，IVT 取 dist=2 点 | 未移植 |
| `LEMMA_3_POINTS` | :1306 | 两次套用得双恰等式 | 未移植（Lean 不需要） |
| `LEMMA_3_POINTS_FINAL` | **:1350** | 终局：coplanar{0,v1',v2',v3} → delta_x=0 vs delta_x_3_points ≥ 13 | sorry |

终局算术件（`tame/Inequalities.hl`）：`delta_x_3_points` :237（box [4,6.3504]³×[0.64,6.3504]
上 delta_x x1 x2 x3 4 4 x6 ≥ 13，经 `main_lemma` 逐变量凸性 + 角点有理验算）；
`Collect_geom.POLFLZY`（二面角公式，本地快照无定义体，仅见消费 :1364）+
`DELTA_EQ_DELTA_X`（Inequalities.hl:553）把"四点共面"翻译成 delta_x = 0
（Cayley–Menger 行列式退化）。

### 2.2 四点链（CKQOWSA_4.hl，模块 Ckqowsa_4_points）

| HOL 引理 | 行号 | 内容 | Lean 现状 |
|---|---|---|---|
| `estd_non_collinear_lemma` | :45 | ✅ | ✅ ContraFan:317 |
| `zero_not_between(_estd)` | :55/:117 | 0 不在线段 vw 内（‖v‖+‖w‖=dist → ≥4 vs ≤2h0） | 未移植（小件） |
| projection 套件 | :128-282 | `PROJECTION_DIST_SPECIAL_EQ/LE` 等 12 件 | 未移植 |
| `points_in_aff_ge_0_2` | :313 | 0 ∈ cone{v1,v2} ↔ v1,v2 对向（between）退化 | 未移植 |
| `aff_ge_0_2_SUBSET` / `segment_inter_aff_ge_ends` | :338/:373 | 锥单调 / 线段穿锥端点判别 | 未移植 |
| `affine_hull_3_plane` / `in_affine_hull_lemma` | :445/:410 | 非共线三元组的平面刻画 | 未移植 |
| `rotation_dist_decrease_lemma` (+special_case) | :624/:758 | 旋转不增距离（四点版） | 未移植 |
| `continuous_lemma_inc/dec` | :785/:967 | 单调连续族的 IVT 打靶 | 未移植 |
| `rotation_lemma_special` | **:1012** | 过原点轴 ℝn 旋转族（保范、保轴上距离、f(1)=正规化 w） | 未移植 |
| `aff_ge_inter_segments` | :1238 | 交非空在"换端点"下的传递 | 未移植 |
| `rotation_lemma_segments` | :1395 | 线段交不变量下的旋转族 | 未移植 |
| `rotation_about_axis` | :1676 | 轴旋转包装（a%w + b%d 端点） | 未移植 |
| `continuous_intersection_point` | :1785 | 交点对参数的连续依赖 | 未移植 |
| `in_aff_ge_cases_lemma` / `segment_intersects_aff_ge_lemma` | :1928/:2138 | 穿锥判别两分支 | 未移植 |
| `continuous_lemma_aff_ge` | **:2204**（665 行，全章最大单件） | 旋转下"[f t,w] ∩ cone ≠ ∅"不变量的传递 | 未移植 |
| `separation_plane_4_points` | **:2870** | 法向量 n=±v2×v4：v1·n<0< v3·n（用 L3F ×4） | 未移植 |
| `lemma_4_points_rotation1(_full)` | :3003/:3203 | 绕轴 ℝv2/ℝv4 旋转使 dist 到 v2,v4 恰 = 2 | 未移植 |
| `segment_inter_conv` + `lemma_4_points_rotation2(_full)` | :3266/:3379/:3814 | 绕线 v2v4 旋转使 ‖v1'‖=‖v3'‖=2（保 dist 到 v2,v4） | 未移植 |
| `lemma_4_points_circumcenter` | **:3866** | 交非空 + 全 2 刚性 → ‖(v1+v3)/2‖ = eta_y(‖v2‖,‖v4‖,‖v2v4‖) | 未移植 |
| `PARALLELOGRAM_LAW` | :4028 | 平行四边形恒等式 | 未移植（Mathlib 有） |
| `lemma_4_points_contradiction` | **:4035** | 平行四边形 + ETA_Y_4_POINTS_INEQ → 16 ≥ 4·2.2+d² vs d≤2h0 矛盾 | 未移植 |
| `LEMMA_4_POINTS_FINAL` | **:4093** | 终局组装 | sorry |

终局算术件：`ETA_Y_4_POINTS_INEQ`（Inequalities.hl:**356**）：边长 ∈ [2,2h0] 的三角形
外接半径 eta_y² ≤ 2.2（经 `eta_x_ineq_lemma` :332 = `2.2·ups_x − x1x2x3 ≥ 0` 的逐变量
凸性 box 论证）；`eta_y` 定义 = sqrt(x1x2x3/ups_x) = abc/(4K)（外接半径公式，
general/sphere.hl:122-135）。

## §3 数学内核诊断（自然语言）

**三点核深在哪**：命题是"2.52-环中的锥容不下第三点"。HOL 证法是**连续归约**：v1 与 v3
同范数化后，在锥 span{v1,u} 内转一段保持范数的圆弧（rotation_lemma，sin/cos 显式族），
距离 dist(f t, v3) 连续地从 ≥2 变到 <2，IVT 打出**恰为 2**的点；于是化为刚性构形
(dist(v1',v3)=dist(v2',v3)=2)，再用 delta_x（Cayley–Menger 行列式）的二重性收网：
四点共面 ⟹ delta_x = 0（POLFLZY+DELTA_EQ_DELTA_X），而 box 约束下的逐变量凸性
（Inequalities `main_lemma`）⟹ delta_x ≥ 13。**"深"= 连续性论证 + 多项式最优化两件套**。

**新证法（路线 B，本报告提出）**：终局矛盾其实有一个纯初等的**平面三角**形式。设
v3 = t1v1 + t2v2（t1,t2 ≥ 0，`affGe_0_2_char`）。若 t1,t2 > 0，则 v3 在非负张成内，
Mathlib 有**锥内角度加法等式**（`angle_eq_angle_add_add_angle_add_of_mem_span`）：
∠(v1,v2) = ∠(v1,v3) + ∠(v3,v2)。而纯算术给出（全有理数，2h0 = 63/25）：
- 下界：dist(v1,v3) ≥ 2 且 ‖v1‖,‖v3‖ ∈ [2,63/25] ⟹ cos∠(v1,v3)
  = (‖v1‖²+‖v3‖²−dist²)/(2‖v1‖‖v3‖) ≤ (2·(63/25)²−4)/(2·(63/25)²) = **2719/3969 ≈ 0.6851**，
  故 ∠(v1,v3) ≥ arccos(2719/3969) ≈ 46.76°（在 r=‖v1‖=‖v3‖=2.52, dist=2 的角点取到；
  二次型 [[3969,−2719],[−2719,3969]] 正定 ⟹ box 上凸 ⟹ 角点验算即可，`nlinarith` 亲和）；
- 上界：dist(v1,v2) ≤ 2h0 ⟹ cos∠(v1,v2) ≥ (4+4−6.3504)/(2·6.3504) = **1031/7938 > 0**，
  故 ∠(v1,v2) ≤ arccos(1031/7938) ≈ 82.54°。
- 合拢：∠(v1,v2) ≥ 2·arccos(2719/3969)，而 cos(2·arccos c1) = 2c1²−1 =
  **−967159/15753081 < 0 < 1031/7938**，cos 在 [0,π] 反号矛盾（`Real.cos_two_mul` +
  `Real.cos_arccos` + `Real.arccos_le_arccos`，链条全在已验证的 Mathlib API 上）。
  2·arccos c1 ≤ π 由 c1 ≥ 0 保证（`arccos_le_pi_div_two`）。
- 退化分支：v1 = v2 或某系数为 0（v3 = t•v2 / t•v1 共线射线）时，**现成的
  `annulus_ray_absurd`（ContraFan:269）直接封死**（|1−t|·‖v2‖ ≥ 2 vs t‖v2‖ ≤ 2.52 的
  1D 算术）。
数值裕量 11°，无临界抖动。这条路线**不需要** in_aff_ge_0_2（严格系数）、rotation_lemma、
IVT、delta_x、coplanar 全部机器。

**四点核深在哪**：命题是"两条 ≤2h0 短边的过原点锥只能交于 {0}"。反证设交点 p ≠ 0，
则 p 的二系数归一化（WLOG t1'+t2' ≤ t1+t2，否则两边对换）给出
**segment [v1,v3] ∩ conv{0,v2,v4} ≠ ∅**——这是全程保持的"穿越不变量"。随后两级旋转：
① rotation2：绕直线 v2v4 转动 v1、v3（到 v2、v4 距离不变，因 v2,v4 在轴上），范数连续
变化，IVT 打到 ‖v1'‖ = ‖v3'‖ = 2；② rotation1：绕轴 ℝv2、ℝv4 转动（保轴上距离），把
四个交叉距离全部打成恰 2。每一步都要靠 `continuous_lemma_aff_ge` 家族证明穿越不变量在
旋转族下不丢（v1·n < 0 < v3·n 的符号分离 + 交点连续依赖）。终局是刚体几何：v1''、v3''
同时落在三个两两距离恰 2 的球面上，其中点 = 三角形 {0,v2,v4} 的**外心** c（到 0,v2,v4
等距 + 交条件保证 c 在平面内）；平行四边形恒等式给
16 = ‖v1''+v3''‖² + ‖v1''−v3''‖² = 4R² + ‖v1''−v3''‖²，而外接半径 R = eta_y(‖v2‖,‖v4‖,
‖v2−v4‖) ≤ √2.2（纯算术 box），故 ‖v1''−v3''‖² ≥ 16−8.8 = 7.2 ⟹ dist ≥ 2.683 > 2h0，
与 dist(v1',v3') ≤ 2h0 矛盾。**"深"= 旋转族上的连续不变量传递（全章 60% 工作量）+ 外心
刻画 + eta_y 的凸性 box 算术**。

## §4 Lean 化路线提案

### 4.0 模块布局建议（避免环与长脏文件）

新建 `lean/Kepler/Text/ContraFanDeep.lean`，只 `import Kepler.Geom.Aff` +
`Kepler.Text.PackingAuto2`（ballAnnulus :533、h0 均在此；**不得** import ContraFan/TameLp，
无环：SphereKit → Azim + PackingAuto5 → PackingAuto2，而 ContraFan 仅 import
{Text.Fan, Text.PackingAuto2, Geom.Aff}）。在 Deep 模块内以"annulus + affGe"语言证两枚
**独立 twin**（陈述同 §1），ContraFan.lean 顶部加 import 后把两个 sorry 换成
`exact ContraFanDeep.lemma3PointsFinal …` 式转发（陈述前缀逐字保留，走闸门②逐字豁免）。
这样 CF-4 lane 的数千行增量全部落在独立文件，ContraFan.lean 只出现 2 行 diff。

### 4.1 Lane CF-3：LEMMA_3_POINTS_FINAL（路线 B，预估 250–400 行，中等档）

| 步 | Lean 引理（建议名） | 形态 | HOL 锚点 | 预估行数 |
|---|---|---|---|---|
| 1 | `annulus_norm_bounds` | 2 ≤ ‖v‖ ≤ 2h0 且 v ≠ 0（inBallAnnulus 重排，几乎免费） | in_ball_annulus CKQOWSA_3.hl:33 | 10 |
| 2 | `cos_ge_of_dist_le`（上界角） | dist v w ≤ 2h0 ∧ 双方 ≥2 → ⟪v,w⟫/(‖v‖‖w‖) ≥ 1031/7938 | （新，对应 delta_x 论证的初等替代） | 40–60 |
| 3 | `cos_le_of_dist_ge`（下界角） | 2 ≤ dist v w ∧ 双方 ≤2h0 → cos ≤ 2719/3969（nlinarith + 角点积式提示） | （新） | 50–80 |
| 4 | `angle_add_cone` | v3 = t1v1+t2v2, t>0 → ∠(v1,v2) = ∠(v1,v3)+∠(v3,v2) | （HOL 无对应——Mathlib `angle_eq_angle_add_add_angle_add_of_mem_span` 直取） | 30–50 |
| 5 | `two_arccos_gt` | 2·arccos(2719/3969) > arccos(1031/7938)（cos_two_mul + cos_arccos + 反单调，纯有理数） | （新） | 40–60 |
| 6 | 组装 `lemma3PointsFinal` | v1=v2 分支 → ray；t1=0/t2=0 → `annulus_ray_absurd`；否则 2-5 合拢 | CKQOWSA_3.hl:1350（陈述） | 80–120 |

风险与备胎：若第 3 步的二次不等式 nlinarith 不闭合，备胎是复刻 HOL `main_lemma`
（一元二次 convex ⟹ 端点取 min）做一次通用 helper（约 +60 行）；路线 B 万一发现漏洞
（陈述固定，只会是证不出），回退路线 A（忠实移植 §2.1 全链，预估 1200–1800 行，
IVT/rotation/coplanar-delta_x 三大件）。

### 4.2 Lane CF-4：LEMMA_4_POINTS_FINAL（预估 2000–3000 行，GIANT，建议再切 3 波）

| 波 | 步 | Lean 引理（建议名） | HOL 锚点 | 预估行数 |
|---|---|---|---|---|
| CF-4a | 1 | `cone_inter_imp_segment_conv`：p≠0 双锥 + 系数归一 + WLOG 对换 → segment[v1,v3] ∩ conv{0,v2,v4} ≠ ∅ | L4F :4096-4185（CONVEX_HULL_3_ALT 部分） | 100–150 |
| CF-4a | 2 | `separationPlane4Points`：n := ±(v2 ⨯₃ v4)，v1·n<0< v3·n（4 次调用 L3F twin；crossProduct：`Mathlib.LinearAlgebra.CrossProduct`） | :2870-3003 | 150–250 |
| CF-4a | 3 | `rotationFamilyAxis`：过原点轴 ℝd 的显式旋转族 f t = cos(θt)•a + sin(θt)•b + p（保范、保轴上距离、连续；a/b 为 d⊥ 的 Gram–Schmidt 或手工正交基） | rotation_lemma_special :1012 + rotation_about_axis :1676 | 250–400 |
| CF-4b | 4 | `crossingInvariant`：旋转族下 segment[f t,v3] ∩ cone{v2,v4} ≠ ∅ 的传递（符号分离 + 交点连续 + IVT） | continuous_lemma_aff_ge :2204 + in_aff_ge_cases :1928 + segment_intersects :2138 + continuous_intersection_point :1785 + aff_ge_inter_segments :1238 | 600–1000 |
| CF-4b | 5 | `rotation1Full`：四次套 3+4 把四个交叉距离打成恰 2 | :3003/:3203 | 150–300 |
| CF-4c | 6 | `rotation2Full`：绕线 v2v4（轴不过原点，保 v2、v4 距离）反射族 + IVT 把范数打成 2；交不变量换 conv hull 形 | segment_inter_conv :3266 + rotation2 :3379 + rotation2_full :3814 | 400–700 |
| CF-4c | 7 | 终局三件：`circumcenterChar`（中点 = {0,v2,v4} 外心，`EuclideanGeometry.eq_circumcenter_of_dist_eq`）；`etaY4Points`：2.2·upsX ≥ x1x2x3（box [4,6.3504]³ 逐变量凸性 + 角点；**直接证多项式不等式，不定义 eta_y**——注意 PackingAuto21.lean:131 的 `eta_y := sorry` 是 def-sorry，严禁依赖）；`parallelogramFinale`（`parallelogram_law_with_norm` + 16−8.8 = 7.2 vs (2h0)² = 6.3504） | :3866 + Inequalities.hl:356/:332 + :4028/:4035 | 300–450 |

复用件清单（全部实测确认存在）：
- Mathlib：`InnerProductGeometry.angle`/`cos_angle`/`angle_le_angle_add_angle`、
  `angle_eq_angle_add_add_angle_add_of_mem_span`（Geometry/Euclidean/Angle/Unoriented/
  TriangleInequality.lean:207）、`Real.arccos_le_arccos`/`antitone_arccos`/`cos_arccos`/
  `sin_arccos`/`arccos_le_pi_div_two`（Analysis/SpecialFunctions/Trigonometric/Inverse.lean
  :283-370）、`Real.cos_two_mul`、`parallelogram_law_with_norm`（Analysis/InnerProductSpace/
  Basic.lean:493）、`EuclideanSpace.crossProduct` 族（LinearAlgebra/CrossProduct.lean:50 起，
  `cross_self` :82、`dot_self_cross` :87）、`EuclideanGeometry.circumcenter`/
  `dist_circumcenter_eq_circumradius`/`eq_circumcenter_of_dist_eq`（Geometry/Euclidean/
  Circumcenter.lean:206/:231/:251）、`intermediate_value_Icc`（Topology/Order/
  IntermediateValue.lean:553）；
- 本仓：`SphereKit.lean` 已有 verbatim twin `deltaX` :46、`deltaP` :57、`upsX` :72、
  `deltaX4` :78、`deltaY` :124（import 无环，见 4.0；路线 B 用不上，路线 A 备胎直接受益；
  IneqClosureDefs.lean:9 注记"deltaX/deltaX4 not re-ported"即指此处共享件）；ContraFan
  自备 `affGe_0_2_char`/`annulus_ray_absurd`/`dot_pos_lemma`/`estd_non_collinear_lemma`。

## §5 风险清单

1. **陈述弱编码自查（planar-fix §1 教训）**：两陈述与 HOL 逐字核对**无弱编码**
   （§1 表），`affGe` 取 `Geom/Aff.lean:42` 的 **闭锥**（sgn_ge）与 HOL `aff_ge` 同义——
   注意与 PA22 `cone0P22` 弱编码事件区分：这里闭锥是**忠实**的（HOL CKQOWSA 链本就
   用 aff_ge 而非 cone0），**不要**"顺手修正"为 `affGt`（Aff.lean:39）。
2. **路线 B 是新证明**：陈述冻结故无语义漂移风险，但要防"证明级想当然"——本报告的
   数值见证（2719/3969、1031/7938、−967159/15753081、正定凸性角点验算）已手工复核，
   但落 Lean 后一切以 kernel 为准；证不出即回退路线 A，不硬凑。
3. **def-sorry 陷阱**：`PackingAuto21.lean:131` 的 `eta_y` 定义体是 `sorry`，
   `PackingAuto25` 的 `RADV_ETAY`(:824)/`ETA_Y_POS_LE_ALT`(:2807) 也是骨架——CF-4c
   终局**自行定义局部 eta/ups 不等式**，不 import 这两个模块的相应名字。
4. **V3 内积写法（playbook §6 PA6/PA7 假绿教训）**：V3 = EuclideanSpace ℝ (Fin 3)；
   一律走 ContraFan 既有模式（`inner ℝ v w`、`real_inner_self_eq_norm_sq`、`dist_eq_norm`，
   参照 dot_pos_lemma :293-311），**避免 `⬝ᵥ`/WithLp.ofLp 显式形态**；linarith 不解构
   `v ∈ ballAnnulus` 的 Set.Mem——先用 `inBallAnnulus` 拆成连立不等式（同文件惯例）。
5. **whnf/defeq**：`affGe` 展开靠 `Affsign`，两系数归一必须经 `affGe_0_2_char`（需
   v1,v2 ≠ 0 ∧ v1 ≠ v2——由 annulus 与 v1=v2 分支前置）；`mem_ESTD` 是 Iff.rfl 级，
   Deep 模块如需 ESTD 请从 ContraFan 侧传入或改以 annulus+dist 直接陈述 twin。
6. **`annulus_ray_absurd` 是 private**（ContraFan:269）：Deep 模块里要么复制该 1D 论证
   （约 20 行），要么在 ContraFan 侧把退化分支吃掉后再调用 Deep twin。
7. **技术陷阱（playbook §6）**：`by` 块多参引理首参提前 elaboration 用 `(x := u)` 具名
   传参；linarith 对 `|x|` 假设先手工分段（abs_of_nonneg 模式，同文件 :279/:285 范本）；
   大文件终验按 §3 双格式 + lake build 同款（env-lean 假绿前科）。
8. **行数预估不确定性**：CF-4b（不变量传递）是唯一无把握项——HOL 665 行的
   `continuous_lemma_aff_ge` 若在 Lean 里按逐 case 展开，可能击穿 1000 行上限；
   建议该波单独设 checkpoint（证出"不变量传递"特例即交付，不留半成品）。

## §6 立项建议

- **拆 2 条 lane，不单 lane**：CF-3（中等档，1 波内收，路线 B）与 CF-4（GIANT，切
  CF-4a/4b/4c 三波）。CF-3 先行：它是 CF-4a 分离步（4 次调用）与既有 fan7_3/fan7_4_1
  的共同上游，且能独立消掉 B 表一半（对 `fan7_3`/`fan7_4_1` 路径的 sorryAx 即断）。
- **模块策略**：按 §4.0 建 `ContraFanDeep.lean`；ContraFan.lean 仅 +1 import、2 行转发
  （闸门②逐字豁免路径，GATE_ROOTS 用 {ContraFan, ContraFanDeep, TameLp} 织网）。
- **依赖关系**：CF-4 依赖 CF-3（分离步）；两者都**不**依赖 A10 mqmsmab / A11 / A12，
  与 A2 `contraveningNegative`、A5 `hypermapOfFanNeg` 平行。双核闭合后：
  `#print axioms contraveningFan`（Assembly.lean:922）与
  `#print axioms the_kepler_conjecture_from_interfaces` 中经 contraveningFan 流入的
  sorryAx 断流；e2e-debt-map.md B 表"深几何双核"行划除，DEBT.md 重算。
- **优先级建议**：若与 A 表数据线（A11/A12 等重型机）抢窗口，CF-3 的性价比最高
  （250–400 行解锁半张 B 表行 + CF-4 的入场券）；CF-4 三波建议排在 CF-3 之后连续排期，
  避免模块长期 half-dirty。

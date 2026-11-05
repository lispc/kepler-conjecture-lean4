# ContraFan 四点终端引理侦察（2026-10-23，Lane H 交付）

> 快照：`lane_snapshots/contrafan-scout/`。结论：LEMMA_4_POINTS_FINAL 机械为主 ~80%、无真数学缺口；
> ContraFanDeep.lean 已零 sorry，余链 = 4 波 1,100–1,700 行；HOL 闭包实测 4,240 行（旧估值 3,800 低估）。

---

# ContraFan `LEMMA_4_POINTS_FINAL` 侦察报告（SCOUT）

> 车道：ContraFan LEMMA_4_POINTS_FINAL 只读侦察（完全只读，零构建、零 tracked 写）。
> 基线：main @ `1355f2bc`（CF-4d 落账）。交付：本文件、`DEP_MAP.tsv`、`WAVES.md`、`MD5SUMS`。
> 方法：CKQOWSA_4.hl 全文件调用图（48 个顶层声明逐一 grep 引用行→按区间归属消费者）、
> ContraFanDeep.lean 全部 53 个声明清单与签名、HOL 关键证明段逐段读。

## 0. 结论速览

1. **总判：机械为主（~80%），无真数学缺口。** 剩余工作 = HOL 旋转归一机器的
   Lean 装配（kit 已 95% 就位）+ 一个路线 B 同类的多项式角点不等式。
   总估 **~1,100–1,700 Lean 行**（中位 ~1,400），4 波。
2. **最大事实修正：这份债的大头已经还了。** `ContraFanDeep.lean`（2,602 行）经
   CF-4a/b/c/d 四波（f25bcc49→dd20ae50→d544b010→1355f2bc）已**零 sorry**：
   HOL 链前段 CKQOWSA_4.hl:22-2869（≈2,850 行，含 665 行最大件
   `continuous_lemma_aff_ge`）全部移植闭合。 ContraFan.lean:613 的 sorry 是
   **全链最后一枚**。旧文档"约 3,800 行链"指整条 HOL 链，不是剩余量。
3. **旧估值核实**：四点链 HOL 闭包 = CKQOWSA_4.hl:22-4270 减 9 行死码
   （PROJECTION_NEG/SUB 无消费者）= **4,240 行**（占全文件 99.8%），
   外加 ETA_Y_4_POINTS_INEQ（Inequalities.hl:356-372）等外部锚 ~35 行。
   "3,800"低估、"4,700"是把三点链混入的口径。其中已移植 ≈2,850 行，
   **剩余 ≈1,390 行 HOL**（:2870-4270）。
4. **剩余件**（全部 b 类机械，仅 W3a 算"新数学"但属角点验算级）：
   分离平面重装（60–120）· dot_of_dist2（10–20）· rotation1（150–250）·
   rotation1_full（60–100）· 投影距离 helper（20–40）· segment_inter_conv
   （80–150）· **rotation2（250–400，全计划最大单件）**· rotation2_full
   （60–100）· etaY 盒界（40–80）· 外心恒等（120–200）· 终局矛盾（60–100）·
   终件装配 + 接线（85–155）。
5. **三点路线可平移性**：CF-3 的路线 B（二次型角点恒等 + 有理余弦界）**不能
   替代**四点的连续旋转归一（终局代数需要 ‖v1‖=‖v3‖=2、四交叉距=2 的等式
   才闭合，归一必须旋转）；但 CF-3 孪生 `cf4_LEMMA_3_POINTS_FINAL`(:283) 作为
   分离步的 4 次调用件**已是** W1a 的现成积木。真正的"路线平移"发生在终局：
   W3a etaY 盒界 = 路线 B 同款纯有理/角点论证，替代 HOL 的
   `ETA_Y_4_POINTS_INEQ` 移植。
6. **e2e 收益**：闭合后消灭 e2e 直源 `Kepler.Text.ContraFan.LEMMA_4_POINTS_FINAL`
   （map:88，parent=fan7_4_0），净 −1；DEBT.md「Text/ContraFan.lean | 1」清零；
   「深几何双核」欠账结清。

## 1. 陈述精确化

**Lean**（ContraFan.lean:605-614，与 HOL 逐字对齐，无弱编码；`affGe` 取
Geom/Aff.lean 闭锥，与 HOL `aff_ge` 同义——前驱 scout §5.1 已核，不要"顺手"
改开锥）：

```
{v1 v2 v3 v4 : V3}
  (hb1..hb4 : v_i ∈ ballAnnulus)                    -- 2 ≤ ‖·‖ ≤ 2h0 = 2.52
  (hd13l : dist v1 v3 ≤ 2*h0) (hd24l : dist v2 v4 ≤ 2*h0)   -- 两条"长对角" ≤ 2.52
  (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
  (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)   -- 四条"边" ≥ 2
  (hd13 : 2 ≤ dist v1 v3) (hd24 : 2 ≤ dist v2 v4)   -- 长对角也 ≥ 2
⊢ affGe {0} {v1,v3} ∩ affGe {0} {v2,v4} = {0}
```

几何内容：环带（半径 [2, 2.52] 球壳）中取四点，"对边"结构（v1v3、v2v4 两条
对角线长度 ≤ 2.52，四条连接边 ≥ 2）——则两个原点锥只能交于原点。这是
contravening fan 章「两条 ESTD 边的锥交分配律」`fan7_4_0`（ContraFan.lean:934，
消费点 :945）的四点核，向上经 ESTD_fan7/contraveningFanTl 进主定理。

**HOL**（CKQOWSA_4.hl:4093-4096）：同构。证明骨架（:4097-4270）：
反设 p ≠ 0 在双锥内 → 二系数表示（`points_in_aff_ge_0_2`）→ 归一子目标
（:4135-4185，系数缩放把 p 拉到 segment 上）+ WLOG 对换 →
`lemma_4_points_rotation2_full`（把 ‖v1‖,‖v3‖ 归一到 2，交不变量
segment∩conv 形）→ `lemma_4_points_rotation1_full`（四条交叉距离归一到恰 2，
交不变量 cone 形）→ `lemma_4_points_contradiction`（平行四边形 + ETA_Y 代数
矛盾）。**W1 件 `cf4_cone_inter_imp_segment_conv`（ContraFanDeep:540）已把
反设到"归一 + WLOG"这一整段证掉**（含对称对换分支，:563-581）。

## 2. 依赖链全图

### 2.1 调用图实测（CKQOWSA_4.hl 内部）

方法：对 48 个声明逐一提取全部引用行号，按定义区间归属消费者。结论：
**闭包 = 全文件**（4,249 行声明区 − 9 行死码 PROJECTION_NEG/SUB = 4,240 行）。
分层（下游 → 上游）：

```
L0 终件      LEMMA_4_POINTS_FINAL :4093（178 行证明）
L1 终局      lemma_4_points_contradiction :4035 ← PARALLELOGRAM_LAW :4028
             ← lemma_4_points_circumcenter :3866（162 行）← DIST_SQR :31
             ← estd_non_collinear_lemma :45；外部 ETA_Y_4_POINTS_INEQ
L1 旋转归一  lemma_4_points_rotation2_full :3814 ← rotation2 :3379（435 行！）
             ← separation_plane_4_points :2870、rotation_lemma_segments :1395、
               segment_inter_conv :3266、continuous_lemma_dec :967、
               continuous_lemma_aff_ge :2204、zero_not_between_estd :117、
               IN_INTERVAL_1 :22、PROJECTION_{ZERO,LINEAR,DIST_SPECIAL_*}、
               segment_inter_aff_ge_ends :373
             lemma_4_points_rotation1_full :3203 ← rotation1 :3003（200 行）
             ← separation_plane_4_points、rotation_about_axis :1676、
               continuous_lemma_aff_ge :2204、zero_not_between_estd、IN_INTERVAL_1
L2 穿越机器  continuous_lemma_aff_ge :2204（665 行）← in_aff_ge_cases :1928、
             segment_intersects :2138、continuous_intersection_point :1785、
             continuous_lemma_inc/dec :785/:967、in_affine_hull_lemma :410、
             affine_hull_3_plane :445、zero_not_between :55、points_in_aff_ge_0_2 :313
             rotation_lemma_segments :1395（280 行）← rotation_lemma_special :1012、
             aff_ge_inter_segments :1238、rotation_dist_decrease_lemma :624(+special :758)
             rotation_about_axis :1676 ← rotation_lemma_special、PROJECTION 四件
L3 代数小件  aux_ineq :533、projection 套件 :131-283、aff_ge_0_2 三小件 :284-372、
             zero_not_between(_estd)、estd_non_collinear_lemma、IN_INTERVAL_1、DIST_SQR
```

外部锚：`h0 = 1.26`（sphere.hl:203，2h0 = 2.52）、`ball_annulus`/`in_ball_annulus`、
`eta_y/eta_x/ups_x`（sphere.hl:122-135）、`ETA_Y_4_POINTS_INEQ`
（Inequalities.hl:356-372，纯盒式有理论证）、HOL 库（CONVEX_HULL_3_ALT、
IN_SEGMENT、IVT 等）。

### 2.2 我的行数（对旧估值的修正）

| 口径 | 行数 | 说明 |
|---|---|---|
| HOL 链内部闭包 | **4,240** | CKQOWSA_4.hl:22-4270 − 9 死码；旧"~3,800"低估 |
| + 外部锚 | ~4,275 | ETA_Y_4_POINTS_INEQ 17 行 + sphere.hl defs ~15 行 |
| 其中已移植（CF-4a/b/c/d） | ≈2,850 | :22-2869 区段 + 终局预备 → ContraFanDeep 2,602 行 Lean，零 sorry |
| **剩余 HOL** | **≈1,390** | :2870-4270（分离 132 + rot1 199 + rot1full 62 + seg_conv 112 + rot2 434 + rot2full 51 + circumcenter 161 + 平行四边形 6 + 矛盾 57 + 终件 177）+ 外部 ETA_Y 17 |
| （不在剩余内） | 280 | rotation_lemma_segments :1395 被「任意连续族不变量」范式吸收，无需单移 |
| ContraFan.lean:38 的"4,700" | — | 混入三点链口径；ContraFan.lean:604 与 TameLp.lean:794 的"3,800"为内部闭包低估 |

### 2.3 与 ContraFanDeep 的对账（inventory drift 警报）

- docs/e2e-debt-map.md:105 与 ContraFanDeep.lean:24 头注记宣称的
  **`cf4_separation_plane_4_points` 在现文件不存在**——CF-4a 落过
  （commit f25bcc49），CF-4b 重构（dd20ae50"继承前驱骨架修复"）时溶散成
  §3 的私件群（:593/:648/:679/:745/:763/:777/:849/:2122）。W1a 需把陈述
  重新装配（积木全在，纯装配活）。
- 头注记 :2528 提到的 `cf4_dot_of_dist2` **尚不存在**（只在 docstring 里
  立项），是 W3b 的输入件。
- ContraFanDeep **不被任何模块 import**（grep 实测）；ContraFan.lean 未 import
  Deep——接线（W4）未发生，方向正确（Deep 不得回头 import ContraFan）。

## 3. 逐条分类

**统计：(a) 已证 41 件（其中 3 件"溶散/内联"需注意）+ dead 2 件；(b) 机械移植
9 件；(c) 桥 1 件；(d) 真缺口 0 件。** 逐件表见 `DEP_MAP.tsv`（48 行，含行号、
Lean 对应物、估行数）。要点：

- **(a) 已证**：整条穿越机器（665 行大件 `cf4_continuous_lemma_aff_ge`:2204、
  `cf4_ivt_first_hit/dec`:1918/:1976、`cf4_in_aff_ge_cases`:1993、
  `cf4_segment_intersects_aff_ge`:2122、`cf4_continuous_intersection_point`:1559、
  `cf4_aff_ge_inter_segments`:1506）+ 旋转族（`cf4_rotation_about_axis`:1392、
  `cf4_rotation_family_special`:1205、`cf4_rotation_lemma`:1038、
  `cf4_rotation_dist_decrease`:909）+ 分离积木 + 外心存在/唯一
  （:2540/:2564，走 Mathlib `AffineIndependent.existsUnique_dist_eq`）+
  全部代数小件。Mathlib 直接覆盖：PARALLELOGRAM_LAW、区间/IVT 记账。
- **(b) 机械移植**（HOL → Lean，kit 组装）：见 §0.4 清单。
- **(c) 桥**：仅 `rotation_lemma_segments`（HOL:1395）——它 = "族构造 + 两条
  距离控制 + 交不变量"三合一；Lean 侧范式已变为 `cf4_rotation_about_axis`
  （族 + 双距离：结论自带 ∀t c, dist(f t, c•d) = dist v (c•d)）×
  `cf4_continuous_lemma_aff_ge`（对任意连续族的交不变量）的组合，
  不需要单移，最多 0–50 行胶水。两侧具名：HOL rotation_lemma_segments ↔
  Lean cf4_rotation_about_axis + cf4_continuous_lemma_aff_ge。
- **(d) 真缺口：无。** 最接近缺口的 W3a（etaY 盒界）在 HOL 里就是纯有理数
  算术（REAL_RAT_REDUCE_CONV 收口），数学上无未解内容；W3b 外心恒等是
  162 行内积代数，预备件已证。

## 4. 三点路线可平移性（逐 kit）

对照 `cf4_LEMMA_3_POINTS_FINAL`（ContraFanDeep:283-364，路线 B twin）与
kit 清单：

| kit（ContraFanDeep 行） | 内容 | 四点场景判定 |
|---|---|---|
| quad_corner :190 / cos_ge_1031 :212 / cos_le_2719 :241 / two_arccos_gt :261 | 路线 B 数值件（二次型角点 + 有理余弦界） | **结构性不适用**（三点内角论证专用）；四点终局换 W3a/W3c（etaY 盒界 + 平行四边形），同为"纯数值 + 逐角点"精神 |
| cf4_LEMMA_3_POINTS_FINAL :283 | 三点锥内反证 twin | **直接用**：分离步 4 次调用件（W1a 消费），CF-4a 起就在用 |
| dot_pos_lemma :367 / estd_non_collinear_lemma :389 | annulus 基础件 | **直接用**（W3c 非共线输入） |
| affGe_0_2_char :119 / cf4_cone_mono :763 / cf4_segment_mem_cone :777 / cf4_segment_inter_aff_ge_ends :679 | 锥/线段刻画 | **直接用**（W1a、W2b 消费） |
| cf4_not_between_estd :593 / cf4_zero_not_between :648 | 0 不在段上 | **直接用**（W1c/W2c 的 hnb 前提） |
| cf4_rotation_dist_decrease :909 | 旋转不增距（代数版） | **直接用**（端点论证备用） |
| cf4_rotation_lemma :1038 / cf4_rotation_family_special :1205 / cf4_rotation_about_axis :1392 | 旋转族三件 | **直接用**（W1c 用 about_axis；W2c 用 about_axis 平移轴；family_special 是 IVT 端点的备胎） |
| cf4_aff_ge_inter_segments :1506 / cf4_continuous_intersection_point :1559 | 换端点传递 / 交点连续 | **直接用**（cf4_continuous_lemma_aff_ge 内部件；若 W2c 需要显式交点追踪则取用） |
| cf4_ivt_first_hit/dec :1918/:1976 | 首穿打靶 | **直接用**（W1c 打 dist(f t,v4)=2、W2c 打 ‖f t+v2‖=2） |
| cf4_in_aff_ge_cases :1993 / cf4_segment_intersects_aff_ge :2122 / cf4_continuous_lemma_aff_ge :2204 | 穿锥判别 / 大件 | **直接用**（W1c/W2c 的交不变量传递；这是"连续旋转链"里最险的分析部分，已闭合） |
| cf4_circumcenter3_exists/Unique :2540/:2564 | 外心预备 | **直接用**（W3b 唯一性认定；也可绕开走显式 α β） |
| cf4_cone_inter_imp_segment_conv :540 | 终件第一子目标（含 WLOG） | **直接用**（W4 首件；HOL :4135-4250 的对应段全部免移植） |
| PackingAuto25.p25_radv_etay_core :999 | 三角外接圆半径 = √(x1x2x3/upsX) | **加参数改造后复制**（private 不可 import；W3b 按 docstring 路线重推 60–80 行） |
| IneqClosureDefs.etaY :620 / SphereKit.upsX :72 | eta/ups 真体 | **直接用**（新增 import Kepler.Text.IneqClosureDefs，无环已核：闭包 {SphereKit→{Azim,PackingAuto5}, PackingAuto2} 无人引 Deep/ContraFan） |

**一句话**：三点波的遗产在四点的价值不在"绕开旋转"（那只在三点成立），
而在把旋转机器本身造成了通用件——剩余波次是纯组装。

## 5. 波次计划与天花板

见 **`WAVES.md`**（分波表 + 每波处方 + 验收）。骨架：

- **W1**（机械，低-中风险）：分离重装 + dot_of_dist2 + rotation1 + rotation1_full。
  估 280–490 行。
- **W2**（机械，中-高风险）：投影 helper + segment_inter_conv + rotation2 +
  rotation2_full。估 410–690 行。**rotation2 是全计划唯一无把握单件**。
- **W3**（代数，低-中）：etaY 盒界 + 外心恒等 + 终局矛盾。估 250–400 行。
- **W4**（装配 + 接线，最后原子落地）：终件 + ContraFan.lean 2–3 行。估 85–155 行。

**诚实天花板**：W1+W2+W4（机械）~830–1,270 行可承诺，成功率 ~80–85%；
W3 ~250–400 行，成功率 ~85–90%（数值 margin 已手验：角点 (4,4,4) 富余 41.6、
最紧角 (6.3504³) 富余 ≈10.08、终局 8.8+6.3504=15.1504<16）。合计
**~1,100–1,700 行、4 波、期望 3–6 个工作日（单工人）**；无真数学风险，
唯一工期风险是 rotation2 的端点代数膨胀（缓解：checkpoint 中转陈述，
见 WAVES §4）。

## 6. 给编排者的上下文笔记（合并入 playbook §5）

1. **cf4 kit 签名速查**（填 W1–W4 的工人直接照抄消费）：
   `cf4_rotation_about_axis(d v w)(hd : d≠0)(hvw : v−proj≠0)(hww : w−proj≠0) :
      ∃ f a b, 0<a ∧ Continuous f ∧ f 0=v ∧ f 1=a•w+b•d ∧
      (∀ t c, dist(f t, c•d)=dist v(c•d)) ∧ (∀ t∈Icc 0 1, dist(f t)w ≤ dist v w)`
   ——注意它**同时**保到轴线的全部距离（v2、v4 都在轴上时一次拿双保）；
   `cf4_continuous_lemma_aff_ge(f w h)(hf : ContinuousOn f (Icc 0 h))
      (hstart : segment(f 0)w ∩ cone{v1,v2}≠∅)(hnb : ∀t∈Icc 0 h, 0∉segment(f t)w)
      (hcol : ¬Collinear{0,v1,v2})`——结论是"全程有交 ∨ 首穿点入锥/端点入锥"
      的二选一，W1c/W2c 里要么全程用、要么在首穿点处排空。
2. **W2c 的轴平移**：HOL rotation2 的轴是直线 v2+ℝ(v4−v2)（不过原点）；
   Lean 里对 v := v1−v2 调 cf4_rotation_about_axis(d := v4−v2) 再平移回去。
   到 0 的距离（要打到 2 的目标函数）是 t 的连续函数——用 cf4_ivt_first_dec。
3. **文档需同步的 drift**（本报告已核）：e2e-debt-map.md:105 的
   `cf4_separation_plane_4_points` 名已失效；ContraFanDeep 头注记"移植状态"
   段落同；前驱 scout（docs/scouts/contrafan-scout.md）§4.2 表的 step 4 已被
   CF-4d 完成，step 5/6/7 = 本报告 W1c-W2d / W2 全部 / W3-W4。
4. **不要碰的两个名字**：`PackingAuto21.eta_y`（同名不同库，模块互斥）、
   `LocalAuto6.upsX_p6`（不同 HOL 函数）。eta/ups 一律走
   IneqClosureDefs.etaY / SphereKit.upsX。
5. **ContraFan.lean:598-613 的 DISCHARGES 注记**在 W4 接线时要改写
   （"骨架占位"→指向 ContraFanDeep 终件）；同文件 :32/:36 的链存档注记
   的"约 4700 行"建议按本报告 §2.2 口径修正。

---

# LEMMA_4_POINTS_FINAL 分波施工表（WAVES）

> 基线：main @ 1355f2bc（CF-4d 落账 commit）；e2e 直源 1 枚 =
> `Kepler.Text.ContraFan.LEMMA_4_POINTS_FINAL`（parent = `fan7_4_0`，
> e2e-reachability-map.tsv:88）。
> 现状：**ContraFanDeep.lean（2,602 行）已零 sorry**——HOL 链前段
> （CKQOWSA_4.hl:22-2869 ≈ 2,850 行）全部移植闭合。剩余 = HOL 3003-4270
> 的旋转归一 + 终局代数块 + 接线，约 **1,400 行 HOL → 估 1,100–1,700 Lean 行**。

## 0. 施工拓扑与债务守恒

```
W1 分离重装 + rotation1(+full) ─┐
W2 segment_inter_conv + rotation2(+full) ─┤
W3 终局代数块（dot_of_dist2/外心恒等/etaY盒界/parallelogram 收口）─┤
                                                                  ├─> W4 装配 + 接线
(cf4_cone_inter_imp_segment_conv 已证：锥交 → segment ∩ conv，含 WLOG 对换) ─┘
```

- **ContraFanDeep 目前无人 import、全模块零 sorry**。W1–W3 的半成品即使带
  `sorry` 也不进任何 import 闭包 → e2e 直源数**恒不变**（仍是 1，即
  ContraFan.lean:613 那枚）。
- **W4 接线（ContraFan.lean 加 import + 把 :613 的 `sorry` 换成对
  ContraFanDeep 终件的转发）必须最后做且与终件同波原子落地**：接早了只会把
  直源从 ContraFan 搬家到 ContraFanDeep（数不变），但会让闸门 GATE_ROOTS
  提前织入 Deep 模块。叶子先行、装配最后，与 PA18 侦察结论同一纪律。
- 全部新件都在**同一个 tracked 文件** ContraFanDeep.lean（W4 另加 ContraFan.lean
  2–3 行）→ tracked 编辑串行；并行价值在 /tmp 探针。
- 方向约束（模块头注记）：**ContraFanDeep 不得 import ContraFan**（接线方向
  ContraFan → ContraFanDeep）。新增 `import Kepler.Text.IneqClosureDefs` 已核实
  无环（IneqClosureDefs → {SphereKit, PackingAuto2}；SphereKit → {Azim,
  PackingAuto5}；全闭包无人 import ContraFan/Deep；PackingAuto2 本就在
  Deep 的 import 里）。

## 1. 分波表

| 波 | 目标（新 Lean 件） | HOL 锚点 | 证明处方（精确 kit） | 预估 | 风险 | e2e |
|---|---|---|---|---|---|---|
| **W1a** | `cf4_separation_plane_4_points`（重装；CF-4a 曾有此名，CF-4b 重构时**溶散成私件**，需把陈述重新装配） | CKQOWSA_4.hl:2870-3002 | n := ±(cf4Cross v2 v4)（:790-850 kit）；`cf4_not_between_estd`(:593) + `cf4_LEMMA_3_POINTS_FINAL`(:283) 4 次排四点入锥；`cf4_plane_repr`(:849) 参数化；`cf4_segment_inter_aff_ge_ends`(:679) + `cf4_segment_intersects_aff_ge`(:2122) 收两支。结论形：`∃ n ≠ 0, ⟪v1,n⟫ ≤ 0 ≤ ⟪v3,n⟫ ∧ v2,v4 ⊥ n`（v1·n 与 v3·n 反号） | 60–120 行 | 低（积木全在，纯装配） | 恒 1 |
| **W1b** | `cf4_dot_of_dist2`：‖v‖=2 ∧ dist(v,w)=2 ⟹ ⟪v,w⟫ = ‖w‖²/2 | :3870-3882（circumcenter 首子目标） | dist² 展开 = ‖v‖²+‖w‖²−2⟪v,w⟫，`real_inner_self_eq_norm_sq` + linarith | 10–20 行 | 极低 | 恒 1 |
| **W1c** | `cf4_rotation_1`：绕轴 ℝ•v2 转动 v1（保 ‖v1‖、保 dist(·,v2)），落点 v1' 满足 dist(v1',v4)=2 恰等，且 segment[v1',v3] ∩ cone{v2,v4} ≠ ∅ | :3003-3202 | 族 = `cf4_rotation_about_axis`(:1392, d:=v2)——结论自带 ∀t, dist(f t,c•v2)=dist(v1,c•v2)（c=0 保范、c=1 保 v2 距）+ dist(f t,v3) ≤ dist(v1,v3) ≤ 2h0；穿越不变量 = `cf4_continuous_lemma_aff_ge`(:2204, v1:=v2, v2:=v4, w:=v3)（0∉segment[f t,v3] 由 f t ∈ annulus + `cf4_not_between_estd`）；t=1 端点 f 1 = a•v3 + b•v2 (a>0) 落 cone{v2,v3}，端点距离论证（HOL :3140-3196 的 dist(f 1,v4)<2 或 v4 入锥两支）；IVT 打靶用 `cf4_ivt_first_hit`(:1918) 作用 g t := dist(f t,v4) | 150–250 行 | 中（端点代数分支） | 恒 1 |
| **W1d** | `cf4_rotation_1_full`：两次 W1c（v1 绕 v2、v3 绕 v4），四条交叉距离全打成恰 2 | :3203-3265 | 两次调用 + 距离 chased（HOL :3220-3260 逐行）；注意结论保 ‖·‖（norm v1'=norm v1） | 60–100 行 | 低中 | 恒 1 |
| **W2a** | 投影距离小 helper（⊥ 投影不增对投影平面内点距离） | :267-283（PROJECTION_DIST_SPECIAL_LE） | Mathlib 正交投影极小性或手扩 ⟨x−p, p−y⟩=0；rotation2 :3573/:3587 消费 | 20–40 行 | 低 | 恒 1 |
| **W2b** | `cf4_segment_inter_conv`：投影平面内 segment ∩ 射线锥 ≠ ∅ ⟹ 原空间 segment[v1,v3] ∩ conv{0,v2,v4} ≠ ∅ | :3266-3378 | 仿射二系数展开 + 投影线性；`cf4_plane_repr` + `affGe_0_2_char`；轴足 ≠ 0 分支（v2、v4 与轴足共线情形） | 80–150 行 | 中（三维仿射代数摩擦） | 恒 1 |
| **W2c** | `cf4_rotation_2`：绕轴 v2 + ℝ(v4−v2) 转动 v1（平移到过原点轴后调 W1 机器；保 dist 到 v2 与 v4 两条），把 ‖v1'‖ 打到恰 2，交不变量换成 cone 形 | :3379-3813（435 行） | 平移 v := v1−v2，d := v4−v2；`cf4_rotation_about_axis`(d:=d) 保 dist 到轴线上 c•d（含 v2 c=0、v4 c=1——平移回 v2+ℝd）；穿越传递 = `cf4_continuous_lemma_aff_ge` 直接吃连续族（**HOL 的 rotation_lemma_segments :1395-1675 被「任意连续族不变量」范式吸收，无需单移**）；`cf4_ivt_first_dec`(:1976) 打靶 ‖f t + v2‖ 下穿 2；W2a helper 给端点 ‖f 1 + v2‖ ≤ 2；W2b 把 segment∩conv 换成 segment∩cone 收尾 | 250–400 行 | **高**（全计划最大单件；HOL 435 行里投影/端点/三分支都密） | 恒 1 |
| **W2d** | `cf4_rotation_2_full`：两次 W2c，‖v1‖=‖v3‖=2 且 dist(·,v2)/(·,v4) 保持，交不变量 cone 形 | :3814-3865 | 两次调用（第二次对 v3，轴/距对称） | 60–100 行 | 低中 | 恒 1 |
| **W3a** | `cf4_etaY_box`：y1,y2,y3 ∈ [2,2h0] ⟹ etaY y1 y2 y3² ≤ 2.2（即 x_i=y_i²∈[4,6.3504] 上 x1x2x3 ≤ 2.2·upsX） | Inequalities.hl:356-372（ETA_Y_4_POINTS_INEQ） | `etaY`/`upsX` 用 IneqClosureDefs.lean:620 / SphereKit.lean:72 真体（**不要 import PackingAuto21 的同名件**——虽然其 :166 现也指真体，但模块不共库）；固定 x2,x3 时 p := 2.2·upsX − x1x2x3 是 x1 的严格凹二次（首项 −2.2）→ 区间最小在端点 → 逐变量归结 8 角点，全数值 `norm_num [h0]`（手工验算：角 (4,4,4) 富余 41.6，角 (6.3504³) 最紧富余 ≈10.08，全正）；upsX>0 由 x1x2x3 ≤ 2.2·upsX 与 64 ≤ x1x2x3 直接导出，免另证 | 40–80 行 | 低中（数值 corner 论证新写；HOL 原证同为纯有理算术） | 恒 1 |
| **W3b** | `cf4_circumcenter_char`：norm v1=norm v3=2 ∧ 四交叉距=2 ∧ segment[v1,v3]∩cone{v2,v4}≠∅ ⟹ 中点 m=(v1+v3)/2 ∈ cone{v2,v4} ∧ dist m 0=dist m v2=dist m v4 ∧ ‖m‖² = etaY(‖v2‖,‖v4‖,dist v2 v4)² | :3866-4027 | `cf4_dot_of_dist2`×4 给 v1·v2=v1·v4=v3·v2=v3·v4=‖v2‖²/2、‖v4‖²/2 型；交点 x 两表达式内积相减 ⟹ (1−2u)(4−⟪v1,v3⟫)=0：u=1/2 主支 + v1·v3=4 ⟹ v1=v3 退化支（C–S 等号，HOL :3940-3990）；m 等距三条由 ⟪m,v2⟫=‖v2‖²/2 平方展开；半径式走 `p25_radv_etay_core` 的显式 α β 公式（**PackingAuto25.lean:999 是 private 不能 import，按其注释路线重推 ~60-80 行**；或引 `cf4_circumcenter3_existsUnique`(:2564) 唯一性认定）；非共线 {0,v2,v4} 由 `estd_non_collinear_lemma`(:389) | 120–200 行 | 中（退化支 + 半径式重推） | 恒 1 |
| **W3c** | `cf4_4_points_contradiction`：W3b + ‖v1‖=‖v3‖=2 ∧ 四交叉距=2 ∧ dist(v1,v3) ≤ 2h0 ∧ v2,v4 ∈ annulus ∧ 2 ≤ dist(v2,v4) ≤ 2h0 ⟹ False | :4035-4092 + :4028 | Mathlib 平行四边形恒等式（PARALLELOGRAM_LAW 同文）：16 = ‖v1+v3‖² + dist(v1,v3)² = 4‖m‖² + dist²；W3a 给 4‖m‖² ≤ 8.8；dist ≤ 2h0 给 dist² ≤ 6.3504；8.8+6.3504 = 15.1504 < 16 矛盾（数字 margin 0.8496）；¬collinear 喂 W3b | 60–100 行 | 低（纯不等式链） | 恒 1 |
| **W4** | `cf4_LEMMA_4_POINTS_FINAL`（ContraFanDeep 终件）+ 接线：ContraFan.lean `import Kepler.Text.ContraFanDeep` + :613 改 `cf4_LEMMA_4_POINTS_FINAL …` | :4093-4270 | `cf4_cone_inter_imp_segment_conv`(:540，已证，内含 WLOG 对换) → `cf4_rotation_2_full` → `cf4_rotation_1_full`（保范，给四交叉距=2）→ `cf4_4_points_contradiction` 反证；假设 chase 全部由旋转件结论自带（annulus/dist/SIDE 表逐项搬运，HOL :4240-4268 的 ASM_REWRITE 对应） | 80–150 + 5 行 | 中低（装配面大但件件有签名） | **1 → 0（该源消灭）** |

## 2. 工作量汇总与诚实天花板

| 项 | 数 |
|---|---|
| 剩余 sorry 件 | 0 枚现存在账 sorry 需填（ContraFanDeep 已净）；新增待证件 10（W1a-W2d、W3a-W3c、W4 终件） |
| 预估总行数 | **~1,100–1,700 行**（中位 ~1,400）；其中机械（W1+W2+W4）~830–1,270，代数（W3）~250–400 |
| 波数 | 4 波（W1 / W2 / W3 / W4；W1、W3 可并行——不同私件互不依赖，但同文件须串行编辑） |
| 真数学缺口 | **0**。唯一"新数学" = W3a 盒式多项式角点论证（路线 B 同类，数值已预验）与 W3b 半径式重推；无未解几何 |
| 可承诺量 | W1+W2+W4 机械 ~830–1,270 行，成功率 ~80–85%（风险集中于 W2c rotation2 端点代数膨胀） |
| W3 成功率 | ~85–90%（角点不等式 margin 已手验为正；最大摩擦在 sqrt/upsX 正负性记账，已给免证路线） |
| e2e 收益 | 该波单源闭合：`Kepler.Text.ContraFan.LEMMA_4_POINTS_FINAL` 消失，净 −1；同时 ContraFan.lean 全模块归零 sorry（DEBT.md「Text/ContraFan.lean | 1」行清零） |

## 3. 每波收工必做

1. `lake build Kepler.Text.ContraFanDeep`（W4 加 `Kepler.Text.ContraFan`）自然退出 0 error；
2. `#print axioms` 新件 ∈ {propext, Classical.choice, Quot.sound}（W4 后终件同）；
3. W4 前重跑 e2e map：确认 W1–W3 期间源清单**恒不变**（Deep 无消费者）；
4. W4 合并后重跑 e2e map：确认该源消失且**无新源**（哈欠口：rotation 件结论 chase
   漏一项会直接编译失败，不会静默产生弱陈述——陈述冻结由签名保证）。

## 4. 风险与开放问题

- **W2c rotation2 是唯一无把握单件**（HOL 435 行）。缓解：cf4_continuous_lemma_aff_ge
  已把最难的连续分析吸收；剩余是投影代数 + 端点 IVT。建议该波单件设 checkpoint，
  证出「族 + 距离双保」中转陈述即交付，不留半成品。
- **inventory drift**：docs/e2e-debt-map.md 与 ContraFanDeep 头注记宣称的
  `cf4_separation_plane_4_points` 在现文件**已不存在**（CF-4b 重构溶散），消费方
  （W1c/W2c）需要 W1a 重装。文档同步责任在本波。
- **前驱 scout 两处 stale**：(1) PackingAuto21 `eta_y := sorry` 陷阱已失效
  （:166 现指真体 etaY）；(2) 其 CF-4 计划的 step 4（crossing invariant）已由
  CF-4d 超额完成，本表波次对应其 step 5/6/7。
- **W3b 半径式**：`p25_radv_etay_core` 是 private 不可 import；重推时注意
 它要求 `¬affineDependent` + 三对互异，均由 annulus 距离 ≥ 2 给出。
- **接环检查**：W4 后 `#print axioms Kepler.Text.ContraFan.LEMMA_4_POINTS_FINAL`
  应只剩标准三条——这是「深几何双核」清债的最终判据（ContraFan.lean:11/32 的
  DISCHARGES 注记同步改写）。

---

```
HOL引理名	HOL行号	分类	Lean对应物	估行数	备注
IN_INTERVAL_1	22-30	a	Mathlib Set.Icc/cf4_ivt_first_hit 内含	0	纯 [0,1] 区间算术；Deep 已吸收
DIST_SQR	31-44	a	Mathlib dist_sq 平凡	0	仅被 circumcenter 用；终端代数内联
estd_non_collinear_lemma	45-53	a	ContraFanDeep.lean:389	0	已证（私件）
zero_not_between	55-116	a	ContraFanDeep.lean:648 cf4_zero_not_between	0	结论形（3 合 1）
zero_not_between_estd	117-127	a	ContraFanDeep.lean:593 cf4_not_between_estd	0	已证
PROJECTION_ORTHOGONAL	131-134	a	内联（inner API/cf4_rotation_about_axis:1392 模式）	0	Mathlib inner 封闭
VECTOR_PROJECTION	135-139	a	内联（v−proj 分解，:1400s）	0	同上
PROJECTION_0	140-144	a	平凡	0	—
PROJECTION_ZERO	145-157	a	平凡	0	—
PROJECTION_LINEAR	158-165	a	Mathlib inner_smul/smul_add	0	—
PROJECTION_NEG	166-169	dead	（无对应物）	0	不在 L4F 闭包内（仅喂 PROJECTION_SUB）
PROJECTION_SUB	170-174	dead	（无对应物）	0	全文件无消费者，死码
PROJECTION_DIST2	175-215	a	内联代数	0	只喂 PROJECTION_DIST_SPECIAL_EQ
PROJECTION_SUM_DIST	216-231	a	内联代数	0	同上
PROJECTION_DIST_SPECIAL_EQ	232-266	a	内联（cf4_continuous_intersection_point:1559/rotation_about_axis:1392）	0	CF-4c 已消化
PROJECTION_DIST_SPECIAL_LE	267-283	b	新 helper（W2a）	20-40	rotation2 :3573/:3587 消费；Mathlib 正交投影极小性可替
aff_ge_0_2_eq_segment	284-291	a	定义级（Lean affGe/convexHull 同体）	0	仅被三个小件用
in_segment_imp_in_aff_ge_0_2	292-312	a	ContraFanDeep.lean:777 cf4_segment_mem_cone	0	已证
points_in_aff_ge_0_2	313-337	a	ContraFanDeep.lean:119 affGe_0_2_char	0	对偶形（显式二系数刻画）
aff_ge_0_2_SUBSET	338-372	a	ContraFanDeep.lean:763 cf4_cone_mono	0	已证
segment_inter_aff_ge_ends	373-409	a	ContraFanDeep.lean:679 cf4_segment_inter_aff_ge_ends	0	已证
in_affine_hull_lemma	410-444	a	ContraFanDeep.lean:1836 cf4_affSpan3_char	0	显式二系数刻画（含退化）
affine_hull_3_plane	445-497	a	ContraFanDeep.lean:849 cf4_plane_repr	0	已证
intersection_point_exists	498-532	a	内联于 cf4_continuous_intersection_point:1559	0	CF-4c 消化
aux_ineq	533-623	a	内联于 cf4_rotation_dist_decrease:909	0	CF-4b 消化（自带代数骨架）
rotation_dist_decrease_lemma	624-757	a	ContraFanDeep.lean:909 cf4_rotation_dist_decrease	0	已证
rotation_dist_decrease_special_case	758-784	a	内联于 cf4_rotation_family_special:1205 距离结论	0	已证
continuous_lemma_inc	785-965	a	ContraFanDeep.lean:1918 cf4_ivt_first_hit	0	sInf+IsClosed 路线，已证
continuous_lemma_dec	967-1011	a	ContraFanDeep.lean:1976 cf4_ivt_first_dec	0	取负归约，已证
rotation_lemma_special	1012-1237	a	ContraFanDeep.lean:1205 cf4_rotation_family_special	0	共线分支含 π 旋转族
aff_ge_inter_segments	1238-1394	a	ContraFanDeep.lean:1506 cf4_aff_ge_inter_segments	0	已证（Cramer 系数）
rotation_lemma_segments	1395-1675	c	cf4_rotation_about_axis:1392 + cf4_continuous_lemma_aff_ge:2204 组合吸收	0-50	**未单移**；「任意连续族不变量」范式覆盖其全部职责；rotation2 唯一消费者
rotation_about_axis	1676-1754	a	ContraFanDeep.lean:1392 cf4_rotation_about_axis	0	已证（正交分解平移）
continuous_solution_aux	1755-1784	a	内联于 cf4_continuous_intersection_point:1559	0	CF-4c 消化
continuous_intersection_point	1785-1927	a	ContraFanDeep.lean:1559 cf4_continuous_intersection_point	0	已证（Cramer+Gram）
in_aff_ge_cases_lemma	1928-2137	a	ContraFanDeep.lean:1993 cf4_in_aff_ge_cases	0	已证（Cramer 符号四分）
segment_intersects_aff_ge_lemma	2138-2203	a	ContraFanDeep.lean:2122 cf4_segment_intersects_aff_ge	0	已证
continuous_lemma_aff_ge	2204-2869	a	ContraFanDeep.lean:2204 cf4_continuous_lemma_aff_ge	0	全章最大件 665 行 HOL，CF-4d 按段闭合
separation_plane_4_points	2870-3002	b	cf4_separation_plane_4_points（W1a 重装）	60-120	**inventory drift**：CF-4a 落过（f25bcc49），CF-4b 重构溶散成私件（:593/:648/:679/:745/:763/:849/:2122 全在）；现文件无此名
lemma_4_points_rotation1	3003-3202	b	cf4_rotation_1（W1c）	150-250	cf4_rotation_about_axis(d:=v2) + cf4_continuous_lemma_aff_ge + cf4_ivt_first_hit 打靶 dist(f t,v4)；端点两分支
lemma_4_points_rotation1_full	3203-3265	b	cf4_rotation_1_full（W1d）	60-100	两次 W1c；保范、四交叉距打成恰 2
segment_inter_conv	3266-3378	b	cf4_segment_inter_conv（W2b）	80-150	投影平面仿射代数；喂 rotation2 收尾换 cone 形
lemma_4_points_rotation2	3379-3813	b	cf4_rotation_2（W2c）	250-400	**全计划最大单件**；平移轴 v2+ℝ(v4−v2)；rotation_lemma_segments 被「任意连续族」范式吸收；IVT 下穿 ‖·‖=2
lemma_4_points_rotation2_full	3814-3865	b	cf4_rotation_2_full（W2d）	60-100	两次 W2c；‖v1‖=‖v3‖=2
lemma_4_points_circumcenter	3866-4027	b	cf4_circumcenter_char（W3b）	120-200	预备已证：cf4_circumcenter3_exists:2540 / existsUnique:2564 / cf4_dot_of_dist2 待写（W1b, 10-20 行）；半径式按 p25_radv_etay_core（PackingAuto25.lean:999，private 不可 import）路线重推
PARALLELOGRAM_LAW	4028-4034	a	Mathlib 内积平行四边形恒等式	0	16 = ‖v1+v3‖²+‖v1−v3‖²
lemma_4_points_contradiction	4035-4092	b	cf4_4_points_contradiction（W3c）	60-100	8.8 + 6.3504 = 15.1504 < 16；依赖 W3a/W3b
ETA_Y_4_POINTS_INEQ（外部）	Inequalities.hl:356-372	b	cf4_etaY_box（W3a）	40-80	etaY=IneqClosureDefs.lean:620、upsX=SphereKit.lean:72 均真体；逐变量凹性→8 角点数值（角 (6.3504³) 富余 ≈10.08 全正）；前驱「PackingAuto21 eta_y:=sorry 陷阱」已失效（:166 现指真体）
h0/ball_annulus（外部）	sphere.hl:203 / Inequalities 用	a	ContraFanDeep.lean:49 inBallAnnulus / :56 two_h0=2.52	0	已证
LEMMA_4_POINTS_FINAL	4093-4270	b	cf4_LEMMA_4_POINTS_FINAL（W4 终件）+ ContraFan.lean:605 接线	80-150+5	锥交→cf4_cone_inter_imp_segment_conv:540（已证，含 WLOG 对换）→rot2_full→rot1_full→contradiction；接线后 DEBT「Text/ContraFan.lean|1」清零
```

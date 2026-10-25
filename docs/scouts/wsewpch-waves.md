# WSEWPCH 核拆波计划（WAVES）— Lane BH 2026-10-23

> 折算口径：对照 BDXKHTW 侦察经验（HOL 名义 540 → Lean 实测 505–955，系数 0.94–1.77）。
> 本核各波的 HOL 体多为"已证 kit 上的 refinement 噪声"（WSEWPCH 本体 1148 行中约六成是
> ASM_REWRITE/MESON 装配），纯几何组按 ~1.2×、hypermap 装配组按 ~1.5×、真数学巨件按
> 1.2–2.0× 折算。每波独立交付独立验收（文件级 axiom 审计 + sorry 计数 + 闸）。

## 波次总图（依赖关系）

```
W1(LA7纯几何) ─────────────────────────┐
W2(桥: p3↔p2打包 + LocalFan→_p3正向) ──┼─→ W4(lunar支) ─┐
W3(LA6轨道件+CIZMRRH) ────────────────┘                ├─→ W6(WSEWPCH装配+闭合)
W5a(SOL/NKEZBFC kit) → W5b(BGMIFTE) ───────────────────┘        ↓
                                                          TameLp:848 单行替换
```

- **W1/W3/W5a 立即可开**（不与在飞 BE/BK/BG/BF 冲突：poolc-edgefirst=PA18、pa2-rvfxzbu2=PA2/24、
  la16-jejtvgb=LA16+PA12、pa14=PA14、pa10=PA10；LA7 自 030ec864(09-19) 后无人动，TameLp
  自 ykit11(2b1c9f60, 10-23) 交付后空闲，LA5 自 e9ec8c13(10-13)"可填面清零"后让出名额）。
- W2 撞 AzimBridge（已清零、无主）与 LA3 头部（LA3 自 0ad09801 后无人在飞）——可开。
- 唯一共用文件风险：PA25/PA22 只读消费（真证件），零编辑零冲突。

## W1 —— LA7 纯几何组 discharge（立即可开）
- 内容：LA7 14 枚纯 V3 桩（DEP_MAP B 区）：AFFINE_HULL_3_GENERATED、COLLINEAR_AZIM_0_OR_PI、
  ANGLES_ADD_AFF_GE（先补 ANGLES_ADD_BETWEEN 私件或核 Mathlib `EuclideanGeometry` 角加法）、
  AFF_GE_SCALE_LEMMA、AZIM_SAME_WITHIN_AFF_GE(_ALT)、COLLINEAR_WITHIN_AFF_GE_COLLINEAR、
  GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE、UNION_AFF_GE_1_2、SIN_AZIM_MUTUAL_CROSS、
  CROSS_POSITIVE_MULTIPLE_AZIM_AXIS(_ALT)、GMLWKPK(_ALT/_SIMPLE)、FAN7/FAN_AFF_GT_CONDITION。
  其中 ORDER_AZIM_SUM2Pi_0 = PA25:10090 指标平移（n↦n+1），~30 行白送。
- 行数区间：**280–520**（HOL 几何体合计 ~200 行，系数 1.2–1.8；GMLWKPK 族为重写噪声）。
- 成功率 ~90%。风险：ANGLES_ADD_BETWEEN 若 Mathlib 无现形需自建（+80–150 行）。
- 验收：LA7 sorry 34→20；零 import 变更；LA7 纯追加。

## W2 —— 词表桥波（立即可开，撞 AzimBridge 无主文件需编排者确认归属）
- 内容：
  a) `_p2`↔`_p3` 逐对 rfl 桥（ordPairs/selfPairs/dartsOfHyp/ee/nn/ff/azimCycle/ivsAzimCycle/
     EE/dih2k/hasOrders），照 AzimBridge §1 `_p4`↔`_p3` 配方；
  b) `localFan_p3.of_LocalFan`（正向打包，无孤立前提 hno）：localFan_data + §2 主桥 +
     Dih2k↔dih2k_p3 双向桥（AzimBridge:682/:710 双真）装配；
  c) 顺带把 LA2:1488 与 LA7:444 的 LOCAL_FAN_ORBIT_MAP_EXPLICIT 双桩统一（建议 LA7 改名
     `_LA7` 后缀消唯一撞名，或在 (a) 落地后由 _p2 版运输）。
- 行数区间：**180–350**。
- 成功率 ~85%。验收：AzimBridge（或新模块）零 sorry 增量 + 一条
  `LocalFan → localFan_p2`（hno 下）样板定理可被下游消费。

## W3 —— LA6 轨道件 + CIZMRRH（立即可开）
- 内容：
  a) LA6 近机械件：CARD_IS_LEAST_CYCLE（HOL 21 行，唯一实质前提 LOFA_IMP_DIS_ELMS23 已真
     LA5:6263）、POINT_PRESENTED_IN_RHOND1（17）、LT_CARD_MONO_LOFA（13）、
     LOCAL_RHO_NODE_PAIR_E（11）、IVS_RHO_NODE_DIFF_ID、LOCAL_FAN_RHO_NODE_IVS；
  b) LOFA_IMP_ITER_RHO_NODE_ID → LOFA_IMP_ITER_RHO_NODE_ID2（MESON 链；主料
     LOOP_SET_DETER_FIRTS_ELMS/CARD_RECUSIVE_EQ/LE_CARDV_IMP_CARD_DETERED/ITER_CYCLIC_ORBIT
     全真 LA5/LA10）；
  c) CIZMRRH（LA3:1881，HOL 275 行三分 exclusive-or，hypermap_lemma 已真）。
- 行数区间：**350–650**（a+b ~120–250；CIZMRRH ~230–400）。
- 成功率 ~75–85%（CIZMRRH 的 hypermap 装配是主要变数；可拆 W3a/b）。
- 验收：LA6 sorry 60→54±，LA3 11→10。

## W4 —— lunar 支（W1/W2/W3 后）
- 内容：RHO_NODE1_MONO_WITH_AZIM（HOL 144，全树缺；依赖全真）→ HALP_CIRCLE_IS_INTERSECTION
  （HOL 165，LA5:7670 桩）→ HKIRPEP（HOL 45 = MESON 装配，LA5:7986 桩）。
- 行数区间：**400–750**。
- 成功率 ~70–80%。真数学缺口：HALP_CIRCLE 的半圆-仿射锥交刻画（球面组合，中等）。
- 验收：LA5 sorry 6→4。

## W5 —— generic 支（可与 W4 并行开工 W5a）
- W5a（立即可开）：SOL kit——NKEZBFC（LA2:1606）、SOL_LOFA_EQ_SUM_INANGLE_p9（LA9:747）、
  CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p9（LA9:768）、IN_V_IMP_AZIM_LESS_PI（全树缺）。
  行数 **200–400**；成功率 ~80%。
- W5b：BGMIFTE（LA7:662，HOL 1050 行，polar_fan 对偶巨件；消费 GENERIC_LOCAL_FAN_AZIM_POS
  + RHO_NODE1_INJECTIVE + JNVXCRC 展开 + SUM_IMAGE）。**本核最大单件**，行数 **700–1400**；
  成功率 ~60–70%（可再拆：极扇凸性 half / arc↔角对偶 half）。
- 验收：LA7 sorry →3（FAN_PERIMETER 族 3 枚留 W6）。

## W6 —— WSEWPCH 本体装配 + TameLp 闭合（收官）
- 内容：
  a) LA7 LocalFan-世界 foundation 桩（W2 桥上换形/运输）：RHO_NODE1_INJECTIVE、
     IVS_RHO_NODE1_IN_V、LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V、LOCAL_FAN_ORBIT_MAP_EXPLICIT(_IVS)、
     ITER_*_IDD、LOFA_IMP_ITER_IVS_RHO_NODE_ID、LOCAL_FAN_NOT_EMPTY_FF、
     LOCAL_FAN_NOT_CARD_FF_GE_2、FAN_PERIMETER_INVARIANT(_CARD_V)、FAN_PERIMETER
     （HOL 体 49+13+29 行，SUM_EQ_GENERAL 轨道重排）；
  b) KCHMAMG（HOL 280，LA5:5018；circular 支主件，依赖 FIRST_AZIM_CYCLE/AZIM_LAST_POINT/
     KOMWBWC/V_AZIM_SMALLEST_ELMS 全真 + LOFA_V_SUBSET_AFF_HULL(LA5:4895 桩) +
     WHEN_A_B_POS_ARCV_STABLE(缺)）；
  c) WSEWPCH 三分支装配（CIZMRRH 三分 + CARD V 良基归纳；circular=ORDER_AZIM_SUM2Pi_0 收口、
     lunar=两片 sum4_azim 望远镜 + COLLINEAR_AZIM_0_OR_PI 收口、generic=BGMIFTE+平角
     dart 分裂归纳）；
  d) dart-和桥（sum_face_rho_node1 内容：face_eq_image_rho_node1 + LOFA_IMP_BIJ_FF_V +
     LOCAL_FAN_CHARACTER_OF_RHO_NODE，~100–150 行）；
  e) TameLp `yk11_WSEWPCH_core`（= hcore：FAN_PERIMETER ▸ WSEWPCH + dart-和桥，~40–80 行）
     + :848 单行替换 + NEEDS 注记清理。
- 行数区间：**a 250–450 + b 350–650 + c 400–700 + d 100–150 + e 60–120 ≈ 1160–2070**
  （建议拆 W6a=foundation、W6b=KCHMAMG、W6c=WSEWPCH+闭合 三波）。
- 成功率：a/b ~80%；c ~65–75%。
- 验收：TameLp 文件级 statement-sorry 1→0；MQMSMAB 审计转标准三；e2e map 直源 +1。

## 总量与工期
- 合计 **~2570–4740 行**（中位 ~3600），6 大波（可拆 9 小波）；W1/W2/W3/W5a 四波立即可开，
  前置链 W4、W5b 依赖 W1–W3，W6 收官。
- 与 ykit11 DELIVERY §6.3 "绕开 fanPerimeter 表达"路线的对比结论：**绕不开**——lunar 支的
  RHO_NODE1_MONO_WITH_AZIM、circular 支的 KCHMAMG azim_cycle 结论本身就是 rho_node1 轨道
  词表对象；但 ITER 恒等式组（LOFA_IMP_ITER_RHO_NODE_ID2 一族）确可由真证 kit 短推导，
  ykit11 对"轨道 kit 重"的担忧可下调一档。

## 立项时机建议
1. 立即：W1（LA7，纯几何，快赢）；W5a（LA2/LA9 SOL kit）；W3a（LA6 近机械六件）。
2. 次波：W2（桥）、W3b（CIZMRRH）。
3. W4/W5b 在 W1–W3 落地后开；W6 收官（KCHMAMG 可与 W4 并行）。
4. 编排者注意：WSEWPCH 若在 LA7 原位施工（DISCHARGES 契约），LA7 无在飞车主；若在 TameLp
   本地重装三分支，则 :848 闭合波需与 ykit 车道遗产（§9m 块）同一文件串行。

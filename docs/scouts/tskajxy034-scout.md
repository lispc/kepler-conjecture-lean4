# TSKAJXY_034 测绘（2026-10-24，Lane AH 交付）

> 快照：`lane_snapshots/tskajxy-scout/`。**结论：零误植、零真数学缺口，建议立即立项。**
> 旧账 ~600 步 GIANT 实为 ~1,700–3,000 行（中位 ~2,300）4 波；PA20 gammaX 双子免移植两大段、
> MXI_EXPLICIT 现成；唯一解析新债 = TSKAJXY_DERIVED4（merge_ineq.hl:1674，银行条目已 DivSqrtdelta 形态）。
> e2e 连带 = 直源净 −1（PA21 唯一行）；W1/W2 可并行，W3→W4 严格链。

---

# TSKAJXY_034（0/3/4 胞巨案）侦察报告（SCOUT）

> 车道：PA21 `TSKAJXY_034`（PA21:4166，`tsk_hyp_new → TSKAJXY_statement_special_case`）
> 只读侦察（完全只读，零构建、零 repo 写、零 git 写）。基线：工作树 @ `d3e411dd`
> （SF-49 落账后，PA21 全文件仅剩这 1 枚 sorry）。交付：本文件、`DEP_MAP.tsv`、
> `WAVES.md`、`MD5SUMS`。
> 方法：TSKAJXY2.hl 全文件（731 行）逐段读 + TSKAJXY_034 证明体（:92-722）按
> NEW_GOAL 分段建档；merge_ineq.hl 的 tsk 链（:1160-1753）逐段读；PA21 现文件
> （9,216 行）声明图实测；全部关键件 grep/sed 行号核对。

## 0. 结论速览

1. **总判：旧账 "~600 步 refinement GIANT" 名义成立、性质已变——现在的 034 是
   "一个纯装配几何外壳 + 一条已知形态的解析链"。** 四分类：(a) Lean 已证 24 件
   （含全部重机械件：PA20 `gammaX_gamm4fgcy`/`gammaX_gamma3f` 双子、PA12
   `MXI_EXPLICIT`、PA11 `LEPJBDJ/_0` 等）；(b) 机械移植 14 件； (c) 桥/假设叶
   4 件；(d) **真数学缺口 0 件**。总估 **~1,700–3,000 Lean 行（中位 ~2,300），
   4 波**。全文件仅剩 034 一枚 sorry（PA21:4168，grep 实测；旧账 35 枚中其余
   34 枚已由 wedge GIANT / LA38 桥 / merge-ineq 波 0-2c / euler 任务 4 全部闭合）。
2. **前提误植检查（CFFONNL 型专查）：零误植。** `TSKAJXY_statement_special_case`
   （PA21:4159-4162）与 HOL TSKAJXY2.hl:80-88 五前提 + 结论逐字对齐（含前提
   顺序）；`tsk_hyp_new`（:1003）与 HOL :77-78 右结合一致；`cell3_from_ineq`/
   `GRKIBMP_concl`（:993/:999）与 HOL :61-75 逐字对齐；`tsk_bank`（:393）10 条
   与 merge_ineq.hl:1370-1377 的字符串序一一对应。机器可判：这不是假陈述。
3. **最大事实修正：034 的三大前提件已经全部"有人喂"。** GRKIBMP（wave 1，
   PA21:1050 已证）、`cell3_from_ineq_thm`（wave 2b，:4094 已证；其 track-7
   解析核 `mi_gamma3f_gamma3f_x_div_sqrtdelta` 由 euler 任务 4 于 28bc7bb9 收口）、
   `tsk_bank`（假设叶，capstone :9212 以 `proj_tsk_bank hnl` 喂入）。**Lean 侧
   剩余工作 = HOL 证明体 TSKAJXY2.hl:92-722 本身的装配 + 4 胞解析核
   `TSKAJXY_DERIVED4`（merge_ineq.hl:1674，树内无 Lean 对位）的一次性移植。**
4. **4 胞几何外壳的最大利好：PA20 双子已把最难的两块整段吃掉。**
   `gammaX_gamm4fgcy`（PA20:1613，2026-10-08）恰好就是 HOL :170 处的
   `vol/gammaX` 重写件（含 VX={u0..u3} 推导、i≥4 归一）；`gammaX_gamma3f`
   （PA20:2339，2026-10-12）恰好就是 3 胞臂的解析归约件（陈述与
   TSKAJXY1.hl:4178 逐字同型、连 eta/hl 前提都不要）。3 胞臂退化成
   "MXI_EXPLICIT + voronoi 三连 + 界套用"的纯组装（~280–480 行）。
5. **唯一的解析新债：`tsk_derived4`**（= HOL tsk_lemma1 :1383-1660 +
   gamma4fgcy_div_sqrtdelta :1160-1234 + sym 五件 + WLOG + 区间 case-bash，
   合计 ~550-600 HOL 行）。这是与刚落地的 euler 任务 4（+1037 行，同型
   gamma3f 链）完全同Genre 的工作，mi_p21e_* 桥件与 10 条 x-space 银行条目
   （`bank_TSKAJXYGXSA/dx4/eulerA/...`）全部已立——是"已知怎么走"的体力活，
   不是开放数学。估 900–1,800 行（W3+W4）。
6. **消费面**：e2e 直源恰 1 枚（map:95 `Kepler.Text.TSKAJXY_034`，parent=
   TSKAJXY）。闭合后 PA21 文件级 sorry 归零、capstone `TSKAJXY`（:9189，已
   装配真）补上最后一角；净 −1 直源。注意 `Kepler.Text.TSKAJXY_statement`
   （PA2:5560）**不**被解除（银行前提仍在），PA18:1141/PA19 的消费是假设叶
   喂入，零扰动。
7. **公理面口径（预登记）**：闭合后 PA21 文件级零 sorry，但 capstone 链仍带
   上游 sorryAx（PA10 `MEASURABLE_MCELL`←rogers 私件 sorry；PA5/PA6 omega 塔
   基座经 PA20 双子；`MCELL2_SOL` 楔形债）——"局部清零 ≠ 公理净"，按
   merge-ineq 章程 §4.3 口径写闸门报告。
8. **建议立项时机：现在即可立项**（无 STATEMENT-FIX 闸、无环、无外部锚）。
   波次依赖 W1→W2 弱、W3→W4 强；W1/W2（机械，~900–1,400 行）可立即开工且
   低风险；W3/W4（解析核）是全计划唯一工期风险，euler-4 先例给出直接模板。
   诚实天花板见 §6。

## 1. 陈述精确化（含误植逐前提对照）

**Lean**（PA21:4159-4168）：

```
def TSKAJXY_statement_special_case : Prop :=
  ∀ (V X : Set V3), saturated V → Packing V → mcellSet V X →
    ¬(∃ i ul, barV V 3 ul ∧ (i = 1 ∨ i = 2) ∧ X = mcell i V ul) →
    criticalEdgeX V X = ∅ → gammaX V X lmfun ≥ 0

theorem TSKAJXY_034 : tsk_hyp_new → TSKAJXY_statement_special_case
```

**HOL**（TSKAJXY2.hl:80-91）：`!V X. saturated /\ packing /\ mcell_set /\
~(?i ul. ul IN barV V 3 /\ (i=1 \/ i=2) /\ X = mcell i V ul) /\
critical_edgeX V X = {} ==> gammaX V X lmfun >= &0`，外层
`mk_imp(tsk_hyp_new, …)`。**逐前提对照：saturated ✓ / packing ✓ / mcell_set ✓ /
1-2 胞排除 ✓ / critical_edgeX=∅ ✓ / 结论 ✓；前提顺序一致，零误植、零弱化。**

`tsk_hyp_new`（PA21:1003）= `GRKIBMP_concl ∧ cell3_from_ineq ∧ tsk_hyp`，
与 HOL mk_conj 嵌套一致。数学内容：饱和 packing 中，非 1/2 胞且无临界边的
mcell X 的 gammaX ≥ 0（0/3/4 胞情形；1/2 胞由 TSKAJXY_1/_2 管，capstone
by_cases 分派，:9193-9213 已装配真）。

## 2. 旧侦察对账与现状核实

- 旧侦察（docs/scouts/tskajxy12-scout.md，2026-09-29，基线 PA21=2,557 行）
  只把 034 记为"0/3/4 臂 2 枚界外 sorry"之一，未建 034 档。其两臂内容
  （TSKAJXY_1/_2）现已全证（现 :5826/:9138），本侦察不重复。
- **"~600 步"的现行口径**：HOL 证明体 TSKAJXY2.hl:92-722 = 630 行 refinement，
  外加它消费的解析链 merge_ineq.hl:1160-1753（~590 行）。"600 步"指的是前者，
  后者是旧口径漏计的部分——但后者的大头（GRKIBMP、cell3_from_ineq_thm、
  euler 任务 4）已被 merge-ineq 波次顺手清掉，**剩余解析债只有 4 胞
  TSKAJXY_DERIVED4 一条**。
- 本会话/近期入仓 kit 对 034 的可复用件（grep 实测，全部 PROVED，行号现文件）：
  PA20 `gammaX_gamm4fgcy`:1613 / `gammaX_gamma3f`:2339（2026-10-12 落账）；
  PA12 `MXI_EXPLICIT`:1971（2026-10-20 十发波换接，公理三零）/
  `VORONOI_LIST_3_SINGLETON_EXPLICIT`:1695 / `HL_DECREASE`:1671（PA7）/
  `HL_EQ_DIST0`:1637（PA7）/ `BARV_IMP_HL_1_POS_LT`:757；
  PA11 `LEPJBDJ`:858 / `LEPJBDJ_0`:886；PA4 `HDTFNFZ_ALT`:1240；
  PA6 `OAPVION2`:2089；PA5 `CONVEX_VORONOI_LIST`:2371 / `BARV_SUBSET`:1469；
  PA8 `BARV_3_EXPLICIT`:210 / `TRUNCATE_SIMPLEX_EXPLICIT_2/3`:91/98；
  PA7 `XNHPWAB1`:1772；PA10 `MEASURABLE_MCELL`:1217（†sorryAx，可用）；
  Geom/SimplexVolume.lean:584 `volume_real_convexHull_tetra`；
  PA21 本文件 `mi_*` kit（:1638-4162，sqrt/mm1/hminus/eta 桥/WLOG-3d/数值种子
  全套，公理净）+ 10 条 tsk_bank 条目 def + `proj_bank_*` 具名投影 59 枚
  （ed9b939a）+ PA25 `GDRQXLGv3`:1347（radV²↔rad2X 桥，**public 但不可
  import——PA25 imports PA21 成环**，照抄证明 ~60-120 行）。

## 3. 依赖链全图（HOL 证明体 :92-722 分段）

```
TSKAJXY_034（HOL :92-722）
├─ A. NULLSET 分支 :100-117        gammaX 展开 + 零测三分（机械）
├─ B. i≥4（4 胞）:118-484（~366 行）
│   ├─ B1 X=mcell4、VX={u0..u3}     MCELL_EXPLICIT+HDTFNFZ+LEPJBDJ（PA20 同型已证）
│   ├─ B2 gammaX_gamm4fgcy 套用     ← PA20:1613 现成
│   ├─ B3 TSKAJXY_DERIVED4 套用     ← merge_ineq.hl:1674（**唯一解析新债**）
│   ├─ B4 ¬critical_edge_y ×6       ← criticalEdgeX 展开 + HL_2 + hminus_prop
│   ├─ B5 0<delta_y ⟺ vol>0        ← volume_real_convexHull_tetra + B2 体积半
│   ├─ B6 边长∈[2,√8] ×6           ← packing + 外心三角不等式（OAPVION2+HL）
│   ├─ B7 CARD=4/distinct/edgeX 六对 ← 集合 case-bash
│   └─ B8 rad2_y=radV²(GDRQXLGv2) + ¬coplanar + hl<√2 ← PA25 GDRQXLGv3 同型
├─ C. i=0（0 胞）:485-500           LEPJBDJ_0 + MEASURABLE_MCELL（机械）
└─ D. i=3（3 胞）:502-721（~220 行）
    ├─ D1 i=3 归一 + mcell3 分支    mcell if_pos（PA20 gammaX_gamma3f 内同型）
    ├─ D2 MXI/thales               ← PA12 MXI_EXPLICIT:1971 现成
    ├─ D3 s∈voronoiList(trunc2) → dist(s,u1)=dist(s,u2)=√2
    │                               ← OMEGA_LIST_N_IN_VORONOI_LIST + CONVEX_VORONOI_LIST
    ├─ D4 gammaX_gamma3f 套用       ← PA20:2339 现成
    └─ D5 cell3_from_ineq 套用 + eta 桥
                                    ← eta_y = 面外接半径 = hl[trunc2 ul]（见 §4）
解析链（merge_ineq.hl，W3/W4 对象）
    tsk = tsk_hyp → TSKAJXY_DERIVED.ineq :1379
    ├─ TSKAJXY_DERIVED4 :1674-1753   WLOG(REAL_WLOG_SIMPLEX) + sym 五件 + CRIT_TAC 区间
    └─ tsk_lemma1 :1383-1660         gamma4fgcy_div_sqrtdelta(:1160) + ups_x_pos24(:651)
                                     + delta_x4/eulerA 银行条目代数
```

## 4. 逐条四分类要点（全表见 DEP_MAP.tsv，30 行）

- **(a) 已证 24 件**：§2 清单全部 + 陈述三件 + capstone。要点：PA20 双子把
  B1/B2/D4 三块整段免移植；D2 的 MXI_EXPLICIT 是 2026-10-20 刚换接的公理三零件；
  `cell3_from_ineq_thm` 在 euler 任务 4（28bc7bb9）后已无继承债。
- **(b) 机械移植 14 件（~1,050–1,900 行）**：A、B4-B8、C、D1、D3、D5、
  sym 五件、WLOG 方案、gamma4fgcy_div_sqrtdelta、tsk_lemma1、DERIVED4 本体、
  终装配。全部有同型先例：六连临界边块 ↔ 旧 BIS/RCONE case-bash 习语；
  tsk_lemma1 ↔ euler 任务 4（+1037 行）；WLOG ↔ mi_REAL_WLOG_SIMPLEX_3d
  （PA21:3211，3d 版 30 行）的 4-顶点推广。
- **(c) 桥/假设叶 4 件（~130–260 行）**：
  ① `p21_hl2 : hl [u,v] = dist u v / 2`（PA13:1274 private，重抄 ~8 行）；
  ② radV²↔rad2X 四点桥（PA25 GDRQXLGv3 同型，环禁 import，重装 60–120）；
  ③ 平面零测小件（p20k_plane_null 同型 private，重抄 20–40）；
  ④ **eta 桥（W2 的钥匙，本侦察新证形状）**：IneqClosureDefs.etaX:606 =
  √(x1x2x3/upsX)，而 upsX = 16·面积²，故 **etaX² = 面外接圆半径²**，即
  `eta_y y4 y5 y6 = hl [u0,u1,u2]`（RADV_FORMULAR/OAPVION2 一推即得，
  20–50 行）。HOL :711-721 的 ENOUGH_TO_SHOW 块就是这个恒等式。
  tsk_bank 十条是假设叶（证书债，不在本 lane 范围）。
- **(d) 真缺口：0。** 解析核的每一步在 HOL 里都是银行条目的代数重排
  （REAL_ARITH/ineq_expand6 级），数值种子（mm1 围闭、hminus 围闭、
  arccos(1/3) 双界）已全部在库。

## 5. 消费面与 e2e 连带

- **e2e**：docs/e2e-reachability-map.tsv:95 是 PA21 唯一一行 =
  `TSKAJXY_034`（parent=TSKAJXY）。闭合 → 直源 −1；PA21 文件级 sorry 归零
  （8710 jobs 全绿口径不变）；capstone `TSKAJXY`（PA21:9189，真装配）补齐。
- **TSKAJXY_statement（PA2:5560）不解除**：capstone 带银行前提
  `pack_nonlinear_non_ox3q1h`，与 PA2 concl 接口不逐字匹配（PA21 头注
  DISCHARGES 段明示）；PA18:1141/PA19:561/591/755/916/1069 均假设叶消费，
  034 翻身对它们零扰动。
- **Assembly.lean:6341** 记"TSKAJXY 臂余债 = TSKAJXY_034"——本 lane 闭合即
  该行销账。Assembly 的 nliTskBank/nliPackNonlinearRest 槽位是独立证书债
  （bank 叶），与本 lane 无关。
- ** axiom 面预登记**：见 §0.7。

## 6. 波次骨架与诚实天花板（详见 WAVES.md）

- **W1 几何机械层（0/4 胞外壳 + 四个私有重抄桥）**：~600–950 行，风险低-中。
- **W2 3 胞臂（MXI + voronoi + 双套用 + eta 桥）**：~280–480 行，风险中。
- **W3 解析核前半（sym 五件 + WLOG-4d + gamma4fgcy_div_sqrtdelta + 骨架）**：
  ~400–800 行，风险中-高。
- **W4 tsk_lemma1 + DERIVED4 + 034 终装配翻 sorry**：~400–800 行，风险高
  （全计划唯一硬点；缓解：checkpoint 中转陈述，euler-4 模板）。
- **合计 ~1,700–3,000 行（中位 ~2,300），4 波，期望 4–8 个工作日（单工人）。**
  诚实天花板：W1+W2（机械）~900–1,400 行可承诺，成功率 ~85%；W3+W4 解析
  ~800–1,600 行，成功率 ~70–75%（体量大但形态已知；若 W4 卡壳，W1-W3 的
  私件仍是下一波净遗产）。
- **替代路线核查**：① 无更强已证定理可直接吃掉 special_case（TSKAJXY_statement
  本身开放且带银行前提；树内无 0/3/4 胞 gammaX 下界的其他来源）；② 陈述冻结、
  单一 sorry、无部分信用，"先弱化后补"无意义；③ 无前提误植，无需 STATEMENT-FIX。

## 7. 给编排者的笔记

1. `TSKAJXY_DERIVED4` 在 lean/scripts/ 内**零定义**（仅 TSKAJXY2.hl:165 一处
   消费），本体在 reference/flyspeck/.../nonlinear/merge_ineq.hl:1674——别按
   文件名去 packing/ 里找。
2. `tsk_bank` 十条的 x-space 盒式陈述（PA21:267-365）已经和 tsk_lemma1 消费
   形态（DivSqrtdelta 展开）对齐——bank_TSKAJXYGXSA 就是 sqrt-delta 形态，
   W4 不需要再换算。
3. PA25 的 `GDRQXLGv3`(:1347)/`p25_radv_etay_core`(:999) 是 W1/W2 两个桥的
   现成模板，但**不可 import**（环）；照抄证明到 PA21 私件区是唯一路。
4. `p13_hl_pair`（PA13:1274，hl 对长 = dist/2）private 不可见；PA21 私件区
   重抄（radV 对定义 + norm 级）。
5. PA10 `MEASURABLE_MCELL`(:1217) 带 rogers sorry 尾巴（PA10:402 私件），
   0 胞分支消费它时会染 sorryAx——公理面口径预登记，不阻塞。
6. 旧头注 drift：PA21:94-98 "REMAINING sorry (2 sites)" 已过时——
   `mi_gamma3f_gamma3f_x_div_sqrtdelta` 已由 28bc7bb9 闭合，现仅剩
   TSKAJXY_034:4168 一处。

---

# TSKAJXY_034 波次计划（WAVES）

> 前置：全部在 PA21 单文件内施工（私件 + 原位翻 sorry）；无 import 增量、
> 无环、无 STATEMENT-FIX 闸。每波收工跑闸门同款 `lake build Kepler.Text.PackingAuto21`。
> 波间依赖：W1 与 W2 弱耦合可并行/换序；W3 → W4 严格链；W4 末枚翻 :4168。

## W1「几何机械层：0/4 胞外壳 + 四个私有桥」（~600–950 行，风险低-中）

先立四个私件（~130–260 行）：
- `p21_hl2 : hl [u,v] = dist u v / 2`（照 PA13:1274 抄，~8）；
- 四点 radV²↔rad2X 桥（照 PA25 GDRQXLGv3:1347 证明重装，~60–120；环禁 import）；
- 平面零测小件（p20k_plane_null 同型，~20–40）；
- barV 四点两两 distinct（p20k_barV_distinct 同型，~15）。

本体（~470–690 行）：
- A. NULLSET 分支（30–60）；
- B1/B2. mcell4 归一 + gammaX_gamm4fgcy 套用（50–100）；
- B4. ¬criticalEdgeY ×6（120–200，六连同型，先做一个再复制五个）；
- B5. delta_y>0 ⟺ vol>0（30–60）；
- B6. 边长 [2,√8]（60–110）；
- B7. CARD/distinct/edgeX 六对（70–150）；
- B8. rad2 桥套用 + ¬coplanar + hl<√2（60–110）；
- C. 0 胞分支（40–80）。

验收：上述件全部 `private theorem` 落地、零 sorry、公理面除 †MEASURABLE_MCELL
消费点外标准三。风险：B4/B7 的 case-bash 体量（机械但长）；B6 的外心三角
不等式方向。无解析依赖，可独立编译验证。

## W2「3 胞臂」（~280–480 行，风险中）

- eta 桥 `eta_y y4 y5 y6 = hl [u0,u1,u2]`（给定三边长；etaX²=面外接半径²，
  IneqClosureDefs:606 + OAPVION2，~20–50；**W2 钥匙，先做**）；
- D1. i=3 归一 + mcell3 分支条件抽取（20–40）；
- D2. MXI_EXPLICIT 套用（10–20）；
- D3. s∈voronoiList(trunc 2 ul) → dist(s,u1)=dist(s,u2)=√2（80–150；
  voronoiList 凸性 + voronoiClosed 展开；PA12:2951 一带有用同件的习语可抄）；
- D4. gammaX_gamma3f（PA20:2339）套用（10–30）；
- D5. cell3_from_ineq 套用：2≤y_i（packing）、y_i≤2√2（DIST_TRIANGLE 经 s）、
  eta<√2（eta 桥 + mcell3 分支条件 hl trunc2<√2）（40–90）；
- 3 胞 ¬coplanar{u0,u1,u2,s} + CARD=4（60–100）。

验收：W1+W2 合并后除 :4168 外 PA21 零 sorry 不变；3 胞分支可整段组装成
一个私有 `tskajxy_034_cell3` 备用。风险：D3 的 voronoi 隶属链（中）；
PA20 双子的前提适配（低）。

## W3「解析核前半：sym + WLOG + div_sqrtdelta + 骨架」（~400–800 行，风险中-高）

- sym 五件：gamma4fgcy 对 (12)(23)(03) 顶点对换 + rad2_y/delta_y 对换
  （60–150；simp[gamma4fgcy,volY,vol4f,solY,dihY]+ring 级）；
- WLOG-4d 方案（mi_REAL_WLOG_SIMPLEX_3d PA21:3211 的 4-顶点推广，60–120）；
- `gamma4fgcy_div_sqrtdelta` 恒等（150–300；对照 PA21:2971 已证同型展开法）；
- tsk_derived4 陈述冻结 + 骨架（WLOG 归约到 tsk_lemma1 的受限盒
  [2.8,√8]×[2,2.01]²×[2.8,√8]×[2,2.01]²，checkpoint 中转陈述先行落位）。

验收：checkpoint 陈述立起、sym/WLOG/div_sqrtdelta 全证。风险：div_sqrtdelta
的 sqrt 代数膨胀（euler-4 先例可抄路径）；陈述冻结需与 HOL :1674 逐字对表
（本 lane 已核：目标形态 = 盒界+¬crit+delta+rad2 → gamma4fgcy≥0）。

## W4「tsk_lemma1 + DERIVED4 + 终装配翻 sorry」（~400–800 行，风险高）

- tsk_lemma1：盒内把 gamma4fgcy≥0 归到 bank_TSKAJXYGXSA（已是 DivSqrtdelta
  形态!）+ dx4/eulerA 正性条目（400–700；mi_p21e_* 桥件 + ups_x_pos24 型
  正性记账；euler 任务 4 为模板）；
- CRIT_TAC 区间 case-bash（100–250；断点 2.0/2.001/2.01/2.8，mi_201_* 数值
  件已备）；
- 034 终装配：by_cases i≥4 / i=0 / i=3 三分，接 W1-W3 私件，翻 :4168
  （60–120）。

验收：`lake build Kepler.Text.PackingAuto21` 自然退出 0 error；`#print axioms
TSKAJXY_034` 无新增本地 sorryAx（上游 taint 预登记）；e2e map:95 直源销账。

## 汇总与天花板

| 波 | 估行数 | 风险 | 成功率（主观） |
|---|---|---|---|
| W1 | 600–950 | 低-中 | ~90% |
| W2 | 280–480 | 中 | ~85% |
| W3 | 400–800 | 中-高 | ~75% |
| W4 | 400–800 | 高 | ~70% |
| 合计 | **1,700–3,000（中位 ~2,300）** | — | 全程 ~70–75% |

诚实天花板：W1+W2 机械部分（~900–1,400 行）可承诺；W3+W4 是体量风险不是
数学风险——每一步在 HOL 里都是收口了的，Lean 侧只有代数膨胀和 case-bash
体力。若 W4 卡壳：checkpoint 陈述（W3 末）+ 已落私件是下一波净遗产，且
PA21 除 :4168 外保持零 sorry（不回退）。

建议立项时机：**立即**。W1/W2 任何时段可开工；W3/W4 建议整波连续排期
（解析链上下文重入成本高）；与其他 PA21 施工零冲突（当前无其他 PA21 lane）。

---

```
HOL引理	行号	分类	Lean对应	估行数	备注
TSKAJXY_statement_special_case	TSKAJXY2.hl:80-88	a-已立(陈述)	PA21:4159-4162	0	五前提+结论逐字对齐HOL，零误植（CFFONNL型专查通过）
tsk_hyp_new	TSKAJXY2.hl:77-78	a-已立(陈述)	PA21:1003	0	=GRKIBMP_concl∧cell3_from_ineq∧tsk_bank，右结合一致
cell3_from_ineq(前提件)	TSKAJXY2.hl:61-70	a-已证	PA21:993(def)/:4094(cell3_from_ineq_thm)	0	wave2b闭合；track7由euler任务4(28bc7bb9)收口
GRKIBMP_concl(前提件)	TSKAJXY2.hl:73-75	a-已证	PA21:999(def)/:1050(GRKIBMP)	0	wave1闭合，公理净
tsk_hyp=tsk_bank(前提件)	merge_ineq.hl:1370-1377	c-假设叶	PA21:967/:393-399(10条def:267-365)	0	capstone:9212以proj_tsk_bank喂入；证书债不在本lane
A. NULLSET分支	TSKAJXY2.hl:100-117	b-机械	—	30-60	gammaX展开+零测三分；setSum空/零测习语
B1. X=mcell4+VX={u0..u3}	TSKAJXY2.hl:118-153	a-同型已证+胶水	PA20 gammaX_gamm4fgcy:1613内含；p20k_mcell_ge4同型	40-80	i≥4归一；HDTFNFZ_ALT(PA4:1240)+LEPJBDJ(PA11:858)
B2. gammaX_gamm4fgcy套用	TSKAJXY2.hl:155-168	a-已证	PA20:1613	10-20	陈述含i≥4/¬nullSet/六dist，逐字适配
B3. TSKAJXY_DERIVED4消费位	TSKAJXY2.hl:160-168	b-机械	→W3/W4新件tsk_derived4	(计入29)	ineq[2,y_i,√8]×6+¬crit×6+0<delta+rad2<2
B4. ¬critical_edge_y×6	TSKAJXY2.hl:169-266	b-机械	新件×6；mi_hminus_prop(PA21:1887)+p21_hl2副本(c-①)	120-200	六连同型case-bash；criticalEdgeX展开(PA2:478)
B5. 0<delta_y⟺vol>0	TSKAJXY2.hl:267-287	b-机械	volume_real_convexHull_tetra(Geom/SimplexVolume.lean:584)+B2体积半	30-60	volY=√deltaY/12(SphereKit:124/PA20:104)
B6. 边长∈[2,√8]×6	TSKAJXY2.hl:288-345	b-机械	新件；Packing+BARV_SUBSET(PA5:1469)+OAPVION2(PA6:2089)+HL(PA2:276)	60-110	外心三角不等式；radV=hl
B7. CARD=4/distinct/edgeX六对	TSKAJXY2.hl:346-407	b-机械	新件；p20k_barV_distinct同型(private重抄~15)	70-150	集合枚举case-bash
B8a. rad2_y=radV²	TSKAJXY2.hl:426-454+merge_ineq.hl:1327-1364	c-桥(重装)	PA25 GDRQXLGv3:1347同型已证但环禁import	60-120	照PA25证明重装(OAPVION2+Cramer代数)
B8b. ¬coplanar{u0..u3}	TSKAJXY2.hl:427-450	b-机械	p20k_plane_null同型(private重抄20-40)	30-60	coplanar→affine hull→nullSet反证
B8c. hl ul<√2→rad2<2	TSKAJXY2.hl:451-470	b-机械	HL_DECREASE(PA7:1671)+BARV_IMP_HL_1_POS_LT(PA12:757)+sqrt单调	30-50	mcell4分支条件直接给出hl<√2
C. 0胞分支	TSKAJXY2.hl:485-500	b-机械	LEPJBDJ_0(PA11:886)+MEASURABLE_MCELL(PA10:1217†sorryAx)	40-80	edgeX=∅+SUM空+MEASURE_POS_LE
D1. i=3归一+mcell3分支	TSKAJXY2.hl:502-527	b-机械	mcell def(PA2:359) if_pos模式(PA20:2339内同型)	20-40	mcell3非空⟺分支条件(PA20 hexp/hcq习语)
D2. MXI/thales存在性	TSKAJXY2.hl:528-545	a-已证	PA12 MXI_EXPLICIT:1971(公理三零,2026-10-20换接)	10-20	∃s, s∈segment(ω2,ω3)∧dist u0 s=√2∧s=mxi
D3. s∈voronoi→dist(s,u1)=dist(s,u2)=√2	TSKAJXY2.hl:546-600	b-机械	OMEGA_LIST_N_IN_VORONOI_LIST+CONVEX_VORONOI_LIST(PA5:2371)+voronoiClosed(PA2:196)	80-150	conv{ω2,ω3}⊆voronoiList(凸)=∩voronoi_closed
D4. gammaX_gamma3f套用	TSKAJXY1.hl:4178-4238	a-已证	PA20:2339(陈述逐字同型,连eta/hl前提都不要)	10-30	直接套用
D5. cell3_from_ineq套用+eta桥	TSKAJXY2.hl:692-721	b-机械	新件eta桥:eta_y=hl[u0,u1,u2](etaX²=面外接半径²,IneqClosureDefs:606/628+OAPVION2)	40-90	侦察新证恒等形状；HOL:711-721即此桥
tsk(4胞解析目标)	merge_ineq.hl:1379	b-机械	→新件tsk_derived4陈述	Ineq.TSKAJXY_DERIVED.ineq展开	盒界+¬crit+delta+rad2→gamma4fgcy≥0
tsk_lemma1	merge_ineq.hl:1383-1660	b-机械(大)	新件；bank_GXSA/dx4/eulerA已立(PA21:267/:286/:294)	400-700	euler任务4(+1037行)为直接同型先例；mi_p21e_*桥件全套在库
gamma4fgcy_div_sqrtdelta	merge_ineq.hl:1160-1234	b-机械	新件；对照mi_gamma3f_gamma3f_x_div_sqrtdelta(PA21:2971)已证同型	150-300	sqrt-delta代数恒等
gamma4fgcy_sym12/23/03+rad2_y_sym+delta_y_sym	merge_ineq.hl:1235-1326/:1569-1620s	b-机械	新件；y空间重排恒等	60-150	simp[gamma4fgcy,volY,vol4f,solY,dihY]+ring级
REAL_WLOG_SIMPLEX方案	(Nonlinear_lemma,树外)	b-机械	新件；mi_REAL_WLOG_SIMPLEX_3d(PA21:3211)为3d先例(30行)	60-120	S4顶点重排WLOG，sym三件生成元内联
TSKAJXY_DERIVED4本体	merge_ineq.hl:1674-1753	b-机械	新件	100-250	CRIT_TAC区间case-bash(2.0/2.001/2.01/2.8断点)；10条银行条目套用
capstone TSKAJXY(消费面)	TSKAJXY3.hl:2251	a-已装配	PA21:9189-9213	0	034翻身即补齐最后一角
基础设施束(全部a)	见SCOUT.md §2	a-已证	HDTFNFZ_ALT PA4:1240/LEPJBDJ,_0 PA11:858,886/BARV_3_EXPLICIT PA8:210/TRUNCATE_SIMPLEX_EXPLICIT_2,3 PA8:91,98/BARV_SUBSET PA5:1469/HL_DECREASE PA7:1671/HL_EQ_DIST0 PA7:1637/BARV_IMP_HL_1_POS_LT PA12:757/OAPVION2 PA6:2089/XNHPWAB1 PA7:1772/VORONOI_LIST_3_SINGLETON_EXPLICIT PA12:1695/CONVEX_VORONOI_LIST PA5:2371/MEASURABLE_MCELL PA10:1217†/volume_real_convexHull_tetra SimplexVolume:584/criticalEdgeX,Y PA2:478,496/gammaX PA2:453/mcell PA2:347-366/etaY,rad2X IneqClosureDefs:620,628/deltaY SphereKit:124/mi_hminus_prop PA21:1887/mi_sqrt8_eq PA21:1647	0	全部public且在PA21 import闭包内(†=sorryAx尾巴,可用)
私有重抄束(c-①③等)	PA13:1274/PA20(p20k_*)	c-桥	p21_hl2(~8)+barV_distinct(~15)+plane_null(20-40)	43-63	private不可见，PA21私件区重抄
d-真数学缺口	—	d-无	—	0	解析核全是银行条目代数重排，无开放数学
```

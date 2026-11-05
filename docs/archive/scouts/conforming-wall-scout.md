# wdart/conforming 真墙测绘（2026-10-24，Lane Y 交付）

> 快照：`lane_snapshots/conforming-scout/`。**重大修正**：V 线"wdart/conforming 章全树未移植"不成立——
> ConformingAuto1–23 + ConformingDefs = 25,357 行已全证（文件头 bare sorry 注记全部过时）。真缺仅一件：
> `AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN`（CFYXFTY.hl:982，41 行 HOL，8 原料全已证）。
> 三枚 tau 直源总解锁 ~570–800 行 / 3 波 / 零数学缺口；连带部分解锁 perimeter_bound。建议立项（已批）。

---

# Lane Y 侦察报告 — wdart/conforming 章真墙测绘（tau4/5/6 解锁成本）2026-10-23

## 0. 结论速览

**V 线的"唯一真墙 = wdart/conforming 章，全树未移植"定性有重大修正：该章在 Lean 侧
已经移植且全部填证完毕（ConformingAuto1–23 + ConformingDefs 共 25,357 行、零实
sorry），V 所列三锚中两枚已证，唯一真缺 = 第三锚
`Cfyxfty.AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN`（CFYXFTY.hl:982，~41 行
HOL）+ 局化簿记（V 绕行件）。**

| 项 | 数 |
|---|---|
| 三枚 tau（ineq_tau4/5/6_tauVEF_std）总解锁成本 | **~570–800 Lean 行（中位 ~680），3 波** |
| 其中新移植（墙件 W1） | ~150–220 行，纯机械，全部原料在库 |
| 其中局化簿记（W2，V §0.3 绕行件 + LocalFan/Dih2k 构造） | ~300–420 行，无新数学 |
| 其中装配（W3，三枚各 ~35–45 行） | ~120–160 行 |
| 真数学缺口 | **0**（HOL 证明完整存在且 Lean 侧同构链已两处落地） |
| 最大风险 | W2 的 LocalFan/Dih2k 受限超图构造（Hypermap 载体 + HasOrders 五合取簿记）；渲染追逐摩擦（wedgeGe 三胞胎 / EE vs setOfEdge / univ vs V / DecidableEq 实例搬运） |
| 建议立项 | **是**——3 波、零数学风险、回报 3 枚 e2e 直源（TameLp 剩余 4 sorry 中的 3 枚），且 perimeter（第 4 枚）三桥之一同波消失 |

### 0.1 三锚引理 Lean 存量（逐枚验证过证明体，非只看文件头）

| HOL 锚 | 位置 | Lean 状态 |
|---|---|---|
| `fully_surrounded_imp_conforming` | add_triangle-compiled.hl:652 | **(a) 已证**：`ConformingAuto21.PIIJBJK`（:903，证明体真实：极小反例 + by_cases）+ TameLp 私件 `p6g_fullySurrounded_conforming`（:1236，FullySurrounded 直接输入）与 `contraveningConformingTl`（:2151，Contravening→ESTD 版）。其上游 TXFBALB 加边机器全链已证：`TXFBALB`=ConformingAuto19:2031（187 行证明）、`TXFBALB_VERSION`=Auto20:143、`GGZWYRM`=Auto20:703、`conforming_bijection_fanadd_verrion`=Auto20:194、`HYUAZSE`=Auto21 |
| `Conforming.DARTSET_LEADS_INTO_SUBSET_WDART_FAN` | Conforming.hl:268 | **(a) 已证**：`ConformingAuto1.DARTSET_LEADS_INTO_SUBSET_WDART_FAN`（:531，863 行文件唯一 "sorry" 是文件头过时注记；grep `^\s*sorry` = 0）。注意它只消费 `conformingFan` 六合取中的 **half-space 一支** |
| `Cfyxfty.AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN` | CFYXFTY.hl:982 | **(b) 未移植**——全树 grep 无同名/同义件（`closure (dartsetLeadsIntoFan …)` 零命中）。这是唯一真墙件。其 8 个上游原料全部已证（见 DEP_MAP），~41 行 HOL → 估 60–100 行 Lean，纯机械 |

### 0.2 波次骨架

```
W1 墙件（锚3 移植 + wedge 闭合胶水 + DecidableEq 实例搬运）~150–220 行
        │   （半成品不进 import 闭包，e2e 恒 4）
        ▼
W2 局化簿记（LocalFan(vPrime,ePrime,f) 构造 + vPrime.ncard=K
        + azim/wedge transfer + local_diag/std 绕行）    ~300–420 行
        ▼
W3 装配（tau4/5/6_std 三枚，JEJTVGB_std_concl 实例化）   ~120–160 行 → e2e 4→1
```

（TameLp 现存 4 枚 proof-position sorry：:847 perimeter、:2112/:2125/:2138 tau4/5/6。）

### 0.3 消费闭包一层结构（f_surr_localization_convex_local 的 wedge 部分）

HOL（RNSYJXM-compiled.hl:327–393）wedge 前提证明 =
`v_prime V f ⊆ wedge_in_fan_ge (a,b) E`（(a,b)∈f，经 ←wedge_eq 换回全边集）：
1. x = pr2(某面 dart) ∈ closure(aff_gt {0} {x,y})（POINT_IN_CLOSURE_AFF_GT_1_2）；
2. aff_gt {0} {x,y} ⊆ closure(dartset_leads_into_fan 0 V E (IMAGE h f))
   （**锚 3** + DARTSET_LEADS_INTO_FAN）；
3. dartset ⊆ w_dart_fan（**锚 2**，conforming_half_space 支）→ closure 单调；
4. w_dart_fan = wedge（开楔，card>1 支）→ closure(wedge) ⊆ wedge_ge（**锚 1**
   的 conforming + CLOSED_WEDGE）；x ∈ wedge_ge。∎

**Lean 侧同构链的两大简化**：
- 编码已全用 pair darts（`hypermapOfFan`），HOL 的 `h = ext_dart` 超图同构步
  （fan_hypermaps_iso_explicit2 + iso_components 三处）**整体消失**；
  TameLp 的 `hypermapOfFanTl` 只是同一超图换 DecidableEq 实例（TameLp:67–73），
  搬运 ~10–20 行（wk_face_mem_faceSet 已有先例）。
- CLOSED_WEDGE 闭合步不需要等式：`wedge ⊆ wedgeGe`（逐点平凡，Geom/Azim.lean:63
  的条件更强）+ `IsClosed (wedgeGe …)`（PackingAuto18:6884/6895 现成）即得
  closure(wedge) ⊆ wedgeGe。
- 渲染桥全部现成：`AzimBridge.sigmaFan_univ_eq`（:461）、
  `AzimBridge.wedgeInFanGe_eq_wedgeInFanGe_p3`（:483）、
  `azimInFan_eq_azimInFan_p3`（:473）、`AZIM_CYCLE_EQ_SIGMA_FAN`（LocalAuto3:771）。

### 0.4 连带解锁面（墙通后除三枚 tau 外）

| 消费点 | 性质 | 备注 |
|---|---|---|
| `fully_surrounded_perimeter_bound`（TameLp:839，e2e 直源） | **部分解锁** | 墙是它三桥之一；仍差 LocalAuto7 三枚 faithful sorry（`BGMIFTE`:642/`FAN_PERIMETER`:691/`WSEWPCH`:698）+ `lemma_face_representation` + `sum_face_rho_node1`。W1 落地后其 NEEDS 注记应改写 |
| HOL `ineq_tau4_pro_tauVEF_aux`(:1134)/`ineq_tau5_pro_tauVEF_aux`(:1029)/`ineq_tau5_pro_tauVEF`(:1069)/`ineq_tau4_diag3_tauVEF`(:1234)/`ineq_tau5_diags_tauVEF`(:1329) | 未来解锁 | lp_main_estimate 中锚件的另外 5 个消费点，Lean 尚无骨架（非现 e2e 源）；W1–W2 落地后成本降为装配级 |
| TameLp `p6g_face_tauVEF`（:1289 已证）与 JEJTVGB 群 | 已在消费 | 墙件不新增它们 |

## 1. 章定位与体量

| HOL 文件 | 行数 | 角色 |
|---|---|---|
| fan/Conforming.hl | 17,033 | conforming 章：六合取 def（:26–48）+ top-level 定理（PIIJBJK :14195、TXFBALB :12056、DARTSET_LEADS_INTO_SUBSET_WDART_FAN :268 等） |
| fan/CFYXFTY.hl | 1,446 | leads-into 集的凸性/闭包/边面（锚 3 所在 :982） |
| formal_lp/hypermap/ssreflect/add_triangle-compiled.hl | 1,489 | FullySurrounded 节：fully_surrounded_imp_conforming（:652）、imp_fan80（:260）、card_set_of_edge1（:226） |
| fan/Planarity.hl（相关段） | ~400（全文件更大） | dartset_leads_into_fan def :10978、DARTSET_LEADS_INTO_FAN :10989、fan80 def :1338、aff_gt_1_3_subset :13744、inter_aff_gt_3_1 :14725、properties_fully_surrounded :1872 |
| fan/fan.hl（相关段） | ~150 | w_dart_fan def :1027、remark1_fan :423、sigma_fan_in_set_of_edge :565、face_subset_dart_fan :2823、dartset_fully_surrounded_is_non_isolated :2847、properties_of_elements_in_face :2857 |
| local/localization.hl | 1,595 | wedge_in_fan_gt/ge def :79/:88、convex_local_fan :92、v_prime/e_prime :97/:100 |
| local/RNSYJXM-compiled.hl | 397 | f_surr_localization :300、f_surr_localization_convex_local :327（Lean 消费面正主） |
| formal_lp/.../lp_main_estimate-compiled.hl | 消费面 | 锚件 9 个使用点：tau4/5/6 忠实链（:752/:845/:944）、pro/diag 五件（:1043/:1083/:1149/:1249/:1348）、perimeter（:1537） |

**Lean 侧对应存量**：ConformingAuto1–23 + ConformingDefs = 25,357 行、零实 sorry
（24 个文件逐个 `grep -cE "^\s*sorry"` 验证；各文件头的 "Every proof is a bare
sorry" 是骨架期过时注记）。支撑件：PlanarityAuto12/13/14、PlanarityComponent、
TopologyFan、AzimBridge（808 行 0 sorry）、Fan.lean、Geom/Azim.lean。
**唯二相关缺口**：LocalAuto10（LVDUCXU 章移植，743 行、17 枚 proof-position
sorry——headline `LVDUCXU`:741 及其局化保持链）；LocalAuto7 周长 lane 三枚
faithful sorry（perimeter 用，不在 tau 关键路径）。

## 2. 四分类总账（关键路径）

- **(a) Lean 已证**：锚 1、锚 2 及其全部上游（TXFBALB 加边机器 ~2,800 HOL 行当量
  已在 Auto19/20/21 落地）；锚 3 的 8 个原料（DEP_MAP 详列）；渲染桥 4 件
  （AzimBridge §4）；Dih2k/轨道引擎（AzimBridge.localFan_data :635 正向 +
  LA10 FACE_CYCLE_CARD :364）。
- **(b) 机械移植**：锚 3 本体（60–100 行）；wedge 闭合胶水（20–40）；实例搬运
  （10–20）；LocalFan(vPrime,ePrime,f) 构造（150–200，簿记量大但逐条有 HOL
  原文与 LA10/AzimBridge 参照）；vPrime.ncard=K（~100）；azim/wedge transfer
  （80–100）；local_diag/std 绕行（~40）；FAN 继承（~40）；三枚装配（3×35–45）。
- **(c) 异陈述现成件需桥**：仅一处实质——CLOSURE_AFF_GT_1_3_EQ_AFF_GE_1_3
  （CFYXFTY:940）无 Lean 同名件，但 PlanarityAuto14:176–183 已示范同型技巧
  （affGe 闭 + closure_mono），15–30 行；wedgeGe 三胞胎（LA1 wedgeGe = canonical、
  LocalAuto2 wedgeGe_p2、Fan.cwedge）用现有 twins 桥纪律处理。
- **(d) 真数学缺口**：**0**。墙的全部数学（fully surrounded ⇒ conforming ⇒
  半空间交 ⇒ wedge 包含）在 HOL 完整、且 Lean 已有同机器的两条独立落地
  （Auto21.PIIJBJK、TameLp.p6g）。

## 3. 最大风险与诚实天花板

1. **W2 LocalFan/Dih2k 构造**是最大单件（~150–200 行）：要为 (vPrime,ePrime)
   造 Hypermap 载体（dart 集 = f ∪ reverse f，2K 元）并验 HasOrders 三函 +
   Dih2k 五合取。两条路线：(i) 直接构造（V §5.3 的 2K 巧合路线，推荐）；
   (ii) 清 LocalAuto10 的 17 枚 sorry 走 LVDUCXU 忠实链（~500 行，覆盖面更大但
   超出 tau 需求）。膨胀上限按 1.5× 计。
2. **渲染追逐摩擦**：univ vs V（sigmaFan_univ_eq 已桥）、EE vs setOfEdge（rfl）、
   wedgeGe 三胞胎、ConformingAuto1 陈述的 `hypermapOfFan` vs TameLp 的
   `hypermapOfFanTl`（DecidableEq 实例搬运，TameLp 已有 wk_* 先例）。
   纯工程摩擦，不构成数学风险。
3. **诚实天花板**：三波合计 ~950 行（W2 膨胀 1.5× 时）；若 W2 选 LVDUCXU
   忠实路线则 ~1,300 行。建议 W2 单设 checkpoint（LocalFan 构造出「FAN 0 v'
   e' + FF=orbit + Dih2k」即交付）。

## 4. 勘误与交接注记

1. **V 线 DELIVERY.md §0.4 "wdart/conforming 章，全树未移植"不成立**——章已
   移植且零实 sorry；三锚缺一（锚 3）。V 的 W4 具名缺件清单第 5 项"wedge（需
   wdart/conforming 章移植立项）"的预估体量应从"章移植"降为"单件移植 + 簿记"。
2. V §0.3 各绕行估价（azim 桥 ~80、vPrime.ncard ~100 等）复核维持；补一项 V 未
   单列的 **LocalFan/Dih2k 构造 ~150–200**（V §0.4 提到"可行但量不小"但未入
   缺件清单的行数账）。
3. ConformingAuto1/2/20/21 等文件头的 "Every proof is a bare `sorry`" 已过时
   （proof-position grep 全零）——建议编排者安排文件头注记刷新，防止下一波
   工人被误导跳过查库。
4. `LocalAuto10.LVDUCXU`（:741）是 sorried 骨架——若后续 LVDUCXU 全链清偿，
   tau 的 W2 部分件可回灌为"引用 LVDUCXU"的短装配（dedup 机会，入 §5.2 类地图）。

---

# wdart/conforming 墙 → tau4/5/6_std 分波施工表（WAVES）

> 基线：主仓 HEAD（Lane V W3 交付后）；目标 = TameLp 三枚 e2e 直源
> `ineq_tau4/5/6_tauVEF_std`（TameLp:2112/:2125/:2138）。
> 前置事实（本侦察验证）：ConformingAuto1–23 全章零实 sorry；
> 锚 1（PIIJBJK 族）与锚 2（DARTSET_LEADS_INTO_SUBSET_WDART_FAN）已证；
> 唯一墙件 = CFYXFTY.hl:982 未移植，其 8 个原料全部在库。

## 0. 施工拓扑与债务守恒

```
W1 墙件（新私件块，建议落 TameLp 同文件 §3b 邻位或独立 ConformingScout 模块）
        │  W1 半成品不进任何消费闭包 → e2e 恒 4（3 tau + perimeter）
        ▼
W2 局化簿记（LocalFan 构造 + vPrime.ncard=K + azim/wedge transfer + diag/std 绕行）
        │  同上，e2e 恒 4
        ▼
W3 装配（三枚 tau 原位 sorry 替换）→ e2e 4→1（perimeter 另波）
```

- 全部新件建议落 **TameLp.lean 同文件**（目标与 wk_* 桥、p6g_fullySurrounded_
  conforming 私件都在此；免跨文件 import 仲裁）。若体量超限走独立模块，则
  依赖方向 = 新模块 → {ConformingAuto1/21, PlanarityAuto12/13, PlanarityComponent,
  AzimBridge, Fan, TopologyFan, PackingAuto2/18}，TameLp 侧一行 import + 转发，
  叶子先行、装配最后（ContraFanDeep 同款纪律）。
- 三锚的 Lean 消费签名（照抄 ConformingAuto1 惯例）：`hfan : FAN 0 V (ESTD V)`
  显式、face_set 走 `(hypermapOfFan 0 V (ESTD V) hfan).faceSet`；到 TameLp 的
  `hypermapOfFanTl` 只差 DecidableEq 实例搬运（TameLp:67–73 + wk_* 先例）。

## 1. 分波表

| 波 | 目标（新 Lean 件） | HOL 锚点 | 证明处方（精确 kit） | 预估 | 风险 | e2e |
|---|---|---|---|---|---|---|
| **W1a** | `affGtSubsetClosureDartsetLeadsIntoFan`：FAN + (∀v∈V, card>1) + fan80 + f ∈ faceSet + e ∈ f → affGt {0} {e.1,e.2} ⊆ closure(dartsetLeadsIntoFan f) | CFYXFTY.hl:982-1022 | 简化链（勿逐字抄 HOL 的 aff_ge 分解步）：u := sigmaFan 0 V E e.1 e.2；`aff_gt_1_3_subset_dart_leads_into_fan`（PlanarityAuto12:270，喂 hsigma:=rfl 方向需按 σ 定义式核对）给 affGt {0}{u,e.1,e.2} ⊆ dartLeadsInto e.1 e.2；`DARTSET_LEADS_INTO_FAN`（PlanarityComponent:375）换 dartsetLeadsIntoFan f；affGt {0}{e.1,e.2} ⊆ affGe {0}{u,e.1,e.2}（affGt⊆affGe + 单调，PlanarityNotCut:138 技巧）；affGe = closure(affGt) 用闭集.Argument：affGt ⊆ affGe、affGe 闭（OPEN_DIFF_AFF_GE 同款，PlanarityAuto14:176-183 模板）、closure_mono | 60–100 行 | 低（全件已证，纯装配） | 恒 4 |
| **W1b** | `wedgeClosureSubsetWedgeGe`：¬Collinear3 0 v σ → closure(wedge 0 v w σ) ⊆ wedgeGe 0 v w σ；及 `wDartFanOfFaceDart`：card>1 支的 if_pos 化简 | 拓扑步（HOL CLOSED_WEDGE 替代） | wedge ⊆ wedgeGe 逐点（0<azim→0≤azim、<→≤、多一 ¬Collinear 合取不妨碍）；`IsClosed (wedgeGe …)`（PackingAuto18:6884/6895，喂 fan_not_collinear）；closure_mono | 20–40 行 | 极低 | 恒 4 |
| **W1c** | `f_surr_wedge_subset`（W1 组合件）：FullySurrounded + f ∈ faceSet + (a,b) ∈ f → vPrime V f ⊆ wedgeInFanGe (a,b) (ESTD V)（全边集版） | RNSYJXM:358-393 的 wedge 半 | 链：x∈vPrime→(x,y)∈f→`POINT_IN_CLOSURE_AFF_GT_1_2`(PlanarityAuto13:584)→W1a→`DARTSET_LEADS_INTO_SUBSET_WDART_FAN`(ConformingAuto1:531，conformingFan 由 TameLp.p6g_fullySurrounded_conforming:1236 私件喂)→W1b→`sigmaFan_univ_eq`(AzimBridge:461)+`wedgeInFanGe_eq_wedgeInFanGe_p3`(AzimBridge:483) 收口；hypermapOfFanTl 实例搬运 ~15 行 | 50–80 行 | 低中（渲染追逐：univ/V、EE/setOfEdge、实例搬运） | 恒 4 |
| **W2a** | 面圈顶点两两相异 + `vPrime.ncard = K` | lp_main_estimate FaceK 节（LOFA_IMP_CARD_FF_V_EQ 内容） | `FACE_CYCLE_CARD`(LA10:364)+轨道单射反向归纳（模板 wk_orbit3；K=4/5/6 同构递推）；面圈 = faceMap 轨道，顶点序列 v_{i+1} = σ v_{i-1} v_i | 80–120 行 | 中（计数簿记，LA5 WRGCVDR 类摩擦；HOL 无此难度的现成对应——它经 LOFA 簇） | 恒 4 |
| **W2b** | azim/wedge transfer：x ∈ f → azimInFan x (ePrime E f) = azimInFan x E ∧ wedgeInFanGe x (ePrime E f) = wedgeInFanGe x E | localization.hl（LA10:584/:603 的 sorried 对应件） | N_E(x) = {prev,next} = N_{e'}(x)（面圈相邻性）；双侧 card=2>1；azimCycle 二元集对称 → sigmaFan 同值（`AZIM_CYCLE_EQ_SIGMA_FAN` LocalAuto3:771 + `sigmaFan_univ_eq`）；if 条件同值 | 60–100 行 | 低中 | 恒 4 |
| **W2c** | `LocalFan (vPrime V f) (ePrime (ESTD V) f) f` 构造 | RNSYJXM:314（LVDUCXU local_fan 支） | 载体 = f ∪ reverse f（2K 元；dart 集 = dart1OfFan v' e'）；e/n/f 三函在圈上逐点定义（faceMap 在 f 上与全扇逐点一致——面圈轨道重定向）；HasOrders 三函 + Dih2k H K（V §5.3 巧合）；FAN 0 v' e' 继承（fan1/2/6/7 逐条 + singletons 遗传） | 150–220 行 | **中高（最大单件）**；checkpoint：先交付「∃ hfan' FAN 0 v' e' + FF=orbit」再补 Dih2k | 恒 4 |
| **W2d** | local_diag/std 绕行 + packing/annulus 遗传 | lp_main_estimate:581/598 | `wk_estd_dist_le`(TameLp:1566) + `V_PRIME_SUBSET_V`(LA2:445) + ePrime ⊆ ESTD V（def 展开）+ Packing/ballAnnulus 子集遗传 | 30–50 行 | 低 | 恒 4 |
| **W3** | 三枚 `ineq_tauK_tauVEF_std` 原位闭合（K=4,5,6） | lp_main_estimate:796/893/992 | JEJTVGB_std_concl（LocalAuto1:580）实例化于 (vPrime,ePrime,f)：ConvexLocalFan = W2c ∧ (azimInFan≤π + W1c∘W2b wedge transfer)；4 ≤ vPrime.ncard ≤ 6 = W2a + wk_dtameK；非边/边距离前提 = W2d；dTame K ≤ tauFun v' e' f 经 W2b + `wk_f_surr_tauFun_eq_tauVEF`(TameLp:1608) 换 tauFun V (ESTD V) f → wk_f_surr_tauFun_eq_tauVEF 反向 → tauVEF；三件同构，K 差分只在 wk_dtame 与 4≤K≤6 数值 | 3×35–45 = 105–135 行 + 5 行 NEEDS 注记清理 | 低（全部件有签名；纯 chase） | **4→1** |

## 2. 工作量汇总与诚实天花板

| 项 | 数 |
|---|---|
| 剩余 sorry 件（消费侧） | TameLp 4 枚（perimeter :847 + tau4/5/6）；本计划消 3 |
| 预估总行数 | **~570–800 行（中位 ~680）**；W1 ~150–220、W2 ~320–490、W3 ~105–135 |
| 波数 | 3 波（W1/W2 可并行不同私件块，同文件须串行编辑；W3 依赖 W1+W2） |
| 真数学缺口 | **0** |
| 可承诺量 | W1+W3 ~255–355 行，成功率 ~90%（机械装配，件件有现成 kit） |
| W2 成功率 | ~75–85%（风险集中于 W2c LocalFan 构造与 W2a 计数；膨胀按 1.5× 备） |
| 诚实天花板 | ~950 行（W2 膨胀 1.5×）；若 W2c 改走清偿 LocalAuto10 LVDUCXU 忠实链（17 sorries，~500 行）则 ~1,300 行且额外解锁 LA10 全章 |
| e2e 收益 | 直源 −3（tau4/5/6_std 消失）；perimeter 需求面缩为两桥（LocalAuto7 三件 + face_representation + sum_face_rho_node1，另波） |

## 3. 每波收工必做

1. `lake build Kepler.Text.TameLp`（或新模块根 + TameLp）自然退出 0 error；
2. `#print axioms` 新公开件 ∈ {propext, Classical.choice, Quot.sound}；
3. W1/W2 期间重跑 e2e map 确认源清单恒 4（新件零消费者）；
4. W3 后重跑 e2e map：确认三源消失、无新源；tau4/5/6 的 DISCHARGES/NEEDS
   注记同步改写（防下一波误读）；perimeter 的 NEEDS 注记同步改写（墙桥已消）。

## 4. 风险与开放问题

- **W2c 是唯一无把握单件**：Hypermap 载体构造（proof-carrying 结构 + dartDecEq
  实例选择）摩擦大。缓解：LA10 的 `IsHypOn_p10` 框架 + `IN_DARTS_FF_IMP_
  DARTS_E_PRIME_V_PRIME`(:180) 等已证件可引；AzimBridge.localFan_data(:635)
  是反向（提取）参照；建议 checkpoint 交付（FAN+orbit 先行，Dih2k 后补）。
- **W2a 计数件**：LA5 LOFA 簇（WRGCVDR 根阻塞）的同内容物不可引——照 V 的
  轨道归纳自证，勿试图消费 LA5 未清件。
- **陈述冻结**：三枚 tau 陈述与 wk_* 桥签名一字不动（V W3 已冻结）；W1–W2
  新件全部 private、零消费，闸门零删行纪律天然满足。
- **过时注记风险**：ConformingAuto1/2/20/21 等文件头 "Every proof is a bare
  `sorry`" 已失真（proof-position grep 全零）——工人勿据此跳过查库；建议
  编排者安排注记刷新波。
- **perimeter 顺延**：W1 落地后 TameLp:847 的 NEEDS 注记应更新为"差
  LocalAuto7 三枚（BGMIFTE/FAN_PERIMETER/WSEWPCH，faithful sorry）+
  lemma_face_representation + sum_face_rho_node1"；勿在本计划内顺手攻
  （LocalAuto7 周长 lane 是独立专项）。

---

```
HOL引理	行号(HOL文件:行)	分类	Lean对应	估行数(Lean)	备注
f_surr_localization_convex_local	RNSYJXM-compiled.hl:327	(c)合成墙件	无（TameLp tau4/5/6 NEEDS 注记锚）	180	三锚合成；wedge 部分走锚1+2+3，local 部分走 W2 簿记；Lean 目标形 ConvexLocalFan (vPrime V f) (ePrime E f) f（LA1 编码）
f_surr_localization	RNSYJXM-compiled.hl:300	(c)异陈述	LocalAuto10.LVDUCXU(:741, sorry) 局部替代；V绕行重建	0(W1外)	5合取：local_fan + face_eq + azim_eq + wedge_gt_eq + wedge_ge_eq；Std 装配只需 azim/wedge transfer + LocalFan 构造
fully_surrounded_imp_conforming	add_triangle-compiled.hl:652	(a)已证	ConformingAuto21.PIIJBJK:903；TameLp.p6g_fullySurrounded_conforming:1236(private)；TameLp.contraveningConformingTl:2151(ESTD版)	0	证明体已验（极小反例+by_cases，非骨架）
— PIIJBJK	Conforming.hl:14195	(a)已证	ConformingAuto21.PIIJBJK:903	0	极小反例(N_FAN) + 加边矛盾；63 HOL 行
— TXFBALB	Conforming.hl:12056	(a)已证	ConformingAuto19.TXFBALB:2031（~187行证明体）	0	加边主件，456 HOL 行
— TXFBALB_VERSION	Conforming.hl:12512	(a)已证	ConformingAuto20.TXFBALB_VERSION:143	0	27 HOL 行，调用 TXFBALB
— GGZWYRM	Conforming.hl:13253	(a)已证	ConformingAuto20.GGZWYRM:703	0	conforming_diagonal 支
— conforming_bijection_fanadd_verrion	Conforming.hl:12539	(a)已证	ConformingAuto20.conforming_bijection_fanadd_verrion:194	0	conforming_bijection 支
— HYUAZSE	Conforming.hl:14143	(a)已证	ConformingAuto21.HYUAZSE（同文件 PIIJBJK 上文）	0	conforming_half_space 支
— nonconformin_fan_imp_n_fan_ge0	Conforming.hl:1806	(a)已证	ConformingAuto8.nonconformin_fan_imp_n_fan_ge0:267	0	13 HOL 行
— fully_surrounded_imp_fan80	add_triangle-compiled.hl:260	(a)已证	TameLp.p6g 内联（fan80 半步 azim_nonneg+unique_azim0_point_fan）+ConformingAuto 链	0	24 HOL 行
— fully_surrounded_card_set_of_edge1	add_triangle-compiled.hl:226	(a)已证	TameLp 私件链（SURROUNDED_IMP_CARD_SET_OF_EDGE_GE_3_TL→hcard）	0	6 HOL 行
Conforming.DARTSET_LEADS_INTO_SUBSET_WDART_FAN	Conforming.hl:268	(a)已证	ConformingAuto1.DARTSET_LEADS_INTO_SUBSET_WDART_FAN:531	0	只消费 conformingFan 的 half-space 合取支；863行文件 proof-position sorry=0（文件头"bare sorry"注记过时）
— conforming_fan(def)	Conforming.hl:44	(a)已证	ConformingDefs.conformingFan:184	0	六合取 def；hfan 显式参惯例
— conforming_half_space_fan(def)	Conforming.hl:26	(a)已证	ConformingDefs.conformingHalfSpaceFan:121	0	半空间交
— dartset_leads_into_fan(def)	Planarity.hl:10978	(a)已证	PlanarityComponent.dartsetLeadsIntoFan:348	0	ε-选择 def
— dartset_fully_surrounded_is_non_isolated_fan	fan.hl:2847	(a)已证	ConformingAuto 链（dartOfFan_eq_dart1_of_surrounded 同族）	0	10 HOL 行
— face_subset_dart_fan	fan.hl:2823	(a)已证	Hypermap.face_subset_darts（本库 Hypermap 结构自带）	0	24 HOL 行
— remark1_fan	fan.hl:423	(a)已证	Fan.edge_ne_of_fan:1039 + properties_of_setOfEdge_fan:334	0	互异+成员两部分
— sigma_fan_in_set_of_edge	fan.hl:565	(a)已证	Fan.sigma_fan_in_setOfEdge:326	0
— properties_fully_surrounded	Planarity.hl:1872	(a)已证	Planarity.properties_fully_surrounded:2370	0	¬Coplanar 四点件
— WEDGE_LUNE_GT	Conforming.hl 用	(a)已证	wedge/azim 恒等（Geom/Azim wedge def + LocalAuto 桥）	0	Auto1 证内已消化
— inter_aff_gt_3_1_is_aff_gt_2_2	Planarity.hl:14725	(a)已证	ConformingAuto1 证内引用（collinear3/affGt 恒等 kit）	0	Auto1:427 docstring 点名
Cfyxfty.AFF_GT_SUBSET_CLOSURE_DARTSET_LEADS_INTO_FAN	CFYXFTY.hl:982	(b)机械移植	无（全树 grep closure+dartsetLeadsIntoFan 零命中）	60-100	唯一真墙件；41 HOL 行；Lean 陈述按 ConformingAuto1 惯例 hfan 显式
— aff_gt_1_3_subset_dart_leads_into_fan	Planarity.hl:13744	(a)已证	PlanarityAuto12.aff_gt_1_3_subset_dart_leads_into_fan:270	0	证明体已验（rwDartFan 阈值法）
— Planarity.DARTSET_LEADS_INTO_FAN	Planarity.hl:10989	(a)已证	PlanarityComponent.DARTSET_LEADS_INTO_FAN:375	0	dartsetLeadsIntoFan f = dartLeadsInto (任一面成员)
— properties_of_elements_in_face_fully_surroundedfan	fan.hl:2857	(a)同义内联	PlanarityComponent:542-546 技巧（faceSet 成员→darts→dart1OfFan→边）	0-10	pair-dart 编码下退化两行；ConformingAuto6:314 缺口注记同此
— CLOSURE_AFF_GT_1_3_EQ_AFF_GE_1_3	CFYXFTY.hl:940	(c)桥	无同名件；绕行=affGe 闭(OPEN_DIFF_AFF_GE)+closure_mono（PlanarityAuto14:176-183 现成技巧）	15-30	35 HOL 行；只需 ⊆ 方向
— aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3	Planarity.hl:14125	(a)已证	PlanarityAuto13.aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3:89	0	（锚3 的 HOL 证用其分解；Lean 简化链可不用）
— POINT_IN_CLOSURE_AFF_GT_1_2	Planarity.hl 对应	(a)已证	PlanarityAuto13.POINT_IN_CLOSURE_AFF_GT_1_2:584	0	v ∈ closure(affGt {x}{v,u})（三点互异）
— AFF_GT_SUBSET_AFF_GE	拓扑平凡	(a)已证	PlanarityNotCut.affGt_subset_affGe':138；TopologyFan.affGt_subset_affGe:1814(private)	0
— fan80(def)	Planarity.hl:1338	(a)已证	Fan.fan80:227	0
wedge_in_fan_gt_eq_w_dart_fan（w_dart_fan def）	fan.hl:1027	(a)已证	Fan.wDartFan:162；TopologyFan.eq_set_wdart_fan:1631	0	card>1 支 = wedge（开楔）
closure(wedge) ⊆ wedgeGe（HOL CLOSED_WEDGE 步）	拓扑.hl 对应	(b)胶水	wedge(Geom/Azim:63)⊆wedgeGe 逐点平凡 + IsClosed wedgeGe（PackingAuto18:6884/6895）	20-40	Lean 无需等式，单调+闭即足
wedge_in_fan_ge(def)+渲染桥	localization.hl:88	(a)已证	LocalAuto1.wedgeInFanGe:162（canonical）；AzimBridge.sigmaFan_univ_eq:461、wedgeInFanGe_eq_wedgeInFanGe_p3:483、azimInFan_eq_azimInFan_p3:473	0	EE/setOfEdge=rfl；univ/V 已桥
hypermap 同构 h=ext_dart（iso 三处）	RNSYJXM:361	(a)消解	pair-dart 编码下整体消失；hypermapOfFanTl=hypermapOfFan 换 DecidableEq（TameLp:67-73）	10-20	HOL fan_hypermaps_iso_explicit2 步不需要
LocalFan(vPrime,ePrime,f) 构造（local_fan 支）	RNSYJXM:314（LVDUCXU）	(b)簿记	无现成构造；LA10 链 17 枚 sorry（IN_DARTS_FF_IMP...:180 等已证可引）；AzimBridge.localFan_data:635 为正向提取参照	150-200	dart1(v',e')=f∪reverse f（2K 元巧合，V §5.3）；Hypermap 载体 + HasOrders 三函 + Dih2k 五合取；建议 checkpoint 交付
vPrime.ncard = K（LOFA_IMP_CARD_FF_V_EQ 同内容）	lp_main_estimate Face4/5/6 节	(b)簿记	无；LA10.FACE_CYCLE_CARD:364（已证）+ 轨道单射归纳	100	面圈顶点两两相异；K=4/5/6 同构递推（模板 wk_orbit3）
azim/wedge transfer（tau_fun_local 绕行）	localization.hl	(b)簿记	LA10.AZIM_IN_FAN_EQ_IZIM_E_PRIME:584 / WEDGE_IN_FAN_EQ_WITH_E_PRIME:603 均 sorry；绕行直接证	N(E)(v_i)={v_{i-1},v_{i+1}} 唯一候选同值（V §0.3）
local_diag 绕行	lp_main_estimate:581	(b)簿记	无；LpFan.3 + ePrime ⊆ ESTD V + vPrime ⊆ V（LocalAuto2.V_PRIME_SUBSET_V:445 已证）	20	非边前提遗传
local_std 绕行	lp_main_estimate:598	(b)簿记	TameLp.wk_estd_dist_le:1566（已证）+ Packing V	20	边前提 = 定义性距离界
FAN 0 vPrime ePrime 继承	lp_main_estimate FaceK 节	(b)簿记	无现成；fan1/2/6/7 从 FAN 0 V E 逐条（ePrime ⊆ E、singletons 遗传）	40	V §0.3 复核维持
packing_v_prime / v_prime_subset	.lp_main_estimate FaceK 节	(a)已证	LocalAuto2.V_PRIME_SUBSET_V:445 + Packing/ballAnnulus 子集遗传	0-5	def 级
三枚 tau 装配（ineq_tau4/5/6_tauVEF_std）	lp_main_estimate:739/831/929（Std :796/893/992）	(b)装配	TameLp:2085/2117/2130 骨架（NEEDS 注记已更新）；wk_f_surr_tauFun_eq_tauVEF:1608、wk_dtame4/5/6（V W3 已备）	3×35-45	JEJTVGB_std_concl（LocalAuto1:580）实例化于 (vPrime,ePrime,f) + dTame V'.ncard ≤ tauFun 链
fully_surrounded_perimeter_bound（连带）	lp_main_estimate:1530	部分解锁	TameLp:839（sorry）；差 LocalAuto7 三枚（BGMIFTE:642/FAN_PERIMETER:691/WSEWPCH:698 均 faithful sorry）+ lemma_face_representation + sum_face_rho_node1	（另波）	墙是三桥之一；W1 落地后其 NEEDS 注记应改写
ineq_tau4/5_pro_tauVEF(_aux)、tau4_diag3、tau5_diags（连带）	lp_main_estimate:1029/1069/1134/1234/1329	未来	W4-W1/W2 落地后降为装配级；现无 Lean 骨架	（另波）	lp_main_estimate 中锚件的另外 5 个消费点
```

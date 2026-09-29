# e2e-debt-map — 主定理端到端可达债务图（M5′ 现行度量文件）

> 2026-09-29 快照 v2（wave3 收官更新；自动探针本机不可用，见 DEBT.md
> 脊柱节说明）。目标定理：`Kepler.Assembly.the_kepler_conjecture_from_interfaces`。
> 里程碑定义与四步路线：`docs/phase6-spine.md` §6。**度量 = 下表"在账"数，
> lane 排序依据 = 本图**；每波收工后编排者更新。

## A. 脊柱接口占位（Assembly.lean §2c/§2d，12 枚，全部在账）

| # | 接口 | 性质/一次性成本 | 分级 | 需重型机 |
|---|---|---|---|---|
| ~~A1~~ | ~~`isoOppositeEq`~~ | **已闭合 (wave3)** | ✅ | 否 |
| A2 | `contraveningNegative` | V↦−V 对称：scriptL/ESTD/ECTC/ncard 不变 + surroundedNode 像 | 廉价 | 否 |
| ~~A3~~ | ~~`localAnnulusInequalityScriptL`~~ | **已闭合 (wave3)**：HOL 对照确认为定义性恒等，已填 | ✅ | 否 |
| A4 | `kcImpTheKc` | HOL kc_imp_the_kc：体积形 kepler_conjecture ⟹ 计数密度形（真实分析计数论证） | 中等 | 否 |
| A5 | `hypermapOfFanNeg` | hypermapOfFan 构造层面 + oppositeHypermap 交换 | 中等 | 否 |
| A6 | `fcdjdot` | FNJLBXS：pack_ineq_def_a + scriptL>12 见证 ⟹ Contravening 存在 | 中等 | 否 |
| A7 | `elllnyz` | ELLLNYZ.hl 镜像析取桥 | GIANT（tame 章） | 否 |
| A8 | `tameCorrespondenceIso` | WMLNYMD.hl | GIANT（tame 章） | 否 |
| A9 | `jcajydu` | JCAJYDU 一般形 + P6-C 遗留 `hypermapOfList` 构造 | GIANT（tame 章） | 否 |
| A10 | `mqmsmab` | MQMSMAB 章（ssreflect 17KB）+ KCBLRQC 桥 | 中大 | 否 |
| A11 | `nonlinearInequalities` | 六件合取注册表：CertifiedIneqHolds 语义填实 + 993 条证书（G4 线，CertTM 在铺） | 数据密集 | **是**（549 重跑） |
| A12 | `lpArchiveCertificates` | 43,078 图 LP 持久化 + 逐行实例化（P6-D 两 schema 模板已试点） | 数据密集 | **是**（~324 核时） |

## B. 已被消费链可达的章级 sorry（在账）

| 节点 | 位置 | 流入路径 | 状态 |
|---|---|---|---|
| ~~`PACKING_CHAPTER_MAIN_CONCLUSION`~~ | PA25 | textCapstone 直接消费 | **已真化 (wave3)**：装配步闭合，债务上移至 RDWKARC_concl(PA2)+TSKAJXY(PA21) 两枚树内 sorry |
| ~~`RDWKARC_concl`~~ | PA2 | PA25:3695 `refine RDWKARC_concl hkc ?_ ?_` 唯一消费 | **已真化 (2026-09-29，`16f31f68`)，JGXZ 半边已清 (`83f5ea04`)**：装配/平移/重编论证全真 + `JGXZYGW_KY_p2` 经新叶模块 `PackingJGXZYGW.jgxzygw_p`（12/12 替证闭合，公理仅标准三）+ PA19 侧 `JGXZYGW_p19` 同源 shim——**RDWKARC 双臂全通**；余 `UPFZBZM_concl` 一枚接口 sorry（上游四巨物 = 波 2/3，见 `docs/upfzbzm-scout.md`）+ PA1 骨架存废/saturated 重名 merge 裁决（scout §5） |
| ~~`UPFZBZM_concl` 架构半边~~ | PA19 | PackingConcl:510 discharge 已接线 | **波 1 已真化 (2026-09-29，`abfd2fcb`)**：`NEGLIGIBLE_FUNC` 忠实架构（侦察 f8c207a7 规格书；零新增 sorry）；capstone/FCC 半边/数值链原已全真证。余上游四巨物（KIZHLTL1/2/4 + SUM_GAMMAX，HL ~2400 行，均已预接线）= 波 2/3；Pack2.hl 测度桥四件套是波 2 唯一未知量，见 `docs/upfzbzm-scout.md`。**波 2A 已真化 (2026-09-29，`dfa60295`)**：PA15 有限性包三件——`HD_IN_MCELL` 真证全净（四 case 路线入 playbook §5.4）、`FINITE_MCELL_SET_lemma1`/`FINITE_MCELL_SET_LEMMA` 真证（唯一染色 = PA12 `VORONOI_LIST_3_SINGLETON_EXPLICIT`，GIANT 落地即自动转净；net −3：26→23）；新私件 `p15_omega_dist_hd` 是 MCELL_SUBSET_BALL_4 的 i∈{0,1} 支钥匙（i=2 唯一卡点，地图入 playbook §5.4）。**波 2B/2C 已真化 (2026-09-30，`9bc5b5bd`)**：PA16 `KIZHLTL1`/`KIZHLTL2` 双闭合（sorry 9→4 零新增），`PackingConcl.KIZHLTL1/2_concl_discharged` 自动真化。**波 3 已真化 (2026-09-30，`c41bccd9`)**：`KIZHLTL4` 闭合（4→3，HL 五步直译，2π 步经 PA2 `GRUTOTI1_concl` 设计接口，PA23 落地时 `exact` 自动放电）；**PA19 上游四巨物实化其三，仅剩 `SUM_GAMMAX_LMFUN_ESTIMATE`(PA18:2538, bare sorry, sum_gamma.hl 1400 行链)**；PA16 余 3（KIZHLTL3 无 HL 证明冻结桩等裁决、QZYZMJC/MCELL_SET_NOT_EMPTY 既有 GIANT） |
| `MHFTTZN_lemma2` | PA6 | MHFTTZN1/2/3/4 + BARV_AFFINE_INDEPENDENT 链 | **已真化 (2026-09-29，`eafa4874`)**：MHFTTZN 全链（lemma/lemma2/1/2/3/4）`#print axioms` 仅标准三零 sorryAx |
| `facet_rep_in_facet` | PA22 | planar 面-表示链 | **已真化 (2026-09-29，`3538883a`)**。**wave-3 已落账 (2026-09-29，`e4248c02`)**：EXPLICIT ℂ kit 19 件（Polytope.lean 模板逐段镜像，公开 `facetOfCPolyhedronExplicit`/`p22_facetOfCPolyhedron` 公理全净）+ 连清 9 枚（`POLYHEDRON_MEMBER`/`facet_rep_refl`/`facet_rep_in_poly`/`facet_rep_a_uniq`/`facet_arg_lt_pi`/`poly_sort_antisym`/`POLY_SORT_LEMMA`/`POLY_SORT`/`POLY_SORT_BIJ`）——sorry 52→43 零新增。**eus1 已收口 (2026-09-29，`87a39f04`)**：同文件序手术（facet_rep 块移至 kit 后）+ 65 行真证（â=‖a‖⁻¹•a 换元 + 球点 mid-point 上确界）——**facet_rep 全族零 sorry 闭合链形成**（`p22_facetOfCPolyhedron`→`eus1`→`facetRepPair`/`spec`/`a`/`b`/`props`/`uniq_c`→`in_facet`/`refl`→`POLYHEDRON_MEMBER`→`facet_rep_in_poly`，:1499→:1794），9 枚继承件全部脱 sorryAx。余 42 枚全在 :2000 行后 GIANT 区（insert_v/bisector_point_exists/POLYSORT_BIJ2/EUSOTYP_simple、GOTCJAH、POLYHEDRON_FACET_SUM_4Pi、XULJEPR；面族计数 4744-5630 是大头）、pad2d3d_facet（ℂ 侧 kit 已就位，还需 V3 侧镜像 kit + FACET_OF_LINEAR_IMAGE ℂ 版） |
| `TSKAJXY` 0/3/4 臂（现 :2550） | PA21 | PA25:3704 `exact TSKAJXY …` 唯一消费 | **四波全落账 (2026-09-29)**：波 0 银行（`2f2c431c`）+ 波 1 GRKIBMP（`1591e1c1`）+ 波 2a kit（`3f162f06`）+ 波 2b cell3_from_ineq_thm（`eedb36b6`）+ 波 3 臂收口（`ba88d11e`，编排者三行机械）——**capstone `TSKAJXY` 装配已真**。**A1+B1 已全清 (2026-09-30，`af3f31fc`)**：A1 几何 5 件 + B1 记账 9 件（含补缺 MCELL2_HL_LT_SQRT2 移植、FRUSTT_RCONE_GE 锥面测度零经保测投影+addHaar_sphere）。**A2 已落账 (2026-09-30，`52a01dfd`)**：5/6 闭合——`OMEGA_LIST_BISECTOR`（塔点等距 kit 绕开 PA5/PA6 sorry 污染）+ `MCELL1_RADIAL`/`MCELL1_VOL`/`GAMMAX_MCELL1`/`TSKAJXY_1`（capstone：gammaX = sol·(√2³/3−2mm1/π)，括号正由 PA20 种子 `HJKDESR1a_1cell`）；`MCELL1_SOL_RESTRICT` 卡文件序（两条收口路线原位注记：p21e 副本上提或区块后移裁决）。余 15 战术 sorry：B2 七枚（FRUSTT_WEDGE_RCONE_GE 起步，import PA18 + 两 ~30 行私件；尾段 MCELL2_VOL_SPLIT_EXPLICIT 是 WedgeVolume 模板 GIANT；LEFT_ACTION/PERMUTE_01 卡 PA14:231/258/286 具名桥）+ B3 四枚 + SOL_RESTRICT + 界外 TSKAJXY_034（G 轨）/mi_gamma3f（merge-ineq 2b）/`pack_nonlinear_rest`（G4 挂账） |
| `LEMMA_3_POINTS_FINAL`/`LEMMA_4_POINTS_FINAL` | ContraFan | contraveningFan → CKQOWSA | **CF-3 已真化（路线 B，前波）；CF-4a 已落账 (2026-09-29，`f25bcc49`)**：新模块 `ContraFanDeep.lean` 1070 行（不 import ContraFan——接线方向相反，twin 自拷前奏含 CF-3 L3F 孪生）；件 1 `cf4_cone_inter_imp_segment_conv` + 件 2 **分离平面四点件** `cf4_separation_plane_4_points`（±(v2×₃v4) 平面 + Cramer 符号四分，辅助链 ~350 行零 sorry）真证；9 枚带账 NEEDS（rotation 三件/连续性大件 665 行/circumcenter 两枚/段交两枚）全附 HOL 锚点。**CF-4b 已落账 (2026-09-29，`dd20ae50`)**：5 件闭合（rotation_dist_decrease/circumcenter 两枚/aff_ge_inter_segments/rotation_lemma，公理全净），sorry 9→4。**CF-4c 已落账 (2026-09-30，`d544b010`)**：再三件闭合（family_special——夹逼延拓统一锥表示，docstring 三段 g 分析实际不需要/continuous_intersection_point——Cramer+Gram 行列式/rotation_about_axis——正交分解平移），**sorry 4→1**，全零签名漂移。唯一遗留 = 主石 `cf4_continuous_lemma_aff_ge`（665 行连续性大件）：上游缺口已精确化 = 穿锥判别两件（HOL :1928/:2138，中等体量，风格同 cf4_not_between_estd）+ IVT 打靶族，②③ 已备齐可直接插，合计 600-1000 行待专项波；见 docs/contrafan-scout.md |
| LA38 `tau3_taum_d`/`tau3_taum_dfun` | LocalAuto38 | （经 main_nonlinear_terminal_v11 合取项间接）| 陈述级：缺 `2 ≤ dist` 下界，待对照 HOL 补陈（走 STATEMENT-FIX） |

## C. 接口填实的下游依赖（未来在账，先遣情报）

- tame 文字章 64 个 .hl/4.6MB（A7-A9）：侦察情报见 playbook §5（GLTVHUM 五级链、
  DUUNHOR 三共享缺件）；`hypermapOfList` 构造（P6-C 遗留）是 A9 前置。
- **GLTVHUM 五级链进展 (2026-09-30，`2c71cde2`)**：①②③ 已闭合（PA6 sorry
  13→10：FACET_OF_POLYHEDRON_EXPLICIT_BIS/IDBEZAL/VORONOI_LIST_EQ_UNION…，
  ③绕开未移植 POLYTOPE_UNION_CONVEX_HULL_FACETS 走紧 polyhedron 边界点引理）；
  ④ GLTVHUM_lemma1 数学路线全推导入 NEEDS（仅 ∃-setOf bookkeeping 收口）；
  ⑤ **结构性阻塞**：装配件在 PA2 而 PA6 import PA2——需整链复制 PA2 侧
  （~600 行 p2_ 私件 + 5 个 PA5-sorry 黑盒）或架构调整，**待编排者/用户裁决**；
  PA4 cellParams 9 枚族与 DUUNHOR（三前件均 sorry）等 ④⑤。
- **新增在账（wave3 侦察）**：PA22 cone0P22=affGe 弱编码族 5 枚 + PA7 permutes 弱
  编码族（KSOQKWL 等）——提案 r2 已出补丁（11/14/15/DUUNHOR），结构性立项
  "planar 编码定义纠正"待用户拍板。
- **wave3 附带解锁**：PA7 `BARV_CIRCUMCENTER_EXISTS` 成真（PA18 cc 簇钥匙）。
- **GRUTOTI 侦察结案 (2026-09-29，`docs/grutoti-scout.md`)**：非从零移植——PA23
  骨架 + capstone 组装已在树（9 机械件已证 + 5 枚 giant sorry，全树零 importer）；
  实际量级 Lean 2800–5000 行（region/cell_vol 双 GIANT）。三座共享银行：
  锥帽体积套件（**源不在本仓**，与 REUHADY(PA24)/TSKAJXY3 三链共享，GT-1 先导波
  建新模块 ConicCapVolume.lean）、Pack2.hl 测度桥（与 UPFZBZM wave-2/KIZHLTL1 共享，
  **已实化**：KIZHLTL1/2 `9bc5b5bd`）、PA15 marchal3 套件 ≥9 枚。
  **GT-1 已落账 (2026-09-30，`0d3243c0`)**：`ConicCapVolume.lean` 1110 行——
  `volumeConicCap`（2/3·π·(1−a)·r³ 完整推导）+Pos/Measurable/Bounded 四公开件
  公理全净，纯 Geom.* 零 sorry 依赖；余 3 sorry 带账（sliceWedge 仅剩 Real.lt/le
  order 结构体对接、wedge kernel、AZIM_EQ_0_PI 桥）。
  **GT-2 前段已落账 (2026-09-30，`dfd748ed`+`d67e5fcf`)**：PA15 ★×2 转真
  （FINITE_EDGE_X2/MCELL_SUBSET_BALL8_1——**i=2 深坑正面攻下**：mutual-rconeGe
  代数相加，23→21）；PA23 p23_ kit ×4（Pack2 测度桥有限版银行化）。
  **陈述缺陷发现 ×3**：①volD_pos 缺 `hne`（STATEMENT-FIX 提案项 18 已立案
  `1137ad92`，patch 可贴性实测 0 error，**待用户裁决**）；②sum_volD 缺
  Packing/saturated 前提；③pivot 缺 region 覆盖假设——②③登记未立项，等
  grutoti_region 落地后补前提走同一流程。GT-3 剩余关键路径：CONIC_CAP trio
  (PA15:818-828，GT-1 公式在手预估 100-200 行)/grutoti_region(giant)/AJRIPQN。
- **Phase 2 Graphs 链**：wave3 收官构建发现 `lake build Kepler.Assembly` 会自展
  式重建 Graphs CertShards（本机 30-2100s/片，9000+ jobs 量级）——后台跑完后
  脊柱探针解锁，DEBT.md"结构性不可用"注记作废。
- MQMSMAB 章（A10）：ssreflect 17KB，相对小。
- G4/LP 两条数据线（A11/A12）：本机只做注册表/模板/checker 形态冻结（CertTM 线
  在铺），灌数据等重型机。

## D. 已闭合（不再在账）

`assembly`、`textCapstone`（真证明）、`linearProgrammingResults`（真推导）、
`goodListArchive`（P6-C，19,715 图）、`contraveningFan`（T5）、
`tamePlanarHypermapRestricted`、`hypermapIsoTrans`、`oppositeHypermap`、
Phase 2 `tame_classification`、LA16 `nonlinear_imp_lp_main_estimate_p16`。

## E. 刷新方式

1. token 口径：`python3 lean/scripts/debt_ledger.py . > DEBT.md`（自动）。
2. 本文件：编排者每波收工后按闸门 commit 手工更新 A/B 表（自动探针待 Graphs
   olean，见 DEBT.md 脊柱节）。

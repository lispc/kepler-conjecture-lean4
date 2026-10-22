# e2e-debt-map — 主定理端到端可达债务图（M5′ 现行度量文件）

> 2026-09-29 快照 v2（wave3 收官更新；自动探针本机不可用，见 DEBT.md
> 脊柱节说明）。目标定理：`Kepler.Assembly.the_kepler_conjecture_from_interfaces`。
> 里程碑定义与四步路线：`docs/phase6-spine.md` §6。**度量 = 下表"在账"数，
> lane 排序依据 = 本图**；每波收工后编排者更新。

## 2026-10-12 增量（五线满负荷日 + 收口令；编排者账）

用户晨令改 steady-state 5-6 线自调度，午后令"本波全部收口后不再起新线，总结
push 待命"。全天落地账（含晨间 22 笔，详见各 commit）：

- **PA20 文件级 sorry 归零**（`4d676cbf`+`67f5c1aa`）：gammaX 章双件全闭——
  `gammaX_gamm4fgcy`（k=4，SimplexVolume 反向 import）与 `gammaX_gamma3f`
  （k=3，绕开 HL 未移植 MCELL_ID_*，voronoiList 隶属自证 apex √2 等距）。
  唯一下游 PA25:3287 `mcell3_gammaX_gamma3f` 移交 leaf_rank 车道。
- **PA7 XYOFCGX 本体闭合**（`5127ecf1`，sorry 36→21）：XYOFCGX 家族 +
  BARV 前置两件 + 投影件八条；四重复定理经 PA6 同名提供（EV20 豁免）。
  残余 21 = GIANT 链（WQPRRDY capstone/WAUFCHE2/KSOQKWL/YIFVQDV/
  XNHPWAB1-4/omegaList 链），下一工位 XNHPWAB1（前置已就位）。
- **PA24 情形 A/B3 全证 + B2 单支残件化**（`8b5bd3d3`+`e4eda77d`）：
  capstone 三分装配；侦察纠错 = `MXI_EXISTS_concl` 在 B2 支为假（r₃<√2
  仅 B3 支成立），**移交 PA2 车道补 `r₃<√2` 假设**；B2 泛具子情形需四点
  凸包装配（~300-400 行），退化子情形（ω₂=ω₃）换叶走支撑面引理
  （~200-300 行，下一整波）。
- **TameSpine 第三批落地**（`cdcc3ea2`）：TameList3.lean 1,309 行/84 件/零
  sorry（tame_list.hl:1469-2934 indexf/split_at/take·drop/betwn 家族）；
  三批累计 ~4,050 行/323 件。
- **闸演进 EV20/EV21**：EV20 重复件豁免（干净直接 import 提供同名声明+
  语句前缀空白归一化全等；证明体不比对）；EV21 sorry 计数代码行口径
  （docstring 散文行双侧剔除，修 EV19 假阳性暴露）。
- LA5 晨间四波 73→48（`43bf4829` 等）；POS_DIRECT→SUCCESEOR 根系攻坚
  线死于 API 连接超时（基础设施），**盘上 salvage 走闸落地**（末笔）：
  RHO_NODE_SET_IN_A_PLANE_IMP_POS_DIRECT（:689 根件）+FAN_IN_AFF_GE_IMP_EQ
  +AFF_GE22+AZIM_EQ_0_GE_ALT2+WEDGE_GE_EQ_AFF_GE 五件骨架转真
  （+815/−18，骨架 38→33，闸 PASS @全七根）；SUCCESEOR 下游 10 件解锁面
  已开，续攻留给下一波。
- **DEBT.md 口径跳变说明**：账本总量 1,713→44,717 系 LP 叶户（43,078 枚
  `lpT<id>`，53acc49c）首次被 ledger 计入；**可比口径**（Text 非LP+root+Geom）
  实际 1,713→1,639（−74，今日全波）；Geom 区清零（SimplexVolume 反向
  import 后无 sorry 文件）。PA20 0 / PA24 2 / PA7 22 / LA5 43。

## 2026-10-08 增量（滚动 sub-agent 稳态制首日；编排者账）

运行方式切为恒定 5-6 线在飞（用户令），落地节奏从"批次"变"流水"。当日八笔
全部推远端，对下表的影响：

- **B 类 `GRUTOTI` 系树内债文件级闭合**（`09ad7a10`）：G3（反向 k=3/4）以
  覆盖反证清零（路线翻案：HL GRUTOTI.hl:2620-2650 覆盖引理证该分支真空，
  非 S₃ 置换/junk 钉定——该死路结论已入档），PA23 证明 sorry 归零。NEGLIGIBLE_FUNC
  全链的 GRUTOTI 系自此只欠跨文件上游（GRHIDFA 簇等），文件内无字面债。
- **p24 情形 A 收口**（`8b5bd3d3`）：`p24_exists_mcell_not_flat` 残余缺口 =
  情形 B（r₄≥√2 支）+ mcell4 测度三明治（`docs/projects/pa24-nonflat-roadmap.md`
  第 5-6 档；注意 B2 已按 d=2.4 反例翻案为 r₃<2）。
- **A11（nonlinearInequalities）T1 展开**（`9fcec148`）：接口单根 → 16 具名
  中层骨架 + 会师真叶 certifiedIneqHoldsPilotCase（零 sorryAx）；SF36 语义
  落地。993 证书/G4 线仍需重型机。
- **packing 前提树 T4 展开**（`60191e40`）：拓扑结论 = packing 不独占上游
  Assembly 级 sorry 根；SF31 debt-bridge 形展开住 PA25（7 具名骨架 + 6 真桥件，
  冻结签名六处逐字节 IDENTICAL）。PA18 def-taint（ccUh→ccKe 语句闭包）是
  pkrmPeriodic 面上 sorryAx 的真实来源，清净需 PA18 leaf-cell 链（YBZFUPO/
  NWVRFMF，新波待立）。
- **A12（lpArchiveCertificates）T2 桥工程启动**：P6-D 形 per-record 骨架
  试点中（数据重跑仍 deferred-compute）。
- **PA2 桩收割波 1+2**（`94c04276`）：DUUNHOR r2 消费侧升形（SF 项 13(c′)，
  公理面零 sorryAx）+ A 类 20 根删除；PA2 独立 sorry 46→27。
- **tame 章（A7/A8/A9 前置）**：W0 keystone（`b733f870`，S1 规格桥 + 验收锚
  `isHypermapOfList_hypermapOfList`——A7/A9 证人机器入 Assembly 谓词层；
  S11 五 flip 源备好待 DEF-FIX 拍板）+ B1 批 1（`d9f1085e`，TameList1 647 行
  30 件全真证）。
- **census 口径注记**：sorryAx-tainted 638 → 633（收割）→ 641（T4/T1 展开期
  按设计上升——单根拆 N 骨架）；**M5″ 递减指标是清叶期指标**，展开期看骨架
  吸附与 bank 叶流动。

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
| ~~`RDWKARC_concl`~~ | PA2 | PA25:3695 `refine RDWKARC_concl hkc ?_ ?_` 唯一消费 | **已真化 (2026-09-29，`16f31f68`)，JGXZ 半边已清 (`83f5ea04`)**：装配/平移/重编论证全真 + `JGXZYGW_KY_p2` 经新叶模块 `PackingJGXZYGW.jgxzygw_p`（12/12 替证闭合，公理仅标准三）+ PA19 侧 `JGXZYGW_p19` 同源 shim——**RDWKARC 双臂全通**；余 `UPFZBZM_concl` 一枚接口 sorry（上游四巨物 = 波 2/3，见 `docs/scouts/upfzbzm-scout.md`）+ PA1 骨架存废/saturated 重名 merge 裁决（scout §5） |
| ~~`UPFZBZM_concl` 架构半边~~ | PA19 | PackingConcl:510 discharge 已接线 | **波 1 已真化 (2026-09-29，`abfd2fcb`)**：`NEGLIGIBLE_FUNC` 忠实架构（侦察 f8c207a7 规格书；零新增 sorry）；capstone/FCC 半边/数值链原已全真证。余上游四巨物（KIZHLTL1/2/4 + SUM_GAMMAX，HL ~2400 行，均已预接线）= 波 2/3；Pack2.hl 测度桥四件套是波 2 唯一未知量，见 `docs/scouts/upfzbzm-scout.md`。**波 2A 已真化 (2026-09-29，`dfa60295`)**：PA15 有限性包三件——`HD_IN_MCELL` 真证全净（四 case 路线入 playbook §5.4）、`FINITE_MCELL_SET_lemma1`/`FINITE_MCELL_SET_LEMMA` 真证（唯一染色 = PA12 `VORONOI_LIST_3_SINGLETON_EXPLICIT`，GIANT 落地即自动转净；net −3：26→23）；新私件 `p15_omega_dist_hd` 是 MCELL_SUBSET_BALL_4 的 i∈{0,1} 支钥匙（i=2 唯一卡点，地图入 playbook §5.4）。**波 2B/2C 已真化 (2026-09-30，`9bc5b5bd`)**：PA16 `KIZHLTL1`/`KIZHLTL2` 双闭合（sorry 9→4 零新增），`PackingConcl.KIZHLTL1/2_concl_discharged` 自动真化。**波 3 已真化 (2026-09-30，`c41bccd9`)**：`KIZHLTL4` 闭合（4→3，HL 五步直译，2π 步经 PA2 `GRUTOTI1_concl` 设计接口，PA23 落地时 `exact` 自动放电）；**PA19 上游四巨物已全部实化 (2026-09-30，`78abe340`+`b419ddd3`：SUM_GAMMAX 波1 两同形主件+主装配 10 步闭合，目标 sorry→`exact p18_sum_gammax_main`，施工图 `docs/handoffs/sum-gammax-handoff.md`)**——NEGLIGIBLE_FUNC 全链仅剩 GRUTOTI 系（GT 链）；PA16 余 3（KIZHLTL3 无 HL 证明冻结桩等裁决、QZYZMJC/MCELL_SET_NOT_EMPTY 既有 GIANT） |
| `MHFTTZN_lemma2` | PA6 | MHFTTZN1/2/3/4 + BARV_AFFINE_INDEPENDENT 链 | **已真化 (2026-09-29，`eafa4874`)**：MHFTTZN 全链（lemma/lemma2/1/2/3/4）`#print axioms` 仅标准三零 sorryAx |
| `facet_rep_in_facet` | PA22 | planar 面-表示链 | **已真化 (2026-09-29，`3538883a`)**。**wave-3 已落账 (2026-09-29，`e4248c02`)**：EXPLICIT ℂ kit 19 件（Polytope.lean 模板逐段镜像，公开 `facetOfCPolyhedronExplicit`/`p22_facetOfCPolyhedron` 公理全净）+ 连清 9 枚（`POLYHEDRON_MEMBER`/`facet_rep_refl`/`facet_rep_in_poly`/`facet_rep_a_uniq`/`facet_arg_lt_pi`/`poly_sort_antisym`/`POLY_SORT_LEMMA`/`POLY_SORT`/`POLY_SORT_BIJ`）——sorry 52→43 零新增。**eus1 已收口 (2026-09-29，`87a39f04`)**：同文件序手术（facet_rep 块移至 kit 后）+ 65 行真证（â=‖a‖⁻¹•a 换元 + 球点 mid-point 上确界）——**facet_rep 全族零 sorry 闭合链形成**（`p22_facetOfCPolyhedron`→`eus1`→`facetRepPair`/`spec`/`a`/`b`/`props`/`uniq_c`→`in_facet`/`refl`→`POLYHEDRON_MEMBER`→`facet_rep_in_poly`，:1499→:1794），9 枚继承件全部脱 sorryAx。余 42 枚全在 :2000 行后 GIANT 区（insert_v/bisector_point_exists/POLYSORT_BIJ2/EUSOTYP_simple、GOTCJAH、POLYHEDRON_FACET_SUM_4Pi、XULJEPR；面族计数 4744-5630 是大头）、pad2d3d_facet（ℂ 侧 kit 已就位，还需 V3 侧镜像 kit + FACET_OF_LINEAR_IMAGE ℂ 版） |
| `TSKAJXY` 0/3/4 臂（现 :2550） | PA21 | PA25:3704 `exact TSKAJXY …` 唯一消费 | **四波全落账 (2026-09-29)**：波 0 银行（`2f2c431c`）+ 波 1 GRKIBMP（`1591e1c1`）+ 波 2a kit（`3f162f06`）+ 波 2b cell3_from_ineq_thm（`eedb36b6`）+ 波 3 臂收口（`ba88d11e`，编排者三行机械）——**capstone `TSKAJXY` 装配已真**。**A1+B1 已全清 (2026-09-30，`af3f31fc`)**：A1 几何 5 件 + B1 记账 9 件（含补缺 MCELL2_HL_LT_SQRT2 移植、FRUSTT_RCONE_GE 锥面测度零经保测投影+addHaar_sphere）。**A2 已落账 (2026-09-30，`52a01dfd`)**：5/6 闭合——`OMEGA_LIST_BISECTOR`（塔点等距 kit 绕开 PA5/PA6 sorry 污染）+ `MCELL1_RADIAL`/`MCELL1_VOL`/`GAMMAX_MCELL1`/`TSKAJXY_1`（capstone：gammaX = sol·(√2³/3−2mm1/π)，括号正由 PA20 种子 `HJKDESR1a_1cell`）。**SOL_RESTRICT+B2 已落账 (2026-09-30，`b9bf1114`)**：文件序收口（1060 行区块整体上提，零重复）+ B2 四枚闭合（FRUSTT_WEDGE_RCONE_GE 消费 PA18 正本/NOT_COPLANAR_EXTREME_MCELL2/MCELL2_DIHV_AZIM/MCELL2_DIHV_LT_PI——dihV=π⇒Gram −1⇒反平行 ~160 行代数——四枚公理全净）。**B3 已落账 (2026-09-30，`9a6d1198`)**：三枚真证装配——
GAMMAX_MCELL2（VX_PROPS 钉死+epsilon 对求值+PA15.DIHX_SYM swap 支）/
MCELL2_VOL（SPLIT 双半+DIHV_SYM 翻轴）/TSKAJXY_2（null 支 GAMMAX_NULLSET+
dist_ge_two 账），sorry 11→8 零新增。**GAMMAX_GAMMA2_X 已闭合 (2026-09-30，`9b0670ff`：LA38 公开 wrapper 经 LocalAuto38Bridge.lean(rho 撞名→_B 后缀)+SF 项 19 执行版 DEDUP：PA21 两枚同名 sorried 孪生删除，接口由 PA14 正本(经 PA17)承担)**——余 5：SPLIT_EXPLICIT/MCELL2_SOL（楔形闭式 GIANT 工位，PA21 已空闲）+ TSKAJXY_034/mi_gamma3f/pack_nonlinear_rest（界外挂账） |
| `LEMMA_3_POINTS_FINAL`/`LEMMA_4_POINTS_FINAL` | ContraFan | contraveningFan → CKQOWSA | **CF-3 已真化（路线 B，前波）；CF-4a 已落账 (2026-09-29，`f25bcc49`)**：新模块 `ContraFanDeep.lean` 1070 行（不 import ContraFan——接线方向相反，twin 自拷前奏含 CF-3 L3F 孪生）；件 1 `cf4_cone_inter_imp_segment_conv` + 件 2 **分离平面四点件** `cf4_separation_plane_4_points`（±(v2×₃v4) 平面 + Cramer 符号四分，辅助链 ~350 行零 sorry）真证；9 枚带账 NEEDS（rotation 三件/连续性大件 665 行/circumcenter 两枚/段交两枚）全附 HOL 锚点。**CF-4b 已落账 (2026-09-29，`dd20ae50`)**：5 件闭合（rotation_dist_decrease/circumcenter 两枚/aff_ge_inter_segments/rotation_lemma，公理全净），sorry 9→4。**CF-4c 已落账 (2026-09-30，`d544b010`)**：再三件闭合（family_special——夹逼延拓统一锥表示/continuous_intersection_point——Cramer+Gram 行列式/rotation_about_axis——正交分解平移）。**CF-4d 已落账 (2026-09-30，`1355f2bc`)——主石完整闭合，ContraFanDeep 全模块 sorry 归零（2602 行零 sorry）**：665 行连续性大件按 HOL 逐段落地（w·n 三分类 + IVT 首穿双件 `cf4_ivt_first_hit/dec`（sInf+IsClosed.isLeast_csInf）+ Cramer 穿锥判别两件），6 私件全净、主石陈述 byte-identical。**ContraFan 链移植完成**（CF-3 路线 B + CF-4a/b/c/d 四波）；IVT/滤波类 Mathlib 替代路径沉淀入 playbook §5.3 |
| LA38 `tau3_taum_d`/`tau3_taum_dfun` | LocalAuto38 | （经 main_nonlinear_terminal_v11 合取项间接）| 陈述级：缺 `2 ≤ dist` 下界，待对照 HOL 补陈（走 STATEMENT-FIX） |

## C. 接口填实的下游依赖（未来在账，先遣情报）

- tame 文字章 64 个 .hl/4.6MB（A7-A9）：侦察情报见 playbook §5（GLTVHUM 五级链、
  DUUNHOR 三共享缺件）；`hypermapOfList` 构造（P6-C 遗留）是 A9 前置。
- **GLTVHUM 五级链进展 (2026-09-30，`2c71cde2`+`3a30af3e`)**：①②③④ 已闭合
  （④ `GLTVHUM_lemma1` 落地：base/step 全按 NEEDS 路线 + 4 私件全真证；
  ③绕开未移植 POLYTOPE_UNION_CONVEX_HULL_FACETS 走紧 polyhedron 边界点引理）。
  **⑤ 预研修正（`3a30af3e` 报告）**：链复制实际只需 `p6_sUnion_image_congr`
  （10 行）+ 新证 rogers-窗引理一枚（HOL Rogers.hl:1170-1225 原型），公开件
  （lemma1/BARV_0/VORONOI_LIST_SING/AFF_DIM_VORONOI_LIST 等）PA2 侧零复制
  直接消费；`PackingConcl.GLTVHUM_concl_discharged` 桥已路由 PA6.GLTVHUM，
  PA2 侧闭合即全线解锁——**架构裁决可倾向 (a) 链复制**（成本已大降）；
  PA4 cellParams 9 枚族与 DUUNHOR（三前件均 sorry）等 ⑤。
- **新增在账（wave3 侦察）**：PA22 cone0P22=affGe 弱编码族 5 枚 + PA7 permutes 弱
  编码族（KSOQKWL 等）——提案 r2 已出补丁（11/14/15/DUUNHOR），结构性立项
  "planar 编码定义纠正"待用户拍板。
- **wave3 附带解锁**：PA7 `BARV_CIRCUMCENTER_EXISTS` 成真（PA18 cc 簇钥匙）。
- **GRUTOTI 侦察结案 (2026-09-29，`docs/scouts/grutoti-scout.md`)**：非从零移植——PA23
  骨架 + capstone 组装已在树（9 机械件已证 + 5 枚 giant sorry，全树零 importer）；
  实际量级 Lean 2800–5000 行（region/cell_vol 双 GIANT）。三座共享银行：
  锥帽体积套件（**源不在本仓**，与 REUHADY(PA24)/TSKAJXY3 三链共享，GT-1 先导波
  建新模块 ConicCapVolume.lean）、Pack2.hl 测度桥（与 UPFZBZM wave-2/KIZHLTL1 共享，
  **已实化**：KIZHLTL1/2 `9bc5b5bd`）、PA15 marchal3 套件 ≥9 枚。
  **GT-1 已落账 (2026-09-30，`0d3243c0`) + 收口 (2026-09-30，`107e0a04`)**：
  `ConicCapVolume.lean` 1610 行——`volumeConicCap`（2/3·π·(1−a)·r³ 完整推导）
  +Pos/Measurable/Bounded 四公开件公理全净，纯 Geom.* 零 sorry 依赖；
  **本模块 sorry 3→0 全绿**（sliceWedge 任意 t 版+临界半径分支/楔体积核/
  AZIM_EQ_0_PI 桥全真）；stretch=PA24:428 REUHADY 对接三公开件
  （measurable/volumeFormula/volumeConicCapWedge）——PA24 wedgeGe shim 只差
  闭开楔零测差集一步；余 GT-1 尾巴（HOL :6511 全量 a<0 反射+STRONG convex
  分量）文件头记账。
  **GT-2 前段已落账 (2026-09-30，`dfd748ed`+`d67e5fcf`)**：PA15 ★×2 转真
  （FINITE_EDGE_X2/MCELL_SUBSET_BALL8_1——**i=2 深坑正面攻下**：mutual-rconeGe
  代数相加，23→21）；PA23 p23_ kit ×4（Pack2 测度桥有限版银行化）。
  **陈述缺陷发现 ×3**：①volD_pos 缺 `hne`（STATEMENT-FIX 提案项 18 已立案
  `1137ad92`，patch 可贴性实测 0 error，**待用户裁决**）；②sum_volD 缺
  Packing/saturated 前提；③pivot 缺 region 覆盖假设——②③登记未立项，等
  grutoti_region 落地后补前提走同一流程。GT-3 剩余关键路径：CONIC_CAP trio
  (PA15:818-828)/grutoti_region(giant)/AJRIPQN。**GT-3a 已落账 (2026-09-30，
  `883e02dc`)**：路线升级——affine-box 替代楔体积（省 ~600 行、免 GT-1 依赖），
  19 枚真证私件铺完（共面桥/线性无关/平分线 Kit）；CONIC_CAP 三件降格为
  **`p15_box_pos` 一引理 + 三段短装配**（续图 /tmp/gt3a_probeD.lean，Kit D
  探针仅余 ~8 小错）；`p15_copl_of_azim_zero`（azim=0 半件）可回灌
  ConicCapVolume 的 AZIM_EQ_0_PI 桥。
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


## 2026-10-12 增量节（三件真数学日 + C1 立项日 + salvage 压力测试日）

**三件真数学全部清账**（milestones-and-risks-2026-10-12.md §0 用户令）：
- **GRKIBMP 组**（侦察 d1ef3913 勘误：'GRKIBMB'系拼写讹误，实体=A/B V2 两条 bank，
  尖锐真相=单变量函数角点 y=√8 真下确界=0 不可分离——手证恰绕开区间求解器）：
  B V2 手证 `06aaf94e`（四段：剥壳/确定性因式分解/单调/数值收口 + G1 种子
  mm1<4/3 半角双角法）→ A V2 手证 `bb1d4923`（h0cut 三分 + delicate 近消支
  三倍角种子 arccos(1/3)≤1231/1000 + mm1 双侧围闭 [5023/5000,507/500]）→
  nliGrkBank 一行装配 `3fa2eb85`。residue16 销账 2/16，81 条记账"1c 两条"清零。
- **PA24 B2 支**：泛具支 `8c8ce8f5`（p24_caseB2_general ~250 行，wg·h>0 直接给
  线性无关免外心参数）+ 退化支换叶 `fdfae86d`（p24_nondeg_leaf_exists 支撑面
  引理等效路线 ~230 行：叶集有限+bisector 方向子模+逃逸方向+fan 分解逼叶）——
  capstone `p24_exists_mcell_not_flat` 本体全真证，PA24 仅剩 :1096 REUHADY1
  外部锚一枚。
- **AJRIPQN**（pivot 侦察 52f52713 勘误：pivot 反向 k=3/4 早已闭合 GT-6，
  AJRIPQN 顶替入列）：五阶段覆盖装配 salvage `cc84d423` + 续二验证/隔离
  `de843eb9`（p17_ajripqn_of_tailfix 单假设定理）→ SF-38 应用后一行闭合
  `4e3450cb`（**零 sorryAx**）。GT 区 axiom 面最后一块具名 taint 源头闭合，
  PA23 p23_cover_C 21 处消费点自动受益。

**SF 账**：决策备忘录六件终账（17/1/15/18/21 五件"已落地销账"——提案状态行
滞后致误判的教训在案 + 22 方向批挂起）；项 37 起草 `c80f6456` + 应用 `9f916218`
（MXI_EXISTS_concl 补 hl(trunc 2)<√2，六文件，pack_concl 接口版假陈述纠正）；
项 38 起草+应用 `3eab5066`/`0c0a2d91`（QZKSYKG2 补尾固定，weak permutes 族
第 N 例）。用户双批一次性兑现。

**C1/A12 线**：侦察 `22c39ef9`（形态重估：非从零移植而是四缺口收尾；Flyspeck
二进制证书 404MB 在库）→ C1a LPSchema `0e788792`（钉定=类型索引位，错 id
发射点即编译错）→ C1b LPSchemaFarkas `393d0421`（精确整数 Farkas checker
+soundness）→ DEF-FIX `e8a7fa8e`（LpTerminalInfeasibleCertified 占位退役，
LPFarkas 内核下沉）→ 余 C1c 三试点。**A12 从"硬件+数据+移植"三重绑定降为
纯数据绑定**。

**脊柱与 PA 系**：A2 contraveningNegative 收口（kit `409c054c` + salvage 修复
`f84b4a19`，Assembly 49→22，azimSpecNeg=AZIM_NEG AzimSpec 级正本；重大勘误：
AZIM_NEG 是末两参换位形非 2π−azim，镜像链大幅简化；公理面唯一来路=
ContraFan.lean:605 路线 B 孪生件）；PA7 XNHPWAB1 波 `ecf8ef0c` + r3
SEPARATES 链收官 `cd0627b1`（19→13，全树首个 V3 点积 Finset-和运输 kit）；
PA25 mcell3 gammaX 波 `c4593766`（141→133）+ S_LEAF_IN_WEDGE_GE 续作
`52e28639`（127，azim 链算术工位定型）。

**TameSpine B1**：批 4-8 五批连落（`2749df2a`/`c86eb1d8`/`3f9e204e`/`f9a0b6ad`/
`86f20731`）≈ 3,600 行 / 120+ 件零 sorry，tame_list.hl :2936-5579；node 显式
刻画链拆除（批 7 第三条直构路线）；旗塔 final_list 合取块上游打通（批 8
FinalDartListSpine）；批 9 在飞（:5580 起）。

**闸演进**：EV22（DF_ANCHORS 环境可覆盖）+ EV23（DEF-FIX 路径 $cmt 兜底）
`62e59aa8`；EV24（bullet 前缀 · sorry 识别，八处模式点）`fc09311f`。

**事故与教训**：5h 配额帽一波带走五线（salvage 协议全胜：PA17/PA24 两绿走闸
`cc84d423`/`83e7a3c9`、Assembly 烂尾留盘续修、TameList8 传染 blocked 实录；
LA5 /tmp 黄金遗产回收式再验证）；1302 限流同秒双杀（并发管控阈值制度）；管道
退出码陷阱（$? 取 tail 的假绿探针）；staged 误卷两犯（路径限定 commit 强制化）；
Phase4 收敛风险单列 ①b + Phase4 常驻车道设立（用户指令二 `b3a846cc`，
TADIAMB 实证 251,054 叶 101.2s 全闭——Taylor 线在该族 100% 可验证）。


## 2026-10-12/13 续节（选项 1 主目标日 + root runner 开跑日；承上节）

**脊柱接口**：A5 hypermapOfFanNeg 收口 `8b8b079b`（azimPredLe descent+σ/inv1 共轭
16 件套，绕开 Localization 群论；textCapstone 镜像分支 sorryAx 断绝）→ **A4
kcImpTheKc 收口 `474b1ced`**（CPNKNXN Zorn + FLYSPECK_DEVOLUTION 测度计数；忠实性
注记：HOL saturated 前提证明不消费已按实去除）；A6 柱① scriptL_attains_max
`9fbd803a`（不需要 ℝ^150 路线实战验证）+ 柱②钥匙件 notSurroundedImpOnOneSideOfPlane
salvage `0ab0bc73`——**A 表 12 枚占位已清 5 枚（A1/A2/A3/A4/A5），剩 A6（柱②③）
A7/A8/A9（tame GIANT）A10（arc kit 在飞）A11/A12（数据）**。elllnyz（A7 前置 B-D1）
收口 `3b3f0dfb`（proper/improper 双支同构机器替代 HOL CONG 字面等式路线；TameLp
import 裁决落地+实例盾先例）。

**三件真数学**：GRKIBMP 组全套闭合（B V2 手证 `06aaf94e` + A V2 手证 `bb1d4923`
+ nliGrkBank 装配 `3fa2eb85`；residue16 销账 2/16）；SF-37/38 应用 `9f916218`/
`0c0a2d91`（MXI_EXISTS_concl 补 trunc-hl 前提六文件 + QZKSYKG2 补尾固定）。

**PA 系**：PA7 两波 `ecf8ef0c`+`cd0627b1`（XNHPWAB1/4+WAUFCHE2+SEPARATES 链，
22→13，V3 点积 Finset-kit 全树首件）；PA25 两波 `c4593766`+`52e28639`（141→127，
azim 链算术工位定型）；PA15 salvage `4333159b`（taint #2/#3 出清，18→16）；
P-A 部分落地 `5caa4492`（docstring 诚实化，改指缓办待 EV25 稳定化）；A10
groundwork `6525b5e4`（CRTTXAT_lemma1/HRXEFDM_lemma1 真证+arc kit 五步路线，
帽石卡前置章诚实分波）；elllnyz 见上。

**TameSpine B1**：批 4-9 五批连落（`2749df2a`/`c86eb1d8`/`3f9e204e`/`f9a0b6ad`/
`d1aeffb3`）≈ 4,700 行 / 190+ 件零 sorry，tame_list.hl :2936-5579 全落账；node
链与旗塔 final_list 上游打通（批 7/8）；批 9 遭限额阵亡后续二线修伤 11 处+续批。

**C1/A12**：C1c 试点 `f94d2d69`（**编译区间钉窄 [30,650]→[34,61] s/条，650 上端
证伪=旧机双重产物；数据波真瓶颈=编译非 G5/G6**——风险表 ② 已改写 `8c8266a0`）；
C1d 工具链 `4b639ad2`（四缺口全闭）→ **root 区预灌装 runner 开跑**（运行态入档
bed9359e：PID 50866 脱离进程 2-worker，19,237 条 ~138-184 条/时 ETA ~4-5.7 天，
首段 18/18+试点 A sha256 对账）；C1.5 G6 gen_branch.py `67f09d94`（全 10 型，
quad×5+hard 117/117 零发散端到端）。

**闸演进**：EV24（bullet sorry 识别）`fc09311f`；EV25 首试未果已还原（改指豁免
缓办，P-A 残留文档债 4 处记账 `5caa4492`）。

**事故**：5h 配额帽两次（第一次五线阵亡 salvage 全胜 `cc84d423`/`83e7a3c9`；
第二次四线阵亡——PA15 前任自愈遗产审计落库、TameList9 续二修伤 11 处、
Assembly 零遗产重发）+ 周/月配额帽（1310，三线阵亡：A6 柱②钥匙件 salvage
`0ab0bc73`、TameList10 未写、W3 在 /tmp）——**周帽重置后按队列续波**。

## 2026-10-15 增量节三（mega 八线全收日：楔形证书面清零 / nli 接线地基 / SF-40 / W7 内核武器；环境事故+负载治理日）

**结构性突破（按 reachable 口径）**：
- **楔形证书面（textCapstone packing 支的 mcell4 环节）阻塞面清零**：CFFONNL
  十槽装配真证（内部余 pa18_ccCell_swap/ZWVCBMN 两笔已记账）→ 当日连续收割
  MCELL4_LEAF_S_LEAF + MCELL4_DOMAIN + GDRQXLGv3 → S_LEAF_CARD2 / LEAF_DOMAIN /
  LEAF_RANK_ONTO 全链解锁。剩余总闸 = PA18 edge-rigidity GIANT kit
  （MCELL4_EDGE_FIRST/STEM_EDGEX，leaf_cell.hl:3281-3432）——落地后
  cc_4_cc_ke4→cc_4_UL→CC_4_PROPS→real_model_azim_c4 一整片批量装配。
- **nli 28+127 接线波地基全就绪**：PA21 bank 具名投影 62/62（禁止裸位置链
  章程 §6.5 清账）→ Assembly nliPackNonlinearRest 62/62 展开（3 条真闭合：
  rest 2/4/60，59 具名骨架待 G4 证书发射+§2a 查表粘合）+ 13 枚裸链位投影
  （六分接口 ×6 + Contravening ×7，消费点改写留待语句冻结面解除波）。
- **merge-ineq 通道清偿**：lindihpi/dih_gt_pi2/gamma3_x_gamma3f 四件 +
  LA11 同根十件（SF-40 def 纠正后全转真）；PA25 MERGED 双件转真；
  TEWNSCJ_MERGED 唯余 PA3 opaque 常数桥（a_spine5/b_spine5 ↔ 数值体，
  Flyspeck_constants 级，待 SF 立项）——桥落十行机械收口。
- **mono 路线 A 双级推进**：W6a Python 原型 13/13 盒实证翻 POS（锚未达，
  根因=df-enclosure 16× 污染 → 先紧 enclosure：W6b 方案 A √ mantissa 填充
  待拍板）→ W7 Lean 内核侧全链（evalReal_deriv + checkMonoCorner 全 decide
  总装 + --mono-lean 重放发射），单盒端到端绿；W8 批量化（sqrt re-bake/
  分树/flat 维）。
- **B1 链**：批 15（Hypermap_iso 桥章）+批 16（quotient_list 章）→ HOL
  :9903+收束件；批 17 起点 :10100，前置 = transform 定义层（tame_defs2.hl
  :435-472）随旗塔波进场。

**账**：DEBT 44,646→44,674（nli 59 具名骨架细粒度记账债压过填实净额；
PA25 −22/PA18 −22/LA11 −10/Assembly +58）。SF-40 应用（用户批准）。
C1.7 长尾自治（A 54 绿/12 非 ok @B067；B 38 绿/4 非 ok @B039）。

## 2026-10-13 增量节二（三线全收日：TameSpine 三连批 / A10 帽石 / G5 收官 / W3 四工位；用户令收波停等）

承上节（`fcd80a84` 后计九笔 + root runner 长跑账）。

**TameSpine B1 三连批（:5580→:8920，累计 +2,232 行 / 94 件全真证零 sorry）**：
批 10 `1baa5d6d`（TameList10 1,129 行 42 件——**前任限额阵亡完整草稿的端到端独立
机械验收后零编辑采用**，salvage 验收模式再验证；tame_list.hl :6607-7514 全落账）；
批 11 `93181878`（TameList11 473 行 24 件——原子理论章全量 :7515-8043，atomListBij
BijOn 三段帽石；TameLp 首次反向消费四件）；批 12 `50b35415`（TameList12 630 行
28 件——MEM_EXTENSION→min_num 块 :8365-8920，lQSpine 证明参折算诚实记账）。
**B1 链 :23-8920 无缺口**；批 13 起点 = HOL :8921 `contour_list_cons` 旗塔章
（ContourListSpine 载体批 8 已备，差件批 12 已就位）。

**脊柱波（A6/A10/A4 线）**：A10 第二波 `a54ebb61`（TameLp +998——**CRTTXAT
帽石装配完成 = B6 出口件一号全清**，mqmsmab 章 CRTTXAT 消费点解锁；arc kit
五件套全零 sorry；方法论突破 `face_sum_snd_eq_fst`：HOL SUM_ORBIT 轨道周期性
全树未移植，改走鸽笼原理 faceMap 有限轨道单射自映射+Finset.sum_bij 整体重排；
TameLp 7→6）；A6 续四 `daa89ba9`（柱② 三件中等档收口，**柱② 仅剩归一化本体
一件**，Lean 路线全文 spec 已入 NEEDS——无需 ℝ^150：packingConfig 紧致机器+
字典序极小化 k 步递归+末步扰动矛盾）+ 柱② 钥匙件 salvage `0ab0bc73`。

**Phase 4 决策与实验**：路由表批准 `715addd3`（R1 多项式→TM / R2 ite→BB 切分+
ite-hull2 / R3 sqrt→第三武器 / R4 角点手证）；92 prep 族画像 `7bc4cbb7`（812 记录
五桶分布，**94.3% 可用已实证武器立即灌装**；真判别式=δ 过零病灶，已二次标注）；
W3 四工位 `aaae330c`（①rung/gran 阶梯三轴扫尽判负+**根因钉死：guard-straddle
系证书结构缺口非精度缺口**，C 侧 --gsplit2 子盒不进证书→镜面重放结构性不可能；
修复路线量化=guard 引导二分 13 子盒/12 定号+1 残差；②disj 主体解耦 stage-A/B
端到端首次全绿+emit_lean.py maxHeartbeats 必要修；③decide 成本 122.7 s/叶实测
→3,626 叶批量真瓶颈=kernel decide，W4 立项 decide 成本工程；④formal_ineqs
sqrt/atn/monotonicity 三板斧考古——monotonicity 降维是我方全缺的免费武器）。
**diagSB 事件**（编排者代收附记）：13 子盒解释跑=孤儿进程（PPID→1）3h 零落盘，
用户令杀；重编译跑复核=直接 decide 结构性不可能（Nat.sqrt 不 kernel-reduce，
探针=证书发现层）→ 正规路线 `--hull` 两段式 ≈4-8h 与 W4 镜像 gsplit 实施本是一事。

**C1/A12 线**：**C1.6 G5 收官 `1f3da927`**（gen_farkas.py 1035 行纯 stdlib——
189 条 infeasible 记录的真实 FarkasCore 导出层，**试点 B 端到端 Lean 机器验证绿**
farkasCheck=true 公理=[propext]，189/189 精确预检全过，93 族零 UNKNOWN；
头号发现=nodes 去重保末次出现 C# 语义；C1c 试点 B 等的"真实叶不闭合"缺口关闭；
C1.7 批量发射处方已给——p3 规模数分钟/条，最大 327×230 decide >40 分钟需排产）。
root runner 长跑：**2,170/19,237 pass 100% @174.9/h，ETA ≈ 3.9 天**（脱离进程
不受本波停令影响，继续跑）。

**新故障模式入册**：①agent 阵亡后 `lake env lean --run` 子进程孤儿化（PPID→1）
继续烧核——杀前查进程树；②`lean --run` 解释模式跑重计算=小时级 + stdout 块
缓冲零落盘假死象——重计算实验须走编译/原生路径，探针输出须行刷；③探针层
（Nat.sqrt 现算证书）与内核层（消费 baked 证书）的分层纪律——decide 只吃后者。

**本波收官状态**：用户令"本批 sub agents 结束后不再启动新线"，三线全收
（批 12 `50b35415` / G5 `1f3da927` / W3 `aaae330c`），编排者停等新指令。

**C1.7 终章（2026-10-17）**：189/189 全绿入库 `7ba6b5b7`——G5 收官处方经
三段执行落地。①**列主序手术**（`f75c305d` LPFarkas.lean §3 纯追加+gen_farkas
`--col-major`）：行主序 coreColSum 每列重走全行+行内 `r.getD i` 位置游走
（B087 ≈2×10⁹ 链表访问→物理足迹 65.8GB>36GB RAM+30GB swap，6h 攒 65min
CPU 不可完成；B086 同病 14 亿次侥幸 4h22m）；列主序单列一趟乘加后 **B086
4h22m→7m45s（33.8×）、B087 9m10s**，axioms 均干净。②**落地波**：189 闭合
模块 `lean/Kepler/LP/T<id>.lean`（41,440 行）+ 列→行桥 `LPFarkasCM.lean`
（rowsFromCols 转置，纯 List 归纳，不经行主序 decide）+ LPLeafInfeas00 189
叶 sorry→转发（gen_lp_skeleton `--emit-closure` 补 infeas 分支）；
**infeas 段 sorry 清零**，lpAllInfeas00=[propext,Classical.choice,Quot.sound]
三零，LPIds/LPAll/LPFarkas/LPCert 零改动。③**统一终账扫波**：全队列 189 条
列主序重刷 **189/189 全绿零失败**（axioms 全 propext，最慢单条 662.6s≈11min，
双实例并行插曲两行 -15 由另一实例自愈覆盖），ledger 备份 c17_backup/
c17sweep_final/。历史 A/B 切片碎片账（含 t60 重编号）作废，以本扫波为准。
**尾账**：C549 类 TM 舰队重烤波（197 模块/18,477 站点，SF-42 落地后翻假待
重烤）排队；root runner 3,485/8,283 本轮 done（含历史 fail 重试消化中），
144/h，ETA ≈ 34h。

**PA24/B 链 taint 普查（2026-10-17，PA24 B2 车道随件）**：任务书勘误——
`p24_caseB2_branch` 已于 `fdfae86d` 闭合（:1118 判读源自 REUHADY1 docstring
过时段落，本次已诚实化）；PA24 唯一文件级 sorry = **REUHADY1 本体 (d) 二面角
分裂主体**（HL REUHADY.hl 239-8356，8100 行/634 NEW_GOALS）。B 链公理 taint
三根（全在他车道辖域）：**R1** PA11 `LEPJBDJ` k=2/3 bites → PA10 `HDTFNFZ` →
A/B3/B2 全支；**R2** PA2 `XNHPWAB1_concl`(:5408)/`XNHPWAB4_concl`(:5391)
（Rogers omega=外心层 |S|≤3 gap）→ PA7 四件 → B3 aux 与 ω₂ 距离恒等式
（SF37 只修了 MXI_EXISTS_concl 陈述，函数体仍 sorry @PA2:5494）；**R3**
REUHADY1 (d) ← PA17 `AJRIPQN` ← Rogers 覆盖链（TIWWFYQ→SLTSTLO1/2+DDZUPHJ→
RVFXZBU）。接续处方：闭 R1/R2 后 PA24 侧零编辑真化（mxi 私证 ~90 行处方在
案）；REUHADY1 (d) 依赖序 = Rogers 覆盖链 → AJRIPQN 五阶段 → HL 400-8356
移植（消费 PA24 在飞 kit）。

## 2026-10-20 增量节（tame_list 收官日 + p24 直 sorry 2→1 日 + 发车冻结→三发批准）

**账本**：DEBT 44,481→**44,478**（−3 逐笔对账：PA2 shim 退役 −2 `a5960367`、PA24
直 sorry 2→1 `80b4554d`）；可比口径（扣 LP 叶户 43,078）**1,400**。spine 探针
（`--with-spine`）本次未跑——机器 12 核/36G，舰队 shard+runner+euler 已占 16G，
root 全构建的内存窗口不够；**周四 root runner 收完的安静窗口补跑**，届时主定理
可达债务面以该次为准。

**本日落地与可达性影响**：
- **B1 全清**：批 59 `f0361c78` tame_list.hl :23-:14428 零缺口、649 主定理零
  sorryAx。tame 章地基层就位，W2（B3 D 链）可开。
- **R2 taint 根（PA2 shim 层）退役**：`XNHPWAB1_concl`/`XNHPWAB4_concl` 删除
  （PA7 本体真证早已入库，shim 删除 = 环境清理，零可达性损失）；`MXI_EXISTS_concl`
  残余消费者 = PA11 `mxiExplicit`（成环未解，记账保留）。
- **REUHADY1 (d) 主体真化**：SF-44+45 应用 + cover_strong 四件 + :3625 gated
  换接（`80b4554d`，STATEMENT-FIX 闸，全量波差 `44b-…fullwave.patch`）。REUHADY1
  的 sorryAx 来源收窄为两条：**scaffold 3 `p24_cap_wedge_cover`**（:3366，走廊/
  侧指认主体，PA24 唯一直 sorry）+ **R3 AJRIPQN inherited**（`p24_wedge_witness_of_
  trace` 携，PA17 GIANT）。10-17 普查的 R1（LEPJBDJ→HDTFNFZ）仍在 B3 支。
- **cleanable 排名**：scaffold 3 收口 = REUHADY1→REUHADY_p24→GRUTOTI1→textCapstone
  链上贪心值最高叶（收掉后 REUHADY1 只剩 AJRIPQN 一债主）；其次 AJRIPQN 本体
  （PA17，同时是 capstone 2 号件输入）。

**派工（用户 2026-10-20 批准三发，间隔 15 分钟，③错峰）**：
1. **十二发波**（pa24reuhady）：scaffold 3 残余真证收口——缺口件「叶表 mcell
   非零测性」+ 侧指认 min-max；p4pa24e 车道 730 行 WIP + 12 根因 fixnotes 作底稿；
   随后 GIANT 分期 a) PA10 可测链 → d) AJRIPQN。
2. **TameSpine 批 60**：**B3 D 链入口 = AUQTZYZ.hl（Rxokskc 直接前置，TameList19/25
   已越章预收部分件）→ RXOKSKC.hl（含 A9 接口件 :523）**——按 port-plan §4/§7 关键
   路径 W2 裁定，取代批 59 候选 reduction1.hl（B5，压 Dpzgbyf/Rxokskc/Aq56 三个
   未移植前置，先开必撞墙）。
3. **W8 gen-8**（rung 收尾 + kd 对半产盒器 + `emit_lean --decide-mode=native|kernel`
   开发/收尾双模开关，用户 10-20 提议）——等 TM 舰队 C549Mono shard 排空再发。

**容量纪律（本日实测后立；20:00 修订）**：重 lean 构建同时 ≤3 个 + runner 恒 2；
**Lake 5.0.0 无 `-j`/`--jobs` 旗标（`-j2` 直接 EXIT=1，十二发波首发即踩；`-Kjobs`
静默毒化缓存）——并发控制靠操作性纪律：每 lane 单 build 跨 lane 串行、热缓存、
冷重建只进安静窗口**（HANDOFF §5.5）。PA 级模块 6–8G/个，shard 7G/个，36G 墙。
在飞：euler v22（残错估 8–10）、TM 舰队、root runner 2,750/6,900（周四上午收）。

## 2026-10-21 增量节（移交令日 + 两 salvage 收工 + spine 探针补跑）

**🔴 移交令（用户令）**：Phase 5 → opencode（接管入口
`docs/projects/phase5-opencode-takeover.md`，自足简报）。ZCode 只收工三件；
TameSpine 线自批 67 移交 opencode。

**账本**：DEBT.md 带 spine 探针重生成（`95e6a037`，11:27）——**主定理可达
债务面首次落盘**：sorryAx 3 个冻结接口（nonlinearInequalities /
linearProgrammingResults / textCapstone）+ 624 shard 特许 native_decide
公理（Phase 2 白名单）+ 标准三公理，**异常项无**。总 sorry 44,478 持平
（可比口径 1,400）。

**root runner 终账（ZCode 收工 1/3）**：首批 6,900/6,900 零 fail 收官
（6 天 22 小时，111 条/时均值，results.jsonl 全 exit=0）；spine 探针欠账清。

**TameSpine 批 67 salvage（ZCode 收工 2/3，`73f14f76`）**：配额断线死在
交付前的半成品直验绿——A9 接口链地基批 27 公开件 607 行（bijOn 三件 +
hypermapOfListG 构造四槽 + good_list_nodes 泛型形 + 缺口底座四件重推导），
6 探针标准三内零 sorryAx，闸 PASS @hypermapOfListG。iso 主件 RXOKSKC（:523）
本体诚实分期 = **批 68（opencode 首棒，处方全备）**。

**TM 舰队重烤终验（ZCode 收工 3/3）**：199/199 全绿入库（8922 jobs RC=0，
sorryAx=0）；12 件怪物件（9-24 用户叫停遗留）全程未触碰、grep 0 命中实证；
9 家族公理抽探全标准三零 sorryAx。**关键勘误**：前驱 ledger 170 条
"axioms_sorry" 为 census 失败态工件（翻假叶 decide 失败 → 错误恢复置
sorryAx → `#print axioms` 传递记录），非真债——C549MonoBatch1 census 20 条
↔ 终建 0 条实证。舰队实账：**197 模块翻假重烤收官**（180 green-rebaked +
17 green-noflip），翻假叶重参数化 6,129 叶、证书参数重写 6,128 处、全 1 轮
收敛、零语句改动——**SF-42 翻假使命闭合**。终账 `lane_snapshots/
w8fleet_rebake/FLEET_REBAKE_FINAL.md`（manifest 199 件 md5 + 排除清单）。

**在决项（2026-10-21 晚更新）**：SF-47 已落库（`fcad9e41`）、gen-8 已落库
（`a726fce2`），原"在决"两项结清；最新待令清单见本节末尾。

## 2026-10-21 第二波增量节（用户令 A·B·E 三发）

**A 批 72 落地（`b40aa2dd`）**：DANGEYJ.hl :739-:949 收章——
SPLIT_NORMAL_LIST_CASES + DANGEYJ_concl/DANGEYJ 主定理 + 15 私件；闸
PASS @DANGEYJ；clone 模块 9504 jobs + 主仓 Text roots 8789 jobs；零 sorry、
零 sorryAx（探针 3/3 标准三）；新雷区 #195-#201。**DANGEYJ 章收官**；
批 73 接续点 = PWSSRAT.hl（759 行）:50 min_not_eq_imp_eq。

**B AJRIPQN 侦察（报告 `docs/scouts/ajripqn-scout.md`，落库 `972ac949`）**：
关键勘误——TIWWFYQ（PA5:663）与 SLTSTLO1（PA13:597）已真证，不是债务；
代码可达 direct sorry = **7 根**（SLTSTLO2 / DDZUPHJ / RVFXZBU 仅 i=3 /
QZKSYKG1 / QZKSYKG2 + PA10 隐藏叶 2），全闭包 **15 节点**。最大单件 =
**QZKSYKG2 k=2**（HOL 约 1681 行），不是 SLTSTLO2。架构雷 = S₃ kit 落点
（PA12 imports PA10，反向不可用；建议 PA14 重落 `RVFXZBU_p14` + PA17 的
hRV 一行改接）。贪心首推 **B1 S₃ action kit**（U=4，解锁 RVFXZBU i=3 /
YNHYJIT i=3 / QZKSYKG1 k=3 / QZKSYKG2 k=3）→ B2/B3/B4/B5；备选并行
**B9 PA10 可测链**（独立便宜）+ B6→B7；B8 最后。**前置 = SF-48**
（`LEFT_ACTION_LIST_PROPERTIES` 补 hfix；新件非改冻结陈述；报告里写的
"SF-47" 编号已占用，正确空号为 48）。

**E W8 gen-9（纯 pipeline，快照 `lane_snapshots/w8rung/gen9/`，主仓零改动）**：
wr64 混合配方证伪（>3342s 未出 DOM 行，≥8× keepconst）；叶 hull rung 门槛
夹在 **(64,128]**，keepconst-128 PASS 且 DOM 99/99——**一套 unified 表达式
同时服务两条线**，无需分表达式 Lean 桥；kc128 ≈ kc256（stage-A 426.2 vs
411.2s，decide 178.9 vs 188.4s，DOM 表 0/99 行差；gen-5 的 612.3s 是
load 9-11 虚高 ≈1.49×）。真实 t3 三叶 @kc128 = 604.3 + 209.4 = **813.7s**
（rc=0、0 error、峰值 23.4GB；gen-8 的 1119.1s 含跨波负载，归一化一致，
不宣称加速比）。kd 整合：case 根 d3 8/8 guard-straddle（0 绿、发射后
8/8 probe FAIL）；POS1 根 d2/d3 全 POS（4/4、8/8 绿）；首 screen-pass 深度
POS1=0（根自身可证，细分多余）。成本模型：每叶 ≈210s 烘 + ≈150s decide
≈ **360 CPU-s**；251k 叶 ≈1046 CPU-天串行；并发受内存卡（decide 峰值
17.2-24.2GB）。gen-10 **不改发射器**（md5 不变、gen-5 重放逐字节相同），
最高杠杆 = Lean 侧常数 trans 盒烘进 `TMParams`（潜力 40-80 CPU-s/叶，
251k ≈116-232 CPU-天）+ kd "首个 screen-pass 即停"。

**euler 窄任务 1 收绿**（`v24_finisher_green.lean` md5 `91765d03`，
286 行、0 sorry；真实上下文 `lake env lean` 0 error、326.97s）：根因 =
把 hre/him 的巨型修正多项式重写进 hsqid 导致 simp motive 爆炸（>40min
不返回）；绿版改用零因子小引理保持 P/Q opaque。窄任务 2（master 移植）
处方在 `v24_TASK1_DONE.md`，未发车。

**B1/B2/B9 收口（2026-10-22，AJRIPQN 链三连）**：
- **B1**（`ae475e70`，SF-48）：PA12 新增 `LEFT_ACTION_LIST_PROPERTIES`
  （S₃ action kit），716 行 `p12_` 私件，零 sorryAx；解开 RVFXZBU /
  QZKSYKG1 / QZKSYKG2 的 S₃ 前置。
- **B2**（`51a72e2c`）：PA14 新增 `RVFXZBU_p14`（i=3 用 B1 收口）与
  `ynhyjit_i3_p14`；PA17 `hRV` 改接 PA14 新件。PA10 源 `RVFXZBU` 保留为
  off-path orphan（仍计入 PA10 的 direct sorry，但已不在 AJRIPQN 公理锥）。
- **B9**（`612bea61`）：PA10 三叶 `INTER_RCONE_GE_LE_lemma` /
  `MCELL_2_PROPERTIES_lemma1` / `measurableSet_affGe_wedge_p10` 全证；
  `BOUNDED_MCELL`/`MEASURABLE_MCELL` 探针翻三零。
- **AJRIPQN 剩余债主**：SLTSTLO2、DDZUPHJ、QZKSYKG1/QZKSYKG2；PA10 的
  RVFXZBU i=3 / YNHYJIT i=2/3 是 off-path（YNHYJIT i=2 待 S₂ kit）。
  下一档建议 B3（YIFVQDV_1+QZKSYKG1）与 B6（DDZUPHJ 支撑链），B8 独立最后。
- **W8**：gen-9 的 1046 CPU-天被 HOL 侦察拆解——251k 是 TADIAMB
  （pilot ≈2.5s/叶，7.3 CPU-天串行），重叶成本属 BIX；gen-10 探针
  （库 `pi4D` 盒 + uniform-128）把 BIX 每叶降到 ≈50 CPU-s、RSS 减半，
  完整 opt-in 落地在飞。

**在飞/待令**：gen-10 完整 opt-in 车道在飞（4-6 轮）。待用户令 =
B3/B6/B8 组合 / 批 73 / euler 窄任务 3 / 主定理锥陈述保真+可信基座清点 /
Lean 4.35 / 雷场入 playbook / RVFXZBU2_concl shim 盘点。

## 2026-10-22 信任边界审计（只读，全文 `docs/main-theorem-trust-audit.md`）

**e2e 锥（`Final → Assembly` 的 import 图）**：`Assembly` import
`PackingAuto2/18/21/25`、`LocalAuto16`、`TameLp` 等；`PackingAuto21` import
`PackingAuto17`，`PackingAuto25` 直接引用 `AJRIPQN`（PA25:234/2814/2876/5071）。
故 **AJRIPQN 链的 QZKSYKG2 / SLTSTLO2 / DDZUPHJ / QZKSYKG1 很可能已在主定理
锥内**（声明级 reachability 待核），是直接 e2e 债务削减；QZKSYKG2 k=2 与
SLTSTLO2 两条在飞车道因此是主线工作，不只是旁支。

**不在 e2e 锥（邻近 pack_concl 层）**：`PackingConcl`（7 direct sorry：
MXI_EXISTS/RVFXZBU1/2/3 的 `_discharged` 桥等；全仓零 importer）、
`PackingAuto24` / REUHADY1(d)（仅被 PackingConcl import，Assembly 不 import）。
它们属 pack_concl 合并层，不阻塞当前 e2e；派工时不应再按"主定理可达"优先，
而应按"PackingConcl 接线前置"排序。

**锥外但将来会一次性接入**：43,078 个 LP 叶户——`linearProgrammingResults`
的唯一债点 `lpArchiveCertificatesDebt`（Assembly:6040）目前是单点 sorry，
填实前 43k 不入锥；接线前必须先做 LP 证书端到端审计，否则主定理锥会从
3+624 一次跳到 43k。

**唯一非 sorry 可信计算**：624 条 shard 公理（`goodListArchive`，
19,715 图 / 23 个 `GoodListShard*` 分片，`native_decide` 白名单）；内核不
验证生成器。列为 P0：manifest + 抽样 replay。

**弱形/shim 清单**：`DUUNHOR_concl` 前提加强、`p17_measure_sdiff_ge` 不等式
替身、PA10 `RVFXZBU` off-path、`qzksykg1/2_p17` 副本、`MXI_EXISTS_concl`
成环、`RVFXZBU2/3_concl` shim——逐条"在锥/不在锥/替代路"表已入审计文档
§4。P0 验证动作：声明级 reachability 地图 → 624 manifest+replay →
LP 端到端审计；P1：三接口 HOL 陈述对照；P2：shim 清理批。

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
| ~~`UPFZBZM_concl` 架构半边~~ | PA19 | PackingConcl:510 discharge 已接线 | **波 1 已真化 (2026-09-29，`abfd2fcb`)**：`NEGLIGIBLE_FUNC` 忠实架构（侦察 f8c207a7 规格书；零新增 sorry）；capstone/FCC 半边/数值链原已全真证。余上游四巨物（KIZHLTL1/2/4 + SUM_GAMMAX，HL ~2400 行，均已预接线）= 波 2/3；Pack2.hl 测度桥四件套是波 2 唯一未知量，见 `docs/upfzbzm-scout.md`。**波 2A 已真化 (2026-09-29，`dfa60295`)**：PA15 有限性包三件——`HD_IN_MCELL` 真证全净（四 case 路线入 playbook §5.4）、`FINITE_MCELL_SET_lemma1`/`FINITE_MCELL_SET_LEMMA` 真证（唯一染色 = PA12 `VORONOI_LIST_3_SINGLETON_EXPLICIT`，GIANT 落地即自动转净；net −3：26→23）；新私件 `p15_omega_dist_hd` 是 MCELL_SUBSET_BALL_4 的 i∈{0,1} 支钥匙（i=2 唯一卡点，地图入 playbook §5.4） |
| `MHFTTZN_lemma2` | PA6 | MHFTTZN1/2/3/4 + BARV_AFFINE_INDEPENDENT 链 | **已真化 (2026-09-29，`eafa4874`)**：MHFTTZN 全链（lemma/lemma2/1/2/3/4）`#print axioms` 仅标准三零 sorryAx |
| `facet_rep_in_facet` | PA22 | planar 面-表示链 | **已真化 (2026-09-29，`3538883a`)**；余 `AFF_GT_RELATIVE_INTERIOR`/`CONE0_FCHANGED_AFF_GT` 两枚 NEEDS 已带 6 步路线+API 全名就地注记（波 3 GIANT 直取） |
| `TSKAJXY` 0/3/4 臂（现 :2550） | PA21 | PA25:3704 `exact TSKAJXY …` 唯一消费 | **四波全落账 (2026-09-29)**：波 0 银行（`2f2c431c`）+ 波 1 GRKIBMP（`1591e1c1`）+ 波 2a kit（`3f162f06`）+ 波 2b cell3_from_ineq_thm（`eedb36b6`）+ 波 3 臂收口（`ba88d11e`，编排者三行机械）——**capstone `TSKAJXY` 装配已真**；余上游巨件：`TSKAJXY_034`（:1308，0/3/4 胞内容）、`TSKAJXY_1`/`TSKAJXY_2`（1/2 胞）、`mi_gamma3f_gamma3f_x_div_sqrtdelta`（波 2a NEEDS，sol_x_sol_euler_x 链）、`pack_nonlinear_rest`（G4 挂账） |
| `LEMMA_3_POINTS_FINAL`/`LEMMA_4_POINTS_FINAL` | ContraFan | contraveningFan → CKQOWSA | **CF-3 已真化（路线 B，前波）；CF-4a 已落账 (2026-09-29，`f25bcc49`)**：新模块 `ContraFanDeep.lean` 1070 行（不 import ContraFan——接线方向相反，twin 自拷前奏含 CF-3 L3F 孪生）；件 1 `cf4_cone_inter_imp_segment_conv` + 件 2 **分离平面四点件** `cf4_separation_plane_4_points`（±(v2×₃v4) 平面 + Cramer 符号四分，辅助链 ~350 行零 sorry）真证；9 枚带账 NEEDS（rotation 三件/连续性大件 665 行/circumcenter 两枚/段交两枚）全附 HOL 锚点。余 = CF-4b（交接地图入 playbook §5.4，连续性大件 :2204-2869 单设 checkpoint）+ CF-4c（rotation_about_axis）；见 docs/contrafan-scout.md |
| LA38 `tau3_taum_d`/`tau3_taum_dfun` | LocalAuto38 | （经 main_nonlinear_terminal_v11 合取项间接）| 陈述级：缺 `2 ≤ dist` 下界，待对照 HOL 补陈（走 STATEMENT-FIX） |

## C. 接口填实的下游依赖（未来在账，先遣情报）

- tame 文字章 64 个 .hl/4.6MB（A7-A9）：侦察情报见 playbook §5（GLTVHUM 五级链、
  DUUNHOR 三共享缺件）；`hypermapOfList` 构造（P6-C 遗留）是 A9 前置。
- **新增在账（wave3 侦察）**：PA22 cone0P22=affGe 弱编码族 5 枚 + PA7 permutes 弱
  编码族（KSOQKWL 等）——提案 r2 已出补丁（11/14/15/DUUNHOR），结构性立项
  "planar 编码定义纠正"待用户拍板。
- **wave3 附带解锁**：PA7 `BARV_CIRCUMCENTER_EXISTS` 成真（PA18 cc 簇钥匙）。
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

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
| `TSKAJXY` 0/3/4 臂（:1428） | PA21 | PA25:3704 `exact TSKAJXY …` 唯一消费 | **GIANT**（2026-09-29 侦察结案）：Merge_ineq 通道三重阻断（银行无结构 + GRKIBMP/cell3_from_ineq_thm 未移植 + eta_y body 缺）——**章程已审定** `docs/merge-ineq-channel.md`（三波收口，执行待 owner 批准） |
| `LEMMA_3_POINTS_FINAL`/`LEMMA_4_POINTS_FINAL` | ContraFan | contraveningFan → CKQOWSA | **侦察结案 (2026-09-29)**：CF-3 = L3F 走路线 B（内积角加法+有理余弦界，中等 250-400 行）可先行；CF-4 = L4F 忠实移植 GIANT 2000-3000 行三波（独立模块 ContraFanDeep.lean，依赖 CF-3）；见 docs/contrafan-scout.md |
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

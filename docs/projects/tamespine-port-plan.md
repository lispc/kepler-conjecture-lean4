# tamespine-port-plan — tame 文字章移植立项文件（2026-10-08 只读侦察轮）

> 任务来源：终装配后最大单一工作量——`reference/flyspeck/text_formalization/tame/`
> 文字章（64 个顶层 .hl，3.3MB / 91,841 行 / **2,042 条定理**（实测口径
> `^[[:space:]]*let NAME = (prove|prove_by_refinement)`——注意两类文件风格不同：
> tame_list/reductions/WMLNYMD 系用 `prove_by_refinement` 顶格写，AQ/D 链/more_lemma/
> betwn 系在 module 内缩进且用经典 `prove`，单一模式会漏计一半，AutoPipeline 的
> `^let …= *prove` 探针需扩为两式）；另 ssreflect/ 子目录 6 个 compiled .hl / 1.2MB
> 属 A10/A11 邻接 lane，不在本立项数内，口径勘误同 tame-chapter-scout.md 头注）。
> 对照基准 flyspeck @ `1ce0353`。
> 本文件是 e2e-debt-map.md A 表六枚 tame 系接口（A2/A5/A7/A8/A9/A10）的**章级立项分解**，
> 与 tame-chapter-scout.md（A7/A8/A9 三接口深侦）互补：那份管"接口怎么填"，
> 这份管"64 个 .hl 按什么顺序、拆多少批、每批验收什么"。
> 纪律：只读侦察；lean/ 零触碰；PA23/PA24 并行线在飞（本侦察未读其工作区文件）。

---

## §0 一页结论

- **剩余量级**：~81.7k HOL 行 / **~1,940 条定理**未移植（定理总量 2,042，减已覆盖
  CKQOWSA 系 85 + JGTDEBU 12 + CDTETAT 4 ≈ 101；行数口径：总量 91.8k 减已覆盖 ~8.0k，
  逐簇求和 14,428 + 34,538 + 25,361 + 4,963 + ~2,450）。
  批数估算：行数口径（先例 740–1,030 行/批）**80–110 批**；定理口径（10 定理/批）
  **194 批上限**——tame 定理密度 ~42 行/条，显著高于 conforming（74）与 planarity（103），
  **建议 BATCH_SIZE 提至 15–20** 以对齐 ~1,000 行/批的先例批次体量，对应 **100–130 批**。
  Lean 新增 **~70–100k 行**（1.5x 展开率为先例中位，tame_list/reduction 两块因
  Mathlib/AFP 落点现成而显著低于此）。
- **依赖形状**：四个近似独立的聚类 + 一条公共地基（tame_list）：
  ① Tame_list 地基（14.4k，无内部依赖，最机械）；
  ② LocalFan 结论链（Auqtzyz→Rxokskc→Dangeyj→…→Hojodcm→AQ1-13，~32.1k，线性主链，
  另加 arc_properties/Inequalities/Meeixjo 三叶 ~2.4k）；
  ③ reduction 链（R1→R2→{R3,R4,more_lemma→betwn_core}→R5，~25.4k，含 more_lemma/betwn 反向吃 R2 的岔）；
  ④ correspondence 簇（Oxaxucs/Asfutbf/ELLLNYZ/WMLNYMD/DPZGBYF/tame_opposite，~4.9k）。
- **关键路径** = ①→②→③→A9（jcajydu）。A7（elllnyz）几乎自足可最先离账；
  A8（tameCorrespondenceIso）只压 ④+S11 def 忠实化；A10（mqmsmab）按 mqmsmab-scout
  只剩 CRTTXAT/HRXEFDM 两枚 tame 侧上游（U1/U2 lane，~2.5k HOL）。
- **最大结构风险**：GoodGraphV4/GoodListNodes 五个 True 占位（Assembly §2b）不忠实化则
  A8 不可证、A9 结论空壳（R1 耦合，scout §6-R1）；tame_list 内部与跨文件共 **14 组同名
  重复绑定**（HOL shadowing 语义，Conforming 教训同类）——骨架设计阶段必须逐组裁决。

---

## §1 逐文件盘点总表（64 个 .hl）

图例：状态 ✅=Lean 已有对应模块收官 / 🟡=部分覆盖 / ⬜=未移植。
"批"为 §4 批次表归属。 HOL 行/定理数实测（`wc -l`/`grep '^let … = prove'`）。

### A. 地基层

| 文件 | HOL 行 | 定理 | defs | 依赖（opens/qualified） | 状态 | Lean 落点 |
|---|---|---|---|---|---|---|
| tame_defs.hl | 450 | 0 | 102 | 无 | 🟡 | Assembly §2b（orbitSet 版孪生）+ TameLp §1（Hypermap 版孪生）；`Adm3` 尾 True 占位（Assembly:369） |
| tame_defs2.hl | 797 | 0 | 102 | Tame_defs | 🟡 | `GoodGraphV4` 镜像但五合取 True 占位（Assembly:427-437，S11 缺口） |
| import_tame_classification.hl | 146 | 0 | 32 | 无 | ✅ | Graphs/ AFP 移植（Tame.lean `tame`，module-map.md） |
| tame_concl.hl | 108 | 0 | 0 | 无（concl 术语表） | 🟡 | 各 concl 随消费者逐条镜像（UBHDEUU/HRXEFDM/JGTDEBU 群已随 TameLp/ContraFan 落） |
| more_tame_concl.hl | 742 | 0 | 0 | Hypermap, list_hypermap_iso | 🟡 | LSKOKJE/enum_indexToVertexList 等 concl 术语；DPZGBYF/WMLNYMD/ASFUTBF/OXAXUCS 的公共消费词汇 |
| **tame_list.hl** | **14,428** | **650** | 2 | 无 | ⬜ | **B1 地基批**（S2/S6 件：map_good_list:3403、hypermap_of_list_map:3486、JXBJOAB:3733、GNBEVVU:3540、DAKEFCC:9360） |
| good_list_archive.hl | 112 | 0 | 1 | List_hypermap_computations | ✅ | Assembly/GoodListAll.lean（P6-C，19,715 图） |
| linear_programming_results.hl | 79 | 1 | 2 | Good_list_archive | ✅（结构） | Assembly §2d（LinearProgrammingResults 纯逻辑 + lpArchiveCertificates=A12 数据线） |

### B. LocalFan 结论链（蓝皮书 Local Fan 章遗留结论，~31.9k）

| 文件 | HOL 行 | 定理 | 依赖 | 状态 |
|---|---|---|---|---|
| arc_properties.hl | 1,091 | 20 | 无（叶） | ⬜（CRTTXAT 的弧长支撑） |
| Inequalities.hl | 729 | 26 | 无（叶） | ⬜ |
| AUQTZYZ.hl | 2,624 | 37 | Truong/Hypermap（叶） | ⬜ |
| AUQTZYZ_list.hl | 329 | 1 | Tame_list 等 | ⬜ |
| RXOKSKC.hl | 1,105 | 12 | Auqtzyz, List_hypermap | ⬜（**A9 直接件** RXOKSKC:523） |
| DANGEYJ.hl | 949 | 38 | Rxokskc | ⬜ |
| PWSSRAT.hl | 759 | 31 | Dangeyj | ⬜ |
| OHCGKFU.hl | 327 | 11 | Pwssrat | ⬜ |
| PPLHULJ.hl | 268 | 7 | Ohcgkfu | ⬜ |
| NCVIBWU.hl | 1,496 | 14 | Pplhulj | ⬜ |
| PBFLHET.hl | 956 | 23 | Ncvibwu | ⬜ |
| KBWPBHQ.hl | 2,008 | 36 | Pbflhet, Diowaas, Ryiuuvk | ⬜ |
| HOJODCM.hl | 2,077 | 28 | Kbwpbhq | ⬜（AQ 链入口） |
| LEBHIRJ.hl | 703 | 4 | Kbwpbhq | ⬜ |
| OBDATYB.hl | 195 | 2 | Kbwpbhq | ⬜ |
| DIOWAAS.hl | 220 | 3 | Pbflhet | ⬜ |
| RYIUUVK.hl | 170 | 2 | Diowaas | ⬜ |
| QCDVKEA.hl | 157 | 2 | Pplhulj | ⬜ |
| PNXVWFS.hl | 182 | 3 | Pplhulj | ⬜ |
| AQ1.hl | 2,201 | 43 | Hojodcm 群 | ⬜ |
| AQ23.hl | 669 | 7 | Aq1 | ⬜ |
| AQ4.hl | 2,569 | 29 | Aq23 | ⬜ |
| AQ56.hl | 702 | 4 | Aq4（reduction1 消费 TL_LAST） | ⬜ |
| AQ7.hl | 289 | 4 | Aq4 | ⬜ |
| AQ8.hl | 3,413 | 24 | Aq4 | ⬜ |
| AQ9.hl | 1,594 | 12 | Aq4 | ⬜ |
| AQ10.hl | 206 | 2 | Aq4 | ⬜ |
| AQ11.hl | 277 | 5 | Aq4 | ⬜ |
| AQ12.hl | 4,091 | 68 | Aq8, Meeixjo | ⬜ |
| AQ13.hl | 1,574 | 15 | Aq12, Tame_list | ⬜ |
| MEEIXJO.hl | 608 | 10 | Tame_list（叶） | ⬜（AQ12/reduction1 消费） |

### C. reduction 链（Tame Hypermap 章归约，~25.4k）

| 文件 | HOL 行 | 定理 | 依赖 | 状态 |
|---|---|---|---|---|
| reduction1.hl | 4,976 | 98 | Tame_list, **Dpzgbyf**, Rxokskc, Aq56, Meeixjo | ⬜ |
| reduction2.hl | 1,671 | 53 | R1, Aq12, Aq13, Tame_list | ⬜ |
| reduction3.hl | 5,656 | 147 | R1, R2, Tame_list, More_lemma1/2, Aq12 | ⬜ |
| reduction4.hl | 5,436 | 117 | R3, R2, R1, Aq12, Diowaas, Ryiuuvk | ⬜ |
| more_lemma1.hl | 3,090 | 36 | **R2**, Aq8/Aq12/Aq13, Diowaas | ⬜ |
| more_lemma2.hl | 2,294 | 26 | R2, Aq8/Aq12, More_lemma1 | ⬜ |
| betwn_corek_z_x.hl | 726 | 13 | More_lemma2, R2, Aq12 | ⬜ |
| betwn_core0_z_y.hl | 1,352 | 10 | More_lemma2, R2, Aq12, betwn_corek | ⬜ |
| reduction5.hl | 160 | 4 | R3, R4, Betwn_corek/Betwn_core0 | ⬜（**A9 出口** restricted_hypermaps_are_planegraphs_thm） |

注：more_lemma/betwn_core **反向消费 Reduction2**——R2 必须先于它们，R5 最后。

### D. correspondence 簇（iso 不变 + 镜像 + 对应，~4.9k）

| 文件 | HOL 行 | 定理 | 依赖 | 状态 |
|---|---|---|---|---|
| ELLLNYZ.hl | 590 | 21 | 无 opens（自足叶；证明体引 Tame_list/Asfutbf/Tame_opposite） | ⬜（**A7 本体** ELLLNYZ:548） |
| tame_opposite.hl | 612 | 30 | Hypermap, Tame_defs | ⬜（A7 消费 opposite_components） |
| OXAXUCS.hl | 614 | 27 | More_tame_concl, Tame_list | ⬜（**A8 iso 不变家族全章**，scout S4） |
| ASFUTBF.hl | 1,106 | 45 | More_tame_concl, Tame_opposite | 🟡（六件 negative 私件+isoOppositeEq 已在 Assembly:612-600；余镜像链 :290-699 与 hyp_conj/n_fan_pair/ASFUTBF 主件 :871-1106）（**A2/A5 出口**） |
| WMLNYMD.hl | 1,515 | 56 | Oxaxucs, Asfutbf, Elllnyz, Tame_list | ⬜（**A8 本体** tame_correspondence_iso:1498；floor 权重机制 :844-1359，scout S9） |
| DPZGBYF.hl | 427 | 12 | Oxaxucs, Asfutbf, Elllnyz, Wmlnymd, Tame_list | ⬜（reduction1 的 generatePolygon/planegraph_induct 落点） |
| JCAJYDU.hl | 99 | 2 | Tame_list, Hypermap, Rxokskc, R5 | ⬜（**A9 本体**，99 行全文件即装配） |

### E. fan-几何出口（tame_general 系 + 三枚重几何件，~4.1k）

| 文件 | HOL 行 | 定理 | 依赖 | 状态 |
|---|---|---|---|---|
| tame_general.hl | 782 | 32 | Fan_defs, Hypermap_and_fan, Tame_defs | 🟡（CONTRAVENING_FAN/NODE_TYPE_lemma/FULLY_SURROUNDED…/TRIANGULAR_FACE_AZIM_DART_BOUNDS/contravening_imp_conforming 已随 TameLp/ContraFan 落） |
| JGTDEBU.hl | 256 | 12 | Tame_general 群 | ✅ TameLp §4 全真 |
| CDTETAT.hl | 328 | 4 | Tame_general, Tame_lemmas(ssreflect) | ✅ TameLp §5（含 SZIPOAS） |
| CRTTXAT.hl | 584 | 6 | Tame_general, Arc_properties, Hypermap_and_fan | 🟡 TameLp:1999 sorry（**A10 上游 U1**，HOL 证体 :320-470） |
| HRXEFDM.hl | 284 | 6 | Tame_general, Hypermap_and_fan | ⬜（**A10 上游 U2**：sum_tauVEF_upper_bound 依赖 HRXEFDM_lemma1） |
| FATUGPD.hl | 1,581 | 26 | Planarity, Pack1/2, Trigonometry1（外部） | ⬜（tame_concl FATUGPD_concl 出口；与 PA 侧消费衔接） |
| CKQOWSA.hl | 580 | 14 | CKQOWSA_3/4 | ✅ ContraFan（全真） |
| CKQOWSA_3.hl | 1,450 | 23 | Fan_defs | ✅ ContraFan（LEMMA_3_POINTS_FINAL 路线 B 真化） |
| CKQOWSA_4.hl | 4,272 | 48 | CKQOWSA_3 | ✅ ContraFan+ContraFanDeep（CF-4a/b/c/d 四波收官，2602 行零 sorry） |

**状态小结**：⬜ 未移植 49 文件 ≈ **81.7k 行 / ~1,940 定理**；✅ 收官 9 文件 ≈ 8.0k 行；
🟡 部分 10 文件（ASFUTBF/CRTTXAT/tame_general/tame_defs2 等，余量已计入上方出口需求；
ASFUTBF 的 1,106 行归入 B-D2/B-D4 子集抽取批）。
注：上表"定理"列 = `^[[:space:]]*let NAME = (prove|prove_by_refinement)` 实测；
tame_list 的 650 条为最大单文件定理群，其余文件头部 `let *_concl = \`…\`` 术语项不在定理数内。

---

## §2 依赖拓扑（tame 内部，分层）

实测口径 = 文件头 `open` + 证明体 qualified 引用（`Mod.name`）并集；只列 tame 内部边，
外部依赖见 §5。

```
L0 定义/术语（大多已落）: Tame_defs ✅  Tame_defs2 🟡  Import_tame_classification ✅
                          Tame_concl/More_tame_concl 术语层 🟡
L1 叶（无内部依赖）:      tame_list(14.4k)  arc_properties  Inequalities  ELLLNYZ
                          tame_opposite  Meeixjo  AUQTZYZ(+_list)  Tame_general🟡
L2 主干:                  Rxokskc ← Auqtzyz
                          Dangeyj ← Rxokskc → Pwssrat → Ohcgkfu → Pplhulj
                              → Ncvibwu → Pbflhet → {Kbwpbhq, Diowaas, QCDVKEA, PNXVWFS}
                          Kbwpbhq → Hojodcm;  Diowaas → Ryiuuvk;  Kbwpbhq → {Lbebhirj, Obdatyb}
                          Oxaxucs ← Tame_list;  Asfutbf ← Tame_opposite
L3 上层:                  Aq1 ← Hojodcm → Aq23 → Aq4 → {Aq56,Aq7,Aq8,Aq9,Aq10,Aq11}
                          Aq8 (+Meeixjo) → Aq12 → Aq13(←Tame_list)
                          Wmlnymd ← Oxaxucs+Asfutbf+Elllnyz → Dpzgbyf
L4 归约:                  Reduction1 ← Tame_list+Dpzgbyf+Rxokskc+Aq56
                          Reduction2 ← R1+Aq12+Aq13
                          More_lemma1 ← R2+Aq8/Aq12/Aq13 → More_lemma2
                              → betwn_corek → betwn_core0
                          Reduction3 ← R1+R2+More_lemma 群
                          Reduction4 ← R3+R2+Diowaas/Ryiuuvk
                          Reduction5 ← R3+R4+Betwn_core 群   [A9 出口]
L5 装配:                  Jcajydu ← Rxokskc+R5+Tame_list(DAKEFCC/GNBEVVU)  [A9]
L6 fan 几何出口:          Crttxat ← Tame_general+arc_properties   [A10-U1]
                          Hrxefdm ← Tame_general                  [A10-U2]
                          Fatugpd ← 外部(Planarity/Pack/Trig)      [独立出口]
```

三接口硬前置（scout §5 继承）：**S1 hypermapOfList 构造**（A7/A9 硬阻塞、A8 def 层阻塞）
不在 64 文件内（源 list_hypermap-compiled.hl，GoodListDefs 只有 def 无定理）——必须
W1 单 lane 先攻。

---

## §3 出口件 ↔ Assembly 接口映射（章"出口"反推）

| Assembly 接口 | sorry 处 | 消费的 tame 出口件 | 出口件所在批 |
|---|---|---|---|
| A7 `elllnyz`（:519） | :523 | ELLLNYZ:548 + Tame_list map 家族（S2）+ tame_opposite.opposite_components + Asfutbf.iso_opposite_adjoint(:95)/hyp_conj_hyp_iso(:927) + S1 | B-D1、B-D2 |
| A8 `tameCorrespondenceIso`（:512） | :515 | Wmlnymd.tame_correspondence_iso:1498 + Oxaxucs 全章（S4 iso 不变）+ Wmlnymd floor 机制（S9）+ 常数换算四件（S10）+ **S11 GoodGraphV4 忠实化**（硬前置）+ S1 | B-D2、B-D3 |
| A9 `jcajydu`（:506） | :509 | Jcajydu 全文件（99 行装配）+ Rxokskc.RXOKSKC:523 + Reduction5.restricted_hypermaps_are_planegraphs_thm + Tame_list(JXBJOAB/GNBEVVU/DAKEFCC) + S1 + S6 | B1、B2、B3、B4、B5 |
| A10 `mqmsmab`（:466） | :469 | TameLp 已真件（KCBLRQC 群清偿完毕）；余 tame 侧上游 = CRTTXAT（U1，584 行 + arc_properties 1,091）+ sum_tauVEF_upper_bound←HRXEFDM（U2，284 行）+ ineq_tauK×4（formal_lp 侧，不在本立项） | B6（U1/U2 两 lane） |
| A5 `hypermapOfFanNeg`（:539）+ A2 `contraveningNegative`（:725） | :544/:727 | Asfutbf 镜像链余量：set_of_edge_neg/dart_of_fan_neg(:290-338)、sigma_fan_neg 群(:421-655)、AZIM_LT_PI_IMP_CARD_GT_1(:668)、contravening_negative(:699)、dart1_of_fan_neg 群(:800-870)、ASFUTBF 主件(:1087)；A2 另需 Geom 侧 azim_mirror/sigmaFan 镜像工具链（Assembly:525-536 NEEDS 注记，非 tame 章） | B-D4 |
| A4 `kcImpTheKc`（:776） | :777 | **不在 tame 章**：flyspeck_devol.hl（FLYSPECK_DEVOLUTION/CPNKNXN）+ Pack2.KIUMVTC（PA 侧在账），本立项只挂边界注记 | — |

另有独立出口（无 A 表接口，但属章结论、防漏）：FATUGPD_concl（FATUGPD.hl，PA/局部扇侧
消费）、tame_general 余量（FULLY_SURROUNDED… 已落，余 conforming 桥面）、tame_concl
UBHDEUU1/2（FAN 存在性，contraveningFan 已覆盖同型）。

---

## §4 章节聚类 → 批次表（每批 = 1 个 Lean 模块 + 根构建绿；BATCH_SIZE 建议 15–20 定理）

吞吐校准：conforming.hl 17,033 行/228 定理 → 23 批（**740 行/批，10 定理/批**，
`auto_pipeline_conforming_state.txt: DONE 23`）；planarity 15,463 行 → 15 批
（`auto_pipeline_state.txt: 15281 16`）；ConformingAuto1-23 共 25,120 Lean 行 =
**1.47x HOL 展开**；polyhedron 3,200 行/71 定理收官。tame 定理密度 ~42 行/条
（81.7k 行 / ~1,940 条），高于 conforming（74）与 planarity（103）：定理口径
~1,940 ÷ 10 = **194 批上限**、行数口径 81.7k ÷ 740–1,030 = **79–110 批**。
建议 BATCH_SIZE 提至 15–20（对齐 ~1,000 行/批先例体量），取 **100–130 批、
Lean 新增 ~70–100k 行**为立项区间；tame_list 与 reduction 两块有 Mathlib/AFP 现成
落点，实际中位估计偏向区间下沿。

| 聚类批 | 内容（文件） | HOL 行 | 定理 | 批数(估) | 每批出口件（验收锚点） |
|---|---|---|---|---|---|
| **W0 keystone** | S1 hypermapOfList 构造 + S3 Iso 孪生桥 + S11 GoodGraphV4/GoodListNodes def 忠实化（Assembly def 体，STATEMENT-FIX 闸） | ~365(外源)+def | — | 2-4 | `IsHypermapOfList L (hypermapOfList L)`；GoodGraphV4 六合取真形；**A7/A8/A9 共同前置** |
| **B1 Tame_list 地基** | tame_list.hl（前 2 批先抽 S2/S6 重点件：map_good_list/hypermap_of_list_map/JXBJOAB/GNBEVVU/DAKEFCC，其余直译） | 14,428 | 650 | 10-14 | S2/S6 件即 A7/A9 装配件；其余为公共库 |
| **B2 叶件** | arc_properties、Inequalities、tame_opposite、Meeixjo、AUQTZYZ(+_list)（可 2-3 lane 并行） | 5,993 | 124 | 4-6 | arc 全章（B6-U1 前置）；opposite_components（A7 前置） |
| **B3 D 链** | Rxokskc→Dangeyj→Pwssrat→Ohcgkfu→Pplhulj→Ncvibwu→Pbflhet→{Diowaas→Ryiuuvk, QCDVKEA, PNXVWFS}→Kbwpbhq→{Hojodcm, LEBHIRJ, OBDATYB} | 11,572 | 246 | 12-16 | RXOKSKC:523（A9 件）；链顶 Hojodcm（AQ 入口） |
| **B4 AQ 链** | Aq1→Aq23→Aq4→{Aq56,Aq7,Aq8,Aq9,Aq10,Aq11}→Aq12(←Meeixjo)→Aq13 | 17,585 | 213 | 14-20 | Aq56.TL_LAST（reduction1 消费）；Aq12/Aq13（more_lemma/R2 前置） |
| **B5 reduction 链** | R1→R2→{R3, More_lemma1→More_lemma2→betwn_corek→betwn_core0}→R4→R5 | 25,361 | 504 | 18-26 | R5.restricted_hypermaps_are_planegraphs_thm（**A9 出口**）；R4.generatePolygon 系落 AFP FaceDivision/GeneratorProps（scout S8，可拆 3 子波） |
| **B6 fan 几何出口（A10-U1/U2）** | CRTTXAT、HRXEFDM、tame_general 余量（arc_properties 已在 B2） | ~900-1,700 | ~26 | 2-3 | TameLp CRTTXAT 脱 sorry；sum_tauVEF_upper_bound 脱 sorry → **A10 可接线**（装配本体 250-350 行按 mqmsmab-scout 单列，不计本表） |
| **B-D1 A7 支撑**（子集抽取批，行数含于 B1/ELLLNYZ） | Tame_list map/REVERSE 家族（S2/S5）+ Asfutbf iso_opposite 群(:30-103) | ~700 | ~15 | 2-3 | A7 可离账（自足） |
| **B-D2 correspondence** | Oxaxucs 全章（S4）+ Asfutbf hyp_conj 群(:871-970) | ~870 | ~40 | 2-3 | iso 不变家族 + hyp_conj_hyp_iso（A7/A8 消费） |
| **B-D3 A8 本体** | Wmlnymd（floor 机制 S9 + 对应链）→ Dpzgbyf → Jcajydu 装配 | 2,041 | 70 | 3-5 | **A8 离账**；Dpzgbyf（B5 前置）；**A9 离账** |
| **B-D4 A2/A5 镜像**（行数含于 Asfutbf） | Asfutbf 镜像链(:290-870) + dart1_of_fan_neg 群(:800-870) + ASFUTBF 主件(:1007-1106) + Geom 侧 azim_mirror 工具链（跨章，单列需求） | ~680 | ~25 | 2-3 | **A2/A5 离账** |
| **B7 独立出口** | FATUGPD（外部依赖 Planarity/Pack1/2/Trig1 已在 Text 层） | 1,581 | 26 | 2-3 | FATUGPD_concl（与 PA 侧消费衔接时再排） |

合计：**76–108 批**（W0-B7 调度批口径，BATCH_SIZE=15–20；B-D1/B-D4 为 B1/Asfutbf 行的
子集抽取批，不重复计入行数总量）。定理口径上限（10/批）194 批说明 BATCH_SIZE 必须上调。
关键路径 = W0→B1→B3→B4→B5→B-D3，约占总批数 55%；B2/B6/B-D1/B-D4 均可提前并行插队。

---

## §5 外部依赖与语义桥缺口（flyspeck_needs 实测汇总）

| 外部件 | 消费者 | Lean 侧现状 | 缺口 |
|---|---|---|---|
| hypermap/hypermap.hl（8 处 needs） | 几乎全体 | ✅ Text/Hypermap.lean 12,322 行 0 sorry（module-map：全书 100%） | 无 |
| fan/fan_defs.hl、fan/hypermap_and_fan.hl | Tame_general 系、Fatugpd、Jgtdebu | ✅ Text/Fan.lean（hypermapOfFan 等）；COMPONENTS_HYPERMAP_OF_FAN 已真（TameLp:541） | dart1_of_fan 孤立 dart 折算（Assembly:121-125 注记，A9 消费点需补一句） |
| packing/pack_defs.hl、pack1/2 | Fatugpd、kcImpTheKc 邻接 | 🟡 PackingAuto 群按需落件 | Pack2 测度桥四件套（upfzbzm-scout 在账，Fatugpd 波前确认） |
| fan/planarity.hl | Fatugpd | ✅ Planarity*.lean + PlanarityAuto6-16 收官 | 无 |
| trigonometry/trig1、trig3 | Fatugpd | 🟡 Geom/Azim 等局部件 | Fatugpd 波前盘点 |
| nonlinear/ineq.hl | Inequalities 相关 | 🟡 IneqClosureDefs/证书线 | B2 波前确认 Inequalities.hl 的 26 条是否已被 155 闭包覆盖（**查重后可能大半免移植**） |
| leg/geomdetail、collect_geom、general/sphere | Fatugpd、Crttxat 系 | 🟡 Geom 层 | 同上波前确认 |
| formal_lp/hypermap/ssreflect/list_hypermap_iso-compiled.hl（4 处） | Rxokskc、tame_list 消费侧、Wmlnymd | 🟡 GoodListDefs.lean 有 def 零定理 | **S1 hypermapOfList 构造 + S2 列表机器定理层**（W0） |
| tame/ssreflect/tame_lemmas-compiled.hl 等 6 文件 | Cdtetat、MQMSMAB、KCBLRQC | 🟡 TameLp 消费切片已真；deprecated_quads/lp_ineqs 注册表归 G4/A11 | 不在本立项（邻接 lane），仅边界注记 |
| Library/rstc.ml | more_tame_concl/Wmlnymd needs | — | 纯 tactic 基建，无需移植 |

语义桥缺口（跨层，装配期集中处理）：①`cong` 语义对照（HOL `__cong` 商 vs Lean
List.rotate，scout R8）；②`res` dart 外恒等 vs `PermutesOn`（scout R4）；③junk-value
家族 next_el/prev_el/idxOf（scout R5）；④×10⁴ 常数表（scout R6）；⑤tame10 合取/析取形
（scout R7）。

---

## §6 风险清单（骨架设计阶段必查）

1. **同名重复绑定（Conforming 教训，本项目实测 14 组跨文件 + 8 组文件内）**：
   - 跨文件：Inequalities↔tame_general 的 `DELTA_EQ_DELTA_X`/`DELTA_X_AND_DELTA_X4`/
     `INEQ_ALT`；FATUGPD↔Inequalities 的 `lemma1..6`；reduction2/3/4↔tame_list 的
     `mem_rotate_to`/`size_replacefacesAt`/`uniq_flatten_all_uniq`/`HD_flatten`；
     Wmlnymd↔tame_list 的 `sumn_cons`。
   - 文件内 rebind（HOL shadowing，后绑定胜出，移植前须裁决哪版承重）：
     tame_list 的 `indexf0`(:1473/:1542)、`fgraph_makeFaceFinal`(:212/:2036)、
     `fgraph_seed`(:10595/:10812)、`iso_list_cons`(:11694/:11737)、`INJ_inj_on`(:468/:13763)、
     `list_pairs_rev`/`REVERSE_rev`/`split_at_mem_snd`/`vertices_set2_makeFaceFinal`；
     Dpzgbyf 的 `subdivFace0_induct`(:137/:170)；ELLLNYZ 的 `ELLLNYZ`(:522 草稿注释/:548 正式)。
   - 处置：每批骨架设计时跑 `lean/scripts/fqn_scan.py` 同款查重（fqn-conflicts.md 口径：
     两模块导出同名 FQN 在 import 时即硬错），命名政策 = 批次模块前缀或 `_p2` 后缀 +
     canonical 裁决记录。
2. **巨证**：未移植集**无 >1,000 行单证**（最大三块：reduction3 `main_induction` 246 行、
   `size_vs` 223 行、reduction1 `flag_list_seed` 203 行）；CKQOWSA_4 的 666/435 行巨证已由
   ContraFan/ContraFanDeep 四波先例消化。分段流水沿用 auto_pipeline 的 10 定理/批即可，
   无需特批机制；但 reduction3/4 批内密度高（148/117 条），建议按 HOL 定理里程碑
   （`reduction_F`/`assumption_setK10`）切子波验收（scout §5 同款建议）。
3. **弱编码占位链（最高危静默风险）**：`GoodGraphV4` 五 True（Assembly:427-437）+
   `GoodListNodes`（:436）+ `Adm3` 尾 True（:369）——不忠实化则 A8 按现编码**不可证**、
   A9 结论空壳（R1/R2，scout §6）；`KcblrqcIneqDef := True`（:189）阻塞 A10 诚实填实
   （mqmsmab-scout Step 0，STATEMENT-FIX 豁免已提案）。三者必须与对应装配批同波落地，
   且 A9 从第一批起就对着补强后的 def。
4. **孪生定义复制（SphereKit 80+ twins 前科）**：§2b TameSpine（orbitSet 版）与
   TameLp/Hypermap.lean（Hypermap 版）双版本并存。纪律：新移植一律落 Hypermap.lean
   家族 + `Hypermap.Iso`，TameSpine 侧只留桥引理（tamePlanarHypermapRestricted 已实证
   defeq 折算可行）；B3/B4 的 fan 计数链优先复用 TameLp §2/§4 已真件。
5. **常数表静默错**：dTame/bTame/squander 表（tame_defs.hl:77-111 ↔
   import_tame_classification.hl:50-75 ↔ Assembly:331-350 ↔ TameLp:406-509）四处同值，
   错一格不触发编译错——B-D3 批验收须含逐值对照 checklist（mqmsmab-scout §6.3 已对过
   Assembly↔TameLp 两侧）。
6. **statement 冻结边界**：S11 改的是 def 体不是定理陈述文本（DEF-FIX 模式），波及面
   grep 核对过 GoodGraphV4 消费者全树仅 Assembly 内两处 + §2b 内部——风险可控但需
   编排者拍板授权。
7. **并行线**：PA23（GRUTOTI）/PA24（REUHADY）在飞，均不在 tame/ 领土；本立项 lane
   文件全部新建 `Kepler/Text/Tame*.lean`，与在飞线零文件交集；唯一共享闸门资源是
   `lake build Kepler.Assembly` 的 Graphs 自展重建（e2e-debt-map §C 已注记）。
8. **吞吐不确定度**：D 链/AQ 链是重算术（fan 计数不等式），1.47x 展开率可能偏乐观；
   反之 tame_list 大量 List 引理可被 Mathlib 直接消化（planarity 流水线已有"Mathlib 已有
   则跳过"惯例），B1 实际批数可能显著低于估计。建议 B1 先导 2 批实测后校准全表。

---

## §7 波次提案（编排者视角）

```
W0（串行 1 lane）：S1+S3+S11 keystone（2-4 批）—— 不动它 A7/A8/A9 全阻塞
W1（4 lane 并行）：B1 Tame_list ｜ B2 叶件 ｜ B6 A10-U1/U2 ｜ B-D1 A7 支撑
                   （A7 在本波末可离账：tame 章第一枚）
W2（3 lane）：     B3 D 链（两段串行子 lane）｜ B-D2 correspondence ｜ B1 收尾
W3（3 lane）：     B4 AQ 链 ｜ B-D4 A2/A5 镜像（含 Geom 侧 azim_mirror 工具链立项）｜ B7 FATUGPD
W4（3 lane）：     B5 reduction 链（R1/R2 → R3+more_lemma → R4 → R5 三子波）
                   ｜ B-D3 A8 本体（等 W0+B-D2）→ A8 离账
W5（收口）：       A9 装配（Jcajydu 99 行 + S6）→ A9 离账；A10 装配（mqmsmab-scout
                   Step 0-3 单 lane）→ A10 离账
```

里程碑口径：每批 `lake env lean` 绿 + 零新增 sorry + fqn 查重干净；每聚类收口跑一次
公理审计（GoodListShard 惯例：新模块不 import Assembly.lean 本体，防接口 sorry 污染）。

## §8 与既有文档的关系

- 细节深侦（三接口怎么填）：`docs/scouts/tame-chapter-scout.md`（S1-S11 分级 + W1-W3 lane 图 +
  R1-R9 风险族）——本文件全盘继承其结论，不重复论证。
- A10 装配：`docs/scouts/mqmsmab-scout.md`（Step 0-3 作战计划）。
- 债务记账：`docs/e2e-debt-map.md` A 表（A2/A5/A7/A8/A9/A10 六行）+ `DEBT.md`；
  本文件立项后，各批收口在 e2e-debt-map 对应行追加 commit 锚点。
- 命名治理：`docs/projects/fqn-conflicts.md` + `lean/scripts/fqn_scan.py`（§6.1 处置工具）。

# tame-chapter-scout — tame 文字章广度侦察（脊柱接口 A7/A8/A9）

> 2026-09-29 只读侦察轮交付物（纪律同 planar-encoding-fix 侦察轮：零 .lean 改动、
> 零 tracked 文件改动，唯一仓库写入 = 本文档）。对照基准：`reference/flyspeck`
> @ `1ce0353`。目标是 e2e-debt-map.md A 表三枚 GIANT 接口：
> A7 `elllnyz`、A8 `tameCorrespondenceIso`、A9 `jcajydu`。
> 领土勘误：tame 文字章 HOL 源 = `reference/flyspeck/text_formalization/tame/`
> 全目录 70 个 .hl / 4.5MB（其中 ssreflect/ 子目录仅 6 个 compiled .hl / 1.2MB，
> 属 A10 MQMSMAB / KCBLRQC / FNJLBXS 与 seq2/sort 机器——任务书所写"ssreflect/
> 下 64 个 .hl"实为全目录口径）。

---

## §1 三接口的 Lean 精确陈述与 sorry 位置

全部在 `lean/Kepler/Assembly.lean`（脊柱 §2c，接口冻结 2026-09-19）：

| 接口 | 位置 | 陈述（逐字要点） | HOL 原形 |
|---|---|---|---|
| **A9** `jcajydu` | 定理 **:506-508**，sorry **:509** | `∀ {α} [DecidableEq α] (H : Hypermap α), H.IsRestricted → ∃ g : Graph, PlaneGraphs g ∧ GoodGraphV4 g ∧ ∃ H' : Hypermap (ℕ×ℕ), IsHypermapOfList g.fgraph H' ∧ HypermapIso H H'` | JCAJYDU.hl:51 一般形 `is_restricted H → ?g. PlaneGraphs g ∧ good_graph_v4 g ∧ iso H (hypermap_of_list (fgraph g))`（Lean 把 HOL 的单一 iso 拆成 `HypermapIso H H'` + `IsHypermapOfList g.fgraph H'` 两合取） |
| **A8** `tameCorrespondenceIso` | 定理 **:512-514**，sorry **:515** | `(g) (H) (H') (hgg : GoodGraphV4 g) (ht : TamePlanarHypermap H) (hiso : HypermapIso H H') (hIs : IsHypermapOfList g.fgraph H') : tame g` | WMLNYMD.hl:1498 `good_graph_v4 g ∧ tame_planar_hypermap H ∧ iso H (hypermap_of_list (fgraph g)) → tame g` |
| **A7** `elllnyz` | 定理 **:519-522**，sorry **:523** | `(x y : fgraph ℕ) (hx : GoodList x) (hy : GoodList y) (hiso : iso_fgraph x y) (Hx) (hHx : IsHypermapOfList x Hx) : ∃ Hy, IsHypermapOfList y Hy ∧ (HypermapIso Hx Hy ∨ HypermapIso (oppositeHypermap Hx) Hy)` | ELLLNYZ.hl:548 析取镜像桥（phase6-spine.md §5 明文要求保持析取形） |

关键定义（消费侧词汇表）：

| Lean 名 | 位置 | 内容/状态 |
|---|---|---|
| `HypermapIso` | Assembly.lean:90-96 | hypermap.hl:9614 `iso` 逐字镜像（BijOn + 三映射交换） |
| `IsHypermapOfList` | Assembly.lean:108-115 | `hypermap_of_list` 的**规格级**结构（darts_eq + 三映射在 dart 上 = eList/nList/fList）；Assembly:99-107 注记：**Lean 无 `hypermapOfList` 构造（P6-C 遗留）** |
| `TamePlanarHypermap` | Assembly.lean:406-409 | Tame1∧Tame2∧Tame3∧Tame4∧Tame5a∧Tame8∧Tame9a∧Tame10∧Tame11a∧Tame11b∧Tame12o∧Tame13a（tame_defs.hl:180 镜像，§2b TameSpine :377-404） |
| `GoodGraphV4` | Assembly.lean:440-442 | tame_defs2.hl:53 `good_graph_v4` 六合取镜像，**但后五合取项是 True 占位**（见 §6-R1）：`FinalGraph`:427、`AllUniq`:429、`GoodFacesV3`:431、`VerticesSet2Eq`:433、`GoodListNodes`:436-437 全为 `True` |
| `GoodList` | Assembly/GoodListDefs.lean:68-70 | list_hypermap-compiled.hl:63 逐字镜像（darts Nodup ∧ 面非空 ∧ dart 对称） |
| `iso_fgraph` | Graphs/PlaneGraphIso.lean:265（`is_Iso`:274 允许镜像析取） | AFP 移植；`cong`（旋转同余）在 Graphs/RotationLemmas.lean:28 |
| `tame` | Graphs/Tame.lean:164 | `tame9a∧tame10∧tame11a∧tame11b∧tame12o∧tame13a`（import_tame_classification.hl:116 逐字镜像，AFP Graph/Face/Nat 编码） |
| `Hypermap.IsRestricted` | Text/Hypermap.lean:9645-9649 | hypermap.hl:11174 逐字镜像 |
| `oppositeHypermap` | Assembly.lean:413-424 | tame_defs.hl:185 镜像，四个 proof 字段已闭合 |
| `Hypermap` | Text/Hypermap.lean:765-783 | hypermap.hl:92 结构化（Finset darts + Equiv.Perm×3 + permutes×3 + comp_eq_one） |

---

## §2 Text 侧骨架地图（消费链与真伪）

### 2.1 唯一消费者：`textCapstone`（Assembly.lean:842-887，真证明）

```
textCapstone (:842)
 ├─ mqmsmab (A10, sorry :469)                         → TamePlanarHypermap (hypermapOfFan 0 V …)  [:858]
 ├─ tamePlanarHypermapRestricted (:481, 真证明)        → IsRestricted                              [:860]
 ├─ jcajydu (A9, sorry :509)                          → g, PlaneGraphs g, GoodGraphV4 g, Hg, hHgIs, hIsoFanHg  [:861]
 ├─ tameCorrespondenceIso (A8, sorry :515)            → tame g                                    [:862]
 ├─ tame_classification (Graphs/TameClassification.lean:23, 真证明, Phase 2 闭合)
 │                                                    → ∃y∈archive, iso_fgraph (fgraph g) y       [:865]
 ├─ elllnyz (A7, sorry :523)                          → Hy, hHyIs, 正向/镜像析取                   [:866-867]
 │   ├─ 正向分支: hypermapIsoTrans (:782 真) ∘ hIsoFanHg ∘ hbr1 → hLPR 证 ¬Contravening V
 │   └─ 镜像分支: contraveningNegative (:725, A2 sorry) + contraveningFan (:457 真)
 │                + hypermapOfFanNeg (:539, A5 sorry) + isoOppositeEq (:591 真, wave3 闭合)
 ├─ goodListArchive (:889 真, P6-C 19715 图)          → 前提 hAllGood
 └─ lpArchiveCertificates (A12, sorry :810)           → hLPR（终点接收方）
```

全树 grep 证实：A7/A8/A9 **没有 textCapstone 之外的消费者**——三枚都是
textCapstone 的直接叶子债务；但 A7/A9 的输出（`HypermapIso Hg Hy`）正是 A12
`FanHypermapIsoList`（Assembly.lean:127-129）的展开形态，属 LP 侧填实路径的
前置（phase6-spine §2"原 P6-D 桥与 P6-C hypermapOfList 构造依赖移入
lpArchiveCertificates"）。

### 2.2 既有可复用件（勿重造，playbook §2.3 查重纪律）

| 件 | 位置 | 状态 | 复用面 |
|---|---|---|---|
| `Hypermap.Iso` + `Iso.refl/symm/trans` | Text/Hypermap.lean:8249-8296 | **已证**（symm 需 `Nonempty α`） | 与 `Assembly.HypermapIso`（:90）**逐字同体孪生**——S3 基础件近乎白捡，见 §6-R3 |
| `hypermapIsoTrans` | Assembly.lean:782-794 | 真证明 | A7/A9 装配 |
| `isoOppositeEq`/`hypermapIsoOpposite`/`oppositeHypermapOpposite` | Assembly.lean:549-600 | 真证明（wave3 闭合 A1） | A7 镜像分支 |
| `tamePlanarHypermapRestricted` | Assembly.lean:481-502 | 真证明，**实证 TameSpine 孪生定义与 Hypermap.lean 原语逐项 defeq 折算可行** | A8 前提 |
| 列表机器 defs | GoodListDefs.lean:30-62（listPairs/listOfDarts/nextEl/prevEl/findFaceDarts/eList/fList/nList） | 已镜像，**零定理层**（只有 Bool 反射三件 :91-107） | S1/S2/S5 的地基 |
| `Hypermap.lean` 全章 | Text/Hypermap.lean（12322 行，**0 sorry**） | 已收官 | S4/S7 的 hypermap 侧轨道引理 |
| AFP 图机器 | Graphs/（Plane1/generatePolygon/subdivFace = FaceDivision*.lean、GeneratorProps.lean、RotationLemmas cong、PlaneGraphIso 同构理论） | 已收官 | S8 reduction 链的 AFP 侧落点 |

### 2.3 缺口件（全部待新建）

`hypermapOfList` 构造（Lean 侧完全缺失——GoodListDefs 只有 defs 无定理）；
`HypermapIso` 不变性家族；列表↔超映射运输家族；reduction 链；floor 权重机制。
下节逐项定位。

---

## §3 HOL 对照：锚点与依赖 DAG

### 3.1 三 .hl 锚点

| 文件 | 规模 | 关键锚点 |
|---|---|---|
| **ELLLNYZ.hl** | 590 行 | `ELLLNYZ_concl` :18-21；同余块 :27-207（CONG_NIL :27、cong_sym :47、cong_refl :63、cong_trans :75、cong_class :94、cong_eq_hypermap_of_list :104、good_list_cong_uniq :134、good_list_cong_perm_eq :169、**CONG_hypermap_of_list :180**）；REVERSE 块 :209-494（good_list_REVERSE :209、dart_REVERSE :238、edge_map_reverse :254、list_of_faces_rev :270、find_face_rev :283、indexl_rev :316、next_el_rev :337、face_map_reverse :370、**hypermap_of_list_reverse :440**）；good_list_iso_fgraph_proper :495；**ELLLNYZ :548**（:522 为注释掉的草稿）。证明消费：map_good_list + hypermap_of_list_map（tame_list.hl:3403/3486）、Asfutbf.iso_opposite_adjoint + hyp_conj_hyp_iso、Tame_opposite.opposite_components、Hypermap.iso_trans/iso_sym |
| **WMLNYMD.hl** | 1515 行 | needs 头 :8-11（rstc.ml、hypermap.hl、list_hypermap_iso-compiled.hl、more_tame_concl.hl）；opens Oxaxucs/Asfutbf/Elllnyz :19-25；对应链：tame9a_correspondence :42、tame10_correspondence :107、finalGraph_except :139、tame11a_list def :170、tame11_correspondence :757、tame12o_correspondence :813；**floor 权重机制 :844-1359**（floor_lemma :844、nfloor_exists :857、wt_floor :878、adm_1/2/3_floor :881-890、tame_13a_floor :894、wt_floor_nn :898、total_weight_floor :942、adm_1_floor_adm_1 :971、FINITE_set_of_face/n_meeting_node :1005/:1020、b_tame_explicit :1052、squanderVertex_explicit :1075、vertextypes_explicit :1098、adm_2_floor_adm_2 :1181、adm_3_floor_adm_3 :1246、tame_13_a_floor_tame_13_a :1293、BIJ_NSUM :1342）；**tame13a_correspondence :1360-1472（~110 行）**；tame_correspondence1 :1473；**tame_correspondence_iso :1498** |
| **JCAJYDU.hl** | 99 行 | **JCAJYDU1 :23-48**（任意型 list 版前提 → 一般形；消费 Rxokskc.RXOKSKC + Tame_list.DAKEFCC + Hypermap.iso_trans）；**JCAJYDU :51-91**（num 版前提 → 一般形；消费 JXBJOAB + GNBEVVU + iso_list_restricted + iso_list_good_list(_nodes) + iso_list_sym_nil_eq + GNBEVVU + iso_trans） |

### 3.2 依赖 DAG（各 .hl 引什么）

```
A7  ELLLNYZ.hl (590)
    ├─ hypermap.hl            → 已移植（Text/Hypermap.lean 0 sorry）
    ├─ Import_tame_classification.hl (146) → iso_fgraph/is_Iso 定义层 → AFP 移植已有
    │     （HOL __cong ↔ Lean RotationLemmas.cong 的语义对照 = §6-R8）
    ├─ tame_list.hl (14428)   → 只取 map_good_list:3403 / find_face_map:3441 /
    │                           hypermap_of_list_map:3486（=S2）
    ├─ Asfutbf.hl (1106)      → iso_opposite_adjoint / hyp_conj_hyp_iso
    ├─ tame_opposite.hl (612) → opposite_components（Lean oppositeHypermap 定义展开+wave3 件可拼）
    └─ 自带块：同余理论 :27-207 + REVERSE 理论 :209-494（=S5）

A8  WMLNYMD.hl (1515)
    ├─ Oxaxucs.hl (614)       → iso 不变家族全章（=S4）：tame9a_iso:38、tame10_iso:57、
    │       tame11a_iso:67、tame11b_iso:86、tgt_squanderTarget:105、d_tame_squanderFace:115、
    │       b_tame_squanderVertex:134、a_tame_excessTCount:150、BIJ_face_iso:160、
    │       BIJ_face_set_iso:255、CARD_face_iso:291、exceptional_face_*:313-407、
    │       tame12o_iso:408、adm_1_iso:431、set_of_*_meeting_node_iso:459-512、
    │       type_of_node_iso:525、adm_2_iso:536、adm_3_iso:566、tame13a_iso:595
    ├─ list_hypermap-compiled.hl (1292) → card_face_of_list:1131、components_hypermap_of_list:630、
    │       good_list_nodes_condition:1025、uniq_list_of_elements:904、card_nodes_of_list:963 等
    ├─ tame_defs/tame_defs2/import_tame_classification → 双侧 tame_N 定义（Lean 双侧均已镜像）
    ├─ Asfutbf/Elllnyz/More_tame_concl/rstc.ml/list_hypermap_iso-compiled.hl (1027)
    └─ 自带块：对应链 :42-1472（=S9 的 floor 机制 + 逐 tameN 对应）

A9  JCAJYDU.hl (99)
    ├─ RXOKSKC.hl (1105)      → RXOKSKC:523（=S7）；子件 EXISTS_LIST_FACE_NODE_FUNC:229、
    │       LIST_COR_FACE_SET1:418 自带；opens Auqtzyz (2624 行, 7 定理, 轨道/POWER 机器;
    │       RXOKSKC 用 node_node_map_eq 等) + List_hypermap
    ├─ reduction1-5 链        → restricted_hypermaps_are_planegraphs_v4（tame_defs2.hl:693-703 定义;
    │       reduction1.hl:4976 装配 :4784 + betwn_core0_z_y.hl:1352 + betwn_corek_z_x.hl:726
    │       + reduction2.hl:1671 + reduction3.hl:5656(reduction_F, generatePolygon_reduction_v7
    │       链接 AFP 侧) + reduction4.hl:5436 + reduction5.hl:160 = **~19.9k HOL 行**）（=S8）
    ├─ tame_list.hl           → JXBJOAB:3733（标准化到 num，用 INJ_NUM_EXISTS 有限集入 num）（=S6）；
    │       GNBEVVU:3540（iso_list → iso，proof = 一行引 hypermap_of_list_map）；
    │       DAKEFCC:9360 = iso_restricted（iso 保 is_restricted，= S4 的推论件）
    └─ Hypermap.iso_trans     → 已移植
```

### 3.3 共享前置件清单（S 编号，§4/§5 逐项定级）

| # | 件 | HOL 位置 | 阻塞谁 |
|---|---|---|---|
| S1 | `hypermapOfList` 构造（good_list L → `IsHypermapOfList L (hypermapOfList L)`） | list_hypermap-compiled.hl:152-517：e_list_ext_permutes_darts:171、dart_in_face:210、uniq_list_pairs:284、next_el_list_pairs:316、prev_el_list_pairs:342、f_list_inverse:361、find_face_f_list:384、f_list_ext_permutes_darts:395、f_list_ext_inverse_works:462、n_eq_e_fi:472、n_list_ext_permutes_darts:486、**e_n_f_id:497**、**tuple_hypermap_of_list:506** | **A7（∃Hy witness）+ A9（∃H' witness）硬阻塞；A8 软阻塞**（GoodListNodes def 内容需要它才能忠实陈述） |
| S2 | MAP(MAP φ) 运输家族（map_good_list/find_face_map/hypermap_of_list_map + CONG_hypermap_of_list） | tame_list.hl:3403-3539 + ELLLNYZ.hl:180-207 | A7 正向分支、A9（GNBEVVU 一行依赖它） |
| S3 | HypermapIso 基础（refl/sym/trans + 孪生桥） | Hypermap.Iso 已证（Lean）；Assembly 侧 trans 已证 | 三者装配 |
| S4 | HypermapIso 不变性家族（轨道双射 + 基数 + IsRestricted 各合取项 = DAKEFCC） | Oxaxucs.hl:160-534 + hypermap.hl | A8（iso 不变）、A9（DAKEFCC） |
| S5 | REVERSE 理论（面反转 ↦ oppositeHypermap） | ELLLNYZ.hl:209-494 | 仅 A7 镜像分支 |
| S6 | JXBJOAB 标准化（有限顶点集 InjOn 入 ℕ） | tame_list.hl:3733-3747 | 仅 A9 |
| S7 | RXOKSKC（受限超映射 → 列表表示） | RXOKSKC.hl:229/418/523（+AUQTZYZ 支撑） | 仅 A9 |
| S8 | reduction1-5（num 列表 → 平面图 g 的构造） | reduction1-5.hl + betwn_core*.hl ~19.9k 行 | 仅 A9（最大单体） |
| S9 | floor 权重机制 + tameN 对应链 | WMLNYMD.hl:844-1472 | 仅 A8 |
| S10 | 常数转换四件（tgt_squanderTarget 等 ×10⁴ 尺度桥） | Oxaxucs.hl:105-158 | 仅 A8 |
| S11 | GoodGraphV4/GoodListNodes 等 def 补全（见 §6-R1） | tame_defs2.hl:31-80 | A8 硬前置；同时加大 A9 结论义务 |

---

## §4 逐子项难度分级 + 行数预估（Lean 新增行）

| 子项 | 分级 | HOL 行 | Lean 预估 | 说明 |
|---|---|---|---|---|
| S1 hypermapOfList 构造 | **GIANT** | ~365（核心 152-517） | **800-1200** | 纯列表手术（idxOf/headD/getD/rotate）；P6-C 单图原型（66 dart Tri）已全链内核闭合，可行性有实证；next_el/prev_el 的 junk 情形按 GoodListDefs:36-47 折算口径逐字移植 |
| S2 MAP 运输家族 | 中等 | ~140 | 300-500 | inj_on φ 下的 find_face/uniq/nodup 搬运；A7/A9 共用 |
| S3 Iso 基础+孪生桥 | 廉价 | — | 50-100 | `Hypermap.Iso`↔`HypermapIso` 互推（同体）+ symm 白捡 |
| S4 iso 不变家族 | **GIANT** | ~370+DAKEFCC | 700-1100 | 全部从零（Hypermap.lean 无 Iso 内容）；轨道双射 + ncard 搬运 + 权重/交会集双射；建议落 Hypermap.lean 家族（§6-R3） |
| S5 REVERSE 理论 | 中等 | ~285 | 400-600 | indexl/next_el/find_face 的 rev 逐字移植，junk 情形密集 |
| S6 JXBJOAB | 廉价 | ~15 | 50-100 | Mathlib 有限集入 ℕ（经典选择，choice 合法） |
| S7 RXOKSKC | **GIANT** | 1105 | 1500-2500 | 两个 200-400 行子件（轨道→面列表构造 + face 对应）+ AUQTZYZ 轨道/POWER 支撑 |
| S8 reduction1-5 | **GIANT²（章节级）** | ~19.9k | 8000-15000 | ytrans/ztrans/rtrans/core/marked_list/transform_count 机器 + generatePolygon_reduction_v7（AFP 侧 Lean 已有 FaceDivision/GeneratorProps 落点）；可再分 3-4 个子 lane |
| S9 floor 机制 + 对应链 | **GIANT** | ~630 | 1000-1500 | 实权重地板化到 Nat 权重 + b_tame/squanderVertex/vertextypes 显式表 + 三条 adm_floor 桥 |
| S10 常数转换 | 廉价 | ~55 | 100-150 | ×10⁴ 尺度表逐值核对（§6-R6） |
| S11 GoodGraphV4 补全 | 中等（def 层） | tame_defs2:31-80 | 150-250 | vertices_set2/facesAt_v2/perm_eq 等 AFP↔HOL 图数据桥；需保真审（§6-R1） |
| A7 装配 | 中等 | ~55 | 150-300 | AFP is_iso 拆 proper/improper + CONG 运输拼装 |
| A8 装配 | 中等-大 | ~60（:1473-1513） | 500-800 | tame_correspondence1 六合取组装 + Oxaxucs 六件 iso 链（主体在 S4/S9） |
| A9 装配 | 中等 | 99（全文件） | 150-250 | JCAJYDU1/JCAJYDU 两次 iso_trans 折叠（前提 = S1/S2/S6/S7/S8/DAKEFCC） |
| **合计** | | | **A7 ≈ 1.3-1.8k；A8 ≈ 2.5-3.7k；A9 ≈ 10-19k** | A9 是 tame 章最大单体，约 70% 体量在 S8 |

---

## §5 填证 lane 拆分提案（波次）

**hypermapOfList（S1）阻塞关系**：A9 需要产出 `∃ H' : Hypermap (ℕ×ℕ)` 且
`IsHypermapOfList g.fgraph H'` 把 dart 集与三映射**逐点钉死**——任何 witness 必须
就是 canonical `hypermapOfList` 构造本身，**硬阻塞**；A7 同理需要对 y 的
∃Hy witness（即使走"Hx 运输"替代路线，darts_eq/faceMap_eq 仍需完整列表机器，
不省实质）→ **硬阻塞**；A8 经 `GoodListNodes`（现 True 占位，忠实化需 S1 先落）
→ **def 层软阻塞**。结论：**S1 是三接口共同 keystone，必须第一波单 lane 攻坚**。

```
W1（keystone 波，串行 1 lane）
  L-KEY：S1 hypermapOfList 构造 + S3 孪生桥 + S11 GoodGraphV4/GoodListNodes
         def 补全（def 体填充不改定理陈述文本；走保真审+折算登记，参照
         planar-encoding-fix §4 的 DEF-FIX 纪律）
W2（并行 4-5 lanes，仅依赖 W1）
  L-A7   ：S2 + S5 + A7 装配           → A7 可在本波离账（自足，不碰 reduction/floor）
  L-ISO  ：S4 + S10 + DAKEFCC          → 共享模块（A8/A9 两头消费）
  L-RXO  ：S7 RXOKSKC                  → 自足（只吃 Hypermap.lean + S1 列表机器）
  L-FLOOR：S9（WMLNYMD 对应链 9a/10/11a-b/12o/13a）
  L-RED-1：S8 前半（reduction2/3 + AFP 链接件，FaceDivision/GeneratorProps 落点）
W3（并行 2-3 lanes）
  L-RED-2：S8 后半（reduction4/5 + betwn_core 双件）
  L-A8   ：A8 装配（等 L-ISO + L-FLOOR + W1）
  L-A9   ：A9 装配（等 S2 + S6 + L-RXO + L-RED + DAKEFCC）
```

- **并行安全**：L-A7/L-ISO/L-RXO/L-FLOOR/L-RED-1 五 lane 互无 import 边（建议各
  自独立新模块，如 `Kepler/Text/TameBridge*.lean`，仅 import Text/Hypermap +
  Assembly/GoodListDefs + Graphs；**不** import Assembly.lean 本体，防接口 sorry
  拉进公理审计——GoodListShard 惯例）；L-A8 与 L-A9 装配 lane 都改 Assembly.lean
  邻域，同波只留一个（W3 二选一先收）。
- **关键路径** = L-KEY(S1) → L-RED-1/2(S8) → L-A9。A7、A8 都不在关键路径上，
  可先行离账（债图 -2 枚后 A9 单独在账）。
- L-RED（S8）本身 GIANT²，建议内部再按 reduction2/3/4 切三个子波，每子波以
  HOL 定理为验收单元（betwn_core0_z_y / reduction_F / assumption_setK10）。

---

## §6 风险清单（弱编码/误移植家族排查，对照 planar-encoding-fix 教训）

planar-encoding-fix 的三种病：**弱定义空洞化**（facetOfC 少合取支）、**谓词整体
换错**（polyhedronC）、**严格→弱化一词之改**（cone0P22 affGt→affGe）。逐项排查：

- **R1（最重要，与 facetOfC 同族但方向相反）`GoodGraphV4` 五个 True 占位**
  （Assembly:427-437）：弱化的是**假设侧**，后果不是"空洞化为真"而是 **A8 按现
  编码不可证**——HOL tame_correspondence1（WMLNYMD:1473）展开 good_graph 后，
  vertices_set2（tame10 对应）、good_faces_v3 的 perm_eq（tame11a/11b 对应）、
  all uniq、finalGraph 全部承重，且这些内容**不能**从 GoodList 单独推出（fgraph g
  与 AFP 图的 faceListAt/faces 字段之间的数据桥全靠它们）。修复 = S11 def 补全
  （六合取忠实化），走保真审；**注意副作用**：def 补强同时加大 A9 的结论义务
  （GoodGraphV4 出现在 A9 结论侧）——A9 装配必须**从一开始就对着补强后的 def**，
  避免返工。这是 A8/A9 的耦合点，两枚必须同一波次口径落地。
- **R2 `GoodListNodes = True`**（Assembly:436）：同 R1；其 HOL 内容
  `node_set (hypermap_of_list L) = set_of_list (nodes_of_list L)` 依赖 S1 才能
  陈述——S1 未落前 GoodGraphV4 无法忠实化，这是 W1 排序的又一理由。
- **R3（polyhedronC"两版并存"式孪生）`HypermapIso` vs `Hypermap.Iso`、
  TameSpine 组件 vs Hypermap.lean 组件**：`Assembly.HypermapIso`（:90）与
  `Hypermap.Iso`（Hypermap.lean:8249）逐字同体；TameSpine 的
  PlainHypermap/PlanarHypermap/SimpleHypermap/IsNoDoubleJoins 等与
  Hypermap.Plain/Planar/Simple/IsNoDoubleJoins 双版本并存（tamePlanarHypermapRestricted
  已实证 defeq 可折）。风险形态同"Polytope.lean V3 版 vs PA22 planar 版两版
  并存"：S4 iso 不变家族若在 TameSpine 侧展开会**复制孪生定理群**（项目自述
  最痛历史债务，SphereKit 80+ twins 前科）。纪律：S4/S7 全部落 `Hypermap.Iso`
  + Hypermap.lean 家族，TameSpine 侧只留桥引理。
- **R4（cone0 式"编码差异无声进账"）`res`（dart 外恒等）约定**：HOL
  hypermap_of_list 用 `res` 把映射限制到 dart 集，Lean 用 `PermutesOn` 字段内
  置（Assembly:99-107 已注记）。消除 S1 时**不得**在 IsHypermapOfList 之外重复
  加合取项（那会弱化 A9 结论的可用性）；反向地，A5 hypermapOfFanNeg 同款
  "dart1_of_fan 不含孤立 dart"折算（Assembly:121-125 注记）在 A9 消费点
  （Contravening V 无孤立点）需补一句证明，不能靠 silent defeq。
- **R5（junk-value 家族，SUM_INTER 前科）next_el/prev_el/idxOf 越界约定**：
  GoodListDefs:36-47 的折算（idxOf=length、headD/getD/getLastD 默认元）与 HOL
  next_el/prev_el 在 dart ∉ s 时的 junk 行为必须逐一对照——A7 的 REVERSE 块
  （indexl_rev/next_el_rev，ELLLNYZ:316-369）会把 junk 情形成批拉进分支；
  移植时逐字带前提，不要"显然成立"跳步。
- **R6（d_tame 表 ×10⁴ 尺度，tame13a 暗礁）**：TameSpine 侧 tgt=1.541/bTame/
  dTame 为实数表（Assembly:331-350，tame_defs.hl:77-111 镜像），AFP 侧
  squanderTarget=15410/squanderFace/squanderVertex 为 Nat 表；Oxaxucs 的
  tgt_squanderTarget(:105)/d_tame_squanderFace(:115)/b_tame_squanderVertex(:134)/
  a_tame_excessTCount(:150) 四件是唯一换算桥。**表值逐一核对**（HOL
  import_tame_classification.hl:50-75 与 tame_defs.hl:81-111），错一格则
  tame13a_correspondence 无声错表——此类数值错不触发编译错，属最高危静默风险。
- **R7（tame10 形态差）**：HOL graph 侧 tame10 = `13 ≤ n ∧ n ≤ 15`（合取，
  import_tame_classification.hl:98-100），TameSpine Tame10 = `13∨14∨15`（析取，
  Assembly:392）——trivial 等价但对应链要显式折算；omega/重写方向坑标注给填工。
- **R8（iso_fgraph 语义对照，phase6-spine §2 已挂账的保真审点）**：Lean
  `iso_fgraph`（AFP 移植，is_Iso = proper ∨ proper∘REVERSE 析取）与 HOL
  text_formalization 版（import_tame_classification.hl:128-141，同有 proper/
  improper 析取 + EQ_CLASS/IMAGE 同余表述）形态一致，但 HOL 走 `__cong` 商
  （EQ_CLASS :120），Lean `cong` 是 List.rotate（RotationLemmas.lean:28）——
  A7 装配第一步（is_iso 拆取 + 同余类搬运）前需一次逐字语义对照，确认
  `cong`、`is_pr_Hom`、`elements_of_list` 三者口径无偏。
- **R9（陈述冻结与 def 语义变更的边界）**：S11 改的是 TameSpine 的 **def 体**
  不是接口定理陈述文本——类比 DEF-FIX 模式（改 def、陈述冻结、登记折算），
  需要编排者/用户拍板授权范围（建议只限 Assembly.lean:427-442 五个 def +
  必要辅助 def，波及面 grep 核对：GoodGraphV4 消费者全树仅 Assembly 内部
  jcajydu/tameCorrespondenceIso 两处 + TameSpine 内部）。

---

## §7 一页结论

- **A7 最大阻塞件**：S5 REVERSE 理论 + S2 MAP 运输（~1000 行，中等档），
  外加 S1 witness；整章自足、无 reduction/floor 依赖，**可最先离账**。
- **A8 最大阻塞件**：S9 floor 权重机制（~630 HOL 行）+ S4 iso 不变家族
  （~370 HOL 行）；但**先决条件是 S11 GoodGraphV4 五占位忠实化**（R1 耦合），
  否则按现编码不可证。
- **A9 最大阻塞件**：S8 reduction1-5 链（~19.9k HOL 行，tame 章 85% 体量在
  此）+ S7 RXOKSKC + S1；A9 是三枚中真正的大流域，建议作为专项波而非单 lane。
- **共同 keystone**：S1 `hypermapOfList` 构造（P6-C 遗留）——A7/A9 硬阻塞、
  A8 def 层阻塞，W1 必做。

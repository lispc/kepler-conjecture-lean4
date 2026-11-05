# pivot-reverse-scout — pivot 反向 k=3/4 侦察报告（零改动只读侦察）

> 2026-10-12 侦察 lane 交付。纪律：零 .lean 改动、零 git 写操作、本文件为唯一写入
> 文件（验证探针经 `lake env lean /dev/stdin` 跑 `#print axioms`，零文件落盘）。
> 所有 file:line 经 grep/sed/Read 实测核对；axiom 结论经 Lean kernel 实测。
>
> **核心结论先行**：
> ① **本件已闭合，立项依据过时**：pivot 反向 k=3/4 = `p23_grutoti_pivot_rev_k34`
> （PA23:5612），GT-5/GT-6 波（2026-10-10）已全额填证。实测：PA23 全文件
> **0 个 tactic 级 sorry**（`grep -E "^\s*sorry\b|:= sorry\b|sorryAx"` 零命中）；
> olean（10-12 15:50）新于源码（10-10 13:36）；capstone `Kepler.Text.GRUTOTI`
> （PA23:6396）已证。milestones-and-risks-2026-10-12.md §2 该行应改记"已闭合"。
> ② **GRUTOTI 五枚 giant 全闭**：region（PA23:2610，GT-4b）、cell_vol
> （PA23:4309，GT-3e/f）、sum_volD（PA23:5796）、pivot（PA23:6221，GT-5/6）、
> volD_pos（PA23:6386——SF-18 已修冻结陈述补 `hne`，一行 `volumeConicCapPos`
> 填证；其上方 docstring "STILL sorry" 已过时）。
> ③ `#print axioms GRUTOTI` = `[propext, sorryAx, Classical.choice, Quot.sound]`
> ——sorryAx **全部来自上游 7 处具名 taint**（§3 表），本文件零直接 sorry。
> 其中真正的大件只剩 **AJRIPQN**（PA17:321 sorry，HL AJRIPQN.hl 1051 行）。
> ④ **三座共享银行已全部落地且 kernel 级干净**：`ConicCapVolume.lean`（1610 行
> 0 sorry；volumeConicCap:902 / volumeConicCapWedge:1447 / volumeConicCapPos:961，
> 已喂 PA24:1594 REUHADY 链）；CONIC_CAP trio（PA15:2218/2266/2275，Kit D
> `p15_box_pos` PA15:1951 路线——**/tmp/gt3a_probeD.lean 已消失，工作落树**，
> 行号自 818-828 漂移；axiom 探针无 sorryAx）；Pack2 测度桥私件化
> （p23_measure_setSum_biUnion 等，PA23:52 注记）。PA12
> VORONOI_LIST_3_SINGLETON_EXPLICIT 也已干净（PA23:732 "still sorried" 注记过时）。
> ⑤ **剩余真数学 = AJRIPQN 一件**（估 400-800 行）；其余 taint 全是 S/M 散件且
> 多与 TSKAJXY/OXLZLEZ 链共享（PA10/PA14 族建议归彼链时窗，勿为 GRUTOTI 单立）。
> ⑥ merge 接线未做：全树仍**零文件 import PA23**；PackingConcl:612 discharge 仍走
> PA24→PA2 sorried 接口（GRUTOTI1_concl PA2:5477 仍 sorry）。改线 = 加 import +
> `exact PA23.GRUTOTI` 一步 + 删 PA24:6369-6398 拷贝，工程微件。

---

## §0 定位与陈述（Q1）

### 0.1 正向 / 反向 / 反向 k=3/4 各指什么

| 名 | Lean 落点 | 陈述（翻译） | 状态 |
|---|---|---|---|
| **正向** `grutoti_cell_vol` | PA23:4309-4329 | 边胞 X（{u0,u1} ∈ edgeX）+ **前向 cellParamsD 见证**（hjunk：`truncateSimplex 1 (cellParams V X).2 = [u0,u1]`；cellParams/cellParamsD 定义 PA2:373/407）+ 窄性 hw1/hw3/hw4 ⇒ `vol(X ∩ D) = vol D · dihX V X (u0,u1) / (2π)` | ✅ GT-3e/f 已证 |
| **反向** `grutoti_pivot` | PA23:6221-6239 | 对边胞全集 `grutotiEdgeCells V e` 的 setSum SUM_EQ：`∑ vol(X∩D) = ∑ vol D·dihX/(2π)`——**不假设每胞有前向见证**（junk 安全：nullSet X ⇒ dihX=0，PA2 编码） | ✅ GT-5/6 已证 |
| **反向 k=3/4**（G3）`p23_grutoti_pivot_rev_k34` | PA23:5612-5706 | X 非零测边胞、canonical `cellParams V X` 指标 ∈ {3,4}、**且无前向见证**（hwit 反）⇒ 同一体积恒等式。证明结论 = **分支真空**（hwit 被制造的见证反驳） | ✅ GT-6 已证（零 sorry） |

反向 k=3/4 之所以难：cell 的 canonical 参数表把边"反向"携带（[u1;u0,…]）或藏在中段
时，正向引理（需要 `truncateSimplex 1 … = [u0,u1]`）吃不到——k=2 可经
MCELL2_PERMUTE_01 镜像救回（PA23:6329-6357），k∈{3,4} 是真正的结构角落。

### 0.2 HOL 侧锚点（无具名定理——GRUTOTI.hl 是单 prove_by_refinement 636 NEW_GOAL）

- **反向 k=3/4 = §H 的 i=3 / i=4 两臂**：
  - `NEW_GOAL F` 分支起点 GRUTOTI.hl:7570；`ASM_CASES_TAC i = 3` :7583；
    `CARD_MINUS_DIFF_TWO_SET` 计数 :7612；SET-级 hull 重表论证 :7583-7755；
  - `ASM_CASES_TAC i = 4` :7671（同款 CARD 链）；
  - 两臂逻辑：`vol(x∩D) > 0` ⇒ 参数表 4 点展开 + {u0,u1} ⊆ 截断表点集 ⇒ CARD
    计数矛盾（F）；否则落 `vol(x∩D) = 0`（junk 支，两侧同零）。
- **使能件 = B7 覆盖陈述** GRUTOTI.hl:2631-2636：`mcell_set V X ∧ ¬NULLSET(X∩D)
  ⇒ ∃k≥2 vl. barV V 3 vl ∧ X = mcell k V vl ∧ truncate_simplex 1 vl = [u0;u1]`
  （即正测度胞必有前向见证）。
- **pivot 求和步** GRUTOTI.hl:7961-7967（REWRITE_WITH sum…= sum…，MATCH_MP_TAC
  SUM_EQ）；**cancel + vol D > 0**（VOLUME_CONIC_CAP）:7968-8001。
- Lean GT-6 走的正是这条 HL 覆盖路线（PA23:5586-5611 docstring 明注"NOT the
  permutation route the GT-5 NEEDS note anticipated"）：正测度迹在 (1,c)（B3+B4
  阈 c，`p23_region_exists_c` PA23:1464）+ `p23_rev34_hull_form`（PA23:5420，
  SET-级 hull 重表为 X = hull{u0,u1,v,w} 且 ¬Coplanar）+ CONIC_CAP_INTER_
  CONVEX_HULL_4_GT_0@PA15:2275 给正体积 + `p23_cover_C`（PA23:2036，B5 覆盖）+
  AJRIPQN 唯一性 ⇒ 前向见证 (min k 4, vl) ⇒ 反驳 hwit。
- **TSKAJXY3.hl 关系**（2288 行，module Tskajxy，"Remaining cases of TSKAJXY"）：
  gammaX/密度章，**无 pivot 内容**；与本件只共享 GT-1 锥帽银行（其 HL:1959 用
  STRONG 版）——该银行已由 ConicCapVolume 落地，TSKAJXY 侧消费待其自身链接线。

## §1 闭合核验证据（本侦察实测，非转抄 docstring）

1. **零 sorry**：`grep -nE "^\s*sorry\b|:= sorry\b|\bsorryAx\b"` 于 PA23 exit=1
   （零命中）；文件内 30+ 处 "sorry" 字样全在 docstring/注记（含 :6370 已过时的
   "STILL sorry"）。
2. **构建新鲜**：PA23.lean mtime 10-10 13:36 < PackingAuto23.olean mtime
   10-12 15:50；PA15/PA17/PA12/ConicCapVolume olean 同批新鲜；olean 字节串含
   `p23_rev34_hull_form`/`p23_pivot_*`/`GRUTOTI` 全套 GT-6 符号。
3. **kernel 级 axiom 探针**（`lake env lean /dev/stdin`，import PA23 实测）：
   - `Kepler.Text.GRUTOTI` ⇒ `[propext, sorryAx, Classical.choice, Quot.sound]`；
   - **干净**（无 sorryAx）：`CONIC_CAP_INTER_CONVEX_HULL_4_GT_0`、
     `CONIC_CAP_WEDGE_EQ_0`、`volumeConicCapPos`、
     `VORONOI_LIST_3_SINGLETON_EXPLICIT`；
   - **有 sorryAx**（= GRUTOTI 的 taint 源，见 §3）：
     `AJRIPQN`、`HL_LE_SQRT2_IMP_BARV_1`、`MXI_EXISTS_concl`、`LEPJBDJ`、
     `HDTFNFZ`、`FINITE_MCELL_SET_LEMMA_2`、`MCELL2_PERMUTE_01`、
     `GRUTOTI1_concl`（PA2 冻结接口本体）与
     `GRUTOTI1_concl_discharged`（PackingConcl 现走线）。
   - 注：探针名是 `Kepler.Text.<名>`（各 PA 文件 `namespace Kepler.Text`，
     PA23:214），不是 `Kepler.Text.PackingAuto23.<名>`。
4. **capstone 装配**（PA23:6401-6421）：`p23_region_data_full` 一步供 r/d/c 数据 →
   volD_pos → sum_volD → pivot → setSum_mul_div → concl_arith，全链零 sorry。

## §2 HOL 证明解剖（Q2）

- **§H 结构**（GRUTOTI.hl:7506-7958，453 行）：per-cell 臂按 canonical 指标 i 分派
  ——i≤1 对边胞不可能（k≥2）；**i=3（:7577-7669）/ i=4（:7671-7786）= 反向 k=3/4
  本体**：vol>0 ⇒ 列表展开 + CARD_MINUS_DIFF_TWO_SET（:7612 等）计数矛盾；i=2
  （:7787 起）：u0=v0/u0=v1 前向-反向双支（:7810-7825），conic_cap ⊆ rcone_ge 链
  （:7831-7839）+ 楔体积式收账。
- **重度自动化 census**（§H 区间实测）：SET_TAC×23、REAL_ARITH_TAC×13、
  MESON_TAC×8、COND_CASES_TAC×6；**无 sos/nl 类重炮**。直译难度中等——真正
  工作量在 CARD 集合计数与测度/零测记账，不在解析计算。
- **核心数学思想一句话**：k=3/4 反向角是"分支真空"——在区域阈 (1,c) 处正测度迹
  （锥帽∩四点 hull 内部非空）经 B5 覆盖与 AJRIPQN 双胞唯一性迫使该胞以
  [u0;u1] 打头的表出现，与"无前向见证"假设直接矛盾，恒等式的前向证明于是适用。

## §3 Lean 存量盘点与剩余移植子清单（Q3）

### 3.1 pivot 相关 kit——全部已座（零成本）

| 件 | 落点 | 状态 |
|---|---|---|
| p23_pivot_mid_* 工具组 / p23_pivot_perm_pack / trunc2_form / setOfList4_form | PA23:4649-4781 | ✅ 已证 |
| p23_pivot_cell_nn（逐胞非零测）/ p23_pivot_cell_eq（前向见证恒等式） | PA23:4795 / 5142 | ✅ 已证 |
| p23_rev34_hull_form（SET-级 hull ⇒ 四点 hull + ¬Coplanar） | PA23:5420 | ✅ 已证 |
| p23_region_exists_c / p23_C_sub_rogers / p23_cover_C | PA23:1464 / 2003 / 2036 | ✅ 已证（cover 消费 AJRIPQN） |
| CONIC_CAP_INTER_CONVEX_HULL_4_GT_0 | PA15:2275（Kit D p15_box_pos:1951） | ✅ axiom 干净 |
| MCELL2_PERMUTE_01（反向 k=2 镜像） | PA14:822 | ✅ 本体证，taint 经 PA14:759 ynhyjit_p14 |
| ConicCapVolume 三 cap（volumeConicCap/Pos/Wedge） | ConicCapVolume.lean:902/961/1447 | ✅ 0 sorry，已喂 PA23 volD_pos + PA24:1594 |

### 3.2 GRUTOTI 链 taint 断流清单（剩余全部工作，无互相阻塞）

| # | 件 | 落点（现行号） | 档级 | 估 Lean 行数 | 共享域 |
|---|---|---|---|---|---|
| 1 | **AJRIPQN** | PA17:321 `sorry`（直接） | **M+/GIANT−** | **400-800** | GRUTOTI 专属入口；五阶段覆盖装配 HL AJRIPQN.hl:100-1048；输入件（MEASURABLE/BOUNDED/CLOSED_MCELL PA12、SLTSTLO、KIUMVTC/VORONOI_BALL2 PA5、BARV_3_EXPLICIT PA8、RVFXZBU/DDZUPHJ/QZKSYKG 等）大多已在树 |
| 2 | HL_LE_SQRT2_IMP_BARV_1 | PA15:580（直接） | S | 30-80 | GRUTOTI + REUHADY |
| 3 | FINITE_MCELL_SET_LEMMA_2 | PA15:1153（直接） | S-M | 60-150 | GRUTOTI + KIZHLTL |
| 4 | LEPJBDJ 内部三支（k3Subset/k2Case/rogersInterVLemma） | PA11:365/401/418 | S-M ×3 | 180-450 | LEPJBDJ 本体（PA11:472）已证，taint 从这三支流入 |
| 5 | MXI_EXISTS_concl | PA2:5478-5482（直接；PA7/PA13 各有拷贝） | M | 100-250 | B1 桥 + mxi 装置共享件；**证明体未探明，需单独侦察** |
| 6 | PA10 族（RVFXZBU:221/226、YNHYJIT:342/346、INTER_RCONE_GE_LE_lemma:433、MCELL_2_PROPERTIES_lemma1:445） | PA10 | S-M ×4 | 200-400 | HDTFNFZ（PA10:257）本体已证；族属 TSKAJXY/OXLZLEZ 时窗 |
| 7 | PA14 族（ynhyjit_p14:759、QZKSYKG1:907、QZKSYKG2:943） | PA14 | M ×3 | 150-300 | MCELL2_PERMUTE_01 的 taint 源；同属 marchal 置换共享域 |

**装配顺序建议**：无任何顺序依赖（全独立、全并行）。建议批次：
- **波 P-A（工程微件，≈0.1 批）**：PackingConcl discharge 改线（import PA23 +
  `exact PA23.GRUTOTI`）+ 删 PA24:6369-6398 拷贝 + 顺手清两条过时注记
  （PA23:732 VORONOI、PA23:6368-6385 volD_pos docstring）。
- **波 P-B（主波，1-2 批）**：AJRIPQN 单章移植（唯一大件）。
- **波 P-C（散件，1 批，与 P-B 并行）**：#2/#3/#4/#5（GRUTOTI 侧必要件）；
  #6/#7 归 TSKAJXY/OXLZLEZ 共享时窗，勿重复移植。

## §4 与"GT-3 其余两件"的关系判定（Q4）

| 件 | 用户假设 | 实测现状 | 对反向 pivot 的关系 |
|---|---|---|---|
| CONIC_CAP trio | PA15:818-828 sorried，p15_box_pos 路线 ~8 错 | **已落树且 kernel 干净**（现行号 PA15:2218/2266/2275，Kit D :1576 起，p15_box_pos :1951）；/tmp/gt3a_probeD.lean **已消失**（工作已吸收） | 无（GT-6 消费件，已供给） |
| grutoti_region（giant） | 待做 giant | **已证**（PA23:2610，GT-4b 2026-09-30；PA23 零 sorry 为其证据） | 无（其导出数据 p23_region_data_full PA23:3041 已喂 capstone） |
| AJRIPQN | PA17:310 sorried | **仍 open**（现行号 PA17:321） | 被 `p23_cover_C` 消费（PA23 全文件 21 处引用）；**只堵 axioms 干净，不堵章节闭合** |
| 反向 pivot | 待做 200-400 行 | **已闭合**（GT-6，PA23:5612 零 sorry） | — |

**依赖方向**：全部单向"taint 自上游流动"，无互相堵死；**全部可并行**。
GRUTOTI 章节闭合 ≠ 链 taint 断流：前者已达成，后者 = §3.2 七件。

## §5 量级与风险（Q5）

- **pivot 本体剩余 = 0 行**。用户估 200-400 行；实际落地 ≈1,060 行（GT-5 kit
  PA23:4643-5611 ≈969 行 + rev_k34 :5612-5706 ≈95 行），2026-10-10 两波完成。
- **GRUTOTI 链 taint 断流总账**：GRUTOTI 侧必要件 ≈ **800-1,600 行**
  （AJRIPQN 400-800 + 散件 #2-#5 约 370-930）；#6/#7（350-700）归共享时窗另计。
  批数：P-B 1-2 批 + P-C 1 批 + P-A 微件。
- **最大不确定点（可能"数学卡住"而非变长）**：仅 AJRIPQN 的五阶段覆盖装配
  （测度鸽笼 + 有限选取 + SLTSTLO1/2 的 k≤4 钉定 + 双胞同一性收口）——它是链上
  唯一非机械结构；其次 MXI_EXISTS_concl 体量未探明（陈述 pack_concl.hl:120-123，
  证明源在 marchal3 系，建议先做 1 小时侦察再排批）。
- **已消除的历史风险**：volD_pos 冻结假（SF-18 已修 + 一行填）；GT-5 预判的
  S₃-置换/ε-junk 钉定路线（GT-6 换覆盖路线避开）；VORONOI shim taint（已干净）。
- **残余文档债**：PA23:732、PA23:6368-6385 两条过时 docstring（不影响 kernel）。

## §6 立项建议

1. milestones §2 表"pivot 反向 k=3/4"行改记：**已闭合（GT-6，2026-10-10，
   PA23 零 sorry）**；"三件真数学"中本件出列，顶替入列的是 **AJRIPQN**
   （GRUTOTI 链最后一块真数学）。
2. 立即做 P-A 接线微件：PackingConcl:612 改指 PA23.GRUTOTI（全树零 importer、
   加 import 无环），使 GRUTOTI1_concl_discharged 的 axiom 面从"PA2 接口 sorry"
   收窄为 §3.2 七件 taint——这一步让 GRUTOTI 消费链（leaf-rank/REUHADY 侧）
   的账面立即诚实。
3. P-B AJRIPQN 按独立章移植（HL 1051 行 → Lean 400-800），先侦察其五阶段的
   SLTSTLO/QZKSYKG 输入件在树状态再开批。
4. 不要为 PA10/PA14 族单独立 GRUTOTI 项——它们是 TSKAJXY/OXLZLEZ 共享域，
   统一时窗一次移植两链受益。

---

关键文件：`lean/Kepler/Text/PackingAuto23.lean`（6423 行，0 tactic sorry；rev_k34
:5612、pivot :6221、capstone :6396）、`lean/Kepler/Text/ConicCapVolume.lean`
（1610 行 0 sorry）、`lean/Kepler/Text/PackingAuto15.lean`（Kit D :1576/:1951，
trio :2218/:2266/:2275）、`lean/Kepler/Text/PackingAuto17.lean`（AJRIPQN :321）、
`lean/scripts/packing/GRUTOTI.hl`（§H :7506-7958、B7 覆盖 :2631-2636、pivot 求和
:7961-8001）、`reference/flyspeck/text_formalization/packing/AJRIPQN.hl`（1051 行）、
`lean/Kepler/Text/PackingConcl.lean`（:612 现走线）。

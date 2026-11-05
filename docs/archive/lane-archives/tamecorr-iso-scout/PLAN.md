# PLAN — 前置判定（E）、首波（F）、风险（G）

## E. 前置判定

### E1. 是否需要 `jcajydu`？——**不需要**

- HOL `WMLNYMD.hl` 全文 `grep -n "JCAJYDU\|Jcajydu\|jcajydu"` = **零命中**（`logs/hol_counts.log`）。
- HOL 主定理证明体只 `MATCH_MP_TAC tame_correspondence1` 并消费 Oxaxucs 六件（:1503-1510）；`jcajydu` 是反方向（restricted hypermap → plane graph），由 `textCapstone` 另一分支消费，不在 W3 证明树内。
- Lean `tameCorrespondenceIso` 的陈述/证明体（`#print`，`logs/probes.log`）没有任何 `jcajydu` 引用；它是 `fun … => sorry`。
- 结论：W3 与 W2 可并行，**无先后依赖**。

### E2. 是否需要 `Reduction5` 链？——**不需要**

- 同上 `grep`：`Reduction5|reduction5|restricted_hypermaps_are_planegraphs` 在 `WMLNYMD.hl` **零命中**。
- W3 的图侧输入是假设 `good_graph_v4 g`（现已是忠实六合取）与 `iso H (hypermap_of_list (fgraph g))`；不构造图，不走 reduction。
- 结论：W3 不依赖 Reduction5；`jcajydu` 才依赖。

### E3. 是否需要 TameSpine 岛件可被 Assembly 消费？——**分两路**

机器事实（`logs/import_bfs.log`）：

- 岛 75 文件，**74 个传递 import `Kepler.Assembly`**；唯一例外 `TameOpposite1`（只 import TameLp）。
- 直接 import Assembly 的 5 个：`Keystone`、`GoodGraph`、`TameList1`、`TameList2`、`TameList3`；其余经 `TameList1/2/3` 传递。
- 反向：`Assembly` **不** import 任何 TameSpine 文件（BFS 0）；`LocalConcl` 当前也不 import 岛（BFS 0）。
- 所以当前无环；但 **W3 若落成一个 import 岛的新模块，Assembly 不能 import 它**（会把岛→Assembly 的边翻成环）。这就是“74/75 成环”的准确含义：不是现有环，而是**任何 Assembly 消费岛件的新边都会成环**。

W3 需要的岛件（若复用）：

| 岛件 | 位置 | 用途 | 可替代性 |
|---|---|---|---|
| `TameSpine.sumnCons` | `TameList45.lean:117` | `sumn_cons` | core `List.sum_cons` 一行，可不用岛 |
| `TameSpine.memFaceLemma` / `cardFaceOfList` | `TameList56.lean:318/:338` | list↔face 集的成员/基数 | 岛外无；需 de-Assembly 或自证（~100–200 行） |
| `TameSpine.listOfFaces` / `faceRep` | `TameList59.lean:100` / `TameList31.lean:152` | `list_of_faces` / 面代表 | 可自证（~50–100 行） |
| `TameSpine.hypIsoCardComponents` / `hypIsoEdgeNode` / `componentsIsoImage` | `TameList15.lean:185/:135/:170` | Oxaxucs 的 iso 支撑 | TameList15 在环后；但同类命题可在 W3 模块按 `Hypermap.Iso` 重证（~100–200 行） |
| `TameSpine.goodListNodesCondition2` | `TameList16.lean:791` | `good_list_nodes_condition` 的商列表特形 | 非 WMLNYMD 所需一般形；仍需一般版 |
| `TameSpine.faceMap_hypermapOfListG` | `TameList67.lean:349` | 一般 α 的 faceMap 律 | 可选（W3 载体是 `fgraph ℕ`） |

W3 **不**需要岛件的充分替代路线（推荐）：只用 `Kepler.Text.TameLp` + `Kepler.Graphs` + `Kepler.Text.TameCorrBase`。三者均不 import `Kepler.Assembly` 本体（TameCorrBase 头注与实测 import 只有 TameLp；`GoodList` 取自 Assembly-free 的 `Kepler.Assembly.GoodListDefs`），且 TameCorrBase 已给 `IsHypermapOfListTl` 的**唯一性/典范性**（把 `hIs : IsHypermapOfList g.fgraph H'` 归约到 `H' = hypermapOfList g.fgraph _`），全部标准三（`tamecorr-w1` 实测）。缺的 List_hypermap 5–7 件可在 W3 模块里自证（450–800 行，见 `SIZING.md`）。

结论：**不强制**等去 Assembly 化；但若要“零重证、复用岛件”，则必须先等 `island-deassembly-scout` GO。W3 可以先走“上游安全 + 自证缺口”路线开工。

### E4. W3 现在能不能独立开工？——**能开工；不能按现陈述收口**

**能独立开工的部分（不依赖 Reduction5 / jcajydu / 岛）**：

- 本体 56 个 prove 块中约 **46 个**只依赖 `Hypermap` 词汇与 `tame_defs` 常量（G1–G8 的 list 面除外，但都可以在 TameLp 的 `hypermapOfList` API 上重建）。
- G6 floor 18 件 + G7 sum/BIJ 4 件是**完全自足**的（只依赖 `Hypermap`、`TameLp.Adm1/2/3`、`Graphs.squander*`、`Nat.floor`），可以先做。
- 前置已就位：`TameLp.hypermapOfList`（:5188，`hypermapOfList_isHypermapOfListTl` :6139 标准三）、`TameCorrBase` 唯一性/典范性（8 件标准三）、`Graphs.tame`（:164）、`Assembly.GoodGraphV4` 已忠实化（SF-57…62）。

**不能收口的硬缺口（按严重度）**：

1. **`Adm3` 陈述保真（最高）**：`Assembly.Adm3` = `… → True`（:2101），TameLp/ HOL 版是 `… → aTame ≤ setSum …`（TameLp:443，`tame_defs.hl:124-127`）。主定理假设侧用的是弱版；HOL 证明的 floor 链消费 `adm_3`。**不修 `Adm3`，主定理无法按 HOL 路线证明**。修法：DEF-FIX，把 `Adm3` 尾逐字抄成 TameLp 体；改后其余 11 槽已 defeq，整个 `TamePlanarHypermap` 变 `rfl`，`b3` 桥可公开复用（同时 `b3` 的 `fun x _ _ => trivial` 尾必须改为 `ha3`，否则该私有证明会类型失败）。
2. **上游 List_hypermap 缺口 5–7 件**（`face_set_eq_list`/`components_hypermap_of_list`/`uniq_faces_of_list`/`uniq_list_of_elements`/`card_nodes_of_list`/`good_list_nodes_condition`/`face_of_list`）：TameLp/岛只覆盖一部分；要么自证（450–800 行），要么等岛去 Assembly 化后复用。
3. **上游 Oxaxucs iso 族 24 件**（614 HOL）：主定理直接吃 6 件，其余 18 件支撑。TameSpine 只有通用 `hypIso*`，**无** `tame9a_iso…tame13a_iso` 族；必须移植（1.04–1.29k Lean）。
4. **GoodGraphV4 上游安全**：Assembly 版已真化且与岛 `*Spine` 六件全部 `rfl`；但 W3 模块若不能 import Assembly，需抄 6 个 def（~60 行）或先 HOIST 到 Assembly-free 模块。**不是数学缺口**。
5. **`hIs` 陈述差**：Lean 用显式 `H'` + `hIs`，HOL 用 `iso H (hypermap_of_list …)`；由 `TameCorrBase` 唯一性等价，但陈述文本不是逐字；落库时按 SF/陈述注记处理。

**结论**：W3 现在可以发“上游安全本体波”（不需要 Reduction5/jcajydu/岛），但**主定理 `tameCorrespondenceIso` 的 `sorry` 不能在本波关闭**；关闭前必须完成 `Adm3` DEF-FIX（用户/编排者拍板），并选定 List_hypermap 缺口的自证或 de-Assembly 路线。

## F. 首波方案（E4 判“能开工”）

### W3-W1（推荐）：floor 机制 + nat 和助手（G6+G7）

- **目标件**（22 个 prove 块）：`floor_lemma`、`nfloor_exists`、`wt_floor_nn`、`wt_floor_le_wt`、`total_weight_floor`、`adm_1_floor_adm_1`、`FINITE_set_of_face_meeting_node`、`FINITE_set_of_n_meeting_node`、`set_of_n_meeting_node_union`、`b_tame_explicit`、`squanderVertex_explicit`、`vertextypes_explicit`、`no_except_empty`、`no_except_wfloor`、`set_of_exceptional_meeting_node_identity`、`adm_2_floor_adm_2`、`adm_3_floor_adm_3`、`tame_13_a_floor_tame_13_a`、`sumn_cons`、`sumn_nsum`、`uniq_facesAt_list`、`BIJ_NSUM`。
- **落点**：新模块 `lean/Kepler/Text/Wmlnymd/Floor.lean`（或单文件 `Kepler/Text/WmlnymdFloor.lean`），`import Kepler.Text.TameLp` + `import Kepler.Graphs.Tame`；**不 import Assembly，不 import TameSpine**。
- **前置**：`TameLp` 的 `Adm1/Adm2/Adm3`、`Tame9a`、`Tame13a`、`setOf*MeetingNode`、`setSum`；`Graphs` 的 `squanderFace/squanderVertex/squanderTarget/excessTCount`；Mathlib `Nat.floor_le/lt_floor_add_one`；core `List.sum_cons`、`Finset.sum_bij`。需新定义 3 个本地件：`nsum : Set α → (α → ℕ) → ℕ`（`Finset.sum` 包装）、`nfloor d x := ⌊x*d⌋₊`、`wtFloor`（逐字抄 HOL :878）。
- **预估行数**：G6 810–945 + G7 82–99 ≈ **900–1,050 Lean 行**（1.8–2.1x 区间）。
- **验收**：
  1. `nice -n 19 lake env lean Kepler/Text/Wmlnymd/Floor.lean` RC=0、0 error、0 `sorry`/`axiom`；
  2. 每个公开件 `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`（无 `sorryAx`）；
  3. 与 HOL 逐条对表：22 条语句逐字（载体折算表：`sumn`↦`List.sum`、`nsum`↦本地 `Finset.sum`、`CARD`↦`Set.ncard`、`real`↦`ℝ`、`&`↦`Nat.cast`）；
  4. 常数表逐值核对（`bTame` 15 值、`squanderVertex` 15 值、`squanderFace` 5 值、`tgt=15410/10000`）；
  5. FQN 查重（`lean/scripts/fqn_scan.py` 同款）零硬撞。
- **止损**：单件超过 ~450 行或 3 轮结构性卡死即停（AGENTS §7）；`adm_2_floor_adm_2`（65 HOL）若 >250 Lean 行、`set_of_n_meeting_node_union` 若 >150 行，单件止损并交班。不得为过 compile 改陈述/加 `sorry`。
- **为什么先做 floor 而不是 list 对应**：G6+G7 是最大自足块（505 HOL / 31%），不碰 `Adm3` 争议的“假设侧传播”（floor 只消费 `tame_9a`/`adm_*` 本身），也不碰 74/75 环；产出的 `nsum/BIJ_NSUM/wt_floor` 是 G8 `tame13a_correspondence` 的硬前置。首波落地后 W3 的“最大单块风险”消失。

### W3-W1'（并行备选，若想先通主链）：list 词汇 + facesAt 桥（G1+G2 的 def 部分）

- 目标：11 个 list 定义（`tame11a_list`…`tame13a_list`）+ `facesAt_list` 的 filter/长度桥 15 件的一部分；落点同上；预估 **500–700 行**。
- 前置：`hypermapOfList`、`elementsOfList`、`facesAt`、`GoodGraphV4`（本地副本或 HOIST）。
- 风险：依赖 List_hypermap 缺口的 5–7 件；建议放到 floor 波之后，或与 floor 并行但由另一 lane 承担。

### W3-W0（可选，0.3 lane）：HOIST `GoodGraphDefs`

把 `Assembly` 的六个忠实 def（`GoodListNodes/FinalGraph/AllUniq/GoodFacesV3/VerticesSet2Eq/GoodGraphV4`）搬到新 Assembly-free 模块 `Kepler.Text.GoodGraphDefs`，Assembly 与岛都改为 import 它（DEF-FIX，零语义变更、零证明）。收益：W3 不再复制第三份 def，岛去 Assembly 化也少 6 个声明。若编排者不愿动 Assembly import 面，退化为 W3 模块内逐字复制 + 末尾 `rfl` 桥。

## G. 风险

1. **`Adm3` 陈述风险（最高，必须先裁）**：Assembly `Adm3` 尾 `True` 使 `TamePlanarHypermap` 严格弱于 HOL/TameLp。若按现陈述硬做，HOL 的 floor 路在 `adm_3_floor_adm_3` 断；若绕过 `Adm3` 另证，等于证一个比 HOL 强的命题，风险与工作量都不可控。**动作**：DEF-FIX 提案（把尾逐字改真），不动定理文本；改后全 def `rfl`，一劳永逸。禁止在 W3 内私自改陈述。
2. **`tame` 定义保真**：`Graphs/Tame.lean:164` 与 HOL `import_tame_classification.hl:116` 六合取逐项对得上（tame9a/10/11a/11b/12o/13a），无缺项；差异只在表示（Lean `Bool`+list、`Face` 结构、`Nat`；HOL Prop+set、`num list#bool`）。重复面/顶点对 `∀` 无影响；`tame13a` 两边都按 `faces` 列表求和，忠实。**风险低**，但落库验收要附逐字对照表。
3. **两份 `TamePlanarHypermap` / 孪生组件**：12×2 个 `Tame*` def；11 槽 defeq、`Adm3` 不 defeq。任何“证明了一半发现用错版本”的返工都昂贵。**动作**：W3 统一以 `TameLp.TamePlanarHypermap` 为真源；Assembly 侧只留 `Adm3` 修好后的 `rfl` 桥。
4. **“移植完成但 Assembly 用不上”（环）**：岛 74/75 文件传递 import Assembly；W3 若 import 岛并被 Assembly import，即成环。**动作**：(a) W3 上游安全模块（只 import TameLp/Graphs/TameCorrBase）；或 (b) 等 island-deassembly GO。落库前用 `logs/import_bfs.log` 同款 BFS 复核“Assembly 不 reach 岛”。
5. **上游漏算**：Oxaxucs 614 行 / 24 件 + List_hypermap 5–7 件是硬上游；只按 1,515 行排波会低估 2–2.5 倍。**动作**：按 `SIZING.md` 的 4.2–5.4k 端到端口径排期；首波只承诺 floor（900–1,050），不承诺主定理。
6. **常数表“非精确 ×10⁴”陷阱**：`dTame/bTame/squanderFace/squanderVertex/tgt/squanderTarget/excessTCount` 在 Assembly / TameLp / Graphs / HOL 四处同值；错一格不报编译错。更有隐蔽陷阱：**实数表与 nat 表不是精确 ×10⁴**，差额是 floor 损失上限。例：`aTame=0.63` 但 `excessTCount=6295=6300−5`（(5,0,1) 型 5 个三角面，逐项 floor 各损失 <1）；`bTame(p,q)*10000 − squanderVertex(p,q) = p+q`（如 0.618*10000−6177=3、1.2851*10000−12846=5）。HOL 的 `d_tame_squanderFace`/`b_tame_squanderVertex`/`a_tame_excessTCount` 三件被 `(* … *)` 注释掉，正因等号不成立（S10 只剩 `tgt_squanderTarget`）。**动作**：首波验收逐值核对 slack；严禁把 `bTame*10000 = squanderVertex` 或 `aTame=excessTCount/10000` 当引理用。
7. **`hIs` 与 HOL `iso` 陈述差**：Lean 主定理多一个显式 `H'`/`hIs`；`TameCorrBase` 已给唯一性/典范性，等价可证，但定理文本不是 HOL 逐字。**动作**：落库时在 STATEMENT-FIX/NOTES 登记；不得为“好看”改回 HOL 形状（会破坏 textCapstone 消费）。
8. **HOL 同名重复绑定**：WMLNYMD `sumn_cons`（:1305）与 `tame_list.hl:12593` 同名；WMLNYMD 版覆盖前者。Lean 用 core `List.sum_cons` 即可，不要引入两份。其他 WMLNYMD 名称与岛无硬撞（namespace 隔离），但 camelCase 命名要统一前缀 `Wmlnymd`。
9. **`nsum` 语义**：HOL `nsum` 对集合按 `CARD`/`sum` 约定；Lean 若用 `Finset.sum` 需 `Set.Finite`，无限集约定 0（与 HOL `sum` 一致）。首波必须先把 `nsum` 的 junk-value 约定写死（建议 `if h : s.Finite then h.toFinset.sum f else 0`，与 TameLp `setSum` 同款）。
10. **Assembly 大文件手术**：最终仍要在 `Assembly.lean` 内把 `sorry` 换成证明项（或将证明模块 import 进 Assembly 并在原位置调用）。后者需要 Assembly 能 import 该模块——这正是风险 4。**动作**：W3 的第一天就决定“in-place proof”还是“upstream module + Assembly import”，不要等移植完再决定。

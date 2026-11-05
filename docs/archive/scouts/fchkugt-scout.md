# FCHKUGT 测绘（PA18:6685 GIANT，2026-10-23，fchkugt-scout 车道交付）

> 快照：`lane_snapshots/fchkugt-scout/`。**关键发现：GIANT 名不副实两层。** (1) FCHKUGT 本体
> HOL 97 行是纯装配（0 新数学），真债面在它脚下的 **FUEIMOV 族 7 件**（HOL 合计 ~447 行，
> Lean 估 430–1030，中位 ~700）；(2) 两件工程注记已过时——FUEIMOV_K"等 PA17.AJRIPQN"实则
> AJRIPQN 已真证且在 PA18 闭包内，MCELL4_EXTREME_POINT"EDGE_FIRST-style kit"实则与 BG 件
> 无关。**FCHKUGT 子树与 BG（MCELL2/3_EDGE_FIRST + TWO_REARRANGEMENT_LEMMA_ALT）值级完全
> 分离**，BG 落库非前置。陈述零误植。唯一政策闸：AJRIPQN 的 axiom 洁净度需首建实测。
> 5 波，无真数学缺口，成功率 ~80–85%；W1/W2 可在 BG 落库当天开工（不同施工段，仅文件排队）。

---

# PA18 `FCHKUGT` 只读侦察报告（SCOUT）

> 车道：池 A/池 C 交汇剩余硬件只读侦察（完全只读，零构建、零 tracked 写、零 git）。
> 基线：main 工作树 HEAD（实测；SF-50/CFFONNL 修复与 2026-10-23 pa25wim 复评注记已在树）。
> 交付：本文件、`DEP_MAP.tsv`、`WAVES.md`、`MD5SUMS`。
> 方法：leaf_cell.hl:3432-3528 证明体逐 tactic 读 + 全部具名依赖 HOL 定位 + Lean 对应件
> 逐件 grep 定位并查 sorry；PA17/PA14/PA5 债链延伸核查；PA25/PA24 消费区逐条对账；
> e2e-reachability-map.tsv 实查。

## 0. 结论速览

1. **GIANT 实测 = "GIANT 名下的装配族"。** FCHKUGT 本体（HOL 97 行）六成以上是
   EL/HD/TL/CONS_11 改写噪声，骨架是完全机械的四分支装配；真正的体量在其依赖
   **FUEIMOV_3（HOL 104）+ FUEIMOV_4（HOL 85）+ FUEIMOV_K（18）+ MCELL4_EXTREME_POINT（21）
   + MXI kit 三件（55+28+24）**，全族 HOL ~447 行，按 BDXKHTW 折算（×1.5–3）Lean
   **430–1030 行（中位 ~700）**，5 波。**真数学缺口 = 0**：最深的两处"疑似硬骨头"
   （MXI 的 sqrt-2 球分离、FUEIMOV_K 的 mcell 唯一性）落地后都是已证 kit 上的记账。
2. **两大事实修正（填证任务书据此行文）：**
   - **FUEIMOV_K（PA18:5334）的 NEEDS 注记"the other half is PA17.AJRIPQN (still sorry
     in PackingAuto17, out of PA18 scope)"已过时**：AJRIPQN（PackingAuto17.lean:931）
     于 2026-10-12 关账真证（五阶段装配 `p17_ajripqn_of_pieces` + SF-38 tail-fixed
     `QZKSYKG2`），且 **PA18 直接 `import Kepler.Text.PackingAuto17`（:155）**，闭包内
     可用。FUEIMOV_K 因此降级为 10–25 行装配（HOL 体 :2732-2749 仅 18 行）。
   - **MCELL4_EXTREME_POINT（PA18:5342）的 NEEDS 注记"needs the EDGE_FIRST-style rigidity
     kit"是误导**：HOL 体（leaf_cell.hl:2779-2810，21 行）实际只消费 FUEIMOV_K +
     CC_CELL_CONVEX_HULL_INJ（已证）+ SET_OF_LIST_CC_UH（已证），与 BG 的
     MCELL2/3_EDGE_FIRST **无关**。10–25 行。
3. **与 BG 波的接口 = 零值级耦合。** FCHKUGT 不消费 MCELL2/3_EDGE_FIRST、不消费
   TWO_REARRANGEMENT_LEMMA_ALT（实测在 leaf_cell.hl:**3104-3111**，是 QZKSYKG.hl:131
   `TWO_REARRANGEMENT_LEMMA` 的 MESON 薄壳；FCHKUGT 及其全部依赖的 HOL 位置都在 :3104
   之前或与之无引用边）、不消费 pa18w4_azim_loc（PA18:7354，方位角局部窗口件——本链
   无任何方位角连续性内容）。FUEIMOV_3/4 的 HOL 体也不消费 MCELL2/3_EDGE_FIRST（:3114-3337
   依赖清单逐项核对，无 FUEIMOV 边）。**双向独立；BG 的 public 件 FCHKUGT 车道一件都不
   需要，不存在"等 BG"的共享子树**；唯一共享 = PA18 文件排队（per-file build）+ 双方
   共同消费的已证 kit（QZKSYKG1 全件、RVFXZBU 全件、LEFT_ACTION_LIST_2/3_EXISTS、AJRIPQN）。
4. **误植检查（零容忍）：本件 5 前提 + 结论与 HOL 逐字一致，零误植。** ccA0/cc_A0 定义
   一致（affGt {EL0,EL1} {EL2}）。FUEIMOV_3 的茎前提 Lean 用 `(ccUh V ul).getD k 0` 编码、
   HOL 用 `EL k ul`——经 EL_CC_UH（已证 :3220）等价，是全文件统一的记法形差，非误植。
   上游抽查：CFFONNL 已是 SF-50 修复后的 HOL 原序（hne : `X ≠ ccCell V ul`，:4638 真证），
   恰为 FCHKUGT 所需形。**无需任何 SF 通道件。**
5. **唯一政策风险 = 标准-三。** FUEIMOV_K 消费 AJRIPQN；AJRIPQN 链 = `p17_ajripqn_of_pieces`
   + `p17_ajripqn_of_tailfix` + `qzksykg1_p17`/`qzksykg2_p17`（shim→PA14.QZKSYKG1 :1936
   真证、QZKSYKG2 :3034 真证，:3034 之后全文件零 `sorry`）+ TIWWFYQ（PA5:847 真证——
   PA17 docstring 的"PA5:581, sorry"亦过时）。**PA17 全文件零代码级 `sorry`**；但 AR 车道
   （poola-harvest DELIVERY）实测 PA2 `XNHPWAB1_concl`(:5405)/`MXI_EXISTS_concl`(:5484)
   在册 sorry 经 PA12 流入含 PA17 的闭包——AJRIPQN 的具体证明子树是否被污染无法纯静态
   判定，**W1 开工首建时 `#print axioms AJRIPQN` 实测**：只含标准三则全链标准-三；
   若含 sorryAx，则本 lane 落库需编排者按"消费在册 sorry"口径裁决（SF-51 模式闸门明示）
   或等 PA2 两件清偿。这不改变工作量估计，只改变落库口径。
6. **消费面（grep 全库实测）：Lean 代码调用点唯一 = PA25:1987 `p25_leaf_azim_inj`**
   （:1963，零裸 sorry、吃 FCHKUGT 的 sorryAx——**FCHKUGT 落证后本件零编辑自动转净**）
   → `LEAF_RANKING_LEMMA`（:1992，同）→ leaf_rank 基建。间接：`REUHADY`（PA25:1797
   sorry）的 azim≠0 wedge-二择支（HOL OXLZLEZ3:863）→ `LEAF_RANK_REUHADY`（PA25:2611，
   **e2e tsv 行 102**，parent `c_4_azim_mcell_dih_y`；其 NEEDS"唯一债=REUHADY"——REUHADY
   还另欠 REUHADY1（PA24 污染闸，AR 车道在记）+ EWYBJUA（池 B 可选 W6））。第三消费者
   `CC_3_AZIM_LT_PI_COPLANAR`（PA25:9444 sorry，HOL OXLZLEZ3:8704 消费 FCHKUGT）。
   `PA24 无现役消费者`（:116/:13006-13145 孪生注记是历史记账；p24_REUHADY_nondeg 两支
   已绕开 FCHKUGT 真证）。**W3 的 FUEIMOV_4 有第二个下游：PA25:4377 WEDGE_UNIQUE_CC_CELL**
   （其 NEEDS 点名"FUEIMOV_4(PA18:5213→实际:5364)，独立侦察 lane 建议"——即本车道）。
7. **建议立项时机**：W1+W2 现在立项（不等 BG）；W3 跟 W1；W4 跟 W1+W2；W5 收口。
   若编排者要"最少波次解锁最多直源"：本 lane 单独清偿即让 PA25 侧 p25_leaf_azim_inj /
   LEAF_RANKING_LEMMA 两件零编辑转净，并把 LEAF_RANK_REUHADY 的债面收窄到
   REUHADY1(PA24)+EWYBJUA 两件具名外部锚。

## 1. 陈述精确化

### 1.1 FCHKUGT（PA18:6685 sorry ↔ leaf_cell.hl:3432-3528）

Lean（现行冻结形，前提顺序与 HOL 完全一致）：

```
theorem FCHKUGT {V : Set V3} {u0 u1 u2 u2' : V3} (hs : saturated V) (hp : Packing V)
    (hA : ccA0 [u0, u1, u2] = ccA0 [u0, u1, u2'])
    (hl1 : leaf V [u0, u1, u2]) (hl2 : leaf V [u0, u1, u2']) : u2 = u2'
```

数学内容：**cc_A0 单射性**。同一茎 [u0,u1] 上两片叶 u2、u2'（都是 leaf，即饱和 packing
里的 Voronoi 顶点叶），若两者的开叶锥 cc_A0 = affGt {u0,u1} {·} 相同（即 u2' 与 u2 张开
同一位侧面），则 u2' = u2。这是"茎 + 位侧面 ⇒ 叶唯一"的叶胞刚性核心，位于
STEM_EDGEX（茎边在胞内）之后、AZIM_BASE_SHIFT_LE/WEDGE_GE_SPLIT（PA18:6694/:6706，均已
真证）之前的 leaf-cell 链脊背上。

定义对齐：HOL `cc_A0 ul = aff_gt {EL 0 ul, EL 1 ul} {EL 2 ul}`（leaf_cell.hl:1139-1140）
↔ Lean `ccA0 ul = affGt {ul[0]!, ul[1]!} {ul[2]!}`（PA18:1102）。一致。

### 1.2 误植检查明细（对照池 A/池 B 教训）

| 件 | Lean 前提序 vs HOL | 结论 | 判定 |
|---|---|---|---|
| **FCHKUGT** | 5/5 一致（sat/pack/ccA0 等式/leaf×2，实参表 [u0,u1,u2] 与 [u0,u1,u2'] 逐字同） | u2 = u2' 一致 | **无误植** |
| ccA0 定义 | affGt {0,1} {2} ↔ aff_gt {EL0,EL1} {EL2} | — | **一致** |
| CFFONNL（上游） | SF-50 后 = HOL 原序 `hne : X ≠ ccCell V ul`（:4638，真证） | 交换序结论 | **一致（已修复）** |
| FUEIMOV_4 | 8/8（sat/pack/leaf×2/ccCell 等/stem/ke=4/ul≠vl） | getD 编码 ↔ EL 编码经 EL_CC_UH 等价 | **无误植** |
| FUEIMOV_3 | 7/7（sat/pack/leaf×2/ke=3/茎集相等/ccCell 等） | ul = vl 一致；茎前提 getD↔EL 记法形差（等价） | **无误植** |
| FUEIMOV_K / MCELL4_EXTREME_POINT / MXI_NOT_IN_V / MCELL_V_INTER_EXTREME / MCELL_EXTREME_DIFF_V | 各 4-6 前提逐一对照 | 一致 | **无误植** |
| CC_CELL_NOT_COPLANAR_EXTREME | 条件 pp 形（if ccKe=3 then mxi else getD 3）与 HOL :2622 同 | ¬Coplanar 一致 | **无误植** |

### 1.3 FCHKUGT HOL 证明骨架（:3436-3527，四分支装配）

核心算术事实（贯穿全证明）：**前提 hA 字面上就是
`affGt {u0,u1} {u2} = affGt {u0,u1} {u2'}`**（两锥作为集合相等）。

1. **茎不退化**（:3436-3445）：`~(u0 = u1)`，由 STEM_EDGEX [u0,u1,u2]（已证 :6641，
   紧邻前件）+ edgeX 成员展开。
2. **茎交换叶**（:3446-3448）：ZASUVOR（已证 :2345）给 `leaf V [u1,u0,u2]`（供分支 d 的
   FUEIMOV_3 第二支的 hl2）。
3. **CFFONNL 二择**（:3449-3463）：取 X := ccCell V [u0,u1,u2']、ul := [u0,u1,u2]。
   前提供给：X ∈ mcellSet（CC_CELL_IN_MCELL_SET，已证 :5015）；edge
   {u0,u1} = {EL 0 [u0,u1,u2'], EL 1 [u0,u1,u2']}（STEM_EDGEX 作用在叶 [u0,u1,u2'] 上）；
   hA : X ∩ ccA0 [u0,u1,u2] ≠ ∅（NUNRRDS_0 [u0,u1,u2']——已证 :3236，
   `ccA0 ul ∩ ccCell V ul ≠ ∅`——经全局 ccA0 相等改写）。TAUT 改写
   `(a∧b∧~c ⇒ d) ⇔ (a∧b ⇒ c∨d)` 后得二择：
   `ccCell [u0,u1,u2'] = ccCell [u0,u1,u2] ∨ ccCell [u0,u1,u2'] = ccCell [u1,u0,u2]`。
4. **ccKe 二分**（:3464-3466）：CC_KE_34 [u0,u1,u2']（已证 :3038）⇒ ccKe = 3 ∨ 4。
5. **case k=3**（:3467-3478）：二择两支各配 FUEIMOV_3——
   支 c：FUEIMOV_3 [u0,u1,u2'][u0,u1,u2]（ke'=3、同茎、cell 相等）⇒ 表相等 ⇒ u2'=u2；
   支 d：FUEIMOV_3 [u0,u1,u2'][u1,u0,u2]（hl2 = ZASUVOR 的交换叶；茎集
   {u0,u1}={u1,u0} 经 PAIR_EQ_EXPAND）⇒ u2'=u2。
6. **case k=4（反证 u2 ≠ u2'）**（:3479-3503）：二择两支各配 FUEIMOV_4——
   支 c：FUEIMOV_4 [u0,u1,u2'][u0,u1,u2]（ul≠vl 由 u2≠u2' 的 CONS_11 注入）结论
   `ccUh V [u0,u1,u2] = [u1,u0,getD3,u2']`，与 LIST_OF_CC_UH（已证 :3315）
   `ccUh V [u0,u1,u2] = [u0,u1,u2,getD3]` 对位 ⇒ u0 = u1，与第 1 步矛盾；
   支 d：FUEIMOV_4 [u0,u1,u2'][u1,u0,u2] + LIST_OF_CC_UH [u1,u0,u2] ⇒
   **u2 = (ccUh V [u0,u1,u2']).getD 3 0**（u2 是 ke'=4 胞的第 4 极点）。
7. **共面性收口**（:3504-3527）：由支 d 方程 + ccKe=4，CC_CELL_NOT_COPLANAR_EXTREME
   （已证 :5193，pp := u2 走 getD 3 支）给 `¬Coplanar {u0,u1,u2',u2}`。但
   **u2' ∈ affGt {u0,u1} {u2'}**（X_IN_AFF_GT_X，x ∈ affGt S {x}）经 hA 改写为
   **u2' ∈ affGt {u0,u1} {u2}**，再 AFF_GT_SUBSET_AFFINE_HULL ⊆ affineSpan {u0,u1,u2}
   ⇒ Coplanar {u0,u1,u2,u2'}——矛盾。∎

**全证明无一处新数学**：唯一"实质"引理是 FUEIMOV_3/4（其自身也是记账 + chi_msb 符号
论证，见 DEP_MAP）。

### 1.4 FUEIMOV_3 / FUEIMOV_4 骨架（本 lane 真正的体量）

- **FUEIMOV_4**（HOL :2810-2894）：FUEIMOV_K ⇒ ke(vl)=4；MCELL4_EXTREME_POINT ⇒
  两胞 4 极点集相等；STEM_OF_LEAF + 茎相等 ⇒ 茎对二择（同序/交换）；每支用
  LENGTH4_SET2 / LENGTH4_SET2_SWAP01（已证 :5095/:5143）从"4 元集共享 2 元"读出
  EL 2/EL 3 的对应，交叉情形用 K4_CHI_MSB_POS（已证 :3374，第 4 极点 chi > 0）+
  chi_msb_swap_23/chi_msb_swap_01（已证 :2726/:2717）的符号翻转排除；LIST_OF_CC_UH
  收口成 ccUh vl = [EL 1 ul; EL 0 ul; EL 3 (cc_uh ul); EL 2 ul]。
- **FUEIMOV_3**（HOL :3000-3103）：FUEIMOV_K 对称引 ke(vl)=3；CC_CELL_CONVEX_HULL_INJ
  （已证 :5311）⇒ 4 极点集相等；MCELL_EXTREME_DIFF_V + MCELL_V_INTER_EXTREME（两件
  等 MXI_NOT_IN_V）剥掉 mxi 得 {EL0,EL1,EL2} 三元集相等；CARD4_IMP_DISTINCT（**树内
  缺名**，用 GBEWYFX :2053 的茎两两不等替代）+ CC_CELL_EXTREME_CARD（已证 :5269）记账；
  茎对二择后第二支用 CELL3_NONDEG（已证 :3443）+ chi_msb_swap_01 符号排除；LENGTH3
  收口 ul = vl。
- **MXI kit**（MXI_NOT_IN_V HOL :2894-2948）：MXI_IN_VORONOI_LIST（已证 :3884）+
  EL_CC_UH（已证 :3220）+ BARV_SUBSET/BARV_IMP_HD_IN_SET_OF_LIST（PA2 私有孪生
  p2g_BARV_SUBSET:716 / p3a_BARV_SUBSET:4982，或 def 级重写 3-5 行）+ sqrt2 < 2 实数
  算术 + packing 定义（球分离）+ DIST_REFL。**无新数学**——"sqrt-2 距离 vs packing 球
  分离"在 HOL 里就是 MXI_IN_VORONOI_LIST 供点 + packing 定义反证。
  MCELL_V_INTER_EXTREME（:2949-2976）/ MCELL_EXTREME_DIFF_V（:2977-3000）是它的
  两条 20-30 行集合论推论。

## 2. 依赖链全图与行数对账

### 2.1 行数实测

| 口径 | 行数 | 说明 |
|---|---|---|
| FCHKUGT 本体 HOL | 97 | :3432-3528；≥60% 为 EL/HD/TL/CONS_11 改写噪声 |
| FUEIMOV 族 HOL | 320 | FUEIMOV_K 18 + MCELL4_EXTREME_POINT 21 + FUEIMOV_4 85 + FUEIMOV_3 104 + MXI kit 107（含 V_INTER 28 + DIFF_V 24） |
| 微件 HOL 等价 | ~30 | AFF_GT_SUBSET_AFFINE_HULL 复制 + X_IN_AFF_GT_X 复制 + BARV 微件 2 + CARD4 替代 |
| 全族 HOL 合计 | **~447** | — |
| Lean 估（×1.5–3） | **430–1030** | 中位 ~700；与池 B 同量级，5 波 |
| wim 报告口径 "FCHKUGT GIANT 97 行" | 97 | 只指本体；**不含脚下 FUEIMOV 族**——任务书"填证车道"须按全族立项 |

### 2.2 依赖状态总表

见 `DEP_MAP.tsv`（41 行）。要点：(a) 已证 **24 件**（全部实测定位+查 sorry）；
(b) 机械移植 **7 件**（FUEIMOV_K、MCELL4_EXTREME_POINT、MXI_NOT_IN_V、
MCELL_V_INTER_EXTREME、MCELL_EXTREME_DIFF_V、FUEIMOV_4、FUEIMOV_3）+ 本体；
(c) 桥/微件 **4 件**（AFF_GT_SUBSET_AFFINE_HULL 本地复制【公版 :9812 在 :6685 之后，
前向不可用；私有孪生 :7808 同】、X_IN_AFF_GT_X 本地复制【LocalAuto5:7702 真证但
LocalAuto5 无人 import、不在闭包】、BARV 微件 2、CARD4_IMP_DISTINCT 用 GBEWYFX 替代）；
(d) 真数学缺口 **0 件**。

关键已证锚（本会话逐件核实 PROVEN，行号为现 HEAD）：
STEM_EDGEX:6641、ZASUVOR:2345、CFFONNL:4638（SF-50 后原序）、CC_CELL_IN_MCELL_SET:5015、
NUNRRDS_0:3236、CC_KE_34:3038、LIST_OF_CC_UH:3315、SET_OF_LIST_CC_UH:3323、
STEM_OF_LEAF:~5346、CC_CELL_NOT_COPLANAR_EXTREME:5193、CC_CELL_EXTREME_CARD:5269、
CC_CELL_CONVEX_HULL_INJ:5311、K4_CHI_MSB_POS:3374、chi_msb_swap_01:2717、
chi_msb_swap_23:2726、CELL3_NONDEG:3443、MXI_IN_VORONOI_LIST:3884、EL_CC_UH:3220、
LENGTH4_SET2:5095、LENGTH4_SET2_SWAP01:5143、GBEWYFX:2053、CC_CELL_NOT_NULLSET:5185、
AJRIPQN（PA17:931，PA18 import :155）、QZKSYKG1（PA14:1936）、QZKSYKG2（PA14:3034，
:3034 后全文件零 sorry）、TIWWFYQ（PA5:847）、KIUMVTC（PA5:817）。

### 2.3 与 BG 波的接口（任务书第二问，逐条回答）

- **FCHKUGT 是否消费 TWO_REARRANGEMENT_LEMMA_ALT：否。** 实测 TWO_REARRANGEMENT_LEMMA_ALT
  在 leaf_cell.hl:**3104-3111**（不是 :3114-3374——那是 MCELL2_EDGE_FIRST 的区间），本体
  是 `BY(MESON_TAC[Qzksykg.TWO_REARRANGEMENT_LEMMA])` 的薄壳（正主在 QZKSYKG.hl:131）。
  FCHKUGT 及其全部依赖（FUEIMOV_3/4/K、MCELL4_EXTREME_POINT、MXI kit、STEM_EDGEX、
  ZASUVOR、CFFONNL、CC_KE_34、NUNRRDS_0、CC_CELL_* 族）的 HOL 证明体没有任何一处引用它。
  **BG 移植的该 public 件与本 lane 无关，不重复规划、也不构成接口。**
- **FCHKUGT 是否消费 MCELL2/3_EDGE_FIRST：否**（双向：MCELL2/3_EDGE_FIRST 的 HOL 体
  :3114-3337 消费 QZKSYKG1/RVFXZBU/LEFT_ACTION_LIST_2/3_EXISTS/MCELL2/3/4_EDGE/
  TWO_REARRANGEMENT_LEMMA_ALT 等，无 FUEIMOV/FCHKUGT 边）。MCELL4_EXTREME_POINT 的
  "EDGE_FIRST-style kit" NEEDS 注记经 HOL 实体核对为**误导**（见 §0.2）。
- **FCHKUGT 是否消费 pa18w4_azim_loc（PA18:7354）：否。** 全链无方位角连续性/局部窗口
  内容；azim 侧工作全部在消费者（PA25 p25_leaf_azim_inj 已用 azim_eq_azim_iff_alt 自备）。
- **BG 落库后可直接消费的件（名字、陈述形）：空集。** 本 lane 一件 BG 产出都不吃；
  反之 BG 也不吃本 lane。两 lane 只共享 (i) PA18 per-file build 排队，(ii) 共同消费的
  已证 kit（QZKSYKG1 全件、RVFXZBU 全件、LEFT_ACTION_LIST_PROPERTIES、AJRIPQN——今日
  已净或在树）。
- **MCELL2/3 是否共享子树：不共享，"可独立"，无"等 BG"项。** 施工段物理不重叠：
  本 lane PA18 :5334-5396 + :6685；BG :5405-5480。文件排队规则见 WAVES.md。

## 3. 消费面（FCHKUGT 清偿的下游；grep 全库 + e2e tsv 实查）

```
FCHKUGT(PA18:6685) 落证
  ├─► p25_leaf_azim_inj(PA25:1963, 调用点:1987)   [零编辑自动转净]
  │      └─► LEAF_RANKING_LEMMA(PA25:1992)         [零编辑自动转净]
  ├─► REUHADY(PA25:1797 sorry) azim≠0 wedge-二择支  [还欠: REUHADY1(PA24 污染闸) + EWYBJUA(池B W6)]
  │      └─► LEAF_RANK_REUHADY(PA25:2611)           [e2e tsv 行 102, parent c_4_azim_mcell_dih_y]
  └─► CC_3_AZIM_LT_PI_COPLANAR(PA25:9444)           [HOL OXLZLEZ3:8704 消费; Lean 现 sorry :9452]
W3 的 FUEIMOV_4 落证
  └─► WEDGE_UNIQUE_CC_CELL(PA25:4377)               [其三重债之一; 另两债 MCELL4_FULL_WEDGE/MCELL4_FI 非本 lane]
```

- e2e 直源：LEAF_RANK_REUHADY 在 `docs/e2e-reachability-map.tsv` **行 102**
  （AR 车道 DELIVERY 写"map:92"已漂）。REUHADY 本体（PA25:1797）不在 e2e 表独立行
  （它经 LEAF_RANK_REUHADY 与 real_model 链间接计价）。
- PA24：无现役消费。PA24:116 与 :13006-13145 的 "FCHKUGT/EWYBJUA 同名孪生仍 ported
  sorry" 是历史记账；p24_REUHADY_nondeg 的 (α)/(β) 两支已于 2026-10-08..12 波绕开
  FCHKUGT 真证（其 heX 用 mcellSet 楔二择假设直供）。**勿把 PA24 孪生注记当现役债。**
- PA18:114 文件头注记（"the MCELL*_EDGE_FIRST/FCHKUGT rigidity kit" 在 Still-sorry 清单）
  是 lane 记账，非代码依赖。

## 4. 波次计划与天花板

见 **`WAVES.md`**。骨架（5 波，430–1030 行，中位 ~700；无 (d) 缺口）：

- **W1**（FUEIMOV_K + MCELL4_EXTREME_POINT，30–90 行）：AJRIPQN 接线（PA17 已证，
  闭包内）+ CC_CELL_NOT_NULLSET + CC_CELL_CONVEX_HULL_INJ。**立即可开，不等 BG。**
  唯一政策动作 = 首建 `#print axioms AJRIPQN`。
- **W2**（MXI kit 三件，100–250 行）：MXI_IN_VORONOI_LIST + packing 球分离 + sqrt2
  算术。无前置，与 W1 并行可开。
- **W3**（FUEIMOV_4，90–200 行）：前置 W1。双支 chi_msb 记账。
- **W4**（FUEIMOV_3，110–260 行）：前置 W1+W2。集合-列表记账链。
- **W5**（FCHKUGT 本体 + 3 微件，100–230 行）：前置 W3+W4。骨架已完全解码（§1.3）。
- **合计 2.5–4 个施工日（单工人），全链成功率 ~80–85%**（最大不确定 = AJRIPQN 的
  axiom 实测结果，只影响落库口径不影响工作量）。

## 5. 给编排者的上下文笔记

1. **行号漂移警报（第三轮）**：PA25:1968 NEEDS 注记 "FCHKUGT（PA18 :2159 ⬜）" → 实际
   **:6685**；PA25:4377 注记 "FUEIMOV_4(PA18:5213)" → 实际 **:5364**；PA17 docstring
   "TIWWFYQ (PackingAuto5:581, sorry)" → 已真证 **PA5:847**；AR DELIVERY "map:92" →
   e2e tsv **行 102**。Lean docstring 内部矛盾：FUEIMOV_4 写 "leaf_cell.hl:2793-?"、
   FUEIMOV_3 写 ":2977-3337"、MCELL2_EDGE_FIRST 写 ":3338-3374"——**HOL 实测正确划界**：
   FUEIMOV_K :2732-2749、MCELL4_EXTREME_POINT :2779-2810、FUEIMOV_4 :2810-2894、
   MXI_NOT_IN_V :2894-2948、MCELL_V_INTER_EXTREME :2949-2976、MCELL_EXTREME_DIFF_V
   :2977-3000、FUEIMOV_3 :3000-3103、TWO_REARRANGEMENT_LEMMA_ALT :3104-3111、
   MCELL2_EDGE_FIRST :3114-3196、MCELL3_EDGE_FIRST :3197-3337、FINITE_CARD1_IMP_SINGLETON
   :3338-3374、STEM_EDGEX :3375-3431、FCHKUGT :3432-3528。编排者统一更新 NEEDS 注记时
   以本报告为准。
2. **共用文件并行纪律**：本 lane 施工区（PA18 :5334-5396 + :6685）与 BG 施工区
   （PA18 :5405-5480）同文件不同段，闸门 = per-file `lake build`——**两 lane 在 PA18 上
   串行集成**；W1–W4 可在独立分支先行（段落不重叠，rebase 成本低），落库顺序由编排者排。
   PA25 侧本 lane **零施工**（p25_leaf_azim_inj/LEAF_RANKING_LEMMA 零编辑自动转净），
   与 PA25 上其他 lane 无排队冲突。
3. **不要引的四个名字**：`CARD4_IMP_DISTINCT`（树内无此名定理——PA12:36 docstring 是
   计划清单、PA25:4228 注"已证"失真；用 GBEWYFX:2053 + Nat.card 记账替代）；
   `BARV_SUBSET`/`BARV_IMP_HD_IN_SET_OF_LIST`（HOL 名；Lean 只有 PA2 私有孪生
   p2g_BARV_SUBSET:716 / p3a_BARV_SUBSET:4982，或 def 级 3-5 行自写）；
   `X_IN_AFF_GT_X` 公版（LocalAuto5:7702，LocalAuto5 无人 import——本地复制）；
   `AFF_GT_SUBSET_AFFINE_HULL` 公版（PA18:9812，在本体 :6685 之后——本地复制，
   连 pa18_affsign_mem_affSpan 体一起 ~10-25 行）。
4. **标准-三闸的裁决预案**：W1 首建若 `#print axioms AJRIPQN` 出 sorryAx（PA2
   XNHPWAB1_concl:5405 / MXI_EXISTS_concl:5484 在册债经 PA12 的可能流入），两个选项：
   (a) 编排者按"消费在册 sorry"口径放行本 lane（AR 车道 DELIVERY 已给先例表述）；
   (b) 把 PA2 两件清偿插队为本 lane 前置。工作量估计两种口径相同。
5. **价值排序**：本 lane 单独清偿的即时增益 = PA25 两件零编辑转净 + LEAF_RANK_REUHADY
   债面收窄至 REUHADY1(PA24)+EWYBJUA 两具名外部锚 + CC_3_AZIM_LT_PI_COPLANAR 可填；
   W3 额外解锁 WEDGE_UNIQUE_CC_CELL 的一重债。与池 B 的 EWYBJUA（W6 可选）、池 A 的
   CFFONNL（已落）、池 D 的 FUEIMOV——**注意：池 B 测绘曾把 FUEIMOV_4 记为"池 D 只进
   WEDGE_UNIQUE/K3 臂"，实测 FUEIMOV_4/3 同在 FCHKUGT 的硬前置上，本报告已把它收编进
   本 lane 的 W3/W4**；编排者若另有池 D 立项，须与本 lane 合并或串行，避免双开工。
6. **任务书口径更正**：本池不是"FCHKUGT 一件"，是 **FCHKUGT + FUEIMOV 族 7 件** 的
   leaf-cell 刚性族。wim 口径的"GIANT"标签应整体移到该族头上；分波后每波单件最大
   HOL 104 行（FUEIMOV_3），无单点深水区。

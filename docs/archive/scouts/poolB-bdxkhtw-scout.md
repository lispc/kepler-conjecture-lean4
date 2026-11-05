# 池 B 测绘：BDXKHTW 中 GIANT（2026-10-24，Lane Z 交付）

> 快照：`lane_snapshots/bdxkhtw-scout/`。**关键发现**：池 B 传递依赖池 A 根因（BDXKHTW 第 7 步
> 消费 CFFONNL 二择推论）但只闸 W4；W1–W3 立即可开。本池五件陈述零误植。真实工作量 505–955 行
> （中位 ~730），4+1 波，成功率 ~85–90%，真数学缺口 0。警报：wim 旧行号已漂（:7002/:7031）；
> PA18/PA25 两池共用文件必须串行集成（SF-50 先行，池 B 交付由编排者排序落地）。

---

# PA25 池 B `BDXKHTW` + `WEDGE_COMPLEMENT` 侦察报告（SCOUT）

> 车道：PA25 WIM 复评线四池之**池 B** 只读侦察（完全只读，零构建、零 tracked 写）。
> 基线：main @ `bd2b5876`（A7 裁决 312f08c8 之后）。交付：本文件、`DEP_MAP.tsv`、
> `WAVES.md`、`MD5SUMS`。
> 方法：leaf_cell.hl:3767-4306 + OXLZLEZ3.hl:1231-1408/:2998-3101 证明体逐段读；
> PA18 全部相关件 awk sorry 状态普查；PA18 import 闭包（43 模块）python 实测；
> PA25 消费区 NEEDS 注记逐条对账。

## 0. 结论速览

1. **GIANT 实测：名不副实，是"中 GIANT"。** BDXKHTW 本体 HOL = 183 行
   （leaf_cell.hl:3984-4166）；池 B 全族（:3767-4306）名义 540 行，其中 **3 小件
   已入仓**（WEDGE_SUBSET_WEDGE_GE / ADD_NN_ZERO / AZIM_POS_IMP_SUM_2PI_ALT），
   剩余 HOL 核心 **408 行**（PREP 137 + AFF_INTER_IMP_COPLANAR 51 + BDXKHTW 183 +
   WEDGE_GE_COMPLEMENT 23 + WEDGE_COMPLEMENT 14）+ EWYBJUA 91（可选赠品）。
   但 BDXKHTW 的 183 行约六成是已证 kit 上的 refinement 战术噪声——真正 Lean 工作量
   **核心 505–955 行（中位 ~730），4 波 + 1 可选波**。对照 ContraFan GIANT
   （HOL 剩余 1,390 → Lean 1,100–1,700），池 B 约为其一半。
2. **最大事实修正：池 B 不是独立池——BDXKHTW 传递依赖池 A 根因。** HOL BDXKHTW
   的证明第 7 步（leaf_cell.hl:4048-4095）消费 **CFFONNL 的"二择"推论**
   （X = cc_cell ul ∨ X = cc_cell 交换序）。而 Lean CFFONNL（PA18:4623）的前提
   误植为交换序 `X ≠ ccCell V [swapped]`——正是 A7 裁决（312f08c8）判定的假陈述，
   修复走 **STATEMENT-FIX（编排者所有，补丁草案在飞）**。BDXKHTW 开工顺序因此
   被 CFFONNL 修复闸住，但只闸 W4 一波；**W1–W3 与 CFFONNL 无关，立即可开工**。
3. **误植检查（池 A 教训逐条对照）：本池五件陈述全部与 HOL 逐前提一致，零误植。**
   BDXKHTW（8 前提 + 结论⊆wedgeGe）、BDXKHTW_PREP_LEMMA（10 前提 + 6 段结论）、
   WEDGE_GE_COMPLEMENT、WEDGE_COMPLEMENT、EWYBJUA 均逐字对齐（含前提顺序）。
   唯一的 CFFONNL 型误植在**上游 CFFONNL 本身**（已立项修复，见第 2 条）。
4. **上游已入仓清单（本会话核实 PROVEN）**：PA18 侧 GBEWYFX:2053、ZASUVOR:2295、
   CELL_NN:3444、CHI_MSB_ADDITIVE:2718、AFFINE_IMP_CHI_MSB_0:2745、
   CHI_MSB_COPLANAR:2876、COPLANAR_INSERT:1968、NOT_COLLINEAR_AFF_DIM2:1843、
   STEM_OF_LEAF:5330、MCELL_CONVEX:4217、CONNECTED_SEGMENT_NOT_COVERED:1991、
   WEDGE_WEDGE_GE:2024、WEDGE_INTER_AFF_GE:6900、AFF_GE_SUBSET_WEDGE_GE:6936、
   AZIM_BASE_SHIFT_LE:6672；PA4 侧 RIJRIED:1224、EDGE_IMP_K2:1277（PA18 闭包内）；
   PA25 侧 MCELL_AVOID_LEAVES:2323、LEAF_RANK_AZIM_NZ:2391、LEAF_RANK_AZIM_INJ:2359、
   s_leaf_leaf、S_LEAF_IN_WEDGE_GE:3089、LEAF_RANK_HAS_SIZE:3454、AZIM_ZERO_SHIFT:9087；
   PA18 侧 CC_CELL_IN_MCELL_SET:5015、CC_CELL_NOT_NULLSET:5185、STEM_EDGEX:6619、
   U2_IN_CC_CELL:3093。**BDXKHTW 的全部数学件一个不缺，只剩装配。**
5. **分类：(a) 已证 28 件；(b) 机械移植 9 件；(c) 桥 3 件（CFFONNL 陈述修复 +
   ConformingAuto2/LocalAuto5 闭包外件本地复制）；(d) 真数学缺口 0 件。**
6. **消费面**：池 B 清 → `MCELL_IN_WEDGE`（PA25:2399）→ `CC_CELL_SUBSET_WEDGE`
   （PA25:3758）机械可填（其余 kit 全就绪）；K3/K4 六枚是"池 B ∧ 池 A(∧C∧D)"
   的合取——池 B 单独清不解锁任何 e2e 直源，但它是 K4 两枚（e2e map:90/:91 的
   K3_CC_WI_ALT/K4_CC_WI_ALT）的**必要合取支**，并经 11 目标是 real_model 28 枚
   直源（map:107-134）下游的前置。可选项 EWYBJUA 顺手馈赠 REUHADY lane
   （HOL 消费者 = REUHADY, OXLZLEZ3:880）。
7. **建议立项时机**：W1–W3 现在立项（不等池 A）；W4 排在 STATEMENT-FIX 落地后的
   下一波；W5 与 W4 同波或紧随。**PA18/PA25 是池 A 与池 B 的共用文件**，编排者应把
   PA18 上两池的波次串行化（或同 lane 两段施工），避免 per-file 闸门冲突。

## 1. 陈述精确化

### 1.1 BDXKHTW（PA18:7002 sorry ↔ leaf_cell.hl:3984-3991）

Lean（现行，前提顺序与 HOL 完全一致）：

```
{V X : Set V3} {u0 u1 v1 v2 : V3}
  (hs : saturated V) (hp : Packing V)
  (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
  (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
  (haz : azim u0 u1 v1 v2 ≠ 0)
  (hy : ∃ y, y ∈ X ∩ wedge u0 u1 v1 v2)
⊢ X ⊆ wedgeGe u0 u1 v1 v2
```

数学内容：饱和 packing 里，茎 {u0,u1} 上挂两片叶 v1、v2（azim ≠ 0，即两叶分居
轴两侧），X 是带这条茎边的 mcell 且碰到 v1 侧的开楔——则整块 X 落在 v1 侧的
**闭**楔 wedgeGe 内。即"mcell 相对叶楔无处逃逸"。这是 leaf/cell 相容性核心，
向上经 MCELL_IN_WEDGE → CC_CELL_SUBSET_WEDGE 进 K3/K4。

### 1.2 WEDGE_COMPLEMENT（PA18:7031 sorry ↔ leaf_cell.hl:4202-4215）

`(u0 u1 v1 v2 : V3) (h : azim u0 u1 v1 v2 ≠ 0) ⊢ (univ \ wedge u0 u1 v1 v2) = wedgeGe u0 u1 v2 v1`——
开楔的非 = 对侧闭楔。MCELL_IN_WEDGE 的"顶片"（f (PRE n) → f 0）分支用它。
伴生件 WEDGE_GE_COMPLEMENT（PA18:7026 sorry ↔ :4179-4201）是其对偶
（univ \ wedgeGe = wedge 对侧开），HOL 用 sum4_azim_fan + AZIM_RANGE 纯实数算术。

### 1.3 误植检查明细（对照池 A 教训）

| 件 | Lean 前提序 vs HOL | 结论 | 判定 |
|---|---|---|---|
| BDXKHTW | 8/8 一致（sat/pack/leaf×2/mcellSet/edgeX/azim≠0/∃y） | ⊆wedgeGe 一致 | **无误植** |
| BDXKHTW_PREP_LEMMA | 10/10 一致（多 hx 分离前提 = HOL 第 9 行） | 6 段结论逐段一致 | **无误植** |
| WEDGE_GE_COMPLEMENT / WEDGE_COMPLEMENT | 1/1 | 集合等式一致 | **无误植** |
| EWYBJUA | 7/7 | 二择一致 | **无误植** |
| MCELL_IN_WEDGE（PA25:2399） | HasSizeP25/leaf_rank/elV 记法与邻件一致 | ∃i<n ∧ ⊆ 一致 | **无误植** |
| CC_CELL_SUBSET_WEDGE（PA25:3758） | 6/6（leaf_rank 在 2-表 [elV 0; elV 1] 上，与 HOL 同） | 二择一致 | **无误植** |
| **CFFONNL（上游，PA18:4623）** | **hne 误植为交换序**（HOL :2182 为 `¬(X = cc_cell V ul)` 原序） | — | **误植=池 A 根因，A7 判假，STATEMENT-FIX 在飞** |

A7 裁决注记（PA18:4596-4616）已给出修复处方：CFFONNL 前提还原为原序
`X ≠ ccCell V ul`（其证明反而变短：`rw [e1,e0,e2] at hne` 删除，wl=ul 分支变
`exact absurd hXYc hne`），删除 pa18_ccCell_swap:4617，PA25 `MCELL4_LEAF_S_LEAF`
的 by_cases 改原序等式（AJRIPQN dispatch 对称，涟漪机械）。**修复后的 CFFONNL
恰好给出 BDXKHTW 需要的二择形式**（by_cases X = ccCell V [u0,u1,v] 即可），
W4 的接线因此是纯机械。

### 1.4 BDXKHTW HOL 证明骨架（:3992-4165，12 步）

反证 x ∈ X 落在 wedgeGe 外 → PREP_LEMMA 给 {p∈X∩wedge, q∈X\wedgeGe, ¬coplanar{p,q,u0,u1},
p,q ∉ 两闭锥之并} → **CONNECTED_SEGMENT_NOT_COVERED**（段 [p,q] 穿楔必有内点，
已证 PA18:1991）+ 凸性 → ∃x 在段上、x∈X、x∉{p,q}、0<u<1 → x∉affine{u0,u1}
（否则 AFF_INTER_IMP_COPLANAR 与 ¬coplanar 矛盾）→ x ∈ affGt {u0,u1}{v}
（affGe 分解 + th3a 平凡件）→ **CFFONNL 二择**：X = cc_cell[u0,u1,v] ∨ X = cc_cell[u1,u0,v]
（第二支 ZASUVOR 归一，两支同构）→ CELL_NN×2（p、q 的 chiMsb > 0，已证）→
AFFINE_IMP_CHI_MSB_0（x 在 affine hull 内 ⇒ chi x = 0）+ CHI_MSB_ADDITIVE →
CHI_MSB_COPLANAR/COPLANAR_INSERT/NOT_COLLINEAR_AFF_DIM2/GBEWYFX 排除共面退化 →
**ADD_NN_ZERO 收口**：(1−u)·chi p + u·chi q = chi x = 0 与 chi p, chi q > 0、
0<u<1 矛盾。**全部引理已证，纯装配，无一步新数学。**

### 1.5 BDXKHTW_PREP_LEMMA HOL 证明骨架（:3774-3902，10 步）

mcell_set 展开 + GBEWYFX×2 + RIJRIED 灭 NULLSET 支 + EDGE_IMP_K2（i≥2）→
MCELL_CONVEX → 令 s = 两闭锥之并，NEGLIGIBLE_AFF_GE_2_1 ⇒ s 测零 →
X' = X∖s 非共面（COPLANAR_IMP_NEGLIGIBLE + 零集并封闭 + NEGLIGIBLE_SUBSET）→
X'' = (X'∩wedge ∪ X'∩补 ∪ {u0,u1}) 非共面（**COPLANAR_UNION**，PA18:1983 sorry）
→ p、q 存在性（WEDGE_INTER_AFF_GE / AFF_GE_SUBSET_WEDGE_GE 集合论，均已证）→
u0≠u1（平凡）→ collinear{p,u0,u1} ⇒ p∈aff_ge（COLLINEAR_3_IN_AFFINE_HULL +
AFFINE_HULL_SUBSET_AFF_GE，两枚微件缺失需新写）→ mcell i V ul ⊆ s 与零集矛盾。
**依赖的 COPLANAR_UNION（PA18:1983）本身是 sorry——W1 必须先补它**
（HOL :241-300，60 行仿射维数论证，用已证 COPLANAR_INSERT + MHFTTZN1（CFFONNL
证明内已有消费先例））。

## 2. 依赖链全图与行数对账

### 2.1 池 B 家族（leaf_cell.hl:3767-4306）行数实测

| 口径 | 行数 | 说明 |
|---|---|---|
| 全族名义 | 540 | :3767-4306（PREP 137 + WEDGE_SUBSET 9 + AFF_INTER 51 + ADD_NN 18 + BDXKHTW 183 + AZIM_POS 10 + WEDGE_GE_COMPL 23 + WEDGE_COMPL 14 + EWYBJUA 91，含空行注释） |
| 已入仓 | 37 | WEDGE_SUBSET_WEDGE_GE:6974 / ADD_NN_ZERO:6986 / AZIM_POS_IMP_SUM_2PI_ALT:7014 全 PROVEN |
| 剩余 HOL 核心 | **408** | PREP 137 + AFF_INTER 51 + BDXKHTW 183 + WEDGE 系 37 |
| （可选）EWYBJUA | 91 | 非 BDXKHTW 链必需；HOL 消费者 = REUHADY |
| wim 报告口径 "~180 GIANT" | 183 | 指 BDXKHTW 本体，实测吻合；但其中 ~60% 是已证 kit 装配噪声 |
| 上游 kit（非本池行数） | — | 28 件已证见 §0.4；缺失微件 6 枚合计 ~30-60 Lean 行 |

### 2.2 BDXKHTW 消费的全部具名件（HOL → Lean 状态）

见 `DEP_MAP.tsv`（45 行）。要点：28 件 (a) 已证、9 件 (b) 机械、3 件 (c) 桥、
0 件 (d) 缺口。三件桥：
- **CFFONNL**：陈述修复（编排者所有）；修复后 BDXKHTW 接线 0-20 行。
- **ConformingAuto2.NEGLIGIBLE_AFF_GE_2_1**：PA18 闭包（43 模块实测）**不含**
  ConformingAuto2——新增 import 或走 PA18:4534 现成私有件（coplanar→null kit，
  affGe ⊆ affineSpan 三点平面）本地推 ~10-20 行。
- **LocalAuto5 三件**（AZIM_RANGE:1549 / AZIM_EQ_0_GE_ALT2:1951 /
  WEDGE_GE_AZIM_LE:3075）：LocalAuto5 **无人 import、不在任何闭包**——本地复制/
  重推合计 ~15-30 行（AZIM_RANGE 两行、WEDGE_GE_AZIM_LE 对主 def 是 3 行
  Iff.rfl 型、ALT2 用 Geom/AzimLemmas.azim_eq_zero_iff_alt 重推 10-20 行）。

### 2.3 PA25 侧两件的依赖状态（全部核实）

- MCELL_IN_WEDGE（PA25:2399）：MCELL_AVOID_LEAVES/LEAF_RANK_AZIM_NZ/INJ/
  S_LEAF_IN_WEDGE_GE/LEAF_RANK_HAS_SIZE/s_leaf_leaf 全 PROVEN；AZIM_ZERO_SHIFT
  在本文件 :9087（PROVEN，但**前向引用**——按 p25_dihV_ne_zero:2456 先例内联 2 行）；
  WEDGE_SIMPLE 缺失但内容 = wedge def 展开 3 行（Geom/Azim.lean:63 的 def 自带
  ¬Collinear 支，AZIM_DEGENERATE 平凡）；num_MAX → 有限集取最大角（Mathlib
  Finset/Nat.find，10-20 行）。
- CC_CELL_SUBSET_WEDGE（PA25:3758）：NEEDS 注记所列 kit（ZASUVOR/
  CC_CELL_IN_MCELL_SET/CC_CELL_NOT_NULLSET/STEM_EDGEX/U2_IN_CC_CELL/
  S_LEAF_IN_WEDGE_GE/LEAF_RANK_AZIM_INJ/LEAF_RANK_HAS_SIZE/MOD_INJ1_ALT_p25/
  periodic_mod）逐一 grep 核实全部在树且 PROVEN。纯 periodic/MOD 记账装配。

## 3. 消费面（池 B 清偿的下游）

值级路径（行号为现 HEAD 实测；wim 报告的 PA18:6873/6902 是旧基线 28752d1a，
A7 提交 +129 行漂移到 :7002/:7031——**PA25 各 NEEDS 注记里的旧行号建议由
编排者统一更新**）：

```
W1-W3 (PA18 装配) ──► BDXKHTW(PA18:7002) ─┐
W2     (WEDGE 系)  ──► WEDGE_COMPLEMENT ────┤
                                          ▼
                            MCELL_IN_WEDGE(PA25:2399)      [池B 清]
                                          ▼
                            CC_CELL_SUBSET_WEDGE(PA25:3758)[池B 清]
                                          ▼
      K4_CC_WI_ALT(PA25:3837) ◄── 还需池A (CFFONNL修复→MCELL4_LEAF_S_LEAF→…)
      K4_CC_WIM   (PA25:3852) ◄── 同上
      K3_CC_WI_ALT(PA25:3866) ◄── 还需池A+池C+池D
      K3_CC_WIM_ALT(PA25:3879)◄── 同上
```

- 池 B 单独清：+2 枚可填（MCELL_IN_WEDGE、CC_CELL_SUBSET_WEDGE），均非 e2e 直源
  （e2e-reachability-map.tsv 无行）。
- 池 B + 池 A：K4_CC_WI_ALT（map:91, parent CC_4_PROPS）、K4_CC_WIM、
  K3_CC_WI_ALT（map:90, parent cc_4_cc_ke4）、K3_CC_WIM_ALT 可填——K3 两枚
  另需池 C（MCELL4_FULL_WEDGE 装配）+ 池 D（FUEIMOV_4），见 wim §5.2 矩阵。
- 11 目标全清后：real_model 28 枚直源（map:107-134，parent pkrm*）的下游链解锁
  （wim §5.1.4 的"本 lane 清偿是 real_model 链的前置"）。
- 可选 EWYBJUA（PA18:7037）：HOL 唯一消费者 = REUHADY（OXLZLEZ3:880）。填了它，
  REUHADY lane（池 C 归属 PA24 lane 协同）白得一枚；Lean 侧 PA24 有自己的
  FCHKUGT/EWYBJUA 孪生注记（PA24:13145），不冲突。

## 4. 波次计划与天花板

见 **`WAVES.md`**。骨架（核心 4 波 505–955 行，中位 ~730；可选 +40–80）：

- **W1**（PA18 前置件，无池 A 依赖，立即可开）：COPLANAR_UNION +
  AFF_INTER_IMP_COPLANAR + 6 微件（interpret/affGt⊆hull/hull⊆affGe/
  collinear∈hull/2-unequal/th3a 内容）+ nullSet 胶水。估 110–230 行。低-中风险。
- **W2**（WEDGE 系）：WEDGE_GE_COMPLEMENT + WEDGE_COMPLEMENT。估 35–65 行。低风险。
- **W3**（PREP_LEMMA）：估 100–180 行。中风险（measure/零集 glue）。无池 A 依赖。
- **W4**（BDXKHTW 本体）：估 80–140 行。低风险装配；**硬前置 = CFFONNL
  STATEMENT-FIX 落地**（池 A 根因修复）。
- **W5**（PA25 两件）：MCELL_IN_WEDGE 120–220 + CC_CELL_SUBSET_WEDGE 60–120。
  前置 = W2+W4；中风险（azim 极径角 + PRE n 算术 + MOD 记账）。
- **W6**（可选）：EWYBJUA 40–80，馈赠 REUHADY lane。

**诚实天花板**：全链无真数学缺口；W1–W3（245–475 行）可立即承诺，成功率 ~85%；
W4–W5 在 STATEMENT-FIX 落地后成功率 ~85–90%（唯一工期风险 = 池 A 修复的落地
时机，不由本池控制）。合计期望 2–4 个工作日（单工人）。

## 5. 给编排者的上下文笔记

1. **行号漂移警报**：pa25wim/DELIVERY.md 与 PA25 各 NEEDS 注记引用的
   `BDXKHTW(PA18:6873)`、`WEDGE_COMPLEMENT(PA18:6902)` 已漂移至
   **:7002/:7031**（A7 提交 312f08c8 在 PA18 前部 +129 行）。CFFONNL 本体
   :4596→:4623、ccCell_swap :4590→:4617。§5 断点地图照抄时以本报告为准。
2. **共用文件并行纪律**：池 A 的 STATEMENT-FIX 施工区（PA18:4596-5330 + PA25
   MCELL4_LEAF_S_LEAF）与池 B W1-W3 施工区（PA18:1983、:6959-7045）同文件不同段。
   闸门是 per-file build——两池在 PA18 上必须串行（先 A 后 B1-3，或同 lane 两段）；
   PA25 侧同理（W5 与池 A 的 PA25 涟漪波串行）。W2/W3 内部互相独立、可同波。
3. **不要引的三个名字**：`wedgeGe_p2/p3/p4`（LocalAuto2/3/4 的孪生 def，主 def 在
   PA2:271 且在两文件闭包内）；`TopologyFan.aff_ge_subset_aff_gt_union_aff:2146`
   是 FAN 特化版（泛化件照它的 mem_affGe 坐标法自写）；PA24 的 FCHKUGT/EWYBJUA
   孪生注记勿与 PA18 本体混淆。
4. **W4 的二择接线**（CFFONNL 修复后）：`by_cases hXYc : X = ccCell V [u0,u1,v]`
   正支取 [u0,u1,v]、负支右推 CFFONNL 得 [u1,u0,v] 再 ZASUVOR 归一——与 HOL
   :4055-4095 逐步同构。修复后的 CFFONNL 用 `(ccUh V ul).getD i 0` 记法，照
   PA18:4623 现行 prove 体头部（EL_CC_UH + list3_eq + getD3 展开）抄即可。
5. **池 C 的免费馈赠**：W6 EWYBJUA 与 W2 同工具集（BDXKHTW+WEDGE_COMPLEMENT+
   AZIM_EQ_0_SYM2），若编排者想给 REUHADY lane 送分，可与 W5 同波捎带。
6. **价值排序**：池 B 的独立 e2e 增益 = 0，但它是 K4 两枚（map:90/:91）的必要
   合取支 + real_model 28 枚的二级前置。若编排者的目标是"最少波次解锁最多直源"，
   池 A（STATEMENT-FIX）仍是第一优先；池 B W1-W3 可在等池 A 的窗口期并行推进。

---

# 池 B 波次计划（WAVES）

> 配套 SCOUT.md §4。行数区间 = 低估–高估（诚实区间，中位加总 ~730）。
> 全程无 (d) 真数学缺口；风险栏只列工期/装配风险。

| 波 | 文件 | 内容 | 估行数 | 前置 | 风险 | 成功率 |
|---|---|---|---|---|---|---|
| W1 | PA18 | COPLANAR_UNION(:1983) + AFF_INTER_IMP_COPLANAR(:6980) + 6 微件（interpret / AFF_GT⊆hull / hull⊆affGe / collinear∈hull / 2-unequal / th3a内容）+ nullSet 并集胶水 | 110–230 | 无（**立即可开**，不等池A） | 低-中（AFF_INTER 的 affineSpan 交非空→Coplanar 是最大单件） | ~85% |
| W2 | PA18 | WEDGE_GE_COMPLEMENT(:7026) + WEDGE_COMPLEMENT(:7031) + AZIM_EQ_0_SYM2 微件 | 35–65 | W1 的 AZIM_RANGE 本地件（2 行，可顺手） | 低（sum4_azim_fan 在闭包内；纯实数算术） | ~90% |
| W3 | PA18 | BDXKHTW_PREP_LEMMA(:6959)：10 步装配 + 零集/测度 glue（PA18:4534 私有 kit 同款）+ NEGLIGIBLE_AFF_GE_2_1 本地化 | 100–180 | W1（COPLANAR_UNION 等） | 中（measure 记账；分块提交防错误级联） | ~80–85% |
| W4 | PA18 | BDXKHTW 本体(:7002)：12 步装配，二择接线（by_cases ccCell 正支/ZASUVOR 负支）+ chiMsb 链（全已证）+ ADD_NN_ZERO 收口 | 80–140 | **CFFONNL STATEMENT-FIX 落地（池A根因，编排者所有）** + W1–W3 | 低（纯装配）；工期风险=池A修复落地时机，非本池可控 | ~85–90% |
| W5 | PA25 | MCELL_IN_WEDGE(:2399) + CC_CELL_SUBSET_WEDGE(:3758)：avoid-leaves 引子 + BDXKHTW/顶片双分支 + num_MAX 极径角 + azim 位移 + MOD 记账 | 180–340 | W2 + W4 | 中（PRE n/SUC 算术、AZIM_ZERO_SHIFT 前向引用内联、getD 记法坑——wim §5.3 已给战术情报） | ~85% |
| W6（可选） | PA18 | EWYBJUA(:7037)：BDXKHTW 两次调用 + 集合论两支 | 40–80 | W4 + W2 | 低 | ~90% |

合计：**核心 W1–W5 = 505–955 Lean 行、4 个施工日量级（单工人）；+W6 = 545–1035。**

## 波次间依赖图

```
W1 ──► W3 ──┐
W1 ──► W2 ──┼──► W5（PA25）
池A STATEMENT-FIX ──► W4 ──┘
W4 ──► W6（可选）
```

## 与池 A / 池 C / 池 D 的并行度

- **同文件约束**：池 A 施工区（PA18:4596-5330 + PA25 MCELL4_LEAF_S_LEAF）与池 B
  施工区（PA18:1983/:6959-7045 + PA25:2399/:3758）在**同一对文件**里。闸门是
  per-file `lake build`——PA18 上两池必须串行（建议：池 A STATEMENT-FIX 波先行，
  W1–W3 在其落地前的窗口期以独立 lane 串行跟进；PA25 同理）。
- **池 C**（MCELL2/3_EDGE_FIRST GIANT、REUHADY、MCELL3_DIHX、MCELL2_DIHX_POS）：
  全部不在池 B 的依赖闭包上（CC_CELL_SUBSET_WEDGE 不经 MCELL4_FULL_WEDGE），
  四池中 B 与 C 无值级耦合，唯一共享是文件排队。
- **池 D**（FUEIMOV_4, PA18:5213）：同样仅文件排队耦合（只进 WEDGE_UNIQUE/K3 臂）。
- **收益叠加**：池 B(W4/W5) ∧ 池 A → K4_CC_WI_ALT/K4_CC_WIM/K3_CC_WI_ALT(map:90)/
  K3_CC_WIM_ALT 四枚可填；再 ∧ 池 C ∧ 池 D → 11 目标清零 → real_model 28 枚
  直源（map:107-134）下游解锁。

## 每波验收处方

- W1：`lake build Kepler.Text.PackingAuto18` 自然退出 0 error；COPLANAR_UNION
  消费者 = W3 的 X'' 非共面步，写完即用 p25 式自查。
- W2：`azim_compl` 路线照 PA18:7014（AZIM_POS_IMP_SUM_2PI_ALT 已证体）同款。
- W3：PREP 六段结论逐段 `have` 落账后再合总；测度段照 :4534-4590 CFFONNL
  证明内的 hnullX/pa18_coplanar_measure_null 先例。
- W4：前置检查 = CFFONNL 陈述已是原序（PA18:4623 的 hne 形状）；接线照
  HOL :4055-4095 逐步；CELL_NN 两次 ANTS 的集合论别恋战（2 次失败即记 NEEDS）。
- W5：先 MCELL_IN_WEDGE 后 CC_CELL_SUBSET_WEDGE；AZIM_ZERO_SHIFT 内联 2 行
  （azim_eq_azim_iff + azim_eq_zero_iff_alt，Geom/AzimLemmas 在闭包）；
  num_MAX 用 Finset 取最大照 PA25 既有算术件风格。

---

```
HOL引理	HOL行号	分类	Lean对应	估Lean行数	备注
COPLANAR_UNION	leaf_cell.hl:241-300 (60)	b机械	PA18:1983 (sorry)	40-80	PREP前置; 仿射维数论证, 用已证COPLANAR_INSERT+MHFTTZN1(CFFONNL证明内有消费先例)
BDXKHTW_PREP_LEMMA	leaf_cell.hl:3767-3903 (137)	b机械	PA18:6959 (sorry)	100-180	陈述与HOL逐前提一致无误植; 零集/测度glue走PA18:4534私有kit同款
WEDGE_SUBSET_WEDGE_GE	leaf_cell.hl:3904-3912 (9)	a已证	PA18:6974 PROVEN	0	-
AFF_INTER_IMP_COPLANAR	leaf_cell.hl:3913-3963 (51)	b机械	PA18:6980 (sorry)	30-60	两条affine line相交非空=>Coplanar; W1最大单件
ADD_NN_ZERO	leaf_cell.hl:3964-3981 (18)	a已证	PA18:6986 PROVEN	0	BDXKHTW终局收口件
CFFONNL	leaf_cell.hl:2178-2514	c桥(陈述修复)	PA18:4623 (证明体完整但hne误植=池A根因, A7判假)	0-20(接线)	STATEMENT-FIX在飞(编排者所有); 修复后给BDXKHTW所需二择; BDXKHTW硬前置
CONNECTED_SEGMENT_NOT_COVERED	leaf_cell.hl:304-327	a已证	PA18:1991 PROVEN	0	-
WEDGE_WEDGE_GE	leaf_cell.hl(已入仓)	a已证	PA18:2024 PROVEN	0	-
GBEWYFX	leaf_cell.hl	a已证	PA18:2053 PROVEN	0	-
ZASUVOR	leaf_cell.hl	a已证	PA18:2295 PROVEN	0	-
CELL_NN	Bump	a已证	PA18:3444 PROVEN	0	chiMsb非零(胞内点)
CHI_MSB_ADDITIVE	Bump	a已证	PA18:2718 PROVEN	0	-
AFFINE_IMP_CHI_MSB_0	Bump	a已证	PA18:2745 PROVEN	0	-
CHI_MSB_COPLANAR	Bump	a已证	PA18:2876 PROVEN	0	-
COPLANAR_INSERT	Bump	a已证	PA18:1968 PROVEN	0	-
NOT_COLLINEAR_AFF_DIM2	leaf_cell.hl	a已证	PA18:1843 PROVEN	0	-
STEM_OF_LEAF	leaf_cell.hl	a已证	PA18:5330 PROVEN	0	-
MCELL_CONVEX	Pack_defs	a已证	PA18:4217 PROVEN	0	-
WEDGE_INTER_AFF_GE	leaf_cell.hl	a已证	PA18:6900 PROVEN	0	PREP第6步用
AFF_GE_SUBSET_WEDGE_GE	leaf_cell.hl	a已证	PA18:6936 PROVEN	0	PREP第7步用
AZIM_BASE_SHIFT_LE	local_lemmas	a已证	PA18:6672 PROVEN	0	MCELL_IN_WEDGE极径角论证用; PA18在PA25闭包内
RIJRIED	Pack_def/Pump	a已证	PA4:1224 (BumpP4.RIJRIED) PROVEN	0	PA18/PA25闭包内
EDGE_IMP_K2	Bump	a已证	PA4:1277 PROVEN	0	PREP第1步(i>=2)
COPLANAR_IMP_NEGLIGIBLE	HOL库	c桥(本地件)	PA18:4534私有kit(内联, CFFONNL证明已用)	10-20	共面=>测零; wim处方同款
NEGLIGIBLE_AFF_GE_2_1	Conforming.NEGLIGIBLE_AFF_GE_2_1	c桥(闭包外)	ConformingAuto2(不在PA18闭包, 实测43模块)	10-20	或加import(无环)或本地推: affGe⊆三点affineSpan+PA18:4534件
NULLSET_RULES(并集封闭)	HOL库	b微件	Mathlib measure glue	5-10	零集并封闭+NEGLIGIBLE_SUBSET
IN_AFF_GE_INTERPRET_TO_AFF_GT_AND_AFF	Collect_geom	b微件	缺; 模板=TopologyFan:2146(FAN特化)	15-30	affGe⊆affGt∪affineSpan; BDXKHTW第7步用
AFF_GT_SUBSET_AFFINE_HULL	leaf_cell.hl系	b微件	缺(LA37有2+1实例, 不在闭包)	5-10	def展开级
AFFINE_HULL_SUBSET_AFF_GE	leaf_cell.hl系	b微件	缺	5-10	PREP第9步+MCELL_IN_WEDGE用
COLLINEAR_3_IN_AFFINE_HULL	Collect_geom	b微件	缺(Mathlib有近型可桥)	3-8	-
NOT_COLLINEAR_IMP_2_UNEQUAL	Collect_geom	b微件	缺	2-3	-
Fan.th3a内容({u0,u1}∪{v}分离)	Fan.th3a	b微件	缺(非共线推v∉{u0,u1})	2	-
BDXKHTW	leaf_cell.hl:3984-4166 (183)	b机械	PA18:7002 (sorry)	80-140	GIANT实测183行但~60%为已证kit装配; 硬前置=CFFONNL修复
AZIM_POS_IMP_SUM_2PI_ALT	leaf_cell.hl:4168-4177 (10)	a已证	PA18:7014 PROVEN (azim_compl)	0	-
WEDGE_GE_COMPLEMENT	leaf_cell.hl:4179-4201 (23)	b机械	PA18:7026 (sorry)	25-45	sum4_azim_fan(TopologyFan,闭包内)+AZIM_RANGE本地2行+实数算术
WEDGE_COMPLEMENT	leaf_cell.hl:4202-4215 (14)	b机械	PA18:7031 (sorry)	10-20	WEDGE_GE_COMPLEMENT+AZIM_EQ_0_SYM2(azim_compl对称,~5行)
AZIM_EQ_0_SYM2	local_lemmas	b微件	缺(azim_compl推)	5	azim≠0在对侧交换下不变
AZIM_RANGE	local_lemmas.hl	c桥(闭包外)	LocalAuto5:1549 (无人import)	2	本地复制; =azim_nonneg+azim_lt_two_pi(Geom在闭包)
AZIM_EQ_0_GE_ALT2	local_lemmas.hl	c桥(闭包外)	LocalAuto5:1951 (无人import)	10-20	本地重推, 用Geom/AzimLemmas.azim_eq_zero_iff_alt
WEDGE_GE_AZIM_LE	local_lemmas.hl	c桥(闭包外)	LocalAuto5:3075是wedgeGe_p2孪生; 主def版缺	3	主def(PA2:271)成员=合取, Iff.rfl型3行
EWYBJUA	leaf_cell.hl:4216-4306 (91)	b机械(可选)	PA18:7037 (sorry)	40-80	非BDXKHTW链必需; HOL消费者=REUHADY(OXLZLEZ3:880); 馈赠REUHADY lane
MCELL_AVOID_LEAVES	OXLZLEZ3	a已证	PA25:2323 PROVEN	0	MCELL_IN_WEDGE第1步
LEAF_RANK_AZIM_NZ	OXLZLEZ3	a已证	PA25:2391 PROVEN	0	-
LEAF_RANK_AZIM_INJ	OXLZLEZ3	a已证	PA25:2359 PROVEN	0	-
S_LEAF_IN_WEDGE_GE	OXLZLEZ3	a已证	PA25:3089 PROVEN	0	-
LEAF_RANK_HAS_SIZE	OXLZLEZ3	a已证	PA25:3454 PROVEN	0	-
s_leaf_leaf	OXLZLEZ3	a已证	PA25 PROVEN	0	-
AZIM_ZERO_SHIFT	OXLZLEZ3	a已证	PA25:9087 PROVEN	2	前向引用: 内联(p25_dihV_ne_zero:2456先例)
WEDGE_SIMPLE	Reuhady.hl:68-75	b微件	缺	3	wedge def(Geom/Azim:63)展开; AZIM_DEGENERATE平凡
num_MAX	HOL库	b微件	Mathlib有限集取最大	10-20	MCELL_IN_WEDGE极径角
MCELL_IN_WEDGE	OXLZLEZ3.hl:1231-1408 (178)	b机械	PA25:2399 (sorry)	120-220	陈述无误植; BDXKHTW分支+WEDGE_COMPLEMENT顶片分支+azim位移算术
CC_CELL_IN_MCELL_SET	leaf_cell.hl	a已证	PA18:5015 PROVEN	0	-
CC_CELL_NOT_NULLSET	leaf_cell.hl	a已证	PA18:5185 PROVEN	0	-
STEM_EDGEX	leaf_cell.hl	a已证	PA18:6619 PROVEN	0	-
U2_IN_CC_CELL	leaf_cell.hl	a已证	PA18:3093 PROVEN	0	-
CC_CELL_SUBSET_WEDGE	OXLZLEZ3.hl:2998-3101 (104)	b机械	PA25:3758 (sorry)	60-120	全部kit已证, 纯periodic/MOD记账; 池B链终点
K4_CC_WI_ALT	OXLZLEZ3.hl:3451	c链	PA25:3837 (sorry)	-	消费CC_CELL_SUBSET_WEDGE+池A; e2e map:91 (parent CC_4_PROPS)
K4_CC_WIM	OXLZLEZ3.hl:3521	c链	PA25:3852 (sorry)	-	同上
K3_CC_WI_ALT	OXLZLEZ3.hl:3620	c链	PA25:3866 (sorry)	-	消费CC_CELL_SUBSET_WEDGE+池A+池C+池D; e2e map:90 (parent cc_4_cc_ke4)
K3_CC_WIM_ALT	OXLZLEZ3.hl:3665	c链	PA25:3879 (sorry)	-	同上
```

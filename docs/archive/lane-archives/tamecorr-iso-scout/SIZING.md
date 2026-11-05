# SIZING — W3 规模测算（D）

## 1. 放大比：本仓实测（不是引裁决）

| 样本 | HOL 行 | Lean 行 | 比 | 来源 |
|---|---:|---:|---:|---|
| `tame_list.hl` → `TameList1..69` | 14,428 | 30,250 | **2.10x** | `wc -l`（`logs/size_ratios.log`） |
| `DANGEYJ.hl` → `TameList70..72` | 949 | 1,610 | **1.70x** | 同上 |
| `RXOKSKC.hl` → `TameList65+66+68+69` | 1,105 | 1,945 | **1.76x** | 同上 + `tamecorr-w1/RECON.md` |
| Conforming 章 | 17,033 | 25,120 | **1.47x** | `docs/archive/projects/tamespine-port-plan.md` §4 |

实测区间 **1.47–2.10x**；本测算逐组取 1.5–2.1。裁决口径的 1.3x 在本章样本中未观测到（1.3 会低估 List/Finset/轨道桥的 Lean 展开）。

## 2. WMLNYMD 本体（1,515 HOL 行）逐组

| 组 | HOL 行 | proves | 采用比 | Lean 估计 | 比的理由 |
|---|---:|---:|---|---:|---|
| G1 tame9a/10 对应 | 97 | 2 | 1.8–2.1 | 175–204 | list 面→Graph/Finset 面，与 tame_list 同型 |
| G2 facesAt/filter/11a-12o | 279 | 15 | 1.9–2.1 | 530–586 | filter/Perm/Face 字段，`List.Perm.filter` 与 `Finset` 反复换装 |
| G3 admissible 权重表 | 176 | 8 | 1.7–2.0 | 299–352 | 表值 + filter/sum，Mathlib 有部分 |
| G4 set_of_n/card/type | 163 | 4 | 1.9–2.1 | 310–342 | `Set.ncard`/BIJ/像集，逐点双射展开最重 |
| G5 11/12o 反向对应 | 87 | 2 | 1.9–2.1 | 165–183 | 依赖 G2+G4 的逐点形态 |
| G6 floor 机制 | 450 | 18 | 1.8–2.1 | 810–945 | 实数→Nat 地板 + 显式表 + 三条 adm_floor |
| G7 sum/BIJ 助手 | 55 | 4 | 1.5–1.8 | 82–99 | Mathlib `Finset.sum` 面可消化 |
| G8 装配/主定理 | 154 | 3 | 1.8–2.1 | 277–323 | 113 行 `tame13a_correspondence` 是总装 |
| **本体合计** | **1,461** | **56** | — | **2,649–3,034** | 另 54 行头/空行 |

本体（只算 `WMLNYMD.hl`）= **2.6–3.0k Lean 行**。这与「1,515 行」的 1.7–2.1x 直觉一致。

## 3. 未移植上游（W3 实际必须吃进来的部分）

| 上游 | HOL 行/件 | Lean 估计 | 说明 |
|---|---:|---:|---|
| `OXAXUCS.hl` iso 不变家族（S4） | 614 行 / 24 活跃 prove（3 件常数换算被 HOL 注释掉） | **1,040–1,290** | 主定理直接消费 6 件 `tame*_iso`；其余 18 件是支撑（BIJ_face_iso/CARD_face_iso/type_of_node_iso/adm_*_iso…）。TameSpine 仅有 `hypIsoCardComponents` 等通用件，无这一族。 |
| `list_hypermap-compiled.hl` 缺口（S1 补片） | 约 250–400 行 / 5–7 件 | **450–800** | WMLNYMD 用到 25 个 `List_hypermap.*`；TameLp/岛已覆盖 card_face_of_list、mem_face_lemma、dart_in_face、findFaceDarts_eq_of_mem、la7_length_listPairs、elementsOfList、listOfFaces 等；仍缺 `face_set_eq_list`、`components_hypermap_of_list`（可四件组装）、`uniq_faces_of_list`、`uniq_list_of_elements`、`card_nodes_of_list`、`good_list_nodes_condition`、`face_of_list`（可复用 cardFaceOfList 内部命题）。 |
| S10 常数换算 | 1 件（`tgt_squanderTarget`） | 10–20 | **勘误**：旧 scout 的“常数换算四件”中 `d_tame_squanderFace`/`b_tame_squanderVertex`/`a_tame_excessTCount` 在 `OXAXUCS.hl:114-158` 被 `(* … *)` 注释掉，活跃的只有 `tgt_squanderTarget`（:105）。原因：实数表与 nat 表不是精确 ×10⁴（差额=floor 损失上限，如 6295=6300−5、6177=6180−3），三条“等号”本身为假。 |
| S11 `GoodGraphV4` 忠实化 | def 层 | **0–100** | **已落库**（SF-57…62）；六 def 与岛 `*Spine` 全部 `rfl`（`probeS11.log`）。W3 上游安全模块若不能 import Assembly，需抄 6 个 def（~60 行）或做一次 HOIST。 |
| Assembly 接线 + `Adm3` DEF-FIX | — | **50–150** | 主定理体替换（~10 行）、`Adm3` 逐字改真（~10 行）、公开/复用 b3 桥（~20 行）、证明项 import 与实例搬运。 |
| **上游合计** | — | **1,550–2,360** | 不含本体 |

## 4. W3 端到端

```
本体          2,649–3,034
未移植上游    1,550–2,360
-------------------------
合计          4,199–5,394  Lean 行（约 4.2–5.4k）
```

若 `island-deassembly` GO 且缺口 list 件可复用，上游 List_hypermap 一栏降到 ~0–200，合计约 **3.8–4.8k**。
若 S11 HOIST 也完成，再省 ~50–100；量级不变。

## 5. 与三波程序裁决的「WMLNYMD 1,515 行 / 40+ 引理」对照

- **行数**：1,515 是**实测准确**的文件行数（`wc -l`），但它是 **HOL 文件口径**，不是 W3 工作量口径。裁决若拿它 ×1.3–2.1 估 Lean，会得到 2.0–3.2k——只覆盖“本体”，**漏掉上游 1.55–2.36k**。
- **引理数**：实测 **56 个 prove 块 + 17 个 def = 73 个 let 绑定**。裁决的“40+”**偏保守**（比实际少 16 个 prove / 33 个声明），不是夸大。
- **结论**：作为“WMLNYMD 文件描述”，裁决准确且引理数偏保守；作为“W3 端到端工作量”，裁决**偏乐观约 2–2.5 倍**（4.2–5.4k vs 直觉 2.0–3.2k）。
- **本体 vs 上游的界线**：本体 = `WMLNYMD.hl` 1,461 行 prove 区；上游 = Oxaxucs（iso 不变 + 常数）+ List_hypermap 缺口 + S11/接线。**上游不是可选项**：没有 Oxaxucs 六件，`tame_planar_hypermap` 传不到 `hypermap_of_list`；没有 List_hypermap 缺口件，`tame9a/10/11/12o/13a_correspondence` 的列表计数无从落地。

## 6. 口径备注

- `WMLNYMD.hl` 的 3 个证明块是 `new_definition`/`new_specification` 之外的 17 个 def，不产生证明行；但它们决定了陈述词汇，属“本体”成本。
- G1 的 1.8–2.1 比 G2 低，是因为 `tame9a/10` 主要走 `card_face_of_list` 与 `components`，已有 TameLp/岛半成品；若自证 `components_hypermap_of_list`，按 2.1 取上沿。
- 所有区间是“诚实移植”估计，不含为绕开 `Adm3`/弱定义而做的重写；若裁决不改 `Adm3` 而另辟证明路线，另计（见 PLAN §G 风险 1）。

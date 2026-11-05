# SCOPE — tameCorrespondenceIso（W3）只读侦察

- 车道：`tamecorr-iso-scout`；主仓 `/Users/zhangzhuo/repos/kepler-conjecture-lean4`；读取时 HEAD `ec57d345`；交卷时 HEAD `0abccb51`（他道对表提交，未触 Assembly/TameLp 锚点；本波零改动）（侦察期间从他道前进，Assembly 相关最近落库 `b8085328` SF-62 / `1036c7c5` SF-61 / `ee88477d` SF-60）。
- 边界：主仓零改动、零 commit；全部探针在 `/tmp/tciso/`；交付在 `~/c17_backup/lane_snapshots/tamecorr-iso-scout/`。
- 验收语言：`#print axioms`；编译探针一律 `nice -n 19 lake env lean <单文件>`（AGENTS §3/§4）。

## 0. 一句话结论

W3 **可以独立开工**（不依赖 `Reduction5` / `jcajydu`），WMLNYMD 与 Oxaxucs/List_hypermap 的上游都可在 `TameLp` + `Graphs` + `TameCorrBase`（三者均不 import `Kepler.Assembly` 本体；`GoodList` 取自 Assembly-free 的 `Kepler.Assembly.GoodListDefs`）上重建；但**不能按现陈述收口**——`Assembly.TamePlanarHypermap` 的 `Tame13a`/`Adm3` 仍是 `True` 占位（唯一不等项），必须先走 DEF-FIX；若要复用 TameSpine 岛件（74/75 文件传递 import Assembly），必须先等岛去 Assembly 化或自证缺口件。

## A. HOL 端结构清单（`WMLNYMD.hl`，1,515 行）

实测：`prove_by_refinement` **56** 个、`new_definition` **16** 个、`new_specification` **1** 个 = **73 个 let 绑定**。逐条机器表见 `ASSETS.tsv`（73 行）与 `logs/hol_items.tsv`（含 internal/external 引用）。

### A.1 主定理 `tame_correspondence_iso`（:1498-1512）

HOL 陈述逐字（`WMLNYMD.hl:1499-1501`）：

```
!g H:(A)hypermap. good_graph_v4 g /\ tame_planar_hypermap H /\ 
  iso H (hypermap_of_list (fgraph g)) ==>
  tame g
```

证明体按顺序消费（:1503-1510）：

1. `REWRITE_TAC[tame_planar_hypermap]` —— 拆 12 合取；
2. `MATCH_MP_TAC tame_correspondence1`（:1473，直接前置 #1）；
3. `Hypermap_iso.iso_imp_hyp_iso` —— 把 `iso` 降为 `hyp_iso`；
4. `ASM_MESON_TAC[Oxaxucs.tame9a_iso; tame10_iso; tame11a_iso; tame11b_iso; tame12o_iso; tame13a_iso]` —— 外部 oxaxucs 六件（:1509，直接前置 #2-#7）。

注意：HOL 主定理**不引用** `JCAJYDU`/`Reduction5`（`grep` 零命中，见 `logs/hol_counts.log`）。

### A.2 直接前置链

```
tame_correspondence_iso (:1498)
├─ tame_correspondence1 (:1473)                       [D1]
│  ├─ tame9a_correspondence (:42)                      [D2]
│  ├─ tame10_correspondence (:107)                     [D2]
│  ├─ tame11a_good_graph (:212)                        [D2]
│  ├─ tame11b_list_tame11b (:308)                      [D2]
│  ├─ tame12o_list_tame12o (:397)                      [D2]
│  ├─ tame13a_list_tame13a (:574)                      [D2]
│  ├─ tame11_correspondence (:757)                     [D2]
│  ├─ tame12o_correspondence (:813)                    [D2]
│  └─ tame13a_correspondence (:1360)                   [D2]
└─ Oxaxucs.tame{9a,10,11a,11b,12o,13a}_iso + Hypermap_iso.iso_imp_hyp_iso  [外部]
```

其余 45 个 prove 块全部是上述 9 件的传递支撑（`T`）；17 个 def 是陈述词汇（`DEF`）。逐条角色/一句话/近载体见 `ASSETS.tsv`。

### A.3 分组规模（HOL 行 / prove 块）

| 组 | 行范围 | HOL 行 | proves | 内容 |
|---|---|---|---|---|
| G1 | :42-138 | 97 | 2 | tame9a/10 对应 |
| G2 | :139-417 | 279 | 15 | facesAt/facesAt_v2 桥、filter、tame11a/11b/12o |
| G3 | :418-593 | 176 | 8 | admissible1/2/3_list、sumn_rot/perm_eq/facesAt、tame13a_list |
| G4 | :594-756 | 163 | 4 | set_of_n_meeting_node / card / type_of_node_vertextype |
| G5 | :757-843 | 87 | 2 | tame11/tame12o 反向对应 |
| G6 | :844-1293 | 450 | 18 | floor 权重机制（nfloor/wt_floor/adm_*_floor） |
| G7 | :1305-1359 | 55 | 4 | sumn_cons/sumn_nsum/uniq_facesAt_list/BIJ_NSUM |
| G8 | :1360-1513 | 154 | 3 | tame13a_correspondence、correspondence1、主定理 |

合计 1,461 行 prove 区 + 54 行头/空行 = 1,515。G6+G7 是自足块（只依赖 `Hypermap`/`tame_defs` 词汇），G1/G2/G5/G8 是 list↔graph 对应块，G4 是计数桥。

## B. 两份 `TamePlanarHypermap` 的关系（必查）

### B.1 逐字定义

`Assembly.lean:2137-2140`（namespace `Kepler.Assembly`）：

```lean
def TamePlanarHypermap (H : Hypermap α) : Prop :=
  Tame1 H ∧ Tame2 H ∧ Tame3 H ∧ Tame4 H ∧ Tame5a H ∧ Tame8 H ∧ Tame9a H ∧
    Tame10 H ∧ Tame11a H ∧ Tame11b H ∧ Tame12o H ∧ Tame13a H
```

`TameLp.lean:488-491`（namespace `Kepler.Text.TameLp`）：

```lean
def TamePlanarHypermap {α : Type*} [DecidableEq α] (H : Hypermap α) : Prop :=
  Tame1 H ∧ Tame2 H ∧ Tame3 H ∧ Tame4 H ∧ Tame5a H ∧ Tame8 H ∧ Tame9a H ∧
    Tame10 H ∧ Tame11a H ∧ Tame11b H ∧ Tame12o H ∧ Tame13a H
```

### B.2 定义级相等？——**否，差恰好一项 `Adm3`**

机器证据（`logs/probes.log`，探针 `probeB.lean`/`probeAdm.lean`）：

- `Tame1`…`Tame12o` **11 件全部 `rfl` 通过**（逐槽 defeq）；
- `Adm1`、`Adm2`、`totalWeight`、`Tame9a` 也 `rfl` 通过；
- **`Adm3` `rfl` 失败**；因此 `AdmissibleWeight`、`Tame13a`、`TamePlanarHypermap` 的 `rfl` 全部失败。

两份 `Adm3` 逐字：

```lean
-- Assembly.lean:2101
def Adm3 (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) → True

-- TameLp.lean:443
def Adm3 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) →
    aTame ≤ setSum (setOfTrianglesMeetingNode H x) w
```

结论：

0. Assembly 版不是转发别名，而是 §2b 自己的一整套 12 个 `Tame*` def；TameLp 版是 §1 的另一套。两者 namespace 不同（`Kepler.Assembly` vs `Kepler.Text.TameLp`），无 Lean 名字碰撞；两套并行维护，只有 `Adm3` 一项分叉。
1. **不是定义级相等**（full def 的 `rfl` 失败）；
2. Assembly 版**严格弱**（`True` 尾丢弃 `a_tame` 下界），TameLp 版才是 `tame_defs.hl:124-127` 的忠实原形；
3. 存在**单向桥** `b3_tamePlanarHypermap`（`Assembly.lean:2367`，private）：`TameLp.TamePlanarHypermap H → TamePlanarHypermap H`；**反向不存在**（`True` 推不出 `aTame` 下界）；
4. 这是**必须先裁的陈述保真度问题**：`tameCorrespondenceIso` 的假设侧用了弱版；HOL 证明的 floor 机制显式消费 `adm_3`（`tame_13_a_floor_tame_13_a`←`adm_3_floor_adm_3`），弱版下该路断。裁决动作 = DEF-FIX：把 `Adm3` 尾逐字抄成 TameLp 体（其余 11 槽已 defeq，改后整个 `TamePlanarHypermap` 退化为 `rfl`）。

### B.3 附带勘误（旧文档 stale）

`GoodGraphV4` 的五个 `True` 占位**已在 HEAD 前落库真化**（SF-57…SF-62：`GoodListNodes`/`FinalGraph`/`AllUniq`/`GoodFacesV3`/`VerticesSet2Eq`/`GoodGraphV4` 全真形，`Assembly.lean:2168-2241`；与 island `*Spine` 六 def 全部 `rfl`——HOL 逐字保真属 SF 批准范围，本波未重审 HOL）。机器证据：六个 def 与 `TameSpine` 的 `*Spine` 版 **全部 `rfl` 通过**（`probeS11.lean`）。旧 scout（`tame-chapter-scout.md` §6-R1）的“A8 按现编码不可证”只对 `Adm3` 仍成立，对 `GoodGraphV4` 已过时。

## 交付物

- `SCOPE.md`（本文）：A 结构 + B 裁决。
- `ASSETS.tsv`：73 行（56 prove + 17 def）四分类。
- `SIZING.md`：D 规模测算 + 裁决对照。
- `PLAN.md`：E 前置判定 + F 首波工单 + G 风险。
- `EVIDENCE.md`：命令 + 原始输出。
- `logs/`：hol_items.tsv、各探针、导入 BFS、比例实测。

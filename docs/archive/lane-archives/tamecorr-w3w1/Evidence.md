# Evidence — tamecorr-w3w1（W3 第一波：floor 18 + sum/BIJ 4）

车道：`tamecorr-w3w1`。主仓 HEAD `17d1df89`。主仓 tracked 零改动（`git status --porcelain`
仅 `?? lean/Kepler/Text/TameCorrFloor.lean`）。

## 1. 交付物

| 项 | 值 |
|---|---|
| 新文件 | `lean/Kepler/Text/TameCorrFloor.lean`（837 行） |
| import | `Kepler.Text.TameLp`、`Kepler.Graphs.Tame`（**无** `Kepler.Assembly`） |
| namespace | `Kepler.Text.TameCorrFloor` |
| 件数 | **22/22 DONE，0 GAP**（floor 18 + sum/BIJ 4） |
| `sorry`/`axiom`/`admit`/`native_decide` | **0**（源码 token 扫描 `NO_FORBIDDEN_TOKENS`） |
| patch | `patch.diff`（`git apply --check --reverse` = OK，843 行 diff） |
| 文件副本 | `TameCorrFloor.lean`（本目录） |

## 2. standalone 验收（`nice -n 19 lake env lean`）

```
$ cd lean && nice -n 19 lake env lean Kepler/Text/TameCorrFloor.lean
（无输出）
RC=0 ｜ error=0 ｜ sorry=0
```
日志：`logs/standalone_lean.log`（空文件即 0 输出）。

## 3. `#print axioms` 实测（22 件全贴）

命令：`nice -n 19 lake env lean <模块副本 + 探针>`（`logs/axioms_probe.log`，RC=1 仅由末尾
**故意的**环自检 `#check` 造成，见 §4）。

```
'Kepler.Text.TameCorrFloor.floorLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.nfloorExists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.wtFloorNN' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.wtFloorLeWt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.totalWeightFloor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.adm1FloorAdm1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.finiteSetOfFaceMeetingNode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.finiteSetOfNMeetingNode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.setOfNMeetingNodeUnion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.bTameExplicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.squanderVertexExplicit' depends on axioms: [propext]
'Kepler.Text.TameCorrFloor.vertextypesExplicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.noExceptEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.noExceptWfloor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.setOfExceptionalMeetingNodeIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Kepler.Text.TameCorrFloor.adm2FloorAdm2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.adm3FloorAdm3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.tame13aFloorTame13a' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.sumnCons' depends on axioms: [propext]
'Kepler.Text.TameCorrFloor.sumnNsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrFloor.uniqFacesAtList' depends on axioms: [propext, Quot.sound]
'Kepler.Text.TameCorrFloor.BIJNSUM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**汇总：22/22 ⊆ `[propext, Classical.choice, Quot.sound]`，零 `sorryAx`。**
其中 `squanderVertexExplicit`/`sumnCons` = `[propext]`，`uniqFacesAtList` =
`[propext, Quot.sound]`（均为标准三子集）。

## 4. 环自检（Evidence 要求项）

在**本模块闭包内**（同一次编译，`logs/axioms_probe.log` 末行）：

```
#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces
/tmp/.../axioms_probe.lean:863:8: error(lean.unknownIdentifier):
  Unknown identifier `Kepler.Assembly.the_kepler_conjecture_from_interfaces`
```

即：本模块 **不传递 import `Kepler.Assembly` 本体** ⇒ Assembly 反向 import 本模块不成环。
（`Kepler.Assembly.GoodList` 只是 `Kepler.Assembly.GoodListDefs` 的 namespace，
该模块 Assembly-free。）

## 5. 逐件对照表（HOL `WMLNYMD.hl` → Lean）

| # | HOL 行 | HOL 名 | Lean 名 | axioms |
|---:|---:|---|---|---|
| 1 | 844 | `floor_lemma` | `floorLemma` | 标准三 |
| 2 | 857 | `nfloor_exists` | `nfloorExists` | 标准三 |
| 3 | 898 | `wt_floor_nn` | `wtFloorNN` | 标准三 |
| 4 | 910 | `wt_floor_le_wt` | `wtFloorLeWt` | 标准三 |
| 5 | 942 | `total_weight_floor` | `totalWeightFloor` | 标准三 |
| 6 | 971 | `adm_1_floor_adm_1` | `adm1FloorAdm1` | 标准三 |
| 7 | 1005 | `FINITE_set_of_face_meeting_node` | `finiteSetOfFaceMeetingNode` | 标准三 |
| 8 | 1020 | `FINITE_set_of_n_meeting_node` | `finiteSetOfNMeetingNode` | 标准三 |
| 9 | 1031 | `set_of_n_meeting_node_union` | `setOfNMeetingNodeUnion` | 标准三 |
| 10 | 1052 | `b_tame_explicit` | `bTameExplicit` | 标准三 |
| 11 | 1075 | `squanderVertex_explicit` | `squanderVertexExplicit` | `[propext]` |
| 12 | 1098 | `vertextypes_explicit` | `vertextypesExplicit` | 标准三 |
| 13 | 1137 | `no_except_empty` | `noExceptEmpty` | 标准三 |
| 14 | 1148 | `no_except_wfloor` | `noExceptWfloor` | 标准三 |
| 15 | 1172 | `set_of_exceptional_meeting_node_identity` | `setOfExceptionalMeetingNodeIdentity` | 标准三 |
| 16 | 1181 | `adm_2_floor_adm_2` | `adm2FloorAdm2` | 标准三 |
| 17 | 1246 | `adm_3_floor_adm_3` | `adm3FloorAdm3` | 标准三 |
| 18 | 1293 | `tame_13_a_floor_tame_13_a` | `tame13aFloorTame13a` | 标准三 |
| 19 | 1305 | `sumn_cons` | `sumnCons` | `[propext]` |
| 20 | 1313 | `sumn_nsum` | `sumnNsum` | 标准三 |
| 21 | 1330 | `uniq_facesAt_list` | `uniqFacesAtList` | `[propext, Quot.sound]` |
| 22 | 1342 | `BIJ_NSUM` | `BIJNSUM` | 标准三 |

逐条陈述 `#check @`（全显式）见 `logs/stmt_probe.log`；与 HOL 的载体折算逐项一致
（`sumn`↦`List.sum`、`nsum`↦本地 `nsum`、`CARD`↦`Set.ncard`、`&`↦`Nat.cast`、
`dart`↦`H.darts`、`adm_1/2/3`↦`Adm1/2/3`、`tame_9a/13a`↦`Tame9a/13a`、
`face_set`↦`H.faceSet`、常数表↦`Kepler.Graphs.*`）。

## 6. 常数表逐值核对

- `bTame` 15 值（`bTameExplicit`）：0.618 / 0.97 / 0.656 / 0.618 / 0.797 / 0.412 /
  1.2851 / 0.311 / 0.817 / 0.347 / 0.366 / 0.04 / 1.136 / 0.686 / 1.450，默认 `tgt=1.541`；
- `squanderVertex` 15 值（`squanderVertexExplicit`）：6177 / 9696 / 6557 / 6176 / 7967 /
  4116 / 12846 / 3106 / 8165 / 3466 / 3655 / 395 / 11354 / 6854 / 14493，默认
  `squanderTarget=15410`；
- **slack 陷阱已按 PLAN 风险 6 处理**：未把 `bTame*10000 = squanderVertex` 当引理；
  `adm2FloorAdm2` 只用逐项成立的 `squanderVertex p q + p + q ≤ bTame p q * 10000`
  （`svAddLeBTameMul`，15 项全部取等，逐项 `norm_num` 核对），
  `wtFloorLeWt` 只在 `CARD > 4` 支用 `squanderFace n = d_tame n * 10000`
  （`squanderFace_eq_dTame_mul`，n=5/6/≥7 三档；n=4 的 2058 vs 2060 slack 已避开）。

## 7. 新增本地载体（HOL 有 / Lean 侧无同名件；均为 def，未改既有陈述）

- `nsum`（HOL `nsum = iterate (+)`）：`if s.Finite then ∑ x ∈ h.toFinset, f x else 0`；
- `nfloor d x := ⌊x * d⌋₊`（HOL `new_specification` 规格由 `nfloorExists` 钉死）；
- `wtFloor` / `Adm1Floor` / `Adm2Floor` / `Adm3Floor` / `Tame13aFloor`（HOL :878/:881/:884/:890/:894 逐字）；
- `facesAtList`（HOL `faces_at_list = FILTER (MEM v) L`，tame_defs2.hl:688）；
- `BIJ`（HOL `BIJ` 三合取：maps-to ∧ InjOn ∧ surj）；
- `isVertexType` / `vertexPairs`（HOL 15 元析取的语法缩写与 List 形；
  `vertextypesExplicit` 的**陈述仍写逐字析取**）。

## 8. 与工单的偏差 / 注记

1. `vertextypesExplicit` 的 `h9 : Tame9a H` 在证明中未被消费（HOL 同款证明也把
   `tame_9a` 分支 kill 掉）；`adm3FloorAdm3` 的 `h9`/`h1` 未被消费（HOL 用它们只为
   `wt_floor_nn` 的非负性，Lean 的 `nfloor` 上界是单边的）。**陈述保留全部 HOL 前提**，
   仅证明不消费；已 `set_option linter.unusedVariables false` 消噪。
2. `bTame 5 0 = 0.04` 的 `#check` 打印为 `4e-2`（同一实数的科学计数打印），非陈述差异。
3. 未触碰 `Adm3` 陈述分叉（Assembly 版 `True` 尾 / TameLp 版真陈述）；本波只做 floor/sum/BIJ，
   未修改任何既有文件。
4. 行数 837（工单估 900–1,050 的下沿略低；无 GAP，无止损）。

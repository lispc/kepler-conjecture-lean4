# DELIVERY — tamecorr-w3w1（W3 第一波）

**结论：22/22 DONE，0 GAP，0 sorry / 0 axiom / 0 native_decide。**
新文件 `lean/Kepler/Text/TameCorrFloor.lean`，**837 行**，standalone `nice -n 19 lake env lean`
**RC=0 / 0 error / 0 sorry**；22 件 `#print axioms` 全部 ⊆ `[propext, Classical.choice, Quot.sound]`。

## 落库

```
git apply <本目录>/patch.diff          # 新增 lean/Kepler/Text/TameCorrFloor.lean
git add -N lean/Kepler/Text/TameCorrFloor.lean
cd lean && bash scripts/auto_gate.sh Kepler/Text/TameCorrFloor.lean
```
（本文件为纯新增；无删除面；无既有文件改动。）

## 主仓状态

HEAD `17d1df89`；`git status --porcelain` = 仅
`?? lean/Kepler/Text/TameCorrFloor.lean`（tracked 零改动）。

## import 与环

- `import Kepler.Text.TameLp` + `import Kepler.Graphs.Tame`（**不 import `Kepler.Assembly`**）。
- 环自检（模块闭包内实测）：
  `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  → `error(lean.unknownIdentifier): Unknown identifier ...`（`logs/axioms_probe.log` 末行）。
- 故 Assembly 可安全 import 本模块（不把岛 74/75 的边翻成环）。

## 交付件

| 文件 | 说明 |
|---|---|
| `patch.diff` | 相对 HEAD `17d1df89` 的新增文件补丁（843 行，`git apply --check --reverse` OK） |
| `TameCorrFloor.lean` | 新文件副本 |
| `Evidence.md` | 22 件对照表 + 全量 `#print axioms` 实测 + 环自检 + 常数表核对 |
| `logs/standalone_lean.log` | standalone 编译输出（空 = 0 error/0 warning/0 sorry） |
| `logs/axioms_probe.log` | 22 件 axioms + 环自检 |
| `logs/stmt_probe.log` | 22 件 `#check @` 全显式陈述（逐字对表） |
| `logs/axioms_probe.lean` / `logs/stmt_probe.lean` | 探针源（模块副本 + 探针），编排者可独立复跑 |

## 下一波起手点（W3-W2）

1. **G1+G2**（`PLAN.md` §F W3-W1'）：11 个 `tame*_list` def + `facesAt_list` 的
   filter/长度桥 15 件（HOL :170-:520）。前置：`TameLp.hypermapOfList`（已就位）+
   List_hypermap 缺口 5–7 件（`face_set_eq_list`/`components_hypermap_of_list`/
   `uniq_faces_of_list`/`uniq_list_of_elements`/`card_nodes_of_list`/
   `good_list_nodes_condition`/`face_of_list`）。
2. **G8 的硬前置已由本波落地**：`nsum` / `BIJNSUM` / `sumnNsum` / `uniqFacesAtList` /
   `wtFloor` / `Adm1/2/3Floor` / `Tame13aFloor` / `adm2FloorAdm2` / `adm3FloorAdm3` /
   `tame13aFloorTame13a`，G8 `tame13a_correspondence` 可直接消费，不必重证。
3. **仍未解**（本波不碰）：`Adm3` 陈述分叉（DEF-FIX 待裁）、TameLp 版
   `TamePlanarHypermap` 与 Assembly 版孪生组件的桥、Oxaxucs iso 族 24 件。
4. 建议 W3-W2 继续沿用本模块的落点策略（只 import TameLp/Graphs/后续 Assembly-free 新叶），
   保持“Assembly 反向可 import”的零环不变式。

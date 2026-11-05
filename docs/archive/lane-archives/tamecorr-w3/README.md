# tamecorr-w3 — `tameCorrespondenceIso` 实体移植（已收官）

**目标**：把 HOL `WMLNYMD.hl`（1,515 行 / 56 个 `prove*` 块）及其上游 `OXAXUCS.hl`
的 iso 不变家族，移植成 Assembly-free 的 Lean 证明，最终闭掉 `Assembly.tameCorrespondenceIso`
（hTC 三件之一、主线 3 号 sorry）。

**结果（2026-11-06）**：**全闭**。`Assembly.tameCorrespondenceIso` 的 `#print axioms` =
`[propext, Classical.choice, Quot.sound]`，陈述逐字未动。

## 1. 模块表（16 文件 / 3,967 行）

| 模块 | 行 | 内容 | 波次 |
|---|---:|---|---|
| `TameCorrBase.lean` | 174 | `IsHypermapOfListTl` 唯一性/典范性（S1 桥） | 前作 `aa567796` |
| `TameCorrFloor.lean` | 837 | G6 floor 18 + G7 sum/BIJ 4 = 22 件 | W3-W1 |
| `TameCorrList.lean` | 357 | 15 条 G2 桥 + 11 个 `*_list` def + 8 图侧镜像 def | W3-W2 |
| `TameCorrG3.lean` | 141 | G3 8 件（admissible 权重表 / sumn_rot / sumn_perm_eq …） | W3-W3 |
| `TameCorrCard.lean` | 259 | `List_hypermap` 缺口 4 件 + G1 第一件 | W3-W4 |
| `TameCorrNode.lean` | 377 | node 轨道引擎 6 件 + `dartOf` 族 4 件 + G1 第二件 | W3-W5a |
| `TameCorrG4.lean` | 208 | G4 头两件（`setOfNMeetingNode` / `cardSetOfNMeetingNode`） | W3-W6 |
| `TameCorrG4b.lean` | 84 | G4 余两件（`_pqr` / `typeOfNodeVertextype`） | W3-W7 |
| `TameCorrNodeCard.lean` | 251 | `dartOfNode` BIJ / `dartOfCardNode` / `dartOfCardFace` | W3-W8a |
| `TameCorrG5.lean` | 162 | G5 两件（`tame11` / `tame12o` 反向对应） | W3-W8b |
| `TameCorrFaceSet.lean` | 119 | `facesOfList` / `uniqFacesOfList` / `faceSetEqList` | W3-W9 |
| `TameCorrG8.lean` | 185 | **`tame13aCorrespondence`**（本体最后一个 prove 块） | W3-W9 |
| `TameCorrG9.lean` | 77 | **`tameCorrespondence1`**（:1473 装配层） | W3-W10 |
| `TameCorrIso.lean` | 251 | S4 W1：`isoImpHypsIso` + `tame9aIso/10/11a` + 典范性件 + 7 引擎 | W3-W10 |
| `TameCorrIso2.lean` | 415 | S4 余三件：`tame11bIso` / `tame12oIso` / `tame13aIso` + 12 引擎 | W3-W11a |
| `TameCorrMain.lean` | 70 | **`tameCorrespondenceIso`**（HOL :1498 主定理） | W3-W11b |

累计 **97 件公开定理**（含引擎件），逐波 `#print axioms` 实测，**全部 ⊆ 标准三、零 `sorryAx`**。

## 2. 三个桥的实测判决（Assembly 接线用）

| 桥 | 判决 |
|---|---|
| `Assembly.HypermapIso ↔ Hypermap.Iso` | **defeq**（同一常量，Assembly 侧是 def 别名） |
| `Assembly.GoodGraphV4 ↔ TameCorrList.GoodGraphV4` | **defeq**（8 个图侧镜像 def 逐字抄体） |
| `Assembly.TamePlanarHypermap ↔ TameLp.TamePlanarHypermap` | **defeq**（探针直接编过，12 槽无需搬运） |
| `Assembly.IsHypermapOfList ↔ TameLp.IsHypermapOfListTl` | **不是 `Iff.rfl`**（同 4 字段、不同 structure 常量）⇒ 四字段匿名构造器各一行折算 |

接线实现（`Assembly.lean`，陈述逐字未动）：

```lean
theorem tameCorrespondenceIso … : tame g := by
  have hIs' : Kepler.Text.TameLp.IsHypermapOfListTl g.fgraph H' :=
    ⟨hIs.darts_eq, hIs.edgeMap_eq, hIs.nodeMap_eq, hIs.faceMap_eq⟩
  exact Kepler.Text.TameCorrMain.tameCorrespondenceIso g H H' hgg ht hiso hIs'
```

## 3. 关键判定：典范性把 S4 从 1.0–1.3k 行压到 ~0.3k

侦察原估 S4 `OXAXUCS` iso 族 24 件 / 1,040–1,290 行，前提是「任意 `H'` 都要维护列表对应」。
W3-W10 实测：

```
isHypermapOfListTl_iff_eq_hypermapOfList : IsHypermapOfListTl L H ↔ H = hypermapOfList L hL
```

`.mp` 直接给出 `H' = hypermapOfList L hL`，三条使用路线（① 直接取等式；② 目标侧 `rw`；
③ 假设侧 `Iso` 运输）全部编译通过，固化为 `isHypermapOfListTl_eq_canonical`（标准三）。
⇒ 六件 `tame*_iso` 统一取 canonical，**18 件支撑 iso 可省**，实际只做 3 件（415 行）。
详见 `docs/archive/lane-archives/tamecorr-iso-scout/SIZING.md` §3.1。

## 4. 纪律（逐波执行）

- **零 `import Kepler.Assembly`**：每波环自检 `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  → `unknownIdentifier`。
- 每件 `#print axioms` 实测（`sumnPermEq`/`dartOf_fst` 等只用 core 的件如实报 `[propext]`）。
- 零 `sorry`/`axiom`/`admit`/`native_decide`；陈述不凑。
- 每文件 ≤450 行，超了拆模块。

## 5. 与本车道无关的相邻项

- `jcajydu`（HOL `JCAJYDU.hl`）是**反方向**（restricted hypermap → plane graph），
  属 W2 链（`Reduction5`），**不在本章范围**。
- `fcdjdot`（poly 簇）属 `pa22-poly-*` 序列。

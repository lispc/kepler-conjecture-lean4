# RECON — tame-correspondence W1（P6-C 桥 + `RXOKSKC`）

- 车道：`tamecorr-w1`；主仓 `/Users/zhangzhuo/repos/kepler-conjecture-lean4`；HEAD `873d2a2c`
- 只新建：`lean/Kepler/Text/TameCorrBase.lean`（`git add -N` 已做）
- HOL 源：`reference/flyspeck/text_formalization/tame/{JCAJYDU.hl,RXOKSKC.hl,auqtzyz.hl}`
- 侦察期环境注记：**另一车道正在并发重建 `.lake`**（`LocalAuto*`/`TameLp`/`LocalConcl` olean 反复消失再出现），
  本文所有编译结论均为"重试至非 transient 后取得"的记录（`logs/`）。本波未执行任何 `lake` 命令、未写 `.lake`。

---

## Step 0.1 — `TameLp.hypermapOfList` 与 `Assembly.IsHypermapOfList` 的逐一对应

**结论：语义一致（`fgraph ℕ` 载体内逐槽同体），无偏差，不需要 SF/DEF-FIX 裁决。**

### 规格侧（`lean/Kepler/Assembly.lean:194`）

```
structure IsHypermapOfList (L : fgraph ℕ) (H : Hypermap (ℕ × ℕ)) : Prop where
  darts_eq   : (↑H.darts : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L}
  edgeMap_eq : ∀ d ∈ H.darts, H.edgeMap d = eList d
  nodeMap_eq : ∀ d ∈ H.darts, H.nodeMap d = nList L d
  faceMap_eq : ∀ d ∈ H.darts, H.faceMap d = fList L d
```

### 构造侧（`lean/Kepler/Text/TameLp.lean`，§9 `S1HypermapOfList`）

| 规格字段 | 构造侧定理 | 位置 | 类型是否逐字相同 |
|---|---|---|---|
| `darts_eq` | `darts_hypermapOfList` | TameLp:5220 | 是（同一 `Set` 等式） |
| `edgeMap_eq` | `edgeMap_hypermapOfList` | TameLp:5225 | 是（`{d} → d ∈ darts → edgeMap d = eList d`） |
| `nodeMap_eq` | `nodeMap_hypermapOfList` | TameLp:5231 | 是 |
| `faceMap_eq` | `faceMap_hypermapOfList` | TameLp:5238 | 是 |

- 构造本体：`noncomputable def hypermapOfList (L : fgraph ℕ) (hL : GoodList L) : Hypermap (ℕ × ℕ)`（TameLp:5188）。
  假设只有一个：`hL : GoodList L`（`Kepler.Assembly.GoodList`，`Assembly/GoodListDefs.lean:72`：
  `(listOfDarts L).Nodup ∧ (∀ l ∈ L, l ≠ []) ∧ ∀ d ∈ listOfDarts L, (d.2,d.1) ∈ listOfDarts L`）。
- 四字段之外没有第五条义务：HOL 侧 `res` 的"dart 集外恒等"由 Lean `Hypermap` 的
  `*_permutes : PermutesOn _ darts`（= `∀ x ∉ s, f x = x`，`Hypermap.lean:678`）字段承载；
  `comp_eq_one` 由 `Hypermap` 的打包字段承载。**这与 `Assembly.lean:186-188` 的注释一致，无需额外合取项。**
- 孪生结构 `TameLp.IsHypermapOfListTl`（TameLp:6126）四槽逐字同体，实例定理
  `hypermapOfList_isHypermapOfListTl`（TameLp:6139）已在库且标准三（实测，`logs/probe1.log`）。
- **载体口径差异（非语义偏差，已记档）**：HOL `hypermap_of_list` 的行类型是 `(A->bool) list`
  （结点集列表），Lean `Assembly.listOfDarts/hypermapOfList` 的行类型是 `List ℕ`（`fgraph ℕ`）。
  规格与构造**两侧都在 `fgraph ℕ`** 上陈述，故桥上无失配；HOL 的**一般类型 A** 形态另在
  TameSpine 线以 `List (List (Set α))` + `hypermapOfListG` 承载（见 Step 0.3）。

### 已存在的同命题件（侦察发现，未重复劳动）

`lean/Kepler/Text/TameSpine/Keystone.lean:117` 已有
`isHypermapOfList_hypermapOfList : Assembly.IsHypermapOfList L (TameLp.hypermapOfList L hL)`，
证明 = 孪生桥 + TameLp 实例定理（转发形）。本波新件 `TameCorrBase.hypermapOfList_isHypermapOfList`
是**直接四槽组装**（不经孪生桥），两者独立、结论相同、互不 import。

---

## Step 0.2 — 桥所需子引理清点（逐个 `grep` + 编译级 `#check`）

| 需要的事实 | 仓内是否已有 | 位置 |
|---|---|---|
| `darts (hypermapOfList L hL) = listOfDarts L`（集合形） | **有** | `TameLp.darts_hypermapOfList` :5220 |
| `edgeMap` 在 dart 上 `= eList` | **有** | `TameLp.edgeMap_hypermapOfList` :5225 |
| `nodeMap` 在 dart 上 `= nList L` | **有** | `TameLp.nodeMap_hypermapOfList` :5231 |
| `faceMap` 在 dart 上 `= fList L` | **有** | `TameLp.faceMap_hypermapOfList` :5238 |
| `eList/nList/fList/findFaceDarts/nextEl/prevEl/listOfDarts/listPairs` 定义 | **有** | `Assembly/GoodListDefs.lean:24-62` |
| `GoodList` 定义 + Bool 反射器 | **有** | `Assembly/GoodListDefs.lean:72,89` |
| `Hypermap` 结构 + `PermutesOn` + 群律 | **有** | `Text/Hypermap.lean:765,678,830-840` |
| `IsHypermapOfListTl` 孪生 + 实例定理 | **有** | `TameLp.lean:6126,6139` |
| `hypermapOfList` 的 MAP/REVERSE 运输族（`la7_*`，W2 编码步要用） | **有** | `TameLp.la7_hypermapOfList_map` :6065 等 |
| 规格解的 `Finset` 形 / 成员判定形 | **缺** → 本波补 | `TameCorrBase.darts_hypermapOfList_finset` 等 |
| 规格解的唯一性 / 典范性 | **缺** → 本波补 | `TameCorrBase.isHypermapOfList_unique` 等 |

编译级验证：`logs/probe1.log`（直接四槽组装 + `#print axioms` 标准三）、`logs/build-TameCorrBase.log`。

---

## Step 0.3 — `RXOKSKC` 移植规模评估（结论：**已在库，HEAD 上已收口**）

HOL `RXOKSKC.hl` 1,105 行，12 个 `let`。**逐站已在 TameSpine 线以一般类型 α 形态落地**：

| HOL 站 | 行 | Lean 件 | 位置 |
|---|---|---|---|
| `UNIQ_LIST_OF_DARTS` | :25 | `rxUniqListOfDarts` | `TameList66.lean:209` |
| `MEM_CONS` | :118 | 平凡（`List.mem_cons_self` 类） | — |
| `LIST_OF_SET_SING` | :122 | 不需要（Lean 用 `Finset.image … |>.toList`） | `TameList68.lean:272`（`RxOkData.L`） |
| `EXISTS_LIST_FACE_NODE` | :133 | `existsListFaceNode` | `TameList66.lean:287` |
| `EXISTS_LIST_FACE_NODE2` | :223 | 折入上件 | — |
| `EXISTS_LIST_FACE_NODE_FUNC` | :229 | `existsListFaceNodeFunc` | `TameList66.lean:340` |
| `LIST_COR_FACE_SET` | :293 | `listCorFaceSet` | `TameList66.lean:399` |
| `LIST_COR_FACE_SET1` | :418 | `listCorFaceSet1` | `TameList66.lean:451` |
| `ONE_TO_ONE_DART` | :474 | `oneToOneDart` | `TameList66.lean:498` |
| `MEM_LIST_DARTS` | :496 | `rxMemListDarts` | `TameList65.lean:217` |
| `SYM_LIST_DART` | :507 | `symListDart` | `TameList65.lean:225` |
| **`RXOKSKC`（主件）** | :523 | **`RXOKSKC`** | **`TameList69.lean:605`** |

主件形态（实测源码）：

```
theorem RXOKSKC (H : Hypermap α) (hr : H.IsRestricted) :
    ∃ L : List (List (Set α)), ∃ hL : rxGoodList L,
      (∀ l ∈ L, l.Nodup) ∧ rxGoodListNodes L hL ∧ H.Iso (hypermapOfListG L hL)
```

- 支撑结构 `RxOkData`（`TameList68.lean:253`）= HOL `:527-:532` 的 `f/S/L` 五前件；
  五个槽定理 `allUniq_L` / `goodList_L` / `goodListNodes_L` / `iso_hypermapOfListG`（`TameList69.lean:184/272/575/441`）。
- **规模实测**：HOL 1,105 行 ↔ Lean `TameList65`(261) + `66`(553) + `68`(516) + `69`(615) ≈ **1,945 行**
  （不含其依赖的 65 批前序链条，`TameList1..64` 合计 ≈ 20k 行）。
- **公理面实测**：`RXOKSKC` / `goodList_L` / `goodListNodes_L` / `iso_hypermapOfListG`
  = `[propext, Classical.choice, Quot.sound]`（`logs/probe2.log`）。
- 载体口径：行类型 = `List (Set α)`（HOL `(A->bool) list` 直译），非 `fgraph ℕ`。

**推论（对 W2 的硬影响）**：W1 原定的两件主交付在 HEAD 上都已存在且标准三。
本波的实际增量因此转为：① 机器验证并收口 P6-C 桥（含唯一性/典范性等 W2 需要的求值律）；
② 给出 `RXOKSKC` 的精确索引与**剩余真实缺口**（下节）。

---

## Step 0.4 — 剩余真实缺口（W2 `jcajydu` 的阻塞项，实测）

1. **`jcajydu` 的陈述比 HOL 强**：HOL `JCAJYDU`（`JCAJYDU.hl:51-91`）是
   `(∀Ln. good_list Ln ∧ good_list_nodes Ln ∧ is_restricted (hypermap_of_list Ln) → ∃gn. PlaneGraphs gn ∧ …)
     ==> (∀H. is_restricted H → ∃gH. PlaneGraphs gH ∧ …)`；
   Lean `Assembly.jcajydu`（:2441）**没有该前提参数**，直接 `(H) (hres) : ∃ g, PlaneGraphs g ∧ GoodGraphV4 g ∧ …`。
   HOL 前提在 Lean 侧无对应定理：`Reduction5.restricted_hypermaps_are_planegraphs_thm`
   全仓只在 `Assembly.lean:1969` 的注释里出现，**无 Lean 证明**（`grep` 实测零命中）。
   → 这是 SF/DEF-FIX 级裁决点（补前提参数，或移植 Reduction5），**本波不自行改陈述**。
2. **载体编码**：`RXOKSKC` 产出 `List (List (Set α))`，`GoodGraphV4` 需要 `Graph`（`g.fgraph : fgraph ℕ`）。
   中间需要：有限 dart 集到 ℕ×ℕ 的单射 + 行映射 + `Graph` 构造 + `PlaneGraphs/GoodFacesV3/VerticesSet2Eq/FinalGraph`
   六合取项。`TameLp` 的 `la7_*`（`la7_hypermapOfList_map` :6065）只覆盖 `φ : ℕ → ℕ`，跨类型编码需一般 φ 版本。
3. **已就位、无需重做**：`is_restricted` 沿 iso 的运输（`TameList15.isoRestrictedIff:655` 公开一般形；
   `TameList1.iso_isRestricted_of_iso:454` 为其私件证明）；HOL `iso_list_restricted` 的列表形
   （`TameList19.isoListRestricted:331`）。

---

## import 闭包（BFS，无环证明）

`TameCorrBase.lean` 头：`import Kepler.Text.TameLp` + `import Kepler.Assembly`。

- 闭包：`TameCorrBase → {TameLp, Assembly}`；`Assembly → TameLp`（Assembly.lean:42）；
  `TameLp → {Graphs.PlaneGraphIso, Assembly.GoodListDefs, LocalAuto16, …}`（既有 DAG）。
- **无环**：`grep -rn "import Kepler.Text.TameCorrBase" lean/` 零命中 ⇒ 新节点是**叶子**（汇点），
  只新增入边、不新增任何环。`Assembly` 已是 TameLp 的下游，本模块不改变既有 DAG 的拓扑。
- 未引入任何新依赖包；未新增 instance / `@[simp]` / abbrev（零全局泄漏）。

---

## 附录 A — 施工口径变更（用户 2026-11-05 批）

初版 `TameCorrBase.lean` 头为 `import Kepler.Text.TameLp` + `import Kepler.Assembly`，桥直接陈述在
`Assembly.IsHypermapOfList` 上（该版曾编译 RC=0、标准三，见 `logs/build-TameCorrBase.log`）。
随后确认 `Kepler.Assembly` 传递 import **`Kepler.Interval.Cases.*`**（证书 shard；当前
237 个源文件 vs 36 个 olean，正在重建），使任何 import Assembly 的模块在重建窗口内**无法验证**。

经用户批准改为**只依赖 `Kepler.Text.TameLp`**：

- 全部结论改述到 `TameLp.IsHypermapOfListTl`（TameLp:6126）；四字段求值律与规格实例定理
  （`hypermapOfList_isHypermapOfListTl`:6139）**直接引用、不重复**；
- Assembly 层 `IsHypermapOfList` 的搬运 = 一行匿名构造器
  `⟨h.darts_eq, h.edgeMap_eq, h.nodeMap_eq, h.faceMap_eq⟩`，**显式登记为 W2 义务**（本模块刻意不 import）；
- 语义零损失：§Step 0.1 已证四槽逐字同体；收益 = 与 shard 重建解耦、可落库。
- 实证（阴性对照）：同 `LEAN_PATH` 下 `import Kepler.Assembly` 的探针 rc=1
  （缺 `Interval/Cases/CQITNPEAx3725403817/Shard490.olean`，`logs/probe-asm2.log`），
  而本模块 rc=0 / 0 error / 8 件标准三（`logs/build-TameCorrBase-tamelp.log`）。
- 旧版证据保留在 `logs/`（`build-TameCorrBase.log`、`probe1-3.log`），仅作历史对照。

§Step 0 的三项侦察结论（语义一致 / 子引理在位 / `RXOKSKC` 已在库）与 §Step 0.4 的 W2 缺口**不受本变更影响**。

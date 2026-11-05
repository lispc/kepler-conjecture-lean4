# EVIDENCE — `island-deassembly-scout`

所有命令均只读 + 探针；主仓 `lean/` 无 tracked 文件改动（`git status` 末尾附）。
探针源码与日志在 `logs/`；patch 在 `logs/island_deassembly.patch`。
机器：macOS darwin 27.0.0 arm64，`leanprover/lean4:v4.32.2`（`lean-toolchain`），
主仓 HEAD `31b7227e`，探测日期 2026-11-06。侦察期间编排者推进到 `0abccb51`；
`git diff 31b7227e..HEAD` 仅 2 个 docs 文件（ERRATA + priority-queue），
5 个待改岛文件 + `Assembly.lean` + `TameLp.lean` 零 diff，分析基线不变。

---

## 0. 起点复核（与工单口径对齐）

```console
$ grep -rn "import Kepler.Assembly" --include="*.lean" Kepler/ | wc -l
60
$ grep -rn "import Kepler.Assembly$" --include="*.lean" Kepler/Text/TameSpine/
TameList1.lean:37  TameList2.lean:63  TameList3.lean:72  GoodGraph.lean:43  Keystone.lean:36
```

全仓直接 `import Kepler.Assembly` 的文件只有 6 个（5 个岛 + `Kepler/Final.lean`）：

```console
$ grep -rln "^import Kepler.Assembly$" --include="*.lean" Kepler/
Kepler/Final.lean
Kepler/Text/TameSpine/TameList3.lean
Kepler/Text/TameSpine/GoodGraph.lean
Kepler/Text/TameSpine/Keystone.lean
Kepler/Text/TameSpine/TameList1.lean
Kepler/Text/TameSpine/TameList2.lean
```

岛规模（机器计数）：75 文件 / 32,435 行 / 899 公开声明 + 347 私有声明；
唯一裸 `sorry` 在 `TameList16.lean:1109`（`markedListIsNodeNondegenerate`，有 NEEDS 记账），
其余 `sorry` 字样全是注释。与 `docs/priority-queue.md` §19 的 899/347 逐位吻合。

### 0.1 勘误（以机器证据为准）

工单/`docs/priority-queue.md` §19 口径：「74 个文件经 TameList1→Assembly 传递**成环**」。
静态 import 图实测：**当前不存在环**——`Kepler.Assembly` 的传递闭包中 TameSpine 模块数 = 0，
`Kepler.Text.LocalConcl` 闭包中 TameSpine 模块数 = 0：

```console
$ python3 -I logs/cycle_probe.py
Kepler.Assembly closure size 4229 TameSpine modules: 0 []
Kepler.Text.LocalConcl closure size 108 TameSpine modules: 0 []
TameList1 -> Assembly: Kepler.Text.TameSpine.TameList1 -> Kepler.Assembly
```

准确形状是**单向下游边** `island → Assembly`（Assembly 从不 import 岛），
一旦 Assembly 想消费岛就会**造出**环。这不改变结论，只改变措辞：
去 Assembly 化 = 删掉这条下坡边，使 `Assembly → island` 合法。

---

## 1. A — 10 个声明的逐个判决（机器可读版 = `DECL-VERDICTS.tsv`）

### 1.1 关键反向发现：10 个里 9 个根本不是 Assembly 的高层声明

`open Kepler.Assembly (...)` 在岛内出现的全部名字（多行 open 也解析）只有 9 个，
且 9 个全部声明在低层 `Kepler/Assembly/GoodListDefs.lean`：

```console
$ python3 - <<'EOF'   # 解析 open ... (...) 直到右括号
... 收集 75 个岛文件的 open Kepler.Assembly 名单 ...
EOF
GoodList 42 42
nextEl 40 39
listOfDarts 34 34
listPairs 33 33
fList 27 27
eList 25 25
prevEl 18 18
findFaceDarts 18 18
nList 14 14
```

`GoodListDefs` 不是声明，是模块；`TameLp.lean:38` 已经 `import Kepler.Assembly.GoodListDefs`
——即岛**本来就有**低层列表机器在闭包里。

真正只在 `Kepler/Assembly.lean` 主文件里声明的只有 4 个：
`HypermapIso`(177)、`IsHypermapOfList`(195)、`oppositeHypermap`(2145)、`GoodGraphV4`(2238)。
其中 `oppositeHypermap` 的岛内「1 处引用」是 `TameOpposite1.lean` 的**注释**（:62），
代码零引用；`TameOpposite1.lean:66` 已有逐字孪生 def。

### 1.2 判决表摘要

| # | name | Assembly 行 | kind | 低层对应物 | Iff.rfl | 判决 |
|---|---|---|---|---|---|---|
| 1 | HypermapIso | Assembly.lean:177-184 | def | `Kepler.Text.Hypermap.Iso` @ Hypermap.lean:8249 | **是** | REDIRECT |
| 2 | nextEl | GoodListDefs.lean:44（经 Assembly.lean:45 转发） | def | 同一常量 | 同一常量 | REDIRECT |
| 3 | IsHypermapOfList | Assembly.lean:195-204 | structure | `TameLp.IsHypermapOfListTl` @ TameLp.lean:6126 | 否；四槽重打包（Keystone.lean:99-102 已有证明） | REDIRECT |
| 4 | GoodListDefs | Assembly.lean:45 | module | 本身 | — | REDIRECT |
| 5 | listPairs | GoodListDefs.lean:34 | def | 同一常量 | 同一常量 | REDIRECT |
| 6 | listOfDarts | GoodListDefs.lean:38 | def | 同一常量 | 同一常量 | REDIRECT |
| 7 | GoodList | GoodListDefs.lean:72 | def | 同一常量 | 同一常量 | REDIRECT |
| 8 | oppositeHypermap | Assembly.lean:2145-2158 | def | `TameSpine.oppositeHypermap` @ TameOpposite1.lean:66 | **是**（rfl） | REDIRECT |
| 9 | eList | GoodListDefs.lean:59 | def | 同一常量 | 同一常量 | REDIRECT |
| 10 | GoodGraphV4 | Assembly.lean:2238-2240 | def | `TameSpine.GoodGraphV4Spine` @ GoodGraph.lean:118 | **是** | REDIRECT |

**分布：REDIRECT 10 / HOIST 0 / KEEP-IMPORT 0。**

---

## 2. B — 依赖闭包与「第二个洞」（HOIST 数为 0，以下为反事实分析）

| 反事实 HOIST 候选 | 类型/体引用常量 | 只在 Assembly 存在的依赖 | 低层可满足？ |
|---|---|---|---|
| HypermapIso | `Hypermap`, `Set.BijOn`, darts/edgeMap/nodeMap/faceMap | 无 | 是（Hypermap + Mathlib） |
| IsHypermapOfList | `fgraph`, `Hypermap`, `listOfDarts`, `eList`, `nList`, `fList` | 无 | 是（GoodListDefs + Hypermap） |
| oppositeHypermap | `Hypermap`, `PermutesOn.mul/symm`, `mul_inv_cancel`, `mul_assoc` | 无 | 是（Text/Hypermap） |
| GoodGraphV4 | `GoodList`, `GoodListNodes`, `FinalGraph`, `AllUniq`, `GoodFacesV3`, `VerticesSet2Eq` + `TameLp.hypermapOfList/nodesOfListSet/elementsOfList` | **5 个 helper**（`GoodListNodes`/`FinalGraph`/`AllUniq`/`GoodFacesV3`/`VerticesSet2Eq`）+ 2 个支撑 def（`verticesSet2`/`facesAtV2`） | 是（Graph + TameLp；见 GoodGraph.lean:59-120 的逐字 Spine 镜像） |

结论：
- **无一个依赖指向 `Contravening` / `textCapstone` / `FAN` 这类高层件**；最深的只有
  `GoodGraphV4` 的 7 件 Assembly-local 集群，且它们自身全是 Graph/TameLp 层可承载。
- **10 个声明里真正「搬不动」的 = 0**。实际成本不在依赖洞，而在引用改写的胶水。
- 唯一「第二个洞」是**模块级**的，不是声明级：`import Kepler.Assembly` 同时供给了
  `Kepler.Graphs` umbrella。删掉后 `Graph/Face/makeFaceFinal/replace/setFinal/...`
  全部消失（实测见 §3.1）。已在方案中用 `import Kepler.Graphs` 补上。

---

## 3. C — 施工面与语义等价

### 3.1 施工面（5 文件，157 行 diff，净 +2 行）

`logs/island_deassembly.patch` 全文。逐处清单：

| 文件 | 行 | 改动 |
|---|---|---|
| `TameList1.lean` | 37 | `import Kepler.Assembly` → `import Kepler.Assembly.GoodListDefs`；38 行新增 `import Kepler.Graphs` |
| `TameList2.lean` | 63 | 同上（无新增行） |
| `TameList3.lean` | 72 | 同上（无新增行） |
| `Keystone.lean` | 36 | import 换低层模块 |
| `Keystone.lean` | 54,58,63,67,74×2,81×2,82,88 | `Kepler.Assembly.HypermapIso` → `Hypermap.Iso`（10 处） |
| `Keystone.lean` | 100,107,118,123 | `Kepler.Assembly.IsHypermapOfList` → `TameLp.IsHypermapOfListTl`（4 处） |
| `GoodGraph.lean` | 43 | import 换低层模块；44 行新增 `import Kepler.Graphs` |
| `GoodGraph.lean` | 129 | `Kepler.Assembly.GoodGraphV4` → `GoodGraphV4Spine` |
| `GoodGraph.lean` | 146 | `Kepler.Assembly.IsHypermapOfList` → `TameLp.IsHypermapOfListTl` |

下游 69 个岛文件的 `open Kepler.Assembly (GoodList nextEl ...)` **零改动**：
namespace 仍存在、9 个名字仍叫 `Kepler.Assembly.*`（只是声明在子模块）。

**为什么必须加 `import Kepler.Graphs`（实测反证）**：只换 `GoodListDefs` 时：

```console
$ ... lean ... GoodGraph.lean
GoodGraph.lean:50:27: error(lean.unknownIdentifier): Unknown constant `Kepler.Graphs.Graph`
GoodGraph.lean:59:22: error: type expected, got (Graph : Type ?u.3 → Type ?u.2 → Type (max ...))
...
$ ... lean ... TameList2.lean
TameList2.lean:72:35: error(lean.unknownIdentifier): Unknown constant `Kepler.Graphs.makeFaceFinal`
... (数十条) ...
```

补 `import Kepler.Graphs` 后 5 个模块全部编译通过（零 error，仅沿用原有 linter warning）。

### 3.2 语义等价探针

`ProbeEquiv.lean`（主仓环境，Assembly 可见）：

```console
$ lake env lean -R /tmp/islanddec/src ProbeEquiv.lean
# 1) HypermapIso ↔ Hypermap.Iso : Iff.rfl        -> 无 error（接受）
# 2) GoodGraphV4Spine ↔ Assembly.GoodGraphV4 : Iff.rfl -> 无 error（接受）
# 3) IsHypermapOfList ↔ IsHypermapOfListTl : Iff.rfl
ProbeEquiv.lean:17:88: error: Type mismatch
  Iff.rfl has type ?m.2 ↔ ?m.2 ...
# 4) 四槽匿名构造器重打包 -> 无 error（接受）
# 5) binder 打印：
@Kepler.Assembly.HypermapIso : {α} → {β} → [DecidableEq α] → [DecidableEq β] → Hypermap α → Hypermap β → Prop
@Hypermap.Iso                : {α} → [DecidableEq α] → {β} → [DecidableEq β] → Hypermap α → Hypermap β → Prop
```

`ProbeOpposite.lean`（主仓环境）：

```console
$ lake env lean ... ProbeOpposite.lean
# rfl 三条全部通过：
example (H) : TameSpine.oppositeHypermap H = Assembly.oppositeHypermap H := rfl
example (H) : (...).darts = (...).darts := rfl
example (H) : (...).edgeMap = (...).edgeMap := rfl
```

`ProbeLowOnly.lean`（只 import `Kepler.Assembly.GoodListDefs`）：

```console
$ lake env lean ... ProbeLowOnly.lean
Kepler.Assembly.GoodList : Kepler.Graphs.fgraph ℕ → Prop
@Kepler.Assembly.listPairs : {α : Type u_1} → List α → List (α × α)
Kepler.Assembly.listOfDarts : Kepler.Graphs.fgraph ℕ → List (ℕ × ℕ)
@Kepler.Assembly.nextEl : {α : Type u_1} → [BEq α] → List α → α → α
Kepler.Assembly.eList : ℕ × ℕ → ℕ × ℕ
ProbeLowOnly.lean:8:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Assembly.GoodGraphV4`
```

⇒ 9 个名字与低层是**同一常量**（不是同名副本）；`GoodGraphV4` 不在低层模块里。

### 3.3 命名歧义（C3）

全仓声明扫描：除 `oppositeHypermap` 外，9 个裸名在全仓只有一处声明（GoodListDefs）。

```console
$ grep -rn "^...\(def\|theorem\|structure\) \(GoodList\|listPairs\|...\)\b" Kepler/
GoodList        -> Kepler/Assembly/GoodListDefs.lean:72   (唯一)
listPairs       -> GoodListDefs.lean:34                    (唯一)
...
oppositeHypermap -> Assembly.lean:2145 AND TameSpine/TameOpposite1.lean:66
```

`oppositeHypermap` 双份在**不同 namespace**（`Kepler.Assembly` vs `Kepler.Text.TameSpine`），
且岛内没有文件同时 `open` 两者 → 零歧义。改指后 Keystone 用 qualified `Hypermap.Iso`，
与 `Kepler.Assembly.HypermapIso` 名字不同，不撞名。

---

## 4. D — 环的最终形态验证

### 4.1 影子副本 ↔ 主仓对应关系

- `/tmp/islanddec/src/Kepler/Text/TameSpine/{Keystone,GoodGraph,TameList1,TameList2,TameList3}.lean`
  = 主仓同名文件的字节副本 + **仅** `logs/island_deassembly.patch` 的改动。
- `/tmp/islanddec/build/Kepler/**` = 主仓 `.lake/build/lib/lean/Kepler/**` 的符号链接镜像，
  **仅**上述 5 个模块的 `.olean` 是本次新编译的真文件；其余（TameLp/Hypermap/
  GoodListDefs/TameList4..72…）全部指向主仓既有 olean。
- 编译命令（每个模块一条，`nice -n 19`，无 `lake build`）：
  `LEAN_PATH=/tmp/islanddec/build:$LEAN_PATH lean -R /tmp/islanddec/src -o /tmp/islanddec/build/Kepler/Text/TameSpine/<M>.olean <M>.lean`
  5/5 绿（日志 `logs/final_compile_*.log`）。

### 4.2 静态闭包（`logs/import_closure2.py`，沿 `^import` 递归）

```console
$ python3 -I logs/import_closure2.py
parsed 18973 Kepler modules
===== CURRENT =====
TameList1: Kepler-closure=4231, contains Kepler.Assembly=True
TameList3: Kepler-closure=4233, contains Kepler.Assembly=True
GoodGraph: Kepler-closure=4231, contains Kepler.Assembly=True
TameList72: Kepler-closure=4302, contains Kepler.Assembly=True
===== PLANNED =====
TameList1: Kepler-closure=757,  contains Kepler.Assembly=False
TameList3: Kepler-closure=759,  contains Kepler.Assembly=False
GoodGraph: Kepler-closure=757,  contains Kepler.Assembly=False
TameList72: Kepler-closure=828, contains Kepler.Assembly=False
CURRENT island files reaching Assembly: 74 / 75
 NOT reaching: ['TameOpposite1']
PLANNED island files reaching Assembly: 0 []
Kepler.Assembly.GoodListDefs: closure=11, contains Kepler.Assembly=False
Kepler.Graphs: closure=629, contains Kepler.Assembly=False
Kepler.Text.TameLp: closure=136, contains Kepler.Assembly=False
Kepler.Text.Hypermap: closure=1, contains Kepler.Assembly=False
```

注：计划态闭包里仍有 **`Kepler.Assembly.GoodListDefs`**（模块名带 Assembly 前缀），
但它是独立模块、其自身闭包（11 模块）不含 `Kepler.Assembly`；工单判据针对模块
`Kepler.Assembly`，故满足。若要求零 `Kepler.Assembly.*` 前缀，需另搬模块（26 importers）。

### 4.3 `unknown identifier` 式反证（影子环境）

`ProbeShadowTameList1.lean`（工单点名对象）：

```console
$ LEAN_PATH=/tmp/islanddec/build:$LEAN_PATH lean ... ProbeShadowTameList1.lean
Kepler.Assembly.GoodList : Kepler.Graphs.fgraph ℕ → Prop
Kepler.Assembly.listOfDarts : Kepler.Graphs.fgraph ℕ → List (ℕ × ℕ)
@Kepler.Text.Hypermap.Iso : ...
ProbeShadowTameList1.lean:7:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Assembly.HypermapIso`
ProbeShadowTameList1.lean:8:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Assembly.IsHypermapOfList`
ProbeShadowTameList1.lean:9:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Assembly.GoodGraphV4`
ProbeShadowTameList1.lean:10:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Assembly.the_kepler_conjecture_from_interfaces`
```

同一探针在主仓环境（`ProbeMain.lean`，不带影子 LEAN_PATH）全部可解析：

```console
$ lake env lean ... ProbeMain.lean
@Kepler.Assembly.HypermapIso : ...
Kepler.Assembly.IsHypermapOfList : ...
@Kepler.Assembly.oppositeHypermap : ...
Kepler.Assembly.GoodGraphV4 : Kepler.Graphs.Graph → Prop
Kepler.Assembly.the_kepler_conjecture_from_interfaces : Kepler.Assembly.TheKeplerConjecture
```

`ProbeShadow.lean`（import shadow TameList3）与 `ProbeShadowGoodGraph.lean` 同样：
低层件可见、4 个高层件 + e2e 根 unknown。

**全岛 ABI 兼容反证**（最强一条）：用主仓既有 olean 链（TameList72/57/69/TameOpposite1，
未重编）直接加载到影子 5 模块接口上——零 error：

```console
$ LEAN_PATH=/tmp/islanddec/build:$LEAN_PATH lean ... ProbeWholeIsland.lean
@Kepler.Text.TameSpine.RXOKSKC : ∀ {α} [DecidableEq α] (H : Hypermap α), H.IsRestricted → ∃ L, ...
@Kepler.Text.TameSpine.DANGEYJ : ∀ (L : fgraph ℕ) (hL : Kepler.Assembly.GoodList L) ...
@Kepler.Text.TameSpine.goodGraphV4Spine_witness : ... ∃ H', TameLp.IsHypermapOfListTl g.fgraph H'
ProbeWholeIsland.lean:9:8: error(lean.unknownIdentifier): Unknown identifier `Kepler.Assembly.HypermapIso`
```

⇒ 70 个下游岛模块的旧 olean 没有一个引用被改掉的 4 个高层声明；
接口替换对它们完全无感。

### 4.4 公理面（`#print axioms`，影子环境）

```console
$ LEAN_PATH=/tmp/islanddec/build:$LEAN_PATH lean ... ProbeAxioms.lean
'Kepler.Text.TameSpine.hypermapIso_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameSpine.hypermapIso_iff' depends on axioms: [propext, Quot.sound]
'Kepler.Text.TameSpine.isHypermapOfList_hypermapOfList' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameSpine.goodGraphV4Spine_implies' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameSpine.goodGraphV4Spine_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameSpine.RXOKSKC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameSpine.DANGEYJ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

零 sorryAx、零新公理。

---

## 5. E — 收益量化

### 5.1 Assembly 直接 import 岛（E1）

合法：岛闭包已无 `Kepler.Assembly`（§4.2），反向无环（`Kepler.Graphs` 闭包零 `Kepler.Text` 模块）。
值得接的前 10（按对 textCapstone 的贡献；textCapstone 是 hTC 三件里唯一吃岛的）：

1. `TameList69.RXOKSKC` — A9：受限 hypermap → 有限 list 表示 + `H.Iso`（jcajydu 的 witness 半）
2. `TameList69.goodList_L` / `goodListNodes_L` — `GoodGraphV4` 合取 1/2
3. `TameList69.iso_hypermapOfListG` — Iso witness 本体
4. `GoodGraph.GoodGraphV4Spine` — 六合取真形（A8 假设侧 / A9 结论侧）
5. `GoodGraph.goodGraphV4Spine_witness` — 把 (4)+(3) 打成 `∃H', IsHypermapOfListTl`
6. `Keystone.isHypermapOfList_hypermapOfList'` — P6-C 规格实例（Tl 形）
7. `TameList72.DANGEYJ` — `transform_assumption_v2` 单调性（W3/tameCorrespondence 上游）
8. `TameList72.SPLIT_NORMAL_LIST_CASES` — `split_normal_list` 覆盖内核
9. `TameList57.injOnListOfFaces` / `injOnListOfDarts` — list 同构单射（jcajydu 的 MAP/REVERSE 运输）
10. `TameList56.finalGraphFilter` / `sizeFlattenLe` — final/loop 过滤与长度界

（额外：`TameOpposite1.oppositeHypermap` 家族 = textCapstone 镜像分支的现成件；
`TameList17` 的 ntrans/rtrans/splitNormalList 机器 = W3 载体。）

### 5.2 jcajydu / tameCorrespondenceIso（E2）

- **jcajydu**：解开 import 后可用 `RXOKSKC` + `goodList_L/goodListNodes_L` +
  `IsHypermapOfListTl` 桥，覆盖 5 个存在合取中的 2–3 个（`∃H'` / `IsHypermapOfList` /
  `HypermapIso`）。但注意 **类型差**：`RXOKSKC` 的 L 是 `List (List (Set α))`、
  `hypermapOfListG` 的 dart 是 `Set α × Set α`；jcajydu 要 `g.fgraph : fgraph ℕ` 与
  `Hypermap (ℕ×ℕ)`，中间还需 α→ℕ 编码 + 图构造。`g/PlaneGraphs/GoodGraphV4` 仍依赖
  Reduction5（文档口径 1,500–3,000 行）。
  **本波直接节省 ≈ 100–200 行胶水**（witness + 桥）；Reduction5 主体不变。
- **tameCorrespondenceIso**：解锁 `DANGEYJ`/`SPLIT_NORMAL_LIST_CASES`/GoodGraph 桥/
  32k 行岛内 list-hypermap 机器。WMLNYMD.hl 本体 1,515 行 / 40+ 引理仍未移植
  （岛终点 = DANGEYJ.hl；下一章 PWSSRAT）。**可复用基础设施 ≈ 300–600 行当量**，
  主移植仍 ~1,000+ 行。

### 5.3 锥 / union / K_REACH（E3）

- **e2e 锥 / K_REACH**：±0。本波不造任何消费边；e2e 根 `Kepler/Final.lean` 仍直接
  import Assembly。
- **union**：根数 ±0（`Kepler.lean` 已 import `TameList72/TameList57/TameOpposite1`）。
- **默认目标 `Kepler.lean` 的模块可达面**：−3,466 个 Kepler 模块
  （4,364 → 898；Assembly 只经岛进入该根，`logs/universe_delta.py`）：
  ```console
  Kepler: current=4364 modules, Assembly=True, planned=898, Assembly=False
    Assembly leaves this root closure; delta = 3466 modules
  Kepler.Final: current=4230, planned=4230, Assembly=True   (e2e 根不变)
  ```
  这是**计量口径变化，不是战绩**：地图仪器若以 `Kepler.lean` 为根会看到 MODULES 骤降；
  若以 e2e 为根则逐位不动。必须在落库时写明，避免误读为"删了 3,466 个模块"。
- 岛自身闭包：TameList1 4,231 → 757（−3,474）；TameList72 4,302 → 828。

---

## 6. F — 风险与台账

### 6.1 隐含参数差异（HypermapIso vs Iso）

```
@Kepler.Assembly.HypermapIso : {α} → {β} → [DE α] → [DE β] → H → G → Prop
@Hypermap.Iso                : {α} → [DE α] → {β} → [DE β] → H → G → Prop
```

binder 顺序不同。**全应用**（`HypermapIso H G` / `Iso H G`）不受影响（`Iff.rfl` 已过）；
风险仅在 `@` 显式逐参应用或部分应用——岛内零此类用法（10 处全是全应用），
Assembly 侧也不改。

### 6.2 PackIneqDefA / textCapstone

**零影响**：本方案不搬任何声明、不改 `Assembly.lean` 一行、不重编 Assembly olean。
`goodGraphV4Spine_implies` 的证明体 `h` 原本就靠 defeq 通过（`Assembly.GoodGraphV4`
的六合取体与 Spine 逐字同体，SF-57/59/60/61/62 已真化）；改成 `GoodGraphV4Spine`
只是把隐式 defeq 显式化，Assembly 侧谓词与 `textCapstone` 消费点文本不变。

### 6.3 台账行号锚（需要/建议更新）

- `docs/axiom-ledger.md`：**零** TameSpine 行号引用 → 无需更新。
- `docs/statement-fix-proposals.md`：39 处 `GoodGraph.lean:N` 锚（38 行），全部 **+1**
  （GoodGraph.lean 插入 1 行 import）。集中行：2723, 2735, 2764, 2796, 2802, 2827,
  2858, 2859, 2860, 2867, 2917, 2939, 2963, 2990, 2994, 2998, 3006, 3053, 3061,
  3084, 3091, 3092, 3095, 3140, 3171, 3172, 3173, 3181, 3237, 3240, 3261, 3289,
  3294, 3308, 3323, 3324, 3331, 3332（另 :3179 `TameList3.lean:633` 不变）。
- `docs/priority-queue.md:49` `Keystone.lean:54`：行号不变（Keystone 净 0 行）。
- 源码注释里的行号锚：`Kepler/Assembly.lean:2167,2176,2203,2212,2217,2228`（`GoodGraph.lean:*` +1）；
  `Kepler/LP/LpVocabW6B.lean:93`（+1）；`TameSpine/TameList23.lean:72`、`TameList24.lean:29,31,45`
  （GoodGraph +1）；`TameList37.lean:66`、`TameList41.lean:38`、`TameList59.lean:65,397`、
  `TameList25.lean:12,26,94`、`TameList5.lean:36`（TameList1 +1）；
  `Kepler/Text/Reduction5Base.lean:14`（行号不变，但"TameList1:37 import Assembly"语义过时）。

### 6.4 其他风险

- **全岛重编未做**（AGENTS §3/§4 禁 `lake build`）：已用旧 olean 全链加载反证 ABI 兼容，
  但最终闸仍应由编排者对 75 文件做单发串行编译。
- **simp/instance 泄漏扫描（已定量）**：去 Assembly 后有 3,473 个模块离开岛闭包；
  对它们做全局效应扫描（`@[simp]` / `instance` / `attribute` / `notation` / `scoped` /
  `export`），实际会离开环境的全局生效声明只有 Dyadic 的 1 个实例 + 3 条 `@[simp]`
  （`Interval/Basic.lean:102,224`、`Interval/CertTM.lean:102,105`）；其余命中全是注释或
  文件局部 `attribute ... in`。tame/hypermap/graph 证明不可能消费它们 ⇒ 重编时
  simp 集与实例集的相关部分不变。另测：离开集合里 `syntax/macro/elab/notation3/infix`
  等语法扩展 = **0**；`Assembly.lean:74` 的 `attribute [-instance] dartDecEq3` 在去
  Assembly 后失效、`dartDecEq2/3`（均 `V3×V3`）重新生效——但岛内 75 文件 `V3` 出现次数 = **0**，
  该实例永远选不中。日志 `logs/global_effect_scan.log`。
- **`Kepler.Graphs` 体积**：闭包 629 模块，其中 627 来自 `TameClassification` 证书链。
  当前经 Assembly 本来就在闭包里，故无回归；若后续要瘦身可改窄 import（另立车道）。
- **`Kepler.Assembly.GoodListDefs` 仍带 Assembly 前缀**：满足工单判据（闭包不含
  `Kepler.Assembly` 模块），但若要求零 `Kepler.Assembly.*` 前缀，则需搬模块
  （26 个 importer，含 24 个 shard；属真 HOIST，本波不做）。

---

## 7. 主仓状态

```console
$ git -C /Users/zhangzhuo/repos/kepler-conjecture-lean4 status --short
(empty)
```

所有探针/编译产物只在 `/tmp/islanddec/`；交付快照在
`~/c17_backup/lane_snapshots/island-deassembly-scout/`。

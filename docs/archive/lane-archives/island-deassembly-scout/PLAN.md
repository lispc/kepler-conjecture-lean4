# PLAN — TameSpine 岛去 Assembly 化（侦察结论 + 施工方案）

基线：`31b7227e`（2026-11-06）；侦察期间 HEAD 前移到 `0abccb51`（仅 docs 变更，相关源文件零 diff）。主仓零改动；影子验证见 `EVIDENCE.md` / `logs/`。
判决表机器可读版：`DECL-VERDICTS.tsv`。

## 0. 一句话结论

**核心假设成立，而且比预想的更便宜：10 个 `Kepler.Assembly.*` 符号全部 `REDIRECT`
（0 HOIST / 0 KEEP-IMPORT），因为 9 个本来就声明在低层 `GoodListDefs`，4 个真高层
声明全都有低层孪生（2 个 `Iff.rfl`，1 个 rfl，1 个四槽重打包）。**
真正的成本不是搬声明，而是两处「隐藏供给」：`import Kepler.Assembly` 顺带供给了
`Kepler.Graphs` umbrella（必须补 import），以及 `Keystone`/`GoodGraph` 的 15 处
语句改写。首波 = **5 文件 / 157 行 diff / 净 +2 行**，影子 5/5 编译绿、
全岛旧 olean 链加载零 error、公理面标准三。

## 1. A — 判决分布

| 判决 | 数量 | 明细 |
|---|---:|---|
| REDIRECT | 10 | HypermapIso, nextEl, IsHypermapOfList, GoodListDefs(模块), listPairs, listOfDarts, GoodList, oppositeHypermap, eList, GoodGraphV4 |
| HOIST | 0 | — |
| KEEP-IMPORT | 0 | — |

关键证据：
- 岛内 `open Kepler.Assembly (...)` 的全部 9 个名字 = `GoodList/nextEl/listOfDarts/
  listPairs/fList/eList/prevEl/findFaceDarts/nList`，全部声明在
  `Kepler/Assembly/GoodListDefs.lean`（:34,:38,:44,:50,:55,:59,:62,:66,:72），
  与低层是**同一常量**（`ProbeLowOnly`：只 import GoodListDefs 即可 `#check`）。
- `HypermapIso ↔ Hypermap.Iso` 已由 `Keystone.lean:54` 的 `Iff.rfl` 编译证明；
  `GoodGraphV4Spine ↔ Assembly.GoodGraphV4` 的 `Iff.rfl` 双向通过
  （`ProbeEquiv`；`goodGraphV4Spine_implies := h` 本来就是 defeq 隐式通过）。
- `IsHypermapOfList` 与 `TameLp.IsHypermapOfListTl` 是**不同结构**（`Iff.rfl` 拒绝），
  但字段名/类型逐槽同体，四槽匿名构造器互转已有证明（`Keystone.lean:99-102`）。
- `oppositeHypermap` 岛内唯一「引用」是 `TameOpposite1.lean:62` 注释；:66 已有逐字
  孪生 def，`rfl` 级相等（`ProbeOpposite`）。

## 2. B — 爆炸半径

- HOIST 数为 0 ⇒ 无「第二个洞」。
- 反事实：4 个高层的依赖闭包都不触碰 `Contravening` / `textCapstone` / `FAN`；
  最深的 `GoodGraphV4` 只拖 5 个 helper + 2 个支撑 def，且全部可由
  `Graph + TameLp + GoodListDefs` 承载（岛内 `GoodGraph.lean:59-120` 已备逐字 Spine 镜像）。
- **真正搬不动的 = 0。**
- 唯一的「洞」在模块层：`import Kepler.Assembly` 同时供给 `Kepler.Graphs`；
  只换 `GoodListDefs` 会报 `Unknown constant Kepler.Graphs.Graph`（实测）。
  方案已在 `TameList1.lean` 与 `GoodGraph.lean` 各补 1 行 `import Kepler.Graphs`
  （闭包 629 模块、零 `Kepler.Text` 依赖、无环；当前经 Assembly 本来就在闭包内）。

## 3. C — 施工面

### C1 逐处清单（= `logs/island_deassembly.patch`）

| 文件 | 行 | 改动 |
|---|---|---|
| `TameList1.lean` | 37 → 37-38 | import 换 `Kepler.Assembly.GoodListDefs` + 新增 `Kepler.Graphs` |
| `TameList2.lean` | 63 | import 换 `GoodListDefs`（无净行） |
| `TameList3.lean` | 72 | 同上 |
| `Keystone.lean` | 36 | import 换 `GoodListDefs` |
| `Keystone.lean` | 54,58,63,67,74×2,81×2,82,88 | `Assembly.HypermapIso` → `Hypermap.Iso`（10 处） |
| `Keystone.lean` | 100,107,118,123 | `Assembly.IsHypermapOfList` → `TameLp.IsHypermapOfListTl`（4 处） |
| `GoodGraph.lean` | 43 → 43-44 | import 换 `GoodListDefs` + 新增 `Kepler.Graphs` |
| `GoodGraph.lean` | 129 | `Assembly.GoodGraphV4` → `GoodGraphV4Spine` |
| `GoodGraph.lean` | 146 | `Assembly.IsHypermapOfList` → `TameLp.IsHypermapOfListTl` |

下游 69 个岛文件的 `open Kepler.Assembly (...)` **零改动**。

### C2 语义等价

| 旧 → 新 | 等价强度 | 证据 |
|---|---|---|
| `Assembly.HypermapIso` → `Hypermap.Iso` | `Iff.rfl` | Keystone:54 已编译；`ProbeEquiv:9-10` |
| `Assembly.GoodGraphV4` → `GoodGraphV4Spine` | `Iff.rfl` 双向 | `ProbeEquiv:13` |
| `Assembly.IsHypermapOfList` → `TameLp.IsHypermapOfListTl` | 四槽重打包（非 rfl） | `ProbeEquiv:16-23`；Keystone:99-102 |
| `Assembly.oppositeHypermap` → `TameSpine.oppositeHypermap` | `rfl` 整体/逐投影 | `ProbeOpposite:9-16` |
| 9 个 `GoodListDefs` 名字 | 同一常量（不是副本） | `ProbeLowOnly` |

### C3 命名歧义

9 个裸名全仓唯一；`oppositeHypermap` 双份但不同 namespace、岛内从不共同 `open`。
`Hypermap.Iso` 用 qualified 形式，与 `Assembly.HypermapIso` 不撞名。**零歧义。**

## 4. D — 环的最终形态（已证）

- 静态：计划态 `TameList1/TameList3/GoodGraph/TameList72` 的 Kepler 闭包分别
  757/759/757/828 模块，`contains Kepler.Assembly = False`；75 个岛文件
  reaching Assembly 从 74 → **0**（`TameOpposite1` 本来就不 reach）。
- 动态反证：影子 `TameList1` 环境里 `#check @Kepler.Assembly.HypermapIso /
  IsHypermapOfList / oppositeHypermap / GoodGraphV4 /
  the_kepler_conjecture_from_interfaces` 全部 `unknown identifier`；
  同探针在主仓环境全部可解析（正/负对照齐）。
- 影子副本 ↔ 主仓：5 个字节副本 + patch；`build/` 是主仓 olean 符号链接农场，
  只重编这 5 个模块。既有 70 个下游 olean 直接加载到新接口上**零 error**
  （`ProbeWholeIsland`），证明没有任何下游模块引用被改掉的 4 个高层声明。
- 勘误：当前静态 import 图**不存在环**（Assembly/LocalConcl 闭包 ∩ TameSpine = 0）；
  准确形状是单向下坡边 `island → Assembly`。去 Assembly 化删掉这条边。

## 5. E — 收益

- **E1**：合法。岛闭包不含 `Kepler.Assembly`，`Assembly → island` 无环。前 10 资产见
  `EVIDENCE.md` §5.1（RXOKSKC / goodList_L / goodListNodes_L / iso_hypermapOfListG /
  GoodGraphV4Spine / goodGraphV4Spine_witness / isHypermapOfList_hypermapOfList' /
  DANGEYJ / SPLIT_NORMAL_LIST_CASES / injOnListOfFaces·OfDarts / finalGraphFilter）。
- **E2**：
  - `jcajydu`：解锁 A9/witness 半（2–3 个存在合取），直接节省 ≈100–200 行胶水；
    `g/PlaneGraphs/GoodGraphV4` 仍待 Reduction5（1,500–3,000 行），另有
    `List (List (Set α)) → fgraph ℕ` 的类型桥（转 reduction5-scout 关注）。
  - `tameCorrespondenceIso`：解锁 32k 行岛内 list/hypermap 机器与 DANGEYJ，
    可复用基础设施 ≈300–600 行当量；WMLNYMD 本体 1,515 行仍 ~1,000+ 行待移植。
- **E3**：e2e 锥 / K_REACH / union 根数 = **±0**（本波不造消费边）。
  仅计量口径变化：`Kepler.lean` 根的模块可达面 4,364 → 898（−3,466，Assembly 离场）；
  e2e 根 `Kepler/Final.lean` 4,230 → 4,230 逐位不动。落库说明必须写清，避免误读。

## 6. F — 施工方案与风险

### F1 三个子波

**W1（本波，去 Assembly 核心）**
- 改动面：5 文件 / 157 行 diff / 净 +2 行（patch 已备）。
- 编译顺序：`Keystone → GoodGraph → TameList1 → TameList2 → TameList3`。
- 验收（无新文件闸时的等价口径）：
  1. 5/5 单发 `lean -o` 零 error（影子已绿）；
  2. 影子 `TameList1/TameList3/GoodGraph` 探针：4 个高层件 + e2e 根 `unknown identifier`，
     低层 9 名 + `Hypermap.Iso` 可解析；
  3. `#print axioms` 7 个出口 = 标准三（影子已跑，零 sorryAx）；
  4. 静态闭包脚本 `contains Kepler.Assembly = False`；
  5. `git diff --stat` 恰好上述 5 文件；主仓其余零改动。
- 止损：全岛单发串行编译若出现任一 error（下游 70 文件级），**不拆补丁硬扛**；
  回退到「先只改 Keystone（S3/S1 桥），GoodGraph 单独一波」，并报告是哪一类名字漏网。

**W2（文档/锚点清理，零语义）**
- 改动面：`docs/statement-fix-proposals.md` 39 处 GoodGraph 行号锚 +1（38 行）；
  `Assembly.lean`/`LpVocabW6B.lean`/岛内注释 ~10 处 GoodGraph/TameList1 行号 +1；
  `Reduction5Base.lean:14` 措辞更新；可选：删掉现已空转的 `hypermapIso_iff` 等 5 个桥件
  （岛内零消费者；建议**保留**名字，降低外部引用风险）。
- 验收：`git diff` 只含注释/文档；无 `.lean` 语句变化（除可选删除）。
- 止损：`docs/statement-fix-proposals.md` 只改行号、不改章节结构（AGENTS §6：
  `auto_gate.sh:83` 按路径 + `^## N.` 切节）。

**W3（消费接线，独立裁决，不属于去 Assembly 化）**
- 改动面：在 `Assembly.lean` 或新 adapter 模块加 1–3 行 `import
  Kepler.Text.TameSpine.{TameList69, Keystone, GoodGraph}`，在 `jcajydu` 消费
  `RXOKSKC`/`goodGraphV4Spine_witness`。
- 验收：走 AGENTS §4 岛协议（standalone Assembly olean + `LEAN_PATH` 探针 +
  与基线根面逐字节比对 + olean 回灌）；`#print axioms the_kepler_conjecture_from_interfaces`
  与基线 628 逐项一致。
- 止损：公理面任一项变化 → 立即回退；类型桥（Set α → ℕ）未定前不写 `jcajydu` 本体。

### F2 风险清单

| 风险 | 评估 | 处置 |
|---|---|---|
| `HypermapIso` vs `Iso` 隐式参数顺序不同（`{α}{β}[DE α][DE β]` vs `{α}[DE α]{β}[DE β]`） | 全应用无影响（Iff.rfl 已过）；`@` 逐参/部分应用会错位 | 岛内 10 处全为全应用；W2 不加 `@` 用法 |
| `IsHypermapOfList` 非 `Iff.rfl`（不同结构） | 四槽重打包靠谱且已有证明 | 保留 Keystone 别名，不删 |
| `PackIneqDefA` / `textCapstone` 受声明搬家影响 | **零**：不搬声明、不改 Assembly 一行 | W3 才触 Assembly，且走独立闸 |
| 文档行号锚 | `docs/axiom-ledger.md` 零岛引用；`docs/statement-fix-proposals.md` 39 处 +1 | W2 统一刷新（清单见 EVIDENCE §6.3） |
| 隐藏供给 `Kepler.Graphs` | 不加则 GoodGraph/TameList2/3 直接 unknown（已实测） | W1 补 2 行 import |
| `Kepler.Graphs` 拖 627 个证书模块 | 当前经 Assembly 已在闭包内，无回归 | 后续可另立窄 import 波 |
| 全岛重编未做（禁 `lake build`） | 旧 olean 全链加载零 error = ABI 兼容；离开闭包的 3,473 模块全局效应扫描仅剩 Dyadic 1 实例 + 3 simp（与 tame 证明无关）；`dartDecEq2/3` 的 `-instance` 失效但岛内 `V3` 零出现；语法扩展 0 | 编排者终闸：75 文件单发串行编译 |
| `Kepler.Assembly.GoodListDefs` 仍带 Assembly 前缀 | 满足工单判据（模块不是 `Kepler.Assembly`） | 若要求零前缀，另立 26-importer 的模块搬迁波 |

### F3 判定

**GO** —— 首波 = 上述 5 文件 / 157 行 diff；影子编译 + 全岛 ABI + 公理面三证已过，
终闸只需编排者做一次全岛单发串行编译。

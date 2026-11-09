# 章程 · 链层参数化定义两件（`markedQ` / `SimpleHypermapTl`）

立案：2026-11-09。立案人：编排者。触发：j1w1 M0h2 的裁决提案（more_lemma2 线最后两个定义层缺口）。
上游章程：`docs/def-fix-charters/chain-list-defs/CHARTER.md`（同款"显式证明参数"口径）。

---

## 1. 对象与 HOL 锚

| Lean 目标 | 依据 | 形态 |
|---|---|---|
| `markedQ`（`l'q` 载体） | HOL `hyp'q` 回引 ↦ `Hypermap.hypQ`（`Hypermap.lean:10842`） | 显式证明参数（同 `hL` 口径） |
| `SimpleHypermapTl`（M0g 镜像） | `Assembly.lean:2075` 的 `SimpleHypermap`；`hypermap.hl:186` | **1 行 def 镜像** |

## 2. 机器核实（编排者 2026-11-09 独立验证）

- **`SimpleHypermap` 与 `Hypermap.Simple` defeq 成立**：`SimpleHypermap H = ∀ x ∈ H.darts, nodeOrbit H x ∩ faceOrbit H x = {x}`；`Simple H = ∀ x ∈ H.darts, H.node x ∩ H.face x = {x}`。其中 `H.node x = orbitMap H.nodeMap x`（`Hypermap.lean:843`，`orbitMap f x = {y | ∃ n, (f^n) x = y}`，`:708`），`nodeOrbit H x = orbitSet H.nodeMap x`（`Assembly.lean:2057`，`orbitSet p x = Set.range (fun n => (p^n) x)`，`:2053`）——`Set.range` 展开即同一集合式 ⇒ **defeq**（`face` 同理）。故镜像不需任何桥。
- **`Hypermap.hypQ` 已带证明参数**（`Hypermap.lean:10842`，`hypQ_spec` 给全规范）⇒ `markedQ` 可按同款显式参数落地，无需改 `Hypermap` 侧。

## 3. 裁定

**批准新增两件，均为纯定义（`Prop`/`ℕ` 载体），零定理改动、零既有文件触碰。**

1. `noncomputable def markedQ (L) (hL : GoodList L) (N) (r) (x) (hM : markedList L hL N r x) (hNF : ¬finalList L r) : ℕ := (hypermapOfList L hL).hypQ (loopFamily N) (loopOfList r) x ⟨…, …⟩`
   - 依赖面：链层 `loopFamilyOfList` / `loopOfList` Loop-族载体 + 三桥（`normalList → IsNormalFamily`、`markedList → IsMarked`、`¬final → ∉ finalLoops`），估 **100–150 行**，纯定义 + 桥、零定理；
   - 允许在 `markedQ` 上加辅助引理（`markedQ_spec` 等），但不得改变任何既有陈述。
2. `def SimpleHypermapTl (H : Hypermap α) : Prop := H.Simple`
   - 零桥零差异（§2 已核）。
   - 落地后 `simple_hypermap_uniq` 应为 **≈30–50 行**的 `all uniq L ↔ …` 组合件。

## 4. 禁止与闸门

- 禁止：import `Kepler.Assembly` 伞模块（`SimpleHypermap` 只作对照，不引用）；新增 `axiom`/`sorry`/`native_decide`；改任何既有陈述；在本项内证 more_lemma2 的其余欠账。
- 闸门：岛协议编译 RC=0；`#print axioms` 对附带的规范引理 ⊆ 标准三；`DF_SORRY_NET = 0`；pit10 零禁词。
- 回滚：`markedQ` 族与 `SimpleHypermapTl` 各自独立 commit。

## 5. 顺序

`markedQ`（M0h3 之后做，依赖 Loop 族载体）→ `SimpleHypermapTl` + `simple_hypermap_uniq`（最后一件，收 #33）。
两件落库后 **more_lemma2 线仅剩 J2 锁**（M0a 11 / M0f #37 / M2 / M1），正式封盘。

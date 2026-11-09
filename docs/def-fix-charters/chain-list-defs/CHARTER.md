# DEF-FIX 章程 · 链世界列表定义族（`normal_list` / `loop_list` / `flag_list` / `s_flag_list` / `find_list` / `marked_list`）

立案：2026-11-09。立案人：编排者。触发：j1w1 报 M0a 有 13 件以 `marked_list` 为载体、链世界无该定义族，保守停手（AGENTS §2）。

---

## 1. HOL 锚（全部在 `reference/flyspeck/text_formalization/tame/tame_defs2.hl`）

| Lean 目标名 | HOL | 说明 |
|---|---|---|
| `normalList` | `normal_list`（:93-100） | 5 合取块 |
| `loopList` | `loop_list` | 与 quotient/final 联动 |
| `flagList` / `sFlagList` | `flag_list` / `s_flag_list` | 双分支 |
| `findList` | `find_list` | `mktop` 形 |
| `markedList` | `marked_list`（:550） | **9 合取块**：全塔（AQ1–AQ13）的靶子 |

HOL `marked_list` 的 9 合取与本树 Spine 侧 `MarkedListSpine`（`TameList7.lean:499`）**只镜像前 7 个**（该文件头注已写明），第 8/9 个在 flag/s_flag 层。

## 2. 缺陷（双载体分叉，机器核实）

- 链世界（非 TameSpine）`def markedList` / `normalList` / `loopList` / `flagList` / `sFlagList` / `findList` **全部零命中**（`grep --include='*.lean' Kepler | grep -v TameSpine`）。
- Spine 侧有 `MarkedListSpine` 等，但绑定 `GoodList L` 的 BEq 实例与 `fgraph` 表示，**不能跨实例直接消费**（j1w1 与 j3def 两条车道独立确认）。
- 被卡住的线（三条）：
  1. **J3-D3b**：`assumptionSet3`/`assumptionSetK10` 的三载体参数化（已按"保守 + 可逆"落地，等本族实例化）；
  2. **M0a 剩余 13 件**（more_lemma2 前置）：4/6 导出 + 7/10 辅助以 `marked_list` 为载体；
  3. **more_lemma2 M1/M2**（J1-B7 前置）与 **J3 定理层 T8**（`betwn_disjoint` 邻域）。
- 现行 workaround（D3b 的 def 参数 + 实例化配方）可行但把问题推给每个调用点，且**不能支持需要 unfold 定义体的证明**。

## 3. 裁定

**批准新增链世界定义族（纯定义，零陈述改动）。** 六个定义逐字对齐 HOL 体，与 Spine 版同形但绑定链世界的 `fgraph`/列表表示；命名空间 `Kepler.Text.Reduction3`（或独立 `Kepler.Text.ChainLists`，实施时定）。

**明确不做的**：
- 不改任何既有定理陈述；
- 不删/改 Spine 侧同名族（双家保留，桥接定理按需另立）；
- 不新增 `axiom`/`sorry`/`native_decide`；`DF_SORRY_NET = 0`；
- 不在本项内做 `marked_list` 的 9 合取"真证"——本项只落**定义**，证明归 J3 定理层。

## 4. 实施与验收

- 分两步：**L1** = `normalList` + `loopList` + `findList`（M0a 13 件的直接载体）；**L2** = `flagList` + `sFlagList` + `markedList`（9 合取）。每步 ≤450 行。
- 每步验收：岛编译 RC=0；新增定义用 `#check` 打印签名比对 HOL 体；`#print axioms` 对"定义即引理"（若有）标准三；`DF_SORRY_NET = 0`；pit10 零禁词。
- **落库后立刻**：把 D3b 的三载体参数实例化（陈述零改，只填 `fun L N r x => …`），并解锁 M0a 剩余 13 件。
- 回滚：L1/L2 各自独立 commit。

## 5. 顺序位置

排在 M0e（37 岛件重落第一批，26 项，无定义依赖）**之后**、M0f 之前。理由：M0e 不依赖本族，先做不阻塞；L1 完成后 M0f 与 M0a 剩余件可并行。

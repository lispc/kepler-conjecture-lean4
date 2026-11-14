# DEF-FIX 章程：OCBICBY 收口汇点 `LocalAuto22Close`

> **状态：APPROVED（用户 2026-11-14，批「5t1批准」；待执行）**。拟案：2026-11-14，车道 `ocbicby5t1-w1`。
> 依据：AGENTS §2「定义改动只走 DEF-FIX 通道」+ `vas-cluster-move/README.md` 先例
> （用户 2026-11-12 裁决 ②a：纯搬运、陈述逐字节、零 sorry 增减）。
> **批准范围**：§3 的 4 条声明逐字节下移 + §4 的 4 条 `private` 关键字删除 + §5 的 import 边
> （新汇点模块 + LA16 增 1 行）；**不含**任何陈述/定义体/证明体改动；**Phase D 的收口证明另单**
> （普通证明车道，不再需要 DEF-FIX）。
> 字节核对脚本：`~/c17_backup/lane_snapshots/ocbicby5t1-w1/verify_move.py`（模拟搬运 22/22 PASS、3 负例全中）。

## 0. 一句话

LA22 体内 4 条 OCBICBY 收口声明（`terminal_pent_taum2_p22` / `empty_5T1_p22` / `empty_6T1_p22` /
`OCBICBY_p22`）**逐字节搬**到新汇点模块 `Kepler.Text.LocalAuto22Close`
（`import LocalAuto22 + LocalAuto19 + Mathlib`）；4 条生产引理（`empty5T1_vpwshto_p22` /
`empty5T1_pent_bridge_p22` / `empty6T1_setSum6` / `empty6T1_hex_bridge_p22`）**只删 `private`
关键字**（留在 LA22，陈述/证明逐字不动）；`LocalAuto16` 增 1 行 import。静态无环（§5）。

## 1. 要解决的问题（DAG 死锁，机器证据）

```
LocalAuto19.lean:82   import Kepler.Text.LocalAuto18
LocalAuto18.lean:112  import Kepler.Text.LocalAuto21
LocalAuto21.lean:107  import Kepler.Text.LocalAuto22
LocalAuto16.lean:106  import Kepler.Text.LocalAuto22
LocalAuto16.lean:437  OCBICBY_p22 h          （唯一代码消费者）
```

闭包实测（全树 `^import Kepler...` 解析）：

- `closure(LocalAuto22)` = 92 模块，**不含 LocalAuto19** ⇒ LA22 内直接写 `terminal_pent_taum2_p22`
  的证明（需 LA19 的 `terminal_pent_taum_p19`）会成环；
- `closure(LocalAuto19)` = 110 模块，**已含 LocalAuto22**、**不含 LocalAuto16**；
- `closure(LocalAuto16)` = 113 模块，含 LA22/LA21、不含 LA19。

⇒ 唯一合规出路：在 **LA22 下游、LA16 上游**插一个汇点模块，把「要消费 LA19」的收口声明搬过去。

## 2. 为什么是「下移 4 条声明」

| 方案 | 动作 | 问题 |
|---|---|---|
| D1 | LA22 直接 import LA19 | **成环**（LA19 闭包含 LA22） |
| D2 | 复制/上移 `terminal_pent_taum_p19` 到 LA22 可 import 的模块 | 复制=重复声明面；上移=动 LA19 塔族，面大 |
| D3 | 只搬 `terminal_pent_taum2_p22` | 不够：`OCBICBY_p22` 要消费 5T1/6T1 支产品，而支产品消费 `empty_5T1/6T1_p22`（又依赖 taum2）⇒ 仍成环 |
| **本方案** | 4 条收口声明整块下移 + 4 helper 放开可见性 | 搬运面 = 4 文本块 + 4 关键字 + 2 import 边；零证明体编辑 |

**机器事实**：4 条声明在 LA22 内零代码消费者（仅注释提及）；全树唯一代码消费者 = `LocalAuto16.lean:437`。

## 3. 搬运清单（4 条声明，逐字节；donor = 落地时 HEAD `c545d94e`，行号/md5 已核）

块定义：`/--` docstring 首行 → 下一顶层命令前一行（去尾部空行）。

| # | 声明 | donor 行（HEAD c545d94e） | 块 md5 | 状态 |
|---|---|---|---|---|
| 1 | `terminal_pent_taum2_p22` | 5198–5210 | `ac28e174988d404f53c441e315c16e88` | sorry（Phase D 补体） |
| 2 | `empty_5T1_p22` | 3053–3056 | `c367331a9bd8bd6c207ffcd994e010c5` | sorry（Phase D 补体） |
| 3 | `empty_6T1_p22` | 3048–3051 | `1f548ef5643c129e2dae6a9b9cd3397f` | sorry（Phase D / ht4nn 解冻） |
| 4 | `OCBICBY_p22` | 6762–6771 | `9298b0e0b2859c86fcc70bd7f38fe37f` | sorry（Phase D 总装配） |

Close 内相对顺序：`empty_6T1_p22` → `empty_5T1_p22` → `terminal_pent_taum2_p22` → `OCBICBY_p22`
（后声明依赖先声明，供 Phase D 直接补体）。

## 4. 可见性调整（4 条 `private` → 公开；只删关键字）

| 声明 | donor 行 | 删 `private ` 后整行 md5 |
|---|---|---|
| `empty5T1_vpwshto_p22` | 4274 | `4ebc5765dc181305d2b62ef0ffd64894` |
| `empty5T1_pent_bridge_p22` | 4347 | `303a2019ca636ce0c1cf69706af4d92c` |
| `empty6T1_setSum6` | 4648 | `79ac3d6a26159bdea2ce4f9b1d629893` |
| `empty6T1_hex_bridge_p22` | 4678 | `e9240441a4aa800112158ec166325d9e` |

理由：Phase D 的 `empty_5T1_p22`/`empty_6T1_p22` 证明体在 Close 内必须消费它们；`private`
跨模块不可见。**只删行首 `private `（10 字节）**，行内其余字节/陈述/证明体零改动。

## 5. 新模块与 import 边

新文件 `lean/Kepler/Text/LocalAuto22Close.lean`：`import Kepler.Text.LocalAuto22` +
`import Kepler.Text.LocalAuto19` + `import Mathlib`；`set_option maxHeartbeats 5000000`；
`namespace Kepler.Text`；`open Kepler.Geom Set Classical`。

| 边 | 类型 |
|---|---|
| `LocalAuto22Close → LocalAuto22` | 新 |
| `LocalAuto22Close → LocalAuto19` | 新 |
| `LocalAuto16 → LocalAuto22Close` | 新（import 块 `LocalAuto22` 行后） |
| `LocalAuto19 → LocalAuto18 → LocalAuto21 → LocalAuto22` | 既有，不动 |

**无环论证**：`closure(Close) = {Close} ∪ closure(LA22) ∪ closure(LA19)`；
`closure(LA22) ⊆ closure(LA19)` ⇒ `closure(Close) = closure(LA19) ∪ {Close}`（111 模块），
不含 `LocalAuto16`（实测）⇒ `LA16 → Close` 不闭圈。落地闸跑 Tarjan：
要求「无任何 >1 的 SCC 含 LA16/Close」。

## 6. 不变量（落地闸逐条核；`verify_move.py` 自动检查）

1. **块逐字节**：4 条声明 donor vs Close md5 相等（§3 表值）；LA22 内同名声明零命中。
2. **陈述行不变**：签名区（`theorem <name>` → 首个 `:= by` 行）md5 donor = Close。
3. **可见性面**：4 条 helper 行 = donor 行删 `private ` 前缀；其余 diff 零。
4. **sorry 零增减**：`LA22 + Close` 的 `^  sorry$` 之和 = donor LA22 计数（52）。
5. **零禁项**：Close 全文无 `axiom`/`admit`/`native_decide`；无新增 `sorry`（只有同字节搬家）。
6. **import 面**：Close 的 Kepler import 恰 2 条；LA16 只增 1 行且次序在 `LocalAuto22` 后。
7. **无环**：§5 闭包 + Tarjan SCC。
8. **根面**：`#print axioms Kepler.the_kepler_conjecture_e2e` md5 `246e952c…` 逐字节同
   （4 条声明不在锥内；搬运阶段 `OCBICBY_p22` 仍 sorry）。
9. **模块级编译**：Close / LA22 / LA16 三者 `nice -n 19` 单文件直编 RC=0 / error 0。

## 7. 落地验证计划（单车道，≤1 lean 并发）

1. worktree@落地 HEAD → 建 Close + 删 LA22 四块 + 4 关键字 + LA16 import+1。
2. `git show <donor>:lean/Kepler/Text/LocalAuto22.lean > /tmp/donor_LA22.lean`，跑
   `verify_move.py` → 全绿。
3. 直编 `LocalAuto22Close.lean`（RC=0/err0）→ `LocalAuto22.lean`（RC=0/err0；删块后无残留引用）
   → `LocalAuto16.lean`（RC=0/err0；新 import 解析）。
4. 探针 `OCBICBY_p22` 搬运阶段 = `[propext, sorryAx, Classical.choice, Quot.sound]`（body 仍 sorry）；
   Phase D 后才要求标准三。
5. 编排者闸：apply --check（a/lean b/lean）→ 直编三件 RC=0 → 根面 md5 → 一笔 commit。
6. 文档：本 charter 状态改 LANDED + `docs/priority-queue.md` §8 一条。

## 8. 风险与回滚

| 风险 | 级别 | 缓解 |
|---|---|---|
| Phase D 在 LA22 内补体 ⇒ 复现 LA19 环 | 高 | body 只能写在 Close；LA22 内该名已不存在（编译即挡） |
| `OCBICBY_5T1_p22`/`OCBICBY_6T1_p22` 支产品误放 LA22 | 中 | 消费 `empty_5T1/6T1_p22`（Close）⇒ 必须在 Close 或更下游 |
| `empty_6T1_p22` 的 Phase D 还缺 `ht4nn` 箱 | 高（内容） | 与搬运正交（LP 解冻项）；搬运后仍 sorry，不影响闸 |
| 4 条 helper 放开后与未来声明撞名 | 低 | `_p22` 尾缀 + 落地前 `rg` 唯一性 |
| 回滚 | — | 单 commit `git revert`：删 Close、恢复 4 条 `private`、删 LA16 import；LA22 四块原样恢复（md5 §3 可验） |

## 9. 用户裁决

- [x] **批准本纯搬运**（用户 2026-11-14，批「5t1批准」）：4 声明逐字节下移 + 4 条 `private`
  关键字删除 + 3 条 import 边；零陈述/零证明体改动。
- [ ] **LANDED**：执行车道 `ocbicby5t1-w1` Phase D1 按 §7 落地（待回填 commit/证据）。

## 附：与其它章程的关系

- 前置：`tauxkit-realify` / `enclosed4-anchor` 已 LANDED；本草案不触碰任何定义体。
- 后续：Phase D（`terminal_pent_taum2_p22` / `empty_5T1_p22` / `OCBICBY_5T1_p22` 的证明体）
  在 Close 内落笔，属普通证明车道，不再需要 DEF-FIX。
- 与 `vas-cluster-move` 同型（纯搬运下移 + import 汇点），diff 面更小（4 声明 vs 14 声明）。

# DELIVERY — tame-correspondence W1（`IsHypermapOfListTl` 规格收口）

- 车道 `tamecorr-w1`｜主仓 HEAD `873d2a2c`｜cwd `/tmp/tamecorr-w1/`
- 快照根 `$S = /Users/zhangzhuo/c17_backup/lane_snapshots/tamecorr-w1/`
- 新增文件（唯一仓内改动）：`lean/Kepler/Text/TameCorrBase.lean`（174 行，`git add -N` 已做）
- **施工口径（用户 2026-11-05 批）**：模块**只依赖 `Kepler.Text.TameLp`**，不 import `Kepler.Assembly`
  ——Assembly 层谓词搬运显式留给 W2（一行匿名构造器）。

## 0. 一句话结论

W1 的两个目标件（P6-C 桥 / `RXOKSKC`）在 HEAD 上都已存在且标准三；本波的实际增量是
**TameLp 侧的规格收口**（唯一性 / 典范性 / 求值律），并把 Assembly 层搬运降为 W2 的一行。
模块与 `Kepler.Interval.Cases.*` 的 shard 重建**完全解耦**（可验证、可落库）。

## 1. 逐件状态

| # | 件 | 状态 | 位置 / 证法一句 |
|---|---|---|---|
| W1-1 | `hypermapOfList_isHypermapOfListTl`（P6-C 规格实例，四槽组装） | **已在库，直接引用** | `TameLp.lean:6139`（本模块不重复） |
| W1-1b | 其 `∀ hL` arity 形 | **闭合**（本波） | `TameCorrBase.hypermapOfList_isHypermapOfListTl_arity`；`fun hL => 实例定理 L hL` |
| W1-2 | 四字段求值律 `darts_/edgeMap_/nodeMap_/faceMap_hypermapOfList` | **已在库，直接引用** | `TameLp.lean:5220/5225/5231/5238`（不重复） |
| W1-3 | 求值律 `Finset`/`List` 形：`darts_hypermapOfList_finset` / `mem_darts_hypermapOfList_iff` | **闭合** | `Finset.ext` + `Set.ext_iff` 逐点折算（`List.mem_toFinset`） |
| W1-4 | 规格解求值律：`isHypermapOfListTl_darts_finset` / `isHypermapOfListTl_mem_darts_iff` | **闭合** | 同上，只消费 `h.darts_eq` |
| W1-5 | **唯一性** `isHypermapOfListTl_unique` | **闭合** | dart 集由 `darts_eq` 钉死；三映射在 dart 上由 `*_eq`、dart 外由 `PermutesOn`（=恒等）钉死；`subst` 依赖消去后证明无关性 `rfl` 收 |
| W1-6 | **典范性**（核心增量）`isHypermapOfListTl_eq_hypermapOfList` / `isHypermapOfListTl_iff_eq_hypermapOfList` | **闭合** | 唯一性 + 规格实例定理 |
| W1-7 | 派生：`hypermapIso_of_isHypermapOfListTl` | **闭合** | 唯一性运输 + `Hypermap.Iso.refl` |
| W1-8 | Assembly 层 `IsHypermapOfList L (hypermapOfList L hL)` | **主动留给 W2** | 一行 `⟨h.darts_eq, h.edgeMap_eq, h.nodeMap_eq, h.faceMap_eq⟩`（Tl→Assembly），反向同形 |
| W1-9 | `RXOKSKC`（HOL 1,105 行） | **HEAD 上已闭合**（非本波产出） | `TameSpine/TameList69.lean:605`，标准三（`logs/probe2.log`） |

## 2. 验收证据

- **import 行原文**：`import Kepler.Text.TameLp`（文件第 46 行，全文件唯一 import；无 Mathlib 额外 import）。
- **编译**：standalone `lean Kepler/Text/TameCorrBase.lean` → **RC=0，0 error，0 warning**（`logs/build-TameCorrBase-tamelp.log`）。
- **sorry**：0（全文唯一命中的 "sorry" 在第 44 行头注的纪律声明里）。
- **公理面 8/8 = `[propext, Classical.choice, Quot.sound]`**（编译日志内联 `#print axioms`）：
  `hypermapOfList_isHypermapOfListTl_arity`、`darts_hypermapOfList_finset`、`mem_darts_hypermapOfList_iff`、
  `isHypermapOfListTl_darts_finset`、`isHypermapOfListTl_unique`、`isHypermapOfListTl_eq_hypermapOfList`、
  `isHypermapOfListTl_iff_eq_hypermapOfList`、`hypermapIso_of_isHypermapOfListTl`。
- **不碰 Assembly 的实证**：同一 `LEAN_PATH` 下 `import Kepler.Assembly` 的探针 **rc=1**，
  报 `Kepler/Interval/Cases/CQITNPEAx3725403817/Shard490.olean does not exist`（`logs/probe-asm2.log`）；
  当前 `Kepler/Interval/Cases/*.lean` 237 个源文件 vs **36 个 olean**。本模块 RC=0 ⇒ 依赖已彻底摘净。
- **补丁**：`kit-tamecorr-w1.diff` 180 行；`git apply --check --reverse` = OK；`HEAD:<path>` 不存在 ⇒ 纯新增。

## 3. 为什么这条路径不碰 Assembly（一句话）

`Kepler.Assembly` 是三万行脊柱且 `import Kepler.Interval.Cases.*`（23 个证书 shard），而本模块的
全部结论在 `TameLp.IsHypermapOfListTl` 上已可陈述，Assembly 层只差一次匿名构造器搬运（W2 在
Assembly 内部一行完成）——所以摘掉该 import 后**语义零损失、构建零 shard 依赖**。

## 4. 残件与精确缺口

**本波无残件**（`Kit-draft-tamecorr-w1.lean` 不适用：所有声明编译通过且标准三）。
真实缺口全在 W2：

| 缺口 | 精确内容 | 规模 |
|---|---|---|
| G1 **陈述差**（SF 级，需裁决） | `Assembly.jcajydu`（:2441）省略了 HOL `JCAJYDU` 的列表级前提；其 Lean 版 `Reduction5.restricted_hypermaps_are_planegraphs_thm` 全仓仅注释（`Assembly.lean:1969`）、无证明 | 裁决点 |
| G2 载体编码 | `RXOKSKC` 产出 `List (List (Set α))` → `Graph.fgraph : fgraph ℕ`；`la7_*` 只覆盖 `φ : ℕ → ℕ` | 150–300 行 |
| G3 图谓词 | `GoodGraphV4` 六合取项（`:2235`）+ `PlaneGraphs`；`GoodList`/`AllUniq`/`GoodListNodes` 已由 `RXOKSKC` 三槽直供 | 200–600 行 |

## 5. 下波 `jcajydu` 工单草案（W2）

0. **先裁决 G1**（两条路线见 RECON §Step 0.4）。
1. **谓词搬运（本模块的消费口，5 分钟）**：在 `Assembly.lean` 内部（不可 import 本模块，环）把
   `TameLp.IsHypermapOfListTl` 与 `Assembly.IsHypermapOfList` 用匿名构造器互转（各一行）；
   `jcajydu` 的 `∃ H', IsHypermapOfList g.fgraph H'` 见证取 `TameLp.hypermapOfList g.fgraph hL`
   （`hL` 来自 `GoodGraphV4.1`），四槽用 `TameLp.hypermapOfList_isHypermapOfListTl g.fgraph hL` 直接投影。
2. **见证替换用本模块的典范性**：两侧若都已满足同一 `L` 的规格，`isHypermapOfListTl_unique`
   把 `Iso` 义务降为 `refl`；TameLp 侧可直接引 `TameCorrBase.isHypermapOfListTl_iff_eq_hypermapOfList`。
3. **`is_restricted` 运输已就位**：`TameSpine.isoRestrictedIff`（TameList15:655）、
   `TameSpine.isoListRestricted`（TameList19:331），无需新证。
4. **G2 / G3** 见上表；建议 G2 单独一小波（可与 shard 重建并行，因其同样不必 import Assembly）。
5. **规模**：G1(a) 路线 ≈ 300–800 行/1–2 波；G1(b) 路线 ≈ 1,500–3,000 行，须另立 reduction5 侦察波。
6. **红线**：W2 必动 `Assembly.lean` ⇒ 陈述冻结审计 + 改前/改后全链 `#print axioms` 对比。

## 6. 归档（交编排者落库时执行）

`docs/archive/lane-archives/tamecorr-w1/` ← 从 `$S` 复制：`kit-tamecorr-w1.diff`、`DELIVERY.md`、`Evidence.md`。
本波未在仓内创建该目录（硬约束：仓内零未跟踪文件）。仓内唯一改动 = `lean/Kepler/Text/TameCorrBase.lean`。

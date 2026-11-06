# WORK ORDER — `pa22-10-chain`（用户已批：`#10 EXISTS_M_POLYHEDRON` 走路线 (a) 全做）

> 状态：**用户 2026-11-06 已批准**（"1.(a)"）。这是本 session 最重要的一项。
> 前置必读：`docs/handoff-2026-11-06.md` §5 红旗清单、`docs/archive/lane-archives/pa22-face-scout/VERDICT.md`。

## 0. 为什么这项特殊

`#10` 现在**陈述为假**，根因是 `PackingAuto22.lean:357`：

```lean
def weaklySaturatedP22 (V : Set V3) (r c : ℝ) : Prop := True
```

而 `#10`（`:14401`）把它当假设 `hws : weaklySaturatedP22 V r (2 * h0)` ⇒ 假设空洞
⇒ 反例（过原点平面上的正六边形）下 `P` 含整条 z 轴、`IsBounded` 假。

**改这个 def 会连带把两条"已证"定理变成待证**（见 §2），这是本波最危险的地方，不要试图绕过。

## 1. W1：DEF-FIX（2 行，但要看环）

真身**已在树里**：`lean/Kepler/Text/PackingAuto3.lean:35`

```lean
def weakly_saturated (V : Set V3) (r r' : ℝ) : Prop :=
  ∀ v : V3, 2 ≤ dist (0 : V3) v → dist (0 : V3) v ≤ r' →
    ∃ u : V3, u ∈ V ∧ u ≠ 0 ∧ dist u v < r
```

`PackingAuto3.olean` 存在（7.8 MB）、该文件零 sorry。两条落地路线：

- **(i) 别名**：PA22 顶部加 `import Kepler.Text.PackingAuto3`，然后
  `def weaklySaturatedP22 (V) (r c) : Prop := weakly_saturated V r c`。
  **先查环**：`PackingAuto3` 只 import `Polytope` / `Statement` / `Mathlib`；若 `Statement`
  反向 import PA22 就会成环，那时走 (ii)。
- **(ii) 逐字抄体**：把上面那段 body 原样抄进 PA22 的 def（无 import）。**保留名字
  `weaklySaturatedP22` 与参数名**，只换 body。这是最保守的路线。

**验收**：`lake env lean -o` 编译 PA22 ⇒ 0 error；`#print axioms` 对任何件不新增。

## 2. W2：真 `weak_saturation`（HOL `counting_spheres.hl:1527`，标 GIANT）

现状（`PA22:6884`）是**假绿**：

```lean
theorem weak_saturation ... :
    ∃ V, ... ∧ weaklySaturatedP22 V r (2 * h0) ∧ ...
  exact ⟨W, hW, hP, trivial, fat_lemma1 W hP hW, le_refl W, hsep⟩
                              ↑ 填的就是 True
```

DEF-FIX 之后这条会**编不过**（`trivial` 不再能填）。必须给真构造：把 `W` 扩成
`W ∪ {需要补的点}` 使其满足 `∀ v, 2 ≤ ‖v‖ ≤ 2h0 → ∃ u ∈ V, u ≠ 0, dist u v < r`。

- 先读 HOL 的 `counting_spheres.hl:1527` 证明脚本，照抄思路（别自己发明）。
- **允许分件**：先证「有限步扩张」（一步加一点、半径不增），再证「终止/有限」，
  最后装配。每件独立 `#print axioms`。
- 若真做不动 ⇒ **止损并量化**：写清卡在哪一步、缺哪条引理、估还差多少行。
  **禁止**改 `weak_saturation` 的陈述（用户批准的是 DEF-FIX，不是改这个定理）。

## 3. W3：`SATURATE_BALL_ANNULUS` 复核

`PA22:15791` 消费 W2。W2 真证后它应自然通过；若不过（因为它自己也可能用了桩），一并修。

## 4. W4：`#10` 本体（300–450 行）

`PA22:14401`。侦察已勘明它需要：
- `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT`（**已在树** `Polytope.lean:1846`，`a := id` 直接消费）
- 6 条前置里已证 3 条：`polyhedron_sum_sum_edge` / `POLYHEDRON_TGJISOK` / `BIJ_FACET_HYPERFACE`
- `FACET_OF_POLYHEDRON_EXPLICIT_ALT`（`PA22:14236`，已证）
- 现在再加上真 `weak_saturation` 提供的饱和性

装配时**陈述不动**（陈述本身不用改——改的是 def 的语义）。

## 5. 硬纪律

- 主仓 tracked 零改动（由编排者落库）；`/tmp/p22w10/` 工作；产物 → `~/c17_backup/lane_snapshots/pa22-10-chain/`。
- 只跑独立 `nice -n 19 lake env lean <单文件>`；并发 ≤3；禁 `lake build`/`auto_gate.sh`/`git commit`。
- 禁 `axiom`/`sorry`/`admit`/`native_decide`；**不许新增 sorry**（唯一例外：W1 的 DEF-FIX 会让
  2 条定理退回，那是**已知且要还的**，不是新增）。
- PA22 单次编译 ~110 s；优先在新模块里开发中间引理，最后再动 PA22。

## 6. 交付

`~/c17_backup/lane_snapshots/pa22-10-chain/{*.lean,patch.diff,DELIVERY.md,Evidence.md,logs/}`。
回我 ≤18 行：W1 走了 (i) 还是 (ii) 及是否有环、W2 的构造与行数、`weak_saturation`/`SATURATE_BALL_ANNULUS`
/`#10` 三件的 axioms、PA22 的 sorry 计数变化（预期 W1 后暂时 5→7，W2/W3 后回 5）、RC/墙钟。

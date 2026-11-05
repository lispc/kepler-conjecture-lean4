# DELIVERY — lane `p21-anchor-defix-w1`（DEF-FIX：LA21/LA18 终端锚点重编码）

- 任务：用户 2026-11-06 批准的 R-fix——把 `LocalAuto21.lean` 的
  `mainNonlinearTerminalV11_p21` 与 `LocalAuto18.lean` 的
  `mainNonlinearTerminalV11_p18` 从可反驳的 `∀ y : Fin 6 → ℝ, box y` 改为
  HOL `terminal.hl:37` 的忠实渲染 `main_nonlinear_terminal_v11`
  （`LocalAuto1.lean:2139` 的 109 条 registry 合取）。
- 仓库 `/Users/zhangzhuo/repos/kepler-conjecture-lean4`；车道发车 HEAD
  `873d2a2c`（车道期间其它车道推进到 `47766955`；两目标文件在区间内未变，
  见 `Evidence.md` §0）。
- cwd `/tmp/p21-anchor-defix-w1/`；产物
  `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/p21-anchor-defix-w1/`。
- 纪律：无 `lake` 子命令；未写 `lean/.lake/`；编译仅 standalone `lean` +
  规定 `LEAN_PATH`；探针串行。

## 0. 一行结果

**两行定义改动成立**：`mainNonlinearTerminalV11_p21 := main_nonlinear_terminal_v11`
与 `mainNonlinearTerminalV11_p18 := main_nonlinear_terminal_v11`；盒谓词
`MainNonlinearTerminalV11_p21/_p18` 原样保留。**破坏面 = 0**：28 个假设类型
改变的签名中，24 个体为 `sorry`（`h` 未用）、4 个已证消费者仅原样转发 `h`；
**零处从盒谓词取约束，零处需要改陈述**。`LocalAuto18/19/21/LocalConcl` 全部
RC=0、零 error，净 sorry = 0。三份 DEF-FIX 章程就位，围栏与 `git diff`
逐字一致。

| 项目 | 结果 |
|---|---|
| 定义改动 | 2 文件 / 2 行语义（+ 2 处 docstring 说明） |
| `git apply --check`（干净 HEAD） | RC=0 |
| `git apply --reverse --check`（当前树） | RC=0 |
| `LocalAuto18` | RC=0，0 error，sorry 11→11 |
| `LocalAuto19` | RC=0，0 error，sorry 29→29 |
| `LocalAuto21` | RC=0，0 error，sorry 29→29 |
| `LocalConcl` | RC=0，0 error，sorry 23 |
| 旧 `not_p21_anchor` 探针 | 改前 RC=0（标准三 axioms）；改后 RC=1（type mismatch） |
| `#print` 两锚 | 均显示 `:= main_nonlinear_terminal_v11` |
| 章程 | `docs/def-fix-charters/p21-anchor/{README,gate-LocalAuto18,gate-LocalAuto21}.md` |
| 闸门规则 1–3 模拟 | 两文件均 `GATE-SIM-PASS`（正式规则 4/4b/5 留给编排者） |
| 净 sorry | 0（diff 中 `sorry`/`admit`/`native_decide` 增删行 = 0） |

## 1. 改动

```lean
-- lean/Kepler/Text/LocalAuto21.lean（def 行 140 → 143）
def mainNonlinearTerminalV11_p21 : Prop := main_nonlinear_terminal_v11

-- lean/Kepler/Text/LocalAuto18.lean（def 行 206 → 212）
def mainNonlinearTerminalV11_p18 : Prop := main_nonlinear_terminal_v11
```

- 同步更新两文件的 ENCODING NOTES 与锚点 docstring（指向本 DEF-FIX 章程）；
  不改任何 theorem 陈述，不新增/删除 `sorry`。
- 零新 import（两文件均已 `import Kepler.Text.LocalAuto1`）。
- 完整 patch：`kit-p21-anchor-defix-w1.diff`（含两 lean 文件 + 三章程，
  5 个 `diff --git` 块；forward/reverse check 均 RC=0）。

## 2. 破坏面结论（详见 `BREAKAGE.md`）

- 代码引用 28 处：LA18 2、LA19 23、LA21 3；另有 `LocalConcl.p21_anchor`
  1 处 `sorry` 定义 + 2 处消费（4746/4779）。
- **0 硬 breakage**。所有消费者二选一：
  - 体 `sorry`，`h` 完全未用（24 个签名）；
  - 已证，仅把 `h` 原样转交下游同型假设（`CUXVZOZ_p21`、`CJBDXXN_p21`；
    LA19 `terminal_hex_126/135_reduction_p19` 在 body 内转交
    `terminal_hex_234_reduction_p19`）。
- 检索 `h (fun` / `h ⟨` / `h y` / `h.1` / `h.2` / `unfold mainNonlinear…` /
  `simp [mainNonlinear…]`：0 命中；盒谓词（大写 M）除定义外无消费者。
- 下游解锁（留给后续车道，本波不改白名单外文件）：`LocalConcl.p21_anchor`
  与 `LocalConcl.mnt11_anchor` 现在同型，`p21_anchor := mnt11_anchor`
  可再省 1 个 sorry。
- 文档债：`LocalConcl.lean:1990-1993` 的 `p21_anchor` docstring 仍描述旧语义
  （`∀ y : Fin 6 → ℝ`、no bridge）；`LocalConcl` 在本车道白名单外，未改。

## 3. 闸门命令

```sh
cd lean
GATE_MODE=DEF-FIX DF_PATCH=docs/def-fix-charters/p21-anchor/gate-LocalAuto18.md \
  DF_ANCHORS="terminal.hl:37" DF_NAMES="mainNonlinearTerminalV11_p18" DF_SORRY_NET=0 \
  LANE_FILES="Kepler/Text/LocalAuto16.lean,Kepler/Text/LocalAuto26.lean,Kepler/Text/LocalAuto18.lean,Kepler/Text/LocalAuto21.lean" \
  bash scripts/auto_gate.sh Kepler/Text/LocalAuto18.lean mainNonlinearTerminalV11_p18

GATE_MODE=DEF-FIX DF_PATCH=docs/def-fix-charters/p21-anchor/gate-LocalAuto21.md \
  DF_ANCHORS="terminal.hl:37" DF_NAMES="mainNonlinearTerminalV11_p21" DF_SORRY_NET=0 \
  LANE_FILES="Kepler/Text/LocalAuto16.lean,Kepler/Text/LocalAuto26.lean,Kepler/Text/LocalAuto18.lean,Kepler/Text/LocalAuto21.lean" \
  bash scripts/auto_gate.sh Kepler/Text/LocalAuto21.lean mainNonlinearTerminalV11_p21
```

注意：`auto_gate.sh` 规则 1 要求除 `$FILE` 外的 tracked 脏文件全部列进
`LANE_FILES`；本车道交付时另一车道仍持有 `Kepler/Text/TameCorrBase.lean`
（staged A）与若干 docs/archive 改动，编排者按当轮实际脏文件补齐
`LANE_FILES`/`outside` 即可。三份章程的 §2.1 围栏已按 `git diff` 的
`-`/`+` 行逐字核对（LA18 4/10、LA21 6/9，无缺无余）。

## 4. 回退

- 单一 patch：`git apply -R kit-p21-anchor-defix-w1.diff`（已用
  `--reverse --check` 在当前树验证 RC=0）；或提交后 `git revert <commit>`。
- 回退后旧 `∀ y` 编码恢复，`not_p21_anchor` 探针也会恢复可证（预期待定，
  说明回退生效）。

## 5. 预算与产物

- 预算：约 55 次工具调用 / 墙钟约 1.3 h（13:46–14:06 CST），低于
  ≤100 调用 / ≤2.5 h。中途未触发简报阈值前的任务变更；无阻塞。
- `$S/` 产物：
  - `kit-p21-anchor-defix-w1.diff`
  - `BREAKAGE.md`
  - `DELIVERY.md`（本文件）
  - `Evidence.md`
  - `logs/`（base / fresh / post 编译日志、三份探针日志、`#print` 日志）
- 入库归档：`docs/archive/lane-archives/p21-anchor-defix-w1/`（kit +
  DELIVERY.md + Evidence.md + BREAKAGE.md + logs/）。

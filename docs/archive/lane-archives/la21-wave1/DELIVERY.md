# DELIVERY — la21-wave1

- 车道: `la21-wave1`；工作目录 `/tmp/la21-wave1/`
- 主仓 HEAD（发车）: `a509e470cc7ff617e8caa38fa3297823f5bb551f`（实测 2026-11-05）
- 收尾时 HEAD 已前进到 `19a6cf9007464b4d85718ce10667f326e6f785bb`；但
  `lean/Kepler/Text/LocalAuto21.lean` 在 `a509e470` 与 `19a6cf90` 的 blob 相同
  （`a1eac7050c5e64a27afaeff9f785c92a1ae3efbf`），patch 基线不变，
  `git apply --check` 在当前 worktree 仍 PASS（见 `logs/patch-check.log`）。
- 目标文件: `lean/Kepler/Text/LocalAuto21.lean`
- 主仓 tracked 文件零改动（收尾 `git status --short` 为空）

## 0. 总览

| 件 | 声明 | 状态 | 说明 |
|---|---|---|---|
| W1-A | `azim_dominated_split_p21` | **CLOSED** | 真证；`#print axioms` = standard three |
| W1-B | `tau3_azim_p21` | **CLOSED** | 真证；`#print axioms` = standard three |
| W1-C | `tau3_taum_nonplanar_p21` | **UNRESOLVED（未动证明，按工单）**；**非 BLOCKED** | 工单前提有误：桥 `DIHV_EQ_DIH_Y_4PT_B` 已在 LA21 闭包内，且 standard three；可行性 probe 已编译通过（RC=0），但按工单“只做侦察，不要动证明”未写入文件 |

- own-sorry：**29 → 27**（净减 2，恰好等于两件真证；删除面只含这两个 `sorry`）
- patch：`patch.diff` 相对 `a509e470`，`git apply --check` **PASS**；`78 insertions(+), 10 deletions(-)`
- 整编：`nice -n 19 lake env lean /tmp/la21-wave1/LocalAuto21.lean`（与交付文件 sha256 相同）
  **RC=0 / 0 error**；warning **27**（基线 29；全部为剩余 `declaration uses sorry`）
- 未触碰 `mainNonlinearTerminalV11_p21` 的 R-fix 重编码区域（`:131-150`）

## 1. W1-A `azim_dominated_split_p21` — CLOSED

- 位置：`LocalAuto21.lean:668`（证明体 `:675-684`）
- 证明结构：`sum3_azim_fan`（`TopologyFan.lean:1137`）用在带撇点上
  （`x:=v0'`, `v:=v1'`, `u:=v2'`, `w1:=v3'`, `w2:=v4'`）：
  - `hxv : v1' ≠ v0'`：反证，`{v0',v1',v3'}` 退化为 `{v0',v3'}`，与 `h1` 矛盾（`collinear_pair`）。
  - 三条 `¬ Collinear3`：`h3/h1/h2` 直接给（`Collinear3` 是 `Geom/Azim.lean:43` 的 rfl 级 def）。
  - `hlt`：`hd1 + hd2` 后用 `hsplit` 得 `≤ azim v0 v1 v2 v4`，再 `azim_lt_two_pi`。
  - 结论用 `.symm` 对齐陈述方向。
- axiom 面（实测，shadow olean）：
  `'Kepler.Text.azim_dominated_split_p21' depends on axioms: [propext, Classical.choice, Quot.sound]`

## 2. W1-B `tau3_azim_p21` — CLOSED

- 位置：`LocalAuto21.lean:1214`；两件 private helper 在同文件 `:1178` / `:1206`
  （`collinear3_coplanar4`、`collinear3_swap23`；LuneVolume 的同名件是 private，不可 import，此处重证）。
- 证明结构：
  - 由 `hnc : ¬ Coplanar {0,v0,v1,v2}` 反推 6 条 `¬ Collinear3`（helper + 置换）。
  - 槽 1 的 `azim ≤ π` 由 `haz`；槽 2/3 由 `FSQKWKK_p16`（`XivphksKit.lean:346`）两次转圈：
    `azim 0 v1 v2 v0 ≤ π`、`azim 0 v2 v0 v1 ≤ π`。
  - 三槽逐一 `AZIM_DIHV_SAME_STRONG`（`LocalAuto7.lean:588`，取 `.symm`）改写 `dihV → azim`，
    `unfold tau3` 后 `rw` 收口。
- axiom 面（实测）：
  `'Kepler.Text.tau3_azim_p21' depends on axioms: [propext, Classical.choice, Quot.sound]`

## 3. W1-C `tau3_taum_nonplanar_p21` — 侦察裁决（勘误，非 BLOCKED）

**工单前提与实测冲突（以机器证据为准，AGENTS.md §7）：**

1. `LocalAuto38Bridge` **在** LA21 闭包内，无需新增 import 边。实测路径：
   `LocalAuto21 → LocalAuto11:117 → LocalAuto2:82 → PackingAuto20:58 → LocalAuto38Bridge`。
   单独 `import Kepler.Text.LocalAuto21` 下 `#check Kepler.Text.DIHV_EQ_DIH_Y_4PT_B` 成功。
2. `DIHV_EQ_DIH_Y_4PT_B`（`LocalAuto38Bridge.lean:600`）axioms = **standard three**（无 `sorryAx`）。
3. `DIHV_EQ_DIH_Y_4PT`（`LocalAuto38.lean:1440`）不在闭包内（`LocalAuto38` 是 OUT），axioms 也是 standard three。
4. 闭包内另有 `azim_dih_y_p18`（`LocalAuto18.lean:1381`，经 LA16:109 → LA33:158 可达），
   但其 axioms 含 **`sorryAx`**，不可用作桥。
5. 闭包外同款桥 `ea2_dihV_eq_dih_y`（`EulerSimplexGeom.lean:1034`）axioms = standard three，
   与 LA21 co-import 无冲突，但为 OUT；闭包同为 37 模块，远轻于 `LocalAuto38`（92 模块）。

**裁决**：W1-C **不是 BLOCKED**；按工单不动其证明（文件里保持 `sorry` 原样，axioms 仍含 `sorryAx`）。
可行性 probe `logs/probe_w1c.lean` 用 `DIHV_EQ_DIH_Y_4PT_B` + `taum_dih_y_p16`
（`LocalAuto16.lean:1107`，standard three）+ 同款 helper，**RC=0** 编译通过；
下一车道可直接搬入（约 30 行），不需要任何新 import。

## 4. 用到的前置 axioms 实测（全部 standard three）

| 前置 | 位置 | axioms |
|---|---|---|
| `sum3_azim_fan` | `TopologyFan.lean:1137` | `[propext, Classical.choice, Quot.sound]` |
| `AZIM_DIHV_SAME_STRONG` | `LocalAuto7.lean:588` | 同左 |
| `FSQKWKK_p16` | `XivphksKit.lean:346` | 同左 |
| `taum_dih_y_p16` | `LocalAuto16.lean:1107` | 同左（W1-C recon 用） |
| `DIHV_EQ_DIH_Y_4PT_B` | `LocalAuto38Bridge.lean:600` | 同左（W1-C recon 用） |
| `DIHV_EQ_DIH_Y_4PT` | `LocalAuto38.lean:1440` | 同左（OUT of closure） |
| `ea2_dihV_eq_dih_y` | `EulerSimplexGeom.lean:1034` | 同左（OUT of closure） |
| `azim_lt_two_pi` | `Geom/Azim.lean:956` | 同左 |
| `azim_nonneg` | `Geom/Azim.lean:947` | 同左 |
| `collinear3_iff_smul` | `Geom/Azim.lean:86` | 同左 |
| `coplanar_triple` | `Geom/Coplanar.lean:45` | 同左 |
| `collinear_pair` | Mathlib | 同左 |
| `mem_affineSpan_pair_iff_exists_lineMap_eq` | Mathlib | 同左 |
| `affineSpan_mono` | Mathlib | `[propext, Quot.sound]` |
| `mem_affineSpan` | Mathlib | `[propext, Quot.sound]` |
| `azim_dih_y_p18` | `LocalAuto18.lean:1381` | **`[propext, sorryAx, Classical.choice, Quot.sound]`（不可用）** |

## 5. 验收对照

1. 整编：RC=0、0 error；warning 27 ≤ 基线 29 — `logs/baseline-compile.log`、`logs/final-compile.log`
2. `#print axioms`：两件均 standard three，零 `sorryAx` — `logs/axioms.log`
3. own-sorry 29 → 27；`git diff` 删除面 = 2 条 `sorry` + 对应 DISCHARGES 注释 + 1 行 FILE MAP 状态字 — `patch.diff`
4. `git apply --check`（基于 `a509e470`）PASS
5. 未触碰 `:131-150` R-fix 区域（diff 无该区域）

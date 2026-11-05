# DELIVERY-w1c — la21-wave1（续 W1-C）

- 车道: `la21-wave1`；工作目录 `/tmp/la21-wave1-w1c/`
- 基线: **`5ccd6212`**（归档提交；`lean/Kepler/Text/LocalAuto21.lean` blob
  `f09b2fa6679fe0d5684605f25b401e5f592eb81b`，与当前 HEAD `91972db0` 该文件 blob 相同）
- 目标: `lean/Kepler/Text/LocalAuto21.lean` 的 **仅一件** `tau3_taum_nonplanar_p21`
- 主仓 tracked 零改动（收尾 `git status --short` 为空）

## 1. 结论

| 件 | 状态 | axiom 面（实测） |
|---|---|---|
| W1-C `tau3_taum_nonplanar_p21` | **CLOSED** | `[propext, Classical.choice, Quot.sound]` |

- own-sorry：**27 → 26**（净减 1，恰好本件；无其他 `sorry` 被删）
- 整编：**0 error / RC=0**；warning **26**（全部为剩余 `declaration uses sorry`）
- `patch-w1c.diff`：**54 insertions(+), 6 deletions(-)**；
  基于 `5ccd6212` 的 `git apply --check` **PASS**，应用后与交付文件 sha256 一致

## 2. 证明结构（`LocalAuto21.lean:1165`）

本件在文件中位于 W1-B 的两个 private helper（`:1178`/`:1206`）之前，Lean 不允许前向引用，
因此把必要的两条退化/置换引理作为 **proof-local `have`**（`hcopl`、`hswap`）内联，
不新增顶层声明、不移动/修改 W1-B 的落地内容。

证明链：

1. `hcopl : Collinear3 z w w1 → Coplanar {z,w,w1,w2}`（局部版；`collinear3_iff_smul` + `affineSpan`）。
2. `hswap : Collinear3 a b c → Collinear3 a c b`。
3. 由 `hnc : ¬ Coplanar {0,v0,v1,v2}` 反推 6 条 `¬ Collinear3`
   （`0v0v1`、`0v0v2`、`0v1v2`、`0v1v0`、`0v2v0`、`0v2v1`）。
4. `rw [taum_dih_y_p16 ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1)]`
   （`LocalAuto16.lean:1107`）。
5. `unfold tau3`，三槽 `DIHV_EQ_DIH_Y_4PT_B`（`LocalAuto38Bridge.lean:600`，闭包内，标准三）改写。
6. `simp only [dist_comm, dist_zero_right]` 对齐 `dist 0 vᵢ = ‖vᵢ‖`，`rfl` 收口。

**未使用** `azim_dih_y_p18`（含 `sorryAx`）；**未新增任何 import 边**。

## 3. 前置 axioms 实测（`logs/axioms-w1c.log`）

```
'Kepler.Text.tau3_taum_nonplanar_p21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DIHV_EQ_DIH_Y_4PT_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.taum_dih_y_p16' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.tau3_azim_p21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.collinear3_iff_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.coplanar_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'collinear_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'mem_affineSpan_pair_iff_exists_lineMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'affineSpan_mono' depends on axioms: [propext, Quot.sound]
'mem_affineSpan' depends on axioms: [propext, Quot.sound]
RC=0
```

## 4. 删除面

`patch-w1c.diff` 的 6 行删除，全部属于本件：

```
-  -- DISCHARGES: HOL Nonlinear_lemma.taum_123, Sphere.rhazim/rhazim2/rhazim3,
-  -- node2_y/node3_y, sol0_const1 and Merge_ineq.DIHV_EQ_DIH_Y (dihV = dih_y
-  -- off the coplanar locus); the dih_y bridge is not on this side.
-  -- NEEDS: the DIHV_EQ_DIH_Y bridge (the `taum` body itself is the real
-  -- `Kepler.Text.SphereKit.taum` since DEDUP 2026-09-17).
-  sorry
```

无其他声明/注释改动；`mainNonlinearTerminalV11_p21` 的 `:131-150` R-fix 区域未触碰。

## 5. 验收对照

1. 整编：RC=0、0 error；warning 26（基线 27）— `logs/w1c-final-compile.log`
2. `#print axioms Kepler.Text.tau3_taum_nonplanar_p21` = standard three — `logs/axioms-w1c.log`
3. own-sorry 27 → 26 — `logs/patch-w1c-check.log`
4. `git apply --check`（基线 `5ccd6212`）PASS；end-to-end 应用后 sha256 =
   `ce9fbfb3c64f27e0e4d6872b9c919abd7cce89ae73fe39656e9e62d1ada51249`
5. 主仓 `git status --short` 为空
6. 产物：`patch-w1c.diff`、本文件、`logs/`（含 `probe_w1c_local.lean`、`probe_axioms_w1c.lean`）

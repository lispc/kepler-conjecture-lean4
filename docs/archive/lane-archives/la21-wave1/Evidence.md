# Evidence — la21-wave1

日期 2026-11-05。所有命令在 `lean/`（`/Users/zhangzhuo/repos/kepler-conjecture-lean4/lean`）下执行；
`nice -n 19`，车道并发 ≤ 3。

## 1. 基线与整编

### 1.1 基线（pristine 副本）

```
cd lean
nice -n 19 lake env lean /tmp/la21-wave1/LocalAuto21.lean
```
日志 `logs/baseline-compile.log`：**29 行 warning，0 error**，
29 行全部是 `declaration uses 'sorry'`（即 own-sorry = 29）。
另有 `grep -c '^\s*sorry\s*$' LocalAuto21.lean` = 29，与编译警告一致。

### 1.2 收尾整编（patch 后）

```
cd lean
nice -n 19 lake env lean /tmp/la21-wave1/LocalAuto21.lean
```
日志 `logs/final-compile.log`：**27 行 warning，0 error（RC=0）**。
27 行全部是剩余 `declaration uses 'sorry'`；无新增 linter 警告。

为给 `#print axioms` 提供新声明的环境，另做了一次等价整编（同一文件，加 `-o`）：

```
nice -n 19 lake env lean -R /tmp/la21-wave1/root \
  -o /tmp/la21-wave1/root/Kepler/Text/LocalAuto21.olean \
  /tmp/la21-wave1/root/Kepler/Text/LocalAuto21.lean
```
日志 `logs/final-olean-compile.log`：同样 **27 warning / 0 error**。
`/tmp/la21-wave1/root/Kepler/Text/LocalAuto21.lean` 与交付文件
sha256 均为 `942f122e7b4bcd718dc722b5070e1b137a564c8944bbb163cebb77123e92e5b0`。

> 探针加载说明：Lean 4.32 在 `LEAN_PATH` 的第一个含 `Kepler/` 目录里解析
> `Kepler.*` 模块；直接把 `/tmp/la21-wave1/root` 放最前会导致其余 `Kepler.*`
> 找不到 olean。故用 `logs/probe_axioms.lean` 的 shadow root
> `/tmp/la21-wave1/root3`：对 LA21 闭包的 101 个模块逐一 symlink 到
> `.lake/build/lib/lean` 的 olean，仅 `Kepler/Text/LocalAuto21.olean`
> 用新编的实体文件覆盖；`Mathlib` 落入后续 `LEAN_PATH` 条目。

## 2. `#print axioms`（新 olean，完整输出）

`logs/axioms.log`：

```
'Kepler.Text.azim_dominated_split_p21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.tau3_azim_p21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.tau3_taum_nonplanar_p21' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.sum3_azim_fan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.AZIM_DIHV_SAME_STRONG' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FSQKWKK_p16' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.taum_dih_y_p16' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DIHV_EQ_DIH_Y_4PT_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.azim_lt_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.azim_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.collinear3_iff_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.coplanar_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'collinear_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'mem_affineSpan_pair_iff_exists_lineMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'affineSpan_mono' depends on axioms: [propext, Quot.sound]
'mem_affineSpan' depends on axioms: [propext, Quot.sound]
RC=0
```

- 两件已证声明 = standard three，零 `sorryAx`。
- `tau3_taum_nonplanar_p21` 仍未动，`sorryAx` 保留 —— 与“未动证明”一致。

## 3. W1-C 侦察（import 闭包与候选桥）

### 3.1 闭包计算

用 Python 从源码逐行解析 `^import Kepler...` 的传递闭包（忽略注释中的
自然语言）；LA21 起点：

- 闭包规模 **101 个 Kepler 模块**；闭包内 `^sorry$` 行合计 383。
- `Kepler.Text.LocalAuto38Bridge`：**IN**
- `Kepler.Text.LocalAuto18`：IN
- `Kepler.Text.LocalAuto33`：IN
- `Kepler.Text.LocalAuto38`：**OUT**
- `Kepler.Text.EulerSimplexGeom`：**OUT**

### 3.2 实际 import 链（源码行号）

```
LocalAuto21
 → LocalAuto11.lean:117   import Kepler.Text.LocalAuto2
 → LocalAuto2.lean:82     import Kepler.Text.PackingAuto20
 → PackingAuto20.lean:58  import Kepler.Text.LocalAuto38Bridge
```

`LocalAuto38Bridge.lean:46-49` 只 import `Kepler.Geom.LuneVolume`、
`SphereKit`、`TopologyFan`、`Mathlib`（**不** import `LocalAuto38`）。

### 3.3 探针 A：闭包可达性（`logs/probe_bridge_reach.lean`）

```
import Kepler.Text.LocalAuto21
#check Kepler.Text.DIHV_EQ_DIH_Y_4PT_B
#print axioms Kepler.Text.DIHV_EQ_DIH_Y_4PT_B
#check Kepler.Text.azim_dih_y_p18
#print axioms Kepler.Text.azim_dih_y_p18
```

输出（`logs/recon-axioms.log` A 段）：

```
Kepler.Text.DIHV_EQ_DIH_Y_4PT_B ... :
  dihV v0 v1 v2 v3 = dihY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3) (dist v1 v3) (dist v1 v2)
'Kepler.Text.DIHV_EQ_DIH_Y_4PT_B' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'Kepler.Text.azim_dih_y_p18' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

→ 工单“两个桥都不在闭包内”**不成立**；`_B` 可达且标准三。
闭包内另一个可用形状 `azim_dih_y_p18` 带 `sorryAx`，**不可用**。

### 3.4 探针 B：`LocalAuto38` 的 `DIHV_EQ_DIH_Y_4PT`

```
import Kepler.Text.LocalAuto38
#print axioms Kepler.Text.DIHV_EQ_DIH_Y_4PT
```
输出：`[propext, Classical.choice, Quot.sound]`（但文件本身 OUT of closure）。

### 3.5 探针 C/D：`EulerSimplexGeom.ea2_dihV_eq_dih_y`

- 与 LA21 co-import（`logs/probe_reach.lean`）：无名字冲突，
  axioms = `[propext, Classical.choice, Quot.sound]`。
- 单独 `import Kepler.Text.LocalAuto21`（`logs/probe_reach2.lean`）：
  `error(lean.unknownIdentifier): Unknown identifier Kepler.Text.ea2_dihV_eq_dih_y`
  → 确认 OUT of closure。

### 3.6 结论

- 若下一车道关闭 W1-C：**不需要新增 import 边**，直接用闭包内
  `DIHV_EQ_DIH_Y_4PT_B` + `taum_dih_y_p16`。
- 若设想的“新增 `import Kepler.Text.LocalAuto38Bridge`”发生：它是冗余边
  （已传递可达）；其被用声明的 axioms 面 = standard three，不会引入
  `sorryAx`；且 LA38Bridge 的所有 import 都在 LA21 上游，**不成环**。
- `LocalAuto38`（更重的 92 模块 / 324 sorry 行）不需要，也不要引。

## 4. W1-C 可行性 probe（未搬入文件）

`logs/probe_w1c.lean`：陈述与 `tau3_taum_nonplanar_p21` 逐字一致，
证明用同一组 `¬ Collinear3` helper + 三次 `DIHV_EQ_DIH_Y_4PT_B`
+ `rw [taum_dih_y_p16 ...]` + `simp only [dist_comm, dist_zero_right]`。

```
cd lean
nice -n 19 lake env lean /tmp/la21-wave1/probe_w1c.lean
```
输出 `logs/w1c-probe.log`：**RC=0**（无 error / warning）。
按工单“只做侦察，不要动证明”，此证明**未**写入 `LocalAuto21.lean`。

## 5. patch 与主仓状态

- `patch.diff` 由 pristine `a509e470` 版与 patch 版在临时 git 索引中
  `git diff` 生成（不触碰主仓）。
- 校验（`logs/patch-check.log`）：

```
HEAD now: 19a6cf9007464b4d85718ce10667f326e6f785bb
blob a509e470: a1eac7050c5e64a27afaeff9f785c92a1ae3efbf
blob HEAD:     a1eac7050c5e64a27afaeff9f785c92a1ae3efbf
blob worktree: a1eac7050c5e64a27afaeff9f785c92a1ae3efbf   ← 三者相同
git apply --check --stat patch.diff → RC=0 (78 insertions, 10 deletions)
git status --short → 空
```

> HEAD 在车道运行期间由 `a509e470` 前进到 `19a6cf90`（编排者对表提交），
> 但目标文件 blob 未变，patch 仍可直接 `git apply`。

## 6. 删除面

`patch.diff` 的 10 行删除：

- W1-A：3 行 `-- DISCHARGES:` 注释 + 1 行 `sorry`
- W1-B：4 行 `-- DISCHARGES:`/`-- NEEDS:` 注释 + 1 行 `sorry`
- FILE MAP 1 行：`tau3_azim_p21` (sorry) → (proved)

无其他 `sorry` 被删。own-sorry 29 → 27，净减 2 = 两件真证。

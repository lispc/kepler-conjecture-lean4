# BREAKAGE — DEF-FIX p21-anchor（LA21/LA18 终端锚点重编码）

- 基线：HEAD `873d2a2c`（两目标文件在 `873d2a2c..47766955` 区间 byte-identical，
  `git diff --stat 873d2a2c HEAD -- <files>` 为空）；工作树 = 基线 + 本 patch。
- 方法：① 全库检索两锚及盒谓词的每个引用；② 对每个带
  `(h : mainNonlinearTerminalV11_p21/_p18)` 的声明做整段 body 的 `h` 使用扫描
  （`\bh\b` / `\bh\.`），并人工复核两处已证消费者；③ 按依赖序编译
  `LocalAuto18 → LocalAuto19 → LocalAuto21 → LocalConcl`，全部用补丁后的
  olean（LA18/LA19/LA21 的 olean 由本车道私有 overlay 先重建，随后 14:00 的
  并发 `lake build` 也以同一补丁源重建；post 日志取后者产出的 fresh olean）。

## 0. 结论

| 项目 | 数值 |
|---|---|
| 硬 breakage（编译 error） | **0** |
| 必须改陈述才能修的站点 | **0** |
| 签名中假设类型改变的声明 | **28**（LA18 2 + LA19 23 + LA21 3） |
| 从盒子里取约束的站点（`h (fun …)` / `h ⟨…⟩` / `h.1` / `h.2` / `unfold`） | **0** |
| `LocalConcl.p21_anchor` | 1 处 `sorry`，类型随别名改变，仍是 1 处 `sorry` |
| 净 sorry | **0** |

所有 28 个签名分两类：**(a)** body 为 `sorry`，`h` 完全未用（24 个）；
**(b)** body 已证，仅把 `h` 原样转交给下游同型假设定理（4 个：LA21 的
`CUXVZOZ_p21`、`CJBDXXN_p21`；LA19 的 `terminal_hex_126/135_reduction_p19`
在 body 内把 `h` 转交给 `terminal_hex_234_reduction_p19`）。没有一处消费旧的 `∀ y, box y`
定义体，因此**零修法需求**。

## 1. 逐站点清单

### 1.1 `LocalAuto18.lean`（2 处）

| 文件:行（改前→改后） | 定理 | 用法行 | 已证? | 处理结论 |
|---|---|---|---|---|
| `LocalAuto18.lean:1435→1441` | `L13_LEMMA_p18` | `(h : mainNonlinearTerminalV11_p18)`；body 仅 `sorry` + DISCHARGES 注释 | 否（sorry） | 无需改；假设类型自动变为 registry 合取 |
| `LocalAuto18.lean:1451→1457` | `IUNBUIG_p18` | 同上 | 否（sorry） | 无需改 |

### 1.2 `LocalAuto19.lean`（23 处，行号未变）

| 文件:行 | 定理 | 用法行 | 已证? | 处理结论 |
|---|---|---|---|---|
| `LocalAuto19.lean:447` | `OWZLKVY4_p19` | `(h : mainNonlinearTerminalV11_p18)`；body `sorry` | 否 | 无需改 |
| `:835` | `taud_minimizer_terminal_pent_cases_p19` | 同上 | 否 | 无需改 |
| `:1077` | `edge2_flatD_x1_delta_lemma3_p19` | 同上 | 否 | 无需改 |
| `:1090` | `delta_2_nn_p19` | 同上 | 否 | 无需改 |
| `:1099` | `delta_mono_p19` | 同上 | 否 | 无需改 |
| `:1109` | `flat_term2_126_x_eval_p19` | 同上 | 否 | 无需改 |
| `:1118` | `flat_term2_135_x_eval_p19` | 同上 | 否 | 无需改 |
| `:1127` | `delta_126_x_2h0_le_d_p19` | 同上 | 否 | 无需改 |
| `:1137` | `delta_135_x_2h0_le_d_p19` | 同上 | 否 | 无需改 |
| `:1148` | `lemma_5546286427_p19` | 同上 | 否 | 无需改 |
| `:1175` | `terminal_pent_taum126_012_p19` | 同上 | 否 | 无需改 |
| `:1186` | `terminal_pent_tau135_012_p19` | 同上 | 否 | 无需改 |
| `:1197` | `terminal_pent_tau126_2_p19` | 同上 | 否 | 无需改 |
| `:1208` | `terminal_pent_tau135_2_p19` | 同上 | 否 | 无需改 |
| `:1219` | `terminal_pent_tau126_2h0_p19` | 同上 | 否 | 无需改 |
| `:1230` | `taud_sqrt20_p19` | 同上 | 否 | 无需改 |
| `:1240` | `terminal_pent_tau126_delta20_p19` | 同上 | 否 | 无需改 |
| `:1251` | `terminal_pent_taum_p19` | 同上 | 否 | 无需改 |
| `:1262` | `taud_minimizer_terminal_hex_cases_p19` | 同上 | 否 | 无需改 |
| `:1599` | `taud_mu_clauses_p19` | 同上 | 否 | 无需改 |
| `:1618` | `terminal_hex_234_reduction_p19` | 同上 | 否 | 无需改 |
| `:1649` | `terminal_hex_126_reduction_p19` | `have h := terminal_hex_234_reduction_p19 h …`；`exact h c3 c1 …` | **是** | 纯转发 `h`；下游签名同批改变，类型一致，无需改 |
| `:1690` | `terminal_hex_135_reduction_p19` | `have h := terminal_hex_234_reduction_p19 h …`；`refine … (h c2 c1 …)` | **是** | 同上 |

### 1.3 `LocalAuto21.lean`（3 处）

| 文件:行（改前→改后） | 定理 | 用法行 | 已证? | 处理结论 |
|---|---|---|---|---|
| `LocalAuto21.lean:1178→1181` | `general_482_deformation_p21` | `(h : mainNonlinearTerminalV11_p21)`；body `sorry` | 否 | 无需改 |
| `LocalAuto21.lean:1203→1206` | `CUXVZOZ_p21` | 已证；`general_482_deformation_p21 h …` 纯转发 | **是** | 下游签名同批改变，无需改 |
| `LocalAuto21.lean:1227→1230` | `CJBDXXN_p21` | 已证；`general_482_deformation_p21 h …` 纯转发 | **是** | 无需改 |

### 1.4 `LocalConcl.lean`（1 处定义 + 2 处消费）

| 文件:行 | 声明/用法 | 已证? | 处理结论 |
|---|---|---|---|
| `LocalConcl.lean:1994` | `private theorem p21_anchor : mainNonlinearTerminalV11_p21 := sorry` | 否（sorry） | 类型自动变为 registry 合取；仍是 1 个 sorry，净 0 |
| `LocalConcl.lean:4746` | `refine CUXVZOZ_p21 p21_anchor …` | 是 | `p21_anchor` 作为 h 传入；类型一致，无需改 |
| `LocalConcl.lean:4779` | `CJBDXXN_p21 p21_anchor …` | 是 | 同上 |

**下游额外收益（非本波改动）**：`LocalConcl.lean:1989` 的
`mnt11_anchor : main_nonlinear_terminal_v11 := sorry` 与 `p21_anchor` 现在
同类型；后续车道可令 `p21_anchor := mnt11_anchor`（或删除 `p21_anchor` 直接
注入 `mnt11_anchor`），减少 1 个 sorry。本车道不改 `LocalConcl`（白名单外）。

## 2. 反向证据（模式检索）

在 `lean/` 全树（`--include='*.lean'`）检索：

- `mainNonlinearTerminalV11_p21|mainNonlinearTerminalV11_p18`：共 28 处**代码**
  引用（上述表）+ 文档/注释提及（LA18 header、LA21 header、LA19:8/51、
  LocalConcl:37/355/1990/4719 等）；`LocalAuto31/33/34/38` 等 LA18 importer
  **零引用**。
- `MainNonlinearTerminalV11_p21|MainNonlinearTerminalV11_p18`（盒谓词，大写 M）：
  仅 2 处定义（LA21:131 / LA18:199）+ 本 patch 新增的 2 处 docstring 提及；
  无任何消费者/证明展开。
- `h (fun`、`h ⟨`、`h y`、`h.1`、`h.2`、`unfold mainNonlinearTerminalV11_`、
  `simp [mainNonlinearTerminalV11_`：0 命中。
- 两个锚的 importers（`LocalAuto18 → 31/33/34/38/LocalConcl`、
  `LocalAuto21 → LocalConcl`）中，只有 `LocalConcl` 消费锚；其余仅 import
  其他声明。

## 3. 编译核验（补丁后）

| 文件 | RC | errors | sorry warning（改前 → 改后） |
|---|---|---|---|
| `LocalAuto18.lean` | 0 | 0 | 11 → 11 |
| `LocalAuto19.lean` | 0 | 0 | 29 → 29 |
| `LocalAuto21.lean` | 0 | 0 | 29 → 29 |
| `LocalConcl.lean` | 0 | 0 | — → 23 |

日志：`logs/post-LocalAuto18.log`、`logs/post-LocalAuto19.log`、
`logs/post-LocalAuto21.log`、`logs/post-LocalConcl.log`。另：私有 overlay
（`/tmp/p21-anchor-defix-w1/olean`）上的 `fresh-LocalAuto18/19/21.log`
显示 LA18/LA19 在**只含本 patch 的 fresh olean** 下即 RC=0；LA21 的首次失败
全部是**其它车道在飞**的新 import（`LocalAuto16` 当时新引入的
`LocalAuto26/33/34`）缺 olean，与两行改动无关；并发 `lake build` 补齐后，
规定命令下 LA21 RC=0（`post-LocalAuto21.log`）。

## 4. 文档债（非阻塞，白名单外）

1. `LocalConcl.lean:1990-1993` 的 `p21_anchor` docstring 仍写
   “no bridge from `main_nonlinear_terminal_v11` exists … `∀ y : Fin 6 → ℝ`”。
   改后语义已变（现在是定义别名），建议后续 doc-only 车道更新。
2. `LocalAuto19.lean:8`、`:51` 的注释写 “carried here by
   `mainNonlinearTerminalV11_p18`”，仍然成立（名字保留），无需动。
3. `LocalAuto18.lean` / `LocalAuto21.lean` 的 ENCODING NOTES 已由本 patch
   同步更新。

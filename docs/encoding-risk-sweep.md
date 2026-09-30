# 冻结陈述编码风险扫描（encoding-risk-sweep）

> 只读侦察 lane 产出（2026-09-30）。范围：LocalAuto1-38 全部 + PackingAuto
> 高 sorry 区 PA25/PA18/PA4/PA7/PA1（另顺带核了 PA2 的 pack_concl 注册表、
> PA5 permutes 件、PA22/PA24 的 ℂ-arg 件）。四类缺陷逐类 grep + HOL 对照
> （`reference/flyspeck` @ `1ce0353`）+ 分诊。**零 .lean 改动、零 git 操作、
> 禁跑全项目 build**；唯一机器验证 = 一次 `/tmp` 微探针（`lake env lean`
> 单文件对现存 olean，0 error，验证后已删，见 §2.4）。
> 已知五枚陈述级假件（SF15/19/20/22 等）不重复立案，只标状态。

## 0. 总表

| 类别 | 命中 | 坐实反例 | 可疑（分叉坐实/反例未立） | 清除（无病） | 新增 SF 立案建议 |
|---|---|---|---|---|---|
| 1 arg 值域 | 4 | 0 | 4（PA22） | 9 | 4（批 B） |
| 2 permutes 强度 | 5 | **5（探针机器验证）** | 0 | 14 | 4（批 A；另 1 枚已立案 SF15） |
| 3 缺前提 | 2 | 0 | 1 | 1（+整段测度 lane 验明无病） | 1 登记（不立项） |
| 4 自由点前提 | ~150 原始 → 8 复核 | 0 | 0 | 8（含 ~40 件 deformation 族批清） | 0 |

**结论：LocalAuto1-38 在四类上全部干净（0 命中）；风险集中在 PA2/PA5/PA7
的弱 `permutes` 族（坐实 5 枚）与 PA22 的 `Complex.arg` 族（新增可疑 4 枚）。
预计新增 SF 立案 8 件（批 A 4 + 批 B 4），其中批 A 全部有机器验证的统一反例
引擎，修复档位 S/M，可与 SF15 同批处理。**

---

## 1. 类别 1：arg 值域类（flyspeck `Arg` = [0,2π) vs `Complex.arg` = (−π,π]）

全库 grep `Complex.arg`/`Real.arg`/`Real.atan`（另核 `atn2`）：命中集中在
PA22（59 处，已知 ARG lane）与 PA24/PA18/PA21/TopologyFan（少量）。
**LocalAuto1-38、PA1/PA4/PA7/PA25 零命中**（LocalAuto 侧仅有 `atn2` 注释与
`Hypermap.faceMap_permutes` 之类无关名）。flyspeck `atn2`（trig1.hl:333-345）
值域 (−π,π]，与 SphereKit 的 `atn2 x y = Real.atan2 y x` 同域，无病。

### 1.1 新增同类（全部 PA22，置信度 = 可疑：语义分叉坐实、为假未立）

| # | 位置 | 陈述 | 缺陷形状 | 分析 |
|---|---|---|---|---|
| C1-1 | PA22:1910 `insert_v` | h1/h4/h5 用 `Complex.arg`；HOL counting_spheres.hl:529 用 `Arg` | h1/h4 因 `psi ∈ (0,π/2)`、`2psi ∈ (0,π)` 两域射线重合无损；**h5 的 `< 2psi` 在主值域下把下半平面法向（Arg ∈ (π,2π)）也吸进前件**，前提被加强 → Lean 陈述严格弱于 HOL（保真破、伪真风险低） | 可疑（M：改述 holArg 后按 HOL 原证明重验） |
| C1-2 | PA22:1940 `poly_sort_fn`（def） | 排序键用 `Complex.arg`；HOL 同名 def 用 `Arg` | 定义级分叉：主值排序 ≠ 圆序。已证消费件（`poly_sort_antisym`/`poly_sort_trans`）前提与结论同域、自洽为真；但任何下游把 `poly_sort_fn` 当圆序消费即传染 | 可疑（M/L：随 holArg 批统一抬升 def 并重验 3 个已证消费件） |
| C1-3 | PA22:3196 `POLYSORT_BIJ2` | 结论三处 `Complex.arg`（含 `arg(a f(j)/u) < arg(a f(k)/u)` 的全序枚举）；HOL counting_spheres.hl:1964 用 `Arg` | ARG_ORDER 同型（排序结论被 2π 折叠）。纸面初判：`≤`-极小性合取支在主值域下可能因"环绕值变负自动 ≤"仍可满足，即分叉但未必为假——**须专案立反例或证真**；至少语义非 HOL（找到的枚举不是圆序） | 可疑（M：与 SF22 同法改述 holArg；反例分析随批补） |
| C1-4 | PA22:3218 `EUSOTYP_simple` | 结论五处 `Complex.arg`（g 的全序 + psi 平分 + `< π`）；HOL counting_spheres.hl:2112 用 `Arg` | 同上型。∃g/h 自由度大（可取向无人选圆序、间隙 < π 的构型），为假风险更低，但语义分叉同坐实；若 P 的圆间隙出现 > π 退化，psi 走负、`h` 落外分角方向，`h i ∈ P` 是否可满足需专案 | 可疑（M：同批改述 + 专案） |

### 1.2 已知在案（状态注记）

- `ARG_ORDER`（PA22:3186）：SF 22 已立项，草案待审（holArg 改述 + 证明待收口）。
- `ARG_INV_ALT`（PA22:3119-3131）：已修（holArg 重述，2026-09-30 前）。
- `holArg`（PA22:3122）即忠实重构（[0,2π)），是批 B 的统一改述目标。

### 1.3 清除（无病，防止攻打 lane 误报）

| 位置 | 件 | 无病理由 |
|---|---|---|
| PA18:365 `ARG_CNJ` | `arg (z/w) = arg (z*conj w)`（w≠0） | 正实数缩放，两域下均真（已证） |
| PA18:379 `RE_NORM_1`、PA18:388 `COS_ARG_VECTOR_ANGLE` | 一律过 `Real.cos` | cos 2π-周期，值域不敏感（已证） |
| PA24:252 `argEqSubsetHalfline`、PA24:284 `argDivEqSubsetHalfline` | `{z | arg z = a} ⊆ 射线` | ∃b 自适应，两域下皆真（已证；HOL REUHADY.hl:88/110） |
| PA21:5256/5274、TopologyFan:3586 | `Complex.arg` | 纯证明体内部（simp/`set`），不在冻结陈述面 |
| SphereKit:37 `atn2` | `Real.atan2 y x` | 与 flyspeck `atn2` 值域 (−π,π] 逐字同域 |

---

## 2. 类别 2：permutes 强度类（PA2:163 弱编码 `x∈s ↔ p x∈s` vs HOL-Light
补集固定 `x∉s → p x = x`；裁定锚 = PA10:183/263）

判据（本轮收紧后）：**弱 permutes 下 `p(Icc 0 k) = Icc 0 k` 仍成立，故
`{leftActionList p ul}` 的可达重排集在两种编码下完全相同**——凡结论只谈
`leftActionList p ul`/`barV`/`mcell`/`rogers`/并集/∃ 的件都不受弱化影响；
**为假的充分必要形状是结论约束 `p` 本身**（`= refl` / `≠ refl` / 由此推出
的列表不等），此时 junk 对换 `p = (k+1 k+2)` 满足全部前提而结论塌。结论侧
（∃/image/集合 `{p | permutes p s}`）的弱化方向只会把陈述变弱，不为假。

### 2.1 未修同类（全部坐实；反例引擎已机器验证，见 §2.4）

| # | 位置 | 陈述 | 缺的 tail-fixedness 形状 | 置信度 | 档位 |
|---|---|---|---|---|---|
| C2-1 | PA7:995 `NOT_ID_IMP_LISTS_NOT_EQ` | `hperm : permutes p (Icc 0 k)` + `¬(p = refl)` ⊢ `¬(ul = leftActionList p ul)` | 缺 `hfix : ∀ j, k < j → p j = j`（恰为 HOL permutes 的补集固定合取支；文件内注记已自认 unprovable） | 坐实（探针 P1-P3 直接否证） | S（补前提 + 注记） |
| C2-2 | PA7:1003 `NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX` | 同型（结论 `¬(hdV ul = hdV (leftActionList p ul)) ∨ …`） | 同上 `hfix`（文件内注记同病） | 坐实（同探针） | S |
| C2-3 | **PA2:3146 `KSOQKWL_concl`** | pack_concl.hl:104-105 注册表件：`permutes p (Icc 0 k)` + `rogers` 相等 ⊢ `p = refl` | 缺 `hfix : ∀ j, k < j → p j = j`（SF15 的 `hpout` 形）。**SF15 补丁只覆盖 PA7:1014，未覆盖此孪生**；消费点 PackingConcl.lean:286 `KSOQKWL_concl_discharged` 须同步加参（SF20 的 PA17-shim 教训） | 坐实（同探针；junk 对换下 hrog 平凡真） | S + 消费者穿透 |
| C2-4 | **PA5:132 `PERMUTES_TRIVIAL`** | `permutes p {0} ↔ p = refl` | 不可加前提修（陈述是 permutes↔恒等识别本身）：弱编码下 `swap 1 2` 反例。补集固定语义下原述才真。修复 = 引入补集固定 `permutesHL` 后重述，或按 HOL pack3.hl:103 语义冻结黑名单（当前无消费者，仅 PA14:882 docstring 提及） | 坐实（探针 P4） | M（语义件）或冻结黑名单 |
| （已知） | PA7:1014 `KSOQKWL` | 同 C2-3 母件 | SF15 已立案（`hpout : ∀ x, k < x → p x = x`），补丁草案待审**未应用**；陈述现状仍无 hpout | 坐实（SF15 反例已核） | —（随批 A 落地） |

### 2.2 批 A 建议（permutes 补集固定批）

1. C2-1、C2-2、C2-3、（SF15）四件同一 `hfix` 形状，照抄 SF15 补丁模式一次
   落地；C2-3 记得 PackingConcl:286 加参穿透。
2. C2-4 与批同车但走语义注记/黑名单（不阻塞）。
3. 探针记录（§2.4）可直接作为批 A 的机器验证附件。

### 2.3 清除清单（无病，防止 LocalAuto/PA 攻打 lane 误报）

| 位置 | 件 | 无病理由 |
|---|---|---|
| PA7:859 `YIFVQDV_1`、PA7:866 `YIFVQDV`、PA2:3137 `YIFVQDV_concl` | 结论只依赖重排结果 | 可达重排集两编码相同（§2 判据）；HOL 证明经 XNHPWAB1 集合型 omega_list |
| PA7:1049 `WQPRRDY`、PA2:3168 `WQPRRDY_concl` | ⋃₀ over `{p | permutes}` | junk 置换给 `leftActionList p ul = ul`，并集吸收，两编码并集相同 |
| PA7:1023 `IVFICRK(_real3)`、PA2:3156 `IVFICRK_concl`、PackingConcl:299 | 逐对 g | r2 项 16 已裁定（修正 g ≈250 行纸面论证）；PA2 版去掉应用子句前提后仍真（g 逐对构造 + BijOn 不受源外值影响） |
| PA2:3218 `RVFXZBU2_concl`、PackingConcl:377 | 结论侧 ∃ p | ∃ 域变大 = 陈述变弱，不为假 |
| PA14:932 `QZKSYKG2`、PA17:253 `qzksykg2_p17` | 结论侧 image | 同上（junk p 产生额外重排，包含变容易） |
| PA15:2538/2544 `LEFT_ACTION_LIST_2/3_EXISTS` | 结论侧 ∃ p | S₃ 证人本身补集固定，两域同证 |
| PA18:1001 `PERMUTE_BARV3` | 集合型结论 | barV 只依赖 length + setOfList，弱 permutes 足够 |
| PA5:1147/1164/1179 `EL/MEM/SET_OF_LIST_LEFT_ACTION_LIST` | `permutes p {i | i < ul.length}` | 全域有限集弱 permutes 仍给双射重排，集合型结论成立（已证） |
| PA10:196 `RVFXZBU`、PA10:275 `YNHYJIT`、PA14:705 `ynhyjit_p14`、PA14:785 一带、PA17:236 `qzksykg1_p17`、PA14:919 `QZKSYKG1`、PA2:3229 `RVFXZBU3_concl` | — | 均已带 `hfix`（2026-09-17/09-19/09-30 三波 ENCODING-FIX，SF19/20 已应用） |

### 2.4 微探针记录（机器验证，用后即删）

`/tmp/enc_probe1.lean`（import Kepler.Text.PackingAuto2，`lake env lean`
对现存 olean，**0 error**，2026-09-30，验证后已删除）：

- P1：`permutes (Equiv.swap (k+1) (k+2)) (Set.Icc 0 k)` 可证（弱编码）；
- P2：`ul.length = k+1 → leftActionList (Equiv.swap (k+1) (k+2)) ul = ul`；
- P3：三联 `permutes ∧ ¬(p = refl) ∧ ul = leftActionList p ul` 同时可满足
  ——即 C2-1/C2-2/C2-3（及 SF15）的前提全部可满足而结论假；
- P4：`¬ ∀ p, permutes p {0} ↔ p = refl`（C2-4）。

---

## 3. 类别 3：缺前提类（mcell/voronoiList/rogers/grutoti/totalSolid 面）

启发式（结论含 Finite/正测度/非空/Measurable 但假设无 packing；同 HOL 段
姊妹件都有某前提而它没有）机械扫全部目标文件，再对每件回对照 HOL 原文。
**优先区结果干净**：PA25 的 leaf/edge 族（MCELL_WEDGE_UNIQUE、CC_k_PROPS、
MCELL4_* 等 ~40 件）全部自带 `hp hs`；PA4 的 CELL_PARAMETERS 族前提齐
（多为 `_hp/_hs` 未用前缀）；PA7 Rogers 族全带 `hV`；PA23 的 ②③
（sum_volD/pivot/volD_pos/cell_vol）归在跑的 PA23 lane，本轮不重复立案。

登记两条：

| # | 位置 | 件 | 状态 |
|---|---|---|---|
| C3-1 | PA2:279 `vorList` + PA2:3636 `KHEJKCI_concl`（PackingConcl:592 discharged 孪生） | `vor_list` 为**重构 def**（本地 HL 源无此名，文件头 97-100 自认"reconciled at fill-in time"） | 可疑（前提强度未对核 core Flyspeck `Sphere.vor_list`；填证时强制对核——已在原位注记，建议编排者列入 KHEJKCI 填证验收单） |
| C3-2 | PA18:1731 `MCELL2_SUBSET_AFF_GE` | 无前提 sorried | **非缺陷**：mcell2 两分支（交出 affGe / ∅）平凡给出子集关系，定义展开级可填（顺带列入易填清单） |

**验明无病的一段（防误报）**：PA1 的 voronoi 测度段 8 件
（`negligible_voronoi` PA1:954、`MEASURE_VORONOI_CLOSED_OPEN` PA1:1293、
`NEGLIGIBLE_INTER_VORONOI_CLOSED` PA1:1313 等无 packing 前提件）逐条对照
HOL pack1.hl:400 / pack2.hl:325-356——HOL 原文同样无条件（开胞两两不交、
闭开胞差集含于平分超平面并），前提缺失是忠实移植且命题无条件为真。
`measurable/measure_unions_*` 有前提件均带 `hV hs` 与 HOL 一致。

---

## 4. 类别 4：自由点前提误置（REUHADY ¬azim 型）

机械扫（数据型 binder 在去掉 binder 声明后的陈述体中出现 ≤ 1 次）得约
150 条原始命中，逐一分诊后**优先区 0 坐实**：

- **REUHADY 自由点案**（PA2:3653 `REUHADY_concl` 的 `w1 w2`、PA24:1166
  `REUHADY_p24`）：已由 2026-09-30 最小件波处置——`¬(azim u0 u1 w1 w2 = 0)`
  在证明内被真实消费（经 `azim_eq_zero_of_collinearY` 导出 `u0 ≠ u1`），
  version2 分支改带 wedge-intersection 前提；PA24 文件头已注记。无残余。
- **deformation a/b 族**（LA14:661-1016、LA34:2011-3538、LA19 等 ~40 件，
  `a b : ℝ` 只出现在 `Deformation f V a b` 前提）：HOL 原文同形（自由变元
  隐式全称；`Deformation` 自带 `0 ∈ Icc a b` 使 0-邻域论证可用）——忠实，
  批清，攻打 lane 勿再标。
- **经存在性间接约束件**（LA4:724 `POINT_COM_AFF_GT_INTER` 的 `w`、
  LA15:237 `EQ_DIAGONAL_MIN_p15` 的 `y y1`、PA25:1853 `LEAF_RANK_ONTO`
  的 `w0`）：前提经 ∃-消去约束结论变元的几何（两射线共点/对角线相交/
  rank 参数），非误置；LA4:724 原位 NEEDS 注记亦证其可用。
- 其余零星（LA37:456 `INJ_IMP_BIJ_IMAGE_p37` 未用 binder `S'`、LA22:797
  `y`、LA29:2525 等）：已证或平凡闲置 binder，无害。

**类别 4 无新增立案。**给后续波次的判定口诀：前提变元若与结论变元集相交
为空，再看它是否经存在性（∈/≠-存在形状）或经全称域限制起作用——两者都不
才是误置。

---

## 5. 统计与 SF 批次分组

**命中统计**：类别 1 = 4 可疑 + 9 清除；类别 2 = 5 坐实（4 新 + SF15 已立）
+ 14 清除；类别 3 = 1 登记 + 1 易件注记 + 一段验明无病；类别 4 = 0 坐实
（~40 件批清）。

**预计新增 SF 立案 = 8 件**，分两批：

- **批 A（permutes 补集固定批；坐实反例已机器验证；档位 S，含 1 个 M）**
  ① PA7:995 `NOT_ID_IMP_LISTS_NOT_EQ`；② PA7:1003
  `NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX`；③ PA2:3146 `KSOQKWL_concl`
  （+ PackingConcl:286 穿透加参）；④ PA5:132 `PERMUTES_TRIVIAL`（M，
  或冻结黑名单）。与 SF15（PA7:1014，草案待审）同车落地，统一形状
  `hfix/hpout : ∀ j, k < j → p j = j`；探针记录（§2.4）作验证附件。
- **批 B（holArg 抬升批；语义分叉坐实、反例待立；档位 M，一件 M/L）**
  ⑤ PA22:1910 `insert_v`；⑥ PA22:1940 `poly_sort_fn`（def，M/L）；⑦
  PA22:3196 `POLYSORT_BIJ2`；⑧ PA22:3218 `EUSOTYP_simple`。与 SF22
  （ARG_ORDER，草案待审）同车：统一改述 `holArg`，⑥ 的三个已证消费件
  （poly_sort_antisym/trans、p22_enum_sorted 链）随批重验；⑦⑧ 的
  立反例/证真专案随批补。

**给 LocalAuto（1100+ 站点）攻打波的正面结论**：LocalAuto1-38 在全部四类
上零命中（其 permutes 面只有 Mathlib 强语义 `Hypermap.*_permutes` 与已带
hfix 的移植件；其 ℂ/arg 面为空；缺前提面是 fan/scs 局部章 faithfully
不带 packing；自由点面已批清）——LocalAuto 的 sorry 区风险在证明难度而不
在陈述编码，可按原计划开攻。

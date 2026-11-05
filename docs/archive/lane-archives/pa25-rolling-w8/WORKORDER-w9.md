# WORKORDER — pa25-rolling-w9（接 w8）

> 基线：主仓 HEAD ≥ `0e2e2dd4` + w8 `patch-pa25-rolling-w8.diff`
> → PA25 应为 **16,187 行 / 4 裸 sorry / 5 编译器 sorry 警告 / 0 error**，
> MD5 `2c18464087f8f871ae0b92468900b4bd`。唯一可改：
> `lean/Kepler/Text/PackingAuto25.lean`。
> 开工第一步整文件 standalone 打绿（继承字节 ≠ 已验证）。

## 0. w8 已闭（勿重复做）

| 件 | 新行 | 证法要点 |
|---|---|---|
| `real_model_quqy` / `_sym` | 10709/10748 | `GG_MCELL_QUARTER` + `critical_weight1a/b` + `mcell3_gammaX{,b}_gamma3f` + `p25w8_g_quqya`；quqy 用 sym23 元组，须用 9509/9521 私件而非 10970/11032 公开件（前向引用） |
| `real_model_gamma10` / `_11` | 12455/12502 | `GG_MCELL_GENERAL` + `critical_weight1a/b` + `mcell3_gammaX{,b}_gamma3f` + `p25w8_gamma10_gamma11` + `MCELL4_DOMAIN`；gamma10 走 sym23 元组，gamma11 自然元组；y4≥2hmin 由 hnot |
| 分析核 | 10582–10656, 12368 | `p25w8_upsX_sq_pos` / `p25w8_rad2_x_eta_x` / `p25w8_rad2_eta2` / `p25w8_g_quqya` / `p25w8_gamma10_gamma11`（全标准三，可复用） |

新 kit 全部 public（除 3 枚 `sym14` 私件），零 sorry / 零新 import。

## 1. W9-A `CELL_CLUSTER_ESTIMATE_REDUCE`（PA25:6150，PROVABLE，先做）

HOL OXLZLEZ3.hl:3860。归约件，**估 60–120 行**：

1. `intro e`；把 `cellClusterInequality` 展开成逐 `e` 的 `clusterGamma` 目标。
2. 若簇 `{X | e ∈ criticalEdgeX V X ∧ mcellSet V X} = ∅`：`setSum ∅ f = 0`（PA2:127
   `setSum` 定义 + `dif_pos`/`Finset` 空和），`linarith`。
3. 否则取 `X` 与 `he : e ∈ criticalEdgeX V X`；`unfold criticalEdgeX at he` 得
   `⟨u, v, rfl, heE, hlo, hhi⟩`；`unfold edgeX at heE` 得 `⟨a, b, rfl, -, -, hab⟩`。
   由 `hab : a ≠ b` 与 `{u,v} = {a,b}` 反证 `u ≠ v`（`Set.ext` + `simp` 或
   `Set.eq_singleton_iff_unique_mem`）。
4. `hedge u v huv hlo hhi` 给出 `{u,v}` 簇和；用第 3 步的 `u,v,e={u,v}` 把
   `clusterGamma V e (cellCluster V e)` 集合改写为
   `{X | {u,v} ∈ edgeX V X ∧ mcellSet V X}`（`criticalEdgeX` 去掉长度条件，
   长度由 hlo/hhi 供给；`betaBumpV1` 项逐字相同）。
5. 收口用 `simpa [clusterGamma, cellCluster, criticalEdgeX]`。

雷：`e` 的表示 `{u,v}` 不唯一（`{v,u}`），改写时先 `subst`/`rw [h]` 固定一个表示。

## 2. W9-B `CELL_CLUSTER_N_LE_1`（PA25:6498，PROVABLE，中等，★ 主菜）

HOL OXLZLEZ3.hl:4186。**估 150–300 行**。HOL 分支图：

1. **无 4 胞**：若 `∃ ul, barV V 3 ul ∧ {u0,u1} ∈ edgeX V (mcell4 V ul)`，用
   `PackingAuto18.MCELL4_EDGE_FIRST`（:7264）把茎边提到表头，再
   `S_LEAF_CARD2`（:3922）得 `2 ≤ ncard (s_leaf …)`，撞 `hcard ≤ 1`。
   注意 `S_LEAF_CARD2` 的头对是 `elV ul 0, elV ul 1`，与茎边对齐要靠
   `MCELL4_EDGE_FIRST` 的表重排。
2. **逐和项非负**：`setSum` 有限集 + `Finset.sum_nonneg`。取
   `X ∈ {X | {u0,u1} ∈ edgeX V X ∧ mcellSet V X}`，`mcellSet` 给 `X = mcell k V ul`
   （`mcellSet` 定义 / `BumpP4` 分解）。由 `edgeX ≠ ∅` + `EDGE_IMP_K2`
   （`PackingAuto4:1590`）得 `2 ≤ k`；`k ≤ 4`；k=4 被第 1 步排除；故 `k=2 ∨ k=3`。
   - k=2：`GAMMAX_NO_BETA`（PA25:1793，k<4）把 bump 归零，`gammaX ≥ 0` 取
     `TSKAJXY_2`（PA21:9141）。
   - k=3：同 `GAMMAX_NO_BETA` + `TSKAJXY_3`（PA25:3610）。
   两支都得到 `gammaX*weight + betaBumpV1 ≥ 0`。
3. `setSum` 的有限性：`{X | … ∈ edgeX ∧ mcellSet}` 是否有限？HOL 直接用
   `SUM_POS_LE`（对一般集合和）；Lean `setSum` 在无限集上返回 0，故只需
   `0 ≤ setSum`：`setSum` 定义分 `Set.Finite` 两支，无限支 `0 ≤ 0`，有限支
   `Finset.sum_nonneg`。**这是本件最省力的收口路线**。

雷：`mcell k` 的 k 分解（`unfold mcell` 的 if-链）与 `mcell2/mcell3` 转换用
`BumpP4.MCELL2/MCELL3`；`edgeX` 非空 ⇒ `¬ nullSet`（`RIJRIED` 反向）。

## 3. W9-C `pkLeafRankCriticalEdge`（PA25:9869，BLOCKED→可开）

HOL Oxl_real.hl。前提 = W9-A + W9-B 落证后的装配（stub docstring 自述）；
`LEAF_RANKING_LEMMA`(PA25:1274 已真) + `S_LEAF_CARD2` 分派 `n≤1`（W9-B）/
`n≥2`（W9-A + 反证 `cellClusterInequality`）。估 ~100 行。W9-A/B 之前**不要**开。

## 4. 不开（保持）

- `real_model_ox3q1h_merge`(9930)：**BLOCKED**——前提 `hox : ox3q1hP25`，
  而 `ox3q1hP25`(90) 是 DEF-FIX 冻结 DEFHOLE（内容未知），不可证、不可绕。

## 5. 章收尾判定

W8 交付后 PA25 债面 = `ox3q1hP25`(DEFHOLE) + `CELL_CLUSTER_*`×2 +
`pkLeafRankCriticalEdge` + `real_model_ox3q1h_merge`（末者依赖 DEFHOLE）——
**章节可宣布收尾（除 DEFHOLE）**。W9 若闭 W9-A/B，则只剩 DEFHOLE 依赖件，
可写「除 DEFHOLE 全闭」。

## 6. 雷区（承 w8，新增）

1. `UPS_X_POS` 的**正确**形是 y-空间平方长 `2≤a,b,c<4 → 0<upsX(a²,b²,c²)`
   （`p25w8_upsX_sq_pos`）；字面 `0<x4∧0<x5∧0<x6 → 0<upsX` 为假（1,1,9 → −45）。
2. `rhoX·upsX = chi² + 4·deltaX·x4x5x6`（chi 见 `EDGE_LE_2RAD`:7500 内联）是
   `rad2_x_eta_x` 与 `EDGE_LE_2RAD` 共用核，勿再推一遍。
3. quqy 在 `gamma4fgcy_sym23P25`(11032) 之前，必须用 `p25w4_gamma4fgcy_sym23`(9521)
   /`p25w4_rad2YP25_sym23`(9509)。首轮整编踩过（unknown identifier）。
4. `Real.lt_sqrt_of_sq_lt : x² < y → x < √y`（本 Mathlib 名）。
5. `div_le_div_iff₀` 带两个 `0 <` 参数；`le_of_not_lt` 不存在（用 `not_lt.mp`）。
6. 整编前先用 `import Kepler.Text.PackingAuto25` 探针（~20 s）验证新件；
   olean 在源改动后过期，**收尾必须整文件 compile**。
7. `set_option maxHeartbeats 8000000 in` 只加在 gamma10/11 两条（预算），
   勿动陈述。

## 7. 交付（`$S` 根下）

`patch-*.diff` + `Work.lean` + `WORKORDER-w10.md` + `DELIVERY.md` + `Evidence.md`
+ `logs/`；归档 `docs/archive/lane-archives/pa25-rolling-w9/`（Work.lean 不入库）。
验收：闭合件 `#print axioms` = `[propext, Classical.choice, Quot.sound]`；
`ox3q1hP25` 与 624 shard 面零漂移。

# AJRIPQN 分期侦察报告（只读车道）

> 落库版说明（2026-10-21）：正本与证据在
> `~/c17_backup/lane_snapshots/ajripqn_scout/{REPORT,EVIDENCE}.md`。车道在写完全文后
> 死于 `reasoning_content` 400（非内容原因），产物完整。报告 §6.3 建议的 SF 编号
> 「47」已占用（SF-47 = PA24 cover_strong 尾合取），下一个空号为 **SF-48**。

- 仓库：`/Users/zhangzhuo/repos/kepler-conjecture-lean4`
- 日期：2026-10-21
- 范围：`lean/Kepler/Text/PackingAuto17.lean` 的 `AJRIPQN` capstone 及其上游五阶段件
- 性质：处方（不是证明）；所有陈述用 Lean 原文；HOL 只作锚点
- 约束：未修改仓库任何文件；未 git/commit；未跑 `auto_gate.sh`；未动 `.lake`；探针经 `lake env lean --stdin`（不落盘）

---

## 0. 结论速览

1. **PA17 本体零 sorry**：`AJRIPQN` 本体（PA17:929）是五阶段装配 `p17_ajripqn_of_pieces`（PA17:682）的真应用，文件内 `grep -c "^[[:space:]]*sorry"` = 0。但 `#print axioms Kepler.Text.AJRIPQN` = `[propext, sorryAx, Classical.choice, Quot.sound]`，taint 全部来自上游。
2. **任务书有一处重要过时**：`TIWWFYQ`（PA5:663）与 `SLTSTLO1`（PA13:597）**已经真证**，`#print axioms` 均为三零（无 `sorryAx`）。它们不是债务。
3. **当前代码可达的直接 sorry 叶 = 7**：
   `SLTSTLO2`、`DDZUPHJ`、`RVFXZBU`(仅 i=3)、`QZKSYKG1`、`QZKSYKG2`、`MCELL_2_PROPERTIES_lemma1`、`measurableSet_affGe_wedge_p10`。
   前 5 个是任务书的「五阶段件」；后 2 个是 PA10 的隐藏叶，经 `BOUNDED_MCELL`/`MEASURABLE_MCELL` 进入 PA17 stage 1。
4. **全闭包（让 AJRIPQN 真正无 sorryAx）还需 8 个节点**：
   `NJIUTIU`、`TEZFFSK`、`ROGERS_INTER_V_LEMMA`、`CONVEX_HULL_EQ_EQ_SET_EQ`、`INTER_RCONE_GE_LE_lemma`、`YIFVQDV_1`、`WQPRRDY`，以及**缺失的 Lean 陈述** `LEFT_ACTION_LIST_PROPERTIES`（S₃ kit）。另有 `YNHYJIT` i=3 可通过 PA14 的 01-kit 绕开；若直接调用则再加 1。
   即：**表面 7 根，全闭包 15 个节点**（15 = 7 + 7 支撑 + 1 缺失陈述）。
5. **最大单件风险不是 SLTSTLO2 而是 QZKSYKG2 k=2**：QZKSYKG2 的 HOL 证明 325-2251 行中，k=0/1 约 16 行、k=4 约 14 行、k=3 约 212 行、**k=2 约 1681 行**（`QZKSYKG.hl:570-2251`）。k=2 的 rcone/midpoint 代数才是巨案主体。
6. **最大架构风险是 S₃ kit 的落点**：`PA12 imports PA10`，而 `PA10` 不 import PA12/PA14。若把 `LEFT_ACTION_LIST_PROPERTIES` 落在 PA12，PA10 里的 `RVFXZBU` i=3 与 `YNHYJIT` i=3 无法消费。推荐：kit 落 PA12；在 PA14 重新落 `RVFXZBU_p14`/`YNHYJIT` i=3；PA17 的 `hRV` 改接（1 行）——PA10 源件保留为 off-path orphan，另账处理。
7. **需要 statement-fix 的点**：只有 1 个新的：`LEFT_ACTION_LIST_PROPERTIES` 必须补 tail-fixedness `hfix`（HOL `permutes` 是 complement-fixing）。QZKSYKG1/RVFXZBU 的 SF-20、QZKSYKG2 的 SF-38 **已经应用**，无需重做。
8. **推荐首发**：批次 B1（S₃ action kit）。它一次解锁 4 个节点（RVFXZBU i=3、YNHYJIT i=3、QZKSYKG1 k=3、QZKSYKG2 k=3），是贪心扇出最高且必须最先做的共享件。备选首发：B9（PA10 可测链，独立、便宜、符合官方十二发波顺序 a）。
9. **预计总轮数**：9 个派工批、15-18 个子批（每子批 ≤500 行 Lean），约 32-44 轮。
10. **消费者确认**：REUHADY1(d) 的 `p24_wedge_cells_pair_null`（PA24:3321）、`p24_edgeX_of_leaf4/leaf23`（PA24:4447/4660）、`p24_cell_cap_dihX_strong`（PA24:5522）直接消费 AJRIPQN；capstone 2 的 `QZYZMJC` 在 PA16:743 直接消费 AJRIPQN。

---

## 1. 侦察方法与只读边界

执行的命令与原文摘录见同目录 `EVIDENCE.md`。核心手段：

- `grep -n "^[[:space:]]*sorry"` 区分 proof-body sorry 与 docstring 中的 "sorry" 字样；
- `#print axioms` 经 `lake env lean --stdin` 探针，直接判定「已绿 / 带 sorryAx」；
- `grep -n "^import"` 重建 import DAG，判定共享 kit 的落点；
- HOL 侧用 `lean/scripts/packing/*.hl` 与 `reference/flyspeck/azure/hol-light-nat/` 原文；
- 未运行 `lake build`（避免写 `.lake`），使用 2026-10-20 的既有 olean。

**重要口径**：本报告把「已绿入库」定义为 `#print axioms` 不含 `sorryAx`；把「direct sorry」定义为当前文件中有实际 `sorry` 体、且经代码路径可达 AJRIPQN 的声明；把「支撑叶」定义为当前因父件 body 是 `sorry` 而尚不可达、但填父件后会暴露的 `sorry`。

---

## 2. 依赖图

### 2.1 PA17 五阶段 → 上游件

```
AJRIPQN (PA17:929, 本体 0 sorry, 但 sorryAx)
└─ p17_ajripqn_of_tailfix (PA17:827)
   └─ p17_ajripqn_of_pieces (PA17:682)
      ├─ stage1 (PA17:372) — 测度鸽笼 over Voronoi 胞
      │  ├─ TIWWFYQ (PA5:663)                         [已绿, 三零]
      │  ├─ KIUMVTC (PA5:633) / VORONOI_BALL2 (PA5:739) [已绿]
      │  ├─ BOUNDED_MCELL (PA10:738)                   [带 sorryAx]
      │  │  └─ MCELL_2_PROPERTIES_lemma1 (PA10:703/707) [DIRECT SORRY]
      │  │     └─ INTER_RCONE_GE_LE_lemma (PA10:689/695) [支撑叶]
      │  └─ MEASURABLE_MCELL (PA10:847)                [带 sorryAx]
      │     └─ measurableSet_affGe_wedge_p10 (PA10:831/833) [DIRECT SORRY]
      ├─ stage2 (PA17:420) — 鸽笼 over rooted Rogers 单形
      │  ├─ GLTVHUM_concl (PA2:3462)                   [已绿, 三零]
      │  ├─ BARV_3_EXPLICIT (PA8:210)                  [已绿]
      │  ├─ OMEGA_LIST_IN_VORONOI_LIST (PA5:2296)      [已绿]
      │  └─ BARV_SUBSET (PA5:1285)                     [已绿]
      ├─ stage3 (PA17:487) — DUUNHOR trim
      │  ├─ DUUNHOR_concl (PA2:3504)                   [已绿, 前提加强]
      │  ├─ p17_coplanar_null (PA17:330)               [已绿]
      │  └─ p17_sUnion_null (PA17:272) / p17_measure_sdiff_ge (PA17:297) [已绿]
      ├─ stage4 (PA17:626) — 五胞鸽笼
      │  └─ SLTSTLO1 (PA13:597)                        [已绿, 三零]
      ├─ stage5 (PA17:647) — 唯一性 off null set
      │  └─ SLTSTLO2 (PA13:820/823)                    [DIRECT SORRY]
      ├─ hQ1 → qzksykg1_p17 (PA17:236) → QZKSYKG1 (PA14:902/914) [DIRECT SORRY]
      │  ├─ LEFT_ACTION_LIST_PROPERTIES (marchal2.hl:4460) [缺失陈述, 需新 SF]
      │  ├─ YNHYJIT (PA10:590; i=3 608)                 [支撑叶, 可绕开]
      │  └─ YIFVQDV_1 (PA7:2697/2701)                   [支撑叶]
      ├─ hQ2 → qzksykg2_p17 (PA17:259) → QZKSYKG2 (PA14:945/961) [DIRECT SORRY; SF-38 已应用]
      │  ├─ WQPRRDY (PA7:2994/2999)                     [支撑叶]
      │  ├─ LEFT_ACTION_LIST_PROPERTIES                  [缺失陈述]
      │  └─ 01-swap kit (PA14:643/792/829)              [已绿]
      ├─ hRV → RVFXZBU (PA10:413; i=3 488)              [DIRECT SORRY（仅 i=3）]
      │  ├─ LEFT_ACTION_LIST_PROPERTIES                  [缺失陈述]
      │  └─ SET_OF_LIST_TRUN2_LEFT_ACTION_LIST2          [新私件, 小]
      └─ hDD → DDZUPHJ (PA13:849/855)                   [DIRECT SORRY]
         ├─ TEZFFSK (PA9:367/388)                        [支撑叶]
         │  └─ NJIUTIU (PA9:339/350)                     [支撑叶]
         │     └─ CONVEX_HULL_EQ_EQ_SET_EQ (PA5:154/155) [支撑叶]
         ├─ ROGERS_INTER_V_LEMMA (PA12:878; PA11:418)    [支撑叶]
         └─ WAUFCHE1/2 (PA7:2431/2460)                  [已绿]
```

### 2.2 债务根计数

| 口径 | 数量 | 内容 |
|---|---:|---|
| 任务书「五阶段件」 | 5 | SLTSTLO2, DDZUPHJ, RVFXZBU(i=3), QZKSYKG1, QZKSYKG2 |
| 表面代码可达 direct sorry | **7** | 上述 5 + `MCELL_2_PROPERTIES_lemma1` + `measurableSet_affGe_wedge_p10` |
| 填体后暴露的支撑叶 | 7 | `NJIUTIU`, `TEZFFSK`, `ROGERS_INTER_V_LEMMA`, `CONVEX_HULL_EQ_EQ_SET_EQ`, `INTER_RCONE_GE_LE_lemma`, `YIFVQDV_1`, `WQPRRDY` |
| 缺失 Lean 陈述 | 1 | `LEFT_ACTION_LIST_PROPERTIES`（S₃ kit） |
| **全闭包节点** | **15** | 7 + 7 + 1 |
| 可绕开、不计入 15 | 1 | `YNHYJIT` i=3（用 PA14 01-kit 或 S₃ kit 直接供给；若调用 PA10 现定理则 +1） |

### 2.3 分类（已绿 / direct sorry / shim 或弱形 / 需 SF）

| 件 | 文件:行 | 状态 | 备注 |
|---|---|---|---|
| TIWWFYQ | PA5:663 | **已绿** | `#print axioms` 三零；任务书行号 581 已过时 |
| SLTSTLO1 | PA13:597 | **已绿** | `#print axioms` 三零；任务书行号 307 已过时 |
| GLTVHUM_concl | PA2:3462 | **已绿** | 三零；PA6:1265 twin 同 |
| DUUNHOR_concl | PA2:3504 | **已绿但前提加强** | Lean 多 `Packing V`/`saturated V`；HOL pack_concl 无此二前提；对 PA17 足够，但不是逐字接口 |
| MEASURE_NEGLIGIBLE_SYMDIFF | HOL measure1.ml:550 | **替身已绿（弱形）** | Lean 无同名件；PA17:297 `p17_measure_sdiff_ge` 只给 `volume s ≤ volume (s \ t)`（`volume t = 0`），对 AJRIPQN 的正测保持足够；不是等号形式 |
| SLTSTLO2 | PA13:820/823 | **direct sorry** | HOL SLTSTLO.hl:582-3692；3100 行级 |
| DDZUPHJ | PA13:849/855 | **direct sorry** | HOL DDZUPHJ.hl:29-34/59-608 |
| RVFXZBU | PA10:413/488 | **direct sorry（仅 i=3）** | i=0,1,2,4 已证；SF-20 hfix 已应用；weak-permutes caveat 已由 hfix 关闭 |
| QZKSYKG1 | PA14:902/914 | **direct sorry** | SF-20 hfix 已应用；k=4 另卡 `YIFVQDV_1` |
| QZKSYKG2 | PA14:945/961 | **direct sorry** | SF-38 tail-fixed comprehension 已应用；k=2 是巨案 |
| MCELL_2_PROPERTIES_lemma1 | PA10:703/707 | **direct sorry（隐藏）** | 经 BOUNDED_MCELL → stage1 |
| measurableSet_affGe_wedge_p10 | PA10:831/833 | **direct sorry（隐藏）** | 经 MEASURABLE_MCELL → stage1 |
| LEFT_ACTION_LIST_PROPERTIES | 无 Lean 声明 | **缺失陈述 / 需新 SF** | marchal2.hl:4460-5662；需补 `hfix` |
| YIFVQDV_1 | PA7:2697/2701 | 支撑叶 | QZKSYKG1 k=4 |
| WQPRRDY | PA7:2994/2999 | 支撑叶 | QZKSYKG2 k=3/4 |
| NJIUTIU | PA9:339/350 | 支撑叶 | DDZUPHJ |
| TEZFFSK | PA9:367/388 | 支撑叶 | DDZUPHJ |
| ROGERS_INTER_V_LEMMA | PA12:878 / PA11:418 | 支撑叶 | DDZUPHJ k=1 |
| CONVEX_HULL_EQ_EQ_SET_EQ | PA5:154/155 | 支撑叶 | NJIUTIU |
| INTER_RCONE_GE_LE_lemma | PA10:689/695 | 支撑叶 | MCELL_2_PROPERTIES |
| YNHYJIT | PA10:590/604,608; PA14:712/766 | 支撑叶（可绕开） | i=2 已有 01-kit；i=3 用 S₃ kit |

---

## 3. 逐件盘点

### 3.1 TIWWFYQ（已绿）

- Lean：`lean/Kepler/Text/PackingAuto5.lean:663`，文件 2305 行，无 sorry 体。
- 陈述：
  ```lean
  theorem TIWWFYQ (V : Set V3) (p : V3) (hV : Packing V) (hs : saturated V) :
      ∃ v ∈ V, p ∈ voronoiClosed V v
  ```
- HOL：`pack3.hl:564`（proof 564-613）。
- 复用引理：`KIUMVTC`（PA5:633）、`PACKING_IMP_DISCRETE`（PA5:627）、`saturated` 定义（PA2:266）。
- 风险：无。`#print axioms` 三零。
- 消费者：PA17 stage1（:398）、PA16 `QZYZMJC`（:805）、PA23（:5791）。

### 3.2 SLTSTLO1（已绿）

- Lean：`lean/Kepler/Text/PackingAuto13.lean:597`，文件 857 行。
- 陈述：
  ```lean
  theorem SLTSTLO1 (V : Set V3) (ul : List V3) (p : V3) (hs : saturated V)
      (hp : Packing V) (hb : barV V 3 ul) (hpr : p ∈ rogers V ul) :
      ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul
  ```
- HOL：`SLTSTLO.hl:43-580`；concl `pack_concl.hl:135`。
- 复用引理：`RCONE_GT_EQ_EMPTY_LEMMA`（PA13:387）、`p13_hull_break4`（PA13:427）、`p13_barV_hd_ne`（PA13:408）、`RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE`（PA12:1272，已证）、`OMEGA_LIST_1_EXPLICIT_NEW`（PA12:1436）、`CONVEX_HULL_4_SUBSET_AFF_GE_2_2`（PA12:1608，三零）、`MXI_EXPLICIT_OLD`（PA12:2075）。
- 风险：`#print axioms` 三零；但证明内部引用的 `RCONEGE_INTER...` 等已绿。无 statement gap。
- 消费者：PA17 stage4（:635）、PackingConcl `SLTSTLO1_concl_discharged`（:363）、PA16:805、PA23/PA24 覆盖链。

### 3.3 SLTSTLO2（direct sorry，最大独立件）

- Lean：`lean/Kepler/Text/PackingAuto13.lean:820`，body `sorry` 在 :823；文件 857 行。
- 陈述：
  ```lean
  theorem SLTSTLO2 (V : Set V3) (ul : List V3) :
      ∃ Z : Set V3, ∀ p : V3, saturated V → Packing V → barV V 3 ul →
        nullSet Z ∧ (p ∈ rogers V ul \ Z → ∃! i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul)
  ```
- HOL：`SLTSTLO.hl:582-3692`；concl `pack_concl.hl:138`。
- HOL 证明结构：
  - `Z = B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7`（SLTSTLO.hl:584-597）；
  - B1 = `frontier (rogers V ul)`；B2 = `{w | norm (w - HD ul) = sqrt 2}`；B3 = `rcone_eq (HD ul) (HD (TL ul)) (hl (truncate_simplex 1 ul)/sqrt 2)`；B4/B6 = 以 `HD` 为基础的三点仿射壳；B5 = `convex hull {ω2, ω3}`；B7 = `affine hull {ω1, ω2, ω3}`；
  - null 证明：`NEGLIGIBLE_UNION` + `NEGLIGIBLE_CONVEX_FRONTIER` + `NULLSET_SPHERE` + `NEGLIGIBLE_RCONE_EQ` + `NEGLIGIBLE_AFFINE_HULL_3` + `NEGLIGIBLE_CONVEX_HULL_3`；
  - 存在性：直接调 `SLTSTLO1`（SLTSTLO.hl:677-686）；
  - 唯一性：按 `hl ul < sqrt2`、`dist(u0,p) ≥ sqrt2`、`rcone_gt`/`aff_ge`/`j ∈ {0,1,2,3}` 的巨 case tree（SLTSTLO.hl:687-3692）。
- Lean 可复用：`NULLSET_SPHERE`（PA13:371，已绿）、`SLTSTLO1`（PA13:597，已绿）、`MCELL_EXPLICIT`（PA12:623）、`EMNWUUS2`（PA9:121，已绿）、`XNHPWAB1-4`（PA7，已绿）、`ROGERS_EXPLICIT`（PA12:1906）、`CONVEX_HULL_4_SUBSET_AFF_GE_2_2`、`RCONE_GT_EQ_EMPTY_LEMMA`（PA13:387）、Mathlib `Measure.addHaar_affineSubspace`、`Convex.addHaar_frontier`。
- 缺失件（需新私件）：`nullSet (rcone_eq a b r)`（HOL `NEGLIGIBLE_RCONE_EQ` 未移植）；`nullSet (affineSpan {a,b,c})`（可用 `p17_coplanar_null` + 三点共面）；`nullSet (convexHull {a,b})`（线段零测）；`nullSet (frontier (rogers V ul))`（凸紧集边界零测，可用 `Convex.addHaar_frontier`）。
- 风险：
  - 3100 HOL 行；但其中约 3000 行是唯一性 case tree，**不是**单一的 `RVFXZBU1` 调用。PA13:818 的 docstring 说「killed by RVFXZBU1 (Auto10)」与 HOL 证明不符（HOL SLTSTLO2 未调用 RVFXZBU1）；这是 docstring 风险，不是陈述缺口。
  - `rcone_eq` 零测需要新的几何测度论证（HOL `NEGLIGIBLE_RCONE_EQ`），是本件最硬的单点。
  - 陈述本身逐字 faithful；无 SF。
- 消费者：PA17 stage5（:841）、PackingConcl `SLTSTLO2_concl_discharged`（:371）。

### 3.4 RVFXZBU（direct sorry，仅 i=3）

- Lean：`lean/Kepler/Text/PackingAuto10.lean:413`，body `sorry` 在 :488；文件 905 行。
- 陈述：
  ```lean
  theorem RVFXZBU {V : Set V3} {ul : List V3} {i : ℕ} {p : Equiv.Perm ℕ}
      (hi : i ∈ ({0, 1, 2, 3, 4} : Set ℕ))
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hperm : permutes p (Set.Icc 0 (i - 1)))
      (hfix : ∀ j, i ≤ j → p j = j) :
      mcell i V (leftActionList p ul) = mcell i V ul
  ```
- HOL：`RVFXZBU.hl:32-36`（concl），proof 38-195。
- 现状：
  - i=0/1：`eq_refl_of_fix_p10` + `leftActionList_refl_p10`（PA10:168/160）；
  - i=2：`mcell2_swap_p10`（PA10:346）+ `omegaListN{1,2,3}_swap_p10` + `mxi_swap_p10`；
  - i=4：`setOfList_leftActionList_fix_p10`（PA10:130）+ `hl`/`setOfList` invariance；
  - **i=3：`sorry`（PA10:488）**。
- HOL i=3 依赖（RVFXZBU.hl:160-195）：
  - `SET_OF_LIST_TRUN2_LEFT_ACTION_LIST2`（未移植，小件）；
  - `LEFT_ACTION_LIST_PROPERTIES`（marchal2.hl:4460）；
  - `mcell3` 展开。
- 风险 / weak-permutes caveat：
  - 陈述已带 `hfix`（SF-20，PA10:391-412 ruling），weak `permutes` caveat **已关闭**；
  - 消费者 PA17 的 `hRV` 传 `hfix`（PA17:848-849）；
  - PA25 只用 i=4（PA25:2742/3298，已证）；
  - PA2 `RVFXZBU3_concl`（PA2:5507）仍 sorry，且量化所有 i；PA10 的 twin 只覆盖 i∈{0..4}，PackingConcl:400 已记「twin mismatch」，不在 AJRIPQN 链。
- 关键架构限制：RVFXZBU 在 PA10，PA10 不 import PA12/PA14；S₃ kit 若落 PA12，PA10 i=3 无法消费。见 §5.2 的方案 A/B。

### 3.5 DDZUPHJ（direct sorry）

- Lean：`lean/Kepler/Text/PackingAuto13.lean:849`，body `sorry` 在 :855；文件 857 行。
- 陈述：
  ```lean
  theorem DDZUPHJ (V : Set V3) (ul vl : List V3) (k : ℕ)
      (hs : saturated V) (hp : Packing V) (hk : k ≤ 4)
      (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
      (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3)
      (hne : mcell k V ul ≠ ∅) :
      mcell k V ul = mcell k V vl
  ```
- HOL：`DDZUPHJ.hl:29-34`（concl），proof 59-608。
- HOL 结构（case k=4,3,2,1,0）：
  - k=4：非空 → `hl ul < sqrt2` → `TEZFFSK` 给 `truncate 3 ul = truncate 3 vl = ul = vl`；
  - k=3,2,1：非空 → circumradius regime；`NJIUTIU` 给 omega chain 相同；`TEZFFSK` 给 truncation 相同；`WAUFCHE1/2` 给 `mxi` 相同；k=1 还需 `ROGERS_INTER_V_LEMMA` 给 `HD ul = HD vl`；k=2 由 `BARV_IMP_LENGTH_EQ_CARD` + `TRUNCATE_SIMPLEX_BARV` 识别 `{u0,u1}`；
  - k=0：同一 rogers 减同一 ball。
- Lean 可复用：`MCELL_EXPLICIT`（PA12:623）、`WAUFCHE1/2`（PA7:2431/2460）、`HD_TRUNCATE_SIMPLEX`（PA5:1421）、`OMEGA_LIST_LEMMA`（PA5:2229）、`BARV_IMP_LENGTH_EQ_CARD`（PA7:1316）、`TRUNCATE_SIMPLEX_EXPLICIT_1/2/3`（PA8/PA5）、`RCONE_GT_EQ_EMPTY_LEMMA`（PA13:387）。
- 依赖（需先做）：`TEZFFSK`、`NJIUTIU`、`ROGERS_INTER_V_LEMMA`。
- 风险：
  - PA13 当前**不 import PA9**（PA13:73-79 只有 PA2/5/6/7/8/12）；填 DDZUPHJ 时需在 PA13 顶部加 `import Kepler.Text.PackingAuto9`（PA9 只 import PA2/5/6/7/8，无环）。
  - `ROGERS_INTER_V_LEMMA` 公开 twin 在 PA12:878（sorry），PA13 可直接消费；PA11 的是 private。
  - 陈述逐字 faithful（`k ≤ 4` ↔ HOL `k IN {0..4}`）；无 SF。
- 消费者：PA17 `hDD`（:850-851）；无 pack_concl 接口。

### 3.6 QZKSYKG1（direct sorry）

- Lean：`lean/Kepler/Text/PackingAuto14.lean:902`，body `sorry` 在 :914；文件 963 行。
- 陈述：
  ```lean
  theorem QZKSYKG1 {V : Set V3} {ul vl : List V3} {k : ℕ} {p : Equiv.Perm ℕ}
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hne : mcell k V ul ≠ ∅)
      (hperm : permutes p (Set.Icc 0 (k - 1)))
      (hfix : ∀ j : ℕ, k ≤ j → p j = j) (hvl : vl = leftActionList p ul) :
      barV V 3 vl
  ```
- HOL：`QZKSYKG.hl:244-253`（concl），proof 266-320（仅约 55 行）。
- HOL case split：
  - k=0/1：`PERMUTES_TRIVIAL` + `LEFT_ACTION_LIST_I`；
  - k=4：`MCELL_EXPLICIT`/`mcell4` 非空 → `hl ul < sqrt2` → `Rogers.YIFVQDV_1`（k=3 实例）；
  - k=3/2：`MCELL_EXPLICIT`/`mcell{3,2}` 非空 → `YNHYJIT`（i=3 用 S₃ kit；i=2 用 01-kit）。Lean 也可以不调用 `YNHYJIT`，直接在 QZKSYKG1 内联 S₃ kit；推荐先补 `YNHYJIT` i=3（B2），保持 HOL 证明结构。
- Lean 可复用：`MCELL_EXPLICIT`（PA12:623）、`YIFVQDV_1`（PA7:2697，需先填）、`LEFT_ACTION_LIST_1_PROPERTIES_ALT`（PA14:792，已绿）、`MCELL2_PERMUTE_01`（PA14:829，已绿）、`p14_swap_pack`（PA14:643）、`eq_refl_of_fix_p10`（PA10:168）、`leftActionList_refl_p10`（PA10:160）。
- 风险：
  - **不要用 `PERMUTES_TRIVIAL`**（PA5:135，sorryAx）；k=0/1 用 `eq_refl_of_fix_p10` 即可。
  - k=4 依赖 `YIFVQDV_1`；k=3 依赖 S₃ kit；k=2 依赖 01-kit（已绿）。
  - SF-20 已应用；陈述 faithful。
- 消费者：PA17 `hQ1`（:845-846）、PA20:816/2102。

### 3.7 QZKSYKG2（direct sorry，HOL 巨案）

- Lean：`lean/Kepler/Text/PackingAuto14.lean:945`，body `sorry` 在 :961；文件 963 行。
- 陈述：
  ```lean
  theorem QZKSYKG2 {V : Set V3} {ul : List V3} {k : ℕ}
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
      mcell k V ul ⊆
        ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧
            ∀ n : ℕ, k ≤ n → p n = n})
  ```
- HOL：`QZKSYKG.hl:255-262`（concl），proof 325-2251。
- HOL case 规模（按 `ASM_CASES_TAC` 界标）：
  - k=0/1：`QZKSYKG.hl:328-341`，约 16 行；
  - k=4：`:344-355`，约 14 行；`WQPRRDY` + `mcell4` hull；
  - k=3：`:358-569`，约 212 行；`WQPRRDY`（对 `truncate 2 ul`）+ `LEFT_ACTION_LIST_PROPERTIES`；
  - k=2：`:570-2251`，约 1681 行；`TWO_REARRANGEMENT_LEMMA`、`YNHYJIT` i=2、`ROGERS_EXPLICIT`、`MXI_EXPLICIT`、`OMEGA_LIST_1_EXPLICIT_NEW`、`MHFTTZN4`、长 rcone/midpoint 代数。
- Lean 可复用：`WQPRRDY`（PA7:2994，需先填）、`LEFT_ACTION_LIST_1_PROPERTIES_ALT`（PA14:792，已绿）、`MCELL2_PERMUTE_01`（PA14:829，已绿）、`twoRearrangementLemma`（PA14:100，private 已证）、`rogersExplicit2`（PA14:129，private 已证）、`convexHull4Imp31`（PA14:145，private 已证）、`MXI_EXPLICIT`（PA12:1958，已绿）、`ROGERS_EXPLICIT`（PA12:1906）、`OMEGA_LIST_1_EXPLICIT_NEW`（PA12:1436）、`MHFTTZN4`（PA6:3163）、`OMEGA_LIST_N_IN_VORONOI_LIST_GEN`（PA6:1388）、`AFF_GE_2_2`（PA12:225）。
- 风险：
  - **k=2 是本链最大的单件**（1681 HOL 行），不要按「QZKSYKG2 总共 1900 行」平摊；k=4 与 k=3 很便宜。
  - SF-38 已应用；`qzksykg2_p17`（PA17:259）是转发 shim，PA14 body 落地后删除。
  - PA17 的 `hQ2` 消费 tail-fixed 形；PA14 现陈述已逐字匹配；不会再触发 SF。
- 消费者：PA17 `qzksykg2_p17`（:259）/`hQ2`（:847）。

### 3.8 GLTVHUM_concl（已绿）

- Lean：`lean/Kepler/Text/PackingAuto2.lean:3462`；文件 5887 行。
- 陈述：
  ```lean
  theorem GLTVHUM_concl : ∀ (V : Set V3) (u0 p : V3), Packing V ∧ saturated V → u0 ∈ V →
      (p ∈ voronoiClosed V u0 ↔
        ∃ vl : List V3, barV V 3 vl ∧ p ∈ rogers V vl ∧ truncateSimplex 0 vl = [u0])
  ```
- HOL：`pack_concl.hl:17-19`；Rogers.hl:1152。
- 状态：`#print axioms` 三零；PA6:1265 twin。
- 风险：无。stage2 的覆盖闭合依赖它。

### 3.9 DUUNHOR_concl（已绿但前提加强）

- Lean：`lean/Kepler/Text/PackingAuto2.lean:3504`；文件 5887 行。
- 陈述：
  ```lean
  theorem DUUNHOR_concl : ∀ (V : Set V3) (ul vl : List V3), Packing V → saturated V →
      barV V 3 ul → barV V 3 vl → rogers V ul ≠ rogers V vl →
      Coplanar (rogers V ul ∩ rogers V vl)
  ```
- HOL：`pack_concl.hl:21-23`；Rogers.hl:1682。
- 状态：`#print axioms` 三零；PA6:1776 twin。
- **保真缺口**：HOL 的 `DUUNHOR_concl` 没有 `packing V`/`saturated V` 前提，Lean 版多了这两个前提（更弱陈述）。对 PA17 stage3 足够（那里 hs/hp 在册），但**不是逐字 pack_concl 接口**；若下游要 HOL 原式，需要另证无 `hp/hs` 版或证明它们可去。
- 风险：无 sorryAx；只是接口强度注记。

### 3.10 MEASURE_NEGLIGIBLE_SYMDIFF（替身已绿，弱形）

- HOL 原文：`reference/flyspeck/azure/hol-light-nat/Multivariate/measure1.ml:550`：
  ```hol
  let MEASURE_NEGLIGIBLE_SYMDIFF = prove
   (`!s t:real^N->bool.
          negligible(s DIFF t UNION t DIFF s) ==> measure s = measure t`, ...)
  ```
- Lean 无同名定理；PA17:297 提供：
  ```lean
  private theorem p17_measure_sdiff_ge {s t : Set V3} (ht : volume t = 0) :
      volume s ≤ volume (s \ t)
  ```
- 用途：PA17 stage5 只需 `volume S4 ≤ volume (S4 \ Z)` 以保正测；不需要等号。因此**无需 SF**；但若下游需要完整 symdiff 等号，需要新增一个 `measure_sdiff_eq_of_null` 件。
- 风险：无。

### 3.11 隐藏叶与支撑叶

| 件 | 文件:行 | 作用 | 备注 |
|---|---|---|---|
| MCELL_2_PROPERTIES_lemma1 | PA10:703/707 | BOUNDED_MCELL k=2 | 300 行 URRPHBZ1 几何；`INTER_RCONE_GE_LE_lemma` 为其前置 |
| measurableSet_affGe_wedge_p10 | PA10:831/833 | MEASURABLE_MCELL k=2 | `affGe {u0,u1} {p,q}` 可测；建议走 cone 参数化 |
| INTER_RCONE_GE_LE_lemma | PA10:689/695 | MCELL_2 前置 | 300 行菱形比较；可用 `SIMPLEX_FURTHEST_LT_2`（PA11:162，已证） |
| YIFVQDV_1 | PA7:2697/2701 | QZKSYKG1 k=4 | HOL Rogers.hl:8777-9116 |
| WQPRRDY | PA7:2994/2999 | QZKSYKG2 k=3/4 | HOL Rogers.hl:10534-10872 |
| NJIUTIU | PA9:339/350 | TEZFFSK 前置 | 需 `CONVEX_HULL_EQ_EQ_SET_EQ` + closest-point descent |
| TEZFFSK | PA9:367/388 | DDZUPHJ k=4/3/2/1 | 前置已证，只剩 vertex identification |
| ROGERS_INTER_V_LEMMA | PA12:878 / PA11:418 | DDZUPHJ k=1 | 可用 GLTVHUM + omega-within-2 |
| CONVEX_HULL_EQ_EQ_SET_EQ | PA5:154/155 | NJIUTIU | Mathlib 仿射独立 hull 单射性；可先证 |
| YNHYJIT | PA10:590/604,608; PA14:712/766 | QZKSYKG1/2 | i=2 已由 01-kit 覆盖；i=3 由 S₃ kit 覆盖；可绕开 |

---

## 4. 切批处方（按依赖序，每子批 ≤500 行 Lean）

> 记号：每批给出「输入陈述（Lean 原文）→ 输出陈述」。对于填 `sorry` 的件，输入陈述 = 现有 theorem signature，输出 = 同一 signature 的无 sorry 证明体。对于新件，输入 = 新增陈述，输出 = 该陈述的证明。
>
> 「轮数」是 agent 工作轮估计（一轮约一个 500 行子批 + 编译修正），不是小时。

### 批 B1：S₃ action kit（LEFT_ACTION_LIST_PROPERTIES）

- 依赖前置：无（可立即开工）。
- 建议落点：`PackingAuto12.lean`（PA12 已 import PA6/7/8/10/11，且有 `MXI_EXPLICIT`/`VORONOI_LIST_3_SINGLETON_EXPLICIT`；PA13/PA14 都能消费）。
- 输入陈述（新增，**需 SF**）：
  ```lean
  theorem LEFT_ACTION_LIST_PROPERTIES {V : Set V3} {ul xl : List V3} {p : Equiv.Perm ℕ}
      (hpack : Packing V) (hsat : saturated V) (hbar : barV V 3 ul)
      (h1 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
      (h2 : Real.sqrt 2 ≤ hl ul)
      (hperm : permutes p (Set.Icc 0 2))
      (hfix : ∀ j : ℕ, 3 ≤ j → p j = j)
      (hxl : xl = leftActionList p ul) :
      barV V 3 xl ∧
        omegaListN V xl 2 = omegaListN V ul 2 ∧
        omegaListN V xl 3 = omegaListN V ul 3 ∧
        mxi V xl = mxi V ul
  ```
- 输出：上述定理（无 sorry）。
- 在册可用载体：
  - `BARV_3_EXPLICIT` PA8:210；`TRUNCATE_SIMPLEX_BARV` PA5:1381；`BARV_SUBSET` PA5:1285；`BARV_IMP_LENGTH_EQ_CARD` PA7:1316；
  - `EL_LEFT_ACTION_LIST` PA5:1152；`SET_OF_LIST_LEFT_ACTION_LIST` PA5:1184；`MEM_LEFT_ACTION_LIST` PA5:1169；
  - `OMEGA_LIST_1_EXPLICIT_NEW` PA12:1436；`OMEGA_LIST_2_EXPLICIT` PA8:174；
  - `VORONOI_LIST_3_SINGLETON_EXPLICIT` PA12:1682；`MXI_EXPLICIT` PA12:1958；
  - `MHFTTZN3` PA6:3109；`MHFTTZN4` PA6:3163；`HL_PROPERTIES` PA7:1621；
  - `LEFT_ACTION_LIST_1_PROPERTIES_ALT` PA14:792（S₂ 情形，可作 case 模板；注意 PA14 在 PA12 之后，不能反向 import；模板可复制）。
- 建议新私件：
  - `s3_permutes_cases`：`p permutes Icc 0 2` + `hfix` → p 是 `{0,1,2}` 上的六种排列之一；
  - `leftActionList_trunc2_set`：`setOfList (truncateSimplex 2 (leftActionList p ul)) = setOfList (truncateSimplex 2 ul)`；
  - `kyPermutes23`：`permutes p (Icc 0 2) → permutes p (Icc 0 3)`（HOL `KY_PERMUTES_2_PERMUTES_3`，未移植）；
  - `memLeftActionList2` / `setOfListLeftActionList2`（HOL `MEM_LEFT_ACTION_LIST_2`/`SET_OF_LIST_LEFT_ACTION_LIST_2`，未移植）；
  - `omegaList2ExplicitNew`（HOL `OMEGA_LIST_2_EXPLICIT_NEW`，未移植）。
- 子批：
  - B1a：排列枚举 + `leftActionList` 显式形态 + `barV` 持久性（约 500 行）；
  - B1b：`omegaListN 2/3` 不变性（约 500 行）；
  - B1c：`mxi` 不变性 + 收口（约 300 行）。
- 雷区：
  - 弱 `permutes` 不含 tail-fixedness；没有 `hfix` 时 p 可把 index 3 的 `getD` junk 甩进 `leftActionList`，陈述为假。必须带 `hfix`。
  - 非初始对 `{u0,u2}`/`{u1,u2}` 的 `voronoiNondg` facet 维数是 HOL 证明的几何硬核（marchal2.hl:4460 的 ~1200 行）；不要假设 `mxi` 只依赖 `{ω₂,ω₃}` 的 hull；要按 HOL case 走。
  - `MXI_EXPLICIT` 需要 `hl (truncateSimplex 2 ul) < sqrt2` 与 `sqrt2 ≤ hl ul` 两个 regime 前提；与本批 h1/h2 完全匹配。
  - `PERMUTES_TRIVIAL`（PA5:135）是 sorry，禁止使用。
- 预计轮数：5-7 轮。

### 批 B2：RVFXZBU i=3 + YNHYJIT i=3

- 依赖前置：B1。
- **落点问题（必须先决策）**：
  - **方案 A（推荐，低改接）**：S₃ kit 落 PA12；在 PA14 新增 `RVFXZBU_p14`（完整 RVFXZBU 陈述）和 `ynhyjit_i3_p14`；PA17 的 `p17_ajripqn_of_tailfix` 把 `hRV` 的实参从 PA10 `RVFXZBU` 改为 `RVFXZBU_p14`（1 行）。PA10 源件保持 sorry，但不再在 AJRIPQN 的 axiom cone 中；记为 off-path orphan。
  - **方案 B（原地，成本高）**：把 S₃ kit 下移到 PA11/PA10。PA10 不 import PA12，因此需在 PA10/PA11 内重证 clean 版 `MXI_EXPLICIT`/`VORONOI_LIST_3_SINGLETON`（PA11 现有 `mxiExplicit` 消费 PA2 `MXI_EXISTS_concl`，带 sorryAx，不可直接用）。预计 +4-6 轮，且与 PA12 的证明重复。
- 输入陈述（方案 A 的 PA14 新件；与 PA10 原文逐字）：
  ```lean
  theorem RVFXZBU_p14 {V : Set V3} {ul : List V3} {i : ℕ} {p : Equiv.Perm ℕ}
      (hi : i ∈ ({0, 1, 2, 3, 4} : Set ℕ))
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hperm : permutes p (Set.Icc 0 (i - 1)))
      (hfix : ∀ j, i ≤ j → p j = j) :
      mcell i V (leftActionList p ul) = mcell i V ul

  theorem ynhyjit_i3_p14 {V : Set V3} {ul vl : List V3} {p : Equiv.Perm ℕ}
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (h1 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
      (h2 : Real.sqrt 2 ≤ hl ul)
      (hperm : permutes p (Set.Icc 0 2))
      (hfix : ∀ j : ℕ, 3 ≤ j → p j = j)
      (hvl : vl = leftActionList p ul) :
      barV V 3 vl ∧
        ∀ j : ℕ, 2 ≤ j → j ≤ 3 → omegaListN V vl j = omegaListN V ul j
  ```
- 输出：上述两件无 sorry；PA17 的 `hRV` 改接 1 行。
- 在册可用载体：B1 的 S₃ kit；`setOfList_leftActionList_fix_p10` PA10:130（可复制）；`TRUNCATE_SIMPLEX_EXPLICIT_2` PA5/PA8；`mcell`/`mcell3` 定义 PA2；`MCELL_EXPLICIT` PA12:623。
- 建议新私件：`setOfListTrun2LeftActionList`（HOL `SET_OF_LIST_TRUN2_LEFT_ACTION_LIST2`）；`mcell3_congr_of_perm`。
- 雷区：
  - i=3 的 `mcell3` 是 `if hcond then convexHull {u0,u1,u2,mxi} else ∅`；两条分支都要处理；
  - `mcell3` 的 `hl` 条件在置换下不变（`setOfList` 不变），但 `mxi` 不变性必须来自 B1；
  - 不要把 i=3 与 i=4 的 `setOfList` 论证混用：i=4 已证，i=3 需要 trunc2 的新件。
- 预计轮数：2 轮（方案 A）；方案 B 另加 4-6 轮。

### 批 B3：YIFVQDV_1 + QZKSYKG1

- 依赖前置：B1（QZKSYKG1 k=3）、B2（可选，若 QZKSYKG1 需要 YNHYJIT）；YIFVQDV_1 独立。
- 输入陈述：
  ```lean
  theorem YIFVQDV_1 (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ)
      (hV : Packing V) (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2)
      (hperm : permutes p (Set.Icc 0 k)) :
      barV V k (leftActionList p ul)

  theorem QZKSYKG1 {V : Set V3} {ul vl : List V3} {k : ℕ} {p : Equiv.Perm ℕ}
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) (hne : mcell k V ul ≠ ∅)
      (hperm : permutes p (Set.Icc 0 (k - 1)))
      (hfix : ∀ j : ℕ, k ≤ j → p j = j) (hvl : vl = leftActionList p ul) :
      barV V 3 vl
  ```
- 输出：两者无 sorry。
- 在册可用载体：
  - `YIFVQDV_lemma_aff_dim` PA7:2687、`BARV_AFFINE_INDEPENDENT` PA7:1291、`BARV_3_EXPLICIT` PA8:210、`BARV_IMP_LENGTH_EQ_CARD` PA7:1316、`AFFINE_INDEPENDENT_OMEGA_LIST_N` PA7:2763（sorry）、`ROGERS_EQ` PA7:2769；
  - QZKSYKG1：`MCELL_EXPLICIT` PA12:623、`YIFVQDV_1` 本批、`LEFT_ACTION_LIST_1_PROPERTIES_ALT` PA14:792、`MCELL2_PERMUTE_01` PA14:829、`p14_swap_pack` PA14:643、`eq_refl_of_fix_p10` PA10:168、`leftActionList_refl_p10` PA10:160、B1 S₃ kit。
- 建议新私件：`barV_fullPerm`（YIFVQDV_1 的 k=3 特化）、`mcell4_nonempty_iff_hl`（用 `EMNWUUS1`/`MCELL_EXPLICIT`）、`mcell3_nonempty_regime`、`mcell2_nonempty_regime`。
- 子批：
  - B3a：YIFVQDV_1（约 400 行）；
  - B3b：QZKSYKG1 k=0/1/4（约 150 行）；
  - B3c：QZKSYKG1 k=2/3（约 200 行）。
- 雷区：
  - `YIFVQDV_1` 在 k=3 时 `permutes p (Icc 0 3)` 覆盖整张 4 元表，`leftActionList` 不会读 junk；不要误加 `hfix`（加了也无害但非必需）。
  - `QZKSYKG1` k=4 的 `hne : mcell 4 V ul ≠ ∅` 要转成 `hl ul < sqrt2`（`MCELL_EXPLICIT` + `mcell4` 的 `if` 条件）。
  - k=0/1 不要用 `PERMUTES_TRIVIAL`（sorry）；用 `eq_refl_of_fix_p10`。
- 预计轮数：2-3 轮。

### 批 B4：WQPRRDY + QZKSYKG2 k=0/1/4

- 依赖前置：无（WQPRRDY 独立）；QZKSYKG2 k=4 只依赖 WQPRRDY。
- 输入陈述：
  ```lean
  theorem WQPRRDY (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
      (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
      convexHull ℝ (setOfList ul) =
        ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 k)})

  theorem QZKSYKG2 {V : Set V3} {ul : List V3} {k : ℕ}
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hk : k ∈ ({0, 1, 2, 3, 4} : Set ℕ)) :
      mcell k V ul ⊆
        ⋃₀ ((fun p => rogers V (leftActionList p ul)) ''
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧
            ∀ n : ℕ, k ≤ n → p n = n})
  ```
  （本批只填 WQPRRDY 全体 + QZKSYKG2 的 k=0/1/4 三条分支。）
- 输出：WQPRRDY 无 sorry；QZKSYKG2 的 k=0/1/4 分支证明（k=2/3 仍 sorry）。
- 在册可用载体：
  - `HL_PROPERTIES` PA7:1621；`SET_OF_LIST_LEFT_ACTION_LIST` PA5:1184；`BARV_3_EXPLICIT` PA8:210；`TRUNCATE_SIMPLEX_BARV` PA5:1381；`ROGERS_EXPLICIT` PA12:1906；`MCELL_EXPLICIT` PA12:623；
  - `mcell0`/`mcell1`/`mcell4` 定义 PA2；`EMNWUUS1` PA9:99（已绿）。
- 建议新私件：`wqprrdy_ind`（按 k 归纳；HOL Rogers.hl:10534 是 `INDUCT_TAC`）、`mcell4_subset_hull`、`mcell0_mcell1_subset_rogers`。
- 雷区：
  - WQPRRDY 的归纳步需要 `HL_PROPERTIES` 与 `set_of_list` 的置换不变性；注意 k 与 `ul.length = k+1` 的关系；
  - QZKSYKG2 k=4：`mcell4` 非空时 `hl ul < sqrt2`，`mcell4 = convexHull setOfList ul`；直接 WQPRRDY；空时 `mcell4 = ∅`，trivial；
  - k=0/1：`permutes p (Icc 0 (k-1))` 强制 p=refl（用 `eq_refl_of_fix_p10`，带尾固定）。
- 预计轮数：2-3 轮。

### 批 B5：QZKSYKG2 k=2/3

- 依赖前置：B1（k=3）、B4（WQPRRDY）。
- 输入陈述：同 QZKSYKG2 现有 signature。
- 输出：QZKSYKG2 剩余 k=2/k=3 分支；整件无 sorry。
- 在册可用载体：
  - k=3：B1 S₃ kit、WQPRRDY、`convexHull4Imp31` PA14:145、`MCELL_EXPLICIT` PA12:623、`TRUNCATE_SIMPLEX_BARV` PA5:1381、`ROGERS_EXPLICIT` PA12:1906；
  - k=2：`twoRearrangementLemma` PA14:100、`MCELL2_PERMUTE_01` PA14:829、`p14_swap_pack` PA14:643、`LEFT_ACTION_LIST_1_PROPERTIES_ALT` PA14:792、`ROGERS_EXPLICIT` PA12:1906、`OMEGA_LIST_1_EXPLICIT_NEW` PA12:1436、`MXI_EXPLICIT` PA12:1958、`MHFTTZN4` PA6:3163、`OMEGA_LIST_N_IN_VORONOI_LIST_GEN` PA6:1388、`AFF_GE_2_2` PA12:225、`CONVEX_HULL_SUBSET` PA8:322、`BARV_SUBSET` PA5:1285。
- 建议新私件：
  - `mcell3_subset_union_trunc2`（k=3）；
  - `mcell2_subset_rogers_pair`（k=2：mcell2 ⊆ rogers V ul ∪ rogers V [u1,u0,u2,u3]）；
  - `mcell2_rcone_cover`（长 rcone 代数）；
  - `mcell2_cover_of_two_rogers`。
- 子批（按 HOL 行段）：
  - B5a：k=3（约 300 行 Lean）；
  - B5b：k=2 前半（rcone/midpoint 设定，约 500 行）；
  - B5c：k=2 中段（MHFTTZN4/Pythagoras，约 500 行）；
  - B5d：k=2 收口（约 500 行）。
- 雷区：
  - k=2 的 HOL 1681 行不能压成「一行 TWO_REARRANGEMENT_LEMMA」；中间有大量 `rcone_ge` 不等式与 `MHFTTZN4` 投影。
  - `YNHYJIT` i=2 可从 `ynhyjit_p14` 的 i=2 分支抽取（已用 01-kit），不要调用 PA10 的整定理（带 i=3 sorry）。
  - k=3 的 WQPRRDY 调用对象是 `truncateSimplex 2 ul`（barV V 2），不是整表；`hl (truncateSimplex 2 ul) < sqrt2` 来自 mcell3 非空。
- 预计轮数：5-7 轮。

### 批 B6：DDZUPHJ 支撑链（NJIUTIU + TEZFFSK + ROGERS_INTER_V_LEMMA + CONVEX_HULL_EQ_EQ_SET_EQ）

- 依赖前置：无（可立即开工，与 B1 并行）。
- 输入陈述：
  ```lean
  theorem CONVEX_HULL_EQ_EQ_SET_EQ (s t : Set V3) (hs : ¬ affineDependent s)
      (ht : ¬ affineDependent t) : (convexHull ℝ s = convexHull ℝ t ↔ s = t)

  theorem NJIUTIU (V : Set V3) (ul vl : List V3) (hs : saturated V) (hP : Packing V)
      (hul : barV V 3 ul) (hvl : barV V 3 vl) (hrogers : rogers V ul = rogers V vl)
      (hdim : affDim (rogers V ul) = 3) :
      ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i

  theorem TEZFFSK (V : Set V3) (ul vl : List V3) (k : ℕ) (hs : saturated V)
      (hP : Packing V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
      (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3)
      (hk : k ≤ 3) (hlt : hl (truncateSimplex k ul) < Real.sqrt 2) :
      truncateSimplex k ul = truncateSimplex k vl

  theorem ROGERS_INTER_V_LEMMA (V : Set V3) (ul : List V3) (v : V3)
      (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
      (hv : v ∈ V) (hr : rogers V ul v) : v = hdV ul
  ```
- 输出：四件无 sorry。
- 在册可用载体：
  - `ROGERS_AFF_DIM_FULL` PA6:1549（已绿）；`ROGERS_EXPLICIT` PA12:1906；`CLOSEST_POINT_SUBSET_lemma` PA9:226；`CONVEX_VORONOI_LIST` PA5:2187；`CLOSED_VORONOI_LIST` PA5:2180；`WAUFCHE1/2` PA7:2431/2460；`XYOFCGX` PA7:1234；`HL_DECREASE` PA7:1671；`TRUNCATE_TRUNCATE_SIMPLEX` PA5:1440；`TRUNCATE_SIMPLEX_BARV` PA5:1381；`GLTVHUM_concl` PA2:3462；`OMEGA_LIST_IN_VORONOI_LIST` PA5:2296；`BARV_3_EXPLICIT` PA8:210；`BARV_IMP_LENGTH_EQ_CARD` PA7:1316。
- 建议新私件：`hull_inj_affineIndependent`（CONVEX_HULL_EQ_EQ 的 Mathlib 证明）、`njiutiu_hd_eq`、`njiutiu_omega_descent`、`tezffsk_vertex_eq`、`rogersInV_of_gltvhum`。
- 子批：
  - B6a：CONVEX_HULL_EQ_EQ_SET_EQ + NJIUTIU（约 500 行）；
  - B6b：TEZFFSK（约 450 行）；
  - B6c：ROGERS_INTER_V_LEMMA（约 150 行）。
- 雷区：
  - `CONVEX_HULL_EQ_EQ_SET_EQ` 是 PA5 的 direct sorry；不要假设 Mathlib 现成，需要仿射独立 + 极点论证。
  - NJIUTIU 的 `CONVEX_HULL_EQ_EQ` 步给 `HD ul = HD vl`，随后 closest-point descent 需要 `CLOSEST_POINT_SUBSET_lemma` + `CONVEX_VORONOI_LIST`/`CLOSED_VORONOI_LIST`；注意 `omegaListN` 的层级索引是 1..3，不要错位。
  - TEZFFSK 的 `hlt` 只对最后一个 truncation 给出；内部要用 `HL_DECREASE` + `TRUNCATE_TRUNCATE_SIMPLEX` 传播小性。
  - ROGERS_INTER_V_LEMMA 用 `GLTVHUM_concl` 的 `→` 方向（`p ∈ voronoiClosed V u0` 来自 `v ∈ rogers`）；注意 `truncateSimplex 0 vl = [u0]`。
- 预计轮数：4-6 轮。

### 批 B7：DDZUPHJ

- 依赖前置：B6；PA13 顶部加 `import Kepler.Text.PackingAuto9`。
- 输入陈述：DDZUPHJ 现有 signature（见 §3.5）。
- 输出：DDZUPHJ 无 sorry。
- 在册可用载体：B6 四件；`MCELL_EXPLICIT` PA12:623；`WAUFCHE1/2` PA7:2431/2460；`HD_TRUNCATE_SIMPLEX` PA5:1421；`OMEGA_LIST_LEMMA` PA5:2229；`BARV_IMP_LENGTH_EQ_CARD` PA7:1316；`TRUNCATE_SIMPLEX_EXPLICIT_1/2/3`；`RCONE_GT_EQ_EMPTY_LEMMA` PA13:387。
- 建议新私件：`ddzuphj_k4`、`ddzuphj_k3`、`ddzuphj_k2`、`ddzuphj_k1`、`ddzuphj_k0`。
- 子批：
  - B7a：k=4 + k=0（约 250 行）；
  - B7b：k=3 + k=2（约 400 行）；
  - B7c：k=1（约 200 行）。
- 雷区：
  - k=4：`TEZFFSK` 给 `truncate 3 ul = truncate 3 vl`，再用 `TRUNCATE_SIMPLEX_EXPLICIT_3` 得 `ul = vl`；注意 `truncateSimplex 3 ul = ul` 需要 `ul.length = 4`。
  - k=1：`HD ul = HD vl` 必须由 `ROGERS_INTER_V_LEMMA` 在公共 Rogers 单形上给出；`HD` 是 `hdV`。
  - k=0：`mcell0 = rogers \ ball`；两边 rogers 相同、ball 中心/半径相同（`HD` 相同 + `hl` 相同）；`hl` 相同来自 rogers 相同 + ROGERS_EXPLICIT。
  - `hk : k ≤ 4` 要做 `k=0..4` 的 `interval_cases`；不要漏 `k ≥ 4` 的 dispatch（`mcell k = mcell4`）。
- 预计轮数：2-3 轮。

### 批 B8：SLTSTLO2

- 依赖前置：无（SLTSTLO1 已绿；可立即开工，与 B1/B6 并行）。
- 输入陈述：SLTSTLO2 现有 signature（见 §3.3）。
- 输出：SLTSTLO2 无 sorry。
- 在册可用载体：`NULLSET_SPHERE` PA13:371；`SLTSTLO1` PA13:597；`MCELL_EXPLICIT` PA12:623；`EMNWUUS2` PA9:121；`XNHPWAB1-4` PA7；`ROGERS_EXPLICIT` PA12:1906；`CONVEX_HULL_4_SUBSET_AFF_GE_2_2`；`RCONE_GT_EQ_EMPTY_LEMMA` PA13:387；`p17_coplanar_null` PA17:330（可复制为私件）；Mathlib `Measure.addHaar_affineSubspace`、`Convex.addHaar_frontier`。
- 建议新私件：
  - `sltstlo2_Z`（B1..B7 定义）；
  - `nullset_rogers_frontier`；
  - `nullset_rcone_eq`（HOL `NEGLIGIBLE_RCONE_EQ`，本件最硬）；
  - `nullset_affine_hull_triple`；
  - `nullset_segment`；
  - `sltstlo2_unique_lowhl` / `_far` / `_cone_out` / `_cell1` / `_cell2` / `_cell3` / `_cell4`。
- 子批（按 HOL 行段）：
  - B8a：Z 定义 + 7 个 null 证明 + 存在性（582-686，约 500 行 Lean）；
  - B8b：`hl ul < sqrt2` + `dist(u0,p) ≥ sqrt2` 分支（687-1126，约 450 行）；
  - B8c：`rcone_gt`/`aff_ge` 外分支与 `j=0/1/2`（1127-1718，约 500 行）；
  - B8d：`j=2/3` 与 mcell2/3 重叠（1719-2632，约 500 行）；
  - B8e：mcell3/4 与最终收口（2633-3692，约 500 行）。
- 雷区：
  - `∃!` 包含存在性；不要只证唯一性，要显式调 `SLTSTLO1` 给 `∃ i`。
  - `Z` 是 7 个边界面的并；`NULLSET Z` 的证明顺序按 HOL 的 `NEGLIGIBLE_UNION` 嵌套，不要重排。
  - `B3 = rcone_eq ...` 的零测是唯一没有现成 Lean 载体的硬点；建议先做 `nullset_rcone_eq` 探针（可用“锥面是 2 维流形/可被可数张图覆盖”或球坐标参数化）。
  - PA13 的 docstring 说唯一性由 `RVFXZBU1` 杀死，与 HOL 不符；按 HOL 的 mcell case tree 走，不要去找 RVFXZBU1。
  - `mcell` 的 `if` 分派（`MCELL_EXPLICIT`）是 case tree 的核心；每个 `i` 都要展开到 `mcell0..mcell4`。
- 预计轮数：7-9 轮。

### 批 B9：PA10 可测/有界隐藏链

- 依赖前置：无（可立即开工，与 B1 并行；符合官方十二发波「PA10 可测链」顺序）。
- 输入陈述：
  ```lean
  theorem INTER_RCONE_GE_LE_lemma {a b p s : V3} {r : ℝ}
      (hab : ¬(a = b)) (hs : s = midpoint ℝ a b) (hr : 0 < r)
      (hpa : ¬(p = a)) (hpb : ¬(p = b)) (hinv : 1 / 2 ≤ r ^ 2)
      (hbet : betweenP10 (projPoint_p10 (b - a) (p - a) + a) a s)
      (hmem : p ∈ rconeGe a b r ∩ rconeGe b a r) :
      dist s p ≤ dist s a

  theorem MCELL_2_PROPERTIES_lemma1 {V : Set V3} {ul : List V3} {p : V3}
      (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
      (hp : p ∈ mcell2 V ul) :
      dist (midpoint ℝ (hdV ul) (hdV ul.tail)) p ≤ hl (truncateSimplex 1 ul)

  private theorem measurableSet_affGe_wedge_p10 (u0 u1 p q : V3) :
      MeasurableSet (affGe {u0, u1} {p, q})
  ```
- 输出：三件无 sorry；`BOUNDED_MCELL`/`MEASURABLE_MCELL` 的 `#print axioms` 转三零。
- 在册可用载体：`INTER_RCONE_GE_IMP_BETWEEN_PROJ_POINT` PA10:633（已证）；`SIMPLEX_FURTHEST_LT_2` PA11:162（已证）；`betweenP10`/`projPoint_p10` PA10 内部；`rconeGe` 定义 PA2；`Affsign` 定义；Mathlib 凸锥/可数并 Borel。
- 建议新私件：`rhombus_compare_p10`、`mcell2_cap_estimate_p10`、`affGe_cone_param`、`affGe_measurable_of_cone`.
- 子批：
  - B9a：INTER_RCONE_GE_LE_lemma（约 350 行）；
  - B9b：MCELL_2_PROPERTIES_lemma1（约 200 行）；
  - B9c：measurableSet_affGe_wedge_p10（约 150 行）。
- 雷区：
  - `INTER_RCONE_GE_LE_lemma` 的 HOL 证明是 300 行菱形比较；`SIMPLEX_FURTHEST_LT_2` 已是真证，但需要把 `between`/投影点与 `simplexFurthestLt2` 的 `‖·‖` 形式对齐。
  - `MCELL_2_PROPERTIES` 还要用 packing 的 `dist ≥ 2` 上界；注意 `hl (truncate 1 ul)` 的半径 regime 与 `mcell2` 的 `if` 条件一致。
  - `affGe` 可测不要走 `¬Collinear3`-gated closedness（PA10 docstring 已指出覆盖不全）；走 cone 参数化：`affGe {u0,u1} {p,q} = u0 + cone(u1-u0, p-u0, q-u0)`，用可数并的紧线性像。
- 预计轮数：3-4 轮。

---

## 5. 排序（贪心）

### 5.1 评分口径

- **U（解锁数）**：完成该批后，能直接消掉的 downstream 债务节点数（含支撑叶）。
- **C（成本）**：预计轮数。
- **V（下游价值）**：对 REUHADY1(d)/capstone 2 的直接贡献。
- 贪心指标：先按 U/C，再按 V；同分时优先「无前置、可立即开工」。

### 5.2 排序表

| 排名 | 批 | U | C | V | 说明 |
|---:|---|---:|---:|---|---|
| 1 | **B1 S₃ kit** | 4 | 5-7 | 极高 | 解锁 RVFXZBU i=3、YNHYJIT i=3、QZKSYKG1 k=3、QZKSYKG2 k=3；所有 S₃ 相关件的唯一前置 |
| 2 | **B9 PA10 可测链** | 3（隐藏根） | 3-4 | 高 | 关闭 BOUNDED/MEASURABLE 的 3 个叶；独立、便宜；也是官方十二发波 a) |
| 3 | **B2 RVFXZBU i=3** | 1（+YNHYJIT） | 2 | 高 | 收掉五阶段件之一（方案 A）；依赖 B1 |
| 4 | **B3 YIFVQDV_1 + QZKSYKG1** | 1 | 2-3 | 高 | 收掉五阶段件之一；依赖 B1 |
| 5 | **B6 DDZUPHJ 支撑链** | 0（支撑） | 4-6 | 中高 | 独立；为 B7 铺路；与 B1 可并行 |
| 6 | **B7 DDZUPHJ** | 1 | 2-3 | 高 | 收掉五阶段件之一；依赖 B6 |
| 7 | **B4 WQPRRDY + QZKSYKG2 k=0/1/4** | 0（部分） | 2-3 | 中 | WQPRRDY 是 QZKSYKG2 k=3/4 的前置；可先做 |
| 8 | **B5 QZKSYKG2 k=2/3** | 1 | 5-7 | 高 | 收掉五阶段件之一；依赖 B1/B4 |
| 9 | **B8 SLTSTLO2** | 1 | 7-9 | 高 | 收掉五阶段件之一；独立但最大；可最后做 |

### 5.3 推荐首批与备选

- **推荐首发：B1（S₃ action kit）**。
  - 理由：扇出最高（4 个节点），是 RVFXZBU/QZKSYKG1/QZKSYKG2 的共同前置；不先做它，后面三个件都无法收口。
  - 首个动作：在 PA12 落 `LEFT_ACTION_LIST_PROPERTIES` 陈述（带 `hfix`），先证 `barV` 持久性，再证 omega/mxi 不变性。
- **备选首发：B9（PA10 可测链）**。
  - 理由：独立、便宜、无前置；关闭 3 个隐藏叶；符合官方十二发波顺序 a)「PA10 可测链」。
  - 若只开一条 lane 且想先拿「可验证的小胜」，选 B9；若目标是尽快让五阶段件数量下降，选 B1。
- **并行建议**（若有多 lane）：
  - Lane 1：B1 → B2 → B3 → B4 → B5；
  - Lane 2：B9（独立）；
  - Lane 3：B6 → B7（独立）；
  - Lane 4：B8（独立但最重，可最后启动）。
- **不推荐的首发**：B8 SLTSTLO2。虽然它独立，但成本最高、且不解锁任何其他节点；先做它会拖慢五阶段件的整体收敛。

---

## 6. 陈述保真注记与 SF 专节

### 6.1 逐件保真表

| 件 | 陈述 vs HOL | 弱形/shim/缺口 | 需 SF？ |
|---|---|---|---|
| TIWWFYQ | 逐字 | 无 | 否 |
| SLTSTLO1 | 逐字 | 无 | 否 |
| SLTSTLO2 | 逐字（`∃ Z` 在 `∀ p` 外；`∃!` 含存在性） | 无 | 否 |
| RVFXZBU | 加 `hfix`（HOL complement-fixing） | 编码修正已应用（SF-20） | 否 |
| DDZUPHJ | `k ≤ 4` vs HOL `k IN {0..4}`；等价 | 无 | 否 |
| QZKSYKG1 | 加 `hfix`；`hvl` 逐字 | 编码修正已应用（SF-20） | 否 |
| QZKSYKG2 | comprehension 加 tail-fixed 合取项 | 编码修正已应用（SF-38）；符号化更强、对弱式可单调回退 | 否 |
| GLTVHUM_concl | 逐字 | 无 | 否 |
| DUUNHOR_concl | **前提加强**：Lean 多 `Packing V`/`saturated V` | 弱形接口；对 PA17 足够，但不是 pack_concl 逐字 | 否（对 AJRIPQN）；若要逐字接口需另处理 |
| MEASURE_NEGLIGIBLE_SYMDIFF | Lean 无同名件；`p17_measure_sdiff_ge` 只给不等式 | 替身弱形；用途足够 | 否 |
| YIFVQDV_1 | Lean 无 `saturated`；HOL 有 | 更强（少前提）；k=3 使用安全 | 否 |
| WQPRRDY | 逐字（Lean 无 `saturated`，HOL 也无） | 无 | 否 |
| NJIUTIU/TEZFFSK/ROGERS_INTER_V_LEMMA | 逐字 | 无 | 否 |
| LEFT_ACTION_LIST_PROPERTIES | **Lean 缺失**；HOL 用 complement-fixing `permutes 0..2` | 新陈述必须加 `hfix` | **是（新 SF）** |

### 6.2 SF-20 / SF-38 现状（已应用，无需重做）

- **SF-20**（QZKSYKG1 补 `hfix`）：已应用（PA14:902-908；PackingAuto2 `RVFXZBU3_concl` 同步带 `hfix`）。
- **SF-20 家族**（RVFXZBU/YNHYJIT 补 `hfix`）：已应用（PA10:413-419、PA10:590-597）。
- **SF-38**（QZKSYKG2 comprehension 补 `∧ ∀ n, k ≤ n → p n = n`）：已应用（PA14:945-951；PA17 `qzksykg2_p17` 同步透传，PA17:259-266）。
- 现状影响：QZKSYKG1/QZKSYKG2/RVFXZBU 的 weak-`permutes` caveat 已关闭；`p17_ajripqn_of_tailfix` 的 `hQ1/hQ2/hRV` 全部按 tail-fixed 形消费。

### 6.3 需要新 SF 的唯一一点：LEFT_ACTION_LIST_PROPERTIES 的 `hfix`

**HOL 原文**（marchal2.hl:4460-4474）：
```hol
let LEFT_ACTION_LIST_PROPERTIES = prove_by_refinement (
 `!V ul p. 
    packing V /\ saturated V /\ barV V 3 ul /\
    hl (truncate_simplex 2 ul) < sqrt (&2) /\ sqrt (&2) <= hl ul /\ 
    p permutes 0..2 /\ 
    xl = left_action_list p ul 
    ==> xl IN barV V 3 /\ 
        omega_list_n V xl 2 = omega_list_n V ul 2 /\
        omega_list_n V xl 3 = omega_list_n V ul 3 /\
        mxi V xl = mxi V ul`,
```

**HOL `permutes` 语义**（`reference/flyspeck/azure/hol-light-nat/Library/permutations.ml:9`）：
```ml
let permutes = new_definition
 `p permutes s <=> (!x. ~(x IN s) ==> p(x) = x) /\ (!y. ?!x. p x = y)`;;
```
即 complement-fixing：`p permutes 0..2` 自动固定所有 `j ≥ 3`。

**Lean 弱编码**（PA2:165）：
```lean
def permutes (p : Equiv.Perm ℕ) (s : Set ℕ) : Prop := ∀ x, x ∈ s ↔ p x ∈ s
```
不含尾固定。`leftActionList` 在本件读 index 3（`ul.length = 4`），所以弱 `permutes 0..2` 允许 p 把 index 3 换成 junk 点，陈述为假/不可证。

**建议 SF 文本**（新件，落在 PA12；编号建议取下一个空号，例如 SF-47，需编排者确认）：
```lean
theorem LEFT_ACTION_LIST_PROPERTIES {V : Set V3} {ul xl : List V3} {p : Equiv.Perm ℕ}
    (hpack : Packing V) (hsat : saturated V) (hbar : barV V 3 ul)
    (h1 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (h2 : Real.sqrt 2 ≤ hl ul)
    (hperm : permutes p (Set.Icc 0 2))
    (hfix : ∀ j : ℕ, 3 ≤ j → p j = j)
    (hxl : xl = leftActionList p ul) :
    barV V 3 xl ∧
      omegaListN V xl 2 = omegaListN V ul 2 ∧
      omegaListN V xl 3 = omegaListN V ul 3 ∧
      mxi V xl = mxi V ul
```
SF 理由：与 SF-20 同族（弱 `permutes` + 尾固定合成 HOL complement-fixing）；补后式 ⇒ 弱式（丢弃 `hfix` 即回退），无下游破坏。注意：本件是**新增定理**，不是修改已冻结陈述，所以是「新增件 + 编码修正」，风险低于改冻结接口。

### 6.4 其它注记（不是 SF）

- **DUUNHOR_concl 前提加强**：Lean 版多 `Packing V`/`saturated V`。这不是错误，但意味着它不是 `pack_concl.hl:21-23` 的逐字 discharge。若未来需要逐字接口，建议另立 `DUUNHOR_concl_verbatim`，不要直接改现有定理（会波及 PA6 twin/PA17 stage3）。
- **PA13 SLTSTLO2 docstring 的 RVFXZBU1 说法**：HOL SLTSTLO2 的唯一性证明没有调用 RVFXZBU1；它走的是 mcell case tree。实现者应按 HOL 原文，不要把 `RVFXZBU1` 当作前置；否则会误判依赖。
- **PA17 `qzksykg2_p17` 是 shim**：它转发 PA14 `QZKSYKG2`；PA14 body 落地后删除 `_p17` 副本（PA17:64-66 已记）。
- **PA2 `RVFXZBU3_concl` 仍 sorry**：它量化所有 i，PA10 的 twin 只覆盖 i∈{0..4}；PackingConcl:395-400 已记 twin mismatch。它不在 AJRIPQN 链上（PA17 用 PA10 的 RVFXZBU），不要把它计入本处方。

---

## 7. 侦察方法记录（复核用）

### 7.1 关键 grep 命令

```bash
# 文件规模
wc -l lean/Kepler/Text/PackingAuto{5,10,13,14,17}.lean lean/scripts/packing/AJRIPQN.hl

# 声明定位
grep -n "^theorem TIWWFYQ\|^theorem SLTSTLO1\|^theorem SLTSTLO2\|^theorem RVFXZBU\|^theorem DDZUPHJ\|^theorem QZKSYKG1\|^theorem QZKSYKG2" \
  lean/Kepler/Text/PackingAuto{5,10,13,14}.lean

# 实际 sorry 体
for f in PackingAuto5 PackingAuto7 PackingAuto9 PackingAuto10 PackingAuto11 PackingAuto13 PackingAuto14; do
  echo "=== $f ==="; grep -n "^[[:space:]]*sorry" lean/Kepler/Text/$f.lean; done

# import DAG
grep -n "^import" lean/Kepler/Text/PackingAuto{10,12,13,14}.lean

# 消费者
grep -rn "AJRIPQN" lean/Kepler/Text/*.lean | grep -v PackingAuto17
grep -rn "REUHADY1" lean/Kepler/Text/PackingAuto24.lean | head -20

# HOL 锚点
grep -n "let AJRIPQN_concl\|let SLTSTLO1_concl\|let SLTSTLO2_concl\|let RVFXZBU_concl\|let QZKSYKG1_concl\|let QZKSYKG2_concl\|let DDZUPHJ_concl" lean/scripts/packing/*.hl
grep -n "let LEFT_ACTION_LIST_PROPERTIES\|let YIFVQDV_1\|let WQPRRDY" lean/scripts/packing/*.hl
grep -n "let permutes" reference/flyspeck/azure/hol-light-nat/Library/permutations.ml
```

### 7.2 关键段落行号

- PA17 五阶段：`p17_stage1` :372、`p17_stage2` :420、`p17_stage3` :487、`p17_stage4` :626、`p17_stage5` :647、装配 :682、tailfix :827、AJRIPQN :929。
- HOL AJRIPQN 阶段界标：:100-244、:248-451、:457-732、:737-837、:842-896、:900-1048。
- SLTSTLO2 HOL：Z 定义 :584-597；null 证明 :600-686；存在性 :677-686；唯一性 :687-3692。
- QZKSYKG2 HOL case 界标：k=0/1 :328、k=4 :344、k=3 :358、k=2 :570。
- QZKSYKG1 HOL：concl :244、proof :266-320。
- RVFXZBU HOL：concl :32、proof :38-195；i=3 :160-195。
- DDZUPHJ HOL：concl :29-34、proof :59-608。
- S₃ kit HOL：marchal2.hl:4460-5662。
- YIFVQDV_1 HOL：Rogers.hl:8777-9116。
- WQPRRDY HOL：Rogers.hl:10534-10872。
- MEASURE_NEGLIGIBLE_SYMDIFF HOL：`reference/flyspeck/azure/hol-light-nat/Multivariate/measure1.ml:550`。

### 7.3 axiom 探针记录

见 `EVIDENCE.md` §3。关键结论：
- `AJRIPQN` = sorryAx；`TIWWFYQ`/`SLTSTLO1`/`GLTVHUM_concl`/`DUUNHOR_concl` = 三零；
- `SLTSTLO2`/`DDZUPHJ`/`RVFXZBU`/`QZKSYKG1`/`QZKSYKG2` = sorryAx；
- `BOUNDED_MCELL`/`MEASURABLE_MCELL` = sorryAx（隐藏链）；
- `LEFT_ACTION_LIST_1_PROPERTIES_ALT`/`MCELL2_PERMUTE_01`/`VORONOI_LIST_3_SINGLETON_EXPLICIT`/`ROGERS_EXPLICIT`/`MXI_EXPLICIT`/`WAUFCHE1/2`/`XNHPWAB1-4`/`EMNWUUS1/2`/`MHFTTZN1/3/4`/`XYOFCGX` = 三零。

---

## 8. 风险清单（按严重度）

1. **S₃ kit 的 import 落点**（高）：PA12 → PA10，PA10 不可 import PA12/PA14。推荐 PA12 + PA14 re-home + PA17 1 行改接；否则需在 PA10/PA11 重证 clean `MXI_EXPLICIT`/`VORONOI_LIST_3_SINGLETON`，成本 +4-6 轮。
2. **QZKSYKG2 k=2 的 1681 HOL 行**（高）：不是「WQPRRDY 一行」，而是长 rcone/midpoint 代数；切 3-4 子批。
3. **SLTSTLO2 的 `rcone_eq` 零测**（高）：Lean 无 `NEGLIGIBLE_RCONE_EQ`；需新几何测度论证。
4. **DDZUPHJ 的 `CONVEX_HULL_EQ_EQ_SET_EQ`**（中高）：PA5:155 direct sorry；NJIUTIU 的硬前置。
5. **PA13 不 import PA9**（中）：DDZUPHJ 批需加 import；无环，低风险。
6. **PA10 源件 RVFXZBU/YNHYJIT 仍是 sorry**（中）：方案 A 下成为 off-path orphan；需在 DEBT 记账，避免「AJRIPQN clean 但 PA10 仍 sorry」的误读。
7. **DUUNHOR_concl 前提加强**（低）：不影响 AJRIPQN，但影响 pack_concl 逐字账。
8. **文档过时**（低）：PA13:818 的 RVFXZBU1 说法、PA17:886-905 的旧「missing pieces」段、任务书的 TIWWFYQ/SLTSTLO1 行号；实现者以本报告/EVIDENCE 的当前树为准。

---

## 9. 建议的验收探针（每批完成后）

```bash
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
lake env lean --stdin <<'EOF'
import Kepler.Text.PackingAuto17
#print axioms Kepler.Text.SLTSTLO2
#print axioms Kepler.Text.DDZUPHJ
#print axioms Kepler.Text.RVFXZBU
#print axioms Kepler.Text.QZKSYKG1
#print axioms Kepler.Text.QZKSYKG2
#print axioms Kepler.Text.BOUNDED_MCELL
#print axioms Kepler.Text.MEASURABLE_MCELL
#print axioms Kepler.Text.AJRIPQN
EOF
```
- B1 后：新增 `LEFT_ACTION_LIST_PROPERTIES` 三零；
- B2 后：`RVFXZBU`（若方案 A，则 `RVFXZBU_p14`）三零；
- B3 后：`YIFVQDV_1`、`QZKSYKG1` 三零；
- B4/B5 后：`WQPRRDY`、`QZKSYKG2` 三零；
- B6/B7 后：`CONVEX_HULL_EQ_EQ_SET_EQ`、`NJIUTIU`、`TEZFFSK`、`ROGERS_INTER_V_LEMMA`、`DDZUPHJ` 三零；
- B8 后：`SLTSTLO2` 三零；
- B9 后：`INTER_RCONE_GE_LE_lemma`、`MCELL_2_PROPERTIES_lemma1`、`BOUNDED_MCELL`、`MEASURABLE_MCELL` 三零；
- 全部后：`AJRIPQN` 三零（这是最终验收）。

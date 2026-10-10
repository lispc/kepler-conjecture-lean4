# p24_exists_mcell_not_flat 完整填充路线图（2026-10-10，诚实收窄波产物）

> 盘面：PA24 零改动（HEAD 态）。本路线图纠正了原 docstring 处方三处实质错误，
> 给出分波执行顺序。预估总量 ~1000–1200 行 / 15 件互锁私件 / 30–40 轮编译迭代。

## 处方纠错（三处）

1. **k′-识别缺口已消失**：不需要 AJRIPQN。`HDTFNFZ`（PA10:257，已真证，PA24
   经 PA12→PA10→PA11 传递可见无需新 import）给 `¬nullSet X → VX V X = V ∩ X`，
   `{u0,u1} ∈ edgeX V X` 归结为 `u0, u1 ∈ X`，与参数表无关。
2. **候选胞不能一律 `mcell 3`**：真实分叉在 `r₄ := hl vl`：`r₄ < √2` 时只有
   `mcell 4 V vl` 非空；`r₄ ≥ √2` 才用 `mcell 3`（且 `r₃ := hl (truncateSimplex
   2 vl) < √2` 可证恒成立）。
3. **fan 不给叶三元组存在性**：`p24_voronoi_pair_split` 是集合等式，指标集可能
   为空。存在性自证：中点 `p ∈ voronoiList V [u0,u1]`（margin 论证，平行四边形
   恒等式 15–25 行私有重推）→ fan 等式右端并集非空抽出 `vl`。

## 已手工验证的数学路线（含数值核查）

记 `d2 = d/2`，`s = √(4−d2²) > √2`，`p` = 中点，`v = elV vl 2`，`w = elV vl 3`：

1. **margin**：`∀ w ∈ V∖{u0,u1}, ‖w−p‖ ≥ s` → `p ∈ S` → fan 抽叶列表。
2. **ω₁ 型事实**：`S ⊆ bis(u0,u1)` 平面内 `dist(u0,·)` 在 p 唯一最小 ⇒
   `omegaListN V vl 1 = p`。
3. **`r₃ ≥ √2` 不可能（B2 杀死，~130 行全初等）**：反设后用 kit
   `p24_cc_exists`/`p24_radV_extract`/`p24_tri_gamma` 得 `r₃² = d2² + w²`；
   三重点 `T ≠ ∅`（`BARV_IMP_VORONOI_LIST_NOT_EMPTY` + `TRUNCATE_SIMPLEX_BARV`），
   取 `x* ∈ T`：`w > 0` 支 `ξ*·v⊥ ≥ s|v⊥|` 与 Cauchy–Schwarz + `|ξ*| < s` 矛盾；
   `w < 0` 纯算术杀死（`(h+s)² ≤ 4` ⇒ `h ≤ 2−s` ⇒ `d > 2√(4−(2−s)²) > 2√2`
   与 `d < √8` 矛盾；数值：s=1.476 时右端 3.86 > 2.83）。
4. **情形 A（`r₄ < √2`，X := `mcell 4 V vl`）**：四点共面 ⇒ 胞单点 `a` 等距于
   四点 + `a ∈ Π_b` ⇒ 四点共圆（半径 `r₄ < √2`）+ pairwise ≥ 2 + W-楔代数
   （`|ξ₃−ξ₄|² < 2r₄² < 4`）矛盾 ⇒ 仿射独立 ⇒ 非平坦。
5. **情形 B（`r₄ ≥ √2`，X := `mcell 2` 或 `mcell 3`）**：对齐排除：`v⊥ ∥ cc⊥`
   迫 `cc = o₃`（外心唯一性，经 `p24_tri_gamma` 的 `2μh = h²+t²−dt`）⇒
   `r₄ = r₃ < √2` 矛盾。`mcell3` 非平坦还需 `ω₂, cc ∈ L_v`（支撑面引理）。
6. **收尾**：`HDTFNFZ` + `u0,u1 ∈ X` 给 `edgeX`；末位合取 `azim_eq_zero_iff` +
   `affGt_pair_iff` + zOf 复数坐标 kit 压成两顶点垂足同射线与线性无关矛盾。

## 剩余风险与体量

- **支撑面引理**（`T ⊆ L_v`）：`affDim(S∩H_v) = 1 + x ∈ relint S` 内球论证；
  x 落 ∂S 时走"有限约束集 F + 线段被有限线族覆盖"分情况（F 有限性经
  `DISCRETE_BOUNDED_IMP_FINITE`/`KIUMVTC`，PA5 真证）。约 150–200 行，全路线
  最脆弱件。
- **正体积工具**（仿射独立四点凸包体积 > 0）：repo 只有逆向（PA20 非共面⇒零
  体积）；需自建重心坐标球构造，约 80–120 行。

## 建议执行顺序（每件独立探针，最后一次性装配进 :3013）

margin+中点∈S+fan（3 件探针）→ B2 杀死（tri_gamma 直用，最稳）→ 情形 A 共圆
杀死 → 支撑面引理 → 情形 B 对齐杀死 → 正体积工具 → 装配 + azim 收尾。

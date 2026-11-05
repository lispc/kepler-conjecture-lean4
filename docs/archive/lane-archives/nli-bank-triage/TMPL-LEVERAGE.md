# B — 模板族杠杆评估（`nli-bank-triage`，HEAD `0abccb51`）

结论先说：**B2 的"证 `∀ i3 i4 …` 一次闭 16/22 条"不成立（不是逻辑不可能，而是没有杠杆）**。
下面逐条给证据。所有数字来自 `/tmp/nlibank/num/` 的浮点三角扫描（triage 用，非证明；见 EVIDENCE.md §6 的口径声明）。

---

## B1. 模板展开陈述（逐字，含全部超越函数）

### B1.1 `bank_QITNPEA1tmpl`（PA21:681；6 实例）

```lean
def bank_QITNPEA1tmpl (i3 i4 : ℕ) : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ,
    2 * hminus ≤ y1 → y1 ≤ 2 * hplus → 2 ≤ y2 → y2 ≤ 2 * hminus →
    bank_QITNPEA1lo i3 ≤ y3 → y3 ≤ bank_QITNPEA1hi i3 →
    bank_QITNPEA1lo i4 ≤ y4 → y4 ≤ bank_QITNPEA1hi i4 →
    2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun /
        (1 + bankGenMid i3 + bankGenMid i4) > 0.0057 ∨
      yOfX rad2X y1 y2 y3 y4 y5 y6 > 2
```
其中 `lo i = if i=0 then 2 else if i=1 then 2*hminus else 2*hplus`、
`hi i = if i=0 then 2*hminus else if i=1 then 2*hplus else √8`、`bankGenMid i = if i=1 then 1 else 0`。

**真实展开（超越函数全部在此）**：

```
gamma4fgcy y⃗ lmfun = volY − vol4f
  volY  = Real.sqrt (deltaX (y1²,…,y6²)) / 12
  vol4f = (2·mm1/π)·(solY(y1,y2,y3,y4,y5,y6) + solY(y1,y5,y6,y4,y2,y3)
                    + solY(y4,y5,y3,y1,y2,y6) + solY(y4,y2,y6,y1,y5,y3))
          − (8·mm2/π)·Σ_{6 项} lmfun(y_i/2)·dihY(…)
  solY  = dihY + dihY + dihY − π
  dihY  = dihXf(y1²,…,y6²) = π/2 + atn2 (Real.sqrt (4·x1·deltaX)) (−deltaX4)
  rad2X = rhoX/(4·deltaX) = [2(uv+uw+vw) − (u²+v²+w²)] / (4·deltaX)，u=x1x4, v=x2x5, w=x3x6
```
即：**每个实例都真含 `Real.sqrt` + `atn2`（arctan 两支）+ `π`**，与"无超越函数"无关。

### B1.2 `bank_ZTGIJCF4tmpl`（PA21:850；16 实例）

```lean
def bank_ZTGIJCF4tmpl (i3 i4 i5 i6 : ℕ) : Prop :=
  ∀ y1 … y6,
    2*hminus ≤ y1 → y1 ≤ 2*hplus → 2 ≤ y2 → y2 ≤ 2*hminus →
    bank_ZTGIJCF4lo i3 ≤ y3 → y3 ≤ bank_ZTGIJCF4hi i3 → … (i4,i5,i6 同) →
    gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun /
        (1 + bankGenMid i3 + bankGenMid i4 + bankGenMid i5 + bankGenMid i6) +
      (if 1 + mid i3 + mid i4 + mid i5 + mid i6 = 2 ∧ i4 = 1 then 1 else 0 : ℝ) * betaBumpLb >
      aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6 ∨
    yOfX rad2X y1 y2 y3 y4 y5 y6 > 2
```
`lo i = if i=0 then 2 else 2*hminus`、`hi i = if i=0 then 2*hminus else √8`、
`aSpine5 = 0.0560305`、`bSpine5 = −0.0445813`、`betaBumpLb = −0.005`（**负**）。

实例的 `def` 体只有 `bank_ZTGIJCF4tmpl a b c d` 一行（PA21:865-895），展开后同上；
`w = 1 + #{i_j = 1}`，`m = 1 ⟺ w = 2 ∧ i4 = 1`。逐实例 `(w,m)`：

| 实例 | w | m | 实例 | w | m |
|---|---:|---:|---|---:|---:|
| (1,1,1,1) | 5 | 0 | (0,1,1,1) | 4 | 0 |
| (1,1,1,0) | 4 | 0 | (0,1,1,0) | 3 | 0 |
| (1,1,0,1) | 4 | 0 | (0,1,0,1) | 3 | 0 |
| (1,1,0,0) | 3 | 0 | (0,1,0,0) | 2 | **1** |
| (1,0,1,1) | 4 | 0 | (0,0,1,1) | 3 | 0 |
| (1,0,1,0) | 3 | 0 | (0,0,1,0) | 2 | 0 |
| (1,0,0,1) | 3 | 0 | (0,0,0,1) | 2 | 0 |
| (1,0,0,0) | 2 | 0 | (0,0,0,0) | 1 | 0 |

### B1.3 其它模板族

`grep tmpl` 只在 PA21 命中这两族（`bank_QITNPEA1tmpl` :681、`bank_ZTGIJCF4tmpl` :850），
没有第三个模板族。`bankGenMid`/`bank_QITNPEA1lo/hi`/`bank_ZTGIJCF4lo/hi` 是共用的辅助 def。

---

## B2. `∀ i3 i4 …, bank_*tmpl …` 能一次闭几条？——**不能（无杠杆）**

### B2.1 逻辑上：`∀` 陈述是真的，而且可以合法写出来

- 对 `i ≥ 2`，`lo = 2*hminus`、`hi = √8`、`mid = 0`，模板仍是有意义的盒式命题，
  所以 `∀ i3 i4 i5 i6 : ℕ, bank_ZTGIJCF4tmpl i3 i4 i5 i6` 是一个**真命题**（不是语法陷阱）。
- 我把"全部可实现参数"枚举了一遍（盒类型 × w × m，其中 `m = 1 ⟹ w = 2`）：
  **48 个 (盒,w,m) 组合，64 角点上逐点检查"rad2 支 ∨ gamma4 支"——0 个失败**。
  即 `∀` 版本在角点上成立，没有被某个怪参数证伪。

### B2.2 但 `∀` 的难度 ≥ 最难实例，逐实例并不更省

关键点：`∀` 版本要求**并集盒**上成立，而并集盒严格大于任何单个实例盒：

| 族 | 并集盒（y 空间） | 并集盒角点 min `rad2X` | 单实例最好/最差角点 min |
|---|---|---:|---|
| ZTGIJCF4（16） | y1∈[2hm,2hp], y2∈[2,2hm], y3..y6∈[2,√8] | **1.674** | 2.165 / 1.674 |
| QITNPEA1（6） | y1∈[2hm,2hp], y2∈[2,2hm], y3,y4∈[2,√8], y5,y6∈[2,2hm] | **1.830** | 2.077 / 1.832 |

- 若有**一条** `rad2X > 2` 的并集盒引理，就能一次闭 16（或 6）；但 rad2 在最优点上就 **< 2**
  ⇒ 这条"便宜的"引理在数值上不成立（对应角点的 gamma4 支恰好为真，见下）。
- 剩下的唯一可能是一次证 `gamma4` 支的并集引理（w=1..5、m∈{0,1} 各档）。但
  `gamma4` 支的最紧余量在实例层面只有 **0.0042**（(0,0,0,0)/(0,0,0,1)/(1,0,0,0) 等，
  见 TRIAGE 的 est/notes），而 `∀` 版要在**更大**的盒上维持同一门槛 ⇒ **只会更难**。
  且它含 `volY`(√) + `vol4f`(arctan, π) —— 本库没有任何 gamma4f 下界资产（`grep` 无 `gamma4fgcy_pos` 类定理），
  这正是 53 条 NEEDS-CERT 的同一个核。
- `m` 项是 `−0.005`（负）：`(0,1,0,0)` 一档反而被 `m` 项削弱，`∀` 版必须同时覆盖它。

### B2.3 结论

**`∀` 模板路线不是杠杆：它的最紧一档至少与最紧实例同难，且要为"盒类型 × w × m"再乘一遍覆盖。**
16/22 条的"一次闭"在抽屉里没有廉价钥匙；能一次闭的只有已证明的 `rad2` 型（且只在 6/16 + 2/6 上成立）。
真正的杠杆不在这两个模板，而在 **`rad2X > 2` 的单条盒引理族**——见 D-LANDING / PURELEAN-LIST（潜在 11 条）。

---

## B3. 若逐实例做：最小工作量（纯 Lean 口径）

| 实例组 | 条数 | 结论支路 | 纯 Lean 可行性 | 单条估行数 |
|---|---:|---|---|---:|
| ZTGIJCF4 rad2-clean：(0,1,1,1),(1,0,1,0),(1,0,1,1),(1,1,0,1),(1,1,1,0),(1,1,1,1) | 6 | `rad2X>2` 整盒覆盖（角点 min 2.017–2.165） | **可行（纯代数）**，共享 1 族引理 | 300–500（首条含引理族 ~500，余 5 条各 ~80–150） |
| ZTGIJCF4 其余 | 10 | 部分角点 rad2≤2，必须 `gamma4/w` 支 | 不可（无 gamma4 资产） | — |
| QITNPEA1 (2,2),(2,1) | 2 | rad2 覆盖（2.077 / 2.011，后者仅 0.5% 余量） | 可行但紧 | 300–500 |
| QITNPEA1 (2,0),(1,2),(1,1),(1,0) | 4 | rad2 角点 1.943/1.985/1.914/1.832 ⇒ 死 | 不可 | — |

> 注：上表"可行"仅指**数学上纯初等**；盒上 `rhoX > 8·deltaX` 的最小值不在角点（`rhoX−8deltaX` 对 x1 的
> 二次系数是 `x4(8−x4) > 0`，**凸**），所以 BIXPCGWb 用的"单独凹 + 角点归约"不能直接复用，
> 需要另配单调性/配方论证。本波没有为任何一条 rad2 条出探针，故 TRIAGE 里它们全是 `UNKNOWN`。

# SIGNS2 — `nli-sign-scout2`：剩余 23 条银行的六偏导认证符号侦察

日期 2026-11-06；主仓 HEAD `5c28e52e`（`nli-sign-scout` 落库后）；**主仓 tracked/staged
零改动**，全部产物在本快照目录。对象 = 工作单 §1 的 23 条（B3 8 + B4 6 + B5 5 + B6 4），
切片逐字取自 `lean/Kepler/Text/PackingAuto21.lean`。

## 0. 一句话结论

**M = 4 / P = 19 / N = 0。** 与 B1+B2 的 `0/28/0` **不同**：这批不是整体不可做。

- **4 条 M**（六轴全定号 ⇒ 极小在顶点）：`QITNPEAv24003532128`、`TskGXSA`、
  `Cell3QZECFICwt0corner`、`Cell3QZECFICwt0sqrt8`。
- 其中 **2 条是可做量**：`TskGXSA`（顶点值 `+4.8583e−3`）与
  `Cell3QZECFICwt0sqrt8`（顶点值 `+3.7447e−3`）——各需 **1 次新求值 + 单调性证书**
  （按 scout 60–150 行/条口径）。
- `Cell3QZECFICwt0corner` 顶点值 `[−1.30e−8, +1.14e−8]`，被 `mm1/mm2` 的 `1e−7` 带
  卡死（需 ~`1e−9`），**当前常数不可判**。
- `QITNPEAv24003532128` 顶点值 `−1.8450e−1`：M 路线**证伪**第一析取项（不是闭合它）。
- 其余 **19 条 P**（至少一轴认证变号），其中 **k=1 的两条**：
  `Cell3QZECFICwt1`（轴 4）、`QITNPEA4003532128a`（轴 1）。

## 1. 方法（与 `nli-sign-scout` 同一套判据）

### 1.1 模型（`scripts/model2.py`）：一个实现、两个后端

前向 mode jet（值 + 六偏导），后端可切换：

- `MPB`（`mpmath.mp`, dps=30）与 `FB`（python float）：**只用于找 witness**；
- `IVB`（`mpmath.iv`, dps=60，定向舍入）：**认证用**。

所有初等量逐字转录 Lean 体：`deltaX/deltaX4`、`dihXf = π/2 + atan2(−Δ₄, √(4x₁Δ))`、
`solY`、`volY`、`gamma4fgcy = volY − (A·Σ₄solY − B·Σ₆ lmfun(y/2)dihY)`、
`gamma3f`（可带逐项权重 `mᵢ·lfun(yᵢ/2)`）、`solEulerXDivSqrtdelta`、
`dihXDivSqrtdeltaPosbranch`、`gamma3fXDivSqrtdelta`、`gamma23Full8X/Keep135X`、
`eta_y² = x₁x₂x₆/upsX`、`betaBumpForceY`、`asnFnhk`。

**模型校验**（`scripts/verify_model.py`，`logs/verify_model.out`）：23 条 × 每片随机点，
值 + 六轴中心差分 vs 独立 mpmath 直译（`scripts/direct.py`）：

```
total value checks 115, mismatches 0
```

**witness 独立复核**（`scripts/verify_witness2.py`，`logs/verify_witness.out`）：
126 个认证 witness 点，直接值函数的中心差分（h=1e−6）与 IVB 点区间：

```
witness FD rows 126, SIGN mismatches 0, max rel dev 4.26e-05, median 7.3e-08
```

（残差 ~4e−5 来自 `mm1/mm2` 的 `1e−7` 带在导数上的放大，不是模型误差。）

### 1.2 恒等式（`scripts/identities.py`，dps=40，全部逐位通过）

- `solEulerXDivSqrtdelta(x)·√Δ = solX(x)`；
- `dihXDivSqrtdeltaPosbranch(x)·√Δ = dihXf(x)` 当 `Δ₄>0`；
  当 `Δ₄<0` 时 = `(dihXf(x)−π)/√Δ`（"posbranch" 的名字来源）；
- `gamma3fXDivSqrtdelta(m;x)·√Δ = gamma3f(y₄,y₅,y₆;√2)`（`mᵢ·lfun` 权重，`mk456` 先置
  2 再旋转；顺序在 `direct.py` 里独立重写过）；
- GXSA 的 `1/12 − A·Σ₄solEuler + B·Σ₄ldih` 按字面求值（它**不等于** `gamma4/√Δ`，
  因为 `Δ₄<0` 的 `ldih` 带 π 修正）。

### 1.3 认证常数（沿用 scout，`certconst.py`）

π、√2、√8、`mm1∈[1.0120808,1.0120809]`、`mm2∈[0.02541450,0.02541451]`、
`A∈[0.6443106485,0.6443107122]`、`B∈[0.0647174928,0.0647175183]`；
`hminus ∈ 9.7e−29` 宽区间（`2hminus = 2.46350884418…`）。所有十进制常数先转成精确
有理数再做 iv 运算（`certconst.dec` 规则）。

### 1.4 分支与垃圾区（必须记住）

| 族 | 分支面 | 处理 |
|---|---|---|
| B3/B6 的 `gamma4fgcy` | `lmfun` 折点 `yᵢ = 2h0 = 2.52` | 按 `pieces.py` 在 2.52 切盒；片内 `lmfun` 一次式（左片 `−1/0.52`，右片 0） |
| `gamma23Full8X/Keep135X` | `h0cut y₁` 在 2.52 | 切 y₁；`m1∈{0,1}` |
| cell3 `gamma3fXDivSqrtdelta` | `h0cut y₄/y₅` 在 2.52 + `matan` 在 `Δ=0` | 切 2.52；`matan` 在 `|t|≤1/2` 用 Taylor 界，`Δ` 变号盒用两分支/Taylor 外壳（`jmatan_coarse`） |
| cell3/GXSA 的 `dihDiv` | `Δ₄ ≠ 0` | 所有盒内 `Δ₄<0` 严格（cell3 `[−28,−8]`，GXSA `[−64,−58]`），无奇点 |
| 全部 `dihY` | `Δ > 0` | 除 IXPOTPA/4003532128a 两条多项式银行外，所有盒 `Δ>0`（角落与抽样都 ≥2.5）；cell3 的 `Δ` 内部元组可变号，由 matan 分支处理 |

**gamma23 三兄弟的 junk 区**：`gamma3X` 内部的 `dih` 元组是 `(yₐ,√2,y_b,√2,y_c,√2)`
形状，当三个自由 y 都较大时 `Δ<0`。Lean 的 `Real.sqrt` 对负数返回 0，光滑模型在那里
不等于字面表达式。本波的处理：**所有 witness 只在 `Δ>0` 的点上取**（模型对 `Δ≤0`
直接拒绝），所以 P 判定有效；但**不对这三条做 M/全域值声明**（它们本来也都是 P）。

## 2. 六元组（23 条）

`±` = 认证变号（witness pair，IVB 点严格异号）；`+`/`-` = M 档认证定号；
`h+`/`h-` = sampled-hint（无变号 witness，但未做全域证书）；`0` = 结构恒零
（函数不依赖该坐标）。`k` = 认证变号轴数。

| # | bank | bucket | s1..s6 | k | class |
|---|---|---|---|---|---|
| 1 | `nliRestGLFVCVK4` | B3 | ± ± ± ± ± ± | 6 | P |
| 2 | `nliRestGLFVCVK4y4subcrit` | B3 | ± ± h+ ± ± ± | 5 | P |
| 3 | `nliRestGLFVCVK4y4supercrit` | B3 | ± h+ h+ ± h+ h+ | 2 | P |
| 4 | `nliRestGLFVCVK4a8328676778` | B3 | ± h+ h+ ± h+ h+ | 2 | P |
| 5 | `nliTskIYOUOBFsharpv2` | B3 | ± h+ h+ ± h+ h+ | 2 | P |
| 6 | `nliTskIYOUOBFsym` | B3 | ± ± ± ± ± ± | 6 | P |
| 7 | `nliTskRIBCYXUsym` | B3 | ± ± ± ± ± ± | 6 | P |
| 8 | `nliTskWKGUESBsym` | B3 | ± h+ h+ ± h+ h+ | 2 | P |
| 9 | `nliRestIXPOTPA` | B4 | ± h- h- ± h- h- | 2 | P |
| 10 | `nliRestTXQTPVC` | B4 | ± ± ± h+ ± ± | 5 | P |
| 11 | `nliRestQITNPEAv24003532128` | B4 | + + 0 0 0 + | 0 | **M** |
| 12 | `nliRestPEMKWU` | B4 | ± ± ± h- ± ± | 5 | P |
| 13 | `nliRestTEWNSCJ` | B4 | ± ± ± h- ± ± | 5 | P |
| 14 | `nliTskGXSA` | B4 | + + + + + + | 0 | **M** |
| 15 | `nliCell3QZECFICwt0` | B5 | 0 0 0 ± ± ± | 3 | P |
| 16 | `nliCell3QZECFICwt0corner` | B5 | 0 0 0 + + + | 0 | **M** |
| 17 | `nliCell3QZECFICwt0sqrt8` | B5 | 0 0 0 + + + | 0 | **M** |
| 18 | `nliCell3QZECFICwt1` | B5 | 0 0 0 ± h+ h+ | 1 | P |
| 19 | `nliCell3QZECFICwt2A` | B5 | 0 0 0 ± ± h+ | 2 | P |
| 20 | `nliRestQITNPEA4003532128a` | B6 | ± h+ h+ h- h+ h+ | 1 | P |
| 21 | `nliRestRQWUDDU` | B6 | h+ ± ± h+ ± ± | 4 | P |
| 22 | `nliRest1965189142a` | B6 | ± ± 0 0 0 0 | 2 | P |
| 23 | `nliTskXLLIPLS` | B6 | ± h+ h+ ± h+ h+ | 2 | P |

逐条 witness 坐标/区间见 `SIGNS2.tsv` 的 `notes` 列；认证轴数与 k 分布：

- `k=1: 2 条`，`k=2: 8 条`，`k=3: 1 条`，`k=4: 1 条`，`k=5: 4 条`，`k=6: 3 条`；
  合计 **63 个认证变号轴**。
- `±?` 没有出现：所有存的 witness 都在 IVB 下严格复核通过。

## 3. M 档（4 条）：顶点 + 值可用性

六轴全定号的认证方式：`gamma4/GXSA/cell3` 用**自适应区间分支定界**（每个子盒的梯度
区间整段同号；`NeedSplit` 触发二分；记录每个子盒的符号并核对全书同号），
`eta` 用**解析因式分解**（见下）。工作量：wt0corner 15 盒/轴，GXSA 7–1535 盒/轴，
wt0sqrt8 约 9.0k 盒/轴（`Δ=0` 曲面用 Taylor 外壳），eta 0 盒。

| bank | 自由轴 | 符号 | 极小顶点 | main(顶点)（IVB） | 现有值覆盖 | 判定 |
|---|---|---|---|---|---|---|
| `nliRestQITNPEAv24003532128` | y1,y2,y6 | +++ | `(2hmin, 2, 2, 2, 2, 2)` | **−1.845034e−1** | 不需新超越（有理式 + 9.7e−29 的 hminus） | 第一析取在极小点**为假**；M 路线不闭合 |
| `nliTskGXSA` | x1..x6 | ++++++ | `x=(7.84, 4, 4, 7.84, 4, 4)`（y=`(2.8,2,2,2.8,2,2)`） | **[+4.858267e−3, +4.858283e−3]** | 不在 `(2h0,2⁵)/(2hplus,2⁵)/(√8,2⁵)` 之列；需 1 次新求值 | **可用 1 次求值闭合** |
| `nliCell3QZECFICwt0corner` | y4,y5,y6 | +++ | `(1, 1, 1, 2, 2, 2)` | **[−1.3017e−8, +1.1384e−8]** | 需 1 次新求值 **且** `mm1/mm2` 收紧到 ~1e−9 | 当前常数**不可判**（值 ~1e−8 ≪ 常数带 1e−7） |
| `nliCell3QZECFICwt0sqrt8` | y4,y5,y6 | +++ | `(1, 1, 1, 2.6508, 2, 2)` | **[+3.744681e−3, +3.744697e−3]** | 需 1 次新求值 | **可用 1 次求值闭合** |

细节：

- **eta 的解析因式分解**（`scripts/final_certify.py:eta_factor_cert`）：
  `eta² = abc/U`，`a=y1²,b=y2²,c=y6²`，
  `U = −a²−b²−c²+2ac+2ab+2bc`，
  `∂/∂a = bc(a²−(b−c)²)/U²`，`∂/∂b = ac(b²−(a−c)²)/U²`，
  `∂/∂c = ab(c²−(a−b)²)/U²`。盒上区间界：
  `U∈[6.064, 175.41]`，`a²−(b−c)²∈[32.55, 53.66]`，
  `b²−(a−c)² = c²−(a−b)² ∈ [6.839, 36.83]`，全部严格正 ⇒ 三个自由轴严格增；
  y3,y4,y5 结构恒零。极小在 `(2hmin,2,2)`，值 `eta²−1.7956 = −0.1845034`。
- **wt0corner 的锐度**：顶点 `(1,1,1,2,2,2)` 处 `gamma3fXDivSqrtdelta = −1.53e−9`
  （mp, dps=60）；IVB 带 `A/B` 区间后为 `[−1.30e−8,+1.14e−8]`。也就是说这条银行的
  不等式**恰好压在零面上**，M 路线把它归约为"一次标量求值 + 常数精度"，而当前
  `mm1` 只到 1e−7（需要 ~1e−9）。
- **QITNPEAv2 的反向结论**：`eta²` 在盒上的最小值 `1.611 < 1.7956`，第一析取
  `eta_y y1 y2 y6² > 1.34²` 在顶点为假；M 路线证明的是第一析取的**否定**。
  银行的真值只能来自其余析取项（`eta_y y1 y3 y5²`、`rad2X<2`、`y2<y3/…`、
  `gamma23Full8X` 项）。

**现有值覆盖**：4 个 M 顶点**没有一个**等于 `(2h0,2⁵)`、`(2hplus,2⁵)`、`(√8,2⁵)`
三个 gamma4 角点（`wt0sqrt8` 的 `2.6508` 在 y4 位，不是 y1 位）；`2hminus` 角点可用
9.7e−29 区间自算，但只对 `QITNPEAv2` 有用（它的值是纯有理式，不需要新的 atan/sqrt 资产）。
⇒ “现成值直接推”的条数 = **0**。

## 4. P 档（19 条）

- 变号轴数分布见 §2；**63 个认证变号轴**。
- **k=1（两条，单列）**：
  - `nliCell3QZECFICwt1`：轴 4（y4）。`+` witness
    `y=(√2,√2,√2,2.4635,2.4635,2.4635)`，`∂₄=[+5.527e−3,+5.527e−3]`；`−` witness
    `y=(√2,√2,√2,2.6508,2,2)`，`∂₄=[−5.531e−2,−5.531e−2]`。沿 y4 的剖面在
    `2.55` 附近由 `+` 转 `−`（**内点**穿越，不是折点）；⇒ 不是顶点，仍需剖分。
  - `nliRestQITNPEA4003532128a`：轴 1（y1）。`+` witness
    `y=(2hmin,2.8284,√2,√2,√2,2.8284)`，`∂₁=+19.03`；`−` witness
    `y=(2hplus,2,√2,√2,√2,2)`，`∂₁=−32.09`（`Δ₄−25` 的导数在盒内两端异号）。
- 其余 17 条 k≥2；最坏的是 3 条 k=6（`GLFVCVK4`、`IYOUOBFsym`、`RIBCYXUsym`），
  剖分退路 ≥64 格/条。
- 三条 `gamma23`（`TXQTPVC`、`PEMKWU`、`TEWNSCJ`）的 witness 全部落在内部
  `Δ>0` 的光滑点；junk 区（Lean `sqrt(neg)=0`）不影响 P 判定，但会阻止任何
  全域值/单调性声明。

## 5. 战略结论

**这批不是"整体不可做"。** 与 B1+B2 的 `0/28` 相比，剩余 23 条里有 **4 条 M**，
其中 **2 条是干净可做量**：

1. **`nliTskGXSA`**：六轴全正（认证），顶点 `x=(7.84,4,4,7.84,4,4)`，
   值 `+4.8583e−3`（IVB 宽 1.6e−8）。需要：**1 次该顶点的 atan/sqrt 求值**
   （约 8 个 matan 参数） + 六轴单调性证书。按 60–150 行/条口径是 **60–150 行**；
   若把 B&B 的 1535 盒证书翻译成 Lean 区间证明，实际会更高（但结构简单：
   两轴各 ~1500 盒，其余各 7 盒）。
2. **`nliCell3QZECFICwt0sqrt8`**：y4,y5,y6 全正（认证，~9k 盒/轴，Taylor 外壳
   处理 `Δ=0`），顶点 `(1,1,1,2.6508,2,2)`，值 `+3.7447e−3`。需要：1 次
   `gamma3fXDivSqrtdelta` 求值（6 个 matan 参数）+ 单调性证书。**60–150 行**量级。

**1 条"差一点"**：`Cell3QZECFICwt0corner` 的顶点值 `~0±1.2e−8`，M 路线已经把它
归约为一次标量求值，但需要把 `mm1/mm2` 从 `1e−7` 收紧到 `~1e−9`（或直接用
`sol0/tau0` 的更高精度展开）。这是一条**常数工程**路线，不是新数学。

**1 条被 M 路线反证**：`QITNPEAv24003532128` 的第一析取在顶点为 `−0.1845`；
不要再在这条上做"顶点 + 求值"。

**19 条 P**：顶点路线死。k=2 的 8 条最粗的剖分退路也要 4 格/条（240–600 行/条），
k=5/6 的 7 条要 32–64 格（1.9k–9.6k 行/条），是证书农场的价。两条 k=1 的
（`Cell3QZECFICwt1`、`QITNPEA4003532128a`）虽然 k 小，但变号轴是**内点**穿越
（不是 scout 那批的折点极小），仍需至少 2 片 + 其余轴的全域证书，单条 150–300 行起。

**排期建议（按 scout 口径）**：先做 `TskGXSA` + `Cell3QZECFICwt0sqrt8`
（≈ 120–300 行 + 2 次标量求值）；`wt0corner` 挂"常数收紧"（≈ 1 次求值 +
`mm1/mm2` 到 1e−9；如果 `gamma4-val1e6` 的 sol0/tau0 能直接给更紧的 mm1，这条会
变便宜）；`QITNPEAv2` 转移到其余析取项；其余 19 条不做。

## 6. 复现

```bash
cd ~/c17_backup/lane_snapshots/nli-sign-scout2/scripts
python3 identities.py        # 4 条 x/y 恒等式（dps=40）
python3 verify_model.py      # jet 模型 vs 独立直译 + 中心差分（115 项 0 mismatch）
python3 scan_witness.py      # 23 条 × 6 轴 × 片：witness 搜索 + IVB 点复核
python3 verify_witness2.py   # witness 的直接值 FD 复核（126 行 0 符号不符）
python3 final_certify.py     # 4 条 M：B&B（gamma4/GXSA/cell3）+ eta 因式分解 + 顶点值
python3 make_report2.py      # 生成 ../SIGNS2.tsv
```

产物：`SIGNS2.tsv`（23 行）、`SIGNS2.md`（本文件）、`scripts/`、`logs/`
（`witness_scan.json`、`witness_scan.out`、`certify_m.json`、`certify_m.out`、
`verify_model.out`、`verify_witness.out`）。

## 7. 与 `nli-sign-scout` 的交叉核对

- 模型：本车道的 `gamma4_jet` 在 3 个点上与 scout 的 `banks_eval.gamma4_value_iv`
  （展开式 `volY + 8mm1 − AΣ₁₂dih + BΣ₆F·dih`）区间重叠（差 ≤1e−6，来自 A/B 带）。
- 常数：直接复用 `certconst.py`（π/mm1/mm2/A/B/hminus 9.7e−29）。
- 判据：同样是"片内 witness pair ⇒ P；六轴定号 ⇒ M；否则 N"，witness 同样用
  直接值函数 FD 复核（本波 126 行 0 mismatch）。
- 结论差异的原因：B1+B2 的盒子全是 `[2,2hmin]` 附近的"窄皮"，六轴几乎都变号；
  本批含 GXSA/WT0 两类**窄盒 + 解析单调**，所以出现了 4 条 M。

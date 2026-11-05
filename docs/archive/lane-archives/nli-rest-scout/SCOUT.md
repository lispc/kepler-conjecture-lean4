# SCOUT — nli-rest-scout（51 条剩余 nli 银行的角点侦察与排期）

HEAD `640605c5`，日期 2026-11-05。**只做侦察，不写证明、不改主仓、不编译 Lean。**

## 0. TL;DR

- **A/B/C/D = 11/26/1/13**（C 的判据见 §4：字面 64 角点 corner_fail = **0**，
  唯一 C 是 `nliRest1965189142a`，角点值不是真最小值、函数无凹/单调结构，必须内点论证）。
- **51/51 条在字面 64 角点上 corner_ok**；但 **41 条**的盒内含有 `lmfun` 的折点
  `y = 2·h0 = 2.52`，**24 条**的 kink-aware 角点余量比字面 64 角点小 10% 以上
  （最大缩水 43×，`BIXPCGW9455898160`：5.69e−3 → 1.31e−4）。**只用 64 角点会系统性高估余量。**
- 最薄 5 条（排除两条恰为 0 的 sharp 恒等式）：`GLFVCVK4`=2.41e-6, `QZECFICwt1`=4.51e-5, `QITNPEA3848804089`=7.97e-5, `RIBCYXUsym`=8.23e-5, `BIXPCGW9455898160`=0.000131；
  恰为 0 的两条非严格 sharp：`nliTskIYOUOBFsharpv2`, `nliCell3QZECFICwt0corner`。
- **A 档 11 条、合计估行 1130**（不含共享 kit；kit 另计 ~700–1,000 行）。
- 最该先开：**B1 = ZTGIJCF4×10 + QITNPEA1×4（模板批，14 条，8 A + 6 B）**，
  **B2 = 窄盒 gamma4 族×14（宽盒导数包络批，2 A + 12 B）**；两批共享 `G4D8/G4ENV/G4FEED/INT`，可并行。
- 按今天速度 3 条/波：**纯计数 17 波**；B1/B2 模板压缩后约 **11–12 波**（A 档 11 条约 4 波）。

## 1. 方法与可复现性

- 数值：`mpmath` 60 位十进制；`hminus` 由 `marchalQuartic h = lmfun h` 在 `[1.2,1.3)` 求根，
  `hminus = 1.2317544220903043901328677155…`（残差 < 1e−60）。
- 定义逐条镜像 `SphereKit.lean` / `IneqClosureDefs.lean` / `PackingAuto2.lean` /
  `PackingAuto20/21.lean`；Lean junk-value 语义显式实现：`Real.sqrt x = 0 (x<0)`、
  `a/0 = 0`、`Real.log x = 0 (x≤0)`。
- 定义正确性锚（全部通过）：`deltaX(4⁶)=128`、`deltaX4(4⁶)=16`、`rad2X(4⁶)=1.5`、
  `dihY(2⁶)=arccos(1/3)`、`etaY(2,2,2)=2/√3`、`gamma4fgcy(2⁶)=0`、
  `gamma4fgcy(√8,2⁵)=0`、`gamma3f(2,2,2,√2)=0`、`gamma3fDiv(1,1,1|1,1,1,4,4,4)=0`。
- 角点：每条枚举 `2^6=64` 个盒角点（退化轴重复计数）；析取逐支求 gap。
  **kink-aware 细化**：对每个含 `2.52` 的轴加 `{lo, 2.52, hi}`（`lmfun` 折点）；
  对 `h0cut` 不连续轴再加右极限 `2.52+1e−30`。这是边界分析，不是内点采样。
- 内点采样（1500 随机 + 3⁶ 网格，`hints.json`）**只作 hint-only**，不作为证据；
  唯一用它下结论的地方是 §4 的 C 档（它给出角点范式的反例：内点比所有角点低）。
- 脚本：`scripts/bankdefs.py`（定义）、`scripts/run_corners.py`（角点）、
  `scripts/hint_scan.py`（hint）、`scripts/make_tsv.py`、`scripts/make_md.py`。
  原始数据：`logs/corners.json`、`logs/hints.json`、`logs/corners.log`、`logs/hints.log`。
  复现：`cd scripts && python3 run_corners.py && python3 hint_scan.py && python3 make_tsv.py`。

## 2. S1 — 51 条逐条抽取

（`γ4` = `gamma4fgcy y1..y6 lmfun`；`γ23full` = `yOfX (gamma23Full8X (h0cut y1)) y`；
`γ23keep` = `yOfX (gamma23Keep135X (h0cut y1)) y`；`η126` = `eta_y y1 y2 y6`，
`η135` = `eta_y y1 y3 y5`；`ΔY`/`Δ4Y` = `deltaY`/`delta4Y`；`ΔX`/`Δ4X` = `deltaX`/`deltaX4`；
`rad2` = `yOfX rad2X y`；`dihY` = `dihY y1..y6`；`a5=0.0560305`，`b5=−0.0445813`，
`β_lb=−0.005`，`β_force=betaBumpForceY`，`mid i = 1 if i=1 else 0`，
`w = 1+Σmid`，`m = 1 iff w=2 ∧ i4=1`。）

| # | decl | bank def (PA21:line; Assembly line) | box | conclusion |
|---|------|-------------------------------|-----|------------|
| 1 | `nliRest1965189142a` | `bank_1965189142a`:437; 437 | y1[1,1.26]×y2[3,34]×y3[1,1]×y4[1,1]×y5[1,1]×y6[1,1] | 2π − 2·asnFnhk(x1,x2) > 0.591 − 0.0331·x2 + 0.506·lfun(x1) |
| 2 | `nliRestQITNPEA4003532128a` | `bank_QITNPEA4003532128a`:460; 460 | y1[2hmin,2hplus]×y2[2,√8]×y3[√2,√2]×y4[√2,√2]×y5[√2,√2]×y6[2,√8] | Δ4Y > 25 ∨ ΔY > 0.14 ∨ ΔY < 0 |
| 3 | `nliRestIXPOTPA` | `bank_IXPOTPA`:470; 470 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[√8,4hmin]×y5[2,2hmin]×y6[2,2hmin] | ΔY<0 ∨ Δ4Y>0 ∨ 4x1ΔX<3.07Δ4X² ∨ 4x1ΔX>6.45Δ4X² ∨ η126²>1.34² ∨ η135²>1.34² ∨ γ23full>0.0171 |
| 4 | `nliRestTXQTPVC` | `bank_TXQTPVC`:485; 485 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,√8]×y5[2,2hmin]×y6[2,2hmin] | γ23full>0.0171 ∨ rad2<2 ∨ dihY>2.089 ∨ dihY<1.946 ∨ η126²>1.34² ∨ η135²>1.34² |
| 5 | `nliRestQITNPEAv24003532128` | `bank_QITNPEAv24003532128`:506; 506 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,√8]×y5[2,2hmin]×y6[2,2hmin] | η126²>1.34² ∨ η135²>1.34² ∨ rad2<2 ∨ y2<y3 ∨ y2<y5 ∨ y2<y6 ∨ γ23full−0.00457511−0.00609451·dihY>0 |
| 6 | `nliRestPEMKWU` | `bank_PEMKWU`:518; 518 | y1[2hmin,2hplus]×y2[2,√8]×y3[2,2hmin]×y4[2,√8]×y5[2,2hmin]×y6[2,√8] | γ23keep > a5+b5·dihY ∨ rad2<2 ∨ dihY>1.074 ∨ η126²>2 ∨ η126²<1.34² ∨ η135²>1.34² |
| 7 | `nliRestTEWNSCJ` | `bank_TEWNSCJ`:531; 531 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,√8]×y5[2,2hmin]×y6[2,2hmin] | γ23full > a5+b5·dihY ∨ rad2<2 ∨ η126²>1.34² ∨ η135²>1.34² |
| 8 | `nliRestQITNPEA5400790175b` | `bank_QITNPEA5400790175b`:543; 543 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/2 + β_lb + γ3f(y1,y2,y6,√2) > 0.0057 ∨ rad2>2 ∨ η126²>1.34² |
| 9 | `nliRestQITNPEA5400790175a` | `bank_QITNPEA5400790175a`:553; 553 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/2 + β_lb > 0.0057 ∨ rad2>2 ∨ η126²<1.34² |
| 10 | `nliRestQITNPEA3848804089` | `bank_QITNPEA3848804089`:563; 563 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 − 0.161517 + 0.119482·dihY > 0 |
| 11 | `nliRestQITNPEA5814748276` | `bank_QITNPEA5814748276`:572; 572 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 − 0.00127562 + 0.00522841·dihY > 0 |
| 12 | `nliRestQITNPEA6206775865` | `bank_QITNPEA6206775865`:581; 581 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 + 0.0142852 − 0.00609451·dihY > 0 |
| 13 | `nliRestQITNPEA5653753305` | `bank_QITNPEA5653753305`:591; 591 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 + 0.0659 − 0.042·dihY > 0 |
| 14 | `nliRestBIXPCGW9455898160` | `bank_BIXPCGW9455898160`:601; 601 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 > −0.00569 |
| 15 | `nliRestFHBVYXZb` | `bank_FHBVYXZb`:619; 619 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 + γ3f(y1,y2,y6,√2) > 0 ∨ rad2>2 ∨ η126²>1.34² |
| 16 | `nliRestFHBVYXZa` | `bank_FHBVYXZa`:629; 629 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 > 0 ∨ rad2>2 ∨ η126²<1.34² |
| 17 | `nliRestFHBVYXZv2a` | `bank_FHBVYXZv2a`:638; 638 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4 > 0.0057 ∨ rad2>2 ∨ η135²<1.34² |
| 18 | `nliRestQITNPEA2134082733` | `bank_QITNPEA2134082733`:648; 648 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/2 + β_lb − 0.213849 + 0.119482·dihY > 0 ∨ rad2>2 |
| 19 | `nliRestQITNPEA1_2_0` | `bank_QITNPEA1_2_0`:696; 1570 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hplus,√8]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4/(1+mid2+mid0) > 0.0057 ∨ rad2>2 |
| 20 | `nliRestQITNPEA1_1_2` | `bank_QITNPEA1_1_2`:698; 1576 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hmin,2hplus]×y4[2hplus,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/(1+mid1+mid2) > 0.0057 ∨ rad2>2 |
| 21 | `nliRestQITNPEA1_1_1` | `bank_QITNPEA1_1_1`:700; 1582 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hmin,2hplus]×y4[2hmin,2hplus]×y5[2,2hmin]×y6[2,2hmin] | γ4/(1+mid1+mid1) > 0.0057 ∨ rad2>2 |
| 22 | `nliRestQITNPEA1_1_0` | `bank_QITNPEA1_1_0`:702; 1588 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hmin,2hplus]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4/(1+mid1+mid0) > 0.0057 ∨ rad2>2 |
| 23 | `nliRestQITNPEA9939613598` | `bank_QITNPEA9939613598`:711; 711 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hplus,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4 − 0.00457511 − 0.00609451·dihY > 0 ∨ rad2>2 |
| 24 | `nliRestBIXPCGW7274157868a` | `bank_BIXPCGW7274157868a`:722; 722 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hplus,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4 > 0.0057 ∨ dihY < 2.3 |
| 25 | `nliRestGLFVCVK4y4subcrit` | `bank_GLFVCVK4y4subcrit`:768; 768 | y1[2hmin,2hplus]×y2[2hmin,√8]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4/2 > 0.0057 ∨ η126²<1.34² ∨ rad2>2 |
| 26 | `nliRestGLFVCVK4y4supercrit` | `bank_GLFVCVK4y4supercrit`:778; 778 | y1[2hmin,2hplus]×y2[2,2h0]×y3[2,2hmin]×y4[2hplus,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/2 > 0.0057 ∨ η126²<1.34² ∨ rad2>2 |
| 27 | `nliRestGLFVCVK4y4crit` | `bank_GLFVCVK4y4crit`:788; 788 | y1[2hmin,2hplus]×y2[2hmin,2hplus]×y3[2,2hmin]×y4[2hmin,2hplus]×y5[2,2hmin]×y6[2,2hmin] | γ4/3 > 0.0057 ∨ η126²<1.34² ∨ rad2>2 |
| 28 | `nliRestGLFVCVK4a8328676778` | `bank_GLFVCVK4a8328676778`:798; 798 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,2hplus]×y5[2,2hmin]×y6[2,2hmin] | γ4/2 + β_force > 0 ∨ rad2>2 |
| 29 | `nliRestGLFVCVK4` | `bank_GLFVCVK4`:808; 808 | y1[2hmin,2hplus]×y2[2,√8]×y3[2,√8]×y4[2,√8]×y5[2,√8]×y6[2,√8] | γ4 > 0 ∨ norm2hh < (hplus−hminus)² ∨ rad2>2 |
| 30 | `nliRestZTGIJCF4_1_1_0_0` | `bank_ZTGIJCF4_1_1_0_0`:871; 1706 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hmin,√8]×y4[2hmin,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 31 | `nliRestZTGIJCF4_1_0_0_1` | `bank_ZTGIJCF4_1_0_0_1`:877; 1726 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hmin,√8]×y4[2,2hmin]×y5[2,2hmin]×y6[2hmin,√8] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 32 | `nliRestZTGIJCF4_1_0_0_0` | `bank_ZTGIJCF4_1_0_0_0`:879; 1732 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2hmin,√8]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 33 | `nliRestZTGIJCF4_0_1_1_0` | `bank_ZTGIJCF4_0_1_1_0`:883; 1745 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,√8]×y5[2hmin,√8]×y6[2,2hmin] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 34 | `nliRestZTGIJCF4_0_1_0_1` | `bank_ZTGIJCF4_0_1_0_1`:885; 1751 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,√8]×y5[2,2hmin]×y6[2hmin,√8] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 35 | `nliRestZTGIJCF4_0_1_0_0` | `bank_ZTGIJCF4_0_1_0_0`:887; 1757 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2hmin,√8]×y5[2,2hmin]×y6[2,2hmin] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 36 | `nliRestZTGIJCF4_0_0_1_1` | `bank_ZTGIJCF4_0_0_1_1`:889; 1763 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2hmin,√8]×y6[2hmin,√8] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 37 | `nliRestZTGIJCF4_0_0_1_0` | `bank_ZTGIJCF4_0_0_1_0`:891; 1769 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2hmin,√8]×y6[2,2hmin] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 38 | `nliRestZTGIJCF4_0_0_0_1` | `bank_ZTGIJCF4_0_0_0_1`:893; 1775 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2hmin,√8] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 39 | `nliRestZTGIJCF4_0_0_0_0` | `bank_ZTGIJCF4_0_0_0_0`:895; 1781 | y1[2hmin,2hplus]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | γ4/w + m·β_lb > a5+b5·dihY ∨ rad2>2 |
| 40 | `nliRestRQWUDDU` | `bank_RQWUDDU`:928; 928 | y1[2hmin,2hplus]×y2[2,√8]×y3[2,√8]×y4[2,√8]×y5[2,√8]×y6[2,√8] | dihY > 0.76 ∨ η126²>2 ∨ η135²>2 |
| 41 | `nliTskGXSA` | `bank_TSKAJXYGXSA`:268; 268 | x1[2.8²,8]×x2[4,2.01²]×x3[4,2.01²]×x4[2.8²,8]×x5[4,2.01²]×x6[4,2.01²] | 1/12 − (2mm1/π)ΣsolE + (8mm2/π)Σldih ≥ 0 ∨ ΔX < 0 |
| 42 | `nliTskIYOUOBFsharpv2` | `bank_TSKAJXYIYOUOBFsharpv2`:326; 326 | y1[2hplus,√8]×y2[2,2.001]×y3[2,2.001]×y4[2,2hmin]×y5[2,2.001]×y6[2,2.001] | 0 ≤ γ4 |
| 43 | `nliTskIYOUOBFsym` | `bank_TSKAJXYIYOUOBFsym`:334; 334 | y1[2hplus,√8]×y2[2.001,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | 0 ≤ γ4 ∨ y2<y3 ∨ y2<y5 ∨ y2<y6 |
| 44 | `nliTskRIBCYXUsym` | `bank_TSKAJXYRIBCYXUsym`:343; 343 | y1[2.001,2hmin]×y2[2,2hmin]×y3[2,2hmin]×y4[2,2hmin]×y5[2,2hmin]×y6[2,2hmin] | 0 < γ4 ∨ y1<y2 ∨ y1<y3 ∨ y1<y4 ∨ y1<y5 ∨ y1<y6 ∨ y2<y3 ∨ y2<y5 ∨ y2<y6 |
| 45 | `nliTskWKGUESBsym` | `bank_TSKAJXYWKGUESBsym`:316; 316 | y1[2hplus,√8]×y2[2.01,2hmin]×y3[2,2hmin]×y4[2hplus,√8]×y5[2,2hmin]×y6[2,2hmin] | 0 < γ4 ∨ y2<y3 ∨ y2<y5 ∨ y2<y6 ∨ y1<y4 |
| 46 | `nliTskXLLIPLS` | `bank_TSKAJXYXLLIPLS`:308; 308 | y1[2hplus,√8]×y2[2,2.01]×y3[2,2.01]×y4[2hplus,2.8]×y5[2,2.01]×y6[2,2.01] | 0 < γ4 |
| 47 | `nliCell3QZECFICwt0` | `bank_QZECFICwt0`:206; 206 | y1[1,1]×y2[1,1]×y3[1,1]×y4[2.01,2hmin]×y5[2,2hmin]×y6[2,2hmin] | 0 < γ3fDiv(1,1,1) |
| 48 | `nliCell3QZECFICwt0corner` | `bank_QZECFICwt0corner`:214; 214 | y1[1,1]×y2[1,1]×y3[1,1]×y4[2,2.01]×y5[2,2.01]×y6[2,2.01] | 0 ≤ γ3fDiv(1,1,1) |
| 49 | `nliCell3QZECFICwt0sqrt8` | `bank_QZECFICwt0sqrt8`:221; 221 | y1[1,1]×y2[1,1]×y3[1,1]×y4[2hplus,√8]×y5[2,2hmin]×y6[2,2hmin] | 0 < γ3fDiv(0,1,1) ∨ η456²>2 |
| 50 | `nliCell3QZECFICwt1` | `bank_QZECFICwt1`:230; 230 | y1[√2,√2]×y2[√2,√2]×y3[√2,√2]×y4[2hmin,2hplus]×y5[2,2hmin]×y6[2,2hmin] | γ3fDiv(h0cut y4,1,1) > 0.008·dih4D ∨ η456²>2 |
| 51 | `nliCell3QZECFICwt2A` | `bank_QZECFICwt2A`:241; 241 | y1[√2,√2]×y2[√2,√2]×y3[√2,√2]×y4[2hmin,√8]×y5[2hmin,√8]×y6[2,2hmin] | γ3fDiv(h0cut y4,h0cut y5,1)/2 > 0.008·dih4D ∨ η456²>2 |

## 3. S2 — 角点判决（全部 64 角点 + kink 细化）

三态：`corner_ok`（单支且 min>bound）/ `disj`（多支，逐角点取最大 gap）/ `corner_fail`（存在角点无支成立）。
**字面 64 角点：51/51 corner_ok，0 corner_fail。kink-aware 细化：仍 51/51 corner_ok，0 corner_fail。**
唯一余量恰为 0 的是两条非严格 `≥` 的 sharp 恒等式：`nliCell3QZECFICwt0corner`（γ3fDiv=0 at
`(1,1,1,2,2,2)`）与 `nliTskIYOUOBFsharpv2`（γ4=0 at `(√8,2⁵)`）。

**关键发现（kink）**：`lmfun` 在 `y=2.52` 折（左斜率 −1/0.26，右斜率 0，折点凸），
`gamma4fgcy` 的 `+(8mm2/π)·lmfun(y/2)·dihY` 项使它可在该面取到内部最小值。
字面 64 角点不包含 `y_i=2.52` 面，因此对 41 条含该面的银行，**64 角点余量不是真余量**。
最严重的缩水：`QITNPEAv24003532128` 8.07e−3→2.00e−4、`BIXPCGW9455898160` 5.69e−3→1.31e−4、
`QITNPEA9939613598` 6.89e−3→2.00e−4、`QITNPEA3848804089` 2.88e−3→7.97e−5、
`nliCell3QZECFICwt1` 9.13e−4→4.51e−5。**任何只按 64 角点排期的计划都会把约 7 条 B 误判成 A（3 条因 kink 缩水、4 条因需支切换）。**

| decl | literal64 | refined | best-uniform | disj | state | argmin |
|------|-----------|---------|--------------|------|-------|--------|
| `nliRest1965189142a` | 0.13908 | 0.13908 | 0.13908 | 0.13908 | corner_ok | (1.26,3,1,1,1,1) |
| `nliRestQITNPEA4003532128a` | 10.995 | 2.4889 | -18.161 | 2.4889 | disj | (2hplus,2,√2,√2,√2,2) |
| `nliRestIXPOTPA` | 0.14615 | 0.055607 | -0.0055056 | 0.055607 | disj | (2hmin,2hmin,2hmin,√8,2hmin,2hmin) |
| `nliRestTXQTPVC` | 0.03372 | 0.03372 | -0.0092945 | 0.03372 | disj | (2hmin,2hmin,2hmin,2,2hmin,2hmin) |
| `nliRestQITNPEAv24003532128` | 0.0080673 | 0.00019999 | -0.0027159 | 0.00019999 | disj | (2hmin,2hmin,2hmin,2,2hmin,2hmin) |
| `nliRestPEMKWU` | 0.092225 | 0.055607 | -0.010468 | 0.055607 | disj | (2hmin,√8,2hmin,2,2hmin,√8) |
| `nliRestTEWNSCJ` | 0.066847 | 0.059213 | -0.0047276 | 0.059213 | disj | (2hmin,2hmin,2hmin,2,2hmin,2hmin) |
| `nliRestQITNPEA5400790175b` | 0.011926 | 0.0020937 | 0.0020937 | 0.0020937 | disj | (2h0,2,2,2h0,2,2) |
| `nliRestQITNPEA5400790175a` | 0.012524 | 0.012524 | -0.0072693 | 0.012524 | disj | (2h0,2,2,2h0,2,2) |
| `nliRestQITNPEA3848804089` | 0.0028805 | 7.9676e-5 | 7.9676e-5 | 7.9676e-5 | corner_ok | (2h0,2,2,2,2,2) |
| `nliRestQITNPEA5814748276` | 0.006012 | 0.00048 | 0.00048 | 0.00048 | corner_ok | (2h0,2,2,2,2,2) |
| `nliRestQITNPEA6206775865` | 0.0053767 | 0.00020003 | 0.00020003 | 0.00020003 | corner_ok | (2h0,2,2,2,2,2) |
| `nliRestQITNPEA5653753305` | 0.0044934 | 0.001583 | 0.001583 | 0.001583 | corner_ok | (2h0,2,2,2,2,2) |
| `nliRestBIXPCGW9455898160` | 0.0056924 | 0.00013106 | 0.00013106 | 0.00013106 | corner_ok | (2h0,2,2,2,2,2) |
| `nliRestFHBVYXZb` | 0.013429 | 0.0038041 | 0.0038041 | 0.0038041 | disj | (2h0,2,2,2,2,2) |
| `nliRestFHBVYXZa` | 0.012524 | 0.012524 | -0.0055589 | 0.012524 | disj | (2h0,2,2,2,2,2) |
| `nliRestFHBVYXZv2a` | 0.012524 | 0.01129 | -0.011259 | 0.01129 | disj | (2h0,2,2,2,2,2) |
| `nliRestQITNPEA2134082733` | 0.0048996 | 0.0048996 | 0.0048996 | 0.0048996 | disj | (2hmin,2,2,2hmin,2hmin,2) |
| `nliRestQITNPEA1_2_0` | 0.019056 | 0.016282 | 0.016282 | 0.016282 | disj | (2h0,2,2hplus,2,2,2) |
| `nliRestQITNPEA1_1_2` | 0.035851 | 0.034969 | 0.034969 | 0.034969 | disj | (2h0,2,2hmin,2hplus,2,2) |
| `nliRestQITNPEA1_1_1` | 0.017392 | 0.016145 | 0.016145 | 0.016145 | disj | (2h0,2,2hmin,2h0,2,2) |
| `nliRestQITNPEA1_1_0` | 0.0044429 | 0.0012863 | 0.0012863 | 0.0012863 | disj | (2h0,2,2h0,2,2,2) |
| `nliRestQITNPEA9939613598` | 0.0068928 | 0.00019999 | 0.00019999 | 0.00019999 | disj | (2h0,2,2,√8,2,2) |
| `nliRestBIXPCGW7274157868a` | 0.021998 | 0.013026 | 0.011537 | 0.013026 | disj | (2h0,2,2,2hplus,2,2) |
| `nliRestGLFVCVK4y4subcrit` | 0.0044429 | 0.0012863 | 0.0012863 | 0.0012863 | disj | (2h0,2h0,2,2,2,2) |
| `nliRestGLFVCVK4y4supercrit` | 0.012524 | 0.012524 | 0.0029183 | 0.012524 | disj | (2h0,2,2,2hplus,2,2) |
| `nliRestGLFVCVK4y4crit` | 0.017392 | 0.016145 | 0.016145 | 0.016145 | disj | (2h0,2hmin,2,2h0,2,2) |
| `nliRestGLFVCVK4a8328676778` | 0.0077576 | 0.0034307 | 0.0034307 | 0.0034307 | disj | (2h0,2,2,2h0,2,2) |
| `nliRestGLFVCVK4` | 2.4128e-6 | 2.4128e-6 | -0.0055589 | 2.4128e-6 | disj | (2h0,2,2,2,2,2) |
| `nliRestZTGIJCF4_1_1_0_0` | 0.037623 | 0.036981 | 0.036981 | 0.036981 | disj | (2hmin,2,2h0,2hmin,2,2) |
| `nliRestZTGIJCF4_1_0_0_1` | 0.01339 | 0.0098985 | 0.0075389 | 0.0098985 | disj | (2hmin,2,√8,2,2,√8) |
| `nliRestZTGIJCF4_1_0_0_0` | 0.008332 | 0.005009 | 0.0035911 | 0.005009 | disj | (2h0,2,√8,2,2,2) |
| `nliRestZTGIJCF4_0_1_1_0` | 0.037623 | 0.036981 | 0.036981 | 0.036981 | disj | (2hmin,2,2,2hmin,2h0,2) |
| `nliRestZTGIJCF4_0_1_0_1` | 0.037623 | 0.036981 | 0.036981 | 0.036981 | disj | (2hmin,2,2,2hmin,2,2h0) |
| `nliRestZTGIJCF4_0_1_0_0` | 0.028282 | 0.026771 | 0.026771 | 0.026771 | disj | (2h0,2,2,2h0,2,2) |
| `nliRestZTGIJCF4_0_0_1_1` | 0.024342 | 0.024342 | 0.024342 | 0.024342 | disj | (2hmin,2,2,2,2hmin,2hmin) |
| `nliRestZTGIJCF4_0_0_1_0` | 0.008332 | 0.005009 | 0.0035911 | 0.005009 | disj | (2h0,2,2,2,√8,2) |
| `nliRestZTGIJCF4_0_0_0_1` | 0.008332 | 0.005009 | 0.0035911 | 0.005009 | disj | (2h0,2,2,2,2,√8) |
| `nliRestZTGIJCF4_0_0_0_0` | 0.0053712 | 0.00077991 | 0.00077991 | 0.00077991 | disj | (2h0,2,2,2,2,2) |
| `nliRestRQWUDDU` | 0.092225 | 0.092225 | -0.15357 | 0.092225 | disj | (2hmin,2,√8,2,2,√8) |
| `nliTskGXSA` | 0.0048583 | 0.0048583 | 0.0048583 | 0.0048583 | disj | (2.8²,4,4,2.8²,4,4) |
| `nliTskIYOUOBFsharpv2` | 7.7788e-62 | 7.7788e-62 | 7.7788e-62 | 7.7788e-62 | corner_ok | (√8,2,2,2,2,2) |
| `nliTskIYOUOBFsym` | 0.00013125 | 0.00013125 | 0.00013125 | 0.00013125 | disj | (√8,2.001,2,2,2,2) |
| `nliTskRIBCYXUsym` | 8.2338e-5 | 8.2338e-5 | 8.2338e-5 | 8.2338e-5 | disj | (2.001,2,2,2,2,2) |
| `nliTskWKGUESBsym` | 0.0085339 | 0.0085339 | 0.0085339 | 0.0085339 | disj | (√8,2.01,2,√8,2,2) |
| `nliTskXLLIPLS` | 0.015838 | 0.015838 | 0.015838 | 0.015838 | corner_ok | (√8,2,2,2.8,2,2) |
| `nliCell3QZECFICwt0` | 0.00017828 | 0.00017828 | 0.00017828 | 0.00017828 | corner_ok | (1,1,1,2.01,2,2) |
| `nliCell3QZECFICwt0corner` | -1.4585e-62 | -1.4585e-62 | -1.4585e-62 | -1.4585e-62 | corner_ok | (1,1,1,2,2,2) |
| `nliCell3QZECFICwt0sqrt8` | 0.0037447 | 0.0037447 | 0.0037447 | 0.0037447 | disj | (1,1,1,2hplus,2,2) |
| `nliCell3QZECFICwt1` | 0.00091251 | 4.5143e-5 | 4.5143e-5 | 4.5143e-5 | disj | (√2,√2,√2,2h0,2,2) |
| `nliCell3QZECFICwt2A` | 0.0033294 | 0.0032506 | -0.16052 | 0.0032506 | disj | (√2,√2,√2,√8,2h0,2) |

（`literal64`/`refined`/`disj` 均为「逐角点取各支 gap 的最大值，再对 64/细化角点取 min」；
`best-uniform` 为「单支在全部角点上的最小 gap 的最大值」——只有它 >0 时才能单支一致收口。
SCOUT.tsv 的 `min_corner/bound/margin` 同口径：`margin = min_corner − bound` 恒为最小 gap；
常数项可能已折进 gap（bound=0，如 `γ4/3−0.0057`）或单列（如 `γ4>0.0057` 记 bound=0.0057），
两种写法不改变 margin。）

## 4. S3 — 路线归类 A/B/C/D

判据（写死在这里，避免口径漂移）：

- **A**：存在**单支**在全部（kink-aware）角点上成立，且该支最小 gap ≥ 1e−2；
  结论对变量有（数值 hint 支持的）凹/单调归约，普通「角点精确 + 归约」即可，不需要 Bernstein。
- **B**：corner_ok，但最佳单支余量 < 1e−2（薄），或 ≥1e−2 只能靠**支切换**（rad2/eta 在 kink 面附近）。
  薄的位置与所需常数精度逐条列在 TSV 的 notes。
- **C**：角点范式不足——角点值不是真最小值、且无凹/单调归约，必须内点/2D 论证。
  字面 corner_fail = **0**；C = **1**（`nliRest1965189142a`）。
- **D**：结论不是 `gamma4fgcy` 角点族（`yOfX gamma23*` / `deltaY` / `solEuler` / `gamma3fDiv` /
  `asnFnhk` / `dihY`），需要各自的 kit，单列。

### A 档（11 条，合计估行 **1130**）

| decl | est_lines | risk | shared kit | note |
|------|-----------|------|-------------|------|
| `nliRestQITNPEA1_2_0` | 60 | 低 | TMPL+G4D8+INT | template i3=2,i4=0; uniform main margin 1.63e-2 |
| `nliRestQITNPEA1_1_2` | 60 | 低 | TMPL+G4D8+INT | template i3=1,i4=2; uniform 3.50e-2 |
| `nliRestQITNPEA1_1_1` | 60 | 低 | TMPL+G4D8+INT | template i3=i4=1; uniform 1.61e-2 |
| `nliRestBIXPCGW7274157868a` | 150 | 中 | G4D8+G4ENV+INT | kink y1=2.52; uniform main 1.15e-2; disj dihY<2.3 1.30e-2 |
| `nliRestGLFVCVK4y4crit` | 200 | 中 | G4D8+G4ENV+INT | 3 kink axes y1,y2,y4=2.52; uniform main 1.61e-2 |
| `nliRestZTGIJCF4_1_1_0_0` | 60 | 低 | TMPL+G4D8+INT | template; uniform 3.70e-2 |
| `nliRestZTGIJCF4_0_1_1_0` | 60 | 低 | TMPL+G4D8+INT | template; uniform 3.70e-2 |
| `nliRestZTGIJCF4_0_1_0_1` | 60 | 低 | TMPL+G4D8+INT | template; uniform 3.70e-2 |
| `nliRestZTGIJCF4_0_1_0_0` | 60 | 低 | TMPL+G4D8+INT | template; uniform 2.68e-2 |
| `nliRestZTGIJCF4_0_0_1_1` | 60 | 低 | TMPL+G4D8+INT | template; uniform 2.43e-2 |
| `nliTskXLLIPLS` | 300 | 中 | G4D8+G4ENV+INT | no kink; argmin (√8,2,2,2.8,2,2); margin 1.58e-2 |

A 档共享 kit：`TMPL`（ZTGIJCF4/QITNPEA1 参数化模板，~400 行）、`G4D8`（Gamma4Deriv8 六槽导数闭式，
已在库）、`G4ENV`（窄盒 `[4,4.004001]⁶` 包络，已在库；宽盒需扩 ~500 行）、
`INT`（`Kepler.Interval` 的 `IExpr/evalReal/monoCorner/checkPosTMHull`，14k 行已在库）。
**A 档合计 1,130 行 + 共享 kit ~700–1,000 行。**

### B 档（26 条）

`nliRestQITNPEA5400790175b`(300,中)、`nliRestQITNPEA5400790175a`(300,高)、`nliRestQITNPEA3848804089`(300,中)、`nliRestQITNPEA5814748276`(300,中)、`nliRestQITNPEA6206775865`(300,中)、`nliRestQITNPEA5653753305`(300,中)、`nliRestBIXPCGW9455898160`(300,中)、`nliRestFHBVYXZb`(300,中)、`nliRestFHBVYXZa`(300,高)、`nliRestFHBVYXZv2a`(300,高)、`nliRestQITNPEA2134082733`(300,中)、`nliRestQITNPEA1_1_0`(150,中)、`nliRestQITNPEA9939613598`(300,中)、`nliRestGLFVCVK4y4subcrit`(300,中)、`nliRestGLFVCVK4y4supercrit`(300,高)、`nliRestGLFVCVK4a8328676778`(300,中)、`nliRestGLFVCVK4`(500,高)、`nliRestZTGIJCF4_1_0_0_1`(150,中)、`nliRestZTGIJCF4_1_0_0_0`(150,中)、`nliRestZTGIJCF4_0_0_1_0`(150,中)、`nliRestZTGIJCF4_0_0_0_1`(150,中)、`nliRestZTGIJCF4_0_0_0_0`(150,中)、`nliTskIYOUOBFsharpv2`(500,高)、`nliTskIYOUOBFsym`(300,高)、`nliTskRIBCYXUsym`(150,中)、`nliTskWKGUESBsym`(300,中)

其中 4 条是「disj≥1e−2 但只能支切换」：`nliRestQITNPEA5400790175a`、`nliRestFHBVYXZa`、
`nliRestFHBVYXZv2a`、`nliRestGLFVCVK4y4supercrit`。其余 22 条是单支薄余量，
最薄 `nliRestGLFVCVK4`=2.41e−6（(2hplus,2⁵)，且无单支一致：main −5.6e−3、rad2 −0.33、norm2hh −3.43）。
B 档合计估行 **7150**（含薄常数/Bernstein；按 TSV 逐条）。

### C 档（1 条）

- `nliRest1965189142a`（`bank_1965189142a`，PA21:437，`asnFnhk`）。
  字面 64 角点 min = 0.13908 at `(1.26,3,1,1,1,1)`，但内点 hint（**hint-only**）在
  `(1.0248,5.3479)` 给出 **8.75e−3**；函数在 x1 上非单调（∂₁ 随 x2 变号），
  且 x1/x2 上都是凸的（无凹性）。⇒ 角点+凹性范式不能收口，需 2D 实分析/Bernstein。
  **代表就是它；字面 corner_fail 仍为 0。**

### D 档（13 条）

`nliRestQITNPEA4003532128a`(300,中)、`nliRestIXPOTPA`(500,高)、`nliRestTXQTPVC`(500,高)、`nliRestQITNPEAv24003532128`(500,高)、`nliRestPEMKWU`(500,高)、`nliRestTEWNSCJ`(500,高)、`nliRestRQWUDDU`(300,中)、`nliTskGXSA`(500,高)、`nliCell3QZECFICwt0`(300,高)、`nliCell3QZECFICwt0corner`(300,高)、`nliCell3QZECFICwt0sqrt8`(300,中)、`nliCell3QZECFICwt1`(500,高)、`nliCell3QZECFICwt2A`(500,高)

D 档合计估行 **5500**。其中最值得先做的是 `nliRestQITNPEA4003532128a`
（deltaY 三分支 `Δ4Y>25 ∨ ΔY>0.14 ∨ ΔY<0` 是干净的符号三分，内点余量 1.21）；
`nliRestRQWUDDU` 的 `dihY>0.76` 支在盒上不成立（min dihY=0.6064），
但 GCKBQEA 的 `gckbP` 机器可复用（把 0.606 的常数换成 0.76 后不成立，只能走 eta>2 支）。

## 5. S4 — 分批与并行度

### 第一批 B1（建议立刻开）：ZTGIJCF4×10 + QITNPEA1×4 = 14 条

- 共享 kit `TMPL`：把模板
  `gamma4fgcy/w + m·betaBumpLb − (aSpine5 + bSpine5·dihY)`（ZTGIJCF4）与
  `gamma4fgcy/w − 0.0057`（QITNPEA1）各写一条**参数化**的角点+归约引理，
  14 个实例按 `(i3,i4[,i5,i6])` 做有限情形 `norm_num`/角点表；
  rad2 支直接复用 `NB3/NB5` 的 `H = rhoX − 8·deltaX` 单调 kit。
- 组成：5 A（`ZTGIJCF4_1_1_0_0/0_1_1_0/0_1_0_1/0_1_0_0/0_0_1_1`）+ 3 A（`QITNPEA1_2_0/1_1_2/1_1_1`）
  + 6 B（`ZTGIJCF4_1_0_0_1/1_0_0_0/0_0_1_0/0_0_0_1/0_0_0_0`、`QITNPEA1_1_0`）。
- 估：模板 ~400 + 每实例 60–150 ≈ **1,200–1,800 行**；低/中风险。
- 为什么先开：14 条里 8 条 A，A 密度最高；一个模板覆盖 14 条；B 的 6 条同型，只差角点常数。

### 第二批 B2（可与 B1 并行）：窄盒 gamma4 族 ×14

- 对象：`QITNPEA5400790175b/a`、`QITNPEA3848804089`、`QITNPEA5814748276`、
  `QITNPEA6206775865`、`QITNPEA5653753305`、`BIXPCGW9455898160`、`FHBVYXZb/a/v2a`、
  `QITNPEA2134082733`、`QITNPEA9939613598` + 2 A：`BIXPCGW7274157868a`、`GLFVCVK4y4crit`。
- 共享 kit `G4ENV-WIDE`：把 `Gamma4Env/EnvAtoms/EnvNum` 的窄盒 `[4,4.004001]⁶`
  导数包络扩到 `[2hmin,2hplus]×[2,√8]⁵`（含 `2.52` 折点分片），
  加一个 `gamma4fgcy → IExpr` 编码器（`Kepler.Interval` 的 `evalReal/monoCorner`），
  角点证书按 refined 角点表发射。
- 估：共享 ~600–900 + 每 bank 150–300 ≈ **2,800–3,800 行**；中/高风险（薄常数）。
- 为什么第二：条数最多（14），覆盖 9 条薄余量 + 3 条支切换，
  且该包络同时解锁 GLFVCVK4 族与 tsk sharp 族。

### 其余批（B1/B2 之后）

- **B3**：GLFVCVK4 族 ×4 + tsk sharp ×4（`IYOUOBFsharpv2/sym`、`RIBCYXUsym`、`WKGUESBsym`）；
  共享 `G4SharpRoute/G4Sharp/G4Feed` + 2D Bernstein。8 条，~2,000 行。
- **B4**：gamma23 族 ×5（`IXPOTPA/TXQTPVC/QITNPEAv2/PEMKWU/TEWNSCJ`）+ `GXSA`；
  新 `G23`/`SOL` kit；6 条，~2,500 行。
- **B5**：QZECFIC cell3 ×5；新 `G3DIV` kit + `h0cut` 分片 + `eta456` 支；~1,500 行。
- **B6**：`QITNPEA4003532128a`、`RQWUDDU`、`1965189142a`；3 条一次性，~1,000 行。

**并行度**：B1 与 B2 互不依赖（模板 vs 宽盒包络），可同时开 2 条 lane；
B3/B4/B5 依赖各自 kit，可在 B2 的 `G4ENV-WIDE` 落地后并行；B6 独立。
按 3 条/波：A 档 11 条 ≈ 4 波；全部 51 条纯计数 17 波，模板压缩后 **~11–12 波**。

## 6. 风险与注意事项

1. **kink 面不是可选优化**：41/51 条的盒含 `y=2.52`；其中 24 条的 refined 余量 < 字面 64 角点的 90%。
   正式证明必须显式 split `y_i ≤ 2.52` / `y_i ≥ 2.52`（`lmfun` 折点），
   以及 `h0cut` 的 `y1=2.52` 右极限（`gamma23*`/`gamma3fDiv` 族）。
2. **thin 常数**：B 档 22 条单支薄余量中，最小 2.41e−6（`GLFVCVK4`）、7.97e−5（`3848804089`）、
   1.31e−4（`BIXPCGW9455898160`）。角点值是超越数（arctan/arcsin），不能用 `norm_num`；
   需要 `Kepler.Interval` 的 `evalReal` 区间证书（或 G4 证书）在足够精度下判定。
   `hminus` 的现有包络（1.2313664 / 1.23175）在薄角点上的影响 ≤ ~1e−6，不是瓶颈。
3. **支切换**：4 条 B 的 disj 余量只在 scattered 角点上由不同支取得（rad2/eta），
   区域不是半空间；需要按支做子区域划分，工作量高于普通 A。
4. **gamma4 的 `IExpr` 编码尚未在 `pipeline/interval` 落地**（grep 无 gamma4 支持）；
   B2 的 `INT` kit 需要新增编码器（atan2 的 ite 分支 + `matan`/`sqrt`）。
5. **hint-only 声明**：`hints.json` 的内点值只用于（a）给 C 档提供反例、
   （b）给凹/单调方向做提示。所有 A/B 判定以角点（含 kink 细化）数值为准。
6. **数值实现**：`gamma3fDiv`/`gamma23*` 的 `rotate` 参数顺序按 `IneqClosureDefs` 的
   `rfl` 锚逐条镜像；`gamma3fDiv(1,1,1|1,1,1,4,4,4)=0`、`gamma3f(2,2,2,√2)=0` 两个精确零
   同时验证了 rotate 与 `vol3f456` 的 `m4` 非对称（只有 y4 槽乘 m4）。

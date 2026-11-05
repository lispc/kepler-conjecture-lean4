# nliPackNonlinearRest 侦察报告

> 落库版说明（2026-10-22）：只读侦察产出；正本与证据在
> `~/c17_backup/lane_snapshots/nliscout/`。关键结论：59 个 `nliRest*` 源
> **全是证书型（b 类）**，不是 ID 清单，pipeline 是闸门；19 已解 / 22 无 case
> 模板 / 18 硬解。**rest 19 `BIXPCGW9455898160` 陈述反号**（HOL `> -0.00569`
> vs Lean `> +0.00569`），已立案 SF-49（待用户批准，未应用）。最大单件
> rest 9 `QITNPEA3725403817`（964,792 叶 / 2,775 分片）。

> 车道：nliPackNonlinearRest（只读，一瓦）
> 仓库：`/Users/zhangzhuo/repos/kepler-conjecture-lean4`
> 快照目录：`~/c17_backup/lane_snapshots/nliscout/`
> 日期：2026-10-22
> 口径：静态 proof-term 地图（`docs/e2e-reachability-map.tsv`）+ 源码逐条核对 + pipeline 产物 join。
> 标记约定：**【原文】** = 源码/文档字面；**【推断】** = 本报告据证据推断，未逐条实测。

---

## 0. 结论速览

1. **59 个 `nliRest*` 不是 ID 清单型。** 它们是 62 个 rest 叶减去 3 个已真闭合件；每个都是独立的
   具体非线性不等式命题 `bank_<idv>`。分类计数：**(a) 0 / (b) 59 / (c) 0 / (d) 0 / (e) 0**。
   (b) 内部再分：**b1 管道已闭合 19**（其中 2 个证书 Lean 源在库）、**b2 无 case 的模板族 22**、
   **b3 求解失败/超时 18**。没有死支，也没有可裁件——62 元合取的每一项都在最终证明项里被内核检查。
2. **证明结构极简**：`nliPackNonlinearRest : pack_nonlinear_rest` 是一个 62 元匿名构造子
   （`Assembly.lean:958-983`），无 tactic。它只挂在**分量 1/6** `pack_nonlinear_non_ox3q1h`
   的第四合取项；与其余五分量（`ox3q1hP25` / `main_nonlinear_terminal_v11` / `LpIneqs` /
   `PackIneqDefA` / `KcblrqcIneqDef`）**没有直接依赖**，只共享底层定义闭包与区间证书基建。
3. **车道判定：pipeline 是闸门，Lean 是收尾。** 59/59 都需要证书；其中 41 条属常规生产
   （19 条重发射 + 22 条连 case JSON 都还没有），18 条另需研究（其中 4 条是 residue16 真残余）。Lean 侧固定是 59 条 `evalReal` 粘合 + 端点嵌入 + 替换 `sorry`。
   **不存在把 59 条塞进 `CertifiedIneqHolds` 查表批量填的捷径**——目标命题不是
   `CertifiedIneqHolds id`，而是 `bank_*`。
4. **推荐首批**：
   - 两条车道都可用：**B 批（rest 10 + rest 62 + rest 1，共 139 叶证书）**，1 波 pipeline +
     1 个 Lean 批，解锁 3/59，最便宜。
   - 只有本机 Lean 车道（本机无 pipeline 工具链）：**A1 批（rest 20 `FWGKMBZ`）**，
     证书 Lean 源在库、粘合是一行多项式恒等式；605 分片 + Base 冷构建是唯一成本。
   - 备选：**A2 批（rest 9 `QITNPEA3725403817`）**，2,775 分片 + Base，964,792 叶，解锁最大单件。
5. **最大风险**：
   - **rest 19 `BIXPCGW9455898160` 陈疑假**：HOL 是 `gamma4fgcy … > -- #0.00569`
     （即 `> -0.00569`），Lean `bank_BIXPCGW9455898160` 写成 `> 0.00569`；pipeline case 的
     AST/RPN 也按 `-0.00569` 生成。**Lean 陈述强了 0.01138，证书永远粘不上**。先发 statement-fix。
   - 18 条硬解（4 条 residue16 + 14 条 92-prep 重做口径）；BIXPCGW 家族有 134,788 个 depth-8
     残留盒记录；MKFKQWU 级曾报 ≥10⁹ 叶。
   - 超越函数粘合（`dihY`/`etaY`/`gamma23Full8X`/`atn2` ite 编码）是 155 定义闭包的主体剩余，
     尚未自动化，单件成本可能远超 60 行估算。
   - 本机（macOS）没有 FLINT/Arb/dReal，也没有 `pipeline/tools/`；pipeline 车道必须发到
     Linux/G4 机。605/2,775 分片 + Base 证书在本机冷构建可能耗时数小时。

---

## 1. 对象与证明结构

### 1.1 60 秒版调用链

```
the_kepler_conjecture_from_interfaces            Assembly.lean:6243
  └ assembly nonlinearInequalities (linearProgrammingResults nonlinearInequalities)
      ├ nonlinearInequalities : TheNonlinearInequalities      Assembly.lean:6076
      │   = ⟨nliPackNonlinearNonOx3q1h, nliOx3q1h,
      │      nliMainNonlinearTerminalV11, nliLpIneqs,
      │      nliPackIneqDefA, nliKcblrqcIneqDef⟩
      └ nliPackNonlinearNonOx3q1h : pack_nonlinear_non_ox3q1h  Assembly.lean:1004
          = ⟨nliCell3Bank, nliTskBank, nliGrkBank, nliPackNonlinearRest⟩
              ├ nliCell3Bank : cell3_bank                 Assembly.lean:380  (7 源)
              ├ nliTskBank   : tsk_bank                   Assembly.lean:510  (8 源 open)
              ├ nliGrkBank   : grk_bank                   Assembly.lean:522  (0 源，真装配)
              └ nliPackNonlinearRest : pack_nonlinear_rest Assembly.lean:958 (59 源)
                    = 62 元显式构造，逐项 = PA21 `bank_*`
```

`TheNonlinearInequalities` 的六分量定义在 `Assembly.lean:261-263`：

```lean
def TheNonlinearInequalities : Prop :=
  pack_nonlinear_non_ox3q1h ∧ ox3q1hP25 ∧ main_nonlinear_terminal_v11 ∧ LpIneqs ∧
    PackIneqDefA ∧ KcblrqcIneqDef
```

`pack_nonlinear_non_ox3q1h` 的定义在 `PackingAuto21.lean:963-964`：

```lean
def pack_nonlinear_non_ox3q1h : Prop :=
  cell3_bank ∧ tsk_bank ∧ grk_bank ∧ pack_nonlinear_rest
```

`pack_nonlinear_rest` 的定义在 `PackingAuto21.lean:935`，是 62 条 `bank_*` 的显式合取
（顺序 = `IdLists.packNonlinearNonOx3q1hIds` 注册序去掉 19 条消费切片）。**原文如此。**

### 1.2 59 源如何被消费

- `nliPackNonlinearRest` 的证明体是 62 个**逐项引用**的匿名构造子：每个位置直接放一个
  `nliRest<Name>`，没有投影、没有 tactic、没有隐蔽链。**原文如此**（`Assembly.lean:958-983`）。
- 59 个 `nliRest*` 声明形如 `theorem nliRestX : bank_X := sorry`；类型是 PA21 的
  `def bank_X : Prop := ∀ y1…y6, 盒 → 结论`。它们是**叶子**：不再引用其它 `nliRest*`，
  彼此独立。**原文如此。**
- 与六分量的关系：只属于分量 1/6 的第四合取项。关闭 59 条只影响分量 1，不影响分量 2-6 的
  sorry 计数；但会直接减少主定理 e2e 债务 59 条。
- 共享前置（59 条全部共享）：
  - 常量 `hminus`/`hplus`/`h0`（`PackingAuto2.lean:436/463/473`）；
  - `bank_*` 定义（`PackingAuto21.lean:419-952`）；
  - 155 定义闭包（`Kepler.Text.IneqClosureDefs`、`SphereKit`、`PackingAuto20` 等）；
  - 区间证书基建（`Kepler.Interval.*`：`IExpr.evalReal`、`BBTree`/`BBTreeG`/`BBTreeD`、
    `bb_sound`/`bb_soundG`/`bb_sound_disj`）；
  - `hminus` 端点事实 `mi_hminus_prop : 1.2 ≤ hminus ∧ hminus < 1.3 ∧ …`
    （`PackingAuto21.lean:1887`，sorry-free）及 `mi_two_hminus_le_*` 族。
- 下游杠杆（不在 59 内，但受 59 阻塞）：PA25 已按投影消费其中 5 条
  （`proj_bank_FWGKMBZ` `:2585`、`proj_bank_IXPOTPA` `:2490`、`proj_bank_TXQTPVC` `:2495`、
  `proj_bank_TEWNSCJ` `:2500`、`proj_bank_BIXPCGW6652007036a2` `:2665`）。
  其中 **TEWNSCJ 是 PA25 `TEWNSCJ_MERGED` 的唯一证明通道**（`docs/statement-fix-proposals.md:1679`）。
  **原文如此。**

### 1.3 三个已真闭合件（不在 59 内，但给了模板）

| rest | 声明 | Assembly 行 | 证法 | 行数 |
|---|---|---|---:|---:|
| 2 | `nliRest6096597438a` | 556 | `lfun 1 = 1` + 常数算术 | 8 |
| 4 | `nliRest1965189142x34` | 578 | `lfunY1 ≤ 1` + 线性算术 | 7 |
| 60 | `nliRestZTGIJCF0` | 934 | `pi_lt_d4` 夹逼 + 常数 | 7 |

这三条证明**没有用任何证书**，是 rest 叶里唯一的手工算术先例；其余 59 条的 docstring
全部标 `deferred-compute`（或等价的“证书不在库/在库外”）。**原文如此。**

---

## 2. 59 源分类与总表

### 2.1 分类口径

任务给的 (a)-(e) 五类，在本簇上的实际分布：

| 类 | 定义 | 计数 | 说明 |
|---|---|---:|---|
| (a) | `AllCertified`/ID 清单型，可查表批量填 | **0** | 59 条全是直接 Prop；ID 清单型在相邻的 5 个直挂节点里（且多为死支） |
| (b) | 具体非线性不等式/计算证书型 | **59** | 每条 = `∀ y, 盒 → 非线性结论`，证书由 bb_arb/G4 产出 |
| (c) | 手证几何/分析型 | **0** | 仅相邻的 `nliKcblrqcIneqDef` 属此类 |
| (d) | 下游依赖型（sorry 来自另一具名件） | **0** | 仅相邻的 `nliOx3q1h`、`nliMainNonlinearTerminalV11` 属此类 |
| (e) | 死支/off-path | **0** | 59 条全在 62 元合取里被内核检查；死支在相邻的 5 个直挂节点及其 `*Ids` 注册表 |

(b) 的施工状态再分（这是派工真正需要的粒度）：

| 子类 | 定义 | 计数 | 清单 |
|---|---|---:|---|
| **b1** | pipeline 已 rc=0（有叶数记录），只差证书发射/粘合 | **19** | rest 1,3,9,10,13,14,20,21,22,23,24,31,32,37,38,39,40,41,62 |
| b1-repo | 其中证书 Lean 源已在仓 | **2** | rest 9 `CQITNPEAx3725403817`（2,775 分片 + Base，964,792 叶）、rest 20 `CFWGKMBZ`（605 分片 + Base，205,418 叶） |
| b1-emit | 其中需重跑 `bb_arb --cert` + `emit_lean.py` | **17** | 其余 b1；去重后 **16 个不同证书**（5400790175 a/b 同证书；FHBVYXZ a/b/v2a 同证书） |
| **b2** | 连 `out/cases/<id>.json` 都没有：模板族未发射 | **22** | QITNPEA1 ×6（rest 25-30）、ZTGIJCF4 ×16（rest 44-59） |
| **b3** | 已发射 case 但求解失败/超时 | **18** | rc=2 ×10、timeout(124/137) ×8；其中 4 条是 residue16 真残余 |
| **b0** | b1/b3 中有陈述保真问题的 | **1** | rest 19 `BIXPCGW9455898160`，见 §2.3 |

b3 的 4 条 residue16（`pipeline/interval/out/residue16.txt`）：`IXPOTPA`（rest 7）、
`TXQTPVC`（rest 8）、`PEMKWKU`（rest 11）、`TEWNSCJ`（rest 12）。**【原文】** 其余 14 条
按 `STATUS.md:188-189` 的“92 prep 家族重做”口径处理。**【推断：按家族总账归类，未逐条比对
prep 清单】**

### 2.2 59 行总表

列说明：`#` = rest 位次（1-62，缺失的 2/4/60 是已闭合件）；`Assembly` = `lean/Kepler/Assembly.lean`
行号；`PA21` = `lean/Kepler/Text/PackingAuto21.lean` 中 `bank_*` def 行号；
`pipeline` = `pipeline/interval/out/bbarb_results{2,3}.txt` 的 rc/叶数；`cert` = 在库 Lean 证书模块。
HOL 锚点：每条 docstring 给出的 `ineq.hl` 行号，全部已对照
`reference/flyspeck/text_formalization/nonlinear/ineq.hl` 原文抽查（§EVIDENCE E6）。

| # | 声明 | Assembly | bank def | PA21 | HOL (ineq.hl) | case | pipeline | cert |
|---:|---|---:|---|---:|---|---|---|---|
| 1 | `nliRest6096597438b` | 550 | `bank_6096597438b` | 420 | 1661 | 6096597438_b | closed 77 | — |
| 3 | `nliRest1965189142a` | 570 | `bank_1965189142a` | 432 | 1598 | 1965189142_a | closed 47415 | — |
| 5 | `nliRestJSPEVYT` | 590 | `bank_JSPEVYT` | 447 | 1495 | JSPEVYT | fail rc=2 | — |
| 6 | `nliRestQITNPEA4003532128a` | 596 | `bank_QITNPEA4003532128a` | 455 | 1290 | QITNPEA_4003532128_a | fail rc=2 | — |
| 7 | `nliRestIXPOTPA` | 603 | `bank_IXPOTPA` | 465 | 1265 | IXPOTPA | fail rc=2 | — |
| 8 | `nliRestTXQTPVC` | 610 | `bank_TXQTPVC` | 480 | 1241 | TXQTPVC | timeout | — |
| 9 | `nliRestQITNPEA3725403817` | 618 | `bank_QITNPEA3725403817` | 493 | 1221 | QITNPEA_3725403817 | closed 964792 | CQITNPEAx3725403817 |
| 10 | `nliRestQITNPEAv24003532128` | 625 | `bank_QITNPEAv24003532128` | 501 | 1193 | QITNPEAv2_4003532128 | closed 16 | — |
| 11 | `nliRestPEMKWU` | 631 | `bank_PEMKWU` | 513 | 1169 | PEMKWKU | timeout | — |
| 12 | `nliRestTEWNSCJ` | 638 | `bank_TEWNSCJ` | 526 | 1146 | TEWNSCJ | timeout | — |
| 13 | `nliRestQITNPEA5400790175b` | 645 | `bank_QITNPEA5400790175b` | 538 | 1121 | QITNPEA_5400790175_b | closed 44295 | — |
| 14 | `nliRestQITNPEA5400790175a` | 651 | `bank_QITNPEA5400790175a` | 548 | 1103 | QITNPEA_5400790175_a | closed 44295 | — |
| 15 | `nliRestQITNPEA3848804089` | 657 | `bank_QITNPEA3848804089` | 558 | 1059 | QITNPEA_3848804089 | timeout | — |
| 16 | `nliRestQITNPEA5814748276` | 663 | `bank_QITNPEA5814748276` | 567 | 1041 | QITNPEA_5814748276 | timeout | — |
| 17 | `nliRestQITNPEA6206775865` | 669 | `bank_QITNPEA6206775865` | 576 | 1023 | QITNPEA_6206775865 | timeout | — |
| 18 | `nliRestQITNPEA5653753305` | 675 | `bank_QITNPEA5653753305` | 586 | 1004 | QITNPEA_5653753305 | timeout | — |
| 19 | `nliRestBIXPCGW9455898160` | 682 | `bank_BIXPCGW9455898160` | 596 | 985 | BIXPCGW_9455898160 | timeout | — |
| 20 | `nliRestFWGKMBZ` | 688 | `bank_FWGKMBZ` | 605 | 967 | FWGKMBZ | closed 205418 | CFWGKMBZ |
| 21 | `nliRestFHBVYXZb` | 693 | `bank_FHBVYXZb` | 614 | 942 | FHBVYXZ_b | closed 47096 | — |
| 22 | `nliRestFHBVYXZa` | 698 | `bank_FHBVYXZa` | 624 | 914 | FHBVYXZ_a | closed 47096 | — |
| 23 | `nliRestFHBVYXZv2a` | 704 | `bank_FHBVYXZv2a` | 633 | 888 | FHBVYXZv2_a | closed 47096 | — |
| 24 | `nliRestQITNPEA2134082733` | 711 | `bank_QITNPEA2134082733` | 643 | 864 | QITNPEA_2134082733 | closed 44295 | — |
| 25 | `nliRestQITNPEA1_2_2` | 717 | `bank_QITNPEA1_2_2` | 687 | 845-862 | — | no case | — |
| 26 | `nliRestQITNPEA1_2_1` | 723 | `bank_QITNPEA1_2_1` | 689 | 845-862 | — | no case | — |
| 27 | `nliRestQITNPEA1_2_0` | 729 | `bank_QITNPEA1_2_0` | 691 | 845-862 | — | no case | — |
| 28 | `nliRestQITNPEA1_1_2` | 735 | `bank_QITNPEA1_1_2` | 693 | 845-862 | — | no case | — |
| 29 | `nliRestQITNPEA1_1_1` | 741 | `bank_QITNPEA1_1_1` | 695 | 845-862 | — | no case | — |
| 30 | `nliRestQITNPEA1_1_0` | 747 | `bank_QITNPEA1_1_0` | 697 | 845-862 | — | no case | — |
| 31 | `nliRestQITNPEA9939613598` | 754 | `bank_QITNPEA9939613598` | 706 | 798 | QITNPEA_9939613598 | closed 27043 | — |
| 32 | `nliRestBIXPCGW7274157868a` | 760 | `bank_BIXPCGW7274157868a` | 717 | 776 | BIXPCGW_7274157868_a | closed 70870 | — |
| 33 | `nliRestBIXPCGWb` | 766 | `bank_BIXPCGWb` | 727 | 758 | BIXPCGW_b | fail rc=2 | — |
| 34 | `nliRestBIXPCGW1738910218a2` | 772 | `bank_BIXPCGW1738910218a2` | 736 | 739 | BIXPCGW_1738910218_a2 | fail rc=2 | — |
| 35 | `nliRestBIXPCGW7080972881a2` | 778 | `bank_BIXPCGW7080972881a2` | 745 | 721 | BIXPCGW_7080972881_a2 | fail rc=2 | — |
| 36 | `nliRestBIXPCGW6652007036a2` | 784 | `bank_BIXPCGW6652007036a2` | 754 | 701 | BIXPCGW_6652007036_a2 | fail rc=2 | — |
| 37 | `nliRestGLFVCVK4y4subcrit` | 791 | `bank_GLFVCVK4y4subcrit` | 763 | 675 | GLFVCVK4_2477216213_y4subcrit | closed 29975 | — |
| 38 | `nliRestGLFVCVK4y4supercrit` | 798 | `bank_GLFVCVK4y4supercrit` | 773 | 649 | GLFVCVK4_2477216213_y4supercrit | closed 24542 | — |
| 39 | `nliRestGLFVCVK4y4crit` | 805 | `bank_GLFVCVK4y4crit` | 783 | 623 | GLFVCVK4_2477216213_y4crit | closed 6424 | — |
| 40 | `nliRestGLFVCVK4a8328676778` | 812 | `bank_GLFVCVK4a8328676778` | 793 | 586 | GLFVCVK4a_8328676778 | closed 19802 | — |
| 41 | `nliRestGLFVCVK4` | 818 | `bank_GLFVCVK4` | 803 | 559 | GLFVCVK4_2477216213 | closed 205418 | — |
| 42 | `nliRestMKFKQWUhalfwt` | 825 | `bank_MKFKQWUhalfwt` | 814 | 523 | MKFKQWU_halfwt | fail rc=2 | — |
| 43 | `nliRestMKFKQWU` | 831 | `bank_MKFKQWU` | 823 | 502 | MKFKQWU | fail rc=2 | — |
| 44 | `nliRestZTGIJCF4_1_1_1_1` | 837 | `bank_ZTGIJCF4_1_1_1_1` | 860 | 486-499 | — | no case | — |
| 45 | `nliRestZTGIJCF4_1_1_1_0` | 843 | `bank_ZTGIJCF4_1_1_1_0` | 862 | 486-499 | — | no case | — |
| 46 | `nliRestZTGIJCF4_1_1_0_1` | 849 | `bank_ZTGIJCF4_1_1_0_1` | 864 | 486-499 | — | no case | — |
| 47 | `nliRestZTGIJCF4_1_1_0_0` | 855 | `bank_ZTGIJCF4_1_1_0_0` | 866 | 486-499 | — | no case | — |
| 48 | `nliRestZTGIJCF4_1_0_1_1` | 861 | `bank_ZTGIJCF4_1_0_1_1` | 868 | 486-499 | — | no case | — |
| 49 | `nliRestZTGIJCF4_1_0_1_0` | 867 | `bank_ZTGIJCF4_1_0_1_0` | 870 | 486-499 | — | no case | — |
| 50 | `nliRestZTGIJCF4_1_0_0_1` | 873 | `bank_ZTGIJCF4_1_0_0_1` | 872 | 486-499 | — | no case | — |
| 51 | `nliRestZTGIJCF4_1_0_0_0` | 879 | `bank_ZTGIJCF4_1_0_0_0` | 874 | 486-499 | — | no case | — |
| 52 | `nliRestZTGIJCF4_0_1_1_1` | 885 | `bank_ZTGIJCF4_0_1_1_1` | 876 | 486-499 | — | no case | — |
| 53 | `nliRestZTGIJCF4_0_1_1_0` | 891 | `bank_ZTGIJCF4_0_1_1_0` | 878 | 486-499 | — | no case | — |
| 54 | `nliRestZTGIJCF4_0_1_0_1` | 897 | `bank_ZTGIJCF4_0_1_0_1` | 880 | 486-499 | — | no case | — |
| 55 | `nliRestZTGIJCF4_0_1_0_0` | 903 | `bank_ZTGIJCF4_0_1_0_0` | 882 | 486-499 | — | no case | — |
| 56 | `nliRestZTGIJCF4_0_0_1_1` | 909 | `bank_ZTGIJCF4_0_0_1_1` | 884 | 486-499 | — | no case | — |
| 57 | `nliRestZTGIJCF4_0_0_1_0` | 915 | `bank_ZTGIJCF4_0_0_1_0` | 886 | 486-499 | — | no case | — |
| 58 | `nliRestZTGIJCF4_0_0_0_1` | 921 | `bank_ZTGIJCF4_0_0_0_1` | 888 | 486-499 | — | no case | — |
| 59 | `nliRestZTGIJCF4_0_0_0_0` | 927 | `bank_ZTGIJCF4_0_0_0_0` | 890 | 486-499 | — | no case | — |
| 61 | `nliRestGCKBQEA` | 946 | `bank_GCKBQEA` | 915 | 1352 | GCKBQEA | fail rc=2 | — |
| 62 | `nliRestRQWUDDU` | 952 | `bank_RQWUDDU` | 923 | 1332 | RQWUDDU | closed 46 | — |

> 注：`timeout` = rc 124 或 137；`fail rc=2` = bb_arb 未闭合退出。`closed` 后的数字是
> `bbarb_results*.txt` 记录的叶数。所有 59 条 docstring 均标 `deferred-compute` 或等价；
> 上述 `closed` 是 pipeline 历史求解记录，不代表 Lean 侧有证书。

### 2.3 标红：rest 19 的陈述反号（最高优先级）

**事实链（全部原文/机读证据）：**

1. HOL 原文 `reference/flyspeck/text_formalization/nonlinear/ineq.hl:985`：
   ```hol
   (gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > -- #0.00569)
   ```
   HOL 的 `--` 是一元负号（同一 HOL 源内 `sphere.hl:632/634` 的 `b_spine5 = -- #0.0445813` 是负数用法），
   所以原文是 `gamma4fgcy > -0.00569`。doc 自述 “If X is a quarter, then γ(X,L) ≥ -0.00569.”
2. pipeline 的 AST `pipeline/interval/out/ineqs_ast.json` `records[35]`：
   ```json
   {"op": ">", "args": [{"app":"gamma4fgcy",...}, {"neg":{"dec":"0.00569"}}]}
   ```
   case JSON 的 RPN 尾部也是 `push_const 569/100000, neg`——pipeline 按 **-0.00569** 编码。
3. Lean `PackingAuto21.lean:596-603`：
   ```lean
   def bank_BIXPCGW9455898160 : Prop :=
     ∀ y1 … y6, … → gamma4fgcy … lmfun > 0.00569
   ```
   **Lean 写成了 +0.00569。**
4. `Assembly.lean:677-681` 的 docstring 自己写了“HOL 字面 `-- #0.00569` 双重负号”——
   说明转录时已经注意到这个字面，但结论写反了。**【推断：转录者把 `--` 当成双重负号；
   按 HOL 词法它是单个一元负号】**

**后果**：Lean 陈述比 HOL 强 0.01138，且比 pipeline 已编码的 case 强。任何基于该 case 的
证书都只能证明 `> -0.00569`，无法粘合到 `> +0.00569`。这条不应进入任何证书批，应先发
**statement-fix**（把 PA21 的 `0.00569` 改成 `-0.00569`，或写成 `> -0.00569`），
再走求解/粘合。PA21 的 `bank_*` 被 PA25 多处消费，改动需 SF 审批与全局 grep 核实；
这是一次“向 HOL 保真”的修正，不是弱化最终定理。**【推断：改动只影响该 bank 的消费者，
但 PA21 是共享文件，需按 statement-fix 流程走】**

### 2.4 其余标红/高风险单件

| 单件 | 风险 | 证据 |
|---|---|---|
| rest 9 `QITNPEA3725403817` | **最大单件**：964,792 叶 / 2,775 分片（+Base）；证书源在库但未构建；粘合涉及 sqrt+atan+ite | `CQITNPEAx3725403817.lean:1-5`、`:2789-2805`；分片 2,775（+Base） |
| rest 20 `FWGKMBZ` | 205,418 叶 / 605 分片（+Base）；证书源在库；粘合最简单（`deltaX` 多项式） | `CFWGKMBZ.lean:1-5`、`:618-636` |
| rest 32 `BIXPCGW7274157868a` | 79 sqrt + 143 atan；70,870 叶记录，但另有 134,788 个 depth-8 STUCK 盒记录，**两份状态互相矛盾**，开工前必须对齐域/版本 | `pipeline/interval/wave2-disj-design.md:10`；`docs/projects/archive/bixpcgw-residual.md:1-8`；`bbarb_results3.txt` rc=0 70870 |
| rest 12 `TEWNSCJ` | residue16 + PA25 `TEWNSCJ_MERGED` 唯一通道；6 路析取；timeout 124 | `residue16.txt`；`docs/statement-fix-proposals.md:1679`；`PackingAuto25.lean:7830` |
| rest 7/8/11 | residue16，无 prep 家族；分别 7/6/6 路析取 | `residue16.txt`；case notes |
| rest 42/43 `MKFKQWU*` | 历史记录“≥10⁹ 叶”级别，naive 区间过估 | `PLAN.md:100`；`STATUS.md:189` |

---

## 3. 相邻 8 + 7 源（nliTskBank / nliCell3Bank）

这两个 bank 是分量 1/6 的第 1、2 合取项，与 59 条同层，但不属于 `nliPackNonlinearRest`。
它们的状态高度不均：**cell3 有 4/7 已有 rc=0（其中 3 条是 3-4 叶的微型证书），tsk 有 3/10
已闭合（2 条手证 + 1 条 1 叶）**，是比 59 簇更便宜的首批候选。

### 3.1 cell3（7 源，`nliCell3Bank` `Assembly.lean:380`）

| 声明 | Assembly | bank | PA21 | HOL | pipeline | 备注 |
|---|---:|---|---:|---|---|---|
| `nliCell3QZECFICwt0` | 339 | `bank_QZECFICwt0` | 205 | 1372 | timeout 124 | |
| `nliCell3QZECFICwt0corner` | 345 | `bank_QZECFICwt0corner` | 213 | 1389 | timeout 124 | |
| `nliCell3QZECFICwt0sqrt8` | 351 | `bank_QZECFICwt0sqrt8` | 220 | 1406 | **closed 3** | 微型证书 |
| `nliCell3QZECFICwt1` | 357 | `bank_QZECFICwt1` | 229 | 1425 | **closed 4** | 微型证书 |
| `nliCell3QZECFICwt2A` | 363 | `bank_QZECFICwt2A` | 240 | 1443 | **closed 4** | 微型证书 |
| `nliCell3CIHTIUM` | 369 | `bank_CIHTIUM` | 250 | 1462 | fail rc=2 | |
| `nliCell3CJFZZDW` | 375 | `bank_CJFZZDW` | 258 | 1479 | **closed 1677** | |

### 3.2 tsk（10 源，`nliTskBank` `Assembly.lean:510`；8 open）

| 声明 | Assembly | bank | PA21 | HOL | pipeline | 备注 |
|---|---:|---|---:|---|---|---|
| `nliTskGXSA` | 389 | `bank_TSKAJXYGXSA` | 267 | 359 | **closed 1** | 最便宜的非手证件 |
| `nliTskIYOUOBFsharpv2` | 395 | `bank_TSKAJXYIYOUOBFsharpv2` | 321 | 242 | timeout 124 | |
| `nliTskIYOUOBFsym` | 401 | `bank_TSKAJXYIYOUOBFsym` | 329 | 223 | timeout 124 | |
| `nliTskRIBCYXUsharp` | 406 | `bank_TSKAJXYRIBCYXUsharp` | 349 | 165 | timeout 124 | residue16 同族 |
| `nliTskRIBCYXUsym` | 412 | `bank_TSKAJXYRIBCYXUsym` | 338 | 183 | timeout 124 | residue16 同族 |
| `nliTskTADIAMB` | 418 | `bank_TSKAJXYTADIAMB` | 357 | 127 | fail rc=2 | |
| `nliTskWKGUESBsym` | 424 | `bank_TSKAJXYWKGUESBsym` | 311 | 281 | timeout 124 | residue16 同族 |
| `nliTskXLLIPLS` | 430 | `bank_TSKAJXYXLLIPLS` | 303 | 304 | timeout 124 | |
| `nliTskdx4` | 437 | `bank_TSKAJXYdx4` | 286 | 341 | closed 1 | **已手证闭合** |
| `nliTskeulerA` | 473 | `bank_TSKAJXYeulerA` | 294 | 324 | closed 1 | **已手证闭合** |

> 说明：`nliTskdx4`/`nliTskeulerA` 不在 8 个 open 源内（TSV 只列 sorry 源）；它们的
> `bank_*` rc=0 记录是 1 叶证书，但 Lean 侧已有 28/33 行手证，说明这两条**不需要证书**。
> `nliTskGXSA` 的 rc=0 也是 1 叶，可作为“微型证书 + 端点嵌入”的最小练习件。

---

## 4. 五个直挂 `nonlinearInequalities` 的源

这 5 条不是 59 簇，但同属 Assembly 的 83 个 direct sorry 源。它们揭示了一个重要事实：
**ID 清单型（a）和死支（e）都在这里，不在 59 簇。**

| 声明 | Assembly | 类型 | 定义位置 | HOL 锚 | 分类 | 说明 |
|---|---:|---|---|---|---|---|
| `nliLpIneqs` | 1055 | `LpIneqs` | `Assembly.lean:245`，`AllCertified idsLpIneqs`，`idsLpIneqs = []` | the_main_statement.hl:29-45（127 条） | **(e) 占位死支** | 空清单使命题空洞成立；政策禁止利用空清单/回落 `True` 平凡闭合 |
| `nliPackIneqDefA` | 1075 | `PackIneqDefA` | `Assembly.lean:249`，`:= True` | YSSKQOY.hl:24-28（5 条） | **(e) 占位死支** | 同上；真化后才能接线 |
| `nliOx3q1h` | 1015 | `ox3q1hP25` | `PackingAuto25.lean:89`，`def … := sorry` | Oxl_def.hl；merge_ineq.hl:78-92（230 条） | **(d) 下游依赖** | 语句级缺口：opaque def 本身是 sorry |
| `nliMainNonlinearTerminalV11` | 1037 | `main_nonlinear_terminal_v11` | `LocalAuto1.lean:975`，`def … := sorry` | terminal.hl:24-44（109 条） | **(d) 下游依赖** | 同上；109 条逐条证书 |
| `nliKcblrqcIneqDef` | 1090 | `KcblrqcIneqDef` | `TameLp.lean:512`（真实 Prop，非证书表） | tame_lemmas-compiled.hl:34-46（28 条） | **(c) 手证几何** | 内容是 Contravening 下的 azim 界，不是区间证书能直接解决的 |

另外，5 个 `*Ids` 注册表（`nliOx3q1hIds` `:1023`、`nliMainNonlinearTerminalV11Ids` `:1044`、
`nliLpIneqsIds` `:1066`、`nliPackIneqDefAIds` `:1082`、`nliKcblrqcIneqDefIds` `:1099`）
**不在 e2e 锥内**（TSV 里没有它们）——因为接口层用 `sorry` 直接闭合，注册表定理是
**死代码**。**【推断，证据：TSV 只列 5 个接口节点，未列任何 `*Ids`；且这些定理不被
`nonlinearInequalities` 的证明项引用】** 这意味着：如果先做 `*Ids` 批量填表，对当前 e2e
债务**零收益**；必须先改接口接线。

---

## 5. 车道判定与机械处方

### 5.1 该发 pipeline 还是 Lean？

**结论：两条都发，pipeline 先行；若只能发一条，发 pipeline。**

理由（按人数/工时口径）：

- **pipeline 是闸门**：59 条里 57 条没有可用的 Lean 证书源。其中 17 条已有 rc=0 记录，
  只差 `bb_arb --cert` + `emit_lean.py`；22 条连 case JSON 都没有，需要先 `emit_rpn.py`；
  18 条需要求解器研究。**Lean 侧单独最多只能立即做 2 条（rest 9/20 的在库证书）**。
- **Lean 是固定收尾**：59 条每条都要一个 `evalReal` 粘合 + 端点嵌入 + 替换 `sorry`。
  这部分可以按批并行，但总量不因 pipeline 收敛而减少。
- **不是 ID 表**：`bank_*` 是直接 Prop，不是 `CertifiedIneqHolds` 查表。所以不存在
  “把 59 个 ID 塞进一个表、一次 `decide`” 的批量填法。**【原文：`Assembly.lean:234-237`
  的 `CertifiedIneqHolds`/`AllCertified` 只服务六分量注册表；59 条的类型是 `bank_*`】**

### 5.2 批量填表的机械处方（每条源）

标准五步（以 y 空间 7 维 case 为例；x 空间 6 维去掉 `hminus` 维）：

1. **case 已存在且 rc=0**：
   ```sh
   # 在 Linux/G4 机（bb_arb 需要 FLINT/Arb；本机没有 pipeline/tools）
   pipeline/interval/bb_arb pipeline/interval/out/cases/<case>.json \
       --cert /tmp/certs/<case>.json
   ```
2. **发射 Lean 证书**：
   ```sh
   python3 pipeline/interval/emit_lean.py \
       pipeline/interval/out/cases/<case>.json /tmp/certs/<case>.json \
       lean/Kepler/Interval/Cases/C<Case>.lean --bbg --params=/tmp/<case>.params
   ```
   `--bbg`/`--fill`/`--disj-gd` 的具体分支取决于 case 是否含 sqrt/atan/disj；
   参考 `emit_lean.py` 头部 usage（`--fill`、`--bbg --params`、`--bbg --disj-gd`、
   `--disj-dummy`）。**【原文：emit_lean.py usage】**
3. **写粘合引理**（新私件，`Kepler.Assembly.NliRest.*`，不得 import `Kepler.Assembly`，
   避免循环）：
   ```lean
   theorem <Case>_evalReal (ρ : Fin n → ℝ) :
       <Case>Expr.evalReal ρ = <HOL 命名定义的组合> := by
     simp only [<Case>Expr, IExpr.evalReal, <defs...>,
       Dyadic.toReal_int, Int.cast_zero]
     ring   -- 仅多项式情形；超越情形需要额外的 atn2/ite 桥
   ```
4. **端点嵌入**（把 Lean 盒 `[2*hminus, 2*hplus]` 等嵌进证书的 dyadic 外扩盒）：
   ```lean
   have hm : boxMem <Case>Box ![hminus, y1, y2, y3, y4, y5, y6] := by
     intro i; fin_cases i <;> exact ⟨…norm_num…, …norm_num…⟩
   ```
   需要的共享端点事实：`mi_hminus_prop`、`mi_two_hminus_le_two_h0`、
   `mi_two_hminus_le_sqrt8`、`mi_two_hminus_le_two_sqrt2`、`mi_two_hplus_le_two_sqrt2`
   （`PackingAuto21.lean:1887-1948`）。
5. **替换 `sorry`**：
   ```lean
   theorem nliRestX : bank_X := by
     intro … hboxes
     have hpos := <Case>_pos ![hminus, y1, …] hm
     rw [<Case>_evalReal] at hpos
     <把 hpos 的表达式桥回 bank 结论：dihY/etaY/gamma23…/yOfX 的 rfl 或恒等式>
     simpa [bank_X, …] using hpos
   ```
   验收：`#print axioms nliRestX` = `[propext, Classical.choice, Quot.sound]`；
   `lake build Kepler.Assembly` 0 error；不得新增 `sorry`/`native_decide`（工人纪律）。

**批量化的唯一加速点**：同证书多实例。已确认 `QITNPEA 5400790175 a/b` 证书逐字节相同、
`FHBVYXZ a/b/v2a` 证书逐字节相同（`wave2-disj-design.md:24-27`），所以 **19 条 b1 只需
16 个不同证书**；粘合引理仍须逐条写（陈述不同）。**【原文：wave2 文档；“逐字节相同”
是文档断言，本报告未重跑校验】**

### 5.3 不要做的事

- 不要给 59 条建 `AllCertified` 查表：类型不匹配，且会引入 `certifiedIneqHolds_pilot` 的
  `else True` 退化风险（`IdLists.lean:699` 警告）。
- 不要用 `nliPackIneqDefA := trivial` 或 `nliLpIneqs` 的空清单闭合：政策明令禁止
  （`Assembly.lean:1052-1053/1073`）。
- 不要在 rest 19 的 PA21 陈述修正前发射/粘合它的证书。
- 不要把 PA25 的 `proj_bank_*` 当作 59 条的证明来源：它们以 `pack_nonlinear_non_ox3q1h`
  为前提，反过来依赖 `nliPackNonlinearRest`，会循环。

---

## 6. 切批处方

### 6.1 依赖序与总览

59 条彼此独立；唯一的依赖是 **证书 → 粘合 → 替换 sorry**。因此按“证书状态”排序，
不按数学依赖排序：

```
P0 陈述修正（rest 19）  ── 必须最先，否则后面白做
P1 b1 证书重发射/构建   ── 19 条（2 条在库，17 条重发射；16 个不同证书）
P2 b1 Lean 粘合         ── 4 个 Lean 批
P3 b2 case 生成 + 求解  ── 22 条（QITNPEA1 ×6, ZTGIJCF4 ×16）
P4 b2 Lean 粘合         ── 5 个 Lean 批
P5 b3 求解器研究        ── 18 条（4 residue16 + 14 prep 重做）
P6 b3 Lean 粘合         ── 4 个 Lean 批
```

**总计：15 个 Lean 批（每批 ≤500 行手写 Lean），4-6 波 pipeline；预计 40-70 个工人轮次。**
（轮次 = 一个工人在一个 lane 文件上从开工到 `lake build` 自然退出；pipeline 轮次另计。）

### 6.2 逐批详情

#### A1（推荐首批之一，Lean-only）：rest 20 `FWGKMBZ`

| 项 | 内容 |
|---|---|
| 输入 | `lean/Kepler/Interval/Cases/CFWGKMBZ.lean` + `CFWGKMBZ/Base.lean`；`bank_FWGKMBZ`（PA21:605）；`deltaX`（`SphereKit.lean:46`） |
| 输出 | `nliRestFWGKMBZ : bank_FWGKMBZ`（`Assembly.lean:688`），无 sorry |
| 在册载体 | 新文件 `lean/Kepler/Assembly/NliRest/CertGlueA.lean`（namespace `Kepler.Assembly`）；`Assembly.lean` 顶部加 import，`:688` 改成 `:= nliRestFWGKMBZ_proof`（只动证明体，陈述冻结） |
| 建议新私件 | `CFWGKMBZ_evalReal`（`simp only […]` + `ring`）、`CFWGKMBZ_boxMem`（`fin_cases` + `norm_num` + `mi_hminus_prop`）、`nliRestFWGKMBZ_proof` |
| 雷区 | 605 分片 + Base 冷构建（本机无 olean，预计 1-2h）；`Dyadic.toReal_int`/`Int.cast_zero` 不可省；`hminus` 是第 0 维（表达式不用，但 `boxMem` 仍要证）；y1 上端 `2*hplus ≤ 2.6508…` 需 `norm_num`；`ring` 可能比 `simp` 慢，先试 `simp only` |
| 预计轮数 | 2-3（1 构建 + 1 粘合 + 1 终验） |
| 解锁 | 1/59；同时验证“多项式 case 的一行粘合”模板 |

#### A2（备选，Lean-only，大件）：rest 9 `QITNPEA3725403817`

| 项 | 内容 |
|---|---|
| 输入 | `CQITNPEAx3725403817.lean`（2,775 分片 + `Base.lean`）；`bank_QITNPEA3725403817`（PA21:493）；`dihY`/`dihXf`/`atn2` |
| 输出 | `nliRestQITNPEA3725403817`（`Assembly.lean:618`） |
| 在册载体 | `NliRest/CertGlueA2.lean` + `Assembly.lean:618` 接线 |
| 建议新私件 | `CQITNPEAx3725403817_evalReal`（sqrt/arctan/ite 展开）、`boxMem`、`dihY` 桥（`yOfX`/`deltaX`/`deltaX4`/`atn2`）、`proof` |
| 雷区 | 2,775 分片 + Base，96 万叶，5h+ 构建；`dihY` 的 `atn2` 是 ite 编码，粘合可能需要 case split；4 个 sqrt 参数槽（`ms`）在 `evalReal` 里被丢弃，但表达式工厂的 `rfl` 桥要用 `CQITNPEAx3725403817_sem`；`hminus` 第 0 维 |
| 预计轮数 | 3-5 |
| 解锁 | 1/59，但解锁**最大单件**；为后续 `dihY` 类 case 提供可复用粘合模板 |

#### B（推荐首批之二，pipeline+Lean，最便宜）：rest 10 + rest 62 + rest 1

| 项 | 内容 |
|---|---|
| 输入 | 已 rc=0 的 case：`QITNPEAv2_4003532128`（16 叶）、`RQWUDDU`（46 叶）、`6096597438_b`（77 叶）；`bank_*` PA21:501/923/420 |
| 输出 | 3 条 `nliRest*`（Assembly:625/952/550），~300 行 |
| 在册载体 | `NliRest/CertGlueB.lean`；Assembly 三处接线 |
| 建议新私件 | 每 case 的 `evalReal`/`boxMem`/`proof`；共享 `nliRest_boxMem_y` 端点助手（`hminus` 7 维模板） |
| 雷区 | rest 10 是 7 路析取（`eta_y`/`rad2X`/`gamma23Full8X`/`dihY`），glue 不便宜；rest 62 是 3 路析取（`dihY`/`eta_y`）；rest 1 含 `asn797k`（arcsin/sin）与 `π`；disj 分支顺序必须与 bank def 一致；`6096597438_b` 的 `lfun 1` 要展开 |
| 预计轮数 | 1 pipeline + 2-3 Lean |
| 解锁 | 3/59；**证书总叶数仅 139**，是全局最便宜的证书生产 |

#### C1（pipeline+Lean，中件）：rest 3, 13, 14, 24, 31

| 项 | 内容 |
|---|---|
| 输入 | `1965189142_a`（47,415）、`QITNPEA_5400790175_a/_b`（44,295，同证书）、`QITNPEA_2134082733`（44,295）、`QITNPEA_9939613598`（27,043） |
| 输出 | 5 条 `nliRest*`（Assembly:570/645/651/711/754），~400 行 |
| 在册载体 | `NliRest/CertGlueC1.lean` |
| 建议新私件 | 每 case `evalReal`/`boxMem`/`proof`；`ineqProp_1965189142a` 形语义命题（可仿 `IneqPilot.lean:38-68`） |
| 雷区 | `1965189142_a` 用 `asnFnhk` + `lfunY1`；三条 QITNPEA 都是多路析取（`eta`/`gamma`/`dih`/`rad2`）；5400790175 a/b 证书同但 bank 盒/结论不同，不可复用 glue；`dihY` 的 `atn2` 桥 |
| 预计轮数 | 1 pipeline + 2-3 Lean |
| 解锁 | 5/59 |

#### C2（pipeline+Lean，硬粘合）：rest 21, 22, 23, 32

| 项 | 内容 |
|---|---|
| 输入 | `FHBVYXZ_a/_b/_v2a`（47,096×3，同证书）、`BIXPCGW_7274157868_a`（70,870） |
| 输出 | 4 条 `nliRest*`（Assembly:693/698/704/760），~450 行 |
| 在册载体 | `NliRest/CertGlueC2.lean` |
| 建议新私件 | 每 case `evalReal`/`boxMem`/`proof`；`BIXPCGW` 的 disj0 glue（4 sqrt + 7 atan + 1 abs）单独私件 |
| 雷区 | FHBVYXZ 三份证书逐字节相同但 goals 不同，不能共用 `evalReal`；BIXPCGW 的证书状态有两份矛盾记录（70,870 叶 rc=0 vs 134,788 残留盒），**开工前对齐域/版本**；`atan`/`abs`/`ite` 的 `evalReal` 语义桥 |
| 预计轮数 | 1 pipeline + 3-4 Lean |
| 解锁 | 4/59 |

#### C3（pipeline+Lean，GLFVCVK4 家族）：rest 37-41

| 项 | 内容 |
|---|---|
| 输入 | `GLFVCVK4 2477216213`（205,418）、`y4subcrit`（29,975）、`y4supercrit`（24,542）、`y4crit`（6,424）、`GLFVCVK4a 8328676778`（19,802） |
| 输出 | 5 条 `nliRest*`（Assembly:791/798/805/812/818），~400 行 |
| 在册载体 | `NliRest/CertGlueC3.lean` |
| 建议新私件 | 每 case `evalReal`/`boxMem`/`proof`；`GLFVCVK4` 的 disj 2-prog 分支 glue |
| 雷区 | 5 个变体的盒/临界性不同；205,418 叶件有 19,938 ops / 60 ite；`GLFVCVK4` 与 `FWGKMBZ` 叶数相同（205,418），**可能是同一证书**，先核 SHA/表达式再决定是否复用到 A1；`disj` 顺序 |
| 预计轮数 | 1-2 pipeline + 3 Lean |
| 解锁 | 5/59 |

#### D（b2 模板族，22 条）：QITNPEA1 ×6 + ZTGIJCF4 ×16

| 项 | 内容 |
|---|---|
| 输入 | `emit_rpn.py` 生成的 22 个 case（当前 `out/cases` 里没有）；PA21 模板 `bank_QITNPEA1tmpl`（:676）、`bank_ZTGIJCF4tmpl`（:845）；`bank_ZTGIJCF4lo/hi`（:839/842）、`bank_QITNPEA1lo/hi`（:665/669）、`bankGenMid`（:673） |
| 输出 | 22 条 `nliRest*`（Assembly:717-747、837-927），分 5 个 Lean 批（每批 4-5 条，≤500 行） |
| 在册载体 | `NliRest/CertGlueD1..D5.lean` |
| 建议新私件 | 模板实例化 `rfl` 桥（PA21:905-906 先例）；每 case `evalReal`/`boxMem`/`proof`；`gamma4fgcy`/`betaBumpLb`/`aSpine5`/`bSpine5` 的共享桥 |
| 雷区 | **22 条连 case 都没有**：先跑 `emit_rpn.py`；模板参数 `i3..i6` 必须与 PA21 的 16+6 个 def 一一对应；QITNPEA1 的分母 `1+mid i3+mid i4`（w=1/2/3）；ZTGIJCF4 的 `betaBumpLb` 只在 `w=2 ∧ i4=1` 时加；`rad2X > 2` 析取支可能在很多盒上平凡，但 `gamma4fgcy` 主支仍需证书；`a_spine5/b_spine5` 的 opaque 常数桥（SF-41 未应用前 PA3 消费点可能卡） |
| 预计轮数 | 2-6 pipeline + 5 个 Lean 批 × 2-4 = 10-20 |
| 解锁 | 22/59（最大一块数量） |

#### E（b3 硬解，18 条）

| 项 | 内容 |
|---|---|
| 输入 | 18 个已发射 case；4 条 residue16（rest 7/8/11/12）；14 条 92-prep 重做口径；rest 19 先做陈述修正 |
| 输出 | 18 条 `nliRest*`（Assembly:590/596/603/610/631/638/657/663/669/675/682/766/772/778/784/825/831/946），分 4 个 Lean 批 |
| 在册载体 | `NliRest/CertGlueE1..E4.lean` |
| 建议新私件 | 每 case `evalReal`/`boxMem`/`proof`；按求解路线（`--tm` / `--ite-hull` / `--mono` / `--gsplit` / `BBTreeGD`）分别建私件；residue16 的 4 条单独私件 |
| 雷区 | **求解器可能根本不收敛**：BIXPCGW/MKFKQWU 曾报巨大叶数；residue16 无 prep 家族；TEWNSCJ 是 PA25 唯一通道，失败会连带 PA25；rest 19 必须先改 PA21 符号；timeout 的 `rc=124/137` 可能是预算不是不可证 |
| 预计轮数 | 3-8 pipeline 波 + 4 个 Lean 批 × 3-8 = 12-32 |
| 解锁 | 18/59 |

### 6.3 推荐首批与备选

**推荐首批（双车道可用）：B 批。**
- 3 条源、证书总叶数 139（16+46+77），是全局最便宜的证书生产；
- 1 波 pipeline（3 个 `bb_arb --cert` + 3 次 `emit_lean.py`）+ 1 个 Lean 批（~300 行）；
- 同时覆盖三种 glue 形态（多项式/多路析取+超越/arcsin），为后续 56 条定模板；
- 解锁 3/59。

**推荐首批（只有本机 Lean 车道）：A1 批（rest 20 `FWGKMBZ`）。**
- 证书 Lean 源已在库，无需 pipeline；
- 粘合是 `deltaX` 多项式恒等式，最可能一次过；
- 唯一成本是 605 分片 + Base 冷构建（1-2h）；
- 解锁 1/59，并验证“在库证书 + 端点嵌入”的全链。

**备选：**
- **A2（rest 9 `QITNPEA3725403817`）**：解锁最大单件，但 2,775 分片 + Base，5h+，且 glue 涉及
  `dihY`/`atn2`，适合作为 A1 之后的第二个 Lean 批。
- **相邻便宜件（不在 59 内）**：`nliTskGXSA`（1 叶）、`nliCell3QZECFICwt0sqrt8`（3 叶）、
  `nliCell3QZECFICwt1`（4 叶）、`nliCell3QZECFICwt2A`（4 叶）、`nliCell3CJFZZDW`（1,677 叶）。
  这 5 条只需 1 波微型 pipeline + 1 个 Lean 批，可先于 59 簇清零，作为管线/glue 的
  端到端演练。**【推断：它们的 bank 类型与 rest 同形，glue 模板可直接复用】**
- **P0 陈述修正（rest 19）**：零 Lean 行，但必须先做；否则 E 批的求解/粘合全部白费。

**不建议首批做**：C2（BIXPCGW 硬 glue + 证书状态矛盾）、E（residue16/92-prep 求解不确定）、
D（22 条 case 未发射，pipeline 周期长）。

---

## 7. 风险清单（按严重度）

1. **rest 19 陈述反号（P0，确定）**：Lean 比 HOL 强 0.01138；证书不可能粘上。
   先发 statement-fix（PA21:603），再做任何求解/粘合。**原文证据见 §2.3。**
2. **18 条硬解（P1，高）**：4 条 residue16 + 14 条 92-prep 重做；BIXPCGW/MKFKQWU 历史
   叶数爆炸；TEWNSCJ 是 PA25 唯一通道。可能长时间不收敛。
3. **超越函数 glue 未自动化（P1，高）**：`dihY`（atn2 ite）、`etaY`（acos 半角化）、
   `gamma23Full8X`、`rad2X` 的 `evalReal` 桥是 155 定义闭包的主体剩余
   （`STATUS.md:208` 明说“主体剩余”）。单件可能 100-300 行，不是 60 行。
4. **本机无 pipeline 工具链（P1，确定）**：`pipeline/tools/` 不存在，`dreal` 不在 PATH；
   `bb_arb.c` 需要 FLINT/Arb。pipeline 车道必须发到 Linux/G4 机；否则只能做 A1/A2。
5. **大证书冷构建（P2，中）**：605/2,775 分片 + Base，本机无 olean；可能 OOM/数小时。
   先 `lake build Kepler.Interval.Cases.CFWGKMBZ` 单模块试水，再决定是否并行。
6. **证书状态矛盾（P2，中）**：BIXPCGW7274157868a 同时有 “rc=0 70,870 叶” 和
   “134,788 个 depth-8 STUCK 盒” 两份记录；开工前必须对齐 case 版本/域。
7. **PA21 共享面（P2，中）**：`bank_*` 被 PA25 多处消费；rest 19 的修正需全局 grep
   + SF 审批；不要把 PA21 的 `bank_*` 改成 `AllCertified` 形态（会破坏 62 元合取）。
8. **重复证书/重复 glue（P3，低）**：5400790175 a/b、FHBVYXZ a/b/v2a 证书相同但
   bank 陈述不同，不能共用 glue；GLFVCVK4/FWGKMBZ 叶数相同，先核是否同一证书。

---

## 8. 方法与复现

关键命令（完整输出/行号见 `EVIDENCE.md`）：

```sh
# 1. 从 e2e 地图抽 59 源
awk -F'\t' '$2 ~ /^Kepler\.Assembly\.nliRest/ {print NR": "$0}' \
  docs/e2e-reachability-map.tsv

# 2. 定位声明
grep -n 'theorem nliRest\|theorem nliPackNonlinearRest\|theorem nliTskBank\|theorem nliCell3Bank' \
  lean/Kepler/Assembly.lean

# 3. 定位 PA21 bank defs
grep -n 'def bank_' lean/Kepler/Text/PackingAuto21.lean

# 4. pipeline 状态 join（Python 解析 case JSON + bbarb_results + Assembly docstring）
python3 - <<'EOF' ... EOF   # 见 EVIDENCE.md E4

# 5. 求解记录
cat pipeline/interval/out/bbarb_results2.txt pipeline/interval/out/bbarb_results3.txt
cat pipeline/interval/out/residue16.txt
```

**本报告未做的事**（避免越界）：
- 未跑 `lake build`/`git`；未改仓库；只读。
- 未验证 16 个证书的逐字节同一性（引用 `wave2-disj-design.md` 的断言）。
- 未验证 GLFVCVK4 与 FWGKMBZ 是否同一证书（只记录叶数相同）。
- 未逐条把 59 个 HOL 盒端点与 Lean bank 盒端点做机器 diff（抽样 + docstring 交叉验证）。
- 未在本机运行 pipeline（工具链缺失）。
